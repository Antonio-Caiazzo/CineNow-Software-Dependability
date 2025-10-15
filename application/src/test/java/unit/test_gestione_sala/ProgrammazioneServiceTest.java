package unit.test_gestione_sala;

import it.unisa.application.model.dao.FilmDAO;
import it.unisa.application.model.dao.ProiezioneDAO;
import it.unisa.application.model.dao.SalaDAO;
import it.unisa.application.model.dao.SlotDAO;
import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.model.entity.Sala;
import it.unisa.application.model.entity.Slot;
import it.unisa.application.sottosistemi.gestione_sala.service.ProgrammazioneService;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.ArgumentCaptor;

import java.sql.Time;
import java.time.LocalDate;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Versione senza construction-mocking: usa injection dei DAO nel service.
 */
class ProgrammazioneServiceTest {

    private FilmDAO filmDAO;
    private SalaDAO salaDAO;
    private SlotDAO slotDAO;
    private ProiezioneDAO proiezioneDAO;

    private ProgrammazioneService service;

    @BeforeEach
    void setUp() {
        filmDAO = mock(FilmDAO.class);
        salaDAO = mock(SalaDAO.class);
        slotDAO = mock(SlotDAO.class);
        proiezioneDAO = mock(ProiezioneDAO.class);
        service = new ProgrammazioneService(filmDAO, salaDAO, slotDAO, proiezioneDAO);
    }

    @Test
    void testFilmNonSelezionato() {
        int salaId = 1;
        List<Integer> slotIds = List.of(1, 2);
        LocalDate data = LocalDate.now().plusDays(5);

        when(filmDAO.retrieveById(anyInt())).thenReturn(null);
        when(salaDAO.retrieveById(anyInt())).thenReturn(new Sala());
        when(slotDAO.retrieveAllSlots()).thenReturn(List.of());

        boolean result = service.aggiungiProiezione(0, salaId, slotIds, data);
        assertFalse(result, "Dovrebbe fallire: film nullo.");
        verify(proiezioneDAO, never()).create(any());
    }

    @Test
    void testDataNonInserita() {
        int filmId = 1;
        int salaId = 1;
        List<Integer> slotIds = List.of(1);

        Film film = new Film(); film.setId(filmId);
        Sala sala = new Sala(); sala.setId(salaId);

        when(filmDAO.retrieveById(filmId)).thenReturn(film);
        when(salaDAO.retrieveById(salaId)).thenReturn(sala);
        when(slotDAO.retrieveAllSlots()).thenReturn(List.of());

        boolean result = service.aggiungiProiezione(filmId, salaId, slotIds, null);
        assertFalse(result, "Dovrebbe fallire: data nulla (NPE interno catturato).");
        verify(proiezioneDAO, never()).create(any());
    }

    @Test
    void testDataPassata() {
        int filmId = 1;
        int salaId = 1;
        LocalDate dataPassata = LocalDate.now().minusDays(1);

        Film film = new Film(); film.setId(filmId);
        Sala sala = new Sala(); sala.setId(salaId);

        when(filmDAO.retrieveById(filmId)).thenReturn(film);
        when(salaDAO.retrieveById(salaId)).thenReturn(sala);
        when(slotDAO.retrieveAllSlots()).thenReturn(List.of());

        boolean result = service.aggiungiProiezione(filmId, salaId, List.of(1, 2), dataPassata);
        assertFalse(result, "Dovrebbe fallire: data nel passato.");
        verify(proiezioneDAO, never()).create(any());
    }

    @Test
    void testSlotNonDisponibili() {
        int filmId = 1;
        int salaId = 1;
        LocalDate data = LocalDate.now().plusDays(10);

        Film film = new Film(); film.setId(filmId);
        Sala sala = new Sala(); sala.setId(salaId);

        when(filmDAO.retrieveById(filmId)).thenReturn(film);
        when(salaDAO.retrieveById(salaId)).thenReturn(sala);
        // Nessuno degli slot disponibili ha ID 10 o 20
        when(slotDAO.retrieveAllSlots()).thenReturn(
                List.of(makeSlot(1, "18:00:00"), makeSlot(2, "18:30:00"))
        );

        boolean result = service.aggiungiProiezione(filmId, salaId, List.of(10, 20), data);
        assertFalse(result, "Dovrebbe fallire: slot selezionati non presenti tra quelli disponibili.");
        verify(proiezioneDAO, never()).create(any());
    }

    @Test
    void testProiezioneAggiuntaConSuccesso() {
        int filmId = 1;
        int salaId = 1;
        LocalDate data = LocalDate.now().plusDays(7);
        List<Integer> slotIds = List.of(1, 2);

        Film film = new Film();
        film.setId(filmId);
        film.setTitolo("Test Film");
        film.setDurata(120);

        Sala sala = new Sala();
        sala.setId(salaId);
        sala.setNumeroSala(1);
        sala.setCapienza(100);

        Slot s1 = makeSlot(1, "19:00:00");
        Slot s2 = makeSlot(2, "19:30:00");

        when(filmDAO.retrieveById(filmId)).thenReturn(film);
        when(salaDAO.retrieveById(salaId)).thenReturn(sala);
        when(slotDAO.retrieveAllSlots()).thenReturn(List.of(s1, s2));
        when(proiezioneDAO.create(any(Proiezione.class))).thenReturn(true);

        boolean result = service.aggiungiProiezione(filmId, salaId, slotIds, data);
        assertTrue(result, "Dovrebbe passare: dati coerenti e create(...) true.");

        ArgumentCaptor<Proiezione> captor = ArgumentCaptor.forClass(Proiezione.class);
        verify(proiezioneDAO, times(1)).create(captor.capture());
        Proiezione saved = captor.getValue();
        assertSame(film, saved.getFilmProiezione());
        assertSame(sala, saved.getSalaProiezione());
        assertEquals(data, saved.getDataProiezione());
        assertEquals(s1, saved.getOrarioProiezione(), "Il primo slot (più precoce) deve essere scelto.");
    }

    @Test
    void testSalaNull() {
        int filmId = 1;
        int salaId = 99;
        LocalDate data = LocalDate.now().plusDays(3);

        Film film = new Film(); film.setId(filmId);

        when(filmDAO.retrieveById(filmId)).thenReturn(film);
        when(salaDAO.retrieveById(salaId)).thenReturn(null);
        when(slotDAO.retrieveAllSlots()).thenReturn(List.of());

        boolean result = service.aggiungiProiezione(filmId, salaId, List.of(1), data);
        assertFalse(result, "Dovrebbe fallire: sala nulla.");
        verify(proiezioneDAO, never()).create(any());
    }

    // --- helper ---
    private static Slot makeSlot(int id, String hhmmss) {
        Slot s = new Slot();
        s.setId(id);
        s.setOraInizio(Time.valueOf(hhmmss));
        return s;
    }
}
