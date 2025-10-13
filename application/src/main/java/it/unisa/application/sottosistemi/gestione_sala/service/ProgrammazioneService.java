package it.unisa.application.sottosistemi.gestione_sala.service;

import it.unisa.application.model.dao.*;
import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.model.entity.Sala;
import it.unisa.application.model.entity.Slot;
import java.time.LocalDate;
import java.util.Comparator;
import java.util.List;

public class ProgrammazioneService {
    private final ProiezioneDAO proiezioneDAO;
    private final FilmDAO filmDAO;
    private final SalaDAO salaDAO;
    private final SlotDAO slotDAO;

    //Costruttore per il testing
    public ProgrammazioneService(ProiezioneDAO proiezioneDAOMock, FilmDAO filmDAOMock, SalaDAO salaDAOMock, SlotDAO slotDAOMock) {
        this.proiezioneDAO = proiezioneDAOMock;
        this.filmDAO = filmDAOMock;
        this.salaDAO = salaDAOMock;
        this.slotDAO = slotDAOMock;
    }

    public ProgrammazioneService() {
        this.proiezioneDAO = new ProiezioneDAO();
        this.filmDAO = new FilmDAO();
        this.salaDAO = new SalaDAO();
        this.slotDAO = new SlotDAO();
    }

    public ProgrammazioneService(ProiezioneDAO proiezioneDAO) {
        this.proiezioneDAO = proiezioneDAO;
        this.filmDAO = new FilmDAO();
        this.salaDAO = new SalaDAO();
        this.slotDAO = new SlotDAO();
    }

    public boolean aggiungiProiezione(int filmId, int salaId, List<Integer> slotIds, LocalDate data) {
        try {
            Film film = filmDAO.retrieveById(filmId);
            Sala sala = salaDAO.retrieveById(salaId);

            if (film == null) {
                throw new RuntimeException("Film non trovato.");
            }
            if (sala == null) {
                throw new RuntimeException("Sala non trovata.");
            }
            if(data == null || data.isBefore(LocalDate.now())){
                throw new RuntimeException("Errore data.");
            }
            List<Slot> slotsDisponibili = slotDAO.retrieveAllSlots();
            List<Slot> slotsSelezionati = slotsDisponibili.stream()
                    .filter(slot -> slotIds.contains(slot.getId()))
                    .sorted(Comparator.comparing(Slot::getOraInizio))
                    .toList();

            if (slotsSelezionati.isEmpty()) {
                throw new RuntimeException("Nessuno slot valido selezionato.");
            }
            Slot primoSlot = slotsSelezionati.get(0);
            Proiezione proiezione = new Proiezione();
            proiezione.setFilmProiezione(film);
            proiezione.setSalaProiezione(sala);
            proiezione.setDataProiezione(data);
            proiezione.setOrarioProiezione(primoSlot);
            return this.proiezioneDAO.create(proiezione);

        } catch (Exception e) {
            e.printStackTrace();
            return false;
        }
    }

}
