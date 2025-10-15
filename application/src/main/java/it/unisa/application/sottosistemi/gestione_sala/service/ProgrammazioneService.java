package it.unisa.application.sottosistemi.gestione_sala.service;

import it.unisa.application.model.dao.FilmDAO;
import it.unisa.application.model.dao.ProiezioneDAO;
import it.unisa.application.model.dao.SalaDAO;
import it.unisa.application.model.dao.SlotDAO;
import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.model.entity.Sala;
import it.unisa.application.model.entity.Slot;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

public class ProgrammazioneService {
    //@ spec_public
    private FilmDAO filmDAO;
    //@ spec_public
    private SalaDAO salaDAO;
    //@ spec_public
    private SlotDAO slotDAO;
    //@ spec_public
    private ProiezioneDAO proiezioneDAO;

    //@ public invariant filmDAO != null && salaDAO != null && slotDAO != null && proiezioneDAO != null;

    /**
     * Costruttore a iniezione per i test (solo ProiezioneDAO).
     */
    /*@ public behavior
      @   requires proiezioneDAOMock != null;
      @   assignable \everything;
      @   ensures this.proiezioneDAO == proiezioneDAOMock;
      @*/
    public ProgrammazioneService(ProiezioneDAO proiezioneDAOMock) {
        this.filmDAO = new FilmDAO();
        this.salaDAO = new SalaDAO();
        this.slotDAO = new SlotDAO();
        this.proiezioneDAO = proiezioneDAOMock;
    }

    /**
     * Costruttore a iniezione completo (consigliato per i test).
     */
    /*@ public behavior
      @   requires filmDAO != null && salaDAO != null && slotDAO != null && proiezioneDAO != null;
      @   assignable \everything;
      @   ensures this.filmDAO == filmDAO && this.salaDAO == salaDAO
      @        && this.slotDAO == slotDAO && this.proiezioneDAO == proiezioneDAO;
      @*/
    public ProgrammazioneService(FilmDAO filmDAO, SalaDAO salaDAO, SlotDAO slotDAO, ProiezioneDAO proiezioneDAO) {
        this.filmDAO = filmDAO;
        this.salaDAO = salaDAO;
        this.slotDAO = slotDAO;
        this.proiezioneDAO = proiezioneDAO;
    }

    /**
     * Costruttore di default.
     */
    /*@ public behavior
      @   assignable \everything;
      @   ensures this.filmDAO != null && this.salaDAO != null
      @        && this.slotDAO != null && this.proiezioneDAO != null;
      @*/
    public ProgrammazioneService() {
        this.filmDAO = new FilmDAO();
        this.salaDAO = new SalaDAO();
        this.slotDAO = new SlotDAO();
        this.proiezioneDAO = new ProiezioneDAO();
    }

    /**
     * Aggiunge una nuova proiezione in sala per la data indicata.
     */
    /*@ public normal_behavior
      @   requires filmId >= 0;
      @   requires salaId >= 0;
      @   requires slotIds != null && slotIds.size() > 0;
      @   requires data != null;
      @   assignable \nothing;
      @   ensures \result == true || \result == false;
      @*/
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
            if (data.isBefore(LocalDate.now())) {
                throw new RuntimeException("Errore data.");
            }

            List<Slot> slotsDisponibili = slotDAO.retrieveAllSlots();

            // Filtro manuale degli slot selezionati (senza stream)
            List<Slot> slotsSelezionati = new ArrayList<>();
            for (int i = 0; i < slotsDisponibili.size(); i++) {
                Slot slot = slotsDisponibili.get(i);
                if (slotIds.contains(slot.getId())) {
                    slotsSelezionati.add(slot);
                }
            }

            // Ordinamento per ora di inizio (senza lambda/anonime)
            sortSlotsByOraInizio(slotsSelezionati);

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

    /*@ private normal_behavior
      @   requires slots != null;
      @   assignable \everything; // riordina il contenuto della lista
      @*/
    private static void sortSlotsByOraInizio(List<Slot> slots) {
        // Insertion sort per evitare Comparator/lambda/anonime
        for (int i = 1; i < slots.size(); i++) {
            Slot key = slots.get(i);
            int j = i - 1;
            while (j >= 0 && slots.get(j).getOraInizio().compareTo(key.getOraInizio()) > 0) {
                slots.set(j + 1, slots.get(j));
                j--;
            }
            slots.set(j + 1, key);
        }
    }
}
