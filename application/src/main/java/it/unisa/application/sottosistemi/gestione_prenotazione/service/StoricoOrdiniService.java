package it.unisa.application.sottosistemi.gestione_prenotazione.service;

import it.unisa.application.model.dao.PrenotazioneDAO;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.model.entity.Prenotazione;

import java.util.List;

public class StoricoOrdiniService {
    //@ spec_public
    private PrenotazioneDAO prenotazioneDAO;

    //@ public invariant prenotazioneDAO != null;

    /**
     * Costruttore di default del servizio storico ordini.
     */
    /*@ public behavior
      @   ensures prenotazioneDAO != null;
      @*/
    public StoricoOrdiniService() {
        this.prenotazioneDAO = new PrenotazioneDAO();
    }

    /**
     * Costruttore a iniezione per test.
     */
    /*@ public behavior
      @   requires prenotazioneDAOMock != null;
      @   ensures prenotazioneDAO == prenotazioneDAOMock;
      @*/
    public StoricoOrdiniService(PrenotazioneDAO prenotazioneDAOMock) {
        prenotazioneDAO = prenotazioneDAOMock;
    }

    /**
     * Restituisce lo storico degli ordini di un cliente.
     */
    /*@ public normal_behavior
      @   requires cliente != null;
      @   assignable \nothing;
      @   ensures \result != null;
      @   ensures (\forall int i; 0 <= i && i < \result.size(); \result.get(i) != null);
      @*/
    public List<Prenotazione> storicoOrdini(Cliente cliente) {
        if (cliente == null) {
            throw new IllegalArgumentException("Il cliente non può essere null.");
        }
        return prenotazioneDAO.retrieveAllByCliente(cliente);
    }
}
