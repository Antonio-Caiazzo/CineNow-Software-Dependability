package it.unisa.application.sottosistemi.gestione_prenotazione.service;

import it.unisa.application.model.dao.PostoProiezioneDAO;
import it.unisa.application.model.dao.PrenotazioneDAO;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.model.entity.PostoProiezione;
import it.unisa.application.model.entity.Prenotazione;
import it.unisa.application.model.entity.Proiezione;

import java.util.List;

public class PrenotazioneService {
    //@ spec_public
    private PrenotazioneDAO prenotazioneDAO = new PrenotazioneDAO();
    //@ spec_public
    private PostoProiezioneDAO postoProiezioneDAO = new PostoProiezioneDAO();

    //@ public invariant prenotazioneDAO != null && postoProiezioneDAO != null;

    /**
     * Costruttore di default.
     */
    /*@ public behavior
      @   assignable \nothing;
      @   ensures this.prenotazioneDAO != null;
      @   ensures this.postoProiezioneDAO != null;
      @*/
    public PrenotazioneService() {
    }

    /**
     * Costruttore a iniezione per test.
     */
    /*@ public behavior
      @   requires prenotazioneDAOMock != null;
      @   requires postoProiezioneDAOMock != null;
      @*/
    public PrenotazioneService(PrenotazioneDAO prenotazioneDAOMock, PostoProiezioneDAO postoProiezioneDAOMock) {
        prenotazioneDAO = prenotazioneDAOMock;
        postoProiezioneDAO = postoProiezioneDAOMock;
    }

    /**
     * Crea una nuova prenotazione occupando i posti selezionati.
     */
    /*@ public behavior
      @   requires cliente != null;
      @   requires posti != null && posti.size() > 0;
      @   requires proiezione != null;
      @   assignable \nothing;
      @   ensures \result != null ==> (
      @              \result.getCliente() == cliente &&
      @              \result.getProiezione() == proiezione &&
      @              \result.getPostiPrenotazione() != null &&
      @              \result.getPostiPrenotazione().size() == posti.size()
      @          );
      @*/
    public Prenotazione aggiungiOrdine(Cliente cliente, List<PostoProiezione> posti, Proiezione proiezione) {
        if (cliente == null || posti == null || posti.isEmpty() || proiezione == null) {
            throw new IllegalArgumentException("Cliente, posti e proiezione non possono essere null.");
        }
        for (PostoProiezione postoProiezione : posti) {
            if (!postoProiezione.isStato()) {
                throw new IllegalArgumentException("Posti occupati");
            }
        }
        Prenotazione prenotazione = new Prenotazione();
        prenotazione.setCliente(cliente);
        prenotazione.setProiezione(proiezione);
        prenotazione.setPostiPrenotazione(posti);

        if (!prenotazioneDAO.create(prenotazione)) {
            throw new RuntimeException("Errore durante la creazione della prenotazione.");
        }

        for (PostoProiezione postoProiezione : posti) {
            if (!postoProiezioneDAO.occupaPosto(postoProiezione, prenotazione.getId())) {
                throw new RuntimeException("Errore durante l'occupazione del posto.");
            }
        }

        return prenotazione;
    }

    /**
     * Restituisce i posti associati alla proiezione.
     */
    /*@ public normal_behavior
      @   requires proiezione != null;
      @   assignable \nothing;
      @   ensures \result != null;
      @   ensures (\forall int i; 0 <= i && i < \result.size();
      @               \result.get(i) != null &&
      @               \result.get(i).getProiezione() == proiezione);
      @*/
    public List<PostoProiezione> ottieniPostiProiezione(Proiezione proiezione){
        return postoProiezioneDAO.retrieveAllByProiezione(proiezione);
    }
}
