package it.unisa.application.sottosistemi.gestione_utente.service;

import it.unisa.application.model.dao.ClienteDAO;
import it.unisa.application.model.dao.SedeDAO;
import it.unisa.application.model.dao.UtenteDAO;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.model.entity.GestoreSede;
import it.unisa.application.model.entity.Sede;
import it.unisa.application.model.entity.Utente;
import it.unisa.application.utilities.PasswordHash;
import jakarta.servlet.http.HttpSession;

public class AutenticazioneService {
    //@ spec_public
    private UtenteDAO utenteDAO;
    //@ spec_public
    private ClienteDAO clienteDAO;

    //@ public invariant utenteDAO != null;
    //@ public invariant clienteDAO != null;

    /**
     * Costruttore di default del servizio di autenticazione.
     */
    /*@ public normal_behavior
      @   requires true;
      @   ensures this.utenteDAO != null;
      @   ensures this.clienteDAO != null;
      @*/
    public AutenticazioneService() {
        this.utenteDAO = new UtenteDAO();
        this.clienteDAO = new ClienteDAO();
    }
    /*Costruttore per il testing*/
    /**
     * Costruttore a iniezione per test.
     */
    /*@ public normal_behavior
      @   requires utenteDAOMock != null;
      @   requires clienteDAOMock != null;
      @   ensures this.utenteDAO == utenteDAOMock;
      @   ensures this.clienteDAO == clienteDAOMock;
      @*/
    public AutenticazioneService(UtenteDAO utenteDAOMock, ClienteDAO clienteDAOMock) {
        this.utenteDAO = utenteDAOMock;
        this.clienteDAO = clienteDAOMock;
    }


    /**
     * Esegue il processo di autenticazione per l'utente con le credenziali fornite.
     */
    /*@ public normal_behavior
      @   requires email != null && !email.isEmpty();
      @   requires password != null && !password.isEmpty();
      @   assignable \nothing;
      @   ensures \result == null || \result.getEmail().equals(email);
      @*/
    public Utente login(String email, String password) {
        Utente baseUser = utenteDAO.retrieveByEmail(email);
        if (baseUser == null) {
            return null;
        }
        String passHash = PasswordHash.hash(password);
        if (!baseUser.getPassword().equals(passHash)) {
            return null;
        }
        if (baseUser.getRuolo().equalsIgnoreCase("cliente")) {
            return clienteDAO.retrieveByEmail(email, passHash);

        }
        if (baseUser.getRuolo().equalsIgnoreCase("gestore_sede")) {
            GestoreSede gs = new GestoreSede();
            gs.setEmail(baseUser.getEmail());
            gs.setPassword(baseUser.getPassword());
            gs.setRuolo(baseUser.getRuolo());

            SedeDAO sedeDAO = new SedeDAO();
            Sede sede = sedeDAO.retrieveByGestoreEmail(baseUser.getEmail());
            gs.setSede(sede);

            return gs;
        }

        return baseUser;
    }

    /**
     * Invalida la sessione corrente.
     */
    /*@ public normal_behavior
      @   requires session != null;
      @   assignable \nothing;
      @   ensures true;
      @*/
    public void logout(HttpSession session) {
        session.invalidate();
    }
}
