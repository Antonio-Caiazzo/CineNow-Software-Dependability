package it.unisa.application.sottosistemi.gestione_utente.service;

import it.unisa.application.model.dao.ClienteDAO;
import it.unisa.application.model.dao.UtenteDAO;
import it.unisa.application.model.entity.Cliente;
import it.unisa.application.utilities.*;

import java.util.HashMap;
import java.util.Map;

public class RegistrazioneService {
    //@ spec_public
    private ValidateStrategyManager validationManager;
    //@ spec_public
    private UtenteDAO utenteDAO;
    //@ spec_public
    private ClienteDAO clienteDAO;

    //@ public invariant validationManager != null;
    //@ public invariant utenteDAO != null;
    //@ public invariant clienteDAO != null;

    /**
     * Costruttore di default che inizializza i validatori.
     */
    /*@ public normal_behavior
      @   requires true;
      @   ensures this.validationManager != null;
      @   ensures this.utenteDAO != null;
      @   ensures this.clienteDAO != null;
      @*/
    public RegistrazioneService() {
        this.validationManager = new ValidateStrategyManager();
        this.utenteDAO = new UtenteDAO();
        this.clienteDAO = new ClienteDAO();

        validationManager.addValidator("email", new EmailValidator());
        validationManager.addValidator("password", new PasswordValidator());
        validationManager.addValidator("nome", new CampoValidator());
        validationManager.addValidator("cognome", new CampoValidator());
    }
    /*Costruttore per il testing*/
    /**
     * Costruttore a iniezione per test.
     */
    /*@ public normal_behavior
      @   requires utenteDAOMock != null;
      @   requires clienteDAOMock != null;
      @   ensures this.validationManager != null;
      @   ensures this.utenteDAO == utenteDAOMock;
      @   ensures this.clienteDAO == clienteDAOMock;
      @*/
    public RegistrazioneService(UtenteDAO utenteDAOMock, ClienteDAO clienteDAOMock) {
        this.validationManager = new ValidateStrategyManager();
        this.utenteDAO = utenteDAOMock;
        this.clienteDAO = clienteDAOMock;
        validationManager.addValidator("email", new EmailValidator());
        validationManager.addValidator("password", new PasswordValidator());
        validationManager.addValidator("nome", new CampoValidator());
        validationManager.addValidator("cognome", new CampoValidator());
    }


    /**
     * Esegue la registrazione di un nuovo cliente.
     */
    /*@ public normal_behavior
      @   requires email != null && !email.isEmpty();
      @   requires password != null && !password.isEmpty();
      @   requires nome != null && !nome.isEmpty();
      @   requires cognome != null && !cognome.isEmpty();
      @   assignable clienteDAO.*;
      @   ensures (\result != null) ==> \result.getEmail().equals(email);
      @*/
    public Cliente registrazione(String email, String password, String nome, String cognome) {
        Map<String, String> inputs = new HashMap<>();
        inputs.put("email", email);
        inputs.put("password", password);
        inputs.put("nome", nome);
        inputs.put("cognome", cognome);

        if (!validationManager.validate(inputs) || utenteDAO.retrieveByEmail(email) != null) {
            return null;
        }

        String passHash = PasswordHash.hash(password);
        Cliente cliente = new Cliente(email, passHash, nome, cognome);
        clienteDAO.create(cliente);
        return cliente;
    }
}
