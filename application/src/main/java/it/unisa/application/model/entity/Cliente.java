package it.unisa.application.model.entity;

import java.util.ArrayList;
import java.util.List;

public class Cliente extends Utente {
    //@ spec_public
    private String nome;
    //@ spec_public
    private String cognome;
    //@ spec_public
    private List<Prenotazione> prenotazioni;

    //@ public invariant prenotazioni != null;

    /*@ public normal_behavior
      @   ensures prenotazioni != null;
      @*/
    public Cliente() {
        super();
        this.setRuolo("cliente");
        this.prenotazioni = new ArrayList<Prenotazione>();
    }

    /*@ public normal_behavior
      @   requires email != null && !email.isEmpty();
      @   requires password != null && !password.isEmpty();
      @   requires nome != null && !nome.isEmpty();
      @   requires cognome != null && !cognome.isEmpty();
      @   ensures getRuolo() != null && getRuolo().equals("cliente");
      @   ensures this.nome == nome;
      @   ensures this.cognome == cognome;
      @   ensures this.prenotazioni != null;
      @*/
    public Cliente(String email, String password, String nome, String cognome) {
        super(email, password, "cliente");
        this.nome = nome;
        this.cognome = cognome;
        this.prenotazioni = new ArrayList<Prenotazione>();
    }

    /*@ public normal_behavior

      @   assignable \nothing;
      @   ensures \result == nome;
      @*/
    /*@ pure @*/
    public String getNome() {
        return nome;
    }

    /*@ public normal_behavior
      @   assignable this.nome;
      @   ensures this.nome == nome;
      @*/
    public void setNome(String nome) {
        this.nome = nome;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == cognome;
      @*/
    /*@ pure @*/
    public String getCognome() {
        return cognome;
    }

    /*@ public normal_behavior
      @   assignable this.cognome;
      @   ensures this.cognome == cognome;
      @*/
    public void setCognome(String cognome) {
        this.cognome = cognome;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == prenotazioni && \result != null;
      @*/
    /*@ pure @*/
    public List<Prenotazione> storicoOrdini() {
        return prenotazioni;
    }

    /*@ public normal_behavior
      @   requires prenotazioni != null;
      @   assignable this.prenotazioni;
      @   ensures this.prenotazioni == prenotazioni;
      @*/
    public void setPrenotazioni(List<Prenotazione> prenotazioni) {
        this.prenotazioni = prenotazioni;
    }

    /*@ public normal_behavior
      @   requires prenotazioni != null;
      @   requires posti != null && proiezione != null;
      @   assignable this.prenotazioni;
      @   ensures prenotazioni.size() == \old(prenotazioni.size()) + 1;
      @*/
    public void aggiungiOrdine(List<PostoProiezione> posti, Proiezione proiezione) {
        Prenotazione prenotazione = new Prenotazione();
        prenotazione.setCliente(this);
        prenotazione.setProiezione(proiezione);
        prenotazione.setPostiPrenotazione(posti);
        prenotazioni.add(prenotazione);
    }

    @Override
    public String toString() {
        return "Cliente{" +
                "nome='" + nome + '\'' +
                ", cognome='" + cognome + '\'' +
                ", prenotazioni=" + prenotazioni +
                '}';
    }
}
