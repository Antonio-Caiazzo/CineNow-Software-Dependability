package it.unisa.application.model.entity;

public class GestoreSede extends Utente {

    //@ spec_public
    private Sede sede;

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == sede;
      @*/
    /*@ pure @*/
    public Sede getSede() {
        return sede;
    }

    /*@ public normal_behavior
      @   assignable this.sede;
      @   ensures this.sede == sede;

      @*/
    public void setSede(Sede sede) {
        this.sede = sede;
    }

    /*@ public behavior
      @*/
    public GestoreSede() {
        super();
        this.setRuolo("gestore_sede");
    }

    /*@ public behavior
      @   requires email != null && !email.isEmpty();
      @   requires password != null && !password.isEmpty();
      @   requires sede != null;
      @   ensures this.sede == sede;
      @*/
    public GestoreSede(String email, String password, Sede sede) {
        super(email, password, "gestore_sede");
        this.sede = sede;
    }

    @Override
    public String toString() {
        return "GestoreSede{" +
                "sede=" + sede +
                '}';
    }
}
