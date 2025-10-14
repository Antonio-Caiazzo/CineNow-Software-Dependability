package it.unisa.application.model.entity;

import java.util.Objects;

public class Utente {
    //@ spec_public
    private String email;
    //@ spec_public
    private String password;
    //@ spec_public
    private String ruolo;

    //@ public invariant email == null || !email.isEmpty();
    //@ public invariant password == null || !password.isEmpty();
    //@ public invariant ruolo == null || !ruolo.isEmpty();

    /*@ public normal_behavior
      @   requires email != null && !email.isEmpty();
      @   requires password != null && !password.isEmpty();
      @   requires ruolo != null && !ruolo.isEmpty();
      @   assignable *;
      @   ensures this.email == email;
      @   ensures this.password == password;
      @   ensures this.ruolo == ruolo;
      @*/
    public Utente(String email, String password,String ruolo) {
        this.email = email;
        this.password = password;
        this.ruolo = ruolo;
    }

    public Utente() {
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == email;
      @*/
    public /*@ pure @*/ String getEmail() {
        return email;
    }

    /*@ public normal_behavior
      @   requires email != null && !email.isEmpty();
      @   assignable email;
      @   ensures this.email == email;
      @*/
    public void setEmail(String email) {
        this.email = email;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == password;
      @*/
    public /*@ pure @*/ String getPassword() {
        return password;
    }

    /*@ public normal_behavior
      @   requires password != null && !password.isEmpty();
      @   assignable password;
      @   ensures this.password == password;
      @*/
    public void setPassword(String password) {
        this.password = password;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == ruolo;
      @*/
    public /*@ pure @*/ String getRuolo() {
        return ruolo;
    }

    /*@ public normal_behavior
      @   requires ruolo != null && !ruolo.isEmpty();
      @   assignable ruolo;
      @   ensures this.ruolo == ruolo;
      @*/
    public void setRuolo(String ruolo) {
        this.ruolo = ruolo;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Utente utente = (Utente) o;
        return Objects.equals(email, utente.email) && Objects.equals(password, utente.password);
    }

    @Override
    public int hashCode() {
        return Objects.hash(email, password);
    }

    @Override
    public String toString() {
        return "Utente{" +
                "email='" + email + '\'' +
                ", password='" + password + '\'' +
                ", ruolo='" + ruolo + '\'' +
                '}';
    }
}
