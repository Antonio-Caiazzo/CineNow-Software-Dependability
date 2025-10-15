package it.unisa.application.model.entity;

import java.sql.Time;

public class Slot {
    //@ spec_public
    private int id;
    //@ spec_public
    private Time oraInizio;

    //@ public invariant id >= 0;
    //@ public invariant oraInizio == null || oraInizio.getTime() >= 0;

    /*@ public normal_behavior
      @   requires true;
      @   assignable *;
      @   ensures this.id == 0;
      @   ensures this.oraInizio == null;
      @*/
    public Slot() {
    }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   ensures this.id == id;
      @   ensures this.oraInizio == null;
      @*/
    public Slot(int id) {
        this.id = id;
    }

    /*@ public normal_behavior
      @   requires true;
      @   assignable \nothing;
      @   ensures \result == oraInizio;
      @*/
    /*@ pure @*/
    public Time getOraInizio() {
        return oraInizio;
    }

    /*@ public normal_behavior
      @   requires oraInizio != null;
      @   assignable this.oraInizio;
      @   ensures this.oraInizio == oraInizio;
      @*/
    public void setOraInizio(Time oraInizio) {
        this.oraInizio = oraInizio;
    }

    /*@ public normal_behavior
      @   requires true;
      @   assignable \nothing;
      @   ensures \result == id;
      @*/
    /*@ pure @*/
    public int getId() {
        return id;
    }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   assignable this.id;
      @   ensures this.id == id;
      @*/
    public void setId(int id) {
        this.id = id;
    }

    @Override
    public String toString() {
        return "Slot{" +
                "id=" + id +
                ", oraInizio=" + oraInizio +
                '}';
    }
}
