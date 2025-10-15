package it.unisa.application.model.entity;

public class PostoProiezione {

    //@ spec_public
    private Posto posto;
    //@ spec_public
    private Proiezione proiezione;
    //@ spec_public
    private boolean stato;

    /*@ public behavior
      @   ensures this.stato == true;
      @   ensures this.posto == null && this.proiezione == null;
      @*/
    public PostoProiezione() {
        this.stato = true;
    }

    /*@ public behavior
      @   requires posto != null;
      @   requires proiezione != null;
      @   ensures this.stato == true;
      @   ensures this.posto == posto;
      @   ensures this.proiezione == proiezione;
      @*/
    public PostoProiezione(Posto posto, Proiezione proiezione) {
        this.stato = true;
        this.posto = posto;
        this.proiezione = proiezione;
    }

    /*@ public behavior
      @   requires sala != null;
      @   requires proiezione != null;
      @   ensures this.posto != null;
      @   ensures this.posto.sala == sala;
      @   ensures this.posto.fila == fila;
      @   ensures this.posto.numero == numero;
      @   ensures this.proiezione == proiezione;
      @   ensures this.stato == true;
      @*/
    public PostoProiezione(Sala sala, char fila, int numero, Proiezione proiezione, boolean stato) {
        this.posto = new Posto(sala, fila, numero);
        this.proiezione = proiezione;
        this.stato = true;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == posto;
      @*/
    /*@ pure @*/
    public  Posto getPosto() {
        return posto;
    }

    /*@ public normal_behavior
      @   assignable this.posto;
      @   ensures this.posto == posto;
      @*/
    public void setPosto(Posto posto) {
        this.posto = posto;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == proiezione;
      @*/
    /*@ pure @*/
    public  Proiezione getProiezione() {
        return proiezione;
    }

    /*@ public normal_behavior
      @   assignable this.proiezione;
      @   ensures this.proiezione == proiezione;
      @*/
    public void setProiezione(Proiezione proiezione) {
        this.proiezione = proiezione;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == stato;
      @*/
    /*@ pure @*/
    public boolean isStato() {
        return stato;
    }

    /*@ public normal_behavior
      @   assignable this.stato;
      @   ensures this.stato == stato;
      @*/
    public void setStato(boolean stato) {
        this.stato = stato;
    }
}
