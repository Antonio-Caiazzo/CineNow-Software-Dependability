package it.unisa.application.model.entity;

public class Posto {
    //@ spec_public
    private Sala sala;
    //@ spec_public
    private char fila;
    //@ spec_public
    private int numero;

    /*@ public behavior @*/
    public Posto() {}

    /*@ public behavior
      @   ensures this.sala == sala;
      @   ensures this.fila == fila;
      @   ensures this.numero == numero;
      @*/
    public Posto(Sala sala, char fila, int numero) {
        this.sala = sala;
        this.fila = fila;
        this.numero = numero;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == sala;
      @*/
    /*@ pure @*/
    public Sala getSala() { return sala; }

    /*@ public normal_behavior
      @   assignable this.sala;
      @   ensures this.sala == sala;
      @*/
    public void setSala(Sala sala) { this.sala = sala; }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == fila;
      @*/
    /*@ pure @*/
    public char getFila() { return fila; }

    /*@ public normal_behavior
      @   assignable this.fila;
      @   ensures this.fila == fila;
      @*/
    public void setFila(char fila) { this.fila = fila; }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == numero;
      @*/
    /*@ pure @*/
    public int getNumero() { return numero; }

    /*@ public normal_behavior
      @   assignable this.numero;
      @   ensures this.numero == numero;
      @*/
    public void setNumero(int numero) { this.numero = numero; }

    @Override
    public String toString() {
        return "Posto{" +
                "sala=" + sala +
                ", fila=" + fila +
                ", numero=" + numero +
                '}';
    }
}
