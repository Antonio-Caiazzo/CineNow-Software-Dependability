package it.unisa.application.model.entity;

import java.util.List;

public class Prenotazione {
    //@ spec_public
    private int id;
    //@ spec_public
    private Proiezione proiezione;
    //@ spec_public
    private List<PostoProiezione> postiPrenotazione;
    //@ spec_public
    private Cliente cliente;

    //@ public invariant id >= 0;
    //@ public invariant proiezione == null || proiezione.getPostiProiezione() != null;
    //@ public invariant postiPrenotazione == null || !postiPrenotazione.contains(null);
    //@ public invariant cliente == null || cliente.getRuolo() != null;

    public Prenotazione() {}

    /*@ public normal_behavior
      @   requires id >= 0;
      @   requires cliente != null;
      @   requires proiezione != null;
      @   ensures this.id == id;
      @   ensures this.cliente == cliente;
      @   ensures this.proiezione == proiezione;
      @   ensures this.postiPrenotazione == null;
      @*/
    public Prenotazione(int id, Cliente cliente, Proiezione proiezione) {
        this.id = id;
        this.cliente = cliente;
        this.proiezione = proiezione;
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

    /*@ public normal_behavior
      @   requires true;
      @   assignable \nothing;
      @   ensures \result == proiezione;
      @*/
    /*@ pure @*/
    public Proiezione getProiezione() {
        return proiezione;
    }

    /*@ public normal_behavior
      @   requires proiezione != null;
      @   assignable this.proiezione;
      @   ensures this.proiezione == proiezione;
      @*/
    public void setProiezione(Proiezione proiezione) {
        this.proiezione = proiezione;
    }

    /*@ public normal_behavior
      @   requires true;
      @   assignable \nothing;
      @   ensures \result == postiPrenotazione;
      @*/
    /*@ pure @*/
    public List<PostoProiezione> getPostiPrenotazione() {
        return postiPrenotazione;
    }

    /*@ public normal_behavior
      @   requires postiProiezione != null;
      @   requires !postiProiezione.contains(null);
      @   assignable this.postiPrenotazione;
      @   ensures this.postiPrenotazione == postiProiezione;
      @*/
    public void setPostiPrenotazione(List<PostoProiezione> postiProiezione) {
        this.postiPrenotazione = postiProiezione;
    }

    /*@ public normal_behavior
      @   requires true;
      @   assignable \nothing;
      @   ensures \result == cliente;
      @*/
    /*@ pure @*/
    public Cliente getCliente() {
        return cliente;
    }

    /*@ public normal_behavior
      @   requires cliente != null;
      @   assignable this.cliente;
      @   ensures this.cliente == cliente;
      @*/
    public void setCliente(Cliente cliente) {
        this.cliente = cliente;
    }

    @Override
    public String toString() {
        return "Prenotazione{" +
                "id=" + id +
                ", proiezione=" + proiezione +
                ", postiPrenotazione=" + postiPrenotazione +
                ", cliente=" + cliente +
                '}';
    }
}
