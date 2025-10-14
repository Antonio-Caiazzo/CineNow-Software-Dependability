package it.unisa.application.model.entity;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

public class Sala {
    //@ spec_public
    private int id;
    //@ spec_public
    private int numeroSala;
    //@ spec_public
    private int capienza;
    //@ spec_public
    private List<Slot> slotList;
    //@ spec_public
    private List<Proiezione> proiezioni;
    //@ spec_public
    private List<Posto> posti;
    //@ spec_public
    private Sede sede;

    //@ public invariant id >= 0;
    //@ public invariant numeroSala >= 0;
    //@ public invariant capienza >= 0;
    //@ public invariant posti == null || !posti.contains(null);
    //@ public invariant slotList == null || !slotList.contains(null);
    //@ public invariant proiezioni == null || !proiezioni.contains(null);
    //@ public invariant sede == null || sede.getId() >= 0;

    public Sala() {
    }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   assignable *;
      @   ensures this.id == id;
      @*/
    public Sala(int id) {
        this.id = id;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == id;
      @*/
    public /*@ pure @*/ int getId() {
        return id;
    }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   assignable id;
      @   ensures this.id == id;
      @*/
    public void setId(int id) {
        this.id = id;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == numeroSala;
      @*/
    public /*@ pure @*/ int getNumeroSala() {
        return numeroSala;
    }

    /*@ public normal_behavior
      @   requires numeroSala >= 0;
      @   assignable numeroSala;
      @   ensures this.numeroSala == numeroSala;
      @*/
    public void setNumeroSala(int numeroSala) {
        this.numeroSala = numeroSala;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == capienza;
      @*/
    public /*@ pure @*/ int getCapienza() {
        return capienza;
    }

    /*@ public normal_behavior
      @   requires capienza >= 0;
      @   assignable capienza;
      @   ensures this.capienza == capienza;
      @*/
    public void setCapienza(int capienza) {
        this.capienza = capienza;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == sede;
      @*/
    public /*@ pure @*/ Sede getSede() {
        return sede;
    }

    /*@ public normal_behavior
      @   requires sede != null;
      @   assignable sede;
      @   ensures this.sede == sede;
      @*/
    public void setSede(Sede sede) {
        this.sede = sede;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == slotList;
      @*/
    public /*@ pure @*/ List<Slot> slotList() {
        return slotList;
    }

    /*@ public normal_behavior
      @   requires slotList != null;
      @   requires !slotList.contains(null);
      @   assignable slotList;
      @   ensures this.slotList == slotList;
      @*/
    public void setSlotList(List<Slot> slotList) {
        this.slotList = slotList;
    }

    /*@ public normal_behavior
      @   requires true;
      @   assignable \nothing;
      @   ensures \result == proiezioni;
      @*/
    public /*@ pure @*/ List<Proiezione> getProiezioni() {
        return proiezioni;
    }

    /*@ public normal_behavior
      @   requires proiezioni != null;
      @   requires !proiezioni.contains(null);
      @   assignable proiezioni;
      @   ensures this.proiezioni == proiezioni;
      @*/
    public void setProiezioni(List<Proiezione> proiezioni) {
        this.proiezioni = proiezioni;
    }

    /*@ public normal_behavior
      @   requires true;
      @   assignable \nothing;
      @   ensures \result == posti;
      @*/
    public /*@ pure @*/ List<Posto> getPosti() {
        return posti;
    }

    /*@ public normal_behavior
      @   requires posti != null;
      @   requires !posti.contains(null);
      @   assignable posti;
      @   ensures this.posti == posti;
      @*/
    public void setPosti(List<Posto> posti) {
        this.posti = posti;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == slotList;
      @*/
    public /*@ pure @*/ List<Slot> getSlotList() {
        return slotList;
    }

    /*@ public normal_behavior
      @   requires this.posti != null;
      @   requires !this.posti.contains(null);
      @   requires slot != null;
      @   requires data != null;
      @   requires film != null;
      @   assignable \nothing;
      @   ensures \result != null;
      @   ensures \result.getDataProiezione() == data;
      @   ensures \result.getFilmProiezione() == film;
      @   ensures \result.getOrarioProiezione() == slot;
      @*/
    public Proiezione aggiungiProiezione(Slot slot, LocalDate data, Film film) {
        Proiezione proiezione = new Proiezione();
        proiezione.setDataProiezione(data);
        proiezione.setFilmProiezione(film);
        proiezione.setOrarioProiezione(slot);
        proiezione.setPostiProiezione(creaListaPosti(proiezione));
        return proiezione;
    }

    /*@ private normal_behavior
      @   requires this.posti != null;
      @   requires !this.posti.contains(null);
      @   assignable \nothing;
      @   ensures \result != null;
      @   ensures \result.size() == this.posti.size();
      @   ensures !\result.contains(null);
      @*/
    private List<PostoProiezione> creaListaPosti(Proiezione proiezione) {
        ArrayList<PostoProiezione> posti = new ArrayList<>();
        /*@ loop_invariant posti != null;
          @ loop_invariant this.posti != null;
          @ loop_invariant posti.size() <= this.posti.size();
          @ loop_invariant (\forall int i; 0 <= i && i < nuoviPosti.size(); nuoviPosti.get(i) != null);
          @ decreases this.posti.size() - posti.size();
          @*/
        for (Posto p : this.posti) {
            posti.add(new PostoProiezione(p, proiezione));
        }
        return posti;
    }

    @Override
    public String toString() {
        return "Sala{" +
                "id=" + id +
                ", numeroSala=" + numeroSala +
                ", capienza=" + capienza +
                ", slotList=" + slotList +
                ", proiezioni=" + proiezioni +
                ", posti=" + posti +
                '}';
    }
}
