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
      @   ensures this.id == id;
      @*/
    public Sala(int id) {
        this.id = id;
    }

    /*@ public normal_behavior
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
      @   assignable \nothing;
      @   ensures \result == numeroSala;
      @*/
    /*@ pure @*/
    public int getNumeroSala() {
        return numeroSala;
    }

    /*@ public normal_behavior
      @   requires numeroSala >= 0;
      @   assignable this.numeroSala;
      @   ensures this.numeroSala == numeroSala;
      @*/
    public void setNumeroSala(int numeroSala) {
        this.numeroSala = numeroSala;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == capienza;
      @*/
    /*@ pure @*/
    public int getCapienza() {
        return capienza;
    }

    /*@ public normal_behavior
      @   requires capienza >= 0;
      @   assignable this.capienza;
      @   ensures this.capienza == capienza;
      @*/
    public void setCapienza(int capienza) {
        this.capienza = capienza;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == sede;
      @*/
    /*@ pure @*/
    public Sede getSede() {
        return sede;
    }

    /*@ public normal_behavior
      @   requires sede != null;
      @   assignable this.sede;
      @   ensures this.sede == sede;
      @*/
    public void setSede(Sede sede) {
        this.sede = sede;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == slotList;
      @*/
    /*@ pure @*/
    public List<Slot> slotList() {
        return slotList;
    }

    /*@ public normal_behavior
      @   requires slotList != null;
      @   requires !slotList.contains(null);
      @   assignable this.slotList;
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
    /*@ pure @*/
    public List<Proiezione> getProiezioni() {
        return proiezioni;
    }

    /*@ public normal_behavior
      @   requires proiezioni != null;
      @   requires !proiezioni.contains(null);
      @   assignable this.proiezioni;
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
    /*@ pure @*/
    public List<Posto> getPosti() {
        return posti;
    }

    /*@ public normal_behavior
      @   requires posti != null;
      @   requires !posti.contains(null);
      @   assignable this.posti;
      @   ensures this.posti == posti;
      @*/
    public void setPosti(List<Posto> posti) {
        this.posti = posti;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == slotList;
      @*/
    /*@ pure @*/
    public List<Slot> getSlotList() {
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
          @ loop_invariant (\forall int i; 0 <= i && i < posti.size(); posti.get(i) != null);
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
