package it.unisa.application.model.entity;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

public class Proiezione {
    //@ spec_public
    private int id;
    //@ spec_public
    private Film filmProiezione;
    //@ spec_public
    private Sala salaProiezione;
    //@ spec_public
    private LocalDate dataProiezione;
    //@ spec_public
    private List<PostoProiezione> postiProiezione;
    //@ spec_public
    private Slot orarioProiezione;

    //@ public invariant id >= 0;
    //@ public invariant postiProiezione != null;
    //@ public invariant !postiProiezione.contains(null);
    //@ public invariant salaProiezione == null || salaProiezione.getId() >= 0;
    //@ public invariant filmProiezione == null || filmProiezione.getId() >= 0;
    //@ public invariant orarioProiezione == null || orarioProiezione.getId() >= 0;

    /*@ public normal_behavior
      @   requires true;
      @   assignable *;
      @   ensures this.id == 0;
      @   ensures postiProiezione != null;
      @   ensures postiProiezione.isEmpty();
      @   ensures this.filmProiezione == null;
      @   ensures this.salaProiezione == null;
      @   ensures this.dataProiezione == null;
      @   ensures this.orarioProiezione == null;
      @*/
    public Proiezione() {
        postiProiezione = new ArrayList<PostoProiezione>();
    }

    /*@ public normal_behavior
      @   requires id >= 0;
      @   requires salaProiezione != null;
      @   requires filmProiezione != null;
      @   requires dataProiezione != null;
      @   requires postiProiezione != null;
      @   requires !postiProiezione.contains(null);
      @   requires orarioProiezione != null;
      @   assignable *;
      @   ensures this.id == id;
      @   ensures this.salaProiezione == salaProiezione;
      @   ensures this.filmProiezione == filmProiezione;
      @   ensures this.dataProiezione == dataProiezione;
      @   ensures this.postiProiezione == postiProiezione;
      @   ensures this.orarioProiezione == orarioProiezione;
      @*/
    public Proiezione(int id, Sala salaProiezione, Film filmProiezione, LocalDate dataProiezione, List<PostoProiezione> postiProiezione, Slot orarioProiezione) {
        this.id = id;
        this.salaProiezione = salaProiezione;
        this.filmProiezione = filmProiezione;
        this.dataProiezione = dataProiezione;
        this.postiProiezione = postiProiezione;
        this.orarioProiezione = orarioProiezione;
    }

    /*@ public normal_behavior
      @   requires i >= 0;
      @   assignable *;
      @   ensures this.id == i;
      @   ensures this.postiProiezione != null;
      @   ensures this.postiProiezione.isEmpty();
      @*/
    public Proiezione(int i) {
        this.id = i;
        this.postiProiezione = new ArrayList<>();
    }

    /*@ public normal_behavior
      @   requires true;
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
      @   requires true;
      @   assignable \nothing;
      @   ensures \result == filmProiezione;
      @*/
    public /*@ pure @*/ Film getFilmProiezione() {
        return filmProiezione;
    }

    /*@ public normal_behavior
      @   requires filmProiezione != null;
      @   assignable filmProiezione;
      @   ensures this.filmProiezione == filmProiezione;
      @*/
    public void setFilmProiezione(Film filmProiezione) {
        this.filmProiezione = filmProiezione;
    }

    /*@ public normal_behavior
      @   requires true;
      @   assignable \nothing;
      @   ensures \result == salaProiezione;
      @*/
    public /*@ pure @*/ Sala getSalaProiezione() {
        return salaProiezione;
    }

    /*@ public normal_behavior
      @   requires salaProiezione != null;
      @   assignable salaProiezione;
      @   ensures this.salaProiezione == salaProiezione;
      @*/
    public void setSalaProiezione(Sala salaProiezione) {
        this.salaProiezione = salaProiezione;
    }

    /*@ public normal_behavior
      @   requires true;
      @   assignable \nothing;
      @   ensures \result == dataProiezione;
      @*/
    public /*@ pure @*/ LocalDate getDataProiezione() {
        return dataProiezione;
    }

    /*@ public normal_behavior
      @   requires dataProiezione != null;
      @   assignable dataProiezione;
      @   ensures this.dataProiezione == dataProiezione;
      @*/
    public void setDataProiezione(LocalDate dataProiezione) {
        this.dataProiezione = dataProiezione;
    }

    /*@ public normal_behavior
      @   requires true;
      @   assignable \nothing;
      @   ensures \result == postiProiezione;
      @*/
    public /*@ pure @*/ List<PostoProiezione> getPostiProiezione() {
        return postiProiezione;
    }

    /*@ public normal_behavior
      @   requires postiProiezione != null;
      @   requires !postiProiezione.contains(null);
      @   assignable postiProiezione;
      @   ensures this.postiProiezione == postiProiezione;
      @*/
    public void setPostiProiezione(List<PostoProiezione> postiProiezione) {
        this.postiProiezione = postiProiezione;
    }

    /*@ public normal_behavior
      @   requires true;
      @   assignable \nothing;
      @   ensures \result == orarioProiezione;
      @*/
    public /*@ pure @*/ Slot getOrarioProiezione() {
        return orarioProiezione;
    }

    /*@ public normal_behavior
      @   requires orarioProiezione != null;
      @   assignable orarioProiezione;
      @   ensures this.orarioProiezione == orarioProiezione;
      @*/
    public void setOrarioProiezione(Slot orarioProiezione) {
        this.orarioProiezione = orarioProiezione;
    }

    @Override
    public String toString() {
        return "Proiezione{" +
                "id=" + id +
                ", filmProiezione=" + filmProiezione +
                ", salaProiezione=" + salaProiezione +
                ", dataProiezione=" + dataProiezione +
                ", postiProiezione=" + postiProiezione +
                ", orarioProiezione=" + orarioProiezione +
                '}';
    }
}
