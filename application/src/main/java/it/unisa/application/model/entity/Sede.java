package it.unisa.application.model.entity;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class Sede {
    //@ spec_public
    private String nome;
    //@ spec_public
    private String indirizzo;
    //@ spec_public
    private int id;
    //@ spec_public
    private Set<Sala> sale;

    //@ public invariant id >= 0;
    //@ public invariant nome == null || !nome.isEmpty();
    //@ public invariant indirizzo == null || !indirizzo.isEmpty();
    //@ public invariant sale != null;
    //@ public invariant !sale.contains(null);

    /*@ public normal_behavior
      @   assignable sale;
      @   ensures sale != null;
      @   ensures sale.isEmpty();
      @*/
    public Sede(){
        sale = new HashSet<>();
    }
    /*@ public normal_behavior
      @   requires id >= 0;
      @   assignable id, sale;
      @   ensures this.id == id;
      @   ensures this.sale != null;
      @   ensures this.sale.isEmpty();
      @*/
    public Sede(int id){
        this.id = id;
        sale = new HashSet<>();
    }
    /*@ public normal_behavior
      @   requires id >= 0;
      @   requires nome != null && !nome.isEmpty();
      @   requires indirizzo != null && !indirizzo.isEmpty();
      @   assignable id, nome, indirizzo, sale;
      @   ensures this.id == id;
      @   ensures this.nome == nome;
      @   ensures this.indirizzo == indirizzo;
      @   ensures this.sale != null;
      @   ensures this.sale.isEmpty();
      @*/
    public Sede(int id, String nome, String indirizzo){
        this.id = id;
        this.nome = nome;
        this.indirizzo = indirizzo;
        this.sale = new HashSet<>();
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == nome;
      @*/
    public /*@ pure @*/ String getNome() {
        return nome;
    }

    /*@ public normal_behavior
      @   requires nome != null && !nome.isEmpty();
      @   assignable nome;
      @   ensures this.nome == nome;
      @*/
    public void setNome(String nome) {
        this.nome = nome;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == indirizzo;
      @*/
    public /*@ pure @*/ String getIndirizzo() {
        return indirizzo;
    }

    /*@ public normal_behavior
      @   requires indirizzo != null && !indirizzo.isEmpty();
      @   assignable indirizzo;
      @   ensures this.indirizzo == indirizzo;
      @*/
    public void setIndirizzo(String indirizzo) {
        this.indirizzo = indirizzo;
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
      @   ensures \result == sale;
      @*/
    public /*@ pure @*/ Set<Sala> getSale() {
        return sale;
    }

    /*@ public normal_behavior
      @   requires sale != null;
      @   requires !sale.contains(null);
      @   assignable sale;
      @   ensures this.sale == sale;
      @*/
    public void setSale(Set<Sala> sale) {
        this.sale = sale;
    }

    /*@ public normal_behavior
      @   requires sale != null;
      @   requires (\forall Sala s; sale.contains(s); s.getProiezioni() != null);
      @   assignable \nothing;
      @   ensures \result != null;
      @*/
    public List<Proiezione> getProgrammazione() {
        return sale.stream().
                flatMap(sala -> sala.getProiezioni().stream())
                .collect(Collectors.toList());
    }

    /*@ public normal_behavior
      @   requires sale != null;
      @   requires (\forall Sala s; sale.contains(s); s.getProiezioni() != null);
      @   requires film != null;
      @   assignable \nothing;
      @   ensures \result != null;
      @*/
    public List<Proiezione> getProiezioniFilm(Film film) {
        return sale.stream()
                .flatMap(sala -> sala.getProiezioni().stream())
                .filter(proiezione -> proiezione.getFilmProiezione().equals(film))
                .collect(Collectors.toList());
    }

    @Override
    public String toString() {
        return "Sede{" +
                "nome='" + nome + '\'' +
                ", indirizzo='" + indirizzo + '\'' +
                ", id=" + id +
                ", sale=" + sale +
                '}';
    }
}
