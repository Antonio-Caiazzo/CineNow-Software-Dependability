package it.unisa.application.model.entity;

public class Film {
    //@ spec_public
    private int id;
    //@ spec_public
    private String titolo;
    //@ spec_public
    private String genere;
    //@ spec_public
    private String classificazione;
    //@ spec_public
    private int durata;
    //@ spec_public
    private byte[] locandina;
    //@ spec_public
    private String descrizione;
    //@ spec_public
    private boolean isProiettato;

    /*@ public normal_behavior @*/
    public Film() {}

    /*@ public normal_behavior
      @   ensures this.id == id;
      @*/
    public Film(int id) {
        this.id = id;
    }

    /*@ public normal_behavior
      @   ensures this.id == id;
      @   ensures this.titolo == titolo;
      @   ensures this.genere == genere;
      @   ensures this.classificazione == classificazione;
      @   ensures this.durata == durata;
      @   ensures this.locandina == locandina;
      @   ensures this.descrizione == descrizione;
      @   ensures this.isProiettato == isProiettato;
      @*/
    public Film(int id, String titolo, String genere, String classificazione, int durata,
                byte[] locandina, String descrizione, boolean isProiettato) {
        this.id = id;
        this.titolo = titolo;
        this.genere = genere;
        this.classificazione = classificazione;
        this.durata = durata;
        this.locandina = locandina;
        this.descrizione = descrizione;
        this.isProiettato = isProiettato;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == id;
      @*/
    /*@ pure @*/
    public int getId() { return id; }

    /*@ public normal_behavior
      @   assignable this.id;
      @   ensures this.id == id;
      @*/
    public void setId(int id) { this.id = id; }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == titolo;
      @*/
    /*@ pure @*/
    public String getTitolo() { return titolo; }

    /*@ public normal_behavior
      @   assignable this.titolo;
      @   ensures this.titolo == titolo;
      @*/
    public void setTitolo(String titolo) { this.titolo = titolo; }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == genere;
      @*/
    /*@ pure @*/
    public String getGenere() { return genere; }

    /*@ public normal_behavior
      @   assignable this.genere;
      @   ensures this.genere == genere;
      @*/
    public void setGenere(String genere) { this.genere = genere; }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == classificazione;
      @*/
    /*@ pure @*/
    public String getClassificazione() { return classificazione; }

    /*@ public normal_behavior
      @   assignable this.classificazione;
      @   ensures this.classificazione == classificazione;
      @*/
    public void setClassificazione(String classificazione) { this.classificazione = classificazione; }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == durata;
      @*/
    /*@ pure @*/
    public int getDurata() { return durata; }

    /*@ public normal_behavior
      @   assignable this.durata;
      @   ensures this.durata == durata;
      @*/
    public void setDurata(int durata) { this.durata = durata; }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == locandina;
      @*/
    /*@ pure @*/
    public byte[] getLocandina() { return locandina; }

    /*@ public normal_behavior
      @   assignable this.locandina;
      @   ensures this.locandina == locandina;
      @*/
    public void setLocandina(byte[] locandina) { this.locandina = locandina; }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == descrizione;
      @*/
    /*@ pure @*/
    public String getDescrizione() { return descrizione; }

    /*@ public normal_behavior
      @   assignable this.descrizione;
      @   ensures this.descrizione == descrizione;
      @*/
    public void setDescrizione(String descrizione) { this.descrizione = descrizione; }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == isProiettato;
      @*/
    /*@ pure @*/
    public boolean isProiettato() { return isProiettato; }

    /*@ public normal_behavior
      @   assignable this.isProiettato;
      @   ensures this.isProiettato == proiettato;
      @*/
    public void setProiettato(boolean proiettato) { isProiettato = proiettato; }

    @Override
    public String toString() {
        return "Film{" +
                "id=" + id +
                ", titolo='" + titolo + '\'' +
                ", genere='" + genere + '\'' +
                ", classificazione='" + classificazione + '\'' +
                ", durata=" + durata +
                ", locandina='" + locandina + '\'' +
                ", descrizione='" + descrizione + '\'' +
                ", isProiettato=" + isProiettato +
                '}';
    }
}
