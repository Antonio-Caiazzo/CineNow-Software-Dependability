package it.unisa.application.sottosistemi.gestione_sede.service;

import it.unisa.application.model.dao.ProiezioneDAO;
import it.unisa.application.model.dao.SedeDAO;
import it.unisa.application.model.entity.Film;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.model.entity.Sede;

import java.sql.SQLException;
import java.time.LocalDate;
import java.util.*;
import java.util.stream.Collectors;

public class ProgrammazioneSedeService {
    //@ spec_public
    private final ProiezioneDAO proiezioneDAO;

    public ProgrammazioneSedeService() {
        this.proiezioneDAO = new ProiezioneDAO();
    }

    public ProgrammazioneSedeService(ProiezioneDAO proiezioneDAO) {
        this.proiezioneDAO = proiezioneDAO;
    }

    //@ public invariant proiezioneDAO != null;
    /**
     * Restituisce la programmazione futura della sede specificata.
     */
    /*@ public normal_behavior
      @   requires sedeId >= 0;
      @   assignable \nothing;
      @   ensures \result != null && !\result.contains(null);
      @*/
    public List<Proiezione> getProgrammazione(int sedeId) {
        List<Proiezione> programmazioni = proiezioneDAO.retrieveAllBySede(sedeId);
        LocalDate today = LocalDate.now();
        List<Proiezione> proiezioniFuture = programmazioni.stream()
                .filter(p -> !p.getDataProiezione().isBefore(today))
                .sorted((p1, p2) -> {
                    if (!p1.getDataProiezione().equals(p2.getDataProiezione())) {
                        return p1.getDataProiezione().compareTo(p2.getDataProiezione());
                    }
                    return p1.getOrarioProiezione().getOraInizio().compareTo(p2.getOrarioProiezione().getOraInizio());
                })
                .toList();

        return proiezioniFuture;
    }



    /**
     * Restituisce le proiezioni del film in una sede per la settimana corrente.
     */
    /*@ public normal_behavior
      @   requires filmId >= 0;
      @   requires sedeId >= 0;
      @   assignable \nothing;
      @   ensures \result != null && !\result.contains(null);
      @*/
    public List<Proiezione> getProiezioniFilm(int filmId, int sedeId){
        List<Proiezione> proiezioni = proiezioneDAO.retrieveByFilm(new Film(filmId),new Sede(sedeId));
        return proiezioni.stream()
                .filter(p -> !p.getDataProiezione().isBefore(LocalDate.now()) &&
                        !p.getDataProiezione().isAfter(LocalDate.now().plusDays(7)))
                .collect(Collectors.toList());

    }

    /**
     * Restituisce il catalogo dei film programmati in una sede.
     */
    /*@ public normal_behavior
      @   requires sede != null;
      @   requires sede.getId() >= 0;
      @   assignable \nothing;
      @   ensures \result == null || !\result.contains(null);
      @*/
    public List<Film> getCatalogoSede(Sede sede){
        SedeDAO sedeDAO = new SedeDAO();
        List<Film> catalogo;
        try {
            catalogo = sedeDAO.retrieveFilm(sede.getId());
        } catch (SQLException e) {
            throw new RuntimeException(e);
        }
        return catalogo;
    }
}
