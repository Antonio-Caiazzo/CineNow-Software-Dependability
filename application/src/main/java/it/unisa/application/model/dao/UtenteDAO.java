package it.unisa.application.model.dao;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.entity.Utente;
import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;

public class UtenteDAO {
    //@ spec_public
    private DataSource ds;

    //@ public invariant ds != null;

    /*@ public normal_behavior
      @   assignable ds;
      @   ensures ds != null;
      @*/
    public UtenteDAO() {
        this.ds = DataSourceSingleton.getInstance();
    }

    /*@ public normal_behavior
      @   requires utente != null;
      @   requires utente.getEmail() != null && !utente.getEmail().isEmpty();
      @   requires utente.getPassword() != null && !utente.getPassword().isEmpty();
      @   requires utente.getRuolo() != null && !utente.getRuolo().isEmpty();
      @   assignable \nothing;
      @   ensures (\result==true) ==> utente.getEmail() != null && utente.getPassword() != null;
      @*/
    public boolean create(Utente utente) {
        String sql = "INSERT INTO utente (email, password, ruolo) VALUES (?, ?, ?)";
        try (Connection conn = ds.getConnection();
             PreparedStatement stmt = conn.prepareStatement(sql)) {
            stmt.setString(1, utente.getEmail());
            stmt.setString(2, utente.getPassword());
            stmt.setString(3, utente.getRuolo());
            return stmt.executeUpdate() > 0;
        } catch (SQLException e) {
            e.printStackTrace();
            return false;
        }
    }

    /*@ public normal_behavior
      @   requires email != null && !email.isEmpty();
      @   assignable \nothing;
      @   ensures \result == null || \result.getEmail().equals(email);
      @*/
    public Utente retrieveByEmail(String email) {
        String sql = "SELECT email, password, ruolo " +
                "FROM utente " +
                "WHERE email = ?";
        try (Connection conn = ds.getConnection();
             PreparedStatement stmt = conn.prepareStatement(sql)) {
            stmt.setString(1, email);
            try (ResultSet rs = stmt.executeQuery()) {
                if (rs.next()) {
                    Utente utente = new Utente();
                    utente.setEmail(rs.getString("email"));
                    utente.setPassword(rs.getString("password"));
                    utente.setRuolo(rs.getString("ruolo"));
                    return utente;
                }
            }
        } catch (SQLException e) {
            e.printStackTrace();
        }
        return null;
    }
}
