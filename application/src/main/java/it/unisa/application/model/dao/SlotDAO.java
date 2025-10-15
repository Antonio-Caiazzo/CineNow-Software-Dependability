package it.unisa.application.model.dao;

import it.unisa.application.database_connection.DataSourceSingleton;
import it.unisa.application.model.entity.Proiezione;
import it.unisa.application.model.entity.Slot;
import javax.sql.DataSource;
import java.sql.*;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

public class SlotDAO {
    //@ spec_public
    private final DataSource ds;

    //@ public invariant ds != null;

    /*@ public normal_behavior
      @   requires true;
      @   ensures this.ds != null;
      @*/
    public SlotDAO() {
        this.ds = DataSourceSingleton.getInstance();
    }
    /*@ public normal_behavior
      @   requires id >= 0;
      @   assignable \nothing;
      @   ensures (\result != null) ==> (\result.getId() == id);
      @*/
    public Slot retrieveById(int id) {
        String sql = "SELECT * FROM slot WHERE id = ?";
        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setInt(1, id);
            ResultSet rs = ps.executeQuery();
            if(rs.next()){
                Slot slot = new Slot();
                slot.setId(rs.getInt("id"));
                slot.setOraInizio(rs.getTime("ora_inizio"));
                return slot;
            }
        } catch (SQLException e) {
            e.printStackTrace();
        }
        return null;
    }
    /*@ public normal_behavior
      @   requires proiezione != null;
      @   requires proiezione.getOrarioProiezione() != null;
      @   assignable \nothing;
      @   ensures (\result != null) ==> (\result.getId() == proiezione.getOrarioProiezione().getId());
      @*/
    public Slot retrieveByProiezione(Proiezione proiezione){
        String sql = "SELECT * FROM slot WHERE id = ?";
        try (Connection connection = ds.getConnection();
             PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setInt(1, proiezione.getOrarioProiezione().getId());
            ResultSet rs = ps.executeQuery();
            if(rs.next()){
                Slot slot = new Slot();
                slot.setId(rs.getInt("id"));
                slot.setOraInizio(rs.getTime("ora_inizio"));
                return slot;
            }
        } catch (SQLException e) {
            e.printStackTrace();
        }
        return null;
    }
    /*@ public normal_behavior
      @   requires true;
      @   assignable \nothing;
      @   ensures \result != null && !\result.contains(null);
      @*/
    public List<Slot> retrieveAllSlots() {
        List<Slot> list = new ArrayList<>();
        String sql = "SELECT * FROM slot ORDER BY ora_inizio";
        try (Connection con = ds.getConnection(); PreparedStatement ps = con.prepareStatement(sql)) {
            ResultSet rs = ps.executeQuery();
            while (rs.next()) {
                Slot s = new Slot();
                s.setId(rs.getInt("id"));
                s.setOraInizio(rs.getTime("ora_inizio"));
                list.add(s);
            }
        } catch (SQLException e) {
            e.printStackTrace();
        }
        return list;
    }
}
