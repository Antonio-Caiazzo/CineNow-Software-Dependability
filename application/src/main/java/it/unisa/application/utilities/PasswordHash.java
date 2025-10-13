package it.unisa.application.utilities;

import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

public class PasswordHash {
    /**
     * Applica l'algoritmo SHA-512 alla password fornita.
     */
    /*@ public normal_behavior
      @   requires password != null && password.length() > 0;
      @   assignable \nothing;
      @   ensures (\result == null) || \result.length() > 0;
      @*/
    public static /*@ pure @*/ String hash(String password) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-512");
            byte[] hash = digest.digest(password.getBytes());
            StringBuilder hexString = new StringBuilder();
            /*@ loop_invariant 0 <= i && i <= hash.length;
              @ loop_invariant hexString != null;
              @ decreases hash.length - i;
              @*/
            for (int i = 0; i < hash.length; i++) {
                byte b = hash[i];
                String hex = Integer.toHexString(0xff & b);
                if (hex.length() == 1) {
                    hexString.append('0');
                }
                hexString.append(hex);
            }
            return hexString.toString();
        } catch (NoSuchAlgorithmException e) {
            return null;
        }
    }
}
