package it.unisa.application.utilities;

public interface ValidatorStrategy {
    /**
     * Valida un campo testuale secondo la strategia specifica.
     */
    /*@ public normal_behavior
      @   requires campo != null;
      @   assignable \nothing;
      @   ensures \result ==> !containsInvalidCharacters(campo);
      @*/
    boolean validate(String campo);

    /**
     * Verifica la presenza di caratteri non ammessi.
     */
    /*@ public normal_behavior
      @   requires campo != null;
      @   assignable \nothing;
      @   ensures \result ==> campo.matches(".*[<>\"%;()&].*");
      @*/
    default boolean containsInvalidCharacters(String campo) {
        String invalidCharactersPattern = "[<>\"%;()&]";
        return campo.matches(".*" + invalidCharactersPattern + ".*");
    }
}

