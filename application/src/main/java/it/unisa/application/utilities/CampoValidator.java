package it.unisa.application.utilities;

public class CampoValidator implements ValidatorStrategy {
    /*@ also public normal_behavior
      @   requires true;
      @   assignable \nothing;
      @   ensures (campo == null || campo.length() == 0) ==> !\result;
      @   ensures \result ==> (campo != null && campo.length() > 0);
      @*/
    @Override
    public boolean validate(String campo) {
        if (campo == null || campo.trim().isEmpty()) {
            return false;
        }
        return !containsInvalidCharacters(campo);
    }
}


