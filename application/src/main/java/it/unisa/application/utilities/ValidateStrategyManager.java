package it.unisa.application.utilities;

import java.util.HashMap;
import java.util.Map;

public class ValidateStrategyManager {
    //@ spec_public
    private Map<String, ValidatorStrategy> validators;

    //@ public invariant validators != null;
    //@ public invariant !validators.containsKey(null);
    //@ public invariant !validators.containsValue(null);

    /**
     * Costruisce un manager senza validatori registrati.
     */
    /*@ public normal_behavior
      @   requires true;
      @   assignable validators;
      @   ensures this.validators != null;
      @   ensures this.validators.isEmpty();
      @*/
    public ValidateStrategyManager() {
        this.validators = new HashMap<>();
    }

    /**
     * Registra un nuovo validatore.
     */
    /*@ public normal_behavior
      @   requires campo != null && !campo.isEmpty();
      @   requires validator != null;
      @   assignable validators, validators.*;
      @   ensures this.validators.get(campo) == validator;
      @*/
    public void addValidator(String campo, ValidatorStrategy validator) {
        validators.put(campo, validator);
    }

    /**
     * Valida un insieme di input sfruttando i validatori registrati.
     */
    /*@ public normal_behavior
      @   requires inputs != null;
      @   assignable \nothing;
      @   ensures \result ==> (\forall Map.Entry<String, ValidatorStrategy> e; validators.entrySet().contains(e); inputs.get(e.getKey()) != null && e.getValue().validate(inputs.get(e.getKey())));
      @*/
    public boolean validate(Map<String, String> inputs) {
        int processed = 0;
        /*@ loop_invariant 0 <= processed && processed <= validators.size();
          @ decreases validators.size() - processed;
          @*/
        for (Map.Entry<String, ValidatorStrategy> entry : validators.entrySet()) {
            String campo = entry.getKey();
            ValidatorStrategy validator = entry.getValue();
            String input = inputs.get(campo);
            if (input == null || !validator.validate(input)) {
                return false;
            }
            processed++;
        }
        return true;
    }
}

