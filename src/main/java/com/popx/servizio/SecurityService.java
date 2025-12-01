package com.popx.servizio;

import org.mindrot.jbcrypt.BCrypt;

public class SecurityService {

    /*@
      @ public normal_behavior
      @ requires password != null && !password.isEmpty();
      @
      @ // L’hash è sempre non nullo e diverso dalla password in chiaro
      @ ensures \result != null;
      @ ensures !\result.equals(password);
      @
      @ // Un hash valido BCrypt inizia sempre con "$2"
      @ ensures \result.startsWith("$2");
      @*/
    public static String hashPassword(String password) {
        int costFactor = 12;
        String salt = BCrypt.gensalt(costFactor);
        return BCrypt.hashpw(password, salt);
    }

    /*@
      @ public normal_behavior
      @ requires password != null && !password.isEmpty();
      @ requires hashedPassword != null && !hashedPassword.isEmpty();
      @
      @ // L’output è sempre booleano
      @ ensures \result == true || \result == false;
      @*/
    public static boolean checkPassword(String password, String hashedPassword) {
        return BCrypt.checkpw(password, hashedPassword);
    }
}
