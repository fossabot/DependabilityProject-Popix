package com.popx.persistenza;

import com.popx.modello.UserBean;
import java.sql.SQLException;

/*@
  @ public normal_behavior
  @ requires email != null && !email.isEmpty();
  @ ensures \result == null
  @      || \result.getEmail().equals(email);
  @ signals (SQLException) true;
  @*/
public /*@ pure @*/ interface UserDAO<T extends UserBean> {

    T getUserByEmail(String email) throws SQLException;

    /*@
      @ public normal_behavior
      @ requires user != null;
      @ requires user.getEmail() != null && !user.getEmail().isEmpty();
      @ ensures \result == true || \result == false;
      @ signals (SQLException) true;
      @*/
    boolean saveUser(T user) throws SQLException;
}
