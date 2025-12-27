package com.popx.servizio;

import com.popx.modello.UserBean;
import com.popx.persistenza.UserDAO;
import com.popx.persistenza.UserDAOImpl;

/*@ public invariant userDAO != null; @*/
public class AuthenticationService {

    private UserDAO userDAO;

    /*@ ensures this.userDAO != null; @*/
    public AuthenticationService() {
        // Production / integration behavior (UNCHANGED)
        this.userDAO = new UserDAOImpl();
    }

    /*@
      @ requires userDAO != null;
      @ ensures this.userDAO == userDAO;
      @*/
    public AuthenticationService(UserDAO userDAO) {
        this.userDAO = userDAO;
    }

    /*@
      @ public normal_behavior
      @ requires email != null && !email.isEmpty();
      @ requires password != null && !password.isEmpty();
      @
      @ ensures \result != null ==>
      @      (\result.getEmail().equals(email));
      @
      @ signals (Exception e)
      @      e.getMessage().equals("Invalid credentials");
      @*/
    public UserBean login(String email, String password) throws Exception {
        UserBean user = userDAO.getUserByEmail(email);

        if (user != null && SecurityService.checkPassword(password, user.getPassword())) {
            return user;
        }
        throw new Exception("Invalid credentials");
    }

    /*@
      @ public normal_behavior
      @ requires user != null;
      @ requires user.getEmail() != null && !user.getEmail().isEmpty();
      @
      @ ensures \result == true || \result == false;
      @ signals (Exception e)
      @      e.getMessage().equals("User already exists");
      @*/
    public boolean registerUser(UserBean user) throws Exception {
        if (userDAO.getUserByEmail(user.getEmail()) == null) {
            return userDAO.saveUser(user);
        }
        throw new Exception("User already exists");
    }

    /*@
      @ public normal_behavior
      @ requires email != null && !email.isEmpty();
      @ ensures \result == true || \result == false;
      @ signals (Exception) true;
      @*/
    public boolean isEmailRegistered(String email) throws Exception {
        return userDAO.getUserByEmail(email) != null;
    }

    /*@
      @ public normal_behavior
      @ requires email != null && !email.isEmpty();
      @ ensures \result != null;
      @ ensures \result.equals( userDAO.getUserByEmail(email).getRole() );
      @ signals (Exception) true;
      @*/
    public String retrieveRole(String email) throws Exception {
        UserBean user = userDAO.getUserByEmail(email);
        return user.getRole();
    }
}
