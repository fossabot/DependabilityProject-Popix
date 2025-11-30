package com.popx.persistenza;

import com.popx.modello.CarrelloBean;

public interface CarrelloDAO {

    /*@ public normal_behavior
      @   requires carrello != null
      @        && carrello.getClienteEmail() != null && !carrello.getClienteEmail().isEmpty();
      @   assignable \everything;
      @*/
    void salvaCarrello(CarrelloBean carrello);

    /*@ public normal_behavior
      @   requires email != null && !email.isEmpty();
      @   assignable \everything;
      @   ensures \result != null && \result.getClienteEmail().equals(email);
      @*/
    CarrelloBean ottieniCarrelloPerEmail(String email);

    /*@ public normal_behavior
      @   requires email != null && !email.isEmpty();
      @   assignable \everything;
      @*/
    void clearCartByUserEmail(String email);
}
