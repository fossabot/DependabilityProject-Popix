package com.popx.persistenza;

import com.popx.modello.OrdineBean;

import java.util.List;

public interface OrdineDAO {

    /*@ public normal_behavior
      @   requires ordine != null
      @        && ordine.getSubtotal() >= 0
      @        && ordine.getCustomerEmail() != null && !ordine.getCustomerEmail().isEmpty()
      @        && ordine.getStatus() != null && !ordine.getStatus().isEmpty()
      @        && ordine.getDataOrdine() != null;
      @   assignable \everything;
      @*/
    boolean insertOrdine(OrdineBean ordine);

    /*@ public normal_behavior
      @   requires id > 0;
      @   assignable \everything;
      @*/
    OrdineBean getOrdineById(int id);

    /*@ public normal_behavior
      @   assignable \everything;
      @*/
    List<OrdineBean> getAllOrdini();

    /*@ public normal_behavior
      @   requires clienteEmail != null && !clienteEmail.isEmpty();
      @   assignable \everything;
      @*/
    List<OrdineBean> getOrdiniByCliente(String clienteEmail);

    /*@ public normal_behavior
      @   requires email != null && !email.isEmpty();
      @   assignable \everything;
      @*/
    int countOrdiniByCliente(String email);

    /*@ public normal_behavior
      @   requires email != null && !email.isEmpty()
      @        && currentPage >= 1
      @        && itemsPerPage > 0;
      @   assignable \everything;
      @*/
    List<OrdineBean> getOrdiniByClientePaginati(String email, int currentPage, int itemsPerPage);

    /*@ public normal_behavior
      @   requires currentPage >= 1 && recordsPerPage > 0;
      @   assignable \everything;
      @*/
    List<OrdineBean> getOrdiniPaginati(int currentPage, int recordsPerPage);

    /*@ public normal_behavior
      @   assignable \everything;
      @*/
    int countTuttiOrdini();

    /*@ public normal_behavior
      @   requires ordineBean != null
      @        && ordineBean.getId() > 0
      @        && ordineBean.getStatus() != null && !ordineBean.getStatus().isEmpty();
      @   assignable \everything;
      @*/
    boolean updateStatus(OrdineBean ordineBean);
}
