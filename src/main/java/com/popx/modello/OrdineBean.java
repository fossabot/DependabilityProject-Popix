package com.popx.modello;

import java.sql.Date;

public class OrdineBean {

    /*@ public invariant id >= 0;
      @ public invariant subtotal >= 0;
      @ public invariant customerEmail == null
      @                 || !customerEmail.isEmpty();
      @ public invariant status != null && !status.isEmpty();
      @ public invariant dataOrdine == null
      @                 || dataOrdine.getTime() >= 0;   // Data valida (non futura non esprimibile in JML)
      @*/
    private int id;
    private float subtotal;
    private String customerEmail;
    private String status = "In elaborazione";
    private Date dataOrdine;

    /*@
      @ ensures this.id == 0;
      @ ensures this.subtotal == 0.0f;
      @ ensures this.customerEmail == null;
      @ ensures this.status.equals("In elaborazione");
      @ ensures this.dataOrdine == null;
      @*/
    public OrdineBean() {}

    /*@
      @ requires subtotal >= 0;
      @ requires customerEmail != null && !customerEmail.isEmpty();
      @ // dataOrdine può essere null
      @ ensures this.id == 0;
      @ ensures this.subtotal == subtotal;
      @ ensures this.customerEmail == customerEmail;
      @ ensures this.status.equals("In elaborazione");
      @ ensures this.dataOrdine == dataOrdine;
      @*/
    public OrdineBean(float subtotal, String customerEmail, Date dataOrdine) {
        this.subtotal = subtotal;
        this.customerEmail = customerEmail;
        this.dataOrdine = dataOrdine;
    }

    /*@ ensures \result == id; @*/
    public int getId() { return id; }

    /*@ requires id >= 0;
      @ ensures this.id == id;
      @*/
    public void setId(int id) { this.id = id; }

    /*@ ensures \result == subtotal; @*/
    public float getSubtotal() { return subtotal; }

    /*@ requires subtotal >= 0;
      @ ensures this.subtotal == subtotal;
      @*/
    public void setSubtotal(float subtotal) { this.subtotal = subtotal; }

    /*@ ensures \result == customerEmail; @*/
    public String getCustomerEmail() { return customerEmail; }

    /*@
      @ requires customerEmail != null && !customerEmail.isEmpty();
      @ ensures this.customerEmail == customerEmail;
      @*/
    public void setCustomerEmail(String customerEmail) {
        this.customerEmail = customerEmail;
    }

    /*@ ensures \result == status; @*/
    public String getStatus() { return status; }

    /*@
      @ requires status != null && !status.isEmpty();
      @ ensures this.status == status;
      @*/
    public void setStatus(String status) { this.status = status; }

    /*@ ensures \result == dataOrdine; @*/
    public Date getDataOrdine() { return dataOrdine; }

    /*@
      @ // dataOrdine può essere null
      @ ensures this.dataOrdine == dataOrdine;
      @*/
    public void setDataOrdine(Date dataOrdine) {
        this.dataOrdine = dataOrdine;
    }
}
