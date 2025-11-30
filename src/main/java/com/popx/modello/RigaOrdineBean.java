package com.popx.modello;

import java.io.Serializable;

/*@
  @ public invariant ordineId >= 0;
  @ public invariant prodottoId == null
  @                 || !prodottoId.isEmpty();
  @ public invariant quantity >= 0;
  @ public invariant unitaryCost >= 0;
@*/
public class RigaOrdineBean implements Serializable {

    private int ordineId;
    private String prodottoId;
    private int quantity;
    private float unitaryCost;

    /*@
      @ ensures this.ordineId == 0;
      @ ensures this.prodottoId == null;
      @ ensures this.quantity == 0;
      @ ensures this.unitaryCost == 0.0f;
    @*/
    public RigaOrdineBean() {}

    /*@
      @ requires ordineId >= 0;
      @ requires prodottoId != null && !prodottoId.isEmpty();
      @ requires quantity >= 0;
      @ requires unitaryCost >= 0;
      @ ensures this.ordineId == ordineId;
      @ ensures this.prodottoId == prodottoId;
      @ ensures this.quantity == quantity;
      @ ensures this.unitaryCost == unitaryCost;
    @*/
    public RigaOrdineBean(int ordineId, String prodottoId, int quantity, float unitaryCost) {
        this.ordineId = ordineId;
        this.prodottoId = prodottoId;
        this.quantity = quantity;
        this.unitaryCost = unitaryCost;
    }

    /*@ ensures \result == ordineId; @*/
    public int getOrdineId() {
        return ordineId;
    }

    /*@
      @ requires ordineId >= 0;
      @ ensures this.ordineId == ordineId;
    @*/
    public void setOrdineId(int ordineId) {
        this.ordineId = ordineId;
    }

    /*@ ensures \result == prodottoId; @*/
    public String getProdottoId() {
        return prodottoId;
    }

    /*@
      @ requires prodottoId != null && !prodottoId.isEmpty();
      @ ensures this.prodottoId == prodottoId;
    @*/
    public void setProdottoId(String prodottoId) {
        this.prodottoId = prodottoId;
    }

    /*@ ensures \result == quantity; @*/
    public int getQuantity() {
        return quantity;
    }

    /*@
      @ requires quantity >= 0;
      @ ensures this.quantity == quantity;
    @*/
    public void setQuantity(int quantity) {
        this.quantity = quantity;
    }

    /*@ ensures \result == unitaryCost; @*/
    public float getUnitaryCost() {
        return unitaryCost;
    }

    /*@
      @ requires unitaryCost >= 0;
      @ ensures this.unitaryCost == unitaryCost;
    @*/
    public void setUnitaryCost(float unitaryCost) {
        this.unitaryCost = unitaryCost;
    }
}
