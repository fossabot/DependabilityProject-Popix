package com.popx.persistenza;

import com.popx.modello.RigaOrdineBean;

import java.util.List;

public interface RigaOrdineDAO {

    /*@ public normal_behavior
      @   requires rigaOrdine != null
      @        && rigaOrdine.getOrdineId() > 0
      @        && rigaOrdine.getProdottoId() != null && !rigaOrdine.getProdottoId().isEmpty()
      @        && rigaOrdine.getQuantity() >= 0
      @        && rigaOrdine.getUnitaryCost() >= 0;
      @   assignable \everything;
      @*/
    void addRigaOrdine(RigaOrdineBean rigaOrdine);

    /*@ public normal_behavior
      @   requires ordineId > 0;
      @   assignable \everything;
      @   ensures \result != null;
      @*/
    List<RigaOrdineBean> getRigheOrdineByOrdineId(int ordineId);

    /*@ public normal_behavior
      @   requires rigaOrdine != null
      @        && rigaOrdine.getOrdineId() > 0
      @        && rigaOrdine.getProdottoId() != null && !rigaOrdine.getProdottoId().isEmpty()
      @        && rigaOrdine.getQuantity() >= 0
      @        && rigaOrdine.getUnitaryCost() >= 0;
      @   assignable \everything;
      @*/
    void updateRigaOrdine(RigaOrdineBean rigaOrdine);

    /*@ public normal_behavior
      @   requires ordineId > 0
      @        && prodottoId != null && !prodottoId.isEmpty();
      @   assignable \everything;
      @*/
    void deleteRigaOrdine(int ordineId, String prodottoId);
}
