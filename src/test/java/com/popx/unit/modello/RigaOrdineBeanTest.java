package com.popx.unit.modello;

import com.popx.modello.RigaOrdineBean;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class RigaOrdineBeanTest {

    @Test
    void defaultConstructor_initialValues() {
        RigaOrdineBean r = new RigaOrdineBean();

        assertEquals(0, r.getOrdineId());
        assertNull(r.getProdottoId());
        assertEquals(0, r.getQuantity());
        assertEquals(0.0f, r.getUnitaryCost(), 0.0001f);
    }

    @Test
    void parameterizedConstructor_setsFieldsCorrectly() {
        int ordineId = 5;
        String prodottoId = "PROD-123";
        int quantity = 10;
        float unitaryCost = 12.5f;

        RigaOrdineBean r = new RigaOrdineBean(ordineId, prodottoId, quantity, unitaryCost);

        assertEquals(ordineId, r.getOrdineId());
        assertEquals(prodottoId, r.getProdottoId());
        assertEquals(quantity, r.getQuantity());
        assertEquals(unitaryCost, r.getUnitaryCost(), 0.0001f);
    }

    @Test
    void settersAndGetters_workCorrectly() {
        RigaOrdineBean r = new RigaOrdineBean();

        r.setOrdineId(2);
        r.setProdottoId("X");
        r.setQuantity(3);
        r.setUnitaryCost(1.25f);

        assertEquals(2, r.getOrdineId());
        assertEquals("X", r.getProdottoId());
        assertEquals(3, r.getQuantity());
        assertEquals(1.25f, r.getUnitaryCost(), 0.0001f);
    }
}
