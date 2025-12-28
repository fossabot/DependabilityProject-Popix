package com.popx.unit.modello;

import com.popx.modello.ProdottoCarrelloBean;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class ProdottoCarrelloBeanTest {

    @Test
    void defaultConstructor_initialValues() {
        ProdottoCarrelloBean p = new ProdottoCarrelloBean();

        assertNull(p.getClienteEmail());
        assertNull(p.getProdottoId());
        assertEquals(0, p.getQuantity());
        assertEquals(0.0f, p.getUnitaryCost(), 0.0001f);
    }

    @Test
    void parameterizedConstructor_setsFieldsCorrectly() {
        String email = "cliente@example.com";
        String prodottoId = "PROD-1";
        int quantity = 3;
        float unitaryCost = 9.99f;

        ProdottoCarrelloBean p = new ProdottoCarrelloBean(email, prodottoId, quantity, unitaryCost);

        assertEquals(email, p.getClienteEmail());
        assertEquals(prodottoId, p.getProdottoId());
        assertEquals(quantity, p.getQuantity());
        assertEquals(unitaryCost, p.getUnitaryCost(), 0.0001f);
        assertNotNull(p.toString());
    }

    @Test
    void settersAndGetters_workCorrectly() {
        ProdottoCarrelloBean p = new ProdottoCarrelloBean();

        p.setClienteEmail("u@e.it");
        p.setProdottoId("P-99");
        p.setQuantity(7);
        p.setUnitaryCost(1.5f);

        assertEquals("u@e.it", p.getClienteEmail());
        assertEquals("P-99", p.getProdottoId());
        assertEquals(7, p.getQuantity());
        assertEquals(1.5f, p.getUnitaryCost(), 0.0001f);
    }
}