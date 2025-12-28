package com.popx.unit.modello;

import com.popx.modello.CarrelloBean;
import com.popx.modello.ProdottoCarrelloBean;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class CarrelloBeanTest {

    @Test
    void carrelloBean_gettersAndSetters_workCorrectly() {
        CarrelloBean carrello = new CarrelloBean();

        // default constructor -> campi null
        assertNull(carrello.getClienteEmail());
        assertNull(carrello.getProdottiCarrello());

        // impostazione tramite setter
        carrello.setClienteEmail("cliente@example.com");
        List<ProdottoCarrelloBean> prodotti = new ArrayList<>(); // lista vuota valida
        carrello.setProdottiCarrello(prodotti);

        assertEquals("cliente@example.com", carrello.getClienteEmail());
        assertSame(prodotti, carrello.getProdottiCarrello());

        // costruttore parametrizzato
        CarrelloBean carrello2 = new CarrelloBean("altro@example.com", prodotti);
        assertEquals("altro@example.com", carrello2.getClienteEmail());
        assertSame(prodotti, carrello2.getProdottiCarrello());

        // toString non nullo
        assertNotNull(carrello.toString());
    }
}
