package com.popx.unit.modello;

import com.popx.modello.GestoreOrdineBean;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class GestoreOrdineBeanTest {

    @Test
    void defaultConstructor_setsFieldsToNull() {
        GestoreOrdineBean gestore = new GestoreOrdineBean();

        assertNull(gestore.getUsername());
        assertNull(gestore.getEmail());
        assertNull(gestore.getPassword());
        assertNull(gestore.getRole());
    }

    @Test
    void parameterizedConstructor_setsFieldsCorrectly() {
        String username = "gestoreUser";
        String email = "gestore@example.com";
        String password = "Passw0rd1"; // almeno una minuscola, una maiuscola e una cifra, lunghezza valida
        String role = "Gestore";

        GestoreOrdineBean gestore = new GestoreOrdineBean(username, email, password, role);

        assertEquals(username, gestore.getUsername());
        assertEquals(email, gestore.getEmail());
        assertEquals(password, gestore.getPassword());
        assertEquals("Gestore", gestore.getRole());

        assertNotNull(gestore.toString());
    }
}
