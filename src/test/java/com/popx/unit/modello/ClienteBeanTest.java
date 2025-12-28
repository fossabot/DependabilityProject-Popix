package com.popx.unit.modello;

import com.popx.modello.ClienteBean;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class ClienteBeanTest {

    @Test
    void defaultConstructor_setsFieldsToNull() {
        ClienteBean cliente = new ClienteBean();

        assertNull(cliente.getUsername());
        assertNull(cliente.getEmail());
        assertNull(cliente.getPassword());
        assertNull(cliente.getRole());
    }

    @Test
    void parameterizedConstructor_setsFieldsCorrectly() {
        String username = "clienteUser";
        String email = "cliente@example.com";
        String password = "Passw0rd1"; // contiene minuscole, maiuscole e cifre, lunghezza valida
        String role = "User";

        ClienteBean cliente = new ClienteBean(username, email, password, role);

        assertEquals(username, cliente.getUsername());
        assertEquals(email, cliente.getEmail());
        assertEquals(password, cliente.getPassword());
        assertEquals("User", cliente.getRole());

        assertNotNull(cliente.toString());
    }
}
