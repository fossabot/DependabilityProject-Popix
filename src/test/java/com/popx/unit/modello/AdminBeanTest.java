package com.popx.unit.modello;

import com.popx.modello.AdminBean;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class AdminBeanTest {

    @Test
    void defaultConstructor_setsFieldsToNull() {
        AdminBean admin = new AdminBean();

        assertNull(admin.getUsername());
        assertNull(admin.getEmail());
        assertNull(admin.getPassword());
        assertNull(admin.getRole());
    }

    @Test
    void parameterizedConstructor_setsFieldsCorrectly() {
        String username = "adminUser";
        String email = "admin@example.com";
        String password = "Passw0rd1"; // contiene minuscole, maiuscole e cifre, lunghezza valida
        String role = "Admin";

        AdminBean admin = new AdminBean(username, email, password, role);

        assertEquals(username, admin.getUsername());
        assertEquals(email, admin.getEmail());
        assertEquals(password, admin.getPassword());
        assertEquals("Admin", admin.getRole());

        assertNotNull(admin.toString());
    }
}
