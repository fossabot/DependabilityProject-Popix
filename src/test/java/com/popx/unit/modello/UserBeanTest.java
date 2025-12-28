package com.popx.unit.modello;

import com.popx.modello.UserBean;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class UserBeanTest {

    @Test
    void userBean_gettersAndSetters_workCorrectly() {
        UserBean user = new UserBean();

        user.setUsername("Mario");
        user.setEmail("mario@example.com");
        user.setPassword("secret");
        user.setRole("User");

        assertEquals("Mario", user.getUsername());
        assertEquals("mario@example.com", user.getEmail());
        assertEquals("secret", user.getPassword());
        assertEquals("User", user.getRole());

        assertNotNull(user.toString());
    }
}
