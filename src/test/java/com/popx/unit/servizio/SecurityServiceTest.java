package com.popx.unit.servizio;

import com.popx.servizio.SecurityService;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class SecurityServiceTest {

    @Test
    void constructor_canBeInstantiated_forCoverage() {
        // Only to cover the implicit default constructor in JaCoCo
        assertNotNull(new SecurityService());
    }

    @Test
    void hashPassword_returnsValidBcryptHash() {
        String password = "ValidPassword123!";
        String hash = SecurityService.hashPassword(password);

        assertNotNull(hash);
        assertFalse(hash.isBlank());
        assertNotEquals(password, hash);

        // Typical BCrypt format starts with $2a$, $2b$ or $2y$
        assertTrue(hash.startsWith("$2"), "BCrypt hash should start with $2");
    }

    @Test
    void checkPassword_correctPassword_returnsTrue() {
        String password = "ValidPassword123!";
        String hash = SecurityService.hashPassword(password);

        assertTrue(SecurityService.checkPassword(password, hash));
    }

    @Test
    void checkPassword_wrongPassword_returnsFalse() {
        String password = "ValidPassword123!";
        String hash = SecurityService.hashPassword(password);

        assertFalse(SecurityService.checkPassword("WrongPassword!", hash));
    }
}
