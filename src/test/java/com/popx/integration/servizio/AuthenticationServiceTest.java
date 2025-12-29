package com.popx.integration.servizio;

import com.popx.modello.UserBean;
import com.popx.persistenza.DataSourceSingleton;
import com.popx.servizio.AuthenticationService;
import org.h2.jdbcx.JdbcDataSource;
import org.junit.jupiter.api.*;

import java.sql.Connection;
import java.sql.Statement;

import static org.junit.jupiter.api.Assertions.*;

class AuthenticationServiceTest {

    private AuthenticationService authService;
    private JdbcDataSource dataSource;

    @BeforeEach
    void setupDatabase() throws Exception {

        // 🔹 H2 in-memory database
        dataSource = new JdbcDataSource();
        dataSource.setURL("jdbc:h2:mem:testdb;DB_CLOSE_DELAY=-1");
        dataSource.setUser("sa");
        dataSource.setPassword("");

        // 🔹 Override del DataSource singleton
        DataSourceSingleton.setInstanceForTest(dataSource);

        // 🔹 Init service
        authService = new AuthenticationService();

        try (Connection conn = dataSource.getConnection();
             Statement stmt = conn.createStatement()) {

            // 🔥 IDPOTENTE
            stmt.execute("DROP TABLE IF EXISTS Cliente");
            stmt.execute("DROP TABLE IF EXISTS UtenteRegistrato");

            stmt.execute("""
                CREATE TABLE UtenteRegistrato (
                    username VARCHAR(50),
                    email VARCHAR(100) PRIMARY KEY,
                    password VARCHAR(255),
                    role VARCHAR(20)
                )
            """);

            stmt.execute("""
                CREATE TABLE Cliente (
                    utente_registrato_email VARCHAR(100) PRIMARY KEY,
                    FOREIGN KEY (utente_registrato_email)
                    REFERENCES UtenteRegistrato(email)
                )
            """);
        }
    }

    // ---------- REGISTER + LOGIN FLOW ----------

    @Test
    void registerAndLogin_successful() throws Exception {

        UserBean user = new UserBean(
                "Mario",
                "mario@example.com",
                "password123",
                "User"
        );

        // Register
        boolean registered = authService.registerUser(user);
        assertTrue(registered);

        // Login
        UserBean logged = authService.login("mario@example.com", "password123");

        assertNotNull(logged);
        assertEquals("mario@example.com", logged.getEmail());
        assertEquals("User", logged.getRole());
    }

    @Test
    void login_wrongPassword_fails() throws Exception {

        UserBean user = new UserBean(
                "Luigi",
                "luigi@example.com",
                "correctPwd",
                "User"
        );

        authService.registerUser(user);

        Exception ex = assertThrows(
                Exception.class,
                () -> authService.login("luigi@example.com", "wrongPwd")
        );

        assertEquals("Invalid credentials", ex.getMessage());
    }

    @Test
    void register_existingUser_fails() throws Exception {

        UserBean user = new UserBean(
                "Peach",
                "peach@example.com",
                "pwd",
                "User"
        );

        authService.registerUser(user);

        Exception ex = assertThrows(
                Exception.class,
                () -> authService.registerUser(user)
        );

        assertEquals("User already exists", ex.getMessage());
    }
}
