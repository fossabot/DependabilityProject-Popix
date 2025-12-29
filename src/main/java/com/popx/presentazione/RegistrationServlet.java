package com.popx.presentazione;

import com.popx.modello.UserBean;
import com.popx.servizio.AuthenticationService;

import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import java.io.IOException;

@WebServlet("/register")
public class RegistrationServlet extends HttpServlet {

    private final AuthenticationService authService;

    // Costruttore usato in produzione
    public RegistrationServlet() {
        this.authService = new AuthenticationService();
    }

    // Costruttore usato nei test (dependency injection)
    public RegistrationServlet(AuthenticationService authService) {
        this.authService = authService;
    }

    @Override
    public void doPost(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        response.setContentType("application/json");
        response.setCharacterEncoding("UTF-8");

        String username = request.getParameter("username");
        String email = request.getParameter("email");
        String password = request.getParameter("password");

        try {
            if (authService.isEmailRegistered(email)) {
                response.getWriter().write(
                        "{\"status\":\"error\",\"message\":\"Email già registrata.\"}"
                );
                return;
            }

            UserBean user = new UserBean();
            user.setUsername(username);
            user.setEmail(email);
            user.setPassword(password);
            user.setRole("User");

            boolean registered = authService.registerUser(user);

            if (registered) {
                response.getWriter().write(
                        "{\"status\":\"success\",\"message\":\"Registrazione avvenuta con successo.\","
                                + "\"redirect\":\"" + request.getContextPath() + "/jsp/HomePage.jsp\"}"
                );
            } else {
                response.getWriter().write(
                        "{\"status\":\"error\",\"message\":\"Errore sconosciuto durante la registrazione.\"}"
                );
            }

        } catch (Exception e) {
            response.getWriter().write(
                    "{\"status\":\"error\",\"message\":\"" + e.getMessage() + "\"}"
            );
        }
    }
}
