package com.popx.presentazione;

import com.popx.modello.OrdineBean;
import com.popx.persistenza.OrdineDAO;
import com.popx.persistenza.OrdineDAOImpl;

import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.*;
import java.io.IOException;
import java.util.logging.Level;
import java.util.logging.Logger;

@WebServlet("/UpdateOrderStatus")
public class UpdateStatusServlet extends HttpServlet {

    private final OrdineDAO ordineDAO;
    private static final Logger LOGGER = Logger.getLogger(UpdateStatusServlet.class.getName());

    // 👉 production
    public UpdateStatusServlet() {
        this.ordineDAO = new OrdineDAOImpl();
    }

    // 👉 test
    public UpdateStatusServlet(OrdineDAO ordineDAO) {
        this.ordineDAO = ordineDAO;
    }

    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        response.setContentType("application/json");

        String idParam = request.getParameter("id");
        String newStatus = request.getParameter("status");

        if (idParam == null || newStatus == null) {
            response.setStatus(HttpServletResponse.SC_BAD_REQUEST);
            response.getWriter().write("{\"success\": false}");
            return;
        }

        int orderId;
        try {
            orderId = Integer.parseInt(idParam);
        } catch (NumberFormatException e) {
            response.setStatus(HttpServletResponse.SC_BAD_REQUEST);
            response.getWriter().write("{\"success\": false}");
            return;
        }

        try {
            OrdineBean ordine = ordineDAO.getOrdineById(orderId);
            if (ordine == null) {
                response.setStatus(HttpServletResponse.SC_NOT_FOUND);
                response.getWriter().write("{\"success\": false}");
                return;
            }

            ordine.setStatus(newStatus);
            boolean success = ordineDAO.updateStatus(ordine);

            response.getWriter().write("{\"success\": " + success + "}");

        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Error updating order status in UpdateStatusServlet", e);
            response.setStatus(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            response.getWriter().write("{\"success\": false}");
        }
    }
}
