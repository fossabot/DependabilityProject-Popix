package com.popx.integration.presentazione;

import com.popx.modello.ProdottoBean;
import com.popx.persistenza.ProdottoDAOImpl;
import com.popx.presentazione.UpdateProductServlet;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.Part;
import java.io.ByteArrayInputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.*;

class UpdateProductServletTest {

    private ProdottoDAOImpl prodottoDAO;
    private UpdateProductServlet servlet;

    private HttpServletRequest request;
    private HttpServletResponse response;

    private StringWriter responseBody;
    private PrintWriter writer;

    @BeforeEach
    void setup() throws Exception {
        prodottoDAO = mock(ProdottoDAOImpl.class);
        servlet = new UpdateProductServlet(prodottoDAO);

        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);

        responseBody = new StringWriter();
        writer = new PrintWriter(responseBody);
        when(response.getWriter()).thenReturn(writer);

        // Parametri base comuni
        when(request.getParameter("idProduct")).thenReturn("P001");
        when(request.getParameter("name")).thenReturn("Prodotto");
        when(request.getParameter("description")).thenReturn("Desc");
        when(request.getParameter("price")).thenReturn("10.0");
        when(request.getParameter("qty")).thenReturn("5");
        when(request.getParameter("brand")).thenReturn("Brand");
        when(request.getParameter("figure")).thenReturn("Figure");
        when(request.getParameter("current_img_src")).thenReturn("existing.png");
    }

    /* ===================== SUCCESS PATH ===================== */

    @Test
    void updateProduct_success_withoutImage() throws Exception {
        when(request.getPart("img_src")).thenReturn(null);
        when(prodottoDAO.getProdottoById("P001")).thenReturn(new ProdottoBean());
        when(prodottoDAO.updateProduct(any())).thenReturn(true);

        servlet.doPost(request, response);
        writer.flush();

        verify(prodottoDAO).updateProduct(any());
        assertTrue(responseBody.toString().contains("\"success\":true"));
    }

    /* ===================== INVALID IMAGE ===================== */

    @Test
    void invalidImage_returnsError() throws Exception {
        Part part = mock(Part.class);
        when(part.getSize()).thenReturn(10L);
        when(part.getContentType()).thenReturn("text/plain");
        when(request.getPart("img_src")).thenReturn(part);

        servlet.doPost(request, response);
        writer.flush();

        String json = responseBody.toString();
        assertTrue(json.contains("\"success\":false"));
        assertTrue(json.contains("non è un'immagine valida"));

        verify(prodottoDAO, never()).updateProduct(any());
    }

    /* ===================== DAO EXCEPTION ===================== */

    @Test
    void daoThrowsException_returnsError() throws Exception {
        when(request.getPart("img_src")).thenReturn(null);
        when(prodottoDAO.updateProduct(any()))
                .thenThrow(new RuntimeException("DB error"));

        servlet.doPost(request, response);
        writer.flush();

        assertTrue(responseBody.toString().contains("\"success\":false"));
    }

    /* ===================== EMPTY IMAGE FALLBACK ===================== */

    @Test
    void emptyImagePart_usesExistingImage() throws Exception {
        Part emptyImg = mock(Part.class);
        when(emptyImg.getSize()).thenReturn(0L);
        when(request.getPart("img_src")).thenReturn(emptyImg);

        ProdottoBean existing = new ProdottoBean();
        existing.setImg(new byte[]{9, 9});

        when(prodottoDAO.getProdottoById("P001")).thenReturn(existing);
        when(prodottoDAO.updateProduct(any())).thenReturn(true);

        servlet.doPost(request, response);
        writer.flush();

        verify(prodottoDAO).updateProduct(argThat(p ->
                Arrays.equals(p.getImg(), new byte[]{9, 9})
        ));
    }

    /* ===================== VALID IMAGE UPLOAD (MUTATION KILLER) ===================== */

    @Test
    void validImage_setsImgFromUpload_andUpdatesProduct() throws Exception {
        byte[] uploadedBytes = {1, 2, 3, 4};

        Part imgPart = mock(Part.class);
        when(imgPart.getSize()).thenReturn((long) uploadedBytes.length);
        when(imgPart.getContentType()).thenReturn("image/png");
        when(imgPart.getInputStream())
                .thenReturn(new ByteArrayInputStream(uploadedBytes));

        when(request.getPart("img_src")).thenReturn(imgPart);
        when(prodottoDAO.updateProduct(any())).thenReturn(true);

        servlet.doPost(request, response);
        writer.flush();

        // 🔥 QUESTO UCCIDE IL MUTANTE setImg()
        verify(prodottoDAO).updateProduct(argThat(p ->
                p != null && Arrays.equals(p.getImg(), uploadedBytes)
        ));

        assertTrue(responseBody.toString().contains("\"success\":true"));
    }
}
