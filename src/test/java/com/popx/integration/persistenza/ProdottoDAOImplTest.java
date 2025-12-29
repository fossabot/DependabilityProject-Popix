package com.popx.integration.persistenza;

import com.popx.modello.ProdottoBean;
import com.popx.persistenza.DataSourceSingleton;
import com.popx.persistenza.ProdottoDAOImpl;
import org.h2.jdbcx.JdbcDataSource;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.sql.Connection;
import java.sql.Statement;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class ProdottoDAOImplTest {

    private ProdottoDAOImpl prodottoDAO;

    @BeforeEach
    void setupDatabase() throws Exception {
        JdbcDataSource ds = new JdbcDataSource();
        ds.setURL("jdbc:h2:mem:testdb;MODE=MySQL;DB_CLOSE_DELAY=-1");
        ds.setUser("sa");
        ds.setPassword("");

        DataSourceSingleton.setInstanceForTest(ds);

        try (Connection conn = ds.getConnection();
             Statement stmt = conn.createStatement()) {

            stmt.execute("""
                CREATE TABLE IF NOT EXISTS Prodotto (
                    id VARCHAR(10) PRIMARY KEY,
                    name VARCHAR(100),
                    description TEXT,
                    cost DOUBLE,
                    pieces_in_stock INT,
                    img BLOB,
                    brand VARCHAR(100),
                    figure VARCHAR(100)
                )
            """);

            stmt.execute("""
                CREATE TABLE IF NOT EXISTS Carrello (
                    id INT AUTO_INCREMENT PRIMARY KEY,
                    cliente_email VARCHAR(100) UNIQUE
                )
            """);

            stmt.execute("""
                CREATE TABLE IF NOT EXISTS ProdottoCarrello (
                    carrello_id INT,
                    prodotto_id VARCHAR(10),
                    quantity INT,
                    unitary_cost DOUBLE,
                    PRIMARY KEY (carrello_id, prodotto_id)
                )
            """);

            stmt.execute("""
                CREATE TABLE IF NOT EXISTS ProductAssociations (
                    product_id_1 VARCHAR(10),
                    product_id_2 VARCHAR(10)
                )
            """);

            stmt.execute("DELETE FROM ProductAssociations");
            stmt.execute("DELETE FROM ProdottoCarrello");
            stmt.execute("DELETE FROM Carrello");
            stmt.execute("DELETE FROM Prodotto");
        }

        prodottoDAO = new ProdottoDAOImpl();
    }

    // --------------------------------------------------
    // BASIC PRODUCT CRUD
    // --------------------------------------------------

    @Test
    void save_and_getProdottoById() {
        ProdottoBean p = new ProdottoBean(
                "P1", "Prod1", "Desc", 10.0, 5, "BrandA", null, "Fig"
        );

        assertTrue(prodottoDAO.saveProdotto(p));

        ProdottoBean loaded = prodottoDAO.getProdottoById("P1");
        assertNotNull(loaded);
        assertEquals("Prod1", loaded.getName());
    }

    @Test
    void getAllProducts_returnsAll() {
        prodottoDAO.saveProdotto(new ProdottoBean("A", "A", "D", 1, 1, "B", null, "F"));
        prodottoDAO.saveProdotto(new ProdottoBean("B", "B", "D", 2, 2, "B", null, "F"));

        List<ProdottoBean> list = prodottoDAO.getAllProducts();
        assertEquals(2, list.size());
    }

    @Test
    void getProdottiByBrand_filtersCorrectly() {
        prodottoDAO.saveProdotto(new ProdottoBean("A", "A", "D", 1, 1, "X", null, "F"));
        prodottoDAO.saveProdotto(new ProdottoBean("B", "B", "D", 2, 2, "Y", null, "F"));

        List<ProdottoBean> result = prodottoDAO.getProdottiByBrand("X");
        assertEquals(1, result.size());
        assertEquals("A", result.get(0).getId());
    }

    @Test
    void getProdottiByBrandAndPrice_ordersCorrectly() {
        prodottoDAO.saveProdotto(new ProdottoBean("A", "A", "D", 30, 1, "B", null, "F"));
        prodottoDAO.saveProdotto(new ProdottoBean("B", "B", "D", 10, 1, "B", null, "F"));

        List<ProdottoBean> asc = prodottoDAO.getProdottiByBrandAndPrice("B", true);
        assertEquals("B", asc.get(0).getId());
    }

    @Test
    void getProdottiSortedByPrice_ordersCorrectly() {
        prodottoDAO.saveProdotto(new ProdottoBean("A", "A", "D", 5, 1, "B", null, "F"));
        prodottoDAO.saveProdotto(new ProdottoBean("B", "B", "D", 15, 1, "B", null, "F"));

        List<ProdottoBean> desc = prodottoDAO.getProdottiSortedByPrice(false);
        assertEquals("B", desc.get(0).getId());
    }

    @Test
    void getRandomProducts_returnsLimited() throws Exception {
        prodottoDAO.saveProdotto(new ProdottoBean("A", "A", "D", 1, 1, "B", null, "F"));
        prodottoDAO.saveProdotto(new ProdottoBean("B", "B", "D", 2, 1, "B", null, "F"));

        List<ProdottoBean> list = prodottoDAO.getRandomProducts(1);
        assertEquals(1, list.size());
    }

    @Test
    void getProductImageById_returnsImage() {
        byte[] img = new byte[]{1, 2, 3};
        ProdottoBean p = new ProdottoBean("IMG", "I", "D", 1, 1, "B", img, "F");

        prodottoDAO.saveProdotto(p);

        byte[] loaded = prodottoDAO.getProductImageById("IMG");
        assertArrayEquals(img, loaded);
    }

    @Test
    void updateStock_updatesCorrectly() throws Exception {
        prodottoDAO.saveProdotto(new ProdottoBean("S", "S", "D", 1, 10, "B", null, "F"));

        prodottoDAO.updateStock("S", 3);

        assertEquals(3, prodottoDAO.getProdottoById("S").getPiecesInStock());
    }

    @Test
    void updateProduct_updatesMainTableEvenWithoutCart() {
        ProdottoBean p = new ProdottoBean("U", "Old", "D", 1, 5, "B", null, "F");
        prodottoDAO.saveProdotto(p);

        p.setName("New");
        p.setCost(99);

        assertTrue(prodottoDAO.updateProduct(p));
        assertEquals("New", prodottoDAO.getProdottoById("U").getName());
    }

    @Test
    void deleteProductById_removesProduct() throws Exception {
        prodottoDAO.saveProdotto(new ProdottoBean("D", "D", "D", 1, 1, "B", null, "F"));

        prodottoDAO.deleteProductById("D");

        assertNull(prodottoDAO.getProdottoById("D"));
    }

    // --------------------------------------------------
    // CART DATABASE METHODS
    // --------------------------------------------------

    @Test
    void saveCartToDatabase_and_getCartByUserEmail() throws Exception {
        ProdottoBean p = new ProdottoBean("C1", "C", "D", 10, 5, "B", null, "F");
        p.setQty(2);

        prodottoDAO.saveProdotto(p);
        prodottoDAO.saveCartToDatabase("user@test.com", List.of(p));

        List<ProdottoBean> cart = prodottoDAO.getCartByUserEmail("user@test.com");

        assertEquals(1, cart.size());
        assertEquals(2, cart.get(0).getQty());
    }

    @Test
    void updateCartProductQuantityInDatabase_updatesQuantity() throws Exception {
        ProdottoBean p = new ProdottoBean("C2", "C", "D", 10, 5, "B", null, "F");
        p.setQty(1);

        prodottoDAO.saveProdotto(p);
        prodottoDAO.saveCartToDatabase("u@test.com", List.of(p));

        prodottoDAO.updateCartProductQuantityInDatabase("u@test.com", "C2", 5);

        assertEquals(5, prodottoDAO.getCartByUserEmail("u@test.com").get(0).getQty());
    }

    @Test
    void removeProductFromCart_removesEntry() throws Exception {
        ProdottoBean p = new ProdottoBean("C3", "C", "D", 10, 5, "B", null, "F");
        p.setQty(1);

        prodottoDAO.saveProdotto(p);
        prodottoDAO.saveCartToDatabase("del@test.com", List.of(p));

        prodottoDAO.removeProductFromCart("del@test.com", "C3");

        assertTrue(prodottoDAO.getCartByUserEmail("del@test.com").isEmpty());
    }

    // --------------------------------------------------
    // ASSOCIATIONS
    // --------------------------------------------------

    @Test
    void isAssociatedWith_true_whenAssociationExists() throws Exception {
        try (Connection conn = DataSourceSingleton.getInstance().getConnection();
             Statement stmt = conn.createStatement()) {

            stmt.execute("""
                INSERT INTO ProductAssociations (product_id_1, product_id_2)
                VALUES ('A', 'B')
            """);
        }

        assertTrue(prodottoDAO.isAssociatedWith("A", "B"));
    }

    @Test
    void isAssociatedWith_false_whenNoAssociation() throws Exception {
        assertFalse(prodottoDAO.isAssociatedWith("X", "Y"));
    }
}
