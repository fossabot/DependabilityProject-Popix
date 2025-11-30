package com.popx.persistenza;

import com.popx.modello.ProdottoBean;

import java.sql.SQLException;
import java.util.List;
import javax.servlet.http.HttpSession;

public interface ProdottoDAO {

    /*@ public normal_behavior
      @   requires prodotto != null
      @        && prodotto.getId() != null && !prodotto.getId().isEmpty()
      @        && prodotto.getName() != null && !prodotto.getName().isEmpty()
      @        && prodotto.getBrand() != null && !prodotto.getBrand().isEmpty()
      @        && prodotto.getCost() >= 0
      @        && prodotto.getPiecesInStock() >= 0;
      @   assignable \everything;
      @*/
    boolean saveProdotto(ProdottoBean prodotto);

    /*@ public normal_behavior
      @   requires id != null && !id.isEmpty();
      @   assignable \everything;
      @*/
    ProdottoBean getProdottoById(String id);

    /*@ public normal_behavior
      @   assignable \everything;
      @   ensures \result != null;
      @*/
    List<ProdottoBean> getAllProducts();

    /*@ public normal_behavior
      @   requires brand != null && !brand.isEmpty();
      @   assignable \everything;
      @   ensures \result != null;
      @*/
    List<ProdottoBean> getProdottiByBrand(String brand);

    /*@ public normal_behavior
      @   requires brand != null && !brand.isEmpty();
      @   assignable \everything;
      @   ensures \result != null;
      @*/
    List<ProdottoBean> getProdottiByBrandAndPrice(String brand, boolean ascending);

    /*@ public normal_behavior
      @   assignable \everything;
      @   ensures \result != null;
      @*/
    List<ProdottoBean> getProdottiSortedByPrice(boolean ascending);

    /*@ public normal_behavior
      @   requires id != null && !id.isEmpty();
      @   assignable \everything;
      @*/
    byte[] getProductImageById(String id);

    /*@ public normal_behavior
      @   requires limit > 0;
      @   assignable \everything;
      @*/
    List<ProdottoBean> getRandomProducts(int limit) throws SQLException;

    /*@ public normal_behavior
      @   requires session != null
      @        && productId != null && !productId.isEmpty()
      @        && qty >= 0;
      @   assignable \everything;
      @*/
    void updateProductQtyInCart(HttpSession session, String productId, int qty);

    /*@ public normal_behavior
      @   requires session != null
      @        && productId != null && !productId.isEmpty();
      @   assignable \everything;
      @*/
    int getProductQtyInCart(HttpSession session, String productId);

    /*@ public normal_behavior
      @   requires userEmail != null && !userEmail.isEmpty()
      @        && cart != null;
      @   assignable \everything;
      @*/
    void saveCartToDatabase(String userEmail, List<ProdottoBean> cart) throws SQLException;

    /*@ public normal_behavior
      @   requires userEmail != null && !userEmail.isEmpty();
      @   assignable \everything;
      @*/
    List<ProdottoBean> getCartByUserEmail(String userEmail) throws SQLException;

    /*@ public normal_behavior
      @   requires userEmail != null && !userEmail.isEmpty()
      @        && productId != null && !productId.isEmpty()
      @        && qty >= 0;
      @   assignable \everything;
      @*/
    void updateCartProductQuantityInDatabase(String userEmail, String productId, int qty) throws SQLException;

    /*@ public normal_behavior
      @   requires userEmail != null && !userEmail.isEmpty()
      @        && productId != null && !productId.isEmpty();
      @   assignable \everything;
      @*/
    void removeProductFromCart(String userEmail, String productId) throws SQLException;

    /*@ public normal_behavior
      @   requires id != null && !id.isEmpty();
      @   assignable \everything;
      @*/
    void deleteProductById(String id) throws SQLException;

    /*@ public normal_behavior
      @   requires prodottoBean != null
      @        && prodottoBean.getId() != null && !prodottoBean.getId().isEmpty();
      @   assignable \everything;
      @*/
    boolean updateProduct(ProdottoBean prodottoBean);

    /*@ public normal_behavior
      @   requires productId != null && !productId.isEmpty()
      @        && quantity >= 0;
      @   assignable \everything;
      @*/
    void updateStock(String productId, int quantity) throws SQLException;
}

