package com.popx.modello;

import java.io.Serializable;
import java.util.Arrays;

public class ProdottoBean implements Serializable {
    /*@ public invariant id != null && !id.isEmpty();
      @ public invariant name != null && !name.isEmpty();
      @ public invariant brand != null && !brand.isEmpty();
      @ public invariant cost >= 0;
      @ public invariant piecesInStock >= 0;
      @ public invariant qty >= 0;
      @ // img, figure e description possono essere null o vuote
      @*/

    private static final long serialVersionUID = 1L;

    private String id;
    private String name;
    private String description;
    private double cost;
    private int piecesInStock;
    private String brand;
    private byte[] img;
    private String figure;

    private int qty;

    // Constructors

    /*@ ensures id == null && name == null && description == null && cost == 0.0
      @      && piecesInStock == 0 && brand == null && img == null && figure == null
      @      && qty == 0;
      @*/
    public ProdottoBean() {
    }

    /*@ requires id != null && !id.isEmpty();
      @ requires name != null && !name.isEmpty();
      @ requires brand != null && !brand.isEmpty();
      @ requires cost >= 0;
      @ requires piecesInStock >= 0;
      @ // description, img, figure possono essere null
      @ ensures this.id == id;
      @ ensures this.name == name;
      @ ensures this.description == description;
      @ ensures this.cost == cost;
      @ ensures this.piecesInStock == piecesInStock;
      @ ensures this.brand == brand;
      @ ensures this.img == img;
      @ ensures this.figure == figure;
      @*/
    public ProdottoBean(String id, String name, String description, double cost, int piecesInStock, String brand, byte[] img, String figure) {
        this.id = id;
        this.name = name;
        this.description = description;
        this.cost = cost;
        this.piecesInStock = piecesInStock;
        this.brand = brand;
        this.img = img;
        this.figure = figure;
    }

    /*@ ensures \result == id; @*/
    public String getId() {
        return id;
    }

    /*@ requires id != null && !id.isEmpty();
      @ ensures this.id == id;
      @*/
    public void setId(String id) {
        this.id = id;
    }

    /*@ ensures \result == name; @*/
    public String getName() {
        return name;
    }

    /*@ requires name != null && !name.isEmpty();
      @ ensures this.name == name;
      @*/
    public void setName(String name) {
        this.name = name;
    }

    /*@ ensures \result == description; @*/
    public String getDescription() {
        return description;
    }

    /*@ // description può essere null o vuota
      @ ensures this.description == description;
      @*/
    public void setDescription(String description) {
        this.description = description;
    }

    /*@ ensures \result == cost; @*/
    public double getCost() {
        return cost;
    }

    /*@ requires cost >= 0;
      @ ensures this.cost == cost;
      @*/
    public void setCost(double cost) {
        this.cost = cost;
    }

    /*@ ensures \result == piecesInStock; @*/
    public int getPiecesInStock() {
        return piecesInStock;
    }

    /*@ requires piecesInStock >= 0;
      @ ensures this.piecesInStock == piecesInStock;
      @*/
    public void setPiecesInStock(int piecesInStock) {
        this.piecesInStock = piecesInStock;
    }

    /*@ ensures \result == brand; @*/
    public String getBrand() {
        return brand;
    }

    /*@ requires brand != null && !brand.isEmpty();
      @ ensures this.brand == brand;
      @*/
    public void setBrand(String brand) {
        this.brand = brand;
    }

    /*@ ensures \result == img; @*/
    public byte[] getImg() {
        return img;
    }

    /*@ // img può essere null
      @ ensures this.img == img;
      @*/
    public void setImg(byte[] img) {
        this.img = img;
    }

    /*@ ensures \result == figure; @*/
    public String getFigure() {
        return figure;
    }

    /*@ // figure può essere null o vuota
      @ ensures this.figure == figure;
      @*/
    public void setFigure(String figure) {
        this.figure = figure;
    }

    /*@ ensures \result == qty; @*/
    public int getQty() {
        return qty;
    }

    /*@ requires qty >= 0;
      @ ensures this.qty == qty;
      @*/
    public void setQty(int qty) {
        this.qty = qty;
    }

    @Override
    public String toString() {
        return "ProdottoBean{" +
                "id='" + id + '\'' +
                ", name='" + name + '\'' +
                ", description='" + description + '\'' +
                ", cost=" + cost +
                ", piecesInStock=" + piecesInStock +
                ", brand='" + brand + '\'' +
                ", img=" + Arrays.toString(img) +
                ", figure='" + figure + '\'' +
                '}';
    }
}
