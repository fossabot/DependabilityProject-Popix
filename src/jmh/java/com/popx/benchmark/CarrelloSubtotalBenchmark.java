package com.popx.benchmark;

import com.popx.modello.ProdottoCarrelloBean;
import org.openjdk.jmh.annotations.*;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * Microbenchmark JMH per il calcolo del subtotal del carrello.
 *
 * Il benchmark misura esclusivamente operazioni CPU-bound in-memory,
 * evitando I/O, DAO, servlet o componenti esterni alla JVM.
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@State(Scope.Thread)
public class CarrelloSubtotalBenchmark {

    /**
     * Dimensione del carrello.
     * Simula carrelli piccoli, medi e grandi.
     */
    @Param({"10", "100", "1000"})
    private int cartSize;

    private List<ProdottoCarrelloBean> prodotti;

    /**
     * Setup eseguito fuori dal tempo di misurazione.
     * Prepara una lista di prodotti realistica e deterministica.
     */
    @Setup(Level.Trial)
    public void setup() {
        prodotti = new ArrayList<>(cartSize);
        for (int i = 0; i < cartSize; i++) {
            prodotti.add(new ProdottoCarrelloBean(
                    "user@example.com",
                    "P" + i,
                    2,
                    9.99f
            ));
        }
    }

    /**
     * Calcolo subtotal con ciclo for tradizionale.
     */
    @Benchmark
    public float subtotalWithForLoop() {
        float subtotal = 0.0f;
        for (ProdottoCarrelloBean prodotto : prodotti) {
            subtotal += prodotto.getQuantity() * prodotto.getUnitaryCost();
        }
        return subtotal;
    }

    /**
     * Calcolo subtotal usando Stream API.
     */
    @Benchmark
    public float subtotalWithStreams() {
        return (float) prodotti.stream()
                .mapToDouble(p -> p.getQuantity() * p.getUnitaryCost())
                .sum();
    }
}
