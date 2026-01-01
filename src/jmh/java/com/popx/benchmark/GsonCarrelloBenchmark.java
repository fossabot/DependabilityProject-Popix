package com.popx.benchmark;

import com.google.gson.Gson;
import com.popx.modello.ProdottoCarrelloBean;
import org.openjdk.jmh.annotations.*;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * JMH benchmark for JSON serialization and deserialization
 * of cart-related data using Gson.
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Warmup(iterations = 3, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(0)
@State(Scope.Thread)
public class GsonCarrelloBenchmark {

    @Param({"10", "100", "1000"})
    private int cartSize;

    private List<ProdottoCarrelloBean> prodotti;
    private Gson gson;
    private String json;

    @Setup(Level.Trial)
    public void setup() {
        gson = new Gson();
        prodotti = new ArrayList<>(cartSize);

        for (int i = 0; i < cartSize; i++) {
            prodotti.add(new ProdottoCarrelloBean(
                    "user@example.com",
                    "P" + i,
                    1,
                    9.99f
            ));
        }

        // Precompute JSON for deserialization benchmark
        json = gson.toJson(prodotti);
    }

    /**
     * Measures the cost of serializing a cart to JSON.
     */
    @Benchmark
    public String serializeCart() {
        return gson.toJson(prodotti);
    }

    /**
     * Measures the cost of deserializing a cart from JSON.
     */
    @Benchmark
    public List<?> deserializeCart() {
        return gson.fromJson(json, List.class);
    }
}
