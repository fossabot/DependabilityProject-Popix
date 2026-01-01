package com.popx.benchmark;

import com.popx.modello.ProdottoBean;
import org.openjdk.jmh.annotations.*;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

/**
 * JMH benchmark for in-memory catalog filtering.
 *
 * This benchmark simulates post-processing of a product catalog already
 * retrieved from the database, applying multiple combinable filters.
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Warmup(iterations = 3, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(0)
@State(Scope.Thread)
public class CatalogFilteringBenchmark {

    @Param({"30", "300", "3000"})
    private int catalogSize;

    private List<ProdottoBean> catalog;

    // Filtri simulati
    private String brandFilter = "Naruto";
    private double minPrice = 10.0;
    private double maxPrice = 50.0;
    private String nameFilter = "figure";

    @Setup(Level.Trial)
    public void setup() {
        catalog = new ArrayList<>(catalogSize);

        for (int i = 0; i < catalogSize; i++) {
            ProdottoBean p = new ProdottoBean();
            p.setId("P" + i);
            p.setName("figure_" + i);
            p.setBrand(i % 2 == 0 ? "Naruto" : "Dragon Ball");
            p.setCost(5 + (i % 100));
            catalog.add(p);
        }
    }

    /**
     * Filters implemented using imperative style (for-loop).
     */
    @Benchmark
    public List<ProdottoBean> filterWithForLoop() {
        List<ProdottoBean> result = new ArrayList<>();

        for (ProdottoBean p : catalog) {
            if (!p.getBrand().equals(brandFilter)) {
                continue;
            }
            if (p.getCost() < minPrice || p.getCost() > maxPrice) {
                continue;
            }
            if (!p.getName().contains(nameFilter)) {
                continue;
            }
            result.add(p);
        }
        return result;
    }

    /**
     * Filters implemented using Java Stream API.
     */
    @Benchmark
    public List<ProdottoBean> filterWithStreams() {
        return catalog.stream()
                .filter(p -> p.getBrand().equals(brandFilter))
                .filter(p -> p.getCost() >= minPrice && p.getCost() <= maxPrice)
                .filter(p -> p.getName().contains(nameFilter))
                .collect(Collectors.toList());
    }
}
