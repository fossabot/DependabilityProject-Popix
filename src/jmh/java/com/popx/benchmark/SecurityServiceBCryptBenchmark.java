package com.popx.benchmark;

import com.popx.servizio.SecurityService;
import org.openjdk.jmh.annotations.*;

import java.util.concurrent.TimeUnit;

/**
 * JMH benchmark for Pop!x SecurityService password hashing and verification.
 *
 * Notes:
 * - This is CPU-bound and intentionally expensive (BCrypt).
 * - Measures the project's own abstraction (SecurityService) rather than calling BCrypt directly.
 * - Results should be interpreted as relative/indicative, not as absolute end-to-end login performance.
 */
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@Warmup(iterations = 3, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(0)
@State(Scope.Thread)
public class SecurityServiceBCryptBenchmark {

    /**
     * Password length affects hashing time slightly.
     * Using a few representative sizes avoids unrealistic extremes.
     */
    @Param({"12", "24", "48"})
    private int passwordLen;

    private String password;
    private String precomputedHash;

    @Setup(Level.Trial)
    public void setup() {
        password = "A".repeat(passwordLen);

        // Precompute a reference hash once per trial,
        // so verification measures only checkPassword cost.
        precomputedHash = SecurityService.hashPassword(password);
    }

    /**
     * Measures the cost of hashing via the project's SecurityService.
     * This includes generating a new salt (cost factor fixed in SecurityService).
     */
    @Benchmark
    public String hashPassword() {
        return SecurityService.hashPassword(password);
    }

    /**
     * Measures the cost of verifying a password against an existing BCrypt hash.
     */
    @Benchmark
    public boolean checkPassword() {
        return SecurityService.checkPassword(password, precomputedHash);
    }
}
