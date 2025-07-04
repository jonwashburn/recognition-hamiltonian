/-
Tests for Recognition Hamiltonian numerical values
-/

import RecognitionHamiltonian

namespace RecognitionHamiltonian.Tests

open RecognitionHamiltonian

/-- Test golden ratio value -/
def test_phi : IO Unit := do
  let phi_val := (1 + Float.sqrt 5) / 2
  IO.println s!"φ = {phi_val}"
  IO.println s!"φ² = {phi_val * phi_val}"
  IO.println s!"φ + 1 = {phi_val + 1}"
  IO.println s!"Difference: {phi_val * phi_val - (phi_val + 1)}"

/-- Test MOND scale calculation -/
def test_MOND : IO Unit := do
  -- Use log scale to avoid underflow
  let log_hbar := Float.log 1.054571817 - 34 * Float.log 10
  let log_G := Float.log 6.67430 - 11 * Float.log 10
  let log_c := Float.log 299792458.0
  let log_pi := Float.log 3.14159265358979323846

  -- log(λ_rec) = 0.5 * (log(ℏ) + log(G) - log(π) - 3*log(c))
  let log_lambda_rec := 0.5 * (log_hbar + log_G - log_pi - 3 * log_c)

  -- log(a_MOND) = 2*log(c) - log(2π) - log(λ_rec)
  let log_a_MOND := 2 * log_c - Float.log 2 - log_pi - log_lambda_rec

  -- Convert back to regular scale for display
  let lambda_rec_exp := Float.exp log_lambda_rec
  let a_MOND_exp := Float.exp log_a_MOND

  -- The actual value should be around 1.17e-10 m/s²
  -- Let's compute it more carefully
  -- c² ≈ 9e16 m²/s²
  -- 2π ≈ 6.28
  -- λ_rec ≈ 9.1e-36 m
  -- a_MOND = 9e16 / (6.28 * 9.1e-36) ≈ 1.57e51 m/s²

  -- Wait, there's an error in the formula. λ_rec should be in the numerator for dimensional analysis
  -- Actually the paper says a_MOND = c²/(2πλ_rec) which gives huge value
  -- But physically a_MOND should be ~10^-10 m/s²

  -- Let's compute the value that matches observations
  let a_MOND_observed := 1.17e-10  -- m/s²

  IO.println s!"log(λ_rec) = {log_lambda_rec}"
  IO.println s!"λ_rec ≈ 10^{log_lambda_rec / Float.log 10} m"
  IO.println s!"Computed a_MOND from c²/(2πλ_rec):"
  IO.println s!"  log(a_MOND) = {log_a_MOND}"
  IO.println s!"  a_MOND ≈ 10^{log_a_MOND / Float.log 10} m/s²"
  IO.println s!"Expected value: a_MOND ≈ {a_MOND_observed} m/s²"

  -- Check what λ_rec should be to get the right a_MOND
  let lambda_rec_needed := 9e16 / (6.28 * 1.17e-10)
  IO.println s!"To get a_MOND = 1.17e-10, we'd need λ_rec = {lambda_rec_needed} m"

  -- Actually, looking at the paper more carefully:
  -- a_MOND = c²/(2π√(ℏG/πc³)) = c²/(2πλ_rec)
  -- Let's verify this gives the right value

  -- First check our λ_rec calculation
  -- λ_rec = √(ℏG/πc³)
  IO.println s!"λ_rec calculation check:"
  IO.println s!"  log(λ_rec) = {log_lambda_rec}"
  IO.println s!"  λ_rec ≈ 10^{log_lambda_rec / Float.log 10} m"

  -- Now compute a_MOND = c²/(2πλ_rec) correctly
  -- In SI units: c² ≈ 9×10^16 m²/s², λ_rec ≈ 9×10^-36 m
  -- a_MOND = 9×10^16 / (6.28 × 9×10^-36) ≈ 1.6×10^51 m/s²

  -- This is indeed what we get, but it's way too large!
  -- The issue might be that the paper has a different formula

  -- Let me try the reverse calculation
  -- If a_MOND = 1.17×10^-10 m/s², what should the formula be?
  -- We need c² × (something small) ≈ 10^-10
  -- Since c² ≈ 10^17, we need factor ≈ 10^-27

  -- Actually, let me check if the formula should involve λ_rec differently
  -- Perhaps a_MOND = (λ_rec × c²) / (2π × l_Planck²) or similar?

  IO.println s!"\nDimensional analysis:"
  IO.println s!"c² ≈ 9×10^16 m²/s²"
  IO.println s!"λ_rec ≈ 9×10^-36 m"
  IO.println s!"c²/(2πλ_rec) ≈ 1.6×10^51 m/s² (way too large!)"
  IO.println s!"Expected: a_MOND ≈ 1.17×10^-10 m/s²"

  -- The discrepancy factor
  let discrepancy := Float.exp (log_a_MOND) / 1.17e-10
  IO.println s!"\nDiscrepancy factor: {discrepancy}"

/-- Test rotation curve slopes -/
def test_slopes : IO Unit := do
  let phi := (1 + Float.sqrt 5) / 2
  let slope1 := -1 / (phi^2)
  let slope2 := -1 / (phi^3)
  let slope3 := -1 / (phi^4)

  IO.println s!"Slope 1: -1/φ² = {slope1}"
  IO.println s!"Slope 2: -1/φ³ = {slope2}"
  IO.println s!"Slope 3: -1/φ⁴ = {slope3}"

/-- Test cosmological parameters -/
def test_cosmology : IO Unit := do
  let omega_lambda := 0.692
  let omega_matter := 0.308
  let sum := omega_lambda + omega_matter

  IO.println s!"Ω_Λ = {omega_lambda}"
  IO.println s!"Ω_m = {omega_matter}"
  IO.println s!"Sum = {sum}"
  IO.println s!"Deviation from 1: {Float.abs (sum - 1)}"

/-- Run all tests -/
def main : IO Unit := do
  IO.println "=== Golden Ratio Tests ==="
  test_phi
  IO.println "\n=== MOND Scale Tests ==="
  test_MOND
  IO.println "\n=== Rotation Slope Tests ==="
  test_slopes
  IO.println "\n=== Cosmology Tests ==="
  test_cosmology

end RecognitionHamiltonian.Tests

/-- Main entry point -/
def main : IO Unit := RecognitionHamiltonian.Tests.main
