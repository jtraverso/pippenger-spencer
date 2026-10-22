/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.Eventually12

/-! # Theorem 1.2 of Ehard–Glock–Joos (statement and proof)

**Theorem 1.2.** Suppose `δ ∈ (0,1)` and `r ∈ ℕ` with `r ≥ 2`, and let `ε := δ / (50 r²)`.
Then there exists `Δ₀` such that for all `Δ ≥ Δ₀` the following holds. Let `H` be an
`r`-uniform hypergraph with `Δ(H) ≤ Δ`, `Δ_c(H) ≤ Δ^{1-δ}` and `e(H) ≤ exp(Δ^{ε²})`. Suppose
that `W` is a set of at most `exp(Δ^{ε²})` weight functions on `E(H)`. Then there is a matching
`M` in `H` such that `ω(M) = (1 ± Δ^{-ε}) ω(E(H)) / Δ` for all `ω ∈ W` with
`ω(E(H)) ≥ max_{e ∈ E(H)} ω(e) Δ^{1+δ}`.

Formalization choices:
* The family `W` is an indexed family `W : ι → (Finset V → ℝ)` over a finite type `ι`
  (repetitions are allowed, which only makes the statement more general).
* Weights only need to be nonnegative on the edges of `H`.
* The condition `ω(E(H)) ≥ max_e ω(e) Δ^{1+δ}` is written edge by edge; for nonempty `H` this
  is the same condition, and for empty `H` both sides of the conclusion are `0`.
* `ω(M) = (1 ± Δ^{-ε}) ω(E(H))/Δ` is written as `|ω(M) - ω(E(H))/Δ| ≤ Δ^{-ε} ω(E(H))/Δ`.
-/

@[expose] public section

namespace Pseudorandom

open Finset

/-- **Theorem 1.2** (Ehard–Glock–Joos). -/
theorem theorem_1_2 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (r : ℕ) (hr : 2 ≤ r) :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ ≤ Δ →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)),
      IsUniform H r →
      (∀ v, (degree H v : ℝ) ≤ Δ) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ Δ ^ (1 - δ)) →
      (H.card : ℝ) ≤ Real.exp (Δ ^ ((δ / (50 * r ^ 2)) ^ 2)) →
      ∀ (ι : Type) [Fintype ι] (W : ι → Finset V → ℝ),
      (∀ k, ∀ e ∈ H, 0 ≤ W k e) →
      (Fintype.card ι : ℝ) ≤ Real.exp (Δ ^ ((δ / (50 * r ^ 2)) ^ 2)) →
      ∃ M ⊆ H, IsMatching M ∧
        ∀ k, (∀ e ∈ H, W k e * Δ ^ (1 + δ) ≤ weight (W k) H) →
          |weight (W k) M - weight (W k) H / Δ| ≤
            Δ ^ (-(δ / (50 * r ^ 2))) * (weight (W k) H / Δ) := by
  set ε : ℝ := δ / (50 * r ^ 2) with hεdef
  have hR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hR0 : (0 : ℝ) < r := by linarith
  have hεδ : ε * (50 * r ^ 2) = δ := by rw [hεdef]; field_simp
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε < 1 := by nlinarith
  set a : ℝ := 10 * r * ε with ha
  set b : ℝ := 2 * a + 3 * ε with hb
  set ρ : ℝ := 3 / (20 * r) with hρ
  set σ : ℝ := 3 * ε / (20 * r) with hσ
  have ha0 : 0 < a := by positivity
  have hρ0 : 0 < ρ := by positivity
  have hσ0 : 0 ≤ σ := by positivity
  have haρ : a * ρ = 3 / 2 * ε := by rw [ha, hρ]; field_simp; ring
  have haσ : a * σ = 3 / 2 * ε ^ 2 := by rw [ha, hσ]; field_simp; ring
  have hr1 : ((r - 1 : ℕ) : ℝ) = r - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hr2 : ((2 * r : ℕ) : ℝ) = 2 * r := by push_cast; ring
  have hsum : (2 * r + 4) * ρ + ρ + σ < 1 := by
    have : (2 * r + 4) * ρ + ρ + σ = (6 * r + 15 + 3 * ε) / (20 * r) := by
      rw [hρ, hσ]; field_simp; ring
    rw [this, div_lt_one (by positivity)]
    linarith
  have hr2' : (20 * r + 3 : ℝ) ≤ 50 * r ^ 2 := by nlinarith
  have hb1 : b ≤ 1 := by
    calc b = (20 * r + 3) * ε := by rw [hb, ha]; ring
      _ ≤ 50 * r ^ 2 * ε := mul_le_mul_of_nonneg_right hr2' hε.le
      _ = δ := by rw [← hεδ]; ring
      _ ≤ 1 := hδ1.le
  have ha5 : 5 * ε ≤ a := by
    have := mul_le_mul_of_nonneg_right (show (5 : ℝ) ≤ 10 * r by linarith) hε.le
    rw [ha]; linarith
  have hδa : a + 4 * ε ≤ δ := by
    have h1 : (10 * r + 4 : ℝ) ≤ 50 * r ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hε.le
    rw [ha, ← hεδ]; linarith
  obtain ⟨D₀, hD₀⟩ := Nibble.nibble_marginal r hr hρ0 hρ0.le hσ0 hsum
  have e2 : b * ((r - 1 : ℕ) : ℝ) < 1 - a := by
    rw [hr1, hb, ha]
    have : (20 * r ^ 2 - 7 * r - 3) * ε < 50 * r ^ 2 * ε := by nlinarith
    nlinarith
  have e3 : b * ((r - 1 : ℕ) : ℝ) + (a - δ) < ε := by
    rw [hr1, hb, ha, ← hεδ]; nlinarith
  have e5 : b * ((2 * r : ℕ) : ℝ) + ε < δ - 4 * ε := by
    rw [hr2, hb, ha, ← hεδ]
    have : 0 < (10 * r ^ 2 - 6 * r - 5) * ε := by
      apply mul_pos _ hε; nlinarith
    nlinarith
  have e8 : ε < a * ρ := by rw [haρ]; linarith
  have e9 : ε ^ 2 < a * σ := by
    rw [haσ]; have : 0 < ε ^ 2 := by positivity
    linarith
  obtain ⟨Δ₀, hΔ₀⟩ := Filter.eventually_atTop.mp (eventually_facts12 r hr D₀ hε hε1 ha0
    e2 e3 e5 e8 e9 e8)
  refine ⟨Δ₀, fun Δ hΔ V _ _ H huni hdeg hcod hcard ι _ W hW0 hι => ?_⟩
  exact core_1_2 r hr δ ε a b ρ ρ σ D₀ hε ha0 rfl hb1 ha5 hδa hρ0.le hρ0.le hσ0
    (fun D hD V _ _ H => hD₀ D hD V H) Δ (hΔ₀ Δ hΔ) V H huni hdeg hcod hcard ι W hW0 hι

end Pseudorandom
