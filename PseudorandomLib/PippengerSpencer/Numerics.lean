/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.Asymptotics

/-! # Numerical conditions for the Pippenger–Spencer theorem

All parameters except `D` are fixed; the conditions below hold for all sufficiently large `D`.
The key one is the Local Lemma condition `e · 2 e^{-c K} · ((1 + r D)^n + 1) ≤ 1` with
`K ≈ a D` colours per batch.
-/

@[expose] public section

namespace Pseudorandom.PS

open Filter

/-- The Local Lemma condition, for all large `D`. -/
theorem eventually_lll {ε₁ a : ℝ} (hε₁ : 0 < ε₁) (ha : 0 < a) (r T : ℕ) :
    ∀ᶠ D : ℝ in atTop, Real.exp 1 * (2 * Real.exp (-(ε₁ ^ 2 * ⌊a * D⌋₊ / 4))) *
      (((1 + r * ⌊D⌋₊) ^ (4 * T + 1) : ℕ) + 1) ≤ 1 := by
  set c : ℝ := ε₁ ^ 2 / 4 with hc
  have hc0 : 0 < c := by positivity
  set n : ℕ := 4 * T + 1 with hn
  have hca : 0 < c * a := mul_pos hc0 ha
  filter_upwards [eventually_mul_log_le_rpow one_pos (2 * n / (c * a)),
    eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop ((Real.log 4 + 1 + n * Real.log (r + 1) + c) / (c * a / 2))]
    with D hlog hD1 hDbig
  have hD0 : 0 < D := by linarith
  rw [Real.rpow_one] at hlog
  set K : ℕ := ⌊a * D⌋₊ with hK
  have hKge : a * D - 1 ≤ K := by
    have := Nat.lt_floor_add_one (a * D); rw [← hK] at this; linarith
  set X : ℝ := ((r + 1) * D) ^ n with hX
  have hr1 : (1 : ℝ) ≤ r + 1 := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
  have hX1 : 1 ≤ X := one_le_pow₀ (by nlinarith)
  have hX0 : 0 < X := by linarith
  have hcast : ((((1 + r * ⌊D⌋₊) ^ n : ℕ)) : ℝ) ≤ X := by
    push_cast
    apply pow_le_pow_left₀ (by positivity)
    have : (⌊D⌋₊ : ℝ) ≤ D := Nat.floor_le hD0.le
    have : (r : ℝ) * ⌊D⌋₊ ≤ r * D := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg r)
    nlinarith
  have hexp : Real.exp (-(ε₁ ^ 2 * K / 4)) ≤ Real.exp (-(c * a * D - c)) := by
    apply Real.exp_le_exp.mpr
    have : ε₁ ^ 2 * K / 4 = c * K := by rw [hc]; ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hKge hc0.le
    nlinarith
  -- `4 e X ≤ exp (c a D - c)`
  have hlogX : Real.log (4 * Real.exp 1 * X) =
      Real.log 4 + 1 + n * (Real.log (r + 1) + Real.log D) := by
    rw [Real.log_mul (by positivity) hX0.ne', Real.log_mul (by norm_num) (Real.exp_pos 1).ne',
      Real.log_exp, hX, Real.log_pow, Real.log_mul (by positivity) hD0.ne']
  have hmain : 4 * Real.exp 1 * X ≤ Real.exp (c * a * D - c) := by
    rw [← Real.log_le_iff_le_exp (by positivity), hlogX]
    have h1 : (n : ℝ) * Real.log D ≤ c * a / 2 * D := by
      have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ c * a / 2)
      have e : c * a / 2 * (2 * n / (c * a) * Real.log D) = n * Real.log D := by
        field_simp
      linarith
    have h2 : Real.log 4 + 1 + n * Real.log (r + 1) + c ≤ c * a / 2 * D := by
      rw [div_le_iff₀ (by positivity)] at hDbig; linarith
    nlinarith
  calc Real.exp 1 * (2 * Real.exp (-(ε₁ ^ 2 * K / 4))) * ((((1 + r * ⌊D⌋₊) ^ n : ℕ) : ℝ) + 1)
      ≤ Real.exp 1 * (2 * Real.exp (-(c * a * D - c))) * (2 * X) := by
        apply mul_le_mul _ (by linarith) (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
        linarith
    _ = 4 * Real.exp 1 * X * Real.exp (-(c * a * D - c)) := by ring
    _ ≤ Real.exp (c * a * D - c) * Real.exp (-(c * a * D - c)) :=
        mul_le_mul_of_nonneg_right hmain (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- All numerical conditions, for large `D`. -/
theorem eventually_numerics {ε₁ a μ τ ε : ℝ} (hε₁ : 0 < ε₁) (ha : 0 < a) (hμ : 0 < μ)
    (hτ : 0 < τ) (hε : 0 < ε) (r T : ℕ) :
    ∀ᶠ D : ℝ in atTop, 1 ≤ D ∧ 1 ≤ μ * τ * D ∧ 1 ≤ ε₁ * ⌊a * D⌋₊ ∧ 6 ≤ ε * D ∧
      Real.exp 1 * (2 * Real.exp (-(ε₁ ^ 2 * ⌊a * D⌋₊ / 4))) *
        (((1 + r * ⌊D⌋₊) ^ (4 * T + 1) : ℕ) + 1) ≤ 1 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (1 / (μ * τ)),
    eventually_ge_atTop ((1 / ε₁ + 1) / a), eventually_ge_atTop (6 / ε),
    eventually_lll hε₁ ha r T] with D h1 h2 h3 h4 h5
  refine ⟨h1, ?_, ?_, ?_, h5⟩
  · rw [div_le_iff₀ (by positivity)] at h2; linarith
  · rw [div_le_iff₀ ha] at h3
    have := Nat.lt_floor_add_one (a * D)
    have h6 : 1 / ε₁ ≤ ⌊a * D⌋₊ := by linarith
    rw [div_le_iff₀ hε₁] at h6
    linarith
  · rw [div_le_iff₀ hε] at h4; linarith

end Pseudorandom.PS
