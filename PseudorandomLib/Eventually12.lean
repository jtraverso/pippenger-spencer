/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.Assembly12
public import PseudorandomLib.Asymptotics

/-! # The numerical conditions of Theorem 1.2 hold for all large `Δ` -/

@[expose] public section

namespace Pseudorandom

open Filter

/-- `C D^α ≤ D^β` eventually, for `α < β`. -/
theorem eventually_mul_rpow_le_rpow {α β : ℝ} (h : α < β) (C : ℝ) :
    ∀ᶠ D : ℝ in atTop, C * D ^ α ≤ D ^ β := by
  rcases le_or_gt C 0 with hC | hC
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
    have h1 : C * D ^ α ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (Real.rpow_pos_of_pos hD _).le
    exact h1.trans (Real.rpow_pos_of_pos hD _).le
  · filter_upwards [eventually_rpow_le_mul_rpow (σ := α) (γ := β) (c := 1 / C) h (by positivity)]
      with D hD
    calc C * D ^ α ≤ C * (1 / C * D ^ β) := mul_le_mul_of_nonneg_left hD hC.le
      _ = D ^ β := by field_simp

theorem two_mul_rpow_pow {D : ℝ} (hD : 0 < D) (b : ℝ) (n : ℕ) :
    (2 * D ^ b) ^ n = 2 ^ n * D ^ (b * n) := by
  rw [mul_pow, ← Real.rpow_natCast (D ^ b), ← Real.rpow_mul hD.le]

theorem rpow_div_two_rpow {D : ℝ} (hD : 0 < D) (a κ : ℝ) :
    (D ^ a / 2) ^ κ = D ^ (a * κ) / 2 ^ κ := by
  rw [Real.div_rpow (Real.rpow_pos_of_pos hD _).le (by norm_num), ← Real.rpow_mul hD.le]

/-- All numerical conditions hold for large `Δ`. -/
theorem eventually_facts12 (r : ℕ) (hr : 2 ≤ r) {δ ε a b ρ κ σ : ℝ} (D₀ : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (ha : 0 < a)
    (e2 : b * ((r - 1 : ℕ) : ℝ) < 1 - a) (e3 : b * ((r - 1 : ℕ) : ℝ) + (a - δ) < ε)
    (e5 : b * ((2 * r : ℕ) : ℝ) + ε < δ - 4 * ε) (e8 : ε < a * κ) (e9 : ε ^ 2 < a * σ)
    (e10 : ε < a * ρ) :
    ∀ᶠ D : ℝ in atTop, Facts12 r δ ε a b ρ κ σ D₀ D := by
  have hε2 : ε ^ 2 < ε := by nlinarith
  have hε2pos : 0 < ε ^ 2 := by positivity
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    eventually_mul_rpow_le_rpow e2 (2 ^ (r - 1)),
    eventually_mul_rpow_le_rpow e3 (2 * 2 ^ (r - 1)),
    eventually_const_le_rpow (by positivity : (0 : ℝ) < 2 * ε) 2,
    eventually_mul_rpow_le_rpow e5 (128 * (r + 1) * 2 ^ (2 * r)),
    eventually_rpow_le_mul_rpow (c := 1 / 512) hε2 (by norm_num),
    eventually_const_le_rpow hε (512 * Real.log (64 * r ^ 2)),
    eventually_mul_log_le_rpow hε 1024,
    eventually_const_le_rpow ha (2 * D₀),
    eventually_mul_rpow_le_rpow e8 (2 ^ κ),
    eventually_mul_rpow_le_rpow e9 (2 ^ σ),
    eventually_mul_rpow_le_rpow (show -(a * ρ) < -ε by linarith) (4 * 2 ^ ρ),
    eventually_mul_rpow_le_rpow (show -(2 * ε) < -ε by linarith) 16,
    eventually_const_le_rpow ha 2]
    with D hD2 f2 f3 f4 f5 f6a f6b f6c f7 f8 f9 f10a f10b f11
  have hD0 : 0 < D := by linarith
  have hDε : 0 < D ^ ε := Real.rpow_pos_of_pos hD0 _
  refine ⟨hD2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [two_mul_rpow_pow hD0]; exact f2
  · rw [two_mul_rpow_pow hD0, mul_assoc (2 : ℝ), mul_assoc, ← Real.rpow_add hD0, ← mul_assoc]
    exact f3
  · rw [Real.rpow_neg hD0.le, inv_eq_one_div, div_le_div_iff₀ (Real.rpow_pos_of_pos hD0 _)
      (by norm_num)]
    linarith
  · rw [two_mul_rpow_pow hD0]
    calc 128 * (r + 1) * (2 ^ (2 * r) * D ^ (b * ((2 * r : ℕ) : ℝ))) * D ^ ε =
        128 * (r + 1) * 2 ^ (2 * r) * D ^ (b * ((2 * r : ℕ) : ℝ) + ε) := by
          rw [Real.rpow_add hD0]; ring
      _ ≤ _ := f5
  · -- the union bound
    have hlog : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
    have hsum : Real.log (64 * r ^ 2) + 2 * Real.log D + (2 * D ^ (ε ^ 2) - D ^ ε / 64) < 0 := by
      have : 2 * Real.log D ≤ D ^ ε / 512 := by linarith
      have : Real.log (64 * r ^ 2) ≤ D ^ ε / 512 := by linarith
      have : D ^ (ε ^ 2) ≤ D ^ ε / 512 := by linarith
      linarith
    have hr0 : (0 : ℝ) < 64 * r ^ 2 := by
      have : (2 : ℝ) ≤ r := by exact_mod_cast hr
      positivity
    have : 64 * r ^ 2 * D ^ 2 * Real.exp (2 * D ^ (ε ^ 2) - D ^ ε / 64) =
        Real.exp (Real.log (64 * r ^ 2) + 2 * Real.log D + (2 * D ^ (ε ^ 2) - D ^ ε / 64)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hr0, show 2 * Real.log D = Real.log (D ^ 2)
        by rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
    rw [this]
    calc _ < Real.exp 0 := Real.exp_lt_exp.mpr hsum
      _ = 1 := Real.exp_zero
  · linarith
  · rw [rpow_div_two_rpow hD0, le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _), mul_comm]
    exact f8
  · rw [rpow_div_two_rpow hD0, le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _), mul_comm]
    exact f9
  · have e : (D ^ a / 2) ^ (-ρ) = 2 ^ ρ * D ^ (-(a * ρ)) := by
      rw [rpow_div_two_rpow hD0, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul,
        mul_comm, mul_neg]
    rw [e]; linarith
  · linarith

end Pseudorandom
