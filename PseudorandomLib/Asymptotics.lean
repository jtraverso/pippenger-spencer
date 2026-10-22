/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-! # Elementary asymptotic facts used to choose `Δ₀`

All statements are of the form "eventually (as `D → ∞`) some explicit inequality holds".
-/

@[expose] public section

namespace Pseudorandom

open Filter Asymptotics

/-- `C ≤ D^c` eventually, for `c > 0`. -/
theorem eventually_const_le_rpow {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∀ᶠ D : ℝ in atTop, C ≤ D ^ c :=
  (tendsto_rpow_atTop hc).eventually_ge_atTop C

/-- `C log D ≤ D^c` eventually, for `c > 0`. -/
theorem eventually_mul_log_le_rpow {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∀ᶠ D : ℝ in atTop, C * Real.log D ≤ D ^ c := by
  have h := (isLittleO_log_rpow_atTop hc).bound (c := 1 / (|C| + 1)) (by positivity)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with D hD hD1
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hpow : 0 ≤ D ^ c := Real.rpow_nonneg (by linarith) c
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hpow] at hD
  calc C * Real.log D ≤ |C| * Real.log D :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hlog
    _ ≤ |C| * (1 / (|C| + 1) * D ^ c) := mul_le_mul_of_nonneg_left hD (abs_nonneg C)
    _ = (|C| / (|C| + 1)) * D ^ c := by ring
    _ ≤ 1 * D ^ c := by
        apply mul_le_mul_of_nonneg_right _ hpow
        rw [div_le_one (by positivity)]; linarith
    _ = D ^ c := one_mul _

/-- `D^σ ≤ c D^γ` eventually, for `σ < γ` and `c > 0`. -/
theorem eventually_rpow_le_mul_rpow {σ γ c : ℝ} (hσγ : σ < γ) (hc : 0 < c) :
    ∀ᶠ D : ℝ in atTop, D ^ σ ≤ c * D ^ γ := by
  filter_upwards [eventually_const_le_rpow (sub_pos.mpr hσγ) (1 / c),
    eventually_gt_atTop (0 : ℝ)] with D hD hD0
  have h1 : D ^ γ = D ^ σ * D ^ (γ - σ) := by
    rw [← Real.rpow_add hD0]; ring_nf
  rw [h1]
  have h2 : 0 < D ^ σ := Real.rpow_pos_of_pos hD0 σ
  calc D ^ σ = c * (D ^ σ * (1 / c)) := by field_simp
    _ ≤ c * (D ^ σ * D ^ (γ - σ)) := by gcongr

end Pseudorandom
