/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-! # Numerical estimates for the proof of Theorem 1.2

Each lemma bounds one of the exponents appearing in the failure probabilities of Steps 1–3
from below by `Δ^ε / 64`.
-/

@[expose] public section

namespace Pseudorandom

theorem rpow_sq' {Δ : ℝ} (hΔ : 0 < Δ) (x : ℝ) : (Δ ^ x) ^ 2 = Δ ^ (2 * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hΔ.le]; norm_num; ring_nf

/-- Degrees in Step 1. -/
theorem e2_bound {Δ ε δ ξ C P p X : ℝ} (r : ℕ) (hΔ : 0 < Δ) (hξ : ξ = Δ ^ (-(2 * ε)))
    (hξ1 : ξ ≤ 1) (hC : C = Δ ^ (1 - δ)) (hp1 : 1 ≤ p) (hP1 : 1 ≤ P)
    (hPX : P ^ 2 ≤ X ^ (2 * r))
    (h5 : 128 * (r + 1) * X ^ (2 * r) * Δ ^ ε ≤ Δ ^ (δ - 4 * ε)) :
    Δ ^ ε / 64 ≤ ξ ^ 2 * Δ / (2 * C * (r * P ^ 2 / p + ξ * P)) := by
  have hξ0 : 0 < ξ := by rw [hξ]; exact Real.rpow_pos_of_pos hΔ _
  have hC0 : 0 < C := by rw [hC]; exact Real.rpow_pos_of_pos hΔ _
  have hid : ξ ^ 2 * Δ / C = Δ ^ (δ - 4 * ε) := by
    rw [hξ, hC, rpow_sq' hΔ, div_eq_iff (Real.rpow_pos_of_pos hΔ _).ne',
      ← Real.rpow_add_one hΔ.ne', ← Real.rpow_add hΔ]; ring_nf
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hden : r * P ^ 2 / p + ξ * P ≤ (r + 1) * X ^ (2 * r) := by
    have h1 : r * P ^ 2 / p ≤ r * P ^ 2 := div_le_self (by positivity) hp1
    have h2 : ξ * P ≤ P ^ 2 := by nlinarith
    nlinarith
  have hpos : 0 < r * P ^ 2 / p + ξ * P := by positivity
  have hX : 0 < X ^ (2 * r) := lt_of_lt_of_le (by positivity) hPX
  have hεp : 0 < Δ ^ ε := Real.rpow_pos_of_pos hΔ _
  calc Δ ^ ε / 64 ≤ 64 * Δ ^ ε := by linarith
    _ = 128 * (r + 1) * X ^ (2 * r) * Δ ^ ε / (2 * ((r + 1) * X ^ (2 * r))) := by
        field_simp; ring
    _ ≤ Δ ^ (δ - 4 * ε) / (2 * ((r + 1) * X ^ (2 * r))) := by gcongr
    _ ≤ Δ ^ (δ - 4 * ε) / (2 * (r * P ^ 2 / p + ξ * P)) := by
        gcongr
    _ = ξ ^ 2 * Δ / (2 * C * (r * P ^ 2 / p + ξ * P)) := by
        rw [← hid]; field_simp

/-- Weights in Step 1. -/
theorem e1_bound {Δ ε δ ξ η p X : ℝ} (r : ℕ) (hΔ : 0 < Δ) (hξ : ξ = Δ ^ (-(2 * ε)))
    (hξ1 : ξ ≤ 1) (hη : η = Δ ^ (-(1 + δ))) (hp1 : 1 ≤ p)
    (hpX : (p ^ r) ^ 2 ≤ X ^ (2 * r))
    (h5 : 128 * (r + 1) * X ^ (2 * r) * Δ ^ ε ≤ Δ ^ (δ - 4 * ε)) :
    Δ ^ ε / 64 ≤ ξ ^ 2 / (2 * Δ * η * (r * (p ^ r) ^ 2 / p + ξ * p ^ r)) := by
  have hξ0 : 0 < ξ := by rw [hξ]; exact Real.rpow_pos_of_pos hΔ _
  have hη0 : 0 < η := by rw [hη]; exact Real.rpow_pos_of_pos hΔ _
  have hid : ξ ^ 2 / (Δ * η) = Δ ^ (δ - 4 * ε) := by
    rw [hξ, hη, rpow_sq' hΔ, div_eq_iff (by positivity), mul_comm Δ,
      ← Real.rpow_add_one hΔ.ne', ← Real.rpow_add hΔ]; ring_nf
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hpr : 1 ≤ p ^ r := one_le_pow₀ hp1
  have hden : r * (p ^ r) ^ 2 / p + ξ * p ^ r ≤ (r + 1) * X ^ (2 * r) := by
    have h1 : r * (p ^ r) ^ 2 / p ≤ r * (p ^ r) ^ 2 := div_le_self (by positivity) hp1
    have h2 : ξ * p ^ r ≤ (p ^ r) ^ 2 := by nlinarith
    nlinarith
  have hpos : 0 < r * (p ^ r) ^ 2 / p + ξ * p ^ r := by positivity
  have hX : 0 < X ^ (2 * r) := lt_of_lt_of_le (by positivity) hpX
  have hεp : 0 < Δ ^ ε := Real.rpow_pos_of_pos hΔ _
  calc Δ ^ ε / 64 ≤ 64 * Δ ^ ε := by linarith
    _ = 128 * (r + 1) * X ^ (2 * r) * Δ ^ ε / (2 * ((r + 1) * X ^ (2 * r))) := by
        field_simp; ring
    _ ≤ Δ ^ (δ - 4 * ε) / (2 * ((r + 1) * X ^ (2 * r))) := by gcongr
    _ ≤ Δ ^ (δ - 4 * ε) / (2 * (r * (p ^ r) ^ 2 / p + ξ * p ^ r)) := by
        gcongr
    _ = ξ ^ 2 / (2 * Δ * η * (r * (p ^ r) ^ 2 / p + ξ * p ^ r)) := by
        rw [← hid]; field_simp

/-- Degrees in Step 2. -/
theorem e3_bound {Δ ε a ξ m : ℝ} (hΔ : 1 ≤ Δ) (hξ : ξ = Δ ^ (-(2 * ε)))
    (hξ1 : ξ ≤ 1 / 2) (hm : Δ ^ a / 2 ≤ m) (ha : 5 * ε ≤ a) :
    Δ ^ ε / 64 ≤ (ξ * m) ^ 2 / (2 * (1 * ((1 + ξ) * m) + 1 * (ξ * m))) := by
  have hΔ0 : 0 < Δ := by linarith
  have hξ0 : 0 < ξ := by rw [hξ]; exact Real.rpow_pos_of_pos hΔ0 _
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have heq : (ξ * m) ^ 2 / (2 * (1 * ((1 + ξ) * m) + 1 * (ξ * m))) =
      ξ ^ 2 * m / (2 * (1 + 2 * ξ)) := by
    field_simp; ring
  rw [heq]
  have hid : ξ ^ 2 * Δ ^ a = Δ ^ (a - 4 * ε) := by
    rw [hξ, rpow_sq' hΔ0, ← Real.rpow_add hΔ0]; ring_nf
  have hpow : Δ ^ ε ≤ Δ ^ (a - 4 * ε) := Real.rpow_le_rpow_of_exponent_le hΔ (by linarith)
  have h1 : ξ ^ 2 * (Δ ^ a / 2) ≤ ξ ^ 2 * m := by gcongr
  rw [le_div_iff₀ (by positivity)]
  have h2 : 2 * (1 + 2 * ξ) ≤ 4 := by linarith
  have : 0 ≤ ξ ^ 2 * m := by positivity
  nlinarith

/-- Codegrees in Step 2. -/
theorem e4_bound {Δ ε c t : ℝ} (hΔ : 0 < Δ) (ht : t = Δ ^ ε / 2) (hc0 : 0 ≤ c) (hct : c ≤ t) :
    Δ ^ ε / 64 ≤ t ^ 2 / (2 * (1 * c + 1 * t)) := by
  have ht0 : 0 < t := by rw [ht]; have := Real.rpow_pos_of_pos hΔ ε; positivity
  rw [le_div_iff₀ (by positivity)]
  have : Δ ^ ε = 2 * t := by rw [ht]; ring
  rw [this]
  nlinarith

/-- Weights in Step 2. -/
theorem e5_bound {Δ ε ξ η β γ q pr : ℝ} (hΔ : 0 < Δ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2)
    (hη : 0 < η) (hq : 0 < q) (hpr : 0 < pr) (hβ : β = (1 + ξ) / pr) (hγ : γ = 1 / (2 * q * pr))
    (hηqp : η * (q * pr) ≤ 4 * Δ ^ (-ε)) :
    Δ ^ ε / 64 ≤ γ ^ 2 / (2 * η * (β / q + γ)) := by
  have hu : β / q + γ ≤ 2 / (q * pr) := by
    have : β / q + γ = (3 + 2 * ξ) / (2 * (q * pr)) := by rw [hβ, hγ]; field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hq hpr]
  have hu0 : 0 < β / q + γ := by rw [hβ, hγ]; positivity
  have hneg : Δ ^ (-ε) = 1 / Δ ^ ε := by rw [Real.rpow_neg hΔ.le, one_div]
  have hεp : 0 < Δ ^ ε := Real.rpow_pos_of_pos hΔ _
  rw [hneg] at hηqp
  have hkey : η * (q * pr) * Δ ^ ε ≤ 4 := by
    calc η * (q * pr) * Δ ^ ε ≤ 4 * (1 / Δ ^ ε) * Δ ^ ε :=
          mul_le_mul_of_nonneg_right hηqp hεp.le
      _ = 4 := by field_simp
  rw [le_div_iff₀ (by positivity)]
  calc Δ ^ ε / 64 * (2 * η * (β / q + γ)) ≤ Δ ^ ε / 64 * (2 * η * (2 / (q * pr))) := by
        gcongr
    _ = (η * (q * pr) * Δ ^ ε) / (16 * (q * pr) ^ 2) := by field_simp; ring
    _ ≤ 4 / (16 * (q * pr) ^ 2) := by gcongr
    _ = γ ^ 2 := by rw [hγ]; field_simp; ring

/-- Concentration in Step 3. -/
theorem e6_bound {Δ ε a b ξ β γ q p P ω Y : ℝ} (r : ℕ) (hΔ : 1 ≤ Δ) (hξ0 : 0 ≤ ξ)
    (hξ1 : ξ ≤ 1 / 2) (hε : 0 ≤ ε) (ha : 0 ≤ a) (hq : 0 < q) (hp : Δ ^ b ≤ p) (hP : 0 < P) (hY : Y = Δ ^ (1 - a))
    (hqP : Y ≤ q * P) (hpr : p ^ r = p * P) (hβ : β = (1 + ξ) / p ^ r)
    (hγ : γ = 1 / (2 * q * p ^ r)) (hb : b = 2 * a + 3 * ε) (hω : 0 < ω) :
    Δ ^ ε / 64 ≤ (Δ ^ (-ε) * ω / (2 * Δ)) ^ 2 /
      (2 * (p * ((β / q + γ) * ω) ^ 2 + (β / q + γ) * ω * (Δ ^ (-ε) * ω / (2 * Δ)))) := by
  have hΔ0 : 0 < Δ := by linarith
  have hp0 : 0 < p := lt_of_lt_of_le (Real.rpow_pos_of_pos hΔ0 _) hp
  have hY0 : 0 < Y := by rw [hY]; exact Real.rpow_pos_of_pos hΔ0 _
  set s := Δ ^ (-ε) / (2 * Δ) with hs
  have hs0 : 0 < s := by positivity
  set u := β / q + γ with hudef
  have hu0 : 0 < u := by rw [hudef, hβ, hγ]; positivity
  have hpr0 : 0 < p ^ r := by positivity
  have hu : u ≤ 2 / (q * (p * P)) := by
    have : u = (3 + 2 * ξ) / (2 * (q * (p * P))) := by
      rw [hudef, hβ, hγ, hpr]; field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < q * (p * P) := by positivity
    nlinarith
  -- reduce to `ω`-free statement
  have hred : (Δ ^ (-ε) * ω / (2 * Δ)) ^ 2 /
      (2 * (p * (u * ω) ^ 2 + u * ω * (Δ ^ (-ε) * ω / (2 * Δ)))) =
      s ^ 2 / (2 * (p * u ^ 2 + u * s)) := by
    have hsω : Δ ^ (-ε) * ω / (2 * Δ) = s * ω := by rw [hs]; ring
    rw [hsω, show (s * ω) ^ 2 = s ^ 2 * ω ^ 2 by ring,
      show 2 * (p * (u * ω) ^ 2 + u * ω * (s * ω)) = 2 * (p * u ^ 2 + u * s) * ω ^ 2 by ring,
      mul_div_mul_right _ _ (by positivity)]
  rw [hred]
  -- the key powers
  have hsY_eq : s * Y = Δ ^ (-ε - a) / 2 := by
    have e : Δ ^ (-ε) * Δ ^ (1 - a) = Δ ^ (-ε - a) * Δ := by
      rw [← Real.rpow_add hΔ0, ← Real.rpow_add_one hΔ0.ne']; ring_nf
    rw [hs, hY, div_mul_eq_mul_div, e]
    field_simp
  have hsY : s * Y ≤ 1 / 2 := by
    rw [hsY_eq]
    have : Δ ^ (-ε - a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hΔ (by linarith)
    linarith
  have hB : s ^ 2 * (Y ^ 2 * Δ ^ b) = Δ ^ ε / 4 := by
    have : s ^ 2 * (Y ^ 2 * Δ ^ b) = (s * Y) ^ 2 * Δ ^ b := by ring
    rw [this, hsY_eq, div_pow, rpow_sq' hΔ0, div_mul_eq_mul_div, ← Real.rpow_add hΔ0, hb]
    ring_nf
  set w := u * (q * (p * P)) with hw
  have hw2 : w ≤ 2 := by
    rw [hw]; rwa [le_div_iff₀ (by positivity)] at hu
  have hw0 : 0 ≤ w := by positivity
  have hZ : Y ^ 2 * Δ ^ b ≤ (q * P) ^ 2 * p := by
    have h1 : Y ^ 2 ≤ (q * P) ^ 2 := by gcongr
    have : 0 ≤ Δ ^ b := (Real.rpow_pos_of_pos hΔ0 _).le
    calc Y ^ 2 * Δ ^ b ≤ (q * P) ^ 2 * Δ ^ b := by gcongr
      _ ≤ (q * P) ^ 2 * p := by gcongr
  have hA : (p * u ^ 2 + u * s) * (Y ^ 2 * Δ ^ b) ≤ 5 := by
    have h1 : p * u ^ 2 * (Y ^ 2 * Δ ^ b) ≤ w ^ 2 := by
      calc p * u ^ 2 * (Y ^ 2 * Δ ^ b) ≤ p * u ^ 2 * ((q * P) ^ 2 * p) := by gcongr
        _ = w ^ 2 := by rw [hw]; ring
    have h2 : u * s * (Y ^ 2 * Δ ^ b) ≤ w * (s * Y) := by
      have : Y * Δ ^ b ≤ (q * P) * p := by
        have : 0 ≤ Δ ^ b := (Real.rpow_pos_of_pos hΔ0 _).le
        calc Y * Δ ^ b ≤ (q * P) * Δ ^ b := by gcongr
          _ ≤ (q * P) * p := by gcongr
      calc u * s * (Y ^ 2 * Δ ^ b) = u * s * Y * (Y * Δ ^ b) := by ring
        _ ≤ u * s * Y * ((q * P) * p) := by gcongr
        _ = w * (s * Y) := by rw [hw]; ring
    have h3 : w * (s * Y) ≤ 2 * (1 / 2) := by
      apply mul_le_mul hw2 hsY (by positivity) (by norm_num)
    have hw4 : w ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ hw0 hw2 2
    have : (p * u ^ 2 + u * s) * (Y ^ 2 * Δ ^ b) =
        p * u ^ 2 * (Y ^ 2 * Δ ^ b) + u * s * (Y ^ 2 * Δ ^ b) := by ring
    linarith
  have hZ0 : 0 < Y ^ 2 * Δ ^ b := by
    have := Real.rpow_pos_of_pos hΔ0 b; positivity
  have hεp : 0 < Δ ^ ε := Real.rpow_pos_of_pos hΔ0 _
  have hden0 : 0 < 2 * (p * u ^ 2 + u * s) := by positivity
  rw [le_div_iff₀ hden0]
  refine le_of_mul_le_mul_right ?_ hZ0
  rw [hB]
  have := mul_le_mul_of_nonneg_left hA (show 0 ≤ Δ ^ ε / 32 by positivity)
  calc Δ ^ ε / 64 * (2 * (p * u ^ 2 + u * s)) * (Y ^ 2 * Δ ^ b) =
        Δ ^ ε / 32 * ((p * u ^ 2 + u * s) * (Y ^ 2 * Δ ^ b)) := by ring
    _ ≤ Δ ^ ε / 32 * 5 := this
    _ ≤ Δ ^ ε / 4 := by linarith

end Pseudorandom
