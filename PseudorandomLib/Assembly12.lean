/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.NibbleMarginal
public import PseudorandomLib.EdgePartition
public import PseudorandomLib.RandomMatching
public import PseudorandomLib.Numerics12

/-! # Assembling the proof of Theorem 1.2

`core_1_2` carries out Steps 1–3 for a fixed (large) `Δ` satisfying the numerical conditions
collected in `Facts12`. The nibble theorem enters as the hypothesis `hnib`.
-/

@[expose] public section

namespace Pseudorandom

open Finset

/-- The numerical conditions on `Δ`. -/
structure Facts12 (r : ℕ) (δ ε a b ρ κ σ D₀ D : ℝ) : Prop where
  h1 : 2 ≤ D
  h2 : (2 * D ^ b) ^ (r - 1) ≤ D ^ (1 - a)
  h3 : 2 * (2 * D ^ b) ^ (r - 1) * D ^ (a - δ) ≤ D ^ ε
  h4 : D ^ (-(2 * ε)) ≤ 1 / 2
  h5 : 128 * (r + 1) * (2 * D ^ b) ^ (2 * r) * D ^ ε ≤ D ^ (δ - 4 * ε)
  h6 : 64 * r ^ 2 * D ^ 2 * Real.exp (2 * D ^ (ε ^ 2) - D ^ ε / 64) < 1
  h7 : D₀ ≤ D ^ a / 2
  h8 : D ^ ε ≤ (D ^ a / 2) ^ κ
  h9 : D ^ (ε ^ 2) ≤ (D ^ a / 2) ^ σ
  h10 : (D ^ a / 2) ^ (-ρ) + 4 * D ^ (-(2 * ε)) ≤ D ^ (-ε) / 2
  h11 : 1 ≤ D ^ a / 2

theorem num_aux1 {r Δ e : ℝ} (hr : 2 ≤ r) (hΔ : 1 ≤ Δ) (he : 1 ≤ e) :
    (r * e + 2 * e) * (2 * Δ) ≤ 64 * r ^ 2 * Δ ^ 2 * (e * e) := by
  have h1 : r * e + 2 * e ≤ 2 * r * e := by nlinarith
  have h2 : e ≤ e * e := by nlinarith
  have h3 : Δ ≤ Δ ^ 2 := by nlinarith
  have h4 : r ≤ r ^ 2 := by nlinarith
  calc (r * e + 2 * e) * (2 * Δ) ≤ 2 * r * e * (2 * Δ) := by gcongr
    _ = 4 * (r * (e * Δ)) := by ring
    _ ≤ 64 * (r ^ 2 * ((e * e) * Δ ^ 2)) := by
        have : r * (e * Δ) ≤ r ^ 2 * ((e * e) * Δ ^ 2) :=
          mul_le_mul h4 (mul_le_mul h2 h3 (by linarith) (by nlinarith)) (by nlinarith)
            (by nlinarith)
        have : 0 ≤ r * (e * Δ) := mul_nonneg (by linarith) (by nlinarith)
        linarith
    _ = 64 * r ^ 2 * Δ ^ 2 * (e * e) := by ring

theorem num_aux2 {r Δ e : ℝ} (hr : 2 ≤ r) (hΔ : 1 ≤ Δ) (he : 1 ≤ e) :
    r * e * (2 * Δ) * (2 * Δ) + (r * e) ^ 2 * (2 * Δ) * (2 * Δ) + e * (2 * Δ) * (2 * Δ) ≤
      64 * r ^ 2 * Δ ^ 2 * (e * e) := by
  have h2 : e ≤ e * e := by nlinarith
  have h4 : r ≤ r ^ 2 := by nlinarith
  have h5 : r * e ≤ r ^ 2 * (e * e) := mul_le_mul h4 h2 (by linarith) (by nlinarith)
  have h6 : e ≤ r ^ 2 * (e * e) := by nlinarith
  have hΔ2 : 0 ≤ Δ ^ 2 := by positivity
  have : r * e * (2 * Δ) * (2 * Δ) + (r * e) ^ 2 * (2 * Δ) * (2 * Δ) + e * (2 * Δ) * (2 * Δ) =
      4 * Δ ^ 2 * (r * e + r ^ 2 * (e * e) + e) := by ring
  rw [this]
  have : r * e + r ^ 2 * (e * e) + e ≤ 3 * (r ^ 2 * (e * e)) := by linarith
  nlinarith

theorem num_aux3 {r Δ e : ℝ} (hr : 2 ≤ r) (hΔ : 1 ≤ Δ) (he : 1 ≤ e) :
    2 * e ≤ 64 * r ^ 2 * Δ ^ 2 * (e * e) := by
  have h2 : e ≤ e * e := by nlinarith
  have h1 : 1 ≤ r ^ 2 * Δ ^ 2 := by
    have hr1 : 1 ≤ r ^ 2 := by nlinarith
    have hD1 : 1 ≤ Δ ^ 2 := by nlinarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ r ^ 2 * Δ ^ 2 := mul_le_mul hr1 hD1 zero_le_one (by linarith)
  have h3 : e * e ≤ r ^ 2 * Δ ^ 2 * (e * e) := le_mul_of_one_le_left (by nlinarith) h1
  calc 2 * e ≤ 64 * (e * e) := by linarith
    _ ≤ 64 * (r ^ 2 * Δ ^ 2 * (e * e)) := by linarith
    _ = 64 * r ^ 2 * Δ ^ 2 * (e * e) := by ring

/-- The final comparison of expectations. -/
theorem final_estimate {ω wM S P Δ ξ ν Dt q x₀ e : ℝ} (hω : 0 < ω) (hΔ : 0 < Δ) (hξ0 : 0 ≤ ξ)
    (hξ1 : ξ ≤ 1 / 2) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hP : 0 < P) (hq : 0 < q) (hDt : 0 < Dt)
    (hDtq : q * Dt = (1 + 2 * ξ) * Δ / P) (hx₀ : x₀ = (1 - ν) / Dt)
    (hS : |S - ω / P| ≤ ξ * (ω / P)) (hM : |wM - x₀ / q * S| < e * ω / (2 * Δ))
    (hsmall : ν + 4 * ξ ≤ e / 2) :
    |wM - ω / Δ| ≤ e * (ω / Δ) := by
  have hE : x₀ / q * S = (1 - ν) * (S * P) / ((1 + 2 * ξ) * Δ) := by
    have : Dt = (1 + 2 * ξ) * Δ / P / q := by rw [← hDtq]; field_simp
    rw [hx₀, this]; field_simp
  rw [abs_le] at hS
  have hZ1 : (1 - ξ) * ω ≤ S * P := by
    have := mul_le_mul_of_nonneg_right hS.1 hP.le
    have e1 : (ω / P - ξ * (ω / P)) * P = (1 - ξ) * ω := by field_simp
    nlinarith [this]
  have hZ2 : S * P ≤ (1 + ξ) * ω := by
    have := mul_le_mul_of_nonneg_right hS.2 hP.le
    have e1 : (ω / P + ξ * (ω / P)) * P = (1 + ξ) * ω := by field_simp
    nlinarith [this]
  have hden : 0 < (1 + 2 * ξ) * Δ := by positivity
  have hup : x₀ / q * S ≤ ω / Δ := by
    rw [hE, div_le_div_iff₀ hden hΔ]
    have h1 : (1 - ν) * (S * P) ≤ 1 * ((1 + ξ) * ω) := by
      apply mul_le_mul (by linarith) hZ2 _ zero_le_one
      nlinarith
    nlinarith
  have hlo : (1 - ν - 3 * ξ) * (ω / Δ) ≤ x₀ / q * S := by
    rw [hE, mul_div_assoc', div_le_div_iff₀ hΔ hden]
    have h1 : (1 - ν) * ((1 - ξ) * ω) ≤ (1 - ν) * (S * P) :=
      mul_le_mul_of_nonneg_left hZ1 (by linarith)
    have h2 : (1 - ν - 3 * ξ) * (1 + 2 * ξ) ≤ (1 - ν) * (1 - ξ) := by nlinarith
    have hωΔ : 0 < ω * Δ := by positivity
    nlinarith
  rw [abs_lt] at hM
  rw [abs_le]
  have hωΔ : 0 < ω / Δ := by positivity
  have hsplit : e * ω / (2 * Δ) = e / 2 * (ω / Δ) := by ring
  rw [hsplit] at hM
  constructor
  · nlinarith
  · nlinarith

set_option maxHeartbeats 4000000 in
/-- Steps 1–3 of the proof of Theorem 1.2 for a fixed `Δ`. -/
theorem core_1_2 (r : ℕ) (hr : 2 ≤ r) (δ ε a b ρ κ σ D₀ : ℝ) (hε : 0 < ε) (ha0 : 0 < a)
    (hb : b = 2 * a + 3 * ε) (hb1 : b ≤ 1) (ha5 : 5 * ε ≤ a)
    (hδa : a + 4 * ε ≤ δ) (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hσ : 0 ≤ σ)
    (hnib : ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (H : Finset (Finset V)), IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
      (∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ D ^ κ) → (H.card : ℝ) ≤ Real.exp (D ^ σ) →
      ∃ μ : Finset (Finset V) → ℝ, (∀ M, 0 ≤ μ M) ∧ ∑ M, μ M = 1 ∧
        (∀ M, μ M ≠ 0 → IsMatching M ∧ M ⊆ H) ∧
        ∀ e ∈ H, (1 - D ^ (-ρ)) / D ≤ ∑ M, μ M * (if e ∈ M then 1 else 0))
    (Δ : ℝ) (F : Facts12 r δ ε a b ρ κ σ D₀ Δ)
    (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (huni : IsUniform H r)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ)
    (hcod : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ Δ ^ (1 - δ))
    (hcard : (H.card : ℝ) ≤ Real.exp (Δ ^ (ε ^ 2)))
    (ι : Type) [Fintype ι] (W : ι → Finset V → ℝ) (hW0 : ∀ k, ∀ e ∈ H, 0 ≤ W k e)
    (hι : (Fintype.card ι : ℝ) ≤ Real.exp (Δ ^ (ε ^ 2))) :
    ∃ M ⊆ H, IsMatching M ∧
      ∀ k, (∀ e ∈ H, W k e * Δ ^ (1 + δ) ≤ weight (W k) H) →
        |weight (W k) M - weight (W k) H / Δ| ≤ Δ ^ (-ε) * (weight (W k) H / Δ) := by
  classical
  have hD2 := F.h1
  have hD0 : 0 < Δ := by linarith
  have hD1 : 1 ≤ Δ := by linarith
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  set ξ : ℝ := Δ ^ (-(2 * ε)) with hξ
  have hξ0 : 0 < ξ := Real.rpow_pos_of_pos hD0 _
  have hξ1 : ξ ≤ 1 / 2 := F.h4
  set C : ℝ := Δ ^ (1 - δ) with hC
  have hC0 : 0 < C := Real.rpow_pos_of_pos hD0 _
  set η : ℝ := Δ ^ (-(1 + δ)) with hη
  have hη0 : 0 < η := Real.rpow_pos_of_pos hD0 _
  set Xb : ℝ := 2 * Δ ^ b with hXb
  have hDb1 : 1 ≤ Δ ^ b := Real.one_le_rpow hD1 (by linarith)
  have hDbD : Δ ^ b ≤ Δ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hD1 hb1
  have hXb1 : 1 ≤ Xb := by rw [hXb]; linarith
  -- the number of parts
  set p : ℕ := ⌈Δ ^ b⌉₊ with hpdef
  have hp_ge : Δ ^ b ≤ p := Nat.le_ceil _
  have hp_le : (p : ℝ) ≤ Xb := by
    have := Nat.ceil_lt_add_one (show 0 ≤ Δ ^ b by linarith)
    rw [hXb]; linarith
  have hp1 : (1 : ℝ) ≤ p := hDb1.trans hp_ge
  have hp0 : 0 < p := by exact_mod_cast (lt_of_lt_of_le one_pos hp1)
  have hpD : (p : ℝ) ≤ 2 * Δ := by rw [hXb] at hp_le; linarith
  set P : ℝ := (p : ℝ) ^ (r - 1) with hPdef
  have hP1 : 1 ≤ P := one_le_pow₀ hp1
  have hPX : P ≤ Xb ^ (r - 1) := pow_le_pow_left₀ (by linarith) hp_le _
  set Y : ℝ := Δ ^ (1 - a) with hY
  have hPY : P ≤ Y := hPX.trans F.h2
  have hY1 : 1 ≤ Y := hP1.trans hPY
  have hpr : (p : ℝ) ^ r = p * P := by
    rw [hPdef, ← pow_succ']; congr 1; omega
  -- the number of edge classes
  set q : ℕ := ⌈Y / P⌉₊ with hqdef
  have hq_ge : Y / P ≤ q := Nat.le_ceil _
  have hq0 : 0 < q := Nat.ceil_pos.mpr (by positivity)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqP_ge : Y ≤ q * P := by rwa [div_le_iff₀ (by linarith)] at hq_ge
  have hqP_le : q * P ≤ 2 * Y := by
    have := Nat.ceil_lt_add_one (show 0 ≤ Y / P by positivity)
    rw [← hqdef] at this
    have h2 : (q : ℝ) * P < (Y / P + 1) * P := mul_lt_mul_of_pos_right this (by linarith)
    rw [add_mul, div_mul_cancel₀ _ (by linarith), one_mul] at h2
    linarith
  have hYD : Y ≤ Δ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hD1 (show 1 - a ≤ 1 by linarith)
  have hq_le : (q : ℝ) ≤ 2 * Δ := by
    have : (q : ℝ) ≤ q * P := le_mul_of_one_le_right hqR.le hP1
    linarith
  -- the hypergraph
  have hne : ∀ e ∈ H, e.Nonempty := fun e he => by rw [← card_pos, huni e he]; omega
  set U := H.biUnion id with hU
  set X₀ : ℝ := Δ ^ (ε ^ 2) with hX₀
  set Y₀ : ℝ := Δ ^ ε / 64 with hY₀
  have heX : 1 ≤ Real.exp X₀ := Real.one_le_exp (Real.rpow_pos_of_pos hD0 _).le
  have hUcard : (U.card : ℝ) ≤ r * Real.exp X₀ := by
    have h1 : U.card ≤ ∑ e ∈ H, (id e).card := card_biUnion_le
    have h2 : ∑ e ∈ H, (id e).card = H.card * r := sum_const_nat (fun e he => huni e he)
    have h3 : (U.card : ℝ) ≤ H.card * r := by exact_mod_cast h2 ▸ h1
    have : (0 : ℝ) ≤ r := by positivity
    calc (U.card : ℝ) ≤ H.card * r := h3
      _ ≤ Real.exp X₀ * r := mul_le_mul_of_nonneg_right hcard this
      _ = r * Real.exp X₀ := mul_comm _ _
  -- the relevant weight functions
  set K : Finset ι := univ.filter (fun k => (∀ e ∈ H, W k e * Δ ^ (1 + δ) ≤ weight (W k) H) ∧
    0 < weight (W k) H) with hK
  have hKcard : (K.card : ℝ) ≤ Real.exp X₀ :=
    le_trans (by exact_mod_cast card_le_univ K) hι
  have hWpos : ∀ k ∈ K, 0 < weight (W k) H := fun k hk => (mem_filter.mp hk).2.2
  have hWmax : ∀ k ∈ K, ∀ e ∈ H, W k e ≤ η * weight (W k) H := by
    intro k hk e he
    have h := (mem_filter.mp hk).2.1 e he
    have hpos : 0 < Δ ^ (1 + δ) := Real.rpow_pos_of_pos hD0 _
    rw [hη, Real.rpow_neg hD0.le, ← div_eq_inv_mul, le_div_iff₀ hpos]
    exact h
  have hunion : 64 * r ^ 2 * Δ ^ 2 * (Real.exp X₀ * Real.exp X₀) * Real.exp (-Y₀) < 1 := by
    have := F.h6
    rw [show 2 * Δ ^ (ε ^ 2) - Δ ^ ε / 64 = X₀ + X₀ + -Y₀ by rw [hX₀, hY₀]; ring,
      Real.exp_add, Real.exp_add] at this
    linarith
  have hexpY : ∀ E : ℝ, Y₀ ≤ E → Real.exp (-E) ≤ Real.exp (-Y₀) := fun E h =>
    Real.exp_le_exp.mpr (by linarith)
  have hY₀pos : 0 < Real.exp (-Y₀) := Real.exp_pos _
  -- Step 1: the vertex partition
  have hXb2 : P ^ 2 ≤ Xb ^ (2 * r) := by
    calc P ^ 2 ≤ (Xb ^ (r - 1)) ^ 2 := pow_le_pow_left₀ (by linarith) hPX 2
      _ = Xb ^ (2 * (r - 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ Xb ^ (2 * r) := pow_le_pow_right₀ hXb1 (by omega)
  have hXbr : ((p : ℝ) ^ r) ^ 2 ≤ Xb ^ (2 * r) := by
    calc ((p : ℝ) ^ r) ^ 2 ≤ (Xb ^ r) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) hp_le r) 2
      _ = Xb ^ (2 * r) := by rw [← pow_mul, mul_comm]
  have hE2 := e2_bound r hD0 hξ (by linarith) hC hp1 hP1 hXb2 F.h5
  have hE1 := e1_bound r hD0 hξ (by linarith) hη hp1 hXbr F.h5
  obtain ⟨τ, hτdeg, hτw⟩ := vertex_partition hp0 H r (by omega) huni Δ C η ξ hD0 hC0 hη0 hξ0
    hdeg hcod W K (fun k _ => hW0 k) hWpos hWmax (by
      refine lt_of_le_of_lt ?_ hunion
      have e1 := hexpY _ hE2
      have e2 := hexpY _ hE1
      have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
      have hK0 : (0 : ℝ) ≤ K.card := Nat.cast_nonneg _
      have hp0' : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      calc (U.card * p : ℝ) * Real.exp (-(ξ ^ 2 * Δ / (2 * C * (r * P ^ 2 / p + ξ * P)))) +
            (2 * K.card * p : ℝ) * Real.exp (-(ξ ^ 2 / (2 * Δ * η *
              (r * ((p : ℝ) ^ r) ^ 2 / p + ξ * (p : ℝ) ^ r))))
          ≤ (U.card * p : ℝ) * Real.exp (-Y₀) + (2 * K.card * p : ℝ) * Real.exp (-Y₀) := by
            gcongr
        _ = (U.card + 2 * K.card) * p * Real.exp (-Y₀) := by ring
        _ ≤ (r * Real.exp X₀ + 2 * Real.exp X₀) * (2 * Δ) * Real.exp (-Y₀) := by gcongr
        _ ≤ 64 * r ^ 2 * Δ ^ 2 * (Real.exp X₀ * Real.exp X₀) * Real.exp (-Y₀) :=
            mul_le_mul_of_nonneg_right (num_aux1 hrR hD1 heX) hY₀pos.le)
  -- Step 2: the edge partition
  set A : Fin p → Finset (Finset V) := part H τ with hAdef
  set m : ℝ := Δ / (q * P) with hmdef
  have hqP0 : 0 < (q : ℝ) * P := by positivity
  have hm_ge : Δ ^ a / 2 ≤ m := by
    have hDY : Δ / Y = Δ ^ a := by
      rw [hY, div_eq_iff (Real.rpow_pos_of_pos hD0 _).ne', ← Real.rpow_add hD0]
      simp
    rw [hmdef, ← hDY, div_div]
    exact div_le_div_of_nonneg_left hD0.le (by positivity) (by linarith)
  set D₁ : ℝ := (1 + ξ) * Δ / P with hD₁
  set t₃ : ℝ := ξ * Δ / (q * P) with ht₃
  set t₄ : ℝ := Δ ^ ε / 2 with ht₄
  set β : ℝ := (1 + ξ) / (p : ℝ) ^ r with hβ
  set γ : ℝ := 1 / (2 * q * (p : ℝ) ^ r) with hγ
  have ht₃0 : 0 < t₃ := by positivity
  have ht₄0 : 0 < t₄ := by have := Real.rpow_pos_of_pos hD0 ε; positivity
  have hβ0 : 0 ≤ β := by positivity
  have hγ0 : 0 < γ := by positivity
  have hD₁q : D₁ / q = (1 + ξ) * m := by
    rw [hD₁, hmdef]; field_simp
  have ht₃m : t₃ = ξ * m := by rw [ht₃, hmdef]; ring
  have hWA : ∀ k ∈ K, ∀ i, weight (W k) (A i) ≤ β * weight (W k) H := by
    intro k hk i
    have h := hτw k hk i
    rw [abs_le] at h
    have : β * weight (W k) H = weight (W k) H / (p : ℝ) ^ r +
        ξ * (weight (W k) H / (p : ℝ) ^ r) := by rw [hβ]; ring
    rw [this]; linarith [h.2]
  have hCq : C / q ≤ t₄ := by
    have h1 : C / q ≤ C * P / Y := by
      rw [div_le_div_iff₀ hqR (by linarith)]
      nlinarith
    have h2 : C * P / Y = P * Δ ^ (a - δ) := by
      rw [hC, hY, mul_comm, mul_div_assoc, ← Real.rpow_sub hD0]; ring_nf
    have h3 : P * Δ ^ (a - δ) ≤ Xb ^ (r - 1) * Δ ^ (a - δ) :=
      mul_le_mul_of_nonneg_right hPX (Real.rpow_pos_of_pos hD0 _).le
    have h4 := F.h3
    rw [ht₄]
    rw [← hXb] at h4
    linarith
  have hCq0 : 0 ≤ C / q := by positivity
  have hE3 : Y₀ ≤ t₃ ^ 2 / (2 * (1 * D₁ / q + 1 * t₃)) := by
    have := e3_bound hD1 hξ hξ1 hm_ge ha5
    rw [mul_div_assoc, hD₁q, ht₃m]; exact this
  have hE4 : Y₀ ≤ t₄ ^ 2 / (2 * (1 * C / q + 1 * t₄)) := by
    have := e4_bound hD0 ht₄ hCq0 hCq
    rw [mul_div_assoc]; exact this
  have hηqp : η * (q * (p : ℝ) ^ r) ≤ 4 * Δ ^ (-ε) := by
    have h1 : η * (q * (p : ℝ) ^ r) = η * ((q * P) * p) := by rw [hpr]; ring
    have h2 : η * ((q * P) * p) ≤ η * ((2 * Y) * Xb) := by
      gcongr
    have h3 : η * ((2 * Y) * Xb) = 4 * Δ ^ (-(1 + δ) + (1 - a) + b) := by
      rw [hη, hY, hXb, Real.rpow_add hD0, Real.rpow_add hD0]; ring
    have h4 : Δ ^ (-(1 + δ) + (1 - a) + b) ≤ Δ ^ (-ε) :=
      Real.rpow_le_rpow_of_exponent_le hD1 (by rw [hb]; linarith)
    linarith
  have hE5 : Y₀ ≤ γ ^ 2 / (2 * η * (β / q + γ)) :=
    e5_bound hD0 hξ0.le hξ1 hη0 hqR (by positivity) hβ hγ hηqp
  obtain ⟨f, hfdeg, hfcod, hfw⟩ := edge_partition hq0 H A (fun i => part_subset H τ i) D₁ C
    t₃ t₄ ht₃0 ht₄0 (fun i x => hτdeg x i)
    (fun i x y hxy => le_trans (by exact_mod_cast codegree_mono (part_subset H τ i) x y)
      (hcod x y hxy))
    W K η β γ hη0 hβ0 hγ0 (fun k _ => hW0 k) hWpos hWmax hWA (by
      refine lt_of_le_of_lt ?_ hunion
      have e3 := hexpY _ hE3
      have e4 := hexpY _ hE4
      have e5 := hexpY _ hE5
      have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
      have hK0 : (0 : ℝ) ≤ K.card := Nat.cast_nonneg _
      have hp0' : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      calc (U.card * p * q : ℝ) * Real.exp (-(t₃ ^ 2 / (2 * (1 * D₁ / q + 1 * t₃)))) +
            (U.card ^ 2 * p * q : ℝ) * Real.exp (-(t₄ ^ 2 / (2 * (1 * C / q + 1 * t₄)))) +
            (K.card * p * q : ℝ) * Real.exp (-(γ ^ 2 / (2 * η * (β / q + γ))))
          ≤ (U.card * p * q : ℝ) * Real.exp (-Y₀) + (U.card ^ 2 * p * q : ℝ) * Real.exp (-Y₀) +
            (K.card * p * q : ℝ) * Real.exp (-Y₀) := by gcongr
        _ = (U.card * p * q + U.card ^ 2 * p * q + K.card * p * q : ℝ) * Real.exp (-Y₀) := by
            ring
        _ ≤ (r * Real.exp X₀ * (2 * Δ) * (2 * Δ) + (r * Real.exp X₀) ^ 2 * (2 * Δ) * (2 * Δ) +
            Real.exp X₀ * (2 * Δ) * (2 * Δ)) * Real.exp (-Y₀) := by gcongr
        _ ≤ 64 * r ^ 2 * Δ ^ 2 * (Real.exp X₀ * Real.exp X₀) * Real.exp (-Y₀) :=
            mul_le_mul_of_nonneg_right (num_aux2 hrR hD1 heX) hY₀pos.le)
  -- Step 3: random matchings of the classes
  set B : Fin p → Fin q → Finset (Finset V) := fun i j => cls A f i j with hBdef
  have hBH : ∀ i j, B i j ⊆ H := fun i j => (cls_subset A f i j).trans (part_subset H τ i)
  set Dt : ℝ := D₁ / q + t₃ with hDt
  have hm0 : 0 < m := lt_of_lt_of_le (by have := F.h11; linarith) hm_ge
  have hDt_eq : Dt = (1 + 2 * ξ) * m := by rw [hDt, hD₁q, ht₃m]; ring
  have hDt_ge : Δ ^ a / 2 ≤ Dt := by
    rw [hDt_eq]; nlinarith
  have hDt1 : 1 ≤ Dt := F.h11.trans hDt_ge
  have hDt0 : 0 < Dt := by linarith
  set νr : ℝ := Dt ^ (-ρ) with hνr
  have hνr0 : 0 ≤ νr := (Real.rpow_pos_of_pos hDt0 _).le
  have hνr_le : νr ≤ (Δ ^ a / 2) ^ (-ρ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith [F.h11]) hDt_ge (by linarith)
  have hνr1 : νr ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hDt1 (by linarith)
  set x₀ : ℝ := (1 - νr) / Dt with hx₀
  have hx₀0 : 0 ≤ x₀ := div_nonneg (by linarith) hDt0.le
  have hdist : ∀ i j, ∃ ν : Finset (Finset V) → ℝ, (∀ N, 0 ≤ ν N) ∧ ∑ N, ν N = 1 ∧
      (∀ N, ν N ≠ 0 → IsMatching N ∧ N ⊆ B i j) ∧ ∀ e ∈ B i j, marg ν e = x₀ := by
    intro i j
    have hcodB : ∀ u w, u ≠ w → (codegree (B i j) u w : ℝ) ≤ Dt ^ κ := by
      intro u w huw
      have h1 := hfcod i j u w huw
      have h2 : Δ ^ ε ≤ Dt ^ κ :=
        F.h8.trans (Real.rpow_le_rpow (by linarith [F.h11]) hDt_ge hκ)
      have : C / q + t₄ ≤ Δ ^ ε := by rw [ht₄] at hCq ⊢; linarith
      linarith
    have hcardB : ((B i j).card : ℝ) ≤ Real.exp (Dt ^ σ) := by
      have h1 : ((B i j).card : ℝ) ≤ H.card := by exact_mod_cast card_le_card (hBH i j)
      have h2 : X₀ ≤ Dt ^ σ := F.h9.trans (Real.rpow_le_rpow (by linarith [F.h11]) hDt_ge hσ)
      exact h1.trans (hcard.trans (Real.exp_le_exp.mpr h2))
    obtain ⟨μ, hμ0, hμ1, hμsupp, hμmarg⟩ := hnib Dt (F.h7.trans hDt_ge) V (B i j)
      (fun e he => huni e (hBH i j he)) (fun v => hfdeg i j v) hcodB hcardB
    obtain ⟨ν, hν0, hν1, hνsupp, hνmarg⟩ := thinning (B i j) μ hμ0 hμ1 x₀ hx₀0
      (fun e he => hμmarg e he)
    refine ⟨ν, hν0, hν1, fun N hN => ?_, hνmarg⟩
    obtain ⟨M, hM, hNM, hNB⟩ := hνsupp N hN
    have hMm := (hμsupp M hM).1
    exact ⟨fun e he g hg heg => hMm e (hNM he) g (hNM hg) heg, hNB⟩
  choose ν hν0 hν1 hνsupp hνmarg using hdist
  have hdisj : ∀ i i', i ≠ i' → ∀ j j', ∀ e ∈ B i j, ∀ g ∈ B i' j', Disjoint e g := by
    intro i i' hii j j' e he g hg
    have he' : ∀ v ∈ e, τ v = i := (mem_filter.mp ((cls_subset A f i j) he)).2
    have hg' : ∀ v ∈ g, τ v = i' := (mem_filter.mp ((cls_subset A f i' j') hg)).2
    rw [Finset.disjoint_left]
    intro v hve hvg
    exact hii ((he' v hve).symm.trans (hg' v hvg))
  set c : ι → ℝ := fun k => (β / q + γ) * weight (W k) H with hcdef
  set t : ι → ℝ := fun k => Δ ^ (-ε) * weight (W k) H / (2 * Δ) with htdef
  have hu0 : 0 < β / q + γ := by positivity
  have hc : ∀ k ∈ K, 0 < c k := fun k hk => mul_pos hu0 (hWpos k hk)
  have ht : ∀ k ∈ K, 0 < t k := fun k hk => by
    have := hWpos k hk; have := Real.rpow_pos_of_pos hD0 (-ε); simp only [htdef]; positivity
  have hcb : ∀ k ∈ K, ∀ i j, weight (W k) (B i j) ≤ c k := by
    intro k hk i j
    have := hfw k hk i j
    simp only [hcdef]
    calc weight (W k) (B i j) ≤ β * weight (W k) H / q + γ * weight (W k) H := this
      _ = (β / q + γ) * weight (W k) H := by ring
  have hE6 : ∀ k ∈ K, Y₀ ≤ t k ^ 2 / (2 * (p * c k ^ 2 + c k * t k)) := by
    intro k hk
    simp only [htdef, hcdef]
    exact e6_bound r hD1 hξ0.le hξ1 hε.le ha0.le hqR hp_ge (by linarith) hY hqP_ge hpr hβ hγ hb
      (hWpos k hk)
  obtain ⟨M, hMH, hMm, hMw⟩ := random_matching hq0 H hne B hBH hdisj ν hν0 hν1 hνsupp x₀
    hνmarg W K (fun k _ => hW0 k) c t hc ht hcb (by
      refine lt_of_le_of_lt ?_ hunion
      calc ∑ k ∈ K, 2 * Real.exp (-(t k ^ 2 / (2 * (p * c k ^ 2 + c k * t k))))
          ≤ ∑ k ∈ K, 2 * Real.exp (-Y₀) :=
            sum_le_sum fun k hk => by have := hexpY _ (hE6 k hk); linarith
        _ = 2 * K.card * Real.exp (-Y₀) := by rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ 2 * Real.exp X₀ * Real.exp (-Y₀) := by gcongr
        _ ≤ 64 * r ^ 2 * Δ ^ 2 * (Real.exp X₀ * Real.exp X₀) * Real.exp (-Y₀) :=
            mul_le_mul_of_nonneg_right (num_aux3 hrR hD1 heX) hY₀pos.le)
  refine ⟨M, hMH, hMm, fun k hk => ?_⟩
  by_cases hkK : k ∈ K
  · have hω := hWpos k hkK
    have hfib : ∑ i, ∑ j, weight (W k) (B i j) = ∑ i, weight (W k) (A i) :=
      sum_congr rfl fun i _ => sum_fiberwise (A i) f (W k)
    have hS : |∑ i, weight (W k) (A i) - weight (W k) H / P| ≤ ξ * (weight (W k) H / P) := by
      have e1 : weight (W k) H / P = ∑ _i : Fin p, weight (W k) H / (p : ℝ) ^ r := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hpr]
        field_simp
      rw [e1, ← sum_sub_distrib, mul_sum]
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => hτw k hkK i)
    have hDtq : (q : ℝ) * Dt = (1 + 2 * ξ) * Δ / P := by
      rw [hDt_eq, hmdef]; field_simp
    have hM := hMw k hkK
    rw [hfib] at hM
    exact final_estimate hω hD0 hξ0.le hξ1 hνr0 hνr1 (by linarith) hqR hDt0 hDtq hx₀ hS hM
      (by linarith [F.h10])
  · have h0 : weight (W k) H = 0 := by
      refine le_antisymm ?_ (sum_nonneg fun e he => hW0 k e he)
      by_contra hpos
      push_neg at hpos
      exact hkK (mem_filter.mpr ⟨mem_univ _, hk, hpos⟩)
    have hz : ∀ e ∈ H, W k e = 0 := (sum_eq_zero_iff_of_nonneg (fun e he => hW0 k e he)).mp h0
    have hM0 : weight (W k) M = 0 := sum_eq_zero fun e he => hz e (hMH he)
    rw [h0, hM0]; simp

end Pseudorandom
