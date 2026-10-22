/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.PippengerSpencer.Batch
public import PseudorandomLib.PippengerSpencer.Marginal

/-! # One batch with explicit parameters

Specialisation of `batch_colouring` to the parameters used in the proof of the
Pippenger–Spencer theorem: `K ≤ ε₁ Db` colours per batch, nibble marginals `(1 - ε₁)/Db`, and
the degree drop `K (1 - 28 ε₁)`.
-/

@[expose] public section

namespace Pseudorandom.PS

open Finset Nibble

theorem exp_two_le_eight : Real.exp 2 ≤ 8 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]
  have h0 := Real.exp_pos 1
  nlinarith

/-- **One batch with explicit parameters.** -/
theorem batch_step {r : ℕ} {ε₁ μ₀ : ℝ} {T : ℕ} (hε₁ : 0 < ε₁) (hε₁' : ε₁ ≤ 1 / 56)
    (hproc : ∀ D : ℝ, 1 ≤ μ₀ * D →
      ∃ as Ds : ℕ → ℝ, (∀ t, 0 ≤ as t) ∧ (∀ t, 0 ≤ Ds t) ∧ Ds 0 = D ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)),
        IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
        (∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ μ₀ * D) →
        ∀ e ∈ H, (1 - ε₁) / D ≤ ∑ M, outMT H as Ds T M * (if e ∈ M then 1 else 0))
    {V : Type} [Fintype V] [DecidableEq V] (G : Finset (Finset V)) (huni : IsUniform G r)
    {Db : ℝ} (hμ : 1 ≤ μ₀ * Db) (hdeg : ∀ v, (degree G v : ℝ) ≤ Db)
    (hcod : ∀ u w, u ≠ w → (codegree G u w : ℝ) ≤ μ₀ * Db)
    {K Δ : ℕ} (hΔ : ∀ v, degree G v ≤ Δ) (hK1 : 1 ≤ ε₁ * K) (hKD : (K : ℝ) ≤ ε₁ * Db)
    (hLLL : Real.exp 1 * (2 * Real.exp (-(ε₁ ^ 2 * K / 4))) *
      (((1 + r * Δ) ^ (4 * T + 1) : ℕ) + 1) ≤ 1) :
    ∃ (Col : Finset (Finset V)) (c : Finset V → Fin K), Col ⊆ G ∧
      IsProperEdgeColouring Col K c ∧
      ∀ v, (degree (G \ Col) v : ℝ) ≤ Db - K * (1 - 28 * ε₁) := by
  obtain ⟨as, Ds, has, hDs, hDs0, hmarg⟩ := hproc Db hμ
  have hmarg' := hmarg V G huni hdeg hcod
  have hKpos' : (0 : ℝ) < K := by
    by_contra h
    push Not at h
    nlinarith
  have hKpos : 0 < K := by exact_mod_cast hKpos'
  have hDb : 0 < Db := by nlinarith
  set x : ℝ := K / Db with hx
  have hx0 : 0 ≤ x := by positivity
  have hxε : x ≤ ε₁ := by rw [hx, div_le_iff₀ hDb]; linarith
  have hKx : (K : ℝ) = x * Db := by rw [hx]; field_simp
  set p : ℝ := (1 - ε₁) / Db with hp
  have hp0 : 0 ≤ p := div_nonneg (by linarith) hDb.le
  have hpD : p * Db = 1 - ε₁ := by rw [hp]; field_simp
  set q : ℝ := ε₁ + 2 * x with hq
  set m : ℕ := ⌈Real.exp 2 * K * q⌉₊ with hm
  have he2 := exp_two_le_eight
  have he2' : 0 < Real.exp 2 := Real.exp_pos 2
  have hmle : (m : ℝ) ≤ 8 * K * q + 1 := by
    have := (Nat.ceil_lt_add_one (by positivity : 0 ≤ Real.exp 2 * K * q)).le
    have h2 : Real.exp 2 * K * q ≤ 8 * K * q := by
      have : 0 ≤ (K : ℝ) * q := by positivity
      nlinarith
    rw [hm]; linarith
  have hmge : Real.exp 2 * K * q ≤ m := Nat.le_ceil _
  have h1q : 1 - (Db - 2 * K) * p = ε₁ + 2 * x * (1 - ε₁) := by
    have : (Db - 2 * K) * p = (1 - ε₁) - 2 * x * (1 - ε₁) := by
      rw [hKx]; nlinarith [hpD]
    linarith
  have h1q' : 1 - (Db - 2 * K) * p ≤ q := by
    rw [h1q, hq]; nlinarith
  have hDKp : (Db - K) * p = (1 - ε₁) * (1 - x) := by
    rw [hKx]; nlinarith [hpD]
  refine batch_colouring (N := G.card) (T := T) (K := K) (t := ε₁ * K) (m := m) (Δ := Δ)
    (lam := 1 - 28 * ε₁) huni le_rfl has hDs hDs0 hdeg hp0 (by
      intro e he; exact hmarg' e he) hKpos hΔ (by linarith)
    (by positivity) ?_ ?_ ?_ ?_
  · -- the main inequality
    rw [hDKp]
    have hKx' : (K : ℝ) * x ≤ K * ε₁ := mul_le_mul_of_nonneg_left hxε hKpos'.le
    have hKq : (K : ℝ) * q = K * ε₁ + 2 * (K * x) := by rw [hq]; ring
    have h8 : 8 * (K : ℝ) * q = 8 * (K * q) := by ring
    have : (K : ℝ) * ((1 - ε₁) * (1 - x)) ≥ K * (1 - 2 * ε₁) := by
      have : (1 - ε₁) * (1 - x) ≥ 1 - 2 * ε₁ := by nlinarith
      exact mul_le_mul_of_nonneg_left this hKpos'.le
    have e1 : (K : ℝ) * (1 - 2 * ε₁) = K - 2 * (K * ε₁) := by ring
    have e2 : (K : ℝ) * (1 - 28 * ε₁) = K - 28 * (K * ε₁) := by ring
    have e3 : ε₁ * (K : ℝ) = K * ε₁ := by ring
    linarith
  · rw [h1q]; nlinarith
  · calc Real.exp 2 * K * (1 - (Db - 2 * K) * p) ≤ Real.exp 2 * K * q := by
          apply mul_le_mul_of_nonneg_left h1q' (by positivity)
      _ ≤ m := hmge
  · refine le_trans ?_ hLLL
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
    have hA : Real.exp (-((ε₁ * K) ^ 2 / (2 * (K + ε₁ * K)))) ≤ Real.exp (-(ε₁ ^ 2 * K / 4)) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      rw [le_div_iff₀ (by positivity)]
      have h1 : (K : ℝ) + ε₁ * K ≤ 2 * K := by
        have : ε₁ * (K : ℝ) ≤ 1 * K := mul_le_mul_of_nonneg_right (by linarith) hKpos'.le
        linarith
      have h0 : 0 ≤ ε₁ ^ 2 * K := by positivity
      have h2 := mul_le_mul_of_nonneg_left h1 h0
      calc ε₁ ^ 2 * K / 4 * (2 * (K + ε₁ * K)) = (ε₁ ^ 2 * K) * (K + ε₁ * K) / 2 := by ring
        _ ≤ (ε₁ ^ 2 * K) * (2 * K) / 2 := by linarith
        _ = (ε₁ * K) ^ 2 := by ring
    have hB : Real.exp (-(m : ℝ)) ≤ Real.exp (-(ε₁ ^ 2 * K / 4)) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      have h3 : ε₁ ^ 2 * K / 4 ≤ Real.exp 2 * K * q := by
        have hsq : ε₁ ^ 2 ≤ ε₁ := by nlinarith
        have h4 : (1 : ℝ) ≤ Real.exp 2 := by
          have := Real.add_one_le_exp 2; linarith
        have hq' : ε₁ ≤ q := by rw [hq]; linarith
        have a1 : ε₁ ^ 2 * K ≤ ε₁ * K := mul_le_mul_of_nonneg_right hsq hKpos'.le
        have a2 : ε₁ * K ≤ q * K := mul_le_mul_of_nonneg_right hq' hKpos'.le
        have a3 : q * K ≤ Real.exp 2 * (q * K) :=
          le_mul_of_one_le_left (by positivity) h4
        have a4 : Real.exp 2 * K * q = Real.exp 2 * (q * K) := by ring
        have : 0 ≤ ε₁ ^ 2 * K := by positivity
        linarith
      linarith
    linarith

end Pseudorandom.PS
