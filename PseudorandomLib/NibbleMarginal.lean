/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.NibbleIterate
public import PseudorandomLib.Asymptotics

/-! # The nibble produces a random matching with almost uniform marginals

**Theorem (nibble marginals).** Let `r ≥ 2` and `ρ > 0`, `κ, σ ≥ 0` with
`(2r + 4) ρ + κ + σ < 1`. For all large `D`, every `r`-uniform hypergraph `H` with maximum
degree `≤ D`, codegrees `≤ D^κ` and at most `exp(D^σ)` edges carries a probability
distribution on its matchings in which every edge is used with probability at least
`(1 - D^{-ρ}) / D`.

The proof runs the nibble of `NibbleIterate.lean` with `θ = D^{-2ρ}`, `η = θ²`,
`⌈2ρ log D / θ⌉` rounds and degree bounds `D_t = D (e^{-(r-1)θ} (1 + 2η))^t`.
-/

@[expose] public section

namespace Pseudorandom.Nibble

open Finset Filter

/-! ## The numerical conditions on `D` -/

/-- The numerical conditions on `D` used by the nibble. -/
structure NibbleFacts (r : ℕ) (ρ κ σ D : ℝ) : Prop where
  h1 : 1 ≤ D
  h2 : 4 * r ≤ D ^ (2 * ρ)
  h4 : 4 * r ^ 2 * Real.exp r ≤ D ^ (1 - κ - 2 * r * ρ)
  h5 : Real.exp r ≤ D ^ (1 - 2 * (r - 1) * ρ)
  h6 : Real.log r + (3 + 2 * ρ) * Real.log D + D ^ σ ≤
    D ^ (1 - (2 * r + 4) * ρ - κ) / (24 * r ^ 2 * Real.exp r)
  h7 : r + 5 ≤ D ^ ρ
  h8 : 2 * ρ * Real.log D * D ^ (2 * ρ) + 1 ≤ D

theorem eventually_nibbleFacts (r : ℕ) (hr : 1 ≤ r) {ρ κ σ : ℝ} (hρ : 0 < ρ) (hκ : 0 ≤ κ)
    (hσ : 0 ≤ σ) (hsum : (2 * r + 4) * ρ + κ + σ < 1) :
    ∀ᶠ D : ℝ in atTop, NibbleFacts r ρ κ σ D := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set C := 24 * (r : ℝ) ^ 2 * Real.exp r with hC
  have hCpos : 0 < C := by positivity
  set γ := 1 - (2 * r + 4) * ρ - κ with hγ
  have hγσ : σ < γ := by rw [hγ]; linarith
  have hγ0 : 0 < γ := by linarith
  have e4 : 0 < 1 - κ - 2 * r * ρ := by nlinarith
  have e5 : 0 < 1 - 2 * (r - 1) * ρ := by nlinarith
  have e8 : 0 < 1 - 2 * ρ := by nlinarith
  have hA := eventually_const_le_rpow (c := γ) hγ0 (4 * C * Real.log r)
  have hB := eventually_mul_log_le_rpow (c := γ) hγ0 (4 * C * (3 + 2 * ρ))
  have hS := eventually_rpow_le_mul_rpow (σ := σ) (γ := γ) (c := 1 / (2 * C)) hγσ (by positivity)
  have hL := eventually_mul_log_le_rpow (c := 1 - 2 * ρ) e8 (4 * ρ)
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    eventually_const_le_rpow (by positivity : (0 : ℝ) < 2 * ρ) (4 * r),
    eventually_const_le_rpow e4 (4 * r ^ 2 * Real.exp r),
    eventually_const_le_rpow e5 (Real.exp r),
    eventually_const_le_rpow hρ (r + 5), hA, hB, hS, hL] with D hD2 h2 h4 h5 h7 hA hB hS hL
  have hD0 : 0 < D := by linarith
  refine ⟨by linarith, h2, h4, h5, ?_, h7, ?_⟩
  · have hlog : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
    have h1 : Real.log r ≤ D ^ γ / (4 * C) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2' : (3 + 2 * ρ) * Real.log D ≤ D ^ γ / (4 * C) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h3 : D ^ σ ≤ D ^ γ / (2 * C) := by
      rw [div_eq_mul_inv, mul_comm]; simpa [one_div] using hS
    have : D ^ γ / (4 * C) + D ^ γ / (4 * C) + D ^ γ / (2 * C) = D ^ γ / C := by
      field_simp; ring
    linarith
  · have hpow : D ^ (1 - 2 * ρ) * D ^ (2 * ρ) = D := by
      rw [← Real.rpow_add hD0]; simp
    have hpos : 0 < D ^ (2 * ρ) := Real.rpow_pos_of_pos hD0 _
    have : 4 * ρ * Real.log D * D ^ (2 * ρ) ≤ D := by
      calc 4 * ρ * Real.log D * D ^ (2 * ρ) ≤ D ^ (1 - 2 * ρ) * D ^ (2 * ρ) :=
            mul_le_mul_of_nonneg_right hL hpos.le
        _ = D := hpow
    have hlog : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
    nlinarith

/-! ## Elementary inequalities -/

theorem exp_le_one_add_two_mul {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    Real.exp y ≤ 1 + 2 * y := by
  have h := exp_le_one_add_add_sq_div y (1 / 2) (by rw [abs_of_nonneg hy0]; exact hy1)
    (by norm_num)
  have : y ^ 2 / (2 * (1 - 1 / 2)) = y ^ 2 := by ring
  rw [this] at h
  nlinarith

theorem one_sub_exp_neg_le {a : ℝ} : 1 - Real.exp (-a) ≤ a := by
  linarith [Real.one_sub_le_exp_neg a]

theorem one_sub_exp_neg_ge {a : ℝ} (ha : 0 ≤ a) : a - a ^ 2 / 2 ≤ 1 - Real.exp (-a) := by
  have h1 := Real.quadratic_le_exp_of_nonneg ha
  have hpos : 0 < 1 + a + a ^ 2 / 2 := by positivity
  have h2 : Real.exp (-a) ≤ 1 / (1 + a + a ^ 2 / 2) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hpos h1
  have h3 : 1 / (1 + a + a ^ 2 / 2) ≤ 1 - a + a ^ 2 / 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg (a ^ 2)]
  linarith

/-- `q^t - t β ≤ Lseq t` when every round has survival factor `q` and failure `≤ β`. -/
theorem Lseq_ge {V : Type*} [DecidableEq V] {r : ℕ} {K : ℝ} {U : Finset V} {a D lam : ℕ → ℝ}
    (q bb : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hbb : 0 ≤ bb)
    (hq : ∀ t, Real.exp (-(a t * (r * D t))) = q) (hb : ∀ t, beta r K U a D lam t ≤ bb) :
    ∀ t : ℕ, q ^ t - t * bb ≤ Lseq r K U a D lam t
  | 0 => by simp [Lseq]
  | t + 1 => by
    have ih := Lseq_ge q bb hq0 hq1 hbb hq hb t
    simp only [Lseq, hq t]
    have h1 : (q ^ t - t * bb) * q ≤ Lseq r K U a D lam t * q :=
      mul_le_mul_of_nonneg_right ih hq0
    have h2 : t * bb * q ≤ t * bb := by
      have : (0 : ℝ) ≤ t * bb := by positivity
      nlinarith
    have h3 := hb t
    have h4 : (q ^ t - t * bb) * q = q ^ (t + 1) - t * bb * q := by ring
    push_cast
    linarith

/-- The final numerical estimate for the marginals. -/
theorem marginal_sum_bound (T : ℕ) (r θ q y bb D : ℝ) (as L : ℕ → ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hD : 1 ≤ D) (hTD : (T : ℝ) ≤ D) (hbb : 0 ≤ bb)
    (hDbb : D ^ 3 * bb ≤ θ) (hy1 : y < 1) (h1y : 1 - y ≤ θ * (1 + 2 * θ))
    (hyT : y ^ T ≤ θ) (hr0 : 0 ≤ r) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hqr : 1 - r * θ ≤ q) (has0 : ∀ t, 0 ≤ as t) (has1 : ∀ t, as t ≤ θ)
    (hmain : ∀ t < T, q ^ (t + 1) * as t = θ * q * y ^ t / D)
    (hL : ∀ t, q ^ t - t * bb ≤ L t) :
    1 - (r + 5) * θ ≤ D * ∑ t ∈ range T, L t * ((1 - Real.exp (-as t)) * q) := by
  have hD0 : 0 < D := by linarith
  have hterm : ∀ t ∈ range T, θ * q * y ^ t / D * (1 - θ / 2) - t * bb * θ ≤
      L t * ((1 - Real.exp (-as t)) * q) := by
    intro t ht
    have htT := mem_range.mp ht
    have ha0 := has0 t
    have ha1 := has1 t
    have hF0 : 0 ≤ (1 - Real.exp (-as t)) * q := by
      have : Real.exp (-as t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      exact mul_nonneg (by linarith) hq0
    have hFle : (1 - Real.exp (-as t)) * q ≤ as t * q :=
      mul_le_mul_of_nonneg_right one_sub_exp_neg_le hq0
    have hFge : (as t - as t ^ 2 / 2) * q ≤ (1 - Real.exp (-as t)) * q :=
      mul_le_mul_of_nonneg_right (one_sub_exp_neg_ge ha0) hq0
    have hqt0 : 0 ≤ q ^ t := pow_nonneg hq0 t
    have h1 : (q ^ t - t * bb) * ((1 - Real.exp (-as t)) * q) ≤
        L t * ((1 - Real.exp (-as t)) * q) := mul_le_mul_of_nonneg_right (hL t) hF0
    have h2 : q ^ t * ((as t - as t ^ 2 / 2) * q) ≤ q ^ t * ((1 - Real.exp (-as t)) * q) :=
      mul_le_mul_of_nonneg_left hFge hqt0
    have htb : (0 : ℝ) ≤ t * bb := by positivity
    have h3 : t * bb * ((1 - Real.exp (-as t)) * q) ≤ t * bb * θ := by
      apply mul_le_mul_of_nonneg_left _ htb
      calc _ ≤ as t * q := hFle
        _ ≤ θ * 1 := mul_le_mul ha1 hq1 hq0 hθ0.le
        _ = θ := mul_one θ
    have h4 : q ^ t * ((as t - as t ^ 2 / 2) * q) =
        q ^ (t + 1) * as t * (1 - as t / 2) := by ring
    have h5 : θ * q * y ^ t / D * (1 - θ / 2) ≤ q ^ (t + 1) * as t * (1 - as t / 2) := by
      rw [← hmain t htT]
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    linarith
  have hsum := sum_le_sum hterm
  rw [sum_sub_distrib, ← sum_mul, ← sum_mul] at hsum
  have hs1 : ∑ i ∈ range T, θ * q * y ^ i / D = θ * q / D * ∑ i ∈ range T, y ^ i := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [hs1] at hsum
  have hgeom : ∑ t ∈ range T, y ^ t = (1 - y ^ T) / (1 - y) := by
    rw [geom_sum_eq hy1.ne, div_eq_div_iff (by linarith) (by linarith)]; ring
  have hgeom2 : (1 - θ) / (1 + 2 * θ) ≤ θ * ∑ t ∈ range T, y ^ t := by
    rw [hgeom, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by linarith)]
    have : 0 ≤ 1 - θ := by linarith
    nlinarith
  have hcnt : ∑ t ∈ range T, (t : ℝ) ≤ D ^ 2 := by
    calc ∑ t ∈ range T, (t : ℝ) ≤ ∑ t ∈ range T, (T : ℝ) :=
          sum_le_sum fun t ht => by exact_mod_cast (mem_range.mp ht).le
      _ = (T : ℝ) ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]; ring
      _ ≤ D ^ 2 := by gcongr
  have hA : 1 - 7 / 2 * θ ≤ (1 - θ / 2) * ((1 - θ) / (1 + 2 * θ)) := by
    rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg θ, mul_pos hθ0 hθ0, mul_pos (mul_pos hθ0 hθ0) hθ0]
  have hstep1 : D * (θ * q / D * (∑ t ∈ range T, y ^ t) * (1 - θ / 2)) =
      q * (1 - θ / 2) * (θ * ∑ t ∈ range T, y ^ t) := by
    field_simp
  have hstep2 : D * ((∑ t ∈ range T, (t : ℝ)) * bb * θ) ≤ θ ^ 2 := by
    have : D * ((∑ t ∈ range T, (t : ℝ)) * bb * θ) ≤ D * (D ^ 2 * bb * θ) := by
      gcongr
    calc _ ≤ D * (D ^ 2 * bb * θ) := this
      _ = (D ^ 3 * bb) * θ := by ring
      _ ≤ θ * θ := by gcongr
      _ = θ ^ 2 := by ring
  have hmul := mul_le_mul_of_nonneg_left hsum hD0.le
  rw [mul_sub, hstep1] at hmul
  have hB : q * (1 - θ / 2) * ((1 - θ) / (1 + 2 * θ)) ≤
      q * (1 - θ / 2) * (θ * ∑ t ∈ range T, y ^ t) :=
    mul_le_mul_of_nonneg_left hgeom2 (by nlinarith)
  have hC : (1 - r * θ) * (1 - 7 / 2 * θ) ≤ q * ((1 - θ / 2) * ((1 - θ) / (1 + 2 * θ))) := by
    apply mul_le_mul hqr hA (by linarith) hq0
  rw [← sum_mul] at hmul
  have hθθ : θ ^ 2 ≤ θ / 8 := by nlinarith
  have hrθθ : 0 ≤ r * θ ^ 2 := by positivity
  nlinarith

/-! ## The main statement -/

set_option maxHeartbeats 4000000 in
/-- **Nibble marginals.** -/
theorem nibble_marginal (r : ℕ) (hr : 2 ≤ r) {ρ κ σ : ℝ} (hρ : 0 < ρ) (hκ : 0 ≤ κ)
    (hσ : 0 ≤ σ) (hsum : (2 * r + 4) * ρ + κ + σ < 1) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (H : Finset (Finset V)), IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
      (∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ D ^ κ) → (H.card : ℝ) ≤ Real.exp (D ^ σ) →
      ∃ μ : Finset (Finset V) → ℝ, (∀ M, 0 ≤ μ M) ∧ ∑ M, μ M = 1 ∧
        (∀ M, μ M ≠ 0 → IsMatching M ∧ M ⊆ H) ∧
        ∀ e ∈ H, (1 - D ^ (-ρ)) / D ≤ ∑ M, μ M * (if e ∈ M then 1 else 0) := by
  obtain ⟨D₀, hD₀⟩ := Filter.eventually_atTop.mp
    (eventually_nibbleFacts r (by omega) hρ hκ hσ hsum)
  refine ⟨D₀, fun D hD V _ _ H huni hdeg hcod hcard => ?_⟩
  have F := hD₀ D hD
  have hD1 : 1 ≤ D := F.h1
  have hD0 : 0 < D := by linarith
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr1 : ((r - 1 : ℕ) : ℝ) = r - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  -- the parameters
  set θ : ℝ := D ^ (-(2 * ρ)) with hθdef
  have hθpos : 0 < θ := Real.rpow_pos_of_pos hD0 _
  have hθinv : θ * D ^ (2 * ρ) = 1 := by
    rw [hθdef, ← Real.rpow_add hD0]; simp
  have hθsmall : θ ≤ 1 / (4 * r) := by
    have h := F.h2
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hθ1 : θ ≤ 1 / 8 := by
    have : 1 / (4 * (r : ℝ)) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  set η : ℝ := θ ^ 2 with hηdef
  set K : ℝ := D ^ κ with hKdef
  have hKpos : 0 < K := Real.rpow_pos_of_pos hD0 _
  set c : ℝ := Real.exp (-(((r - 1 : ℕ) : ℝ) * θ)) with hcdef
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c ≤ 1 := Real.exp_le_one_iff.mpr (by rw [hr1]; nlinarith)
  have hc34 : 3 / 4 ≤ c := by
    have h0 := Real.add_one_le_exp (-(((r - 1 : ℕ) : ℝ) * θ))
    rw [hr1] at h0
    rw [hcdef, hr1]
    have : (r - 1 : ℝ) * θ ≤ 1 / 4 := by
      have : (r : ℝ) * θ ≤ 1 / 4 := by
        rw [le_div_iff₀ (by positivity)] at hθsmall
        nlinarith
      nlinarith
    linarith
  set x : ℝ := c * (1 + 2 * η) with hxdef
  have hx0 : 0 < x := by positivity
  have hcx : c ≤ x := by nlinarith [sq_nonneg θ]
  have hx1 : x ≤ 1 := by
    have h1 : 1 + 2 * η ≤ Real.exp (((r - 1 : ℕ) : ℝ) * θ) := by
      have := Real.add_one_le_exp (((r - 1 : ℕ) : ℝ) * θ)
      rw [hr1] at this ⊢
      have : 2 * η ≤ (r - 1) * θ := by
        rw [hηdef]; nlinarith
      linarith
    calc x = c * (1 + 2 * η) := rfl
      _ ≤ c * Real.exp (((r - 1 : ℕ) : ℝ) * θ) := mul_le_mul_of_nonneg_left h1 hc0.le
      _ = 1 := by rw [hcdef, ← Real.exp_add]; simp
  set T : ℕ := ⌈2 * ρ * Real.log D / θ⌉₊ with hTdef
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hθT1 : 2 * ρ * Real.log D ≤ θ * T := by
    have := Nat.le_ceil (2 * ρ * Real.log D / θ)
    rw [← hTdef, div_le_iff₀ hθpos] at this
    linarith
  have hθT2 : θ * T ≤ 2 * ρ * Real.log D + θ := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * ρ * Real.log D / θ by positivity)
    rw [← hTdef] at this
    have h2 : θ * T ≤ θ * (2 * ρ * Real.log D / θ + 1) :=
      mul_le_mul_of_nonneg_left this.le hθpos.le
    rw [mul_add, mul_div_cancel₀ _ hθpos.ne', mul_one] at h2
    exact h2
  have hTD : (T : ℝ) ≤ D := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * ρ * Real.log D / θ by positivity)
    rw [← hTdef] at this
    have h8 := F.h8
    have : 2 * ρ * Real.log D / θ = 2 * ρ * Real.log D * D ^ (2 * ρ) := by
      rw [div_eq_iff hθpos.ne']
      linear_combination (2 * ρ * Real.log D) * hθinv.symm
    linarith
  -- degree bounds
  obtain ⟨Ds, hDs_eq⟩ : ∃ Ds : ℕ → ℝ, ∀ t, Ds t = D * x ^ (min t T) := ⟨_, fun t => rfl⟩
  obtain ⟨as, has_eq⟩ : ∃ as : ℕ → ℝ, ∀ t, as t = θ / Ds t := ⟨_, fun t => rfl⟩
  obtain ⟨ls, hls_eq⟩ : ∃ ls : ℕ → ℝ, ∀ t, ls t = η * Ds t * c := ⟨_, fun t => rfl⟩
  set Dmin : ℝ := D ^ (1 - 2 * (r - 1) * ρ) / Real.exp r with hDmin
  have hDmin1 : 1 ≤ Dmin := by
    rw [hDmin, le_div_iff₀ (Real.exp_pos _), one_mul]; exact F.h5
  have hDT : Dmin ≤ D * c ^ T := by
    have hcT : c ^ T = Real.exp (-((r - 1 : ℝ) * θ * T)) := by
      rw [hcdef, ← Real.exp_nat_mul, hr1]; ring_nf
    have h2 : Dmin = D * Real.exp (-((r - 1 : ℝ) * (2 * ρ * Real.log D)) - r) := by
      rw [hDmin, Real.rpow_def_of_pos hD0, ← Real.exp_sub,
        show Real.log D * (1 - 2 * (r - 1) * ρ) - r =
          Real.log D + (-((r - 1 : ℝ) * (2 * ρ * Real.log D)) - r) by ring,
        Real.exp_add, Real.exp_log hD0]
    have hr0 : (0 : ℝ) ≤ r - 1 := by linarith
    have h1 : -((r - 1 : ℝ) * (2 * ρ * Real.log D)) - r ≤ -((r - 1 : ℝ) * θ * T) := by
      have := mul_le_mul_of_nonneg_left hθT2 hr0
      nlinarith
    rw [hcT, h2]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) hD0.le
  have hDs : ∀ t, Dmin ≤ Ds t := by
    intro t
    rw [hDs_eq]
    refine hDT.trans (mul_le_mul_of_nonneg_left ?_ hD0.le)
    exact (pow_le_pow_left₀ hc0.le hcx T).trans
      (pow_le_pow_of_le_one hx0.le hx1 (min_le_right _ _))
  have hDs1 : ∀ t, 1 ≤ Ds t := fun t => hDmin1.trans (hDs t)
  have hDspos : ∀ t, 0 < Ds t := fun t => lt_of_lt_of_le one_pos (hDs1 t)
  -- two identities between the parameters
  have hθDmin : 4 * (r : ℝ) ^ 2 * K ≤ θ * Dmin := by
    have h4 := F.h4
    have e1 : θ * Dmin = D ^ (1 - 2 * r * ρ) / Real.exp r := by
      rw [hDmin, hθdef, mul_div_assoc', ← Real.rpow_add hD0]; congr 2; ring
    have e2 : D ^ (1 - κ - 2 * r * ρ) * K = D ^ (1 - 2 * r * ρ) := by
      rw [hKdef, ← Real.rpow_add hD0]; congr 1; ring
    rw [e1, le_div_iff₀ (Real.exp_pos _)]
    calc 4 * (r : ℝ) ^ 2 * K * Real.exp r = (4 * r ^ 2 * Real.exp r) * K := by ring
      _ ≤ D ^ (1 - κ - 2 * r * ρ) * K := mul_le_mul_of_nonneg_right h4 hKpos.le
      _ = _ := e2
  set γ : ℝ := 1 - (2 * r + 4) * ρ - κ with hγ
  have hθ3 : θ ^ 3 * Dmin = D ^ γ * K / Real.exp r := by
    rw [hDmin, hθdef, hKdef, hγ, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le, mul_div_assoc',
      ← Real.rpow_add hD0, ← Real.rpow_add hD0]
    congr 2; push_cast; ring
  -- the degree recursion
  have hxs : ∀ t, Ds t * x ≤ Ds (t + 1) := by
    intro t
    rw [hDs_eq, hDs_eq, mul_assoc, ← pow_succ]
    apply mul_le_mul_of_nonneg_left _ hD0.le
    apply pow_le_pow_of_le_one hx0.le hx1
    omega
  have hη1 : η ≤ θ := by
    rw [hηdef]; exact pow_le_of_le_one hθpos.le (by linarith) two_ne_zero
  have hstep : ∀ t, Ds t * Real.exp (-(as t * (((r - 1 : ℕ) : ℝ) * Ds t -
      ((r - 1 : ℕ) : ℝ) ^ 2 * K))) + ls t ≤ Ds (t + 1) := by
    intro t
    have hp := hDspos t
    set y := θ * (((r - 1 : ℕ) : ℝ)) ^ 2 * K / Ds t with hydef
    have hy0 : 0 ≤ y := by positivity
    have hyη : y ≤ η / 2 := by
      rw [hydef, div_le_iff₀ hp, hηdef]
      have hr1' : (((r - 1 : ℕ) : ℝ)) ^ 2 ≤ r ^ 2 := by rw [hr1]; nlinarith
      have h1 : θ * (((r - 1 : ℕ) : ℝ)) ^ 2 * K ≤ θ * (r ^ 2 * K) := by
        rw [mul_assoc]; gcongr
      have h2 : θ * (r ^ 2 * K) ≤ θ * (θ * Dmin / 4) := by
        gcongr; linarith
      have h3 : θ * (θ * Dmin / 4) ≤ θ ^ 2 / 2 * Ds t := by
        have := hDs t
        have : θ * θ * Dmin ≤ θ * θ * Ds t := by gcongr
        nlinarith
      linarith
    have hey : Real.exp y ≤ 1 + η := by
      have := exp_le_one_add_two_mul hy0 (by linarith); linarith
    have heq : Real.exp (-(as t * (((r - 1 : ℕ) : ℝ) * Ds t - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) =
        c * Real.exp y := by
      rw [hcdef, ← Real.exp_add, has_eq, hydef]; congr 1; field_simp; ring
    rw [heq, hls_eq]
    calc Ds t * (c * Real.exp y) + η * Ds t * c ≤ Ds t * (c * (1 + η)) + η * Ds t * c := by
          gcongr
      _ = Ds t * x := by rw [hxdef]; ring
      _ ≤ _ := hxs t
  set U : Finset V := H.biUnion id with hUdef
  have P : Params H r K U as Ds ls :=
    { hr := by omega
      huni := huni
      hK := hKpos
      hcod := hcod
      hU := fun e he => subset_biUnion_of_mem id he
      ha := fun t => by rw [has_eq]; exact div_nonneg hθpos.le (hDspos t).le
      hD := fun t => (hDspos t).le
      hlam := fun t => by rw [hls_eq]; have := hDspos t; positivity
      hstep := hstep
      hdeg0 := fun v => by rw [hDs_eq]; simpa using hdeg v }
  -- the survival factor and the failure probabilities
  set q : ℝ := Real.exp (-(r * θ)) with hqdef
  have hq : ∀ t, Real.exp (-(as t * (r * Ds t))) = q := by
    intro t
    rw [hqdef, has_eq]; congr 2; field_simp [(hDspos t).ne']
  set E : ℝ := D ^ γ / (24 * r ^ 2 * Real.exp r) with hEdef
  set bb : ℝ := r * Real.exp (D ^ σ) * Real.exp (-E) with hbbdef
  have hbb0 : 0 ≤ bb := by positivity
  have hUcard : (U.card : ℝ) ≤ r * Real.exp (D ^ σ) := by
    have h1 : U.card ≤ ∑ e ∈ H, (id e).card := card_biUnion_le
    have h2 : ∑ e ∈ H, (id e).card = H.card * r := by
      exact sum_const_nat (fun e he => huni e he)
    have h3 : (U.card : ℝ) ≤ H.card * r := by exact_mod_cast h2 ▸ h1
    nlinarith
  have hb : ∀ t, beta r K U as Ds ls t ≤ bb := by
    intro t
    have hp := hDspos t
    unfold beta
    rw [hbbdef]
    apply mul_le_mul hUcard _ (Real.exp_pos _).le (by positivity)
    rw [Real.exp_le_exp, neg_le_neg_iff]
    have hden : 0 < 2 * (2 * as t * r ^ 2 * K * Ds t ^ 2 + r * K * ls t) := by
      have := P.hlam t; have := P.ha t; positivity
    rw [le_div_iff₀ hden]
    have hZ : 6 * E * r ^ 2 * K = D ^ γ * K / Real.exp r / 4 := by
      rw [hEdef]; field_simp; ring
    have hden2 : 2 * (2 * as t * r ^ 2 * K * Ds t ^ 2 + r * K * ls t) ≤
        6 * θ * r ^ 2 * K * Ds t := by
      rw [has_eq, hls_eq]
      have hrr : (r : ℝ) ≤ r ^ 2 := by nlinarith
      have h1 : r * K * (η * Ds t * c) ≤ r ^ 2 * K * (θ * Ds t * 1) := by
        gcongr
      have h2 : 2 * (θ / Ds t) * r ^ 2 * K * Ds t ^ 2 = 2 * θ * r ^ 2 * K * Ds t := by
        field_simp
      nlinarith
    have hZle : D ^ γ * K / Real.exp r * (9 / 16) ≤ θ ^ 3 * Ds t * c ^ 2 := by
      rw [← hθ3]
      have : θ ^ 3 * Dmin ≤ θ ^ 3 * Ds t := by gcongr; exact hDs t
      have hc2 : 9 / 16 ≤ c ^ 2 := by nlinarith
      have : 0 ≤ θ ^ 3 * Dmin := by positivity
      nlinarith
    have hE0 : 0 ≤ E := by positivity
    calc E * (2 * (2 * as t * r ^ 2 * K * Ds t ^ 2 + r * K * ls t))
        ≤ E * (6 * θ * r ^ 2 * K * Ds t) := mul_le_mul_of_nonneg_left hden2 hE0
      _ = θ * Ds t * (6 * E * r ^ 2 * K) := by ring
      _ ≤ θ * Ds t * (θ ^ 3 * Ds t * c ^ 2) := by
          rw [hZ]; gcongr
          have hZ0 : 0 ≤ D ^ γ * K / Real.exp r := by positivity
          linarith
      _ = ls t ^ 2 := by rw [hls_eq, hηdef]; ring
  have hDbb : D ^ 3 * bb ≤ θ := by
    have h6 := F.h6
    have hrpos : (0 : ℝ) < r := by linarith
    have e1 : D ^ 3 * bb = Real.exp (3 * Real.log D + Real.log r + D ^ σ - E) := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log hrpos,
        show 3 * Real.log D = ((3 : ℕ) : ℝ) * Real.log D by norm_num, Real.exp_nat_mul,
        Real.exp_log hD0, hbbdef, Real.exp_neg]
      field_simp
    have e2 : θ = Real.exp (-(2 * ρ) * Real.log D) := by
      rw [hθdef, Real.rpow_def_of_pos hD0, mul_comm]
    rw [e1, e2, Real.exp_le_exp]
    have : E = D ^ (1 - (2 * r + 4) * ρ - κ) / (24 * r ^ 2 * Real.exp r) := by rw [hEdef, hγ]
    linarith
  -- the auxiliary ratio y
  have hqc : q = c * Real.exp (-θ) := by
    rw [hqdef, hcdef, ← Real.exp_add, hr1]; congr 1; ring
  set y : ℝ := q / x with hydef
  have hy_eq : y = Real.exp (-θ) / (1 + 2 * η) := by
    rw [hydef, hqc, hxdef]; field_simp
  have hyle : y ≤ Real.exp (-θ) := by
    rw [hy_eq]; exact div_le_self (Real.exp_pos _).le (by nlinarith)
  have hy0 : 0 ≤ y := by rw [hy_eq]; positivity
  have hy1 : y < 1 := hyle.trans_lt (Real.exp_lt_one_iff.mpr (by linarith))
  have h1y : 1 - y ≤ θ * (1 + 2 * θ) := by
    have he := Real.add_one_le_exp (-θ)
    have hpos : 0 < 1 + 2 * η := by positivity
    have : (1 - θ - 2 * θ ^ 2) * (1 + 2 * η) ≤ Real.exp (-θ) := by
      rw [hηdef]; nlinarith [pow_pos hθpos 3, pow_pos hθpos 4]
    have : 1 - θ * (1 + 2 * θ) ≤ y := by
      rw [hy_eq, le_div_iff₀ hpos]; linarith
    linarith
  have hyT : y ^ T ≤ θ := by
    calc y ^ T ≤ Real.exp (-θ) ^ T := pow_le_pow_left₀ hy0 hyle T
      _ = Real.exp (-(θ * T)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(2 * ρ) * Real.log D) := Real.exp_le_exp.mpr (by nlinarith)
      _ = θ := by rw [hθdef, Real.rpow_def_of_pos hD0, mul_comm]
  have hrθ : (r : ℝ) * θ ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hθsmall; nlinarith
  have hqr : 1 - r * θ ≤ q := by
    have := Real.add_one_le_exp (-(r * θ)); rw [hqdef]; linarith
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have has1 : ∀ t, as t ≤ θ := fun t => by rw [has_eq]; exact div_le_self hθpos.le (hDs1 t)
  have hmain : ∀ t < T, q ^ (t + 1) * as t = θ * q * y ^ t / D := by
    intro t ht
    rw [has_eq, hDs_eq, min_eq_left ht.le, hydef, div_pow]
    field_simp
    ring
  have hL := Lseq_ge (r := r) (K := K) (U := U) (a := as) (D := Ds) (lam := ls) q bb
    (Real.exp_pos _).le hq1 hbb0 hq hb
  have hfinal := marginal_sum_bound T r θ q y bb D as (Lseq r K U as Ds ls) hθpos hθ1 hD1 hTD
    hbb0 hDbb hy1 h1y hyT (by linarith) (Real.exp_pos _).le hq1 hqr P.ha has1 hmain hL
  have hrho : ((r : ℝ) + 5) * θ ≤ D ^ (-ρ) := by
    have e1 : θ = D ^ (-ρ) * D ^ (-ρ) := by rw [hθdef, ← Real.rpow_add hD0]; congr 1; ring
    have e2 : D ^ (-ρ) * D ^ ρ = 1 := by rw [← Real.rpow_add hD0]; simp
    have hpos : 0 < D ^ (-ρ) := Real.rpow_pos_of_pos hD0 _
    rw [e1]
    calc (r + 5) * (D ^ (-ρ) * D ^ (-ρ)) = D ^ (-ρ) * ((r + 5) * D ^ (-ρ)) := by ring
      _ ≤ D ^ (-ρ) * (D ^ ρ * D ^ (-ρ)) := by gcongr; exact F.h7
      _ = D ^ (-ρ) := by rw [mul_comm (D ^ ρ), e2, mul_one]
  refine ⟨outM H as Ds T, outM_nonneg P T, outM_sum P T,
    fun M hM => outM_support P T M hM, fun e he => ?_⟩
  have hm := outM_marginal P T he
  simp_rw [hq] at hm
  rw [div_le_iff₀ hD0]
  have := mul_le_mul_of_nonneg_left hm hD0.le
  convert (show 1 - D ^ (-ρ) ≤ D * ∑ M, outM H as Ds T M * (if e ∈ M then 1 else 0) by
    linarith) using 1
  ring

end Pseudorandom.Nibble
