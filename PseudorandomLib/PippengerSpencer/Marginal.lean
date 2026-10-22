/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.Pippenger

/-! # The trimmed nibble with explicit parameters

This is `Pseudorandom.Nibble.pippenger_marginal` with the random matching made explicit: the
law of the matching is `outMT H as Ds T`, where the number of rounds `T` only depends on `r` and
`ε`, and the parameter sequences `as`, `Ds` only depend on `D` (not on `H`). This is what allows
the process to be run locally (see `LocalNibble.lean`). The proof is the one of
`pippenger_marginal`.
-/

@[expose] public section

namespace Pseudorandom.Nibble

open Finset

set_option maxHeartbeats 4000000 in
/-- The trimmed nibble with explicit parameters: every edge is in the output matching with
probability at least `(1 - ε)/D`. -/
theorem pippenger_process (r : ℕ) (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ T : ℕ, ∀ D : ℝ, 1 ≤ μ * D →
      ∃ as Ds : ℕ → ℝ, (∀ t, 0 ≤ as t) ∧ (∀ t, 0 ≤ Ds t) ∧ Ds 0 = D ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (H : Finset (Finset V)),
        IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
        (∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ μ * D) →
        ∀ e ∈ H, (1 - ε) / D ≤ ∑ M, outMT H as Ds T M * (if e ∈ M then 1 else 0) := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr1 : ((r - 1 : ℕ) : ℝ) = r - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  -- the parameters
  set ε₁ : ℝ := min ε 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  set θ : ℝ := ε₁ / (8 * (r + 3)) with hθdef
  have hθpos : 0 < θ := by positivity
  have hθr : ((r : ℝ) + 3) * θ = ε₁ / 8 := by rw [hθdef]; field_simp
  have hθ1 : θ ≤ 1 / 8 := by
    have : (1 : ℝ) ≤ r + 3 := by linarith
    nlinarith
  have hrθ : (r : ℝ) * θ ≤ 1 / 8 := by nlinarith
  set η : ℝ := θ ^ 2 with hηdef
  set c : ℝ := Real.exp (-(((r - 1 : ℕ) : ℝ) * θ)) with hcdef
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c ≤ 1 := Real.exp_le_one_iff.mpr (by rw [hr1]; nlinarith)
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
  set T : ℕ := ⌈Real.log (4 / ε₁) / θ⌉₊ with hTdef
  have hθT : Real.log (4 / ε₁) ≤ θ * T := by
    have := Nat.le_ceil (Real.log (4 / ε₁) / θ)
    rw [← hTdef, div_le_iff₀ hθpos] at this
    linarith
  set ζ : ℝ := Real.exp (-(θ * T)) with hζdef
  have hζ : ζ ≤ ε₁ / 4 := by
    rw [hζdef]
    calc Real.exp (-(θ * T)) ≤ Real.exp (-Real.log (4 / ε₁)) := Real.exp_le_exp.mpr (by linarith)
      _ = ε₁ / 4 := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have hζ0 : 0 ≤ ζ := (Real.exp_pos _).le
  set cT : ℝ := c ^ T with hcTdef
  have hcT0 : 0 < cT := pow_pos hc0 T
  have hcT1 : cT ≤ 1 := pow_le_one₀ hc0.le hc1
  set Z : ℝ := θ ^ 3 * cT * c ^ 2 / (6 * r ^ 2) with hZdef
  have hZ0 : 0 < Z := by positivity
  set w : ℝ := ε₁ * cT / (4 * ((T : ℝ) ^ 2 + 1) * θ * r) with hwdef
  have hw0 : 0 < w := by positivity
  set μ : ℝ := min (θ * cT / (2 * r ^ 2)) (Z * w) with hμdef
  have hμ0 : 0 < μ := lt_min (by positivity) (by positivity)
  have hμ1 : μ ≤ θ * cT / (2 * r ^ 2) := min_le_left _ _
  have hμ2 : μ ≤ Z * w := min_le_right _ _
  refine ⟨μ, hμ0, T, fun D hμD => ?_⟩
  classical
  have hD0 : 0 < D := by
    by_contra h; push_neg at h; nlinarith
  set K : ℝ := μ * D with hKdef
  have hKpos : 0 < K := by positivity
  -- degree bounds
  obtain ⟨Ds, hDs_eq⟩ : ∃ Ds : ℕ → ℝ, ∀ t, Ds t = D * x ^ (min t T) := ⟨_, fun t => rfl⟩
  obtain ⟨as, has_eq⟩ : ∃ as : ℕ → ℝ, ∀ t, as t = θ / Ds t := ⟨_, fun t => rfl⟩
  obtain ⟨ls, hls_eq⟩ : ∃ ls : ℕ → ℝ, ∀ t, ls t = η * Ds t * c := ⟨_, fun t => rfl⟩
  set Dmin : ℝ := D * cT with hDmin
  have hDminpos : 0 < Dmin := by positivity
  have hKDmin : 2 * r ^ 2 * K ≤ θ * Dmin := by
    rw [hKdef, hDmin]
    have := mul_le_mul_of_nonneg_right hμ1 hD0.le
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
    nlinarith
  have hDmin1 : 1 ≤ Dmin := by
    have : 2 * (r : ℝ) ^ 2 * 1 ≤ 2 * r ^ 2 * K := by gcongr
    nlinarith
  have hDs : ∀ t, Dmin ≤ Ds t := by
    intro t
    rw [hDs_eq]
    refine mul_le_mul_of_nonneg_left ?_ hD0.le
    exact (pow_le_pow_left₀ hc0.le hcx T).trans
      (pow_le_pow_of_le_one hx0.le hx1 (min_le_right _ _))
  have hDs1 : ∀ t, 1 ≤ Ds t := fun t => hDmin1.trans (hDs t)
  have hDspos : ∀ t, 0 < Ds t := fun t => lt_of_lt_of_le one_pos (hDs1 t)
  -- the degree recursion
  have hxs : ∀ t, Ds t * x ≤ Ds (t + 1) := by
    intro t
    rw [hDs_eq, hDs_eq, mul_assoc, ← pow_succ]
    apply mul_le_mul_of_nonneg_left _ hD0.le
    apply pow_le_pow_of_le_one hx0.le hx1
    omega
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
      have h2 : θ * (r ^ 2 * K) ≤ θ * (θ * Dmin / 2) := by
        gcongr; linarith
      have h3 : θ * (θ * Dmin / 2) ≤ θ ^ 2 / 2 * Ds t := by
        have := hDs t
        have : θ * θ * Dmin ≤ θ * θ * Ds t := by gcongr
        nlinarith
      linarith
    have hey : Real.exp y ≤ 1 + η := by
      have hη64 : η ≤ 1 / 64 := by rw [hηdef]; nlinarith
      have := exp_le_one_add_two_mul hy0 (by linarith); linarith
    have heq : Real.exp (-(as t * (((r - 1 : ℕ) : ℝ) * Ds t - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) =
        c * Real.exp y := by
      rw [hcdef, ← Real.exp_add, has_eq, hydef]; congr 1; field_simp; ring
    rw [heq, hls_eq]
    calc Ds t * (c * Real.exp y) + η * Ds t * c ≤ Ds t * (c * (1 + η)) + η * Ds t * c := by
          gcongr
      _ = Ds t * x := by rw [hxdef]; ring
      _ ≤ _ := hxs t
  refine ⟨as, Ds, fun t => by rw [has_eq]; exact div_nonneg hθpos.le (hDspos t).le,
    fun t => (hDspos t).le, by rw [hDs_eq]; simp, fun V _ _ H huni hdeg hcod e he => ?_⟩
  have P : ParamsT H r K as Ds ls :=
    { hr := by omega
      huni := huni
      hK := hKpos
      hcod := hcod
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
  set bb : ℝ := r * Real.exp (-(Z / μ)) with hbbdef
  have hbb0 : 0 ≤ bb := by positivity
  have hb : ∀ t, betaT r K as Ds ls t ≤ bb := by
    intro t
    have hp := hDspos t
    unfold betaT
    rw [hbbdef]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.exp_le_exp, neg_le_neg_iff]
    have hden : 0 < 2 * (2 * as t * r ^ 2 * K * Ds t ^ 2 + r * K * ls t) := by
      have := P.hlam t; have := P.ha t; positivity
    rw [div_le_div_iff₀ hμ0 hden]
    have hden2 : 2 * (2 * as t * r ^ 2 * K * Ds t ^ 2 + r * K * ls t) ≤
        6 * θ * r ^ 2 * K * Ds t := by
      rw [has_eq, hls_eq]
      have hrr : (r : ℝ) ≤ r ^ 2 := by nlinarith
      have hηθ : η * c ≤ θ := by rw [hηdef]; nlinarith
      have h1 : r * K * (η * Ds t * c) ≤ r ^ 2 * K * (θ * Ds t) := by
        have : r * K * (η * Ds t * c) = r * K * Ds t * (η * c) := by ring
        rw [this]
        have : r * K * Ds t * (η * c) ≤ r * K * Ds t * θ := by gcongr
        have : r * K * Ds t * θ ≤ r ^ 2 * K * Ds t * θ := by gcongr
        nlinarith
      have h2 : 2 * (θ / Ds t) * r ^ 2 * K * Ds t ^ 2 = 2 * θ * r ^ 2 * K * Ds t := by
        field_simp
      nlinarith
    have hZ0' : 0 ≤ Z := hZ0.le
    calc Z * (2 * (2 * as t * r ^ 2 * K * Ds t ^ 2 + r * K * ls t))
        ≤ Z * (6 * θ * r ^ 2 * K * Ds t) := mul_le_mul_of_nonneg_left hden2 hZ0'
      _ = θ ^ 4 * c ^ 2 * Dmin * Ds t * μ := by
          rw [hZdef, hKdef, hDmin]; field_simp
      _ ≤ θ ^ 4 * c ^ 2 * Ds t * Ds t * μ := by
          gcongr; exact hDs t
      _ = ls t ^ 2 * μ := by rw [hls_eq, hηdef]; ring
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
  have hyT : y ^ T ≤ ζ := by
    calc y ^ T ≤ Real.exp (-θ) ^ T := pow_le_pow_left₀ hy0 hyle T
      _ = ζ := by rw [hζdef, ← Real.exp_nat_mul]; ring_nf
  have hqr : 1 - r * θ ≤ q := by
    have := Real.add_one_le_exp (-(r * θ)); rw [hqdef]; linarith
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  set A : ℝ := θ / Dmin with hAdef
  have hasA : ∀ t, as t ≤ A := fun t => by
    rw [has_eq, hAdef]; exact div_le_div_of_nonneg_left hθpos.le hDminpos (hDs t)
  have hAθ : A ≤ θ := div_le_self hθpos.le hDmin1
  have hmain : ∀ t < T, q ^ (t + 1) * as t = θ * q * y ^ t / D := by
    intro t ht
    rw [has_eq, hDs_eq, min_eq_left ht.le, hydef, div_pow]
    field_simp
    ring
  have hL := LseqT_ge (r := r) (K := K) (a := as) (D := Ds) (lam := ls) q bb
    (Real.exp_pos _).le hq1 hbb0 hq hb
  have hfinal := marginal_sum_bound_gen T r θ q y bb D ζ A as (LseqT r K as Ds ls) hθpos hθ1
    hD0 hbb0 hy1 h1y hyT (by linarith) (Real.exp_pos _).le hq1 hqr P.ha hasA hAθ hmain hL
  -- the error term
  have hbbw : bb ≤ r * w := by
    rw [hbbdef]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : 1 / w ≤ Z / μ := by
      rw [div_le_div_iff₀ hw0 hμ0]; linarith
    calc Real.exp (-(Z / μ)) ≤ Real.exp (-(1 / w)) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1 / (1 / w) := exp_neg_le_inv (by positivity)
      _ = w := by field_simp
  have herr : D * ((T : ℝ) ^ 2 * bb * A) ≤ ε₁ / 4 := by
    have e1 : D * ((T : ℝ) ^ 2 * bb * A) = (T : ℝ) ^ 2 * θ / cT * bb := by
      rw [hAdef, hDmin]; field_simp
    have e2 : (T : ℝ) ^ 2 * θ / cT * (r * w) = ε₁ / 4 * ((T : ℝ) ^ 2 / ((T : ℝ) ^ 2 + 1)) := by
      rw [hwdef]; field_simp
    have e3 : (T : ℝ) ^ 2 / ((T : ℝ) ^ 2 + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    rw [e1]
    calc (T : ℝ) ^ 2 * θ / cT * bb ≤ (T : ℝ) ^ 2 * θ / cT * (r * w) :=
          mul_le_mul_of_nonneg_left hbbw (by positivity)
      _ = _ := e2
      _ ≤ ε₁ / 4 * 1 := mul_le_mul_of_nonneg_left e3 (by positivity)
      _ = ε₁ / 4 := mul_one _
  have hprod : 1 - ε₁ / 8 - ζ ≤ (1 - r * θ) * (1 - 5 / 2 * θ) * (1 - ζ) := by
    have h1 : 1 - ((r : ℝ) + 5 / 2) * θ ≤ (1 - r * θ) * (1 - 5 / 2 * θ) := by
      have : 0 ≤ (r : ℝ) * θ * (5 / 2 * θ) := by positivity
      nlinarith
    have h2 : ((r : ℝ) + 5 / 2) * θ ≤ ε₁ / 8 := by nlinarith
    have h3 : 0 ≤ 1 - ζ := by linarith
    have h4 : (1 - ε₁ / 8) * (1 - ζ) ≤ (1 - r * θ) * (1 - 5 / 2 * θ) * (1 - ζ) :=
      mul_le_mul_of_nonneg_right (by linarith) h3
    have : 0 ≤ ε₁ / 8 * ζ := by positivity
    nlinarith
  have hm := outMT_marginal P T he
  simp_rw [hq] at hm
  rw [div_le_iff₀ hD0]
  have := mul_le_mul_of_nonneg_left hm hD0.le
  have hgoal : 1 - ε ≤ D * ∑ M, outMT H as Ds T M * (if e ∈ M then 1 else 0) := by linarith
  linarith [mul_comm (∑ M, outMT H as Ds T M * (if e ∈ M then (1 : ℝ) else 0)) D]

end Pseudorandom.Nibble
