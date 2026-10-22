/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.NibbleTrim
public import PseudorandomLib.NibbleMarginal

/-! # The trimmed nibble with small codegrees (towards Pippenger's theorem)

**Theorem (marginals under small codegrees).** Let `r ≥ 2` and `ε > 0`. There is `μ > 0` such
that every `r`-uniform hypergraph `H` with maximum degree `≤ D` and codegrees `≤ μ D` carries a
probability distribution on its matchings in which every edge is used with probability at
least `(1 - ε) / D`.

The proof runs the trimmed nibble of `NibbleTrim.lean` with a fixed number of rounds and a
fixed `θ`; the failure probabilities only depend on `μ` and tend to `0` as `μ → 0`.
-/

@[expose] public section

namespace Pseudorandom.Nibble

open Finset

/-- `q^t - t β ≤ LseqT t` when every round has survival factor `q` and failure `≤ β`. -/
theorem LseqT_ge {r : ℕ} {K : ℝ} {a D lam : ℕ → ℝ}
    (q bb : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hbb : 0 ≤ bb)
    (hq : ∀ t, Real.exp (-(a t * (r * D t))) = q) (hb : ∀ t, betaT r K a D lam t ≤ bb) :
    ∀ t : ℕ, q ^ t - t * bb ≤ LseqT r K a D lam t
  | 0 => by simp [LseqT]
  | t + 1 => by
    have ih := LseqT_ge q bb hq0 hq1 hbb hq hb t
    simp only [LseqT, hq t]
    have h1 : (q ^ t - t * bb) * q ≤ LseqT r K a D lam t * q :=
      mul_le_mul_of_nonneg_right ih hq0
    have h2 : t * bb * q ≤ t * bb := by
      have : (0 : ℝ) ≤ t * bb := by positivity
      nlinarith
    have h3 := hb t
    have h4 : (q ^ t - t * bb) * q = q ^ (t + 1) - t * bb * q := by ring
    push_cast
    linarith

/-- The final numerical estimate for the marginals (general version). -/
theorem marginal_sum_bound_gen (T : ℕ) (r θ q y bb D ζ A : ℝ) (as L : ℕ → ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hD : 0 < D) (hbb : 0 ≤ bb)
    (hy1 : y < 1) (h1y : 1 - y ≤ θ * (1 + 2 * θ))
    (hyT : y ^ T ≤ ζ) (hζ : ζ ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hqr : 1 - r * θ ≤ q) (has0 : ∀ t, 0 ≤ as t) (hasA : ∀ t, as t ≤ A) (hAθ : A ≤ θ)
    (hmain : ∀ t < T, q ^ (t + 1) * as t = θ * q * y ^ t / D)
    (hL : ∀ t, q ^ t - t * bb ≤ L t) :
    (1 - r * θ) * (1 - 5 / 2 * θ) * (1 - ζ) - D * (T ^ 2 * bb * A) ≤
      D * ∑ t ∈ range T, L t * ((1 - Real.exp (-as t)) * q) := by
  have hA0 : 0 ≤ A := (has0 0).trans (hasA 0)
  have hterm : ∀ t ∈ range T, θ * q * y ^ t / D * (1 - θ / 2) - t * bb * A ≤
      L t * ((1 - Real.exp (-as t)) * q) := by
    intro t ht
    have htT := mem_range.mp ht
    have ha0 := has0 t
    have ha1 := (hasA t).trans hAθ
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
    have h3 : t * bb * ((1 - Real.exp (-as t)) * q) ≤ t * bb * A := by
      apply mul_le_mul_of_nonneg_left _ htb
      calc _ ≤ as t * q := hFle
        _ ≤ A * 1 := mul_le_mul (hasA t) hq1 hq0 hA0
        _ = A := mul_one A
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
  have hgeom2 : (1 - ζ) / (1 + 2 * θ) ≤ θ * ∑ t ∈ range T, y ^ t := by
    rw [hgeom, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by linarith)]
    have : 0 ≤ 1 - ζ := by linarith
    have h1 : (1 - ζ) * (1 - y) ≤ (1 - ζ) * (θ * (1 + 2 * θ)) :=
      mul_le_mul_of_nonneg_left h1y this
    have h2 : (1 - ζ) ≤ 1 - y ^ T := by linarith
    have h3 : (1 - ζ) * (θ * (1 + 2 * θ)) ≤ (1 - y ^ T) * (θ * (1 + 2 * θ)) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    nlinarith
  have hcnt : ∑ t ∈ range T, (t : ℝ) ≤ T ^ 2 := by
    calc ∑ t ∈ range T, (t : ℝ) ≤ ∑ t ∈ range T, (T : ℝ) :=
          sum_le_sum fun t ht => by exact_mod_cast (mem_range.mp ht).le
      _ = (T : ℝ) ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hstep1 : D * (θ * q / D * (∑ t ∈ range T, y ^ t) * (1 - θ / 2)) =
      q * (1 - θ / 2) * (θ * ∑ t ∈ range T, y ^ t) := by
    field_simp
  have hstep2 : D * ((∑ t ∈ range T, (t : ℝ)) * bb * A) ≤ D * (T ^ 2 * bb * A) := by
    gcongr
  have hmul := mul_le_mul_of_nonneg_left hsum hD.le
  rw [mul_sub, hstep1] at hmul
  have hB : q * (1 - θ / 2) * ((1 - ζ) / (1 + 2 * θ)) ≤
      q * (1 - θ / 2) * (θ * ∑ t ∈ range T, y ^ t) :=
    mul_le_mul_of_nonneg_left hgeom2 (by nlinarith)
  have hA : (1 - 5 / 2 * θ) * (1 - ζ) ≤ (1 - θ / 2) * ((1 - ζ) / (1 + 2 * θ)) := by
    rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
    have : 0 ≤ 1 - ζ := by linarith
    have : (1 - 5 / 2 * θ) * (1 + 2 * θ) ≤ 1 - θ / 2 := by nlinarith
    nlinarith
  have hC : (1 - r * θ) * ((1 - 5 / 2 * θ) * (1 - ζ)) ≤
      q * ((1 - θ / 2) * ((1 - ζ) / (1 + 2 * θ))) := by
    apply mul_le_mul hqr hA (by nlinarith) hq0
  rw [← sum_mul] at hmul
  have e : q * (1 - θ / 2) * ((1 - ζ) / (1 + 2 * θ)) =
    q * ((1 - θ / 2) * ((1 - ζ) / (1 + 2 * θ))) := by ring
  have e2 : (1 - r * θ) * (1 - 5 / 2 * θ) * (1 - ζ) =
    (1 - r * θ) * ((1 - 5 / 2 * θ) * (1 - ζ)) := by ring
  linarith


/-- `e^{-u} ≤ 1/u` for `u > 0`. -/
theorem exp_neg_le_inv {u : ℝ} (hu : 0 < u) : Real.exp (-u) ≤ 1 / u := by
  rw [Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le hu
  linarith [Real.add_one_le_exp u]

/-- In an `r`-uniform hypergraph with `r ≥ 2`, an edge gives a codegree `≥ 1`. -/
theorem one_le_codegree_of_mem {V : Type*} [DecidableEq V] {H : Finset (Finset V)} {r : ℕ}
    (hr : 2 ≤ r) (huni : IsUniform H r) {e : Finset V} (he : e ∈ H) :
    ∃ u w, u ≠ w ∧ 1 ≤ codegree H u w := by
  have h1 : 1 < e.card := by rw [huni e he]; omega
  obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp h1
  refine ⟨u, w, huw, ?_⟩
  unfold codegree
  exact Finset.card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hu, hw⟩⟩

set_option maxHeartbeats 4000000 in
/-- **Marginals under small codegrees.** For `r ≥ 2` and `ε > 0` there is `μ > 0` such that
every `r`-uniform hypergraph with maximum degree `≤ D` and codegrees `≤ μ D` carries a
probability distribution on its matchings with all edge marginals `≥ (1 - ε) / D`. -/
theorem pippenger_marginal (r : ℕ) (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (D : ℝ),
      IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
      (∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ μ * D) →
      ∃ ν : Finset (Finset V) → ℝ, (∀ M, 0 ≤ ν M) ∧ ∑ M, ν M = 1 ∧
        (∀ M, ν M ≠ 0 → IsMatching M ∧ M ⊆ H) ∧
        ∀ e ∈ H, (1 - ε) / D ≤ ∑ M, ν M * (if e ∈ M then 1 else 0) := by
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
  refine ⟨μ, hμ0, fun V _ _ H D huni hdeg hcod => ?_⟩
  classical
  by_cases hH : H = ∅
  · refine ⟨fun M => if M = ∅ then 1 else 0, fun M => by dsimp only; split_ifs <;> norm_num,
      by simp, fun M hM => ?_, fun e he => by simp [hH] at he⟩
    have : M = ∅ := by by_contra h; exact hM (if_neg h)
    subst this
    exact ⟨fun e he => by simp at he, empty_subset _⟩
  obtain ⟨e₀, he₀⟩ := nonempty_iff_ne_empty.mpr hH
  obtain ⟨u₀, w₀, huw₀, hcod₀⟩ := one_le_codegree_of_mem hr huni he₀
  have hμD : 1 ≤ μ * D := le_trans (by exact_mod_cast hcod₀) (hcod u₀ w₀ huw₀)
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
  refine ⟨outMT H as Ds T, outMT_nonneg P T, outMT_sum P T,
    fun M hM => outMT_support P T M hM, fun e he => ?_⟩
  have hm := outMT_marginal P T he
  simp_rw [hq] at hm
  rw [div_le_iff₀ hD0]
  have := mul_le_mul_of_nonneg_left hm hD0.le
  have hgoal : 1 - ε ≤ D * ∑ M, outMT H as Ds T M * (if e ∈ M then 1 else 0) := by linarith
  linarith [mul_comm (∑ M, outMT H as Ds T M * (if e ∈ M then (1 : ℝ) else 0)) D]

end Pseudorandom.Nibble
