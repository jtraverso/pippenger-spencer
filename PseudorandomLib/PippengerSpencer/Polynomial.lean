/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.PippengerSpencer.ColourHypergraph
public import PseudorandomLib.Theorem12
public import PseudorandomLib.Asymptotics

/-! # Chromatic index under polynomial codegrees

**Theorem.** Let `r ≥ 2` and `δ ∈ (0,1)`. There are `γ > 0` and `D₀` such that every
`r`-uniform hypergraph `H` with maximum degree `≤ D`, codegrees `≤ D^{1-δ}` and at most
`exp(D^γ)` edges has a proper edge colouring with at most `D + D^{1-γ}` colours, whenever
`D ≥ D₀`.

Proof: apply Theorem 1.2 to the `(r+1)`-uniform colour hypergraph with `⌊D⌋` colours, with one
weight function per vertex `v` counting the edges at `v`. The resulting matching colours all but
`O(D^{1-ε})` edges at every vertex of large degree, and the leftover hypergraph has maximum degree
`O(D^{1-ε} + D^δ)`; it is coloured greedily.
-/

@[expose] public section

namespace Pseudorandom.PS

open Finset Filter

/-- `D exp(D^γ) ≤ exp(D^κ)` eventually, for `0 < γ < κ`. -/
theorem eventually_mul_exp_le_exp {γ κ : ℝ} (hγκ : γ < κ) (hκ : 0 < κ) :
    ∀ᶠ D : ℝ in atTop, D * Real.exp (D ^ γ) ≤ Real.exp (D ^ κ) := by
  filter_upwards [eventually_mul_log_le_rpow hκ 2,
    eventually_rpow_le_mul_rpow hγκ (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_gt_atTop (0 : ℝ)] with D h1 h2 h3
  calc D * Real.exp (D ^ γ) = Real.exp (Real.log D + D ^ γ) := by
        rw [Real.exp_add, Real.exp_log h3]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- The final numerical inequality for the number of colours. -/
theorem eventually_colour_count (r : ℝ) (hr : 0 < r) {δ e γ : ℝ} (hδ : δ < 1 - γ)
    (he : 1 - e < 1 - γ) (hγ : γ < 1) :
    ∀ᶠ D : ℝ in atTop, r * (2 * D ^ δ + 2 + D ^ (1 - e)) + 1 ≤ D ^ (1 - γ) := by
  filter_upwards [eventually_rpow_le_mul_rpow hδ (by positivity : (0 : ℝ) < 1 / (8 * r)),
    eventually_rpow_le_mul_rpow he (by positivity : (0 : ℝ) < 1 / (4 * r)),
    eventually_const_le_rpow (by linarith : (0 : ℝ) < 1 - γ) (2 * (2 * r + 1))]
    with D h1 h2 h3
  have e1 : r * (2 * D ^ δ) ≤ D ^ (1 - γ) / 4 := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * r)
    calc r * (2 * D ^ δ) = 2 * r * D ^ δ := by ring
      _ ≤ 2 * r * (1 / (8 * r) * D ^ (1 - γ)) := this
      _ = D ^ (1 - γ) / 4 := by field_simp; ring
  have e2 : r * D ^ (1 - e) ≤ D ^ (1 - γ) / 4 := by
    have := mul_le_mul_of_nonneg_left h2 hr.le
    calc r * D ^ (1 - e) ≤ r * (1 / (4 * r) * D ^ (1 - γ)) := this
      _ = D ^ (1 - γ) / 4 := by field_simp
  nlinarith

end PS

open Finset Filter PS in
/-- **Chromatic index under polynomial codegrees.** -/
theorem chromatic_index_polynomial (r : ℕ) (hr : 2 ≤ r) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ D₀ : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V))
      (D : ℝ), D₀ ≤ D → IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ D ^ (1 - δ)) →
      (H.card : ℝ) ≤ Real.exp (D ^ γ) →
      ∃ (m : ℕ) (c : Finset V → Fin m), (m : ℝ) ≤ D + D ^ (1 - γ) ∧
        IsProperEdgeColouring H m c := by
  set e : ℝ := δ / (50 * ((r + 1 : ℕ) : ℝ) ^ 2) with he_def
  have hR : (3 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by push_cast; exact_mod_cast (by omega : 3 ≤ r + 1)
  have he0 : 0 < e := by positivity
  have he1 : e < 1 := by
    rw [he_def, div_lt_one (by positivity)]; nlinarith
  have heδ : e < δ := by
    have h50 : (1 : ℝ) < 50 * ((r + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    rw [he_def, div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left h50 hδ0]
  set γ : ℝ := min (e ^ 2 / 2) ((1 - δ) / 2) with hγ_def
  have hγ0 : 0 < γ := lt_min (by positivity) (by linarith)
  have hγe2 : γ < e ^ 2 := by
    have := sq_pos_of_pos he0
    have : γ ≤ e ^ 2 / 2 := min_le_left _ _
    linarith
  have he2e : e ^ 2 < e := by nlinarith
  have hγδ : δ < 1 - γ := by
    have : γ ≤ (1 - δ) / 2 := min_le_right _ _
    linarith
  have hγ1 : γ < 1 := by linarith
  obtain ⟨Δ₀, hT⟩ := theorem_1_2 δ hδ0 hδ1 (r + 1) (by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp ((eventually_ge_atTop Δ₀).and
    ((eventually_ge_atTop (max 2 (r : ℝ))).and
    ((eventually_mul_exp_le_exp hγe2 (by positivity)).and
    (eventually_colour_count (r : ℝ) hrR (e := e) hγδ (by linarith) hγ1))))
  refine ⟨γ, hγ0, D₀, fun V _ _ H D hD huni hdeg hcod hcard => ?_⟩
  obtain ⟨hΔ₀, hD2, hexp, hcount⟩ := hD₀ D hD
  have hD2' : (2 : ℝ) ≤ D := (le_max_left _ _).trans hD2
  have hDr : (r : ℝ) ≤ D := (le_max_right _ _).trans hD2
  have hDpos : 0 < D := by linarith
  set C : ℕ := ⌊D⌋₊ with hC_def
  have hCD : (C : ℝ) ≤ D := Nat.floor_le hDpos.le
  have hDC : D < C + 1 := Nat.lt_floor_add_one D
  have hC0 : 0 < C := by
    have : (0 : ℝ) < C := by linarith
    exact_mod_cast this
  have hne : ∀ f ∈ H, f.Nonempty := fun f hf => by
    rw [← card_pos, huni f hf]; omega
  set G := colourHyp H C with hG_def
  set s : Finset V := H.biUnion id with hs_def
  -- hypotheses of Theorem 1.2 for the colour hypergraph
  have hGuni : IsUniform G (r + 1) := colourHyp_uniform huni
  have hGdeg : ∀ y, (degree G y : ℝ) ≤ D := by
    intro y
    rcases y with f | ⟨v, c⟩
    · exact (Nat.cast_le.mpr (degree_colourHyp_inl H f)).trans hCD
    · exact (Nat.cast_le.mpr (degree_colourHyp_inr H v c)).trans (hdeg v)
  have hone : (1 : ℝ) ≤ D ^ (1 - δ) := Real.one_le_rpow (by linarith) (by linarith)
  have hGcod : ∀ y z, y ≠ z → (codegree G y z : ℝ) ≤ D ^ (1 - δ) := by
    intro y z hyz
    rcases codegree_colourHyp_le (C := C) H y z hyz with h | ⟨u, v, huv, h⟩
    · exact (Nat.cast_le.mpr h).trans (by simpa using hone)
    · exact (Nat.cast_le.mpr h).trans (hcod u v huv)
  have hcap : D * Real.exp (D ^ γ) ≤ Real.exp (D ^ ((δ / (50 * ((r + 1 : ℕ) : ℝ) ^ 2)) ^ 2)) :=
    hexp
  have hGcard : (G.card : ℝ) ≤ Real.exp (D ^ ((δ / (50 * ((r + 1 : ℕ) : ℝ) ^ 2)) ^ 2)) := by
    have h1 : (G.card : ℝ) ≤ H.card * C := by exact_mod_cast card_colourHyp_le H
    have h2 : (H.card : ℝ) * C ≤ Real.exp (D ^ γ) * D :=
      mul_le_mul hcard hCD (Nat.cast_nonneg _) (Real.exp_pos _).le
    linarith
  have hscard : (Fintype.card {v // v ∈ s} : ℝ) ≤
      Real.exp (D ^ ((δ / (50 * ((r + 1 : ℕ) : ℝ) ^ 2)) ^ 2)) := by
    rw [Fintype.card_coe]
    have h1 : s.card ≤ ∑ f ∈ H, (id f).card := card_biUnion_le
    have h2 : ∑ f ∈ H, (id f).card = H.card * r := by
      rw [sum_const_nat (m := r) (fun f hf => by simpa using huni f hf)]
    have h3 : (s.card : ℝ) ≤ H.card * r := by exact_mod_cast h2 ▸ h1
    have h4 : (H.card : ℝ) * r ≤ Real.exp (D ^ γ) * D :=
      mul_le_mul hcard hDr (Nat.cast_nonneg _) (Real.exp_pos _).le
    linarith
  obtain ⟨M, hMG, hM, hW⟩ := hT D hΔ₀ (Finset V ⊕ (V × Fin C)) G hGuni hGdeg hGcod hGcard
    {v // v ∈ s} (fun v => wv v.1) (fun k x _ => wv_nonneg _ _) hscard
  -- the leftover hypergraph has small degrees
  set L := H \ col H M with hL_def
  set Lb : ℝ := 2 * D ^ δ + 2 + D ^ (1 - e) with hLb_def
  have hDδ : 0 ≤ D ^ δ := Real.rpow_nonneg hDpos.le _
  have hDe : 0 ≤ D ^ (1 - e) := Real.rpow_nonneg hDpos.le _
  have hLdeg : ∀ v, (degree L v : ℝ) ≤ Lb := by
    intro v
    have hsplit := degree_sdiff_col H M v
    have hsplitR : (degree L v : ℝ) =
        degree H v - (((col H M).filter (fun f => v ∈ f)).card : ℝ) := by
      rw [← hsplit]; push_cast; ring
    by_cases hv : v ∈ s
    · by_cases hbig : D ^ (1 + δ) ≤ (degree H v : ℝ) * C
      · have hcond : ∀ x ∈ G, wv v x * D ^ (1 + δ) ≤ weight (wv v) G := by
          intro x hx
          rw [weight_colourHyp hne]
          have := wv_le_one hx v
          have hp : 0 ≤ D ^ (1 + δ) := Real.rpow_nonneg hDpos.le _
          exact (mul_le_of_le_one_left hp this).trans hbig
        have hk := hW ⟨v, hv⟩ hcond
        simp only at hk
        rw [weight_matching hne hMG hM, weight_colourHyp hne] at hk
        have habs := (abs_le.mp hk).1
        set d : ℝ := (degree H v : ℝ) with hd_def
        have hd0 : 0 ≤ d := Nat.cast_nonneg _
        have hdD : d ≤ D := hdeg v
        have hDneg : D ^ (-e) * (d * C / D) ≤ D ^ (1 - e) := by
          have h1 : d * C / D ≤ D := by
            rw [div_le_iff₀ hDpos]
            exact mul_le_mul hdD hCD (Nat.cast_nonneg _) hDpos.le
          have h2 : D ^ (-e) * D = D ^ (1 - e) := by
            rw [show (1 - e) = -e + 1 by ring, Real.rpow_add hDpos, Real.rpow_one]
          calc D ^ (-e) * (d * C / D) ≤ D ^ (-e) * D :=
                mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hDpos.le _)
            _ = _ := h2
        have hdC : d - d * C / D ≤ 1 := by
          have : d - d * C / D = d * (D - C) / D := by field_simp
          rw [this, div_le_one hDpos]
          have : D - C ≤ 1 := by linarith
          calc d * (D - C) ≤ d * 1 := mul_le_mul_of_nonneg_left this hd0
            _ ≤ D := by linarith
        rw [hsplitR]
        linarith
      · push Not at hbig
        have hCD2 : D ≤ 2 * C := by linarith
        have hdsmall : (degree H v : ℝ) ≤ 2 * D ^ δ := by
          have hpow : D ^ (1 + δ) = D * D ^ δ := by
            rw [Real.rpow_add hDpos, Real.rpow_one]
          rw [hpow] at hbig
          by_contra hcon
          push Not at hcon
          have hC0' : (0 : ℝ) ≤ C := Nat.cast_nonneg _
          have h1 := mul_le_mul_of_nonneg_right hcon.le hC0'
          have h2 := mul_le_mul_of_nonneg_right hCD2 hDδ
          linarith
        have : (degree L v : ℝ) ≤ degree H v := by
          rw [hsplitR]; linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤
            (((col H M).filter (fun f => v ∈ f)).card : ℝ))]
        linarith
    · have h0 : degree H v = 0 := by
        unfold degree
        rw [card_eq_zero, filter_eq_empty_iff]
        intro f hf hvf
        exact hv (mem_biUnion.mpr ⟨f, hf, hvf⟩)
      have : degree L v ≤ degree H v := degree_mono' sdiff_subset v
      rw [h0] at this
      have : (degree L v : ℝ) = 0 := by exact_mod_cast Nat.le_zero.mp this
      rw [this]; positivity
  set Δ' : ℕ := ⌊Lb⌋₊ with hΔ'_def
  have hLdeg' : ∀ v, degree L v ≤ Δ' := fun v => Nat.le_floor (hLdeg v)
  obtain ⟨c₂, hc₂⟩ := exists_greedy_colouring r Δ' L
    (fun f hf => huni f (sdiff_subset hf)) hLdeg'
  have hglue := (colOf_proper H hM hC0).glue hc₂
  rw [union_sdiff_of_subset (col_subset H M)] at hglue
  refine ⟨C + (r * Δ' + 1), _, ?_, hglue⟩
  have hΔ'le : (Δ' : ℝ) ≤ Lb := Nat.floor_le (by positivity)
  push_cast
  have : (r : ℝ) * Δ' ≤ r * Lb := mul_le_mul_of_nonneg_left hΔ'le hrR.le
  linarith

end Pseudorandom
