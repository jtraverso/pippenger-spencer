/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.Bernstein

/-! # Concentration of weighted counts of monochromatic sets

Colour every coordinate `v ∈ ι` independently and uniformly with one of `m` colours. For a
family of sets `B s ⊆ ι` with weights `w s ≥ 0`, consider the weighted number of sets that are
entirely coloured with the fixed colour `a`:

  `cyl S w B a ω = ∑_{s ∈ S} w s · [ω ≡ a on B s]`.

Its expectation is `∑ w s m^{-|B s|}`, and it is concentrated by the Bernstein-type
bounded-differences inequality of `Bernstein.lean`: coordinate `v` changes it by at most
`c v = ∑_{s : v ∈ B s} w s`, and only if one of the two colours is `a`.
-/

@[expose] public section

namespace Pseudorandom

open Finset

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι]

/-- The uniform distribution on `m` colours at every coordinate. -/
noncomputable def unif (ι : Type*) (m : ℕ) : ι → Fin m → ℝ := fun _ _ => 1 / m

omit [Fintype ι] [DecidableEq ι] in
theorem unif_isPMF (m : ℕ) (hm : 0 < m) : IsPMF (unif ι m) := by
  refine ⟨fun _ _ => by unfold unif; positivity, fun _ => ?_⟩
  simp only [unif, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

open Classical in
/-- The weighted count of sets coloured entirely with colour `a`. -/
noncomputable def cyl {m : ℕ} (S : Finset σ) (w : σ → ℝ) (B : σ → Finset ι) (a : Fin m)
    (ω : ι → Fin m) : ℝ :=
  ∑ s ∈ S, w s * (if ∀ v ∈ B s, ω v = a then 1 else 0)

/-- The influence of a coordinate. -/
noncomputable def cylGap (S : Finset σ) (w : σ → ℝ) (B : σ → Finset ι) (v : ι) : ℝ :=
  ∑ s ∈ S.filter (fun s => v ∈ B s), w s

theorem cyl_pE {m : ℕ} (hm : 0 < m) (S : Finset σ) (w : σ → ℝ) (B : σ → Finset ι)
    (a : Fin m) : pE (unif ι m) (cyl S w B a) = ∑ s ∈ S, w s * (1 / m) ^ (B s).card := by
  classical
  unfold cyl
  rw [pE_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [pE_const_mul]
  congr 1
  have h := pProb_cylinder (unif_isPMF (ι := ι) m hm) (B s) (fun _ => a)
  simp only [unif, prod_const] at h
  rw [← h]; unfold pProb; congr 1; funext ω; split_ifs <;> rfl

theorem cyl_gap {m : ℕ} (S : Finset σ) (w : σ → ℝ) (hw : ∀ s ∈ S, 0 ≤ w s)
    (B : σ → Finset ι) (a : Fin m) : CoordGap (cyl S w B a) (cylGap S w B) := by
  classical
  intro v ω b b'
  unfold cyl cylGap
  rw [← sum_sub_distrib, sum_filter]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s hs => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (hw s hs)]
  by_cases hv : v ∈ B s
  · rw [if_pos hv]
    have : |(if ∀ u ∈ B s, Function.update ω v b u = a then (1 : ℝ) else 0) -
        (if ∀ u ∈ B s, Function.update ω v b' u = a then 1 else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    exact mul_le_of_le_one_right (hw s hs) this
  · rw [if_neg hv]
    have : (∀ u ∈ B s, Function.update ω v b u = a) ↔
        (∀ u ∈ B s, Function.update ω v b' u = a) := by
      constructor <;> intro h u hu <;> have := h u hu <;>
        rwa [Function.update_of_ne (show u ≠ v from fun h => hv (h ▸ hu))] at this ⊢
    simp [this]

theorem cyl_rare {m : ℕ} (S : Finset σ) (w : σ → ℝ) (B : σ → Finset ι) (a : Fin m) :
    CoordRare (cyl S w B a) (fun _ => {a}) := by
  classical
  intro v ω b b' hb hb'
  rw [mem_singleton] at hb hb'
  unfold cyl
  refine sum_congr rfl fun s _ => ?_
  congr 1
  by_cases hv : v ∈ B s
  · have h1 : ¬ ∀ u ∈ B s, Function.update ω v b u = a := fun h => hb (by simpa using h v hv)
    have h2 : ¬ ∀ u ∈ B s, Function.update ω v b' u = a := fun h => hb' (by simpa using h v hv)
    rw [if_neg h1, if_neg h2]
  · have : (∀ u ∈ B s, Function.update ω v b u = a) ↔
        (∀ u ∈ B s, Function.update ω v b' u = a) := by
      constructor <;> intro h u hu <;> have := h u hu <;>
        rwa [Function.update_of_ne (show u ≠ v from fun h => hv (h ▸ hu))] at this ⊢
    simp [this]

theorem sum_cylGap (S : Finset σ) (w : σ → ℝ) (B : σ → Finset ι) :
    ∑ v, cylGap S w B v = ∑ s ∈ S, w s * (B s).card := by
  classical
  unfold cylGap
  simp_rw [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  simp

omit [Fintype ι] in
theorem cylGap_nonneg (S : Finset σ) (w : σ → ℝ) (hw : ∀ s ∈ S, 0 ≤ w s)
    (B : σ → Finset ι) (v : ι) : 0 ≤ cylGap S w B v :=
  sum_nonneg fun s hs => hw s (mem_filter.mp hs).1

/-- Variance proxy for `cyl`. -/
theorem cyl_var_le {m : ℕ} (S : Finset σ) (w : σ → ℝ) (hw : ∀ s ∈ S, 0 ≤ w s)
    (B : σ → Finset ι) (L Wt : ℝ) (hL : ∀ v, cylGap S w B v ≤ L)
    (hWt : ∑ s ∈ S, w s * (B s).card ≤ Wt) (hL0 : 0 ≤ L) :
    ∑ v, (1 / (m : ℝ)) * cylGap S w B v ^ 2 ≤ L * Wt / m := by
  have h1 : ∀ v, (1 / (m : ℝ)) * cylGap S w B v ^ 2 ≤ (L / m) * cylGap S w B v := by
    intro v
    have h0 := cylGap_nonneg S w hw B v
    have : cylGap S w B v ^ 2 ≤ L * cylGap S w B v := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (hL v) h0
    rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right this (Nat.cast_nonneg m)
  calc _ ≤ ∑ v, (L / m) * cylGap S w B v := sum_le_sum fun v _ => h1 v
    _ = (L / m) * ∑ s ∈ S, w s * (B s).card := by rw [← mul_sum, sum_cylGap]
    _ ≤ (L / m) * Wt := mul_le_mul_of_nonneg_left hWt (by positivity)
    _ = L * Wt / m := by ring

/-- **Upper tail** for weighted monochromatic counts. -/
theorem cyl_upper {m : ℕ} (hm : 0 < m) (S : Finset σ) (w : σ → ℝ) (hw : ∀ s ∈ S, 0 ≤ w s)
    (B : σ → Finset ι) (a : Fin m) (L Wt : ℝ) (hL0 : 0 < L) (hL : ∀ v, cylGap S w B v ≤ L)
    (hWt : ∑ s ∈ S, w s * (B s).card ≤ Wt) (t : ℝ) (ht : 0 < t) :
    pProb (unif ι m) (fun ω => t ≤ cyl S w B a ω - pE (unif ι m) (cyl S w B a)) ≤
      Real.exp (-(t ^ 2 / (2 * (L * Wt / m + L * t)))) := by
  have h := pE_upper_tail (unif ι m) (unif_isPMF m hm) (cyl S w B a) (cylGap S w B)
    (fun _ => 1 / (m : ℝ)) (fun _ => {a}) L hL0 (fun v => ⟨cylGap_nonneg S w hw B v, hL v⟩)
    (cyl_gap S w hw B a) (cyl_rare S w B a) (fun v => by simp [unif]) t ht
  refine h.trans (Real.exp_le_exp.mpr (neg_le_neg ?_))
  have hv := cyl_var_le (m := m) S w hw B L Wt hL hWt hL0.le
  have hpos : 0 < 2 * ((∑ v, (1 / (m : ℝ)) * cylGap S w B v ^ 2) + L * t) := by
    have : 0 ≤ ∑ v, (1 / (m : ℝ)) * cylGap S w B v ^ 2 :=
      sum_nonneg fun v _ => by positivity
    positivity
  exact div_le_div_of_nonneg_left (by positivity) hpos (by linarith)

/-- **Lower tail** for weighted monochromatic counts. -/
theorem cyl_lower {m : ℕ} (hm : 0 < m) (S : Finset σ) (w : σ → ℝ) (hw : ∀ s ∈ S, 0 ≤ w s)
    (B : σ → Finset ι) (a : Fin m) (L Wt : ℝ) (hL0 : 0 < L) (hL : ∀ v, cylGap S w B v ≤ L)
    (hWt : ∑ s ∈ S, w s * (B s).card ≤ Wt) (t : ℝ) (ht : 0 < t) :
    pProb (unif ι m) (fun ω => t ≤ pE (unif ι m) (cyl S w B a) - cyl S w B a ω) ≤
      Real.exp (-(t ^ 2 / (2 * (L * Wt / m + L * t)))) := by
  have h := pE_lower_tail (unif ι m) (unif_isPMF m hm) (cyl S w B a) (cylGap S w B)
    (fun _ => 1 / (m : ℝ)) (fun _ => {a}) L hL0 (fun v => ⟨cylGap_nonneg S w hw B v, hL v⟩)
    (cyl_gap S w hw B a) (cyl_rare S w B a) (fun v => by simp [unif]) t ht
  refine h.trans (Real.exp_le_exp.mpr (neg_le_neg ?_))
  have hv := cyl_var_le (m := m) S w hw B L Wt hL hWt hL0.le
  have hpos : 0 < 2 * ((∑ v, (1 / (m : ℝ)) * cylGap S w B v ^ 2) + L * t) := by
    have : 0 ≤ ∑ v, (1 / (m : ℝ)) * cylGap S w B v ^ 2 :=
      sum_nonneg fun v _ => by positivity
    positivity
  exact div_le_div_of_nonneg_left (by positivity) hpos (by linarith)

end Pseudorandom
