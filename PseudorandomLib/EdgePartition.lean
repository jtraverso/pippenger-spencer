/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.VertexPartition

/-! # Step 2: a random edge partition

Every edge receives one of `q` colours uniformly at random. For a family of edge sets `A i`
(the parts of Step 1) let `cls A f i j` be the edges of `A i` with colour `j`. With positive
probability all degrees, codegrees and relevant weights of all classes are close to their
expectations (upper bounds only).
-/

@[expose] public section

namespace Pseudorandom

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `A i` with colour `j`. -/
def cls {p q : ℕ} (A : Fin p → Finset (Finset V)) (f : Finset V → Fin q) (i : Fin p)
    (j : Fin q) : Finset (Finset V) :=
  (A i).filter (fun e => f e = j)

omit [Fintype V] [DecidableEq V] in
theorem cls_subset {p q : ℕ} (A : Fin p → Finset (Finset V)) (f : Finset V → Fin q) (i : Fin p)
    (j : Fin q) : cls A f i j ⊆ A i := filter_subset _ _

/-! ## Colour classes of single edges -/

section Single

variable {q : ℕ}

theorem cyl_single_eq (S : Finset (Finset V)) (w : Finset V → ℝ) (j : Fin q)
    (f : Finset V → Fin q) :
    cyl S w (fun e => {e}) j f = ∑ e ∈ S.filter (fun e => f e = j), w e := by
  classical
  unfold cyl
  rw [sum_filter]
  refine sum_congr rfl fun e _ => ?_
  simp only [mem_singleton, forall_eq]
  split_ifs <;> simp

theorem pE_cyl_single (hq : 0 < q) (S : Finset (Finset V)) (w : Finset V → ℝ) (j : Fin q) :
    pE (unif (Finset V) q) (cyl S w (fun e => {e}) j) = (∑ e ∈ S, w e) * (1 / q) := by
  rw [cyl_pE hq, sum_mul]
  simp

omit [Fintype V] in
theorem cylGap_single_le (S : Finset (Finset V)) (w : Finset V → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hw : ∀ e ∈ S, w e ≤ L) (v : Finset V) : cylGap S w (fun e => {e}) v ≤ L := by
  classical
  unfold cylGap
  by_cases hv : v ∈ S
  · have : S.filter (fun s => v ∈ ({s} : Finset (Finset V))) = {v} := by
      ext s; simp only [mem_filter, mem_singleton]; constructor
      · rintro ⟨_, h⟩; exact h.symm
      · rintro rfl; exact ⟨hv, rfl⟩
    rw [this, sum_singleton]; exact hw v hv
  · have : S.filter (fun s => v ∈ ({s} : Finset (Finset V))) = ∅ := by
      rw [filter_eq_empty_iff]; intro s hs h; rw [mem_singleton] at h; exact hv (h ▸ hs)
    rw [this, sum_empty]; exact hL

/-- Tail bound for the weight of a colour class. -/
theorem single_tail (hq : 0 < q) (S : Finset (Finset V)) (w : Finset V → ℝ)
    (hw0 : ∀ e ∈ S, 0 ≤ w e) (L Wt : ℝ) (hL : 0 < L) (hwL : ∀ e ∈ S, w e ≤ L)
    (hWt : ∑ e ∈ S, w e ≤ Wt) (j : Fin q) (t : ℝ) (ht : 0 < t) :
    pProb (unif (Finset V) q) (fun f => t ≤ cyl S w (fun e => {e}) j f -
        pE (unif (Finset V) q) (cyl S w (fun e => {e}) j)) ≤
      Real.exp (-(t ^ 2 / (2 * (L * Wt / q + L * t)))) := by
  refine cyl_upper hq S w hw0 (fun e => {e}) j L Wt hL
    (cylGap_single_le S w L hL.le hwL) ?_ t ht
  simpa using hWt

end Single

/-! ## Degrees and codegrees outside the vertex set of `H` -/

omit [Fintype V] in
theorem codegree_eq_zero_of_not_mem (A H : Finset (Finset V)) (hA : A ⊆ H) {x y : V}
    (h : x ∉ H.biUnion id ∨ y ∉ H.biUnion id) : codegree A x y = 0 := by
  unfold codegree
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro e he ⟨hx, hy⟩
  rcases h with h | h
  · exact h (mem_biUnion.mpr ⟨e, hA he, hx⟩)
  · exact h (mem_biUnion.mpr ⟨e, hA he, hy⟩)

/-! ## Existence of a good edge partition -/

/-- **Step 2.** A random edge partition is good with positive probability; an additional bad
event `Bad` of probability at most `πB` can be avoided at the same time. -/
theorem edge_partition_ext {p q : ℕ} (hq : 0 < q) (H : Finset (Finset V))
    (A : Fin p → Finset (Finset V)) (hA : ∀ i, A i ⊆ H) (D₁ C t₃ t₄ : ℝ) (ht₃ : 0 < t₃)
    (ht₄ : 0 < t₄) (hdeg : ∀ i x, (degree (A i) x : ℝ) ≤ D₁)
    (hcod : ∀ i x y, x ≠ y → (codegree (A i) x y : ℝ) ≤ C)
    {ι : Type*} (W : ι → Finset V → ℝ) (K : Finset ι) (η β γ : ℝ) (hη : 0 < η) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hW0 : ∀ k ∈ K, ∀ e ∈ H, 0 ≤ W k e) (hWpos : ∀ k ∈ K, 0 < weight (W k) H)
    (hWmax : ∀ k ∈ K, ∀ e ∈ H, W k e ≤ η * weight (W k) H)
    (hWA : ∀ k ∈ K, ∀ i, weight (W k) (A i) ≤ β * weight (W k) H)
    (Bad : (Finset V → Fin q) → Prop) (πB : ℝ) (hBad : pProb (unif (Finset V) q) Bad ≤ πB)
    (hfail : ((H.biUnion id).card * p * q : ℝ) *
        Real.exp (-(t₃ ^ 2 / (2 * (1 * D₁ / q + 1 * t₃)))) +
      ((H.biUnion id).card ^ 2 * p * q : ℝ) *
        Real.exp (-(t₄ ^ 2 / (2 * (1 * C / q + 1 * t₄)))) +
      (K.card * p * q : ℝ) * Real.exp (-(γ ^ 2 / (2 * η * (β / q + γ)))) + πB < 1) :
    ∃ f : Finset V → Fin q,
      (∀ i j x, (degree (cls A f i j) x : ℝ) ≤ D₁ / q + t₃) ∧
      (∀ i j x y, x ≠ y → (codegree (cls A f i j) x y : ℝ) ≤ C / q + t₄) ∧
      (∀ k ∈ K, ∀ i j, weight (W k) (cls A f i j) ≤ β * weight (W k) H / q +
        γ * weight (W k) H) ∧ ¬ Bad f := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hP := unif_isPMF (ι := Finset V) q hq
  set U := H.biUnion id with hU
  set Sd : Fin p → V → Finset (Finset V) := fun i x => (A i).filter (fun e => x ∈ e)
  set Sc : Fin p → V × V → Finset (Finset V) :=
    fun i xy => (A i).filter (fun e => xy.1 ∈ e ∧ xy.2 ∈ e)
  have hdegS : ∀ i x (j : Fin q) (f : Finset V → Fin q), (degree (cls A f i j) x : ℝ) =
      cyl (Sd i x) (fun _ => 1) (fun e => {e}) j f := by
    intro i x j f
    rw [cyl_single_eq, sum_const, nsmul_eq_mul, mul_one]
    unfold degree cls
    congr 2
    ext e; simp only [Sd, mem_filter]; tauto
  have hcodS : ∀ i x y (j : Fin q) (f : Finset V → Fin q), (codegree (cls A f i j) x y : ℝ) =
      cyl (Sc i (x, y)) (fun _ => 1) (fun e => {e}) j f := by
    intro i x y j f
    rw [cyl_single_eq, sum_const, nsmul_eq_mul, mul_one]
    unfold codegree cls
    congr 2
    ext e; simp only [Sc, mem_filter]; tauto
  have hwS : ∀ k i (j : Fin q) (f : Finset V → Fin q), weight (W k) (cls A f i j) = cyl (A i) (W k) (fun e => {e}) j f := by
    intro k i j f
    rw [cyl_single_eq]; rfl
  set P3 := U ×ˢ ((univ : Finset (Fin p)) ×ˢ (univ : Finset (Fin q)))
  set P4 := (U ×ˢ U).filter (fun xy => xy.1 ≠ xy.2) ×ˢ
    ((univ : Finset (Fin p)) ×ˢ (univ : Finset (Fin q)))
  set P5 := K ×ˢ ((univ : Finset (Fin p)) ×ˢ (univ : Finset (Fin q)))
  set bad3 : (Finset V → Fin q) → Prop := fun f => ∃ a ∈ P3,
    t₃ ≤ cyl (Sd a.2.1 a.1) (fun _ => 1) (fun e => {e}) a.2.2 f -
      pE (unif (Finset V) q) (cyl (Sd a.2.1 a.1) (fun _ => 1) (fun e => {e}) a.2.2)
  set bad4 : (Finset V → Fin q) → Prop := fun f => ∃ a ∈ P4,
    t₄ ≤ cyl (Sc a.2.1 a.1) (fun _ => 1) (fun e => {e}) a.2.2 f -
      pE (unif (Finset V) q) (cyl (Sc a.2.1 a.1) (fun _ => 1) (fun e => {e}) a.2.2)
  set bad5 : (Finset V → Fin q) → Prop := fun f => ∃ a ∈ P5,
    γ * weight (W a.1) H ≤ cyl (A a.2.1) (W a.1) (fun e => {e}) a.2.2 f -
      pE (unif (Finset V) q) (cyl (A a.2.1) (W a.1) (fun e => {e}) a.2.2)
  have h3 : pProb (unif (Finset V) q) bad3 ≤
      (U.card * p * q : ℝ) * Real.exp (-(t₃ ^ 2 / (2 * (1 * D₁ / q + 1 * t₃)))) := by
    refine (pProb_exists_le hP _ _).trans ?_
    refine (sum_le_sum fun a _ => single_tail hq (Sd a.2.1 a.1) (fun _ => 1)
      (fun _ _ => zero_le_one) 1 D₁ one_pos (fun _ _ => le_rfl) ?_ a.2.2 t₃ ht₃).trans
      (le_of_eq ?_)
    · have := hdeg a.2.1 a.1
      unfold degree at this
      simpa [Sd] using this
    · rw [sum_const, card_product, card_product, card_univ, card_univ, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have h4 : pProb (unif (Finset V) q) bad4 ≤
      (U.card ^ 2 * p * q : ℝ) * Real.exp (-(t₄ ^ 2 / (2 * (1 * C / q + 1 * t₄)))) := by
    refine (pProb_exists_le hP _ _).trans ?_
    refine (sum_le_sum fun a ha => single_tail hq (Sc a.2.1 a.1) (fun _ => 1)
      (fun _ _ => zero_le_one) 1 C one_pos (fun _ _ => le_rfl) ?_ a.2.2 t₄ ht₄).trans ?_
    · have hne : a.1.1 ≠ a.1.2 := (mem_filter.mp (mem_product.mp ha).1).2
      have := hcod a.2.1 a.1.1 a.1.2 hne
      unfold codegree at this
      simpa [Sc] using this
    · rw [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      rw [card_product, card_product, card_univ, card_univ, Fintype.card_fin,
        Fintype.card_fin]
      have : ((U ×ˢ U).filter (fun xy => xy.1 ≠ xy.2)).card ≤ U.card ^ 2 := by
        refine (card_filter_le _ _).trans ?_
        rw [card_product, sq]
      push_cast
      have h' : (((U ×ˢ U).filter (fun xy => xy.1 ≠ xy.2)).card : ℝ) ≤ U.card ^ 2 := by
        exact_mod_cast this
      have : (0 : ℝ) ≤ p * q := by positivity
      nlinarith
  have h5 : pProb (unif (Finset V) q) bad5 ≤
      (K.card * p * q : ℝ) * Real.exp (-(γ ^ 2 / (2 * η * (β / q + γ)))) := by
    refine (pProb_exists_le hP _ _).trans ?_
    refine (sum_le_sum (g := fun _ => Real.exp (-(γ ^ 2 / (2 * η * (β / q + γ)))))
      fun a ha => ?_).trans (le_of_eq ?_)
    · have hk := (mem_product.mp ha).1
      set ω := weight (W a.1) H
      have hω := hWpos a.1 hk
      have h := single_tail hq (A a.2.1) (W a.1) (fun e he => hW0 a.1 hk e (hA _ he))
        (η * ω) (β * ω) (by positivity) (fun e he => hWmax a.1 hk e (hA _ he))
        (hWA a.1 hk a.2.1) a.2.2 (γ * ω) (by positivity)
      refine h.trans (le_of_eq ?_)
      have : 0 < β + γ * q := by positivity
      have hω0 : ω ≠ 0 := hω.ne'
      congr 2
      field_simp
    · rw [sum_const, card_product, card_product, card_univ, card_univ, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have hall : pProb (unif (Finset V) q) (fun f => bad3 f ∨ bad4 f ∨ bad5 f ∨ Bad f) < 1 := by
    have := pProb_or_le hP bad3 (fun f => bad4 f ∨ bad5 f ∨ Bad f)
    have := pProb_or_le hP bad4 (fun f => bad5 f ∨ Bad f)
    have := pProb_or_le hP bad5 Bad
    linarith
  obtain ⟨f, _, hf⟩ := exists_of_pProb_lt_one hP hall
  simp only [not_or] at hf
  obtain ⟨n3, n4, n5, n6⟩ := hf
  refine ⟨f, fun i j x => ?_, fun i j x y hxy => ?_, fun k hk i j => ?_, n6⟩
  · by_cases hx : x ∈ U
    · have hn : ¬ (t₃ ≤ cyl (Sd i x) (fun _ => 1) (fun e => {e}) j f -
          pE (unif (Finset V) q) (cyl (Sd i x) (fun _ => 1) (fun e => {e}) j)) :=
        fun h => n3 ⟨(x, i, j), by simp [P3, hx], h⟩
      push_neg at hn
      rw [pE_cyl_single hq] at hn
      rw [hdegS]
      have hd := hdeg i x
      have : (∑ e ∈ Sd i x, (fun _ => (1 : ℝ)) e) = degree (A i) x := by
        simp only [sum_const, nsmul_eq_mul, mul_one]; rfl
      rw [this] at hn
      have : (degree (A i) x : ℝ) * (1 / q) ≤ D₁ / q := by
        rw [mul_one_div]; exact div_le_div_of_nonneg_right hd hqR.le
      linarith
    · rw [degree_eq_zero_of_not_mem_biUnion _ H ((cls_subset A f i j).trans (hA i)) hx]
      have : 0 ≤ D₁ := le_trans (by positivity) (hdeg i x)
      simp only [Nat.cast_zero]
      positivity
  · by_cases hU2 : x ∈ U ∧ y ∈ U
    · have hn : ¬ (t₄ ≤ cyl (Sc i (x, y)) (fun _ => 1) (fun e => {e}) j f -
          pE (unif (Finset V) q) (cyl (Sc i (x, y)) (fun _ => 1) (fun e => {e}) j)) :=
        fun h => n4 ⟨((x, y), i, j), by simp [P4, hU2.1, hU2.2, hxy], h⟩
      push_neg at hn
      rw [pE_cyl_single hq] at hn
      rw [hcodS]
      have hd := hcod i x y hxy
      have : (∑ e ∈ Sc i (x, y), (fun _ => (1 : ℝ)) e) = codegree (A i) x y := by
        simp only [sum_const, nsmul_eq_mul, mul_one]; rfl
      rw [this] at hn
      have : (codegree (A i) x y : ℝ) * (1 / q) ≤ C / q := by
        rw [mul_one_div]; exact div_le_div_of_nonneg_right hd hqR.le
      linarith
    · rw [not_and_or] at hU2
      rw [codegree_eq_zero_of_not_mem _ H ((cls_subset A f i j).trans (hA i)) hU2]
      have : 0 ≤ C := le_trans (by positivity) (hcod i x y hxy)
      simp only [Nat.cast_zero]
      positivity
  · have hn : ¬ (γ * weight (W k) H ≤ cyl (A i) (W k) (fun e => {e}) j f -
        pE (unif (Finset V) q) (cyl (A i) (W k) (fun e => {e}) j)) :=
      fun h => n5 ⟨(k, i, j), by simp [P5, hk], h⟩
    push_neg at hn
    rw [pE_cyl_single hq] at hn
    rw [hwS]
    have hb := hWA k hk i
    have : (∑ e ∈ A i, W k e) * (1 / q) ≤ β * weight (W k) H / q := by
      rw [mul_one_div]; exact div_le_div_of_nonneg_right hb hqR.le
    linarith

/-- **Step 2.** A random edge partition is good with positive probability. -/
theorem edge_partition {p q : ℕ} (hq : 0 < q) (H : Finset (Finset V))
    (A : Fin p → Finset (Finset V)) (hA : ∀ i, A i ⊆ H) (D₁ C t₃ t₄ : ℝ) (ht₃ : 0 < t₃)
    (ht₄ : 0 < t₄) (hdeg : ∀ i x, (degree (A i) x : ℝ) ≤ D₁)
    (hcod : ∀ i x y, x ≠ y → (codegree (A i) x y : ℝ) ≤ C)
    {ι : Type*} (W : ι → Finset V → ℝ) (K : Finset ι) (η β γ : ℝ) (hη : 0 < η) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hW0 : ∀ k ∈ K, ∀ e ∈ H, 0 ≤ W k e) (hWpos : ∀ k ∈ K, 0 < weight (W k) H)
    (hWmax : ∀ k ∈ K, ∀ e ∈ H, W k e ≤ η * weight (W k) H)
    (hWA : ∀ k ∈ K, ∀ i, weight (W k) (A i) ≤ β * weight (W k) H)
    (hfail : ((H.biUnion id).card * p * q : ℝ) *
        Real.exp (-(t₃ ^ 2 / (2 * (1 * D₁ / q + 1 * t₃)))) +
      ((H.biUnion id).card ^ 2 * p * q : ℝ) *
        Real.exp (-(t₄ ^ 2 / (2 * (1 * C / q + 1 * t₄)))) +
      (K.card * p * q : ℝ) * Real.exp (-(γ ^ 2 / (2 * η * (β / q + γ)))) < 1) :
    ∃ f : Finset V → Fin q,
      (∀ i j x, (degree (cls A f i j) x : ℝ) ≤ D₁ / q + t₃) ∧
      (∀ i j x y, x ≠ y → (codegree (cls A f i j) x y : ℝ) ≤ C / q + t₄) ∧
      ∀ k ∈ K, ∀ i j, weight (W k) (cls A f i j) ≤ β * weight (W k) H / q +
        γ * weight (W k) H := by
  classical
  obtain ⟨f, h1, h2, h3, -⟩ := edge_partition_ext hq H A hA D₁ C t₃ t₄ ht₃ ht₄ hdeg hcod W K
    η β γ hη hβ hγ hW0 hWpos hWmax hWA (fun _ => False) 0 (by unfold pProb pE; simp) (by linarith)
  exact ⟨f, h1, h2, h3⟩

end Pseudorandom
