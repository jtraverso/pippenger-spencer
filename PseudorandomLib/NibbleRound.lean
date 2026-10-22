/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.Defs
public import PseudorandomLib.Bernstein
public import PseudorandomLib.Counting

/-! # One round of the (wasteful) Rödl nibble

The state is a set `A` of alive edges. In one round every alive edge `e` is *selected*
independently with probability `1 - e^{-a}`, and every vertex `v` gets an extra independent
*killing coin* with probability `1 - e^{-a (D - deg_A v)}` (this equalises the survival
probabilities of the vertices). A vertex *dies* if it lies in a selected edge or its killing
coin comes up. An edge is *accepted* if it is selected and no other selected alive edge meets
it. The accepted edges form a matching, and the new alive edges are the alive edges all of
whose vertices survive.

All coins are coordinates of one finite product space indexed by `Finset V ⊕ V`.
-/

@[expose] public section

namespace Pseudorandom.Nibble

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Coin indices: one coin per (potential) edge and one per vertex. -/
abbrev Coin (V : Type*) := Finset V ⊕ V

/-- The probability that a coin comes up `true`. -/
noncomputable def qTrue (A : Finset (Finset V)) (a D : ℝ) : Coin V → ℝ
  | Sum.inl e => if e ∈ A then 1 - Real.exp (-a) else 0
  | Sum.inr v => 1 - Real.exp (-(a * max 0 (D - degree A v)))

/-- The coin distributions of one round. -/
noncomputable def roundP (A : Finset (Finset V)) (a D : ℝ) : Coin V → Bool → ℝ :=
  fun i b => if b then qTrue A a D i else 1 - qTrue A a D i

omit [Fintype V] in
theorem qTrue_mem (A : Finset (Finset V)) {a : ℝ} (ha : 0 ≤ a) (D : ℝ) (i : Coin V) :
    0 ≤ qTrue A a D i ∧ qTrue A a D i ≤ 1 := by
  cases i with
  | inl e =>
    simp only [qTrue]
    split_ifs
    · constructor
      · have : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        linarith
      · linarith [Real.exp_pos (-a)]
    · norm_num
  | inr v =>
    simp only [qTrue]
    constructor
    · have : Real.exp (-(a * max 0 (D - degree A v))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [le_max_left 0 (D - degree A v)])
      linarith
    · linarith [Real.exp_pos (-(a * max 0 (D - degree A v)))]

omit [Fintype V] in
theorem roundP_isPMF (A : Finset (Finset V)) {a : ℝ} (ha : 0 ≤ a) (D : ℝ) :
    IsPMF (roundP A a D) := by
  refine ⟨fun i b => ?_, fun i => ?_⟩
  · have := qTrue_mem A ha D i
    cases b <;> simp [roundP] <;> linarith
  · simp [roundP]

/-! ## The deterministic part of a round -/

/-- A vertex dies if it lies in a selected alive edge or its killing coin comes up. -/
def Dead (A : Finset (Finset V)) (ω : Coin V → Bool) (v : V) : Prop :=
  (∃ f ∈ A, v ∈ f ∧ ω (Sum.inl f) = true) ∨ ω (Sum.inr v) = true

instance (A : Finset (Finset V)) (ω : Coin V → Bool) : DecidablePred (Dead A ω) :=
  fun v => inferInstanceAs (Decidable ((∃ f ∈ A, v ∈ f ∧ ω (Sum.inl f) = true) ∨
    ω (Sum.inr v) = true))

/-- The new alive edges: alive edges all of whose vertices survive. -/
def alive (A : Finset (Finset V)) (ω : Coin V → Bool) : Finset (Finset V) :=
  A.filter (fun e => ∀ v ∈ e, ¬ Dead A ω v)

/-- The accepted edges: selected alive edges meeting no other selected alive edge. -/
def acc (A : Finset (Finset V)) (ω : Coin V → Bool) : Finset (Finset V) :=
  A.filter (fun e => ω (Sum.inl e) = true ∧
    ∀ f ∈ A, f ≠ e → ¬ Disjoint f e → ω (Sum.inl f) = false)

/-- The number of alive edges at `v` whose other vertices survive. -/
def degP (A : Finset (Finset V)) (ω : Coin V → Bool) (v : V) : ℕ :=
  (A.filter (fun e => v ∈ e ∧ ∀ u ∈ e, u ≠ v → ¬ Dead A ω u)).card

theorem alive_subset (A : Finset (Finset V)) (ω : Coin V → Bool) : alive A ω ⊆ A :=
  filter_subset _ _

theorem acc_subset (A : Finset (Finset V)) (ω : Coin V → Bool) : acc A ω ⊆ A :=
  filter_subset _ _

theorem acc_isMatching (A : Finset (Finset V)) (ω : Coin V → Bool) :
    IsMatching (acc A ω) := by
  intro e he f hf hef
  simp only [acc, mem_filter] at he hf
  by_contra hd
  have := he.2.2 f hf.1 (Ne.symm hef) (fun h => hd h.symm)
  rw [hf.2.1] at this
  exact Bool.noConfusion this

theorem disjoint_alive_acc (A : Finset (Finset V)) (ω : Coin V → Bool) :
    ∀ f ∈ alive A ω, ∀ g ∈ acc A ω, Disjoint f g := by
  intro f hf g hg
  simp only [alive, acc, mem_filter] at hf hg
  rw [Finset.disjoint_left]
  intro v hvf hvg
  exact hf.2 v hvf (Or.inl ⟨g, hg.1, hvg, hg.2.1⟩)

theorem degree_alive_le_degP (A : Finset (Finset V)) (ω : Coin V → Bool) (v : V) :
    degree (alive A ω) v ≤ degP A ω v := by
  unfold degree degP alive
  apply card_le_card
  intro e he
  simp only [mem_filter] at he ⊢
  exact ⟨he.1.1, he.2, fun u hu _ => he.1.2 u hu⟩

/-! ## Exact probabilities -/

section Prob

variable (A : Finset (Finset V)) {a : ℝ} (D : ℝ)

omit [Fintype V] in
theorem roundP_inl_true {f : Finset V} (hf : f ∈ A) :
    roundP A a D (Sum.inl f) true = 1 - Real.exp (-a) := by
  simp [roundP, qTrue, hf]

omit [Fintype V] in
theorem roundP_inl_false {f : Finset V} (hf : f ∈ A) :
    roundP A a D (Sum.inl f) false = Real.exp (-a) := by
  simp [roundP, qTrue, hf]

omit [Fintype V] in
theorem roundP_inr_false (v : V) :
    roundP A a D (Sum.inr v) false = Real.exp (-(a * max 0 (D - degree A v))) := by
  simp [roundP, qTrue]

omit [Fintype V] in
theorem notDead_iff (T : Finset V) (ω : Coin V → Bool) :
    (∀ u ∈ T, ¬ Dead A ω u) ↔ ∀ i ∈ (meet A T).disjSum T, ω i = (fun _ => false) i := by
  constructor
  · intro h i hi
    cases i with
    | inl f =>
      rw [inl_mem_disjSum, mem_meet] at hi
      obtain ⟨hfA, u, huT, huf⟩ := hi
      by_contra hc
      exact h u huT (Or.inl ⟨f, hfA, huf, by simpa using hc⟩)
    | inr u =>
      rw [inr_mem_disjSum] at hi
      by_contra hc
      exact h u hi (Or.inr (by simpa using hc))
  · intro h u huT hd
    rcases hd with ⟨f, hfA, huf, hω⟩ | hω
    · have := h (Sum.inl f) (inl_mem_disjSum.mpr (mem_meet.mpr ⟨hfA, u, huT, huf⟩))
      rw [hω] at this; exact Bool.noConfusion this
    · have := h (Sum.inr u) (inr_mem_disjSum.mpr huT)
      rw [hω] at this; exact Bool.noConfusion this

/-- The exact probability that every vertex of `T` survives. -/
theorem prob_notDead (ha : 0 ≤ a) (T : Finset V) :
    pProb (roundP A a D) (fun ω => ∀ u ∈ T, ¬ Dead A ω u) =
      Real.exp (-a) ^ (meet A T).card *
        ∏ u ∈ T, Real.exp (-(a * max 0 (D - degree A u))) := by
  rw [pProb_congr (notDead_iff A T), pProb_cylinder (roundP_isPMF A ha D), prod_disjSum]
  congr 1
  · rw [prod_congr rfl (fun f hf => roundP_inl_false A D (mem_meet.mp hf).1), prod_const]
  · exact prod_congr rfl (fun u _ => roundP_inr_false A D u)

/-- The survival probability as a single exponential. -/
theorem prob_notDead_eq_exp (ha : 0 ≤ a) (T : Finset V) (hdeg : ∀ u ∈ T, (degree A u : ℝ) ≤ D) :
    pProb (roundP A a D) (fun ω => ∀ u ∈ T, ¬ Dead A ω u) =
      Real.exp (-(a * ((meet A T).card + ∑ u ∈ T, (D - degree A u)))) := by
  rw [prob_notDead A D ha, ← Real.exp_nat_mul, ← Real.exp_sum, ← Real.exp_add]
  congr 1
  have : ∀ u ∈ T, max 0 (D - degree A u) = D - degree A u := fun u hu =>
    max_eq_right (by linarith [hdeg u hu])
  rw [sum_congr rfl (fun u hu => by rw [this u hu])]
  rw [mul_add, mul_sum, sum_neg_distrib]
  ring

/-- Lower bound for the survival probability: `≥ e^{-a |T| D}`. -/
theorem prob_notDead_ge (ha : 0 ≤ a) (T : Finset V) (hdeg : ∀ u ∈ T, (degree A u : ℝ) ≤ D) :
    Real.exp (-(a * (T.card * D))) ≤ pProb (roundP A a D) (fun ω => ∀ u ∈ T, ¬ Dead A ω u) := by
  rw [prob_notDead_eq_exp A D ha T hdeg]
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply mul_le_mul_of_nonneg_left _ ha
  have h1 : ((meet A T).card : ℝ) ≤ ∑ u ∈ T, (degree A u : ℝ) := by
    exact_mod_cast card_meet_le A T
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  linarith

/-- Upper bound for the survival probability, using codegrees: `≤ e^{-a (|T| D - |T|² K)}`. -/
theorem prob_notDead_le (ha : 0 ≤ a) (T : Finset V) (hdeg : ∀ u ∈ T, (degree A u : ℝ) ≤ D)
    (K : ℝ) (hK : 0 ≤ K) (hcod : ∀ u ∈ T, ∀ w ∈ T, u ≠ w → (codegree A u w : ℝ) ≤ K) :
    pProb (roundP A a D) (fun ω => ∀ u ∈ T, ¬ Dead A ω u) ≤
      Real.exp (-(a * (T.card * D - T.card ^ 2 * K))) := by
  rw [prob_notDead_eq_exp A D ha T hdeg]
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply mul_le_mul_of_nonneg_left _ ha
  have h1 : (∑ u ∈ T, (degree A u : ℝ)) ≤ (meet A T).card +
      ∑ u ∈ T, ∑ w ∈ T.erase u, (codegree A u w : ℝ) := by
    exact_mod_cast sum_degree_le A T
  have h2 : ∑ u ∈ T, ∑ w ∈ T.erase u, (codegree A u w : ℝ) ≤ T.card ^ 2 * K := by
    calc ∑ u ∈ T, ∑ w ∈ T.erase u, (codegree A u w : ℝ)
        ≤ ∑ u ∈ T, ∑ w ∈ T.erase u, K := sum_le_sum fun u hu => sum_le_sum fun w hw =>
          hcod u hu w (mem_of_mem_erase hw) (ne_of_mem_erase hw).symm
      _ = T.card * ((T.card - 1 : ℕ) : ℝ) * K := by
          rw [sum_congr rfl (fun u hu => by rw [sum_const, card_erase_of_mem hu]), sum_const]
          simp only [nsmul_eq_mul]; ring
      _ ≤ T.card ^ 2 * K := by
          have : ((T.card - 1 : ℕ) : ℝ) ≤ T.card := by exact_mod_cast Nat.sub_le _ _
          rw [sq]; gcongr
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  linarith

theorem alive_iff (ω : Coin V → Bool) {e : Finset V} (he : e ∈ A) :
    e ∈ alive A ω ↔ ∀ u ∈ e, ¬ Dead A ω u := by
  simp [alive, he]

/-- Lower bound on the probability that an alive edge stays alive. -/
theorem prob_alive_ge (ha : 0 ≤ a) {e : Finset V} (he : e ∈ A) (r : ℕ) (her : e.card = r)
    (hdeg : ∀ u ∈ e, (degree A u : ℝ) ≤ D) :
    Real.exp (-(a * (r * D))) ≤ pProb (roundP A a D) (fun ω => e ∈ alive A ω) := by
  rw [pProb_congr (fun ω => alive_iff A ω he), ← her]
  exact prob_notDead_ge A D ha e hdeg

theorem acc_iff (ω : Coin V → Bool) {e : Finset V} (he : e ∈ A) (hne : e.Nonempty) :
    e ∈ acc A ω ↔ ∀ i ∈ (meet A e).disjSum (∅ : Finset V),
      ω i = (fun j => decide (j = Sum.inl e)) i := by
  have hem : e ∈ meet A e := mem_meet.mpr ⟨he, hne.choose, hne.choose_spec, hne.choose_spec⟩
  simp only [acc, mem_filter, he, true_and]
  constructor
  · rintro ⟨h1, h2⟩ i hi
    cases i with
    | inl f =>
      rw [inl_mem_disjSum] at hi
      by_cases hfe : f = e
      · subst hfe; simpa using h1
      · have hfA := (mem_meet.mp hi).1
        have hnd : ¬ Disjoint f e := by
          obtain ⟨_, u, hu1, hu2⟩ := mem_meet.mp hi
          rw [Finset.not_disjoint_iff]; exact ⟨u, hu2, hu1⟩
        simp [h2 f hfA hfe hnd, hfe]
    | inr u => simp at hi
  · intro h
    refine ⟨by simpa using h (Sum.inl e) (inl_mem_disjSum.mpr hem), fun f hfA hfe hnd => ?_⟩
    have hfm : f ∈ meet A e := by
      obtain ⟨u, hu1, hu2⟩ := Finset.not_disjoint_iff.mp hnd
      exact mem_meet.mpr ⟨hfA, u, hu2, hu1⟩
    simpa [hfe] using h (Sum.inl f) (inl_mem_disjSum.mpr hfm)

/-- The exact acceptance probability. -/
theorem prob_acc (ha : 0 ≤ a) {e : Finset V} (he : e ∈ A) (hne : e.Nonempty) :
    pProb (roundP A a D) (fun ω => e ∈ acc A ω) =
      (1 - Real.exp (-a)) * Real.exp (-a) ^ ((meet A e).card - 1) := by
  have hem : e ∈ meet A e := mem_meet.mpr ⟨he, hne.choose, hne.choose_spec, hne.choose_spec⟩
  rw [pProb_congr (fun ω => acc_iff A ω he hne), pProb_cylinder (roundP_isPMF A ha D),
    prod_disjSum]
  simp only [prod_empty, mul_one]
  rw [← mul_prod_erase _ _ hem]
  simp only [decide_true]
  rw [roundP_inl_true A D he]
  congr 1
  rw [prod_congr rfl (g := fun _ => Real.exp (-a)) (fun f hf => by
      have h1 : decide (Sum.inl f = (Sum.inl e : Coin V)) = false := by
        simpa using ne_of_mem_erase hf
      rw [h1]; exact roundP_inl_false A D (mem_meet.mp (mem_of_mem_erase hf)).1),
    prod_const, card_erase_of_mem hem]

/-- Lower bound on the acceptance probability: `≥ (1 - e^{-a}) e^{-a r D}`. -/
theorem prob_acc_ge (ha : 0 ≤ a) {e : Finset V} (he : e ∈ A) (hne : e.Nonempty) (r : ℕ)
    (her : e.card = r) (hdeg : ∀ u ∈ e, (degree A u : ℝ) ≤ D) :
    (1 - Real.exp (-a)) * Real.exp (-(a * (r * D))) ≤
      pProb (roundP A a D) (fun ω => e ∈ acc A ω) := by
  rw [prob_acc A D ha he hne]
  apply mul_le_mul_of_nonneg_left _ (by linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)])
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h1 : (((meet A e).card - 1 : ℕ) : ℝ) ≤ r * D := by
    have h2 : (((meet A e).card - 1 : ℕ) : ℝ) ≤ (meet A e).card := by
      exact_mod_cast Nat.sub_le _ _
    have h3 : ((meet A e).card : ℝ) ≤ ∑ u ∈ e, (degree A u : ℝ) := by
      exact_mod_cast card_meet_le A e
    have h4 : ∑ u ∈ e, (degree A u : ℝ) ≤ ∑ u ∈ e, D := sum_le_sum hdeg
    rw [sum_const, her, nsmul_eq_mul] at h4
    linarith
  nlinarith

end Prob

end Pseudorandom.Nibble
