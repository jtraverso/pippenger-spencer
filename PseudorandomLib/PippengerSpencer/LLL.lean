/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.PippengerSpencer.ProdProb

/-! # The Lovász Local Lemma on finite product spaces

**Symmetric Lovász Local Lemma.** Let `(A k)_{k ∈ U}` be events in a finite product space,
where `A k` only depends on the coordinates in `S k`. If `P(A k) ≤ p` for all `k`, every `S k`
meets at most `d` of the other sets `S k'`, and `e p (d + 1) ≤ 1`, then with positive
probability none of the events occurs.

The proof is the standard one, with `x = 1/(d+2)`: by induction on `|T|`,
`P(A_k ∩ B_T) ≤ x P(B_T)` for `k ∉ T`, where `B_T` is the event that no `A_j`, `j ∈ T`, occurs.
-/

@[expose] public section

namespace Pseudorandom.PS

open Finset

section LLL

variable {ι α κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq κ]
  {P : ι → α → ℝ}

theorem pProb_and_add_and_not (hP : IsPMF P) (X Y : (ι → α) → Prop) :
    pProb P (fun ω => X ω ∧ Y ω) + pProb P (fun ω => ¬ X ω ∧ Y ω) = pProb P Y := by
  classical
  unfold pProb
  rw [← pE_add]
  congr 1; funext ω
  by_cases hx : X ω <;> by_cases hy : Y ω <;> simp [hx, hy]

theorem pProb_true (hP : IsPMF P) : pProb P (fun _ => True) = 1 := by
  classical
  unfold pProb
  simp only [ite_true]
  exact pE_const hP 1

/-- The numerical heart: `x (1 - x)^d ≥ 1 / (e (d+1))` for `x = 1/(d+2)`. -/
theorem lll_numeric (d : ℕ) {p : ℝ} (hpd : Real.exp 1 * p * (d + 1) ≤ 1) :
    p ≤ 1 / ((d : ℝ) + 2) * (1 - 1 / ((d : ℝ) + 2)) ^ d := by
  set x : ℝ := 1 / ((d : ℝ) + 2) with hx
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have h1x : 1 - x = ((d : ℝ) + 1) / (d + 2) := by rw [hx]; field_simp; ring
  have hpos : 0 < 1 - x := by rw [h1x]; positivity
  -- `1 - x ≥ exp(-1/(d+1))`
  have hge : Real.exp (-(1 / ((d : ℝ) + 1))) ≤ 1 - x := by
    have := Real.add_one_le_exp (1 / ((d : ℝ) + 1))
    have h2 : 1 / (1 - x) = 1 / ((d : ℝ) + 1) + 1 := by rw [h1x]; field_simp; ring
    rw [Real.exp_neg, ← one_div]
    rw [← h2] at this
    have h3 : 0 < Real.exp (1 / ((d : ℝ) + 1)) := Real.exp_pos _
    rw [div_le_iff₀ h3]
    rw [div_le_iff₀ hpos] at this
    linarith [mul_comm (1 - x) (Real.exp (1 / ((d : ℝ) + 1)))]
  have hpow : Real.exp (-1) ≤ (1 - x) ^ (d + 1) := by
    have := pow_le_pow_left₀ (Real.exp_pos _).le hge (d + 1)
    rw [← Real.exp_nat_mul] at this
    have e : ((d + 1 : ℕ) : ℝ) * -(1 / ((d : ℝ) + 1)) = -1 := by push_cast; field_simp
    rwa [e] at this
  have hkey : x * (1 - x) ^ d = (1 - x) ^ (d + 1) / ((d : ℝ) + 1) := by
    rw [pow_succ, h1x, hx]; field_simp
  rw [hkey, le_div_iff₀ hd1]
  have hp : p * ((d : ℝ) + 1) ≤ Real.exp (-1) := by
    rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos 1)]
    linarith
  linarith

/-- **The symmetric Lovász Local Lemma.** -/
theorem lovasz_local_lemma (hP : IsPMF P) (A : κ → (ι → α) → Prop) (S : κ → Finset ι)
    (hA : ∀ k, EvDepOn (A k) (S k)) (U : Finset κ) (p : ℝ) (d : ℕ)
    (hp : ∀ k ∈ U, pProb P (A k) ≤ p)
    (hd : ∀ k ∈ U, (U.filter (fun k' => k' ≠ k ∧ ¬ Disjoint (S k) (S k'))).card ≤ d)
    (hpd : Real.exp 1 * p * (d + 1) ≤ 1) :
    ∃ ω, ∀ k ∈ U, ¬ A k ω := by
  classical
  set x : ℝ := 1 / ((d : ℝ) + 2) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one (by positivity)]; linarith
  have hnum := lll_numeric d hpd
  set B : Finset κ → (ι → α) → Prop := fun T ω => ∀ j ∈ T, ¬ A j ω with hB
  have hBins : ∀ T j ω, B (insert j T) ω ↔ ¬ A j ω ∧ B T ω := by
    intro T j ω; simp [hB]
  have hstep : ∀ T j, pProb P (B (insert j T)) =
      pProb P (B T) - pProb P (fun ω => A j ω ∧ B T ω) := by
    intro T j
    have := pProb_and_add_and_not hP (A j) (B T)
    rw [pProb_congr (hBins T j)]
    linarith
  have hBnn : ∀ T, 0 ≤ pProb P (B T) := fun T => pProb_nonneg hP _
  -- the main induction
  have main : ∀ n : ℕ, ∀ T ⊆ U, T.card ≤ n →
      ∀ k ∈ U, k ∉ T → pProb P (fun ω => A k ω ∧ B T ω) ≤ x * pProb P (B T) := by
    intro n
    induction n with
    | zero =>
      intro T _ hT k hk _
      have hT0 : T = ∅ := card_eq_zero.mp (Nat.le_zero.mp hT)
      subst hT0
      have h1 : pProb P (fun ω => A k ω ∧ B ∅ ω) = pProb P (A k) :=
        pProb_congr fun ω => by simp [hB]
      have h2 : pProb P (B ∅) = 1 := by
        rw [pProb_congr (fun ω => show B ∅ ω ↔ True by simp [hB])]; exact pProb_true hP
      rw [h1, h2, mul_one]
      have : x * (1 - x) ^ d ≤ x := mul_le_of_le_one_right hx0 (pow_le_one₀ (by linarith)
        (by linarith))
      linarith [hp k hk]
    | succ n ih =>
      intro T hTU hT k hk hkT
      set T2 := T.filter (fun j => Disjoint (S k) (S j)) with hT2
      set T1 := T.filter (fun j => ¬ Disjoint (S k) (S j)) with hT1
      have hT1d : T1.card ≤ d := by
        refine le_trans (card_le_card ?_) (hd k hk)
        intro j hj
        rw [mem_filter] at hj ⊢
        exact ⟨hTU hj.1, fun h => hkT (h ▸ hj.1), hj.2⟩
      -- peeling off the neighbours
      have peel : ∀ R ⊆ T1, (1 - x) ^ R.card * pProb P (B T2) ≤ pProb P (B (T2 ∪ R)) := by
        intro R
        induction R using Finset.induction_on with
        | empty => intro _; simp
        | @insert j R hjR ihR =>
          intro hR
          have hRT1 : R ⊆ T1 := (subset_insert j R).trans hR
          have hjT1 : j ∈ T1 := hR (mem_insert_self j R)
          have hjT : j ∈ T := (mem_filter.mp hjT1).1
          have hjnot : j ∉ T2 ∪ R := by
            rw [mem_union, not_or]
            refine ⟨fun h => (mem_filter.mp hjT1).2 (mem_filter.mp h).2, hjR⟩
          have hsub : T2 ∪ R ⊆ T := union_subset (filter_subset _ _)
            (hRT1.trans (filter_subset _ _))
          have hcard : (T2 ∪ R).card ≤ n := by
            have : T2 ∪ R ⊂ T := ⟨hsub, fun h => hjnot (h hjT)⟩
            have := card_lt_card this
            omega
          have hIH := ih (T2 ∪ R) (hsub.trans hTU) hcard j (hTU hjT) hjnot
          have heq : T2 ∪ insert j R = insert j (T2 ∪ R) := by
            ext y; simp only [mem_union, mem_insert]; tauto
          rw [heq, hstep, card_insert_of_notMem hjR, pow_succ]
          have := ihR hRT1
          have h1x : 0 ≤ 1 - x := by linarith
          calc (1 - x) ^ R.card * (1 - x) * pProb P (B T2)
              = (1 - x) * ((1 - x) ^ R.card * pProb P (B T2)) := by ring
            _ ≤ (1 - x) * pProb P (B (T2 ∪ R)) := mul_le_mul_of_nonneg_left this h1x
            _ ≤ _ := by linarith
      have hT21 : T2 ∪ T1 = T := filter_union_filter_not_eq _ _
      have hBT := peel T1 (subset_refl _)
      rw [hT21] at hBT
      have hpow : (1 - x) ^ d * pProb P (B T2) ≤ (1 - x) ^ T1.card * pProb P (B T2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by linarith) (by linarith) hT1d)
          (hBnn _)
      -- independence of `A k` and `B T2`
      have hind : pProb P (fun ω => A k ω ∧ B T2 ω) = pProb P (A k) * pProb P (B T2) := by
        refine pProb_and_of_indep hP (S k) (A k) (B T2) (hA k) ?_
        intro ω ω' hωω'
        simp only [hB]
        refine forall₂_congr fun j hj => ?_
        rw [hA j ω ω' fun i hi => hωω' i fun hik =>
          Finset.disjoint_left.mp (mem_filter.mp hj).2 hik hi]
      have hmono : pProb P (fun ω => A k ω ∧ B T ω) ≤ pProb P (fun ω => A k ω ∧ B T2 ω) :=
        pProb_mono hP fun ω h => ⟨h.1, fun j hj => h.2 j (filter_subset _ _ hj)⟩
      calc pProb P (fun ω => A k ω ∧ B T ω) ≤ pProb P (A k) * pProb P (B T2) := hmono.trans hind.le
        _ ≤ (x * (1 - x) ^ d) * pProb P (B T2) :=
            mul_le_mul_of_nonneg_right ((hp k hk).trans hnum) (hBnn _)
        _ = x * ((1 - x) ^ d * pProb P (B T2)) := by ring
        _ ≤ x * pProb P (B T) := mul_le_mul_of_nonneg_left (hpow.trans hBT) hx0
  -- positivity of `P(B T)`
  have pos : ∀ T ⊆ U, 0 < pProb P (B T) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      rw [pProb_congr (fun ω => show B ∅ ω ↔ True by simp [hB]), pProb_true hP]
      exact one_pos
    | @insert j T hjT ihT =>
      intro hTU
      have hT : T ⊆ U := (subset_insert j T).trans hTU
      have h1 := ihT hT
      have h2 := main T.card T hT le_rfl j (hTU (mem_insert_self j T)) hjT
      rw [hstep]
      have hx1' : x < 1 := by rw [hx, div_lt_one (by positivity)]; linarith
      nlinarith
  have hU := pos U (subset_refl _)
  by_contra hcon
  push Not at hcon
  have : pProb P (B U) = 0 := by
    rw [pProb_congr (fun ω => show B U ω ↔ False from
      ⟨fun h => by obtain ⟨k, hk, hAk⟩ := hcon ω; exact h k hk hAk, False.elim⟩)]
    classical
    unfold pProb pE
    simp
  linarith

end LLL

end Pseudorandom.PS
