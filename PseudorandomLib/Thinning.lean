/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.FiniteProb
public import PseudorandomLib.Defs

/-! # Thinning a random set of edges to exact marginals

If a random set of edges `M` contains every edge `e ∈ A` with probability at least `x`, then
deleting every edge `e` independently with a suitable probability produces a random subset
`N ⊆ M ∩ A` that contains every edge of `A` with probability exactly `x`.
-/

@[expose] public section

namespace Pseudorandom

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The marginal probability of an edge. -/
noncomputable def marg (μ : Finset (Finset V) → ℝ) (e : Finset V) : ℝ :=
  ∑ M, μ M * (if e ∈ M then 1 else 0)

/-- **Thinning.** -/
theorem thinning (A : Finset (Finset V)) (μ : Finset (Finset V) → ℝ) (hμ0 : ∀ M, 0 ≤ μ M)
    (hμ1 : ∑ M, μ M = 1) (x : ℝ) (hx0 : 0 ≤ x) (hmarg : ∀ e ∈ A, x ≤ marg μ e) :
    ∃ ν : Finset (Finset V) → ℝ, (∀ N, 0 ≤ ν N) ∧ ∑ N, ν N = 1 ∧
      (∀ N, ν N ≠ 0 → ∃ M, μ M ≠ 0 ∧ N ⊆ M ∧ N ⊆ A) ∧ ∀ e ∈ A, marg ν e = x := by
  classical
  -- keep probabilities
  set s : Finset V → ℝ := fun e => if e ∈ A then x / marg μ e else 0 with hs
  have hs0 : ∀ e, 0 ≤ s e := by
    intro e
    simp only [hs]
    split_ifs with he
    · exact div_nonneg hx0 (hx0.trans (hmarg e he))
    · exact le_rfl
  have hs1 : ∀ e, s e ≤ 1 := by
    intro e
    simp only [hs]
    split_ifs with he
    · rcases (hx0.trans (hmarg e he)).lt_or_eq with hpos | hzero
      · rw [div_le_one hpos]; exact hmarg e he
      · rw [← hzero, div_zero]; norm_num
    · norm_num
  set Pc : Finset V → Bool → ℝ := fun e b => if b then s e else 1 - s e with hPc
  have hP : IsPMF Pc := by
    refine ⟨fun e b => ?_, fun e => ?_⟩
    · simp only [hPc]; split_ifs
      · exact hs0 e
      · linarith [hs1 e]
    · simp [hPc]
  set thin : Finset (Finset V) → (Finset V → Bool) → Finset (Finset V) :=
    fun M c => M.filter (fun e => e ∈ A ∧ c e = true) with hthin
  set ν : Finset (Finset V) → ℝ :=
    fun N => ∑ M, μ M * pE Pc (fun c => if thin M c = N then 1 else 0) with hν
  refine ⟨ν, fun N => ?_, ?_, fun N hN => ?_, fun e he => ?_⟩
  · exact sum_nonneg fun M _ => mul_nonneg (hμ0 M)
      (pE_nonneg hP fun c => by split_ifs <;> norm_num)
  · simp only [hν]
    rw [sum_comm]
    conv_rhs => rw [← hμ1]
    refine sum_congr rfl fun M _ => ?_
    rw [← mul_sum, ← pE_sum]
    have : (fun c => ∑ N, (if thin M c = N then (1 : ℝ) else 0)) = fun _ => 1 := by
      funext c; simp
    rw [this, pE_const hP, mul_one]
  · obtain ⟨M, _, hM⟩ := exists_ne_zero_of_sum_ne_zero hN
    have hμM : μ M ≠ 0 := left_ne_zero_of_mul hM
    have hE := right_ne_zero_of_mul hM
    obtain ⟨c, _, hc⟩ := exists_ne_zero_of_sum_ne_zero hE
    have hc' := right_ne_zero_of_mul hc
    have hNc : thin M c = N := by by_contra h; exact hc' (if_neg h)
    refine ⟨M, hμM, ?_, ?_⟩
    · rw [← hNc]; exact filter_subset _ _
    · rw [← hNc]; intro f hf; exact (mem_filter.mp hf).2.1
  · unfold marg
    simp only [hν]
    simp_rw [sum_mul]
    rw [sum_comm]
    have key : ∀ M, ∑ N, μ M * pE Pc (fun c => if thin M c = N then (1 : ℝ) else 0) *
        (if e ∈ N then 1 else 0) = μ M * ((if e ∈ M then 1 else 0) * s e) := by
      intro M
      simp_rw [mul_assoc]
      rw [← mul_sum]
      congr 1
      have h1 : ∀ N, pE Pc (fun c => if thin M c = N then (1 : ℝ) else 0) *
          (if e ∈ N then 1 else 0) =
          pE Pc (fun c => (if thin M c = N then (1 : ℝ) else 0) * (if e ∈ N then 1 else 0)) := by
        intro N; rw [mul_comm, ← pE_const_mul]; congr 1; funext c; ring
      simp_rw [h1]
      rw [← pE_sum]
      have h2 : (fun c => ∑ N, (if thin M c = N then (1 : ℝ) else 0) *
          (if e ∈ N then 1 else 0)) = fun c => (if e ∈ M then 1 else 0) *
            (if c e = true then 1 else 0) := by
        funext c
        rw [sum_eq_single (thin M c)]
        · simp only [if_true, one_mul, hthin, mem_filter]
          by_cases heM : e ∈ M <;> by_cases hce : c e = true <;> simp [heM, hce, he]
        · intro N _ hN; rw [if_neg (Ne.symm hN), zero_mul]
        · intro h; exact absurd (mem_univ _) h
      rw [h2, pE_const_mul, pE_coord hP e (fun b => if b = true then (1 : ℝ) else 0)]
      simp [hPc]
    simp_rw [key]
    have : ∀ M, μ M * ((if e ∈ M then (1 : ℝ) else 0) * s e) =
        μ M * (if e ∈ M then 1 else 0) * s e := fun M => by ring
    simp_rw [this]
    rw [← sum_mul]
    change marg μ e * s e = x
    simp only [hs, if_pos he]
    rcases (hx0.trans (hmarg e he)).lt_or_eq with hpos | hzero
    · field_simp
    · have hx : x = 0 := le_antisymm (hzero ▸ hmarg e he) hx0
      rw [← hzero, hx]; simp

end Pseudorandom
