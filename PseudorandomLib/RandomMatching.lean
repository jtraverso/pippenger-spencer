/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.Thinning
public import PseudorandomLib.Bernstein

/-! # Step 3: combining random matchings of the parts

We are given vertex-disjoint parts `i ∈ [p]`, each split into `q` edge classes `A i j`, and
for each class a random matching `N ⊆ A i j` that contains every edge of `A i j` with
probability exactly `x`. For every part independently we pick a uniformly random class `j`
and a random matching of that class. The union `M` is a matching, every edge of every class
is in `M` with probability `x / q`, and the weight of `M` is concentrated by the
bounded-differences inequality (one coordinate per part).
-/

@[expose] public section

namespace Pseudorandom

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- `ω(N ∩ A)` as a sum over `A`. -/
theorem weight_inter_eq (w : Finset V → ℝ) (N A : Finset (Finset V)) :
    weight w (N ∩ A) = ∑ e ∈ A, w e * (if e ∈ N then 1 else 0) := by
  classical
  unfold weight
  rw [inter_comm, ← filter_mem_eq_inter, sum_filter]
  refine sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

/-- Expected weight of `N ∩ A` for a random `N` with exact marginals on `A`. -/
theorem sum_weight_inter (w : Finset V → ℝ) (A : Finset (Finset V))
    (ν : Finset (Finset V) → ℝ) (x : ℝ) (hmarg : ∀ e ∈ A, marg ν e = x) :
    ∑ N, ν N * weight w (N ∩ A) = x * weight w A := by
  simp_rw [weight_inter_eq, mul_sum]
  rw [sum_comm, weight, mul_sum]
  refine sum_congr rfl fun e he => ?_
  rw [← hmarg e he, marg, sum_mul]
  exact sum_congr rfl fun N _ => by ring

/-- **Step 3.** -/
theorem random_matching {p q : ℕ} (hq : 0 < q) (H : Finset (Finset V))
    (hne : ∀ e ∈ H, e.Nonempty)
    (A : Fin p → Fin q → Finset (Finset V)) (hAH : ∀ i j, A i j ⊆ H)
    (hdisj : ∀ i i', i ≠ i' → ∀ j j', ∀ e ∈ A i j, ∀ f ∈ A i' j', Disjoint e f)
    (ν : Fin p → Fin q → Finset (Finset V) → ℝ) (hν0 : ∀ i j N, 0 ≤ ν i j N)
    (hν1 : ∀ i j, ∑ N, ν i j N = 1)
    (hνsupp : ∀ i j N, ν i j N ≠ 0 → IsMatching N ∧ N ⊆ A i j)
    (x : ℝ) (hνmarg : ∀ i j, ∀ e ∈ A i j, marg (ν i j) e = x)
    {ι : Type*} (W : ι → Finset V → ℝ) (K : Finset ι) (hW0 : ∀ k ∈ K, ∀ e ∈ H, 0 ≤ W k e)
    (c t : ι → ℝ) (hc : ∀ k ∈ K, 0 < c k) (ht : ∀ k ∈ K, 0 < t k)
    (hcb : ∀ k ∈ K, ∀ i j, weight (W k) (A i j) ≤ c k)
    (hfail : ∑ k ∈ K, 2 * Real.exp (-(t k ^ 2 / (2 * (p * c k ^ 2 + c k * t k)))) < 1) :
    ∃ M ⊆ H, IsMatching M ∧ ∀ k ∈ K,
      |weight (W k) M - x / q * ∑ i, ∑ j, weight (W k) (A i j)| < t k := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  -- the product space
  set P : Fin p → Fin q × Finset (Finset V) → ℝ := fun i a => ν i a.1 a.2 / q with hPdef
  have hP : IsPMF P := by
    refine ⟨fun i a => div_nonneg (hν0 _ _ _) hqR.le, fun i => ?_⟩
    rw [Fintype.sum_prod_type]
    simp only [hPdef]
    simp_rw [← sum_div, hν1]
    simp [hqR.ne']
  set g : ι → Fin p → Fin q × Finset (Finset V) → ℝ :=
    fun k i a => weight (W k) (a.2 ∩ A i a.1) with hgdef
  set F : ι → (Fin p → Fin q × Finset (Finset V)) → ℝ := fun k ω => ∑ i, g k i (ω i)
    with hFdef
  set Mω : (Fin p → Fin q × Finset (Finset V)) → Finset (Finset V) :=
    fun ω => univ.biUnion (fun i => (ω i).2 ∩ A i (ω i).1) with hMdef
  -- basic facts
  have hg0 : ∀ k ∈ K, ∀ i a, 0 ≤ g k i a := fun k hk i a =>
    sum_nonneg fun e he => hW0 k hk e (hAH _ _ (mem_inter.mp he).2)
  have hgc : ∀ k ∈ K, ∀ i a, g k i a ≤ c k := by
    intro k hk i a
    refine le_trans ?_ (hcb k hk i a.1)
    exact sum_le_sum_of_subset_of_nonneg inter_subset_right
      fun e he _ => hW0 k hk e (hAH _ _ he)
  have hEF : ∀ k, pE P (F k) = x / q * ∑ i, ∑ j, weight (W k) (A i j) := by
    intro k
    simp only [hFdef]
    rw [pE_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [pE_coord hP i (g k i), Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [hPdef, hgdef]
    have := sum_weight_inter (W k) (A i j) (ν i j) x (hνmarg i j)
    have e2 : ∑ N, ν i j N / q * weight (W k) (N ∩ A i j) =
        (∑ N, ν i j N * weight (W k) (N ∩ A i j)) / q := by
      rw [sum_div]; exact sum_congr rfl fun N _ => by ring
    rw [e2, this]; ring
  have hgap : ∀ k ∈ K, CoordGap (F k) (fun _ => c k) := by
    intro k hk i ω a b
    simp only [hFdef]
    rw [← sum_sub_distrib, sum_eq_single i]
    · simp only [Function.update_self]
      have h1 := hg0 k hk i a; have h2 := hg0 k hk i b
      have h3 := hgc k hk i a; have h4 := hgc k hk i b
      rw [abs_le]; constructor <;> linarith
    · intro i' _ hi'
      simp [Function.update_of_ne hi']
    · intro h; exact absurd (mem_univ i) h
  have hrare : ∀ k, CoordRare (F k) (fun _ => (univ : Finset (Fin q × Finset (Finset V)))) :=
    fun k i ω a b ha _ => absurd (mem_univ a) ha
  have hq1 : ∀ i, ∑ a ∈ (univ : Finset (Fin q × Finset (Finset V))), P i a ≤ 1 :=
    fun i => le_of_eq (hP.2 i)
  have htail : ∀ k ∈ K, pProb P (fun ω => t k ≤ F k ω - pE P (F k)) +
      pProb P (fun ω => t k ≤ pE P (F k) - F k ω) ≤
        2 * Real.exp (-(t k ^ 2 / (2 * (p * c k ^ 2 + c k * t k)))) := by
    intro k hk
    have hsum : (∑ _i : Fin p, (1 : ℝ) * c k ^ 2) = p * c k ^ 2 := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, one_mul]
    have h1 := pE_upper_tail P hP (F k) (fun _ => c k) (fun _ => 1) _ (c k) (hc k hk)
      (fun _ => ⟨(hc k hk).le, le_rfl⟩) (hgap k hk) (hrare k) hq1 (t k) (ht k hk)
    have h2 := pE_lower_tail P hP (F k) (fun _ => c k) (fun _ => 1) _ (c k) (hc k hk)
      (fun _ => ⟨(hc k hk).le, le_rfl⟩) (hgap k hk) (hrare k) hq1 (t k) (ht k hk)
    rw [hsum] at h1 h2
    linarith
  set bad : (Fin p → Fin q × Finset (Finset V)) → Prop := fun ω =>
    ∃ k ∈ K, t k ≤ F k ω - pE P (F k) ∨ t k ≤ pE P (F k) - F k ω
  have hbad : pProb P bad < 1 := by
    refine lt_of_le_of_lt ((pProb_exists_le hP K _).trans ?_) hfail
    exact sum_le_sum fun k hk => (pProb_or_le hP _ _).trans (htail k hk)
  obtain ⟨ω, hω, hgood⟩ := exists_of_pProb_lt_one hP hbad
  -- the outcome has positive weight in every coordinate
  have hpos : ∀ i, ν i (ω i).1 (ω i).2 ≠ 0 := by
    intro i h
    have : pw P ω = 0 := by
      unfold pw
      exact prod_eq_zero (mem_univ i) (by simp [hPdef, h])
    linarith
  have hsupp : ∀ i, IsMatching (ω i).2 ∧ (ω i).2 ⊆ A i (ω i).1 := fun i =>
    hνsupp i _ _ (hpos i)
  have hpd : ((univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint
      (fun i => (ω i).2 ∩ A i (ω i).1) := by
    intro i _ i' _ hii'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    have h1 := (mem_inter.mp he).2
    have h2 := (mem_inter.mp he').2
    have := hdisj i i' hii' _ _ e h1 e h2
    rw [disjoint_self_iff_empty] at this
    exact (hne e (hAH _ _ h1)).ne_empty this
  have hweight : ∀ k, weight (W k) (Mω ω) = F k ω := by
    intro k
    simp only [hMdef, hFdef, hgdef, weight]
    rw [sum_biUnion hpd]
  refine ⟨Mω ω, ?_, ?_, fun k hk => ?_⟩
  · intro e he
    simp only [hMdef, mem_biUnion] at he
    obtain ⟨i, _, hi⟩ := he
    exact hAH _ _ (mem_inter.mp hi).2
  · intro e he f hf hef
    simp only [hMdef, mem_biUnion] at he hf
    obtain ⟨i, _, hi⟩ := he
    obtain ⟨i', _, hi'⟩ := hf
    by_cases hii : i = i'
    · subst hii
      exact (hsupp i).1 e (mem_inter.mp hi).1 f (mem_inter.mp hi').1 hef
    · exact hdisj i i' hii _ _ e (mem_inter.mp hi).2 f (mem_inter.mp hi').2
  · rw [hweight, ← hEF k, abs_sub_lt_iff]
    have h1 : ¬ (t k ≤ F k ω - pE P (F k)) := fun h => hgood ⟨k, hk, Or.inl h⟩
    have h2 : ¬ (t k ≤ pE P (F k) - F k ω) := fun h => hgood ⟨k, hk, Or.inr h⟩
    push_neg at h1 h2
    exact ⟨h1, h2⟩

end Pseudorandom
