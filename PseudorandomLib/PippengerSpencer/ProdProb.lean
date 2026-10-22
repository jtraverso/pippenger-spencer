/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.Freedman

/-! # More on finite product probability spaces

* independence of functions of disjoint sets of coordinates;
* pushing a product measure forward along coordinatewise maps;
* grouping the coordinates of a product space into blocks (currying);
* integrating out one coordinate.
-/

@[expose] public section

namespace Pseudorandom.PS

open Finset

section Indep

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] {P : ι → α → ℝ}

/-- The outcome equal to `ω` on `S` and to `ω'` off `S`. -/
def merge (S : Finset ι) (ω ω' : ι → α) : ι → α := fun i => if i ∈ S then ω i else ω' i

theorem merge_merge (S : Finset ι) (ω ω' : ι → α) :
    merge S (merge S ω ω') (merge S ω' ω) = ω := by
  funext i; unfold merge; split_ifs <;> rfl

theorem pw_merge_mul (S : Finset ι) (ω ω' : ι → α) :
    pw P (merge S ω ω') * pw P (merge S ω' ω) = pw P ω * pw P ω' := by
  unfold pw
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  unfold merge
  split_ifs <;> ring

/-- `f` only depends on the coordinates in `S`. -/
def DepOn (f : (ι → α) → ℝ) (S : Finset ι) : Prop :=
  ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → f ω = f ω'

/-- An event only depends on the coordinates in `S`. -/
def EvDepOn (A : (ι → α) → Prop) (S : Finset ι) : Prop :=
  ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → (A ω ↔ A ω')

omit [Fintype ι] [Fintype α] in
theorem EvDepOn.mono {A : (ι → α) → Prop} {S T : Finset ι} (h : EvDepOn A S) (hST : S ⊆ T) :
    EvDepOn A T := fun ω ω' hω => h ω ω' fun i hi => hω i (hST hi)

/-- **Independence.** Functions of disjoint sets of coordinates are uncorrelated. -/
theorem pE_mul_of_indep (hP : IsPMF P) (S : Finset ι) (f g : (ι → α) → ℝ)
    (hf : ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → f ω = f ω')
    (hg : ∀ ω ω', (∀ i ∉ S, ω i = ω' i) → g ω = g ω') :
    pE P (fun ω => f ω * g ω) = pE P f * pE P g := by
  unfold pE
  rw [sum_mul_sum, ← Fintype.sum_prod_type']
  set σ : (ι → α) × (ι → α) → (ι → α) × (ι → α) := fun p => (merge S p.1 p.2, merge S p.2 p.1)
  have hσ : Function.Involutive σ := fun p => by
    simp only [σ, merge_merge]
  rw [← Equiv.sum_comp hσ.toPerm]
  have key : ∀ p : (ι → α) × (ι → α),
      pw P (σ p).1 * f (σ p).1 * (pw P (σ p).2 * g (σ p).2) =
        pw P p.1 * f p.1 * g p.1 * pw P p.2 := by
    intro p
    have h1 : f (σ p).1 = f p.1 := hf _ _ fun i hi => by simp [σ, merge, hi]
    have h2 : g (σ p).2 = g p.1 := hg _ _ fun i hi => by simp [σ, merge, hi]
    have h3 := pw_merge_mul (P := P) S p.1 p.2
    simp only [σ] at h1 h2 ⊢
    rw [h1, h2]
    calc pw P (merge S p.1 p.2) * f p.1 * (pw P (merge S p.2 p.1) * g p.1)
        = (pw P (merge S p.1 p.2) * pw P (merge S p.2 p.1)) * (f p.1 * g p.1) := by ring
      _ = _ := by rw [h3]; ring
  simp only [Function.Involutive.coe_toPerm]
  rw [Fintype.sum_congr _ _ key, Fintype.sum_prod_type]
  refine sum_congr rfl fun ω _ => ?_
  simp_rw [show ∀ y : ι → α, pw P (ω, y).1 * f (ω, y).1 * g (ω, y).1 * pw P (ω, y).2 =
    (pw P ω * (f ω * g ω)) * pw P y from fun y => by ring]
  rw [← mul_sum, sum_pw hP, mul_one]

/-- **Independence of events** depending on disjoint sets of coordinates. -/
theorem pProb_and_of_indep (hP : IsPMF P) (S : Finset ι) (A B : (ι → α) → Prop)
    (hA : EvDepOn A S) (hB : ∀ ω ω', (∀ i ∉ S, ω i = ω' i) → (B ω ↔ B ω')) :
    pProb P (fun ω => A ω ∧ B ω) = pProb P A * pProb P B := by
  classical
  have h := pE_mul_of_indep hP S (fun ω => if A ω then (1 : ℝ) else 0)
    (fun ω => if B ω then (1 : ℝ) else 0)
    (fun ω ω' h => by simp only [hA ω ω' h])
    (fun ω ω' h => by simp only [hB ω ω' h])
  rw [pProb_eq_pE _ (fun ω => (if A ω then (1 : ℝ) else 0) * (if B ω then (1 : ℝ) else 0))
    (fun ω h => by simp [h.1, h.2]) (fun ω h => by
      by_cases ha : A ω
      · have hb : ¬ B ω := fun hb => h ⟨ha, hb⟩
        simp [hb]
      · simp [ha]), h,
    pProb_eq_pE A (fun ω => if A ω then (1 : ℝ) else 0) (fun ω h => by simp [h])
      (fun ω h => by simp [h]),
    pProb_eq_pE B (fun ω => if B ω then (1 : ℝ) else 0) (fun ω h => by simp [h])
      (fun ω h => by simp [h])]

end Indep

section Push

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] {P : ι → α → ℝ}

/-- Expectation of a product of functions of distinct coordinates `j k`. -/
theorem pE_prod_comp (hP : IsPMF P) {κ : Type*} [Fintype κ] [DecidableEq κ] (j : κ → ι)
    (hj : Function.Injective j) (h : κ → α → ℝ) :
    pE P (fun ω => ∏ k, h k (ω (j k))) = ∏ k, ∑ a, P (j k) a * h k a := by
  set h' : ι → α → ℝ := fun i a => ∏ k ∈ univ.filter (fun k => j k = i), h k a with hh'
  have e1 : ∀ ω : ι → α, ∏ k, h k (ω (j k)) = ∏ i, h' i (ω i) := by
    intro ω
    rw [← prod_fiberwise univ j (fun k => h k (ω (j k)))]
    refine prod_congr rfl fun i _ => prod_congr rfl fun k hk => ?_
    rw [(mem_filter.mp hk).2]
  simp_rw [e1]
  rw [pE_prod h', ← prod_fiberwise univ j (fun k => ∑ a, P (j k) a * h k a)]
  refine prod_congr rfl fun i _ => ?_
  have hcard : (univ.filter (fun k => j k = i)).card ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    exact hj ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
  · rw [card_eq_zero] at h0
    simp only [hh', h0, prod_empty, mul_one, hP.2 i]
  · obtain ⟨k, hk⟩ := card_eq_one.mp h1
    have hmem : k ∈ univ.filter (fun k => j k = i) := by rw [hk]; exact mem_singleton_self k
    have hjk : j k = i := (mem_filter.mp hmem).2
    simp only [hh', hk, prod_singleton, hjk]

/-- **Pushforward along coordinatewise maps.** -/
theorem pE_map_coord (hP : IsPMF P) {κ β : Type*} [Fintype κ] [DecidableEq κ] [Fintype β]
    [DecidableEq β] (j : κ → ι) (hj : Function.Injective j) (φ : κ → α → β)
    (g : (κ → β) → ℝ) :
    pE P (fun ω => g (fun k => φ k (ω (j k)))) =
      pE (fun k b => ∑ a ∈ univ.filter (fun a => φ k a = b), P (j k) a) g := by
  have expand : ∀ η : κ → β, g η = ∑ η', g η' * ∏ k, (if η k = η' k then (1 : ℝ) else 0) := by
    intro η
    rw [sum_eq_single η]
    · rw [Finset.prod_eq_one (fun k _ => if_pos rfl), mul_one]
    · intro η' _ hne
      have : ∃ k, η k ≠ η' k := by
        by_contra h; push Not at h; exact hne (funext h).symm
      obtain ⟨k, hk⟩ := this
      rw [prod_eq_zero (mem_univ k) (by simp [hk]), mul_zero]
    · intro h; exact absurd (mem_univ η) h
  have h1 : (fun ω : ι → α => g (fun k => φ k (ω (j k)))) = fun ω =>
      ∑ η', g η' * ∏ k, (if φ k (ω (j k)) = η' k then (1 : ℝ) else 0) :=
    funext fun ω => expand _
  rw [h1, pE_sum]
  unfold pE
  refine sum_congr rfl fun η' _ => ?_
  have hpe := pE_prod_comp hP j hj (fun k a => if φ k a = η' k then (1 : ℝ) else 0)
  unfold pE at hpe
  calc ∑ ω, pw P ω * (g η' * ∏ k, if φ k (ω (j k)) = η' k then (1 : ℝ) else 0)
      = g η' * ∑ ω, pw P ω * ∏ k, (if φ k (ω (j k)) = η' k then (1 : ℝ) else 0) := by
        rw [mul_sum]; exact sum_congr rfl fun ω _ => by ring
    _ = g η' * ∏ k, ∑ a, P (j k) a * (if φ k a = η' k then (1 : ℝ) else 0) := by rw [hpe]
    _ = _ := by
        rw [mul_comm]
        congr 1
        unfold pw
        refine prod_congr rfl fun k _ => ?_
        show _ = ∑ a ∈ univ.filter (fun a => φ k a = η' k), P (j k) a
        rw [sum_filter]
        refine sum_congr rfl fun a _ => ?_
        split_ifs <;> simp

end Push

section Curry

variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype α]

/-- The block distribution: the product law of a block of coordinates. -/
def blockP (P : ι × κ → α → ℝ) : ι → (κ → α) → ℝ := fun i x => pw (fun k => P (i, k)) x

theorem blockP_isPMF {P : ι × κ → α → ℝ} (hP : IsPMF P) : IsPMF (blockP P) :=
  ⟨fun i x => pw_nonneg ⟨fun k a => hP.1 (i, k) a, fun k => hP.2 (i, k)⟩ x,
    fun i => sum_pw ⟨fun k a => hP.1 (i, k) a, fun k => hP.2 (i, k)⟩⟩

/-- **Grouping coordinates into blocks.** -/
theorem pE_curry (P : ι × κ → α → ℝ) (f : (ι × κ → α) → ℝ) :
    pE P f = pE (blockP P) (fun y => f (fun p => y p.1 p.2)) := by
  unfold pE
  refine (Fintype.sum_equiv (Equiv.curry ι κ α) _ _ fun ω => ?_)
  simp only [Equiv.curry_apply, Function.curry_apply]
  congr 1
  unfold pw blockP pw
  rw [← Fintype.prod_prod_type']
  rfl

theorem pProb_curry (P : ι × κ → α → ℝ) (S : (ι × κ → α) → Prop) :
    pProb P S = pProb (blockP P) (fun y => S (fun p => y p.1 p.2)) := by
  classical
  unfold pProb
  rw [pE_curry]

end Curry

section Resample

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] {P : ι → α → ℝ}

/-- Integrating out the coordinate `i` of a product `f * g` where `f` does not depend on it. -/
theorem pE_mul_le_of_coord (hP : IsPMF P) (i : ι) (f g : (ι → α) → ℝ) (q : ℝ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hf : ∀ ω a, f (Function.update ω i a) = f ω)
    (hg : ∀ ω, ∑ a, P i a * g (Function.update ω i a) ≤ q) :
    pE P (fun ω => f ω * g ω) ≤ q * pE P f := by
  rw [← pE_resample hP i (fun ω => f ω * g ω), ← pE_const_mul]
  refine pE_mono hP fun ω => ?_
  simp only [hf]
  simp_rw [show ∀ a, P i a * (f ω * g (Function.update ω i a)) =
      f ω * (P i a * g (Function.update ω i a)) from fun a => by ring]
  rw [← mul_sum]
  calc f ω * ∑ a, P i a * g (Function.update ω i a) ≤ f ω * q :=
        mul_le_mul_of_nonneg_left (hg ω) (hf0 ω)
    _ = q * f ω := by ring

end Resample

end Pseudorandom.PS
