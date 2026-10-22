/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.Defs

/-! # Counting lemmas for hypergraphs

* `meet A T`: the edges of `A` meeting a vertex set `T`;
* `|meet A T| ≤ ∑_{u ∈ T} deg u` and the Bonferroni lower bound
  `∑_{u ∈ T} deg u ≤ |meet A T| + ∑_{u ≠ w ∈ T} codeg(u, w)`;
* `∑_{w ≠ v} codeg(v, w) = (r - 1) deg v` for `r`-uniform hypergraphs;
* an elementary bound for the difference of two filtered cardinalities.
-/

@[expose] public section

namespace Pseudorandom

open Finset

variable {V : Type*} [DecidableEq V]

/-- The edges of `A` meeting the vertex set `T`. -/
def meet (A : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  A.filter (fun f => ¬ Disjoint f T)

theorem mem_meet {A : Finset (Finset V)} {T : Finset V} {f : Finset V} :
    f ∈ meet A T ↔ f ∈ A ∧ ∃ u ∈ T, u ∈ f := by
  unfold meet
  rw [mem_filter, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨h1, u, h2, h3⟩; exact ⟨h1, u, h3, h2⟩
  · rintro ⟨h1, u, h2, h3⟩; exact ⟨h1, u, h3, h2⟩

theorem degree_eq_sum (A : Finset (Finset V)) (u : V) :
    degree A u = ∑ f ∈ A, if u ∈ f then 1 else 0 := by
  unfold degree; rw [card_filter]

theorem codegree_eq_sum (A : Finset (Finset V)) (u w : V) :
    codegree A u w = ∑ f ∈ A, if u ∈ f ∧ w ∈ f then 1 else 0 := by
  unfold codegree; rw [card_filter]

theorem sum_degree_eq (A : Finset (Finset V)) (T : Finset V) :
    ∑ u ∈ T, degree A u = ∑ f ∈ A, (T.filter (· ∈ f)).card := by
  simp_rw [degree_eq_sum, card_filter]
  rw [sum_comm]

theorem card_meet_eq (A : Finset (Finset V)) (T : Finset V) :
    (meet A T).card = ∑ f ∈ A, if 0 < (T.filter (· ∈ f)).card then 1 else 0 := by
  unfold meet
  rw [card_filter]
  refine sum_congr rfl fun f _ => ?_
  congr 1
  apply propext
  rw [Finset.not_disjoint_iff, card_pos, filter_nonempty_iff]
  constructor
  · rintro ⟨u, h1, h2⟩; exact ⟨u, h2, h1⟩
  · rintro ⟨u, h1, h2⟩; exact ⟨u, h2, h1⟩

/-- `|meet A T| ≤ ∑_{u ∈ T} deg u`. -/
theorem card_meet_le (A : Finset (Finset V)) (T : Finset V) :
    (meet A T).card ≤ ∑ u ∈ T, degree A u := by
  rw [card_meet_eq, sum_degree_eq]
  refine sum_le_sum fun f _ => ?_
  split_ifs with h
  · exact h
  · exact Nat.zero_le _

theorem sum_codegree_eq (A : Finset (Finset V)) (T : Finset V) :
    ∑ u ∈ T, ∑ w ∈ T.erase u, codegree A u w =
      ∑ f ∈ A, (T.filter (· ∈ f)).card * ((T.filter (· ∈ f)).card - 1) := by
  simp_rw [codegree_eq_sum]
  have h1 : ∀ u ∈ T, ∑ w ∈ T.erase u, ∑ f ∈ A, (if u ∈ f ∧ w ∈ f then 1 else 0) =
      ∑ f ∈ A, ∑ w ∈ T.erase u, (if u ∈ f ∧ w ∈ f then 1 else 0) := fun u _ => sum_comm
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun f _ => ?_
  set S := T.filter (· ∈ f)
  have h2 : ∀ u ∈ T, ∑ w ∈ T.erase u, (if u ∈ f ∧ w ∈ f then 1 else 0) =
      if u ∈ S then (S.erase u).card else 0 := by
    intro u hu
    by_cases huf : u ∈ f
    · have : u ∈ S := mem_filter.mpr ⟨hu, huf⟩
      rw [if_pos this]
      simp only [huf, true_and]
      rw [← card_filter]
      congr 1
      ext w
      simp [S, mem_filter, mem_erase]
      tauto
    · have : u ∉ S := fun h => huf (mem_filter.mp h).2
      rw [if_neg this]
      simp [huf]
  rw [sum_congr rfl h2, ← sum_filter]
  have h3 : T.filter (· ∈ S) = S := by
    ext u; simp only [mem_filter, S]; tauto
  rw [h3]
  have h4 : ∀ u ∈ S, (S.erase u).card = S.card - 1 := fun u hu => card_erase_of_mem hu
  rw [sum_congr rfl h4, sum_const, smul_eq_mul]

/-- Bonferroni: `∑_{u ∈ T} deg u ≤ |meet A T| + ∑_{u ∈ T} ∑_{w ∈ T, w ≠ u} codeg(u, w)`. -/
theorem sum_degree_le (A : Finset (Finset V)) (T : Finset V) :
    ∑ u ∈ T, degree A u ≤ (meet A T).card + ∑ u ∈ T, ∑ w ∈ T.erase u, codegree A u w := by
  rw [sum_codegree_eq, card_meet_eq, sum_degree_eq, ← sum_add_distrib]
  refine sum_le_sum fun f _ => ?_
  set k := (T.filter (· ∈ f)).card
  split_ifs with h
  · rcases k with _ | k
    · omega
    · simp only [Nat.add_sub_cancel]
      nlinarith
  · omega

/-- Two filters of the same finset that agree outside `B` differ in size by at most `|B|`. -/
theorem abs_card_filter_sub_le {β : Type*} [DecidableEq β] (s : Finset β) (p q : β → Prop)
    [DecidablePred p] [DecidablePred q] (B : Finset β)
    (hB : ∀ x ∈ s, x ∉ B → (p x ↔ q x)) :
    |((s.filter p).card : ℝ) - (s.filter q).card| ≤ B.card := by
  have hp := card_filter_add_card_filter_not (s := s.filter p) (fun x => x ∈ B)
  have hq := card_filter_add_card_filter_not (s := s.filter q) (fun x => x ∈ B)
  have heq : (s.filter p).filter (fun x => ¬ x ∈ B) = (s.filter q).filter (fun x => ¬ x ∈ B) := by
    ext x
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, (hB x h1 h3).mp h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, (hB x h1 h3).mpr h2⟩, h3⟩
  have hpB : ((s.filter p).filter (fun x => x ∈ B)).card ≤ B.card :=
    card_le_card fun x hx => (mem_filter.mp hx).2
  have hqB : ((s.filter q).filter (fun x => x ∈ B)).card ≤ B.card :=
    card_le_card fun x hx => (mem_filter.mp hx).2
  rw [heq] at hp
  rw [abs_le]
  constructor
  · have : ((s.filter q).card : ℝ) ≤ (s.filter p).card + B.card := by
      have : (s.filter q).card ≤ (s.filter p).card + B.card := by omega
      exact_mod_cast this
    linarith
  · have : ((s.filter p).card : ℝ) ≤ (s.filter q).card + B.card := by
      have : (s.filter p).card ≤ (s.filter q).card + B.card := by omega
      exact_mod_cast this
    linarith

theorem codegree_le_degree (A : Finset (Finset V)) (u w : V) : codegree A u w ≤ degree A u :=
  card_le_card fun f hf => by
    simp only [mem_filter] at hf ⊢; exact ⟨hf.1, hf.2.1⟩

theorem degree_mono {A B : Finset (Finset V)} (h : A ⊆ B) (v : V) : degree A v ≤ degree B v :=
  card_le_card (filter_subset_filter _ h)

theorem codegree_mono {A B : Finset (Finset V)} (h : A ⊆ B) (u w : V) :
    codegree A u w ≤ codegree B u w :=
  card_le_card (filter_subset_filter _ h)

/-- In an `r`-uniform hypergraph, `∑_{w ≠ v} codeg(v, w) = (r - 1) deg v`. -/
theorem sum_codegree_erase [Fintype V] (A : Finset (Finset V)) (r : ℕ) (hA : IsUniform A r)
    (v : V) : ∑ w ∈ univ.erase v, codegree A v w = (r - 1) * degree A v := by
  simp_rw [codegree_eq_sum]
  rw [sum_comm, degree_eq_sum, mul_sum]
  refine sum_congr rfl fun f hf => ?_
  by_cases hv : v ∈ f
  · simp only [hv, true_and, if_true, mul_one]
    rw [← card_filter]
    have : (univ.erase v).filter (· ∈ f) = f.erase v := by
      ext w; simp [mem_erase]
    rw [this, card_erase_of_mem hv, hA f hf]
  · simp [hv]

end Pseudorandom
