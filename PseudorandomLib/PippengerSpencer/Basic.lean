/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.Defs

/-! # Proper edge colourings

Basic facts about proper edge colourings of hypergraphs:
* the definition `IsProperEdgeColouring`;
* the greedy bound: an `r`-uniform hypergraph of maximum degree `≤ Δ` has a proper edge
  colouring with `r Δ + 1` colours;
* gluing colourings of two edge sets with disjoint palettes.
-/

@[expose] public section

namespace Pseudorandom

open Finset

variable {V : Type*} [DecidableEq V]

/-- A proper edge colouring of `H` with `m` colours: edges of the same colour are disjoint. -/
def IsProperEdgeColouring (H : Finset (Finset V)) (m : ℕ) (c : Finset V → Fin m) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ≠ f → c e = c f → Disjoint e f

omit [DecidableEq V] in
theorem IsProperEdgeColouring.mono {H H' : Finset (Finset V)} {m : ℕ} {c : Finset V → Fin m}
    (h : IsProperEdgeColouring H m c) (hH : H' ⊆ H) : IsProperEdgeColouring H' m c :=
  fun e he f hf hef hc => h e (hH he) f (hH hf) hef hc

theorem degree_mono' {A B : Finset (Finset V)} (h : A ⊆ B) (v : V) :
    degree A v ≤ degree B v :=
  card_le_card (filter_subset_filter _ h)

/-- The edges of `H` meeting a set `e` number at most `∑_{v ∈ e} deg_H(v)`. -/
theorem card_filter_not_disjoint_le (H : Finset (Finset V)) (e : Finset V) :
    (H.filter (fun f => ¬ Disjoint e f)).card ≤ ∑ v ∈ e, degree H v := by
  have hsub : H.filter (fun f => ¬ Disjoint e f) ⊆
      e.biUnion (fun v => H.filter (fun f => v ∈ f)) := by
    intro f hf
    rw [mem_filter, Finset.not_disjoint_iff] at hf
    obtain ⟨hfH, v, hve, hvf⟩ := hf
    rw [mem_biUnion]
    exact ⟨v, hve, mem_filter.mpr ⟨hfH, hvf⟩⟩
  exact (card_le_card hsub).trans card_biUnion_le

/-- **Greedy colouring.** An `r`-uniform hypergraph with all degrees `≤ Δ` has a proper edge
colouring with `r Δ + 1` colours. -/
theorem exists_greedy_colouring (r Δ : ℕ) :
    ∀ (H : Finset (Finset V)), IsUniform H r → (∀ v, degree H v ≤ Δ) →
      ∃ c : Finset V → Fin (r * Δ + 1), IsProperEdgeColouring H (r * Δ + 1) c := by
  intro H
  induction H using Finset.induction_on with
  | empty => exact fun _ _ => ⟨fun _ => 0, fun e he => by simp at he⟩
  | @insert e H heH ih =>
    intro huni hdeg
    obtain ⟨c, hc⟩ := ih (fun f hf => huni f (mem_insert_of_mem hf))
      (fun v => (degree_mono' (subset_insert e H) v).trans (hdeg v))
    set used : Finset (Fin (r * Δ + 1)) := (H.filter (fun f => ¬ Disjoint e f)).image c
    have hused : used.card < r * Δ + 1 := by
      have h1 : used.card ≤ (H.filter (fun f => ¬ Disjoint e f)).card := card_image_le
      have h2 := card_filter_not_disjoint_le H e
      have h3 : ∑ v ∈ e, degree H v ≤ ∑ v ∈ e, Δ :=
        sum_le_sum fun v _ => (degree_mono' (subset_insert e H) v).trans (hdeg v)
      rw [sum_const, huni e (mem_insert_self e H), smul_eq_mul] at h3
      omega
    obtain ⟨k, hk⟩ : ∃ k : Fin (r * Δ + 1), k ∉ used := by
      by_contra h
      push Not at h
      have : (univ : Finset (Fin (r * Δ + 1))) ⊆ used := fun k _ => h k
      have := card_le_card this
      rw [card_univ, Fintype.card_fin] at this
      omega
    refine ⟨fun f => if f = e then k else c f, ?_⟩
    intro f hf g hg hfg hcol
    rw [mem_insert] at hf hg
    by_cases hfe : f = e
    · subst hfe
      have hge : g ≠ f := fun h => hfg h.symm
      have hgH : g ∈ H := hg.resolve_left hge
      simp only [hge, ite_true, ite_false] at hcol
      by_contra hd
      exact hk (hcol ▸ mem_image_of_mem c (mem_filter.mpr ⟨hgH, hd⟩))
    · have hfH : f ∈ H := hf.resolve_left hfe
      by_cases hge : g = e
      · subst hge
        simp only [hfe, ite_true, ite_false] at hcol
        by_contra hd
        exact hk (hcol.symm ▸ mem_image_of_mem c (mem_filter.mpr ⟨hfH, fun h => hd h.symm⟩))
      · have hgH : g ∈ H := hg.resolve_left hge
        simp only [hfe, hge, ite_false] at hcol
        exact hc f hfH g hgH hfg hcol

/-- Gluing two proper colourings with disjoint palettes. -/
theorem IsProperEdgeColouring.glue {H₁ H₂ : Finset (Finset V)} {m₁ m₂ : ℕ}
    {c₁ : Finset V → Fin m₁} {c₂ : Finset V → Fin m₂}
    (h₁ : IsProperEdgeColouring H₁ m₁ c₁) (h₂ : IsProperEdgeColouring H₂ m₂ c₂) :
    IsProperEdgeColouring (H₁ ∪ H₂) (m₁ + m₂)
      (fun e => if e ∈ H₁ then Fin.castAdd m₂ (c₁ e) else Fin.natAdd m₁ (c₂ e)) := by
  intro e he f hf hef hc
  rw [mem_union] at he hf
  by_cases he1 : e ∈ H₁ <;> by_cases hf1 : f ∈ H₁ <;>
    simp only [he1, hf1, ite_true, ite_false] at hc
  · exact h₁ e he1 f hf1 hef (Fin.castAdd_inj.mp hc)
  · exfalso
    have := congrArg Fin.val hc
    simp at this
    omega
  · exfalso
    have := congrArg Fin.val hc
    simp at this
    omega
  · exact h₂ e (he.resolve_left he1) f (hf.resolve_left hf1) hef (by
      have := congrArg Fin.val hc
      simp at this
      exact Fin.ext this)

omit [DecidableEq V] in
/-- Enlarging the palette. -/
theorem IsProperEdgeColouring.castLE {H : Finset (Finset V)} {m m' : ℕ} {c : Finset V → Fin m}
    (h : IsProperEdgeColouring H m c) (hm : m ≤ m') :
    IsProperEdgeColouring H m' (fun e => Fin.castLE hm (c e)) :=
  fun e he f hf hef hc => h e he f hf hef (Fin.castLE_inj.mp hc)

end Pseudorandom
