/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.PippengerSpencer.Basic

/-! # Iterating batches of colours

If every subhypergraph of maximum degree `Db ≥ L` admits a partial proper colouring with `K`
colours lowering the maximum degree to `Db - K λ`, then after `b` rounds (as long as the degree
bound stays `≥ L`) we obtain a partial proper colouring with `b K + 1` colours whose leftover has
maximum degree `≤ D - b K λ`.
-/

@[expose] public section

namespace Pseudorandom.PS

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Iterating batches.** -/
theorem iterate_batches (H : Finset (Finset V)) {K : ℕ} {lam D L : ℝ}
    (hstep : ∀ G ⊆ H, ∀ Db : ℝ, L ≤ Db → (∀ v, (degree G v : ℝ) ≤ Db) →
      ∃ (Col : Finset (Finset V)) (c : Finset V → Fin K), Col ⊆ G ∧
        IsProperEdgeColouring Col K c ∧ ∀ v, (degree (G \ Col) v : ℝ) ≤ Db - K * lam)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ D) :
    ∀ b : ℕ, (∀ j < b, L ≤ D - j * (K * lam)) →
      ∃ (Col : Finset (Finset V)) (c : Finset V → Fin (b * K + 1)), Col ⊆ H ∧
        IsProperEdgeColouring Col (b * K + 1) c ∧
        ∀ v, (degree (H \ Col) v : ℝ) ≤ D - b * (K * lam) := by
  intro b
  induction b with
  | zero =>
    intro _
    refine ⟨∅, fun _ => 0, empty_subset _, ?_, ?_⟩
    · intro e he; simp at he
    · intro v; simpa using hdeg v
  | succ b ih =>
    intro hj
    obtain ⟨Col, c, hCol, hc, hdegC⟩ := ih (fun j hjb => hj j (by omega))
    obtain ⟨Col', c', hCol', hc', hdegC'⟩ := hstep (H \ Col) sdiff_subset _
      (by have := hj b (by omega); exact this) hdegC
    have hglue := hc.glue hc'
    have hle : b * K + 1 + K ≤ (b + 1) * K + 1 := le_of_eq (by ring)
    refine ⟨Col ∪ Col', _, union_subset hCol (hCol'.trans sdiff_subset),
      hglue.castLE hle, ?_⟩
    intro v
    have : H \ (Col ∪ Col') = (H \ Col) \ Col' := by
      ext e; simp only [mem_sdiff, mem_union]; tauto
    rw [this]
    refine (hdegC' v).trans (le_of_eq ?_)
    push_cast; ring

end Pseudorandom.PS
