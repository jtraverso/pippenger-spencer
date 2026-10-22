/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.NibbleRound

/-! # Degrees after one nibble round

`degP A ω v` counts the alive edges at `v` whose other vertices survive the round; it
dominates the new degree of `v`. We compute its expectation, bound it using codegrees, and
prove a Bernstein-type upper tail for it.
-/

@[expose] public section

namespace Pseudorandom.Nibble

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

section Expectation

variable (A : Finset (Finset V)) {a : ℝ} (D : ℝ)

theorem degP_eq_sum (ω : Coin V → Bool) (v : V) :
    (degP A ω v : ℝ) = ∑ e ∈ A.filter (v ∈ ·),
      (if ∀ u ∈ e.erase v, ¬ Dead A ω u then (1 : ℝ) else 0) := by
  unfold degP
  have : A.filter (fun e => v ∈ e ∧ ∀ u ∈ e, u ≠ v → ¬ Dead A ω u) =
      (A.filter (v ∈ ·)).filter (fun e => ∀ u ∈ e.erase v, ¬ Dead A ω u) := by
    rw [filter_filter]
    congr 1
    ext e
    simp only [mem_erase]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun u ⟨hu1, hu2⟩ => h2 u hu2 hu1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun u hu1 hu2 => h2 u ⟨hu2, hu1⟩⟩
  rw [this, card_filter]
  push_cast
  rfl

theorem pE_degP (v : V) :
    pE (roundP A a D) (fun ω => (degP A ω v : ℝ)) =
      ∑ e ∈ A.filter (v ∈ ·), pProb (roundP A a D) (fun ω => ∀ u ∈ e.erase v, ¬ Dead A ω u) := by
  simp_rw [degP_eq_sum]
  rw [pE_sum]
  refine sum_congr rfl fun e _ => ?_
  exact (pProb_eq_pE _ _ (fun ω h => if_pos h) (fun ω h => if_neg h)).symm

/-- `E[degP v] ≤ D e^{-a((r-1) D - (r-1)² K)}`. -/
theorem pE_degP_le (ha : 0 ≤ a) (r : ℕ) (huni : IsUniform A r)
    (hdeg : ∀ u, (degree A u : ℝ) ≤ D) (K : ℝ) (hK : 0 ≤ K)
    (hcod : ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K) (v : V) :
    pE (roundP A a D) (fun ω => (degP A ω v : ℝ)) ≤
      D * Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) := by
  rw [pE_degP]
  have hterm : ∀ e ∈ A.filter (v ∈ ·),
      pProb (roundP A a D) (fun ω => ∀ u ∈ e.erase v, ¬ Dead A ω u) ≤
        Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) := by
    intro e he
    rw [mem_filter] at he
    have hc : (e.erase v).card = r - 1 := by rw [card_erase_of_mem he.2, huni e he.1]
    have := prob_notDead_le A D ha (e.erase v) (fun u _ => hdeg u) K hK
      (fun u _ w _ huw => hcod u w huw)
    rwa [hc] at this
  calc _ ≤ ∑ e ∈ A.filter (v ∈ ·),
        Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) :=
        sum_le_sum hterm
    _ = (degree A v : ℝ) *
        Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) := by
        rw [sum_const, nsmul_eq_mul]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (hdeg v) (Real.exp_pos _).le

end Expectation

/-! ## Bounded differences for `degP` -/

section Gap

omit [Fintype V] in
theorem dead_update_inl (A : Finset (Finset V)) (ω : Coin V → Bool) (g : Finset V) (b : Bool)
    (u : V) (h : g ∉ A ∨ u ∉ g) :
    Dead A (Function.update ω (Sum.inl g) b) u ↔ Dead A ω u := by
  unfold Dead
  have h2 : Function.update ω (Sum.inl g) b (Sum.inr u) = ω (Sum.inr u) :=
    Function.update_of_ne (by simp) _ _
  rw [h2]
  constructor
  · rintro (⟨f, hf, huf, hω⟩ | h3)
    · have hfg : f ≠ g := by rintro rfl; rcases h with h | h <;> contradiction
      rw [Function.update_of_ne (by simpa using hfg)] at hω
      exact Or.inl ⟨f, hf, huf, hω⟩
    · exact Or.inr h3
  · rintro (⟨f, hf, huf, hω⟩ | h3)
    · have hfg : f ≠ g := by rintro rfl; rcases h with h | h <;> contradiction
      refine Or.inl ⟨f, hf, huf, ?_⟩
      rw [Function.update_of_ne (by simpa using hfg)]; exact hω
    · exact Or.inr h3

omit [Fintype V] in
theorem dead_update_inr (A : Finset (Finset V)) (ω : Coin V → Bool) (w : V) (b : Bool)
    (u : V) (h : u ≠ w) :
    Dead A (Function.update ω (Sum.inr w) b) u ↔ Dead A ω u := by
  unfold Dead
  have h2 : Function.update ω (Sum.inr w) b (Sum.inr u) = ω (Sum.inr u) :=
    Function.update_of_ne (by simpa using h) _ _
  have h3 : ∀ f : Finset V, Function.update ω (Sum.inr w) b (Sum.inl f) = ω (Sum.inl f) :=
    fun f => Function.update_of_ne (by simp) _ _
  simp only [h2, h3]

omit [Fintype V] [DecidableEq V] in
theorem degP_pred_congr (A : Finset (Finset V)) (ω₁ ω₂ : Coin V → Bool) (v : V) (e : Finset V)
    (h : v ∈ e → ∀ u ∈ e, u ≠ v → (Dead A ω₁ u ↔ Dead A ω₂ u)) :
    (v ∈ e ∧ ∀ u ∈ e, u ≠ v → ¬ Dead A ω₁ u) ↔ (v ∈ e ∧ ∀ u ∈ e, u ≠ v → ¬ Dead A ω₂ u) := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun u hu huv hd => h2 u hu huv ((h h1 u hu huv).mpr hd)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun u hu huv hd => h2 u hu huv ((h h1 u hu huv).mp hd)⟩

/-- The sensitivity of `degP v` to each coin. -/
noncomputable def cDeg (A : Finset (Finset V)) (v : V) : Coin V → ℝ
  | Sum.inl g => if g ∈ A then
      ((A.filter (fun e => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) else 0
  | Sum.inr w => if w = v then 0 else (codegree A v w : ℝ)

theorem degP_coordGap (A : Finset (Finset V)) (v : V) :
    CoordGap (fun ω => (degP A ω v : ℝ)) (cDeg A v) := by
  intro i ω b b'
  unfold degP
  cases i with
  | inl g =>
    by_cases hg : g ∈ A
    · simp only [cDeg, hg, if_true]
      apply abs_card_filter_sub_le
      intro e heA heB
      apply degP_pred_congr
      intro hve u hu huv
      have hug : u ∉ g := fun hug => heB (mem_filter.mpr ⟨heA, hve, u, hu, huv, hug⟩)
      rw [dead_update_inl A ω g b u (Or.inr hug), dead_update_inl A ω g b' u (Or.inr hug)]
    · simp only [cDeg, hg, if_false]
      have := abs_card_filter_sub_le A _ _ (∅ : Finset (Finset V))
        (fun e _ _ => degP_pred_congr A (Function.update ω (Sum.inl g) b)
          (Function.update ω (Sum.inl g) b') v e (fun _ u _ _ => by
            rw [dead_update_inl A ω g b u (Or.inl hg), dead_update_inl A ω g b' u (Or.inl hg)]))
      simpa using this
  | inr w =>
    by_cases hw : w = v
    · subst hw
      simp only [cDeg, if_true]
      have := abs_card_filter_sub_le A _ _ (∅ : Finset (Finset V))
        (fun e _ _ => degP_pred_congr A (Function.update ω (Sum.inr w) b)
          (Function.update ω (Sum.inr w) b') w e (fun _ u _ huv => by
            rw [dead_update_inr A ω w b u huv, dead_update_inr A ω w b' u huv]))
      simpa using this
    · simp only [cDeg, hw, if_false]
      unfold codegree
      apply abs_card_filter_sub_le
      intro e heA heB
      apply degP_pred_congr
      intro hve u hu huv
      have huw : u ≠ w := by
        rintro rfl
        exact heB (mem_filter.mpr ⟨heA, hve, hu⟩)
      rw [dead_update_inr A ω w b u huw, dead_update_inr A ω w b' u huw]

end Gap

/-! ## The upper tail of `degP` -/

section Tail

variable (A : Finset (Finset V)) {a : ℝ} (D : ℝ)

omit [Fintype V] in
theorem cDeg_nonneg (v : V) (i : Coin V) : 0 ≤ cDeg A v i := by
  cases i <;> simp only [cDeg] <;> split_ifs <;> positivity

omit [Fintype V] in
theorem cDeg_le (r : ℕ) (huni : IsUniform A r) (hr : 1 ≤ r) (K : ℝ) (hK : 0 ≤ K)
    (hcod : ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K) (v : V) (i : Coin V) :
    cDeg A v i ≤ r * K := by
  cases i with
  | inl g =>
    simp only [cDeg]
    split_ifs with hg
    · have hsub : A.filter (fun e => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g) ⊆
          (g.erase v).biUnion (fun u => A.filter (fun e => v ∈ e ∧ u ∈ e)) := by
        intro e he
        simp only [mem_filter] at he
        obtain ⟨heA, hve, u, hue, huv, hug⟩ := he
        exact mem_biUnion.mpr ⟨u, mem_erase.mpr ⟨huv, hug⟩, mem_filter.mpr ⟨heA, hve, hue⟩⟩
      have h1 := (card_le_card hsub).trans card_biUnion_le
      have h2 : ((A.filter (fun e => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) ≤
          ∑ u ∈ g.erase v, (codegree A v u : ℝ) := by
        unfold codegree; exact_mod_cast h1
      have h3 : ∑ u ∈ g.erase v, (codegree A v u : ℝ) ≤ ∑ u ∈ g.erase v, K :=
        sum_le_sum fun u hu => hcod v u (ne_of_mem_erase hu).symm
      have h4 : ((g.erase v).card : ℝ) ≤ r := by
        have := card_erase_le (s := g) (a := v)
        rw [huni g hg] at this
        exact_mod_cast this
      rw [sum_const, nsmul_eq_mul] at h3
      nlinarith
    · have : (0 : ℝ) ≤ r := by positivity
      positivity
  | inr w =>
    simp only [cDeg]
    split_ifs with hw
    · positivity
    · have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have := hcod v w (Ne.symm hw)
      nlinarith

omit [Fintype V] in
theorem sum_card_filter_meet_le (r : ℕ) (huni : IsUniform A r)
    (hdeg : ∀ u, (degree A u : ℝ) ≤ D) (v : V) :
    ∑ g ∈ A, ((A.filter (fun e => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) ≤ r * D * D := by
  have hswap : ∑ g ∈ A, ((A.filter (fun e => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) =
      ∑ e ∈ A, ((A.filter (fun g => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) := by
    simp_rw [card_filter]
    push_cast
    exact sum_comm
  rw [hswap]
  have hterm : ∀ e ∈ A, ((A.filter (fun g => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) ≤
      if v ∈ e then r * D else 0 := by
    intro e he
    split_ifs with hve
    · have hsub : A.filter (fun g => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g) ⊆ meet A (e.erase v) := by
        intro g hg
        simp only [mem_filter] at hg
        obtain ⟨hgA, _, u, hue, huv, hug⟩ := hg
        exact mem_meet.mpr ⟨hgA, u, mem_erase.mpr ⟨huv, hue⟩, hug⟩
      have h1 : ((A.filter (fun g => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) ≤
          ∑ u ∈ e.erase v, (degree A u : ℝ) := by
        exact_mod_cast (card_le_card hsub).trans (card_meet_le A _)
      have h2 : ∑ u ∈ e.erase v, (degree A u : ℝ) ≤ ∑ u ∈ e.erase v, D :=
        sum_le_sum fun u _ => hdeg u
      have h3 : ((e.erase v).card : ℝ) ≤ r := by
        have := card_erase_le (s := e) (a := v)
        rw [huni e he] at this
        exact_mod_cast this
      have hD : 0 ≤ D := (Nat.cast_nonneg _).trans (hdeg v)
      rw [sum_const, nsmul_eq_mul] at h2
      nlinarith
    · have : A.filter (fun g => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g) = ∅ := by
        ext g; simp [hve]
      simp [this]
  calc _ ≤ ∑ e ∈ A, (if v ∈ e then r * D else 0) := sum_le_sum hterm
    _ = (degree A v : ℝ) * (r * D) := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]; rfl
    _ ≤ D * (r * D) := by
        have hD : 0 ≤ D := (Nat.cast_nonneg _).trans (hdeg v)
        exact mul_le_mul_of_nonneg_right (hdeg v) (by positivity)
    _ = r * D * D := by ring

theorem sum_q_cDeg_sq_le (ha : 0 ≤ a) (hD : 0 ≤ D) (r : ℕ) (huni : IsUniform A r) (hr : 1 ≤ r)
    (hdeg : ∀ u, (degree A u : ℝ) ≤ D) (K : ℝ) (hK : 0 ≤ K)
    (hcod : ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K) (v : V) :
    ∑ i, qTrue A a D i * cDeg A v i ^ 2 ≤ 2 * a * r ^ 2 * K * D ^ 2 := by
  have hcle := cDeg_le A r huni hr K hK hcod v
  have hc0 := cDeg_nonneg A v
  rw [Fintype.sum_sum_type]
  -- edge coins
  have h1 : ∑ g : Finset V, qTrue A a D (Sum.inl g) * cDeg A v (Sum.inl g) ^ 2 ≤
      a * (r * K) * (r * D * D) := by
    have hpt : ∀ g : Finset V, qTrue A a D (Sum.inl g) * cDeg A v (Sum.inl g) ^ 2 ≤
        a * (r * K) * cDeg A v (Sum.inl g) := by
      intro g
      have hq : qTrue A a D (Sum.inl g) ≤ a ∨ cDeg A v (Sum.inl g) = 0 := by
        by_cases hg : g ∈ A
        · left; simp only [qTrue, hg, if_true]; linarith [Real.one_sub_le_exp_neg a]
        · right; simp [cDeg, hg]
      have hq0 := (qTrue_mem A ha D (Sum.inl g)).1
      rcases hq with hq | hq
      · have := hcle (Sum.inl g)
        have := hc0 (Sum.inl g)
        calc _ = qTrue A a D (Sum.inl g) * cDeg A v (Sum.inl g) * cDeg A v (Sum.inl g) := by
              ring
          _ ≤ a * cDeg A v (Sum.inl g) * (r * K) := by gcongr
          _ = _ := by ring
      · rw [hq]; simp
    have hsum : ∑ g : Finset V, cDeg A v (Sum.inl g) ≤ r * D * D := by
      have : ∑ g : Finset V, cDeg A v (Sum.inl g) =
          ∑ g ∈ A, ((A.filter (fun e => v ∈ e ∧ ∃ u ∈ e, u ≠ v ∧ u ∈ g)).card : ℝ) := by
        simp only [cDeg]
        rw [← sum_filter]
        simp
      rw [this]
      exact sum_card_filter_meet_le A D r huni hdeg v
    calc _ ≤ ∑ g : Finset V, a * (r * K) * cDeg A v (Sum.inl g) := sum_le_sum fun g _ => hpt g
      _ = a * (r * K) * ∑ g : Finset V, cDeg A v (Sum.inl g) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  -- vertex coins
  have h2 : ∑ w : V, qTrue A a D (Sum.inr w) * cDeg A v (Sum.inr w) ^ 2 ≤
      (a * D) * (r * K) * (r * D) := by
    have hpt : ∀ w : V, qTrue A a D (Sum.inr w) * cDeg A v (Sum.inr w) ^ 2 ≤
        (a * D) * (r * K) * cDeg A v (Sum.inr w) := by
      intro w
      have hq : qTrue A a D (Sum.inr w) ≤ a * D := by
        simp only [qTrue]
        have h3 := Real.one_sub_le_exp_neg (a * max 0 (D - degree A w))
        have h4 : max 0 (D - degree A w) ≤ D := max_le hD (by linarith [Nat.cast_nonneg (α := ℝ) (degree A w)])
        have h5 : a * max 0 (D - degree A w) ≤ a * D := mul_le_mul_of_nonneg_left h4 ha
        linarith
      have hq0 := (qTrue_mem A ha D (Sum.inr w)).1
      have := hcle (Sum.inr w)
      have := hc0 (Sum.inr w)
      calc _ = qTrue A a D (Sum.inr w) * cDeg A v (Sum.inr w) * cDeg A v (Sum.inr w) := by ring
        _ ≤ (a * D) * cDeg A v (Sum.inr w) * (r * K) := by gcongr
        _ = _ := by ring
    have hsum : ∑ w : V, cDeg A v (Sum.inr w) ≤ r * D := by
      have : ∑ w : V, cDeg A v (Sum.inr w) = ∑ w ∈ univ.erase v, (codegree A v w : ℝ) := by
        rw [← add_sum_erase _ _ (mem_univ v)]
        simp only [cDeg, if_true, zero_add]
        refine sum_congr rfl fun w hw => ?_
        rw [if_neg (ne_of_mem_erase hw)]
      rw [this]
      have h3 := sum_codegree_erase A r huni v
      have h4 : ∑ w ∈ univ.erase v, (codegree A v w : ℝ) = ((r - 1 : ℕ) : ℝ) * degree A v := by
        exact_mod_cast h3
      rw [h4]
      have h5 : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
      have := hdeg v
      have : (0 : ℝ) ≤ degree A v := Nat.cast_nonneg _
      nlinarith
    calc _ ≤ ∑ w : V, (a * D) * (r * K) * cDeg A v (Sum.inr w) := sum_le_sum fun w _ => hpt w
      _ = (a * D) * (r * K) * ∑ w : V, cDeg A v (Sum.inr w) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  calc _ ≤ a * (r * K) * (r * D * D) + (a * D) * (r * K) * (r * D) := add_le_add h1 h2
    _ = 2 * a * r ^ 2 * K * D ^ 2 := by ring

/-- **Upper tail of `degP`**:
`P(degP v ≥ E[degP v] + λ) ≤ exp(-λ² / (2 (2 a r² K D² + r K λ)))`. -/
theorem degP_tail (ha : 0 ≤ a) (hD : 0 ≤ D) (r : ℕ) (hr : 1 ≤ r) (huni : IsUniform A r)
    (hdeg : ∀ u, (degree A u : ℝ) ≤ D) (K : ℝ) (hK : 0 < K)
    (hcod : ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K) (v : V) (lam : ℝ) (hlam : 0 < lam) :
    pProb (roundP A a D) (fun ω => lam ≤ (degP A ω v : ℝ) -
        pE (roundP A a D) (fun ω => (degP A ω v : ℝ))) ≤
      Real.exp (-(lam ^ 2 / (2 * (2 * a * r ^ 2 * K * D ^ 2 + r * K * lam)))) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have h := pE_upper_tail (roundP A a D) (roundP_isPMF A ha D) (fun ω => (degP A ω v : ℝ))
    (cDeg A v) (qTrue A a D) (fun _ => {true}) (r * K) (by positivity)
    (fun i => ⟨cDeg_nonneg A v i, cDeg_le A r huni hr K hK.le hcod v i⟩) (degP_coordGap A v)
    (by
      intro i ω b b' hb hb'
      simp only [mem_singleton] at hb hb'
      rw [Bool.eq_false_iff.mpr hb, Bool.eq_false_iff.mpr hb'])
    (fun i => by simp [roundP]) lam hlam
  refine h.trans (Real.exp_le_exp.mpr (neg_le_neg ?_))
  have hV := sum_q_cDeg_sq_le A D ha hD r huni hr hdeg K hK.le hcod v
  have hV0 : 0 ≤ ∑ i, qTrue A a D i * cDeg A v i ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (qTrue_mem A ha D i).1 (sq_nonneg _)
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  nlinarith

end Tail

end Pseudorandom.Nibble
