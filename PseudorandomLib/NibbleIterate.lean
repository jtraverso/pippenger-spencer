/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.NibbleDegree

/-! # Iterating the nibble

We first summarise one round on a *good* state (all degrees at most `D`): an alive edge is
accepted with probability at least `(1 - e^{-a}) e^{-a r D}`, and it stays alive while all new
degrees stay below `D'` with probability at least `e^{-a r D} - β`.

Then we run the rounds one after the other. The state of the process is a pair `(A, M)` of
alive edges and the matching built so far, and the law of the state after `t` rounds is a
probability mass function `proc H a D t` on the finite type of states. If a state is not good,
the process simply stops there.
-/

@[expose] public section

namespace Pseudorandom.Nibble

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## One round on a good state -/

section Round

variable (A : Finset (Finset V)) {a D : ℝ}

/-- Union bound for the new degrees. -/
theorem round_bad_le (ha : 0 ≤ a) (hD : 0 ≤ D) (r : ℕ) (hr : 1 ≤ r) (huni : IsUniform A r)
    (hdeg : ∀ u, (degree A u : ℝ) ≤ D) (K : ℝ) (hK : 0 < K)
    (hcod : ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K) (lam D' : ℝ) (hlam : 0 < lam)
    (hD' : D * Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) + lam ≤ D')
    (U : Finset V) (hU : ∀ e ∈ A, e ⊆ U) :
    pProb (roundP A a D) (fun ω => ∃ v, D' < degree (alive A ω) v) ≤
      U.card * Real.exp (-(lam ^ 2 / (2 * (2 * a * r ^ 2 * K * D ^ 2 + r * K * lam)))) := by
  have hP := roundP_isPMF A ha D
  have hsub : ∀ ω, (∃ v, D' < degree (alive A ω) v) →
      ∃ v ∈ U, lam ≤ (degP A ω v : ℝ) - pE (roundP A a D) (fun ω => (degP A ω v : ℝ)) := by
    rintro ω ⟨v, hv⟩
    have hEle := pE_degP_le A D ha r huni hdeg K hK.le hcod v
    have h1 : (degree (alive A ω) v : ℝ) ≤ degP A ω v := by
      exact_mod_cast degree_alive_le_degP A ω v
    have hD'pos : 0 < D' := by
      have : 0 ≤ D * Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) :=
        mul_nonneg hD (Real.exp_pos _).le
      linarith
    have hvU : v ∈ U := by
      have hpos : 0 < degree (alive A ω) v := by
        have : (0 : ℝ) < degree (alive A ω) v := lt_trans hD'pos hv
        exact_mod_cast this
      unfold degree at hpos
      obtain ⟨e, he⟩ := card_pos.mp hpos
      rw [mem_filter] at he
      exact hU e (alive_subset A ω he.1) he.2
    exact ⟨v, hvU, by linarith⟩
  calc _ ≤ pProb (roundP A a D) (fun ω => ∃ v ∈ U,
        lam ≤ (degP A ω v : ℝ) - pE (roundP A a D) (fun ω => (degP A ω v : ℝ))) :=
        pProb_mono hP hsub
    _ ≤ ∑ v ∈ U, pProb (roundP A a D) (fun ω =>
        lam ≤ (degP A ω v : ℝ) - pE (roundP A a D) (fun ω => (degP A ω v : ℝ))) :=
        pProb_exists_le hP U _
    _ ≤ ∑ v ∈ U, Real.exp (-(lam ^ 2 / (2 * (2 * a * r ^ 2 * K * D ^ 2 + r * K * lam)))) :=
        sum_le_sum fun v _ => degP_tail A D ha hD r hr huni hdeg K hK hcod v lam hlam
    _ = _ := by rw [sum_const, nsmul_eq_mul]

/-- An alive edge stays alive and the state stays good with probability `≥ e^{-a r D} - β`. -/
theorem round_alive_good_ge (ha : 0 ≤ a) (hD : 0 ≤ D) (r : ℕ) (hr : 1 ≤ r)
    (huni : IsUniform A r) (hdeg : ∀ u, (degree A u : ℝ) ≤ D) (K : ℝ) (hK : 0 < K)
    (hcod : ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K) (lam D' : ℝ) (hlam : 0 < lam)
    (hD' : D * Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) + lam ≤ D')
    (U : Finset V) (hU : ∀ e ∈ A, e ⊆ U) {e : Finset V} (he : e ∈ A) :
    Real.exp (-(a * (r * D))) -
        U.card * Real.exp (-(lam ^ 2 / (2 * (2 * a * r ^ 2 * K * D ^ 2 + r * K * lam)))) ≤
      pProb (roundP A a D) (fun ω => e ∈ alive A ω ∧ ∀ v, (degree (alive A ω) v : ℝ) ≤ D') := by
  have hP := roundP_isPMF A ha D
  have h1 := prob_alive_ge A D ha he r (huni e he) (fun u _ => hdeg u)
  have h2 := round_bad_le A ha hD r hr huni hdeg K hK hcod lam D' hlam hD' U hU
  have h3 : pProb (roundP A a D) (fun ω => e ∈ alive A ω) ≤
      pProb (roundP A a D) (fun ω => e ∈ alive A ω ∧ ∀ v, (degree (alive A ω) v : ℝ) ≤ D') +
      pProb (roundP A a D) (fun ω => ∃ v, D' < degree (alive A ω) v) := by
    refine (pProb_mono hP (T := fun ω => (e ∈ alive A ω ∧ ∀ v, (degree (alive A ω) v : ℝ) ≤ D') ∨
      ∃ v, D' < degree (alive A ω) v) ?_).trans (pProb_or_le hP _ _)
    intro ω h
    by_cases hg : ∀ v, (degree (alive A ω) v : ℝ) ≤ D'
    · exact Or.inl ⟨h, hg⟩
    · push_neg at hg; exact Or.inr hg
  linarith

end Round

/-! ## The process -/

/-- States: alive edges and the matching built so far. -/
abbrev State (V : Type*) := Finset (Finset V) × Finset (Finset V)

/-- A state is good if all degrees are at most `D`. -/
def Good (D : ℝ) (A : Finset (Finset V)) : Prop := ∀ v, (degree A v : ℝ) ≤ D

/-- The state after a round with coins `ω`. -/
def next (S : State V) (ω : Coin V → Bool) : State V := (alive S.1 ω, S.2 ∪ acc S.1 ω)

/-- The invariant of the process. -/
def Inv (H : Finset (Finset V)) (S : State V) : Prop :=
  S.1 ⊆ H ∧ S.2 ⊆ H ∧ IsMatching S.2 ∧ ∀ f ∈ S.1, ∀ g ∈ S.2, Disjoint f g

open Classical in
/-- One step of the process, as a transformation of probability mass functions on states. -/
noncomputable def step (a D : ℝ) (μ : State V → ℝ) : State V → ℝ := fun S' =>
  ∑ S, μ S * (if Good D S.1 then
    pE (roundP S.1 a D) (fun ω => if next S ω = S' then 1 else 0)
    else if S = S' then 1 else 0)

open Classical in
/-- The law of the state after `t` rounds. -/
noncomputable def proc (H : Finset (Finset V)) (a D : ℕ → ℝ) : ℕ → State V → ℝ
  | 0 => fun S => if S = (H, ∅) then 1 else 0
  | t + 1 => step (a t) (D t) (proc H a D t)

open Classical in
theorem step_sum (a D : ℝ) (μ : State V → ℝ) (g : State V → ℝ) :
    ∑ S', step a D μ S' * g S' =
      ∑ S, μ S * (if Good D S.1 then pE (roundP S.1 a D) (fun ω => g (next S ω)) else g S) := by
  unfold step
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun S _ => ?_
  simp_rw [mul_assoc]
  rw [← mul_sum]
  congr 1
  split_ifs with hg
  · have : ∀ S', pE (roundP S.1 a D) (fun ω => if next S ω = S' then (1 : ℝ) else 0) * g S' =
        pE (roundP S.1 a D) (fun ω => (if next S ω = S' then (1 : ℝ) else 0) * g S') := by
      intro S'
      rw [mul_comm, ← pE_const_mul]
      congr 1; funext ω; ring
    simp_rw [this]
    rw [← pE_sum]
    congr 1; funext ω
    simp
  · simp

theorem step_nonneg (a D : ℝ) (ha : 0 ≤ a) {μ : State V → ℝ} (hμ : ∀ S, 0 ≤ μ S) (S' : State V) :
    0 ≤ step a D μ S' := by
  classical
  unfold step
  refine sum_nonneg fun S _ => mul_nonneg (hμ S) ?_
  split_ifs
  · exact pE_nonneg (roundP_isPMF S.1 ha D) fun ω => by split_ifs <;> norm_num
  · norm_num
  · norm_num

theorem inv_next {H : Finset (Finset V)} {S : State V} (hS : Inv H S) (ω : Coin V → Bool) :
    Inv H (next S ω) := by
  obtain ⟨h1, h2, h3, h4⟩ := hS
  refine ⟨(alive_subset _ ω).trans h1, union_subset h2 ((acc_subset _ ω).trans h1), ?_, ?_⟩
  · intro e he f hf hef
    simp only [next] at he hf
    rw [mem_union] at he hf
    rcases he with he | he <;> rcases hf with hf | hf
    · exact h3 e he f hf hef
    · exact (h4 f (acc_subset _ ω hf) e he).symm
    · exact h4 e (acc_subset _ ω he) f hf
    · exact acc_isMatching _ ω e he f hf hef
  · intro f hf g hg
    simp only [next] at hf hg
    rw [mem_union] at hg
    rcases hg with hg | hg
    · exact h4 f (alive_subset _ ω hf) g hg
    · exact disjoint_alive_acc _ ω f hf g hg

/-! ## Properties of the process -/

/-- The hypotheses under which the process is analysed. -/
structure Params (H : Finset (Finset V)) (r : ℕ) (K : ℝ) (U : Finset V) (a D lam : ℕ → ℝ) :
    Prop where
  hr : 1 ≤ r
  huni : IsUniform H r
  hK : 0 < K
  hcod : ∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ K
  hU : ∀ e ∈ H, e ⊆ U
  ha : ∀ t, 0 ≤ a t
  hD : ∀ t, 0 ≤ D t
  hlam : ∀ t, 0 < lam t
  hstep : ∀ t, D t * Real.exp (-(a t * (((r - 1 : ℕ) : ℝ) * D t - ((r - 1 : ℕ) : ℝ) ^ 2 * K)))
    + lam t ≤ D (t + 1)
  hdeg0 : ∀ v, (degree H v : ℝ) ≤ D 0

/-- The failure probability of a round. -/
noncomputable def beta (r : ℕ) (K : ℝ) (U : Finset V) (a D lam : ℕ → ℝ) (t : ℕ) : ℝ :=
  U.card * Real.exp (-(lam t ^ 2 / (2 * (2 * a t * r ^ 2 * K * D t ^ 2 + r * K * lam t))))

/-- Lower bound for the probability that a fixed edge is alive (and the state good). -/
noncomputable def Lseq (r : ℕ) (K : ℝ) (U : Finset V) (a D lam : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => Lseq r K U a D lam t * Real.exp (-(a t * (r * D t))) - beta r K U a D lam t

variable {H : Finset (Finset V)} {r : ℕ} {K : ℝ} {U : Finset V} {a D lam : ℕ → ℝ}

omit [Fintype V] [DecidableEq V] in
theorem beta_nonneg (t : ℕ) : 0 ≤ beta r K U a D lam t := by
  unfold beta; positivity

theorem proc_nonneg (P : Params H r K U a D lam) : ∀ t S, 0 ≤ proc H a D t S
  | 0, S => by simp only [proc]; split_ifs <;> norm_num
  | t + 1, S => step_nonneg _ _ (P.ha t) (proc_nonneg P t) S

theorem proc_sum (P : Params H r K U a D lam) : ∀ t, ∑ S, proc H a D t S = 1
  | 0 => by simp [proc]
  | t + 1 => by
    classical
    have h := step_sum (a t) (D t) (proc H a D t) (fun _ => 1)
    simp only [mul_one] at h
    simp only [proc]
    rw [h]
    calc _ = ∑ S, proc H a D t S := by
          refine sum_congr rfl fun S _ => ?_
          split_ifs
          · rw [pE_const (roundP_isPMF _ (P.ha t) _), mul_one]
          · rw [mul_one]
      _ = 1 := proc_sum P t

theorem proc_inv (P : Params H r K U a D lam) : ∀ t S, proc H a D t S ≠ 0 → Inv H S
  | 0, S => by
    intro h
    simp only [proc] at h
    split_ifs at h with hS
    · subst hS
      refine ⟨subset_refl _, empty_subset _, ?_, ?_⟩
      · intro e he; simp at he
      · intro f _ g hg; simp at hg
    · exact absurd rfl h
  | t + 1, S' => by
    classical
    intro h
    by_contra hinv
    apply h
    simp only [proc, step]
    refine sum_eq_zero fun S _ => ?_
    by_cases hμ : proc H a D t S = 0
    · rw [hμ, zero_mul]
    · have hS := proc_inv P t S hμ
      split_ifs with hg hSS
      · have : (fun ω => if next S ω = S' then (1 : ℝ) else 0) = fun _ => 0 := by
          funext ω
          rw [if_neg]
          intro heq
          exact hinv (heq ▸ inv_next hS ω)
        rw [this, pE_const (roundP_isPMF _ (P.ha t) _), mul_zero]
      · exact absurd (hSS ▸ hS) hinv
      · rw [mul_zero]

omit [Fintype V] in
theorem Params.uni_of_sub (P : Params H r K U a D lam) {A : Finset (Finset V)} (h : A ⊆ H) :
    IsUniform A r := fun e he => P.huni e (h he)

omit [Fintype V] in
theorem Params.cod_of_sub (P : Params H r K U a D lam) {A : Finset (Finset V)} (h : A ⊆ H) :
    ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K := fun u w huw =>
  le_trans (by exact_mod_cast codegree_mono h u w) (P.hcod u w huw)

open Classical in
/-- The probability that a fixed edge is alive in a good state after `t` rounds. -/
theorem alive_ge (P : Params H r K U a D lam) {e : Finset V} (he : e ∈ H) : ∀ t,
    Lseq r K U a D lam t ≤
      ∑ S, proc H a D t S * (if e ∈ S.1 ∧ Good (D t) S.1 then 1 else 0)
  | 0 => by
    simp only [proc, Lseq]
    rw [sum_eq_single (H, ∅)]
    · simp only [if_true, one_mul]
      rw [if_pos ⟨he, P.hdeg0⟩]
    · intro S _ hS; rw [if_neg hS, zero_mul]
    · intro h; exact absurd (mem_univ _) h
  | t + 1 => by
    have ih := alive_ge P he t
    simp only [proc]
    rw [step_sum]
    have hper : ∀ S, proc H a D t S *
        (if e ∈ S.1 ∧ Good (D t) S.1 then 1 else 0) * Real.exp (-(a t * (r * D t))) -
          proc H a D t S * beta r K U a D lam t ≤
        proc H a D t S * (if Good (D t) S.1 then pE (roundP S.1 (a t) (D t))
          (fun ω => if e ∈ (next S ω).1 ∧ Good (D (t + 1)) (next S ω).1 then 1 else 0)
          else if e ∈ S.1 ∧ Good (D (t + 1)) S.1 then 1 else 0) := by
      intro S
      have hμ0 := proc_nonneg P t S
      have hb := beta_nonneg (r := r) (K := K) (U := U) (a := a) (D := D) (lam := lam) t
      by_cases hμ : proc H a D t S = 0
      · simp [hμ]
      have hS := proc_inv P t S hμ
      rw [mul_assoc, ← mul_sub]
      apply mul_le_mul_of_nonneg_left _ hμ0
      by_cases hg : Good (D t) S.1
      · rw [if_pos hg]
        by_cases heS : e ∈ S.1
        · rw [if_pos ⟨heS, hg⟩, one_mul]
          have hround := round_alive_good_ge S.1 (P.ha t) (P.hD t) r P.hr (P.uni_of_sub hS.1)
            hg K P.hK (P.cod_of_sub hS.1) (lam t) (D (t + 1)) (P.hlam t) (P.hstep t) U
            (fun f hf => P.hU f (hS.1 hf)) heS
          rw [← pProb_eq_pE _ _ (fun ω h => if_pos h) (fun ω h => if_neg h)]
          exact hround
        · rw [if_neg (fun h => heS h.1), zero_mul, zero_sub]
          have := pE_nonneg (roundP_isPMF S.1 (P.ha t) (D t))
            (f := fun ω => if e ∈ (next S ω).1 ∧ Good (D (t + 1)) (next S ω).1 then (1 : ℝ) else 0)
            (fun ω => by dsimp (config := { failIfUnchanged := false }) only; split_ifs <;> norm_num)
          linarith
      · rw [if_neg hg, if_neg (show ¬(e ∈ S.1 ∧ Good (D t) S.1) from fun h => hg h.2), zero_mul,
          zero_sub]
        have : (0 : ℝ) ≤ if e ∈ S.1 ∧ Good (D (t + 1)) S.1 then 1 else 0 := by
          split_ifs <;> norm_num
        linarith
    calc Lseq r K U a D lam (t + 1)
        = Lseq r K U a D lam t * Real.exp (-(a t * (r * D t))) - beta r K U a D lam t := rfl
      _ ≤ (∑ S, proc H a D t S * (if e ∈ S.1 ∧ Good (D t) S.1 then 1 else 0)) *
            Real.exp (-(a t * (r * D t))) - beta r K U a D lam t := by
          gcongr
      _ = ∑ S, (proc H a D t S * (if e ∈ S.1 ∧ Good (D t) S.1 then 1 else 0) *
            Real.exp (-(a t * (r * D t))) - proc H a D t S * beta r K U a D lam t) := by
          rw [sum_sub_distrib, ← sum_mul, ← sum_mul, proc_sum P t, one_mul]
      _ ≤ _ := sum_le_sum fun S _ => hper S

open Classical in
/-- The probability that a fixed edge is in the matching after `T` rounds. -/
theorem inM_ge (P : Params H r K U a D lam) {e : Finset V} (he : e ∈ H) : ∀ T,
    ∑ t ∈ range T, Lseq r K U a D lam t * ((1 - Real.exp (-a t)) * Real.exp (-(a t * (r * D t))))
      ≤ ∑ S, proc H a D T S * (if e ∈ S.2 then 1 else 0)
  | 0 => by
    simp only [range_zero, sum_empty, proc]
    exact sum_nonneg fun S _ => by split_ifs <;> norm_num
  | T + 1 => by
    have ih := inM_ge P he T
    have hal := alive_ge P he T
    have hne : e.Nonempty := by
      rw [← card_pos, P.huni e he]; exact P.hr
    set acc0 := (1 - Real.exp (-a T)) * Real.exp (-(a T * (r * D T))) with hacc0
    have hacc_nonneg : 0 ≤ acc0 := by
      have : Real.exp (-a T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [P.ha T])
      have : 0 ≤ 1 - Real.exp (-a T) := by linarith
      positivity
    simp only [proc]
    rw [step_sum, sum_range_succ]
    have hper : ∀ S, proc H a D T S * (if e ∈ S.2 then 1 else 0) +
        proc H a D T S * (if e ∈ S.1 ∧ Good (D T) S.1 then 1 else 0) * acc0 ≤
        proc H a D T S * (if Good (D T) S.1 then pE (roundP S.1 (a T) (D T))
          (fun ω => if e ∈ (next S ω).2 then 1 else 0)
          else if e ∈ S.2 then 1 else 0) := by
      intro S
      have hμ0 := proc_nonneg P T S
      by_cases hμ : proc H a D T S = 0
      · simp [hμ]
      have hS := proc_inv P T S hμ
      rw [mul_assoc, ← mul_add]
      apply mul_le_mul_of_nonneg_left _ hμ0
      by_cases hg : Good (D T) S.1
      · rw [if_pos hg]
        by_cases heM : e ∈ S.2
        · have heA : e ∉ S.1 := by
            intro heA
            have := hS.2.2.2 e heA e heM
            rw [disjoint_self_iff_empty] at this
            exact hne.ne_empty this
          rw [if_pos heM, if_neg (fun h => heA h.1), zero_mul, add_zero]
          have : (fun ω => if e ∈ (next S ω).2 then (1 : ℝ) else 0) = fun _ => 1 := by
            funext ω; rw [if_pos]; simp [next, heM]
          rw [this, pE_const (roundP_isPMF _ (P.ha T) _)]
        · rw [if_neg heM, zero_add]
          have heq : (fun ω => if e ∈ (next S ω).2 then (1 : ℝ) else 0) =
              fun ω => if e ∈ acc S.1 ω then 1 else 0 := by
            funext ω
            simp [next, heM]
          rw [heq, ← pProb_eq_pE _ _ (fun ω h => if_pos h) (fun ω h => if_neg h)]
          by_cases heA : e ∈ S.1
          · rw [if_pos ⟨heA, hg⟩, one_mul]
            exact prob_acc_ge S.1 (D T) (P.ha T) heA hne r (P.huni e he) (fun u _ => hg u)
          · rw [if_neg (fun h => heA h.1), zero_mul]
            exact pProb_nonneg (roundP_isPMF _ (P.ha T) _) _
      · rw [if_neg hg, if_neg (show ¬(e ∈ S.1 ∧ Good (D T) S.1) from fun h => hg h.2), zero_mul,
          add_zero]
    calc _ ≤ (∑ S, proc H a D T S * (if e ∈ S.2 then 1 else 0)) +
          (∑ S, proc H a D T S * (if e ∈ S.1 ∧ Good (D T) S.1 then 1 else 0)) * acc0 := by
          gcongr
      _ = ∑ S, (proc H a D T S * (if e ∈ S.2 then 1 else 0) +
          proc H a D T S * (if e ∈ S.1 ∧ Good (D T) S.1 then 1 else 0) * acc0) := by
          rw [sum_add_distrib, sum_mul]
      _ ≤ _ := sum_le_sum fun S _ => hper S

/-! ## The output: a random matching -/

/-- The law of the matching after `T` rounds. -/
noncomputable def outM (H : Finset (Finset V)) (a D : ℕ → ℝ) (T : ℕ) :
    Finset (Finset V) → ℝ :=
  fun M => ∑ A : Finset (Finset V), proc H a D T (A, M)

theorem outM_nonneg (P : Params H r K U a D lam) (T : ℕ) (M : Finset (Finset V)) :
    0 ≤ outM H a D T M :=
  sum_nonneg fun _ _ => proc_nonneg P T _

theorem outM_sum (P : Params H r K U a D lam) (T : ℕ) : ∑ M, outM H a D T M = 1 := by
  unfold outM
  rw [sum_comm, ← proc_sum P T, ← Fintype.sum_prod_type']

theorem outM_support (P : Params H r K U a D lam) (T : ℕ) (M : Finset (Finset V))
    (h : outM H a D T M ≠ 0) : IsMatching M ∧ M ⊆ H := by
  unfold outM at h
  obtain ⟨_, _, hA⟩ := exists_ne_zero_of_sum_ne_zero h
  have := proc_inv P T _ hA
  exact ⟨this.2.2.1, this.2.1⟩

open Classical in
theorem outM_marginal (P : Params H r K U a D lam) (T : ℕ) {e : Finset V} (he : e ∈ H) :
    ∑ t ∈ range T, Lseq r K U a D lam t * ((1 - Real.exp (-a t)) * Real.exp (-(a t * (r * D t))))
      ≤ ∑ M, outM H a D T M * (if e ∈ M then 1 else 0) := by
  refine (inM_ge P he T).trans (le_of_eq ?_)
  unfold outM
  simp_rw [sum_mul]
  rw [sum_comm, ← Fintype.sum_prod_type']

end Pseudorandom.Nibble
