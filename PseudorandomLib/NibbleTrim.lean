/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.NibbleIterate

/-! # The nibble with trimming

A variant of the process of `NibbleIterate.lean`: after every round, all edges at vertices
whose degree exceeds the next degree bound are deleted ("trimming"). The state is then good
automatically, and the failure probability of a round for a fixed edge only involves the `r`
vertices of that edge. This avoids any union bound over all vertices, which is what makes the
analysis work when the codegrees are only a small constant fraction of the degrees
(Pippenger's theorem).
-/

@[expose] public section

namespace Pseudorandom.Nibble

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Delete all edges at vertices of degree larger than `D'`. -/
noncomputable def trim (A : Finset (Finset V)) (D' : ℝ) : Finset (Finset V) :=
  A.filter (fun e => ∀ v ∈ e, (degree A v : ℝ) ≤ D')

theorem trim_subset (A : Finset (Finset V)) (D' : ℝ) : trim A D' ⊆ A := filter_subset _ _

theorem trim_good (A : Finset (Finset V)) {D' : ℝ} (hD' : 0 ≤ D') : Good D' (trim A D') := by
  intro v
  by_cases hv : (degree A v : ℝ) ≤ D'
  · exact le_trans (by exact_mod_cast degree_mono (trim_subset A D') v) hv
  · have : degree (trim A D') v = 0 := by
      unfold degree
      rw [card_eq_zero, filter_eq_empty_iff]
      intro e he hve
      exact hv ((mem_filter.mp he).2 v hve)
    rw [this]; simpa using hD'

section Round

variable (A : Finset (Finset V)) {a D : ℝ}

/-- One vertex becomes overloaded only with small probability. -/
theorem round_vertex_bad_le (ha : 0 ≤ a) (hD : 0 ≤ D) (r : ℕ) (hr : 1 ≤ r)
    (huni : IsUniform A r) (hdeg : ∀ u, (degree A u : ℝ) ≤ D) (K : ℝ) (hK : 0 < K)
    (hcod : ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K) (lam D' : ℝ) (hlam : 0 < lam)
    (hD' : D * Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) + lam ≤ D')
    (v : V) :
    pProb (roundP A a D) (fun ω => D' < degree (alive A ω) v) ≤
      Real.exp (-(lam ^ 2 / (2 * (2 * a * r ^ 2 * K * D ^ 2 + r * K * lam)))) := by
  have hP := roundP_isPMF A ha D
  refine le_trans (pProb_mono hP (T := fun ω =>
    lam ≤ (degP A ω v : ℝ) - pE (roundP A a D) (fun ω => (degP A ω v : ℝ))) ?_)
    (degP_tail A D ha hD r hr huni hdeg K hK hcod v lam hlam)
  intro ω hv
  have hEle := pE_degP_le A D ha r huni hdeg K hK.le hcod v
  have h1 : (degree (alive A ω) v : ℝ) ≤ degP A ω v := by
    exact_mod_cast degree_alive_le_degP A ω v
  linarith

/-- A fixed edge survives a round including trimming with probability `≥ e^{-a r D} - β`. -/
theorem round_trim_ge (ha : 0 ≤ a) (hD : 0 ≤ D) (r : ℕ) (hr : 1 ≤ r)
    (huni : IsUniform A r) (hdeg : ∀ u, (degree A u : ℝ) ≤ D) (K : ℝ) (hK : 0 < K)
    (hcod : ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K) (lam D' : ℝ) (hlam : 0 < lam)
    (hD' : D * Real.exp (-(a * (((r - 1 : ℕ) : ℝ) * D - ((r - 1 : ℕ) : ℝ) ^ 2 * K))) + lam ≤ D')
    (hD'0 : 0 ≤ D') {e : Finset V} (he : e ∈ A) :
    Real.exp (-(a * (r * D))) -
        r * Real.exp (-(lam ^ 2 / (2 * (2 * a * r ^ 2 * K * D ^ 2 + r * K * lam)))) ≤
      pProb (roundP A a D) (fun ω => e ∈ trim (alive A ω) D' ∧
        Good D' (trim (alive A ω) D')) := by
  classical
  have hP := roundP_isPMF A ha D
  have h1 := prob_alive_ge A D ha he r (huni e he) (fun u _ => hdeg u)
  have h2 : pProb (roundP A a D) (fun ω => ∃ v ∈ e, D' < degree (alive A ω) v) ≤
      r * Real.exp (-(lam ^ 2 / (2 * (2 * a * r ^ 2 * K * D ^ 2 + r * K * lam)))) := by
    refine (pProb_exists_le hP e _).trans ?_
    refine (sum_le_sum fun v _ => round_vertex_bad_le A ha hD r hr huni hdeg K hK hcod lam D'
      hlam hD' v).trans (le_of_eq ?_)
    rw [sum_const, nsmul_eq_mul, huni e he]
  have h3 : pProb (roundP A a D) (fun ω => e ∈ alive A ω) ≤
      pProb (roundP A a D) (fun ω => e ∈ trim (alive A ω) D' ∧
        Good D' (trim (alive A ω) D')) +
      pProb (roundP A a D) (fun ω => ∃ v ∈ e, D' < degree (alive A ω) v) := by
    refine (pProb_mono hP (T := fun ω => (e ∈ trim (alive A ω) D' ∧
      Good D' (trim (alive A ω) D')) ∨ ∃ v ∈ e, D' < degree (alive A ω) v) ?_).trans
      (pProb_or_le hP _ _)
    intro ω h
    by_cases hg : ∀ v ∈ e, (degree (alive A ω) v : ℝ) ≤ D'
    · exact Or.inl ⟨mem_filter.mpr ⟨h, hg⟩, trim_good _ hD'0⟩
    · push_neg at hg; exact Or.inr hg
  linarith

end Round

/-- The state after a round with coins `ω`, followed by trimming at level `D'`. -/
noncomputable def nextT (D' : ℝ) (S : State V) (ω : Coin V → Bool) : State V :=
  (trim (alive S.1 ω) D', S.2 ∪ acc S.1 ω)

theorem inv_nextT {H : Finset (Finset V)} {S : State V} {D' : ℝ} (hS : Inv H S)
    (ω : Coin V → Bool) : Inv H (nextT D' S ω) := by
  obtain ⟨h1, h2, h3, h4⟩ := inv_next hS ω
  refine ⟨(trim_subset _ _).trans h1, h2, h3, fun f hf g hg => h4 f (trim_subset _ _ hf) g hg⟩

open Classical in
/-- One step of the process, as a transformation of probability mass functions on states. -/
noncomputable def stepT (a D D' : ℝ) (μ : State V → ℝ) : State V → ℝ := fun S' =>
  ∑ S, μ S * (if Good D S.1 then
    pE (roundP S.1 a D) (fun ω => if nextT D' S ω = S' then 1 else 0)
    else if S = S' then 1 else 0)

open Classical in
/-- The law of the state after `t` rounds. -/
noncomputable def procT (H : Finset (Finset V)) (a D : ℕ → ℝ) : ℕ → State V → ℝ
  | 0 => fun S => if S = (H, ∅) then 1 else 0
  | t + 1 => stepT (a t) (D t) (D (t + 1)) (procT H a D t)

open Classical in
theorem stepT_sum (a D D' : ℝ) (μ : State V → ℝ) (g : State V → ℝ) :
    ∑ S', stepT a D D' μ S' * g S' =
      ∑ S, μ S * (if Good D S.1 then pE (roundP S.1 a D) (fun ω => g (nextT D' S ω)) else g S) := by
  unfold stepT
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun S _ => ?_
  simp_rw [mul_assoc]
  rw [← mul_sum]
  congr 1
  split_ifs with hg
  · have : ∀ S', pE (roundP S.1 a D) (fun ω => if nextT D' S ω = S' then (1 : ℝ) else 0) * g S' =
        pE (roundP S.1 a D) (fun ω => (if nextT D' S ω = S' then (1 : ℝ) else 0) * g S') := by
      intro S'
      rw [mul_comm, ← pE_const_mul]
      congr 1; funext ω; ring
    simp_rw [this]
    rw [← pE_sum]
    congr 1; funext ω
    simp
  · simp

theorem stepT_nonneg (a D D' : ℝ) (ha : 0 ≤ a) {μ : State V → ℝ} (hμ : ∀ S, 0 ≤ μ S) (S' : State V) :
    0 ≤ stepT a D D' μ S' := by
  classical
  unfold stepT
  refine sum_nonneg fun S _ => mul_nonneg (hμ S) ?_
  split_ifs
  · exact pE_nonneg (roundP_isPMF S.1 ha D) fun ω => by split_ifs <;> norm_num
  · norm_num
  · norm_num

/-- The hypotheses under which the trimmed process is analysed. -/
structure ParamsT (H : Finset (Finset V)) (r : ℕ) (K : ℝ) (a D lam : ℕ → ℝ) : Prop where
  hr : 1 ≤ r
  huni : IsUniform H r
  hK : 0 < K
  hcod : ∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ K
  ha : ∀ t, 0 ≤ a t
  hD : ∀ t, 0 ≤ D t
  hlam : ∀ t, 0 < lam t
  hstep : ∀ t, D t * Real.exp (-(a t * (((r - 1 : ℕ) : ℝ) * D t - ((r - 1 : ℕ) : ℝ) ^ 2 * K)))
    + lam t ≤ D (t + 1)
  hdeg0 : ∀ v, (degree H v : ℝ) ≤ D 0

/-- The failure probability of a round for a fixed edge. -/
noncomputable def betaT (r : ℕ) (K : ℝ) (a D lam : ℕ → ℝ) (t : ℕ) : ℝ :=
  r * Real.exp (-(lam t ^ 2 / (2 * (2 * a t * r ^ 2 * K * D t ^ 2 + r * K * lam t))))

/-- Lower bound for the probability that a fixed edge is alive. -/
noncomputable def LseqT (r : ℕ) (K : ℝ) (a D lam : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => LseqT r K a D lam t * Real.exp (-(a t * (r * D t))) - betaT r K a D lam t

variable {H : Finset (Finset V)} {r : ℕ} {K : ℝ} {a D lam : ℕ → ℝ}

omit [Fintype V] [DecidableEq V] in
theorem betaT_nonneg (t : ℕ) : 0 ≤ betaT r K a D lam t := by
  unfold betaT; positivity

theorem procT_nonneg (P : ParamsT H r K a D lam) : ∀ t S, 0 ≤ procT H a D t S
  | 0, S => by simp only [procT]; split_ifs <;> norm_num
  | t + 1, S => stepT_nonneg _ _ _ (P.ha t) (procT_nonneg P t) S

theorem procT_sum (P : ParamsT H r K a D lam) : ∀ t, ∑ S, procT H a D t S = 1
  | 0 => by simp [procT]
  | t + 1 => by
    classical
    have h := stepT_sum (a t) (D t) (D (t + 1)) (procT H a D t) (fun _ => 1)
    simp only [mul_one] at h
    simp only [procT]
    rw [h]
    calc _ = ∑ S, procT H a D t S := by
          refine sum_congr rfl fun S _ => ?_
          split_ifs
          · rw [pE_const (roundP_isPMF _ (P.ha t) _), mul_one]
          · rw [mul_one]
      _ = 1 := procT_sum P t

theorem procT_inv (P : ParamsT H r K a D lam) : ∀ t S, procT H a D t S ≠ 0 → Inv H S
  | 0, S => by
    intro h
    simp only [procT] at h
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
    simp only [procT, stepT]
    refine sum_eq_zero fun S _ => ?_
    by_cases hμ : procT H a D t S = 0
    · rw [hμ, zero_mul]
    · have hS := procT_inv P t S hμ
      split_ifs with hg hSS
      · have : (fun ω => if nextT (D (t + 1)) S ω = S' then (1 : ℝ) else 0) = fun _ => 0 := by
          funext ω
          rw [if_neg]
          intro heq
          exact hinv (heq ▸ inv_nextT hS ω)
        rw [this, pE_const (roundP_isPMF _ (P.ha t) _), mul_zero]
      · exact absurd (hSS ▸ hS) hinv
      · rw [mul_zero]

omit [Fintype V] in
theorem ParamsT.uni_of_sub (P : ParamsT H r K a D lam) {A : Finset (Finset V)} (h : A ⊆ H) :
    IsUniform A r := fun e he => P.huni e (h he)

omit [Fintype V] in
theorem ParamsT.cod_of_sub (P : ParamsT H r K a D lam) {A : Finset (Finset V)} (h : A ⊆ H) :
    ∀ u w, u ≠ w → (codegree A u w : ℝ) ≤ K := fun u w huw =>
  le_trans (by exact_mod_cast codegree_mono h u w) (P.hcod u w huw)

open Classical in
/-- The probability that a fixed edge is alive in a good state after `t` rounds. -/
theorem alive_geT (P : ParamsT H r K a D lam) {e : Finset V} (he : e ∈ H) : ∀ t,
    LseqT r K a D lam t ≤
      ∑ S, procT H a D t S * (if e ∈ S.1 ∧ Good (D t) S.1 then 1 else 0)
  | 0 => by
    simp only [procT, LseqT]
    rw [sum_eq_single (H, ∅)]
    · simp only [if_true, one_mul]
      rw [if_pos ⟨he, P.hdeg0⟩]
    · intro S _ hS; rw [if_neg hS, zero_mul]
    · intro h; exact absurd (mem_univ _) h
  | t + 1 => by
    have ih := alive_geT P he t
    simp only [procT]
    rw [stepT_sum]
    have hper : ∀ S, procT H a D t S *
        (if e ∈ S.1 ∧ Good (D t) S.1 then 1 else 0) * Real.exp (-(a t * (r * D t))) -
          procT H a D t S * betaT r K a D lam t ≤
        procT H a D t S * (if Good (D t) S.1 then pE (roundP S.1 (a t) (D t))
          (fun ω => if e ∈ (nextT (D (t + 1)) S ω).1 ∧ Good (D (t + 1)) (nextT (D (t + 1)) S ω).1 then 1 else 0)
          else if e ∈ S.1 ∧ Good (D (t + 1)) S.1 then 1 else 0) := by
      intro S
      have hμ0 := procT_nonneg P t S
      have hb := betaT_nonneg (r := r) (K := K) (a := a) (D := D) (lam := lam) t
      by_cases hμ : procT H a D t S = 0
      · simp [hμ]
      have hS := procT_inv P t S hμ
      rw [mul_assoc, ← mul_sub]
      apply mul_le_mul_of_nonneg_left _ hμ0
      by_cases hg : Good (D t) S.1
      · rw [if_pos hg]
        by_cases heS : e ∈ S.1
        · rw [if_pos ⟨heS, hg⟩, one_mul]
          have hround := round_trim_ge S.1 (P.ha t) (P.hD t) r P.hr (P.uni_of_sub hS.1)
            hg K P.hK (P.cod_of_sub hS.1) (lam t) (D (t + 1)) (P.hlam t) (P.hstep t)
            (P.hD (t + 1)) heS
          rw [← pProb_eq_pE _ _ (fun ω h => if_pos h) (fun ω h => if_neg h)]
          exact hround
        · rw [if_neg (fun h => heS h.1), zero_mul, zero_sub]
          have := pE_nonneg (roundP_isPMF S.1 (P.ha t) (D t))
            (f := fun ω => if e ∈ (nextT (D (t + 1)) S ω).1 ∧ Good (D (t + 1)) (nextT (D (t + 1)) S ω).1 then (1 : ℝ) else 0)
            (fun ω => by split_ifs <;> norm_num)
          linarith
      · rw [if_neg hg, if_neg (show ¬(e ∈ S.1 ∧ Good (D t) S.1) from fun h => hg h.2), zero_mul,
          zero_sub]
        have : (0 : ℝ) ≤ if e ∈ S.1 ∧ Good (D (t + 1)) S.1 then 1 else 0 := by
          split_ifs <;> norm_num
        linarith
    calc LseqT r K a D lam (t + 1)
        = LseqT r K a D lam t * Real.exp (-(a t * (r * D t))) - betaT r K a D lam t := rfl
      _ ≤ (∑ S, procT H a D t S * (if e ∈ S.1 ∧ Good (D t) S.1 then 1 else 0)) *
            Real.exp (-(a t * (r * D t))) - betaT r K a D lam t := by
          gcongr
      _ = ∑ S, (procT H a D t S * (if e ∈ S.1 ∧ Good (D t) S.1 then 1 else 0) *
            Real.exp (-(a t * (r * D t))) - procT H a D t S * betaT r K a D lam t) := by
          rw [sum_sub_distrib, ← sum_mul, ← sum_mul, procT_sum P t, one_mul]
      _ ≤ _ := sum_le_sum fun S _ => hper S

open Classical in
/-- The probability that a fixed edge is in the matching after `T` rounds. -/
theorem inM_geT (P : ParamsT H r K a D lam) {e : Finset V} (he : e ∈ H) : ∀ T,
    ∑ t ∈ range T, LseqT r K a D lam t * ((1 - Real.exp (-a t)) * Real.exp (-(a t * (r * D t))))
      ≤ ∑ S, procT H a D T S * (if e ∈ S.2 then 1 else 0)
  | 0 => by
    simp only [range_zero, sum_empty, procT]
    exact sum_nonneg fun S _ => by split_ifs <;> norm_num
  | T + 1 => by
    have ih := inM_geT P he T
    have hal := alive_geT P he T
    have hne : e.Nonempty := by
      rw [← card_pos, P.huni e he]; exact P.hr
    set acc0 := (1 - Real.exp (-a T)) * Real.exp (-(a T * (r * D T))) with hacc0
    have hacc_nonneg : 0 ≤ acc0 := by
      have : Real.exp (-a T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [P.ha T])
      have : 0 ≤ 1 - Real.exp (-a T) := by linarith
      positivity
    simp only [procT]
    rw [stepT_sum, sum_range_succ]
    have hper : ∀ S, procT H a D T S * (if e ∈ S.2 then 1 else 0) +
        procT H a D T S * (if e ∈ S.1 ∧ Good (D T) S.1 then 1 else 0) * acc0 ≤
        procT H a D T S * (if Good (D T) S.1 then pE (roundP S.1 (a T) (D T))
          (fun ω => if e ∈ (nextT (D (T + 1)) S ω).2 then 1 else 0)
          else if e ∈ S.2 then 1 else 0) := by
      intro S
      have hμ0 := procT_nonneg P T S
      by_cases hμ : procT H a D T S = 0
      · simp [hμ]
      have hS := procT_inv P T S hμ
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
          have : (fun ω => if e ∈ (nextT (D (T + 1)) S ω).2 then (1 : ℝ) else 0) = fun _ => 1 := by
            funext ω; rw [if_pos]; simp [nextT, heM]
          rw [this, pE_const (roundP_isPMF _ (P.ha T) _)]
        · rw [if_neg heM, zero_add]
          have heq : (fun ω => if e ∈ (nextT (D (T + 1)) S ω).2 then (1 : ℝ) else 0) =
              fun ω => if e ∈ acc S.1 ω then 1 else 0 := by
            funext ω
            simp [nextT, heM]
          rw [heq, ← pProb_eq_pE _ _ (fun ω h => if_pos h) (fun ω h => if_neg h)]
          by_cases heA : e ∈ S.1
          · rw [if_pos ⟨heA, hg⟩, one_mul]
            exact prob_acc_ge S.1 (D T) (P.ha T) heA hne r (P.huni e he) (fun u _ => hg u)
          · rw [if_neg (fun h => heA h.1), zero_mul]
            exact pProb_nonneg (roundP_isPMF _ (P.ha T) _) _
      · rw [if_neg hg, if_neg (show ¬(e ∈ S.1 ∧ Good (D T) S.1) from fun h => hg h.2), zero_mul,
          add_zero]
    calc _ ≤ (∑ S, procT H a D T S * (if e ∈ S.2 then 1 else 0)) +
          (∑ S, procT H a D T S * (if e ∈ S.1 ∧ Good (D T) S.1 then 1 else 0)) * acc0 := by
          gcongr
      _ = ∑ S, (procT H a D T S * (if e ∈ S.2 then 1 else 0) +
          procT H a D T S * (if e ∈ S.1 ∧ Good (D T) S.1 then 1 else 0) * acc0) := by
          rw [sum_add_distrib, sum_mul]
      _ ≤ _ := sum_le_sum fun S _ => hper S

/-! ## The output: a random matching -/

/-- The law of the matching after `T` rounds. -/
noncomputable def outMT (H : Finset (Finset V)) (a D : ℕ → ℝ) (T : ℕ) :
    Finset (Finset V) → ℝ :=
  fun M => ∑ A : Finset (Finset V), procT H a D T (A, M)

theorem outMT_nonneg (P : ParamsT H r K a D lam) (T : ℕ) (M : Finset (Finset V)) :
    0 ≤ outMT H a D T M :=
  sum_nonneg fun _ _ => procT_nonneg P T _

theorem outMT_sum (P : ParamsT H r K a D lam) (T : ℕ) : ∑ M, outMT H a D T M = 1 := by
  unfold outMT
  rw [sum_comm, ← procT_sum P T, ← Fintype.sum_prod_type']

theorem outMT_support (P : ParamsT H r K a D lam) (T : ℕ) (M : Finset (Finset V))
    (h : outMT H a D T M ≠ 0) : IsMatching M ∧ M ⊆ H := by
  unfold outMT at h
  obtain ⟨_, _, hA⟩ := exists_ne_zero_of_sum_ne_zero h
  have := procT_inv P T _ hA
  exact ⟨this.2.2.1, this.2.1⟩

open Classical in
theorem outMT_marginal (P : ParamsT H r K a D lam) (T : ℕ) {e : Finset V} (he : e ∈ H) :
    ∑ t ∈ range T, LseqT r K a D lam t * ((1 - Real.exp (-a t)) * Real.exp (-(a t * (r * D t))))
      ≤ ∑ M, outMT H a D T M * (if e ∈ M then 1 else 0) := by
  refine (inM_geT P he T).trans (le_of_eq ?_)
  unfold outMT
  simp_rw [sum_mul]
  rw [sum_comm, ← Fintype.sum_prod_type']

end Pseudorandom.Nibble
