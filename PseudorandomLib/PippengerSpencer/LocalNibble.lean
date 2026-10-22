/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.PippengerSpencer.Marginal
public import PseudorandomLib.PippengerSpencer.ProdProb

/-! # The trimmed nibble on a fixed product space

The trimmed nibble of `NibbleTrim.lean` is a Markov chain whose coin probabilities depend on the
current state (the killing coin of a vertex `v` has probability depending on `deg_A(v)`). Here
the same process is realised as a deterministic function `stateAt` of one fixed family of
independent coins: one coin with values in `Fin (N + 2)` per round and per `Coin V`. The killing
coin of `v` fires when its value exceeds `deg_A(v)` (a threshold coin), so its law does not
depend on the state. We prove that the law of `stateAt ω t` is `procT H as Ds t`.

This realisation is *local*: what happens near a vertex only depends on the coins near it
(`Locality.lean`), which is what the Lovász Local Lemma needs.
-/

@[expose] public section

namespace Pseudorandom.PS

open Finset Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## One round -/

/-- `tailP N a D m` is the probability that a threshold coin takes a value `≥ m`. -/
noncomputable def tailP (N : ℕ) (a D : ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => if m ≤ N then 1 - Real.exp (-(a * max 0 (D - m))) else 0

/-- The law of the coins of one round. -/
noncomputable def coinQ (N : ℕ) (a D : ℝ) : Coin V → Fin (N + 2) → ℝ
  | Sum.inl _ => fun k => if k.val = 0 then Real.exp (-a) else if k.val = 1 then
      1 - Real.exp (-a) else 0
  | Sum.inr _ => fun k => tailP N a D k.val - tailP N a D (k.val + 1)

/-- Reading the Boolean coins of the nibble round at state `A` off the threshold coins. -/
def decode (N : ℕ) (A : Finset (Finset V)) : Coin V → Fin (N + 2) → Bool
  | Sum.inl e => fun k => decide (e ∈ A ∧ k.val ≠ 0)
  | Sum.inr v => fun k => decide (degree A v < k.val)

theorem tailP_nonneg (N : ℕ) {a : ℝ} (ha : 0 ≤ a) (D : ℝ) (m : ℕ) : 0 ≤ tailP N a D m := by
  cases m with
  | zero => simp [tailP]
  | succ m =>
    simp only [tailP]
    split_ifs
    · have : Real.exp (-(a * max 0 (D - m))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [le_max_left 0 (D - m)])
      linarith
    · exact le_rfl

theorem tailP_anti (N : ℕ) {a : ℝ} (ha : 0 ≤ a) (D : ℝ) (m : ℕ) :
    tailP N a D (m + 1) ≤ tailP N a D m := by
  cases m with
  | zero =>
    simp only [tailP]
    split_ifs
    · linarith [Real.exp_pos (-(a * max 0 (D - ((0 : ℕ) : ℝ))))]
    · norm_num
  | succ m =>
    simp only [tailP]
    split_ifs with h1 h2 h2
    · have : max 0 (D - ((m + 1 : ℕ) : ℝ)) ≤ max 0 (D - m) := by
        push_cast; exact max_le_max le_rfl (by linarith)
      have := Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left this ha))
      linarith
    · omega
    · have := tailP_nonneg N ha D (m + 1)
      simp only [tailP, h2, if_true] at this
      linarith
    · exact le_rfl

theorem tailP_top (N : ℕ) (a D : ℝ) : tailP N a D (N + 2) = 0 := by
  simp [tailP]

/-- Telescoping sums over `Fin (N + 2)`. -/
theorem sum_tail_telescope (N : ℕ) (f : ℕ → ℝ) (m : ℕ) (hm : m ≤ N + 2) :
    ∑ k ∈ (univ : Finset (Fin (N + 2))).filter (fun k => m ≤ k.val), (f k.val - f (k.val + 1)) =
      f m - f (N + 2) := by
  rw [sum_filter, Fin.sum_univ_eq_sum_range (fun k => if m ≤ k then f k - f (k + 1) else 0)]
  have key : ∀ n, m ≤ n → ∑ k ∈ range n, (if m ≤ k then f k - f (k + 1) else 0) = f m - f n := by
    intro n hn
    induction n with
    | zero => have : m = 0 := by omega
              subst this; simp
    | succ n ih =>
      rcases Nat.lt_or_ge n m with h | h
      · have : m = n + 1 := by omega
        subst this
        rw [sum_eq_zero]
        · ring
        · intro k hk; rw [if_neg (by rw [mem_range] at hk; omega)]
      · rw [sum_range_succ, ih h, if_pos h]; ring
  exact key _ hm

theorem coinQ_isPMF (N : ℕ) {a : ℝ} (ha : 0 ≤ a) (D : ℝ) : IsPMF (coinQ (V := V) N a D) := by
  refine ⟨fun c k => ?_, fun c => ?_⟩
  · cases c with
    | inl e =>
      simp only [coinQ]
      split_ifs
      · exact (Real.exp_pos _).le
      · have : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        linarith
      · exact le_rfl
    | inr v =>
      simp only [coinQ]
      linarith [tailP_anti N ha D k.val]
  · cases c with
    | inl e =>
      simp only [coinQ]
      rw [Fin.sum_univ_eq_sum_range (fun k => if k = 0 then Real.exp (-a) else if k = 1 then
        1 - Real.exp (-a) else 0)]
      rw [sum_range_succ', sum_range_succ', sum_eq_zero (fun k _ => by simp)]
      simp
    | inr v =>
      simp only [coinQ]
      have := sum_tail_telescope N (tailP N a D) 0 (by omega)
      rw [filter_true_of_mem (fun k _ => Nat.zero_le _)] at this
      rw [this, tailP_top]
      simp [tailP]

/-- The pushforward of the threshold coins is the law of the Boolean coins of the round. -/
theorem push_coinQ (N : ℕ) {a : ℝ} (ha : 0 ≤ a) (D : ℝ) (A : Finset (Finset V))
    (hA : ∀ v, degree A v ≤ N) :
    (fun c b => ∑ k ∈ univ.filter (fun k => decode N A c k = b), coinQ N a D c k) =
      roundP A a D := by
  have hP := coinQ_isPMF (V := V) N ha D
  -- it suffices to compute the probability of `true`
  have htrue : ∀ c, ∑ k ∈ univ.filter (fun k => decode N A c k = true), coinQ N a D c k =
      roundP A a D c true := by
    intro c
    cases c with
    | inl e =>
      simp only [decode, roundP, qTrue, if_true, decide_eq_true_eq]
      by_cases he : e ∈ A
      · simp only [he, true_and, if_true]
        have h1 := hP.2 (Sum.inl e)
        rw [← sum_filter_add_sum_filter_not univ (fun k : Fin (N + 2) => k.val ≠ 0)] at h1
        have h2 : ∑ k ∈ univ.filter (fun k : Fin (N + 2) => ¬ k.val ≠ 0), coinQ (V := V) N a D
            (Sum.inl e) k = Real.exp (-a) := by
          rw [sum_eq_single (0 : Fin (N + 2))]
          · simp [coinQ]
          · intro k hk hk0
            simp only [mem_filter, not_not] at hk
            exact absurd (Fin.ext hk.2) hk0
          · intro h; simp at h
        linarith
      · simp [he]
    | inr v =>
      simp only [decode, roundP, qTrue, if_true, decide_eq_true_eq, coinQ]
      have := sum_tail_telescope N (tailP N a D) (degree A v + 1) (by have := hA v; omega)
      rw [show (univ.filter (fun k : Fin (N + 2) => degree A v < k.val)) =
        univ.filter (fun k : Fin (N + 2) => degree A v + 1 ≤ k.val) from
          filter_congr (fun k _ => by omega), this, tailP_top]
      simp [tailP, hA v]
  funext c b
  cases b with
  | true => exact htrue c
  | false =>
    have h1 := hP.2 c
    rw [← sum_filter_add_sum_filter_not univ (fun k => decode N A c k = true)] at h1
    have h2 : univ.filter (fun k => decode N A c k = false) =
        univ.filter (fun k => ¬ decode N A c k = true) := filter_congr (fun k _ => by simp)
    rw [h2]
    have h3 : roundP A a D c false = 1 - roundP A a D c true := by simp [roundP]
    rw [h3, ← htrue c]
    linarith

/-! ## The process -/

section Process

variable (N : ℕ) (H : Finset (Finset V)) (as Ds : ℕ → ℝ) (T : ℕ)

/-- The law of all coins: round `t`, coin `c`. -/
noncomputable def procQ : Fin T × Coin V → Fin (N + 2) → ℝ :=
  fun i => coinQ N (as i.1) (Ds i.1) i.2

/-- The state of the process after `t` rounds, as a function of the coins. -/
noncomputable def stateAt (ω : Fin T × Coin V → Fin (N + 2)) : ℕ → State V
  | 0 => (H, ∅)
  | t + 1 => if h : t < T then
      nextT (Ds (t + 1)) (stateAt ω t) (fun c => decode N (stateAt ω t).1 c (ω (⟨t, h⟩, c)))
    else stateAt ω t

/-- The output matching. -/
noncomputable def outM (ω : Fin T × Coin V → Fin (N + 2)) : Finset (Finset V) :=
  (stateAt N H Ds T ω T).2

variable {N H as Ds T}

theorem procQ_isPMF (has : ∀ t, 0 ≤ as t) : IsPMF (procQ (V := V) N as Ds T) :=
  ⟨fun i k => (coinQ_isPMF N (has i.1) (Ds i.1)).1 i.2 k,
    fun i => (coinQ_isPMF N (has i.1) (Ds i.1)).2 i.2⟩

theorem stateAt_inv (ω : Fin T × Coin V → Fin (N + 2)) : ∀ t, Inv H (stateAt N H Ds T ω t)
  | 0 => ⟨subset_refl _, empty_subset _, fun e he => (Finset.notMem_empty e he).elim,
      fun f _ g hg => (Finset.notMem_empty g hg).elim⟩
  | t + 1 => by
    simp only [stateAt]
    split_ifs
    · exact inv_nextT (stateAt_inv ω t) _
    · exact stateAt_inv ω t

theorem outM_isMatching (ω : Fin T × Coin V → Fin (N + 2)) :
    IsMatching (outM N H Ds T ω) ∧ outM N H Ds T ω ⊆ H :=
  ⟨(stateAt_inv ω T).2.2.1, (stateAt_inv ω T).2.1⟩

/-- The state after `t` rounds only depends on the coins of the rounds `< t`. -/
theorem stateAt_dep {ω ω' : Fin T × Coin V → Fin (N + 2)} :
    ∀ t, (∀ i : Fin T × Coin V, i.1.val < t → ω i = ω' i) →
      stateAt N H Ds T ω t = stateAt N H Ds T ω' t
  | 0, _ => rfl
  | t + 1, h => by
    have ih := stateAt_dep t (fun i hi => h i (by omega))
    simp only [stateAt]
    split_ifs with ht
    · rw [ih]
      congr 1
      funext c
      rw [h (⟨t, ht⟩, c) (by simp)]
    · exact ih

/-- The process stays good. -/
theorem procT_good (hDs : ∀ t, 0 ≤ Ds t) (hdeg : Good (Ds 0) H) :
    ∀ t S, procT H as Ds t S ≠ 0 → Good (Ds t) S.1
  | 0, S => by
    classical
    intro h
    simp only [procT] at h
    split_ifs at h with hS
    · rw [hS]; exact hdeg
    · exact absurd rfl h
  | t + 1, S' => by
    classical
    intro h
    simp only [procT, stepT] at h
    obtain ⟨S, -, hS⟩ := exists_ne_zero_of_sum_ne_zero h
    have hμ : procT H as Ds t S ≠ 0 := left_ne_zero_of_mul hS
    have hg := procT_good hDs hdeg t S hμ
    have hS2 := right_ne_zero_of_mul hS
    rw [if_pos hg] at hS2
    unfold pE at hS2
    obtain ⟨ω, -, hω⟩ := exists_ne_zero_of_sum_ne_zero hS2
    have hω2 := right_ne_zero_of_mul hω
    rw [ite_ne_right_iff] at hω2
    rw [← hω2.1]
    exact trim_good _ (hDs (t + 1))

/-- **The law of the realised process is the law of the trimmed nibble.** -/
theorem stateAt_law (has : ∀ t, 0 ≤ as t) (hDs : ∀ t, 0 ≤ Ds t) (hdeg : Good (Ds 0) H)
    (hN : H.card ≤ N) :
    ∀ t ≤ T, ∀ g : State V → ℝ,
      pE (procQ N as Ds T) (fun ω => g (stateAt N H Ds T ω t)) =
        ∑ S, procT H as Ds t S * g S := by
  classical
  have hQ := procQ_isPMF (V := V) (N := N) (Ds := Ds) (T := T) has
  intro t
  induction t with
  | zero =>
    intro _ g
    simp only [stateAt, procT]
    rw [pE_const hQ, sum_eq_single (H, ∅)]
    · simp
    · intro S _ hS; simp [hS]
    · simp
  | succ t ih =>
    intro ht g
    have htT : t < T := ht
    set tt : Fin T := ⟨t, htT⟩ with htt
    -- the round-`t` expectation at a fixed state
    set h : State V → ℝ := fun S => pE (roundP S.1 (as t) (Ds t))
      (fun ω' => g (nextT (Ds (t + 1)) S ω')) with hh
    have hround : ∀ S : State V, S.1 ⊆ H →
        pE (procQ N as Ds T) (fun ω => g (nextT (Ds (t + 1)) S
          (fun c => decode N S.1 c (ω (tt, c))))) = h S := by
      intro S hS
      have hdegS : ∀ v, degree S.1 v ≤ N := fun v =>
        ((card_le_card (filter_subset _ _)).trans (card_le_card hS)).trans hN
      have := pE_map_coord hQ (fun c : Coin V => (tt, c)) (fun a b h => by simpa using h)
        (fun c => decode N S.1 c) (fun ω' => g (nextT (Ds (t + 1)) S ω'))
      rw [this]
      have hpush := push_coinQ N (has t) (Ds t) S.1 hdegS
      simp only [procQ, htt] at hpush ⊢
      rw [hpush]
    have hstep : ∀ ω, stateAt N H Ds T ω (t + 1) =
        nextT (Ds (t + 1)) (stateAt N H Ds T ω t)
          (fun c => decode N (stateAt N H Ds T ω t).1 c (ω (tt, c))) := by
      intro ω
      simp only [stateAt, dif_pos htT]
      rfl
    simp_rw [hstep]
    -- expand along the value of the state after `t` rounds
    have hexp : ∀ ω, g (nextT (Ds (t + 1)) (stateAt N H Ds T ω t)
        (fun c => decode N (stateAt N H Ds T ω t).1 c (ω (tt, c)))) =
        ∑ S, g (nextT (Ds (t + 1)) S (fun c => decode N S.1 c (ω (tt, c)))) *
          (if stateAt N H Ds T ω t = S then 1 else 0) := by
      intro ω
      rw [sum_eq_single (stateAt N H Ds T ω t)]
      · simp
      · intro S _ hS; simp [Ne.symm hS]
      · simp
    simp_rw [hexp]
    rw [pE_sum]
    -- independence of the round-`t` coins from the past
    have hind : ∀ S : State V, pE (procQ N as Ds T) (fun ω =>
        g (nextT (Ds (t + 1)) S (fun c => decode N S.1 c (ω (tt, c)))) *
          (if stateAt N H Ds T ω t = S then 1 else 0)) =
        h S * pE (procQ N as Ds T) (fun ω => if stateAt N H Ds T ω t = S then 1 else 0) := by
      intro S
      rw [pE_mul_of_indep hQ (univ.filter (fun i : Fin T × Coin V => i.1 = tt))]
      · by_cases hS : S.1 ⊆ H
        · rw [hround S hS]
        · have : (fun ω => if stateAt N H Ds T ω t = S then (1 : ℝ) else 0) = fun _ => 0 := by
            funext ω
            rw [if_neg]
            intro heq
            exact hS (heq ▸ (stateAt_inv ω t).1)
          rw [this, pE_const hQ, mul_zero, mul_zero]
      · intro ω ω' hωω'
        congr 2
        funext c
        rw [hωω' (tt, c) (by simp)]
      · intro ω ω' hωω'
        rw [stateAt_dep t (fun i hi => hωω' i (by
          simp only [mem_filter, mem_univ, true_and]
          intro heq; rw [heq] at hi; simp [htt] at hi))]
    simp_rw [hind]
    -- back to an expectation of a function of the state after `t` rounds
    have hback : ∑ S, h S * pE (procQ N as Ds T) (fun ω =>
        if stateAt N H Ds T ω t = S then (1 : ℝ) else 0) =
        pE (procQ N as Ds T) (fun ω => h (stateAt N H Ds T ω t)) := by
      simp_rw [← pE_const_mul]
      rw [← pE_sum]
      congr 1; funext ω
      rw [sum_eq_single (stateAt N H Ds T ω t)]
      · simp
      · intro S _ hS; simp [Ne.symm hS]
      · simp
    rw [hback, ih (by omega) h]
    simp only [procT]
    rw [stepT_sum]
    refine sum_congr rfl fun S _ => ?_
    by_cases hS : procT H as Ds t S = 0
    · rw [hS, zero_mul, zero_mul]
    · rw [if_pos (procT_good hDs hdeg t S hS)]

/-- **Marginals of the realised process.** -/
theorem outM_marginal (has : ∀ t, 0 ≤ as t) (hDs : ∀ t, 0 ≤ Ds t) (hdeg : Good (Ds 0) H)
    (hN : H.card ≤ N) (e : Finset V) :
    pProb (procQ N as Ds T) (fun ω => e ∈ outM N H Ds T ω) =
      ∑ M, outMT H as Ds T M * (if e ∈ M then 1 else 0) := by
  classical
  rw [pProb_eq_pE _ (fun ω => if e ∈ (stateAt N H Ds T ω T).2 then (1 : ℝ) else 0)
    (fun ω h => by simp [outM] at h; simp [h]) (fun ω h => by simp [outM] at h; simp [h])]
  rw [stateAt_law has hDs hdeg hN T le_rfl (fun S => if e ∈ S.2 then 1 else 0)]
  unfold outMT
  simp_rw [sum_mul]
  rw [sum_comm, ← Fintype.sum_prod_type']

end Process

end Pseudorandom.PS
