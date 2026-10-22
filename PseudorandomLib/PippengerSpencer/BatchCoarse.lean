/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.PippengerSpencer.BatchProb

/-! # A batch of independent nibbles: the failure probability at one vertex

`K` independent samples `y : Fin K → Ω₁` of the realised nibble on `G`. For a vertex `v`, the
probability that fewer than `K λ` edges at `v` lie in one of the sampled matchings is at most
`exp(-t²/(2(K+t))) + exp(-m)`, under the conditions of `BatchProb.lean`.
-/

@[expose] public section

namespace Pseudorandom.PS

open Finset Nibble

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {N : ℕ} {G : Finset (Finset V)} {as Ds : ℕ → ℝ} {T K : ℕ}

/-- The law of `K` independent samples. -/
noncomputable def sampleQ (N : ℕ) (as Ds : ℕ → ℝ) (T K : ℕ) :
    Fin K → (Fin T × Coin V → Fin (N + 2)) → ℝ :=
  fun _ x => pw (procQ N as Ds T) x

theorem sampleQ_isPMF (has : ∀ t, 0 ≤ as t) : IsPMF (sampleQ (V := V) N as Ds T K) :=
  ⟨fun _ x => pw_nonneg (procQ_isPMF has) x, fun _ => sum_pw (procQ_isPMF has)⟩

/-- All edges coloured by the batch. -/
noncomputable def colSet (N : ℕ) (G : Finset (Finset V)) (Ds : ℕ → ℝ) (T : ℕ)
    (y : Fin K → (Fin T × Coin V → Fin (N + 2))) : Finset (Finset V) :=
  univ.biUnion (fun i => outM N G Ds T (y i))

/-- The edge of the `i`-th sample at `v` was already used by an earlier sample. -/
def Rep (N : ℕ) (G : Finset (Finset V)) (Ds : ℕ → ℝ) (T : ℕ) (v : V)
    (y : Fin K → (Fin T × Coin V → Fin (N + 2))) (i : Fin K) : Prop :=
  ∃ e ∈ outM N G Ds T (y i), v ∈ e ∧ ∃ j < i, e ∈ outM N G Ds T (y j)

open Classical in
/-- **Counting.** `#coloured edges at v ≥ #{i : M_i covers v} - #{i : repetition at i}`. -/
theorem card_cov_sub_card_rep_le (v : V) (y : Fin K → (Fin T × Coin V → Fin (N + 2))) :
    ((univ.filter (fun i => Cov N G Ds T v (y i))).card : ℝ) -
        (univ.filter (fun i => Rep N G Ds T v y i)).card ≤
      ((colSet N G Ds T y).filter (fun e => v ∈ e)).card := by
  set I := univ.filter (fun i => Cov N G Ds T v (y i) ∧ ¬ Rep N G Ds T v y i)
  have h1 : (univ.filter (fun i => Cov N G Ds T v (y i))).card ≤
      I.card + (univ.filter (fun i => Rep N G Ds T v y i)).card := by
    refine (card_le_card ?_).trans (card_union_le _ _)
    intro i hi
    rw [mem_filter] at hi
    rw [mem_union, mem_filter, mem_filter]
    by_cases hr : Rep N G Ds T v y i
    · exact Or.inr ⟨mem_univ _, hr⟩
    · exact Or.inl ⟨mem_univ _, hi.2, hr⟩
  have h2 : I.card ≤ ((colSet N G Ds T y).filter (fun e => v ∈ e)).card := by
    let f : Fin K → Finset V := fun i =>
      if h : Cov N G Ds T v (y i) then h.choose else ∅
    have hf : ∀ i, Cov N G Ds T v (y i) → f i ∈ outM N G Ds T (y i) ∧ v ∈ f i := by
      intro i h
      simp only [f, dif_pos h]
      exact h.choose_spec
    refine card_le_card_of_injOn f ?_ ?_
    · intro i hi
      have hi' := (mem_filter.mp hi).2
      obtain ⟨h1, h2⟩ := hf i hi'.1
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨i, mem_univ _, h1⟩, h2⟩
    · intro i hi i' hi' heq
      have hi1 := (mem_filter.mp hi).2
      have hi2 := (mem_filter.mp hi').2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · apply hi2.2
        obtain ⟨h1, h2⟩ := hf i' hi2.1
        refine ⟨f i', h1, h2, i, hlt, ?_⟩
        rw [← heq]; exact (hf i hi1.1).1
      · apply hi1.2
        obtain ⟨h1, h2⟩ := hf i hi1.1
        refine ⟨f i, h1, h2, i', hlt, ?_⟩
        rw [heq]; exact (hf i' hi2.1).1
  have : ((univ.filter (fun i => Cov N G Ds T v (y i))).card : ℝ) ≤
      I.card + (univ.filter (fun i => Rep N G Ds T v y i)).card := by exact_mod_cast h1
  have h2' : (I.card : ℝ) ≤ ((colSet N G Ds T y).filter (fun e => v ∈ e)).card := by
    exact_mod_cast h2
  linarith

open Classical in
/-- **Lower tail for the number of samples covering `v`.** -/
theorem pProb_cov_lower (has : ∀ t, 0 ≤ as t) (v : V) {m₁ t : ℝ} (ht : 0 < t)
    (hm₁ : m₁ ≤ pProb (procQ N as Ds T) (Cov N G Ds T v)) :
    pProb (sampleQ N as Ds T K) (fun y =>
        ((univ.filter (fun i => Cov N G Ds T v (y i))).card : ℝ) ≤ K * m₁ - t) ≤
      Real.exp (-(t ^ 2 / (2 * (K + t)))) := by
  have hQ := sampleQ_isPMF (V := V) (N := N) (Ds := Ds) (T := T) (K := K) has
  set g : (Fin T × Coin V → Fin (N + 2)) → ℝ := fun a => if Cov N G Ds T v a then 1 else 0
  set f : (Fin K → (Fin T × Coin V → Fin (N + 2))) → ℝ := fun y => ∑ i, g (y i) with hfdef
  have hfeq : ∀ y, f y = ((univ.filter (fun i => Cov N G Ds T v (y i))).card : ℝ) := by
    intro y; simp only [hfdef, g]; rw [sum_boole]
  have hEf : (K : ℝ) * m₁ ≤ pE (sampleQ N as Ds T K) f := by
    simp only [hfdef]
    rw [pE_sum]
    have : ∀ i, pE (sampleQ N as Ds T K) (fun y => g (y i)) =
        pProb (procQ N as Ds T) (Cov N G Ds T v) := by
      intro i
      rw [pE_coord hQ i g]
      rw [pProb_eq_pE _ g (fun a h => by simp [g, h]) (fun a h => by simp [g, h])]
      rfl
    simp_rw [this]
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left hm₁ (Nat.cast_nonneg _)
  have hgap : CoordGap f (fun _ => 1) := by
    intro i y a b
    have key : ∀ c, f (Function.update y i c) = g c + ∑ j ∈ univ.erase i, g (y j) := by
      intro c
      simp only [hfdef]
      rw [← add_sum_erase _ _ (mem_univ i)]
      simp only [Function.update_self]
      congr 1
      refine sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (ne_of_mem_erase hj)]
    rw [key a, key b]
    simp only [add_sub_add_right_eq_sub, g]
    split_ifs <;> norm_num
  have hrare : CoordRare f (fun _ => univ) := fun i y a b ha => absurd (mem_univ a) ha
  have h := pE_lower_tail (sampleQ N as Ds T K) hQ f (fun _ => 1) (fun _ => 1) (fun _ => univ)
    1 one_pos (fun _ => ⟨zero_le_one, le_rfl⟩) hgap hrare
    (fun i => by rw [hQ.2 i]) t ht
  simp only [one_pow, mul_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    one_mul] at h
  refine le_trans (pProb_mono hQ fun y hy => ?_) h
  rw [hfeq y]
  linarith

open Classical in
/-- **Repetitions.** If, whatever the earlier samples, the `i`-th sample hits any given set of at
most `K` edges at `v` with probability at most `q`, then `P(Rep_i for all i ∈ I) ≤ q^{|I|}`. -/
theorem pProb_rep_all_le (has : ∀ t, 0 ≤ as t) (v : V) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ U : Finset (Finset V), U.card ≤ K → (∀ e ∈ U, v ∈ e) →
      pProb (procQ N as Ds T) (fun y => ∃ e ∈ outM N G Ds T y, e ∈ U) ≤ q)
    (I : Finset (Fin K)) :
    pProb (sampleQ N as Ds T K) (fun y => ∀ i ∈ I, Rep N G Ds T v y i) ≤ q ^ I.card := by
  have hQ := sampleQ_isPMF (V := V) (N := N) (Ds := Ds) (T := T) (K := K) has
  induction I using Finset.induction_on_max with
  | empty =>
    simp only [notMem_empty, IsEmpty.forall_iff, implies_true, card_empty, pow_zero]
    exact pProb_le_one hQ _
  | insert a s hlt ih =>
    have has' : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem has', pow_succ]
    set f : (Fin K → (Fin T × Coin V → Fin (N + 2))) → ℝ :=
      fun y => if ∀ i ∈ s, Rep N G Ds T v y i then 1 else 0 with hfdef
    set g : (Fin K → (Fin T × Coin V → Fin (N + 2))) → ℝ :=
      fun y => if Rep N G Ds T v y a then 1 else 0 with hgdef
    rw [pProb_eq_pE _ (fun y => f y * g y)]
    · -- the events for `i < a` do not depend on the `a`-th sample
      have hRep : ∀ i < a, ∀ y b, Rep N G Ds T v (Function.update y a b) i ↔
          Rep N G Ds T v y i := by
        intro i hi y b
        unfold Rep
        rw [Function.update_of_ne (ne_of_lt hi)]
        refine exists_congr fun e => and_congr_right fun _ => and_congr_right fun _ =>
          exists_congr fun j => and_congr_right fun hj => ?_
        rw [Function.update_of_ne (ne_of_lt (hj.trans hi))]
      have hf : ∀ y b, f (Function.update y a b) = f y := by
        intro y b
        simp only [hfdef]
        congr 1
        exact propext (forall₂_congr fun i hi => hRep i (hlt i hi) y b)
      have hg : ∀ y, ∑ b, sampleQ N as Ds T K a b * g (Function.update y a b) ≤ q := by
        intro y
        set U := (univ.filter (fun j => j < a)).biUnion
          (fun j => (outM N G Ds T (y j)).filter (fun e => v ∈ e)) with hU
        have hUcard : U.card ≤ K := by
          refine card_biUnion_le.trans ?_
          calc ∑ j ∈ univ.filter (fun j => j < a),
                ((outM N G Ds T (y j)).filter (fun e => v ∈ e)).card
              ≤ ∑ j ∈ univ.filter (fun j => j < a), 1 :=
                sum_le_sum fun j _ => card_filter_mem_le_one
                  (outM_isMatching (N := N) (H := G) (Ds := Ds) (T := T) (y j)).1 v
            _ ≤ K := by
                rw [sum_const, smul_eq_mul, mul_one]
                exact (card_le_univ _).trans (by simp)
        have hUv : ∀ e ∈ U, v ∈ e := by
          intro e he
          obtain ⟨j, -, hj⟩ := mem_biUnion.mp he
          exact (mem_filter.mp hj).2
        have hiff : ∀ b, Rep N G Ds T v (Function.update y a b) a ↔
            ∃ e ∈ outM N G Ds T b, e ∈ U := by
          intro b
          unfold Rep
          simp only [Function.update_self]
          constructor
          · rintro ⟨e, he, hv, j, hj, hej⟩
            rw [Function.update_of_ne (ne_of_lt hj)] at hej
            exact ⟨e, he, mem_biUnion.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩,
              mem_filter.mpr ⟨hej, hv⟩⟩⟩
          · rintro ⟨e, he, heU⟩
            obtain ⟨j, hj, hej⟩ := mem_biUnion.mp heU
            have hja := (mem_filter.mp hj).2
            refine ⟨e, he, (mem_filter.mp hej).2, j, hja, ?_⟩
            rw [Function.update_of_ne (ne_of_lt hja)]
            exact (mem_filter.mp hej).1
        have := hq U hUcard hUv
        rw [pProb_eq_pE _ (fun b => if ∃ e ∈ outM N G Ds T b, e ∈ U then (1 : ℝ) else 0)
          (fun b h => by simp [h]) (fun b h => by simp [h])] at this
        refine le_trans (le_of_eq ?_) this
        unfold pE
        refine sum_congr rfl fun b _ => ?_
        simp only [sampleQ, hgdef]
        congr 1
        exact if_congr (hiff b) rfl rfl
      have hf0 : ∀ y, 0 ≤ f y := fun y => by simp only [hfdef]; split_ifs <;> norm_num
      have := pE_mul_le_of_coord hQ a f g q hf0 hf hg
      rw [pProb_eq_pE _ f (fun y h => by simp only [hfdef]; exact if_pos h)
        (fun y h => by simp only [hfdef]; exact if_neg h)] at ih
      calc pE (sampleQ N as Ds T K) (fun y => f y * g y) ≤ q * pE (sampleQ N as Ds T K) f := this
        _ ≤ q * q ^ s.card := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ s.card * q := by ring
    · intro y h
      have h1 : ∀ i ∈ s, Rep N G Ds T v y i := fun i hi => h i (mem_insert_of_mem hi)
      have h2 : Rep N G Ds T v y a := h a (mem_insert_self a s)
      simp only [hfdef, hgdef]
      rw [if_pos h1, if_pos h2, mul_one]
    · intro y h
      by_cases h1 : ∀ i ∈ s, Rep N G Ds T v y i
      · have h2 : ¬ Rep N G Ds T v y a := by
          intro h2
          apply h
          intro i hi
          rcases mem_insert.mp hi with rfl | hi
          · exact h2
          · exact h1 i hi
        simp only [hgdef]
        rw [if_neg h2, mul_zero]
      · simp only [hfdef]
        rw [if_neg h1, zero_mul]

open Classical in
/-- **Few repetitions.** `P(#{i : Rep_i} ≥ m) ≤ e^{-m}` when `m ≥ e² K q`. -/
theorem pProb_rep_ge (has : ∀ t, 0 ≤ as t) (v : V) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ U : Finset (Finset V), U.card ≤ K → (∀ e ∈ U, v ∈ e) →
      pProb (procQ N as Ds T) (fun y => ∃ e ∈ outM N G Ds T y, e ∈ U) ≤ q)
    (m : ℕ) (hm : Real.exp 2 * K * q ≤ m) :
    pProb (sampleQ N as Ds T K) (fun y =>
        (m : ℝ) ≤ (univ.filter (fun i => Rep N G Ds T v y i)).card) ≤ Real.exp (-m) := by
  have hQ := sampleQ_isPMF (V := V) (N := N) (Ds := Ds) (T := T) (K := K) has
  have hsub : ∀ y, (m : ℝ) ≤ (univ.filter (fun i => Rep N G Ds T v y i)).card →
      ∃ I ∈ (univ : Finset (Fin K)).powersetCard m, ∀ i ∈ I, Rep N G Ds T v y i := by
    intro y hy
    have hy' : m ≤ (univ.filter (fun i => Rep N G Ds T v y i)).card := by exact_mod_cast hy
    obtain ⟨I, hI, hIcard⟩ := exists_subset_card_eq hy'
    exact ⟨I, mem_powersetCard.mpr ⟨subset_univ _, hIcard⟩,
      fun i hi => (mem_filter.mp (hI hi)).2⟩
  refine (pProb_mono hQ hsub).trans ((pProb_exists_le hQ _ _).trans ?_)
  have h1 : ∑ I ∈ (univ : Finset (Fin K)).powersetCard m,
      pProb (sampleQ N as Ds T K) (fun y => ∀ i ∈ I, Rep N G Ds T v y i) ≤
      ∑ I ∈ (univ : Finset (Fin K)).powersetCard m, q ^ m := by
    refine sum_le_sum fun I hI => ?_
    rw [← (mem_powersetCard.mp hI).2]
    exact pProb_rep_all_le has v hq0 hq I
  refine h1.trans ?_
  rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- `C(K,m) q^m ≤ (Kq)^m/m! ≤ e^{-m}`
  have hc : ((K.choose m : ℕ) : ℝ) ≤ (K : ℝ) ^ m / m.factorial := Nat.choose_le_pow_div m K
  have hx : 0 ≤ Real.exp 2 * K * q := by positivity
  have hexp := Real.pow_div_factorial_le_exp _ hx m
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  calc ((K.choose m : ℕ) : ℝ) * q ^ m ≤ (K : ℝ) ^ m / m.factorial * q ^ m :=
        mul_le_mul_of_nonneg_right hc (pow_nonneg hq0 m)
    _ = (Real.exp 2 * K * q) ^ m / m.factorial * Real.exp (-(2 * m)) := by
        rw [mul_pow, mul_pow, ← Real.exp_nat_mul, show -(2 * (m : ℝ)) = -(↑m * 2) by ring,
          Real.exp_neg]
        field_simp
    _ ≤ Real.exp (Real.exp 2 * K * q) * Real.exp (-(2 * m)) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    _ ≤ Real.exp m * Real.exp (-(2 * m)) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hm) (Real.exp_pos _).le
    _ = Real.exp (-m) := by rw [← Real.exp_add]; ring_nf

end Pseudorandom.PS
