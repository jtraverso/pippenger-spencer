/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PseudorandomLib.Bernstein

/-! # Freedman's inequality for stopped exposure martingales

We work in the finite product space `Fin n → α` with independent coordinates (distribution
`P i` at coordinate `i`), revealed in the order `0, 1, …, n - 1`.

A process is a sequence `X k : (Fin n → α) → ℝ` where `X k` only depends on the coordinates
`< k` (`Adapted`). It is a martingale if `X i ω = ∑ₐ P i a · X (i+1) (ω[i ↦ a])`.

`freedman_upper`: if, as long as the "good" events `G 0, …, G i` hold, the increments are
bounded by `C` and the accumulated conditional expected absolute increments are at most `s`,
then `P[X n - X 0 ≥ λ and all G i hold] ≤ exp(-λ² / (2C(λ + s)))`. This is Freedman's
inequality applied to the process stopped at the first bad time.
-/

@[expose] public section

namespace Pseudorandom

open Finset

section Resample

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] {P : ι → α → ℝ}

/-- Resampling one coordinate does not change the expectation. -/
theorem pE_resample (hP : IsPMF P) (i : ι) (g : (ι → α) → ℝ) :
    pE P (fun ω => ∑ a, P i a * g (Function.update ω i a)) = pE P g := by
  classical
  unfold pE pw
  set e := Equiv.funSplitAt i α
  have key : ∀ F : (ι → α) → ℝ, ∑ ω, F ω = ∑ x : α × ({j // j ≠ i} → α), F (e.symm x) :=
    fun F => (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm
  have hpw : ∀ x : α × ({j // j ≠ i} → α),
      ∏ j, P j (e.symm x j) = P i x.1 * ∏ j : {j // j ≠ i}, P j (x.2 j) := by
    intro x
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    congr 1
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · refine Fintype.prod_congr _ _ fun j => ?_
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt, j.2]
  have hupd : ∀ (x : α × ({j // j ≠ i} → α)) (a : α),
      Function.update (e.symm x) i a = e.symm (a, x.2) := by
    intro x a
    funext j
    by_cases hj : j = i
    · subst hj; simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  rw [key, key]
  simp_rw [hpw, hupd, Fintype.sum_prod_type]
  rw [sum_comm (γ := α)]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [← sum_mul, ← sum_mul, hP.2 i, one_mul, mul_sum]
  exact sum_congr rfl fun a _ => by ring

end Resample

section Freedman

variable {α : Type*} [Fintype α] {n : ℕ}

/-- `F` only depends on the coordinates `< k`. -/
def Adapted {β : Type*} (k : ℕ) (F : (Fin n → α) → β) : Prop :=
  ∀ ω ω' : Fin n → α, (∀ i : Fin n, (i : ℕ) < k → ω i = ω' i) → F ω = F ω'

omit [Fintype α] in
theorem Adapted.mono {β : Type*} {k k' : ℕ} {F : (Fin n → α) → β} (h : Adapted k F)
    (hk : k ≤ k') : Adapted k' F :=
  fun ω ω' hω => h ω ω' fun i hi => hω i (lt_of_lt_of_le hi hk)

omit [Fintype α] in
theorem Adapted.update {β : Type*} {k : ℕ} {F : (Fin n → α) → β} (h : Adapted k F)
    (i : Fin n) (hi : k ≤ i) (ω : Fin n → α) (a : α) : F (Function.update ω i a) = F ω :=
  h _ _ fun j hj => by
    rw [Function.update_of_ne]
    intro hji; subst hji; omega

/-- All good events up to time `k` hold. -/
def Alive (G : ℕ → (Fin n → α) → Prop) (k : ℕ) (ω : Fin n → α) : Prop := ∀ j ≤ k, G j ω

/-- Conditional expected absolute increment at step `i`. -/
noncomputable def condAbsInc (P : Fin n → α → ℝ) (X : ℕ → (Fin n → α) → ℝ) (i : Fin n)
    (ω : Fin n → α) : ℝ :=
  ∑ a, P i a * |X (i + 1) (Function.update ω i a) - X i ω|

open Classical in
/-- The stopped process. -/
noncomputable def stopped (X : ℕ → (Fin n → α) → ℝ) (G : ℕ → (Fin n → α) → Prop) :
    ℕ → (Fin n → α) → ℝ
  | 0 => X 0
  | k + 1 => fun ω => if Alive G k ω then X (k + 1) ω else stopped X G k ω

open Classical in
/-- The accumulated conditional expected absolute increments of the stopped process. -/
noncomputable def accInc (P : Fin n → α → ℝ) (X : ℕ → (Fin n → α) → ℝ)
    (G : ℕ → (Fin n → α) → Prop) : ℕ → (Fin n → α) → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun ω => if h : k < n then
      (if Alive G k ω then accInc P X G k ω + condAbsInc P X ⟨k, h⟩ ω else accInc P X G k ω)
      else accInc P X G k ω

variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}

omit [Fintype α] in
theorem Alive.mono {k k' : ℕ} {ω : Fin n → α} (h : Alive G k' ω) (hk : k ≤ k') :
    Alive G k ω := fun j hj => h j (hj.trans hk)

omit [Fintype α] in
theorem alive_adapted (hG : ∀ k, Adapted k (G k)) (k : ℕ) :
    Adapted k (fun ω => Alive G k ω) := by
  intro ω ω' hω
  apply propext
  unfold Alive
  constructor
  · intro h j hj
    have := hG j ω ω' (fun i hi => hω i (by omega))
    rw [← this]; exact h j hj
  · intro h j hj
    have := hG j ω ω' (fun i hi => hω i (by omega))
    rw [this]; exact h j hj

omit [Fintype α] in
theorem stopped_eq_of_alive {ω : Fin n → α} :
    ∀ k, (k = 0 ∨ Alive G (k - 1) ω) → stopped X G k ω = X k ω
  | 0, _ => rfl
  | k + 1, h => by
    have hk : Alive G k ω := by
      rcases h with h | h
      · omega
      · simpa using h
    simp [stopped, hk]

omit [Fintype α] in
theorem stopped_adapted (hX : ∀ k, Adapted k (X k)) (hG : ∀ k, Adapted k (G k)) :
    ∀ k, Adapted k (stopped X G k)
  | 0 => hX 0
  | k + 1 => by
    intro ω ω' hω
    have ha := alive_adapted hG k ω ω' (fun i hi => hω i (by omega))
    simp only [stopped]
    simp only at ha
    rw [ha, hX (k + 1) ω ω' hω, stopped_adapted hX hG k ω ω' (fun i hi => hω i (by omega))]

theorem condAbsInc_adapted (hX : ∀ k, Adapted k (X k)) (i : Fin n) :
    Adapted i (condAbsInc P X i) := by
  intro ω ω' hω
  unfold condAbsInc
  refine sum_congr rfl fun a _ => ?_
  congr 3
  · apply hX
    intro j hj
    by_cases hji : j = i
    · subst hji; simp
    · rw [Function.update_of_ne hji, Function.update_of_ne hji]
      exact hω j (by have : (j : ℕ) ≠ i := fun h => hji (Fin.ext h); omega)
  · exact hX i ω ω' hω

theorem accInc_adapted (hX : ∀ k, Adapted k (X k)) (hG : ∀ k, Adapted k (G k)) :
    ∀ k, Adapted k (accInc P X G k)
  | 0 => fun _ _ _ => rfl
  | k + 1 => by
    intro ω ω' hω
    have ha := alive_adapted hG k ω ω' (fun i hi => hω i (by omega))
    have hA := accInc_adapted hX hG k ω ω' (fun i hi => hω i (by omega))
    simp only at ha
    simp only [accInc]
    split_ifs with h1 h2 h3 h3
    · rw [hA, condAbsInc_adapted hX ⟨k, h1⟩ ω ω' (fun i hi => hω i (by simp at hi; omega))]
    · exact absurd (ha ▸ h2) h3
    · exact absurd (ha ▸ h3) h2
    · exact hA
    · exact hA

theorem accInc_nonneg (hP : IsPMF P) : ∀ k ω, 0 ≤ accInc P X G k ω
  | 0, _ => le_rfl
  | k + 1, ω => by
    have h0 := accInc_nonneg hP k ω
    simp only [accInc]
    split_ifs
    · have : 0 ≤ condAbsInc P X ⟨k, by omega⟩ ω :=
        sum_nonneg fun a _ => mul_nonneg (hP.1 _ a) (abs_nonneg _)
      linarith
    all_goals exact h0

theorem accInc_eq_sum_of_alive {ω : Fin n → α} (hall : ∀ i : Fin n, G i ω) :
    ∀ k, k ≤ n → accInc P X G k ω =
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), condAbsInc P X i ω
  | 0, _ => by simp [accInc]
  | k + 1, hk => by
    have hal : Alive G k ω := fun j hj => hall ⟨j, by omega⟩
    simp only [accInc, dif_pos (show k < n by omega), if_pos hal]
    rw [accInc_eq_sum_of_alive hall k (by omega)]
    have : (univ.filter fun i : Fin n => (i : ℕ) < k + 1) =
        insert ⟨k, by omega⟩ (univ.filter fun i : Fin n => (i : ℕ) < k) := by
      ext i; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]; omega
    rw [this, sum_insert (by simp)]
    ring

/-- One step of the exponential supermartingale. -/
theorem exp_step_le (p : α → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (Δ : α → ℝ)
    (hmean : ∑ a, p a * Δ a = 0) (C θ : ℝ) (hθ : 0 ≤ θ) (hθC : θ * C < 1)
    (hΔ : ∀ a, p a ≠ 0 → |Δ a| ≤ C) :
    ∑ a, p a * Real.exp (θ * Δ a) ≤
      Real.exp (θ ^ 2 * C / (2 * (1 - θ * C)) * ∑ a, p a * |Δ a|) := by
  have hK : 0 < 2 * (1 - θ * C) := by linarith
  have hpt : ∀ a, p a * Real.exp (θ * Δ a) ≤
      p a * (1 + θ * Δ a + θ ^ 2 * C / (2 * (1 - θ * C)) * |Δ a|) := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    apply mul_le_mul_of_nonneg_left _ (hp0 a)
    have hC := hΔ a hpa
    have h1 := exp_le_one_add_add_sq_div (θ * Δ a) (θ * C)
      (by rw [abs_mul, abs_of_nonneg hθ]; exact mul_le_mul_of_nonneg_left hC hθ) hθC
    have h2 : (θ * Δ a) ^ 2 / (2 * (1 - θ * C)) ≤ θ ^ 2 * C / (2 * (1 - θ * C)) * |Δ a| := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hK.le
      have : Δ a ^ 2 ≤ C * |Δ a| := by
        rw [← sq_abs, sq]; exact mul_le_mul_of_nonneg_right hC (abs_nonneg _)
      calc (θ * Δ a) ^ 2 = θ ^ 2 * Δ a ^ 2 := by ring
        _ ≤ θ ^ 2 * (C * |Δ a|) := mul_le_mul_of_nonneg_left this (sq_nonneg θ)
        _ = θ ^ 2 * C * |Δ a| := by ring
    linarith
  calc ∑ a, p a * Real.exp (θ * Δ a)
      ≤ ∑ a, p a * (1 + θ * Δ a + θ ^ 2 * C / (2 * (1 - θ * C)) * |Δ a|) :=
        sum_le_sum fun a _ => hpt a
    _ = ∑ a, p a + θ * ∑ a, p a * Δ a +
          θ ^ 2 * C / (2 * (1 - θ * C)) * ∑ a, p a * |Δ a| := by
        rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
        refine sum_congr rfl fun a _ => by ring
    _ = 1 + θ ^ 2 * C / (2 * (1 - θ * C)) * ∑ a, p a * |Δ a| := by rw [hp1, hmean]; ring
    _ ≤ _ := by linarith [Real.add_one_le_exp (θ ^ 2 * C / (2 * (1 - θ * C)) *
          ∑ a, p a * |Δ a|)]

/-- A martingale with respect to the coordinate exposure. -/
def IsExposureMartingale (P : Fin n → α → ℝ) (X : ℕ → (Fin n → α) → ℝ) : Prop :=
  (∀ k, Adapted k (X k)) ∧
    ∀ (i : Fin n) ω, X i ω = ∑ a, P i a * X (i + 1) (Function.update ω i a)

/-- The expectation of the final value of an exposure martingale is its initial value. -/
theorem IsExposureMartingale.pE_eq (hP : IsPMF P) (hX : IsExposureMartingale P X)
    (ω₀ : Fin n → α) : ∀ k, k ≤ n → pE P (X k) = X 0 ω₀
  | 0, _ => by
    have : X 0 = fun _ => X 0 ω₀ := funext fun ω =>
      hX.1 0 ω ω₀ fun i hi => absurd hi (by omega)
    rw [this, pE_const hP]
  | k + 1, hk => by
    rw [← hX.pE_eq hP ω₀ k (by omega), ← pE_resample hP ⟨k, by omega⟩ (X (k + 1))]
    congr 1
    funext ω
    exact (hX.2 ⟨k, by omega⟩ ω).symm

/-- **Freedman's inequality** (upper tail) for a stopped exposure martingale. -/
theorem freedman_upper (hP : IsPMF P) (hX : IsExposureMartingale P X)
    (hG : ∀ k, Adapted k (G k)) (C s lam : ℝ) (hC : 0 < C) (hs : 0 < s) (hlam : 0 < lam)
    (hinc : ∀ (i : Fin n) ω, Alive G i ω → ∀ a, P i a ≠ 0 →
      |X (i + 1) (Function.update ω i a) - X i ω| ≤ C)
    (hacc : ∀ (i : Fin n) ω, Alive G i ω →
      ∑ j : Fin n with j ≤ i, condAbsInc P X j ω ≤ s) :
    pProb P (fun ω => lam ≤ X n ω - X 0 ω ∧ ∀ i : Fin n, G i ω) ≤
      Real.exp (-(lam ^ 2 / (2 * C * (lam + s)))) := by
  classical
  set θ := lam / (C * (lam + s)) with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθC : θ * C = lam / (lam + s) := by rw [hθdef]; field_simp
  have hθC1 : θ * C < 1 := by rw [hθC, div_lt_one (by positivity)]; linarith
  set ψ := θ ^ 2 * C / (2 * (1 - θ * C)) with hψdef
  have hψ0 : 0 ≤ ψ := div_nonneg (by positivity) (by linarith)
  set Z : ℕ → (Fin n → α) → ℝ := fun k ω =>
    Real.exp (θ * (stopped X G k ω - X 0 ω) - ψ * accInc P X G k ω) with hZ
  have hX0 : ∀ ω ω', X 0 ω = X 0 ω' := fun ω ω' => hX.1 0 ω ω' fun i hi => absurd hi (by omega)
  -- supermartingale step
  have hsuper : ∀ (i : Fin n) ω,
      ∑ a, P i a * Z (i + 1) (Function.update ω i a) ≤ Z i ω := by
    intro i ω
    have hupdY : ∀ a, stopped X G i (Function.update ω i a) = stopped X G i ω := fun a =>
      (stopped_adapted hX.1 hG i).update i le_rfl ω a
    have hupdA : ∀ a, accInc P X G i (Function.update ω i a) = accInc P X G i ω := fun a =>
      (accInc_adapted hX.1 hG i).update i le_rfl ω a
    have hupdAl : ∀ a, (Alive G i (Function.update ω i a) ↔ Alive G i ω) := fun a => by
      have := (alive_adapted hG i).update i le_rfl ω a
      rw [this]
    have hupd0 : ∀ a, X 0 (Function.update ω i a) = X 0 ω := fun a => hX0 _ _
    have hupdD : ∀ a, condAbsInc P X ⟨i, i.2⟩ (Function.update ω i a) = condAbsInc P X i ω :=
      fun a => (condAbsInc_adapted hX.1 i).update i le_rfl ω a
    by_cases hal : Alive G i ω
    · have hYi : stopped X G i ω = X i ω :=
        stopped_eq_of_alive i (by
          rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
          · left; exact h
          · right; exact hal.mono (by omega))
      have hZa : ∀ a, Z (i + 1) (Function.update ω i a) = Z i ω *
          Real.exp (θ * (X (i + 1) (Function.update ω i a) - X i ω) -
            ψ * condAbsInc P X i ω) := by
        intro a
        simp only [hZ, stopped, accInc, dif_pos i.2, (hupdAl a).mpr hal, if_true, hupdA a,
          hupd0 a, hupdD a]
        rw [← Real.exp_add, hYi]
        congr 1; ring
      simp_rw [hZa]
      have hmean : ∑ a, P i a * (X (i + 1) (Function.update ω i a) - X i ω) = 0 := by
        simp_rw [mul_sub]; rw [sum_sub_distrib, ← sum_mul, hP.2 i, one_mul, ← hX.2 i ω]; ring
      have hstep := exp_step_le (P i) (hP.1 i) (hP.2 i)
        (fun a => X (i + 1) (Function.update ω i a) - X i ω) hmean C θ hθ0.le hθC1
        (fun a ha => hinc i ω hal a ha)
      calc ∑ a, P i a * (Z i ω * Real.exp (θ * (X (↑i + 1) (Function.update ω i a) - X (↑i) ω) -
              ψ * condAbsInc P X i ω))
          = Z i ω * Real.exp (-(ψ * condAbsInc P X i ω)) *
              ∑ a, P i a * Real.exp (θ * (X (↑i + 1) (Function.update ω i a) - X (↑i) ω)) := by
            rw [mul_sum]; refine sum_congr rfl fun a _ => ?_
            rw [sub_eq_add_neg, Real.exp_add]; ring
        _ ≤ Z i ω * Real.exp (-(ψ * condAbsInc P X i ω)) *
              Real.exp (ψ * condAbsInc P X i ω) := by
            apply mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = Z i ω := by rw [mul_assoc, ← Real.exp_add]; simp
    · have hZa : ∀ a, Z (i + 1) (Function.update ω i a) = Z i ω := by
        intro a
        have hn : ¬ Alive G i (Function.update ω i a) := fun h => hal ((hupdAl a).mp h)
        simp only [hZ, stopped, accInc, dif_pos i.2, hn, if_false, hupdA a, hupd0 a, hupdY a]
      simp_rw [hZa]
      rw [← sum_mul, hP.2 i, one_mul]
  -- expectation of `Z n` is at most `1`
  have hEZ : ∀ k, k ≤ n → pE P (Z k) ≤ 1 := by
    intro k
    induction k with
    | zero =>
      intro _
      have : Z 0 = fun _ => 1 := by funext ω; simp [hZ, stopped, accInc]
      rw [this, pE_const hP]
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      rw [← pE_resample hP ⟨k, hk'⟩]
      refine le_trans (pE_mono hP fun ω => ?_) (ih (by omega))
      exact hsuper ⟨k, hk'⟩ ω
  -- Markov
  have hev : ∀ ω, (lam ≤ X n ω - X 0 ω ∧ ∀ i : Fin n, G i ω) →
      Real.exp (θ * lam - ψ * s) ≤ Z n ω := by
    rintro ω ⟨hl, hall⟩
    have hYn : stopped X G n ω = X n ω := by
      apply stopped_eq_of_alive
      rcases Nat.eq_zero_or_pos n with h | h
      · left; exact h
      · right; exact fun j hj => hall ⟨j, by omega⟩
    have hAn : accInc P X G n ω ≤ s := by
      rw [accInc_eq_sum_of_alive hall n le_rfl]
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp; exact hs.le
      · have := hacc ⟨n - 1, by omega⟩ ω (fun j hj => hall ⟨j, by omega⟩)
        refine le_of_eq_of_le (sum_congr ?_ fun _ _ => rfl) this
        ext i; simp only [mem_filter, mem_univ, true_and, Fin.le_def]; omega
    simp only [hZ]
    apply Real.exp_le_exp.mpr
    rw [hYn]
    nlinarith [mul_le_mul_of_nonneg_left hl hθ0.le, mul_le_mul_of_nonneg_left hAn hψ0]
  have hprob : pProb P (fun ω => lam ≤ X n ω - X 0 ω ∧ ∀ i : Fin n, G i ω) *
      Real.exp (θ * lam - ψ * s) ≤ 1 := by
    unfold pProb
    rw [mul_comm, ← pE_const_mul]
    refine le_trans (pE_mono hP fun ω => ?_) (hEZ n le_rfl)
    split_ifs with h
    · rw [mul_one]; exact hev ω h
    · rw [mul_zero]; exact (Real.exp_pos _).le
  have hval : θ * lam - ψ * s = lam ^ 2 / (2 * C * (lam + s)) := by
    rw [hψdef, hθC, hθdef]
    have h1 : 1 - lam / (lam + s) = s / (lam + s) := by field_simp; ring
    rw [h1]
    field_simp
    ring
  rw [hval] at hprob
  rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)]
  exact hprob

theorem IsExposureMartingale.neg (hX : IsExposureMartingale P X) :
    IsExposureMartingale P (fun k ω => -X k ω) := by
  refine ⟨fun k ω ω' h => by simp only [hX.1 k ω ω' h], fun i ω => ?_⟩
  simp only
  rw [hX.2 i ω, ← sum_neg_distrib]
  exact sum_congr rfl fun a _ => by ring

/-- **Freedman's inequality** (two-sided) for a stopped exposure martingale. -/
theorem freedman_two_sided (hP : IsPMF P) (hX : IsExposureMartingale P X)
    (hG : ∀ k, Adapted k (G k)) (C s lam : ℝ) (hC : 0 < C) (hs : 0 < s) (hlam : 0 < lam)
    (hinc : ∀ (i : Fin n) ω, Alive G i ω → ∀ a, P i a ≠ 0 →
      |X (i + 1) (Function.update ω i a) - X i ω| ≤ C)
    (hacc : ∀ (i : Fin n) ω, Alive G i ω →
      ∑ j : Fin n with j ≤ i, condAbsInc P X j ω ≤ s) :
    pProb P (fun ω => lam ≤ |X n ω - X 0 ω| ∧ ∀ i : Fin n, G i ω) ≤
      2 * Real.exp (-(lam ^ 2 / (2 * C * (lam + s)))) := by
  have h1 := freedman_upper hP hX hG C s lam hC hs hlam hinc hacc
  have h2 := freedman_upper hP hX.neg hG C s lam hC hs hlam
    (fun i ω h a ha => by
      have := hinc i ω h a ha
      rw [← abs_neg]; convert this using 2; ring)
    (fun i ω h => by
      have := hacc i ω h
      refine le_trans (le_of_eq (sum_congr rfl fun j _ => ?_)) this
      unfold condAbsInc
      refine sum_congr rfl fun a _ => ?_
      rw [← abs_neg]; congr 2; ring)
  refine le_trans (pProb_mono hP (T := fun ω => (lam ≤ X n ω - X 0 ω ∧ ∀ i : Fin n, G i ω) ∨
    (lam ≤ -X n ω - -X 0 ω ∧ ∀ i : Fin n, G i ω)) fun ω h => ?_) ?_
  · rcases le_abs'.mp h.1 with h' | h'
    · right; exact ⟨by linarith, h.2⟩
    · left; exact ⟨h', h.2⟩
  · refine (pProb_or_le hP _ _).trans ?_
    linarith

end Freedman

end Pseudorandom
