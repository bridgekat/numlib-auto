/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter07.Section01
import Numlib.LinearAlgebra.Matrix.Aeval
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Singular difference equations

Section 8.8 of [benIsrael2003generalized] solves singular difference
equations on all nonnegative times. A regular pencil separates a
stable-range initial value from the consistency restrictions.

## Deviations from the source

* **Theorem 13** uses a regular pencil. This is equivalent to tractability
  together with existence of a solution for the given forcing.
* **Equation (120)** uses the future sum at time zero.
* **Exercise 31** uses multiplication by `B⁻¹` to obtain the identity
  right-hand coefficient. The pencil normalization at zero gives the
  negatives of both coefficients.
-/

namespace BenIsraelGreville.Chapter08

open Matrix
open Chapter04 (drazinInverse matrixIndex)
open scoped BigOperators

variable {n : Type*} [Fintype n]

/-- **Equation (111)** of [benIsrael2003generalized], Chapter 8.
A solution of the difference equation at every nonnegative time. -/
def IsDifferenceSolution (A B : Matrix n n ℂ) (f x : ℕ → n → ℂ) : Prop :=
  ∀ t, A *ᵥ x (t + 1) = B *ᵥ x t + f t

/-- **Definition 1(a)** of [benIsrael2003generalized], Chapter 8.
An initial vector is consistent when it extends to a solution on all
nonnegative times. -/
def IsConsistentInitialVector (A B : Matrix n n ℂ) (f : ℕ → n → ℂ) (c : n → ℂ) : Prop :=
  ∃ x, IsDifferenceSolution A B f x ∧ x 0 = c

/-- **Definition 1(b)** of [benIsrael2003generalized], Chapter 8.
A tractable equation has a unique solution for every consistent initial vector. -/
def IsTractableDifferenceEquation (A B : Matrix n n ℂ) (f : ℕ → n → ℂ) : Prop :=
  ∀ c, IsConsistentInitialVector A B f c →
    ∃! x, IsDifferenceSolution A B f x ∧ x 0 = c

variable [DecidableEq n]

/-- The first coefficient of the normalized pencil in **Equation (113)**. -/
noncomputable def normalizedDifferenceA (A B : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  (z • A - B)⁻¹ * A

/-- The second coefficient of the normalized pencil in **Equation (113)**. -/
noncomputable def normalizedDifferenceB (A B : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  (z • A - B)⁻¹ * B

/-- **Exercise 28**, Equation (121) of [benIsrael2003generalized], Chapter 8.
Normalizing a regular pencil makes its normalized coefficients commute. -/
theorem exercise_8_28 (A B : Matrix n n ℂ) (z : ℂ) (hz : IsUnit (z • A - B)) :
    z • normalizedDifferenceA A B z - normalizedDifferenceB A B z = 1 ∧
      Commute (normalizedDifferenceA A B z) (normalizedDifferenceB A B z) := by
  let C := normalizedDifferenceA A B z
  let D := normalizedDifferenceB A B z
  have h : z • C - D = 1 := by
    change z • ((z • A - B)⁻¹ * A) - (z • A - B)⁻¹ * B = 1
    rw [← Matrix.mul_smul, ← Matrix.mul_sub,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hz)]
  have he : D = z • C - 1 := by
    have h' := congrArg (fun M : Matrix n n ℂ => z • C - M) h
    simpa only [sub_sub_cancel] using h'
  refine ⟨h, ?_⟩
  change Commute C D
  rw [he]
  change C * (z • C - 1) = (z • C - 1) * C
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul]

/-- **Equation (113)** of [benIsrael2003generalized], Chapter 8.
An invertible pencil factor transports the difference equation, including
the value of the forcing at every time. -/
theorem isDifferenceSolution_normalized_iff (A B : Matrix n n ℂ) (z : ℂ)
    (hz : IsUnit (z • A - B)) (f x : ℕ → n → ℂ) :
    IsDifferenceSolution (normalizedDifferenceA A B z) (normalizedDifferenceB A B z)
      (fun t => (z • A - B)⁻¹ *ᵥ f t) x ↔ IsDifferenceSolution A B f x := by
  let M := z • A - B
  have hu : IsUnit M⁻¹ := isUnit_nonsing_inv_iff.mpr hz
  change (∀ t, (M⁻¹ * A) *ᵥ x (t + 1) = (M⁻¹ * B) *ᵥ x t + M⁻¹ *ᵥ f t) ↔ _
  simp only [← mulVec_mulVec, ← mulVec_add, (mulVec_injective_of_isUnit hu).eq_iff]
  rfl

private theorem mulVec_mem_range_of_commute {A T : Matrix n n ℂ} (h : Commute T A)
    {j : ℕ} {x : n → ℂ} (hx : x ∈ LinearMap.range (A ^ j).mulVecLin) :
    T *ᵥ x ∈ LinearMap.range (A ^ j).mulVecLin := by
  obtain ⟨y, hy⟩ := hx
  change (A ^ j) *ᵥ y = x at hy
  refine ⟨T *ᵥ y, ?_⟩
  change (A ^ j) *ᵥ (T *ᵥ y) = T *ᵥ x
  rw [← hy, mulVec_mulVec, mulVec_mulVec, (h.pow_right j).eq]

private theorem differenceSolution_eq_pow_mulVec {A B : Matrix n n ℂ}
    {x : ℕ → n → ℂ} {z : ℂ} (hB : B = z • A - 1)
    (hx : IsDifferenceSolution A B 0 x) :
    (∀ t, x t ∈ LinearMap.range (A ^ matrixIndex A).mulVecLin) ∧
      ∀ t, x t = (drazinInverse A * B) ^ t *ᵥ x 0 := by
  have hRange (j : ℕ) (t : ℕ) : x t ∈ LinearMap.range (A ^ j).mulVecLin := by
    induction j generalizing t with
    | zero =>
      exact ⟨x t, by change A ^ 0 *ᵥ x t = x t; rw [pow_zero, one_mulVec]⟩
    | succ j ih =>
      obtain ⟨u, hu⟩ := ih t
      obtain ⟨v, hv⟩ := ih (t + 1)
      change (A ^ j) *ᵥ u = x t at hu
      change (A ^ j) *ᵥ v = x (t + 1) at hv
      refine ⟨z • u - v, ?_⟩
      change A ^ (j + 1) *ᵥ (z • u - v) = x t
      have he := hx t
      rw [Pi.zero_apply, add_zero, hB, sub_mulVec, smul_mulVec, one_mulVec] at he
      rw [pow_succ', ← mulVec_mulVec, mulVec_sub, mulVec_smul, hu, hv,
        mulVec_sub, mulVec_smul, he]
      abel
  have hD := Chapter04.isDrazinInverseAt_drazinInverse A
  have hstep (t : ℕ) : (drazinInverse A * B) *ᵥ x t = x (t + 1) := by
    have he := hx t
    rw [Pi.zero_apply, add_zero] at he
    rw [← mulVec_mulVec, ← he, mulVec_mulVec, hD.commute.symm.eq, ← mulVec_mulVec]
    exact Chapter04.mulVec_drazinInverse_of_mem_stableRange (hRange _ _)
  refine ⟨hRange _, ?_⟩
  intro t
  induction t with
  | zero => rw [pow_zero, one_mulVec]
  | succ t ih => rw [← hstep t, ih, mulVec_mulVec, ← pow_succ']

private theorem range_mul_drazinInverse (A : Matrix n n ℂ) :
    LinearMap.range (A * drazinInverse A).mulVecLin =
      LinearMap.range (A ^ matrixIndex A).mulVecLin := by
  let D := drazinInverse A
  have hr : LinearMap.range D.mulVecLin = LinearMap.range (A ^ matrixIndex A).mulVecLin :=
    (Chapter07.drazin_unique_outerInverse_range_ker A le_rfl).1.2.1
  have hD := Chapter04.isDrazinInverseAt_drazinInverse A
  rw [← hr]
  apply le_antisymm
  · rw [hD.commute.eq, mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · rintro x ⟨y, hy⟩
    change D *ᵥ y = x at hy
    refine ⟨D *ᵥ y, ?_⟩
    change (A * D) *ᵥ (D *ᵥ y) = x
    rw [mulVec_mulVec, hD.commute.eq, hD.outer, hy]

private theorem differenceSolution_pow_mulVec {A B : Matrix n n ℂ}
    (hBA : Commute B A) {c : n → ℂ}
    (hc : c ∈ LinearMap.range (A ^ matrixIndex A).mulVecLin) :
    IsDifferenceSolution A B 0 (fun t => (drazinInverse A * B) ^ t *ᵥ c) := by
  let T := drazinInverse A * B
  have hAT : Commute A T :=
    (Chapter04.isDrazinInverseAt_drazinInverse A).commute.mul_right hBA.symm
  intro t
  have hT : T ^ t *ᵥ c ∈ LinearMap.range (A ^ matrixIndex A).mulVecLin :=
    mulVec_mem_range_of_commute (hAT.symm.pow_left t) hc
  have hB := mulVec_mem_range_of_commute hBA hT
  change A *ᵥ (T ^ (t + 1) *ᵥ c) = B *ᵥ (T ^ t *ᵥ c) + 0
  rw [pow_succ', ← mulVec_mulVec, add_zero]
  change A *ᵥ ((drazinInverse A * B) *ᵥ (T ^ t *ᵥ c)) = _
  rw [← mulVec_mulVec]
  exact Chapter04.mulVec_drazinInverse_of_mem_stableRange hB

/-- **Theorem 12**, Equation (116) of [benIsrael2003generalized], Chapter 8.
A homogeneous solution starts in the stable range of the normalized
coefficient and is propagated by the powers of its Drazin step. -/
theorem theorem_12 (A B : Matrix n n ℂ) (z : ℂ) (hz : IsUnit (z • A - B))
    (x : ℕ → n → ℂ) :
    let C := normalizedDifferenceA A B z
    let D := normalizedDifferenceB A B z
    IsDifferenceSolution A B 0 x ↔
      x 0 ∈ LinearMap.range (C ^ matrixIndex C).mulVecLin ∧
        ∀ t, x t = (drazinInverse C * D) ^ t *ᵥ x 0 := by
  intro C D
  have he : IsDifferenceSolution C D 0 x ↔ IsDifferenceSolution A B 0 x := by
    have h := isDifferenceSolution_normalized_iff A B z hz 0 x
    have hf : (fun t : ℕ => (z • A - B)⁻¹ *ᵥ (0 : ℕ → n → ℂ) t) = 0 := by
      funext t
      simp
    rw [hf] at h
    exact h
  have ⟨hsub, hc⟩ := exercise_8_28 A B z hz
  change z • C - D = 1 at hsub
  have hD : D = z • C - 1 := by
    simpa only [sub_sub_cancel] using congrArg (fun M : Matrix n n ℂ => z • C - M) hsub
  rw [← he]
  constructor
  · intro hx
    obtain ⟨hr, hp⟩ := differenceSolution_eq_pow_mulVec hD hx
    exact ⟨hr 0, hp⟩
  · rintro ⟨hr, hx⟩
    have hseq := differenceSolution_pow_mulVec hc.symm hr
    exact (funext hx).symm ▸ hseq

/-- **Theorem 12**, Equation (116) of [benIsrael2003generalized], Chapter 8.
Initial consistency is exactly membership in the stable range of the
normalized coefficient. -/
theorem homogeneousInitialVector_consistent_iff (A B : Matrix n n ℂ) (z : ℂ)
    (hz : IsUnit (z • A - B)) (c : n → ℂ) :
    IsConsistentInitialVector A B 0 c ↔
      c ∈ LinearMap.range ((normalizedDifferenceA A B z) ^
        matrixIndex (normalizedDifferenceA A B z)).mulVecLin := by
  let C := normalizedDifferenceA A B z
  let D := normalizedDifferenceB A B z
  constructor
  · rintro ⟨x, hx, h0⟩
    exact h0 ▸ ((theorem_12 A B z hz x).mp hx).1
  · intro hc
    let x (t : ℕ) := (drazinInverse C * D) ^ t *ᵥ c
    have h0 : x 0 = c := by simp [x, one_mulVec]
    refine ⟨x, (theorem_12 A B z hz x).mpr ⟨h0.symm ▸ hc, ?_⟩, h0⟩
    intro t
    rw [h0]

/-- **Theorem 12**, Equation (115) of [benIsrael2003generalized], Chapter 8.
Projecting an arbitrary vector onto the stable range parametrizes all
homogeneous initial values. At positive times the powers already discard
the complementary part of that vector. -/
theorem homogeneousSolution_iff_exists_projectedStart (A B : Matrix n n ℂ) (z : ℂ)
    (hz : IsUnit (z • A - B)) (x : ℕ → n → ℂ) :
    let C := normalizedDifferenceA A B z
    let D := normalizedDifferenceB A B z
    IsDifferenceSolution A B 0 x ↔ ∃ y : n → ℂ,
      x 0 = (C * drazinInverse C) *ᵥ y ∧
        ∀ t : ℕ, 0 < t → x t = (drazinInverse C * D) ^ t *ᵥ y := by
  intro C D
  let V := drazinInverse C
  let P := C * V
  let T := V * D
  have hV : IsDrazinInverseAt (matrixIndex C) C V :=
    Chapter04.isDrazinInverseAt_drazinInverse C
  have hP : LinearMap.range P.mulVecLin = LinearMap.range (C ^ matrixIndex C).mulVecLin :=
    range_mul_drazinInverse C
  have hD : D = z • C - 1 := by
    have h := (exercise_8_28 A B z hz).1
    change z • C - D = 1 at h
    simpa only [sub_sub_cancel] using congrArg (fun M : Matrix n n ℂ => z • C - M) h
  have hDP : D * P = P * D := by
    rw [hD]
    change (z • C - 1) * (C * V) = (C * V) * (z • C - 1)
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    have he : C * (C * V) = (C * V) * C := by
      rw [Matrix.mul_assoc C V C, hV.commute.eq]
    rw [he]
  have hTP : T * P = T := by
    change (V * D) * P = V * D
    rw [Matrix.mul_assoc V D P, hDP, ← Matrix.mul_assoc V P D]
    change V * (C * V) * D = V * D
    rw [← Matrix.mul_assoc V C V, hV.outer]
  have hp (t : ℕ) (ht : 0 < t) : T ^ t * P = T ^ t := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    rw [pow_succ, Matrix.mul_assoc, hTP]
  have h12 : IsDifferenceSolution A B 0 x ↔
      x 0 ∈ LinearMap.range (C ^ matrixIndex C).mulVecLin ∧
        ∀ t : ℕ, x t = T ^ t *ᵥ x 0 := theorem_12 A B z hz x
  rw [h12, ← hP]
  constructor
  · rintro ⟨⟨y, hy⟩, hx⟩
    change P *ᵥ y = x 0 at hy
    refine ⟨y, hy.symm, fun t ht => ?_⟩
    change x t = T ^ t *ᵥ y
    rw [hx t, ← hy, mulVec_mulVec, hp t ht]
  · rintro ⟨y, h0, hx⟩
    refine ⟨⟨y, h0.symm⟩, fun t => ?_⟩
    by_cases ht : t = 0
    · subst t
      rw [pow_zero, one_mulVec]
    · rw [h0, mulVec_mulVec, hp t (Nat.pos_of_ne_zero ht)]
      exact hx t (Nat.pos_of_ne_zero ht)

private theorem nontrivialSolution_of_singular_pencil (A B : Matrix n n ℂ)
    (h : ∀ z : ℂ, ¬ IsUnit (z • A - B)) :
    ∃ x, IsDifferenceSolution A B 0 x ∧ x 0 = 0 ∧ x ≠ 0 := by
  classical
  let ι := Fin (Fintype.card n + 1)
  let z (i : ι) : ℂ := (i : ℕ)
  have hz : Function.Injective z := by
    intro i j hij
    exact Fin.ext (Nat.cast_injective (R := ℂ) hij)
  have hv (i : ι) : ∃ v ≠ 0, ((z i) • A - B) *ᵥ v = 0 := by
    apply exists_mulVec_eq_zero_iff.mpr
    have hi := h (z i)
    rwa [isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hi
  choose v hv0 hvz using hv
  have heq (i : ι) : B *ᵥ v i = z i • (A *ᵥ v i) := by
    have hi := hvz i
    rw [sub_mulVec, smul_mulVec, sub_eq_zero] at hi
    exact hi.symm
  have hdep : ¬ LinearIndependent ℂ v := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    change Fintype.card (Fin (Fintype.card n + 1)) ≤ Module.finrank ℂ (n → ℂ) at hcard
    simp only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at hcard
    omega
  obtain ⟨c, hc0, ⟨i, hi⟩⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let x (t : ℕ) := ∑ j : ι, (c j * z j ^ t) • v j
  refine ⟨x, ?_, by simpa only [x, pow_zero, mul_one] using hc0, ?_⟩
  · intro t
    change A *ᵥ (∑ j : ι, (c j * z j ^ (t + 1)) • v j) =
      B *ᵥ (∑ j : ι, (c j * z j ^ t) • v j) + 0
    rw [add_zero, mulVec_sum, mulVec_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mulVec_smul, mulVec_smul, heq j, smul_smul, pow_succ, mul_assoc]
  · intro hn
    have hvi : ∃ j : n, v i j ≠ 0 := by
      by_contra! hzero
      exact hv0 i (funext hzero)
    obtain ⟨j, hj⟩ := hvi
    let e (l : ι) := c l * v l j
    have h0 : (vandermonde z)ᵀ *ᵥ e = 0 := by
      funext t
      have ht := congrFun (congrFun hn (t : ℕ)) j
      simp only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ht
      change ∑ l : ι, z l ^ (t : ℕ) * (c l * v l j) = 0
      rw [← ht]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hu : IsUnit (vandermonde z)ᵀ := by
      rw [isUnit_iff_isUnit_det, det_transpose, isUnit_iff_ne_zero, det_vandermonde_ne_zero_iff]
      exact hz
    have he := mulVec_injective_of_isUnit hu (h0.trans (mulVec_zero _).symm)
    exact mul_ne_zero hi hj (congrFun he i)

/-- **Theorem 11** of [benIsrael2003generalized], Chapter 8.
A homogeneous matrix difference equation is tractable exactly when its
pencil is regular. For a singular pencil, exponential solutions with
distinct scalars give a nonzero solution with zero initial vector. -/
theorem theorem_11 (A B : Matrix n n ℂ) :
    IsTractableDifferenceEquation A B 0 ↔ ∃ z : ℂ, IsUnit (z • A - B) := by
  constructor
  · intro h
    by_contra! hs
    obtain ⟨x, hx, h0, hn⟩ := nontrivialSolution_of_singular_pencil A B hs
    have hz : IsDifferenceSolution A B 0 0 ∧ (0 : ℕ → n → ℂ) 0 = 0 := by
      simp [IsDifferenceSolution]
    obtain ⟨y, _, hy⟩ := h 0 ⟨0, hz⟩
    exact hn ((hy x ⟨hx, h0⟩).trans (hy 0 hz).symm)
  · rintro ⟨z, hz⟩ c ⟨x, hx, h0⟩
    refine ⟨x, ⟨hx, h0⟩, ?_⟩
    rintro y ⟨hy, hy0⟩
    have hpx := ((theorem_12 A B z hz x).mp hx).2
    have hpy := ((theorem_12 A B z hz y).mp hy).2
    funext t
    rw [hpy, hpx, hy0, h0]

/-- **Example 1**, Equations (109)–(110) of [benIsrael2003generalized],
Chapter 8. In the equation with right-hand coefficient `1`, every
solution lies in the stable range and advances by the Drazin inverse. -/
theorem differenceSolution_iff_drazin (A : Matrix n n ℂ) (x : ℕ → n → ℂ) :
    IsDifferenceSolution A 1 0 x ↔
      (∀ t, x t ∈ LinearMap.range (A ^ matrixIndex A).mulVecLin) ∧
      ∀ t, x (t + 1) = drazinInverse A *ᵥ x t := by
  constructor
  · intro h
    have he (t : ℕ) : A *ᵥ x (t + 1) = x t := by
      simpa only [one_mulVec, Pi.zero_apply, add_zero] using h t
    have hr (k t : ℕ) : A ^ k *ᵥ x (t + k) = x t := by
      induction k with
      | zero => simp [one_mulVec]
      | succ k ih =>
        rw [pow_succ, ← mulVec_mulVec, ← Nat.add_assoc, he (t + k), ih]
    have hR (t : ℕ) : x t ∈ LinearMap.range (A ^ matrixIndex A).mulVecLin :=
      ⟨x (t + matrixIndex A), hr _ t⟩
    refine ⟨hR, fun t => ?_⟩
    have hD := Chapter04.isDrazinInverseAt_drazinInverse A
    rw [← he t, mulVec_mulVec, hD.commute.symm.eq, ← mulVec_mulVec]
    exact (Chapter04.mulVec_drazinInverse_of_mem_stableRange (hR (t + 1))).symm
  · rintro ⟨hR, hx⟩ t
    rw [hx t, one_mulVec, Pi.zero_apply, add_zero]
    exact Chapter04.mulVec_drazinInverse_of_mem_stableRange (hR t)

section ForcedResponse

open Finset

/-- The finite causal sum in **Equation (119)** of
[benIsrael2003generalized], Chapter 8. -/
def differencePastSum (T : Matrix n n ℂ) (g : ℕ → n → ℂ) (t : ℕ) : n → ℂ :=
  ∑ i ∈ range t, T ^ (t - 1 - i) *ᵥ g i

/-- The finite future sum in **Equation (119)** of
[benIsrael2003generalized], Chapter 8. -/
def differenceFutureSum (G : Matrix n n ℂ) (g : ℕ → n → ℂ) (k t : ℕ) : n → ℂ :=
  ∑ i ∈ range k, G ^ i *ᵥ g (t + i)

private theorem differencePastSum_succ (T : Matrix n n ℂ) (g : ℕ → n → ℂ) (t : ℕ) :
    differencePastSum T g (t + 1) = T *ᵥ differencePastSum T g t + g t := by
  unfold differencePastSum
  rw [sum_range_succ, mulVec_sum]
  have ht : t + 1 - 1 - t = 0 := by omega
  rw [ht, pow_zero, one_mulVec]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hit := mem_range.mp hi
  rw [mulVec_mulVec, ← pow_succ', show t + 1 - 1 - i = (t - 1 - i) + 1 by omega]

private theorem differenceFutureSum_sub_step (G : Matrix n n ℂ) (g : ℕ → n → ℂ) (k t : ℕ) :
    differenceFutureSum G g k t - G *ᵥ differenceFutureSum G g k (t + 1) =
      g t - G ^ k *ᵥ g (t + k) := by
  let f (i : ℕ) := G ^ i *ᵥ g (t + i)
  have he : G *ᵥ differenceFutureSum G g k (t + 1) = ∑ i ∈ range k, f (i + 1) := by
    unfold differenceFutureSum
    rw [mulVec_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [f, mulVec_mulVec, pow_succ']
    congr 2
    omega
  rw [he]
  change (∑ i ∈ range k, f i) - (∑ i ∈ range k, f (i + 1)) = _
  rw [← sum_sub_distrib, sum_range_sub']
  simp [f, one_mulVec]

private theorem commute_drazin_right {A B : Matrix n n ℂ} (h : Commute A B) :
    Commute A (drazinInverse B) := by
  obtain ⟨p, hp⟩ := (Chapter04.theorem_4_7 B).1
  rw [hp]
  exact h.aeval_right p

private theorem mul_drazinInverse_mul_complement {A B : Matrix n n ℂ} {z : ℂ}
    (hB : B = z • A - 1) :
    B * drazinInverse B * (1 - A * drazinInverse A) = 1 - A * drazinInverse A := by
  let k := matrixIndex A
  let D := drazinInverse A
  let Q := 1 - A * D
  let H := -(∑ i ∈ range k, (z • A) ^ i)
  have hD : IsDrazinInverseAt k A D := Chapter04.isDrazinInverseAt_drazinInverse A
  have hAQ : A ^ k * Q = 0 := by
    change A ^ k * (1 - A * D) = 0
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← pow_succ, hD.stable, sub_self]
  have hBH : B * H * Q = Q := by
    have h : B * H = 1 - (z • A) ^ k := by
      change B * -(∑ i ∈ range k, (z • A) ^ i) = _
      rw [hB, Matrix.mul_neg, mul_geom_sum, neg_sub]
    rw [h, Matrix.sub_mul, Matrix.one_mul, smul_pow, Matrix.smul_mul, hAQ, smul_zero, sub_zero]
  have hBA : Commute B A := by
    rw [hB]
    exact (((Commute.refl A).smul_right z).sub_right (Commute.one_right A)).symm
  have hComm : Commute B H := by
    change B * -(∑ i ∈ range k, (z • A) ^ i) =
      -(∑ i ∈ range k, (z • A) ^ i) * B
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sum, Matrix.sum_mul]
    congr 1
    exact sum_congr rfl fun i _ => ((hBA.smul_right z).pow_right i).eq
  have hFix (l : ℕ) : (B * H) ^ l * Q = Q := by
    induction l with
    | zero => rw [pow_zero, Matrix.one_mul]
    | succ l ih => rw [pow_succ', Matrix.mul_assoc, ih, hBH]
  change B * drazinInverse B * Q = Q
  apply ext_iff_mulVec.mpr
  intro x
  have hmem : Q *ᵥ x ∈ LinearMap.range (B ^ matrixIndex B).mulVecLin := by
    refine ⟨(H ^ matrixIndex B * Q) *ᵥ x, ?_⟩
    change B ^ matrixIndex B *ᵥ ((H ^ matrixIndex B * Q) *ᵥ x) = Q *ᵥ x
    rw [mulVec_mulVec, ← Matrix.mul_assoc, ← hComm.mul_pow, hFix]
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  exact Chapter04.mulVec_drazinInverse_of_mem_stableRange hmem

/-- The two forcing terms in **Equation (119)** of
[benIsrael2003generalized], Chapter 8, in normalized pencil coordinates. -/
noncomputable def differenceParticularResponse (A B : Matrix n n ℂ)
    (g : ℕ → n → ℂ) (t : ℕ) : n → ℂ :=
  let D := drazinInverse A
  let F := drazinInverse B
  let Q := 1 - A * D
  D *ᵥ differencePastSum (D * B) g t -
    (Q * F) *ᵥ differenceFutureSum (A * F) g (matrixIndex A) t

/-- **Theorem 13**, Equation (119) of [benIsrael2003generalized], Chapter 8.
The past and future responses together solve the normalized forced equation. -/
theorem differenceParticularResponse_solves {A B : Matrix n n ℂ}
    {z : ℂ} (hB : B = z • A - 1) (g : ℕ → n → ℂ) :
    IsDifferenceSolution A B g (differenceParticularResponse A B g) := by
  let k := matrixIndex A
  let D := drazinInverse A
  let F := drazinInverse B
  let P := A * D
  let Q := 1 - P
  let T := D * B
  let G := A * F
  let W := Q * F
  have hD : IsDrazinInverseAt k A D := Chapter04.isDrazinInverseAt_drazinInverse A
  have hAB : Commute A B := hB ▸ (((Commute.refl A).smul_right z).sub_right (Commute.one_right A))
  have hAF : Commute A F := commute_drazin_right hAB
  have hBD : Commute B D := commute_drazin_right hAB.symm
  have hAQ : Commute A Q :=
    (Commute.one_right A).sub_right ((Commute.refl A).mul_right hD.commute)
  have hBQ : Commute B Q :=
    (Commute.one_right B).sub_right (hAB.symm.mul_right hBD)
  have hQF : Commute Q F := commute_drazin_right hBQ.symm
  have hPT : P * T = B * D := by
    change (A * D) * (D * B) = B * D
    rw [← Matrix.mul_assoc (A * D) D B, hD.commute.eq, hD.outer, hBD.symm.eq]
  have hAW : A * W = Q * G := by
    change A * (Q * F) = Q * (A * F)
    rw [← Matrix.mul_assoc A Q F, hAQ.eq, Matrix.mul_assoc]
  have hBW : B * W = Q := by
    change B * (Q * F) = Q
    rw [hQF.eq, ← Matrix.mul_assoc]
    exact mul_drazinInverse_mul_complement hB
  have hQG : Q * G ^ k = 0 := by
    have hPower : A ^ k * Q = 0 := by
      change A ^ k * (1 - A * D) = 0
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← pow_succ, hD.stable, sub_self]
    change Q * (A * F) ^ k = 0
    rw [hAF.mul_pow, ← Matrix.mul_assoc, (hAQ.pow_left k).symm.eq, hPower, Matrix.zero_mul]
  let u (t : ℕ) := D *ᵥ differencePastSum T g t
  let v (t : ℕ) := W *ᵥ differenceFutureSum G g k t
  have hu (t : ℕ) : A *ᵥ u (t + 1) = B *ᵥ u t + P *ᵥ g t := by
    change A *ᵥ (D *ᵥ differencePastSum T g (t + 1)) =
      B *ᵥ (D *ᵥ differencePastSum T g t) + P *ᵥ g t
    rw [differencePastSum_succ, mulVec_mulVec, mulVec_add, mulVec_mulVec, hPT,
      ← mulVec_mulVec]
  have hv (t : ℕ) : A *ᵥ v (t + 1) = B *ᵥ v t - Q *ᵥ g t := by
    have he := congrArg (fun x => Q *ᵥ x) (differenceFutureSum_sub_step G g k t)
    rw [mulVec_sub, mulVec_sub, mulVec_mulVec (differenceFutureSum G g k (t + 1)) Q G,
      mulVec_mulVec (g (t + k)) Q (G ^ k), hQG, zero_mulVec, sub_zero] at he
    change A *ᵥ (W *ᵥ differenceFutureSum G g k (t + 1)) =
      B *ᵥ (W *ᵥ differenceFutureSum G g k t) - Q *ᵥ g t
    rw [mulVec_mulVec, mulVec_mulVec, hAW, hBW, ← he]
    abel
  intro t
  change A *ᵥ (u (t + 1) - v (t + 1)) = B *ᵥ (u t - v t) + g t
  have hg : P *ᵥ g t + Q *ᵥ g t = g t := by
    rw [← add_mulVec, show P + Q = 1 from add_sub_cancel _ _, one_mulVec]
  rw [mulVec_sub, mulVec_sub, hu, hv]
  calc
    _ = B *ᵥ u t - B *ᵥ v t + (P *ᵥ g t + Q *ᵥ g t) := by abel
    _ = _ := by rw [hg]

/-- The future response puts the second Drazin inverse on each forcing
vector in the printed form of **Equation (119)**. -/
theorem differenceParticularResponse_eq_past_sub_future {A B : Matrix n n ℂ}
    (hAB : Commute A B) (g : ℕ → n → ℂ) (t : ℕ) :
    differenceParticularResponse A B g t =
      drazinInverse A *ᵥ differencePastSum (drazinInverse A * B) g t -
        (1 - A * drazinInverse A) *ᵥ
          differenceFutureSum (A * drazinInverse B) (fun i => drazinInverse B *ᵥ g i)
            (matrixIndex A) t := by
  let Q := 1 - A * drazinInverse A
  let F := drazinInverse B
  let G := A * F
  have hF : Commute F G := (commute_drazin_right hAB).symm.mul_right (Commute.refl F)
  apply congrArg (fun u => drazinInverse A *ᵥ differencePastSum (drazinInverse A * B) g t - u)
  change (Q * F) *ᵥ differenceFutureSum G g (matrixIndex A) t =
    Q *ᵥ differenceFutureSum G (fun i => F *ᵥ g i) (matrixIndex A) t
  rw [← mulVec_mulVec]
  congr 1
  unfold differenceFutureSum
  rw [mulVec_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mulVec_mulVec, (hF.pow_right i).eq, ← mulVec_mulVec]

omit [DecidableEq n] in
private theorem differenceSolution_sub_particular {A B : Matrix n n ℂ}
    {g x y : ℕ → n → ℂ} (hy : IsDifferenceSolution A B g y) :
    IsDifferenceSolution A B g x ↔ IsDifferenceSolution A B 0 (fun t => x t - y t) := by
  constructor
  · intro hx t
    change A *ᵥ (x (t + 1) - y (t + 1)) = B *ᵥ (x t - y t) + 0
    rw [mulVec_sub, mulVec_sub, hx t, hy t]
    abel
  · intro hx t
    have h := hx t
    change A *ᵥ (x (t + 1) - y (t + 1)) = B *ᵥ (x t - y t) + 0 at h
    rw [mulVec_sub, mulVec_sub, add_zero] at h
    change A *ᵥ x (t + 1) = B *ᵥ x t + g t
    calc
      _ = (A *ᵥ x (t + 1) - A *ᵥ y (t + 1)) + A *ᵥ y (t + 1) := by abel
      _ = _ := by rw [h, hy t]; abel

/-- **Equation (119)** of [benIsrael2003generalized], Chapter 8.
Propagate the projected free vector and add the two forcing responses. -/
noncomputable def differenceRegularSolution (A B : Matrix n n ℂ) (z : ℂ)
    (f : ℕ → n → ℂ) (y : n → ℂ) (t : ℕ) : n → ℂ :=
  let C := normalizedDifferenceA A B z
  let D := normalizedDifferenceB A B z
  let g (i : ℕ) := (z • A - B)⁻¹ *ᵥ f i
  (drazinInverse C * D) ^ t *ᵥ ((C * drazinInverse C) *ᵥ y) +
    differenceParticularResponse C D g t

/-- **Theorem 13**, Equation (119) of [benIsrael2003generalized],
Chapter 8. A regular pencil gives exactly the solutions obtained by
varying the free initial vector in the formula. -/
theorem theorem_13 (A B : Matrix n n ℂ) (z : ℂ) (hz : IsUnit (z • A - B))
    (f x : ℕ → n → ℂ) :
    IsDifferenceSolution A B f x ↔ ∃ y, x = differenceRegularSolution A B z f y := by
  let C := normalizedDifferenceA A B z
  let D := normalizedDifferenceB A B z
  let g (i : ℕ) := (z • A - B)⁻¹ *ᵥ f i
  let r := differenceParticularResponse C D g
  let T := drazinInverse C * D
  let P := C * drazinInverse C
  have he : IsDifferenceSolution C D g x ↔ IsDifferenceSolution A B f x :=
    isDifferenceSolution_normalized_iff A B z hz f x
  obtain ⟨heq, hc⟩ := exercise_8_28 A B z hz
  change z • C - D = 1 at heq
  have hD : D = z • C - 1 := by
    simpa only [sub_sub_cancel] using congrArg (fun M : Matrix n n ℂ => z • C - M) heq
  have hr : IsDifferenceSolution C D g r := differenceParticularResponse_solves hD g
  have hP : LinearMap.range P.mulVecLin = LinearMap.range (C ^ matrixIndex C).mulVecLin :=
    range_mul_drazinInverse C
  rw [← he, differenceSolution_sub_particular hr]
  constructor
  · intro hx
    obtain ⟨hwR, hw⟩ := differenceSolution_eq_pow_mulVec hD hx
    rw [← hP] at hwR
    obtain ⟨y, hy⟩ := hwR 0
    change P *ᵥ y = x 0 - r 0 at hy
    refine ⟨y, funext fun t => ?_⟩
    change x t = T ^ t *ᵥ (P *ᵥ y) + r t
    exact (sub_eq_iff_eq_add.mp (hw t)).trans (by rw [hy])
  · rintro ⟨y, hy⟩
    have hStart : P *ᵥ y ∈ LinearMap.range (C ^ matrixIndex C).mulVecLin := by
      rw [← hP]
      exact ⟨y, rfl⟩
    have hw := differenceSolution_pow_mulVec hc.symm hStart
    have ht : (fun t => x t - r t) = fun t => T ^ t *ᵥ (P *ᵥ y) := by
      funext t
      rw [hy]
      change T ^ t *ᵥ (P *ᵥ y) + r t - r t = T ^ t *ᵥ (P *ᵥ y)
      exact add_sub_cancel_right _ _
    rw [ht]
    exact hw

/-- **Equation (120)** of [benIsrael2003generalized], Chapter 8.
The consistency test at time zero adds the future response sum to the
prescribed initial vector. -/
theorem forcedInitialVector_consistent_iff (A B : Matrix n n ℂ) (z : ℂ)
    (hz : IsUnit (z • A - B)) (f : ℕ → n → ℂ) (c : n → ℂ) :
    let C := normalizedDifferenceA A B z
    let D := normalizedDifferenceB A B z
    let g (i : ℕ) := (z • A - B)⁻¹ *ᵥ f i
    IsConsistentInitialVector A B f c ↔
      c + ((1 - C * drazinInverse C) * drazinInverse D) *ᵥ
        differenceFutureSum (C * drazinInverse D) g (matrixIndex C) 0 ∈
          LinearMap.range (C ^ matrixIndex C).mulVecLin := by
  intro C D g
  let P := C * drazinInverse C
  let u := ((1 - P) * drazinInverse D) *ᵥ
    differenceFutureSum (C * drazinInverse D) g (matrixIndex C) 0
  have h0 (y : n → ℂ) : differenceRegularSolution A B z f y 0 = P *ᵥ y - u := by
    simp [differenceRegularSolution, differenceParticularResponse, differencePastSum, P, C, D, g, u,
      mulVec_zero, sub_eq_add_neg]
  change IsConsistentInitialVector A B f c ↔
    c + u ∈ LinearMap.range (C ^ matrixIndex C).mulVecLin
  rw [← range_mul_drazinInverse C]
  constructor
  · rintro ⟨x, hx, hc⟩
    obtain ⟨y, rfl⟩ := (theorem_13 A B z hz f x).mp hx
    rw [h0, sub_eq_iff_eq_add] at hc
    exact ⟨y, hc⟩
  · rintro ⟨y, hy⟩
    let x := differenceRegularSolution A B z f y
    refine ⟨x, (theorem_13 A B z hz f x).mpr ⟨y, rfl⟩, ?_⟩
    change differenceRegularSolution A B z f y 0 = c
    rw [h0, sub_eq_iff_eq_add]
    exact hy

/-- The family in **Equation (119)** of [benIsrael2003generalized],
Chapter 8, is independent of the point used to normalize the pencil. -/
theorem differenceRegularSolution_range_eq (A B : Matrix n n ℂ)
    {z w : ℂ} (hz : IsUnit (z • A - B)) (hw : IsUnit (w • A - B))
    (f : ℕ → n → ℂ) :
    Set.range (differenceRegularSolution A B z f) =
      Set.range (differenceRegularSolution A B w f) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have hx := (theorem_13 A B z hz f (differenceRegularSolution A B z f y)).mpr ⟨y, rfl⟩
    obtain ⟨v, hv⟩ := (theorem_13 A B w hw f _).mp hx
    exact ⟨v, hv.symm⟩
  · rintro ⟨y, rfl⟩
    have hx := (theorem_13 A B w hw f (differenceRegularSolution A B w f y)).mpr ⟨y, rfl⟩
    obtain ⟨v, hv⟩ := (theorem_13 A B z hz f _).mp hx
    exact ⟨v, hv.symm⟩

/-- **Theorem 13** of [benIsrael2003generalized], Chapter 8.
A forced system has a solution and is tractable exactly when the
underlying pencil is regular. -/
theorem forced_exists_and_tractable_iff_regular (A B : Matrix n n ℂ) (f : ℕ → n → ℂ) :
    (∃ x, IsDifferenceSolution A B f x) ∧ IsTractableDifferenceEquation A B f ↔
      ∃ z : ℂ, IsUnit (z • A - B) := by
  constructor
  · rintro ⟨⟨y, hy⟩, h⟩
    by_contra! hn
    obtain ⟨v, hv, h0, hne⟩ := nontrivialSolution_of_singular_pencil A B hn
    let x (t : ℕ) := v t + y t
    have hx : IsDifferenceSolution A B f x := by
      apply (differenceSolution_sub_particular hy).mpr
      have he : (fun t => x t - y t) = v := by
        funext t
        exact add_sub_cancel_right _ _
      rwa [he]
    have hx0 : x 0 = y 0 := by simp [x, h0]
    obtain ⟨w, _, hw⟩ := h (y 0) ⟨y, hy, rfl⟩
    have he := (hw x ⟨hx, hx0⟩).trans (hw y ⟨hy, rfl⟩).symm
    apply hne
    funext t
    have ht := congrFun he t
    change v t + y t = y t at ht
    exact add_eq_right.mp ht
  · rintro ⟨z, hz⟩
    let x := differenceRegularSolution A B z f 0
    refine ⟨⟨x, (theorem_13 A B z hz f x).mpr ⟨0, rfl⟩⟩, ?_⟩
    rintro c ⟨y, hy, hy0⟩
    refine ⟨y, ⟨hy, hy0⟩, ?_⟩
    rintro w ⟨hw, hw0⟩
    have hv := (differenceSolution_sub_particular hy).mp hw
    have he := ((theorem_12 A B z hz (fun t => w t - y t)).mp hv).2
    funext t
    apply sub_eq_zero.mp
    rw [he t, hw0, hy0, sub_self, mulVec_zero]

end ForcedResponse

/-- **Exercise 31** of [benIsrael2003generalized], Chapter 8.
For nonsingular `B`, zero is a regular pencil point and direct
multiplication by `B⁻¹` puts the right-hand coefficient at the identity. -/
theorem exercise_8_31 (A B : Matrix n n ℂ) (hB : IsUnit B) :
    IsUnit ((0 : ℂ) • A - B) ∧
    normalizedDifferenceA A B 0 = -(B⁻¹ * A) ∧ normalizedDifferenceB A B 0 = -1 ∧
    ∀ f x : ℕ → n → ℂ, IsDifferenceSolution A B f x ↔
      IsDifferenceSolution (B⁻¹ * A) 1 (fun t => B⁻¹ *ᵥ f t) x := by
  have hI : B⁻¹ * B = 1 := nonsing_inv_mul B ((isUnit_iff_isUnit_det B).mp hB)
  have hneg : (-B)⁻¹ = -B⁻¹ := inv_eq_left_inv (by rw [neg_mul_neg, hI])
  refine ⟨?_, ?_, ?_, fun f x => ?_⟩
  · simpa only [zero_smul, zero_sub] using hB.neg
  · rw [normalizedDifferenceA, zero_smul, zero_sub, hneg, Matrix.neg_mul]
  · rw [normalizedDifferenceB, zero_smul, zero_sub, hneg, Matrix.neg_mul, hI]
  · apply forall_congr'
    intro t
    have hBx : B⁻¹ *ᵥ (B *ᵥ x t) = x t := by rw [mulVec_mulVec, hI, one_mulVec]
    have hinj := mulVec_injective_of_isUnit (isUnit_nonsing_inv_iff.mpr hB)
    calc
      _ ↔ B⁻¹ *ᵥ (A *ᵥ x (t + 1)) = B⁻¹ *ᵥ (B *ᵥ x t + f t) := hinj.eq_iff.symm
      _ ↔ _ := by rw [mulVec_mulVec, mulVec_add, hBx, one_mulVec]

/-- **Exercise 31** of [benIsrael2003generalized], Chapter 8.
The homogeneous system with nonsingular `B` is the recurrence in
Example 1 for `B⁻¹ * A`. -/
theorem exercise_8_31_homogeneous (A B : Matrix n n ℂ) (hB : IsUnit B)
    (x : ℕ → n → ℂ) :
    let C := B⁻¹ * A
    IsDifferenceSolution A B 0 x ↔
      (∀ t, x t ∈ LinearMap.range (C ^ matrixIndex C).mulVecLin) ∧
        ∀ t, x (t + 1) = drazinInverse C *ᵥ x t := by
  intro C
  have h := (exercise_8_31 A B hB).2.2.2 0 x
  have hf : (fun t : ℕ => B⁻¹ *ᵥ (0 : ℕ → n → ℂ) t) = 0 := by
    funext t
    simp
  rw [hf] at h
  exact h.trans (differenceSolution_iff_drazin C x)

private theorem range_pow_mul_of_commute_isUnit {H C : Matrix n n ℂ}
    (hH : IsUnit H) (hHC : Commute H C) (j : ℕ) :
    LinearMap.range ((H * C) ^ j).mulVecLin = LinearMap.range (C ^ j).mulVecLin := by
  rw [hHC.mul_pow, (hHC.pow_pow j j).eq, mulVecLin_mul]
  apply LinearMap.range_comp_of_range_eq_top
  exact LinearMap.range_eq_top.mpr (mulVec_surjective_iff_isUnit.mpr (hH.pow j))

private theorem matrixIndex_mul_of_commute_isUnit {H C : Matrix n n ℂ}
    (hH : IsUnit H) (hHC : Commute H C) :
    matrixIndex (H * C) = matrixIndex C := by
  have hr (j : ℕ) : ((H * C) ^ j).rank = (C ^ j).rank := by
    rw [rank, rank, range_pow_mul_of_commute_isUnit hH hHC]
  apply le_antisymm
  · apply ((H * C).rank_pow_eq_succ_iff C.rankStabilizationIndex_spec.1).mp
    simpa only [hr] using C.rankStabilizationIndex_spec.2
  · apply (C.rank_pow_eq_succ_iff (H * C).rankStabilizationIndex_spec.1).mp
    simpa only [hr] using (H * C).rankStabilizationIndex_spec.2

private theorem drazinInverse_mul_of_commute_isUnit {H C : Matrix n n ℂ}
    (hH : IsUnit H) (hHC : Commute H C) :
    drazinInverse (H * C) = drazinInverse C * H⁻¹ := by
  let X := drazinInverse C
  let k := matrixIndex C
  have hD : IsDrazinInverseAt k C X := Chapter04.isDrazinInverseAt_drazinInverse C
  have hd := (isUnit_iff_isUnit_det H).mp hH
  have hHI : H * H⁻¹ = 1 := mul_nonsing_inv H hd
  have hIH : H⁻¹ * H = 1 := nonsing_inv_mul H hd
  have hCI := commute_nonsing_inv_right hHC.symm
  have hHX : Commute H X := commute_drazin_right hHC
  have hC : Commute (H * C) (X * H⁻¹) :=
    (hHX.mul_left hD.commute).mul_right
      ((commute_nonsing_inv_right (Commute.refl H)).mul_left hCI)
  have hO : (X * H⁻¹) * (H * C) * (X * H⁻¹) = X * H⁻¹ := calc
    _ = X * (H⁻¹ * H) * C * X * H⁻¹ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hIH, Matrix.mul_one, hD.outer]
  have hS : (H * C) ^ (k + 1) * (X * H⁻¹) = (H * C) ^ k := calc
    _ = H ^ (k + 1) * (C ^ (k + 1) * X) * H⁻¹ := by
      rw [hHC.mul_pow (k + 1)]
      simp only [Matrix.mul_assoc]
    _ = H ^ (k + 1) * C ^ k * H⁻¹ := by rw [hD.stable]
    _ = (H ^ (k + 1) * H⁻¹) * C ^ k := by
      rw [Matrix.mul_assoc, (hCI.pow_left k).eq, ← Matrix.mul_assoc]
    _ = _ := by
      rw [hHC.mul_pow k, pow_succ H k, Matrix.mul_assoc (H ^ k), hHI, Matrix.mul_one]
  have hInv := Chapter04.isDrazinInverseAt_drazinInverse (H * C)
  rw [matrixIndex_mul_of_commute_isUnit hH hHC] at hInv
  exact hInv.unique ⟨hC, hO, hS⟩

private theorem commute_mul_inv_cancel {H M : Matrix n n ℂ} (hH : IsUnit H)
    (hHM : Commute H M) : H * M * H⁻¹ = M := by
  rw [hHM.eq, Matrix.mul_assoc, mul_nonsing_inv H ((isUnit_iff_isUnit_det H).mp hH), Matrix.mul_one]

/-- **Exercise 29** of [benIsrael2003generalized], Chapter 8.
The spectral projection, the two mixed Drazin products, the index and
ranges of powers, and the two Drazin-weighted forcings are independent
of the regular point used to normalize the pencil. In part (a), the
factor `α • Âβ - B̂β` inside the printed Drazin formula needs an inverse. -/
theorem exercise_8_29 (A B : Matrix n n ℂ) (α β : ℂ)
    (hα : IsUnit (α • A - B)) (hβ : IsUnit (β • A - B)) (f : n → ℂ) :
    let Cα := normalizedDifferenceA A B α
    let Dα := normalizedDifferenceB A B α
    let Cβ := normalizedDifferenceA A B β
    let Dβ := normalizedDifferenceB A B β
    let fα := (α • A - B)⁻¹ *ᵥ f
    let fβ := (β • A - B)⁻¹ *ᵥ f
    Cα * drazinInverse Cα = Cβ * drazinInverse Cβ ∧
      (drazinInverse Cα * Dα = drazinInverse Cβ * Dβ ∧
        Cα * drazinInverse Dα = Cβ * drazinInverse Dβ) ∧
      (matrixIndex Cα = matrixIndex Cβ ∧
        ∀ j : ℕ, LinearMap.range (Cα ^ j).mulVecLin = LinearMap.range (Cβ ^ j).mulVecLin) ∧
      drazinInverse Cα *ᵥ fα = drazinInverse Cβ *ᵥ fβ ∧
      drazinInverse Dα *ᵥ fα = drazinInverse Dβ *ᵥ fβ := by
  dsimp only
  let Mα := α • A - B
  let Mβ := β • A - B
  let C := normalizedDifferenceA A B β
  let D := normalizedDifferenceB A B β
  let H := Mα⁻¹ * Mβ
  have hH : IsUnit H := (isUnit_nonsing_inv_iff.mpr hα).mul hβ
  have hαdet := (isUnit_iff_isUnit_det Mα).mp hα
  have hβdet := (isUnit_iff_isUnit_det Mβ).mp hβ
  have hHdet := (isUnit_iff_isUnit_det H).mp hH
  have hHinv : H⁻¹ = α • C - D := by
    have h : (Mβ⁻¹ * Mα) * H = 1 := by
      change (Mβ⁻¹ * Mα) * (Mα⁻¹ * Mβ) = 1
      rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left Mα Mβ hαdet, nonsing_inv_mul Mβ hβdet]
    rw [inv_eq_left_inv h]
    change Mβ⁻¹ * Mα = α • (Mβ⁻¹ * A) - Mβ⁻¹ * B
    rw [← Matrix.mul_smul, ← Matrix.mul_sub]
  have hInvInv : (H⁻¹)⁻¹ = H := inv_eq_left_inv (mul_nonsing_inv H hHdet)
  have hCD : Commute C D := (exercise_8_28 A B β hβ).2
  have hHC : Commute H C := by
    rw [← hInvInv]
    apply commute_nonsing_inv_left
    rw [hHinv]
    exact ((Commute.refl C).smul_left α).sub_left hCD.symm
  have hHD : Commute H D := by
    rw [← hInvInv]
    apply commute_nonsing_inv_left
    rw [hHinv]
    exact (hCD.smul_left α).sub_left (Commute.refl D)
  have htransport (F : Matrix n n ℂ) : H * (Mβ⁻¹ * F) = Mα⁻¹ * F := by
    change Mα⁻¹ * Mβ * (Mβ⁻¹ * F) = Mα⁻¹ * F
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left Mβ F hβdet]
  have hCα : normalizedDifferenceA A B α = H * C := (htransport A).symm
  have hDα : normalizedDifferenceB A B α = H * D := (htransport B).symm
  have hfα : Mα⁻¹ *ᵥ f = H *ᵥ (Mβ⁻¹ *ᵥ f) := by
    rw [mulVec_mulVec]
    change Mα⁻¹ *ᵥ f = (Mα⁻¹ * Mβ * Mβ⁻¹) *ᵥ f
    rw [Matrix.mul_assoc, mul_nonsing_inv Mβ hβdet, Matrix.mul_one]
  have hforcing (X : Matrix n n ℂ) : (X * H⁻¹) *ᵥ (Mα⁻¹ *ᵥ f) = X *ᵥ (Mβ⁻¹ *ᵥ f) := by
    rw [hfα, mulVec_mulVec, nonsing_inv_mul_cancel_right H X hHdet]
  have hCInv : drazinInverse (normalizedDifferenceA A B α) = drazinInverse C * H⁻¹ := by
    rw [hCα, drazinInverse_mul_of_commute_isUnit hH hHC]
  have hDInv : drazinInverse (normalizedDifferenceB A B α) = drazinInverse D * H⁻¹ := by
    rw [hDα, drazinInverse_mul_of_commute_isUnit hH hHD]
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hCInv, hCα, ← Matrix.mul_assoc, Matrix.mul_assoc H C]
    exact commute_mul_inv_cancel hH (hHC.mul_right (commute_drazin_right hHC))
  · rw [hCInv, hDα, ← Matrix.mul_assoc, nonsing_inv_mul_cancel_right H _ hHdet]
  · rw [hDInv, hCα, ← Matrix.mul_assoc, Matrix.mul_assoc H C]
    exact commute_mul_inv_cancel hH (hHC.mul_right (commute_drazin_right hHD))
  · rw [hCα]
    exact matrixIndex_mul_of_commute_isUnit hH hHC
  · intro j
    rw [hCα]
    exact range_pow_mul_of_commute_isUnit hH hHC j
  · rw [hCInv]
    exact hforcing (drazinInverse C)
  · rw [hDInv]
    exact hforcing (drazinInverse D)

private theorem mulVec_differencePastSum {U T : Matrix n n ℂ} (h : Commute U T)
    (g : ℕ → n → ℂ) (t : ℕ) :
    U *ᵥ differencePastSum T g t = differencePastSum T (fun i => U *ᵥ g i) t := by
  unfold differencePastSum
  rw [mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_mulVec, (h.pow_right _).eq, ← mulVec_mulVec]

/-- **Theorem 13** and **Exercise 30** of [benIsrael2003generalized],
Chapter 8. With the same free vector and forcing, each value of the
solution formula is independent of the normalization point. -/
theorem differenceRegularSolution_eq (A B : Matrix n n ℂ) {z w : ℂ}
    (hz : IsUnit (z • A - B)) (hw : IsUnit (w • A - B))
    (f : ℕ → n → ℂ) (y : n → ℂ) :
    differenceRegularSolution A B z f y = differenceRegularSolution A B w f y := by
  let C₁ := normalizedDifferenceA A B z
  let C₂ := normalizedDifferenceA A B w
  let D₁ := normalizedDifferenceB A B z
  let D₂ := normalizedDifferenceB A B w
  let g₁ (i : ℕ) := (z • A - B)⁻¹ *ᵥ f i
  let g₂ (i : ℕ) := (w • A - B)⁻¹ *ᵥ f i
  have h₁ : Commute C₁ D₁ := (exercise_8_28 A B z hz).2
  have h₂ : Commute C₂ D₂ := (exercise_8_28 A B w hw).2
  obtain ⟨hP, ⟨hT, hG⟩, ⟨hk, _⟩, _⟩ := exercise_8_29 A B z w hz hw 0
  change C₁ * drazinInverse C₁ = C₂ * drazinInverse C₂ at hP
  change drazinInverse C₁ * D₁ = drazinInverse C₂ * D₂ at hT
  change C₁ * drazinInverse D₁ = C₂ * drazinInverse D₂ at hG
  change matrixIndex C₁ = matrixIndex C₂ at hk
  have hC (i : ℕ) : drazinInverse C₁ *ᵥ g₁ i = drazinInverse C₂ *ᵥ g₂ i :=
    (exercise_8_29 A B z w hz hw (f i)).2.2.2.1
  have hD (i : ℕ) : drazinInverse D₁ *ᵥ g₁ i = drazinInverse D₂ *ᵥ g₂ i :=
    (exercise_8_29 A B z w hz hw (f i)).2.2.2.2
  have hPast₁ : Commute (drazinInverse C₁) (drazinInverse C₁ * D₁) :=
    (Commute.refl _).mul_right (commute_drazin_right h₁.symm).symm
  have hPast₂ : Commute (drazinInverse C₂) (drazinInverse C₂ * D₂) :=
    (Commute.refl _).mul_right (commute_drazin_right h₂.symm).symm
  funext t
  change (drazinInverse C₁ * D₁) ^ t *ᵥ ((C₁ * drazinInverse C₁) *ᵥ y) +
      differenceParticularResponse C₁ D₁ g₁ t =
    (drazinInverse C₂ * D₂) ^ t *ᵥ ((C₂ * drazinInverse C₂) *ᵥ y) +
      differenceParticularResponse C₂ D₂ g₂ t
  rw [differenceParticularResponse_eq_past_sub_future h₁,
    differenceParticularResponse_eq_past_sub_future h₂,
    mulVec_differencePastSum hPast₁, mulVec_differencePastSum hPast₂, hT, hP, hG, hk,
    funext hC, funext hD]

open Matrix

section NilpotentBlockCoordinates

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

omit [DecidableEq p] [DecidableEq q] in
private theorem blockDiagonal_mulVec_sumElim (C : Matrix p p ℂ) (N : Matrix q q ℂ)
    (x : p → ℂ) (y : q → ℂ) :
    (fromBlocks C 0 0 N) *ᵥ Sum.elim x y = Sum.elim (C *ᵥ x) (N *ᵥ y) := by
  rw [fromBlocks_mulVec]
  funext i
  cases i <;> simp [zero_mulVec]

private theorem homogeneousBlock_rec_iff (C : Matrix p p ℂ) (N : Matrix q q ℂ)
    (z : ℂ) (a : ℕ → p → ℂ) (b : ℕ → q → ℂ) :
    IsDifferenceSolution (fromBlocks C 0 0 N) (fromBlocks (z • C - 1) 0 0 (z • N - 1))
      0 (fun t => Sum.elim (a t) (b t)) ↔
      (∀ t, C *ᵥ a (t + 1) = (z • C - 1) *ᵥ a t) ∧
      (∀ t, N *ᵥ b (t + 1) = (z • N - 1) *ᵥ b t) := by
  unfold IsDifferenceSolution
  simp only [Pi.zero_apply, add_zero, blockDiagonal_mulVec_sumElim]
  constructor
  · intro h
    exact ⟨fun t => congrArg (fun x => x ∘ Sum.inl) (h t),
      fun t => congrArg (fun x => x ∘ Sum.inr) (h t)⟩
  · rintro ⟨hC, hN⟩ t
    rw [hC t, hN t]

private theorem homogeneous_nilpotent_component_zero (N : Matrix q q ℂ) (z : ℂ)
    (b : ℕ → q → ℂ) {k : ℕ} (hN : N ^ k = 0)
    (hRec : ∀ t, N *ᵥ b (t + 1) = (z • N - 1) *ᵥ b t) : ∀ t, b t = 0 := by
  have hstep (t : ℕ) : b t = N *ᵥ (z • b t - b (t + 1)) := by
    rw [mulVec_sub, mulVec_smul, hRec t, sub_mulVec, smul_mulVec, one_mulVec, sub_sub_cancel]
  have hAll (e : ℕ) (t : ℕ) : ∃ y, b t = N ^ e *ᵥ y := by
    induction e generalizing t with
    | zero => exact ⟨b t, by simp⟩
    | succ e ih =>
        obtain ⟨x, hx⟩ := ih t
        obtain ⟨y, hy⟩ := ih (t + 1)
        refine ⟨z • x - y, ?_⟩
        calc
          b t = N *ᵥ (z • b t - b (t + 1)) := hstep t
          _ = N *ᵥ (N ^ e *ᵥ (z • x - y)) := by
            have hxy : N ^ e *ᵥ (z • x - y) = z • b t - b (t + 1) := by
              rw [mulVec_sub, mulVec_smul, ← hx, ← hy]
            rw [hxy]
          _ = _ := by rw [mulVec_mulVec, pow_succ']
  intro t
  obtain ⟨y, hy⟩ := hAll k t
  rw [hN, zero_mulVec] at hy
  exact hy

/-- **Equations (117)–(118)** of [benIsrael2003generalized]. In the
invertible and nilpotent coordinates of a regular homogeneous difference
system, the nilpotent component vanishes and the other is propagated by
powers from its own initial value. -/
theorem homogeneousSolution_nilpotent_block (C : Matrix p p ℂ) (N : Matrix q q ℂ)
    (z : ℂ) (hC : IsUnit C) {k : ℕ} (hN : N ^ k = 0) (a : ℕ → p → ℂ) (b : ℕ → q → ℂ) :
    IsDifferenceSolution (fromBlocks C 0 0 N) (fromBlocks (z • C - 1) 0 0 (z • N - 1))
      0 (fun t => Sum.elim (a t) (b t)) ↔
      (∀ t, b t = 0) ∧ (∀ t, a t = (C⁻¹ ^ t * (z • C - 1) ^ t) *ᵥ a 0) := by
  rw [homogeneousBlock_rec_iff]
  let D := z • C - 1
  let X := C⁻¹ * D
  have hd := (isUnit_iff_isUnit_det C).mp hC
  have hL : C⁻¹ * C = 1 := nonsing_inv_mul C hd
  have hR : C * C⁻¹ = 1 := mul_nonsing_inv C hd
  have hcomm : Commute C⁻¹ D := by
    change C⁻¹ * (z • C - 1) = (z • C - 1) * C⁻¹
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, hL, hR]
  have hp (t : ℕ) : X ^ t = C⁻¹ ^ t * D ^ t := hcomm.mul_pow t
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨homogeneous_nilpotent_component_zero N z b hN hb, ?_⟩
    have hRec (t : ℕ) : a (t + 1) = X *ᵥ a t := by
      have h := congrArg (C⁻¹ *ᵥ ·) (ha t)
      simpa only [mulVec_mulVec, hL, one_mulVec] using h
    have hAll (t : ℕ) : a t = X ^ t *ᵥ a 0 := by
      induction t with
      | zero => simp
      | succ t ih => rw [hRec t, ih, mulVec_mulVec, pow_succ']
    intro t
    exact (hAll t).trans (congrArg (· *ᵥ a 0) (hp t))
  · rintro ⟨hb, ha⟩
    refine ⟨?_, fun t => by rw [hb, hb, mulVec_zero, mulVec_zero]⟩
    have ha' (t : ℕ) : a t = X ^ t *ᵥ a 0 := (ha t).trans (congrArg (· *ᵥ a 0) (hp t).symm)
    intro t
    rw [ha' (t + 1), ha' t, pow_succ', mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc C X,
      show C * X = D by rw [show X = C⁻¹ * D from rfl, ← Matrix.mul_assoc, hR, Matrix.one_mul]]

end NilpotentBlockCoordinates

end BenIsraelGreville.Chapter08
