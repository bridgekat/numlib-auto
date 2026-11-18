/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Numlib.Analysis.Matrix.OperatorNorm
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Iterative methods for the Moore–Penrose inverse

Section 7.7 of [benIsrael2003generalized] computes the pseudoinverse by iterations
controlled by powers of a range residual. The two support conditions in (75)
identify the approximants with maps between the initial and final spaces of the
pseudoinverse. Spectral-norm convergence follows from the spectral radius bound.

## Deviations from the source

* **Exercise 17** (correction). In the printed example, the start has zero range residual
  but fails right support, so its computable correction can be nonzero. The fixed-point
  example here has right support and fails left support.
* **Exercise 19(c)** (correction). This characterization assumes a nonzero scale.
  At zero scale the computable residual is the identity.
* **Exercise 21** (correction). The initial range residual is raised to `p^k` at index `k`,
  as required by Equation (89).
-/

namespace BenIsraelGreville.Chapter07

open Matrix Filter Finset
open scoped Topology Matrix.Norms.L2Operator

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Equation (67)** of [benIsrael2003generalized], Chapter 7.
The residual of an approximate inverse relative to the projection onto the range of `A`. -/
noncomputable def pinvIterationResidual (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    Matrix m m ℂ := A * A.pinv - A * X

/-- **Equation (68)** of [benIsrael2003generalized], Chapter 7.
The residual inequality for the order of a sequence of approximate inverses.
The predicate accepts any real-valued function on matrices and any exponent.
The convergence results supply the norm and order hypotheses. -/
def IsPinvIterationOrder (ν : Matrix m m ℂ → ℝ) (p : ℕ) (A : Matrix m n ℂ)
    (X : ℕ → Matrix n m ℂ) : Prop :=
  ∃ c > 0, ∀ k, ν (pinvIterationResidual A (X (k + 1))) ≤
    c * ν (pinvIterationResidual A (X k)) ^ p

/-- **Equation (75)** of [benIsrael2003generalized], Chapter 7.
The approximate inverse is supported on both sides by the pseudoinverse's projections. -/
structure IsPinvSupported (A : Matrix m n ℂ) (X : Matrix n m ℂ) : Prop where
  /-- The column space of the approximate inverse is contained in that of the adjoint. -/
  left : (A.pinv * A) * X = X
  /-- The approximate inverse vanishes on the orthogonal complement of the range of `A`. -/
  right : X * (A * A.pinv) = X

omit [DecidableEq m] in
/-- **Equation (75)** of [benIsrael2003generalized], Chapter 7.
Two-sided support is equivalent to factorization through the adjoint on both sides. -/
theorem isPinvSupported_iff {A : Matrix m n ℂ} {X : Matrix n m ℂ} :
    IsPinvSupported A X ↔ ∃ B : Matrix m n ℂ, X = Aᴴ * B * Aᴴ := by
  constructor
  · intro h
    refine ⟨A.pinvᴴ * X * A.pinvᴴ, ?_⟩
    have hL : Aᴴ * A.pinvᴴ = A.pinv * A := by
      rw [← conjTranspose_mul, A.isHermitian_pinv_mul.eq]
    have hR : A.pinvᴴ * Aᴴ = A * A.pinv := by
      rw [← conjTranspose_mul, A.isHermitian_mul_pinv.eq]
    calc
      X = (A.pinv * A) * X * (A * A.pinv) := by rw [h.left, h.right]
      _ = _ := by rw [← hL, ← hR]; simp only [Matrix.mul_assoc]
  · rintro ⟨B, rfl⟩
    constructor
    · simp only [← Matrix.mul_assoc, A.pinv_mul_self_mul_conjTranspose]
    · simp only [Matrix.mul_assoc, A.conjTranspose_mul_mul_pinv]

/-- **Equation (71)** of [benIsrael2003generalized], Chapter 7.
A correction supported on the range of `A` can use the computable residual `I - A X`. -/
theorem pinvCorrection_eq {A : Matrix m n ℂ} (X C : Matrix n m ℂ)
    (hC : C * (A * A.pinv) = C) :
    C * pinvIterationResidual A X = C * (1 - A * X) := by
  rw [pinvIterationResidual, Matrix.mul_sub, Matrix.mul_sub, hC, Matrix.mul_one]

omit [DecidableEq m] in
/-- **Equations (67′) and (69′)–(73′)** of [benIsrael2003generalized], Chapter 7.
The dual correction multiplies the row-space residual on the right. -/
theorem pinvCorrection_dual_eq {A : Matrix m n ℂ} (X C : Matrix n m ℂ)
    (hC : (A.pinv * A) * C = C) :
    (A.pinv * A - X * A) * C = (1 - X * A) * C := by
  rw [Matrix.sub_mul, Matrix.sub_mul, hC, Matrix.one_mul]

/-- **Equation (77)** of [benIsrael2003generalized], Chapter 7.
The first-order method uses a fixed correction equal to the initial approximate inverse. -/
def pinvFirstOrderIterate (A : Matrix m n ℂ) (X₀ : Matrix n m ℂ) : ℕ → Matrix n m ℂ
  | 0 => X₀
  | k + 1 => pinvFirstOrderIterate A X₀ k + X₀ * (1 - A * pinvFirstOrderIterate A X₀ k)

/-- **Equation (84)** of [benIsrael2003generalized], Chapter 7.
The order-`p` method right-multiplies by the first `p` terms of the geometric sum in
the computable residual. -/
def pinvHigherOrderIterate (A : Matrix m n ℂ) (X₀ : Matrix n m ℂ) (p : ℕ) : ℕ → Matrix n m ℂ
  | 0 => X₀
  | k + 1 => let X := pinvHigherOrderIterate A X₀ p k
    X * ∑ j ∈ range p, (1 - A * X) ^ j

omit [DecidableEq n] in
/-- The zeroth first-order iterate is the supplied initial approximation. -/
@[simp] theorem pinvFirstOrderIterate_zero (A : Matrix m n ℂ) (X₀ : Matrix n m ℂ) :
    pinvFirstOrderIterate A X₀ 0 = X₀ := rfl

omit [DecidableEq n] in
/-- The zeroth higher-order iterate is the supplied initial approximation. -/
@[simp] theorem pinvHigherOrderIterate_zero (A : Matrix m n ℂ) (X₀ : Matrix n m ℂ) (p : ℕ) :
    pinvHigherOrderIterate A X₀ p 0 = X₀ := rfl

omit [DecidableEq m] in
private theorem rangeProjection_idempotent (A : Matrix m n ℂ) : IsIdempotentElem (A * A.pinv) := by
  rw [isIdempotentElem_iff, ← Matrix.mul_assoc, A.mul_pinv_mul_self]

omit [DecidableEq m] in
private theorem rangeProjection_mul_residual (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    (A * A.pinv) * pinvIterationResidual A X = pinvIterationResidual A X := by
  rw [pinvIterationResidual, Matrix.mul_sub, (rangeProjection_idempotent A).eq,
    ← Matrix.mul_assoc, A.mul_pinv_mul_self]

omit [DecidableEq m] in
private theorem residual_mul_rangeProjection {A : Matrix m n ℂ} {X : Matrix n m ℂ}
    (hX : X * (A * A.pinv) = X) :
    pinvIterationResidual A X * (A * A.pinv) = pinvIterationResidual A X := by
  rw [pinvIterationResidual, Matrix.sub_mul, (rangeProjection_idempotent A).eq,
    Matrix.mul_assoc, hX]

omit [DecidableEq m] in
private theorem pinv_sub_eq_pinv_mul_residual {A : Matrix m n ℂ} {X : Matrix n m ℂ}
    (hX : (A.pinv * A) * X = X) :
    A.pinv - X = A.pinv * pinvIterationResidual A X := by
  rw [pinvIterationResidual, Matrix.mul_sub, ← Matrix.mul_assoc, A.pinv_mul_self_mul_pinv,
    ← Matrix.mul_assoc, hX]

/-- **Equation (80)** of [benIsrael2003generalized], Chapter 7.
The first-order correction can be expressed in terms of the range residual. -/
theorem pinvFirstOrderIterate_succ_eq {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : X₀ * (A * A.pinv) = X₀) (k : ℕ) :
    pinvFirstOrderIterate A X₀ (k + 1) = pinvFirstOrderIterate A X₀ k +
      X₀ * pinvIterationResidual A (pinvFirstOrderIterate A X₀ k) := by
  rw [pinvCorrection_eq _ _ hX₀]
  rfl

/-- **Theorem 3** of [benIsrael2003generalized], Chapter 7.
First-order iteration preserves both support conditions. -/
theorem isPinvSupported_firstOrder {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : IsPinvSupported A X₀) (k : ℕ) :
    IsPinvSupported A (pinvFirstOrderIterate A X₀ k) := by
  induction k with
  | zero => exact hX₀
  | succ k ih =>
    rw [pinvFirstOrderIterate_succ_eq hX₀.right]
    constructor
    · rw [Matrix.mul_add, ih.left, ← Matrix.mul_assoc, hX₀.left]
    · rw [Matrix.add_mul, ih.right, Matrix.mul_assoc, residual_mul_rangeProjection ih.right]

/-- **Equation (81)** of [benIsrael2003generalized], Chapter 7.
The range residual after one step is left-multiplied by the initial range residual. -/
theorem pinvFirstOrderIterate_residual_succ {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : X₀ * (A * A.pinv) = X₀) (k : ℕ) :
    pinvIterationResidual A (pinvFirstOrderIterate A X₀ (k + 1)) =
      pinvIterationResidual A X₀ * pinvIterationResidual A (pinvFirstOrderIterate A X₀ k) := by
  rw [pinvFirstOrderIterate_succ_eq hX₀]
  let X := pinvFirstOrderIterate A X₀ k
  let R := pinvIterationResidual A X
  change pinvIterationResidual A (X + X₀ * R) = pinvIterationResidual A X₀ * R
  calc
    _ = R - (A * X₀) * R := by
      rw [pinvIterationResidual, Matrix.mul_add, ← Matrix.mul_assoc, ← sub_sub]
      rfl
    _ = _ := by
      rw [pinvIterationResidual, Matrix.sub_mul, rangeProjection_mul_residual]

/-- **Equation (81)** of [benIsrael2003generalized], Chapter 7.
The residual at index `k` is the `(k+1)`-st power of the initial residual. -/
theorem pinvFirstOrderIterate_residual_pow {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : X₀ * (A * A.pinv) = X₀) (k : ℕ) :
    pinvIterationResidual A (pinvFirstOrderIterate A X₀ k) =
      pinvIterationResidual A X₀ ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pinvFirstOrderIterate_residual_succ hX₀, ih]
    exact (pow_succ' _ _).symm

/-- **Equation (83)** of [benIsrael2003generalized], Chapter 7.
First-order iteration sums the initial range residual's powers. -/
theorem pinvFirstOrderIterate_eq_geom {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : X₀ * (A * A.pinv) = X₀) (k : ℕ) :
    pinvFirstOrderIterate A X₀ k =
      X₀ * ∑ j ∈ range (k + 1), pinvIterationResidual A X₀ ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pinvFirstOrderIterate_succ_eq hX₀, pinvFirstOrderIterate_residual_pow hX₀, ih]
    exact (Matrix.mul_add _ _ _).symm.trans
      (congrArg (X₀ * ·) (sum_range_succ (fun j => pinvIterationResidual A X₀ ^ j) (k + 1)).symm)

private theorem projection_mul_error_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Y : Matrix ι ι ℂ} (hP : IsIdempotentElem P) (hL : P * Y = Y) (hR : Y * P = Y)
    {j : ℕ} (hj : j ≠ 0) :
    P * (1 - Y) ^ j = (P - Y) ^ j := by
  have hc : Commute P (1 - Y) :=
    (Commute.one_right P).sub_right (show Commute P Y from hL.trans hR.symm)
  have he : P * (1 - Y) = P - Y := by rw [Matrix.mul_sub, Matrix.mul_one, hL]
  rw [← he, hc.mul_pow, hP.pow_eq hj]

private theorem projectionGeomStep_residual {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Y : Matrix ι ι ℂ} (hP : IsIdempotentElem P) (hL : P * Y = Y) (hR : Y * P = Y)
    {p : ℕ} (hp : p ≠ 0) :
    P - Y * (∑ j ∈ range p, (1 - Y) ^ j) = (P - Y) ^ p := by
  have hgeom := mul_neg_geom_sum (1 - Y) p
  rw [sub_sub_cancel] at hgeom
  rw [← projection_mul_error_pow hP hL hR hp, ← sub_sub_cancel (1 : Matrix ι ι ℂ) ((1 - Y) ^ p),
    ← hgeom, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hL]

/-- **Equation (89)** of [benIsrael2003generalized], Chapter 7.
One higher-order step raises the current range residual to the exponent `p`. -/
theorem pinvHigherOrderStep_residual {A : Matrix m n ℂ} {X : Matrix n m ℂ}
    (hX : X * (A * A.pinv) = X) {p : ℕ} (hp : p ≠ 0) :
    pinvIterationResidual A (X * ∑ j ∈ range p, (1 - A * X) ^ j) =
      pinvIterationResidual A X ^ p := by
  simp only [pinvIterationResidual, ← Matrix.mul_assoc A X]
  exact projectionGeomStep_residual (rangeProjection_idempotent A)
    (by rw [← Matrix.mul_assoc, A.mul_pinv_mul_self])
    (by rw [Matrix.mul_assoc, hX]) hp

private theorem geomStep_mul_projection {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Y : Matrix ι ι ℂ} (hL : P * Y = Y) (hR : Y * P = Y) (p : ℕ) :
    Commute P (∑ j ∈ range p, (1 - Y) ^ j) := by
  have hc : Commute P (1 - Y) :=
    (Commute.one_right P).sub_right (show Commute P Y from hL.trans hR.symm)
  change P * (∑ j ∈ range p, (1 - Y) ^ j) = (∑ j ∈ range p, (1 - Y) ^ j) * P
  simp only [Matrix.mul_sum, Matrix.sum_mul, fun j => (hc.pow_right j).eq]

/-- **Theorem 4** of [benIsrael2003generalized], Chapter 7.
Higher-order iteration preserves both support conditions. -/
theorem isPinvSupported_higherOrder {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : IsPinvSupported A X₀) (p k : ℕ) :
    IsPinvSupported A (pinvHigherOrderIterate A X₀ p k) := by
  induction k with
  | zero => exact hX₀
  | succ k ih =>
    rw [pinvHigherOrderIterate]
    let X := pinvHigherOrderIterate A X₀ p k
    let S := ∑ j ∈ range p, (1 - A * X) ^ j
    change IsPinvSupported A (X * S)
    constructor
    · rw [← Matrix.mul_assoc, ih.left]
    · have hc : Commute (A * A.pinv) S := geomStep_mul_projection
        (by rw [← Matrix.mul_assoc, A.mul_pinv_mul_self]) (by rw [Matrix.mul_assoc, ih.right]) p
      rw [Matrix.mul_assoc, ← hc.eq, ← Matrix.mul_assoc, ih.right]

/-- **Equation (87)** of [benIsrael2003generalized], Chapter 7.
Higher-order iteration can also use the powers of the range residual. -/
theorem pinvHigherOrderStep_eq_residual {A : Matrix m n ℂ} {X : Matrix n m ℂ}
    (hX : X * (A * A.pinv) = X) (p : ℕ) :
    X * (∑ j ∈ range p, (1 - A * X) ^ j) =
      X * ∑ j ∈ range p, pinvIterationResidual A X ^ j := by
  rw [Matrix.mul_sum, Matrix.mul_sum]
  apply sum_congr rfl
  intro j _
  by_cases hj : j = 0
  · simp [hj]
  · have h := projection_mul_error_pow (rangeProjection_idempotent A)
      (Y := A * X) (by rw [← Matrix.mul_assoc, A.mul_pinv_mul_self])
      (by rw [Matrix.mul_assoc, hX]) hj
    rw [pinvIterationResidual, ← h, ← Matrix.mul_assoc, hX]

/-- **Equation (89)** of [benIsrael2003generalized], Chapter 7.
The range residual of consecutive higher-order iterates obeys the power recurrence. -/
theorem pinvHigherOrderIterate_residual_succ {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : IsPinvSupported A X₀) {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    pinvIterationResidual A (pinvHigherOrderIterate A X₀ p (k + 1)) =
      pinvIterationResidual A (pinvHigherOrderIterate A X₀ p k) ^ p := by
  rw [pinvHigherOrderIterate]
  exact pinvHigherOrderStep_residual (isPinvSupported_higherOrder hX₀ p k).right hp

/-- **Equation (89)** of [benIsrael2003generalized], Chapter 7.
At index `k`, the range residual is the initial residual raised to `p^k`. -/
theorem pinvHigherOrderIterate_residual_pow {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : IsPinvSupported A X₀) {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    pinvIterationResidual A (pinvHigherOrderIterate A X₀ p k) =
      pinvIterationResidual A X₀ ^ (p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pinvHigherOrderIterate_residual_succ hX₀ hp, ih, ← pow_mul, ← pow_succ]

/-- **Theorem 5**, Equation (90) of [benIsrael2003generalized], Chapter 7.
The higher-order iterate at index `k` equals the first-order iterate at index `p^k - 1`. -/
theorem theorem_5 {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : IsPinvSupported A X₀) {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    pinvHigherOrderIterate A X₀ p k = pinvFirstOrderIterate A X₀ (p ^ k - 1) := by
  apply (sub_right_inj (a := A.pinv)).mp
  rw [pinv_sub_eq_pinv_mul_residual (isPinvSupported_higherOrder hX₀ p k).left,
    pinv_sub_eq_pinv_mul_residual (isPinvSupported_firstOrder hX₀ (p ^ k - 1)).left,
    pinvHigherOrderIterate_residual_pow hX₀ hp, pinvFirstOrderIterate_residual_pow hX₀.right,
    Nat.sub_add_cancel (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hp))]

/-- **Equation (91)** of [benIsrael2003generalized], Chapter 7.
The higher-order iterate is the geometric sum of the initial residual
with `p^k` terms, multiplied on the left by the initial inverse. -/
theorem pinvHigherOrderIterate_eq_geomSum {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : IsPinvSupported A X₀) {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    pinvHigherOrderIterate A X₀ p k =
      X₀ * ∑ j ∈ range (p ^ k), pinvIterationResidual A X₀ ^ j := by
  rw [theorem_5 hX₀ hp, pinvFirstOrderIterate_eq_geom hX₀.right,
    Nat.sub_add_cancel (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hp))]

omit [DecidableEq m] in
private theorem tendsto_pinv_of_tendsto_residual {A : Matrix m n ℂ}
    {X : ℕ → Matrix n m ℂ} (hX : ∀ k, (A.pinv * A) * X k = X k)
    (hR : Tendsto (fun k => pinvIterationResidual A (X k)) atTop (𝓝 0)) :
    Tendsto X atTop (𝓝 A.pinv) := by
  have hmul : Continuous (fun R : Matrix m m ℂ => A.pinv * R) :=
    continuous_const.matrix_mul continuous_id
  have h : Tendsto (fun k => A.pinv * pinvIterationResidual A (X k)) atTop (𝓝 0) := by
    have hcomp := (hmul.tendsto 0).comp hR
    rw [Matrix.mul_zero] at hcomp
    exact hcomp
  simp_rw [← pinv_sub_eq_pinv_mul_residual (hX _)] at h
  have h' := (tendsto_const_nhds (x := A.pinv)).sub h
  simpa only [sub_sub_cancel, sub_zero] using h'

/-- **Equation (82)** of [benIsrael2003generalized], Chapter 7.
The first-order range residuals tend to zero. -/
theorem pinvFirstOrderIterate_tendsto_residual {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : X₀ * (A * A.pinv) = X₀)
    (hρ : spectralRadius ℂ (pinvIterationResidual A X₀) < 1) :
    Tendsto (fun k => pinvIterationResidual A (pinvFirstOrderIterate A X₀ k)) atTop (𝓝 0) := by
  simp_rw [pinvFirstOrderIterate_residual_pow hX₀]
  exact (tendsto_pow_of_spectralRadius_lt_one hρ).comp (tendsto_add_atTop_nat 1)

/-- **Theorem 3**, Equations (78) and (82) of [benIsrael2003generalized], Chapter 7.
The first-order method converges under the spectral radius condition. The stepwise
residual bound holds for every submultiplicative norm represented by `ν`. -/
theorem theorem_3 {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : IsPinvSupported A X₀) (hρ : spectralRadius ℂ (pinvIterationResidual A X₀) < 1) :
    Tendsto (pinvFirstOrderIterate A X₀) atTop (𝓝 A.pinv) ∧
      ∀ (ν : Matrix m m ℂ → ℝ), (∀ M N, ν (M * N) ≤ ν M * ν N) →
        ∀ k, ν (pinvIterationResidual A (pinvFirstOrderIterate A X₀ (k + 1))) ≤
          ν (pinvIterationResidual A X₀) *
            ν (pinvIterationResidual A (pinvFirstOrderIterate A X₀ k)) := by
  constructor
  · exact tendsto_pinv_of_tendsto_residual (fun k => (isPinvSupported_firstOrder hX₀ k).left)
      (pinvFirstOrderIterate_tendsto_residual hX₀.right hρ)
  · intro ν hν k
    rw [pinvFirstOrderIterate_residual_succ hX₀.right]
    apply hν

private theorem submultiplicative_pow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Matrix ι ι ℂ → ℝ) (hn : ∀ M, 0 ≤ ν M) (hm : ∀ M N, ν (M * N) ≤ ν M * ν N)
    (M : Matrix ι ι ℂ) {k : ℕ} (hk : k ≠ 0) : ν (M ^ k) ≤ ν M ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk
  clear hk
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ (ν M)]
    exact (hm _ _).trans (mul_le_mul_of_nonneg_right ih (hn M))

/-- **Theorem 4**, Equations (84)–(85) of [benIsrael2003generalized], Chapter 7.
The higher-order method converges under the spectral radius condition. The stepwise
residual bound holds for every submultiplicative norm represented by `ν`. -/
theorem theorem_4 {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : IsPinvSupported A X₀) (hρ : spectralRadius ℂ (pinvIterationResidual A X₀) < 1)
    {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (pinvHigherOrderIterate A X₀ p) atTop (𝓝 A.pinv) ∧
      ∀ (ν : Matrix m m ℂ → ℝ), (∀ M, 0 ≤ ν M) → (∀ M N, ν (M * N) ≤ ν M * ν N) →
        ∀ k, ν (pinvIterationResidual A (pinvHigherOrderIterate A X₀ p (k + 1))) ≤
          ν (pinvIterationResidual A (pinvHigherOrderIterate A X₀ p k)) ^ p := by
  have hp' : p ≠ 0 := by omega
  constructor
  · apply tendsto_pinv_of_tendsto_residual (fun k => (isPinvSupported_higherOrder hX₀ p k).left)
    simp_rw [pinvHigherOrderIterate_residual_pow hX₀ hp']
    exact (tendsto_pow_of_spectralRadius_lt_one hρ).comp
      (tendsto_pow_atTop_atTop_of_one_lt (show 1 < p by omega))
  · intro ν hn hm k
    rw [pinvHigherOrderIterate_residual_succ hX₀ hp']
    exact submultiplicative_pow_le ν hn hm _ hp'

/-- **Equation (68)** of [benIsrael2003generalized], Chapter 7.
The higher-order sequence has order at least `p` in every submultiplicative norm. -/
theorem isPinvIterationOrder_higherOrder {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : IsPinvSupported A X₀) {p : ℕ} (hp : p ≠ 0)
    (ν : Matrix m m ℂ → ℝ) (hn : ∀ M, 0 ≤ ν M) (hm : ∀ M N, ν (M * N) ≤ ν M * ν N) :
    IsPinvIterationOrder ν p A (pinvHigherOrderIterate A X₀ p) := by
  refine ⟨1, zero_lt_one, fun k => ?_⟩
  rw [_root_.one_mul, pinvHigherOrderIterate_residual_succ hX₀ hp]
  exact submultiplicative_pow_le ν hn hm _ hp

/-- **Exercise 18**, Equation (92) of [benIsrael2003generalized], Chapter 7.
The starting approximate inverse times the inverse of the initial residual complement
equals the pseudoinverse. -/
theorem exercise_7_18 {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : IsPinvSupported A X₀) (hρ : spectralRadius ℂ (pinvIterationResidual A X₀) < 1) :
    A.pinv = X₀ * (1 - pinvIterationResidual A X₀)⁻¹ := by
  let R := pinvIterationResidual A X₀
  have hu : IsUnit (1 - R) := by
    by_contra hh
    have hmem : (1 : ℂ) ∈ spectrum ℂ R := spectrum.mem_iff.mpr (by simpa using hh)
    have hbound : (‖(1 : ℂ)‖₊ : ENNReal) ≤ spectralRadius ℂ R := by
      rw [spectralRadius_eq_of_unital]
      exact le_iSup₂_of_le 1 hmem le_rfl
    exact (not_le_of_gt hρ) (by simpa using hbound)
  have hmul : A.pinv * (1 - R) = X₀ := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← pinv_sub_eq_pinv_mul_residual hX₀.left, sub_sub_cancel]
  calc
    A.pinv = A.pinv * (1 - R) * (1 - R)⁻¹ :=
      (mul_nonsing_inv_cancel_right _ _ ((isUnit_iff_isUnit_det _).mp hu)).symm
    _ = X₀ * (1 - R)⁻¹ := congrArg (· * (1 - R)⁻¹) hmul

/-- **Exercise 22**, Equations (101)–(102) of [benIsrael2003generalized], Chapter 7.
The order-two method is the Schulz recurrence, with quadratic residual decay. -/
theorem exercise_7_22 {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : IsPinvSupported A X₀) (hρ : spectralRadius ℂ (pinvIterationResidual A X₀) < 1) :
    Tendsto (pinvHigherOrderIterate A X₀ 2) atTop (𝓝 A.pinv) ∧
      ∀ k, let X := pinvHigherOrderIterate A X₀ 2 k
        pinvHigherOrderIterate A X₀ 2 (k + 1) = X * (2 - A * X) ∧
          ‖pinvIterationResidual A (pinvHigherOrderIterate A X₀ 2 (k + 1))‖ ≤
            ‖pinvIterationResidual A X‖ ^ 2 := by
  obtain ⟨hconv, hnorm⟩ := theorem_4 hX₀ hρ (p := 2) le_rfl
  refine ⟨hconv, fun k => ⟨?_, hnorm norm norm_nonneg norm_mul_le k⟩⟩
  rw [pinvHigherOrderIterate]
  congr 1
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one]
  rw [← add_sub_assoc, one_add_one_eq_two]

section Projection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Equation (111)** of [benIsrael2003generalized], Chapter 7.
The projection iteration uses only the current approximate projection. -/
def projectionHigherOrderIterate (Y₀ : Matrix ι ι ℂ) (p : ℕ) : ℕ → Matrix ι ι ℂ
  | 0 => Y₀
  | k + 1 => let Y := projectionHigherOrderIterate Y₀ p k
    Y * ∑ j ∈ range p, (1 - Y) ^ j

private theorem projectionHigherOrderIterate_supported {P Y₀ : Matrix ι ι ℂ}
    (hL : P * Y₀ = Y₀) (hR : Y₀ * P = Y₀) (p k : ℕ) :
    P * projectionHigherOrderIterate Y₀ p k = projectionHigherOrderIterate Y₀ p k ∧
      projectionHigherOrderIterate Y₀ p k * P = projectionHigherOrderIterate Y₀ p k := by
  induction k with
  | zero => exact ⟨hL, hR⟩
  | succ k ih =>
    let Y := projectionHigherOrderIterate Y₀ p k
    let S := ∑ j ∈ range p, (1 - Y) ^ j
    have hc : Commute P S := geomStep_mul_projection ih.1 ih.2 p
    change P * (Y * S) = Y * S ∧ (Y * S) * P = Y * S
    constructor
    · rw [← Matrix.mul_assoc, ih.1]
    · rw [Matrix.mul_assoc, ← hc.eq, ← Matrix.mul_assoc, ih.2]

/-- **Equations (109) and (112)** of [benIsrael2003generalized], Chapter 7.
For a supported start, the projection residual is a power of the initial residual. -/
theorem projectionHigherOrderIterate_residual {P Y₀ : Matrix ι ι ℂ}
    (hP : IsIdempotentElem P) (hL : P * Y₀ = Y₀) (hR : Y₀ * P = Y₀)
    {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    P - projectionHigherOrderIterate Y₀ p k = (P - Y₀) ^ (p ^ k) := by
  induction k with
  | zero => simp [projectionHigherOrderIterate]
  | succ k ih =>
    obtain ⟨hleft, hright⟩ := projectionHigherOrderIterate_supported hL hR p k
    rw [projectionHigherOrderIterate, projectionGeomStep_residual hP hleft hright hp,
      ih, ← pow_mul, ← pow_succ]

/-- **Exercise 24** of [benIsrael2003generalized], Chapter 7.
The projection iteration converges when the initial residual has spectral radius below one. -/
theorem exercise_7_24 {P Y₀ : Matrix ι ι ℂ}
    (hP : IsIdempotentElem P) (hL : P * Y₀ = Y₀) (hR : Y₀ * P = Y₀)
    (hρ : spectralRadius ℂ (P - Y₀) < 1) {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (projectionHigherOrderIterate Y₀ p) atTop (𝓝 P) ∧
      ∀ (ν : Matrix ι ι ℂ → ℝ), (∀ M, 0 ≤ ν M) → (∀ M N, ν (M * N) ≤ ν M * ν N) →
        ∀ k, ν (P - projectionHigherOrderIterate Y₀ p (k + 1)) ≤
          ν (P - projectionHigherOrderIterate Y₀ p k) ^ p := by
  have hp' : p ≠ 0 := by omega
  constructor
  · have h : Tendsto (fun k => P - projectionHigherOrderIterate Y₀ p k) atTop (𝓝 0) := by
      simp_rw [projectionHigherOrderIterate_residual hP hL hR hp']
      exact (tendsto_pow_of_spectralRadius_lt_one hρ).comp
        (tendsto_pow_atTop_atTop_of_one_lt (show 1 < p by omega))
    simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x := P)).sub h
  · intro ν hn hm k
    obtain ⟨hleft, hright⟩ := projectionHigherOrderIterate_supported hL hR p k
    rw [projectionHigherOrderIterate, projectionGeomStep_residual hP hleft hright hp']
    exact submultiplicative_pow_le ν hn hm _ hp'

end Projection

section Products

variable {q : Type*} [Fintype q]

/-- **Exercise 27**, Equations (114)–(117) of [benIsrael2003generalized], Chapter 7.
The product iteration propagates the approximate product and the computable residual. -/
def pinvProductIterate (A : Matrix m n ℂ) (B : Matrix q n ℂ) (X₀ : Matrix n m ℂ)
    (p : ℕ) : ℕ → Matrix q m ℂ × Matrix m m ℂ
  | 0 => (B * X₀, 1 - A * X₀)
  | k + 1 =>
    let (Z, T) := pinvProductIterate A B X₀ p k
    let S := ∑ j ∈ range p, T ^ j
    (Z * S, 1 + S * (T - 1))

omit [DecidableEq n] [Fintype q] in
/-- **Exercise 27**, Equations (114)–(117) of [benIsrael2003generalized], Chapter 7.
The product iteration gives the product and residual from the higher-order approximation. -/
theorem pinvProductIterate_eq (A : Matrix m n ℂ) (B : Matrix q n ℂ)
    (X₀ : Matrix n m ℂ) (p k : ℕ) :
    pinvProductIterate A B X₀ p k =
      (B * pinvHigherOrderIterate A X₀ p k, 1 - A * pinvHigherOrderIterate A X₀ p k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pinvProductIterate, pinvHigherOrderIterate, ih]
    dsimp only
    let X := pinvHigherOrderIterate A X₀ p k
    let T : Matrix m m ℂ := 1 - A * X
    let S := ∑ j ∈ range p, T ^ j
    change ((B * X) * S, 1 + S * (T - 1)) = (B * (X * S), 1 - A * (X * S))
    apply Prod.ext
    · exact Matrix.mul_assoc _ _ _
    · change 1 + S * (T - 1) = 1 - A * (X * S)
      have hST : S * (T - 1) = T ^ p - 1 := geom_sum_mul T p
      have hTS : (T - 1) * S = T ^ p - 1 := mul_geom_sum T p
      rw [hST, ← hTS, show T - 1 = -(A * X) by dsimp only [T]; abel,
        neg_mul, ← sub_eq_add_neg, Matrix.mul_assoc]

omit [Fintype q] in
/-- **Exercise 27** of [benIsrael2003generalized], Chapter 7.
The product iteration converges to `B * A.pinv` under the same
conditions as the inverse iteration. -/
theorem exercise_7_27 {A : Matrix m n ℂ} (B : Matrix q n ℂ) {X₀ : Matrix n m ℂ}
    (hX₀ : IsPinvSupported A X₀) (hρ : spectralRadius ℂ (pinvIterationResidual A X₀) < 1)
    {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun k => (pinvProductIterate A B X₀ p k).1) atTop (𝓝 (B * A.pinv)) := by
  have hmul : Continuous (fun Y : Matrix n m ℂ => B * Y) :=
    continuous_const.matrix_mul continuous_id
  simp_rw [pinvProductIterate_eq]
  exact (hmul.tendsto A.pinv).comp (theorem_4 hX₀ hρ hp).1

end Products

/-- **Exercise 17** of [benIsrael2003generalized], Chapter 7.
An initial approximate inverse with zero range residual and right support is fixed by both
iterations. Left support is needed to identify such a fixed point with the pseudoinverse. -/
theorem pinvIterate_fixed_of_residual_eq_zero {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (hX₀ : X₀ * (A * A.pinv) = X₀) (hR : pinvIterationResidual A X₀ = 0)
    {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    pinvFirstOrderIterate A X₀ k = X₀ ∧ pinvHigherOrderIterate A X₀ p k = X₀ := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    constructor
    · rw [pinvFirstOrderIterate_succ_eq hX₀, ih.1, hR, Matrix.mul_zero, add_zero]
    · rw [pinvHigherOrderIterate, ih.2, pinvHigherOrderStep_eq_residual hX₀, hR]
      have hs : ∑ j ∈ range p, (0 : Matrix m m ℂ) ^ j = 1 := by
        rw [sum_eq_single 0]
        · exact pow_zero _
        · exact fun j _ hj => zero_pow hj
        · exact fun h => False.elim (h (mem_range.mpr (Nat.pos_of_ne_zero hp)))
      rw [hs, Matrix.mul_one]

/-- **Exercise 17** of [benIsrael2003generalized], Chapter 7, with a corrected constant-sequence
example. For the projection `diag(1,0)`, the matrix with first column `(1,1)` and second
column zero has zero range residual and is fixed by both iterations. -/
theorem exercise_7_17 (p : ℕ) (hp : 2 ≤ p) :
    ∃ A X₀ : Matrix (Fin 2) (Fin 2) ℂ, A ≠ 0 ∧ X₀ ≠ A.pinv ∧
      pinvIterationResidual A X₀ = 0 ∧
      ∀ k, pinvFirstOrderIterate A X₀ k = X₀ ∧ pinvHigherOrderIterate A X₀ p k = X₀ := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 1, 0]
  have hA : A * A = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, Matrix.mul_apply, Fin.sum_univ_two]
  have hH : A.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [A]
  have hpinv : A.pinv = A :=
    (A.pinv_unique (by rwa [hA]) (by rwa [hA]) (hA.symm ▸ hH) (hA.symm ▸ hH)).symm
  have hAX : A * X = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, X, Matrix.mul_apply, Fin.sum_univ_two]
  have hXA : X * A = X := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, X, Matrix.mul_apply, Fin.sum_univ_two]
  have hR : pinvIterationResidual A X = 0 := by
    rw [pinvIterationResidual, hpinv, hA, hAX, sub_self]
  refine ⟨A, X, ?_, ?_, hR, pinvIterate_fixed_of_residual_eq_zero ?_ hR (by omega)⟩
  · intro hz
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hz
    norm_num [A] at this
  · intro eq
    rw [hpinv] at eq
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) eq
    norm_num [A, X] at this
  · rw [hpinv, hA, hXA]

omit [DecidableEq n] in
/-- **Equation (96)** of [benIsrael2003generalized], Chapter 7, for an arbitrary initial
approximation. The first-order iterate is the geometric sum of the computable residual powers. -/
theorem pinvFirstOrderIterate_eq_geom_computable (A : Matrix m n ℂ) (X₀ : Matrix n m ℂ) (k : ℕ) :
    pinvFirstOrderIterate A X₀ k = X₀ * ∑ j ∈ range (k + 1), (1 - A * X₀) ^ j := by
  let T : Matrix m m ℂ := 1 - A * X₀
  change pinvFirstOrderIterate A X₀ k = X₀ * ∑ j ∈ range (k + 1), T ^ j
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pinvFirstOrderIterate, ih]
    let S := ∑ j ∈ range (k + 1), T ^ j
    have hS : (∑ j ∈ range (k + 1 + 1), T ^ j) = S + T ^ (k + 1) := sum_range_succ _ _
    have hT : 1 - A * (X₀ * S) = T ^ (k + 1) := by
      rw [← Matrix.mul_assoc A X₀ S, show A * X₀ = 1 - T by exact (sub_sub_cancel _ _).symm]
      change 1 - (1 - T) * (∑ j ∈ range (k + 1), T ^ j) = T ^ (k + 1)
      rw [mul_neg_geom_sum, sub_sub_cancel]
    change X₀ * S + X₀ * (1 - A * (X₀ * S)) = _
    rw [hS, hT, Matrix.mul_add]

/-- **Equation (103)** of [benIsrael2003generalized], Chapter 7.
The least iteration index that reaches the first-order index `k` is the natural ceiling
logarithm of `k+1` in base `p`. -/
theorem exercise_7_23_iterationCount {p : ℕ} (hp : 1 < p) (k : ℕ) :
    IsLeast {j : ℕ | k ≤ p ^ j - 1} (Nat.clog p (k + 1)) := by
  have hiff (j : ℕ) : k ≤ p ^ j - 1 ↔ Nat.clog p (k + 1) ≤ j := by
    rw [Nat.clog_le_iff_le_pow hp]
    have hpow := Nat.one_le_pow j p (by omega : 0 < p)
    omega
  exact ⟨(hiff _).mpr le_rfl, fun j hj => (hiff j).mp hj⟩

omit [DecidableEq n] in
/-- **Equation (95)** of [benIsrael2003generalized], Chapter 7,
for an arbitrary initial approximation. Each first-order step is also an affine
right multiplication with the initial computable residual as its linear factor. -/
theorem pinvFirstOrderIterate_succ_eq_initialError (A : Matrix m n ℂ)
    (X₀ : Matrix n m ℂ) (k : ℕ) :
    pinvFirstOrderIterate A X₀ (k + 1) =
      pinvFirstOrderIterate A X₀ k * (1 - A * X₀) + X₀ := by
  let T : Matrix m m ℂ := 1 - A * X₀
  rw [pinvFirstOrderIterate_eq_geom_computable, pinvFirstOrderIterate_eq_geom_computable]
  change X₀ * (∑ j ∈ range (k + 1 + 1), T ^ j) =
    (X₀ * ∑ j ∈ range (k + 1), T ^ j) * T + X₀
  rw [sum_range_succ', Matrix.mul_add, pow_zero, Matrix.mul_one,
    Matrix.mul_assoc X₀, Matrix.sum_mul]
  simp only [pow_succ]

section Trace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem trace_pow_re_of_hermitian {R : Matrix ι ι ℂ} (hR : R.IsHermitian) (j : ℕ) :
    (R ^ j).trace.re = ∑ i, hR.eigenvalues i ^ j := by
  let D := diagonal (fun i => (hR.eigenvalues i : ℂ))
  let f := Unitary.conjStarAlgAut ℂ _ hR.eigenvectorUnitary
  have hd : R = f D := hR.spectral_theorem
  conv_lhs => rw [hd, ← map_pow, Matrix.trace_map', diagonal_pow, trace_diagonal]
  simp only [Pi.pow_apply, Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re]

private theorem abs_eigenvalues_lt_one_of_radius_lt_one {R : Matrix ι ι ℂ}
    (hR : R.IsHermitian) (hρ : spectralRadius ℂ R < 1) (i : ι) :
    |hR.eigenvalues i| < 1 := by
  let D := diagonal (fun i => (hR.eigenvalues i : ℂ))
  let f := Unitary.conjStarAlgAut ℂ _ hR.eigenvectorUnitary
  have hd : R = f D := hR.spectral_theorem
  have hmem : (hR.eigenvalues i : ℂ) ∈ spectrum ℂ R := by
    have hs : spectrum ℂ R = spectrum ℂ D := by rw [hd, AlgEquiv.spectrum_eq]
    rw [hs, spectrum_diagonal]
    exact ⟨i, rfl⟩
  have hbound : (‖(hR.eigenvalues i : ℂ)‖₊ : ENNReal) ≤ spectralRadius ℂ R := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup₂_of_le _ hmem le_rfl
  simpa only [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one,
    Complex.norm_real, Real.norm_eq_abs] using hbound.trans_lt hρ

private theorem monotone_projectionTrace {P Y₀ : Matrix ι ι ℂ}
    (hP : IsIdempotentElem P) (hPH : P.IsHermitian)
    (hL : P * Y₀ = Y₀) (hR : Y₀ * P = Y₀) (hYH : Y₀.IsHermitian)
    (hρ : spectralRadius ℂ (P - Y₀) < 1) {p : ℕ} (hp : 2 ≤ p) (hEven : Even p) :
    Monotone (fun k => (projectionHigherOrderIterate Y₀ p (k + 1)).trace.re) := by
  have hp' : p ≠ 0 := by omega
  have hRH := hPH.sub hYH
  have he (k : ℕ) : (projectionHigherOrderIterate Y₀ p (k + 1)).trace.re =
      P.trace.re - ∑ i, hRH.eigenvalues i ^ (p ^ (k + 1)) := by
    have h := projectionHigherOrderIterate_residual hP hL hR hp' (k + 1)
    have hy : projectionHigherOrderIterate Y₀ p (k + 1) = P - (P - Y₀) ^ (p ^ (k + 1)) := by
      rw [← h, sub_sub_cancel]
    rw [hy, trace_sub, Complex.sub_re, trace_pow_re_of_hermitian hRH]
  intro j k hjk
  simp only [he]
  apply sub_le_sub_left
  apply sum_le_sum
  intro i _
  have heK : Even (p ^ (k + 1)) := (Nat.even_pow' (Nat.succ_ne_zero _)).mpr hEven
  have heJ : Even (p ^ (j + 1)) := (Nat.even_pow' (Nat.succ_ne_zero _)).mpr hEven
  rw [← heK.pow_abs, ← heJ.pow_abs]
  exact pow_le_pow_of_le_one (abs_nonneg _) (abs_eigenvalues_lt_one_of_radius_lt_one hRH hρ i).le
    (Nat.pow_le_pow_right (by omega) (by omega))

end Trace

omit [DecidableEq m] in
private theorem trace_rangeProjection_eq_rank (A : Matrix m n ℂ) :
    (A * A.pinv).trace = (A.rank : ℂ) := by
  classical
  let P := A * A.pinv
  let f := toEuclideanLin P
  have hi : IsIdempotentElem f := by
    change f * f = f
    rw [Module.End.mul_eq_comp, ← toEuclideanLin_mul, (rangeProjection_idempotent A).eq]
  have h := ((LinearMap.isProj_range_iff_isIdempotentElem f).mpr hi).trace
  rw [show f = toEuclideanLin P from rfl, toEuclideanLin_eq_toLin_orthonormal, trace_toLin_eq] at h
  rw [← toEuclideanLin_eq_toLin_orthonormal, finrank_range_toEuclideanLin] at h
  have hr : P.rank = A.rank := by
    apply le_antisymm (rank_mul_le_left _ _)
    have hPA : P * A = A := A.mul_pinv_mul_self
    have hle := rank_mul_le_left P A
    rwa [hPA] at hle
  rwa [hr] at h

/-- **Exercise 25** of [benIsrael2003generalized], Chapter 7.
For an even order and Hermitian start, the real parts of the projection iterates'
traces are monotone from the first step and converge to the rank. -/
theorem exercise_7_25 (A : Matrix m n ℂ) {Y₀ : Matrix m m ℂ}
    (hL : (A * A.pinv) * Y₀ = Y₀) (hR : Y₀ * (A * A.pinv) = Y₀)
    (hYH : Y₀.IsHermitian) (hρ : spectralRadius ℂ (A * A.pinv - Y₀) < 1)
    {p : ℕ} (hp : 2 ≤ p) (hEven : Even p) :
    Monotone (fun k => (projectionHigherOrderIterate Y₀ p (k + 1)).trace.re) ∧
      Tendsto (fun k => (projectionHigherOrderIterate Y₀ p (k + 1)).trace.re) atTop
        (𝓝 (A.rank : ℝ)) := by
  have hP := rangeProjection_idempotent A
  refine ⟨monotone_projectionTrace hP A.isHermitian_mul_pinv hL hR hYH hρ hp hEven, ?_⟩
  have hc : Continuous (fun Y : Matrix m m ℂ => Y.trace.re) := by
    apply Complex.continuous_re.comp
    exact continuous_finsetSum _ fun i _ =>
      (continuous_apply i).comp (continuous_apply i)
  have h := (hc.tendsto (A * A.pinv)).comp
    ((exercise_7_24 hP hL hR hρ hp).1.comp (tendsto_add_atTop_nat 1))
  rw [trace_rangeProjection_eq_rank A] at h
  exact_mod_cast h

/-- **Exercise 26**, Equation (113) of [benIsrael2003generalized], Chapter 7.
Rounding the trace of a Hermitian projection iterate upward gives a lower bound on the rank. -/
theorem exercise_7_26 (A : Matrix m n ℂ) {Y₀ : Matrix m m ℂ}
    (hL : (A * A.pinv) * Y₀ = Y₀) (hR : Y₀ * (A * A.pinv) = Y₀)
    (hYH : Y₀.IsHermitian) (hρ : spectralRadius ℂ (A * A.pinv - Y₀) < 1)
    {p : ℕ} (hp : 2 ≤ p) (hEven : Even p) (k : ℕ) :
    ⌈(projectionHigherOrderIterate Y₀ p (k + 1)).trace.re⌉₊ ≤ A.rank := by
  obtain ⟨hmono, hlim⟩ := exercise_7_25 A hL hR hYH hρ hp hEven
  exact Nat.ceil_le.mpr (hmono.ge_of_tendsto hlim k)

section ScaledAdjoint

variable {a b : ℕ}

/-- The sorted eigenvalues of the left Gram matrix, including its zero eigenvalues. -/
noncomputable def leftGramEigenvalue (A : Matrix (Fin a) (Fin b) ℂ) (i : ℕ) : ℝ :=
  A.sortedSingularValues i ^ 2

private theorem leftGramEigenvalue_nonneg (A : Matrix (Fin a) (Fin b) ℂ) (i : ℕ) :
    0 ≤ leftGramEigenvalue A i := sq_nonneg _

private theorem leftGramEigenvalue_antitone (A : Matrix (Fin a) (Fin b) ℂ) :
    Antitone (leftGramEigenvalue A) :=
  fun _ j hij => pow_le_pow_left₀ (A.sortedSingularValues_nonneg j)
    (A.sortedSingularValues_antitone hij) _

private theorem leftGramEigenvalue_zero_iff (A : Matrix (Fin a) (Fin b) ℂ) (i : ℕ) :
    leftGramEigenvalue A i = 0 ↔ A.rank ≤ i := by
  rw [leftGramEigenvalue, pow_eq_zero_iff two_ne_zero, A.sortedSingularValues_eq_zero_iff_rank_le]

/-- **Exercises 19–21** of [benIsrael2003generalized], Chapter 7.
The left Gram matrix and range projection are simultaneously unitarily diagonalized.
The Gram diagonal contains the squared singular values, and the projection
diagonal is the indicator of their nonzero support. -/
theorem exists_leftGram_and_rangeProjection_diagonalizations
    (A : Matrix (Fin a) (Fin b) ℂ) :
    ∃ U : unitaryGroup (Fin a) ℂ,
      A * Aᴴ = Unitary.conjStarAlgAut ℂ _ U
        (diagonal (fun i : Fin a => (leftGramEigenvalue A i : ℂ))) ∧
      A * A.pinv = Unitary.conjStarAlgAut ℂ _ U
        (diagonal (fun i : Fin a => if i.val < A.rank then (1 : ℂ) else 0)) := by
  obtain ⟨U, hU, V, hV, hUV⟩ := A.exists_svd
  let σ (i : ℕ) : ℂ := A.sortedSingularValues i
  let D : Matrix (Fin a) (Fin b) ℂ := rectDiagonal σ
  let E : Matrix (Fin b) (Fin a) ℂ := rectDiagonal σ
  let J : Matrix (Fin b) (Fin a) ℂ := rectDiagonal fun i => (σ i)⁻¹
  have hUV' : star U * A * V = rectDiagonal σ := hUV
  have hA : A = U * D * Vᴴ := eq_mul_mul_star_of_star_mul_mul_eq hU hV hUV'
  have hp : A.pinv = V * J * Uᴴ := pinv_eq_of_svd hU hV hUV'
  have hDE : Dᴴ = E := by
    change (rectDiagonal σ : Matrix (Fin a) (Fin b) ℂ)ᴴ = rectDiagonal σ
    rw [rectDiagonal_conjTranspose]
    congr 1
    funext i
    simp [σ]
  have hAH : Aᴴ = V * E * Uᴴ := by
    rw [hA, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hDE,
      Matrix.mul_assoc]
  have hVstar : Vᴴ * V = 1 := mem_unitaryGroup_iff'.mp hV
  have hcancel (F : Matrix (Fin b) (Fin a) ℂ) :
      (U * D * Vᴴ) * (V * F * Uᴴ) = U * (D * F) * Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hVstar, Matrix.one_mul]
  have hbr : A.rank ≤ b := by simpa using rank_le_card_width A
  refine ⟨⟨U, hU⟩, ?_, ?_⟩
  · calc
      A * Aᴴ = (U * D * Vᴴ) * (V * E * Uᴴ) := congrArg₂ (· * ·) hA hAH
      _ = U * (D * E) * Uᴴ := hcancel E
      _ = _ := by
        change U * ((rectDiagonal σ : Matrix (Fin a) (Fin b) ℂ) *
          (rectDiagonal σ : Matrix (Fin b) (Fin a) ℂ)) * Uᴴ = _
        rw [rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal]
        change U * (diagonal (fun i : Fin a => if i.val < b then σ i * σ i else 0)) * Uᴴ =
          U * (diagonal (fun i : Fin a => (leftGramEigenvalue A i : ℂ))) * Uᴴ
        congr 3
        funext i
        by_cases hi : i.val < b
        · simp [hi, σ, leftGramEigenvalue, pow_two]
        · have hz := (leftGramEigenvalue_zero_iff A i).mpr (hbr.trans (le_of_not_gt hi))
          simp [hi, hz]
  · calc
      A * A.pinv = (U * D * Vᴴ) * (V * J * Uᴴ) := congrArg₂ (· * ·) hA hp
      _ = U * (D * J) * Uᴴ := hcancel J
      _ = _ := by
        change U * ((rectDiagonal σ : Matrix (Fin a) (Fin b) ℂ) *
          (rectDiagonal (fun i => (σ i)⁻¹) : Matrix (Fin b) (Fin a) ℂ)) * Uᴴ = _
        rw [rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal]
        change U * (diagonal (fun i : Fin a => if i.val < b then σ i * (σ i)⁻¹ else 0)) * Uᴴ =
          U * (diagonal (fun i : Fin a => if i.val < A.rank then (1 : ℂ) else 0)) * Uᴴ
        congr 3
        funext i
        by_cases hi : i.val < A.rank
        · have hne : σ i ≠ 0 := Complex.ofReal_ne_zero.mpr
            ((A.sortedSingularValues_eq_zero_iff_rank_le i).not.mpr (not_le.mpr hi))
          simp [hi, hi.trans_le hbr, mul_inv_cancel₀ hne]
        · have hz := (A.sortedSingularValues_eq_zero_iff_rank_le i).mpr (le_of_not_gt hi)
          simp [hi, σ, hz]

/-- **Exercises 19–21** of [benIsrael2003generalized], Chapter 7.
In singular-vector coordinates the initial range residual has entries
`1 - β σᵢ²` on the positive singular directions and zero on the remaining directions. -/
theorem exists_scaledAdjointResidual_diagonalizations
    (A : Matrix (Fin a) (Fin b) ℂ) (β : ℝ) :
    ∃ U : unitaryGroup (Fin a) ℂ,
      pinvIterationResidual A ((β : ℂ) • Aᴴ) =
        Unitary.conjStarAlgAut ℂ _ U
          (diagonal (fun i : Fin a =>
            if i.val < A.rank then ((1 - β * leftGramEigenvalue A i : ℝ) : ℂ) else 0)) ∧
      1 - A * ((β : ℂ) • Aᴴ) =
        Unitary.conjStarAlgAut ℂ _ U
          (diagonal (fun i : Fin a => ((1 - β * leftGramEigenvalue A i : ℝ) : ℂ))) := by
  obtain ⟨U, hG, hP⟩ := exists_leftGram_and_rangeProjection_diagonalizations A
  let f := Unitary.conjStarAlgAut ℂ _ U
  refine ⟨U, ?_, ?_⟩
  · rw [pinvIterationResidual, Matrix.mul_smul, hG, hP]
    change f _ - (β : ℂ) • f _ = f _
    rw [← map_smul, ← map_sub]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i.val < A.rank
      · simp [Matrix.sub_apply, Matrix.smul_apply, hi]
      · simp [Matrix.sub_apply, Matrix.smul_apply, hi,
          (leftGramEigenvalue_zero_iff A i).mpr (le_of_not_gt hi)]
    · simp [Matrix.sub_apply, Matrix.smul_apply, diagonal_apply_ne _ hij]
  · rw [Matrix.mul_smul, hG]
    change 1 - (β : ℂ) • f _ = f _
    rw [← map_smul, ← map_one f, ← map_sub]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.sub_apply, Matrix.smul_apply]
    · simp [Matrix.sub_apply, Matrix.smul_apply, diagonal_apply_ne _ hij, one_apply_ne hij]

/-- **Equations (97) and (99)** of [benIsrael2003generalized], Chapter 7.
The spectral norm bound on any positive power of the initial scaled-adjoint range residual
is equivalent to the corresponding bounds on all its supported diagonal entries. -/
theorem scaledAdjointResidual_norm_pow_le_iff
    (A : Matrix (Fin a) (Fin b) ℂ) (β : ℝ) {j : ℕ} (hj : j ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖pinvIterationResidual A ((β : ℂ) • Aᴴ) ^ j‖ ≤ t ↔
      ∀ i : Fin a, i.val < A.rank → |1 - β * leftGramEigenvalue A i| ^ j ≤ t := by
  obtain ⟨U, hR, _⟩ := exists_scaledAdjointResidual_diagonalizations A β
  let f := Unitary.conjStarAlgAut ℂ _ U
  let d : Fin a → ℂ := fun i => if i.val < A.rank then
    ((1 - β * leftGramEigenvalue A i : ℝ) : ℂ) else 0
  rw [hR]
  change ‖(f (diagonal d)) ^ j‖ ≤ t ↔ _
  rw [← map_pow, diagonal_pow, Unitary.conjStarAlgAut_apply,
    l2_opNorm_unitary_mul_mul_unitary U.property _ (Unitary.star_mem U.property),
    l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg ht]
  constructor
  · intro h i hi
    simpa only [Pi.pow_apply, d, ite_eq_left hi, norm_pow, Complex.norm_real,
      Real.norm_eq_abs] using h i
  · intro h i
    by_cases hi : i.val < A.rank
    · simpa only [Pi.pow_apply, d, ite_eq_left hi, norm_pow, Complex.norm_real,
        Real.norm_eq_abs] using h i hi
    · simpa only [Pi.pow_apply, d, ite_eq_right hi, zero_pow hj, norm_zero] using ht

private theorem leftGramEigenvalue_pos_of_lt_rank (A : Matrix (Fin a) (Fin b) ℂ)
    {i : ℕ} (hi : i < A.rank) : 0 < leftGramEigenvalue A i :=
  lt_of_le_of_ne (leftGramEigenvalue_nonneg A i)
    (fun heq => (not_le.mpr hi) ((leftGramEigenvalue_zero_iff A i).mp heq.symm))

private theorem isHermitian_scaledAdjoint_residuals (A : Matrix (Fin a) (Fin b) ℂ)
    (β : ℝ) :
    (pinvIterationResidual A ((β : ℂ) • Aᴴ)).IsHermitian ∧
      (1 - A * ((β : ℂ) • Aᴴ)).IsHermitian := by
  have hG : (A * Aᴴ).IsHermitian := isHermitian_mul_conjTranspose_self A
  have hS : ((β : ℂ) • (A * Aᴴ)).IsHermitian := hG.smul (by simp [IsSelfAdjoint])
  rw [pinvIterationResidual, Matrix.mul_smul]
  exact ⟨A.isHermitian_mul_pinv.sub hS, Matrix.isHermitian_one.sub hS⟩

private theorem scaledAdjointResidual_radius_lt_one_iff_entries
    (A : Matrix (Fin a) (Fin b) ℂ) (β : ℝ) :
    spectralRadius ℂ (pinvIterationResidual A ((β : ℂ) • Aᴴ)) < 1 ↔
      ∀ i : Fin a, i.val < A.rank → |1 - β * leftGramEigenvalue A i| < 1 := by
  have hHerm := (isHermitian_scaledAdjoint_residuals A β).1
  obtain ⟨U, hR, _⟩ := exists_scaledAdjointResidual_diagonalizations A β
  rw [hHerm.isSelfAdjoint.spectralRadius_eq_nnnorm, ENNReal.coe_lt_one_iff,
    ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one, hR,
    Unitary.conjStarAlgAut_apply,
    l2_opNorm_unitary_mul_mul_unitary U.property _ (Unitary.star_mem U.property),
    l2_opNorm_diagonal, pi_norm_lt_iff zero_lt_one]
  constructor
  · intro h i hi
    simpa only [ite_eq_left hi, Complex.norm_real, Real.norm_eq_abs] using h i
  · intro h i
    by_cases hi : i.val < A.rank
    · simpa only [ite_eq_left hi, Complex.norm_real, Real.norm_eq_abs] using h i hi
    · simp [hi]

/-- **Exercise 19(a,b)**, Equation (94) of [benIsrael2003generalized], Chapter 7.
The positive scale is below twice the reciprocal of the largest Gram eigenvalue
exactly when the initial range residual has spectral radius below one. -/
theorem spectralRadius_scaled_adjoint_start {A : Matrix (Fin a) (Fin b) ℂ}
    (hA : A ≠ 0) (β : ℝ) :
    spectralRadius ℂ (pinvIterationResidual A ((β : ℂ) • Aᴴ)) < 1 ↔
      0 < β ∧ β < 2 / leftGramEigenvalue A 0 := by
  have hr : 0 < A.rank := Nat.pos_of_ne_zero (hA ∘ rank_eq_zero_iff.mp)
  have hra : A.rank ≤ a := by simpa using rank_le_card_height A
  have hu := leftGramEigenvalue_pos_of_lt_rank A hr
  rw [scaledAdjointResidual_radius_lt_one_iff_entries]
  constructor
  · intro h
    have h0 := abs_lt.mp (h ⟨0, hr.trans_le hra⟩ hr)
    change -1 < 1 - β * leftGramEigenvalue A 0 ∧ 1 - β * leftGramEigenvalue A 0 < 1 at h0
    have hprod : 0 < β * leftGramEigenvalue A 0 := by linarith
    exact ⟨pos_of_mul_pos_left hprod hu.le, (lt_div_iff₀ hu).mpr (by linarith)⟩
  · rintro ⟨hβ, hbound⟩ i hi
    have hil := leftGramEigenvalue_antitone A (Nat.zero_le i.val)
    have hprod := mul_pos hβ (leftGramEigenvalue_pos_of_lt_rank A hi)
    have hupper := mul_le_mul_of_nonneg_left hil hβ.le
    have h2 := (lt_div_iff₀ hu).mp hbound
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- **Exercise 19(b,c)** of [benIsrael2003generalized], Chapter 7, for a nonzero scale.
The computable residual has spectral radius at most one and excludes eigenvalue `-1`
exactly when the range residual has spectral radius strictly below one. -/
theorem spectralRadius_scaled_adjoint_computable {A : Matrix (Fin a) (Fin b) ℂ}
    {β : ℝ} (hβ : β ≠ 0) :
    spectralRadius ℂ (pinvIterationResidual A ((β : ℂ) • Aᴴ)) < 1 ↔
      spectralRadius ℂ (1 - A * ((β : ℂ) • Aᴴ)) ≤ 1 ∧
        (-1 : ℂ) ∉ spectrum ℂ (1 - A * ((β : ℂ) • Aᴴ)) := by
  have hHerm := (isHermitian_scaledAdjoint_residuals A β).2
  obtain ⟨U, _, hT⟩ := exists_scaledAdjointResidual_diagonalizations A β
  have hspec : spectrum ℂ (1 - A * ((β : ℂ) • Aᴴ)) =
      Set.range (fun i : Fin a => ((1 - β * leftGramEigenvalue A i : ℝ) : ℂ)) := by
    rw [hT, AlgEquiv.spectrum_eq, spectrum_diagonal]
  rw [scaledAdjointResidual_radius_lt_one_iff_entries,
    hHerm.isSelfAdjoint.spectralRadius_eq_nnnorm, ENNReal.coe_le_one_iff,
    ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, hspec, hT,
    Unitary.conjStarAlgAut_apply,
    l2_opNorm_unitary_mul_mul_unitary U.property _ (Unitary.star_mem U.property),
    l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg zero_le_one]
  simp only [Complex.norm_real, Real.norm_eq_abs, Set.mem_range, not_exists]
  constructor
  · intro h
    constructor
    · intro i
      by_cases hi : i.val < A.rank
      · exact (h i hi).le
      · simp [(leftGramEigenvalue_zero_iff A i).mpr (le_of_not_gt hi)]
    · intro i heq
      have he : (1 - β * leftGramEigenvalue A i : ℝ) = -1 := by exact_mod_cast heq
      by_cases hi : i.val < A.rank
      · have := h i hi
        rw [he, abs_neg, abs_one] at this
        exact (lt_irrefl _ this)
      · simp [(leftGramEigenvalue_zero_iff A i).mpr (le_of_not_gt hi)] at he
        linarith
  · rintro ⟨hbound, hNeg⟩ i hi
    have hl := abs_le.mp (hbound i)
    have hneNeg : 1 - β * leftGramEigenvalue A i ≠ -1 := by
      intro he
      exact hNeg i (by exact_mod_cast he)
    have hnePos : 1 - β * leftGramEigenvalue A i ≠ 1 := by
      intro he
      have hprod : β * leftGramEigenvalue A i = 0 := by linarith
      exact (mul_ne_zero hβ (leftGramEigenvalue_pos_of_lt_rank A hi).ne') hprod
    exact abs_lt.mpr ⟨lt_of_le_of_ne hl.1 (Ne.symm hneNeg), lt_of_le_of_ne hl.2 hnePos⟩

private theorem abs_linear_le_max_endpoints (β : ℝ) {l x u : ℝ} (hl : l ≤ x) (hu : x ≤ u) :
    |1 - β * x| ≤ max |1 - β * l| |1 - β * u| := by
  by_cases hβ : 0 ≤ β
  · have hmin := mul_le_mul_of_nonneg_left hl hβ
    have hmax := mul_le_mul_of_nonneg_left hu hβ
    exact abs_le.mpr ⟨
      (neg_le_neg (le_max_right _ _)).trans ((neg_abs_le _).trans (by linarith)),
      (show 1 - β * x ≤ 1 - β * l by linarith).trans ((le_abs_self _).trans (le_max_left _ _))⟩
  · have hmin := mul_le_mul_of_nonpos_left hl (le_of_not_ge hβ)
    have hmax := mul_le_mul_of_nonpos_left hu (le_of_not_ge hβ)
    exact abs_le.mpr ⟨
      (neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans (by linarith)),
      (show 1 - β * x ≤ 1 - β * u by linarith).trans ((le_abs_self _).trans (le_max_right _ _))⟩

/-- **Exercise 20(c)** of [benIsrael2003generalized], Chapter 7.
The residual power's spectral norm is the corresponding power of the maximum
of the two endpoint residual magnitudes. -/
theorem scaledAdjointResidual_norm_pow_eq {A : Matrix (Fin a) (Fin b) ℂ}
    (hA : A ≠ 0) (β : ℝ) {j : ℕ} (hj : j ≠ 0) :
    ‖pinvIterationResidual A ((β : ℂ) • Aᴴ) ^ j‖ =
      (max |1 - β * leftGramEigenvalue A (A.rank - 1)|
        |1 - β * leftGramEigenvalue A 0|) ^ j := by
  let R := pinvIterationResidual A ((β : ℂ) • Aᴴ)
  let l := leftGramEigenvalue A (A.rank - 1)
  let u := leftGramEigenvalue A 0
  let v := max |1 - β * l| |1 - β * u|
  have hr : 0 < A.rank := Nat.pos_of_ne_zero (hA ∘ rank_eq_zero_iff.mp)
  have hra : A.rank ≤ a := by simpa using rank_le_card_height A
  have ht : A.rank - 1 < A.rank := by omega
  have hv : 0 ≤ v := (abs_nonneg _).trans (le_max_left _ _)
  change ‖R ^ j‖ = v ^ j
  apply le_antisymm
  · apply (scaledAdjointResidual_norm_pow_le_iff A β hj (pow_nonneg hv _)).mpr
    intro i hi
    apply pow_le_pow_left₀ (abs_nonneg _)
    exact abs_linear_le_max_endpoints β (leftGramEigenvalue_antitone A (by omega))
      (leftGramEigenvalue_antitone A (Nat.zero_le _))
  · have h := (scaledAdjointResidual_norm_pow_le_iff A β hj (norm_nonneg (R ^ j))).mp le_rfl
    rcases max_choice |1 - β * l| |1 - β * u| with hchoice | hchoice
    · rw [show v = _ from hchoice]
      exact h ⟨A.rank - 1, ht.trans_le hra⟩ ht
    · rw [show v = _ from hchoice]
      exact h ⟨0, hr.trans_le hra⟩ hr


private theorem endpoint_scale_minimum {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) :
    let β₀ := 2 / (u + l)
    let δ := (u - l) / (u + l)
    max |1 - β₀ * l| |1 - β₀ * u| = δ ∧
      ∀ β : ℝ, δ ≤ max |1 - β * l| |1 - β * u| := by
  let β₀ := 2 / (u + l)
  let δ := (u - l) / (u + l)
  have hu : 0 < u := hl.trans_le hlu
  have hd : 0 < u + l := add_pos hu hl
  have hδ : 0 ≤ δ := div_nonneg (sub_nonneg.mpr hlu) hd.le
  have hlEnd : 1 - β₀ * l = δ := by
    dsimp only [β₀, δ]
    field_simp [hd.ne']
    ring
  have huEnd : 1 - β₀ * u = -δ := by
    dsimp only [β₀, δ]
    field_simp [hd.ne']
    ring
  change _ = δ ∧ ∀ β : ℝ, δ ≤ max |1 - β * l| |1 - β * u|
  refine ⟨by rw [hlEnd, huEnd, abs_neg, abs_of_nonneg hδ, max_self], fun β => ?_⟩
  by_cases hβ : β ≤ β₀
  · calc
      δ = 1 - β₀ * l := hlEnd.symm
      _ ≤ 1 - β * l := sub_le_sub_left (mul_le_mul_of_nonneg_right hβ hl.le) _
      _ ≤ |1 - β * l| := le_abs_self _
      _ ≤ _ := le_max_left _ _
  · calc
      δ = -(1 - β₀ * u) := by rw [huEnd, neg_neg]
      _ ≤ -(1 - β * u) := by
        exact neg_le_neg (sub_le_sub_left (mul_le_mul_of_nonneg_right (le_of_not_ge hβ) hu.le) _)
      _ ≤ |1 - β * u| := neg_le_abs _
      _ ≤ _ := le_max_right _ _

/-- **Exercise 20(c)**, Equations (98)–(100) of [benIsrael2003generalized], Chapter 7.
The optimal scale is twice the reciprocal of the sum of the extreme positive Gram
eigenvalues. The smallest norm of the residual power is the corresponding power of
their difference divided by their sum. -/
theorem exercise_7_20_optimalScale {A : Matrix (Fin a) (Fin b) ℂ}
    (hA : A ≠ 0) {j : ℕ} (hj : j ≠ 0) :
    let l := leftGramEigenvalue A (A.rank - 1)
    let u := leftGramEigenvalue A 0
    let β₀ := 2 / (u + l)
    let δ := (u - l) / (u + l)
    ‖pinvIterationResidual A ((β₀ : ℂ) • Aᴴ) ^ j‖ = δ ^ j ∧
      ∀ β : ℝ, ‖pinvIterationResidual A ((β₀ : ℂ) • Aᴴ) ^ j‖ ≤
        ‖pinvIterationResidual A ((β : ℂ) • Aᴴ) ^ j‖ := by
  let l := leftGramEigenvalue A (A.rank - 1)
  let u := leftGramEigenvalue A 0
  let β₀ := 2 / (u + l)
  let δ := (u - l) / (u + l)
  have hr : 0 < A.rank := Nat.pos_of_ne_zero (hA ∘ rank_eq_zero_iff.mp)
  have hl : 0 < l := leftGramEigenvalue_pos_of_lt_rank A (by omega)
  have hlu : l ≤ u := leftGramEigenvalue_antitone A (Nat.zero_le _)
  have hd : 0 ≤ δ := div_nonneg (sub_nonneg.mpr hlu) (add_pos (hl.trans_le hlu) hl).le
  obtain ⟨hβ₀, hmin⟩ := endpoint_scale_minimum hl hlu
  have hone : ‖pinvIterationResidual A ((β₀ : ℂ) • Aᴴ) ^ j‖ = δ ^ j := by
    rw [scaledAdjointResidual_norm_pow_eq hA β₀ hj]
    exact congrArg (· ^ j) hβ₀
  refine ⟨hone, fun β => ?_⟩
  rw [hone, scaledAdjointResidual_norm_pow_eq hA β hj]
  exact pow_le_pow_left₀ hd (hmin β) j

private theorem isPinvSupported_scaledAdjoint (A : Matrix (Fin a) (Fin b) ℂ) (β : ℝ) :
    IsPinvSupported A ((β : ℂ) • Aᴴ) := by
  constructor
  · rw [Matrix.mul_smul, A.pinv_mul_self_mul_conjTranspose]
  · rw [Matrix.smul_mul, A.conjTranspose_mul_mul_pinv]

/-- **Exercise 20(a,b)**, Equations (95)–(97) of [benIsrael2003generalized], Chapter 7.
The first-order method with scaled-adjoint start converges and has the stated
affine recurrence and range residual powers. -/
theorem exercise_7_20 {A : Matrix (Fin a) (Fin b) ℂ}
    (hA : A ≠ 0) {β : ℝ} (hβ : 0 < β ∧ β < 2 / leftGramEigenvalue A 0) :
    let X₀ := ((β : ℂ) • Aᴴ)
    let X := pinvFirstOrderIterate A X₀
    Tendsto X atTop (𝓝 A.pinv) ∧
      ∀ k, X (k + 1) = X k * (1 - (β : ℂ) • (A * Aᴴ)) + X₀ ∧
        X k = X₀ * ∑ j ∈ range (k + 1), (1 - (β : ℂ) • (A * Aᴴ)) ^ j ∧
        pinvIterationResidual A (X k) = (A * A.pinv - (β : ℂ) • (A * Aᴴ)) ^ (k + 1) := by
  have hX₀ := isPinvSupported_scaledAdjoint A β
  have hρ := (spectralRadius_scaled_adjoint_start hA β).mpr hβ
  refine ⟨(theorem_3 hX₀ hρ).1, fun k => ⟨?_, ?_, ?_⟩⟩
  · rw [pinvFirstOrderIterate_succ_eq_initialError, Matrix.mul_smul]
  · rw [pinvFirstOrderIterate_eq_geom_computable, Matrix.mul_smul]
  · rw [pinvFirstOrderIterate_residual_pow hX₀.right, pinvIterationResidual, Matrix.mul_smul]

/-- **Exercise 21** of [benIsrael2003generalized], Chapter 7.
The higher-order method with scaled-adjoint start converges. At index `k`
its range residual is the initial residual raised to the power `p^k`. -/
theorem exercise_7_21 {A : Matrix (Fin a) (Fin b) ℂ}
    (hA : A ≠ 0) {β : ℝ} (hβ : 0 < β ∧ β < 2 / leftGramEigenvalue A 0)
    {p : ℕ} (hp : 2 ≤ p) :
    let X := pinvHigherOrderIterate A ((β : ℂ) • Aᴴ) p
    Tendsto X atTop (𝓝 A.pinv) ∧
      ∀ k, pinvIterationResidual A (X k) = (A * A.pinv - (β : ℂ) • (A * Aᴴ)) ^ (p ^ k) := by
  have hX₀ := isPinvSupported_scaledAdjoint A β
  have hρ := (spectralRadius_scaled_adjoint_start hA β).mpr hβ
  refine ⟨(theorem_4 hX₀ hρ hp).1, fun k => ?_⟩
  rw [pinvHigherOrderIterate_residual_pow hX₀ (by omega), pinvIterationResidual, Matrix.mul_smul]

end ScaledAdjoint

omit [DecidableEq n] in
/-- **Equation (86)** of [benIsrael2003generalized], Chapter 7.
The higher-order step can be expressed as an additive correction using the
geometric sum with one fewer term. -/
theorem pinvHigherOrderStep_eq_correction (A : Matrix m n ℂ) (X : Matrix n m ℂ) (p : ℕ) :
    X * (∑ j ∈ range (p + 1), (1 - A * X) ^ j) =
      X + (X * ∑ j ∈ range p, (1 - A * X) ^ j) * (1 - A * X) := by
  let T : Matrix m m ℂ := 1 - A * X
  change X * (∑ j ∈ range (p + 1), T ^ j) =
    X + (X * ∑ j ∈ range p, T ^ j) * T
  rw [sum_range_succ', Matrix.mul_add, pow_zero, Matrix.mul_one, Matrix.mul_assoc X, Matrix.sum_mul]
  simp only [pow_succ, add_comm]

omit [DecidableEq n] in
/-- **Exercise 24** of [benIsrael2003generalized], Chapter 7.
Multiplying the inverse approximations on the left by `A` gives the range projection sequence. -/
theorem projectionHigherOrderIterate_eq_mul (A : Matrix m n ℂ) (X₀ : Matrix n m ℂ)
    (p k : ℕ) :
    projectionHigherOrderIterate (A * X₀) p k = A * pinvHigherOrderIterate A X₀ p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [projectionHigherOrderIterate, pinvHigherOrderIterate, ih, Matrix.mul_assoc]

section IterationCosts

/-- **Exercise 23**, Equation (103) of [benIsrael2003generalized], Chapter 7.
The number of steps is the ceiling of the logarithm ratio from the textbook. -/
theorem exercise_7_23_iterationCount_log (p k : ℕ) :
    ⌈Real.log ((k + 1 : ℕ) : ℝ) / Real.log (p : ℝ)⌉₊ = Nat.clog p (k + 1) :=
  Real.natCeil_logb_natCast p (k + 1)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Exercise 23**, Equation (105) of [benIsrael2003generalized], Chapter 7.
The ordered product of factors `1 + T^(2^j)` for `j < q`. -/
def dyadicPinvGeomProduct (T : Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => 1
  | q + 1 => dyadicPinvGeomProduct T q * (1 + T ^ ((2 : ℕ) ^ q))

/-- **Exercise 23**, Equation (105) of [benIsrael2003generalized], Chapter 7.
For dyadic order the geometric sum is the ordered product used by the cheaper recurrence. -/
theorem dyadicPinvGeomProduct_eq_sum (T : Matrix ι ι ℂ) (q : ℕ) :
    dyadicPinvGeomProduct T q = ∑ j ∈ range ((2 : ℕ) ^ q), T ^ j := by
  induction q with
  | zero => simp [dyadicPinvGeomProduct]
  | succ q ih =>
    rw [dyadicPinvGeomProduct, ih, pow_succ (2 : ℕ), Nat.mul_two, sum_range_add,
      Matrix.mul_add, Matrix.mul_one, Matrix.sum_mul]
    congr 1
    apply sum_congr rfl
    intro j _
    rw [← pow_add, Nat.add_comm]

/-- **Exercise 23**, Equations (104) and (106) of [benIsrael2003generalized], Chapter 7.
The dyadic product has strictly lower modeled cost than the nested sum for `q ≥ 3`. -/
theorem dyadicPinvStepCost_lt (aspectRatio : ℝ) (q : ℕ) (hq : 3 ≤ q) :
    2 * ((q : ℝ) - 1) + 2 * aspectRatio < ((2 : ℕ) ^ q : ℝ) - 2 + 2 * aspectRatio := by
  have h : 2 * q < 2 ^ q := by
    induction q, hq using Nat.le_induction with
    | base => decide
    | succ q hq ih =>
      rw [pow_succ]
      omega
  have h' : 2 * (q : ℝ) < (2 : ℝ) ^ q := by exact_mod_cast h
  norm_num at h' ⊢
  linarith

/-- The first-order multiplication cost in **Exercise 23** of
[benIsrael2003generalized], Chapter 7. -/
def pinvFirstOrderStepCost (aspectRatio : ℝ) : ℝ := 2 * aspectRatio

/-- **Exercise 23**, Equations (104) and (106) of [benIsrael2003generalized],
Chapter 7. For higher orders `p ≥ 2`, the step cost uses the dyadic
factorization when the order is a power of two. -/
noncomputable def pinvModeledStepCost (aspectRatio : ℝ) (p : ℕ) : ℝ := by
  classical
  exact if ∃ q : ℕ, 1 ≤ q ∧ p = 2 ^ q then
    2 * ((Nat.log 2 p : ℝ) - 1) + 2 * aspectRatio
  else (p : ℝ) - 2 + 2 * aspectRatio

/-- **Exercise 23**, Equations (107a,b) of [benIsrael2003generalized], Chapter 7.
An optimal order reaches the target index with the least modeled effort. -/
def IsOptimalPinvOrder (aspectRatio : ℝ) (k p : ℕ) : Prop :=
  IsLeast ((fun q : ℕ => pinvModeledStepCost aspectRatio q * Nat.clog q (k + 1)) ''
    Set.Ici 2) (pinvModeledStepCost aspectRatio p * Nat.clog p (k + 1)) ∧ 2 ≤ p

/-- **Exercise 23**, Equation (108) of [benIsrael2003generalized], Chapter 7.
The approximate optimum minimizes the ratio of modeled step cost to logarithmic progress. -/
def IsApproxOptimalPinvOrder (aspectRatio : ℝ) (p : ℕ) : Prop :=
  IsLeast ((fun q : ℕ => pinvModeledStepCost aspectRatio q / Real.log (q : ℝ)) ''
    Set.Ici 2) (pinvModeledStepCost aspectRatio p / Real.log (p : ℝ)) ∧ 2 ≤ p

/-- **Exercise 23**, Equations (107a′,b′) of [benIsrael2003generalized], Chapter 7.
Replacing the ceiling in the step count by the corresponding real number gives
a lower bound for the modeled effort. -/
theorem pinvModeledEffort_lower_bound (aspectRatio : ℝ) (hRatio : 0 ≤ aspectRatio)
    (p k : ℕ) (hp : 2 ≤ p) :
    Real.log ((k + 1 : ℕ) : ℝ) * (pinvModeledStepCost aspectRatio p / Real.log (p : ℝ)) ≤
      pinvModeledStepCost aspectRatio p * Nat.clog p (k + 1) := by
  have hc : 0 ≤ pinvModeledStepCost aspectRatio p := by
    classical
    unfold pinvModeledStepCost
    split_ifs with h
    · obtain ⟨q, hq, rfl⟩ := h
      rw [Nat.log_pow (by decide : 1 < (2 : ℕ))]
      have hq' : 1 ≤ (q : ℝ) := by exact_mod_cast hq
      linarith
    · have hp' : 2 ≤ (p : ℝ) := by exact_mod_cast hp
      linarith
  have hceil :
      Real.log ((k + 1 : ℕ) : ℝ) / Real.log (p : ℝ) ≤ (Nat.clog p (k + 1) : ℝ) := by
    rw [← exercise_7_23_iterationCount_log]
    exact Nat.le_ceil _
  rw [_root_.mul_div_left_comm]
  exact mul_le_mul_of_nonneg_left hceil hc

end IterationCosts

/-- **Exercise 25** of [benIsrael2003generalized], Chapter 7.
A Hermitian starting projection yields Hermitian iterates. -/
theorem projectionHigherOrderIterate_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Y₀ : Matrix ι ι ℂ} (hP : IsIdempotentElem P) (hPH : P.IsHermitian)
    (hL : P * Y₀ = Y₀) (hR : Y₀ * P = Y₀) (hYH : Y₀.IsHermitian)
    {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    (projectionHigherOrderIterate Y₀ p k).IsHermitian := by
  have h := projectionHigherOrderIterate_residual hP hL hR hp k
  have hy : projectionHigherOrderIterate Y₀ p k = P - (P - Y₀) ^ (p ^ k) := by
    rw [← h, sub_sub_cancel]
  rw [hy]
  exact hPH.sub ((hPH.sub hYH).pow _)

/-- **Exercise 26**, Equation (113) of [benIsrael2003generalized], Chapter 7.
The integer ceiling of the real trace gives the stated lower bound on the rank. -/
theorem exercise_7_26_int (A : Matrix m n ℂ) {Y₀ : Matrix m m ℂ}
    (hL : (A * A.pinv) * Y₀ = Y₀) (hR : Y₀ * (A * A.pinv) = Y₀)
    (hYH : Y₀.IsHermitian) (hρ : spectralRadius ℂ (A * A.pinv - Y₀) < 1)
    {p : ℕ} (hp : 2 ≤ p) (hEven : Even p) (k : ℕ) :
    ⌈(projectionHigherOrderIterate Y₀ p (k + 1)).trace.re⌉ ≤ (A.rank : ℤ) := by
  obtain ⟨hmono, hlim⟩ := exercise_7_25 A hL hR hYH hρ hp hEven
  exact Int.ceil_le.mpr (by exact_mod_cast hmono.ge_of_tendsto hlim k)

/-- **Equations (67) and (67′)** of [benIsrael2003generalized], Chapter 7.
The range residual for the adjoint is the adjoint of the row-space residual. -/
theorem pinvIterationResidual_conjTranspose (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    pinvIterationResidual Aᴴ Xᴴ = (A.pinv * A - X * A)ᴴ := by
  rw [pinvIterationResidual, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul,
    A.pinv_conjTranspose]

/-- **Equation (67′)** of [benIsrael2003generalized], Chapter 7.
The residual on the row space of the matrix. -/
noncomputable def pinvRowIterationResidual (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    Matrix n n ℂ :=
  A.pinv * A - X * A

private theorem conjTranspose_rangeResidual (A : Matrix m n ℂ) (Z : Matrix m n ℂ) :
    (pinvIterationResidual Aᴴ Z)ᴴ = pinvRowIterationResidual A Zᴴ := by
  have h := pinvIterationResidual_conjTranspose A Zᴴ
  rw [conjTranspose_conjTranspose] at h
  exact (congrArg Matrix.conjTranspose h).trans (conjTranspose_conjTranspose _)

private theorem IsPinvSupported.conjTranspose {A : Matrix m n ℂ} {X : Matrix n m ℂ}
    (h : IsPinvSupported A X) : IsPinvSupported Aᴴ Xᴴ := by
  constructor
  · simpa only [conjTranspose_mul, ← A.pinv_conjTranspose] using
      congrArg Matrix.conjTranspose h.right
  · simpa only [conjTranspose_mul, ← A.pinv_conjTranspose] using
      congrArg Matrix.conjTranspose h.left

/-- **Equations (72′)–(73′)** of [benIsrael2003generalized], Chapter 7.
The dual order-`p` iterate is the conjugate transpose of the iterate for the adjoint. -/
def pinvDualHigherOrderIterate (A : Matrix m n ℂ) (X₀ : Matrix n m ℂ) (p k : ℕ) :
    Matrix n m ℂ := (pinvHigherOrderIterate Aᴴ X₀ᴴ p k)ᴴ

omit [DecidableEq m] in
/-- **Equation (84)** of [benIsrael2003generalized], Chapter 7, in row-space form.
The geometric factor in the dual iteration acts on the left. -/
theorem pinvDualHigherOrderIterate_succ (A : Matrix m n ℂ) (X₀ : Matrix n m ℂ) (p k : ℕ) :
    let X := pinvDualHigherOrderIterate A X₀ p k
    pinvDualHigherOrderIterate A X₀ p (k + 1) =
      (∑ j ∈ range p, (1 - X * A) ^ j) * X := by
  dsimp only [pinvDualHigherOrderIterate]
  rw [pinvHigherOrderIterate]
  simp only [conjTranspose_mul, conjTranspose_sum, conjTranspose_pow,
    conjTranspose_sub, conjTranspose_one, conjTranspose_conjTranspose]

omit [DecidableEq m] in
/-- **Theorem 4** of [benIsrael2003generalized], Chapter 7, in row-space
form. Each step raises the row-space residual to the chosen order. -/
theorem pinvDualHigherOrderIterate_residual_succ {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (h₀ : IsPinvSupported A X₀) {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    pinvRowIterationResidual A (pinvDualHigherOrderIterate A X₀ p (k + 1)) =
      pinvRowIterationResidual A (pinvDualHigherOrderIterate A X₀ p k) ^ p := by
  classical
  simpa only [conjTranspose_rangeResidual, conjTranspose_pow, pinvDualHigherOrderIterate] using
    congrArg Matrix.conjTranspose (pinvHigherOrderIterate_residual_succ h₀.conjTranspose hp k)

omit [DecidableEq m] in
/-- **Equation (89)** of [benIsrael2003generalized], Chapter 7, in row-space
form. The residual after `k` higher-order steps is the `p^k` power. -/
theorem pinvDualHigherOrderIterate_residual_pow {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (h₀ : IsPinvSupported A X₀) {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    pinvRowIterationResidual A (pinvDualHigherOrderIterate A X₀ p k) =
      pinvRowIterationResidual A X₀ ^ (p ^ k) := by
  classical
  simpa only [conjTranspose_rangeResidual, conjTranspose_pow, pinvDualHigherOrderIterate,
    conjTranspose_conjTranspose] using
    congrArg Matrix.conjTranspose (pinvHigherOrderIterate_residual_pow h₀.conjTranspose hp k)

omit [DecidableEq m] in
/-- **Equation (85)** of [benIsrael2003generalized], Chapter 7, in
row-space form. Submultiplicativity gives the order bound. -/
theorem pinvDualHigherOrderIterate_residual_bound {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (h₀ : IsPinvSupported A X₀) {p : ℕ} (hp : p ≠ 0)
    (ν : Matrix n n ℂ → ℝ) (hn : ∀ M, 0 ≤ ν M) (hm : ∀ M N, ν (M * N) ≤ ν M * ν N)
    (k : ℕ) :
    ν (pinvRowIterationResidual A (pinvDualHigherOrderIterate A X₀ p (k + 1))) ≤
      ν (pinvRowIterationResidual A (pinvDualHigherOrderIterate A X₀ p k)) ^ p := by
  classical
  rw [pinvDualHigherOrderIterate_residual_succ h₀ hp]
  exact submultiplicative_pow_le ν hn hm _ hp

omit [DecidableEq m] in
/-- **Theorem 4** of [benIsrael2003generalized], Chapter 7, in row-space form.
The row-space iteration converges under the spectral radius bound on its initial residual. -/
theorem pinvDualHigherOrderIterate_tendsto {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (h₀ : IsPinvSupported A X₀) (hρ : spectralRadius ℂ (A.pinv * A - X₀ * A) < 1)
    {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (pinvDualHigherOrderIterate A X₀ p) atTop (𝓝 A.pinv) := by
  classical
  have hρ' : spectralRadius ℂ (pinvIterationResidual Aᴴ X₀ᴴ) < 1 := by
    rwa [pinvIterationResidual_conjTranspose, ← star_eq_conjTranspose, spectralRadius_star]
  have hc : Continuous (fun X : Matrix m n ℂ => Xᴴ) := continuous_id.matrix_conjTranspose
  have h := (hc.tendsto (Aᴴ.pinv)).comp (theorem_4 h₀.conjTranspose hρ' hp).1
  rw [A.pinv_conjTranspose, conjTranspose_conjTranspose] at h
  exact h

/-- **Equations (72′)–(73′)** of [benIsrael2003generalized], Chapter 7.
The dual first-order iterate uses the fixed correction on the right. -/
def pinvDualFirstOrderIterate (A : Matrix m n ℂ) (X₀ : Matrix n m ℂ) (k : ℕ) :
    Matrix n m ℂ := (pinvFirstOrderIterate Aᴴ X₀ᴴ k)ᴴ

omit [DecidableEq m] in
/-- **Equation (77)** of [benIsrael2003generalized], Chapter 7, in row-space form.
The row-space computable residual multiplies the fixed approximate inverse. -/
theorem pinvDualFirstOrderIterate_succ (A : Matrix m n ℂ) (X₀ : Matrix n m ℂ) (k : ℕ) :
    let X := pinvDualFirstOrderIterate A X₀ k
    pinvDualFirstOrderIterate A X₀ (k + 1) = X + (1 - X * A) * X₀ := by
  dsimp only [pinvDualFirstOrderIterate]
  rw [pinvFirstOrderIterate, conjTranspose_add, conjTranspose_mul,
    conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
    conjTranspose_conjTranspose A, conjTranspose_conjTranspose X₀]

omit [DecidableEq m] in
/-- **Theorem 3** of [benIsrael2003generalized], Chapter 7, in row-space
form. The initial residual acts on the right at each step. -/
theorem pinvDualFirstOrderIterate_residual_succ {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (h₀ : IsPinvSupported A X₀) (k : ℕ) :
    pinvRowIterationResidual A (pinvDualFirstOrderIterate A X₀ (k + 1)) =
      pinvRowIterationResidual A (pinvDualFirstOrderIterate A X₀ k) *
        pinvRowIterationResidual A X₀ := by
  classical
  simpa only [conjTranspose_mul, conjTranspose_rangeResidual, pinvDualFirstOrderIterate,
    conjTranspose_conjTranspose] using
    congrArg Matrix.conjTranspose (pinvFirstOrderIterate_residual_succ h₀.conjTranspose.right k)

omit [DecidableEq m] in
/-- **Equation (78)** of [benIsrael2003generalized], Chapter 7, in
row-space form. Each step contracts the residual whenever its initial
norm is less than one. -/
theorem pinvDualFirstOrderIterate_residual_bound {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (h₀ : IsPinvSupported A X₀)
    (ν : Matrix n n ℂ → ℝ) (hm : ∀ M N, ν (M * N) ≤ ν M * ν N) (k : ℕ) :
    ν (pinvRowIterationResidual A (pinvDualFirstOrderIterate A X₀ (k + 1))) ≤
      ν (pinvRowIterationResidual A (pinvDualFirstOrderIterate A X₀ k)) *
        ν (pinvRowIterationResidual A X₀) := by
  classical
  rw [pinvDualFirstOrderIterate_residual_succ h₀]
  exact hm _ _

omit [DecidableEq m] in
/-- **Theorem 3** of [benIsrael2003generalized], Chapter 7, in row-space form.
The dual first-order iteration converges under the spectral radius bound on its initial residual. -/
theorem pinvDualFirstOrderIterate_tendsto {A : Matrix m n ℂ} {X₀ : Matrix n m ℂ}
    (h₀ : IsPinvSupported A X₀) (hρ : spectralRadius ℂ (A.pinv * A - X₀ * A) < 1) :
    Tendsto (pinvDualFirstOrderIterate A X₀) atTop (𝓝 A.pinv) := by
  classical
  have hρ' : spectralRadius ℂ (pinvIterationResidual Aᴴ X₀ᴴ) < 1 := by
    rwa [pinvIterationResidual_conjTranspose, ← star_eq_conjTranspose, spectralRadius_star]
  have hc : Continuous (fun X : Matrix m n ℂ => Xᴴ) := continuous_id.matrix_conjTranspose
  have h := (hc.tendsto Aᴴ.pinv).comp (theorem_3 h₀.conjTranspose hρ').1
  rw [A.pinv_conjTranspose, conjTranspose_conjTranspose] at h
  exact h

omit [DecidableEq m] in
/-- **Exercise 24** of [benIsrael2003generalized], Chapter 7.
Convergent pseudoinverse approximations induce convergent approximations to both orthogonal
projections, by multiplying on the left and on the right. -/
theorem tendsto_projection_products {A : Matrix m n ℂ} {X : ℕ → Matrix n m ℂ}
    (h : Tendsto X atTop (𝓝 A.pinv)) :
    Tendsto (fun k => A * X k) atTop (𝓝 (A * A.pinv)) ∧
      Tendsto (fun k => X k * A) atTop (𝓝 (A.pinv * A)) := by
  have hL : Continuous (fun Z : Matrix n m ℂ => A * Z) := continuous_const.matrix_mul continuous_id
  have hR : Continuous (fun Z : Matrix n m ℂ => Z * A) := continuous_id.matrix_mul continuous_const
  exact ⟨(hL.tendsto _).comp h, (hR.tendsto _).comp h⟩

omit [DecidableEq m] in
/-- **Equation (110)** of [benIsrael2003generalized], Chapter 7.
The two range-projection support equations characterize products
of the form `A * B * Aᴴ`. -/
theorem projectionStart_iff_exists_mul_conjTranspose (A : Matrix m n ℂ) (Y : Matrix m m ℂ) :
    ((A * A.pinv) * Y = Y ∧ Y * (A * A.pinv) = Y) ↔
      ∃ B : Matrix n n ℂ, Y = A * B * Aᴴ := by
  constructor
  · rintro ⟨hL, hR⟩
    refine ⟨A.pinv * Y * A.pinvᴴ, ?_⟩
    have h : A.pinvᴴ * Aᴴ = A * A.pinv := by
      rw [← conjTranspose_mul, A.isHermitian_mul_pinv.eq]
    calc
      Y = (A * A.pinv) * Y * (A * A.pinv) := by rw [hL, hR]
      _ = (A * A.pinv) * Y * (A.pinvᴴ * Aᴴ) := congrArg (fun Z => (A * A.pinv) * Y * Z) h.symm
      _ = A * (A.pinv * Y * A.pinvᴴ) * Aᴴ := by simp only [Matrix.mul_assoc]
  · rintro ⟨B, rfl⟩
    constructor
    · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, A.mul_pinv_mul_self]
    · have h : Aᴴ * (A * A.pinv) = Aᴴ := A.conjTranspose_mul_mul_pinv
      rw [Matrix.mul_assoc (A * B), h]

section ScaledAdjoint

variable {a b : ℕ}

/-- **Exercise 20(c)**, Equation (100) of [benIsrael2003generalized], Chapter 7.
Every scale other than the one balancing the extreme residual magnitudes
gives a strictly larger norm for each positive residual power. -/
theorem exercise_7_20_optimalScale_unique {A : Matrix (Fin a) (Fin b) ℂ}
    (hA : A ≠ 0) {j : ℕ} (hj : j ≠ 0) :
    let l := leftGramEigenvalue A (A.rank - 1)
    let u := leftGramEigenvalue A 0
    let β₀ := 2 / (u + l)
    ∀ β : ℝ, β ≠ β₀ → ‖pinvIterationResidual A ((β₀ : ℂ) • Aᴴ) ^ j‖ <
      ‖pinvIterationResidual A ((β : ℂ) • Aᴴ) ^ j‖ := by
  let l := leftGramEigenvalue A (A.rank - 1)
  let u := leftGramEigenvalue A 0
  let β₀ := 2 / (u + l)
  let δ := (u - l) / (u + l)
  have hr : 0 < A.rank := Nat.pos_of_ne_zero (hA ∘ rank_eq_zero_iff.mp)
  have hl : 0 < l := leftGramEigenvalue_pos_of_lt_rank A (by omega)
  have hlu : l ≤ u := leftGramEigenvalue_antitone A (Nat.zero_le _)
  have hu : 0 < u := hl.trans_le hlu
  have hd : 0 < u + l := add_pos hu hl
  have hδ : 0 ≤ δ := div_nonneg (sub_nonneg.mpr hlu) hd.le
  have hlEnd : 1 - β₀ * l = δ := by
    dsimp only [β₀, δ]
    field_simp [hd.ne']
    ring
  have huEnd : 1 - β₀ * u = -δ := by
    dsimp only [β₀, δ]
    field_simp [hd.ne']
    ring
  change ∀ β : ℝ, β ≠ β₀ → ‖pinvIterationResidual A ((β₀ : ℂ) • Aᴴ) ^ j‖ <
    ‖pinvIterationResidual A ((β : ℂ) • Aᴴ) ^ j‖
  intro β hβ
  rw [(exercise_7_20_optimalScale hA hj).1, scaledAdjointResidual_norm_pow_eq hA β hj]
  apply pow_lt_pow_left₀ _ hδ hj
  rcases lt_or_gt_of_ne hβ with hlt | hgt
  · calc
      δ = 1 - β₀ * l := hlEnd.symm
      _ < 1 - β * l := sub_lt_sub_left (mul_lt_mul_of_pos_right hlt hl) _
      _ ≤ |1 - β * l| := le_abs_self _
      _ ≤ _ := le_max_left _ _
  · calc
      δ = -(1 - β₀ * u) := by rw [huEnd, neg_neg]
      _ < -(1 - β * u) :=
        neg_lt_neg (sub_lt_sub_left (mul_lt_mul_of_pos_right hgt hu) _)
      _ ≤ |1 - β * u| := neg_le_abs _
      _ ≤ _ := le_max_right _ _

end ScaledAdjoint

omit [DecidableEq m] in
/-- **Exercise 27** of [benIsrael2003generalized], Chapter 7.
Applied to adjoints, the product iteration computes a product with the inverse on the left. -/
theorem exercise_7_27_dual {q : Type*} {A : Matrix m n ℂ} (B : Matrix m q ℂ)
    {X₀ : Matrix n m ℂ} (h₀ : IsPinvSupported A X₀)
    (hρ : spectralRadius ℂ (A.pinv * A - X₀ * A) < 1) {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun k => ((pinvProductIterate Aᴴ Bᴴ X₀ᴴ p k).1)ᴴ) atTop (𝓝 (A.pinv * B)) := by
  classical
  have hρ' : spectralRadius ℂ (pinvIterationResidual Aᴴ X₀ᴴ) < 1 := by
    rwa [pinvIterationResidual_conjTranspose, ← star_eq_conjTranspose, spectralRadius_star]
  have hc : Continuous (fun Z : Matrix q n ℂ => Zᴴ) := continuous_id.matrix_conjTranspose
  have h := (hc.tendsto (Bᴴ * Aᴴ.pinv)).comp
    (exercise_7_27 Bᴴ h₀.conjTranspose hρ' hp)
  rw [conjTranspose_mul, A.pinv_conjTranspose, conjTranspose_conjTranspose,
    conjTranspose_conjTranspose] at h
  exact h

/-- **Exercise 23**, Equation (106) of [benIsrael2003generalized], Chapter 7.
The modeled step cost on a power-of-two order is the dyadic multiplication count. -/
theorem pinvModeledStepCost_dyadic (aspectRatio : ℝ) {q : ℕ} (hq : 1 ≤ q) :
    pinvModeledStepCost aspectRatio (2 ^ q) = 2 * ((q : ℝ) - 1) + 2 * aspectRatio := by
  classical
  unfold pinvModeledStepCost
  rw [ite_eq_left (show ∃ j : ℕ, 1 ≤ j ∧ 2 ^ q = 2 ^ j from ⟨q, hq, rfl⟩),
    Nat.log_pow (by decide : 1 < (2 : ℕ))]

/-- The order-two and fixed first-order steps in **Exercise 23**
have the same modeled multiplication cost. -/
theorem pinvModeledStepCost_two (aspectRatio : ℝ) :
    pinvModeledStepCost aspectRatio 2 = pinvFirstOrderStepCost aspectRatio := by
  rw [show (2 : ℕ) = 2 ^ 1 by rfl, pinvModeledStepCost_dyadic _ le_rfl]
  simp [pinvFirstOrderStepCost]

/-- **Exercise 23**, Equation (104) of [benIsrael2003generalized], Chapter 7.
The modeled step cost for a nondyadic order is the nested multiplication count. -/
theorem pinvModeledStepCost_nondyadic (aspectRatio : ℝ) {p : ℕ}
    (hp : ¬ ∃ q : ℕ, 1 ≤ q ∧ p = 2 ^ q) :
    pinvModeledStepCost aspectRatio p = (p : ℝ) - 2 + 2 * aspectRatio := by
  classical
  unfold pinvModeledStepCost
  rw [ite_eq_right hp]

/-- **Exercise 25** of [benIsrael2003generalized], Chapter 7.
The trace of each Hermitian projection iterate is real. -/
theorem projectionHigherOrderIterate_trace_im {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Y₀ : Matrix ι ι ℂ} (hP : IsIdempotentElem P) (hPH : P.IsHermitian)
    (hL : P * Y₀ = Y₀) (hR : Y₀ * P = Y₀) (hYH : Y₀.IsHermitian)
    {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    (projectionHigherOrderIterate Y₀ p k).trace.im = 0 := by
  have hH := projectionHigherOrderIterate_isHermitian hP hPH hL hR hYH hp k
  have h := congrArg Matrix.trace hH.eq
  rw [trace_conjTranspose] at h
  have h' := congrArg Complex.im h
  change -(projectionHigherOrderIterate Y₀ p k).trace.im =
    (projectionHigherOrderIterate Y₀ p k).trace.im at h'
  linarith

end BenIsraelGreville.Chapter07
