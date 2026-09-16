import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Stationary.Splitting

/-!
# The classical stationary iterations as sweeps on vectors

The splitting `A = P - N` of `Numlib/Stationary/Splitting` is the object the convergence theory is
about; what a textbook writes down is the *sweep*, the map `x ↦ x_{new}` on `n → 𝕜` that a
program executes.  This module defines the sweeps and proves each equal to the step of its
splitting, which is the one lemma every consumer needs before it can quote a convergence theorem
about a componentwise formula.

* `Stationary.Splitting.mulVecStep s b x = s.m⁻¹ *ᵥ (s.n *ᵥ x + b)` is one step of `P x_{k+1} =
  N x_k + b` ([quarteroni2000numerical] (4.6); [saad2003iterative] (4.28)), in its three forms:
  the update form `x + P⁻¹ (b - A x)` ((4.7)), the affine form `B x + P⁻¹ b`, and — over an
  `RCLike` field, under `WithLp.toLp 2` — `Stationary.step` of the operator `toEuclideanCLM B`,
  through which the theory of `Numlib/Stationary/Basic` applies.  Its fixed points are the
  solutions of `A x = b` (consistency, [quarteroni2000numerical] Definition 4.1).
* `Matrix.jorSweep` is the componentwise JOR formula ([quarteroni2000numerical], the display after
  (4.11); `ω = 1` is Jacobi, (4.10)); `Matrix.sorSweep` and `Matrix.backwardSorSweep` are the SOR
  and backward SOR sweeps ([quarteroni2000numerical] (4.16) multiplied through by `D`, and §4.2.6),
  with `ω = 1` the two Gauss–Seidel sweeps; the componentwise recursion (4.15) of the SOR sweep is
  the theorem `Matrix.sorSweep_apply`, and (4.13) is its case `ω = 1`.
* `Matrix.jorSweep_eq_mulVecStep`, `Matrix.sorSweep_eq_mulVecStep` and
  `Matrix.backwardSorSweep_eq_mulVecStep` identify the sweeps with the steps of
  `Matrix.jorSplitting`, `Matrix.sorSplitting`, `Matrix.backwardSorSplitting`, and
  `Matrix.ssorSweep_eq_mulVecStep` says
  that a forward SOR sweep followed by a backward one is the step of `Matrix.ssorSplitting`
  ([quarteroni2000numerical] §4.2.6, the elimination of `x^{(k+1/2)}`; at `ω = 1` the symmetric
  Gauss–Seidel method (4.21)).

## Design

A sweep is *defined* by its matrix formula (`sorSweep A ω b x = (D + ωL)⁻¹ *ᵥ (((1 - ω) D - ωU)
*ᵥ x + ω b)`) and the componentwise recursion is a *theorem* about it, obtained by reading the
triangular system row by row along the linear order of `n`.  This keeps the definitions total and
index-type-agnostic and puts the induction where it belongs; the JOR sweep, whose components are
independent, is defined componentwise.  Everything is stated for `Matrix n n 𝕜` over a field with
`[LinearOrder n]` (the sweep order) and vectors `n → 𝕜`; no analysis enters except in the
`EuclideanSpace` transport `Stationary.Splitting.toLp_mulVecStep`.
-/

open Finset

namespace Stationary.Splitting

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [Field 𝕜] {A : Matrix n n 𝕜}

open Matrix

/-- One step of the splitting iteration `P x_{k+1} = N x_k + b` on `n → 𝕜`: `mulVecStep s b x =
P⁻¹ (N x + b)` ([quarteroni2000numerical] (4.6); [saad2003iterative] (4.28)). -/
noncomputable def mulVecStep (s : Splitting A) (b x : n → 𝕜) : n → 𝕜 :=
  s.m⁻¹ *ᵥ (s.n *ᵥ x + b)

variable (s : Splitting A) (b x : n → 𝕜)

/-- The update form of the step: `x_{k+1} = x_k + P⁻¹ r_k` with the residual `r_k = b - A x_k`
([quarteroni2000numerical] (4.7)–(4.8)). -/
theorem mulVecStep_eq_add_inv_mulVec : mulVecStep s b x = x + s.m⁻¹ *ᵥ (b - A *ᵥ x) := by
  have hn : s.n = s.m - A := rfl
  rw [mulVecStep, hn, sub_mulVec, show s.m *ᵥ x - A *ᵥ x + b = s.m *ᵥ x + (b - A *ᵥ x) by abel,
    mulVec_add, nonsing_inv_mulVec_mulVec s.isUnit]

/-- The step multiplied through by `P`: `P (x_{k+1} - x_k) = b - A x_k`. -/
theorem mulVec_mulVecStep_sub : s.m *ᵥ (mulVecStep s b x - x) = b - A *ᵥ x := by
  rw [mulVecStep_eq_add_inv_mulVec, add_sub_cancel_left, mulVec_nonsing_inv_mulVec s.isUnit]

/-- The step is characterized by `P (y - x) = b - A x`: whatever solves the update system is the
step.  This is how a componentwise sweep is identified with the step of its splitting. -/
theorem mulVecStep_eq_of_mulVec_sub_eq {y : n → 𝕜} (h : s.m *ᵥ (y - x) = b - A *ᵥ x) :
    mulVecStep s b x = y := by
  rw [mulVecStep_eq_add_inv_mulVec, nonsing_inv_mulVec_eq s.isUnit h]
  abel

/-- The affine form of the step: `x_{k+1} = B x_k + f` with the iteration matrix `B = P⁻¹ N` and
`f = P⁻¹ b` ([quarteroni2000numerical], the sentence after (4.6)). -/
theorem mulVecStep_eq_iterationOperator_mulVec_add :
    mulVecStep s b x = s.iterationOperator *ᵥ x + s.m⁻¹ *ᵥ b := by
  rw [mulVecStep, mulVec_add, Splitting.iterationOperator_eq, ← nonsing_inv_eq_ringInverse,
    ← mulVec_mulVec]

/-- **Consistency** of the splitting iteration: `x` is a fixed point of the step iff it solves
`A x = b` ([quarteroni2000numerical] Definition 4.1 for the method (4.6); [saad2003iterative]
(4.29)). -/
theorem mulVecStep_fixed_iff : mulVecStep s b x = x ↔ A *ᵥ x = b := by
  rw [mulVecStep_eq_add_inv_mulVec, add_eq_left]
  constructor
  · intro h
    have h' := congrArg (s.m *ᵥ ·) h
    simp only [mulVec_nonsing_inv_mulVec s.isUnit, mulVec_zero] at h'
    exact (sub_eq_zero.mp h').symm
  · intro h
    rw [h, sub_self, mulVec_zero]

/-- **Two steps compose into one**: if `t.m⁻¹ = m₂⁻¹ (m₁ + m₂ - A) m₁⁻¹`, one step of the splitting
`m₁` followed by one step of the splitting `m₂` is one step of `t`
(`Stationary.Splitting.iterationOperator_eq_mul_of_inverse_m_eq` for the linear part and
`Stationary.Splitting.inverse_m_eq_iterationOperator_mul_inverse_add` for the constant term). -/
theorem mulVecStep_mulVecStep (s₁ s₂ t : Splitting A)
    (ht : Ring.inverse t.m = Ring.inverse s₂.m * (s₁.m + s₂.m - A) * Ring.inverse s₁.m) :
    mulVecStep s₂ b (mulVecStep s₁ b x) = mulVecStep t b x := by
  simp only [mulVecStep_eq_iterationOperator_mulVec_add, nonsing_inv_eq_ringInverse]
  rw [iterationOperator_eq_mul_of_inverse_m_eq s₁ s₂ t ht,
    inverse_m_eq_iterationOperator_mul_inverse_add s₁ s₂ t ht, mulVec_add, add_mulVec,
    ← mulVec_mulVec, ← mulVec_mulVec, add_assoc]

section EuclideanSpace

variable {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜}

/-- Under `WithLp.toLp 2`, the step of a splitting is the affine step `Stationary.step` of the
operator `toEuclideanCLM B` on `EuclideanSpace 𝕜 n`, with `f = P⁻¹ b`: the transport through which
the theory of `Numlib/Stationary/Basic` — error propagation, convergence factors, the a priori and
a posteriori bounds — applies to a matrix iteration. -/
theorem toLp_mulVecStep (s : Splitting A) (b x : n → 𝕜) :
    (WithLp.toLp 2 (mulVecStep s b x) : EuclideanSpace 𝕜 n) =
      Stationary.step (toEuclideanCLM (n := n) (𝕜 := 𝕜) s.iterationOperator)
        (WithLp.toLp 2 (s.m⁻¹ *ᵥ b)) (WithLp.toLp 2 x) := by
  rw [mulVecStep_eq_iterationOperator_mulVec_add, Stationary.step, toEuclideanCLM_toLp]
  rfl

end EuclideanSpace

end Stationary.Splitting

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {𝕜 : Type*} [Field 𝕜]

/-! ### The JOR and Jacobi sweeps -/

omit [LinearOrder n] in
/-- The JOR sweep: `x_i ↦ (ω / a_ii) (b_i - ∑_{j ≠ i} a_ij x_j) + (1 - ω) x_i`
([quarteroni2000numerical], the display after (4.11)).  At `ω = 1` it is the Jacobi formula
(4.10).  Every component depends on the old vector only, so it is defined componentwise. -/
noncomputable def jorSweep (A : Matrix n n 𝕜) (ω : 𝕜) (b x : n → 𝕜) : n → 𝕜 := fun i =>
  ω / A i i * (b i - ∑ j ∈ univ.erase i, A i j * x j) + (1 - ω) * x i

omit [LinearOrder n] in
/-- The JOR sweep is the step of the JOR splitting `M = ω⁻¹ D` (`Matrix.jorSplitting`): row `i` of
`ω⁻¹ D (y - x) = b - A x` is the sweep formula. -/
theorem jorSweep_eq_mulVecStep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0)
    (b : n → 𝕜) : jorSweep A ω b = Splitting.mulVecStep (jorSplitting A h hω) b := by
  have hd := (isUnit_diagPart_iff A).mp h
  funext x
  refine (Splitting.mulVecStep_eq_of_mulVec_sub_eq _ b x ?_).symm
  funext i
  have hm : (jorSplitting A h hω).m = ω⁻¹ • diagPart A := rfl
  have hi := hd i
  rw [hm, smul_mulVec, Pi.smul_apply, diagPart_mulVec_apply, Pi.sub_apply, Pi.sub_apply,
    mulVec_apply_eq_add_sum_erase, jorSweep, smul_eq_mul]
  field_simp
  ring

omit [LinearOrder n] in
/-- The Jacobi sweep is the step of the Jacobi splitting `M = D` ([quarteroni2000numerical] (4.10)
and (4.11)). -/
theorem jorSweep_one_eq_mulVecStep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) (b : n → 𝕜) :
    jorSweep A 1 b = Splitting.mulVecStep (jacobiSplitting A h) b := by
  rw [jorSweep_eq_mulVecStep A h one_ne_zero, jorSplitting_one]

/-! ### The SOR and Gauss–Seidel sweeps -/

/-- The SOR sweep as a function on vectors: `x ↦ (D + ωL)⁻¹ (((1 - ω) D - ωU) x + ω b)`, that is
[quarteroni2000numerical] (4.16) multiplied through by `D`, in the letters `D = diagPart A`,
`L = strictLower A`, `U = strictUpper A`.  At `ω = 1` it is the Gauss–Seidel sweep (4.13). -/
noncomputable def sorSweep (A : Matrix n n 𝕜) (ω : 𝕜) (b x : n → 𝕜) : n → 𝕜 :=
  (diagPart A + ω • strictLower A)⁻¹ *ᵥ (((1 - ω) • diagPart A - ω • strictUpper A) *ᵥ x + ω • b)

/-- The backward SOR sweep: `x ↦ (D + ωU)⁻¹ (((1 - ω) D - ωL) x + ω b)`, the method
`(D - ωF) x_{k+1} = [ωE + (1 - ω) D] x_k + ω b` of [quarteroni2000numerical] §4.2.6.  At `ω = 1`
it is the backward Gauss–Seidel sweep. -/
noncomputable def backwardSorSweep (A : Matrix n n 𝕜) (ω : 𝕜) (b x : n → 𝕜) : n → 𝕜 :=
  (diagPart A + ω • strictUpper A)⁻¹ *ᵥ (((1 - ω) • diagPart A - ω • strictLower A) *ᵥ x + ω • b)

/-- The SOR sweep solves the triangular system `(D + ωL) y = ((1 - ω) D - ωU) x + ω b`. -/
theorem diagPart_add_smul_strictLower_mulVec_sorSweep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    (ω : 𝕜) (b x : n → 𝕜) :
    (diagPart A + ω • strictLower A) *ᵥ sorSweep A ω b x =
      ((1 - ω) • diagPart A - ω • strictUpper A) *ᵥ x + ω • b :=
  mulVec_nonsing_inv_mulVec (isUnit_diagPart_add_smul_strictLower h ω) _

/-- The backward SOR sweep solves the triangular system `(D + ωU) y = ((1 - ω) D - ωL) x + ω b`. -/
theorem diagPart_add_smul_strictUpper_mulVec_backwardSorSweep (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) (ω : 𝕜) (b x : n → 𝕜) :
    (diagPart A + ω • strictUpper A) *ᵥ backwardSorSweep A ω b x =
      ((1 - ω) • diagPart A - ω • strictLower A) *ᵥ x + ω • b :=
  mulVec_nonsing_inv_mulVec (isUnit_diagPart_add_smul_strictUpper h ω) _

/-- **The componentwise SOR recursion** ([quarteroni2000numerical] (4.15)): with `y` the SOR sweep
from `x`,
`y_i = (ω / a_ii) (b_i - ∑_{j < i} a_ij y_j - ∑_{j > i} a_ij x_j) + (1 - ω) x_i`,
the already updated components entering for `j < i` and the old ones for `j > i`.  It is row `i` of
`(D + ωL) y = ((1 - ω) D - ωU) x + ω b`, read as a recursion along the linear order of `n`; at
`ω = 1` it is the Gauss–Seidel recursion (4.13). -/
theorem sorSweep_apply (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) (ω : 𝕜) (b x : n → 𝕜)
    (i : n) :
    sorSweep A ω b x i =
      ω / A i i * (b i - ∑ j ∈ univ.filter (· < i), A i j * sorSweep A ω b x j
        - ∑ j ∈ univ.filter (i < ·), A i j * x j) + (1 - ω) * x i := by
  have hi : A i i ≠ 0 := (isUnit_diagPart_iff A).mp h i
  have hrow := congrFun (diagPart_add_smul_strictLower_mulVec_sorSweep A h ω b x) i
  rw [add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, Pi.add_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
    diagPart_mulVec_apply, diagPart_mulVec_apply, strictLower_mulVec_apply,
    strictUpper_mulVec_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hrow
  field_simp
  linear_combination hrow

/-- **The componentwise backward SOR recursion**: the mirror image of `Matrix.sorSweep_apply`, the
updated components entering for `j > i`. -/
theorem backwardSorSweep_apply (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) (ω : 𝕜)
    (b x : n → 𝕜) (i : n) :
    backwardSorSweep A ω b x i =
      ω / A i i * (b i - ∑ j ∈ univ.filter (i < ·), A i j * backwardSorSweep A ω b x j
        - ∑ j ∈ univ.filter (· < i), A i j * x j) + (1 - ω) * x i := by
  have hi : A i i ≠ 0 := (isUnit_diagPart_iff A).mp h i
  have hrow := congrFun (diagPart_add_smul_strictUpper_mulVec_backwardSorSweep A h ω b x) i
  rw [add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, Pi.add_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
    diagPart_mulVec_apply, diagPart_mulVec_apply, strictLower_mulVec_apply,
    strictUpper_mulVec_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hrow
  field_simp
  linear_combination hrow

/-- The residual form of the SOR sweep: `(D + ωL) (y - x) = ω (b - A x)`. -/
theorem diagPart_add_smul_strictLower_mulVec_sorSweep_sub (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) (ω : 𝕜) (b x : n → 𝕜) :
    (diagPart A + ω • strictLower A) *ᵥ (sorSweep A ω b x - x) = ω • (b - A *ᵥ x) := by
  have hA : A *ᵥ x = diagPart A *ᵥ x + strictLower A *ᵥ x + strictUpper A *ᵥ x := by
    conv_lhs => rw [← diagPart_add_strictLower_add_strictUpper A]
    simp only [add_mulVec]
  rw [mulVec_sub, diagPart_add_smul_strictLower_mulVec_sorSweep A h, hA]
  simp only [add_mulVec, sub_mulVec, smul_mulVec, sub_smul, one_smul, smul_sub, smul_add]
  abel

/-- The residual form of the backward SOR sweep: `(D + ωU) (y - x) = ω (b - A x)`. -/
theorem diagPart_add_smul_strictUpper_mulVec_backwardSorSweep_sub (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) (ω : 𝕜) (b x : n → 𝕜) :
    (diagPart A + ω • strictUpper A) *ᵥ (backwardSorSweep A ω b x - x) = ω • (b - A *ᵥ x) := by
  have hA : A *ᵥ x = diagPart A *ᵥ x + strictLower A *ᵥ x + strictUpper A *ᵥ x := by
    conv_lhs => rw [← diagPart_add_strictLower_add_strictUpper A]
    simp only [add_mulVec]
  rw [mulVec_sub, diagPart_add_smul_strictUpper_mulVec_backwardSorSweep A h, hA]
  simp only [add_mulVec, sub_mulVec, smul_mulVec, sub_smul, one_smul, smul_sub, smul_add]
  abel

/-- **The SOR sweep is the step of the SOR splitting** `M = ω⁻¹ (D - ωE)` (`Matrix.sorSplitting`),
so it is `x ↦ x + (ω⁻¹ D - E)⁻¹ (b - A x)`, the display after [quarteroni2000numerical] (4.17):
scale the residual form `(D + ωL) (y - x) = ω (b - A x)` by `ω⁻¹`. -/
theorem sorSweep_eq_mulVecStep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0)
    (b : n → 𝕜) : sorSweep A ω b = Splitting.mulVecStep (sorSplitting A h hω) b := by
  funext x
  refine (Splitting.mulVecStep_eq_of_mulVec_sub_eq _ b x ?_).symm
  have hm : (sorSplitting A h hω).m = ω⁻¹ • (diagPart A + ω • strictLower A) := by
    change ω⁻¹ • diagPart A + strictLower A = _
    rw [smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul]
  rw [hm, smul_mulVec, diagPart_add_smul_strictLower_mulVec_sorSweep_sub A h, smul_smul,
    inv_mul_cancel₀ hω, one_smul]

/-- **The Gauss–Seidel sweep is the step of the Gauss–Seidel splitting** `M = D - E`
([quarteroni2000numerical] (4.13)–(4.14)). -/
theorem sorSweep_one_eq_mulVecStep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) (b : n → 𝕜) :
    sorSweep A 1 b = Splitting.mulVecStep (gaussSeidelSplitting A h) b := by
  rw [sorSweep_eq_mulVecStep A h one_ne_zero, sorSplitting_one]

/-- **The backward SOR sweep is the step of the backward SOR splitting** `M = ω⁻¹ (D - ωF)`
(`Matrix.backwardSorSplitting`). -/
theorem backwardSorSweep_eq_mulVecStep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜}
    (hω : ω ≠ 0) (b : n → 𝕜) :
    backwardSorSweep A ω b = Splitting.mulVecStep (backwardSorSplitting A h hω) b := by
  funext x
  refine (Splitting.mulVecStep_eq_of_mulVec_sub_eq _ b x ?_).symm
  have hm : (backwardSorSplitting A h hω).m = ω⁻¹ • (diagPart A + ω • strictUpper A) := by
    change ω⁻¹ • diagPart A + strictUpper A = _
    rw [smul_add, smul_smul, inv_mul_cancel₀ hω, one_smul]
  rw [hm, smul_mulVec, diagPart_add_smul_strictUpper_mulVec_backwardSorSweep_sub A h, smul_smul,
    inv_mul_cancel₀ hω, one_smul]

/-- **The backward Gauss–Seidel sweep is the step of the backward Gauss–Seidel splitting**
`M = D - F` ([quarteroni2000numerical] §4.2.6). -/
theorem backwardSorSweep_one_eq_mulVecStep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    (b : n → 𝕜) :
    backwardSorSweep A 1 b = Splitting.mulVecStep (backwardGaussSeidelSplitting A h) b := by
  rw [backwardSorSweep_eq_mulVecStep A h one_ne_zero, backwardSorSplitting_one]

/-- **One SSOR step is a forward SOR sweep followed by a backward one**: the composite is the step
of the SSOR splitting `Matrix.ssorSplitting` ([quarteroni2000numerical] §4.2.6, the elimination of
the half-step `x^{(k+1/2)}`; at `ω = 1` the symmetric Gauss–Seidel method with `B_SGS`, `b_SGS` of
(4.21); [saad2003iterative] (4.13)–(4.14)). -/
theorem ssorSweep_eq_mulVecStep (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0)
    (hω2 : ω ≠ 2) (b x : n → 𝕜) :
    backwardSorSweep A ω b (sorSweep A ω b x) =
      Splitting.mulVecStep (ssorSplitting A h hω hω2) b x := by
  rw [sorSweep_eq_mulVecStep A h hω, backwardSorSweep_eq_mulVecStep A h hω]
  exact Splitting.mulVecStep_mulVecStep b x _ _ _ (ringInverse_ssorSplitting_m A h hω hω2)

end Matrix
