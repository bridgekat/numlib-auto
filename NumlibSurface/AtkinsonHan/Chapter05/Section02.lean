import Numlib.IntegralEquations.Basic
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearSolve.Stationary.Basic
import Numlib.LinearSolve.Stationary.Splitting
import NumlibSurface.AtkinsonHan.Chapter05.Section01

/-!
# Atkinson–Han §5.2: applications of the fixed-point theorem to iterative methods

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §5.2: the four applications the book makes of
Theorem 5.1.3 — the scalar iteration on an interval, the stationary iterative methods for a
linear system, the integral equations of the second kind, and the Picard iteration for an initial
value problem.

Proofs specialize `Numlib/LinearSolve/Stationary/{Basic,Splitting}.lean`,
`Numlib/LinearAlgebra/Matrix/{Complexify,Hessenberg}.lean`, `Numlib/Nonlinear/FixedPoint.lean`
and `Numlib/IntegralEquations/Basic.lean`.

## Book-specific definitions

* `mulVecCLM` — a square matrix as a continuous linear map of `ι → ℝ`, the ambient normed space
  the backbone's `Stationary.step` operates in.
* `BookSplitting` — §5.2.2, the book's splitting `A = N - M` with `N` nonsingular, together with
  its iteration matrix `BookSplitting.iterMatrix = N⁻¹ M` and its step
  `BookSplitting.iterStep`, `N x_n = M x_{n-1} + b`. `BookSplitting.toSplitting` is the
  corresponding backbone `Stationary.Splitting`, which writes `a = m - n` — so `m = N` and
  `n = M`, a naming swap the `toSplitting_*` lemmas record.
* `jacobi`, `gaussSeidel`, `sor` — the three classical splittings of §5.2.2, each identified with
  its backbone counterpart.

## Main results

* `theorem_5_2_1` — Theorem 5.2.1, the scalar case of Theorem 5.1.3 on `[a, b]`, with
  `theorem_5_2_1_deriv` for the derivative criterion `sup_{[a,b]} |T'| ≤ α < 1`.
* `BookSplitting.equation_5_2_5` — the error equation `x - x_n = (N⁻¹M)ⁿ (x - x₀)`.
* `BookSplitting.tendsto_of_opNorm_lt_one` — §5.2.2(b), convergence when `‖N⁻¹ M‖ < 1`;
  `complexSpectralRadius_lt_one_of_opNorm_lt_one` is the implication `‖G‖ < 1 ⇒ r_σ(G) < 1`
  behind it.
* `tendsto_pow_iff_complexSpectralRadius_lt_one` — §5.2.2(c), `Gᵏ → 0` iff `r_σ(G) < 1`.
* `BookSplitting.forall_tendsto_iff`,
  `BookSplitting.forall_tendsto_iff_complexSpectralRadius_lt_one` — §5.2.2(d), convergence from
  every `x₀` iff `(N⁻¹M)ᵏ → 0` iff `r_σ(N⁻¹M) < 1`.
* `theorem_5_2_2_fredholm` — §5.2.3, the linear Fredholm equation of the second kind, whose
  contractivity constant is `|λ|⁻¹ ‖K‖` with `‖K‖` the norm formula (2.2.8).
* `theorem_5_2_2` — the nonlinear Urysohn form (5.2.10).
* `theorem_5_2_3` — the Volterra equation, where no smallness of the kernel is needed because
  the factorial estimate on the iterated kernels makes some power of the operator contract and
  Example 5.1.2 applies.
* `theorem_5_2_4` — §5.2.4, the Picard iteration for the initial value problem, in the weighted
  (Bielecki) norm in which the Picard operator itself contracts.

## Not formalized here

Theorem 5.2.4 is stated for the integral equation (the fixed-point form of the initial value
problem) on an interval to the right of `t₀`, for a scalar equation whose right-hand side is
globally Lipschitz in `u`; that is the part of the book's theorem whose proof is Bielecki's
contraction argument.  The differential form of the local existence and uniqueness statement, in
a Banach space and on a two-sided interval around `t₀` with the ball constraint `‖u - z‖ ≤ b`, is
Mathlib's `IsPicardLindelof` and is not re-derived here.
-/

open Filter Set Topology
open scoped Matrix

namespace AtkinsonHan.Chapter05

section Scalar

variable {a b α : ℝ} {T : ℝ → ℝ}

/-- On `ℝ` the norm of Definition 5.1.2 is the absolute value, which is how the book writes
Theorem 5.2.1. -/
theorem contractiveOn_real_iff {K : Set ℝ} :
    ContractiveOn T K α ↔ 0 ≤ α ∧ α < 1 ∧ ∀ u ∈ K, ∀ v ∈ K, |T u - T v| ≤ α * |u - v| := by
  simp only [ContractiveOn, Real.norm_eq_abs]

/-- **Theorem 5.2.1**: the scalar case of the Banach fixed-point theorem.  A contractive
`T : [a, b] → [a, b]` has a unique fixed point in `[a, b]`, the iteration converges to it from
every starting point, and the three error bounds (5.1.4)–(5.1.6) hold. -/
theorem theorem_5_2_1 (hab : a ≤ b) (hT : MapsTo T (Icc a b) (Icc a b))
    (hα : ContractiveOn T (Icc a b) α) :
    (∃! u, u ∈ Icc a b ∧ T u = u) ∧
      ∀ u₀ ∈ Icc a b, ∃ u ∈ Icc a b, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
        (∀ n, ‖T^[n] u₀ - u‖ ≤ α ^ n / (1 - α) * ‖u₀ - T u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α / (1 - α) * ‖T^[n] u₀ - T^[n + 1] u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α * ‖T^[n] u₀ - u‖) :=
  theorem_5_1_3 isClosed_Icc (nonempty_Icc.2 hab) hT hα

/-- The derivative criterion accompanying Theorem 5.2.1: if `|T'| ≤ α < 1` on `[a, b]` then `T` is
contractive there with constant `α`.  This is the scalar case of the backbone's
`lipschitzOnWith_of_hasFDerivWithinAt` (`Numlib/Nonlinear/FixedPoint.lean`), i.e. Mathlib's
`Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le`. -/
theorem theorem_5_2_1_deriv {T' : ℝ → ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hT : ∀ x ∈ Icc a b, HasDerivWithinAt T (T' x) (Icc a b) x)
    (hbound : ∀ x ∈ Icc a b, |T' x| ≤ α) : ContractiveOn T (Icc a b) α :=
  (contractiveOn_iff hα0).2
    ⟨hα1, (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hT hbound⟩

end Scalar

section Splittings

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A square matrix acting on `ι → ℝ` as a continuous linear map; the ambient normed space in
which the backbone's `Stationary.step` operates. -/
noncomputable def mulVecCLM (G : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin G)

omit [DecidableEq ι] in
/-- `mulVecCLM G` acts by matrix-vector multiplication. -/
@[simp]
theorem mulVecCLM_apply (G : Matrix ι ι ℝ) (x : ι → ℝ) : mulVecCLM G x = G *ᵥ x := rfl

/-- Powers of `mulVecCLM G` act by the corresponding matrix power. -/
theorem mulVecCLM_pow (G : Matrix ι ι ℝ) (k : ℕ) :
    ∀ x : ι → ℝ, (mulVecCLM G ^ k) x = G ^ k *ᵥ x := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, pow_succ]
    change (mulVecCLM G ^ k) (mulVecCLM G x) = (G ^ k * G) *ᵥ x
    rw [mulVecCLM_apply, ih, Matrix.mulVec_mulVec]

omit [DecidableEq ι] in
/-- Submultiplicativity of the operator norm, in the iterated form `‖G^k‖ ≤ ‖G‖^k`. -/
private theorem norm_mulVecCLM_pow_le (G : Matrix ι ι ℝ) (k : ℕ) :
    ‖mulVecCLM G ^ k‖ ≤ ‖mulVecCLM G‖ ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/-- Convergence of the matrix powers to `0` is convergence of `Gᵏ v` for every vector `v`. -/
private theorem tendsto_pow_zero_iff_mulVec (G : Matrix ι ι ℝ) :
    Tendsto (fun k => G ^ k) atTop (𝓝 0) ↔
      ∀ v : ι → ℝ, Tendsto (fun k => G ^ k *ᵥ v) atTop (𝓝 0) := by
  constructor
  · intro h v
    have hc : Continuous fun M : Matrix ι ι ℝ => M *ᵥ v :=
      continuous_id.matrix_mulVec continuous_const
    have hcomp := (hc.tendsto 0).comp h
    simpa [Function.comp_def] using hcomp
  · intro h
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have hj := tendsto_pi_nhds.1 (h (Pi.single j 1)) i
    simpa using hj

/-- §5.2.2: the book's splitting `A = N - M` of a square matrix, with `N` nonsingular. -/
structure BookSplitting (A : Matrix ι ι ℝ) where
  /-- The nonsingular part `N`. -/
  N : Matrix ι ι ℝ
  /-- The remaining part `M`. -/
  M : Matrix ι ι ℝ
  /-- The splitting identity `A = N - M`. -/
  eq : A = N - M
  /-- `N` is nonsingular. -/
  isUnit : IsUnit N

namespace BookSplitting

variable {A : Matrix ι ι ℝ} (s : BookSplitting A)

/-- The iteration matrix `N⁻¹ M` of the splitting. -/
noncomputable def iterMatrix : Matrix ι ι ℝ := s.N⁻¹ * s.M

/-- One step of the iteration `N x_n = M x_{n-1} + b`, that is
`x_n = N⁻¹ M x_{n-1} + N⁻¹ b`. -/
noncomputable def iterStep (b x : ι → ℝ) : ι → ℝ := s.iterMatrix *ᵥ x + s.N⁻¹ *ᵥ b

/-- The corresponding backbone splitting (`Numlib/LinearSolve/Stationary/Splitting.lean`).  Note
the naming swap: the backbone writes `a = m - n` with `m` invertible, the book `A = N - M` with
`N` nonsingular, so `m = N` and `n = M`. -/
def toSplitting : Stationary.Splitting A := ⟨s.N, s.isUnit⟩

/-- The invertible part of the backbone splitting is the book's `N`. -/
@[simp]
theorem toSplitting_m : s.toSplitting.m = s.N := rfl

/-- The remaining part of the backbone splitting is the book's `M`. -/
theorem toSplitting_n : s.toSplitting.n = s.M := by
  have h : s.toSplitting.n = s.N - A := rfl
  have h2 : s.N - A = s.N - (s.N - s.M) := by rw [← s.eq]
  rw [h, h2, sub_sub_cancel]

/-- The backbone's iteration operator of the splitting is the book's iteration matrix
`N⁻¹ M`. -/
theorem toSplitting_iterationOperator : s.toSplitting.iterationOperator = s.iterMatrix := by
  rw [Stationary.Splitting.iterationOperator_eq, toSplitting_n, toSplitting_m, iterMatrix,
    Matrix.nonsing_inv_eq_ringInverse]

/-- The book's iteration is the backbone's affine step
(`Stationary.step`, `Numlib/LinearSolve/Stationary/Basic.lean`). -/
theorem iterStep_eq_stationary_step (b : ι → ℝ) :
    s.iterStep b = Stationary.step (mulVecCLM s.iterMatrix) (s.N⁻¹ *ᵥ b) := rfl

/-- The solution of `A x = b` is the fixed point of the iteration. -/
theorem step_fixed {x b : ι → ℝ} (hx : A *ᵥ x = b) :
    mulVecCLM s.iterMatrix x + s.N⁻¹ *ᵥ b = x := by
  have hdet : IsUnit s.N.det := (Matrix.isUnit_iff_isUnit_det _).mp s.isUnit
  have hkey : s.N⁻¹ * (s.N - s.M) = 1 - s.iterMatrix := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hdet, iterMatrix]
  have hb : s.N⁻¹ *ᵥ b = x - s.iterMatrix *ᵥ x := by
    have h1 : s.N⁻¹ *ᵥ b = s.N⁻¹ *ᵥ ((s.N - s.M) *ᵥ x) := by rw [← hx, ← s.eq]
    rw [h1, Matrix.mulVec_mulVec, hkey, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp [hb]

/-- **(5.2.5)**: the error equation `x - x_n = (N⁻¹M)ⁿ (x - x₀)`. -/
theorem equation_5_2_5 {x b : ι → ℝ} (hx : A *ᵥ x = b) (x₀ : ι → ℝ) (k : ℕ) :
    x - (s.iterStep b)^[k] x₀ = s.iterMatrix ^ k *ᵥ (x - x₀) := by
  have h := Stationary.step_iterate_sub (mulVecCLM s.iterMatrix) (s.N⁻¹ *ᵥ b) (s.step_fixed hx)
    x₀ k
  rw [mulVecCLM_pow] at h
  rw [← neg_sub ((s.iterStep b)^[k] x₀) x, iterStep_eq_stationary_step, h, Matrix.mulVec_sub,
    Matrix.mulVec_sub]
  abel

/-- §5.2.2(b): the iteration converges from every `x₀` whenever the iteration matrix has operator
norm less than `1`.  This is the backbone's `Stationary.norm_iterate_sub_le`. -/
theorem tendsto_of_opNorm_lt_one (hG : ‖mulVecCLM s.iterMatrix‖ < 1) {x b : ι → ℝ}
    (hx : A *ᵥ x = b) (x₀ : ι → ℝ) :
    Tendsto (fun k => (s.iterStep b)^[k] x₀) atTop (𝓝 x) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
    (fun k => Stationary.norm_iterate_sub_le _ _ hG (s.step_fixed hx) x₀ k) ?_)
  have h1 : Tendsto (fun k : ℕ => ‖mulVecCLM s.iterMatrix‖ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hG
  simpa using (h1.div_const (1 - ‖mulVecCLM s.iterMatrix‖)).mul_const
    ‖Stationary.step (mulVecCLM s.iterMatrix) (s.N⁻¹ *ᵥ b) x₀ - x₀‖

/-- §5.2.2(d): the iteration converges from *every* starting point exactly when the powers of the
iteration matrix tend to `0`. -/
theorem forall_tendsto_iff {x b : ι → ℝ} (hx : A *ᵥ x = b) :
    (∀ x₀, Tendsto (fun k => (s.iterStep b)^[k] x₀) atTop (𝓝 x)) ↔
      Tendsto (fun k => s.iterMatrix ^ k) atTop (𝓝 0) := by
  rw [tendsto_pow_zero_iff_mulVec]
  constructor
  · intro h v
    have hv := (h (x - v)).const_sub x
    rw [sub_self] at hv
    have heq : (fun k => x - (s.iterStep b)^[k] (x - v)) = fun k => s.iterMatrix ^ k *ᵥ v := by
      funext k
      simpa using s.equation_5_2_5 hx (x - v) k
    rwa [heq] at hv
  · intro h x₀
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have heq : (fun k => ‖(s.iterStep b)^[k] x₀ - x‖)
        = fun k => ‖s.iterMatrix ^ k *ᵥ (x - x₀)‖ := by
      funext k
      rw [← norm_neg, neg_sub, s.equation_5_2_5 hx x₀]
    rw [heq]
    simpa using (h (x - x₀)).norm

end BookSplitting

/-- §5.2.2(c): `Gᵏ → 0` if and only if the spectral radius `r_σ(G)`, computed over `ℂ`, is less
than `1`.  This is the backbone's `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`. -/
theorem tendsto_pow_iff_complexSpectralRadius_lt_one (G : Matrix ι ι ℝ) :
    Tendsto (fun k => G ^ k) atTop (𝓝 0) ↔ Matrix.complexSpectralRadius G < 1 :=
  Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one G

/-- §5.2.2(c)+(d): the classical criterion — the iteration `N x_n = M x_{n-1} + b` converges for
every starting point if and only if `r_σ(N⁻¹M) < 1`. -/
theorem BookSplitting.forall_tendsto_iff_complexSpectralRadius_lt_one {A : Matrix ι ι ℝ}
    (s : BookSplitting A) {x b : ι → ℝ} (hx : A *ᵥ x = b) :
    (∀ x₀, Tendsto (fun k => (s.iterStep b)^[k] x₀) atTop (𝓝 x)) ↔
      Matrix.complexSpectralRadius s.iterMatrix < 1 :=
  (s.forall_tendsto_iff hx).trans
    (Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one s.iterMatrix)

/-- §5.2.2, relation 1, in the form the book uses it: an operator norm of the iteration matrix
below `1` forces `r_σ < 1`, hence convergence.  The inequality `r_σ(G) ≤ ‖G‖` for an arbitrary
submultiplicative, absolutely homogeneous, positive definite matrix norm is the backbone's
`Matrix.complexSpectralRadius_le_of_norm`, and its instance for the maximum absolute row sum —
which is `‖mulVecCLM G‖`, by Mathlib's `Matrix.linfty_opNorm_eq_opNorm` — is
`Matrix.complexSpectralRadius_le_linfty_opNNNorm`.  Both are stated under the scoped norm
instance on `Matrix ι ι ℝ` that this file deliberately does not open, so the proof below goes
through `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one` instead. -/
theorem complexSpectralRadius_lt_one_of_opNorm_lt_one {G : Matrix ι ι ℝ}
    (hG : ‖mulVecCLM G‖ < 1) : Matrix.complexSpectralRadius G < 1 := by
  rw [← Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one, tendsto_pow_zero_iff_mulVec]
  intro v
  have hb : ∀ k : ℕ, ‖G ^ k *ᵥ v‖ ≤ ‖mulVecCLM G‖ ^ k * ‖v‖ := fun k =>
    calc ‖G ^ k *ᵥ v‖ = ‖(mulVecCLM G ^ k) v‖ := by rw [mulVecCLM_pow]
      _ ≤ ‖mulVecCLM G ^ k‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖mulVecCLM G‖ ^ k * ‖v‖ :=
          mul_le_mul_of_nonneg_right (norm_mulVecCLM_pow_le G k) (norm_nonneg _)
  have hlim : Tendsto (fun k : ℕ => ‖mulVecCLM G‖ ^ k * ‖v‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hG).mul_const ‖v‖
  exact squeeze_zero_norm hb hlim

section Classical

variable [LinearOrder ι]

/-- The Jacobi splitting `N = D`, `M = -(L + U)`, where `A = D + L + U` splits `A` into its
diagonal, strictly lower and strictly upper parts (§5.2.2). -/
noncomputable def jacobi (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) : BookSplitting A :=
  ⟨A.diagPart, -(A.strictLower + A.strictUpper), by
    rw [sub_neg_eq_add, ← add_assoc, Matrix.diagPart_add_strictLower_add_strictUpper], h⟩

/-- The Gauss–Seidel splitting `N = D + L`, `M = -U` (§5.2.2). -/
noncomputable def gaussSeidel (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) : BookSplitting A :=
  ⟨A.diagPart + A.strictLower, -A.strictUpper, by
    rw [sub_neg_eq_add, Matrix.diagPart_add_strictLower_add_strictUpper],
    (Matrix.gaussSeidelSplitting A h).isUnit⟩

/-- The SOR splitting `N = D/ω + L`, `M = N - A = (1/ω - 1) D - U` (§5.2.2). -/
noncomputable def sor (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) {ω : ℝ} (hω : ω ≠ 0) :
    BookSplitting A :=
  ⟨ω⁻¹ • A.diagPart + A.strictLower, (ω⁻¹ - 1) • A.diagPart - A.strictUpper, by
    have hsub : ω⁻¹ • A.diagPart + A.strictLower - ((ω⁻¹ - 1) • A.diagPart - A.strictUpper)
        = A.diagPart + A.strictLower + A.strictUpper := by
      rw [sub_smul, one_smul]
      abel
    rw [hsub, Matrix.diagPart_add_strictLower_add_strictUpper],
    (Matrix.sorSplitting A h hω).isUnit⟩

/-- The book's Jacobi splitting is the backbone's. -/
@[simp]
theorem jacobi_toSplitting (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) :
    (jacobi A h).toSplitting = Matrix.jacobiSplitting A h := rfl

/-- The book's Gauss–Seidel splitting is the backbone's. -/
@[simp]
theorem gaussSeidel_toSplitting (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) :
    (gaussSeidel A h).toSplitting = Matrix.gaussSeidelSplitting A h := rfl

/-- The book's SOR splitting is the backbone's. -/
@[simp]
theorem sor_toSplitting (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) {ω : ℝ} (hω : ω ≠ 0) :
    (sor A h hω).toSplitting = Matrix.sorSplitting A h hω := rfl

/-- Gauss–Seidel is SOR with `ω = 1` (§5.2.2). -/
theorem sor_one (A : Matrix ι ι ℝ) (h : IsUnit A.diagPart) :
    (sor A h one_ne_zero).N = (gaussSeidel A h).N := by
  change (1 : ℝ)⁻¹ • A.diagPart + A.strictLower = A.diagPart + A.strictLower
  rw [inv_one, one_smul]

end Classical

end Splittings

/-! ### §5.2.3–5.2.4: integral equations of the second kind and the Picard iteration -/

section IntegralEquations

open IntegralOperator

open scoped NNReal Nat

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Theorem 5.1.3 on the whole space: a contractive self-map of a Banach space has a unique fixed
point, reached from every starting point, with the error bounds (5.1.4)–(5.1.6). -/
private theorem theorem_5_1_3_univ {T : V → V} {α : ℝ} (hα : ContractiveOn T univ α) :
    (∃! u, T u = u) ∧
      ∀ u₀ : V, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
        (∀ n, ‖T^[n] u₀ - u‖ ≤ α ^ n / (1 - α) * ‖u₀ - T u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α / (1 - α) * ‖T^[n] u₀ - T^[n + 1] u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ α * ‖T^[n] u₀ - u‖) := by
  obtain ⟨huniq, hconv⟩ :=
    theorem_5_1_3 isClosed_univ ⟨(0 : V), mem_univ 0⟩ (mapsTo_univ T univ) hα
  refine ⟨by simpa using huniq, fun u₀ => ?_⟩
  obtain ⟨u, -, hfix, hlim, h1, h2, h3⟩ := hconv u₀ (mem_univ u₀)
  exact ⟨u, hfix, hlim, h1, h2, h3⟩

/-- Example 5.1.2 on the whole space: it is enough that some power of `T` be contractive. -/
private theorem example_5_1_2_univ {T : V → V} {α : ℝ} (hc : Continuous T) {m : ℕ} (hm : 0 < m)
    (hα : ContractiveOn T^[m] univ α) :
    (∃! u, T u = u) ∧ ∀ u₀ : V, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) := by
  obtain ⟨huniq, hconv⟩ := example_5_1_2 isClosed_univ ⟨(0 : V), mem_univ 0⟩ (mapsTo_univ T univ)
    hc.continuousOn hm hα
  refine ⟨by simpa using huniq, fun u₀ => ?_⟩
  obtain ⟨u, -, hfix, hlim⟩ := hconv u₀ (mem_univ u₀)
  exact ⟨u, hfix, hlim⟩

variable {a b : ℝ}

/-- The kernel that absorbs the inhomogeneity of a Volterra equation of the second kind:
substituting `v = u - f` turns `u = V u + f`, with `V` the Volterra operator of `k`, into
`v = V' v` with `V'` the Volterra operator of `shiftKernel k f`. -/
private def shiftKernel (k : C(Icc a b × Icc a b × ℝ, ℝ)) (f : C(Icc a b, ℝ)) :
    C(Icc a b × Icc a b × ℝ, ℝ) :=
  ⟨fun p => k (p.1, p.2.1, p.2.2 + f p.2.1), by fun_prop⟩

/-- Translating the last argument of a kernel by a fixed function preserves its Lipschitz
constant. -/
private theorem lipschitzWith_shiftKernel {k : C(Icc a b × Icc a b × ℝ, ℝ)} {M : ℝ≥0}
    (hk : ∀ t s : Icc a b, LipschitzWith M fun z => k (t, s, z)) (f : C(Icc a b, ℝ))
    (t s : Icc a b) : LipschitzWith M fun z => shiftKernel k f (t, s, z) :=
  LipschitzWith.of_dist_le_mul fun z w => by
    have h : dist (k (t, s, z + f s)) (k (t, s, w + f s)) ≤ M * dist (z + f s) (w + f s) :=
      (hk t s).dist_le_mul _ _
    rwa [dist_add_right] at h

/-- The defining property of `shiftKernel`: its Volterra operator at `u` is the Volterra
operator of `k` at `u + f`. -/
private theorem volterra_shiftKernel (hab : a ≤ b) (k : C(Icc a b × Icc a b × ℝ, ℝ))
    (f u : C(Icc a b, ℝ)) : volterra hab (shiftKernel k f) u = volterra hab k (u + f) :=
  rfl

/-- The inhomogeneous Volterra map `u ↦ V u + f` is conjugate, by the translation `u ↦ u + f`, to
the Volterra operator of the shifted kernel; so its iterates inherit the factorial estimate. -/
private theorem iterate_volterra_add (hab : a ≤ b) (k : C(Icc a b × Icc a b × ℝ, ℝ))
    (f : C(Icc a b, ℝ)) (n : ℕ) (v : C(Icc a b, ℝ)) :
    (fun u => volterra hab k u + f)^[n] v
      = (volterra hab (shiftKernel k f))^[n] (v - f) + f := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih]
    rw [volterra_shiftKernel]

/-- **§5.2.3, the linear Fredholm equation of the second kind** `λ u(x) - ∫ₐᵇ k(x, y) u(y) dy =
f(x)`, written as the fixed-point problem `u = λ⁻¹ (K u + f)` of (5.2.7).  Its contractivity
constant is `α = |λ|⁻¹ max_x ∫ₐᵇ |k(x, y)| dy` by the norm formula (2.2.8), and (5.2.8) `α < 1` is
exactly what Theorem 5.1.3 asks for. -/
theorem theorem_5_2_2_fredholm (hab : a ≤ b) (k : C(Icc a b × Icc a b, ℝ)) (f : C(Icc a b, ℝ))
    {lam : ℝ} (hlam : |lam|⁻¹ * (⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)|) < 1)
    (T : C(Icc a b, ℝ) → C(Icc a b, ℝ))
    (hT : ∀ (u : C(Icc a b, ℝ)) (x : Icc a b),
      T u x = lam⁻¹ * ((∫ y in a..b, k (x, projIcc a b hab y) * u (projIcc a b hab y)) + f x)) :
    (∃! u, T u = u) ∧
      ∀ u₀, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
        ∀ n, ‖T^[n] u₀ - u‖
          ≤ (|lam|⁻¹ * (⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)|)) ^ n
              / (1 - |lam|⁻¹ * (⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)|)) * ‖u₀ - T u₀‖ := by
  have hTeq : T = fun u => lam⁻¹ • (fredholm hab k u + f) := by
    funext u; ext x; rw [hT u x]; simp [mul_add]
  subst hTeq
  have hnorm : ‖fredholm hab k‖ = ⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)| :=
    norm_fredholm hab k
  have hα : ContractiveOn (fun u => lam⁻¹ • (fredholm hab k u + f)) univ
      (|lam|⁻¹ * (⨆ x, ∫ y in a..b, |k (x, projIcc a b hab y)|)) := by
    refine ⟨by rw [← hnorm]; positivity, hlam, fun u _ v _ => ?_⟩
    have hsub : lam⁻¹ • (fredholm hab k u + f) - lam⁻¹ • (fredholm hab k v + f)
        = lam⁻¹ • fredholm hab k (u - v) := by
      rw [map_sub, ← smul_sub]; congr 1; abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_inv, ← hnorm, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((fredholm hab k).le_opNorm _) (by positivity)
  obtain ⟨huniq, hconv⟩ := theorem_5_1_3_univ hα
  refine ⟨huniq, fun u₀ => ?_⟩
  obtain ⟨u, hfix, hlim, h1, -, -⟩ := hconv u₀
  exact ⟨u, hfix, hlim, h1⟩

/-- **Theorem 5.2.2**: the Urysohn integral equation of the second kind
`u(x) = μ ∫ₐᵇ k(x, y, u(y)) dy + f(x)` (5.2.10).  If the kernel is Lipschitz in its last argument
with constant `M`, uniformly in the other two (5.2.11)–(5.2.12), and `|μ| M (b - a) < 1`, then the
equation has a unique solution `u ∈ C[a, b]`, the iteration (5.2.13) converges to it from every
starting point, and the error bounds (5.1.4)–(5.1.6) hold with `α = |μ| M (b - a)`. -/
theorem theorem_5_2_2 (hab : a ≤ b) {k : C(Icc a b × Icc a b × ℝ, ℝ)} {M : ℝ≥0}
    (hk : ∀ x y : Icc a b, LipschitzWith M fun z => k (x, y, z)) (f : C(Icc a b, ℝ)) {mu : ℝ}
    (hmu : |mu| * ((M : ℝ) * (b - a)) < 1) (T : C(Icc a b, ℝ) → C(Icc a b, ℝ))
    (hT : ∀ (u : C(Icc a b, ℝ)) (x : Icc a b),
      T u x = mu * (∫ y in a..b, k (x, projIcc a b hab y, u (projIcc a b hab y))) + f x) :
    (∃! u, T u = u) ∧
      ∀ u₀, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
        (∀ n, ‖T^[n] u₀ - u‖
          ≤ (|mu| * ((M : ℝ) * (b - a))) ^ n / (1 - |mu| * ((M : ℝ) * (b - a)))
              * ‖u₀ - T u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖
          ≤ |mu| * ((M : ℝ) * (b - a)) / (1 - |mu| * ((M : ℝ) * (b - a)))
              * ‖T^[n] u₀ - T^[n + 1] u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ |mu| * ((M : ℝ) * (b - a)) * ‖T^[n] u₀ - u‖) := by
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab
  have hTeq : T = fun u => mu • urysohn hab k u + f := by
    funext u; ext x; rw [hT u x]; simp
  subst hTeq
  refine theorem_5_1_3_univ ⟨by positivity, hmu, fun u _ v _ => ?_⟩
  have hlip := (lipschitzWith_urysohn hab hk).dist_le_mul u v
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, Real.coe_toNNReal _ hba] at hlip
  have hsub : mu • urysohn hab k u + f - (mu • urysohn hab k v + f)
      = mu • (urysohn hab k u - urysohn hab k v) := by rw [smul_sub]; abel
  rw [hsub, norm_smul, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left hlip (abs_nonneg _)

/-- **Theorem 5.2.3**: the Volterra integral equation of the second kind
`u(t) = ∫ₐᵗ k(t, s, u(s)) ds + f(t)` (5.2.15).  However large the Lipschitz constant of the kernel,
the equation has a unique solution in `C[a, b]` and the iteration (5.2.16) converges to it from
every starting point: no smallness hypothesis is needed, because the factorial estimate of
`IntegralOperator.norm_iterate_volterra_sub_le` makes some power of the operator a contraction,
and Example 5.1.2 applies. -/
theorem theorem_5_2_3 (hab : a ≤ b) {k : C(Icc a b × Icc a b × ℝ, ℝ)} {M : ℝ≥0}
    (hk : ∀ t s : Icc a b, LipschitzWith M fun z => k (t, s, z)) (f : C(Icc a b, ℝ))
    (T : C(Icc a b, ℝ) → C(Icc a b, ℝ))
    (hT : ∀ (u : C(Icc a b, ℝ)) (t : Icc a b),
      T u t = (∫ s in a..(t : ℝ), k (t, projIcc a b hab s, u (projIcc a b hab s))) + f t) :
    (∃! u, T u = u) ∧ ∀ u₀, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) := by
  have hTeq : T = fun u => volterra hab k u + f := by
    funext u; ext t; rw [hT u t]; simp
  subst hTeq
  obtain ⟨m, hm, hcw⟩ :=
    exists_contractingWith_iterate_volterra hab (lipschitzWith_shiftKernel hk f)
  refine example_5_1_2_univ
    ((lipschitzWith_volterra hab hk).continuous.add continuous_const) hm
    ⟨NNReal.coe_nonneg _, by exact_mod_cast hcw.1, fun u _ v _ => ?_⟩
  rw [iterate_volterra_add hab k f m u, iterate_volterra_add hab k f m v,
    add_sub_add_right_eq_sub]
  have h := hcw.2.dist_le_mul (u - f) (v - f)
  rw [dist_eq_norm, dist_eq_norm] at h
  have huv : u - f - (v - f) = u - v := by abel
  rwa [huv] at h

/-- **Theorem 5.2.4** (Picard–Lindelöf), the fixed-point half.  The initial value problem
`u' = g(t, u)`, `u(t₀) = z` is equivalent to the integral equation
`u(t) = z + ∫_{t₀}^t g(s, u(s)) ds` (5.2.19), whose right-hand side is a Volterra operator.  If `g`
is Lipschitz in `u` with constant `L`, then in the **weighted (Bielecki) norm**
`max_t e^{-β (t - t₀)} |v(t)|` with `β > L` that operator is already a contraction, with constant
`L / β`; so the equation has a unique solution, Picard's iteration (5.2.20) converges to it from
every starting function, and the three bounds (5.1.4)–(5.1.6) hold in the weighted norm.  Since
`IntegralOperator.Bielecki.exp_mul_norm_equiv_le_norm` makes the weighted norm equivalent to the
supremum norm, that convergence is uniform convergence on `[t₀, t₁]`.

The book states the theorem in a Banach space, on a two-sided interval around `t₀`, and for a
right-hand side defined and Lipschitz only on `{(t, u) : |t - t₀| ≤ a, ‖u - z‖ ≤ b}`; the local
existence and uniqueness in that generality is Mathlib's `IsPicardLindelof`. -/
theorem theorem_5_2_4 {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {g : C(Icc t₀ t₁ × ℝ, ℝ)} {L : ℝ≥0}
    (hg : ∀ s : Icc t₀ t₁, LipschitzWith L fun w => g (s, w)) (z : ℝ) {β : ℝ} (hβ : (L : ℝ) < β)
    (T : Bielecki t₀ t₁ β → Bielecki t₀ t₁ β)
    (hT : ∀ (u : Bielecki t₀ t₁ β) (t : Icc t₀ t₁),
      Bielecki.equiv (T u) t
        = z + ∫ s in t₀..(t : ℝ), g (projIcc t₀ t₁ ht s, Bielecki.equiv u (projIcc t₀ t₁ ht s))) :
    (∃! u, T u = u) ∧
      ∀ u₀, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) ∧
        (∀ n, ‖T^[n] u₀ - u‖ ≤ ((L : ℝ) / β) ^ n / (1 - (L : ℝ) / β) * ‖u₀ - T u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖
          ≤ (L : ℝ) / β / (1 - (L : ℝ) / β) * ‖T^[n] u₀ - T^[n + 1] u₀‖) ∧
        (∀ n, ‖T^[n + 1] u₀ - u‖ ≤ (L : ℝ) / β * ‖T^[n] u₀ - u‖) := by
  have hβ0 : (0 : ℝ) < β := lt_of_le_of_lt L.coe_nonneg hβ
  have hdiv : (0 : ℝ) ≤ (L : ℝ) / β := by positivity
  -- the Picard operator is the Volterra operator of the kernel `(t, s, w) ↦ g (s, w)`, shifted by
  -- the constant function `z`
  set k : C(Icc t₀ t₁ × Icc t₀ t₁ × ℝ, ℝ) := ⟨fun p => g (p.2.1, p.2.2), by fun_prop⟩ with hk
  set f : C(Icc t₀ t₁, ℝ) := .const _ z with hf
  have hklip : ∀ t s : Icc t₀ t₁, LipschitzWith L fun w => k (t, s, w) := fun _ s => hg s
  have hTeq : T = fun u => Bielecki.equiv.symm (volterra ht k (Bielecki.equiv u) + f) := by
    funext u
    refine Bielecki.equiv.injective (ContinuousMap.ext fun t => ?_)
    rw [hT u t]
    simp [hk, hf, add_comm]
  subst hTeq
  have hstep : ∀ w : Bielecki t₀ t₁ β,
      volterraBielecki ht (shiftKernel k f) β (w - Bielecki.equiv.symm f)
        = Bielecki.equiv.symm (volterra ht k (Bielecki.equiv w)) := by
    intro w
    refine Bielecki.equiv.injective ?_
    rw [equiv_volterraBielecki, LinearEquiv.apply_symm_apply, volterra_shiftKernel]
    congr 1
    rw [map_sub, LinearEquiv.apply_symm_apply]
    abel
  obtain ⟨-, hlip⟩ := contractingWith_volterra_bielecki ht (lipschitzWith_shiftKernel hklip f) hβ
  refine theorem_5_1_3_univ ⟨hdiv, by rwa [div_lt_one hβ0], fun u _ v _ => ?_⟩
  dsimp only
  have h := hlip.dist_le_mul (u - Bielecki.equiv.symm f) (v - Bielecki.equiv.symm f)
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hdiv, hstep u, hstep v] at h
  have huv : u - Bielecki.equiv.symm f - (v - Bielecki.equiv.symm f) = u - v := by abel
  rw [huv, ← map_sub] at h
  have hcancel : volterra ht k (Bielecki.equiv u) + f - (volterra ht k (Bielecki.equiv v) + f)
      = volterra ht k (Bielecki.equiv u) - volterra ht k (Bielecki.equiv v) := by abel
  rw [← map_sub, hcancel]
  exact h

end IntegralEquations

end AtkinsonHan.Chapter05
