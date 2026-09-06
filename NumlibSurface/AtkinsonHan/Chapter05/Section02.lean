import Numlib.Analysis.ODE.PicardLindelof
import Numlib.IntegralEquations.Basic
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.EpsilonNorm
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
* `complexSpectralRadius_le_opNorm` — §5.2.2, relation 1, `r_σ(A) ≤ ‖A‖`, and
  `tendsto_pow_rpow_complexSpectralRadius` — relation 3, Gelfand's formula
  `‖Aᵏ‖^{1/k} → r_σ(A)`; both for the operator norm induced by the maximum norm on `ℝ^d`.
* `exists_opNorm_le_complexSpectralRadius_add` — §5.2.2, relation 2, the **ε-norm theorem**: a
  vector norm whose induced operator norm of `A` lies in `[r_σ(A), r_σ(A) + ε]`, so that `r_σ(A)`
  is the infimum of `‖A‖` over the operator matrix norms.
* `tendsto_pow_iff_complexSpectralRadius_lt_one` — §5.2.2(c), `Gᵏ → 0` iff `r_σ(G) < 1`.
* `BookSplitting.forall_tendsto_iff`,
  `BookSplitting.forall_tendsto_iff_complexSpectralRadius_lt_one` — §5.2.2(d), convergence from
  every `x₀` iff `(N⁻¹M)ᵏ → 0` iff `r_σ(N⁻¹M) < 1`.
* `equation_5_2_7` — §5.2.3, the linear Fredholm equation of the second kind, whose
  contractivity constant is `|λ|⁻¹ ‖K‖` with `‖K‖` the norm formula (2.2.8).
* `theorem_5_2_2` — the nonlinear Urysohn form (5.2.10).
* `theorem_5_2_3` — the Volterra equation, where no smallness of the kernel is needed because
  the factorial estimate on the iterated kernels makes some power of the operator contract and
  Exercise 5.1.2 applies.
* `theorem_5_2_4` — §5.2.4, the Picard iteration for the initial value problem, in the weighted
  (Bielecki) norm in which the Picard operator itself contracts, and `theorem_5_2_4_ode` — the
  differential form of the same theorem, in a Banach space and on the two-sided interval
  `[t₀ - a₀, t₀ + a₀]` with `a₀ = min(a, b/M)`: a unique continuously differentiable solution of
  `u' = f(t, u)`, `u(t₀) = z` with values in `‖u - z‖ ≤ b`.

## Not formalized here

* The remark after Theorem 5.2.3, that its hypotheses on `[a, ∞)` give a unique solution in
  `C[a, ∞)` whose restrictions are the solutions on each `[a, b]`.  The obstruction is the kernel
  type: `IntegralOperator.volterra` and the whole `C[a, b]` toolkit it belongs to are
  interval-indexed by construction, so the remark needs a second, `Ici a`-indexed kernel type in
  the backbone together with the compatibility argument gluing the per-interval solutions, and
  nothing else in the corpus would use it.  The mathematical content — that the solution on
  `[a, b']` restricts to the solution on `[a, b]` — is already the uniqueness clause of
  `theorem_5_2_3` on `[a, b]`.

`theorem_5_2_4` is the book's theorem for the integral equation (the fixed-point form of the initial
value problem) on an interval to the right of `t₀`, for a scalar equation whose right-hand side is
globally Lipschitz in `u`; that is the part whose proof is Bielecki's contraction argument.  The
book's own statement is the differential one, and `theorem_5_2_4_ode` states that, in the book's
generality, on `Numlib/Analysis/ODE/PicardLindelof.lean`: Mathlib's own
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` does not say that the solution it
produces stays inside `‖u - z‖ ≤ b`, which `ODE_solution_unique_of_mem_Icc` needs, and the backbone
file supplies exactly that containment.
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
below `1` forces `r_σ < 1`, hence convergence.  The inequality itself is
`complexSpectralRadius_le_opNorm` below; the proof here goes through
`Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one` instead, which needs no matrix norm at
all. -/
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

open scoped Matrix.Norms.Operator in
/-- **§5.2.2, relation 1**: `r_σ(A) ≤ ‖A‖` for a matrix operator norm — here the one induced by
the maximum norm on `ℝ^d`, which is the maximum absolute row sum and is `‖mulVecCLM A‖` by
Mathlib's `Matrix.linfty_opNorm_eq_opNorm`.  The backbone proves the inequality for an arbitrary
submultiplicative, absolutely homogeneous, positive definite matrix norm
(`Matrix.complexSpectralRadius_le_of_norm`); the instance used here is
`Matrix.complexSpectralRadius_le_linfty_opNNNorm`.

The spectral radius is `ENNReal`-valued, and finite for a matrix over a finite index type
(`Matrix.complexSpectralRadius_ne_top`), so `toReal` loses nothing. -/
theorem complexSpectralRadius_le_opNorm (G : Matrix ι ι ℝ) :
    (Matrix.complexSpectralRadius G).toReal ≤ ‖mulVecCLM G‖ :=
  calc (Matrix.complexSpectralRadius G).toReal
      ≤ ((‖G‖₊ : ENNReal)).toReal :=
        ENNReal.toReal_mono ENNReal.coe_ne_top (Matrix.complexSpectralRadius_le_linfty_opNNNorm G)
    _ = ‖G‖ := by simp
    _ = ‖mulVecCLM G‖ := Matrix.linfty_opNorm_eq_opNorm G

/-- **§5.2.2, relation 2** (the ε-norm theorem): for every `ε > 0` there is a vector norm
`‖·‖_{A,ε}` on `ℝ^d`, equivalent to the maximum norm, whose induced operator norm of `A` satisfies
`r_σ(A) ≤ ‖A‖_{A,ε} ≤ r_σ(A) + ε`; hence `r_σ(A)` is the infimum of `‖A‖` over the operator matrix
norms, relation 1 giving the other inequality for every one of them.

The induced operator norm `‖A‖_p` of a vector norm `p` is the least `c ≥ 0` with `p (A x) ≤ c p x`
for every `x`, so the last two clauses say exactly `‖A‖_p ≤ r_σ(A) + ε` and `r_σ(A) ≤ ‖A‖_p`, with
no need to name the induced norm.  The first two clauses say that `p` is equivalent to the maximum
norm, which is what makes it a norm and its induced operator norm finite.

The book quotes this from Ortega and Rheinboldt, whose proof triangularizes `A` and shrinks the
off-diagonal entries by the scaling `diag(δ, δ², …)`.  The backbone's
`Matrix.exists_seminorm_forall_mulVec_le` takes the shorter route through Gelfand's formula,
`p x = ∑_{j<k} c⁻ʲ ‖Aʲ x‖` for `c = r_σ(A) + ε` and `k` with `‖Aᵏ‖ ≤ cᵏ`; the reverse inequality is
`Matrix.complexSpectralRadius_toReal_le_of_forall_mulVec_le`. -/
theorem exists_opNorm_le_complexSpectralRadius_add (A : Matrix ι ι ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Seminorm ℝ (ι → ℝ), (∀ x, ‖x‖ ≤ p x) ∧ (∃ C, ∀ x, p x ≤ C * ‖x‖) ∧
      (∀ x, p (A *ᵥ x) ≤ ((Matrix.complexSpectralRadius A).toReal + ε) * p x) ∧
      ∀ c : ℝ, 0 ≤ c → (∀ x, p (A *ᵥ x) ≤ c * p x) →
        (Matrix.complexSpectralRadius A).toReal ≤ c := by
  obtain ⟨p, hlow, ⟨C, hup⟩, hA⟩ := Matrix.exists_seminorm_forall_mulVec_le A hε
  exact ⟨p, hlow, ⟨C, hup⟩, hA, fun c hc hcA =>
    Matrix.complexSpectralRadius_toReal_le_of_forall_mulVec_le A p one_pos
      (by simpa using hlow) hup hc hcA⟩

open scoped Matrix.Norms.Operator in
/-- **§5.2.2, relation 3** (Gelfand's formula): `‖Aᵏ‖^{1/k} → r_σ(A)`, so the spectral radius is
the asymptotic rate of the iteration whatever the norm.  Stated for the maximum-absolute-row-sum
operator norm, which is the one relation 1 above is stated in; the backbone's
`Matrix.tendsto_pow_rpow_linfty_opNorm` is the same limit written on `Matrix ι ι ℝ` itself.

The book's "any matrix norm, not necessarily induced by a vector norm" is the same limit, since
two norms on a finite-dimensional space differ by a factor `C` with `C^{1/k} → 1`. -/
theorem tendsto_pow_rpow_complexSpectralRadius (G : Matrix ι ι ℝ) :
    Tendsto (fun k : ℕ => ‖mulVecCLM (G ^ k)‖ ^ (1 / k : ℝ)) atTop
      (𝓝 (Matrix.complexSpectralRadius G).toReal) := by
  refine (Matrix.tendsto_pow_rpow_linfty_opNorm G).congr fun k => ?_
  congr 1
  exact Matrix.linfty_opNorm_eq_opNorm (G ^ k)

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

/-- Exercise 5.1.2 on the whole space: it is enough that some power of `T` be contractive. -/
private theorem exercise_5_1_2_univ {T : V → V} {α : ℝ} (hc : Continuous T) {m : ℕ} (hm : 0 < m)
    (hα : ContractiveOn T^[m] univ α) :
    (∃! u, T u = u) ∧ ∀ u₀ : V, ∃ u, T u = u ∧ Tendsto (fun n => T^[n] u₀) atTop (𝓝 u) := by
  obtain ⟨huniq, hconv⟩ := exercise_5_1_2 isClosed_univ ⟨(0 : V), mem_univ 0⟩ (mapsTo_univ T univ)
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
theorem equation_5_2_7 (hab : a ≤ b) (k : C(Icc a b × Icc a b, ℝ)) (f : C(Icc a b, ℝ))
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
and Exercise 5.1.2 applies. -/
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
  refine exercise_5_1_2_univ
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

/-- **Theorem 5.2.4** (Picard–Lindelöf), the differential form.  Let `f` be continuous on the box
`Q_b = {(t, u) : |t - t₀| ≤ a, ‖u - z‖ ≤ b}` of a Banach space, Lipschitz in `u` there with constant
`L`, let `M` bound `‖f‖` on `Q_b`, and put `a₀ = min(a, b/M)`.  Then the initial value problem
`u' = f(t, u)`, `u(t₀) = z` has exactly one continuously differentiable solution on
`[t₀ - a₀, t₀ + a₀]` taking values in `‖u - z‖ ≤ b`.

Confinement to the ball is not an extra demand but part of the book's statement: `f` is given only
on `Q_b`, so a solution of the book's problem is by definition one that stays there.  It is also
what makes uniqueness meaningful — off the box the differential equation says nothing.
"Continuously differentiable" is the fourth clause: the derivative `t ↦ f(t, u(t))` is continuous.

The four constants of the book are exactly the four of Mathlib's `IsPicardLindelof` — `b` its ball
radius, `M` its bound on the field, `L` its Lipschitz constant, and `a₀` the largest half-length its
field `mul_max_le` permits — so the proof is
`IsPicardLindelof.exists_unique_mem_closedBall_hasDerivWithinAt`.  The other half of the book's
theorem, the convergence of Picard's iteration, is `theorem_5_2_4` above. -/
theorem theorem_5_2_4_ode {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {t₀ a b M a₀ : ℝ} {L : ℝ≥0} {z : E} (ha : 0 < a) (hb : 0 < b) (hM : 0 < M)
    (hcont : ContinuousOn (fun p : ℝ × E => f p.1 p.2)
      (Icc (t₀ - a) (t₀ + a) ×ˢ Metric.closedBall z b))
    (hlip : ∀ t ∈ Icc (t₀ - a) (t₀ + a), LipschitzOnWith L (f t) (Metric.closedBall z b))
    (hbdd : ∀ t ∈ Icc (t₀ - a) (t₀ + a), ∀ u ∈ Metric.closedBall z b, ‖f t u‖ ≤ M)
    (ha₀ : a₀ = min a (b / M)) :
    ∃ u : ℝ → E, u t₀ = z ∧
      (∀ t ∈ Icc (t₀ - a₀) (t₀ + a₀), u t ∈ Metric.closedBall z b) ∧
      (∀ t ∈ Icc (t₀ - a₀) (t₀ + a₀),
        HasDerivWithinAt u (f t (u t)) (Icc (t₀ - a₀) (t₀ + a₀)) t) ∧
      ContinuousOn (fun t => f t (u t)) (Icc (t₀ - a₀) (t₀ + a₀)) ∧
      ∀ v : ℝ → E, v t₀ = z → (∀ t ∈ Icc (t₀ - a₀) (t₀ + a₀), v t ∈ Metric.closedBall z b) →
        (∀ t ∈ Icc (t₀ - a₀) (t₀ + a₀),
          HasDerivWithinAt v (f t (v t)) (Icc (t₀ - a₀) (t₀ + a₀)) t) →
        EqOn u v (Icc (t₀ - a₀) (t₀ + a₀)) := by
  obtain ⟨bn, rfl⟩ : ∃ bn : ℝ≥0, (bn : ℝ) = b := ⟨b.toNNReal, Real.coe_toNNReal b hb.le⟩
  obtain ⟨Mn, rfl⟩ : ∃ Mn : ℝ≥0, (Mn : ℝ) = M := ⟨M.toNNReal, Real.coe_toNNReal M hM.le⟩
  have ha₀pos : 0 < a₀ := ha₀ ▸ lt_min ha (by positivity)
  have hmem₀ : t₀ ∈ Icc (t₀ - a₀) (t₀ + a₀) := ⟨by linarith, by linarith⟩
  have hsub : Icc (t₀ - a₀) (t₀ + a₀) ⊆ Icc (t₀ - a) (t₀ + a) := by
    have h : a₀ ≤ a := ha₀ ▸ min_le_left _ _
    exact Icc_subset_Icc (by linarith) (by linarith)
  have hmulmax : (Mn : ℝ) * max (t₀ + a₀ - t₀) (t₀ - (t₀ - a₀)) ≤ (bn : ℝ) - ((0 : ℝ≥0) : ℝ) := by
    have h1 : a₀ ≤ (bn : ℝ) / Mn := ha₀ ▸ min_le_right _ _
    have h2 : (Mn : ℝ) * a₀ ≤ bn := by
      have h := mul_le_mul_of_nonneg_left h1 hM.le
      rwa [mul_div_cancel₀ _ hM.ne'] at h
    simpa using h2
  have hpl : IsPicardLindelof f (⟨t₀, hmem₀⟩ : Icc (t₀ - a₀) (t₀ + a₀)) z bn 0 Mn L := by
    refine ⟨fun t ht => hlip t (hsub ht), fun u hu => ?_,
      fun t ht u hu => hbdd t (hsub ht) u hu, hmulmax⟩
    exact hcont.comp (f := fun t : ℝ => (t, u)) (by fun_prop) fun t ht => ⟨hsub ht, hu⟩
  obtain ⟨u, hu₀, humem, hu, huniq⟩ :=
    hpl.exists_unique_mem_closedBall_hasDerivWithinAt (Metric.mem_closedBall_self le_rfl)
      ⟨by linarith, by linarith⟩
  refine ⟨u, hu₀, humem, hu, ?_, huniq⟩
  exact hcont.comp (f := fun t : ℝ => (t, u t))
    (continuousOn_id.prodMk fun t ht => (hu t ht).continuousWithinAt)
    fun t ht => ⟨hsub ht, humem t ht⟩

end IntegralEquations

end AtkinsonHan.Chapter05
