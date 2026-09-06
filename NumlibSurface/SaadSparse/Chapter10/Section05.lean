import Mathlib.Analysis.Matrix.Normed
import Numlib.LinearSolve.Preconditioner.ApproximateInverse
import Numlib.LinearSolve.Projection.OneDimensional
import NumlibSurface.SaadSparse.Common

/-!
# Saad §10.5: approximate inverse preconditioners

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §10.5: instead of factoring `A`, minimize the Frobenius objective `F(M) = ‖I - A M‖_F²` over
sparse `M` and use `M` itself as the preconditioner.

The Frobenius norm is Mathlib's, under `open scoped Matrix.Norms.Frobenius`, so `‖·‖` on matrices
means `‖·‖_F` throughout this file. The Frobenius inner product `⟨X, Y⟩ = tr(Yᵀ X)` of (10.48) is
introduced here, together with the linear isometry `frobeniusEquiv` onto
`EuclideanSpace ℝ (Fin n × Fin n)`: Mathlib carries the Frobenius *norm* but no inner product
space structure on `Matrix`, and the isometry is what lets the general Hilbert-space statements of
`Numlib/LinearSolve/Preconditioner/ApproximateInverse` be read as statements about matrices. That
is how Proposition 10.9, the gradient `G = -2 Aᵀ R`, is obtained.

The rest of the section has almost no matrix content, and the backbone reflects that. Proposition
10.10 is Neumann's series in a normed ring; Proposition 10.11 and Corollary 10.12 are a Hölder
bound on `M = A⁻¹ - A⁻¹ R`; and the quadratic convergence of the self-preconditioned
minimal-residual iteration — Proposition 10.13 (10.60) and Proposition 10.14 — is the one-line
observation that a minimizer over the step length beats the choice `α = 1`, whose residual is
`R²`. The first half of Proposition 10.13, one minimal-residual step on a single column, is the
one-dimensional projection step of `Numlib/LinearSolve/Projection/OneDimensional` applied to the
preconditioned matrix `C = A M`, since self-preconditioned MR for `A m = e_j` *is* plain MR for
`C y = e_j`.

The dropping strategies of §10.5.1–10.5.5 and the factored forms of §10.5.7–10.5.8 carry no
statement of their own.
-/

open Matrix Projection
open scoped Matrix.Norms.Frobenius SaadSparse

namespace SaadSparse.Chapter10

variable {n : ℕ}

/-! ### The Frobenius inner product, (10.43)–(10.48) -/

private theorem norm_toLp_eq (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖(WithLp.toLp 2 fun p : Fin n × Fin n => M p.1 p.2 : EuclideanSpace ℝ (Fin n × Fin n))‖
      = ‖M‖ := by
  rw [EuclideanSpace.norm_eq, Matrix.frobenius_norm_def, Fintype.sum_prod_type, Real.sqrt_eq_rpow]
  norm_num

/-- The Frobenius norm on `n × n` matrices is the Euclidean norm on `n²` coordinates: reading a
matrix as the vector of its entries is a linear isometry onto `EuclideanSpace ℝ (Fin n × Fin n)`.
Mathlib has the Frobenius norm but no inner product space structure on `Matrix`, and this is the
identification that supplies one. -/
noncomputable def frobeniusEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n × Fin n) where
  toFun M := WithLp.toLp 2 fun p => M p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := Matrix.of fun i j => WithLp.ofLp x (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' := norm_toLp_eq

@[simp]
theorem frobeniusEquiv_apply (M : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusEquiv n M = WithLp.toLp 2 fun p => M p.1 p.2 := rfl

/-- Saad (10.48): the Frobenius inner product `⟨X, Y⟩_F = tr(Yᵀ X) = ∑ᵢⱼ Xᵢⱼ Yᵢⱼ`, the inner
product whose norm is the Frobenius norm. -/
def frobeniusInner (X Y : Matrix (Fin n) (Fin n) ℝ) : ℝ := Matrix.trace (Yᵀ * X)

theorem frobeniusInner_eq_sum (X Y : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusInner X Y = ∑ i, ∑ j, X i j * Y i j := by
  simp only [frobeniusInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The Frobenius inner product is the Euclidean inner product read through `frobeniusEquiv`. -/
theorem inner_frobeniusEquiv (X Y : Matrix (Fin n) (Fin n) ℝ) :
    inner ℝ (frobeniusEquiv n X) (frobeniusEquiv n Y) = frobeniusInner X Y := by
  rw [frobeniusInner_eq_sum]
  simp only [frobeniusEquiv_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Saad (10.43) and (10.48): the Frobenius inner product of a matrix with itself is the square of
its Frobenius norm, so the objective `F(M) = ‖I - A M‖_F²` is the squared norm of the residual in
this inner product. -/
theorem frobeniusInner_self (X : Matrix (Fin n) (Fin n) ℝ) : frobeniusInner X X = ‖X‖ ^ 2 := by
  rw [← inner_frobeniusEquiv, real_inner_self_eq_norm_sq, (frobeniusEquiv n).norm_map]

theorem norm_sq_eq_sum (X : Matrix (Fin n) (Fin n) ℝ) : ‖X‖ ^ 2 = ∑ i, ∑ j, X i j ^ 2 := by
  rw [← frobeniusInner_self, frobeniusInner_eq_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (sq _).symm

/-- Saad (10.46): the Frobenius objective decouples into `n` independent least-squares problems,
one per column — `F(M) = ∑ⱼ ‖eⱼ - A mⱼ‖₂²` with `mⱼ` the `j`-th column of `M`. This is what makes
the approximate-inverse computation parallel over the columns. -/
theorem equation_10_46 (A M : Matrix (Fin n) (Fin n) ℝ) :
    ‖1 - A * M‖ ^ 2 =
      ∑ j, ‖(WithLp.toLp 2 (Pi.single j (1 : ℝ) - A *ᵥ Mᵀ j) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  rw [norm_sq_eq_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.sub_apply, Matrix.one_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Pi.single_apply, eq_comm]

/-! ### Proposition 10.9: the gradient of the Frobenius objective -/

/-- Moving a left factor across the Frobenius inner product transposes it: this is the identity
that turns the abstract gradient into Saad's array form `-2 Aᵀ R`. -/
private theorem frobeniusInner_mul_left (A X Y : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusInner X (A * Y) = frobeniusInner (Aᵀ * X) Y := by
  change Matrix.trace ((A * Y)ᵀ * X) = Matrix.trace (Yᵀ * (Aᵀ * X))
  rw [Matrix.transpose_mul, Matrix.mul_assoc]

/-- The Frobenius inner product with a fixed matrix, as a continuous linear functional. -/
noncomputable def frobeniusInnerL (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  (innerSL ℝ (frobeniusEquiv n X)).comp (frobeniusEquiv n).toLinearIsometry.toContinuousLinearMap

@[simp]
theorem frobeniusInnerL_apply (X Y : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusInnerL X Y = frobeniusInner X Y :=
  inner_frobeniusEquiv X Y

/-- Saad Proposition 10.9: the array representation of the gradient of `F(M) = ‖I - A M‖_F²` with
respect to `M` is `G = -2 Aᵀ R`, where `R = I - A M` is the residual. In Fréchet form, the
derivative of `F` at `M` is the Frobenius inner product against `-2 Aᵀ R`. -/
theorem proposition_10_9 (A M : Matrix (Fin n) (Fin n) ℝ) :
    HasFDerivAt (fun Z : Matrix (Fin n) (Fin n) ℝ => ‖1 - A * Z‖ ^ 2)
      ((-2 : ℝ) • frobeniusInnerL (Aᵀ * (1 - A * M))) M := by
  have h := Preconditioner.hasFDerivAt_normSq_sub_apply
    (((frobeniusEquiv n).toLinearIsometry.toContinuousLinearMap).comp
      (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ) A)) (frobeniusEquiv n 1) M
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun Z => ?_)).congr_fderiv
    (ContinuousLinearMap.ext fun E => ?_)
  · rw [← (frobeniusEquiv n).norm_map (1 - A * Z), map_sub]
    rfl
  · change (-2 : ℝ) * inner ℝ (frobeniusEquiv n 1 - frobeniusEquiv n (A * M))
        (frobeniusEquiv n (A * E))
      = (-2 : ℝ) * frobeniusInnerL (Aᵀ * (1 - A * M)) E
    rw [frobeniusInnerL_apply, ← map_sub, inner_frobeniusEquiv, frobeniusInner_mul_left]

/-! ### Proposition 10.10: nonsingularity from a small residual -/

/-- Saad Proposition 10.10: if the residual `I - A M` is smaller than `1` in a consistent matrix
norm — here the Frobenius norm — then `A M` is nonsingular, hence so is `M`. This is Neumann's
series. -/
theorem proposition_10_10 {A M : Matrix (Fin n) (Fin n) ℝ} (h : ‖1 - A * M‖ < 1) : IsUnit M := by
  have hAM := Preconditioner.isUnit_of_norm_one_sub_mul_lt_one h
  rw [Matrix.isUnit_iff_isUnit_det] at hAM ⊢
  rw [Matrix.det_mul] at hAM
  exact isUnit_of_mul_isUnit_right hAM

/-- Saad (10.54): the same conclusion under a two-sided scaling. If `D₁ A M D₂` has residual
smaller than `1` for nonsingular `D₁`, `D₂` — in the book, diagonal scalings that improve the
conditioning — then `M` is still nonsingular. -/
theorem equation_10_54 {A M D₁ D₂ : Matrix (Fin n) (Fin n) ℝ} (hD₁ : IsUnit D₁) (hD₂ : IsUnit D₂)
    (h : ‖1 - D₁ * (A * M) * D₂‖ < 1) : IsUnit M := by
  have hAM := Preconditioner.isUnit_of_norm_one_sub_units_mul_lt_one
    (d₁ := hD₁.unit) (d₂ := hD₂.unit) (by rwa [IsUnit.unit_spec, IsUnit.unit_spec])
  rw [Matrix.isUnit_iff_isUnit_det] at hAM ⊢
  rw [Matrix.det_mul] at hAM
  exact isUnit_of_mul_isUnit_right hAM

/-! ### Proposition 10.11 and Corollary 10.12: the sparsity of an approximate inverse -/

/-- Saad Proposition 10.11: if the `j`-th column residual `eⱼ - A mⱼ` is small in the `ℓ¹` norm,
say at most `τⱼ`, and the entry `(A⁻¹)ᵢⱼ` is large relative to the `i`-th row of `A⁻¹` — precisely
`τⱼ · maxₖ |(A⁻¹)ᵢₖ| < |(A⁻¹)ᵢⱼ|` — then `Mᵢⱼ` cannot vanish. An accurate approximate inverse must
carry the large entries of `A⁻¹` in its pattern. -/
theorem proposition_10_11 {A M : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det) {τ : Fin n → ℝ}
    (hτ : ∀ j, ∑ i, |(Pi.single j (1 : ℝ) : Fin n → ℝ) i - (A *ᵥ Mᵀ j) i| ≤ τ j) {i j : Fin n}
    (hlt : τ j * (⨆ k, |A⁻¹ i k|) < |A⁻¹ i j|) : M i j ≠ 0 := by
  refine Preconditioner.apply_ne_zero_of_abs_lt (Matrix.nonsing_inv_mul A hA) ?_ hlt
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) (hτ j)
  congr 1
  simp [Matrix.sub_apply, Matrix.one_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Pi.single_apply, eq_comm]

/-- Saad Corollary 10.12: if every column residual has `ℓ¹` norm at most `τ` and the nonzero
entries of `A⁻¹` are `τ`-equimodular — each is larger than `τ` times the largest entry of `A⁻¹` —
then the pattern of `M` contains the pattern of `A⁻¹`. In particular an approximate inverse of a
matrix whose inverse is dense with comparable entries must itself be dense, which is the practical
limitation of the whole approach. -/
theorem corollary_10_12 {A M : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det) {τ : ℝ}
    (hτ : ∀ j, ∑ i, |(Pi.single j (1 : ℝ) : Fin n → ℝ) i - (A *ᵥ Mᵀ j) i| ≤ τ)
    (hequi : ∀ i j : Fin n, A⁻¹ i j ≠ 0 → τ * (⨆ (l : Fin n) (k : Fin n), |A⁻¹ l k|) < |A⁻¹ i j|)
    {i j : Fin n} (h : A⁻¹ i j ≠ 0) : M i j ≠ 0 := by
  have hτ0 : 0 ≤ τ :=
    le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hτ j)
  have hbdd : BddAbove (Set.range fun k => |A⁻¹ i k|) := Set.Finite.bddAbove (Set.finite_range _)
  have hbdd' : BddAbove (Set.range fun l => ⨆ k, |A⁻¹ l k|) :=
    Set.Finite.bddAbove (Set.finite_range _)
  have hle : (⨆ k, |A⁻¹ i k|) ≤ ⨆ (l : Fin n) (k : Fin n), |A⁻¹ l k| := le_ciSup hbdd' i
  exact proposition_10_11 (τ := fun _ => τ) hA hτ
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle hτ0) (hequi i j h))

/-! ### Propositions 10.13 and 10.14: quadratic convergence of self-preconditioned MR -/

/-- Saad (10.59), the first half of Proposition 10.13: one minimal-residual step of the
self-preconditioned iteration for a single column. Self-preconditioned MR for `A m = b` with
search direction `M r` *is* plain MR for `C y = b` with `C = A M` and `m = M y`, so the exact
one-step identity `‖r′‖ = ‖r‖ sin ∠(r, C r)` of `Numlib/LinearSolve/Projection/OneDimensional`
applies verbatim to the preconditioned matrix. In particular `‖r′‖ ≤ ‖(I - A M) r‖`, which is the
bound the book draws. The second half, (10.60), is `proposition_10_14`, which is stated for the
whole residual matrix and covers both. -/
theorem proposition_10_13 (A M : Matrix (Fin n) (Fin n) ℝ) (b x : EuclideanSpace ℝ (Fin n)) :
    ‖b - ((A * M) ⬝ minResStep (Matrix.toEuclideanLin (A * M)) b x)‖ ^ 2 =
      ‖b - ((A * M) ⬝ x)‖ ^ 2 *
        (1 - ‖inner ℝ ((A * M) ⬝ (b - ((A * M) ⬝ x))) (b - ((A * M) ⬝ x))‖ ^ 2 /
          (‖b - ((A * M) ⬝ x)‖ ^ 2 * ‖(A * M) ⬝ (b - ((A * M) ⬝ x))‖ ^ 2)) :=
  Projection.norm_residual_minResStep_sq_eq x

/-- Saad (10.61): the residual of the global self-preconditioned minimal-residual step
`M ← M + α M R`, `R = I - A M`, is `R' = (1 - α) R + α R²`. Iterating, `R_k` is a polynomial of
degree `2^k` in `R₀`. -/
theorem equation_10_61 (A M : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    1 - A * (M + α • (M * (1 - A * M))) = (1 - α) • (1 - A * M) + α • (1 - A * M) ^ 2 :=
  Preconditioner.residual_selfPreconditionedStep A M α

/-- Saad (10.63): the preconditioned matrix `B = A M` of the self-preconditioned step obeys
`B' = B + α B (I - B)`, so it stays a polynomial in `B₀`. -/
theorem equation_10_63 (A M : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    A * (M + α • (M * (1 - A * M))) = A * M + α • (A * M * (1 - A * M)) :=
  Preconditioner.mul_selfPreconditionedStep A M α

/-- The consequence Saad draws from (10.63): a symmetric `B₀ = A M₀` — as when `M₀ = α₀ Aᵀ` —
keeps every `B_k` symmetric, so the self-preconditioned iteration preserves symmetry of the
preconditioned matrix. -/
theorem isSymm_mul_selfPreconditionedStep {A M : Matrix (Fin n) (Fin n) ℝ} (α : ℝ)
    (hB : (A * M).IsSymm) : (A * (M + α • (M * (1 - A * M)))).IsSymm := by
  have h1 : (A * M * (1 - A * M))ᵀ = A * M * (1 - A * M) := by
    rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, hB, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  rw [equation_10_63]
  change (A * M + α • (A * M * (1 - A * M)))ᵀ = A * M + α • (A * M * (1 - A * M))
  rw [Matrix.transpose_add, Matrix.transpose_smul, hB, h1]

/-- Saad Proposition 10.14, and with it (10.60): the global self-preconditioned minimal-residual
iteration without dropping satisfies `‖R_{k+1}‖_F ≤ ‖R_k²‖_F ≤ ‖R_k‖_F²`, so convergence, when it
occurs, is quadratic. The hypothesis is exactly what a minimal-residual choice of the step length
provides: the new residual is no larger than the one produced by any other step length, and the
step length `α = 1` produces `R²`. -/
theorem proposition_10_14 {A M : Matrix (Fin n) (Fin n) ℝ} {α : ℝ}
    (hmin : ∀ t : ℝ, ‖1 - A * (M + α • (M * (1 - A * M)))‖
      ≤ ‖1 - A * (M + t • (M * (1 - A * M)))‖) :
    ‖1 - A * (M + α • (M * (1 - A * M)))‖ ≤ ‖1 - A * M‖ ^ 2 :=
  Preconditioner.norm_le_norm_sq_of_isMinOn fun t => by
    simpa only [equation_10_61] using hmin t

/-! ### Lemma 10.15: the bordering algorithm -/

/-- Saad Lemma 10.15: in the bordering algorithm for a symmetric positive definite `A`, the scalar
`δ_{k+1}` of (10.70) is positive however inaccurately the auxiliary systems (10.67)–(10.68) are
solved. It is the `(k+1, k+1)` entry of `L A Lᵀ` for the unit lower triangular `L` built by the
algorithm, hence the value of the quadratic form of `A` at the nonzero vector `Lᵀ e_{k+1}`, and
positivity is all that positive definiteness has to say. -/
theorem lemma_10_15 {A L : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hL : IsUnit L)
    (k : Fin n) : 0 < (L * A * Lᵀ) k k := by
  have hinj : Function.Injective L.vecMul := Matrix.vecMul_injective_iff_isUnit.2 hL
  have h := hA.mul_mul_conjTranspose_same hinj
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.diag_pos

end SaadSparse.Chapter10
