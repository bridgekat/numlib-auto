import NumlibSurface.SaadSparse.Chapter13.Section02
import NumlibSurface.SaadSparse.Chapter13.Section03
import NumlibSurface.SaadSparse.Common
import Numlib.LinearSolve.Multigrid.FullMultigrid

/-!
# Saad §13.4: the standard multigrid cycles

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §13.4: the Galerkin coarse problem (13.39), the smoother written through its error propagation
operator (13.40)–(13.42), the two-grid operator (13.43) and Lemma 13.1, the V- and W-cycles, the
cost of one cycle (13.44)–(13.46), and full multigrid with its error bound (Theorem 13.2).

## The pair of grids

The section is stated for a general pair of grids — a fine matrix `A`, a prolongation `P` and a
restriction `R` — with `IsCoarsening A R P` bundling the three standing hypotheses: `A` symmetric
positive definite, `P` injective, and `R` a *positive multiple* of `Pᵀ`, which is Saad's (13.37)
`I_h^H = 2^{-d} (I_H^h)ᵀ`.  The one-dimensional model problem of §13.2 with the inter-grid operators
of §13.3 satisfies them (`isCoarsening_model`), and `example_13_2` is the only concrete coarse
matrix the chapter computes.

Everything the chapter proves about the coarse-grid correction is read off
`Numlib/LinearSolve/Multigrid/Basic.lean` through two bridges: `toEuclideanLin_coarseProjector`,
which identifies Saad's `Q_h = I_H^h A_H⁻¹ I_h^H A_h` with the backbone's `A`-orthogonal projector
onto `Ran(I_H^h)`, and `equation_13_43_eq`, which identifies the two-grid operator (13.43) with
`Multigrid.twoGridOperator`.  Lemma 13.1 is then `Submodule.starProjection`'s own idempotence,
self-adjointness and range, read in the energy inner product.  The factor `2^{-d}` cancels because
it multiplies both sides of the coarse equation — that is `coarseProjection_apply_eq_of_smul`
of §13.3.

## The cycles

The cycles are definitions and nothing more, as they are in the book.  A `Hierarchy` carries one
grid per level, level `0` being the coarsest; `Hierarchy.cycle` is Algorithm 13.4, its cases
`γ = 1` and `γ = 2` are the V-cycle (Algorithm 13.3) and the W-cycle, and
`Hierarchy.fullMultigrid` is Algorithm 13.5.  The book proves nothing about the cycles directly:
the error operator of a `γ`-cycle is a perturbation of the two-grid one, whose analysis is §13.5.
So the two theorems of the section are `equation_13_44`, the cost recurrence, and `theorem_13_2`,
the full multigrid error bound, which is `Multigrid.norm_sub_fullMultigrid_le` under the book's
(13.49)–(13.52).

Not formalized: Algorithm 13.1 (nested iteration), which the book presents only to introduce the
notation and which full multigrid supersedes; the displayed identity
`M_h = M_H^h + S^{ν₂} I_H^h M_H A_H⁻¹ I_h^H A_h` at the end of §13.4.3, which would need the error
operator of the whole recursive cycle as an object of its own and is used nowhere; and Example 13.4,
a table of measured convergence factors.
-/

open Matrix Stationary

open scoped SaadSparse

namespace SaadSparse.Chapter13

variable {n m : ℕ}

/-! ### §13.4.1 The Galerkin coarse problem -/

/-- **Saad (13.39)**, the Galerkin coarse matrix `A_H = I_h^H A_h I_H^h`. -/
def coarseOperator (R : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  R * A * P

/-- **Saad (13.39)**, the coarse right-hand side `f^H = I_h^H f^h`. -/
noncomputable def coarseRhs (R : Matrix (Fin m) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  R ⬝ f

/-- The adjoint of a real matrix is its transpose. -/
theorem adjoint_toEuclideanLin (P : Matrix (Fin n) (Fin m) ℝ) :
    LinearMap.adjoint (toEuclideanLin P) = toEuclideanLin Pᵀ := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1

/-- The Galerkin coarse matrix built from the *transpose* of the prolongation is the backbone's
`Multigrid.galerkinCoarse`. -/
theorem coarseOperator_transpose_eq_galerkinCoarse (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    toEuclideanLin (coarseOperator Pᵀ A P)
      = Multigrid.galerkinCoarse (toEuclideanLin A) (toEuclideanLin P) := by
  have hdef : Multigrid.galerkinCoarse (toEuclideanLin A) (toEuclideanLin P)
      = LinearMap.adjoint (toEuclideanLin P) ∘ₗ toEuclideanLin A ∘ₗ toEuclideanLin P := rfl
  rw [hdef, adjoint_toEuclideanLin, coarseOperator, Matrix.toLpLin_mul_same,
    Matrix.toLpLin_mul_same, LinearMap.comp_assoc]

/-- Rescaling the restriction rescales the coarse matrix. -/
theorem coarseOperator_smul (c : ℝ) (R : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    coarseOperator (c • R) A P = c • coarseOperator R A P := by
  rw [coarseOperator, coarseOperator, Matrix.smul_mul, Matrix.smul_mul]

/-- Saad's restriction is `2^{-d}` times the transpose of the prolongation (13.37), so the coarse
matrix (13.39) is that factor times the backbone's Galerkin coarse operator. -/
theorem coarseOperator_eq_galerkinCoarse (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    toEuclideanLin (coarseOperator (c • Pᵀ) A P)
      = c • Multigrid.galerkinCoarse (toEuclideanLin A) (toEuclideanLin P) := by
  rw [coarseOperator_smul, map_smul, coarseOperator_transpose_eq_galerkinCoarse]

/-- **The coarse problem is well posed**: for a symmetric positive definite fine matrix and an
injective prolongation, the Galerkin coarse matrix (13.39) is symmetric positive definite, so the
coarse solve of Algorithm 13.2 makes sense. -/
theorem posDef_coarseOperator {A : Matrix (Fin n) (Fin n) ℝ} {P : Matrix (Fin n) (Fin m) ℝ}
    (hA : A.PosDef) (hP : Function.Injective (toEuclideanLin P)) {c : ℝ} (hc : 0 < c) :
    (coarseOperator (c • Pᵀ) A P).PosDef := by
  have h1 : (coarseOperator Pᵀ A P).PosDef := by
    rw [Matrix.posDef_iff_isSymmetricCoercive, coarseOperator_transpose_eq_galerkinCoarse]
    exact Multigrid.galerkinCoarse_isSymmetricCoercive
      ((Matrix.posDef_iff_isSymmetricCoercive A).1 hA) hP
  rw [coarseOperator_smul]
  exact Matrix.PosDef.smul h1 hc

/-! ### Example 13.2 -/

/-- Contracting a sum against a column of the interpolation matrix: column `q` carries the stencil
`½ [1 2 1]` on the fine rows `2 q`, `2 q + 1`, `2 q + 2`. -/
private theorem sum_mul_prolongation1D (m : ℕ) (g : Fin (2 * m + 1) → ℝ) (q : Fin m)
    {a b c : Fin (2 * m + 1)} (ha : (a : ℕ) = 2 * (q : ℕ)) (hb : (b : ℕ) = 2 * (q : ℕ) + 1)
    (hc : (c : ℕ) = 2 * (q : ℕ) + 2) :
    ∑ i, g i * prolongation1D m i q = (g a + 2 * g b + g c) / 2 := by
  have hstep : ∀ i : Fin (2 * m + 1), g i * prolongation1D m i q
      = 2 * (restriction1D m q i * g i) := fun i => by
    rw [prolongation1D_eq_smul_transpose, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.mul_sum, ← Matrix.mulVec_apply_eq_sum,
    restriction1D_mulVec m g q ha hb hc]
  ring

/-- One column of `A_h I_{2h}^h` for the one-dimensional model problem: applying
`tridiag(-1, 2, -1)` to the hat function centred at the fine point `2 q + 1` leaves `1` there and
`-½` at the two fine points `2 q - 1` and `2 q + 3`, the ends of its support. -/
private theorem laplacian1D_mul_prolongation1D_apply (m : ℕ) (i : Fin (2 * m + 1)) (q : Fin m) :
    (laplacian1D (2 * m + 1) * prolongation1D m) i q
      = if (i : ℕ) = 2 * (q : ℕ) + 1 then 1
        else if (i : ℕ) + 1 = 2 * (q : ℕ) then -(1 / 2)
        else if (i : ℕ) = 2 * (q : ℕ) + 3 then -(1 / 2) else 0 := by
  obtain ⟨a, ha⟩ : ∃ a : Fin (2 * m + 1), (a : ℕ) = 2 * (q : ℕ) := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin (2 * m + 1), (b : ℕ) = 2 * (q : ℕ) + 1 := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin (2 * m + 1), (c : ℕ) = 2 * (q : ℕ) + 2 := ⟨⟨_, by omega⟩, rfl⟩
  rw [Matrix.mul_apply,
    sum_mul_prolongation1D m (fun k => laplacian1D (2 * m + 1) i k) q ha hb hc]
  simp only [laplacian1D_apply, ha, hb, hc]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- **Example 13.2**: in one dimension with linear interpolation and full weighting the Galerkin
coarse matrix (13.39) of the model problem *is* the coarse discretization,
`I_h^{2h} tridiag(-1, 2, -1)_{2m+1} I_{2h}^h = ¼ tridiag(-1, 2, -1)_m`.

The factor `¼` is the ratio `h² / (2h)²` of the two mesh sizes: the matrices of §13.2 are the
unscaled ones, and on the scaled matrices `h^{-2} tridiag(-1, 2, -1)` of §2.2.3 the identity reads
`A_{2h} = I_h^{2h} A_h I_{2h}^h` with no factor at all — which is the sense in which the Galerkin
coarse operator *is* the coarse discretization.  (The book's column-by-column computation ends at
`A_H e_j^H = -e_{j-1}^H + 2 e_j^H - e_{j+1}^H`, dropping that factor: applying full weighting
`¼[1 2 1]` to its own previous line `-½ e^h_{2j-2} + e^h_{2j} - ½ e^h_{2j+2}` gives
`-¼ e^H_{j-1} + ½ e^H_j - ¼ e^H_{j+1}`.)  Saad's Exercise 6 notes that the corresponding statement
is false in two dimensions with full weighting, which is why the Galerkin definition, and not the
coarse discretization, is what §13.4 takes as primary. -/
theorem example_13_2 (m : ℕ) :
    coarseOperator (restriction1D m) (laplacian1D (2 * m + 1)) (prolongation1D m)
      = (1 / 4 : ℝ) • laplacian1D m := by
  ext q q'
  obtain ⟨a, ha⟩ : ∃ a : Fin (2 * m + 1), (a : ℕ) = 2 * (q : ℕ) := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin (2 * m + 1), (b : ℕ) = 2 * (q : ℕ) + 1 := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin (2 * m + 1), (c : ℕ) = 2 * (q : ℕ) + 2 := ⟨⟨_, by omega⟩, rfl⟩
  have hmul : coarseOperator (restriction1D m) (laplacian1D (2 * m + 1)) (prolongation1D m) q q'
      = ∑ i, restriction1D m q i * (laplacian1D (2 * m + 1) * prolongation1D m) i q' := by
    rw [coarseOperator, congrFun₂ (Matrix.mul_assoc (restriction1D m) (laplacian1D (2 * m + 1))
      (prolongation1D m)) q q', Matrix.mul_apply]
  rw [hmul, ← Matrix.mulVec_apply_eq_sum,
    restriction1D_mulVec m (fun i => (laplacian1D (2 * m + 1) * prolongation1D m) i q') q ha hb hc]
  simp only [laplacian1D_mul_prolongation1D_apply, Matrix.smul_apply, laplacian1D_apply,
    smul_eq_mul, ha, hb, hc]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-! ### §13.4.1 Smoothers -/

/-- The action of a product of matrices on a vector. -/
private theorem mul_act {p q r : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (N : Matrix (Fin q) (Fin r) ℝ)
    (x : EuclideanSpace ℝ (Fin r)) : ((M * N) ⬝ x) = M ⬝ (N ⬝ x) := by
  rw [Matrix.toLpLin_mul_same]
  rfl

/-- The action of a difference of matrices on a vector. -/
private theorem sub_act {p q : ℕ} (M N : Matrix (Fin p) (Fin q) ℝ)
    (x : EuclideanSpace ℝ (Fin q)) : ((M - N) ⬝ x) = (M ⬝ x) - (N ⬝ x) := by
  rw [map_sub]
  rfl

/-- The identity matrix acts as the identity. -/
private theorem one_act (x : EuclideanSpace ℝ (Fin n)) : ((1 : Matrix (Fin n) (Fin n) ℝ) ⬝ x) = x :=
  congrFun (congrArg _ (Matrix.toLpLin_one 2)) x

/-- **Saad (13.40)–(13.41)**: the error propagation operator `S = I - B A` of a smoother with
approximate inverse `B`.  A smoother enters the chapter only through this operator, because every
statement of the theory is about the error. -/
def smoother (A B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := 1 - B * A

/-- The error propagation operator, unfolded. -/
theorem smoother_def (A B : Matrix (Fin n) (Fin n) ℝ) : smoother A B = 1 - B * A := rfl

/-- **Saad (13.41)**: one smoothing step `u ← S u + g` with `g = B f`, the affine iteration whose
error propagation operator is `S = I - B A`. -/
noncomputable def smootherStep (A B : Matrix (Fin n) (Fin n) ℝ)
    (f u : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (smoother A B ⬝ u) + (B ⬝ f)

/-- One smoothing step, unfolded. -/
theorem smootherStep_apply (A B : Matrix (Fin n) (Fin n) ℝ)
    (f u : EuclideanSpace ℝ (Fin n)) :
    smootherStep A B f u = (smoother A B ⬝ u) + (B ⬝ f) := rfl

/-- **Saad (13.41)**, the smoothing step in preconditioning form: `u ← u + B (f - A u)`. -/
theorem equation_13_41 (A B : Matrix (Fin n) (Fin n) ℝ)
    (f u : EuclideanSpace ℝ (Fin n)) :
    smootherStep A B f u = u + (B ⬝ (f - (A ⬝ u))) := by
  simp only [smootherStep_apply, smoother_def, sub_act, one_act, mul_act]
  simp only [map_sub]
  abel

/-- Saad's smoother is the backbone's error propagation operator. -/
theorem smoother_eq_smootherOperator (A B : Matrix (Fin n) (Fin n) ℝ) :
    toEuclideanLin (smoother A B)
      = Multigrid.smootherOperator (toEuclideanLin A) (toEuclideanLin B) := by
  have hdef : Multigrid.smootherOperator (toEuclideanLin A) (toEuclideanLin B)
      = 1 - toEuclideanLin B ∘ₗ toEuclideanLin A := rfl
  rw [smoother_def, hdef, map_sub, Matrix.toLpLin_mul_same, Matrix.toLpLin_one]
  rfl

/-- **Saad (13.42)**: the approximate inverse is recovered from the error propagation operator,
`B = (I - S) A⁻¹`. -/
theorem equation_13_42 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (B : Matrix (Fin n) (Fin n) ℝ) : (1 - smoother A B) * A⁻¹ = B := by
  rw [smoother_def, sub_sub_cancel, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA), Matrix.mul_one]

/-- The solution of `A u = f` is a fixed point of the smoothing step: the smoother is
consistent. -/
theorem smootherStep_of_eq {A B : Matrix (Fin n) (Fin n) ℝ} {f x : EuclideanSpace ℝ (Fin n)}
    (hx : (A ⬝ x) = f) : smootherStep A B f x = x := by
  simp only [smootherStep_apply, smoother_def, sub_act, one_act, mul_act, hx]
  abel

/-- One smoothing step propagates the error by `S`. -/
theorem smootherStep_sub {A B : Matrix (Fin n) (Fin n) ℝ} {f x : EuclideanSpace ℝ (Fin n)}
    (hx : (A ⬝ x) = f) (u : EuclideanSpace ℝ (Fin n)) :
    smootherStep A B f u - x = smoother A B ⬝ (u - x) := by
  have hfix : (smoother A B ⬝ x) + (B ⬝ f) = x := smootherStep_of_eq hx
  conv_lhs => rw [smootherStep_apply, ← hfix]
  rw [map_sub]
  abel

/-- **Saad (13.42)**: the error after `ν` smoothing steps is `d_ν = S^ν d_0`. -/
theorem smootherStep_iterate_sub {A B : Matrix (Fin n) (Fin n) ℝ}
    {f x : EuclideanSpace ℝ (Fin n)} (hx : (A ⬝ x) = f) (u₀ : EuclideanSpace ℝ (Fin n)) (ν : ℕ) :
    (smootherStep A B f)^[ν] u₀ - x = (smoother A B ^ ν) ⬝ (u₀ - x) := by
  induction ν with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_act]
  | succ ν ih =>
    rw [Function.iterate_succ_apply', smootherStep_sub hx, ih, ← mul_act, ← pow_succ']

/-- **Saad (13.42)**: the residual after `ν` smoothing steps is `r_ν = (I - A B)^ν r_0`. -/
theorem smootherStep_iterate_residual (A B : Matrix (Fin n) (Fin n) ℝ)
    (f u₀ : EuclideanSpace ℝ (Fin n)) (ν : ℕ) :
    f - (A ⬝ ((smootherStep A B f)^[ν] u₀)) = ((1 - A * B) ^ ν) ⬝ (f - (A ⬝ u₀)) := by
  have hstep : ∀ u : EuclideanSpace ℝ (Fin n), f - (A ⬝ (smootherStep A B f u))
      = (1 - A * B) ⬝ (f - (A ⬝ u)) := fun u => by
    simp only [smootherStep_apply, smoother_def, sub_act, one_act, mul_act]
    simp only [map_add, map_sub]
    abel
  induction ν with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_act]
  | succ ν ih =>
    rw [Function.iterate_succ_apply', hstep, ih, ← mul_act, ← pow_succ']

/-- **Example 13.3**: the Jacobi smoother is `B = D⁻¹`, and its error propagation operator is the
Jacobi iteration matrix of `Numlib/LinearSolve/Stationary/Splitting.lean`. -/
theorem example_13_3_jacobi (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (diagPart A)) :
    smoother A (diagPart A)⁻¹ = (A.jacobiSplitting h).iterationOperator := by
  change 1 - (diagPart A)⁻¹ * A = 1 - Ring.inverse (diagPart A) * A
  rw [Matrix.nonsing_inv_eq_ringInverse]

/-- **Example 13.3**: the Gauss–Seidel smoother is `B = (D - E)⁻¹`, in Saad's letters
`A = D - E - F`, and its error propagation operator is the Gauss–Seidel iteration matrix. -/
theorem example_13_3_gaussSeidel (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (diagPart A)) :
    smoother A (diagPart A + strictLower A)⁻¹ = (A.gaussSeidelSplitting h).iterationOperator := by
  change 1 - (diagPart A + strictLower A)⁻¹ * A
    = 1 - Ring.inverse (diagPart A + strictLower A) * A
  rw [Matrix.nonsing_inv_eq_ringInverse]

/-- **Example 13.3**: Richardson's smoother is `B = ω I`, and its error propagation operator is
`I - ω A`. -/
theorem example_13_3_richardson (A : Matrix (Fin n) (Fin n) ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    smoother A (ω • 1) = (Stationary.Splitting.richardson A hω).iterationOperator := by
  rw [Stationary.Splitting.richardson_iterationOperator, smoother_def, Matrix.smul_mul,
    Matrix.one_mul]

/-! ### §13.4.2 The two-grid cycle, (13.43) and Lemma 13.1 -/

/-- The standing hypotheses of §13.4 on one pair of grids: the fine matrix is symmetric positive
definite, the prolongation has full column rank, and Saad's restriction is the transpose of the
prolongation scaled by the positive factor `2^{-d}` of (13.37).

Under them the Galerkin coarse matrix (13.39) is nonsingular, so the coarse solve of Algorithm 13.2
makes sense, and the coarse-grid correction (13.43) is the `A`-orthogonal projector of Lemma 13.1.
The one-dimensional model problem of §13.2–13.3 satisfies them (`isCoarsening_model`). -/
structure IsCoarsening (A : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) : Prop where
  /-- The fine matrix is symmetric positive definite. -/
  posDef : A.PosDef
  /-- The prolongation is injective: the coarse space has the dimension of the coarse grid. -/
  injective : Function.Injective (toEuclideanLin P)
  /-- Saad (13.37): the restriction is a positive multiple of the transpose of the prolongation. -/
  exists_smul : ∃ c : ℝ, 0 < c ∧ R = c • Pᵀ

/-- The one-dimensional model problem of §13.2 with the inter-grid operators of §13.3 satisfies
the hypotheses of §13.4: `tridiag(-1, 2, -1)` is positive definite, linear interpolation is
injective, and full weighting is `½ (I_{2h}^h)ᵀ` by (13.35). -/
theorem isCoarsening_model (m : ℕ) :
    IsCoarsening (laplacian1D (2 * m + 1)) (restriction1D m) (prolongation1D m) :=
  ⟨laplacian1D_posDef _, injective_prolongation1D m, 1 / 2, by norm_num, equation_13_35 m⟩

namespace IsCoarsening

variable {A : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin m) (Fin n) ℝ}
  {P : Matrix (Fin n) (Fin m) ℝ}

/-- A symmetric positive definite matrix is a symmetric coercive operator, which is the hypothesis
under which the energy inner product `(x, y)_A` and the backbone's coarse-grid projector exist. -/
theorem isSymmetricCoercive (h : IsCoarsening A R P) : (toEuclideanLin A).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive A).1 h.posDef

/-- The Galerkin coarse matrix (13.39) of a coarsening is symmetric positive definite. -/
theorem posDef_coarseOperator (h : IsCoarsening A R P) : (coarseOperator R A P).PosDef := by
  obtain ⟨c, hc, rfl⟩ := h.exists_smul
  exact _root_.SaadSparse.Chapter13.posDef_coarseOperator h.posDef h.injective hc

/-- The Galerkin coarse matrix (13.39) of a coarsening is nonsingular, so `A_H⁻¹` of (13.43) is a
genuine inverse. -/
theorem isUnit_coarseOperator (h : IsCoarsening A R P) : IsUnit (coarseOperator R A P) :=
  h.posDef_coarseOperator.isUnit

/-- The coarse matrix cancels against its inverse, which is what makes the coarse solve of
(13.43) exact. -/
theorem coarseOperator_mul_inv (h : IsCoarsening A R P) :
    coarseOperator R A P * (coarseOperator R A P)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit_coarseOperator)

end IsCoarsening

/-- **Saad (13.43)**: the coarse-grid preconditioner `B_h = I_H^h A_H⁻¹ I_h^H`, which restricts a
fine residual, solves the coarse problem and interpolates the correction back. -/
noncomputable def coarsePreconditioner (R : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  P * (coarseOperator R A P)⁻¹ * R

/-- **Saad (13.43)**: the coarse-grid projector `Q_h = I_H^h A_H⁻¹ I_h^H A_h = B_h A_h`. -/
noncomputable def coarseProjector (R : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  coarsePreconditioner R A P * A

/-- **Saad (13.43)**: the coarse-grid correction operator `T_h^H = I - I_H^h A_H⁻¹ I_h^H A_h`, the
error propagation operator of one coarse-grid correction. -/
noncomputable def coarseCorrection (R : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - coarseProjector R A P

/-- The coarse-grid correction is the complement of the coarse-grid projector. -/
theorem coarseCorrection_def (R : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    coarseCorrection R A P = 1 - coarseProjector R A P := rfl

/-- **Saad (13.43)** and Algorithm 13.2: the two-grid iteration operator
`M_H^h = S^{ν₂} (I - I_H^h A_H⁻¹ I_h^H A_h) S^{ν₁}`, with `ν₁` pre-smoothing and `ν₂`
post-smoothing steps around one coarse-grid correction. -/
noncomputable def equation_13_43 (R : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (ν₁ ν₂ : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  S ^ ν₂ * coarseCorrection R A P * S ^ ν₁

variable {A : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin m) (Fin n) ℝ}
  {P : Matrix (Fin n) (Fin m) ℝ}

/-- **Saad's coarse-grid projector is the backbone's**: `Q_h = I_H^h A_H⁻¹ I_h^H A_h` is the
`A`-orthogonal projector onto the range of the prolongation.  The factor `2^{-d}` of Saad's
restriction multiplies both sides of the coarse equation and so cancels. -/
theorem toEuclideanLin_coarseProjector (h : IsCoarsening A R P) :
    toEuclideanLin (coarseProjector R A P)
      = Multigrid.coarseProjection (toEuclideanLin A) h.isSymmetricCoercive
          (toEuclideanLin P) := by
  have hunit := h.coarseOperator_mul_inv
  obtain ⟨c, hc, rfl⟩ := h.exists_smul
  refine LinearMap.ext fun x => ?_
  have hgal : ∀ z : EuclideanSpace ℝ (Fin m),
      c • Multigrid.galerkinCoarse (toEuclideanLin A) (toEuclideanLin P) z
        = (coarseOperator (c • Pᵀ) A P) ⬝ z := fun z => by
    rw [coarseOperator_eq_galerkinCoarse]
    rfl
  have hadj : ∀ w : EuclideanSpace ℝ (Fin n),
      c • LinearMap.adjoint (toEuclideanLin P) w = (c • Pᵀ) ⬝ w := fun w => by
    rw [adjoint_toEuclideanLin, map_smul]
    rfl
  have hy : c • Multigrid.galerkinCoarse (toEuclideanLin A) (toEuclideanLin P)
        ((coarseOperator (c • Pᵀ) A P)⁻¹ ⬝ ((c • Pᵀ) ⬝ (A ⬝ x)))
      = c • LinearMap.adjoint (toEuclideanLin P) (toEuclideanLin A x) := by
    rw [hgal, hadj, ← mul_act, hunit, one_act]
  rw [coarseProjection_apply_eq_of_smul (toEuclideanLin A) h.isSymmetricCoercive
    (toEuclideanLin P) (ne_of_gt hc) hy, coarseProjector, coarsePreconditioner]
  simp only [mul_act]

/-- **Saad (13.43)**: the coarse-grid correction operator is the backbone's. -/
theorem toEuclideanLin_coarseCorrection (h : IsCoarsening A R P) :
    toEuclideanLin (coarseCorrection R A P)
      = Multigrid.coarseCorrection (toEuclideanLin A) h.isSymmetricCoercive
          (toEuclideanLin P) := by
  have hdef : Multigrid.coarseCorrection (toEuclideanLin A) h.isSymmetricCoercive
      (toEuclideanLin P)
      = 1 - Multigrid.coarseProjection (toEuclideanLin A) h.isSymmetricCoercive
          (toEuclideanLin P) := rfl
  rw [coarseCorrection_def, hdef, map_sub, toEuclideanLin_coarseProjector h,
    Matrix.toEuclideanLin_one]
  rfl

/-- **Saad (13.43)**: the two-grid iteration operator is the backbone's
`Multigrid.twoGridOperator`, so the convergence theory of §13.5 applies to it. -/
theorem equation_13_43_eq (h : IsCoarsening A R P) (S : Matrix (Fin n) (Fin n) ℝ) (ν₁ ν₂ : ℕ) :
    toEuclideanLin (equation_13_43 R A P S ν₁ ν₂)
      = Multigrid.twoGridOperator (toEuclideanLin A) h.isSymmetricCoercive (toEuclideanLin P)
          (toEuclideanLin S) ν₁ ν₂ := by
  have hdef : Multigrid.twoGridOperator (toEuclideanLin A) h.isSymmetricCoercive
      (toEuclideanLin P) (toEuclideanLin S) ν₁ ν₂
      = (toEuclideanLin S ^ ν₂) ∘ₗ Multigrid.coarseCorrection (toEuclideanLin A)
          h.isSymmetricCoercive (toEuclideanLin P) ∘ₗ (toEuclideanLin S ^ ν₁) := rfl
  rw [equation_13_43, hdef, Matrix.toEuclideanLin_mul, Matrix.toEuclideanLin_mul,
    toEuclideanLin_coarseCorrection h, Matrix.toEuclideanLin_pow, Matrix.toEuclideanLin_pow,
    LinearMap.comp_assoc]

/-- **Lemma 13.1**: with the coarse matrix defined by (13.39), the coarse-grid correction operator
(13.43) is a projector, `(T_h^H)² = T_h^H`. -/
theorem lemma_13_1 (h : IsCoarsening A R P) :
    coarseCorrection R A P * coarseCorrection R A P = coarseCorrection R A P := by
  have hQ : coarseProjector R A P * coarseProjector R A P = coarseProjector R A P := by
    refine (Matrix.toEuclideanLin (𝕜 := ℝ)).injective ?_
    rw [Matrix.toEuclideanLin_mul, toEuclideanLin_coarseProjector h]
    refine LinearMap.ext fun x => ?_
    exact Multigrid.coarseProjection_apply_of_mem _ _ _
      (Multigrid.coarseProjection_apply_mem _ h.isSymmetricCoercive _ x)
  have hexpand : ∀ Q : Matrix (Fin n) (Fin n) ℝ,
      (1 - Q) * (1 - Q) = 1 - Q - (Q - Q * Q) := fun Q => by noncomm_ring
  rw [coarseCorrection_def, hexpand, hQ, sub_self, sub_zero]

/-- **Lemma 13.1**: the coarse-grid correction is *orthogonal with respect to the `A_h`-inner
product*, `(A T x, y) = (A x, T y)`.  Together with `lemma_13_1` this says that `T_h^H` is the
`A_h`-orthogonal projector onto the complement of the coarse space. -/
theorem lemma_13_1_energyInner (h : IsCoarsening A R P) (x y : EuclideanSpace ℝ (Fin n)) :
    energyInner (toEuclideanLin A) (coarseCorrection R A P ⬝ x) y
      = energyInner (toEuclideanLin A) x (coarseCorrection R A P ⬝ y) := by
  have hval : ∀ z : EuclideanSpace ℝ (Fin n),
      WithEnergy.equiv (toEuclideanLin A) h.isSymmetricCoercive (coarseCorrection R A P ⬝ z)
        = (WithEnergy.submoduleMap (toEuclideanLin A) h.isSymmetricCoercive
            (LinearMap.range (toEuclideanLin P)))ᗮ.starProjection
              (WithEnergy.equiv (toEuclideanLin A) h.isSymmetricCoercive z) := fun z => by
    rw [toEuclideanLin_coarseCorrection h, Multigrid.coarseCorrection_apply, map_sub,
      Multigrid.equiv_coarseProjection, Submodule.starProjection_orthogonal_val]
  rw [← WithEnergy.inner_equiv (toEuclideanLin A) h.isSymmetricCoercive,
    ← WithEnergy.inner_equiv (toEuclideanLin A) h.isSymmetricCoercive, hval, hval,
    Submodule.inner_starProjection_left_eq_right]

/-- **Lemma 13.1**: the range of the coarse-grid correction is `A_h`-orthogonal to the range of the
prolongation — the error left by a coarse-grid correction has no component in the coarse space. -/
theorem lemma_13_1_energyInner_eq_zero (h : IsCoarsening A R P) (x : EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin m)) :
    energyInner (toEuclideanLin A) (coarseCorrection R A P ⬝ x) (P ⬝ u) = 0 := by
  have hmem : (coarseCorrection R A P ⬝ x)
      ∈ LinearMap.range (Multigrid.coarseCorrection (toEuclideanLin A) h.isSymmetricCoercive
          (toEuclideanLin P)) := by
    rw [← toEuclideanLin_coarseCorrection h]
    exact ⟨x, rfl⟩
  rw [Multigrid.range_coarseCorrection, LinearMap.mem_ker, LinearMap.comp_apply] at hmem
  rw [energyInner, ← LinearMap.adjoint_inner_left (toEuclideanLin P) u
    (toEuclideanLin A (coarseCorrection R A P ⬝ x)), hmem, inner_zero_left]

/-! ### §13.4.3 The V-cycle, the W-cycle and full multigrid -/

/-- The data of a multigrid hierarchy: for every level `l` a grid of `size l` unknowns carrying the
matrix `A_{h_l}` and the approximate inverse `B_{h_l}` of its smoother (13.40), a prolongation and a
restriction between the levels `l` and `l + 1`, and the interpolation `Î` that full multigrid starts
each level from — Saad allows it to be of higher order than the cycle's own prolongation.

Level `0` is the coarsest, where the problem is solved exactly, and level `l + 1` is finer than
level `l`: Saad's `p + 1` levels `h_0 > h_1 > ⋯ > h_p` are the levels `0, …, p` here.  A hierarchy
is indexed by all of `ℕ` rather than by `Fin (p + 1)`, so that no bound has to be carried through
the recursions; a cycle on level `l` uses the levels `0, …, l` only. -/
structure Hierarchy where
  /-- The number of unknowns of level `l`. -/
  size : ℕ → ℕ
  /-- The matrix `A_{h_l}` of level `l`. -/
  matrix : ∀ l, Matrix (Fin (size l)) (Fin (size l)) ℝ
  /-- The approximate inverse `B_{h_l}` defining the smoother (13.40) of level `l`. -/
  approxInverse : ∀ l, Matrix (Fin (size l)) (Fin (size l)) ℝ
  /-- The prolongation `I_{h_l}^{h_{l+1}}` from level `l` to the finer level `l + 1`. -/
  prolongation : ∀ l, Matrix (Fin (size (l + 1))) (Fin (size l)) ℝ
  /-- The restriction `I_{h_{l+1}}^{h_l}` from level `l + 1` to the coarser level `l`. -/
  restriction : ∀ l, Matrix (Fin (size l)) (Fin (size (l + 1))) ℝ
  /-- The interpolation `Î_{h_l}^{h_{l+1}}` of Algorithm 13.5. -/
  fmgInterpolation : ∀ l, Matrix (Fin (size (l + 1))) (Fin (size l)) ℝ

namespace Hierarchy

/-- The vectors of level `l` of a hierarchy. -/
abbrev Vec (H : Hierarchy) (l : ℕ) : Type := EuclideanSpace ℝ (Fin (H.size l))

/-- One `γ`-cycle on level `l + 1` written in terms of the solver `mg` of level `l`: `ν₁`
pre-smoothing steps, a coarse-grid correction obtained by `γ` recursive calls on the restricted
residual, and `ν₂` post-smoothing steps.  This is the body of Algorithm 13.4. -/
noncomputable def cycleStep (H : Hierarchy) (ν₁ ν₂ γ l : ℕ) (mg : H.Vec l → H.Vec l → H.Vec l)
    (u f : H.Vec (l + 1)) : H.Vec (l + 1) :=
  let S := smootherStep (H.matrix (l + 1)) (H.approxInverse (l + 1)) f
  let u₁ := S^[ν₁] u
  let d := coarseRhs (H.restriction l) (f - (H.matrix (l + 1) ⬝ u₁))
  S^[ν₂] (u₁ + (H.prolongation l ⬝ (fun v => mg v d)^[γ] 0))

/-- **Algorithm 13.4**, the `γ`-cycle `MG(A_h, u, f, ν₁, ν₂, γ)`: on the coarsest level the system
is solved exactly, and on every finer level `ν₁` smoothing steps are followed by `γ` recursive
cycles on the restricted residual and then by `ν₂` smoothing steps.

The book proves nothing about the cycles themselves — their error propagation operators are the
composites of the two-grid ones of (13.43) — so this is a definition and nothing more; what §13.4
does prove about them is the cost estimate `equation_13_44` and, through Algorithm 13.5,
`theorem_13_2`. -/
noncomputable def cycle (H : Hierarchy) (ν₁ ν₂ γ : ℕ) : ∀ l : ℕ, H.Vec l → H.Vec l → H.Vec l
  | 0 => fun _ f => ((H.matrix 0)⁻¹ ⬝ f)
  | l + 1 => cycleStep H ν₁ ν₂ γ l (cycle H ν₁ ν₂ γ l)

/-- On the coarsest level a cycle solves the system exactly. -/
@[simp]
theorem cycle_zero (H : Hierarchy) (ν₁ ν₂ γ : ℕ) (u f : H.Vec 0) :
    H.cycle ν₁ ν₂ γ 0 u f = ((H.matrix 0)⁻¹ ⬝ f) := rfl

/-- On every finer level a cycle is one `cycleStep` around `γ` cycles of the level below. -/
theorem cycle_succ (H : Hierarchy) (ν₁ ν₂ γ l : ℕ) :
    H.cycle ν₁ ν₂ γ (l + 1) = cycleStep H ν₁ ν₂ γ l (H.cycle ν₁ ν₂ γ l) := rfl

/-- **Algorithm 13.3**, the V-cycle: the `γ`-cycle with one recursive call per level. -/
noncomputable def vcycle (H : Hierarchy) (ν₁ ν₂ : ℕ) : ∀ l : ℕ, H.Vec l → H.Vec l → H.Vec l :=
  H.cycle ν₁ ν₂ 1

/-- The W-cycle: the `γ`-cycle with two recursive calls per level. -/
noncomputable def wcycle (H : Hierarchy) (ν₁ ν₂ : ℕ) : ∀ l : ℕ, H.Vec l → H.Vec l → H.Vec l :=
  H.cycle ν₁ ν₂ 2

/-- **Algorithm 13.5**, full multigrid: sweep once from the coarsest level upwards, solving the
coarsest problem exactly and taking on each finer level the interpolant `Î` of the previous level's
approximation as the initial guess for `μ` cycles.  The right-hand sides `f l` are the
discretizations of the problem on each level, not restrictions of one another. -/
noncomputable def fullMultigrid (H : Hierarchy) (ν₁ ν₂ γ μ : ℕ) (f : ∀ l, H.Vec l) :
    ∀ l : ℕ, H.Vec l
  | 0 => ((H.matrix 0)⁻¹ ⬝ f 0)
  | l + 1 => (fun u => H.cycle ν₁ ν₂ γ (l + 1) u (f (l + 1)))^[μ]
      (H.fmgInterpolation l ⬝ fullMultigrid H ν₁ ν₂ γ μ f l)

/-- Full multigrid solves the coarsest system exactly. -/
@[simp]
theorem fullMultigrid_zero (H : Hierarchy) (ν₁ ν₂ γ μ : ℕ) (f : ∀ l, H.Vec l) :
    H.fullMultigrid ν₁ ν₂ γ μ f 0 = ((H.matrix 0)⁻¹ ⬝ f 0) := rfl

/-- On every finer level full multigrid applies `μ` cycles to the interpolated approximation of
the level below. -/
theorem fullMultigrid_succ (H : Hierarchy) (ν₁ ν₂ γ μ : ℕ) (f : ∀ l, H.Vec l) (l : ℕ) :
    H.fullMultigrid ν₁ ν₂ γ μ f (l + 1)
      = (fun u => H.cycle ν₁ ν₂ γ (l + 1) u (f (l + 1)))^[μ]
          (H.fmgInterpolation l ⬝ H.fullMultigrid ν₁ ν₂ γ μ f l) := rfl

end Hierarchy

/-! ### §13.4.3 The cost of a cycle, (13.44)–(13.46) -/

/-- **Saad (13.44)–(13.46)**, the cost of one cycle.  Let `n_l` be the number of unknowns of level
`l`, so that `n_{l+1} = 2^d n_l` after a coarsening by two in each of `d` dimensions, and let `C l`
bound the cost of one `γ`-cycle on level `l`: a visit to a level costs `η` per unknown, and the
level below is visited `γ` times, which is the recurrence `C (l+1) ≤ η n_{l+1} + γ C l`.

If `γ < 2^d` then the total cost stays proportional to the number of unknowns of the *finest* level,
`C l ≤ η n_l / (1 - γ 2^{-d})` — Saad's `O(n)`, and his condition "`γ < 2` in 1-D and `γ < 4` in
2-D".  A V-cycle (`γ = 1`) satisfies it in every dimension, with the constant `2` in one dimension
and `4/3` in two; a W-cycle (`γ = 2`) satisfies it as soon as `d ≥ 2`, with the constant `2` in two
dimensions.  In one dimension the W-cycle is the borderline case `γ = 2^d`, where this bound fails
and the cost grows like `η n_l log₂ n_l`, Saad's `O(n log₂ n)`.

This is the only quantitative statement the book makes about the cycles themselves, and the whole
of it is the geometric series `∑ (γ 2^{-d})^k`. -/
theorem equation_13_44 {C nsize : ℕ → ℝ} {η γ : ℝ} {d : ℕ} (hη : 0 ≤ η) (hγ : 0 ≤ γ)
    (hγd : γ < 2 ^ d) (hn : ∀ l, nsize (l + 1) = 2 ^ d * nsize l) (hnpos : ∀ l, 0 < nsize l)
    (hC₀ : C 0 ≤ η * nsize 0) (hrec : ∀ l, C (l + 1) ≤ η * nsize (l + 1) + γ * C l) (l : ℕ) :
    C l ≤ η * nsize l / (1 - γ / 2 ^ d) := by
  have hs : (0 : ℝ) < 2 ^ d := by positivity
  have ht : γ / 2 ^ d < 1 := (div_lt_one hs).2 hγd
  have ht0 : (0 : ℝ) ≤ γ / 2 ^ d := div_nonneg hγ hs.le
  have hden : (0 : ℝ) < 1 - γ / 2 ^ d := by linarith
  induction l with
  | zero =>
    have h0 : 0 ≤ η * nsize 0 := mul_nonneg hη (hnpos 0).le
    rw [le_div_iff₀ hden]
    nlinarith
  | succ l ih =>
    have hnl : nsize l = nsize (l + 1) / 2 ^ d := by
      rw [hn l]
      field_simp
    have hne : (2 : ℝ) ^ d - γ ≠ 0 := ne_of_gt (sub_pos.2 hγd)
    calc C (l + 1) ≤ η * nsize (l + 1) + γ * C l := hrec l
      _ ≤ η * nsize (l + 1) + γ * (η * nsize l / (1 - γ / 2 ^ d)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hγ)
      _ = η * nsize (l + 1) / (1 - γ / 2 ^ d) := by
          rw [hnl]
          field_simp
          ring

/-! ### §13.4.4 Full multigrid, Theorem 13.2 -/

/-- The `μ` cycles of Algorithm 13.5 contract the error by `ξ^μ` when one cycle contracts it
by `ξ`. -/
private theorem norm_sub_iterate_le {X : Type*} [NormedAddCommGroup X] {F : X → X} {x : X} {ξ : ℝ}
    (hξ : 0 ≤ ξ) (hF : ∀ v, ‖x - F v‖ ≤ ξ * ‖x - v‖) (μ : ℕ) (v : X) :
    ‖x - F^[μ] v‖ ≤ ξ ^ μ * ‖x - v‖ := by
  induction μ generalizing v with
  | zero => simp
  | succ μ ih =>
    calc ‖x - F^[μ + 1] v‖ = ‖x - F^[μ] (F v)‖ := by rw [Function.iterate_succ_apply]
      _ ≤ ξ ^ μ * ‖x - F v‖ := ih (F v)
      _ ≤ ξ ^ μ * (ξ * ‖x - v‖) := mul_le_mul_of_nonneg_left (hF v) (pow_nonneg hξ μ)
      _ = ξ ^ (μ + 1) * ‖x - v‖ := by ring

/-- **Theorem 13.2**, the full multigrid error bound.  On a hierarchy whose mesh sizes `h_l` halve
from one level to the next, let `u l` be the exact solution of the level-`l` system and `ũ l` the
full multigrid approximation of Algorithm 13.5.  Assume

* the coarsest system is solved exactly, `A_{h_0} u^{h_0} = f^{h_0}` with `A_{h_0}` nonsingular;
* **(13.49)** the interpolation is accurate to the discretization order,
  `‖u^{h_{l+1}} - Î u^{h_l}‖ ≤ c₁ h_{l+1}^κ`;
* **(13.50)** one cycle contracts the error by `ξ`, `‖u^{h_{l+1}} - MG(v)‖ ≤ ξ ‖u^{h_{l+1}} - v‖`,
  which is what `‖M_h‖ ≤ ξ < 1` says once the exact solution is recognized as a fixed point of the
  cycle — the book's (13.55) — and is the only form of (13.50) the proof uses;
* **(13.51)** the interpolations are bounded, `‖Î‖ ≤ c₂ 2^{-κ}`;
* **(13.52)** `c₂ ξ^μ < 1`.

Then the full multigrid approximation is accurate to the discretization order on *every* level,
`‖u^{h_l} - ũ^{h_l}‖ ≤ c₃ c₁ h_l^κ` with `c₃ = ξ^μ/(1 - c₂ ξ^μ)`.

Saad's assumption (13.48) — that the discrete solution is within `c h^κ` of the sampled continuous
one — is what motivates (13.49) and is not used by the proof, so it does not appear. -/
theorem theorem_13_2 (H : Hierarchy) {ν₁ ν₂ γ μ : ℕ} {f u : ∀ l, H.Vec l} {hmesh : ℕ → ℝ}
    {c₁ c₂ ξ κ : ℝ} (hh : ∀ l, hmesh (l + 1) = hmesh l / 2) (hhpos : ∀ l, 0 < hmesh l)
    (hunit : IsUnit (H.matrix 0)) (hsolve : (H.matrix 0 ⬝ u 0) = f 0) (hc₁ : 0 ≤ c₁) (hξ : 0 ≤ ξ)
    (hlt : c₂ * ξ ^ μ < 1)
    (h1349 : ∀ l, ‖u (l + 1) - (H.fmgInterpolation l ⬝ u l)‖ ≤ c₁ * hmesh (l + 1) ^ κ)
    (h1350 : ∀ (l : ℕ) (v : H.Vec (l + 1)),
      ‖u (l + 1) - H.cycle ν₁ ν₂ γ (l + 1) v (f (l + 1))‖ ≤ ξ * ‖u (l + 1) - v‖)
    (h1351 : ∀ l, ‖LinearMap.toContinuousLinearMap (toEuclideanLin (H.fmgInterpolation l))‖
      ≤ c₂ * (2 : ℝ) ^ (-κ)) (l : ℕ) :
    ‖u l - H.fullMultigrid ν₁ ν₂ γ μ f l‖ ≤ ξ ^ μ / (1 - c₂ * ξ ^ μ) * c₁ * hmesh l ^ κ := by
  have hexact : H.fullMultigrid ν₁ ν₂ γ μ f 0 = u 0 := by
    rw [Hierarchy.fullMultigrid_zero, ← hsolve, ← mul_act,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit), one_act]
  refine Multigrid.norm_sub_fullMultigrid_le
    (utilde := fun l => H.fullMultigrid ν₁ ν₂ γ μ f l)
    (interp := fun l => LinearMap.toContinuousLinearMap (toEuclideanLin (H.fmgInterpolation l)))
    hh hhpos hexact hc₁ hξ hlt h1349 (fun l => ?_) h1351 l
  rw [Hierarchy.fullMultigrid_succ]
  exact norm_sub_iterate_le hξ (h1350 l) μ _

end SaadSparse.Chapter13
