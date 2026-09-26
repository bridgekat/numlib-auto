import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Eigen.Sturm
import Numlib.Krylov.CG
import Numlib.Krylov.Convergence.CG
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.NormalEquations
import Numlib.Krylov.Singular
import Numlib.LinearAlgebra.Matrix.LU
import Numlib.Projection.OneDimensional
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter01.Section02

/-!
# Golub–Van Loan §11.3: the conjugate gradient method

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §11.3:
the quadratic `φ(x) = ½ xᵀAx − xᵀb` and the `A`-norm ((11.3.1)–(11.3.5)), steepest descent with
exact line search ((11.3.6)–(11.3.9), Algorithm 11.3.1), the subspace strategy
((11.3.10)–(11.3.11)), CG as the Galerkin method on Krylov spaces (Theorem 11.3.3,
Corollary 11.3.2), CG as Lanczos plus an `LDLᵀ` of `T_k` ((11.3.12)–(11.3.22), Algorithm 11.3.2,
Theorems 11.3.4–11.3.5), the Hestenes–Stiefel form ((11.3.23)–(11.3.25), Algorithm 11.3.3) and the
practical loop (11.3.26), the error estimates of §11.3.8 ((11.3.27)), and CG on the normal
equations (§11.3.9, (11.3.28), Figure 11.3.1).

## Design

The book is real: `A : Matrix (Fin n) (Fin n) ℝ` symmetric positive definite (`A.PosDef`). Every
statement about subspaces, the energy norm or the Krylov iteration is made for the operator
`Matrix.toEuclideanLin A` on `EuclideanSpace ℝ (Fin n)` (written `𝔼 n` in this file), vectors
being moved between `Fin n → ℝ` and `𝔼 n` by `WithLp.toLp 2` / `WithLp.ofLp`. The book's
`φ(x) = ½ xᵀAx − xᵀb` is the backbone's `energyFunctional`, `‖v‖_A = √(vᵀAv)` is `energyNorm`,
`κ₂(A) = λ_max(A)/λ_min(A)` is `NormedRing.condNumber A` for the (scoped) `2`-operator norm of
matrices, equal to the eigenvalue ratio by `Matrix.PosDef.condNumber_l2_eq_div_eigenvalues`. The
book's gradient is `g = Ax − b` and its residual `r = b − Ax`; the backbone's CG state carries the
residual. The book's Hestenes–Stiefel `p_k, μ_k` (`k ≥ 1`) are the backbone's `(CG.iterate (k−1)).p`
and `CG.alpha` at step `k − 1`; `x_k`, `r_k` agree.

Algorithms 11.3.1 and 11.3.3, the practical loop (11.3.26) and the two new columns of
Figure 11.3.1 are monadic programs over a rounding hook `rnd : ℝ → M ℝ` (conventions 1–14 of
`NumlibSurface/GolubVanLoan`), built from Chapter 1's Algorithms 1.1.1 (dot product), 1.1.2
(saxpy) and 1.1.3 (gaxpy); `while` loops are `List.foldlM` over `List.range fuel` with a `done`
flag, `fuel` the last argument. The book analyses no rounding error in this section (§11.3.8 says
only that orthogonality is lost), so each program has an exact specification only: its exact run
(`M := Id`, `rnd := pure`) is the backbone recurrence (`CG.iterate`, `Krylov.CGNR.iterate`,
`Krylov.CGNE.iterate`, `Projection.steepestDescentStep`). Algorithm 11.3.3 and (11.3.26) share the
body `cgUpdate` and its exact specification `cgUpdate_run`.

Algorithm 11.3.2 is identified with Hestenes–Stiefel CG through the backbone's dictionary between
the Lanczos and the CG coefficients (`CG.arnoldi_vec_eq`, `CG.lanczos_alpha_zero_eq`,
`CG.lanczos_alpha_succ_eq`, `CG.lanczos_beta_eq`): after `k = i + 1` steps its `q_k`, `r_k`, `α_k`,
`β_k` are the Lanczos quantities of `r₀`, its pivot `d_k` is the `LDLᵀ` pivot of `T_k` and equals
`1/α^{CG}_i`, `ν_k = (−1)ⁱ‖r_i‖α^{CG}_i` and `c_k = (−1)ⁱ‖r_i‖⁻¹p_i`, so that the update
`x_k = x_{k−1} + ν_kc_k` is the CG update `x_{i+1} = x_i + α^{CG}_ip_i` (`algorithm_11_3_2_spec`).
The `LDLᵀ` recurrence (11.3.15) is the backbone's Thomas algorithm (`Matrix.thomasAlpha`,
`Matrix.isLU_tridiagonal_thomas`) for the symmetric tridiagonal matrix. The book's Lanczos
quantities `q_j, α_j, β_j` (`j ≥ 1`) are the backbone's `Arnoldi.vec T r₀ (j−1)`,
`Lanczos.alpha T r₀ (j−1)`, `Lanczos.beta T r₀ (j−1)`.

## Main results

* `equation_11_3_2`, `gradient_energyFunctional`, `equation_11_3_5`: `φ` and the `A`-norm.
* `steepestDescent_mu_eq`, `equation_11_3_7`, `equation_11_3_8`, `kappa_c_le`, `equation_11_3_9`,
  `steepestDescent_rate`, `algorithm_11_3_1`, `algorithm_11_3_1_spec`: steepest descent.
* `equation_11_3_11`, `gradient_mem_krylov`: the subspace strategy.
* `corollary_11_3_2`, `theorem_11_3_3`: termination and the one-step rate of CG.
* `equation_11_3_13`, `lanczos_tridiag_posDef`, `cg_lanczos_coordinates`: CG through Lanczos.
* `ldlTridiag`, `equation_11_3_15`, `cgLDLv`, `cgLDLC`, `equation_11_3_18`–`equation_11_3_22`,
  `cgLDL_x_succ`: the `LDLᵀ` recurrences.
* `algorithm_11_3_2`, `algorithm_11_3_2_spec`, `theorem_11_3_4`, `theorem_11_3_5`: the Lanczos
  version and its orthogonality properties.
* `equation_11_3_23`, `equation_11_3_24`, `equation_11_3_25`, `hestenesStiefel_coeffs`: the
  passage to the Hestenes–Stiefel form.
* `algorithm_11_3_3`, `algorithm_11_3_3_spec`, `practicalCG`, `equation_11_3_26`: the
  Hestenes–Stiefel programs.
* `cg_relativeError_le`, `equation_11_3_27`: error estimates.
* `energyFunctional_normalEquations`, `equation_11_3_28`, `cgne_isMinError`, `cgnr`, `cgnr_spec`,
  `cgne`, `cgne_spec`: CGNR and CGNE.

## Not formalized here

Operation counts and storage (§11.3.5's "13n flops", §11.3.8's four arrays), the uniqueness claim
"the only way to satisfy this requirement is `S_k = 𝒦(A, g₀, k)`" of §11.3.3 (no precise statement),
the Problems, and the Notes and References. The preliminary CG loop (11.3.14) and Theorem 11.3.1,
which is stated for it, are not here yet: (11.3.14) calls Chapter 10's Lanczos program
(Algorithm 10.1.1), whose surface is not available on this branch.
-/

open Matrix Krylov Filter Topology
open scoped RealInnerProductSpace

namespace GolubVanLoan.Chapter11

/-- The Euclidean space `ℝⁿ` on which the Krylov statements of this file live. -/
local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- The CG iterates of `A` in the backbone, for the data `b`, `x₀` in coordinates. -/
local notation "cgIt" A:max b:max x₀:max j:max =>
  CG.iterate (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) j

/-- The initial residual `r₀ = b − Ax₀` in `𝔼 n`, for the data `b`, `x₀` in coordinates. -/
local notation "cgR" A:max b:max x₀:max =>
  WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)

/-! ### Helpers: matrices acting on `𝔼 n` -/

section Helpers

/-- The real Euclidean inner product of two coordinate vectors is their dot product. -/
private theorem inner_toLp (u v : Fin n → ℝ) :
    ⟪(WithLp.toLp 2 u : 𝔼 n), WithLp.toLp 2 v⟫ = u ⬝ᵥ v := by
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]

/-- `√(uᵀu) = ‖u‖₂`. -/
private theorem sqrt_dotProduct_self (u : Fin n → ℝ) :
    √(u ⬝ᵥ u) = ‖(WithLp.toLp 2 u : 𝔼 n)‖ := by
  rw [← inner_toLp, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- `uᵀu = 0 ↔ u = 0`. -/
private theorem dotProduct_self_eq_zero_iff (u : Fin n → ℝ) : u ⬝ᵥ u = 0 ↔ u = 0 := by
  rw [← inner_toLp, inner_self_eq_zero, WithLp.toLp_eq_zero]

/-- `A⁻¹ (A v) = v` on `𝔼 n` for nonsingular `A`. -/
private theorem inv_apply_apply {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (v : 𝔼 n) :
    toEuclideanLin A⁻¹ (toEuclideanLin A v) = v := by
  have h := (isUnit_iff_isUnit_det A).1 hA
  simp only [toEuclideanLin_apply, mulVec_mulVec, nonsing_inv_mul _ h,
    one_mulVec, WithLp.toLp_ofLp]

/-- `A (A⁻¹ v) = v` on `𝔼 n` for nonsingular `A`. -/
private theorem apply_inv_apply {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (v : 𝔼 n) :
    toEuclideanLin A (toEuclideanLin A⁻¹ v) = v := by
  have h := (isUnit_iff_isUnit_det A).1 hA
  simp only [toEuclideanLin_apply, mulVec_mulVec, mul_nonsing_inv _ h,
    one_mulVec, WithLp.toLp_ofLp]

/-- The energy norm is even: `‖x − y‖_A = ‖y − x‖_A`. -/
private theorem energyNorm_sub_comm (T : 𝔼 n →ₗ[ℝ] 𝔼 n) (x y : 𝔼 n) :
    energyNorm T (x - y) = energyNorm T (y - x) := by
  rw [energyNorm, energyNorm, ← neg_sub y x, map_neg, inner_neg_left, inner_neg_right, neg_neg]

/-- The spectral bounds of a positive definite matrix: its extreme eigenvalues `0 < λ_min ≤ λ_max`
bound the quadratic form, and `κ₂(A) = λ_max/λ_min`. -/
private theorem posDef_bounds {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) [Nonempty (Fin n)] :
    ∃ lmin lmax : ℝ, 0 < lmin ∧ lmin ≤ lmax ∧
      (toEuclideanLin A).IsSymmetricBoundedBy lmin lmax ∧
      (open scoped Matrix.Norms.L2Operator in NormedRing.condNumber A) = lmax / lmin := by
  have hbddA : BddAbove (Set.range hA.1.eigenvalues) := (Set.finite_range _).bddAbove
  have hbddB : BddBelow (Set.range hA.1.eigenvalues) := (Set.finite_range _).bddBelow
  obtain ⟨imin, himin⟩ := exists_eq_ciInf_of_finite (f := hA.1.eigenvalues)
  refine ⟨⨅ i, hA.1.eigenvalues i, ⨆ i, hA.1.eigenvalues i, ?_, ?_, ?_, ?_⟩
  · rw [← himin]; exact hA.eigenvalues_pos imin
  · exact (ciInf_le hbddB imin).trans (le_ciSup hbddA imin)
  · exact hA.1.isSymmetricBoundedBy_toEuclideanLin fun i =>
      ⟨ciInf_le hbddB i, le_ciSup hbddA i⟩
  · exact hA.condNumber_l2_eq_div_eigenvalues

open scoped Matrix.Norms.L2Operator in
/-- `‖A v‖₂ ≤ ‖A‖₂ ‖v‖₂`. -/
private theorem norm_toEuclideanLin_apply_le (M : Matrix (Fin n) (Fin n) ℝ) (v : 𝔼 n) :
    ‖toEuclideanLin M v‖ ≤ ‖M‖ * ‖v‖ := by
  rw [l2_opNorm_eq_norm_toEuclideanLin]
  exact (LinearMap.toContinuousLinearMap (toEuclideanLin M)).le_opNorm v

/-- The steepest-descent rate beats the book's: `(λ_max − λ_min)/(λ_max + λ_min)` is at most
`√(1 − λ_min/λ_max)`, i.e. `((κ − 1)/(κ + 1))² ≤ 1 − 1/κ`. -/
private theorem kantorovich_sq_le {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin ≤ lmax) :
    ((lmax - lmin) / (lmax + lmin)) ^ 2 ≤ 1 - 1 / (lmax / lmin) := by
  have hL : 0 < lmax := hl.trans_le hll
  rw [one_div_div, div_pow, div_le_iff₀ (by positivity),
    show 1 - lmin / lmax = (lmax - lmin) / lmax by field_simp, div_mul_eq_mul_div,
    le_div_iff₀ hL]
  nlinarith [mul_nonneg (sub_nonneg.2 hll) hl.le]

end Helpers

/-! ### §11.3.1: an optimization problem -/

section Optimization

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- The quadratic of the energy functional along a gradient line: with `g = Ax − b`,
`φ(x − μg) = φ(x) − μ gᵀg + ½ μ² gᵀAg`. -/
private theorem energyFunctional_sub_smul (hA : (toEuclideanLin A).IsSymmetric) {b x g : 𝔼 n}
    (hg : toEuclideanLin A x - b = g) (μ : ℝ) :
    energyFunctional (toEuclideanLin A) b (x - μ • g) =
      energyFunctional (toEuclideanLin A) b x - μ * ⟪g, g⟫ +
        μ ^ 2 * ⟪toEuclideanLin A g, g⟫ / 2 := by
  have h := energyFunctional_add_smul hA b x g (-μ)
  rw [show x - μ • g = x + (-μ) • g by rw [neg_smul, sub_eq_add_neg], h,
    show b - toEuclideanLin A x = -g by rw [← hg]; abel]
  simp only [inner_neg_left, RCLike.re_to_real, Real.norm_eq_abs, sq_abs]
  ring

/-- A positive definite `A` has a solution of `Ax = b`, namely `A⁻¹b`. -/
private theorem apply_inv_eq (hA : A.PosDef) (b : 𝔼 n) :
    toEuclideanLin A (toEuclideanLin A⁻¹ b) = b :=
  apply_inv_apply hA.isUnit b

/-- **(11.3.1)–(11.3.3).** "If `A ∈ ℝⁿˣⁿ` is symmetric positive definite, … the problem `Ax = b` is
equivalent to solving the optimization problem `min φ(x)` where `φ(x) = ½ xᵀAx − xᵀb`": `x` solves
`Ax = b` iff it minimizes `φ`. -/
theorem equation_11_3_2 (hA : A.PosDef) (b x : 𝔼 n) :
    toEuclideanLin A x = b ↔
      ∀ y, energyFunctional (toEuclideanLin A) b x ≤ energyFunctional (toEuclideanLin A) b y := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  constructor
  · intro hx y
    have h := hT.energyFunctional_sub_eq hx y
    have := sq_nonneg (energyNorm (toEuclideanLin A) (y - x))
    linarith
  · intro h
    have hs := apply_inv_eq hA b
    have h1 := hT.energyFunctional_sub_eq hs x
    have h2 := h (toEuclideanLin A⁻¹ b)
    have h3 : energyNorm (toEuclideanLin A) (x - toEuclideanLin A⁻¹ b) = 0 := by
      nlinarith [energyNorm_nonneg (toEuclideanLin A) (x - toEuclideanLin A⁻¹ b)]
    rw [hT.energyNorm_eq_zero_iff, sub_eq_zero] at h3
    rw [h3, hs]

/-- **§11.3.1.** "`φ` is convex and its gradient is given by `∇φ(x) = Ax − b`." -/
theorem gradient_energyFunctional (hA : A.PosDef) (b : 𝔼 n) :
    (∀ x, HasGradientAt (energyFunctional (toEuclideanLin A) b) (toEuclideanLin A x - b) x) ∧
      ConvexOn ℝ Set.univ (energyFunctional (toEuclideanLin A) b) := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  refine ⟨fun x => hasGradientAt_energyFunctional_of_finiteDimensional hT.isSymmetric b x,
    convex_univ, fun x _ y _ a c ha hc hac => ?_⟩
  -- `a φ x + c φ y − φ(a x + c y) = ½ a c ‖x − y‖²_A ≥ 0`
  have hsym : ⟪toEuclideanLin A y, x⟫ = ⟪toEuclideanLin A x, y⟫ := by
    rw [hT.isSymmetric y x, real_inner_comm]
  have hq : 0 ≤ ⟪toEuclideanLin A (x - y), x - y⟫ := by
    have := hT.isPositive.re_inner_nonneg_left (x - y)
    simpa only [RCLike.re_to_real] using this
  have hc' : c = 1 - a := by linarith
  subst hc'
  simp only [energyFunctional, RCLike.re_to_real, smul_eq_mul, map_add, map_smul, map_sub,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, conj_trivial] at hq ⊢
  rw [hsym] at hq ⊢
  nlinarith [mul_nonneg ha hc]

/-- **(11.3.5).** "`φ(x_c) = ½‖x_c − x_*‖²_A + φ(x_*)`" and "`φ(x_*) = −bᵀA⁻¹b/2`", for
`x_* = A⁻¹b`. -/
theorem equation_11_3_5 (hA : A.PosDef) (b x : 𝔼 n) :
    energyFunctional (toEuclideanLin A) b x =
        energyNorm (toEuclideanLin A) (x - toEuclideanLin A⁻¹ b) ^ 2 / 2 +
          energyFunctional (toEuclideanLin A) b (toEuclideanLin A⁻¹ b) ∧
      energyFunctional (toEuclideanLin A) b (toEuclideanLin A⁻¹ b) =
        -⟪b, toEuclideanLin A⁻¹ b⟫ / 2 := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  refine ⟨?_, ?_⟩
  · have h := hT.energyFunctional_sub_eq (apply_inv_eq hA b) x
    linarith
  · simp only [energyFunctional, apply_inv_eq hA b, RCLike.re_to_real]
    ring

end Optimization

/-! ### §11.3.2: steepest descent -/

section SteepestDescent

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **(11.3.6)** and the line after it. With the gradient `g_c = Ax_c − b ≠ 0`, the line search
`min_μ φ(x_c − μg_c)` is solved exactly by `μ_c = g_cᵀg_c / g_cᵀAg_c` and by no other `μ`, and the
resulting point `x_c − μ_c g_c` is the backbone's steepest-descent step (the one-dimensional
Galerkin step along the residual `r_c = −g_c`). -/
theorem steepestDescent_mu_eq (hA : A.PosDef) {b x g : 𝔼 n} (hg : toEuclideanLin A x - b = g)
    (hg0 : g ≠ 0) :
    (∀ μ₀ : ℝ, (∀ μ : ℝ, energyFunctional (toEuclideanLin A) b (x - μ₀ • g) ≤
        energyFunctional (toEuclideanLin A) b (x - μ • g)) ↔
        μ₀ = ⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫) ∧
      x - (⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫) • g =
        Projection.steepestDescentStep (toEuclideanLin A) b x := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have hq : 0 < ⟪toEuclideanLin A g, g⟫ := by
    simpa only [RCLike.re_to_real] using hT.isCoercive.inner_self_pos hg0
  have hq' : ⟪g, toEuclideanLin A g⟫ = ⟪toEuclideanLin A g, g⟫ := real_inner_comm _ _
  have hquad := energyFunctional_sub_smul hT.isSymmetric hg
  -- `φ(x − μg) = φ(x − μ_c g) + ½ gᵀAg (μ − μ_c)²`
  have hsq : ∀ μ : ℝ, energyFunctional (toEuclideanLin A) b (x - μ • g) =
      energyFunctional (toEuclideanLin A) b (x - (⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫) • g) +
        ⟪toEuclideanLin A g, g⟫ / 2 * (μ - ⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫) ^ 2 := by
    intro μ
    rw [hquad, hquad, hq']
    field_simp
    ring
  refine ⟨fun μ₀ => ⟨fun h => ?_, fun h μ => ?_⟩, ?_⟩
  · have h1 := h (⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫)
    rw [hsq μ₀] at h1
    have h2 : (μ₀ - ⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫) ^ 2 ≤ 0 := by
      have := mul_nonneg (div_nonneg hq.le zero_le_two)
        (sq_nonneg (μ₀ - ⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫))
      nlinarith
    have h3 := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _))
    linarith
  · rw [h, hsq μ]
    have := mul_nonneg (div_nonneg hq.le zero_le_two)
      (sq_nonneg (μ - ⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫))
    linarith
  · have hr : b - toEuclideanLin A x = -g := by rw [← hg]; abel
    rw [Projection.steepestDescentStep, Projection.step1, hr, map_neg, inner_neg_neg,
      inner_neg_neg, smul_neg, ← sub_eq_add_neg]

/-- **(11.3.7).** "`φ(x_+) = φ(x_c) − ½ (g_cᵀg_c)²/(r_cᵀAr_c)`" for the steepest-descent successor
`x_+ = x_c − μ_c g_c`; `r_c = −g_c`, so the printed `r_cᵀAr_c` is `g_cᵀAg_c`. -/
theorem equation_11_3_7 (hA : A.PosDef) {b x g : 𝔼 n} (hg : toEuclideanLin A x - b = g)
    (hg0 : g ≠ 0) :
    energyFunctional (toEuclideanLin A) b (x - (⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫) • g) =
      energyFunctional (toEuclideanLin A) b x - ⟪g, g⟫ ^ 2 / ⟪g, toEuclideanLin A g⟫ / 2 := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have hq : 0 < ⟪toEuclideanLin A g, g⟫ := by
    simpa only [RCLike.re_to_real] using hT.isCoercive.inner_self_pos hg0
  rw [energyFunctional_sub_smul hT.isSymmetric hg, real_inner_comm g (toEuclideanLin A g)]
  field_simp
  ring

/-- **(11.3.8).** With `κ_c = (g_cᵀAg_c/g_cᵀg_c)(g_cᵀA⁻¹g_c/g_cᵀg_c)`: "`g_cᵀA⁻¹g_c = 2φ(x_c) +
bᵀA⁻¹b`" and "`φ(x_+) = φ(x_c) − (1/κ_c)(φ(x_c) + ½ bᵀA⁻¹b)`". -/
theorem equation_11_3_8 (hA : A.PosDef) {b x g : 𝔼 n} (hg : toEuclideanLin A x - b = g)
    (hg0 : g ≠ 0) :
    ⟪g, toEuclideanLin A⁻¹ g⟫ =
        2 * energyFunctional (toEuclideanLin A) b x + ⟪b, toEuclideanLin A⁻¹ b⟫ ∧
      energyFunctional (toEuclideanLin A) b (x - (⟪g, g⟫ / ⟪g, toEuclideanLin A g⟫) • g) =
        energyFunctional (toEuclideanLin A) b x -
          1 / ((⟪g, toEuclideanLin A g⟫ / ⟪g, g⟫) * (⟪g, toEuclideanLin A⁻¹ g⟫ / ⟪g, g⟫)) *
            (energyFunctional (toEuclideanLin A) b x + ⟪b, toEuclideanLin A⁻¹ b⟫ / 2) := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have hu := hA.isUnit
  have hinv : toEuclideanLin A⁻¹ g = x - toEuclideanLin A⁻¹ b := by
    rw [← hg, map_sub, inv_apply_apply hu]
  have hsym : ⟪g, toEuclideanLin A⁻¹ b⟫ = ⟪toEuclideanLin A x, toEuclideanLin A⁻¹ b⟫ -
      ⟪b, toEuclideanLin A⁻¹ b⟫ := by rw [← hg, inner_sub_left]
  have hAx : ⟪toEuclideanLin A x, toEuclideanLin A⁻¹ b⟫ = ⟪x, b⟫ := by
    rw [hT.isSymmetric, apply_inv_apply hu]
  have h1 : ⟪g, toEuclideanLin A⁻¹ g⟫ =
      2 * energyFunctional (toEuclideanLin A) b x + ⟪b, toEuclideanLin A⁻¹ b⟫ := by
    rw [hinv, inner_sub_right, hsym, hAx, energyFunctional, RCLike.re_to_real, RCLike.re_to_real,
      ← hg, inner_sub_left, real_inner_comm x b]
    ring
  refine ⟨h1, ?_⟩
  have hgg : 0 < ⟪g, g⟫ := real_inner_self_pos.2 hg0
  have hq : 0 < ⟪g, toEuclideanLin A g⟫ := by
    rw [real_inner_comm]
    simpa only [RCLike.re_to_real] using hT.isCoercive.inner_self_pos hg0
  have hinvpos : 0 < ⟪g, toEuclideanLin A⁻¹ g⟫ := by
    have hne : toEuclideanLin A⁻¹ g ≠ 0 := fun h0 => hg0 (by
      rw [← apply_inv_apply hu g, h0, map_zero])
    have := hT.isCoercive.inner_self_pos hne
    rw [apply_inv_apply hu, RCLike.re_to_real] at this
    exact this
  rw [equation_11_3_7 hA hg hg0,
    show energyFunctional (toEuclideanLin A) b x + ⟪b, toEuclideanLin A⁻¹ b⟫ / 2 =
      ⟪g, toEuclideanLin A⁻¹ g⟫ / 2 by rw [h1]; ring]
  field_simp

open scoped Matrix.Norms.L2Operator in
/-- **§11.3.2.** "`κ_c = (g_cᵀAg_c/g_cᵀg_c)(g_cᵀA⁻¹g_c/g_cᵀg_c) ≤ λ_max(A)/λ_min(A) = κ₂(A)`." -/
theorem kappa_c_le (hA : A.PosDef) {g : 𝔼 n} (hg0 : g ≠ 0) :
    (⟪g, toEuclideanLin A g⟫ / ⟪g, g⟫) * (⟪g, toEuclideanLin A⁻¹ g⟫ / ⟪g, g⟫) ≤
      NormedRing.condNumber A := by
  have : Nonempty (Fin n) := by
    by_contra h
    exact hg0 (Subsingleton.elim (h := by
      rw [not_nonempty_iff] at h
      infer_instance) g 0)
  obtain ⟨lmin, lmax, hl, hll, hB, hκ⟩ := posDef_bounds hA
  rw [hκ]
  have hu := hA.isUnit
  set h := toEuclideanLin A⁻¹ g with hh
  have hAh : toEuclideanLin A h = g := apply_inv_apply hu g
  have hgg : 0 < ⟪g, g⟫ := real_inner_self_pos.2 hg0
  have hgg' : ⟪g, g⟫ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  have hup : ⟪g, toEuclideanLin A g⟫ ≤ lmax * ‖g‖ ^ 2 := by
    have := hB.re_inner_le g
    rwa [RCLike.re_to_real, real_inner_comm] at this
  have hlow : 0 ≤ ⟪g, toEuclideanLin A g⟫ := by
    have := hB.le_re_inner g
    rw [RCLike.re_to_real, real_inner_comm] at this
    nlinarith [sq_nonneg ‖g‖]
  -- `gᵀA⁻¹g = hᵀAh ≥ λ_min ‖h‖²` and `gᵀA⁻¹g = gᵀh ≤ ‖g‖‖h‖`, so `gᵀA⁻¹g ≤ ‖g‖²/λ_min`
  have hlow' : lmin * ‖h‖ ^ 2 ≤ ⟪g, h⟫ := by
    have := hB.le_re_inner h
    rwa [RCLike.re_to_real, hAh] at this
  have hcs : ⟪g, h⟫ ≤ ‖g‖ * ‖h‖ := real_inner_le_norm g h
  have hnh : lmin * ‖h‖ ≤ ‖g‖ := by
    rcases (norm_nonneg h).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]; exact norm_nonneg g
    · nlinarith
  have hinv_le : ⟪g, h⟫ ≤ ‖g‖ ^ 2 / lmin := by
    rw [le_div_iff₀ hl]
    nlinarith [norm_nonneg g, norm_nonneg h]
  have hinv_nonneg : 0 ≤ ⟪g, h⟫ := le_trans (by positivity) hlow'
  rw [hgg']
  have hg2 : 0 < ‖g‖ ^ 2 := by rw [← hgg']; exact hgg
  calc (⟪g, toEuclideanLin A g⟫ / ‖g‖ ^ 2) * (⟪g, h⟫ / ‖g‖ ^ 2)
      ≤ (lmax * ‖g‖ ^ 2 / ‖g‖ ^ 2) * (‖g‖ ^ 2 / lmin / ‖g‖ ^ 2) := by
        gcongr
        exact div_nonneg (mul_nonneg (hl.le.trans hll) hg2.le) hg2.le
    _ = lmax / lmin := by field_simp

/-- In the zero-dimensional case every vector vanishes. -/
private theorem eq_zero_of_isEmpty [IsEmpty (Fin n)] (v : 𝔼 n) : v = 0 :=
  Subsingleton.elim v 0

open scoped Matrix.Norms.L2Operator in
/-- **(11.3.9).** "`‖x_+ − x_*‖²_A ≤ (1 − 1/κ₂(A)) ‖x_c − x_*‖²_A`" for the steepest-descent
successor `x_+` of `x_c`. (Proved through the sharper Kantorovich factor
`((κ − 1)/(κ + 1))² ≤ 1 − 1/κ` of `Projection.energyNorm_steepestDescentStep_le`.) -/
theorem equation_11_3_9 (hA : A.PosDef) {b xs : 𝔼 n} (hxs : toEuclideanLin A xs = b) (x : 𝔼 n) :
    energyNorm (toEuclideanLin A) (Projection.steepestDescentStep (toEuclideanLin A) b x - xs) ^ 2 ≤
      (1 - 1 / NormedRing.condNumber A) * energyNorm (toEuclideanLin A) (x - xs) ^ 2 := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [eq_zero_of_isEmpty (x - xs), eq_zero_of_isEmpty (_ - xs)]
    simp [energyNorm]
  obtain ⟨lmin, lmax, hl, hll, hB, hκ⟩ := posDef_bounds hA
  rw [hκ, energyNorm_sub_comm, energyNorm_sub_comm _ x]
  have h := Projection.energyNorm_steepestDescentStep_le hl hB hxs x
  have hc : 0 ≤ (lmax - lmin) / (lmax + lmin) :=
    div_nonneg (sub_nonneg.2 hll) (by linarith)
  calc energyNorm (toEuclideanLin A)
          (xs - Projection.steepestDescentStep (toEuclideanLin A) b x) ^ 2
      ≤ ((lmax - lmin) / (lmax + lmin) * energyNorm (toEuclideanLin A) (xs - x)) ^ 2 :=
        pow_le_pow_left₀ (energyNorm_nonneg _ _) h 2
    _ = ((lmax - lmin) / (lmax + lmin)) ^ 2 * energyNorm (toEuclideanLin A) (xs - x) ^ 2 := by
        ring
    _ ≤ (1 - 1 / (lmax / lmin)) * energyNorm (toEuclideanLin A) (xs - x) ^ 2 :=
        mul_le_mul_of_nonneg_right (kantorovich_sq_le hl hll) (sq_nonneg _)

open scoped Matrix.Norms.L2Operator in
/-- **§11.3.2.** "It follows by induction that the method of steepest descent with exact line search
is globally convergent", with "a convergence rate characterized by `(1 − 1/κ₂(A))^{k/2}`":
`‖x_k − x_*‖_A ≤ (1 − 1/κ₂(A))^{k/2} ‖x₀ − x_*‖_A`, and `x_k → x_*`. -/
theorem steepestDescent_rate (hA : A.PosDef) {b xs : 𝔼 n} (hxs : toEuclideanLin A xs = b)
    (x₀ : 𝔼 n) :
    (∀ k : ℕ, energyNorm (toEuclideanLin A)
        ((Projection.steepestDescentStep (toEuclideanLin A) b)^[k] x₀ - xs) ≤
          √(1 - 1 / NormedRing.condNumber A) ^ k * energyNorm (toEuclideanLin A) (x₀ - xs)) ∧
      Tendsto (fun k => (Projection.steepestDescentStep (toEuclideanLin A) b)^[k] x₀) atTop
        (𝓝 xs) := by
  set T := toEuclideanLin A
  set c := √(1 - 1 / NormedRing.condNumber A)
  have hstep : ∀ x, energyNorm T (Projection.steepestDescentStep T b x - xs) ≤
      c * energyNorm T (x - xs) := by
    intro x
    have h := equation_11_3_9 hA hxs x
    rw [← Real.sqrt_sq (energyNorm_nonneg T _), ← Real.sqrt_sq (energyNorm_nonneg T (x - xs)),
      ← Real.sqrt_mul' _ (sq_nonneg _)]
    exact Real.sqrt_le_sqrt h
  have hrate : ∀ k : ℕ, energyNorm T ((Projection.steepestDescentStep T b)^[k] x₀ - xs) ≤
      c ^ k * energyNorm T (x₀ - xs) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', pow_succ, mul_comm (c ^ k) c, mul_assoc]
      exact (hstep _).trans (mul_le_mul_of_nonneg_left ih (Real.sqrt_nonneg _))
  refine ⟨hrate, ?_⟩
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp only [eq_zero_of_isEmpty _]
    exact tendsto_const_nhds
  obtain ⟨lmin, lmax, hl, hll, hB, hκ⟩ := posDef_bounds hA
  have hc1 : c < 1 := by
    rw [Real.sqrt_lt' one_pos, one_pow, hκ, one_div_div]
    have : 0 < lmin / lmax := div_pos hl (hl.trans_le hll)
    linarith
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  -- `√λ_min ‖v‖ ≤ ‖v‖_A`
  have hlow : ∀ v, ‖v‖ ≤ energyNorm T v / √lmin := fun v => by
    rw [le_div_iff₀ (Real.sqrt_pos.2 hl), mul_comm]
    exact LinearMap.IsCoerciveWith.norm_le_energyNorm hl.le hB.le_re_inner v
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => (hlow _).trans
    (div_le_div_of_nonneg_right (hrate k) (Real.sqrt_nonneg _))) ?_
  simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const
    (energyNorm T (x₀ - xs))).div_const (√lmin)

end SteepestDescent

/-! ### Algorithm 11.3.1 -/

section Algorithm1

variable {M : Type → Type} [Monad M]

/-- The state of Algorithm 11.3.1: the step count `k`, the iterate `x`, the gradient `g = Ax − b`,
and the flag `done` recording that the `while` test has failed. -/
structure SteepestDescentState (n : ℕ) where
  /-- The number of completed steps. -/
  k : ℕ
  /-- The iterate `x`. -/
  x : Fin n → ℝ
  /-- The gradient `g = Ax − b`, recomputed after each step. -/
  g : Fin n → ℝ
  /-- The `while` test `‖g‖₂ > τ` has failed. -/
  done : Bool

/-- One pass of the `while` body of Algorithm 11.3.1: the test `‖g‖₂ > τ` (the norm
`fl(√(fl(gᵀg)))` computed and compared exactly with `τ`), then
`μ = (gᵀg)/(gᵀAg)`, `x = x − μg`, `g = Ax − b`. -/
noncomputable def steepestDescentBody (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (τ : ℝ) (s : SteepestDescentState n) : M (SteepestDescentState n) :=
  if s.done then pure s else do
    let gg ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd s.g s.g
    let nrm ← rnd (√gg)
    if nrm ≤ τ then pure { s with done := true } else do
      let Ag ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A s.g 0
      let gAg ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd s.g Ag
      let μ ← rnd (gg / gAg)
      let x ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd (-μ) s.g s.x
      let g ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A x (-b)
      pure ⟨s.k + 1, x, g, false⟩

/-- **Algorithm 11.3.1 (Steepest Descent with Exact Line Search).** "Given a symmetric positive
definite `A ∈ ℝⁿˣⁿ`, `b ∈ ℝⁿ`, `Ax₀ ≈ b`, and a termination tolerance `τ`, the following algorithm
produces `x ∈ ℝⁿ` so that `‖Ax − b‖₂ ≤ τ`":
```
x = x₀, g = Ax − b
while ‖g‖₂ > τ
    μ = (gᵀg)/(gᵀAg), x = x − μg, g = Ax − b
end
```
The `while` loop runs at most `fuel` times. -/
noncomputable def algorithm_11_3_1 (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (b x₀ : Fin n → ℝ) (τ : ℝ) (fuel : ℕ) : M (SteepestDescentState n) := do
  let g₀ ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A x₀ (-b)
  (List.range fuel).foldlM (fun s _ => steepestDescentBody rnd A b τ s) ⟨0, x₀, g₀, false⟩

/-- A `fuel + 1`-pass loop is one more pass after the `fuel`-pass loop, in the identity monad. -/
private theorem run_foldlM_range_succ {σ : Type} (f : σ → ℕ → Id σ) (s : σ) (k : ℕ) :
    Id.run ((List.range (k + 1)).foldlM f s) =
      Id.run (f (Id.run ((List.range k).foldlM f s)) k) := by
  rw [List.range_succ, List.foldlM_append]
  simp

/-- The steepest-descent step of the backbone, in coordinates. -/
private theorem steepestDescentStep_toLp (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    Projection.steepestDescentStep (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x) =
      WithLp.toLp 2 (x + (-((A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b) /
        ((A *ᵥ x - b) ⬝ᵥ (A *ᵥ (A *ᵥ x - b))))) • (A *ᵥ x - b)) := by
  have hr : (WithLp.toLp 2 b : 𝔼 n) - toEuclideanLin A (WithLp.toLp 2 x) =
      WithLp.toLp 2 (-(A *ᵥ x - b)) := by
    rw [toEuclideanLin_toLp, ← WithLp.toLp_sub, neg_sub]
  rw [Projection.steepestDescentStep, Projection.step1, hr, toEuclideanLin_toLp, inner_toLp,
    inner_toLp, ← WithLp.toLp_smul, ← WithLp.toLp_add]
  congr 1
  rw [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_dotProduct, dotProduct_neg, neg_neg, neg_neg,
    smul_neg, neg_smul]

/-- The exact run of one pass of the loop body. -/
private theorem steepestDescentBody_run (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (τ : ℝ)
    (s : SteepestDescentState n) :
    Id.run (steepestDescentBody pure A b τ s) =
      if s.done then s else
        if ‖(WithLp.toLp 2 s.g : 𝔼 n)‖ ≤ τ then { s with done := true } else
          ⟨s.k + 1, s.x + (-(s.g ⬝ᵥ s.g / (s.g ⬝ᵥ (A *ᵥ s.g)))) • s.g,
            A *ᵥ (s.x + (-(s.g ⬝ᵥ s.g / (s.g ⬝ᵥ (A *ᵥ s.g)))) • s.g) - b, false⟩ := by
  unfold steepestDescentBody
  by_cases hd : s.done
  · simp [hd]
  · simp only [hd, Bool.false_eq_true, ite_false, Id.run_bind, Id.run_pure]
    rw [GolubVanLoan.Chapter01.algorithm_1_1_1_spec, ← sqrt_dotProduct_self]
    by_cases ht : √(s.g ⬝ᵥ s.g) ≤ τ
    · simp [ht]
    · simp only [ht, ite_false, Id.run_bind, Id.run_pure,
        GolubVanLoan.Chapter01.algorithm_1_1_3_spec, GolubVanLoan.Chapter01.algorithm_1_1_1_spec,
        GolubVanLoan.Chapter01.algorithm_1_1_2_spec, zero_add]
      rw [neg_add_eq_sub]

/-- The exact run of Algorithm 11.3.1 before the loop. -/
private theorem algorithm_11_3_1_run_zero (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (τ : ℝ) : Id.run (algorithm_11_3_1 pure A b x₀ τ 0) = ⟨0, x₀, A *ᵥ x₀ - b, false⟩ := by
  simp only [algorithm_11_3_1, Id.run_bind, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
    List.range_zero, List.foldlM_nil, Id.run_pure]
  rw [neg_add_eq_sub]

/-- The exact run of Algorithm 11.3.1 with one more pass of the loop. -/
private theorem algorithm_11_3_1_run_succ (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (τ : ℝ) (m : ℕ) : Id.run (algorithm_11_3_1 pure A b x₀ τ (m + 1)) =
      Id.run (steepestDescentBody pure A b τ (Id.run (algorithm_11_3_1 pure A b x₀ τ m))) := by
  simp only [algorithm_11_3_1, Id.run_bind]
  exact run_foldlM_range_succ _ _ _

/-- The loop invariant of the exact run of Algorithm 11.3.1: after `fuel` passes the state holds
the `k`-th steepest-descent iterate for some `k ≤ fuel` and its gradient; if the test failed then
`‖g‖₂ ≤ τ`, and otherwise all `fuel` passes were steps. -/
@[reducible] private def SDInv (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (τ : ℝ)
    (fuel : ℕ) (s : SteepestDescentState n) : Prop :=
  s.k ≤ fuel ∧
    WithLp.toLp 2 s.x =
      (Projection.steepestDescentStep (toEuclideanLin A) (WithLp.toLp 2 b))^[s.k]
        (WithLp.toLp 2 x₀) ∧
    s.g = A *ᵥ s.x - b ∧ (s.done = true → ‖(WithLp.toLp 2 s.g : 𝔼 n)‖ ≤ τ) ∧
    (s.done = false → s.k = fuel)

/-- The exact run of Algorithm 11.3.1 satisfies the loop invariant `SDInv`. -/
private theorem algorithm_11_3_1_inv (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (τ : ℝ)
    (fuel : ℕ) : SDInv A b x₀ τ fuel (Id.run (algorithm_11_3_1 pure A b x₀ τ fuel)) := by
  induction fuel with
  | zero =>
    rw [algorithm_11_3_1_run_zero]
    exact ⟨le_rfl, rfl, rfl, fun h => by simp at h, fun _ => rfl⟩
  | succ fuel ih =>
    rw [algorithm_11_3_1_run_succ, steepestDescentBody_run]
    set s := Id.run (algorithm_11_3_1 pure A b x₀ τ fuel)
    obtain ⟨hk, hx, hg, hdone, hnd⟩ := ih
    by_cases hd : s.done
    · simp only [hd, ↓reduceIte]
      exact ⟨hk.trans (Nat.le_succ _), hx, hg, fun _ => hdone hd,
        fun h => absurd (hd.symm.trans h) (by decide)⟩
    · have hkf : s.k = fuel := hnd (by simpa using hd)
      simp only [hd, Bool.false_eq_true, ↓reduceIte]
      by_cases ht : ‖(WithLp.toLp 2 s.g : 𝔼 n)‖ ≤ τ
      · simp only [ht, ↓reduceIte]
        exact ⟨hk.trans (Nat.le_succ _), hx, hg, fun _ => ht, fun h => by simp at h⟩
      · simp only [ht, ↓reduceIte]
        refine ⟨show s.k + 1 ≤ fuel + 1 by omega, ?_, rfl, fun h => by simp at h,
          fun _ => show s.k + 1 = fuel + 1 by omega⟩
        change WithLp.toLp 2 (s.x + (-(s.g ⬝ᵥ s.g / (s.g ⬝ᵥ (A *ᵥ s.g)))) • s.g) =
          (Projection.steepestDescentStep (toEuclideanLin A) (WithLp.toLp 2 b))^[s.k + 1]
            (WithLp.toLp 2 x₀)
        rw [Function.iterate_succ_apply', ← hx, steepestDescentStep_toLp, ← hg]

/-- **Algorithm 11.3.1, exact semantics.** For symmetric positive definite `A`: (i) the run makes
`k ≤ fuel` steepest-descent steps `x_k = (Projection.steepestDescentStep A b)^[k] x₀`, keeps
`g = Ax − b`, and stops early only when `‖g‖₂ ≤ τ`; (ii) the book's claim "produces `x` so that
`‖Ax − b‖₂ ≤ τ`": for `τ > 0`, every run with enough fuel does. -/
theorem algorithm_11_3_1_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (τ : ℝ) :
    (∀ fuel : ℕ,
      let s := Id.run (algorithm_11_3_1 pure A b x₀ τ fuel)
      s.k ≤ fuel ∧
        WithLp.toLp 2 s.x =
          (Projection.steepestDescentStep (toEuclideanLin A) (WithLp.toLp 2 b))^[s.k]
            (WithLp.toLp 2 x₀) ∧
        s.g = A *ᵥ s.x - b ∧ (s.done = true → ‖(WithLp.toLp 2 s.g : 𝔼 n)‖ ≤ τ) ∧
        (s.done = false → s.k = fuel)) ∧
      (0 < τ → ∃ N, ∀ fuel ≥ N,
        ‖(WithLp.toLp 2 (A *ᵥ (Id.run (algorithm_11_3_1 pure A b x₀ τ fuel)).x - b) : 𝔼 n)‖ ≤
          τ) := by
  refine ⟨fun fuel => algorithm_11_3_1_inv A b x₀ τ fuel, fun hτ => ?_⟩
  have hconv := (steepestDescent_rate hA (apply_inv_eq hA (WithLp.toLp 2 b))
    (WithLp.toLp 2 x₀)).2
  -- `‖A x_k − b‖₂ → 0`
  have hres : Tendsto (fun k => toEuclideanLin A
      ((Projection.steepestDescentStep (toEuclideanLin A) (WithLp.toLp 2 b))^[k]
        (WithLp.toLp 2 x₀)) - WithLp.toLp 2 b) atTop (𝓝 0) := by
    have hc : Continuous (toEuclideanLin A) :=
      LinearMap.continuous_of_finiteDimensional (toEuclideanLin A)
    have := ((hc.tendsto _).comp hconv).sub_const (WithLp.toLp 2 b)
    rwa [Function.comp_def, apply_inv_eq hA, sub_self] at this
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hres) τ hτ
  refine ⟨N, fun fuel hfuel => ?_⟩
  obtain ⟨_, hx, hg, hdone, hnd⟩ := algorithm_11_3_1_inv A b x₀ τ fuel
  rw [← hg]
  cases hd : (Id.run (algorithm_11_3_1 pure A b x₀ τ fuel)).done
  · have hk := hnd hd
    have := hN (Id.run (algorithm_11_3_1 pure A b x₀ τ fuel)).k (by rw [hk]; exact hfuel)
    rw [dist_zero_right, ← hx, toEuclideanLin_toLp, ← WithLp.toLp_sub, ← hg] at this
    exact this.le
  · exact hdone hd

end Algorithm1

/-! ### §11.3.3: a subspace strategy -/

section Subspace

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **(11.3.10)–(11.3.11).** Let `x_k` minimize `φ` over `x₀ + S_k` for nested subspaces
`S₁ ⊆ S₂ ⊆ ⋯`. (i) If `S_{k+1}` contains `x_k − x₀` and the gradient `g_k = Ax_k − b`, then
"`φ(x_{k+1}) ≤ min_μ φ(x_k − μg_k)`"; (ii) "`φ(x₁) ≥ φ(x₂) ≥ ⋯`"; (iii) "since `S_n = ℝⁿ`, we
ultimately obtain `x_* = A⁻¹b`": if `S_m = ℝⁿ` then `Ax_m = b`. -/
theorem equation_11_3_11 (hA : A.PosDef) (b x₀ : 𝔼 n) {S : ℕ → Submodule ℝ (𝔼 n)}
    (hS : Monotone S) {x : ℕ → 𝔼 n}
    (hx : ∀ k, x k - x₀ ∈ S k ∧ ∀ y, y - x₀ ∈ S k →
      energyFunctional (toEuclideanLin A) b (x k) ≤ energyFunctional (toEuclideanLin A) b y) :
    (∀ k, x k - x₀ ∈ S (k + 1) → toEuclideanLin A (x k) - b ∈ S (k + 1) → ∀ μ : ℝ,
      energyFunctional (toEuclideanLin A) b (x (k + 1)) ≤
        energyFunctional (toEuclideanLin A) b (x k - μ • (toEuclideanLin A (x k) - b))) ∧
      Antitone (fun k => energyFunctional (toEuclideanLin A) b (x k)) ∧
      (∀ m, S m = ⊤ → toEuclideanLin A (x m) = b) := by
  refine ⟨fun k h1 h2 μ => (hx (k + 1)).2 _ ?_, fun k l hkl => (hx l).2 _ ?_,
    fun m hm => (equation_11_3_2 hA b (x m)).2 fun y => (hx m).2 y (by rw [hm]; trivial)⟩
  · rw [sub_right_comm]
    exact (S (k + 1)).sub_mem h1 ((S (k + 1)).smul_mem μ h2)
  · exact hS hkl (hx k).1

/-- **§11.3.3.** The Krylov spaces meet the requirement of (11.3.11): with `g₀ = Ax₀ − b` and
`S_k = 𝒦(A, g₀, k)`, if `x_k − x₀ ∈ 𝒦(A, g₀, k)` then the gradient `g_k = Ax_k − b` and the
steepest-descent point `x_k − μg_k` lie in `x₀ + 𝒦(A, g₀, k + 1)`. -/
theorem gradient_mem_krylov (b x₀ : 𝔼 n) {k : ℕ} {xk : 𝔼 n}
    (hxk : xk - x₀ ∈ Krylov.subspace (toEuclideanLin A) (toEuclideanLin A x₀ - b) k) :
    toEuclideanLin A xk - b ∈ Krylov.subspace (toEuclideanLin A) (toEuclideanLin A x₀ - b) (k + 1) ∧
      ∀ μ : ℝ, xk - μ • (toEuclideanLin A xk - b) - x₀ ∈
        Krylov.subspace (toEuclideanLin A) (toEuclideanLin A x₀ - b) (k + 1) := by
  set T := toEuclideanLin A
  -- `𝒦(A, −v, k) = 𝒦(A, v, k)`
  have hneg : ∀ (v : 𝔼 n) m, Krylov.subspace T (-v) m = Krylov.subspace T v m := fun v m =>
    le_antisymm (by simpa using Krylov.subspace_smul T v (-1 : ℝ) m)
      (by simpa using Krylov.subspace_smul T (-v) (-1 : ℝ) m)
  have hg0 : T x₀ - b = -(b - T x₀) := by abel
  rw [hg0, hneg] at hxk ⊢
  have hr := Krylov.residual_mem_subspace_succ hxk
  have hg : T xk - b ∈ Krylov.subspace T (b - T x₀) (k + 1) := by
    rw [show T xk - b = -(b - T xk) by abel]; exact Submodule.neg_mem _ hr
  refine ⟨hg, fun μ => ?_⟩
  rw [sub_right_comm]
  exact Submodule.sub_mem _ (Krylov.subspace_mono T _ (Nat.le_succ k) hxk)
    (Submodule.smul_mem _ μ hg)

end Subspace

/-! ### §11.3.4: termination and the rate of one CG step -/

section CGTheorems

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Corollary 11.3.2.** "Assume that `U ∈ ℝⁿˣʳ`, `D ∈ ℝʳˣʳ` is symmetric, and `r < n`. If
`A = I_n + UDUᵀ` is positive definite and the conjugate gradient iteration is applied to the
problem `Ax = b`, then at most `r + 1` iterations are required to compute `x_*`": the grade of
`r₀ = b − Ax₀` is at most `r + 1`, and the CG iterate `x_{r+1}` solves `Ax = b`. (Neither the
symmetry of `D` nor `r < n` is needed; the proof bounds the grade by `rank(A − I) + 1` instead of
counting distinct eigenvalues.) -/
theorem corollary_11_3_2 {r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ) (D : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) (hAUD : A = 1 + U * D * Uᵀ) (b x₀ : 𝔼 n) :
    Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀) ≤ r + 1 ∧
      toEuclideanLin A (CG.iterate (toEuclideanLin A) b x₀ (r + 1)).x = b := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have hgrade : Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀) ≤ r + 1 := by
    refine (Krylov.grade_le_finrank_range_sub_algebraMap_add_one (toEuclideanLin A)
      (b - toEuclideanLin A x₀) 1).trans ?_
    have hsub : toEuclideanLin A - algebraMap ℝ (Module.End ℝ (𝔼 n)) 1 =
        toEuclideanLin (U * D * Uᵀ) := by
      rw [map_one, Module.End.one_eq_id, ← toEuclideanLin_one (n := Fin n) (𝕜 := ℝ),
        ← map_sub, hAUD, add_sub_cancel_left]
    rw [hsub, toEuclideanLin_eq_toLin_orthonormal, ← rank_eq_finrank_range_toLin]
    have : (U * D * Uᵀ).rank ≤ r := by
      rw [Matrix.mul_assoc]
      exact (rank_mul_le_left _ _).trans (rank_le_width U)
    omega
  exact ⟨hgrade, (CG.isGalerkinIterate b x₀ hT (r + 1)).apply_eq_of_grade_le hgrade⟩

open scoped Matrix.Norms.L2Operator in
/-- **Theorem 11.3.3.** "If `x_*` is the solution to the symmetric positive definite system `Ax = b`
and `x_k` and `x_{k+1}` are produced by the CG method, then
`‖x_{k+1} − x_*‖_A ≤ (1 − 1/κ₂(A))^{1/2} ‖x_k − x_*‖_A`." Here the CG iterates are
`CG.iterate`, the Galerkin iterates over `x₀ + 𝒦(A, r₀, k)`. -/
theorem theorem_11_3_3 (hA : A.PosDef) {b xs : 𝔼 n} (hxs : toEuclideanLin A xs = b) (x₀ : 𝔼 n)
    (k : ℕ) :
    energyNorm (toEuclideanLin A) ((CG.iterate (toEuclideanLin A) b x₀ (k + 1)).x - xs) ≤
      √(1 - 1 / NormedRing.condNumber A) *
        energyNorm (toEuclideanLin A) ((CG.iterate (toEuclideanLin A) b x₀ k).x - xs) := by
  set T := toEuclideanLin A
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [eq_zero_of_isEmpty (_ - xs), eq_zero_of_isEmpty (_ - xs)]
    simp [energyNorm]
  obtain ⟨lmin, lmax, hl, hll, hB, hκ⟩ := posDef_bounds hA
  have h := Krylov.IsGalerkinIterate.energyNorm_error_succ_le hl hB
    (CG.isGalerkinIterate b x₀ hT k) (CG.isGalerkinIterate b x₀ hT (k + 1)) hxs
  rw [energyNorm_sub_comm, energyNorm_sub_comm _ _ xs, hκ]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (energyNorm_nonneg _ _))
  rw [← Real.sqrt_sq (div_nonneg (sub_nonneg.2 hll) (by linarith : (0 : ℝ) ≤ lmax + lmin))]
  exact Real.sqrt_le_sqrt (kantorovich_sq_le hl hll)

end CGTheorems

/-! ### §11.3.4: the Lanczos view of CG -/

section LanczosView

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- **(11.3.12)–(11.3.13)**, recalled from §10.1: "after `k` steps of the Lanczos iteration we have
generated a matrix `Q_k = [q₁ | ⋯ | q_k]` with orthonormal columns, a tridiagonal matrix `T_k` and a
vector `r_k ∈ ran(Q_k)^⊥` so that `AQ_k = Q_kT_k + r_ke_kᵀ`". In coordinates, for `k + 1` steps
from `r₀` (`q_{j+1}` is `Arnoldi.vec (toEuclideanLin A) r₀ j`, `T_{k+1}` is `Lanczos.tridiag`, and
`r_{k+1} = β_{k+1}q_{k+2}` with `β_{k+1} = Lanczos.beta … k`): `A(Q_{k+1}y) = Q_{k+1}(T_{k+1}y) +
β_{k+1} y_{k+1} q_{k+2}`, and `q_{k+2}` is orthogonal to `q₁, …, q_{k+1}`. -/
theorem equation_11_3_13 (hA : A.IsSymm) (r₀ : 𝔼 n) (k : ℕ) (y : Fin (k + 1) → ℝ) :
    toEuclideanLin A (∑ j, y j • Arnoldi.vec (toEuclideanLin A) r₀ j) =
      ∑ i : Fin (k + 1), (Lanczos.tridiag (toEuclideanLin A) r₀ (k + 1) *ᵥ y) i •
          Arnoldi.vec (toEuclideanLin A) r₀ i +
        (Lanczos.beta (toEuclideanLin A) r₀ k * y (Fin.last k)) •
          Arnoldi.vec (toEuclideanLin A) r₀ (k + 1) ∧
      ∀ i ≤ k, ⟪Arnoldi.vec (toEuclideanLin A) r₀ i,
        Arnoldi.vec (toEuclideanLin A) r₀ (k + 1)⟫ = 0 := by
  refine ⟨?_, fun i hi => Arnoldi.inner_vec_eq_zero _ _ (by omega)⟩
  have h := Lanczos.apply_sum r₀ hA.isSymmetric_toEuclideanLin k y
  have hmap : (Lanczos.tridiag (toEuclideanLin A) r₀ (k + 1)).map (algebraMap ℝ ℝ) =
      Lanczos.tridiag (toEuclideanLin A) r₀ (k + 1) := by
    ext; simp
  rw [hmap] at h
  simpa using h

/-- For symmetric `A`, the Lanczos tridiagonal is the Hessenberg matrix of the Arnoldi process. -/
private theorem tridiag_eq_hessenbergSq (hA : A.IsSymm) (r₀ : 𝔼 n) (k : ℕ) :
    Lanczos.tridiag (toEuclideanLin A) r₀ k = Arnoldi.hessenbergSq (toEuclideanLin A) r₀ k := by
  rw [Lanczos.hessenbergSq_eq_map_tridiag r₀ hA.isSymmetric_toEuclideanLin]
  ext; simp

/-- **§11.3.4.** "Note that the tridiagonal matrix `Q_kᵀAQ_k = T_k` is positive definite": for
symmetric positive definite `A` and `k` at most the grade of `r₀`. -/
theorem lanczos_tridiag_posDef (hA : A.PosDef) (r₀ : 𝔼 n) {k : ℕ}
    (hk : k ≤ Krylov.grade (toEuclideanLin A) r₀) :
    (Lanczos.tridiag (toEuclideanLin A) r₀ k).PosDef := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have hsymm : A.IsSymm := isHermitian_iff_isSymm.1 hA.isHermitian
  -- `yᵀT_ky = ⟪Q_ky, AQ_ky⟫`
  have hq : ∀ y : Fin k → ℝ, y ⬝ᵥ (Lanczos.tridiag (toEuclideanLin A) r₀ k *ᵥ y) =
      ⟪∑ i, y i • Arnoldi.vec (toEuclideanLin A) r₀ i,
        toEuclideanLin A (∑ j, y j • Arnoldi.vec (toEuclideanLin A) r₀ j)⟫ := by
    intro y
    rw [tridiag_eq_hessenbergSq hsymm]
    simp only [dotProduct, mulVec, Finset.mul_sum, map_sum, map_smul, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right, Arnoldi.hessenbergSq, Arnoldi.coeff,
      of_apply]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  -- `Q_k` has orthonormal columns, so `Q_ky = 0` forces `y = 0`
  have hv : ∀ y : Fin k → ℝ, (∑ j, y j • Arnoldi.vec (toEuclideanLin A) r₀ j) = 0 → y = 0 := by
    intro y h0
    funext i
    have h1 := congrArg (fun v => ⟪Arnoldi.vec (toEuclideanLin A) r₀ i, v⟫) h0
    simp only [inner_sum, real_inner_smul_right, inner_zero_right] at h1
    rw [Finset.sum_eq_single i (fun j _ hji => by
        rw [Arnoldi.inner_vec_eq_zero _ _ (fun h => hji (Fin.ext h.symm)), mul_zero])
      (by simp), real_inner_self_eq_norm_sq,
      Arnoldi.norm_vec_eq_one_of_lt_grade _ _ (i.2.trans_le hk), one_pow, mul_one] at h1
    exact h1
  refine posDef_iff_dotProduct_mulVec.2 ⟨isHermitian_iff_isSymm.2
    (Lanczos.tridiag_isSymm _ _ _), fun y hy => ?_⟩
  rw [star_trivial, hq]
  have hne : (∑ j, y j • Arnoldi.vec (toEuclideanLin A) r₀ j) ≠ 0 := fun h => hy (hv y h)
  have := hT.isCoercive.inner_self_pos hne
  rwa [RCLike.re_to_real, real_inner_comm] at this

/-- **§11.3.4.** "Since the columns of `Q_k` span `S_k = 𝒦(A, g₀, k)`, … minimizing `φ` over
`x₀ + S_k` is equivalent to minimizing `φ(x₀ + Q_ky)` over all `y ∈ ℝᵏ`, … the minimizer `y_k`
satisfies `T_ky_k = Q_kᵀr₀ = β₀e₁` and so `x_k = x₀ + Q_ky_k`": for `k` at most the grade of
`r₀ = b − Ax₀`, `x₀ + Q_ky` is the Galerkin iterate (the minimizer of `φ` over `x₀ + 𝒦(A, r₀, k)`,
`IsGalerkin.energyFunctional_le`) exactly when `T_ky = β₀e₁`, `β₀ = ‖r₀‖₂`. -/
theorem cg_lanczos_coordinates (hA : A.PosDef) (b x₀ : 𝔼 n) {k : ℕ}
    (hk : k ≤ Krylov.grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) (y : Fin k → ℝ) :
    Krylov.IsGalerkinIterate (toEuclideanLin A) b x₀ k
        (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀) j) ↔
      Lanczos.tridiag (toEuclideanLin A) (b - toEuclideanLin A x₀) k *ᵥ y =
        Krylov.firstVec ‖b - toEuclideanLin A x₀‖ k := by
  rw [Krylov.isGalerkinIterate_iff_mulVec_eq hk,
    ← tridiag_eq_hessenbergSq (isHermitian_iff_isSymm.1 hA.isHermitian)]
  exact Iff.rfl

end LanczosView

/-! ### §11.3.5: the `LDLᵀ` recurrences -/

section LDL

/-- **(11.3.15)** as a definition: the `LDLᵀ` factors of the symmetric tridiagonal matrix with
diagonal `α` and off-diagonal `β`, "`d₁ = α₁`; for `i = 2:k`, `ℓ_{i−1} = β_{i−1}/d_{i−1}`,
`d_i = α_i − ℓ_{i−1}β_{i−1}`", as the pair `(d, ℓ)` of `ℕ`-indexed sequences (0-based, prefix
stable in `k`). The recurrence is the backbone's Thomas algorithm `Matrix.thomasAlpha` for the
tridiagonal matrix with sub- and superdiagonal `β`. -/
noncomputable def ldlTridiag (α β : ℕ → ℝ) : (ℕ → ℝ) × (ℕ → ℝ) :=
  (Matrix.thomasAlpha α (fun i => β (i - 1)) β,
    fun i => β i / Matrix.thomasAlpha α (fun i => β (i - 1)) β i)

/-- `d₁ = α₁`. -/
theorem ldlTridiag_fst_zero (α β : ℕ → ℝ) : (ldlTridiag α β).1 0 = α 0 := rfl

/-- `d_i = α_i − ℓ_{i−1}β_{i−1}`. -/
theorem ldlTridiag_fst_succ (α β : ℕ → ℝ) (i : ℕ) :
    (ldlTridiag α β).1 (i + 1) = α (i + 1) - (ldlTridiag α β).2 i * β i := rfl

/-- `ℓ_{i−1} = β_{i−1}/d_{i−1}`. -/
theorem ldlTridiag_snd (α β : ℕ → ℝ) (i : ℕ) :
    (ldlTridiag α β).2 i = β i / (ldlTridiag α β).1 i := rfl

/-- **(11.3.15).** "By comparing coefficients in `T_k = L_kD_kL_kᵀ` …": if the pivots
`d₁, …, d_{k−1}` are nonzero, the symmetric tridiagonal matrix `T_k` with diagonal `α` and
off-diagonal `β` (`Matrix.symmTridiagonalOf α β k`; the Lanczos `T_k` is
`Lanczos.tridiag = Matrix.symmTridiagonalOf (Lanczos.alpha …) (Lanczos.beta …)`) factors as
`L_kD_kL_kᵀ`, `L_k` unit lower bidiagonal with subdiagonal `ℓ` and `D_k = diag(d)`. For positive
definite `T_k` the pivots are then positive (`Matrix.IsLDM.diag_pos_of_posDef`) and the
factorization is unique (`Matrix.IsLDM.eq_of_isSymm`). -/
theorem equation_11_3_15 (α β : ℕ → ℝ) (k : ℕ)
    (hd : ∀ i, i + 1 < k → (ldlTridiag α β).1 i ≠ 0) :
    Matrix.IsLDM (Matrix.symmTridiagonalOf α β k)
      (Matrix.lowerBidiagonalOf (fun i => (ldlTridiag α β).2 (i - 1)) k)
      (Matrix.diagonal fun i : Fin k => (ldlTridiag α β).1 i)
      (Matrix.lowerBidiagonalOf (fun i => (ldlTridiag α β).2 (i - 1)) k) := by
  have hLU := Matrix.isLU_tridiagonal_thomas α (fun i => β (i - 1)) β hd
  have hL : Matrix.lowerBidiagonalOf (fun i => (ldlTridiag α β).2 (i - 1)) k =
      Matrix.thomasLower α (fun i => β (i - 1)) β k := by
    ext i j
    simp only [Matrix.lowerBidiagonalOf, Matrix.thomasLower, Matrix.of_apply]
    split_ifs with h1 h2
    · rfl
    · rw [← h2]; rfl
    · rfl
  have hU : Matrix.diagonal (fun i : Fin k => (ldlTridiag α β).1 i) *
      (Matrix.lowerBidiagonalOf (fun i => (ldlTridiag α β).2 (i - 1)) k)ᵀ =
      Matrix.thomasUpper α (fun i => β (i - 1)) β k := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.transpose_apply]
    simp only [Matrix.lowerBidiagonalOf, Matrix.thomasUpper, Matrix.of_apply]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, mul_one]
      rfl
    · have hji : j ≠ i := Ne.symm hij
      simp only [hji, hij, ↓reduceIte]
      by_cases hs : (i : ℕ) + 1 = j
      · simp only [hs, ↓reduceIte]
        have hlt : (i : ℕ) + 1 < k := hs ▸ j.2
        have hdi := hd i hlt
        rw [← hs, Nat.add_sub_cancel, ldlTridiag_snd]
        field_simp
      · simp only [hs, ↓reduceIte, mul_zero]
  have hA' : Matrix.symmTridiagonalOf α β k =
      Matrix.tridiagonalOfNat α (fun i => β (i - 1)) β k := by
    ext i j
    simp only [Matrix.symmTridiagonalOf, Matrix.tridiagonalOfNat, Matrix.of_apply]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)
  refine ⟨?_, Matrix.isDiag_diagonal _, ?_, ?_⟩
  · rw [hL]; exact hLU.isUnitLowerTriangular
  · rw [hL]; exact hLU.isUnitLowerTriangular
  · rw [Matrix.mul_assoc, hU, hL, hA']
    exact hLU.mul_eq

/-- The recurrence **(11.3.20)** for the entries of `v_k`, 0-based: `ν₁ = β₀/d₁` and
`ν_k = −d_{k−1}ℓ_{k−1}ν_{k−1}/d_k`. -/
noncomputable def cgLDLnu (α β : ℕ → ℝ) (β₀ : ℝ) : ℕ → ℝ
  | 0 => β₀ / (ldlTridiag α β).1 0
  | i + 1 => -((ldlTridiag α β).1 i * (ldlTridiag α β).2 i * cgLDLnu α β β₀ i) /
      (ldlTridiag α β).1 (i + 1)

/-- **(11.3.16)**: the vector `v_k ∈ ℝᵏ` with `L_kD_kv_k = β₀e₁`, obtained by forward substitution
on the lower bidiagonal `L_kD_k` (`equation_11_3_19`); its entries are `cgLDLnu`. -/
noncomputable def cgLDLv (α β : ℕ → ℝ) (β₀ : ℝ) (k : ℕ) : Fin k → ℝ :=
  fun i => cgLDLnu α β β₀ i

/-- **(11.3.19).** "Consider the lower bidiagonal system (11.3.16), e.g.
`[d₁ 0 0 0; d₁ℓ₁ d₂ 0 0; 0 d₂ℓ₂ d₃ 0; 0 0 d₃ℓ₃ d₄] [ν₁; ν₂; ν₃; ν₄] = [β₀; 0; 0; 0]`. We conclude
that `v_k = [v_{k−1}; ν_k]`": the entries `ν` of `v_k` satisfy the rows `d₁ν₁ = β₀` and
`d_{i−1}ℓ_{i−1}ν_{i−1} + d_iν_i = 0` of `L_kD_kv_k = β₀e₁` (for nonzero pivots), and `v_{k+1}`
extends `v_k` by the one entry `ν_{k+1}` (forward substitution is prefix stable). The printed
`v_k = [ν₁; …; ν_{k−1}/ν_k]` is garbled. -/
theorem equation_11_3_19 (α β : ℕ → ℝ) (β₀ : ℝ) (k : ℕ) :
    ((ldlTridiag α β).1 0 ≠ 0 → (ldlTridiag α β).1 0 * cgLDLnu α β β₀ 0 = β₀) ∧
      (∀ i, (ldlTridiag α β).1 (i + 1) ≠ 0 →
        (ldlTridiag α β).1 i * (ldlTridiag α β).2 i * cgLDLnu α β β₀ i +
          (ldlTridiag α β).1 (i + 1) * cgLDLnu α β β₀ (i + 1) = 0) ∧
      cgLDLv α β β₀ (k + 1) = Fin.snoc (cgLDLv α β β₀ k) (cgLDLnu α β β₀ k) := by
  refine ⟨fun h => ?_, fun i h => ?_, ?_⟩
  · simp only [cgLDLnu]
    field_simp
  · simp only [cgLDLnu]
    field_simp
    ring
  · funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [cgLDLv]
    · simp [cgLDLv]

/-- **(11.3.20).** "`ν_k = β₀/d₁` if `k = 1`, `−d_{k−1}ℓ_{k−1}ν_{k−1}/d_k` if `k > 1`" is the last
entry of `v_k`; with `d_{k−1}ℓ_{k−1} = β_{k−1}` it is Algorithm 11.3.2's
`ν_k = −β_{k−1}ν_{k−1}/d_k`. -/
theorem equation_11_3_20 (α β : ℕ → ℝ) (β₀ : ℝ) (k : ℕ) :
    cgLDLv α β β₀ (k + 1) (Fin.last k) = cgLDLnu α β β₀ k ∧
      cgLDLnu α β β₀ 0 = β₀ / (ldlTridiag α β).1 0 ∧
      (∀ i, cgLDLnu α β β₀ (i + 1) = -((ldlTridiag α β).1 i * (ldlTridiag α β).2 i *
        cgLDLnu α β β₀ i) / (ldlTridiag α β).1 (i + 1)) ∧
      ∀ i, (ldlTridiag α β).1 i ≠ 0 →
        cgLDLnu α β β₀ (i + 1) = -(β i * cgLDLnu α β β₀ i) / (ldlTridiag α β).1 (i + 1) := by
  refine ⟨rfl, rfl, fun i => rfl, fun i h => ?_⟩
  rw [cgLDLnu, ldlTridiag_snd, mul_div_cancel₀ _ h]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The columns `c_k` of `C_k` by the recurrence **(11.3.22)**, 0-based: `c₁ = q₁`,
`c_k = q_k − ℓ_{k−1}c_{k−1}`. -/
noncomputable def cgLDLc (q : ℕ → E) (ℓ : ℕ → ℝ) : ℕ → E
  | 0 => q 0
  | i + 1 => q (i + 1) - ℓ i • cgLDLc q ℓ i

/-- **(11.3.17)**: `C_k ∈ ℝ^{n×k}` with `C_kL_kᵀ = Q_k`, as its family of columns `c_1, …, c_k`
(`cgLDLc`); `Q_k = [q₁ | ⋯ | q_k]` is given by its columns `q` (the Lanczos vectors
`Arnoldi.vec (toEuclideanLin A) r₀`), and `L_k` by its subdiagonal `ℓ`. That `C_kL_kᵀ = Q_k`,
column by column `c_j + ℓ_{j−1}c_{j−1} = q_j`, is `equation_11_3_21`. -/
noncomputable def cgLDLC (q : ℕ → E) (ℓ : ℕ → ℝ) (k : ℕ) : Fin k → E :=
  fun j => cgLDLc q ℓ j

/-- **(11.3.18).** "If `C_k ∈ ℝ^{n×k}` satisfies `C_kL_kᵀ = Q_k` (11.3.17), then
`x_k = x₀ + Q_ky_k = x₀ + C_kL_kᵀy_k = x₀ + C_kv_k`": for any coefficients `y`,
`x₀ + Q_ky = x₀ + C_k(L_kᵀy)`, where `(L_kᵀy)_j = y_j + ℓ_jy_{j+1}` (the last entry `y_k`). With
`y = y_k` the solution of `T_ky = β₀e₁` (`cg_lanczos_coordinates`) and `v_k = L_kᵀy_k`, this is the
Galerkin iterate. -/
theorem equation_11_3_18 (q : ℕ → E) (ℓ : ℕ → ℝ) (x₀ : E) (y : ℕ → ℝ) (k : ℕ) :
    x₀ + ∑ j ∈ Finset.range k, y j • q j =
      x₀ + ∑ j ∈ Finset.range k,
        (y j + if j + 1 < k then ℓ j * y (j + 1) else 0) • cgLDLc q ℓ j := by
  congr 1
  -- `∑_{j ≤ m} y_j q_j = ∑_{j ≤ m} y_j c_j + ∑_{j < m} ℓ_j y_{j+1} c_j`
  have key : ∀ m, ∑ j ∈ Finset.range (m + 1), y j • q j =
      ∑ j ∈ Finset.range (m + 1), y j • cgLDLc q ℓ j +
        ∑ j ∈ Finset.range m, (ℓ j * y (j + 1)) • cgLDLc q ℓ j := by
    intro m
    induction m with
    | zero => simp [cgLDLc]
    | succ m ih =>
      have hq : q (m + 1) = cgLDLc q ℓ (m + 1) + ℓ m • cgLDLc q ℓ m := by
        rw [cgLDLc, sub_add_cancel]
      rw [Finset.sum_range_succ (fun j => y j • q j) (m + 1), ih,
        Finset.sum_range_succ (fun j => y j • cgLDLc q ℓ j) (m + 1),
        Finset.sum_range_succ (fun j => (ℓ j * y (j + 1)) • cgLDLc q ℓ j) m, hq, smul_add,
        smul_smul, mul_comm (y (m + 1)) (ℓ m)]
      abel
  rcases k with _ | m
  · simp
  · rw [key, Finset.sum_congr rfl fun j _ => add_smul _ _ _, Finset.sum_add_distrib,
      Finset.sum_range_succ (fun j => (if j + 1 < m + 1 then ℓ j * y (j + 1) else 0) •
        cgLDLc q ℓ j)]
    simp only [show ¬(m + 1 < m + 1) from lt_irrefl _, ↓reduceIte, zero_smul, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j + 1 < m + 1 := by have := Finset.mem_range.1 hj; omega
    simp only [hj', ↓reduceIte]

/-- **(11.3.21)–(11.3.22).** "From this we conclude that `C_k = [C_{k−1} | c_k]`": `C_{k+1}`
extends `C_k` by the column `c_{k+1}`, and the columns solve `C_kL_kᵀ = Q_k` column by column:
`c₁ = q₁`, `c_j + ℓ_{j−1}c_{j−1} = q_j`. -/
theorem equation_11_3_21 (q : ℕ → E) (ℓ : ℕ → ℝ) (k : ℕ) :
    cgLDLC q ℓ (k + 1) = Fin.snoc (cgLDLC q ℓ k) (cgLDLc q ℓ k) ∧
      cgLDLc q ℓ 0 = q 0 ∧ ∀ j, cgLDLc q ℓ (j + 1) + ℓ j • cgLDLc q ℓ j = q (j + 1) := by
  refine ⟨?_, rfl, fun j => by rw [cgLDLc, sub_add_cancel]⟩
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [cgLDLC]
  · simp [cgLDLC]

/-- **(11.3.22).** "`c_k = q₁` if `k = 1`, `q_k − ℓ_{k−1}c_{k−1}` if `k > 1`." -/
theorem equation_11_3_22 (q : ℕ → E) (ℓ : ℕ → ℝ) :
    cgLDLc q ℓ 0 = q 0 ∧ ∀ i, cgLDLc q ℓ (i + 1) = q (i + 1) - ℓ i • cgLDLc q ℓ i :=
  ⟨rfl, fun _ => rfl⟩

/-- **§11.3.5.** "It follows from (11.3.19) and (11.3.21) that `x_k = x₀ + C_kv_k =
x₀ + C_{k−1}v_{k−1} + ν_kc_k = x_{k−1} + ν_kc_k`", with `x_k := x₀ + C_kv_k`. -/
theorem cgLDL_x_succ (α β : ℕ → ℝ) (β₀ : ℝ) (q : ℕ → E) (x₀ : E) (k : ℕ) :
    x₀ + ∑ j ∈ Finset.range (k + 1),
        cgLDLnu α β β₀ j • cgLDLc q (ldlTridiag α β).2 j =
      (x₀ + ∑ j ∈ Finset.range k, cgLDLnu α β β₀ j • cgLDLc q (ldlTridiag α β).2 j) +
        cgLDLnu α β β₀ k • cgLDLc q (ldlTridiag α β).2 k := by
  rw [Finset.sum_range_succ, add_assoc]

end LDL

/-! ### Algorithm 11.3.2: CG, Lanczos version -/

section LanczosCG

variable {M : Type → Type} [Monad M]

/-- The book's vector division `r/β`: every entry divided by `β` and rounded. -/
noncomputable def divVec (rnd : ℝ → M ℝ) (v : Fin n → ℝ) (β : ℝ) : M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun y i => do
    let t ← rnd (y i / β)
    pure (Function.update y i t)) v

/-- The exact run of `divVec` is `v/β`. -/
theorem divVec_run (v : Fin n → ℝ) (β : ℝ) : Id.run (divVec pure v β) = fun i => v i / β := by
  funext i
  rw [divVec, GolubVanLoan.Chapter01.idRun_foldlM_update_apply (fun _ t => (pure (t / β) : Id ℝ))
    _ (List.nodup_finRange n), ite_eq_left (List.mem_finRange i)]
  rfl

/-- The state of Algorithm 11.3.2: the step count `k`, the iterate `x_k`, the Lanczos vector `q_k`
(`0` before the first step), the Lanczos residual `r_k` and `β_k = ‖r_k‖₂`, the last `α_k`, the
last pivot `d_k`, `ν_k`, the direction `c_k`, and the flag `done` of the `while` test. -/
structure LanczosCGState (n : ℕ) where
  /-- The number of completed steps. -/
  k : ℕ
  /-- The iterate `x_k`. -/
  x : Fin n → ℝ
  /-- The Lanczos vector `q_k`. -/
  q : Fin n → ℝ
  /-- The Lanczos residual `r_k = Aq_k − α_kq_k − β_{k−1}q_{k−1}`. -/
  r : Fin n → ℝ
  /-- `β_k = ‖r_k‖₂`. -/
  β : ℝ
  /-- `α_k = q_kᵀAq_k`. -/
  α : ℝ
  /-- The pivot `d_k`. -/
  d : ℝ
  /-- `ν_k`. -/
  ν : ℝ
  /-- The direction `c_k`. -/
  c : Fin n → ℝ
  /-- The `while` test `β_k ≠ 0` has failed. -/
  done : Bool

/-- The `if k = 1 … else … end` block of Algorithm 11.3.2: from `α_k`, `β_{k−1}`, `d_{k−1}`,
`ν_{k−1}`, `c_{k−1}` and `q_k`, the new `(d_k, ν_k, c_k)`: `d₁ = α₁`, `ν₁ = β₀/d₁`, `c₁ = q₁`, or
`ℓ_{k−1} = β_{k−1}/d_{k−1}`, `d_k = α_k − β_{k−1}ℓ_{k−1}`, `ν_k = −β_{k−1}ν_{k−1}/d_k`,
`c_k = q_k − ℓ_{k−1}c_{k−1}`. -/
noncomputable def lanczosCGUpdate (rnd : ℝ → M ℝ) (first : Bool) (α β d ν : ℝ)
    (c q : Fin n → ℝ) : M (ℝ × ℝ × (Fin n → ℝ)) :=
  if first then do
    let ν' ← rnd (β / α)
    pure (α, ν', q)
  else do
    let ℓ ← rnd (β / d)
    let t ← rnd (β * ℓ)
    let d' ← rnd (α - t)
    let u ← rnd (β * ν)
    let ν' ← rnd (-u / d')
    let c' ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd (-ℓ) c q
    pure (d', ν', c')

/-- One pass of the `while` body of Algorithm 11.3.2 (the test `β_k ≠ 0` on the computed value). -/
noncomputable def lanczosCGBody (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (s : LanczosCGState n) : M (LanczosCGState n) :=
  if s.done then pure s else
    if s.β = 0 then pure { s with done := true } else do
      let q ← divVec rnd s.r s.β
      let Aq ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A q 0
      let α ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd q Aq
      let o ← lanczosCGUpdate rnd (decide (s.k = 0)) α s.β s.d s.ν s.c q
      let x ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd o.2.1 o.2.2 s.x
      let r₁ ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd (-α) q Aq
      let r ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd (-s.β) s.q r₁
      let rr ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd r r
      let β ← rnd (√rr)
      pure ⟨s.k + 1, x, q, r, β, α, o.1, o.2.1, o.2.2, false⟩

/-- **Algorithm 11.3.2 (Conjugate Gradients: Lanczos Version).** "If `A ∈ ℝⁿˣⁿ` is symmetric
positive definite, `b ∈ ℝⁿ`, and `Ax₀ ≈ b`, then this algorithm computes `x_* ∈ ℝⁿ` so that
`Ax_* = b`":
```
k = 0, r₀ = b − Ax₀, β₀ = ‖r₀‖₂, q₀ = 0, c₀ = 0
while β_k ≠ 0
    q_{k+1} = r_k/β_k
    k = k + 1
    α_k = q_kᵀAq_k
    if k = 1
        d₁ = α₁, ν₁ = β₀/d₁
        c_k = q₁
    else
        ℓ_{k−1} = β_{k−1}/d_{k−1}, d_k = α_k − β_{k−1}ℓ_{k−1}, ν_k = −β_{k−1}ν_{k−1}/d_k
        c_k = q_k − ℓ_{k−1}c_{k−1}
    end
    x_k = x_{k−1} + ν_kc_k
    r_k = Aq_k − α_kq_k − β_{k−1}q_{k−1}
    β_k = ‖r_k‖₂
end
x_* = x_k
```
The `while` loop runs at most `fuel` times. -/
noncomputable def algorithm_11_3_2 (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (b x₀ : Fin n → ℝ) (fuel : ℕ) : M (LanczosCGState n) := do
  let r₀ ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A (-x₀) b
  let rr ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd r₀ r₀
  let β₀ ← rnd (√rr)
  (List.range fuel).foldlM (fun s _ => lanczosCGBody rnd A s) ⟨0, x₀, 0, r₀, β₀, 0, 0, 0, 0, false⟩

/-- The exact run of the `if k = 1 … else … end` block. -/
private theorem lanczosCGUpdate_run (first : Bool) (α β d ν : ℝ) (c q : Fin n → ℝ) :
    Id.run (lanczosCGUpdate pure first α β d ν c q) =
      if first then (α, β / α, q)
      else (α - β * (β / d), -(β * ν) / (α - β * (β / d)), q + (-(β / d)) • c) := by
  cases first <;>
    simp [lanczosCGUpdate, GolubVanLoan.Chapter01.algorithm_1_1_2_spec]

/-- The new Lanczos vector `q_{k+1} = r_k/β_k` of an exact step. -/
private noncomputable def lcgQ (s : LanczosCGState n) : Fin n → ℝ := fun i => s.r i / s.β

/-- The new `α_{k+1} = q_{k+1}ᵀAq_{k+1}` of an exact step. -/
private noncomputable def lcgAlpha (A : Matrix (Fin n) (Fin n) ℝ) (s : LanczosCGState n) : ℝ :=
  lcgQ s ⬝ᵥ (A *ᵥ lcgQ s)

/-- The new pivot `d_{k+1}` of an exact step. -/
private noncomputable def lcgD (A : Matrix (Fin n) (Fin n) ℝ) (s : LanczosCGState n) : ℝ :=
  if s.k = 0 then lcgAlpha A s else lcgAlpha A s - s.β * (s.β / s.d)

/-- The new `ν_{k+1}` of an exact step. -/
private noncomputable def lcgNu (A : Matrix (Fin n) (Fin n) ℝ) (s : LanczosCGState n) : ℝ :=
  if s.k = 0 then s.β / lcgAlpha A s else -(s.β * s.ν) / lcgD A s

/-- The new direction `c_{k+1}` of an exact step. -/
private noncomputable def lcgC (s : LanczosCGState n) : Fin n → ℝ :=
  if s.k = 0 then lcgQ s else lcgQ s + (-(s.β / s.d)) • s.c

/-- The new Lanczos residual `r_{k+1}` of an exact step. -/
private noncomputable def lcgR (A : Matrix (Fin n) (Fin n) ℝ) (s : LanczosCGState n) :
    Fin n → ℝ :=
  A *ᵥ lcgQ s + (-lcgAlpha A s) • lcgQ s + (-s.β) • s.q

/-- One exact step of Algorithm 11.3.2 (`β_k ≠ 0`). -/
private noncomputable def lanczosCGStep (A : Matrix (Fin n) (Fin n) ℝ) (s : LanczosCGState n) :
    LanczosCGState n :=
  ⟨s.k + 1, s.x + lcgNu A s • lcgC s, lcgQ s, lcgR A s, √(lcgR A s ⬝ᵥ lcgR A s), lcgAlpha A s,
    lcgD A s, lcgNu A s, lcgC s, false⟩

/-- The exact run of one pass of the body of Algorithm 11.3.2. -/
private theorem lanczosCGBody_run (A : Matrix (Fin n) (Fin n) ℝ) (s : LanczosCGState n) :
    Id.run (lanczosCGBody pure A s) =
      if s.done then s else if s.β = 0 then { s with done := true } else lanczosCGStep A s := by
  unfold lanczosCGBody
  by_cases hd : s.done
  · simp only [hd, ↓reduceIte, Id.run_pure]
  · by_cases h0 : s.β = 0
    · simp only [hd, h0, Bool.false_eq_true, ↓reduceIte, Id.run_pure]
    · by_cases hk : s.k = 0
      · simp only [hd, h0, hk, Bool.false_eq_true, ↓reduceIte, decide_true, Id.run_bind,
          Id.run_pure, divVec_run, lanczosCGUpdate_run, GolubVanLoan.Chapter01.algorithm_1_1_1_spec,
          GolubVanLoan.Chapter01.algorithm_1_1_2_spec, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
          zero_add, lanczosCGStep, lcgD, lcgNu, lcgC]
        rfl
      · simp only [hd, h0, hk, Bool.false_eq_true, ↓reduceIte, decide_false, Id.run_bind,
          Id.run_pure, divVec_run, lanczosCGUpdate_run, GolubVanLoan.Chapter01.algorithm_1_1_1_spec,
          GolubVanLoan.Chapter01.algorithm_1_1_2_spec, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
          zero_add, lanczosCGStep, lcgD, lcgNu, lcgC]
        rfl

/-- The exact run of Algorithm 11.3.2 before the loop. -/
private theorem algorithm_11_3_2_run_zero (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) :
    Id.run (algorithm_11_3_2 pure A b x₀ 0) =
      ⟨0, x₀, 0, b - A *ᵥ x₀, √((b - A *ᵥ x₀) ⬝ᵥ (b - A *ᵥ x₀)), 0, 0, 0, 0, false⟩ := by
  simp only [algorithm_11_3_2, Id.run_bind, Id.run_pure,
    GolubVanLoan.Chapter01.algorithm_1_1_3_spec, GolubVanLoan.Chapter01.algorithm_1_1_1_spec,
    List.range_zero, List.foldlM_nil, mulVec_neg, ← sub_eq_add_neg]

/-- The exact run of Algorithm 11.3.2 with one more pass of the loop. -/
private theorem algorithm_11_3_2_run_succ (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (m : ℕ) : Id.run (algorithm_11_3_2 pure A b x₀ (m + 1)) =
      Id.run (lanczosCGBody pure A (Id.run (algorithm_11_3_2 pure A b x₀ m))) := by
  simp only [algorithm_11_3_2, Id.run_bind, Id.run_pure,
    GolubVanLoan.Chapter01.algorithm_1_1_1_spec]
  exact run_foldlM_range_succ _ _ _

/-- The data of Algorithm 11.3.2's state after step `i + 1`, in backbone terms: the Lanczos
vector, residual and coefficients of `r₀`, the `LDLᵀ` pivot, and the CG dictionary
`d = 1/α^{CG}_i`, `ν = (−1)ⁱ‖r_i‖α^{CG}_i`, `c = (−1)ⁱ‖r_i‖⁻¹p_i`. -/
@[reducible] private def LCGData (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (i : ℕ)
    (s : LanczosCGState n) : Prop :=
  WithLp.toLp 2 s.q = Arnoldi.vec (toEuclideanLin A) (cgR A b x₀) i ∧
    WithLp.toLp 2 s.r = Arnoldi.w (toEuclideanLin A) (cgR A b x₀) i ∧
    s.β = Lanczos.beta (toEuclideanLin A) (cgR A b x₀) i ∧
    s.α = Lanczos.alpha (toEuclideanLin A) (cgR A b x₀) i ∧
    s.d = (ldlTridiag (Lanczos.alpha (toEuclideanLin A) (cgR A b x₀))
      (Lanczos.beta (toEuclideanLin A) (cgR A b x₀))).1 i ∧
    s.d = (CG.alpha (toEuclideanLin A) (cgIt A b x₀ i))⁻¹ ∧
    s.ν = (-1) ^ i * ‖(cgIt A b x₀ i).r‖ * CG.alpha (toEuclideanLin A) (cgIt A b x₀ i) ∧
    WithLp.toLp 2 s.c = ((-1) ^ i * ‖(cgIt A b x₀ i).r‖⁻¹) • (cgIt A b x₀ i).p

/-- The state of Algorithm 11.3.2 after `j` steps. -/
@[reducible] private def LCGInv (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (j : ℕ)
    (s : LanczosCGState n) : Prop :=
  s.k = j ∧ WithLp.toLp 2 s.x = (cgIt A b x₀ j).x ∧
    (j = 0 → s.q = 0 ∧ WithLp.toLp 2 s.r = cgR A b x₀ ∧ s.β = ‖cgR A b x₀‖) ∧
    ∀ i, j = i + 1 → LCGData A b x₀ i s

/-- The CG step length is positive while the residual is nonzero. -/
private theorem cg_alpha_pos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    {j : ℕ} (hr : (cgIt A b x₀ j).r ≠ 0) : 0 < CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have h1 := CG.re_inner_apply_direction_pos (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT hr
  rw [RCLike.re_to_real] at h1
  exact div_pos (real_inner_self_pos.2 hr) h1

/-- `α_j⟪Ap_j, p_j⟫ = ‖r_j‖²` for the CG iterates of a positive definite `A`. -/
private theorem cg_alpha_mul {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (j : ℕ) : CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) *
      ⟪toEuclideanLin A (cgIt A b x₀ j).p, (cgIt A b x₀ j).p⟫ = ‖(cgIt A b x₀ j).r‖ ^ 2 := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  rw [CG.alpha, ← real_inner_self_eq_norm_sq]
  by_cases hr : (cgIt A b x₀ j).r = 0
  · rw [hr, inner_zero_left, zero_div, zero_mul]
  · have h1 := CG.re_inner_apply_direction_pos (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT hr
    rw [RCLike.re_to_real] at h1
    exact div_mul_cancel₀ _ h1.ne'

/-- One step of Algorithm 11.3.2 preserves the invariant, below the grade. -/
private theorem lanczosCGStep_inv {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (b x₀ : Fin n → ℝ) {j : ℕ} {s : LanczosCGState n} (hs : LCGInv A b x₀ j s)
    (hj : j < Krylov.grade (toEuclideanLin A) (cgR A b x₀)) :
    s.β ≠ 0 ∧ LCGInv A b x₀ (j + 1) (lanczosCGStep A s) := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have hsym := hT.isSymmetric
  obtain ⟨hk, hx, h0, hsucc⟩ := hs
  have hrj : (cgIt A b x₀ j).r ≠ 0 := CG.residual_ne_zero_of_lt_grade _ _ hT hj
  have hαj : 0 < CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) := cg_alpha_pos hA b x₀ hrj
  have hρj : ‖(cgIt A b x₀ j).r‖ ≠ 0 := norm_ne_zero_iff.2 hrj
  have hQdiv : lcgQ s = s.β⁻¹ • s.r := by funext t; simp [lcgQ, div_eq_inv_mul]
  -- `β_j ≠ 0`, and `q_{j+1}` is the next Lanczos vector
  have hβq : s.β ≠ 0 ∧
      WithLp.toLp 2 (lcgQ s) = Arnoldi.vec (toEuclideanLin A) (cgR A b x₀) j := by
    rcases j with _ | i
    · obtain ⟨-, hr, hb⟩ := h0 rfl
      have hR : cgR A b x₀ ≠ 0 := hrj
      refine ⟨by rw [hb]; exact norm_ne_zero_iff.2 hR, ?_⟩
      have hv := Arnoldi.vec_zero (toEuclideanLin A) (cgR A b x₀) hR
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hv
      rw [hv, hQdiv, WithLp.toLp_smul, hr, hb]
    · obtain ⟨-, hr, hb, -⟩ := hsucc i rfl
      refine ⟨fun h => (not_le.2 hj) ((Lanczos.beta_eq_zero_iff _ hsym _).1 (hb.symm.trans h)),
        ?_⟩
      have hv := Arnoldi.vec_succ_eq (toEuclideanLin A) (cgR A b x₀) i
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hv
      rw [hv, hQdiv, WithLp.toLp_smul, hr, hb]
      rfl
  obtain ⟨hβne, hqv⟩ := hβq
  have hα : lcgAlpha A s = Lanczos.alpha (toEuclideanLin A) (cgR A b x₀) j := by
    rw [lcgAlpha, ← inner_toLp, ← toEuclideanLin_toLp, hqv, Lanczos.alpha, Arnoldi.coeff,
      RCLike.re_to_real]
  have hr' : WithLp.toLp 2 (lcgR A s) = Arnoldi.w (toEuclideanLin A) (cgR A b x₀) j := by
    rw [lcgR, WithLp.toLp_add, WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul,
      ← toEuclideanLin_toLp, hqv, hα]
    rcases j with _ | i
    · have hc := Lanczos.coe_alpha (cgR A b x₀) hsym 0
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hc
      rw [(h0 rfl).1, WithLp.toLp_zero, smul_zero, add_zero, Arnoldi.w, zero_add,
        Finset.sum_range_one, ← hc, neg_smul, ← sub_eq_add_neg]
    · obtain ⟨hq, -, hb, -⟩ := hsucc i rfl
      have hw := Lanczos.w_succ_eq (cgR A b x₀) hsym i
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hw
      rw [hq, hb, hw, neg_smul, neg_smul, ← sub_eq_add_neg, ← sub_eq_add_neg]
  have hβ' : √(lcgR A s ⬝ᵥ lcgR A s) = Lanczos.beta (toEuclideanLin A) (cgR A b x₀) j := by
    rw [sqrt_dotProduct_self, hr']
    rfl
  -- the `LDLᵀ` and CG data of the new state
  have hnew : lcgD A s = (ldlTridiag (Lanczos.alpha (toEuclideanLin A) (cgR A b x₀))
        (Lanczos.beta (toEuclideanLin A) (cgR A b x₀))).1 j ∧
      lcgD A s = (CG.alpha (toEuclideanLin A) (cgIt A b x₀ j))⁻¹ ∧
      lcgNu A s = (-1) ^ j * ‖(cgIt A b x₀ j).r‖ * CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) ∧
      WithLp.toLp 2 (lcgC s) =
        ((-1) ^ j * ‖(cgIt A b x₀ j).r‖⁻¹) • (cgIt A b x₀ j).p := by
    rcases j with _ | i
    · have hk0 : s.k = 0 := hk
      obtain ⟨-, -, hb⟩ := h0 rfl
      have hR : cgR A b x₀ ≠ 0 := hrj
      have hla0 := CG.lanczos_alpha_zero_eq (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT hrj
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hla0
      have hv0 := Arnoldi.vec_zero (toEuclideanLin A) (cgR A b x₀) hR
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hv0
      have hR0 : (cgIt A b x₀ 0).r = cgR A b x₀ := rfl
      have hP0 : (cgIt A b x₀ 0).p = cgR A b x₀ := rfl
      have hd : lcgD A s = (CG.alpha (toEuclideanLin A) (cgIt A b x₀ 0))⁻¹ := by
        simp only [lcgD, hk0, ↓reduceIte]
        rw [hα, hla0]
      refine ⟨?_, hd, ?_, ?_⟩
      · simp only [lcgD, hk0, ↓reduceIte]
        rw [hα, ldlTridiag_fst_zero]
      · simp only [lcgNu, hk0, ↓reduceIte]
        rw [hR0, hb, hα, hla0, div_inv_eq_mul, pow_zero, one_mul]
      · simp only [lcgC, hk0, ↓reduceIte]
        rw [hqv, hR0, hP0, pow_zero, one_mul, hv0]
    · have hk' : s.k ≠ 0 := by omega
      obtain ⟨-, -, hb, -, hd1, hd2, hν, hc⟩ := hsucc i rfl
      have hri : (cgIt A b x₀ i).r ≠ 0 :=
        CG.residual_ne_zero_of_lt_grade _ _ hT (Nat.lt_of_succ_lt hj)
      have hαi : 0 < CG.alpha (toEuclideanLin A) (cgIt A b x₀ i) := cg_alpha_pos hA b x₀ hri
      have hρi : ‖(cgIt A b x₀ i).r‖ ≠ 0 := norm_ne_zero_iff.2 hri
      have hlb := CG.lanczos_beta_eq (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT (k := i) hrj
      rw [RCLike.re_to_real] at hlb
      have hla := CG.lanczos_alpha_succ_eq (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT (k := i) hrj
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hla
      have hbeta : CG.beta (toEuclideanLin A) (cgIt A b x₀ i) =
          ‖(cgIt A b x₀ (i + 1)).r‖ ^ 2 / ‖(cgIt A b x₀ i).r‖ ^ 2 := by
        rw [CG.beta_iterate, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      have hd : lcgD A s = (CG.alpha (toEuclideanLin A) (cgIt A b x₀ (i + 1)))⁻¹ := by
        simp only [lcgD, hk', ↓reduceIte]
        rw [hα, hb, hd2, hla, hbeta, hlb]
        field_simp
        ring
      refine ⟨?_, hd, ?_, ?_⟩
      · simp only [lcgD, hk', ↓reduceIte]
        rw [hα, hb, hd1, ldlTridiag_fst_succ, ldlTridiag_snd]
        ring
      · have hdd := hd
        simp only [lcgNu, hk', ↓reduceIte]
        rw [hdd, hb, hν, hlb]
        field_simp
        ring
      · have hv := CG.arnoldi_vec_eq (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT (i + 1) hrj
        simp only [RCLike.ofReal_real_eq_id, id_eq] at hv
        simp only [lcgC, hk', ↓reduceIte]
        rw [WithLp.toLp_add, WithLp.toLp_smul, hqv, hv, hc, hb, hd2, hlb, CG.iterate_succ_p,
          hbeta, smul_add, smul_smul, smul_smul]
        congr 2
        field_simp
        ring
  obtain ⟨hd1, hd2, hν, hc⟩ := hnew
  have hsgn : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
  refine ⟨hβne, show s.k + 1 = j + 1 by rw [hk], ?_, fun h => absurd h (Nat.succ_ne_zero j),
    fun i hi => ?_⟩
  · change WithLp.toLp 2 (s.x + lcgNu A s • lcgC s) = _
    rw [WithLp.toLp_add, WithLp.toLp_smul, hx, hc, hν, smul_smul, CG.iterate_succ_x]
    congr 2
    rw [show (-1 : ℝ) ^ j * ‖(cgIt A b x₀ j).r‖ * CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) *
        ((-1) ^ j * ‖(cgIt A b x₀ j).r‖⁻¹) = ((-1) ^ j * (-1) ^ j) *
          (‖(cgIt A b x₀ j).r‖ * ‖(cgIt A b x₀ j).r‖⁻¹) *
          CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) by ring,
      hsgn, mul_inv_cancel₀ hρj, one_mul, one_mul]
  · obtain rfl : i = j := by omega
    exact ⟨hqv, hr', hβ', hα, hd1, hd2, hν, hc⟩

/-- The loop invariant of the exact run of Algorithm 11.3.2: after `m` passes the state is the
`min m g`-th state, `g` the grade of `r₀`, and the test has failed iff `g < m`. -/
private theorem algorithm_11_3_2_inv {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (b x₀ : Fin n → ℝ) (m : ℕ) :
    LCGInv A b x₀ (min m (Krylov.grade (toEuclideanLin A) (cgR A b x₀)))
        (Id.run (algorithm_11_3_2 pure A b x₀ m)) ∧
      (Id.run (algorithm_11_3_2 pure A b x₀ m)).done =
        decide (Krylov.grade (toEuclideanLin A) (cgR A b x₀) < m) := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  set g := Krylov.grade (toEuclideanLin A) (cgR A b x₀)
  induction m with
  | zero =>
    rw [algorithm_11_3_2_run_zero, Nat.zero_min]
    refine ⟨⟨rfl, rfl, fun _ => ⟨rfl, ?_, ?_⟩, fun i h => absurd h (by omega)⟩,
      (decide_eq_false (Nat.not_lt_zero g)).symm⟩
    · change WithLp.toLp 2 (b - A *ᵥ x₀) = _
      rw [WithLp.toLp_sub, ← toEuclideanLin_toLp]
    · change √((b - A *ᵥ x₀) ⬝ᵥ (b - A *ᵥ x₀)) = _
      rw [sqrt_dotProduct_self, WithLp.toLp_sub, ← toEuclideanLin_toLp]
  | succ m ih =>
    obtain ⟨hinv, hd⟩ := ih
    rw [algorithm_11_3_2_run_succ, lanczosCGBody_run]
    set s := Id.run (algorithm_11_3_2 pure A b x₀ m)
    rcases lt_or_ge g m with hgm | hmg
    · -- the loop had already stopped
      have hdone : s.done = true := hd.trans (decide_eq_true hgm)
      simp only [hdone, ↓reduceIte]
      rw [min_eq_right hgm.le] at hinv
      rw [min_eq_right (by omega : g ≤ m + 1)]
      exact ⟨hinv, (decide_eq_true (by omega)).symm⟩
    · have hdone : s.done = false := hd.trans (decide_eq_false (by omega))
      rcases hmg.eq_or_lt with hmg | hmg
      · -- the test fails at the grade
        rw [hmg, min_self] at hinv
        have hβ : s.β = 0 := by
          obtain ⟨-, -, h0, hsucc⟩ := hinv
          rcases Nat.eq_zero_or_eq_succ_pred g with hg0 | hg1
          · rw [(h0 hg0).2.2, norm_eq_zero]
            have := CG.residual_eq_zero_of_grade_le (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
              (k := 0) (by omega)
            exact this
          · rw [(hsucc (g - 1) hg1).2.2.1]
            exact (Lanczos.beta_eq_zero_iff _ hT.isSymmetric _).2 (by omega)
        simp only [hdone, Bool.false_eq_true, ↓reduceIte]
        rw [ite_eq_left hβ, min_eq_right (by omega : g ≤ m + 1)]
        exact ⟨hinv, (decide_eq_true (by omega : g < m + 1)).symm⟩
      · -- a step
        rw [min_eq_left hmg.le] at hinv
        obtain ⟨hβ, hstep⟩ := lanczosCGStep_inv hA b x₀ hinv hmg
        simp only [hdone, hβ, Bool.false_eq_true, ↓reduceIte]
        rw [min_eq_left (by omega : m + 1 ≤ g)]
        exact ⟨hstep, (decide_eq_false (by omega)).symm⟩

/-- **Algorithm 11.3.2, exact semantics.** For symmetric positive definite `A`, the exact run makes
`k = min(fuel, grade)` steps, `grade` the dimension of the least `A`-invariant subspace containing
`r₀ = b − Ax₀`; `x_k` is the `k`-th CG iterate `(CG.iterate …).x` (so the Galerkin iterate, and at
the exit through the test `Ax = b`); and for `k = i + 1 ≥ 1`: `q_k` is the Lanczos vector
`Arnoldi.vec … i`, `r_k` the Lanczos residual `Arnoldi.w … i`, `α_k`, `β_k` the Lanczos
coefficients, `d_k` the `LDLᵀ` pivot of `T_k` (`ldlTridiag`), and in terms of the Hestenes–Stiefel
quantities `d_k = 1/α^{CG}_i`, `ν_k = (−1)ⁱ‖r_i‖α^{CG}_i` and `c_k = (−1)ⁱ‖r_i‖⁻¹p_i` — so
`ν_kc_k = α^{CG}_ip_i`. -/
theorem algorithm_11_3_2_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (fuel : ℕ) :
    let s := Id.run (algorithm_11_3_2 pure A b x₀ fuel)
    let T := toEuclideanLin A
    let r₀ : 𝔼 n := WithLp.toLp 2 b - T (WithLp.toLp 2 x₀)
    let it := CG.iterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
    s.k = min fuel (Krylov.grade T r₀) ∧ WithLp.toLp 2 s.x = (it s.k).x ∧
      (∀ i, s.k = i + 1 →
        WithLp.toLp 2 s.q = Arnoldi.vec T r₀ i ∧ WithLp.toLp 2 s.r = Arnoldi.w T r₀ i ∧
        s.β = Lanczos.beta T r₀ i ∧ s.α = Lanczos.alpha T r₀ i ∧
        s.d = (ldlTridiag (Lanczos.alpha T r₀) (Lanczos.beta T r₀)).1 i ∧
        s.d = (CG.alpha T (it i))⁻¹ ∧ s.ν = (-1) ^ i * ‖(it i).r‖ * CG.alpha T (it i) ∧
        WithLp.toLp 2 s.c = ((-1) ^ i * ‖(it i).r‖⁻¹) • (it i).p) ∧
      (s.done = true → A *ᵥ s.x = b) := by
  intro s T r₀ it
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  obtain ⟨⟨hk, hx, -, hsucc⟩, hd⟩ := algorithm_11_3_2_inv hA b x₀ fuel
  refine ⟨hk, by rw [hk]; exact hx, fun i hi => hsucc i (hk.symm.trans hi), fun hdone => ?_⟩
  have hgf : Krylov.grade (toEuclideanLin A) (cgR A b x₀) < fuel :=
    of_decide_eq_true (hd.symm.trans hdone)
  have hr0 := CG.residual_eq_zero_of_grade_le (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
    (k := min fuel (Krylov.grade (toEuclideanLin A) (cgR A b x₀))) (by omega)
  have h0 : WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 s.x) = 0 := by
    rw [hx, ← CG.residual_eq, hr0]
  rw [toEuclideanLin_toLp, ← WithLp.toLp_sub, WithLp.toLp_eq_zero, sub_eq_zero] at h0
  exact h0.symm

/-- `(−1)ʲ(−1)ʲ = 1`. -/
private theorem neg_one_pow_mul_self (j : ℕ) : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by
  rw [← mul_pow]; norm_num

/-- The gradient of the `m`-th CG iterate is minus its residual: `g_m = Ax_m − b = −r_m`. -/
private theorem cg_gradient_eq (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (m : ℕ) :
    toEuclideanLin A (cgIt A b x₀ m).x - WithLp.toLp 2 b = -(cgIt A b x₀ m).r := by
  rw [CG.residual_eq, neg_sub]

/-- **Theorem 11.3.4.** "If `x₁, …, x_k` are generated by Algorithm 11.3.2, then `g_iᵀg_j = 0` for
all `i` and `j` that satisfy `1 ≤ i < j ≤ k`. Moreover, `g_k = ν_kr_k` where `ν_k` and `r_k` are
defined by the algorithm." Here `x_i` is the output of the exact run with `fuel = i`, which for
`i ≤ grade` makes exactly `i` steps (`algorithm_11_3_2_spec`), `g_i = Ax_i − b`; the orthogonality
holds for `0 ≤ i < j` as well. -/
theorem theorem_11_3_4 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    {i j : ℕ} (hij : i < j) (hj : j ≤ Krylov.grade (toEuclideanLin A) (cgR A b x₀)) :
    (A *ᵥ (Id.run (algorithm_11_3_2 pure A b x₀ i)).x - b) ⬝ᵥ
        (A *ᵥ (Id.run (algorithm_11_3_2 pure A b x₀ j)).x - b) = 0 ∧
      A *ᵥ (Id.run (algorithm_11_3_2 pure A b x₀ j)).x - b =
        (Id.run (algorithm_11_3_2 pure A b x₀ j)).ν •
          (Id.run (algorithm_11_3_2 pure A b x₀ j)).r := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  -- `toLp (Ax_m − b) = −r_m` for `m ≤ grade`
  have hg : ∀ m, m ≤ Krylov.grade (toEuclideanLin A) (cgR A b x₀) →
      WithLp.toLp 2 (A *ᵥ (Id.run (algorithm_11_3_2 pure A b x₀ m)).x - b) =
        -(cgIt A b x₀ m).r := by
    intro m hm
    obtain ⟨⟨-, hx, -, -⟩, -⟩ := algorithm_11_3_2_inv hA b x₀ m
    rw [min_eq_left hm] at hx
    rw [WithLp.toLp_sub, ← toEuclideanLin_toLp, hx, cg_gradient_eq]
  refine ⟨?_, ?_⟩
  · rw [← inner_toLp, hg i (hij.le.trans hj), hg j hj, inner_neg_neg]
    exact CG.inner_residual_eq_zero _ _ hT hij.ne
  · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    obtain ⟨⟨-, -, -, hsucc⟩, -⟩ := algorithm_11_3_2_inv hA b x₀ (m + 1)
    rw [min_eq_left hj] at hsucc
    obtain ⟨-, hr, -, -, -, -, hν, -⟩ := hsucc m rfl
    apply WithLp.toLp_injective 2
    rw [hg _ hj, WithLp.toLp_smul, hr, hν]
    -- `w_m = β_m q_{m+1}`
    have hw := Arnoldi.vec_succ_eq (toEuclideanLin A) (cgR A b x₀) m
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hw
    have hwn : Arnoldi.w (toEuclideanLin A) (cgR A b x₀) m =
        Lanczos.beta (toEuclideanLin A) (cgR A b x₀) m •
          Arnoldi.vec (toEuclideanLin A) (cgR A b x₀) (m + 1) := by
      by_cases h0 : Arnoldi.w (toEuclideanLin A) (cgR A b x₀) m = 0
      · rw [h0, Lanczos.beta, h0, norm_zero, zero_smul]
      · rw [hw, smul_smul, Lanczos.beta, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]
    rcases hj.lt_or_eq with hlt | heq
    · have hrm1 : (cgIt A b x₀ (m + 1)).r ≠ 0 := CG.residual_ne_zero_of_lt_grade _ _ hT hlt
      have hrm : (cgIt A b x₀ m).r ≠ 0 :=
        CG.residual_ne_zero_of_lt_grade _ _ hT (Nat.lt_of_succ_lt hlt)
      have hαm := cg_alpha_pos hA b x₀ hrm
      have hρm : ‖(cgIt A b x₀ m).r‖ ≠ 0 := norm_ne_zero_iff.2 hrm
      have hρm1 : ‖(cgIt A b x₀ (m + 1)).r‖ ≠ 0 := norm_ne_zero_iff.2 hrm1
      have hlb := CG.lanczos_beta_eq (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT (k := m) hrm1
      rw [RCLike.re_to_real] at hlb
      have hv := CG.arnoldi_vec_eq (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT (m + 1) hrm1
      simp only [RCLike.ofReal_real_eq_id, id_eq] at hv
      rw [hwn, hv, hlb, smul_smul, smul_smul, ← neg_one_smul ℝ (cgIt A b x₀ (m + 1)).r]
      congr 1
      rw [show (-1 : ℝ) ^ m * ‖(cgIt A b x₀ m).r‖ * CG.alpha (toEuclideanLin A) (cgIt A b x₀ m) *
          (‖(cgIt A b x₀ (m + 1)).r‖ /
            (‖(cgIt A b x₀ m).r‖ * CG.alpha (toEuclideanLin A) (cgIt A b x₀ m))) *
          ((-1) ^ (m + 1) * ‖(cgIt A b x₀ (m + 1)).r‖⁻¹) =
          -((-1) ^ m * (-1) ^ m) *
            ((‖(cgIt A b x₀ m).r‖ * CG.alpha (toEuclideanLin A) (cgIt A b x₀ m)) /
              (‖(cgIt A b x₀ m).r‖ * CG.alpha (toEuclideanLin A) (cgIt A b x₀ m))) *
            (‖(cgIt A b x₀ (m + 1)).r‖ * ‖(cgIt A b x₀ (m + 1)).r‖⁻¹) by ring,
        neg_one_pow_mul_self, div_self (mul_ne_zero hρm hαm.ne'), mul_inv_cancel₀ hρm1]
      ring
    · have hβ0 : Lanczos.beta (toEuclideanLin A) (cgR A b x₀) m = 0 :=
        (Lanczos.beta_eq_zero_iff _ hT.isSymmetric _).2 heq.ge
      have hr0 := CG.residual_eq_zero_of_grade_le (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
        (k := m + 1) heq.ge
      rw [hwn, hβ0, zero_smul, smul_zero, hr0, neg_zero]

/-- **Theorem 11.3.5.** "If `c₁, …, c_k` are generated by Algorithm 11.3.2, then `c_iᵀAc_j = 0` if
`i ≠ j` and `d_j` if `i = j`, for all `i` and `j` that satisfy `1 ≤ i < j ≤ k`" — the printed range
excludes the diagonal case the statement includes; here `1 ≤ i, j ≤ k`, `c_i` and `d_j` read off the
exact runs with `fuel = i`, `j` (at most the grade). -/
theorem theorem_11_3_5 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hig : i ≤ Krylov.grade (toEuclideanLin A) (cgR A b x₀))
    (hjg : j ≤ Krylov.grade (toEuclideanLin A) (cgR A b x₀)) :
    (Id.run (algorithm_11_3_2 pure A b x₀ i)).c ⬝ᵥ
        (A *ᵥ (Id.run (algorithm_11_3_2 pure A b x₀ j)).c) =
      if i = j then (Id.run (algorithm_11_3_2 pure A b x₀ j)).d else 0 := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨⟨-, -, -, hsi⟩, -⟩ := algorithm_11_3_2_inv hA b x₀ (i' + 1)
  obtain ⟨⟨-, -, -, hsj⟩, -⟩ := algorithm_11_3_2_inv hA b x₀ (j' + 1)
  rw [min_eq_left hig] at hsi
  rw [min_eq_left hjg] at hsj
  obtain ⟨-, -, -, -, -, hdj, -, hcj⟩ := hsj j' rfl
  obtain ⟨-, -, -, -, -, -, -, hci⟩ := hsi i' rfl
  rw [← inner_toLp, ← toEuclideanLin_toLp, hci, hcj, map_smul, real_inner_smul_left,
    real_inner_smul_right]
  split_ifs with hij
  · obtain rfl : i' = j' := by omega
    have hr : (cgIt A b x₀ i').r ≠ 0 := CG.residual_ne_zero_of_lt_grade _ _ hT (by omega)
    have hα := cg_alpha_pos hA b x₀ hr
    have hρ : ‖(cgIt A b x₀ i').r‖ ≠ 0 := norm_ne_zero_iff.2 hr
    have hX : ⟪(cgIt A b x₀ i').p, toEuclideanLin A (cgIt A b x₀ i').p⟫ =
        ‖(cgIt A b x₀ i').r‖ ^ 2 / CG.alpha (toEuclideanLin A) (cgIt A b x₀ i') := by
      rw [real_inner_comm, eq_div_iff hα.ne', mul_comm, cg_alpha_mul hA b x₀ i']
    rw [hX, hdj, show (-1 : ℝ) ^ i' * ‖(cgIt A b x₀ i').r‖⁻¹ *
        ((-1) ^ i' * ‖(cgIt A b x₀ i').r‖⁻¹ *
          (‖(cgIt A b x₀ i').r‖ ^ 2 / CG.alpha (toEuclideanLin A) (cgIt A b x₀ i'))) =
        ((-1) ^ i' * (-1) ^ i') * (‖(cgIt A b x₀ i').r‖⁻¹ * ‖(cgIt A b x₀ i').r‖) ^ 2 *
          (CG.alpha (toEuclideanLin A) (cgIt A b x₀ i'))⁻¹ by ring,
      neg_one_pow_mul_self, inv_mul_cancel₀ hρ, one_pow, one_mul, one_mul]
  · have hne : i' ≠ j' := fun h => hij (by rw [h])
    rw [← hT.isSymmetric, CG.inner_apply_direction_eq_zero _ _ hT hne, mul_zero, mul_zero]

/-- **(11.3.23).** "If we write this as `p_k = g_{k−1} + τ_{k−1}p_{k−1}`, …": in the
Hestenes–Stiefel form the search directions are `p_k = −p^{CG}_{k−1}` (`p₁ = g₀`; the backbone's
directions carry the residual sign), they satisfy the book's recurrence with
`τ_{k−1} = β^{CG}_{k−2}`, and each is a nonzero multiple of the direction `c_k` of Algorithm 11.3.2
("since `q_k` is a multiple of `g_{k−1}` … `p_k` is a multiple of `c_k`"), for `k` at most the
grade. -/
theorem equation_11_3_23 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    {k : ℕ} (hk : k + 1 ≤ Krylov.grade (toEuclideanLin A) (cgR A b x₀)) :
    -(cgIt A b x₀ 0).p = toEuclideanLin A (cgIt A b x₀ 0).x - WithLp.toLp 2 b ∧
      (∀ j, -(cgIt A b x₀ (j + 1)).p =
        (toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b) +
          CG.beta (toEuclideanLin A) (cgIt A b x₀ j) • -(cgIt A b x₀ j).p) ∧
      ∃ σ : ℝ, σ ≠ 0 ∧
        -(cgIt A b x₀ k).p =
          σ • WithLp.toLp 2 (Id.run (algorithm_11_3_2 pure A b x₀ (k + 1))).c := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  refine ⟨by rw [cg_gradient_eq]; rfl, fun j => ?_, ?_⟩
  · rw [cg_gradient_eq, CG.iterate_succ_p, neg_add, smul_neg]
  · obtain ⟨⟨-, -, -, hs⟩, -⟩ := algorithm_11_3_2_inv hA b x₀ (k + 1)
    rw [min_eq_left hk] at hs
    obtain ⟨-, -, -, -, -, -, -, hc⟩ := hs k rfl
    have hr : (cgIt A b x₀ k).r ≠ 0 := CG.residual_ne_zero_of_lt_grade _ _ hT (by omega)
    have hρ : ‖(cgIt A b x₀ k).r‖ ≠ 0 := norm_ne_zero_iff.2 hr
    refine ⟨-((-1) ^ k * ‖(cgIt A b x₀ k).r‖),
      neg_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) hρ), ?_⟩
    rw [hc, smul_smul, show -((-1 : ℝ) ^ k * ‖(cgIt A b x₀ k).r‖) *
        ((-1) ^ k * ‖(cgIt A b x₀ k).r‖⁻¹) =
        -(((-1) ^ k * (-1) ^ k) * (‖(cgIt A b x₀ k).r‖ * ‖(cgIt A b x₀ k).r‖⁻¹)) by ring,
      neg_one_pow_mul_self, mul_inv_cancel₀ hρ, mul_one, neg_smul, one_smul]

/-- **(11.3.24)–(11.3.25).** From `Ap_k = Ag_{k−1} + τ_{k−1}Ap_{k−1}` and Theorem 11.3.5:
"`τ_{k−1} = −p_{k−1}ᵀAg_{k−1}/p_{k−1}ᵀAp_{k−1}`" and "`p_kᵀAg_{k−1} = p_kᵀAp_k`", for the
Hestenes–Stiefel directions `p = −p^{CG}` and gradients `g = Ax − b` (`equation_11_3_23`); the first
while the residual `r_{k−2}` is nonzero. -/
theorem equation_11_3_24 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (j : ℕ) :
    ((cgIt A b x₀ j).r ≠ 0 → CG.beta (toEuclideanLin A) (cgIt A b x₀ j) =
      -⟪-(cgIt A b x₀ j).p,
          toEuclideanLin A (toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b)⟫ /
        ⟪-(cgIt A b x₀ j).p, toEuclideanLin A (-(cgIt A b x₀ j).p)⟫) ∧
      ⟪-(cgIt A b x₀ (j + 1)).p,
          toEuclideanLin A (toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b)⟫ =
        ⟪-(cgIt A b x₀ (j + 1)).p, toEuclideanLin A (-(cgIt A b x₀ (j + 1)).p)⟫ := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  have hsym := hT.isSymmetric
  simp only [cg_gradient_eq, map_neg, inner_neg_neg]
  refine ⟨fun hj => ?_, ?_⟩
  · have hpos := CG.re_inner_apply_direction_pos (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT hj
    rw [RCLike.re_to_real] at hpos
    have hconj := CG.inner_apply_direction_eq_zero (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
      (i := j) (j := j + 1) (by omega)
    rw [CG.iterate_succ_p, inner_add_right, real_inner_smul_right] at hconj
    rw [← hsym, ← hsym, eq_div_iff hpos.ne']
    linarith
  · have hconj := CG.inner_apply_direction_eq_zero (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
      (i := j + 1) (j := j) (by omega)
    have hexp : toEuclideanLin A (cgIt A b x₀ (j + 1)).p =
        toEuclideanLin A (cgIt A b x₀ (j + 1)).r +
          CG.beta (toEuclideanLin A) (cgIt A b x₀ j) • toEuclideanLin A (cgIt A b x₀ j).p := by
      rw [CG.iterate_succ_p, map_add, map_smul]
    rw [hexp, inner_add_right, real_inner_smul_right,
      ← hsym (cgIt A b x₀ (j + 1)).p (cgIt A b x₀ j).p, hconj, mul_zero, add_zero]

/-- **(11.3.25).** "`p_kᵀAg_{k−1} = p_kᵀAp_k`" (the second clause of `equation_11_3_24`). -/
theorem equation_11_3_25 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (j : ℕ) :
    ⟪-(cgIt A b x₀ (j + 1)).p,
        toEuclideanLin A (toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b)⟫ =
      ⟪-(cgIt A b x₀ (j + 1)).p, toEuclideanLin A (-(cgIt A b x₀ (j + 1)).p)⟫ :=
  (equation_11_3_24 hA b x₀ j).2

/-- **§11.3.7**, the formulas the Hestenes–Stiefel derivation ends with, for `p = −p^{CG}` and
`g = Ax − b` (`equation_11_3_23`): "`x_k = x_{k−1} − μ_kp_k`" with
"`μ_k = g_{k−1}ᵀg_{k−1}/p_kᵀAp_k`", "`τ_{k−1} = g_{k−1}ᵀg_{k−1}/g_{k−2}ᵀg_{k−2}`", and the two
displays "`g_{k−1}ᵀg_{k−1} = −μ_{k−1}g_{k−1}ᵀAp_{k−1}`",
"`g_{k−2}ᵀg_{k−2} = μ_{k−1}p_{k−1}ᵀAp_{k−1}`"; `μ` is the backbone's `CG.alpha` and `τ` its
`CG.beta`. -/
theorem hestenesStiefel_coeffs {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (j : ℕ) :
    (cgIt A b x₀ (j + 1)).x =
        (cgIt A b x₀ j).x - CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) • -(cgIt A b x₀ j).p ∧
      CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) =
        ⟪toEuclideanLin A (cgIt A b x₀ j).x - WithLp.toLp 2 b,
            toEuclideanLin A (cgIt A b x₀ j).x - WithLp.toLp 2 b⟫ /
          ⟪-(cgIt A b x₀ j).p, toEuclideanLin A (-(cgIt A b x₀ j).p)⟫ ∧
      CG.beta (toEuclideanLin A) (cgIt A b x₀ j) =
        ⟪toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b,
            toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b⟫ /
          ⟪toEuclideanLin A (cgIt A b x₀ j).x - WithLp.toLp 2 b,
            toEuclideanLin A (cgIt A b x₀ j).x - WithLp.toLp 2 b⟫ ∧
      ⟪toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b,
          toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b⟫ =
        -CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) *
          ⟪toEuclideanLin A (cgIt A b x₀ (j + 1)).x - WithLp.toLp 2 b,
            toEuclideanLin A (-(cgIt A b x₀ j).p)⟫ ∧
      ⟪toEuclideanLin A (cgIt A b x₀ j).x - WithLp.toLp 2 b,
          toEuclideanLin A (cgIt A b x₀ j).x - WithLp.toLp 2 b⟫ =
        CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) *
          ⟪-(cgIt A b x₀ j).p, toEuclideanLin A (-(cgIt A b x₀ j).p)⟫ := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  simp only [cg_gradient_eq, map_neg, inner_neg_neg]
  have hcomm : ⟪(cgIt A b x₀ j).p, toEuclideanLin A (cgIt A b x₀ j).p⟫ =
      ⟪toEuclideanLin A (cgIt A b x₀ j).p, (cgIt A b x₀ j).p⟫ := real_inner_comm _ _
  refine ⟨by rw [CG.iterate_succ_x, smul_neg, sub_neg_eq_add], by rw [hcomm]; rfl,
    CG.beta_iterate _ _ _ j, ?_, ?_⟩
  · have horth := CG.inner_residual_eq_zero (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
      (i := j + 1) (j := j) (by omega)
    have h2 : ⟪(cgIt A b x₀ (j + 1)).r, (cgIt A b x₀ (j + 1)).r⟫ =
        ⟪(cgIt A b x₀ (j + 1)).r, (cgIt A b x₀ j).r⟫ -
          CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) *
            ⟪(cgIt A b x₀ (j + 1)).r, toEuclideanLin A (cgIt A b x₀ j).p⟫ := by
      nth_rewrite 2 [CG.iterate_succ_r]
      rw [inner_sub_right, real_inner_smul_right]
    rw [h2, horth]
    ring
  · rw [hcomm, cg_alpha_mul hA b x₀ j, real_inner_self_eq_norm_sq]

end LanczosCG

/-! ### Algorithm 11.3.3 and the practical loop (11.3.26) -/

section HestenesStiefel

variable {M : Type → Type} [Monad M]

/-- The update shared by Algorithm 11.3.3 and (11.3.26): given `ρ = r_{k−1}ᵀr_{k−1}` (and, after
the first step, the previous `ρ₋ = r_{k−2}ᵀr_{k−2}` and direction `p_{k−1}`), form the direction
`p_k = r_{k−1}` (first step) or `p_k = r_{k−1} + τ_{k−1}p_{k−1}` with `τ_{k−1} = ρ/ρ₋`, then
`w = Ap_k`, `μ_k = ρ/p_kᵀw`, `x_k = x_{k−1} + μ_kp_k`, `r_k = r_{k−1} − μ_kw`. Returns
`(x_k, r_k, p_k)`. -/
noncomputable def cgUpdate (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (first : Bool)
    (ρ ρprev : ℝ) (x r p : Fin n → ℝ) : M ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)) := do
  let p ← if first then pure r else do
    let τ ← rnd (ρ / ρprev)
    GolubVanLoan.Chapter01.algorithm_1_1_2 rnd τ p r
  let w ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A p 0
  let pw ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd p w
  let μ ← rnd (ρ / pw)
  let x ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd μ p x
  let r ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd (-μ) w r
  pure (x, r, p)

/-- The direction formed by `cgUpdate` in exact arithmetic. -/
private noncomputable def cgDir (first : Bool) (ρ ρprev : ℝ) (r p : Fin n → ℝ) : Fin n → ℝ :=
  if first then r else r + (ρ / ρprev) • p

/-- The exact run of `cgUpdate`, in closed form. -/
private theorem cgUpdate_run_eq (A : Matrix (Fin n) (Fin n) ℝ) (first : Bool) (ρ ρprev : ℝ)
    (x r p : Fin n → ℝ) :
    Id.run (cgUpdate pure A first ρ ρprev x r p) =
      (x + (ρ / (cgDir first ρ ρprev r p ⬝ᵥ (A *ᵥ cgDir first ρ ρprev r p))) •
          cgDir first ρ ρprev r p,
        r + (-(ρ / (cgDir first ρ ρprev r p ⬝ᵥ (A *ᵥ cgDir first ρ ρprev r p)))) •
          (A *ᵥ cgDir first ρ ρprev r p),
        cgDir first ρ ρprev r p) := by
  cases first <;>
    simp [cgUpdate, cgDir, GolubVanLoan.Chapter01.algorithm_1_1_1_spec,
      GolubVanLoan.Chapter01.algorithm_1_1_2_spec, GolubVanLoan.Chapter01.algorithm_1_1_3_spec]

/-- The exact run of `cgUpdate` is one step of the backbone CG recurrence: if `(x, r)` is the
`j`-th CG state, `ρ = r_jᵀr_j`, and the direction data are right (`first` at `j = 0`; the previous
direction and `ρ₋ = r_{j−1}ᵀr_{j−1}` at `j = i + 1`), the output is `(x_{j+1}, r_{j+1}, p_j)`. -/
theorem cgUpdate_run (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (j : ℕ) (first : Bool)
    (ρ ρprev : ℝ) (x r p : Fin n → ℝ) (hx : WithLp.toLp 2 x = (cgIt A b x₀ j).x)
    (hr : WithLp.toLp 2 r = (cgIt A b x₀ j).r) (hρ : ρ = r ⬝ᵥ r)
    (hdir : (first = true ∧ j = 0) ∨
      (first = false ∧ ∃ i, j = i + 1 ∧ WithLp.toLp 2 p = (cgIt A b x₀ i).p ∧
        ρprev = ⟪(cgIt A b x₀ i).r, (cgIt A b x₀ i).r⟫)) :
    WithLp.toLp 2 (Id.run (cgUpdate pure A first ρ ρprev x r p)).1 = (cgIt A b x₀ (j + 1)).x ∧
      WithLp.toLp 2 (Id.run (cgUpdate pure A first ρ ρprev x r p)).2.1 =
        (cgIt A b x₀ (j + 1)).r ∧
      WithLp.toLp 2 (Id.run (cgUpdate pure A first ρ ρprev x r p)).2.2 = (cgIt A b x₀ j).p := by
  rw [cgUpdate_run_eq]
  have hdirp : WithLp.toLp 2 (cgDir first ρ ρprev r p) = (cgIt A b x₀ j).p := by
    rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, i, rfl, hp, hρp⟩
    · change WithLp.toLp 2 r = _
      rw [hr]
      rfl
    · change WithLp.toLp 2 (r + (ρ / ρprev) • p) = _
      rw [CG.iterate_succ_p, CG.beta_iterate, WithLp.toLp_add, WithLp.toLp_smul, hr, hp, hρ,
        hρp, ← inner_toLp, hr]
  have hρ' : ρ = ⟪(cgIt A b x₀ j).r, (cgIt A b x₀ j).r⟫ := by rw [hρ, ← inner_toLp, hr]
  have halpha : ρ / (cgDir first ρ ρprev r p ⬝ᵥ (A *ᵥ cgDir first ρ ρprev r p)) =
      CG.alpha (toEuclideanLin A) (cgIt A b x₀ j) := by
    rw [CG.alpha, ← hρ', ← hdirp, toEuclideanLin_toLp, inner_toLp, dotProduct_comm]
  refine ⟨?_, ?_, hdirp⟩
  · change WithLp.toLp 2 (x + (ρ / (cgDir first ρ ρprev r p ⬝ᵥ (A *ᵥ cgDir first ρ ρprev r p))) •
      cgDir first ρ ρprev r p) = _
    rw [halpha, CG.iterate_succ_x, WithLp.toLp_add, WithLp.toLp_smul, hx, hdirp]
  · change WithLp.toLp 2 (r + (-(ρ / (cgDir first ρ ρprev r p ⬝ᵥ
      (A *ᵥ cgDir first ρ ρprev r p)))) • (A *ᵥ cgDir first ρ ρprev r p)) = _
    rw [halpha, CG.iterate_succ_r, WithLp.toLp_add, WithLp.toLp_smul, hr, ← hdirp,
      toEuclideanLin_toLp, neg_smul, ← sub_eq_add_neg]

/-- The state of Algorithm 11.3.3: the step count `k`, the iterate `x_k`, the residual `r_k`, the
last direction `p_k`, the last `ρ = r_{k−1}ᵀr_{k−1}`, and the flag `done` of the `while` test. -/
structure HestenesStiefelState (n : ℕ) where
  /-- The number of completed steps. -/
  k : ℕ
  /-- The iterate `x_k`. -/
  x : Fin n → ℝ
  /-- The residual `r_k = b − Ax_k`. -/
  r : Fin n → ℝ
  /-- The last search direction `p_k`. -/
  p : Fin n → ℝ
  /-- `r_{k−1}ᵀr_{k−1}`, the numerator of the last step. -/
  ρ : ℝ
  /-- The `while` test `‖r_k‖₂ > 0` has failed. -/
  done : Bool

/-- One pass of the `while` body of Algorithm 11.3.3: the test `‖r_k‖₂ > 0`, performed as
`fl(r_kᵀr_k) ≠ 0` on the computed value, then `cgUpdate`. -/
noncomputable def hestenesStiefelBody (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (s : HestenesStiefelState n) : M (HestenesStiefelState n) :=
  if s.done then pure s else do
    let ρ ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd s.r s.r
    if ρ = 0 then pure { s with done := true } else do
      let o ← cgUpdate rnd A (decide (s.k = 0)) ρ s.ρ s.x s.r s.p
      pure ⟨s.k + 1, o.1, o.2.1, o.2.2, ρ, false⟩

/-- **Algorithm 11.3.3 (Conjugate Gradients: Hestenes–Stiefel Version).** "If `A ∈ ℝⁿˣⁿ` is
symmetric positive definite, `b ∈ ℝⁿ`, and `Ax₀ ≈ b`, then this algorithm computes `x_* ∈ ℝⁿ` so
that `Ax_* = b`":
```
k = 0, r₀ = b − Ax₀
while ‖r_k‖₂ > 0
    k = k + 1
    if k = 1
        p_k = r₀
    else
        τ_{k−1} = (r_{k−1}ᵀr_{k−1})/(r_{k−2}ᵀr_{k−2}),  p_k = r_{k−1} + τ_{k−1}p_{k−1}
    end
    μ_k = (r_{k−1}ᵀr_{k−1})/(p_kᵀAp_k),  x_k = x_{k−1} + μ_kp_k,  r_k = r_{k−1} − μ_kAp_k
end
x_* = x_k
```
The `while` loop runs at most `fuel` times. -/
noncomputable def algorithm_11_3_3 (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (b x₀ : Fin n → ℝ) (fuel : ℕ) : M (HestenesStiefelState n) := do
  let r₀ ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A (-x₀) b
  (List.range fuel).foldlM (fun s _ => hestenesStiefelBody rnd A s) ⟨0, x₀, r₀, r₀, 0, false⟩

/-- The exact initial residual `b + A(−x₀) = b − Ax₀`, in the backbone. -/
private theorem initial_residual (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) :
    WithLp.toLp 2 (Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A (-x₀) b)) =
      (cgIt A b x₀ 0).r := by
  rw [GolubVanLoan.Chapter01.algorithm_1_1_3_spec, mulVec_neg, ← sub_eq_add_neg, CG.iterate_zero,
    CG.init_r, toEuclideanLin_toLp, WithLp.toLp_sub]

/-- The exact run of one pass of the body of Algorithm 11.3.3. -/
private theorem hestenesStiefelBody_run (A : Matrix (Fin n) (Fin n) ℝ)
    (s : HestenesStiefelState n) :
    Id.run (hestenesStiefelBody pure A s) =
      if s.done then s else if s.r ⬝ᵥ s.r = 0 then { s with done := true } else
        ⟨s.k + 1, (Id.run (cgUpdate pure A (decide (s.k = 0)) (s.r ⬝ᵥ s.r) s.ρ s.x s.r s.p)).1,
          (Id.run (cgUpdate pure A (decide (s.k = 0)) (s.r ⬝ᵥ s.r) s.ρ s.x s.r s.p)).2.1,
          (Id.run (cgUpdate pure A (decide (s.k = 0)) (s.r ⬝ᵥ s.r) s.ρ s.x s.r s.p)).2.2,
          s.r ⬝ᵥ s.r, false⟩ := by
  unfold hestenesStiefelBody
  by_cases hd : s.done
  · simp only [hd, ↓reduceIte, Id.run_pure]
  · by_cases h0 : s.r ⬝ᵥ s.r = 0
    · simp only [hd, h0, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure,
        GolubVanLoan.Chapter01.algorithm_1_1_1_spec]
    · simp only [hd, h0, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure,
        GolubVanLoan.Chapter01.algorithm_1_1_1_spec]

/-- The exact run of Algorithm 11.3.3 before the loop. -/
private theorem algorithm_11_3_3_run_zero (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) :
    Id.run (algorithm_11_3_3 pure A b x₀ 0) =
      ⟨0, x₀, Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A (-x₀) b),
        Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A (-x₀) b), 0, false⟩ :=
  rfl

/-- The exact run of Algorithm 11.3.3 with one more pass of the loop. -/
private theorem algorithm_11_3_3_run_succ (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (m : ℕ) : Id.run (algorithm_11_3_3 pure A b x₀ (m + 1)) =
      Id.run (hestenesStiefelBody pure A (Id.run (algorithm_11_3_3 pure A b x₀ m))) := by
  simp only [algorithm_11_3_3, Id.run_bind]
  exact run_foldlM_range_succ _ _ _

/-- The state of Algorithm 11.3.3 corresponds to the `j`-th backbone CG state. -/
@[reducible] private def HSInv (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (j : ℕ)
    (s : HestenesStiefelState n) : Prop :=
  s.k = j ∧ WithLp.toLp 2 s.x = (cgIt A b x₀ j).x ∧ WithLp.toLp 2 s.r = (cgIt A b x₀ j).r ∧
    ∀ i, j = i + 1 → WithLp.toLp 2 s.p = (cgIt A b x₀ i).p ∧
      s.ρ = ⟪(cgIt A b x₀ i).r, (cgIt A b x₀ i).r⟫

/-- The loop invariant of the exact run of Algorithm 11.3.3: after `m` passes the state is the
`min m g`-th CG state, `g` the grade of `r₀`, and the test has failed iff `g < m`. -/
private theorem algorithm_11_3_3_inv {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (b x₀ : Fin n → ℝ) (m : ℕ) :
    HSInv A b x₀ (min m (Krylov.grade (toEuclideanLin A)
        (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀))))
        (Id.run (algorithm_11_3_3 pure A b x₀ m)) ∧
      (Id.run (algorithm_11_3_3 pure A b x₀ m)).done =
        decide (Krylov.grade (toEuclideanLin A)
          (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)) < m) := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  set g := Krylov.grade (toEuclideanLin A) (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀))
  induction m with
  | zero =>
    rw [algorithm_11_3_3_run_zero, Nat.zero_min]
    exact ⟨⟨rfl, rfl, initial_residual A b x₀, fun i h => absurd h (by omega)⟩,
      (decide_eq_false (Nat.not_lt_zero g)).symm⟩
  | succ m ih =>
    obtain ⟨⟨hk, hx, hr, hp⟩, hd⟩ := ih
    rw [algorithm_11_3_3_run_succ, hestenesStiefelBody_run]
    set s := Id.run (algorithm_11_3_3 pure A b x₀ m)
    rcases lt_or_ge g m with hgm | hmg
    · -- the loop had already stopped
      have hdone : s.done = true := hd.trans (decide_eq_true hgm)
      simp only [hdone, ↓reduceIte]
      rw [min_eq_right hgm.le] at hk hx hr hp
      rw [min_eq_right (by omega : g ≤ m + 1)]
      exact ⟨⟨hk, hx, hr, hp⟩, (decide_eq_true (by omega)).symm⟩
    · have hdone : s.done = false := hd.trans (decide_eq_false (by omega))
      rcases hmg.eq_or_lt with hmg | hmg
      · -- the test fails at the grade
        rw [hmg, min_self] at hk hx hr hp
        have hr0 : s.r = 0 := by
          have h0 := CG.residual_eq_zero_of_grade_le (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
            (k := g) le_rfl
          exact (WithLp.toLp_eq_zero 2).1 (hr.trans h0)
        have hc : s.r ⬝ᵥ s.r = 0 := by rw [hr0, dotProduct_zero]
        simp only [hdone, hc, Bool.false_eq_true, ↓reduceIte]
        rw [min_eq_right (by omega : g ≤ m + 1)]
        exact ⟨⟨hk, hx, hr, hp⟩, (decide_eq_true (by omega : g < m + 1)).symm⟩
      · -- a step
        rw [min_eq_left hmg.le] at hk hx hr hp
        have hne : (cgIt A b x₀ m).r ≠ 0 := CG.residual_ne_zero_of_lt_grade _ _ hT hmg
        have hc : ¬ s.r ⬝ᵥ s.r = 0 := by
          rw [dotProduct_self_eq_zero_iff]
          rintro h0
          exact hne (by rw [← hr, h0, WithLp.toLp_zero])
        simp only [hdone, hc, Bool.false_eq_true, ↓reduceIte]
        rw [min_eq_left (by omega : m + 1 ≤ g)]
        have hdir : (decide (s.k = 0) = true ∧ m = 0) ∨ (decide (s.k = 0) = false ∧
            ∃ i, m = i + 1 ∧ WithLp.toLp 2 s.p = (cgIt A b x₀ i).p ∧
              s.ρ = ⟪(cgIt A b x₀ i).r, (cgIt A b x₀ i).r⟫) := by
          rcases Nat.eq_zero_or_eq_succ_pred m with h0 | h1
          · exact Or.inl ⟨by rw [hk, h0]; rfl, h0⟩
          · exact Or.inr ⟨by rw [hk]; exact decide_eq_false (by omega), m - 1, h1,
              hp (m - 1) h1⟩
        obtain ⟨h1, h2, h3⟩ := cgUpdate_run A b x₀ m _ _ s.ρ s.x s.r s.p hx hr rfl hdir
        refine ⟨⟨show s.k + 1 = m + 1 by omega, h1, h2, fun i hi => ?_⟩,
          (decide_eq_false (by omega)).symm⟩
        obtain rfl : i = m := by omega
        exact ⟨h3, show s.r ⬝ᵥ s.r = _ by rw [← inner_toLp, hr]⟩

/-- **Algorithm 11.3.3, exact semantics.** For symmetric positive definite `A`, the exact run makes
`k = min(fuel, grade)` steps, `grade` the dimension of the least `A`-invariant subspace containing
`r₀ = b − Ax₀`; its `x` and `r` are the `k`-th backbone CG iterate and residual (the book's `p_k`
being the backbone's `p_{k−1}`, `τ` the backbone's `CG.beta`, `μ` its `CG.alpha`); and when the
loop exits through its test, `Ax = b`. -/
theorem algorithm_11_3_3_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ)
    (fuel : ℕ) :
    let s := Id.run (algorithm_11_3_3 pure A b x₀ fuel)
    let T := toEuclideanLin A
    let r₀ : 𝔼 n := WithLp.toLp 2 b - T (WithLp.toLp 2 x₀)
    s.k = min fuel (Krylov.grade T r₀) ∧
      WithLp.toLp 2 s.x = (CG.iterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) s.k).x ∧
      WithLp.toLp 2 s.r = (CG.iterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) s.k).r ∧
      (s.done = true → A *ᵥ s.x = b) := by
  intro s T r₀
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  obtain ⟨⟨hk, hx, hr, -⟩, hd⟩ := algorithm_11_3_3_inv hA b x₀ fuel
  refine ⟨hk, by rw [hk]; exact hx, by rw [hk]; exact hr, fun hdone => ?_⟩
  have hgf : Krylov.grade (toEuclideanLin A)
      (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)) < fuel :=
    of_decide_eq_true (hd.symm.trans hdone)
  have hr0 := CG.residual_eq_zero_of_grade_le (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) hT
    (k := min fuel (Krylov.grade (toEuclideanLin A)
      (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)))) (by omega)
  have h0 : WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 s.x) = 0 := by
    rw [hx, ← CG.residual_eq, hr0]
  rw [toEuclideanLin_toLp, ← WithLp.toLp_sub, WithLp.toLp_eq_zero, sub_eq_zero] at h0
  exact h0.symm

/-- The state of the practical CG loop (11.3.26): the step count, `x`, `r`, `p`, the current
`ρ_c = rᵀr` and previous `ρ₋`, and the flag of the `while` test. -/
structure PracticalCGState (n : ℕ) where
  /-- The number of completed steps. -/
  k : ℕ
  /-- The iterate `x`. -/
  x : Fin n → ℝ
  /-- The residual `r = b − Ax`. -/
  r : Fin n → ℝ
  /-- The search direction `p`. -/
  p : Fin n → ℝ
  /-- `ρ_c = rᵀr`. -/
  ρc : ℝ
  /-- `ρ₋`, the previous `ρ_c`. -/
  ρm : ℝ
  /-- The `while` test `√ρ_c > δ` has failed. -/
  done : Bool

/-- One pass of the `while` body of (11.3.26): the test `√ρ_c > δ` (the square root rounded), then
`cgUpdate`, `ρ₋ = ρ_c`, `ρ_c = rᵀr`. -/
noncomputable def practicalCGBody (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ)
    (s : PracticalCGState n) : M (PracticalCGState n) :=
  if s.done then pure s else do
    let nrm ← rnd (√s.ρc)
    if nrm ≤ δ then pure { s with done := true } else do
      let o ← cgUpdate rnd A (decide (s.k = 0)) s.ρc s.ρm s.x s.r s.p
      let ρ ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd o.2.1 o.2.1
      pure ⟨s.k + 1, o.1, o.2.1, o.2.2, ρ, s.ρc, false⟩

/-- **(11.3.26)**, the practical version of Algorithm 11.3.3 with the stopping test
`‖r‖₂ ≤ tol · ‖b‖₂`:
```
k = 0, x = x₀, r = b − Ax, ρ_c = rᵀr, δ = tol · ‖b‖₂
while √ρ_c > δ
    k = k + 1
    if k = 1
        p = r
    else
        τ = ρ_c/ρ₋,  p = r + τp
    end
    w = Ap
    μ = ρ_c/pᵀw,  x = x + μp,  r = r − μw,  ρ₋ = ρ_c,  ρ_c = rᵀr
end
```
The arithmetic feeding the test (`‖b‖₂ = √(bᵀb)`, `δ`, `√ρ_c`) is rounded, the comparison exact;
the loop runs at most `fuel` times. -/
noncomputable def practicalCG (rnd : ℝ → M ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (tol : ℝ) (fuel : ℕ) : M (PracticalCGState n) := do
  let r ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A (-x₀) b
  let ρ ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd r r
  let bb ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd b b
  let nb ← rnd (√bb)
  let δ ← rnd (tol * nb)
  (List.range fuel).foldlM (fun s _ => practicalCGBody rnd A δ s) ⟨0, x₀, r, r, ρ, 0, false⟩

/-- The exact run of one pass of the body of (11.3.26). -/
private theorem practicalCGBody_run (A : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ)
    (s : PracticalCGState n) :
    Id.run (practicalCGBody pure A δ s) =
      if s.done then s else if √s.ρc ≤ δ then { s with done := true } else
        ⟨s.k + 1, (Id.run (cgUpdate pure A (decide (s.k = 0)) s.ρc s.ρm s.x s.r s.p)).1,
          (Id.run (cgUpdate pure A (decide (s.k = 0)) s.ρc s.ρm s.x s.r s.p)).2.1,
          (Id.run (cgUpdate pure A (decide (s.k = 0)) s.ρc s.ρm s.x s.r s.p)).2.2,
          (Id.run (cgUpdate pure A (decide (s.k = 0)) s.ρc s.ρm s.x s.r s.p)).2.1 ⬝ᵥ
            (Id.run (cgUpdate pure A (decide (s.k = 0)) s.ρc s.ρm s.x s.r s.p)).2.1,
          s.ρc, false⟩ := by
  unfold practicalCGBody
  by_cases hd : s.done
  · simp only [hd, ↓reduceIte, Id.run_pure]
  · by_cases h0 : √s.ρc ≤ δ
    · simp only [hd, h0, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure]
    · simp only [hd, h0, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure,
        GolubVanLoan.Chapter01.algorithm_1_1_1_spec]

/-- The exact run of (11.3.26) before the loop. -/
private theorem practicalCG_run_zero (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (tol : ℝ) : Id.run (practicalCG pure A b x₀ tol 0) =
      ⟨0, x₀, Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A (-x₀) b),
        Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A (-x₀) b),
        Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A (-x₀) b) ⬝ᵥ
          Id.run (GolubVanLoan.Chapter01.algorithm_1_1_3 pure A (-x₀) b), 0, false⟩ := by
  simp only [practicalCG, Id.run_bind, Id.run_pure, GolubVanLoan.Chapter01.algorithm_1_1_1_spec,
    List.range_zero, List.foldlM_nil]

/-- The exact run of (11.3.26) with one more pass of the loop. -/
private theorem practicalCG_run_succ (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ)
    (tol : ℝ) (m : ℕ) : Id.run (practicalCG pure A b x₀ tol (m + 1)) =
      Id.run (practicalCGBody pure A (tol * √(b ⬝ᵥ b))
        (Id.run (practicalCG pure A b x₀ tol m))) := by
  simp only [practicalCG, Id.run_bind, Id.run_pure, GolubVanLoan.Chapter01.algorithm_1_1_1_spec]
  exact run_foldlM_range_succ _ _ _

/-- The loop invariant of the exact run of (11.3.26), with the threshold `δ`. -/
@[reducible] private def PCGInv (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (δ : ℝ)
    (m : ℕ) (s : PracticalCGState n) : Prop :=
  (WithLp.toLp 2 s.x = (cgIt A b x₀ s.k).x ∧ WithLp.toLp 2 s.r = (cgIt A b x₀ s.k).r ∧
    s.ρc = s.r ⬝ᵥ s.r ∧
    ∀ i, s.k = i + 1 → WithLp.toLp 2 s.p = (cgIt A b x₀ i).p ∧
      s.ρm = ⟪(cgIt A b x₀ i).r, (cgIt A b x₀ i).r⟫) ∧
  s.k ≤ m ∧ (∀ j < s.k, δ < ‖(cgIt A b x₀ j).r‖) ∧
  (s.done = true → ‖(cgIt A b x₀ s.k).r‖ ≤ δ) ∧ (s.done = false → s.k = m)

/-- The exact run of (11.3.26) satisfies the loop invariant `PCGInv`. -/
private theorem practicalCG_inv (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (tol : ℝ)
    (m : ℕ) : PCGInv A b x₀ (tol * √(b ⬝ᵥ b)) m (Id.run (practicalCG pure A b x₀ tol m)) := by
  induction m with
  | zero =>
    rw [practicalCG_run_zero]
    exact ⟨⟨rfl, initial_residual A b x₀, rfl,
        fun i h => absurd (show 0 = i + 1 from h) (by omega)⟩,
      le_rfl, fun j hj => absurd (show j < 0 from hj) (Nat.not_lt_zero j),
      fun h => by simp at h, fun _ => rfl⟩
  | succ m ih =>
    rw [practicalCG_run_succ, practicalCGBody_run]
    set s := Id.run (practicalCG pure A b x₀ tol m)
    obtain ⟨⟨hx, hr, hρc, hp⟩, hkm, hlt, hdone, hnd⟩ := ih
    have hnorm : √s.ρc = ‖(cgIt A b x₀ s.k).r‖ := by rw [hρc, sqrt_dotProduct_self, hr]
    by_cases hd : s.done
    · simp only [hd, ↓reduceIte]
      exact ⟨⟨hx, hr, hρc, hp⟩, hkm.trans (Nat.le_succ m), hlt, hdone,
        fun h => absurd (hd.symm.trans h) (by decide)⟩
    · have hkm' : s.k = m := hnd (by simpa using hd)
      simp only [hd, Bool.false_eq_true, ↓reduceIte]
      by_cases ht : √s.ρc ≤ tol * √(b ⬝ᵥ b)
      · simp only [ht, ↓reduceIte]
        exact ⟨⟨hx, hr, hρc, hp⟩, hkm.trans (Nat.le_succ m), hlt,
          fun _ => by rw [← hnorm]; exact ht, fun h => by simp at h⟩
      · simp only [ht, ↓reduceIte]
        have hdir : (decide (s.k = 0) = true ∧ s.k = 0) ∨ (decide (s.k = 0) = false ∧
            ∃ i, s.k = i + 1 ∧ WithLp.toLp 2 s.p = (cgIt A b x₀ i).p ∧
              s.ρm = ⟪(cgIt A b x₀ i).r, (cgIt A b x₀ i).r⟫) := by
          rcases Nat.eq_zero_or_eq_succ_pred s.k with h0 | h1
          · exact Or.inl ⟨by rw [h0]; rfl, h0⟩
          · exact Or.inr ⟨decide_eq_false (by omega), s.k - 1, h1, hp (s.k - 1) h1⟩
        obtain ⟨h1, h2, h3⟩ := cgUpdate_run A b x₀ s.k _ _ s.ρm s.x s.r s.p hx hr hρc hdir
        refine ⟨⟨h1, h2, rfl, fun i hi => ?_⟩, show s.k + 1 ≤ m + 1 by omega, fun j hj => ?_,
          fun h => by simp at h, fun _ => show s.k + 1 = m + 1 by omega⟩
        · obtain rfl : i = s.k := by
            have hi' : s.k + 1 = i + 1 := hi
            omega
          exact ⟨h3, show s.ρc = _ by rw [hρc, ← inner_toLp, hr]⟩
        · have hj' : j < s.k + 1 := hj
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj | rfl
          · exact hlt j hj
          · rw [← hnorm]; exact lt_of_not_ge ht

/-- **(11.3.26), exact semantics.** The exact run makes `k ≤ fuel` steps; its `x` and `r` are the
`k`-th backbone CG iterate and residual; every earlier residual failed the test
(`‖r_j‖₂ > tol · ‖b‖₂` for `j < k`); fewer than `fuel` steps are made only when the test stopped
the loop; and "on exit by the test", `‖b − Ax‖₂ ≤ tol · ‖b‖₂`. -/
theorem equation_11_3_26 (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (tol : ℝ)
    (fuel : ℕ) :
    let s := Id.run (practicalCG pure A b x₀ tol fuel)
    let T := toEuclideanLin A
    s.k ≤ fuel ∧
      WithLp.toLp 2 s.x = (CG.iterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) s.k).x ∧
      WithLp.toLp 2 s.r = (CG.iterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) s.k).r ∧
      (∀ j < s.k, tol * ‖(WithLp.toLp 2 b : 𝔼 n)‖ <
        ‖(CG.iterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) j).r‖) ∧
      (s.k < fuel → s.done = true) ∧
      (s.done = true →
        ‖(WithLp.toLp 2 (b - A *ᵥ s.x) : 𝔼 n)‖ ≤ tol * ‖(WithLp.toLp 2 b : 𝔼 n)‖) := by
  intro s T
  obtain ⟨⟨hx, hr, -, -⟩, hkm, hlt, hdone, hnd⟩ := practicalCG_inv A b x₀ tol fuel
  rw [sqrt_dotProduct_self] at hlt hdone
  refine ⟨hkm, hx, hr, hlt, fun h => ?_, fun h => ?_⟩
  · cases hd : s.done
    · exact absurd (hnd hd) (Nat.ne_of_lt h)
    · rfl
  · have := hdone h
    rwa [CG.residual_eq, ← hx, toEuclideanLin_toLp, ← WithLp.toLp_sub] at this

end HestenesStiefel

/-! ### §11.3.8: error estimates -/

section Estimates

variable {A : Matrix (Fin n) (Fin n) ℝ}

open scoped Matrix.Norms.L2Operator in
/-- **§11.3.8**, the display after (11.3.26): "if `x_c` is the final iterate and `x_*` is the exact
solution, then `‖x_c − x_*‖ = ‖A⁻¹(b − Ax_c)‖₂ ≤ tol · ‖A⁻¹‖₂‖b‖₂ ≤ tol · κ₂(A)‖x_*‖`", for any
`x_c` with `‖b − Ax_c‖₂ ≤ tol · ‖b‖₂`. -/
theorem cg_relativeError_le (hA : IsUnit A) {b xs xc : 𝔼 n} (hxs : toEuclideanLin A xs = b)
    {tol : ℝ} (htol : 0 ≤ tol) (h : ‖b - toEuclideanLin A xc‖ ≤ tol * ‖b‖) :
    ‖xc - xs‖ ≤ tol * ‖A⁻¹‖ * ‖b‖ ∧ tol * ‖A⁻¹‖ * ‖b‖ ≤ tol * NormedRing.condNumber A * ‖xs‖ := by
  have he : xc - xs = toEuclideanLin A⁻¹ (-(b - toEuclideanLin A xc)) := by
    rw [neg_sub, map_sub, inv_apply_apply hA, ← hxs, inv_apply_apply hA]
  refine ⟨?_, ?_⟩
  · rw [he]
    refine (norm_toEuclideanLin_apply_le _ _).trans ?_
    rw [norm_neg]
    calc ‖A⁻¹‖ * ‖b - toEuclideanLin A xc‖ ≤ ‖A⁻¹‖ * (tol * ‖b‖) :=
          mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = tol * ‖A⁻¹‖ * ‖b‖ := by ring
  · rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse]
    have hb : ‖b‖ ≤ ‖A‖ * ‖xs‖ := by rw [← hxs]; exact norm_toEuclideanLin_apply_le A xs
    calc tol * ‖A⁻¹‖ * ‖b‖ ≤ tol * ‖A⁻¹‖ * (‖A‖ * ‖xs‖) :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg htol (norm_nonneg _))
      _ = tol * (‖A‖ * ‖A⁻¹‖) * ‖xs‖ := by ring

open scoped Matrix.Norms.L2Operator in
/-- **(11.3.27)** (Trefethen–Bau, quoted by the book): the CG iterates of a symmetric positive
definite `A` satisfy `‖x − x_k‖_A ≤ 2‖x − x₀‖_A ((√κ₂(A) − 1)/(√κ₂(A) + 1))^k`. -/
theorem equation_11_3_27 (hA : A.PosDef) {b xs : 𝔼 n} (hxs : toEuclideanLin A xs = b) (x₀ : 𝔼 n)
    (k : ℕ) :
    energyNorm (toEuclideanLin A) (xs - (CG.iterate (toEuclideanLin A) b x₀ k).x) ≤
      2 * energyNorm (toEuclideanLin A) (xs - x₀) *
        ((√(NormedRing.condNumber A) - 1) / (√(NormedRing.condNumber A) + 1)) ^ k := by
  have hT := hA.isSymmetricCoercive_toEuclideanLin
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [eq_zero_of_isEmpty (xs - _), eq_zero_of_isEmpty (xs - x₀)]
    simp [energyNorm]
  obtain ⟨lmin, lmax, hl, hll, hB, hκ⟩ := posDef_bounds hA
  rw [hκ]
  have h := Krylov.IsGalerkinIterate.energyNorm_error_le hl hll hB
    (CG.isGalerkinIterate b x₀ hT k) hxs
  linarith

end Estimates

/-! ### §11.3.9: CG on `AᵀA` and `AAᵀ` -/

section NormalEquations

/-- The adjoint relation of `Cᵀ` and `C` on Euclidean spaces: `⟪Cᵀu, v⟫ = ⟪u, Cv⟫`. -/
private theorem inner_transpose_apply {p q : ℕ} (C : Matrix (Fin p) (Fin q) ℝ) (u : 𝔼 p)
    (v : 𝔼 q) : ⟪toEuclideanLin Cᵀ u, v⟫ = ⟪u, toEuclideanLin C v⟫ := by
  rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose_inner_left]

/-- **§11.3.9**, the two identities: for `A ∈ ℝ^{m×n}`,
"`φ_{AᵀA}(x) = ½ xᵀ(AᵀA)x − xᵀ(Aᵀb) = ½‖Ax − b‖²₂ − ½ bᵀb`"; and for nonsingular square `B`
(the book's `A`), "`φ_{BBᵀ}(y) = ½ yᵀBBᵀy − yᵀc = ½‖Bᵀy − B⁻¹c‖²₂ − ½ cᵀ(BBᵀ)⁻¹c`". -/
theorem energyFunctional_normalEquations {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : 𝔼 m)
    (x : 𝔼 n) :
    energyFunctional (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A) (toEuclideanLin Aᵀ b) x =
        ‖toEuclideanLin A x - b‖ ^ 2 / 2 - ‖b‖ ^ 2 / 2 ∧
      ∀ (B : Matrix (Fin n) (Fin n) ℝ), IsUnit B → ∀ (c y : 𝔼 n),
        energyFunctional (toEuclideanLin B ∘ₗ toEuclideanLin Bᵀ) c y =
          ‖toEuclideanLin Bᵀ y - toEuclideanLin B⁻¹ c‖ ^ 2 / 2 -
            ⟪c, toEuclideanLin (B * Bᵀ)⁻¹ c⟫ / 2 := by
  refine ⟨?_, fun B hB c y => ?_⟩
  · simp only [energyFunctional, RCLike.re_to_real, LinearMap.comp_apply]
    rw [inner_transpose_apply A (toEuclideanLin A x) x, inner_transpose_apply A b x,
      @norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_comm b (toEuclideanLin A x)]
    ring
  · -- with `w = B⁻¹c`: `(BBᵀ)⁻¹c = B⁻ᵀw` and `⟪c, (BBᵀ)⁻¹c⟫ = ‖w‖²`
    have hBT : IsUnit Bᵀ := (isUnit_transpose B).2 hB
    obtain ⟨w, hw⟩ : ∃ w, w = toEuclideanLin B⁻¹ c := ⟨_, rfl⟩
    have hcw : toEuclideanLin B w = c := by rw [hw]; exact apply_inv_apply hB c
    have hinv : toEuclideanLin (B * Bᵀ)⁻¹ c = toEuclideanLin Bᵀ⁻¹ w := by
      rw [hw, Matrix.mul_inv_rev]
      simp only [toEuclideanLin_apply, mulVec_mulVec]
    have hq : ⟪c, toEuclideanLin (B * Bᵀ)⁻¹ c⟫ = ‖w‖ ^ 2 := by
      have h1 := inner_transpose_apply Bᵀ w (toEuclideanLin Bᵀ⁻¹ w)
      rw [transpose_transpose, apply_inv_apply hBT] at h1
      rw [hinv, ← hcw, h1, real_inner_self_eq_norm_sq]
    rw [hq, ← hw]
    simp only [energyFunctional, RCLike.re_to_real, LinearMap.comp_apply]
    rw [real_inner_comm y (toEuclideanLin B (toEuclideanLin Bᵀ y)),
      ← inner_transpose_apply B y (toEuclideanLin Bᵀ y), ← hcw,
      real_inner_comm y (toEuclideanLin B w), ← inner_transpose_apply B y w, @norm_sub_sq_real,
      real_inner_self_eq_norm_sq]
    ring

/-- **(11.3.28)**, CGNR: "if we apply CG to the `AᵀAx = Aᵀb` problem, then at the `k`th step a
vector `x_k` is produced that minimizes `φ_{AᵀA}(x) = ½‖Ax − b‖²₂ − ½bᵀb` over the affine space
`S_k = x₀ + 𝒦(AᵀA, Aᵀr₀, k)`", `r₀ = b − Ax₀`, for nonsingular `A`. -/
theorem equation_11_3_28 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (b x₀ : 𝔼 n) (k : ℕ) :
    IsMinResidual (toEuclideanLin A) b x₀
      (Krylov.subspace (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A)
        (toEuclideanLin Aᵀ (b - toEuclideanLin A x₀)) k)
      (CG.iterate (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A) (toEuclideanLin Aᵀ b) x₀ k).x := by
  have hadj := inner_transpose_apply A
  have hinj : Function.Injective (toEuclideanLin A) := fun u v h => by
    rw [← inv_apply_apply hA u, h, inv_apply_apply hA]
  have hS := Krylov.adjoint_comp_isSymmetricCoercive_of_injective hadj hinj
  exact (Krylov.isGalerkinIterate_adjoint_comp_iff_isMinResidual hadj b x₀ k _).1
    (CG.isGalerkinIterate _ x₀ hS k)

/-- **§11.3.9**, CGNE (Craig's method): "if we apply the CG method to the `y`-problem `AAᵀy = b`,
… setting `x_k = Aᵀy_k`, … `x = x_k` minimizes `‖x − x_*‖₂` over the affine space defined in
(11.3.28)", for nonsingular `A`, `x₀ = Aᵀy₀`. -/
theorem cgne_isMinError {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) {b xs : 𝔼 n}
    (hxs : toEuclideanLin A xs = b) (y₀ : 𝔼 n) (k : ℕ) :
    IsMinError xs (toEuclideanLin Aᵀ y₀)
      (Krylov.subspace (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A)
        (toEuclideanLin Aᵀ (b - toEuclideanLin A (toEuclideanLin Aᵀ y₀))) k)
      (toEuclideanLin Aᵀ (CG.iterate (toEuclideanLin A ∘ₗ toEuclideanLin Aᵀ) b y₀ k).x) := by
  have hadj := inner_transpose_apply A
  have hBT : IsUnit Aᵀ := (isUnit_transpose A).2 hA
  have hinj : Function.Injective (toEuclideanLin Aᵀ) := fun u v h => by
    rw [← inv_apply_apply hBT u, h, inv_apply_apply hBT]
  -- `AAᵀ` is symmetric positive definite: `(Aᵀ)ᵀ = A` is the adjoint of `Aᵀ`
  have hadj' : ∀ u v : 𝔼 n, ⟪toEuclideanLin A u, v⟫ = ⟪u, toEuclideanLin Aᵀ v⟫ := fun u v => by
    have := inner_transpose_apply Aᵀ u v
    rwa [transpose_transpose] at this
  have hS := Krylov.adjoint_comp_isSymmetricCoercive_of_injective hadj' hinj
  have h := Krylov.isMinError_of_isGalerkinIterate_comp_adjoint hadj b (toEuclideanLin Aᵀ y₀)
    rfl hxs (CG.isGalerkinIterate b y₀ hS k)
  rwa [← map_add, add_sub_cancel] at h

variable {M : Type → Type} [Monad M]

/-- The state of the CGNR loop: the iterate `x`, the residual `r = b − Ax`, `z = Aᵀr`, and the
search direction `p`. -/
structure CGNRState (m n : ℕ) where
  /-- The iterate `x_c`. -/
  x : Fin n → ℝ
  /-- The residual `r_c = b − Ax_c`. -/
  r : Fin m → ℝ
  /-- `z_c = Aᵀr_c`. -/
  z : Fin n → ℝ
  /-- The search direction `p_c`. -/
  p : Fin n → ℝ

/-- **Figure 11.3.1, the CGNR column**: "`r_c = b − Ax₀`, `z_c = Aᵀr_c`, `p_c = z_c`" and the
update "`μ = z_cᵀz_c/(Ap_c)ᵀ(Ap_c)`, `x_+ = x_c + μp_c`, `r_+ = r_c − μAp_c`, `z_+ = Aᵀr_+`,
`τ = z_+ᵀz_+/z_cᵀz_c`, `p_+ = z_+ + τp_c`", repeated `fuel` times; `A` may be rectangular. -/
noncomputable def cgnr {m : ℕ} (rnd : ℝ → M ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x₀ : Fin n → ℝ) (fuel : ℕ) : M (CGNRState m n) := do
  let r ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A (-x₀) b
  let z ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd Aᵀ r 0
  (List.range fuel).foldlM (fun s _ => do
    let Ap ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A s.p 0
    let zz ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd s.z s.z
    let ApAp ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd Ap Ap
    let μ ← rnd (zz / ApAp)
    let x ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd μ s.p s.x
    let r ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd (-μ) Ap s.r
    let z ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd Aᵀ r 0
    let zz' ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd z z
    let τ ← rnd (zz' / zz)
    let p ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd τ s.p z
    pure (⟨x, r, z, p⟩ : CGNRState m n)) ⟨x₀, r, z, z⟩

/-- One exact CGNR step. -/
private noncomputable def cgnrStep {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s : CGNRState m n) :
    CGNRState m n :=
  ⟨s.x + (s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p))) • s.p,
    s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p),
    Aᵀ *ᵥ (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p)),
    Aᵀ *ᵥ (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p)) +
      ((Aᵀ *ᵥ (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p))) ⬝ᵥ
          (Aᵀ *ᵥ (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p))) /
        (s.z ⬝ᵥ s.z)) • s.p⟩

/-- The exact run of the CGNR loop before any step. -/
private theorem cgnr_run_zero {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x₀ : Fin n → ℝ) : Id.run (cgnr pure A b x₀ 0) =
      ⟨x₀, b - A *ᵥ x₀, Aᵀ *ᵥ (b - A *ᵥ x₀), Aᵀ *ᵥ (b - A *ᵥ x₀)⟩ := by
  simp only [cgnr, Id.run_bind, GolubVanLoan.Chapter01.algorithm_1_1_3_spec, List.range_zero,
    List.foldlM_nil, Id.run_pure, zero_add, mulVec_neg, ← sub_eq_add_neg]

/-- The exact run of the CGNR loop with one more step. -/
private theorem cgnr_run_succ {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x₀ : Fin n → ℝ) (k : ℕ) :
    Id.run (cgnr pure A b x₀ (k + 1)) = cgnrStep A (Id.run (cgnr pure A b x₀ k)) := by
  simp only [cgnr, Id.run_bind]
  rw [run_foldlM_range_succ]
  simp only [Id.run_bind, Id.run_pure, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
    GolubVanLoan.Chapter01.algorithm_1_1_1_spec, GolubVanLoan.Chapter01.algorithm_1_1_2_spec,
    zero_add, cgnrStep]

/-- **Figure 11.3.1, CGNR, exact semantics** (square `A`): after `k` passes the state is the
backbone's `Krylov.CGNR.iterate` (one product with `A` and one with `Aᵀ` per step) with `z = Aᵀr`;
so its iterates are CG on the normal equations, those of (11.3.28). -/
theorem cgnr_spec (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (k : ℕ) :
    let s := Id.run (cgnr pure A b x₀ k)
    let it := Krylov.CGNR.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
      (WithLp.toLp 2 x₀) k
    WithLp.toLp 2 s.x = it.x ∧ WithLp.toLp 2 s.r = it.r ∧ WithLp.toLp 2 s.p = it.p ∧
      s.z = Aᵀ *ᵥ s.r := by
  induction k with
  | zero =>
    rw [cgnr_run_zero]
    exact ⟨rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨hx, hr, hp, hz⟩ := ih
    rw [cgnr_run_succ]
    intro s' it'
    simp only [s', it']
    set s := Id.run (cgnr pure A b x₀ k)
    set it := Krylov.CGNR.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
      (WithLp.toLp 2 x₀) k
    have hAr : toEuclideanLin Aᵀ it.r = WithLp.toLp 2 s.z := by
      rw [← hr, toEuclideanLin_toLp, hz]
    have hAp : toEuclideanLin A it.p = WithLp.toLp 2 (A *ᵥ s.p) := by
      rw [← hp, toEuclideanLin_toLp]
    have halpha : s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)) =
        Krylov.CGNR.alpha (toEuclideanLin A) (toEuclideanLin Aᵀ) it := by
      rw [Krylov.CGNR.alpha, hAr, hAp, inner_toLp, inner_toLp]
    have hr' : WithLp.toLp 2
        (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p)) =
        (Krylov.CGNR.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
          (WithLp.toLp 2 x₀) (k + 1)).r := by
      rw [Krylov.CGNR.iterate_succ, Krylov.CGNR.step_r, ← halpha, hAp, ← hr, neg_smul,
        ← sub_eq_add_neg, WithLp.toLp_sub, WithLp.toLp_smul]
    refine ⟨?_, hr', ?_, rfl⟩
    · change WithLp.toLp 2 (s.x + (s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p))) • s.p) = _
      rw [Krylov.CGNR.iterate_succ, Krylov.CGNR.step_x, ← halpha, ← hx, ← hp, WithLp.toLp_add,
        WithLp.toLp_smul]
    · change WithLp.toLp 2
        (Aᵀ *ᵥ (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p)) +
          ((Aᵀ *ᵥ (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p))) ⬝ᵥ
              (Aᵀ *ᵥ (s.r + (-(s.z ⬝ᵥ s.z / ((A *ᵥ s.p) ⬝ᵥ (A *ᵥ s.p)))) • (A *ᵥ s.p))) /
            (s.z ⬝ᵥ s.z)) • s.p) = _
      rw [Krylov.CGNR.iterate_succ, Krylov.CGNR.step_p, Krylov.CGNR.beta,
        ← Krylov.CGNR.iterate_succ, ← hr', hAr, toEuclideanLin_toLp, inner_toLp, inner_toLp,
        ← hp, WithLp.toLp_add, WithLp.toLp_smul]

/-- The state of the CGNE loop: the iterate `x`, the residual `r = b − Ax`, and the search direction
`p`. -/
structure CGNEState (m n : ℕ) where
  /-- The iterate `x_c`. -/
  x : Fin n → ℝ
  /-- The residual `r_c = b − Ax_c`. -/
  r : Fin m → ℝ
  /-- The search direction `p_c`. -/
  p : Fin n → ℝ

/-- **Figure 11.3.1, the CGNE column**: "`r_c = b − Ax_c`, `p_c = Aᵀr_c`" and the update
"`μ = r_cᵀr_c/p_cᵀp_c`, `x_+ = x_c + μp_c`, `r_+ = r_c − μAp_c`, `τ = r_+ᵀr_+/r_cᵀr_c`,
`p_+ = Aᵀr_+ + τp_c`", repeated `fuel` times; `A` may be rectangular. -/
noncomputable def cgne {m : ℕ} (rnd : ℝ → M ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x₀ : Fin n → ℝ) (fuel : ℕ) : M (CGNEState m n) := do
  let r ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A (-x₀) b
  let p ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd Aᵀ r 0
  (List.range fuel).foldlM (fun s _ => do
    let rr ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd s.r s.r
    let pp ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd s.p s.p
    let μ ← rnd (rr / pp)
    let x ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd μ s.p s.x
    let Ap ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A s.p 0
    let r ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd (-μ) Ap s.r
    let rr' ← GolubVanLoan.Chapter01.algorithm_1_1_1 rnd r r
    let τ ← rnd (rr' / rr)
    let Atr ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd Aᵀ r 0
    let p ← GolubVanLoan.Chapter01.algorithm_1_1_2 rnd τ s.p Atr
    pure (⟨x, r, p⟩ : CGNEState m n)) ⟨x₀, r, p⟩

/-- One exact CGNE step. -/
private noncomputable def cgneStep {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s : CGNEState m n) :
    CGNEState m n :=
  ⟨s.x + (s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p)) • s.p,
    s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p),
    Aᵀ *ᵥ (s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p)) +
      ((s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p)) ⬝ᵥ
          (s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p)) / (s.r ⬝ᵥ s.r)) • s.p⟩

/-- The exact run of the CGNE loop before any step. -/
private theorem cgne_run_zero {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x₀ : Fin n → ℝ) : Id.run (cgne pure A b x₀ 0) =
      ⟨x₀, b - A *ᵥ x₀, Aᵀ *ᵥ (b - A *ᵥ x₀)⟩ := by
  simp only [cgne, Id.run_bind, GolubVanLoan.Chapter01.algorithm_1_1_3_spec, List.range_zero,
    List.foldlM_nil, Id.run_pure, zero_add, mulVec_neg, ← sub_eq_add_neg]

/-- The exact run of the CGNE loop with one more step. -/
private theorem cgne_run_succ {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x₀ : Fin n → ℝ) (k : ℕ) :
    Id.run (cgne pure A b x₀ (k + 1)) = cgneStep A (Id.run (cgne pure A b x₀ k)) := by
  simp only [cgne, Id.run_bind]
  rw [run_foldlM_range_succ]
  simp only [Id.run_bind, Id.run_pure, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
    GolubVanLoan.Chapter01.algorithm_1_1_1_spec, GolubVanLoan.Chapter01.algorithm_1_1_2_spec,
    zero_add, cgneStep]

/-- **Figure 11.3.1, CGNE, exact semantics** (square `A`): after `k` passes the state is the
backbone's `Krylov.CGNE.iterate`, which is `Aᵀ` of CG on `AAᵀy = b` (`Krylov.CGNE.iterate_eq`); so
for consistent `Ax = b` its iterates are those of `cgne_isMinError`. -/
theorem cgne_spec (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (k : ℕ) :
    let s := Id.run (cgne pure A b x₀ k)
    let it := Krylov.CGNE.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
      (WithLp.toLp 2 x₀) k
    WithLp.toLp 2 s.x = it.x ∧ WithLp.toLp 2 s.r = it.r ∧ WithLp.toLp 2 s.p = it.p := by
  induction k with
  | zero =>
    rw [cgne_run_zero]
    exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨hx, hr, hp⟩ := ih
    rw [cgne_run_succ]
    intro s' it'
    simp only [s', it']
    set s := Id.run (cgne pure A b x₀ k)
    set it := Krylov.CGNE.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
      (WithLp.toLp 2 x₀) k
    have halpha : s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p) = (Krylov.CGNE.alpha it : ℝ) := by
      rw [Krylov.CGNE.alpha, ← hr, ← hp, inner_toLp, inner_toLp]
    have hAp : toEuclideanLin A it.p = WithLp.toLp 2 (A *ᵥ s.p) := by
      rw [← hp, toEuclideanLin_toLp]
    have hr' : WithLp.toLp 2 (s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p)) =
        (Krylov.CGNE.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
          (WithLp.toLp 2 x₀) (k + 1)).r := by
      rw [Krylov.CGNE.iterate_succ, Krylov.CGNE.step_r, ← halpha, hAp, ← hr, neg_smul,
        ← sub_eq_add_neg, WithLp.toLp_sub, WithLp.toLp_smul]
    refine ⟨?_, hr', ?_⟩
    · change WithLp.toLp 2 (s.x + (s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p)) • s.p) = _
      rw [Krylov.CGNE.iterate_succ, Krylov.CGNE.step_x, ← halpha, ← hx, ← hp, WithLp.toLp_add,
        WithLp.toLp_smul]
    · change WithLp.toLp 2
        (Aᵀ *ᵥ (s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p)) +
          ((s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p)) ⬝ᵥ
              (s.r + (-(s.r ⬝ᵥ s.r / (s.p ⬝ᵥ s.p))) • (A *ᵥ s.p)) / (s.r ⬝ᵥ s.r)) • s.p) = _
      rw [Krylov.CGNE.iterate_succ, Krylov.CGNE.step_p, Krylov.CGNE.beta,
        ← Krylov.CGNE.iterate_succ, ← hr', ← hr, inner_toLp, inner_toLp, toEuclideanLin_toLp,
        ← hp, WithLp.toLp_add, WithLp.toLp_smul]

end NormalEquations

end GolubVanLoan.Chapter11
