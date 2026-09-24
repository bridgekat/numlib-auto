import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Projection.Angle
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Eigen.MinMax
import Numlib.Eigen.Normal
import Numlib.Eigen.PowerMethod
import Numlib.LinearAlgebra.Matrix.HermitianPart
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Topology.Algebra.Polynomial

/-!
# Eigenvalue perturbation and a posteriori bounds

Residual bounds for approximate eigenpairs of symmetric operators ([saad2011numerical], Cor 3.3,
Lemma 3.2, Thm 3.8–3.9 for Kato–Temple; [meurant2006lanczos] §2.1; [choi2006iterative] §2.4),
Bauer–Fike for diagonalizable matrices ([saad2011numerical], Thm 3.6; [kress1998numerical] Problem
7.6), the backward error of an approximate eigenpair ([saad2011numerical], Prop 3.4), Bendixson
([saad2003iterative], Thm 1.35), the Gershgorin discs with their counting theorem
([saad2011numerical], Thm 3.11–3.12) and Rayleigh-quotient bounds.

Throughout, an approximate eigenpair of `A` is a unit vector `x` together with a scalar `θ` (usually
the Rayleigh quotient `θ = re⟪A x, x⟫`), and `r = A x - θ x` is its residual; the bounds below turn
`‖r‖` into a distance from `θ` to the spectrum.

## The eigenvector and the condition numbers

`LinearMap.IsSymmetric.sin_angle_le_norm_residual_div` is the residual bound for the eigen*vector*
([saad2011numerical], Thm 3.9): a small residual and a separated eigenvalue force a small angle
between `x` and the eigenspace.  The subspace really has to be the eigenspace and not the line
through a single eigenvector, which is what the printed statement uses; the two agree exactly when
the eigenvalue is simple, and that case is
`LinearMap.IsSymmetric.sin_angle_span_singleton_le_norm_residual_div`.  The theorem's doc comment
carries the three-by-three counterexample to the line form at a multiple eigenvalue.

`Module.End.eigenvalueCondNumber` is the sensitivity of a simple eigenvalue ([saad2011numerical],
Def 3.1), the reciprocal cosine of the angle between the right and the left eigenvector.  It is at
least one, it is one for a normal operator, and it is what bounds the first-order motion of the
eigenvalue under a perturbation: `Module.End.deriv_eigenvalue_perturbation` computes the derivative
of a differentiable branch of eigenvalues of `A + t B` as `⟪w, B u⟫ / ⟪w, u⟫`, and
`Module.End.norm_deriv_eigenvalue_perturbation_le` bounds it by `‖B‖` times the condition number.
`Module.End.hasDerivAt_eigenvalue_perturbation` produces the branch, for a simple eigenvalue: the
inverse function theorem applied to `(t, μ, z) ↦ (t, ⟪w, z⟫, A z + t B z - μ z)`, whose derivative
is injective exactly because the eigenvalue is simple.  No determinant and no implicit function
theorem are involved.

The `ε`-pseudospectra, open (`ContinuousLinearMap.pseudospectrum`) and closed
(`ContinuousLinearMap.closedPseudospectrum`), live in `Numlib/Eigen/Pseudospectrum.lean`.

## Non-diagonalizable matrices and approximate invariant subspaces

`Matrix.one_le_norm_mul_of_mem_spectrum_add` (and its `p`-norm twin) is the resolvent step shared
by the eigenvalue perturbation bounds of [golub2013matrix] §7.2: an eigenvalue `μ` of `A + E` that
is not one of `A` has `‖(μ I - A)⁻¹ E‖ ≥ 1`. `Matrix.infDist_spectrum_le_of_schur` is
[golub2013matrix] Theorem 7.2.3, the Henrici-type bound for a matrix that need not be
diagonalizable: from a Schur form `Qᴴ A Q = D + N`, the distance from `μ` to the diagonal of `D` is
at most `max θ θ^{1/p}`, `θ = ‖E‖₂ ∑_{k<p} ‖N‖₂^k`, where `p` is the nilpotency index of the
entrywise absolute value `|N|`. `Matrix.IsHermitian.exists_mem_spectrum_abs_sub_le_of_mul_sub_mul`
is the block form of the residual bound ([golub2013matrix] Theorem 8.1.13, with constant `1`): an
orthonormal block `Q₁` and a Hermitian `S` with `‖A Q₁ - Q₁ S‖₂ ≤ ε` put an eigenvalue of `A`
within `ε` of every eigenvalue of `S`.

## The Gershgorin discs and how many eigenvalues each group of them holds

`Matrix.spectrum_subset_iUnion_closedBall` and its column-sum twin place the spectrum in the union
of the discs ([saad2011numerical], Thm 3.11), and `Matrix.card_spectrum_of_disjoint_gershgorin`
counts ([saad2011numerical], Thm 3.12): a union `S` of `m` discs that is disjoint from the other
discs contains exactly `m` eigenvalues with multiplicity, and
`Matrix.card_spectrum_of_isolated_gershgorin` is the case `m = 1` that is used in practice.  The
count is `Polynomial.countRootsIn S A.charpoly`, the number of roots of the characteristic
polynomial in `S` with multiplicity.

The proof is the homotopy `A t = D + t H` of the book, whose "continuity argument" is
`Polynomial.countRootsIn_eq_of_preconnected` in `Numlib/Topology/Algebra/Polynomial.lean`: the
number of roots of a monic polynomial in a compact set is constant along a connected family, as
long as the roots stay in the union of two disjoint compact sets.  That is a compactness argument
in the coefficients rather than Rouché's theorem, which is what lets `S` be a union of overlapping
discs instead of something with a contour around it.

Two books by [saad2011numerical] are cited in this file and are kept apart by their short titles:
*Large Eigenvalue Problems* and *Iterative Methods*.  Bauer–Fike, Gershgorin, Kato–Temple and
Bendixson are the classical names of the results; the numbered forms used here are the ones proved
in the cited texts.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The sine of the angle depends only on the subspace, so two spellings of the same subspace give
the same value even when their `HasOrthogonalProjection` instances are found by different routes.
Rewriting a subspace under `sinAngle` directly fails, the instance argument depending on it. This is
the twin of `Submodule.tanAngle_congr`. -/
theorem Submodule.sinAngle_congr {K L : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (h : K = L) (u : E) : K.sinAngle u = L.sinAngle u := by
  subst h
  rfl

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
include hA

/-! ### Diagonalization bookkeeping

All the symmetric bounds below are inequalities between the sums `∑ i, f (λ i) ‖⟪v i, x⟫‖²` over an
orthonormal eigenbasis `v` with eigenvalues `λ`. -/

private theorem repr_sub_smul {n : ℕ} (hn : Module.finrank 𝕜 E = n) (θ : ℝ) (x : E) (i : Fin n) :
    (hA.eigenvectorBasis hn).repr (A x - (θ : 𝕜) • x) i =
      ((hA.eigenvalues hn i - θ : ℝ) : 𝕜) * (hA.eigenvectorBasis hn).repr x i := by
  rw [map_sub, PiLp.sub_apply, map_smul, PiLp.smul_apply, smul_eq_mul,
    hA.eigenvectorBasis_apply_self_apply hn]
  push_cast
  ring

private theorem norm_residual_sq {n : ℕ} (hn : Module.finrank 𝕜 E = n) (θ : ℝ) (x : E) :
    ‖A x - (θ : 𝕜) • x‖ ^ 2 =
      ∑ i, (hA.eigenvalues hn i - θ) ^ 2 * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  rw [hA.norm_sq_eq_sum_norm_repr_sq hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA.repr_sub_smul hn, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]

/-- The identity behind [saad2011numerical], Lemma 3.2 and the Kato–Temple bounds: for a unit vector
`x` with Rayleigh quotient `θ = re⟪A x, x⟫`, residual `r = A x - θ x` and eigenbasis coefficients
`c`, `∑ (λ - u)(λ - v) ‖c‖² = ‖r‖² + (θ - u)(θ - v)`. -/
private theorem sum_quadratic {n : ℕ} (hn : Module.finrank 𝕜 E = n) {x : E} (hx : ‖x‖ = 1)
    (u v : ℝ) :
    ∑ i, (hA.eigenvalues hn i - u) * (hA.eigenvalues hn i - v) *
        ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 =
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 +
        (RCLike.re (inner 𝕜 (A x) x) - u) * (RCLike.re (inner 𝕜 (A x) x) - v) := by
  set θ := RCLike.re (inner 𝕜 (A x) x) with hθ
  have hs : ∑ i, ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 = 1 := by
    rw [← hA.norm_sq_eq_sum_norm_repr_sq hn, hx, one_pow]
  have hth : ∑ i, hA.eigenvalues hn i * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 = θ :=
    (hA.re_inner_apply_self_eq_sum hn x).symm
  have hr : ‖A x - (θ : 𝕜) • x‖ ^ 2 =
      ∑ i, (hA.eigenvalues hn i - θ) ^ 2 * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 :=
    hA.norm_residual_sq hn θ x
  have hsplit : ∀ i : Fin n,
      (hA.eigenvalues hn i - u) * (hA.eigenvalues hn i - v) *
          ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 =
        (hA.eigenvalues hn i - θ) ^ 2 * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 +
          (2 * θ - u - v) * (hA.eigenvalues hn i * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2) +
          (u * v - θ ^ 2) * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 := fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hs, hth, ← hr]
  ring

private theorem quadratic_nonneg {n : ℕ} (hn : Module.finrank 𝕜 E = n) {x : E} (hx : ‖x‖ = 1)
    (u v : ℝ) (h : ∀ i, 0 ≤ (hA.eigenvalues hn i - u) * (hA.eigenvalues hn i - v)) :
    0 ≤ ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 +
      (RCLike.re (inner 𝕜 (A x) x) - u) * (RCLike.re (inner 𝕜 (A x) x) - v) := by
  rw [← hA.sum_quadratic hn hx u v]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (h i) (sq_nonneg _)

/-- Residual bound ([saad2011numerical], Cor 3.3): some eigenvalue lies within `‖A x - θ x‖ / ‖x‖`
of `θ`. -/
theorem exists_hasEigenvalue_dist_le (θ : ℝ) {x : E} (hx : x ≠ 0) :
    ∃ μ : 𝕜, Module.End.HasEigenvalue A μ ∧ ‖μ - (θ : 𝕜)‖ ≤ ‖A x - (θ : 𝕜) • x‖ / ‖x‖ := by
  set n := Module.finrank 𝕜 E with hn'
  have hn : Module.finrank 𝕜 E = n := rfl
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · have : Subsingleton E := Module.finrank_zero_iff.mp (hn'.symm.trans h)
      exact absurd (Subsingleton.elim x 0) hx
    · exact h
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ
    (fun i => |hA.eigenvalues hn i - θ|) ⟨⟨0, hn0⟩, Finset.mem_univ _⟩
  refine ⟨(hA.eigenvalues hn i₀ : 𝕜), hA.hasEigenvalue_eigenvalues hn i₀, ?_⟩
  have hnorm : ‖((hA.eigenvalues hn i₀ : ℝ) : 𝕜) - (θ : 𝕜)‖ = |hA.eigenvalues hn i₀ - θ| := by
    rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]
  rw [hnorm, le_div_iff₀ (norm_pos_iff.mpr hx)]
  have key : (|hA.eigenvalues hn i₀ - θ| * ‖x‖) ^ 2 ≤ ‖A x - (θ : 𝕜) • x‖ ^ 2 := by
    rw [mul_pow, sq_abs, hA.norm_sq_eq_sum_norm_repr_sq hn, hA.norm_residual_sq hn,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have habs := hi₀ i (Finset.mem_univ i)
    nlinarith [abs_nonneg (hA.eigenvalues hn i₀ - θ), abs_nonneg (hA.eigenvalues hn i - θ),
      sq_abs (hA.eigenvalues hn i₀ - θ), sq_abs (hA.eigenvalues hn i - θ)]
  exact le_of_sq_le_sq key (norm_nonneg _)

/-- [saad2011numerical], Lemma 3.2: with `θ = re⟪A x, x⟫` (`‖x‖ = 1`) and an interval `(α, β) ∋ θ`
free of eigenvalues, `(β - θ)(θ - α) ≤ ‖r‖²` for the residual `r = A x - θ x`. -/
theorem rayleigh_gap_le_norm_residual_sq {x : E} (hx : ‖x‖ = 1) {α β : ℝ}
    (hαβ : α < RCLike.re (inner 𝕜 (A x) x) ∧ RCLike.re (inner 𝕜 (A x) x) < β)
    (hfree : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∉ Set.Ioo α β) :
    (β - RCLike.re (inner 𝕜 (A x) x)) * (RCLike.re (inner 𝕜 (A x) x) - α) ≤
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 := by
  set n := Module.finrank 𝕜 E
  have hn : Module.finrank 𝕜 E = n := rfl
  have hout : ∀ i : Fin n, hA.eigenvalues hn i ≤ α ∨ β ≤ hA.eigenvalues hn i := by
    intro i
    have hfi := hfree ((hA.eigenvalues hn i : ℝ) : 𝕜) (hA.hasEigenvalue_eigenvalues hn i)
    rwa [RCLike.ofReal_re, Set.mem_Ioo, not_and_or, not_lt, not_lt] at hfi
  have hab1 := hαβ.1
  have hab2 := hαβ.2
  have h := hA.quadratic_nonneg hn hx α β fun i => by
    rcases hout i with h | h
    · have h1 : hA.eigenvalues hn i - α ≤ 0 := by linarith
      have h2 : hA.eigenvalues hn i - β ≤ 0 := by linarith
      nlinarith
    · exact mul_nonneg (by linarith) (by linarith)
  nlinarith [h]

-- `hμ` says that `μ` is an eigenvalue, which is what makes this Kato–Temple and is part of the
-- stated interface; the proof does not use it, because `hunique` and `hμab` already force every
-- eigenvalue in `(a, b)` to be `μ` and the estimate then holds for `re μ` whether or not `μ` is
-- one. Keeping it makes the statement faithful, and it is what the caller
-- `abs_sub_rayleigh_le_norm_residual_sq_div` has to hand anyway.
set_option linter.unusedVariables false in
/-- Kato–Temple ([saad2011numerical], Thm 3.8): if `(a, b)` contains the Rayleigh quotient `θ = re⟪A
x, x⟫` of a unit vector `x` and exactly one eigenvalue `λ`, then `-‖r‖²/(b - θ) ≤ λ - θ ≤ ‖r‖²/(θ -
a)` for the residual `r = A x - θ x`.

The denominators here are the ones the proof produces: the *lower* bound is controlled by the
distance from `θ` to the right end `b`, and the *upper* bound by the distance to the left end `a`.
Exchanging the two denominators gives a false statement: for `A = diag(0, 10)` and `x` with `‖x‖ =
1`, `x₂² = 3/5`, one gets `θ = 6`, `‖r‖² = 24`, and `(a, b) = (5, 20)` contains only the eigenvalue
`10`, yet `10 - 6 = 4 > 24/(20 - 6)`. -/
theorem kato_temple {x : E} (hx : ‖x‖ = 1) {a b : ℝ} {μ : 𝕜} (hμ : Module.End.HasEigenvalue A μ)
    (hab : a < RCLike.re (inner 𝕜 (A x) x) ∧ RCLike.re (inner 𝕜 (A x) x) < b)
    (hμab : RCLike.re μ ∈ Set.Ioo a b)
    (hunique : ∀ μ' : 𝕜, Module.End.HasEigenvalue A μ' → RCLike.re μ' ∈ Set.Ioo a b → μ' = μ) :
    -(‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 / (b - RCLike.re (inner 𝕜 (A x) x))) ≤
        RCLike.re μ - RCLike.re (inner 𝕜 (A x) x) ∧
      RCLike.re μ - RCLike.re (inner 𝕜 (A x) x) ≤
        ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 /
          (RCLike.re (inner 𝕜 (A x) x) - a) := by
  set n := Module.finrank 𝕜 E
  have hn : Module.finrank 𝕜 E = n := rfl
  set θ := RCLike.re (inner 𝕜 (A x) x) with hθ
  obtain ⟨hab1, hab2⟩ := hab
  obtain ⟨hμa, hμb⟩ := Set.mem_Ioo.mp hμab
  -- every eigenvalue is either `re μ` or outside `(a, b)`
  have hout : ∀ i : Fin n, hA.eigenvalues hn i = RCLike.re μ ∨
      (hA.eigenvalues hn i ≤ a ∨ b ≤ hA.eigenvalues hn i) := by
    intro i
    by_cases hin : a < hA.eigenvalues hn i ∧ hA.eigenvalues hn i < b
    · left
      have heq := hunique ((hA.eigenvalues hn i : ℝ) : 𝕜) (hA.hasEigenvalue_eigenvalues hn i)
        (by rw [RCLike.ofReal_re, Set.mem_Ioo]; exact hin)
      rw [← heq, RCLike.ofReal_re]
    · right
      rwa [not_and_or, not_lt, not_lt] at hin
  constructor
  · have h := hA.quadratic_nonneg hn hx (RCLike.re μ) b fun i => by
      rcases hout i with h | h | h
      · rw [h]; simp
      · have h1 : hA.eigenvalues hn i - RCLike.re μ ≤ 0 := by linarith
        have h2 : hA.eigenvalues hn i - b ≤ 0 := by linarith
        nlinarith
      · exact mul_nonneg (by linarith) (by linarith)
    rw [← hθ] at h
    rw [neg_le, le_div_iff₀ (by linarith : (0 : ℝ) < b - θ)]
    nlinarith [h]
  · have h := hA.quadratic_nonneg hn hx (RCLike.re μ) a fun i => by
      rcases hout i with h | h | h
      · rw [h]; simp
      · have h1 : hA.eigenvalues hn i - RCLike.re μ ≤ 0 := by linarith
        have h2 : hA.eigenvalues hn i - a ≤ 0 := by linarith
        nlinarith
      · exact mul_nonneg (by linarith) (by linarith)
    rw [← hθ] at h
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < θ - a)]
    nlinarith [h]

/-- [saad2011numerical], Cor 3.4: `|λ - θ| ≤ ‖r‖² / δ`, where `θ = re⟪A x, x⟫` is the Rayleigh
quotient of a unit vector `x`, `r = A x - θ x` its residual, and `δ` the gap from `θ` to the
eigenvalues other than `λ`. -/
theorem abs_sub_rayleigh_le_norm_residual_sq_div {x : E} (hx : ‖x‖ = 1) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue A μ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ μ' : 𝕜, Module.End.HasEigenvalue A μ' → μ' ≠ μ →
      δ ≤ |RCLike.re μ' - RCLike.re (inner 𝕜 (A x) x)|)
    (hclose : |RCLike.re μ - RCLike.re (inner 𝕜 (A x) x)| ≤
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖) :
    |RCLike.re μ - RCLike.re (inner 𝕜 (A x) x)| ≤
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 / δ := by
  set θ := RCLike.re (inner 𝕜 (A x) x) with hθ
  by_cases hlt : |RCLike.re μ - θ| < δ
  · obtain ⟨hlt1, hlt2⟩ := abs_lt.mp hlt
    have hunique : ∀ μ' : 𝕜, Module.End.HasEigenvalue A μ' →
        RCLike.re μ' ∈ Set.Ioo (θ - δ) (θ + δ) → μ' = μ := by
      intro μ' h1 h2
      by_contra hne
      have hg := hgap μ' h1 hne
      obtain ⟨h21, h22⟩ := Set.mem_Ioo.mp h2
      have hcon : |RCLike.re μ' - θ| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith
    obtain ⟨h1, h2⟩ := hA.kato_temple hx hμ ⟨by linarith, by linarith⟩
      (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩) hunique
    rw [← hθ] at h1 h2
    rw [show θ + δ - θ = δ from by ring] at h1
    rw [show θ - (θ - δ) = δ from by ring] at h2
    exact abs_le.mpr ⟨by linarith, h2⟩
  · rw [not_lt] at hlt
    rw [le_div_iff₀ hδ]
    calc |RCLike.re μ - θ| * δ ≤ ‖A x - (θ : 𝕜) • x‖ * ‖A x - (θ : 𝕜) • x‖ :=
          mul_le_mul hclose (hlt.trans hclose) hδ.le (norm_nonneg _)
      _ = ‖A x - (θ : 𝕜) • x‖ ^ 2 := (sq _).symm

/-- Rayleigh quotient bounds: `λmin ≤ re⟪A x, x⟫ / ‖x‖² ≤ λmax`. -/
theorem rayleigh_mem_Icc {lmin lmax : ℝ}
    (hspec : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∈ Set.Icc lmin lmax) {x : E}
    (hx : x ≠ 0) : RCLike.re (inner 𝕜 (A x) x) / ‖x‖ ^ 2 ∈ Set.Icc lmin lmax := by
  set n := Module.finrank 𝕜 E
  have hn : Module.finrank 𝕜 E = n := rfl
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  have hbounds : ∀ i : Fin n, hA.eigenvalues hn i ∈ Set.Icc lmin lmax := by
    intro i
    have := hspec ((hA.eigenvalues hn i : ℝ) : 𝕜) (hA.hasEigenvalue_eigenvalues hn i)
    rwa [RCLike.ofReal_re] at this
  rw [Set.mem_Icc]
  constructor
  · rw [le_div_iff₀ hpos, hA.re_inner_apply_self_eq_sum hn, hA.norm_sq_eq_sum_norm_repr_sq hn,
      Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hbounds i).1 (sq_nonneg _)
  · rw [div_le_iff₀ hpos, hA.re_inner_apply_self_eq_sum hn, hA.norm_sq_eq_sum_norm_repr_sq hn,
      Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hbounds i).2 (sq_nonneg _)

/-! ### The eigenvector residual bound

A small residual forces the approximate eigenvector to be close to an eigenspace, provided the
corresponding eigenvalue is separated from the rest of the spectrum. -/

/-- On the orthogonal complement of the `lam`-eigenspace the shifted operator `A - θ` is bounded
below by the separation `δ` of `lam` from the other eigenvalues: `δ ‖q‖ ≤ ‖(A - θ) q‖`.

In the eigenvector basis the coordinates of `q` vanish at every index whose eigenvalue is `lam`, so
the sum defining `‖(A - θ) q‖²` runs only over the indices where the separation applies. -/
private theorem mul_norm_le_norm_sub_smul_of_mem_orthogonal {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) {lam θ δ : ℝ} (hδ : 0 ≤ δ)
    (hsep : ∀ i, hA.eigenvalues hn i ≠ lam → δ ≤ |hA.eigenvalues hn i - θ|)
    {q : E} (hq : q ∈ (Module.End.eigenspace A (lam : 𝕜))ᗮ) :
    δ * ‖q‖ ≤ ‖A q - (θ : 𝕜) • q‖ := by
  have hzero : ∀ i, hA.eigenvalues hn i = lam → (hA.eigenvectorBasis hn).repr q i = 0 := by
    intro i hi
    have hmem : hA.eigenvectorBasis hn i ∈ Module.End.eigenspace A (lam : 𝕜) :=
      Module.End.mem_eigenspace_iff.2 (by rw [hA.apply_eigenvectorBasis hn, hi])
    rw [OrthonormalBasis.repr_apply_apply]
    exact (Submodule.mem_orthogonal _ q).1 hq _ hmem
  have hsq : (δ * ‖q‖) ^ 2 ≤ ‖A q - (θ : 𝕜) • q‖ ^ 2 := by
    rw [mul_pow, hA.norm_residual_sq hn θ q, hA.norm_sq_eq_sum_norm_repr_sq hn q, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : hA.eigenvalues hn i = lam
    · rw [hzero i hi]
      simp
    · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have h := hsep i hi
      nlinarith [sq_abs (hA.eigenvalues hn i - θ), abs_nonneg (hA.eigenvalues hn i - θ)]
  exact le_of_sq_le_sq hsq (norm_nonneg _)

/-- **The eigenvector residual bound** ([saad2011numerical], Thm 3.9): for a unit vector `x` with
Rayleigh quotient `θ = re⟪A x, x⟫` and residual `r = A x - θ x`, and a real number `lam` separated
by `δ > 0` from every eigenvalue of `A` other than `lam` itself, `sin ∠(x, ker (A - lam)) ≤ ‖r‖/δ`.

The subspace is the **eigenspace** of `lam`, not the line through one eigenvector for it: with a
multiple eigenvalue the statement about a line is false, as `A = diag(1, 1, 5)` with `x` the second
basis vector shows -- there `r = 0` and `δ = 4`, yet the angle to the line through the first basis
vector is a right angle. [saad2011numerical] takes `δ` to bound `A - θ` from below on the orthogonal
complement of that line, which it does only when `lam` is a simple eigenvalue; the simple case is
`sin_angle_span_singleton_le_norm_residual_div` below.

No hypothesis says that `lam` is an eigenvalue at all.  When it is not, the eigenspace is `⊥`, the
left-hand side is `1`, and the separation applies at every index, so the bound still holds.

The proof splits `x` into `p + q` along the eigenspace and its complement.  The residual splits
accordingly as `(lam - θ) p + (A - θ) q`, whose two terms are orthogonal because the eigenspace of a
symmetric operator is invariant and so is its complement, and Pythagoras then discards the `p` term.
-/
theorem sin_angle_le_norm_residual_div {n : ℕ} (hn : Module.finrank 𝕜 E = n) {x : E}
    (hx : ‖x‖ = 1) {lam δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i, hA.eigenvalues hn i ≠ lam →
      δ ≤ |hA.eigenvalues hn i - RCLike.re (inner 𝕜 (A x) x)|) :
    (Module.End.eigenspace A (lam : 𝕜)).sinAngle x
      ≤ ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ / δ := by
  set W : Submodule 𝕜 E := Module.End.eigenspace A (lam : 𝕜) with hWdef
  set θ : ℝ := RCLike.re (inner 𝕜 (A x) x) with hθdef
  have hpmem : W.starProjection x ∈ W := W.starProjection_apply_mem x
  have hqmem : x - W.starProjection x ∈ Wᗮ := W.sub_starProjection_mem_orthogonal x
  have hAp : A (W.starProjection x) = (lam : 𝕜) • W.starProjection x :=
    Module.End.mem_eigenspace_iff.1 hpmem
  have hres : A (x - W.starProjection x) - (θ : 𝕜) • (x - W.starProjection x) ∈ Wᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    have hzero := (Submodule.mem_orthogonal W _).1 hqmem y hy
    have h1 : inner 𝕜 y (A (x - W.starProjection x)) = (0 : 𝕜) := by
      rw [← hA y _, Module.End.mem_eigenspace_iff.1 hy, inner_smul_left, RCLike.conj_ofReal,
        hzero, mul_zero]
    rw [inner_sub_right, inner_smul_right, h1, hzero, mul_zero, sub_zero]
  have hsplit : A x - (θ : 𝕜) • x
      = ((lam : 𝕜) - (θ : 𝕜)) • W.starProjection x
        + (A (x - W.starProjection x) - (θ : 𝕜) • (x - W.starProjection x)) := by
    rw [map_sub, hAp]
    module
  have hpyth : ‖A x - (θ : 𝕜) • x‖ ^ 2
      = ‖((lam : 𝕜) - (θ : 𝕜)) • W.starProjection x‖ ^ 2
        + ‖A (x - W.starProjection x) - (θ : 𝕜) • (x - W.starProjection x)‖ ^ 2 := by
    rw [hsplit]
    simp only [pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (Submodule.inner_right_of_mem_orthogonal (Submodule.smul_mem _ _ hpmem) hres)
  have hlow := hA.mul_norm_le_norm_sub_smul_of_mem_orthogonal hn hδ.le hsep hqmem
  have hle : δ * ‖x - W.starProjection x‖ ≤ ‖A x - (θ : 𝕜) • x‖ := by
    refine hlow.trans ?_
    nlinarith [hpyth, norm_nonneg (A x - (θ : 𝕜) • x),
      norm_nonneg (A (x - W.starProjection x) - (θ : 𝕜) • (x - W.starProjection x)),
      sq_nonneg (‖((lam : 𝕜) - (θ : 𝕜)) • W.starProjection x‖)]
  rw [le_div_iff₀ hδ]
  calc W.sinAngle x * δ = δ * (W.sinAngle x * ‖x‖) := by rw [hx]; ring
    _ = δ * ‖x - W.starProjection x‖ := by rw [Submodule.sinAngle_mul_norm]
    _ ≤ _ := hle

/-- **The eigenvector residual bound at a simple eigenvalue**, which is [saad2011numerical], Thm 3.9
as printed: when the `lam`-eigenspace is a line, the angle it bounds is the angle to any eigenvector
`u` for `lam`.

Simplicity is what the printed proof needs and does not state: it takes `δ` to bound `A - θ` from
below on `u`'s orthogonal complement, and at a multiple eigenvalue that complement still meets the
`lam`-eigenspace, where `A - θ` is only `lam - θ`. -/
theorem sin_angle_span_singleton_le_norm_residual_div {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    {x : E} (hx : ‖x‖ = 1) {lam δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i, hA.eigenvalues hn i ≠ lam →
      δ ≤ |hA.eigenvalues hn i - RCLike.re (inner 𝕜 (A x) x)|)
    {u : E} (hu : A u = (lam : 𝕜) • u) (hu0 : u ≠ 0)
    (hsimple : Module.finrank 𝕜 (Module.End.eigenspace A (lam : 𝕜)) = 1) :
    (𝕜 ∙ u).sinAngle x ≤ ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ / δ := by
  have hle : (𝕜 ∙ u) ≤ Module.End.eigenspace A (lam : 𝕜) :=
    (Submodule.span_singleton_le_iff_mem _ _).2 (Module.End.mem_eigenspace_iff.2 hu)
  have heq : (𝕜 ∙ u) = Module.End.eigenspace A (lam : 𝕜) :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hsimple, finrank_span_singleton hu0])
  rw [Submodule.sinAngle_congr heq]
  exact hA.sin_angle_le_norm_residual_div hn hx hδ hsep

end LinearMap.IsSymmetric

/-- Backward error of an approximate eigenpair ([saad2011numerical], Prop 3.4): the least `‖ΔA‖`
with `(A - ΔA) u = θ u` (`‖u‖ = 1`) is `‖A u - θ u‖`, attained by the rank-one perturbation `r uᴴ`
built from the residual `r = A u - θ u`. -/
theorem isLeast_eigen_backwardError (A : E →L[𝕜] E) {u : E} (hu : ‖u‖ = 1) (θ : 𝕜) :
    IsLeast {ε : ℝ | ∃ ΔA : E →L[𝕜] E, (A - ΔA) u = θ • u ∧ ‖ΔA‖ = ε} ‖A u - θ • u‖ := by
  have huu : inner 𝕜 u u = (1 : 𝕜) := by
    rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  constructor
  · refine ⟨InnerProductSpace.rankOne 𝕜 (A u - θ • u) u, ?_, ?_⟩
    · have hr : (InnerProductSpace.rankOne 𝕜 (A u - θ • u) u) u = A u - θ • u := by
        rw [InnerProductSpace.rankOne_apply, huu, one_smul]
      rw [sub_apply, hr, sub_sub_cancel]
    · rw [InnerProductSpace.norm_rankOne, hu, mul_one]
  · rintro ε ⟨ΔA, hΔ, rfl⟩
    have hval : ΔA u = A u - θ • u := by
      rw [sub_apply, sub_eq_iff_eq_add] at hΔ
      rw [hΔ]; abel
    calc ‖A u - θ • u‖ = ‖ΔA u‖ := by rw [hval]
      _ ≤ ‖ΔA‖ * ‖u‖ := ΔA.le_opNorm u
      _ = ‖ΔA‖ := by rw [hu, mul_one]

/-- Bendixson's theorem ([saad2003iterative], Thm 1.35): the real part of every eigenvalue of a
bounded operator lies between the extreme eigenvalues of its symmetric part `H = (A + A†)/2`. -/
theorem re_hasEigenvalue_mem_Icc_of_symmetricPart {A H : E →ₗ[𝕜] E} {lmin lmax : ℝ}
    (hH : H.IsSymmetricBoundedBy lmin lmax)
    (hHA : ∀ x, RCLike.re (inner 𝕜 (H x) x) = RCLike.re (inner 𝕜 (A x) x)) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue A μ) : RCLike.re μ ∈ Set.Icc lmin lmax := by
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  have hAv : A v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  have hpos : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv0) 2
  have hkey : RCLike.re (inner 𝕜 (A v) v) = RCLike.re μ * ‖v‖ ^ 2 := by
    rw [hAv, inner_smul_left, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.mul_re]
    simp
  have h1 := hH.le_re_inner v
  have h2 := hH.re_inner_le v
  rw [hHA v, hkey] at h1 h2
  exact ⟨le_of_mul_le_mul_right (by linarith) hpos,
    le_of_mul_le_mul_right (by linarith) hpos⟩

/-! ### The condition number of a simple eigenvalue

[saad2011numerical], Def 3.1 measures the sensitivity of a simple eigenvalue by `‖u‖ ‖w‖ / |⟪w, u⟫|`
for a right eigenvector `u` and a left eigenvector `w`, that is, by the reciprocal cosine of the
angle between them.  The quantity is scale invariant, so it depends on the eigenvalue alone whenever
the eigenvalue is simple, its two eigenvectors being determined up to scale. -/

/-- **The condition number of a simple eigenvalue** ([saad2011numerical], Def 3.1): `‖u‖ ‖w‖ / ‖⟪w,
u⟫‖` for a right eigenvector `u` (`A u = μ u`) and a left eigenvector `w` (`A† w = conj μ • w`).

The definition mentions neither the operator nor the eigenvalue, because it does not depend on them:
it is `1 / cos ∠(u, w)`, and by `Module.End.eigenvalueCondNumber_smul` it is unchanged when either
eigenvector is rescaled, so at a *simple* eigenvalue — where each of the two eigenvectors spans a
line — it is a function of the eigenvalue.  The junk value at `⟪w, u⟫ = 0` is `0`;
`Module.End.one_le_eigenvalueCondNumber` therefore assumes the inner product nonzero, which for a
simple eigenvalue is a theorem rather than a hypothesis. -/
noncomputable def Module.End.eigenvalueCondNumber (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (u w : E) : ℝ :=
  ‖u‖ * ‖w‖ / ‖(inner 𝕜 w u : 𝕜)‖

namespace Module.End

/-- The condition number of a simple eigenvalue is scale invariant, which is what makes it a
function of the eigenvalue and not of the choice of eigenvectors. -/
theorem eigenvalueCondNumber_smul {u w : E} {a b : 𝕜} (ha : a ≠ 0) (hb : b ≠ 0) :
    eigenvalueCondNumber 𝕜 (a • u) (b • w) = eigenvalueCondNumber 𝕜 u w := by
  have hi : ‖(inner 𝕜 (b • w) (a • u) : 𝕜)‖ = ‖b‖ * ‖a‖ * ‖(inner 𝕜 w u : 𝕜)‖ := by
    rw [inner_smul_left, inner_smul_right, norm_mul, norm_mul, RCLike.norm_conj]
    ring
  have hane : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hbne : ‖b‖ ≠ 0 := norm_ne_zero_iff.2 hb
  rcases eq_or_ne (inner 𝕜 w u : 𝕜) 0 with h | h
  · simp [eigenvalueCondNumber, hi, h]
  · have hne : ‖(inner 𝕜 w u : 𝕜)‖ ≠ 0 := norm_ne_zero_iff.2 h
    rw [eigenvalueCondNumber, eigenvalueCondNumber, hi, norm_smul, norm_smul]
    field_simp

/-- The condition number of a simple eigenvalue is at least one, by Cauchy–Schwarz. -/
theorem one_le_eigenvalueCondNumber {u w : E} (h : (inner 𝕜 w u : 𝕜) ≠ 0) :
    1 ≤ eigenvalueCondNumber 𝕜 u w := by
  rw [eigenvalueCondNumber, le_div_iff₀ (norm_pos_iff.2 h), one_mul, mul_comm]
  exact norm_inner_le_norm w u

/-- A **normal** operator is perfectly conditioned at every simple eigenvalue: its left and right
eigenvectors span the same line (`LinearMap.IsStarNormal.eigenspace_adjoint`), so the angle between
them is zero and the condition number is `1`. -/
theorem eigenvalueCondNumber_eq_one_of_isStarNormal [FiniteDimensional 𝕜 E]
    {A : E →ₗ[𝕜] E} (hA : IsStarNormal A) {μ : 𝕜} {u w : E} (hu : A u = μ • u) (hu0 : u ≠ 0)
    (hw : A.adjoint w = (starRingEnd 𝕜) μ • w) (hw0 : w ≠ 0)
    (hsimple : Module.finrank 𝕜 (Module.End.eigenspace A μ) = 1) :
    eigenvalueCondNumber 𝕜 u w = 1 := by
  have hwmem : w ∈ Module.End.eigenspace A μ := by
    rw [← LinearMap.IsStarNormal.eigenspace_adjoint hA μ]
    exact Module.End.mem_eigenspace_iff.2 hw
  have hle : (𝕜 ∙ u) ≤ Module.End.eigenspace A μ :=
    (Submodule.span_singleton_le_iff_mem _ _).2 (Module.End.mem_eigenspace_iff.2 hu)
  have heq : (𝕜 ∙ u) = Module.End.eigenspace A μ :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hsimple, finrank_span_singleton hu0])
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (heq ▸ hwmem)
  have hc : c ≠ 0 := by
    rintro rfl
    exact hw0 (by simp)
  have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu0
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  rw [eigenvalueCondNumber, inner_smul_left, norm_smul, norm_mul, RCLike.norm_conj,
    inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg u)]
  field_simp

/-! ### First-order perturbation of a simple eigenvalue

Along a differentiable branch of eigenpairs of `A + t B` the eigenvalue moves at the rate `⟪w, B u⟫
/ ⟪w, u⟫`, whose modulus is at most `‖B‖` times the condition number of the eigenvalue.
[saad2011numerical], §3.2.1 displays exactly this computation.

The branch is assumed here and constructed in
`Module.End.hasDerivAt_eigenvalue_perturbation`, whose hypotheses are the same eigen-relations
together with the simplicity of `λ`. -/

/-- **The derivative of a simple eigenvalue** ([saad2011numerical], §3.2.1): along a differentiable
branch `t ↦ (μ t, u t)` of eigenpairs of `A + t B`, with `w` a left eigenvector of `A` for `λ = μ 0`
not orthogonal to `u 0`, the eigenvalue's derivative at `0` is `⟪w, B (u 0)⟫ / ⟪w, u 0⟫`.

The left-eigenvector hypothesis is stated as `⟪w, A y⟫ = λ ⟪w, y⟫` for every `y`, which is what the
proof tests the differentiated eigenvalue equation against; it is equivalent to `A† w = conj λ • w`
in finite dimension, and needs no adjoint to state.

Differentiating `A (u t) + t B (u t) = μ t • u t` at `t = 0` gives `A u' + B (u 0) = μ 0 • u' + μ' •
u 0`, and testing against `w` cancels the two terms carrying the unknown `u'`. -/
theorem deriv_eigenvalue_perturbation {A B : E →L[𝕜] E} {u : 𝕜 → E}
    {mu : 𝕜 → 𝕜} {u' : E} {mu' lam : 𝕜} {w : E}
    (hu : HasDerivAt u u' 0) (hmu : HasDerivAt mu mu' 0)
    (heig : ∀ t, A (u t) + t • B (u t) = mu t • u t)
    (hw : ∀ y, (inner 𝕜 w (A y) : 𝕜) = lam * inner 𝕜 w y) (hlam : mu 0 = lam)
    (hne : (inner 𝕜 w (u 0) : 𝕜) ≠ 0) :
    mu' = inner 𝕜 w (B (u 0)) / inner 𝕜 w (u 0) := by
  have h1 : HasDerivAt (fun t : 𝕜 => A (u t)) (A u') 0 := by
    simpa [Function.comp_def] using A.hasFDerivAt.comp_hasDerivAt (0 : 𝕜) hu
  have h2 : HasDerivAt (fun t : 𝕜 => B (u t)) (B u') 0 := by
    simpa [Function.comp_def] using B.hasFDerivAt.comp_hasDerivAt (0 : 𝕜) hu
  have hid : HasDerivAt (fun t : 𝕜 => t) 1 0 := hasDerivAt_id 0
  have h3 : HasDerivAt (fun t : 𝕜 => t • B (u t)) (B (u 0)) 0 := by
    have h := HasDerivAt.smul hid h2
    rw [zero_smul, one_smul, zero_add] at h
    exact h
  have hf : HasDerivAt (fun t : 𝕜 => mu t • u t) (A u' + B (u 0)) 0 :=
    HasDerivAt.congr_of_eventuallyEq (HasDerivAt.add h1 h3)
      (Filter.Eventually.of_forall fun t => (heig t).symm)
  have hderiv : A u' + B (u 0) = mu 0 • u' + mu' • u 0 :=
    hf.unique (HasDerivAt.smul hmu hu)
  have htest := congrArg (fun y : E => (inner 𝕜 w y : 𝕜)) hderiv
  simp only [inner_add_right, inner_smul_right, hw u', hlam] at htest
  have hmul : (inner 𝕜 w (B (u 0)) : 𝕜) = mu' * inner 𝕜 w (u 0) := by
    linear_combination htest
  rw [hmul, mul_div_assoc, div_self hne, mul_one]

/-- **The condition number bounds the first-order sensitivity** ([saad2011numerical], §3.2.1): the
rate at which a simple eigenvalue moves under the perturbation `t B` is at most `‖B‖` times its
condition number.

No normalization of `u 0` or of `w` is needed: both sides are scale invariant. -/
theorem norm_deriv_eigenvalue_perturbation_le {A B : E →L[𝕜] E} {u : 𝕜 → E}
    {mu : 𝕜 → 𝕜} {u' : E} {mu' lam : 𝕜} {w : E}
    (hu : HasDerivAt u u' 0) (hmu : HasDerivAt mu mu' 0)
    (heig : ∀ t, A (u t) + t • B (u t) = mu t • u t)
    (hw : ∀ y, (inner 𝕜 w (A y) : 𝕜) = lam * inner 𝕜 w y) (hlam : mu 0 = lam)
    (hne : (inner 𝕜 w (u 0) : 𝕜) ≠ 0) :
    ‖mu'‖ ≤ ‖B‖ * eigenvalueCondNumber 𝕜 (u 0) w := by
  have hpos : (0 : ℝ) < ‖(inner 𝕜 w (u 0) : 𝕜)‖ := norm_pos_iff.2 hne
  have hnum : ‖(inner 𝕜 w (B (u 0)) : 𝕜)‖ ≤ ‖B‖ * (‖u 0‖ * ‖w‖) := by
    calc ‖(inner 𝕜 w (B (u 0)) : 𝕜)‖ ≤ ‖w‖ * ‖B (u 0)‖ := norm_inner_le_norm w (B (u 0))
      _ ≤ ‖w‖ * (‖B‖ * ‖u 0‖) := by
          gcongr
          exact B.le_opNorm (u 0)
      _ = ‖B‖ * (‖u 0‖ * ‖w‖) := by ring
  rw [deriv_eigenvalue_perturbation hu hmu heig hw hlam hne, norm_div, eigenvalueCondNumber]
  calc ‖(inner 𝕜 w (B (u 0)) : 𝕜)‖ / ‖(inner 𝕜 w (u 0) : 𝕜)‖
      ≤ (‖B‖ * (‖u 0‖ * ‖w‖)) / ‖(inner 𝕜 w (u 0) : 𝕜)‖ := by gcongr
    _ = ‖B‖ * (‖u 0‖ * ‖w‖ / ‖(inner 𝕜 w (u 0) : 𝕜)‖) := by ring

/-- **A simple eigenvalue moves differentiably** ([saad2011numerical], §3.2.1): if `l` is an
eigenvalue of `A` with eigenvector `u` whose eigenspace is `𝕜 ∙ u`, and `w` is a left eigenvector
for `l` not orthogonal to `u`, then near `t = 0` there is a branch `t ↦ (mu t, v t)` of eigenpairs
of `A + t B` through `(l, u)`, differentiable at `0`, whose eigenvalue derivative is Saad's
`⟪w, B u⟫ / ⟪w, u⟫`.

This is the branch that `Module.End.deriv_eigenvalue_perturbation` assumes. It is built by the
inverse function theorem, not by the implicit function theorem and not through a determinant:
the map

`F (t, μ, z) = (t, ⟪w, z⟫, A z + t B z - μ z)`

on `𝕜 × 𝕜 × E` is a polynomial, so its strict derivative at `(0, l, u)` is immediate, and that
derivative is *injective* exactly because the eigenvalue is simple — testing `(A - l) δz = δμ u`
against `w` kills the left-hand side and forces `δμ = 0`, after which simplicity puts `δz` in
`𝕜 ∙ u` and `⟪w, δz⟫ = 0` kills it. In finite dimension injective is bijective, so `F` has a local
inverse `g`, and the branch is `t ↦ g (t, ⟪w, u⟫, 0)`. The derivative of the eigenvalue is read off
the same test: the second component `r` of `F' ⁻¹ (1, 0, 0)` satisfies `r ⟪w, u⟫ = ⟪w, B u⟫`.

The normalization carried along the branch is `⟪w, v t⟫ = ⟪w, u⟫`, which is what makes the branch
unique; it is the second component of the local inverse's defining equation. -/
theorem hasDerivAt_eigenvalue_perturbation [FiniteDimensional 𝕜 E] {A B : E →L[𝕜] E} {l : 𝕜}
    {u w : E} (hAu : A u = l • u) (hw : ∀ y, (inner 𝕜 w (A y) : 𝕜) = l * inner 𝕜 w y)
    (hne : (inner 𝕜 w u : 𝕜) ≠ 0)
    (hsimple : ∀ z : E, A z = l • z → ∃ c : 𝕜, z = c • u) :
    ∃ (mu : 𝕜 → 𝕜) (v : 𝕜 → E) (v' : E), mu 0 = l ∧ v 0 = u ∧
      (∀ᶠ t in nhds (0 : 𝕜), A (v t) + t • B (v t) = mu t • v t) ∧
      HasDerivAt v v' 0 ∧
      HasDerivAt mu (inner 𝕜 w (B u) / inner 𝕜 w u) 0 := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  set π₁ : (𝕜 × 𝕜 × E) →L[𝕜] 𝕜 := ContinuousLinearMap.fst 𝕜 𝕜 (𝕜 × E) with hπ₁
  set π₂ : (𝕜 × 𝕜 × E) →L[𝕜] 𝕜 :=
    (ContinuousLinearMap.fst 𝕜 𝕜 E).comp (ContinuousLinearMap.snd 𝕜 𝕜 (𝕜 × E)) with hπ₂
  set π₃ : (𝕜 × 𝕜 × E) →L[𝕜] E :=
    (ContinuousLinearMap.snd 𝕜 𝕜 E).comp (ContinuousLinearMap.snd 𝕜 𝕜 (𝕜 × E)) with hπ₃
  have hx1 : ∀ x : 𝕜 × 𝕜 × E, π₁ x = x.1 := fun _ => rfl
  have hx2 : ∀ x : 𝕜 × 𝕜 × E, π₂ x = x.2.1 := fun _ => rfl
  have hx3 : ∀ x : 𝕜 × 𝕜 × E, π₃ x = x.2.2 := fun _ => rfl
  set p : 𝕜 × 𝕜 × E := (0, l, u) with hp
  have hp1 : p.1 = (0 : 𝕜) := rfl
  have hp2 : p.2.1 = l := rfl
  have hp3 : p.2.2 = u := rfl
  set F : (𝕜 × 𝕜 × E) → (𝕜 × 𝕜 × E) := fun x =>
    (x.1, (inner 𝕜 w x.2.2 : 𝕜), A x.2.2 + x.1 • B x.2.2 - x.2.1 • x.2.2) with hF
  set D : (𝕜 × 𝕜 × E) →L[𝕜] (𝕜 × 𝕜 × E) :=
    π₁.prod (((innerSL 𝕜 w).comp π₃).prod
      (A.comp π₃ - l • π₃ - π₂.smulRight u + π₁.smulRight (B u))) with hD
  have hDapply : ∀ x : 𝕜 × 𝕜 × E, D x =
      (x.1, (inner 𝕜 w x.2.2 : 𝕜), A x.2.2 - l • x.2.2 - x.2.1 • u + x.1 • B u) := by
    intro x
    simp [hD, hπ₁, hπ₂, hπ₃]
  -- `D` is the strict derivative of `F` at `p`.
  have hFD : HasStrictFDerivAt F D p := by
    have h1 : HasStrictFDerivAt (fun x : 𝕜 × 𝕜 × E => x.1) π₁ p := π₁.hasStrictFDerivAt
    have h2 : HasStrictFDerivAt (fun x : 𝕜 × 𝕜 × E => x.2.1) π₂ p := π₂.hasStrictFDerivAt
    have h3 : HasStrictFDerivAt (fun x : 𝕜 × 𝕜 × E => x.2.2) π₃ p := π₃.hasStrictFDerivAt
    have hAc : HasStrictFDerivAt (fun x : 𝕜 × 𝕜 × E => A x.2.2) (A.comp π₃) p :=
      (A.comp π₃).hasStrictFDerivAt
    have hin : HasStrictFDerivAt (fun x : 𝕜 × 𝕜 × E => (inner 𝕜 w x.2.2 : 𝕜))
        ((innerSL 𝕜 w).comp π₃) p := ((innerSL 𝕜 w).comp π₃).hasStrictFDerivAt
    have hBc : HasStrictFDerivAt (fun x : 𝕜 × 𝕜 × E => B x.2.2) (B.comp π₃) p :=
      (B.comp π₃).hasStrictFDerivAt
    have hsum := (hAc.add (h1.smul hBc)).sub (h2.smul h3)
    refine (h1.prodMk (hin.prodMk hsum)).congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
    rw [hDapply]
    simp only [ContinuousLinearMap.prod_apply, add_apply, sub_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, hx1, hx2, hx3, hp1, hp2, hp3, zero_smul, zero_add]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    abel_nf
  -- `D` is injective, hence an equivalence.
  have hDker : ∀ x : 𝕜 × 𝕜 × E, D x = 0 → x = 0 := by
    intro x hx
    rw [hDapply] at hx
    have e1 : x.1 = 0 := by simpa using congrArg (fun z : 𝕜 × 𝕜 × E => z.1) hx
    have e2 : (inner 𝕜 w x.2.2 : 𝕜) = 0 := by
      simpa using congrArg (fun z : 𝕜 × 𝕜 × E => z.2.1) hx
    have e3 : A x.2.2 - l • x.2.2 - x.2.1 • u + x.1 • B u = 0 := by
      simpa using congrArg (fun z : 𝕜 × 𝕜 × E => z.2.2) hx
    rw [e1, zero_smul, add_zero, sub_eq_zero] at e3
    have e5 : (inner 𝕜 w (A x.2.2 - l • x.2.2) : 𝕜) = inner 𝕜 w (x.2.1 • u) := by rw [e3]
    rw [inner_sub_right, inner_smul_right, inner_smul_right, hw, e2] at e5
    have e6 : x.2.1 = 0 := by
      have hz : x.2.1 * (inner 𝕜 w u : 𝕜) = 0 := by rw [← e5]; ring
      rcases mul_eq_zero.1 hz with h | h
      · exact h
      · exact absurd h hne
    rw [e6, zero_smul, sub_eq_zero] at e3
    obtain ⟨c, hc⟩ := hsimple x.2.2 e3
    have e7 : c = 0 := by
      rw [hc, inner_smul_right] at e2
      rcases mul_eq_zero.1 e2 with h | h
      · exact h
      · exact absurd h hne
    have e8 : x.2.2 = 0 := by rw [hc, e7, zero_smul]
    exact Prod.ext e1 (Prod.ext e6 e8)
  have hDinj : Function.Injective D := by
    intro x y hxy
    have hz : D (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hzz := hDker _ hz
    rwa [sub_eq_zero] at hzz
  have hDbij : Function.Bijective D :=
    ⟨hDinj, LinearMap.injective_iff_surjective.1 hDinj⟩
  set D' : (𝕜 × 𝕜 × E) ≃L[𝕜] (𝕜 × 𝕜 × E) :=
    (LinearEquiv.ofBijective (D : (𝕜 × 𝕜 × E) →ₗ[𝕜] (𝕜 × 𝕜 × E)) hDbij).toContinuousLinearEquiv
      with hD'
  have hD'coe : (D' : (𝕜 × 𝕜 × E) →L[𝕜] (𝕜 × 𝕜 × E)) = D :=
    ContinuousLinearMap.ext fun _ => rfl
  rw [← hD'coe] at hFD
  set g : (𝕜 × 𝕜 × E) → (𝕜 × 𝕜 × E) := hFD.localInverse F D' p with hg
  have hFp : F p = (0, (inner 𝕜 w u : 𝕜), 0) := by
    simp [hF, hp, hAu]
  have hgp : g (0, (inner 𝕜 w u : 𝕜), 0) = p := by
    rw [hg, ← hFp]; exact hFD.localInverse_apply_image
  have hev : ∀ᶠ y in nhds (F p), F (g y) = y := hFD.eventually_right_inverse
  have hkderiv : HasDerivAt (fun t : 𝕜 => (t, (inner 𝕜 w u : 𝕜), (0 : E)))
      ((1 : 𝕜), (0 : 𝕜), (0 : E)) 0 :=
    HasDerivAt.prodMk (hasDerivAt_id' (0 : 𝕜))
      (HasDerivAt.prodMk (hasDerivAt_const _ _) (hasDerivAt_const _ _))
  have hkcont : Filter.Tendsto (fun t : 𝕜 => (t, (inner 𝕜 w u : 𝕜), (0 : E)))
      (nhds 0) (nhds (F p)) := by
    rw [hFp]
    exact hkderiv.continuousAt
  have hevt : ∀ᶠ t in nhds (0 : 𝕜),
      F (g (t, (inner 𝕜 w u : 𝕜), 0)) = (t, (inner 𝕜 w u : 𝕜), 0) := hkcont.eventually hev
  have hgd : HasStrictFDerivAt g (D'.symm : (𝕜 × 𝕜 × E) →L[𝕜] (𝕜 × 𝕜 × E)) (F p) :=
    hFD.to_localInverse
  have hgd' : HasFDerivAt g (D'.symm : (𝕜 × 𝕜 × E) →L[𝕜] (𝕜 × 𝕜 × E))
      ((0 : 𝕜), (inner 𝕜 w u : 𝕜), (0 : E)) := by
    rw [hFp] at hgd; exact hgd.hasFDerivAt
  have hcomp : HasDerivAt (fun t : 𝕜 => g (t, (inner 𝕜 w u : 𝕜), 0))
      (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))) 0 := by
    have := hgd'.comp_hasDerivAt (0 : 𝕜) hkderiv
    simpa [Function.comp_def] using this
  -- the second component of `D'.symm (1, 0, 0)` is Saad's derivative
  have hsymm : D (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))) = ((1 : 𝕜), (0 : 𝕜), (0 : E)) := by
    rw [← hD'coe, ContinuousLinearEquiv.coe_coe, D'.apply_symm_apply]
  have hr : (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).2.1 = inner 𝕜 w (B u) / inner 𝕜 w u := by
    rw [hDapply] at hsymm
    have f1 : (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).1 = 1 := by
      simpa using congrArg (fun z : 𝕜 × 𝕜 × E => z.1) hsymm
    have f2 : (inner 𝕜 w (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).2.2 : 𝕜) = 0 := by
      simpa using congrArg (fun z : 𝕜 × 𝕜 × E => z.2.1) hsymm
    have f3 : A (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).2.2
        - l • (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).2.2
        - (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).2.1 • u
        + (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).1 • B u = 0 := by
      simpa using congrArg (fun z : 𝕜 × 𝕜 × E => z.2.2) hsymm
    rw [f1, one_smul] at f3
    have f4 := congrArg (fun y : E => (inner 𝕜 w y : 𝕜)) f3
    simp only [inner_add_right, inner_sub_right, inner_smul_right, hw, f2, inner_zero_right] at f4
    have f5 : (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).2.1 * (inner 𝕜 w u : 𝕜)
        = inner 𝕜 w (B u) := by linear_combination -f4
    rw [eq_div_iff hne]
    exact f5
  refine ⟨fun t => (g (t, (inner 𝕜 w u : 𝕜), 0)).2.1,
    fun t => (g (t, (inner 𝕜 w u : 𝕜), 0)).2.2,
    (D'.symm ((1 : 𝕜), (0 : 𝕜), (0 : E))).2.2, ?_, ?_, ?_, ?_, ?_⟩
  · change (g ((0 : 𝕜), (inner 𝕜 w u : 𝕜), (0 : E))).2.1 = l
    rw [hgp]
  · change (g ((0 : 𝕜), (inner 𝕜 w u : 𝕜), (0 : E))).2.2 = u
    rw [hgp]
  · filter_upwards [hevt] with t ht
    have c1 : (g (t, (inner 𝕜 w u : 𝕜), 0)).1 = t := by
      simpa [hF] using congrArg (fun z : 𝕜 × 𝕜 × E => z.1) ht
    have c3 : A (g (t, (inner 𝕜 w u : 𝕜), 0)).2.2
        + (g (t, (inner 𝕜 w u : 𝕜), 0)).1 • B (g (t, (inner 𝕜 w u : 𝕜), 0)).2.2
        - (g (t, (inner 𝕜 w u : 𝕜), 0)).2.1 • (g (t, (inner 𝕜 w u : 𝕜), 0)).2.2 = 0 := by
      simpa [hF] using congrArg (fun z : 𝕜 × 𝕜 × E => z.2.2) ht
    rw [c1, sub_eq_zero] at c3
    exact c3
  · have := (π₃.hasFDerivAt).comp_hasDerivAt (0 : 𝕜) hcomp
    simpa [Function.comp_def, hx3] using this
  · rw [← hr]
    have := (π₂.hasFDerivAt).comp_hasDerivAt (0 : 𝕜) hcomp
    simpa [Function.comp_def, hx2] using this

end Module.End

namespace Matrix

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Bauer–Fike ([saad2011numerical], Thm 3.6; [kress1998numerical], Problem 7.6): for a
diagonalizable `A = X D X⁻¹` and `μ ∈ σ(A + ΔA)`, `dist(μ, σ(A)) ≤ κ₂(X) ‖ΔA‖₂`, where `κ₂(X) = ‖X‖₂
‖X⁻¹‖₂`. -/
theorem bauer_fike (X : Matrix n n ℂ) (d : n → ℂ) (hX : IsUnit X) (ΔA : Matrix n n ℂ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (X * Matrix.diagonal d * X⁻¹ + ΔA)) :
    ∃ i, ‖μ - d i‖ ≤ NormedRing.condNumber X * ‖ΔA‖ := by
  classical
  have hcond : NormedRing.condNumber X * ‖ΔA‖ = ‖X‖ * ‖X⁻¹‖ * ‖ΔA‖ := by
    rw [NormedRing.condNumber, Matrix.nonsing_inv_eq_ringInverse]
  rw [← Matrix.spectrum_toLin'] at hμ
  obtain ⟨v, hv, hv0⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ).exists_hasEigenvector
  have hveq : (X * Matrix.diagonal d * X⁻¹ + ΔA) *ᵥ v = μ • v := by
    have h := Module.End.mem_eigenspace_iff.mp hv
    rwa [Matrix.toLin'_apply] at h
  have hne : Nonempty n := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    exact hv0 (Subsingleton.elim v 0)
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => ‖μ - d i‖)
    ⟨Classical.arbitrary n, Finset.mem_univ _⟩
  refine ⟨i₀, ?_⟩
  rw [hcond]
  by_cases hz : μ - d i₀ = 0
  · rw [hz, norm_zero]; positivity
  have hδ : 0 < ‖μ - d i₀‖ := norm_pos_iff.mpr hz
  have hne0 : ∀ i, μ - d i ≠ 0 := fun i hi => by
    have h := hi₀ i (Finset.mem_univ i)
    rw [hi, norm_zero] at h
    exact hz (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  set N : Matrix n n ℂ := Matrix.diagonal (fun i => μ - d i) with hN
  set Ninv : Matrix n n ℂ := Matrix.diagonal (fun i => (μ - d i)⁻¹) with hNinv
  have hNN : Ninv * N = 1 := by
    rw [hNinv, hN, Matrix.diagonal_mul_diagonal,
      show (fun i => (μ - d i)⁻¹ * (μ - d i)) = (1 : n → ℂ) from
        funext fun i => inv_mul_cancel₀ (hne0 i)]
    simp
  have hXd : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).mp hX
  have hXinvX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hXd
  set w := X⁻¹ *ᵥ v with hw
  have hvw : X *ᵥ w = v := by rw [hw, Matrix.mulVec_nonsing_inv_mulVec hX]
  have hw0 : w ≠ 0 := fun h => hv0 (by rw [← hvw, h, Matrix.mulVec_zero])
  have key : N *ᵥ w = (X⁻¹ * ΔA * X) *ᵥ w := by
    have e1 : (X⁻¹ * ΔA * X) *ᵥ w = X⁻¹ *ᵥ (ΔA *ᵥ v) := by
      rw [← hvw, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have e2 : ΔA *ᵥ v = μ • v - (X * Matrix.diagonal d * X⁻¹) *ᵥ v := by
      rw [← hveq, Matrix.add_mulVec]; abel
    have e3 : X⁻¹ *ᵥ ((X * Matrix.diagonal d * X⁻¹) *ᵥ v) = Matrix.diagonal d *ᵥ w := by
      rw [Matrix.mulVec_mulVec, show X⁻¹ * (X * Matrix.diagonal d * X⁻¹)
          = Matrix.diagonal d * X⁻¹ by rw [← mul_assoc, ← mul_assoc, hXinvX, one_mul],
        ← Matrix.mulVec_mulVec]
    rw [e1, e2, Matrix.mulVec_sub, Matrix.mulVec_smul, e3, ← hw, hN]
    funext i
    simp [Matrix.mulVec_diagonal, sub_mul]
  set u : EuclideanSpace ℂ n := WithLp.toLp 2 w with hu
  have hu0 : u ≠ 0 := fun h => hw0 (by simpa [hu] using congrArg WithLp.ofLp h)
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hid : Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv (Matrix.toEuclideanCLM (𝕜 := ℂ) N u) = u := by
    have hmap : Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv * Matrix.toEuclideanCLM (𝕜 := ℂ) N = 1 := by
      rw [← map_mul, hNN, map_one]
    calc Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv (Matrix.toEuclideanCLM (𝕜 := ℂ) N u)
        = (Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv * Matrix.toEuclideanCLM (𝕜 := ℂ) N) u := rfl
      _ = u := by rw [hmap]; rfl
  have hkey2 : Matrix.toEuclideanCLM (𝕜 := ℂ) N u
      = Matrix.toEuclideanCLM (𝕜 := ℂ) (X⁻¹ * ΔA * X) u := by
    rw [hu, Matrix.toEuclideanCLM_toLp, Matrix.toEuclideanCLM_toLp, key]
  have hbound : ‖u‖ ≤ ‖Ninv‖ * (‖X⁻¹ * ΔA * X‖ * ‖u‖) := by
    calc ‖u‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv
                (Matrix.toEuclideanCLM (𝕜 := ℂ) (X⁻¹ * ΔA * X) u)‖ := by rw [← hkey2, hid]
      _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) Ninv‖ *
            ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (X⁻¹ * ΔA * X) u‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖Ninv‖ * (‖X⁻¹ * ΔA * X‖ * ‖u‖) := by
          rw [Matrix.l2_opNorm_toEuclideanCLM]
          exact mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
  have hNinvle : ‖Ninv‖ ≤ ‖μ - d i₀‖⁻¹ := by
    rw [hNinv, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    rw [norm_inv]
    gcongr
    exact hi₀ i (Finset.mem_univ i)
  have hmul : ‖X⁻¹ * ΔA * X‖ ≤ ‖X⁻¹‖ * ‖ΔA‖ * ‖X‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have h1 : 1 ≤ ‖Ninv‖ * ‖X⁻¹ * ΔA * X‖ := by nlinarith [hbound, hupos]
  have h2 : 1 ≤ ‖μ - d i₀‖⁻¹ * (‖X⁻¹‖ * ‖ΔA‖ * ‖X‖) :=
    h1.trans (mul_le_mul hNinvle hmul (norm_nonneg _) (by positivity))
  have h3 : ‖μ - d i₀‖ ≤ ‖X⁻¹‖ * ‖ΔA‖ * ‖X‖ := by
    have h4 := mul_le_mul_of_nonneg_left h2 hδ.le
    rwa [mul_one, ← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul] at h4
  calc ‖μ - d i₀‖ ≤ ‖X⁻¹‖ * ‖ΔA‖ * ‖X‖ := h3
    _ = ‖X‖ * ‖X⁻¹‖ * ‖ΔA‖ := by ring

/-- Residual form of Bauer–Fike: for a unit approximate eigenpair `(θ, u)` of a diagonalizable `A =
X D X⁻¹`, `dist(θ, σ(A)) ≤ κ₂(X) ‖A u - θ u‖`, where `κ₂(X) = ‖X‖₂ ‖X⁻¹‖₂`. -/
theorem bauer_fike_residual (X : Matrix n n ℂ) (d : n → ℂ) (hX : IsUnit X)
    {u : EuclideanSpace ℂ n} (hu : ‖u‖ = 1) (θ : ℂ) :
    ∃ i, ‖θ - d i‖ ≤ NormedRing.condNumber X *
      ‖Matrix.toEuclideanLin (X * Matrix.diagonal d * X⁻¹) u - θ • u‖ := by
  classical
  set A := X * Matrix.diagonal d * X⁻¹ with hA
  set r : EuclideanSpace ℂ n := Matrix.toEuclideanLin A u - θ • u with hr
  -- the rank-one backward perturbation `r uᴴ`
  set M : Matrix n n ℂ :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (InnerProductSpace.rankOne ℂ r u) with hM
  have hMapply : Matrix.toEuclideanCLM (𝕜 := ℂ) M = InnerProductSpace.rankOne ℂ r u := by
    rw [hM, StarAlgEquiv.apply_symm_apply]
  have hMnorm : ‖M‖ = ‖r‖ := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM, hMapply, InnerProductSpace.norm_rankOne, hu, mul_one]
  have huu : inner ℂ u u = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have hu0 : WithLp.ofLp u ≠ 0 := by
    intro h
    have : u = 0 := by
      apply WithLp.ofLp_injective
      simpa using h
    rw [this, norm_zero] at hu
    exact one_ne_zero hu.symm
  have hclm : Matrix.toEuclideanCLM (𝕜 := ℂ) (A + (-M)) u = θ • u := by
    rw [map_add, map_neg, hMapply]
    change Matrix.toEuclideanLin A u + -(inner ℂ u u • r) = θ • u
    rw [huu, one_smul, hr]
    abel
  have heig : (A + (-M)) *ᵥ (WithLp.ofLp u) = θ • WithLp.ofLp u := by
    have h := congrArg WithLp.ofLp hclm
    rw [Matrix.add_mulVec, Matrix.neg_mulVec]
    simpa using h
  have hspec : θ ∈ spectrum ℂ (A + (-M)) := by
    rw [← Matrix.spectrum_toLin']
    refine Module.End.hasEigenvalue_iff_mem_spectrum.mp
      (Module.End.hasEigenvalue_of_hasEigenvector (x := WithLp.ofLp u) ⟨?_, hu0⟩)
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact heig
  obtain ⟨i, hi⟩ := bauer_fike X d hX (-M) hspec
  exact ⟨i, by rwa [norm_neg, hMnorm] at hi⟩

/-- Gershgorin discs, union form ([saad2011numerical], Thm 3.11; [kress1998numerical], Thm 7.7): the
spectrum is contained in the union over `i` of the discs centred at `a_ii` with radius `∑_{j ≠ i}
|a_ij|`.  Mathlib's `eigenvalue_mem_ball` is the pointwise version. -/
theorem spectrum_subset_iUnion_closedBall (A : Matrix n n ℂ) :
    spectrum ℂ A ⊆ ⋃ i, Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖) := by
  intro μ hμ
  rw [← Matrix.spectrum_toLin'] at hμ
  obtain ⟨i, hi⟩ := _root_.eigenvalue_mem_ball (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ)
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- The column-sum Gershgorin theorem ([saad2011numerical], Thm 3.11; [saad2003iterative], Thm 4.6,
column form): the spectrum is contained in the union over `j` of the discs centred at `a_jj` with
radius `∑_{i ≠ j} |a_ij|`.

A matrix and its transpose have the same spectrum, so this is the row form applied to the transpose.
-/
theorem spectrum_subset_iUnion_closedBall_col (A : Matrix n n ℂ) :
    spectrum ℂ A ⊆ ⋃ j, Metric.closedBall (A j j) (∑ i ∈ Finset.univ.erase j, ‖A i j‖) := by
  intro μ hμ
  have hT : μ ∈ spectrum ℂ Aᵀ := by rwa [Matrix.spectrum_transpose]
  simpa using spectrum_subset_iUnion_closedBall Aᵀ hT

/-- **Gershgorin disc counting** (Saad, *Numerical Methods for Large Eigenvalue Problems*, 2nd
edition, Theorem 3.12): if the union `S` of the Gershgorin discs indexed by `τ` is disjoint from
the union `S'` of the remaining discs, then `S` contains exactly `τ.card` eigenvalues, counted with
multiplicity.

The count is `Polynomial.countRootsIn`, the number of roots of the characteristic polynomial in
`S` with multiplicity, which by `Matrix.mem_spectrum_iff_isRoot_charpoly` is the total algebraic
multiplicity of the eigenvalues lying in `S`.

The proof is Saad's homotopy `A t = D + t H`, with `D` the diagonal of `A` and `H` the rest.  The
Gershgorin discs of `A t` are those of `A` shrunk by the factor `t`, so for `0 ≤ t ≤ 1` the
eigenvalues of `A t` stay in `S ∪ S'` throughout; at `t = 0` the eigenvalues are the diagonal
entries, of which exactly those indexed by `τ` lie in `S`.  Saad's "continuity argument" — that the
branches of eigenvalues cannot cross from `S` to `S'` — is
`Polynomial.countRootsIn_eq_of_preconnected`, a compactness argument in the coefficients that needs
no complex analysis and no separation of the branches from each other. -/
theorem card_spectrum_of_disjoint_gershgorin (A : Matrix n n ℂ) (τ : Finset n) {S S' : Set ℂ}
    (hS : S = ⋃ i ∈ τ, Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖))
    (hS' : S' = ⋃ i ∈ τᶜ, Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖))
    (hdisj : Disjoint S S') :
    A.charpoly.countRootsIn S = τ.card := by
  classical
  set r : n → ℝ := fun i => ∑ j ∈ Finset.univ.erase i, ‖A i j‖ with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => Finset.sum_nonneg fun j _ => norm_nonneg _
  set D : Matrix n n ℂ := Matrix.diagonal fun i => A i i with hD
  set H : Matrix n n ℂ := A - D with hH
  set M : ℝ → Matrix n n ℂ := fun t => D + (t : ℂ) • H with hM
  have hMdiag : ∀ t i, M t i i = A i i := by
    intro t i; simp [hM, hD, hH, Matrix.diagonal_apply_eq]
  have hMoff : ∀ t i j, i ≠ j → M t i j = (t : ℂ) * A i j := by
    intro t i j hij; simp [hM, hD, hH, Matrix.diagonal_apply_ne _ hij]
  have hM0 : M 0 = D := by simp [hM]
  have hM1 : M 1 = A := by simp [hM, hH]
  have hMcont : Continuous M :=
    continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  -- the two unions of discs are compact, and together they are all the discs
  have hScpt : IsCompact S := by
    rw [hS]; exact τ.finite_toSet.isCompact_biUnion fun i _ => isCompact_closedBall _ _
  have hS'cpt : IsCompact S' := by
    rw [hS']; exact τᶜ.finite_toSet.isCompact_biUnion fun i _ => isCompact_closedBall _ _
  have hunion : S ∪ S' = ⋃ i, Metric.closedBall (A i i) (r i) := by
    ext z
    simp only [hS, hS', Set.mem_union, Set.mem_iUnion, Finset.mem_compl, exists_prop, hr]
    constructor
    · rintro (⟨i, _, hi⟩ | ⟨i, _, hi⟩) <;> exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      by_cases h : i ∈ τ
      · exact Or.inl ⟨i, h, hi⟩
      · exact Or.inr ⟨i, h, hi⟩
  -- Gershgorin for `M t`: its discs are those of `A` with the radii scaled by `t ≤ 1`
  have hroots : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ z ∈ (M t).charpoly.roots, z ∈ S ∪ S' := by
    intro t ht z hz
    rw [hunion]
    have hz' : z ∈ spectrum ℂ (M t) := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (Matrix.spectrum_subset_iUnion_closedBall (M t) hz')
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [hMdiag t i] at hi
    refine Metric.closedBall_subset_closedBall ?_ hi
    calc ∑ j ∈ Finset.univ.erase i, ‖M t i j‖
        = ∑ j ∈ Finset.univ.erase i, |t| * ‖A i j‖ := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [hMoff t i j (Finset.ne_of_mem_erase hj).symm]
          simp
      _ = |t| * r i := by rw [hr, Finset.mul_sum]
      _ ≤ r i := by
          rw [abs_of_nonneg ht.1]
          exact mul_le_of_le_one_left (hr0 i) ht.2
  have hcard : ∀ t : ℝ, Multiset.card (M t).charpoly.roots = Fintype.card n := fun t =>
    (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits (M t).charpoly)).trans
      (Matrix.charpoly_natDegree_eq_dim _)
  have : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have key := Polynomial.countRootsIn_eq_of_preconnected (T := Set.Icc (0 : ℝ) 1)
    (p := fun t => (M t.1).charpoly) (n := Fintype.card n) hScpt hS'cpt hdisj
    (fun _ => Matrix.charpoly_monic _)
    (fun _ => Matrix.charpoly_natDegree_eq_dim _)
    (fun t => hcard t.1)
    (fun t z hz => hroots t.1 t.2 z hz)
    (fun j => (Matrix.continuous_coeff_charpoly hMcont j).comp continuous_subtype_val)
    ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
  simp only at key
  -- at `t = 0` the roots are the diagonal entries, and `a_ii ∈ S` exactly for `i ∈ τ`
  rw [← hM1, ← key, hM0, Matrix.charpoly_diagonal, Polynomial.countRootsIn_prod_univ_X_sub_C]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    by_contra hiτ
    exact Set.disjoint_left.mp hdisj hi (by
      rw [hS']
      exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_compl.mpr hiτ, Metric.mem_closedBall_self (hr0 i)⟩)
  · intro hiτ
    rw [hS]
    exact Set.mem_iUnion₂.mpr ⟨i, hiτ, Metric.mem_closedBall_self (hr0 i)⟩

/-- **An isolated Gershgorin disc contains exactly one eigenvalue** (Saad, *Numerical Methods for
Large Eigenvalue Problems*, 2nd edition, the particular case of Theorem 3.12 noted after its
proof): the case `τ = {i}` of `Matrix.card_spectrum_of_disjoint_gershgorin`.

In particular the eigenvalue in an isolated disc is simple. -/
theorem card_spectrum_of_isolated_gershgorin (A : Matrix n n ℂ) (i : n) {S S' : Set ℂ}
    (hS : S = Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖))
    (hS' : S' = ⋃ k ∈ ({i} : Finset n)ᶜ,
      Metric.closedBall (A k k) (∑ j ∈ Finset.univ.erase k, ‖A k j‖))
    (hdisj : Disjoint S S') :
    A.charpoly.countRootsIn S = 1 := by
  have := card_spectrum_of_disjoint_gershgorin A {i} (by simpa using hS) hS' hdisj
  simpa using this

end Matrix

/-! ### Hirsch's bounds

[quarteroni2000numerical] Theorem 5.1 (Hirsch): the real and the imaginary part of every eigenvalue
of `A` lie between the extreme eigenvalues of the Hermitian part `H = (A + Aᴴ)/2` and of the matrix
`S = (A - Aᴴ)/(2i)` respectively. Both are Bendixson's theorem
`re_hasEigenvalue_mem_Icc_of_symmetricPart` read through `Matrix.toEuclideanLin`, the imaginary
half being the real half for `-i A`, whose Hermitian part is `S`. -/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Bendixson's theorem for matrices: if `H` is Hermitian and its quadratic form is the real part
of that of `A`, every eigenvalue of `A` has real part between the extreme eigenvalues of `H`. -/
theorem re_mem_Icc_eigenvalues_of_mem_spectrum {A H : Matrix n n 𝕜} (hH : H.IsHermitian)
    (hHA : ∀ x : EuclideanSpace 𝕜 n, RCLike.re (inner 𝕜 (toEuclideanLin H x) x)
      = RCLike.re (inner 𝕜 (toEuclideanLin A x) x))
    {μ : 𝕜} (hμ : μ ∈ spectrum 𝕜 A) :
    RCLike.re μ ∈ Set.Icc (⨅ i, hH.eigenvalues i) (⨆ i, hH.eigenvalues i) := by
  refine re_hasEigenvalue_mem_Icc_of_symmetricPart (hH.isSymmetricBoundedBy_toEuclideanLin
    fun i => ⟨ciInf_le (Set.finite_range _).bddBelow i, le_ciSup (Set.finite_range _).bddAbove i⟩)
    hHA ((hasEigenvalue_toEuclideanLin_iff A μ).mpr hμ)

/-- **Hirsch's theorem, real part** ([quarteroni2000numerical] Theorem 5.1; Bendixson): the real
part of every eigenvalue of `A` lies between the smallest and the largest eigenvalue of the
Hermitian part `H = (A + Aᴴ)/2`. -/
theorem hirsch_re (A : Matrix n n 𝕜) {μ : 𝕜} (hμ : μ ∈ spectrum 𝕜 A) :
    RCLike.re μ ∈ Set.Icc (⨅ i, (hermitianPart_isHermitian A).eigenvalues i)
      (⨆ i, (hermitianPart_isHermitian A).eigenvalues i) :=
  re_mem_Icc_eigenvalues_of_mem_spectrum _ (re_inner_hermitianPart A) hμ

/-- **Hirsch's theorem, imaginary part** ([quarteroni2000numerical] Theorem 5.1): the imaginary
part of every eigenvalue of `A` lies between the smallest and the largest eigenvalue of
`S = (A - Aᴴ)/(2i)`. It is the real part of the theorem for `-i A`, whose Hermitian part is `S`
and whose eigenvalues are `-i` times those of `A`. -/
theorem hirsch_im (A : Matrix n n ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    μ.im ∈ Set.Icc (⨅ i, (skewHermitianPart_isHermitian A).eigenvalues i)
      (⨆ i, (skewHermitianPart_isHermitian A).eigenvalues i) := by
  have hμ' : (-Complex.I) • μ ∈ spectrum ℂ ((-Complex.I) • A) := by
    rw [show (-Complex.I) = (Units.mk0 (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero) : ℂ)
      from rfl, ← Units.smul_def, ← Units.smul_def, spectrum.unit_smul_eq_smul]
    exact Set.smul_mem_smul_set hμ
  have h := re_mem_Icc_eigenvalues_of_mem_spectrum (skewHermitianPart_isHermitian A)
    (fun x => by rw [← hermitianPart_neg_I_smul, re_inner_hermitianPart]) hμ'
  simpa [Complex.mul_re] using h

end Matrix

/-! ### Algebraically simple eigenvalues

At an eigenvalue of algebraic multiplicity one — `finrank (maxGenEigenspace A l) = 1` — the two
hypotheses that `Module.End.hasDerivAt_eigenvalue_perturbation` carries separately, `⟪w, u⟫ ≠ 0`
and the geometric simplicity `∀ z, A z = l • z → ∃ c, z = c • u`, are theorems. The first is the
opening paragraph of the proof of [quarteroni2000numerical] Theorem 5.4, without its
diagonalizability. -/

namespace Module.End

variable [FiniteDimensional 𝕜 E]

/-- At an eigenvalue of algebraic multiplicity one, the maximal generalized eigenspace is the line
through any eigenvector. -/
theorem maxGenEigenspace_eq_span_singleton_of_finrank_eq_one {A : E →ₗ[𝕜] E} {l : 𝕜} {u : E}
    (hAu : A u = l • u) (hu : u ≠ 0)
    (hsimple : Module.finrank 𝕜 (Module.End.maxGenEigenspace A l) = 1) :
    Module.End.maxGenEigenspace A l = 𝕜 ∙ u := by
  have hle : (𝕜 ∙ u) ≤ Module.End.maxGenEigenspace A l :=
    (Submodule.span_singleton_le_iff_mem _ _).2
      (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hAu))
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hsimple, finrank_span_singleton hu])).symm

/-- **A right and a left eigenvector for an algebraically simple eigenvalue are not orthogonal**
([quarteroni2000numerical] Theorem 5.4, first step of the proof; [saad2011numerical] §3.2.1): if
`A u = l u` with `u ≠ 0`, `⟪w, A y⟫ = l ⟪w, y⟫` for all `y` with `w ≠ 0`, and
`finrank (maxGenEigenspace A l) = 1`, then `⟪w, u⟫ ≠ 0`.

Were `⟪w, u⟫ = 0`, `u` would lie in `(𝕜 ∙ w)ᗮ`, which is the range of `A - l`: that range is
contained in `(𝕜 ∙ w)ᗮ` because `w` is a left eigenvector, and both have codimension one, the
kernel of `A - l` being the line through `u`. So `u = (A - l) z` for some `z`, which makes `z` a
generalized eigenvector of index two — `(A - l)² z = 0` with `(A - l) z ≠ 0` — inside a generalized
eigenspace that is only a line. This is why the hypothesis `hne` of
`Module.End.hasDerivAt_eigenvalue_perturbation` is automatic at an algebraically simple eigenvalue.
-/
theorem inner_ne_zero_of_finrank_maxGenEigenspace_eq_one {A : E →ₗ[𝕜] E} {l : 𝕜} {u w : E}
    (hAu : A u = l • u) (hu : u ≠ 0) (hw : ∀ y, (inner 𝕜 w (A y) : 𝕜) = l * inner 𝕜 w y)
    (hw0 : w ≠ 0) (hsimple : Module.finrank 𝕜 (Module.End.maxGenEigenspace A l) = 1) :
    (inner 𝕜 w u : 𝕜) ≠ 0 := by
  intro hwu
  set B : E →ₗ[𝕜] E := A - l • 1 with hBdef
  have hBapply : ∀ y, B y = A y - l • y := fun y => by simp [hBdef]
  have hBu : B u = 0 := by rw [hBapply, hAu, sub_self]
  -- the kernel of `B` is the line through `u`
  have hker : LinearMap.ker B = 𝕜 ∙ u := by
    rw [hBdef, ← Module.End.eigenspace_def,
      ← Krylov.maxGenEigenspace_eq_eigenspace_of_finrank_eq_one hsimple]
    exact maxGenEigenspace_eq_span_singleton_of_finrank_eq_one hAu hu hsimple
  -- the range of `B` is the orthogonal complement of `w`
  have hrange_le : LinearMap.range B ≤ (𝕜 ∙ w)ᗮ := by
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, hBapply, inner_sub_right,
      inner_smul_right, hw, sub_self]
  have hrange : LinearMap.range B = (𝕜 ∙ w)ᗮ := by
    refine Submodule.eq_of_le_of_finrank_le hrange_le ?_
    have h1 := LinearMap.finrank_range_add_finrank_ker B
    have h2 := Submodule.finrank_add_finrank_orthogonal (𝕜 ∙ w)
    rw [hker, finrank_span_singleton hu] at h1
    rw [finrank_span_singleton hw0] at h2
    omega
  -- so `u = B z` for some `z`, a generalized eigenvector of index two
  have humem : u ∈ LinearMap.range B := by
    rw [hrange, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hwu
  obtain ⟨z, hz⟩ := humem
  have hzmem : z ∈ Module.End.maxGenEigenspace A l := by
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨2, by rw [pow_two, Module.End.mul_apply, ← hBdef, hz, hBu]⟩
  rw [maxGenEigenspace_eq_span_singleton_of_finrank_eq_one hAu hu hsimple,
    Submodule.mem_span_singleton] at hzmem
  obtain ⟨c, rfl⟩ := hzmem
  rw [map_smul, hBu, smul_zero] at hz
  exact hu hz.symm

/-- **A simple eigenvalue moves differentiably**, under the single hypothesis that it is
algebraically simple: `Module.End.hasDerivAt_eigenvalue_perturbation` with its two hypotheses
`⟪w, u⟫ ≠ 0` and geometric simplicity replaced by `finrank (maxGenEigenspace A l) = 1`, for any
nonzero eigenvector `u` and any nonzero left eigenvector `w`. This is the branch that
[quarteroni2000numerical] Theorem 5.4 presupposes when it calls `λ` simple. -/
theorem hasDerivAt_eigenvalue_perturbation_of_finrank_eq_one {A B : E →L[𝕜] E} {l : 𝕜}
    {u w : E} (hAu : A u = l • u) (hu : u ≠ 0)
    (hw : ∀ y, (inner 𝕜 w (A y) : 𝕜) = l * inner 𝕜 w y) (hw0 : w ≠ 0)
    (hsimple : Module.finrank 𝕜 (Module.End.maxGenEigenspace (A : E →ₗ[𝕜] E) l) = 1) :
    ∃ (mu : 𝕜 → 𝕜) (v : 𝕜 → E) (v' : E), mu 0 = l ∧ v 0 = u ∧
      (∀ᶠ t in nhds (0 : 𝕜), A (v t) + t • B (v t) = mu t • v t) ∧
      HasDerivAt v v' 0 ∧
      HasDerivAt mu (inner 𝕜 w (B u) / inner 𝕜 w u) 0 := by
  refine hasDerivAt_eigenvalue_perturbation hAu hw
    (inner_ne_zero_of_finrank_maxGenEigenspace_eq_one (A := (A : E →ₗ[𝕜] E)) hAu hu hw hw0
      hsimple) fun z hz => ?_
  have hz' : z ∈ Module.End.maxGenEigenspace (A : E →ₗ[𝕜] E) l :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hz)
  rw [maxGenEigenspace_eq_span_singleton_of_finrank_eq_one (A := (A : E →ₗ[𝕜] E)) hAu hu hsimple,
    Submodule.mem_span_singleton] at hz'
  obtain ⟨c, rfl⟩ := hz'
  exact ⟨c, rfl⟩

end Module.End

/-! ### The distance to a group of eigenvectors -/

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
include hA

/-- A vector is orthogonal to `hA.eigenvectorSpan hn s` exactly when its eigenbasis coordinates
vanish on `s`. -/
theorem mem_orthogonal_eigenvectorSpan_iff {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    {s : Finset (Fin n)} {x : E} :
    x ∈ (hA.eigenvectorSpan hn s)ᗮ ↔ ∀ i ∈ s, (hA.eigenvectorBasis hn).repr x i = 0 := by
  rw [← Submodule.span_singleton_le_iff_mem, ← Submodule.isOrtho_iff_le, Submodule.isOrtho_comm,
    eigenvectorSpan, Submodule.isOrtho_span]
  simp only [Set.mem_image, Finset.mem_coe, Set.mem_singleton_iff, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, forall_eq, OrthonormalBasis.repr_apply_apply]

/-- **The distance from an approximate eigenvector to a group of eigenvectors**
([quarteroni2000numerical] Property 5.6; Isaacson–Keller, *Analysis of Numerical Methods*,
pp. 142–143): for a symmetric `A` with eigenpairs `(hA.eigenvalues hn i, hA.eigenvectorBasis hn
i)`, an approximate pair `(θ, x)` with residual `r = A x - θ x`, and a set `s` of indices such that
every eigenvalue *outside* `s` is at distance at least `δ > 0` from `θ`, the distance from `x` to
the span of the eigenvectors indexed by `s` is at most `‖r‖ / δ`.

The book also assumes `|λ_i - θ| ≤ ‖r‖` for `i ∈ s`; that hypothesis plays no role. Taking `s` to
be the indices of one eigenvalue recovers `LinearMap.IsSymmetric.sin_angle_le_norm_residual_div`,
the residual bound for a single eigenspace.

The proof is the one of that theorem: split `x = p + q` along the span and its complement, both
`A`-invariant; the residual splits as `(A - θ) p + (A - θ) q` with orthogonal terms, so
`‖r‖ ≥ ‖(A - θ) q‖`, and in the eigenbasis `‖(A - θ) q‖² = ∑_{i ∉ s} (λ_i - θ)² |q_i|² ≥ δ² ‖q‖²`.
-/
theorem dist_eigenvectorSpan_le_norm_residual_div {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    (s : Finset (Fin n)) (θ : ℝ) (x : E) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∉ s, δ ≤ |hA.eigenvalues hn i - θ|) :
    ‖x - (hA.eigenvectorSpan hn s).starProjection x‖ ≤ ‖A x - (θ : 𝕜) • x‖ / δ := by
  set W : Submodule 𝕜 E := hA.eigenvectorSpan hn s with hWdef
  set p : E := W.starProjection x with hpdef
  set q : E := x - p with hqdef
  have hpmem : p ∈ W := W.starProjection_apply_mem x
  have hqmem : q ∈ Wᗮ := W.sub_starProjection_mem_orthogonal x
  have hpres : A p - (θ : 𝕜) • p ∈ W :=
    (hA.mem_eigenvectorSpan_iff hn).mpr fun i hi => by
      rw [hA.repr_sub_smul hn, (hA.mem_eigenvectorSpan_iff hn).mp hpmem i hi, mul_zero]
  have hqres : A q - (θ : 𝕜) • q ∈ Wᗮ :=
    (hA.mem_orthogonal_eigenvectorSpan_iff hn).mpr fun i hi => by
      rw [hA.repr_sub_smul hn, (hA.mem_orthogonal_eigenvectorSpan_iff hn).mp hqmem i hi, mul_zero]
  have hsplit : A x - (θ : 𝕜) • x = (A p - (θ : 𝕜) • p) + (A q - (θ : 𝕜) • q) := by
    rw [hqdef, map_sub, smul_sub]
    abel
  have hpyth : ‖A x - (θ : 𝕜) • x‖ ^ 2
      = ‖A p - (θ : 𝕜) • p‖ ^ 2 + ‖A q - (θ : 𝕜) • q‖ ^ 2 := by
    rw [hsplit]
    simp only [pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (Submodule.inner_right_of_mem_orthogonal hpres hqres)
  have hlow : δ * ‖q‖ ≤ ‖A q - (θ : 𝕜) • q‖ := by
    have hsq : (δ * ‖q‖) ^ 2 ≤ ‖A q - (θ : 𝕜) • q‖ ^ 2 := by
      rw [mul_pow, hA.norm_residual_sq hn θ q, hA.norm_sq_eq_sum_norm_repr_sq hn q,
        Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : i ∈ s
      · rw [(hA.mem_orthogonal_eigenvectorSpan_iff hn).mp hqmem i hi]
        simp
      · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have h := hsep i hi
        nlinarith [sq_abs (hA.eigenvalues hn i - θ), abs_nonneg (hA.eigenvalues hn i - θ)]
    exact le_of_sq_le_sq hsq (norm_nonneg _)
  rw [le_div_iff₀ hδ, mul_comm]
  refine hlow.trans ?_
  nlinarith [hpyth, norm_nonneg (A x - (θ : 𝕜) • x), norm_nonneg (A q - (θ : 𝕜) • q),
    sq_nonneg ‖A p - (θ : 𝕜) • p‖]

end LinearMap.IsSymmetric

/-! ### The resolvent step, the Schur-form bound and approximate invariant subspaces

`NormedRing.one_le_norm_inverse_mul_of_not_isUnit_sub` is the step shared by every
resolvent-based perturbation bound ([golub2013matrix] (7.2.1), via Lemma 2.3.3): if `μ` is an
eigenvalue of `A + E` but not of `A`, then `‖(μ - A)⁻¹ E‖ ≥ 1`, since otherwise
`μ - A - E = (μ - A)(1 - (μ - A)⁻¹ E)` would be invertible by the Neumann series.
`Matrix.infDist_spectrum_le_of_schur` is [golub2013matrix] Theorem 7.2.3, a Henrici-type bound for
a matrix that need not be diagonalizable: with a Schur form `Qᴴ A Q = D + N`, the resolvent of
`D + N` is a finite Neumann series in `(μ - D)⁻¹ N`, whose length is the nilpotency index of the
entrywise absolute value `|N|`.

`Matrix.IsHermitian.exists_mem_spectrum_abs_sub_le_of_mul_sub_mul` is the block form of the
residual bound ([golub2013matrix] Theorem 8.1.13, with the constant `1` of the one-vector residual
bound instead of the book's `√2`): an orthonormal block `Q₁` and a Hermitian `S` with
`‖A Q₁ - Q₁ S‖₂ ≤ ε` put an eigenvalue of `A` within `ε` of every eigenvalue of `S`. -/

/-- In a Banach algebra, if `a` is a unit and `a - b` is not, then `‖a⁻¹ b‖ ≥ 1`: otherwise
`a - b = a (1 - a⁻¹ b)` would be a unit by the Neumann series. -/
theorem NormedRing.one_le_norm_inverse_mul_of_not_isUnit_sub {R : Type*} [NormedRing R]
    [HasSummableGeomSeries R] {a b : R} (ha : IsUnit a) (hab : ¬IsUnit (a - b)) :
    1 ≤ ‖Ring.inverse a * b‖ := by
  by_contra hlt
  push Not at hlt
  apply hab
  obtain ⟨u, rfl⟩ := ha
  have : (u : R) - b = u * (1 - Ring.inverse (u : R) * b) := by
    rw [Ring.inverse_unit, mul_sub, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  rw [this]
  exact u.isUnit.mul (Units.oneSub _ hlt).isUnit

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem not_isUnit_sub_sub_of_mem_spectrum_add {A E : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 (A + E)) : ¬IsUnit ((μ • 1 - A) - E) := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one] at hμ
  rwa [sub_sub]

private theorem isUnit_smul_one_sub_of_notMem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜}
    (hA : μ ∉ spectrum 𝕜 A) : IsUnit (μ • 1 - A) := by
  rwa [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, not_not] at hA

section L2

open scoped Matrix.Norms.L2Operator

/-- The step shared by [golub2013matrix] Theorems 7.2.1–7.2.3 and 7.9.8 ((7.2.1), via their
Lemma 2.3.3), in the spectral norm: if `μ ∈ σ(A + E)` and `μ ∉ σ(A)` then
`1 ≤ ‖(μ I - A)⁻¹ E‖₂` (and so `1 ≤ ‖(μ I - A)⁻¹‖₂ ‖E‖₂`). -/
theorem one_le_norm_mul_of_mem_spectrum_add {A E : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 (A + E)) (hA : μ ∉ spectrum 𝕜 A) : 1 ≤ ‖(μ • 1 - A)⁻¹ * E‖ := by
  rw [nonsing_inv_eq_ringInverse]
  exact NormedRing.one_le_norm_inverse_mul_of_not_isUnit_sub
    (isUnit_smul_one_sub_of_notMem_spectrum hA) (not_isUnit_sub_sub_of_mem_spectrum_add hμ)

end L2

/-- The resolvent step `Matrix.one_le_norm_mul_of_mem_spectrum_add` in every induced `p`-norm:
if `μ ∈ σ(A + E)` and `μ ∉ σ(A)` then `1 ≤ ‖(μ I - A)⁻¹ E‖_p`. -/
theorem one_le_lpOpNorm_mul_of_mem_spectrum_add (p : ENNReal) [Fact (1 ≤ p)]
    {A E : Matrix n n 𝕜} {μ : 𝕜} (hμ : μ ∈ spectrum 𝕜 (A + E)) (hA : μ ∉ spectrum 𝕜 A) :
    1 ≤ lpOpNorm p ((μ • 1 - A)⁻¹ * E) := by
  rw [lpOpNorm, lpCLM_mul, ← ringInverse_lpCLM]
  refine NormedRing.one_le_norm_inverse_mul_of_not_isUnit_sub
    ((isUnit_lpCLM_iff p _).mpr (isUnit_smul_one_sub_of_notMem_spectrum hA)) ?_
  have : lpCLM p (μ • 1 - A) - lpCLM p E = lpCLM p ((μ • 1 - A) - E) := by
    ext x i; simp [sub_mulVec]
  rw [this, isUnit_lpCLM_iff]
  exact not_isUnit_sub_sub_of_mem_spectrum_add hμ

/-- Unitary conjugation preserves the spectrum. -/
private theorem spectrum_star_mul_mul {Q : Matrix n n 𝕜} (hQ : Q ∈ unitaryGroup n 𝕜)
    (M : Matrix n n 𝕜) : spectrum 𝕜 (star Q * M * Q) = spectrum 𝕜 M := by
  have hQ' : star Q * Q = 1 := mem_unitaryGroup_iff'.mp hQ
  have hdet : star Q.det * Q.det = 1 := by
    have := congrArg det hQ'
    rwa [det_mul, det_one, star_eq_conjTranspose, det_conjTranspose] at this
  ext μ
  simp only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det]
  have : μ • (1 : Matrix n n 𝕜) - star Q * M * Q = star Q * (μ • 1 - M) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQ']
  rw [this, det_mul, det_mul, star_eq_conjTranspose, det_conjTranspose, mul_comm (star Q.det),
    mul_assoc, hdet, mul_one]

section Schur

open scoped Matrix.Norms.L2Operator

/-- Entrywise domination of powers: if `‖M i j‖ ≤ c ‖N i j‖` entrywise then
`‖(M ^ k) i j‖ ≤ c ^ k ((|N|) ^ k) i j`, with `|N| = N.map ‖·‖`. -/
private theorem norm_pow_apply_le {M N : Matrix n n ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, ‖M i j‖ ≤ c * ‖N i j‖) (k : ℕ) (i j : n) :
    ‖(M ^ k) i j‖ ≤ c ^ k * ((N.map (‖·‖)) ^ k) i j ∧ 0 ≤ ((N.map (‖·‖)) ^ k) i j := by
  induction k generalizing i j with
  | zero =>
    by_cases hij : i = j
    · subst hij; simp
    · simp [one_apply_ne hij]
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · rw [pow_succ M, mul_apply, pow_succ (N.map (‖·‖)), mul_apply, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      rw [norm_mul, map_apply]
      calc ‖(M ^ k) i l‖ * ‖M l j‖ ≤ (c ^ k * ((N.map (‖·‖)) ^ k) i l) * (c * ‖N l j‖) :=
            mul_le_mul (ih i l).1 (h l j) (norm_nonneg _)
              (mul_nonneg (pow_nonneg hc _) (ih i l).2)
        _ = c ^ (k + 1) * (((N.map (‖·‖)) ^ k) i l * ‖N l j‖) := by ring
    · rw [pow_succ, mul_apply]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l).2 (by rw [map_apply]; positivity)

/-- [golub2013matrix] Theorem 7.2.3: let `Qᴴ A Q = diagonal d + N` for a unitary `Q`, and let
`p ≥ 1` be such that the entrywise absolute value `|N|` satisfies `|N| ^ p = 0` (for a strictly
upper triangular `N`, `p = n` always works; the book takes the least such `p`). If `μ` is an
eigenvalue of `A + E`, then `|μ - d i| ≤ max θ θ^{1/p}` for some `i`, where
`θ = ‖E‖₂ ∑_{k < p} ‖N‖₂ ^ k`. With `δ = min_i |μ - d_i| > 0`, the resolvent of `D + N` is the
finite Neumann series `∑_{k<p} ((μ - D)⁻¹ N)^k (μ - D)⁻¹` (the entrywise bound
`|((μ - D)⁻¹ N)^p| ≤ δ^{-p} |N|^p = 0`), so `‖(μ - A)⁻¹‖₂ ≤ ∑_{k<p} ‖N‖₂^k / δ^{k+1}` and
`1 ≤ ‖(μ - A)⁻¹‖₂ ‖E‖₂` gives `δ ≤ θ` if `δ ≥ 1` and `δ^p ≤ θ` if `δ < 1`. The book's
hypothesis that `N` be strictly upper triangular is not needed. -/
theorem infDist_spectrum_le_of_schur {A : Matrix n n ℂ} {Q : Matrix n n ℂ}
    (hQ : Q ∈ unitaryGroup n ℂ) {d : n → ℂ} {N : Matrix n n ℂ}
    (hQA : star Q * A * Q = diagonal d + N) {p : ℕ} (hp : 1 ≤ p) (hN : (N.map (‖·‖)) ^ p = 0)
    (E : Matrix n n ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A + E)) :
    ∃ i, ‖μ - d i‖ ≤
      max (‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k)
        ((‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k) ^ (1 / p : ℝ)) := by
  set θ := ‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k with hθ
  have hθ0 : 0 ≤ θ := mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)
  -- the index set is nonempty, since the spectrum of `A + E` is
  have hne : Nonempty n := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [spectrum.mem_iff] at hμ
    exact hμ (isUnit_of_subsingleton _)
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => ‖μ - d i‖)
    ⟨Classical.arbitrary n, Finset.mem_univ _⟩
  refine ⟨i₀, ?_⟩
  set δ := ‖μ - d i₀‖ with hδdef
  rcases (norm_nonneg (μ - d i₀)).eq_or_lt with hδ0 | hδ
  · rw [hδdef, ← hδ0]; exact hθ0.trans (le_max_left _ _)
  have hne0 : ∀ i, μ - d i ≠ 0 := fun i hi => by
    have h := hi₀ i (Finset.mem_univ i)
    rw [hi, norm_zero] at h
    exact hδ.ne' (le_antisymm h (norm_nonneg _))
  -- the diagonal part and its inverse
  set Dμ : Matrix n n ℂ := diagonal fun i => μ - d i with hDμ
  set Dinv : Matrix n n ℂ := diagonal fun i => (μ - d i)⁻¹ with hDinv
  have hDD : Dinv * Dμ = 1 := by
    rw [hDinv, hDμ, diagonal_mul_diagonal,
      show (fun i => (μ - d i)⁻¹ * (μ - d i)) = (1 : n → ℂ) from
        funext fun i => inv_mul_cancel₀ (hne0 i)]
    simp
  have hDinv_le : ‖Dinv‖ ≤ δ⁻¹ := by
    rw [hDinv, l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    rw [norm_inv]
    gcongr
    exact hi₀ i (Finset.mem_univ i)
  -- `M = (μ - D)⁻¹ N` is nilpotent
  set M := Dinv * N with hM
  have hMent : ∀ i j, ‖M i j‖ ≤ δ⁻¹ * ‖N i j‖ := fun i j => by
    rw [hM, hDinv, diagonal_mul, norm_mul, norm_inv]
    gcongr
    exact hi₀ i (Finset.mem_univ i)
  have hMp : M ^ p = 0 := by
    ext i j
    have h := (norm_pow_apply_le (inv_nonneg.mpr hδ.le) hMent p i j).1
    rw [hN, zero_apply, mul_zero] at h
    simpa using h
  -- the resolvent of `B = D + N` as a finite Neumann series
  set B := diagonal d + N with hB
  set S := ∑ k ∈ Finset.range p, M ^ k with hS
  have hSinv : S * Dinv * (μ • 1 - B) = 1 := by
    have h1 : μ • (1 : Matrix n n ℂ) - B = Dμ - N := by
      rw [hB, hDμ, ← diagonal_one, ← diagonal_smul, sub_add_eq_sub_sub, diagonal_sub]
      congr 2
      funext i
      simp
    rw [h1, Matrix.mul_assoc, Matrix.mul_sub, hDD, ← hM, geom_sum_mul_neg, hMp, sub_zero]
  have hBunit : IsUnit (μ • (1 : Matrix n n ℂ) - B) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_det_of_left_inverse hSinv)
  have hBinv : (μ • (1 : Matrix n n ℂ) - B)⁻¹ = S * Dinv := inv_eq_left_inv hSinv
  have hμB : μ ∉ spectrum ℂ B := by
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, not_not]; exact hBunit
  -- move the perturbation to the Schur basis
  set E' := star Q * E * Q with hE'
  have hμ' : μ ∈ spectrum ℂ (B + E') := by
    rw [← hQA, hE', ← Matrix.add_mul, ← Matrix.mul_add, spectrum_star_mul_mul hQ]
    exact hμ
  have hE'n : ‖E'‖ = ‖E‖ := l2_opNorm_unitary_mul_mul_unitary (Unitary.star_mem hQ) E hQ
  have hstep := one_le_norm_mul_of_mem_spectrum_add hμ' hμB
  rw [hBinv] at hstep
  -- bound the Neumann series
  have hpow : ∀ k : ℕ, ‖M ^ k‖ ≤ ‖M‖ ^ k := by
    intro k
    rcases k with _ | k
    · rw [pow_zero, pow_zero, CStarRing.norm_one]
    · exact norm_pow_le' M (Nat.succ_pos k)
  have hMnorm : ‖M‖ ≤ δ⁻¹ * ‖N‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hDinv_le (norm_nonneg _))
  have hSnorm : ‖S * Dinv‖ ≤ ∑ k ∈ Finset.range p, ‖N‖ ^ k * δ⁻¹ ^ (k + 1) := by
    calc ‖S * Dinv‖ ≤ ‖S‖ * ‖Dinv‖ := norm_mul_le _ _
      _ ≤ (∑ k ∈ Finset.range p, ‖M‖ ^ k) * δ⁻¹ :=
          mul_le_mul ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hpow k)) hDinv_le
            (norm_nonneg _) (Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)
      _ ≤ (∑ k ∈ Finset.range p, (δ⁻¹ * ‖N‖) ^ k) * δ⁻¹ :=
          mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun k _ =>
            pow_le_pow_left₀ (norm_nonneg _) hMnorm k) (inv_nonneg.mpr hδ.le)
      _ = ∑ k ∈ Finset.range p, ‖N‖ ^ k * δ⁻¹ ^ (k + 1) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => by ring
  have hmain : 1 ≤ ‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k * δ⁻¹ ^ (k + 1) := by
    calc (1 : ℝ) ≤ ‖S * Dinv * E'‖ := hstep
      _ ≤ ‖S * Dinv‖ * ‖E'‖ := norm_mul_le _ _
      _ ≤ (∑ k ∈ Finset.range p, ‖N‖ ^ k * δ⁻¹ ^ (k + 1)) * ‖E‖ := by
          rw [hE'n]; exact mul_le_mul_of_nonneg_right hSnorm (norm_nonneg _)
      _ = _ := mul_comm _ _
  rcases le_or_gt 1 δ with h1 | h1
  · -- `δ ≥ 1`: every `δ^{-(k+1)} ≤ δ⁻¹`
    refine le_max_of_le_left ?_
    have : ‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k * δ⁻¹ ^ (k + 1) ≤ θ * δ⁻¹ := by
      rw [hθ, mul_assoc, Finset.sum_mul]
      gcongr with k
      calc δ⁻¹ ^ (k + 1) = δ⁻¹ ^ k * δ⁻¹ := pow_succ _ _
        _ ≤ 1 * δ⁻¹ := by gcongr; exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1)
        _ = δ⁻¹ := one_mul _
    have h2 := hmain.trans this
    rwa [← div_eq_mul_inv, one_le_div hδ] at h2
  · -- `δ < 1`: every `δ^{-(k+1)} ≤ δ^{-p}`
    refine le_max_of_le_right ?_
    have : ‖E‖ * ∑ k ∈ Finset.range p, ‖N‖ ^ k * δ⁻¹ ^ (k + 1) ≤ θ * δ⁻¹ ^ p := by
      rw [hθ, mul_assoc, Finset.sum_mul]
      gcongr with k hk
      all_goals first
        | exact (one_le_inv₀ hδ).mpr h1.le
        | exact Finset.mem_range.mp hk
    have h2 := hmain.trans this
    rw [inv_pow, ← div_eq_mul_inv, one_le_div (by positivity)] at h2
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    calc δ = (δ ^ p) ^ (1 / p : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, mul_one_div_cancel hp0, Real.rpow_one]
      _ ≤ θ ^ (1 / p : ℝ) := by gcongr

end Schur

/-- The block form of the residual bound ([golub2013matrix] Theorem 8.1.13, with the constant `1`
in place of `√2`): let `A` and `S` be Hermitian, `Q₁ : Matrix n r 𝕜` have orthonormal columns
(`Q₁ᴴ Q₁ = 1`) and `‖A Q₁ - Q₁ S‖₂ ≤ ε`. Then every eigenvalue `θ` of `S` has an eigenvalue `μ`
of `A` with `|μ - θ| ≤ ε`: a unit eigenvector `y` of `S` gives the unit vector `x = Q₁ y` with
`A x - θ x = (A Q₁ - Q₁ S) y`, and `LinearMap.IsSymmetric.exists_hasEigenvalue_dist_le` does the
rest. The book's paired form, with `√2 ε` and distinct eigenvalues of `A` for distinct `θ`, is
`Matrix.IsHermitian.exists_embedding_abs_sub_le_of_mul_sub_mul`. -/
theorem IsHermitian.exists_mem_spectrum_abs_sub_le_of_mul_sub_mul {r : Type*} [Fintype r]
    [DecidableEq r] {A : Matrix n n 𝕜} {S : Matrix r r 𝕜} (hA : A.IsHermitian)
    (hS : S.IsHermitian) {Q₁ : Matrix n r 𝕜} (hQ : Q₁ᴴ * Q₁ = 1) {ε : ℝ}
    (hε : lpOpNorm 2 (A * Q₁ - Q₁ * S) ≤ ε) {θ : ℝ} (hθ : θ ∈ spectrum ℝ S) :
    ∃ μ ∈ spectrum ℝ A, |μ - θ| ≤ ε := by
  rw [hS.spectrum_real_eq_range_eigenvalues] at hθ
  obtain ⟨k, rfl⟩ := hθ
  set y := hS.eigenvectorBasis k with hy
  have hy1 : ‖y‖ = 1 := hS.eigenvectorBasis.orthonormal.1 k
  set x : EuclideanSpace 𝕜 n := toEuclideanLin Q₁ y with hx
  -- `Q₁` is an isometry
  have hxy : ‖x‖ = ‖y‖ := by
    have h : (inner 𝕜 x x : 𝕜) = inner 𝕜 y y := by
      rw [hx, inner_toEuclideanLin_apply, hQ]
      simp
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖x‖ ^ 2 = ‖y‖ ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'
  have hx1 : ‖x‖ = 1 := hxy.trans hy1
  have hx0 : x ≠ 0 := by rintro h; rw [h, norm_zero] at hx1; exact zero_ne_one hx1
  have hres : toEuclideanLin A x - ((hS.eigenvalues k : ℝ) : 𝕜) • x =
      toEuclideanLin (A * Q₁ - Q₁ * S) y := by
    have hSy : S *ᵥ ⇑y = ((hS.eigenvalues k : ℝ) : 𝕜) • ⇑y := by
      rw [hS.mulVec_eigenvectorBasis k, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    apply WithLp.ofLp_injective 2
    simp only [hx, WithLp.ofLp_sub, WithLp.ofLp_smul, toLpLin_apply, WithLp.ofLp_toLp,
      sub_mulVec, ← mulVec_mulVec, hSy, mulVec_smul]
  obtain ⟨μ, hμ, hμle⟩ := (isSymmetric_toEuclideanLin_iff.mpr hA).exists_hasEigenvalue_dist_le
    (hS.eigenvalues k) hx0
  have hμsp : μ ∈ spectrum 𝕜 A := by
    rw [← spectrum_toLpLin (p := 2)]
    exact hμ.mem_spectrum
  rw [hA.spectrum_eq_image_range] at hμsp
  obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hμsp
  refine ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i, ?_⟩
  rw [hres, hx1, div_one, ← RCLike.ofReal_sub, RCLike.norm_ofReal] at hμle
  refine hμle.trans ((norm_toEuclideanLin_apply_le _ _).trans ?_)
  rw [hy1, mul_one, ← lpOpNorm_two]
  exact hε

end Matrix
