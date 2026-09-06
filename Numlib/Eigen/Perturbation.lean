import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Projection.Angle
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Eigen.Normal

/-!
# Eigenvalue perturbation and a posteriori bounds

Residual bounds for approximate eigenpairs of symmetric operators
(Saad, *Numerical Methods for Large Eigenvalue Problems*[^saad-eigenvalue], Cor 3.3, Lemma 3.2,
Thm 3.8–3.9 for Kato–Temple; Meurant–Strakoš[^meurant-strakos] §2.1; Choi[^choi] §2.4),
Bauer–Fike for diagonalizable matrices (Saad, *Large Eigenvalue Problems*, Thm 3.6;
Kress[^kress] Problem 7.6), the backward error of an approximate eigenpair
(Saad, *Large Eigenvalue Problems*, Prop 3.4), Bendixson
(Saad, *Iterative Methods for Sparse Linear Systems*[^saad-iterative], Thm 1.35) and
Rayleigh-quotient bounds.

Throughout, an approximate eigenpair of `A` is a unit vector `x` together with a scalar `θ`
(usually the Rayleigh quotient `θ = re⟪A x, x⟫`), and `r = A x - θ x` is its residual; the
bounds below turn `‖r‖` into a distance from `θ` to the spectrum.

## The eigenvector, the condition numbers and the pseudospectrum

`LinearMap.IsSymmetric.sin_angle_le_norm_residual_div` is the residual bound for the eigen*vector*
(Saad, *Large Eigenvalue Problems*, Thm 3.9): a small residual and a separated eigenvalue force a
small angle between `x` and the eigenspace.  The subspace really has to be the eigenspace and not
the line through a single eigenvector, which is what the printed statement uses; the two agree
exactly when the eigenvalue is simple, and that case is
`LinearMap.IsSymmetric.sin_angle_span_singleton_le_norm_residual_div`.  The theorem's doc comment
carries the three-by-three counterexample to the line form at a multiple eigenvalue.

`Module.End.eigenvalueCondNumber` is the sensitivity of a simple eigenvalue (Saad, Def 3.1), the
reciprocal cosine of the angle between the right and the left eigenvector.  It is at least one,
it is one for a normal operator, and it is what bounds the first-order motion of the eigenvalue
under a perturbation: `Module.End.deriv_eigenvalue_perturbation` computes the derivative of a
differentiable branch of eigenvalues of `A + t B` as `⟪w, B u⟫ / ⟪w, u⟫`, and
`Module.End.norm_deriv_eigenvalue_perturbation_le` bounds it by `‖B‖` times the condition number.
The branch is a hypothesis, not a conclusion: producing it needs the implicit function theorem on
`det (A + t B - μ)`, and the plan records that as still open.

`ContinuousLinearMap.pseudospectrum` is the `ε`-pseudospectrum (Saad, Def 3.3).  It is defined by
the approximate-eigenvector form `∃ w, ‖w‖ = 1 ∧ ‖A w - z w‖ < ε`, his (3.55), rather than by the
resolvent norm, so that no convention about the resolvent on the spectrum is needed;
`ContinuousLinearMap.mem_pseudospectrum_iff` is the backward-error characterization of his
Prop 3.7, with the strict inequality `‖B‖ < ε` that the equivalence actually needs.

Two books by Saad are cited in this file and are kept apart by their short titles:
*Large Eigenvalue Problems* and *Iterative Methods*.  Bauer–Fike, Gershgorin, Kato–Temple and
Bendixson are the classical names of the results; the numbered forms used here are the ones
proved in the cited texts.

## References

[^saad-eigenvalue]: Yousef Saad, *Numerical Methods for Large Eigenvalue Problems*, 2nd edition,
  SIAM, 2011.
[^meurant-strakos]: Gérard Meurant and Zdeněk Strakoš, *The Lanczos and conjugate gradient
  algorithms in finite precision arithmetic*, Acta Numerica (2006), 471–542.
[^choi]: Sou-Cheng Choi, *Iterative Methods for Singular Linear Equations and Least-Squares
  Problems*, PhD thesis, Stanford University, 2006.
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The sine of the angle depends only on the subspace, so two spellings of the same subspace give
the same value even when their `HasOrthogonalProjection` instances are found by different routes.
Rewriting a subspace under `sinAngle` directly fails, the instance argument depending on it.
This is the twin of `Submodule.tanAngle_congr`. -/
theorem Submodule.sinAngle_congr {K L : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (h : K = L) (u : E) : K.sinAngle u = L.sinAngle u := by
  subst h
  rfl

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
include hA

/-! ### Diagonalization bookkeeping

All the symmetric bounds below are inequalities between the sums
`∑ i, f (λ i) ‖⟪v i, x⟫‖²` over an orthonormal eigenbasis `v` with eigenvalues `λ`. -/

private theorem sum_norm_repr_sq {n : ℕ} (hn : Module.finrank 𝕜 E = n) (x : E) :
    ∑ i, ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
  simpa only [OrthonormalBasis.repr_apply_apply] using
    (hA.eigenvectorBasis hn).sum_sq_norm_inner_right x

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
  rw [← hA.sum_norm_repr_sq hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA.repr_sub_smul hn, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]

private theorem re_inner_apply_self {n : ℕ} (hn : Module.finrank 𝕜 E = n) (x : E) :
    RCLike.re (inner 𝕜 (A x) x) =
      ∑ i, hA.eigenvalues hn i * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  rw [← (hA.eigenvectorBasis hn).sum_inner_mul_inner (A x) x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA x (hA.eigenvectorBasis hn i), hA.apply_eigenvectorBasis hn, inner_smul_right,
    ← inner_conj_symm x (hA.eigenvectorBasis hn i), mul_assoc, RCLike.conj_mul,
    OrthonormalBasis.repr_apply_apply]
  simp

/-- The identity behind Saad, *Large Eigenvalue Problems*, Lemma 3.2 and the Kato–Temple bounds:
for a unit vector `x` with Rayleigh quotient `θ = re⟪A x, x⟫`, residual `r = A x - θ x` and
eigenbasis coefficients `c`, `∑ (λ - u)(λ - v) ‖c‖² = ‖r‖² + (θ - u)(θ - v)`. -/
private theorem sum_quadratic {n : ℕ} (hn : Module.finrank 𝕜 E = n) {x : E} (hx : ‖x‖ = 1)
    (u v : ℝ) :
    ∑ i, (hA.eigenvalues hn i - u) * (hA.eigenvalues hn i - v) *
        ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 =
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 +
        (RCLike.re (inner 𝕜 (A x) x) - u) * (RCLike.re (inner 𝕜 (A x) x) - v) := by
  set θ := RCLike.re (inner 𝕜 (A x) x) with hθ
  have hs : ∑ i, ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 = 1 := by
    rw [hA.sum_norm_repr_sq hn, hx, one_pow]
  have hth : ∑ i, hA.eigenvalues hn i * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 = θ :=
    (hA.re_inner_apply_self hn x).symm
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

/-- Residual bound (Saad, *Large Eigenvalue Problems*, Cor 3.3): some eigenvalue lies within
`‖A x - θ x‖ / ‖x‖` of `θ`. -/
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
    rw [mul_pow, sq_abs, ← hA.sum_norm_repr_sq hn, hA.norm_residual_sq hn, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have habs := hi₀ i (Finset.mem_univ i)
    nlinarith [abs_nonneg (hA.eigenvalues hn i₀ - θ), abs_nonneg (hA.eigenvalues hn i - θ),
      sq_abs (hA.eigenvalues hn i₀ - θ), sq_abs (hA.eigenvalues hn i - θ)]
  have hsq := Real.sqrt_le_sqrt key
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)] at hsq

/-- Saad, *Large Eigenvalue Problems*, Lemma 3.2: with `θ = re⟪A x, x⟫` (`‖x‖ = 1`) and an
interval `(α, β) ∋ θ` free of eigenvalues, `(β - θ)(θ - α) ≤ ‖r‖²` for the residual
`r = A x - θ x`. -/
theorem rayleigh_gap_le_norm_residual_sq {x : E} (hx : ‖x‖ = 1) {α β : ℝ}
    (hαβ : α < RCLike.re (inner 𝕜 (A x) x) ∧ RCLike.re (inner 𝕜 (A x) x) < β)
    (hfree : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∉ Set.Ioo α β) :
    (β - RCLike.re (inner 𝕜 (A x) x)) * (RCLike.re (inner 𝕜 (A x) x) - α) ≤
      ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 := by
  set n := Module.finrank 𝕜 E with hn'
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
/-- Kato–Temple (Saad, *Large Eigenvalue Problems*, Thm 3.8): if `(a, b)` contains the Rayleigh
quotient `θ = re⟪A x, x⟫` of a unit vector `x` and exactly one eigenvalue `λ`, then
`-‖r‖²/(b - θ) ≤ λ - θ ≤ ‖r‖²/(θ - a)` for the residual `r = A x - θ x`.

The denominators here are the ones the proof produces: the *lower* bound is controlled by the
distance from `θ` to the right end `b`, and the *upper* bound by the distance to the left end `a`.
Exchanging the two denominators gives a false statement: for `A = diag(0, 10)` and `x` with
`‖x‖ = 1`, `x₂² = 3/5`, one gets `θ = 6`, `‖r‖² = 24`,
and `(a, b) = (5, 20)` contains only the eigenvalue `10`, yet `10 - 6 = 4 > 24/(20 - 6)`. -/
theorem kato_temple {x : E} (hx : ‖x‖ = 1) {a b : ℝ} {μ : 𝕜} (hμ : Module.End.HasEigenvalue A μ)
    (hab : a < RCLike.re (inner 𝕜 (A x) x) ∧ RCLike.re (inner 𝕜 (A x) x) < b)
    (hμab : RCLike.re μ ∈ Set.Ioo a b)
    (hunique : ∀ μ' : 𝕜, Module.End.HasEigenvalue A μ' → RCLike.re μ' ∈ Set.Ioo a b → μ' = μ) :
    -(‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 / (b - RCLike.re (inner 𝕜 (A x) x))) ≤
        RCLike.re μ - RCLike.re (inner 𝕜 (A x) x) ∧
      RCLike.re μ - RCLike.re (inner 𝕜 (A x) x) ≤
        ‖A x - (RCLike.re (inner 𝕜 (A x) x) : 𝕜) • x‖ ^ 2 /
          (RCLike.re (inner 𝕜 (A x) x) - a) := by
  set n := Module.finrank 𝕜 E with hn'
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

/-- Saad, *Large Eigenvalue Problems*, Cor 3.4: `|λ - θ| ≤ ‖r‖² / δ`, where `θ = re⟪A x, x⟫` is
the Rayleigh quotient of a unit vector `x`, `r = A x - θ x` its residual, and `δ` the gap from
`θ` to the eigenvalues other than `λ`. -/
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
  set n := Module.finrank 𝕜 E with hn'
  have hn : Module.finrank 𝕜 E = n := rfl
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  have hbounds : ∀ i : Fin n, hA.eigenvalues hn i ∈ Set.Icc lmin lmax := by
    intro i
    have := hspec ((hA.eigenvalues hn i : ℝ) : 𝕜) (hA.hasEigenvalue_eigenvalues hn i)
    rwa [RCLike.ofReal_re] at this
  rw [Set.mem_Icc]
  constructor
  · rw [le_div_iff₀ hpos, hA.re_inner_apply_self hn, ← hA.sum_norm_repr_sq hn, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hbounds i).1 (sq_nonneg _)
  · rw [div_le_iff₀ hpos, hA.re_inner_apply_self hn, ← hA.sum_norm_repr_sq hn, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hbounds i).2 (sq_nonneg _)

/-! ### The eigenvector residual bound

A small residual forces the approximate eigenvector to be close to an eigenspace, provided the
corresponding eigenvalue is separated from the rest of the spectrum. -/

/-- On the orthogonal complement of the `lam`-eigenspace the shifted operator `A - θ` is bounded
below by the separation `δ` of `lam` from the other eigenvalues: `δ ‖q‖ ≤ ‖(A - θ) q‖`.

In the eigenvector basis the coordinates of `q` vanish at every index whose eigenvalue is `lam`,
so the sum defining `‖(A - θ) q‖²` runs only over the indices where the separation applies. -/
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
    rw [mul_pow, hA.norm_residual_sq hn θ q, ← hA.sum_norm_repr_sq hn q, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : hA.eigenvalues hn i = lam
    · rw [hzero i hi]
      simp
    · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have h := hsep i hi
      nlinarith [sq_abs (hA.eigenvalues hn i - θ), abs_nonneg (hA.eigenvalues hn i - θ)]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (mul_nonneg hδ (norm_nonneg q)), Real.sqrt_sq (norm_nonneg _)] at h

/-- **The eigenvector residual bound** (Saad, *Large Eigenvalue Problems*, Thm 3.9): for a unit
vector `x` with Rayleigh quotient `θ = re⟪A x, x⟫` and residual `r = A x - θ x`, and a real
number `lam` separated by `δ > 0` from every eigenvalue of `A` other than `lam` itself,
`sin ∠(x, ker (A - lam)) ≤ ‖r‖/δ`.

The subspace is the **eigenspace** of `lam`, not the line through one eigenvector for it: with a
multiple eigenvalue the statement about a line is false, as `A = diag(1, 1, 5)` with `x` the
second basis vector shows -- there `r = 0` and `δ = 4`, yet the angle to the line through the
first basis vector is a right angle.  Saad takes `δ` to bound `A - θ` from below on the orthogonal
complement of that line, which it does only when `lam` is a simple eigenvalue; the simple case is
`sin_angle_span_singleton_le_norm_residual_div` below.

No hypothesis says that `lam` is an eigenvalue at all.  When it is not, the eigenspace is `⊥`,
the left-hand side is `1`, and the separation applies at every index, so the bound still holds.

The proof splits `x` into `p + q` along the eigenspace and its complement.  The residual splits
accordingly as `(lam - θ) p + (A - θ) q`, whose two terms are orthogonal because the eigenspace of
a symmetric operator is invariant and so is its complement, and Pythagoras then discards the `p`
term. -/
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

/-- **The eigenvector residual bound at a simple eigenvalue**, which is Saad, *Large Eigenvalue
Problems*, Thm 3.9 as printed: when the `lam`-eigenspace is a line, the angle it bounds is the
angle to any eigenvector `u` for `lam`.

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

/-- Backward error of an approximate eigenpair (Saad, *Large Eigenvalue Problems*, Prop 3.4):
the least `‖ΔA‖` with `(A - ΔA) u = θ u` (`‖u‖ = 1`) is `‖A u - θ u‖`, attained by the rank-one
perturbation `r uᴴ` built from the residual `r = A u - θ u`. -/
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

/-- Bendixson's theorem (Saad, *Iterative Methods*, Thm 1.35): the real part of every eigenvalue
of a bounded operator lies between the extreme eigenvalues of its symmetric part
`H = (A + A†)/2`. -/
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

Saad, *Large Eigenvalue Problems*, Def 3.1 measures the sensitivity of a simple eigenvalue by
`‖u‖ ‖w‖ / |⟪w, u⟫|` for a right eigenvector `u` and a left eigenvector `w`, that is, by the
reciprocal cosine of the angle between them.  The quantity is scale invariant, so it depends on
the eigenvalue alone whenever the eigenvalue is simple, its two eigenvectors being determined up
to scale. -/

/-- **The condition number of a simple eigenvalue** (Saad, *Large Eigenvalue Problems*, Def 3.1):
`‖u‖ ‖w‖ / ‖⟪w, u⟫‖` for a right eigenvector `u` (`A u = μ u`) and a left eigenvector `w`
(`A† w = conj μ • w`).

The definition mentions neither the operator nor the eigenvalue, because it does not depend on
them: it is `1 / cos ∠(u, w)`, and by `Module.End.eigenvalueCondNumber_smul` it is unchanged when
either eigenvector is rescaled, so at a *simple* eigenvalue — where each of the two eigenvectors
spans a line — it is a function of the eigenvalue.  The junk value at `⟪w, u⟫ = 0` is `0`;
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
eigenvectors span the same line (`LinearMap.IsStarNormal.eigenspace_adjoint`), so the angle
between them is zero and the condition number is `1`. -/
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

Along a differentiable branch of eigenpairs of `A + t B` the eigenvalue moves at the rate
`⟪w, B u⟫ / ⟪w, u⟫`, whose modulus is at most `‖B‖` times the condition number of the eigenvalue.
Saad, *Large Eigenvalue Problems*, §3.2.1 displays exactly this computation.

The branch is assumed here, not constructed: producing it from the simplicity of the eigenvalue is
the implicit function theorem applied to `(t, μ) ↦ det (A + t B - μ)`, whose `μ`-derivative at
`(0, λ)` is nonzero precisely because the root is simple. -/

/-- **The derivative of a simple eigenvalue** (Saad, *Large Eigenvalue Problems*, §3.2.1): along a
differentiable branch `t ↦ (μ t, u t)` of eigenpairs of `A + t B`, with `w` a left eigenvector of
`A` for `λ = μ 0` not orthogonal to `u 0`, the eigenvalue's derivative at `0` is
`⟪w, B (u 0)⟫ / ⟪w, u 0⟫`.

The left-eigenvector hypothesis is stated as `⟪w, A y⟫ = λ ⟪w, y⟫` for every `y`, which is what
the proof tests the differentiated eigenvalue equation against; it is equivalent to
`A† w = conj λ • w` in finite dimension, and needs no adjoint to state.

Differentiating `A (u t) + t B (u t) = μ t • u t` at `t = 0` gives
`A u' + B (u 0) = μ 0 • u' + μ' • u 0`, and testing against `w` cancels the two terms carrying
the unknown `u'`. -/
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

/-- **The condition number bounds the first-order sensitivity** (Saad, *Large Eigenvalue
Problems*, §3.2.1): the rate at which a simple eigenvalue moves under the perturbation `t B` is at
most `‖B‖` times its condition number.

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

end Module.End

/-! ### Pseudospectra

The `ε`-pseudospectrum of `A` (Saad, *Large Eigenvalue Problems*, Def 3.3) is the set of scalars
that are eigenvalues of some perturbation of `A` of norm below `ε`.  Saad defines it by the
resolvent, `‖(A - z)⁻¹‖ > ε⁻¹`, with the convention that the resolvent norm is infinite on the
spectrum; the equivalent form taken here as the definition,

`z ∈ pseudospectrum ε A ↔ ∃ w, ‖w‖ = 1 ∧ ‖A w - z w‖ < ε`,

is his (3.55), needs no convention at the spectrum — an exact eigenvector has residual `0` — and
is what the perturbation statements consume. -/

/-- The **`ε`-pseudospectrum** of `A` (Saad, *Large Eigenvalue Problems*, Def 3.3, in the form of
his (3.55)): the scalars `z` for which some unit vector is an eigenvector to within `ε`.

`ContinuousLinearMap.mem_pseudospectrum_iff` identifies this with the backward-error form, and
`ContinuousLinearMap.spectrum_subset_pseudospectrum` records that it contains the spectrum,
which is why no convention about the resolvent at the spectrum is needed. -/
def ContinuousLinearMap.pseudospectrum (ε : ℝ) (A : E →L[𝕜] E) : Set 𝕜 :=
  {z | ∃ w : E, ‖w‖ = 1 ∧ ‖A w - z • w‖ < ε}

namespace ContinuousLinearMap

/-- Membership in the pseudospectrum, unfolded. -/
theorem mem_pseudospectrum {ε : ℝ} {A : E →L[𝕜] E} {z : 𝕜} :
    z ∈ pseudospectrum ε A ↔ ∃ w : E, ‖w‖ = 1 ∧ ‖A w - z • w‖ < ε := Iff.rfl

/-- **The backward-error characterization of the pseudospectrum** (Saad, *Large Eigenvalue
Problems*, Prop 3.7, (iv) ↔ (v)): `z` is in the `ε`-pseudospectrum exactly when it is an
eigenvalue of some `A - B` with `‖B‖ < ε`.

Forwards, the perturbation is the rank-one one of `isLeast_eigen_backwardError`, built from the
residual of the approximate eigenvector; backwards, an eigenvector of `A - B` has residual `B w`
for `A`.  The book states (v) with `‖B‖ ≤ ε`, but its own proof of (v) ⇒ (iv) needs the strict
inequality, and with `≤` the equivalence is false: for `A = 0` and `B = ε • 1` every `z` of
modulus `ε` satisfies the right-hand side and none satisfies the left. -/
theorem mem_pseudospectrum_iff {ε : ℝ} (A : E →L[𝕜] E) (z : 𝕜) :
    z ∈ pseudospectrum ε A ↔
      ∃ B : E →L[𝕜] E, ‖B‖ < ε ∧ Module.End.HasEigenvalue ((A - B : E →L[𝕜] E) :
        E →ₗ[𝕜] E) z := by
  constructor
  · rintro ⟨w, hw, hlt⟩
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    refine ⟨InnerProductSpace.rankOne 𝕜 (A w - z • w) w, ?_, ?_⟩
    · rwa [InnerProductSpace.norm_rankOne, hw, mul_one]
    · have huu : (inner 𝕜 w w : 𝕜) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hw]; norm_num
      refine Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 ?_, hw0⟩
      simp only [ContinuousLinearMap.coe_coe, sub_apply, InnerProductSpace.rankOne_apply, huu,
        one_smul, sub_sub_cancel]
  · rintro ⟨B, hB, hz⟩
    obtain ⟨w, hw, hw0⟩ := hz.exists_hasEigenvector
    have hval : A w - B w = z • w := by
      have := Module.End.mem_eigenspace_iff.1 hw
      simpa using this
    have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
    refine ⟨(‖w‖ : 𝕜)⁻¹ • w, ?_, ?_⟩
    · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg w),
        inv_mul_cancel₀ hn]
    · have hres : A ((‖w‖ : 𝕜)⁻¹ • w) - z • (‖w‖ : 𝕜)⁻¹ • w
          = (‖w‖ : 𝕜)⁻¹ • B w := by
        rw [map_smul, smul_comm z, ← smul_sub]
        congr 1
        rw [← hval]
        abel
      rw [hres, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg w)]
      calc ‖w‖⁻¹ * ‖B w‖ ≤ ‖w‖⁻¹ * (‖B‖ * ‖w‖) := by
            gcongr
            exact B.le_opNorm w
        _ = ‖B‖ := by field_simp
        _ < ε := hB

/-- Every eigenvalue lies in every pseudospectrum of positive radius: an exact eigenvector has
residual `0`.  With `Module.End.hasEigenvalue_iff_mem_spectrum` this is the inclusion
`σ(A) ⊆ Λ_ε(A)`, and it is the reason the residual form of the definition needs no convention
about the resolvent norm on the spectrum. -/
theorem mem_pseudospectrum_of_hasEigenvalue {ε : ℝ} (hε : 0 < ε) {A : E →L[𝕜] E} {z : 𝕜}
    (hz : Module.End.HasEigenvalue (A : E →ₗ[𝕜] E) z) : z ∈ pseudospectrum ε A := by
  obtain ⟨w, hw, hw0⟩ := hz.exists_hasEigenvector
  have hval : A w = z • w := by simpa using Module.End.mem_eigenspace_iff.1 hw
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
  refine ⟨(‖w‖ : 𝕜)⁻¹ • w, ?_, ?_⟩
  · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg w),
      inv_mul_cancel₀ hn]
  · rw [map_smul, smul_comm z, hval, sub_self, norm_zero]
    exact hε

end ContinuousLinearMap

namespace Matrix

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Bauer–Fike (Saad, *Large Eigenvalue Problems*, Thm 3.6; Kress, *Numerical Analysis*,
Problem 7.6): for a diagonalizable `A = X D X⁻¹` and `μ ∈ σ(A + ΔA)`,
`dist(μ, σ(A)) ≤ κ₂(X) ‖ΔA‖₂`, where `κ₂(X) = ‖X‖₂ ‖X⁻¹‖₂`. -/
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
  have hXXinv : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hXd
  set w := X⁻¹ *ᵥ v with hw
  have hvw : X *ᵥ w = v := by rw [hw, Matrix.mulVec_mulVec, hXXinv, Matrix.one_mulVec]
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

/-- Residual form of Bauer–Fike: for a unit approximate eigenpair `(θ, u)` of a diagonalizable
`A = X D X⁻¹`, `dist(θ, σ(A)) ≤ κ₂(X) ‖A u - θ u‖`, where `κ₂(X) = ‖X‖₂ ‖X⁻¹‖₂`. -/
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

/-- Gershgorin discs, union form (Saad, *Large Eigenvalue Problems*, Thm 3.11; Kress,
*Numerical Analysis*, Thm 7.7): the spectrum is contained in the union over `i` of the discs
centred at `a_ii` with radius `∑_{j ≠ i} |a_ij|`.  Mathlib's `eigenvalue_mem_ball` is the
pointwise version. -/
theorem spectrum_subset_iUnion_closedBall (A : Matrix n n ℂ) :
    spectrum ℂ A ⊆ ⋃ i, Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖) := by
  intro μ hμ
  rw [← Matrix.spectrum_toLin'] at hμ
  obtain ⟨i, hi⟩ := _root_.eigenvalue_mem_ball (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ)
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- The column-sum Gershgorin theorem (Saad, *Large Eigenvalue Problems*, Thm 3.11; Saad,
*Iterative Methods*, Thm 4.6, column form): the spectrum is contained in the union over `j` of the
discs centred at `a_jj` with radius `∑_{i ≠ j} |a_ij|`.

A matrix and its transpose have the same spectrum, so this is the row form applied to the
transpose. -/
theorem spectrum_subset_iUnion_closedBall_col (A : Matrix n n ℂ) :
    spectrum ℂ A ⊆ ⋃ j, Metric.closedBall (A j j) (∑ i ∈ Finset.univ.erase j, ‖A i j‖) := by
  intro μ hμ
  have hT : μ ∈ spectrum ℂ Aᵀ := by rwa [Matrix.spectrum_transpose]
  simpa using spectrum_subset_iUnion_closedBall Aᵀ hT

end Matrix
