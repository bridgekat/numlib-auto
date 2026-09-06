import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.RingTheory.Polynomial.Chebyshev
import Numlib.Analysis.SpecialFunctions.Chebyshev
import Numlib.LinearAlgebra.Matrix.KroneckerSum
import Numlib.LinearAlgebra.Matrix.MMatrix
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz
import NumlibSurface.SaadSparse.Chapter02.Section05

/-!
# Saad §2.2: finite difference methods

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §2.2: the truncation errors of §2.2.1–2.2.2, the one-dimensional model matrix of §2.2.3, the
exactly solvable convection–diffusion problem of §2.2.4, the two-dimensional five-point matrix of
§2.2.5, and the spectral facts of §2.2.6 on which the fast Poisson solvers rest.

The chapter states no numbered result, so what matters here are the *definitions*:
`SaadSparse.Chapter02.laplacian1D`, `SaadSparse.Chapter02.laplacian2D` and the block
`SaadSparse.Chapter02.blockB` of (2.27) are cited by Chapters 4, 6, 10, 12 and 13, and every
numerical experiment of the book runs on them.  They carry the `1/h²` scaling on the matrix, as the
displays of §2.2.3 and §2.2.5 do; §2.2.6 scales it away, and `SaadSparse.Chapter02.laplacian2D_smul`
relates the two conventions.

The spectral work is the backbone's.  `Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz` has the
eigenpairs of `tridiag(a, b, a)` and the orthogonality of the discrete sine basis, and
`Numlib/LinearAlgebra/Matrix/KroneckerSum` has the eigenvalues of a Kronecker sum.  Saad gives the
eigenvalues only for the block `B = tridiag(-1, 4, -1)` of (2.27); the corresponding statements for
the one-dimensional Laplacean (`laplacian1D_posDef`, `laplacian1D_mulVec_sineVec`) and for the
two-dimensional matrix (`laplacian2D_eq_kroneckerSum`) are not in the book at all and are recorded
here as what the backbone supplies.

The two-dimensional grid is indexed by the **product type** `Fin n₁ × Fin n₂`, not by
`Fin (n₁ * n₂)`: that is what `Numlib.LinearAlgebra.Matrix.KroneckerSum` is stated over, and Saad's
lexicographic vector ordering is then a reindexing along a `Fin`-product equivalence, a definition
rather than a theorem, which nothing downstream needs. The first coordinate is the `x` direction,
with mesh `h₁`, and it is also the block index of the block form (2.26).

Textual points fixed here rather than reproduced: the interior index range of §2.2.5 is printed as
`0 < i < n₁`, which is off by one; the decoupled systems (2.29) are printed with the two indices
transposed and are stated here as `p` systems of size `m`, which is what Algorithm 2.1 line 2 says;
and the `1/h²` scaling of §2.2.3, which the book writes on the right-hand side of the scalar
equation and on the matrix in the display, is used in the matrix convention only.

Two claims of the chapter are here only in part, and the reasons are with them: the sixth-order
accuracy of the nine-point stencil (d) of Figure 2.4 on harmonic functions, which needs the
equality of mixed partial derivatives in a form Mathlib does not have for a curried
`u : ℝ → ℝ → ℝ` (the second-order accuracy of both nine-point stencils *is* proved,
`ninePointC_error` and `ninePointD_error`); and the stability of plain block cyclic reduction
against Buneman's variant, which the book asserts with no analysis anywhere.

The module imports §2.5 for the positive/negative-part identity
`SaadSparse.Chapter02.equation_2_53`, which is the same algebraic fact as the upwind combination
(2.22) and is proved there once.
-/

open Finset Matrix Polynomial
open scoped Kronecker Matrix Real

namespace SaadSparse.Chapter02

/-! ### §2.2.1–2.2.2 Truncation errors of the difference formulas

Saad's derivations are Taylor expansions with a Lagrange remainder, so each statement below names
the intermediate point that the remainder is evaluated at, exactly as the book's displays do. -/

section Truncation

/-- The Taylor expansion with a Lagrange remainder, in the form the difference formulas need: for
`u` of class `C^(k+1)` and `t ≠ 0`, the value `u (x + t)` differs from its `k`-th Taylor
polynomial at `x` by `t ^ (k + 1) / (k + 1)! * u^(k+1)(ξ)` for some `ξ` strictly between `x` and
`x + t`. -/
private theorem exists_taylor {u : ℝ → ℝ} {k : ℕ} (hu : ContDiff ℝ (k + 1 : ℕ) u) (x : ℝ)
    {t : ℝ} (ht : t ≠ 0) :
    ∃ ξ ∈ Set.uIoo x (x + t),
      u (x + t) = (∑ i ∈ Finset.range (k + 1), t ^ i / (Nat.factorial i : ℝ) * iteratedDeriv i u x)
        + t ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) * iteratedDeriv (k + 1) u ξ := by
  have hne : x ≠ x + t := fun he => ht (by linarith)
  have hUD : UniqueDiffOn ℝ (Set.uIcc x (x + t)) := uniqueDiffOn_Icc (inf_lt_sup.2 hne)
  have hle : ((k : ℕ) : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast Nat.le_succ k
  have hwithin : ∀ (m : ℕ), m ≤ k + 1 → ∀ y ∈ Set.uIcc x (x + t),
      iteratedDerivWithin m u (Set.uIcc x (x + t)) y = iteratedDeriv m u y := fun m hm y hy =>
    iteratedDerivWithin_eq_iteratedDeriv hUD
      (hu.of_le (by exact_mod_cast hm)).contDiffAt hy
  have hcd : ContDiffOn ℝ (k : ℕ) u (Set.uIcc x (x + t)) := (hu.of_le hle).contDiffOn
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin k u (Set.uIcc x (x + t)))
      (Set.uIoo x (x + t)) :=
    ((hu.differentiable_iteratedDeriv' k).differentiableOn).congr fun y hy =>
      hwithin k (Nat.le_succ k) y (Set.Ioo_subset_Icc_self hy)
  obtain ⟨ξ, hξ, hval⟩ := taylor_mean_remainder_lagrange hne hcd hdiff
  refine ⟨ξ, hξ, ?_⟩
  rw [taylor_within_apply] at hval
  have hsum : ∑ i ∈ Finset.range (k + 1),
      ((Nat.factorial i : ℝ)⁻¹ * (x + t - x) ^ i) • iteratedDerivWithin i u (Set.uIcc x (x + t)) x
      = ∑ i ∈ Finset.range (k + 1), t ^ i / (Nat.factorial i : ℝ) * iteratedDeriv i u x := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i < k + 1 := Finset.mem_range.1 hi
    rw [hwithin i (by omega) x Set.left_mem_uIcc, smul_eq_mul, add_sub_cancel_left]
    ring
  rw [hsum, hwithin (k + 1) le_rfl ξ (Set.Ioo_subset_Icc_self hξ), add_sub_cancel_left] at hval
  have hfin : t ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) * iteratedDeriv (k + 1) u ξ
      = iteratedDeriv (k + 1) u ξ * t ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by ring
  rw [hfin]
  linarith

/-- The mean value of the two remainders is attained, by the intermediate value theorem applied
to the continuous top derivative.  This is the step Saad flags when adding the two expansions of
the centered differences. -/
private theorem exists_mid {u : ℝ → ℝ} {m : ℕ} (hu : ContDiff ℝ (m : ℕ) u) {a b x h : ℝ}
    (ha : a ∈ Set.Ioo (x - h) x) (hb : b ∈ Set.Ioo x (x + h)) :
    ∃ ξ ∈ Set.Icc (x - h) (x + h),
      iteratedDeriv m u ξ = (iteratedDeriv m u b + iteratedDeriv m u a) / 2 := by
  have hcont : Continuous (iteratedDeriv m u) := hu.continuous_iteratedDeriv m le_rfl
  have havg : (iteratedDeriv m u b + iteratedDeriv m u a) / 2
      ∈ Set.uIcc (iteratedDeriv m u a) (iteratedDeriv m u b) := by
    rcases le_total (iteratedDeriv m u a) (iteratedDeriv m u b) with hle | hle
    · rw [Set.uIcc_of_le hle]; constructor <;> linarith
    · rw [Set.uIcc_of_ge hle]; constructor <;> linarith
  obtain ⟨ξ, hmem, hveq⟩ := intermediate_value_uIcc hcont.continuousOn havg
  refine ⟨ξ, ?_, hveq⟩
  rcases Set.mem_uIcc.1 hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    exact ⟨by linarith [ha.1, ha.2, hb.1, hb.2], by linarith [ha.1, ha.2, hb.1, hb.2]⟩

/-- Saad (2.9)–(2.10): the forward difference is a first-order approximation of the derivative.
For `u` of class `C³` and `h > 0` there is `ξ` in `(x, x + h)` with
`(u(x + h) - u(x))/h = u'(x) + (h/2) u''(x) + (h²/6) u'''(ξ)`; in particular the error is
`(h/2) u''(x) + O(h²)`, which is first order in `h`.  The backward form (2.11) is the same
statement at `-h`. -/
theorem equation_2_10 {u : ℝ → ℝ} (hu : ContDiff ℝ 3 u) (x : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ ξ ∈ Set.Ioo x (x + h),
      (u (x + h) - u x) / h
        = deriv u x + h / 2 * iteratedDeriv 2 u x + h ^ 2 / 6 * iteratedDeriv 3 u ξ := by
  have hu3 : ContDiff ℝ ((2 : ℕ) + 1 : ℕ) u := by exact_mod_cast hu
  obtain ⟨ξ, hξ, hval⟩ := exists_taylor hu3 x (ne_of_gt hh)
  rw [Set.uIoo_of_le (by linarith)] at hξ
  refine ⟨ξ, hξ, ?_⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at hval
  simp only [iteratedDeriv_zero, iteratedDeriv_one] at hval
  norm_num [Nat.factorial] at hval
  rw [div_eq_iff (ne_of_gt hh)]
  linear_combination hval

/-- Saad (2.12), the centered second difference: for `u` of class `C⁴` there is `ξ` in
`[x - h, x + h]` with
`(u(x + h) - 2u(x) + u(x - h))/h² = u''(x) + (h²/12) u⁗(ξ)`.
Two Lagrange remainders of order four, added; the two fourth-order terms are combined by the
intermediate value theorem applied to `u⁗`, which is the step the book flags.  This is the
truncation error of the model problem and the reason it is second order. -/
theorem equation_2_12 {u : ℝ → ℝ} (hu : ContDiff ℝ 4 u) (x : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ ξ ∈ Set.Icc (x - h) (x + h),
      (u (x + h) - 2 * u x + u (x - h)) / h ^ 2
        = iteratedDeriv 2 u x + h ^ 2 / 12 * iteratedDeriv 4 u ξ := by
  have hu4 : ContDiff ℝ ((3 : ℕ) + 1 : ℕ) u := by exact_mod_cast hu
  obtain ⟨b, hb, hvb⟩ := exists_taylor hu4 x (ne_of_gt hh)
  obtain ⟨a, ha, hva⟩ := exists_taylor hu4 x (neg_ne_zero.2 (ne_of_gt hh))
  rw [Set.uIoo_of_le (by linarith)] at hb
  rw [Set.uIoo_of_ge (by linarith), show x + -h = x - h by ring] at ha
  rw [show x + -h = x - h by ring] at hva
  obtain ⟨ξ, hξ, hmid⟩ := exists_mid (m := 4) (by exact_mod_cast hu) ha hb
  refine ⟨ξ, hξ, ?_⟩
  simp only [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one] at hvb hva
  norm_num [Nat.factorial] at hvb hva
  rw [hmid, div_eq_iff (by positivity : (h : ℝ) ^ 2 ≠ 0)]
  linear_combination hvb + hva

/-- Saad (2.13), the centered first difference: for `u` of class `C³` there is `ξ` in
`[x - h, x + h]` with `(u(x + h) - u(x - h))/(2h) = u'(x) + (h²/6) u'''(ξ)`, so the centered
formula is second order where the forward difference (2.8) of `equation_2_10` is only first
order.  Saad calls this "easy to show" and gives no proof; it is the difference of two Lagrange
remainders of order three. -/
theorem equation_2_13 {u : ℝ → ℝ} (hu : ContDiff ℝ 3 u) (x : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ ξ ∈ Set.Icc (x - h) (x + h),
      (u (x + h) - u (x - h)) / (2 * h) = deriv u x + h ^ 2 / 6 * iteratedDeriv 3 u ξ := by
  have hu3 : ContDiff ℝ ((2 : ℕ) + 1 : ℕ) u := by exact_mod_cast hu
  obtain ⟨b, hb, hvb⟩ := exists_taylor hu3 x (ne_of_gt hh)
  obtain ⟨a, ha, hva⟩ := exists_taylor hu3 x (neg_ne_zero.2 (ne_of_gt hh))
  rw [Set.uIoo_of_le (by linarith)] at hb
  rw [Set.uIoo_of_ge (by linarith), show x + -h = x - h by ring] at ha
  rw [show x + -h = x - h by ring] at hva
  obtain ⟨ξ, hξ, hmid⟩ := exists_mid (m := 3) (by exact_mod_cast hu) ha hb
  refine ⟨ξ, hξ, ?_⟩
  simp only [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one] at hvb hva
  norm_num [Nat.factorial] at hvb hva
  rw [hmid, div_eq_iff (by positivity : (2 : ℝ) * h ≠ 0)]
  linear_combination hvb - hva

/-- Saad Problem P-2.6: the conservative difference of (2.16) *is* the backward difference of the
staggered forward difference, `δ⁻(a_{i+1/2} δ⁺ u)`.  Writing
`g t = a (t + h/2) * (u (t + h) - u t)` for the staggered flux, the numerator of (2.16) is
`g x - g (x - h)`. -/
theorem equation_2_16_symm (a u : ℝ → ℝ) (x h : ℝ) :
    a (x + h / 2) * (u (x + h) - u x) - a (x - h / 2) * (u x - u (x - h))
      = (fun t => a (t + h / 2) * (u (t + h) - u t)) x
        - (fun t => a (t + h / 2) * (u (t + h) - u t)) (x - h) := by
  simp only
  ring_nf

/-- The divergence form `(a u')'` written out: `a' u' + a u''`. -/
private theorem deriv_mul_deriv {a u : ℝ → ℝ} (ha : ContDiff ℝ 4 a) (hu : ContDiff ℝ 4 u)
    (x : ℝ) : deriv (fun t => a t * deriv u t) x
      = deriv a x * deriv u x + a x * iteratedDeriv 2 u x := by
  have hda : DifferentiableAt ℝ a x := (ha.differentiable (by norm_num)).differentiableAt
  have hdu : DifferentiableAt ℝ (deriv u) x := by
    have hd := (hu.differentiable_iteratedDeriv 1 (by norm_num)).differentiableAt (x := x)
    rwa [iteratedDeriv_one] at hd
  have hm : HasDerivAt (fun t => a t * deriv u t)
      (deriv a x * deriv u x + a x * deriv (deriv u) x) x := hda.hasDerivAt.mul hdu.hasDerivAt
  rw [hm.deriv, iteratedDeriv_succ, iteratedDeriv_one]

/-- Saad (2.16) and Problem P-2.7: the conservative difference approximates the divergence form
`(a u')'` to **second** order.  For `a` and `u` of class `C⁴` and `h > 0` there are four points of
`[x - h, x + h]` with
`(a(x + h/2)(u(x+h) - u(x)) - a(x - h/2)(u(x) - u(x-h)))/h² - (a u')'(x) = h² · (…)`,
the bracket being a fixed polynomial in the values of `a`, `a'`, `a''(x)`, `a'''`, `a⁗`, `u'`,
`u''(x)`, `u'''`, `u⁗` at those points and at `x`, hence bounded independently of `h` on any
bounded range of steps.  The proof splits the difference into the *average* and the *half
difference* of the two staggered coefficients: the first multiplies the centered second difference
of `u` and the second the centered first difference, and all four are expanded by
`equation_2_12` and `equation_2_13`, at step `h/2` for `a` and at step `h` for `u`. -/
theorem equation_2_16 {a u : ℝ → ℝ} (ha : ContDiff ℝ 4 a) (hu : ContDiff ℝ 4 u) (x : ℝ)
    {h : ℝ} (hh : 0 < h) :
    ∃ ζ ∈ Set.Icc (x - h) (x + h), ∃ ζ' ∈ Set.Icc (x - h) (x + h),
      ∃ ξ ∈ Set.Icc (x - h) (x + h), ∃ ξ' ∈ Set.Icc (x - h) (x + h),
      (a (x + h / 2) * (u (x + h) - u x) - a (x - h / 2) * (u x - u (x - h))) / h ^ 2
          - deriv (fun t => a t * deriv u t) x
        = h ^ 2 * (a x * iteratedDeriv 4 u ξ / 12
            + (iteratedDeriv 2 a x + h ^ 2 / 48 * iteratedDeriv 4 a ζ)
              * (iteratedDeriv 2 u x + h ^ 2 / 12 * iteratedDeriv 4 u ξ) / 8
            + deriv a x * iteratedDeriv 3 u ξ' / 6
            + iteratedDeriv 3 a ζ' * (deriv u x + h ^ 2 / 6 * iteratedDeriv 3 u ξ') / 24) := by
  have hk : (0 : ℝ) < h / 2 := by linarith
  have hkne : (h / 2 : ℝ) ^ 2 ≠ 0 := by positivity
  have hkne' : (2 : ℝ) * (h / 2) ≠ 0 := by positivity
  have hhne : (h : ℝ) ^ 2 ≠ 0 := by positivity
  have hhne' : (2 : ℝ) * h ≠ 0 := by positivity
  obtain ⟨ζ, hζ, hA2⟩ := equation_2_12 ha x hk
  obtain ⟨ζ', hζ', hA1⟩ := equation_2_13 (ha.of_le (by norm_num)) x hk
  obtain ⟨ξ, hξ, hU2⟩ := equation_2_12 hu x hh
  obtain ⟨ξ', hξ', hU1⟩ := equation_2_13 (hu.of_le (by norm_num)) x hh
  rw [div_eq_iff hkne] at hA2
  rw [div_eq_iff hkne'] at hA1
  rw [div_eq_iff hhne] at hU2
  rw [div_eq_iff hhne'] at hU1
  refine ⟨ζ, ⟨by linarith [hζ.1], by linarith [hζ.2]⟩,
    ζ', ⟨by linarith [hζ'.1], by linarith [hζ'.2]⟩, ξ, hξ, ξ', hξ', ?_⟩
  have hAp : a (x + h / 2)
      = a x + h ^ 2 / 8 * (iteratedDeriv 2 a x + h ^ 2 / 48 * iteratedDeriv 4 a ζ)
        + h / 2 * (deriv a x + h ^ 2 / 24 * iteratedDeriv 3 a ζ') := by
    linear_combination (1 / 2 : ℝ) * hA2 + (1 / 2 : ℝ) * hA1
  have hAm : a (x - h / 2)
      = a x + h ^ 2 / 8 * (iteratedDeriv 2 a x + h ^ 2 / 48 * iteratedDeriv 4 a ζ)
        - h / 2 * (deriv a x + h ^ 2 / 24 * iteratedDeriv 3 a ζ') := by
    linear_combination (1 / 2 : ℝ) * hA2 - (1 / 2 : ℝ) * hA1
  have hUp : u (x + h) - u x
      = h ^ 2 / 2 * (iteratedDeriv 2 u x + h ^ 2 / 12 * iteratedDeriv 4 u ξ)
        + h * (deriv u x + h ^ 2 / 6 * iteratedDeriv 3 u ξ') := by
    linear_combination (1 / 2 : ℝ) * hU2 + (1 / 2 : ℝ) * hU1
  have hUm : u x - u (x - h)
      = h * (deriv u x + h ^ 2 / 6 * iteratedDeriv 3 u ξ')
        - h ^ 2 / 2 * (iteratedDeriv 2 u x + h ^ 2 / 12 * iteratedDeriv 4 u ξ) := by
    linear_combination (-1 / 2 : ℝ) * hU2 + (1 / 2 : ℝ) * hU1
  rw [hAp, hAm, hUp, hUm, deriv_mul_deriv ha hu]
  field_simp
  ring

/-- Saad (2.17), the five-point centered approximation of the Laplacean on a uniform mesh, with
its truncation error.  For `u` of class `C⁴` in each variable separately there are `ξ` and `η` in
`[x₁ - h, x₁ + h]` and `[x₂ - h, x₂ + h]` with
`(u(x₁+h, x₂) + u(x₁-h, x₂) + u(x₁, x₂+h) + u(x₁, x₂-h) - 4u(x₁, x₂))/h²
  = Δu(x₁, x₂) + (h²/12)(∂⁴₁u(ξ, x₂) + ∂⁴₂u(x₁, η))`.
It is two applications of `equation_2_12`, one in each variable; the anisotropic form with
`h₁ ≠ h₂` is the same statement with the two errors weighted separately. -/
theorem equation_2_17 {u : ℝ → ℝ → ℝ} (h₁ : ∀ y, ContDiff ℝ 4 fun t => u t y)
    (h₂ : ∀ x, ContDiff ℝ 4 fun t => u x t) (x₁ x₂ : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ ξ ∈ Set.Icc (x₁ - h) (x₁ + h), ∃ η ∈ Set.Icc (x₂ - h) (x₂ + h),
      (u (x₁ + h) x₂ + u (x₁ - h) x₂ + u x₁ (x₂ + h) + u x₁ (x₂ - h) - 4 * u x₁ x₂) / h ^ 2
        = iteratedDeriv 2 (fun t => u t x₂) x₁ + iteratedDeriv 2 (fun t => u x₁ t) x₂
          + h ^ 2 / 12 * (iteratedDeriv 4 (fun t => u t x₂) ξ
            + iteratedDeriv 4 (fun t => u x₁ t) η) := by
  obtain ⟨ξ, hξ, hv1⟩ := equation_2_12 (h₁ x₂) x₁ hh
  obtain ⟨η, hη, hv2⟩ := equation_2_12 (h₂ x₁) x₂ hh
  refine ⟨ξ, hξ, η, hη, ?_⟩
  rw [div_eq_iff (by positivity : (h : ℝ) ^ 2 ≠ 0)]
  rw [div_eq_iff (by positivity : (h : ℝ) ^ 2 ≠ 0)] at hv1 hv2
  linear_combination hv1 + hv2

/-! #### §2.2.2 The nine-point stencils of Figure 2.4

The two nine-point formulas are combinations of the five-point stencil (2.17) with the *diagonal*
one, the same five-point pattern on the two diagonal lines: Problem P-2.4 gives the recipe, `1/3`
of one plus `2/3` of the other and the reverse combination. Figure 2.4 itself is an image the text
extraction does not reproduce, so the coefficients below come from that recipe.

The whole analysis rests on one exact identity among the nine values, `diagonal_eq` below: the
diagonal stencil is `δ²ₓ + δ²_y + (h²/2) δ²ₓ δ²_y`, so each nine-point formula is the five-point
one plus a multiple of `h²` times the *product* of the two one-dimensional second differences. No
two-variable Taylor expansion is needed anywhere: every error term below comes from applying the
one-dimensional `equation_2_12` along a grid line.

**Not formalized: the sixth-order clause.** Saad also says that (d) is sixth order accurate on
harmonic functions. The expansion above continues
`= Δu + (h²/12) Δ²u + (h⁴/360) Δ(∂⁴₁ + 4∂²₁∂²₂ + ∂⁴₂)u + O(h⁶)`, and both correction terms are
`Δ` of something, hence zero when `Δu` vanishes identically. Collapsing them to that form needs
the equality of the mixed partial derivatives `∂²₁∂²₂u = ∂²₂∂²₁u`, and the terms the expansion
produces are in a fixed order: without Clairaut's theorem the `h⁴` bracket cannot be rewritten as
`Δ` of anything. Mathlib has Clairaut for the second `fderiv` of a function on a normed space
(`second_derivative_symmetric`), but nothing that transports it to the iterated *partial*
derivatives of a curried `u : ℝ → ℝ → ℝ`, which is the form this file works in and the form the
statement below is in; building that bridge, and then iterating it to order six, is what the
sixth-order clause costs. -/

/-- The centred second difference quotient in the first variable,
`δ²ₓ u (x, y) = (u(x + h, y) - 2u(x, y) + u(x - h, y))/h²`, kept as a function of both variables so
that it can be differenced again. -/
noncomputable def diffX (u : ℝ → ℝ → ℝ) (h : ℝ) : ℝ → ℝ → ℝ :=
  fun x y => (u (x + h) y - 2 * u x y + u (x - h) y) / h ^ 2

/-- The centred second difference quotient in the second variable,
`δ²_y u (x, y) = (u(x, y + h) - 2u(x, y) + u(x, y - h))/h²`. -/
noncomputable def diffY (u : ℝ → ℝ → ℝ) (h : ℝ) : ℝ → ℝ → ℝ :=
  fun x y => (u x (y + h) - 2 * u x y + u x (y - h)) / h ^ 2

/-- Saad Figure 2.3(b), the **diagonal (skewed) stencil**: the five-point pattern taken on the two
diagonal lines through `(x, y)`, where the mesh spacing is `h√2`, hence the `2h²`. -/
noncomputable def diagonalStencil (u : ℝ → ℝ → ℝ) (h x y : ℝ) : ℝ :=
  (u (x + h) (y + h) + u (x + h) (y - h) + u (x - h) (y + h) + u (x - h) (y - h)
    - 4 * u x y) / (2 * h ^ 2)

/-- Saad Figure 2.4(c), the nine-point stencil `(1/(3h²))[(N + S + E + W) + (NE + NW + SE + SW)
- 8 C]`: `1/3` of the five-point formula (2.17) plus `2/3` of the diagonal one. -/
noncomputable def ninePointC (u : ℝ → ℝ → ℝ) (h x y : ℝ) : ℝ :=
  (u (x + h) y + u (x - h) y + u x (y + h) + u x (y - h)
    + (u (x + h) (y + h) + u (x + h) (y - h) + u (x - h) (y + h) + u (x - h) (y - h))
    - 8 * u x y) / (3 * h ^ 2)

/-- Saad Figure 2.4(d), the nine-point stencil `(1/(6h²))[4(N + S + E + W) + (NE + NW + SE + SW)
- 20 C]`: `2/3` of the five-point formula (2.17) plus `1/3` of the diagonal one.  This is the
formula the book singles out as sixth order accurate on harmonic functions. -/
noncomputable def ninePointD (u : ℝ → ℝ → ℝ) (h x y : ℝ) : ℝ :=
  (4 * (u (x + h) y + u (x - h) y + u x (y + h) + u x (y - h))
    + (u (x + h) (y + h) + u (x + h) (y - h) + u (x - h) (y + h) + u (x - h) (y - h))
    - 20 * u x y) / (6 * h ^ 2)

/-- **The diagonal stencil is `δ²ₓ + δ²_y + (h²/2) δ²ₓ δ²_y`**, exactly: an identity among the
nine grid values that assumes nothing about `u`.  Grouping the four diagonal points into the two
second differences in `y` at `x ± h` and averaging is what produces the extra product term. -/
theorem diagonalStencil_eq (u : ℝ → ℝ → ℝ) {h : ℝ} (hh : h ≠ 0) (x y : ℝ) :
    diagonalStencil u h x y
      = diffX u h x y + diffY u h x y + h ^ 2 / 2 * diffX (diffY u h) h x y := by
  simp only [diagonalStencil, diffX, diffY]
  field_simp
  ring

/-- Saad Figure 2.4(c) as a five-point formula plus a product correction,
`(c) = δ²ₓ + δ²_y + (h²/3) δ²ₓ δ²_y`. -/
theorem ninePointC_eq (u : ℝ → ℝ → ℝ) {h : ℝ} (hh : h ≠ 0) (x y : ℝ) :
    ninePointC u h x y
      = diffX u h x y + diffY u h x y + h ^ 2 / 3 * diffX (diffY u h) h x y := by
  simp only [ninePointC, diffX, diffY]
  field_simp
  ring

/-- Saad Figure 2.4(d) as a five-point formula plus a product correction,
`(d) = δ²ₓ + δ²_y + (h²/6) δ²ₓ δ²_y`. -/
theorem ninePointD_eq (u : ℝ → ℝ → ℝ) {h : ℝ} (hh : h ≠ 0) (x y : ℝ) :
    ninePointD u h x y
      = diffX u h x y + diffY u h x y + h ^ 2 / 6 * diffX (diffY u h) h x y := by
  simp only [ninePointD, diffX, diffY]
  field_simp
  ring

/-- The **second symmetric difference is a second derivative at an intermediate point**:
`(w(t + h) - 2w(t) + w(t - h))/h² = w''(θ)` for some `θ` in `[t - h, t + h]`.  Two Lagrange
remainders of order two, added, and the intermediate value theorem applied to `w''`. -/
private theorem exists_secondDifference {w : ℝ → ℝ} (hw : ContDiff ℝ 2 w) (t : ℝ) {h : ℝ}
    (hh : 0 < h) :
    ∃ θ ∈ Set.Icc (t - h) (t + h),
      (w (t + h) - 2 * w t + w (t - h)) / h ^ 2 = iteratedDeriv 2 w θ := by
  have hw2 : ContDiff ℝ ((1 : ℕ) + 1 : ℕ) w := by exact_mod_cast hw
  obtain ⟨b, hb, hvb⟩ := exists_taylor hw2 t (ne_of_gt hh)
  obtain ⟨a, ha, hva⟩ := exists_taylor hw2 t (neg_ne_zero.2 (ne_of_gt hh))
  rw [Set.uIoo_of_le (by linarith)] at hb
  rw [Set.uIoo_of_ge (by linarith), show t + -h = t - h by ring] at ha
  rw [show t + -h = t - h by ring] at hva
  obtain ⟨θ, hθ, hmid⟩ := exists_mid (m := 2) (by exact_mod_cast hw) ha hb
  refine ⟨θ, hθ, ?_⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero,
    iteratedDeriv_one] at hvb hva
  norm_num [Nat.factorial] at hvb hva
  rw [hmid, div_eq_iff (by positivity : (h : ℝ) ^ 2 ≠ 0)]
  linear_combination hvb + hva

/-- The second derivative of the fixed combination that a centred second difference is. -/
private theorem iteratedDeriv_two_comb {f g k : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hk : ContDiff ℝ 2 k) (c : ℝ) (t : ℝ) :
    iteratedDeriv 2 (fun s => (f s - 2 * g s + k s) / c) t
      = (iteratedDeriv 2 f t - 2 * iteratedDeriv 2 g t + iteratedDeriv 2 k t) / c := by
  have hg2 : ContDiff ℝ 2 fun s => 2 * g s := contDiff_const.mul hg
  have hfg : ContDiff ℝ 2 fun s => f s - 2 * g s := hf.sub hg2
  rw [iteratedDeriv_div_const, iteratedDeriv_fun_add hfg.contDiffAt hk.contDiffAt,
    iteratedDeriv_fun_sub hf.contDiffAt hg2.contDiffAt, iteratedDeriv_const_mul 2 hg.contDiffAt]

/-- **The product difference `δ²ₓ δ²_y u` is a mixed fourth derivative at an intermediate point**,
`∂²₂∂²₁u(θ, ζ)`: the second symmetric difference in `x` of the second symmetric difference in `y`,
each replaced by a second derivative through `exists_secondDifference`.  The hypothesis `h₁₂` is
the mixed regularity that "`u` of class `C⁴`" supplies and that the separate-variable hypotheses
of this file do not. -/
private theorem exists_diffX_diffY {u : ℝ → ℝ → ℝ} (h₁ : ∀ y, ContDiff ℝ 4 fun t => u t y)
    (h₁₂ : ∀ t, ContDiff ℝ 2 fun s => iteratedDeriv 2 (fun r => u r s) t)
    (x y : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ θ ∈ Set.Icc (x - h) (x + h), ∃ ζ ∈ Set.Icc (y - h) (y + h),
      diffX (diffY u h) h x y
        = iteratedDeriv 2 (fun s => iteratedDeriv 2 (fun r => u r s) θ) ζ := by
  have hle : (2 : WithTop ℕ∞) ≤ 4 := by norm_num
  have hv : ContDiff ℝ 2 fun t => diffY u h t y := by
    simp only [diffY]
    exact ((((h₁ (y + h)).of_le hle).sub (contDiff_const.mul ((h₁ y).of_le hle))).add
      ((h₁ (y - h)).of_le hle)).div_const _
  obtain ⟨θ, hθ, hveq⟩ := exists_secondDifference hv x hh
  obtain ⟨ζ, hζ, hzeq⟩ := exists_secondDifference (h₁₂ θ) y hh
  refine ⟨θ, hθ, ζ, hζ, ?_⟩
  have hcomb : iteratedDeriv 2 (fun t => diffY u h t y) θ
      = (iteratedDeriv 2 (fun t => u t (y + h)) θ - 2 * iteratedDeriv 2 (fun t => u t y) θ
        + iteratedDeriv 2 (fun t => u t (y - h)) θ) / h ^ 2 := by
    simp only [diffY]
    exact iteratedDeriv_two_comb ((h₁ (y + h)).of_le hle) ((h₁ y).of_le hle)
      ((h₁ (y - h)).of_le hle) _ θ
  rw [show diffX (diffY u h) h x y
      = ((fun t => diffY u h t y) (x + h) - 2 * (fun t => diffY u h t y) x
        + (fun t => diffY u h t y) (x - h)) / h ^ 2 from rfl, hveq, hcomb, ← hzeq]

/-- **Saad §2.2.2, Figure 2.4(d): the nine-point formula is second order accurate.**  For `u` of
class `C⁴` along each grid line, with the mixed regularity `h₁₂`, there are four intermediate
points at which
`(d) - Δu = h² (∂⁴₁u(ξ, y)/12 + ∂⁴₂u(x, η)/12 + ∂²₂∂²₁u(θ, ζ)/6)`.
The first two terms are the five-point error of (2.17); the third is the price of the product
correction `(h²/6) δ²ₓ δ²_y` that `ninePointD_eq` exhibits. -/
theorem ninePointD_error {u : ℝ → ℝ → ℝ} (h₁ : ∀ y, ContDiff ℝ 4 fun t => u t y)
    (h₂ : ∀ x, ContDiff ℝ 4 fun t => u x t)
    (h₁₂ : ∀ t, ContDiff ℝ 2 fun s => iteratedDeriv 2 (fun r => u r s) t)
    (x y : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ ξ ∈ Set.Icc (x - h) (x + h), ∃ η ∈ Set.Icc (y - h) (y + h),
      ∃ θ ∈ Set.Icc (x - h) (x + h), ∃ ζ ∈ Set.Icc (y - h) (y + h),
      ninePointD u h x y
          - (iteratedDeriv 2 (fun t => u t y) x + iteratedDeriv 2 (fun t => u x t) y)
        = h ^ 2 * (iteratedDeriv 4 (fun t => u t y) ξ / 12
            + iteratedDeriv 4 (fun t => u x t) η / 12
            + iteratedDeriv 2 (fun s => iteratedDeriv 2 (fun r => u r s) θ) ζ / 6) := by
  obtain ⟨ξ, hξ, hx2⟩ := equation_2_12 (h₁ y) x hh
  obtain ⟨η, hη, hy2⟩ := equation_2_12 (h₂ x) y hh
  obtain ⟨θ, hθ, ζ, hζ, hxy⟩ := exists_diffX_diffY h₁ h₁₂ x y hh
  refine ⟨ξ, hξ, η, hη, θ, hθ, ζ, hζ, ?_⟩
  rw [ninePointD_eq u hh.ne' x y, hxy, show diffX u h x y
      = ((fun t => u t y) (x + h) - 2 * (fun t => u t y) x + (fun t => u t y) (x - h)) / h ^ 2
      from rfl, hx2, show diffY u h x y
      = ((fun t => u x t) (y + h) - 2 * (fun t => u x t) y + (fun t => u x t) (y - h)) / h ^ 2
      from rfl, hy2]
  ring

/-- **Saad §2.2.2, Figure 2.4(c): the other nine-point formula is second order accurate.**  Same
statement as `ninePointD_error` with the product correction weighted `1/3` instead of `1/6`, which
is the reverse combination of Problem P-2.4. -/
theorem ninePointC_error {u : ℝ → ℝ → ℝ} (h₁ : ∀ y, ContDiff ℝ 4 fun t => u t y)
    (h₂ : ∀ x, ContDiff ℝ 4 fun t => u x t)
    (h₁₂ : ∀ t, ContDiff ℝ 2 fun s => iteratedDeriv 2 (fun r => u r s) t)
    (x y : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ ξ ∈ Set.Icc (x - h) (x + h), ∃ η ∈ Set.Icc (y - h) (y + h),
      ∃ θ ∈ Set.Icc (x - h) (x + h), ∃ ζ ∈ Set.Icc (y - h) (y + h),
      ninePointC u h x y
          - (iteratedDeriv 2 (fun t => u t y) x + iteratedDeriv 2 (fun t => u x t) y)
        = h ^ 2 * (iteratedDeriv 4 (fun t => u t y) ξ / 12
            + iteratedDeriv 4 (fun t => u x t) η / 12
            + iteratedDeriv 2 (fun s => iteratedDeriv 2 (fun r => u r s) θ) ζ / 3) := by
  obtain ⟨ξ, hξ, hx2⟩ := equation_2_12 (h₁ y) x hh
  obtain ⟨η, hη, hy2⟩ := equation_2_12 (h₂ x) y hh
  obtain ⟨θ, hθ, ζ, hζ, hxy⟩ := exists_diffX_diffY h₁ h₁₂ x y hh
  refine ⟨ξ, hξ, η, hη, θ, hθ, ζ, hζ, ?_⟩
  rw [ninePointC_eq u hh.ne' x y, hxy, show diffX u h x y
      = ((fun t => u t y) (x + h) - 2 * (fun t => u t y) x + (fun t => u t y) (x - h)) / h ^ 2
      from rfl, hx2, show diffY u h x y
      = ((fun t => u x t) (y + h) - 2 * (fun t => u x t) y + (fun t => u x t) (y - h)) / h ^ 2
      from rfl, hy2]
  ring

end Truncation

/-! ### §2.2.3 The one-dimensional model problem -/

section OneDimensional

variable {n : ℕ}

/-- A grid function on the `n` interior points, extended by the homogeneous Dirichlet boundary
values `u₀ = u_{n+1} = 0`.  The argument is the book's grid index `k = 0, …, n + 1`, so
`dirichletExt v (i + 1) = v i` for an interior index `i : Fin n`, and the value is `0` at both
boundary points. -/
def dirichletExt (v : Fin n → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if hk : k < n then v ⟨k, hk⟩ else 0

@[simp]
theorem dirichletExt_zero (v : Fin n → ℝ) : dirichletExt v 0 = 0 := rfl

theorem dirichletExt_succ (v : Fin n → ℝ) (k : ℕ) :
    dirichletExt v (k + 1) = if hk : k < n then v ⟨k, hk⟩ else 0 := rfl

@[simp]
theorem dirichletExt_coe_succ (v : Fin n → ℝ) (i : Fin n) :
    dirichletExt v ((i : ℕ) + 1) = v i := by
  rw [dirichletExt_succ, dite_eq_left i.isLt]

theorem dirichletExt_of_gt (v : Fin n → ℝ) {k : ℕ} (hk : n < k) : dirichletExt v k = 0 := by
  cases k with
  | zero => rfl
  | succ k => rw [dirichletExt_succ, dite_eq_right (by omega)]

/-- Saad §2.2.3: the one-dimensional model matrix of `-u'' = f` on `(0, 1)` with homogeneous
Dirichlet boundary conditions, discretized on the uniform grid `x_i = i h` with `h = 1/(n + 1)`.
It is `tridiag(-1, 2, -1)` scaled by `1/h²`; the book displays it without an equation number. -/
noncomputable def laplacian1D (n : ℕ) (h : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (h ^ 2)⁻¹ • Matrix.symmTridiagonalToeplitz n (-1) 2

theorem laplacian1D_apply (h : ℝ) (i j : Fin n) :
    laplacian1D n h i j =
      (h ^ 2)⁻¹ * (if (i : ℕ) = j then 2 else
        if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0) := by
  rw [laplacian1D, Matrix.smul_apply, smul_eq_mul, Matrix.symmTridiagonalToeplitz_apply']

/-- The half-angle identity `2 - 2 cos θ = 4 sin²(θ/2)`, which turns the backbone's eigenvalue
`b + 2 a cos θ` of `tridiag(-1, 2, -1)` into Saad's `4 sin²(θ/2)`. -/
private theorem two_sub_two_mul_cos (θ : ℝ) : 2 - 2 * Real.cos θ = 4 * Real.sin (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul_eq_one_sub (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  linarith

/-- The half-angle identity `2 + 2 cos θ = 4 cos²(θ/2)`, the other end of the spectrum. -/
private theorem two_add_two_mul_cos (θ : ℝ) : 2 + 2 * Real.cos θ = 4 * Real.cos (θ / 2) ^ 2 := by
  have h := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h
  linarith

/-- Quadratic-form bounds are homogeneous: scaling a matrix by a positive constant scales both
ends of the enclosing interval.  This is what carries the backbone's bounds for
`tridiag(a, b, a)` across the `1/h²` of the model matrix. -/
private theorem isSymmetricBoundedBy_smul {A : Matrix (Fin n) (Fin n) ℝ} {lmin lmax c : ℝ}
    (hA : (Matrix.toEuclideanLin A).IsSymmetricBoundedBy lmin lmax) (hc : 0 < c) :
    (Matrix.toEuclideanLin (c • A)).IsSymmetricBoundedBy (c * lmin) (c * lmax) := by
  have hmul : ∀ x : EuclideanSpace ℝ (Fin n),
      Matrix.toEuclideanLin (c • A) x = c • Matrix.toEuclideanLin A x := by
    intro x
    change WithLp.toLp 2 ((c • A) *ᵥ WithLp.ofLp x) = _
    rw [Matrix.smul_mulVec]
    rfl
  refine ⟨fun x y => ?_, fun x => ?_, fun x => ?_⟩
  · rw [hmul, hmul, real_inner_smul_left, real_inner_smul_right, hA.isSymmetric x y]
  · have h := hA.isCoerciveWith x
    rw [hmul, RCLike.re_to_real, real_inner_smul_left, mul_assoc]
    rw [RCLike.re_to_real] at h
    exact mul_le_mul_of_nonneg_left h hc.le
  · have h := hA.re_inner_le x
    rw [hmul, RCLike.re_to_real, real_inner_smul_left, mul_assoc]
    rw [RCLike.re_to_real] at h
    exact mul_le_mul_of_nonneg_left h hc.le

/-- The sum picking out the entry at grid index `m + 1`, in the extended form. -/
private theorem sum_ite_dirichletExt (c : ℝ) (v : Fin n → ℝ) (m : ℕ) :
    ∑ j : Fin n, (if (j : ℕ) = m then c * v j else 0) = c * dirichletExt v (m + 1) := by
  have h : ∀ j : Fin n, (if (j : ℕ) = m then c * v j else 0)
      = if (j : ℕ) = m then c * dirichletExt v ((j : ℕ) + 1) else 0 := by
    intro j; rw [dirichletExt_coe_succ]
  rw [Finset.sum_congr rfl fun j _ => h j,
    Fin.sum_univ_eq_sum_range fun j => if j = m then c * dirichletExt v (j + 1) else 0,
    Finset.sum_ite_eq' (Finset.range n) m fun j => c * dirichletExt v (j + 1)]
  by_cases hm : m < n
  · rw [ite_eq_left (Finset.mem_range.2 hm)]
  · rw [ite_eq_right fun hmem => hm (Finset.mem_range.1 hmem), dirichletExt_of_gt v (by omega),
      mul_zero]

/-- The sum picking out the entry just below grid index `m`, in the extended form. -/
private theorem sum_ite_succ_dirichletExt (c : ℝ) (v : Fin n → ℝ) (m : ℕ) :
    ∑ j : Fin n, (if (j : ℕ) + 1 = m then c * v j else 0) = c * dirichletExt v m := by
  cases m with
  | zero => simp
  | succ m =>
    have h : ∀ j : Fin n, ((j : ℕ) + 1 = m + 1) = ((j : ℕ) = m) := fun j => by simp
    simp only [h]
    exact sum_ite_dirichletExt c v m

/-- The three-term row of a symmetric tridiagonal Toeplitz matrix, uniform across the first, the
last and the interior rows because the missing neighbours are supplied by the Dirichlet
extension. -/
private theorem symmTridiagonalToeplitz_mulVec_apply (a b : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (Matrix.symmTridiagonalToeplitz n a b *ᵥ v) i
      = a * dirichletExt v (i : ℕ) + b * dirichletExt v ((i : ℕ) + 1)
        + a * dirichletExt v ((i : ℕ) + 2) := by
  have hsplit : ∀ j : Fin n, Matrix.symmTridiagonalToeplitz n a b i j * v j
      = (if (j : ℕ) + 1 = (i : ℕ) then a * v j else 0)
        + (if (j : ℕ) = (i : ℕ) then b * v j else 0)
        + (if (j : ℕ) = (i : ℕ) + 1 then a * v j else 0) := by
    intro j
    rw [Matrix.symmTridiagonalToeplitz_apply']
    split_ifs <;> first | (exfalso; omega) | ring
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_succ_dirichletExt,
    sum_ite_dirichletExt, sum_ite_dirichletExt]

/-- The rows of the model matrix are the difference equations of §2.2.3: the `i`-th row of
`laplacian1D n h *ᵥ v` is `(-v_{i-1} + 2 v_i - v_{i+1}) / h²`, with the boundary values
`v_0 = v_{n+1} = 0` supplied by `dirichletExt`. -/
theorem laplacian1D_mulVec_apply (h : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (laplacian1D n h *ᵥ v) i
      = (-dirichletExt v (i : ℕ) + 2 * dirichletExt v ((i : ℕ) + 1)
          - dirichletExt v ((i : ℕ) + 2)) / h ^ 2 := by
  rw [laplacian1D, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    symmTridiagonalToeplitz_mulVec_apply]
  field_simp
  ring

/-- The eigenpairs of the one-dimensional model matrix: the `k`-th discrete sine vector is an
eigenvector with eigenvalue `4 sin²(kπ/(2(n+1)))/h²`, in Saad's `1`-based numbering
`k = 1, …, n`. -/
theorem laplacian1D_mulVec_sineVec (h : ℝ) (k : Fin n) :
    laplacian1D n h *ᵥ Matrix.sineVec n k
      = (4 * Real.sin ((((k : ℕ) : ℝ) + 1) * π / (2 * ((n : ℝ) + 1))) ^ 2 / h ^ 2)
        • Matrix.sineVec n k := by
  rw [laplacian1D, Matrix.smul_mulVec, Matrix.symmTridiagonalToeplitz_mulVec_sineVec, smul_smul]
  congr 1
  have h2 := (two_sub_two_mul_cos ((((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1))).symm
  rw [show (((k : ℕ) : ℝ) + 1) * π / ((n : ℝ) + 1) / 2
      = (((k : ℕ) : ℝ) + 1) * π / (2 * ((n : ℝ) + 1)) by
    rw [div_div, mul_comm ((n : ℝ) + 1) 2]] at h2
  rw [h2]
  ring

/-- The extreme eigenvalues of the one-dimensional model matrix, as quadratic-form bounds:
`4 sin²(π/(2(n+1)))/h² ≤ (A x, x)/‖x‖² ≤ 4 cos²(π/(2(n+1)))/h²`.  Both ends are eigenvalues —
`laplacian1D_mulVec_sineVec` at `k = 1` and at `k = n` — so the interval is the sharp one. -/
theorem laplacian1D_isSymmetricBoundedBy (n : ℕ) {h : ℝ} (hh : h ≠ 0) :
    (Matrix.toEuclideanLin (laplacian1D n h)).IsSymmetricBoundedBy
      (4 * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 / h ^ 2)
      (4 * Real.cos (π / (2 * ((n : ℝ) + 1))) ^ 2 / h ^ 2) := by
  have hpos : (0 : ℝ) < (h ^ 2)⁻¹ :=
    inv_pos.2 (lt_of_le_of_ne (sq_nonneg h) (Ne.symm (pow_ne_zero 2 hh)))
  have hhalf : π / ((n : ℝ) + 1) / 2 = π / (2 * ((n : ℝ) + 1)) := by
    rw [div_div, mul_comm ((n : ℝ) + 1) 2]
  have hlo := two_sub_two_mul_cos (π / ((n : ℝ) + 1))
  have hhi := two_add_two_mul_cos (π / ((n : ℝ) + 1))
  rw [hhalf] at hlo hhi
  have key := isSymmetricBoundedBy_smul
    (Matrix.isSymmetricBoundedBy_symmTridiagonalToeplitz n (-1) 2) hpos
  have e1 : (h ^ 2)⁻¹ * (2 - 2 * |(-1 : ℝ)| * Real.cos (π / ((n : ℝ) + 1)))
      = 4 * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 / h ^ 2 := by
    rw [abs_neg, abs_one, show (2 : ℝ) - 2 * 1 * Real.cos (π / ((n : ℝ) + 1))
      = 2 - 2 * Real.cos (π / ((n : ℝ) + 1)) by ring, hlo]
    ring
  have e2 : (h ^ 2)⁻¹ * (2 + 2 * |(-1 : ℝ)| * Real.cos (π / ((n : ℝ) + 1)))
      = 4 * Real.cos (π / (2 * ((n : ℝ) + 1))) ^ 2 / h ^ 2 := by
    rw [abs_neg, abs_one, show (2 : ℝ) + 2 * 1 * Real.cos (π / ((n : ℝ) + 1))
      = 2 + 2 * Real.cos (π / ((n : ℝ) + 1)) by ring, hhi]
    ring
  rw [e1, e2] at key
  exact key

/-- The one-dimensional model matrix is symmetric positive definite.  Its diagonal dominance is
not strict, so what does the work is the sharp bound `cos(π/(n+1)) < 1` of
`Matrix.posDef_symmTridiagonalToeplitz_neg_one_two`.  Not stated in Chapter 2 — Saad gives the
spectrum only for the block `B` of (2.27) — but used throughout Chapters 4, 6 and 10. -/
theorem laplacian1D_posDef (n : ℕ) {h : ℝ} (hh : h ≠ 0) : (laplacian1D n h).PosDef :=
  (Matrix.posDef_symmTridiagonalToeplitz_neg_one_two n).smul
    (inv_pos.2 (lt_of_le_of_ne (sq_nonneg h) (Ne.symm (pow_ne_zero 2 hh))))

/-- The ratio of the two ends of `laplacian1D_isSymmetricBoundedBy` is `cot²(π/(2(n+1)))`, which
is the `2`-norm condition number of the model matrix and is independent of `h`.  Since
`h = 1/(n + 1)`, it is asymptotically `4/(π² h²)`, which is the source of every "the condition
number grows like `h⁻²`" remark in the book; that asymptotic is not formalized here. -/
theorem laplacian1D_lambdaMax_div_lambdaMin (n : ℕ) {h : ℝ} (hh : h ≠ 0) :
    (4 * Real.cos (π / (2 * ((n : ℝ) + 1))) ^ 2 / h ^ 2)
        / (4 * Real.sin (π / (2 * ((n : ℝ) + 1))) ^ 2 / h ^ 2)
      = (Real.cos (π / (2 * ((n : ℝ) + 1))) / Real.sin (π / (2 * ((n : ℝ) + 1)))) ^ 2 := by
  have hh2 : (h : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hh
  rw [div_pow]
  rcases eq_or_ne (Real.sin (π / (2 * ((n : ℝ) + 1)))) 0 with hs | hs
  · simp [hs]
  · field_simp

end OneDimensional

/-! ### §2.2.4 The convection–diffusion problem -/

section ConvectionDiffusion

/-- Saad (2.20): the solution of the two-point boundary value problem `-a u'' + b u' = 0` on
`(0, 1)` with `u(0) = 0`, `u(1) = 1`, written with the Péclet number `R = b/a`. -/
noncomputable def convDiffExact (R x : ℝ) : ℝ := (1 - Real.exp (R * x)) / (1 - Real.exp R)

/-- Saad (2.20): `convDiffExact R` is differentiable, with derivative
`-R exp(R x)/(1 - exp R)`. -/
theorem convDiffExact_hasDerivAt (R x : ℝ) :
    HasDerivAt (convDiffExact R) (-(R * Real.exp (R * x)) / (1 - Real.exp R)) x := by
  have hE : HasDerivAt (fun t : ℝ => Real.exp (R * t)) (Real.exp (R * x) * R) x := by
    simpa using ((hasDerivAt_id x).const_mul R).exp
  have h4 : HasDerivAt (fun t : ℝ => (1 - Real.exp (R * t)) / (1 - Real.exp R))
      (-(Real.exp (R * x) * R) / (1 - Real.exp R)) x := (hE.const_sub 1).div_const _
  rw [show -(R * Real.exp (R * x)) = -(Real.exp (R * x) * R) by ring]
  exact h4

/-- A function whose derivative vanishes on `[0, 1]` is constant there. -/
private theorem eq_of_deriv_eq_zero {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hz : ∀ x ∈ Set.Icc (0 : ℝ) 1, f' x = 0) : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = f 0 := by
  refine constant_of_has_deriv_right_zero (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    fun x hx => ?_
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
  have hd := hf x hx'
  rw [hz x hx'] at hd
  exact hd.hasDerivWithinAt

/-- The uniqueness half of Saad (2.20), with the Péclet number as the only parameter: a solution
of `u'' = R u'` on `[0, 1]` with `u(0) = 0` and `u(1) = 1` is `convDiffExact R`.  The equation
makes `u'` a multiple of `exp(R ·)`, and the two boundary conditions fix the two constants. -/
private theorem convDiffExact_unique {R : ℝ} (hR : R ≠ 0) {u u' u'' : ℝ → ℝ}
    (hu : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u' (u'' x) x)
    (heq : ∀ x ∈ Set.Icc (0 : ℝ) 1, u'' x = R * u' x) (h0 : u 0 = 0) (h1 : u 1 = 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u x = convDiffExact R x := by
  have hexp1 : Real.exp R ≠ 1 := fun he => hR ((Real.exp_eq_one_iff R).1 he)
  have hden : Real.exp R - 1 ≠ 0 := sub_ne_zero.2 hexp1
  -- `u' x exp(-R x)` is constant, so `u' x = u'(0) exp(R x)`.
  have hg : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      u' x * Real.exp (-(R * x)) = u' 0 * Real.exp (-(R * 0)) := by
    refine eq_of_deriv_eq_zero (f' := fun x => (u'' x - R * u' x) * Real.exp (-(R * x)))
      (fun x hx => ?_) fun x hx => by rw [heq x hx]; ring
    have hE : HasDerivAt (fun t : ℝ => Real.exp (-(R * t))) (Real.exp (-(R * x)) * -R) x := by
      simpa using (((hasDerivAt_id x).const_mul R).neg).exp
    have hp := (hu' x hx).mul hE
    rw [show u'' x * Real.exp (-(R * x)) + u' x * (Real.exp (-(R * x)) * -R)
      = (u'' x - R * u' x) * Real.exp (-(R * x)) by ring] at hp
    exact hp
  have hu'x : ∀ x ∈ Set.Icc (0 : ℝ) 1, u' x = u' 0 * Real.exp (R * x) := by
    intro x hx
    have hgx := hg x hx
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at hgx
    have hmul : u' x * Real.exp (-(R * x)) * Real.exp (R * x) = u' 0 * Real.exp (R * x) := by
      rw [hgx]
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hmul
  -- Integrating once more, `u x = u'(0) (exp(R x) - 1)/R`.
  have hk : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      u x - u' 0 * (Real.exp (R * x) - 1) / R = u 0 - u' 0 * (Real.exp (R * 0) - 1) / R := by
    refine eq_of_deriv_eq_zero (f' := fun x => u' x - u' 0 * Real.exp (R * x)) (fun x hx => ?_)
      fun x hx => by rw [hu'x x hx]; ring
    have hE : HasDerivAt (fun t : ℝ => Real.exp (R * t)) (Real.exp (R * x) * R) x := by
      simpa using ((hasDerivAt_id x).const_mul R).exp
    have h2 : HasDerivAt (fun t : ℝ => u' 0 * (Real.exp (R * t) - 1) / R)
        (u' 0 * Real.exp (R * x)) x := by
      have hq := ((hE.sub_const 1).const_mul (u' 0)).div_const R
      rw [show u' 0 * (Real.exp (R * x) * R) / R = u' 0 * Real.exp (R * x) by
        field_simp] at hq
      exact hq
    exact (hu x hx).sub h2
  have hux : ∀ y ∈ Set.Icc (0 : ℝ) 1, u y = u' 0 * (Real.exp (R * y) - 1) / R := by
    intro y hy
    have hky := hk y hy
    rw [h0] at hky
    norm_num at hky
    linarith
  have hval := hux 1 (by norm_num)
  rw [h1, mul_one] at hval
  have hu0 : u' 0 = R / (Real.exp R - 1) := by
    field_simp at hval ⊢
    linarith
  have hR2 : (1 : ℝ) - Real.exp R ≠ 0 := sub_ne_zero.2 (Ne.symm hexp1)
  intro x hx
  rw [hux x hx, hu0, convDiffExact]
  field_simp
  ring

/-- Saad (2.20): the boundary value problem `-a u'' + b u' = 0`, `u(0) = 0`, `u(1) = 1` has
`convDiffExact (b/a)` as its **only** solution on `[0, 1]`.  Uniqueness is the content: the
equation forces `u' = R u'` up to the exponential factor, so `u'` is a multiple of `exp(R·)` and
the two boundary conditions fix the two constants. -/
theorem equation_2_20 {a b : ℝ} (ha : a ≠ 0) (hR : b / a ≠ 0) {u u' u'' : ℝ → ℝ}
    (hu : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u' (u'' x) x)
    (heq : ∀ x ∈ Set.Icc (0 : ℝ) 1, -a * u'' x + b * u' x = 0)
    (h0 : u 0 = 0) (h1 : u 1 = 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u x = convDiffExact (b / a) x :=
  convDiffExact_unique hR hu hu'
    (fun x hx => by
      have hx' := heq x hx
      field_simp
      linarith) h0 h1

/-- For a positive Péclet number the exponential exceeds `1`. -/
private theorem one_lt_exp_of_pos {t : ℝ} (ht : 0 < t) : 1 < Real.exp t := by
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.2 ht

/-- Saad §2.2.4: for a positive Péclet number the exact solution is positive on `(0, 1]` — the
behaviour the centered scheme fails to reproduce when the mesh is too coarse. -/
theorem convDiffExact_pos {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : 0 < x) : 0 < convDiffExact R x := by
  have h1 := one_lt_exp_of_pos (mul_pos hR hx)
  have h2 := one_lt_exp_of_pos hR
  rw [convDiffExact, show (1 - Real.exp (R * x)) / (1 - Real.exp R)
      = (Real.exp (R * x) - 1) / (Real.exp R - 1) by
    rw [← neg_sub (Real.exp (R * x)) 1, ← neg_sub (Real.exp R) 1, neg_div_neg_eq]]
  exact div_pos (by linarith) (by linarith)

/-- Saad §2.2.4: for a positive Péclet number the exact solution is strictly increasing. -/
theorem convDiffExact_strictMono {R : ℝ} (hR : 0 < R) : StrictMono (convDiffExact R) := by
  intro x y hxy
  have h2 := one_lt_exp_of_pos hR
  have hexp : Real.exp (R * x) < Real.exp (R * y) :=
    Real.exp_lt_exp.2 (by nlinarith)
  have hd : 1 - Real.exp R < 0 := by linarith
  rw [convDiffExact, convDiffExact, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_neg_right (by linarith) (inv_lt_zero.2 hd)

/-- Saad (2.21): the ratio `σ = (1 + c)/(1 - c)` of the two roots of the characteristic equation
`(1 - c) r² - 2 r + (1 + c) = 0` of the centered difference scheme, with `c = R h / 2`. -/
noncomputable def convDiffRatio (c : ℝ) : ℝ := (1 + c) / (1 - c)

/-- Saad (2.21): the solution of the centered difference scheme. -/
noncomputable def convDiffDiscrete (c : ℝ) (n i : ℕ) : ℝ :=
  (1 - convDiffRatio c ^ i) / (1 - convDiffRatio c ^ (n + 1))

/-- The characteristic equation `(1 - c) r² - 2 r + (1 + c) = 0` of the centered scheme, at its
root `σ = (1 + c)/(1 - c)`.  The other root is `1`. -/
private theorem convDiffRatio_char {c : ℝ} (hc1 : c ≠ 1) :
    (1 - c) * convDiffRatio c ^ 2 - 2 * convDiffRatio c + (1 + c) = 0 := by
  have hcne : (1 : ℝ) - c ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
  rw [convDiffRatio]
  field_simp
  ring

private theorem convDiffRatio_ne_one {c : ℝ} (hc1 : c ≠ 1) (hc0 : c ≠ 0) :
    convDiffRatio c ≠ 1 := by
  have hcne : (1 : ℝ) - c ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
  intro h
  rw [convDiffRatio, div_eq_iff hcne] at h
  exact hc0 (by linarith)

private theorem convDiffRatio_ne_neg_one {c : ℝ} (hc1 : c ≠ 1) : convDiffRatio c ≠ -1 := by
  have hcne : (1 : ℝ) - c ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
  intro h
  rw [convDiffRatio, div_eq_iff hcne] at h
  linarith

/-- `σ` is neither `1` nor `-1`, so no power of it is `1`: the denominator of (2.21) never
vanishes. -/
private theorem convDiffRatio_pow_ne_one {c : ℝ} (hc1 : c ≠ 1) (hc0 : c ≠ 0) (n : ℕ) :
    convDiffRatio c ^ (n + 1) ≠ 1 := by
  intro h
  have habs : |convDiffRatio c| ^ (n + 1) = 1 := by rw [← abs_pow, h, abs_one]
  have h1 := (pow_eq_one_iff_of_nonneg (abs_nonneg _) (Nat.succ_ne_zero n)).1 habs
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 h1 with h' | h'
  · exact convDiffRatio_ne_one hc1 hc0 h'
  · exact convDiffRatio_ne_neg_one hc1 h'

/-- Saad (2.21): the centered difference scheme
`-(1 - c) u_{i+1} + 2 u_i - (1 + c) u_{i-1} = 0` with `u_0 = 0` and `u_{n+1} = 1` has
`u_i = (1 - σ^i)/(1 - σ^{n+1})`, `σ = (1 + c)/(1 - c)`, as its only solution, provided `c ≠ 0`
(so `σ ≠ 1`) and `c ≠ 1` (so `σ` exists).  The characteristic equation has the roots `1` and `σ`,
and the two boundary conditions fix the coefficients. -/
theorem equation_2_21 {n : ℕ} {c : ℝ} (hc1 : c ≠ 1) (hc0 : c ≠ 0) {u : ℕ → ℝ}
    (hrec : ∀ i, 1 ≤ i → i ≤ n → -(1 - c) * u (i + 1) + 2 * u i - (1 + c) * u (i - 1) = 0)
    (h0 : u 0 = 0) (h1 : u (n + 1) = 1) :
    ∀ i ≤ n + 1, u i = convDiffDiscrete c n i := by
  have hcne : (1 : ℝ) - c ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
  have hσne : (1 : ℝ) - convDiffRatio c ≠ 0 :=
    sub_ne_zero.2 (Ne.symm (convDiffRatio_ne_one hc1 hc0))
  have hpow : (1 : ℝ) - convDiffRatio c ^ (n + 1) ≠ 0 :=
    sub_ne_zero.2 (Ne.symm (convDiffRatio_pow_ne_one hc1 hc0 n))
  -- The particular solution `(1 - σ^i)/(1 - σ)` satisfies the recurrence.
  have hnum : ∀ i : ℕ, -(1 - c) * (1 - convDiffRatio c ^ (i + 2))
      + 2 * (1 - convDiffRatio c ^ (i + 1)) - (1 + c) * (1 - convDiffRatio c ^ i) = 0 := by
    intro i
    have hexp : -(1 - c) * (1 - convDiffRatio c ^ (i + 2))
        + 2 * (1 - convDiffRatio c ^ (i + 1)) - (1 + c) * (1 - convDiffRatio c ^ i)
        = convDiffRatio c ^ i
          * ((1 - c) * convDiffRatio c ^ 2 - 2 * convDiffRatio c + (1 + c)) := by ring
    rw [hexp, convDiffRatio_char hc1, mul_zero]
  -- Shooting from `u 0 = 0`: every value is `u 1` times the particular solution.
  have key : ∀ i, i ≤ n →
      u i = u 1 * ((1 - convDiffRatio c ^ i) / (1 - convDiffRatio c)) ∧
        u (i + 1) = u 1 * ((1 - convDiffRatio c ^ (i + 1)) / (1 - convDiffRatio c)) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨by rw [h0]; norm_num, ?_⟩
      rw [pow_one]
      field_simp
    | succ i ih =>
      intro hi
      obtain ⟨hA, hB⟩ := ih (by omega)
      refine ⟨hB, ?_⟩
      have hr := hrec (i + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hr
      have hT : -(1 - c) * ((1 - convDiffRatio c ^ (i + 2)) / (1 - convDiffRatio c))
          + 2 * ((1 - convDiffRatio c ^ (i + 1)) / (1 - convDiffRatio c))
          - (1 + c) * ((1 - convDiffRatio c ^ i) / (1 - convDiffRatio c)) = 0 := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        linear_combination (1 - convDiffRatio c)⁻¹ * hnum i
      rw [hA, hB] at hr
      refine mul_left_cancel₀ hcne ?_
      show (1 - c) * u (i + 1 + 1)
        = (1 - c) * (u 1 * ((1 - convDiffRatio c ^ (i + 1 + 1)) / (1 - convDiffRatio c)))
      linear_combination (-1 : ℝ) * hr + u 1 * hT
  have hcand : ∀ i, i ≤ n + 1 →
      u i = u 1 * ((1 - convDiffRatio c ^ i) / (1 - convDiffRatio c)) := by
    intro i hi
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact (key i (by omega)).1
    · have hin : i = n + 1 := by omega
      subst hin
      exact (key n le_rfl).2
  intro i hi
  have hval := hcand (n + 1) le_rfl
  rw [h1] at hval
  have hu1 : u 1 = (1 - convDiffRatio c) / (1 - convDiffRatio c ^ (n + 1)) := by
    field_simp at hval ⊢
    linarith
  rw [hcand i hi, hu1, convDiffDiscrete]
  field_simp

/-- The oscillation criterion of §2.2.4.  When `h > 2/R`, that is `c = R h/2 > 1`, the ratio `σ`
is negative and the discrete solution alternates in sign, `u_i u_{i+1} < 0` for `1 ≤ i ≤ n`,
whereas the exact solution of `equation_2_20` is positive and increasing
(`convDiffExact_pos`, `convDiffExact_strictMono`).  The book's remark that the oscillations
disappear when `b < 0` is the same computation with the sign of `c` reversed. -/
theorem equation_2_21_oscillates {n : ℕ} {c : ℝ} (hc : 1 < c) {i : ℕ} (hi : 1 ≤ i) :
    convDiffDiscrete c n i * convDiffDiscrete c n (i + 1) < 0 := by
  have hc1 : c ≠ 1 := ne_of_gt hc
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; linarith
  have hcneg : (1 : ℝ) - c < 0 := by linarith
  have hσ : convDiffRatio c < -1 := by
    rw [convDiffRatio, div_lt_iff_of_neg hcneg]
    linarith
  have habs : 1 < |convDiffRatio c| := by
    rw [abs_of_neg (by linarith)]
    linarith
  have hev : ∀ k : ℕ, Even k → k ≠ 0 → 1 < convDiffRatio c ^ k := by
    intro k hk hk0
    rw [← hk.pow_abs]
    exact one_lt_pow₀ habs hk0
  have hod : ∀ k : ℕ, Odd k → convDiffRatio c ^ k < 0 := fun k hk =>
    hk.pow_neg_iff.2 (by linarith)
  have hne : (1 : ℝ) - convDiffRatio c ^ (n + 1) ≠ 0 :=
    sub_ne_zero.2 (Ne.symm (convDiffRatio_pow_ne_one hc1 hc0 n))
  have hden : (0 : ℝ) < (1 - convDiffRatio c ^ (n + 1)) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  rw [convDiffDiscrete, convDiffDiscrete, div_mul_div_comm, ← pow_two]
  refine div_neg_of_neg_of_pos ?_ hden
  rcases Nat.even_or_odd i with he | ho
  · have hb1 : 1 < convDiffRatio c ^ i := hev i he (by omega)
    have hb2 : convDiffRatio c ^ (i + 1) < 0 := hod _ he.add_one
    nlinarith
  · have hb1 : convDiffRatio c ^ i < 0 := hod i ho
    have hb2 : 1 < convDiffRatio c ^ (i + 1) := hev _ ho.add_one (by omega)
    nlinarith

/-- The other half of the criterion: when `h < 2/R`, that is `0 < c < 1`, the ratio `σ` exceeds
`1` and the discrete solution is strictly increasing along the grid, as the exact solution is. -/
theorem equation_2_21_strictMono {n : ℕ} {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (i : ℕ) :
    convDiffDiscrete c n i < convDiffDiscrete c n (i + 1) := by
  have hcpos : (0 : ℝ) < 1 - c := by linarith
  have hσ : 1 < convDiffRatio c := by
    rw [convDiffRatio, lt_div_iff₀ hcpos]
    linarith
  have hpos : (0 : ℝ) < convDiffRatio c ^ i := pow_pos (by linarith) i
  have hmono : convDiffRatio c ^ i < convDiffRatio c ^ (i + 1) := by
    rw [pow_succ]
    nlinarith
  have hdenneg : (1 : ℝ) - convDiffRatio c ^ (n + 1) < 0 := by
    have hgt : 1 < convDiffRatio c ^ (n + 1) := one_lt_pow₀ hσ (Nat.succ_ne_zero n)
    linarith
  rw [convDiffDiscrete, convDiffDiscrete, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_neg_right (by linarith) (inv_lt_zero.2 hdenneg)

/-- Saad §2.2.4: the tridiagonal matrix of the centered difference scheme, with diagonal `2`,
subdiagonal `-1 - c` and superdiagonal `-1 + c`, all scaled by `1/h²`.  The book displays it
without an equation number. -/
noncomputable def convDiffCentered (n : ℕ) (h c : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (h ^ 2)⁻¹ • Matrix.of fun i j : Fin n =>
    if (i : ℕ) = j then 2 else if (i : ℕ) + 1 = j then -1 + c
      else if (j : ℕ) + 1 = i then -1 - c else 0

/-- Saad §2.2.4: the tridiagonal matrix of the upwind difference scheme for `b > 0`, with
diagonal `2 + c`, subdiagonal `-1 - c` and superdiagonal `-1`, all scaled by `1/h²`. -/
noncomputable def convDiffUpwind (n : ℕ) (h c : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (h ^ 2)⁻¹ • Matrix.of fun i j : Fin n =>
    if (i : ℕ) = j then 2 + c else if (i : ℕ) + 1 = j then -1
      else if (j : ℕ) + 1 = i then -1 - c else 0

theorem convDiffCentered_apply (n : ℕ) (h c : ℝ) (i j : Fin n) :
    convDiffCentered n h c i j =
      (h ^ 2)⁻¹ * (if (i : ℕ) = j then 2 else if (i : ℕ) + 1 = j then -1 + c
        else if (j : ℕ) + 1 = i then -1 - c else 0) := rfl

theorem convDiffUpwind_apply (n : ℕ) (h c : ℝ) (i j : Fin n) :
    convDiffUpwind n h c i j =
      (h ^ 2)⁻¹ * (if (i : ℕ) = j then 2 + c else if (i : ℕ) + 1 = j then -1
        else if (j : ℕ) + 1 = i then -1 - c else 0) := rfl

/-- The reciprocal square of a nonzero step is positive. -/
private theorem inv_sq_pos {h : ℝ} (hh : h ≠ 0) : (0 : ℝ) < (h ^ 2)⁻¹ :=
  inv_pos.2 (lt_of_le_of_ne (sq_nonneg h) (Ne.symm (pow_ne_zero 2 hh)))

/-- The structural point of §2.2.4: for `c > 1` the centered matrix has a **positive**
off-diagonal entry, so it is not a Z-matrix and hence not an M-matrix.  This is why the
convergence theorems of Chapter 4 do not apply to the centered discretization of a
convection-dominated problem. -/
theorem convDiffCentered_not_isMMatrix {n : ℕ} (hn : 2 ≤ n) {h c : ℝ} (hh : h ≠ 0) (hc : 1 < c) :
    ¬ (convDiffCentered n h c).IsMMatrix := by
  intro hM
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  have hle := hM.offDiag_nonpos ⟨0, h0⟩ ⟨1, h1⟩ (by simp [Fin.ext_iff])
  have hval : convDiffCentered n h c ⟨0, h0⟩ ⟨1, h1⟩ = (h ^ 2)⁻¹ * (-1 + c) := by
    rw [convDiffCentered_apply]
    norm_num
  rw [hval] at hle
  nlinarith [inv_sq_pos hh]

/-- For `c > 1` the centered matrix is not even weakly diagonally dominant by rows: an interior
row has `|-1 - c| + |-1 + c| = 2c > 2`. -/
theorem convDiffCentered_not_diagDominant {n : ℕ} (hn : 3 ≤ n) {h c : ℝ} (hh : h ≠ 0)
    (hc : 1 < c) :
    ¬ ∀ i : Fin n, ∑ j ∈ univ.erase i, |convDiffCentered n h c i j|
        ≤ |convDiffCentered n h c i i| := by
  intro hd
  have hpos := inv_sq_pos (h := h) hh
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  have h2 : (2 : ℕ) < n := by omega
  have hsub : ({⟨0, h0⟩, ⟨2, h2⟩} : Finset (Fin n)) ⊆ univ.erase ⟨1, h1⟩ := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [Finset.mem_erase, Fin.ext_iff]
  have hle := (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun j _ _ => abs_nonneg _)).trans (hd ⟨1, h1⟩)
  rw [Finset.sum_pair (by simp [Fin.ext_iff])] at hle
  have e0 : convDiffCentered n h c ⟨1, h1⟩ ⟨0, h0⟩ = (h ^ 2)⁻¹ * (-1 - c) := by
    rw [convDiffCentered_apply]; norm_num
  have e2 : convDiffCentered n h c ⟨1, h1⟩ ⟨2, h2⟩ = (h ^ 2)⁻¹ * (-1 + c) := by
    rw [convDiffCentered_apply]; norm_num
  have ed : convDiffCentered n h c ⟨1, h1⟩ ⟨1, h1⟩ = (h ^ 2)⁻¹ * 2 := by
    rw [convDiffCentered_apply]; norm_num
  rw [e0, e2, ed, abs_of_nonpos (by nlinarith), abs_of_nonneg (by nlinarith),
    abs_of_nonneg (by nlinarith)] at hle
  nlinarith

/-- Weak diagonal dominance by rows, for a matrix with a nonnegative diagonal and nonpositive
off-diagonal entries, is exactly the nonnegativity of the row sums. -/
private theorem diagDominant_of_rowSum_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {i : Fin n}
    (hd : 0 ≤ A i i) (hoff : ∀ j, j ≠ i → A i j ≤ 0) (hrow : 0 ≤ ∑ j, A i j) :
    ∑ j ∈ univ.erase i, |A i j| ≤ |A i i| := by
  have h1 : ∑ j ∈ univ.erase i, |A i j| = -∑ j ∈ univ.erase i, A i j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj => abs_of_nonpos (hoff j (Finset.mem_erase.1 hj).1)
  have h2 : ∑ j ∈ univ.erase i, A i j = (∑ j, A i j) - A i i :=
    Finset.sum_erase_eq_sub (Finset.mem_univ i)
  rw [h1, h2, abs_of_nonneg hd]
  linarith

/-- The Dirichlet extension of the constant vector `1` takes values in `[0, 1]`: it is `1` at an
interior index and `0` at the two boundary indices. -/
private theorem dirichletExt_one_mem_Icc {n : ℕ} (k : ℕ) :
    0 ≤ dirichletExt (fun _ : Fin n => (1 : ℝ)) k ∧
      dirichletExt (fun _ : Fin n => (1 : ℝ)) k ≤ 1 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [dirichletExt_succ]
    split_ifs <;> norm_num

/-- The row sum of a tridiagonal matrix with constant diagonals, uniformly across the first, the
last and the interior rows. -/
private theorem tridiag_row_sum {n : ℕ} (sub diag sup : ℝ) (i : Fin n) :
    ∑ j : Fin n, (if (i : ℕ) = j then diag else if (i : ℕ) + 1 = j then sup
        else if (j : ℕ) + 1 = i then sub else 0)
      = sub * dirichletExt (fun _ : Fin n => (1 : ℝ)) (i : ℕ) + diag
        + sup * dirichletExt (fun _ : Fin n => (1 : ℝ)) ((i : ℕ) + 2) := by
  have hsplit : ∀ j : Fin n, (if (i : ℕ) = j then diag else if (i : ℕ) + 1 = j then sup
        else if (j : ℕ) + 1 = i then sub else 0)
      = (if (j : ℕ) + 1 = (i : ℕ) then sub * (1 : ℝ) else 0)
        + (if (j : ℕ) = (i : ℕ) then diag * (1 : ℝ) else 0)
        + (if (j : ℕ) = (i : ℕ) + 1 then sup * (1 : ℝ) else 0) := by
    intro j
    split_ifs <;> first | (exfalso; omega) | ring
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_ite_succ_dirichletExt, sum_ite_dirichletExt, sum_ite_dirichletExt,
    dirichletExt_coe_succ, mul_one]

/-- The other half of the structural point: for `c > 0` the upwind matrix has a positive
diagonal, nonpositive off-diagonal entries and is weakly diagonally dominant by rows — the
hypotheses under which Chapter 4's theorems do apply. -/
theorem convDiffUpwind_diagDominant {n : ℕ} {h c : ℝ} (hh : h ≠ 0) (hc : 0 ≤ c) :
    (∀ i : Fin n, 0 < convDiffUpwind n h c i i) ∧
      (∀ i j : Fin n, i ≠ j → convDiffUpwind n h c i j ≤ 0) ∧
      (∀ i : Fin n, ∑ j ∈ univ.erase i, |convDiffUpwind n h c i j|
        ≤ |convDiffUpwind n h c i i|) := by
  have hpos := inv_sq_pos (h := h) hh
  have hdiag : ∀ i : Fin n, convDiffUpwind n h c i i = (h ^ 2)⁻¹ * (2 + c) := fun i => by
    rw [convDiffUpwind_apply, ite_eq_left rfl]
  have hoff : ∀ i j : Fin n, i ≠ j → convDiffUpwind n h c i j ≤ 0 := by
    intro i j hij
    rw [convDiffUpwind_apply, ite_eq_right fun hE => hij (Fin.ext hE)]
    split_ifs <;> nlinarith
  refine ⟨fun i => ?_, hoff, fun i => ?_⟩
  · rw [hdiag i]; nlinarith
  · refine diagDominant_of_rowSum_nonneg (by rw [hdiag i]; nlinarith)
      (fun j hj => hoff i j (Ne.symm hj)) ?_
    have hrow : ∑ j : Fin n, convDiffUpwind n h c i j
        = (h ^ 2)⁻¹ * ((-1 - c) * dirichletExt (fun _ : Fin n => (1 : ℝ)) (i : ℕ) + (2 + c)
            + (-1) * dirichletExt (fun _ : Fin n => (1 : ℝ)) ((i : ℕ) + 2)) := by
      rw [← tridiag_row_sum (-1 - c) (2 + c) (-1) i, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => convDiffUpwind_apply n h c i j
    rw [hrow]
    obtain ⟨hl0, hu0⟩ := dirichletExt_one_mem_Icc (n := n) (i : ℕ)
    obtain ⟨hl2, hu2⟩ := dirichletExt_one_mem_Icc (n := n) ((i : ℕ) + 2)
    refine mul_nonneg hpos.le ?_
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 + c by linarith)
      (show (0 : ℝ) ≤ 1 - dirichletExt (fun _ : Fin n => (1 : ℝ)) (i : ℕ) by linarith)]

/-- Saad (2.22)–(2.23), the upwind approximation of `b(x) u'(x_i)`: whatever the sign of `b_i`,
taking the backward difference where `b_i > 0` and the forward difference where `b_i < 0` gives
the single formula `(-b_i⁺ u_{i-1} + |b_i| u_i + b_i⁻ u_{i+1})/h`, whose three coefficients have
nonnegative diagonal, nonpositive off-diagonal parts and sum to zero.  The identity behind it is
`SaadSparse.Chapter02.equation_2_53`, proved once in §2.5. -/
theorem equation_2_23 (b uprev ucur unext h : ℝ) :
    (max b 0 * (ucur - uprev) + min b 0 * (unext - ucur)) / h
        = (-(max b 0) * uprev + |b| * ucur + min b 0 * unext) / h ∧
      0 ≤ |b| ∧ -(max b 0) ≤ 0 ∧ min b 0 ≤ 0 ∧ -(max b 0) + |b| + min b 0 = 0 := by
  refine ⟨?_, abs_nonneg b, neg_nonpos.2 (le_max_right b 0), min_le_right b 0, ?_⟩
  · rw [max_zero_eq_half, min_zero_eq_half]; ring
  · rw [max_zero_eq_half, min_zero_eq_half]; ring

end ConvectionDiffusion

/-! ### §2.2.5–2.2.6 The two-dimensional model problem -/

section TwoDimensional

variable {n₁ n₂ : ℕ}

/-- Saad §2.2.5: the two-dimensional five-point matrix on an `n₁ × n₂` interior grid with the
natural row-wise ordering, indexed by the product `Fin n₁ × Fin n₂`.  The diagonal entry is
`2/h₁² + 2/h₂²`, a horizontal neighbour contributes `-1/h₁²` and a vertical one `-1/h₂²`.  Saad
displays the matrix without an equation number, and numbers the scaled copy (2.26)–(2.27). -/
noncomputable def laplacian2D (n₁ n₂ : ℕ) (h₁ h₂ : ℝ) :
    Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ :=
  Matrix.of fun p q =>
    if (p.1 : ℕ) = q.1 ∧ (p.2 : ℕ) = q.2 then 2 * (h₁ ^ 2)⁻¹ + 2 * (h₂ ^ 2)⁻¹
    else if (p.2 : ℕ) = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1) then -(h₁ ^ 2)⁻¹
    else if (p.1 : ℕ) = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2) then -(h₂ ^ 2)⁻¹
    else 0

theorem laplacian2D_apply (n₁ n₂ : ℕ) (h₁ h₂ : ℝ) (p q : Fin n₁ × Fin n₂) :
    laplacian2D n₁ n₂ h₁ h₂ p q =
      if (p.1 : ℕ) = q.1 ∧ (p.2 : ℕ) = q.2 then 2 * (h₁ ^ 2)⁻¹ + 2 * (h₂ ^ 2)⁻¹
      else if (p.2 : ℕ) = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1) then -(h₁ ^ 2)⁻¹
      else if (p.1 : ℕ) = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2) then -(h₂ ^ 2)⁻¹
      else 0 := rfl

/-- Saad (2.27): the diagonal block `B = tridiag(-1, 4, -1)` of the block form (2.26) of the
scaled five-point matrix. -/
noncomputable def blockB (p : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.symmTridiagonalToeplitz p (-1) 4

/-- Saad (2.27): the eigenvalues `λ_j = 4 - 2 cos(jπ/(p + 1))`, `j = 1, …, p`, of the block `B`,
in Saad's `1`-based numbering. -/
noncomputable def blockEigenvalue (p : ℕ) (j : Fin p) : ℝ :=
  4 - 2 * Real.cos ((((j : ℕ) : ℝ) + 1) * π / ((p : ℝ) + 1))

/-- The five-point matrix is the Kronecker sum of two one-dimensional model matrices, one for
each coordinate direction.  Saad writes neither this identity nor the spectrum it yields, and
both are what a reader of the block display (2.26) needs. -/
theorem laplacian2D_eq_kroneckerSum (n₁ n₂ : ℕ) (h₁ h₂ : ℝ) :
    laplacian2D n₁ n₂ h₁ h₂ = laplacian1D n₁ h₁ ⊕ₖ laplacian1D n₂ h₂ := by
  ext p q
  obtain ⟨i₁, i₂⟩ := p
  obtain ⟨j₁, j₂⟩ := q
  rw [Matrix.kroneckerSum_apply, laplacian1D_apply, laplacian1D_apply, laplacian2D_apply]
  simp only [← Fin.val_eq_val]
  split_ifs <;> first | (exfalso; omega) | ring

/-- The two conventions of §2.2.3 and §2.2.6: scaling the five-point matrix by `h²` removes the
mesh size and leaves the Kronecker sum of two copies of `tridiag(-1, 2, -1)`, which is the matrix
of (2.26)–(2.27). -/
theorem laplacian2D_smul (n₁ n₂ : ℕ) {h : ℝ} (hh : h ≠ 0) :
    h ^ 2 • laplacian2D n₁ n₂ h h
      = Matrix.symmTridiagonalToeplitz n₁ (-1) 2 ⊕ₖ Matrix.symmTridiagonalToeplitz n₂ (-1) 2 := by
  rw [laplacian2D_eq_kroneckerSum, ← Matrix.kroneckerSum_smul, laplacian1D, laplacian1D,
    smul_smul, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hh), one_smul, one_smul]

/-- Saad (2.26): the block form of the scaled five-point matrix.  Blocks are indexed by the first
(row-wise) coordinate; the diagonal blocks are `B = tridiag(-1, 4, -1)` and the blocks next to
the diagonal are `-I`, all other blocks vanishing. -/
theorem laplacian2D_block_apply (n₁ n₂ : ℕ) {h : ℝ} (hh : h ≠ 0) (i₁ j₁ : Fin n₁)
    (i₂ j₂ : Fin n₂) :
    (h ^ 2 • laplacian2D n₁ n₂ h h) (i₁, i₂) (j₁, j₂)
      = if (i₁ : ℕ) = j₁ then blockB n₂ i₂ j₂
        else if (i₁ : ℕ) + 1 = j₁ ∨ (j₁ : ℕ) + 1 = i₁ then -(1 : Matrix (Fin n₂) (Fin n₂) ℝ) i₂ j₂
        else 0 := by
  rw [laplacian2D_smul n₁ n₂ hh, Matrix.kroneckerSum_apply, blockB,
    Matrix.symmTridiagonalToeplitz_apply', Matrix.symmTridiagonalToeplitz_apply',
    Matrix.symmTridiagonalToeplitz_apply', Matrix.one_apply]
  simp only [← Fin.val_eq_val]
  split_ifs <;> ring

/-- The eigenpairs of the two-dimensional model matrix: the tensor product of the `k`-th and
`l`-th discrete sine vectors is an eigenvector with eigenvalue
`4 sin²(kπ/(2(n₁+1)))/h₁² + 4 sin²(lπ/(2(n₂+1)))/h₂²`, in Saad's `1`-based numbering. -/
theorem laplacian2D_mulVec_kroneckerVec (h₁ h₂ : ℝ) (k : Fin n₁) (l : Fin n₂) :
    laplacian2D n₁ n₂ h₁ h₂ *ᵥ Matrix.kroneckerVec (Matrix.sineVec n₁ k) (Matrix.sineVec n₂ l)
      = (4 * Real.sin ((((k : ℕ) : ℝ) + 1) * π / (2 * ((n₁ : ℝ) + 1))) ^ 2 / h₁ ^ 2
          + 4 * Real.sin ((((l : ℕ) : ℝ) + 1) * π / (2 * ((n₂ : ℝ) + 1))) ^ 2 / h₂ ^ 2)
        • Matrix.kroneckerVec (Matrix.sineVec n₁ k) (Matrix.sineVec n₂ l) := by
  rw [laplacian2D_eq_kroneckerSum]
  exact Matrix.kroneckerSum_mulVec_kroneckerVec_of_mulVec_eq_smul
    (laplacian1D_mulVec_sineVec h₁ k) (laplacian1D_mulVec_sineVec h₂ l)

/-- The two-dimensional model matrix is symmetric positive definite, because positive
definiteness adds under a Kronecker sum. -/
theorem laplacian2D_posDef (n₁ n₂ : ℕ) {h₁ h₂ : ℝ} (h₁0 : h₁ ≠ 0) (h₂0 : h₂ ≠ 0) :
    (laplacian2D n₁ n₂ h₁ h₂).PosDef := by
  rw [laplacian2D_eq_kroneckerSum]
  exact Matrix.posDef_kroneckerSum (laplacian1D_posDef n₁ h₁0) (laplacian1D_posDef n₂ h₂0)

/-! #### §2.2.6 The fast Poisson solver -/

/-- Saad (2.27): the orthogonal matrix `Q = [q₁, …, q_p]` whose `j`-th column is the normalized
discrete sine vector `q_j = √(2/(p+1)) w_j`. -/
noncomputable def sineMatrix (p : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => Real.sqrt (2 / ((p : ℝ) + 1)) * Matrix.sineVec p j i

theorem sineMatrix_apply (p : ℕ) (i j : Fin p) :
    sineMatrix p i j = Real.sqrt (2 / ((p : ℝ) + 1)) * Matrix.sineVec p j i := rfl

/-- The `j`-th column of `Q`, as a vector. -/
private theorem sineMatrix_col (p : ℕ) (j : Fin p) :
    (fun i => sineMatrix p i j) = Real.sqrt (2 / ((p : ℝ) + 1)) • Matrix.sineVec p j := by
  funext i
  rw [sineMatrix_apply, Pi.smul_apply, smul_eq_mul]

/-- Saad (2.27): `Q` is orthogonal. -/
theorem sineMatrix_transpose_mul_self (p : ℕ) : (sineMatrix p)ᵀ * sineMatrix p = 1 := by
  have hp : ((p : ℝ) + 1) ≠ 0 := by positivity
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ i : Fin p, (sineMatrix p)ᵀ j i * sineMatrix p i k
      = 2 / ((p : ℝ) + 1) * (Matrix.sineVec p j i * Matrix.sineVec p k i) := by
    intro i
    rw [Matrix.transpose_apply, sineMatrix_apply, sineMatrix_apply,
      show Real.sqrt (2 / ((p : ℝ) + 1)) * Matrix.sineVec p j i
          * (Real.sqrt (2 / ((p : ℝ) + 1)) * Matrix.sineVec p k i)
        = Real.sqrt (2 / ((p : ℝ) + 1)) * Real.sqrt (2 / ((p : ℝ) + 1))
          * (Matrix.sineVec p j i * Matrix.sineVec p k i) by ring,
      Real.mul_self_sqrt (by positivity)]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
  have hdot : ∑ i : Fin p, Matrix.sineVec p j i * Matrix.sineVec p k i
      = if j = k then ((p : ℝ) + 1) / 2 else 0 := Matrix.dotProduct_sineVec j k
  rw [hdot]
  split_ifs
  · field_simp
  · ring

/-- Saad (2.27): the columns of `Q` are eigenvectors of the block `B = tridiag(-1, 4, -1)` with
eigenvalues `λ_j = 4 - 2 cos(jπ/(p+1))`, `j = 1, …, p`. -/
theorem blockB_mulVec_sineVec (p : ℕ) (j : Fin p) :
    blockB p *ᵥ Matrix.sineVec p j = blockEigenvalue p j • Matrix.sineVec p j := by
  rw [blockB, Matrix.symmTridiagonalToeplitz_mulVec_sineVec, blockEigenvalue]
  congr 1
  ring

/-- Saad §2.2.6, the only spectral statement the book makes: the block `B` of (2.27) is
diagonalized by the orthogonal matrix `Q` of the normalized discrete sine vectors,
`Qᵀ B Q = diag(λ₁, …, λ_p)` with `λ_j = 4 - 2 cos(jπ/(p+1))`.  The book states it without
proof. -/
theorem equation_2_27_spectrum (p : ℕ) :
    (sineMatrix p)ᵀ * blockB p * sineMatrix p = Matrix.diagonal (blockEigenvalue p) := by
  have hcol : blockB p * sineMatrix p = sineMatrix p * Matrix.diagonal (blockEigenvalue p) := by
    ext i j
    have h1 : (blockB p * sineMatrix p) i j
        = (blockB p *ᵥ fun k => sineMatrix p k j) i := rfl
    rw [h1, sineMatrix_col, Matrix.mulVec_smul, blockB_mulVec_sineVec, Matrix.mul_diagonal,
      sineMatrix_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  rw [Matrix.mul_assoc, hcol, ← Matrix.mul_assoc, sineMatrix_transpose_mul_self, Matrix.one_mul]

/-- Algorithm 2.1, line 1: the coefficients of a grid function in the sine basis of the second
(within-block) index, `ū_i(j) = ∑_k Q_{k i} u(j, k)`. -/
noncomputable def sineCoeff {m p : ℕ} (u : Fin m × Fin p → ℝ) (i : Fin p) : Fin m → ℝ :=
  fun j => ∑ k, sineMatrix p k i * u (j, k)

theorem sineCoeff_apply {m p : ℕ} (u : Fin m × Fin p → ℝ) (i : Fin p) (j : Fin m) :
    sineCoeff u i j = ∑ k, sineMatrix p k i * u (j, k) := rfl

/-- Shifting the diagonal of a symmetric tridiagonal Toeplitz matrix: `tridiag(a, b + c, a)` is
`tridiag(a, b, a) + c I`.  This is what turns the decoupled system of (2.29) into a tridiagonal
Toeplitz one. -/
private theorem symmTridiagonalToeplitz_add_diag (m : ℕ) (a b c : ℝ) :
    Matrix.symmTridiagonalToeplitz m a (b + c)
      = Matrix.symmTridiagonalToeplitz m a b + c • 1 := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    Matrix.symmTridiagonalToeplitz_apply', Matrix.symmTridiagonalToeplitz_apply']
  simp only [← Fin.val_eq_val]
  split_ifs <;> ring

/-- The row of a Kronecker sum, split into its two directions: the `(j, k)` component of
`(A ⊕ₖ B) *ᵥ v` is the `A`-row along the first index plus the `B`-row along the second. -/
private theorem kroneckerSum_mulVec_apply {m p : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin p) (Fin p) ℝ) (v : Fin m × Fin p → ℝ) (j : Fin m) (k : Fin p) :
    ((A ⊕ₖ B) *ᵥ v) (j, k) = (∑ j', A j j' * v (j', k)) + ∑ k', B k k' * v (j, k') := by
  rw [Matrix.mulVec_apply_eq_sum, Fintype.sum_prod_type]
  have hterm : ∀ (j' : Fin m) (k' : Fin p), (A ⊕ₖ B) (j, k) (j', k') * v (j', k')
      = (if k = k' then A j j' * v (j', k') else 0)
        + if j = j' then B k k' * v (j', k') else 0 := by
    intro j' k'
    rw [Matrix.kroneckerSum_apply]
    split_ifs <;> ring
  simp only [hterm]
  rw [Finset.sum_congr rfl fun j' _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.sum_ite_eq Finset.univ k fun k' => A j j' * v (j', k')]
    simp
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Finset.sum_ite_eq Finset.univ j fun j' => B k k' * v (j', k')]
    simp

/-- Saad (2.28)–(2.29) and Algorithm 2.1, the fast Poisson solver: conjugating the scaled
five-point matrix by `Q` in the within-block index replaces the block `B` by `diag λ` and
decouples the system into `p` independent tridiagonal systems `tridiag(-1, λ_i, -1) ū_i = b̄_i`
of size `m`.  The fast Fourier transform that computes `Qᵀ u` and the operation count are
implementation, not statements.  The book prints the indices of (2.29) transposed, giving systems
of the wrong size; the statement here follows Algorithm 2.1. -/
theorem equation_2_29 {m p : ℕ} {u b : Fin m × Fin p → ℝ}
    (hub : (Matrix.symmTridiagonalToeplitz m (-1) 2 ⊕ₖ Matrix.symmTridiagonalToeplitz p (-1) 2)
      *ᵥ u = b) (i : Fin p) :
    Matrix.symmTridiagonalToeplitz m (-1) (blockEigenvalue p i) *ᵥ sineCoeff u i
      = sineCoeff b i := by
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, blockEigenvalue p i = 2 + μ := ⟨blockEigenvalue p i - 2, by ring⟩
  have hμ' : μ = 2 + 2 * (-1) * Real.cos ((((i : ℕ) : ℝ) + 1) * π / ((p : ℝ) + 1)) := by
    rw [blockEigenvalue] at hμ; linarith
  have hsymm : ∀ k k' : Fin p, Matrix.symmTridiagonalToeplitz p (-1) 2 k k'
      = Matrix.symmTridiagonalToeplitz p (-1) 2 k' k := by
    intro k k'
    rw [Matrix.symmTridiagonalToeplitz_apply', Matrix.symmTridiagonalToeplitz_apply']
    split_ifs <;> first | rfl | (exfalso; omega)
  -- The `i`-th column of `Q` is a left eigenvector of `T_p` for `μ = λ_i - 2`.
  have hcol : ∀ k' : Fin p,
      ∑ k : Fin p, sineMatrix p k i * Matrix.symmTridiagonalToeplitz p (-1) 2 k k'
        = μ * sineMatrix p k' i := by
    intro k'
    have h1 : ∑ k : Fin p, sineMatrix p k i * Matrix.symmTridiagonalToeplitz p (-1) 2 k k'
        = (Matrix.symmTridiagonalToeplitz p (-1) 2 *ᵥ fun k => sineMatrix p k i) k' := by
      rw [Matrix.mulVec_apply_eq_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hsymm k k', mul_comm]
    rw [h1, sineMatrix_col, Matrix.mulVec_smul,
      Matrix.symmTridiagonalToeplitz_mulVec_sineVec, sineMatrix_apply, hμ']
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hstep : ∀ (j : Fin m) (k : Fin p), sineMatrix p k i
        * ((Matrix.symmTridiagonalToeplitz m (-1) 2 ⊕ₖ Matrix.symmTridiagonalToeplitz p (-1) 2)
          *ᵥ u) (j, k)
      = (∑ j' : Fin m, sineMatrix p k i * (Matrix.symmTridiagonalToeplitz m (-1) 2 j j'
          * u (j', k)))
        + ∑ k' : Fin p, sineMatrix p k i * (Matrix.symmTridiagonalToeplitz p (-1) 2 k k'
          * u (j, k')) := by
    intro j k
    rw [kroneckerSum_mulVec_apply, mul_add, Finset.mul_sum, Finset.mul_sum]
  funext j
  have hrhs : sineCoeff b i j
      = (∑ j' : Fin m, Matrix.symmTridiagonalToeplitz m (-1) 2 j j' * sineCoeff u i j')
        + μ * sineCoeff u i j := by
    rw [← hub, sineCoeff_apply, Finset.sum_congr rfl fun k _ => hstep j k,
      Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [sineCoeff_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    · rw [Finset.sum_comm, sineCoeff_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k' _ => ?_
      have hin : ∑ k : Fin p, sineMatrix p k i
            * (Matrix.symmTridiagonalToeplitz p (-1) 2 k k' * u (j, k'))
          = (∑ k : Fin p, sineMatrix p k i * Matrix.symmTridiagonalToeplitz p (-1) 2 k k')
            * u (j, k') := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hin, hcol k']
      ring
  rw [hrhs, hμ, symmTridiagonalToeplitz_add_diag, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply_eq_sum]

/-! #### §2.2.7 Block cyclic reduction -/

/-- Saad (2.33): the block cyclic reduction sequence `B⁽⁰⁾ = B`, `B⁽ʳ⁺¹⁾ = (B⁽ʳ⁾)² - 2 I`.  The
numeral `2` is the matrix `2 I`, as the book's display has it. -/
noncomputable def cyclicReduction {p : ℕ} (B : Matrix (Fin p) (Fin p) ℝ) : ℕ →
    Matrix (Fin p) (Fin p) ℝ
  | 0 => B
  | r + 1 => cyclicReduction B r ^ 2 - 2

/-- The duplication formula of the Vieta–Lucas polynomials, `C_{2k} = C_k² - 2`, which is
Mathlib's `Polynomial.Chebyshev.C_mul_C` at `m = k` together with `C_0 = 2`.  It is the
polynomial form of the cyclic reduction recurrence. -/
private theorem chebyshevC_two_mul (k : ℤ) :
    Polynomial.Chebyshev.C ℝ (2 * k) = Polynomial.Chebyshev.C ℝ k ^ 2 - 2 := by
  have hC := Polynomial.Chebyshev.C_mul_C ℝ k k
  rw [sub_self, Polynomial.Chebyshev.C_zero, show k + k = 2 * k by ring] at hC
  linear_combination -hC

/-- Saad (2.33): the block cyclic reduction sequence is the Vieta–Lucas polynomial `C_{2^r}`
evaluated at `B`, and `C_m` is `2 T_m(·/2)`, so `B⁽ʳ⁾ = 2 T_{2^r}(B/2)`.  The induction step is the
duplication formula `C_{2k} = C_k² - 2`.  The root factorization of that polynomial is (2.36),
`equation_2_36` below. -/
theorem equation_2_33 {p : ℕ} (B : Matrix (Fin p) (Fin p) ℝ) (r : ℕ) :
    cyclicReduction B r = Polynomial.aeval B (Polynomial.Chebyshev.C ℝ ((2 : ℤ) ^ r)) := by
  induction r with
  | zero => simp [cyclicReduction, Polynomial.Chebyshev.C_one]
  | succ r ih =>
    have hpow : (2 : ℤ) ^ (r + 1) = 2 * (2 : ℤ) ^ r := by ring
    rw [show cyclicReduction B (r + 1) = cyclicReduction B r ^ 2 - 2 from rfl, ih, hpow,
      chebyshevC_two_mul, map_sub, map_pow, map_ofNat]

/-- Saad (2.36) read on the sine eigenbasis: the cyclic reduction sequence acts on the
eigenvectors of `B` by the scalar recurrence `μ ↦ μ² - 2`, so its eigenvalues are
`C_{2^r}(λ_j)` for the eigenvalues `λ_j` of `B`. -/
theorem cyclicReduction_mulVec_of_mulVec_eq_smul {p : ℕ} {B : Matrix (Fin p) (Fin p) ℝ}
    {v : Fin p → ℝ} {μ : ℝ} (hv : B *ᵥ v = μ • v) (r : ℕ) :
    cyclicReduction B r *ᵥ v = Polynomial.eval μ (Polynomial.Chebyshev.C ℝ ((2 : ℤ) ^ r)) • v := by
  induction r with
  | zero => simpa [cyclicReduction, Polynomial.Chebyshev.C_one] using hv
  | succ r ih =>
    have hpow : (2 : ℤ) ^ (r + 1) = 2 * (2 : ℤ) ^ r := by ring
    have htwo : ((2 : Matrix (Fin p) (Fin p) ℝ)) *ᵥ v = (2 : ℝ) • v := by
      simp [two_smul]
    have hev : Polynomial.eval μ (Polynomial.Chebyshev.C ℝ ((2 : ℤ) ^ r) ^ 2 - 2)
        = Polynomial.eval μ (Polynomial.Chebyshev.C ℝ ((2 : ℤ) ^ r)) ^ 2 - 2 := by simp
    rw [show cyclicReduction B (r + 1) = cyclicReduction B r ^ 2 - 2 from rfl, hpow,
      chebyshevC_two_mul, Matrix.sub_mulVec, pow_two (cyclicReduction B r),
      ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, ih, htwo, hev]
    module

/-- Evaluating a product of monic linear factors at a matrix: `aeval` is multiplicative, and the
image is an ordered product because the matrices do not commute in general — these particular ones
do, being polynomials in `B`, but nothing in the statement needs that. -/
private theorem aeval_prod_X_sub_C {p : ℕ} (B : Matrix (Fin p) (Fin p) ℝ) (c : ℕ → ℝ) (m : ℕ) :
    Polynomial.aeval B (∏ k ∈ Finset.range m, (Polynomial.X - Polynomial.C (c k)))
      = ((List.range m).map fun k => B - c k • (1 : Matrix (Fin p) (Fin p) ℝ)).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, map_mul, ih, List.range_succ, List.map_append, List.prod_append]
    simp [Algebra.algebraMap_eq_smul_one]

/-- **Saad (2.36)**, the root factorization of the cyclic reduction operator:
`B⁽ʳ⁾ = ∏_{i=1}^{h} (B - λ_i^{(r)} I)` with `h = 2^r` and `λ_i^{(r)} = 2 cos((2i - 1)π/(2h))`, so
that the solves with `B⁽ʳ⁾` on lines 5 and 14 of Algorithm 2.2 split into `h` tridiagonal solves.
The product below runs over `i = 0, …, h - 1` and writes the node as `2 cos((2i + 1)π/(2h))`, which
is the book's list of `h` nodes with the index shifted by one; it is a `List.prod` because the
matrices carry no commutative multiplication, although these factors do commute.

It is the backbone's `Polynomial.Chebyshev.C_natCast_eq_prod` — the Vieta–Lucas polynomial `C_h` is
monic of degree `h` with the `h` distinct real roots above — carried across the algebra map
`Polynomial.aeval B` by (2.33). -/
theorem equation_2_36 {p : ℕ} (B : Matrix (Fin p) (Fin p) ℝ) (r : ℕ) :
    cyclicReduction B r = ((List.range (2 ^ r)).map fun i : ℕ =>
        B - (2 * Real.cos ((2 * i + 1) * π / (2 * 2 ^ r))) •
          (1 : Matrix (Fin p) (Fin p) ℝ)).prod := by
  have hne : (2 : ℕ) ^ r ≠ 0 := (Nat.two_pow_pos r).ne'
  have hcast : ((2 ^ r : ℕ) : ℤ) = (2 : ℤ) ^ r := by push_cast; ring
  rw [equation_2_33, ← hcast, Polynomial.Chebyshev.C_natCast_eq_prod hne, aeval_prod_X_sub_C]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  have hnode : Polynomial.Chebyshev.rootNode (2 ^ r) k
      = 2 * Real.cos ((2 * k + 1) * π / (2 * 2 ^ r)) := by
    rw [Polynomial.Chebyshev.rootNode]
    push_cast
    ring_nf
  rw [hnode]

end TwoDimensional

end SaadSparse.Chapter02
