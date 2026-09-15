import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Order.IntermediateValue
import Numlib.Approximation.GaussLobatto

/-!
# Finite-difference approximation of derivatives

The forward, backward and centred difference quotients and the second centred difference of a
function of one real variable, each with its truncation error in mean-value form; the general
implicit ("compact") three-point scheme for the first derivative, its consistency error and the
order conditions; and the differentiation matrix `D i j = ℓ_j'(x i)` of Lagrange interpolation,
through which the derivative of the interpolant at the nodes is a matrix–vector product.

**Truncation errors.** Every mean-value error is Taylor's theorem with the Lagrange remainder
(`taylor_mean_remainder_lagrange`) at one or two expansion points. The two one-sided quotients are
stated for a function that is `C²` on the closed interval between the two points only, so the
derivative being approximated is the one-sided `derivWithin` at the endpoint
(`FiniteDifference.derivWithin_sub_forwardDiff_eq`); the two-sided `deriv` needs differentiability
at the point as an extra hypothesis (`FiniteDifference.deriv_sub_forwardDiff_eq`). For the two
centred quotients the base point is interior and everything is two-sided. Where the book states a
single intermediate point for a two-sided difference, the two Lagrange remainders are averaged and
the intermediate value theorem for the continuous top derivative supplies the point
(`FiniteDifference.deriv_sub_centredDiff_eq`,
`FiniteDifference.iteratedDeriv_two_sub_secondCentredDiff_eq_one_point`).

**Compact schemes.** The scheme `α u_{i-1} + u_i + α u_{i+1} = (β/2h)(f_{i+1} - f_{i-1}) +
(γ/4h)(f_{i+2} - f_{i-2})` has the consistency error `FiniteDifference.compactError`, obtained by
forcing `f` itself to satisfy it. Its expansion `FiniteDifference.compactError_expansion` is an
`IsBigO` statement along `𝓝[≠] 0` in the step — the error divides by the step, so it is junk at
`h = 0` and the punctured neighbourhood is the correct filter — and the three order conditions
`compactError_isBigO_pow_two`, `_four`, `_six` read off its coefficients. The coefficients here are
the correct ones; the printed expansion of [quarteroni2000numerical] §10.10.2 carries a spurious
factor `1/2` on both `h²` terms, which does not affect the order conditions.

**The differentiation matrix** `Lagrange.derivMatrix v` is stated for any finite family of nodes
over any field, and `Lagrange.eval_derivative_interpolate_node` needs no injectivity: it is
linearity of `derivative` and `eval` over the Lagrange basis expansion of the interpolant. Its
entries are the derivatives of the Lagrange basis polynomials at the nodes, which the nodal
polynomial `ω = ∏ (X - x_k)` expresses as `ℓ_j'(x_l) = ω'(x_l) / ((x_l - x_j) ω'(x_j))` off the
diagonal and `ℓ_j'(x_j) = ω''(x_j) / (2 ω'(x_j))` on it (`Lagrange.eval_derivative_basis_of_ne`,
`Lagrange.eval_derivative_basis_self_of_injOn`); both formulas are invariant under scaling `ω`, so
any nonzero multiple of the nodal polynomial serves.

**The Chebyshev–Gauss–Lobatto matrix.** At the nodes `x_j = cos (jπ/n)`, `j = 0, …, n`
(Mathlib's `Polynomial.Chebyshev.node`), the nodal polynomial is a multiple of
`(X² - 1) T_n'`, whose derivatives at the nodes come from the Chebyshev differential equation
`(1 - X²) T_n'' = X T_n' - n² T_n` and the values `T_n(x_j) = (-1)^j`, `T_n'(1) = n²`,
`T_n'(-1) = -(-1)^n n²`. The result, `Lagrange.chebyshevLobattoDerivMatrix_apply`, is the formula
of Canuto–Hussaini–Quarteroni–Zang, *Spectral Methods in Fluid Dynamics* (1988), p. 69:
`D_{lj} = (d_l/d_j) (-1)^{l+j}/(x_l - x_j)` for `l ≠ j`, `D_{jj} = -x_j/(2(1 - x_j²))` at the
interior nodes, `D_{00} = (2n² + 1)/6` and `D_{nn} = -(2n² + 1)/6`, with `d_0 = d_n = 2` and
`d_j = 1` otherwise. [quarteroni2000numerical] (10.73) states it at the reflected nodes
`x̄_j = -x_j`, where the whole matrix changes sign (`Lagrange.derivMatrix_neg`): the off-diagonal
and interior-diagonal formulas keep their form, `D̄_{00} = -(2n² + 1)/6` and
`D̄_{nn} = (2n² + 1)/6` — the book prints `D̄_{nn} = (2n² + 1)/3`, an erratum (`D` has zero trace).

The material is [quarteroni2000numerical] §10.10; the same quotients are the stencils of the
finite-difference schemes of chapters 12 and 13 there and of [kress1998numerical] §9.5.
-/

open Set Filter Topology Asymptotics Finset Polynomial Matrix
open scoped Nat

namespace FiniteDifference

/-! ### Taylor's theorem in two-sided form -/

section Taylor

variable {f : ℝ → ℝ} {x₀ x : ℝ} {n : ℕ}

/-- Taylor's theorem with the Lagrange remainder, the derivative in the remainder being the
two-sided `iteratedDeriv` (the intermediate point is interior to the interval). -/
theorem exists_taylorWithinEval_add_iteratedDeriv_mul (hne : x₀ ≠ x)
    (hf : ContDiffOn ℝ (n + 1) f (uIcc x₀ x)) :
    ∃ ξ ∈ uIoo x₀ x, f x = taylorWithinEval f n (uIcc x₀ x) x₀ x
      + iteratedDeriv (n + 1) f ξ * (x - x₀) ^ (n + 1) / (n + 1)! := by
  have hs : UniqueDiffOn ℝ (uIcc x₀ x) := uniqueDiffOn_uIcc hne
  have hsub : uIoo x₀ x ⊆ uIcc x₀ x := Ioo_subset_Icc_self
  obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange hne (hf.of_le (by exact_mod_cast n.le_succ))
    ((hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast n.lt_succ_self) hs).mono hsub)
  refine ⟨ξ, hξ, ?_⟩
  have hξ' : uIcc x₀ x ∈ 𝓝 ξ := mem_nhds_iff.2 ⟨uIoo x₀ x, hsub, isOpen_Ioo, hξ⟩
  rw [iteratedDerivWithin_eq_iteratedDeriv hs (hf.contDiffAt hξ') (hsub hξ)] at h
  linarith

/-- The Taylor polynomial of `f` at an interior point `x₀` of a set on which `f` is `C^n`, written
with the two-sided iterated derivatives. -/
theorem taylorWithinEval_eq_sum_of_contDiffAt (hne : x₀ ≠ x) (hf : ContDiffAt ℝ n f x₀) :
    taylorWithinEval f n (uIcc x₀ x) x₀ x
      = ∑ k ∈ range (n + 1), (x - x₀) ^ k / k ! * iteratedDeriv k f x₀ := by
  rw [taylor_within_apply]
  refine sum_congr rfl fun k hk => ?_
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
    (hf.of_le (by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hk))) left_mem_uIcc, smul_eq_mul]
  ring

/-- **Taylor's theorem with a uniform remainder bound on a ball**: if `f` is `C^{n+1}` on
`ball x ε` with `|f^{(n+1)}| ≤ M` there, then for every `y` in the ball
`|f y - ∑_{k ≤ n} (y - x)^k / k! f^{(k)}(x)| ≤ M |y - x|^{n+1} / (n + 1)!`. -/
theorem abs_sub_sum_taylor_le {ε M : ℝ} (hf : ContDiffOn ℝ (n + 1) f (Metric.ball x₀ ε))
    (hM : ∀ t ∈ Metric.ball x₀ ε, |iteratedDeriv (n + 1) f t| ≤ M) {y : ℝ}
    (hy : y ∈ Metric.ball x₀ ε) :
    |f y - ∑ k ∈ range (n + 1), (y - x₀) ^ k / k ! * iteratedDeriv k f x₀|
      ≤ M * |y - x₀| ^ (n + 1) / (n + 1)! := by
  have hx₀ : x₀ ∈ Metric.ball x₀ ε := Metric.mem_ball_self (Metric.pos_of_mem_ball hy)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀ hx₀)
  rcases eq_or_ne x₀ y with rfl | hne
  · rw [sum_range_succ', sub_self]
    simp
  have hsub : uIcc x₀ y ⊆ Metric.ball x₀ ε := fun t ht => by
    rw [Metric.mem_ball, Real.dist_eq]
    exact (abs_sub_left_of_mem_uIcc ht).trans_lt (by rwa [Metric.mem_ball, Real.dist_eq] at hy)
  obtain ⟨ξ, hξ, hT⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul hne (hf.mono hsub)
  rw [taylorWithinEval_eq_sum_of_contDiffAt hne
    ((hf.contDiffAt (Metric.isOpen_ball.mem_nhds hx₀)).of_le (by exact_mod_cast n.le_succ))] at hT
  rw [hT, add_sub_cancel_left, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  gcongr
  exact hM ξ (hsub (Ioo_subset_Icc_self hξ))

end Taylor

/-! ### The classical difference quotients -/

section Quotients

variable {f : ℝ → ℝ} {x h : ℝ}

/-- The forward difference quotient `(f (x + h) - f x) / h` ([quarteroni2000numerical] (10.59)).
-/
noncomputable def forwardDiff (f : ℝ → ℝ) (h x : ℝ) : ℝ := (f (x + h) - f x) / h

/-- The backward difference quotient `(f x - f (x - h)) / h` ([quarteroni2000numerical] (10.63)).
-/
noncomputable def backwardDiff (f : ℝ → ℝ) (h x : ℝ) : ℝ := (f x - f (x - h)) / h

/-- The centred difference quotient `(f (x + h) - f (x - h)) / (2 h)`
([quarteroni2000numerical] (10.61)). -/
noncomputable def centredDiff (f : ℝ → ℝ) (h x : ℝ) : ℝ := (f (x + h) - f (x - h)) / (2 * h)

/-- The second centred difference `(f (x + h) - 2 f x + f (x - h)) / h²`
([quarteroni2000numerical] (10.65)). -/
noncomputable def secondCentredDiff (f : ℝ → ℝ) (h x : ℝ) : ℝ :=
  (f (x + h) - 2 * f x + f (x - h)) / h ^ 2

/-- Unfolding `forwardDiff`. -/
theorem forwardDiff_apply : forwardDiff f h x = (f (x + h) - f x) / h := rfl

/-- Unfolding `backwardDiff`. -/
theorem backwardDiff_apply : backwardDiff f h x = (f x - f (x - h)) / h := rfl

/-- Unfolding `centredDiff`. -/
theorem centredDiff_apply : centredDiff f h x = (f (x + h) - f (x - h)) / (2 * h) := rfl

/-- Unfolding `secondCentredDiff`. -/
theorem secondCentredDiff_apply :
    secondCentredDiff f h x = (f (x + h) - 2 * f x + f (x - h)) / h ^ 2 := rfl

/-- The backward quotient with step `h` is the forward quotient with step `-h`. -/
theorem backwardDiff_eq_forwardDiff_neg : backwardDiff f h x = forwardDiff f (-h) x := by
  rw [backwardDiff, forwardDiff, ← sub_eq_add_neg, div_neg, ← neg_div, neg_sub]

/-- The centred quotient is the mean of the forward and backward quotients. -/
theorem centredDiff_eq_add_div_two :
    centredDiff f h x = (forwardDiff f h x + backwardDiff f h x) / 2 := by
  simp only [centredDiff, forwardDiff, backwardDiff]
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  · field_simp
    ring

/-- The second centred difference is the forward difference of the backward difference. -/
theorem secondCentredDiff_eq_forwardDiff_backwardDiff :
    secondCentredDiff f h x = forwardDiff (backwardDiff f h) h x := by
  simp only [secondCentredDiff, forwardDiff, backwardDiff, add_sub_cancel_right]
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  · field_simp
    ring

/-- **The forward difference error** ([quarteroni2000numerical] (10.60)): for `f` of class `C²`
on `[x, x + h]`, `f'(x) - (f (x + h) - f x)/h = -(h/2) f''(ξ)` for some `ξ ∈ (x, x + h)`. The
derivative at the left endpoint is the one-sided `derivWithin`. -/
theorem derivWithin_sub_forwardDiff_eq (hh : 0 < h) (hf : ContDiffOn ℝ 2 f (Icc x (x + h))) :
    ∃ ξ ∈ Ioo x (x + h),
      derivWithin f (Icc x (x + h)) x - forwardDiff f h x = -(h / 2) * iteratedDeriv 2 f ξ := by
  have hle : x ≤ x + h := by linarith
  have hne : x ≠ x + h := by linarith
  have hI : uIcc x (x + h) = Icc x (x + h) := uIcc_of_le hle
  have hf' : ContDiffOn ℝ (1 + 1) f (uIcc x (x + h)) := by rw [hI]; exact hf
  obtain ⟨ξ, hξ, hT⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul hne hf'
  rw [uIoo_of_le hle] at hξ
  refine ⟨ξ, hξ, ?_⟩
  rw [taylor_within_apply, hI] at hT
  simp only [sum_range_succ, sum_range_one, iteratedDerivWithin_zero, iteratedDerivWithin_one,
    Nat.factorial, smul_eq_mul, add_sub_cancel_left] at hT
  rw [forwardDiff_apply, hT]
  field_simp
  ring

/-- **The forward difference error** for `f` differentiable at `x` and `C²` on `[x, x + h]`:
`deriv f x - forwardDiff f h x = -(h/2) f''(ξ)` for some `ξ ∈ (x, x + h)`
([quarteroni2000numerical] (10.60)). -/
theorem deriv_sub_forwardDiff_eq (hh : 0 < h) (hf : ContDiffOn ℝ 2 f (Icc x (x + h)))
    (hd : DifferentiableAt ℝ f x) :
    ∃ ξ ∈ Ioo x (x + h), deriv f x - forwardDiff f h x = -(h / 2) * iteratedDeriv 2 f ξ := by
  rw [← hd.hasDerivAt.hasDerivWithinAt.derivWithin
    ((uniqueDiffOn_Icc (show x < x + h by linarith)).uniqueDiffWithinAt
      (left_mem_Icc.2 (by linarith)))]
  exact derivWithin_sub_forwardDiff_eq hh hf

/-- **The backward difference error** ([quarteroni2000numerical] (10.64)): for `f` of class `C²`
on `[x - h, x]`, `f'(x) - (f x - f (x - h))/h = (h/2) f''(ξ)` for some `ξ ∈ (x - h, x)`. The
derivative at the right endpoint is the one-sided `derivWithin`. -/
theorem derivWithin_sub_backwardDiff_eq (hh : 0 < h) (hf : ContDiffOn ℝ 2 f (Icc (x - h) x)) :
    ∃ ξ ∈ Ioo (x - h) x,
      derivWithin f (Icc (x - h) x) x - backwardDiff f h x = (h / 2) * iteratedDeriv 2 f ξ := by
  have hge : x - h ≤ x := by linarith
  have hne : x ≠ x - h := by linarith
  have hI : uIcc x (x - h) = Icc (x - h) x := uIcc_of_ge hge
  have hf' : ContDiffOn ℝ (1 + 1) f (uIcc x (x - h)) := by rw [hI]; exact hf
  obtain ⟨ξ, hξ, hT⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul hne hf'
  rw [uIoo_of_ge hge] at hξ
  refine ⟨ξ, hξ, ?_⟩
  rw [taylor_within_apply, hI] at hT
  simp only [sum_range_succ, sum_range_one, iteratedDerivWithin_zero, iteratedDerivWithin_one,
    Nat.factorial, smul_eq_mul, sub_sub_cancel_left] at hT
  rw [backwardDiff_apply, hT]
  field_simp
  ring

/-- **The backward difference error** for `f` differentiable at `x` and `C²` on `[x - h, x]`
([quarteroni2000numerical] (10.64)). -/
theorem deriv_sub_backwardDiff_eq (hh : 0 < h) (hf : ContDiffOn ℝ 2 f (Icc (x - h) x))
    (hd : DifferentiableAt ℝ f x) :
    ∃ ξ ∈ Ioo (x - h) x, deriv f x - backwardDiff f h x = (h / 2) * iteratedDeriv 2 f ξ := by
  rw [← hd.hasDerivAt.hasDerivWithinAt.derivWithin
    ((uniqueDiffOn_Icc (show x - h < x by linarith)).uniqueDiffWithinAt
      (right_mem_Icc.2 (by linarith)))]
  exact derivWithin_sub_backwardDiff_eq hh hf

/-- A function `C^n` on `Icc (x - h) (x + h)` is `C^n` at every point of the open interval. -/
private theorem contDiffAt_of_mem_Ioo {n : ℕ} (hf : ContDiffOn ℝ n f (Icc (x - h) (x + h)))
    {y : ℝ} (hy : y ∈ Ioo (x - h) (x + h)) : ContDiffAt ℝ n f y :=
  hf.contDiffAt (Icc_mem_nhds hy.1 hy.2)

/-- The `n`-th derivative of a function `C^n` on `Icc (x - h) (x + h)` is continuous on the open
interval. -/
private theorem continuousOn_iteratedDeriv_Ioo {n : ℕ} (hh : 0 < h)
    (hf : ContDiffOn ℝ n f (Icc (x - h) (x + h))) :
    ContinuousOn (iteratedDeriv n f) (Ioo (x - h) (x + h)) := by
  have hs : UniqueDiffOn ℝ (Icc (x - h) (x + h)) := uniqueDiffOn_Icc (by linarith)
  refine ((hf.continuousOn_iteratedDerivWithin le_rfl hs).mono Ioo_subset_Icc_self).congr
    fun y hy => ?_
  exact (iteratedDerivWithin_eq_iteratedDeriv hs (contDiffAt_of_mem_Ioo hf hy)
    (Ioo_subset_Icc_self hy)).symm

/-- The mean of two values of a function continuous on an interval is attained between the two
points: the intermediate value theorem in the form the two-sided difference errors use. -/
private theorem exists_eq_add_div_two {g : ℝ → ℝ} {a b s t : ℝ}
    (hg : ContinuousOn g (Ioo a b)) (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    ∃ ξ ∈ Ioo a b, g ξ = (g s + g t) / 2 := by
  have hsub : uIcc s t ⊆ Ioo a b := ordConnected_Ioo.uIcc_subset hs ht
  have hmem : (g s + g t) / 2 ∈ uIcc (g s) (g t) := by
    rcases le_total (g s) (g t) with hst | hst
    · exact ⟨by rw [inf_eq_left.2 hst]; linarith, by rw [sup_eq_right.2 hst]; linarith⟩
    · exact ⟨by rw [inf_eq_right.2 hst]; linarith, by rw [sup_eq_left.2 hst]; linarith⟩
  obtain ⟨ξ, hξ, hgξ⟩ := intermediate_value_uIcc (hg.mono hsub) hmem
  exact ⟨ξ, hsub hξ, hgξ⟩

/-- **The centred difference error in two-point form**: for `f` of class `C³` on
`[x - h, x + h]`, `f'(x) - (f (x + h) - f (x - h))/(2h) = -(h²/12)(f'''(ξ) + f'''(η))` with
`ξ ∈ (x - h, x)` and `η ∈ (x, x + h)`, the two Lagrange remainders of the Taylor expansions at
`x`. -/
theorem deriv_sub_centredDiff_eq_two_points (hh : 0 < h)
    (hf : ContDiffOn ℝ 3 f (Icc (x - h) (x + h))) :
    ∃ ξ ∈ Ioo (x - h) x, ∃ η ∈ Ioo x (x + h),
      deriv f x - centredDiff f h x
        = -(h ^ 2 / 12) * (iteratedDeriv 3 f ξ + iteratedDeriv 3 f η) := by
  have hx : ContDiffAt ℝ 3 f x := contDiffAt_of_mem_Ioo hf ⟨by linarith, by linarith⟩
  have hnep : x ≠ x + h := by linarith
  have hnem : x ≠ x - h := by linarith
  have hfp : ContDiffOn ℝ (2 + 1) f (uIcc x (x + h)) :=
    hf.mono (by rw [Set.uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) le_rfl)
  have hfm : ContDiffOn ℝ (2 + 1) f (uIcc x (x - h)) :=
    hf.mono (by rw [Set.uIcc_of_ge (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith))
  obtain ⟨η, hη, hTp⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul hnep hfp
  obtain ⟨ξ, hξ, hTm⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul hnem hfm
  rw [uIoo_of_le (by linarith)] at hη
  rw [uIoo_of_ge (by linarith)] at hξ
  rw [taylorWithinEval_eq_sum_of_contDiffAt hnep (hx.of_le (by norm_num))] at hTp
  rw [taylorWithinEval_eq_sum_of_contDiffAt hnem (hx.of_le (by norm_num))] at hTm
  simp only [sum_range_succ, sum_range_zero, Nat.factorial, iteratedDeriv_zero, iteratedDeriv_one,
    add_sub_cancel_left, sub_sub_cancel_left] at hTp hTm
  refine ⟨ξ, hξ, η, hη, ?_⟩
  rw [centredDiff_apply, hTp, hTm]
  field_simp
  ring

/-- **The centred difference error** ([quarteroni2000numerical] (10.62)): for `f` of class `C³`
on `[x - h, x + h]`, `f'(x) - (f (x + h) - f (x - h))/(2h) = -(h²/6) f'''(ξ)` for some
`ξ ∈ (x - h, x + h)`. The two remainders of `deriv_sub_centredDiff_eq_two_points` are averaged
by the intermediate value theorem. -/
theorem deriv_sub_centredDiff_eq (hh : 0 < h) (hf : ContDiffOn ℝ 3 f (Icc (x - h) (x + h))) :
    ∃ ξ ∈ Ioo (x - h) (x + h),
      deriv f x - centredDiff f h x = -(h ^ 2 / 6) * iteratedDeriv 3 f ξ := by
  obtain ⟨ξ, hξ, η, hη, hT⟩ := deriv_sub_centredDiff_eq_two_points hh hf
  obtain ⟨ζ, hζ, hgζ⟩ := exists_eq_add_div_two (continuousOn_iteratedDeriv_Ioo hh hf)
    (Ioo_subset_Ioo le_rfl (by linarith) hξ) (Ioo_subset_Ioo (by linarith) le_rfl hη)
  refine ⟨ζ, hζ, ?_⟩
  rw [hT, hgζ]
  ring

/-- **The second centred difference error in two-point form**: for `f` of class `C⁴` on
`[x - h, x + h]`, `f''(x) - (f (x + h) - 2 f x + f (x - h))/h² = -(h²/24)(f⁗(ξ) + f⁗(η))` with
`ξ ∈ (x - h, x)` and `η ∈ (x, x + h)`, the two Lagrange remainders of the third-order Taylor
expansions at `x` (the odd terms cancel). -/
theorem iteratedDeriv_two_sub_secondCentredDiff_eq_two_points (hh : 0 < h)
    (hf : ContDiffOn ℝ 4 f (Icc (x - h) (x + h))) :
    ∃ ξ ∈ Ioo (x - h) x, ∃ η ∈ Ioo x (x + h),
      iteratedDeriv 2 f x - secondCentredDiff f h x
        = -(h ^ 2 / 24) * (iteratedDeriv 4 f ξ + iteratedDeriv 4 f η) := by
  have hx : ContDiffAt ℝ 4 f x := contDiffAt_of_mem_Ioo hf ⟨by linarith, by linarith⟩
  have hnep : x ≠ x + h := by linarith
  have hnem : x ≠ x - h := by linarith
  have hfp : ContDiffOn ℝ (3 + 1) f (uIcc x (x + h)) :=
    hf.mono (by rw [Set.uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) le_rfl)
  have hfm : ContDiffOn ℝ (3 + 1) f (uIcc x (x - h)) :=
    hf.mono (by rw [Set.uIcc_of_ge (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith))
  obtain ⟨η, hη, hTp⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul hnep hfp
  obtain ⟨ξ, hξ, hTm⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul hnem hfm
  rw [uIoo_of_le (by linarith)] at hη
  rw [uIoo_of_ge (by linarith)] at hξ
  rw [taylorWithinEval_eq_sum_of_contDiffAt hnep (hx.of_le (by norm_num))] at hTp
  rw [taylorWithinEval_eq_sum_of_contDiffAt hnem (hx.of_le (by norm_num))] at hTm
  simp only [sum_range_succ, sum_range_zero, Nat.factorial, iteratedDeriv_zero, iteratedDeriv_one,
    add_sub_cancel_left, sub_sub_cancel_left] at hTp hTm
  refine ⟨ξ, hξ, η, hη, ?_⟩
  rw [secondCentredDiff_apply, hTp, hTm]
  field_simp
  ring

/-- **The second centred difference error** ([quarteroni2000numerical] (10.66), in the book's
form): for `f` of class `C⁴` on `[x - h, x + h]`,
`f''(x) - (f (x + h) - 2 f x + f (x - h))/h² = -(h²/24)(f⁗(x + θ h) + f⁗(x - ω h))` for some
`θ, ω ∈ (0, 1)`. -/
theorem iteratedDeriv_two_sub_secondCentredDiff_eq (hh : 0 < h)
    (hf : ContDiffOn ℝ 4 f (Icc (x - h) (x + h))) :
    ∃ θ ∈ Ioo (0 : ℝ) 1, ∃ ω ∈ Ioo (0 : ℝ) 1,
      iteratedDeriv 2 f x - secondCentredDiff f h x =
        -(h ^ 2 / 24) * (iteratedDeriv 4 f (x + θ * h) + iteratedDeriv 4 f (x - ω * h)) := by
  obtain ⟨ξ, hξ, η, hη, hT⟩ := iteratedDeriv_two_sub_secondCentredDiff_eq_two_points hh hf
  refine ⟨(η - x) / h, ⟨by have := hη.1; positivity, ?_⟩, (x - ξ) / h,
    ⟨by have := hξ.2; positivity, ?_⟩, ?_⟩
  · rw [div_lt_one hh]; linarith [hη.2]
  · rw [div_lt_one hh]; linarith [hξ.1]
  · rw [hT, div_mul_cancel₀ _ hh.ne', div_mul_cancel₀ _ hh.ne', add_sub_cancel, sub_sub_cancel,
      add_comm]

/-- **The second centred difference error in one-point form**: for `f` of class `C⁴` on
`[x - h, x + h]`, `f''(x) - (f (x + h) - 2 f x + f (x - h))/h² = -(h²/12) f⁗(ξ)` for some
`ξ ∈ (x - h, x + h)`, by the intermediate value theorem applied to
`iteratedDeriv_two_sub_secondCentredDiff_eq_two_points`. -/
theorem iteratedDeriv_two_sub_secondCentredDiff_eq_one_point (hh : 0 < h)
    (hf : ContDiffOn ℝ 4 f (Icc (x - h) (x + h))) :
    ∃ ξ ∈ Ioo (x - h) (x + h),
      iteratedDeriv 2 f x - secondCentredDiff f h x = -(h ^ 2 / 12) * iteratedDeriv 4 f ξ := by
  obtain ⟨ξ, hξ, η, hη, hT⟩ := iteratedDeriv_two_sub_secondCentredDiff_eq_two_points hh hf
  obtain ⟨ζ, hζ, hgζ⟩ := exists_eq_add_div_two (continuousOn_iteratedDeriv_Ioo hh hf)
    (Ioo_subset_Ioo le_rfl (by linarith) hξ) (Ioo_subset_Ioo (by linarith) le_rfl hη)
  refine ⟨ζ, hζ, ?_⟩
  rw [hT, hgζ]
  ring

end Quotients

/-! ### Compact schemes -/

section Compact

variable {α β γ : ℝ} {f : ℝ → ℝ} {x : ℝ}

/-- **The consistency error of the compact scheme** with parameters `α, β, γ` at `x` with step
`h` ([quarteroni2000numerical] (10.67)–(10.68)): the residual
`α f'(x - h) + f'(x) + α f'(x + h) - ((β/2h)(f(x + h) - f(x - h)) + (γ/4h)(f(x + 2h) - f(x - 2h)))`
obtained by forcing `f` to satisfy the scheme. -/
noncomputable def compactError (α β γ : ℝ) (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  α * deriv f (x - h) + deriv f x + α * deriv f (x + h)
    - (β / (2 * h) * (f (x + h) - f (x - h)) + γ / (4 * h) * (f (x + 2 * h) - f (x - 2 * h)))

/-- The compact scheme with `α = γ = 0`, `β = 1` is the centred difference: its consistency error
is the centred difference error. -/
theorem compactError_zero_one_zero (h : ℝ) :
    compactError 0 1 0 f x h = deriv f x - centredDiff f h x := by
  simp only [compactError, centredDiff, zero_mul, zero_add, add_zero, zero_div]
  ring

/-- **The Taylor expansion of the consistency error** of the compact scheme
([quarteroni2000numerical] §10.10.2, with the printed spurious factor `1/2` on the `h²` terms
removed): for `f` of class `C⁷` at `x`,
`σ(h) = (2α + 1 - β - γ) f'(x) + h² (α - β/6 - 2γ/3) f'''(x) + h⁴ (α/12 - β/120 - 2γ/15) f⁽⁵⁾(x)
+ O(h⁶)` as `h → 0`, `h ≠ 0`. The even powers of `h` cancel in the antisymmetric differences and
the odd ones in the symmetric sum of `f'`. -/
theorem compactError_expansion (hf : ContDiffAt ℝ 7 f x) :
    (fun h => compactError α β γ f x h
        - ((2 * α + 1 - β - γ) * deriv f x
          + h ^ 2 * (α - β / 6 - 2 * γ / 3) * iteratedDeriv 3 f x
          + h ^ 4 * (α / 12 - β / 120 - 2 * γ / 15) * iteratedDeriv 5 f x))
      =O[𝓝[≠] 0] fun h => h ^ 6 := by
  -- a ball on which `f` is `C⁷`, and a bound on the seventh derivative on half of it
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
  have hf7 : ContDiffOn ℝ (6 + 1) f (Metric.ball x ε) := hfu.mono hball
  have hcont : ContinuousOn (iteratedDeriv 7 f) (Metric.ball x ε) :=
    ((hf7.continuousOn_iteratedDerivWithin le_rfl Metric.isOpen_ball.uniqueDiffOn).congr
      (iteratedDerivWithin_of_isOpen Metric.isOpen_ball).symm)
  obtain ⟨M, hM⟩ := (isCompact_closedBall x (ε / 2)).exists_bound_of_continuousOn
    (hcont.mono (Metric.closedBall_subset_ball (by linarith)))
  have hM' : ∀ t ∈ Metric.ball x (ε / 2), |iteratedDeriv (6 + 1) f t| ≤ M := fun t ht =>
    hM t (Metric.ball_subset_closedBall ht)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x (Metric.mem_closedBall_self (by positivity)))
  have hf7' : ContDiffOn ℝ (6 + 1) f (Metric.ball x (ε / 2)) :=
    hf7.mono (Metric.ball_subset_ball (by linarith))
  -- the derivative is `C⁶` on the ball, with the same seventh derivative
  have hf6 : ContDiffOn ℝ (5 + 1) (deriv f) (Metric.ball x (ε / 2)) :=
    ((contDiffOn_succ_iff_deriv_of_isOpen Metric.isOpen_ball).1 hf7').2.2
  have hM6 : ∀ t ∈ Metric.ball x (ε / 2), |iteratedDeriv (5 + 1) (deriv f) t| ≤ M := fun t ht => by
    rw [← iteratedDeriv_succ']; exact hM' t ht
  -- the remainders
  set P : ℝ → ℝ := fun t => ∑ k ∈ range (6 + 1), t ^ k / k ! * iteratedDeriv k f x with hP
  set Q : ℝ → ℝ := fun t => ∑ k ∈ range (5 + 1), t ^ k / k ! * iteratedDeriv (k + 1) f x with hQ
  have hR : ∀ t, |t| < ε / 2 → |f (x + t) - P t| ≤ M * |t| ^ 7 / 5040 := fun t ht => by
    have := abs_sub_sum_taylor_le hf7' hM' (y := x + t)
      (by rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left]; exact ht)
    rwa [add_sub_cancel_left] at this
  have hS : ∀ t, |t| < ε / 2 → |deriv f (x + t) - Q t| ≤ M * |t| ^ 6 / 720 := fun t ht => by
    have := abs_sub_sum_taylor_le hf6 hM6 (y := x + t)
      (by rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left]; exact ht)
    simp only [add_sub_cancel_left, ← iteratedDeriv_succ'] at this
    exact this
  -- the algebraic identity behind the expansion
  have hkey : ∀ h : ℝ, h ≠ 0 → compactError α β γ f x h
      - ((2 * α + 1 - β - γ) * deriv f x
          + h ^ 2 * (α - β / 6 - 2 * γ / 3) * iteratedDeriv 3 f x
          + h ^ 4 * (α / 12 - β / 120 - 2 * γ / 15) * iteratedDeriv 5 f x)
      = α * (deriv f (x + -h) - Q (-h)) + α * (deriv f (x + h) - Q h)
        - β / (2 * h) * ((f (x + h) - P h) - (f (x + -h) - P (-h)))
        - γ / (4 * h) * ((f (x + 2 * h) - P (2 * h)) - (f (x + -(2 * h)) - P (-(2 * h)))) := by
    intro h hh
    simp only [hP, hQ, sum_range_succ, sum_range_zero, Nat.factorial, iteratedDeriv_zero,
      iteratedDeriv_one, zero_add, compactError, ← sub_eq_add_neg]
    field_simp
    ring
  -- the bound
  refine IsBigO.of_bound (M * (|α| / 360 + |β| / 5040 + |γ| * 64 / 5040)) ?_
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨ε / 4, by positivity, fun h hh hh0 => ?_⟩
  rw [Real.dist_eq, sub_zero] at hh
  have hh0' : h ≠ 0 := hh0
  have hpos : 0 < |h| := abs_pos.2 hh0'
  have h1 := hS h (by linarith)
  have h2 := hS (-h) (by rw [abs_neg]; linarith)
  rw [abs_neg] at h2
  have h3 := hR h (by linarith)
  have h4 := hR (-h) (by rw [abs_neg]; linarith)
  rw [abs_neg] at h4
  have h5 := hR (2 * h) (by rw [abs_mul, abs_two]; linarith)
  rw [abs_mul, abs_two] at h5
  have h6 := hR (-(2 * h)) (by rw [abs_neg, abs_mul, abs_two]; linarith)
  rw [abs_neg, abs_mul, abs_two] at h6
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hkey h hh0', abs_pow]
  have e1 : |α * (deriv f (x + -h) - Q (-h)) + α * (deriv f (x + h) - Q h)|
      ≤ |α| * (M * |h| ^ 6 / 720) + |α| * (M * |h| ^ 6 / 720) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have e2 : |β / (2 * h) * ((f (x + h) - P h) - (f (x + -h) - P (-h)))|
      ≤ |β| / (2 * |h|) * (M * |h| ^ 7 / 5040 + M * |h| ^ 7 / 5040) := by
    rw [abs_mul, abs_div, abs_mul, abs_two]
    gcongr
    exact (abs_sub _ _).trans (add_le_add h3 h4)
  have e3 : |γ / (4 * h) * ((f (x + 2 * h) - P (2 * h)) - (f (x + -(2 * h)) - P (-(2 * h))))|
      ≤ |γ| / (4 * |h|) * (M * (2 * |h|) ^ 7 / 5040 + M * (2 * |h|) ^ 7 / 5040) := by
    rw [abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    gcongr
    exact (abs_sub _ _).trans (add_le_add h5 h6)
  have e2' : |β| / (2 * |h|) * (M * |h| ^ 7 / 5040 + M * |h| ^ 7 / 5040)
      = |β| * M * |h| ^ 6 / 5040 := by field_simp; ring
  have e3' : |γ| / (4 * |h|) * (M * (2 * |h|) ^ 7 / 5040 + M * (2 * |h|) ^ 7 / 5040)
      = |γ| * 64 * M * |h| ^ 6 / 5040 := by field_simp; ring
  calc |α * (deriv f (x + -h) - Q (-h)) + α * (deriv f (x + h) - Q h)
        - β / (2 * h) * ((f (x + h) - P h) - (f (x + -h) - P (-h)))
        - γ / (4 * h) * ((f (x + 2 * h) - P (2 * h)) - (f (x + -(2 * h)) - P (-(2 * h))))|
      ≤ |α * (deriv f (x + -h) - Q (-h)) + α * (deriv f (x + h) - Q h)|
        + |β / (2 * h) * ((f (x + h) - P h) - (f (x + -h) - P (-h)))|
        + |γ / (4 * h) * ((f (x + 2 * h) - P (2 * h)) - (f (x + -(2 * h)) - P (-(2 * h))))| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (|α| * (M * |h| ^ 6 / 720) + |α| * (M * |h| ^ 6 / 720))
        + |β| * M * |h| ^ 6 / 5040 + |γ| * 64 * M * |h| ^ 6 / 5040 := by
        rw [← e2', ← e3']; exact add_le_add (add_le_add e1 e2) e3
    _ = M * (|α| / 360 + |β| / 5040 + |γ| * 64 / 5040) * |h| ^ 6 := by ring

/-- `h ^ n = O(h ^ m)` as `h → 0` for `m ≤ n`. -/
private theorem isBigO_pow_pow_nhdsWithin {m n : ℕ} (hmn : m ≤ n) :
    (fun h : ℝ => h ^ n) =O[𝓝[≠] 0] fun h => h ^ m := by
  rcases hmn.lt_or_eq with hlt | rfl
  · exact (isLittleO_pow_pow hlt).isBigO.mono nhdsWithin_le_nhds
  · exact isBigO_refl _ _

/-- **Second-order compact schemes** ([quarteroni2000numerical] §10.10.2): if `2α + 1 = β + γ`
then the consistency error is `O(h²)` for `f` of class `C⁷` at `x`. -/
theorem compactError_isBigO_pow_two (h₁ : 2 * α + 1 = β + γ) (hf : ContDiffAt ℝ 7 f x) :
    (fun h => compactError α β γ f x h) =O[𝓝[≠] 0] fun h => h ^ 2 := by
  have e1 : 2 * α + 1 - β - γ = 0 := by linarith
  have hexp := (compactError_expansion (α := α) (β := β) (γ := γ) hf).trans
    (isBigO_pow_pow_nhdsWithin (by norm_num : 2 ≤ 6))
  have hmain : (fun h : ℝ => (α - β / 6 - 2 * γ / 3) * iteratedDeriv 3 f x * h ^ 2
      + (α / 12 - β / 120 - 2 * γ / 15) * iteratedDeriv 5 f x * h ^ 4)
      =O[𝓝[≠] 0] fun h => h ^ 2 :=
    ((isBigO_refl (fun h : ℝ => h ^ 2) _).const_mul_left _).add
      (((isBigO_pow_pow_nhdsWithin (by norm_num : 2 ≤ 4)).const_mul_left _))
  refine (hexp.add hmain).congr_left fun h => ?_
  rw [e1]
  ring

/-- **Fourth-order compact schemes** ([quarteroni2000numerical] §10.10.2): if `2α + 1 = β + γ`
and `6α = β + 4γ` then the consistency error is `O(h⁴)` for `f` of class `C⁷` at `x`. -/
theorem compactError_isBigO_pow_four (h₁ : 2 * α + 1 = β + γ) (h₂ : 6 * α = β + 4 * γ)
    (hf : ContDiffAt ℝ 7 f x) :
    (fun h => compactError α β γ f x h) =O[𝓝[≠] 0] fun h => h ^ 4 := by
  have e1 : 2 * α + 1 - β - γ = 0 := by linarith
  have e2 : α - β / 6 - 2 * γ / 3 = 0 := by linarith
  have hexp := (compactError_expansion (α := α) (β := β) (γ := γ) hf).trans
    (isBigO_pow_pow_nhdsWithin (by norm_num : 4 ≤ 6))
  have hmain : (fun h : ℝ => (α / 12 - β / 120 - 2 * γ / 15) * iteratedDeriv 5 f x * h ^ 4)
      =O[𝓝[≠] 0] fun h => h ^ 4 :=
    (isBigO_refl (fun h : ℝ => h ^ 4) _).const_mul_left _
  refine (hexp.add hmain).congr_left fun h => ?_
  rw [e1, e2]
  ring

/-- **Sixth-order compact schemes** ([quarteroni2000numerical] §10.10.2): if `2α + 1 = β + γ`,
`6α = β + 4γ` and `10α = β + 16γ` then the consistency error is `O(h⁶)` for `f` of class `C⁷` at
`x`. -/
theorem compactError_isBigO_pow_six (h₁ : 2 * α + 1 = β + γ) (h₂ : 6 * α = β + 4 * γ)
    (h₃ : 10 * α = β + 16 * γ) (hf : ContDiffAt ℝ 7 f x) :
    (fun h => compactError α β γ f x h) =O[𝓝[≠] 0] fun h => h ^ 6 := by
  have e1 : 2 * α + 1 - β - γ = 0 := by linarith
  have e2 : α - β / 6 - 2 * γ / 3 = 0 := by linarith
  have e3 : α / 12 - β / 120 - 2 * γ / 15 = 0 := by linarith
  refine (compactError_expansion (α := α) (β := β) (γ := γ) hf).congr_left fun h => ?_
  rw [e1, e2, e3]
  ring

/-- **The unique sixth-order compact scheme** ([quarteroni2000numerical] (10.69)): the three
order conditions have the unique solution `α = 1/3`, `β = 14/9`, `γ = 1/9`. -/
theorem order_six_unique (h₁ : 2 * α + 1 = β + γ) (h₂ : 6 * α = β + 4 * γ)
    (h₃ : 10 * α = β + 16 * γ) : α = 1 / 3 ∧ β = 14 / 9 ∧ γ = 1 / 9 := by
  refine ⟨?_, ?_, ?_⟩ <;> linarith

end Compact

end FiniteDifference

/-! ### The differentiation matrix of Lagrange interpolation -/

namespace Lagrange

section DerivMatrix

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The differentiation matrix** of a family of nodes `v : ι → F`: `D i j = ℓ_j'(v i)`, the
derivative of the `j`-th Lagrange basis polynomial at the `i`-th node
([quarteroni2000numerical] §10.10.3, the pseudo-spectral differentiation matrix when the nodes are
the Chebyshev–Gauss–Lobatto points). -/
noncomputable def derivMatrix (v : ι → F) : Matrix ι ι F :=
  Matrix.of fun i j => (derivative (Lagrange.basis Finset.univ v j)).eval (v i)

/-- The entries of the differentiation matrix. -/
theorem derivMatrix_apply (v : ι → F) (i j : ι) :
    derivMatrix v i j = (derivative (Lagrange.basis Finset.univ v j)).eval (v i) := rfl

/-- **The derivative of the interpolant at the nodes is the differentiation matrix applied to the
nodal values** ([quarteroni2000numerical] (10.72)): for the interpolant of the values `r` at the
nodes `v`, `(interpolate v r)'(v i) = (derivMatrix v *ᵥ r) i`. With `r = f ∘ v` this is the
pseudo-spectral derivative of `f` at the nodes. No injectivity of the nodes is needed: the identity
is linearity of `derivative` and `eval` over the Lagrange basis. -/
theorem eval_derivative_interpolate_node (v : ι → F) (r : ι → F) (i : ι) :
    (derivative (interpolate Finset.univ v r)).eval (v i) = (derivMatrix v *ᵥ r) i := by
  simp only [interpolate_apply, derivative_sum, derivative_C_mul, eval_finsetSum, eval_mul, eval_C,
    Matrix.mulVec, dotProduct, derivMatrix_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end DerivMatrix

/-! #### Derivatives of the Lagrange basis at the nodes -/

section BasisDerivative

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → F} {i j : ι}

/-- `(X - x_i) ℓ_i = ω / ω'(x_i)`: the Lagrange basis polynomial times its missing factor is the
nodal polynomial divided by the nodal weight's inverse. -/
theorem X_sub_C_mul_basis (hi : i ∈ s) :
    (X - C (v i)) * Lagrange.basis s v i = C (nodalWeight s v i) * nodal s v := by
  rw [basis_eq_prod_sub_inv_mul_nodal_div hi, ← nodal_erase_eq_nodal_div hi,
    nodal_eq_mul_nodal_erase hi]
  ring

omit [DecidableEq ι] in
/-- The derivative of the nodal polynomial does not vanish at a node (the nodes being distinct).
-/
theorem eval_derivative_nodal_ne_zero (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (derivative (nodal s v)).eval (v i) ≠ 0 := by
  classical
  have := nodalWeight_ne_zero hvs hi
  rw [nodalWeight_eq_eval_derivative_nodal hi] at this
  exact fun h => this (by rw [h, _root_.inv_zero])

/-- **The derivative of a Lagrange basis polynomial at another node**:
`ℓ_i'(x_j) = ω'(x_j) / ((x_j - x_i) ω'(x_i))` for `i ≠ j`, from differentiating
`(X - x_i) ℓ_i = ω / ω'(x_i)` and evaluating at `x_j`, where `ℓ_i` vanishes. -/
theorem eval_derivative_basis_of_ne (hvs : Set.InjOn v s) (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) :
    (derivative (Lagrange.basis s v i)).eval (v j)
      = (derivative (nodal s v)).eval (v j)
        / ((v j - v i) * (derivative (nodal s v)).eval (v i)) := by
  have h := congr_arg (fun q => (derivative q).eval (v j)) (X_sub_C_mul_basis (v := v) hi)
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, zero_mul, zero_add] at h
  have hne : v j - v i ≠ 0 := sub_ne_zero.2 fun h => hij (hvs hi hj h.symm)
  have hω := eval_derivative_nodal_ne_zero hvs hi
  rw [eval_basis_of_ne hij hj, zero_add, nodalWeight_eq_eval_derivative_nodal hi, inv_mul_eq_div,
    eq_div_iff hω] at h
  field_simp
  linear_combination h

/-- **The derivative of a Lagrange basis polynomial at its own node**, in the form valid in every
characteristic: `2 ℓ_i'(x_i) ω'(x_i) = ω''(x_i)`, from differentiating `(X - x_i) ℓ_i = ω / ω'(x_i)`
twice and evaluating at `x_i`. -/
theorem two_mul_eval_derivative_basis_self_mul (hvs : Set.InjOn v s) (hi : i ∈ s) :
    2 * (derivative (Lagrange.basis s v i)).eval (v i) * (derivative (nodal s v)).eval (v i)
      = (derivative (derivative (nodal s v))).eval (v i) := by
  have h := congr_arg (fun q => (derivative (derivative q)).eval (v i))
    (X_sub_C_mul_basis (v := v) hi)
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    derivative_add, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self,
    zero_mul, add_zero, zero_add] at h
  have hω := eval_derivative_nodal_ne_zero hvs hi
  rw [nodalWeight_eq_eval_derivative_nodal hi, inv_mul_eq_div, eq_div_iff hω] at h
  linear_combination h

/-- **The derivative of a Lagrange basis polynomial at its own node**:
`ℓ_i'(x_i) = ω''(x_i) / (2 ω'(x_i))`. -/
theorem eval_derivative_basis_self_of_injOn [NeZero (2 : F)] (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (derivative (Lagrange.basis s v i)).eval (v i)
      = (derivative (derivative (nodal s v))).eval (v i)
        / (2 * (derivative (nodal s v)).eval (v i)) := by
  have hω := eval_derivative_nodal_ne_zero hvs hi
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  rw [eq_div_iff (mul_ne_zero h2 hω), ← two_mul_eval_derivative_basis_self_mul hvs hi]
  ring

/-- `eval_derivative_basis_of_ne` with the nodal polynomial replaced by any nonzero multiple
`p = c ω` of it: the formula `ℓ_i'(x_j) = p'(x_j) / ((x_j - x_i) p'(x_i))` is scale invariant. -/
theorem eval_derivative_basis_of_ne_of_eq_C_mul_nodal (hvs : Set.InjOn v s) (hi : i ∈ s)
    (hj : j ∈ s) (hij : i ≠ j) {p : F[X]} {c : F} (hc : c ≠ 0) (hp : p = C c * nodal s v) :
    (derivative (Lagrange.basis s v i)).eval (v j)
      = (derivative p).eval (v j) / ((v j - v i) * (derivative p).eval (v i)) := by
  rw [eval_derivative_basis_of_ne hvs hi hj hij, hp, derivative_C_mul, eval_mul, eval_C, eval_mul,
    eval_C, mul_left_comm (v j - v i), mul_div_mul_left _ _ hc]

/-- `eval_derivative_basis_self_of_injOn` with the nodal polynomial replaced by any nonzero
multiple `p = c ω` of it: `ℓ_i'(x_i) = p''(x_i) / (2 p'(x_i))`. -/
theorem eval_derivative_basis_self_of_eq_C_mul_nodal [NeZero (2 : F)] (hvs : Set.InjOn v s)
    (hi : i ∈ s) {p : F[X]} {c : F} (hc : c ≠ 0) (hp : p = C c * nodal s v) :
    (derivative (Lagrange.basis s v i)).eval (v i)
      = (derivative (derivative p)).eval (v i) / (2 * (derivative p).eval (v i)) := by
  rw [eval_derivative_basis_self_of_injOn hvs hi, hp, derivative_C_mul, derivative_C_mul, eval_mul,
    eval_C, eval_mul, eval_C, mul_left_comm (2 : F), mul_div_mul_left _ _ hc]

/-- The Lagrange basis at the reflected nodes `-v` is the reflection of the Lagrange basis:
`ℓ̄_i(t) = ℓ_i(-t)`. -/
theorem basis_neg (s : Finset ι) (v : ι → F) (i : ι) :
    Lagrange.basis s (-v) i = (Lagrange.basis s v i).comp (-X) := by
  simp only [Lagrange.basis, Pi.neg_apply]
  rw [Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [basisDivisor, mul_comp, C_comp, sub_comp, X_comp]
  rw [neg_sub_neg, ← neg_sub (v i), inv_neg, C_neg, C_neg]
  ring

/-- **Reflecting the nodes changes the sign of the differentiation matrix**:
`derivMatrix (-v) = -derivMatrix v`, because `ℓ̄_j(t) = ℓ_j(-t)` has derivative `-ℓ_j'(-t)`. This is
how a formula at the Chebyshev–Gauss–Lobatto nodes `cos (jπ/n)` transfers to the reversed nodes
`-cos (jπ/n)` of [quarteroni2000numerical] §10.3. -/
theorem derivMatrix_neg [Fintype ι] (v : ι → F) : derivMatrix (-v) = -derivMatrix v := by
  ext i j
  rw [Matrix.neg_apply, derivMatrix_apply, derivMatrix_apply, basis_neg, derivative_comp,
    derivative_neg, derivative_X, eval_mul, eval_neg, eval_one, eval_comp, eval_neg, eval_X,
    Pi.neg_apply, neg_neg, neg_one_mul]

end BasisDerivative

end Lagrange

/-! ### The Chebyshev–Gauss–Lobatto differentiation matrix -/

namespace Polynomial.Chebyshev

open Real

variable {n : ℕ}

/-- The Chebyshev–Gauss–Lobatto nodes `cos (jπ/n)`, `j = 0, …, n`, are distinct. -/
theorem node_injective : Function.Injective fun j : Fin (n + 1) => node n j := by
  intro j k h
  exact Fin.ext ((strictAntiOn_node n).injOn (Finset.mem_coe.2 (Finset.mem_range.2 j.isLt))
    (Finset.mem_coe.2 (Finset.mem_range.2 k.isLt)) h)

/-- `T_n'` vanishes at the interior Chebyshev–Gauss–Lobatto nodes, the extrema of `T_n`. -/
theorem eval_derivative_T_node_of_pos_of_lt {j : ℕ} (hj0 : 0 < j) (hjn : j < n) :
    (derivative (T ℝ n)).eval (node n j) = 0 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hθ : 0 < (j : ℝ) * π / n ∧ (j : ℝ) * π / n < π := by
    constructor
    · positivity
    · rw [div_lt_iff₀ (by positivity)]
      have : (j : ℝ) < n := by exact_mod_cast hjn
      nlinarith [pi_pos]
  have hsin : sin ((j : ℝ) * π / n) ≠ 0 := (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hU := U_real_cos ((j : ℝ) * π / n) ((n : ℤ) - 1)
  have hval : ((((n : ℤ) - 1 : ℤ) : ℝ) + 1) * ((j : ℝ) * π / n) = (j : ℝ) * π := by
    push_cast; field_simp; ring
  rw [hval, sin_nat_mul_pi] at hU
  rw [T_derivative_eq_U, node, eval_mul, eval_intCast, (mul_eq_zero.1 hU).resolve_right hsin,
    mul_zero]

/-- `T_n'(1) = n²`, for a natural `n`. -/
theorem derivative_T_natCast_eval_one : (derivative (T ℝ n)).eval 1 = (n : ℝ) ^ 2 := by
  have := derivative_T_eval_one (R := ℝ) (n : ℤ)
  exact_mod_cast this

/-- `T_n(-1) = (-1)^n`, for a natural `n`. -/
theorem T_natCast_eval_neg_one : (T ℝ n).eval (-1) = (-1) ^ n := by
  rw [T_eval_neg_one, Int.cast_negOnePow_natCast]

/-- `T_n'(-1) = -(-1)^n n²`, from the Chebyshev differential equation at `x = -1`. -/
theorem derivative_T_natCast_eval_neg_one :
    (derivative (T ℝ n)).eval (-1) = -(n : ℝ) ^ 2 * (-1) ^ n := by
  have h := one_sub_X_sq_mul_iterate_derivative_T_eval (R := ℝ) (n : ℤ) 0 (-1)
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
    Nat.cast_zero, zero_pow two_ne_zero, sub_zero] at h
  rw [T_natCast_eval_neg_one] at h
  push_cast at h
  linear_combination h

/-- The differentiated Chebyshev equation at `x = ±1`: `3 x T_n''(x) = (n² - 1) T_n'(x)`. -/
theorem three_mul_eval_derivative_derivative_T_of_sq_eq_one {x : ℝ} (hx : x ^ 2 = 1) :
    3 * x * (derivative (derivative (T ℝ n))).eval x
      = ((n : ℝ) ^ 2 - 1) * (derivative (T ℝ n)).eval x := by
  have h := one_sub_X_sq_mul_iterate_derivative_T_eval (R := ℝ) (n : ℤ) 1 x
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id] at h
  rw [hx, sub_self, zero_mul] at h
  push_cast at h
  linear_combination -h

/-- The Chebyshev differential equation at a point: `(1 - x²) T_n''(x) = x T_n'(x) - n² T_n(x)`.
-/
theorem one_sub_sq_mul_eval_derivative_derivative_T (x : ℝ) :
    (1 - x ^ 2) * (derivative (derivative (T ℝ n))).eval x
      = x * (derivative (T ℝ n)).eval x - (n : ℝ) ^ 2 * (T ℝ n).eval x := by
  have h := one_sub_X_sq_mul_iterate_derivative_T_eval (R := ℝ) (n : ℤ) 0 x
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
    Nat.cast_zero, zero_pow two_ne_zero, sub_zero] at h
  push_cast at h
  linear_combination h

/-- The polynomial `(X² - 1) T_n'`, which vanishes exactly at the Chebyshev–Gauss–Lobatto nodes and
is therefore a constant multiple of their nodal polynomial (`lobattoNodalT_eq_C_mul_nodal`). -/
noncomputable def lobattoNodalT (n : ℕ) : ℝ[X] := (X ^ 2 - 1) * derivative (T ℝ n)

/-- `((X² - 1) T_n')' = X T_n' + n² T_n`, by the Chebyshev differential equation. -/
theorem derivative_lobattoNodalT :
    derivative (lobattoNodalT n) = X * derivative (T ℝ n) + (n : ℝ[X]) ^ 2 * T ℝ n := by
  have h := one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := ℝ) (n : ℤ)
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply] at h
  simp only [lobattoNodalT, derivative_mul, derivative_sub, derivative_X_sq, derivative_one,
    sub_zero, C_ofNat]
  push_cast at h ⊢
  linear_combination (norm := ring_nf) -h

/-- `((X² - 1) T_n')'' = (n² + 1) T_n' + X T_n''`. -/
theorem derivative_derivative_lobattoNodalT :
    derivative (derivative (lobattoNodalT n))
      = ((n : ℝ[X]) ^ 2 + 1) * derivative (T ℝ n) + X * derivative (derivative (T ℝ n)) := by
  rw [derivative_lobattoNodalT]
  simp only [derivative_add, derivative_mul, derivative_X, one_mul, derivative_pow,
    derivative_natCast, mul_zero, zero_mul, zero_add]
  ring

/-- `(X² - 1) T_n'` vanishes at every Chebyshev–Gauss–Lobatto node. -/
theorem eval_lobattoNodalT_node {j : ℕ} (hj : j ≤ n) : (lobattoNodalT n).eval (node n j) = 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [lobattoNodalT, node_eq_one]
  rcases eq_or_ne j n with rfl | hjn
  · rw [node_eq_neg_one (by omega)]
    simp [lobattoNodalT]
  · simp [lobattoNodalT, eval_derivative_T_node_of_pos_of_lt hj0 (lt_of_le_of_ne hj hjn)]

/-- `(X² - 1) T_n' ≠ 0` for `n ≥ 1`: its derivative at `1` is `2n²`. -/
theorem lobattoNodalT_ne_zero (hn : n ≠ 0) : lobattoNodalT n ≠ 0 := by
  intro h
  have h1 := congr_arg (fun p => (derivative p).eval 1) h
  simp only [derivative_lobattoNodalT, derivative_zero, eval_zero, eval_add, eval_mul, eval_X,
    eval_pow, eval_natCast, derivative_T_natCast_eval_one, T_eval_one, one_mul, mul_one] at h1
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have : (n : ℝ) ^ 2 + (n : ℝ) ^ 2 ≠ 0 := by positivity
  exact this h1

/-- `(X² - 1) T_n'` has degree at most `n + 1`. -/
theorem natDegree_lobattoNodalT_le (hn : n ≠ 0) : (lobattoNodalT n).natDegree ≤ n + 1 := by
  refine natDegree_mul_le.trans ?_
  have h1 : (X ^ 2 - 1 : ℝ[X]).natDegree ≤ 2 := by
    rw [show (X ^ 2 - 1 : ℝ[X]) = X ^ 2 - Polynomial.C 1 by simp, natDegree_X_pow_sub_C]
  have h2 : (derivative (T ℝ n)).natDegree ≤ n - 1 := by
    refine (natDegree_derivative_le _).trans ?_
    rw [natDegree_T]
    simp
  omega

/-- **The nodal polynomial of the Chebyshev–Gauss–Lobatto nodes** is a nonzero constant multiple
of `(X² - 1) T_n'`: the latter has degree at most `n + 1` and vanishes at the `n + 1` distinct
nodes. -/
theorem lobattoNodalT_eq_C_mul_nodal (hn : n ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧ lobattoNodalT n
      = Polynomial.C c * Lagrange.nodal Finset.univ (fun j : Fin (n + 1) => node n j) := by
  have hdvd : Lagrange.nodal Finset.univ (fun j : Fin (n + 1) => node n j) ∣ lobattoNodalT n := by
    rw [Lagrange.nodal_eq]
    refine Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C node_injective).set_pairwise _)
      fun j _ => ?_
    rw [dvd_iff_isRoot]
    exact eval_lobattoNodalT_node (Nat.lt_succ_iff.1 j.isLt)
  obtain ⟨q, hq⟩ := hdvd
  have hp0 := lobattoNodalT_ne_zero hn
  have hq0 : q ≠ 0 := fun h => hp0 (by rw [hq, h, mul_zero])
  have hdeg : q.natDegree = 0 := by
    have h1 := natDegree_lobattoNodalT_le hn
    rw [hq, Lagrange.nodal_monic.natDegree_mul' hq0, Lagrange.natDegree_nodal, Finset.card_univ,
      Fintype.card_fin] at h1
    omega
  have hqC : q = Polynomial.C (q.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
  refine ⟨q.coeff 0, fun h => hq0 (by rw [hqC, h, C_0]), ?_⟩
  rw [hq, mul_comm]
  congr 1

/-- `((X² - 1) T_n')'(x_l) = d_l n² (-1)^l` at the node `x_l = cos (lπ/n)`, with
`d_l = lobattoFactor n l` (`2` at the endpoints, `1` inside). -/
theorem eval_derivative_lobattoNodalT_node {l : ℕ} (hl : l ≤ n) :
    (derivative (lobattoNodalT n)).eval (node n l)
      = lobattoFactor n l * (n : ℝ) ^ 2 * (-1) ^ l := by
  rw [derivative_lobattoNodalT]
  simp only [eval_add, eval_mul, eval_X, eval_pow, eval_natCast,
    eval_T_real_node (Finset.mem_Iic.2 hl)]
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · rw [node_eq_one, derivative_T_natCast_eval_one, lobattoFactor, ite_eq_left (Or.inl rfl)]
    ring
  rcases eq_or_ne l n with rfl | hln
  · have hn : l ≠ 0 := by omega
    rw [node_eq_neg_one hn, derivative_T_natCast_eval_neg_one, lobattoFactor,
      ite_eq_left (Or.inr rfl)]
    ring
  · rw [eval_derivative_T_node_of_pos_of_lt hl0 (lt_of_le_of_ne hl hln),
      lobattoFactor_of_ne hl0.ne' hln]
    ring

/-- `(1 - x_l²) ((X² - 1) T_n')''(x_l) = -x_l n² (-1)^l` at an interior node. -/
theorem one_sub_sq_mul_eval_derivative_derivative_lobattoNodalT_node {l : ℕ} (hl0 : 0 < l)
    (hln : l < n) :
    (1 - node n l ^ 2) * (derivative (derivative (lobattoNodalT n))).eval (node n l)
      = -node n l * (n : ℝ) ^ 2 * (-1) ^ l := by
  rw [derivative_derivative_lobattoNodalT]
  simp only [eval_add, eval_mul, eval_X, eval_pow, eval_natCast, eval_one,
    eval_derivative_T_node_of_pos_of_lt hl0 hln, mul_zero, zero_add]
  have h := one_sub_sq_mul_eval_derivative_derivative_T (n := n) (node n l)
  rw [eval_derivative_T_node_of_pos_of_lt hl0 hln, eval_T_real_node (Finset.mem_Iic.2 hln.le)] at h
  linear_combination node n l * h

/-- `((X² - 1) T_n')''(1) = n² (4n² + 2)/3`. -/
theorem eval_derivative_derivative_lobattoNodalT_one :
    (derivative (derivative (lobattoNodalT n))).eval 1
      = (n : ℝ) ^ 2 * (4 * (n : ℝ) ^ 2 + 2) / 3 := by
  rw [derivative_derivative_lobattoNodalT]
  simp only [eval_add, eval_mul, eval_X, eval_pow, eval_natCast, eval_one,
    derivative_T_natCast_eval_one, one_mul]
  have h := three_mul_eval_derivative_derivative_T_of_sq_eq_one (n := n) (x := 1) (by norm_num)
  rw [derivative_T_natCast_eval_one] at h
  linear_combination h / 3

/-- `((X² - 1) T_n')''(-1) = -(-1)^n n² (4n² + 2)/3`. -/
theorem eval_derivative_derivative_lobattoNodalT_neg_one :
    (derivative (derivative (lobattoNodalT n))).eval (-1)
      = -((n : ℝ) ^ 2 * (-1) ^ n * (4 * (n : ℝ) ^ 2 + 2) / 3) := by
  rw [derivative_derivative_lobattoNodalT]
  simp only [eval_add, eval_mul, eval_X, eval_pow, eval_natCast, eval_one,
    derivative_T_natCast_eval_neg_one]
  have h := three_mul_eval_derivative_derivative_T_of_sq_eq_one (n := n) (x := -1) (by norm_num)
  rw [derivative_T_natCast_eval_neg_one] at h
  linear_combination h / 3

end Polynomial.Chebyshev

namespace Lagrange

open Polynomial.Chebyshev

variable {n : ℕ}

/-- **The off-diagonal entries of the Chebyshev–Gauss–Lobatto differentiation matrix**
(Canuto–Hussaini–Quarteroni–Zang p. 69; [quarteroni2000numerical] (10.73) at the reflected nodes):
at the nodes `x_j = cos (jπ/n)`, `D_{lj} = (d_l/d_j) (-1)^{l+j} / (x_l - x_j)` for `l ≠ j`, with
`d_0 = d_n = 2` and `d_j = 1` otherwise. -/
theorem derivMatrix_node_of_ne (hn : n ≠ 0) {l j : Fin (n + 1)} (hlj : l ≠ j) :
    derivMatrix (fun j : Fin (n + 1) => node n j) l j
      = lobattoFactor n l / lobattoFactor n j * (-1) ^ ((l : ℕ) + j) / (node n l - node n j) := by
  obtain ⟨c, hc, hp⟩ := lobattoNodalT_eq_C_mul_nodal hn
  rw [derivMatrix_apply, eval_derivative_basis_of_ne_of_eq_C_mul_nodal node_injective.injOn
    (Finset.mem_univ _) (Finset.mem_univ _) hlj.symm hc hp]
  rw [eval_derivative_lobattoNodalT_node (Nat.lt_succ_iff.1 l.isLt),
    eval_derivative_lobattoNodalT_node (Nat.lt_succ_iff.1 j.isLt)]
  have hne : node n l - node n j ≠ 0 := sub_ne_zero.2 fun h => hlj (node_injective h)
  have hdl : lobattoFactor n l ≠ 0 := (lobattoFactor_pos n l).ne'
  have hdj : lobattoFactor n j ≠ 0 := (lobattoFactor_pos n j).ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hj1 : ((-1 : ℝ) ^ (j : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  field_simp
  linear_combination (-(-1 : ℝ) ^ (l : ℕ)) * hj1

/-- **The interior diagonal entries of the Chebyshev–Gauss–Lobatto differentiation matrix**:
`D_{jj} = -x_j / (2 (1 - x_j²))` for `0 < j < n`. -/
theorem derivMatrix_node_self_of_pos_of_lt (hn : n ≠ 0) {j : Fin (n + 1)} (hj0 : 0 < (j : ℕ))
    (hjn : (j : ℕ) < n) :
    derivMatrix (fun j : Fin (n + 1) => node n j) j j = -node n j / (2 * (1 - node n j ^ 2)) := by
  obtain ⟨c, hc, hp⟩ := lobattoNodalT_eq_C_mul_nodal hn
  rw [derivMatrix_apply, eval_derivative_basis_self_of_eq_C_mul_nodal node_injective.injOn
    (Finset.mem_univ _) hc hp, eval_derivative_lobattoNodalT_node (Nat.lt_succ_iff.1 j.isLt),
    lobattoFactor_of_ne hj0.ne' hjn.ne]
  have h := one_sub_sq_mul_eval_derivative_derivative_lobattoNodalT_node hj0 hjn
  have hlt : node n j < 1 := by simpa [node_eq_one] using node_lt (n := n) (i := 0) hjn.le hj0
  have hgt : -1 < node n j := by
    have := node_lt (n := n) (i := j) le_rfl hjn
    rwa [node_eq_neg_one hn] at this
  have h1 : 1 - node n j ^ 2 ≠ 0 := by nlinarith
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hj1 : ((-1 : ℝ) ^ (j : ℕ)) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination 2 * h

/-- **The first diagonal entry of the Chebyshev–Gauss–Lobatto differentiation matrix**:
`D_{00} = (2n² + 1)/6` at the node `x_0 = 1`. -/
theorem derivMatrix_node_zero_zero (hn : n ≠ 0) :
    derivMatrix (fun j : Fin (n + 1) => node n j) 0 0 = (2 * (n : ℝ) ^ 2 + 1) / 6 := by
  obtain ⟨c, hc, hp⟩ := lobattoNodalT_eq_C_mul_nodal hn
  rw [derivMatrix_apply, eval_derivative_basis_self_of_eq_C_mul_nodal node_injective.injOn
    (Finset.mem_univ _) hc hp]
  simp only [Fin.val_zero, node_eq_one, eval_derivative_derivative_lobattoNodalT_one]
  rw [← node_eq_one (n := n), eval_derivative_lobattoNodalT_node (Nat.zero_le n), node_eq_one,
    lobattoFactor, ite_eq_left (Or.inl rfl)]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  ring

/-- **The last diagonal entry of the Chebyshev–Gauss–Lobatto differentiation matrix**:
`D_{nn} = -(2n² + 1)/6` at the node `x_n = -1`. -/
theorem derivMatrix_node_last_last (hn : n ≠ 0) :
    derivMatrix (fun j : Fin (n + 1) => node n j) (Fin.last n) (Fin.last n)
      = -((2 * (n : ℝ) ^ 2 + 1) / 6) := by
  obtain ⟨c, hc, hp⟩ := lobattoNodalT_eq_C_mul_nodal hn
  rw [derivMatrix_apply, eval_derivative_basis_self_of_eq_C_mul_nodal node_injective.injOn
    (Finset.mem_univ _) hc hp]
  simp only [Fin.val_last]
  rw [eval_derivative_lobattoNodalT_node le_rfl, node_eq_neg_one hn,
    eval_derivative_derivative_lobattoNodalT_neg_one, lobattoFactor, ite_eq_left (Or.inr rfl)]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hj1 : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

/-- **The Chebyshev–Gauss–Lobatto differentiation matrix** (Canuto–Hussaini–Quarteroni–Zang,
*Spectral Methods in Fluid Dynamics*, p. 69; [quarteroni2000numerical] (10.73)): at the nodes
`x_j = cos (jπ/n)`, `j = 0, …, n`, `n ≥ 1`,

  `D_{lj} = (d_l/d_j) (-1)^{l+j} / (x_l - x_j)` for `l ≠ j`,
  `D_{jj} = -x_j / (2 (1 - x_j²))` for `0 < j < n`,
  `D_{00} = (2n² + 1)/6`, `D_{nn} = -(2n² + 1)/6`,

with `d_0 = d_n = 2` and `d_j = 1` otherwise (`Polynomial.Chebyshev.lobattoFactor`). The book
states the matrix at the reflected nodes `x̄_j = -x_j`, where it is `-D`
(`Lagrange.derivMatrix_neg`): the two entry formulas keep their form and the corner entries change
sign, so the book's `D̄_{00} = -(2n² + 1)/6` and, correcting its printed `(2n² + 1)/3`,
`D̄_{nn} = (2n² + 1)/6`. -/
theorem chebyshevLobattoDerivMatrix_apply (hn : n ≠ 0) (l j : Fin (n + 1)) :
    derivMatrix (fun j : Fin (n + 1) => node n j) l j
      = if l = j then
          (if (j : ℕ) = 0 then (2 * (n : ℝ) ^ 2 + 1) / 6
            else if (j : ℕ) = n then -((2 * (n : ℝ) ^ 2 + 1) / 6)
            else -node n j / (2 * (1 - node n j ^ 2)))
        else lobattoFactor n l / lobattoFactor n j * (-1) ^ ((l : ℕ) + j)
          / (node n l - node n j) := by
  by_cases hlj : l = j
  · subst hlj
    rw [ite_eq_left rfl]
    by_cases hj0 : (l : ℕ) = 0
    · rw [ite_eq_left hj0, show l = 0 from Fin.ext hj0, derivMatrix_node_zero_zero hn]
    rw [ite_eq_right hj0]
    by_cases hjn : (l : ℕ) = n
    · rw [ite_eq_left hjn, show l = Fin.last n from Fin.ext hjn, derivMatrix_node_last_last hn]
    · rw [ite_eq_right hjn]
      exact derivMatrix_node_self_of_pos_of_lt hn (Nat.pos_of_ne_zero hj0)
        (lt_of_le_of_ne (Nat.lt_succ_iff.1 l.isLt) hjn)
  · rw [ite_eq_right hlj]
    exact derivMatrix_node_of_ne hn hlj

end Lagrange
