import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Numlib.Analysis.ODE.SturmComparison
import Numlib.Approximation.MarkovInequality
import Numlib.Approximation.OrthogonalPolynomial

/-!
# The location of the zeros of the Legendre polynomials and of the Gauss–Lobatto nodes

In the variable `θ = arccos x` the Legendre polynomial becomes the **Liouville normal form**
`u(θ) = √(sin θ) · L_N(cos θ)`, which satisfies

`u'' + ((N + ½)² + 1/(4 sin² θ)) u = 0` on `(0, π)`

(`Polynomial.isSturmSolutionOn_legendreLiouville`; Szegő (4.7.10), derived here from the Legendre
differential equation `Polynomial.legendre_ode`). The potential exceeds `(N + ½)²`, so Sturm's
comparison theorem with `sin ((N + ½)(θ − a))` (`IsSturmSolutionOn.exists_zero_Ioo_of_sq_lt`)
puts a zero of `L_N(cos θ)` in every open interval of `θ`-length `π/(N + ½)` inside `(0, π)`
(`Polynomial.exists_eval_legendre_cos_eq_zero`): in `θ` the zeros of `L_N` are at most
`π/(N + ½)` apart.

The interior Gauss–Lobatto nodes are the zeros of `L_N'` (`Quadrature.derivative_legendre_eq_family`
in `Numlib/Approximation/GaussLobatto`). Two zeros of `L_N` in an interval of `θ`-length
`2π/(N + ½)` give, by Rolle, a zero of `L_N'` between them
(`Polynomial.exists_eval_derivative_legendre_cos_eq_zero`): the Gauss–Lobatto nodes are at most
`2π/(N + ½)` apart in `θ`, and the node nearest to `1` is at `θ < 9π/(4N + 2)`
(`Polynomial.exists_eval_derivative_legendre_cos_eq_zero_lt`), that is at
`x > 1 − 81π²/(32 N²)` (`Polynomial.exists_eval_derivative_legendre_eq_zero_near_one`). By the
symmetry `L_N(−x) = (−1)^N L_N(x)` the same holds at `−1`.

The `θ`-spacing bound is the ingredient of the Marcinkiewicz–Zygmund inequality at the
Gauss–Lobatto nodes; the location of the first node is what the lower eigenvalue bound of the
pseudo-spectral stiffness matrix ([quarteroni2000numerical] §13.3.1, `λ_max ≥ c N⁴`) needs,
together with the size of the Gauss–Lobatto weight there, `w_j ≤ 2048/N²`
(`Quadrature.legendreLobattoWeight_le_of_near_one`): the Christoffel-function bound
`w_j ≤ ∫ p²/p(x_j)²` of a positive rule (`Quadrature.weight_mul_eval_sq_le_of_isExactOnMeasure`)
with the kernel `K_M(·, 1)` of degree `M = ⌊N/16⌋` as test polynomial.

## Main results

* `Polynomial.legendreLiouville`, `Polynomial.legendreLiouvillePotential`,
  `Polynomial.isSturmSolutionOn_legendreLiouville` — the Liouville normal form and its equation.
* `Polynomial.exists_eval_legendre_cos_eq_zero` — a zero of `L_N(cos ·)` in every open
  `θ`-interval of length `π/(N + ½)` inside `(0, π)`.
* `Polynomial.exists_eval_derivative_legendre_cos_eq_zero` — a zero of `L_N'(cos ·)` in every
  open `θ`-interval of length `2π/(N + ½)` inside `(0, π)`.
* `Polynomial.exists_eval_derivative_legendre_eq_zero_near_one` — for `N ≥ 2`, a zero `t` of
  `L_N'` with `1 − 81π²/(32 N²) < t < 1`.
* `Polynomial.abs_eval_derivative_legendre_le` — `|L_k'(x)| ≤ k²` on `[-1, 1]`.
* `Quadrature.weight_mul_eval_sq_le_of_isExactOnMeasure`,
  `Quadrature.legendreLobattoWeight_le_of_near_one` — the Christoffel-function bound on the
  weights and the Legendre–Gauss–Lobatto weight `w_j ≤ 2048/N²` at a node within `81π²/(32 N²)`
  of `1`.

## References

Szegő, *Orthogonal Polynomials*, §4.7 (4.7.10) and §6.3; [quarteroni2000numerical] §10.4, §13.3.1.
-/

open MeasureTheory Real Set

namespace Polynomial

variable (N : ℕ)

/-! ### The Liouville normal form of the Legendre equation -/

/-- **The Liouville normal form of the Legendre polynomial**: `u(θ) = √(sin θ) · L_N(cos θ)`. -/
noncomputable def legendreLiouville (θ : ℝ) : ℝ :=
  √(sin θ) * (legendre N).eval (cos θ)

/-- The derivative of `legendreLiouville`:
`u'(θ) = (cos θ / (2 √(sin θ))) L_N(cos θ) − √(sin θ) sin θ L_N'(cos θ)`. -/
noncomputable def legendreLiouvilleDeriv (θ : ℝ) : ℝ :=
  cos θ / (2 * √(sin θ)) * (legendre N).eval (cos θ) -
    √(sin θ) * sin θ * (derivative (legendre N)).eval (cos θ)

/-- The potential of the Liouville normal form: `q(θ) = (N + ½)² + 1/(4 sin² θ)`. -/
noncomputable def legendreLiouvillePotential (θ : ℝ) : ℝ :=
  ((N : ℝ) + 1 / 2) ^ 2 + 1 / (4 * sin θ ^ 2)

variable {N}

/-- The derivative of `√(sin θ)` on `(0, π)`. -/
private theorem hasDerivAt_sqrt_sin {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (fun θ => √(sin θ)) (1 / (2 * √(sin θ)) * cos θ) θ :=
  (Real.hasDerivAt_sqrt (sin_pos_of_mem_Ioo hθ).ne').comp θ (Real.hasDerivAt_sin θ)

/-- The derivative of `p(cos θ)`. -/
private theorem hasDerivAt_eval_cos (p : ℝ[X]) (θ : ℝ) :
    HasDerivAt (fun θ => p.eval (cos θ)) ((derivative p).eval (cos θ) * -sin θ) θ :=
  (p.hasDerivAt (cos θ)).comp θ (Real.hasDerivAt_cos θ)

/-- `u' = legendreLiouvilleDeriv` on `(0, π)`. -/
theorem hasDerivAt_legendreLiouville {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (legendreLiouville N) (legendreLiouvilleDeriv N θ) θ := by
  refine ((hasDerivAt_sqrt_sin hθ).mul (hasDerivAt_eval_cos (legendre N) θ)).congr_deriv ?_
  unfold legendreLiouvilleDeriv
  ring

/-- **The Legendre equation in Liouville normal form**: on `(0, π)`,
`u'' = −((N + ½)² + 1/(4 sin² θ)) u` for `u(θ) = √(sin θ) L_N(cos θ)`. With `r = √(sin θ)`,
`c = cos θ`, the second derivative of `u = r L_N(c)` is
`−(2r⁴ + c²) L/(4r³) − 2 r c L' + r⁵ L''`, and `c² = 1 − r⁴` together with the Legendre equation
`(c² − 1) L'' + 2c L' = N(N+1) L` (`Polynomial.legendre_ode`) turn it into
`−((N + ½)² + 1/(4r⁴)) r L`. -/
theorem hasDerivAt_legendreLiouvilleDeriv {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (legendreLiouvilleDeriv N)
      (-(legendreLiouvillePotential N θ * legendreLiouville N θ)) θ := by
  have hs : 0 < sin θ := sin_pos_of_mem_Ioo hθ
  have hr : 0 < √(sin θ) := Real.sqrt_pos.2 hs
  have hsq := hasDerivAt_sqrt_sin hθ
  have hA : HasDerivAt (fun θ => cos θ / (2 * √(sin θ)))
      ((-sin θ * (2 * √(sin θ)) - cos θ * (2 * (1 / (2 * √(sin θ)) * cos θ))) /
        (2 * √(sin θ)) ^ 2) θ :=
    (Real.hasDerivAt_cos θ).div (hsq.const_mul 2) (by positivity)
  have hC : HasDerivAt (fun θ => √(sin θ) * sin θ)
      (1 / (2 * √(sin θ)) * cos θ * sin θ + √(sin θ) * cos θ) θ :=
    hsq.mul (Real.hasDerivAt_sin θ)
  refine ((hA.mul (hasDerivAt_eval_cos (legendre N) θ)).sub
    (hC.mul (hasDerivAt_eval_cos (derivative (legendre N)) θ))).congr_deriv ?_
  -- the algebra: `r = √(sin θ)`, `c = cos θ`, `sin θ = r²`, `c² = 1 − r⁴`, and the ODE
  have hode := congrArg (eval (cos θ)) (legendre_ode N)
  simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_one, eval_natCast,
    eval_ofNat] at hode
  have hcs : cos θ ^ 2 = 1 - sin θ ^ 2 := by rw [cos_sq']
  unfold legendreLiouvillePotential legendreLiouville
  set r := √(sin θ) with hr_def
  have hr2 : sin θ = r ^ 2 := (Real.sq_sqrt hs.le).symm
  rw [hr2] at hcs ⊢
  set c := cos θ
  set L := (legendre N).eval c
  set L' := (derivative (legendre N)).eval c
  set L'' := (derivative (derivative (legendre N))).eval c
  have hr0 : r ≠ 0 := hr.ne'
  field_simp
  linear_combination (-4 * L + 16 * r ^ 4 * L'') * hcs + (-16 * r ^ 4) * hode

/-- **`u = √(sin θ) L_N(cos θ)` solves `u'' + ((N + ½)² + 1/(4 sin² θ)) u = 0` on `(0, π)`.**

Reference: Szegő, *Orthogonal Polynomials*, (4.7.10). -/
theorem isSturmSolutionOn_legendreLiouville :
    IsSturmSolutionOn (legendreLiouvillePotential N) (legendreLiouville N)
      (legendreLiouvilleDeriv N) (Ioo 0 π) :=
  ⟨fun _ hθ => hasDerivAt_legendreLiouville hθ, fun _ hθ => hasDerivAt_legendreLiouvilleDeriv hθ⟩

/-- The potential of the Liouville normal form exceeds `(N + ½)²` on `(0, π)`. -/
theorem sq_lt_legendreLiouvillePotential {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    ((N : ℝ) + 1 / 2) ^ 2 < legendreLiouvillePotential N θ := by
  have hs : 0 < sin θ := sin_pos_of_mem_Ioo hθ
  unfold legendreLiouvillePotential
  have : 0 < 1 / (4 * sin θ ^ 2) := by positivity
  linarith

/-! ### The zeros of `L_N(cos θ)` -/

/-- **The zeros of `L_N(cos θ)` are at most `π/(N + ½)` apart**: every open interval
`(a, b) ⊆ (0, π)` of length at least `π/(N + ½)` contains a zero of `θ ↦ L_N(cos θ)`. Sturm
comparison of the Liouville normal form with `sin ((N + ½)(θ − a))`.

Reference: Szegő, *Orthogonal Polynomials*, Theorem 6.3.2 (the Legendre case). -/
theorem exists_eval_legendre_cos_eq_zero {a b : ℝ} (ha : 0 < a) (hb : b < π)
    (hab : π / ((N : ℝ) + 1 / 2) ≤ b - a) :
    ∃ θ ∈ Ioo a b, (legendre N).eval (cos θ) = 0 := by
  have hm : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  have hsub : Icc a b ⊆ Ioo 0 π := fun x hx => ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  obtain ⟨θ, hθ, hθ0⟩ := (isSturmSolutionOn_legendreLiouville (N := N)).mono hsub
    |>.exists_zero_Ioo_of_sq_lt hm hab
      fun x hx => sq_lt_legendreLiouvillePotential (hsub (Ioo_subset_Icc_self hx))
  refine ⟨θ, hθ, ?_⟩
  have hs : 0 < sin θ := sin_pos_of_mem_Ioo (hsub (Ioo_subset_Icc_self hθ))
  unfold legendreLiouville at hθ0
  exact (mul_eq_zero.1 hθ0).resolve_left (Real.sqrt_pos.2 hs).ne'

/-! ### The Gauss–Lobatto nodes -/

/-- **The zeros of `L_N'(cos θ)` — the interior Gauss–Lobatto nodes — are at most `2π/(N + ½)`
apart in `θ`**: every open interval `(a, b) ⊆ (0, π)` of length at least `2π/(N + ½)` contains a
zero of `θ ↦ L_N'(cos θ)`. Two zeros of `L_N(cos ·)` in `(a, b)`, one in each half, and Rolle's
theorem for `L_N` between the corresponding points `cos θ₂ < cos θ₁`. -/
theorem exists_eval_derivative_legendre_cos_eq_zero {a b : ℝ} (ha : 0 < a) (hb : b < π)
    (hab : 2 * (π / ((N : ℝ) + 1 / 2)) ≤ b - a) :
    ∃ θ ∈ Ioo a b, (derivative (legendre N)).eval (cos θ) = 0 := by
  have hm : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  have hπm : 0 < π / ((N : ℝ) + 1 / 2) := div_pos pi_pos hm
  obtain ⟨θ₁, hθ₁, h1⟩ := exists_eval_legendre_cos_eq_zero (N := N) (a := a)
    (b := a + π / ((N : ℝ) + 1 / 2)) ha (by linarith) (by linarith)
  obtain ⟨θ₂, hθ₂, h2⟩ := exists_eval_legendre_cos_eq_zero (N := N)
    (a := a + π / ((N : ℝ) + 1 / 2)) (b := b) (by linarith) hb (by linarith)
  have h12 : θ₁ < θ₂ := hθ₁.2.trans hθ₂.1
  have hθ₁0 : 0 ≤ θ₁ := by linarith [hθ₁.1]
  have hθ₂π : θ₂ ≤ π := by linarith [hθ₂.2]
  have hcos : cos θ₂ < cos θ₁ := cos_lt_cos_of_nonneg_of_le_pi hθ₁0 hθ₂π h12
  obtain ⟨t, ht, ht0⟩ := exists_hasDerivAt_eq_zero (f := fun x => (legendre N).eval x)
    (f' := fun x => (derivative (legendre N)).eval x) hcos
    (legendre N).continuous.continuousOn (by simp only [h1, h2])
    fun x _ => (legendre N).hasDerivAt x
  have ht1 : -1 ≤ t := (neg_one_le_cos θ₂).trans ht.1.le
  have ht2 : t ≤ 1 := ht.2.le.trans (cos_le_one θ₁)
  refine ⟨arccos t, ⟨?_, ?_⟩, by rwa [cos_arccos ht1 ht2]⟩
  · calc a < θ₁ := hθ₁.1
      _ = arccos (cos θ₁) := (arccos_cos hθ₁0 (by linarith)).symm
      _ < arccos t := strictAntiOn_arccos ⟨ht1, ht2⟩ ⟨neg_one_le_cos _, cos_le_one _⟩ ht.2
  · calc arccos t < arccos (cos θ₂) :=
          strictAntiOn_arccos ⟨neg_one_le_cos _, cos_le_one _⟩ ⟨ht1, ht2⟩ ht.1
      _ = θ₂ := arccos_cos (by linarith) hθ₂π
      _ < b := hθ₂.2

/-- **The Gauss–Lobatto node nearest to `1`, in `θ`-form**: for `N ≥ 2` there is a zero of
`L_N'(cos θ)` with `0 < θ < 9π/(4N + 2)`, from
`Polynomial.exists_eval_derivative_legendre_cos_eq_zero` on `(π/(4N + 2), 9π/(4N + 2))`. -/
theorem exists_eval_derivative_legendre_cos_eq_zero_lt (hN : 2 ≤ N) :
    ∃ θ, 0 < θ ∧ θ < 9 * π / (4 * (N : ℝ) + 2) ∧ (derivative (legendre N)).eval (cos θ) = 0 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hm : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  set m : ℝ := (N : ℝ) + 1 / 2 with hm_def
  have hπm : 0 < π / m := div_pos pi_pos hm
  have h9 : 9 * π / (4 * (N : ℝ) + 2) = 9 / 4 * (π / m) := by
    rw [hm_def]; field_simp; ring
  have hb : 9 / 4 * (π / m) < π := by
    rw [mul_div_assoc', div_lt_iff₀ hm, hm_def]
    nlinarith [pi_pos]
  obtain ⟨θ, hθ, h⟩ := exists_eval_derivative_legendre_cos_eq_zero (N := N)
    (a := 1 / 4 * (π / m)) (b := 9 / 4 * (π / m)) (by positivity) hb (by linarith)
  exact ⟨θ, by linarith [hθ.1], by rw [h9]; exact hθ.2, h⟩

/-- **The Gauss–Lobatto node nearest to `1` is within `81π²/(32 N²)` of it**: for `N ≥ 2` there is a
zero `t` of `L_N'` with `1 − 81π²/(32 N²) < t < 1`. From the `θ`-form
`θ < 9π/(4N + 2) < 9π/(4N)` and `1 − cos θ ≤ θ²/2` (`Real.one_sub_sq_div_two_le_cos`).

This is the node location the lower eigenvalue bound of the pseudo-spectral stiffness matrix
needs ([quarteroni2000numerical] §13.3.1, `λ_max ≥ c N⁴`). -/
theorem exists_eval_derivative_legendre_eq_zero_near_one (hN : 2 ≤ N) :
    ∃ t, (derivative (legendre N)).eval t = 0 ∧
      1 - 81 * π ^ 2 / (32 * (N : ℝ) ^ 2) < t ∧ t < 1 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨θ, hθ0, hθ, h⟩ := exists_eval_derivative_legendre_cos_eq_zero_lt hN
  refine ⟨cos θ, h, ?_, ?_⟩
  · have hθ' : θ < 9 * π / (4 * (N : ℝ)) := by
      refine hθ.trans_le ?_
      gcongr
      linarith
    have hsq : θ ^ 2 < (9 * π / (4 * (N : ℝ))) ^ 2 := by gcongr
    have hcos := one_sub_sq_div_two_le_cos (x := θ)
    have h81 : (9 * π / (4 * (N : ℝ))) ^ 2 / 2 = 81 * π ^ 2 / (32 * (N : ℝ) ^ 2) := by
      field_simp; ring
    linarith
  · have hθπ : θ < π := by
      refine hθ.trans_le ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith [pi_pos]
    simpa using cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ.le hθ0

/-! ### The Gauss–Lobatto weights near the endpoints

The weight of a positive quadrature rule exact on `ℙ_{2n-1}` at a node `x_j` is at most
`∫ p² / p(x_j)²` for every `p ∈ ℙ_{n-1}` (`Quadrature.weight_mul_eval_sq_le_of_isExactOnMeasure`),
the Christoffel-function bound. At a node within `81π²/(32 N²)` of `1` the test polynomial
`K_M(x, 1) = ∑_{k ≤ M} ((2k + 1)/2) L_k(x)` with `M = ⌊N/16⌋` has `∫ K_M² = (M + 1)²/2` (Parseval)
and `K_M(x_j, 1) ≥ (M + 1)²/4`, because `L_k(x_j) ≥ 1 − k²(1 − x_j) ≥ 1/2` for `k ≤ M` by the
endpoint bound `|L_k'| ≤ k²`; hence `w_j ≤ 8/(M + 1)² < 2048/N²`
(`Quadrature.legendreLobattoWeight_le_of_near_one`). -/

/-- **`|L_k'(x)| ≤ k²` on `[-1, 1]`**: `L_k' = ∑_{j < k} (L_k')^_j L_j` with `|(L_k')^_j| ≤ 2j + 1`
(`Polynomial.abs_legendreCoeff_derivative_legendre_le`) and `|L_j| ≤ 1`. -/
theorem abs_eval_derivative_legendre_le (k : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(derivative (legendre k)).eval x| ≤ (k : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [legendre_zero]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hdeg : (derivative (legendre (m + 1))).natDegree ≤ m := by
    have := natDegree_derivative_le (legendre (m + 1))
    rw [natDegree_legendre] at this
    omega
  rw [eq_sum_legendreCoeff hdeg]
  simp only [eval_finsetSum, eval_mul, eval_C]
  calc |∑ j ∈ Finset.range (m + 1),
        legendreCoeff (derivative (legendre (m + 1))) j * (legendre j).eval x|
      ≤ ∑ j ∈ Finset.range (m + 1),
          |legendreCoeff (derivative (legendre (m + 1))) j * (legendre j).eval x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (m + 1), (2 * (j : ℝ) + 1) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        calc |legendreCoeff (derivative (legendre (m + 1))) j| * |(legendre j).eval x|
            ≤ (2 * (j : ℝ) + 1) * 1 :=
              mul_le_mul (abs_legendreCoeff_derivative_legendre_le _ _)
                (abs_eval_legendre_le_one j hx) (abs_nonneg _) (by positivity)
          _ = 2 * (j : ℝ) + 1 := mul_one _
    _ = ((m : ℝ) + 1) ^ 2 := sum_range_two_mul_add_one m
    _ = ((m + 1 : ℕ) : ℝ) ^ 2 := by push_cast; ring

/-- **`L_k(t) ≥ 1 − k²(1 − t)` on `[-1, 1]`**: `L_k(1) = 1` and `|L_k'| ≤ k²`. -/
theorem one_sub_sq_mul_le_eval_legendre (k : ℕ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    1 - (k : ℝ) ^ 2 * (1 - t) ≤ (legendre k).eval t := by
  have hftc : ∫ x in t..1, (derivative (legendre k)).eval x =
      (legendre k).eval 1 - (legendre k).eval t :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (legendre k).hasDerivAt x)
      ((derivative (legendre k)).continuous.intervalIntegrable _ _)
  have hle : ∫ x in t..1, (derivative (legendre k)).eval x ≤ ∫ x in t..1, (k : ℝ) ^ 2 := by
    refine intervalIntegral.integral_mono_on ht.2
      ((derivative (legendre k)).continuous.intervalIntegrable _ _)
      intervalIntegrable_const fun x hx => ?_
    exact (le_abs_self _).trans (abs_eval_derivative_legendre_le k ⟨by linarith [hx.1, ht.1], hx.2⟩)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hle
  rw [legendre_eval_one] at hftc
  linarith

/-- **The Christoffel–Darboux kernel at `1`**, `K_M(x, 1) = ∑_{k ≤ M} ((2k + 1)/2) L_k(x)`: the
polynomial of degree `M` concentrated at `x = 1` on a layer of width `M⁻²`. -/
noncomputable def legendreKernelOne (M : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (M + 1), C ((2 * (k : ℝ) + 1) / 2) * legendre k

/-- `K_M(·, 1)` has degree at most `M`. -/
theorem natDegree_legendreKernelOne_le (M : ℕ) : (legendreKernelOne M).natDegree ≤ M := by
  refine (natDegree_sum_le_of_forall_le _ _ fun k hk => ?_)
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_legendre]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)

/-- The Legendre coefficients of `K_M(·, 1)` are `(2k + 1)/2` for `k ≤ M`. -/
theorem legendreCoeff_legendreKernelOne (M : ℕ) {k : ℕ} (hk : k ∈ Finset.range (M + 1)) :
    legendreCoeff (legendreKernelOne M) k = (2 * (k : ℝ) + 1) / 2 := by
  rw [legendreKernelOne, legendreCoeff_sum, Finset.sum_eq_single k]
  · rw [legendreCoeff_C_mul, legendreCoeff_legendre, ite_eq_left rfl, mul_one]
  · intro j _ hjk
    rw [legendreCoeff_C_mul, legendreCoeff_legendre, ite_eq_right hjk, mul_zero]
  · intro h; exact absurd hk h

/-- **`∫_{-1}^1 K_M(x, 1)² dx = (M + 1)²/2`**, by Parseval. -/
theorem integral_legendreKernelOne_sq (M : ℕ) :
    ∫ x in (-1 : ℝ)..1, (legendreKernelOne M).eval x ^ 2 = ((M : ℝ) + 1) ^ 2 / 2 := by
  rw [integral_sq_eq_sum_legendreCoeff (natDegree_legendreKernelOne_le M)]
  rw [← sum_range_two_mul_add_one M, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [legendreCoeff_legendreKernelOne M hk]
  have : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- **`K_M(t, 1) ≥ (M + 1)²/4`** when `k²(1 − t) ≤ 1/2` for every `k ≤ M`, since then every
`L_k(t) ≥ 1/2`. -/
theorem le_eval_legendreKernelOne (M : ℕ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (hsmall : ∀ k ≤ M, (k : ℝ) ^ 2 * (1 - t) ≤ 1 / 2) :
    ((M : ℝ) + 1) ^ 2 / 4 ≤ (legendreKernelOne M).eval t := by
  rw [legendreKernelOne, eval_finsetSum]
  simp only [eval_mul, eval_C]
  calc ((M : ℝ) + 1) ^ 2 / 4 = ∑ k ∈ Finset.range (M + 1), (2 * (k : ℝ) + 1) / 2 * (1 / 2) := by
        rw [← Finset.sum_mul, ← Finset.sum_div, sum_range_two_mul_add_one]; ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have h1 := one_sub_sq_mul_le_eval_legendre k ht
        have h2 := hsmall k hk'
        have : (0 : ℝ) ≤ (2 * (k : ℝ) + 1) / 2 := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) this

end Polynomial

namespace Quadrature

open OrthogonalPolynomial Polynomial

/-- **The Christoffel-function bound on the weights of a positive rule**: if the rule with
nonnegative weights is exact to degree `d` and `p² ∈ ℙ_d`, then `w_j p(x_j)² ≤ ∫ p² ∂μ`, one term
of the nonnegative sum `∑ w_i p(x_i)² = ∫ p²`. -/
theorem weight_mul_eval_sq_le_of_isExactOnMeasure {μ : MeasureTheory.Measure ℝ} {n d : ℕ}
    {w x : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) (hexact : IsExactOnMeasure μ w x d) {p : ℝ[X]}
    (hp : (p * p).degree ≤ d) (j : Fin n) :
    w j * p.eval (x j) ^ 2 ≤ ∫ t, p.eval t ^ 2 ∂μ := by
  have h := hexact (p * p) hp
  simp only [eval_mul] at h
  have hsq : ∫ t, p.eval t ^ 2 ∂μ = ∫ t, p.eval t * p.eval t ∂μ := by simp only [sq]
  rw [hsq, ← h, sq]
  exact Finset.single_le_sum (f := fun i => w i * (p.eval (x i) * p.eval (x i)))
    (fun i _ => mul_nonneg (hw i) (mul_self_nonneg _)) (Finset.mem_univ j)

/-- **The Legendre–Gauss–Lobatto weight at a node within `81π²/(32 N²)` of `1` is at most
`2048/N²`.** The Christoffel-function bound with the test polynomial `K_M(·, 1)`, `M = ⌊N/16⌋`:
`w_j ≤ ∫ K_M² / K_M(x_j)² ≤ ((M + 1)²/2) / ((M + 1)²/4)² = 8/(M + 1)² < 2048/N²`, the
hypothesis `k²(1 − x_j) ≤ (N/16)² · 81π²/(32 N²) ≤ 1/2` (`π ≤ 4`) of
`Polynomial.le_eval_legendreKernelOne` holding for every `k ≤ M`. -/
theorem legendreLobattoWeight_le_of_near_one {N : ℕ} (hN : 1 ≤ N) {x w : Fin (N + 1) → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hexact : IsExactOnMeasure legendreMeasure w x (2 * N - 1))
    (j : Fin (N + 1)) (hxj : x j ∈ Icc (-1 : ℝ) 1)
    (hnear : 1 - x j ≤ 81 * π ^ 2 / (32 * (N : ℝ) ^ 2)) :
    w j ≤ 2048 / (N : ℝ) ^ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set M := N / 16 with hM
  have hM16 : 16 * M ≤ N := by omega
  have hNM : N < 16 * (M + 1) := by omega
  have hMR : 16 * (M : ℝ) ≤ N := by exact_mod_cast hM16
  have hNMR : (N : ℝ) < 16 * ((M : ℝ) + 1) := by exact_mod_cast hNM
  -- the smallness hypothesis
  have hsmall : ∀ k ≤ M, (k : ℝ) ^ 2 * (1 - x j) ≤ 1 / 2 := by
    intro k hk
    have hkR : (k : ℝ) ≤ M := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hpi := pi_le_four
    have hpi2 : π ^ 2 ≤ 16 := by nlinarith [pi_pos]
    have h1 : (k : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 / 256 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    have h2 : 0 ≤ 1 - x j := by linarith [hxj.2]
    have h3 : 81 * π ^ 2 / (32 * (N : ℝ) ^ 2) ≤ 81 * 16 / (32 * (N : ℝ) ^ 2) := by gcongr
    calc (k : ℝ) ^ 2 * (1 - x j) ≤ (N : ℝ) ^ 2 / 256 * (81 * 16 / (32 * (N : ℝ) ^ 2)) :=
          mul_le_mul h1 (hnear.trans h3) h2 (by positivity)
      _ = 81 / 512 := by field_simp; ring
      _ ≤ 1 / 2 := by norm_num
  have hK := Polynomial.le_eval_legendreKernelOne M hxj hsmall
  have hKpos : 0 < (Polynomial.legendreKernelOne M).eval (x j) := lt_of_lt_of_le (by positivity) hK
  have hdeg : (Polynomial.legendreKernelOne M * Polynomial.legendreKernelOne M).degree ≤
      ((2 * N - 1 : ℕ) : WithBot ℕ) := by
    refine (degree_mul_le _ _).trans ?_
    have h1 := degree_le_of_natDegree_le (Polynomial.natDegree_legendreKernelOne_le M)
    calc (Polynomial.legendreKernelOne M).degree + (Polynomial.legendreKernelOne M).degree
        ≤ (M : WithBot ℕ) + (M : WithBot ℕ) := add_le_add h1 h1
      _ = ((M + M : ℕ) : WithBot ℕ) := by push_cast; rfl
      _ ≤ ((2 * N - 1 : ℕ) : WithBot ℕ) := by exact_mod_cast (by omega : M + M ≤ 2 * N - 1)
  have hbound := weight_mul_eval_sq_le_of_isExactOnMeasure hw hexact hdeg j
  rw [integral_legendreMeasure, Polynomial.integral_legendreKernelOne_sq] at hbound
  -- `w_j ≤ ((M+1)²/2) / K(x_j)² ≤ 8/(M+1)²`
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hw8 : w j ≤ 8 / ((M : ℝ) + 1) ^ 2 := by
    have hKsq : ((M : ℝ) + 1) ^ 4 / 16 ≤ (Polynomial.legendreKernelOne M).eval (x j) ^ 2 := by
      calc ((M : ℝ) + 1) ^ 4 / 16 = (((M : ℝ) + 1) ^ 2 / 4) ^ 2 := by ring
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hK 2
    have := mul_le_mul_of_nonneg_left hKsq (hw j)
    rw [le_div_iff₀ (by positivity)]
    calc w j * ((M : ℝ) + 1) ^ 2 = w j * (((M : ℝ) + 1) ^ 4 / 16) * (16 / ((M : ℝ) + 1) ^ 2) := by
          field_simp
      _ ≤ (((M : ℝ) + 1) ^ 2 / 2) * (16 / ((M : ℝ) + 1) ^ 2) := by
          exact mul_le_mul_of_nonneg_right (this.trans hbound) (by positivity)
      _ = 8 := by field_simp; ring
  refine hw8.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hNMR, hNR]

end Quadrature
