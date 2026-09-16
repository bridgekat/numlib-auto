import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Numlib.Approximation.OrthogonalPolynomial.Classical
import Numlib.Approximation.Quadrature
import Numlib.Approximation.TrapezoidExactness

/-!
# Gauss–Lobatto quadrature and the classical Gauss rules

Gauss–Lobatto quadrature: the rule with `n + 1` nodes including both endpoints of the interval
carrying the weight, exact on the polynomials of degree at most `2n - 1`; and the closed forms of
the Chebyshev and Legendre Gauss and Gauss–Lobatto rules and of the Gauss–Laguerre and Gauss–Hermite
weights.

## The construction

The Lobatto nodal polynomial is not built from the textbook ansatz "choose `a, b` so that `p_{n+1} +
a p_n + b p_{n-1}` vanishes at `±1`" but from its equivalent: `ω̄ = (X² - 1) q_{n-1}` with `q_{n-1}`
the `(n - 1)`-st monic orthogonal polynomial of the *modified* weight `(1 - x²) μ`
(`OrthogonalPolynomial.lobattoMeasure`), which is again a weight carried by `[-1, 1]`. Then
`q_{n-1}` has `n - 1` simple roots in `(-1, 1)`, `ω̄` is `μ`-orthogonal to `P_{n-2}` because `∫ ω̄ p
∂μ = -∫ q_{n-1} p ∂((1 - x²) μ)`, and Jacobi's theorem `Quadrature.isExactOnMeasure_add_iff` at `m =
n - 1` gives exactness `2n - 1` for the interpolatory rule (`Quadrature.exists_gaussLobatto`).
Positivity of the weights uses the test polynomials `(1 - x²)(q/(x - x̄_i))²` at interior nodes and
`(1 ∓ x) q²` at the endpoints (`Quadrature.pos_of_isExactOnMeasure`). The textbook form of `ω̄` is
recovered by expanding it in the orthogonal family (`Quadrature.lobattoNodal_eq_add_smul`), and
conversely any such combination vanishing at `±1` is `ω̄`
(`Quadrature.eq_lobattoNodal_of_eval_eq_zero`).

## The weights

All closed-form weights come from one identity. For an interpolatory rule whose nodal polynomial is
`ω = p_{n+1} + a p_n + b p_{n-1}`, the Christoffel–Darboux identity
`OrthogonalPolynomial.christoffel_darboux` gives `p_n(x_j) ω/(X - x_j) = ‖p_n‖² K_n(x_j) - b
‖p_{n-1}‖² K_{n-1}(x_j)`, whose integral is `‖p_n‖² - b ‖p_{n-1}‖²`; hence `w_j = (‖p_n‖² - b
‖p_{n-1}‖²) / (p_n(x_j) ω'(x_j))` (`Quadrature.weight_eq_of_nodal_eq`). With `a = b = 0` this is the
Gauss weight `‖p_n‖² / (p_n(x_j) p_{n+1}'(x_j))` (`Quadrature.gaussWeight_eq`), which the Legendre,
Laguerre and Hermite identities turn into the textbook formulas; with the Lobatto nodal polynomial
of the Legendre weight it gives `2 / (n(n+1) L_n(x̄_j)²)`.

The derivative of a Jacobi polynomial is a Jacobi polynomial of the shifted weight
(`Quadrature.derivative_family_jacobiMeasure`), by one integration by parts with `rpow` weights on
the open interval; so the interior Lobatto nodes of a Jacobi weight are the zeros of
`(J_n^{(α,β)})'`, and for the Legendre weight the zeros of `L_n'`
(`Quadrature.derivative_legendre_eq_family`).

The Chebyshev–Gauss–Lobatto rule at the extrema `cos (jπ/n)` of `T_n` with weights `π/(d_j n)` is
proved by the discrete orthogonality of the cosines (`Polynomial.Chebyshev.integral_eq_sumExtrema`),
and the discrete Chebyshev and Legendre transforms are the instances of
`Quadrature.interpolate_eq_sum_discreteInner_smul`.

## References

[quarteroni2000numerical] §10.2–10.5; Davis–Rabinowitz, *Methods of Numerical Integration*, §2.7;
[kress1998numerical] §9.3.
-/

open MeasureTheory Polynomial Real Set Filter Topology

open scoped Nat

noncomputable section

namespace OrthogonalPolynomial

variable {μ : Measure ℝ}

/-! ### The modified weight `(1 - x²) μ` -/

/-- The weight `(1 - x²) μ` whose orthogonal polynomials supply the interior Gauss–Lobatto nodes
of `μ`. -/
abbrev lobattoMeasure (μ : Measure ℝ) : Measure ℝ :=
  μ.withDensity fun x => ENNReal.ofReal (1 - x ^ 2)

/-- An integral against the modified weight, for a weight carried by `[-1, 1]`. -/
theorem integral_lobattoMeasure (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) (f : ℝ → ℝ) :
    ∫ x, f x ∂lobattoMeasure μ = ∫ x, (1 - x ^ 2) * f x ∂μ := by
  refine integral_withDensity_ofReal (by fun_prop) ?_ f
  have hae : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := by
    rw [ae_iff]
    exact hsupp
  filter_upwards [hae] with x hx
  nlinarith [hx.1, hx.2]

/-- The modified weight is carried by `[-1, 1]` when `μ` is. -/
theorem lobattoMeasure_compl_Icc (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) :
    lobattoMeasure μ (Icc (-1 : ℝ) 1)ᶜ = 0 :=
  withDensity_absolutelyContinuous μ _ hsupp

/-- The Lobatto weight of a Jacobi weight is the Jacobi weight with both exponents raised by
one. -/
theorem lobattoMeasure_jacobiMeasure (α β : ℝ) :
    lobattoMeasure (jacobiMeasure α β) = jacobiMeasure (α + 1) (β + 1) := by
  rw [lobattoMeasure, jacobiMeasure, jacobiMeasure, ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  refine withDensity_congr_ae ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun x hx => ?_
  have h1 : 1 - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx.2)
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h1' : 0 ≤ 1 - x := by linarith [hx.2]
  have h2' : 0 ≤ 1 + x := by linarith [hx.1]
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (by positivity), rpow_add_one h1, rpow_add_one h2]
  congr 1
  ring

/-- **The modified weight is a weight.** Its moments are moments of `μ`, and its density is
positive on `(-1, 1)`, where `μ` puts positive mass outside every finite set once the endpoints are
added to that set. -/
theorem isWeight_withDensity_one_sub_sq (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) :
    IsWeight (μ.withDensity fun x => ENNReal.ofReal (1 - x ^ 2)) := by
  have hae : ∀ᵐ x ∂μ, x ∈ Icc (-1 : ℝ) 1 := by
    rw [ae_iff]
    exact hsupp
  have hnn : ∀ᵐ x ∂μ, 0 ≤ 1 - x ^ 2 := by
    filter_upwards [hae] with x hx
    nlinarith [hx.1, hx.2]
  constructor
  · intro n
    rw [integrable_withDensity_ofReal_iff (by fun_prop) hnn]
    exact (hw.integrable_eval ((1 - X ^ 2) * X ^ n)).congr
      (Eventually.of_forall fun x => by simp)
  · intro s hs h
    rw [withDensity_apply_eq_zero' (by fun_prop)] at h
    have hsub : Icc (-1 : ℝ) 1 ∩ (({-1, 1} : Set ℝ) ∪ s)ᶜ ⊆
        {x | ENNReal.ofReal (1 - x ^ 2) ≠ 0} ∩ sᶜ := by
      rintro x ⟨hx, hx'⟩
      simp only [mem_compl_iff, mem_union, mem_insert_iff, mem_singleton_iff, not_or] at hx'
      refine ⟨fun h0 => ?_, hx'.2⟩
      have h1 : x ≠ -1 := hx'.1.1
      have h2 : x ≠ 1 := hx'.1.2
      have hlt : 0 < 1 - x ^ 2 := by
        have ha : -1 < x := lt_of_le_of_ne hx.1 (Ne.symm h1)
        have hb : x < 1 := lt_of_le_of_ne hx.2 h2
        nlinarith
      exact absurd (ENNReal.ofReal_eq_zero.mp h0) (not_le.mpr hlt)
    have h1 : μ (Icc (-1 : ℝ) 1 ∩ (({-1, 1} : Set ℝ) ∪ s)ᶜ) = 0 := measure_mono_null hsub h
    have hfin : (({-1, 1} : Set ℝ) ∪ s).Finite := (Set.toFinite _).union hs
    refine hw.measure_compl_ne_zero hfin ?_
    have hsplit := measure_inter_add_sdiff (μ := μ) ((({-1, 1} : Set ℝ) ∪ s)ᶜ)
      (measurableSet_Icc (a := (-1 : ℝ)) (b := 1))
    rw [inter_comm, h1, zero_add] at hsplit
    rw [← hsplit]
    exact measure_mono_null (fun x hx => hx.2) hsupp

/-- The modified weight of a weight carried by `[-1, 1]` is a weight. -/
theorem isWeight_lobattoMeasure (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) :
    IsWeight (lobattoMeasure μ) :=
  isWeight_withDensity_one_sub_sq hw hsupp

end OrthogonalPolynomial

namespace Quadrature

open OrthogonalPolynomial

variable {μ : Measure ℝ}

/-! ### The Lobatto nodal polynomial -/

/-- **The Lobatto nodal polynomial** `ω̄ = (X² - 1) q_{n-1}`, with `q_{n-1}` the `(n-1)`-st monic
orthogonal polynomial of the modified weight `(1 - x²) μ`: monic of degree `n + 1`, vanishing at
`±1`, and `μ`-orthogonal to the polynomials of degree at most `n - 2`. Its roots are the
Gauss–Lobatto nodes of `μ`.

Reference: [quarteroni2000numerical] (10.17). -/
def lobattoNodal (μ : Measure ℝ) (n : ℕ) : ℝ[X] :=
  (X ^ 2 - 1) * family (lobattoMeasure μ) (n - 1)

theorem lobattoNodal_monic (μ : Measure ℝ) (n : ℕ) : (lobattoNodal μ n).Monic := by
  have h : (X ^ 2 - 1 : ℝ[X]).Monic := by
    have := monic_X_pow_sub_C (1 : ℝ) (two_ne_zero)
    rwa [C_1] at this
  exact h.mul (monic_family _ _)

theorem degree_lobattoNodal (μ : Measure ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (lobattoNodal μ n).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
  have h : (X ^ 2 - 1 : ℝ[X]).degree = 2 := by
    have := degree_X_pow_sub_C (two_pos) (1 : ℝ)
    rwa [C_1] at this
  rw [lobattoNodal, degree_mul, h, degree_family]
  norm_cast
  omega

theorem lobattoNodal_eval_one (μ : Measure ℝ) (n : ℕ) : (lobattoNodal μ n).eval 1 = 0 := by
  simp [lobattoNodal]

theorem lobattoNodal_eval_neg_one (μ : Measure ℝ) (n : ℕ) : (lobattoNodal μ n).eval (-1) = 0 := by
  simp [lobattoNodal]

/-- **The Lobatto nodal polynomial is orthogonal to the polynomials of degree at most `n - 2`**:
against `μ`, `ω̄ p = -(1 - x²) q_{n-1} p`, which is `-q_{n-1} p` against the modified weight, and
`q_{n-1}` is orthogonal to the polynomials of degree less than `n - 1`.

Reference: [quarteroni2000numerical] §10.2. -/
theorem integral_lobattoNodal_mul_of_degree_le (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0)
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ[X]} (hp : p.degree ≤ ((n - 2 : ℕ) : WithBot ℕ)) :
    ∫ t, (lobattoNodal μ n).eval t * p.eval t ∂μ = 0 := by
  have hw' := isWeight_lobattoMeasure hw hsupp
  have h := integral_family_mul_of_degree_lt hw' (n := n - 1) (q := p)
    (hp.trans_lt (by exact_mod_cast (by omega : n - 2 < n - 1)))
  rw [integral_lobattoMeasure hsupp] at h
  rw [← neg_eq_zero, ← integral_neg, ← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [lobattoNodal, eval_mul, eval_sub, eval_pow, eval_X, eval_one]
  ring

/-- **The textbook form of the Lobatto nodal polynomial**: `ω̄ = p_{n+1} + a p_n + b p_{n-1}` for
some reals `a`, `b`. The monic polynomial `ω̄ - p_{n+1}` of degree at most `n` expands in the
family, and its coefficients on `p_k` for `k ≤ n - 2` vanish by
`Quadrature.integral_lobattoNodal_mul_of_degree_le`.

Reference: [quarteroni2000numerical] (10.17). -/
theorem lobattoNodal_eq_add_smul (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) {n : ℕ}
    (hn : 1 ≤ n) :
    ∃ a b : ℝ, lobattoNodal μ n = family μ (n + 1) + C a * family μ n + C b * family μ (n - 1) := by
  have hdeg : (lobattoNodal μ n - family μ (n + 1)).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have := degree_sub_lt_left (p := lobattoNodal μ n) (q := family μ (n + 1))
      (by rw [degree_lobattoNodal μ hn, degree_family]) (lobattoNodal_monic μ n).ne_zero
      (by rw [(lobattoNodal_monic μ n).leadingCoeff, (monic_family μ (n + 1)).leadingCoeff])
    rwa [degree_lobattoNodal μ hn] at this
  have hexp := eq_sum_family hw hdeg
  -- the coefficients below `n - 1` vanish
  have hcoeff : ∀ k < n - 1,
      ∫ x, (lobattoNodal μ n - family μ (n + 1)).eval x * (family μ k).eval x ∂μ = 0 := by
    intro k hk
    have h1 : ∫ x, (lobattoNodal μ n).eval x * (family μ k).eval x ∂μ = 0 :=
      integral_lobattoNodal_mul_of_degree_le hw hsupp (by omega)
        (by rw [degree_family]; exact_mod_cast (by omega : k ≤ n - 2))
    have h2 : ∫ x, (family μ (n + 1)).eval x * (family μ k).eval x ∂μ = 0 :=
      integral_family_mul_family hw (by omega)
    have hev : ∀ x, (lobattoNodal μ n - family μ (n + 1)).eval x * (family μ k).eval x =
        (lobattoNodal μ n).eval x * (family μ k).eval x -
          (family μ (n + 1)).eval x * (family μ k).eval x := by
      intro x
      simp only [eval_sub]
      ring
    simp only [hev]
    rw [integral_sub (hw.integrable_eval_mul _ _) (hw.integrable_eval_mul _ _), h1, h2, sub_zero]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨(∫ x, (lobattoNodal μ (m + 1) - family μ (m + 1 + 1)).eval x *
      (family μ (m + 1)).eval x ∂μ) / normSq μ (m + 1),
    (∫ x, (lobattoNodal μ (m + 1) - family μ (m + 1 + 1)).eval x *
      (family μ m).eval x ∂μ) / normSq μ m, ?_⟩
  rw [Nat.add_sub_cancel]
  have hsplit : lobattoNodal μ (m + 1) = family μ (m + 1 + 1) +
      (lobattoNodal μ (m + 1) - family μ (m + 1 + 1)) := by ring
  conv_lhs => rw [hsplit, hexp]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero fun k hk => by
      rw [hcoeff k (by simpa using Finset.mem_range.mp hk), zero_div, zero_smul]]
  simp only [smul_eq_C_mul, zero_add]
  ring

/-- **Any combination `p_{n+1} + a p_n + b p_{n-1}` vanishing at `±1` is the Lobatto nodal
polynomial**, so the coefficients `a`, `b` of `Quadrature.lobattoNodal_eq_add_smul` are unique.
Such a combination is `(X² - 1) r` with `r` monic of degree `n - 1`, and `r` is orthogonal to the
polynomials of degree less than `n - 1` for the modified weight because the combination is
`μ`-orthogonal to them; so `r` is the `(n-1)`-st orthogonal polynomial of the modified weight.

Reference: [quarteroni2000numerical] (10.17). -/
theorem eq_lobattoNodal_of_eval_eq_zero (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0)
    {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (h1 : (family μ (n + 1) + C a * family μ n + C b * family μ (n - 1)).eval 1 = 0)
    (h2 : (family μ (n + 1) + C a * family μ n + C b * family μ (n - 1)).eval (-1) = 0) :
    family μ (n + 1) + C a * family μ n + C b * family μ (n - 1) = lobattoNodal μ n := by
  have hw' := isWeight_lobattoMeasure hw hsupp
  set g := family μ (n + 1) + C a * family μ n + C b * family μ (n - 1) with hg
  -- degree and leading coefficient of `g`
  have hlt : (C a * family μ n + C b * family μ (n - 1)).degree < (family μ (n + 1)).degree := by
    rw [degree_family]
    refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · refine (degree_mul_le _ _).trans_lt ?_
      rw [degree_family]
      calc (C a : ℝ[X]).degree + (n : WithBot ℕ) ≤ 0 + (n : WithBot ℕ) := by
            gcongr; exact degree_C_le
        _ < ((n + 1 : ℕ) : WithBot ℕ) := by
            rw [zero_add]; exact_mod_cast Nat.lt_succ_self n
    · refine (degree_mul_le _ _).trans_lt ?_
      rw [degree_family]
      calc (C b : ℝ[X]).degree + ((n - 1 : ℕ) : WithBot ℕ) ≤ 0 + ((n - 1 : ℕ) : WithBot ℕ) := by
            gcongr; exact degree_C_le
        _ < ((n + 1 : ℕ) : WithBot ℕ) := by
            rw [zero_add]; exact_mod_cast (by omega : n - 1 < n + 1)
  have hgdeg : g.degree = ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [hg, add_assoc, degree_add_eq_left_of_degree_lt hlt, degree_family]
  have hgmonic : g.Monic := by
    rw [Monic, hg, add_assoc, leadingCoeff_add_of_degree_lt' hlt]
    exact (monic_family μ (n + 1)).leadingCoeff
  -- `g` is orthogonal to the polynomials of degree `< n - 1`
  have hgorth : ∀ p : ℝ[X], p.degree < ((n - 1 : ℕ) : WithBot ℕ) →
      ∫ x, g.eval x * p.eval x ∂μ = 0 := by
    intro p hp
    have e1 := integral_family_mul_of_degree_lt hw (n := n + 1) (q := p)
      (hp.trans_le (by exact_mod_cast (by omega : n - 1 ≤ n + 1)))
    have e2 := integral_family_mul_of_degree_lt hw (n := n) (q := p)
      (hp.trans_le (by exact_mod_cast (by omega : n - 1 ≤ n)))
    have e3 := integral_family_mul_of_degree_lt hw (n := n - 1) (q := p) hp
    have hev : ∀ x, g.eval x * p.eval x = (family μ (n + 1)).eval x * p.eval x +
        a * ((family μ n).eval x * p.eval x) + b * ((family μ (n - 1)).eval x * p.eval x) := by
      intro x
      simp only [hg, eval_add, eval_mul, eval_C]
      ring
    simp only [hev]
    have i1 : Integrable (fun x => (family μ (n + 1)).eval x * p.eval x) μ :=
      hw.integrable_eval_mul _ _
    have i2 : Integrable (fun x => a * ((family μ n).eval x * p.eval x)) μ :=
      (hw.integrable_eval_mul _ _).const_mul _
    have i3 : Integrable (fun x => b * ((family μ (n - 1)).eval x * p.eval x)) μ :=
      (hw.integrable_eval_mul _ _).const_mul _
    have i12 : Integrable (fun x => (family μ (n + 1)).eval x * p.eval x +
        a * ((family μ n).eval x * p.eval x)) μ := i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      e1, e2, e3]
    ring
  -- `g = (X² - 1) r`
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : ℝ[X], g = (X - C 1) * r₁ :=
    ⟨_, (mul_divByMonic_eq_iff_isRoot.mpr h1).symm⟩
  have hr₁root : r₁.eval (-1) = 0 := by
    have h := h2
    rw [hr₁, eval_mul, eval_sub, eval_X, eval_C] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  obtain ⟨r, hr⟩ : ∃ r : ℝ[X], r₁ = (X - C (-1)) * r :=
    ⟨_, (mul_divByMonic_eq_iff_isRoot.mpr hr₁root).symm⟩
  have hgr : g = (X ^ 2 - 1) * r := by
    rw [hr₁, hr, C_neg, C_1]
    ring
  have hquad : (X ^ 2 - 1 : ℝ[X]).Monic := by
    have := monic_X_pow_sub_C (1 : ℝ) two_ne_zero
    rwa [C_1] at this
  have hquadnat : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by
    have := natDegree_X_pow_sub_C (n := 2) (r := (1 : ℝ))
    rwa [C_1] at this
  have hr0 : r ≠ 0 := fun h => hgmonic.ne_zero (by rw [hgr, h, mul_zero])
  have hrnat : r.natDegree = n - 1 := by
    have h := natDegree_eq_of_degree_eq_some hgdeg
    rw [hgr, natDegree_mul hquad.ne_zero hr0, hquadnat] at h
    omega
  have hrdeg : r.degree = ((n - 1 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hr0, hrnat]
  have hrmonic : r.Monic := by
    have h := hgmonic.leadingCoeff
    rwa [hgr, leadingCoeff_mul, hquad.leadingCoeff, one_mul] at h
  -- `r` is the `(n-1)`-st orthogonal polynomial of the modified weight
  have hr_eq : r = family (lobattoMeasure μ) (n - 1) := by
    refine sub_eq_zero.mp (eq_zero_of_degree_lt hw' (n := n - 1) ?_ ?_)
    · have := degree_sub_lt_left (p := r) (q := family (lobattoMeasure μ) (n - 1))
        (by rw [hrdeg, degree_family]) hr0
        (by rw [hrmonic.leadingCoeff, (monic_family _ _).leadingCoeff])
      rwa [hrdeg] at this
    · intro k hk
      have e1 : ∫ x, r.eval x * (family (lobattoMeasure μ) k).eval x ∂lobattoMeasure μ = 0 := by
        rw [integral_lobattoMeasure hsupp]
        have h := hgorth (family (lobattoMeasure μ) k) (by rw [degree_family]; exact_mod_cast hk)
        rw [← neg_eq_zero, ← integral_neg, ← h]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        rw [hgr]
        simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one]
        ring
      have e2 : ∫ x, (family (lobattoMeasure μ) (n - 1)).eval x *
          (family (lobattoMeasure μ) k).eval x ∂lobattoMeasure μ = 0 :=
        integral_family_mul_family hw' (by omega)
      have hev : ∀ x, (r - family (lobattoMeasure μ) (n - 1)).eval x *
          (family (lobattoMeasure μ) k).eval x =
          r.eval x * (family (lobattoMeasure μ) k).eval x -
            (family (lobattoMeasure μ) (n - 1)).eval x * (family (lobattoMeasure μ) k).eval x := by
        intro x
        simp only [eval_sub]
        ring
      simp only [hev]
      rw [integral_sub (hw'.integrable_eval_mul _ _) (hw'.integrable_eval_mul _ _), e1, e2,
        sub_zero]
  rw [hgr, hr_eq]
  rfl

/-- An interpolatory rule whose nodal polynomial is the Lobatto nodal polynomial has degree of
exactness `2n - 1`: Jacobi's theorem with `Quadrature.integral_lobattoNodal_mul_of_degree_le`. -/
theorem isExactOnMeasure_of_nodal_eq_lobattoNodal {n : ℕ} (hw : IsWeight μ)
    (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) (hn : 1 ≤ n) {x α : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (hint : IsInterpolatoryMeasure μ α x)
    (hnodal : Lagrange.nodal Finset.univ x = lobattoNodal μ n) :
    IsExactOnMeasure μ α x (2 * n - 1) := by
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    exact (isInterpolatoryMeasure_iff_isExactOnMeasure hw hx).mp hint
  · rw [show 2 * n - 1 = n + (n - 1) by omega, isExactOnMeasure_add_iff hw (by omega) hx α]
    refine ⟨hint, fun p hp => ?_⟩
    rw [hnodal]
    exact integral_lobattoNodal_mul_of_degree_le hw hsupp hn2
      (hp.trans (by exact_mod_cast (by omega : n - 1 - 1 ≤ n - 2)))

/-! ### Positivity of weights, and the weights through the Christoffel–Darboux kernel -/

/-- The Lagrange basis polynomial at a node, as the erased nodal polynomial divided by the
derivative of the nodal polynomial at the node. -/
private theorem basis_eq_C_mul_nodal_erase {n : ℕ} (x : Fin n → ℝ) (j : Fin n) :
    Lagrange.basis Finset.univ x j =
      C ((derivative (Lagrange.nodal Finset.univ x)).eval (x j))⁻¹ *
        Lagrange.nodal (Finset.univ.erase j) x := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ j),
    Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ j),
    ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ j)]

/-- **The weights of a rule whose nodal polynomial is `p_{n+2} + a p_{n+1} + b p_n`.** For an
interpolatory rule with `n + 2` distinct nodes whose nodal polynomial `ω` is that combination,
`p_{n+1}(x_j) ≠ 0` and `w_j = (‖p_{n+1}‖² - b ‖p_n‖²) / (p_{n+1}(x_j) ω'(x_j))`, provided the
numerator is nonzero. The Christoffel–Darboux identity at `t = x_j` gives
`p_{n+1}(x_j) ω / (X - x_j) = ‖p_{n+1}‖² K_{n+1}(x_j) - b ‖p_n‖² K_n(x_j)`, whose integral is
`‖p_{n+1}‖² - b ‖p_n‖²`, while `ω / (X - x_j)` is `ω'(x_j)` times the Lagrange basis polynomial.

This is the common source of the Gauss weights (`a = b = 0`) and of the Gauss–Lobatto weights.

Reference: Davis–Rabinowitz, *Methods of Numerical Integration*, §2.7. -/
theorem weight_eq_of_nodal_eq (hw : IsWeight μ) {n : ℕ} {x w : Fin (n + 2) → ℝ}
    (hx : Function.Injective x) (hint : IsInterpolatoryMeasure μ w x) {a b : ℝ}
    (hnodal : Lagrange.nodal Finset.univ x =
      family μ (n + 2) + C a * family μ (n + 1) + C b * family μ n)
    (hb : normSq μ (n + 1) - b * normSq μ n ≠ 0) (j : Fin (n + 2)) :
    (family μ (n + 1)).eval (x j) ≠ 0 ∧
      w j = (normSq μ (n + 1) - b * normSq μ n) /
        ((family μ (n + 1)).eval (x j) *
          (derivative (Lagrange.nodal Finset.univ x)).eval (x j)) := by
  set E := Lagrange.nodal (Finset.univ.erase j) x with hE
  have hωE : Lagrange.nodal Finset.univ x = (X - C (x j)) * E :=
    Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ j)
  have hω' : (derivative (Lagrange.nodal Finset.univ x)).eval (x j) = E.eval (x j) :=
    Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ j)
  have hω'ne : (derivative (Lagrange.nodal Finset.univ x)).eval (x j) ≠ 0 := by
    have h := Lagrange.nodalWeight_ne_zero hx.injOn (Finset.mem_univ j)
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ j)] at h
    intro h0
    exact h (by rw [h0, inv_zero])
  -- the root relation at `x j`
  have hroot : (family μ (n + 2)).eval (x j) + a * (family μ (n + 1)).eval (x j) +
      b * (family μ n).eval (x j) = 0 := by
    have h := Lagrange.eval_nodal_at_node (s := Finset.univ) (v := x) (Finset.mem_univ j)
    rw [hnodal] at h
    simpa [eval_add, eval_mul, eval_C] using h
  -- the key identity `p_{n+1}(x_j) E = h_{n+1} K_{n+1} - b h_n K_n`
  have hkey : C ((family μ (n + 1)).eval (x j)) * E =
      C (normSq μ (n + 1)) * cdKernel μ (n + 1) (x j) -
        C (b * normSq μ n) * cdKernel μ n (x j) := by
    refine mul_left_cancel₀ (X_sub_C_ne_zero (x j)) ?_
    have hCD1 := christoffel_darboux hw (n + 1) (x j)
    have hCD0 := christoffel_darboux hw n (x j)
    have hrootC : C ((family μ (n + 2)).eval (x j)) + C a * C ((family μ (n + 1)).eval (x j)) +
        C b * C ((family μ n).eval (x j)) = 0 := by
      rw [← C_mul, ← C_mul, ← C_add, ← C_add, hroot, C_0]
    have hω : (X - C (x j)) * E = family μ (n + 2) + C a * family μ (n + 1) + C b * family μ n :=
      hωE.symm.trans hnodal
    rw [C_mul]
    linear_combination C ((family μ (n + 1)).eval (x j)) * hω - hCD1 + C b * hCD0 +
      family μ (n + 1) * hrootC
  -- integrate the key identity
  have hintE : (family μ (n + 1)).eval (x j) * ∫ t, E.eval t ∂μ =
      normSq μ (n + 1) - b * normSq μ n := by
    have h := congrArg (fun q : ℝ[X] => ∫ t, q.eval t ∂μ) hkey
    simp only [eval_mul, eval_C, eval_sub] at h
    rw [integral_const_mul, integral_sub ((hw.integrable_eval _).const_mul _)
      ((hw.integrable_eval _).const_mul _), integral_const_mul, integral_const_mul,
      integral_eval_cdKernel hw, integral_eval_cdKernel hw, mul_one, mul_one] at h
    exact h
  have hpne : (family μ (n + 1)).eval (x j) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hintE
    exact hb hintE.symm
  refine ⟨hpne, ?_⟩
  rw [hint j, basis_eq_C_mul_nodal_erase x j]
  simp only [eval_mul, eval_C]
  rw [integral_const_mul, ← hE, ← hintE]
  field_simp

/-- **The Gauss weights through the Christoffel–Darboux kernel**: for the Gauss rule with `N + 1`
nodes — an interpolatory rule at the roots of `p_{N+1}` — the weights are
`w_j = ‖p_N‖² / (p_N(x_j) p_{N+1}'(x_j))`, and `p_N(x_j) ≠ 0`.

Reference: Davis–Rabinowitz, *Methods of Numerical Integration*, §2.7; [quarteroni2000numerical]
(10.32), (10.41), (10.42). -/
theorem gaussWeight_eq (hw : IsWeight μ) {N : ℕ} {x w : Fin (N + 1) → ℝ}
    (hx : Function.Injective x) (hint : IsInterpolatoryMeasure μ w x)
    (hnodal : Lagrange.nodal Finset.univ x = family μ (N + 1)) (j : Fin (N + 1)) :
    (family μ N).eval (x j) ≠ 0 ∧
      w j = normSq μ N /
        ((family μ N).eval (x j) * (derivative (family μ (N + 1))).eval (x j)) := by
  cases N with
  | zero =>
    have hj : j = 0 := Fin.ext (by omega)
    subst hj
    have h1 : family μ (0 + 1) = X - C (alpha μ 0) := family_one μ
    have hx0 : x 0 = alpha μ 0 := by
      have h := congrArg (fun p : ℝ[X] => p.eval (x 0)) hnodal
      simp only [Lagrange.eval_nodal_at_node (Finset.mem_univ (0 : Fin (0 + 1))), h1, eval_sub,
        eval_X, eval_C] at h
      linarith
    refine ⟨by simp, ?_⟩
    rw [hint 0, h1, derivative_sub, derivative_X, derivative_C, sub_zero, eval_one,
      family_zero, eval_one, one_mul, div_one, normSq, family_zero]
    simp
  | succ N =>
    have h := weight_eq_of_nodal_eq hw hx hint (a := 0) (b := 0)
      (by rw [hnodal, C_0, zero_mul, zero_mul, add_zero, add_zero]) (by
        rw [zero_mul, sub_zero]; exact normSq_ne_zero hw _) j
    rw [zero_mul, sub_zero, hnodal] at h
    exact h

/-! ### The Gauss–Lobatto rule -/

/-- **Gauss–Lobatto quadrature.** For a weight `μ` carried by `[-1, 1]` and `n ≥ 1` there are
`n + 1` distinct nodes in `[-1, 1]`, the first being `-1` and the last `1`, and positive weights,
such that the rule is exact on the polynomials of degree at most `2n - 1`; the nodal polynomial is
`Quadrature.lobattoNodal μ n` and the rule is interpolatory.

The interior nodes are the `n - 1` roots of the `(n-1)`-st orthogonal polynomial of the modified
weight `(1 - x²) μ`, which lie in `(-1, 1)`; exactness is Jacobi's theorem
`Quadrature.isExactOnMeasure_add_iff` with `Quadrature.integral_lobattoNodal_mul_of_degree_le`;
positivity of the weights is `Quadrature.pos_of_isExactOnMeasure` with the test polynomials
`(1 ∓ x) q²` at the endpoints and `(1 - x²) (q / (x - x̄_i))²` at the interior nodes.

Reference: [quarteroni2000numerical] (10.17)–(10.18). -/
theorem exists_gaussLobatto (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) {n : ℕ}
    (hn : 1 ≤ n) :
    ∃ x w : Fin (n + 1) → ℝ, Function.Injective x ∧ x 0 = -1 ∧ x (Fin.last n) = 1 ∧
      (∀ i, x i ∈ Icc (-1 : ℝ) 1) ∧ (∀ i, 0 < w i) ∧ IsExactOnMeasure μ w x (2 * n - 1) ∧
        Lagrange.nodal Finset.univ x = lobattoNodal μ n ∧ IsInterpolatoryMeasure μ w x := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hw' := isWeight_lobattoMeasure hw hsupp
  have hsupp' := lobattoMeasure_compl_Icc hsupp
  have hae : ∀ᵐ t ∂μ, t ∈ Icc (-1 : ℝ) 1 := by
    rw [ae_iff]
    exact hsupp
  -- the interior nodes
  obtain ⟨y, hyinj, hyprod⟩ := exists_injective_family_eq_prod hw' m
  have hymem : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i =>
    root_family_mem_Ioo hw' hsupp' (by
      rw [hyprod, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp))
  have hq : Lagrange.nodal Finset.univ y = family (lobattoMeasure μ) m := by
    rw [Lagrange.nodal_eq, hyprod]
  -- the nodes
  set x : Fin (m + 2) → ℝ := Fin.cons (-1) (Fin.snoc y 1) with hx
  have hx0 : x 0 = -1 := Fin.cons_zero _ _
  have hxlast : x (Fin.last (m + 1)) = 1 := by
    rw [hx, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]
  have hxint : ∀ i : Fin m, x (Fin.succ (Fin.castSucc i)) = y i := fun i => by
    rw [hx, Fin.cons_succ, Fin.snoc_castSucc]
  have hnodes : ∀ k : Fin (m + 2), x k = -1 ∨ x k = 1 ∨ ∃ i, x k = y i := by
    intro k
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
    · exact Or.inl hx0
    · rcases Fin.eq_castSucc_or_eq_last k' with ⟨i, rfl⟩ | rfl
      · exact Or.inr (Or.inr ⟨i, hxint i⟩)
      · exact Or.inr (Or.inl (by rw [Fin.succ_last]; exact hxlast))
  have hxmem : ∀ k, x k ∈ Icc (-1 : ℝ) 1 := by
    intro k
    rcases hnodes k with h | h | ⟨i, h⟩
    · rw [h]; exact ⟨le_rfl, by norm_num⟩
    · rw [h]; exact ⟨by norm_num, le_rfl⟩
    · rw [h]; exact Ioo_subset_Icc_self (hymem i)
  have hxinj : Function.Injective x := by
    rw [hx, Fin.cons_injective_iff, Fin.snoc_injective_iff]
    refine ⟨?_, hyinj, ?_⟩
    · rintro ⟨i, hi⟩
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [Fin.snoc_castSucc] at hi
        exact absurd hi (hymem j).1.ne'
      · rw [Fin.snoc_last] at hi
        norm_num at hi
    · rintro ⟨i, hi⟩
      exact absurd hi (hymem i).2.ne
  -- the nodal polynomial
  have hnodal : Lagrange.nodal Finset.univ x = lobattoNodal μ (m + 1) := by
    rw [Lagrange.nodal_eq, Fin.prod_univ_succ, Fin.prod_univ_castSucc, lobattoNodal,
      Nat.add_sub_cancel, hyprod]
    simp only [hx0, hxint, Fin.succ_last, hxlast, C_neg, C_1]
    ring
  -- the weights
  set w : Fin (m + 2) → ℝ := fun i => ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ with hw_def
  have hint : IsInterpolatoryMeasure μ w x := fun i => rfl
  -- exactness
  have hexact : IsExactOnMeasure μ w x (2 * (m + 1) - 1) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact (isInterpolatoryMeasure_iff_isExactOnMeasure hw hxinj).mp hint
    · rw [show 2 * (m + 1) - 1 = m + 1 + m by omega, isExactOnMeasure_add_iff hw hm hxinj]
      refine ⟨hint, fun p hp => ?_⟩
      rw [hnodal]
      exact integral_lobattoNodal_mul_of_degree_le hw hsupp (by omega)
        (hp.trans (by exact_mod_cast (by omega : m - 1 ≤ m + 1 - 2)))
  -- positivity of the weights
  have hqnat : (Lagrange.nodal Finset.univ y).natDegree = m := by
    rw [Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin]
  have hqy : ∀ i, (Lagrange.nodal Finset.univ y).eval (y i) = 0 := fun i =>
    Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  have hqne : ∀ t : ℝ, (∀ i, t ≠ y i) → (Lagrange.nodal Finset.univ y).eval t ≠ 0 := by
    intro t ht
    rw [Lagrange.eval_nodal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (ht i)
  have hdeg2 : (2 * (m + 1) - 1 : ℕ) = 2 * m + 1 := by omega
  have hpos : ∀ k, 0 < w k := by
    intro k
    rcases hnodes k with hk | hk | ⟨i, hk⟩
    · -- the node `-1`: test polynomial `(1 - X) q²`
      set p : ℝ[X] := (1 - X) * Lagrange.nodal Finset.univ y ^ 2 with hp
      have hval : 0 < p.eval (x k) := by
        rw [hp, hk]
        simp only [eval_mul, eval_sub, eval_one, eval_X, eval_pow]
        have := hqne (-1) fun i => (hymem i).1.ne
        positivity
      have hp0 : p ≠ 0 := fun h => by
        rw [h, eval_zero] at hval
        exact lt_irrefl _ hval
      refine pos_of_isExactOnMeasure hw hexact ?_ hp0 ?_ k ?_ hval
      · refine degree_le_of_natDegree_le ?_
        rw [hdeg2, hp]
        have h1 : (1 - X : ℝ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
        have h2 : (Lagrange.nodal Finset.univ y ^ 2).natDegree ≤ 2 * m :=
          natDegree_pow_le.trans (by rw [hqnat])
        exact natDegree_mul_le.trans (by omega)
      · filter_upwards [hae] with t ht
        simp only [hp, eval_mul, eval_sub, eval_one, eval_X, eval_pow]
        exact mul_nonneg (by linarith [ht.2]) (sq_nonneg _)
      · intro k' hk'
        have hne : x k' ≠ x k := fun h => hk' (hxinj h)
        rcases hnodes k' with h' | h' | ⟨j, h'⟩
        · exact absurd (h'.trans hk.symm) hne
        · rw [hp, h']; simp
        · rw [hp, h']; simp [hqy j]
    · -- the node `1`: test polynomial `(1 + X) q²`
      set p : ℝ[X] := (1 + X) * Lagrange.nodal Finset.univ y ^ 2 with hp
      have hval : 0 < p.eval (x k) := by
        rw [hp, hk]
        simp only [eval_mul, eval_add, eval_one, eval_X, eval_pow]
        have := hqne 1 fun i => (hymem i).2.ne'
        positivity
      have hp0 : p ≠ 0 := fun h => by
        rw [h, eval_zero] at hval
        exact lt_irrefl _ hval
      refine pos_of_isExactOnMeasure hw hexact ?_ hp0 ?_ k ?_ hval
      · refine degree_le_of_natDegree_le ?_
        rw [hdeg2, hp]
        have h1 : (1 + X : ℝ[X]).natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
        have h2 : (Lagrange.nodal Finset.univ y ^ 2).natDegree ≤ 2 * m :=
          natDegree_pow_le.trans (by rw [hqnat])
        exact natDegree_mul_le.trans (by omega)
      · filter_upwards [hae] with t ht
        simp only [hp, eval_mul, eval_add, eval_one, eval_X, eval_pow]
        exact mul_nonneg (by linarith [ht.1]) (sq_nonneg _)
      · intro k' hk'
        have hne : x k' ≠ x k := fun h => hk' (hxinj h)
        rcases hnodes k' with h' | h' | ⟨j, h'⟩
        · rw [hp, h']; simp
        · exact absurd (h'.trans hk.symm) hne
        · rw [hp, h']; simp [hqy j]
    · -- an interior node `y i`: test polynomial `(1 - X²) (q / (X - y i))²`
      set p : ℝ[X] := (1 - X ^ 2) * Lagrange.nodal (Finset.univ.erase i) y ^ 2 with hp
      have hEnat : (Lagrange.nodal (Finset.univ.erase i) y).natDegree = m - 1 := by
        rw [Lagrange.natDegree_nodal, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
      have hEval : (Lagrange.nodal (Finset.univ.erase i) y).eval (y i) ≠ 0 := by
        rw [Lagrange.eval_nodal]
        refine Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr fun h => ?_
        exact (Finset.mem_erase.mp hj).1 (hyinj h).symm
      have hval : 0 < p.eval (x k) := by
        rw [hp, hk]
        simp only [eval_mul, eval_sub, eval_one, eval_X, eval_pow]
        have h1 := (hymem i).1
        have h2 := (hymem i).2
        have hsq : 0 < 1 - y i ^ 2 := by nlinarith
        positivity
      have hp0 : p ≠ 0 := fun h => by
        rw [h, eval_zero] at hval
        exact lt_irrefl _ hval
      refine pos_of_isExactOnMeasure hw hexact ?_ hp0 ?_ k ?_ hval
      · refine degree_le_of_natDegree_le ?_
        rw [hdeg2, hp]
        refine natDegree_mul_le.trans ?_
        have h1 : (1 - X ^ 2 : ℝ[X]).natDegree ≤ 2 := (natDegree_sub_le _ _).trans (by simp)
        have h2 : (Lagrange.nodal (Finset.univ.erase i) y ^ 2).natDegree ≤ 2 * (m - 1) :=
          natDegree_pow_le.trans (by rw [hEnat])
        have hm : 1 ≤ m := Nat.succ_le_of_lt (Fin.pos i)
        omega
      · filter_upwards [hae] with t ht
        simp only [hp, eval_mul, eval_sub, eval_one, eval_X, eval_pow]
        exact mul_nonneg (by nlinarith [ht.1, ht.2]) (sq_nonneg _)
      · intro k' hk'
        have hne : x k' ≠ x k := fun h => hk' (hxinj h)
        rcases hnodes k' with h' | h' | ⟨j, h'⟩
        · rw [hp, h']; simp
        · rw [hp, h']; simp
        · have hji : j ≠ i := fun h => hne (by rw [h', hk, h])
          rw [hp, h']
          simp [Lagrange.eval_nodal_at_node (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)]
  exact ⟨x, w, hxinj, hx0, hxlast, hxmem, hpos, hexact, hnodal, hint⟩

/-! ### The classical Gauss weights -/

/-- **The Legendre–Gauss weights**: for the interpolatory rule at the `n + 1` zeros of `L_{n+1}`,
`w_j = 2 / ((1 - x_j²) L_{n+1}'(x_j)²)`. From `Quadrature.gaussWeight_eq`,
`w_j = 2 / ((n + 1) L_n(x_j) L_{n+1}'(x_j))`, and `(1 - x_j²) L_{n+1}'(x_j) = (n + 1) L_n(x_j)` at a
root of `L_{n+1}` by the Legendre differential identities.

Reference: [quarteroni2000numerical] (10.32). -/
theorem legendreGaussWeight_eq {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hint : IsInterpolatoryMeasure legendreMeasure w x)
    (hroot : ∀ j, (Polynomial.legendre (n + 1)).eval (x j) = 0) (j : Fin (n + 1)) :
    w j = 2 / ((1 - x j ^ 2) * (derivative (Polynomial.legendre (n + 1))).eval (x j) ^ 2) := by
  have hroot' : ∀ j, (family legendreMeasure (n + 1)).eval (x j) = 0 := fun j => by
    rw [family_eq_legendre, eval_mul, hroot j, mul_zero]
  obtain ⟨hpne, hw⟩ := gaussWeight_eq isWeight_legendreMeasure hx hint
    (nodal_eq_family_of_forall_eval_eq_zero _ hx hroot') j
  have hlc1 := leadingCoeff_legendre_succ n
  have hlcn : (Polynomial.legendre n).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero n)
  rw [family_eq_legendre, eval_mul, eval_C] at hpne
  have hLn : (Polynomial.legendre n).eval (x j) ≠ 0 := fun h => hpne (by rw [h, mul_zero])
  -- the identity `(1 - x_j²) L_{n+1}'(x_j) = (n + 1) L_n(x_j)` at a root of `L_{n+1}`
  have hid : (1 - x j ^ 2) * (derivative (Polynomial.legendre (n + 1))).eval (x j) =
      ((n : ℝ) + 1) * (Polynomial.legendre n).eval (x j) := by
    have h1 := congrArg (fun p : ℝ[X] => p.eval (x j))
      (Polynomial.quad_mul_derivative_legendre (n + 1))
    have h2 := congrArg (fun p : ℝ[X] => p.eval (x j)) (Polynomial.legendre_recurrence n)
    simp only [eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_one, eval_natCast, eval_ofNat,
      hroot j] at h1 h2
    push_cast at h1 h2
    linear_combination -h1 - h2
  have hL' : (derivative (Polynomial.legendre (n + 1))).eval (x j) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hid
    exact hLn (by
      have := hid.symm
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by positivity)
      · exact h)
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2n : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hR : (1 - x j ^ 2) * (derivative (Polynomial.legendre (n + 1))).eval (x j) ^ 2 =
      ((n : ℝ) + 1) * (Polynomial.legendre n).eval (x j) *
        (derivative (Polynomial.legendre (n + 1))).eval (x j) := by
    rw [pow_two ((derivative (Polynomial.legendre (n + 1))).eval (x j)), ← mul_assoc, hid]
  rw [hw, normSq_legendreMeasure, family_eq_legendre, family_eq_legendre, derivative_C_mul,
    eval_mul, eval_mul, eval_C, eval_C, hlc1, hR]
  field_simp

/-- **The Gauss–Laguerre weights**: for the interpolatory rule at the `n + 1` zeros of `ℒ_{n+1}`,
`w_k = ((n + 1)!)² x_k / ℒ_{n+2}(x_k)²`. From `Quadrature.gaussWeight_eq`,
`w_k = -(n!)² / (ℒ_n(x_k) ℒ_{n+1}'(x_k))`, and at a root of `ℒ_{n+1}` both `x_k ℒ_{n+1}'(x_k)` and
`ℒ_{n+2}(x_k)` equal `-(n + 1)² ℒ_n(x_k)`.

Reference: [quarteroni2000numerical] (10.41) (with `n + 1` nodes in place of `n`). -/
theorem laguerreGaussWeight_eq {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hint : IsInterpolatoryMeasure laguerreMeasure w x)
    (hroot : ∀ k, (Polynomial.laguerre (n + 1)).eval (x k) = 0) (k : Fin (n + 1)) :
    w k = ((n + 1) ! : ℝ) ^ 2 * x k / (Polynomial.laguerre (n + 2)).eval (x k) ^ 2 := by
  have hroot' : ∀ k, (family laguerreMeasure (n + 1)).eval (x k) = 0 := fun k => by
    rw [family_laguerreMeasure_eq, eval_mul, hroot k, mul_zero]
  obtain ⟨hpne, hw⟩ := gaussWeight_eq isWeight_laguerreMeasure hx hint
    (nodal_eq_family_of_forall_eval_eq_zero _ hx hroot') k
  rw [family_laguerreMeasure_eq, eval_mul, eval_C] at hpne
  have hLn : (Polynomial.laguerre n).eval (x k) ≠ 0 := fun h => hpne (by rw [h, mul_zero])
  have hxk : x k ≠ 0 := by
    intro h
    have := hroot k
    rw [h, Polynomial.laguerre_eval_zero] at this
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _) this
  -- the two identities at a root of `ℒ_{n+1}`
  have hA : x k * (derivative (Polynomial.laguerre (n + 1))).eval (x k) =
      -(((n : ℝ) + 1) ^ 2) * (Polynomial.laguerre n).eval (x k) := by
    have h := congrArg (fun p : ℝ[X] => p.eval (x k)) (Polynomial.X_mul_derivative_laguerre_succ n)
    simp only [eval_mul, eval_sub, eval_X, eval_C, hroot k] at h
    linear_combination h
  have hB : (Polynomial.laguerre (n + 2)).eval (x k) =
      -(((n : ℝ) + 1) ^ 2) * (Polynomial.laguerre n).eval (x k) := by
    have h := congrArg (fun p : ℝ[X] => p.eval (x k)) (Polynomial.laguerre_succ_succ n)
    simp only [eval_mul, eval_sub, eval_X, eval_C, hroot k] at h
    linear_combination h
  have hL' : (derivative (Polynomial.laguerre (n + 1))).eval (x k) =
      -(((n : ℝ) + 1) ^ 2) * (Polynomial.laguerre n).eval (x k) / x k := by
    rw [← hA]
    field_simp
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hprod : (-1 : ℝ) ^ n * (-1) ^ (n + 1) = -1 := by
    rw [← pow_add, show n + (n + 1) = 2 * n + 1 by ring, pow_succ, pow_mul]
    simp
  rw [hw, normSq_laguerreMeasure, family_laguerreMeasure_eq, family_laguerreMeasure_eq,
    derivative_C_mul, eval_mul, eval_mul, eval_C, eval_C,
    show (-1 : ℝ) ^ n * (Polynomial.laguerre n).eval (x k) *
      ((-1) ^ (n + 1) * (derivative (Polynomial.laguerre (n + 1))).eval (x k)) =
      ((-1 : ℝ) ^ n * (-1) ^ (n + 1)) * ((Polynomial.laguerre n).eval (x k) *
        (derivative (Polynomial.laguerre (n + 1))).eval (x k)) by ring, hprod, hL', hB,
    Nat.factorial_succ]
  push_cast
  field_simp

/-- **The Gauss–Hermite weights**: for the interpolatory rule at the `n + 1` zeros of `H_{n+1}`,
`w_k = 2^{n+2} (n + 1)! √π / H_{n+2}(x_k)²`. From `Quadrature.gaussWeight_eq`,
`w_k = 2^{n+1} n! √π / (H_n(x_k) H_{n+1}'(x_k))`, with `H_{n+1}' = 2(n + 1) H_n` and
`H_{n+2}(x_k) = -2(n + 1) H_n(x_k)` at a root of `H_{n+1}`.

Reference: [quarteroni2000numerical] (10.42) (with `n + 1` nodes in place of `n`). -/
theorem hermiteGaussWeight_eq {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hint : IsInterpolatoryMeasure hermiteMeasure w x)
    (hroot : ∀ k, (Polynomial.physHermite (n + 1)).eval (x k) = 0) (k : Fin (n + 1)) :
    w k = 2 ^ (n + 2) * ((n + 1) ! : ℝ) * √π / (Polynomial.physHermite (n + 2)).eval (x k) ^ 2 := by
  have hroot' : ∀ k, (family hermiteMeasure (n + 1)).eval (x k) = 0 := fun k => by
    rw [family_hermiteMeasure_eq, eval_mul, hroot k, mul_zero]
  obtain ⟨hpne, hw⟩ := gaussWeight_eq isWeight_hermiteMeasure hx hint
    (nodal_eq_family_of_forall_eval_eq_zero _ hx hroot') k
  rw [family_hermiteMeasure_eq, eval_mul, eval_C] at hpne
  have hHn : (Polynomial.physHermite n).eval (x k) ≠ 0 := fun h => hpne (by rw [h, mul_zero])
  have hB : (Polynomial.physHermite (n + 2)).eval (x k) =
      -(2 * ((n : ℝ) + 1)) * (Polynomial.physHermite n).eval (x k) := by
    have h := congrArg (fun p : ℝ[X] => p.eval (x k)) (Polynomial.physHermite_succ_succ n)
    simp only [eval_mul, eval_sub, eval_X, eval_C, eval_ofNat, hroot k] at h
    linear_combination h
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  rw [hw, normSq_hermiteMeasure, family_hermiteMeasure_eq, family_hermiteMeasure_eq,
    derivative_C_mul, Polynomial.derivative_physHermite_succ, eval_mul, eval_mul, eval_mul, eval_C,
    eval_C, eval_C, hB, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end Quadrature

/-! ### The Chebyshev–Gauss–Lobatto rule -/

namespace Polynomial.Chebyshev

open Quadrature

variable {n : ℕ}

/-- The factor `d_j` of the Chebyshev–Gauss–Lobatto rule: `2` at the endpoints `j = 0` and `j = n`,
`1` at the interior nodes.

Reference: [quarteroni2000numerical] (10.21). -/
def lobattoFactor (n j : ℕ) : ℝ := if j = 0 ∨ j = n then 2 else 1

theorem lobattoFactor_pos (n j : ℕ) : 0 < lobattoFactor n j := by
  unfold lobattoFactor
  split_ifs <;> norm_num

theorem lobattoFactor_of_ne {n j : ℕ} (h0 : j ≠ 0) (hn : j ≠ n) : lobattoFactor n j = 1 := by
  rw [lobattoFactor, ite_eq_right (not_or.mpr ⟨h0, hn⟩)]

/-- The Chebyshev–Gauss–Lobatto weights `π / (d_j n)`, with `d_0 = d_n = 2` and `d_j = 1` at the
interior nodes.

Reference: [quarteroni2000numerical] (10.21). -/
def lobattoWeight (n j : ℕ) : ℝ := π / (lobattoFactor n j * n)

theorem lobattoWeight_pos {n : ℕ} (hn : n ≠ 0) (j : ℕ) : 0 < lobattoWeight n j :=
  div_pos pi_pos (mul_pos (lobattoFactor_pos n j) (by positivity))

/-- The Chebyshev–Gauss–Lobatto sum `∑_{j ≤ n} (π / (d_j n)) P(cos (jπ/n))` over the extrema
`Polynomial.Chebyshev.node n j` of `T_n`, the companion of Mathlib's
`Polynomial.Chebyshev.sumZeroes`.

Reference: [quarteroni2000numerical] (10.21). -/
def sumExtrema (n : ℕ) (P : ℝ[X]) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), lobattoWeight n j * P.eval (node n j)

theorem sumExtrema_sum (n : ℕ) {ι : Type*} (s : Finset ι) (P : ι → ℝ[X]) :
    sumExtrema n (∑ i ∈ s, P i) = ∑ i ∈ s, sumExtrema n (P i) := by
  simp only [sumExtrema, eval_finsetSum, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem sumExtrema_smul (n : ℕ) (c : ℝ) (P : ℝ[X]) : sumExtrema n (c • P) = c * sumExtrema n P := by
  simp only [sumExtrema, eval_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The nodes are symmetric under `j ↦ 2n - j`. -/
theorem node_two_mul_sub {n j : ℕ} (hj : j ≤ 2 * n) : node n (2 * n - j) = node n j := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [node]
  rw [node, node, Nat.cast_sub hj]
  push_cast
  rw [show (2 * (n : ℝ) - j) * π / n = 2 * π - j * π / n by field_simp, cos_two_pi_sub]

/-- **The Lobatto sum is a trapezoidal sum over a full period**: the endpoint half-weights are the
two halves of the periodic trapezoidal rule, and the interior nodes appear twice in a period. -/
theorem sumExtrema_eq_sum_range (hn : n ≠ 0) (P : ℝ[X]) :
    sumExtrema n P = π / (2 * n) * ∑ j ∈ Finset.range (2 * n), P.eval (node n j) := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  set g : ℕ → ℝ := fun j => P.eval (node n j) with hg
  -- the full period splits into `[0, n]` and `(n, 2n)`, the second half mirroring `(0, n)`
  have hsplit : ∑ j ∈ Finset.range (2 * n), g j =
      ∑ j ∈ Finset.range (n + 1), g j + ∑ j ∈ Finset.Ico 1 n, g j := by
    rw [← Finset.sum_range_add_sum_Ico g (show n + 1 ≤ 2 * n by omega)]
    congr 1
    have := Finset.sum_Ico_reflect g 1 (n := 2 * n) (m := n) (by omega)
    rw [show 2 * n + 1 - n = n + 1 by omega, show 2 * n + 1 - 1 = 2 * n by omega] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    simp only [hg, node_two_mul_sub (by omega : j ≤ 2 * n)]
  have hmid : ∑ j ∈ Finset.range (n + 1), g j = g 0 + ∑ j ∈ Finset.Ico 1 n, g j + g n := by
    rw [Finset.sum_range_succ, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < n)]
  have hmidw : sumExtrema n P = lobattoWeight n 0 * g 0 +
      ∑ j ∈ Finset.Ico 1 n, lobattoWeight n j * g j + lobattoWeight n n * g n := by
    rw [sumExtrema, Finset.sum_range_succ, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < n)]
  have hint : ∑ j ∈ Finset.Ico 1 n, lobattoWeight n j * g j =
      π / n * ∑ j ∈ Finset.Ico 1 n, g j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    rw [lobattoWeight, lobattoFactor_of_ne (by omega) (by omega), one_mul]
  have hw0 : lobattoWeight n 0 = π / (2 * n) := by simp [lobattoWeight, lobattoFactor]
  have hwn : lobattoWeight n n = π / (2 * n) := by simp [lobattoWeight, lobattoFactor]
  rw [hmidw, hint, hw0, hwn, hsplit, hmid]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  ring

/-- The Lobatto sum of `T_0` is `π`. -/
theorem sumExtrema_T_zero (hn : n ≠ 0) : sumExtrema n (T ℝ 0) = π := by
  rw [sumExtrema_eq_sum_range hn]
  simp only [T_zero, eval_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp

/-- The Lobatto sum of `T_k` vanishes for `0 < k < 2n`: over a full period it is the real part of
a sum of `2n`-th roots of unity (`Quadrature.sum_exp_angleNode`). -/
theorem sumExtrema_T_of_pos_of_lt (hn : n ≠ 0) {k : ℕ} (hk0 : 0 < k) (hk : k < 2 * n) :
    sumExtrema n (T ℝ k) = 0 := by
  rw [sumExtrema_eq_sum_range hn]
  refine mul_eq_zero_of_right _ ?_
  have hcos : ∀ j : ℕ, (T ℝ k).eval (node n j) = Real.cos ((k : ℤ) * angleNode (2 * n) j) := by
    intro j
    rw [node, T_real_cos, angleNode]
    congr 1
    push_cast
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  simp only [hcos]
  have h := sum_exp_angleNode (N := 2 * n) (by omega) (k : ℤ)
  have hndvd : ¬ ((2 * n : ℕ) : ℤ) ∣ (k : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    intro hdvd
    exact absurd (Nat.le_of_dvd hk0 hdvd) (not_le.mpr hk)
  rw [Nat.cast_mul, Nat.cast_ofNat] at h
  rw [ite_eq_right (by exact_mod_cast hndvd)] at h
  have hre := congrArg Complex.re h
  rw [Complex.re_sum, Complex.zero_re] at hre
  rw [← hre]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.exp_ofReal_mul_I_re]
  push_cast
  ring_nf

/-- **Chebyshev–Gauss–Lobatto quadrature**: for `n ≠ 0` the rule with the `n + 1` extrema
`cos (jπ/n)` of `T_n` and the weights `π / (d_j n)` integrates every polynomial of degree less than
`2n` exactly against the Chebyshev weight. By linearity it suffices to treat `T_k` for `k < 2n`,
where both sides are `π` for `k = 0` and `0` otherwise.

Reference: [quarteroni2000numerical] (10.21). -/
theorem integral_eq_sumExtrema {n : ℕ} {P : ℝ[X]} (hn : n ≠ 0) (hP : P.degree < 2 * n) :
    ∫ x, P.eval x ∂measureT = sumExtrema n P := by
  have hmem : P ∈ degreeLT ℝ (2 * n) := by rwa [mem_degreeLT]
  rw [← Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio (2 * n) = Finset.range (2 * n) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  simp_rw [eval_finsetSum, eval_smul]
  rw [MeasureTheory.integral_finsetSum, sumExtrema_sum]
  · simp_rw [sumExtrema_smul, smul_eq_mul, MeasureTheory.integral_const_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [chebyshevTsequence]
    rcases eq_or_ne i 0 with rfl | hi0
    · rw [Nat.cast_zero, integral_eval_T_real_measureT_zero, sumExtrema_T_zero hn]
    · rw [integral_eval_T_real_measureT_of_ne_zero (by exact_mod_cast hi0),
        sumExtrema_T_of_pos_of_lt hn (Nat.pos_of_ne_zero hi0) (Finset.mem_range.mp hi)]
  · simp_rw [← eval_smul]
    exact fun i _ => integrable_measureT (by fun_prop)

/-- The Chebyshev–Gauss–Lobatto rule as an exactness statement about the measure
`OrthogonalPolynomial.chebyshevMeasure`, with `Fin`-indexed nodes and weights. -/
theorem isExactOnMeasure_lobattoWeight_node (hn : n ≠ 0) :
    IsExactOnMeasure OrthogonalPolynomial.chebyshevMeasure
      (fun j : Fin (n + 1) => lobattoWeight n j) (fun j : Fin (n + 1) => node n j) (2 * n - 1) := by
  intro P hP
  rw [integral_eq_sumExtrema hn (hP.trans_lt (by exact_mod_cast (by omega : 2 * n - 1 < 2 * n))),
    sumExtrema, ← Fin.sum_univ_eq_sum_range (fun j => lobattoWeight n j * P.eval (node n j))]

/-- The nodes `cos (jπ/n)`, `j ≤ n`, are distinct. -/
theorem injective_node (n : ℕ) : Function.Injective fun j : Fin (n + 1) => node n j := by
  intro i j hij
  have hi : (i : ℕ) ∈ (↑(Finset.range (n + 1)) : Set ℕ) := by
    simp only [Finset.coe_range, mem_Iio]
    exact i.is_lt
  have hj : (j : ℕ) ∈ (↑(Finset.range (n + 1)) : Set ℕ) := by
    simp only [Finset.coe_range, mem_Iio]
    exact j.is_lt
  exact Fin.ext ((strictAntiOn_node n).injOn hi hj hij)

/-- **The discrete norms of the Chebyshev polynomials for the Gauss–Lobatto rule**: with
`(f, g)_n = ∑_j (π / (d_j n)) f(x̄_j) g(x̄_j)`, the `T_k` for `k ≤ n` are orthogonal, with
`(T_k, T_k)_n = π` for `k = 0` or `k = n` and `π / 2` for `0 < k < n`. Below the degree of exactness
this is the continuous inner product; at `k = n` it is the direct sum `∑_j (π / (d_j n)) = π`, twice
the continuous norm `π / 2` (the hint of [quarteroni2000numerical] Exercise 10.2).

Reference: [quarteroni2000numerical] §10.3. -/
theorem discreteInner_T_T (hn : n ≠ 0) {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n) :
    discreteInner (fun j : Fin (n + 1) => lobattoWeight n j) (fun j : Fin (n + 1) => node n j)
        (fun t => (T ℝ k).eval t) (fun t => (T ℝ l).eval t) =
      if k = l then (if k = 0 ∨ k = n then π else π / 2) else 0 := by
  have hsum : discreteInner (fun j : Fin (n + 1) => lobattoWeight n j)
      (fun j : Fin (n + 1) => node n j) (fun t => (T ℝ k).eval t) (fun t => (T ℝ l).eval t) =
      sumExtrema n (T ℝ k * T ℝ l) := by
    rw [discreteInner, sumExtrema,
      ← Fin.sum_univ_eq_sum_range (fun j => lobattoWeight n j * (T ℝ k * T ℝ l).eval (node n j))]
    exact Finset.sum_congr rfl fun j _ => by rw [eval_mul, mul_assoc]
  have hdeg : (T ℝ k * T ℝ l).degree = ((k + l : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_T, degree_T]
    simp
  rw [hsum]
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl]
    by_cases hkn : k = n
    · subst hkn
      rw [ite_eq_left (Or.inr rfl), sumExtrema, ← sumExtrema_T_zero hn, sumExtrema]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [eval_mul, eval_T_real_node (Finset.mem_Iic.mpr (Finset.mem_range_succ_iff.mp hj)),
        T_zero, eval_one]
      rw [← mul_pow]
      norm_num
    · rw [← integral_eq_sumExtrema hn (by rw [hdeg]; exact_mod_cast (by omega : k + k < 2 * n))]
      simp only [eval_mul]
      rcases eq_or_ne k 0 with rfl | hk0
      · rw [ite_eq_left (Or.inl rfl)]
        exact integral_eval_T_real_mul_self_measureT_zero
      · rw [ite_eq_right (not_or.mpr ⟨hk0, hkn⟩)]
        exact integral_T_real_mul_self_measureT_of_ne_zero hk0
  · rw [ite_eq_right hkl,
      ← integral_eq_sumExtrema hn (by rw [hdeg]; exact_mod_cast (by omega : k + l < 2 * n))]
    simp only [eval_mul]
    exact integral_eval_T_real_mul_eval_T_real_measureT_of_ne hkl

/-- **The Chebyshev discrete transform.** The interpolant of `f` at the Chebyshev–Gauss–Lobatto
nodes `x̄_j = cos (jπ/n)` is `∑_{k ≤ n} f̃_k T_k` with
`f̃_k = (2 / (n d_k)) ∑_{j ≤ n} d_j⁻¹ cos (kjπ/n) f(x̄_j)`: it is the discrete truncation
`Quadrature.interpolate_eq_sum_discreteInner_smul` of the Chebyshev expansion, with the discrete
norms `Polynomial.Chebyshev.discreteInner_T_T` and `T_k(x̄_j) = cos (kjπ/n)`.

Reference: [quarteroni2000numerical] (10.29)–(10.31), Exercise 10.2. -/
theorem interpolate_eq_sum_cdt (hn : n ≠ 0) (f : ℝ → ℝ) :
    Lagrange.interpolate Finset.univ (fun j : Fin (n + 1) => node n j) (fun j => f (node n j)) =
      ∑ k ∈ Finset.range (n + 1),
        Polynomial.C (2 / (n * lobattoFactor n k) * ∑ j ∈ Finset.range (n + 1),
          (lobattoFactor n j)⁻¹ * Real.cos ((k : ℝ) * (j : ℝ) * π / n) * f (node n j)) * T ℝ k := by
  have hw := OrthogonalPolynomial.isWeight_chebyshevMeasure
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [interpolate_eq_sum_discreteInner_smul hw hn1 (injective_node n)
    (fun i => lobattoWeight_pos hn i) (isExactOnMeasure_lobattoWeight_node hn) f,
    ← Fin.sum_univ_eq_sum_range (fun k => Polynomial.C (2 / (n * lobattoFactor n k) *
      ∑ j ∈ Finset.range (n + 1), (lobattoFactor n j)⁻¹ * Real.cos ((k : ℝ) * (j : ℝ) * π / n) *
        f (node n j)) * T ℝ k) (n + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.2
  set c : ℝ := ((2 : ℝ) ^ ((k : ℕ) - 1))⁻¹ with hc
  have hc0 : c ≠ 0 := by positivity
  rw [OrthogonalPolynomial.family_chebyshevMeasure_eq]
  have e1 : discreteInner (fun j : Fin (n + 1) => lobattoWeight n j) (fun j => node n j) f
      (fun t => (Polynomial.C c * T ℝ k).eval t) =
      c * discreteInner (fun j : Fin (n + 1) => lobattoWeight n j) (fun j => node n j) f
        (fun t => (T ℝ k).eval t) := by
    simp only [discreteInner, eval_mul, eval_C, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : discreteInner (fun j : Fin (n + 1) => lobattoWeight n j) (fun j => node n j)
      (fun t => (Polynomial.C c * T ℝ k).eval t) (fun t => (Polynomial.C c * T ℝ k).eval t) =
      c ^ 2 * discreteInner (fun j : Fin (n + 1) => lobattoWeight n j) (fun j => node n j)
        (fun t => (T ℝ k).eval t) (fun t => (T ℝ k).eval t) := by
    simp only [discreteInner, eval_mul, eval_C, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hv := discreteInner_T_T hn hk hk
  rw [ite_eq_left rfl] at hv
  have hvd : discreteInner (fun j : Fin (n + 1) => lobattoWeight n j) (fun j => node n j)
      (fun t => (T ℝ k).eval t) (fun t => (T ℝ k).eval t) = π * lobattoFactor n k / 2 := by
    rw [hv, lobattoFactor]
    split_ifs <;> ring
  have hf : discreteInner (fun j : Fin (n + 1) => lobattoWeight n j) (fun j => node n j) f
      (fun t => (T ℝ k).eval t) = π / n * ∑ j ∈ Finset.range (n + 1),
        (lobattoFactor n j)⁻¹ * Real.cos ((k : ℝ) * (j : ℝ) * π / n) * f (node n j) := by
    rw [discreteInner, Finset.mul_sum,
      ← Fin.sum_univ_eq_sum_range (fun j => π / n * ((lobattoFactor n j)⁻¹ *
        Real.cos ((k : ℝ) * (j : ℝ) * π / n) * f (node n j))) (n + 1)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hd := lobattoFactor_pos n j
    rw [lobattoWeight, node, T_real_cos]
    push_cast
    rw [show ((k : ℕ) : ℝ) * ((j : ℕ) * π / n) = (k : ℝ) * (j : ℝ) * π / n by ring]
    field_simp
  rw [e1, e2, hvd, hf, ← mul_assoc, ← Polynomial.C_mul]
  congr 2
  have hd := lobattoFactor_pos n k
  generalize (∑ j ∈ Finset.range (n + 1),
    (lobattoFactor n j)⁻¹ * Real.cos ((k : ℝ) * (j : ℝ) * π / n) * f (node n j)) = S
  rw [hc]
  field_simp

end Polynomial.Chebyshev

namespace Quadrature

open OrthogonalPolynomial

/-! ### The derivative of a Jacobi polynomial -/

/-- The integration by parts behind Remark 10.2 of [quarteroni2000numerical]: for `p` of degree
less than `n - 1`, `∫ (J_n^{(α,β)})' p (1-x)^{α+1} (1+x)^{β+1} dx = 0`, because it is
`-∫ J_n^{(α,β)} [p (1-x)^{α+1} (1+x)^{β+1}]' dx`, the boundary terms vanishing as
`α + 1, β + 1 > 0`, and the derivative in the bracket is `(1-x)^α (1+x)^β` times a polynomial of
degree less than `n`. -/
private theorem integral_derivative_family_jacobiMeasure_mul {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    {n : ℕ} {p : ℝ[X]} (hp : p.degree < ((n - 1 : ℕ) : WithBot ℕ)) :
    ∫ x, (derivative (family (jacobiMeasure α β) n)).eval x * p.eval x
      ∂jacobiMeasure (α + 1) (β + 1) = 0 := by
  have hw := isWeight_jacobiMeasure hα hβ
  have hα1 : 0 < α + 1 := by linarith
  have hβ1 : 0 < β + 1 := by linarith
  set J := family (jacobiMeasure α β) n with hJ
  set r : ℝ[X] := (1 - X ^ 2) * derivative p +
    p * (C (β + 1) * (1 - X) - C (α + 1) * (1 + X)) with hr
  -- the degree of the bracket polynomial
  have hrdeg : r.degree < n := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · -- `n ≤ 1`: `p = 0`
      have hp0 : p = 0 := by
        have : p.degree < 0 := by
          refine hp.trans_le ?_
          have : n - 1 = 0 := by omega
          rw [this]
          exact le_rfl
        exact degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp this)
      rw [hr, hp0]
      simp
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have hpnat : p.natDegree ≤ m := by
        rcases eq_or_ne p 0 with rfl | hp0
        · simp
        · have := (natDegree_lt_iff_degree_lt hp0).mpr hp
          omega
      refine lt_of_le_of_lt (degree_le_natDegree) ?_
      have h1 : ((1 - X ^ 2) * derivative p).natDegree ≤ m + 1 := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · have : derivative p = 0 := by
            rw [derivative_eq_zero]
            omega
          rw [this, mul_zero, natDegree_zero]
          exact Nat.zero_le _
        · refine natDegree_mul_le.trans ?_
          have ha : (1 - X ^ 2 : ℝ[X]).natDegree ≤ 2 := (natDegree_sub_le _ _).trans (by simp)
          have hb : (derivative p).natDegree ≤ m - 1 :=
            (natDegree_derivative_le p).trans (by omega)
          omega
      have h2 : (p * (C (β + 1) * (1 - X) - C (α + 1) * (1 + X))).natDegree ≤ m + 1 := by
        refine natDegree_mul_le.trans ?_
        have hb : (C (β + 1) * (1 - X) - C (α + 1) * (1 + X) : ℝ[X]).natDegree ≤ 1 := by
          refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
          · exact (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (by simp))
          · exact (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
        omega
      have := (natDegree_add_le _ _).trans (max_le h1 h2)
      exact_mod_cast Nat.lt_of_le_of_lt this (by omega)
  -- the function whose derivative is integrated
  set F : ℝ → ℝ := fun x => J.eval x * p.eval x * ((1 - x) ^ (α + 1) * (1 + x) ^ (β + 1)) with hF
  set F' : ℝ → ℝ := fun x => (1 - x) ^ α * (1 + x) ^ β *
    ((derivative J).eval x * p.eval x * (1 - x ^ 2) + J.eval x * r.eval x) with hF'
  have hderiv : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt F (F' x) x := by
    intro x hx
    have h1x : 1 - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx.2)
    have h1x' : 1 + x ≠ 0 := by linarith [hx.1]
    have hd0 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := (hasDerivAt_id x).const_sub 1
    have hd0' : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
    have hd1 : HasDerivAt (fun y : ℝ => (1 - y) ^ (α + 1))
        (-1 * (α + 1) * (1 - x) ^ (α + 1 - 1)) x := hd0.rpow_const (Or.inl h1x)
    have hd2 : HasDerivAt (fun y : ℝ => (1 + y) ^ (β + 1))
        (1 * (β + 1) * (1 + x) ^ (β + 1 - 1)) x := hd0'.rpow_const (Or.inl h1x')
    have := ((J.hasDerivAt x).mul (p.hasDerivAt x)).mul (hd1.mul hd2)
    refine this.congr_deriv ?_
    simp only [hF', hr, Pi.mul_apply, add_sub_cancel_right, eval_add, eval_mul, eval_sub, eval_one,
      eval_pow, eval_X, eval_C]
    rw [rpow_add_one h1x, rpow_add_one h1x']
    ring
  have hcont : Continuous F := by
    simp only [hF]
    refine (J.continuous.mul p.continuous).mul (Continuous.mul ?_ ?_)
    · exact (continuous_rpow_const hα1.le).comp (continuous_const.sub continuous_id)
    · exact (continuous_rpow_const hβ1.le).comp (continuous_const.add continuous_id)
  have hF1 : F 1 = 0 := by
    rw [hF]
    simp [zero_rpow hα1.ne']
  have hFm1 : F (-1) = 0 := by
    rw [hF]
    simp [zero_rpow hβ1.ne']
  have hint1 : IntegrableOn (fun x => (1 - x) ^ α * (1 + x) ^ β *
      ((derivative J).eval x * p.eval x * (1 - x ^ 2))) (Ioo (-1 : ℝ) 1) :=
    integrableOn_jacobiDensity_mul hα hβ (by fun_prop)
  have hint2 : IntegrableOn (fun x => (1 - x) ^ α * (1 + x) ^ β * (J.eval x * r.eval x))
      (Ioo (-1 : ℝ) 1) :=
    integrableOn_jacobiDensity_mul hα hβ (by fun_prop)
  have hint' : IntervalIntegrable F' volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
    exact integrableOn_jacobiDensity_mul hα hβ (by fun_prop)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (-1 : ℝ) < 1) hderiv hint'
    (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  rw [hF1, hFm1, sub_zero, intervalIntegral.integral_of_le (by norm_num),
    integral_Ioc_eq_integral_Ioo] at hFTC
  have hsplit : ∫ x in Ioo (-1 : ℝ) 1, F' x =
      (∫ x in Ioo (-1 : ℝ) 1, (1 - x) ^ α * (1 + x) ^ β *
        ((derivative J).eval x * p.eval x * (1 - x ^ 2))) +
      ∫ x in Ioo (-1 : ℝ) 1, (1 - x) ^ α * (1 + x) ^ β * (J.eval x * r.eval x) := by
    rw [← integral_add hint1 hint2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF']
    ring
  have hJr : ∫ x in Ioo (-1 : ℝ) 1, (1 - x) ^ α * (1 + x) ^ β * (J.eval x * r.eval x) = 0 := by
    rw [← integral_jacobiMeasure]
    exact integral_family_mul_of_degree_lt hw hrdeg
  rw [hsplit, hJr, add_zero] at hFTC
  rw [integral_jacobiMeasure, ← hFTC]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have h1x : 1 - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx.2)
  have h1x' : 1 + x ≠ 0 := by linarith [hx.1]
  rw [rpow_add_one h1x, rpow_add_one h1x']
  ring

/-- **The derivative of a Jacobi polynomial is a Jacobi polynomial of the shifted weight**:
for `α, β > -1` and `n ≥ 1`, `(J_n^{(α,β)})' = n J_{n-1}^{(α+1,β+1)}` for the monic families. Both
sides are `n` times a monic polynomial of degree `n - 1`, and the left side is orthogonal to the
polynomials of degree less than `n - 1` for the weight `(1-x)^{α+1}(1+x)^{β+1}` by one integration
by parts. Consequently the interior Gauss–Lobatto nodes of a Jacobi weight are the zeros of the
derivative of its `n`-th orthogonal polynomial, as the modified weight
`(1 - x²) · jacobiMeasure α β` is `jacobiMeasure (α + 1) (β + 1)`.

Reference: [quarteroni2000numerical] Remark 10.2 (with the weight read as `(1-x)^α (1+x)^β`). -/
theorem derivative_family_jacobiMeasure {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ}
    (hn : 1 ≤ n) :
    derivative (family (jacobiMeasure α β) n) =
      C (n : ℝ) * family (jacobiMeasure (α + 1) (β + 1)) (n - 1) := by
  have hw' := isWeight_jacobiMeasure (by linarith : -1 < α + 1) (by linarith : -1 < β + 1)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  set J' := derivative (family (jacobiMeasure α β) n) with hJ'
  have hnat : (family (jacobiMeasure α β) n).natDegree = n :=
    natDegree_eq_of_degree_eq_some (degree_family _ _)
  have hJ'deg : J'.degree = ((n - 1 : ℕ) : WithBot ℕ) := by
    rw [hJ', degree_derivative (by rw [hnat]; omega), hnat]
  have hJ'lc : J'.leadingCoeff = n := by
    rw [hJ', leadingCoeff_derivative, (monic_family _ _).leadingCoeff, hnat, one_mul]
  have hJ'ne : J' ≠ 0 := fun h => by
    rw [h, leadingCoeff_zero] at hJ'lc
    exact hnR hJ'lc.symm
  set r : ℝ[X] := C (n : ℝ)⁻¹ * J' with hr
  have hrdeg : r.degree = ((n - 1 : ℕ) : WithBot ℕ) := by
    rw [hr, degree_C_mul (inv_ne_zero hnR), hJ'deg]
  have hrmonic : r.Monic := by
    rw [Monic, hr, leadingCoeff_mul, leadingCoeff_C, hJ'lc, inv_mul_cancel₀ hnR]
  have hr_eq : r = family (jacobiMeasure (α + 1) (β + 1)) (n - 1) := by
    refine sub_eq_zero.mp (eq_zero_of_degree_lt hw' (n := n - 1) ?_ ?_)
    · have := degree_sub_lt_left (p := r) (q := family (jacobiMeasure (α + 1) (β + 1)) (n - 1))
        (by rw [hrdeg, degree_family]) hrmonic.ne_zero
        (by rw [hrmonic.leadingCoeff, (monic_family _ _).leadingCoeff])
      rwa [hrdeg] at this
    · intro k hk
      have e1 : ∫ x, r.eval x * (family (jacobiMeasure (α + 1) (β + 1)) k).eval x
          ∂jacobiMeasure (α + 1) (β + 1) = 0 := by
        have h := integral_derivative_family_jacobiMeasure_mul hα hβ (n := n)
          (p := family (jacobiMeasure (α + 1) (β + 1)) k) (by rw [degree_family]; exact_mod_cast hk)
        rw [← hJ'] at h
        simp only [hr, eval_mul, eval_C, mul_assoc]
        rw [integral_const_mul, h, mul_zero]
      have e2 : ∫ x, (family (jacobiMeasure (α + 1) (β + 1)) (n - 1)).eval x *
          (family (jacobiMeasure (α + 1) (β + 1)) k).eval x ∂jacobiMeasure (α + 1) (β + 1) = 0 :=
        integral_family_mul_family hw' (by omega)
      have hev : ∀ x, (r - family (jacobiMeasure (α + 1) (β + 1)) (n - 1)).eval x *
          (family (jacobiMeasure (α + 1) (β + 1)) k).eval x =
          r.eval x * (family (jacobiMeasure (α + 1) (β + 1)) k).eval x -
            (family (jacobiMeasure (α + 1) (β + 1)) (n - 1)).eval x *
              (family (jacobiMeasure (α + 1) (β + 1)) k).eval x := by
        intro x
        simp only [eval_sub]
        ring
      simp only [hev]
      rw [integral_sub (hw'.integrable_eval_mul _ _) (hw'.integrable_eval_mul _ _), e1, e2,
        sub_zero]
  rw [← hr_eq, hr, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hnR, C_1, one_mul]

/-- The modified weight of the Legendre weight is the Jacobi weight with `α = β = 1`. -/
theorem _root_.OrthogonalPolynomial.jacobiMeasure_one_one :
    jacobiMeasure 1 1 = lobattoMeasure legendreMeasure := by
  rw [jacobiMeasure]
  refine withDensity_congr_ae ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun x _ => ?_
  simp only [rpow_one]
  congr 1
  ring

/-- **The interior Legendre–Gauss–Lobatto nodes are the zeros of `L_n'`**: for `n ≥ 1`,
`L_n' = n lc(L_n) · q_{n-1}` where `q_{n-1}` is the `(n-1)`-st orthogonal polynomial of the modified
weight `(1 - x²) dx`, so the Lobatto nodal polynomial of the Legendre weight is a multiple of
`(1 - x²) L_n'`. This is the Legendre case `α = β = 0` of
`Quadrature.derivative_family_jacobiMeasure`.

Reference: [quarteroni2000numerical] (10.33). -/
theorem derivative_legendre_eq_family {n : ℕ} (hn : 1 ≤ n) :
    derivative (Polynomial.legendre n) =
      C ((n : ℝ) * (Polynomial.legendre n).leadingCoeff) * family (lobattoMeasure legendreMeasure)
        (n - 1) := by
  have h := derivative_family_jacobiMeasure (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (-1 : ℝ) < 0) hn
  rw [jacobiMeasure_zero_zero, zero_add, jacobiMeasure_one_one, family_eq_legendre,
    derivative_C_mul] at h
  have hlc : (Polynomial.legendre n).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero n)
  calc derivative (Polynomial.legendre n)
      = C (Polynomial.legendre n).leadingCoeff *
          (C ((Polynomial.legendre n).leadingCoeff)⁻¹ * derivative (Polynomial.legendre n)) := by
        rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]
    _ = C (Polynomial.legendre n).leadingCoeff *
          (C (n : ℝ) * family (lobattoMeasure legendreMeasure) (n - 1)) := by rw [h]
    _ = _ := by rw [← mul_assoc, ← C_mul, mul_comm (Polynomial.legendre n).leadingCoeff]

end Quadrature

namespace Quadrature

open OrthogonalPolynomial

/-! ### The Legendre–Gauss–Lobatto weights -/

/-- The identity `(X² - 1) L_{m+1}' = (m + 1)(X L_{m+1} - L_m)`, from the two Legendre differential
identities. -/
private theorem quad_mul_derivative_legendre_succ (m : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative (Polynomial.legendre (m + 1)) =
      C ((m : ℝ) + 1) * (X * Polynomial.legendre (m + 1) - Polynomial.legendre m) := by
  have h1 := Polynomial.quad_mul_derivative_legendre m
  have h2 := Polynomial.derivative_legendre_succ m
  rw [h2]
  simp only [map_add, map_natCast, map_one]
  linear_combination X * h1

/-- **The Lobatto nodal polynomial of the Legendre weight** is `X p_{m+1} - c p_m` with
`c = lc(L_m) / lc(L_{m+1})`, for the monic Legendre family `p_k`. -/
private theorem lobattoNodal_legendreMeasure_eq (m : ℕ) :
    lobattoNodal legendreMeasure (m + 1) =
      X * family legendreMeasure (m + 1) -
        C ((Polynomial.legendre m).leadingCoeff / (Polynomial.legendre (m + 1)).leadingCoeff) *
          family legendreMeasure m := by
  have hlcm : (Polynomial.legendre m).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero m)
  have hlcm1 : (Polynomial.legendre (m + 1)).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero (m + 1))
  have hne : ((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff ≠ 0 :=
    mul_ne_zero (by positivity) hlcm1
  have hq : family (lobattoMeasure legendreMeasure) m =
      C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ *
        derivative (Polynomial.legendre (m + 1)) := by
    have h := derivative_legendre_eq_family (n := m + 1) (by omega)
    rw [Nat.add_sub_cancel] at h
    rw [h, ← mul_assoc, ← C_mul]
    push_cast
    rw [inv_mul_cancel₀ hne, C_1, one_mul]
  rw [lobattoNodal, Nat.add_sub_cancel, hq, family_eq_legendre, family_eq_legendre]
  calc (X ^ 2 - 1) * (C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ *
        derivative (Polynomial.legendre (m + 1)))
      = C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ *
          ((X ^ 2 - 1) * derivative (Polynomial.legendre (m + 1))) := by ring
    _ = C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ *
          (C ((m : ℝ) + 1) * (X * Polynomial.legendre (m + 1) - Polynomial.legendre m)) := by
        rw [quad_mul_derivative_legendre_succ]
    _ = _ := by
        rw [← mul_assoc, ← C_mul]
        have e1 : (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ * ((m : ℝ) + 1) =
            ((Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ := by
          field_simp
        have e2 : (Polynomial.legendre m).leadingCoeff /
            (Polynomial.legendre (m + 1)).leadingCoeff * ((Polynomial.legendre m).leadingCoeff)⁻¹ =
            ((Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ := by
          field_simp
        rw [e1, mul_sub, ← mul_assoc (C _) (C _), ← C_mul, e2]
        ring

/-- The derivative of the Lobatto nodal polynomial of the Legendre weight is `(m + 2) p_{m+1}`, by
the Legendre differential equation. -/
private theorem derivative_lobattoNodal_legendreMeasure (m : ℕ) :
    derivative (lobattoNodal legendreMeasure (m + 1)) =
      C ((m : ℝ) + 2) * family legendreMeasure (m + 1) := by
  have hlcm1 : (Polynomial.legendre (m + 1)).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero (m + 1))
  have hne : ((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff ≠ 0 :=
    mul_ne_zero (by positivity) hlcm1
  have hq : family (lobattoMeasure legendreMeasure) m =
      C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ *
        derivative (Polynomial.legendre (m + 1)) := by
    have h := derivative_legendre_eq_family (n := m + 1) (by omega)
    rw [Nat.add_sub_cancel] at h
    rw [h, ← mul_assoc, ← C_mul]
    push_cast
    rw [inv_mul_cancel₀ hne, C_1, one_mul]
  have hode := Polynomial.legendre_ode (m + 1)
  push_cast at hode
  rw [lobattoNodal, Nat.add_sub_cancel, hq, family_eq_legendre,
    show (X ^ 2 - 1) * (C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ *
      derivative (Polynomial.legendre (m + 1))) =
      C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹ *
        ((X ^ 2 - 1) * derivative (Polynomial.legendre (m + 1))) by ring,
    derivative_C_mul, derivative_mul]
  have hder : derivative (X ^ 2 - 1 : ℝ[X]) = 2 * X := by
    rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero, C_eq_natCast]
    norm_num
  rw [hder]
  have e : (X ^ 2 - 1 : ℝ[X]) * derivative (derivative (Polynomial.legendre (m + 1))) +
      2 * X * derivative (Polynomial.legendre (m + 1)) =
      C (((m : ℝ) + 1) * ((m : ℝ) + 2)) * Polynomial.legendre (m + 1) := by
    rw [hode]
    simp only [map_mul, map_add, map_natCast, map_one, map_ofNat]
    ring
  rw [show 2 * X * derivative (Polynomial.legendre (m + 1)) +
      (X ^ 2 - 1) * derivative (derivative (Polynomial.legendre (m + 1))) =
      (X ^ 2 - 1 : ℝ[X]) * derivative (derivative (Polynomial.legendre (m + 1))) +
        2 * X * derivative (Polynomial.legendre (m + 1)) by ring, e,
    ← mul_assoc (C (((m : ℝ) + 1) * (Polynomial.legendre (m + 1)).leadingCoeff)⁻¹), ← C_mul,
    ← mul_assoc (C ((m : ℝ) + 2)), ← C_mul]
  congr 2
  field_simp

/-- **The Legendre–Gauss–Lobatto weights**: for the rule of `Quadrature.exists_gaussLobatto` for the
Legendre weight with `n + 1` nodes, `n ≥ 1`, every weight is `w_j = 2 / (n (n + 1) L_n(x̄_j)²)`,
endpoints included. The Lobatto nodal polynomial is `p_{n+1} + b p_{n-1}` with
`b = β_{n-1} - lc(L_{n-1})/lc(L_n)`, so `Quadrature.weight_eq_of_nodal_eq` gives
`w_j = (‖p_n‖² - b ‖p_{n-1}‖²) / (p_n(x̄_j) ω̄'(x̄_j))`, and `ω̄' = (n + 1) p_n` by the Legendre
differential equation.

Reference: [quarteroni2000numerical] (10.34); Davis–Rabinowitz, *Methods of Numerical Integration*,
§2.7. -/
theorem legendreLobattoWeight_eq {n : ℕ} (hn : 1 ≤ n) {x w : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (hint : IsInterpolatoryMeasure legendreMeasure w x)
    (hnodal : Lagrange.nodal Finset.univ x = lobattoNodal legendreMeasure n) (j : Fin (n + 1)) :
    w j = 2 / ((n : ℝ) * ((n : ℝ) + 1) * (Polynomial.legendre n).eval (x j) ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hw := isWeight_legendreMeasure
  have hlcm : (Polynomial.legendre m).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero m)
  have hlcm1 : (Polynomial.legendre (m + 1)).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero (m + 1))
  have hlcsucc := leadingCoeff_legendre_succ m
  set c : ℝ := (Polynomial.legendre m).leadingCoeff / (Polynomial.legendre (m + 1)).leadingCoeff
    with hc
  have hc0 : c ≠ 0 := div_ne_zero hlcm hlcm1
  -- the Lobatto nodal polynomial in the textbook form
  have hnodal' : Lagrange.nodal Finset.univ x = family legendreMeasure (m + 2) +
      C 0 * family legendreMeasure (m + 1) +
        C (beta legendreMeasure m - c) * family legendreMeasure m := by
    rw [hnodal, lobattoNodal_legendreMeasure_eq, three_term_recurrence hw m,
      alpha_legendreMeasure, C_0, sub_zero, C_sub]
    ring
  have hb : normSq legendreMeasure (m + 1) - (beta legendreMeasure m - c) * normSq legendreMeasure m
      ≠ 0 := by
    rw [normSq_succ hw m, show beta legendreMeasure m * normSq legendreMeasure m -
      (beta legendreMeasure m - c) * normSq legendreMeasure m =
        c * normSq legendreMeasure m by ring]
    exact mul_ne_zero hc0 (normSq_ne_zero hw m)
  obtain ⟨hpne, hwj⟩ := weight_eq_of_nodal_eq hw hx hint hnodal' hb j
  rw [normSq_succ hw m, show beta legendreMeasure m * normSq legendreMeasure m -
    (beta legendreMeasure m - c) * normSq legendreMeasure m = c * normSq legendreMeasure m by ring]
    at hwj
  rw [family_eq_legendre, eval_mul, eval_C] at hpne
  have hL : (Polynomial.legendre (m + 1)).eval (x j) ≠ 0 := fun h => hpne (by rw [h, mul_zero])
  have h2m : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  rw [hwj, hnodal, derivative_lobattoNodal_legendreMeasure, family_eq_legendre,
    normSq_legendreMeasure, hc, hlcsucc]
  simp only [eval_mul, eval_C]
  push_cast
  field_simp
  ring

/-- `L_n` does not vanish at a Legendre–Gauss–Lobatto node: the Christoffel–Darboux computation
of the weights, `Quadrature.weight_eq_of_nodal_eq`, has `p_n(x̄_j)` as a factor of a nonzero
quantity. -/
theorem legendre_eval_ne_zero_of_nodal_eq_lobattoNodal {n : ℕ} (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x)
    (hnodal : Lagrange.nodal Finset.univ x = lobattoNodal legendreMeasure n) (j : Fin (n + 1)) :
    (Polynomial.legendre n).eval (x j) ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hw := isWeight_legendreMeasure
  have hlcm : (Polynomial.legendre m).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero m)
  have hlcm1 : (Polynomial.legendre (m + 1)).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero (m + 1))
  set c : ℝ := (Polynomial.legendre m).leadingCoeff / (Polynomial.legendre (m + 1)).leadingCoeff
    with hc
  have hc0 : c ≠ 0 := div_ne_zero hlcm hlcm1
  have hnodal' : Lagrange.nodal Finset.univ x = family legendreMeasure (m + 2) +
      C 0 * family legendreMeasure (m + 1) +
        C (beta legendreMeasure m - c) * family legendreMeasure m := by
    rw [hnodal, lobattoNodal_legendreMeasure_eq, three_term_recurrence hw m,
      alpha_legendreMeasure, C_0, sub_zero, C_sub]
    ring
  have hb : normSq legendreMeasure (m + 1) - (beta legendreMeasure m - c) * normSq legendreMeasure m
      ≠ 0 := by
    rw [normSq_succ hw m, show beta legendreMeasure m * normSq legendreMeasure m -
      (beta legendreMeasure m - c) * normSq legendreMeasure m =
        c * normSq legendreMeasure m by ring]
    exact mul_ne_zero hc0 (normSq_ne_zero hw m)
  have hpne := (weight_eq_of_nodal_eq hw hx (w := fun i =>
    ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂legendreMeasure) (fun _ => rfl) hnodal' hb j).1
  rw [family_eq_legendre, eval_mul, eval_C] at hpne
  exact fun h => hpne (by rw [h, mul_zero])

/-- **The discrete norms of the Legendre polynomials for the Legendre–Gauss–Lobatto rule**: with
`(f, g)_n = ∑_j w̄_j f(x̄_j) g(x̄_j)`, the `L_k` for `k ≤ n` are orthogonal,
`(L_k, L_k)_n = 2/(2k+1)` for `k < n` (exactness), and `(L_n, L_n)_n = 2/n` (from the weights
`2/(n(n+1) L_n(x̄_j)²)`, the hint of [quarteroni2000numerical] Exercise 10.6).

Reference: [quarteroni2000numerical] §10.4. -/
theorem discreteInner_legendre_legendre {n : ℕ} (hn : 1 ≤ n) {x w : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (hint : IsInterpolatoryMeasure legendreMeasure w x)
    (hnodal : Lagrange.nodal Finset.univ x = lobattoNodal legendreMeasure n)
    (hexact : IsExactOnMeasure legendreMeasure w x (2 * n - 1)) {k l : ℕ} (hk : k ≤ n)
    (hl : l ≤ n) :
    discreteInner w x (fun t => (Polynomial.legendre k).eval t)
        (fun t => (Polynomial.legendre l).eval t) =
      if k = l then (if k = n then (2 : ℝ) / n else 2 / (2 * (k : ℝ) + 1)) else 0 := by
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl]
    by_cases hkn : k = n
    · subst hkn
      rw [ite_eq_left rfl, discreteInner]
      have hval : ∀ i, w i * (Polynomial.legendre k).eval (x i) *
          (Polynomial.legendre k).eval (x i) = 2 / (k * (k + 1)) := by
        intro i
        rw [legendreLobattoWeight_eq hn hx hint hnodal i]
        have := legendre_eval_ne_zero_of_nodal_eq_lobattoNodal hn hx hnodal i
        field_simp
      simp only [hval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      push_cast
      field_simp
    · rw [ite_eq_right hkn, discreteInner_eq_integral_of_degree_le hexact
        (by rw [Polynomial.degree_legendre]; exact_mod_cast (by omega : k + k ≤ 2 * n - 1)),
        integral_legendreMeasure, Polynomial.integral_legendre_mul_legendre, ite_eq_left rfl]
  · rw [ite_eq_right hkl, discreteInner_eq_integral_of_degree_le hexact
      (by rw [Polynomial.degree_legendre, Polynomial.degree_legendre]
          exact_mod_cast (by omega : k + l ≤ 2 * n - 1)),
      integral_legendreMeasure, Polynomial.integral_legendre_mul_legendre, ite_eq_right hkl]

/-- **The discrete Legendre transform.** The interpolant of `f` at the Legendre–Gauss–Lobatto
nodes is `∑_{k ≤ n} f̃_k L_k` with
`f̃_k = ((2k + 1) / (n(n+1))) ∑_j L_k(x̄_j) f(x̄_j) / L_n(x̄_j)²` for `k < n` and
`f̃_n = (1 / (n + 1)) ∑_j f(x̄_j) / L_n(x̄_j)`: the discrete truncation
`Quadrature.interpolate_eq_sum_discreteInner_smul` of the Legendre expansion, with the discrete
norms `Quadrature.discreteInner_legendre_legendre` and the weights
`Quadrature.legendreLobattoWeight_eq`.

Reference: [quarteroni2000numerical] (10.38)–(10.40), Exercise 10.6. -/
theorem interpolate_eq_sum_dlt {n : ℕ} (hn : 1 ≤ n) {x w : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (hwpos : ∀ i, 0 < w i)
    (hint : IsInterpolatoryMeasure legendreMeasure w x)
    (hnodal : Lagrange.nodal Finset.univ x = lobattoNodal legendreMeasure n)
    (hexact : IsExactOnMeasure legendreMeasure w x (2 * n - 1)) (f : ℝ → ℝ) :
    Lagrange.interpolate Finset.univ x (fun i => f (x i)) =
      ∑ k ∈ Finset.range (n + 1),
        C (if k = n then 1 / ((n : ℝ) + 1) * ∑ i, f (x i) / (Polynomial.legendre n).eval (x i)
          else (2 * k + 1) / ((n : ℝ) * ((n : ℝ) + 1)) *
            ∑ i, (Polynomial.legendre k).eval (x i) * f (x i) /
              (Polynomial.legendre n).eval (x i) ^ 2) * Polynomial.legendre k := by
  have hw := isWeight_legendreMeasure
  have hLn : ∀ i, (Polynomial.legendre n).eval (x i) ≠ 0 := fun i =>
    legendre_eval_ne_zero_of_nodal_eq_lobattoNodal hn hx hnodal i
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [interpolate_eq_sum_discreteInner_smul hw hn hx hwpos hexact f,
    ← Fin.sum_univ_eq_sum_range (fun k => C (if k = n then 1 / ((n : ℝ) + 1) *
      ∑ i, f (x i) / (Polynomial.legendre n).eval (x i)
      else (2 * k + 1) / ((n : ℝ) * ((n : ℝ) + 1)) *
        ∑ i, (Polynomial.legendre k).eval (x i) * f (x i) /
          (Polynomial.legendre n).eval (x i) ^ 2) * Polynomial.legendre k) (n + 1)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.2
  have hlc : (Polynomial.legendre k).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (Polynomial.legendre_ne_zero k)
  set c : ℝ := ((Polynomial.legendre k).leadingCoeff)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hlc
  rw [family_eq_legendre]
  have e1 : discreteInner w x f (fun t => (C c * Polynomial.legendre k).eval t) =
      c * discreteInner w x f (fun t => (Polynomial.legendre k).eval t) := by
    simp only [discreteInner, eval_mul, eval_C, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : discreteInner w x (fun t => (C c * Polynomial.legendre k).eval t)
      (fun t => (C c * Polynomial.legendre k).eval t) =
      c ^ 2 * discreteInner w x (fun t => (Polynomial.legendre k).eval t)
        (fun t => (Polynomial.legendre k).eval t) := by
    simp only [discreteInner, eval_mul, eval_C, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hv := discreteInner_legendre_legendre hn hx hint hnodal hexact hk hk
  rw [ite_eq_left rfl] at hv
  have hf : discreteInner w x f (fun t => (Polynomial.legendre k).eval t) =
      2 / ((n : ℝ) * ((n : ℝ) + 1)) * ∑ i, (Polynomial.legendre k).eval (x i) * f (x i) /
        (Polynomial.legendre n).eval (x i) ^ 2 := by
    rw [discreteInner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [legendreLobattoWeight_eq hn hx hint hnodal i]
    have := hLn i
    field_simp
  rw [e1, e2, hv, hf, ← mul_assoc, ← C_mul]
  congr 2
  by_cases hkn : (k : ℕ) = n
  · rw [ite_eq_left hkn, ite_eq_left hkn]
    have hS : ∑ i, (Polynomial.legendre k).eval (x i) * f (x i) /
        (Polynomial.legendre n).eval (x i) ^ 2 =
        ∑ i, f (x i) / (Polynomial.legendre n).eval (x i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hkn]
      have := hLn i
      field_simp
    rw [hS, hc]
    field_simp
  · rw [ite_eq_right hkn, ite_eq_right hkn]
    have h2k : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    rw [hc]
    field_simp

end Quadrature

end
