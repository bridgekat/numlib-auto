import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Weierstrass
import Numlib.Approximation.BestApprox

/-!
# Orthogonal polynomials of a measure

The family of monic orthogonal polynomials attached to a measure `μ` on `ℝ`, its three-term
recurrence, the orthonormal family obtained by scaling it, and the truncated expansion as a best
`L²(μ)` approximation.

## Main definitions

* `OrthogonalPolynomial.IsWeight μ` is the standing hypothesis: every moment of `μ` is finite, and
  `μ` is not carried by a finite set. The first makes every polynomial square integrable, the second
  makes `∫ p² ∂μ` strictly positive for `p ≠ 0`, so that the Gram–Schmidt process on the monomials
  never stalls.
* `OrthogonalPolynomial.family μ n` is the outcome of that process, rescaled to be monic; it is
  defined for every `μ`, but only under `IsWeight μ` is it orthogonal.
  `OrthogonalPolynomial.normSq`, `OrthogonalPolynomial.alpha` and `OrthogonalPolynomial.beta` are
  its squared `L²(μ)` norms and the coefficients of its three-term recurrence.
* `OrthogonalPolynomial.orthonormalFamily μ n` is that family scaled to unit `L²(μ)` norm, and
  `OrthogonalPolynomial.cdA`, `cdB`, `cdC` are the coefficients of *its* three-term recurrence, in
  the form `p_{n+2} = (a_{n+1} X + b_{n+1}) p_{n+1} - c_{n+1} p_n` that the Christoffel–Darboux
  identity consumes; `cdA_eq_leadingCoeff_div` identifies `a_n` with the ratio `A_{n+1} / A_n` of
  leading coefficients.
* `Polynomial.legendre n` is the `n`-th Legendre polynomial, by Rodrigues' formula, and
  `OrthogonalPolynomial.legendreMeasure` is the weight it is orthogonal for.

## Main results

* `OrthogonalPolynomial.integral_family_mul_family` and
  `OrthogonalPolynomial.integral_family_mul_of_degree_lt`: the family is orthogonal, and each member
  is orthogonal to every polynomial of lower degree.
* `OrthogonalPolynomial.three_term_recurrence`: `p_{n+2} = (X - a_{n+1}) p_{n+1} - b_n p_n`, and
  `OrthogonalPolynomial.orthonormalFamily_recurrence` for the orthonormal family.
* `OrthogonalPolynomial.exists_injective_family_eq_prod`: `family μ n` has `n` distinct real roots —
  the nodes of the `n`-point Gauss quadrature rule of `μ`.
* `OrthogonalPolynomial.isBestApprox_truncation`: the truncated expansion is the best `L²(μ)`
  approximation by polynomials of degree at most `N`, and
  `OrthogonalPolynomial.isBestApprox_truncation_of_degree_eq` the same for a family that is already
  orthonormal.
* `OrthogonalPolynomial.IsWeight.denseRange_toLpₗ`: for a weight carried by a compact interval the
  polynomials are dense in `L²(μ)`, by Weierstrass; hence
  `OrthogonalPolynomial.hilbertBasis`, the orthonormal polynomials as a Hilbert basis of `L²(μ)`,
  and `OrthogonalPolynomial.hilbertBasisOfDegreeEq` for any orthonormal family with one polynomial
  of each degree.
* `Polynomial.legendre_recurrence`, `Polynomial.legendre_ode` and
  `Polynomial.integral_legendre_mul_legendre` for the Legendre family, with
  `OrthogonalPolynomial.family_eq_legendre` identifying its monic rescaling with the general
  construction; `Polynomial.Chebyshev.integral_T_mul_T_div_sqrt` is the Chebyshev instance.

## References

The material is [han2009theoretical] §3.5 and [kress1998numerical] §9.3.
-/

open MeasureTheory Polynomial

open scoped Nat

noncomputable section

namespace Polynomial

/-! ### Real polynomials of constant sign

Nothing in Mathlib says when a real polynomial keeps its sign, and the Gauss-quadrature argument
needs exactly that: a polynomial whose real roots all have even multiplicity does not change sign.
-/

/-- **A real polynomial without real roots has constant sign**, by the intermediate value theorem.
-/
theorem forall_pos_or_forall_neg_of_forall_eval_ne_zero {p : ℝ[X]} (h : ∀ x : ℝ, p.eval x ≠ 0) :
    (∀ x, 0 < p.eval x) ∨ (∀ x, p.eval x < 0) := by
  by_cases hpos : ∀ x, 0 < p.eval x
  · exact Or.inl hpos
  refine Or.inr fun v => ?_
  push Not at hpos
  obtain ⟨u, hu⟩ := hpos
  have hu' : p.eval u < 0 := lt_of_le_of_ne hu (h u)
  by_contra hv
  push Not at hv
  have hv' : 0 < p.eval v := lt_of_le_of_ne hv (Ne.symm (h v))
  have hmem : (0 : ℝ) ∈ Set.uIcc (p.eval u) (p.eval v) :=
    Set.mem_uIcc.mpr (Or.inl ⟨hu'.le, hv'.le⟩)
  obtain ⟨c, -, hc⟩ :=
    intermediate_value_uIcc (f := fun x => p.eval x) p.continuous.continuousOn hmem
  exact h c hc

/-- **A real polynomial all of whose real roots have even multiplicity does not change sign.**
Splitting off the square of the product of its linear factors leaves a polynomial with no real root,
which has constant sign by the intermediate value theorem. -/
theorem forall_nonneg_or_forall_nonpos_of_even_rootMultiplicity {p : ℝ[X]} (hp : p ≠ 0)
    (heven : ∀ r : ℝ, Even (p.rootMultiplicity r)) :
    (∀ x, 0 ≤ p.eval x) ∨ (∀ x, p.eval x ≤ 0) := by
  classical
  set g : ℝ[X] := ∏ r ∈ p.roots.toFinset, (X - C r) ^ (p.rootMultiplicity r / 2) with hg
  clear_value g
  have hgsq : g ^ 2 = ∏ r ∈ p.roots.toFinset, (X - C r) ^ p.rootMultiplicity r := by
    rw [hg, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [← pow_mul]
    obtain ⟨k, hk⟩ := heven r
    congr 1
    omega
  have hdvd : g ^ 2 ∣ p := by
    rw [hgsq, ← Polynomial.prod_multiset_root_eq_finset_root]
    exact p.prod_multiset_X_sub_C_dvd
  obtain ⟨h, hh⟩ := hdvd
  have hne : ∀ x : ℝ, h.eval x ≠ 0 := by
    intro x hx
    have hroot : p.IsRoot x := by
      rw [IsRoot, hh, eval_mul, hx, mul_zero]
    have hmem : x ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots hp).2 hroot)
    have hdvd1 : (X - C x) ^ p.rootMultiplicity x ∣ g ^ 2 := by
      rw [hgsq]
      exact Finset.dvd_prod_of_mem _ hmem
    have hdvd2 : (X - C x) ∣ h := dvd_iff_isRoot.mpr hx
    have hdvd3 : (X - C x) ^ (p.rootMultiplicity x + 1) ∣ p := by
      have hgh : (X - C x) ^ (p.rootMultiplicity x + 1) ∣ g ^ 2 * h := by
        rw [pow_succ]
        exact mul_dvd_mul hdvd1 hdvd2
      rwa [← hh] at hgh
    have := (le_rootMultiplicity_iff hp).2 hdvd3
    omega
  have heval : ∀ x : ℝ, p.eval x = g.eval x ^ 2 * h.eval x := by
    intro x
    rw [hh, eval_mul, eval_pow]
  rcases forall_pos_or_forall_neg_of_forall_eval_ne_zero hne with hpos | hneg
  · exact Or.inl fun x => by rw [heval x]; exact mul_nonneg (sq_nonneg _) (hpos x).le
  · refine Or.inr fun x => ?_
    rw [heval x]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hneg x).le

end Polynomial

namespace OrthogonalPolynomial

variable {μ : Measure ℝ}

/-! ### The standing hypothesis -/

/-- A measure on `ℝ` admitting a family of orthogonal polynomials: all its moments are finite, and
it is not carried by a finite set. The second condition is what makes `∫ p ^ 2 ∂μ` positive for
every nonzero polynomial `p`, since a polynomial vanishes only on a finite set. -/
structure IsWeight (μ : Measure ℝ) : Prop where
  /-- Every moment of `μ` is finite. -/
  integrable_pow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) μ
  /-- `μ` gives positive mass to the complement of every finite set. -/
  measure_compl_ne_zero {s : Set ℝ} (hs : s.Finite) : μ sᶜ ≠ 0

namespace IsWeight

/-- A weight is a finite measure: it is the moment of order zero that says so. -/
theorem isFiniteMeasure (hw : IsWeight μ) : IsFiniteMeasure μ := by
  have h : Integrable (fun _ : ℝ => (1 : ℝ)) μ := by simpa using hw.integrable_pow 0
  rcases (integrable_const_iff (μ := μ) (c := (1 : ℝ))).1 h with h1 | h1
  · exact absurd h1 one_ne_zero
  · exact h1

/-- Every polynomial is `μ`-integrable. -/
theorem integrable_eval (hw : IsWeight μ) (p : ℝ[X]) :
    Integrable (fun x => p.eval x) μ := by
  have h : (fun x => p.eval x) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
    funext x; exact p.eval_eq_sum_range x
  rw [h]
  exact integrable_finsetSum _ fun i _ => (hw.integrable_pow i).const_mul _

/-- A product of two polynomials is `μ`-integrable. -/
theorem integrable_eval_mul (hw : IsWeight μ) (p q : ℝ[X]) :
    Integrable (fun x => p.eval x * q.eval x) μ := by
  simpa using hw.integrable_eval (p * q)

/-- The square of a polynomial is `μ`-integrable. -/
theorem integrable_eval_sq (hw : IsWeight μ) (p : ℝ[X]) :
    Integrable (fun x => p.eval x ^ 2) μ := by
  simpa [sq] using hw.integrable_eval_mul p p

/-- The `L²(μ)` norm of a nonzero polynomial is positive: this is where the infinitude of the
support of `μ` is used. -/
theorem integral_eval_sq_pos (hw : IsWeight μ) {p : ℝ[X]} (hp : p ≠ 0) :
    0 < ∫ x, p.eval x ^ 2 ∂μ := by
  refine lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg _) fun h => ?_
  have hae : (fun x => p.eval x ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (hw.integrable_eval_sq p)).1 h.symm
  have hsub : (↑p.roots.toFinset : Set ℝ)ᶜ ⊆ {x | p.eval x ^ 2 ≠ 0} := by
    intro x hx
    simp only [Set.mem_compl_iff, Multiset.mem_toFinset, Finset.mem_coe] at hx
    have : p.eval x ≠ 0 := fun h0 => hx ((mem_roots hp).2 (by simpa [IsRoot] using h0))
    simpa using pow_ne_zero 2 this
  refine hw.measure_compl_ne_zero p.roots.toFinset.finite_toSet ?_
  refine measure_mono_null hsub ?_
  simpa [Filter.EventuallyEq, ae_iff] using hae

/-- The integral of a nonzero polynomial that is nonnegative everywhere is positive: it vanishes
only on a finite set, and `μ` charges the complement of every finite set. -/
theorem integral_eval_pos (hw : IsWeight μ) {p : ℝ[X]} (hp : p ≠ 0)
    (hnn : ∀ x, 0 ≤ p.eval x) : 0 < ∫ x, p.eval x ∂μ := by
  refine lt_of_le_of_ne (integral_nonneg hnn) fun h => ?_
  have hae : (fun x => p.eval x) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg hnn (hw.integrable_eval p)).1 h.symm
  have hsub : (↑p.roots.toFinset : Set ℝ)ᶜ ⊆ {x | p.eval x ≠ 0} := by
    intro x hx
    simp only [Set.mem_compl_iff, Multiset.mem_toFinset, Finset.mem_coe] at hx
    exact fun h0 => hx ((mem_roots hp).2 (by simpa [IsRoot] using h0))
  refine hw.measure_compl_ne_zero p.roots.toFinset.finite_toSet ?_
  refine measure_mono_null hsub ?_
  simpa [Filter.EventuallyEq, ae_iff] using hae

end IsWeight

/-! ### The family -/

/-- The monic orthogonal polynomials of `μ`: Gram–Schmidt applied to the monomials for the inner
product `⟪p, q⟫ = ∫ p q ∂μ`, rescaled to be monic. `family μ n` is monic of degree `n` for every
measure `μ`, and orthogonal to `family μ m` for `m ≠ n` as soon as `IsWeight μ` holds. -/
def family (μ : Measure ℝ) : ℕ → ℝ[X]
  | n => X ^ n - ∑ k ∈ (Finset.range n).attach,
      C ((∫ x, x ^ n * (family μ k.1).eval x ∂μ) / ∫ x, (family μ k.1).eval x ^ 2 ∂μ) *
        family μ k.1
  termination_by n => n
  decreasing_by all_goals exact Finset.mem_range.mp k.2

/-- The defining Gram–Schmidt recursion for `family`, with the sum over `Finset.range`. -/
theorem family_eq (μ : Measure ℝ) (n : ℕ) :
    family μ n = X ^ n - ∑ k ∈ Finset.range n,
      C ((∫ x, x ^ n * (family μ k).eval x ∂μ) / ∫ x, (family μ k).eval x ^ 2 ∂μ) * family μ k := by
  rw [family]
  congr 1
  exact Finset.sum_attach _ fun k =>
    C ((∫ x, x ^ n * (family μ k).eval x ∂μ) / ∫ x, (family μ k).eval x ^ 2 ∂μ) * family μ k

/-- The family starts at the constant `1`, the Gram–Schmidt process having nothing to subtract. -/
@[simp]
theorem family_zero (μ : Measure ℝ) : family μ 0 = 1 := by rw [family_eq]; simp

/-- A linear combination of `family μ 0, …, family μ (n-1)` has degree `< n`, provided the degrees
of those members are already known. -/
private theorem degree_sum_C_mul_family_lt (μ : Measure ℝ) (c : ℕ → ℝ) (n : ℕ)
    (h : ∀ k < n, (family μ k).degree = k) :
    (∑ k ∈ Finset.range n, C (c k) * family μ k).degree < (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  refine lt_of_le_of_lt (degree_mul_le _ _) ?_
  rw [h k hkn]
  calc (C (c k) : ℝ[X]).degree + (k : WithBot ℕ) ≤ 0 + (k : WithBot ℕ) := by
        gcongr; exact degree_C_le
    _ = (k : WithBot ℕ) := zero_add _
    _ < (n : WithBot ℕ) := by exact_mod_cast hkn

/-- `family μ n` has degree `n`. -/
@[simp]
theorem degree_family (μ : Measure ℝ) (n : ℕ) : (family μ n).degree = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [family_eq, degree_sub_eq_left_of_degree_lt, degree_X_pow]
    rw [degree_X_pow]
    exact degree_sum_C_mul_family_lt μ _ n ih

/-- `family μ n` is monic. -/
theorem monic_family (μ : Measure ℝ) (n : ℕ) : (family μ n).Monic := by
  have hlt := degree_sum_C_mul_family_lt μ
    (fun k => (∫ x, x ^ n * (family μ k).eval x ∂μ) / ∫ x, (family μ k).eval x ^ 2 ∂μ) n
    (fun k _ => degree_family μ k)
  rw [family_eq, sub_eq_add_neg]
  refine (monic_X_pow n).add_of_left ?_
  rw [degree_neg, degree_X_pow]
  exact hlt

/-- `family μ n` is never zero. -/
theorem family_ne_zero (μ : Measure ℝ) (n : ℕ) : family μ n ≠ 0 :=
  (monic_family μ n).ne_zero

/-- A constant multiple of a member of the family of index `< n` has degree `< n`. -/
private theorem degree_C_mul_family_lt (μ : Measure ℝ) (a : ℝ) {k n : ℕ} (h : k < n) :
    (C a * family μ k).degree < (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_mul_le _ _) ?_
  rw [degree_family]
  calc (C a : ℝ[X]).degree + (k : WithBot ℕ) ≤ 0 + (k : WithBot ℕ) := by
        gcongr; exact degree_C_le
    _ = (k : WithBot ℕ) := zero_add _
    _ < (n : WithBot ℕ) := by exact_mod_cast h

/-- `X * family μ k` has degree `k + 1`, hence `< n` as soon as `k + 1 < n`. -/
private theorem degree_X_mul_family_lt (μ : Measure ℝ) {k n : ℕ} (h : k + 1 < n) :
    (X * family μ k).degree < (n : WithBot ℕ) := by
  rw [degree_mul, degree_X, degree_family]
  norm_cast
  omega

/-- The `family` as a `Polynomial.Sequence`, so that Mathlib's spanning and independence lemmas for
degree-graded sequences apply to it. -/
def sequence (μ : Measure ℝ) : Polynomial.Sequence ℝ :=
  ⟨family μ, degree_family μ⟩

/-- The members of `OrthogonalPolynomial.sequence` are those of the family. -/
@[simp]
theorem sequence_apply (μ : Measure ℝ) (n : ℕ) : sequence μ n = family μ n := rfl

/-- The squared `L²(μ)` norm `∫ (family μ n)² ∂μ` of the `n`-th orthogonal polynomial. -/
def normSq (μ : Measure ℝ) (n : ℕ) : ℝ := ∫ x, (family μ n).eval x ^ 2 ∂μ

/-- The members of the family are nonzero, so their squared norms are positive. -/
theorem normSq_pos (hw : IsWeight μ) (n : ℕ) : 0 < normSq μ n :=
  hw.integral_eval_sq_pos (family_ne_zero μ n)

/-- The squared norms are nonzero, which is what makes the Fourier coefficients well defined. -/
theorem normSq_ne_zero (hw : IsWeight μ) (n : ℕ) : normSq μ n ≠ 0 :=
  (normSq_pos hw n).ne'

/-! ### Orthogonality -/

private theorem integral_family_mul_family_of_lt (hw : IsWeight μ) :
    ∀ n : ℕ, ∀ j < n, ∫ x, (family μ n).eval x * (family μ j).eval x ∂μ = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j hj
    have hint : ∀ k, Integrable
        (fun x => (family μ k).eval x * (family μ j).eval x) μ :=
      fun k => hw.integrable_eval_mul _ _
    have hsplit : ∀ x : ℝ, (family μ n).eval x * (family μ j).eval x =
        x ^ n * (family μ j).eval x - ∑ k ∈ Finset.range n,
          ((∫ x, x ^ n * (family μ k).eval x ∂μ) / ∫ x, (family μ k).eval x ^ 2 ∂μ) *
            ((family μ k).eval x * (family μ j).eval x) := by
      intro x
      rw [family_eq μ n]
      simp only [eval_sub, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, sub_mul,
        Finset.sum_mul, mul_assoc]
    simp only [hsplit]
    rw [integral_sub (by simpa using hw.integrable_eval_mul (X ^ n) (family μ j))
      (integrable_finsetSum _ fun k _ => (hint k).const_mul _),
      integral_finsetSum _ fun k _ => (hint k).const_mul _]
    simp only [integral_const_mul]
    rw [Finset.sum_eq_single j]
    · have hnz : (∫ x, (family μ j).eval x ^ 2 ∂μ) ≠ 0 := normSq_ne_zero hw j
      have : (∫ x, (family μ j).eval x * (family μ j).eval x ∂μ) =
          ∫ x, (family μ j).eval x ^ 2 ∂μ := by simp [sq]
      rw [this, div_mul_cancel₀ _ hnz]
      simp
    · intro k hk hkj
      have hkn : k < n := Finset.mem_range.mp hk
      rcases lt_or_gt_of_ne hkj with h | h
      · have := ih j hj k h
        rw [show (∫ x, (family μ k).eval x * (family μ j).eval x ∂μ) =
          ∫ x, (family μ j).eval x * (family μ k).eval x ∂μ from
          integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _), this, mul_zero]
      · rw [ih k hkn j h, mul_zero]
    · intro hj'
      exact absurd (Finset.mem_range.mpr hj) hj'

/-- Orthogonality of the family, [han2009theoretical] §3.5: distinct members are orthogonal in
`L²(μ)`. -/
theorem integral_family_mul_family (hw : IsWeight μ) {m n : ℕ} (hmn : m ≠ n) :
    ∫ x, (family μ m).eval x * (family μ n).eval x ∂μ = 0 := by
  rcases lt_or_gt_of_ne hmn with h | h
  · rw [show (∫ x, (family μ m).eval x * (family μ n).eval x ∂μ) =
      ∫ x, (family μ n).eval x * (family μ m).eval x ∂μ from
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)]
    exact integral_family_mul_family_of_lt hw n m h
  · exact integral_family_mul_family_of_lt hw m n h

/-- Every polynomial of degree `< n` is a linear combination of `family μ 0, …, family μ (n-1)`. -/
theorem exists_eq_sum_family (μ : Measure ℝ) {n : ℕ} {q : ℝ[X]} (hq : q.degree < n) :
    ∃ c : ℕ → ℝ, q = ∑ k ∈ Finset.range n, c k • family μ k := by
  have hmem : q ∈ Polynomial.degreeLT ℝ n := Polynomial.mem_degreeLT.mpr hq
  rw [← Polynomial.Sequence.span_degreeLT (sequence μ)
      (fun i _ => by simp [(monic_family μ i).leadingCoeff]),
    show Set.Iio n = (↑(Finset.range n) : Set ℕ) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, by simpa using hc.symm⟩

/-- The family is orthogonal to every polynomial of lower degree. This is the form in which
orthogonality is used: in the Gauss quadrature and best-approximation arguments the second factor is
an arbitrary polynomial, not another member of the family. -/
theorem integral_family_mul_of_degree_lt (hw : IsWeight μ) {n : ℕ} {q : ℝ[X]}
    (hq : q.degree < n) : ∫ x, (family μ n).eval x * q.eval x ∂μ = 0 := by
  obtain ⟨c, rfl⟩ := exists_eq_sum_family μ hq
  have hev : ∀ x : ℝ, (family μ n).eval x * (∑ k ∈ Finset.range n, c k • family μ k).eval x =
      ∑ k ∈ Finset.range n, c k * ((family μ n).eval x * (family μ k).eval x) := by
    intro x
    simp only [eval_finsetSum, eval_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm]
  simp only [hev]
  rw [integral_finsetSum _ fun k _ => ((hw.integrable_eval_mul _ _).const_mul _)]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [integral_const_mul, integral_family_mul_family hw (Nat.ne_of_gt (Finset.mem_range.mp hk)),
    mul_zero]

/-- The expansion of a polynomial of degree `< n` in the orthogonal family, with the Fourier
coefficients `⟪q, p_k⟫ / ‖p_k‖²` made explicit. -/
theorem eq_sum_family (hw : IsWeight μ) {n : ℕ} {q : ℝ[X]} (hq : q.degree < n) :
    q = ∑ k ∈ Finset.range n,
      ((∫ x, q.eval x * (family μ k).eval x ∂μ) / normSq μ k) • family μ k := by
  obtain ⟨c, rfl⟩ := exists_eq_sum_family μ hq
  have hcoeff : ∀ j ∈ Finset.range n,
      (∫ x, (∑ k ∈ Finset.range n, c k • family μ k).eval x * (family μ j).eval x ∂μ) =
        c j * normSq μ j := by
    intro j hj
    have hev : ∀ x : ℝ, (∑ k ∈ Finset.range n, c k • family μ k).eval x * (family μ j).eval x =
        ∑ k ∈ Finset.range n, c k * ((family μ k).eval x * (family μ j).eval x) := by
      intro x
      simp only [eval_finsetSum, eval_smul, smul_eq_mul, Finset.sum_mul, mul_assoc]
    simp only [hev]
    rw [integral_finsetSum _ fun k _ => ((hw.integrable_eval_mul _ _).const_mul _)]
    rw [Finset.sum_eq_single j]
    · rw [integral_const_mul, normSq]
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => (sq _).symm)
    · intro k _ hkj
      rw [integral_const_mul, integral_family_mul_family hw hkj, mul_zero]
    · intro hj'; exact absurd hj hj'
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hcoeff j hj, mul_div_assoc, div_self (normSq_ne_zero hw j), mul_one]

/-- A polynomial of degree `< n` orthogonal to `family μ 0, …, family μ (n-1)` is zero: those `n`
polynomials span the polynomials of degree `< n`. -/
theorem eq_zero_of_degree_lt (hw : IsWeight μ) {n : ℕ} {q : ℝ[X]} (hq : q.degree < n)
    (h : ∀ k < n, ∫ x, q.eval x * (family μ k).eval x ∂μ = 0) : q = 0 := by
  rw [eq_sum_family hw hq]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [h k (Finset.mem_range.mp hk), zero_div, zero_smul]

/-! ### The zeros of the orthogonal polynomials -/

/-- The `n`-th orthogonal polynomial changes sign at least `n` times: it has at least `n` roots of
odd multiplicity.

This is the classical argument. If it changed sign at fewer than `n` points, the product of `family
μ n` with the monic polynomial vanishing at those points would have every real root of even
multiplicity, hence constant sign by
`Polynomial.forall_nonneg_or_forall_nonpos_of_even_rootMultiplicity`, while orthogonality to every
polynomial of lower degree forces its integral against `μ` to vanish. -/
private theorem le_card_odd_rootMultiplicity (hw : IsWeight μ) (n : ℕ) :
    n ≤ ((family μ n).roots.toFinset.filter
      fun r => Odd ((family μ n).rootMultiplicity r)).card := by
  classical
  by_contra hlt
  push Not at hlt
  set S : Finset ℝ :=
    (family μ n).roots.toFinset.filter fun r => Odd ((family μ n).rootMultiplicity r) with hS
  set q : ℝ[X] := ∏ r ∈ S, (X - C r) with hq
  have hqmonic : q.Monic := monic_prod_of_monic _ _ fun r _ => monic_X_sub_C r
  have hqnat : q.natDegree = S.card := by
    rw [hq, natDegree_prod _ _ fun r _ => (monic_X_sub_C r).ne_zero]
    simp
  have hqdeg : q.degree < (n : WithBot ℕ) := by
    rw [degree_eq_natDegree hqmonic.ne_zero, hqnat]
    exact_mod_cast hlt
  have hzero : ∫ x, (family μ n).eval x * q.eval x ∂μ = 0 :=
    integral_family_mul_of_degree_lt hw hqdeg
  have hf0 : family μ n * q ≠ 0 := mul_ne_zero (family_ne_zero μ n) hqmonic.ne_zero
  -- the multiplicities of the auxiliary factor
  have hqroots : q.roots = S.val := by
    rw [hq, Finset.prod_eq_multiset_prod]
    exact roots_multiset_prod_X_sub_C S.val
  have hqmult : ∀ r : ℝ, q.rootMultiplicity r = if r ∈ S then 1 else 0 := by
    intro r
    rw [← count_roots, hqroots]
    by_cases hr : r ∈ S
    · rw [ite_eq_left hr]
      exact Multiset.count_eq_one_of_mem S.nodup (Finset.mem_val.mpr hr)
    · rw [ite_eq_right hr]
      exact Multiset.count_eq_zero_of_notMem fun h => hr (Finset.mem_val.mp h)
  -- every real root of the product has even multiplicity
  have heven : ∀ r : ℝ, Even ((family μ n * q).rootMultiplicity r) := by
    intro r
    rw [rootMultiplicity_mul hf0, hqmult r]
    by_cases hr : r ∈ S
    · rw [ite_eq_left hr]
      exact ((Finset.mem_filter.mp hr).2).add_one
    · rw [ite_eq_right hr, add_zero]
      rcases Nat.even_or_odd ((family μ n).rootMultiplicity r) with hev | hodd
      · exact hev
      · exfalso
        have hpos : 0 < (family μ n).rootMultiplicity r :=
          Nat.pos_of_ne_zero fun h0 => by rw [h0] at hodd; simp at hodd
        have hmem : r ∈ (family μ n).roots.toFinset :=
          Multiset.mem_toFinset.mpr
            ((mem_roots (family_ne_zero μ n)).2
              ((rootMultiplicity_pos (family_ne_zero μ n)).mp hpos))
        exact hr (Finset.mem_filter.mpr ⟨hmem, hodd⟩)
  -- a polynomial of constant sign cannot integrate to zero against a weight
  have hcongr : ∫ x, (family μ n * q).eval x ∂μ = 0 := by
    rw [← hzero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => eval_mul)
  rcases Polynomial.forall_nonneg_or_forall_nonpos_of_even_rootMultiplicity hf0 heven with
    hsign | hsign
  · exact absurd hcongr (hw.integral_eval_pos hf0 hsign).ne'
  · have hneg : 0 < ∫ x, (-(family μ n * q)).eval x ∂μ :=
      hw.integral_eval_pos (neg_ne_zero.mpr hf0) fun x => by
        rw [eval_neg]; exact neg_nonneg.mpr (hsign x)
    have hflip : (∫ x, (-(family μ n * q)).eval x ∂μ) = -∫ x, (family μ n * q).eval x ∂μ := by
      rw [← integral_neg]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => eval_neg _ _)
    rw [hflip, hcongr] at hneg
    norm_num at hneg

/-- **The `n`-th orthogonal polynomial of a weight has `n` distinct real roots**, and is the monic
product of the corresponding linear factors. These roots are the nodes of the `n`-point Gauss
quadrature rule of `μ`.

Reference: [kress1998numerical], §9.3; [han2009theoretical], §3.5.
-/
theorem exists_injective_family_eq_prod (hw : IsWeight μ) (n : ℕ) :
    ∃ x : Fin n → ℝ, Function.Injective x ∧ family μ n = ∏ i, (X - C (x i)) := by
  classical
  have hp0 : family μ n ≠ 0 := family_ne_zero μ n
  have hnat : (family μ n).natDegree = n := natDegree_eq_of_degree_eq_some (degree_family μ n)
  -- the number of distinct roots is squeezed between `n` and `n`
  have hsub : ((family μ n).roots.toFinset.filter
      fun r => Odd ((family μ n).rootMultiplicity r)) ⊆ (family μ n).roots.toFinset :=
    Finset.filter_subset _ _
  have hcard : (family μ n).roots.toFinset.card = n := by
    have h1 := le_card_odd_rootMultiplicity hw n
    have h2 := Finset.card_le_card hsub
    have h3 := Multiset.toFinset_card_le (family μ n).roots
    have h4 := card_roots' (family μ n)
    omega
  -- the product of the linear factors divides, and both sides are monic of degree `n`
  have hGmonic : (∏ r ∈ (family μ n).roots.toFinset, (X - C r)).Monic :=
    monic_prod_of_monic _ _ fun r _ => monic_X_sub_C r
  have hGnat : (∏ r ∈ (family μ n).roots.toFinset, (X - C r)).natDegree = n := by
    rw [natDegree_prod _ _ fun r _ => (monic_X_sub_C r).ne_zero]
    simpa using hcard
  have hmid : (∏ r ∈ (family μ n).roots.toFinset,
      (X - C r) ^ (family μ n).rootMultiplicity r) ∣ family μ n := by
    rw [← Polynomial.prod_multiset_root_eq_finset_root]
    exact (family μ n).prod_multiset_X_sub_C_dvd
  have hGdvd : (∏ r ∈ (family μ n).roots.toFinset, (X - C r)) ∣ family μ n := by
    refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun r hr => ?_) hmid
    have hpos : 0 < (family μ n).rootMultiplicity r :=
      (rootMultiplicity_pos hp0).mpr ((mem_roots hp0).1 (Multiset.mem_toFinset.mp hr))
    exact dvd_pow_self _ hpos.ne'
  have hGeq : family μ n = ∏ r ∈ (family μ n).roots.toFinset, (X - C r) := by
    have h := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hGmonic hGdvd (by
      rw [hnat, hGnat])
    rwa [Monic.leadingCoeff (monic_family μ n), map_one, one_mul] at h
  -- enumerate the roots
  refine ⟨⇑(((family μ n).roots.toFinset).orderEmbOfFin hcard),
    (((family μ n).roots.toFinset).orderEmbOfFin hcard).strictMono.injective, ?_⟩
  have himg : Finset.image (⇑(((family μ n).roots.toFinset).orderEmbOfFin hcard)) Finset.univ
      = (family μ n).roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le (fun r hr => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
      exact Finset.orderEmbOfFin_mem _ hcard i
    · rw [Finset.card_image_of_injective _
        (((family μ n).roots.toFinset).orderEmbOfFin hcard).strictMono.injective,
        Finset.card_univ, Fintype.card_fin, hcard]
  calc family μ n = ∏ r ∈ (family μ n).roots.toFinset, (X - C r) := hGeq
    _ = ∏ r ∈ Finset.image (⇑(((family μ n).roots.toFinset).orderEmbOfFin hcard)) Finset.univ,
          (X - C r) := by rw [himg]
    _ = ∏ i, (X - C ((((family μ n).roots.toFinset).orderEmbOfFin hcard) i)) :=
        Finset.prod_image fun i _ j _ h =>
          (((family μ n).roots.toFinset).orderEmbOfFin hcard).strictMono.injective h

/-! ### The three-term recurrence -/

/-- The coefficient `a_n = ⟪x p_n, p_n⟫ / ‖p_n‖²` of the three-term recurrence. -/
def alpha (μ : Measure ℝ) (n : ℕ) : ℝ :=
  (∫ x, x * (family μ n).eval x ^ 2 ∂μ) / normSq μ n

/-- The coefficient `b_n = ‖p_{n+1}‖² / ‖p_n‖²` of the three-term recurrence. -/
def beta (μ : Measure ℝ) (n : ℕ) : ℝ := normSq μ (n + 1) / normSq μ n

/-- `X * family μ n` agrees with `family μ (n + 1)` up to a polynomial of degree `< n + 1`. -/
private theorem degree_X_mul_family_sub_lt (μ : Measure ℝ) (n : ℕ) :
    (X * family μ n - family μ (n + 1)).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
  have h1 : (X * family μ n).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_X, degree_family]
    push_cast
    exact add_comm _ _
  have h2 : (family μ (n + 1)).degree = ((n + 1 : ℕ) : WithBot ℕ) := degree_family μ (n + 1)
  have hne : X * family μ n ≠ 0 := mul_ne_zero X_ne_zero (family_ne_zero μ n)
  have hlc : (X * family μ n).leadingCoeff = (family μ (n + 1)).leadingCoeff := by
    rw [leadingCoeff_mul, monic_X, (monic_family μ n).leadingCoeff,
      (monic_family μ (n + 1)).leadingCoeff, one_mul]
  simpa [h1] using degree_sub_lt_left (h1.trans h2.symm) hne hlc

/-- `⟪X p_{n+1}, p_n⟫ = ‖p_{n+1}‖²`, because `X p_n` is `p_{n+1}` plus a polynomial of degree `< n +
1`. -/
private theorem integral_X_mul_family_succ_mul_family (hw : IsWeight μ) (n : ℕ) :
    ∫ x, x * (family μ (n + 1)).eval x * (family μ n).eval x ∂μ = normSq μ (n + 1) := by
  have hsplit : ∀ x : ℝ, x * (family μ (n + 1)).eval x * (family μ n).eval x =
      (family μ (n + 1)).eval x ^ 2 +
        (family μ (n + 1)).eval x * (X * family μ n - family μ (n + 1)).eval x := by
    intro x
    simp only [eval_sub, eval_mul, eval_X]
    ring
  simp only [hsplit]
  rw [integral_add (hw.integrable_eval_sq _) (hw.integrable_eval_mul _ _),
    integral_family_mul_of_degree_lt hw (degree_X_mul_family_sub_lt μ n), add_zero]
  rfl

/-- The first step of the three-term recurrence: `p_1 = X - a_0`. It is the Gram–Schmidt step
itself, so no orthogonality is needed. -/
theorem family_one (μ : Measure ℝ) : family μ 1 = X - C (alpha μ 0) := by
  rw [family_eq, alpha, normSq]
  simp

/-- Multiplication by `X` moves across the inner product. -/
private theorem integral_X_mul_family_mul_family (μ : Measure ℝ) (m k : ℕ) :
    ∫ x, x * (family μ m).eval x * (family μ k).eval x ∂μ
      = ∫ x, (family μ m).eval x * (X * family μ k).eval x ∂μ :=
  integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp only [eval_mul, eval_X]; ring)

private theorem integral_family_mul_self (μ : Measure ℝ) (m : ℕ) :
    ∫ x, (family μ m).eval x * (family μ m).eval x ∂μ = normSq μ m :=
  integral_congr_ae (Filter.Eventually.of_forall fun x => (sq ((family μ m).eval x)).symm)

private theorem integral_X_mul_family_mul_self (μ : Measure ℝ) (m : ℕ) :
    ∫ x, x * (family μ m).eval x * (family μ m).eval x ∂μ
      = ∫ x, x * (family μ m).eval x ^ 2 ∂μ :=
  integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- The three-term recurrence for the monic orthogonal polynomials of `μ`, [han2009theoretical]
Exercises 3.5.5–3.5.6: `p_{n+2} = (X - a_{n+1}) p_{n+1} - b_n p_n`. -/
theorem three_term_recurrence (hw : IsWeight μ) (n : ℕ) :
    family μ (n + 2) =
      (X - C (alpha μ (n + 1))) * family μ (n + 1) - C (beta μ n) * family μ n := by
  refine sub_eq_zero.mp (eq_zero_of_degree_lt hw (n := n + 2) ?_ ?_)
  · have hrw : family μ (n + 2) -
        ((X - C (alpha μ (n + 1))) * family μ (n + 1) - C (beta μ n) * family μ n) =
        -(X * family μ (n + 1) - family μ (n + 2)) +
          (C (alpha μ (n + 1)) * family μ (n + 1) + C (beta μ n) * family μ n) := by ring
    rw [hrw]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · rw [degree_neg]
      exact degree_X_mul_family_sub_lt μ (n + 1)
    · refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · exact degree_C_mul_family_lt μ _ (by omega)
      · exact degree_C_mul_family_lt μ _ (by omega)
  · intro k hk
    have hi1 : Integrable (fun x => (family μ (n + 2)).eval x * (family μ k).eval x) μ :=
      hw.integrable_eval_mul _ _
    have hi2 : Integrable
        (fun x => x * (family μ (n + 1)).eval x * (family μ k).eval x) μ :=
      (hw.integrable_eval (X * family μ (n + 1) * family μ k)).congr
        (Filter.Eventually.of_forall fun x => by simp [mul_assoc])
    have hi3 : Integrable (fun x => alpha μ (n + 1) *
        ((family μ (n + 1)).eval x * (family μ k).eval x)) μ :=
      (hw.integrable_eval_mul _ _).const_mul _
    have hi4 : Integrable (fun x => beta μ n *
        ((family μ n).eval x * (family μ k).eval x)) μ :=
      (hw.integrable_eval_mul _ _).const_mul _
    have hi12 : Integrable (fun x => (family μ (n + 2)).eval x * (family μ k).eval x -
        x * (family μ (n + 1)).eval x * (family μ k).eval x) μ := hi1.sub hi2
    have hi123 : Integrable (fun x => (family μ (n + 2)).eval x * (family μ k).eval x -
        x * (family μ (n + 1)).eval x * (family μ k).eval x +
        alpha μ (n + 1) * ((family μ (n + 1)).eval x * (family μ k).eval x)) μ := hi12.add hi3
    have hev : ∀ x : ℝ,
        (family μ (n + 2) -
            ((X - C (alpha μ (n + 1))) * family μ (n + 1) - C (beta μ n) * family μ n)).eval x *
          (family μ k).eval x =
          (family μ (n + 2)).eval x * (family μ k).eval x -
            x * (family μ (n + 1)).eval x * (family μ k).eval x +
            alpha μ (n + 1) * ((family μ (n + 1)).eval x * (family μ k).eval x) +
            beta μ n * ((family μ n).eval x * (family μ k).eval x) := by
      intro x
      simp only [eval_sub, eval_mul, eval_X, eval_C]
      ring
    simp only [hev]
    rw [integral_add hi123 hi4, integral_add hi12 hi3, integral_sub hi1 hi2,
      integral_const_mul, integral_const_mul,
      integral_family_mul_family hw (by omega : n + 2 ≠ k),
      integral_X_mul_family_mul_family]
    rcases lt_trichotomy k n with hkn | hkn | hkn
    · rw [integral_family_mul_of_degree_lt hw (degree_X_mul_family_lt μ (by omega)),
        integral_family_mul_family hw (by omega : n + 1 ≠ k),
        integral_family_mul_family hw (by omega : n ≠ k)]
      ring
    · rw [hkn, ← integral_X_mul_family_mul_family, integral_X_mul_family_succ_mul_family hw,
        integral_family_mul_family hw (by omega : n + 1 ≠ n), integral_family_mul_self]
      simp only [beta]
      rw [div_mul_cancel₀ _ (normSq_ne_zero hw n)]
      ring
    · rw [show k = n + 1 by omega, ← integral_X_mul_family_mul_family,
        integral_X_mul_family_mul_self, integral_family_mul_self,
        integral_family_mul_family hw (by omega : n ≠ n + 1)]
      simp only [alpha]
      rw [div_mul_cancel₀ _ (normSq_ne_zero hw (n + 1))]
      ring

/-! ### The orthonormal polynomials -/

/-- The `L²(μ)` norm `‖p_n‖` of the `n`-th monic orthogonal polynomial. -/
noncomputable def normOf (μ : Measure ℝ) (n : ℕ) : ℝ := Real.sqrt (normSq μ n)

theorem normOf_pos (hw : IsWeight μ) (n : ℕ) : 0 < normOf μ n :=
  Real.sqrt_pos.2 (normSq_pos hw n)

theorem sq_normOf (hw : IsWeight μ) (n : ℕ) : normOf μ n ^ 2 = normSq μ n :=
  Real.sq_sqrt (normSq_pos hw n).le

/-- The **orthonormal polynomials** of a weight: the monic family scaled to unit `L²(μ)` norm.
This is the family [han2009theoretical] §3.7.2 works with, where the normalization
`(p_n, p_n) = 1` is taken "without loss of generality". -/
noncomputable def orthonormalFamily (μ : Measure ℝ) (n : ℕ) : ℝ[X] :=
  C (normOf μ n)⁻¹ * family μ n

theorem eval_orthonormalFamily (μ : Measure ℝ) (n : ℕ) (x : ℝ) :
    (orthonormalFamily μ n).eval x = (normOf μ n)⁻¹ * (family μ n).eval x := by
  rw [orthonormalFamily, eval_mul, eval_C]

/-- Distinct orthonormal polynomials are orthogonal. -/
theorem integral_orthonormalFamily_mul (hw : IsWeight μ) {m n : ℕ} (hmn : m ≠ n) :
    ∫ x, (orthonormalFamily μ m).eval x * (orthonormalFamily μ n).eval x ∂μ = 0 := by
  have h : ∀ x : ℝ, (orthonormalFamily μ m).eval x * (orthonormalFamily μ n).eval x
      = ((normOf μ m)⁻¹ * (normOf μ n)⁻¹) *
        ((family μ m).eval x * (family μ n).eval x) := fun x => by
    rw [eval_orthonormalFamily, eval_orthonormalFamily]; ring
  simp only [h]
  rw [integral_const_mul, integral_family_mul_family hw hmn, mul_zero]

/-- The orthonormal polynomials have unit `L²(μ)` norm. -/
theorem integral_orthonormalFamily_sq (hw : IsWeight μ) (n : ℕ) :
    ∫ x, (orthonormalFamily μ n).eval x ^ 2 ∂μ = 1 := by
  have hn := (normOf_pos hw n).ne'
  have h : ∀ x : ℝ, (orthonormalFamily μ n).eval x ^ 2
      = ((normOf μ n)⁻¹ ^ 2) * ((family μ n).eval x ^ 2) := fun x => by
    rw [eval_orthonormalFamily]; ring
  simp only [h]
  rw [integral_const_mul]
  change (normOf μ n)⁻¹ ^ 2 * normSq μ n = 1
  rw [← sq_normOf hw n]
  field_simp

theorem degree_orthonormalFamily (hw : IsWeight μ) (n : ℕ) :
    (orthonormalFamily μ n).degree = n := by
  rw [orthonormalFamily, degree_C_mul (by
    simpa using inv_ne_zero (normOf_pos hw n).ne'), degree_family]

/-- The leading coefficient `A_n` of the `n`-th orthonormal polynomial is `1 / ‖p_n‖`. -/
theorem leadingCoeff_orthonormalFamily (μ : Measure ℝ) (n : ℕ) :
    (orthonormalFamily μ n).leadingCoeff = (normOf μ n)⁻¹ := by
  rw [orthonormalFamily, leadingCoeff_mul, leadingCoeff_C, (monic_family μ n).leadingCoeff,
    mul_one]

/-! ### The three-term recurrence of the orthonormal polynomials -/

/-- The coefficient `a_n = ‖p_n‖ / ‖p_{n+1}‖` of `X` in the three-term recurrence for the
orthonormal polynomials. It is the ratio `A_{n+1} / A_n` of consecutive leading coefficients
(`cdA_eq_leadingCoeff_div`), which is the form [han2009theoretical] Theorem 3.7.3 states it in. -/
noncomputable def cdA (μ : Measure ℝ) (n : ℕ) : ℝ := normOf μ n / normOf μ (n + 1)

/-- The constant coefficient `b_n = -a_n a_n'` of the three-term recurrence for the orthonormal
polynomials, where `a_n'` is the recurrence coefficient of the monic family. -/
noncomputable def cdB (μ : Measure ℝ) (n : ℕ) : ℝ := -(alpha μ n * cdA μ n)

/-- The coefficient `c_n = ‖p_n‖² / (‖p_{n-1}‖ ‖p_{n+1}‖)` of the three-term recurrence for the
orthonormal polynomials. Only its values at `n ≥ 1` are used. -/
noncomputable def cdC (μ : Measure ℝ) (n : ℕ) : ℝ :=
  normOf μ n * normOf μ n / (normOf μ (n - 1) * normOf μ (n + 1))

theorem cdA_pos (hw : IsWeight μ) (n : ℕ) : 0 < cdA μ n :=
  div_pos (normOf_pos hw n) (normOf_pos hw (n + 1))

/-- The recurrence coefficient `a_n` is the ratio `A_{n+1} / A_n` of the leading coefficients of
consecutive orthonormal polynomials, which is the form the Christoffel–Darboux identity is usually
stated in. -/
theorem cdA_eq_leadingCoeff_div (hw : IsWeight μ) (n : ℕ) :
    cdA μ n = (orthonormalFamily μ (n + 1)).leadingCoeff /
      (orthonormalFamily μ n).leadingCoeff := by
  have h0 := (normOf_pos hw n).ne'
  have h1 := (normOf_pos hw (n + 1)).ne'
  rw [leadingCoeff_orthonormalFamily, leadingCoeff_orthonormalFamily, cdA]
  field_simp

/-- The first step of the three-term recurrence for the orthonormal polynomials. -/
theorem orthonormalFamily_one (hw : IsWeight μ) :
    orthonormalFamily μ 1 = (C (cdA μ 0) * X + C (cdB μ 0)) * orthonormalFamily μ 0 := by
  have h0 := (normOf_pos hw 0).ne'
  have h1 := (normOf_pos hw 1).ne'
  have e1 : cdA μ 0 * (normOf μ 0)⁻¹ = (normOf μ 1)⁻¹ := by
    rw [cdA]; field_simp
  have e2 : cdB μ 0 * (normOf μ 0)⁻¹ = -(alpha μ 0 * (normOf μ 1)⁻¹) := by
    rw [cdB, cdA]; field_simp
  rw [orthonormalFamily, orthonormalFamily, family_one, family_zero, mul_one]
  have hsplit : (C (cdA μ 0) * X + C (cdB μ 0)) * C (normOf μ 0)⁻¹
      = C (cdA μ 0 * (normOf μ 0)⁻¹) * X + C (cdB μ 0 * (normOf μ 0)⁻¹) := by
    simp only [C_mul]; ring
  rw [hsplit, e1, e2, C_neg, C_mul]
  ring

/-- **The three-term recurrence for the orthonormal polynomials**, in the form
`p_{n+2} = (a_{n+1} X + b_{n+1}) p_{n+1} - c_{n+1} p_n` that the Christoffel–Darboux identity
consumes. -/
theorem orthonormalFamily_recurrence (hw : IsWeight μ) (n : ℕ) :
    orthonormalFamily μ (n + 2)
      = (C (cdA μ (n + 1)) * X + C (cdB μ (n + 1))) * orthonormalFamily μ (n + 1)
        - C (cdC μ (n + 1)) * orthonormalFamily μ n := by
  have h0 := (normOf_pos hw n).ne'
  have h1 := (normOf_pos hw (n + 1)).ne'
  have h2 := (normOf_pos hw (n + 2)).ne'
  have e1 : cdA μ (n + 1) * (normOf μ (n + 1))⁻¹ = (normOf μ (n + 2))⁻¹ := by
    rw [cdA]; field_simp
  have e2 : cdB μ (n + 1) * (normOf μ (n + 1))⁻¹
      = -(alpha μ (n + 1) * (normOf μ (n + 2))⁻¹) := by
    rw [cdB, cdA]; field_simp
  have e3 : cdC μ (n + 1) * (normOf μ n)⁻¹ = beta μ n * (normOf μ (n + 2))⁻¹ := by
    have hb : beta μ n = normOf μ (n + 1) ^ 2 / normOf μ n ^ 2 := by
      rw [beta, sq_normOf hw, sq_normOf hw]
    rw [cdC, hb]
    simp only [Nat.add_sub_cancel]
    field_simp
  rw [orthonormalFamily, orthonormalFamily, orthonormalFamily, three_term_recurrence hw n]
  have hsplit : (C (cdA μ (n + 1)) * X + C (cdB μ (n + 1))) *
        (C (normOf μ (n + 1))⁻¹ * family μ (n + 1))
      - C (cdC μ (n + 1)) * (C (normOf μ n)⁻¹ * family μ n)
      = (C (cdA μ (n + 1) * (normOf μ (n + 1))⁻¹) * X
          + C (cdB μ (n + 1) * (normOf μ (n + 1))⁻¹)) * family μ (n + 1)
        - C (cdC μ (n + 1) * (normOf μ n)⁻¹) * family μ n := by
    simp only [C_mul]; ring
  rw [hsplit, e1, e2, e3, C_neg, C_mul, C_mul]
  ring

/-- The normalization `c_{n+1} a_n = a_{n+1}` that the orthonormal scaling produces, and that the
Christoffel–Darboux identity needs. -/
theorem cdC_mul_cdA (hw : IsWeight μ) (n : ℕ) : cdC μ (n + 1) * cdA μ n = cdA μ (n + 1) := by
  have h0 := (normOf_pos hw n).ne'
  have h1 := (normOf_pos hw (n + 1)).ne'
  have h2 := (normOf_pos hw (n + 2)).ne'
  rw [cdC, cdA, cdA]
  simp only [Nat.add_sub_cancel]
  field_simp

/-! ### The truncated expansion as a best approximation -/

namespace IsWeight

/-- Every polynomial lies in `L²(μ)`. -/
theorem memLp (hw : IsWeight μ) (p : ℝ[X]) : MemLp (fun x => p.eval x) 2 μ :=
  (memLp_two_iff_integrable_sq p.continuous.aestronglyMeasurable).2 (hw.integrable_eval_sq p)

/-- The polynomials as a subspace of `L²(μ)`. -/
def toLpₗ (hw : IsWeight μ) : ℝ[X] →ₗ[ℝ] Lp ℝ 2 μ where
  toFun p := (hw.memLp p).toLp _
  map_add' p q := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by simp)
  map_smul' c p := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by simp)

/-- The `L²(μ)` class of a polynomial is represented by the polynomial function. -/
theorem coeFn_toLpₗ (hw : IsWeight μ) (p : ℝ[X]) :
    ⇑(hw.toLpₗ p) =ᵐ[μ] fun x => p.eval x := (hw.memLp p).coeFn_toLp

/-- The `L²(μ)` inner product of two polynomials is `∫ p q ∂μ`. -/
theorem inner_toLpₗ (hw : IsWeight μ) (p q : ℝ[X]) :
    inner ℝ (hw.toLpₗ p) (hw.toLpₗ q) = ∫ x, p.eval x * q.eval x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hw.coeFn_toLpₗ p, hw.coeFn_toLpₗ q] with x hp hq
  rw [hp, hq]
  simp [RCLike.inner_apply, mul_comm]

end IsWeight

/-- The span of `family μ 0, …, family μ N` in `L²(μ)` is the image of the polynomials of degree `≤
N`. -/
theorem map_degreeLE_toLpₗ (hw : IsWeight μ) (N : ℕ) :
    (Polynomial.degreeLE ℝ N).map hw.toLpₗ =
      Submodule.span ℝ (Set.range fun k : Fin (N + 1) => hw.toLpₗ (family μ k)) := by
  rw [← Polynomial.Sequence.span_degreeLE (sequence μ)
      (fun i _ => by simp [(monic_family μ i).leadingCoeff]), Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨family μ k, ⟨k, Nat.lt_succ_iff.mp k.2, rfl⟩, rfl⟩

/-- [han2009theoretical] (3.5.2): the truncated expansion `∑_{k ≤ N} (⟪u, p_k⟫ / ‖p_k‖²) p_k` is the
best `L²(μ)` approximation of `u` by polynomials of degree at most `N`. -/
theorem isBestApprox_truncation (hw : IsWeight μ) (N : ℕ) (u : Lp ℝ 2 μ) :
    IsBestApprox ((Polynomial.degreeLE ℝ N).map hw.toLpₗ : Set (Lp ℝ 2 μ)) u
      (∑ k : Fin (N + 1),
        (inner ℝ (hw.toLpₗ (family μ k)) u / normSq μ k) • hw.toLpₗ (family μ k)) := by
  rw [map_degreeLE_toLpₗ hw N, isBestApprox_sum_iff]
  intro j
  rw [Finset.sum_eq_single j]
  · rw [hw.inner_toLpₗ, integral_family_mul_self, div_mul_cancel₀ _ (normSq_ne_zero hw j)]
  · intro i _ hij
    have hne : ((j : ℕ)) ≠ ((i : ℕ)) := fun h => hij (Fin.val_injective h).symm
    rw [hw.inner_toLpₗ, integral_family_mul_family hw hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-! ### Completeness: the orthonormal polynomials as a Hilbert basis

For a weight carried by a compact interval the polynomials are dense in `L²(μ)`, so an orthonormal
family of polynomials with one member of each degree is a Hilbert basis: the expansion of `u`
converges in `L²(μ)` and Parseval's identity holds. -/

namespace IsWeight

/-- **The polynomials are dense in `L²(μ)`** when the weight is carried by a compact interval.

Three steps: the bounded continuous functions are dense in `L²` of a finite Borel measure on `ℝ`
(`BoundedContinuousFunction.toLp_denseRange`); Weierstrass approximates one of them uniformly on the
interval; and for a finite measure carried by that interval a uniform bound is an `L²` bound
(`MeasureTheory.Lp.norm_le_of_ae_bound`). -/
theorem denseRange_toLpₗ (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) :
    DenseRange (hw.toLpₗ : ℝ[X] → Lp ℝ 2 μ) := by
  have := hw.isFiniteMeasure
  -- a uniform bound is an `L²` bound, with a constant depending only on the total mass
  obtain ⟨M, hM0, hMle⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ (F : Lp ℝ 2 μ) (C : ℝ), 0 ≤ C →
      (∀ᵐ x ∂μ, ‖F x‖ ≤ C) → ‖F‖ ≤ M * C := by
    refine ⟨_, ?_, fun F C hC h => Lp.norm_le_of_ae_bound hC h⟩
    positivity
  have hae : ∀ᵐ x ∂μ, x ∈ Set.Icc a b := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  rw [Metric.denseRange_iff]
  intro F ε hε
  set δ : ℝ := ε / 2 / (M + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  -- a bounded continuous function close to `F` in `L²`
  obtain ⟨g, hg⟩ := Metric.denseRange_iff.1
    (BoundedContinuousFunction.toLp_denseRange (p := 2) ℝ μ ℝ (by simp)) F (ε / 2) (by linarith)
  -- a polynomial uniformly close to it on the interval
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap a b
    ((g : C(ℝ, ℝ)).restrict (Set.Icc a b)) δ hδ0
  refine ⟨p, lt_of_le_of_lt (dist_triangle F (BoundedContinuousFunction.toLp 2 μ ℝ g)
    (hw.toLpₗ p)) ?_⟩
  have hkey : ∀ y ∈ Set.Icc a b, |Polynomial.eval y p - g y| ≤ δ := by
    intro y hy
    have h := ContinuousMap.norm_coe_le_norm
      (p.toContinuousMapOn (Set.Icc a b) - (g : C(ℝ, ℝ)).restrict (Set.Icc a b)) ⟨y, hy⟩
    simpa [Real.norm_eq_abs] using h.trans hp.le
  have hbound : ‖BoundedContinuousFunction.toLp 2 μ ℝ g - hw.toLpₗ p‖ ≤ M * δ := by
    refine hMle _ δ hδ0.le ?_
    filter_upwards [Lp.coeFn_sub (BoundedContinuousFunction.toLp 2 μ ℝ g) (hw.toLpₗ p),
      BoundedContinuousFunction.coeFn_toLp (p := 2) (𝕜 := ℝ) (μ := μ) g, hw.coeFn_toLpₗ p, hae]
      with x hsub hgx hpx hx
    rw [hsub, Pi.sub_apply, hgx, hpx, Real.norm_eq_abs, abs_sub_comm]
    exact hkey x hx
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  have hd : δ * (M + 1) = ε / 2 := by rw [hδ]; field_simp
  have hMδ : M * δ < ε / 2 := by nlinarith
  have hdist : dist (BoundedContinuousFunction.toLp 2 μ ℝ g) (hw.toLpₗ p) ≤ M * δ := by
    rw [dist_eq_norm]; exact hbound
  linarith

end IsWeight

/-- A family of polynomials with one member of each degree spans, in `L²(μ)`, the whole image of the
polynomials. -/
theorem span_range_toLpₗ (hw : IsWeight μ) {q : ℕ → ℝ[X]} (hdeg : ∀ n, (q n).degree = n) :
    Submodule.span ℝ (Set.range (⇑hw.toLpₗ ∘ q)) = LinearMap.range hw.toLpₗ := by
  have hunit : ∀ i, IsUnit (q i).leadingCoeff := by
    intro i
    refine isUnit_iff_ne_zero.2 (Polynomial.leadingCoeff_ne_zero.2 fun h => ?_)
    have := hdeg i
    rw [h, Polynomial.degree_zero] at this
    simp at this
  rw [Set.range_comp, Submodule.span_image,
    Polynomial.Sequence.span (S := ⟨q, hdeg⟩) hunit, Submodule.map_top]

/-- The span of the first `N + 1` members of a family of polynomials with one member of each degree
is, in `L²(μ)`, the image of the polynomials of degree at most `N`. -/
theorem map_degreeLE_toLpₗ_of_degree_eq (hw : IsWeight μ) {q : ℕ → ℝ[X]}
    (hdeg : ∀ n, (q n).degree = n) (N : ℕ) :
    (Polynomial.degreeLE ℝ N).map hw.toLpₗ =
      Submodule.span ℝ (Set.range fun k : Fin (N + 1) => hw.toLpₗ (q k)) := by
  have hunit : ∀ i ≤ N, IsUnit (q i).leadingCoeff := by
    intro i _
    refine isUnit_iff_ne_zero.2 (Polynomial.leadingCoeff_ne_zero.2 fun h => ?_)
    have := hdeg i
    rw [h, Polynomial.degree_zero] at this
    simp at this
  rw [← Polynomial.Sequence.span_degreeLE (S := ⟨q, hdeg⟩) hunit, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨q k, ⟨k, Nat.lt_succ_iff.mp k.2, rfl⟩, rfl⟩

/-- **The truncated expansion in an orthonormal polynomial family is the best `L²(μ)`
approximation** by polynomials of degree at most `N`. This is `isBestApprox_truncation` for a family
that is already normalized, where the coefficients are the plain inner products. -/
theorem isBestApprox_truncation_of_degree_eq (hw : IsWeight μ) {q : ℕ → ℝ[X]}
    (hdeg : ∀ n, (q n).degree = n) (hon : Orthonormal ℝ fun n => hw.toLpₗ (q n)) (N : ℕ)
    (u : Lp ℝ 2 μ) :
    IsBestApprox ((Polynomial.degreeLE ℝ N).map hw.toLpₗ : Set (Lp ℝ 2 μ)) u
      (∑ k : Fin (N + 1), inner ℝ (hw.toLpₗ (q k)) u • hw.toLpₗ (q k)) := by
  classical
  have hon' : Orthonormal ℝ fun k : Fin (N + 1) => hw.toLpₗ (q k) :=
    hon.comp (fun k : Fin (N + 1) => (k : ℕ)) Fin.val_injective
  rw [map_degreeLE_toLpₗ_of_degree_eq hw hdeg N, isBestApprox_sum_iff]
  intro j
  simp [orthonormal_iff_ite.1 hon' j]

/-- **An orthonormal family of polynomials with one member of each degree is a Hilbert basis of
`L²(μ)`**, provided the weight is carried by a compact interval so that Weierstrass applies. -/
noncomputable def hilbertBasisOfDegreeEq (hw : IsWeight μ) {a b : ℝ}
    (hsupp : μ (Set.Icc a b)ᶜ = 0) {q : ℕ → ℝ[X]} (hdeg : ∀ n, (q n).degree = n)
    (hon : Orthonormal ℝ fun n => hw.toLpₗ (q n)) : HilbertBasis ℕ ℝ (Lp ℝ 2 μ) := by
  refine HilbertBasis.mk hon ?_
  rw [show (Set.range fun n => hw.toLpₗ (q n)) = Set.range (⇑hw.toLpₗ ∘ q) from rfl,
    span_range_toLpₗ hw hdeg]
  intro x _
  have hx : x ∈ closure (Set.range ⇑hw.toLpₗ) := hw.denseRange_toLpₗ hsupp x
  rwa [← LinearMap.coe_range, ← Submodule.topologicalClosure_coe] at hx

/-- The Hilbert basis built from a family of polynomials is that family. -/
@[simp]
theorem coe_hilbertBasisOfDegreeEq (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0)
    {q : ℕ → ℝ[X]} (hdeg : ∀ n, (q n).degree = n)
    (hon : Orthonormal ℝ fun n => hw.toLpₗ (q n)) :
    ⇑(hilbertBasisOfDegreeEq hw hsupp hdeg hon) = fun n => hw.toLpₗ (q n) :=
  HilbertBasis.coe_mk hon _

/-- The orthonormal polynomials of a weight are orthonormal in `L²(μ)`. -/
theorem orthonormal_toLpₗ_orthonormalFamily (hw : IsWeight μ) :
    Orthonormal ℝ fun n => hw.toLpₗ (orthonormalFamily μ n) := by
  constructor
  · intro n
    have h : ‖hw.toLpₗ (orthonormalFamily μ n)‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hw.inner_toLpₗ]
      simpa only [← sq] using integral_orthonormalFamily_sq hw n
    nlinarith [norm_nonneg (hw.toLpₗ (orthonormalFamily μ n))]
  · intro m n hmn
    rw [hw.inner_toLpₗ]
    exact integral_orthonormalFamily_mul hw hmn

/-- **The orthonormal polynomials of a weight carried by a compact interval form a Hilbert basis of
`L²(μ)`**: every `u ∈ L²(μ)` is the sum of its orthogonal expansion, and Parseval's identity holds.
This is the completeness that [han2009theoretical] Example 3.4.8 asserts for the Legendre family. -/
noncomputable def hilbertBasis (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) :
    HilbertBasis ℕ ℝ (Lp ℝ 2 μ) :=
  hilbertBasisOfDegreeEq hw hsupp (degree_orthonormalFamily hw)
    (orthonormal_toLpₗ_orthonormalFamily hw)

/-- The Hilbert basis of a weight is its family of orthonormal polynomials. -/
@[simp]
theorem coe_hilbertBasis (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) :
    ⇑(hilbertBasis hw hsupp) = fun n => hw.toLpₗ (orthonormalFamily μ n) :=
  coe_hilbertBasisOfDegreeEq _ _ _ _

end OrthogonalPolynomial

/-! ### The Legendre family -/

namespace Polynomial

/-! ### Leibniz rules for the iterated derivative -/

private lemma iterate_derivative_quad_mul (g : ℝ[X]) (k : ℕ) :
    derivative^[k + 2] ((X ^ 2 - 1) * g) =
      (X ^ 2 - 1) * derivative^[k + 2] g + 2 * ((k : ℝ[X]) + 2) * X * derivative^[k + 1] g +
        ((k : ℝ[X]) + 2) * ((k : ℝ[X]) + 1) * derivative^[k] g := by
  induction k with
  | zero =>
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, derivative_add,
      derivative_mul, derivative_sub, derivative_pow, derivative_X, derivative_one,
      derivative_ofNat, map_zero, map_natCast, map_ofNat, Nat.cast_ofNat]
    push_cast
    ring
  | succ k ih =>
    have h1 : derivative (derivative^[k] g) = derivative^[k + 1] g :=
      (Function.iterate_succ_apply' derivative k g).symm
    have h2 : derivative (derivative^[k + 1] g) = derivative^[k + 2] g :=
      (Function.iterate_succ_apply' derivative (k + 1) g).symm
    have h3 : derivative (derivative^[k + 2] g) = derivative^[k + 3] g :=
      (Function.iterate_succ_apply' derivative (k + 2) g).symm
    rw [show k + 1 + 2 = k + 2 + 1 from rfl,
      Function.iterate_succ_apply' derivative (k + 2) ((X ^ 2 - 1) * g), ih]
    simp only [derivative_add, derivative_mul, derivative_sub, derivative_pow, derivative_X,
      derivative_one, derivative_natCast, derivative_ofNat, map_ofNat,
      Nat.cast_ofNat, h1, h2, h3]
    push_cast
    ring

/-! ### The Legendre polynomials -/

/-- The `n`-th Legendre polynomial, defined by Rodrigues' formula `Pₙ = (2ⁿ n!)⁻¹ (d/dx)ⁿ (x² -
1)ⁿ`. -/
def legendre (n : ℕ) : ℝ[X] :=
  C ((2 ^ n * n ! : ℝ)⁻¹) * derivative^[n] ((X ^ 2 - 1) ^ n)

/-- The normalising constant `2ⁿ n!` of Rodrigues' formula. -/
private def legFac (n : ℕ) : ℝ := 2 ^ n * n !

private lemma legendre_eq (n : ℕ) :
    legendre n = C (legFac n)⁻¹ * derivative^[n] ((X ^ 2 - 1) ^ n) := rfl

private lemma legFac_pos (n : ℕ) : 0 < legFac n := by
  have : 0 < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  simpa [legFac] using by positivity

private lemma legFac_ne_zero (n : ℕ) : legFac n ≠ 0 := (legFac_pos n).ne'

private lemma legFac_succ (n : ℕ) : legFac (n + 1) = 2 * ((n : ℝ) + 1) * legFac n := by
  simp only [legFac, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- Rodrigues' formula, solved for the iterated derivative. -/
private lemma iterate_derivative_pow_eq (n : ℕ) :
    derivative^[n] ((X ^ 2 - 1 : ℝ[X]) ^ n) = C (legFac n) * legendre n := by
  rw [legendre_eq, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (legFac_ne_zero n), C_1, one_mul]

/-! ### The first two Legendre polynomials -/

/-- `P₀ = 1`. -/
theorem legendre_zero : legendre 0 = 1 := by
  simp [legendre_eq, legFac]

private lemma derivative_quad : derivative (X ^ 2 - 1 : ℝ[X]) = 2 * X := by
  have h : (X ^ 2 - 1 : ℝ[X]) = X * X - 1 := by ring
  rw [h]
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, sub_zero, mul_one,
    one_mul]
  ring

/-- `P₁ = X`. -/
theorem legendre_one : legendre 1 = X := by
  have h2 : (C (2 : ℝ)⁻¹ : ℝ[X]) * 2 = 1 := by
    rw [show (2 : ℝ[X]) = C (2 : ℝ) from (map_ofNat C 2).symm, ← C_mul]
    norm_num
  rw [legendre_eq]
  simp only [legFac, pow_one, Nat.factorial_one, Nat.cast_one, mul_one, Function.iterate_one,
    derivative_quad]
  linear_combination (X : ℝ[X]) * h2

/-! ### The two structural identities -/

private lemma quad_mul_derivative_pow (n : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative ((X ^ 2 - 1) ^ (n + 1))
      = C (2 * ((n : ℝ) + 1)) * ((X ^ 2 - 1) ^ (n + 1) * X) := by
  rw [derivative_pow_succ, derivative_quad]
  simp only [map_mul, map_add, map_natCast, map_ofNat, map_one]
  ring

private lemma quad_mul_iterate_derivative_succ (j : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative^[j + 3] ((X ^ 2 - 1) ^ (j + 2))
      = ((j : ℝ[X]) + 3) * (((j : ℝ[X]) + 2) * derivative^[j + 1] ((X ^ 2 - 1) ^ (j + 2))) := by
  have hkey := congrArg (fun p : ℝ[X] => derivative^[j + 2] p) (quad_mul_derivative_pow (j + 1))
  simp only [show j + 1 + 1 = j + 2 from rfl] at hkey
  rw [iterate_derivative_quad_mul, iterate_derivative_C_mul, iterate_derivative_mul_X] at hkey
  simp only [← Function.iterate_succ_apply, nsmul_eq_mul, show j + 2 - 1 = j + 1 from rfl,
    map_mul, map_add, map_natCast, map_ofNat, map_one] at hkey
  push_cast at hkey
  linear_combination hkey

private lemma quad_mul_iterate_derivative (n : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative^[n + 2] ((X ^ 2 - 1) ^ (n + 1))
      = ((n : ℝ[X]) + 2) * (((n : ℝ[X]) + 1) * derivative^[n] ((X ^ 2 - 1) ^ (n + 1))) := by
  cases n with
  | zero =>
    have hd2 : derivative^[0 + 2] ((X ^ 2 - 1 : ℝ[X]) ^ (0 + 1)) = 2 := by
      rw [pow_one, show (0 + 2) = 1 + 1 from rfl, Function.iterate_add_apply,
        Function.iterate_one, derivative_quad]
      simp
    rw [hd2]
    simp only [Nat.cast_zero, zero_add, Function.iterate_zero_apply, pow_one, one_mul]
    ring
  | succ j =>
    have h := quad_mul_iterate_derivative_succ j
    rw [show j + 1 + 2 = j + 3 from rfl, show j + 1 + 1 = j + 2 from rfl]
    push_cast
    linear_combination h

private lemma iterate_derivative_pow_succ_succ (n : ℕ) :
    derivative^[n + 2] ((X ^ 2 - 1 : ℝ[X]) ^ (n + 2))
      = 2 * ((n : ℝ[X]) + 2) *
        (((n : ℝ[X]) + 1) * derivative^[n] ((X ^ 2 - 1) ^ (n + 1))
          + X * derivative^[n + 1] ((X ^ 2 - 1) ^ (n + 1))) := by
  have hu : ((X ^ 2 - 1 : ℝ[X]) ^ (n + 2)) = (X ^ 2 - 1) * (X ^ 2 - 1) ^ (n + 1) := by ring
  rw [hu, iterate_derivative_quad_mul]
  linear_combination quad_mul_iterate_derivative n

private lemma quad_mul_derivative_iterate (n : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative (derivative^[n + 1] ((X ^ 2 - 1) ^ (n + 1)))
      = ((n : ℝ[X]) + 2) * (((n : ℝ[X]) + 1) * derivative^[n] ((X ^ 2 - 1) ^ (n + 1))) := by
  rw [← Function.iterate_succ_apply' derivative (n + 1)]
  exact quad_mul_iterate_derivative n

/-! ### Translation to the Legendre polynomials -/

private lemma natCast_succ_mul_iterate (n : ℕ) :
    ((n : ℝ[X]) + 1) * derivative^[n] ((X ^ 2 - 1) ^ (n + 1))
      = C (legFac (n + 1)) * (legendre (n + 2) - X * legendre (n + 1)) := by
  have hB := iterate_derivative_pow_succ_succ n
  rw [iterate_derivative_pow_eq (n + 2), iterate_derivative_pow_eq (n + 1)] at hB
  have hfac : legFac (n + 2) = 2 * ((n : ℝ) + 2) * legFac (n + 1) := by
    rw [legFac_succ (n + 1)]; push_cast; ring
  rw [hfac] at hB
  simp only [map_mul, map_add, map_natCast, map_ofNat] at hB
  have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 2) := by positivity
  have hne : (2 * ((n : ℝ[X]) + 2)) ≠ 0 := by
    have h2 : (2 * ((n : ℝ[X]) + 2)) = C (2 * ((n : ℝ) + 2)) := by
      simp only [map_mul, map_add, map_natCast, map_ofNat]
    rw [h2]
    exact C_ne_zero.mpr hpos.ne'
  refine mul_left_cancel₀ hne ?_
  linear_combination -hB

private lemma quad_mul_derivative_legendre_succ (n : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative (legendre (n + 1))
      = ((n : ℝ[X]) + 2) * (legendre (n + 2) - X * legendre (n + 1)) := by
  have hA := quad_mul_derivative_iterate n
  rw [iterate_derivative_pow_eq (n + 1), derivative_C_mul, natCast_succ_mul_iterate n] at hA
  refine mul_left_cancel₀ (C_ne_zero.mpr (legFac_ne_zero (n + 1))) ?_
  linear_combination hA

/-- The differential identity `(x² - 1) Pₙ' = (n + 1) (Pₙ₊₁ - x Pₙ)`. -/
theorem quad_mul_derivative_legendre (n : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative (legendre n)
      = ((n : ℝ[X]) + 1) * (legendre (n + 1) - X * legendre n) := by
  cases n with
  | zero => simp [legendre_zero, legendre_one]
  | succ j =>
    have h := quad_mul_derivative_legendre_succ j
    rw [show j + 1 + 1 = j + 2 from rfl]
    push_cast
    linear_combination h

/-- The differential identity `Pₙ₊₁' = x Pₙ' + (n + 1) Pₙ`. -/
theorem derivative_legendre_succ (n : ℕ) :
    derivative (legendre (n + 1))
      = X * derivative (legendre n) + ((n : ℝ[X]) + 1) * legendre n := by
  cases n with
  | zero => simp [legendre_zero, legendre_one]
  | succ j =>
    have hbox : derivative (((j : ℝ[X]) + 1) * derivative^[j] ((X ^ 2 - 1) ^ (j + 1)))
        = derivative (C (legFac (j + 1)) * (legendre (j + 2) - X * legendre (j + 1))) := by
      rw [natCast_succ_mul_iterate j]
    simp only [derivative_mul, derivative_sub, derivative_add, derivative_natCast,
      derivative_one, derivative_C, derivative_X, zero_add, zero_mul, one_mul, add_zero] at hbox
    rw [← Function.iterate_succ_apply' derivative j, iterate_derivative_pow_eq (j + 1)] at hbox
    rw [show j + 1 + 1 = j + 2 from rfl]
    push_cast
    refine mul_left_cancel₀ (C_ne_zero.mpr (legFac_ne_zero (j + 1))) ?_
    linear_combination -hbox

/-- The Legendre differential equation `(x² - 1) Pₙ'' + 2x Pₙ' = n (n + 1) Pₙ`. -/
theorem legendre_ode (n : ℕ) :
    (X ^ 2 - 1 : ℝ[X]) * derivative (derivative (legendre n)) + 2 * X * derivative (legendre n)
      = (n : ℝ[X]) * ((n : ℝ[X]) + 1) * legendre n := by
  have h1 : 2 * X * derivative (legendre n)
        + (X ^ 2 - 1 : ℝ[X]) * derivative (derivative (legendre n))
      = ((n : ℝ[X]) + 1) * (derivative (legendre (n + 1))
        - (legendre n + X * derivative (legendre n))) := by
    rw [← derivative_quad, ← derivative_mul, quad_mul_derivative_legendre n]
    simp only [derivative_mul, derivative_sub, derivative_add, derivative_natCast,
      derivative_one, derivative_X, zero_add, zero_mul, one_mul, add_zero]
  linear_combination h1 + ((n : ℝ[X]) + 1) * derivative_legendre_succ n

/-- The three-term recurrence `(n + 1) Pₙ₊₁ = (2n + 1) x Pₙ - n Pₙ₋₁`, shifted so that no
natural-number subtraction occurs. -/
theorem legendre_recurrence (n : ℕ) :
    ((n : ℝ[X]) + 2) * legendre (n + 2)
      = (2 * (n : ℝ[X]) + 3) * X * legendre (n + 1) - ((n : ℝ[X]) + 1) * legendre n := by
  have h1 := quad_mul_derivative_legendre n
  have h2 := derivative_legendre_succ n
  have h3 := quad_mul_derivative_legendre (n + 1)
  rw [show n + 1 + 1 = n + 2 from rfl] at h3
  push_cast at h3
  linear_combination (-1 : ℝ[X]) * h3 + (X ^ 2 - 1 : ℝ[X]) * h2 + (X : ℝ[X]) * h1

/-! ### Degree -/

private lemma monic_quad : ((X : ℝ[X]) ^ 2 - 1).Monic := by
  have h : ((X : ℝ[X]) ^ 2 - 1) = X ^ 2 - C 1 := by rw [C_1]
  rw [h]
  exact monic_X_pow_sub_C 1 two_ne_zero

private lemma natDegree_quad_pow (n : ℕ) : (((X : ℝ[X]) ^ 2 - 1) ^ n).natDegree = n * 2 := by
  have h : ((X : ℝ[X]) ^ 2 - 1) = X ^ 2 - C 1 := by rw [C_1]
  rw [monic_quad.natDegree_pow, h, natDegree_X_pow_sub_C]

private lemma coeff_iterate_derivative_pow (n : ℕ) :
    (derivative^[n] ((X ^ 2 - 1 : ℝ[X]) ^ n)).coeff n = ((n + n).descFactorial n : ℝ) := by
  have hc : (((X : ℝ[X]) ^ 2 - 1) ^ n).coeff (n + n) = 1 := by
    have h := (monic_quad.pow n).coeff_natDegree
    rw [natDegree_quad_pow] at h
    rw [show n + n = n * 2 by ring]
    exact h
  rw [coeff_iterate_derivative, hc]
  simp

private lemma coeff_iterate_derivative_pow_ne_zero (n : ℕ) :
    (derivative^[n] ((X ^ 2 - 1 : ℝ[X]) ^ n)).coeff n ≠ 0 := by
  rw [coeff_iterate_derivative_pow]
  have h : (n + n).descFactorial n ≠ 0 := by
    rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
    omega
  exact_mod_cast h

private lemma natDegree_iterate_derivative_pow (n : ℕ) :
    (derivative^[n] ((X ^ 2 - 1 : ℝ[X]) ^ n)).natDegree = n := by
  refine le_antisymm ?_ (le_natDegree_of_ne_zero (coeff_iterate_derivative_pow_ne_zero n))
  have h := natDegree_iterate_derivative (((X : ℝ[X]) ^ 2 - 1) ^ n) n
  rw [natDegree_quad_pow] at h
  omega

/-- `Pₙ` is not the zero polynomial. -/
theorem legendre_ne_zero (n : ℕ) : legendre n ≠ 0 := by
  rw [legendre_eq]
  refine mul_ne_zero (C_ne_zero.mpr (inv_ne_zero (legFac_ne_zero n))) ?_
  intro h
  exact coeff_iterate_derivative_pow_ne_zero n (by rw [h, coeff_zero])

/-- `Pₙ` has degree `n`. -/
theorem natDegree_legendre (n : ℕ) : (legendre n).natDegree = n := by
  rw [legendre_eq, natDegree_C_mul (inv_ne_zero (legFac_ne_zero n))]
  exact natDegree_iterate_derivative_pow n

/-- `Pₙ` has degree `n`. -/
theorem degree_legendre (n : ℕ) : (legendre n).degree = n := by
  rw [degree_eq_natDegree (legendre_ne_zero n), natDegree_legendre]

/-! ### Value at the right endpoint -/

/-- `Pₙ(1) = 1`. -/
theorem legendre_eval_one (n : ℕ) : (legendre n).eval 1 = 1 := by
  have hsplit : ((X : ℝ[X]) ^ 2 - 1) ^ n = (X - C 1) ^ n * (X + C 1) ^ n := by
    rw [← mul_pow, C_1]; ring
  rw [legendre_eq, hsplit, iterate_derivative_mul, eval_mul, eval_C, eval_finsetSum,
    Finset.sum_eq_single 0]
  · rw [Nat.sub_zero, Nat.choose_zero_right, Function.iterate_zero_apply,
      iterate_derivative_X_sub_pow_self]
    have h0 : ((2 : ℝ) ^ n * n !) ≠ 0 := legFac_ne_zero n
    simp only [one_smul, eval_mul, eval_natCast, eval_pow, eval_add, eval_X, eval_C, legFac]
    rw [show ((1 : ℝ) + 1) = 2 by norm_num]
    field_simp
  · intro k hk hk0
    rw [Finset.mem_range] at hk
    rw [iterate_derivative_X_sub_pow, show n - (n - k) = k by omega]
    simp [hk0]
  · intro h
    simp at h

/-! ### Orthogonality -/

/-- The integral of a polynomial over the interval `[-1, 1]`. -/
private def legInt (p : ℝ[X]) : ℝ := ∫ x in (-1 : ℝ)..1, p.eval x

private lemma legInt_intervalIntegrable (p : ℝ[X]) :
    IntervalIntegrable (fun x => p.eval x) MeasureTheory.volume (-1) 1 :=
  (p.differentiable (𝕜 := ℝ)).continuous.intervalIntegrable _ _

private lemma legInt_sub (p q : ℝ[X]) : legInt (p - q) = legInt p - legInt q := by
  simp only [legInt, eval_sub]
  exact intervalIntegral.integral_sub (legInt_intervalIntegrable p) (legInt_intervalIntegrable q)

private lemma legInt_C_mul (a : ℝ) (p : ℝ[X]) : legInt (C a * p) = a * legInt p := by
  simp only [legInt, eval_mul, eval_C]
  exact intervalIntegral.integral_const_mul a _

private lemma legInt_mul (p q : ℝ[X]) :
    legInt (p * q) = ∫ x in (-1 : ℝ)..1, p.eval x * q.eval x := by
  simp only [legInt, eval_mul]

private lemma legInt_one : legInt 1 = 2 := by
  simp only [legInt, eval_one, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  norm_num

private lemma legInt_derivative (p : ℝ[X]) : legInt (derivative p) = p.eval 1 - p.eval (-1) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => p.hasDerivAt x)
    (legInt_intervalIntegrable (derivative p))

private lemma legInt_derivative_quad_mul (p : ℝ[X]) :
    legInt (derivative ((X ^ 2 - 1) * p)) = 0 := by
  rw [legInt_derivative]
  simp

/-- The Wronskian-type identity behind orthogonality: a consequence of the two Legendre differential
equations. -/
private lemma derivative_wronskian (m n : ℕ) :
    derivative ((X ^ 2 - 1 : ℝ[X]) *
        (derivative (legendre m) * legendre n - legendre m * derivative (legendre n)))
      = C ((m : ℝ) * ((m : ℝ) + 1) - (n : ℝ) * ((n : ℝ) + 1)) * (legendre m * legendre n) := by
  have hC : (C ((m : ℝ) * ((m : ℝ) + 1) - (n : ℝ) * ((n : ℝ) + 1)) : ℝ[X])
      = (m : ℝ[X]) * ((m : ℝ[X]) + 1) - (n : ℝ[X]) * ((n : ℝ[X]) + 1) := by
    simp only [map_sub, map_mul, map_add, map_natCast, map_one]
  rw [hC, derivative_mul, derivative_quad]
  simp only [derivative_sub, derivative_mul]
  linear_combination legendre n * legendre_ode m - legendre m * legendre_ode n

private lemma legInt_legendre_mul_legendre_of_ne {m n : ℕ} (h : m ≠ n) :
    legInt (legendre m * legendre n) = 0 := by
  have key := legInt_derivative_quad_mul
    (derivative (legendre m) * legendre n - legendre m * derivative (legendre n))
  rw [derivative_wronskian, legInt_C_mul] at key
  have hne : ((m : ℝ) * ((m : ℝ) + 1) - (n : ℝ) * ((n : ℝ) + 1)) ≠ 0 := by
    intro hz
    apply h
    have hfac : ((m : ℝ) - (n : ℝ)) * ((m : ℝ) + (n : ℝ) + 1) = 0 := by linear_combination hz
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact_mod_cast sub_eq_zero.mp h1
    · have hpos : (0 : ℝ) < (m : ℝ) + (n : ℝ) + 1 := by positivity
      exact absurd h2 hpos.ne'
  exact (mul_eq_zero.mp key).resolve_left hne

/-- Legendre polynomials of distinct degrees are orthogonal on `[-1, 1]`. -/
theorem integral_legendre_mul_legendre_of_ne {m n : ℕ} (h : m ≠ n) :
    ∫ x in (-1 : ℝ)..1, (legendre m).eval x * (legendre n).eval x = 0 := by
  rw [← legInt_mul]
  exact legInt_legendre_mul_legendre_of_ne h

/-! ### The `L²` norm -/

private lemma legInt_recurrence (n j : ℕ) :
    ((n : ℝ) + 2) * legInt (legendre (n + 2) * legendre j)
      = (2 * (n : ℝ) + 3) * legInt (X * legendre (n + 1) * legendre j)
        - ((n : ℝ) + 1) * legInt (legendre n * legendre j) := by
  have hpoly : C ((n : ℝ) + 2) * (legendre (n + 2) * legendre j)
      = C (2 * (n : ℝ) + 3) * (X * legendre (n + 1) * legendre j)
        - C ((n : ℝ) + 1) * (legendre n * legendre j) := by
    simp only [map_add, map_mul, map_natCast, map_ofNat, map_one]
    linear_combination legendre j * legendre_recurrence n
  have h := congrArg legInt hpoly
  rwa [legInt_C_mul, legInt_sub, legInt_C_mul, legInt_C_mul] at h

private lemma legInt_cross (n : ℕ) :
    (2 * (n : ℝ) + 3) * legInt (X * legendre (n + 1) * legendre n)
      = ((n : ℝ) + 1) * legInt (legendre n * legendre n) := by
  have h := legInt_recurrence n n
  rw [legInt_legendre_mul_legendre_of_ne (by omega : n + 2 ≠ n)] at h
  linarith

private lemma legInt_cross' (n : ℕ) :
    ((n : ℝ) + 2) * legInt (legendre (n + 2) * legendre (n + 2))
      = (2 * (n : ℝ) + 3) * legInt (X * legendre (n + 2) * legendre (n + 1)) := by
  have h := legInt_recurrence n (n + 2)
  rw [legInt_legendre_mul_legendre_of_ne (by omega : n ≠ n + 2)] at h
  have hcomm : legInt (X * legendre (n + 1) * legendre (n + 2))
      = legInt (X * legendre (n + 2) * legendre (n + 1)) := by
    congr 1
    ring
  rw [hcomm] at h
  linarith

private lemma legInt_sq_step (n : ℕ) :
    (2 * (n : ℝ) + 5) * legInt (legendre (n + 2) * legendre (n + 2))
      = (2 * (n : ℝ) + 3) * legInt (legendre (n + 1) * legendre (n + 1)) := by
  have h1 := legInt_cross' n
  have h2 := legInt_cross (n + 1)
  rw [show n + 1 + 1 = n + 2 from rfl] at h2
  push_cast at h2
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  refine mul_left_cancel₀ hpos.ne' ?_
  linear_combination (2 * (n : ℝ) + 5) * h1 + (2 * (n : ℝ) + 3) * h2

private lemma legInt_sq_aux (n : ℕ) :
    legInt (legendre n * legendre n) = 2 / (2 * (n : ℝ) + 1) ∧
      legInt (legendre (n + 1) * legendre (n + 1)) = 2 / (2 * (n : ℝ) + 3) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [legendre_zero, mul_one, legInt_one]
      norm_num
    · have h := legInt_cross 0
      simp only [Nat.cast_zero, mul_zero, zero_add, legendre_zero, legendre_one, mul_one,
        one_mul, legInt_one] at h
      simp only [Nat.cast_zero, mul_zero, zero_add, legendre_one]
      linarith
  | succ j ih =>
    refine ⟨?_, ?_⟩
    · rw [ih.2]
      push_cast
      ring_nf
    · have h := legInt_sq_step j
      rw [ih.2] at h
      rw [show j + 1 + 1 = j + 2 from rfl]
      push_cast
      have h3 : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
      have h5 : (2 * (j : ℝ) + 5) ≠ 0 := by positivity
      field_simp at h ⊢
      linarith

/-- The `L²` norm of `Pₙ` on `[-1, 1]`. -/
theorem integral_legendre_sq (n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (legendre n).eval x ^ 2 = 2 / (2 * n + 1) := by
  have h := (legInt_sq_aux n).1
  rw [legInt_mul] at h
  simp only [pow_two]
  exact h

/-- Orthogonality of the Legendre polynomials on `[-1, 1]`. -/
theorem integral_legendre_mul_legendre (m n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (legendre m).eval x * (legendre n).eval x
      = if m = n then (2 : ℝ) / (2 * n + 1) else 0 := by
  split_ifs with h
  · subst h
    rw [← integral_legendre_sq]
    simp only [pow_two]
  · exact integral_legendre_mul_legendre_of_ne h

end Polynomial

/-! ### The Legendre family as an instance of the general theory -/

namespace OrthogonalPolynomial

/-- The Legendre weight: Lebesgue measure on the interval `(-1, 1)`. -/
def legendreMeasure : Measure ℝ := volume.restrict (Set.Ioo (-1 : ℝ) 1)

/-- An integral against the Legendre weight is an integral over `[-1, 1]`. -/
theorem integral_legendreMeasure (f : ℝ → ℝ) :
    ∫ x, f x ∂legendreMeasure = ∫ x in (-1 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), legendreMeasure,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- The Legendre weight has finite moments and infinite support. -/
theorem isWeight_legendreMeasure : IsWeight legendreMeasure := by
  constructor
  · intro n
    exact (((continuous_pow n).continuousOn.integrableOn_Icc
      (a := (-1 : ℝ)) (b := 1)).mono_set Set.Ioo_subset_Icc_self)
  · intro s hs hzero
    rw [legendreMeasure, Measure.restrict_apply hs.measurableSet.compl] at hzero
    rw [show sᶜ ∩ Set.Ioo (-1 : ℝ) 1 = Set.Ioo (-1 : ℝ) 1 \ s by ext x; simp [and_comm],
      measure_sdiff_null (hs.measure_zero volume), Real.volume_Ioo] at hzero
    norm_num at hzero

/-- The Legendre polynomials are orthogonal to every polynomial of lower degree. -/
theorem integral_legendre_mul_of_degree_lt {n : ℕ} {p : ℝ[X]} (hp : p.degree < n) :
    ∫ x, (legendre n).eval x * p.eval x ∂legendreMeasure = 0 := by
  have hmem : p ∈ Polynomial.degreeLT ℝ n := Polynomial.mem_degreeLT.mpr hp
  rw [← Polynomial.Sequence.span_degreeLT (⟨legendre, degree_legendre⟩ : Polynomial.Sequence ℝ)
      (fun i _ => isUnit_iff_ne_zero.2 (leadingCoeff_ne_zero.2 (legendre_ne_zero i))),
    show Set.Iio n = (↑(Finset.range n) : Set ℕ) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hev : ∀ x : ℝ, (legendre n).eval x * p.eval x =
      ∑ k ∈ Finset.range n, c k * ((legendre n).eval x * (legendre k).eval x) := by
    intro x
    rw [← hc]
    simp only [eval_finsetSum, eval_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm]
  simp only [hev]
  rw [integral_finsetSum _ fun k _ =>
    ((isWeight_legendreMeasure.integrable_eval_mul _ _).const_mul _)]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [integral_const_mul, integral_legendreMeasure,
    integral_legendre_mul_legendre_of_ne (Nat.ne_of_gt (Finset.mem_range.mp hk)), mul_zero]

/-- The monic rescaling of `Polynomial.legendre n` is the `n`-th orthogonal polynomial of Lebesgue
measure on `(-1, 1)`: the Legendre family is an instance of the general theory. -/
theorem family_eq_legendre (n : ℕ) :
    family legendreMeasure n = C ((legendre n).leadingCoeff)⁻¹ * legendre n := by
  have hlc : (legendre n).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 (legendre_ne_zero n)
  have hdeg : (C ((legendre n).leadingCoeff)⁻¹ * legendre n).degree = (n : WithBot ℕ) := by
    rw [degree_mul, degree_C (inv_ne_zero hlc), zero_add, degree_legendre]
  have hmonic : (C ((legendre n).leadingCoeff)⁻¹ * legendre n).Monic := by
    rw [Monic, leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hlc]
  refine sub_eq_zero.mp (eq_zero_of_degree_lt isWeight_legendreMeasure (n := n) ?_ ?_)
  · have h := degree_sub_lt_left (p := family legendreMeasure n)
      (q := C ((legendre n).leadingCoeff)⁻¹ * legendre n)
      (by rw [degree_family, hdeg]) (family_ne_zero _ n)
      (by rw [(monic_family legendreMeasure n).leadingCoeff, hmonic.leadingCoeff])
    rwa [degree_family] at h
  · intro k hk
    have h1 : ∫ x, (family legendreMeasure n).eval x * (family legendreMeasure k).eval x
        ∂legendreMeasure = 0 :=
      integral_family_mul_family isWeight_legendreMeasure (Nat.ne_of_gt hk)
    have h2 : ∫ x, (C ((legendre n).leadingCoeff)⁻¹ * legendre n).eval x *
        (family legendreMeasure k).eval x ∂legendreMeasure = 0 := by
      have hev : ∀ x : ℝ, (C ((legendre n).leadingCoeff)⁻¹ * legendre n).eval x *
          (family legendreMeasure k).eval x =
          ((legendre n).leadingCoeff)⁻¹ *
            ((legendre n).eval x * (family legendreMeasure k).eval x) := by
        intro x
        simp only [eval_mul, eval_C]
        ring
      simp only [hev]
      rw [integral_const_mul,
        integral_legendre_mul_of_degree_lt (by rw [degree_family]; exact_mod_cast hk), mul_zero]
    have hev : ∀ x : ℝ, (family legendreMeasure n -
        C ((legendre n).leadingCoeff)⁻¹ * legendre n).eval x *
          (family legendreMeasure k).eval x =
        (family legendreMeasure n).eval x * (family legendreMeasure k).eval x -
          (C ((legendre n).leadingCoeff)⁻¹ * legendre n).eval x *
            (family legendreMeasure k).eval x := by
      intro x
      simp only [eval_sub]
      ring
    simp only [hev]
    rw [integral_sub (isWeight_legendreMeasure.integrable_eval_mul _ _)
      (isWeight_legendreMeasure.integrable_eval_mul _ _), h1, h2, sub_zero]

end OrthogonalPolynomial

/-! ### The Chebyshev family -/

namespace Polynomial.Chebyshev

open Real

/-- [han2009theoretical] (3.5.8)–(3.5.9): the Chebyshev polynomials are orthogonal on `(-1, 1)` for
the weight `(1 - x²)^{-1/2}`. -/
theorem integral_T_mul_T_div_sqrt (m n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (T ℝ m).eval x * (T ℝ n).eval x / √(1 - x ^ 2) =
      if m ≠ n then 0 else if n = 0 then π else π / 2 := by
  have hmeas : ∫ x in (-1 : ℝ)..1, (T ℝ m).eval x * (T ℝ n).eval x / √(1 - x ^ 2) =
      ∫ x, (T ℝ m).eval x * (T ℝ n).eval x ∂measureT := by
    rw [integral_measureT]
    simp [div_eq_mul_inv]
  rw [hmeas]
  rcases eq_or_ne m n with rfl | hmn
  · rcases eq_or_ne m 0 with rfl | hm
    · simpa using integral_eval_T_real_mul_self_measureT_zero
    · simpa [hm] using integral_T_real_mul_self_measureT_of_ne_zero hm
  · simpa [hmn] using integral_eval_T_real_mul_eval_T_real_measureT_of_ne hmn

end Polynomial.Chebyshev

end
