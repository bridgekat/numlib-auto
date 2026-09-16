import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.TietzeExtension
import Numlib.Analysis.Normed.Operator.BanachSteinhaus
import Numlib.Approximation.Hermite
import Numlib.Approximation.Interpolation
import Numlib.Approximation.OrthogonalPolynomial

/-!
# Numerical quadrature

A quadrature rule is the bounded linear functional `f ↦ ∑ i, w i * f (x i)` on the continuous
functions of a compact space: finitely many *nodes* `x i` with *weights* `w i`, approximating an
integral. This file has the rule itself, its norm, the criterion by which a sequence of rules
converges for every continuous integrand, and Peano's kernel representation of the error of a
single rule, then the Gauss theory with respect to a weight: Jacobi's characterization of the
degree of exactness, the discrete inner product of a rule and the Gauss remainder. The material is
[han2009theoretical] §2.4, [kress1998numerical] §9.1--§9.3 and [quarteroni2000numerical] §10.2.

## Main definitions

* `Quadrature.functional w x` is the rule, as an element of the dual of `C(X, ℝ)`.
* `Quadrature.IsExactOn L w x d` says that the rule reproduces a target functional `L` on the
  polynomials of degree at most `d`, and `Quadrature.degreeOfExactness` is the largest such `d`.
* `Quadrature.IsInterpolatory L w x` says that the weights are the values of `L` at the Lagrange
  basis functions of the nodes.
* `Quadrature.truncPow m y t` is the truncated power `(y - t)_+^m`, and
  `Quadrature.peanoKernel a b w z m` is the Peano kernel of the rule with weights `w` at nodes `z`:
  the error functional applied to `(· - t)_+^m`, divided by `m!`.
* `Quadrature.IsExactOnMeasure μ w x d` and `Quadrature.IsInterpolatoryMeasure μ w x` are the
  same two notions at the level of a measure `μ` on `ℝ` and polynomials, the form the Gauss theory
  is stated in; `Quadrature.discreteInner w x f g` is the discrete inner product `∑ w i f (x i) g
  (x i)` of a rule.

## Main results

* `Quadrature.norm_functional`: for distinct nodes the norm of the rule is `∑ i, |w i|`. The
  inequality `≤` is the triangle inequality; `≥` needs a continuous function of norm `1` taking the
  value `sign (w i)` at each node, which the Tietze extension theorem supplies.
* `Quadrature.isInterpolatory_iff_isExactOn`: for `n + 1` distinct nodes, being interpolatory and
  being exact to degree `n` agree, both being the statement that the rule is `L` applied to the
  interpolant.
* `Quadrature.tendsto_iff_bddAbove_sum_abs` is the convergence criterion of Szegő and Pólya: rules
  that are exact on polynomials of a degree tending to infinity converge for *every* continuous
  integrand exactly when their weights are uniformly absolutely summable. Sufficiency is the density
  of the polynomials — Weierstrass — together with the ε/3 argument
  `ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded`; necessity is the uniform boundedness
  principle. `Quadrature.tendsto_of_nonneg` is the corollary for nonnegative weights, whose absolute
  sum is the value of the rule at the constant function `1`.
* `Quadrature.exists_gauss` is Gauss quadrature: the roots of the `n`-th orthogonal polynomial of a
  weight carry positive weights making the rule exact on the polynomials of degree less than `2n`,
  and `Quadrature.not_forall_eq_integral_of_degree_le` says that no `n`-point rule does better. Both
  are stated about polynomials and a measure rather than through `IsExactOn`, which lives on `C(X,
  ℝ)` for a compact `X` and would need the weight to be carried by `X`.
* `Quadrature.isExactOnMeasure_add_iff` is **Jacobi's theorem**: a rule with `n + 1` distinct
  nodes is exact to degree `n + m` for `μ` exactly when it is interpolatory and its nodal polynomial
  is `μ`-orthogonal to the polynomials of degree at most `m - 1`;
  `Quadrature.isExactOnMeasure_two_mul_add_one_iff` is the case `m = n + 1`, characterizing the
  Gauss nodes as the roots of the orthogonal polynomial, and
  `Quadrature.not_isExactOnMeasure_two_mul_add_two` the impossibility of degree `2n + 2`.
  `Quadrature.isExactOnMeasure_iff_isExactOn` bridges to the functional level, and
  `Quadrature.isExactOnMeasure_map_affine` transports a rule along an affine change of interval.
* `Quadrature.interpolate_eq_sum_discreteInner_smul`: for a rule exact to degree `2n - 1` the
  interpolant at its `n + 1` nodes is the discrete truncation `∑ (f, p_k)_n / (p_k, p_k)_n · p_k`
  of the orthogonal expansion — the discrete Chebyshev and Legendre transforms are its instances.
* `Quadrature.exists_gauss_error_eq_of_convex` is the **Gauss remainder**
  `f^{(2n)}(ξ)/(2n)! · ∫ p_n² ∂μ`, for a weight carried by any convex set and with no bound asked
  of `f^{(2n)}`, proved through the Hermite interpolant with double nodes: the error minus
  `c · ∫ p_n² ∂μ` integrates to zero, so `f^{(2n)}/(2n)!` cannot stay strictly on one side of `c`
  on the carrier, and the intermediate value theorem produces `ξ`.
  `Quadrature.exists_gauss_error_eq` is the special case of a weight carried by a compact interval,
  where the integrability of the integrand is automatic; the Laguerre weight on `(0, ∞)` and the
  Hermite weight on `ℝ` need the general form.
* `Quadrature.error_eq_integral_peanoKernel` is **Peano's kernel theorem**: a rule exact on the
  polynomials of degree at most `m` has, at an integrand of class `C^{m+1}`, the error
  `∫_a^b K(t) f^{(m+1)}(t) dt` with `K` the Peano kernel; and
  `Quadrature.abs_error_le_integral_abs_peanoKernel` is the bound it is used for.  Unlike the rest
  of this file the statement is not about an arbitrary target functional: the interchange it rests
  on needs the target to be the integral itself, so it is stated for `f ↦ ∫ t in a..b, f t` and for
  a rule given by plain real nodes and weights.

  The proof needs no Fubini step.  `Quadrature.eq_taylorSum_add_integral` is Taylor's formula with
  the integral remainder in the derivative-family form used here, and
  `Quadrature.integral_eq_taylorSum_add_integral` is the same telescoping identity with the kernel
  `(b - t)^{m+1}/(m+1)!`, which is exactly the integral over the panel of the pointwise remainder;
  applying the first at each node and the second over the panel puts both halves of the error on
  one interval.
-/

open Filter Topology

open scoped Polynomial

namespace Quadrature

section Definition

variable {X : Type*} [TopologicalSpace X]

/-- **A quadrature rule.** The bounded linear functional `f ↦ ∑ i, w i * f (x i)` on `C(X, ℝ)` with
nodes `x` and weights `w`, the elementary approximation to an integral.

Reference: [han2009theoretical], (2.4.3). -/
noncomputable def functional {n : ℕ} (w : Fin n → ℝ) (x : Fin n → X) : C(X, ℝ) →L[ℝ] ℝ :=
  ∑ i, w i • ContinuousMap.evalCLM ℝ (x i)

/-- The value of a quadrature rule at an integrand. -/
@[simp]
theorem functional_apply {n : ℕ} (w : Fin n → ℝ) (x : Fin n → X) (f : C(X, ℝ)) :
    functional w x f = ∑ i, w i * f (x i) := by
  simp [functional]

end Definition

section Norm

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- A continuous function of norm at most `1` with prescribed values of modulus at most `1` at
finitely many distinct points: the values already are a continuous function on the finite, hence
discrete, set of nodes, and the Tietze extension theorem extends it with values in `[-1, 1]`. -/
private theorem exists_norm_le_one_apply_eq {n : ℕ} {x : Fin n → X} (hx : Function.Injective x)
    (σ : Fin n → ℝ) (hσ : ∀ i, |σ i| ≤ 1) : ∃ f : C(X, ℝ), ‖f‖ ≤ 1 ∧ ∀ i, f (x i) = σ i := by
  classical
  have hclosed : IsClosed (Set.range x) := (Set.finite_range x).isClosed
  let g : C((Set.range x : Set X), ℝ) :=
    ⟨fun u => σ (Classical.choose u.2), continuous_of_discreteTopology⟩
  have hg : ∀ (u : (Set.range x : Set X)) (i : Fin n), (u : X) = x i → g u = σ i := by
    intro u i hu
    exact congrArg σ (hx ((Classical.choose_spec u.2).trans hu))
  have hmem : ∀ u : (Set.range x : Set X), g u ∈ Set.Icc (-1 : ℝ) 1 := fun u =>
    Set.mem_Icc.mpr (abs_le.mp (hσ (Classical.choose u.2)))
  obtain ⟨f, hfmem, hfeq⟩ :=
    ContinuousMap.exists_restrict_eq_forall_mem_of_closed g hmem ⟨0, by norm_num⟩ hclosed
  refine ⟨f, ?_, fun i => ?_⟩
  · rw [ContinuousMap.norm_le _ zero_le_one]
    exact fun u => Real.norm_eq_abs _ ▸ abs_le.2 ⟨(hfmem u).1, (hfmem u).2⟩
  · have hcongr := congrArg
      (fun h : C((Set.range x : Set X), ℝ) => h ⟨x i, Set.mem_range_self i⟩) hfeq
    simp only [ContinuousMap.restrict_apply] at hcongr
    rw [hcongr, hg _ i rfl]

/-- **The norm of a quadrature rule is the absolute sum of its weights.** The nodes must be
distinct: otherwise the rule with weights `1` and `-1` at one repeated node is the zero functional.

Reference: [han2009theoretical], (2.4.4) and Exercise 2.4.2. -/
theorem norm_functional {n : ℕ} (w : Fin n → ℝ) {x : Fin n → X} (hx : Function.Injective x) :
    ‖functional w x‖ = ∑ i, |w i| := by
  have hnn : (0 : ℝ) ≤ ∑ i, |w i| := by positivity
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ hnn fun f => ?_) ?_
  · rw [functional_apply, Real.norm_eq_abs]
    calc |∑ i, w i * f (x i)| ≤ ∑ i, |w i * f (x i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |w i| * |f (x i)| := by simp [abs_mul]
      _ ≤ ∑ i, |w i| * ‖f‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hfi := f.norm_coe_le_norm (x i)
          rw [Real.norm_eq_abs] at hfi
          exact mul_le_mul_of_nonneg_left hfi (abs_nonneg _)
      _ = (∑ i, |w i|) * ‖f‖ := by rw [Finset.sum_mul]
  · set σ : Fin n → ℝ := fun i => if 0 ≤ w i then 1 else -1 with hσdef
    have hσabs : ∀ i, |σ i| ≤ 1 := by
      intro i
      by_cases hi : 0 ≤ w i <;> simp [hσdef, hi]
    have hσmul : ∀ i, w i * σ i = |w i| := by
      intro i
      by_cases hi : 0 ≤ w i
      · simp [hσdef, hi, abs_of_nonneg hi]
      · simp [hσdef, hi, abs_of_neg (not_le.mp hi)]
    obtain ⟨f, hfnorm, hfnode⟩ := exists_norm_le_one_apply_eq hx σ hσabs
    have hval : functional w x f = ∑ i, |w i| := by
      rw [functional_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hfnode i, hσmul i]
    calc ∑ i, |w i| = |functional w x f| := by rw [hval, abs_of_nonneg hnn]
      _ = ‖functional w x f‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖functional w x‖ * ‖f‖ := (functional w x).le_opNorm f
      _ ≤ ‖functional w x‖ * 1 := by gcongr
      _ = ‖functional w x‖ := mul_one _

end Norm

section Exactness

variable {X : Set ℝ} [CompactSpace X] {n : ℕ}

/-- The constant function `1` is a polynomial of every degree. -/
private theorem one_mem_polyLE (X : Set ℝ) (d : ℕ) : (1 : C(X, ℝ)) ∈ polyLE X d :=
  mem_polyLE_iff.mpr
    ⟨1, Polynomial.degree_one_le.trans (by exact_mod_cast Nat.zero_le d), fun t => by simp⟩

/-- Lagrange interpolation at `n + 1` distinct nodes fixes the polynomials of degree at most `n`. -/
private theorem interpolateCLM_of_mem_polyLE {x : Fin (n + 1) → X} (hx : Function.Injective x)
    {p : C(X, ℝ)} (hp : p ∈ polyLE X n) : Lagrange.interpolateCLM x p = p := by
  obtain ⟨q, hq⟩ := (Lagrange.range_interpolateCLM hx).ge hp
  rw [ContinuousLinearMap.coe_coe] at hq
  rw [← hq]
  simpa using ContinuousLinearMap.ext_iff.mp (Lagrange.isIdempotentElem_interpolateCLM hx) q

/-- A rule is **exact to degree `d`** for a target functional `L` when it reproduces `L` on every
polynomial of degree at most `d`. The *degree of exactness* of a rule is the largest such `d`. -/
def IsExactOn (L : C(X, ℝ) →L[ℝ] ℝ) {m : ℕ} (w : Fin m → ℝ) (x : Fin m → X) (d : ℕ) : Prop :=
  ∀ p ∈ polyLE X d, functional w x p = L p

omit [CompactSpace X] in
/-- Exactness to a degree implies exactness to every smaller degree. -/
theorem IsExactOn.mono {L : C(X, ℝ) →L[ℝ] ℝ} {m : ℕ} {w : Fin m → ℝ} {x : Fin m → X} {d e : ℕ}
    (h : IsExactOn L w x d) (hed : e ≤ d) : IsExactOn L w x e := fun p hp => by
  obtain ⟨P, hP, hPval⟩ := mem_polyLE_iff.mp hp
  exact h p (mem_polyLE_iff.mpr ⟨P, hP.trans (by exact_mod_cast hed), hPval⟩)

/-- The **degree of exactness** of a quadrature rule: the largest degree up to which it reproduces
the target functional. The value is junk when the rule is exact to every degree, as it is when the
target functional is the rule itself. -/
noncomputable def degreeOfExactness (L : C(X, ℝ) →L[ℝ] ℝ) {m : ℕ} (w : Fin m → ℝ)
    (x : Fin m → X) : ℕ :=
  sSup {d | IsExactOn L w x d}

omit [CompactSpace X] in
/-- Every degree of exactness is at most the degree of exactness, provided the latter is not the
junk value of an unbounded set. -/
theorem IsExactOn.le_degreeOfExactness {L : C(X, ℝ) →L[ℝ] ℝ} {m : ℕ} {w : Fin m → ℝ}
    {x : Fin m → X} {d : ℕ} (h : IsExactOn L w x d) (hbdd : BddAbove {e | IsExactOn L w x e}) :
    d ≤ degreeOfExactness L w x :=
  le_csSup hbdd h

/-- **An interpolatory rule.** Its weights are the values of the target functional at the Lagrange
basis functions of its nodes, so that the rule is `L` applied to the interpolant.

Reference: [kress1998numerical], §9.1. -/
def IsInterpolatory (L : C(X, ℝ) →L[ℝ] ℝ) (w : Fin (n + 1) → ℝ) (x : Fin (n + 1) → X) : Prop :=
  ∀ i, w i = L (Lagrange.basisCM x i)

/-- Exactness on the polynomials of degree at most `n` says exactly that the rule is the target
functional applied to the Lagrange interpolant at its nodes. -/
theorem isExactOn_iff_functional_eq {L : C(X, ℝ) →L[ℝ] ℝ} {w : Fin (n + 1) → ℝ}
    {x : Fin (n + 1) → X} (hx : Function.Injective x) :
    IsExactOn L w x n ↔ functional w x = L.comp (Lagrange.interpolateCLM x) := by
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun f => ?_
    have hmem : Lagrange.interpolateCLM x f ∈ polyLE X n :=
      (Lagrange.range_interpolateCLM hx).le ⟨f, rfl⟩
    rw [ContinuousLinearMap.comp_apply, ← h _ hmem, functional_apply, functional_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Lagrange.interpolateCLM_apply_node hx f i]
  · intro h p hp
    rw [h, ContinuousLinearMap.comp_apply, interpolateCLM_of_mem_polyLE hx hp]

/-- **An `n + 1`-point rule at distinct nodes is interpolatory exactly when it is exact on the
polynomials of degree at most `n`.**

Reference: [kress1998numerical], §9.1. -/
theorem isInterpolatory_iff_isExactOn {L : C(X, ℝ) →L[ℝ] ℝ} {w : Fin (n + 1) → ℝ}
    {x : Fin (n + 1) → X} (hx : Function.Injective x) :
    IsInterpolatory L w x ↔ IsExactOn L w x n := by
  have hfix : ∀ i, Lagrange.interpolateCLM x (Lagrange.basisCM x i) = Lagrange.basisCM x i := by
    intro i
    ext t
    rw [Lagrange.interpolateCLM_apply, Finset.sum_eq_single i]
    · rw [Lagrange.basisCM_apply_node_self hx, one_mul]
    · intro j _ hji
      rw [Lagrange.basisCM_apply_node_ne (Ne.symm hji), zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hval : ∀ i, functional w x (Lagrange.basisCM x i) = w i := by
    intro i
    rw [functional_apply, Finset.sum_eq_single i]
    · rw [Lagrange.basisCM_apply_node_self hx, mul_one]
    · intro j _ hji
      rw [Lagrange.basisCM_apply_node_ne (Ne.symm hji), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [isExactOn_iff_functional_eq hx]
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun f => ?_
    have hL : L (Lagrange.interpolateCLM x f) = ∑ i, f (x i) * L (Lagrange.basisCM x i) := by
      have hsum : Lagrange.interpolateCLM x f = ∑ i, f (x i) • Lagrange.basisCM x i := by
        ext t
        rw [Lagrange.interpolateCLM_apply, ContinuousMap.sum_apply]
        exact Finset.sum_congr rfl fun i _ => rfl
      rw [hsum, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    rw [ContinuousLinearMap.comp_apply, hL, functional_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [h i, mul_comm]
  · intro h i
    have := congrArg (fun T : C(X, ℝ) →L[ℝ] ℝ => T (Lagrange.basisCM x i)) h
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [hval i, hfix i] at this
    exact this

end Exactness

section Convergence

variable {a b : ℝ}

/-- Weierstrass' theorem: the polynomial functions are dense in `C([a, b], ℝ)`. -/
private theorem dense_polynomialFunctions (a b : ℝ) :
    Dense ((polynomialFunctions (Set.Icc a b) : Subalgebra ℝ C(Set.Icc a b, ℝ)) :
      Set C(Set.Icc a b, ℝ)) := by
  have h := polynomialFunctions_closure_eq_top a b
  rw [SetLike.ext'_iff, Subalgebra.topologicalClosure_coe, Algebra.coe_top] at h
  exact dense_iff_closure_eq.2 h

/-- A convergent sequence in a normed space has bounded norms. -/
private theorem exists_norm_le_of_tendsto {Y : Type*} [NormedAddCommGroup Y] {f : ℕ → Y} {y : Y}
    (h : Tendsto f atTop (𝓝 y)) : ∃ C : ℝ, ∀ k, ‖f k‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ h)
  exact ⟨C, fun k => hC _ ⟨k, rfl⟩⟩

/-- **The Szegő–Pólya convergence criterion for quadrature rules.** A sequence of rules at distinct
nodes of `[a, b]`, exact for a bounded functional `L` on the polynomials of degree at most `d k`
with `d k → ∞`, converges to `L` at every continuous integrand if and only if the absolute sums of
its weights are bounded.

Sufficiency is Weierstrass' theorem — on a polynomial the rules are eventually equal to `L` —
together with the ε/3 argument for a uniformly bounded family. Necessity is the uniform boundedness
principle applied to the rules, whose norms are the absolute sums of their weights.

Reference: [han2009theoretical], §2.4.4; [kress1998numerical], Theorem 9.10. -/
theorem tendsto_iff_bddAbove_sum_abs {m d : ℕ → ℕ} {w : ∀ k, Fin (m k) → ℝ}
    {x : ∀ k, Fin (m k) → Set.Icc a b} (hx : ∀ k, Function.Injective (x k))
    {L : C(Set.Icc a b, ℝ) →L[ℝ] ℝ} (hd : Tendsto d atTop atTop)
    (hexact : ∀ k, IsExactOn L (w k) (x k) (d k)) :
    (∀ v, Tendsto (fun k => functional (w k) (x k) v) atTop (𝓝 (L v))) ↔
      ∃ C, ∀ k, ∑ i, |w k i| ≤ C := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := banach_steinhaus fun v => exists_norm_le_of_tendsto (h v)
    exact ⟨C, fun k => by rw [← norm_functional (w k) (hx k)]; exact hC k⟩
  · rintro ⟨C, hC⟩
    have hCk : ∀ k, ‖functional (w k) (x k)‖ ≤ C := fun k => by
      rw [norm_functional (w k) (hx k)]; exact hC k
    refine ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded
      (dense_polynomialFunctions a b) hCk ?_
    rintro v ⟨P, -, rfl⟩
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hd.eventually_ge_atTop P.natDegree] with k hk
    refine (hexact k _ ⟨P, Polynomial.mem_degreeLE.mpr ?_, rfl⟩).symm
    exact P.degree_le_natDegree.trans (by exact_mod_cast hk)

/-- **Rules with nonnegative weights converge.** Under the exactness hypothesis of
`Quadrature.tendsto_iff_bddAbove_sum_abs`, nonnegative weights are automatically bounded in absolute
sum, because that sum is the value of the rule at the constant function `1`, hence `L 1`.

Reference: [han2009theoretical], Exercise 2.4.3. -/
theorem tendsto_of_nonneg {m d : ℕ → ℕ} {w : ∀ k, Fin (m k) → ℝ}
    {x : ∀ k, Fin (m k) → Set.Icc a b} (hx : ∀ k, Function.Injective (x k))
    {L : C(Set.Icc a b, ℝ) →L[ℝ] ℝ} (hd : Tendsto d atTop atTop)
    (hexact : ∀ k, IsExactOn L (w k) (x k) (d k)) (hw : ∀ k i, 0 ≤ w k i)
    (v : C(Set.Icc a b, ℝ)) :
    Tendsto (fun k => functional (w k) (x k) v) atTop (𝓝 (L v)) := by
  refine (tendsto_iff_bddAbove_sum_abs hx hd hexact).mpr ⟨L 1, fun k => le_of_eq ?_⟩ v
  have hval := hexact k _ (one_mem_polyLE (Set.Icc a b) (d k))
  rw [functional_apply] at hval
  rw [← hval]
  exact Finset.sum_congr rfl fun i _ => by rw [abs_of_nonneg (hw k i)]; simp

end Convergence

/-! ### Gauss quadrature -/

section Gauss

open OrthogonalPolynomial Polynomial MeasureTheory

variable {μ : Measure ℝ}

/-- **Gauss quadrature.** For a weight `μ` and every `n`, the `n` roots of the `n`-th orthogonal
polynomial of `μ` carry positive weights making the rule exact on every polynomial of degree less
than `2n` — twice as far as the `n` degrees of freedom of the nodes alone would give.

The nodes are the roots of `OrthogonalPolynomial.family μ n`, which are `n` and distinct
(`OrthogonalPolynomial.exists_injective_family_eq_prod`), and the weights are the integrals of the
Lagrange basis functions of those nodes, so the rule is interpolatory and hence exact to degree `n -
1` by construction. Exactness to degree `2n - 1` is division with remainder by the orthogonal
polynomial: the quotient has degree less than `n`, so its integral against the orthogonal polynomial
vanishes, while the nodes annihilate that term in the sum. Positivity of the weights is exactness
applied to the square of a Lagrange basis function.

`Quadrature.not_forall_eq_integral_of_degree_le` is the converse: no `n`-point rule at all is exact
to degree `2n`.

Reference: [kress1998numerical], §9.3; [han2009theoretical], §3.5.
-/
theorem exists_gauss (hw : IsWeight μ) (n : ℕ) :
    ∃ x w : Fin n → ℝ, Function.Injective x ∧ (∀ i, 0 < w i) ∧
      ∀ p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) →
        ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ := by
  classical
  obtain ⟨x, hxinj, hprod⟩ := exists_injective_family_eq_prod hw n
  obtain ⟨w, hwval⟩ : ∃ w : Fin n → ℝ,
      ∀ i, w i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ := ⟨_, fun _ => rfl⟩
  have hxroot : ∀ i, (family μ n).eval (x i) = 0 := by
    intro i
    rw [hprod, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hcarduniv : (Finset.univ : Finset (Fin n)).card = n := by simp
  -- the rule is interpolatory, hence exact below the number of nodes
  have hlow : ∀ r : ℝ[X], r.degree < (n : WithBot ℕ) →
      ∑ i, w i * r.eval (x i) = ∫ t, r.eval t ∂μ := by
    intro r hr
    have heq : r = Lagrange.interpolate Finset.univ x fun i => r.eval (x i) :=
      Lagrange.eq_interpolate hxinj.injOn (by rw [hcarduniv]; exact hr)
    have hev : ∀ t : ℝ,
        r.eval t = ∑ i, r.eval (x i) * (Lagrange.basis Finset.univ x i).eval t := by
      intro t
      conv_lhs => rw [heq]
      rw [Lagrange.interpolate_apply, eval_finsetSum]
      exact Finset.sum_congr rfl fun i _ => by rw [eval_mul, eval_C]
    rw [integral_congr_ae (Filter.Eventually.of_forall hev),
      integral_finsetSum _ fun i _ => (hw.integrable_eval _).const_mul _]
    refine (Finset.sum_congr rfl fun i _ => ?_).symm
    rw [integral_const_mul, hwval i]
    ring
  -- division with remainder by the orthogonal polynomial doubles the reach
  have hexact : ∀ p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) →
      ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ := by
    intro p hp
    rcases eq_or_ne p 0 with rfl | hp0
    · simp
    have hmonic : (family μ n).Monic := monic_family μ n
    have hfamnat : (family μ n).natDegree = n :=
      natDegree_eq_of_degree_eq_some (degree_family μ n)
    have hnatp : p.natDegree < 2 * n := (natDegree_lt_iff_degree_lt hp0).mpr (by exact_mod_cast hp)
    obtain ⟨q, hqval⟩ : ∃ q : ℝ[X], q = p /ₘ family μ n := ⟨_, rfl⟩
    obtain ⟨r, hrval⟩ : ∃ r : ℝ[X], r = p %ₘ family μ n := ⟨_, rfl⟩
    have hdiv : r + family μ n * q = p := by
      rw [hrval, hqval]
      exact modByMonic_add_div p (family μ n)
    have hrdeg : r.degree < (n : WithBot ℕ) := by
      have h := degree_modByMonic_lt p hmonic
      rw [degree_family] at h
      rwa [hrval]
    have hqdeg : q.degree < (n : WithBot ℕ) := by
      have hqnat : q.natDegree = p.natDegree - n := by
        rw [hqval, natDegree_divByMonic p hmonic, hfamnat]
      refine lt_of_le_of_lt degree_le_natDegree ?_
      exact_mod_cast (by omega : q.natDegree < n)
    have hsplit : ∀ t : ℝ, p.eval t = r.eval t + (family μ n).eval t * q.eval t := by
      intro t
      conv_lhs => rw [← hdiv]
      rw [eval_add, eval_mul]
    have hint : ∫ t, p.eval t ∂μ = ∫ t, r.eval t ∂μ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
        integral_add (hw.integrable_eval r) (hw.integrable_eval_mul _ _),
        integral_family_mul_of_degree_lt hw hqdeg, add_zero]
    have hsum : ∑ i, w i * p.eval (x i) = ∑ i, w i * r.eval (x i) :=
      Finset.sum_congr rfl fun i _ => by rw [hsplit (x i), hxroot i]; ring
    rw [hsum, hlow r hrdeg, hint]
  refine ⟨x, w, hxinj, fun i => ?_, hexact⟩
  -- the weights are positive: apply exactness to the square of a Lagrange basis function
  have hne : Lagrange.basis Finset.univ x i ≠ 0 :=
    Lagrange.basis_ne_zero hxinj.injOn (Finset.mem_univ i)
  have hbnat : (Lagrange.basis Finset.univ x i).natDegree = n - 1 := by
    rw [Lagrange.natDegree_basis hxinj.injOn (Finset.mem_univ i), hcarduniv]
  have hn : 0 < n := Fin.pos i
  have hdeg2 : ((Lagrange.basis Finset.univ x i) ^ 2).degree < ((2 * n : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt degree_le_natDegree ?_
    rw [natDegree_pow, hbnat]
    exact_mod_cast (by omega : 2 * (n - 1) < 2 * n)
  have h1 := hexact _ hdeg2
  have hlhs : ∑ j, w j * ((Lagrange.basis Finset.univ x i) ^ 2).eval (x j) = w i := by
    rw [Finset.sum_eq_single i]
    · rw [eval_pow, Lagrange.eval_basis_self hxinj.injOn (Finset.mem_univ i)]
      ring
    · intro j _ hji
      rw [eval_pow, Lagrange.eval_basis_of_ne (Ne.symm hji) (Finset.mem_univ j)]
      ring
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hlhs] at h1
  rw [h1]
  exact hw.integral_eval_pos (pow_ne_zero 2 hne) fun t => by rw [eval_pow]; positivity

/-- **No `n`-point rule is exact to degree `2n`**: the square of the nodal polynomial is a
polynomial of degree `2n` that the rule evaluates to zero and the weight integrates to something
positive. Gauss quadrature is therefore optimal.

Reference: [kress1998numerical], §9.3. -/
theorem not_forall_eq_integral_of_degree_le (hw : IsWeight μ) {n : ℕ} (x w : Fin n → ℝ) :
    ¬ ∀ p : ℝ[X], p.degree ≤ ((2 * n : ℕ) : WithBot ℕ) →
      ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ := by
  classical
  intro h
  obtain ⟨q, hqval⟩ : ∃ q : ℝ[X], q = ∏ i, (X - C (x i)) := ⟨_, rfl⟩
  have hqmonic : q.Monic := by
    rw [hqval]
    exact monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)
  have hqnat : q.natDegree = n := by
    rw [hqval, natDegree_prod _ _ fun i _ => (monic_X_sub_C (x i)).ne_zero]
    simp
  have hdeg : (q ^ 2).degree ≤ ((2 * n : ℕ) : WithBot ℕ) := by
    refine degree_le_natDegree.trans ?_
    rw [natDegree_pow, hqnat]
  have hzero : ∀ i, q.eval (x i) = 0 := by
    intro i
    rw [hqval, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hlhs : ∑ i, w i * (q ^ 2).eval (x i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [eval_pow, hzero i]
    ring
  have hpos : 0 < ∫ t, (q ^ 2).eval t ∂μ :=
    hw.integral_eval_pos (pow_ne_zero 2 hqmonic.ne_zero) fun t => by rw [eval_pow]; positivity
  rw [← h _ hdeg, hlhs] at hpos
  exact absurd hpos (lt_irrefl 0)

end Gauss

/-! ### Exactness with respect to a weight -/

section ExactnessMeasure

open OrthogonalPolynomial Polynomial MeasureTheory

variable {μ : Measure ℝ} {n : ℕ}

/-- A rule with weights `w` at nodes `x` is **exact to degree `d` for the weight `μ`** when it
integrates every polynomial of degree at most `d` exactly against `μ`. This is the polynomial-level
degree of exactness of [quarteroni2000numerical] §10.2, stated for a measure on `ℝ` rather than
for a functional on `C(X, ℝ)` as `Quadrature.IsExactOn` is, so that it can host a weight of
unbounded support (the Laguerre and Hermite weights). -/
def IsExactOnMeasure (μ : Measure ℝ) {n : ℕ} (w x : Fin n → ℝ) (d : ℕ) : Prop :=
  ∀ p : ℝ[X], p.degree ≤ d → ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ

/-- Exactness to a degree implies exactness to every smaller degree. -/
theorem IsExactOnMeasure.mono {w x : Fin n → ℝ} {d e : ℕ} (h : IsExactOnMeasure μ w x d)
    (hed : e ≤ d) : IsExactOnMeasure μ w x e := fun p hp =>
  h p (hp.trans (by exact_mod_cast hed))

/-- `degree < d + 1` is `degree ≤ d`, for the degree of a polynomial. -/
private theorem degree_lt_succ_iff {p : ℝ[X]} {d : ℕ} :
    p.degree < ((d + 1 : ℕ) : WithBot ℕ) ↔ p.degree ≤ d := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [degree_eq_natDegree hp]
    exact_mod_cast Nat.lt_succ_iff

/-- Exactness to degree `d` in the strict form `degree < d + 1` used by `Quadrature.exists_gauss`.
-/
theorem isExactOnMeasure_iff_forall_degree_lt {w x : Fin n → ℝ} {d : ℕ} :
    IsExactOnMeasure μ w x d ↔ ∀ p : ℝ[X], p.degree < ((d + 1 : ℕ) : WithBot ℕ) →
      ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ :=
  forall_congr' fun _ => imp_congr_left degree_lt_succ_iff.symm

/-- A rule with `n + 1` nodes is **interpolatory for the weight `μ`** when its weights are the
integrals of the Lagrange basis polynomials of its nodes, so that the rule is the integral of the
Lagrange interpolant. This is [quarteroni2000numerical] (10.14), the measure-level twin of
`Quadrature.IsInterpolatory`. -/
def IsInterpolatoryMeasure (μ : Measure ℝ) (w x : Fin (n + 1) → ℝ) : Prop :=
  ∀ i, w i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ

/-- The value of a rule at a Lagrange basis polynomial of its own nodes is the corresponding
weight. -/
private theorem sum_mul_eval_basis {w x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (i : Fin (n + 1)) : ∑ j, w j * (Lagrange.basis Finset.univ x i).eval (x j) = w i := by
  rw [Finset.sum_eq_single i]
  · rw [Lagrange.eval_basis_self hx.injOn (Finset.mem_univ i), mul_one]
  · intro j _ hji
    rw [Lagrange.eval_basis_of_ne (Ne.symm hji) (Finset.mem_univ j), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **An `n + 1`-point rule at distinct nodes is interpolatory for `μ` exactly when it is exact to
degree `n` for `μ`.** Exactness applied to a Lagrange basis polynomial reads off the weight; and
conversely every polynomial of degree at most `n` is its own Lagrange interpolant.

Reference: [quarteroni2000numerical] §10.2, (10.14); [kress1998numerical] §9.1. -/
theorem isInterpolatoryMeasure_iff_isExactOnMeasure (hw : IsWeight μ) {w x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) : IsInterpolatoryMeasure μ w x ↔ IsExactOnMeasure μ w x n := by
  have hcard : (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by simp
  constructor
  · intro h p hp
    have heq : p = Lagrange.interpolate Finset.univ x fun i => p.eval (x i) :=
      Lagrange.eq_interpolate hx.injOn (by rw [hcard]; exact degree_lt_succ_iff.mpr hp)
    have hev : ∀ t : ℝ,
        p.eval t = ∑ i, p.eval (x i) * (Lagrange.basis Finset.univ x i).eval t := by
      intro t
      conv_lhs => rw [heq]
      rw [Lagrange.interpolate_apply, eval_finsetSum]
      exact Finset.sum_congr rfl fun i _ => by rw [eval_mul, eval_C]
    rw [integral_congr_ae (Filter.Eventually.of_forall hev),
      integral_finsetSum _ fun i _ => (hw.integrable_eval _).const_mul _]
    refine (Finset.sum_congr rfl fun i _ => ?_).symm
    rw [integral_const_mul, h i]
    ring
  · intro h i
    have hdeg : (Lagrange.basis Finset.univ x i).degree ≤ n := by
      rw [Lagrange.degree_basis hx.injOn (Finset.mem_univ i), hcard]
      simp
    rw [← h _ hdeg, sum_mul_eval_basis hx]

/-- Division with remainder by the nodal polynomial of `n + 1` nodes: a polynomial of degree at
most `n + m` is `ω q + r` with `q` of degree at most `m - 1` and `r` of degree at most `n`. -/
private theorem exists_nodal_mul_add {x : Fin (n + 1) → ℝ} {m : ℕ} (hm : 1 ≤ m) {p : ℝ[X]}
    (hp : p.degree ≤ ((n + m : ℕ) : WithBot ℕ)) :
    ∃ q r : ℝ[X], p = Lagrange.nodal Finset.univ x * q + r ∧
      q.degree ≤ ((m - 1 : ℕ) : WithBot ℕ) ∧ r.degree ≤ n := by
  have hmonic : (Lagrange.nodal Finset.univ x).Monic := Lagrange.nodal_monic
  have hnat : (Lagrange.nodal Finset.univ x).natDegree = n + 1 := by
    rw [Lagrange.natDegree_nodal]; simp
  refine ⟨p /ₘ Lagrange.nodal Finset.univ x, p %ₘ Lagrange.nodal Finset.univ x, ?_, ?_, ?_⟩
  · rw [add_comm]
    exact (modByMonic_add_div p _).symm
  · refine degree_le_natDegree.trans ?_
    rw [natDegree_divByMonic p hmonic, hnat]
    have hpnat : p.natDegree ≤ n + m := natDegree_le_iff_degree_le.mpr hp
    exact_mod_cast (by omega : p.natDegree - (n + 1) ≤ m - 1)
  · have h := degree_modByMonic_lt p hmonic
    rw [degree_eq_natDegree hmonic.ne_zero, hnat] at h
    exact degree_lt_succ_iff.mp h

/-- **Jacobi's theorem.** For `m ≥ 1`, a rule with `n + 1` distinct nodes is exact to degree
`n + m` for the weight `μ` if and only if it is interpolatory and its nodal polynomial
`ω = ∏ (X - x i)` is `μ`-orthogonal to every polynomial of degree at most `m - 1`.

Sufficiency: divide `f ∈ P_{n+m}` by the monic `ω`, `f = ω q + r` with `deg q ≤ m - 1` and
`deg r ≤ n`; the rule kills `ω q`, which vanishes at the nodes, the integral kills it by the
orthogonality, and on `r` an interpolatory rule is exact. Necessity: exactness to degree `n + m ≥
n` makes the rule interpolatory, and for `p ∈ P_{m-1}` the polynomial `ω p ∈ P_{n+m}` vanishes at
the nodes, so its integral is the value of the rule at it, namely `0`.

Reference: [quarteroni2000numerical] Theorem 10.1. -/
theorem isExactOnMeasure_add_iff (hw : IsWeight μ) {m : ℕ} (hm : 1 ≤ m)
    {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (w : Fin (n + 1) → ℝ) :
    IsExactOnMeasure μ w x (n + m) ↔
      IsInterpolatoryMeasure μ w x ∧ ∀ p : ℝ[X], p.degree ≤ ((m - 1 : ℕ) : WithBot ℕ) →
        ∫ t, (Lagrange.nodal Finset.univ x).eval t * p.eval t ∂μ = 0 := by
  have hroot : ∀ i, (Lagrange.nodal Finset.univ x).eval (x i) = 0 := fun i =>
    Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  have hnodaldeg : (Lagrange.nodal Finset.univ x).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [Lagrange.degree_nodal]; simp
  constructor
  · intro h
    refine ⟨(isInterpolatoryMeasure_iff_isExactOnMeasure hw hx).mpr (h.mono (by omega)),
      fun p hp => ?_⟩
    have hdeg : (Lagrange.nodal Finset.univ x * p).degree ≤ ((n + m : ℕ) : WithBot ℕ) := by
      refine (degree_mul_le _ _).trans ?_
      rw [hnodaldeg]
      calc ((n + 1 : ℕ) : WithBot ℕ) + p.degree
          ≤ ((n + 1 : ℕ) : WithBot ℕ) + ((m - 1 : ℕ) : WithBot ℕ) := by gcongr
        _ = ((n + m : ℕ) : WithBot ℕ) := by
            norm_cast
            omega
    have h2 : ∑ i, w i * (Lagrange.nodal Finset.univ x * p).eval (x i) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [eval_mul, hroot i]; ring
    calc ∫ t, (Lagrange.nodal Finset.univ x).eval t * p.eval t ∂μ
        = ∫ t, (Lagrange.nodal Finset.univ x * p).eval t ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun t => (eval_mul).symm)
      _ = 0 := (h _ hdeg).symm.trans h2
  · rintro ⟨hint, horth⟩ p hp
    obtain ⟨q, r, rfl, hq, hr⟩ := exists_nodal_mul_add (x := x) hm hp
    have hsum : ∑ i, w i * (Lagrange.nodal Finset.univ x * q + r).eval (x i) =
        ∑ i, w i * r.eval (x i) :=
      Finset.sum_congr rfl fun i _ => by rw [eval_add, eval_mul, hroot i]; ring
    have hev : ∀ t : ℝ, (Lagrange.nodal Finset.univ x * q + r).eval t =
        (Lagrange.nodal Finset.univ x).eval t * q.eval t + r.eval t := fun t => by
      rw [eval_add, eval_mul]
    rw [hsum, integral_congr_ae (Filter.Eventually.of_forall hev),
      integral_add (hw.integrable_eval_mul _ _) (hw.integrable_eval r), horth q hq, zero_add]
    exact (isInterpolatoryMeasure_iff_isExactOnMeasure hw hx).mp hint r hr

/-- **No rule with `n + 1` nodes is exact to degree `2n + 2`**; the Gauss rule's degree `2n + 1`
is the maximum. This is `Quadrature.not_forall_eq_integral_of_degree_le` restated.

Reference: [quarteroni2000numerical] Corollary 10.1. -/
theorem not_isExactOnMeasure_two_mul_add_two (hw : IsWeight μ) (w x : Fin (n + 1) → ℝ) :
    ¬ IsExactOnMeasure μ w x (2 * n + 2) := fun h =>
  not_forall_eq_integral_of_degree_le hw x w fun p hp =>
    h p (hp.trans (by exact_mod_cast (by omega : 2 * n + 2 ≤ 2 * (n + 1))))

/-- **The Gauss nodes are the roots of the orthogonal polynomial.** A rule with `n + 1` distinct
nodes is exact to degree `2n + 1` for the weight `μ` exactly when its nodal polynomial is the monic
orthogonal polynomial `family μ (n + 1)` — so that its nodes are the roots of that polynomial —
and it is interpolatory.

This is Jacobi's theorem at `m = n + 1`: a monic polynomial of degree `n + 1` orthogonal to every
polynomial of degree at most `n` differs from `family μ (n + 1)` by a polynomial of degree at most
`n` orthogonal to all of `P_n`, hence zero.

Reference: [quarteroni2000numerical] (10.16). -/
theorem isExactOnMeasure_two_mul_add_one_iff (hw : IsWeight μ) {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (w : Fin (n + 1) → ℝ) :
    IsExactOnMeasure μ w x (2 * n + 1) ↔
      Lagrange.nodal Finset.univ x = family μ (n + 1) ∧ IsInterpolatoryMeasure μ w x := by
  have hnodaldeg : (Lagrange.nodal Finset.univ x).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [Lagrange.degree_nodal]; simp
  have h2 : 2 * n + 1 = n + (n + 1) := by omega
  rw [h2, isExactOnMeasure_add_iff hw (by omega) hx w, Nat.add_sub_cancel, and_comm]
  refine and_congr_left fun _ => ⟨fun h => ?_, fun h p hp => ?_⟩
  · refine sub_eq_zero.mp (eq_zero_of_degree_lt hw (n := n + 1) ?_ ?_)
    · have := degree_sub_lt_left (p := Lagrange.nodal Finset.univ x) (q := family μ (n + 1))
        (by rw [hnodaldeg, degree_family]) Lagrange.nodal_ne_zero
        (by rw [Lagrange.nodal_monic.leadingCoeff, (monic_family μ (n + 1)).leadingCoeff])
      rwa [hnodaldeg] at this
    · intro k hk
      have hkdeg : (family μ k).degree ≤ n := by
        rw [degree_family]; exact_mod_cast Nat.lt_succ_iff.mp hk
      have hev : ∀ t : ℝ, (Lagrange.nodal Finset.univ x - family μ (n + 1)).eval t *
          (family μ k).eval t = (Lagrange.nodal Finset.univ x).eval t * (family μ k).eval t -
            (family μ (n + 1)).eval t * (family μ k).eval t := fun t => by
        rw [eval_sub, sub_mul]
      rw [integral_congr_ae (Filter.Eventually.of_forall hev),
        integral_sub (hw.integrable_eval_mul _ _) (hw.integrable_eval_mul _ _), h _ hkdeg,
        integral_family_mul_family hw (by omega), sub_zero]
  · rw [h]
    exact integral_family_mul_of_degree_lt hw (degree_lt_succ_iff.mpr hp)

/-- **The bridge to the functional level.** For a finite weight carried by `[a, b]`, nodes in
`[a, b]`, and `L` the functional `f ↦ ∫ f ∂μ` on `C([a, b], ℝ)`, exactness for `μ` at the
polynomial level is exactness for `L` in the sense of `Quadrature.IsExactOn`. This is what lets the
Szegő–Pólya criterion `Quadrature.tendsto_of_nonneg` apply to the Gauss and Gauss–Lobatto rules,
which are stated at the measure level. -/
theorem isExactOnMeasure_iff_isExactOn {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0)
    (w : Fin n → ℝ) (x : Fin n → Set.Icc a b) {L : C(Set.Icc a b, ℝ) →L[ℝ] ℝ}
    (hL : ∀ f : C(Set.Icc a b, ℝ), L f = ∫ t, f t ∂(μ.comap Subtype.val)) (d : ℕ) :
    IsExactOnMeasure μ w (Subtype.val ∘ x) d ↔ IsExactOn L w x d := by
  have hae : ∀ᵐ t ∂μ, t ∈ Set.Icc a b := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  have hint : ∀ P : ℝ[X], ∫ t : Set.Icc a b, P.eval (t : ℝ) ∂(μ.comap Subtype.val) =
      ∫ t, P.eval t ∂μ := by
    intro P
    have h1 := integral_subtype_comap (μ := μ) (s := Set.Icc a b) measurableSet_Icc
      fun t => P.eval t
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at h1
  constructor
  · intro h f hf
    obtain ⟨P, hP, hfP⟩ := mem_polyLE_iff.mp hf
    rw [functional_apply, hL]
    have hfun : (fun t : Set.Icc a b => f t) = fun t : Set.Icc a b => P.eval (t : ℝ) :=
      funext hfP
    rw [hfun, hint, ← h P hP]
    exact Finset.sum_congr rfl fun i _ => by rw [hfP]; rfl
  · intro h P hP
    have hmem : P.toContinuousMapOn (Set.Icc a b) ∈ polyLE (Set.Icc a b) d :=
      mem_polyLE_iff.mpr ⟨P, hP, fun t => by simp⟩
    have h1 := h _ hmem
    rw [functional_apply, hL] at h1
    simp only [Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply] at h1
    rw [hint] at h1
    exact h1

/-- **Change of interval.** A rule exact to degree `r` for `μ` transports along an affine map
`φ t = c * t + d` to a rule exact to degree `r` for the image measure `μ.map φ`, with nodes `φ ∘ x`
and the same weights: `p ∘ φ` is a polynomial of degree at most that of `p`.

Reference: [quarteroni2000numerical] Remark 10.3. -/
theorem isExactOnMeasure_map_affine {w x : Fin n → ℝ} {r : ℕ} (h : IsExactOnMeasure μ w x r)
    (c d : ℝ) :
    IsExactOnMeasure (μ.map fun t => c * t + d) w ((fun t => c * t + d) ∘ x) r := by
  intro p hp
  have hφ : Measurable fun t : ℝ => c * t + d := by fun_prop
  rw [integral_map hφ.aemeasurable p.continuous.aestronglyMeasurable]
  have hcomp : ∀ t : ℝ, p.eval (c * t + d) = (p.comp (C c * X + C d)).eval t := fun t => by
    simp [eval_comp]
  simp only [Function.comp_apply, hcomp]
  refine h _ ?_
  refine degree_le_natDegree.trans ?_
  rw [natDegree_comp]
  have h1 : (C c * X + C d : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
    exact (natDegree_C_mul_le _ _).trans (by simp)
  have h2 : p.natDegree ≤ r := natDegree_le_iff_degree_le.mpr hp
  exact_mod_cast (Nat.mul_le_mul h2 h1).trans (by omega)

/-- **Change of interval for Lebesgue measure**: a rule on `[-1, 1]` with nodes `ξ j` and weights
`β j`, exact to degree `r`, gives on `[a, b]` the rule with nodes `((b - a)/2) ξ j + (a + b)/2` and
weights `((b - a)/2) β j`, exact to the same degree.

Reference: [quarteroni2000numerical] Remark 10.3 (with the affine map corrected to
`φ(ξ) = ((b - a)/2) ξ + (a + b)/2`). -/
theorem isExactOnMeasure_volume_Icc_of_affine {a b : ℝ} (hab : a < b) {w x : Fin n → ℝ} {r : ℕ}
    (h : IsExactOnMeasure (volume.restrict (Set.Icc (-1 : ℝ) 1)) w x r) :
    IsExactOnMeasure (volume.restrict (Set.Icc a b)) (fun i => (b - a) / 2 * w i)
      (fun i => (b - a) / 2 * x i + (a + b) / 2) r := by
  intro p hp
  have hc : (b - a) / 2 ≠ 0 := by
    have : 0 < b - a := sub_pos.mpr hab
    positivity
  have hcomp : ∀ t : ℝ, p.eval ((b - a) / 2 * t + (a + b) / 2) =
      (p.comp (C ((b - a) / 2) * X + C ((a + b) / 2))).eval t := fun t => by simp [eval_comp]
  have hdeg : (p.comp (C ((b - a) / 2) * X + C ((a + b) / 2))).degree ≤ r := by
    refine degree_le_natDegree.trans ?_
    rw [natDegree_comp]
    have h1 : (C ((b - a) / 2) * X + C ((a + b) / 2) : ℝ[X]).natDegree ≤ 1 := by
      refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
      exact (natDegree_C_mul_le _ _).trans (by simp)
    have h2 : p.natDegree ≤ r := natDegree_le_iff_degree_le.mpr hp
    exact_mod_cast (Nat.mul_le_mul h2 h1).trans (by omega)
  have hrule := h _ hdeg
  simp only [hcomp]
  calc ∑ i, (b - a) / 2 * w i * (p.comp (C ((b - a) / 2) * X + C ((a + b) / 2))).eval (x i)
      = (b - a) / 2 * ∑ i, w i * (p.comp (C ((b - a) / 2) * X + C ((a + b) / 2))).eval (x i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = (b - a) / 2 * ∫ t in (-1 : ℝ)..1, p.eval ((b - a) / 2 * t + (a + b) / 2) := by
        rw [hrule, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        simp only [hcomp]
    _ = ∫ t in ((b - a) / 2 * (-1) + (a + b) / 2)..((b - a) / 2 * 1 + (a + b) / 2), p.eval t := by
        rw [← intervalIntegral.smul_integral_comp_mul_add, smul_eq_mul]
    _ = ∫ t in Set.Icc a b, p.eval t := by
        rw [show (b - a) / 2 * (-1) + (a + b) / 2 = a by ring,
          show (b - a) / 2 * 1 + (a + b) / 2 = b by ring, intervalIntegral.integral_of_le hab.le,
          integral_Icc_eq_integral_Ioc]

end ExactnessMeasure

/-! ### The discrete inner product -/

section DiscreteInner

open OrthogonalPolynomial Polynomial MeasureTheory

variable {μ : Measure ℝ} {n : ℕ}

/-- **The discrete inner product** of a rule: `(f, g)_n = ∑ i, w i * f (x i) * g (x i)`, the rule
applied to the product `f g`. It is a symmetric bilinear form, positive semidefinite for positive
weights, and an inner product on the polynomials of degree less than the number of distinct nodes
(`Quadrature.discreteInner_self_pos`).

Reference: [quarteroni2000numerical] (10.28), (10.51). -/
def discreteInner (w x : Fin n → ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∑ i, w i * f (x i) * g (x i)

theorem discreteInner_comm (w x : Fin n → ℝ) (f g : ℝ → ℝ) :
    discreteInner w x f g = discreteInner w x g f :=
  Finset.sum_congr rfl fun i _ => by ring

theorem discreteInner_add_left (w x : Fin n → ℝ) (f₁ f₂ g : ℝ → ℝ) :
    discreteInner w x (f₁ + f₂) g = discreteInner w x f₁ g + discreteInner w x f₂ g := by
  simp only [discreteInner, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem discreteInner_smul_left (w x : Fin n → ℝ) (c : ℝ) (f g : ℝ → ℝ) :
    discreteInner w x (c • f) g = c * discreteInner w x f g := by
  simp only [discreteInner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem discreteInner_sum_left (w x : Fin n → ℝ) {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (g : ℝ → ℝ) : discreteInner w x (∑ k ∈ s, f k) g = ∑ k ∈ s, discreteInner w x (f k) g := by
  simp only [discreteInner, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The discrete inner product only sees the values at the nodes. -/
theorem discreteInner_congr (w x : Fin n → ℝ) {f f' g g' : ℝ → ℝ} (hf : ∀ i, f (x i) = f' (x i))
    (hg : ∀ i, g (x i) = g' (x i)) : discreteInner w x f g = discreteInner w x f' g' :=
  Finset.sum_congr rfl fun i _ => by rw [hf i, hg i]

/-- For nonnegative weights the discrete inner product of a function with itself is nonnegative. -/
theorem discreteInner_self_nonneg {w x : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i) (f : ℝ → ℝ) :
    0 ≤ discreteInner w x f f :=
  Finset.sum_nonneg fun i _ => by rw [mul_assoc, ← sq]; exact mul_nonneg (hw i) (sq_nonneg _)

/-- **The discrete inner product is an inner product on the polynomials of degree less than the
number of nodes**: for positive weights at distinct nodes, `(p, p)_n > 0` for every nonzero
polynomial `p` of degree `< n`, since such a polynomial cannot vanish at all `n` nodes.

Reference: [quarteroni2000numerical] Exercise 10.4. -/
theorem discreteInner_self_pos {w x : Fin n → ℝ} (hw : ∀ i, 0 < w i) (hx : Function.Injective x)
    {p : ℝ[X]} (hp : p ≠ 0) (hdeg : p.degree < n) :
    0 < discreteInner w x (fun t => p.eval t) fun t => p.eval t := by
  classical
  have hne : ∃ i, p.eval (x i) ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hp (Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ hx.injOn
      (by simpa using hdeg) fun i _ => hall i)
  obtain ⟨i, hi⟩ := hne
  refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · rw [mul_assoc, ← sq]; exact mul_nonneg (hw j).le (sq_nonneg _)
  · rw [mul_assoc, ← sq]; exact mul_pos (hw i) (by positivity)

/-- The discrete inner product of two polynomials agrees with the weighted `L²(μ)` inner product
as long as the rule integrates their product exactly. -/
theorem discreteInner_eq_integral_of_degree_le {w x : Fin n → ℝ} {d : ℕ}
    (h : IsExactOnMeasure μ w x d) {p q : ℝ[X]} (hpq : p.degree + q.degree ≤ d) :
    discreteInner w x (fun t => p.eval t) (fun t => q.eval t) = ∫ t, p.eval t * q.eval t ∂μ := by
  rw [← degree_mul] at hpq
  have h1 := h _ hpq
  simp only [eval_mul] at h1
  rw [← h1]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Discrete orthogonality.** For a rule with `n + 1` nodes exact to degree `2n - 1`, the monic
orthogonal polynomials `p_0, …, p_n` of the weight are orthogonal for the discrete inner product:
`(p_j, p_k)_n = 0` for `j ≠ k` with `j, k ≤ n`, because `p_j p_k` then has degree at most
`2n - 1`. The rule need not integrate `p_n²` exactly, and `(p_n, p_n)_n` is where the Gauss and
Gauss–Lobatto rules differ.

Reference: [quarteroni2000numerical] §10.1, §10.3. -/
theorem discreteInner_family_family (hw : IsWeight μ) (hn : 1 ≤ n) {w x : Fin (n + 1) → ℝ}
    (hexact : IsExactOnMeasure μ w x (2 * n - 1)) {j k : ℕ} (hjk : j ≠ k) (hj : j ≤ n)
    (hk : k ≤ n) :
    discreteInner w x (fun t => (family μ j).eval t) (fun t => (family μ k).eval t) = 0 := by
  rw [discreteInner_eq_integral_of_degree_le hexact, integral_family_mul_family hw hjk]
  rw [degree_family, degree_family]
  norm_cast
  omega

/-- The discrete norm of `p_k` for `k < n` is its `L²(μ)` norm: the rule integrates `p_k²` exactly.
-/
theorem discreteInner_family_self (hn : 1 ≤ n) {w x : Fin (n + 1) → ℝ}
    (hexact : IsExactOnMeasure μ w x (2 * n - 1)) {k : ℕ} (hk : k < n) :
    discreteInner w x (fun t => (family μ k).eval t) (fun t => (family μ k).eval t) =
      normSq μ k := by
  rw [discreteInner_eq_integral_of_degree_le hexact, normSq]
  · exact integral_congr_ae (Filter.Eventually.of_forall fun t => (sq _).symm)
  · rw [degree_family]
    norm_cast
    omega

/-- **The interpolant at the nodes of a rule is the discrete truncation of the orthogonal
expansion.** For a rule with `n + 1` distinct nodes, positive weights and degree of exactness
`2n - 1`, the Lagrange interpolant of `f` at the nodes is `∑_{k ≤ n} f̃_k p_k` with the discrete
Fourier coefficients `f̃_k = (f, p_k)_n / (p_k, p_k)_n`: expand the interpolant in the basis
`p_0, …, p_n` of `P_n` and pair with `p_j` in the discrete inner product, where the basis is
orthogonal by `Quadrature.discreteInner_family_family` and the interpolant agrees with `f` at the
nodes.

Reference: [quarteroni2000numerical] (10.4)–(10.5), (10.29), (10.38), §10.7. -/
theorem interpolate_eq_sum_discreteInner_smul (hw : IsWeight μ) (hn : 1 ≤ n)
    {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) {w : Fin (n + 1) → ℝ} (hwpos : ∀ i, 0 < w i)
    (hexact : IsExactOnMeasure μ w x (2 * n - 1)) (f : ℝ → ℝ) :
    Lagrange.interpolate Finset.univ x (fun i => f (x i)) =
      ∑ k : Fin (n + 1),
        C (discreteInner w x f (fun t => (family μ k).eval t) /
            discreteInner w x (fun t => (family μ k).eval t) (fun t => (family μ k).eval t)) *
          family μ k := by
  classical
  set P : ℝ[X] := Lagrange.interpolate Finset.univ x (fun i => f (x i)) with hP
  have hPdeg : P.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin (n + 1))))
      (r := fun i => f (x i)) hx.injOn
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hPnode : ∀ i, P.eval (x i) = f (x i) := fun i =>
    Lagrange.eval_interpolate_at_node _ hx.injOn (Finset.mem_univ i)
  obtain ⟨c, hc⟩ := exists_eq_sum_family μ hPdeg
  have hcoeff : ∀ j : Fin (n + 1), c j =
      discreteInner w x f (fun t => (family μ j).eval t) /
        discreteInner w x (fun t => (family μ j).eval t) (fun t => (family μ j).eval t) := by
    intro j
    have hpos : 0 < discreteInner w x (fun t => (family μ j).eval t)
        (fun t => (family μ j).eval t) :=
      discreteInner_self_pos hwpos hx (family_ne_zero μ j)
        (by rw [degree_family]; exact_mod_cast j.2)
    rw [eq_div_iff hpos.ne']
    have h1 : discreteInner w x (fun t => P.eval t) (fun t => (family μ j).eval t) =
        discreteInner w x f (fun t => (family μ j).eval t) :=
      discreteInner_congr w x (fun i => hPnode i) fun _ => rfl
    rw [← h1, hc]
    have hev : (fun t => (∑ k ∈ Finset.range (n + 1), c k • family μ k).eval t) =
        ∑ k ∈ Finset.range (n + 1), c k • fun t => (family μ k).eval t := by
      funext t
      simp [eval_finsetSum]
    rw [hev, discreteInner_sum_left, Finset.sum_eq_single (j : ℕ)]
    · rw [discreteInner_smul_left]
    · intro k hk hkj
      rw [discreteInner_smul_left,
        discreteInner_family_family hw hn hexact hkj (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
          (Nat.lt_succ_iff.mp j.2), mul_zero]
    · intro hj
      exact absurd (Finset.mem_range.mpr j.2) hj
  rw [hc, ← Fin.sum_univ_eq_sum_range (fun k => c k • family μ k) (n + 1)]
  exact Finset.sum_congr rfl fun j _ => by rw [hcoeff j, smul_eq_C_mul]

end DiscreteInner

/-! ### The Gauss remainder -/

section GaussError

open OrthogonalPolynomial Polynomial MeasureTheory

variable {μ : Measure ℝ}

/-- A continuous function is integrable for a finite measure carried by a compact interval. -/
private theorem integrable_of_continuous_of_compl_eq_zero [IsFiniteMeasure μ] {a b : ℝ}
    (hsupp : μ (Set.Icc a b)ᶜ = 0) {f : ℝ → ℝ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hf).isBounded.exists_norm_le
  refine Integrable.mono' (integrable_const C) hf.aestronglyMeasurable ?_
  have hae : ∀ᵐ t ∂μ, t ∈ Set.Icc a b := by
    rw [MeasureTheory.ae_iff]
    exact hsupp
  filter_upwards [hae] with t ht
  exact hC _ ⟨t, ht, rfl⟩

/-- A function that is nonnegative on a carrier `s` of the weight `μ` and vanishes there only at
roots of a nonzero polynomial `p` has nonzero integral against `μ`: were the integral zero, the
function would vanish `μ`-almost everywhere, so the complement of the finite root set of `p` would
be `μ`-null, which no weight allows. -/
private theorem integral_ne_zero_of_ne_zero_off_roots (hw : IsWeight μ) {s : Set ℝ}
    (hsupp : μ sᶜ = 0) {p : ℝ[X]} (hp : p ≠ 0) {g : ℝ → ℝ} (hgint : Integrable g μ)
    (hg : ∀ t ∈ s, 0 ≤ g t) (hgne : ∀ t ∈ s, p.eval t ≠ 0 → g t ≠ 0) :
    ∫ t, g t ∂μ ≠ 0 := by
  intro h0
  have hae : ∀ᵐ t ∂μ, t ∈ s := by
    rw [MeasureTheory.ae_iff]; exact hsupp
  have hae0 : 0 ≤ᵐ[μ] g := by filter_upwards [hae] with t ht using hg t ht
  have hzero : g =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hae0 hgint).mp h0
  have hmeas : μ {t | g t ≠ 0} = 0 := by
    have hz := hzero
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at hz
    simpa using hz
  refine hw.measure_compl_ne_zero (Polynomial.finite_setOfPred_isRoot hp) ?_
  refine measure_mono_null (fun t ht => ?_) (measure_union_null hmeas hsupp)
  by_cases hts : t ∈ s
  · exact Or.inl (hgne t hts ht)
  · exact Or.inr hts

/-- **The Gauss remainder on an arbitrary interval.** Let `μ` be a weight carried by a convex set
`s ⊆ ℝ` (`μ sᶜ = 0`), let `x : Fin n → ℝ` be distinct nodes in `s` and `w` weights whose rule is
exact on the polynomials of degree less than `2n` — the Gauss rule of `Quadrature.exists_gauss` —
and let `f` be `μ`-integrable of class `C^{2n}`. Then

`(∫ f ∂μ) - ∑ i, w i * f (x i) = f^{(2n)}(ξ) / (2n)! * ∫ p_n² ∂μ`

for some `ξ ∈ s`, where `p_n = family μ n` is the nodal polynomial of the rule.

`Quadrature.exists_gauss_error_eq` is the special case of a compact carrier `[a, b]`, where the
integrability of `f` comes for free; here neither the carrier nor `f^{(2n)}` need be bounded, which
is what the Laguerre weight on `(0, ∞)` and the Hermite weight on `ℝ` require. The rule is exact
on the Hermite
interpolant `H` of `f` with double nodes at the `x i`, whose degree is less than `2n` and which
agrees with `f` at the nodes, so the error is `∫ (f - H) ∂μ`; and
`Hermite.exists_sub_interpolate_eq`, applied on the compact interval spanned by `t` and the nodes,
writes `f t - H t = f^{(2n)}(ξ_t)/(2n)! · p_n(t)²` for `t ∈ s`. Writing `c` for the error divided
by `∫ p_n² ∂μ`, the function `f - H - c p_n²` has zero integral; if `f^{(2n)}/(2n)!` were
everywhere above `c` on `s` that function would be nonnegative on `s` and nonzero off the roots of
`p_n`, which `integral_ne_zero_of_ne_zero_off_roots` forbids, and symmetrically below `c`. The
intermediate value theorem on the interval joining the two witnesses produces `ξ`.

Reference: [quarteroni2000numerical] (10.41)–(10.42); [kress1998numerical] §9.3. -/
theorem exists_gauss_error_eq_of_convex (hw : IsWeight μ) {s : Set ℝ} (hs : Convex ℝ s)
    (hsupp : μ sᶜ = 0) {n : ℕ} {x w : Fin n → ℝ} (hx : Function.Injective x)
    (hxmem : ∀ i, x i ∈ s)
    (hexact : ∀ p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) →
      ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) f) (hfint : Integrable f μ) :
    ∃ ξ ∈ s, (∫ t, f t ∂μ) - ∑ i, w i * f (x i) =
      iteratedDeriv (2 * n) f ξ / (2 * n).factorial * normSq μ n := by
  classical
  have := hw.isFiniteMeasure
  set D : ℝ → ℝ := fun ξ => iteratedDeriv (2 * n) f ξ / (2 * n).factorial with hD
  have hDcont : Continuous D := (hf.continuous_iteratedDeriv (2 * n) le_rfl).div_const _
  set H : ℝ[X] := Hermite.interpolate x (fun _ => 1) f with hH
  have hHdeg : H.degree < ((2 * n : ℕ) : WithBot ℕ) := by
    have hd := Hermite.degree_interpolate_lt hx (fun _ => 1) f
    simpa [Finset.sum_const, mul_comm] using hd
  have hHnode : ∀ i, H.eval (x i) = f (x i) := by
    intro i
    have hi := Hermite.eval_iterate_derivative_interpolate (f := f) (m := fun _ => 1) hx i
      (Nat.zero_le 1)
    simpa using hi
  have hint_H : Integrable (fun t => H.eval t) μ := hw.integrable_eval H
  have hIpos : 0 < normSq μ n := normSq_pos hw n
  -- the error is the integral of `f - H`
  have hsum : ∑ i, w i * f (x i) = ∫ t, H.eval t ∂μ := by
    rw [← hexact H hHdeg]
    exact Finset.sum_congr rfl fun i _ => by rw [hHnode i]
  have hint_fH : Integrable (fun t => f t - H.eval t) μ := hfint.sub hint_H
  have hEeq : (∫ t, f t ∂μ) - ∑ i, w i * f (x i) = ∫ t, (f t - H.eval t) ∂μ := by
    rw [hsum, ← integral_sub hfint hint_H]
  set c : ℝ := ((∫ t, f t ∂μ) - ∑ i, w i * f (x i)) / normSq μ n with hcdef
  have hc : (∫ t, f t ∂μ) - ∑ i, w i * f (x i) = c * normSq μ n := by
    rw [hcdef, div_mul_cancel₀ _ hIpos.ne']
  -- the pointwise error formula, on the compact interval spanned by `t` and the nodes
  have hpt : ∀ t ∈ s, ∃ ξ ∈ s, f t - H.eval t = D ξ * (family μ n).eval t ^ 2 := by
    intro t ht
    cases n with
    | zero =>
      refine ⟨t, ht, ?_⟩
      have hH0 : H = 0 := by
        rw [← degree_eq_bot]
        exact Nat.WithBot.lt_zero_iff.mp (by simpa using hHdeg)
      simp [hH0, hD]
    | succ m =>
      obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x
      obtain ⟨i₁, -, hi₁⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
      set a : ℝ := min t (x i₀) with ha
      set b : ℝ := max t (x i₁) with hb
      have hamem : a ∈ s := by
        rcases min_cases t (x i₀) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [ha, h]
        · exact ht
        · exact hxmem i₀
      have hbmem : b ∈ s := by
        rcases max_cases t (x i₁) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [hb, h]
        · exact ht
        · exact hxmem i₁
      have hsub : Set.Icc a b ⊆ s := hs.ordConnected.out hamem hbmem
      have htmem : t ∈ Set.Icc a b := ⟨min_le_left _ _, le_max_left _ _⟩
      have hxmem' : ∀ i, x i ∈ Set.Icc a b := by
        intro i
        refine ⟨le_trans (min_le_right _ _) ?_, le_trans ?_ (le_max_right _ _)⟩
        · rw [← hi₀]; exact Finset.inf'_le _ (Finset.mem_univ i)
        · rw [← hi₁]; exact Finset.le_sup' _ (Finset.mem_univ i)
      have hf' : ContDiff ℝ ((2 * m + 1 + 1 : ℕ) : WithTop ℕ∞) f := by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]; exact hf
      obtain ⟨ξ, hξ, hξeq⟩ := Hermite.exists_sub_interpolate_eq (N := 2 * m + 1) hf' hx hxmem'
        (m := fun _ => 1) (by simp; ring) htmem
      refine ⟨ξ, hsub hξ, ?_⟩
      have hnodal : Lagrange.nodal Finset.univ x = family μ (m + 1) :=
        ((isExactOnMeasure_two_mul_add_one_iff hw hx w).mp
          (isExactOnMeasure_iff_forall_degree_lt.mpr
            (by rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]; exact hexact))).1
      rw [hξeq, ← hnodal, Lagrange.eval_nodal, hD]
      simp only [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, Finset.prod_pow]
  -- the error minus `c` times `∫ p_n²` integrates to zero
  have hsqint : Integrable (fun t => c * (family μ n).eval t ^ 2) μ :=
    (hw.integrable_eval_sq _).const_mul c
  have hgint : Integrable (fun t => f t - H.eval t - c * (family μ n).eval t ^ 2) μ :=
    hint_fH.sub hsqint
  have hIeq : ∫ t, c * (family μ n).eval t ^ 2 ∂μ = c * normSq μ n := by
    rw [integral_const_mul]; rfl
  have hgzero : ∫ t, (f t - H.eval t - c * (family μ n).eval t ^ 2) ∂μ = 0 := by
    rw [integral_sub hint_fH hsqint, hIeq, ← hEeq, hc, sub_self]
  -- the scaled top derivative takes values on both sides of `c`
  have hA : ∃ ξ ∈ s, D ξ ≤ c := by
    by_contra hcon
    push Not at hcon
    refine integral_ne_zero_of_ne_zero_off_roots hw hsupp (family_ne_zero μ n) hgint ?_ ?_ hgzero
    · intro t ht
      obtain ⟨ξ, hξ, hξeq⟩ := hpt t ht
      have h1 : 0 ≤ (D ξ - c) * (family μ n).eval t ^ 2 :=
        mul_nonneg (by linarith [hcon ξ hξ]) (sq_nonneg _)
      rw [sub_mul] at h1
      rw [hξeq]
      linarith
    · intro t ht hnz
      obtain ⟨ξ, hξ, hξeq⟩ := hpt t ht
      have h1 : 0 < (D ξ - c) * (family μ n).eval t ^ 2 :=
        mul_pos (by linarith [hcon ξ hξ])
          (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hnz)))
      rw [sub_mul] at h1
      rw [hξeq]
      exact ne_of_gt (by linarith)
  have hB : ∃ ξ ∈ s, c ≤ D ξ := by
    by_contra hcon
    push Not at hcon
    have hgzero' : ∫ t, -(f t - H.eval t - c * (family μ n).eval t ^ 2) ∂μ = 0 := by
      rw [integral_neg, hgzero, neg_zero]
    have hgintneg : Integrable (fun t => -(f t - H.eval t - c * (family μ n).eval t ^ 2)) μ :=
      hgint.neg
    refine integral_ne_zero_of_ne_zero_off_roots hw hsupp (family_ne_zero μ n) hgintneg ?_ ?_
      hgzero'
    · intro t ht
      obtain ⟨ξ, hξ, hξeq⟩ := hpt t ht
      have h1 : 0 ≤ (c - D ξ) * (family μ n).eval t ^ 2 :=
        mul_nonneg (by linarith [hcon ξ hξ]) (sq_nonneg _)
      rw [sub_mul] at h1
      rw [hξeq]
      linarith
    · intro t ht hnz
      obtain ⟨ξ, hξ, hξeq⟩ := hpt t ht
      have h1 : 0 < (c - D ξ) * (family μ n).eval t ^ 2 :=
        mul_pos (by linarith [hcon ξ hξ])
          (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hnz)))
      rw [sub_mul] at h1
      rw [hξeq]
      exact ne_of_gt (by linarith)
  obtain ⟨ξ₁, hξ₁, hle₁⟩ := hA
  obtain ⟨ξ₂, hξ₂, hle₂⟩ := hB
  have hmem : c ∈ Set.uIcc (D ξ₁) (D ξ₂) := Set.mem_uIcc.mpr (Or.inl ⟨hle₁, hle₂⟩)
  obtain ⟨ξ, hξmem, hξeq⟩ := intermediate_value_uIcc hDcont.continuousOn hmem
  refine ⟨ξ, hs.ordConnected.uIcc_subset hξ₁ hξ₂ hξmem, ?_⟩
  change _ = D ξ * normSq μ n
  rw [hξeq, hcdef, div_mul_cancel₀ _ hIpos.ne']

/-- **The Gauss remainder on a compact interval.** For a weight carried by `[a, b]`, an `n`-point
rule at distinct nodes of `[a, b]` exact on the polynomials of degree less than `2n` — the Gauss
rule of `Quadrature.exists_gauss` — and an integrand `f` of class `C^{2n}`, the error is
`f^{(2n)}(ξ) / (2n)! · ∫ p_n² ∂μ` for some `ξ ∈ [a, b]`, where `p_n = family μ n` is the nodal
polynomial of the rule. At `n = 0` the statement is the mean value theorem for integrals.

The case `s = [a, b]` of `Quadrature.exists_gauss_error_eq_of_convex`: a compact carrier is the one
case in which the integrability of `f` needs no hypothesis, being what that statement asks for in
addition.

Reference: [quarteroni2000numerical] (10.41)–(10.42); [kress1998numerical] §9.3. -/
theorem exists_gauss_error_eq (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0)
    {n : ℕ} {x w : Fin n → ℝ} (hx : Function.Injective x) (hxmem : ∀ i, x i ∈ Set.Icc a b)
    (hexact : ∀ p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) →
      ∑ i, w i * p.eval (x i) = ∫ t, p.eval t ∂μ)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) f) :
    ∃ ξ ∈ Set.Icc a b, (∫ t, f t ∂μ) - ∑ i, w i * f (x i) =
      iteratedDeriv (2 * n) f ξ / (2 * n).factorial * normSq μ n := by
  have := hw.isFiniteMeasure
  exact exists_gauss_error_eq_of_convex hw (convex_Icc a b) hsupp hx hxmem hexact hf
    (integrable_of_continuous_of_compl_eq_zero hsupp hf.continuous)

end GaussError


/-! ### Peano's kernel theorem -/

section Peano

open MeasureTheory

variable {F : ℕ → ℝ → ℝ}

/-- The telescoping sum behind Taylor's formula with the integral remainder: for a chain of
derivatives `F 0, F 1, …, F (m + 1)` the function `s ↦ ∑_{k ≤ m} F k s (v - s)^k / k!` has
derivative `(v - t)^m F (m + 1) t / m!` at `t`, every other term cancelling against its
neighbour. -/
private theorem hasDerivAt_taylorSum {v x : ℝ} :
    ∀ m : ℕ, (∀ k ≤ m, HasDerivAt (F k) (F (k + 1) x) x) →
      HasDerivAt (fun t => ∑ k ∈ Finset.range (m + 1), F k t * (v - t) ^ k / (k.factorial : ℝ))
        ((v - x) ^ m / (m.factorial : ℝ) * F (m + 1) x) x := by
  have hvt : HasDerivAt (fun t : ℝ => v - t) (-1) x := (hasDerivAt_id x).const_sub v
  intro m
  induction m with
  | zero =>
    intro hF
    simpa using hF 0 le_rfl
  | succ m ih =>
    intro hF
    have h1 := ih fun k hk => hF k (by omega)
    have h2 : HasDerivAt (fun t => F (m + 1) t * (v - t) ^ (m + 1) / ((m + 1).factorial : ℝ))
        ((F (m + 1 + 1) x * (v - x) ^ (m + 1)
            + F (m + 1) x * ((m + 1 : ℕ) * (v - x) ^ m * (-1))) / ((m + 1).factorial : ℝ)) x :=
      ((hF (m + 1) le_rfl).mul (hvt.pow (m + 1))).div_const _
    have h3 : HasDerivAt
        (fun t => (∑ k ∈ Finset.range (m + 1), F k t * (v - t) ^ k / (k.factorial : ℝ))
          + F (m + 1) t * (v - t) ^ (m + 1) / ((m + 1).factorial : ℝ))
        ((v - x) ^ m / (m.factorial : ℝ) * F (m + 1) x
          + (F (m + 1 + 1) x * (v - x) ^ (m + 1)
              + F (m + 1) x * ((m + 1 : ℕ) * (v - x) ^ m * (-1))) /
            ((m + 1).factorial : ℝ)) x := h1.add h2
    have hsplit : (fun t => ∑ k ∈ Finset.range (m + 1 + 1), F k t * (v - t) ^ k / (k.factorial : ℝ))
        = fun t => (∑ k ∈ Finset.range (m + 1), F k t * (v - t) ^ k / (k.factorial : ℝ))
          + F (m + 1) t * (v - t) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
      funext t
      rw [Finset.sum_range_succ]
    rw [hsplit]
    convert h3 using 1
    have hfac : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hne : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    rw [hfac]
    push_cast
    field_simp
    ring

/-- The telescoping sum behind the *integrated* Taylor formula: `s ↦ ∑_{k ≤ m} F k s (b - s)^{k+1} /
(k+1)!` has derivative `(b - t)^{m+1} F (m + 1) t / (m + 1)! - F 0 t`.  Integrating it over `[a, b]`
gives `∫_a^b F 0` as the integral of the Taylor polynomial plus a single remainder integral, with no
Fubini step. -/
private theorem hasDerivAt_integratedTaylorSum {b x : ℝ} :
    ∀ m : ℕ, (∀ k ≤ m, HasDerivAt (F k) (F (k + 1) x) x) →
      HasDerivAt
        (fun t => ∑ k ∈ Finset.range (m + 1),
          F k t * (b - t) ^ (k + 1) / ((k + 1).factorial : ℝ))
        ((b - x) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) x - F 0 x) x := by
  have hvt : HasDerivAt (fun t : ℝ => b - t) (-1) x := (hasDerivAt_id x).const_sub b
  intro m
  induction m with
  | zero =>
    intro hF
    have hsplit : (fun t => ∑ k ∈ Finset.range (0 + 1),
          F k t * (b - t) ^ (k + 1) / ((k + 1).factorial : ℝ))
        = fun t => F 0 t * (b - t) ^ (0 + 1) / ((0 + 1).factorial : ℝ) := by
      funext t
      rw [Finset.sum_range_one]
    have h : HasDerivAt (fun t => F 0 t * (b - t) ^ (0 + 1) / ((0 + 1).factorial : ℝ))
        ((F (0 + 1) x * (b - x) ^ (0 + 1)
            + F 0 x * ((0 + 1 : ℕ) * (b - x) ^ 0 * (-1))) / ((0 + 1).factorial : ℝ)) x :=
      ((hF 0 le_rfl).mul (hvt.pow (0 + 1))).div_const _
    rw [hsplit]
    convert h using 1
    have hfac : ((0 + 1).factorial : ℝ) = 1 := by norm_num
    rw [hfac]
    push_cast
    ring
  | succ m ih =>
    intro hF
    have h1 := ih fun k hk => hF k (by omega)
    have h2 : HasDerivAt
        (fun t => F (m + 1) t * (b - t) ^ (m + 1 + 1) / ((m + 1 + 1).factorial : ℝ))
        ((F (m + 1 + 1) x * (b - x) ^ (m + 1 + 1)
            + F (m + 1) x * ((m + 1 + 1 : ℕ) * (b - x) ^ (m + 1) * (-1))) /
          ((m + 1 + 1).factorial : ℝ)) x :=
      ((hF (m + 1) le_rfl).mul (hvt.pow (m + 1 + 1))).div_const _
    have h3 : HasDerivAt
        (fun t => (∑ k ∈ Finset.range (m + 1),
            F k t * (b - t) ^ (k + 1) / ((k + 1).factorial : ℝ))
          + F (m + 1) t * (b - t) ^ (m + 1 + 1) / ((m + 1 + 1).factorial : ℝ))
        (((b - x) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) x - F 0 x)
          + (F (m + 1 + 1) x * (b - x) ^ (m + 1 + 1)
              + F (m + 1) x * ((m + 1 + 1 : ℕ) * (b - x) ^ (m + 1) * (-1))) /
            ((m + 1 + 1).factorial : ℝ)) x := h1.add h2
    have hsplit : (fun t => ∑ k ∈ Finset.range (m + 1 + 1),
          F k t * (b - t) ^ (k + 1) / ((k + 1).factorial : ℝ))
        = fun t => (∑ k ∈ Finset.range (m + 1),
            F k t * (b - t) ^ (k + 1) / ((k + 1).factorial : ℝ))
          + F (m + 1) t * (b - t) ^ (m + 1 + 1) / ((m + 1 + 1).factorial : ℝ) := by
      funext t
      rw [Finset.sum_range_succ]
    rw [hsplit]
    convert h3 using 1
    have hfac : ((m + 1 + 1).factorial : ℝ) = ((m : ℝ) + 1 + 1) * ((m + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hne : ((m + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (m + 1))
    rw [hfac]
    push_cast
    field_simp
    ring

/-- **Taylor's formula with the integral remainder**, for a chain of derivatives on an interval:
`F 0 v = ∑_{k ≤ m} F k u (v - u)^k / k! + ∫_u^v (v - t)^m F (m + 1) t / m! dt`.

This is Mathlib's `taylor_integral_remainder` in the derivative-family form the quadrature
statements use, and it is proved from the telescoping identity above rather than by `m + 1`
integrations by parts. -/
theorem eq_taylorSum_add_integral {u v : ℝ} {m : ℕ}
    (hF : ∀ k ≤ m, ∀ t ∈ Set.uIcc u v, HasDerivAt (F k) (F (k + 1) t) t)
    (hint : IntervalIntegrable (F (m + 1)) volume u v) :
    F 0 v = (∑ k ∈ Finset.range (m + 1), F k u * (v - u) ^ k / (k.factorial : ℝ))
      + ∫ t in u..v, (v - t) ^ m / (m.factorial : ℝ) * F (m + 1) t := by
  have hΦ : ∀ t ∈ Set.uIcc u v,
      HasDerivAt (fun s => ∑ k ∈ Finset.range (m + 1), F k s * (v - s) ^ k / (k.factorial : ℝ))
        ((v - t) ^ m / (m.factorial : ℝ) * F (m + 1) t) t :=
    fun t ht => hasDerivAt_taylorSum m fun k hk => hF k hk t ht
  have hi : IntervalIntegrable
      (fun t => (v - t) ^ m / (m.factorial : ℝ) * F (m + 1) t) volume u v :=
    hint.continuousOn_mul (by fun_prop)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hΦ hi
  have hv : (∑ k ∈ Finset.range (m + 1), F k v * (v - v) ^ k / (k.factorial : ℝ)) = F 0 v := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      rw [sub_self, zero_pow hk]
      ring
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.succ_pos m)) h
  rw [hv] at hftc
  linarith

/-- **The integrated Taylor formula.**  `∫_a^b F 0` is the integral of the Taylor polynomial of `F`
at `a`, whose value is `∑_{k ≤ m} F k a (b - a)^{k+1}/(k+1)!`, plus one remainder integral against
the kernel `(b - t)^{m+1}/(m+1)!`.

This is what replaces the Fubini step in the usual proof of Peano's theorem: the double integral
`∫_a^b ∫_a^x (x - t)^m F^{(m+1)}(t) dt dx` never has to be formed. -/
theorem integral_eq_taylorSum_add_integral {a b : ℝ} {m : ℕ}
    (hF : ∀ k ≤ m, ∀ t ∈ Set.uIcc a b, HasDerivAt (F k) (F (k + 1) t) t)
    (hint : IntervalIntegrable (F (m + 1)) volume a b) :
    (∫ t in a..b, F 0 t)
      = (∑ k ∈ Finset.range (m + 1), F k a * (b - a) ^ (k + 1) / ((k + 1).factorial : ℝ))
        + ∫ t in a..b, (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) t := by
  have hΨ : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun s => ∑ k ∈ Finset.range (m + 1),
          F k s * (b - s) ^ (k + 1) / ((k + 1).factorial : ℝ))
        ((b - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) t - F 0 t) t :=
    fun t ht => hasDerivAt_integratedTaylorSum m fun k hk => hF k hk t ht
  have hc0 : ContinuousOn (F 0) (Set.uIcc a b) := fun t ht =>
    (hF 0 (Nat.zero_le m) t ht).continuousAt.continuousWithinAt
  have hi0 : IntervalIntegrable (F 0) volume a b := hc0.intervalIntegrable
  have hi1 : IntervalIntegrable
      (fun t => (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) t) volume a b :=
    hint.continuousOn_mul (by fun_prop)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hΨ (hi1.sub hi0)
  rw [intervalIntegral.integral_sub hi1 hi0] at hftc
  have hb : (∑ k ∈ Finset.range (m + 1),
      F k b * (b - b) ^ (k + 1) / ((k + 1).factorial : ℝ)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [sub_self, zero_pow (Nat.succ_ne_zero k)]
    ring
  rw [hb] at hftc
  linarith

/-- **The truncated power** `(y - t)_+^m`: it is `(y - t)^m` for `t ≤ y` and `0` beyond, so that
`t ↦ (y - t)_+^m` is the piece of the monomial that Peano's kernel integrates against. -/
noncomputable def truncPow (m : ℕ) (y t : ℝ) : ℝ := if t ≤ y then (y - t) ^ m else 0

/-- The truncated power as the indicator of a half line, in the truncated variable. -/
theorem truncPow_eq_indicator (m : ℕ) (y : ℝ) :
    truncPow m y = (Set.Iic y).indicator fun t => (y - t) ^ m := by
  funext t
  by_cases h : t ≤ y <;> simp [truncPow, h]

/-- The truncated power as the indicator of a half line, in the other variable. -/
theorem truncPow_flip_eq_indicator (m : ℕ) (t : ℝ) :
    (fun y => truncPow m y t) = (Set.Ici t).indicator fun y => (y - t) ^ m := by
  funext y
  by_cases h : t ≤ y <;> simp [truncPow, h]

/-- The truncated power is interval integrable in the variable it is truncated at. -/
theorem intervalIntegrable_truncPow (m : ℕ) (y u v : ℝ) :
    IntervalIntegrable (truncPow m y) volume u v := by
  have hc : IntervalIntegrable (fun t : ℝ => (y - t) ^ m) volume u v :=
    Continuous.intervalIntegrable (by fun_prop) u v
  rw [intervalIntegrable_iff] at hc ⊢
  rw [truncPow_eq_indicator]
  exact hc.indicator measurableSet_Iic

/-- The truncated power is interval integrable in the variable it is a power of. -/
theorem intervalIntegrable_truncPow_flip (m : ℕ) (t u v : ℝ) :
    IntervalIntegrable (fun y => truncPow m y t) volume u v := by
  have hc : IntervalIntegrable (fun y : ℝ => (y - t) ^ m) volume u v :=
    Continuous.intervalIntegrable (by fun_prop) u v
  rw [intervalIntegrable_iff] at hc ⊢
  rw [truncPow_flip_eq_indicator]
  exact hc.indicator measurableSet_Ici

/-- Integrating against a truncated power over the whole panel is integrating against the plain
power over the part of the panel below the truncation point. -/
theorem integral_truncPow_mul {a b y : ℝ} {m : ℕ} {g : ℝ → ℝ} (hay : a ≤ y) (hyb : y ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    (∫ t in a..b, truncPow m y t * g t) = ∫ t in a..y, (y - t) ^ m * g t := by
  have hsub1 : Set.uIcc a y ⊆ Set.Icc a b := by
    rw [Set.uIcc_of_le hay]
    exact Set.Icc_subset_Icc le_rfl hyb
  have hsub2 : Set.uIcc y b ⊆ Set.Icc a b := by
    rw [Set.uIcc_of_le hyb]
    exact Set.Icc_subset_Icc hay le_rfl
  have h1 : IntervalIntegrable (fun t => truncPow m y t * g t) volume a y :=
    (intervalIntegrable_truncPow m y a y).mul_continuousOn (hg.mono hsub1)
  have h2 : IntervalIntegrable (fun t => truncPow m y t * g t) volume y b :=
    (intervalIntegrable_truncPow m y y b).mul_continuousOn (hg.mono hsub2)
  have e1 : (∫ t in a..y, truncPow m y t * g t) = ∫ t in a..y, (y - t) ^ m * g t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hay] at ht
    simp [truncPow, ht.2]
  have e2 : (∫ t in y..b, truncPow m y t * g t) = 0 := by
    rw [intervalIntegral.integral_of_le hyb,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        (g := fun _ : ℝ => (0 : ℝ)) fun t ht => by
          have hty : ¬ t ≤ y := not_le.2 ht.1
          simp [truncPow, hty],
      MeasureTheory.integral_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, e1, e2, add_zero]

/-- The integral of the truncated power in its *upper* variable:
`∫_a^b (x - t)_+^m dx = (b - t)^{m+1}/(m + 1)` for `t` in the panel. -/
theorem integral_truncPow_flip {a b t : ℝ} {m : ℕ} (hat : a ≤ t) (htb : t ≤ b) :
    (∫ x in a..b, truncPow m x t) = (b - t) ^ (m + 1) / ((m : ℝ) + 1) := by
  have e1 : (∫ x in a..t, truncPow m x t) = 0 := by
    rw [intervalIntegral.integral_of_le hat, MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (g := fun _ : ℝ => (0 : ℝ)) fun x hx => by
          have hxt : ¬ t ≤ x := not_le.2 hx.2
          simp [truncPow, hxt],
      MeasureTheory.integral_zero]
  have e2 : (∫ x in t..b, truncPow m x t) = ∫ x in t..b, (x - t) ^ m := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le htb] at hx
    simp [truncPow, hx.1]
  have e3 : (∫ x in t..b, (x - t) ^ m) = (b - t) ^ (m + 1) / ((m : ℝ) + 1) := by
    have hD : ∀ x ∈ Set.uIcc t b,
        HasDerivAt (fun s : ℝ => (s - t) ^ (m + 1) / ((m : ℝ) + 1)) ((x - t) ^ m) x := by
      intro x _
      have h : HasDerivAt (fun s : ℝ => (s - t) ^ (m + 1) / ((m : ℝ) + 1))
          (((m + 1 : ℕ) : ℝ) * (x - t) ^ m * 1 / ((m : ℝ) + 1)) x :=
        (((hasDerivAt_id x).sub_const t).pow (m + 1)).div_const _
      convert h using 1
      have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_truncPow_flip m t a t) (intervalIntegrable_truncPow_flip m t t b),
    e1, e2, e3, zero_add]

/-- **The Peano kernel** of the rule with weights `w` at nodes `z` on `[a, b]`, at order `m`: the
error functional applied to the truncated power `(· - t)_+^m`, divided by `m!`.

`Quadrature.peanoKernel_eq` gives its closed form `(b - t)^{m+1}/(m+1)! - ∑ᵢ wᵢ (zᵢ - t)_+^m/m!`
on the panel, and `Quadrature.error_eq_integral_peanoKernel` is Peano's theorem. -/
noncomputable def peanoKernel {n : ℕ} (a b : ℝ) (w z : Fin n → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ((∫ x in a..b, truncPow m x t) - ∑ i, w i * truncPow m (z i) t) / (m.factorial : ℝ)

/-- The closed form of the Peano kernel on the panel. -/
theorem peanoKernel_eq {n : ℕ} {a b : ℝ} (w z : Fin n → ℝ) (m : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc a b) :
    peanoKernel a b w z m t
      = (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ)
        - ∑ i, w i * truncPow m (z i) t / (m.factorial : ℝ) := by
  have hfac : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hne : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [peanoKernel, integral_truncPow_flip ht.1 ht.2, hfac, sub_div, Finset.sum_div]
  congr 1
  field_simp

/-- **Peano's kernel theorem.**  A rule with weights `w` at nodes `z` in `[a, b]` that integrates
every polynomial of degree at most `m` exactly has, at an integrand `F 0` carrying a chain of
derivatives `F 1, …, F (m + 1)` on `[a, b]`, the error

`∫_a^b F 0 - ∑ᵢ wᵢ F 0 (zᵢ) = ∫_a^b K(t) F (m + 1) t dt`,

with `K = Quadrature.peanoKernel a b w z m` the error functional applied to the truncated power
`(· - t)_+^m` and divided by `m!`.

Taylor's formula with the integral remainder, applied once over the panel
(`Quadrature.integral_eq_taylorSum_add_integral`) and once at each node
(`Quadrature.eq_taylorSum_add_integral`), splits both halves of the error into the Taylor
polynomial — which exactness annihilates — plus a remainder integral.  The truncated power is what
puts the node remainders on the same interval as the panel remainder, and the finitely many node
remainders come out of the integral by linearity, so no Fubini step is needed.

Reference: [kress1998numerical], §9.2. -/
theorem error_eq_integral_peanoKernel {a b : ℝ} {n m : ℕ} (hab : a ≤ b) {w z : Fin n → ℝ}
    (hz : ∀ i, z i ∈ Set.Icc a b)
    (hF : ∀ k ≤ m, ∀ t ∈ Set.Icc a b, HasDerivAt (F k) (F (k + 1) t) t)
    (hc : ContinuousOn (F (m + 1)) (Set.Icc a b))
    (hexact : ∀ p : ℝ[X], p.degree ≤ (m : WithBot ℕ) →
      (∫ t in a..b, p.eval t) = ∑ i, w i * p.eval (z i)) :
    (∫ t in a..b, F 0 t) - ∑ i, w i * F 0 (z i)
      = ∫ t in a..b, peanoKernel a b w z m t * F (m + 1) t := by
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hint : IntervalIntegrable (F (m + 1)) volume a b :=
    ContinuousOn.intervalIntegrable (by rw [huIcc]; exact hc)
  -- exactness on the shifted monomials
  have hmono : ∀ k ≤ m, (∫ t in a..b, (t - a) ^ k) = ∑ i, w i * (z i - a) ^ k := by
    intro k hk
    have hdeg : ((Polynomial.X - Polynomial.C a) ^ k).degree ≤ (m : WithBot ℕ) := by
      have h1 : ((Polynomial.X - Polynomial.C a) ^ k).degree = (k : WithBot ℕ) := by
        simp [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
      rw [h1]
      exact_mod_cast hk
    simpa using hexact _ hdeg
  -- the moments of the shifted monomials
  have hpow : ∀ k : ℕ, (∫ t in a..b, (t - a) ^ k) = (b - a) ^ (k + 1) / ((k : ℝ) + 1) := by
    intro k
    have hD : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun s : ℝ => (s - a) ^ (k + 1) / ((k : ℝ) + 1)) ((x - a) ^ k) x := by
      intro x _
      have h : HasDerivAt (fun s : ℝ => (s - a) ^ (k + 1) / ((k : ℝ) + 1))
          (((k + 1 : ℕ) : ℝ) * (x - a) ^ k * 1 / ((k : ℝ) + 1)) x :=
        (((hasDerivAt_id x).sub_const a).pow (k + 1)).div_const _
      convert h using 1
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp
  -- exactness, applied to the Taylor polynomial of `F` at `a`
  have hkey : (∑ k ∈ Finset.range (m + 1), F k a * (b - a) ^ (k + 1) / ((k + 1).factorial : ℝ))
      = ∑ i, w i * ∑ k ∈ Finset.range (m + 1), F k a * (z i - a) ^ k / (k.factorial : ℝ) := by
    have step : ∀ k ∈ Finset.range (m + 1),
        F k a * (b - a) ^ (k + 1) / ((k + 1).factorial : ℝ)
          = ∑ i, w i * (F k a * (z i - a) ^ k / (k.factorial : ℝ)) := by
      intro k hk
      have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have h1 : (b - a) ^ (k + 1) / ((k : ℝ) + 1) = ∑ i, w i * (z i - a) ^ k := by
        rw [← hpow k, hmono k hk']
      have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hkne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      calc F k a * (b - a) ^ (k + 1) / ((k + 1).factorial : ℝ)
          = F k a / (k.factorial : ℝ) * ((b - a) ^ (k + 1) / ((k : ℝ) + 1)) := by
            rw [hfac]
            field_simp
        _ = F k a / (k.factorial : ℝ) * ∑ i, w i * (z i - a) ^ k := by rw [h1]
        _ = ∑ i, w i * (F k a * (z i - a) ^ k / (k.factorial : ℝ)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_congr rfl step, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  -- the panel half of the error
  have hleft : (∫ t in a..b, F 0 t)
      = (∑ k ∈ Finset.range (m + 1), F k a * (b - a) ^ (k + 1) / ((k + 1).factorial : ℝ))
        + ∫ t in a..b, (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) t :=
    integral_eq_taylorSum_add_integral (by rw [huIcc]; exact hF) hint
  -- the rule half of the error, node by node
  have hright : ∀ i, F 0 (z i)
      = (∑ k ∈ Finset.range (m + 1), F k a * (z i - a) ^ k / (k.factorial : ℝ))
        + ∫ t in a..b, truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t := by
    intro i
    have haz : a ≤ z i := (hz i).1
    have hzb : z i ≤ b := (hz i).2
    have hsub : Set.uIcc a (z i) ⊆ Set.Icc a b := by
      rw [Set.uIcc_of_le haz]
      exact Set.Icc_subset_Icc le_rfl hzb
    have h := eq_taylorSum_add_integral (F := F) (u := a) (v := z i) (m := m)
      (fun k hk t ht => hF k hk t (hsub ht)) (hint.mono_set (by rw [huIcc]; exact hsub))
    rw [h]
    congr 1
    calc (∫ t in a..(z i), (z i - t) ^ m / (m.factorial : ℝ) * F (m + 1) t)
        = ∫ t in a..(z i), (z i - t) ^ m * (F (m + 1) t / (m.factorial : ℝ)) :=
          intervalIntegral.integral_congr fun t _ => by ring
      _ = ∫ t in a..b, truncPow m (z i) t * (F (m + 1) t / (m.factorial : ℝ)) :=
          (integral_truncPow_mul haz hzb (hc.div_const _)).symm
      _ = ∫ t in a..b, truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t :=
          intervalIntegral.integral_congr fun t _ => by ring
  -- integrability of the pieces
  have hRint : ∀ i, IntervalIntegrable
      (fun t => w i * (truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t)) volume a b := by
    intro i
    have h := (intervalIntegrable_truncPow m (z i) a b).mul_continuousOn
      (g := fun t => w i * (F (m + 1) t / (m.factorial : ℝ)))
      (by rw [huIcc]; exact (hc.div_const _).const_smul (w i))
    have hfun : (fun t => truncPow m (z i) t * (w i * (F (m + 1) t / (m.factorial : ℝ))))
        = fun t => w i * (truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t) := by
      funext t
      ring
    rwa [hfun] at h
  have hsumint : IntervalIntegrable
      (fun t => ∑ i, w i * (truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t)) volume a b := by
    have h := IntervalIntegrable.sum (μ := volume) (a := a) (b := b) Finset.univ
      fun i (_ : i ∈ Finset.univ) => hRint i
    have hfun : (∑ i ∈ Finset.univ,
          fun t => w i * (truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t))
        = fun t => ∑ i, w i * (truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t) := by
      funext t
      rw [Finset.sum_apply]
    rwa [hfun] at h
  have hi1 : IntervalIntegrable
      (fun t => (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) t) volume a b :=
    hint.continuousOn_mul (by fun_prop)
  -- the kernel integral, expanded
  have hK : (∫ t in a..b, peanoKernel a b w z m t * F (m + 1) t)
      = (∫ t in a..b, (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) t)
        - ∑ i, w i * ∫ t in a..b, truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t := by
    have e0 : (∫ t in a..b, peanoKernel a b w z m t * F (m + 1) t)
        = ∫ t in a..b, ((b - t) ^ (m + 1) / ((m + 1).factorial : ℝ) * F (m + 1) t
            - ∑ i, w i * (truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t)) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [huIcc] at ht
      rw [peanoKernel_eq w z m ht, sub_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e0, intervalIntegral.integral_sub hi1 hsumint,
      intervalIntegral.integral_finsetSum fun i _ => hRint i]
    congr 1
    exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _
  have hsumF : ∑ i, w i * F 0 (z i)
      = (∑ i, w i * ∑ k ∈ Finset.range (m + 1), F k a * (z i - a) ^ k / (k.factorial : ℝ))
        + ∑ i, w i * ∫ t in a..b, truncPow m (z i) t / (m.factorial : ℝ) * F (m + 1) t := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hright i]; ring
  rw [hK, hleft, hsumF, hkey]
  ring

/-- **The Peano error bound.**  Under the hypotheses of `Quadrature.error_eq_integral_peanoKernel`,
the error is at most the `L¹` norm of the kernel times a bound on `F (m + 1)`. -/
theorem abs_error_le_integral_abs_peanoKernel {a b : ℝ} {n m : ℕ} (hab : a ≤ b) {w z : Fin n → ℝ}
    {M : ℝ} (hz : ∀ i, z i ∈ Set.Icc a b)
    (hF : ∀ k ≤ m, ∀ t ∈ Set.Icc a b, HasDerivAt (F k) (F (k + 1) t) t)
    (hc : ContinuousOn (F (m + 1)) (Set.Icc a b))
    (hexact : ∀ p : ℝ[X], p.degree ≤ (m : WithBot ℕ) →
      (∫ t in a..b, p.eval t) = ∑ i, w i * p.eval (z i))
    (hM : ∀ t ∈ Set.Icc a b, |F (m + 1) t| ≤ M) :
    |(∫ t in a..b, F 0 t) - ∑ i, w i * F 0 (z i)|
      ≤ (∫ t in a..b, |peanoKernel a b w z m t|) * M := by
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hint : IntervalIntegrable (F (m + 1)) volume a b :=
    ContinuousOn.intervalIntegrable (by rw [huIcc]; exact hc)
  -- the kernel is integrable on the panel: on it, it is the closed form
  have hclosed : ∀ t ∈ Set.uIcc a b, peanoKernel a b w z m t
      = (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ)
        - ∑ i, w i * truncPow m (z i) t / (m.factorial : ℝ) := by
    intro t ht
    rw [huIcc] at ht
    exact peanoKernel_eq w z m ht
  have hKint : IntervalIntegrable (peanoKernel a b w z m) volume a b := by
    have hbase : IntervalIntegrable (fun t => (b - t) ^ (m + 1) / ((m + 1).factorial : ℝ)
        - ∑ i, w i * truncPow m (z i) t / (m.factorial : ℝ)) volume a b := by
      refine (Continuous.intervalIntegrable (by fun_prop) a b).sub ?_
      have h := IntervalIntegrable.sum (μ := volume) (a := a) (b := b) Finset.univ
        fun i (_ : i ∈ Finset.univ) =>
          ((intervalIntegrable_truncPow m (z i) a b).const_mul (w i)).div_const
            ((m.factorial : ℝ))
      have hfun : (∑ i ∈ Finset.univ, fun t => w i * truncPow m (z i) t / (m.factorial : ℝ))
          = fun t => ∑ i, w i * truncPow m (z i) t / (m.factorial : ℝ) := by
        funext t
        rw [Finset.sum_apply]
      rwa [hfun] at h
    exact hbase.congr fun t ht => (hclosed t (Set.uIoc_subset_uIcc ht)).symm
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM a (Set.left_mem_Icc.2 hab))
  have habs : IntervalIntegrable (fun t => |peanoKernel a b w z m t|) volume a b := hKint.abs
  have hprod : IntervalIntegrable
      (fun t => |peanoKernel a b w z m t * F (m + 1) t|) volume a b := by
    have := (hKint.mul_continuousOn (by rw [huIcc]; exact hc)).abs
    exact this
  have hbdd : IntervalIntegrable (fun t => |peanoKernel a b w z m t| * M) volume a b :=
    habs.mul_const M
  rw [error_eq_integral_peanoKernel hab hz hF hc hexact]
  calc |∫ t in a..b, peanoKernel a b w z m t * F (m + 1) t|
      ≤ ∫ t in a..b, |peanoKernel a b w z m t * F (m + 1) t| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, |peanoKernel a b w z m t| * M := by
        refine intervalIntegral.integral_mono_on hab hprod hbdd fun t ht => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hM t ht) (abs_nonneg _)
    _ = (∫ t in a..b, |peanoKernel a b w z m t|) * M := intervalIntegral.integral_mul_const _ _

end Peano

end Quadrature
