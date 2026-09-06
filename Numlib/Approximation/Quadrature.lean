import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.TietzeExtension
import Numlib.Analysis.Normed.Operator.BanachSteinhaus
import Numlib.Approximation.Interpolation
import Numlib.Approximation.OrthogonalPolynomial

/-!
# Numerical quadrature

A quadrature rule is the bounded linear functional `f ↦ ∑ i, w i * f (x i)` on the continuous
functions of a compact space: finitely many *nodes* `x i` with *weights* `w i`, approximating an
integral. This file has the rule itself, its norm, and the criterion by which a sequence of rules
converges for every continuous integrand. The material is [han2009theoretical] §2.4 and
[kress1998numerical] §9.1 and §9.3.

## Main definitions

* `Quadrature.functional w x` is the rule, as an element of the dual of `C(X, ℝ)`.
* `Quadrature.IsExactOn L w x d` says that the rule reproduces a target functional `L` on the
  polynomials of degree at most `d`, and `Quadrature.degreeOfExactness` is the largest such `d`.
* `Quadrature.IsInterpolatory L w x` says that the weights are the values of `L` at the Lagrange
  basis functions of the nodes.

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

end Quadrature
