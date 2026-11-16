/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.IntegralEquations.SecondKind
import NumlibSurface.AtkinsonHan.Chapter03.Section06

/-!
# Atkinson and Han, Section 12.1: Projection methods for equations of the second kind

This module formalizes Section 12.1 of [han2009theoretical]. Let $V$ be a Banach space,
$\lambda \neq 0$ a scalar, $K$ a bounded operator on $V$ and $f \in V$. The section approximates the
solution of the equation of the second kind $(\lambda - K) u = f$ by the projection method
(12.1.18): for a bounded projection $P_n$ onto a trial space $V_n$, find $u_n \in V_n$ with
$P_n (\lambda - K) u_n = P_n f$. Theorem 12.1.2 says that if $\lambda - K$ is invertible and
$\|K - P_n K\| \to 0$, then $\lambda - P_n K$ is invertible with a uniformly bounded inverse for
large $n$, and the error satisfies
$$u - u_n = \lambda (\lambda - P_n K)^{-1} (u - P_n u),$$
so $\|u - u_n\|$ and $\|u - P_n u\|$ tend to zero at the same rate. Lemma 12.1.4 says that
$\|K - P_n K\| \to 0$ holds for every compact $K$ when $P_n \to I$ pointwise. Example 12.1.1 is
collocation by Lagrange interpolation.

The proofs specialize `Numlib.IntegralEquations.SecondKind` and the projection method
`IsProjectionMethodSolution` of `Numlib.Variational.ProjectionMethod`.

## Main definitions

* (12.1.18), `AtkinsonHan.Chapter12.IsProjectionSolution`: $u_n \in \operatorname{range} P$ and
  $P (\lambda - K) u_n = P f$.

## Main results

* Example 12.1.1, `AtkinsonHan.Chapter12.example_12_1_1`: Lagrange interpolation at $n + 1$ distinct
  nodes is a projection onto the polynomials of degree at most $n$, and the collocation conditions
  (12.1.5) are the projection equations, (12.1.12).
* (12.1.11), `AtkinsonHan.Chapter12.interpolate_eq_zero_iff`: the interpolant of $g$ is zero if and
  only if $g$ vanishes at every node.
* (12.1.17), `AtkinsonHan.Chapter12.equation_12_1_17`: a nonzero bounded projection has norm at
  least $1$.
* (12.1.19), `AtkinsonHan.Chapter12.isProjectionSolution_iff_smul_sub_comp`: for $\lambda \neq 0$
  the projection equations are $(\lambda - P K) u_n = P f$.
* Theorem 12.1.2, `AtkinsonHan.Chapter12.theorem_12_1_2`: if
  $\|(\lambda - K)^{-1}\| \|K - P K\| < 1$, then $\lambda - P K$ is invertible with the bound
  (12.1.22), and the projection equations are uniquely solvable.
* Lemma 12.1.3, `AtkinsonHan.Chapter12.lemma_12_1_3`: a pointwise convergent sequence of bounded
  operators converges uniformly on compact sets.
* Lemma 12.1.4, `AtkinsonHan.Chapter12.lemma_12_1_4`: if $P_n \to I$ pointwise and $K$ is compact,
  then $\|K - P_n K\| \to 0$, which is (12.1.21).
* (12.1.23), `AtkinsonHan.Chapter12.equation_12_1_23`: the error identity $u - u_n = \lambda
  (\lambda - P K)^{-1} (u - P u)$.
* (12.1.24), `AtkinsonHan.Chapter12.equation_12_1_24`: the two-sided bound of $\|u - u_n\|$ by
  $\|u - P u\|$.
* Exercise 12.1.3, `AtkinsonHan.Chapter12.exercise_12_1_3`: the constant of the upper bound in
  (12.1.24) can be taken as $|\lambda| (1 + \gamma_n) \|(\lambda - K)^{-1}\|$ with $\gamma_n \to 0$.
* Exercise 12.1.4, `AtkinsonHan.Chapter12.exercise_12_1_4`: the error is asymptotically its leading
  term $\lambda (\lambda - K)^{-1} (u - P_n u)$.

## Conventions

* The scalar $\lambda$ of the source is `μ`, because `λ` is the lambda binder of Lean. The scalar
  field is `𝕜` with `[RCLike 𝕜]`.
* An invertible operator such as $\lambda - K$ is given as a continuous linear equivalence
  `e : X ≃L[𝕜] X` whose underlying operator is $\lambda - K$. Its inverse $(\lambda - K)^{-1}$ is
  `e.symm`.

## Deviations from the source

* **Theorem 12.1.2, (12.1.17)–(12.1.24)** (generalization). The source states the results for a
  sequence of projections $P_n$ onto finite-dimensional subspaces $V_n$. The library states them for
  a single bounded idempotent $P$, without finite dimension, and uses a sequence only where a limit
  is taken. See `AtkinsonHan.Chapter12.theorem_12_1_2`.
* **(12.1.24)** (reading). The source divides by $\|\lambda - P K\|$. The library states the lower
  bound in product form, so that no quotient by a norm that can vanish occurs. See
  `AtkinsonHan.Chapter12.equation_12_1_24`.

## Not formalized

* **The linear systems (12.1.5) and (12.1.14) in coordinates**, written in a basis
  $\varphi_1, \dots, \varphi_\kappa$ of the trial space. They are this framework at a concrete
  projection, and the rest of the chapter does not use the coordinate form; the passage from
  (12.1.5) to `AtkinsonHan.Chapter12.IsProjectionSolution` is
  `AtkinsonHan.Chapter12.example_12_1_1`.
* **Section 12.1.2**, the Galerkin method with $V = L^2(D)$. It is this framework at a concrete
  projection, and the rest of the chapter does not use it.
-/

open Filter Topology

namespace AtkinsonHan.Chapter12

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ### The projection equations -/

/-- **Equation (12.1.18)** of [han2009theoretical], the projection method. Let $X$ be a normed space
over $\mathbb{R}$ or $\mathbb{C}$, let $\lambda$ be a scalar, let $K$ and $P$ be bounded
operators on $X$, and let $f \in X$. Then $u_n$ is a **solution of the projection equations**
for $(\lambda - K) u = f$ if $u_n$ lies in the trial space $\operatorname{range} P$ and
$$P (\lambda - K) u_n = P f.$$

This is the backbone's `IsProjectionMethodSolution` for the operator $\lambda - K$, by
`AtkinsonHan.Chapter12.isProjectionSolution_iff`. The equivalent form (12.1.19), with no
membership condition, is `AtkinsonHan.Chapter12.isProjectionSolution_iff_smul_sub_comp`. -/
def IsProjectionSolution (μ : 𝕜) (K P : X →L[𝕜] X) (f un : X) : Prop :=
  un ∈ LinearMap.range (P : X →ₗ[𝕜] X) ∧ P ((μ • 1 - K : X →L[𝕜] X) un) = P f

/-- The projection equations (12.1.18) are equivalent to the backbone's `IsProjectionMethodSolution`
for the operator $\lambda - K$, the datum $f$ and the projection $P$. -/
theorem isProjectionSolution_iff (μ : 𝕜) (K P : X →L[𝕜] X) (f un : X) :
    IsProjectionSolution μ K P f un ↔
      IsProjectionMethodSolution ((μ • 1 - K : X →L[𝕜] X) : X →ₗ[𝕜] X) f P un :=
  Iff.rfl

/-- If $P$ is idempotent and $u_n$ solves the projection equations, then $P u_n = u_n$. -/
theorem IsProjectionSolution.apply_eq_self {μ : 𝕜} {K P : X →L[𝕜] X} (hP : IsIdempotentElem P)
    {f un : X} (h : IsProjectionSolution μ K P f un) : P un = un :=
  IsProjectionMethodSolution.apply_eq_self hP h

/-- **Equation (12.1.19)** of [han2009theoretical]. Let $\lambda \neq 0$ and let $P$ be a bounded
idempotent operator. Then $u_n$ solves the projection equations
$u_n \in \operatorname{range} P$, $P (\lambda - K) u_n = P f$ if and only if
$$(\lambda - P K) u_n = P f$$
on the whole space. The membership $u_n \in \operatorname{range} P$ is not needed on the right,
because $\lambda u_n = P (f + K u_n)$ implies it. -/
theorem isProjectionSolution_iff_smul_sub_comp {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X}
    (hP : IsIdempotentElem P) (f un : X) :
    IsProjectionSolution μ K P f un ↔ (μ • 1 - P ∘L K : X →L[𝕜] X) un = P f := by
  constructor
  · rintro ⟨hmem, heq⟩
    have hPun : P un = un := IsProjectionMethodSolution.apply_eq_self hP ⟨hmem, heq⟩
    rw [← heq]
    simp only [sub_apply, smul_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, map_sub,
      map_smul, hPun]
  · intro heq
    have h1 : μ • un - P (K un) = P f := by
      simpa only [sub_apply, smul_apply, one_apply_eq_self,
        ContinuousLinearMap.comp_apply] using heq
    have h2 : P (f + K un) = μ • un := by rw [map_add, ← h1]; abel
    have hun : (P : X →ₗ[𝕜] X) (μ⁻¹ • (f + K un)) = un := by
      change P (μ⁻¹ • (f + K un)) = un
      rw [map_smul, h2, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    have hmem : un ∈ LinearMap.range (P : X →ₗ[𝕜] X) := ⟨_, hun⟩
    refine ⟨hmem, ?_⟩
    have hPun : P un = un := by
      obtain ⟨v, hv⟩ := hmem
      rw [← hv]
      exact DFunLike.congr_fun hP v
    simp only [sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul, hPun]
    exact h1

/-- **Equation (12.1.17)** of [han2009theoretical]. A nonzero bounded idempotent operator $P$ on a
normed space has $\|P\| \ge 1$, because $\|P\| = \|P^2\| \le \|P\|^2$.

The norm $\|P_n\|$ enters the error constants of the projection method, in (12.1.24) and in the
hypothesis of Theorem 12.1.2, so no choice of $P_n$ makes these constants smaller than their
values at $\|P_n\| = 1$. This is Exercise 3.6.7, `AtkinsonHan.Chapter03.exercise_3_6_7`. -/
theorem equation_12_1_17 {P : X →L[𝕜] X} (hP : IsIdempotentElem P) (hP0 : P ≠ 0) : 1 ≤ ‖P‖ :=
  Chapter03.exercise_3_6_7 P hP hP0

/-! ### Example 12.1.1: collocation with Lagrange interpolation -/

section Collocation

variable {a b : ℝ} {n : ℕ} {x : Fin (n + 1) → Set.Icc a b}

/-- **Equation (12.1.11)** of [han2009theoretical]. Let $x_0, \dots, x_n \in [a, b]$ be distinct
nodes and let $P$ be the interpolatory projection at these nodes on $C[a, b]$. Then for
$g \in C[a, b]$, $P g = 0$ if and only if $g(x_j) = 0$ for every $j$.

One direction is (12.1.8) at a node, $(P g)(x_j) = g(x_j)$. The other is the Lagrange form
$P g = \sum_i g(x_i) \ell_i$. -/
theorem interpolate_eq_zero_iff (hx : Function.Injective x) (g : C(Set.Icc a b, ℝ)) :
    Lagrange.interpolateCLM x g = 0 ↔ ∀ j, g (x j) = 0 := by
  constructor
  · intro h j
    rw [← Lagrange.interpolateCLM_apply_node hx g j, h, ContinuousMap.zero_apply]
  · intro h
    ext t
    rw [ContinuousMap.zero_apply, Lagrange.interpolateCLM_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [h i, zero_mul]

/-- **Example 12.1.1** of [han2009theoretical] (collocation with Lagrange interpolation). Let
$V = C[a, b]$, let $x_0, \dots, x_n \in [a, b]$ be distinct nodes, and let $P_n$ be the Lagrange
interpolatory projection (12.1.10) at these nodes. Let $\lambda \in \mathbb{R}$, let $K$ be a
bounded operator on $C[a, b]$, and let $f, u_n \in C[a, b]$. Then:

* $P_n$ is a projection operator, with range the space $V_n$ of polynomials of degree at most
  $n$, which is Example 3.6.5;
* (12.1.11): $P_n g = 0$ if and only if $g(x_j) = 0$ for every $j$;
* (12.1.12): the collocation conditions (12.1.5), $u_n \in V_n$ and
  $\bigl((\lambda - K) u_n - f\bigr)(x_j) = 0$ for every $j$, hold if and only if $u_n$ solves
  the projection equations $P_n (\lambda - K) u_n = P_n f$.

The third clause is the passage from the linear system (12.1.5) to
`AtkinsonHan.Chapter12.IsProjectionSolution`, where the general theory of the section applies.
No hypothesis on $\lambda$ is needed, because the membership $u_n \in V_n$ is on both sides. The
projection is `Lagrange.interpolateCLM`, the projection property is
`AtkinsonHan.Chapter03.IsProjectionOperator`, and $V_n$ is `AtkinsonHan.Chapter03.polyLE`. -/
theorem example_12_1_1 (hx : Function.Injective x) (μ : ℝ)
    (K : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) (f un : C(Set.Icc a b, ℝ)) :
    Chapter03.IsProjectionOperator (Lagrange.interpolateCLM x) ∧
      LinearMap.range ((Lagrange.interpolateCLM x :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) :
          C(Set.Icc a b, ℝ) →ₗ[ℝ] C(Set.Icc a b, ℝ)) = Chapter03.polyLE a b n ∧
      (∀ g : C(Set.Icc a b, ℝ), Lagrange.interpolateCLM x g = 0 ↔ ∀ j, g (x j) = 0) ∧
      ((un ∈ LinearMap.range ((Lagrange.interpolateCLM x :
            C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) :
            C(Set.Icc a b, ℝ) →ₗ[ℝ] C(Set.Icc a b, ℝ)) ∧
          ∀ j, ((μ • 1 - K : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un - f) (x j) = 0) ↔
        IsProjectionSolution μ K (Lagrange.interpolateCLM x) f un) := by
  obtain ⟨hproj, hrange, -⟩ := Chapter03.example_3_6_5 hx
  refine ⟨hproj, hrange, interpolate_eq_zero_iff hx, and_congr_right fun _ => ?_⟩
  rw [← interpolate_eq_zero_iff hx, map_sub, sub_eq_zero]

end Collocation

/-! ### The two convergence lemmas -/

/-- **Lemma 12.1.3** of [han2009theoretical]. Let $X$ be a Banach space and $W$ a normed space, and
let $A_n, L \colon X \to W$ be bounded linear operators with $A_n x \to L x$ for every
$x \in X$. Then $A_n \to L$ uniformly on every compact subset of $X$. -/
theorem lemma_12_1_3 [CompleteSpace X] {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {A : ℕ → X →L[𝕜] W} {L : X →L[𝕜] W} (hA : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (L x)))
    {S : Set X} (hS : IsCompact S) :
    TendstoUniformlyOn (fun n => (A n : X → W)) L atTop S :=
  tendstoUniformlyOn_of_tendsto_of_isCompact hA hS

/-- **Lemma 12.1.4** of [han2009theoretical]. Let $X$ be a Banach space, let $K$ be a compact
operator on $X$, and let $P_n$ be bounded operators with $P_n x \to x$ for every $x \in X$. Then
$$\|K - P_n K\| \to 0.$$

This is the hypothesis (12.1.21) of Theorem 12.1.2, so that hypothesis holds for every compact
$K$ when the projections converge pointwise. -/
theorem lemma_12_1_4 [CompleteSpace X] {K : X →L[𝕜] X} (hK : IsCompactOperator K)
    {P : ℕ → X →L[𝕜] X} (hP : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) :
    Tendsto (fun n => ‖K - P n ∘L K‖) atTop (𝓝 0) := by
  have hA : ∀ x, Tendsto (fun n => (1 - P n : X →L[𝕜] X) x) atTop (𝓝 0) := by
    intro x
    have h : Tendsto (fun n => x - P n x) atTop (𝓝 (x - x)) := tendsto_const_nhds.sub (hP x)
    rw [sub_self] at h
    simpa using h
  have hid : ∀ n, ((1 - P n : X →L[𝕜] X) ∘L K : X →L[𝕜] X) = K - P n ∘L K := by
    intro n
    ext x
    simp
  simpa only [hid] using tendsto_opNorm_comp_of_isCompactOperator hA hK

/-! ### Stability and convergence -/

/-- **Theorem 12.1.2** of [han2009theoretical], stability. Let $X$ be a Banach space,
$\lambda \neq 0$, $K$ a bounded operator and $P$ a bounded idempotent operator on $X$. Let
$\lambda - K$ be invertible with bounded inverse, and let $P$ satisfy (12.1.25),
$\|(\lambda - K)^{-1}\| \|K - P K\| < 1$. Then $\lambda - P K$ is invertible with bounded
inverse, the bound (12.1.22),
$$\|(\lambda - P K)^{-1}\| \le \frac{\|(\lambda - K)^{-1}\|}{1 - \|(\lambda - K)^{-1}\| \|K - P
  K\|},$$
holds, and for every $f \in X$ the projection equations (12.1.18) have exactly one solution.

**Generalization.** The source states the theorem for a sequence of projections onto
finite-dimensional subspaces. It is stated here for one bounded idempotent $P$, without finite
dimension.

By Lemma 12.1.4 the hypothesis holds for all large $n$ when $K$ is compact and $P_n u \to u$, so
the bound is uniform in $n$. -/
theorem theorem_12_1_2 [CompleteSpace X] {μ : 𝕜} (hμ : μ ≠ 0) {K P : X →L[𝕜] X}
    (hP : IsIdempotentElem P) (e : X ≃L[𝕜] X) (he : (e : X →L[𝕜] X) = μ • 1 - K)
    (h : ‖(e.symm : X →L[𝕜] X)‖ * ‖K - P ∘L K‖ < 1) :
    ∃ e' : X ≃L[𝕜] X, (e' : X →L[𝕜] X) = μ • 1 - P ∘L K ∧
      ‖(e'.symm : X →L[𝕜] X)‖ ≤
        ‖(e.symm : X →L[𝕜] X)‖ / (1 - ‖(e.symm : X →L[𝕜] X)‖ * ‖K - P ∘L K‖) ∧
      ∀ f : X, ∃! un : X, IsProjectionSolution μ K P f un := by
  obtain ⟨e', he'coe, he'norm⟩ := SecondKind.exists_equiv_of_projection e he h
  refine ⟨e', he'coe, he'norm, fun f => ?_⟩
  have hiff : ∀ un : X,
      IsProjectionSolution μ K P f un ↔ (μ • 1 - P ∘L K : X →L[𝕜] X) un = P f :=
    fun un => isProjectionSolution_iff_smul_sub_comp hμ hP f un
  simp only [hiff]
  refine ⟨e'.symm (P f), ?_, ?_⟩
  · dsimp only
    rw [← he'coe, ContinuousLinearEquiv.coe_coe, e'.apply_symm_apply]
  · intro y hy
    rw [← he'coe, ContinuousLinearEquiv.coe_coe] at hy
    rw [← hy, e'.symm_apply_apply]

/-- **Equation (12.1.23)** of [han2009theoretical], the error identity. Let $P$ be a bounded
idempotent operator and let $\lambda - P K$ be invertible with bounded inverse. If
$(\lambda - K) u = f$ and $u_n$ solves the projection equations (12.1.18), then
$$u - u_n = \lambda (\lambda - P K)^{-1} (u - P u).$$

The convergence analysis of the projection method follows from this identity. -/
theorem equation_12_1_23 {μ : 𝕜} {K P : X →L[𝕜] X} (hP : IsIdempotentElem P) {e' : X ≃L[𝕜] X}
    (he' : (e' : X →L[𝕜] X) = μ • 1 - P ∘L K) {f u un : X}
    (hu : (μ • 1 - K : X →L[𝕜] X) u = f) (hun : IsProjectionSolution μ K P f un) :
    u - un = e'.symm (μ • (u - P u)) := by
  have hkey := SecondKind.sub_projection_eq hP hu hun
  rw [← hkey, ← he', ContinuousLinearEquiv.coe_coe, e'.symm_apply_apply]

/-- **Equation (12.1.24)** of [han2009theoretical], the two-sided error bound. Under the hypotheses
of `AtkinsonHan.Chapter12.equation_12_1_23`,
$$|\lambda| \|u - P u\| \le \|\lambda - P K\| \|u - u_n\| \qquad \text{and} \qquad \|u - u_n\|
  \le |\lambda| \|(\lambda - P K)^{-1}\| \|u - P u\|.$$

**Reading.** The source divides by $\|\lambda - P K\|$ in the lower bound. The product form is
stated here, so that no quotient by a norm that can vanish occurs.

With the uniform bound of `AtkinsonHan.Chapter12.theorem_12_1_2`, the two inequalities say that
the error of the method and the approximation error of the trial space tend to zero at the same
rate. -/
theorem equation_12_1_24 {μ : 𝕜} {K P : X →L[𝕜] X} (hP : IsIdempotentElem P) {e' : X ≃L[𝕜] X}
    (he' : (e' : X →L[𝕜] X) = μ • 1 - P ∘L K) {f u un : X}
    (hu : (μ • 1 - K : X →L[𝕜] X) u = f) (hun : IsProjectionSolution μ K P f un) :
    ‖μ‖ * ‖u - P u‖ ≤ ‖(μ • 1 - P ∘L K : X →L[𝕜] X)‖ * ‖u - un‖ ∧
      ‖u - un‖ ≤ ‖μ‖ * ‖(e'.symm : X →L[𝕜] X)‖ * ‖u - P u‖ :=
  ⟨SecondKind.norm_smul_sub_le_of_projection hP hu hun,
    SecondKind.norm_sub_le_of_projection hP he' hu hun⟩

/-! ### The asymptotic constant -/

/-- For $A, c \ge 0$ with $A c \le 1/2$, the geometric-series bound
$A / (1 - A c) \le A (1 + 2 A c)$ holds. -/
private theorem div_le_mul_one_add {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (h : A * c ≤ 1 / 2) :
    A / (1 - A * c) ≤ A * (1 + 2 * (A * c)) := by
  have hx : 0 ≤ A * c := mul_nonneg hA hc
  have hpos : 0 < 1 - A * c := by linarith
  have h2 : 0 ≤ 1 - 2 * (A * c) := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [mul_nonneg (mul_nonneg hA hx) h2]

/-- If $\lambda - K$ is invertible and $\|K - P_n K\| \to 0$, then eventually $\lambda - P_n K$ is
invertible with $\|(\lambda - P_n K)^{-1}\| \le \|(\lambda - K)^{-1}\| (1 + 2 \|(\lambda -
K)^{-1}\| \|K - P_n K\|)$ and $\|(\lambda - P_n K)^{-1}\| \le 2 \|(\lambda - K)^{-1}\|$. -/
private theorem eventually_exists_equiv [CompleteSpace X] {μ : 𝕜} {K : X →L[𝕜] X}
    {P : ℕ → X →L[𝕜] X} {e : X ≃L[𝕜] X} (he : (e : X →L[𝕜] X) = μ • 1 - K)
    (hc : Tendsto (fun n => ‖K - P n ∘L K‖) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∃ e' : X ≃L[𝕜] X, (e' : X →L[𝕜] X) = μ • 1 - P n ∘L K ∧
      ‖(e'.symm : X →L[𝕜] X)‖ ≤
        ‖(e.symm : X →L[𝕜] X)‖ *
          (1 + 2 * (‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖)) ∧
      ‖(e'.symm : X →L[𝕜] X)‖ ≤ 2 * ‖(e.symm : X →L[𝕜] X)‖ := by
  have hA : (0 : ℝ) ≤ ‖(e.symm : X →L[𝕜] X)‖ := norm_nonneg _
  have hhalf : ∀ᶠ n in atTop, ‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖ < 1 / 2 := by
    have h0 : Tendsto (fun n => ‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖) atTop (𝓝 0) := by
      simpa using hc.const_mul ‖(e.symm : X →L[𝕜] X)‖
    exact h0.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hhalf] with n hn
  obtain ⟨e', he'coe, he'norm⟩ :=
    SecondKind.exists_equiv_of_projection e he (by linarith)
  have hbound := he'norm.trans (div_le_mul_one_add hA (norm_nonneg _) hn.le)
  exact ⟨e', he'coe, hbound, hbound.trans (by nlinarith)⟩

/-- **Exercise 12.1.3** of [han2009theoretical]. Let $X$ be a Banach space, $K$ a bounded operator
and $P_n$ bounded idempotent operators on $X$, with $\lambda - K$ invertible with bounded
inverse and $\|K - P_n K\| \to 0$. Then there are $\gamma_n \to 0$ such that, for all large $n$,
whenever $(\lambda - K) u = f$ and $u_n$ solves the projection equations for $P_n$,
$$\|u - u_n\| \le |\lambda| (1 + \gamma_n) \|(\lambda - K)^{-1}\| \|u - P_n u\|.$$

So the constant of the upper bound in (12.1.24) can be taken from the exact inverse. The proof
takes $\gamma_n = 2 \|(\lambda - K)^{-1}\| \|K - P_n K\|$. The hypothesis $\|K - P_n K\| \to 0$
is (12.1.21), which holds for a compact $K$ and pointwise convergent projections by Lemma
12.1.4. -/
theorem exercise_12_1_3 [CompleteSpace X] {μ : 𝕜} {K : X →L[𝕜] X}
    {P : ℕ → X →L[𝕜] X} (hP : ∀ n, IsIdempotentElem (P n)) {e : X ≃L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - K)
    (hc : Tendsto (fun n => ‖K - P n ∘L K‖) atTop (𝓝 0)) :
    ∃ γ : ℕ → ℝ, Tendsto γ atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ∀ f u un : X,
      (μ • 1 - K : X →L[𝕜] X) u = f → IsProjectionSolution μ K (P n) f un →
        ‖u - un‖ ≤ ‖μ‖ * (1 + γ n) * ‖(e.symm : X →L[𝕜] X)‖ * ‖u - P n u‖ := by
  refine ⟨fun n => 2 * (‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖), ?_, ?_⟩
  · simpa using (hc.const_mul ‖(e.symm : X →L[𝕜] X)‖).const_mul 2
  filter_upwards [eventually_exists_equiv he hc] with n hn f u un hu hun
  obtain ⟨e', he'coe, he'norm, -⟩ := hn
  refine (SecondKind.norm_sub_le_of_projection (hP n) he'coe hu hun).trans ?_
  have h1 : ‖μ‖ * ‖(e'.symm : X →L[𝕜] X)‖ ≤
      ‖μ‖ * (‖(e.symm : X →L[𝕜] X)‖ *
        (1 + 2 * (‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖))) :=
    mul_le_mul_of_nonneg_left he'norm (norm_nonneg _)
  have h2 : ‖μ‖ * (1 + 2 * (‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖)) *
      ‖(e.symm : X →L[𝕜] X)‖ =
      ‖μ‖ * (‖(e.symm : X →L[𝕜] X)‖ *
        (1 + 2 * (‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖))) := by ring
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- **Exercise 12.1.4** of [han2009theoretical]. Let $X$ be a Banach space, $K$ a bounded operator
and $P_n$ bounded idempotent operators on $X$, with $\lambda - K$ invertible with bounded
inverse and $\|K - P_n K\| \to 0$. Split the error as $u - u_n = e_n^{(1)} + e_n^{(2)}$, with
the leading term $e_n^{(1)} = \lambda (\lambda - K)^{-1} (u - P_n u)$ of (12.1.31). Then there
are $\delta_n \to 0$ such that, for all large $n$, whenever $(\lambda - K) u = f$ and $u_n$
solves the projection equations for $P_n$,
$$\|e_n^{(2)}\| \le \delta_n \|e_n^{(1)}\|.$$

So the error is asymptotically its leading term, which uses the exact inverse. The proof takes
$\delta_n = 2 \|(\lambda - K)^{-1}\| \|K - P_n K\|$, because $(\lambda - P_n K) e_n^{(2)} = (P_n
K - K) e_n^{(1)}$. -/
theorem exercise_12_1_4 [CompleteSpace X] {μ : 𝕜} {K : X →L[𝕜] X}
    {P : ℕ → X →L[𝕜] X} (hP : ∀ n, IsIdempotentElem (P n)) {e : X ≃L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - K)
    (hc : Tendsto (fun n => ‖K - P n ∘L K‖) atTop (𝓝 0)) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ∀ f u un : X,
      (μ • 1 - K : X →L[𝕜] X) u = f → IsProjectionSolution μ K (P n) f un →
        ‖u - un - μ • e.symm (u - P n u)‖ ≤ δ n * ‖μ • e.symm (u - P n u)‖ := by
  refine ⟨fun n => 2 * (‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖), ?_, ?_⟩
  · simpa using (hc.const_mul ‖(e.symm : X →L[𝕜] X)‖).const_mul 2
  filter_upwards [eventually_exists_equiv he hc] with n hn f u un hu hun
  obtain ⟨e', he'coe, -, he'norm⟩ := hn
  set y : X := μ • e.symm (u - P n u) with hy
  -- the leading term solves the exact equation with the same right-hand side
  have hy1 : (μ • 1 - K : X →L[𝕜] X) y = μ • (u - P n u) := by
    rw [hy, map_smul, ← he, ContinuousLinearEquiv.coe_coe, e.apply_symm_apply]
  -- hence the remainder solves the projected equation with a small right-hand side
  have hkey : (μ • 1 - P n ∘L K : X →L[𝕜] X) (u - un - y)
      = -((K - P n ∘L K : X →L[𝕜] X) y) := by
    have hsplit : (μ • 1 - P n ∘L K : X →L[𝕜] X) y
        = (μ • 1 - K : X →L[𝕜] X) y + (K - P n ∘L K : X →L[𝕜] X) y := by
      simp only [sub_apply, smul_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply]
      abel
    rw [map_sub, SecondKind.sub_projection_eq (hP n) hu hun, hsplit, hy1]
    abel
  have hsol : u - un - y = e'.symm (-((K - P n ∘L K : X →L[𝕜] X) y)) := by
    rw [← hkey, ← he'coe, ContinuousLinearEquiv.coe_coe, e'.symm_apply_apply]
  rw [hsol]
  calc ‖e'.symm (-((K - P n ∘L K : X →L[𝕜] X) y))‖
      ≤ ‖(e'.symm : X →L[𝕜] X)‖ * ‖(K - P n ∘L K : X →L[𝕜] X) y‖ := by
        rw [← norm_neg ((K - P n ∘L K : X →L[𝕜] X) y)]
        exact ContinuousLinearMap.le_opNorm (e'.symm : X →L[𝕜] X) _
    _ ≤ 2 * ‖(e.symm : X →L[𝕜] X)‖ * (‖K - P n ∘L K‖ * ‖y‖) :=
        mul_le_mul he'norm (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) (by positivity)
    _ = 2 * (‖(e.symm : X →L[𝕜] X)‖ * ‖K - P n ∘L K‖) * ‖y‖ := by ring

end AtkinsonHan.Chapter12
