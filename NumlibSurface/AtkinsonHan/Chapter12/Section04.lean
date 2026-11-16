/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Numlib.Approximation.CompositeQuadrature
import Numlib.IntegralEquations.Nystrom
import Numlib.IntegralEquations.SecondKind
import NumlibSurface.AtkinsonHan.Chapter02.Section03
import NumlibSurface.AtkinsonHan.Chapter12.Section03

/-!
# Atkinson and Han, Section 12.4: The Nyström method

This module formalizes Section 12.4 of [han2009theoretical]. The Nyström method replaces the
integral in $K u(t) = \int_D k(t, s) u(s)\, ds$ by a quadrature rule with weights $w_{n,j}$ and
nodes $x_{n,j}$, which gives the operator $K_n u(t) = \sum_j w_{n,j} k(t, x_{n,j}) u(x_{n,j})$ of
(12.4.4), and solves $(\lambda - K_n) u_n = f$. In general $\|K - K_n\|$ does not tend to zero. The
analysis rests instead on Anselone's perturbation theorem (Theorem 12.4.3), whose hypothesis bounds
$\|(T - S) S\|$, and on the identities of Lemma 12.4.2, which express $(K - K_n) K$ and
$(K - K_n) K_n$ through one kernel $e_n$. Theorem 12.4.4 follows: for convergent rules with bounded
absolute weight sums, $\lambda - K_n$ is invertible for large $n$ with uniformly bounded inverses,
and $\|u - u_n\|_\infty \le c \|K u - K_n u\|_\infty$.

The module also proves the abstract form of the theory of §12.4.3: assumptions A1–A3 on a family of
operators (a collectively compact family that converges pointwise), the consequences in Lemma
12.4.7, and the convergence of the approximate equations, which Section 12.5 reuses for product
integration. The concrete part treats the equation (12.4.7) of Example 12.4.1, the composite
trapezoidal rule and its asymptotic error (Example 12.4.5 and (12.4.39)), and the asymptotic error
expansion of the Nyström solution (Example 12.4.6). The proofs specialize
`Numlib.IntegralEquations.Nystrom`, `Numlib.IntegralEquations.SecondKind` and
`Numlib.Approximation.CompositeQuadrature`.

## Main definitions

* Assumptions A1–A3 of §12.4.3, `AtkinsonHan.Chapter12.IsCollectivelyCompactFamily`: a family $K_n$
  converges pointwise to $K$, and $\{K_n v : n \in \mathbb{N}, \|v\| \le 1\}$ has compact closure
  (12.4.53).

## Main results

* Example 12.4.1, `AtkinsonHan.Chapter12.norm_fredholm_expKernel`: the operator of (12.4.7) has norm
  $e - 1$.
* Example 12.4.1, `AtkinsonHan.Chapter12.example_12_4_1`: the equation (12.4.7) is uniquely solvable
  for every $f \in C[0, 1]$.
* Lemma 12.4.2, `AtkinsonHan.Chapter12.lemma_12_4_2_a`: $(K - K_n) K$ is the integral operator of
  $e_n$, (12.4.14), with norm (12.4.16).
* Lemma 12.4.2, `AtkinsonHan.Chapter12.lemma_12_4_2_b`: $(K - K_n) K_n$ is the Nyström operator of
  $e_n$, (12.4.15), with norm (12.4.17).
* Lemma 12.4.2, `AtkinsonHan.Chapter12.lemma_12_4_2_c`: both norms tend to zero, (12.4.18).
* Theorem 12.4.3, `AtkinsonHan.Chapter12.theorem_12_4_3`: Anselone's perturbation theorem, with the
  inverse bound (12.4.23) and the error bound (12.4.24).
* Theorem 12.4.4, `AtkinsonHan.Chapter12.theorem_12_4_4`: the Nyström equations are uniquely
  solvable for large $n$, with uniformly bounded inverses (12.4.32), and $\|u - u_n\|_\infty \le c
  \|K u - K_n u\|_\infty$.
* Example 12.4.5, `AtkinsonHan.Chapter12.example_12_4_5`: the error $-h^2 (b - a) g''(\xi)/12$ of
  the composite trapezoidal rule.
* Equation (12.4.39), `AtkinsonHan.Chapter12.equation_12_4_39`: the asymptotic error
  $-(h^2/12)[g'(b) - g'(a)] + O(h^4)$ of the composite trapezoidal rule.
* Equation (12.4.44), `AtkinsonHan.Chapter12.equation_12_4_44`: the expansion
  $(K - K_n) u = h^2 d + O(h^4)$ of the consistency error, uniformly in the row variable.
* Example 12.4.6, `AtkinsonHan.Chapter12.example_12_4_6`: the asymptotic error expansion
  $u - u_n = h^2 \gamma + O(h^4)$ of the Nyström solution.
* Lemma 12.4.7, `AtkinsonHan.Chapter12.lemma_12_4_7_a`, `AtkinsonHan.Chapter12.lemma_12_4_7_b`,
  `AtkinsonHan.Chapter12.lemma_12_4_7_c` and `AtkinsonHan.Chapter12.lemma_12_4_7_d`: the limit of a
  collectively compact family is compact, the family is uniformly bounded, $\|(K - K_n) M\| \to 0$
  for compact $M$, and $\|(K - K_n) K_n\| \to 0$.
* Theorem 12.4.4 in the setting of §12.4.3,
  `AtkinsonHan.Chapter12.exists_norm_inverse_le_of_isCollectivelyCompactFamily`: the conclusion of
  Theorem 12.4.4 for every family that satisfies A1–A3.
* `AtkinsonHan.Chapter12.isCollectivelyCompactFamily_nystromCLM`: the Nyström operators of
  convergent quadrature rules with bounded absolute weight sums satisfy A1–A3.

## Conventions

* The scalar $\lambda$ of the source is `μ`, because `λ` is the Lean lambda binder. The measure of
  the concrete part is therefore `ν`.
* In the abstract results the family of the source is $K_n$ with limit $K$. In Lean the family is
  `K : ℕ → X →L[𝕜] X` and its limit is `L`. The doc comments below use the notation of the source,
  so the $K$ and $K_n$ of a comment are `L` and `K n` in the abstract statements.
* A quadrature rule is `Quadrature.functional w x`, the functional $v \mapsto \sum_j w_j v(x_j)$,
  and the Nyström operator is `IntegralOperator.nystromCLM`.

## Implementation notes

* The source formulates assumption A3 on the closed unit ball, as (12.4.53). The backbone notion
  `IsCollectivelyCompact` uses some neighbourhood of the origin. The two agree by
  `AtkinsonHan.Chapter12.IsCollectivelyCompactFamily.isCollectivelyCompact` and
  `AtkinsonHan.Chapter12.isCollectivelyCompactFamily_of_isCollectivelyCompact`.
* Boundedness of the operators, assumption A1, is part of the type `X →L[𝕜] X`.

## Deviations from the source

* **The domain $D$** (generalization). The source takes a closed bounded set
  $D \subseteq \mathbb{R}^m$ with Lebesgue measure. The statements hold on every compact space with
  a finite Borel measure, the generality of `IntegralOperator.kernelCLM` and
  `IntegralOperator.nystromCLM`; the case of the source is `IntegralOperator.regionMeasure D`. See
  `AtkinsonHan.Chapter12.theorem_12_4_4`.
* **Lemma 12.4.7(3)** (generalization). The compact operator $M$ may have any normed space as its
  domain. See `AtkinsonHan.Chapter12.lemma_12_4_7_c`.
* **Theorem 12.4.4** (generalization). The source states the convergence for the Nyström operators
  on $C(D)$. Its proof uses only A1–A3, and the statement holds for every family that satisfies
  them. See `AtkinsonHan.Chapter12.exists_norm_inverse_le_of_isCollectivelyCompactFamily`.

## Not formalized

* **The numerical part of Example 12.4.1.** The nodal errors (12.4.8) and (12.4.9) of the
  three-point Simpson and Gauss–Legendre rules, the comparison of Nyström interpolation with
  quadratic interpolation away from the nodes, and Figure 12.1 are computed floating-point numbers.
* **The unconditional form of the last clause of Example 12.4.6.** The claim of the source that
  $r_n = O(h^4)$ "by a similar argument" needs $\|(K - K_n) \gamma\| = O(h^2)$, hence the smoothness
  of the solution $\gamma$ of the auxiliary equation, hence differentiation under the integral sign.
  That bound is a hypothesis of the clause that needs it.
-/

open Filter Topology

namespace AtkinsonHan.Chapter12

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ### Anselone's perturbation theorem -/

/-- **Theorem 12.4.3** of [han2009theoretical] (Anselone's perturbation theorem). Let $S$ and $T$ be
bounded operators on a Banach space with $S$ compact, let $\lambda \neq 0$ be such that
$\lambda - T$ is invertible, and assume (12.4.22), $$\|(\lambda - T)^{-1}\| \, \|(T - S) S\| <
|\lambda|.$$ Then $\lambda - S$ is invertible with the bound (12.4.23), $$\|(\lambda - S)^{-1}\|
\le \frac{1 + \|(\lambda - T)^{-1}\| \|S\|}{|\lambda| - \|(\lambda - T)^{-1}\| \|(T - S) S\|},$$
and the solutions of $(\lambda - T) u = f$ and $(\lambda - S) z = f$ satisfy (12.4.24), $$\|u -
z\| \le \|(\lambda - S)^{-1}\| \, \|T u - S u\|.$$

The source prints (12.4.22) as $\|(T - S) S\| < |\lambda| / \|(\lambda - T)^{-1}\|$. The product
form is equivalent and divides by nothing. The hypothesis concerns $(T - S) S$ and not $T - S$,
and this is why the theorem applies to quadrature approximations of an integral operator, where
$\|T - S\|$ does not tend to zero. -/
theorem theorem_12_4_3 [CompleteSpace X] {μ : 𝕜} (hμ : μ ≠ 0) {S T : X →L[𝕜] X}
    (hS : IsCompactOperator S) {e : X ≃L[𝕜] X} (he : (e : X →L[𝕜] X) = μ • 1 - T)
    (h : ‖(e.symm : X →L[𝕜] X)‖ * ‖(T - S) ∘L S‖ < ‖μ‖) :
    ∃ e' : X ≃L[𝕜] X, (e' : X →L[𝕜] X) = μ • 1 - S ∧
      ‖(e'.symm : X →L[𝕜] X)‖ ≤ (1 + ‖(e.symm : X →L[𝕜] X)‖ * ‖S‖) /
        (‖μ‖ - ‖(e.symm : X →L[𝕜] X)‖ * ‖(T - S) ∘L S‖) ∧
      ∀ f u z : X, (μ • 1 - T : X →L[𝕜] X) u = f → (μ • 1 - S : X →L[𝕜] X) z = f →
        ‖u - z‖ ≤ ‖(e'.symm : X →L[𝕜] X)‖ * ‖T u - S u‖ := by
  obtain ⟨e', he'coe, he'norm⟩ := SecondKind.exists_equiv_of_isCompactOperator hμ hS he h
  exact ⟨e', he'coe, he'norm, fun _ _ _ hu hz => SecondKind.norm_sub_le he'coe hu hz⟩

/-! ### The assumptions A1–A3 -/

/-- **Assumptions A1–A3** of [han2009theoretical], §12.4.3. Let $K_n$, $n \in \mathbb{N}$, and $K$
be bounded operators on a normed space $X$ (A1). The family is a **collectively compact family
that converges pointwise to $K$** if $K_n u \to K u$ for every $u \in X$ (A2), and the set
$$\{K_n v : n \in \mathbb{N}, \ \|v\| \le 1\}$$ of (12.4.53) has compact closure (A3).

Boundedness (A1) is part of the type `X →L[𝕜] X`, so it needs no field. The limit operator is
`L` and the family is `K`. -/
structure IsCollectivelyCompactFamily (K : ℕ → X →L[𝕜] X) (L : X →L[𝕜] X) : Prop where
  /-- Assumption A2: $K_n u \to K u$ for every $u$. -/
  tendsto : ∀ x, Tendsto (fun n => K n x) atTop (𝓝 (L x))
  /-- Assumption A3, (12.4.53): the union of the images of the closed unit ball under the $K_n$ has
  compact closure. -/
  isCompact_closure : IsCompact (closure (⋃ n, K n '' Metric.closedBall 0 1))

/-- A family that satisfies A1–A3 is collectively compact in the sense of `IsCollectivelyCompact`,
because the closed unit ball is a neighbourhood of the origin. -/
theorem IsCollectivelyCompactFamily.isCollectivelyCompact {K : ℕ → X →L[𝕜] X} {L : X →L[𝕜] X}
    (h : IsCollectivelyCompactFamily K L) : IsCollectivelyCompact K :=
  ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos, h.isCompact_closure⟩

/-- A family that is collectively compact in the sense of `IsCollectivelyCompact` and converges
pointwise to $K$ satisfies A1–A3. A neighbourhood of the origin contains a ball of some radius
$r$, and multiplication by $r/2$ maps the closed unit ball into it, so the two unions of images
differ by a homeomorphism of the space. -/
theorem isCollectivelyCompactFamily_of_isCollectivelyCompact {K : ℕ → X →L[𝕜] X} {L : X →L[𝕜] X}
    (hK : IsCollectivelyCompact K) (hL : ∀ x, Tendsto (fun n => K n x) atTop (𝓝 (L x))) :
    IsCollectivelyCompactFamily K L := by
  obtain ⟨U, hU, hcpt⟩ := hK
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨hL, ?_⟩
  obtain ⟨c, hcnorm⟩ : ∃ c : 𝕜, ‖c‖ = r / 2 :=
    ⟨((r / 2 : ℝ) : 𝕜), by rw [RCLike.norm_ofReal, abs_of_pos (by linarith)]⟩
  have hc0 : c ≠ 0 := by
    rw [← norm_ne_zero_iff, hcnorm]
    exact ne_of_gt (by linarith)
  have hsub : closure (⋃ n, K n '' Metric.closedBall (0 : X) 1) ⊆
      (fun y : X => c⁻¹ • y) '' closure (⋃ i, K i '' U) := by
    refine closure_minimal ?_ ((hcpt.image (continuous_const_smul c⁻¹)).isClosed)
    rintro z hz
    obtain ⟨n, hzn⟩ := Set.mem_iUnion.1 hz
    obtain ⟨x, hx, rfl⟩ := hzn
    have hxU : c • x ∈ U := by
      refine hrU (mem_ball_zero_iff.2 ?_)
      rw [norm_smul, hcnorm]
      calc r / 2 * ‖x‖ ≤ r / 2 * 1 :=
            mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hx) (by linarith)
        _ < r := by linarith
    refine ⟨K n (c • x), subset_closure (Set.mem_iUnion.2 ⟨n, ⟨c • x, hxU, rfl⟩⟩), ?_⟩
    simp only [map_smul, inv_smul_smul₀ hc0]
  exact (hcpt.image (continuous_const_smul c⁻¹)).of_isClosed_subset isClosed_closure hsub

/-! ### Lemma 12.4.7 -/

variable {K : ℕ → X →L[𝕜] X} {L : X →L[𝕜] X}

/-- **Lemma 12.4.7(1)** of [han2009theoretical]. If $\{K_n\}$ satisfies A1–A3 with limit $K$, then
$K$ is compact. -/
theorem lemma_12_4_7_a (h : IsCollectivelyCompactFamily K L) : IsCompactOperator L :=
  IsCollectivelyCompact.isCompactOperator_of_tendsto h.isCollectivelyCompact h.tendsto

/-- **Lemma 12.4.7(2)** of [han2009theoretical]. If $\{K_n\}$ satisfies A1–A3, then there is a
constant $C$ with $\|K_n\| \le C$ for all $n$. -/
theorem lemma_12_4_7_b (h : IsCollectivelyCompactFamily K L) : ∃ C, ∀ n, ‖K n‖ ≤ C :=
  IsCollectivelyCompact.exists_opNorm_le h.isCollectivelyCompact

/-- **Lemma 12.4.7(3)** of [han2009theoretical]. Let $X$ be a Banach space and let $\{K_n\}$ satisfy
A1–A3 with limit $K$. If $M : U \to X$ is a compact operator from a normed space $U$, then
$$\|(K - K_n) M\| \to 0.$$

**Generalization.** The domain $U$ of $M$ is any normed space. The proof uses only the pointwise
convergence A2. -/
theorem lemma_12_4_7_c [CompleteSpace X] {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    (h : IsCollectivelyCompactFamily K L) {M : U →L[𝕜] X} (hM : IsCompactOperator M) :
    Tendsto (fun n => ‖(L - K n) ∘L M‖) atTop (𝓝 0) := by
  refine tendsto_opNorm_comp_of_isCompactOperator (fun x => ?_) hM
  have hx : Tendsto (fun n => L x - K n x) atTop (𝓝 (L x - L x)) :=
    tendsto_const_nhds.sub (h.tendsto x)
  rw [sub_self] at hx
  simpa using hx

/-- **Lemma 12.4.7(4)** of [han2009theoretical]. Let $X$ be a Banach space and let $\{K_n\}$ satisfy
A1–A3 with limit $K$. Then $$\|(K - K_n) K_n\| \to 0,$$ although $\|K - K_n\|$ need not tend to
zero.

This gives hypothesis (12.4.22) of Theorem 12.4.3 for all large $n$. -/
theorem lemma_12_4_7_d [CompleteSpace X] (h : IsCollectivelyCompactFamily K L) :
    Tendsto (fun n => ‖(L - K n) ∘L K n‖) atTop (𝓝 0) :=
  IsCollectivelyCompact.tendsto_opNorm_sub_comp h.isCollectivelyCompact h.tendsto

/-! ### The convergence of the approximate equations -/

/-- **Theorem 12.4.4** of [han2009theoretical], for a family that satisfies A1–A3. Let $X$ be a
Banach space, let $\{K_n\}$ satisfy A1–A3 with limit $K$, and let $\lambda \neq 0$ be such that
$\lambda - K$ is invertible. Then there is a constant $c$ such that for all large $n$ the
operator $\lambda - K_n$ is invertible with $\|(\lambda - K_n)^{-1}\| \le c$, which is
(12.4.32), and the solutions of $(\lambda - K) u = f$ and $(\lambda - K_n) u_n = f$ satisfy
$$\|u - u_n\| \le c \, \|K u - K_n u\|,$$ the consistency error at the exact solution.

**Generalization.** The source states this for the Nyström operators on $C(D)$. Its proof is
Lemma 12.4.7 followed by Theorem 12.4.3 and uses only A1–A3.

The proof gives $c = 2 (1 + \|(\lambda - K)^{-1}\| C) / |\lambda|$, with $C$ the uniform bound
of `AtkinsonHan.Chapter12.lemma_12_4_7_b`. -/
theorem exists_norm_inverse_le_of_isCollectivelyCompactFamily [CompleteSpace X] {μ : 𝕜}
    (hμ : μ ≠ 0) (h : IsCollectivelyCompactFamily K L) {e : X ≃L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - L) :
    ∃ c : ℝ, ∀ᶠ n in atTop, ∃ en : X ≃L[𝕜] X, (en : X →L[𝕜] X) = μ • 1 - K n ∧
      ‖(en.symm : X →L[𝕜] X)‖ ≤ c ∧
      ∀ f u un : X, (μ • 1 - L : X →L[𝕜] X) u = f → (μ • 1 - K n : X →L[𝕜] X) un = f →
        ‖u - un‖ ≤ c * ‖L u - K n u‖ := by
  have hμpos : (0 : ℝ) < ‖μ‖ := norm_pos_iff.2 hμ
  obtain ⟨C, hC⟩ := lemma_12_4_7_b h
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hA0 : (0 : ℝ) ≤ ‖(e.symm : X →L[𝕜] X)‖ := norm_nonneg _
  refine ⟨(1 + ‖(e.symm : X →L[𝕜] X)‖ * C) / (‖μ‖ / 2), ?_⟩
  have hsmall : ∀ᶠ n in atTop,
      ‖(e.symm : X →L[𝕜] X)‖ * ‖(L - K n) ∘L K n‖ < ‖μ‖ / 2 := by
    have h0 : Tendsto (fun n => ‖(e.symm : X →L[𝕜] X)‖ * ‖(L - K n) ∘L K n‖) atTop (𝓝 0) := by
      simpa using (lemma_12_4_7_d h).const_mul ‖(e.symm : X →L[𝕜] X)‖
    exact h0.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hsmall] with n hn
  obtain ⟨en, hencoe, hennorm, herr⟩ :=
    theorem_12_4_3 hμ (IsCollectivelyCompact.isCompactOperator h.isCollectivelyCompact n) he
      (by linarith)
  have hbound : ‖(en.symm : X →L[𝕜] X)‖ ≤
      (1 + ‖(e.symm : X →L[𝕜] X)‖ * C) / (‖μ‖ / 2) := by
    refine hennorm.trans ?_
    have hnum : 1 + ‖(e.symm : X →L[𝕜] X)‖ * ‖K n‖ ≤ 1 + ‖(e.symm : X →L[𝕜] X)‖ * C := by
      linarith [mul_le_mul_of_nonneg_left (hC n) hA0]
    have hnum0 : (0 : ℝ) ≤ 1 + ‖(e.symm : X →L[𝕜] X)‖ * C := by
      linarith [mul_nonneg hA0 hC0]
    have hden : ‖μ‖ / 2 ≤ ‖μ‖ - ‖(e.symm : X →L[𝕜] X)‖ * ‖(L - K n) ∘L K n‖ := by linarith
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    calc (1 + ‖(e.symm : X →L[𝕜] X)‖ * ‖K n‖) * (‖μ‖ / 2)
        ≤ (1 + ‖(e.symm : X →L[𝕜] X)‖ * C) * (‖μ‖ / 2) :=
          mul_le_mul_of_nonneg_right hnum (by linarith)
      _ ≤ (1 + ‖(e.symm : X →L[𝕜] X)‖ * C) *
            (‖μ‖ - ‖(e.symm : X →L[𝕜] X)‖ * ‖(L - K n) ∘L K n‖) :=
          mul_le_mul_of_nonneg_left hden hnum0
  exact ⟨en, hencoe, hbound, fun f u un hu hun =>
    (herr f u un hu hun).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))⟩

/-! ### The Nyström operators -/

section Nystrom

open IntegralOperator MeasureTheory

variable {D : Type*} [TopologicalSpace D] [CompactSpace D] [MeasurableSpace D] [BorelSpace D]
  (ν : Measure D) [IsFiniteMeasure ν]

/-- Let $D$ be a compact space with a finite Borel measure $\nu$, let $k$ be a continuous kernel on
$D \times D$ with integral operator $K u(t) = \int k(t, s) u(s)\, d\nu(s)$, and let $K_n u(t) =
\sum_j w_{n,j} k(t, x_{n,j}) u(x_{n,j})$ be the Nyström operators (12.4.4) of a sequence of
quadrature rules. If $\sum_j |w_{n,j}| \le W$ for all $n$ and the rules converge to
$\int v \, d\nu$ for every $v \in C(D)$, as in (12.4.3), then $\{K_n\}$ satisfies A1–A3 with
limit $K$.

A2 is `IntegralOperator.tendsto_nystromCLM` and A3 is
`IntegralOperator.isCollectivelyCompact_nystromCLM`. Both follow from the uniform convergence of
the rules on the compact set of functions $s \mapsto k(t, s) u(s)$. -/
theorem isCollectivelyCompactFamily_nystromCLM (k : C(D × D, ℝ)) {m : ℕ → ℕ}
    {w : ∀ n, Fin (m n) → ℝ} {x : ∀ n, Fin (m n) → D} {W : ℝ} (hW : ∀ n, ∑ j, |w n j| ≤ W)
    (hQ : ∀ v : C(D, ℝ), Tendsto (fun n => Quadrature.functional (w n) (x n) v) atTop
      (𝓝 (integralCLM ν v))) :
    IsCollectivelyCompactFamily (fun n => nystromCLM (w n) (x n) k) (kernelCLM ν k) :=
  isCollectivelyCompactFamily_of_isCollectivelyCompact
    (isCollectivelyCompact_nystromCLM k hW) fun u => tendsto_nystromCLM ν hQ u

/-- **Lemma 12.4.2** of [han2009theoretical], first clause. Let $D$ be a nonempty, second countable
compact space with a finite Borel measure $\nu$, let $k$ be a continuous kernel, and let $w_j$,
$x_j$ be the weights and nodes of a quadrature rule. Let $$e_n(t, s) = \int k(t, v) k(v, s)\,
d\nu(v) - \sum_j w_j k(t, x_j) k(x_j, s)$$ be the quadrature error of the composed kernel. Then
$(K - K_n) K$ is the integral operator of $e_n$, which is (12.4.14), and $$\|(K - K_n) K\| =
\sup_t \int |e_n(t, s)|\, d\nu(s),$$ which is (12.4.16).

The kernel $e_n$ is `IntegralOperator.compKernel`. -/
theorem lemma_12_4_2_a [SecondCountableTopology D] [Nonempty D] {m : ℕ} (w : Fin m → ℝ)
    (x : Fin m → D) (k : C(D × D, ℝ)) :
    (kernelCLM ν k - nystromCLM w x k) ∘L kernelCLM ν k = kernelCLM ν (compKernel ν w x k) ∧
      ‖(kernelCLM ν k - nystromCLM w x k) ∘L kernelCLM ν k‖
        = ⨆ t, ∫ s, |compKernel ν w x k (t, s)| ∂ν := by
  refine ⟨kernelCLM_sub_nystromCLM_comp_kernelCLM ν w x k, ?_⟩
  rw [kernelCLM_sub_nystromCLM_comp_kernelCLM ν w x k, norm_kernelCLM]

/-- **Lemma 12.4.2** of [han2009theoretical], second clause. Let $D$ be a nonempty Hausdorff compact
space with a finite Borel measure $\nu$, let $k$ be a continuous kernel, and let $w_j$ and
distinct nodes $x_j$ define a quadrature rule. Then $(K - K_n) K_n$ is the Nyström operator of
the kernel $e_n$ of the first clause, which is (12.4.15), and $$\|(K - K_n) K_n\| = \sup_t
\sum_j |w_j e_n(t, x_j)|,$$ which is (12.4.17). -/
theorem lemma_12_4_2_b [T2Space D] [Nonempty D] {m : ℕ} {w : Fin m → ℝ} {x : Fin m → D}
    (hx : Function.Injective x) (k : C(D × D, ℝ)) :
    (kernelCLM ν k - nystromCLM w x k) ∘L nystromCLM w x k
        = nystromCLM w x (compKernel ν w x k) ∧
      ‖(kernelCLM ν k - nystromCLM w x k) ∘L nystromCLM w x k‖
        = ⨆ t, ∑ j, |w j * compKernel ν w x k (t, x j)| := by
  refine ⟨kernelCLM_sub_nystromCLM_comp_nystromCLM ν w x k, ?_⟩
  rw [kernelCLM_sub_nystromCLM_comp_nystromCLM ν w x k, norm_nystromCLM hx]

/-- **Lemma 12.4.2** of [han2009theoretical], third clause, (12.4.18). Let $D$ be a second countable
compact space with a finite Borel measure $\nu$, let $k$ be a continuous kernel, and let a
sequence of quadrature rules satisfy $\sum_j |w_{n,j}| \le W$ for all $n$ and converge to
$\int v\, d\nu$ for every $v \in C(D)$. Then $$\|(K - K_n) K\| \to 0 \quad \text{and} \quad
\|(K - K_n) K_n\| \to 0.$$ This is hypothesis (12.4.22) of Theorem 12.4.3 for all large $n$.

The proof shows that $\max_{t, s} |e_n(t, s)| \to 0$ and uses the bounds
$\|(K - K_n) K\| \le \nu(D) \|e_n\|_\infty$ and $\|(K - K_n) K_n\| \le W \|e_n\|_\infty$, which
follow from the first two clauses. -/
theorem lemma_12_4_2_c [SecondCountableTopology D] {m : ℕ → ℕ} {w : ∀ n, Fin (m n) → ℝ}
    {x : ∀ n, Fin (m n) → D} (k : C(D × D, ℝ)) {W : ℝ} (hW : ∀ n, ∑ j, |w n j| ≤ W)
    (hQ : ∀ v : C(D, ℝ), Tendsto (fun n => Quadrature.functional (w n) (x n) v) atTop
      (𝓝 (integralCLM ν v))) :
    Tendsto (fun n => ‖(kernelCLM ν k - nystromCLM (w n) (x n) k) ∘L kernelCLM ν k‖)
        atTop (𝓝 0) ∧
      Tendsto (fun n => ‖(kernelCLM ν k - nystromCLM (w n) (x n) k) ∘L
        nystromCLM (w n) (x n) k‖) atTop (𝓝 0) := by
  have hW0 : (0 : ℝ) ≤ W := le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hW 0)
  have he := tendsto_norm_compKernel ν k hQ
  constructor
  · refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using he.const_mul (ν.real Set.univ))
    rw [kernelCLM_sub_nystromCLM_comp_kernelCLM ν (w n) (x n) k]
    refine norm_kernelCLM_le ν (by positivity) fun t => ?_
    have hint : (∫ s, |compKernel ν (w n) (x n) k (t, s)| ∂ν)
        ≤ ∫ _s : D, ‖compKernel ν (w n) (x n) k‖ ∂ν :=
      integral_mono (integrable_kernel_row ν _ t).abs (integrable_const _) fun s => by
        simpa using (compKernel ν (w n) (x n) k).norm_coe_le_norm (t, s)
    rwa [integral_const, smul_eq_mul] at hint
  · refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using he.const_mul W)
    rw [kernelCLM_sub_nystromCLM_comp_nystromCLM ν (w n) (x n) k]
    refine norm_nystromCLM_le (by positivity) fun t => ?_
    calc ∑ j, |w n j * compKernel ν (w n) (x n) k (t, x n j)|
        ≤ ∑ j, |w n j| * ‖compKernel ν (w n) (x n) k‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (by simpa using (compKernel ν (w n) (x n) k).norm_coe_le_norm (t, x n j))
            (abs_nonneg _)
      _ = (∑ j, |w n j|) * ‖compKernel ν (w n) (x n) k‖ := by rw [Finset.sum_mul]
      _ ≤ W * ‖compKernel ν (w n) (x n) k‖ :=
          mul_le_mul_of_nonneg_right (hW n) (norm_nonneg _)

/-- **Theorem 12.4.4** of [han2009theoretical]. Let $D$ be a compact space with a finite Borel
measure $\nu$, let $k$ be a continuous kernel on $D \times D$ with integral operator $K$ on
$C(D)$, and let $\lambda \neq 0$ be such that $\lambda - K$ is invertible. Let $K_n$ be the
Nyström operators of a sequence of quadrature rules with $\sum_j |w_{n,j}| \le W$ for all $n$
that converge to $\int v\, d\nu$ for every $v \in C(D)$. Then there is a constant $c$ such that
for all large $n$ the operator $\lambda - K_n$ is invertible with
$\|(\lambda - K_n)^{-1}\| \le c$, which is (12.4.32), so the Nyström equations are uniquely
solvable, and the solutions of $(\lambda - K) u = f$ and $(\lambda - K_n) u_n = f$ satisfy
$$\|u - u_n\|_\infty \le c \, \|K u - K_n u\|_\infty,$$ the consistency error of the quadrature
rule at the exact solution.

**Generalization.** The source takes a closed bounded set $D \subseteq \mathbb{R}^m$ with
Lebesgue measure, which is the case `IntegralOperator.regionMeasure D`.

The proof applies `AtkinsonHan.Chapter12.exists_norm_inverse_le_of_isCollectivelyCompactFamily`
to `AtkinsonHan.Chapter12.isCollectivelyCompactFamily_nystromCLM`. The bound (12.4.23) of the
source is part of `AtkinsonHan.Chapter12.theorem_12_4_3`. -/
theorem theorem_12_4_4 {μ : ℝ} (hμ : μ ≠ 0) (k : C(D × D, ℝ)) {m : ℕ → ℕ}
    {w : ∀ n, Fin (m n) → ℝ} {x : ∀ n, Fin (m n) → D} {W : ℝ} (hW : ∀ n, ∑ j, |w n j| ≤ W)
    (hQ : ∀ v : C(D, ℝ), Tendsto (fun n => Quadrature.functional (w n) (x n) v) atTop
      (𝓝 (integralCLM ν v)))
    {e : C(D, ℝ) ≃L[ℝ] C(D, ℝ)}
    (he : (e : C(D, ℝ) →L[ℝ] C(D, ℝ)) = μ • 1 - kernelCLM ν k) :
    ∃ c : ℝ, ∀ᶠ n in atTop, ∃ en : C(D, ℝ) ≃L[ℝ] C(D, ℝ),
      (en : C(D, ℝ) →L[ℝ] C(D, ℝ)) = μ • 1 - nystromCLM (w n) (x n) k ∧
      ‖(en.symm : C(D, ℝ) →L[ℝ] C(D, ℝ))‖ ≤ c ∧
      ∀ f u un : C(D, ℝ), (μ • 1 - kernelCLM ν k : C(D, ℝ) →L[ℝ] C(D, ℝ)) u = f →
        (μ • 1 - nystromCLM (w n) (x n) k : C(D, ℝ) →L[ℝ] C(D, ℝ)) un = f →
        ‖u - un‖ ≤ c * ‖kernelCLM ν k u - nystromCLM (w n) (x n) k u‖ :=
  exists_norm_inverse_le_of_isCollectivelyCompactFamily hμ
    (isCollectivelyCompactFamily_nystromCLM ν k hW hQ) he

end Nystrom

/-! ### Example 12.4.1: the equation the section computes with -/

section Example

open IntegralOperator MeasureTheory Set

/-- **Example 12.4.1** of [han2009theoretical], the rows of the kernel. For $x \in [0, 1]$,
$$\int_0^1 |e^{xy}|\, dy = \int_0^1 e^{xy}\, dy.$$ The kernel is positive, and on $[0, 1]$ the
clamping `Set.projIcc` does nothing. -/
theorem row_expKernel (x : Icc (0 : ℝ) 1) :
    ∫ y in (0 : ℝ)..1, |expKernel (x, projIcc 0 1 zero_le_one y)|
      = ∫ y in (0 : ℝ)..1, Real.exp ((x : ℝ) * y) := by
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le zero_le_one] at hy
  rw [expKernel]
  simp [projIcc_of_mem zero_le_one hy]

/-- **Example 12.4.1** of [han2009theoretical], the largest row integral. The largest value of
$\int_0^1 e^{xy}\, dy$ over $x \in [0, 1]$ is $e - 1$, attained at $x = 1$: for
$x, y \in [0, 1]$ one has $xy \le y$, so every row integral is at most
$\int_0^1 e^y\, dy = e - 1$. -/
theorem isGreatest_row_expKernel :
    IsGreatest (Set.range fun x : Icc (0 : ℝ) 1 => ∫ y in (0 : ℝ)..1, Real.exp ((x : ℝ) * y))
      (Real.exp 1 - 1) := by
  constructor
  · refine ⟨⟨1, by norm_num⟩, ?_⟩
    norm_num [integral_exp]
  · rintro _ ⟨x, rfl⟩
    have hx := x.2
    calc ∫ y in (0 : ℝ)..1, Real.exp ((x : ℝ) * y)
        ≤ ∫ y in (0 : ℝ)..1, Real.exp y := by
          refine intervalIntegral.integral_mono_on zero_le_one
            ((by fun_prop : Continuous fun y : ℝ => Real.exp ((x : ℝ) * y)).intervalIntegrable 0 1)
            (Real.continuous_exp.intervalIntegrable 0 1) fun y hy => ?_
          exact Real.exp_le_exp.2 (by nlinarith [hx.1, hx.2, hy.1, hy.2])
      _ = Real.exp 1 - 1 := by simp [integral_exp]

/-- **Example 12.4.1** of [han2009theoretical], the norm. The integral operator
$K u(x) = \int_0^1 e^{xy} u(y)\, dy$ of (12.4.7) on $C[0, 1]$ has $$\|K\| = e - 1,$$ the number
that the source gives as $\doteq 1.72$.

The proof applies the operator norm formula (2.2.8) for an integral operator on $C[a, b]$ to
`AtkinsonHan.Chapter12.isGreatest_row_expKernel`. -/
theorem norm_fredholm_expKernel :
    ‖fredholm zero_le_one expKernel‖ = Real.exp 1 - 1 := by
  have hne : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩
  rw [norm_fredholm zero_le_one expKernel]
  simp only [row_expKernel]
  exact isGreatest_row_expKernel.isLUB.ciSup_eq

/-- **Example 12.4.1** of [han2009theoretical]. For the equation (12.4.7), $$2 u(x) - \int_0^1
e^{xy} u(y)\, dy = f(x), \qquad 0 \le x \le 1,$$ the operator norm is
$\|K\| = e - 1 \doteq 1.72$. Hence $2 - K$ is invertible on $C[0, 1]$ with $$\|(2 - K)^{-1}\|
\le \frac{1}{2 - (e - 1)},$$ and every solution satisfies
$\|u\|_\infty \le \|f\|_\infty / (2 - (e - 1))$.

Since $\|K\| < |\lambda| = 2$, this is the geometric series theorem, Example 2.3.2 of the source
at this kernel (`AtkinsonHan.Chapter02.example_2_3_2_integral`). This is the reason that the
source gives for the choice $\lambda = 2$. The rest of Example 12.4.1 consists of computed
numbers and is not formalized; the general statement that they illustrate is
`AtkinsonHan.Chapter12.theorem_12_4_4`. -/
theorem example_12_4_1 :
    ‖fredholm zero_le_one expKernel‖ = Real.exp 1 - 1 ∧
      ∃ e : C(Icc (0 : ℝ) 1, ℝ) ≃L[ℝ] C(Icc (0 : ℝ) 1, ℝ),
        (e : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] C(Icc (0 : ℝ) 1, ℝ))
            = (2 : ℝ) • (1 : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] C(Icc (0 : ℝ) 1, ℝ))
              - fredholm zero_le_one expKernel ∧
          ‖(e.symm : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] C(Icc (0 : ℝ) 1, ℝ))‖
            ≤ 1 / (2 - (Real.exp 1 - 1)) ∧
          ∀ u f : C(Icc (0 : ℝ) 1, ℝ),
            (2 : ℝ) • u - fredholm zero_le_one expKernel u = f →
              ‖u‖ ≤ ‖f‖ / (2 - (Real.exp 1 - 1)) := by
  have hsup : (⨆ x, ∫ y in (0 : ℝ)..1, |expKernel (x, projIcc 0 1 zero_le_one y)|)
      = Real.exp 1 - 1 := by
    have hne : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩
    simp only [row_expKernel]
    exact isGreatest_row_expKernel.isLUB.ciSup_eq
  have hlt : (⨆ x, ∫ y in (0 : ℝ)..1, |expKernel (x, projIcc 0 1 zero_le_one y)|)
      < |(2 : ℝ)| := by
    rw [hsup, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := Real.exp_one_lt_d9
    linarith
  obtain ⟨e, he, hb, hu⟩ := Chapter02.example_2_3_2_integral zero_le_one expKernel hlt
  rw [hsup, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hb hu
  exact ⟨norm_fredholm_expKernel, e, he, hb, hu⟩

end Example

/-! ### The composite trapezoidal rule -/

/-- **Example 12.4.5** of [han2009theoretical] (error of the composite trapezoidal rule). Let
$a < b$, $N > 0$ and $h = (b - a)/N$, and let $g : \mathbb{R} \to \mathbb{R}$ be $C^2$. Then
there is $\xi \in [a, b]$ with $$\int_a^b g(t)\, dt - h \left[ \frac{g(a) + g(b)}{2} +
\sum_{j=1}^{N-1} g(a + j h) \right] = -\frac{h^2 (b - a)}{12} g''(\xi).$$

This is `Quadrature.sub_composite_trapezoid_eq` with the sum written as in the source, which is
`Quadrature.trapezoidSum_eq`. The asymptotic form (12.4.39),
`AtkinsonHan.Chapter12.equation_12_4_39`, is a different statement, and Example 12.4.6 uses that
one. -/
theorem example_12_4_5 {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) {h : ℝ}
    (hh : h = (b - a) / N) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) :
    ∃ ξ ∈ Set.Icc a b,
      (∫ t in a..b, g t) - h * ((g a + g b) / 2 + ∑ j ∈ Finset.Ico 1 N, g (a + j * h))
        = -(h ^ 2 * (b - a) / 12) * iteratedDeriv 2 g ξ := by
  have hd1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdd : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv.mp hg).2.2
  have hd2 : Differentiable ℝ (deriv g) := hdd.differentiable (by norm_num)
  have hc2 : Continuous (deriv (deriv g)) := (contDiff_one_iff_deriv.mp hdd).2
  have hiter : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hxN : a + (N : ℝ) * h = b := by
    have hc : (N : ℝ) * ((b - a) / N) = b - a := by field_simp
    rw [hh, hc]
    ring
  obtain ⟨ξ, hξ, hval⟩ := Quadrature.sub_composite_trapezoid_eq hab hN hh
    (g' := deriv g) (g'' := deriv (deriv g)) (fun x _ => (hd1 x).hasDerivAt)
    (fun x _ => (hd2 x).hasDerivAt) hc2.continuousOn
  refine ⟨ξ, hξ, ?_⟩
  rw [hiter, ← hval, Quadrature.trapezoidSum_eq hN, hxN]

/-- **Equation (12.4.39)** of [han2009theoretical] (asymptotic error of the composite trapezoidal
rule). Let $a < b$, $N > 0$ and $h = (b - a)/N$, and let $g : \mathbb{R} \to \mathbb{R}$ be
$C^4$ with $|g''''| \le M$ on $[a, b]$. Then $$\left| \int_a^b g(t)\, dt - h \left[ \frac{g(a) +
g(b)}{2} + \sum_{j=1}^{N-1} g(a + j h) \right] + \frac{h^2}{12} \left[ g'(b) - g'(a) \right]
\right| \le \frac{(b - a) h^4 M}{720}.$$ So the error is $-(h^2/12)[g'(b) - g'(a)] + O(h^4)$,
with an explicit remainder.

This is the first Euler–Maclaurin term. Unlike `AtkinsonHan.Chapter12.example_12_4_5` it names
the leading term, which Example 12.4.6 and Richardson extrapolation need. The source quotes the
result from the literature. It is `Quadrature.abs_sub_trapezoidSum_add_le`, proved by two more
integrations by parts of the Peano identity on each panel and a telescoping sum. -/
theorem equation_12_4_39 {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) {h : ℝ}
    (hh : h = (b - a) / N) {g : ℝ → ℝ} (hg : ContDiff ℝ 4 g) {M : ℝ}
    (hM : ∀ t ∈ Set.Icc a b, |iteratedDeriv 4 g t| ≤ M) :
    |(∫ t in a..b, g t) - h * ((g a + g b) / 2 + ∑ j ∈ Finset.Ico 1 N, g (a + j * h))
        + h ^ 2 / 12 * (deriv g b - deriv g a)| ≤ (b - a) * h ^ 4 * M / 720 := by
  have hd0 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hc3 : ContDiff ℝ 3 (deriv g) := (contDiff_succ_iff_deriv.mp hg).2.2
  have hd1 : Differentiable ℝ (deriv g) := hc3.differentiable (by norm_num)
  have hc2 : ContDiff ℝ 2 (deriv (deriv g)) := (contDiff_succ_iff_deriv.mp hc3).2.2
  have hd2 : Differentiable ℝ (deriv (deriv g)) := hc2.differentiable (by norm_num)
  have hc1 : ContDiff ℝ 1 (deriv (deriv (deriv g))) := (contDiff_succ_iff_deriv.mp hc2).2.2
  have hd3 : Differentiable ℝ (deriv (deriv (deriv g))) := hc1.differentiable (by norm_num)
  have hcont4 : Continuous (deriv (deriv (deriv (deriv g)))) := (contDiff_one_iff_deriv.mp hc1).2
  have hiter : iteratedDeriv 4 g = deriv (deriv (deriv (deriv g))) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hxN : a + (N : ℝ) * h = b := by
    have hc : (N : ℝ) * ((b - a) / N) = b - a := by field_simp
    rw [hh, hc]
    ring
  have hbound := Quadrature.abs_sub_trapezoidSum_add_le hab hN hh
    (g' := deriv g) (g'' := deriv (deriv g)) (g₃ := deriv (deriv (deriv g)))
    (g₄ := deriv (deriv (deriv (deriv g)))) (M := M) (fun t _ => (hd0 t).hasDerivAt)
    (fun t _ => (hd1 t).hasDerivAt) (fun t _ => (hd2 t).hasDerivAt)
    (fun t _ => (hd3 t).hasDerivAt) hcont4.continuousOn (by rw [← hiter]; exact hM)
  rwa [Quadrature.trapezoidSum_eq hN, hxN] at hbound

/-! ### The asymptotic error expansion of the Nyström solution -/

section Expansion

open IntegralOperator MeasureTheory

/-- Let $(\lambda - K) u = f$, $(\lambda - K_n) u_n = f$ and $(\lambda - K_n) \gamma_n = d$, with
$\lambda - K_n$ invertible. Then for every scalar $r$, $u - u_n - r \gamma_n = (\lambda -
K_n)^{-1} [(K - K_n) u - r d]$; at $r = 0$ this is (12.4.45). -/
private theorem sub_smul_eq_symm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : ℝ}
    {K Kn : V →L[ℝ] V} {en : V ≃L[ℝ] V} (hen : (en : V →L[ℝ] V) = μ • 1 - Kn)
    {u un f d γn : V} (hu : (μ • 1 - K : V →L[ℝ] V) u = f)
    (hun : (μ • 1 - Kn : V →L[ℝ] V) un = f) (hγn : (μ • 1 - Kn : V →L[ℝ] V) γn = d) (r : ℝ) :
    u - un - r • γn = en.symm (K u - Kn u - r • d) := by
  have e0 : (μ • 1 - Kn : V →L[ℝ] V) (u - un) = K u - Kn u := by
    rw [map_sub, hun, ← hu]
    simp only [sub_apply, smul_apply, one_apply_eq_self]
    abel
  have e1 : (μ • 1 - Kn : V →L[ℝ] V) (u - un - r • γn) = K u - Kn u - r • d := by
    rw [map_sub, map_smul, hγn, e0]
  rw [← e1, ← hen, ContinuousLinearEquiv.coe_coe, en.symm_apply_apply]

/-- If $(\lambda - K) \gamma = d$ and $(\lambda - K_n) \gamma_n = d$, with $\lambda - K_n$
invertible, then $\gamma_n - \gamma = (\lambda - K_n)^{-1} (K_n - K) \gamma$. -/
private theorem sub_aux_eq_symm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : ℝ}
    {K Kn : V →L[ℝ] V} {en : V ≃L[ℝ] V} (hen : (en : V →L[ℝ] V) = μ • 1 - Kn)
    {d γ γn : V} (hγ : (μ • 1 - K : V →L[ℝ] V) γ = d)
    (hγn : (μ • 1 - Kn : V →L[ℝ] V) γn = d) :
    γn - γ = en.symm (Kn γ - K γ) := by
  have e1 : (μ • 1 - Kn : V →L[ℝ] V) (γn - γ) = Kn γ - K γ := by
    rw [map_sub, hγn, ← hγ]
    simp only [sub_apply, smul_apply, one_apply_eq_self]
    abel
  rw [← e1, ← hen, ContinuousLinearEquiv.coe_coe, en.symm_apply_apply]

variable {a b : ℝ}

/-- **Equation (12.4.44)** of [han2009theoretical] (asymptotic error of the Nyström method with the
trapezoidal rule, uniformly in the row variable). Let $a < b$, let $k$ be a continuous kernel on
$[a, b] \times [a, b]$ with integral operator $K$, let $N > 0$ and $h = (b - a)/N$, and let
$K_n$ be the Nyström operator of a quadrature rule that equals the composite trapezoidal rule
with $N$ panels on every continuous function. Let $u \in C[a, b]$, and let
$G_t : \mathbb{R} \to \mathbb{R}$, for $t \in [a, b]$, be $C^4$ functions with
$G_t(y) = k(t, y) u(y)$ for $y \in [a, b]$ and $|G_t''''| \le M_4$ on $[a, b]$, with $M_4$
independent of $t$. Let $d(t) = -\frac{1}{12} [G_t'(b) - G_t'(a)]$, that is $d(t) =
-\frac{1}{12} \left[ \partial_y (k(t, y) u(y)) \right]_{y=a}^{y=b}$. Then $$\|(K - K_n) u - h^2
d\|_\infty \le \frac{(b - a) h^4 M_4}{720},$$ which is (12.4.44) with an explicit remainder.

The proof applies `AtkinsonHan.Chapter12.equation_12_4_39` at each row $t$. The bound is uniform
because $M_4$ does not depend on $t$. The quadrature hypothesis identifies
`IntegralOperator.nystromCLM` with `Quadrature.trapezoidSum` on the clamped integrand, with the
help of `IntegralOperator.nystromCLM_apply_eq_functional`. -/
theorem equation_12_4_44 (hab : a < b) (k : C(Set.Icc a b × Set.Icc a b, ℝ))
    {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : h = (b - a) / N)
    {m : ℕ} {w : Fin m → ℝ} {x : Fin m → Set.Icc a b}
    (hquad : ∀ v : C(Set.Icc a b, ℝ), Quadrature.functional w x v
      = Quadrature.trapezoidSum (fun y => v (Set.projIcc a b hab.le y)) a h N)
    (u : C(Set.Icc a b, ℝ)) {G : Set.Icc a b → ℝ → ℝ}
    (hG : ∀ t, ContDiff ℝ 4 (G t))
    (hGval : ∀ t y : Set.Icc a b, k (t, y) * u y = G t (y : ℝ))
    {M₄ : ℝ} (hM₄ : ∀ t : Set.Icc a b, ∀ y ∈ Set.Icc a b, |iteratedDeriv 4 (G t) y| ≤ M₄)
    {d : C(Set.Icc a b, ℝ)}
    (hd : ∀ t : Set.Icc a b, d t = -(1 / 12) * (deriv (G t) b - deriv (G t) a)) :
    ‖kernelCLM (iccMeasure a b) k u - nystromCLM w x k u - h ^ 2 • d‖
      ≤ (b - a) * h ^ 4 * M₄ / 720 := by
  have hab' : a ≤ b := hab.le
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hh0 : 0 < h := by
    rw [hh]
    exact div_pos (by linarith) hNR
  have hbN : a + (N : ℝ) * h = b := by
    rw [hh]
    field_simp
    ring
  have hnode : ∀ r : ℝ, 0 ≤ r → r ≤ (N : ℝ) → a + r * h ∈ Set.Icc a b := by
    intro r hr0 hrN
    refine ⟨by nlinarith, ?_⟩
    nlinarith
  have hM0 : (0 : ℝ) ≤ M₄ :=
    le_trans (abs_nonneg _) (hM₄ ⟨a, Set.left_mem_Icc.2 hab'⟩ a (Set.left_mem_Icc.2 hab'))
  have hKu : ∀ t : Set.Icc a b, kernelCLM (iccMeasure a b) k u t = ∫ y in a..b, G t y := by
    intro t
    rw [← fredholm_eq_kernelCLM hab' k, fredholm_apply]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hab'] at hy
    rw [hGval t (Set.projIcc a b hab' y), coe_projIcc_of_mem hab' hy]
  have hKnu : ∀ t : Set.Icc a b,
      nystromCLM w x k u t = Quadrature.trapezoidSum (G t) a h N := by
    intro t
    have hcl : ∀ r : ℝ, r ∈ Set.Icc a b →
        (rowMul k u t) (Set.projIcc a b hab' r) = G t r := by
      intro r hr
      rw [rowMul_apply, hGval t (Set.projIcc a b hab' r), coe_projIcc_of_mem hab' hr]
    rw [nystromCLM_apply_eq_functional, hquad, Quadrature.trapezoidSum, Quadrature.trapezoidSum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt : j < N := Finset.mem_range.1 hj
    have hjN : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hjlt.le
    have hj1 : (j : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hjlt
    rw [hcl _ (hnode _ (Nat.cast_nonneg j) hjN), hcl _ (hnode _ (by positivity) hj1)]
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  have htrap : Quadrature.trapezoidSum (G t) a h N
      = h * ((G t a + G t b) / 2 + ∑ j ∈ Finset.Ico 1 N, G t (a + j * h)) := by
    rw [Quadrature.trapezoidSum_eq hN, hbN]
  have hval : (kernelCLM (iccMeasure a b) k u - nystromCLM w x k u - h ^ 2 • d) t
      = (∫ y in a..b, G t y)
        - h * ((G t a + G t b) / 2 + ∑ j ∈ Finset.Ico 1 N, G t (a + j * h))
        + h ^ 2 / 12 * (deriv (G t) b - deriv (G t) a) := by
    rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
      hKu t, hKnu t, htrap, hd t]
    ring
  rw [hval, Real.norm_eq_abs]
  exact equation_12_4_39 hab hN hh (hG t) (hM₄ t)

/-- **Example 12.4.6** of [han2009theoretical] (asymptotic error expansion of the Nyström solution).
Let $a < b$, let $k$ be a continuous kernel on $[a, b] \times [a, b]$ with integral operator
$K$, and let $\lambda \neq 0$ be such that $\lambda - K$ is invertible. For each $n$ let
$N_n > 0$ and $h_n = (b - a)/N_n$, with $h_n \to 0$, and let $K_n$ be the Nyström operator of a
quadrature rule that equals the composite trapezoidal rule with $N_n$ panels, with
$\sum_j |w_{n,j}| \le W$ for all $n$. Let $u$, $G_t$, $M_4$ and $d$ be as in
`AtkinsonHan.Chapter12.equation_12_4_44`. Then there are a function $\gamma \in C[a, b]$, the
solution of the auxiliary equation $$\lambda \gamma(x) - \int_a^b k(x, y) \gamma(y)\, dy =
-\frac{1}{12} \left[ \partial_y (k(x, y) u(y)) \right]_{y=a}^{y=b},$$ and a constant $c$, such
that $\|(K - K_n) \gamma\| \to 0$ and, for all large $n$, there is $\gamma_n$ with
$(\lambda - K_n) \gamma_n = d$ and $\|\gamma_n - \gamma\| \le c \|(K - K_n) \gamma\|$, and,
whenever $(\lambda - K) u = f$ and $(\lambda - K_n) u_n = f$:

* $\|u - u_n - h_n^2 \gamma_n\|_\infty \le c (b - a) h_n^4 M_4 / 720$, which is (12.4.49) with
  $\gamma_n$ in place of $\gamma$ and an explicit remainder;
* for every $c_2$ with $\|(K - K_n) \gamma\| \le c_2 h_n^2$, $$\|u - u_n - h_n^2 \gamma\|_\infty
  \le c (b - a) h_n^4 M_4 / 720 + c c_2 h_n^4,$$ which is (12.4.49) with $\gamma$ itself.

In particular $\gamma_n \to \gamma$ and $u - u_n = h_n^2 \gamma + o(h_n^2)$. The bound
$\|(K - K_n) \gamma\| \le c_2 h_n^2$ follows from the smoothness of $\gamma$, by (12.4.43)
applied to the functions $y \mapsto k(x, y) \gamma(y)$ when these are $C^2$ uniformly in $x$. It
is the claim of the source that "by a similar argument, it can also be shown that
$r_n = O(h^4)$". A proof would differentiate $\gamma = \lambda^{-1}(d + K \gamma)$ twice under
the integral sign, which the library cannot do, so this bound is a hypothesis of the last
clause.

The proof replaces the $\varepsilon_n = (\lambda - K)^{-1} (K - K_n) u$ of the source by $h_n^2
\gamma_n = (\lambda - K_n)^{-1} (h_n^2 d)$. Then $(\lambda - K_n)(u - u_n - h_n^2 \gamma_n) =
(K - K_n) u - h_n^2 d$, whose norm `AtkinsonHan.Chapter12.equation_12_4_44` bounds, and
$(\lambda - K_n)(\gamma_n - \gamma) = (K_n - K) \gamma$. -/
theorem example_12_4_6 (hab : a < b) (k : C(Set.Icc a b × Set.Icc a b, ℝ))
    {N : ℕ → ℕ} (hN : ∀ n, 0 < N n) {hs : ℕ → ℝ} (hhs : ∀ n, hs n = (b - a) / N n)
    (hlim : Tendsto hs atTop (𝓝 0))
    {m : ℕ → ℕ} {w : ∀ n, Fin (m n) → ℝ} {x : ∀ n, Fin (m n) → Set.Icc a b} {W : ℝ}
    (hW : ∀ n, ∑ j, |w n j| ≤ W)
    (hquad : ∀ n, ∀ v : C(Set.Icc a b, ℝ), Quadrature.functional (w n) (x n) v
      = Quadrature.trapezoidSum (fun y => v (Set.projIcc a b hab.le y)) a (hs n) (N n))
    {μ : ℝ} (hμ : μ ≠ 0) {e : C(Set.Icc a b, ℝ) ≃L[ℝ] C(Set.Icc a b, ℝ)}
    (he : (e : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))
      = μ • 1 - kernelCLM (iccMeasure a b) k)
    (u : C(Set.Icc a b, ℝ)) {G : Set.Icc a b → ℝ → ℝ} (hG : ∀ t, ContDiff ℝ 4 (G t))
    (hGval : ∀ t y : Set.Icc a b, k (t, y) * u y = G t (y : ℝ))
    {M₄ : ℝ} (hM₄ : ∀ t : Set.Icc a b, ∀ y ∈ Set.Icc a b, |iteratedDeriv 4 (G t) y| ≤ M₄)
    {d : C(Set.Icc a b, ℝ)}
    (hd : ∀ t : Set.Icc a b, d t = -(1 / 12) * (deriv (G t) b - deriv (G t) a)) :
    ∃ (γ : C(Set.Icc a b, ℝ)) (c : ℝ),
      (μ • 1 - kernelCLM (iccMeasure a b) k :
        C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) γ = d ∧
      Tendsto (fun n => ‖kernelCLM (iccMeasure a b) k γ - nystromCLM (w n) (x n) k γ‖)
        atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∃ γn : C(Set.Icc a b, ℝ),
        (μ • 1 - nystromCLM (w n) (x n) k :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) γn = d ∧
        ‖γn - γ‖ ≤ c * ‖kernelCLM (iccMeasure a b) k γ - nystromCLM (w n) (x n) k γ‖ ∧
        ∀ f un : C(Set.Icc a b, ℝ),
          (μ • 1 - kernelCLM (iccMeasure a b) k :
            C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) u = f →
          (μ • 1 - nystromCLM (w n) (x n) k :
            C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = f →
          ‖u - un - hs n ^ 2 • γn‖ ≤ c * ((b - a) * hs n ^ 4 * M₄ / 720) ∧
          ∀ c₂ : ℝ,
            ‖kernelCLM (iccMeasure a b) k γ - nystromCLM (w n) (x n) k γ‖ ≤ c₂ * hs n ^ 2 →
            ‖u - un - hs n ^ 2 • γ‖
              ≤ c * ((b - a) * hs n ^ 4 * M₄ / 720) + c * c₂ * hs n ^ 4 := by
  have hab' : a ≤ b := hab.le
  have hQ : ∀ v : C(Set.Icc a b, ℝ),
      Tendsto (fun n => Quadrature.functional (w n) (x n) v) atTop
        (𝓝 (integralCLM (iccMeasure a b) v)) := by
    intro v
    have hcont : ContinuousOn (fun y : ℝ => v (Set.projIcc a b hab' y)) (Set.Icc a b) :=
      (continuous_apply_projIcc hab' v).continuousOn
    have hint : integralCLM (iccMeasure a b) v = ∫ y in a..b, v (Set.projIcc a b hab' y) := by
      rw [integralCLM_apply, ← integral_iccMeasure hab' fun y => v (Set.projIcc a b hab' y)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp)
    rw [hint]
    refine (Quadrature.tendsto_trapezoidSum (g := fun y : ℝ => v (Set.projIcc a b hab' y))
      hab' hcont hN hhs hlim).congr fun n => ?_
    rw [hquad n v]
  have hfam := isCollectivelyCompactFamily_nystromCLM (iccMeasure a b) k hW hQ
  obtain ⟨c₀, hc₀⟩ := theorem_12_4_4 (ν := iccMeasure a b) hμ k hW hQ he
  have hγ : (μ • 1 - kernelCLM (iccMeasure a b) k :
      C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) (e.symm d) = d := by
    rw [← he, ContinuousLinearEquiv.coe_coe, e.apply_symm_apply]
  refine ⟨e.symm d, c₀, hγ, ?_, ?_⟩
  · have h1 : Tendsto (fun n => nystromCLM (w n) (x n) k (e.symm d)) atTop
        (𝓝 (kernelCLM (iccMeasure a b) k (e.symm d))) := hfam.tendsto (e.symm d)
    have h2 : Tendsto (fun n => kernelCLM (iccMeasure a b) k (e.symm d)
        - nystromCLM (w n) (x n) k (e.symm d)) atTop
        (𝓝 (kernelCLM (iccMeasure a b) k (e.symm d)
          - kernelCLM (iccMeasure a b) k (e.symm d))) := tendsto_const_nhds.sub h1
    rw [sub_self] at h2
    simpa using h2.norm
  filter_upwards [hc₀] with n hn
  obtain ⟨en, hencoe, hennorm, -⟩ := hn
  have hc00 : (0 : ℝ) ≤ c₀ := le_trans (norm_nonneg _) hennorm
  have hsym : ∀ v : C(Set.Icc a b, ℝ), ‖en.symm v‖ ≤ c₀ * ‖v‖ := fun v =>
    (ContinuousLinearMap.le_opNorm (en.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) v).trans
      (mul_le_mul_of_nonneg_right hennorm (norm_nonneg v))
  have hγn : (μ • 1 - nystromCLM (w n) (x n) k :
      C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) (en.symm d) = d := by
    rw [← hencoe, ContinuousLinearEquiv.coe_coe, en.apply_symm_apply]
  have hgap : ‖en.symm d - e.symm d‖
      ≤ c₀ * ‖kernelCLM (iccMeasure a b) k (e.symm d)
        - nystromCLM (w n) (x n) k (e.symm d)‖ := by
    rw [sub_aux_eq_symm hencoe hγ hγn]
    refine (hsym _).trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) hc00)
    exact norm_sub_rev _ _
  refine ⟨en.symm d, hγn, hgap, fun f un hu hun => ?_⟩
  have hbase : ‖u - un - hs n ^ 2 • en.symm d‖ ≤ c₀ * ((b - a) * hs n ^ 4 * M₄ / 720) := by
    rw [sub_smul_eq_symm hencoe hu hun hγn (hs n ^ 2)]
    refine (hsym _).trans (mul_le_mul_of_nonneg_left ?_ hc00)
    exact equation_12_4_44 hab k (hN n) (hhs n) (hquad n) u hG hGval hM₄ hd
  refine ⟨hbase, fun c₂ hc₂ => ?_⟩
  have hsq : (0 : ℝ) ≤ hs n ^ 2 := sq_nonneg _
  have hsplit : u - un - hs n ^ 2 • e.symm d
      = (u - un - hs n ^ 2 • en.symm d) + hs n ^ 2 • (en.symm d - e.symm d) := by
    rw [smul_sub]
    abel
  calc ‖u - un - hs n ^ 2 • e.symm d‖
      ≤ ‖u - un - hs n ^ 2 • en.symm d‖ + ‖hs n ^ 2 • (en.symm d - e.symm d)‖ := by
        rw [hsplit]
        exact norm_add_le _ _
    _ = ‖u - un - hs n ^ 2 • en.symm d‖ + hs n ^ 2 * ‖en.symm d - e.symm d‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsq]
    _ ≤ c₀ * ((b - a) * hs n ^ 4 * M₄ / 720) + hs n ^ 2 * (c₀ * (c₂ * hs n ^ 2)) := by
        gcongr
        exact hgap.trans (mul_le_mul_of_nonneg_left hc₂ hc00)
    _ = c₀ * ((b - a) * hs n ^ 4 * M₄ / 720) + c₀ * c₂ * hs n ^ 4 := by ring

end Expansion

end AtkinsonHan.Chapter12
