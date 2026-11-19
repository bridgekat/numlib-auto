/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Numlib.Analysis.PDE.Heat.SineSeries
import Numlib.FiniteDifference.LaxEquivalence

/-!
# Atkinson and Han, Section 6.2: The Lax equivalence theorem

This module formalizes Section 6.2 of [han2009theoretical]. The section studies the abstract initial
value problem $u'(t) = L u(t)$ for $t \in [0, T]$, $u(0) = u_0$, in a Banach space $V$, for a linear
and generally unbounded operator $L$ defined on a dense subspace $V_0 \subseteq V$. A well-posed
problem has bounded solution operators $S(t)$ with $S(t) u_0 = u(t)$, and $S(t) u_0$ for
$u_0 \notin V_0$ is the generalized solution. A difference method is a family of bounded operators
$C(\Delta t)$, and $C(\Delta t)^m u_0$ approximates $u(m \Delta t)$. The Lax equivalence theorem
(Theorem 6.2.11) says that a consistent method for a well-posed problem converges if and only if it
is stable.

The running example is the heat equation $u_t = \nu u_{xx}$ on $(0, \pi) \times (0, T)$ with
homogeneous Dirichlet boundary values, in $V = C_0[0, \pi]$ with the maximum norm, with $V_0$ the
finite sine polynomials (6.2.5) and $L = \nu \, \partial^2 / \partial x^2$ on $V_0$. The problem is
well posed with $c_0 = 1$ (Example 6.2.4). The forward scheme is consistent and is stable if and
only if the mesh ratio $r = \nu \Delta t / \Delta x^2$ satisfies $r \le 1/2$, and the backward
scheme is consistent and stable for every $r$ (Examples 6.2.8 and 6.2.13, Exercise 6.2.3). The
abstract results specialize `Numlib.FiniteDifference.LaxEquivalence`, and the example uses
`Numlib.Analysis.PDE.Heat.SineSeries`, `Numlib.Analysis.Fourier.SineBasis` and
`Numlib.Analysis.Fourier.OddExtension`.

## Main definitions

* Definition 6.2.1, `AtkinsonHan.Chapter06.IsSolution`: $u$ solves $u' = Lu$, $u(0) = u_0$ on
  $[0, T]$, with the derivative a limit of difference quotients within $[0, T]$.
* Definition 6.2.2, `AtkinsonHan.Chapter06.IsWellPosed`: existence, uniqueness and the stability
  bound $\|u(t) - \bar u(t)\| \le c_0 \|u_0 - \bar u_0\|$ (6.2.3).
* Definition 6.2.3, `AtkinsonHan.Chapter06.solutionOperator`: the bounded solution operators $S(t)$
  of a well-posed problem with a dense domain.
* Example 6.2.4, `AtkinsonHan.Chapter06.C₀`: the space $V = C_0[0, \pi]$ of continuous functions on
  $[0, \pi]$ that vanish at both ends.
* Example 6.2.4, `AtkinsonHan.Chapter06.sinePolynomials`: the subspace $V_0$ of (6.2.5), spanned by
  the functions $\sin(jx)$, $j \ge 1$.
* Example 6.2.4, `AtkinsonHan.Chapter06.heatOperator`: the operator
  $L = \nu \, \partial^2 / \partial x^2$ with domain $V_0$.
* Equation (6.2.7), `AtkinsonHan.Chapter06.sineSolution`: the solution
  $u(t) = \sum_j b_j e^{-\nu j^2 t} \sin(jx)$ for a sine polynomial initial value.
* Definition 6.2.7, `AtkinsonHan.Chapter06.IsConsistent`: the local truncation error divided by
  $\Delta t$ tends to $0$ uniformly in $t$, on a dense set of initial values.
* Example 6.2.8, `AtkinsonHan.Chapter06.forwardScheme`: the forward scheme $C(\Delta t) v = (1 - 2r)
  v + r [\tilde v(\cdot + \Delta x) + \tilde v(\cdot - \Delta x)]$.
* Example 6.2.8, `AtkinsonHan.Chapter06.backwardScheme`: the backward scheme
  $C(\Delta t) = Q_1^{-1}$ with $Q_1 = (1 + 2r) I - r [\tilde v(\cdot + \Delta x) + \tilde v(\cdot -
  \Delta x)]$.
* Definition 6.2.9, `AtkinsonHan.Chapter06.IsConvergent`:
  $\|(C(\Delta t_i)^{m_i} - S(t)) u_0\| \to 0$ whenever $\Delta t_i \to 0$ and
  $m_i \Delta t_i \to t$.
* Definition 6.2.10, `AtkinsonHan.Chapter06.IsStable`: the powers $C(\Delta t)^m$ with
  $m \Delta t \le T$ are uniformly bounded.

## Main results

* Example 6.2.4, `AtkinsonHan.Chapter06.example_6_2_4`: the heat equation is well posed in
  $C_0[0, \pi]$ with $c_0 = 1$.
* Example 6.2.4 and Exercise 6.2.1, `AtkinsonHan.Chapter06.example_6_2_4_dense`: the sine
  polynomials are dense in $C_0[0, \pi]$.
* Example 6.2.4, `AtkinsonHan.Chapter06.example_6_2_4_norm_solutionOperator_le`: the solution
  operators of the heat equation satisfy $\|S(t)\| \le 1$.
* Example 6.2.4, `AtkinsonHan.Chapter06.isSolution_sineSolution`: the curve (6.2.7) is a solution
  for a sine polynomial initial value.
* Example 6.2.4, `AtkinsonHan.Chapter06.example_6_2_4_solutionOperator_apply`: the solution
  operators map a sine polynomial initial value to the curve (6.2.7).
* Proposition 6.2.5, `AtkinsonHan.Chapter06.proposition_6_2_5`: the generalized solution
  $t \mapsto S(t) u_0$ is continuous on $[0, T]$ for every $u_0 \in V$.
* Proposition 6.2.6, `AtkinsonHan.Chapter06.proposition_6_2_6`: the solution operators satisfy
  $S(t_1 + t_0) = S(t_1) S(t_0)$.
* Example 6.2.8, `AtkinsonHan.Chapter06.norm_forwardScheme_le`: the bound (6.2.8),
  $\|C(\Delta t)\| \le |1 - 2r| + 2r$, for the forward scheme.
* Example 6.2.8, `AtkinsonHan.Chapter06.example_6_2_8`: the forward scheme is consistent on the sine
  polynomials.
* Example 6.2.8, `AtkinsonHan.Chapter06.norm_backwardScheme_le`: the backward scheme satisfies
  $\|C(\Delta t)\| \le 1$ for every $r \ge 0$.
* Example 6.2.8, `AtkinsonHan.Chapter06.example_6_2_8_backward`: the backward scheme is consistent
  on the sine polynomials.
* Theorem 6.2.11, `AtkinsonHan.Chapter06.theorem_6_2_11`: the Lax equivalence theorem, stability is
  equivalent to convergence.
* Corollary 6.2.12, `AtkinsonHan.Chapter06.corollary_6_2_12`: a stable method with local error
  $O(\Delta t^{k+1})$ has global error at most $M_0 t c \Delta t^k$.
* Example 6.2.13, `AtkinsonHan.Chapter06.example_6_2_13`: for $r \le 1/2$ the forward scheme is
  stable and convergent.
* Example 6.2.13, `AtkinsonHan.Chapter06.example_6_2_13_backward`: the backward scheme is stable and
  convergent for every $r > 0$.
* Exercise 6.2.3, `AtkinsonHan.Chapter06.norm_forwardScheme_eq`: $\|C(\Delta t)\| = |1 - 2r| + 2r$
  for the forward scheme when $\Delta x < \pi/2$.
* Exercise 6.2.3, `AtkinsonHan.Chapter06.not_isStable_forwardScheme`: for $r > 1/2$ the forward
  scheme is not stable.

## Implementation notes

* The source allows real or complex scalars. This module takes $V$ over $\mathbb{R}$; the backbone
  `Numlib.FiniteDifference.LaxEquivalence` has the same results over any `RCLike` field.
* The operator $L : V_0 \subseteq V \to V$ is a `LinearPMap`, `L : V →ₗ.[ℝ] V`, with
  `Dense (L.domain : Set V)`, as for the closed operators of Section 8.2.
* Definition 6.2.1 is a limit of the difference quotient $(u(s) - u(t))/(s - t)$ as $s \to t$ within
  $[0, T]$, and Definition 6.2.7 divides by $\Delta t$. The backbone uses `HasDerivWithinAt` and
  clears the division. `AtkinsonHan.Chapter06.isSolution_iff` and
  `AtkinsonHan.Chapter06.isConsistent_iff` identify the two forms.
* Definition 6.2.3 is an existence statement in the backbone,
  `FiniteDifference.exists_solutionOperator`, which is the appeal of the source to its Theorem 2.4.1
  (proved here as `AtkinsonHan.Chapter02.theorem_2_4_1`). `AtkinsonHan.Chapter06.solutionOperator`
  chooses the family once. Only its three properties `AtkinsonHan.Chapter06.solutionOperator_zero`,
  `AtkinsonHan.Chapter06.norm_solutionOperator_le` and
  `AtkinsonHan.Chapter06.solutionOperator_apply` are meaningful, because the choice is not canonical
  outside $[0, T]$.
* The Lax equivalence theorem does not use the semigroup property of Proposition 6.2.6.
* In the heat example, $L$ is defined by its action $\sin(jx) \mapsto -\nu j^2 \sin(jx)$ on the
  basis of $V_0$, and `AtkinsonHan.Chapter06.heatOperator_apply_eq_laplacian` identifies it with
  $\nu$ times the second derivative. The maximum principle
  `Heat.IsClassicalSolution.abs_le_of_eq_zero_frontier` gives the stability bound. The schemes act
  on the odd $2\pi$-periodic extension $\tilde v$ of $v$, `oddPeriodicExtend`, with the space step
  $\Delta x = \sqrt{\nu \Delta t / r}$.

## Deviations from the source

* **Definition 6.2.7** (reading). The truncation error is tested only at the $t \in [0, T]$ with
  $t + \Delta t \le T$, where the solution operators are determined. Any dense set of
  initial values suffices in place of a dense linear subspace. See
  `AtkinsonHan.Chapter06.IsConsistent`.
* **Definition 6.2.9** (reading). The limit is taken along every pair of sequences
  $(\Delta t_i, m_i)$ with $\Delta t_i \to 0$ and $m_i \Delta t_i \to t$, restricted to
  $m_i \Delta t_i \le T$. See `AtkinsonHan.Chapter06.IsConvergent`.
* **Proposition 6.2.6** (reading). The statement assumes well-posedness on every horizon $T' \le T$,
  not only on $T$. See `AtkinsonHan.Chapter06.proposition_6_2_6`.
* **Theorem 6.2.11** (reading). The statement takes the uniform bound
  $\|C(\Delta t)\| \le c_1$ as an argument. The source explicitly assumes this bound
  when introducing the family, before stating the theorem. See
  `AtkinsonHan.Chapter06.theorem_6_2_11`.
* **Corollary 6.2.12** (correction and scope). The source prints the same constant $c$
  for the local and global bounds. The estimate takes a bound $M_0$ on the powers as
  a hypothesis and has the factor $M_0 t c$ in the global error. It applies at one
  fixed step size to any initial value satisfying the local bound.
* **Example 6.2.8** (scope). The stencil definitions extend to arbitrary real parameters
  using totalized division, square root and, for the backward scheme, inversion. The
  local error estimates replace Taylor remainder notation with explicit sine-series bounds.
* **Exercise 6.2.3** (correction). The equality $\|C(\Delta t)\| = |1 - 2r| + 2r$ needs a small
  space step; the library assumes $\Delta x < \pi/2$. See
  `AtkinsonHan.Chapter06.norm_forwardScheme_eq`.

## Not formalized

* **Exercise 6.2.2** (the Crank–Nicolson scheme).
-/

open Filter Set Topology

namespace AtkinsonHan.Chapter06

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The abstract initial value problem -/

/-- **Definition 6.2.1** of [han2009theoretical], with (6.2.2). Let $L : V_0 \subseteq V \to V$ be a
linear operator and let $T \in \mathbb{R}$. A function $u : \mathbb{R} \to V$ is a **solution**
of $u' = Lu$, $u(0) = u_0$ on $[0, T]$ if $u(0) = u_0$ and, for every $t \in [0, T]$,
$u(t) \in V_0$ and
$$\frac{u(s) - u(t)}{s - t} \to L u(t) \qquad \text{as } s \to t,\ s \in [0, T] \setminus
  \{t\}.$$

The limit within the closed interval is the one-sided derivative of the source at the two
endpoints. Only the values of $u$ on $[0, T]$ and at $0$ matter. -/
def IsSolution (L : V →ₗ.[ℝ] V) (T : ℝ) (u₀ : V) (u : ℝ → V) : Prop :=
  u 0 = u₀ ∧ ∀ t ∈ Icc (0 : ℝ) T, ∃ h : u t ∈ L.domain,
    Tendsto (fun s : ℝ => (s - t)⁻¹ • (u s - u t)) (𝓝[Icc 0 T \ {t}] t) (𝓝 (L ⟨u t, h⟩))

/-- The difference quotient $(u(s) - u(t))/(s - t)$ is Mathlib's `slope u t s`. -/
private theorem slope_eq (u : ℝ → V) (t : ℝ) :
    slope u t = fun s : ℝ => (s - t)⁻¹ • (u s - u t) := rfl

/-- A function $u$ is a solution in the sense of Definition 6.2.1 if and only if it is a solution in
the sense of the backbone, `FiniteDifference.IsSolution`, where the derivative is
`HasDerivWithinAt` on $[0, T]$. -/
theorem isSolution_iff (L : V →ₗ.[ℝ] V) (T : ℝ) (u₀ : V) (u : ℝ → V) :
    IsSolution L T u₀ u ↔ FiniteDifference.IsSolution L T u₀ u := by
  simp only [IsSolution, FiniteDifference.IsSolution, hasDerivWithinAt_iff_tendsto_slope, slope_eq]

/-- **Definition 6.2.2** of [han2009theoretical], with (6.2.3). The initial value problem $u' = Lu$,
$u(0) = u_0$ is **well posed** on $[0, T]$ with stability constant $c_0$ if the following hold.

1. For every $u_0 \in V_0$ there is a solution on $[0, T]$.
2. Two solutions with the same initial value $u_0 \in V_0$ agree on $[0, T]$.
3. Any two solutions $u$ and $\bar u$ with initial values $u_0$ and $\bar u_0$ satisfy $\|u(t) -
   \bar u(t)\| \le c_0 \|u_0 - \bar u_0\|$ for all $t \in [0, T]$.

Uniqueness is agreement on $[0, T]$, because the source constrains $u$ only there. It follows
from the stability bound with $u_0 = \bar u_0$ (`FiniteDifference.IsWellPosed.eqOn`), so the
backbone predicate has only the clauses 1 and 3; `AtkinsonHan.Chapter06.isWellPosed_iff` shows
that the two predicates agree. -/
def IsWellPosed (L : V →ₗ.[ℝ] V) (T c₀ : ℝ) : Prop :=
  (∀ u₀ ∈ L.domain, ∃ u, IsSolution L T u₀ u) ∧
    (∀ u₀ ∈ L.domain, ∀ u ū, IsSolution L T u₀ u → IsSolution L T u₀ ū → EqOn u ū (Icc 0 T)) ∧
      ∀ u₀ ū₀ u ū, IsSolution L T u₀ u → IsSolution L T ū₀ ū →
        ∀ t ∈ Icc (0 : ℝ) T, ‖u t - ū t‖ ≤ c₀ * ‖u₀ - ū₀‖

/-- The problem is well posed in the sense of Definition 6.2.2 if and only if it is well posed in
the sense of the backbone, `FiniteDifference.IsWellPosed`, which has no uniqueness clause. -/
theorem isWellPosed_iff (L : V →ₗ.[ℝ] V) (T c₀ : ℝ) :
    IsWellPosed L T c₀ ↔ FiniteDifference.IsWellPosed L T c₀ := by
  constructor
  · rintro ⟨hex, -, hst⟩
    refine ⟨fun u₀ hu₀ => (hex u₀ hu₀).imp fun u hu => (isSolution_iff L T u₀ u).1 hu,
      fun u₀ ū₀ u ū hu hū => hst u₀ ū₀ u ū ((isSolution_iff L T u₀ u).2 hu)
        ((isSolution_iff L T ū₀ ū).2 hū)⟩
  · intro hwp
    refine ⟨fun u₀ hu₀ => (hwp.1 u₀ hu₀).imp fun u hu => (isSolution_iff L T u₀ u).2 hu,
      fun u₀ _ u ū hu hū => hwp.eqOn ((isSolution_iff L T u₀ u).1 hu)
        ((isSolution_iff L T u₀ ū).1 hū),
      fun u₀ ū₀ u ū hu hū => hwp.2 u₀ ū₀ u ū ((isSolution_iff L T u₀ u).1 hu)
        ((isSolution_iff L T ū₀ ū).1 hū)⟩

/-- A solution on $[0, T]$ is a solution on $[0, T']$ for every $T' \le T$. -/
private theorem isSolution_mono {L : V →ₗ.[ℝ] V} {T T' : ℝ} {u₀ : V} {u : ℝ → V}
    (hu : FiniteDifference.IsSolution L T u₀ u) (hT' : T' ≤ T) :
    FiniteDifference.IsSolution L T' u₀ u := by
  refine ⟨hu.1, fun t ht => ?_⟩
  obtain ⟨h, hd⟩ := hu.2 t ⟨ht.1, ht.2.trans hT'⟩
  exact ⟨h, hd.mono (Icc_subset_Icc le_rfl hT')⟩

/-! ### Definition 6.2.3: the solution operators and the generalized solution -/

section SolutionOperator

variable [CompleteSpace V]

/-- **Definition 6.2.3** of [han2009theoretical]. Let $V$ be a Banach space, let
$L : V_0 \subseteq V \to V$ have a dense domain, let $T \ge 0$ and $c_0 \ge 0$, and let the
problem be well posed on $[0, T]$ with constant $c_0$. The **solution operators** are a family
of bounded linear operators $S(t) : V \to V$ with $S(0) = I$, $\|S(t)\| \le c_0$ for
$t \in [0, T]$, and $S(t) u_0 = u(t)$ for $t \in [0, T]$ whenever $u_0 \in V_0$ and $u$ is the
solution with initial value $u_0$. For $u_0 \notin V_0$, the function $t \mapsto S(t) u_0$ is
the **generalized solution**.

The backbone gives the family as an existence statement,
`FiniteDifference.exists_solutionOperator`, which is the appeal of the source to its Theorem
2.4.1 on the extension of a bounded operator from a dense subspace. This definition chooses one
such family. Its three properties are `AtkinsonHan.Chapter06.solutionOperator_zero`,
`AtkinsonHan.Chapter06.norm_solutionOperator_le` and
`AtkinsonHan.Chapter06.solutionOperator_apply`; no other property should be used, because the
choice is not canonical outside $[0, T]$. -/
noncomputable def solutionOperator (L : V →ₗ.[ℝ] V) (hdense : Dense (L.domain : Set V)) {T c₀ : ℝ}
    (hT : 0 ≤ T) (hc₀ : 0 ≤ c₀) (hwp : IsWellPosed L T c₀) : ℝ → V →L[ℝ] V :=
  (FiniteDifference.exists_solutionOperator L hdense hT hc₀
    ((isWellPosed_iff L T c₀).1 hwp)).choose

variable (L : V →ₗ.[ℝ] V) (hdense : Dense (L.domain : Set V)) {T c₀ : ℝ} (hT : 0 ≤ T)
  (hc₀ : 0 ≤ c₀) (hwp : IsWellPosed L T c₀)

private theorem solutionOperator_spec :
    solutionOperator L hdense hT hc₀ hwp 0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖solutionOperator L hdense hT hc₀ hwp t‖ ≤ c₀) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ u₀ ∈ L.domain, ∀ u, FiniteDifference.IsSolution L T u₀ u →
        solutionOperator L hdense hT hc₀ hwp t u₀ = u t :=
  (FiniteDifference.exists_solutionOperator L hdense hT hc₀
    ((isWellPosed_iff L T c₀).1 hwp)).choose_spec

/-- The solution operators satisfy $S(0) = I$. -/
theorem solutionOperator_zero : solutionOperator L hdense hT hc₀ hwp 0 = 1 :=
  (solutionOperator_spec L hdense hT hc₀ hwp).1

/-- The solution operators satisfy $\|S(t)\| \le c_0$ for every $t \in [0, T]$, the stability bound
of (6.2.3). -/
theorem norm_solutionOperator_le :
    ∀ t ∈ Icc (0 : ℝ) T, ‖solutionOperator L hdense hT hc₀ hwp t‖ ≤ c₀ :=
  (solutionOperator_spec L hdense hT hc₀ hwp).2.1

/-- If $t \in [0, T]$, $u_0 \in V_0$ and $u$ is a solution with initial value $u_0$, then
$S(t) u_0 = u(t)$. -/
theorem solutionOperator_apply {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {u₀ : V} (hu₀ : u₀ ∈ L.domain)
    (u : ℝ → V) (hu : IsSolution L T u₀ u) : solutionOperator L hdense hT hc₀ hwp t u₀ = u t :=
  (solutionOperator_spec L hdense hT hc₀ hwp).2.2 t ht u₀ hu₀ u ((isSolution_iff L T u₀ u).1 hu)

/-- **Proposition 6.2.5** of [han2009theoretical]. Under the hypotheses of Definition 6.2.3, for
every $u_0 \in V$ the generalized solution $t \mapsto S(t) u_0$ is continuous on $[0, T]$.

For $u_0 \in V_0$ the function is a solution, hence continuous. The uniform bound
$\|S(t)\| \le c_0$ and the density of $V_0$ extend the continuity to every $u_0$, by the density
criterion of the Banach–Steinhaus theorem. -/
theorem proposition_6_2_5 (u₀ : V) :
    ContinuousOn (fun t => solutionOperator L hdense hT hc₀ hwp t u₀) (Icc 0 T) := by
  refine FiniteDifference.continuousOn_of_dense hdense
    (norm_solutionOperator_le L hdense hT hc₀ hwp) (fun v hv => ?_) u₀
  obtain ⟨u, hu⟩ := hwp.1 v hv
  refine ContinuousOn.congr ?_ (fun t ht =>
    solutionOperator_apply L hdense hT hc₀ hwp ht hv u hu)
  intro t ht
  obtain ⟨_, hd⟩ := ((isSolution_iff L T v u).1 hu).2 t ht
  exact HasDerivWithinAt.continuousWithinAt hd

/-- **Proposition 6.2.6** of [han2009theoretical]. Under the hypotheses of Definition 6.2.3, assume
also that the problem is well posed with constant $c_0$ on every horizon $T' \in [0, T]$. Then
for $t_0, t_1 \ge 0$ with $t_1 + t_0 \le T$,
$$S(t_1 + t_0) = S(t_1) S(t_0).$$

**Reading.** The source assumes well-posedness on $[0, T]$ only. The proof translates a solution
back by $t_0$, which gives a solution on $[0, T - t_0]$, and it needs uniqueness on that shorter
interval to identify the translate with the solution that starts at $S(t_0) u_0$.

The Lax equivalence theorem `AtkinsonHan.Chapter06.theorem_6_2_11` does not use this result. -/
theorem proposition_6_2_6 (hwp' : ∀ T' ∈ Icc (0 : ℝ) T, IsWellPosed L T' c₀) {t₀ t₁ : ℝ}
    (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁) (hsum : t₁ + t₀ ≤ T) :
    solutionOperator L hdense hT hc₀ hwp (t₁ + t₀)
      = solutionOperator L hdense hT hc₀ hwp t₁ ∘L solutionOperator L hdense hT hc₀ hwp t₀ := by
  refine FiniteDifference.solutionOperator_add hdense
    (fun u₀ hu₀ => (hwp.1 u₀ hu₀).imp fun u hu => (isSolution_iff L T u₀ u).1 hu) ?_ ht₀ ht₁ hsum
  intro T' hT' t ht u₀ hu₀ u hu
  obtain ⟨w, hw⟩ := hwp.1 u₀ hu₀
  have hwb : FiniteDifference.IsSolution L T u₀ w := (isSolution_iff L T u₀ w).1 hw
  have hwT' : IsSolution L T' u₀ w := (isSolution_iff L T' u₀ w).2 (isSolution_mono hwb hT'.2)
  have hEq := (hwp' T' hT').2.1 u₀ hu₀ u w ((isSolution_iff L T' u₀ u).2 hu) hwT'
  rw [solutionOperator_apply L hdense hT hc₀ hwp ⟨ht.1, ht.2.trans hT'.2⟩ hu₀ w hw]
  exact (hEq ht).symm

end SolutionOperator

/-! ### Consistency, stability and convergence -/

/-- **Definition 6.2.7** of [han2009theoretical]. Let $S, C : \mathbb{R} \to \mathcal{L}(V)$, let
$T, \Delta_0 \in \mathbb{R}$ and let $V_c \subseteq V$. The difference method $\{C(\Delta t)\}$
is **consistent** with the family $S$ on $[0, T]$, for step sizes in $(0, \Delta_0]$ and initial
values in $V_c$, if $V_c$ is dense in $V$ and, for every $u_0 \in V_c$ and every
$\varepsilon > 0$, there is $\delta > 0$ such that
$$\Big\| \frac{C(\Delta t) u(t) - u(t + \Delta t)}{\Delta t} \Big\| \le \varepsilon, \qquad
  u(t) = S(t) u_0,$$
for all $\Delta t \in (0, \Delta_0]$ with $\Delta t < \delta$ and all $t \in [0, T]$ with
$t + \Delta t \le T$.

**Reading.** The source tests all $t \in [0, T]$. The condition $t + \Delta t \le T$ keeps $S$
on the horizon $[0, T]$, where the solution operators of Definition 6.2.3 are determined. The
proof of Theorem 6.2.11 uses the truncation error only at grid points $k \Delta t$ with
$(k + 1) \Delta t \le T$.

The division is written as in the source. The backbone `FiniteDifference.IsConsistent` clears
it, and `AtkinsonHan.Chapter06.isConsistent_iff` identifies the two forms. -/
def IsConsistent (S C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) (D : Set V) : Prop :=
  Dense D ∧ ∀ u₀ ∈ D, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, Δt < δ →
    ∀ t ∈ Icc (0 : ℝ) T, t + Δt ≤ T → ‖(Δt)⁻¹ • (C Δt (S t u₀) - S (t + Δt) u₀)‖ ≤ ε

/-- For $\Delta t > 0$, $\|x / \Delta t\| \le \varepsilon$ if and only if
$\|x\| \le \varepsilon \Delta t$. -/
private theorem norm_inv_smul_le_iff {x : V} {Δt ε : ℝ} (hΔt : 0 < Δt) :
    ‖(Δt)⁻¹ • x‖ ≤ ε ↔ ‖x‖ ≤ ε * Δt := by
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hΔt, ← div_eq_inv_mul, div_le_iff₀ hΔt]

/-- Consistency in the sense of Definition 6.2.7 is equivalent to consistency in the sense of the
backbone, `FiniteDifference.IsConsistent`, where the division by $\Delta t$ is cleared. -/
theorem isConsistent_iff (S C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) (D : Set V) :
    IsConsistent S C T Δ₀ D ↔ FiniteDifference.IsConsistent S C T Δ₀ D := by
  constructor
  · rintro ⟨hD, h⟩
    refine ⟨hD, fun u₀ hu₀ ε hε => ?_⟩
    obtain ⟨δ, hδ, hb⟩ := h u₀ hu₀ ε hε
    exact ⟨δ, hδ, fun Δt hΔt hlt t ht htΔ =>
      (norm_inv_smul_le_iff hΔt.1).1 (hb Δt hΔt hlt t ht htΔ)⟩
  · rintro ⟨hD, h⟩
    refine ⟨hD, fun u₀ hu₀ ε hε => ?_⟩
    obtain ⟨δ, hδ, hb⟩ := h u₀ hu₀ ε hε
    exact ⟨δ, hδ, fun Δt hΔt hlt t ht htΔ =>
      (norm_inv_smul_le_iff hΔt.1).2 (hb Δt hΔt hlt t ht htΔ)⟩

/-- **Definition 6.2.9** of [han2009theoretical]. The difference method $\{C(\Delta t)\}$ is
**convergent** to the family $S$ on $[0, T]$, for step sizes in $(0, \Delta_0]$, if for every
$t \in [0, T]$, every $u_0 \in V$, and all sequences $\Delta t_i \in (0, \Delta_0]$ and
$m_i \in \mathbb{N}$ with $m_i \Delta t_i \le T$, $\Delta t_i \to 0$ and $m_i \Delta t_i \to t$,
$$\|(C(\Delta t_i)^{m_i} - S(t)) u_0\| \to 0.$$

**Reading.** The source does not say how the limit is taken. Here it is taken along every pair
of sequences whose discrete time tends to $t$. The step counts are restricted to
$m_i \Delta t_i \le T$, because outside $[0, T]$ nothing is known about the family $S$. -/
def IsConvergent (S C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ∀ u₀ : V, ∀ (Δt : ℕ → ℝ) (m : ℕ → ℕ), (∀ i, Δt i ∈ Ioc (0 : ℝ) Δ₀) →
    (∀ i, (m i : ℝ) * Δt i ≤ T) → Tendsto Δt atTop (𝓝 0) →
    Tendsto (fun i => (m i : ℝ) * Δt i) atTop (𝓝 t) →
    Tendsto (fun i => ‖(C (Δt i) ^ m i - S t) u₀‖) atTop (𝓝 0)

/-- Convergence in the sense of Definition 6.2.9 is equivalent to convergence in the sense of the
backbone, `FiniteDifference.IsConvergent`. -/
theorem isConvergent_iff (S C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) :
    IsConvergent S C T Δ₀ ↔ FiniteDifference.IsConvergent S C T Δ₀ := by
  simp only [IsConvergent, FiniteDifference.IsConvergent, sub_apply]

/-- **Definition 6.2.10** of [han2009theoretical]. The difference method $\{C(\Delta t)\}$ is
**stable** on $[0, T]$, for step sizes in $(0, \Delta_0]$, if there is $M_0$ with
$\|C(\Delta t)^m\| \le M_0$ for all $\Delta t \in (0, \Delta_0]$ and all $m \in \mathbb{N}$ with
$m \Delta t \le T$. -/
def IsStable (C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) : Prop :=
  ∃ M₀ : ℝ, ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ∀ m : ℕ, (m : ℝ) * Δt ≤ T → ‖C Δt ^ m‖ ≤ M₀

/-- Stability in the sense of Definition 6.2.10 is, by definition, stability in the sense of the
backbone, `FiniteDifference.IsStable`. -/
theorem isStable_iff (C : ℝ → V →L[ℝ] V) (T Δ₀ : ℝ) :
    IsStable C T Δ₀ ↔ FiniteDifference.IsStable C T Δ₀ := Iff.rfl

/-! ### The equivalence theorem -/

section Equivalence

variable [CompleteSpace V] (L : V →ₗ.[ℝ] V) (hdense : Dense (L.domain : Set V)) {T c₀ : ℝ}
  (hT : 0 ≤ T) (hc₀ : 0 ≤ c₀) (hwp : IsWellPosed L T c₀)

/-- **Theorem 6.2.11** of [han2009theoretical] (Lax equivalence theorem). Let $V$ be a Banach space,
let $L : V_0 \subseteq V \to V$ have a dense domain, let $T \ge 0$ and $c_0 \ge 0$, let the
problem be well posed on $[0, T]$ with constant $c_0$, and let $S$ be its solution operators.
Let $\{C(\Delta t)\}$ be a family of bounded operators with $\|C(\Delta t)\| \le c_1$ for all
$\Delta t \in (0, \Delta_0]$, consistent with $S$ on a set $V_c$. Then the method is stable if
and only if it is convergent.

**Reading.** The source assumes the uniform bound $\|C(\Delta t)\| \le c_1$ explicitly when it
introduces the family a page before the theorem. Its proof of the implication from convergence
to stability uses the bound: without it, the estimate $\sup_k \|C(\Delta t_k)^{m_k}\| \le \sup_k
\|C(\Delta t_k)\|^{m_k} < \infty$ for step sizes bounded away from zero fails.

The proof specializes `FiniteDifference.isStable_iff_isConvergent`. It does not use the
semigroup property of Proposition 6.2.6. -/
theorem theorem_6_2_11 {C : ℝ → V →L[ℝ] V} {Δ₀ c₁ : ℝ} {D : Set V}
    (hC : ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ‖C Δt‖ ≤ c₁)
    (hcons : IsConsistent (solutionOperator L hdense hT hc₀ hwp) C T Δ₀ D) :
    IsStable C T Δ₀ ↔ IsConvergent (solutionOperator L hdense hT hc₀ hwp) C T Δ₀ := by
  rw [isStable_iff, isConvergent_iff]
  exact FiniteDifference.isStable_iff_isConvergent hT (solutionOperator_zero L hdense hT hc₀ hwp)
    (proposition_6_2_5 L hdense hT hc₀ hwp) hC ((isConsistent_iff _ _ _ _ _).1 hcons)

/-- **Corollary 6.2.12** of [han2009theoretical]. Under the hypotheses of Definition 6.2.3, let $S$
be the solution operators, let $u_0 \in V$, $\Delta t > 0$, $m, k \in \mathbb{N}$, and
$t = m \Delta t \in [0, T]$. Assume that $\|C(\Delta t)^i\| \le M_0$ for all $i \le m$, and that
$$\|C(\Delta t) S(s) u_0 - S(s + \Delta t) u_0\| \le c \, \Delta t^{k+1} \qquad \text{for all }
  s \in [0, T].$$
Then
$$\|C(\Delta t)^m u_0 - S(t) u_0\| \le M_0 \, t \, c \, \Delta t^k.$$

The statement is for one fixed step size, with explicit constants and no limit. For
$u_0 \in V_0$, $S(t) u_0$ is the exact solution $u(t)$, by
`AtkinsonHan.Chapter06.solutionOperator_apply`. The local error hypothesis is asked for every
$s \in [0, T]$, so also at $s$ with $s + \Delta t > T$. The proof specializes
`FiniteDifference.norm_iterate_sub_le`.

**Reading.** Requires an explicit power bound and includes the missing time and stability factors in
global error.
-/
theorem corollary_6_2_12 {C : ℝ → V →L[ℝ] V} {Δt c M₀ t : ℝ} {k m : ℕ} (u₀ : V) (hΔt : 0 < Δt)
    (hmΔt : (m : ℝ) * Δt = t) (ht : t ∈ Icc (0 : ℝ) T)
    (hstab : ∀ i ≤ m, ‖C Δt ^ i‖ ≤ M₀)
    (hloc : ∀ s ∈ Icc (0 : ℝ) T,
      ‖C Δt (solutionOperator L hdense hT hc₀ hwp s u₀)
        - solutionOperator L hdense hT hc₀ hwp (s + Δt) u₀‖ ≤ c * Δt ^ (k + 1)) :
    ‖(C Δt ^ m) u₀ - solutionOperator L hdense hT hc₀ hwp t u₀‖ ≤ M₀ * t * c * Δt ^ k :=
  FiniteDifference.norm_iterate_sub_le u₀ (solutionOperator_zero L hdense hT hc₀ hwp) hΔt hmΔt
    hstab fun s hs => hloc s ⟨hs.1, hs.2.trans ht.2⟩

end Equivalence

/-! ### Example 6.2.4: the heat equation on $(0, \pi)$ in $C_0[0, \pi]$ -/

section HeatExample

open Submodule InnerProductSpace Laplacian
open scoped Real

/-- **Example 6.2.4** of [han2009theoretical], the space $V$. The space $V = C_0[0, \pi]$ is the
subspace of the continuous functions $v$ on $[0, \pi]$ with $v(0) = v(\pi) = 0$. It is a closed
subspace of $C[0, \pi]$ with the maximum norm, hence a Banach space. -/
def C₀ : Submodule ℝ C(Icc (0 : ℝ) π, ℝ) where
  carrier := {v | v ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0 ∧
    v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0}
  add_mem' ha hb := ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c v hv := ⟨by simp [hv.1], by simp [hv.2]⟩

/-- A function $v \in C[0, \pi]$ lies in $C_0[0, \pi]$ if and only if $v(0) = 0$ and $v(\pi) = 0$.
-/
theorem mem_C₀_iff {v : C(Icc (0 : ℝ) π, ℝ)} :
    v ∈ C₀ ↔ v ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0 ∧
      v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0 :=
  Iff.rfl

/-- The subspace $C_0[0, \pi]$ is closed in $C[0, \pi]$. -/
theorem isClosed_C₀ : IsClosed (C₀ : Set C(Icc (0 : ℝ) π, ℝ)) :=
  (isClosed_eq (continuous_eval_const _) continuous_const).inter
    (isClosed_eq (continuous_eval_const _) continuous_const)

/-- The space $C_0[0, \pi]$ is complete, because it is closed in the Banach space $C[0, \pi]$. -/
instance : CompleteSpace C₀ := isClosed_C₀.completeSpace_coe

/-- Every sine polynomial $\sum_{j < n} c_j \sin((j + 1) x)$ lies in $C_0[0, \pi]$. -/
theorem sinePolynomial_mem_C₀ (n : ℕ) (c : ℕ → ℝ) : sinePolynomial n c ∈ C₀ :=
  ⟨sinePolynomial_zero_apply n c, sinePolynomial_pi_apply n c⟩

/-- For $k \in \mathbb{N}$, the function $x \mapsto \sin((k + 1) x)$ as an element of $C_0[0, \pi]$.
This is the basis of the subspace $V_0$ in Example 6.2.4. -/
noncomputable def sinV (k : ℕ) : C₀ :=
  ⟨sinMap k, by
    refine ⟨by simp [sinMap_apply], ?_⟩
    rw [sinMap_apply]
    exact_mod_cast Real.sin_nat_mul_pi (k + 1)⟩

/-- As a function in $C[0, \pi]$, `AtkinsonHan.Chapter06.sinV k` is the sine `sinMap k`,
$x \mapsto \sin((k + 1) x)$. -/
@[simp]
theorem coe_sinV (k : ℕ) : (sinV k : C(Icc (0 : ℝ) π, ℝ)) = sinMap k := rfl

/-- **Example 6.2.4** of [han2009theoretical], the subspace $V_0$ of (6.2.5). The subspace
$V_0 \subseteq C_0[0, \pi]$ is the linear span of the functions $\sin(jx)$, $j \ge 1$: its
elements are the finite sine polynomials $\sum_{j=1}^n a_j \sin(jx)$. -/
noncomputable def sinePolynomials : Submodule ℝ C₀ := span ℝ (range sinV)

/-- For $n \in \mathbb{N}$ and $c : \mathbb{N} \to \mathbb{R}$, the sine polynomial
$\sum_{j < n} c_j \sin((j + 1) x)$ as an element of $C_0[0, \pi]$. It describes the elements of
$V_0$ in Example 6.2.4.

The index starts at $0$, so the coefficient $c_j$ belongs to $\sin((j + 1) x)$. -/
noncomputable def sinePolyV (n : ℕ) (c : ℕ → ℝ) : C₀ := ∑ j ∈ Finset.range n, c j • sinV j

/-- As a function in $C[0, \pi]$, `AtkinsonHan.Chapter06.sinePolyV n c` is the sine polynomial
`sinePolynomial n c`. -/
@[simp]
theorem coe_sinePolyV (n : ℕ) (c : ℕ → ℝ) :
    (sinePolyV n c : C(Icc (0 : ℝ) π, ℝ)) = sinePolynomial n c := by
  simp [sinePolyV, sinePolynomial]

/-- Every sine polynomial $\sum_{j < n} c_j \sin((j + 1) x)$ lies in $V_0$. -/
theorem sinePolyV_mem (n : ℕ) (c : ℕ → ℝ) : sinePolyV n c ∈ sinePolynomials :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (subset_span ⟨j, rfl⟩)

/-- The image of $V_0$ under the inclusion $C_0[0, \pi] \subseteq C[0, \pi]$ is the span of the
functions $\sin((k + 1) x)$, $k \in \mathbb{N}$, in $C[0, \pi]$. -/
theorem sinePolynomials_map_subtype :
    sinePolynomials.map C₀.subtype = span ℝ (range sinMap) := by
  rw [sinePolynomials, Submodule.map_span, ← Set.range_comp]
  rfl

/-- An element $v \in C_0[0, \pi]$ lies in $V_0$ of Example 6.2.4 if and only if
$v = \sum_{j < n} c_j \sin((j + 1) x)$ for some $n \in \mathbb{N}$ and some coefficients
$c : \mathbb{N} \to \mathbb{R}$. -/
theorem mem_sinePolynomials_iff {v : C₀} :
    v ∈ sinePolynomials ↔ ∃ (n : ℕ) (c : ℕ → ℝ), v = sinePolyV n c := by
  constructor
  · intro hv
    have h : (v : C(Icc (0 : ℝ) π, ℝ)) ∈ span ℝ (range sinMap) := by
      rw [← sinePolynomials_map_subtype]
      exact Submodule.mem_map_of_mem hv
    obtain ⟨n, c, hc⟩ := mem_span_sinMap_iff.1 h
    exact ⟨n, c, Subtype.ext (by rw [coe_sinePolyV, hc])⟩
  · rintro ⟨n, c, rfl⟩
    exact sinePolyV_mem n c

/-- The functions $\sin((k + 1) x)$, $k \in \mathbb{N}$, are linearly independent in $C_0[0, \pi]$.
-/
theorem linearIndependent_sinV : LinearIndependent ℝ sinV :=
  LinearIndependent.of_comp C₀.subtype linearIndependent_sinMap

/-- The linear map $V_0 \to C_0[0, \pi]$ with $\sin((k + 1) x) \mapsto -\nu (k + 1)^2 \sin((k + 1)
x)$ on the basis of $V_0$. It is the underlying map of `AtkinsonHan.Chapter06.heatOperator`. -/
noncomputable def heatOperatorAux (ν : ℝ) : sinePolynomials →ₗ[ℝ] C₀ :=
  (Module.Basis.span linearIndependent_sinV).constr ℝ fun k => (-ν * ((k : ℝ) + 1) ^ 2) • sinV k

/-- **Example 6.2.4** of [han2009theoretical], the operator $L$. For $\nu \in \mathbb{R}$, the
operator $L = \nu \, \partial^2 / \partial x^2$ with domain $V_0$ is the linear operator
$L : V_0 \subseteq C_0[0, \pi] \to C_0[0, \pi]$ with
$$L \sin(jx) = -\nu j^2 \sin(jx), \qquad j \ge 1.$$

The operator is defined by its action on the basis of $V_0$.
`AtkinsonHan.Chapter06.heatOperator_apply_eq_laplacian` shows that on every element of $V_0$ it
is $\nu$ times the second derivative. The domain is $V_0$ and not all of $C^2 \cap C_0$, because
well-posedness (Definition 6.2.2) asks for a solution from every initial value in the domain,
and the source gives one only for sine polynomials, by the formula (6.2.7). The operator is a
`LinearPMap`, `C₀ →ₗ.[ℝ] C₀`. -/
noncomputable def heatOperator (ν : ℝ) : C₀ →ₗ.[ℝ] C₀ := ⟨sinePolynomials, heatOperatorAux ν⟩

variable {ν : ℝ}

/-- The domain of the operator $L$ of Example 6.2.4 is $V_0$. -/
@[simp]
theorem heatOperator_domain : (heatOperator ν).domain = sinePolynomials := rfl

/-- The operator $L$ of Example 6.2.4 acts on $V_0$ as its underlying linear map
`AtkinsonHan.Chapter06.heatOperatorAux`. -/
theorem heatOperator_apply (x : sinePolynomials) : heatOperator ν x = heatOperatorAux ν x := rfl

/-- The underlying linear map of $L$ sends $\sin((k + 1) x)$ to $-\nu (k + 1)^2 \sin((k + 1) x)$. -/
theorem heatOperatorAux_sinV (k : ℕ) (hk : sinV k ∈ sinePolynomials) :
    heatOperatorAux ν ⟨sinV k, hk⟩ = (-ν * ((k : ℝ) + 1) ^ 2) • sinV k := by
  have h : (⟨sinV k, hk⟩ : sinePolynomials) = Module.Basis.span linearIndependent_sinV k :=
    Subtype.ext (by rw [Module.Basis.span_apply])
  rw [heatOperatorAux, h]
  exact Module.Basis.constr_basis (Module.Basis.span linearIndependent_sinV) ℝ
    (fun k => (-ν * ((k : ℝ) + 1) ^ 2) • sinV k) k

/-- The underlying linear map of $L$ sends $\sum_{j < n} c_j \sin((j + 1) x)$ to $\sum_{j < n} c_j
(-\nu (j + 1)^2) \sin((j + 1) x)$. -/
theorem heatOperatorAux_sinePolyV (n : ℕ) (c : ℕ → ℝ) (h : sinePolyV n c ∈ sinePolynomials) :
    heatOperatorAux ν ⟨sinePolyV n c, h⟩
      = sinePolyV n fun j => c j * (-ν * ((j : ℝ) + 1) ^ 2) := by
  have hmem : ∀ j, sinV j ∈ sinePolynomials := fun j => subset_span ⟨j, rfl⟩
  have e : (⟨sinePolyV n c, h⟩ : sinePolynomials)
      = ∑ j ∈ Finset.range n, c j • (⟨sinV j, hmem j⟩ : sinePolynomials) :=
    Subtype.ext (by simp only [sinePolyV, Submodule.coe_sum, Submodule.coe_smul])
  rw [e, map_sum]
  simp only [map_smul, heatOperatorAux_sinV, sinePolyV, smul_smul]

/-- For the operator $L$ of Example 6.2.4 and every sine polynomial,
$$L \sum_{j < n} c_j \sin((j + 1) x) = \sum_{j < n} c_j \bigl(-\nu (j + 1)^2\bigr) \sin((j + 1)
  x).$$
-/
theorem heatOperator_sinePolyV (n : ℕ) (c : ℕ → ℝ) (h : sinePolyV n c ∈ sinePolynomials) :
    heatOperator ν ⟨sinePolyV n c, h⟩ = sinePolyV n fun j => c j * (-ν * ((j : ℝ) + 1) ^ 2) :=
  heatOperatorAux_sinePolyV n c h

/-- The value of the sine polynomial $\sum_{j < n} c_j \sin((j + 1) x)$ of $C_0[0, \pi]$ at a point
$x \in [0, \pi]$ is $\sum_{j < n} c_j \sin((j + 1) x)$. -/
theorem sinePolyV_apply (n : ℕ) (c : ℕ → ℝ) (x : Icc (0 : ℝ) π) :
    (sinePolyV n c : C(Icc (0 : ℝ) π, ℝ)) x
      = ∑ j ∈ Finset.range n, c j * Real.sin (((j : ℝ) + 1) * (x : ℝ)) := by
  rw [coe_sinePolyV, sinePolynomial_apply]

/-- For a sine polynomial $v = \sum_{j < n} c_j \sin((j + 1) x)$ and every $x \in [0, \pi]$, the
underlying linear map of $L$ satisfies $(Lv)(x) = \nu v''(x)$, where $v''$ is the second
derivative of $v$ read as a function on $\mathbb{R}$.

The second derivative is Mathlib's Laplacian `Δ` on $\mathbb{R}$. -/
theorem heatOperatorAux_apply_eq_laplacian (n : ℕ) (c : ℕ → ℝ)
    (h : sinePolyV n c ∈ sinePolynomials) (x : Icc (0 : ℝ) π) :
    (heatOperatorAux ν ⟨sinePolyV n c, h⟩ : C(Icc (0 : ℝ) π, ℝ)) x
      = ν * Δ (fun y : ℝ => ∑ j ∈ Finset.range n, c j * Real.sin (((j : ℝ) + 1) * y)) (x : ℝ) := by
  rw [heatOperatorAux_sinePolyV, sinePolyV_apply, ← Heat.sineSeries_zero_nu_eq n c 0,
    Heat.laplacian_sineSeries_fst, Heat.sineSeriesDerivX_two, mul_neg, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [neg_zero, zero_mul, Real.exp_zero]
  ring

/-- For the operator $L$ of Example 6.2.4, a sine polynomial $v = \sum_{j < n} c_j \sin((j + 1) x)$
and every $x \in [0, \pi]$,
$$(Lv)(x) = \nu \, v''(x),$$
where $v''$ is the second derivative of $v$ read as a function on $\mathbb{R}$. So $L$ is
$\nu \, \partial^2 / \partial x^2$ on $V_0$.

The second derivative is Mathlib's Laplacian `Δ` on $\mathbb{R}$. -/
theorem heatOperator_apply_eq_laplacian (n : ℕ) (c : ℕ → ℝ)
    (h : sinePolyV n c ∈ sinePolynomials) (x : Icc (0 : ℝ) π) :
    (heatOperator ν ⟨sinePolyV n c, h⟩ : C(Icc (0 : ℝ) π, ℝ)) x
      = ν * Δ (fun y : ℝ => ∑ j ∈ Finset.range n, c j * Real.sin (((j : ℝ) + 1) * y)) (x : ℝ) :=
  heatOperatorAux_apply_eq_laplacian n c h x

/-! ### The solution (6.2.7) -/

/-- **Equation (6.2.7)** of [han2009theoretical]. For the initial value
$u_0 = \sum_{j < n} b_j \sin((j + 1) x)$, the curve $u : \mathbb{R} \to C_0[0, \pi]$ with
$$u(t) = \sum_{j < n} b_j \, e^{-\nu (j + 1)^2 t} \sin((j + 1) x).$$
-/
noncomputable def sineSolution (ν : ℝ) (n : ℕ) (b : ℕ → ℝ) (t : ℝ) : C₀ :=
  sinePolyV n fun j => b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * t)

/-- At $t = 0$ the solution (6.2.7) is its initial value $\sum_{j < n} b_j \sin((j + 1) x)$. -/
theorem sineSolution_zero (n : ℕ) (b : ℕ → ℝ) : sineSolution ν n b 0 = sinePolyV n b := by
  simp [sineSolution]

/-- The value of the solution (6.2.7) at time $t$ and at $x \in [0, \pi]$ is the finite sine series
`Heat.sineSeries ν n b (x, t)`. -/
theorem sineSolution_apply (n : ℕ) (b : ℕ → ℝ) (t : ℝ) (x : Icc (0 : ℝ) π) :
    (sineSolution ν n b t : C(Icc (0 : ℝ) π, ℝ)) x = Heat.sineSeries ν n b ((x : ℝ), t) := by
  rw [sineSolution, sinePolyV_apply, Heat.sineSeries]

/-- For every $t$, the solution (6.2.7) at time $t$ lies in $V_0$. -/
theorem sineSolution_mem (n : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    sineSolution ν n b t ∈ sinePolynomials := sinePolyV_mem _ _

/-- The curve (6.2.7) is differentiable on $\mathbb{R}$ in $C_0[0, \pi]$, with derivative
$u'(t) = L u(t)$. -/
theorem hasDerivAt_sineSolution (n : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (sineSolution ν n b) (heatOperator ν ⟨sineSolution ν n b t, sineSolution_mem n b t⟩)
      t := by
  rw [show heatOperator ν ⟨sineSolution ν n b t, sineSolution_mem n b t⟩
      = sinePolyV n fun j => b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * t) * (-ν * ((j : ℝ) + 1) ^ 2)
    from heatOperator_sinePolyV _ _ _]
  unfold sineSolution sinePolyV
  refine HasDerivAt.fun_sum (A := fun j s => (b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * s)) • sinV j)
    fun j _ => ?_
  have h1 : HasDerivAt (fun s : ℝ => -ν * ((j : ℝ) + 1) ^ 2 * s) (-ν * ((j : ℝ) + 1) ^ 2) t :=
    (hasDerivAt_id t).const_mul (-ν * ((j : ℝ) + 1) ^ 2) |>.congr_deriv (mul_one _)
  have h2 := (((Real.hasDerivAt_exp _).comp t h1).const_mul (b j)).smul_const (sinV j)
  refine h2.congr_deriv ?_
  simp only
  ring_nf

/-- **Example 6.2.4** of [han2009theoretical], the solution (6.2.7). For every $\nu \in \mathbb{R}$,
$T \in \mathbb{R}$ and initial value $u_0 = \sum_{j < n} b_j \sin((j + 1) x) \in V_0$, the curve
(6.2.7) is a solution of $u' = Lu$, $u(0) = u_0$ on $[0, T]$ in the sense of Definition 6.2.1. -/
theorem isSolution_sineSolution (T : ℝ) (n : ℕ) (b : ℕ → ℝ) :
    IsSolution (heatOperator ν) T (sinePolyV n b) (sineSolution ν n b) := by
  rw [isSolution_iff]
  exact ⟨sineSolution_zero n b, fun t _ =>
    ⟨sineSolution_mem n b t, (hasDerivAt_sineSolution n b t).hasDerivWithinAt⟩⟩

/-! ### The maximum principle and well-posedness -/

/-- A curve $u$ in $C_0[0, \pi]$ read as a function of $(x, t)$: $U(x, t) = u(t)(x)$, with $x$
clamped to $[0, \pi]$. -/
private noncomputable def spaceTime (u : ℝ → C₀) (p : ℝ × ℝ) : ℝ :=
  (u p.2 : C(Icc (0 : ℝ) π, ℝ)) (projIcc 0 π Real.pi_pos.le p.1)

/-- Evaluation at a point of $[0, \pi]$, as a bounded linear functional on $C_0[0, \pi]$. -/
private noncomputable def evalC₀ (x : Icc (0 : ℝ) π) : C₀ →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ x).comp C₀.subtypeL

private theorem evalC₀_apply (x : Icc (0 : ℝ) π) (v : C₀) :
    evalC₀ x v = (v : C(Icc (0 : ℝ) π, ℝ)) x := rfl

/-- A solution of $u' = Lu$ on $[0, T]$ in the sense of the backbone, for the operator $L$ of
Example 6.2.4, is a classical solution of the heat equation on $(0, \pi) \times (0, T)$ in the
sense of `Heat.IsClassicalSolution`. -/
private theorem isClassicalSolution_of_isSolution {T : ℝ} {u₀ : C₀} {u : ℝ → C₀}
    (hu : FiniteDifference.IsSolution (heatOperator ν) T u₀ u) :
    Heat.IsClassicalSolution ν (Ioo 0 π) T (spaceTime u) := by
  have hcl : closure (Ioo (0 : ℝ) π) = Icc 0 π := closure_Ioo Real.pi_pos.ne
  -- the representation of `u t` as a sine polynomial, at every time
  have hrep : ∀ t ∈ Icc (0 : ℝ) T, ∃ (n : ℕ) (c : ℕ → ℝ), u t = sinePolyV n c :=
    fun t ht => mem_sinePolynomials_iff.1 (hu.2 t ht).1
  -- the derivative of `u` at an interior time
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) T, ∃ h : u t ∈ sinePolynomials,
      HasDerivAt u (heatOperator ν ⟨u t, h⟩) t := fun t ht => by
    obtain ⟨h, hd⟩ := hu.2 t (Ioo_subset_Icc_self ht)
    exact ⟨h, hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩
  refine ⟨?_, fun x _ t ht => ?_, fun x hx t _ => ?_, fun x hx t ht => ?_⟩
  · -- continuity on the closed cylinder
    have hcont : ContinuousOn u (Icc 0 T) := fun t ht =>
      (hu.2 t ht).2.continuousWithinAt
    have h1 : ContinuousOn (fun p : ℝ × ℝ => ((u p.2 : C(Icc (0 : ℝ) π, ℝ)),
        projIcc 0 π Real.pi_pos.le p.1)) (closure (Ioo 0 π) ×ˢ Icc 0 T) := by
      refine ContinuousOn.prodMk ?_ (continuous_projIcc.comp continuous_fst).continuousOn
      exact continuous_subtype_val.comp_continuousOn
        (hcont.comp continuous_snd.continuousOn fun p hp => hp.2)
    exact continuous_eval.comp_continuousOn h1
  · -- differentiability in `t`
    obtain ⟨h, hd⟩ := hderiv t ht
    exact ((evalC₀ (projIcc 0 π Real.pi_pos.le x)).hasFDerivAt.comp_hasDerivAt t
      hd).differentiableAt
  · -- `C²` in `x`: near `x ∈ (0, π)`, the slice is a sine polynomial
    obtain ⟨n, c, hc⟩ := hrep t (Ioo_subset_Icc_self ‹_›)
    have heq : (fun y => spaceTime u (y, t))
        =ᶠ[𝓝 x] fun y => Heat.sineSeries 0 n c (y, 0) := by
      filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
      simp only [spaceTime, hc, coe_sinePolyV, projIcc_of_mem _ hy, sinePolynomial_apply]
      exact (congrFun (Heat.sineSeries_zero_nu_eq n c 0) y).symm
    exact ((Heat.contDiff_sineSeries_fst (ν := 0) (n := n) (b := c) 0).contDiffAt
      ).congr_of_eventuallyEq heq
  · -- the equation
    obtain ⟨h, hd⟩ := hderiv t ht
    obtain ⟨n, c, hc⟩ := hrep t (Ioo_subset_Icc_self ht)
    have hdx : HasDerivAt (fun s => spaceTime u (x, s))
        (evalC₀ (projIcc 0 π Real.pi_pos.le x) (heatOperator ν ⟨u t, h⟩)) t :=
      (evalC₀ (projIcc 0 π Real.pi_pos.le x)).hasFDerivAt.comp_hasDerivAt t hd
    rw [hdx.deriv]
    have hval : evalC₀ (projIcc 0 π Real.pi_pos.le x) (heatOperator ν ⟨u t, h⟩)
        = ν * Δ (fun y : ℝ => ∑ j ∈ Finset.range n, c j * Real.sin (((j : ℝ) + 1) * y)) x := by
      have e : (⟨u t, h⟩ : sinePolynomials) = ⟨sinePolyV n c, hc ▸ h⟩ := Subtype.ext hc
      refine (congrArg (fun z : sinePolynomials =>
        evalC₀ (projIcc 0 π Real.pi_pos.le x) (heatOperatorAux ν z)) e).trans ?_
      rw [evalC₀_apply, heatOperatorAux_apply_eq_laplacian,
        projIcc_of_mem _ (Ioo_subset_Icc_self hx)]
    rw [hval]
    congr 1
    refine Filter.EventuallyEq.eq_of_nhds (laplacian_congr_nhds ?_)
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
    simp only [spaceTime, hc, coe_sinePolyV, projIcc_of_mem _ hy, sinePolynomial_apply]

/-- **The maximum principle** for the problem of Example 6.2.4. Let $\nu > 0$. Every solution $u$ of
$u' = Lu$, $u(0) = u_0$ on $[0, T]$ in the sense of Definition 6.2.1 satisfies
$$\|u(t)\| \le \|u_0\|, \quad \text{that is,} \quad \max_x |u(x, t)| \le \max_x |u_0(x)|, \qquad
  t \in [0, T].$$

The solution is a classical solution of the heat equation, and the proof applies
`Heat.IsClassicalSolution.abs_le_of_eq_zero_frontier`, the parabolic maximum principle of
Theorem 10.6 of [brezis2011functional]. -/
theorem norm_le_of_isSolution (hν : 0 < ν) {T : ℝ} {u₀ : C₀} {u : ℝ → C₀}
    (hu : IsSolution (heatOperator ν) T u₀ u) : ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ ‖u₀‖ := by
  rw [isSolution_iff] at hu
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | htpos
  · rw [hu.1]
  have hT : 0 < T := htpos.trans_le ht.2
  have hcl : closure (Ioo (0 : ℝ) π) = Icc 0 π := closure_Ioo Real.pi_pos.ne
  have hfr : frontier (Ioo (0 : ℝ) π) = {0, π} := frontier_Ioo Real.pi_pos
  have hbound := (isClassicalSolution_of_isSolution hu).abs_le_of_eq_zero_frontier isOpen_Ioo
    (Metric.isBounded_Ioo 0 π) hν hT (M := ‖u₀‖) ?_ ?_
  · rw [← Submodule.norm_coe]
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
    have := hbound x (by rw [hcl]; exact x.2) t ht
    rw [spaceTime, projIcc_val] at this
    rw [Real.norm_eq_abs]
    exact this
  · intro x hx s _
    rw [hfr] at hx
    rcases hx with rfl | rfl
    · change (u s : C(Icc (0 : ℝ) π, ℝ)) (projIcc 0 π Real.pi_pos.le 0) = 0
      rw [projIcc_left]
      exact (u s).2.1
    · change (u s : C(Icc (0 : ℝ) π, ℝ)) (projIcc 0 π Real.pi_pos.le π) = 0
      rw [projIcc_right]
      exact (u s).2.2
  · intro y hy
    rw [spaceTime, hu.1, ← Real.norm_eq_abs, ← Submodule.norm_coe]
    exact ContinuousMap.norm_coe_le_norm _ _

/-- **Example 6.2.4** of [han2009theoretical], well-posedness. Let $\nu > 0$ and $T \in \mathbb{R}$.
The heat equation problem $u' = Lu$ in $V = C_0[0, \pi]$, with
$L = \nu \, \partial^2 / \partial x^2$ on the sine polynomials $V_0$ of (6.2.5), is well posed
on $[0, T]$ in the sense of Definition 6.2.2, with stability constant $c_0 = 1$.

Existence is the explicit solution (6.2.7), `AtkinsonHan.Chapter06.isSolution_sineSolution`.
Uniqueness and the bound $\|u(t) - \bar u(t)\| \le \|u_0 - \bar u_0\|$ are the maximum principle
`AtkinsonHan.Chapter06.norm_le_of_isSolution`, applied to the difference of two solutions. -/
theorem example_6_2_4 (hν : 0 < ν) (T : ℝ) : IsWellPosed (heatOperator ν) T 1 := by
  rw [isWellPosed_iff]
  refine ⟨fun u₀ hu₀ => ?_, fun u₀ ū₀ u ū hu hū t ht => ?_⟩
  · obtain ⟨n, c, rfl⟩ := mem_sinePolynomials_iff.1 hu₀
    exact ⟨sineSolution ν n c, (isSolution_iff _ _ _ _).1 (isSolution_sineSolution T n c)⟩
  · have h := norm_le_of_isSolution hν ((isSolution_iff _ _ _ _).2 (hu.sub hū)) t ht
    rwa [one_mul]

/-- **Example 6.2.4** of [han2009theoretical], density of $V_0$, which is **Exercise 6.2.1**. The
sine polynomials are dense in $C_0[0, \pi]$ with the maximum norm.

The proof approximates the odd $2\pi$-periodic extension uniformly by trigonometric polynomials,
`exists_mem_span_sinMap_norm_sub_lt`. -/
theorem example_6_2_4_dense : Dense (sinePolynomials : Set C₀) := by
  refine Metric.dense_iff.2 fun v ε hε => ?_
  obtain ⟨p, hp, hvp⟩ := exists_mem_span_sinMap_norm_sub_lt v.2.1 v.2.2 hε
  obtain ⟨n, c, rfl⟩ := mem_span_sinMap_iff.1 hp
  refine ⟨sinePolyV n c, ?_, sinePolyV_mem n c⟩
  rw [Metric.mem_ball, dist_eq_norm, ← Submodule.norm_coe, Submodule.coe_sub, coe_sinePolyV,
    norm_sub_rev]
  exact hvp

/-- For every $\nu$, the domain $V_0$ of the operator $L$ of Example 6.2.4 is dense in
$C_0[0, \pi]$. -/
theorem dense_heatOperator_domain : Dense ((heatOperator ν).domain : Set C₀) :=
  example_6_2_4_dense

/-- **Example 6.2.4** of [han2009theoretical], the solution operators. Let $\nu > 0$ and $T \ge 0$.
The solution operators $S(t)$ of Definition 6.2.3 for the heat equation satisfy $\|S(t)\| \le 1$
for every $t \in [0, T]$. This is the bound $\max_x |u(x, t)| \le \max_x |u_0(x)|$, extended to
all initial values in $C_0[0, \pi]$. -/
theorem example_6_2_4_norm_solutionOperator_le (hν : 0 < ν) {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖solutionOperator (heatOperator ν) dense_heatOperator_domain hT zero_le_one
      (example_6_2_4 hν T) t‖ ≤ 1 :=
  norm_solutionOperator_le _ _ _ _ _

/-- **Example 6.2.4** of [han2009theoretical], the solution (6.2.7) through the solution operators.
Let $\nu > 0$, $T \ge 0$ and $t \in [0, T]$. For the initial value
$u_0 = \sum_{j < n} b_j \sin((j + 1) x)$, the solution operator gives $S(t) u_0 = \sum_{j < n}
b_j e^{-\nu (j + 1)^2 t} \sin((j + 1) x)$. -/
theorem example_6_2_4_solutionOperator_apply (hν : 0 < ν) {T : ℝ} (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (n : ℕ) (b : ℕ → ℝ) :
    solutionOperator (heatOperator ν) dense_heatOperator_domain hT zero_le_one
      (example_6_2_4 hν T) t (sinePolyV n b) = sineSolution ν n b t :=
  solutionOperator_apply _ _ _ _ _ ht (sinePolyV_mem n b) _ (isSolution_sineSolution T n b)

/-! ### Examples 6.2.8 and 6.2.13: the forward and backward schemes on $C_0[0, \pi]$ -/

section Schemes

/-- The odd $2\pi$-periodic extension $\tilde v : \mathbb{R} \to \mathbb{R}$ of $v \in C_0[0, \pi]$,
used in Example 6.2.8. -/
noncomputable abbrev ext (v : C₀) : ℝ → ℝ := oddPeriodicExtend (v : C(Icc (0 : ℝ) π, ℝ))

/-- The extension $\tilde v$ is continuous. -/
theorem continuous_ext (v : C₀) : Continuous (ext v) := continuous_oddPeriodicExtend v.2.1 v.2.2

/-- The extension $\tilde v$ is odd: $\tilde v(-x) = -\tilde v(x)$. -/
theorem ext_neg (v : C₀) (x : ℝ) : ext v (-x) = -ext v x := oddPeriodicExtend_neg v.2.1 v.2.2 x

/-- The extension $\tilde v$ agrees with $v$ on $[0, \pi]$. -/
theorem ext_of_mem (v : C₀) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) π) :
    ext v x = (v : C(Icc (0 : ℝ) π, ℝ)) ⟨x, hx⟩ := oddPeriodicExtend_of_mem v.2.2 hx

/-- The extension satisfies $|\tilde v(x)| \le \|v\|$ for every $x \in \mathbb{R}$. -/
theorem abs_ext_le (v : C₀) (x : ℝ) : |ext v x| ≤ ‖v‖ := abs_oddPeriodicExtend_le _ x

/-- The extension of the sine polynomial $\sum_{j < n} c_j \sin((j + 1) x)$ is the same sine
polynomial on all of $\mathbb{R}$. -/
theorem ext_sinePolyV (n : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    ext (sinePolyV n c) x = ∑ j ∈ Finset.range n, c j * Real.sin (((j : ℝ) + 1) * x) := by
  rw [ext, coe_sinePolyV, oddPeriodicExtend_sinePolynomial]

/-- The extension of the solution (6.2.7) at time $t$, evaluated at $x \in \mathbb{R}$, is the
finite sine series `Heat.sineSeries ν n b (x, t)`. -/
theorem ext_sineSolution (n : ℕ) (b : ℕ → ℝ) (t x : ℝ) :
    ext (sineSolution ν n b t) x = Heat.sineSeries ν n b (x, t) := by
  rw [sineSolution, ext_sinePolyV, Heat.sineSeries]

/-- For $\Delta x \in \mathbb{R}$, the map $v \mapsto \tilde v(\cdot + \Delta x) + \tilde v(\cdot -
\Delta x)$ from $C_0[0, \pi]$ to itself, as a function. It is the shift part of both schemes of
Example 6.2.8. The image lies in $C_0[0, \pi]$ because the extension is odd about $0$ and about
$\pi$. -/
noncomputable def translateSumFun (Δx : ℝ) (v : C₀) : C₀ :=
  ⟨⟨fun x => ext v ((x : ℝ) + Δx) + ext v ((x : ℝ) - Δx), by
      have hc := continuous_ext v
      exact (hc.comp (continuous_subtype_val.add continuous_const)).add
        (hc.comp (continuous_subtype_val.sub continuous_const))⟩, by
    refine ⟨?_, ?_⟩
    · change ext v ((0 : ℝ) + Δx) + ext v ((0 : ℝ) - Δx) = 0
      rw [zero_add, zero_sub, ext_neg, add_neg_cancel]
    · change ext v (π + Δx) + ext v (π - Δx) = 0
      have h : ext v (π + Δx) = -ext v (π - Δx) := by
        have hp := (oddPeriodicExtend_periodic (v : C(Icc (0 : ℝ) π, ℝ))).sub_eq (π + Δx)
        rw [show π + Δx - 2 * π = -(π - Δx) by ring] at hp
        rw [ext, ← hp, ← ext, ext_neg]
      rw [h, neg_add_cancel]⟩

/-- The value of the translated sum at $x \in [0, \pi]$ is $\tilde v(x + \Delta x) + \tilde v(x -
\Delta x)$. -/
theorem translateSumFun_apply (Δx : ℝ) (v : C₀) (x : Icc (0 : ℝ) π) :
    (translateSumFun Δx v : C(Icc (0 : ℝ) π, ℝ)) x = ext v ((x : ℝ) + Δx) + ext v ((x : ℝ) - Δx) :=
  rfl

/-- The translated sum satisfies $\|\tilde v(\cdot + \Delta x) + \tilde v(\cdot - \Delta x)\| \le 2
\|v\|$. -/
theorem norm_translateSumFun_le (Δx : ℝ) (v : C₀) : ‖translateSumFun Δx v‖ ≤ 2 * ‖v‖ := by
  rw [← Submodule.norm_coe]
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
  rw [translateSumFun_apply, Real.norm_eq_abs]
  calc |ext v ((x : ℝ) + Δx) + ext v ((x : ℝ) - Δx)|
      ≤ |ext v ((x : ℝ) + Δx)| + |ext v ((x : ℝ) - Δx)| := abs_add_le _ _
    _ ≤ ‖v‖ + ‖v‖ := add_le_add (abs_ext_le v _) (abs_ext_le v _)
    _ = 2 * ‖v‖ := by ring

/-- For $\Delta x \in \mathbb{R}$, the bounded linear operator $v \mapsto \tilde v(\cdot + \Delta
x) + \tilde v(\cdot - \Delta x)$ on $C_0[0, \pi]$, where $\tilde v$ is the odd $2\pi$-periodic
extension of $v$. It is the shift part of both schemes of Example 6.2.8, and its norm is at most
$2$. -/
noncomputable def translateSum (Δx : ℝ) : C₀ →L[ℝ] C₀ :=
  LinearMap.mkContinuous
    { toFun := translateSumFun Δx
      map_add' := fun v w => Subtype.ext (ContinuousMap.ext fun x => by
        simp only [translateSumFun_apply, Submodule.coe_add, ContinuousMap.add_apply, ext,
          oddPeriodicExtend_add]
        ring)
      map_smul' := fun a v => Subtype.ext (ContinuousMap.ext fun x => by
        simp only [translateSumFun_apply, Submodule.coe_smul, ContinuousMap.smul_apply, ext,
          oddPeriodicExtend_smul, RingHom.id_apply, smul_eq_mul]
        ring) }
    2 (norm_translateSumFun_le Δx)

/-- The value of the translated sum operator at $x \in [0, \pi]$ is $\tilde v(x + \Delta x) + \tilde
v(x - \Delta x)$. -/
theorem translateSum_apply (Δx : ℝ) (v : C₀) (x : Icc (0 : ℝ) π) :
    (translateSum Δx v : C(Icc (0 : ℝ) π, ℝ)) x = ext v ((x : ℝ) + Δx) + ext v ((x : ℝ) - Δx) :=
  rfl

/-- The translated sum operator has norm at most $2$. -/
theorem norm_translateSum_le (Δx : ℝ) : ‖translateSum Δx‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

/-- **Example 6.2.8** of [han2009theoretical], the forward scheme. For
$\nu, r, \Delta t \in \mathbb{R}$, the forward scheme is the bounded operator $C(\Delta t)$ on
$C_0[0, \pi]$ with
$$C(\Delta t) v(x) = (1 - 2r) v(x) + r [\tilde v(x + \Delta x) + \tilde v(x - \Delta x)], \qquad
  \Delta x = \sqrt{\nu \Delta t / r},$$
where $\tilde v$ is the odd $2\pi$-periodic extension of $v$. The mesh ratio
$r = \nu \Delta t / \Delta x^2$ is held fixed as $\Delta t \to 0$.

The space step is `Real.sqrt (ν * Δt / r)`, which is $0$ when $\nu \Delta t / r \le 0$.

**Generalization.** Same operator on physical inputs, extending formula to arbitrary real
parameters.
-/
noncomputable def forwardScheme (ν r Δt : ℝ) : C₀ →L[ℝ] C₀ :=
  (1 - 2 * r) • (1 : C₀ →L[ℝ] C₀) + r • translateSum (Real.sqrt (ν * Δt / r))

/-- The value of the forward scheme at $x \in [0, \pi]$ is $(1 - 2r) v(x) + r [\tilde v(x + \Delta
x) + \tilde v(x - \Delta x)]$ with $\Delta x = \sqrt{\nu \Delta t / r}$, the formula of Example
6.2.8.

**Reading.** Same stencil and mesh relation with totalized square root and division.
-/
theorem forwardScheme_apply (ν r Δt : ℝ) (v : C₀) (x : Icc (0 : ℝ) π) :
    (forwardScheme ν r Δt v : C(Icc (0 : ℝ) π, ℝ)) x
      = (1 - 2 * r) * (v : C(Icc (0 : ℝ) π, ℝ)) x
        + r * (ext v ((x : ℝ) + Real.sqrt (ν * Δt / r))
          + ext v ((x : ℝ) - Real.sqrt (ν * Δt / r))) := by
  simp only [forwardScheme, add_apply, smul_apply, one_apply_eq_self, Submodule.coe_add,
    Submodule.coe_smul, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
    translateSum_apply]

/-- **Equation (6.2.8)** of [han2009theoretical]. For $r \ge 0$ and all $\nu, \Delta t$, the forward
scheme of Example 6.2.8 satisfies
$$\|C(\Delta t)\| \le |1 - 2r| + 2r.$$
So the forward family is uniformly bounded. -/
theorem norm_forwardScheme_le {r : ℝ} (hr : 0 ≤ r) (ν Δt : ℝ) :
    ‖forwardScheme ν r Δt‖ ≤ |1 - 2 * r| + 2 * r := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) ContinuousLinearMap.norm_id_le
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_translateSum_le _) hr

/-- For $r \ge 0$, the forward scheme satisfies $\|C(\Delta t)\| \le |1 - 2r| + 2r$ for every
$\Delta t \in (0, \Delta_0]$. -/
theorem forall_norm_forwardScheme_le {r : ℝ} (hr : 0 ≤ r) (ν Δ₀ : ℝ) :
    ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ‖forwardScheme ν r Δt‖ ≤ |1 - 2 * r| + 2 * r :=
  fun Δt _ => norm_forwardScheme_le hr ν Δt

/-! ### Consistency of the forward scheme (Example 6.2.8) -/

/-- The constant of the Taylor expansions of Example 6.2.8 for the initial value
$\sum_{j < n} b_j \sin((j + 1) x)$:
$$c = \frac{1}{2} \sum_{j < n} |b_j| \bigl(\nu (j + 1)^2\bigr)^2 + \frac{\nu^2}{12 r} \sum_{j <
  n} |b_j| (j + 1)^4.$$
The two terms bound $u_{tt}/2$ and $(\nu^2 / 12 r) \, u_{xxxx}$.

**Reading.** Replaces implicit remainder constants with finite sine-coefficient sums.
-/
noncomputable def forwardConsistencyConst (ν r : ℝ) (n : ℕ) (b : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) / 2
    + ν ^ 2 * (∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4) / (12 * r)

/-- For $r \ge 0$, the consistency constant of Example 6.2.8 is nonnegative. -/
theorem forwardConsistencyConst_nonneg {ν r : ℝ} (hr : 0 ≤ r) (n : ℕ) (b : ℕ → ℝ) :
    0 ≤ forwardConsistencyConst ν r n b := by
  unfold forwardConsistencyConst
  have h1 : 0 ≤ ∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2 :=
    Finset.sum_nonneg fun j _ => by positivity
  have h2 : 0 ≤ ∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4 :=
    Finset.sum_nonneg fun j _ => by positivity
  positivity

/-- The local truncation error of the forward scheme of Example 6.2.8 on the solution (6.2.7). Let
$\nu > 0$, $r > 0$, $t \ge 0$ and $\Delta t \ge 0$. For the initial value
$\sum_{j < n} b_j \sin((j + 1) x)$, the solution $u$ of (6.2.7) satisfies
$$\|C(\Delta t) u(t) - u(t + \Delta t)\| \le c \, \Delta t^2,$$
with the constant $c$ of `AtkinsonHan.Chapter06.forwardConsistencyConst`.

The proof uses Taylor expansions of $u$ in $t$ and in $x$.

**Reading.** Explicit second-order local error bound before division by the time step.
-/
theorem norm_forwardScheme_sineSolution_sub_le (hν : 0 < ν) {r : ℝ} (hr : 0 < r) (n : ℕ)
    (b : ℕ → ℝ) {t Δt : ℝ} (ht : 0 ≤ t) (hΔt : 0 ≤ Δt) :
    ‖forwardScheme ν r Δt (sineSolution ν n b t) - sineSolution ν n b (t + Δt)‖
      ≤ forwardConsistencyConst ν r n b * Δt ^ 2 := by
  set Δx := Real.sqrt (ν * Δt / r) with hΔx
  have hΔx0 : 0 ≤ Δx := Real.sqrt_nonneg _
  have hΔx2 : Δx ^ 2 = ν * Δt / r := Real.sq_sqrt (by positivity)
  have hrΔx : r * Δx ^ 2 = ν * Δt := by rw [hΔx2]; field_simp
  set Mt := ∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2 with hMt
  set Mx := ∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4 with hMx
  have hMt0 : 0 ≤ Mt := Finset.sum_nonneg fun j _ => by positivity
  have hMx0 : 0 ≤ Mx := Finset.sum_nonneg fun j _ => by positivity
  rw [← Submodule.norm_coe]
  refine (ContinuousMap.norm_le _ (by
    have := forwardConsistencyConst_nonneg (ν := ν) hr.le n b
    positivity)).2 fun x => ?_
  rw [Submodule.coe_sub, ContinuousMap.sub_apply, forwardScheme_apply, ext_sineSolution,
    ext_sineSolution, sineSolution_apply, sineSolution_apply, Real.norm_eq_abs]
  -- the identity `C (Δt) u (t) - u (t + Δt) = r B - A`
  set U := Heat.sineSeries ν n b with hU
  have hUt : Heat.sineSeriesDerivT ν n b 1 ((x : ℝ), t)
      = ν * Heat.sineSeriesDerivX ν n b 2 ((x : ℝ), t) := Heat.sineSeriesDerivT_one _
  have e : (1 - 2 * r) * U ((x : ℝ), t) + r * (U ((x : ℝ) + Δx, t) + U ((x : ℝ) - Δx, t))
        - U ((x : ℝ), t + Δt)
      = r * (U ((x : ℝ) + Δx, t) - 2 * U ((x : ℝ), t) + U ((x : ℝ) - Δx, t)
          - Δx ^ 2 * Heat.sineSeriesDerivX ν n b 2 ((x : ℝ), t))
        - (U ((x : ℝ), t + Δt) - U ((x : ℝ), t)
          - Δt * Heat.sineSeriesDerivT ν n b 1 ((x : ℝ), t)) := by
    rw [hUt]
    linear_combination (Heat.sineSeriesDerivX ν n b 2 ((x : ℝ), t)) * hrΔx
  rw [e]
  have hA := Heat.abs_sineSeries_sub_forward_time_le (ν := ν) (n := n) (b := b) hν.le (x := x) ht
    hΔt
  have hB := Heat.abs_sineSeries_centred_sub_le (ν := ν) (n := n) (b := b) hν.le (x := x) ht hΔx0
  have hΔx4 : r * Δx ^ 4 = ν ^ 2 * Δt ^ 2 / r := by
    rw [show Δx ^ 4 = (Δx ^ 2) ^ 2 by ring, hΔx2]; field_simp
  calc _ ≤ r * (Mx * Δx ^ 4 / 12) + Mt * Δt ^ 2 / 2 := by
        refine (abs_sub _ _).trans (add_le_add ?_ hA)
        rw [abs_mul, abs_of_pos hr]
        exact mul_le_mul_of_nonneg_left hB hr.le
    _ = forwardConsistencyConst ν r n b * Δt ^ 2 := by
        rw [forwardConsistencyConst, ← hMt, ← hMx,
          show r * (Mx * Δx ^ 4 / 12) = (r * Δx ^ 4) * Mx / 12 by ring, hΔx4]
        field_simp
        ring

/-- **Example 6.2.8** of [han2009theoretical], consistency of the forward scheme. Let $\nu > 0$,
$r > 0$, $T \ge 0$ and $\Delta_0 \in \mathbb{R}$. The forward scheme is consistent (Definition
6.2.7) on $V_c = V_0$ with the solution operators $S$ of the heat equation on $[0, T]$, for step
sizes in $(0, \Delta_0]$. For each sine polynomial initial value, the truncation error satisfies
$\|[C(\Delta t) u(t) - u(t + \Delta t)] / \Delta t\| \le c \, \Delta t$.

The family $S$ is the solution operators of Definition 6.2.3 on $[0, T]$ itself, since
Definition 6.2.7 evaluates $S(t + \Delta t)$ only for $t + \Delta t \le T$.

**Reading.** Formalizes consistency using the clipped time horizon.
-/
theorem example_6_2_8 (hν : 0 < ν) {r : ℝ} (hr : 0 < r) {T Δ₀ : ℝ} (hT : 0 ≤ T) :
    IsConsistent (solutionOperator (heatOperator ν) dense_heatOperator_domain hT zero_le_one
      (example_6_2_4 hν T)) (forwardScheme ν r) T Δ₀ sinePolynomials := by
  refine ⟨example_6_2_4_dense, fun u₀ hu₀ ε hε => ?_⟩
  obtain ⟨n, b, rfl⟩ := mem_sinePolynomials_iff.1 hu₀
  set c := forwardConsistencyConst ν r n b with hc
  have hc0 : 0 ≤ c := forwardConsistencyConst_nonneg hr.le n b
  refine ⟨ε / (c + 1), by positivity, fun Δt hΔt hlt t ht htΔ => ?_⟩
  have htΔT : t + Δt ∈ Icc (0 : ℝ) T := ⟨by linarith [ht.1, hΔt.1], htΔ⟩
  rw [example_6_2_4_solutionOperator_apply hν hT ht, example_6_2_4_solutionOperator_apply hν hT
    htΔT, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hΔt.1, ← div_eq_inv_mul,
    div_le_iff₀ hΔt.1]
  calc ‖forwardScheme ν r Δt (sineSolution ν n b t) - sineSolution ν n b (t + Δt)‖
      ≤ c * Δt ^ 2 := norm_forwardScheme_sineSolution_sub_le hν hr n b ht.1 hΔt.1.le
    _ = (c * Δt) * Δt := by ring
    _ ≤ ε * Δt := by
        refine mul_le_mul_of_nonneg_right ?_ hΔt.1.le
        calc c * Δt ≤ c * (ε / (c + 1)) := mul_le_mul_of_nonneg_left hlt.le hc0
          _ ≤ ε := by
              rw [mul_div_assoc', div_le_iff₀ (by positivity)]
              nlinarith

/-! ### The backward scheme (Example 6.2.8, second half) -/

/-- For $\nu, r, \Delta t \in \mathbb{R}$, the bounded operator $Q_1 = (1 + 2r) I - r [\tilde
v(\cdot + \Delta x) + \tilde v(\cdot - \Delta x)]$ on $C_0[0, \pi]$, with
$\Delta x = \sqrt{\nu \Delta t / r}$. It is the left side of the implicit relation of the
backward scheme of Example 6.2.8,
$$(1 + 2r) u(x, t + \Delta t) - r [u(x - \Delta x, t + \Delta t) + u(x + \Delta x, t + \Delta
  t)] = u(x, t).$$

**Generalization.** Extends the same implicit stencil to arbitrary real parameters.
-/
noncomputable def backwardSchemeInv (ν r Δt : ℝ) : C₀ →L[ℝ] C₀ :=
  (1 + 2 * r) • (1 : C₀ →L[ℝ] C₀) - r • translateSum (Real.sqrt (ν * Δt / r))

/-- The value of $Q_1 v$ at $x \in [0, \pi]$ is $(1 + 2r) v(x) - r [\tilde v(x + \Delta x) + \tilde
v(x - \Delta x)]$.

**Reading.** Pointwise formula uses totalized mesh relation.
-/
theorem backwardSchemeInv_apply (ν r Δt : ℝ) (v : C₀) (x : Icc (0 : ℝ) π) :
    (backwardSchemeInv ν r Δt v : C(Icc (0 : ℝ) π, ℝ)) x
      = (1 + 2 * r) * (v : C(Icc (0 : ℝ) π, ℝ)) x
        - r * (ext v ((x : ℝ) + Real.sqrt (ν * Δt / r))
          + ext v ((x : ℝ) - Real.sqrt (ν * Δt / r))) := by
  simp only [backwardSchemeInv, sub_apply, smul_apply, one_apply_eq_self, Submodule.coe_sub,
    Submodule.coe_smul, ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
    translateSum_apply]

/-- For $r \ge 0$ the operator $Q_1$ is invertible. The proof writes $Q_1 = (1 + 2r)(I - B)$ with
$\|B\| \le 2r / (1 + 2r) < 1$ and uses a Neumann series. -/
theorem isUnit_backwardSchemeInv {r : ℝ} (hr : 0 ≤ r) (ν Δt : ℝ) :
    IsUnit (backwardSchemeInv ν r Δt) := by
  have h12 : (0 : ℝ) < 1 + 2 * r := by linarith
  have hB : ‖(r / (1 + 2 * r)) • translateSum (Real.sqrt (ν * Δt / r))‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc r / (1 + 2 * r) * ‖translateSum (Real.sqrt (ν * Δt / r))‖ ≤ r / (1 + 2 * r) * 2 :=
          mul_le_mul_of_nonneg_left (norm_translateSum_le _) (by positivity)
      _ < 1 := by rw [div_mul_eq_mul_div, div_lt_one h12]; linarith
  have e : backwardSchemeInv ν r Δt
      = ((1 + 2 * r) • (1 : C₀ →L[ℝ] C₀))
        * (1 - (r / (1 + 2 * r)) • translateSum (Real.sqrt (ν * Δt / r))) := by
    rw [backwardSchemeInv, mul_sub, mul_one, smul_mul_assoc, one_mul, smul_smul,
      mul_div_cancel₀ _ h12.ne']
  rw [e]
  refine IsUnit.mul ?_ (isUnit_one_sub_of_norm_lt_one hB)
  rw [← Algebra.algebraMap_eq_smul_one]
  exact (algebraMap ℝ (C₀ →L[ℝ] C₀)).isUnit_map (isUnit_iff_ne_zero.2 h12.ne')

/-- **Example 6.2.8** of [han2009theoretical], the backward scheme. For
$\nu, r, \Delta t \in \mathbb{R}$, the backward scheme is $C(\Delta t) = Q_1^{-1}$: it maps $v$
to the solution $w$ of the implicit relation
$$(1 + 2r) w(x) - r [\tilde w(x - \Delta x) + \tilde w(x + \Delta x)] = v(x), \qquad \Delta x =
  \sqrt{\nu \Delta t / r}.$$

The inverse is Mathlib's `Ring.inverse`, which is $0$ when $Q_1$ is not invertible. For
$r \ge 0$, $Q_1$ is invertible by `AtkinsonHan.Chapter06.isUnit_backwardSchemeInv`.

**Reading.** The ring inverse is defined even outside the parameter range that makes the stencil
invertible.
-/
noncomputable def backwardScheme (ν r Δt : ℝ) : C₀ →L[ℝ] C₀ :=
  Ring.inverse (backwardSchemeInv ν r Δt)

/-- For $r \ge 0$, $Q_1 C(\Delta t) = I$ for the backward scheme. -/
theorem backwardSchemeInv_mul_backwardScheme {r : ℝ} (hr : 0 ≤ r) (ν Δt : ℝ) :
    backwardSchemeInv ν r Δt * backwardScheme ν r Δt = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_backwardSchemeInv hr ν Δt)

/-- For $r \ge 0$, $C(\Delta t) Q_1 = I$ for the backward scheme. -/
theorem backwardScheme_mul_backwardSchemeInv {r : ℝ} (hr : 0 ≤ r) (ν Δt : ℝ) :
    backwardScheme ν r Δt * backwardSchemeInv ν r Δt = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_backwardSchemeInv hr ν Δt)

/-- For $r \ge 0$ and every $v$, $Q_1 (C(\Delta t) v) = v$: the backward scheme solves its implicit
relation. -/
theorem backwardSchemeInv_backwardScheme {r : ℝ} (hr : 0 ≤ r) (ν Δt : ℝ) (v : C₀) :
    backwardSchemeInv ν r Δt (backwardScheme ν r Δt v) = v := by
  rw [← mul_apply_eq_comp, backwardSchemeInv_mul_backwardScheme hr, one_apply_eq_self]

/-- **Example 6.2.8** of [han2009theoretical], the bound on the backward scheme. For every $r \ge 0$
and all $\nu, \Delta t$, the backward scheme satisfies
$$\|C(\Delta t)\| \le 1.$$

The proof follows the source: with $w = C(\Delta t) v$, the relation $(1 + 2r) w = v + r [\tilde
w(\cdot - \Delta x) + \tilde w(\cdot + \Delta x)]$ gives $(1 + 2r) \|w\| \le \|v\| + 2r \|w\|$. -/
theorem norm_backwardScheme_le {r : ℝ} (hr : 0 ≤ r) (ν Δt : ℝ) : ‖backwardScheme ν r Δt‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul]
  set w := backwardScheme ν r Δt v with hw
  have h12 : (0 : ℝ) < 1 + 2 * r := by linarith
  have hQ : (1 + 2 * r) • w = v + r • translateSum (Real.sqrt (ν * Δt / r)) w := by
    have := backwardSchemeInv_backwardScheme hr ν Δt v
    rw [backwardSchemeInv, sub_apply, smul_apply, one_apply_eq_self, smul_apply] at this
    rw [← this]
    abel
  have hnorm : (1 + 2 * r) * ‖w‖ ≤ ‖v‖ + 2 * r * ‖w‖ := by
    calc (1 + 2 * r) * ‖w‖ = ‖(1 + 2 * r) • w‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos h12]
      _ ≤ ‖v‖ + ‖r • translateSum (Real.sqrt (ν * Δt / r)) w‖ := by
          rw [hQ]; exact norm_add_le _ _
      _ ≤ ‖v‖ + r * (2 * ‖w‖) := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
          exact mul_le_mul_of_nonneg_left (norm_translateSumFun_le _ w) hr
      _ = ‖v‖ + 2 * r * ‖w‖ := by ring
  linarith

/-- For $r \ge 0$, the backward scheme satisfies $\|C(\Delta t)\| \le 1$ for every
$\Delta t \in (0, \Delta_0]$. -/
theorem forall_norm_backwardScheme_le {r : ℝ} (hr : 0 ≤ r) (ν Δ₀ : ℝ) :
    ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ‖backwardScheme ν r Δt‖ ≤ 1 :=
  fun Δt _ => norm_backwardScheme_le hr ν Δt

/-- The local truncation error of the backward scheme of Example 6.2.8 on the solution (6.2.7). Let
$\nu > 0$, $r > 0$, $t \ge 0$ and $\Delta t \ge 0$. For the initial value
$\sum_{j < n} b_j \sin((j + 1) x)$, the solution $u$ of (6.2.7) satisfies
$$\|C(\Delta t) u(t) - u(t + \Delta t)\| \le c \, \Delta t^2,$$
with the same constant $c$ (`AtkinsonHan.Chapter06.forwardConsistencyConst`) as for the forward
scheme.

The proof writes $C(\Delta t) u(t) - u(t + \Delta t) = C(\Delta t) [u(t) - Q_1 u(t + \Delta
t)]$, uses $\|C(\Delta t)\| \le 1$, and expands $u$ by Taylor's formula at $(x, t + \Delta t)$.

**Reading.** Provides an explicit local error constant for the second-order bound.
-/
theorem norm_backwardScheme_sineSolution_sub_le (hν : 0 < ν) {r : ℝ} (hr : 0 < r) (n : ℕ)
    (b : ℕ → ℝ) {t Δt : ℝ} (ht : 0 ≤ t) (hΔt : 0 ≤ Δt) :
    ‖backwardScheme ν r Δt (sineSolution ν n b t) - sineSolution ν n b (t + Δt)‖
      ≤ forwardConsistencyConst ν r n b * Δt ^ 2 := by
  set Δx := Real.sqrt (ν * Δt / r) with hΔx
  have hΔx0 : 0 ≤ Δx := Real.sqrt_nonneg _
  have hΔx2 : Δx ^ 2 = ν * Δt / r := Real.sq_sqrt (by positivity)
  have hrΔx : r * Δx ^ 2 = ν * Δt := by rw [hΔx2]; field_simp
  set Mt := ∑ j ∈ Finset.range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2 with hMt
  set Mx := ∑ j ∈ Finset.range n, |b j| * ((j : ℝ) + 1) ^ 4 with hMx
  have hMt0 : 0 ≤ Mt := Finset.sum_nonneg fun j _ => by positivity
  have hMx0 : 0 ≤ Mx := Finset.sum_nonneg fun j _ => by positivity
  -- the difference is `C (Δt)` of the residual of `u (t + Δt)` in the implicit relation
  have e : backwardScheme ν r Δt (sineSolution ν n b t) - sineSolution ν n b (t + Δt)
      = backwardScheme ν r Δt
          (sineSolution ν n b t - backwardSchemeInv ν r Δt (sineSolution ν n b (t + Δt))) := by
    rw [map_sub, ← mul_apply_eq_comp, backwardScheme_mul_backwardSchemeInv hr.le,
      one_apply_eq_self]
  rw [e]
  refine ((backwardScheme ν r Δt).le_opNorm _).trans ?_
  refine (mul_le_mul_of_nonneg_right (norm_backwardScheme_le hr.le ν Δt) (norm_nonneg _)).trans ?_
  rw [one_mul, ← Submodule.norm_coe]
  refine (ContinuousMap.norm_le _ (by
    have := forwardConsistencyConst_nonneg (ν := ν) hr.le n b
    positivity)).2 fun x => ?_
  rw [Submodule.coe_sub, ContinuousMap.sub_apply, backwardSchemeInv_apply, ext_sineSolution,
    ext_sineSolution, sineSolution_apply, sineSolution_apply, Real.norm_eq_abs]
  set U := Heat.sineSeries ν n b with hU
  have hUt : Heat.sineSeriesDerivT ν n b 1 ((x : ℝ), t + Δt)
      = ν * Heat.sineSeriesDerivX ν n b 2 ((x : ℝ), t + Δt) := Heat.sineSeriesDerivT_one _
  have e2 : U ((x : ℝ), t) - ((1 + 2 * r) * U ((x : ℝ), t + Δt)
        - r * (U ((x : ℝ) + Δx, t + Δt) + U ((x : ℝ) - Δx, t + Δt)))
      = r * (U ((x : ℝ) + Δx, t + Δt) - 2 * U ((x : ℝ), t + Δt) + U ((x : ℝ) - Δx, t + Δt)
          - Δx ^ 2 * Heat.sineSeriesDerivX ν n b 2 ((x : ℝ), t + Δt))
        - (U ((x : ℝ), t + Δt) - U ((x : ℝ), t)
          - Δt * Heat.sineSeriesDerivT ν n b 1 ((x : ℝ), t + Δt)) := by
    rw [hUt]
    linear_combination (Heat.sineSeriesDerivX ν n b 2 ((x : ℝ), t + Δt)) * hrΔx
  rw [e2]
  have hA := Heat.abs_sineSeries_sub_backward_time_le (ν := ν) (n := n) (b := b) hν.le (x := x) ht
    hΔt
  have hB := Heat.abs_sineSeries_centred_sub_le (ν := ν) (n := n) (b := b) hν.le (x := x)
    (by linarith : 0 ≤ t + Δt) hΔx0
  have hΔx4 : r * Δx ^ 4 = ν ^ 2 * Δt ^ 2 / r := by
    rw [show Δx ^ 4 = (Δx ^ 2) ^ 2 by ring, hΔx2]; field_simp
  calc _ ≤ r * (Mx * Δx ^ 4 / 12) + Mt * Δt ^ 2 / 2 := by
        refine (abs_sub _ _).trans (add_le_add ?_ hA)
        rw [abs_mul, abs_of_pos hr]
        exact mul_le_mul_of_nonneg_left hB hr.le
    _ = forwardConsistencyConst ν r n b * Δt ^ 2 := by
        rw [forwardConsistencyConst, ← hMt, ← hMx,
          show r * (Mx * Δx ^ 4 / 12) = (r * Δx ^ 4) * Mx / 12 by ring, hΔx4]
        field_simp
        ring

/-- **Example 6.2.8** of [han2009theoretical], consistency of the backward scheme. Let $\nu > 0$,
$r > 0$, $T \ge 0$ and $\Delta_0 \in \mathbb{R}$. The backward scheme is consistent (Definition
6.2.7) on $V_c = V_0$ with the solution operators of the heat equation on $[0, T]$, for step
sizes in $(0, \Delta_0]$.

The source calls this case "more involved" and leaves it to the reader. The proof uses
`AtkinsonHan.Chapter06.norm_backwardScheme_sineSolution_sub_le`.

**Reading.** The backward consistency proof uses the clipped time horizon.
-/
theorem example_6_2_8_backward (hν : 0 < ν) {r : ℝ} (hr : 0 < r) {T Δ₀ : ℝ} (hT : 0 ≤ T) :
    IsConsistent (solutionOperator (heatOperator ν) dense_heatOperator_domain hT zero_le_one
      (example_6_2_4 hν T)) (backwardScheme ν r) T Δ₀ sinePolynomials := by
  refine ⟨example_6_2_4_dense, fun u₀ hu₀ ε hε => ?_⟩
  obtain ⟨n, b, rfl⟩ := mem_sinePolynomials_iff.1 hu₀
  set c := forwardConsistencyConst ν r n b with hc
  have hc0 : 0 ≤ c := forwardConsistencyConst_nonneg hr.le n b
  refine ⟨ε / (c + 1), by positivity, fun Δt hΔt hlt t ht htΔ => ?_⟩
  have htΔT : t + Δt ∈ Icc (0 : ℝ) T := ⟨by linarith [ht.1, hΔt.1], htΔ⟩
  rw [example_6_2_4_solutionOperator_apply hν hT ht, example_6_2_4_solutionOperator_apply hν hT
    htΔT, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hΔt.1, ← div_eq_inv_mul,
    div_le_iff₀ hΔt.1]
  calc ‖backwardScheme ν r Δt (sineSolution ν n b t) - sineSolution ν n b (t + Δt)‖
      ≤ c * Δt ^ 2 := norm_backwardScheme_sineSolution_sub_le hν hr n b ht.1 hΔt.1.le
    _ = (c * Δt) * Δt := by ring
    _ ≤ ε * Δt := by
        refine mul_le_mul_of_nonneg_right ?_ hΔt.1.le
        calc c * Δt ≤ c * (ε / (c + 1)) := mul_le_mul_of_nonneg_left hlt.le hc0
          _ ≤ ε := by
              rw [mul_div_assoc', div_le_iff₀ (by positivity)]
              nlinarith

/-! ### Example 6.2.13: the Lax equivalence theorem applied -/

/-- **Example 6.2.13** of [han2009theoretical], the forward scheme. Let $\nu > 0$, $0 < r \le 1/2$,
$T \ge 0$ and $\Delta_0 \in \mathbb{R}$. The forward scheme is stable on $[0, T]$ for step sizes
in $(0, \Delta_0]$, and it is convergent to the solution operators of the heat equation:
$\|C(\Delta t_i)^{m_i} u_0 - S(t) u_0\| \to 0$ whenever $\Delta t_i \to 0$ and
$m_i \Delta t_i \to t$, for every $u_0 \in C_0[0, \pi]$.

For $r \le 1/2$ the bound (6.2.8) gives $\|C(\Delta t)\| \le 1$, hence
$\|C(\Delta t)^m\| \le 1$. Convergence then follows from consistency
(`AtkinsonHan.Chapter06.example_6_2_8`) and the Lax equivalence theorem
`AtkinsonHan.Chapter06.theorem_6_2_11`.

**Reading.** Same sufficient condition and conclusions using the formal clipped convergence
definition.
-/
theorem example_6_2_13 (hν : 0 < ν) {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2) {T Δ₀ : ℝ}
    (hT : 0 ≤ T) :
    IsStable (forwardScheme ν r) T Δ₀ ∧
      IsConvergent (solutionOperator (heatOperator ν) dense_heatOperator_domain hT zero_le_one
        (example_6_2_4 hν T)) (forwardScheme ν r) T Δ₀ := by
  have hC : ∀ Δt ∈ Ioc (0 : ℝ) Δ₀, ‖forwardScheme ν r Δt‖ ≤ 1 := fun Δt hΔt => by
    refine (norm_forwardScheme_le hr.le ν Δt).trans ?_
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hstab := (isStable_iff _ _ _).2 (FiniteDifference.isStable_of_forall_norm_le_one hC T)
  exact ⟨hstab, (theorem_6_2_11 (heatOperator ν) dense_heatOperator_domain hT zero_le_one
    (example_6_2_4 hν T) hC (example_6_2_8 hν hr hT)).1 hstab⟩

/-- **Example 6.2.13** of [han2009theoretical], the backward scheme. Let $\nu > 0$, $r > 0$,
$T \ge 0$ and $\Delta_0 \in \mathbb{R}$. The backward scheme is stable on $[0, T]$ for step
sizes in $(0, \Delta_0]$, and it is convergent to the solution operators of the heat equation.
So the backward scheme is unconditionally stable and convergent.

The proof uses $\|C(\Delta t)\| \le 1$, consistency
(`AtkinsonHan.Chapter06.example_6_2_8_backward`) and the Lax equivalence theorem.

**Reading.** Same unconditional stability and convergence for positive mesh ratios, with clipped
convergence definition.
-/
theorem example_6_2_13_backward (hν : 0 < ν) {r : ℝ} (hr : 0 < r) {T Δ₀ : ℝ} (hT : 0 ≤ T) :
    IsStable (backwardScheme ν r) T Δ₀ ∧
      IsConvergent (solutionOperator (heatOperator ν) dense_heatOperator_domain hT zero_le_one
        (example_6_2_4 hν T)) (backwardScheme ν r) T Δ₀ := by
  have hC := forall_norm_backwardScheme_le hr.le ν Δ₀
  have hstab := (isStable_iff _ _ _).2 (FiniteDifference.isStable_of_forall_norm_le_one hC T)
  exact ⟨hstab, (theorem_6_2_11 (heatOperator ν) dense_heatOperator_domain hT zero_le_one
    (example_6_2_4 hν T) hC (example_6_2_8_backward hν hr hT)).1 hstab⟩

/-! ### Exercise 6.2.3: the exact norm of the forward scheme -/

section ExactNorm

/-- The test function of Exercise 6.2.3 on $[0, \pi]$: the plateau $1$ on
$[\pi/2 - \Delta x, \pi/2 + \Delta x]$, joined linearly to $0$ at the ends, minus twice the hat
function of height $1$ and half-width $\Delta x$ at $\pi/2$ when $r > 1/2$; it has $|v| \le 1$,
$v(\pi/2 \pm \Delta x) = 1$, and $v(\pi/2) = \pm 1$ with the sign of $1 - 2r$. -/
private noncomputable def testFun (r Δx : ℝ) : C(Icc (0 : ℝ) π, ℝ) :=
  ⟨fun x => min 1 (min ((x : ℝ) / (π / 2 - Δx)) ((π - (x : ℝ)) / (π / 2 - Δx)))
    - (if r ≤ 1 / 2 then 0 else 2) * max 0 (1 - |(x : ℝ) - π / 2| / Δx), by fun_prop⟩

private theorem testFun_apply (r Δx : ℝ) (x : Icc (0 : ℝ) π) :
    testFun r Δx x = min 1 (min ((x : ℝ) / (π / 2 - Δx)) ((π - (x : ℝ)) / (π / 2 - Δx)))
      - (if r ≤ 1 / 2 then 0 else 2) * max 0 (1 - |(x : ℝ) - π / 2| / Δx) := rfl

variable {r Δx : ℝ} (hΔx : 0 < Δx) (hΔx' : Δx < π / 2)
include hΔx hΔx'

omit hΔx' in
private theorem hat_eq_zero {y : ℝ} (hy : Δx ≤ |y - π / 2|) :
    max 0 (1 - |y - π / 2| / Δx) = 0 :=
  max_eq_left (by rw [sub_nonpos, one_le_div hΔx]; exact hy)

private theorem testFun_mem_C₀ : testFun r Δx ∈ C₀ := by
  have ha : 0 < π / 2 - Δx := by linarith
  refine ⟨?_, ?_⟩
  · change min 1 (min ((0 : ℝ) / (π / 2 - Δx)) ((π - 0) / (π / 2 - Δx)))
      - (if r ≤ 1 / 2 then 0 else 2) * max 0 (1 - |0 - π / 2| / Δx) = 0
    have h0 : Δx ≤ |(0 : ℝ) - π / 2| := by
      rw [zero_sub, abs_neg, abs_of_pos (by positivity)]; exact hΔx'.le
    rw [hat_eq_zero hΔx h0, zero_div,
      min_eq_left (a := (0 : ℝ)) (b := (π - 0) / (π / 2 - Δx))
        (div_nonneg (by linarith [Real.pi_pos]) ha.le),
      min_eq_right zero_le_one]
    ring
  · change min 1 (min (π / (π / 2 - Δx)) ((π - π) / (π / 2 - Δx)))
      - (if r ≤ 1 / 2 then 0 else 2) * max 0 (1 - |π - π / 2| / Δx) = 0
    have hπ : Δx ≤ |π - π / 2| := by
      rw [show π - π / 2 = π / 2 by ring, abs_of_pos (by positivity)]; exact hΔx'.le
    rw [hat_eq_zero hΔx hπ, sub_self, zero_div,
      min_eq_right (a := π / (π / 2 - Δx)) (b := (0 : ℝ)) (div_nonneg Real.pi_pos.le ha.le),
      min_eq_right zero_le_one]
    ring

private theorem abs_testFun_le (x : Icc (0 : ℝ) π) : |testFun r Δx x| ≤ 1 := by
  have ha : 0 < π / 2 - Δx := by linarith
  rw [testFun_apply]
  set w := min 1 (min ((x : ℝ) / (π / 2 - Δx)) ((π - (x : ℝ)) / (π / 2 - Δx))) with hw
  set h := max 0 (1 - |(x : ℝ) - π / 2| / Δx) with hh
  have hw1 : w ≤ 1 := min_le_left _ _
  have hw0 : 0 ≤ w := le_min zero_le_one (le_min (by have := x.2.1; positivity)
    (by have := x.2.2; exact div_nonneg (by linarith) ha.le))
  have hh0 : 0 ≤ h := le_max_left _ _
  have hh1 : h ≤ 1 := max_le zero_le_one (by
    have : 0 ≤ |(x : ℝ) - π / 2| / Δx := by positivity
    linarith)
  split_ifs with hr
  · rw [zero_mul, sub_zero, abs_le]; constructor <;> linarith
  · -- off the plateau the hat vanishes, on it `w = 1`
    rw [abs_le]
    rcases le_or_gt (|(x : ℝ) - π / 2|) Δx with hin | hout
    · have hw' : w = 1 := by
        rw [hw]
        refine min_eq_left (le_min ?_ ?_)
        · rw [le_div_iff₀ ha]
          have := abs_le.1 hin
          linarith
        · rw [le_div_iff₀ ha]
          have := abs_le.1 hin
          linarith
      rw [hw']
      constructor <;> linarith
    · have hh' : h = 0 := hat_eq_zero hΔx hout.le
      rw [hh', mul_zero, sub_zero]
      exact ⟨by linarith, hw1⟩

private theorem testFun_mid :
    testFun r Δx ⟨π / 2, ⟨by positivity, by linarith [Real.pi_pos]⟩⟩
      = if r ≤ 1 / 2 then 1 else -1 := by
  have ha : 0 < π / 2 - Δx := by linarith
  change min 1 (min (π / 2 / (π / 2 - Δx)) ((π - π / 2) / (π / 2 - Δx)))
    - (if r ≤ 1 / 2 then 0 else 2) * max 0 (1 - |π / 2 - π / 2| / Δx) = _
  have h1 : min 1 (min (π / 2 / (π / 2 - Δx)) ((π - π / 2) / (π / 2 - Δx))) = 1 := by
    refine min_eq_left (le_min ?_ ?_)
    · rw [le_div_iff₀ ha]; linarith
    · rw [le_div_iff₀ ha]; linarith
  rw [h1, sub_self, abs_zero, zero_div, sub_zero, max_eq_right zero_le_one, mul_one]
  split_ifs <;> norm_num

private theorem testFun_mid_add :
    testFun r Δx ⟨π / 2 + Δx, ⟨by positivity, by linarith [Real.pi_pos]⟩⟩ = 1 := by
  have ha : 0 < π / 2 - Δx := by linarith
  change min 1 (min ((π / 2 + Δx) / (π / 2 - Δx)) ((π - (π / 2 + Δx)) / (π / 2 - Δx)))
    - (if r ≤ 1 / 2 then 0 else 2) * max 0 (1 - |π / 2 + Δx - π / 2| / Δx) = 1
  have h1 : Δx ≤ |π / 2 + Δx - π / 2| := by rw [add_sub_cancel_left, abs_of_pos hΔx]
  rw [hat_eq_zero hΔx h1, mul_zero, sub_zero]
  refine min_eq_left (le_min ?_ ?_)
  · rw [le_div_iff₀ ha]; linarith
  · rw [le_div_iff₀ ha]; linarith

private theorem testFun_mid_sub :
    testFun r Δx ⟨π / 2 - Δx, ⟨by linarith, by linarith [Real.pi_pos]⟩⟩ = 1 := by
  have ha : 0 < π / 2 - Δx := by linarith
  change min 1 (min ((π / 2 - Δx) / (π / 2 - Δx)) ((π - (π / 2 - Δx)) / (π / 2 - Δx)))
    - (if r ≤ 1 / 2 then 0 else 2) * max 0 (1 - |π / 2 - Δx - π / 2| / Δx) = 1
  have h1 : Δx ≤ |π / 2 - Δx - π / 2| := by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hΔx]
  rw [hat_eq_zero hΔx h1, mul_zero, sub_zero]
  refine min_eq_left (le_min ?_ ?_)
  · rw [div_self ha.ne']
  · rw [le_div_iff₀ ha]; linarith

omit hΔx hΔx' in
/-- **Exercise 6.2.3** of [han2009theoretical], the exact norm of the forward scheme. Let $r > 0$,
and let the space step $\Delta x = \sqrt{\nu \Delta t / r}$ satisfy $0 < \Delta x < \pi/2$. Then
the forward scheme of Example 6.2.8 satisfies
$$\|C(\Delta t)\| = |1 - 2r| + 2r.$$

**Correction.** The source states the equality with no condition on $\Delta x$. Some smallness
of $\Delta x$ is needed: for $\Delta x = 2\pi$ the shifts are trivial, so $C(\Delta t) = I$ and
$\|C(\Delta t)\| = 1 < |1 - 2r| + 2r$ when $r > 1/2$.

The bound $\le$ is (6.2.8). For $\ge$, a test function $v$ with $|v| \le 1$,
$v(\pi/2 \pm \Delta x) = 1$ and $v(\pi/2) = \operatorname{sign}(1 - 2r)$ gives
$C(\Delta t) v(\pi/2) = |1 - 2r| + 2r$. -/
theorem norm_forwardScheme_eq {ν r Δt : ℝ} (hr : 0 < r) (hΔx : 0 < Real.sqrt (ν * Δt / r))
    (hΔx' : Real.sqrt (ν * Δt / r) < π / 2) :
    ‖forwardScheme ν r Δt‖ = |1 - 2 * r| + 2 * r := by
  refine le_antisymm (norm_forwardScheme_le hr.le ν Δt) ?_
  set Δx := Real.sqrt (ν * Δt / r) with hΔxdef
  set v : C₀ := ⟨testFun r Δx, testFun_mem_C₀ hΔx hΔx'⟩ with hv
  have hv1 : ‖v‖ ≤ 1 := by
    rw [← Submodule.norm_coe]
    exact (ContinuousMap.norm_le _ zero_le_one).2 fun x => by
      rw [Real.norm_eq_abs]; exact abs_testFun_le hΔx hΔx' x
  have hmid : π / 2 ∈ Icc (0 : ℝ) π := ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hval : (forwardScheme ν r Δt v : C(Icc (0 : ℝ) π, ℝ)) ⟨π / 2, hmid⟩
      = |1 - 2 * r| + 2 * r := by
    rw [forwardScheme_apply, ← hΔxdef, ext_of_mem v (x := π / 2 + Δx)
      ⟨by positivity, by linarith [Real.pi_pos]⟩, ext_of_mem v (x := π / 2 - Δx)
      ⟨by linarith, by linarith [Real.pi_pos]⟩]
    change (1 - 2 * r) * testFun r Δx ⟨π / 2, hmid⟩ + r * (testFun r Δx ⟨π / 2 + Δx, _⟩
      + testFun r Δx ⟨π / 2 - Δx, _⟩) = _
    rw [testFun_mid hΔx hΔx', testFun_mid_add hΔx hΔx', testFun_mid_sub hΔx hΔx']
    split_ifs with h
    · rw [abs_of_nonneg (by linarith)]; ring
    · rw [abs_of_neg (by linarith)]; ring
  calc |1 - 2 * r| + 2 * r = ‖(forwardScheme ν r Δt v : C(Icc (0 : ℝ) π, ℝ)) ⟨π / 2, hmid⟩‖ := by
        rw [hval, Real.norm_eq_abs, abs_of_nonneg (a := |1 - 2 * r| + 2 * r) (by positivity)]
    _ ≤ ‖forwardScheme ν r Δt v‖ := by
        rw [← Submodule.norm_coe]; exact ContinuousMap.norm_coe_le_norm _ _
    _ ≤ ‖forwardScheme ν r Δt‖ * ‖v‖ := (forwardScheme ν r Δt).le_opNorm v
    _ ≤ ‖forwardScheme ν r Δt‖ := mul_le_of_le_one_right (norm_nonneg _) hv1

end ExactNorm

/-! ### Exercise 6.2.3, second half: the forward scheme is unstable for $r > 1/2$ -/

section Instability

/-- For $k \in \mathbb{N}$ and $y \in \mathbb{R}$, the odd $2\pi$-periodic extension of
$\sin((k + 1) x)$ takes the value $\sin((k + 1) y)$ at $y$. -/
theorem ext_sinV (k : ℕ) (y : ℝ) : ext (sinV k) y = Real.sin (((k : ℝ) + 1) * y) := by
  have h : sinV k = sinePolyV (k + 1) fun j => if j = k then 1 else 0 := by
    apply Subtype.ext
    rw [coe_sinePolyV, coe_sinV]
    ext x
    rw [sinePolynomial_apply, Finset.sum_eq_single k (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_range.2 (Nat.lt_succ_self k)) h)]
    simp [sinMap_apply]
  rw [h, ext_sinePolyV, Finset.sum_eq_single k (fun j _ hj => by simp [hj])
    (fun h => absurd (Finset.mem_range.2 (Nat.lt_succ_self k)) h)]
  simp

/-- The amplification factor of the forward scheme of Example 6.2.8 on the mode $\sin((k + 1) x)$.
For all $\nu, r, \Delta t$ and $k \in \mathbb{N}$, with $\Delta x = \sqrt{\nu \Delta t / r}$,
$$C(\Delta t) \sin((k + 1) x) = \bigl(1 - 2r + 2r \cos((k + 1) \Delta x)\bigr) \sin((k + 1)
  x).$$
-/
theorem forwardScheme_sinV (ν r Δt : ℝ) (k : ℕ) :
    forwardScheme ν r Δt (sinV k)
      = (1 - 2 * r + 2 * r * Real.cos (((k : ℝ) + 1) * Real.sqrt (ν * Δt / r))) • sinV k := by
  apply Subtype.ext
  ext x
  rw [forwardScheme_apply, ext_sinV, ext_sinV, Submodule.coe_smul, ContinuousMap.smul_apply,
    coe_sinV, sinMap_apply, smul_eq_mul]
  simp only [mul_add, mul_sub, Real.sin_add, Real.sin_sub]
  ring

/-- For $m \in \mathbb{N}$, the power $C(\Delta t)^m$ of the forward scheme maps $\sin((k + 1) x)$
to $\bigl(1 - 2r + 2r \cos((k + 1) \Delta x)\bigr)^m \sin((k + 1) x)$. -/
theorem forwardScheme_pow_sinV (ν r Δt : ℝ) (k m : ℕ) :
    (forwardScheme ν r Δt ^ m) (sinV k)
      = (1 - 2 * r + 2 * r * Real.cos (((k : ℝ) + 1) * Real.sqrt (ν * Δt / r))) ^ m • sinV k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    change forwardScheme ν r Δt ((forwardScheme ν r Δt ^ m) (sinV k)) = _
    rw [ih, map_smul, forwardScheme_sinV, smul_smul, pow_succ, mul_comm]

/-- The function $\sin((k + 1) x)$ has maximum norm $1$ in $C_0[0, \pi]$. The maximum is attained at
$x = \pi / (2(k + 1))$. -/
theorem norm_sinV (k : ℕ) : ‖sinV k‖ = 1 := by
  rw [← Submodule.norm_coe, coe_sinV]
  refine le_antisymm ((ContinuousMap.norm_le _ zero_le_one).2 fun x => by
    rw [sinMap_apply, Real.norm_eq_abs]; exact Real.abs_sin_le_one _) ?_
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hmem : π / (2 * ((k : ℝ) + 1)) ∈ Icc (0 : ℝ) π := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  calc (1 : ℝ) = ‖sinMap k ⟨π / (2 * ((k : ℝ) + 1)), hmem⟩‖ := by
        rw [sinMap_apply, Real.norm_eq_abs]
        change (1 : ℝ) = |Real.sin (((k : ℝ) + 1) * (π / (2 * ((k : ℝ) + 1))))|
        rw [show ((k : ℝ) + 1) * (π / (2 * ((k : ℝ) + 1))) = π / 2 by field_simp,
          Real.sin_pi_div_two, abs_one]
    _ ≤ ‖sinMap k‖ := ContinuousMap.norm_coe_le_norm _ _

/-- For all $k, m \in \mathbb{N}$, the forward scheme satisfies $\|C(\Delta t)^m\| \ge |1 - 2r + 2r
\cos((k + 1) \Delta x)|^m$, by its action on the mode $\sin((k + 1) x)$. -/
theorem pow_le_norm_forwardScheme_pow (ν r Δt : ℝ) (k m : ℕ) :
    |1 - 2 * r + 2 * r * Real.cos (((k : ℝ) + 1) * Real.sqrt (ν * Δt / r))| ^ m
      ≤ ‖forwardScheme ν r Δt ^ m‖ := by
  have h := (forwardScheme ν r Δt ^ m).le_opNorm (sinV k)
  rw [forwardScheme_pow_sinV, norm_smul, norm_sinV, mul_one, mul_one, Real.norm_eq_abs,
    abs_pow] at h
  exact h

/-- **Exercise 6.2.3** of [han2009theoretical], the necessity of $r \le 1/2$. Let $\nu > 0$,
$r > 1/2$, $T > 0$ and $\Delta_0 > 0$. Then the forward scheme of Example 6.2.8 is not stable on
$[0, T]$ for step sizes in $(0, \Delta_0]$.

With `AtkinsonHan.Chapter06.example_6_2_13`, the forward scheme is stable if and only if
$r \le 1/2$: it is conditionally stable. On a mode $\sin((k + 1) x)$ with $(k + 1) \Delta x$
within $\Delta x$ of $\pi$, the amplification factor $1 - 2r + 2r \cos((k + 1) \Delta x)$ is at
most $-2r$ once $\Delta x^2 \le (2r - 1)/r$. So $\|C(\Delta t)^m\| \ge (2r)^m$ with $2r > 1$,
which is unbounded as $\Delta t \to 0$ with $m \Delta t \le T$. -/
theorem not_isStable_forwardScheme (hν : 0 < ν) {r : ℝ} (hr : 1 / 2 < r) {T Δ₀ : ℝ} (hT : 0 < T)
    (hΔ₀ : 0 < Δ₀) : ¬ IsStable (forwardScheme ν r) T Δ₀ := by
  rintro ⟨M₀, hM₀⟩
  have hr0 : 0 < r := by linarith
  have h2r : 1 < 2 * r := by linarith
  -- a number of steps `m ≥ 1` with `(2r)^m > M₀`
  obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h2r).eventually_gt_atTop M₀ |>.exists
  set m' := m + 1
  have hm' : M₀ < (2 * r) ^ m' :=
    hm.trans_le (pow_le_pow_right₀ h2r.le (Nat.le_succ m))
  have hm'pos : (0 : ℝ) < m' := by positivity
  -- the step size
  set Δt := min (T / m') (min Δ₀ ((2 * r - 1) / ν)) with hΔt
  have hΔt0 : 0 < Δt := lt_min (by positivity) (lt_min hΔ₀ (by
    have : 0 < 2 * r - 1 := by linarith
    positivity))
  have hΔtT : (m' : ℝ) * Δt ≤ T := by
    calc (m' : ℝ) * Δt ≤ m' * (T / m') := mul_le_mul_of_nonneg_left (min_le_left _ _) hm'pos.le
      _ = T := by field_simp
  have hΔtΔ₀ : Δt ≤ Δ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hΔtν : Δt ≤ (2 * r - 1) / ν := (min_le_right _ _).trans (min_le_right _ _)
  -- the space step and the mode
  set Δx := Real.sqrt (ν * Δt / r) with hΔx
  have hΔx0 : 0 < Δx := Real.sqrt_pos.2 (by positivity)
  have hΔx2 : Δx ^ 2 ≤ (2 * r - 1) / r := by
    rw [hΔx, Real.sq_sqrt (by positivity), div_le_div_iff_of_pos_right hr0]
    calc ν * Δt ≤ ν * ((2 * r - 1) / ν) := mul_le_mul_of_nonneg_left hΔtν hν.le
      _ = 2 * r - 1 := by field_simp
  set k := ⌈π / Δx⌉₊ - 1 with hk
  have hk1 : 1 ≤ ⌈π / Δx⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  have hkcast : ((k : ℕ) : ℝ) + 1 = (⌈π / Δx⌉₊ : ℝ) := by
    rw [hk, Nat.cast_sub hk1, Nat.cast_one, sub_add_cancel]
  -- `(k + 1) Δx ∈ [π, π + Δx)`
  have hlow : π ≤ ((k : ℝ) + 1) * Δx := by
    rw [hkcast, ← div_le_iff₀ hΔx0]
    exact Nat.le_ceil _
  have hupp : ((k : ℝ) + 1) * Δx < π + Δx := by
    rw [hkcast, ← lt_div_iff₀ hΔx0, add_div, div_self hΔx0.ne']
    exact Nat.ceil_lt_add_one (by positivity)
  -- the amplification factor is at most `-2r`
  have hcos : Real.cos (((k : ℝ) + 1) * Δx) ≤ -(1 - Δx ^ 2 / 2) := by
    have h1 : Real.cos (((k : ℝ) + 1) * Δx) = -Real.cos (((k : ℝ) + 1) * Δx - π) := by
      rw [Real.cos_sub_pi, neg_neg]
    rw [h1, neg_le_neg_iff]
    refine (Real.one_sub_sq_div_two_le_cos (x := ((k : ℝ) + 1) * Δx - π)).trans' ?_
    have h2 : (((k : ℝ) + 1) * Δx - π) ^ 2 ≤ Δx ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    linarith
  have hlam : 1 - 2 * r + 2 * r * Real.cos (((k : ℝ) + 1) * Δx) ≤ -(2 * r) := by
    have h3 : 2 * r * Real.cos (((k : ℝ) + 1) * Δx) ≤ 2 * r * (-(1 - Δx ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left hcos (by positivity)
    have h4 : r * Δx ^ 2 ≤ 2 * r - 1 := by
      rw [mul_comm, ← le_div_iff₀ hr0]; exact hΔx2
    nlinarith
  have habs : 2 * r ≤ |1 - 2 * r + 2 * r * Real.cos (((k : ℝ) + 1) * Δx)| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  -- the contradiction
  have hbound := hM₀ Δt ⟨hΔt0, hΔtΔ₀⟩ m' hΔtT
  have hlower := pow_le_norm_forwardScheme_pow ν r Δt k m'
  rw [← hΔx] at hlower
  have : (2 * r) ^ m' ≤ ‖forwardScheme ν r Δt ^ m'‖ :=
    (pow_le_pow_left₀ (by positivity) habs m').trans hlower
  linarith

end Instability

end Schemes

end HeatExample

end AtkinsonHan.Chapter06
