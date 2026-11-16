/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Variational.EllipticInterval.BoundaryConditions
import NumlibSurface.Brezis.Chapter08.Section01
import NumlibSurface.Brezis.Chapter08.Section03

/-!
# Brezis, Section 8.4: Some examples of boundary value problems

This module formalizes Section 8.4 of [brezis2011functional]. Let $I = (0, 1)$ and
$\bar I = [0, 1]$. The section first carries out the variational method of Section 8.1 for the
Dirichlet problem (14),
$$-u'' + u = f \text{ on } I, \qquad u(0) = u(1) = 0.$$
A weak solution is a function $u \in H_0^1(I)$ with $\int_I u'v' + \int_I uv = \int_I fv$ for all
$v \in H_0^1(I)$, which is (15). Step A says that a classical solution is a weak solution.
Proposition 8.15 (Step B) gives a unique weak solution for every $f \in L^2(I)$, which minimizes
$\frac12 \int_I (v'^2 + v^2) - \int_I fv$ over $H_0^1(I)$. Steps C and D show that $u \in H^2(I)$,
and that $u \in C^2(\bar I)$ is a classical solution when $f \in C(\bar I)$. Remark 22 identifies
the weak solution with the Riesz–Fréchet representative of $v \mapsto \int fv$, and Remark 23 gives
$u \in H^{k+2}(I)$ for $f \in H^k(I)$.

Examples 1–8 apply the method to other problems: the inhomogeneous Dirichlet condition (Proposition
8.16, by two methods), the Sturm–Liouville problem $-(pu')' + qu = f$ and the problem (20)
$-(pu')' + ru' + qu = f$ with a first-order term (Example 2), the homogeneous and inhomogeneous
Neumann conditions (Propositions 8.17 and 8.18), the mixed, Robin and periodic conditions (Examples
5–7), and the problem $-u'' + u = f$ on $\mathbb{R}$ (Example 8). Remarks 24 and 25 treat the
problem $-u'' = f$ on $\mathbb{R}$, which is not coercive, and the problem $-u'' + u = f$ on the
half-line $(0, +\infty)$. The proofs specialize the backbone modules
`Numlib.Variational.EllipticInterval` and `Numlib.Variational.EllipticInterval.BoundaryConditions`.

## Main definitions

* Section 8.4, definition of a classical solution of (14),
  `Brezis.Chapter08.IsClassicalSolutionDirichlet`: $u \in C^2(\bar I)$ satisfies (14).
* Section 8.4, definition of a weak solution of (14), `Brezis.Chapter08.IsWeakSolutionDirichlet`:
  $u \in H_0^1(I)$ satisfies (15).

## Main results

* Section 8.4, the weak formulation, `Brezis.Chapter08.isWeakSolutionDirichlet_iff`: a weak solution
  is exactly a function $u \in H_0^1(I)$ that satisfies (15).
* Section 8.4, Step A, `Brezis.Chapter08.dirichlet_stepA`: a classical solution of (14) is a weak
  solution.
* Proposition 8.15, `Brezis.Chapter08.proposition_8_15`: for every $f \in L^2(I)$, (14) has a unique
  weak solution.
* Proposition 8.15, the energy, `Brezis.Chapter08.energy_dirichlet_eq`: the energy of the problem is
  $\frac12 \int_I (v'^2 + v^2) - \int_I fv$.
* Proposition 8.15, Dirichlet's principle, `Brezis.Chapter08.proposition_8_15_dirichletPrinciple`:
  $u \in H_0^1(I)$ is the weak solution if and only if it minimizes the energy over $H_0^1(I)$.
* Remark 22, `Brezis.Chapter08.remark_8_22`: for every $F \in H^{-1}(I)$ there is a unique
  $u \in H_0^1(I)$ with $(u, v)_{H^1} = \langle F, v \rangle$ for all $v \in H_0^1(I)$.
* Remark 22, the weak solution, `Brezis.Chapter08.remark_8_22_eq_weakSolution`: for
  $F = (v \mapsto \int fv)$ this $u$ is the weak solution of (14).
* Section 8.4, Steps C and D, `Brezis.Chapter08.dirichlet_stepC`: the weak solution lies in $H^2(I)$
  and satisfies $u'' = u - f$ almost everywhere.
* Section 8.4, Steps C and D, `Brezis.Chapter08.dirichlet_stepCD`: for continuous $f$, the weak
  solution is a classical solution in $C^2(\bar I)$.
* Remark 23, `Brezis.Chapter08.remark_8_23`: if $f \in H^k(I)$ with $k \ge 1$, the weak solution
  lies in $H^{k+2}(I)$.
* Proposition 8.16, `Brezis.Chapter08.proposition_8_16`: the problem $-u'' + u = f$,
  $u(0) = \alpha$, $u(1) = \beta$ has a unique solution in $H^2(I)$.
* Proposition 8.16, the minimization, `Brezis.Chapter08.proposition_8_16_min`: this solution
  minimizes the energy over $\{v \in H^1(I) : v(0) = \alpha, v(1) = \beta\}$.
* Proposition 8.16, the classical solution, `Brezis.Chapter08.proposition_8_16_C2`: for continuous
  $f$ the solution lies in $C^2(\bar I)$.
* Proposition 8.16, Method 1, `Brezis.Chapter08.proposition_8_16_method1`: $u - u_0$, with $u_0$
  affine, solves the homogeneous problem (14) with the datum $f - u_0$.
* Proposition 8.16, Method 2, `Brezis.Chapter08.proposition_8_16_method2`: the variational
  inequality (17) on the set $K$ has a unique solution, which minimizes the energy on $K$ and
  satisfies the weak equation.
* Example 2, existence and uniqueness, `Brezis.Chapter08.example_8_2_existsUnique`: the
  Sturm–Liouville problem has a unique weak solution in $H_0^1(I)$.
* Example 2, the minimization, `Brezis.Chapter08.example_8_2_min`: the weak solution minimizes
  $\frac12 \int_I (pv'^2 + qv^2) - \int_I fv$ over $H_0^1(I)$.
* Example 2, $H^2$ regularity, `Brezis.Chapter08.example_8_2_H2`: the weak solution lies in
  $H^2(I)$.
* Example 2, the classical solution, `Brezis.Chapter08.example_8_2_C2`: for continuous $q$ and $f$
  the weak solution is a classical solution in $C^2(\bar I)$.
* Example 2, `Brezis.Chapter08.example_8_2`: the three statements above together.
* Example 2, case (i), `Brezis.Chapter08.example_8_2_general_i_coercive` and
  `Brezis.Chapter08.example_8_2_general_i`: if $q \ge 1$ and $\|r\|_\infty^2 < 4\alpha$, the form of
  (20) is coercive on $H^1(I)$, and (20) has a unique weak solution.
* Example 2, case (ii), `Brezis.Chapter08.example_8_2_general_ii_coercive` and
  `Brezis.Chapter08.example_8_2_general_ii`: if $q \ge 1$, $r \in C^1(\bar I)$ and $r' \le 2$, the
  form of (20) is coercive on $H_0^1(I)$, and (20) has a unique weak solution.
* Example 2, problem (20), `Brezis.Chapter08.example_8_2_general`: the two cases together.
* Example 2, the symmetrization, `Brezis.Chapter08.example_8_2_symmetrization_deriv` and
  `Brezis.Chapter08.example_8_2_symmetrization`: with $\zeta = e^{-R}$ and $R' = r/p$, equation (20)
  is equivalent to $-(\zeta pu')' + \zeta qu = \zeta f$.
* Proposition 8.17, `Brezis.Chapter08.proposition_8_17`: the Neumann problem $-u'' + u = f$,
  $u'(0) = u'(1) = 0$ has a unique solution in $H^2(I)$.
* Proposition 8.17, the weak formulation and the minimization,
  `Brezis.Chapter08.proposition_8_17_min`: this solution satisfies (22) and minimizes the energy
  over $H^1(I)$.
* Proposition 8.17, the classical solution, `Brezis.Chapter08.proposition_8_17_C2`: for continuous
  $f$ the solution lies in $C^2(\bar I)$.
* Proposition 8.18, `Brezis.Chapter08.proposition_8_18`: the problem $-u'' + u = f$,
  $u'(0) = \alpha$, $u'(1) = \beta$ has a unique solution in $H^2(I)$.
* Proposition 8.18, the minimization, `Brezis.Chapter08.proposition_8_18_min`: this solution
  minimizes $\frac12 \int_I (v'^2 + v^2) - \int_I fv + \alpha v(0) - \beta v(1)$ over $H^1(I)$.
* Example 5, `Brezis.Chapter08.example_8_5`: the mixed problem $u(0) = 0$, $u'(1) = 0$ has a unique
  solution in $H^2(I)$.
* Example 6, the form, `Brezis.Chapter08.example_8_6_coercive`: for $k \ge 0$ the Robin form is
  symmetric and coercive.
* Example 6, `Brezis.Chapter08.example_8_6`: the Robin problem $u'(0) = ku(0)$, $u(1) = 0$ has a
  unique solution in $H^2(I)$.
* Example 7, `Brezis.Chapter08.example_8_7`: the periodic problem $u(0) = u(1)$, $u'(0) = u'(1)$ has
  a unique solution in $H^2(I)$.
* Examples 5–7, the classical solution, `Brezis.Chapter08.example_8_5_6_7_C2`: for continuous $f$
  these solutions lie in $C^2(\bar I)$.
* Example 8, a classical solution is a weak solution, `Brezis.Chapter08.example_8_8_classical_weak`:
  a classical solution of (30) lies in $H^1(\mathbb{R})$ and satisfies (31).
* Example 8, existence and uniqueness, `Brezis.Chapter08.example_8_8_existsUnique`: (31) has a
  unique solution in $H^1(\mathbb{R})$.
* Example 8, regularity, `Brezis.Chapter08.example_8_8_regularity`: the weak solution lies in
  $H^2(\mathbb{R})$ and tends to $0$ at infinity, and for continuous $f$ problem (30) has a unique
  classical solution.
* Example 8, `Brezis.Chapter08.example_8_8`: the statements of Example 8 together.
* Remark 24, `Brezis.Chapter08.remark_8_24_not_coercive`,
  `Brezis.Chapter08.remark_8_24_exists_not_solvable` and `Brezis.Chapter08.remark_8_24`: the form
  $\int u'v'$ is not coercive on $H^1(\mathbb{R})$, and $-u'' = f$ on $\mathbb{R}$, $u(x) \to 0$ as
  $|x| \to \infty$, need not have a solution for $f \in C_c^\infty(\mathbb{R})$.
* Remark 25, `Brezis.Chapter08.remark_8_25_space`, `Brezis.Chapter08.remark_8_25_existsUnique`,
  `Brezis.Chapter08.remark_8_25_regularity`, `Brezis.Chapter08.remark_8_25_boundary` and
  `Brezis.Chapter08.remark_8_25`: on $(0, +\infty)$, $H_0^1 = \{u \in H^1 : u(0) = 0\}$, and
  $-u'' + u = f$, $u(0) = 0$, $u(x) \to 0$ as $x \to +\infty$ has a unique weak solution, which lies
  in $H^2(0, +\infty)$.

## Conventions

* $H^1(0, 1)$ is `SobolevInterval 1 0 1`, which is `SobolevIntervalLp 1 2 (Opens.Ioo 0 1)` of
  Section 8.2. $H_0^1(0, 1)$ is `SobolevIntervalZero 0 1`, which is
  `Brezis.Chapter08.H10 (Opens.Ioo 0 1)` of Section 8.3. $H^2(0, 1)$ is `SobolevInterval 2 0 1`, and
  $C^2(\bar I)$ is `ContDiffMapIcc zero_le_one 2`.
* For $u \in H^1$, the value $u(x)$ is the value of the continuous representative,
  `SobolevInterval.rep u x`.
* The bilinear form $a(u, v) = \int u'v' + \int uv$ is `EllipticInterval.modelForm 0 1`, and the
  linear functional $v \mapsto \int fv$ is `EllipticInterval.load 0 1 f`. The form
  $\int pu'v' + \int ru'v + \int quv$ of Example 2 is `EllipticInterval.form 0 1 p r q`, with the
  coefficients in $L^\infty(0, 1)$.
* "$u \in H^2(I)$ satisfies $-u'' + u = f$" is `Φ : SobolevInterval 2 0 1` with
  `(SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo 0 1)] fun x ↦ SobolevInterval.fn Φ
  x - f x`. The function $u$ in $H^1$ is `SobolevInterval.inclusionCLM 1 0 1 Φ`, and $u'(0)$ is
  `SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0`.
* The energy $\frac12 a(v, v) - \ell(v)$ of a form $a$ and a load $\ell$ is `SesqForm.energy`.
* $H^1(\mathbb{R})$ is `SobolevIntervalLp 1 2 ⊤`, and $H_0^1(0, +\infty)$ is
  `SobolevIntervalLpZero 1 2 (Opens.Ioi 0)`.

## Deviations from the source

* **Example 2, existence, uniqueness and minimization** (generalization). The source assumes
  $p \in C^1(\bar I)$ and $q \in C(\bar I)$. Existence, uniqueness and the minimization need only
  $p, q \in L^\infty(I)$ with $p \ge \alpha > 0$ and $q \ge 0$. See
  `Brezis.Chapter08.example_8_2_existsUnique` and `Brezis.Chapter08.example_8_2_min`.
* **Example 2, problem (20)** (generalization). The source takes $p \in C^1(\bar I)$ and
  $q, r \in C(\bar I)$. The coefficients here are in $L^\infty(I)$, with the bounds almost
  everywhere. See `Brezis.Chapter08.example_8_2_general`.

## Not formalized

* **Footnotes 14 and 15 of Example 6.** The general boundary condition of the third type, and the
  Robin problem for small negative $k$.
-/

open Filter MeasureTheory Set TopologicalSpace EllipticInterval
open scoped Distributions ENNReal InnerProductSpace Topology

noncomputable section

namespace Brezis.Chapter08

/-! ### The definitions -/

/-- **Section 8.4** of [brezis2011functional], definition of a classical solution of (14). Let
$f : \mathbb{R} \to \mathbb{R}$. A function $u \in C^2([0, 1])$ is a **classical solution** of
problem (14) if
$$-u'' + u = f \text{ on } [0, 1], \qquad u(0) = u(1) = 0.$$

This is `Brezis.Chapter08.IsClassicalSolution` of Section 8.1 on the interval $[0, 1]$. -/
abbrev IsClassicalSolutionDirichlet (f : ℝ → ℝ) (u : ContDiffMapIcc (zero_lt_one' ℝ).le 2) :
    Prop :=
  IsClassicalSolution (zero_lt_one' ℝ) f u

/-- **Section 8.4** of [brezis2011functional], definition of a weak solution of (14). Let
$I = (0, 1)$ and $f \in L^2(I)$. A function $u \in H^1(I)$ is a **weak solution** of (14) if
$u \in H_0^1(I)$ and (15) holds:
$$\int_I u'v' + \int_I uv = \int_I fv \quad \text{for all } v \in H_0^1(I).$$

The definition is the Galerkin problem `IsGalerkinSolution` of the form
`EllipticInterval.modelForm 0 1` and the load `EllipticInterval.load 0 1 f` on the subspace
`SobolevIntervalZero 0 1`. `Brezis.Chapter08.isWeakSolutionDirichlet_iff` unfolds it to (15). -/
def IsWeakSolutionDirichlet (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (u : SobolevInterval 1 0 1) : Prop :=
  IsGalerkinSolution (modelForm 0 1) (load 0 1 f) (SobolevIntervalZero 0 1) u

/-- The product of two $L^2$ functions is integrable. -/
private theorem integrable_mul_L2 {μ : Measure ℝ} (f g : Lp ℝ 2 μ) :
    Integrable (fun x ↦ f x * g x) μ :=
  (L2.integrable_inner (𝕜 := ℝ) f g).congr (Eventually.of_forall fun x ↦ by
    simp [RCLike.inner_apply, mul_comm])

/-- **Section 8.4** of [brezis2011functional], the weak formulation (15). Let $f \in L^2(0, 1)$ and
$u \in H^1(0, 1)$. Then $u$ is a weak solution of (14) if and only if $u \in H_0^1(0, 1)$ and
$$\int_0^1 u'v' + \int_0^1 uv = \int_0^1 fv \quad \text{for all } v \in H_0^1(0, 1).$$
-/
theorem isWeakSolutionDirichlet_iff (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (u : SobolevInterval 1 0 1) :
    IsWeakSolutionDirichlet f u ↔ u ∈ SobolevIntervalZero 0 1 ∧ ∀ v ∈ SobolevIntervalZero 0 1,
      (∫ x in Ioo (0 : ℝ) 1, SobolevInterval.deriv u 1 x * SobolevInterval.deriv v 1 x)
        + ∫ x in Ioo (0 : ℝ) 1, SobolevInterval.fn u x * SobolevInterval.fn v x
        = ∫ x in Ioo (0 : ℝ) 1, f x * SobolevInterval.fn v x := by
  refine and_congr_right fun _ ↦ forall₂_congr fun v _ ↦ ?_
  rw [modelForm_apply, SobolevInterval.inner_eq_intervalIntegral zero_le_one,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, load_apply]
  have e : ∫ x in Ioo (0 : ℝ) 1, (SobolevInterval.deriv u 1 x * SobolevInterval.deriv v 1 x
      + SobolevInterval.fn u x * SobolevInterval.fn v x)
      = (∫ x in Ioo (0 : ℝ) 1, SobolevInterval.deriv u 1 x * SobolevInterval.deriv v 1 x)
        + ∫ x in Ioo (0 : ℝ) 1, SobolevInterval.fn u x * SobolevInterval.fn v x :=
    integral_add (integrable_mul_L2 _ _) (integrable_mul_L2 (SobolevInterval.deriv u 0) _)
  rw [e]
  rfl

/-! ### Steps A and B -/

/-- **Section 8.4** of [brezis2011functional], Step A. Let $f : \mathbb{R} \to \mathbb{R}$, and let
$f_L \in L^2(0, 1)$ be equal to $f$ almost everywhere on $(0, 1)$. If $u \in C^2([0, 1])$ is a
classical solution of (14), then $u$ is a weak solution of (14) for the datum $f_L$.

The source calls this obvious by integration by parts, as justified in Corollary 8.10. The
element of $H^1(0, 1)$ carried by $u$ is `EllipticInterval.ofContDiffMapIcc zero_lt_one u`. The
proof specializes `EllipticInterval.isWeakSolution_of_classical`. -/
theorem dirichlet_stepA {f : ℝ → ℝ} (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f) (u : ContDiffMapIcc (zero_lt_one' ℝ).le 2)
    (hu : IsClassicalSolutionDirichlet f u) :
    IsWeakSolutionDirichlet fL (ofContDiffMapIcc (zero_lt_one' ℝ) u) := by
  refine isWeakSolution_of_classical (zero_lt_one' ℝ) (α := fun _ ↦ 1) (β := fun _ ↦ 0)
    (γ := fun _ ↦ 1) (constLinf 0 1 1) 0 (constLinf 0 1 1) fL (coeFn_constLinf 0 1 1)
    (Lp.coeFn_zero ℝ ⊤ _) (coeFn_constLinf 0 1 1) hfL contDiffOn_const continuousOn_const
    continuousOn_const u (fun x hx ↦ ?_) ?_ ?_
  · have e : (fun t ↦ (1 : ℝ) * u.shift.extend t) = u.shift.extend := funext fun t ↦ one_mul _
    rw [e, zero_mul, add_zero, one_mul, deriv_shift_extend (zero_lt_one' ℝ) u hx,
      ContDiffMapIcc.extend_of_mem _ (Ioo_subset_Icc_self hx)]
    exact hu.1 ⟨x, Ioo_subset_Icc_self hx⟩
  · rw [ContDiffMapIcc.extend_of_mem _ (left_mem_Icc.2 zero_le_one)]
    exact hu.2.1
  · rw [ContDiffMapIcc.extend_of_mem _ (right_mem_Icc.2 zero_le_one)]
    exact hu.2.2

/-- The constant coefficient $1$, as an element of $L^\infty(0, 1)$, is at least $1$ almost
everywhere. -/
private theorem one_le_constLinf_ae :
    ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 1 ≤ constLinf 0 1 1 x :=
  (coeFn_constLinf 0 1 1).mono fun x hx ↦ by rw [hx]

/-- **Proposition 8.15** of [brezis2011functional]. This is Step B of the variational method for
(14). Let $I = (0, 1)$. For every $f \in L^2(I)$ there is a unique weak solution
$u \in H_0^1(I)$ of (14), that is, a unique $u$ that satisfies (15).

The source applies the Lax–Milgram theorem in the Hilbert space $H_0^1(I)$ to the bilinear form
$a(u, v) = \int u'v' + \int uv$, which is the scalar product of $H^1$, and to the functional
$v \mapsto \int fv$. The proof specializes `EllipticInterval.existsUnique_isWeakSolution` with
both coefficients equal to $1$. -/
theorem proposition_8_15 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! u, IsWeakSolutionDirichlet f u :=
  existsUnique_isWeakSolution (zero_lt_one' ℝ) (constLinf 0 1 1) (constLinf 0 1 1) one_pos
    one_le_constLinf_ae (one_le_constLinf_ae.mono fun _ hx ↦ zero_le_one.trans hx) f

/-- **Proposition 8.15** of [brezis2011functional], the energy. Let $f \in L^2(0, 1)$ and
$v \in H^1(0, 1)$. The energy (`SesqForm.energy`) of the form $a(u, v) = \int u'v' + \int uv$
and the load $v \mapsto \int fv$, at $v$, is the functional of the source:
$$\frac12 \int_0^1 (v'^2 + v^2) - \int_0^1 fv.$$
-/
theorem energy_dirichlet_eq (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (v : SobolevInterval 1 0 1) :
    (modelForm 0 1).energy (load 0 1 f) v
      = (1 / 2 : ℝ) * (∫ x in Ioo (0 : ℝ) 1,
          (SobolevInterval.deriv v 1 x ^ 2 + SobolevInterval.fn v x ^ 2))
        - ∫ x in Ioo (0 : ℝ) 1, f x * SobolevInterval.fn v x := by
  rw [SesqForm.energy, RCLike.re_to_real, RCLike.re_to_real, modelForm_apply,
    SobolevInterval.inner_eq_intervalIntegral zero_le_one,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, load_apply]
  congr 2
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [sq])

/-- **Proposition 8.15** of [brezis2011functional], Dirichlet's principle. Let $I = (0, 1)$,
$f \in L^2(I)$ and $u \in H_0^1(I)$. Then $u$ is a weak solution of (14) if and only if $u$
minimizes
$$\frac12 \int_I (v'^2 + v^2) - \int_I fv$$
over $v \in H_0^1(I)$.

The functional is `SesqForm.energy` of `EllipticInterval.modelForm 0 1` (see
`Brezis.Chapter08.energy_dirichlet_eq`). The proof uses `SesqForm.isMinOn_energy_iff`, since the
form is symmetric and coercive. -/
theorem proposition_8_15_dirichletPrinciple (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {u : SobolevInterval 1 0 1} (hu : u ∈ SobolevIntervalZero 0 1) :
    IsWeakSolutionDirichlet f u ↔
      IsMinOn ((modelForm 0 1).energy (load 0 1 f)) (SobolevIntervalZero 0 1) u :=
  ⟨fun h ↦ (SesqForm.isMinOn_energy_iff (load 0 1 f) modelForm_isHermitian one_pos
    modelForm_isCoerciveWith _ hu).2 h.2, fun h ↦ ⟨hu, (SesqForm.isMinOn_energy_iff (load 0 1 f)
    modelForm_isHermitian one_pos modelForm_isCoerciveWith _ hu).1 h⟩⟩

/-- **Remark 22** in Chapter 8 of [brezis2011functional]. Let $I = (0, 1)$ and $F \in H^{-1}(I)$.
There is a unique $u \in H_0^1(I)$ with
$$(u, v)_{H^1} = \langle F, v \rangle \quad \text{for all } v \in H_0^1(I).$$

The space $H^{-1}(I)$ is `Brezis.Chapter08.Hneg1`, the dual of $H_0^1(I)$, which is
`Brezis.Chapter08.H10`. The map $F \mapsto u$ is the inverse of the Riesz–Fréchet isomorphism
`InnerProductSpace.toDual` of $H_0^1(I)$ onto $H^{-1}(I)$. -/
theorem remark_8_22 (F : Hneg1 (Opens.Ioo 0 1)) :
    ∃! u : H10 (Opens.Ioo 0 1), ∀ v : H10 (Opens.Ioo 0 1), ⟪u, v⟫_ℝ = F v :=
  ⟨(InnerProductSpace.toDual ℝ (H10 (Opens.Ioo 0 1))).symm F,
    fun v ↦ InnerProductSpace.toDual_symm_apply, fun w hw ↦ by
      refine ext_inner_right ℝ fun v ↦ ?_
      rw [hw v, InnerProductSpace.toDual_symm_apply]⟩

/-- **Remark 22** in Chapter 8 of [brezis2011functional], the identification with the weak solution.
Let $I = (0, 1)$ and $f \in L^2(I)$, and let $u \in H_0^1(I)$ satisfy
$$(u, v)_{H^1} = \int_I fv \quad \text{for all } v \in H_0^1(I).$$
Then $u$ is the weak solution of (14), in the sense of (15).

This is Remark 22 for the functional $F = (v \mapsto \int fv)$, which is the image of $f$ under
the inclusion $L^2 \subset H^{-1}$ of Section 8.3 (`SobolevIntervalLpDual.ofL2`, whose values
are these integrals by `SobolevIntervalLpDual.ofL2_apply`). The source says that the function
$u$ coincides with the weak solution of (14). -/
theorem remark_8_22_eq_weakSolution (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (u : H10 (Opens.Ioo 0 1))
    (hu : ∀ v : H10 (Opens.Ioo 0 1),
      ⟪u, v⟫_ℝ = ∫ x in Ioo (0 : ℝ) 1, f x * SobolevInterval.fn (v : SobolevInterval 1 0 1) x) :
    IsWeakSolutionDirichlet f u :=
  ⟨u.2, fun v hv ↦ by
    have := hu ⟨v, hv⟩
    rw [Submodule.coe_inner] at this
    rw [modelForm_apply, load_apply]
    exact this⟩

/-! ### Steps C and D -/

/-- **Section 8.4** of [brezis2011functional], Steps C and D, the $H^2$ regularity. Let
$f \in L^2(0, 1)$ and let $u$ be a weak solution of (14). Then $u$ belongs to $H^2(0, 1)$: there
is $\Phi \in H^2(0, 1)$ whose image in $H^1(0, 1)$ is $u$, with
$$\Phi'' = \Phi - f \quad \text{a.e. on } (0, 1).$$

In the source, $\int u'v' = \int (f - u)v$ for all test functions $v$, so $u' \in H^1$. The
image of $\Phi$ in $H^1$ is `SobolevInterval.inclusionCLM 1 0 1 Φ`. The proof specializes
`EllipticInterval.exists_sobolevInterval_two_of_forall_modelForm`. -/
theorem dirichlet_stepC (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {u : SobolevInterval 1 0 1} (hu : IsWeakSolutionDirichlet f u) :
    MemSobolevInterval (SobolevInterval.fn u) 2 0 1 ∧
      ∃ Φ : SobolevInterval 2 0 1, SobolevInterval.inclusionCLM 1 0 1 Φ = u ∧
        (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
          fun x ↦ SobolevInterval.fn Φ x - f x := by
  obtain ⟨Φ, hΦ, hΦ2⟩ := exists_sobolevInterval_two_of_forall_modelForm f hu.2
  refine ⟨?_, Φ, hΦ, hΦ2⟩
  have := SobolevIntervalLp.memSobolevIntervalLp_fn Φ
  rw [← SobolevInterval.fn_inclusionCLM Φ, hΦ] at this
  exact this

/-- **Section 8.4** of [brezis2011functional], Steps C and D, the classical solution. Let
$f : \mathbb{R} \to \mathbb{R}$ be continuous on $[0, 1]$, let $f_L \in L^2(0, 1)$ be equal to
$f$ almost everywhere on $(0, 1)$, and let $u$ be a weak solution of (14) for the datum $f_L$.
Then there is $v \in C^2([0, 1])$ such that $u$ is the element of $H^1(0, 1)$ carried by $v$ and
$v$ is a classical solution of (14).

In the source, $(u')' = u - f \in C(\bar I)$, so $u' \in C^1(\bar I)$ by Remark 6, and Step D of
Section 8.1 gives the classical solution. The proof uses
`EllipticInterval.exists_contDiffMapIcc_of_deriv_two`, the endpoint values from $u \in H_0^1$,
and the equation at the endpoints by continuity. -/
theorem dirichlet_stepCD {f : ℝ → ℝ} (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f) (hf : ContinuousOn f (Icc 0 1))
    {u : SobolevInterval 1 0 1} (hu : IsWeakSolutionDirichlet fL u) :
    ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2,
      ofContDiffMapIcc (zero_lt_one' ℝ) v = u ∧ IsClassicalSolutionDirichlet f v := by
  obtain ⟨-, Φ, hΦ, hΦ2⟩ := dirichlet_stepC fL hu
  obtain ⟨v, hv, hode⟩ := exists_contDiffMapIcc_of_deriv_two (zero_lt_one' ℝ) fL hfL hf hΦ2
  rw [hΦ] at hv
  have hrep : ∀ x ∈ Icc (0 : ℝ) 1, v.extend x = SobolevInterval.rep u x := fun x hx ↦ by
    rw [← hv]; exact (rep_ofContDiffMapIcc (zero_lt_one' ℝ) v hx).symm
  refine ⟨v, hv, fun x ↦ ?_, ?_, ?_⟩
  · -- the equation on `(0, 1)`, extended to the endpoints by continuity
    have hae : (fun t ↦ -v.shift.shift.extend t + v.extend t)
        =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f := by
      refine (ae_restrict_mem measurableSet_Ioo).mono fun t ht ↦ ?_
      change -v.shift.shift.extend t + v.extend t = f t
      have := hode t ht
      rw [deriv_shift_extend (zero_lt_one' ℝ) v ht] at this
      rw [ContDiffMapIcc.extend_of_mem _ (Ioo_subset_Icc_self ht)]
      exact this
    have hEq := eqOn_Icc_of_ae_eq (zero_lt_one' ℝ)
      (v.shift.shift.extend.continuous.neg.add v.extend.continuous).continuousOn hf hae x.2
    change -v.shift.shift.extend x + v.extend x = f x at hEq
    rw [ContDiffMapIcc.extend_val, ContDiffMapIcc.extend_val] at hEq
    exact hEq
  · rw [← ContDiffMapIcc.extend_val, hrep 0 (left_mem_Icc.2 zero_le_one)]
    exact SobolevIntervalZero.rep_left_eq_zero (zero_lt_one' ℝ) hu.1
  · rw [← ContDiffMapIcc.extend_val, hrep 1 (right_mem_Icc.2 zero_le_one)]
    exact SobolevIntervalZero.rep_right_eq_zero (zero_lt_one' ℝ) hu.1

/-- **Remark 23** in Chapter 8 of [brezis2011functional]. Let $I = (0, 1)$, $f \in L^2(I)$, let $u$
be a weak solution of (14), and let $k \ge 1$. If $f \in H^k(I)$, then $u \in H^{k+2}(I)$.

The source argues by induction on $k$, and the case $k = 0$ is Step C. The proof specializes
`EllipticInterval.memSobolevInterval_add_two_of_isWeakSolution`. -/
theorem remark_8_23 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {u : SobolevInterval 1 0 1}
    (hu : IsWeakSolutionDirichlet f u) {k : ℕ} (_hk : 1 ≤ k) (hf : MemSobolevInterval f k 0 1) :
    MemSobolevInterval (SobolevInterval.fn u) (k + 2) 0 1 :=
  memSobolevInterval_add_two_of_isWeakSolution f hu.2 hf

/-! ### Example 1: the inhomogeneous Dirichlet condition -/

/-- **Proposition 8.16** of [brezis2011functional]. This is Example 1 of Section 8.4, the
inhomogeneous Dirichlet condition. Let $I = (0, 1)$, $\alpha, \beta \in \mathbb{R}$ and
$f \in L^2(I)$. There is a unique $u \in H^2(I)$ that satisfies (16):
$$-u'' + u = f \text{ a.e. on } I, \qquad u(0) = \alpha, \quad u(1) = \beta.$$

The proof specializes `EllipticInterval.existsUnique_dirichlet_inhomogeneous`, which follows
Method 2 (Stampacchia). -/
theorem proposition_8_16 (α β : ℝ) (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! Φ : SobolevInterval 2 0 1,
      ((SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun x ↦ SobolevInterval.fn Φ x - f x) ∧
      SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 = α ∧
      SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 = β :=
  existsUnique_dirichlet_inhomogeneous (zero_lt_one' ℝ) f α β

/-- **Proposition 8.16** of [brezis2011functional], the minimization. Let $I = (0, 1)$,
$\alpha, \beta \in \mathbb{R}$ and $f \in L^2(I)$, and let $u \in H^2(I)$ satisfy (16). Then $u$
minimizes
$$\frac12 \int_I (v'^2 + v^2) - \int_I fv$$
over the closed convex set $K = \{v \in H^1(I) : v(0) = \alpha, v(1) = \beta\}$.

The set $K$ is `EllipticInterval.dirichletSet 0 1 α β`. The proof shows the variational
inequality (17) of Stampacchia, which $u$ satisfies because the boundary terms of Green's
formula vanish against $v - u \in H_0^1$. -/
theorem proposition_8_16_min (α β : ℝ) (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 = α)
    (h1 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 = β) :
    IsMinOn ((modelForm 0 1).energy (load 0 1 f)) (dirichletSet 0 1 α β)
      (SobolevInterval.inclusionCLM 1 0 1 Φ) := by
  have hK : SobolevInterval.inclusionCLM 1 0 1 Φ ∈ dirichletSet 0 1 α β := ⟨h0, h1⟩
  refine (dirichletSet_isMinOn_energy_iff (zero_lt_one' ℝ) f hK).2 fun v hv ↦ ?_
  have hmem : v - SobolevInterval.inclusionCLM 1 0 1 Φ ∈ SobolevIntervalZero 0 1 := by
    rw [mem_dirichletSet_iff_sub_mem (zero_lt_one' ℝ)] at hv hK
    have := (SobolevIntervalZero 0 1).sub_mem hv hK
    rwa [sub_sub_sub_cancel_right] at this
  exact (modelForm_inclusionCLM_eq_load_of_mem (zero_lt_one' ℝ) f hΦ hmem).ge

/-- **Proposition 8.16** of [brezis2011functional], the classical solution. Let
$f : \mathbb{R} \to \mathbb{R}$ be continuous on $[0, 1]$, let $f_L \in L^2(0, 1)$ be equal to
$f$ almost everywhere on $(0, 1)$, and let $u \in H^2(0, 1)$ satisfy $u'' = u - f_L$ almost
everywhere on $(0, 1)$. Then there is $v \in C^2([0, 1])$ such that $u$ is the element of
$H^1(0, 1)$ carried by $v$ and
$$-v'' + v = f \text{ on } (0, 1).$$

This is the statement of the source that $u \in C^2(\bar I)$ if in addition $f \in C(\bar I)$.
The boundary conditions play no role. Here $v''$ is the derivative of the extension of $v'$ to
$\mathbb{R}$ (`ContDiffMapIcc.shift` and `ContDiffMapIcc.extend`). The proof specializes
`EllipticInterval.exists_contDiffMapIcc_of_deriv_two`. -/
theorem proposition_8_16_C2 {f : ℝ → ℝ} (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f) (hf : ContinuousOn f (Icc 0 1))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - fL x) :
    ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2,
      ofContDiffMapIcc (zero_lt_one' ℝ) v = SobolevInterval.inclusionCLM 1 0 1 Φ ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, -deriv v.shift.extend x + v.extend x = f x :=
  exists_contDiffMapIcc_of_deriv_two (zero_lt_one' ℝ) fL hfL hf hΦ

/-- **Proposition 8.16** of [brezis2011functional], Method 1. Let $I = (0, 1)$,
$\alpha, \beta \in \mathbb{R}$ and $f \in L^2(I)$, let $u \in H^2(I)$ satisfy (16), and let
$u_0(x) = \alpha + (\beta - \alpha)x$ be the affine function with $u_0(0) = \alpha$ and
$u_0(1) = \beta$. Then $u - u_0$ is the weak solution of (14) with the datum $f - u_0$.

The source writes the new datum as $f + u_0'' - u_0$, which is $f - u_0$ because $u_0$ is
affine. The function $u_0$ is `EllipticInterval.affineLift`. -/
theorem proposition_8_16_method1 (α β : ℝ) (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 = α)
    (h1 : SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 = β) :
    IsWeakSolutionDirichlet (f - SobolevInterval.deriv (affineLift (zero_lt_one' ℝ) 2 α β) 0)
      (SobolevInterval.inclusionCLM 1 0 1 Φ - affineLift (zero_lt_one' ℝ) 1 α β) := by
  have hK : SobolevInterval.inclusionCLM 1 0 1 Φ ∈ dirichletSet 0 1 α β := ⟨h0, h1⟩
  refine ⟨(mem_dirichletSet_iff_sub_mem (zero_lt_one' ℝ) α β _).1 hK, fun v hv ↦ ?_⟩
  -- the affine lift solves the model equation with datum `u₀` (its second derivative is `0`)
  have hu₀ : (SobolevInterval.deriv (affineLift (zero_lt_one' ℝ) 2 α β) 2 : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun x ↦
        SobolevInterval.fn (affineLift (zero_lt_one' ℝ) 2 α β) x
          - SobolevInterval.deriv (affineLift (zero_lt_one' ℝ) 2 α β) 0 x := by
    rw [deriv_affineLift_two]
    refine (Lp.coeFn_zero ℝ 2 _).trans (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.zero_apply, SobolevInterval.deriv_zero, sub_self]
  rw [form_sub_eq_of_forall _ _ _ f (fun w hw ↦ modelForm_inclusionCLM_eq_load_of_mem
    (zero_lt_one' ℝ) f hΦ hw) _ hv, ← inclusionCLM_affineLift (zero_lt_one' ℝ) α β,
    modelForm_inclusionCLM_eq_load_of_mem (zero_lt_one' ℝ) _ hu₀ hv, load_apply, load_apply,
    load_apply]
  have e : (fun x ↦ (f - SobolevInterval.deriv (affineLift (zero_lt_one' ℝ) 2 α β) 0) x
      * SobolevInterval.deriv v 0 x) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ f x * SobolevInterval.deriv v 0 x
        - SobolevInterval.deriv (affineLift (zero_lt_one' ℝ) 2 α β) 0 x
          * SobolevInterval.deriv v 0 x :=
    (Lp.coeFn_sub f (SobolevInterval.deriv (affineLift (zero_lt_one' ℝ) 2 α β) 0)).mono
      fun x hx ↦ by simp only [hx, Pi.sub_apply, sub_mul]
  rw [integral_congr_ae e, integral_sub (integrable_mul_L2 f (SobolevInterval.deriv v 0))
    (integrable_mul_L2 (SobolevInterval.deriv (affineLift (zero_lt_one' ℝ) 2 α β) 0)
      (SobolevInterval.deriv v 0))]

/-- **Proposition 8.16** of [brezis2011functional], Method 2 (Stampacchia). Let $I = (0, 1)$,
$\alpha, \beta \in \mathbb{R}$ and $f \in L^2(I)$, and let $K = \{v \in H^1(I) : v(0) = \alpha,
v(1) = \beta\}$. There is exactly one $u \in H^1(I)$ with the following four properties:
* $u \in K$;
* $u$ satisfies the variational inequality (17), $\int_I u'(v - u)' + \int_I u(v - u) \ge \int_I
  f(v - u)$ for all $v \in K$;
* $u$ minimizes $\frac12 \int_I (v'^2 + v^2) - \int_I fv$ over $K$;
* $u$ satisfies the weak equation $\int_I u'w' + \int_I uw = \int_I fw$ for all
  $w \in H_0^1(I)$.

The weak equation follows from (17) with $v = u \pm w$. The proof combines
`EllipticInterval.existsUnique_dirichletSet_of_variationalInequality`,
`EllipticInterval.dirichletSet_isMinOn_energy_iff` and
`EllipticInterval.forall_modelForm_eq_load_of_variationalInequality`. -/
theorem proposition_8_16_method2 (α β : ℝ) (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! u, u ∈ dirichletSet 0 1 α β ∧
      (∀ v ∈ dirichletSet 0 1 α β, load 0 1 f (v - u) ≤ modelForm 0 1 u (v - u)) ∧
      IsMinOn ((modelForm 0 1).energy (load 0 1 f)) (dirichletSet 0 1 α β) u ∧
      ∀ w ∈ SobolevIntervalZero 0 1, modelForm 0 1 u w = load 0 1 f w := by
  obtain ⟨u, ⟨huK, hvi⟩, huniq⟩ := existsUnique_dirichletSet_of_variationalInequality
    (zero_lt_one' ℝ) f α β
  refine ⟨u, ⟨huK, hvi, (dirichletSet_isMinOn_energy_iff (zero_lt_one' ℝ) f huK).2 hvi,
    forall_modelForm_eq_load_of_variationalInequality (zero_lt_one' ℝ) f huK hvi⟩,
    fun w hw ↦ huniq w ⟨hw.1, hw.2.1⟩⟩

/-! ### Example 2: the Sturm–Liouville problem -/

section SturmLiouville

variable {p q r : ℝ → ℝ} {α₀ : ℝ}
  {pL rL qL : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))}

/-- A coefficient that is at least $c$ on $[0, 1]$ is at least $c$ almost everywhere on $(0, 1)$, in
any representative in $L^\infty(0, 1)$. -/
private theorem ae_le_of_forall_Icc {g : ℝ → ℝ} {gL : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))}
    (hgL : gL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g) {c : ℝ} (hg : ∀ x ∈ Icc (0 : ℝ) 1, c ≤ g x) :
    ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), c ≤ gL x := by
  filter_upwards [hgL, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  rw [hx]
  exact hg x (Ioo_subset_Icc_self hxI)

/-- **Example 2** in Section 8.4 of [brezis2011functional] (Sturm–Liouville problem), existence and
uniqueness. Let $I = (0, 1)$ and $\alpha > 0$. Let $p, q : \mathbb{R} \to \mathbb{R}$ satisfy
$p \ge \alpha$ and $q \ge 0$ on $[0, 1]$, and let $p_L, q_L \in L^\infty(I)$ be equal to $p$ and
$q$ almost everywhere on $I$. For every $f \in L^2(I)$ there is a unique $u \in H_0^1(I)$ with
$$\int_I pu'v' + \int_I quv = \int_I fv \quad \text{for all } v \in H_0^1(I).$$

**Generalization.** The source assumes $p \in C^1(\bar I)$ and $q \in C(\bar I)$. Existence and
uniqueness need only the bounds $p \ge \alpha$ and $q \ge 0$, with $p$ and $q$ bounded.

The weak problem is the Galerkin problem of the symmetric form
$a(u, v) = \int pu'v' + \int quv$, `EllipticInterval.form 0 1 pL 0 qL`, which is coercive on
$H_0^1$ by Poincaré's inequality. The proof is the Lax–Milgram theorem,
`EllipticInterval.existsUnique_isWeakSolution`. -/
theorem example_8_2_existsUnique (hα₀ : 0 < α₀)
    (hpL : pL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] p) (hpα : ∀ x ∈ Icc (0 : ℝ) 1, α₀ ≤ p x)
    (hqL : qL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] q) (hq0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ q x)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! u, IsGalerkinSolution (form 0 1 pL 0 qL) (load 0 1 f) (SobolevIntervalZero 0 1) u :=
  existsUnique_isWeakSolution (zero_lt_one' ℝ) pL qL hα₀ (ae_le_of_forall_Icc hpL hpα)
    (ae_le_of_forall_Icc hqL hq0) f

/-- The Sturm–Liouville form $\int pu'v' + \int quv$ is symmetric. -/
private theorem form_isHermitian_of_symm : (form 0 1 pL 0 qL).IsHermitian := fun u v ↦ by
  rw [form_comm, RCLike.conj_to_real]

/-- **Example 2** in Section 8.4 of [brezis2011functional], the minimization. Let $I = (0, 1)$,
$\alpha > 0$, and let $p, q, p_L, q_L$ be as in `Brezis.Chapter08.example_8_2_existsUnique`:
$p \ge \alpha$ and $q \ge 0$ on $[0, 1]$. Let $f \in L^2(I)$, and let $u \in H_0^1(I)$ satisfy
$\int_I pu'v' + \int_I quv = \int_I fv$ for all $v \in H_0^1(I)$. Then $u$ minimizes
$$\frac12 \int_I (pv'^2 + qv^2) - \int_I fv$$
over $v \in H_0^1(I)$.

**Generalization.** The source assumes $p \in C^1(\bar I)$ and $q \in C(\bar I)$. The statement
needs only the bounds on $p$ and $q$.

The functional is the energy of the restriction of the form to $H_0^1(I)$. The form is symmetric
(`EllipticInterval.form_comm`) and coercive on $H_0^1(I)$. -/
theorem example_8_2_min (hα₀ : 0 < α₀)
    (hpL : pL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] p) (hpα : ∀ x ∈ Icc (0 : ℝ) 1, α₀ ≤ p x)
    (hqL : qL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] q) (hq0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ q x)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {u : SobolevInterval 1 0 1}
    (hu : IsGalerkinSolution (form 0 1 pL 0 qL) (load 0 1 f) (SobolevIntervalZero 0 1) u) :
    IsMinOn (((form 0 1 pL 0 qL).restrict (SobolevIntervalZero 0 1)).energy
      ((load 0 1 f).comp (SobolevIntervalZero 0 1).subtypeL)) univ ⟨u, hu.1⟩ := by
  have hc : 0 < α₀ / (1 + ((1 : ℝ) - 0) ^ 2 / 2) := by positivity
  have := (SesqForm.isMinOn_energy_iff ((load 0 1 f).comp (SobolevIntervalZero 0 1).subtypeL)
    (form_isHermitian_of_symm.restrict _) hc
    (form_isCoerciveWith_restrict (zero_lt_one' ℝ) pL qL (ae_le_of_forall_Icc hpL hpα)
      (ae_le_of_forall_Icc hqL hq0) hα₀.le) ⊤ (u := ⟨u, hu.1⟩) Submodule.mem_top).2
    fun v _ ↦ by rw [SesqForm.restrict_apply]; exact hu.2 v v.2
  rwa [Submodule.top_coe] at this

/-- **Example 2** in Section 8.4 of [brezis2011functional], $H^2$ regularity. Let $I = (0, 1)$ and
$\alpha > 0$, let $p \in C^1([0, 1])$ satisfy $p \ge \alpha$ on $[0, 1]$, let
$p_L \in L^\infty(I)$ be equal to $p$ almost everywhere on $I$, and let $q_L \in L^\infty(I)$.
Let $f \in L^2(I)$. If $u \in H_0^1(I)$ satisfies (19),
$\int_I pu'v' + \int_I q_L uv = \int_I fv$ for all $v \in H_0^1(I)$, then $u \in H^2(I)$.

In the source, (19) shows that $pu' \in H^1$, so $u' = (1/p)(pu') \in H^1$ by Corollary 8.10. No
sign condition on $q$ is used. The proof specializes
`EllipticInterval.isWeakSolution_mem_sobolevInterval_two`. -/
theorem example_8_2_H2 (hα₀ : 0 < α₀) (hpL : pL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] p)
    (hp : ContDiffOn ℝ 1 p (Icc 0 1)) (hpα : ∀ x ∈ Icc (0 : ℝ) 1, α₀ ≤ p x)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) {u : SobolevInterval 1 0 1}
    (hu : IsGalerkinSolution (form 0 1 pL 0 qL) (load 0 1 f) (SobolevIntervalZero 0 1) u) :
    MemSobolevInterval (SobolevInterval.fn u) 2 0 1 :=
  isWeakSolution_mem_sobolevInterval_two (zero_lt_one' ℝ) pL 0 qL hpL hp
    (fun x hx ↦ (hα₀.trans_le (hpα x hx)).ne') f hu

/-- **Example 2** in Section 8.4 of [brezis2011functional], the classical solution. Let $I = (0, 1)$
and $\alpha > 0$. Let $p \in C^1([0, 1])$ satisfy $p \ge \alpha$ on $[0, 1]$, let $q$ and $f$ be
continuous on $[0, 1]$, and let $p_L, q_L \in L^\infty(I)$ and $f_L \in L^2(I)$ be equal to $p$,
$q$ and $f$ almost everywhere on $I$. If $u \in H_0^1(I)$ satisfies
$\int_I pu'v' + \int_I quv = \int_I f_L v$ for all $v \in H_0^1(I)$, then there is
$v \in C^2([0, 1])$ that carries $u$, with
$$-(pv')' + qv = f \text{ on } (0, 1), \qquad v(0) = v(1) = 0.$$
So $v$ is a classical solution of the Sturm–Liouville problem (18).

In the source, $pu' \in C^1(\bar I)$, so $u \in C^2(\bar I)$, and Step D carries over. The proof
specializes `EllipticInterval.exists_contDiffMapIcc_of_continuous`. -/
theorem example_8_2_C2 {f : ℝ → ℝ} (hpL : pL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] p)
    (hp : ContDiffOn ℝ 1 p (Icc 0 1)) (hpα : ∀ x ∈ Icc (0 : ℝ) 1, α₀ ≤ p x) (hα₀ : 0 < α₀)
    (hqL : qL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] q) (hq : ContinuousOn q (Icc 0 1))
    (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f) (hf : ContinuousOn f (Icc 0 1))
    {u : SobolevInterval 1 0 1}
    (hu : IsGalerkinSolution (form 0 1 pL 0 qL) (load 0 1 fL) (SobolevIntervalZero 0 1) u) :
    ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2, ofContDiffMapIcc (zero_lt_one' ℝ) v = u ∧
      (∀ x ∈ Ioo (0 : ℝ) 1,
        -deriv (fun t ↦ p t * v.shift.extend t) x + q x * v.extend x = f x) ∧
      v.extend 0 = 0 ∧ v.extend 1 = 0 := by
  obtain ⟨v, hv, hode⟩ := exists_contDiffMapIcc_of_continuous (zero_lt_one' ℝ) pL 0 qL fL
    (β := fun _ ↦ 0) hpL (Lp.coeFn_zero ℝ ⊤ _) hqL hfL hp (fun x hx ↦ (hα₀.trans_le (hpα x hx)).ne')
    continuousOn_const hq hf hu.2
  refine ⟨v, hv, fun x hx ↦ ?_, ?_, ?_⟩
  · have := hode x hx
    rwa [zero_mul, add_zero] at this
  · rw [← rep_ofContDiffMapIcc (zero_lt_one' ℝ) v (left_mem_Icc.2 zero_le_one), hv]
    exact SobolevIntervalZero.rep_left_eq_zero (zero_lt_one' ℝ) hu.1
  · rw [← rep_ofContDiffMapIcc (zero_lt_one' ℝ) v (right_mem_Icc.2 zero_le_one), hv]
    exact SobolevIntervalZero.rep_right_eq_zero (zero_lt_one' ℝ) hu.1

/-- **Example 2** in Section 8.4 of [brezis2011functional] (Sturm–Liouville problem). Let
$I = (0, 1)$ and $\alpha > 0$. Let $p \in C^1([0, 1])$ satisfy $p \ge \alpha$ on $[0, 1]$, let
$q \in C([0, 1])$ satisfy $q \ge 0$ on $[0, 1]$, let $p_L, q_L \in L^\infty(I)$ be equal to $p$
and $q$ almost everywhere on $I$, and let $f \in L^2(I)$. Consider the problem (18),
$-(pu')' + qu = f$ on $I$, $u(0) = u(1) = 0$, with weak solutions $u \in H_0^1(I)$ that satisfy
$\int_I pu'v' + \int_I quv = \int_I fv$ for all $v \in H_0^1(I)$. Then:
* there is a unique weak solution;
* every weak solution lies in $H^2(I)$;
* if $f$ is equal almost everywhere on $I$ to a function $g$ continuous on $[0, 1]$, then every
  weak solution is carried by some $v \in C^2([0, 1])$ with $-(pv')' + qv = g$ on $(0, 1)$ and
  $v(0) = v(1) = 0$. -/
theorem example_8_2 (hα₀ : 0 < α₀)
    (hpL : pL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] p) (hp : ContDiffOn ℝ 1 p (Icc 0 1))
    (hpα : ∀ x ∈ Icc (0 : ℝ) 1, α₀ ≤ p x)
    (hqL : qL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] q) (hq : ContinuousOn q (Icc 0 1))
    (hq0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ q x) (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    (∃! u, IsGalerkinSolution (form 0 1 pL 0 qL) (load 0 1 f) (SobolevIntervalZero 0 1) u) ∧
    (∀ u, IsGalerkinSolution (form 0 1 pL 0 qL) (load 0 1 f) (SobolevIntervalZero 0 1) u →
      MemSobolevInterval (SobolevInterval.fn u) 2 0 1) ∧
    ∀ g : ℝ → ℝ, f =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g → ContinuousOn g (Icc 0 1) →
      ∀ u, IsGalerkinSolution (form 0 1 pL 0 qL) (load 0 1 f) (SobolevIntervalZero 0 1) u →
      ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2, ofContDiffMapIcc (zero_lt_one' ℝ) v = u ∧
        (∀ x ∈ Ioo (0 : ℝ) 1,
          -deriv (fun t ↦ p t * v.shift.extend t) x + q x * v.extend x = g x) ∧
        v.extend 0 = 0 ∧ v.extend 1 = 0 :=
  ⟨example_8_2_existsUnique hα₀ hpL hpα hqL hq0 f,
    fun _ hu ↦ example_8_2_H2 hα₀ hpL hp hpα f hu,
    fun _ hfL hg _ hu ↦ example_8_2_C2 hpL hp hpα hα₀ hqL hq f hfL hg hu⟩

/-! ### The problem (20) with a first-order term -/

/-- If $\gamma \ge \gamma_0$ almost everywhere, then $\langle \gamma g, g \rangle_{L^2} \ge \gamma_0
\|g\|^2$. -/
private theorem inner_mulL_self_ge {γ : Lp ℝ ⊤ (volume.restrict (Ioo (0 : ℝ) 1))} {γ₀ : ℝ}
    (hγ : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), γ₀ ≤ γ x)
    (g : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) : γ₀ * ‖g‖ ^ 2 ≤ ⟪mulL γ g, g⟫_ℝ := by
  rw [inner_mulL_eq_integral, ← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_const_mul]
  refine integral_mono_ae ((L2.integrable_inner (𝕜 := ℝ) g g).const_mul γ₀)
    (integrable_mul_mul _ _ _) ?_
  filter_upwards [hγ] with x hx
  simp only [RCLike.inner_apply, conj_trivial]
  nlinarith [mul_self_nonneg (g x)]

/-- **Example 2** in Section 8.4 of [brezis2011functional], coercivity of the form of (20) in case
(i). Let $I = (0, 1)$ and $\alpha > 0$, and let $p, r, q \in L^\infty(I)$ with $p \ge \alpha$
and $q \ge 1$ almost everywhere on $I$ and $\|r\|_\infty^2 < 4\alpha$. Then the form
$$a(u, v) = \int_I pu'v' + \int_I ru'v + \int_I quv$$
satisfies $a(v, v) \ge c \|v\|_{H^1}^2$ for all $v \in H^1(I)$, with $c = (4\alpha -
\|r\|_\infty^2) / (4(\alpha + 1))$.

The proof bounds $a(v, v) \ge \alpha \|v'\|^2 - \|r\|_\infty \|v'\| \|v\| + \|v\|^2$, a positive
definite quadratic form in $(\|v'\|, \|v\|)$. Here $\|r\|_\infty$ is the norm of `rL` in
$L^\infty(I)$. -/
theorem example_8_2_general_i_coercive (hα₀ : 0 < α₀)
    (hp : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ pL x)
    (hq : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 1 ≤ qL x) (_hr : ‖rL‖ ^ 2 < 4 * α₀) :
    (form 0 1 pL rL qL).IsCoerciveWith ((4 * α₀ - ‖rL‖ ^ 2) / (4 * (α₀ + 1))) := by
  intro v
  rw [RCLike.re_to_real, form_apply_inner, SobolevInterval.norm_sq_eq, Fin.sum_univ_two]
  have hX := inner_mulL_self_ge hp (SobolevInterval.deriv v 1)
  have hY := inner_mulL_self_ge hq (SobolevInterval.deriv v 0)
  have hR := abs_pairing_mulL_le rL 1 0 v v
  rw [pairing_apply, abs_le] at hR
  obtain ⟨c, hc⟩ : ∃ c, c = (4 * α₀ - ‖rL‖ ^ 2) / (4 * (α₀ + 1)) := ⟨_, rfl⟩
  rw [← hc]
  have hR0 := norm_nonneg rL
  have hX0 := norm_nonneg (SobolevInterval.deriv v 1)
  have hY0 := norm_nonneg (SobolevInterval.deriv v 0)
  -- the discriminant of the quadratic form in `(‖v'‖, ‖v‖)`: `4 (α₀ − c)(1 − c) = ‖r‖² + 4c²`
  have hdisc : 4 * c * (α₀ + 1) = 4 * α₀ - ‖rL‖ ^ 2 := by
    rw [hc]; field_simp
  have hcpos : 0 < α₀ - c := by
    have : c < α₀ := by
      rw [hc, div_lt_iff₀ (by positivity)]
      nlinarith [sq_nonneg ‖rL‖]
    linarith
  have key : 4 * (α₀ - c) * ((α₀ - c) * ‖SobolevInterval.deriv v 1‖ ^ 2
      - ‖rL‖ * ‖SobolevInterval.deriv v 1‖ * ‖SobolevInterval.deriv v 0‖
      + (1 - c) * ‖SobolevInterval.deriv v 0‖ ^ 2)
      = (2 * (α₀ - c) * ‖SobolevInterval.deriv v 1‖ - ‖rL‖ * ‖SobolevInterval.deriv v 0‖) ^ 2
        + (4 * c ^ 2) * ‖SobolevInterval.deriv v 0‖ ^ 2 := by
    nlinarith [hdisc]
  have hquad : 0 ≤ (α₀ - c) * ‖SobolevInterval.deriv v 1‖ ^ 2
      - ‖rL‖ * ‖SobolevInterval.deriv v 1‖ * ‖SobolevInterval.deriv v 0‖
      + (1 - c) * ‖SobolevInterval.deriv v 0‖ ^ 2 := by
    have h4 : 0 ≤ 4 * (α₀ - c) * ((α₀ - c) * ‖SobolevInterval.deriv v 1‖ ^ 2
        - ‖rL‖ * ‖SobolevInterval.deriv v 1‖ * ‖SobolevInterval.deriv v 0‖
        + (1 - c) * ‖SobolevInterval.deriv v 0‖ ^ 2) := by
      rw [key]; positivity
    exact nonneg_of_mul_nonneg_right h4 (by positivity) |> fun h ↦ by
      rcases le_or_gt 0 ((α₀ - c) * ‖SobolevInterval.deriv v 1‖ ^ 2
        - ‖rL‖ * ‖SobolevInterval.deriv v 1‖ * ‖SobolevInterval.deriv v 0‖
        + (1 - c) * ‖SobolevInterval.deriv v 0‖ ^ 2) with h' | h'
      · exact h'
      · exact absurd h4 (not_le.2 (mul_neg_of_pos_of_neg (by positivity) h'))
  nlinarith [hX, hY, hR.1, hquad]

/-- **Example 2** in Section 8.4 of [brezis2011functional], problem (20) in case (i). Let
$I = (0, 1)$ and $\alpha > 0$, and let $p, r, q \in L^\infty(I)$ with $p \ge \alpha$ and
$q \ge 1$ almost everywhere on $I$ and $\|r\|_\infty^2 < 4\alpha$. For every $f \in L^2(I)$
there is a unique $u \in H_0^1(I)$ with
$$\int_I pu'v' + \int_I ru'v + \int_I quv = \int_I fv \quad \text{for all } v \in H_0^1(I).$$

The proof is the Lax–Milgram theorem. The source remarks that there is no straightforward
associated minimization problem, because the form is not symmetric. -/
theorem example_8_2_general_i (hα₀ : 0 < α₀)
    (hp : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ pL x)
    (hq : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 1 ≤ qL x) (hr : ‖rL‖ ^ 2 < 4 * α₀)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! u, IsGalerkinSolution (form 0 1 pL rL qL) (load 0 1 f) (SobolevIntervalZero 0 1) u :=
  existsUnique_isGalerkinSolution_of_isClosed (by
      rw [div_pos_iff_of_pos_right (by positivity)]; linarith)
    (example_8_2_general_i_coercive hα₀ hp hq hr) (load 0 1 f) SobolevMultiIndexZero.isClosed

/-- **Example 2** in Section 8.4 of [brezis2011functional], coercivity of the form of (20) in case
(ii). Let $I = (0, 1)$ and $\alpha > 0$, and let $p, q, r_L \in L^\infty(I)$ with $p \ge \alpha$
and $q \ge 1$ almost everywhere on $I$. Let $r_L$ be equal almost everywhere on $I$ to a
function $r \in C^1([0, 1])$ with $r' \le 2$ on $[0, 1]$. Then the form $a(u, v) = \int_I
pu'v' + \int_I r_L u'v + \int_I quv$ satisfies
$$a(v, v) \ge \frac{\alpha}{1 + 1/2} \|v\|_{H^1}^2 \quad \text{for all } v \in H_0^1(I).$$

For $v \in H_0^1$, $\int rv'v = -\frac12 \int r'v^2$
(`EllipticInterval.integral_mul_deriv_mul_rep_eq`), so $a(v, v) \ge \alpha \|v'\|^2$; Poincaré's
inequality on $H_0^1(0, 1)$ then gives the constant. The proof specializes
`EllipticInterval.form_isCoerciveWith_seminorm_of_le`. -/
theorem example_8_2_general_ii_coercive (hα₀ : 0 < α₀)
    (hp : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ pL x)
    (hq : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 1 ≤ qL x)
    (hrL : rL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] r) (hr : ContDiffOn ℝ 1 r (Icc 0 1))
    (hr' : ∀ x ∈ Icc (0 : ℝ) 1, deriv r x ≤ 2) :
    ((form 0 1 pL rL qL).restrict (SobolevIntervalZero 0 1)).IsCoerciveWith
      (α₀ / (1 + ((1 : ℝ) - 0) ^ 2 / 2)) := by
  intro v
  rw [SesqForm.restrict_apply, RCLike.re_to_real, ← Submodule.norm_coe]
  have hcond : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), deriv r x / 2 ≤ qL x := by
    filter_upwards [hq, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    linarith [hr' x (Ioo_subset_Icc_self hxI)]
  have h1 := form_isCoerciveWith_seminorm_of_le (zero_lt_one' ℝ) pL rL qL hp hrL hr hcond v.2
  have h2 := SobolevIntervalZero.norm_le_seminorm (zero_lt_one' ℝ) v.2
  have h3 : 0 ≤ SobolevInterval.seminorm 1 0 1 (v : SobolevInterval 1 0 1) := apply_nonneg _ _
  have h4 : 0 < 1 + ((1 : ℝ) - 0) ^ 2 / 2 := by norm_num
  rw [div_mul_eq_mul_div, div_le_iff₀ h4]
  have h5 : ‖(v : SobolevInterval 1 0 1)‖ ^ 2
      ≤ (1 + ((1 : ℝ) - 0) ^ 2 / 2)
        * SobolevInterval.seminorm 1 0 1 (v : SobolevInterval 1 0 1) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h2 2
    rw [mul_pow, Real.sq_sqrt h4.le] at this
    exact this
  nlinarith [h1, h5]

/-- **Example 2** in Section 8.4 of [brezis2011functional], problem (20) in case (ii). Let
$I = (0, 1)$ and $\alpha > 0$, let $p, q, r_L \in L^\infty(I)$ with $p \ge \alpha$ and $q \ge 1$
almost everywhere on $I$, and let $r_L$ be equal almost everywhere on $I$ to a function
$r \in C^1([0, 1])$ with $r' \le 2$ on $[0, 1]$. For every $f \in L^2(I)$ there is a unique
$u \in H_0^1(I)$ with
$$\int_I pu'v' + \int_I r_L u'v + \int_I quv = \int_I fv \quad \text{for all } v \in H_0^1(I).$$

The proof is the Lax–Milgram theorem on $H_0^1(I)$. -/
theorem example_8_2_general_ii (hα₀ : 0 < α₀)
    (hp : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ pL x)
    (hq : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 1 ≤ qL x)
    (hrL : rL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] r) (hr : ContDiffOn ℝ 1 r (Icc 0 1))
    (hr' : ∀ x ∈ Icc (0 : ℝ) 1, deriv r x ≤ 2) (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! u, IsGalerkinSolution (form 0 1 pL rL qL) (load 0 1 f) (SobolevIntervalZero 0 1) u := by
  have hc : 0 < α₀ / (1 + ((1 : ℝ) - 0) ^ 2 / 2) := by positivity
  obtain ⟨w, hw, hwu⟩ := SesqForm.laxMilgram
    ((form 0 1 pL rL qL).restrict (SobolevIntervalZero 0 1))
    ((load 0 1 f).comp (SobolevIntervalZero 0 1).subtypeL) hc
    (example_8_2_general_ii_coercive hα₀ hp hq hrL hr hr')
  refine ⟨(w : SobolevInterval 1 0 1), ⟨w.2, fun v hv ↦ hw ⟨v, hv⟩⟩, fun u hu ↦ ?_⟩
  have := hwu ⟨u, hu.1⟩ fun v ↦ hu.2 v v.2
  rw [← this]

/-- **Example 2** in Section 8.4 of [brezis2011functional], the more general problem (20),
$$-(pu')' + ru' + qu = f \text{ on } I, \qquad u(0) = u(1) = 0.$$
Let $I = (0, 1)$ and $\alpha > 0$, let $p, q, r_L \in L^\infty(I)$ with $p \ge \alpha$ and
$q \ge 1$ almost everywhere on $I$, and let $f \in L^2(I)$. The problem has a unique weak
solution $u \in H_0^1(I)$, that is, $\int_I pu'v' + \int_I r_L u'v + \int_I quv = \int_I fv$ for
all $v \in H_0^1(I)$, in each of two cases:
* (i) $\|r_L\|_\infty^2 < 4\alpha$;
* (ii) $r_L$ is equal almost everywhere on $I$ to a function $r \in C^1([0, 1])$ with $r' \le 2$
  on $[0, 1]$.

**Generalization.** The source takes $p$ and $q$ as in the Sturm–Liouville problem,
$p \in C^1(\bar I)$ and $q \in C(\bar I)$, and $r \in C(\bar I)$. Here the coefficients are
bounded measurable functions, with the bounds almost everywhere.

The form is not symmetric, but it is coercive, and the Lax–Milgram theorem applies. The
symmetrization by $\zeta = e^{-R}$ with $R' = r/p$ is
`Brezis.Chapter08.example_8_2_symmetrization`. -/
theorem example_8_2_general (hα₀ : 0 < α₀)
    (hp : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), α₀ ≤ pL x)
    (hq : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), 1 ≤ qL x)
    (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    (‖rL‖ ^ 2 < 4 * α₀ →
      ∃! u, IsGalerkinSolution (form 0 1 pL rL qL) (load 0 1 f) (SobolevIntervalZero 0 1) u) ∧
    ∀ r : ℝ → ℝ, rL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] r → ContDiffOn ℝ 1 r (Icc 0 1) →
      (∀ x ∈ Icc (0 : ℝ) 1, deriv r x ≤ 2) →
      ∃! u, IsGalerkinSolution (form 0 1 pL rL qL) (load 0 1 f) (SobolevIntervalZero 0 1) u :=
  ⟨fun hr ↦ example_8_2_general_i hα₀ hp hq hr f,
    fun _ hrL hr hr' ↦ example_8_2_general_ii hα₀ hp hq hrL hr hr' f⟩

/-- **Example 2** in Section 8.4 of [brezis2011functional], the identity $\zeta' p + \zeta r = 0$ of
the symmetrization. Let $p, r, R : \mathbb{R} \to \mathbb{R}$ and $x \in \mathbb{R}$ with
$p(x) \neq 0$, and let $R$ have the derivative $r(x)/p(x)$ at $x$. Then $\zeta = e^{-R}$
satisfies
$$\zeta'(x) p(x) + \zeta(x) r(x) = 0.$$
-/
theorem example_8_2_symmetrization_deriv {R : ℝ → ℝ} {x : ℝ}
    (hR : HasDerivAt R (r x / p x) x) (hpx : p x ≠ 0) :
    deriv (fun t ↦ Real.exp (-R t)) x * p x + Real.exp (-R x) * r x = 0 := by
  have hζ : HasDerivAt (fun t ↦ Real.exp (-R t)) (Real.exp (-R x) * -(r x / p x)) x :=
    (Real.hasDerivAt_exp _).comp x hR.neg
  rw [hζ.deriv]
  field_simp
  ring

/-- **Example 2** in Section 8.4 of [brezis2011functional], the symmetrization of (20). Let
$p, q, r, f, u, R : \mathbb{R} \to \mathbb{R}$, with $p$ differentiable and nowhere zero,
$u \in C^2(\mathbb{R})$, and $R' = r/p$ on $\mathbb{R}$. Let $\zeta = e^{-R}$. Then for every
$x \in \mathbb{R}$,
$$-(pu')'(x) + r(x)u'(x) + q(x)u(x) = f(x) \iff -(\zeta pu')'(x) + \zeta(x) q(x) u(x) = \zeta(x)
  f(x).$$

The proof multiplies by $\zeta > 0$ and uses $\zeta' p + \zeta r = 0$
(`Brezis.Chapter08.example_8_2_symmetrization_deriv`). -/
theorem example_8_2_symmetrization {R u f : ℝ → ℝ} (hR : ∀ x, HasDerivAt R (r x / p x) x)
    (hp : ∀ x, p x ≠ 0) (hpd : Differentiable ℝ p) (hu : ContDiff ℝ 2 u) (x : ℝ) :
    -deriv (fun t ↦ p t * deriv u t) x + r x * deriv u x + q x * u x = f x ↔
      -deriv (fun t ↦ Real.exp (-R t) * (p t * deriv u t)) x
        + Real.exp (-R x) * (q x * u x) = Real.exp (-R x) * f x := by
  have hu1 : Differentiable ℝ (deriv u) :=
    (hu.iterate_deriv' 1 1).differentiable one_ne_zero
  have hζ : HasDerivAt (fun t ↦ Real.exp (-R t)) (Real.exp (-R x) * -(r x / p x)) x :=
    (Real.hasDerivAt_exp _).comp x (hR x).neg
  have hpu : HasDerivAt (fun t ↦ p t * deriv u t) (deriv (fun t ↦ p t * deriv u t) x) x :=
    ((hpd x).hasDerivAt.mul (hu1 x).hasDerivAt).differentiableAt.hasDerivAt
  have hd := (hζ.fun_mul hpu).deriv
  rw [hd]
  have hζpos : 0 < Real.exp (-R x) := Real.exp_pos _
  constructor
  · intro h
    field_simp
    have := hp x
    field_simp at h ⊢
    nlinarith [h, hζpos]
  · intro h
    have hp' := hp x
    field_simp at h
    have : Real.exp (-R x) * (-deriv (fun t ↦ p t * deriv u t) x + r x * deriv u x + q x * u x)
        = Real.exp (-R x) * f x := by
      field_simp
      nlinarith [h]
    exact mul_left_cancel₀ hζpos.ne' this

end SturmLiouville

/-! ### Examples 3–7: Neumann, mixed, Robin and periodic conditions -/

/-- **Proposition 8.17** of [brezis2011functional]. This is Example 3 of Section 8.4, the
homogeneous Neumann condition. Let $I = (0, 1)$. For every $f \in L^2(I)$ there is a unique
$u \in H^2(I)$ that satisfies (21):
$$-u'' + u = f \text{ a.e. on } I, \qquad u'(0) = u'(1) = 0.$$

Since $u \in H^2$, $u'$ has a continuous representative on $\bar I$ (footnote 13 of the source),
so $u'(0)$ and $u'(1)$ make sense. The proof specializes
`EllipticInterval.existsUnique_neumann`: the Lax–Milgram theorem on all of $H^1(I)$ for the weak
formulation (22), and then the natural boundary conditions from (23). -/
theorem proposition_8_17 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! Φ : SobolevInterval 2 0 1,
      ((SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun x ↦ SobolevInterval.fn Φ x - f x) ∧
      SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0 = 0 ∧
      SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = 0 :=
  existsUnique_neumann (zero_lt_one' ℝ) f

/-- **Proposition 8.17** of [brezis2011functional], the weak formulation (22) and the minimization.
Let $I = (0, 1)$ and $f \in L^2(I)$, and let $u \in H^2(I)$ satisfy (21). Then
$$\int_I u'v' + \int_I uv = \int_I fv \quad \text{for all } v \in H^1(I),$$
and $u$ minimizes $\frac12 \int_I (v'^2 + v^2) - \int_I fv$ over $v \in H^1(I)$.

The weak formulation follows from Green's formula, since the boundary terms vanish. -/
theorem proposition_8_17_min (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0 = 0)
    (h1 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = 0) :
    (∀ v, modelForm 0 1 (SobolevInterval.inclusionCLM 1 0 1 Φ) v = load 0 1 f v) ∧
      IsMinOn ((modelForm 0 1).energy (load 0 1 f)) univ
        (SobolevInterval.inclusionCLM 1 0 1 Φ) := by
  have hweak : ∀ v, modelForm 0 1 (SobolevInterval.inclusionCLM 1 0 1 Φ) v = load 0 1 f v :=
    fun v ↦ by
      rw [modelForm_inclusionCLM_eq_of_deriv_two (zero_lt_one' ℝ) f hΦ v, h0, h1]; ring
  exact ⟨hweak, (neumann_isMinOn_energy_iff (load 0 1 f) _).2 hweak⟩

/-- **Proposition 8.17** of [brezis2011functional], the classical solution. Let
$f : \mathbb{R} \to \mathbb{R}$ be continuous on $[0, 1]$, let $f_L \in L^2(0, 1)$ be equal to
$f$ almost everywhere on $(0, 1)$, and let $u \in H^2(0, 1)$ satisfy $u'' = u - f_L$ almost
everywhere on $(0, 1)$. Then there is $v \in C^2([0, 1])$ such that $u$ is the element of
$H^1(0, 1)$ carried by $v$ and $-v'' + v = f$ on $(0, 1)$.

This is the statement of the source that $u \in C^2(\bar I)$ if in addition $f \in C(\bar I)$.
The boundary conditions play no role, and the statement is the same as
`Brezis.Chapter08.proposition_8_16_C2`. -/
theorem proposition_8_17_C2 {f : ℝ → ℝ} (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f) (hf : ContinuousOn f (Icc 0 1))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - fL x) :
    ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2,
      ofContDiffMapIcc (zero_lt_one' ℝ) v = SobolevInterval.inclusionCLM 1 0 1 Φ ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, -deriv v.shift.extend x + v.extend x = f x :=
  exists_contDiffMapIcc_of_deriv_two (zero_lt_one' ℝ) fL hfL hf hΦ

/-- **Proposition 8.18** of [brezis2011functional]. This is Example 4 of Section 8.4, the
inhomogeneous Neumann condition. Let $I = (0, 1)$. For every $f \in L^2(I)$ and
$\alpha, \beta \in \mathbb{R}$ there is a unique $u \in H^2(I)$ that satisfies (24):
$$-u'' + u = f \text{ a.e. on } I, \qquad u'(0) = \alpha, \quad u'(1) = \beta.$$

The source adds that $u$ is obtained by minimizing $\frac12 \int (v'^2 + v^2) - \int fv + \alpha
v(0) - \beta v(1)$ over $H^1(I)$; this is `Brezis.Chapter08.proposition_8_18_min`. The proof
specializes `EllipticInterval.existsUnique_neumann_inhomogeneous`. -/
theorem proposition_8_18 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (α β : ℝ) :
    ∃! Φ : SobolevInterval 2 0 1,
      ((SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun x ↦ SobolevInterval.fn Φ x - f x) ∧
      SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0 = α ∧
      SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = β :=
  existsUnique_neumann_inhomogeneous (zero_lt_one' ℝ) f α β

/-- **Proposition 8.18** of [brezis2011functional], the minimization. Let $I = (0, 1)$,
$f \in L^2(I)$ and $\alpha, \beta \in \mathbb{R}$, and let $u \in H^2(I)$ satisfy (24). Then $u$
minimizes
$$\frac12 \int_I (v'^2 + v^2) - \int_I fv + \alpha v(0) - \beta v(1)$$
over $v \in H^1(I)$.

The functional is the energy for the load $v \mapsto \int fv - \alpha v(0) + \beta v(1)$,
`EllipticInterval.neumannLoad`, which is continuous on $H^1(I)$ by Theorem 8.8. The proof shows
the weak formulation with this load and applies Dirichlet's principle on $H^1(I)$. -/
theorem proposition_8_18_min (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) (α β : ℝ)
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - f x)
    (h0 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0 = α)
    (h1 : SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = β) :
    IsMinOn ((modelForm 0 1).energy (neumannLoad (zero_lt_one' ℝ) f α β)) univ
      (SobolevInterval.inclusionCLM 1 0 1 Φ) := by
  refine (neumann_isMinOn_energy_iff _ _).2 fun v ↦ ?_
  rw [modelForm_inclusionCLM_eq_of_deriv_two (zero_lt_one' ℝ) f hΦ v, h0, h1,
    neumannLoad_apply]
  ring

/-- **Example 5** in Section 8.4 of [brezis2011functional], the mixed boundary condition. Let
$I = (0, 1)$. For every $f \in L^2(I)$ there is a unique $u \in H^2(I)$ that satisfies (25):
$$-u'' + u = f \text{ a.e. on } I, \qquad u(0) = 0, \quad u'(1) = 0.$$

The weak formulation (26) is set in $H = \{v \in H^1(I) : v(0) = 0\}$,
`EllipticInterval.mixedSpace`. The source leaves the rest to the reader. The proof specializes
`EllipticInterval.existsUnique_mixed`. -/
theorem example_8_5 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! Φ : SobolevInterval 2 0 1,
      ((SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun x ↦ SobolevInterval.fn Φ x - f x) ∧
      SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 = 0 ∧
      SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 = 0 :=
  existsUnique_mixed (zero_lt_one' ℝ) f

/-- **Example 6** in Section 8.4 of [brezis2011functional], the Robin form. Let $I = (0, 1)$ and
$k \ge 0$. The Robin form $a$ on $H^1(I)$ is given by
$$a(u, v) = \int_I u'v' + \int_I uv + k u(0) v(0),$$
it is symmetric, and it satisfies $a(v, v) \ge \|v\|_{H^1}^2$ for all $v \in H^1(I)$.

The form is `EllipticInterval.robinForm`, and it is continuous by its type. The source uses it
on $H = \{v \in H^1(I) : v(1) = 0\}$, `EllipticInterval.robinSpace`. -/
theorem example_8_6_coercive {k : ℝ} (hk : 0 ≤ k) :
    (∀ u v : SobolevInterval 1 0 1, robinForm (zero_lt_one' ℝ) k u v
      = modelForm 0 1 u v + k * (SobolevInterval.rep u 0 * SobolevInterval.rep v 0)) ∧
    (robinForm (zero_lt_one' ℝ) k).IsHermitian ∧ (robinForm (zero_lt_one' ℝ) k).IsCoerciveWith 1 :=
  ⟨robinForm_apply (zero_lt_one' ℝ) k, robinForm_isHermitian (zero_lt_one' ℝ) k,
    robinForm_isCoerciveWith (zero_lt_one' ℝ) hk⟩

/-- **Example 6** in Section 8.4 of [brezis2011functional], the Robin boundary condition. Let
$I = (0, 1)$ and $k \ge 0$. For every $f \in L^2(I)$ there is a unique $u \in H^2(I)$ that
satisfies (27):
$$-u'' + u = f \text{ a.e. on } I, \qquad u'(0) = k u(0), \quad u(1) = 0.$$

The proof is the Lax–Milgram theorem for the Robin form on $H = \{v \in H^1(I) : v(1) = 0\}$,
`EllipticInterval.existsUnique_robin`. Footnotes 14 and 15 of the source, on the general
condition of the third type and on small negative $k$, are not formalized. -/
theorem example_8_6 {k : ℝ} (hk : 0 ≤ k) (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! Φ : SobolevInterval 2 0 1,
      ((SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun x ↦ SobolevInterval.fn Φ x - f x) ∧
      SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0
        = k * SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0 ∧
      SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 = 0 :=
  existsUnique_robin (zero_lt_one' ℝ) f hk

/-- **Example 7** in Section 8.4 of [brezis2011functional], the periodic boundary condition. Let
$I = (0, 1)$. For every $f \in L^2(I)$ there is a unique $u \in H^2(I)$ that satisfies (28):
$$-u'' + u = f \text{ a.e. on } I, \qquad u(0) = u(1), \quad u'(0) = u'(1).$$

The proof is the Lax–Milgram theorem for the form $\int u'v' + \int uv$ on
$H = \{v \in H^1(I) : v(0) = v(1)\}$, `EllipticInterval.periodicSpace`, with the weak
formulation (29). It specializes `EllipticInterval.existsUnique_periodic`. -/
theorem example_8_7 (f : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃! Φ : SobolevInterval 2 0 1,
      ((SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        fun x ↦ SobolevInterval.fn Φ x - f x) ∧
      SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 0
        = SobolevInterval.rep (SobolevInterval.inclusionCLM 1 0 1 Φ) 1 ∧
      SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 0
        = SobolevInterval.rep (SobolevInterval.derivCLM 1 0 1 Φ) 1 :=
  existsUnique_periodic (zero_lt_one' ℝ) f

/-- **Examples 5–7** in Section 8.4 of [brezis2011functional], the classical solution. Let
$f : \mathbb{R} \to \mathbb{R}$ be continuous on $[0, 1]$, let $f_L \in L^2(0, 1)$ be equal to
$f$ almost everywhere on $(0, 1)$, and let $u \in H^2(0, 1)$ satisfy $u'' = u - f_L$ almost
everywhere on $(0, 1)$. Then there is $v \in C^2([0, 1])$ such that $u$ is the element of
$H^1(0, 1)$ carried by $v$ and $-v'' + v = f$ on $(0, 1)$.

The boundary conditions play no role, so the statement covers the solutions of the mixed, Robin
and periodic problems. The proof specializes
`EllipticInterval.exists_contDiffMapIcc_of_deriv_two`. -/
theorem example_8_5_6_7_C2 {f : ℝ → ℝ} (fL : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hfL : fL =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f) (hf : ContinuousOn f (Icc 0 1))
    {Φ : SobolevInterval 2 0 1}
    (hΦ : (SobolevInterval.deriv Φ 2 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun x ↦ SobolevInterval.fn Φ x - fL x) :
    ∃ v : ContDiffMapIcc (zero_lt_one' ℝ).le 2,
      ofContDiffMapIcc (zero_lt_one' ℝ) v = SobolevInterval.inclusionCLM 1 0 1 Φ ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, -deriv v.shift.extend x + v.extend x = f x :=
  exists_contDiffMapIcc_of_deriv_two (zero_lt_one' ℝ) fL hfL hf hΦ

/-! ### Example 8: a boundary value problem on $\mathbb{R}$ -/

/-- **Example 8** in Section 8.4 of [brezis2011functional], a classical solution is a weak solution.
Let $f : \mathbb{R} \to \mathbb{R}$ be equal almost everywhere to some
$f_L \in L^2(\mathbb{R})$, and let $u \in C^2(\mathbb{R})$ be a classical solution of (30):
$$-u'' + u = f \text{ on } \mathbb{R}, \qquad u(x) \to 0 \text{ as } |x| \to \infty.$$
Then $u \in H^1(\mathbb{R})$, and there is $U \in H^1(\mathbb{R})$ whose continuous
representative is $u$ and which satisfies (31):
$$\int_{\mathbb{R}} U'v' + \int_{\mathbb{R}} Uv = \int_{\mathbb{R}} fv \quad \text{for all } v
  \in H^1(\mathbb{R}).$$

The source proves $u \in H^1(\mathbb{R})$ with cut-off functions $\zeta_n$. The form and the
load of (31) are `EllipticInterval.Line.form`, the inner product of $H^1(\mathbb{R})$, and
`EllipticInterval.Line.load`. The proof specializes
`EllipticInterval.Line.memSobolevIntervalLp_of_classical` and
`EllipticInterval.Line.isWeakSolution_of_classical`. -/
theorem example_8_8_classical_weak {u f : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (fL : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hfL : fL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f)
    (hode : ∀ x, -deriv (deriv u) x + u x = f x) (hlim : Tendsto u (cocompact ℝ) (𝓝 0)) :
    MemSobolevIntervalLp u 1 2 ⊤ ∧
      ∃ U : SobolevIntervalLp 1 2 ⊤, (∀ x, U.rep x = u x) ∧
        ∀ v : SobolevIntervalLp 1 2 ⊤, Line.form U v = Line.load fL v :=
  have hf : MemLp f 2 volume :=
    (SobolevIntervalLp.memLp_restrict_top_iff.1 (Lp.memLp fL)).ae_eq
      (SobolevIntervalLp.eventuallyEq_restrict_top_iff.1 hfL)
  let ⟨U, hU, hUrep, _⟩ := Line.isWeakSolution_of_classical hu fL hfL hode hlim
  ⟨Line.memSobolevIntervalLp_of_classical hu hf hode hlim, U, hUrep, fun v ↦ by
    rw [hU]; exact Line.form_solution fL v⟩

/-- **Example 8** in Section 8.4 of [brezis2011functional], existence and uniqueness of the weak
solution. For every $f \in L^2(\mathbb{R})$ there is exactly one $u \in H^1(\mathbb{R})$ that
satisfies (31):
$$\int_{\mathbb{R}} u'v' + \int_{\mathbb{R}} uv = \int_{\mathbb{R}} fv \quad \text{for all } v
  \in H^1(\mathbb{R}).$$

The proof is the Lax–Milgram theorem, which here is the Riesz–Fréchet theorem in the Hilbert
space $H^1(\mathbb{R})$. The solution is `EllipticInterval.Line.solution`. -/
theorem example_8_8_existsUnique (fL : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    ∃! u : SobolevIntervalLp 1 2 ⊤, ∀ v, Line.form u v = Line.load fL v :=
  ⟨Line.solution fL, Line.form_solution fL, fun _ hu ↦ Line.eq_solution_of_forall hu⟩

/-- **Example 8** in Section 8.4 of [brezis2011functional], regularity and the classical solution.
Let $f \in L^2(\mathbb{R})$ and let $u \in H^1(\mathbb{R})$ be the weak solution of (31). Then:
* $u \in H^2(\mathbb{R})$;
* $u(x) \to 0$ as $|x| \to \infty$;
* if $f$ is equal almost everywhere to a continuous function $g$, then $u \in C^2(\mathbb{R})$
  with $-u'' + u = g$ on $\mathbb{R}$, and problem (30) with the datum $g$ has a unique
  classical solution $w \in C^2(\mathbb{R})$, $-w'' + w = g$ on $\mathbb{R}$, $w(x) \to 0$ as
  $|x| \to \infty$.

The decay of $u$ uses Corollary 8.9. The proof specializes
`EllipticInterval.Line.memSobolevIntervalLp_two_solution`,
`EllipticInterval.Line.contDiff_rep_solution`,
`EllipticInterval.Line.tendsto_rep_solution_cocompact` and
`EllipticInterval.Line.exists_classical_solution`. -/
theorem example_8_8_regularity (fL : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    MemSobolevIntervalLp (Line.solution fL).fn 2 2 ⊤ ∧
      Tendsto (Line.solution fL).rep (cocompact ℝ) (𝓝 0) ∧
      ∀ f : ℝ → ℝ, fL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f → Continuous f →
        (ContDiff ℝ 2 (Line.solution fL).rep ∧
          ∀ x, -deriv (deriv (Line.solution fL).rep) x + (Line.solution fL).rep x = f x) ∧
        ∃! w : ℝ → ℝ, ContDiff ℝ 2 w ∧ (∀ x, -deriv (deriv w) x + w x = f x) ∧
          Tendsto w (cocompact ℝ) (𝓝 0) :=
  ⟨Line.memSobolevIntervalLp_two_solution fL, Line.tendsto_rep_solution_cocompact fL,
    fun _ hfL hf ↦ ⟨Line.contDiff_rep_solution fL hfL hf, Line.exists_classical_solution fL hfL hf⟩⟩

/-- **Example 8** in Section 8.4 of [brezis2011functional]. Let $f \in L^2(\mathbb{R})$, and let
$u_f \in H^1(\mathbb{R})$ be the weak solution of (31). Then:
* every classical solution $u \in C^2(\mathbb{R})$ of (30) for a function a.e. equal to $f$ lies
  in $H^1(\mathbb{R})$ and is equal to the continuous representative of $u_f$;
* (31) has exactly one solution in $H^1(\mathbb{R})$;
* $u_f \in H^2(\mathbb{R})$;
* if $f$ is equal almost everywhere to a continuous function $g$, problem (30) with the datum
  $g$ has a unique classical solution in $C^2(\mathbb{R})$.

The decay $u_f(x) \to 0$ as $|x| \to \infty$ is in `Brezis.Chapter08.example_8_8_regularity`,
not in this statement. -/
theorem example_8_8 (fL : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))) :
    (∀ u f : ℝ → ℝ, ContDiff ℝ 2 u → fL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f →
      (∀ x, -deriv (deriv u) x + u x = f x) → Tendsto u (cocompact ℝ) (𝓝 0) →
      MemSobolevIntervalLp u 1 2 ⊤ ∧ ∀ x, (Line.solution fL).rep x = u x) ∧
    (∃! u : SobolevIntervalLp 1 2 ⊤, ∀ v, Line.form u v = Line.load fL v) ∧
    MemSobolevIntervalLp (Line.solution fL).fn 2 2 ⊤ ∧
    ∀ f : ℝ → ℝ, fL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f → Continuous f →
      ∃! w : ℝ → ℝ, ContDiff ℝ 2 w ∧ (∀ x, -deriv (deriv w) x + w x = f x) ∧
        Tendsto w (cocompact ℝ) (𝓝 0) :=
  ⟨fun u _ hu hfL hode hlim ↦
    ⟨(example_8_8_classical_weak hu fL hfL hode hlim).1, fun x ↦ by
      rw [Line.eq_rep_solution_of_classical fL hfL hu hode hlim]⟩,
    example_8_8_existsUnique fL, Line.memSobolevIntervalLp_two_solution fL,
    fun _ hfL hf ↦ Line.exists_classical_solution fL hfL hf⟩

/-! ### Remarks 24 and 25 -/

/-- **Remark 24** in Chapter 8 of [brezis2011functional], the problem need not have a solution.
There is $f \in C_c^\infty(\mathbb{R})$ such that the problem
$$-u'' = f \text{ on } \mathbb{R}, \qquad u(x) \to 0 \text{ as } |x| \to \infty,$$
has no solution $u \in C^2(\mathbb{R})$.

The source asks why. The proof takes a nonnegative bump $f$ with $f(0) = 1$. For a solution,
$u'' = -f \le 0$, so $u'$ is nonincreasing. If $u'(x_0) < 0$, then
$u(y) \le u(x_0) + u'(x_0)(y - x_0) \to -\infty$ as $y \to +\infty$; if $u'(x_0) > 0$, then
$u(y) \to -\infty$ as $y \to -\infty$. So $u' = 0$, $u$ is constant, hence $u = 0$, and $f = 0$. -/
theorem remark_8_24_exists_not_solvable :
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      ¬ ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ (∀ x, -deriv (deriv u) x = f x) ∧
        Tendsto u (cocompact ℝ) (𝓝 0) := by
  obtain ⟨φ, hφin⟩ : ∃ φ : ContDiffBump (0 : ℝ), φ.rIn = 1 := ⟨⟨1, 2, one_pos, one_lt_two⟩, rfl⟩
  refine ⟨φ, φ.contDiff, φ.hasCompactSupport, ?_⟩
  rintro ⟨u, hu, hode, hlim⟩
  rw [cocompact_eq_atBot_atTop, tendsto_sup] at hlim
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu2 : Differentiable ℝ (deriv u) := (hu.iterate_deriv' 1 1).differentiable one_ne_zero
  have hanti : Antitone (deriv u) := antitone_of_deriv_nonpos hu2 fun x ↦ by
    have := hode x
    linarith [φ.nonneg' x]
  -- `u' ≡ 0`
  have hderiv : ∀ x, deriv u x = 0 := fun x₀ ↦ by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · -- `u → −∞` at `+∞`
      have hbd : ∀ y, x₀ ≤ y → u y - u x₀ ≤ deriv u x₀ * (y - x₀) := fun y hy ↦
        (convex_Ici x₀).image_sub_le_mul_sub_of_deriv_le hu1.continuous.continuousOn
          hu1.differentiableOn (fun z hz ↦ hanti (interior_subset (s := Ici x₀) hz).out)
          x₀ self_mem_Ici y hy hy
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.2.eventually (eventually_gt_nhds
        (show (-1 : ℝ) < 0 by norm_num)))
      obtain ⟨y, hy₁, hy₂⟩ : ∃ y, max N x₀ ≤ y ∧ deriv u x₀ * (y - x₀) ≤ -(2 + |u x₀|) := by
        refine ⟨max (max N x₀) (x₀ + (2 + |u x₀|) / (-deriv u x₀)), le_max_left _ _, ?_⟩
        have h1 : x₀ + (2 + |u x₀|) / (-deriv u x₀)
            ≤ max (max N x₀) (x₀ + (2 + |u x₀|) / (-deriv u x₀)) := le_max_right _ _
        have h2 : 0 < -deriv u x₀ := by linarith
        have h3 : (2 + |u x₀|) / (-deriv u x₀) * (-deriv u x₀) = 2 + |u x₀| := by
          field_simp
        nlinarith [abs_nonneg (u x₀), h1, h2, h3]
      have := hbd y ((le_max_right N x₀).trans hy₁)
      have := hN y ((le_max_left N x₀).trans hy₁)
      linarith [le_abs_self (u x₀), neg_abs_le (u x₀)]
    · -- `u → −∞` at `−∞`
      have hbd : ∀ y, y ≤ x₀ → deriv u x₀ * (x₀ - y) ≤ u x₀ - u y := fun y hy ↦
        (convex_Iic x₀).mul_sub_le_image_sub_of_le_deriv hu1.continuous.continuousOn
          hu1.differentiableOn (fun z hz ↦ hanti (Set.mem_Iic.1 (interior_subset hz)))
          y hy x₀ self_mem_Iic hy
      obtain ⟨N, hN⟩ := eventually_atBot.1 (hlim.1.eventually (eventually_gt_nhds
        (show (-1 : ℝ) < 0 by norm_num)))
      obtain ⟨y, hy₁, hy₂⟩ : ∃ y, y ≤ min N x₀ ∧ 2 + |u x₀| ≤ deriv u x₀ * (x₀ - y) := by
        refine ⟨min (min N x₀) (x₀ - (2 + |u x₀|) / deriv u x₀), min_le_left _ _, ?_⟩
        have h1 : min (min N x₀) (x₀ - (2 + |u x₀|) / deriv u x₀)
            ≤ x₀ - (2 + |u x₀|) / deriv u x₀ := min_le_right _ _
        have h3 : (2 + |u x₀|) / deriv u x₀ * deriv u x₀ = 2 + |u x₀| := by
          field_simp
        nlinarith [abs_nonneg (u x₀), h1, hpos, h3]
      have := hbd y (hy₁.trans (min_le_right N x₀))
      have := hN y (hy₁.trans (min_le_left N x₀))
      linarith [le_abs_self (u x₀), neg_abs_le (u x₀)]
  -- so `u` is constant, hence `0`, hence `f = 0`
  have hconst : ∀ x, u x = u 0 := fun x ↦ is_const_of_deriv_eq_zero hu1 hderiv x 0
  have hu0 : u 0 = 0 := by
    have h1 : Tendsto u atTop (𝓝 (u 0)) :=
      tendsto_const_nhds.congr fun x ↦ (hconst x).symm
    exact tendsto_nhds_unique h1 hlim.2
  have hf0 : φ 0 = 0 := by
    rw [← hode 0]
    have : deriv u = fun _ ↦ 0 := funext hderiv
    rw [this, deriv_const]
    simp
  rw [φ.one_of_mem_closedBall (by rw [hφin]; exact Metric.mem_closedBall_self zero_le_one)] at hf0
  exact one_ne_zero hf0

/-- The square of a continuous function with compact support is integrable on $\mathbb{R}$. -/
private theorem integrable_sq_of_hasCompactSupport {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun x ↦ g x ^ 2) := by
  refine (hg.pow 2).integrable_of_hasCompactSupport (hgc.mono' fun x hx ↦ subset_tsupport g ?_)
  intro h
  rw [Function.mem_support] at hx
  exact hx (by rw [Pi.pow_apply, h]; norm_num)

/-- The inner product in $L^2(\mathbb{R})$ of an element with itself is $\int g^2$, for any
representative $g$. -/
private theorem inner_self_eq_integral_sq {g : ℝ → ℝ}
    (F : Lp ℝ 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hF : ⇑F =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] g) : ⟪F, F⟫_ℝ = ∫ x, g x ^ 2 := by
  rw [L2.inner_def]
  change ∫ a in (univ : Set ℝ), ⟪F a, F a⟫_ℝ = _
  rw [Measure.restrict_univ]
  have hF' : ⇑F =ᵐ[volume] g := SobolevIntervalLp.eventuallyEq_restrict_top_iff.1 hF
  refine integral_congr_ae (hF'.mono fun x hx ↦ ?_)
  simp only [RCLike.inner_apply, conj_trivial, hx, sq]

/-- **Remark 24** in Chapter 8 of [brezis2011functional], the form is not coercive. The bilinear
form $a(u, v) = \int_{\mathbb{R}} u'v'$ is not coercive in $H^1(\mathbb{R})$: there is no
$c > 0$ with
$$c \|v\|_{H^1}^2 \le \int_{\mathbb{R}} v'^2 \quad \text{for all } v \in H^1(\mathbb{R}).$$

The proof uses the dilations $v_n(x) = \varphi(x/n)$ of a bump $\varphi$. They satisfy
$\int v_n'^2 = n^{-1} \int \varphi'^2$, while $\|v_n\|_{H^1}^2 \ge \|v_n\|_{L^2}^2 = n \int
\varphi^2 \ge 2n$. -/
theorem remark_8_24_not_coercive :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ v : SobolevIntervalLp 1 2 ⊤,
      c * ‖v‖ ^ 2 ≤ ∫ x, (SobolevIntervalLp.deriv v 1 x) ^ 2 := by
  rintro ⟨c, hc, hcoer⟩
  obtain ⟨φ, hφin⟩ : ∃ φ : ContDiffBump (0 : ℝ), φ.rIn = 1 := ⟨⟨1, 2, one_pos, one_lt_two⟩, rfl⟩
  have hφc : Continuous φ := φ.continuous
  have hφ'c : Continuous (deriv φ) := (φ.contDiff (n := 1)).continuous_deriv le_rfl
  -- `∫ φ² ≥ 2`, `φ` being `1` on `[-1, 1]`
  have hφ2 : 2 ≤ ∫ x, (φ x) ^ 2 := by
    have hint := integrable_sq_of_hasCompactSupport hφc φ.hasCompactSupport
    have h1 : ∫ x in Icc (-1 : ℝ) 1, (φ x) ^ 2 = 2 := by
      rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ ↦ (1 : ℝ)) fun x hx ↦ by
        rw [φ.one_of_mem_closedBall (by
          rw [hφin, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le]
          exact hx), one_pow]]
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul]
      norm_num
    rw [← h1]
    exact setIntegral_le_integral hint (Eventually.of_forall fun x ↦ sq_nonneg _)
  -- the dilations `x ↦ φ((n+1)⁻¹ x)`, as test functions on `ℝ`
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℕ → 𝓓((⊤ : Opens ℝ), ℝ), ∀ n, ⇑(ψ n) = fun x ↦ φ (((n : ℝ) + 1)⁻¹ * x) :=
    ⟨fun n ↦ ⟨fun x ↦ φ (((n : ℝ) + 1)⁻¹ * x),
      (φ.contDiff (n := ⊤)).comp (contDiff_const.mul contDiff_id),
      φ.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft₀ ((n : ℝ) + 1)⁻¹ (by positivity)),
      fun _ _ ↦ trivial⟩, fun n ↦ rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℕ → SobolevIntervalLp 1 2 ⊤,
      ∀ n, v n = TestFunction.toSobolevIntervalLp 2 (ψ n) := ⟨_, fun n ↦ rfl⟩
  -- the derivative of the dilation
  have hderiv : ∀ n x, deriv (ψ n) x = ((n : ℝ) + 1)⁻¹ * deriv φ (((n : ℝ) + 1)⁻¹ * x) :=
    fun n x ↦ by rw [hψ]; exact deriv_comp_mul_left _ _ _
  -- the two integrals, by the change of variables `x ↦ (n+1)⁻¹ x`
  have hA : ∀ n, ∫ x, (SobolevIntervalLp.deriv (v n) 1 x) ^ 2
      = ((n : ℝ) + 1)⁻¹ * ∫ y, (deriv φ y) ^ 2 := fun n ↦ by
    have e1 : (fun x ↦ (SobolevIntervalLp.deriv (v n) 1 x) ^ 2) =ᵐ[volume]
        fun x ↦ (((n : ℝ) + 1)⁻¹ * deriv φ (((n : ℝ) + 1)⁻¹ * x)) ^ 2 := by
      have := SobolevIntervalLp.eventuallyEq_restrict_top_iff.1
        (TestFunction.coeFn_deriv_toSobolevIntervalLp_one (p := 2) (ψ n))
      rw [← hv] at this
      filter_upwards [this] with x hx
      rw [hx, hderiv]
    rw [integral_congr_ae e1]
    have e2 : (fun x ↦ (((n : ℝ) + 1)⁻¹ * deriv φ (((n : ℝ) + 1)⁻¹ * x)) ^ 2)
        = fun x ↦ (((n : ℝ) + 1)⁻¹) ^ 2 * (fun y ↦ (deriv φ y) ^ 2) (((n : ℝ) + 1)⁻¹ * x) :=
      funext fun x ↦ by ring
    rw [e2, integral_const_mul, Measure.integral_comp_mul_left (fun y ↦ (deriv φ y) ^ 2),
      inv_inv, abs_of_pos (by positivity), smul_eq_mul]
    field_simp
  have hB : ∀ n, ‖SobolevIntervalLp.deriv (v n) 0‖ ^ 2 = ((n : ℝ) + 1) * ∫ y, (φ y) ^ 2 :=
    fun n ↦ by
    rw [← real_inner_self_eq_norm_sq, inner_self_eq_integral_sq _
      (g := fun x ↦ φ (((n : ℝ) + 1)⁻¹ * x)) (by
        rw [hv, SobolevIntervalLp.deriv_zero, ← hψ]
        exact TestFunction.fn_toSobolevIntervalLp_ae_eq (ψ n))]
    rw [Measure.integral_comp_mul_left (fun y ↦ (φ y) ^ 2), inv_inv, abs_of_pos (by positivity),
      smul_eq_mul]
  -- the contradiction for `n` large
  obtain ⟨M, hM⟩ : ∃ M, M = ∫ y, (deriv φ y) ^ 2 := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M / (2 * c) < n := exists_nat_gt _
  have h1 := hcoer (v n)
  rw [hA n, ← hM] at h1
  have h2 : ((n : ℝ) + 1) * 2 ≤ ‖v n‖ ^ 2 := by
    calc ((n : ℝ) + 1) * 2 ≤ ((n : ℝ) + 1) * ∫ y, (φ y) ^ 2 := by gcongr
      _ = ‖SobolevIntervalLp.deriv (v n) 0‖ ^ 2 := (hB n).symm
      _ ≤ ‖v n‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (SobolevIntervalLp.norm_deriv_le _ 0) 2
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h3 : M < 2 * c * n := by
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith
  have h4 : c * (((n : ℝ) + 1) * 2) ≤ ((n : ℝ) + 1)⁻¹ * M := by
    calc c * (((n : ℝ) + 1) * 2) ≤ c * ‖v n‖ ^ 2 := by gcongr
      _ ≤ ((n : ℝ) + 1)⁻¹ * M := h1
  have h5 : c * (((n : ℝ) + 1) * 2) * ((n : ℝ) + 1) ≤ M := by
    have := mul_le_mul_of_nonneg_right h4 hn1.le
    have e : ((n : ℝ) + 1)⁻¹ * M * ((n : ℝ) + 1) = M := by field_simp
    rwa [e] at this
  have h6 : 2 * c * n ≤ c * (((n : ℝ) + 1) * 2) * ((n : ℝ) + 1) := by
    have : 0 ≤ c * ((n : ℝ) ^ 2 + n + 1) := mul_nonneg hc.le (by positivity)
    nlinarith
  linarith

/-- **Remark 24** in Chapter 8 of [brezis2011functional]. The problem $-u'' = f$ on $\mathbb{R}$,
$u(x) \to 0$ as $|x| \to \infty$, cannot be attacked by the technique of Example 8:
* the bilinear form $a(u, v) = \int_{\mathbb{R}} u'v'$ is not coercive in $H^1(\mathbb{R})$:
  there is no $c > 0$ with $c \|v\|_{H^1}^2 \le \int v'^2$ for all $v \in H^1(\mathbb{R})$
  (`Brezis.Chapter08.remark_8_24_not_coercive`);
* the problem need not have a solution in $C^2(\mathbb{R})$ even if $f$ is smooth with compact
  support (`Brezis.Chapter08.remark_8_24_exists_not_solvable`). -/
theorem remark_8_24 :
    (¬ ∃ c : ℝ, 0 < c ∧ ∀ v : SobolevIntervalLp 1 2 ⊤,
      c * ‖v‖ ^ 2 ≤ ∫ x, (SobolevIntervalLp.deriv v 1 x) ^ 2) ∧
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      ¬ ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ (∀ x, -deriv (deriv u) x = f x) ∧
        Tendsto u (cocompact ℝ) (𝓝 0) :=
  ⟨remark_8_24_not_coercive, remark_8_24_exists_not_solvable⟩

/-- **Remark 25** in Chapter 8 of [brezis2011functional], the space. Let $u \in H^1(0, +\infty)$.
Then $u \in H_0^1(0, +\infty)$ if and only if $u(0) = 0$.

This is Theorem 8.12 on the half-line $(0, +\infty)$, whose boundary is $\{0\}$. -/
theorem remark_8_25_space (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)) :
    u ∈ SobolevIntervalLpZero 1 2 (Opens.Ioi 0) ↔ u.rep 0 = 0 := by
  rw [mem_sobolevIntervalLpZero_iff (p := 2) (SobolevIntervalLp.ordConnected_coe_Ioi 0)
    ENNReal.ofNat_ne_top, Opens.coe_Ioi, frontier_Ioi]
  simp

/-- The load $v \mapsto \int_0^\infty fv$ on $H_0^1(0, +\infty)$, as a continuous linear functional.
-/
private def halfLineLoad (f : Lp ℝ 2 (volume.restrict ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ))) :
    SobolevIntervalLpZero 1 2 (Opens.Ioi 0) →L[ℝ] ℝ :=
  (innerSL ℝ f).comp ((SobolevIntervalLp.derivL 1 2 (Opens.Ioi 0) 0).comp
    (SobolevIntervalLpZero 1 2 (Opens.Ioi 0)).subtypeL)

private theorem halfLineLoad_apply
    (f : Lp ℝ 2 (volume.restrict ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ)))
    (v : SobolevIntervalLpZero 1 2 (Opens.Ioi 0)) :
    halfLineLoad f v = ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
      f x * (v : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn x := by
  change ⟪f, SobolevIntervalLp.deriv (v : SobolevIntervalLp 1 2 (Opens.Ioi 0)) 0⟫_ℝ = _
  rw [L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  change ⟪f x, SobolevIntervalLp.deriv (v : SobolevIntervalLp 1 2 (Opens.Ioi 0)) 0 x⟫_ℝ
    = f x * (v : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn x
  rw [RCLike.inner_apply, conj_trivial, mul_comm]
  rfl

/-- **Remark 25** in Chapter 8 of [brezis2011functional], existence and uniqueness of the weak
solution. Consider the problem
$$-u'' + u = f \text{ on } (0, +\infty), \qquad u(0) = 0, \quad u(x) \to 0 \text{ as } x \to
  +\infty,$$
with $f \in L^2(0, +\infty)$. There is exactly one weak solution: exactly one
$u \in H_0^1(0, +\infty)$ with
$$(u, v)_{H^1} = \int_0^\infty fv \quad \text{for all } v \in H_0^1(0, +\infty).$$

The proof is the Lax–Milgram theorem, here the Riesz–Fréchet theorem for the $H^1$ inner product
on the closed subspace $H_0^1(0, +\infty)$. The source says that the same method as in Example 8
applies. -/
theorem remark_8_25_existsUnique
    (f : Lp ℝ 2 (volume.restrict ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ))) :
    ∃! u : SobolevIntervalLpZero 1 2 (Opens.Ioi 0), ∀ v : SobolevIntervalLpZero 1 2 (Opens.Ioi 0),
      ⟪u, v⟫_ℝ = ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
        f x * (v : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn x :=
  ⟨(InnerProductSpace.toDual ℝ (SobolevIntervalLpZero 1 2 (Opens.Ioi 0))).symm (halfLineLoad f),
    fun v ↦ by rw [← halfLineLoad_apply]; exact InnerProductSpace.toDual_symm_apply,
    fun w hw ↦ by
      refine ext_inner_right ℝ fun v ↦ ?_
      rw [hw v, ← halfLineLoad_apply, InnerProductSpace.toDual_symm_apply]⟩

/-- **Remark 25** in Chapter 8 of [brezis2011functional], regularity. Let $f \in L^2(0, +\infty)$,
and let $u \in H_0^1(0, +\infty)$ satisfy $(u, v)_{H^1} = \int_0^\infty fv$ for all
$v \in H_0^1(0, +\infty)$. Then $u'$ has the weak derivative $u - f$ on $(0, +\infty)$, and
$u \in H^2(0, +\infty)$.

Testing the weak equation against $\mathcal{D}((0, +\infty))$ gives
$\int u'\varphi' = \int (f - u)\varphi$, as in Step C. -/
theorem remark_8_25_regularity
    (f : Lp ℝ 2 (volume.restrict ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ)))
    {u : SobolevIntervalLpZero 1 2 (Opens.Ioi 0)}
    (hu : ∀ v : SobolevIntervalLpZero 1 2 (Opens.Ioi 0),
      ⟪u, v⟫_ℝ = ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
        f x * (v : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn x) :
    HasWeakDerivOn (SobolevIntervalLp.deriv (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)) 1)
      (fun x ↦ (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn x - f x) (Opens.Ioi 0) ∧
    MemSobolevIntervalLp (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn 2 2 (Opens.Ioi 0) := by
  obtain ⟨U, hU⟩ : ∃ U : SobolevIntervalLp 1 2 (Opens.Ioi 0), U = u := ⟨_, rfl⟩
  have hweak : HasWeakDerivOn (SobolevIntervalLp.deriv U 1) (fun x ↦ U.fn x - f x)
      (Opens.Ioi 0) := by
    refine hasWeakDerivOn_iff.2 ⟨SobolevIntervalLp.locallyIntegrableOn_deriv U 1,
      ((Lp.memLp (SobolevIntervalLp.deriv U 0)).sub (Lp.memLp f)).locallyIntegrableOn one_le_two,
      fun φ ↦ ?_⟩
    have h := hu ⟨TestFunction.toSobolevIntervalLp 2 φ, TestFunction.toSobolevIntervalLp_mem φ⟩
    rw [Submodule.coe_inner, ← hU, SobolevIntervalLp.inner_eq_integral] at h
    have hφ0 := TestFunction.fn_toSobolevIntervalLp_ae_eq (p := 2) φ
    have hφ1 := TestFunction.coeFn_deriv_toSobolevIntervalLp_one (p := 2) φ
    have e1 : ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
        (U.fn x * (TestFunction.toSobolevIntervalLp 2 φ).fn x
          + SobolevIntervalLp.deriv U 1 x
            * SobolevIntervalLp.deriv (TestFunction.toSobolevIntervalLp 2 φ) 1 x)
        = (∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ), U.fn x * φ x)
          + ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
            SobolevIntervalLp.deriv U 1 x * deriv φ x := by
      rw [← integral_add]
      · refine integral_congr_ae ?_
        filter_upwards [hφ0, hφ1] with x hx0 hx1
        rw [hx0, hx1]
      · exact (Lp.memLp (SobolevIntervalLp.deriv U 0)).integrable_mul (φ.memLp' 2)
      · exact (Lp.memLp (SobolevIntervalLp.deriv U 1)).integrable_mul (φ.memLp_deriv 2)
    have e2 : ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
        f x * (TestFunction.toSobolevIntervalLp 2 φ).fn x
        = ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ), f x * φ x :=
      integral_congr_ae (hφ0.mono fun x hx ↦ by simp only [hx])
    rw [e1, e2] at h
    have e3 : ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ), φ x * (U.fn x - f x)
        = (∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ), U.fn x * φ x)
          - ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ), f x * φ x := by
      rw [← integral_sub]
      · refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        ring
      · exact ((Lp.memLp (SobolevIntervalLp.deriv U 0)).integrable_mul (φ.memLp' 2)).congr
          (Eventually.of_forall fun x ↦ rfl)
      · exact ((Lp.memLp f).integrable_mul (φ.memLp' 2)).congr
          (Eventually.of_forall fun x ↦ rfl)
    rw [e3]
    have e4 : ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
          deriv φ x * SobolevIntervalLp.deriv U 1 x
        = ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
          SobolevIntervalLp.deriv U 1 x * deriv φ x :=
      integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    rw [e4]
    linarith
  rw [← hU]
  refine ⟨hweak, memSobolevIntervalLp_succ_iff.2 ⟨Lp.memLp _, SobolevIntervalLp.deriv U 1,
    U.hasWeakDerivOn_fn, memSobolevIntervalLp_one_iff.2 ⟨Lp.memLp _, _, hweak,
      (Lp.memLp (SobolevIntervalLp.deriv U 0)).sub (Lp.memLp f)⟩⟩⟩

/-- **Remark 25** in Chapter 8 of [brezis2011functional], the boundary condition and the decay at
infinity. Every $u \in H_0^1(0, +\infty)$ satisfies $u(0) = 0$ and $u(x) \to 0$ as
$x \to +\infty$. In particular the weak solution of the half-line problem does.

The decay is Corollary 8.9. -/
theorem remark_8_25_boundary (u : SobolevIntervalLpZero 1 2 (Opens.Ioi 0)) :
    (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)).rep 0 = 0 ∧
      Tendsto (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)).rep atTop (𝓝 0) :=
  ⟨(remark_8_25_space _).1 u.2, SobolevIntervalLp.tendsto_rep_atTop
    (SobolevIntervalLp.ordConnected_coe_Ioi 0) ENNReal.ofNat_ne_top
    (by rw [Opens.coe_Ioi]; exact not_bddAbove_Ioi 0) _⟩

/-- **Remark 25** in Chapter 8 of [brezis2011functional]. The method of Example 8 applies to the
problem
$$-u'' + u = f \text{ on } (0, +\infty), \qquad u(0) = 0, \quad u(x) \to 0 \text{ as } x \to
  +\infty,$$
with $f \in L^2(0, +\infty)$:
* $H_0^1(0, +\infty) = \{u \in H^1(0, +\infty) : u(0) = 0\}$, by Theorem 8.12;
* there is exactly one $u \in H_0^1(0, +\infty)$ with $(u, v)_{H^1} = \int_0^\infty fv$ for all
  $v \in H_0^1(0, +\infty)$;
* this $u$ lies in $H^2(0, +\infty)$, satisfies $u(0) = 0$, and tends to $0$ as $x \to +\infty$
  (Corollary 8.9). -/
theorem remark_8_25 (f : Lp ℝ 2 (volume.restrict ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ))) :
    (∀ u : SobolevIntervalLp 1 2 (Opens.Ioi 0),
      u ∈ SobolevIntervalLpZero 1 2 (Opens.Ioi 0) ↔ u.rep 0 = 0) ∧
    ∃! u : SobolevIntervalLpZero 1 2 (Opens.Ioi 0),
      (∀ v : SobolevIntervalLpZero 1 2 (Opens.Ioi 0),
        ⟪u, v⟫_ℝ = ∫ x in ((Opens.Ioi (0 : ℝ) : Opens ℝ) : Set ℝ),
          f x * (v : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn x) ∧
      MemSobolevIntervalLp (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)).fn 2 2 (Opens.Ioi 0) ∧
      (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)).rep 0 = 0 ∧
      Tendsto (u : SobolevIntervalLp 1 2 (Opens.Ioi 0)).rep atTop (𝓝 0) := by
  obtain ⟨u, hu, huniq⟩ := remark_8_25_existsUnique f
  exact ⟨remark_8_25_space, u, ⟨hu, (remark_8_25_regularity f hu).2, (remark_8_25_boundary u).1,
    (remark_8_25_boundary u).2⟩, fun w hw ↦ huniq w hw.1⟩


end Brezis.Chapter08
