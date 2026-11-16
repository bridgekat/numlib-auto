/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.PDE.Bochner.SpaceTime
import Numlib.Analysis.PDE.DirichletLaplacian
import Numlib.Analysis.PDE.Elliptic.Spectral

/-!
# The heat equation

Let $\Omega \subseteq \mathbb{R}^N$ be open with boundary $\Gamma$. This module studies the heat
equation
$$\partial_t u - \Delta u = 0 \text{ in } \Omega \times (0, \infty), \qquad u = 0 \text{ on } \Gamma
  \times (0, \infty), \qquad u(\cdot, 0) = u_0,$$
in the form of §10.1 of [brezis2011functional]. A solution is a curve
$u : \mathbb{R} \to L^2(\Omega)$ with $u' + Au = 0$ for $t > 0$ and $u(0) = u_0$, where
$A = -\Delta$ is the Dirichlet Laplacian with domain $D(A) = \{u \in H^1_0(\Omega) : \Delta u \in
L^2(\Omega)\}$. The operator $A$ is self-adjoint and maximal monotone, so the Hille–Yosida theory of
Chapter 7 of [brezis2011functional] applies. The solution is $u(t) = S_A(t) u_0$, where $S_A$ is the
contraction semigroup of $A$. The boundary condition is part of the domain:
$D(A) \subseteq H^1_0(\Omega)$.

The module proves Theorems 10.1 and 10.2 and Remarks 1 and 3 of [brezis2011functional]: existence
and uniqueness, the smoothing estimates $\|u(t)\| \le \|u_0\|$ and $\|u'(t)\| \le \|u_0\|/t$, the
regularity of the solution in time and in space, the energy identities, the backward problem, and
the expansion $u(t) = \sum_n e^{-\lambda_n t} \langle u_0, e_n \rangle e_n$ in the Dirichlet
eigenfunctions. The maximum principles of §10.2 are in `Numlib.Analysis.PDE.Heat.MaximumPrinciple`
and `Numlib.Analysis.PDE.Heat.Classical`.

## Main definitions

* `Heat.IsSolution`: $u$ solves the heat equation with datum $u_0$, in the class $C([0, \infty);
  L^2(\Omega)) \cap C^1((0, \infty); L^2(\Omega))$.
* `Heat.solution`: the solution $t \mapsto S_A(t) u_0$.
* `Heat.IsBackwardSolution`: $u$ solves the backward problem $-\partial_t u - \Delta u = 0$ on
  $(-\infty, T)$ with final datum $u(T) = u_T$.

## Main results

* `Heat.existsUnique_isSolution`: Theorem 10.1, existence and uniqueness on every open set.
* `Heat.IsSolution.norm_le`, `Heat.IsSolution.norm_deriv_le`,
  `Heat.IsSolution.norm_iteratedDeriv_le`: $\|u(t)\| \le \|u_0\|$, $\|u'(t)\| \le \|u_0\|/t$ and
  $\|u^{(k)}(t)\| \le (k/t)^k \|u_0\|$.
* `Heat.IsSolution.contDiffOn_top`, `Heat.IsSolution.exists_powDomain`:
  $u \in C^\infty((0, \infty); L^2(\Omega))$ and $u(t) \in D(A^\ell)$ for all $t > 0$ and all
  $\ell$.
* `Heat.IsSolution.energy`, `Heat.IsSolution.integral_inner_apply_le`: the energy identity (6) and
  $\int_0^\infty \|\nabla u(t)\|^2 \, dt \le \frac12 \|u_0\|^2$.
* `Heat.IsSolution.contDiffOnThrough_sobolevZero_of_mem`, `Heat.IsSolution.energy_sobolevZero`:
  Theorem 10.2 (a), $u \in C([0, \infty); H^1_0(\Omega))$ and the identity (11) for
  $u_0 \in H^1_0(\Omega)$.
* `Heat.IsSolution.contDiffOn_Ici_of_mem_domain`, `Heat.IsSolution.energy_domain`: Theorem 10.2 (b)
  for $u_0 \in D(A)$.
* `Heat.IsSolution.contDiffOnPowDomain_Ici_of_powDomain`,
  `Heat.IsSolution.contDiffOnThrough_sobolev_Ici_of_powDomain`: Theorem 10.2 (c) for
  $u_0 \in D(A^k)$.
* `Heat.IsSolution.contDiffOnThrough_sobolev`: $u \in C^\infty((0, \infty); H^{2\ell}(\Omega))$ on a
  domain of class $C^{2\ell}$.
* `Heat.IsSolution.contDiffOnClosure_spaceTime`, `Heat.IsSolution.contDiffOnClosure_spaceTime_Ici`:
  $u \in C^\infty(\overline{\Omega} \times [\varepsilon, \infty))$ for every $\varepsilon > 0$, and
  $u \in C^\infty(\overline{\Omega} \times [0, \infty))$ when $u_0 \in D(A^k)$ for every $k$.
* `Heat.IsSolution.memLpThrough_sobolevZero_of_isBounded`,
  `Heat.IsSolution.memLpThrough_two_of_isBounded`,
  `Heat.IsSolution.memLpThrough_three_of_isBounded`: the memberships
  $u \in L^2(0, \infty; H^1_0(\Omega))$, $L^2(0, \infty; H^2(\Omega))$ and
  $L^2(0, \infty; H^3(\Omega))$ on a bounded $\Omega$.
* `Heat.existsUnique_isSolution_backward`: Remark 1, the backward problem is well posed.
* `Heat.IsSolution.hasSum_eigenfunction`: Remark 3, the expansion (14) of $u(t)$ in the Dirichlet
  eigenfunctions.

## Proof outline

Existence, uniqueness and the estimate $\|u'(t)\| \le \|u_0\|/t$ are Theorem 7.7 of
[brezis2011functional] for $A$. The derivatives are $u^{(j)}(t) = (-A)^j u(t)$, and they are proved
for the semigroup of any self-adjoint maximal monotone operator in
`Numlib.Analysis.ODE.HilleYosida`. There, `LinearPMap.semigroupLift A u₀ ℓ t` is the element of
$D(A^\ell)$ over $S_A(t) u_0$ for $t > 0$. Its coordinates $A^j S_A(t) u_0$ have the derivatives
$-A^{j+1} S_A(t) u_0$ (`LinearPMap.hasDerivAt_applyL_semigroupLift`), and
$\|A^j S_A(t) u_0\| \le (j/t)^j \|u_0\|$ (`LinearPMap.norm_applyL_semigroupLift_le`). The energy
identity (6) holds for any monotone operator (`LinearPMap.IsSolutionOn.energy_Ioi`), with $\langle
Au, u \rangle = \int_\Omega |\nabla u|^2$. For $u_0 \in H^1_0(\Omega)$ the same theory applies to
the realization $A_1$ of $-\Delta$ in $H^1_0(\Omega)$, and uniqueness identifies its solution with
$u$.

## Implementation notes

* $L^2(\Omega)$ is `Lp ℝ 2 (volume.restrict Ω)` for `Ω : Opens (EuclideanSpace ℝ (Fin N))`. The
  solution is the semigroup, `Heat.solution Ω u₀ = fun t ↦ (dirichletLaplacian Ω).semigroup t u₀`,
  so that its linearity in $u_0$ and the contraction property come from Chapter 7.
* [brezis2011functional] reads $u(t)$ as the function $x \mapsto u(x, t)$, an element of
  $L^2(\Omega)$. `Heat.IsSolution` is the solution notion `LinearPMap.IsSolutionOn` of Chapter 7 on
  $(0, \infty)$ together with continuity on $[0, \infty)$ and class $C^1$ on $(0, \infty)$. This is
  the class of Theorem 7.7. The clause $u \in C((0, \infty); D(A))$ follows from the equation.
* With the weak domain $D(A)$, the following results hold on every open set $\Omega$: existence and
  uniqueness, the estimates of $\|u(t)\|$ and $\|u'(t)\|$, the smoothing
  $u \in C^\infty((0, \infty); L^2(\Omega))$ with $u(t) \in D(A^\ell)$, the bounds on
  $\|u^{(k)}(t)\|$, the energy identity (6), Theorem 10.2 (a) with (11), and Theorem 10.2 (b) with
  its identity. They are Theorems 7.4, 7.5 and 7.7 of [brezis2011functional] together with the
  identity $\langle Au, u \rangle = \int_\Omega |\nabla u|^2$.
* The regularity hypothesis of [brezis2011functional] on $\Omega$ is `IsContDiffChartDomain n Ω`
  together with `Bornology.IsBounded (frontier Ω)`. It enters only through the identification of
  $D(A^\ell)$ with a subspace of $H^{2\ell}(\Omega)$ (Theorem 9.25,
  `dirichletLaplacian.powDomainToSobolevL`). That identification gives
  $u \in C^k((0, \infty); H^{2\ell}(\Omega))$ and, with the space–time results of
  `Numlib.Analysis.PDE.Bochner.SpaceTime`, $u \in C^\infty(\overline{\Omega} \times [\varepsilon,
  \infty))$.
* A curve $u : \mathbb{R} \to L^2(\Omega)$ is in $C^k(s; V)$ for a space $V$ that maps continuously
  into $L^2(\Omega)$, such as $H^m(\Omega)$, when it factors on $s$ through a curve of class $C^k$
  into $V$ (`Bochner.ContDiffOnThrough`). The class $L^2(s; V)$ is `Bochner.MemLpThrough` in the
  same way. The class $C^k(s; D(A^j))$ is `LinearPMap.ContDiffOnPowDomain`.
* Theorem 10.1 of [brezis2011functional] states $u \in L^2(0, \infty; H^1_0(\Omega))$, and Theorem
  10.2 states $u \in L^2(0, \infty; H^2(\Omega))$ and $u \in L^2(0, \infty; H^3(\Omega))$. These
  memberships are false on unbounded domains: on $\Omega = \mathbb{R}$ with a Gaussian datum,
  $\|u(t)\|_{L^2}^2$ behaves like $(1 + 2t)^{-1/2}$ and is not integrable in $t$. The proofs of the
  book show $\int_0^\infty \|\nabla u(t)\|^2 \, dt \le \frac12 \|u_0\|^2$, $\int_0^\infty
  \|u'(t)\|^2 \, dt \le \frac12 \|\nabla u_0\|^2$ and $\int_0^\infty \|\nabla \Delta u(t)\|^2 \, dt
  \le \frac12 \|\Delta u_0\|^2$, and these are stated for every open $\Omega$. The memberships
  follow for a bounded $\Omega$ by Poincaré's inequality (Corollary 9.19,
  `SobolevEuclideanZero.norm_le_gradNorm`), and they are stated under `Bornology.IsBounded Ω`.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

/-! ### The solution notion, existence and uniqueness -/

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

variable (Ω) in
/-- A **solution of the heat equation** with datum $u_0 \in L^2(\Omega)$ is a curve
$u : \mathbb{R} \to L^2(\Omega)$ such that $u(0) = u_0$, $u(t) \in D(A)$ and $u'(t) = -A u(t)$
for every $t > 0$, $u$ is continuous on $[0, \infty)$, and $u$ is of class $C^1$ on
$(0, \infty)$. Here $A$ is the Dirichlet Laplacian.

This is the problem (1)–(3) of §10.1 of [brezis2011functional], $\partial_t u - \Delta u = 0$ in
$\Omega \times (0, \infty)$, $u = 0$ on $\Gamma \times (0, \infty)$, $u(\cdot, 0) = u_0$, in the
class (4) of Theorem 10.1, with the weak domain $D(A)$ in place of
$H^2(\Omega) \cap H^1_0(\Omega)$. The equation (1) is the derivative clause, the boundary
condition (2) is $u(t) \in D(A) \subseteq H^1_0(\Omega)$, and (3) is $u(0) = u_0$.

The first three conditions are the solution notion `LinearPMap.IsSolutionOn` of Chapter 7 on
$(0, \infty)$. The clause $u \in C((0, \infty); D(A))$ follows
(`Heat.IsSolution.continuousOn_apply`), because $Au(t) = -u'(t)$. The definition puts no
condition on $u(t)$ for $t < 0$. -/
structure IsSolution (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : Prop where
  /-- The curve solves $u' + Au = 0$ on $(0, \infty)$ with $u(0) = u_0$ and $u(t) \in D(A)$ for
  $t > 0$. -/
  toIsSolutionOn : (dirichletLaplacian Ω).IsSolutionOn u₀ (Ioi 0) u
  /-- The curve is continuous on $[0, \infty)$: $u \in C([0, \infty); L^2(\Omega))$. -/
  continuousOn : ContinuousOn u (Ici 0)
  /-- The curve is of class $C^1$ on $(0, \infty)$: $u \in C^1((0, \infty); L^2(\Omega))$. -/
  contDiffOn : ContDiffOn ℝ 1 u (Ioi 0)

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u v : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- A solution satisfies the initial condition (3): $u(0) = u_0$. -/
theorem apply_zero (h : IsSolution Ω u₀ u) : u 0 = u₀ := h.toIsSolutionOn.apply_zero

/-- A solution satisfies the boundary condition (2): $u(t) \in D(A) \subseteq H^1_0(\Omega)$ for
every $t > 0$. -/
theorem mem_domain (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    u t ∈ (dirichletLaplacian Ω).domain :=
  h.toIsSolutionOn.mem_domain t ht

/-- A solution satisfies the equation (1): for every $t > 0$, $u$ is differentiable at $t$ with
$u'(t) = -A u(t) = \Delta u(t)$. -/
theorem hasDerivAt (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    HasDerivAt u (-(dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩)) t :=
  (h.toIsSolutionOn.hasDerivWithinAt t ht).hasDerivAt (Ioi_mem_nhds ht)

/-- For a solution $u$ and $t > 0$, the derivative is $u'(t) = -A u(t)$. -/
theorem deriv_eq (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    deriv u t = -(dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩) :=
  (h.hasDerivAt ht).deriv

/-- **Uniqueness** in Theorem 10.1 of [brezis2011functional]: two solutions $u$ and $v$ with the
same datum $u_0$ agree on $[0, \infty)$.

This is Step 1 of the proof in Chapter 7: $\|u - v\|$ is nonincreasing on $(0, \infty)$ because
$A$ is monotone, it is continuous on $[0, \infty)$, and it is zero at $0$. -/
theorem unique (h : IsSolution Ω u₀ u) (h' : IsSolution Ω u₀ v) : EqOn u v (Ici 0) :=
  dirichletLaplacian_isMonotone.eqOn_of_isSolutionOn_Ioi h.toIsSolutionOn h'.toIsSolutionOn
    h.continuousOn h'.continuousOn

end IsSolution

variable (Ω) in
/-- The **solution of the heat equation** with datum $u_0 \in L^2(\Omega)$: the curve
$t \mapsto S_A(t) u_0$, where $S_A$ is the contraction semigroup of the Dirichlet Laplacian $A$
(Remark 5 of Chapter 7 of [brezis2011functional]). -/
def solution (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))) :=
  fun t ↦ (dirichletLaplacian Ω).semigroup t u₀

variable (u₀ v₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))

/-- The solution with datum $u_0$ is $S_A(t) u_0$ at every time $t$. -/
theorem solution_apply (t : ℝ) : solution Ω u₀ t = (dirichletLaplacian Ω).semigroup t u₀ :=
  rfl

/-- The solution is additive in the datum: the solution with datum $u_0 + v_0$ is the sum of the
solutions with data $u_0$ and $v_0$. -/
theorem solution_add (t : ℝ) : solution Ω (u₀ + v₀) t = solution Ω u₀ t + solution Ω v₀ t :=
  map_add _ _ _

/-- The solution is homogeneous in the datum: the solution with datum $c u_0$ is $c$ times the
solution with datum $u_0$, for $c \in \mathbb{R}$. -/
theorem solution_smul (c : ℝ) (t : ℝ) : solution Ω (c • u₀) t = c • solution Ω u₀ t :=
  map_smul _ _ _

/-- The solution with datum $u_0 - v_0$ is the difference of the solutions with data $u_0$ and
$v_0$. -/
theorem solution_sub (t : ℝ) : solution Ω (u₀ - v₀) t = solution Ω u₀ t - solution Ω v₀ t :=
  map_sub _ _ _

/-- The solution with datum $0$ is $0$. -/
theorem solution_zero (t : ℝ) : solution Ω 0 t = 0 :=
  map_zero _

/-- The **contraction property**: the solution with datum $u_0$ satisfies $\|u(t)\| \le \|u_0\|$ for
every $t \ge 0$.

This is Remark 5 (a) of Chapter 7 of [brezis2011functional]. Applied to differences of solutions
it is the estimate in the proof of Corollary 10.5. -/
theorem norm_solution_le {t : ℝ} (ht : 0 ≤ t) : ‖solution Ω u₀ t‖ ≤ ‖u₀‖ :=
  dirichletLaplacian_isMaximalMonotone.norm_semigroup_apply_le ht u₀

/-- **Existence** in Theorem 10.1 of [brezis2011functional]: on every open set $\Omega$ and for
every $u_0 \in L^2(\Omega)$, the curve $t \mapsto S_A(t) u_0$ is a solution of the heat equation
with datum $u_0$.

The proof is Theorem 7.7 for the self-adjoint maximal monotone Dirichlet Laplacian
(`LinearPMap.isSolutionOn_semigroup_Ioi`). -/
theorem isSolution_solution : IsSolution Ω u₀ (solution Ω u₀) :=
  let h := isSolutionOn_semigroup_Ioi dirichletLaplacian_isMaximalMonotone
    dirichletLaplacian_isFormalAdjoint u₀
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- Theorem 10.1 of [brezis2011functional], existence and uniqueness, on an arbitrary open set
$\Omega$: for every $u_0 \in L^2(\Omega)$ there is a solution $u$ of the heat equation with
datum $u_0$, and every solution with datum $u_0$ agrees with $u$ on $[0, \infty)$.

Uniqueness holds only on $[0, \infty)$ because `Heat.IsSolution` puts no condition on negative
times. -/
theorem existsUnique_isSolution :
    ∃ u, IsSolution Ω u₀ u ∧ ∀ v, IsSolution Ω u₀ v → EqOn v u (Ici 0) :=
  ⟨solution Ω u₀, isSolution_solution u₀, fun _ hv ↦ hv.unique (isSolution_solution u₀)⟩

variable {u₀ v₀}

namespace IsSolution

variable {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- Every solution with datum $u_0$ agrees on $[0, \infty)$ with the semigroup solution
$t \mapsto S_A(t) u_0$. -/
theorem eqOn_solution (h : IsSolution Ω u₀ u) : EqOn u (solution Ω u₀) (Ici 0) :=
  h.unique (isSolution_solution u₀)

/-- A solution with datum $u_0$ satisfies $u(t) = S_A(t) u_0$ for every $t \ge 0$. -/
theorem apply_eq (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 ≤ t) :
    u t = (dirichletLaplacian Ω).semigroup t u₀ :=
  h.eqOn_solution ht

/-- A solution satisfies $\|u(t)\| \le \|u_0\|$ for every $t \ge 0$. This is the first estimate of
Theorem 7.7 of [brezis2011functional]. -/
theorem norm_le (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 ≤ t) : ‖u t‖ ≤ ‖u₀‖ := by
  rw [h.eqOn_solution ht]
  exact norm_solution_le u₀ ht

/-- The **smoothing estimate**: a solution satisfies $\|A u(t)\| \le \|u_0\| / t$ for every $t > 0$.
This is (26) of Theorem 7.7 of [brezis2011functional]. -/
theorem norm_apply_le (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    ‖dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩‖ ≤ ‖u₀‖ / t := by
  obtain ⟨hmem, hb⟩ := semigroup_apply_mem_domain_of_isFormalAdjoint
    dirichletLaplacian_isMaximalMonotone dirichletLaplacian_isFormalAdjoint u₀ ht
  have : (⟨u t, h.mem_domain ht⟩ : (dirichletLaplacian Ω).domain)
      = ⟨(dirichletLaplacian Ω).semigroup t u₀, hmem⟩ := Subtype.ext (h.apply_eq ht.le)
  rw [this]
  exact hb

/-- The **parabolic smoothing bound**: a solution satisfies $\|u'(t)\| \le \|u_0\| / t$ for every
$t > 0$. This is (26) of Theorem 7.7 of [brezis2011functional], since $u'(t) = -A u(t)$. -/
theorem norm_deriv_le (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) : ‖deriv u t‖ ≤ ‖u₀‖ / t := by
  rw [h.deriv_eq ht, norm_neg]
  exact h.norm_apply_le ht

/-- **Smoothing in time**, in the form of Chapter 7: a solution lies in
$C^k((0, \infty); D(A^\ell))$ for all $k, \ell \in \mathbb{N}$. This is (27) of Theorem 7.7 of
[brezis2011functional].

The class $C^k((0, \infty); D(A^\ell))$ is `LinearPMap.ContDiffOnPowDomain`. -/
theorem contDiffOnPowDomain (h : IsSolution Ω u₀ u) (k ℓ : ℕ) :
    (dirichletLaplacian Ω).ContDiffOnPowDomain k ℓ u (Ioi 0) :=
  (contDiffOnPowDomain_semigroup_Ioi dirichletLaplacian_isMaximalMonotone
    dirichletLaplacian_isFormalAdjoint u₀ k ℓ).congr fun _ ht ↦ (h.apply_eq (le_of_lt ht)).symm

/-- A solution lies in $C((0, \infty); D(A))$, in the form `LinearPMap.ContDiffOnPowDomain` of
Chapter 7. -/
theorem contDiffOnPowDomain_one (h : IsSolution Ω u₀ u) :
    (dirichletLaplacian Ω).ContDiffOnPowDomain 0 1 u (Ioi 0) :=
  h.contDiffOnPowDomain 0 1

/-- A solution lies in $C((0, \infty); D(A))$: every function $g$ with $g(t) = A u(t)$ for all
$t > 0$ is continuous on $(0, \infty)$. This is part of the class (4) of Theorem 10.1 of
[brezis2011functional].

The proof is $A u(t) = -u'(t)$. -/
theorem continuousOn_apply (h : IsSolution Ω u₀ u)
    {g : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    (hg : ∀ t (ht : 0 < t), g t = dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩) :
    ContinuousOn g (Ioi 0) := by
  refine (h.contDiffOn.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).neg.congr fun t ht ↦ ?_
  change g t = -deriv u t
  rw [hg t ht, h.deriv_eq ht, neg_neg]

/-- A solution satisfies $u(t) \in D(A^\ell)$ for every $t > 0$ and every $\ell \in \mathbb{N}$:
there is $x \in D(A^\ell)$ whose $0$-th coordinate is $u(t)$.

This follows from Theorem 7.7 of [brezis2011functional]. It is the necessary condition (12) on
final data in Remark 1 of Chapter 10. -/
theorem exists_powDomain (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) (ℓ : ℕ) :
    ∃ x : (dirichletLaplacian Ω).PowDomain ℓ, applyL (dirichletLaplacian Ω) ℓ 0 x = u t := by
  rw [h.apply_eq ht.le]
  exact exists_powDomain_semigroup_apply_of_isFormalAdjoint dirichletLaplacian_isMaximalMonotone
    dirichletLaplacian_isFormalAdjoint u₀ ℓ ht

/-- **Smoothing in time**: a solution lies in $C^\infty((0, \infty); L^2(\Omega))$. This is part of
Theorem 10.1 of [brezis2011functional]. -/
theorem contDiffOn_top (h : IsSolution Ω u₀ u) : ContDiffOn ℝ ∞ u (Ioi 0) := by
  refine contDiffOn_infty.2 fun k ↦ ?_
  obtain ⟨w, hw0, hw⟩ := h.contDiffOnPowDomain k 0
  exact ((applyL (dirichletLaplacian Ω) 0 0).contDiff.comp_contDiffOn hw).congr
    fun t ht ↦ (hw0 t ht).symm

/-- For a solution $u$, $t > 0$ and $\ell \in \mathbb{N}$, the curve $u$ agrees near $t$ with
$\tau \mapsto x_0(\tau)$, the $0$-th coordinate of the lift `LinearPMap.semigroupLift` of
$S_A(\tau) u_0$ into $D(A^\ell)$. -/
theorem eventuallyEq_applyL_semigroupLift (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) (ℓ : ℕ) :
    u =ᶠ[𝓝 t] fun τ ↦ applyL (dirichletLaplacian Ω) ℓ 0
      (semigroupLift (dirichletLaplacian Ω) u₀ ℓ τ) := by
  filter_upwards [Ioi_mem_nhds ht] with τ hτ
  rw [applyL_zero_semigroupLift dirichletLaplacian_isMaximalMonotone
    dirichletLaplacian_isFormalAdjoint hτ, h.apply_eq (le_of_lt hτ)]

/-- **The derivatives are the iterates.** For a solution $u$, $\ell \in \mathbb{N}$, $j \le \ell$
and $t > 0$,
$$u^{(j)}(t) = (-1)^j A^j u(t),$$
where $A^j u(t)$ is the $j$-th coordinate of the lift `LinearPMap.semigroupLift` of $u(t)$ into
$D(A^\ell)$.

The proof is an induction on $j$ with `LinearPMap.hasDerivAt_applyL_semigroupLift`. -/
theorem iteratedDeriv_eq_applyL_semigroupLift (h : IsSolution Ω u₀ u) (ℓ : ℕ) :
    ∀ j : ℕ, ∀ hj : j ≤ ℓ, ∀ t : ℝ, 0 < t → iteratedDeriv j u t
      = (-1 : ℝ) ^ j • applyL (dirichletLaplacian Ω) ℓ ⟨j, Nat.lt_succ_of_le hj⟩
        (semigroupLift (dirichletLaplacian Ω) u₀ ℓ t) := by
  intro j
  induction j with
  | zero =>
    intro _ t ht
    rw [iteratedDeriv_zero, pow_zero, one_smul]
    exact (h.eventuallyEq_applyL_semigroupLift ht ℓ).eq_of_nhds
  | succ j ih =>
    intro hj t ht
    have hj' : j ≤ ℓ := Nat.le_of_succ_le hj
    have hloc : iteratedDeriv j u =ᶠ[𝓝 t] fun τ ↦ (-1 : ℝ) ^ j •
        applyL (dirichletLaplacian Ω) ℓ ⟨j, Nat.lt_succ_of_le hj'⟩
          (semigroupLift (dirichletLaplacian Ω) u₀ ℓ τ) := by
      filter_upwards [Ioi_mem_nhds ht] with τ hτ
      exact ih hj' τ hτ
    have hd : HasDerivAt (fun τ ↦ (-1 : ℝ) ^ j •
        applyL (dirichletLaplacian Ω) ℓ ⟨j, Nat.lt_succ_of_le hj'⟩
          (semigroupLift (dirichletLaplacian Ω) u₀ ℓ τ))
        ((-1 : ℝ) ^ j • -(applyL (dirichletLaplacian Ω) ℓ ⟨j + 1, Nat.lt_succ_of_le hj⟩
          (semigroupLift (dirichletLaplacian Ω) u₀ ℓ t))) t :=
      (hasDerivAt_applyL_semigroupLift dirichletLaplacian_isMaximalMonotone
        dirichletLaplacian_isFormalAdjoint (u₀ := u₀) ht ⟨j, Nat.lt_of_succ_le hj⟩).const_smul
        ((-1 : ℝ) ^ j)
    rw [iteratedDeriv_succ, hloc.deriv_eq, hd.deriv, smul_neg, pow_succ, mul_neg, mul_one,
      neg_smul]

/-- For a solution $u$, $t > 0$, any $x \in D(A^\ell)$ whose $0$-th coordinate is $u(t)$, and
$j \le \ell$,
$$u^{(j)}(t) = (-1)^j A^j x,$$
where $A^j x$ is the $j$-th coordinate of $x$. This is the identity $u^{(j)} = (-A)^j u$ on
$(0, \infty)$ stated after (7) in §10.1 of [brezis2011functional]. -/
theorem iteratedDeriv_eq (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) {ℓ : ℕ}
    (x : (dirichletLaplacian Ω).PowDomain ℓ) (hx : applyL (dirichletLaplacian Ω) ℓ 0 x = u t)
    (j : Fin (ℓ + 1)) :
    iteratedDeriv j u t = (-1 : ℝ) ^ (j : ℕ) • applyL (dirichletLaplacian Ω) ℓ j x := by
  have hx' : x = semigroupLift (dirichletLaplacian Ω) u₀ ℓ t :=
    eq_semigroupLift dirichletLaplacian_isMaximalMonotone dirichletLaplacian_isFormalAdjoint ht
      (hx.trans (h.apply_eq ht.le))
  rw [hx']
  exact h.iteratedDeriv_eq_applyL_semigroupLift ℓ j (Nat.lt_succ_iff.1 j.2) t ht

/-- **Parabolic smoothing of every order**: a solution satisfies, for every $t > 0$ and
$k \in \mathbb{N}$,
$$\|u^{(k)}(t)\| \le \left(\frac{k}{t}\right)^k \|u_0\|.$$

This bound is not in [brezis2011functional]. It is the bound $\|u_t(t)\| \le C \|u_0\| / t$ used
in error analyses of parabolic problems. The proof applies the bound $\|A u(s)\| \le \|u_0\|/s$
along the subdivision $0 < t/k < 2t/k < \dots < t$ with the semigroup law
(`LinearPMap.norm_applyL_semigroupLift_le`). -/
theorem norm_iteratedDeriv_le (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ‖iteratedDeriv k u t‖ ≤ ((k : ℝ) / t) ^ k * ‖u₀‖ := by
  have := h.iteratedDeriv_eq_applyL_semigroupLift k k le_rfl t ht
  rw [this, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hb := norm_applyL_semigroupLift_le dirichletLaplacian_isMaximalMonotone
    dirichletLaplacian_isFormalAdjoint (u₀ := u₀) (ℓ := k) ht ⟨k, Nat.lt_succ_self k⟩
  exact hb

/-- **The energy identity** (6) of Theorem 10.1 of [brezis2011functional]. Let $u$ be a solution,
let $T > 0$, and let $g(t) = \langle A u(t), u(t) \rangle = \int_\Omega |\nabla u(t)|^2$ for
$t > 0$. Then $g$ is integrable on $(0, T]$ and
$$\frac12 \|u(T)\|^2 + \int_0^T g(t) \, dt = \frac12 \|u_0\|^2.$$

The identity $\langle Au, u \rangle = \int_\Omega |\nabla u|^2$ is
`dirichletLaplacian_inner_self_eq_dirichletForm`. The proof is
`LinearPMap.IsSolutionOn.energy_Ioi`. -/
theorem energy (h : IsSolution Ω u₀ u) {g : ℝ → ℝ}
    (hg : ∀ t (ht : 0 < t), g t = ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩, u t⟫_ℝ)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn g (Ioc 0 T) ∧
      1 / 2 * ‖u T‖ ^ 2 + ∫ t in (0 : ℝ)..T, g t = 1 / 2 * ‖u₀‖ ^ 2 :=
  IsSolutionOn.energy_Ioi dirichletLaplacian_isMonotone h.toIsSolutionOn h.continuousOn
    h.contDiffOn hg hT

/-- The gradient part of $u \in L^2(0, \infty; H^1_0(\Omega))$ in Theorem 10.1 of
[brezis2011functional]. Let $u$ be a solution and let $g(t) = \langle A u(t), u(t) \rangle =
\int_\Omega |\nabla u(t)|^2$ for $t > 0$. Then $g$ is integrable on $(0, \infty)$ and
$$\int_0^\infty g(t) \, dt \le \frac12 \|u_0\|^2.$$

The proof is the energy identity for every $T$ and $\|u(T)\|^2 \ge 0$. -/
theorem integral_inner_apply_le (h : IsSolution Ω u₀ u) {g : ℝ → ℝ}
    (hg : ∀ t (ht : 0 < t), g t = ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩, u t⟫_ℝ) :
    IntegrableOn g (Ioi 0) ∧ ∫ t in Ioi 0, g t ≤ 1 / 2 * ‖u₀‖ ^ 2 := by
  have hg0 : ∀ t, 0 < t → 0 ≤ g t := fun t ht ↦ by
    rw [hg t ht]
    exact dirichletLaplacian_inner_self_nonneg _
  have hT : ∀ T : ℝ, 0 < T → ∫ t in (0 : ℝ)..T, g t ≤ 1 / 2 * ‖u₀‖ ^ 2 := fun T hT ↦ by
    have := (h.energy hg hT).2
    nlinarith [norm_nonneg (u T)]
  exact integrableOn_Ioi_and_integral_le_of_forall_integral_le hg0
    (fun T hT ↦ (h.energy hg hT).1) hT

end IsSolution

end Heat

/-! ### The second derivative, and the $H^1_0$-lift of $D(A)$ -/

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- For a solution $u$ and $t > 0$, $u'(t) = -A u(t)$, where $A u(t)$ is the first coordinate of the
lift `LinearPMap.semigroupLift` of $u(t)$ into $D(A^2)$. -/
theorem deriv_eq_neg_applyL_semigroupLift (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    deriv u t = -applyL (dirichletLaplacian Ω) 2 1
      (semigroupLift (dirichletLaplacian Ω) u₀ 2 t) := by
  have := h.iteratedDeriv_eq_applyL_semigroupLift 2 1 (by norm_num) t ht
  rwa [iteratedDeriv_one, pow_one, neg_one_smul] at this

/-- For a solution $u$ and $t > 0$, $u'(t) \in D(A)$. The proof is $u'(t) = -A u(t)$ and
$u(t) \in D(A^2)$. -/
theorem deriv_mem_domain (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    deriv u t ∈ (dirichletLaplacian Ω).domain := by
  rw [h.deriv_eq_neg_applyL_semigroupLift ht]
  exact neg_mem (applyL_mem_domain _ 1)

/-- **The equation for the derivative**: for a solution $u$ and $t > 0$, the derivative $u'$ is
differentiable at $t$ with $u''(t) = -A u'(t)$.

The proof writes $u'(t) = -A u(t)$ as a coordinate of the lift of $u(t)$ into $D(A^2)$, whose
coordinates are differentiable (`LinearPMap.hasDerivAt_applyL_semigroupLift`). -/
theorem hasDerivAt_deriv (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv u) (-(dirichletLaplacian Ω ⟨deriv u t, h.deriv_mem_domain ht⟩)) t := by
  have hloc : deriv u =ᶠ[𝓝 t] fun τ ↦ -applyL (dirichletLaplacian Ω) 2 1
      (semigroupLift (dirichletLaplacian Ω) u₀ 2 τ) := by
    filter_upwards [Ioi_mem_nhds ht] with τ hτ
    exact h.deriv_eq_neg_applyL_semigroupLift hτ
  have hd := (hasDerivAt_applyL_semigroupLift dirichletLaplacian_isMaximalMonotone
    dirichletLaplacian_isFormalAdjoint (u₀ := u₀) ht (1 : Fin 2)).neg
  rw [neg_neg] at hd
  refine (hd.congr_of_eventuallyEq hloc).congr_deriv ?_
  have e1 : (⟨deriv u t, h.deriv_mem_domain ht⟩ : (dirichletLaplacian Ω).domain)
      = -⟨applyL (dirichletLaplacian Ω) 2 1 (semigroupLift (dirichletLaplacian Ω) u₀ 2 t),
          applyL_mem_domain _ 1⟩ :=
    Subtype.ext (h.deriv_eq_neg_applyL_semigroupLift ht)
  rw [e1, LinearPMap.map_neg, neg_neg]
  exact (apply_applyL _ 1).symm

/-- For a solution $u$ and $t > 0$, $\langle A u'(t), u(t) \rangle = -\|u'(t)\|^2$.

The proof uses the symmetry of $A$ and $u' = -Au$. -/
theorem inner_apply_deriv_eq (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    ⟪dirichletLaplacian Ω ⟨deriv u t, h.deriv_mem_domain ht⟩, u t⟫_ℝ = -‖deriv u t‖ ^ 2 := by
  have hFA := dirichletLaplacian_isFormalAdjoint ⟨deriv u t, h.deriv_mem_domain ht⟩
    ⟨u t, h.mem_domain ht⟩
  have e2 : dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩ = -deriv u t := by
    rw [h.deriv_eq ht, neg_neg]
  rw [e2] at hFA
  refine hFA.trans ?_
  change ⟪deriv u t, -deriv u t⟫_ℝ = -‖deriv u t‖ ^ 2
  rw [inner_neg_right, real_inner_self_eq_norm_sq]

end IsSolution

end Heat

/-! ### Theorem 10.2 (a): $u_0 \in H^1_0(\Omega)$ -/

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- **The solution of the realization in $H^1_0(\Omega)$ is a solution in $L^2(\Omega)$.** Let
$v_0 \in H^1_0(\Omega)$ have the function $u_0$, and let $w : \mathbb{R} \to H^1_0(\Omega)$
satisfy $w' + A_1 w = 0$ on $(0, \infty)$ with $w(0) = v_0$, be continuous on $[0, \infty)$ and
of class $C^1$ on $(0, \infty)$. Here $A_1$ is the Dirichlet Laplacian in $H^1_0(\Omega)$
(`dirichletLaplacianH10`). Then the curve of the functions of $w(t)$ is a solution of the heat
equation in $L^2(\Omega)$ with datum $u_0$.

The proof uses `fnL_dirichletLaplacianH10_apply`. -/
theorem _root_.Heat.isSolution_fnL_of_isSolutionOn_H10 {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) {w : ℝ → SobolevEuclideanZero N 1 2 Ω}
    (hw : (dirichletLaplacianH10 Ω).IsSolutionOn v₀ (Ioi 0) w) (hwc : ContinuousOn w (Ici 0))
    (hwd : ContDiffOn ℝ 1 w (Ioi 0)) :
    IsSolution Ω u₀ fun t ↦ SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
      1 2 Ω volume (w t) where
  toIsSolutionOn :=
    { apply_zero := by rw [hw.apply_zero, hv₀]
      mem_domain := fun t ht ↦ (hw.mem_domain t ht).1
      hasDerivWithinAt := fun t ht ↦ by
        have h1 := (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
          volume).hasFDerivAt.comp_hasDerivWithinAt t (hw.hasDerivWithinAt t ht)
        exact h1.congr_deriv ((_root_.map_neg _ _).trans
          (congrArg Neg.neg (fnL_dirichletLaplacianH10_apply ⟨w t, hw.mem_domain t ht⟩))) }
  continuousOn := (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
    volume).continuous.comp_continuousOn hwc
  contDiffOn := (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
    volume).contDiff.comp_contDiffOn hwd

/-- The first clause of Theorem 10.2 (a) of [brezis2011functional]. Let $u$ be a solution with datum
$u_0$, and let $u_0$ be the function of some $v_0 \in H^1_0(\Omega)$. Then
$u \in C([0, \infty); H^1_0(\Omega))$: on $[0, \infty)$, $u$ is the function of a continuous
curve in $H^1_0(\Omega)$. This holds on every open set $\Omega$.

Theorem 7.7 for the self-adjoint maximal monotone operator $A_1$ = `dirichletLaplacianH10 Ω` in
the Hilbert space $H^1_0(\Omega)$ gives $w \in C([0, \infty); H^1_0(\Omega))$ with
$w' + A_1 w = 0$ and $w(0) = v_0$. The functions of $w(t)$ form a solution in $L^2(\Omega)$,
which is $u$ by uniqueness. -/
theorem contDiffOnThrough_sobolevZero_of_mem (h : IsSolution Ω u₀ u)
    {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) :
    Bochner.ContDiffOnThrough (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume) 0 u (Ici 0) := by
  have h4 := isSolutionOn_semigroup_Ioi dirichletLaplacianH10_isMaximalMonotone
    dirichletLaplacianH10_isFormalAdjoint v₀
  have hsol := Heat.isSolution_fnL_of_isSolutionOn_H10 hv₀ h4.1 h4.2.1 h4.2.2.1
  exact ⟨_, contDiffOn_zero.2 h4.2.1, fun t ht ↦ h.unique hsol ht⟩

/-- Let $u$ be a solution with datum $u_0$, and let $u_0$ be the function of
$v_0 \in H^1_0(\Omega)$. Then for every $t \ge 0$, $u(t)$ is the function of
$S_{A_1}(t) v_0 \in H^1_0(\Omega)$, where $S_{A_1}$ is the semigroup of the Dirichlet Laplacian
$A_1$ in $H^1_0(\Omega)$. -/
theorem apply_eq_fnL_semigroup_H10 (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) {t : ℝ} (ht : 0 ≤ t) :
    u t = SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      ((dirichletLaplacianH10 Ω).semigroup t v₀) := by
  have h4 := isSolutionOn_semigroup_Ioi dirichletLaplacianH10_isMaximalMonotone
    dirichletLaplacianH10_isFormalAdjoint v₀
  have hsol := Heat.isSolution_fnL_of_isSolutionOn_H10 hv₀ h4.1 h4.2.1 h4.2.2.1
  exact h.unique hsol ht

/-- Let $u$ be a solution with datum $u_0$, let $u_0$ be the function of $v_0 \in H^1_0(\Omega)$,
and let $t > 0$. Then the function of the $0$-th coordinate of the lift of $S_{A_1}(t) v_0$ into
$D(A_1)$ is $u(t)$. -/
theorem fnL_applyL_zero_semigroupLift_H10 (h : IsSolution Ω u₀ u)
    {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) {t : ℝ} (ht : 0 < t) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (applyL (dirichletLaplacianH10 Ω) 1 0 (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t))
      = u t :=
  (congrArg _ (applyL_zero_semigroupLift dirichletLaplacianH10_isMaximalMonotone
    dirichletLaplacianH10_isFormalAdjoint ht)).trans (h.apply_eq_fnL_semigroup_H10 hv₀ ht.le).symm

/-- Let $u$ be a solution with datum $u_0$, let $u_0$ be the function of $v_0 \in H^1_0(\Omega)$,
and let $t > 0$. Then the function of the first coordinate of the lift $y$ of $S_{A_1}(t) v_0$
into $D(A_1)$ is $-u'(t)$.

The proof is that the function of $A_1 y$ is $A$ applied to the function of $y$, which is
$A u(t) = -u'(t)$. -/
theorem fnL_applyL_one_semigroupLift_H10 (h : IsSolution Ω u₀ u)
    {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) {t : ℝ} (ht : 0 < t) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume
      (applyL (dirichletLaplacianH10 Ω) 1 1 (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t))
      = -deriv u t := by
  have h1 := apply_applyL (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t) 0
  have hmem := applyL_mem_domain (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t) 0
  have h2 := fnL_dirichletLaplacianH10_apply ⟨applyL (dirichletLaplacianH10 Ω) 1 0
    (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t), hmem⟩
  have h3 : (⟨SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω
      volume (applyL (dirichletLaplacianH10 Ω) 1 0 (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1
        t)), hmem.1⟩ : (dirichletLaplacian Ω).domain) = ⟨u t, h.mem_domain ht⟩ :=
    Subtype.ext (h.fnL_applyL_zero_semigroupLift_H10 hv₀ ht)
  have h4 := congrArg (fun z : (dirichletLaplacian Ω).domain ↦ dirichletLaplacian Ω z) h3
  exact (congrArg _ h1.symm).trans (h2.trans (h4.trans (neg_eq_iff_eq_neg.1 (h.deriv_eq ht).symm)))

/-- For a solution $u$, $t > 0$ and any $v \in H^1_0(\Omega)$ whose function is $u(t)$,
$$\langle A u(t), u(t) \rangle = \int_\Omega |\nabla v|^2.$$
-/
theorem inner_apply_self_eq_dirichletForm (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t)
    {v : SobolevEuclideanZero N 1 2 Ω}
    (hv : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v
      = u t) :
    ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩, u t⟫_ℝ
      = dirichletForm Ω (v : SobolevEuclidean N 1 2 Ω) (v : SobolevEuclidean N 1 2 Ω) :=
  dirichletLaplacian_inner_self_eq_dirichletForm ⟨u t, h.mem_domain ht⟩ v.2 hv

/-- For a solution $u$ and $t > 0$, $-\frac12 \langle u'(t), u(t) \rangle = \frac12 \langle A u(t),
u(t) \rangle$.

The left side is the function $\varphi(t) = \frac12 \|\nabla u(t)\|^2$ of the proof of Theorem
10.2 (a) of [brezis2011functional], written without the proof that $u(t) \in D(A)$. -/
theorem neg_half_inner_deriv_eq (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    -(1 / 2) * ⟪deriv u t, u t⟫_ℝ
      = 1 / 2 * ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩, u t⟫_ℝ := by
  rw [h.deriv_eq ht, inner_neg_left]
  ring

/-- For a solution $u$ and $t > 0$, the function $\varphi(t) = -\frac12 \langle u'(t), u(t)
\rangle$, which is $\frac12 \|\nabla u(t)\|^2$, has the derivative $\varphi'(t) = -\|u'(t)\|^2$.

This is the computation in the proof of Theorem 10.2 (a) of [brezis2011functional]. It uses
$u'' = -Au'$ and the symmetry of $A$. -/
theorem hasDerivAt_neg_half_inner_deriv (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t ↦ -(1 / 2) * ⟪deriv u t, u t⟫_ℝ) (-(‖deriv u t‖ ^ 2)) t := by
  have := ((h.hasDerivAt_deriv ht).inner ℝ (h.hasDerivAt ht)).const_mul (-(1 / 2))
  convert this using 1
  rw [← h.deriv_eq ht, inner_neg_left, h.inner_apply_deriv_eq ht, real_inner_self_eq_norm_sq]
  ring

/-- Let $u$ be a solution with datum $u_0$, and let $u_0$ be the function of
$v_0 \in H^1_0(\Omega)$. Then $-\frac12 \langle u'(t), u(t) \rangle \to \frac12 \int_\Omega
|\nabla v_0|^2$ as $t \to 0^+$.

This is the continuity of $u$ into $H^1_0(\Omega)$ at $0$ from Theorem 10.2 (a), since the left
side is $\frac12 \|\nabla u(t)\|^2$. -/
theorem tendsto_neg_half_inner_deriv_of_mem (h : IsSolution Ω u₀ u)
    {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) :
    Tendsto (fun t ↦ -(1 / 2) * ⟪deriv u t, u t⟫_ℝ) (𝓝[>] 0)
      (𝓝 (1 / 2 * dirichletForm Ω (v₀ : SobolevEuclidean N 1 2 Ω)
        (v₀ : SobolevEuclidean N 1 2 Ω))) := by
  obtain ⟨w, hw, huw⟩ := h.contDiffOnThrough_sobolevZero_of_mem hv₀
  rw [contDiffOn_zero] at hw
  have hw0 : w 0 = v₀ := SobolevMultiIndexZero.fnL_injective
    ((huw 0 self_mem_Ici).symm.trans (h.apply_zero.trans hv₀.symm))
  have hw' : ContinuousOn (fun t ↦ (w t : SobolevEuclidean N 1 2 Ω)) (Ici 0) :=
    continuous_subtype_val.comp_continuousOn hw
  have hwc : ContinuousOn (fun t ↦ 1 / 2 * dirichletForm Ω (w t : SobolevEuclidean N 1 2 Ω)
      (w t : SobolevEuclidean N 1 2 Ω)) (Ici 0) :=
    continuousOn_const.mul (((dirichletForm Ω).continuous.comp_continuousOn hw').clm_apply hw')
  have h1 : Tendsto (fun t ↦ 1 / 2 * dirichletForm Ω (w t : SobolevEuclidean N 1 2 Ω)
      (w t : SobolevEuclidean N 1 2 Ω)) (𝓝[>] 0)
      (𝓝 (1 / 2 * dirichletForm Ω (w 0 : SobolevEuclidean N 1 2 Ω)
        (w 0 : SobolevEuclidean N 1 2 Ω))) :=
    (hwc 0 self_mem_Ici).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have h2 : (fun t ↦ -(1 / 2) * ⟪deriv u t, u t⟫_ℝ) =ᶠ[𝓝[>] 0]
      fun t ↦ 1 / 2 * dirichletForm Ω (w t : SobolevEuclidean N 1 2 Ω)
        (w t : SobolevEuclidean N 1 2 Ω) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact (h.neg_half_inner_deriv_eq ht).trans (congrArg (1 / 2 * ·)
      (h.inner_apply_self_eq_dirichletForm ht (huw t (le_of_lt ht)).symm))
  rw [hw0] at h1
  exact h1.congr' h2.symm

/-- The identity (11) of Theorem 10.2 (a) of [brezis2011functional]. Let $u$ be a solution with
datum $u_0$, let $u_0$ be the function of $v_0 \in H^1_0(\Omega)$, and let $T > 0$. Then
$t \mapsto \|u'(t)\|^2$ is integrable on $(0, T]$ and
$$\int_0^T \|u'(t)\|^2 \, dt + \frac12 \langle A u(T), u(T) \rangle = \frac12 \int_\Omega
  |\nabla v_0|^2,$$
that is, $\int_0^T \|\partial_t u\|^2 + \frac12 \|\nabla u(T)\|^2 = \frac12 \|\nabla u_0\|^2$.

The function $\varphi(t) = \frac12 \langle Au, u \rangle = -\frac12 \langle u', u \rangle$ has
$\varphi' = -\|u'\|^2$ on $(0, \infty)$ (`Heat.IsSolution.hasDerivAt_neg_half_inner_deriv`), and
$\varphi(\varepsilon) \to \frac12 \int_\Omega |\nabla v_0|^2$ by the continuity into
$H^1_0(\Omega)$ at $0$ (`Heat.IsSolution.tendsto_neg_half_inner_deriv_of_mem`). -/
theorem energy_sobolevZero (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t ↦ ‖deriv u t‖ ^ 2) (Ioc 0 T) ∧
      (∫ t in (0 : ℝ)..T, ‖deriv u t‖ ^ 2)
        + 1 / 2 * ⟪dirichletLaplacian Ω ⟨u T, h.mem_domain hT⟩, u T⟫_ℝ
      = 1 / 2 * dirichletForm Ω (v₀ : SobolevEuclidean N 1 2 Ω)
        (v₀ : SobolevEuclidean N 1 2 Ω) := by
  have hgc : ContinuousOn (fun t ↦ ‖deriv u t‖ ^ 2) (Ioi 0) :=
    (h.contDiffOn.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).norm.pow 2
  have hφ0 : ∀ t, 0 < t → 0 ≤ -(1 / 2) * ⟪deriv u t, u t⟫_ℝ := fun t ht ↦ by
    rw [h.neg_half_inner_deriv_eq ht]
    exact mul_nonneg (by norm_num) (dirichletLaplacian_inner_self_nonneg _)
  obtain ⟨h1, h2⟩ := integrableOn_Ioc_and_integral_eq_of_hasDerivAt_neg hT
    (fun t ht ↦ h.hasDerivAt_neg_half_inner_deriv ht) (fun t _ ↦ by positivity) hgc hφ0
    (h.tendsto_neg_half_inner_deriv_of_mem hv₀)
  refine ⟨h1, ?_⟩
  rw [← h.neg_half_inner_deriv_eq hT]
  beta_reduce at h2
  linarith

/-- The clause $\partial_t u \in L^2(0, \infty; L^2(\Omega))$ of Theorem 10.2 (a) of
[brezis2011functional]. Let $u$ be a solution with datum $u_0$, and let $u_0$ be the function of
$v_0 \in H^1_0(\Omega)$. Then the curve $u'$ lies in $L^2((0, \infty); L^2(\Omega))$ and
$$\int_0^\infty \|u'(t)\|^2 \, dt \le \frac12 \int_\Omega |\nabla v_0|^2.$$
-/
theorem memLp_deriv (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero N 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume v₀
      = u₀) :
    MemLp (deriv u) 2 (volume.restrict (Ioi 0)) ∧
      ∫ t in Ioi 0, ‖deriv u t‖ ^ 2
        ≤ 1 / 2 * dirichletForm Ω (v₀ : SobolevEuclidean N 1 2 Ω)
          (v₀ : SobolevEuclidean N 1 2 Ω) := by
  have key := integrableOn_Ioi_and_integral_le_of_forall_integral_le
    (g := fun t ↦ ‖deriv u t‖ ^ 2)
    (L := 1 / 2 * dirichletForm Ω (v₀ : SobolevEuclidean N 1 2 Ω) (v₀ : SobolevEuclidean N 1 2 Ω))
    (fun t _ ↦ by positivity)
    (fun T hT ↦ (h.energy_sobolevZero hv₀ hT).1) fun T hT ↦ by
      have := (h.energy_sobolevZero hv₀ hT).2
      have h0 : 0 ≤ ⟪dirichletLaplacian Ω ⟨u T, h.mem_domain hT⟩, u T⟫_ℝ :=
        dirichletLaplacian_inner_self_nonneg ⟨u T, h.mem_domain hT⟩
      beta_reduce
      linarith
  refine ⟨?_, key.2⟩
  rw [memLp_two_iff_integrable_sq_norm
    ((h.contDiffOn.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).aestronglyMeasurable
      measurableSet_Ioi)]
  exact key.1

/-! ### Theorem 10.2 (b): $u_0 \in D(A)$ -/

/-- The first clause of Theorem 10.2 (b) of [brezis2011functional], in abstract form. Let $u$ be a
solution with datum $u_0 \in D(A)$. Then $u \in C^1([0, \infty); L^2(\Omega))$, the one-sided
derivative of $u$ at $0$ within $[0, \infty)$ is $-A u_0$, and $u \in C([0, \infty); D(A))$.
This holds on every open set $\Omega$.

This is the Hille–Yosida theorem (Theorem 7.4) for the datum $u_0 \in D(A)$, transported along
$u = S_A(\cdot) u_0$. -/
theorem contDiffOn_Ici_of_mem_domain (h : IsSolution Ω u₀ u)
    (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain) :
    ContDiffOn ℝ 1 u (Ici 0) ∧
      HasDerivWithinAt u (-(dirichletLaplacian Ω ⟨u₀, hu₀⟩)) (Ici 0) 0 ∧
      (dirichletLaplacian Ω).ContDiffOnPowDomain 0 1 u (Ici 0) := by
  have hA := dirichletLaplacian_isMaximalMonotone (Ω := Ω)
  refine ⟨(hA.contDiffOn_semigroup_apply ⟨u₀, hu₀⟩).congr fun t ht ↦ h.apply_eq ht, ?_, ?_⟩
  · have h1 := (hA.isSolutionOn_semigroup ⟨u₀, hu₀⟩).hasDerivWithinAt 0 self_mem_Ici
    have e : (⟨(dirichletLaplacian Ω).semigroup 0
          ((⟨u₀, hu₀⟩ : (dirichletLaplacian Ω).domain) :
            Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))),
          hA.semigroup_apply_mem_domain ⟨u₀, hu₀⟩ le_rfl⟩ : (dirichletLaplacian Ω).domain)
        = ⟨u₀, hu₀⟩ := Subtype.ext (by simp [hA.semigroup_zero])
    exact (h1.congr_deriv (congrArg (fun z ↦ -(dirichletLaplacian Ω z)) e)).congr
      (fun t ht ↦ h.apply_eq ht) (h.apply_eq le_rfl)
  · obtain ⟨x, hx0, -⟩ := exists_powDomain_one (A := dirichletLaplacian Ω) ⟨u₀, hu₀⟩
    have := hA.contDiffOnPowDomain_semigroup x (j := 1) le_rfl
    rw [hx0] at this
    exact this.congr fun t ht ↦ (h.apply_eq ht).symm

/-- Let $u$ be a solution with datum $u_0 \in D(A)$. Then $u'(t) \to -A u_0$ as $t \to 0^+$.

The proof is $u'(t) = -S_A(t) (A u_0)$ and the continuity of the semigroup at $0$. -/
theorem tendsto_deriv_of_mem_domain (h : IsSolution Ω u₀ u)
    (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain) :
    Tendsto (deriv u) (𝓝[>] 0) (𝓝 (-(dirichletLaplacian Ω ⟨u₀, hu₀⟩))) := by
  have hA := dirichletLaplacian_isMaximalMonotone (Ω := Ω)
  have h1 := ((hA.continuousOn_semigroup_apply (dirichletLaplacian Ω ⟨u₀, hu₀⟩) 0
    self_mem_Ici).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)).neg
  rw [hA.semigroup_zero, one_apply_eq_self] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [h.deriv_eq ht, ← hA.semigroup_apply_apply ⟨u₀, hu₀⟩ (le_of_lt ht)]
  congr 2
  exact Subtype.ext (h.apply_eq (le_of_lt ht)).symm

/-- The identity of Theorem 10.2 (b) of [brezis2011functional], stated after (b). Let $u$ be a
solution with datum $u_0 \in D(A)$, let $T > 0$, and let $g(t) = \langle A u'(t), u'(t)
\rangle = \int_\Omega |\nabla \Delta u(t)|^2$ for $t > 0$. Then $g$ is integrable on $(0, T]$
and
$$\frac12 \|u'(T)\|^2 + \int_0^T g(t) \, dt = \frac12 \|A u_0\|^2,$$
that is, $\frac12 \|\Delta u(T)\|^2 + \int_0^T \|\nabla \Delta u\|^2 = \frac12 \|\Delta
u_0\|^2$.

The function $\varphi = \frac12 \|u'\|^2$ has $\varphi' = \langle u', u'' \rangle = -g$, because
$u'' = -Au'$, and $\varphi(\varepsilon) \to \frac12 \|A u_0\|^2$
(`Heat.IsSolution.tendsto_deriv_of_mem_domain`). -/
theorem energy_domain (h : IsSolution Ω u₀ u) (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain)
    {g : ℝ → ℝ}
    (hg : ∀ t (ht : 0 < t),
      g t = ⟪dirichletLaplacian Ω ⟨deriv u t, h.deriv_mem_domain ht⟩, deriv u t⟫_ℝ)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn g (Ioc 0 T) ∧
      1 / 2 * ‖deriv u T‖ ^ 2 + ∫ t in (0 : ℝ)..T, g t
        = 1 / 2 * ‖dirichletLaplacian Ω ⟨u₀, hu₀⟩‖ ^ 2 := by
  have hφ : ∀ t, 0 < t → HasDerivAt (fun t ↦ 1 / 2 * ‖deriv u t‖ ^ 2) (-(g t)) t := by
    intro t ht
    have := (h.hasDerivAt_deriv ht).norm_sq.const_mul (1 / 2)
    convert this using 1
    rw [hg t ht, inner_neg_right, real_inner_comm]
    ring
  have hg0 : ∀ t, 0 < t → 0 ≤ g t := fun t ht ↦ by
    rw [hg t ht]
    exact dirichletLaplacian_inner_self_nonneg _
  have hgc : ContinuousOn g (Ioi 0) := by
    have h1 : ContinuousOn (fun t ↦ ⟪-deriv (deriv u) t, deriv u t⟫_ℝ) (Ioi 0) := by
      have h2 : ContDiffOn ℝ (1 + 1) u (Ioi 0) := h.contDiffOn_top.of_le (by simp)
      have h3 : ContDiffOn ℝ 1 (deriv u) (Ioi 0) :=
        ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).1 h2).2.2
      exact (h3.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).neg.inner
        (h.contDiffOn.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl)
    refine h1.congr fun t ht ↦ ?_
    change g t = ⟪-deriv (deriv u) t, deriv u t⟫_ℝ
    rw [hg t ht, (h.hasDerivAt_deriv ht).deriv, neg_neg]
  have hL : Tendsto (fun t ↦ 1 / 2 * ‖deriv u t‖ ^ 2) (𝓝[>] 0)
      (𝓝 (1 / 2 * ‖dirichletLaplacian Ω ⟨u₀, hu₀⟩‖ ^ 2)) := by
    have := ((h.tendsto_deriv_of_mem_domain hu₀).norm.pow 2).const_mul (1 / 2)
    rwa [norm_neg] at this
  exact integrableOn_Ioc_and_integral_eq_of_hasDerivAt_neg hT hφ hg0 hgc
    (fun t _ ↦ by positivity) hL

/-- Theorem 10.2 (c) of [brezis2011functional], in the form of Chapter 7. Let $u$ be a solution with
datum $u_0 \in D(A^k)$, given as the $0$-th coordinate of some $x \in D(A^k)$. Then
$u \in C^{k-j}([0, \infty); D(A^j))$ for every $j \le k$. This holds on every open set $\Omega$;
it is Theorem 7.5 of [brezis2011functional]. -/
theorem contDiffOnPowDomain_Ici_of_powDomain (h : IsSolution Ω u₀ u) {k : ℕ}
    (x : (dirichletLaplacian Ω).PowDomain k) (hx : applyL (dirichletLaplacian Ω) k 0 x = u₀)
    {j : ℕ} (hj : j ≤ k) :
    (dirichletLaplacian Ω).ContDiffOnPowDomain (k - j : ℕ) j u (Ici 0) := by
  have := dirichletLaplacian_isMaximalMonotone.contDiffOnPowDomain_semigroup x hj
  rw [hx] at this
  exact this.congr fun t ht ↦ (h.apply_eq ht).symm

end IsSolution

end Heat

/-! ### The regular-domain clauses: $H^{2\ell}(\Omega)$ -/

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- A solution lies in $C^\infty((0, \infty); H^{2\ell}(\Omega))$ on a domain $\Omega$ of class
$C^{2\ell}$ with bounded boundary. This is the display after (7) in §10.1 of
[brezis2011functional].

The proof composes the $C^\infty$ lift into $D(A^\ell)$ (`LinearPMap.contDiffOn_semigroupLift`)
with the bounded injection $D(A^\ell) \to H^{2\ell}(\Omega)$ of Theorem 9.25
(`dirichletLaplacian.powDomainToSobolevL`). Every finite order follows by
`Bochner.ContDiffOnThrough.of_le`. Here $\Omega \subseteq \mathbb{R}^N$ with $N = d + 1$. -/
theorem contDiffOnThrough_sobolev (h : IsSolution Ω u₀ u) {ℓ : ℕ}
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω
      volume) ∞ u (Ioi 0) :=
  ⟨fun t ↦ dirichletLaplacian.powDomainToSobolevL hΩ hΓ
      (semigroupLift (dirichletLaplacian Ω) u₀ ℓ t),
    (dirichletLaplacian.powDomainToSobolevL hΩ hΓ).contDiff.comp_contDiffOn
      (contDiffOn_semigroupLift dirichletLaplacian_isMaximalMonotone
        dirichletLaplacian_isFormalAdjoint u₀ ℓ),
    fun t ht ↦ by
      rw [fnL_powDomainToSobolevL, applyL_zero_semigroupLift dirichletLaplacian_isMaximalMonotone
        dirichletLaplacian_isFormalAdjoint ht, h.apply_eq ht.le]⟩

/-- The clause $u \in C((0, \infty); H^2(\Omega) \cap H^1_0(\Omega))$ of (4) in Theorem 10.1 of
[brezis2011functional]. Let $\Omega$ be a domain of class $C^2$ with bounded boundary, and let
$u$ be a solution. Then on $(0, \infty)$ the curve $u$ is the function of a continuous curve in
$H^2(\Omega)$, and $u(t)$ is the function of an element of $H^1_0(\Omega)$ for every $t > 0$. -/
theorem contDiffOnThrough_two (h : IsSolution Ω u₀ u)
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω
      volume) 0 u (Ioi 0) ∧
    ∀ t, 0 < t → u t ∈ Set.range (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume) := by
  have hΩ' : IsContDiffChartDomain (2 * 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    hΩ.of_le (by norm_num)
  exact ⟨(h.contDiffOnThrough_sobolev hΩ' hΓ).of_le bot_le, fun t ht ↦
    dirichletLaplacian_exists_sobolevZero_lift ⟨u t, h.mem_domain ht⟩⟩

/-- Theorem 10.2 (c) of [brezis2011functional], in the form with $H^{2\ell}(\Omega)$. Let $u$ be a
solution with datum $u_0 \in D(A^k)$, given as the $0$-th coordinate of some $x \in D(A^k)$, let
$\ell \le k$, and let $\Omega$ be a domain of class $C^{2\ell}$ with bounded boundary. Then $u
\in C^{k-\ell}([0, \infty); H^{2\ell}(\Omega))$. -/
theorem contDiffOnThrough_sobolev_Ici_of_powDomain (h : IsSolution Ω u₀ u) {k : ℕ}
    (x : (dirichletLaplacian Ω).PowDomain k) (hx : applyL (dirichletLaplacian Ω) k 0 x = u₀)
    {ℓ : ℕ} (hℓ : ℓ ≤ k)
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω
      volume) (k - ℓ : ℕ) u (Ici 0) :=
  Bochner.ContDiffOnThrough.of_contDiffOnPowDomain (h.contDiffOnPowDomain_Ici_of_powDomain x hx hℓ)
    (dirichletLaplacian.powDomainToSobolevL hΩ hΓ) _ (fnL_powDomainToSobolevL hΩ hΓ)

/-- The clause $u \in C([0, \infty); H^2(\Omega))$ of Theorem 10.2 (b) of [brezis2011functional]: a
solution with datum $u_0 \in D(A)$ on a domain of class $C^2$ with bounded boundary lies in
$C([0, \infty); H^2(\Omega))$. -/
theorem contDiffOnThrough_two_Ici_of_mem_domain (h : IsSolution Ω u₀ u)
    (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain)
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω
      volume) 0 u (Ici 0) := by
  have hΩ' : IsContDiffChartDomain (2 * 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    hΩ.of_le (by norm_num)
  obtain ⟨x, hx0, -⟩ := exists_powDomain_one (A := dirichletLaplacian Ω) ⟨u₀, hu₀⟩
  exact h.contDiffOnThrough_sobolev_Ici_of_powDomain x hx0 le_rfl hΩ' hΓ

end IsSolution

end Heat

/-!
### Square integrability in time on bounded domains

On a bounded domain, $u \in L^2(0, \infty; H^1_0(\Omega))$. On a bounded domain of class $C^2$ with
bounded boundary, $u \in L^2(0, \infty; H^2(\Omega))$ for $u_0 \in H^1_0(\Omega)$.
-/

/-- **Poincaré's inequality on $H^1_0(\Omega)$, squared.** Let $\Omega \subseteq \mathbb{R}^N$,
$N = d + 1$, be bounded. Then there is $C \ge 0$ with
$$\|v\|_{H^1}^2 \le C \int_\Omega |\nabla v|^2 \qquad \text{for every } v \in H^1_0(\Omega).$$

This is Corollary 9.19 of [brezis2011functional]. The proof uses
`Elliptic.dirichletForm_restrict_isCoercive`. -/
theorem SobolevEuclideanZero.exists_norm_sq_le_dirichletForm {d : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      ‖v‖ ^ 2 ≤ C * Elliptic.dirichletForm Ω (v : SobolevEuclidean (d + 1) 1 2 Ω)
        (v : SobolevEuclidean (d + 1) 1 2 Ω) := by
  obtain ⟨c, hc, hcoer⟩ := Elliptic.dirichletForm_restrict_isCoercive Ω hΩ
  refine ⟨c⁻¹, by positivity, fun v ↦ ?_⟩
  have := hcoer v
  rw [RCLike.re_to_real, SesqForm.restrict_apply] at this
  rw [← div_eq_inv_mul, le_div_iff₀' hc]
  exact this

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

end IsSolution

variable (Ω) in
/-- The **$H^1_0$-lift of the solution curve**: the curve $t \mapsto v(t) \in H^1_0(\Omega)$
obtained by applying the bounded lift $D(A) \to H^1_0(\Omega)$
(`dirichletLaplacian.sobolevZeroLiftL`) to the lift of $S_A(t) u_0$ into $D(A)$
(`LinearPMap.semigroupLift`).

For a solution $u$ with datum $u_0$ and $t > 0$, the function of $v(t)$ is $u(t)$
(`Heat.IsSolution.fnL_sobolevZeroLift`). The curve is $C^\infty$ on $(0, \infty)$. -/
def sobolevZeroLift (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (t : ℝ) : SobolevEuclideanZero (d + 1) 1 2 Ω :=
  dirichletLaplacian.sobolevZeroLiftL Ω (semigroupLift (dirichletLaplacian Ω) u₀ 1 t)

/-- The $H^1_0$-lift of the solution curve is of class $C^\infty$ on $(0, \infty)$. -/
theorem contDiffOn_sobolevZeroLift
    (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ContDiffOn ℝ ∞ (sobolevZeroLift Ω u₀) (Ioi 0) :=
  (dirichletLaplacian.sobolevZeroLiftL Ω).contDiff.comp_contDiffOn
    (contDiffOn_semigroupLift dirichletLaplacian_isMaximalMonotone
      dirichletLaplacian_isFormalAdjoint u₀ 1)

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- For a solution $u$ with datum $u_0$ and $t > 0$, the function of the $H^1_0$-lift $v(t)$ is
$u(t)$. -/
theorem fnL_sobolevZeroLift (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      (sobolevZeroLift Ω u₀ t) = u t :=
  (fnL_sobolevZeroLiftL _).trans ((applyL_zero_semigroupLift dirichletLaplacian_isMaximalMonotone
    dirichletLaplacian_isFormalAdjoint ht).trans (h.apply_eq ht.le).symm)

/-- Let $C$ satisfy $\|w\|_{H^1}^2 \le C \int_\Omega |\nabla w|^2$ for every $w \in H^1_0(\Omega)$.
Then for a solution $u$ and $t > 0$, the $H^1_0$-lift $v$ satisfies
$$\|v(t)\|_{H^1}^2 \le C \langle A u(t), u(t) \rangle.$$

Such a constant $C$ exists on a bounded $\Omega$
(`SobolevEuclideanZero.exists_norm_sq_le_dirichletForm`). -/
theorem norm_sq_sobolevZeroLift_le (h : IsSolution Ω u₀ u) {C : ℝ}
    (hC : ∀ v : SobolevEuclideanZero (d + 1) 1 2 Ω,
      ‖v‖ ^ 2 ≤ C * dirichletForm Ω (v : SobolevEuclidean (d + 1) 1 2 Ω)
        (v : SobolevEuclidean (d + 1) 1 2 Ω))
    {t : ℝ} (ht : 0 < t) :
    ‖sobolevZeroLift Ω u₀ t‖ ^ 2
      ≤ C * ⟪dirichletLaplacian Ω ⟨u t, h.mem_domain ht⟩, u t⟫_ℝ :=
  (hC _).trans_eq (congrArg (C * ·)
    (h.inner_apply_self_eq_dirichletForm ht (h.fnL_sobolevZeroLift ht)).symm)

/-- Let $\Omega$ be bounded and let $u$ be a solution. Then $t \mapsto \|v(t)\|_{H^1}^2$ is
integrable on $(0, \infty)$, where $v$ is the $H^1_0$-lift of $u$.

The proof is Poincaré's inequality and the energy identity
(`Heat.IsSolution.integral_inner_apply_le`). -/
theorem integrableOn_norm_sq_sobolevZeroLift
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (h : IsSolution Ω u₀ u) :
    IntegrableOn (fun t ↦ ‖sobolevZeroLift Ω u₀ t‖ ^ 2) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := SobolevEuclideanZero.exists_norm_sq_le_dirichletForm hΩ
  obtain ⟨hgi, -⟩ := h.integral_inner_apply_le (g := fun t ↦ dirichletForm Ω
    (sobolevZeroLift Ω u₀ t : SobolevEuclidean (d + 1) 1 2 Ω)
    (sobolevZeroLift Ω u₀ t : SobolevEuclidean (d + 1) 1 2 Ω))
    fun t ht ↦ (h.inner_apply_self_eq_dirichletForm ht (h.fnL_sobolevZeroLift ht)).symm
  refine (hgi.const_mul C).mono' (((contDiffOn_sobolevZeroLift u₀).continuousOn.norm.pow 2
    |>.aestronglyMeasurable measurableSet_Ioi)) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t _ ↦ ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact hC _

/-- The clause $u \in L^2(0, \infty; H^1_0(\Omega))$ of Theorem 10.1 of [brezis2011functional], for
a bounded $\Omega$. Let $\Omega$ be bounded and let $u$ be a solution. Then on $(0, \infty)$ the
curve $u$ is the function of a curve in $L^2((0, \infty); H^1_0(\Omega))$, namely the
$H^1_0$-lift.

On an unbounded domain only the gradient form of this clause holds
(`Heat.IsSolution.integral_inner_apply_le`). -/
theorem memLpThrough_sobolevZero_of_isBounded
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (h : IsSolution Ω u₀ u) :
    Bochner.MemLpThrough (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume) 2 u (Ioi 0) := by
  have hint := h.integrableOn_norm_sq_sobolevZeroLift hΩ
  have hint2 : IntegrableOn (fun t ↦ ‖sobolevZeroLift Ω u₀ t‖ ^ (2 : ℝ≥0∞).toReal) (Ioi 0) := by
    refine hint.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
  exact Bochner.MemLpThrough.of_contDiffOnThrough_of_integrable
    (contDiffOn_sobolevZeroLift u₀).continuousOn (fun t ht ↦ (h.fnL_sobolevZeroLift ht).symm)
    measurableSet_Ioi two_ne_zero ENNReal.ofNat_ne_top hint2

/-- Let $\Omega$ be bounded and let $u$ be a solution. Then $t \mapsto \|u(t)\|^2$ is integrable on
$(0, \infty)$.

The proof is $\|u(t)\| \le \|v(t)\|_{H^1}$ for the $H^1_0$-lift $v$. -/
theorem integrableOn_norm_sq_of_isBounded
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (h : IsSolution Ω u₀ u) :
    IntegrableOn (fun t ↦ ‖u t‖ ^ 2) (Ioi 0) := by
  refine (h.integrableOn_norm_sq_sobolevZeroLift hΩ).mono'
    ((h.contDiffOn.continuousOn.norm.pow 2).aestronglyMeasurable measurableSet_Ioi) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
  rw [Real.norm_of_nonneg (by positivity), ← h.fnL_sobolevZeroLift ht]
  exact pow_le_pow_left₀ (norm_nonneg _) (SobolevMultiIndexZero.norm_fnL_apply_le _) 2

/-- Let $u$ be a solution with datum $u_0$, and let $u_0$ be the function of
$v_0 \in H^1_0(\Omega)$. Then $t \mapsto \|u'(t)\|^2$ is integrable on $(0, \infty)$.

This is the form of (11) that the $L^2$ memberships use. -/
theorem integrableOn_norm_sq_deriv (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) :
    IntegrableOn (fun t ↦ ‖deriv u t‖ ^ 2) (Ioi 0) :=
  (memLp_two_iff_integrable_sq_norm ((h.contDiffOn.continuousOn_deriv_of_isOpen isOpen_Ioi
    le_rfl).aestronglyMeasurable measurableSet_Ioi)).1 (h.memLp_deriv hv₀).1

/-- For a solution $u$ and $t > 0$, $u'(t) = -A u(t)$, where $A u(t)$ is the first coordinate of the
lift $x_t$ of $u(t)$ into $D(A)$. -/
theorem deriv_eq_neg_applyL_semigroupLift_one (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    deriv u t = -applyL (dirichletLaplacian Ω) 1 1
      (semigroupLift (dirichletLaplacian Ω) u₀ 1 t) := by
  have := h.iteratedDeriv_eq_applyL_semigroupLift 1 1 le_rfl t ht
  rwa [iteratedDeriv_one, pow_one, neg_one_smul] at this

/-- For a solution $u$ and $t > 0$, the lift $x_t$ of $u(t)$ into $D(A)$ has the graph norm
$$\|x_t\|_{D(A)}^2 = \|u(t)\|^2 + \|u'(t)\|^2.$$
-/
theorem norm_sq_semigroupLift_one (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    ‖semigroupLift (dirichletLaplacian Ω) u₀ 1 t‖ ^ 2 = ‖u t‖ ^ 2 + ‖deriv u t‖ ^ 2 := by
  have h1 : applyL (dirichletLaplacian Ω) 1 0 (semigroupLift (dirichletLaplacian Ω) u₀ 1 t) = u t :=
    (applyL_zero_semigroupLift dirichletLaplacian_isMaximalMonotone
      dirichletLaplacian_isFormalAdjoint ht).trans (h.apply_eq ht.le).symm
  have h2 : applyL (dirichletLaplacian Ω) 1 1 (semigroupLift (dirichletLaplacian Ω) u₀ 1 t)
      = -deriv u t := neg_eq_iff_eq_neg.1 (h.deriv_eq_neg_applyL_semigroupLift_one ht).symm
  rw [PowDomain.norm_sq_eq, Fin.sum_univ_two, h1, h2, norm_neg]

end IsSolution

variable (Ω) in
/-- The **$H^2$-lift of the solution curve** on a domain $\Omega$ of class $C^2$ with bounded
boundary: the curve $t \mapsto w(t) \in H^2(\Omega)$ obtained by applying the bounded injection
$D(A) \to H^2(\Omega)$ (`dirichletLaplacian.powDomainToSobolevL`) to the lift of $S_A(t) u_0$
into $D(A)$.

For a solution $u$ with datum $u_0$ and $t > 0$, the function of $w(t)$ is $u(t)$
(`Heat.IsSolution.fnL_sobolevTwoLift`). -/
def sobolevTwoLift
    (hΩ : IsContDiffChartDomain (2 * 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) (t : ℝ) :
    SobolevEuclidean (d + 1) (2 * 1) 2 Ω :=
  dirichletLaplacian.powDomainToSobolevL hΩ hΓ (semigroupLift (dirichletLaplacian Ω) u₀ 1 t)

/-- The $H^2$-lift of the solution curve is of class $C^\infty$ on $(0, \infty)$. -/
theorem contDiffOn_sobolevTwoLift
    (hΩ : IsContDiffChartDomain (2 * 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ContDiffOn ℝ ∞ (sobolevTwoLift Ω hΩ hΓ u₀) (Ioi 0) :=
  (dirichletLaplacian.powDomainToSobolevL hΩ hΓ).contDiff.comp_contDiffOn
    (contDiffOn_semigroupLift dirichletLaplacian_isMaximalMonotone
      dirichletLaplacian_isFormalAdjoint u₀ 1)

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- For a solution $u$ with datum $u_0$ and $t > 0$, the function of the $H^2$-lift $w(t)$ is
$u(t)$. -/
theorem fnL_sobolevTwoLift
    (hΩ : IsContDiffChartDomain (2 * 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * 1) 2 Ω volume
      (sobolevTwoLift Ω hΩ hΓ u₀ t) = u t :=
  (fnL_powDomainToSobolevL hΩ hΓ _).trans
    ((applyL_zero_semigroupLift dirichletLaplacian_isMaximalMonotone
      dirichletLaplacian_isFormalAdjoint ht).trans (h.apply_eq ht.le).symm)

/-- For a solution $u$ and $t > 0$, the $H^2$-lift $w$ satisfies
$$\|w(t)\|_{H^2}^2 \le C \left( \|u(t)\|^2 + \|u'(t)\|^2 \right),$$
where $C$ is the square of the norm of the injection `dirichletLaplacian.powDomainToSobolevL`. -/
theorem norm_sq_sobolevTwoLift_le
    (hΩ : IsContDiffChartDomain (2 * 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 < t) :
    ‖sobolevTwoLift Ω hΩ hΓ u₀ t‖ ^ 2
      ≤ ‖dirichletLaplacian.powDomainToSobolevL hΩ hΓ‖ ^ 2 * (‖u t‖ ^ 2 + ‖deriv u t‖ ^ 2) := by
  have h1 := (dirichletLaplacian.powDomainToSobolevL hΩ hΓ).le_opNorm
    (semigroupLift (dirichletLaplacian Ω) u₀ 1 t)
  calc ‖sobolevTwoLift Ω hΩ hΓ u₀ t‖ ^ 2
      ≤ (‖dirichletLaplacian.powDomainToSobolevL hΩ hΓ‖
        * ‖semigroupLift (dirichletLaplacian Ω) u₀ 1 t‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ‖dirichletLaplacian.powDomainToSobolevL hΩ hΓ‖ ^ 2 * (‖u t‖ ^ 2 + ‖deriv u t‖ ^ 2) := by
        rw [mul_pow, h.norm_sq_semigroupLift_one ht]

/-- The clause $u \in L^2(0, \infty; H^2(\Omega))$ of Theorem 10.2 (a) of [brezis2011functional],
for a bounded domain. Let $\Omega$ be bounded and of class $C^2$ with bounded boundary, let $u$
be a solution with datum $u_0$, and let $u_0$ be the function of some $v_0 \in H^1_0(\Omega)$.
Then on $(0, \infty)$ the curve $u$ is the function of a curve in
$L^2((0, \infty); H^2(\Omega))$.

The $H^2$-lift $w$ satisfies $\|w(t)\|_{H^2}^2 \le C (\|u(t)\|^2 + \|u'(t)\|^2)$, and both terms
are integrable on $(0, \infty)$, by Poincaré's inequality and by (11). On an unbounded domain
only $\int_0^\infty \|\Delta u(t)\|^2 \, dt < \infty$ holds. -/
theorem memLpThrough_two_of_isBounded
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) :
    Bochner.MemLpThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 2 Ω volume) 2
      u (Ioi 0) := by
  have hΩ2 : IsContDiffChartDomain (2 * 1) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    hΩ.of_le (by norm_num)
  have hint : IntegrableOn (fun t ↦ ‖sobolevTwoLift Ω hΩ2 hΓ u₀ t‖ ^ 2) (Ioi 0) := by
    refine (((h.integrableOn_norm_sq_of_isBounded hΩb).add (h.integrableOn_norm_sq_deriv hv₀))
      |>.const_mul (‖dirichletLaplacian.powDomainToSobolevL hΩ2 hΓ‖ ^ 2)).mono'
      (((contDiffOn_sobolevTwoLift hΩ2 hΓ u₀).continuousOn.norm.pow 2).aestronglyMeasurable
        measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact h.norm_sq_sobolevTwoLift_le hΩ2 hΓ ht
  have hint2 : IntegrableOn (fun t ↦ ‖sobolevTwoLift Ω hΩ2 hΓ u₀ t‖ ^ (2 : ℝ≥0∞).toReal)
      (Ioi 0) := by
    refine hint.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
  exact Bochner.MemLpThrough.of_contDiffOnThrough_of_integrable
    (contDiffOn_sobolevTwoLift hΩ2 hΓ u₀).continuousOn
    (fun t ht ↦ (h.fnL_sobolevTwoLift hΩ2 hΓ ht).symm) measurableSet_Ioi two_ne_zero
    ENNReal.ofNat_ne_top hint2

end IsSolution

end Heat

/-! ### Remark 1: the well-posed backward problem -/

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

variable (Ω) in
/-- A **solution of the backward problem** (9'), (10), (11) of Remark 1 in Chapter 10 of
[brezis2011functional]: $-\partial_t u - \Delta u = 0$ on $\Omega \times (-\infty, T)$, $u = 0$
on $\Gamma \times (-\infty, T)$, and $u(T) = u_T$. It is a curve
$u : \mathbb{R} \to L^2(\Omega)$ such that $u(T) = u_T$, $u(t) \in D(A)$ and $u'(t) = A u(t)$
for every $t < T$, $u$ is continuous on $(-\infty, T]$, and $u$ is of class $C^1$ on
$(-\infty, T)$.

The equation reads $u' = Au$ because $A = -\Delta$. -/
structure IsBackwardSolution (T : ℝ)
    (uT : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) : Prop where
  /-- The final condition $u(T) = u_T$. -/
  apply_eq : u T = uT
  /-- The curve takes values in $D(A)$: $u(t) \in D(A)$ for every $t < T$. -/
  mem_domain : ∀ t, t < T → u t ∈ (dirichletLaplacian Ω).domain
  /-- The equation $u'(t) = A u(t) = -\Delta u(t)$ for every $t < T$. -/
  hasDerivAt : ∀ t (ht : t < T), HasDerivAt u (dirichletLaplacian Ω ⟨u t, mem_domain t ht⟩) t
  /-- The curve is continuous on $(-\infty, T]$: $u \in C((-\infty, T]; L^2(\Omega))$. -/
  continuousOn : ContinuousOn u (Iic T)
  /-- The curve is of class $C^1$ on $(-\infty, T)$: $u \in C^1((-\infty, T); L^2(\Omega))$. -/
  contDiffOn : ContDiffOn ℝ 1 u (Iio T)

variable {T : ℝ} {uT : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}

/-- **The change of variables $t \mapsto T - t$**: $u$ solves the backward problem with final datum
$u_T$ at time $T$ if and only if $s \mapsto u(T - s)$ solves the heat equation with initial
datum $u_T$. -/
theorem isBackwardSolution_iff :
    IsBackwardSolution Ω T uT u ↔ IsSolution Ω uT fun s ↦ u (T - s) := by
  constructor
  · intro h
    refine ⟨⟨by simpa using h.apply_eq, fun s hs ↦ h.mem_domain _ (sub_lt_self T hs),
      fun s hs ↦ ?_⟩, ?_, ?_⟩
    · exact ((h.hasDerivAt (T - s) (sub_lt_self T hs)).comp_const_sub T s).hasDerivWithinAt
    · exact h.continuousOn.comp (continuousOn_const.sub continuousOn_id)
        fun s (hs : 0 ≤ s) ↦ show T - s ∈ Iic T from sub_le_self T hs
    · exact h.contDiffOn.comp (contDiffOn_const.sub contDiffOn_id)
        fun s (hs : 0 < s) ↦ show T - s ∈ Iio T from sub_lt_self T hs
  · intro h
    have hmem : ∀ t, t < T → u t ∈ (dirichletLaplacian Ω).domain := fun t ht ↦ by
      have := h.mem_domain (sub_pos.2 ht)
      rwa [sub_sub_cancel] at this
    refine ⟨by simpa using h.apply_zero, hmem, fun t ht ↦ ?_, ?_, ?_⟩
    · have h1 := (h.hasDerivAt (sub_pos.2 ht)).comp_const_sub T t
      have e2 : (⟨(fun s ↦ u (T - s)) (T - t), h.mem_domain (sub_pos.2 ht)⟩ :
          (dirichletLaplacian Ω).domain) = ⟨u t, hmem t ht⟩ :=
        Subtype.ext (by simp only [sub_sub_cancel])
      refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun x ↦ ?_)).congr_deriv ?_
      · change u x = u (T - (T - x))
        rw [sub_sub_cancel]
      · rw [neg_neg]
        exact congrArg (fun z ↦ dirichletLaplacian Ω z) e2
    · have := h.continuousOn.comp (continuousOn_const.sub continuousOn_id)
        (fun t (ht : t ∈ Iic T) ↦ show T - t ∈ Ici (0 : ℝ) from mem_Ici.2 (sub_nonneg.2 ht))
      refine this.congr fun t _ ↦ ?_
      change u t = u (T - (T - t))
      rw [sub_sub_cancel]
    · have := h.contDiffOn.comp (contDiffOn_const.sub contDiffOn_id)
        (fun t (ht : t ∈ Iio T) ↦ show T - t ∈ Ioi (0 : ℝ) from mem_Ioi.2 (sub_pos.2 ht))
      refine this.congr fun t _ ↦ ?_
      change u t = u (T - (T - t))
      rw [sub_sub_cancel]

/-- The well-posed half of Remark 1 in Chapter 10 of [brezis2011functional]. For every
$T \in \mathbb{R}$ and every $u_T \in L^2(\Omega)$, the backward problem
$-\partial_t u - \Delta u = 0$ on $\Omega \times (-\infty, T)$, $u = 0$ on
$\Gamma \times (-\infty, T)$, $u(T) = u_T$ has a solution $u$, and every solution agrees with
$u$ on $(-\infty, T]$. The solution is $t \mapsto S_A(T - t) u_T$.

The book says: "change $t$ into $T - t$ and apply Theorem 10.1". The ill-posed problem (9),
(10), (11) is not a theorem of the book. Its necessary condition (12) is
`Heat.IsSolution.exists_powDomain`. -/
theorem existsUnique_isSolution_backward (T : ℝ)
    (uT : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ∃ u, IsBackwardSolution Ω T uT u ∧ ∀ v, IsBackwardSolution Ω T uT v → EqOn v u (Iic T) := by
  refine ⟨fun t ↦ solution Ω uT (T - t), isBackwardSolution_iff.2 ?_, fun v hv t ht ↦ ?_⟩
  · have e : (fun s ↦ solution Ω uT (T - (T - s))) = solution Ω uT :=
      funext fun s ↦ by rw [sub_sub_cancel]
    rw [e]
    exact isSolution_solution uT
  · have := (isBackwardSolution_iff.1 hv).eqOn_solution
      (show T - t ∈ Ici (0 : ℝ) from mem_Ici.2 (sub_nonneg.2 (mem_Iic.1 ht)))
    simpa only [sub_sub_cancel] using this

end Heat

/-! ### Remark 3: the eigenfunction expansion -/

section Eigen

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)

/-- Let $\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be a bounded nonempty open set. Then every
Dirichlet eigenfunction $e_n$ lies in $D(A)$, and $A e_n = \lambda_n e_n$.

The weak eigenvalue equation (83) of Theorem 9.31 is the defining identity of the weak domain
(`dirichletLaplacianDomain`) with the datum $\lambda_n e_n$. -/
theorem dirichletLaplacian_apply_dirichletEigenbasis (n : ℕ) :
    ∃ h : dirichletEigenbasis Ω hΩ hne n ∈ (dirichletLaplacian Ω).domain,
      dirichletLaplacian Ω ⟨dirichletEigenbasis Ω hΩ hne n, h⟩
        = dirichletEigenvalue Ω hΩ n • dirichletEigenbasis Ω hΩ hne n := by
  have hv : (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω)
      ∈ SobolevEuclideanZero (d + 1) 1 2 Ω := (dirichletEigenfunction Ω hΩ hne n).2
  have hvf : fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω)
      = dirichletEigenbasis Ω hΩ hne n := fnL_dirichletEigenfunction Ω hΩ hne n
  have hg : ∀ φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
      dirichletForm Ω (dirichletEigenfunction Ω hΩ hne n : SobolevEuclidean (d + 1) 1 2 Ω) φ
        = load Ω (dirichletEigenvalue Ω hΩ n • dirichletEigenbasis Ω hΩ hne n) φ := fun φ hφ ↦ by
    have h1 := dirichletForm_dirichletEigenfunction Ω hΩ hne n ⟨φ, hφ⟩
    have h2 : load Ω (dirichletEigenvalue Ω hΩ n • dirichletEigenbasis Ω hΩ hne n) φ
        = dirichletEigenvalue Ω hΩ n * ⟪dirichletEigenbasis Ω hΩ hne n,
          fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume φ⟫_ℝ := by
      rw [load_apply_inner, real_inner_smul_left]
      rfl
    exact h1.trans h2.symm
  exact ⟨⟨_, hv, hvf, _, hg⟩, dirichletLaplacian_apply_unique _ hv hvf hg⟩

namespace Heat.IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- Let $\Omega$ be bounded and nonempty, let $u$ be a solution, and let
$a_n(t) = \langle u(t), e_n \rangle$ be its coefficient in the Dirichlet eigenbasis. Then for
every $t > 0$, $a_n$ is differentiable at $t$ with $a_n'(t) = -\lambda_n a_n(t)$.

The proof is $\langle u', e_n \rangle = -\langle Au, e_n \rangle = -\langle u, A e_n \rangle =
-\lambda_n \langle u, e_n \rangle$. -/
theorem hasDerivAt_inner_eigenfunction (h : IsSolution Ω u₀ u) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t ↦ ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ)
      (-dirichletEigenvalue Ω hΩ n * ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ) t := by
  obtain ⟨hmem, hAe⟩ := dirichletLaplacian_apply_dirichletEigenbasis hΩ hne n
  have h1 := (h.hasDerivAt ht).inner ℝ (hasDerivAt_const t (dirichletEigenbasis Ω hΩ hne n))
  refine h1.congr_deriv ?_
  rw [inner_zero_right, zero_add, inner_neg_left,
    dirichletLaplacian_isFormalAdjoint ⟨u t, h.mem_domain ht⟩ ⟨_, hmem⟩, hAe,
    inner_smul_right, neg_mul]

/-- The coefficients (13) of Remark 3 in Chapter 10 of [brezis2011functional]. Let
$\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be a bounded nonempty open set, and let $u$ be a
solution with datum $u_0$. Then for every $t \ge 0$ and every $n$,
$$\langle u(t), e_n \rangle = e^{-\lambda_n t} \langle u_0, e_n \rangle,$$
where $(e_n)$ is the Dirichlet eigenbasis and $\lambda_n$ are the Dirichlet eigenvalues.

The function $e^{\lambda_n t} \langle u(t), e_n \rangle$ has derivative zero on $(0, \infty)$
and is continuous on $[0, \infty)$. -/
theorem inner_eigenfunction (h : IsSolution Ω u₀ u) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ
      = Real.exp (-dirichletEigenvalue Ω hΩ n * t) * ⟪u₀, dirichletEigenbasis Ω hΩ hne n⟫_ℝ := by
  set lam := dirichletEigenvalue Ω hΩ n with hlam
  set F : ℝ → ℝ := fun t ↦ Real.exp (lam * t) * ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ with hF
  have hFd : ∀ t, 0 < t → HasDerivAt F 0 t := fun t ht ↦ by
    have h1 : HasDerivAt (fun t ↦ Real.exp (lam * t)) (Real.exp (lam * t) * lam) t := by
      simpa using ((hasDerivAt_id t).const_mul lam).exp
    have := h1.mul (h.hasDerivAt_inner_eigenfunction hΩ hne n ht)
    convert this using 1
    ring
  have hFc : ContinuousOn F (Ici 0) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (h.continuousOn.inner continuousOn_const)
  have hFdiff : DifferentiableOn ℝ F (interior (Ici 0)) := by
    rw [interior_Ici]
    exact fun t ht ↦ (hFd t ht).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn F (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) hFc hFdiff fun t ht ↦ by
      rw [interior_Ici] at ht
      rw [(hFd t ht).deriv]
  have hanti : AntitoneOn F (Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hFc hFdiff fun t ht ↦ by
      rw [interior_Ici] at ht
      rw [(hFd t ht).deriv]
  have hconst : F t = F 0 := le_antisymm (hanti self_mem_Ici ht ht) (hmono self_mem_Ici ht ht)
  have hF0 : F 0 = ⟪u₀, dirichletEigenbasis Ω hΩ hne n⟫_ℝ := by
    simp [hF, h.apply_zero]
  have hFt : F t = Real.exp (lam * t) * ⟪u t, dirichletEigenbasis Ω hΩ hne n⟫_ℝ := rfl
  rw [hF0] at hconst
  rw [← hconst, hFt, neg_mul, Real.exp_neg, ← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne',
    one_mul]

/-- The series (14) of Remark 3 in Chapter 10 of [brezis2011functional]. Let
$\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be a bounded nonempty open set, and let $u$ be a
solution with datum $u_0$. Then for every $t \ge 0$,
$$u(t) = \sum_{n} e^{-\lambda_n t} \langle u_0, e_n \rangle e_n \qquad \text{in } L^2(\Omega).$$

This is the expansion of $u(t)$ in the Hilbert basis $(e_n)$, with the coefficients of
`Heat.IsSolution.inner_eigenfunction`. -/
theorem hasSum_eigenfunction (h : IsSolution Ω u₀ u) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun n ↦ (Real.exp (-dirichletEigenvalue Ω hΩ n * t)
      * ⟪u₀, dirichletEigenbasis Ω hΩ hne n⟫_ℝ) • dirichletEigenbasis Ω hΩ hne n) (u t) := by
  have := (dirichletEigenbasis Ω hΩ hne).hasSum_repr (u t)
  refine this.congr_fun fun n ↦ ?_
  rw [HilbertBasis.repr_apply_apply, real_inner_comm (u t) (dirichletEigenbasis Ω hΩ hne n),
    h.inner_eigenfunction hΩ hne n ht]

end Heat.IsSolution

end Eigen

/-!
### Theorem 10.2 (b): $H^3$ in space, and $\partial_t u$ in $H^1_0$

For $u_0 \in D(A)$: on a bounded domain, $\partial_t u \in L^2(0, \infty; H^1_0(\Omega))$, and on a
bounded domain of class $C^3$ with bounded boundary, $u \in L^2(0, \infty; H^3(\Omega))$.
-/

section SobolevThree

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

namespace Heat

variable (Ω) in
/-- The **$H^1_0$-lift of $u'$**: for $v_0 \in H^1_0(\Omega)$, the curve
$t \mapsto z(t) = -A_1 x_t \in H^1_0(\Omega)$, where $x_t$ is the lift of $S_{A_1}(t) v_0$ into
$D(A_1)$ and $A_1 x_t$ is its first coordinate.

For a solution $u$ whose datum is the function of $v_0$, the function of $z(t)$ is $u'(t)$ for
every $t > 0$ (`Heat.IsSolution.fnL_sobolevZeroLiftDeriv`). -/
def sobolevZeroLiftDeriv (v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω) (t : ℝ) :
    SobolevEuclideanZero (d + 1) 1 2 Ω :=
  -applyL (dirichletLaplacianH10 Ω) 1 1 (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t)

/-- The $H^1_0$-lift of $u'$ is of class $C^\infty$ on $(0, \infty)$. -/
theorem contDiffOn_sobolevZeroLiftDeriv (v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    ContDiffOn ℝ ∞ (sobolevZeroLiftDeriv Ω v₀) (Ioi 0) :=
  ((applyL (dirichletLaplacianH10 Ω) 1 1).contDiff.comp_contDiffOn
    (contDiffOn_semigroupLift dirichletLaplacianH10_isMaximalMonotone
      dirichletLaplacianH10_isFormalAdjoint v₀ 1)).neg

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- Let $u$ be a solution with datum $u_0$, and let $u_0$ be the function of
$v_0 \in H^1_0(\Omega)$. Then for every $t > 0$, the function of the $H^1_0$-lift $z(t)$ of $u'$
is $u'(t)$. -/
theorem fnL_sobolevZeroLiftDeriv (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) {t : ℝ} (ht : 0 < t) :
    SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume
      (sobolevZeroLiftDeriv Ω v₀ t) = deriv u t :=
  (_root_.map_neg _ _).trans ((congrArg Neg.neg (h.fnL_applyL_one_semigroupLift_H10 hv₀ ht)).trans
    (neg_neg _))

/-- Let $u$ be a solution with datum $u_0$, let $u_0$ be the function of $v_0 \in H^1_0(\Omega)$,
and let $t > 0$. Then the $H^1_0$-lift $z$ of $u'$ satisfies
$$\int_\Omega |\nabla z(t)|^2 = \langle A u'(t), u'(t) \rangle.$$
-/
theorem dirichletForm_sobolevZeroLiftDeriv (h : IsSolution Ω u₀ u)
    {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) {t : ℝ} (ht : 0 < t) :
    dirichletForm Ω (sobolevZeroLiftDeriv Ω v₀ t : SobolevEuclidean (d + 1) 1 2 Ω)
        (sobolevZeroLiftDeriv Ω v₀ t : SobolevEuclidean (d + 1) 1 2 Ω)
      = ⟪dirichletLaplacian Ω ⟨deriv u t, h.deriv_mem_domain ht⟩, deriv u t⟫_ℝ :=
  (dirichletLaplacian_inner_self_eq_dirichletForm ⟨deriv u t, h.deriv_mem_domain ht⟩
    (sobolevZeroLiftDeriv Ω v₀ t).2 (h.fnL_sobolevZeroLiftDeriv hv₀ ht)).symm

/-- Let $\Omega$ be bounded, let $u$ be a solution with datum $u_0 \in D(A)$, and let $u_0$ be the
function of $v_0 \in H^1_0(\Omega)$. Then $t \mapsto \|z(t)\|_{H^1}^2$ is integrable on
$(0, \infty)$, where $z$ is the $H^1_0$-lift of $u'$.

The proof is Poincaré's inequality and the identity of Theorem 10.2 (b). -/
theorem integrableOn_norm_sq_sobolevZeroLiftDeriv
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (h : IsSolution Ω u₀ u) (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain)
    {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) :
    IntegrableOn (fun t ↦ ‖sobolevZeroLiftDeriv Ω v₀ t‖ ^ 2) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := SobolevEuclideanZero.exists_norm_sq_le_dirichletForm hΩb
  obtain ⟨hgi, -⟩ := integrableOn_Ioi_and_integral_le_of_forall_integral_le
    (g := fun t ↦ dirichletForm Ω (sobolevZeroLiftDeriv Ω v₀ t : SobolevEuclidean (d + 1) 1 2 Ω)
      (sobolevZeroLiftDeriv Ω v₀ t : SobolevEuclidean (d + 1) 1 2 Ω))
    (L := 1 / 2 * ‖dirichletLaplacian Ω ⟨u₀, hu₀⟩‖ ^ 2)
    (fun t _ ↦ dirichletForm_self_nonneg Ω _)
    (fun T hT ↦ (h.energy_domain hu₀ (fun t ht ↦ h.dirichletForm_sobolevZeroLiftDeriv hv₀ ht)
      hT).1) fun T hT ↦ by
      have := (h.energy_domain hu₀ (fun t ht ↦ h.dirichletForm_sobolevZeroLiftDeriv hv₀ ht) hT).2
      nlinarith [norm_nonneg (deriv u T)]
  refine (hgi.const_mul C).mono' (((contDiffOn_sobolevZeroLiftDeriv v₀).continuousOn.norm.pow 2
    |>.aestronglyMeasurable measurableSet_Ioi)) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t _ ↦ ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact hC _

/-- The clause $\partial_t u \in L^2(0, \infty; H^1_0(\Omega))$ of Theorem 10.2 (b) of
[brezis2011functional], for a bounded domain. Let $\Omega$ be bounded and let $u$ be a solution
with datum $u_0 \in D(A)$. Then on $(0, \infty)$ the curve $u'$ is the function of a curve in
$L^2((0, \infty); H^1_0(\Omega))$, namely the $H^1_0$-lift of $u'$. -/
theorem memLpThrough_sobolevZero_deriv_of_isBounded
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (h : IsSolution Ω u₀ u) (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain) :
    Bochner.MemLpThrough (SobolevMultiIndexZero.fnL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω volume) 2 (deriv u) (Ioi 0) := by
  obtain ⟨v₀, hv₀⟩ := dirichletLaplacian_exists_sobolevZero_lift ⟨u₀, hu₀⟩
  have hint := h.integrableOn_norm_sq_sobolevZeroLiftDeriv hΩb hu₀ hv₀
  have hint2 : IntegrableOn (fun t ↦ ‖sobolevZeroLiftDeriv Ω v₀ t‖ ^ (2 : ℝ≥0∞).toReal)
      (Ioi 0) := by
    refine hint.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
  exact Bochner.MemLpThrough.of_contDiffOnThrough_of_integrable
    (contDiffOn_sobolevZeroLiftDeriv v₀).continuousOn
    (fun t ht ↦ (h.fnL_sobolevZeroLiftDeriv hv₀ ht).symm) measurableSet_Ioi two_ne_zero
    ENNReal.ofNat_ne_top hint2

/-- Let $u$ be a solution with datum $u_0$, let $u_0$ be the function of $v_0 \in H^1_0(\Omega)$,
and let $t > 0$. Then the $0$-th coordinate of the lift of $S_{A_1}(t) v_0$ into $D(A_1)$ is the
$H^1_0$-lift $v(t)$ of $u$. -/
theorem applyL_zero_semigroupLift_H10_eq (h : IsSolution Ω u₀ u)
    {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) {t : ℝ} (ht : 0 < t) :
    applyL (dirichletLaplacianH10 Ω) 1 0 (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t)
      = sobolevZeroLift Ω u₀ t :=
  SobolevMultiIndexZero.fnL_injective
    ((h.fnL_applyL_zero_semigroupLift_H10 hv₀ ht).trans (h.fnL_sobolevZeroLift ht).symm)

/-- For $v_0 \in H^1_0(\Omega)$ and every $t$, the $H^1_0$-lift $z(t)$ of $u'$ has the norm
$\|z(t)\|_{H^1} = \|A_1 x_t\|_{H^1}$, where $x_t$ is the lift of $S_{A_1}(t) v_0$ into $D(A_1)$. -/
theorem _root_.Heat.norm_sobolevZeroLiftDeriv (v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω) (t : ℝ) :
    ‖sobolevZeroLiftDeriv Ω v₀ t‖
      = ‖applyL (dirichletLaplacianH10 Ω) 1 1 (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t)‖ :=
  norm_neg _

/-- Let $u$ be a solution with datum $u_0$, let $u_0$ be the function of $v_0 \in H^1_0(\Omega)$,
and let $t > 0$. Then the lift $x_t$ of $S_{A_1}(t) v_0$ into $D(A_1)$ has the graph norm
$$\|x_t\|_{D(A_1)}^2 = \|v(t)\|_{H^1}^2 + \|z(t)\|_{H^1}^2,$$
where $v$ is the $H^1_0$-lift of $u$ and $z$ is the $H^1_0$-lift of $u'$. -/
theorem norm_sq_semigroupLift_H10_one (h : IsSolution Ω u₀ u)
    {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) {t : ℝ} (ht : 0 < t) :
    ‖semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t‖ ^ 2
      = ‖sobolevZeroLift Ω u₀ t‖ ^ 2 + ‖sobolevZeroLiftDeriv Ω v₀ t‖ ^ 2 :=
  (norm_sq_powDomain_one _).trans (congrArg₂ (· + ·)
    (congrArg (‖·‖ ^ 2) (h.applyL_zero_semigroupLift_H10_eq hv₀ ht))
    (congrArg (· ^ 2) (Heat.norm_sobolevZeroLiftDeriv v₀ t).symm))

end IsSolution

variable (Ω) in
/-- The **$H^3$-lift of the solution curve** on a domain $\Omega$ of class $C^3$ with bounded
boundary, for $v_0 \in H^1_0(\Omega)$: the curve $t \mapsto U(t) \in H^3(\Omega)$ obtained by
applying the bounded injection $D(A_1) \to H^3(\Omega)$
(`dirichletLaplacianH10.powDomainOneToSobolevThreeL`) to the lift of $S_{A_1}(t) v_0$ into
$D(A_1)$. -/
def sobolevThreeLift (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω) (t : ℝ) : SobolevEuclidean (d + 1) 3 2 Ω :=
  dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ
    (semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t)

/-- The $H^3$-lift of the solution curve is of class $C^\infty$ on $(0, \infty)$. -/
theorem contDiffOn_sobolevThreeLift
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω) :
    ContDiffOn ℝ ∞ (sobolevThreeLift Ω hΩ hΓ v₀) (Ioi 0) :=
  (dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ).contDiff.comp_contDiffOn
    (contDiffOn_semigroupLift dirichletLaplacianH10_isMaximalMonotone
      dirichletLaplacianH10_isFormalAdjoint v₀ 1)

/-- For every $t$, the $H^3$-lift satisfies $\|U(t)\|_{H^3} \le \|J\| \, \|x_t\|_{D(A_1)}$, where
$J$ is the injection `dirichletLaplacianH10.powDomainOneToSobolevThreeL` and $x_t$ is the lift
of $S_{A_1}(t) v_0$ into $D(A_1)$. -/
theorem norm_sobolevThreeLift_le
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω) (t : ℝ) :
    ‖sobolevThreeLift Ω hΩ hΓ v₀ t‖
      ≤ ‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖
        * ‖semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t‖ :=
  (dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ).le_opNorm _

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- Let $u$ be a solution with datum $u_0$, let $u_0$ be the function of $v_0 \in H^1_0(\Omega)$,
and let $t > 0$. Then the function of the $H^3$-lift $U(t)$ is $u(t)$. -/
theorem fnL_sobolevThreeLift
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) {t : ℝ} (ht : 0 < t) :
    fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume
      (sobolevThreeLift Ω hΩ hΓ v₀ t) = u t :=
  (fnL_powDomainOneToSobolevThreeL hΩ hΓ _).trans (h.fnL_applyL_zero_semigroupLift_H10 hv₀ ht)

/-- Let $u$ be a solution with datum $u_0$, let $u_0$ be the function of $v_0 \in H^1_0(\Omega)$,
and let $t > 0$. Then
$$\|U(t)\|_{H^3}^2 \le \|J\|^2 \left( \|v(t)\|_{H^1}^2 + \|z(t)\|_{H^1}^2 \right),$$
where $U$ is the $H^3$-lift, $J$ is the injection
`dirichletLaplacianH10.powDomainOneToSobolevThreeL`, and $v$ and $z$ are the $H^1_0$-lifts of
$u$ and $u'$. -/
theorem norm_sq_sobolevThreeLift_le
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) {t : ℝ} (ht : 0 < t) :
    ‖sobolevThreeLift Ω hΩ hΓ v₀ t‖ ^ 2
      ≤ ‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖ ^ 2
        * (‖sobolevZeroLift Ω u₀ t‖ ^ 2 + ‖sobolevZeroLiftDeriv Ω v₀ t‖ ^ 2) := by
  have h1 := norm_sobolevThreeLift_le hΩ hΓ v₀ t
  have h2 := h.norm_sq_semigroupLift_H10_one hv₀ ht
  calc ‖sobolevThreeLift Ω hΩ hΓ v₀ t‖ ^ 2
      ≤ (‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖
        * ‖semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖ ^ 2
        * ‖semigroupLift (dirichletLaplacianH10 Ω) v₀ 1 t‖ ^ 2 := mul_pow _ _ 2
    _ = ‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖ ^ 2
        * (‖sobolevZeroLift Ω u₀ t‖ ^ 2 + ‖sobolevZeroLiftDeriv Ω v₀ t‖ ^ 2) :=
        congrArg (‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖ ^ 2 * ·) h2

/-- The bound of `Heat.IsSolution.norm_sq_sobolevThreeLift_le` for the absolute value
$\left| \|U(t)\|_{H^3}^2 \right|$, the form that the comparison test for integrability uses. -/
theorem norm_norm_sq_sobolevThreeLift_le
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) {t : ℝ} (ht : 0 < t) :
    ‖‖sobolevThreeLift Ω hΩ hΓ v₀ t‖ ^ 2‖
      ≤ ‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖ ^ 2
        * (‖sobolevZeroLift Ω u₀ t‖ ^ 2 + ‖sobolevZeroLiftDeriv Ω v₀ t‖ ^ 2) :=
  (Real.norm_of_nonneg (sq_nonneg _)).le.trans (h.norm_sq_sobolevThreeLift_le hΩ hΓ hv₀ ht)

/-- Let $\Omega$ be bounded and of class $C^3$ with bounded boundary, let $u$ be a solution with
datum $u_0 \in D(A)$, and let $u_0$ be the function of $v_0 \in H^1_0(\Omega)$. Then
$t \mapsto \|U(t)\|_{H^3}^2$ is integrable on $(0, \infty)$, where $U$ is the $H^3$-lift. -/
theorem integrableOn_norm_sq_sobolevThreeLift
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain)
    {v₀ : SobolevEuclideanZero (d + 1) 1 2 Ω}
    (hv₀ : SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 2 Ω
      volume v₀ = u₀) :
    IntegrableOn (fun t ↦ ‖sobolevThreeLift Ω hΩ hΓ v₀ t‖ ^ 2) (Ioi 0) := by
  have hint0 : IntegrableOn (fun t ↦ ‖dirichletLaplacianH10.powDomainOneToSobolevThreeL Ω hΩ hΓ‖ ^ 2
      * (‖sobolevZeroLift Ω u₀ t‖ ^ 2 + ‖sobolevZeroLiftDeriv Ω v₀ t‖ ^ 2)) (Ioi 0) :=
    ((h.integrableOn_norm_sq_sobolevZeroLift hΩb).add
      (h.integrableOn_norm_sq_sobolevZeroLiftDeriv hΩb hu₀ hv₀)).const_mul _
  exact hint0.mono' (((contDiffOn_sobolevThreeLift hΩ hΓ v₀).continuousOn.norm.pow 2
    |>.aestronglyMeasurable measurableSet_Ioi))
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦
      h.norm_norm_sq_sobolevThreeLift_le hΩ hΓ hv₀ ht)

/-- The clause $u \in L^2(0, \infty; H^3(\Omega))$ of Theorem 10.2 (b) of [brezis2011functional],
for a bounded domain. Let $\Omega$ be bounded and of class $C^3$ with bounded boundary, and let
$u$ be a solution with datum $u_0 \in D(A)$. Then on $(0, \infty)$ the curve $u$ is the function
of a curve in $L^2((0, \infty); H^3(\Omega))$.

This answers the question "why?" that the book asks at this clause. The $H^3$-lift $U$ satisfies
$\|U(t)\|_{H^3}^2 \le \|J\|^2 (\|v(t)\|_{H^1}^2 + \|z(t)\|_{H^1}^2)$, where $v$ and $z$ are the
$H^1_0$-lifts of $u$ and $u'$. Both are square integrable on $(0, \infty)$ by Poincaré's
inequality and the identities of Theorems 10.1 and 10.2 (b). -/
theorem memLpThrough_three_of_isBounded
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΩ : IsContDiffChartDomain 3 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (h : IsSolution Ω u₀ u) (hu₀ : u₀ ∈ (dirichletLaplacian Ω).domain) :
    Bochner.MemLpThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 3 2 Ω volume) 2
      u (Ioi 0) := by
  obtain ⟨v₀, hv₀⟩ := dirichletLaplacian_exists_sobolevZero_lift ⟨u₀, hu₀⟩
  have hint2 : IntegrableOn (fun t ↦ ‖sobolevThreeLift Ω hΩ hΓ v₀ t‖ ^ (2 : ℝ≥0∞).toReal)
      (Ioi 0) := by
    refine (h.integrableOn_norm_sq_sobolevThreeLift hΩb hΩ hΓ hu₀ hv₀).congr_fun (fun t _ ↦ ?_)
      measurableSet_Ioi
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
  exact Bochner.MemLpThrough.of_contDiffOnThrough_of_integrable
    (contDiffOn_sobolevThreeLift hΩ hΓ v₀).continuousOn
    (fun t ht ↦ (h.fnL_sobolevThreeLift hΩ hΓ hv₀ ht).symm) measurableSet_Ioi two_ne_zero
    ENNReal.ofNat_ne_top hint2

end IsSolution

end Heat

end SobolevThree

/-!
### The space–time reading: smoothness up to the boundary

The clauses $u \in C^\infty(\overline{\Omega} \times [\varepsilon, \infty))$ for every
$\varepsilon > 0$, and $u \in C^\infty(\overline{\Omega} \times [0, \infty))$ for a smooth datum.
-/

section SpaceTime

namespace Heat

open LinearPMap LinearPMap.PowDomain SobolevMultiIndex Elliptic

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

namespace IsSolution

variable {u₀ : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
  {u : ℝ → Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}

/-- Let $\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be a domain of class $C^\infty$ with bounded
boundary, and let $u$ be a solution. Then $u \in C^\infty((0, \infty); H^m(\Omega))$ for every
$m \in \mathbb{N}$.

The proof uses `Heat.IsSolution.contDiffOnThrough_sobolev` for every $\ell$ and lowers the order
from $2\ell$ to $m \le 2\ell$ (`Bochner.ContDiffOnThrough.sobolev_of_le`). -/
theorem contDiffOnThrough_sobolev_forall (h : IsSolution Ω u₀ u)
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) (m : ℕ) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis m 2 Ω
      volume) ∞ u (Ioi 0) :=
  (h.contDiffOnThrough_sobolev (ℓ := m) (hΩ.of_le (WithTop.coe_le_coe.2 le_top)) hΓ).sobolev_of_le
    (by omega)

/-- The clause (5) of Theorem 10.1 of [brezis2011functional], $u \in C^\infty(\overline{\Omega}
\times [\varepsilon, \infty))$ for every $\varepsilon > 0$. Let $\Omega \subseteq \mathbb{R}^N$,
$N = d + 1$, be a domain of class $C^\infty$ with bounded boundary, and let $u$ be a solution.
Then there is $U : \mathbb{R}^N \times \mathbb{R} \to \mathbb{R}$ such that $U(\cdot, t) = u(t)$
almost everywhere on $\Omega$ for every $t > 0$, and for every $\varepsilon > 0$, $U$ is of
class $C^\infty$ on $\Omega \times (\varepsilon, \infty)$ and every derivative of $U$ there
extends continuously to $\overline{\Omega} \times [\varepsilon, \infty)$.

The conclusion cannot be strengthened to $\overline{\Omega} \times [0, \infty)$: with a datum in
$L^2(\Omega)$ the solution is not smooth up to $t = 0$. The book uses Corollary 9.15 for
$H^{2\ell}(\Omega) \subseteq C^k(\overline{\Omega})$. The hypothesis of that corollary,
"$m - N/p$ is not an integer", fails at $p = 2$ for even $N$. The proof here uses the condition
$k + N/2 < m$ instead, which is valid for all $N$.

The class $C^\infty$ up to the closure is `ContDiffOnClosure`. The proof is
$u \in C^\infty((0, \infty); H^m(\Omega))$ for every $m$
(`Heat.IsSolution.contDiffOnThrough_sobolev_forall`) and the space–time result
`Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ioi`, for the extension domain
$\Omega$ (`IsSobolevExtensionDomainAll.of_isContDiffChartDomain`). -/
theorem contDiffOnClosure_spaceTime (h : IsSolution Ω u₀ u)
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ U : EuclideanSpace ℝ (Fin (d + 1)) × ℝ → ℝ,
      (∀ t ∈ Ioi (0 : ℝ),
        (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u t) ∧
      ∀ ε > (0 : ℝ),
        ContDiffOnClosure ℝ ∞ U ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ×ˢ Ioi ε) :=
  Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ioi
    (IsSobolevExtensionDomainAll.of_isContDiffChartDomain (hΩ.of_le (by simp)) hΓ)
    (h.contDiffOnThrough_sobolev_forall hΩ hΓ)

/-- Let $u$ be a solution with datum $u_0$, where $u_0 \in D(A^k)$ for every $k$, and let $\Omega$
be a domain of class $C^{2\ell}$ with bounded boundary. Then
$u \in C^\infty([0, \infty); H^{2\ell}(\Omega))$.

One lift serves for all orders. The lifts of
`Heat.IsSolution.contDiffOnThrough_sobolev_Ici_of_powDomain` at the orders $n$ agree on
$[0, \infty)$ (`SobolevMultiIndex.fnL_injective`), so the lift of order $0$ is of class $C^n$ on
$[0, \infty)$ for every $n$. -/
theorem contDiffOnThrough_sobolev_Ici_of_forall_powDomain (h : IsSolution Ω u₀ u)
    (hu₀ : ∀ k, ∃ x : (dirichletLaplacian Ω).PowDomain k, applyL (dirichletLaplacian Ω) k 0 x = u₀)
    {ℓ : ℕ}
    (hΩ : IsContDiffChartDomain (2 * ℓ) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω
      volume) ∞ u (Ici 0) := by
  have hn : ∀ n : ℕ, Bochner.ContDiffOnThrough
      (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (2 * ℓ) 2 Ω volume) n u (Ici 0) := by
    intro n
    obtain ⟨x, hx⟩ := hu₀ (ℓ + n)
    have := h.contDiffOnThrough_sobolev_Ici_of_powDomain x hx (ℓ := ℓ) (by omega) hΩ hΓ
    rwa [show ℓ + n - ℓ = n by omega] at this
  obtain ⟨v, hv0, huv⟩ := hn 0
  refine ⟨v, ?_, huv⟩
  rw [contDiffOn_infty]
  intro n
  obtain ⟨w, hw, huw⟩ := hn n
  refine hw.congr fun t ht ↦ ?_
  exact fnL_injective ((huv t ht).symm.trans (huw t ht))

/-- Let $u$ be a solution with datum $u_0$, where $u_0 \in D(A^k)$ for every $k$, and let $\Omega$
be a domain of class $C^\infty$ with bounded boundary. Then
$u \in C^\infty([0, \infty); H^m(\Omega))$ for every $m \in \mathbb{N}$. -/
theorem contDiffOnThrough_sobolev_Ici_forall (h : IsSolution Ω u₀ u)
    (hu₀ : ∀ k, ∃ x : (dirichletLaplacian Ω).PowDomain k, applyL (dirichletLaplacian Ω) k 0 x = u₀)
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) (m : ℕ) :
    Bochner.ContDiffOnThrough (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis m 2 Ω
      volume) ∞ u (Ici 0) :=
  (h.contDiffOnThrough_sobolev_Ici_of_forall_powDomain hu₀ (ℓ := m)
    (hΩ.of_le (WithTop.coe_le_coe.2 le_top)) hΓ).sobolev_of_le (by omega)

/-- Theorem 10.2 (c) of [brezis2011functional]. Let $\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be
a domain of class $C^\infty$ with bounded boundary, and let $u$ be a solution with datum
$u_0 \in D(A^k)$ for every $k$. Then $u \in C^\infty(\overline{\Omega} \times [0, \infty))$:
there is $U : \mathbb{R}^N \times \mathbb{R} \to \mathbb{R}$ such that $U(\cdot, t) = u(t)$
almost everywhere on $\Omega$ for every $t \ge 0$, $U$ is of class $C^\infty$ on
$\Omega \times (0, \infty)$, and every derivative of $U$ there extends continuously to
$\overline{\Omega} \times [0, \infty)$.

The book states the hypothesis as $u_0 \in H^{2k}(\Omega)$ for every $k$ with the compatibility
conditions (8), $\Delta^j u_0 = 0$ on $\Gamma$. It is equivalent to $u_0 \in D(A^k)$ for every
$k$ by `dirichletLaplacian_mem_powDomain_iff`.

The proof is $u \in C^\infty([0, \infty); H^m(\Omega))$ for every $m$
(`Heat.IsSolution.contDiffOnThrough_sobolev_Ici_forall`) and the space–time result on
$[0, \infty)$ (`Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici`). -/
theorem contDiffOnClosure_spaceTime_Ici (h : IsSolution Ω u₀ u)
    (hu₀ : ∀ k, ∃ x : (dirichletLaplacian Ω).PowDomain k, applyL (dirichletLaplacian Ω) k 0 x = u₀)
    (hΩ : IsContDiffChartDomain ∞ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ U : EuclideanSpace ℝ (Fin (d + 1)) × ℝ → ℝ,
      (∀ t ∈ Ici (0 : ℝ),
        (fun x ↦ U (x, t)) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] u t) ∧
      ContDiffOnClosure ℝ ∞ U ((Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ×ˢ Ioi 0) :=
  Bochner.contDiffOnClosure_spaceTime_of_forall_contDiffOnThrough_Ici
    (IsSobolevExtensionDomainAll.of_isContDiffChartDomain (hΩ.of_le (by simp)) hΓ)
    (h.contDiffOnThrough_sobolev_Ici_forall hu₀ hΩ hΓ)

end IsSolution

end Heat

end SpaceTime
