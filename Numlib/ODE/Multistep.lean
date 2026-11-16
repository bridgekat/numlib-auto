/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Lagrange
import Numlib.Analysis.Asymptotics.Pow
import Numlib.Analysis.Calculus.Taylor
import Numlib.Analysis.LinearRecurrence
import Numlib.Data.Fin.Sum
import Numlib.ODE.OneStep
import Numlib.RingTheory.Polynomial.SchurCohn

/-!
# Linear multistep methods

A linear multistep method with $p + 1$ steps approximates the solution of the Cauchy problem
$y' = f(t, y)$, with values in a real normed space $E$, at the nodes $t_n = t_0 + nh$ by the
recursion
$$u_{n+1} = \sum_{j=0}^p a_j u_{n-j} + h \sum_{j=0}^p b_j f_{n-j} + h b_{-1} f_{n+1},
  \qquad f_k = f(t_k, u_k),$$
with real coefficients $a_j$, $b_j$ and $b_{-1}$. The method is explicit if $b_{-1} = 0$ and
implicit otherwise. This module develops the theory of linear multistep methods of
[quarteroni2000numerical], §11.5–11.7, which [hairer1993solving], Sections III.2–III.4, also
presents. On a horizon $[t_0, t_0 + T]$ the method takes the steps $p \le n < N_h$, where
$N_h = \lfloor T / h \rfloor$.

The local truncation error $\tau_{n+1}(h)$ is $h^{-1} \mathcal{L}[y; h](t_n)$, where
$$\mathcal{L}[w; h](t) = w(t + h) - \sum_{j=0}^p a_j w(t - jh) - h \sum_{j=-1}^p b_j w'(t - jh),$$
and $\tau(h)$ is its maximum over the steps. The method has order $q$ if and only if the order
conditions $\sum_j (-j)^i a_j + i \sum_{j=-1}^p (-j)^{i-1} b_j = 1$ hold for $i \le q$ (Theorem 11.3
of [quarteroni2000numerical]). With the characteristic polynomials
$\rho(r) = r^{p+1} - \sum_j a_j r^{p-j}$ and $\sigma(r) = b_{-1} r^{p+1} + \sum_j b_j r^{p-j}$, the
method is zero-stable for every scalar field that is Lipschitz in the state if and only if $\rho$
satisfies the root condition (Theorem 11.4), and a consistent method converges if and only if it is
zero-stable (Theorem 11.5 and Corollary 11.1). The module also treats absolute stability through the
polynomial $\Pi_z = \rho - z \sigma$, the Adams, BDF, midpoint and Simpson methods, and
predictor–corrector pairs with their order (Property 11.3).

## Main definitions

* `ODE.LinearMultistep`: the coefficients $p$, $a_0, \dots, a_p$, $b_0, \dots, b_p$ and $b_{-1}$ of
  a method.
* `ODE.LinearMultistep.IsOrbit`, `ODE.LinearMultistep.IsOrbitWith`: a sequence that satisfies the
  recursion, without or with a perturbation $h \delta_{n+1}$.
* `ODE.LinearMultistep.opL`, `ODE.LinearMultistep.lte`, `ODE.LinearMultistep.globalLte`: the
  operator $\mathcal{L}$, the local truncation error $\tau_{n+1}(h)$ and the global truncation error
  $\tau(h)$.
* `ODE.LinearMultistep.IsConsistent`, `ODE.LinearMultistep.HasOrder`: consistency and order $q$ of
  the method.
* `ODE.LinearMultistep.orderCondition`, `ODE.LinearMultistep.taylorCoeff`,
  `ODE.LinearMultistep.errorConstant`: the order conditions, the Taylor coefficients $c_m$ of
  $\mathcal{L}$ and the error constant $c_{q+1} / (q + 1)!$.
* `ODE.LinearMultistep.rho`, `ODE.LinearMultistep.sigma`, `ODE.LinearMultistep.charPoly`: the
  polynomials $\rho$, $\sigma$ and $\Pi_z = \rho - z \sigma$.
* `ODE.LinearMultistep.SatisfiesRootCondition`: every root of $\rho$ lies in the closed unit disc,
  and the roots on the unit circle are simple.
* `ODE.LinearMultistep.IsZeroStable`, `ODE.LinearMultistep.IsConvergentFor`: zero-stability and
  convergence for one field on one horizon.
* `ODE.LinearMultistep.absStabilityRegion`, `ODE.LinearMultistep.absStabilityRegionStar`: the set
  $\mathcal{A}$ of $z = h\lambda$ at which all solutions on $y' = \lambda y$ tend to zero, and the
  set $\mathcal{A}^*$ at which they are bounded.
* `ODE.LinearMultistep.IsAStable`, `ODE.LinearMultistep.IsThetaStable`: A-stability and ϑ-stability.
* `ODE.LinearMultistep.adamsBashforth`, `ODE.LinearMultistep.adamsMoulton`,
  `ODE.LinearMultistep.bdf`, `ODE.LinearMultistep.midpoint`, `ODE.LinearMultistep.simpson`: the
  classical methods.
* `ODE.PredictorCorrector`, `ODE.PredictorCorrector.IsOrbitPEC`,
  `ODE.PredictorCorrector.IsOrbitPECE`: a predictor–corrector pair and its $P(EC)^m$ and $P(EC)^m E$
  schemes.

## Main results

* `ODE.LinearMultistep.isConsistent_iff`, `ODE.LinearMultistep.hasOrder_iff`: the method is
  consistent if and only if the order conditions $0$ and $1$ hold, and it has order $q$ if and only
  if the order conditions $0, \dots, q$ hold.
* `ODE.LinearMultistep.norm_sub_le_of_satisfiesRootCondition`: under the root condition, two
  solutions of the scheme, one of them perturbed, differ by at most
  $K(\varepsilon_0 + T \varepsilon_1)$.
* `ODE.LinearMultistep.isZeroStable_iff_satisfiesRootCondition`: the method is zero-stable for every
  scalar field that is Lipschitz in the state if and only if it satisfies the root condition.
* `ODE.LinearMultistep.isConvergentFor_of_satisfiesRootCondition`,
  `ODE.LinearMultistep.satisfiesRootCondition_of_isConvergentFor`: under the root condition a
  consistent method converges, and convergence on $y' = 0$ forces the root condition.
* `ODE.LinearMultistep.isConvergentFor_iff_isZeroStable`: a consistent method is convergent for all
  Lipschitz scalar problems with a $C^1$ solution if and only if it is zero-stable for all Lipschitz
  scalar problems.
* `ODE.LinearMultistep.mem_absStabilityRegion_iff`: $z \in \mathcal{A}$ if and only if
  $1 - z b_{-1} \neq 0$ and every root of $\Pi_z$ has modulus less than $1$.
* `ODE.LinearMultistep.adamsBashforth_hasOrder`, `ODE.LinearMultistep.adamsMoulton_hasOrder`,
  `ODE.LinearMultistep.bdf_hasOrder`: the orders of the Adams and BDF methods.
* `ODE.LinearMultistep.bdf_satisfiesRootCondition_all`: the six BDF methods satisfy the root
  condition.
* `ODE.LinearMultistep.absStabilityRegion_midpoint`: the midpoint method has
  $\mathcal{A} = \emptyset$ and $\mathcal{A}^* = \{ i\alpha : |\alpha| < 1 \}$.
* `ODE.LinearMultistep.not_isAStable_of_bm1_eq_zero`: an explicit method with $\sum_j a_j = 1$ is
  not A-stable.
* `ODE.PredictorCorrector.heun_eq_pece`: Heun's method is the $P(EC)E$ scheme of forward Euler and
  Crank–Nicolson.
* `ODE.PredictorCorrector.hasOrderFor_of`: a pair with a predictor of order $\tilde q$ and a
  corrector of order $q$ has order $\min(q, \tilde q + m)$ in the $P(EC)^m E$ mode.

## Proof outline

The order conditions come from the Taylor expansion of $\mathcal{L}[w; h](t)$ about $t$:
$\mathcal{L}[w; h](t) = \sum_{m \le q} (h^m / m!) c_m w^{(m)}(t) + O(h^{q+1})$, where $c_m$ is $1$
minus the left side of the $m$-th order condition. For the converse, the monomials $t \mapsto t^i$
have the truncation error $h^{i-1} c_i$, which is $O(h^q)$ only if $c_i = 0$. For zero-stability,
the difference of a perturbed and an unperturbed solution solves the linear recurrence with
characteristic polynomial $\rho$, with a source that the Lipschitz constant bounds; the bound for
such recurrences under the root condition (Lemma 11.3 of [quarteroni2000numerical], which extends
from complex scalar sequences to sequences in $E$ through a norming functional given by the
Hahn–Banach theorem) and the discrete Gronwall lemma give the estimate. When the root condition
fails, the recurrence has an unbounded real solution, which is a perturbed solution of the scheme
for $y' = 0$. Convergence follows from the same estimate with the perturbation
$\delta_{n+1} = \tau_{n+1}(h)$; its necessity uses a solution that grows at least linearly, scaled
by $h$. The orders of the Adams methods follow from the exactness of interpolatory quadrature on
polynomials, and the zero-stability of the BDF methods with four to six steps from the Schur–Cohn
test.

## Implementation notes

* The normalization $a_p \neq 0$ or $b_p \neq 0$ of the source is not part of the structure, because
  a predictor–corrector pair pads a corrector with zero coefficients. It is the separate predicate
  `ODE.LinearMultistep.IsGenuine`.
* Sequences are indexed by $\mathbb{N}$. The recursion is imposed at every $n \ge p$ and written for
  $u_{n+p+1}$, so that no natural subtraction underflows. The $p + 1$ starting values
  $u_0, \dots, u_p$ are free.
* The operator $\mathcal{L}$ uses the derivative `deriv w` of the curve, not the field $f$.
* `ODE.LinearMultistep.IsConsistent` and `ODE.LinearMultistep.HasOrder` quantify over all real $C^1$
  (respectively $C^{q+1}$) curves on all horizons $T > 0$. Every such curve $y$ solves
  $y' = f(t, y)$ for the field $f(t, v) = y'(t)$, which is Lipschitz in $v$ with constant $0$, so
  this is the same as quantifying over all scalar Cauchy problems with such a solution.
* The root conditions are those of `Polynomial.SatisfiesRootCondition` and
  `Polynomial.SatisfiesStrongRootCondition` for $\rho$ read in $\mathbb{C}[X]$.
* The difference equations are Mathlib's `LinearRecurrence`, with the convention
  $u_{n+k} = \sum_{i<k} \alpha_i u_{n+i}$. The real recurrence of the method has the coefficients
  $\alpha_i = a_{p-i}$.
* The regions $\mathcal{A}$ and $\mathcal{A}^*$ contain only points $z$ with $1 - z b_{-1} \neq 0$,
  at which the scheme on $y' = \lambda y$ determines $u_{n+1}$.
* Theorem 11.4 is proved without the consistency hypothesis of [quarteroni2000numerical], and
  Theorem 11.3 also for $q = 0$.
* Table 11.2 of [quarteroni2000numerical] prints $b_{-1} = 60/137$ in its last row. This is a
  misprint: with it the order condition $1$ fails. `ODE.LinearMultistep.bdf` uses $60/147$.
* Remark 11.3 of [quarteroni2000numerical] prints $\mathcal{A}^* = \{ i\alpha : \alpha \in [-1, 1]
  \}$ for the midpoint method. At $\alpha = \pm 1$ the root $\pm i$ of $\Pi_z$ is double, so the
  endpoints are excluded.
* The first Dahlquist barrier, the order bound of the second barrier and Widlund's statement on
  ϑ-stability are not formalized. The explicit clause of the second barrier is proved here.
-/

open Set Filter Topology Asymptotics Polynomial
open Finset (range)

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A **linear multistep method** with $p + 1$ steps is given by real coefficients
$a_0, \dots, a_p$, $b_0, \dots, b_p$ and $b_{-1}$. It defines the scheme (11.45) of
[quarteroni2000numerical]
$$u_{n+1} = \sum_{j=0}^p a_j u_{n-j} + h \sum_{j=0}^p b_j f_{n-j} + h b_{-1} f_{n+1},
  \qquad f_k = f(t_k, u_k).$$

The coefficient $b_{-1}$ is the field `bm1`. The normalization $a_p \neq 0$ or $b_p \neq 0$ of
the source is not part of the structure; it is the predicate `ODE.LinearMultistep.IsGenuine`. -/
structure LinearMultistep where
  /-- The number $p$; the method has $p + 1$ steps. -/
  p : ℕ
  /-- The coefficients $a_0, \dots, a_p$ of the past values $u_n, \dots, u_{n-p}$. -/
  a : Fin (p + 1) → ℝ
  /-- The coefficients $b_0, \dots, b_p$ of the past function values $f_n, \dots, f_{n-p}$. -/
  b : Fin (p + 1) → ℝ
  /-- The coefficient $b_{-1}$ of $f_{n+1}$. The method is implicit if and only if $b_{-1} \neq 0$.
  -/
  bm1 : ℝ

namespace LinearMultistep

variable (M : LinearMultistep) {f : ℝ → E → E} {h t₀ T : ℝ} {n : ℕ}

/-- A method is **implicit** if $b_{-1} \neq 0$ ([quarteroni2000numerical], §11.5). -/
def IsImplicit : Prop := M.bm1 ≠ 0

/-- A method is **genuine** if $a_p \neq 0$ or $b_p \neq 0$, so that it really uses $p + 1$ steps.
This is the normalization of [quarteroni2000numerical], §11.5. -/
def IsGenuine : Prop := M.a (Fin.last M.p) ≠ 0 ∨ M.b (Fin.last M.p) ≠ 0

/-! ### Orbits -/

/-- The **right-hand side of the scheme** (11.45) of [quarteroni2000numerical] at the step from
$t_{n+p}$ to $t_{n+p+1}$, for a sequence $w$:
$$\sum_{j=0}^p a_j w_{n+p-j} + h \sum_{j=0}^p b_j f(t_{n+p-j}, w_{n+p-j}) + h b_{-1}
  f(t_{n+p+1}, w_{n+p+1}),$$
where $t_k = t_0 + kh$. The last term contains the new value $w_{n+p+1}$ when the method is
implicit. -/
def rhs (f : ℝ → E → E) (h t₀ : ℝ) (w : ℕ → E) (n : ℕ) : E :=
  ∑ j : Fin (M.p + 1), M.a j • w (n + M.p - j) +
    h • ∑ j : Fin (M.p + 1), M.b j • f (node t₀ h (n + M.p - j)) (w (n + M.p - j)) +
    (h * M.bm1) • f (node t₀ h (n + M.p + 1)) (w (n + M.p + 1))

/-- A **perturbed orbit** of the method for the field $f$, with step $h$ from the time $t_0$ and
perturbation $\delta$, is a sequence $z$ such that for every $n \ge p$
$$z_{n+1} = \sum_{j=0}^p a_j z_{n-j} + h \sum_{j=0}^p b_j f(t_{n-j}, z_{n-j}) + h b_{-1}
  f(t_{n+1}, z_{n+1}) + h \delta_{n+1}.$$
This is (11.59) of [quarteroni2000numerical].

The starting values $z_0, \dots, z_p$ are not constrained. The recursion is written for
$z_{n+p+1}$ with $n \in \mathbb{N}$, through `ODE.LinearMultistep.rhs`. -/
def IsOrbitWith (f : ℝ → E → E) (h t₀ : ℝ) (δ : ℕ → E) (z : ℕ → E) : Prop :=
  ∀ n, z (n + M.p + 1) = M.rhs f h t₀ z n + h • δ (n + M.p + 1)

/-- An **orbit** of the method is a perturbed orbit with zero perturbation: a sequence that
satisfies the scheme (11.45) of [quarteroni2000numerical] at every $n \ge p$, from arbitrary
starting values. This is (11.60) of the source. -/
def IsOrbit (f : ℝ → E → E) (h t₀ : ℝ) (u : ℕ → E) : Prop := M.IsOrbitWith f h t₀ 0 u

/-- A sequence $z$ is a perturbed orbit with perturbation $\delta$ if and only if, for every $n$,
$z_{n+p+1}$ equals the right-hand side of the scheme at $n + p$ plus $h \delta_{n+p+1}$, written
out in full. -/
theorem isOrbitWith_iff {δ z : ℕ → E} :
    M.IsOrbitWith f h t₀ δ z ↔ ∀ n, z (n + M.p + 1) =
      ∑ j : Fin (M.p + 1), M.a j • z (n + M.p - j) +
      h • ∑ j : Fin (M.p + 1), M.b j • f (node t₀ h (n + M.p - j)) (z (n + M.p - j)) +
      (h * M.bm1) • f (node t₀ h (n + M.p + 1)) (z (n + M.p + 1)) + h • δ (n + M.p + 1) :=
  Iff.rfl

/-- A sequence $u$ is an orbit if and only if it satisfies the scheme (11.45), written out in full,
at every $n \ge p$. -/
theorem isOrbit_iff {u : ℕ → E} :
    M.IsOrbit f h t₀ u ↔ ∀ n, u (n + M.p + 1) = ∑ j : Fin (M.p + 1), M.a j • u (n + M.p - j) +
      h • ∑ j : Fin (M.p + 1), M.b j • f (node t₀ h (n + M.p - j)) (u (n + M.p - j)) +
      (h * M.bm1) • f (node t₀ h (n + M.p + 1)) (u (n + M.p + 1)) := by
  simp [IsOrbit, IsOrbitWith, rhs]

/-- A sequence $u$ is an orbit if and only if $u_{n+p+1}$ equals `ODE.LinearMultistep.rhs` at $n$
for every $n$. -/
theorem isOrbit_iff_rhs {u : ℕ → E} :
    M.IsOrbit f h t₀ u ↔ ∀ n, u (n + M.p + 1) = M.rhs f h t₀ u n :=
  M.isOrbit_iff

/-! ### The operator $\mathcal{L}$ and the local and global truncation errors -/

/-- The **linear operator** $\mathcal{L}$ of the method, (11.48) of [quarteroni2000numerical]: for a
curve $w \colon \mathbb{R} \to E$, a step $h$ and a time $t$,
$$\mathcal{L}[w; h](t) = w(t + h) - \sum_{j=0}^p a_j w(t - jh) - h \Bigl( b_{-1} w'(t + h) +
  \sum_{j=0}^p b_j w'(t - jh) \Bigr).$$

The derivative $w'$ is `deriv w`, which is $0$ at a point where $w$ is not differentiable. -/
noncomputable def opL (h : ℝ) (w : ℝ → E) (t : ℝ) : E :=
  w (t + h) - ∑ j : Fin (M.p + 1), M.a j • w (t - j * h) -
    h • (M.bm1 • deriv w (t + h) + ∑ j : Fin (M.p + 1), M.b j • deriv w (t - j * h))

/-- The operator $\mathcal{L}$ is additive in the curve: if $w$ and $v$ are differentiable
everywhere, then $\mathcal{L}[w + v; h](t) = \mathcal{L}[w; h](t) + \mathcal{L}[v; h](t)$. -/
theorem opL_add (h : ℝ) (w v : ℝ → E) (t : ℝ) (hw : ∀ s, DifferentiableAt ℝ w s)
    (hv : ∀ s, DifferentiableAt ℝ v s) : M.opL h (w + v) t = M.opL h w t + M.opL h v t := by
  simp only [opL, Pi.add_apply, deriv_add (hw _) (hv _), smul_add, Finset.sum_add_distrib]
  abel

/-- The operator $\mathcal{L}$ is homogeneous in the curve: if $w$ is differentiable everywhere,
then $\mathcal{L}[cw; h](t) = c \, \mathcal{L}[w; h](t)$ for every real $c$. -/
theorem opL_smul (h : ℝ) (c : ℝ) (w : ℝ → E) (t : ℝ) (hw : ∀ s, DifferentiableAt ℝ w s) :
    M.opL h (c • w) t = c • M.opL h w t := by
  simp only [opL, Pi.smul_apply, deriv_const_smul c (hw _), smul_sub, smul_add, Finset.smul_sum,
    smul_comm c]

/-- The **local truncation error** of the method along the curve $y$ at the time $t$ is
$$\tau(h; t) = h^{-1} \mathcal{L}[y; h](t).$$
At $t = t_n$ this is $\tau_{n+1}(h)$ of Definition 11.8 and (11.47) of
[quarteroni2000numerical].

At $h = 0$ the value is $0$, since $0^{-1} = 0$ in Lean. -/
noncomputable def lte (h : ℝ) (y : ℝ → E) (t : ℝ) : E := h⁻¹ • M.opL h y t

/-- The local truncation error is $h^{-1} \mathcal{L}[y; h](t)$. -/
theorem lte_eq (h : ℝ) (y : ℝ → E) (t : ℝ) : M.lte h y t = h⁻¹ • M.opL h y t := rfl

/-- If $j \le m$, then $t_m - jh = t_{m-j}$ for the nodes $t_k = t_0 + kh$. -/
theorem node_sub_mul {j m : ℕ} (hj : j ≤ m) :
    node t₀ h m - j * h = node t₀ h (m - j) := by
  simp only [node, Nat.cast_sub hj]
  ring

/-- The exact curve satisfies the scheme up to $h$ times its local truncation error, (11.47) of
[quarteroni2000numerical]. Let $h \neq 0$, and let $y \colon \mathbb{R} \to E$ satisfy
$y'(s) = f(s, y(s))$ at the points $s = t - jh$, $j = -1, 0, \dots, p$, where $y'$ is `deriv y`.
Then
$$y(t + h) = \sum_{j=0}^p a_j y(t - jh) + h \sum_{j=0}^p b_j f(t - jh, y(t - jh)) + h b_{-1}
  f(t + h, y(t + h)) + h \tau(h; t).$$
-/
theorem lte_spec (hh : h ≠ 0) {y : ℝ → E} {t : ℝ}
    (hd : ∀ j : Fin (M.p + 1), deriv y (t - j * h) = f (t - j * h) (y (t - j * h)))
    (hd' : deriv y (t + h) = f (t + h) (y (t + h))) :
    y (t + h) = ∑ j : Fin (M.p + 1), M.a j • y (t - j * h) +
      h • ∑ j : Fin (M.p + 1), M.b j • f (t - j * h) (y (t - j * h)) +
      (h * M.bm1) • f (t + h) (y (t + h)) + h • M.lte h y t := by
  have e : h • M.lte h y t = M.opL h y t := by
    rw [lte, smul_smul, mul_inv_cancel₀ hh, one_smul]
  rw [e, opL]
  simp only [hd, hd']
  module

/-- The **global truncation error** of the method along the curve $y$ on the horizon
$[t_0, t_0 + T]$ is
$$\tau(h) = \max_{p \le n < N_h} \|\tau_{n+1}(h)\|, \qquad N_h = \lfloor T / h \rfloor,$$
the maximum over the steps that the method takes, with $\tau_{n+1}(h)$ the local truncation
error at $t_n = t_0 + nh$. It is $0$ when the method takes no step.

The maximum is a supremum over $n < N_h$ in which the terms with $n < p$ are $0$. -/
noncomputable def globalLte (t₀ T : ℝ) (y : ℝ → E) (h : ℝ) : ℝ :=
  ⨆ n : Fin (gridCount T h), if M.p ≤ (n : ℕ) then ‖M.lte h y (node t₀ h n)‖ else 0

/-- The local truncation error of each step taken on the grid is bounded by the global one: if
$p \le n < N_h$, then $\|\tau_{n+1}(h)\| \le \tau(h)$. -/
theorem norm_lte_le_globalLte {y : ℝ → E} (hp : M.p ≤ n) (hn : n < gridCount T h) :
    ‖M.lte h y (node t₀ h n)‖ ≤ M.globalLte t₀ T y h := by
  refine le_ciSup_of_le (f := fun n : Fin (gridCount T h) =>
    if M.p ≤ (n : ℕ) then ‖M.lte h y (node t₀ h n)‖ else 0) (Finite.bddAbove_range _) ⟨n, hn⟩ ?_
  simp [hp]

/-- The global truncation error is nonnegative. -/
theorem globalLte_nonneg (y : ℝ → E) : 0 ≤ M.globalLte t₀ T y h :=
  Real.iSup_nonneg fun _ => by split_ifs <;> simp

/-- Let $C \ge 0$. If $\|\tau_{n+1}(h)\| \le C$ for every step $p \le n < N_h$, then
$\tau(h) \le C$. -/
theorem globalLte_le {y : ℝ → E} {C : ℝ} (hC : 0 ≤ C)
    (hle : ∀ n, M.p ≤ n → n < gridCount T h → ‖M.lte h y (node t₀ h n)‖ ≤ C) :
    M.globalLte t₀ T y h ≤ C :=
  Real.iSup_le (fun i => by split_ifs with hi; exacts [hle i hi i.2, hC]) hC

/-- The method is **consistent along the curve** $y$ on the horizon $[t_0, t_0 + T]$ if the global
truncation error $\tau(h)$ tends to $0$ as $h \to 0^+$. This is Definition 11.9 of
[quarteroni2000numerical] for one solution. -/
def IsConsistentFor (t₀ T : ℝ) (y : ℝ → E) : Prop :=
  Tendsto (M.globalLte t₀ T y) (𝓝[>] 0) (𝓝 0)

/-- The method has **order $q$ along the curve** $y$ on the horizon $[t_0, t_0 + T]$ if
$\tau(h) = O(h^q)$ as $h \to 0^+$. This is Definition 11.9 of [quarteroni2000numerical] for one
solution. -/
def HasOrderFor (t₀ T : ℝ) (y : ℝ → E) (q : ℕ) : Prop :=
  M.globalLte t₀ T y =O[𝓝[>] 0] fun h => h ^ q

/-- If the method has order $q \ge 1$ along a curve, then it is consistent along that curve. -/
theorem HasOrderFor.isConsistentFor {y : ℝ → E} {q : ℕ} (hq : 1 ≤ q)
    (hM : M.HasOrderFor t₀ T y q) : M.IsConsistentFor t₀ T y :=
  hM.trans_tendsto <| ((continuous_pow q).tendsto' 0 0
    (by simp [zero_pow (Nat.one_le_iff_ne_zero.1 hq)])).mono_left nhdsWithin_le_nhds

/-- The method is **consistent** if it is consistent along every real $C^1$ curve $y$ on every
horizon $[t_0, t_0 + T]$ with $T > 0$. This is Definition 11.9 of [quarteroni2000numerical].

Every $C^1$ curve $y$ solves the scalar Cauchy problem with the field $f(t, v) = y'(t)$, which
does not depend on the state and is Lipschitz with constant $0$. Hence this definition is
consistency for every scalar problem with a $C^1$ solution. -/
def IsConsistent : Prop :=
  ∀ t₀ T : ℝ, 0 < T → ∀ y : ℝ → ℝ, ContDiff ℝ 1 y → M.IsConsistentFor t₀ T y

/-- The method has **order $q$** if it has order $q$ along every real $C^{q+1}$ curve on every
horizon $[t_0, t_0 + T]$ with $T > 0$. This is Definition 11.9 of [quarteroni2000numerical].

As for `ODE.LinearMultistep.IsConsistent`, the quantification over curves is a quantification
over all scalar Cauchy problems with a $C^{q+1}$ solution. -/
def HasOrder (q : ℕ) : Prop :=
  ∀ t₀ T : ℝ, 0 < T → ∀ y : ℝ → ℝ, ContDiff ℝ (q + 1) y → M.HasOrderFor t₀ T y q

/-! ### The order conditions -/

/-- The **$i$-th order condition** of the method, from Theorem 11.3 of [quarteroni2000numerical]:
$$\sum_{j=0}^p (-j)^i a_j + i \Bigl( b_{-1} + \sum_{j=0}^p (-j)^{i-1} b_j \Bigr) = 1.$$
For $i = 0$ it reads $\sum_j a_j = 1$ (`ODE.LinearMultistep.orderCondition_zero`). The
conditions $0$ and $1$ are the consistency conditions (11.52) of the source.

The term $b_{-1}$ is the term $j = -1$, since $(-(-1))^{i-1} = 1$. For $i = 0$ the exponent
$i - 1$ is the natural subtraction $0$, which does not matter because the factor $i$ is $0$. -/
def orderCondition (i : ℕ) : Prop :=
  ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ i * M.a j +
    i * (M.bm1 + ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ (i - 1) * M.b j) = 1

/-- The order condition $0$ is $\sum_{j=0}^p a_j = 1$. -/
theorem orderCondition_zero : M.orderCondition 0 ↔ ∑ j, M.a j = 1 := by
  simp [orderCondition]

/-- The order condition $i + 1$ is
$$\sum_{j=0}^p (-j)^{i+1} a_j + (i + 1) \Bigl( b_{-1} + \sum_{j=0}^p (-j)^i b_j \Bigr) = 1.$$
-/
theorem orderCondition_succ (i : ℕ) :
    M.orderCondition (i + 1) ↔ ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ (i + 1) * M.a j +
      (i + 1 : ℝ) * (M.bm1 + ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ i * M.b j) = 1 := by
  simp [orderCondition]

/-- The order condition $1$ is $-\sum_j j a_j + \sum_{j=-1}^p b_j = 1$, the second condition of
(11.52) of [quarteroni2000numerical]. -/
theorem orderCondition_one :
    M.orderCondition 1 ↔ -∑ j : Fin (M.p + 1), (j : ℝ) * M.a j + (M.bm1 + ∑ j, M.b j) = 1 := by
  simp [orderCondition, Finset.sum_neg_distrib]

/-- The **Taylor coefficients** of the method are
$$c_m = 1 - \sum_{j=0}^p (-j)^m a_j - m \Bigl( b_{-1} + \sum_{j=0}^p (-j)^{m-1} b_j \Bigr).$$
They are the coefficients of the Taylor expansion $\mathcal{L}[w; h](t) = \sum_m (h^m / m!) c_m
w^{(m)}(t)$ of the operator $\mathcal{L}$ about $t$, and $c_m = 0$ is the $m$-th order
condition.

The expansion follows [quarteroni2000numerical], §11.5, which expands about $t_{n-p}$ instead of
$t_n$. The conditions $c_0 = \dots = c_q = 0$ and the value of $c_{q+1}$ under them do not
depend on the point of expansion. -/
noncomputable def taylorCoeff (m : ℕ) : ℝ :=
  1 - ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ m * M.a j -
    m * (M.bm1 + ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ (m - 1) * M.b j)

/-- The $m$-th order condition holds if and only if the $m$-th Taylor coefficient $c_m$ is $0$. -/
theorem orderCondition_iff_taylorCoeff_eq_zero (m : ℕ) :
    M.orderCondition m ↔ M.taylorCoeff m = 0 := by
  rw [orderCondition, taylorCoeff, sub_sub, sub_eq_zero, eq_comm]

/-- The **error constant** of a method of order $q$ is
$$C_{q+1} = \frac{c_{q+1}}{(q + 1)!}
  = \frac{1 - \sum_{j=0}^p (-j)^{q+1} a_j - (q + 1) \sum_{j=-1}^p (-j)^q b_j}{(q + 1)!},$$
the coefficient of $h^{q+1} y^{(q+1)}(t_n)$ in the principal part of $h \tau_{n+1}(h)$
([quarteroni2000numerical], §11.5). -/
noncomputable def errorConstant (q : ℕ) : ℝ := M.taylorCoeff (q + 1) / (q + 1).factorial


/-! ### The Taylor expansion of $\mathcal{L}$ -/

section Expansion

variable {y : ℕ → ℝ → E} {a b K h t : ℝ} {q : ℕ}

/-- The constant of the remainder of the Taylor expansion of $\mathcal{L}[w; h](t)$ to order $q$:
$$R_q = \frac{1 + \sum_{j=0}^p |a_j| j^{q+1}}{(q + 1)!} + \frac{|b_{-1}| + \sum_{j=0}^p |b_j|
  j^q}{q!}.$$
-/
noncomputable def remainderConst (q : ℕ) : ℝ :=
  (1 + ∑ j : Fin (M.p + 1), |M.a j| * (j : ℝ) ^ (q + 1)) / (q + 1).factorial +
    (|M.bm1| + ∑ j : Fin (M.p + 1), |M.b j| * (j : ℝ) ^ q) / q.factorial

/-- The remainder constant $R_q$ is nonnegative. -/
theorem remainderConst_nonneg (q : ℕ) : 0 ≤ M.remainderConst q := by
  unfold remainderConst
  positivity

/-- The algebraic identity behind the Taylor expansion of $\mathcal{L}$. Suppose that for every $s$
$$w(t + s) = \sum_{m=0}^q \frac{s^m}{m!} Y_m + S(s), \qquad
  w'(t + s) = \sum_{m=0}^{q-1} \frac{s^m}{m!} Y_{m+1} + S'(s),$$
where $w'$ is `deriv w`, and $S$ and $S'$ are arbitrary functions. Then
$$\mathcal{L}[w; h](t) = \sum_{m=0}^q \frac{h^m}{m!} c_m Y_m + S(h) - \sum_{j=0}^p a_j S(-jh) -
  h \Bigl( b_{-1} S'(h) + \sum_{j=0}^p b_j S'(-jh) \Bigr).$$
-/
theorem opL_eq_sum_add {w S S' : ℝ → E} {Y : ℕ → E}
    (hw : ∀ s, w (t + s) = (∑ m ∈ range (q + 1), (s ^ m / m.factorial) • Y m) + S s)
    (hw' : ∀ s, deriv w (t + s) = (∑ m ∈ range q, (s ^ m / m.factorial) • Y (m + 1)) + S' s) :
    M.opL h w t = (∑ m ∈ range (q + 1), (h ^ m / m.factorial * M.taylorCoeff m) • Y m) +
      (S h - ∑ j : Fin (M.p + 1), M.a j • S (-(j * h)) -
        h • (M.bm1 • S' h + ∑ j : Fin (M.p + 1), M.b j • S' (-(j * h)))) := by
  have hsub : ∀ j : Fin (M.p + 1), t - j * h = t + -(j * h) := fun j => by ring
  simp only [opL, hsub, hw, hw']
  -- the three families of main terms
  have e2 : ∑ j : Fin (M.p + 1), M.a j • ∑ m ∈ range (q + 1), ((-(j * h)) ^ m / m.factorial) • Y m
      = ∑ m ∈ range (q + 1),
        (h ^ m / m.factorial * ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ m * M.a j) • Y m := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring
  have e3 : ∑ j : Fin (M.p + 1), M.b j • ∑ m ∈ range q, ((-(j * h)) ^ m / m.factorial) • Y (m + 1)
      = ∑ m ∈ range q,
        (h ^ m / m.factorial * ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ m * M.b j) • Y (m + 1) := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring
  have e4 : ∑ m ∈ range (q + 1), (h ^ m / m.factorial * M.taylorCoeff m) • Y m =
      (∑ m ∈ range (q + 1), (h ^ m / m.factorial) • Y m) -
        (∑ m ∈ range (q + 1),
          (h ^ m / m.factorial * ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ m * M.a j) • Y m) -
        h • (M.bm1 • ∑ m ∈ range q, (h ^ m / m.factorial) • Y (m + 1) +
          ∑ m ∈ range q,
            (h ^ m / m.factorial * ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ m * M.b j) • Y (m + 1)) := by
    have e5 : h • (M.bm1 • ∑ m ∈ range q, (h ^ m / m.factorial) • Y (m + 1) +
        ∑ m ∈ range q,
          (h ^ m / m.factorial * ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ m * M.b j) • Y (m + 1)) =
        ∑ m ∈ range (q + 1), (h ^ m / m.factorial * m *
          (M.bm1 + ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ (m - 1) * M.b j)) • Y m := by
      have hfac : ∀ m : ℕ, h ^ (m + 1) / ((m + 1).factorial : ℝ) * ((m : ℝ) + 1) =
          h * (h ^ m / m.factorial) := fun m => by
        rw [Nat.factorial_succ]; push_cast; field_simp; ring
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, zero_mul, zero_smul, add_zero, smul_add, Finset.smul_sum,
        smul_smul, ← Finset.sum_add_distrib, Nat.add_sub_cancel]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← add_smul]
      congr 1
      push_cast
      rw [hfac]
      ring
    rw [e5, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← sub_smul, ← sub_smul]
    congr 1
    rw [taylorCoeff]
    ring
  simp only [smul_add, Finset.sum_add_distrib]
  rw [e2, e3, e4]
  simp only [smul_add]
  abel

/-- The **Taylor expansion of $\mathcal{L}[w; h](t)$ about $t$** ([quarteroni2000numerical], §11.5).
Let $y_0, y_1, \dots, y_{q+1} \colon \mathbb{R} \to E$ and let $[a, b]$ be an interval that
contains $t - ph$ and $t + h$, with $h > 0$. Suppose that on $[a, b]$ each $y_{m+1}$, $m \le q$,
is the derivative of $y_m$ within $[a, b]$, that $y_0' = y_1$, where $y_0'$ is `deriv` of
$y_0$, and that $\|y_{q+1}\| \le K$. Then
$$\Bigl\| \mathcal{L}[y_0; h](t) - \sum_{m=0}^q \frac{h^m}{m!} c_m y_m(t) \Bigr\|
  \le K R_q h^{q+1},$$
where $R_q$ is `ODE.LinearMultistep.remainderConst`.

Each of $w(t + h)$, $w(t - jh)$, $w'(t + h)$ and $w'(t - jh)$ is expanded about $t$ with the
Taylor bound `norm_sub_sum_smul_le`, and `ODE.LinearMultistep.opL_eq_sum_add` collects the
coefficients. -/
theorem opL_eq_sum_add_remainder
    (hy : ∀ m ≤ q, ∀ s ∈ Icc a b, HasDerivWithinAt (y m) (y (m + 1) s) (Icc a b) s)
    (hd : ∀ s ∈ Icc a b, deriv (y 0) s = y 1 s) (hK : ∀ s ∈ Icc a b, ‖y (q + 1) s‖ ≤ K)
    (hh : 0 < h) (ht : t - M.p * h ∈ Icc a b) (hth : t + h ∈ Icc a b) :
    ‖M.opL h (y 0) t - ∑ m ∈ range (q + 1), (h ^ m / m.factorial * M.taylorCoeff m) • y m t‖ ≤
      K * M.remainderConst q * h ^ (q + 1) := by
  have htmem : t ∈ Icc a b := ⟨by nlinarith [ht.1, hh], by linarith [hth.2]⟩
  have hmem : ∀ j : Fin (M.p + 1), t + -(j * h) ∈ Icc a b := fun j => by
    have hj : (j : ℝ) ≤ M.p := by exact_mod_cast Nat.lt_succ_iff.1 j.2
    constructor
    · nlinarith [ht.1, hh]
    · nlinarith [hth.2, hh, (Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ j)]
  -- the remainders
  set S : ℝ → E := fun s => y 0 (t + s) - ∑ m ∈ range (q + 1), (s ^ m / m.factorial) • y m t
  set S' : ℝ → E := fun s => y 1 (t + s) - ∑ m ∈ range q, (s ^ m / m.factorial) • y (m + 1) t
  have hS : ∀ s, t + s ∈ Icc a b → ‖S s‖ ≤ K * |s| ^ (q + 1) / (q + 1).factorial := by
    intro s hs
    have := norm_sub_sum_smul_le (y := y) (q + 1) (fun m hm => hy m (by omega)) hK htmem hs
    simpa [S] using this
  have hS' : ∀ s, t + s ∈ Icc a b → ‖S' s‖ ≤ K * |s| ^ q / q.factorial := by
    intro s hs
    have := norm_sub_sum_smul_le (y := fun m => y (m + 1)) q
      (fun m hm => hy (m + 1) (by omega)) hK htmem hs
    simpa [S'] using this
  have hw : ∀ s, y 0 (t + s) = (∑ m ∈ range (q + 1), (s ^ m / m.factorial) • y m t) + S s :=
    fun s => by simp [S]
  have hw' : ∀ s, t + s ∈ Icc a b →
      deriv (y 0) (t + s) = (∑ m ∈ range q, (s ^ m / m.factorial) • y (m + 1) t) + S' s :=
    fun s hs => by rw [hd _ hs]; simp [S']
  -- the expansion, with `S'` read only at the points used
  have key := M.opL_eq_sum_add (h := h) (t := t) (q := q) (Y := fun m => y m t) (w := y 0)
    (S := S) (S' := fun s => if t + s ∈ Icc a b then S' s else deriv (y 0) (t + s) -
      ∑ m ∈ range q, (s ^ m / m.factorial) • y (m + 1) t) hw (fun s => by
        split_ifs with hs
        · exact hw' s hs
        · simp)
  rw [key, add_sub_cancel_left]
  simp only [hth, hmem, ite_true]
  -- bound the remainder term by term
  have hh0 : 0 ≤ h := hh.le
  have hj : ∀ j : Fin (M.p + 1), |(-(j * h))| = j * h := fun j => by
    rw [abs_neg, abs_of_nonneg (by positivity)]
  have b1 := hS h hth
  have b2 : ∀ j : Fin (M.p + 1), ‖M.a j • S (-(j * h))‖ ≤
      |M.a j| * (K * ((j : ℝ) * h) ^ (q + 1) / (q + 1).factorial) := fun j => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (by simpa [hj j] using hS _ (hmem j)) (abs_nonneg _)
  have b3 := hS' h hth
  have b4 : ∀ j : Fin (M.p + 1), ‖M.b j • S' (-(j * h))‖ ≤
      |M.b j| * (K * ((j : ℝ) * h) ^ q / q.factorial) := fun j => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (by simpa [hj j] using hS' _ (hmem j)) (abs_nonneg _)
  rw [abs_of_pos hh] at b1 b3
  calc ‖S h - ∑ j : Fin (M.p + 1), M.a j • S (-(j * h)) -
        h • (M.bm1 • S' h + ∑ j : Fin (M.p + 1), M.b j • S' (-(j * h)))‖
      ≤ ‖S h‖ + ∑ j : Fin (M.p + 1), ‖M.a j • S (-(j * h))‖ +
        h * (|M.bm1| * ‖S' h‖ + ∑ j : Fin (M.p + 1), ‖M.b j • S' (-(j * h))‖) := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add_right (norm_sum_le _ _) _)) ?_)
        rw [norm_smul, Real.norm_of_nonneg hh0]
        gcongr
        refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sum_le _ _))
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ K * h ^ (q + 1) / (q + 1).factorial +
        ∑ j : Fin (M.p + 1), |M.a j| * (K * ((j : ℝ) * h) ^ (q + 1) / (q + 1).factorial) +
        h * (|M.bm1| * (K * h ^ q / q.factorial) +
          ∑ j : Fin (M.p + 1), |M.b j| * (K * ((j : ℝ) * h) ^ q / q.factorial)) := by
        gcongr with j _ j _
        · exact b2 j
        · exact b4 j
    _ = K * M.remainderConst q * h ^ (q + 1) := by
        simp only [remainderConst, mul_pow]
        rw [add_div, add_div, Finset.sum_div, Finset.sum_div]
        simp only [mul_add, Finset.mul_sum, add_mul, Finset.sum_mul]
        congr 1
        · congr 1
          · ring
          · refine Finset.sum_congr rfl fun j _ => ?_
            ring
        · congr 1
          · ring
          · refine Finset.sum_congr rfl fun j _ => ?_
            ring

/-- **Order $q$ with an explicit constant**, the sufficiency part of Theorem 11.3 of
[quarteroni2000numerical]. Assume the order conditions $0, \dots, q$. Let $y_0, \dots, y_{q+1}$,
$[a, b]$, $h > 0$ and $K$ be as in `ODE.LinearMultistep.opL_eq_sum_add_remainder`: $[a, b]$
contains $t - ph$ and $t + h$, each $y_{m+1}$ is the derivative of $y_m$ within $[a, b]$,
$y_0' = y_1$, where $y_0'$ is `deriv` of $y_0$, and $\|y_{q+1}\| \le K$ on $[a, b]$. Then the
local truncation error along $y_0$ satisfies
$$\|\tau(h; t)\| \le K R_q h^q.$$
-/
theorem norm_lte_le_of_orderCondition (hq : ∀ i ≤ q, M.orderCondition i)
    (hy : ∀ m ≤ q, ∀ s ∈ Icc a b, HasDerivWithinAt (y m) (y (m + 1) s) (Icc a b) s)
    (hd : ∀ s ∈ Icc a b, deriv (y 0) s = y 1 s) (hK : ∀ s ∈ Icc a b, ‖y (q + 1) s‖ ≤ K)
    (hh : 0 < h) (ht : t - M.p * h ∈ Icc a b) (hth : t + h ∈ Icc a b) :
    ‖M.lte h (y 0) t‖ ≤ K * M.remainderConst q * h ^ q := by
  have key := M.opL_eq_sum_add_remainder hy hd hK hh ht hth
  have hz : ∑ m ∈ range (q + 1), (h ^ m / m.factorial * M.taylorCoeff m) • y m t = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [(M.orderCondition_iff_taylorCoeff_eq_zero m).1 (hq m (Nat.lt_succ_iff.1
      (Finset.mem_range.1 hm))), mul_zero, zero_smul]
  rw [hz, sub_zero] at key
  rw [lte, norm_smul, norm_inv, Real.norm_of_nonneg hh.le]
  calc h⁻¹ * ‖M.opL h (y 0) t‖ ≤ h⁻¹ * (K * M.remainderConst q * h ^ (q + 1)) := by gcongr
    _ = K * M.remainderConst q * h ^ q := by field_simp; ring

/-- If $\|\tau_{n+1}(h)\| \le C h^q$ for every $h > 0$ and every step $p \le n < N_h$, then the
method has order $q$ along $y$ on $[t_0, t_0 + T]$. -/
theorem hasOrderFor_of_forall_norm_lte_le {t₀ T : ℝ} {y : ℝ → E} {C : ℝ}
    (hle : ∀ h > 0, ∀ n, M.p ≤ n → n < gridCount T h →
      ‖M.lte h y (node t₀ h n)‖ ≤ C * h ^ q) : M.HasOrderFor t₀ T y q := by
  refine IsBigO.of_bound (max C 0) (eventually_nhdsWithin_of_forall fun h (hh : 0 < h) => ?_)
  rw [Real.norm_of_nonneg (M.globalLte_nonneg _), Real.norm_of_nonneg (by positivity)]
  refine M.globalLte_le (by positivity) fun n hp hn => (hle h hh n hp hn).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- **Order $q$ along a curve from the order conditions.** Assume the order conditions
$0, \dots, q$. Let $y_0, \dots, y_{q+1}$ be curves such that on $[t_0, t_0 + T]$ each $y_{m+1}$,
$m \le q$, is the derivative of $y_m$ within the interval, $y_0' = y_1$, where $y_0'$ is `deriv`
of $y_0$, and $\|y_{q+1}\| \le K$. Then the method has order $q$ along $y_0$ on
$[t_0, t_0 + T]$. -/
theorem hasOrderFor_of_orderCondition {t₀ T : ℝ} (hq : ∀ i ≤ q, M.orderCondition i)
    (hy : ∀ m ≤ q, ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (y m) (y (m + 1) s) (Icc t₀ (t₀ + T)) s)
    (hd : ∀ s ∈ Icc t₀ (t₀ + T), deriv (y 0) s = y 1 s)
    (hK : ∀ s ∈ Icc t₀ (t₀ + T), ‖y (q + 1) s‖ ≤ K) : M.HasOrderFor t₀ T (y 0) q :=
  M.hasOrderFor_of_forall_norm_lte_le (C := K * M.remainderConst q) fun h hh n hp hn => by
    refine M.norm_lte_le_of_orderCondition hq hy hd hK hh ?_ (node_add_mem_Icc_of_lt hh hn)
    rw [node_sub_mul hp]
    exact node_mem_Icc_of_lt hh (by omega)

end Expansion


/-! ### Consistency from the first two order conditions -/

section Consistency

variable {t₀ T h : ℝ}

/-- The operator $\mathcal{L}$ in terms of first-order Taylor remainders. Assume the order
conditions $0$ and $1$, and let $y'$ be a function that equals `deriv y` at the points $t - jh$,
$j = -1, \dots, p$. Then
$$\mathcal{L}[y; h](t) = R(h) - \sum_{j=0}^p a_j R(-jh) - h \Bigl( b_{-1} R'(h) + \sum_{j=0}^p
  b_j R'(-jh) \Bigr),$$
where $R(s) = y(t + s) - y(t) - s y'(t)$ and $R'(s) = y'(t + s) - y'(t)$. -/
theorem opL_eq_of_orderCondition (h0 : M.orderCondition 0) (h1 : M.orderCondition 1)
    {y y' : ℝ → E} {t : ℝ} (hd : ∀ j : Fin (M.p + 1), deriv y (t - j * h) = y' (t - j * h))
    (hd' : deriv y (t + h) = y' (t + h)) :
    M.opL h y t = (y (t + h) - y t - h • y' t) -
      ∑ j : Fin (M.p + 1), M.a j • (y (t - j * h) - y t - (-(j * h)) • y' t) -
      h • (M.bm1 • (y' (t + h) - y' t) +
        ∑ j : Fin (M.p + 1), M.b j • (y' (t - j * h) - y' t)) := by
  rw [orderCondition_zero] at h0
  rw [orderCondition_one] at h1
  have f1 : ∑ j : Fin (M.p + 1), M.a j • y t = y t := by rw [← Finset.sum_smul, h0, one_smul]
  have f2 : ∑ j : Fin (M.p + 1), M.a j • ((-(j * h)) • y' t) =
      (h * (1 - (M.bm1 + ∑ j, M.b j))) • y' t := by
    simp_rw [smul_smul, ← Finset.sum_smul]
    congr 1
    have : ∑ j : Fin (M.p + 1), (j : ℝ) * M.a j = M.bm1 + ∑ j, M.b j - 1 := by linarith
    rw [Finset.sum_congr rfl fun j _ => show M.a j * -(j * h) = -h * (j * M.a j) by ring,
      ← Finset.mul_sum, this]
    ring
  have f3 : ∑ j : Fin (M.p + 1), M.b j • y' t = (∑ j, M.b j) • y' t := (Finset.sum_smul).symm
  simp only [opL, hd, hd', smul_sub, Finset.sum_sub_distrib, f1, f2, f3]
  module

/-- **Consistency from the two consistency conditions**, the sufficiency part of Theorem 11.3 of
[quarteroni2000numerical] for curves with values in $E$. Assume the order conditions $0$ and
$1$. Let $y \colon \mathbb{R} \to E$ have the derivative $y'(s)$ at every
$s \in [t_0, t_0 + T]$, with $y'$ continuous on $[t_0, t_0 + T]$. Then the method is consistent
along $y$ on $[t_0, t_0 + T]$.

The derivative is two-sided at every point of the closed interval, including the endpoints. -/
theorem isConsistentFor_of_orderCondition (h0 : M.orderCondition 0) (h1 : M.orderCondition 1)
    {y y' : ℝ → E} (hy : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivAt y (y' s) s)
    (hy' : ContinuousOn y' (Icc t₀ (t₀ + T))) : M.IsConsistentFor t₀ T y := by
  rw [IsConsistentFor, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set A : ℝ := 1 + ∑ j : Fin (M.p + 1), |M.a j| * j + |M.bm1| + ∑ j : Fin (M.p + 1), |M.b j|
  have hA1 : 1 ≤ A := by
    have h1' : 0 ≤ ∑ j : Fin (M.p + 1), |M.a j| * j := Finset.sum_nonneg fun j _ => by positivity
    have h2' : 0 ≤ ∑ j : Fin (M.p + 1), |M.b j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have := abs_nonneg M.bm1
    simp only [A]; linarith
  set ε' : ℝ := ε / (2 * A)
  have hε' : 0 < ε' := by positivity
  obtain ⟨η, hη, hη'⟩ :=
    exists_forall_norm_sub_sub_smul_le (fun s hs => (hy s hs).hasDerivWithinAt) hy' hε'
  -- the modulus of continuity of `y'`, once more, for the derivative terms
  obtain ⟨η₂, hη₂, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hy') ε' hε'
  refine ⟨min η η₂ / (M.p + 1), by positivity, fun h (hh : 0 < h) hdist => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hh] at hdist
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (M.globalLte_nonneg _)]
  refine lt_of_le_of_lt (M.globalLte_le (by positivity) fun n hp hn => ?_) (by linarith : ε / 2 < ε)
  set t := node t₀ h n
  have ht : t ∈ Icc t₀ (t₀ + T) := node_mem_Icc_of_lt hh hn
  have hth : t + h ∈ Icc t₀ (t₀ + T) := node_add_mem_Icc_of_lt hh hn
  have hmem : ∀ j : Fin (M.p + 1), t - j * h ∈ Icc t₀ (t₀ + T) := fun j => by
    rw [show t - j * h = node t₀ h (n - j) from node_sub_mul (by omega)]
    exact node_mem_Icc_of_lt hh (by omega)
  have hph : (M.p + 1) * h < min η η₂ := by
    have := (lt_div_iff₀ (by positivity)).1 hdist
    linarith
  have hjh : ∀ j : Fin (M.p + 1), (j : ℝ) * h < min η η₂ := fun j => by
    have hj : (j : ℝ) ≤ M.p := by exact_mod_cast Nat.lt_succ_iff.1 j.2
    nlinarith
  have hh' : h < min η η₂ := by nlinarith [(Nat.cast_nonneg M.p : (0 : ℝ) ≤ M.p)]
  -- the four remainder bounds
  have hd : ∀ j : Fin (M.p + 1), deriv y (t - j * h) = y' (t - j * h) := fun j =>
    (hy _ (hmem j)).deriv
  have hd' : deriv y (t + h) = y' (t + h) := (hy _ hth).deriv
  have r1 : ‖y (t + h) - y t - h • y' t‖ ≤ ε' * h := by
    have := hη' t ht h hth (by rw [abs_of_pos hh]; exact (hh'.trans_le (min_le_left _ _)).le)
    rwa [abs_of_pos hh] at this
  have r2 : ∀ j : Fin (M.p + 1), ‖y (t - j * h) - y t - (-(j * h)) • y' t‖ ≤ ε' * (j * h) :=
    fun j => by
      have hjh0 : (0 : ℝ) ≤ j * h := by positivity
      have := hη' t ht (-(j * h)) (by rw [← sub_eq_add_neg]; exact hmem j)
        (by rw [abs_neg, abs_of_nonneg hjh0]; exact ((hjh j).trans_le (min_le_left _ _)).le)
      rwa [← sub_eq_add_neg, abs_neg, abs_of_nonneg hjh0] at this
  have r3 : ‖y' (t + h) - y' t‖ ≤ ε' := by
    have := hunif _ hth t ht (by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hh]
      exact hh'.trans_le (min_le_right _ _))
    rw [dist_eq_norm] at this
    exact this.le
  have r4 : ∀ j : Fin (M.p + 1), ‖y' (t - j * h) - y' t‖ ≤ ε' := fun j => by
    have := hunif _ (hmem j) t ht (by
      rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity)]
      exact (hjh j).trans_le (min_le_right _ _))
    rw [dist_eq_norm] at this
    exact this.le
  -- assemble
  rw [lte, norm_smul, norm_inv, Real.norm_of_nonneg hh.le, M.opL_eq_of_orderCondition h0 h1 hd hd']
  have hε'A : ε' * A = ε / 2 := by simp only [ε']; field_simp
  calc h⁻¹ * ‖(y (t + h) - y t - h • y' t) -
        ∑ j : Fin (M.p + 1), M.a j • (y (t - j * h) - y t - (-(j * h)) • y' t) -
        h • (M.bm1 • (y' (t + h) - y' t) +
          ∑ j : Fin (M.p + 1), M.b j • (y' (t - j * h) - y' t))‖
      ≤ h⁻¹ * (ε' * h + ∑ j : Fin (M.p + 1), |M.a j| * (ε' * (j * h)) +
          h * (|M.bm1| * ε' + ∑ j : Fin (M.p + 1), |M.b j| * ε')) := by
        gcongr
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add r1 ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)))) ?_)
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (r2 j) (abs_nonneg _)
        · rw [norm_smul, Real.norm_of_nonneg hh.le]
          gcongr
          refine (norm_add_le _ _).trans (add_le_add ?_ ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun j _ => ?_)))
          · rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left r3 (abs_nonneg _)
          · rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (r4 j) (abs_nonneg _)
    _ = ε' * A := by
        have e1 : ∑ j : Fin (M.p + 1), |M.a j| * (ε' * (j * h)) =
            ε' * h * ∑ j : Fin (M.p + 1), |M.a j| * j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        have e2 : ∑ j : Fin (M.p + 1), |M.b j| * ε' = ε' * ∑ j : Fin (M.p + 1), |M.b j| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [e1, e2]
        simp only [A]
        field_simp
        ring
    _ = ε / 2 := hε'A

end Consistency

/-! ### Regularity: globally smooth curves and the monomials -/

section Bridges

variable {t₀ T h : ℝ} {q : ℕ}

/-- **Order $q$ along a globally $C^{q+1}$ curve**, the sufficiency part of Theorem 11.3 of
[quarteroni2000numerical]. Assume the order conditions $0, \dots, q$. If
$y \colon \mathbb{R} \to E$ is $C^{q+1}$, then the method has order $q$ along $y$ on every
horizon $[t_0, t_0 + T]$.

The derivatives are the iterated derivatives of $y$, and $\|y^{(q+1)}\|$ is bounded on the
compact horizon. -/
theorem hasOrderFor_of_contDiff (hq : ∀ i ≤ q, M.orderCondition i) {y : ℝ → E}
    (hy : ContDiff ℝ (q + 1) y) (t₀ T : ℝ) : M.HasOrderFor t₀ T y q := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := t₀) (b := t₀ + T)).exists_bound_of_continuousOn
    (hy.continuous_iteratedDeriv (q + 1) le_rfl).continuousOn
  have hder : ∀ m ≤ q, ∀ s, HasDerivAt (iteratedDeriv m y) (iteratedDeriv (m + 1) y s) s := by
    intro m hm s
    have hdiff : Differentiable ℝ (iteratedDeriv m y) :=
      hy.differentiable_iteratedDeriv m (by exact_mod_cast Nat.lt_succ_of_le hm)
    rw [iteratedDeriv_succ]
    exact (hdiff s).hasDerivAt
  have := M.hasOrderFor_of_orderCondition (y := fun m => iteratedDeriv m y) (t₀ := t₀) (T := T) hq
    (fun m hm s _ => (hder m hm s).hasDerivWithinAt)
    (fun s _ => (hder 0 (Nat.zero_le q) s).deriv) hK
  simpa using this

/-- **Order $q$ from the order conditions**, the sufficiency part of Theorem 11.3 of
[quarteroni2000numerical]: if the order conditions $0, \dots, q$ hold, then the method has order
$q$. -/
theorem hasOrder_of_orderCondition (hq : ∀ i ≤ q, M.orderCondition i) : M.HasOrder q :=
  fun t₀ T _ _ hy => M.hasOrderFor_of_contDiff hq hy t₀ T

/-- The operator $\mathcal{L}$ on the monomials. For $h > 0$, $i \in \mathbb{N}$ and
$t \in \mathbb{R}$,
$$\mathcal{L}[s \mapsto s^i; h](t) = \sum_{m=0}^i \binom{i}{m} t^{i-m} h^m c_m.$$
This is the Taylor expansion of $\mathcal{L}$ with zero remainder. -/
theorem opL_pow (hh : 0 < h) (i : ℕ) (t : ℝ) :
    M.opL h (fun s : ℝ => s ^ i) t =
      ∑ m ∈ range (i + 1), (i.choose m : ℝ) * t ^ (i - m) * h ^ m * M.taylorCoeff m := by
  set Y : ℕ → ℝ → ℝ := fun m => iteratedDeriv m fun s : ℝ => s ^ i with hY
  have hy : ∀ m ≤ i, ∀ s ∈ Icc (t - M.p * h) (t + h),
      HasDerivWithinAt (Y m) (Y (m + 1) s) (Icc (t - M.p * h) (t + h)) s := by
    intro m _ s _
    have hdiff : Differentiable ℝ (iteratedDeriv m fun s : ℝ => s ^ i) :=
      (contDiff_id.pow i).differentiable_iteratedDeriv m (WithTop.coe_lt_top _)
    simp only [Y]
    rw [iteratedDeriv_succ]
    exact (hdiff s).hasDerivAt.hasDerivWithinAt
  have hd : ∀ s ∈ Icc (t - M.p * h) (t + h), deriv (Y 0) s = Y 1 s := fun s _ => by
    simp only [Y, iteratedDeriv_zero, iteratedDeriv_one]
  have hK : ∀ s ∈ Icc (t - M.p * h) (t + h), ‖Y (i + 1) s‖ ≤ 0 := fun s _ => by
    simp [Y, iteratedDeriv_pow]
  have key := M.opL_eq_sum_add_remainder hy hd hK hh
    (left_mem_Icc.2 (by nlinarith [(Nat.cast_nonneg M.p : (0 : ℝ) ≤ M.p)]))
    (right_mem_Icc.2 (by nlinarith [(Nat.cast_nonneg M.p : (0 : ℝ) ≤ M.p)]))
  rw [zero_mul, zero_mul, norm_le_zero_iff, sub_eq_zero] at key
  simp only [Y, iteratedDeriv_zero] at key
  rw [key]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedDeriv_pow, smul_eq_mul, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

/-- The truncation error of a monomial at the first step. Let $h > 0$ and suppose that $c_m = 0$ for
$m < i$. Then the local truncation error of $s \mapsto s^i$ at the node $t_p = ph$ of the grid
from $t_0 = 0$ is
$$\tau = h^{-1} h^i c_i.$$
-/
theorem lte_pow_node (hh : 0 < h) {i : ℕ} (hlow : ∀ m < i, M.taylorCoeff m = 0) :
    M.lte h (fun s : ℝ => s ^ i) (node 0 h M.p) = h⁻¹ * h ^ i * M.taylorCoeff i := by
  rw [lte, M.opL_pow hh, smul_eq_mul, Finset.sum_eq_single i (fun m hm hmi => ?_) (by simp)]
  · simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero, mul_assoc]
  · rw [hlow m (lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) hmi), mul_zero]

/-- Let $h > 0$ with $(p + 1) h \le 1$. Then $p < N_h = \lfloor 1 / h \rfloor$, so the method takes
the step $n = p$ on the horizon $[0, 1]$. -/
theorem lt_gridCount_one (hh : 0 < h) (hph : (M.p + 1) * h ≤ 1) : M.p < gridCount 1 h :=
  (le_gridCount_iff zero_le_one hh).2 (by exact_mod_cast hph)

/-- The Taylor coefficients of a method of order $q$ vanish up to $q$. Let $i \le q$, let the method
have order $q$, and let $c_m = 0$ for $m < i$. Then $c_i = 0$.

The truncation error of $s \mapsto s^i$ at the first step is $h^{i-1} c_i$, which is $O(h^q)$
only if $c_i = 0$. The proof reads the coefficient off with
`Asymptotics.eq_zero_of_isBigO_pow_succ`. -/
theorem taylorCoeff_eq_zero_of_hasOrder {i : ℕ} (hiq : i ≤ q) (hq : M.HasOrder q)
    (hlow : ∀ m < i, M.taylorCoeff m = 0) : M.taylorCoeff i = 0 := by
  have hbig := hq 0 1 one_pos (fun s => s ^ i) (contDiff_id.pow i)
  have hlow' : (fun h : ℝ => h⁻¹ * h ^ i * M.taylorCoeff i) =O[𝓝[>] 0] fun h => h ^ q := by
    refine (IsBigO.of_bound 1 ?_).trans hbig
    filter_upwards [Ioc_mem_nhdsGT (by positivity : (0 : ℝ) < 1 / (M.p + 1))] with h hh
    rw [one_mul, Real.norm_of_nonneg (M.globalLte_nonneg _), ← M.lte_pow_node hh.1 hlow]
    refine M.norm_lte_le_globalLte le_rfl (M.lt_gridCount_one hh.1 ?_)
    have := (le_div_iff₀ (by positivity)).1 hh.2
    linarith
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · -- `τ = C_0 / h`
    refine eq_zero_of_isBigO_pow_succ (m := 0) ?_
    obtain ⟨C, hC0, hC⟩ := hlow'.exists_pos
    refine IsBigO.of_bound C ?_
    filter_upwards [hC.bound, Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with h hh (hh1 : h ∈ Ioc 0 1)
    rw [pow_zero, mul_one, Real.norm_eq_abs, Real.norm_of_nonneg (pow_nonneg hh1.1.le _),
      abs_mul, abs_inv, abs_of_pos hh1.1, inv_mul_eq_div, div_le_iff₀ hh1.1] at hh
    rw [pow_zero, mul_one, pow_one, Real.norm_eq_abs, Real.norm_of_nonneg hh1.1.le]
    have hq' : h ^ q ≤ 1 := pow_le_one₀ hh1.1.le hh1.2
    calc |M.taylorCoeff 0| ≤ C * h ^ q * h := hh
      _ ≤ C * 1 * h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq' hC0.le) hh1.1.le
      _ = C * h := by ring
  · refine eq_zero_of_isBigO_pow_succ (m := i - 1) ?_
    have e : (fun h : ℝ => M.taylorCoeff i * h ^ (i - 1)) =ᶠ[𝓝[>] 0]
        fun h => h⁻¹ * h ^ i * M.taylorCoeff i := by
      filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      field_simp
      ring
    rw [show i - 1 + 1 = i by omega]
    exact (e.trans_isBigO hlow').trans ((isBigO_pow_pow hiq).mono nhdsWithin_le_nhds)

end Bridges

/-! ### Theorem 11.3 -/

section Theorem113

/-- **Consistency is the two conditions (11.52)**, the first part of Theorem 11.3 of
[quarteroni2000numerical]: the method is consistent if and only if
$$\sum_{j=0}^p a_j = 1 \quad \text{and} \quad -\sum_{j=0}^p j a_j + \sum_{j=-1}^p b_j = 1.$$
-/
theorem isConsistent_iff : M.IsConsistent ↔ M.orderCondition 0 ∧ M.orderCondition 1 := by
  constructor
  · intro hc
    -- the test curves `1` and `t`, on `[0, 1]`
    have key : ∀ i, (∀ m < i, M.taylorCoeff m = 0) →
        (∀ᶠ h in 𝓝[>] (0 : ℝ), |M.taylorCoeff i| * (h⁻¹ * h ^ i) ≤
          M.globalLte 0 1 (fun s : ℝ => s ^ i) h) := by
      intro i hlow
      filter_upwards [Ioc_mem_nhdsGT (by positivity : (0 : ℝ) < 1 / (M.p + 1))] with h hh
      have hh0 : 0 < h := hh.1
      rw [← Real.norm_eq_abs, ← Real.norm_of_nonneg (by positivity : 0 ≤ h⁻¹ * h ^ i), ← norm_mul,
        mul_comm, ← M.lte_pow_node hh0 hlow]
      refine M.norm_lte_le_globalLte le_rfl (M.lt_gridCount_one hh0 ?_)
      have := (le_div_iff₀ (by positivity)).1 hh.2
      linarith
    have hlim : ∀ i, Tendsto (M.globalLte 0 1 fun s : ℝ => s ^ i) (𝓝[>] 0) (𝓝 0) :=
      fun i => hc 0 1 one_pos _ (contDiff_id.pow i)
    have h0 : M.taylorCoeff 0 = 0 := by
      have : |M.taylorCoeff 0| ≤ 0 := ge_of_tendsto (hlim 0) (by
        filter_upwards [key 0 (fun m hm => absurd hm (Nat.not_lt_zero m)),
          Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with h hh (hh1 : h ∈ Ioc 0 1)
        refine le_trans ?_ hh
        rw [pow_zero, mul_one]
        exact le_mul_of_one_le_right (abs_nonneg _) (one_le_inv_iff₀.2 ⟨hh1.1, hh1.2⟩))
      exact abs_nonpos_iff.1 this
    have h1 : M.taylorCoeff 1 = 0 := by
      have : |M.taylorCoeff 1| ≤ 0 := ge_of_tendsto (hlim 1) (by
        filter_upwards [key 1 (fun m hm => by rw [Nat.lt_one_iff.1 hm]; exact h0),
          self_mem_nhdsWithin] with h hh (hh1 : 0 < h)
        rwa [pow_one, inv_mul_cancel₀ hh1.ne', mul_one] at hh)
      exact abs_nonpos_iff.1 this
    exact ⟨(M.orderCondition_iff_taylorCoeff_eq_zero 0).2 h0,
      (M.orderCondition_iff_taylorCoeff_eq_zero 1).2 h1⟩
  · rintro ⟨h0, h1⟩ t₀ T _ y hy
    exact M.isConsistentFor_of_orderCondition h0 h1
      (fun s _ => ((hy.differentiable one_ne_zero) s).hasDerivAt)
      (hy.continuous_deriv le_rfl).continuousOn

/-- **Order $q$ is the order conditions $0, \dots, q$**, the second part of Theorem 11.3 of
[quarteroni2000numerical]: for every $q \in \mathbb{N}$, the method has order $q$ if and only if
$$\sum_{j=0}^p (-j)^i a_j + i \sum_{j=-1}^p (-j)^{i-1} b_j = 1 \qquad (0 \le i \le q).$$

The source states the theorem for $q \ge 1$. It also holds for $q = 0$, where it says that
$\tau(h)$ is bounded along every $C^1$ curve if and only if $\sum_j a_j = 1$. -/
theorem hasOrder_iff {q : ℕ} : M.HasOrder q ↔ ∀ i ≤ q, M.orderCondition i := by
  refine ⟨fun H i hi => ?_, M.hasOrder_of_orderCondition⟩
  rw [orderCondition_iff_taylorCoeff_eq_zero]
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    exact M.taylorCoeff_eq_zero_of_hasOrder hi H fun m hm => ih m hm (by omega)

/-- A method of order $q \ge 1$ is consistent. -/
theorem HasOrder.isConsistent {q : ℕ} (hq : 1 ≤ q) (H : M.HasOrder q) : M.IsConsistent := by
  rw [isConsistent_iff]
  rw [M.hasOrder_iff] at H
  exact ⟨H 0 (Nat.zero_le _), H 1 hq⟩

end Theorem113


/-! ### The characteristic polynomials -/

section CharPoly

/-- The **first characteristic polynomial** of the method ([quarteroni2000numerical], §11.6.2):
$$\rho(r) = r^{p+1} - \sum_{j=0}^p a_j r^{p-j} \in \mathbb{R}[r].$$
-/
noncomputable def rho : ℝ[X] :=
  X ^ (M.p + 1) - ∑ j : Fin (M.p + 1), C (M.a j) * X ^ (M.p - j)

/-- The **second characteristic polynomial** of the method ([quarteroni2000numerical], §11.6.2):
$$\sigma(r) = b_{-1} r^{p+1} + \sum_{j=0}^p b_j r^{p-j} \in \mathbb{R}[r].$$
-/
noncomputable def sigma : ℝ[X] :=
  C M.bm1 * X ^ (M.p + 1) + ∑ j : Fin (M.p + 1), C (M.b j) * X ^ (M.p - j)

/-- The **characteristic polynomial of the method on the test equation**, (11.55) of
[quarteroni2000numerical]: for $z \in \mathbb{C}$,
$$\Pi_z(r) = \rho(r) - z \sigma(r) \in \mathbb{C}[r],$$
with $\rho$ and $\sigma$ read in $\mathbb{C}[r]$. On $y' = \lambda y$ with step $h$ the relevant
value is $z = h\lambda$. -/
noncomputable def charPoly (z : ℂ) : ℂ[X] :=
  M.rho.map (algebraMap ℝ ℂ) - C z * M.sigma.map (algebraMap ℝ ℂ)

/-- At $z = 0$ the characteristic polynomial $\Pi_0$ is $\rho$, read in $\mathbb{C}[r]$. -/
theorem charPoly_zero : M.charPoly 0 = M.rho.map (algebraMap ℝ ℂ) := by
  simp [charPoly]

/-- The value of $\rho$ at a real $r$ is $r^{p+1} - \sum_j a_j r^{p-j}$. -/
theorem eval_rho (r : ℝ) :
    M.rho.eval r = r ^ (M.p + 1) - ∑ j : Fin (M.p + 1), M.a j * r ^ (M.p - j) := by
  simp [rho, eval_finsetSum]

/-- The value of $\sigma$ at a real $r$ is $b_{-1} r^{p+1} + \sum_j b_j r^{p-j}$. -/
theorem eval_sigma (r : ℝ) :
    M.sigma.eval r = M.bm1 * r ^ (M.p + 1) + ∑ j : Fin (M.p + 1), M.b j * r ^ (M.p - j) := by
  simp [sigma, eval_finsetSum]

/-- The polynomial $\sum_{j=0}^p a_j r^{p-j}$ has degree less than $p + 1$. -/
theorem degree_sum_lt :
    (∑ j : Fin (M.p + 1), C (M.a j) * X ^ (M.p - j)).degree < ((M.p + 1 : ℕ) : WithBot ℕ) := by
  refine (degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro j _
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact_mod_cast Nat.lt_succ_of_le (Nat.sub_le _ _)

/-- The polynomial $\rho$ is monic. -/
theorem rho_monic : M.rho.Monic := monic_X_pow_sub M.degree_sum_lt

/-- The polynomial $\rho$ has degree $p + 1$. -/
theorem degree_rho : M.rho.degree = ((M.p + 1 : ℕ) : WithBot ℕ) := by
  rw [rho, degree_sub_eq_left_of_degree_lt, degree_X_pow]
  rw [degree_X_pow]
  exact M.degree_sum_lt

/-- The polynomial $\rho$ has natural degree $p + 1$. -/
theorem natDegree_rho : M.rho.natDegree = M.p + 1 := natDegree_eq_of_degree_eq_some M.degree_rho

/-- The **consistency root** ([quarteroni2000numerical], §11.6.2): if the order condition $0$ holds,
then $\rho(1) = 1 - \sum_j a_j = 0$. -/
theorem rho_isRoot_one (h : M.orderCondition 0) : M.rho.IsRoot 1 := by
  rw [orderCondition_zero] at h
  simp [IsRoot, eval_rho, h]

/-- The derivative of $\rho$ at $1$ is $\rho'(1) = (p + 1) - \sum_{j=0}^p (p - j) a_j$. -/
theorem derivative_rho_eval_one :
    (derivative M.rho).eval 1 = (M.p + 1) - ∑ j : Fin (M.p + 1), ((M.p : ℝ) - j) * M.a j := by
  simp only [rho, derivative_sub, derivative_X_pow, derivative_sum, derivative_C_mul_X_pow,
    eval_sub, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one, eval_finsetSum]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.cast_sub (Nat.lt_succ_iff.1 j.2)]
  ring

/-- The **classical form of consistency**: if the order conditions $0$ and $1$ hold, then
$\rho'(1) = \sigma(1)$, that is,
$$(p + 1) - \sum_{j=0}^p (p - j) a_j = b_{-1} + \sum_{j=0}^p b_j.$$
-/
theorem derivative_rho_eval_one_eq_sigma (h0 : M.orderCondition 0) (h1 : M.orderCondition 1) :
    (derivative M.rho).eval 1 = M.sigma.eval 1 := by
  rw [orderCondition_zero] at h0
  rw [orderCondition_one] at h1
  rw [derivative_rho_eval_one, eval_sigma]
  simp only [one_pow, mul_one, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, h0]
  linarith

/-- The **root condition** for the method, Definition 11.10 and (11.56) of
[quarteroni2000numerical]: every complex root of $\rho$ lies in the closed unit disc, and every
root of modulus $1$ is simple.

This is `Polynomial.SatisfiesRootCondition` for $\rho$ read in $\mathbb{C}[X]$. -/
def SatisfiesRootCondition : Prop := (M.rho.map (algebraMap ℝ ℂ)).SatisfiesRootCondition

/-- The **strong root condition**, Definition 11.11 and (11.57) of [quarteroni2000numerical]: $\rho$
satisfies the root condition, and every complex root of $\rho$ other than $1$ has modulus less
than $1$.

This is `Polynomial.SatisfiesStrongRootCondition` for $\rho$ read in $\mathbb{C}[X]$. -/
def SatisfiesStrongRootCondition : Prop :=
  (M.rho.map (algebraMap ℝ ℂ)).SatisfiesStrongRootCondition

/-- The strong root condition implies the root condition. -/
theorem SatisfiesStrongRootCondition.satisfiesRootCondition
    (h : M.SatisfiesStrongRootCondition) : M.SatisfiesRootCondition :=
  h.1

end CharPoly

/-! ### The method as a linear recurrence -/

section Recurrence

/-- Reindexing by $j = p - i$: for $g \colon \{0, \dots, p\} \to \mathbb{R}$ and a sequence $w$ in
$E$,
$$\sum_{i=0}^p g_{p-i} w_{n+i} = \sum_{j=0}^p g_j w_{n+p-j}.$$
-/
theorem sum_rev_smul (g : Fin (M.p + 1) → ℝ) (w : ℕ → E) (n : ℕ) :
    ∑ i : Fin (M.p + 1), g (Fin.rev i) • w (n + i) =
      ∑ j : Fin (M.p + 1), g j • w (n + M.p - j) := by
  rw [← Equiv.sum_comp Fin.revPerm (fun j => g j • w (n + M.p - j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply]
  congr 2
  have := Fin.val_rev i
  have := i.is_lt
  omega

/-- The **real linear recurrence of the method**, the scheme (11.46) of [quarteroni2000numerical]
for the zero field: the recurrence of order $p + 1$
$$u_{n+p+1} = \sum_{i=0}^p a_{p-i} u_{n+i}.$$
Its characteristic polynomial is $\rho$ (`ODE.LinearMultistep.charPoly_toLinearRecurrenceZero`).

The coefficients $\alpha_i = a_{p-i}$ follow the convention of Mathlib's `LinearRecurrence`,
$u_{n+k} = \sum_{i<k} \alpha_i u_{n+i}$. -/
def toLinearRecurrenceZero : LinearRecurrence ℝ := ⟨M.p + 1, fun i => M.a (Fin.rev i)⟩

/-- The real recurrence of the method has order $p + 1$. -/
@[simp] theorem toLinearRecurrenceZero_order : M.toLinearRecurrenceZero.order = M.p + 1 := rfl

/-- The characteristic polynomial of the real recurrence
`ODE.LinearMultistep.toLinearRecurrenceZero` is the first characteristic polynomial $\rho$. -/
theorem charPoly_toLinearRecurrenceZero : M.toLinearRecurrenceZero.charPoly = M.rho := by
  simp only [LinearRecurrence.charPoly, toLinearRecurrenceZero, rho, ← C_mul_X_pow_eq_monomial,
    C_1, one_mul]
  congr 1
  rw [← Equiv.sum_comp Fin.revPerm (fun j => C (M.a j) * X ^ (M.p - j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply]
  congr 2
  have := Fin.val_rev i
  have := i.is_lt
  omega

/-- The sum $\sum_i \alpha_i w_{n+i}$ of the real recurrence equals the sum $\sum_j a_j w_{n+p-j}$
of the method, for a sequence $w$ in $E$. -/
theorem sum_coeffs_smul (w : ℕ → E) (n : ℕ) :
    ∑ i : Fin M.toLinearRecurrenceZero.order, M.toLinearRecurrenceZero.coeffs i • w (n + i) =
      ∑ j : Fin (M.p + 1), M.a j • w (n + M.p - j) :=
  M.sum_rev_smul M.a w n

/-- For the zero field $f = 0$, a real sequence is an orbit of the method if and only if it is a
solution of the real recurrence `ODE.LinearMultistep.toLinearRecurrenceZero`. This holds for
every step $h$ and every initial time $t_0$. -/
theorem isOrbit_zero_iff_isSolution {h t₀ : ℝ} {u : ℕ → ℝ} :
    M.IsOrbit (fun _ _ => (0 : ℝ)) h t₀ u ↔ M.toLinearRecurrenceZero.IsSolution u := by
  simp only [isOrbit_iff, smul_zero, Finset.sum_const_zero, add_zero]
  refine forall_congr' fun n => ?_
  rw [show u (n + M.toLinearRecurrenceZero.order) =
      ∑ i, M.toLinearRecurrenceZero.coeffs i * u (n + i) ↔
      u (n + M.toLinearRecurrenceZero.order) =
      ∑ i, M.toLinearRecurrenceZero.coeffs i • u (n + i) from Iff.rfl, sum_coeffs_smul,
    toLinearRecurrenceZero_order, ← add_assoc]

end Recurrence

/-! ### Zero-stability: the estimate (11.65) -/

section ZeroStability

/-- Each coefficient satisfies $|b_j| \le \beta$, where $\beta = |b_{-1}| + \sum_{j=0}^p |b_j|$. -/
theorem abs_b_le (j : Fin (M.p + 1)) : |M.b j| ≤ |M.bm1| + ∑ j, |M.b j| :=
  le_add_of_nonneg_of_le (abs_nonneg _)
    (Finset.single_le_sum (f := fun j => |M.b j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))

/-- The coefficient $b_{-1}$ satisfies $|b_{-1}| \le \beta = |b_{-1}| + \sum_{j=0}^p |b_j|$. -/
theorem abs_bm1_le : |M.bm1| ≤ |M.bm1| + ∑ j, |M.b j| :=
  le_add_of_le_of_nonneg le_rfl (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- The **zero-stability estimate**, (11.65) of [quarteroni2000numerical], which is the core of
Theorem 11.4. Let the method satisfy the root condition, let $T \ge 0$, and let $f(t, \cdot)$ be
$L$-Lipschitz for every $t \in [t_0, t_0 + T]$. Then there are $h_0 > 0$ and $K > 0$ with the
following property. Let $h \in (0, h_0]$, $N_h = \lfloor T / h \rfloor$, and
$\varepsilon_0, \varepsilon_1 \ge 0$. Let $u$ and $z$ be sequences in $E$ such that, for every
step with $n + p + 1 \le N_h$, $u$ satisfies the scheme and $z$ satisfies the scheme with the
added perturbation $h \delta_{n+p+1}$. If $\|z_k - u_k\| \le \varepsilon_0$ for $k \le p$ and
$\|\delta_k\| \le \varepsilon_1$ for $p + 1 \le k \le N_h$, then
$$\|z_n - u_n\| \le K (\varepsilon_0 + T \varepsilon_1) \qquad (n \le N_h).$$

The proof takes $h_0 = 1 / (Q + 1)$ and $K = 2 M_0 e^{TQ}$, where $Q = 2 M_0 \beta L (p + 2)$,
$\beta = |b_{-1}| + \sum_j |b_j|$, and $M_0$ is the constant of Lemma 11.3 of
[quarteroni2000numerical] for the recurrence `ODE.LinearMultistep.toLinearRecurrenceZero`. The
difference $w = z - u$ solves that recurrence with a source bounded by $h (\beta L (\|w_l\| +
\sum_j \|w_{l-1-j}\|) + \|\delta_l\|)$. Lemma 11.3
(`LinearRecurrence.norm_le_of_satisfiesRootCondition_smul_of_le`), the bound $1 - hQ/2 \ge 1/2$
that isolates $\|w_n\|$, and the discrete Gronwall lemma `Gronwall.discrete_sum_const_of_le`
finish the proof. -/
theorem norm_sub_le_of_satisfiesRootCondition (hroot : M.SatisfiesRootCondition) (hT : 0 ≤ T)
    {L : NNReal} (hf : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t)) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ K : ℝ, 0 < K ∧ ∀ h ∈ Ioc 0 h₀, ∀ {ε₀ ε₁ : ℝ}, 0 ≤ ε₀ → 0 ≤ ε₁ →
      ∀ {δ u z : ℕ → E},
      (∀ n, n + M.p + 1 ≤ gridCount T h → u (n + M.p + 1) = M.rhs f h t₀ u n) →
      (∀ n, n + M.p + 1 ≤ gridCount T h →
        z (n + M.p + 1) = M.rhs f h t₀ z n + h • δ (n + M.p + 1)) →
      (∀ k ≤ M.p, ‖z k - u k‖ ≤ ε₀) → (∀ k, M.p + 1 ≤ k → k ≤ gridCount T h → ‖δ k‖ ≤ ε₁) →
      ∀ n ≤ gridCount T h, ‖z n - u n‖ ≤ K * (ε₀ + T * ε₁) := by
  have hE : (M.toLinearRecurrenceZero.map (algebraMap ℝ ℂ)).charPoly.SatisfiesRootCondition := by
    rwa [LinearRecurrence.charPoly_map, charPoly_toLinearRecurrenceZero]
  obtain ⟨M₀, hM₀, hM⟩ := M.toLinearRecurrenceZero.norm_le_of_satisfiesRootCondition_smul_of_le
    (Nat.succ_pos _) hE (V := E)
  set β : ℝ := |M.bm1| + ∑ j, |M.b j| with hβ
  set c₁ : ℝ := β * L * (M.p + 2) with hc₁
  set c : ℝ := M₀ * c₁ with hc
  set Q : ℝ := 2 * c with hQ
  refine ⟨1 / (Q + 1), by positivity, 2 * M₀ * Real.exp (T * Q), by positivity,
    fun h hh ε₀ ε₁ hε₀ hε₁ δ u z hu hz h0 hδ => ?_⟩
  have hh0 : 0 < h := hh.1
  have hhc : h * c ≤ 1 / 2 := by
    have := (le_div_iff₀ (by positivity)).1 hh.2
    rw [hQ] at this
    nlinarith
  set N := gridCount T h with hN
  set w : ℕ → E := fun n => z n - u n with hw
  set Δf : ℕ → E := fun l => f (node t₀ h l) (z l) - f (node t₀ h l) (u l) with hΔf
  set φ : ℕ → E := fun l =>
    h • (∑ j : Fin (M.p + 1), M.b j • Δf (l - 1 - j) + M.bm1 • Δf l + δ l) with hφ
  -- `w` solves the recurrence with source `φ` on the horizon
  have hrec : ∀ n, n + M.toLinearRecurrenceZero.order ≤ N →
      w (n + M.toLinearRecurrenceZero.order) =
        ∑ i, M.toLinearRecurrenceZero.coeffs i • w (n + i) +
          φ (n + M.toLinearRecurrenceZero.order) := by
    intro n hn
    have hn' : n + M.p + 1 ≤ N := by rw [toLinearRecurrenceZero_order] at hn; omega
    rw [sum_coeffs_smul, toLinearRecurrenceZero_order, ← add_assoc]
    simp only [hw, hφ, hΔf]
    conv_lhs => rw [hz n hn', hu n hn']
    simp only [rhs]
    have e : ∀ j : Fin (M.p + 1), n + M.p + 1 - 1 - j = n + M.p - j := fun j => by omega
    simp only [e, smul_sub, smul_add, Finset.sum_sub_distrib]
    module
  -- the source is controlled by the Lipschitz constant
  set S : ℕ → ℝ := fun l => ‖w l‖ + ∑ j : Fin (M.p + 1), ‖w (l - 1 - j)‖ with hS
  have hφle : ∀ l, M.p + 1 ≤ l → l ≤ N → ‖φ l‖ ≤ h * (β * L * S l + ε₁) := by
    intro l hl1 hl2
    have hΔ : ∀ m ≤ N, ‖Δf m‖ ≤ L * ‖w m‖ := fun m hm =>
      (hf _ (node_mem_Icc hT hh0 hm)).norm_sub_le _ _
    simp only [hφ]
    rw [norm_smul, Real.norm_of_nonneg hh0.le]
    gcongr
    calc ‖∑ j : Fin (M.p + 1), M.b j • Δf (l - 1 - j) + M.bm1 • Δf l + δ l‖
        ≤ ∑ j : Fin (M.p + 1), |M.b j| * (L * ‖w (l - 1 - j)‖) + |M.bm1| * (L * ‖w l‖) + ε₁ := by
          refine norm_add₃_le.trans (add_le_add (add_le_add ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun j _ => ?_)) ?_) (hδ l hl1 hl2))
          · rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hΔ _ (by omega)) (abs_nonneg _)
          · rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hΔ _ hl2) (abs_nonneg _)
      _ ≤ ∑ j : Fin (M.p + 1), β * (L * ‖w (l - 1 - j)‖) + β * (L * ‖w l‖) + ε₁ := by
          gcongr with j _
          · exact M.abs_b_le j
          · exact M.abs_bm1_le
      _ = β * L * S l + ε₁ := by
          simp only [hS, ← Finset.mul_sum]
          ring
  -- summing the source bound over the horizon
  have hsum : ∀ n ≤ N, ∑ l ∈ Finset.Icc (M.p + 1) n, ‖φ l‖ ≤
      h * c₁ * ∑ m ∈ range (n + 1), ‖w m‖ + T * ε₁ := by
    intro n hn
    have hsub : ∀ l ∈ Finset.Icc (M.p + 1) n, ‖φ l‖ ≤ h * (β * L * S l + ε₁) := fun l hl =>
      hφle l (Finset.mem_Icc.1 hl).1 ((Finset.mem_Icc.1 hl).2.trans hn)
    refine (Finset.sum_le_sum hsub).trans ?_
    have hcard : ((Finset.Icc (M.p + 1) n).card : ℝ) * h ≤ T := by
      rw [Nat.card_Icc]
      have h1 : ((n + 1 - (M.p + 1) : ℕ) : ℝ) ≤ n := by
        exact_mod_cast Nat.sub_le_of_le_add (by omega)
      exact (mul_le_mul_of_nonneg_right h1 hh0.le).trans (mul_le_of_le_gridCount hT hh0 hn)
    -- each history value appears at most `p + 2` times
    have hw0 : ∀ m, 0 ≤ ‖w m‖ := fun m => norm_nonneg _
    have hS1 : ∑ l ∈ Finset.Icc (M.p + 1) n, ‖w l‖ ≤ ∑ m ∈ range (n + 1), ‖w m‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun l hl => Finset.mem_range.2
        (by have := (Finset.mem_Icc.1 hl).2; omega)) fun m _ _ => hw0 m
    have hS2 : ∀ j : Fin (M.p + 1), ∑ l ∈ Finset.Icc (M.p + 1) n, ‖w (l - 1 - j)‖ ≤
        ∑ m ∈ range (n + 1), ‖w m‖ := fun j => by
      refine Finset.sum_le_sum_of_injOn (fun l => l - 1 - j) (fun l hl l' hl' hll' => ?_)
        (fun m hm => ?_) (fun l _ => le_rfl) (fun m _ _ => hw0 m)
      · have := (Finset.mem_Icc.1 hl).1
        have := (Finset.mem_Icc.1 hl').1
        have := j.is_lt
        simp only at hll'
        omega
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hm
        exact Finset.mem_range.2 (by have := (Finset.mem_Icc.1 hl).2; omega)
    have hSsum : ∑ l ∈ Finset.Icc (M.p + 1) n, S l ≤ (M.p + 2) * ∑ m ∈ range (n + 1), ‖w m‖ := by
      simp only [hS]
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      calc ∑ l ∈ Finset.Icc (M.p + 1) n, ‖w l‖ +
            ∑ j : Fin (M.p + 1), ∑ l ∈ Finset.Icc (M.p + 1) n, ‖w (l - 1 - j)‖
          ≤ ∑ m ∈ range (n + 1), ‖w m‖ +
            ∑ j : Fin (M.p + 1), ∑ m ∈ range (n + 1), ‖w m‖ :=
            add_le_add hS1 (Finset.sum_le_sum fun j _ => hS2 j)
        _ = (M.p + 2) * ∑ m ∈ range (n + 1), ‖w m‖ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    calc ∑ l ∈ Finset.Icc (M.p + 1) n, h * (β * L * S l + ε₁)
        = ∑ l ∈ Finset.Icc (M.p + 1) n, (h * (β * L) * S l + h * ε₁) :=
          Finset.sum_congr rfl fun l _ => by ring
      _ = h * (β * L) * ∑ l ∈ Finset.Icc (M.p + 1) n, S l +
          ((Finset.Icc (M.p + 1) n).card : ℝ) * h * ε₁ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ h * (β * L) * ((M.p + 2) * ∑ m ∈ range (n + 1), ‖w m‖) + T * ε₁ := by
          gcongr
      _ = h * c₁ * ∑ m ∈ range (n + 1), ‖w m‖ + T * ε₁ := by rw [hc₁]; ring
  -- Lemma 11.3 and the isolation of `‖w n‖`
  have hgron : ∀ n ≤ N, ‖w n‖ ≤ 2 * M₀ * (ε₀ + T * ε₁) + n * h * 0 +
      h * Q * ∑ m ∈ range n, ‖w m‖ := by
    intro n hn
    have h1 : ‖w n‖ ≤ M₀ * ((⨆ j : Fin (M.p + 1), ‖w j‖) + ∑ l ∈ Finset.Icc (M.p + 1) n, ‖φ l‖) :=
      hM N φ w hrec n hn
    have hsup : (⨆ j : Fin (M.p + 1), ‖w j‖) ≤ ε₀ :=
      ciSup_le fun j => h0 j (Nat.lt_succ_iff.1 j.2)
    have h2 := hsum n hn
    rw [Finset.sum_range_succ] at h2
    have h3 : ‖w n‖ ≤ M₀ * (ε₀ + T * ε₁) + h * c * (∑ m ∈ range n, ‖w m‖ + ‖w n‖) := by
      calc ‖w n‖ ≤ M₀ * ((⨆ j : Fin (M.p + 1), ‖w j‖) +
            ∑ l ∈ Finset.Icc (M.p + 1) n, ‖φ l‖) := h1
        _ ≤ M₀ * (ε₀ + (h * c₁ * (∑ m ∈ range n, ‖w m‖ + ‖w n‖) + T * ε₁)) := by
            gcongr
        _ = M₀ * (ε₀ + T * ε₁) + h * c * (∑ m ∈ range n, ‖w m‖ + ‖w n‖) := by rw [hc]; ring
    have hwn : 0 ≤ ‖w n‖ := norm_nonneg _
    have hprod : h * c * ‖w n‖ ≤ 1 / 2 * ‖w n‖ := mul_le_mul_of_nonneg_right hhc hwn
    rw [hQ]
    nlinarith
  intro n hn
  have key := Gronwall.discrete_sum_const_of_le (by positivity) hh0.le le_rfl (by positivity)
    hgron hn
  simp only [mul_zero, add_zero] at key
  refine key.trans ?_
  have hnh : (n : ℝ) * h ≤ T := mul_le_of_le_gridCount hT hh0 hn
  calc 2 * M₀ * (ε₀ + T * ε₁) * Real.exp (n * h * Q)
      ≤ 2 * M₀ * (ε₀ + T * ε₁) * Real.exp (T * Q) := by
        gcongr
    _ = 2 * M₀ * Real.exp (T * Q) * (ε₀ + T * ε₁) := by ring

end ZeroStability


/-! ### Zero-stability: Theorem 11.4 -/

section Theorem114

variable {L : NNReal}

/-- **Zero-stability** of the method for the field $f$ on the horizon $[t_0, t_0 + T]$, Definition
11.13 and (11.58) of [quarteroni2000numerical]. There are $h_0 > 0$ and $C > 0$ with the
following property. Let $h \in (0, h_0]$, $\varepsilon \ge 0$, and let $\delta$ be a sequence
with $\|\delta_k\| \le \varepsilon$ for $k \le N_h = \lfloor T / h \rfloor$. Let $u$ be an
orbit, and let $z$ be a perturbed orbit with perturbation $\delta$ and starting values
$z_k = u_k + \delta_k$ for $k \le p$. Then
$$\|z_n - u_n\| \le C \varepsilon \qquad (n \le N_h).$$

The starting values $u_0, \dots, u_p$ of the unperturbed orbit are arbitrary. -/
def IsZeroStable (f : ℝ → E → E) (t₀ T : ℝ) : Prop :=
  ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ, 0 < C ∧ ∀ h ∈ Ioc 0 h₀, ∀ ε : ℝ, 0 ≤ ε → ∀ δ : ℕ → E,
    (∀ k ≤ gridCount T h, ‖δ k‖ ≤ ε) → ∀ u z : ℕ → E, M.IsOrbit f h t₀ u →
      M.IsOrbitWith f h t₀ δ z → (∀ k ≤ M.p, z k = u k + δ k) →
        ∀ n ≤ gridCount T h, ‖z n - u n‖ ≤ C * ε

/-- **Theorem 11.4** of [quarteroni2000numerical], sufficiency. Let the method satisfy the root
condition, let $T \ge 0$, and let $f(t, \cdot)$ be $L$-Lipschitz for every
$t \in [t_0, t_0 + T]$. Then the method is zero-stable for $f$ on $[t_0, t_0 + T]$.

The proof specializes `ODE.LinearMultistep.norm_sub_le_of_satisfiesRootCondition`. -/
theorem isZeroStable_of_satisfiesRootCondition (hroot : M.SatisfiesRootCondition) (hT : 0 ≤ T)
    (hf : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t)) : M.IsZeroStable f t₀ T := by
  obtain ⟨h₀, hh₀, K, hK, hest⟩ := M.norm_sub_le_of_satisfiesRootCondition hroot hT hf
  refine ⟨h₀, hh₀, K * (1 + T) + 1, by positivity,
    fun h hh ε hε δ hδ u z hu hz hzu n hn => ?_⟩
  by_cases hpN : M.p ≤ gridCount T h
  · have := hest h hh hε hε (fun n _ => (M.isOrbit_iff_rhs.1 hu) n) (fun n _ => hz n)
      (fun k hk => by rw [hzu k hk, add_sub_cancel_left]; exact hδ k (hk.trans hpN))
      (fun k _ hk => hδ k hk) n hn
    refine this.trans ?_
    nlinarith
  · have hnp : n ≤ M.p := by omega
    rw [hzu n hnp, add_sub_cancel_left]
    refine (hδ n hn).trans (le_mul_of_one_le_left hε ?_)
    nlinarith [mul_nonneg hK.le hT]

/-- An orbit is a perturbed orbit for every perturbation $\delta$ with $\delta_k = 0$ for
$k \ge p + 1$. -/
theorem isOrbitWith_of_isOrbit {δ u : ℕ → E} (hu : M.IsOrbit f h t₀ u)
    (hδ : ∀ k, M.p + 1 ≤ k → δ k = 0) : M.IsOrbitWith f h t₀ δ u := fun n => by
  rw [hδ (n + M.p + 1) (by omega), smul_zero, add_zero]
  exact M.isOrbit_iff_rhs.1 hu n

/-- **Theorem 11.4** of [quarteroni2000numerical], necessity. Let $T > 0$. If the method is
zero-stable for the scalar problem $y' = 0$ on $[t_0, t_0 + T]$, then it satisfies the root
condition.

When the root condition fails, the real recurrence of the method has an unbounded real solution
$v$ (`LinearRecurrence.exists_isSolution_real_not_bddAbove_of_not_satisfiesRootCondition`). The
zero sequence is an orbit of $y' = 0$, and $v$ is a perturbed orbit with the perturbation
$\delta_k = v_k$ for $k \le p$ and $\delta_k = 0$ for $k > p$, which is bounded by
$\varepsilon = \max_{k \le p} |v_k|$. Zero-stability then bounds every $|v_n|$ by
$C \varepsilon$, with $h$ so small that $n \le N_h$. The proof of the source uses the sequences
$\varepsilon r_i^n$ and $\varepsilon (r_i + \bar r_i)^n$ as witnesses, and these do not work;
the proof here does not use them. -/
theorem satisfiesRootCondition_of_isZeroStable (hT : 0 < T)
    (h : M.IsZeroStable (E := ℝ) (fun _ _ => 0) t₀ T) : M.SatisfiesRootCondition := by
  by_contra hroot
  obtain ⟨v, hv, hv'⟩ :=
    M.toLinearRecurrenceZero.exists_isSolution_real_not_bddAbove_of_not_satisfiesRootCondition
      (by rwa [LinearRecurrence.charPoly_map, charPoly_toLinearRecurrenceZero])
  obtain ⟨h₀, hh₀, C, hC, hst⟩ := h
  set ε : ℝ := ⨆ k : Fin (M.p + 1), |v k| with hε
  have hε0 : 0 ≤ ε := Real.iSup_nonneg fun _ => abs_nonneg _
  set δ : ℕ → ℝ := fun k => if k ≤ M.p then v k else 0 with hδ
  have hδle : ∀ k, |δ k| ≤ ε := fun k => by
    simp only [hδ]
    split_ifs with hk
    · exact le_ciSup (f := fun k : Fin (M.p + 1) => |v k|) (Finite.bddAbove_range _)
        ⟨k, Nat.lt_succ_of_le hk⟩
    · simpa using hε0
  refine hv' ⟨C * ε, ?_⟩
  rintro _ ⟨n, rfl⟩
  -- a step so small that `n` lies on the grid
  set hs : ℝ := min h₀ (T / (n + 1)) with hhs
  have hhs0 : 0 < hs := lt_min hh₀ (by positivity)
  have hnN : n ≤ gridCount T hs := by
    rw [le_gridCount_iff hT.le hhs0]
    calc (n : ℝ) * hs ≤ n * (T / (n + 1)) := by gcongr; exact min_le_right _ _
      _ ≤ T := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  have hu : M.IsOrbit (fun _ _ => (0 : ℝ)) hs t₀ (fun _ => 0) := by
    rw [isOrbit_iff]
    intro n
    simp
  have hz : M.IsOrbitWith (fun _ _ => (0 : ℝ)) hs t₀ δ v :=
    M.isOrbitWith_of_isOrbit (M.isOrbit_zero_iff_isSolution.2 hv) fun k hk => by
      have : ¬ k ≤ M.p := by omega
      simp [hδ, this]
  have := hst hs ⟨hhs0, min_le_left _ _⟩ ε hε0 δ (fun k _ => by
    rw [Real.norm_eq_abs]; exact hδle k) _ v hu hz (fun k hk => by simp [hδ, hk]) n hnN
  simpa using this

/-- **Theorem 11.4** of [quarteroni2000numerical], the equivalence of zero-stability and the root
condition. Let $T > 0$. The method is zero-stable on $[t_0, t_0 + T]$ for every scalar field $f$
such that $f(t, \cdot)$ is Lipschitz, with one constant $L$, for all $t \in [t_0, t_0 + T]$, if
and only if it satisfies the root condition.

The source also assumes that the method is consistent. The proof does not need it. -/
theorem isZeroStable_iff_satisfiesRootCondition (hT : 0 < T) :
    (∀ (f : ℝ → ℝ → ℝ) (L : NNReal), (∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t)) →
      M.IsZeroStable f t₀ T) ↔ M.SatisfiesRootCondition :=
  ⟨fun H => M.satisfiesRootCondition_of_isZeroStable hT
    (H _ 0 fun _ _ => LipschitzWith.const' 0),
    fun hroot _ _ hf => M.isZeroStable_of_satisfiesRootCondition hroot hT.le hf⟩

end Theorem114

/-! ### Convergence: Theorem 11.5 and Corollary 11.1 -/

section Theorem115

variable {L : NNReal} {y : ℝ → E}

/-- **Convergence** of the method for the field $f$ to the curve $y$ on the horizon
$[t_0, t_0 + T]$. There are $h_0 > 0$ and a function $C(\varepsilon, h)$ with
$C(\varepsilon, h) \to 0$ as $\varepsilon \to 0^+$ (with $\varepsilon \ge 0$) and $h \to 0^+$
jointly, such that for every $h \in (0, h_0]$ every orbit $u$ satisfies
$$\|u_n - y(t_n)\| \le C\Bigl( \max_{k \le p} \|u_k - y(t_k)\|, \, h \Bigr) \qquad (n \le
  N_h).$$

This reads Definition 11.5 of [quarteroni2000numerical] for a multistep method with starting
values, as Theorem 11.5 of the source requires. The source assumes that the error in the
starting values tends to $0$ as $h \to 0$; that is a hypothesis on a family of orbits. Because
the limit here is joint, the conclusion follows for every such family. -/
def IsConvergentFor (f : ℝ → E → E) (t₀ T : ℝ) (y : ℝ → E) : Prop :=
  ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ → ℝ → ℝ,
    Tendsto (fun p : ℝ × ℝ => C p.1 p.2) (𝓝[≥] 0 ×ˢ 𝓝[>] 0) (𝓝 0) ∧
    ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → E, M.IsOrbit f h t₀ u → ∀ n ≤ gridCount T h,
      ‖u n - y (node t₀ h n)‖ ≤ C (⨆ k : Fin (M.p + 1), ‖u k - y (node t₀ h k)‖) h

/-- **Convergence with order $q$** of the method for the field $f$ to the curve $y$ on
$[t_0, t_0 + T]$, from Theorem 11.5 of [quarteroni2000numerical]. There are $h_0 > 0$ and
$K > 0$ such that for every $h \in (0, h_0]$ every orbit $u$ satisfies
$$\|u_n - y(t_n)\| \le K \Bigl( \max_{k \le p} \|u_k - y(t_k)\| + h^q \Bigr) \qquad (n \le
  N_h).$$
Hence starting errors of size $O(h^q)$ give a global error $O(h^q)$. -/
def IsConvergentWithOrderFor (f : ℝ → E → E) (t₀ T : ℝ) (y : ℝ → E) (q : ℕ) : Prop :=
  ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ K : ℝ, 0 < K ∧ ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → E, M.IsOrbit f h t₀ u →
    ∀ n ≤ gridCount T h,
      ‖u n - y (node t₀ h n)‖ ≤ K * ((⨆ k : Fin (M.p + 1), ‖u k - y (node t₀ h k)‖) + h ^ q)

/-- The **convergence estimate**, from (11.65) of [quarteroni2000numerical] with
$\delta_m = \tau_m(h)$, behind Theorem 11.5. Let the method satisfy the root condition, let
$T \ge 0$, let $f(t, \cdot)$ be $L$-Lipschitz for every $t \in [t_0, t_0 + T]$, and let $y$ have
the derivative $f(t, y(t))$ at every $t \in [t_0, t_0 + T]$. Then there are $h_0 > 0$ and
$K > 0$ such that for every $h \in (0, h_0]$ every orbit $u$ satisfies
$$\|u_n - y(t_n)\| \le K \Bigl( \max_{k \le p} \|u_k - y(t_k)\| + T \tau(h) \Bigr)
  \qquad (n \le N_h),$$
where $\tau(h)$ is the global truncation error along $y$.

The exact solution is a perturbed orbit on the horizon with $\delta_{n+1} = \tau_{n+1}(h)$, by
`ODE.LinearMultistep.lte_spec`. -/
theorem norm_sub_le_globalLte_of_satisfiesRootCondition (hroot : M.SatisfiesRootCondition)
    (hT : 0 ≤ T) (hf : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t))
    (hy : ∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ K : ℝ, 0 < K ∧ ∀ h ∈ Ioc 0 h₀, ∀ u : ℕ → E, M.IsOrbit f h t₀ u →
      ∀ n ≤ gridCount T h, ‖u n - y (node t₀ h n)‖ ≤
        K * ((⨆ k : Fin (M.p + 1), ‖u k - y (node t₀ h k)‖) + T * M.globalLte t₀ T y h) := by
  obtain ⟨h₀, hh₀, K, hK, hest⟩ := M.norm_sub_le_of_satisfiesRootCondition hroot hT hf
  refine ⟨h₀, hh₀, K, hK, fun h hh u hu n hn => ?_⟩
  have hh0 : 0 < h := hh.1
  set δ : ℕ → E := fun l => if l ≤ M.p then y (node t₀ h l) - u l else M.lte h y (node t₀ h (l - 1))
    with hδ
  have hz : ∀ n, n + M.p + 1 ≤ gridCount T h → y (node t₀ h (n + M.p + 1)) =
      M.rhs f h t₀ (fun k => y (node t₀ h k)) n + h • δ (n + M.p + 1) := by
    intro n hn
    have hd : ∀ j : Fin (M.p + 1), deriv y (node t₀ h (n + M.p) - j * h) =
        f (node t₀ h (n + M.p) - j * h) (y (node t₀ h (n + M.p) - j * h)) := fun j => by
      rw [node_sub_mul (by omega)]
      exact (hy _ (node_mem_Icc hT hh0 (by omega))).deriv
    have hd' : deriv y (node t₀ h (n + M.p) + h) =
        f (node t₀ h (n + M.p) + h) (y (node t₀ h (n + M.p) + h)) := by
      rw [← node_succ]
      exact (hy _ (node_mem_Icc hT hh0 hn)).deriv
    have key := M.lte_spec hh0.ne' hd hd'
    have e1 : ∀ j : Fin (M.p + 1), node t₀ h (n + M.p) - j * h = node t₀ h (n + M.p - j) :=
      fun j => node_sub_mul (by omega)
    have e2 : node t₀ h (n + M.p) + h = node t₀ h (n + M.p + 1) := (node_succ _ _ _).symm
    simp only [e1, e2] at key
    simp only [hδ, show ¬ (n + M.p + 1 ≤ M.p) by omega, ite_false, Nat.add_sub_cancel, rhs]
    exact key
  have hδ0 : ∀ k ≤ M.p, ‖y (node t₀ h k) - u k‖ ≤ ⨆ k : Fin (M.p + 1), ‖u k - y (node t₀ h k)‖ :=
    fun k hk => by
      rw [norm_sub_rev]
      exact le_ciSup (f := fun k : Fin (M.p + 1) => ‖u k - y (node t₀ h k)‖)
        (Finite.bddAbove_range _) ⟨k, Nat.lt_succ_of_le hk⟩
  have hδ1 : ∀ k, M.p + 1 ≤ k → k ≤ gridCount T h → ‖δ k‖ ≤ M.globalLte t₀ T y h := by
    intro k hk1 hk2
    simp only [hδ, show ¬ (k ≤ M.p) by omega, ite_false]
    exact M.norm_lte_le_globalLte (by omega) (by omega)
  have := hest h hh (Real.iSup_nonneg fun _ => norm_nonneg _) (M.globalLte_nonneg _)
    (fun n _ => (M.isOrbit_iff_rhs.1 hu) n) hz hδ0 hδ1 n hn
  rwa [norm_sub_rev] at this

/-- **Theorem 11.5** of [quarteroni2000numerical], sufficiency. Let the method satisfy the root
condition, let $T \ge 0$, let $f(t, \cdot)$ be $L$-Lipschitz for every $t \in [t_0, t_0 + T]$,
and let $y$ have the derivative $f(t, y(t))$ at every $t \in [t_0, t_0 + T]$. If the method is
consistent along $y$, then it is convergent for $f$ to $y$ on $[t_0, t_0 + T]$.

The bound is $C(\varepsilon, h) = K (\varepsilon + T \tau(h))$, from
`ODE.LinearMultistep.norm_sub_le_globalLte_of_satisfiesRootCondition`. -/
theorem isConvergentFor_of_satisfiesRootCondition (hroot : M.SatisfiesRootCondition) (hT : 0 ≤ T)
    (hf : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t))
    (hy : ∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) (hcons : M.IsConsistentFor t₀ T y) :
    M.IsConvergentFor f t₀ T y := by
  obtain ⟨h₀, hh₀, K, hK, hest⟩ := M.norm_sub_le_globalLte_of_satisfiesRootCondition hroot hT hf hy
  refine ⟨h₀, hh₀, fun ε h => K * (ε + T * M.globalLte t₀ T y h), ?_, hest⟩
  have h1 : Tendsto (fun p : ℝ × ℝ => p.1) (𝓝[≥] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_fst.mono_right nhdsWithin_le_nhds
  have h2 : Tendsto (fun p : ℝ × ℝ => M.globalLte t₀ T y p.2) (𝓝[≥] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝 0) := hcons.comp tendsto_snd
  have := (h1.add (h2.const_mul T)).const_mul K
  simpa using this

/-- **Theorem 11.5** of [quarteroni2000numerical], order of convergence. Let the method satisfy the
root condition, let $T \ge 0$, let $f(t, \cdot)$ be $L$-Lipschitz for every
$t \in [t_0, t_0 + T]$, and let $y$ have the derivative $f(t, y(t))$ at every
$t \in [t_0, t_0 + T]$. If the method has order $q$ along $y$, then it is convergent with order
$q$ for $f$ to $y$ on $[t_0, t_0 + T]$. -/
theorem isConvergentWithOrderFor_of_satisfiesRootCondition (hroot : M.SatisfiesRootCondition)
    (hT : 0 ≤ T) (hf : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t))
    (hy : ∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) {q : ℕ}
    (hord : M.HasOrderFor t₀ T y q) : M.IsConvergentWithOrderFor f t₀ T y q := by
  obtain ⟨h₀, hh₀, K, hK, hest⟩ := M.norm_sub_le_globalLte_of_satisfiesRootCondition hroot hT hf hy
  obtain ⟨c, hc, hbig⟩ := hord.exists_pos
  obtain ⟨h₁, hh₁, hIoc⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hbig.bound
  refine ⟨min h₀ h₁, lt_min hh₀ hh₁, K * (1 + T * c), by positivity, fun h hh u hu n hn => ?_⟩
  have hh0 : h ∈ Ioc 0 h₀ := ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  have hτ : M.globalLte t₀ T y h ≤ c * h ^ q := by
    have h' : ‖M.globalLte t₀ T y h‖ ≤ c * ‖h ^ q‖ := hIoc ⟨hh.1, hh.2.trans (min_le_right _ _)⟩
    rwa [Real.norm_of_nonneg (M.globalLte_nonneg _), Real.norm_of_nonneg (pow_nonneg hh.1.le q)]
      at h'
  refine (hest h hh0 u hu n hn).trans ?_
  have hε : 0 ≤ ⨆ k : Fin (M.p + 1), ‖u k - y (node t₀ h k)‖ :=
    Real.iSup_nonneg fun _ => norm_nonneg _
  have hp : 0 ≤ h ^ q := pow_nonneg hh.1.le q
  calc K * ((⨆ k : Fin (M.p + 1), ‖u k - y (node t₀ h k)‖) + T * M.globalLte t₀ T y h)
      ≤ K * ((⨆ k : Fin (M.p + 1), ‖u k - y (node t₀ h k)‖) + T * (c * h ^ q)) := by gcongr
    _ ≤ K * (1 + T * c) * ((⨆ k : Fin (M.p + 1), ‖u k - y (node t₀ h k)‖) + h ^ q) := by
        nlinarith [mul_nonneg hT hc.le, mul_nonneg (mul_nonneg hT hc.le) hε, mul_nonneg hK.le hp]

end Theorem115

section Theorem115Necessity

/-- **Theorem 11.5** of [quarteroni2000numerical], necessity. Let $T > 0$. If the method is
convergent for the scalar problem $y' = 0$ to the solution $y = 0$ on $[t_0, t_0 + T]$, then it
satisfies the root condition.

When the root condition fails, the real recurrence of the method has a solution $v$ with
$|v_n| \ge cn$ for infinitely many $n$
(`LinearRecurrence.exists_isSolution_real_frequently_le`). The orbits $hv$ have the starting
error $h \max_{k \le p} |v_k| \to 0$. With $h = T / n$, convergence gives
$(T / n) |v_n| \le C(h m_0, h) \to 0$, where $m_0 = \max_{k \le p} |v_k|$, while
$(T / n) |v_n| \ge Tc$ for infinitely many $n$. -/
theorem satisfiesRootCondition_of_isConvergentFor (hT : 0 < T)
    (h : M.IsConvergentFor (E := ℝ) (fun _ _ => 0) t₀ T fun _ => 0) : M.SatisfiesRootCondition := by
  by_contra hroot
  obtain ⟨v, hv, c, hc, hfreq⟩ := M.toLinearRecurrenceZero.exists_isSolution_real_frequently_le
    (by rwa [LinearRecurrence.charPoly_map, charPoly_toLinearRecurrenceZero])
  obtain ⟨h₀, hh₀, C, hC, hconv⟩ := h
  set m₀ : ℝ := ⨆ k : Fin (M.p + 1), |v k| with hm₀
  have hm₀0 : 0 ≤ m₀ := Real.iSup_nonneg fun _ => abs_nonneg _
  -- the path `n ↦ (T m₀ / n, T / n)` and the limit of `C` along it
  have hpath : Tendsto (fun n : ℕ => (T * m₀ / n, T / n)) atTop (𝓝[≥] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) := by
    refine Tendsto.prodMk ?_ ?_
    · exact tendsto_nhdsWithin_iff.2 ⟨tendsto_const_div_atTop_nhds_zero_nat _,
        Eventually.of_forall fun n => by simp only [mem_Ici]; positivity⟩
    · refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_div_atTop_nhds_zero_nat _, ?_⟩
      filter_upwards [eventually_gt_atTop 0] with n hn
      simp only [mem_Ioi]
      positivity
  have hlim : Tendsto (fun n : ℕ => C (T * m₀ / n) (T / n)) atTop (𝓝 0) := hC.comp hpath
  have hev : ∀ᶠ n : ℕ in atTop, C (T * m₀ / n) (T / n) < T * c :=
    hlim.eventually (gt_mem_nhds (by positivity))
  -- for large `n` on the subsequence, the orbit `(T/n) • v` contradicts the bound
  have hbound : ∀ᶠ n : ℕ in atTop, c * n ≤ |v n| → T * c ≤ C (T * m₀ / n) (T / n) := by
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈T / h₀⌉₊] with n hn1 hn2 hcn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    set hs : ℝ := T / n with hhs
    have hhs0 : 0 < hs := by positivity
    have hhsle : hs ≤ h₀ := by
      rw [hhs, div_le_iff₀ hn0]
      have := (Nat.ceil_le.1 hn2)
      rw [div_le_iff₀ hh₀] at this
      linarith
    have hnN : n ≤ gridCount T hs := by
      rw [le_gridCount_iff hT.le hhs0, hhs, mul_div_cancel₀ _ hn0.ne']
    have hu : M.IsOrbit (fun _ _ => (0 : ℝ)) hs t₀ fun k => hs * v k := by
      rw [isOrbit_zero_iff_isSolution]
      have : (fun k => hs * v k) = hs • v := by ext k; simp
      rw [this, LinearRecurrence.is_sol_iff_mem_solSpace]
      exact M.toLinearRecurrenceZero.solSpace.smul_mem hs
        ((LinearRecurrence.is_sol_iff_mem_solSpace _ _).1 hv)
    have key := hconv hs ⟨hhs0, hhsle⟩ _ hu n hnN
    simp only [sub_zero, Real.norm_eq_abs, abs_mul, abs_of_pos hhs0] at key
    rw [← Real.mul_iSup_of_nonneg hhs0.le] at key
    have e1 : hs * ⨆ k : Fin (M.p + 1), |v k| = T * m₀ / n := by rw [hhs, hm₀]; ring
    rw [e1] at key
    calc T * c = hs * (c * n) := by rw [hhs]; field_simp
      _ ≤ hs * |v n| := by gcongr
      _ ≤ C (T * m₀ / n) (T / n) := key
  obtain ⟨n, hn1, hn2, hn3⟩ := (hfreq.and_eventually (hbound.and hev)).exists
  linarith [hn2 hn1]

/-- **Corollary 11.1** of [quarteroni2000numerical] (the Lax–Richtmyer equivalence theorem). Let the
method be consistent and let $T > 0$. Then the following are equivalent:

* for every scalar field $f$ such that $f(t, \cdot)$ is $L$-Lipschitz for all
  $t \in [t_0, t_0 + T]$, and every $y$ with the derivative $f(t, y(t))$ at every
  $t \in [t_0, t_0 + T]$ such that $t \mapsto f(t, y(t))$ is continuous on $[t_0, t_0 + T]$, the
  method is convergent for $f$ to $y$;
* for every scalar field $f$ such that $f(t, \cdot)$ is $L$-Lipschitz for all
  $t \in [t_0, t_0 + T]$, the method is zero-stable for $f$ on $[t_0, t_0 + T]$.

Both statements are equivalent to the root condition, by Theorems 11.4 and 11.5. The continuity
of $t \mapsto f(t, y(t))$ says that the solution $y$ is $C^1$ on the horizon. -/
theorem isConvergentFor_iff_isZeroStable (hcons : M.IsConsistent) (hT : 0 < T) :
    (∀ (f : ℝ → ℝ → ℝ) (L : NNReal) (y : ℝ → ℝ), (∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t)) →
      (∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) →
      ContinuousOn (fun t => f t (y t)) (Icc t₀ (t₀ + T)) → M.IsConvergentFor f t₀ T y) ↔
    (∀ (f : ℝ → ℝ → ℝ) (L : NNReal), (∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t)) →
      M.IsZeroStable f t₀ T) := by
  rw [M.isZeroStable_iff_satisfiesRootCondition hT]
  constructor
  · intro H
    exact M.satisfiesRootCondition_of_isConvergentFor hT
      (H _ 0 _ (fun _ _ => LipschitzWith.const' 0) (fun _ _ => hasDerivAt_const _ _)
        continuousOn_const)
  · intro hroot f L y hf hy hy'
    obtain ⟨h0, h1⟩ := M.isConsistent_iff.1 hcons
    exact M.isConvergentFor_of_satisfiesRootCondition hroot hT.le hf hy
      (M.isConsistentFor_of_orderCondition h0 h1 hy hy')

end Theorem115Necessity



end LinearMultistep

end ODE

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace LinearMultistep

variable (M : LinearMultistep) {f : ℝ → E → E} {h t₀ T : ℝ} {n : ℕ}

/-! ### One-step methods as multistep methods -/

section OneStepInstance

/-- **A one-step method** as a linear multistep method with $p = 0$:
$$u_{n+1} = a_0 u_n + h (b_0 f_n + b_{-1} f_{n+1}).$$
Forward Euler is `ofOneStep 1 1 0`, backward Euler is `ofOneStep 1 0 1`, Crank–Nicolson is
`ofOneStep 1 (1/2) (1/2)`, and the θ-method is `ofOneStep 1 (1 - θ) θ`. -/
def ofOneStep (a₀ b₀ bm1 : ℝ) : LinearMultistep := ⟨0, ![a₀], ![b₀], bm1⟩

/-- A sequence $u$ is an orbit of `ODE.LinearMultistep.ofOneStep a₀ b₀ bm1` if and only if, for
every $n$,
$$u_{n+1} = a_0 u_n + h \bigl( b_0 f(t_n, u_n) + b_{-1} f(t_{n+1}, u_{n+1}) \bigr).$$
-/
theorem isOrbit_ofOneStep_iff {a₀ b₀ bm1 : ℝ} {u : ℕ → E} :
    (ofOneStep a₀ b₀ bm1).IsOrbit f h t₀ u ↔ ∀ n, u (n + 1) =
      a₀ • u n + h • (b₀ • f (node t₀ h n) (u n) + bm1 • f (node t₀ h (n + 1)) (u (n + 1))) := by
  rw [isOrbit_iff]
  unfold ofOneStep
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Nat.sub_zero,
    Matrix.cons_val_zero, add_zero, smul_add, smul_smul, add_assoc]

/-- The orbits of `ofOneStep 1 (1 - θ) θ` are the orbits of the θ-method `ODE.OneStep.theta` of
`Numlib.ODE.OneStep`, $u_{n+1} = u_n + h ((1 - \theta) f(t_n, u_n) + \theta f(t_{n+1},
u_{n+1}))$. -/
theorem isOrbit_ofOneStep_theta_iff {θ : ℝ} {u : ℕ → E} :
    (ofOneStep 1 (1 - θ) θ).IsOrbit f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (OneStep.theta f θ)) h t₀ u := by
  rw [isOrbit_ofOneStep_iff, OneStep.isOrbit_ofIncrement_iff]
  simp only [OneStep.theta, one_smul, node_succ]

/-- The orbits of `ofOneStep 1 1 0` are the orbits of forward Euler, `ODE.OneStep.forwardEuler`. -/
theorem isOrbit_ofOneStep_forwardEuler_iff {u : ℕ → E} :
    (ofOneStep 1 1 0).IsOrbit f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (OneStep.forwardEuler f)) h t₀ u := by
  rw [isOrbit_ofOneStep_iff, OneStep.isOrbit_ofIncrement_iff]
  simp only [OneStep.forwardEuler, one_smul, zero_smul, add_zero]

/-- The orbits of `ofOneStep 1 0 1` are the orbits of backward Euler, `ODE.OneStep.backwardEuler`.
-/
theorem isOrbit_ofOneStep_backwardEuler_iff {u : ℕ → E} :
    (ofOneStep 1 0 1).IsOrbit f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (OneStep.backwardEuler f)) h t₀ u := by
  rw [isOrbit_ofOneStep_iff, OneStep.isOrbit_ofIncrement_iff]
  simp only [OneStep.backwardEuler, one_smul, zero_smul, zero_add, node_succ]

/-- The orbits of `ofOneStep 1 (1/2) (1/2)` are the orbits of Crank–Nicolson,
`ODE.OneStep.crankNicolson`. -/
theorem isOrbit_ofOneStep_crankNicolson_iff {u : ℕ → E} :
    (ofOneStep 1 (1 / 2) (1 / 2)).IsOrbit f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (OneStep.crankNicolson f)) h t₀ u := by
  rw [isOrbit_ofOneStep_iff, OneStep.isOrbit_ofIncrement_iff]
  simp only [OneStep.crankNicolson, one_smul, smul_add, node_succ, one_div]

/-- The first characteristic polynomial of `ODE.LinearMultistep.ofOneStep a₀ b₀ bm1` is
$\rho(r) = r - a_0$. -/
theorem rho_ofOneStep (a₀ b₀ bm1 : ℝ) : (ofOneStep a₀ b₀ bm1).rho = X - C a₀ := by
  unfold rho ofOneStep
  simp

/-- The second characteristic polynomial of `ODE.LinearMultistep.ofOneStep a₀ b₀ bm1` is
$\sigma(r) = b_{-1} r + b_0$. -/
theorem sigma_ofOneStep (a₀ b₀ bm1 : ℝ) : (ofOneStep a₀ b₀ bm1).sigma = C bm1 * X + C b₀ := by
  unfold sigma ofOneStep
  simp

/-- **Consistent one-step methods satisfy the root condition** ([quarteroni2000numerical], §11.6.3).
If $p = 0$ and the order condition $0$ holds, then $\rho(r) = r - 1$, and the method satisfies
the root condition. -/
theorem satisfiesRootCondition_of_p_eq_zero (hp : M.p = 0) (h0 : M.orderCondition 0) :
    M.SatisfiesRootCondition := by
  obtain ⟨p, a, b, bm1⟩ := M
  simp only at hp
  subst hp
  rw [orderCondition_zero] at h0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h0
  have hrho : (⟨0, a, b, bm1⟩ : LinearMultistep).rho = X ^ 0 * (X - C 1) := by
    unfold rho
    simp [h0]
  rw [SatisfiesRootCondition, hrho]
  exact Polynomial.satisfiesRootCondition_X_pow_mul_X_sub_one 0

end OneStepInstance

/-!
### Adams-type methods

An Adams-type method has $a_0 = 1$ and $a_j = 0$ for $j \ge 1$, that is, $a = e_0$.
-/

section AdamsType

/-- An Adams-type method, with $a = e_0$, satisfies the order condition $0$. -/
theorem orderCondition_zero_of_a_single (ha : M.a = Pi.single 0 1) : M.orderCondition 0 := by
  rw [orderCondition_zero, ha, Fintype.sum_pi_single']

/-- For an Adams-type method, with $a = e_0$, the sum $\sum_j (-j)^{i+1} a_j$ is $0$ for every $i$.
-/
theorem sum_pow_succ_mul_a_eq_zero (ha : M.a = Pi.single 0 1) (i : ℕ) :
    ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ (i + 1) * M.a j = 0 := by
  rw [ha, Finset.sum_eq_single 0 (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
  simp

/-- For an Adams-type method, with $a = e_0$, the order condition $i + 1$ reads
$$(i + 1) \Bigl( b_{-1} + \sum_{j=0}^p (-j)^i b_j \Bigr) = 1.$$
-/
theorem orderCondition_succ_of_a_single (ha : M.a = Pi.single 0 1) (i : ℕ) :
    M.orderCondition (i + 1) ↔
      (i + 1 : ℝ) * (M.bm1 + ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ i * M.b j) = 1 := by
  rw [orderCondition_succ, M.sum_pow_succ_mul_a_eq_zero ha, zero_add]

/-- For an Adams-type method, with $a = e_0$, the Taylor coefficient $c_{i+1}$ is
$$c_{i+1} = 1 - (i + 1) \Bigl( b_{-1} + \sum_{j=0}^p (-j)^i b_j \Bigr).$$
-/
theorem taylorCoeff_succ_of_a_single (ha : M.a = Pi.single 0 1) (i : ℕ) :
    M.taylorCoeff (i + 1) =
      1 - (i + 1 : ℝ) * (M.bm1 + ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ i * M.b j) := by
  rw [taylorCoeff, M.sum_pow_succ_mul_a_eq_zero ha, sub_zero, Nat.add_sub_cancel]
  push_cast
  ring

/-- For an Adams-type method, with $a = e_0$, the error constant of order $q$ is
$$C_{q+1} = \frac{1 - (q + 1) \bigl( b_{-1} + \sum_{j=0}^p (-j)^q b_j \bigr)}{(q + 1)!}.$$
-/
theorem errorConstant_of_a_single (ha : M.a = Pi.single 0 1) (q : ℕ) :
    M.errorConstant q =
      (1 - (q + 1 : ℝ) * (M.bm1 + ∑ j : Fin (M.p + 1), (-(j : ℝ)) ^ q * M.b j)) /
        (q + 1).factorial := by
  rw [errorConstant, M.taylorCoeff_succ_of_a_single ha]

/-- For an Adams-type method, with $a = e_0$, the first characteristic polynomial is
$\rho(r) = r^{p+1} - r^p = r^p (r - 1)$. -/
theorem rho_of_a_single (ha : M.a = Pi.single 0 1) : M.rho = X ^ M.p * (X - C 1) := by
  rw [rho, ha, Finset.sum_eq_single 0 (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
  simp only [Pi.single_eq_same, map_one, one_mul, Fin.val_zero, Nat.sub_zero]
  ring

/-- **Adams-type methods satisfy the root condition** ([quarteroni2000numerical], §11.6.3). If
$a = e_0$, then the roots of $\rho(r) = r^p (r - 1)$ are $0$, of multiplicity $p$, and $1$,
which is simple. -/
theorem satisfiesRootCondition_of_a_single (ha : M.a = Pi.single 0 1) :
    M.SatisfiesRootCondition := by
  rw [SatisfiesRootCondition, M.rho_of_a_single ha]
  exact Polynomial.satisfiesRootCondition_X_pow_mul_X_sub_one M.p

end AdamsType

/-! ### The Adams weights -/

section AdamsWeight

/-- The **Adams weights** of a node vector $x = (x_0, \dots, x_{k-1})$ are
$$w_i = \int_0^1 \ell_i(s) \, ds,$$
where $\ell_i$ is the Lagrange basis polynomial of the node $x_i$. In the normalized variable
$s = (t - t_n) / h$, this is the integral over $[t_n, t_{n+1}]$ that defines the coefficients of
the Adams methods ([quarteroni2000numerical], §11.5.1).

The definition does not assume that the nodes are distinct. -/
noncomputable def adamsWeight {k : ℕ} (x : Fin k → ℝ) (i : Fin k) : ℝ :=
  ∫ s in (0 : ℝ)..1, (Lagrange.basis Finset.univ x i).eval s

/-- The **moment identities** of the Adams weights. If the nodes $x_0, \dots, x_{k-1}$ are distinct
and $m < k$, then
$$\sum_{i=0}^{k-1} x_i^m w_i = \frac{1}{m + 1}.$$
That is, the interpolatory quadrature $g \mapsto \sum_i w_i g(x_i)$ of $\int_0^1 g$ is exact on
the monomials $s^m$, $m < k$. -/
theorem sum_pow_mul_adamsWeight {k : ℕ} {x : Fin k → ℝ} (hx : Function.Injective x) {m : ℕ}
    (hm : m < k) : ∑ i, x i ^ m * adamsWeight x i = 1 / (m + 1) := by
  have hint : ∀ i : Fin k, IntervalIntegrable (fun s => (Lagrange.basis Finset.univ x i).eval s)
      MeasureTheory.volume 0 1 := fun i =>
    (Lagrange.basis Finset.univ x i).continuous.intervalIntegrable _ _
  have e : ∀ s : ℝ, ∑ i, x i ^ m * (Lagrange.basis Finset.univ x i).eval s = s ^ m := by
    intro s
    have hf := Lagrange.eq_interpolate (s := Finset.univ) (v := x) (f := (X : ℝ[X]) ^ m)
      hx.injOn (by rw [degree_X_pow, Finset.card_univ, Fintype.card_fin]; exact_mod_cast hm)
    have := congrArg (eval s) hf
    rw [Lagrange.interpolate_apply, eval_finsetSum] at this
    simp only [eval_pow, eval_X, eval_mul, eval_C] at this
    rw [this]
  simp only [adamsWeight, ← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum fun i _ => (hint i).const_mul _]
  simp only [e, integral_pow, one_pow, zero_pow (Nat.succ_ne_zero m), sub_zero]

/-- **Uniqueness of weights with given moments.** Let the nodes $x_0, \dots, x_{k-1}$ be distinct.
If a weight vector $w$ satisfies $\sum_i x_i^m w_i = 1 / (m + 1)$ for all $m < k$, then $w$ is
the vector of Adams weights of $x$.

The moment system is a transposed Vandermonde system. This identifies the printed coefficient
rows of the Adams methods. -/
theorem eq_adamsWeight_of_moments {k : ℕ} {x : Fin k → ℝ} (hx : Function.Injective x)
    {w : Fin k → ℝ} (hw : ∀ m < k, ∑ i, x i ^ m * w i = 1 / (m + 1)) : w = adamsWeight x := by
  set V := (Matrix.vandermonde x).transpose with hV
  have hVu : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).2
    (isUnit_iff_ne_zero.2 (LinearRecurrence.det_vandermonde_transpose_ne_zero hx))
  have hmul : ∀ γ : Fin k → ℝ, V.mulVec γ = fun m : Fin k => ∑ i, x i ^ (m : ℕ) * γ i := by
    intro γ
    ext m
    simp [hV, Matrix.mulVec, dotProduct, Matrix.vandermonde, mul_comm]
  apply Matrix.mulVec_injective_iff_isUnit.2 hVu
  rw [hmul, hmul]
  ext m
  rw [hw m m.2, sum_pow_mul_adamsWeight hx m.2]

end AdamsWeight

/-! ### The Adams–Bashforth methods -/

section AdamsBashforth

/-- The Adams–Bashforth nodes $x_j = -j$, $j = 0, \dots, p$, in the normalized variable. -/
def adamsBashforthNode (p : ℕ) (j : Fin (p + 1)) : ℝ := -(j : ℝ)

/-- The Adams–Bashforth nodes are distinct. -/
theorem injective_adamsBashforthNode (p : ℕ) : Function.Injective (adamsBashforthNode p) :=
  fun _ _ hij => Fin.ext (Nat.cast_injective (neg_injective hij))

/-- The **Adams–Bashforth method with $p + 1$ steps**, (11.49) of [quarteroni2000numerical], case 1:
$$u_{n+1} = u_n + h \sum_{j=0}^p b_j f_{n-j},$$
with $b_{-1} = 0$ and the Adams weights $b_j = \int_0^1 \ell_j(s) \, ds$ of the nodes
$t_n, t_{n-1}, \dots, t_{n-p}$, that is, $s = 0, -1, \dots, -p$. The method is explicit, and
`adamsBashforth 0` is forward Euler. -/
noncomputable def adamsBashforth (p : ℕ) : LinearMultistep :=
  ⟨p, Pi.single 0 1, adamsWeight (adamsBashforthNode p), 0⟩

/-- For the Adams–Bashforth method, $b_{-1} + \sum_j (-j)^i b_j = \sum_j x_j^i w_j$, the $i$-th
moment of the Adams weights $w$ of the nodes $x_j = -j$. -/
theorem adamsBashforth_bm1_add_sum (p i : ℕ) :
    (adamsBashforth p).bm1 + ∑ j : Fin ((adamsBashforth p).p + 1),
      (-(j : ℝ)) ^ i * (adamsBashforth p).b j =
      ∑ j : Fin (p + 1), adamsBashforthNode p j ^ i * adamsWeight (adamsBashforthNode p) j := by
  change 0 + ∑ j : Fin (p + 1), (-(j : ℝ)) ^ i * adamsWeight (adamsBashforthNode p) j = _
  rw [zero_add]
  rfl

/-- **The Adams–Bashforth methods have order equal to their number of steps**
([quarteroni2000numerical], §11.5.1): the method with $p + 1$ steps has order $p + 1$.

The order conditions are the moment identities `ODE.LinearMultistep.sum_pow_mul_adamsWeight` of
the interpolatory weights. -/
theorem adamsBashforth_hasOrder (p : ℕ) : (adamsBashforth p).HasOrder (p + 1) := by
  rw [hasOrder_iff]
  intro i hi
  rcases i with _ | i
  · exact (adamsBashforth p).orderCondition_zero_of_a_single rfl
  · rw [(adamsBashforth p).orderCondition_succ_of_a_single rfl, adamsBashforth_bm1_add_sum,
      sum_pow_mul_adamsWeight (injective_adamsBashforthNode p) (by omega)]
    field_simp

/-- The Adams–Bashforth methods satisfy the root condition. -/
theorem adamsBashforth_satisfiesRootCondition (p : ℕ) :
    (adamsBashforth p).SatisfiesRootCondition :=
  (adamsBashforth p).satisfiesRootCondition_of_a_single rfl

/-- Let $w_0, \dots, w_p$ satisfy $\sum_i (-i)^m w_i = 1 / (m + 1)$ for all $m \le p$. Then
`adamsBashforth p` is the method with $p + 1$ steps, $a = e_0$, $b = w$ and $b_{-1} = 0$. -/
theorem adamsBashforth_eq {p : ℕ} {w : Fin (p + 1) → ℝ}
    (hw : ∀ m < p + 1, ∑ i, adamsBashforthNode p i ^ m * w i = 1 / (m + 1)) :
    adamsBashforth p = ⟨p, Pi.single 0 1, w, 0⟩ := by
  unfold adamsBashforth
  rw [eq_adamsWeight_of_moments (injective_adamsBashforthNode p) hw]

/-- **Forward Euler is the Adams–Bashforth method with one step** ([quarteroni2000numerical],
§11.5.1): `adamsBashforth 0 = ofOneStep 1 1 0`. -/
theorem adamsBashforth_zero_eq : adamsBashforth 0 = ofOneStep 1 1 0 := by
  rw [adamsBashforth_eq (w := ![1]) fun m hm => by rw [Nat.lt_one_iff.1 hm]; simp]
  unfold ofOneStep
  congr 1
  funext j
  fin_cases j
  simp

/-- **The Adams–Bashforth method with two steps**, (11.50) of [quarteroni2000numerical]:
$$u_{n+1} = u_n + \frac{h}{2} (3 f_n - f_{n-1}),$$
that is, $a = (1, 0)$, $b = (3/2, -1/2)$ and $b_{-1} = 0$. -/
theorem adamsBashforth_one_eq : adamsBashforth 1 = ⟨1, ![1, 0], ![3 / 2, -1 / 2], 0⟩ := by
  rw [adamsBashforth_eq (w := ![3 / 2, -1 / 2]) fun m hm => by
    interval_cases m <;> simp [Fin.sum_univ_succ, adamsBashforthNode] <;> norm_num]
  congr 1
  funext j
  fin_cases j <;> simp

/-- **The Adams–Bashforth method with three steps** ([quarteroni2000numerical], §11.5.1):
$$u_{n+1} = u_n + \frac{h}{12} (23 f_n - 16 f_{n-1} + 5 f_{n-2}).$$
-/
theorem adamsBashforth_two_eq :
    adamsBashforth 2 = ⟨2, ![1, 0, 0], ![23 / 12, -16 / 12, 5 / 12], 0⟩ := by
  rw [adamsBashforth_eq (w := ![23 / 12, -16 / 12, 5 / 12]) fun m hm => by
    interval_cases m <;> simp [Fin.sum_univ_succ, adamsBashforthNode] <;> norm_num]
  congr 1
  funext j
  fin_cases j <;> simp

/-- **The Adams–Bashforth method with four steps** ([quarteroni2000numerical], §11.5.1):
$$u_{n+1} = u_n + \frac{h}{24} (55 f_n - 59 f_{n-1} + 37 f_{n-2} - 9 f_{n-3}).$$
-/
theorem adamsBashforth_three_eq :
    adamsBashforth 3 = ⟨3, ![1, 0, 0, 0], ![55 / 24, -59 / 24, 37 / 24, -9 / 24], 0⟩ := by
  rw [adamsBashforth_eq (w := ![55 / 24, -59 / 24, 37 / 24, -9 / 24]) fun m hm => by
    interval_cases m <;> simp [Fin.sum_univ_succ, adamsBashforthNode] <;> norm_num]
  congr 1
  funext j
  fin_cases j <;> simp

/-- **The error constants of the Adams–Bashforth methods of orders 1 to 4** (Table 11.1 of
[quarteroni2000numerical], the column $C^*_{q+1}$): the method with $q$ steps has the error
constant $C_{q+1}$ equal to $1/2$, $5/12$, $3/8$ and $251/720$ for $q = 1, 2, 3, 4$. -/
theorem adamsBashforth_errorConstant :
    (adamsBashforth 0).errorConstant 1 = 1 / 2 ∧ (adamsBashforth 1).errorConstant 2 = 5 / 12 ∧
      (adamsBashforth 2).errorConstant 3 = 3 / 8 ∧
      (adamsBashforth 3).errorConstant 4 = 251 / 720 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [adamsBashforth_zero_eq]
    unfold errorConstant taylorCoeff ofOneStep
    norm_num [Fin.sum_univ_succ, Nat.factorial]
  · rw [adamsBashforth_one_eq]
    unfold errorConstant taylorCoeff
    norm_num [Fin.sum_univ_succ, Nat.factorial]
  · rw [adamsBashforth_two_eq]
    unfold errorConstant taylorCoeff
    norm_num [Fin.sum_univ_succ, Nat.factorial]
  · rw [adamsBashforth_three_eq]
    unfold errorConstant taylorCoeff
    norm_num [Fin.sum_univ_succ, Nat.factorial]

end AdamsBashforth

/-! ### The Adams–Moulton methods -/

section AdamsMoulton

/-- The Adams–Moulton nodes $x_i = 1 - i$, $i = 0, \dots, p$, that is, $1, 0, -1, \dots, -(p - 1)$,
in the normalized variable. -/
def adamsMoultonNode (p : ℕ) (i : Fin (p + 1)) : ℝ := 1 - (i : ℝ)

/-- The Adams–Moulton nodes are distinct. -/
theorem injective_adamsMoultonNode (p : ℕ) : Function.Injective (adamsMoultonNode p) :=
  fun _ _ hij => Fin.ext (Nat.cast_injective (sub_right_injective hij))

/-- The Adams–Moulton weights of the nodes $1, 0, \dots, -(p - 1)$, indexed by $\mathbb{N}$ and
extended by zero: the value at $i \le p$ is the Adams weight $w_i$ of the node $1 - i$, and the
value at $i > p$ is $0$. Thus the value at $0$ is $b_{-1}$ and the value at $k + 1$ is $b_k$. -/
noncomputable def adamsMoultonWeight (p : ℕ) (i : ℕ) : ℝ :=
  if h : i < p + 1 then adamsWeight (adamsMoultonNode p) ⟨i, h⟩ else 0

/-- The **Adams–Moulton method with $p$ steps**, (11.49) of [quarteroni2000numerical], case 2:
$$u_{n+1} = u_n + h \sum_{j=-1}^{p-1} b_j f_{n-j},$$
with the Adams weights of the nodes $t_{n+1}, t_n, \dots, t_{n-p+1}$, that is,
$s = 1, 0, \dots, -(p - 1)$. The method is implicit. `adamsMoulton 0` is backward Euler, with
the single node $t_{n+1}$ (the case $p = -1$ of the source), and `adamsMoulton 1` is
Crank–Nicolson.

The field `p` of the structure is $p - 1$, a natural subtraction, so that `adamsMoulton p` has
$p$ steps for $p \ge 1$ and one step for $p = 0$. -/
noncomputable def adamsMoulton (p : ℕ) : LinearMultistep :=
  ⟨p - 1, Pi.single 0 1, fun k => adamsMoultonWeight p (k + 1), adamsMoultonWeight p 0⟩

/-- For the Adams–Moulton method, $b_{-1} + \sum_k (-k)^i b_k = \sum_{l=0}^p x_l^i w_l$, the $i$-th
moment of the Adams weights $w$ over all $p + 1$ nodes $x_l = 1 - l$. -/
theorem adamsMoulton_bm1_add_sum (p i : ℕ) :
    (adamsMoulton p).bm1 + ∑ k : Fin ((adamsMoulton p).p + 1),
      (-(k : ℝ)) ^ i * (adamsMoulton p).b k =
      ∑ l : Fin (p + 1), adamsMoultonNode p l ^ i * adamsWeight (adamsMoultonNode p) l := by
  change adamsMoultonWeight p 0 +
    ∑ k : Fin (p - 1 + 1), (-(k : ℝ)) ^ i * adamsMoultonWeight p (k + 1) = _
  have hR : ∑ l : Fin (p + 1), adamsMoultonNode p l ^ i * adamsWeight (adamsMoultonNode p) l =
      ∑ n ∈ range (p + 1), (1 - (n : ℝ)) ^ i * adamsMoultonWeight p n := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n < p + 1 := Finset.mem_range.1 hn
    simp only [hn', dite_true, adamsMoultonWeight, adamsMoultonNode]
  have hL : ∑ k : Fin (p - 1 + 1), (-(k : ℝ)) ^ i * adamsMoultonWeight p (k + 1) =
      ∑ n ∈ range (p - 1 + 1), (-(n : ℝ)) ^ i * adamsMoultonWeight p (n + 1) :=
    Fin.sum_univ_eq_sum_range (fun n : ℕ => (-(n : ℝ)) ^ i * adamsMoultonWeight p (n + 1))
      (p - 1 + 1)
  rw [hR, hL, Finset.sum_range_succ' (fun n : ℕ => (1 - (n : ℝ)) ^ i * adamsMoultonWeight p n) p]
  simp only [Nat.cast_zero, sub_zero, one_pow, one_mul]
  rw [add_comm]
  refine congrArg (· + adamsMoultonWeight p 0) ?_
  rcases p with _ | p
  · simp [adamsMoultonWeight]
  · rw [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring_nf

/-- **The Adams–Moulton methods have order one more than their number of steps**
([quarteroni2000numerical], §11.5.1): `adamsMoulton p` has order $p + 1$. For $p \ge 1$ the
method has $p$ steps. The exception is `adamsMoulton 0`, backward Euler, which has one step and
order $1$. -/
theorem adamsMoulton_hasOrder (p : ℕ) : (adamsMoulton p).HasOrder (p + 1) := by
  rw [hasOrder_iff]
  intro i hi
  rcases i with _ | i
  · exact (adamsMoulton p).orderCondition_zero_of_a_single rfl
  · rw [(adamsMoulton p).orderCondition_succ_of_a_single rfl, adamsMoulton_bm1_add_sum,
      sum_pow_mul_adamsWeight (injective_adamsMoultonNode p) (by omega)]
    field_simp

/-- The Adams–Moulton methods satisfy the root condition. -/
theorem adamsMoulton_satisfiesRootCondition (p : ℕ) : (adamsMoulton p).SatisfiesRootCondition :=
  (adamsMoulton p).satisfiesRootCondition_of_a_single rfl

/-- **The Adams methods satisfy the root condition** ([quarteroni2000numerical], §11.6.3): for every
$p$, `adamsBashforth p` and `adamsMoulton p` satisfy the root condition.

For $a = e_0$ the polynomial $\rho(r) = r^{p+1} - r^p$ has the simple root $1$ and the root $0$
of multiplicity $p$. By `ODE.LinearMultistep.isZeroStable_of_satisfiesRootCondition`, the Adams
methods are therefore zero-stable for every field that is Lipschitz in the state. -/
theorem adams_satisfiesRootCondition (p : ℕ) :
    (adamsBashforth p).SatisfiesRootCondition ∧ (adamsMoulton p).SatisfiesRootCondition :=
  ⟨adamsBashforth_satisfiesRootCondition p, adamsMoulton_satisfiesRootCondition p⟩

/-- Let $w_0, \dots, w_p$ satisfy $\sum_i (1 - i)^m w_i = 1 / (m + 1)$ for all $m \le p$. Then the
Adams–Moulton weight at $i$ is $w_i$ for $i \le p$ and $0$ for $i > p$. -/
theorem adamsMoultonWeight_eq {p : ℕ} {w : Fin (p + 1) → ℝ}
    (hw : ∀ m < p + 1, ∑ i, adamsMoultonNode p i ^ m * w i = 1 / (m + 1)) (i : ℕ) :
    adamsMoultonWeight p i = if h : i < p + 1 then w ⟨i, h⟩ else 0 := by
  rw [adamsMoultonWeight, ← eq_adamsWeight_of_moments (injective_adamsMoultonNode p) hw]

/-- **Backward Euler is the Adams–Moulton method with the single node $t_{n+1}$**
([quarteroni2000numerical], §11.5.1): `adamsMoulton 0 = ofOneStep 1 0 1`. -/
theorem adamsMoulton_zero_eq : adamsMoulton 0 = ofOneStep 1 0 1 := by
  have hw := adamsMoultonWeight_eq (p := 0) (w := ![1]) fun m hm => by
    rw [Nat.lt_one_iff.1 hm]; simp
  change (⟨0, Pi.single 0 1, fun k => adamsMoultonWeight 0 (k + 1), adamsMoultonWeight 0 0⟩ :
    LinearMultistep) = _
  unfold ofOneStep
  simp only [hw]
  congr 1 <;> (funext j; fin_cases j; simp)

/-- **Crank–Nicolson is the Adams–Moulton method with one step** ([quarteroni2000numerical],
§11.5.1): `adamsMoulton 1 = ofOneStep 1 (1/2) (1/2)`. -/
theorem adamsMoulton_one_eq : adamsMoulton 1 = ofOneStep 1 (1 / 2) (1 / 2) := by
  have hw := adamsMoultonWeight_eq (p := 1) (w := ![1 / 2, 1 / 2]) fun m hm => by
    interval_cases m <;> simp [Fin.sum_univ_succ, adamsMoultonNode] <;> norm_num
  change (⟨0, Pi.single 0 1, fun k => adamsMoultonWeight 1 (k + 1), adamsMoultonWeight 1 0⟩ :
    LinearMultistep) = _
  unfold ofOneStep
  simp only [hw]
  congr 1 <;> (funext j; fin_cases j; simp)

/-- **The Adams–Moulton method with two steps**, (11.51) of [quarteroni2000numerical]:
$$u_{n+1} = u_n + \frac{h}{12} (5 f_{n+1} + 8 f_n - f_{n-1}).$$
-/
theorem adamsMoulton_two_eq : adamsMoulton 2 = ⟨1, ![1, 0], ![8 / 12, -1 / 12], 5 / 12⟩ := by
  have hw := adamsMoultonWeight_eq (p := 2) (w := ![5 / 12, 8 / 12, -1 / 12]) fun m hm => by
    interval_cases m <;> simp [Fin.sum_univ_succ, adamsMoultonNode] <;> norm_num
  change (⟨1, Pi.single 0 1, fun k => adamsMoultonWeight 2 (k + 1), adamsMoultonWeight 2 0⟩ :
    LinearMultistep) = _
  simp only [hw]
  congr 1 <;> funext j <;> fin_cases j <;> simp

/-- **The Adams–Moulton method with three steps** ([quarteroni2000numerical], §11.5.1):
$$u_{n+1} = u_n + \frac{h}{24} (9 f_{n+1} + 19 f_n - 5 f_{n-1} + f_{n-2}).$$
-/
theorem adamsMoulton_three_eq :
    adamsMoulton 3 = ⟨2, ![1, 0, 0], ![19 / 24, -5 / 24, 1 / 24], 9 / 24⟩ := by
  have hw := adamsMoultonWeight_eq (p := 3) (w := ![9 / 24, 19 / 24, -5 / 24, 1 / 24])
    fun m hm => by interval_cases m <;> simp [Fin.sum_univ_succ, adamsMoultonNode] <;> norm_num
  change (⟨2, Pi.single 0 1, fun k => adamsMoultonWeight 3 (k + 1), adamsMoultonWeight 3 0⟩ :
    LinearMultistep) = _
  simp only [hw]
  congr 1 <;> funext j <;> fin_cases j <;> simp

/-- **The Adams–Moulton method with four steps** ([quarteroni2000numerical], §11.5.1):
$$u_{n+1} = u_n + \frac{h}{720} (251 f_{n+1} + 646 f_n - 264 f_{n-1} + 106 f_{n-2} - 19
  f_{n-3}).$$
-/
theorem adamsMoulton_four_eq :
    adamsMoulton 4 =
      ⟨3, ![1, 0, 0, 0], ![646 / 720, -264 / 720, 106 / 720, -19 / 720], 251 / 720⟩ := by
  have hw := adamsMoultonWeight_eq (p := 4)
    (w := ![251 / 720, 646 / 720, -264 / 720, 106 / 720, -19 / 720])
    fun m hm => by interval_cases m <;> simp [Fin.sum_univ_succ, adamsMoultonNode] <;> norm_num
  change (⟨3, Pi.single 0 1, fun k => adamsMoultonWeight 4 (k + 1), adamsMoultonWeight 4 0⟩ :
    LinearMultistep) = _
  simp only [hw]
  congr 1 <;> funext j <;> fin_cases j <;> simp

/-- **The error constants of the Adams–Moulton methods of orders 1 to 4** (Table 11.1 of
[quarteroni2000numerical], the column $C_{q+1}$): the Adams–Moulton method of order $q$,
`adamsMoulton (q - 1)`, has the error constant $C_{q+1}$ equal to $-1/2$, $-1/12$, $-1/24$ and
$-19/720$ for $q = 1, 2, 3, 4$.

The column of the table is indexed by the order of the method, not by its number of steps. -/
theorem adamsMoulton_errorConstant :
    (adamsMoulton 0).errorConstant 1 = -1 / 2 ∧ (adamsMoulton 1).errorConstant 2 = -1 / 12 ∧
      (adamsMoulton 2).errorConstant 3 = -1 / 24 ∧
      (adamsMoulton 3).errorConstant 4 = -19 / 720 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [adamsMoulton_zero_eq]
    unfold errorConstant taylorCoeff ofOneStep
    norm_num [Fin.sum_univ_succ, Nat.factorial]
  · rw [adamsMoulton_one_eq]
    unfold errorConstant taylorCoeff ofOneStep
    norm_num [Fin.sum_univ_succ, Nat.factorial]
  · rw [adamsMoulton_two_eq]
    unfold errorConstant taylorCoeff
    norm_num [Fin.sum_univ_succ, Nat.factorial]
  · rw [adamsMoulton_three_eq]
    unfold errorConstant taylorCoeff
    norm_num [Fin.sum_univ_succ, Nat.factorial]

end AdamsMoulton

/-! ### The BDF methods -/

section BDF

/-- The **backward differentiation formulae** of Table 11.2 of [quarteroni2000numerical]: for
$p = 0, \dots, 5$, the implicit method with $p + 1$ steps
$$u_{n+1} = \sum_{j=0}^p a_j u_{n-j} + h b_{-1} f_{n+1},$$
with $b_0 = \dots = b_p = 0$ and the coefficients of the table. `bdf 0` is backward Euler.

The table prints $b_{-1} = 60/137$ in the row $p = 5$. This is a misprint: with it the order
condition $1$ fails. The definition uses $b_{-1} = 60/147$. -/
noncomputable def bdf : Fin 6 → LinearMultistep :=
  ![⟨0, ![1], ![0], 1⟩,
    ⟨1, ![4 / 3, -1 / 3], 0, 2 / 3⟩,
    ⟨2, ![18 / 11, -9 / 11, 2 / 11], 0, 6 / 11⟩,
    ⟨3, ![48 / 25, -36 / 25, 16 / 25, -3 / 25], 0, 12 / 25⟩,
    ⟨4, ![300 / 137, -300 / 137, 200 / 137, -75 / 137, 12 / 137], 0, 60 / 137⟩,
    ⟨5, ![360 / 147, -450 / 147, 400 / 147, -225 / 147, 72 / 147, -10 / 147], 0, 60 / 147⟩]

/-- `bdf 0` is backward Euler: `bdf 0 = ofOneStep 1 0 1`. -/
theorem bdf_zero_eq : bdf 0 = ofOneStep 1 0 1 := rfl

/-- The BDF method with two steps is $u_{n+1} = \frac{4}{3} u_n - \frac{1}{3} u_{n-1} + \frac{2}{3}
h f_{n+1}$. -/
theorem bdf_one_eq : bdf 1 = ⟨1, ![4 / 3, -1 / 3], 0, 2 / 3⟩ := rfl

/-- The BDF method with three steps is $u_{n+1} = \frac{18}{11} u_n - \frac{9}{11} u_{n-1} +
\frac{2}{11} u_{n-2} + \frac{6}{11} h f_{n+1}$. -/
theorem bdf_two_eq : bdf 2 = ⟨2, ![18 / 11, -9 / 11, 2 / 11], 0, 6 / 11⟩ := rfl

/-- The BDF method with four steps is $u_{n+1} = \frac{1}{25} (48 u_n - 36 u_{n-1} + 16 u_{n-2} - 3
u_{n-3}) + \frac{12}{25} h f_{n+1}$. -/
theorem bdf_three_eq : bdf 3 = ⟨3, ![48 / 25, -36 / 25, 16 / 25, -3 / 25], 0, 12 / 25⟩ := rfl

/-- The BDF method with five steps is $u_{n+1} = \frac{1}{137} (300 u_n - 300 u_{n-1} + 200
u_{n-2} - 75 u_{n-3} + 12 u_{n-4}) + \frac{60}{137} h f_{n+1}$. -/
theorem bdf_four_eq :
    bdf 4 = ⟨4, ![300 / 137, -300 / 137, 200 / 137, -75 / 137, 12 / 137], 0, 60 / 137⟩ := rfl

/-- The BDF method with six steps is $u_{n+1} = \frac{1}{147} (360 u_n - 450 u_{n-1} + 400 u_{n-2} -
225 u_{n-3} + 72 u_{n-4} - 10 u_{n-5}) + \frac{60}{147} h f_{n+1}$, with $b_{-1} = 60/147$. -/
theorem bdf_five_eq :
    bdf 5 = ⟨5, ![360 / 147, -450 / 147, 400 / 147, -225 / 147, 72 / 147, -10 / 147], 0,
      60 / 147⟩ := rfl

/-- **The BDF method with $k + 1$ steps has order $k + 1$** ([quarteroni2000numerical], §11.5.2),
for $k = 0, \dots, 5$.

The order conditions are identities between rational numbers. -/
theorem bdf_hasOrder (k : Fin 6) : (bdf k).HasOrder (k + 1) := by
  fin_cases k
  · change (ofOneStep 1 0 1).HasOrder 1
    rw [hasOrder_iff]
    intro i hi
    unfold orderCondition ofOneStep
    interval_cases i <;> simp
  · change (⟨1, ![4 / 3, -1 / 3], 0, 2 / 3⟩ : LinearMultistep).HasOrder 2
    rw [hasOrder_iff]
    intro i hi
    unfold orderCondition
    interval_cases i <;> simp [Fin.sum_univ_succ] <;> norm_num
  · change (⟨2, ![18 / 11, -9 / 11, 2 / 11], 0, 6 / 11⟩ : LinearMultistep).HasOrder 3
    rw [hasOrder_iff]
    intro i hi
    unfold orderCondition
    interval_cases i <;> simp [Fin.sum_univ_succ] <;> norm_num
  · change (⟨3, ![48 / 25, -36 / 25, 16 / 25, -3 / 25], 0, 12 / 25⟩ : LinearMultistep).HasOrder 4
    rw [hasOrder_iff]
    intro i hi
    unfold orderCondition
    interval_cases i <;> simp [Fin.sum_univ_succ] <;> norm_num
  · change (⟨4, ![300 / 137, -300 / 137, 200 / 137, -75 / 137, 12 / 137], 0, 60 / 137⟩ :
      LinearMultistep).HasOrder 5
    rw [hasOrder_iff]
    intro i hi
    unfold orderCondition
    interval_cases i <;> simp [Fin.sum_univ_succ] <;> norm_num
  · change (⟨5, ![360 / 147, -450 / 147, 400 / 147, -225 / 147, 72 / 147, -10 / 147], 0,
      60 / 147⟩ : LinearMultistep).HasOrder 6
    rw [hasOrder_iff]
    intro i hi
    unfold orderCondition
    interval_cases i <;> simp [Fin.sum_univ_succ] <;> norm_num

/-- The first characteristic polynomial of the BDF method with two steps, read in $\mathbb{C}[r]$,
is $r^2 - \frac{4}{3} r + \frac{1}{3} = (r - 1)(r - \frac{1}{3})$. -/
theorem rho_bdf_one_map : (bdf 1).rho.map (algebraMap ℝ ℂ) = (X - C 1) * (X - C (1 / 3)) := by
  rw [bdf_one_eq]
  unfold rho
  apply Polynomial.funext
  intro z
  simp [Fin.sum_univ_succ]
  ring

/-- The first characteristic polynomial of the BDF method with three steps, read in $\mathbb{C}[r]$,
is
$$r^3 - \frac{18}{11} r^2 + \frac{9}{11} r - \frac{2}{11} = (r - 1)(r - r_+)(r - r_-),
  \qquad r_\pm = \frac{7}{22} \pm \frac{\sqrt{39}}{22} i.$$
-/
theorem rho_bdf_two_map : (bdf 2).rho.map (algebraMap ℝ ℂ) =
    (X - C 1) * ((X - C (7 / 22 + (Real.sqrt 39 / 22 : ℝ) * Complex.I)) *
      (X - C (7 / 22 - (Real.sqrt 39 / 22 : ℝ) * Complex.I))) := by
  rw [bdf_two_eq]
  unfold rho
  have hsq : ((Real.sqrt 39 : ℝ) : ℂ) ^ 2 = 39 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  apply Polynomial.funext
  intro z
  simp [Fin.sum_univ_succ]
  linear_combination ((z - 1) / 484) * (39 * Complex.I_sq + Complex.I ^ 2 * hsq)

/-- **The BDF methods with at most three steps satisfy the root condition**
([quarteroni2000numerical], §11.6.3, which states that the BDF methods are zero-stable for
$p \le 5$): if $k \le 2$, then `bdf k` satisfies the root condition.

The polynomials $\rho$ are $r - 1$, $(r - 1)(r - 1/3)$ and
$(r - 1)(r^2 - \frac{7}{11} r + \frac{2}{11})$. The complex roots $7/22 \pm i\sqrt{39}/22$ of
the last factor have modulus $\sqrt{2/11} < 1$. The cases $k = 3, 4, 5$ need the location of the
roots of a cubic, a quartic and a quintic; they are in
`ODE.LinearMultistep.bdf_satisfiesRootCondition_all`. -/
theorem bdf_satisfiesRootCondition (k : Fin 6) (hk : k ≤ 2) : (bdf k).SatisfiesRootCondition := by
  classical
  fin_cases k
  · exact (bdf 0).satisfiesRootCondition_of_p_eq_zero rfl (by
      rw [bdf_zero_eq, orderCondition_zero]; unfold ofOneStep; simp)
  · change (bdf 1).SatisfiesRootCondition
    rw [SatisfiesRootCondition, rho_bdf_one_map]
    exact Polynomial.satisfiesRootCondition_X_sub_C_mul_X_sub_C (by norm_num) (by simp)
      (by norm_num)
  · change (bdf 2).SatisfiesRootCondition
    rw [SatisfiesRootCondition, rho_bdf_two_map]
    set rp : ℂ := 7 / 22 + (Real.sqrt 39 / 22 : ℝ) * Complex.I with hrp
    set rm : ℂ := 7 / 22 - (Real.sqrt 39 / 22 : ℝ) * Complex.I with hrm
    have hsq : (Real.sqrt 39 : ℝ) ^ 2 = 39 := Real.sq_sqrt (by norm_num)
    have hne : ((X - C 1) * ((X - C rp) * (X - C rm)) : ℂ[X]) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero _) (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))
    have hne' : ((X - C rp) * (X - C rm) : ℂ[X]) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
    have hnorm : ‖rp‖ ^ 2 = 2 / 11 ∧ ‖rm‖ ^ 2 = 2 / 11 := by
      constructor <;>
      · rw [Complex.sq_norm, Complex.normSq_apply]
        simp [hrp, hrm]
        ring_nf
        rw [hsq]
        norm_num
    have hlt : ‖rp‖ < 1 ∧ ‖rm‖ < 1 := by
      constructor <;> nlinarith [hnorm.1, hnorm.2, norm_nonneg rp, norm_nonneg rm]
    have hroots : ((X - C 1) * ((X - C rp) * (X - C rm)) : ℂ[X]).roots = {1} + ({rp} + {rm}) := by
      rw [roots_mul hne, roots_mul hne', roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
    refine Polynomial.satisfiesRootCondition_of_roots hne ?_ ?_
    · intro r hr
      rw [hroots, Multiset.mem_add, Multiset.mem_add, Multiset.mem_singleton,
        Multiset.mem_singleton, Multiset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · simp
      · exact hlt.1.le
      · exact hlt.2.le
    · intro r hr h1
      rw [hroots, Multiset.mem_add, Multiset.mem_add, Multiset.mem_singleton,
        Multiset.mem_singleton, Multiset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hroots, Multiset.count_add, Multiset.count_add, Multiset.count_singleton_self,
          Multiset.count_singleton, Multiset.count_singleton]
        have hp' : (1 : ℂ) ≠ rp := fun h => by rw [← h] at hlt; simp at hlt
        have hm' : (1 : ℂ) ≠ rm := fun h => by rw [← h] at hlt; simp at hlt
        simp [hp', hm']
      · exact absurd h1 hlt.1.ne
      · exact absurd h1 hlt.2.ne
  all_goals exact absurd hk (by decide)

/-!
### Zero-stability of the BDF methods with four, five and six steps

For $p = 3, 4, 5$ the roots of $\rho$ other than $1$ are the roots of a cubic, a quartic and a
quintic without a closed form. The Schur–Cohn test of `Numlib.RingTheory.Polynomial.SchurCohn`
places them inside the unit disc. Each chain below applies the reduction
$Q \mapsto (a_n Q - a_0 Q^\sharp) / X$, with the greatest common divisor of the coefficients divided
out, down to a nonzero constant. Here $a_n$ and $a_0$ are the leading and the constant coefficient
of $Q$, and $Q^\sharp$ is $Q$ with its coefficients reversed. Every step satisfies $|a_0| < |a_n|$.
-/

/-- **The extra factor of $\rho$ for the BDF method with four steps is Schur stable**: every complex
root of $25 r^3 - 23 r^2 + 13 r - 3$ has modulus less than $1$.

The Schur–Cohn chain is $(25, -23, 13, -3) \to (77, -67, 32) \to (109, -67) \to (7392)$, where
each step divides out the greatest common divisor of the coefficients. -/
theorem isSchurStable_bdfFactor3 : Polynomial.IsSchurStable
    (C 25 * X ^ 3 + C (-23) * X ^ 2 + C 13 * X + C (-3)) := by
  have h3 : Polynomial.IsSchurCohnPair (C 7392) (C 7392) :=
    Polynomial.isSchurCohnPair_C (by norm_num)
  have h2 : Polynomial.IsSchurCohnPair
      (C 109 * X + C (-67))
      (C (-67) * X + C 109) :=
    h3.step (A := 109) (B := -67) (c := 1) (by norm_num) (by norm_num)
      (by simp only [map_ofNat, map_neg, map_one]; ring)
      (by simp only [map_ofNat, map_neg, map_one]; ring)
  have h1 : Polynomial.IsSchurCohnPair
      (C 77 * X ^ 2 + C (-67) * X + C 32)
      (C 32 * X ^ 2 + C (-67) * X + C 77) :=
    h2.step (A := 77) (B := 32) (c := 45) (by norm_num) (by norm_num)
      (by simp only [map_ofNat, map_neg]; ring)
      (by simp only [map_ofNat, map_neg]; ring)
  have h0 : Polynomial.IsSchurCohnPair
      (C 25 * X ^ 3 + C (-23) * X ^ 2 + C 13 * X + C (-3))
      (C (-3) * X ^ 3 + C 13 * X ^ 2 + C (-23) * X + C 25) :=
    h1.step (A := 25) (B := -3) (c := 8) (by norm_num) (by norm_num)
      (by simp only [map_ofNat, map_neg]; ring)
      (by simp only [map_ofNat, map_neg]; ring)
  exact h0.isSchurStable

/-- **The extra factor of $\rho$ for the BDF method with five steps is Schur stable**: every complex
root of $137 r^4 - 163 r^3 + 137 r^2 - 63 r + 12$ has modulus less than $1$.

The Schur–Cohn chain is
$$(137, -163, 137, -63, 12) \to (745, -863, 685, -267) \to (60467, -57505, 34988)
  \to (19091, -11501) \to (232193280).$$
-/
theorem isSchurStable_bdfFactor4 : Polynomial.IsSchurStable
    (C 137 * X ^ 4 + C (-163) * X ^ 3 + C 137 * X ^ 2 + C (-63) * X + C 12) := by
  have h4 : Polynomial.IsSchurCohnPair (C 232193280) (C 232193280) :=
    Polynomial.isSchurCohnPair_C (by norm_num)
  have h3 : Polynomial.IsSchurCohnPair
      (C 19091 * X + C (-11501))
      (C (-11501) * X + C 19091) :=
    h4.step (A := 19091) (B := -11501) (c := 1) (by norm_num) (by norm_num)
      (by simp only [map_ofNat, map_neg, map_one]; ring)
      (by simp only [map_ofNat, map_neg, map_one]; ring)
  have h2 : Polynomial.IsSchurCohnPair
      (C 60467 * X ^ 2 + C (-57505) * X + C 34988)
      (C 34988 * X ^ 2 + C (-57505) * X + C 60467) :=
    h3.step (A := 60467) (B := 34988) (c := 127395) (by norm_num) (by norm_num)
      (by simp only [map_ofNat, map_neg]; ring)
      (by simp only [map_ofNat, map_neg]; ring)
  have h1 : Polynomial.IsSchurCohnPair
      (C 745 * X ^ 3 + C (-863) * X ^ 2 + C 685 * X + C (-267))
      (C (-267) * X ^ 3 + C 685 * X ^ 2 + C (-863) * X + C 745) :=
    h2.step (A := 745) (B := -267) (c := 8) (by norm_num) (by norm_num)
      (by simp only [map_ofNat, map_neg]; ring)
      (by simp only [map_ofNat, map_neg]; ring)
  have h0 : Polynomial.IsSchurCohnPair
      (C 137 * X ^ 4 + C (-163) * X ^ 3 + C 137 * X ^ 2 + C (-63) * X + C 12)
      (C 12 * X ^ 4 + C (-63) * X ^ 3 + C 137 * X ^ 2 + C (-163) * X + C 137) :=
    h1.step (A := 137) (B := 12) (c := 25) (by norm_num) (by norm_num)
      (by simp only [map_ofNat, map_neg]; ring)
      (by simp only [map_ofNat, map_neg]; ring)
  exact h0.isSchurStable

/-- **The extra factor of $\rho$ for the BDF method with six steps is Schur stable**: every complex
root of $147 r^5 - 213 r^4 + 237 r^3 - 163 r^2 + 62 r - 10$ has modulus less than $1$.

The Schur–Cohn chain is
$$(147, -213, 237, -163, 62, -10) \to (21509, -30691, 33209, -21591, 6984)
  \to (2364919, -2910521, 2756347, -1428885)$$
$$\to (20637463, -17112857, 13713664) \to (413869, -206179) \to (128777769120).$$
-/
theorem isSchurStable_bdfFactor5 : Polynomial.IsSchurStable
    (C 147 * X ^ 5 + C (-213) * X ^ 4 + C 237 * X ^ 3 + C (-163) * X ^ 2 + C 62 * X +
      C (-10)) := by
  have h5 : Polynomial.IsSchurCohnPair (C 128777769120) (C 128777769120) :=
    Polynomial.isSchurCohnPair_C (by norm_num)
  have h4 : Polynomial.IsSchurCohnPair
      (C 413869 * X + C (-206179))
      (C (-206179) * X + C 413869) :=
    h5.step (A := 413869) (B := -206179) (c := 1) (by norm_num) (by norm_num)
      (by simp only [map_ofNat, map_neg, map_one]; ring)
      (by simp only [map_ofNat, map_neg, map_one]; ring)
  have h3 : Polynomial.IsSchurCohnPair
      (C 20637463 * X ^ 2 + C (-17112857) * X + C 13713664)
      (C 13713664 * X ^ 2 + C (-17112857) * X + C 20637463) :=
    h4.step (A := 20637463) (B := 13713664) (c := 574675317) (by norm_num) (by norm_num)
      (by simp only [map_ofNat, map_neg]; ring)
      (by simp only [map_ofNat, map_neg]; ring)
  have h2 : Polynomial.IsSchurCohnPair
      (C 2364919 * X ^ 3 + C (-2910521) * X ^ 2 + C 2756347 * X + C (-1428885))
      (C (-1428885) * X ^ 3 + C 2756347 * X ^ 2 + C (-2910521) * X + C 2364919) :=
    h3.step (A := 2364919) (B := -1428885) (c := 172072) (by norm_num) (by norm_num)
      (by simp only [map_ofNat, map_neg]; ring)
      (by simp only [map_ofNat, map_neg]; ring)
  have h1 : Polynomial.IsSchurCohnPair
      (C 21509 * X ^ 4 + C (-30691) * X ^ 3 + C 33209 * X ^ 2 + C (-21591) * X + C 6984)
      (C 6984 * X ^ 4 + C (-21591) * X ^ 3 + C 33209 * X ^ 2 + C (-30691) * X + C 21509) :=
    h2.step (A := 21509) (B := 6984) (c := 175) (by norm_num) (by norm_num)
      (by simp only [map_ofNat, map_neg]; ring)
      (by simp only [map_ofNat, map_neg]; ring)
  have h0 : Polynomial.IsSchurCohnPair
      (C 147 * X ^ 5 + C (-213) * X ^ 4 + C 237 * X ^ 3 + C (-163) * X ^ 2 + C 62 * X + C (-10))
      (C (-10) * X ^ 5 + C 62 * X ^ 4 + C (-163) * X ^ 3 + C 237 * X ^ 2 + C (-213) * X + C 147) :=
    h1.step (A := 147) (B := -10) (c := 1) (by norm_num) (by norm_num)
      (by simp only [map_ofNat, map_neg, map_one]; ring)
      (by simp only [map_ofNat, map_neg, map_one]; ring)
  exact h0.isSchurStable

/-- The first characteristic polynomial of the BDF method with four steps factors as $25 \rho(r) =
(r - 1)(25 r^3 - 23 r^2 + 13 r - 3)$. -/
theorem rho_bdf_three_factor : (bdf 3).rho =
    C (1 / 25) * ((X - C 1) * (C 25 * X ^ 3 + C (-23) * X ^ 2 + C 13 * X + C (-3))) := by
  rw [bdf_three_eq]
  unfold rho
  apply Polynomial.funext
  intro x
  simp [Fin.sum_univ_succ]
  ring

/-- The first characteristic polynomial of the BDF method with five steps factors as $137 \rho(r) =
(r - 1)(137 r^4 - 163 r^3 + 137 r^2 - 63 r + 12)$. -/
theorem rho_bdf_four_factor : (bdf 4).rho =
    C (1 / 137) * ((X - C 1) *
      (C 137 * X ^ 4 + C (-163) * X ^ 3 + C 137 * X ^ 2 + C (-63) * X + C 12)) := by
  rw [bdf_four_eq]
  unfold rho
  apply Polynomial.funext
  intro x
  simp [Fin.sum_univ_succ]
  ring

/-- The first characteristic polynomial of the BDF method with six steps factors as $147 \rho(r) =
(r - 1)(147 r^5 - 213 r^4 + 237 r^3 - 163 r^2 + 62 r - 10)$. -/
theorem rho_bdf_five_factor : (bdf 5).rho =
    C (1 / 147) * ((X - C 1) *
      (C 147 * X ^ 5 + C (-213) * X ^ 4 + C 237 * X ^ 3 + C (-163) * X ^ 2 + C 62 * X +
        C (-10))) := by
  rw [bdf_five_eq]
  unfold rho
  apply Polynomial.funext
  intro x
  simp [Fin.sum_univ_succ]
  ring

/-- **Every BDF method of Table 11.2 satisfies the root condition** ([quarteroni2000numerical],
§11.6.3): `bdf k` satisfies the root condition for $k = 0, \dots, 5$. The source states that the
BDF methods are zero-stable for $p \le 5$ and quotes this from Cryer without proof.

For $k \le 2$ this is `ODE.LinearMultistep.bdf_satisfiesRootCondition`. For $k = 3, 4, 5$,
$\rho$ factors as $c (r - 1) Q$ with $Q$ Schur stable
(`ODE.LinearMultistep.isSchurStable_bdfFactor3`, `ODE.LinearMultistep.isSchurStable_bdfFactor4`,
`ODE.LinearMultistep.isSchurStable_bdfFactor5`), and
`Polynomial.satisfiesRootCondition_of_isSchurStable` gives the root condition. -/
theorem bdf_satisfiesRootCondition_all (k : Fin 6) : (bdf k).SatisfiesRootCondition := by
  fin_cases k
  · exact bdf_satisfiesRootCondition _ (by decide)
  · exact bdf_satisfiesRootCondition _ (by decide)
  · exact bdf_satisfiesRootCondition _ (by decide)
  · exact Polynomial.satisfiesRootCondition_of_isSchurStable (by norm_num)
      isSchurStable_bdfFactor3 rho_bdf_three_factor
  · exact Polynomial.satisfiesRootCondition_of_isSchurStable (by norm_num)
      isSchurStable_bdfFactor4 rho_bdf_four_factor
  · exact Polynomial.satisfiesRootCondition_of_isSchurStable (by norm_num)
      isSchurStable_bdfFactor5 rho_bdf_five_factor

end BDF

/-! ### The midpoint and Simpson methods -/

section MidpointSimpson

/-- The **midpoint method**, (11.43) of [quarteroni2000numerical]: the explicit method with two
steps
$$u_{n+1} = u_{n-1} + 2h f_n,$$
that is, $a = (0, 1)$, $b = (2, 0)$ and $b_{-1} = 0$. -/
noncomputable def midpoint : LinearMultistep := ⟨1, ![0, 1], ![2, 0], 0⟩

/-- The **Simpson method**, (11.44) of [quarteroni2000numerical]: the implicit method with two steps
$$u_{n+1} = u_{n-1} + \frac{h}{3} (f_{n-1} + 4 f_n + f_{n+1}),$$
that is, $a = (0, 1)$, $b = (4/3, 1/3)$ and $b_{-1} = 1/3$. -/
noncomputable def simpson : LinearMultistep := ⟨1, ![0, 1], ![4 / 3, 1 / 3], 1 / 3⟩

/-- A sequence $u$ is an orbit of the midpoint method if and only if
$u_{n+2} = u_n + 2h f(t_{n+1}, u_{n+1})$ for every $n$. -/
theorem isOrbit_midpoint_iff {u : ℕ → E} :
    midpoint.IsOrbit f h t₀ u ↔
      ∀ n, u (n + 2) = u n + (2 * h) • f (node t₀ h (n + 1)) (u (n + 1)) := by
  rw [isOrbit_iff]
  change (∀ n, u (n + 1 + 1) = ∑ j : Fin 2, ![(0 : ℝ), 1] j • u (n + 1 - j) +
    h • ∑ j : Fin 2, ![(2 : ℝ), 0] j • f (node t₀ h (n + 1 - j)) (u (n + 1 - j)) +
    (h * 0) • f (node t₀ h (n + 1 + 1)) (u (n + 1 + 1))) ↔ _
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.sub_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_smul, one_smul, zero_add, add_zero,
    mul_zero, smul_smul, Nat.add_sub_cancel]
  exact forall_congr' fun n => by rw [mul_comm h 2]

/-- A sequence $u$ is an orbit of the Simpson method if and only if, for every $n$,
$$u_{n+2} = u_n + \frac{h}{3} \bigl( f(t_n, u_n) + 4 f(t_{n+1}, u_{n+1}) + f(t_{n+2}, u_{n+2})
  \bigr).$$
-/
theorem isOrbit_simpson_iff {u : ℕ → E} :
    simpson.IsOrbit f h t₀ u ↔ ∀ n, u (n + 2) = u n + (h / 3) •
      (f (node t₀ h n) (u n) + (4 : ℝ) • f (node t₀ h (n + 1)) (u (n + 1)) +
        f (node t₀ h (n + 2)) (u (n + 2))) := by
  rw [isOrbit_iff]
  change (∀ n, u (n + 1 + 1) = ∑ j : Fin 2, ![(0 : ℝ), 1] j • u (n + 1 - j) +
    h • ∑ j : Fin 2, ![(4 / 3 : ℝ), 1 / 3] j • f (node t₀ h (n + 1 - j)) (u (n + 1 - j)) +
    (h * (1 / 3)) • f (node t₀ h (n + 1 + 1)) (u (n + 1 + 1))) ↔ _
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.sub_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_smul, one_smul, zero_add,
    Nat.add_sub_cancel]
  refine forall_congr' fun n => ?_
  rw [show n + 1 + 1 = n + 2 from rfl]
  refine ⟨fun H => H.trans ?_, fun H => H.trans ?_⟩ <;> module

/-- The first characteristic polynomial of the midpoint method is $\rho(r) = r^2 - 1$. -/
theorem rho_midpoint : midpoint.rho = X ^ 2 - 1 := by
  unfold rho midpoint
  simp [Fin.sum_univ_succ]

/-- The second characteristic polynomial of the midpoint method is $\sigma(r) = 2r$. -/
theorem sigma_midpoint : midpoint.sigma = C 2 * X := by
  unfold sigma midpoint
  simp [Fin.sum_univ_succ]

/-- The first characteristic polynomial of the Simpson method is $\rho(r) = r^2 - 1$. -/
theorem rho_simpson : simpson.rho = X ^ 2 - 1 := by
  unfold rho simpson
  simp [Fin.sum_univ_succ]

/-- The second characteristic polynomial of the Simpson method is $\sigma(r) = (r^2 + 4r + 1) / 3$.
-/
theorem sigma_simpson : simpson.sigma = C (1 / 3) * X ^ 2 + C (4 / 3) * X + C (1 / 3) := by
  unfold sigma simpson
  simp [Fin.sum_univ_succ]
  ring

/-- **The midpoint method satisfies the root condition** ([quarteroni2000numerical], §11.6.3): the
roots of $\rho(r) = r^2 - 1$ are $\pm 1$, and both are simple. -/
theorem midpoint_satisfiesRootCondition : midpoint.SatisfiesRootCondition := by
  rw [SatisfiesRootCondition, rho_midpoint]
  exact Polynomial.satisfiesRootCondition_X_sq_sub_one

/-- **The Simpson method satisfies the root condition** ([quarteroni2000numerical], §11.6.3): the
roots of $\rho(r) = r^2 - 1$ are $\pm 1$, and both are simple. -/
theorem simpson_satisfiesRootCondition : simpson.SatisfiesRootCondition := by
  rw [SatisfiesRootCondition, rho_simpson]
  exact Polynomial.satisfiesRootCondition_X_sq_sub_one

/-- **The midpoint method has order $2$.** -/
theorem midpoint_hasOrder : midpoint.HasOrder 2 := by
  rw [hasOrder_iff]
  intro i hi
  unfold orderCondition midpoint
  interval_cases i <;> norm_num [Fin.sum_univ_succ]

/-- The midpoint method does not satisfy the order condition $3$, so it does not have order $3$. -/
theorem midpoint_not_orderCondition_three : ¬ midpoint.orderCondition 3 := by
  unfold orderCondition midpoint
  simp [Fin.sum_univ_succ]
  norm_num

/-- **The Simpson method has order $4$.** -/
theorem simpson_hasOrder : simpson.HasOrder 4 := by
  rw [hasOrder_iff]
  intro i hi
  unfold orderCondition simpson
  interval_cases i <;> norm_num [Fin.sum_univ_succ]

end MidpointSimpson


/-! ### Absolute stability -/

section AbsoluteStability

/-- The **complex linear recurrence of the method on the test equation** $y' = \lambda y$, (11.54)
of [quarteroni2000numerical], at $z = h\lambda$: the recurrence of order $p + 1$
$$u_{n+p+1} = \sum_{i=0}^p \frac{a_{p-i} + z b_{p-i}}{1 - z b_{-1}} u_{n+i}.$$

The coefficients follow the convention of Mathlib's `LinearRecurrence`. If $1 - z b_{-1} = 0$,
the scheme does not determine $u_{n+1}$; the division by zero then makes all coefficients $0$,
and the results below exclude this case. -/
noncomputable def toLinearRecurrence (z : ℂ) : LinearRecurrence ℂ :=
  ⟨M.p + 1, fun i => ((M.a (Fin.rev i) : ℂ) + z * M.b (Fin.rev i)) / (1 - z * M.bm1)⟩

/-- The complex recurrence of the method has order $p + 1$. -/
@[simp] theorem toLinearRecurrence_order (z : ℂ) : (M.toLinearRecurrence z).order = M.p + 1 := rfl

/-- Reindexing by $j = p - i$: for $g \colon \{0, \dots, p\} \to \mathbb{C}$ and a complex sequence
$w$,
$$\sum_{i=0}^p g_{p-i} w_{n+i} = \sum_{j=0}^p g_j w_{n+p-j}.$$
-/
theorem sum_rev_mul (g : Fin (M.p + 1) → ℂ) (w : ℕ → ℂ) (n : ℕ) :
    ∑ i : Fin (M.p + 1), g (Fin.rev i) * w (n + i) =
      ∑ j : Fin (M.p + 1), g j * w (n + M.p - j) := by
  rw [← Equiv.sum_comp Fin.revPerm (fun j => g j * w (n + M.p - j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply]
  congr 2
  have := Fin.val_rev i
  have := i.is_lt
  omega

/-- **The characteristic polynomial of the complex recurrence is $\Pi_z / (1 - z b_{-1})$**, from
(11.55) of [quarteroni2000numerical]. If $1 - z b_{-1} \neq 0$, then the characteristic
polynomial of `ODE.LinearMultistep.toLinearRecurrence z` is
$$(1 - z b_{-1})^{-1} \Pi_z,$$
so the two polynomials have the same roots. -/
theorem charPoly_toLinearRecurrence {z : ℂ} (hz : 1 - z * M.bm1 ≠ 0) :
    (M.toLinearRecurrence z).charPoly = C (1 - z * M.bm1)⁻¹ * M.charPoly z := by
  apply Polynomial.funext
  intro r
  have e : ∑ i : Fin (M.toLinearRecurrence z).order,
      (M.toLinearRecurrence z).coeffs i * r ^ (i : ℕ) =
      (∑ j : Fin (M.p + 1), ((M.a j : ℂ) + z * M.b j) * r ^ (M.p - j)) / (1 - z * M.bm1) := by
    rw [Finset.sum_div]
    have := M.sum_rev_mul (fun j => ((M.a j : ℂ) + z * M.b j) / (1 - z * M.bm1))
      (fun k => r ^ k) 0
    simp only [zero_add] at this
    rw [show (∑ i : Fin (M.toLinearRecurrence z).order,
      (M.toLinearRecurrence z).coeffs i * r ^ (i : ℕ)) = ∑ i : Fin (M.p + 1),
      (((M.a (Fin.rev i) : ℂ) + z * M.b (Fin.rev i)) / (1 - z * M.bm1)) * r ^ (i : ℕ) from rfl,
      this]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [LinearRecurrence.charPoly, eval_sub, eval_finsetSum, eval_monomial, one_mul]
  rw [e, toLinearRecurrence_order]
  simp only [charPoly, rho, sigma, eval_sub, eval_mul, eval_C, eval_map, eval₂_sub, eval₂_pow,
    eval₂_X, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_add, Complex.coe_algebraMap]
  have hS : ∑ j : Fin (M.p + 1), ((M.a j : ℂ) + z * M.b j) * r ^ (M.p - j) =
      ∑ j : Fin (M.p + 1), (M.a j : ℂ) * r ^ (M.p - j) +
        z * ∑ j : Fin (M.p + 1), (M.b j : ℂ) * r ^ (M.p - j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hS]
  field_simp
  ring

/-- If $1 - z b_{-1} \neq 0$, then the characteristic polynomial of the complex recurrence and
$\Pi_z$ have the same roots. -/
theorem isRoot_charPoly_toLinearRecurrence_iff {z : ℂ} (hz : 1 - z * M.bm1 ≠ 0) (r : ℂ) :
    (M.toLinearRecurrence z).charPoly.IsRoot r ↔ (M.charPoly z).IsRoot r := by
  rw [M.charPoly_toLinearRecurrence hz]
  simp [IsRoot, hz]

/-- **The method on the test equation is the complex recurrence**, (11.54) of
[quarteroni2000numerical]. Let $h$ be real, $\lambda \in \mathbb{C}$ and
$1 - h\lambda b_{-1} \neq 0$. A complex sequence is an orbit of the method for $y' = \lambda y$
with step $h$ from $t_0 = 0$ if and only if it solves the recurrence
`ODE.LinearMultistep.toLinearRecurrence (h * lam)`.

The test field is `ODE.OneStep.testField`. -/
theorem isOrbit_testField_iff {h : ℝ} {lam : ℂ} (hz : 1 - (h : ℂ) * lam * M.bm1 ≠ 0) {u : ℕ → ℂ} :
    M.IsOrbit (testField lam) h 0 u ↔ (M.toLinearRecurrence (h * lam)).IsSolution u := by
  rw [isOrbit_iff]
  simp only [LinearRecurrence.IsSolution]
  refine forall_congr' fun n => ?_
  rw [show ∑ i : Fin (M.toLinearRecurrence (h * lam)).order,
      (M.toLinearRecurrence (h * lam)).coeffs i * u (n + i) =
      ∑ j : Fin (M.p + 1), (((M.a j : ℂ) + (h * lam) * M.b j) / (1 - (h * lam) * M.bm1)) *
        u (n + M.p - j) from M.sum_rev_mul
          (fun j => ((M.a j : ℂ) + (h * lam) * M.b j) / (1 - (h * lam) * M.bm1)) u n,
    toLinearRecurrence_order, ← add_assoc]
  simp only [testField, Complex.real_smul, Complex.ofReal_mul]
  have e1 : ∑ j : Fin (M.p + 1), (M.b j : ℂ) * (lam * u (n + M.p - j)) =
      lam * ∑ j : Fin (M.p + 1), (M.b j : ℂ) * u (n + M.p - j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1]
  set A := ∑ j : Fin (M.p + 1), (M.a j : ℂ) * u (n + M.p - j) with hA
  set B := ∑ j : Fin (M.p + 1), (M.b j : ℂ) * u (n + M.p - j) with hB
  have e2 : ∑ j : Fin (M.p + 1),
      (((M.a j : ℂ) + (h * lam) * M.b j) / (1 - (h * lam) * M.bm1)) * u (n + M.p - j) =
      (A + h * lam * B) / (1 - h * lam * M.bm1) := by
    simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    congr 1
    simp only [hA, hB, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e2, eq_div_iff hz]
  constructor <;> intro H <;> linear_combination H

/-- The **region of absolute stability** $\mathcal{A}$ of the method, (11.26) of
[quarteroni2000numerical] for a multistep method: the set of $z \in \mathbb{C}$ with
$1 - z b_{-1} \neq 0$ such that every solution of the recurrence
`ODE.LinearMultistep.toLinearRecurrence z` tends to $0$.

The condition $1 - z b_{-1} \neq 0$ says that the scheme on $y' = \lambda y$, with
$z = h\lambda$, determines $u_{n+1}$. The decay of all solutions is absolute stability in the
sense of Definition 11.6 of the source. -/
def absStabilityRegion : Set ℂ :=
  {z | 1 - z * M.bm1 ≠ 0 ∧
    ∀ u : ℕ → ℂ, (M.toLinearRecurrence z).IsSolution u → Tendsto u atTop (𝓝 0)}

/-- **Absolute stability is the absolute root condition** ([quarteroni2000numerical], §11.6.4):
$z \in \mathcal{A}$ if and only if $1 - z b_{-1} \neq 0$ and every root $r$ of $\Pi_z$ satisfies
$|r| < 1$.

The proof uses `LinearRecurrence.forall_tendsto_zero_iff`. -/
theorem mem_absStabilityRegion_iff (z : ℂ) :
    z ∈ M.absStabilityRegion ↔
      1 - z * M.bm1 ≠ 0 ∧ ∀ r : ℂ, (M.charPoly z).IsRoot r → ‖r‖ < 1 := by
  simp only [absStabilityRegion, Set.mem_ofPred_eq]
  refine and_congr_right fun hz => ?_
  rw [LinearRecurrence.forall_tendsto_zero_iff]
  simp only [M.isRoot_charPoly_toLinearRecurrence_iff hz]

/-- **Absolute stability with step $h$ at $\lambda$ is membership of $h\lambda$ in $\mathcal{A}$**
(Definition 11.6 and (11.26) of [quarteroni2000numerical]). Let $h$ be real and
$\lambda \in \mathbb{C}$. Then $1 - h\lambda b_{-1} \neq 0$ and every orbit of the method for
$y' = \lambda y$ with step $h$ from $t_0 = 0$ tends to $0$, if and only if
$h\lambda \in \mathcal{A}$. -/
theorem isAbsStable_iff_mem {h : ℝ} (lam : ℂ) :
    (1 - (h : ℂ) * lam * M.bm1 ≠ 0 ∧
      ∀ u : ℕ → ℂ, M.IsOrbit (testField lam) h 0 u → Tendsto u atTop (𝓝 0)) ↔
      (h : ℂ) * lam ∈ M.absStabilityRegion := by
  simp only [absStabilityRegion, Set.mem_ofPred_eq]
  exact and_congr_right fun hz => forall_congr' fun u => by rw [M.isOrbit_testField_iff hz]

/-- The **absolute root condition** at $\lambda \in \mathbb{C}$, Definition 11.12 of
[quarteroni2000numerical]: there is $h_0 > 0$ such that for every $h \in (0, h_0]$ every root
$r$ of $\Pi_{h\lambda}$ satisfies $|r| < 1$. -/
def SatisfiesAbsRootCondition (lam : ℂ) : Prop :=
  ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioc 0 h₀, ∀ r : ℂ, (M.charPoly (h * lam)).IsRoot r → ‖r‖ < 1

/-- If $0 < h < 1 / (|\lambda| |b_{-1}| + 1)$, then $1 - h\lambda b_{-1} \neq 0$. -/
theorem one_sub_mul_bm1_ne_zero {h : ℝ} (lam : ℂ) (hh : 0 < h)
    (hh' : h < 1 / (‖lam‖ * |M.bm1| + 1)) : 1 - (h : ℂ) * lam * M.bm1 ≠ 0 := by
  intro h0
  have h1 : ‖(h : ℂ) * lam * M.bm1‖ = 1 := by
    have := congrArg norm (sub_eq_zero.1 h0)
    simpa using this.symm
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hh.le,
    Real.norm_eq_abs] at h1
  rw [lt_div_iff₀ (by positivity)] at hh'
  nlinarith [norm_nonneg lam, abs_nonneg M.bm1]

/-- **The absolute root condition is absolute stability for all small steps**
([quarteroni2000numerical], §11.6.4): the method satisfies the absolute root condition at
$\lambda$ if and only if there is $h_0 > 0$ such that $h\lambda \in \mathcal{A}$ for every
$h \in (0, h_0]$.

The condition $1 - h\lambda b_{-1} \neq 0$ in $\mathcal{A}$ holds automatically for small $h$,
by `ODE.LinearMultistep.one_sub_mul_bm1_ne_zero`. -/
theorem satisfiesAbsRootCondition_iff (lam : ℂ) :
    M.SatisfiesAbsRootCondition lam ↔
      ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h ∈ Ioc 0 h₀, (h : ℂ) * lam ∈ M.absStabilityRegion := by
  constructor
  · rintro ⟨h₀, hh₀, H⟩
    refine ⟨min h₀ (1 / (‖lam‖ * |M.bm1| + 1) / 2), by positivity, fun h hh => ?_⟩
    rw [mem_absStabilityRegion_iff]
    refine ⟨M.one_sub_mul_bm1_ne_zero lam hh.1 ?_, H h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩⟩
    have := hh.2.trans (min_le_right _ _)
    have hpos : 0 < 1 / (‖lam‖ * |M.bm1| + 1) := by positivity
    linarith
  · rintro ⟨h₀, hh₀, H⟩
    exact ⟨h₀, hh₀, fun h hh => ((M.mem_absStabilityRegion_iff _).1 (H h hh)).2⟩

/-- The method is **A-stable** if its region of absolute stability contains the open left
half-plane: every $z \in \mathbb{C}$ with $\operatorname{Re} z < 0$ lies in $\mathcal{A}$
([quarteroni2000numerical], §11.3.3 and §11.6.4). -/
def IsAStable : Prop := ∀ z : ℂ, z.re < 0 → z ∈ M.absStabilityRegion

/-- The method is **ϑ-stable** if its region of absolute stability contains the sector of the left
half-plane with half-angle $\vartheta$ about the negative real axis: every $z \neq 0$ with
$|\arg(-z)| < \vartheta$ lies in $\mathcal{A}$ ([quarteroni2000numerical], §11.6.4).

The source writes the sector as $-\vartheta < \pi - \arg z < \vartheta$. Here `Complex.arg`
takes values in $(-\pi, \pi]$. -/
def IsThetaStable (ϑ : ℝ) : Prop :=
  ∀ z : ℂ, z ≠ 0 → |Complex.arg (-z)| < ϑ → z ∈ M.absStabilityRegion

/-- An A-stable method is ϑ-stable for every $\vartheta \le \pi / 2$. -/
theorem IsAStable.isThetaStable (hA : M.IsAStable) {ϑ : ℝ} (hϑ : ϑ ≤ Real.pi / 2) :
    M.IsThetaStable ϑ := by
  intro z hz harg
  refine hA z ?_
  rcases Complex.abs_arg_lt_pi_div_two_iff.1 (harg.trans_le hϑ) with h | h
  · simpa using h
  · exact absurd (neg_eq_zero.1 h) hz

/-- The **region $\mathcal{A}^*$** of Remark 11.3 of [quarteroni2000numerical]: the set of
$z \in \mathbb{C}$ with $1 - z b_{-1} \neq 0$ such that every solution of the recurrence
`ODE.LinearMultistep.toLinearRecurrence z` is bounded. -/
def absStabilityRegionStar : Set ℂ :=
  {z | 1 - z * M.bm1 ≠ 0 ∧ ∀ u : ℕ → ℂ, (M.toLinearRecurrence z).IsSolution u →
    BddAbove (Set.range fun n => ‖u n‖)}

/-- **$\mathcal{A}^*$ is the root condition on $\Pi_z$** (Remark 11.3 of [quarteroni2000numerical],
through Lemma 11.3): $z \in \mathcal{A}^*$ if and only if $1 - z b_{-1} \neq 0$ and $\Pi_z$
satisfies the root condition. -/
theorem mem_absStabilityRegionStar_iff (z : ℂ) :
    z ∈ M.absStabilityRegionStar ↔
      1 - z * M.bm1 ≠ 0 ∧ (M.charPoly z).SatisfiesRootCondition := by
  simp only [absStabilityRegionStar, Set.mem_ofPred_eq]
  refine and_congr_right fun hz => ?_
  rw [LinearRecurrence.forall_bddAbove_iff_satisfiesRootCondition, M.charPoly_toLinearRecurrence hz,
    Polynomial.satisfiesRootCondition_C_mul_iff (inv_ne_zero hz)]

/-- The region of absolute stability is contained in $\mathcal{A}^*$: a sequence that tends to $0$
is bounded. -/
theorem absStabilityRegion_subset_star : M.absStabilityRegion ⊆ M.absStabilityRegionStar :=
  fun _ hz => ⟨hz.1, fun u hu => (hz.2 u hu).norm.bddAbove_range⟩

/-- **Zero-stable methods are those with $0 \in \mathcal{A}^*$** (Remark 11.3 of
[quarteroni2000numerical]): $0 \in \mathcal{A}^*$ if and only if the method satisfies the root
condition.

Since $\Pi_0 = \rho$, this follows from `ODE.LinearMultistep.mem_absStabilityRegionStar_iff`.
With Theorem 11.4 (`ODE.LinearMultistep.isZeroStable_iff_satisfiesRootCondition`), the condition
is zero-stability for every Lipschitz problem. -/
theorem zero_mem_absStabilityRegionStar_iff :
    (0 : ℂ) ∈ M.absStabilityRegionStar ↔ M.SatisfiesRootCondition := by
  rw [mem_absStabilityRegionStar_iff, charPoly_zero]
  simp [SatisfiesRootCondition]

/-- **The region of a one-step method.** For `ODE.LinearMultistep.ofOneStep a₀ b₀ bm1` and
$z \in \mathbb{C}$,
$$z \in \mathcal{A} \iff 1 - z b_{-1} \neq 0 \ \text{and} \
  \Bigl| \frac{a_0 + z b_0}{1 - z b_{-1}} \Bigr| < 1.$$
The quotient is the single root of $\Pi_z(r) = (1 - z b_{-1}) r - (a_0 + z b_0)$. -/
theorem mem_absStabilityRegion_ofOneStep_iff (a₀ b₀ bm1 : ℝ) (z : ℂ) :
    z ∈ (ofOneStep a₀ b₀ bm1).absStabilityRegion ↔
      1 - z * bm1 ≠ 0 ∧ ‖((a₀ : ℂ) + z * b₀) / (1 - z * bm1)‖ < 1 := by
  rw [mem_absStabilityRegion_iff]
  refine and_congr_right fun hz => ?_
  have hz' : (1 : ℂ) - z * bm1 ≠ 0 := hz
  have hroot : ∀ r : ℂ, ((ofOneStep a₀ b₀ bm1).charPoly z).IsRoot r ↔
      r = ((a₀ : ℂ) + z * b₀) / (1 - z * bm1) := by
    intro r
    rw [charPoly, rho_ofOneStep, sigma_ofOneStep, eq_div_iff hz']
    simp only [IsRoot, eval_sub, eval_mul, eval_C, eval_map, eval₂_sub, eval₂_add, eval₂_mul,
      eval₂_X, eval₂_C, Complex.coe_algebraMap]
    constructor <;> intro H <;> linear_combination H
  simp only [hroot, forall_eq]

/-- **The region of forward Euler as a multistep method** equals the region of
`ODE.OneStep.forwardEuler` in `Numlib.ODE.OneStep`, the disc $|1 + z| < 1$. -/
theorem absStabilityRegion_ofOneStep_forwardEuler :
    (ofOneStep 1 1 0).absStabilityRegion =
      OneStep.absStabilityRegion fun f => OneStep.ofIncrement (OneStep.forwardEuler f) := by
  ext z
  rw [mem_absStabilityRegion_ofOneStep_iff, OneStep.mem_absStabilityRegion_forwardEuler_iff]
  simp

/-- **The region of backward Euler as a multistep method** equals the region of
`ODE.OneStep.backwardEuler` in `Numlib.ODE.OneStep`, the set $|1 - z| > 1$. -/
theorem absStabilityRegion_ofOneStep_backwardEuler :
    (ofOneStep 1 0 1).absStabilityRegion =
      OneStep.absStabilityRegion fun f => OneStep.ofIncrement (OneStep.backwardEuler f) := by
  ext z
  rw [mem_absStabilityRegion_ofOneStep_iff, OneStep.mem_absStabilityRegion_backwardEuler_iff]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_zero, add_zero, mul_one, norm_div,
    norm_one]
  constructor
  · rintro ⟨hz, h⟩
    rwa [div_lt_one (norm_pos_iff.2 hz)] at h
  · intro h
    have hz : (1 : ℂ) - z ≠ 0 := norm_pos_iff.1 (by linarith)
    exact ⟨hz, (div_lt_one (norm_pos_iff.2 hz)).2 h⟩

/-- **The region of Crank–Nicolson as a multistep method** equals the region of
`ODE.OneStep.crankNicolson` in `Numlib.ODE.OneStep`, the open left half-plane. -/
theorem absStabilityRegion_ofOneStep_crankNicolson :
    (ofOneStep 1 (1 / 2) (1 / 2)).absStabilityRegion =
      OneStep.absStabilityRegion fun f => OneStep.ofIncrement (OneStep.crankNicolson f) := by
  ext z
  rw [mem_absStabilityRegion_ofOneStep_iff, OneStep.mem_absStabilityRegion_crankNicolson_iff]
  have e : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; rfl
  simp only [e, Complex.ofReal_one, mul_one_div]
  constructor
  · rintro ⟨hz, h⟩
    rw [norm_div, div_lt_one (norm_pos_iff.2 hz), ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
      Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.div_ofNat_re, Complex.div_ofNat_im, zero_add, zero_sub] at h
    nlinarith [h]
  · intro h
    have hz : (1 : ℂ) - z / 2 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    refine ⟨hz, ?_⟩
    rw [norm_div, div_lt_one (norm_pos_iff.2 hz), ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
      Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.div_ofNat_re, Complex.div_ofNat_im, zero_add, zero_sub]
    nlinarith [h]

/-- **Backward Euler is A-stable as a multistep method**: `ofOneStep 1 0 1`, which is `bdf 0`, is
A-stable. -/
theorem isAStable_ofOneStep_backwardEuler : (ofOneStep 1 0 1).IsAStable := by
  intro z hz
  rw [absStabilityRegion_ofOneStep_backwardEuler]
  exact OneStep.isAStable_backwardEuler z hz

/-- **Crank–Nicolson is A-stable as a multistep method**: `ofOneStep 1 (1/2) (1/2)`, which is
`adamsMoulton 1`, is A-stable. -/
theorem isAStable_ofOneStep_crankNicolson : (ofOneStep 1 (1 / 2) (1 / 2)).IsAStable := by
  intro z hz
  rw [absStabilityRegion_ofOneStep_crankNicolson]
  exact OneStep.isAStable_crankNicolson z hz

/-- **The regions of the one-step methods** ([quarteroni2000numerical], §11.6.4). As multistep
methods, forward Euler, backward Euler and Crank–Nicolson have the same regions of absolute
stability as the corresponding one-step methods of `Numlib.ODE.OneStep`. In particular backward
Euler (`bdf 0`) and Crank–Nicolson (`adamsMoulton 1`) are A-stable. -/
theorem absStabilityRegion_ofOneStep :
    ((ofOneStep 1 1 0).absStabilityRegion =
      OneStep.absStabilityRegion fun f => OneStep.ofIncrement (OneStep.forwardEuler f)) ∧
    ((ofOneStep 1 0 1).absStabilityRegion =
      OneStep.absStabilityRegion fun f => OneStep.ofIncrement (OneStep.backwardEuler f)) ∧
    ((ofOneStep 1 (1 / 2) (1 / 2)).absStabilityRegion =
      OneStep.absStabilityRegion fun f => OneStep.ofIncrement (OneStep.crankNicolson f)) ∧
    (bdf 0).IsAStable ∧ (adamsMoulton 1).IsAStable :=
  ⟨absStabilityRegion_ofOneStep_forwardEuler, absStabilityRegion_ofOneStep_backwardEuler,
    absStabilityRegion_ofOneStep_crankNicolson, by rw [bdf_zero_eq]; exact
    isAStable_ofOneStep_backwardEuler, by rw [adamsMoulton_one_eq]; exact
    isAStable_ofOneStep_crankNicolson⟩

/-- The characteristic polynomial of the midpoint method on the test equation is
$\Pi_z(r) = r^2 - 2zr - 1$. -/
theorem charPoly_midpoint (z : ℂ) : midpoint.charPoly z = X ^ 2 - C (2 * z) * X - 1 := by
  rw [charPoly, rho_midpoint, sigma_midpoint]
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one,
    Polynomial.map_mul, map_C, Complex.coe_algebraMap, Complex.ofReal_ofNat]
  rw [show (C (2 : ℂ)) = 2 from rfl, show C (2 * z) = C 2 * C z by rw [C_mul],
    show (C (2 : ℂ)) = 2 from rfl]
  ring

/-- **The midpoint method has an empty region of absolute stability** (Remark 11.3 of
[quarteroni2000numerical]).

The roots of $r^2 - 2zr - 1$ have the product $-1$, so they cannot both lie in the open unit
disc. -/
theorem absStabilityRegion_midpoint_eq_empty : midpoint.absStabilityRegion = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_absStabilityRegion_iff, charPoly_midpoint]
  rintro ⟨-, H⟩
  -- a root `r₁`, and `-1/r₁` is the other root
  obtain ⟨r, hr⟩ := Complex.exists_root (f := X ^ 2 - C (2 * z) * X - 1) (by
    rw [show (X ^ 2 - C (2 * z) * X - 1 : ℂ[X]) = C 1 * X ^ 2 + C (-(2 * z)) * X + C (-1) by
      simp only [map_one, map_neg, one_mul]; ring, degree_quadratic one_ne_zero]
    norm_num)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp [IsRoot] at hr
  have hr' : (X ^ 2 - C (2 * z) * X - 1 : ℂ[X]).IsRoot (-1 / r) := by
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one] at hr ⊢
    have : (-1 / r) ^ 2 - 2 * z * (-1 / r) - 1 = -(r ^ 2 - 2 * z * r - 1) / r ^ 2 := by
      field_simp
      ring
    rw [this, hr]
    simp
  have h1 := H r hr
  have h2 := H _ hr'
  rw [norm_div, norm_neg, norm_one, div_lt_one (norm_pos_iff.2 hr0)] at h2
  linarith

end AbsoluteStability


/-! ### Padding a method to more steps -/

section Pad

/-- **Padding** a method with $p + 1$ steps to $q + 1 \ge p + 1$ steps: the method with the
coefficients $a_j$ and $b_j$ for $j \le p$, the coefficients $a_j = b_j = 0$ for $p < j \le q$,
and the same $b_{-1}$. It defines the same scheme, read as a method with more steps.

This is the convention of [quarteroni2000numerical], §11.7, after Example 11.8, for the
corrector of a predictor–corrector pair. -/
def pad (q : ℕ) (_hq : M.p ≤ q) : LinearMultistep :=
  ⟨q, fun i => if h : (i : ℕ) < M.p + 1 then M.a ⟨i, h⟩ else 0,
    fun i => if h : (i : ℕ) < M.p + 1 then M.b ⟨i, h⟩ else 0, M.bm1⟩

/-- The padded method has $q + 1$ steps: its field `p` is $q$. -/
@[simp] theorem pad_p (q : ℕ) (hq : M.p ≤ q) : (M.pad q hq).p = q := rfl

/-- The padded method has the same coefficient $b_{-1}$. -/
@[simp] theorem pad_bm1 (q : ℕ) (hq : M.p ≤ q) : (M.pad q hq).bm1 = M.bm1 := rfl

/-- Padding a coefficient vector by zeros multiplies its polynomial by a power of $X$: for
$p \le q$, $X^{q-p} \sum_{j \le p} c_j X^{p-j} = \sum_{i \le q} c'_i X^{q-i}$, where $c'$ is $c$
extended by zeros. -/
private theorem X_pow_mul_sum_eq_sum_pad {p q : ℕ} (hq : p ≤ q) (c : Fin (p + 1) → ℝ) :
    X ^ (q - p) * ∑ j : Fin (p + 1), C (c j) * X ^ (p - j)
      = ∑ i : Fin (q + 1), C (if h : (i : ℕ) < p + 1 then c ⟨i, h⟩ else 0) * X ^ (q - i) := by
  rw [Finset.mul_sum, Finset.sum_congr rfl fun j _ => show X ^ (q - p) * (C (c j) * X ^ (p - j)) =
      C (c j) * X ^ (q - j) by
    have := j.is_lt
    rw [mul_left_comm, ← pow_add, show q - p + (p - j) = q - j by omega],
    ← Fin.sum_dite_lt (Nat.succ_le_succ hq) fun j => C (c j) * X ^ (q - j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> first | rfl | simp

/-- The first characteristic polynomial of the method padded to $q + 1$ steps is $X^{q-p} \rho$. -/
theorem rho_pad (q : ℕ) (hq : M.p ≤ q) : (M.pad q hq).rho = X ^ (q - M.p) * M.rho := by
  unfold rho pad
  dsimp only
  rw [mul_sub, ← pow_add, show q - M.p + (M.p + 1) = q + 1 by omega,
    X_pow_mul_sum_eq_sum_pad hq]

/-- The second characteristic polynomial of the method padded to $q + 1$ steps is $X^{q-p} \sigma$.
-/
theorem sigma_pad (q : ℕ) (hq : M.p ≤ q) : (M.pad q hq).sigma = X ^ (q - M.p) * M.sigma := by
  unfold sigma pad
  dsimp only
  rw [mul_add, mul_left_comm (X ^ (q - M.p)) (C M.bm1), ← pow_add,
    show q - M.p + (M.p + 1) = q + 1 by omega, X_pow_mul_sum_eq_sum_pad hq]

/-- Padding an Adams-type method gives an Adams-type method: if $a = e_0$, then the padded method
also has $a = e_0$. -/
theorem pad_a_single (q : ℕ) (hq : M.p ≤ q) (ha : M.a = Pi.single 0 1) :
    (M.pad q hq).a = Pi.single 0 1 := by
  change (fun i : Fin (q + 1) => if h : (i : ℕ) < M.p + 1 then M.a ⟨i, h⟩ else 0) =
    Pi.single (0 : Fin (q + 1)) (1 : ℝ)
  funext i
  rw [ha]
  by_cases hi : (i : ℕ) < M.p + 1
  · simp only [hi, ↓reduceDIte]
    by_cases h0 : (i : ℕ) = 0
    · have : i = 0 := Fin.ext h0
      subst this
      simp
    · rw [Pi.single_eq_of_ne (fun h => h0 (by simpa using congrArg Fin.val h)),
        Pi.single_eq_of_ne (fun h => h0 (by rw [h, Fin.val_zero]))]
  · simp only [hi, ↓reduceDIte]
    rw [Pi.single_eq_of_ne]
    intro h
    rw [h] at hi
    simp at hi

end Pad

end LinearMultistep

/-! ### Predictor–corrector methods -/

/-- A **predictor–corrector pair** ([quarteroni2000numerical], §11.7) consists of a predictor with
the coefficients $\tilde a_j$ and $\tilde b_j$, a corrector with the coefficients $a_j$, $b_j$
and $b_{-1}$, both with $p + 1$ steps, and a number $m$ of corrections per step. The predictor
is explicit.

A corrector with fewer steps is padded with zeros (`ODE.LinearMultistep.pad`), as the source
does after Example 11.8. The number $m$ is any natural number; the source has $m \ge 1$. -/
structure PredictorCorrector where
  /-- The number $p$; the pair has the $p + 1$ steps of the predictor. -/
  p : ℕ
  /-- The coefficients $\tilde a_0, \dots, \tilde a_p$ of the predictor. -/
  pa : Fin (p + 1) → ℝ
  /-- The coefficients $\tilde b_0, \dots, \tilde b_p$ of the predictor. -/
  pb : Fin (p + 1) → ℝ
  /-- The coefficients $a_0, \dots, a_p$ of the corrector. -/
  a : Fin (p + 1) → ℝ
  /-- The coefficients $b_0, \dots, b_p$ of the corrector. -/
  b : Fin (p + 1) → ℝ
  /-- The coefficient $b_{-1}$ of the corrector. -/
  bm1 : ℝ
  /-- The number $m$ of corrections per step. -/
  m : ℕ

namespace PredictorCorrector

variable (PC : PredictorCorrector) {f : ℝ → E → E} {h t₀ T : ℝ}

/-- The predictor as a linear multistep method: the coefficients $\tilde a$ and $\tilde b$, with
$b_{-1} = 0$. -/
def toPredictor : LinearMultistep := ⟨PC.p, PC.pa, PC.pb, 0⟩

/-- The corrector as a linear multistep method: the coefficients $a$, $b$ and $b_{-1}$. -/
def toCorrector : LinearMultistep := ⟨PC.p, PC.a, PC.b, PC.bm1⟩

/-- **The pair of two methods** ([quarteroni2000numerical], §11.7): for methods $P$ and $C$ such
that $C$ has at most as many steps as $P$, the pair with the predictor $P$, the corrector $C$
padded to the steps of $P$, and $m$ corrections.

The coefficient $b_{-1}$ of $P$ is dropped, so the predictor of the pair is explicit. -/
def ofPair (P C : LinearMultistep) (hpc : C.p ≤ P.p) (m : ℕ) : PredictorCorrector :=
  ⟨P.p, P.a, P.b, (C.pad P.p hpc).a, (C.pad P.p hpc).b, C.bm1, m⟩

/-- If the method $P$ is explicit, then the predictor of the pair of $P$ and $C$ is $P$. -/
theorem toPredictor_ofPair (P C : LinearMultistep) (hpc : C.p ≤ P.p) (m : ℕ) (hP : P.bm1 = 0) :
    (ofPair P C hpc m).toPredictor = P := by
  obtain ⟨p, a, b, bm1⟩ := P
  simp only at hP
  subst hP
  rfl

/-- The corrector of the pair of $P$ and $C$ is $C$ padded to the steps of $P$. -/
theorem toCorrector_ofPair (P C : LinearMultistep) (hpc : C.p ≤ P.p) (m : ℕ) :
    (ofPair P C hpc m).toCorrector = C.pad P.p hpc := rfl

/-- **One correction** ([quarteroni2000numerical], §11.7, the step $[C]$). Given the history sum
$G = \sum_j a_j u_{n-j} + h \sum_j b_j f_{n-j}$ and the current value $v = u^{(k)}_{n+1}$, the
corrected value is
$$u^{(k+1)}_{n+1} = G + h b_{-1} f(t_{n+1}, v),$$
with $t = t_n$ and $t_{n+1} = t + h$. -/
def correct (f : ℝ → E → E) (h t : ℝ) (G v : E) : E := G + (h * PC.bm1) • f (t + h) v

/-- **The predicted value** ([quarteroni2000numerical], (11.69), the step $[P]$): from the history
values $u_{n-j}$ and the history function values $f_{n-j}$, $j = 0, \dots, p$,
$$u^{(0)}_{n+1} = \sum_{j=0}^p \tilde a_j u_{n-j} + h \sum_{j=0}^p \tilde b_j f_{n-j}.$$
-/
def predict (h : ℝ) (uh fh : Fin (PC.p + 1) → E) : E :=
  ∑ j, PC.pa j • uh j + h • ∑ j, PC.pb j • fh j

/-- The history sum of the corrector, $G = \sum_{j=0}^p a_j u_{n-j} + h \sum_{j=0}^p b_j f_{n-j}$,
from the history values $u_{n-j}$ and the history function values $f_{n-j}$. -/
def historySum (h : ℝ) (uh fh : Fin (PC.p + 1) → E) : E :=
  ∑ j, PC.a j • uh j + h • ∑ j, PC.b j • fh j

/-- **The $P(EC)^m$ step**, (11.69) of [quarteroni2000numerical], at $t = t_n$. The input is the
history $u^{(m)}_{n-j}$ of values and the history $f^{(m-1)}_{n-j}$ of function values,
$j = 0, \dots, p$. The output is the pair $(u^{(m)}_{n+1}, f^{(m-1)}_{n+1})$: the corrections
$u^{(k+1)}_{n+1} = G + h b_{-1} f(t_{n+1}, u^{(k)}_{n+1})$ are applied $m$ times to the
predicted value $u^{(0)}_{n+1}$, and $f^{(m-1)}_{n+1} = f(t_{n+1}, u^{(m-1)}_{n+1})$.

For $m = 0$ the natural subtraction gives $m - 1 = 0$, so the step returns the predicted value
and $f$ at the predicted value. -/
noncomputable def pecStep (f : ℝ → E → E) (h t : ℝ) (uh fh : Fin (PC.p + 1) → E) : E × E :=
  ((PC.correct f h t (PC.historySum h uh fh))^[PC.m] (PC.predict h uh fh),
    f (t + h) ((PC.correct f h t (PC.historySum h uh fh))^[PC.m - 1] (PC.predict h uh fh)))

/-- **The $P(EC)^m E$ step** ([quarteroni2000numerical], §11.7) at $t = t_n$. The input is the
history $u^{(m)}_{n-j}$, $j = 0, \dots, p$. The function values are recomputed from the
corrected values, $f_{n-j} = f(t_{n-j}, u^{(m)}_{n-j})$. The output is $u^{(m)}_{n+1}$, the
predicted value corrected $m$ times. -/
noncomputable def peceStep (f : ℝ → E → E) (h t : ℝ) (uh : Fin (PC.p + 1) → E) : E :=
  (PC.correct f h t (PC.historySum h uh fun j => f (t - j * h) (uh j)))^[PC.m]
    (PC.predict h uh fun j => f (t - j * h) (uh j))

/-- An **orbit of the $P(EC)^m$ scheme** is a pair of sequences $u = u^{(m)}$ and $f^{(m-1)}$ such
that, for every $n \ge p$, the pair $(u_{n+1}, f^{(m-1)}_{n+1})$ is the $P(EC)^m$ step at $t_n$
from the histories $u_{n-j}$ and $f^{(m-1)}_{n-j}$.

The second sequence is the argument `fv`. -/
def IsOrbitPEC (f : ℝ → E → E) (h t₀ : ℝ) (u fv : ℕ → E) : Prop :=
  ∀ n, (u (n + PC.p + 1), fv (n + PC.p + 1)) =
    PC.pecStep f h (node t₀ h (n + PC.p)) (fun j => u (n + PC.p - j)) fun j => fv (n + PC.p - j)

/-- An **orbit of the $P(EC)^m E$ scheme** is a sequence $u = u^{(m)}$ such that, for every
$n \ge p$, $u_{n+1}$ is the $P(EC)^m E$ step at $t_n$ from the history $u_{n-j}$. -/
def IsOrbitPECE (f : ℝ → E → E) (h t₀ : ℝ) (u : ℕ → E) : Prop :=
  ∀ n, u (n + PC.p + 1) = PC.peceStep f h (node t₀ h (n + PC.p)) fun j => u (n + PC.p - j)

/-- **Heun's method is the $P(EC)E$ scheme of forward Euler and Crank–Nicolson** (Example 11.8 of
[quarteroni2000numerical]): the $P(EC)E$ orbits of the pair with predictor `ofOneStep 1 1 0`,
corrector `ofOneStep 1 (1/2) (1/2)` and $m = 1$ are the orbits of Heun's method
`ODE.OneStep.heun`.

In the $P(EC)$ scheme the stored function values are those of the predicted values, and that
scheme is not Heun's method. -/
theorem heun_eq_pece {u : ℕ → E} :
    (ofPair (LinearMultistep.ofOneStep 1 1 0) (LinearMultistep.ofOneStep 1 (1 / 2) (1 / 2))
      le_rfl 1).IsOrbitPECE f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (OneStep.heun f)) h t₀ u := by
  rw [OneStep.isOrbit_ofIncrement_iff]
  unfold IsOrbitPECE
  refine forall_congr' fun n => ?_
  unfold peceStep correct historySum predict ofPair LinearMultistep.ofOneStep LinearMultistep.pad
  simp only [Function.iterate_one, OneStep.heun, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Fin.val_zero, Nat.sub_zero, Nat.cast_zero, zero_mul, sub_zero, Matrix.cons_val_zero, add_zero,
    one_smul, Nat.zero_lt_succ, ↓reduceDIte, Fin.zero_eta, smul_add, smul_smul]
  refine ⟨fun H => H.trans ?_, fun H => H.trans ?_⟩ <;> module

/-- **The Adams–Bashforth–Moulton pair with $p$ steps** ([quarteroni2000numerical], §11.7, Example
11.10): the predictor `adamsBashforth (p - 1)`, which has $p$ steps, the corrector
`adamsMoulton (p - 1)` padded to $p$ steps, and $m$ corrections.

The number $p - 1$ is a natural subtraction. -/
noncomputable def abm (p m : ℕ) : PredictorCorrector :=
  ofPair (LinearMultistep.adamsBashforth (p - 1)) (LinearMultistep.adamsMoulton (p - 1))
    (Nat.sub_le _ _) m

/-- **Example 11.10** of [quarteroni2000numerical]. For the Adams–Bashforth–Moulton pair with
$p \ge 2$ steps, the padded corrector and the predictor have the same first characteristic
polynomial
$$\hat\rho(r) = \tilde\rho(r) = r^p - r^{p-1} = r (r^{p-1} - r^{p-2}),$$
and the second characteristic polynomial of the padded corrector is
$\hat\sigma(r) = r \sigma(r)$, where $\sigma$ is that of the Adams–Moulton corrector
`adamsMoulton (p - 1)`. -/
theorem abm_charPoly (p m : ℕ) (hp : 2 ≤ p) :
    (abm p m).toCorrector.rho = X ^ p - X ^ (p - 1) ∧
      (abm p m).toPredictor.rho = X ^ p - X ^ (p - 1) ∧
      (abm p m).toCorrector.sigma = X * (LinearMultistep.adamsMoulton (p - 1)).sigma := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
  have e1 : k + 2 - 1 = k + 1 := by omega
  simp only [abm, e1]
  have hpred : (ofPair (LinearMultistep.adamsBashforth (k + 1))
      (LinearMultistep.adamsMoulton (k + 1)) (Nat.sub_le _ _) m).toPredictor =
      LinearMultistep.adamsBashforth (k + 1) :=
    toPredictor_ofPair _ _ _ _ rfl
  have hcorr : (ofPair (LinearMultistep.adamsBashforth (k + 1))
      (LinearMultistep.adamsMoulton (k + 1)) (Nat.sub_le _ _) m).toCorrector =
      (LinearMultistep.adamsMoulton (k + 1)).pad (k + 1) (Nat.sub_le _ _) := rfl
  have hrho := LinearMultistep.rho_pad (LinearMultistep.adamsMoulton (k + 1)) (k + 1)
    (Nat.sub_le _ _)
  have hsigma := LinearMultistep.sigma_pad (LinearMultistep.adamsMoulton (k + 1)) (k + 1)
    (Nat.sub_le _ _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hcorr]
    refine hrho.trans ?_
    rw [LinearMultistep.rho_of_a_single _ rfl]
    change X ^ (k + 1 - (k + 1 - 1)) * (X ^ (k + 1 - 1) * (X - C 1)) = _
    simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left, pow_one, map_one]
    ring
  · rw [hpred, LinearMultistep.rho_of_a_single _ rfl]
    change X ^ (k + 1) * (X - C 1) = _
    rw [map_one]
    ring
  · rw [hcorr]
    refine hsigma.trans ?_
    change X ^ (k + 1 - (k + 1 - 1)) * (LinearMultistep.adamsMoulton (k + 1)).sigma = _
    simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left, pow_one]


/-! ### The order of a predictor–corrector pair: Property 11.3 -/

section Order

variable {t : ℝ} {L : NNReal} {y : ℝ → E}

/-- The **local truncation error of the $P(EC)^m E$ scheme** along the curve $y$ at the time $t$:
$$\tau(h; t) = h^{-1} \bigl( y(t + h) - \Psi_h(t; y(t), y(t - h), \dots, y(t - ph)) \bigr),$$
where $\Psi_h$ is the $P(EC)^m E$ step. At $t = t_n$ it measures how far the exact values fail
to satisfy the scheme. -/
noncomputable def lte (f : ℝ → E → E) (h : ℝ) (y : ℝ → E) (t : ℝ) : E :=
  h⁻¹ • (y (t + h) - PC.peceStep f h t fun j => y (t - j * h))

/-- **Each correction is a contraction towards the fixed point of the corrector.** Let
$f(t + h, \cdot)$ be $L$-Lipschitz and $h \ge 0$, and let
$w = G + h b_{-1} f(t + h, w) + h \tau$, so that $w$ is a fixed point of the correction up to
$h \tau$. Then for every $k$ and every starting value $v_0$, the $k$-fold correction $v_k$ of
$v_0$ satisfies
$$\|v_k - w\| \le (h |b_{-1}| L)^k \|v_0 - w\| + h \|\tau\| \sum_{i<k} (h |b_{-1}| L)^i.$$
-/
theorem norm_iterate_correct_sub_le (hL : LipschitzWith L (f (t + h))) (hh : 0 ≤ h) {G v₀ w τ : E}
    (hw : w = PC.correct f h t G w + h • τ) (k : ℕ) :
    ‖(PC.correct f h t G)^[k] v₀ - w‖ ≤ (h * |PC.bm1| * L) ^ k * ‖v₀ - w‖ +
      h * ‖τ‖ * ∑ i ∈ range k, (h * |PC.bm1| * L) ^ i := by
  set c : ℝ := h * |PC.bm1| * L with hc
  have hstep : ∀ v : E, ‖PC.correct f h t G v - w‖ ≤ c * ‖v - w‖ + h * ‖τ‖ := by
    intro v
    have e : PC.correct f h t G v - w = (h * PC.bm1) • (f (t + h) v - f (t + h) w) - h • τ := by
      conv_lhs => rw [hw]
      simp only [correct, smul_sub]
      abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg hh, abs_mul, abs_of_nonneg hh,
      hc]
    have := hL.norm_sub_le v w
    nlinarith [abs_nonneg PC.bm1, mul_nonneg hh (abs_nonneg PC.bm1)]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Finset.sum_range_succ', pow_zero]
    refine (hstep _).trans ?_
    have hsum : ∑ i ∈ range k, c ^ (i + 1) = c * ∑ i ∈ range k, c ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    calc c * ‖(PC.correct f h t G)^[k] v₀ - w‖ + h * ‖τ‖
        ≤ c * (c ^ k * ‖v₀ - w‖ + h * ‖τ‖ * ∑ i ∈ range k, c ^ i) + h * ‖τ‖ := by gcongr
      _ = c ^ (k + 1) * ‖v₀ - w‖ + h * ‖τ‖ * (∑ i ∈ range k, c ^ (i + 1) + 1) := by
          rw [hsum]
          ring

/-- **Property 11.3** of [quarteroni2000numerical], the local truncation error of a pair. Let
$f(t + h, \cdot)$ be $L$-Lipschitz, let $h > 0$, and let $y$ satisfy $y'(s) = f(s, y(s))$ at the
points $s = t - jh$, $j = -1, 0, \dots, p$, where $y'$ is `deriv y`. Then the truncation error
$\tau$ of the $P(EC)^m E$ scheme satisfies
$$\|\tau\| \le (h |b_{-1}| L)^m \|\tilde\tau\| + \|\hat\tau\| \sum_{i<m} (h |b_{-1}| L)^i,$$
where $\tilde\tau$ and $\hat\tau$ are the local truncation errors of the predictor and of the
corrector along $y$ at $t$.

Each correction is a contraction with the constant $h |b_{-1}| L$ towards the value that the
corrector assigns to the exact history. -/
theorem norm_lte_le (hL : LipschitzWith L (f (t + h))) (hh : 0 < h)
    (hd : ∀ j : Fin (PC.p + 1), deriv y (t - j * h) = f (t - j * h) (y (t - j * h)))
    (hd' : deriv y (t + h) = f (t + h) (y (t + h))) :
    ‖PC.lte f h y t‖ ≤ (h * |PC.bm1| * L) ^ PC.m * ‖PC.toPredictor.lte h y t‖ +
      ‖PC.toCorrector.lte h y t‖ * ∑ i ∈ range PC.m, (h * |PC.bm1| * L) ^ i := by
  have hP := PC.toPredictor.lte_spec hh.ne' hd hd'
  have hC := PC.toCorrector.lte_spec hh.ne' hd hd'
  rw [show PC.toPredictor.bm1 = 0 from rfl, mul_zero, zero_smul, add_zero] at hP
  have hw : y (t + h) = PC.correct f h t
      (PC.historySum h (fun j => y (t - j * h)) fun j => f (t - j * h) (y (t - j * h)))
        (y (t + h)) + h • PC.toCorrector.lte h y t := hC
  have hv : (PC.predict h (fun j => y (t - j * h)) fun j => f (t - j * h) (y (t - j * h))) -
      y (t + h) = -(h • PC.toPredictor.lte h y t) := by
    have e : (PC.predict h (fun j => y (t - j * h)) fun j => f (t - j * h) (y (t - j * h))) =
        ∑ j, PC.toPredictor.a j • y (t - j * h) +
          h • ∑ j, PC.toPredictor.b j • f (t - j * h) (y (t - j * h)) := rfl
    rw [e]
    conv_lhs => rw [hP]
    abel
  have key := PC.norm_iterate_correct_sub_le hL hh.le hw PC.m
    (v₀ := PC.predict h (fun j => y (t - j * h)) fun j => f (t - j * h) (y (t - j * h)))
  rw [hv, norm_neg, norm_smul, Real.norm_of_nonneg hh.le] at key
  rw [lte, norm_smul, norm_inv, Real.norm_of_nonneg hh.le, norm_sub_rev, peceStep]
  calc h⁻¹ * ‖(PC.correct f h t (PC.historySum h (fun j => y (t - j * h)) fun j =>
        f (t - j * h) (y (t - j * h))))^[PC.m] (PC.predict h (fun j => y (t - j * h)) fun j =>
          f (t - j * h) (y (t - j * h))) - y (t + h)‖
      ≤ h⁻¹ * ((h * |PC.bm1| * L) ^ PC.m * (h * ‖PC.toPredictor.lte h y t‖) +
          h * ‖PC.toCorrector.lte h y t‖ * ∑ i ∈ range PC.m, (h * |PC.bm1| * L) ^ i) := by
        gcongr
    _ = (h * |PC.bm1| * L) ^ PC.m * ‖PC.toPredictor.lte h y t‖ +
          ‖PC.toCorrector.lte h y t‖ * ∑ i ∈ range PC.m, (h * |PC.bm1| * L) ^ i := by
        field_simp

/-- The global truncation error $\tau(h)$ of the $P(EC)^m E$ scheme along $y$ on $[t_0, t_0 + T]$:
the maximum of $\|\tau(h; t_n)\|$ over the steps $p \le n < N_h$, and $0$ if there is no such
step. -/
noncomputable def globalLte (f : ℝ → E → E) (t₀ T : ℝ) (y : ℝ → E) (h : ℝ) : ℝ :=
  ⨆ n : Fin (gridCount T h), if PC.p ≤ (n : ℕ) then ‖PC.lte f h y (node t₀ h n)‖ else 0

/-- The global truncation error of the $P(EC)^m E$ scheme is nonnegative. -/
theorem globalLte_nonneg (f : ℝ → E → E) (t₀ T : ℝ) (y : ℝ → E) (h : ℝ) :
    0 ≤ PC.globalLte f t₀ T y h :=
  Real.iSup_nonneg fun _ => by split_ifs <;> simp

/-- The $P(EC)^m E$ scheme has **order $q$ along the curve** $y$ on $[t_0, t_0 + T]$ if its global
truncation error satisfies $\tau(h) = O(h^q)$ as $h \to 0^+$. -/
def HasOrderFor (f : ℝ → E → E) (t₀ T : ℝ) (y : ℝ → E) (q : ℕ) : Prop :=
  PC.globalLte f t₀ T y =O[𝓝[>] 0] fun h => h ^ q

/-- **Property 11.3** of [quarteroni2000numerical], the order of a predictor–corrector pair. Let
$f(t, \cdot)$ be $L$-Lipschitz for every $t \in [t_0, t_0 + T]$, and let $y$ have the derivative
$f(t, y(t))$ at every $t \in [t_0, t_0 + T]$. If the predictor has order $\tilde q$ and the
corrector has order $q$ along $y$ on $[t_0, t_0 + T]$, then the $P(EC)^m E$ scheme has order
$\min(q, \tilde q + m)$ along $y$.

Thus the scheme has order $q$ when $m \ge q - \tilde q$, and order $\tilde q + m$ when
$m \le q - \tilde q$. -/
theorem hasOrderFor_of (hf : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith L (f t))
    (hy : ∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) {qp qc : ℕ}
    (hP : PC.toPredictor.HasOrderFor t₀ T y qp) (hC : PC.toCorrector.HasOrderFor t₀ T y qc) :
    PC.HasOrderFor f t₀ T y (min qc (qp + PC.m)) := by
  obtain ⟨cp, hcp, hPb⟩ := hP.exists_pos
  obtain ⟨cc, hcc, hCb⟩ := hC.exists_pos
  obtain ⟨h₁, hh₁, hI₁⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hPb.bound
  obtain ⟨h₂, hh₂, hI₂⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hCb.bound
  set β : ℝ := |PC.bm1| * L with hβ
  have hβ0 : 0 ≤ β := by positivity
  set K : ℝ := β ^ PC.m * cp + cc * ∑ i ∈ range PC.m, β ^ i with hK
  refine IsBigO.of_bound K ?_
  filter_upwards [Ioc_mem_nhdsGT (lt_min (lt_min hh₁ hh₂) zero_lt_one)] with h hh
  have hh0 : 0 < h := hh.1
  have hh1 : h ≤ 1 := hh.2.trans (min_le_right _ _)
  have hτp : PC.toPredictor.globalLte t₀ T y h ≤ cp * h ^ qp := by
    have := hI₁ ⟨hh0, hh.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
    simp only [Set.mem_ofPred_eq] at this
    rwa [Real.norm_of_nonneg (LinearMultistep.globalLte_nonneg _ _),
      Real.norm_of_nonneg (pow_nonneg hh0.le _)] at this
  have hτc : PC.toCorrector.globalLte t₀ T y h ≤ cc * h ^ qc := by
    have := hI₂ ⟨hh0, hh.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
    simp only [Set.mem_ofPred_eq] at this
    rwa [Real.norm_of_nonneg (LinearMultistep.globalLte_nonneg _ _),
      Real.norm_of_nonneg (pow_nonneg hh0.le _)] at this
  rw [Real.norm_of_nonneg (pow_nonneg hh0.le _),
    Real.norm_of_nonneg (PC.globalLte_nonneg _ _ _ _ _), globalLte]
  refine Real.iSup_le (fun n => ?_) (by positivity)
  split_ifs with hp
  · -- the pointwise bound at the node `t_n`
    have hn := n.2
    have hnode : node t₀ h n + h ∈ Icc t₀ (t₀ + T) := node_add_mem_Icc_of_lt hh0 hn
    have hL : LipschitzWith L (f (node t₀ h n + h)) := hf _ hnode
    have hd : ∀ j : Fin (PC.p + 1), deriv y (node t₀ h n - j * h) =
        f (node t₀ h n - j * h) (y (node t₀ h n - j * h)) := fun j => by
      rw [LinearMultistep.node_sub_mul (by omega)]
      exact (hy _ (node_mem_Icc_of_lt hh0 (by omega))).deriv
    have hd' : deriv y (node t₀ h n + h) = f (node t₀ h n + h) (y (node t₀ h n + h)) :=
      (hy _ hnode).deriv
    have key := PC.norm_lte_le hL hh0 hd hd'
    have hp' : ‖PC.toPredictor.lte h y (node t₀ h n)‖ ≤ cp * h ^ qp :=
      (PC.toPredictor.norm_lte_le_globalLte hp hn).trans hτp
    have hc' : ‖PC.toCorrector.lte h y (node t₀ h n)‖ ≤ cc * h ^ qc :=
      (PC.toCorrector.norm_lte_le_globalLte hp hn).trans hτc
    have hβh : ∀ i : ℕ, (h * |PC.bm1| * L) ^ i ≤ β ^ i := fun i => by
      rw [hβ, mul_assoc]
      exact pow_le_pow_left₀ (by positivity) (mul_le_of_le_one_left hβ0 hh1) i
    have hpow1 : h ^ (qp + PC.m) ≤ h ^ min qc (qp + PC.m) :=
      pow_le_pow_of_le_one hh0.le hh1 (min_le_right _ _)
    have hpow2 : h ^ qc ≤ h ^ min qc (qp + PC.m) :=
      pow_le_pow_of_le_one hh0.le hh1 (min_le_left _ _)
    have hS : ∑ i ∈ range PC.m, (h * |PC.bm1| * L) ^ i ≤ ∑ i ∈ range PC.m, β ^ i :=
      Finset.sum_le_sum fun i _ => hβh i
    calc ‖PC.lte f h y (node t₀ h n)‖
        ≤ (h * |PC.bm1| * L) ^ PC.m * ‖PC.toPredictor.lte h y (node t₀ h n)‖ +
          ‖PC.toCorrector.lte h y (node t₀ h n)‖ *
            ∑ i ∈ range PC.m, (h * |PC.bm1| * L) ^ i := key
      _ ≤ (h * |PC.bm1| * L) ^ PC.m * (cp * h ^ qp) + (cc * h ^ qc) * ∑ i ∈ range PC.m, β ^ i := by
          gcongr
      _ = β ^ PC.m * cp * h ^ (qp + PC.m) + cc * (∑ i ∈ range PC.m, β ^ i) * h ^ qc := by
          rw [hβ, pow_add]
          ring
      _ ≤ β ^ PC.m * cp * h ^ min qc (qp + PC.m) +
          cc * (∑ i ∈ range PC.m, β ^ i) * h ^ min qc (qp + PC.m) := by
          gcongr
      _ = K * h ^ min qc (qp + PC.m) := by rw [hK]; ring
  · positivity

end Order

end PredictorCorrector

/-! ### The region $\mathcal{A}^*$ of the midpoint method -/

namespace LinearMultistep

/-- The characteristic polynomial $\Pi_z(r) = r^2 - 2zr - 1$ of the midpoint method has degree $2$.
-/
theorem degree_charPoly_midpoint (z : ℂ) : (midpoint.charPoly z).degree = 2 := by
  rw [charPoly_midpoint, show (X ^ 2 - C (2 * z) * X - 1 : ℂ[X]) =
    C 1 * X ^ 2 + C (-(2 * z)) * X + C (-1) by simp only [map_one, map_neg, one_mul]; ring,
    degree_quadratic one_ne_zero]

/-- If $r$ is a root of $\Pi_z(r) = r^2 - 2zr - 1$, then $r \neq 0$ and $-1/r$ is also a root, since
the product of the roots is $-1$. -/
theorem isRoot_charPoly_midpoint_neg_inv {z r : ℂ} (hr : (midpoint.charPoly z).IsRoot r) :
    r ≠ 0 ∧ (midpoint.charPoly z).IsRoot (-1 / r) := by
  rw [charPoly_midpoint] at hr ⊢
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one] at hr ⊢
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  refine ⟨hr0, ?_⟩
  have : (-1 / r) ^ 2 - 2 * z * (-1 / r) - 1 = -(r ^ 2 - 2 * z * r - 1) / r ^ 2 := by
    field_simp
    ring
  rw [this, hr]
  simp

/-- **The region $\mathcal{A}^*$ of the midpoint method** (Remark 11.3 of
[quarteroni2000numerical]):
$$\mathcal{A}^* = \{ i\alpha : \alpha \in \mathbb{R}, \ |\alpha| < 1 \}.$$

The source prints $\alpha \in [-1, 1]$. At $\alpha = \pm 1$ the root $\pm i$ of
$r^2 \mp 2ir - 1$ is double, so the solution $n (\pm i)^n$ is unbounded, and the endpoints are
excluded.

For $z = i\alpha$ with $|\alpha| < 1$ the roots $i\alpha \pm \sqrt{1 - \alpha^2}$ are distinct
and have modulus $1$. Conversely, if a root $r$ and $-1/r$ both lie in the closed disc, they lie
on the circle, so $2z = r - 1/r = r - \bar r = 2i \operatorname{Im} r$; and
$|\operatorname{Im} r| = 1$ would make $r = \pm i$ a double root. -/
theorem absStabilityRegionStar_midpoint :
    midpoint.absStabilityRegionStar = {z | ∃ α : ℝ, |α| < 1 ∧ z = α * Complex.I} := by
  classical
  ext z
  rw [mem_absStabilityRegionStar_iff, Set.mem_ofPred_eq]
  have hbm1 : midpoint.bm1 = 0 := rfl
  simp only [hbm1, Complex.ofReal_zero, mul_zero, sub_zero, ne_eq, one_ne_zero, not_false_eq_true,
    true_and]
  constructor
  · intro H
    obtain ⟨r, hr⟩ := Complex.exists_root (f := midpoint.charPoly z)
      (by rw [degree_charPoly_midpoint]; norm_num)
    obtain ⟨hr0, hr'⟩ := isRoot_charPoly_midpoint_neg_inv hr
    obtain ⟨hle, hmul⟩ := H r hr
    obtain ⟨hle', -⟩ := H _ hr'
    have hnorm : ‖r‖ = 1 := by
      rw [norm_div, norm_neg, norm_one, div_le_one (norm_pos_iff.2 hr0)] at hle'
      linarith
    have hmult := hmul hnorm
    have hconj : r * (starRingEnd ℂ) r = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    have hr2 : r ^ 2 - 2 * z * r - 1 = 0 := by
      rw [charPoly_midpoint] at hr
      simpa [IsRoot] using hr
    have h2z : 2 * z = r - (starRingEnd ℂ) r := by
      have h1 : (2 * z) * r = r ^ 2 - 1 := by linear_combination -hr2
      have h2 : (r - (starRingEnd ℂ) r) * r = r ^ 2 - 1 := by linear_combination (-1 : ℂ) * hconj
      exact mul_right_cancel₀ hr0 (h1.trans h2.symm)
    have hsub : r - (starRingEnd ℂ) r = 2 * r.im * Complex.I := by
      apply Complex.ext
      · simp
      · simp
        ring
    have hz : z = r.im * Complex.I := by
      have : 2 * z = 2 * (r.im * Complex.I) := by rw [h2z, hsub]; ring
      exact mul_left_cancel₀ two_ne_zero this
    refine ⟨r.im, ?_, hz⟩
    by_contra hab
    have him1 : |r.im| ≤ 1 := hnorm ▸ Complex.abs_im_le_norm r
    have him : |r.im| = 1 := le_antisymm him1 (not_lt.1 hab)
    have hsq : r.re ^ 2 + r.im ^ 2 = 1 := by
      have := Complex.sq_norm r
      rw [hnorm, Complex.normSq_apply] at this
      nlinarith
    have hre : r.re = 0 := by
      have : r.im ^ 2 = 1 := by rw [← sq_abs, him]; norm_num
      nlinarith
    -- `r = ±i` is a double root
    have hzr : z = r := by
      rw [hz]
      apply Complex.ext <;> simp [hre]
    have hrr : r ^ 2 = -1 := by
      have : r.im ^ 2 = 1 := by rw [← sq_abs, him]; norm_num
      apply Complex.ext
      · simp [sq, hre]
        nlinarith
      · simp [sq, hre]
    have hfac : midpoint.charPoly z = (X - C r) ^ 2 := by
      rw [charPoly_midpoint, hzr]
      apply Polynomial.funext
      intro w
      simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one]
      linear_combination -hrr
    rw [hfac, rootMultiplicity_X_sub_C_pow] at hmult
    norm_num at hmult
  · rintro ⟨α, hα, rfl⟩
    obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
    set s : ℝ := Real.sqrt (1 - α ^ 2) with hs_def
    have hs : s ^ 2 = 1 - α ^ 2 := Real.sq_sqrt (by nlinarith)
    have hs0 : 0 < s := Real.sqrt_pos.2 (by nlinarith)
    set rp : ℂ := α * Complex.I + s with hrp
    set rm : ℂ := α * Complex.I - s with hrm
    have hsC : (s : ℂ) ^ 2 = 1 - (α : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, hs]
      push_cast
      ring
    have hfac : midpoint.charPoly (α * Complex.I) = (X - C rp) * (X - C rm) := by
      rw [charPoly_midpoint]
      apply Polynomial.funext
      intro w
      simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one, hrp, hrm]
      linear_combination -(α : ℂ) ^ 2 * Complex.I_sq + hsC
    have hne : ((X - C rp) * (X - C rm) : ℂ[X]) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
    have hnp : ‖rp‖ = 1 := by
      rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, Complex.sq_norm, Complex.normSq_apply, one_pow]
      simp [hrp]
      nlinarith
    have hnm : ‖rm‖ = 1 := by
      rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, Complex.sq_norm, Complex.normSq_apply, one_pow]
      simp [hrm]
      nlinarith
    have hpm : rp ≠ rm := by
      intro h
      have := congrArg Complex.re h
      simp [hrp, hrm] at this
      linarith
    rw [hfac]
    refine Polynomial.satisfiesRootCondition_of_roots hne ?_ ?_
    · intro r hr
      rw [roots_mul hne, roots_X_sub_C, roots_X_sub_C, Multiset.mem_add, Multiset.mem_singleton,
        Multiset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hnp.le
      · exact hnm.le
    · intro r hr _
      rw [roots_mul hne, roots_X_sub_C, roots_X_sub_C, Multiset.mem_add, Multiset.mem_singleton,
        Multiset.mem_singleton] at hr
      rw [roots_mul hne, roots_X_sub_C, roots_X_sub_C, Multiset.count_add, Multiset.count_singleton,
        Multiset.count_singleton]
      rcases hr with rfl | rfl
      · simp [hpm]
      · simp [hpm.symm]

/-- **Remark 11.3** of [quarteroni2000numerical], the midpoint method: the midpoint method has
$\mathcal{A} = \emptyset$ and $\mathcal{A}^* = \{ i\alpha : \alpha \in \mathbb{R}, \ |\alpha| <
1 \}$. -/
theorem absStabilityRegion_midpoint :
    midpoint.absStabilityRegion = ∅ ∧
      midpoint.absStabilityRegionStar = {z | ∃ α : ℝ, |α| < 1 ∧ z = α * Complex.I} :=
  ⟨absStabilityRegion_midpoint_eq_empty, absStabilityRegionStar_midpoint⟩

end LinearMultistep

/-!
### The explicit clause of the second Dahlquist barrier

An explicit method with $\sum_j a_j = 1$ is neither A-stable nor ϑ-stable (Property 11.2 of
[quarteroni2000numerical], first sentence). For such a method and real $t$, $\Pi_{-t}$ is monic of
degree $p + 1$. If all its roots were in the open unit disc, its value at a point $x_0 \in [0, 1]$
would be bounded by $2^{p+1}$. But $|\Pi_{-t}(x_0)| = |\rho(x_0) + t \sigma(x_0)| \ge t
|\sigma(x_0)| - |\rho(x_0)|$ is unbounded in $t$ once $\sigma(x_0) \neq 0$. The order bound of the
second barrier and Widlund's statement on ϑ-stability are not formalized.
-/

namespace LinearMultistep

variable (M : LinearMultistep)

/-- The polynomial $\sum_{j=0}^p b_j X^{p-j}$ has degree less than $p + 1$. -/
theorem degree_sigma_sum_lt :
    (∑ j : Fin (M.p + 1), C (M.b j) * X ^ (M.p - j)).degree < ((M.p + 1 : ℕ) : WithBot ℕ) := by
  refine (degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro j _
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact_mod_cast Nat.lt_succ_of_le (Nat.sub_le _ _)

/-- For an explicit method ($b_{-1} = 0$), $\sigma$ has degree less than $p + 1$. -/
theorem degree_sigma_lt_of_bm1_eq_zero (h : M.bm1 = 0) :
    M.sigma.degree < ((M.p + 1 : ℕ) : WithBot ℕ) := by
  rw [sigma, h, C_0, zero_mul, zero_add]
  exact M.degree_sigma_sum_lt

/-- For an explicit method ($b_{-1} = 0$), the polynomial $\Pi_z$ is monic for every
$z \in \mathbb{C}$. -/
theorem charPoly_monic_of_bm1_eq_zero (h : M.bm1 = 0) (z : ℂ) : (M.charPoly z).Monic := by
  refine (M.rho_monic.map _).sub_of_left ?_
  rw [degree_map, degree_rho, ← smul_eq_C_mul]
  refine (degree_smul_le _ _).trans_lt ?_
  rw [degree_map]
  exact M.degree_sigma_lt_of_bm1_eq_zero h

/-- For an explicit method ($b_{-1} = 0$), the polynomial $\Pi_z$ has natural degree $p + 1$ for
every $z \in \mathbb{C}$. -/
theorem natDegree_charPoly_of_bm1_eq_zero (h : M.bm1 = 0) (z : ℂ) :
    (M.charPoly z).natDegree = M.p + 1 := by
  apply natDegree_eq_of_degree_eq_some
  rw [charPoly, degree_sub_eq_left_of_degree_lt, degree_map, degree_rho]
  rw [degree_map, degree_rho, ← smul_eq_C_mul]
  refine (degree_smul_le _ _).trans_lt ?_
  rw [degree_map]
  exact M.degree_sigma_lt_of_bm1_eq_zero h

/-- The value of $\Pi_z$ at a real point $x$ is $\Pi_z(x) = \rho(x) - z \sigma(x)$, with $\rho(x)$
and $\sigma(x)$ real. -/
theorem eval_ofReal_charPoly (z : ℂ) (x : ℝ) :
    (M.charPoly z).eval (x : ℂ) = ((M.rho.eval x : ℝ) : ℂ) - z * ((M.sigma.eval x : ℝ) : ℂ) := by
  have e : ∀ P : ℝ[X], (P.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((P.eval x : ℝ) : ℂ) := fun P => by
    rw [eval_map]
    exact eval₂_at_apply (algebraMap ℝ ℂ) x
  rw [charPoly, eval_sub, eval_mul, eval_C, e, e]

/-- **The explicit clause of the second Dahlquist barrier** (Property 11.2 of
[quarteroni2000numerical]). Let the method be explicit ($b_{-1} = 0$) and satisfy
$\sum_j a_j = 1$. Then for every $t_1$ there is $t > \max(t_1, 0)$ such that
$-t \notin \mathcal{A}$.

So the region of absolute stability misses points of the negative real axis arbitrarily far from
$0$. The hypothesis is the order condition $0$ alone, not full consistency. -/
theorem exists_neg_notMem_absStabilityRegion_of_bm1_eq_zero (h : M.bm1 = 0)
    (h0 : M.orderCondition 0) (t₁ : ℝ) :
    ∃ t : ℝ, t₁ < t ∧ 0 < t ∧ -(t : ℂ) ∉ M.absStabilityRegion := by
  rcases eq_or_ne M.sigma 0 with hσ | hσ
  · refine ⟨max t₁ 0 + 1, by linarith [le_max_left t₁ 0], by linarith [le_max_right t₁ 0],
      fun hmem => ?_⟩
    rw [mem_absStabilityRegion_iff] at hmem
    have h1 : (M.charPoly (-((max t₁ 0 + 1 : ℝ) : ℂ))).IsRoot 1 := by
      rw [charPoly, hσ, Polynomial.map_zero, mul_zero, sub_zero]
      simpa using (M.rho_isRoot_one h0).map (f := algebraMap ℝ ℂ)
    have := hmem.2 1 h1
    simp at this
  · obtain ⟨x₀, hx₀, hσx⟩ : ∃ x₀ ∈ Icc (0 : ℝ) 1, M.sigma.eval x₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hσ (M.sigma.eq_zero_of_infinite_isRoot
        ((Set.Icc_infinite zero_lt_one).mono fun x hx => hcon x hx))
    set A := |M.rho.eval x₀| with hA
    set B := |M.sigma.eval x₀| with hB
    have hB0 : 0 < B := abs_pos.2 hσx
    refine ⟨max t₁ 0 + (2 ^ (M.p + 1) + A) / B + 1, ?_, ?_, fun hmem => ?_⟩
    · have := le_max_left t₁ 0
      have : 0 ≤ (2 ^ (M.p + 1) + A) / B := by positivity
      linarith
    · have := le_max_right t₁ 0
      have : 0 ≤ (2 ^ (M.p + 1) + A) / B := by positivity
      linarith
    set t := max t₁ 0 + (2 ^ (M.p + 1) + A) / B + 1 with ht
    have ht0 : 0 < t := by
      have := le_max_right t₁ 0
      have : 0 ≤ (2 ^ (M.p + 1) + A) / B := by positivity
      linarith
    have htB : 2 ^ (M.p + 1) + A < t * B := by
      have h1 : ((2 ^ (M.p + 1) + A) / B + 1) * B = 2 ^ (M.p + 1) + A + B := by
        field_simp
      have h2 : ((2 ^ (M.p + 1) + A) / B + 1) * B ≤ t * B := by
        apply mul_le_mul_of_nonneg_right _ hB0.le
        linarith [le_max_right t₁ 0]
      linarith
    rw [mem_absStabilityRegion_iff] at hmem
    have hx₀C : ‖(x₀ : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx₀.1]
      exact hx₀.2
    have hbound := Polynomial.norm_eval_le_two_pow_natDegree (M.charPoly_monic_of_bm1_eq_zero h _)
      hmem.2 hx₀C
    rw [M.natDegree_charPoly_of_bm1_eq_zero h, M.eval_ofReal_charPoly] at hbound
    have e : ((M.rho.eval x₀ : ℝ) : ℂ) - -(t : ℂ) * ((M.sigma.eval x₀ : ℝ) : ℂ) =
        ((M.rho.eval x₀ + t * M.sigma.eval x₀ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, Complex.norm_real, Real.norm_eq_abs] at hbound
    have h3 : |t * M.sigma.eval x₀| ≤ |M.rho.eval x₀ + t * M.sigma.eval x₀| + A := by
      have := abs_add_le (M.rho.eval x₀ + t * M.sigma.eval x₀) (-M.rho.eval x₀)
      rwa [add_neg_cancel_comm, abs_neg] at this
    rw [abs_mul, abs_of_pos ht0] at h3
    linarith

/-- **Explicit methods are not A-stable** (Property 11.2 of [quarteroni2000numerical]): an explicit
method ($b_{-1} = 0$) with $\sum_j a_j = 1$ is not A-stable. -/
theorem not_isAStable_of_bm1_eq_zero (h : M.bm1 = 0) (h0 : M.orderCondition 0) :
    ¬ M.IsAStable := by
  intro hA
  obtain ⟨t, -, ht0, hmem⟩ := M.exists_neg_notMem_absStabilityRegion_of_bm1_eq_zero h h0 0
  exact hmem (hA _ (by simpa using ht0))

/-- **Explicit methods are not ϑ-stable** (Property 11.2 of [quarteroni2000numerical]): an explicit
method ($b_{-1} = 0$) with $\sum_j a_j = 1$ is not ϑ-stable for any $\vartheta > 0$. -/
theorem not_isThetaStable_of_bm1_eq_zero (h : M.bm1 = 0) (h0 : M.orderCondition 0) {ϑ : ℝ}
    (hϑ : 0 < ϑ) : ¬ M.IsThetaStable ϑ := by
  intro hA
  obtain ⟨t, -, ht0, hmem⟩ := M.exists_neg_notMem_absStabilityRegion_of_bm1_eq_zero h h0 0
  refine hmem (hA _ ?_ ?_)
  · simpa using ht0.ne'
  · rw [neg_neg, Complex.arg_ofReal_of_nonneg ht0.le, abs_zero]
    exact hϑ

end LinearMultistep

end ODE
