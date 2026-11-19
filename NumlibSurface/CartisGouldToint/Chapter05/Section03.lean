/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.MeasureDominated
import NumlibSurface.CartisGouldToint.Chapter05.Section01

/-!
# Cartis, Gould and Toint, Section 5.3: Measure-dominated problems

This module formalizes Section 5.3 of [cartis2022evaluation]. Let $f : \mathbb{R}^n \to \mathbb{R}$
have a nonnegative optimality measure $\psi$. The function $f$ is $\psi$-dominated of level $\mu$
(5.3.1) if $f(x) - f_* \le \kappa_\psi \psi(x)^\mu$, where $f_*$ is the minimum value. The classes
$\mathrm{AR}_{\psi,\nu}$ and $\mathrm{TR}_{\psi,\nu}$ of Sections 5.3.2 and 5.3.3 contain the
methods that decrease $f$ by $\kappa_\nu \psi(x_{k+1})^\nu$, respectively by
$\kappa_\nu (\min_{i \le k} \psi(x_i))^\nu$, at every successful iteration, and whose successful
iterations are dense, $k \le \kappa_R |\mathcal{S}_k| + \kappa_A$ (5.3.9). For these methods the gap
$\Gamma_k = f(x_k) - f_*$ converges superlinearly, linearly or sublinearly when $\nu < \mu$,
$\nu = \mu$ or $\nu > \mu$, and the module gives the corresponding iteration counts. Uniformly
full-rank nonlinear least squares, with $f = \Phi_\ell$ of Section 5.1, is the main example
(Theorems 5.3.10–5.3.12).

All results reduce to the scalar recurrences of `Numlib.Optimization.Complexity.GapRecurrence` for
the gap, with $c = \kappa_\nu/\kappa_\psi^{\nu/\mu}$, $\tau = \nu/\mu$ and
$\alpha = \tau - 1 = (\nu - \mu)/\mu$. The classes are those of
`Numlib.Optimization.Complexity.MeasureDominated`.

## Main definitions

* Equation (5.3.1), `CartisGouldToint.Chapter05.IsDominated`:
  $f(x) - f_* \le \kappa_\psi \psi(x)^\mu$ for all $x$.
* Section 5.3.2, `CartisGouldToint.Chapter05.IsARpsiNuRun`: the class $\mathrm{AR}_{\psi,\nu}$.
* Section 5.3.3, `CartisGouldToint.Chapter05.IsTRpsiNuRun`: the class $\mathrm{TR}_{\psi,\nu}$.

## Main results

* Equations (5.3.2)–(5.3.3), `CartisGouldToint.Chapter05.Phi_isMeasureDominated`: under the
  full-rank condition (5.1.62), $\Phi_\ell$ is $\|\nabla\Phi_\ell\|$-dominated of level
  $\ell/(\ell - 1)$.
* Lemma 5.3.1, `CartisGouldToint.Chapter05.lemma_5_3_1`: the gap recurrence (5.3.10) of
  $\mathrm{AR}_{\psi,\nu}$ and the three rates of convergence.
* Theorem 5.3.2, `CartisGouldToint.Chapter05.theorem_5_3_2`: iteration counts from the comparison
  sequence (5.3.12).
* Theorem 5.3.3, `CartisGouldToint.Chapter05.theorem_5_3_3`: for $\nu < \mu$, superlinear
  convergence and counts of order $\log|\log\epsilon|$.
* Theorem 5.3.4, `CartisGouldToint.Chapter05.theorem_5_3_4`: for $\nu = \mu$, linear convergence and
  counts of order $|\log\epsilon|$.
* Theorem 5.3.5, `CartisGouldToint.Chapter05.theorem_5_3_5`: for $\nu > \mu$, sublinear convergence
  and counts of order $\epsilon^{-\alpha}$.
* Lemma 5.3.6, `CartisGouldToint.Chapter05.lemma_5_3_6`: the gap recurrence (5.3.33) of
  $\mathrm{TR}_{\psi,\nu}$ and its consequences in the three cases.
* Theorem 5.3.7, `CartisGouldToint.Chapter05.theorem_5_3_7`: for $\nu < \mu$, the gap vanishes after
  finitely many successful iterations.
* Theorem 5.3.8, `CartisGouldToint.Chapter05.theorem_5_3_8`: for $\nu = \mu$, linear convergence and
  counts of order $|\log\epsilon|$.
* Theorem 5.3.9, `CartisGouldToint.Chapter05.theorem_5_3_9`: for $\nu > \mu$, sublinear convergence
  and counts of order $\epsilon^{-\alpha}$.
* Theorem 5.3.10, `CartisGouldToint.Chapter05.theorem_5_3_10`: full-rank least squares with an
  $\mathrm{AR}_{\psi,\nu}$ method, superlinear convergence of $\|r(x_k)\|$.
* Theorem 5.3.11, `CartisGouldToint.Chapter05.theorem_5_3_11`: full-rank least squares with a
  $\mathrm{TR}_{\psi,\nu}$ method and $\ell > 2$, sublinear convergence.
* Theorem 5.3.12, `CartisGouldToint.Chapter05.theorem_5_3_12`: full-rank least squares with a
  $\mathrm{TR}_{\psi,\nu}$ method and $\ell = 2$, linear convergence.

## Conventions

* The space $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. A run is a sequence $x$ of iterates with a
  predicate $S$ on the iterations, which says which iterations are successful. The set
  $\mathcal{S}_k$ of successful iterations $j \le k$ is `Optimization.successSet S k`.
* The standing hypotheses of Sections 5.3.2 and 5.3.3 are `CartisGouldToint.Chapter05.ARSetting` and
  `CartisGouldToint.Chapter05.TRSetting`: $\psi \ge 0$, $f$ is $\psi$-dominated of level $\mu \ge 1$
  with constant $\kappa_\psi > 0$ at the iterates, and the run is in $\mathrm{AR}_{\psi,\nu}$,
  respectively $\mathrm{TR}_{\psi,\nu}$, with $\kappa_\nu > 0$, $\nu \ge 1$, $\kappa_R \ge 1$ and
  $\kappa_A \ge 0$.
* Rates and counts are upper bounds along the successful iterations. "The algorithm needs at most
  $N$ successful iterations to compute $x_\epsilon$ with $\Gamma_\epsilon \le \epsilon$" is stated
  as "$\Gamma_{k+1} \le \epsilon$ whenever $N \le |\mathcal{S}_k|$", because $x_{k+1}$ is computed
  at iteration $k$ and the gaps do not increase. "At most $N$ iterations" is stated as
  "$\Gamma_{k+1} \le \epsilon$ whenever $\kappa_R N + \kappa_A \le k$", by (5.3.9).

## Implementation notes

* The classes are the backbone's `Optimization.IsARLikeRun` and `Optimization.IsTRLikeRun`.
  Domination at a set of points is `Optimization.IsMeasureDominated`.
* The measure versions of the counts ("an iterate with $\psi(x_\epsilon) \le \epsilon$") come from
  (B.5.11): a successful iteration $k$ with $\Gamma_k \le \kappa_\nu \epsilon^\nu$ gives
  $\psi(x_{k+1}) \le \epsilon$ for AR methods, and $\min_{i \le k} \psi(x_i) \le \epsilon$ for TR
  methods. The terms $\max(0, \cdot)$ guard counts that may be negative for small $\Gamma_0$.
* Where a theorem does not assume $\Gamma_0 > 0$, the bounds at $\Gamma_0 = 0$ hold with the
  conventions $\log 0 = 0$ and $0^{-\alpha} = 0$ of Lean.
* The corrections of the constants of Appendix B, and the reasons for them, are recorded in the
  module doc comment of `Numlib.Optimization.Complexity.GapRecurrence`.

## Deviations from the source

* **Domination** (generalization). The global predicate uses the infimum and leaves the
  restrictions on $\mu$, $\kappa_\psi$ and $\psi$ to theorems. The run settings need domination
  only at the iterates and permit any reference lower bound there, as motivated after
  Lemma 5.3.1. See `CartisGouldToint.Chapter05.IsDominated` and
  `CartisGouldToint.Chapter05.ARSetting`.
* **Run classes** (generalization). The predicates leave sign and exponent restrictions to their
  callers. A TR run may continue after a zero measure, since (5.3.28) then asks only for
  nonnegative decrease. See `CartisGouldToint.Chapter05.IsTRpsiNuRun`.
* **Lemmas 5.3.1 and 5.3.6, Theorems 5.3.5, 5.3.9 and 5.3.11** (correction). The
  $\nu>\mu$ estimates give polynomial upper bounds. The conditions permit faster convergence,
  so the successive-error ratio need not tend to $1$ as in the definition in §A.3.
  See `CartisGouldToint.Chapter05.lemma_5_3_1` and `CartisGouldToint.Chapter05.lemma_5_3_6`.
* **Theorems 5.3.2–5.3.5 and 5.3.7–5.3.12** (reading). The abstract bounds count iterations
  and successful iterations. Objective and derivative evaluation counts require a concrete
  algorithm with the corresponding evaluation schedule.
* **Theorems 5.3.3–5.3.5** (generalization). The appendix's formulas use $\Gamma_0 > 0$.
  Lean also handles $\Gamma_0 = 0$. See `CartisGouldToint.Chapter05.theorem_5_3_3`.
* **Theorems 5.3.7–5.3.9** (specialization). The Lean statements explicitly require
  $\Gamma_0 > 0$, the nondegenerate case treated by Lemma 5.3.6 and used in their formulas.
* **Theorem 5.3.3** (reading). The bounds of the form $\log|\log\epsilon|$ are stated with
  $\log\max(1, |\log\epsilon|)$; the book's footnote to Theorem 5.3.10 assumes
  $|\log\epsilon| \ge 1$. See `CartisGouldToint.Chapter05.theorem_5_3_3`.
* **Theorem 5.3.3, constant $\kappa^F$** (typo). The constant of Appendix B is corrected to
  `Optimization.superlinearCountConst`, because the second phase must reach
  $\omega \le c^{1/\alpha}\epsilon$. See `CartisGouldToint.Chapter05.theorem_5_3_3`.
* **Theorem 5.3.4, convergence factor** (typo). Appendix B omits the reciprocal
  on $1+\kappa_\nu/\kappa_\psi$. See `CartisGouldToint.Chapter05.theorem_5_3_4`.
* **Theorem 5.3.5, constant $\kappa^E$** (typo). It uses $\min(1, \alpha)$ in place of $\alpha$,
  because (B.5.12) holds only for $\alpha \le 1$, and $\Gamma_0^{-\alpha}$ in place of the printed
  $\kappa_\psi^{\nu/\mu}/\kappa_\nu$. The halving argument gives $2M + 2$ successful iterations. See
  `CartisGouldToint.Chapter05.theorem_5_3_5`.
* **Theorem 5.3.9, constants** (typo). $\kappa^E = \mu\kappa_\psi^{\nu/\mu}/((\nu -
  \mu)\kappa_\nu)$, where the book prints the exponent $\mu/\nu$, and
  $\kappa^F = -\kappa^E\Gamma_0^{-\alpha}$, where the book prints $\kappa^B$. See
  `CartisGouldToint.Chapter05.theorem_5_3_9`.
* **Theorem 5.3.9, optimality measure** (correction). Equation (5.3.28) controls the
  running minimum of the measures. The individual measures at successful iterates need
  not converge, and the Lean theorem gives complexity for finding one small measure.
* **Measure versions of Theorems 5.3.3–5.3.5 and 5.3.7–5.3.9** (reading). Since the gap counts are
  real numbers, reaching an iteration with a small measure takes up to two successful iterations
  more than the gap count, where the book adds one. See
  `CartisGouldToint.Chapter05.ARSetting.exists_measure_le`.
* **Measure versions of Theorems 5.3.7–5.3.9** (correction). For TR methods the iterate reached is
  $x_i$ with $i \le k$, where the book writes $x_k$. See `CartisGouldToint.Chapter05.theorem_5_3_7`.
* **Lemma 5.3.6 (ii)** (typo). "A final value $\Gamma_{k_\square} \ge 1$" means
  $\Gamma_{k_\square} \ge \Gamma_\square$. See `CartisGouldToint.Chapter05.lemma_5_3_6`.
* **Theorem 5.3.7** (reading). The constant $\kappa^F_{\mathrm{TR},1}$ is taken in an integer form
  with a ceiling. See `CartisGouldToint.Chapter05.theorem_5_3_7`.
* **Equations (5.3.2)–(5.3.3)** (generalization). The book also claims $\min \Phi_\ell = 0$; only
  the reference value $0$ is needed. See `CartisGouldToint.Chapter05.Phi_isMeasureDominated`.
* **Theorems 5.3.10 and 5.3.11** (generalization). The book takes $\ell$ even, which matters only
  for the smoothness of $\Phi_\ell$ and is not needed. See
  `CartisGouldToint.Chapter05.theorem_5_3_10`.
* **Theorem 5.3.12** (typo). The display mixes $\kappa^C_{\mathrm{TR1,FRLS}}$ and
  $\kappa^C_{\mathrm{TR,FRLS}}$; one constant is meant. See
  `CartisGouldToint.Chapter05.theorem_5_3_12`.

## Not formalized

* The examples of Section 5.3.1 other than full-rank least squares: convex functions on a ball,
  strongly convex functions, and $\|x\|^{2i}$.
* The claim that TR1 and TR2 belong to $\mathrm{TR}_{\psi,\nu}$ with uniform constants (see
  `Numlib.Optimization.Complexity.MeasureDominated`).
-/

open Set Filter Topology Optimization

namespace CartisGouldToint.Chapter05

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ### Domination and the classes $\mathrm{AR}_{\psi,\nu}$ and $\mathrm{TR}_{\psi,\nu}$ -/

/-- **Equation (5.3.1)** of [cartis2022evaluation]. Let $f, \psi : \mathbb{R}^n \to \mathbb{R}$,
$\mu, \kappa_\psi \in \mathbb{R}$, and let $f_* = \inf_x f(x)$. The function $f$ is
**$\psi$-dominated of level $\mu$** with constant $\kappa_\psi$ if, for all
$x \in \mathbb{R}^n$, $f_* \le f(x)$ and
$$f(x) - f_* \le \kappa_\psi \psi(x)^\mu.$$

**Generalization.** The source uses a global minimum and assumes a nonnegative measure,
$\mu \ge 1$ and $\kappa_\psi > 0$. The predicate uses `Optimization.IsMeasureDominated`
on the whole space with the infimum `⨅ x, f x` and leaves the measure and parameter
restrictions to the results. Its lower-bound conjunct excludes objectives unbounded below. -/
def IsDominated (f ψ : ℝⁿ → ℝ) (μ κψ : ℝ) : Prop :=
  IsMeasureDominated f ψ (⨅ x, f x) μ κψ univ

/-- The function $f$ is $\psi$-dominated of level $\mu$ with constant $\kappa_\psi$ if and only if
$\inf f \le f(x)$ and $f(x) - \inf f \le \kappa_\psi \psi(x)^\mu$ for all $x$.

**Generalization.** Expands the generalized global inequality with its infimum lower bound.
-/
theorem isDominated_iff {f ψ : ℝⁿ → ℝ} {μ κψ : ℝ} :
    IsDominated f ψ μ κψ ↔ ∀ x, (⨅ y, f y) ≤ f x ∧ f x - ⨅ y, f y ≤ κψ * ψ x ^ μ :=
  isMeasureDominated_univ_iff

/-- If $f$ is $\psi$-dominated of level $\mu$ with constant $\kappa_\psi$, then $f$ is dominated in
the same way at the points of every sequence $x$, with the reference value $\inf f$. -/
theorem IsDominated.range {f ψ : ℝⁿ → ℝ} {μ κψ : ℝ} (h : IsDominated f ψ μ κψ) (x : ℕ → ℝⁿ) :
    IsMeasureDominated f ψ (⨅ y, f y) μ κψ (Set.range x) :=
  IsMeasureDominated.range h x

/-- **Section 5.3.2** of [cartis2022evaluation], the class $\mathrm{AR}_{\psi,\nu}$. Let
$f, \psi : \mathbb{R}^n \to \mathbb{R}$ and $\kappa_\nu, \nu, \kappa_R, \kappa_A \in
\mathbb{R}$. A sequence $x$ of iterates with the success predicate $S$ belongs to the **class
$\mathrm{AR}_{\psi,\nu}$** if every successful iteration $k$ satisfies
$$f(x_k) - f(x_{k+1}) \ge \kappa_\nu \psi(x_{k+1})^\nu, \qquad (5.3.5)$$
every unsuccessful iteration keeps the iterate, $x_{k+1} = x_k$, and the successful iterations
are dense: $k \le \kappa_R |\mathcal{S}_k| + \kappa_A$ for every $k$ (5.3.9), where
$\mathcal{S}_k$ is the set of successful iterations $j \le k$.

The definition is `Optimization.IsARLikeRun`. The sign and exponent conditions of §5.3.2
are separate hypotheses. The density condition implies infinitely many successes.
Runs of ARp without termination are members
(`Optimization.isARLikeRun_of_isARpRun`, (5.3.6)–(5.3.7)), and
`Optimization.exists_isARpRun_softplus` is a complete example.

**Reading.** Matches the structural rules and inclusive success count; sign and exponent
restrictions are separate hypotheses.
-/
def IsARpsiNuRun (f ψ : ℝⁿ → ℝ) (κν ν κR κA : ℝ) (x : ℕ → ℝⁿ) (S : ℕ → Prop) : Prop :=
  IsARLikeRun f ψ κν ν κR κA x S

/-- **Section 5.3.3** of [cartis2022evaluation], the class $\mathrm{TR}_{\psi,\nu}$. A sequence $x$
of iterates with the success predicate $S$ belongs to the **class $\mathrm{TR}_{\psi,\nu}$** if
every successful iteration $k$ satisfies
$$f(x_k) - f(x_{k+1}) \ge \kappa_\nu \left(\min_{i \le k} \psi(x_i)\right)^\nu, \qquad
  (5.3.28)$$
every unsuccessful iteration keeps the iterate, and the successful iterations are dense (5.3.9),
as in the class $\mathrm{AR}_{\psi,\nu}$.

The definition is `Optimization.IsTRLikeRun`. The sign and exponent conditions of §5.3.3
are separate hypotheses. The source stops at a zero measure. The Lean run can continue
because (5.3.28) then requires only nonnegative decrease. A member is
`Optimization.isTRLikeRun_halving`.

**Reading.** Matches the running-minimum decrease and density; no automatic exit on a zero measure
and parameter domains are separate.
-/
def IsTRpsiNuRun (f ψ : ℝⁿ → ℝ) (κν ν κR κA : ℝ) (x : ℕ → ℝⁿ) (S : ℕ → Prop) : Prop :=
  IsTRLikeRun f ψ κν ν κR κA x S

/-- A run is in the class $\mathrm{AR}_{\psi,\nu}$ if and only if it satisfies
`Optimization.IsARLikeRun`.

**Generalization.** Unfolds the generalized AR run class.
-/
theorem isARpsiNuRun_iff {f ψ : ℝⁿ → ℝ} {κν ν κR κA : ℝ} {x : ℕ → ℝⁿ} {S : ℕ → Prop} :
    IsARpsiNuRun f ψ κν ν κR κA x S ↔ IsARLikeRun f ψ κν ν κR κA x S :=
  Iff.rfl

/-- A run is in the class $\mathrm{TR}_{\psi,\nu}$ if and only if it satisfies
`Optimization.IsTRLikeRun`.

**Generalization.** Unfolds the generalized TR run class.
-/
theorem isTRpsiNuRun_iff {f ψ : ℝⁿ → ℝ} {κν ν κR κA : ℝ} {x : ℕ → ℝⁿ} {S : ℕ → Prop} :
    IsTRpsiNuRun f ψ κν ν κR κA x S ↔ IsTRLikeRun f ψ κν ν κR κA x S :=
  Iff.rfl

/-- The standing hypotheses of Section 5.3.2 of [cartis2022evaluation]: the optimality measure
$\psi$ is nonnegative, $f$ is $\psi$-dominated of level $\mu \ge 1$ with constant
$\kappa_\psi > 0$ and reference value $f_*$ at the iterates, and $x$ is a run in
$\mathrm{AR}_{\psi,\nu}$ with the success predicate $S$ and constants $\kappa_\nu > 0$,
$\nu \ge 1$, $\kappa_R \ge 1$ and $\kappa_A \ge 0$.

**Reading.** Uses domination on the iterates with a reference lower bound that need not be attained
or global.
-/
structure ARSetting (f ψ : ℝⁿ → ℝ) (fstar μ κψ κν ν κR κA : ℝ) (x : ℕ → ℝⁿ) (S : ℕ → Prop) :
    Prop where
  /-- The measure $\psi$ is nonnegative. -/
  psi_nonneg : ∀ y, 0 ≤ ψ y
  /-- The level satisfies $\mu \ge 1$. -/
  one_le_mu : 1 ≤ μ
  /-- The domination constant satisfies $\kappa_\psi > 0$. -/
  kappaPsi_pos : 0 < κψ
  /-- The function $f$ is dominated (5.3.1) at the iterates, with the reference value $f_*$. -/
  dominated : IsMeasureDominated f ψ fstar μ κψ (Set.range x)
  /-- The run is in the class $\mathrm{AR}_{\psi,\nu}$. -/
  run : IsARpsiNuRun f ψ κν ν κR κA x S
  /-- The decrease constant satisfies $\kappa_\nu > 0$. -/
  kappaNu_pos : 0 < κν
  /-- The decrease exponent satisfies $\nu \ge 1$. -/
  one_le_nu : 1 ≤ ν
  /-- The density constant satisfies $\kappa_R \ge 1$. -/
  one_le_kappaR : 1 ≤ κR
  /-- The density constant satisfies $\kappa_A \ge 0$. -/
  kappaA_nonneg : 0 ≤ κA

/-- The standing hypotheses of Section 5.3.3 of [cartis2022evaluation]: the same as those of Section
5.3.2 (`CartisGouldToint.Chapter05.ARSetting`), for a run in $\mathrm{TR}_{\psi,\nu}$.

**Generalization.** Applies local-to-the-run domination and arbitrary reference lower bound to the
generalized TR run.
-/
structure TRSetting (f ψ : ℝⁿ → ℝ) (fstar μ κψ κν ν κR κA : ℝ) (x : ℕ → ℝⁿ) (S : ℕ → Prop) :
    Prop where
  /-- The measure $\psi$ is nonnegative. -/
  psi_nonneg : ∀ y, 0 ≤ ψ y
  /-- The level satisfies $\mu \ge 1$. -/
  one_le_mu : 1 ≤ μ
  /-- The domination constant satisfies $\kappa_\psi > 0$. -/
  kappaPsi_pos : 0 < κψ
  /-- The function $f$ is dominated (5.3.1) at the iterates, with the reference value $f_*$. -/
  dominated : IsMeasureDominated f ψ fstar μ κψ (Set.range x)
  /-- The run is in the class $\mathrm{TR}_{\psi,\nu}$. -/
  run : IsTRpsiNuRun f ψ κν ν κR κA x S
  /-- The decrease constant satisfies $\kappa_\nu > 0$. -/
  kappaNu_pos : 0 < κν
  /-- The decrease exponent satisfies $\nu \ge 1$. -/
  one_le_nu : 1 ≤ ν
  /-- The density constant satisfies $\kappa_R \ge 1$. -/
  one_le_kappaR : 1 ≤ κR
  /-- The density constant satisfies $\kappa_A \ge 0$. -/
  kappaA_nonneg : 0 ≤ κA


/-- The standing hypotheses of Section 5.3.2 follow from the global domination (5.3.1), with the
reference value $f_* = \inf f$: if $\psi \ge 0$, $\mu \ge 1$, $\kappa_\psi > 0$, $f$ is
$\psi$-dominated of level $\mu$ with constant $\kappa_\psi$, and $x$ is a run in
$\mathrm{AR}_{\psi,\nu}$ with $\kappa_\nu > 0$, $\nu \ge 1$, $\kappa_R \ge 1$ and
$\kappa_A \ge 0$.

**Reading.** Packages global domination using the infimum and explicit positivity rather than an
attained minimum.
-/
theorem ARSetting.of_isDominated {f ψ : ℝⁿ → ℝ} {μ κψ κν ν κR κA : ℝ} {x : ℕ → ℝⁿ}
    {S : ℕ → Prop} (hψ : ∀ y, 0 ≤ ψ y) (hμ : 1 ≤ μ) (hκψ : 0 < κψ) (hdom : IsDominated f ψ μ κψ)
    (hrun : IsARpsiNuRun f ψ κν ν κR κA x S) (hκν : 0 < κν) (hν : 1 ≤ ν) (hκR : 1 ≤ κR)
    (hκA : 0 ≤ κA) : ARSetting f ψ (⨅ y, f y) μ κψ κν ν κR κA x S :=
  ⟨hψ, hμ, hκψ, hdom.range x, hrun, hκν, hν, hκR, hκA⟩

/-- The standing hypotheses of Section 5.3.3 follow from the global domination (5.3.1), with the
reference value $f_* = \inf f$, for a run in $\mathrm{TR}_{\psi,\nu}$ with the same conditions
on the constants as in `CartisGouldToint.Chapter05.ARSetting.of_isDominated`.

**Generalization.** Packages global domination using the infimum and the generalized TR run.
-/
theorem TRSetting.of_isDominated {f ψ : ℝⁿ → ℝ} {μ κψ κν ν κR κA : ℝ} {x : ℕ → ℝⁿ}
    {S : ℕ → Prop} (hψ : ∀ y, 0 ≤ ψ y) (hμ : 1 ≤ μ) (hκψ : 0 < κψ) (hdom : IsDominated f ψ μ κψ)
    (hrun : IsTRpsiNuRun f ψ κν ν κR κA x S) (hκν : 0 < κν) (hν : 1 ≤ ν) (hκR : 1 ≤ κR)
    (hκA : 0 ≤ κA) : TRSetting f ψ (⨅ y, f y) μ κψ κν ν κR κA x S :=
  ⟨hψ, hμ, hκψ, hdom.range x, hrun, hκν, hν, hκR, hκA⟩

/-! ### Adaptive-regularization-like methods -/

namespace ARSetting

variable {f ψ : ℝⁿ → ℝ} {fstar μ κψ κν ν κR κA : ℝ} {x : ℕ → ℝⁿ} {S : ℕ → Prop}
  (h : ARSetting f ψ fstar μ κψ κν ν κR κA x S)
include h

/-- Under the standing hypotheses of Section 5.3.2, $\mu > 0$. -/
theorem mu_pos : 0 < μ := one_pos.trans_le h.one_le_mu

/-- Under the standing hypotheses of Section 5.3.2, $\nu > 0$. -/
theorem nu_pos : 0 < ν := one_pos.trans_le h.one_le_nu

/-- Under the standing hypotheses of Section 5.3.2, $c = \kappa_\nu/\kappa_\psi^{\nu/\mu} > 0$. -/
theorem c_pos : 0 < κν / κψ ^ (ν / μ) :=
  div_pos h.kappaNu_pos (Real.rpow_pos_of_pos h.kappaPsi_pos _)

/-- The recurrence (5.3.11). Under the standing hypotheses of Section 5.3.2, the gaps
$\Gamma_k = f(x_k) - f_*$ satisfy the implicit recurrence with
$c = \kappa_\nu/\kappa_\psi^{\nu/\mu}$ and $\tau = \nu/\mu$: $\Gamma_k \ge 0$,
$\Gamma_{k+1} = \Gamma_k$ at the unsuccessful iterations, and $\Gamma_k - \Gamma_{k+1} \ge
c\,\Gamma_{k+1}^\tau$ at the successful ones.

**Generalization.** Packages the same recurrence, including the generalized reference value and
domination at iterates.
-/
theorem gap :
    IsImplicitGapDecrease (fun k => f (x k) - fstar) S (κν / κψ ^ (ν / μ)) (ν / μ) :=
  isImplicitGapDecrease_of_isARLikeRun h.run h.psi_nonneg h.kappaPsi_pos h.mu_pos
    h.kappaNu_pos.le h.nu_pos.le h.dominated

/-- Under the standing hypotheses of Section 5.3.2, there are infinitely many successful iterations:
for every $N$ there is a successful iteration $k \ge N$. -/
theorem frequently : ∀ N, ∃ k ≥ N, S k :=
  Optimization.frequently_of_density (by linarith [h.one_le_kappaR]) h.run.density

/-- Under the standing hypotheses of Section 5.3.2, if $\kappa_R N + \kappa_A \le k$, then
$N \le |\mathcal{S}_k|$, by (5.3.9). -/
theorem le_card {N : ℝ} {k : ℕ} (hk : κR * N + κA ≤ k) : N ≤ (successSet S k).card :=
  le_card_of_density (by linarith [h.one_le_kappaR]) h.run.density hk

/-- The bound (B.5.11). Under the standing hypotheses of Section 5.3.2, if iteration $k$ is
successful, $\epsilon \ge 0$ and $\Gamma_k \le \kappa_\nu \epsilon^\nu$, then
$\psi(x_{k+1}) \le \epsilon$. -/
theorem measure_le {k : ℕ} (hk : S k) {ε : ℝ} (hε : 0 ≤ ε)
    (hΓ : f (x k) - fstar ≤ κν * ε ^ ν) : ψ (x (k + 1)) ≤ ε := by
  have h1 := h.run.decrease k hk
  have h2 : 0 ≤ f (x (k + 1)) - fstar := h.gap.nonneg (k + 1)
  have h3 : ψ (x (k + 1)) ^ ν ≤ ε ^ ν :=
    le_of_mul_le_mul_left (by linarith) h.kappaNu_pos
  exact (Real.rpow_le_rpow_iff (h.psi_nonneg _) hε h.nu_pos).1 h3

/-- Measure counts from gap counts. Assume the standing hypotheses of Section 5.3.2, let
$\epsilon \ge 0$ and $N \in \mathbb{R}$, and suppose that
$\Gamma_{k+1} \le \kappa_\nu \epsilon^\nu$ whenever $N \le |\mathcal{S}_k|$. Then some
successful iteration $k$ has $\psi(x_{k+1}) \le \epsilon$, $|\mathcal{S}_k| \le \max(N, 0) + 2$
and $k \le \kappa_R(\max(N, 0) + 2) + \kappa_A$.

**Reading.** Converts a real gap count into a measure count with allowance for rounding and one
following success.
-/
theorem exists_measure_le {ε N : ℝ} (hε : 0 ≤ ε)
    (hcount : ∀ k, N ≤ (successSet S k).card → f (x (k + 1)) - fstar ≤ κν * ε ^ ν) :
    ∃ k, S k ∧ ψ (x (k + 1)) ≤ ε ∧ ((successSet S k).card : ℝ) ≤ max N 0 + 2 ∧
      (k : ℝ) ≤ κR * (max N 0 + 2) + κA := by
  obtain ⟨k, hk, hφ, hcard⟩ := Optimization.exists_le_of_gap_count (φ := fun k => ψ (x (k + 1)))
    (κν := κν) (ν := ν)
    h.gap.nonneg h.frequently hcount fun k hk => by
      have := h.run.decrease k hk; linarith
  refine ⟨k, hk, ?_, hcard, ?_⟩
  · have h3 : ψ (x (k + 1)) ^ ν ≤ ε ^ ν := le_of_mul_le_mul_left hφ h.kappaNu_pos
    exact (Real.rpow_le_rpow_iff (h.psi_nonneg _) hε h.nu_pos).1 h3
  · have := h.run.density k
    have : κR * ((successSet S k).card : ℝ) ≤ κR * (max N 0 + 2) :=
      mul_le_mul_of_nonneg_left hcard (by linarith [h.one_le_kappaR])
    linarith

/-- Measure counts from integer gap counts. Assume the standing hypotheses of Section 5.3.2, let
$\epsilon \ge 0$ and $n \in \mathbb{N}$, and suppose that
$\Gamma_{k+1} \le \kappa_\nu \epsilon^\nu$ whenever $n \le |\mathcal{S}_k|$. Then some
successful iteration $k$ has $\psi(x_{k+1}) \le \epsilon$, $|\mathcal{S}_k| \le \max(n, 1) + 1$
and $k \le \kappa_R(\max(n, 1) + 1) + \kappa_A$.

**Reading.** Converts the same gap-to-measure argument to an explicit integer threshold with a floor
at one.
-/
theorem exists_measure_le_nat {ε : ℝ} {n : ℕ} (hε : 0 ≤ ε)
    (hcount : ∀ k, n ≤ (successSet S k).card → f (x (k + 1)) - fstar ≤ κν * ε ^ ν) :
    ∃ k, S k ∧ ψ (x (k + 1)) ≤ ε ∧ (successSet S k).card ≤ max n 1 + 1 ∧
      (k : ℝ) ≤ κR * (max n 1 + 1 : ℕ) + κA := by
  obtain ⟨k, hk, hφ, hcard⟩ := Optimization.exists_le_of_gap_count_nat
    (φ := fun k => ψ (x (k + 1))) (κν := κν) (ν := ν)
    h.gap.nonneg h.frequently hcount fun k hk => by
      have := h.run.decrease k hk; linarith
  refine ⟨k, hk, ?_, hcard, ?_⟩
  · have h3 : ψ (x (k + 1)) ^ ν ≤ ε ^ ν := le_of_mul_le_mul_left hφ h.kappaNu_pos
    exact (Real.rpow_le_rpow_iff (h.psi_nonneg _) hε h.nu_pos).1 h3
  · have := h.run.density k
    have : κR * ((successSet S k).card : ℝ) ≤ κR * (max n 1 + 1 : ℕ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by linarith [h.one_le_kappaR])
    linarith

/-- Under the standing hypotheses of Section 5.3.2, if $\Gamma_0 = 0$, then $\Gamma_k = 0$ for every
$k$. -/
theorem gap_eq_zero (h0 : f (x 0) - fstar = 0) (k : ℕ) : f (x k) - fstar = 0 :=
  le_antisymm (h0 ▸ h.gap.antitone h.c_pos.le (Nat.zero_le k)) (h.gap.nonneg k)

/-- Under the standing hypotheses of Section 5.3.2, if $\Gamma_0 = 0$ and $\epsilon \ge 0$, then
some successful iteration $k$ with $|\mathcal{S}_k| \le 1$, that is, the first successful
iteration, has $\psi(x_{k+1}) \le \epsilon$ and $k \le \kappa_R + \kappa_A$. -/
theorem exists_measure_le_of_gap_zero (h0 : f (x 0) - fstar = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ k, S k ∧ ψ (x (k + 1)) ≤ ε ∧ (successSet S k).card ≤ 1 ∧ (k : ℝ) ≤ κR + κA := by
  classical
  have hex : ∃ k, S k := let ⟨k, _, hk⟩ := h.frequently 0; ⟨k, hk⟩
  have hk : S (Nat.find hex) := Nat.find_spec hex
  have hcard : (successSet S (Nat.find hex)).card ≤ 1 := Finset.card_le_one.2 fun a ha b hb => by
    rw [mem_successSet] at ha hb
    have := Nat.find_min' hex ha.2; have := Nat.find_min' hex hb.2; omega
  refine ⟨Nat.find hex, hk, h.measure_le hk hε ?_, hcard, ?_⟩
  · rw [h.gap_eq_zero h0]; exact mul_nonneg h.kappaNu_pos.le (Real.rpow_nonneg hε _)
  · have := h.run.density (Nat.find hex)
    have : κR * ((successSet S (Nat.find hex)).card : ℝ) ≤ κR * 1 :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by linarith [h.one_le_kappaR])
    linarith

end ARSetting

private theorem sub_div_self_eq {μ ν : ℝ} (hμ : μ ≠ 0) : ν / μ - 1 = (ν - μ) / μ := by
  field_simp

section AR

variable {f ψ : ℝⁿ → ℝ} {fstar μ κψ κν ν κR κA : ℝ} {x : ℕ → ℝⁿ} {S : ℕ → Prop}

/-- **Lemma 5.3.1** of [cartis2022evaluation]. Assume the standing hypotheses of Section 5.3.2, and
let $\Gamma_k = f(x_k) - f_*$ and $c = \kappa_\nu/\kappa_\psi^{\nu/\mu}$. Then every successful
iteration $k$ satisfies
$$\Gamma_{k+1} \le \Gamma_k \left(1 + c\,\Gamma_{k+1}^{(\nu - \mu)/\mu}\right)^{-1}, \qquad
  (5.3.10)$$
and $\Gamma_k \to 0$. Moreover:

* (i) if $\nu < \mu$, the gaps converge superlinearly along the successful iterations: for every
  $\eta > 0$ there is $K$ such that $\Gamma_{k+1} \le \eta\Gamma_k$ for every successful
  $k \ge K$;
* (ii) if $\nu = \mu$, they converge linearly: $\Gamma_{k+1} \le (1 +
  \kappa_\nu/\kappa_\psi)^{-1}\Gamma_k$ for every successful $k$;
* (iii) if $\nu > \mu$ and $\Gamma_0 > 0$, they satisfy the polynomial bound $\Gamma_{k+1} \le
  (\Gamma_0^{-\alpha} + c\,\kappa_{\rm dom}|\mathcal{S}_k|)^{-1/\alpha}$ for every $k$, with
  $\alpha = (\nu - \mu)/\mu$.

**Correction.** The source describes (iii) as sublinear convergence. Its ratio definition
in §A.3 requires $\Gamma_{k+1}/\Gamma_k \to 1$ along successive successes.
For $\mu=1$ and $\nu=2$, both (5.3.1) and (5.3.5) permit
$\Gamma_k=\psi(x_k)=2^{-k}$ with $\kappa_\psi=\kappa_\nu=1$ and every iteration successful.

The constant $\kappa_{\rm dom} = \min(\Gamma_0^{-\alpha}c^{-1}(2^\alpha - 1), \min(1,
\alpha)/2)$ is `Optimization.IsImplicitGapDecrease.kappaDom`. -/
theorem lemma_5_3_1 (h : ARSetting f ψ fstar μ κψ κν ν κR κA x S) :
    (∀ k, S k → f (x (k + 1)) - fstar ≤ (f (x k) - fstar) *
      (1 + κν / κψ ^ (ν / μ) * (f (x (k + 1)) - fstar) ^ ((ν - μ) / μ))⁻¹) ∧
    Tendsto (fun k => f (x k) - fstar) atTop (𝓝 0) ∧
    (ν < μ → ∀ η, 0 < η → ∃ K, ∀ k ≥ K, S k →
      f (x (k + 1)) - fstar ≤ η * (f (x k) - fstar)) ∧
    (ν = μ → ∀ k, S k → f (x (k + 1)) - fstar ≤ (1 + κν / κψ)⁻¹ * (f (x k) - fstar)) ∧
    (μ < ν → 0 < f (x 0) - fstar → ∀ k, f (x (k + 1)) - fstar ≤
      ((f (x 0) - fstar) ^ (-((ν - μ) / μ)) + κν / κψ ^ (ν / μ) *
        IsImplicitGapDecrease.kappaDom (κν / κψ ^ (ν / μ)) ((ν - μ) / μ) (f (x 0) - fstar) *
          (successSet S k).card) ^ (-1 / ((ν - μ) / μ))) := by
  have hμ := h.mu_pos
  have hα := sub_div_self_eq (ν := ν) hμ.ne'
  have hτ : 0 < ν / μ := div_pos h.nu_pos hμ
  obtain ⟨r1, r2, r3⟩ := h.gap.rates h.c_pos hτ h.frequently
  refine ⟨fun k hk => ?_, h.gap.tendsto_zero h.c_pos hτ h.frequently,
    fun hνμ => r1 ((div_lt_one hμ).2 hνμ), fun hνμ k hk => ?_, fun hνμ hΓ0 k => ?_⟩
  · have := h.gap.le_div h.c_pos.le hk
    rw [hα] at this
    rwa [← div_eq_mul_inv]
  · have := r2 (by rw [hνμ, div_self hμ.ne']) k hk
    rwa [hνμ, div_self hμ.ne', Real.rpow_one] at this
  · have := r3 ((one_lt_div hμ).2 hνμ) hΓ0 k
    rwa [hα] at this

/-- **Theorem 5.3.2** of [cartis2022evaluation]. Assume the standing hypotheses of Section 5.3.2,
and let $\epsilon > 0$. Let $N = \Upsilon_{c,\nu/\mu}(\Gamma_0, \epsilon)$ be the first index at
which the comparison sequence (5.3.12), started at $\Gamma_0$, is at most $\epsilon$ (5.3.13),
where $c = \kappa_\nu/\kappa_\psi^{\nu/\mu}$. Then $\Gamma_{k+1} \le \epsilon$ for every $k$
with $N \le |\mathcal{S}_k|$ (5.3.14), and for every $k \ge \kappa_R N + \kappa_A$ (5.3.15).

The index $N$ is the value of `Optimization.implicitGapHitIndex` at
$(c, \nu/\mu, \Gamma_0, \epsilon)$. The Lean statement counts iterations and
successful iterations. The corresponding number of evaluations depends on the algorithm.

**Reading.** Same implicit threshold at the stated c and tau, including zero initial gap; counts
iterations rather than evaluations.
-/
theorem theorem_5_3_2 (h : ARSetting f ψ fstar μ κψ κν ν κR κA x S) {ε : ℝ} (hε : 0 < ε) :
    (∀ k, implicitGapHitIndex (κν / κψ ^ (ν / μ)) (ν / μ) (f (x 0) - fstar) ε ≤
        (successSet S k).card → f (x (k + 1)) - fstar ≤ ε) ∧
    (∀ k : ℕ, κR * implicitGapHitIndex (κν / κψ ^ (ν / μ)) (ν / μ) (f (x 0) - fstar) ε + κA ≤ k →
        f (x (k + 1)) - fstar ≤ ε) := by
  have hcount := (h.gap.le_implicitGapSeq h.c_pos (div_pos h.nu_pos h.mu_pos)).2 ε hε
  exact ⟨hcount, fun k hk => hcount k (by exact_mod_cast h.le_card hk)⟩


/-- **Theorem 5.3.3** of [cartis2022evaluation] (case $1 \le \nu < \mu$). Assume the standing
hypotheses of Section 5.3.2 and $\nu < \mu$. Let $c = \kappa_\nu/\kappa_\psi^{\nu/\mu}$,
$\kappa^E = 1/(\log\mu - \log\nu)$, $\kappa^F$ the value of `Optimization.superlinearCountConst`
at $(c, \nu/\mu, \Gamma_0)$, $\kappa^B = \kappa_R\kappa^E$ and
$\kappa^C = \kappa_R\kappa^F + \kappa_A$. Then:

* the gaps converge superlinearly along the successful iterations: for every $\eta > 0$ there is
  $K$ such that $\Gamma_{k+1} \le \eta\Gamma_k$ for every successful $k \ge K$;
* for every $\epsilon > 0$, $\Gamma_{k+1} \le \epsilon$ for every $k$ with $|\mathcal{S}_k| \ge
  \kappa^E\log\max(1, |\log\epsilon|) + \kappa^F$ (5.3.17);
* for every $\epsilon > 0$, $\Gamma_{k+1} \le \epsilon$ for every $k \ge \kappa^B\log\max(1,
  |\log\epsilon|) + \kappa^C$ (5.3.16);
* for every $\epsilon > 0$, some successful iteration $k$ has $\psi(x_{k+1}) \le \epsilon$,
  $|\mathcal{S}_k| \le M$ and $k \le \kappa_R M + \kappa_A$, where $M = \kappa^E\log\max(1,
  |\log(\kappa_\nu\epsilon^\nu)|) + \kappa^F + 1$ ((5.3.18)–(5.3.19)).

**Typo.** The constant $\kappa^F$ of Appendix B is corrected: the second phase of the argument
must reach $\omega \le c^{1/\alpha}\epsilon$, which gives `Optimization.superlinearCountConst`.

**Reading.** The book's bounds $\log|\log\epsilon|$ are stated with
$\log\max(1, |\log\epsilon|)$.

**Generalization.** The appendix's constants use $\Gamma_0 > 0$. When $\Gamma_0 = 0$, every gap
vanishes, and the first successful iteration satisfies the measure bound. -/
theorem theorem_5_3_3 (h : ARSetting f ψ fstar μ κψ κν ν κR κA x S) (hνμ : ν < μ) :
    (∀ η, 0 < η → ∃ K, ∀ k ≥ K, S k → f (x (k + 1)) - fstar ≤ η * (f (x k) - fstar)) ∧
    (∀ ε, 0 < ε → ∀ k, 1 / (Real.log μ - Real.log ν) * Real.log (max 1 |Real.log ε|) +
        superlinearCountConst (κν / κψ ^ (ν / μ)) (ν / μ) (f (x 0) - fstar) ≤
          (successSet S k).card →
      f (x (k + 1)) - fstar ≤ ε) ∧
    (∀ ε, 0 < ε → ∀ k : ℕ, κR * (1 / (Real.log μ - Real.log ν)) * Real.log (max 1 |Real.log ε|) +
        (κR * superlinearCountConst (κν / κψ ^ (ν / μ)) (ν / μ) (f (x 0) - fstar) + κA) ≤ k →
      f (x (k + 1)) - fstar ≤ ε) ∧
    (∀ ε, 0 < ε → ∃ k, S k ∧ ψ (x (k + 1)) ≤ ε ∧
      ((successSet S k).card : ℝ) ≤ 1 / (Real.log μ - Real.log ν) *
          Real.log (max 1 |Real.log (κν * ε ^ ν)|) +
        superlinearCountConst (κν / κψ ^ (ν / μ)) (ν / μ) (f (x 0) - fstar) + 1 ∧
      (k : ℝ) ≤ κR * (1 / (Real.log μ - Real.log ν) * Real.log (max 1 |Real.log (κν * ε ^ ν)|) +
        superlinearCountConst (κν / κψ ^ (ν / μ)) (ν / μ) (f (x 0) - fstar) + 1) + κA) := by
  have hμ := h.mu_pos
  have hν := h.nu_pos
  have hτ0 : 0 < ν / μ := div_pos hν hμ
  have hτ1 : ν / μ < 1 := (div_lt_one hμ).2 hνμ
  rcases (h.gap.nonneg 0).lt_or_eq with hΓ0 | hΓ0
  swap
  · -- the degenerate case `Γ_0 = 0`
    have hz := h.gap_eq_zero hΓ0.symm
    refine ⟨(lemma_5_3_1 h).2.2.1 hνμ, fun ε hε k _ => by rw [hz]; exact hε.le,
      fun ε hε k _ => by rw [hz]; exact hε.le, fun ε hε => ?_⟩
    obtain ⟨k, hk, hψ, hcard, hkle⟩ := h.exists_measure_le_of_gap_zero hΓ0.symm hε.le
    have hB : 0 ≤ 1 / (Real.log μ - Real.log ν) * Real.log (max 1 |Real.log (κν * ε ^ ν)|) +
        superlinearCountConst (κν / κψ ^ (ν / μ)) (ν / μ) (f (x 0) - fstar) :=
      add_nonneg (mul_nonneg (div_nonneg zero_le_one (sub_nonneg.2
        (Real.log_le_log hν hνμ.le))) (Real.log_nonneg (le_max_left _ _)))
        (superlinearCountConst_nonneg h.c_pos.le hτ0 hτ1.le (h.gap.nonneg 0))
    have hc : ((successSet S k).card : ℝ) ≤ 1 := by exact_mod_cast hcard
    refine ⟨k, hk, hψ, by linarith, hkle.trans ?_⟩
    nlinarith [h.one_le_kappaR]
  set c := κν / κψ ^ (ν / μ) with hc_def
  set Γ0 := f (x 0) - fstar with hΓ0_def
  set κF := superlinearCountConst c (ν / μ) Γ0 with hκF
  have hlog : Real.log (1 / (ν / μ)) = Real.log μ - Real.log ν := by
    rw [one_div_div, Real.log_div hμ.ne' hν.ne']
  have hκF0 : 0 ≤ κF := superlinearCountConst_nonneg h.c_pos.le hτ0 hτ1.le hΓ0.le
  -- the gap count
  have hcount : ∀ ε, 0 < ε → ∀ k, 1 / (Real.log μ - Real.log ν) *
      Real.log (max 1 |Real.log ε|) + κF ≤ (successSet S k).card →
      f (x (k + 1)) - fstar ≤ ε := by
    intro ε hε k hk
    have hb := superlinearGapCount_le (Γ0 := Γ0) h.c_pos hτ0 hτ1 hΓ0 hε
    rw [hlog] at hb
    refine h.gap.le_of_superlinear_count h.c_pos hτ0 hτ1 hΓ0 hε ?_
    have : (superlinearGapCount c (ν / μ) Γ0 ε : ℝ) ≤ (successSet S k).card := by
      refine hb.trans (le_trans (le_of_eq ?_) hk)
      rw [hκF, superlinearCountConst, hlog]
      ring
    exact_mod_cast this
  refine ⟨(lemma_5_3_1 h).2.2.1 hνμ, hcount, fun ε hε k hk => hcount ε hε k
    (h.le_card (by linarith)), fun ε hε => ?_⟩
  have hεν : 0 < κν * ε ^ ν := mul_pos h.kappaNu_pos (Real.rpow_pos_of_pos hε _)
  -- the integer count `n = superlinearGapCount …` and one more successful iteration
  set n := superlinearGapCount c (ν / μ) Γ0 (κν * ε ^ ν) with hn
  have hn1 : 1 ≤ n := by
    rw [hn, superlinearGapCount]
    exact le_add_right (Nat.le_add_left 1 _)
  have hnb := superlinearGapCount_le_const (Γ0 := Γ0) h.c_pos hτ0 hτ1 hΓ0 hεν
  rw [hlog] at hnb
  have hgc : ∀ k, n ≤ (successSet S k).card → f (x (k + 1)) - fstar ≤ κν * ε ^ ν :=
    fun k hk => h.gap.le_of_superlinear_count h.c_pos hτ0 hτ1 hΓ0 hεν hk
  obtain ⟨k, hk, hψ, hcard, hkle⟩ := ARSetting.exists_measure_le_nat h hε.le hgc
  rw [max_eq_left hn1] at hcard hkle
  have hb : ((n + 1 : ℕ) : ℝ) ≤ 1 / (Real.log μ - Real.log ν) *
      Real.log (max 1 |Real.log (κν * ε ^ ν)|) + κF + 1 := by
    push_cast; rw [hκF]; linarith [show Real.log (max 1 |Real.log (κν * ε ^ ν)|) /
      (Real.log μ - Real.log ν) = 1 / (Real.log μ - Real.log ν) *
        Real.log (max 1 |Real.log (κν * ε ^ ν)|) by ring]
  refine ⟨k, hk, hψ, (by exact_mod_cast hcard : ((successSet S k).card : ℝ) ≤ (n + 1 : ℕ)).trans hb,
    hkle.trans ?_⟩
  have := mul_le_mul_of_nonneg_left hb (by linarith [h.one_le_kappaR] : (0 : ℝ) ≤ κR)
  linarith

/-- **Theorem 5.3.4** of [cartis2022evaluation] (case $\nu = \mu$). Assume the standing hypotheses
of Section 5.3.2 and $\nu = \mu$. Let $\kappa^E = 1/\log(1 + \kappa_\nu/\kappa_\psi)$ and
$\kappa^F = \log\Gamma_0/\log(1 + \kappa_\nu/\kappa_\psi) + 1$. Then:

* the gaps converge linearly: $\Gamma_{k+1} \le (1 + \kappa_\nu/\kappa_\psi)^{-1}\Gamma_k$ for
  every successful $k$;
* for every $\epsilon > 0$, $\Gamma_{k+1} \le \epsilon$ for every $k$ with $|\mathcal{S}_k| \ge
  \kappa^E|\log\epsilon| + \kappa^F$ (5.3.21);
* for every $\epsilon > 0$, $\Gamma_{k+1} \le \epsilon$ for every $k \ge
  \kappa_R\kappa^E|\log\epsilon| + \kappa_R\kappa^F + \kappa_A$ (5.3.20);
* for every $\epsilon > 0$, some successful iteration $k$ has $\psi(x_{k+1}) \le \epsilon$,
  $|\mathcal{S}_k| \le M$ and $k \le \kappa_R M + \kappa_A$, where $M =
  \max(\nu\kappa^E|\log\epsilon| + \kappa^E|\log\kappa_\nu| + \kappa^F, 1) + 1$
  ((5.3.22)–(5.3.23)).

**Generalization.** The appendix takes $\log\Gamma_0$. When $\Gamma_0 = 0$, every gap vanishes,
the bounds hold with the convention $\log 0 = 0$, and the first successful iteration satisfies
the measure bound.

**Typo.** The proof in Appendix B prints $1+\kappa_\nu/\kappa_\psi$ as the convergence
factor. The reciprocal in the main statement is the factor used here. -/
theorem theorem_5_3_4 (h : ARSetting f ψ fstar μ κψ κν ν κR κA x S) (hνμ : ν = μ) :
    (∀ k, S k → f (x (k + 1)) - fstar ≤ (1 + κν / κψ)⁻¹ * (f (x k) - fstar)) ∧
    (∀ ε, 0 < ε → ∀ k, 1 / Real.log (1 + κν / κψ) * |Real.log ε| +
        (Real.log (f (x 0) - fstar) / Real.log (1 + κν / κψ) + 1) ≤ (successSet S k).card →
      f (x (k + 1)) - fstar ≤ ε) ∧
    (∀ ε, 0 < ε → ∀ k : ℕ, κR * (1 / Real.log (1 + κν / κψ)) * |Real.log ε| +
        (κR * (Real.log (f (x 0) - fstar) / Real.log (1 + κν / κψ) + 1) + κA) ≤ k →
      f (x (k + 1)) - fstar ≤ ε) ∧
    (∀ ε, 0 < ε → ∃ k, S k ∧ ψ (x (k + 1)) ≤ ε ∧
      ((successSet S k).card : ℝ) ≤ max (ν * (1 / Real.log (1 + κν / κψ)) * |Real.log ε| +
          (1 / Real.log (1 + κν / κψ) * |Real.log κν| +
            (Real.log (f (x 0) - fstar) / Real.log (1 + κν / κψ) + 1))) 1 + 1 ∧
      (k : ℝ) ≤ κR * (max (ν * (1 / Real.log (1 + κν / κψ)) * |Real.log ε| +
          (1 / Real.log (1 + κν / κψ) * |Real.log κν| +
            (Real.log (f (x 0) - fstar) / Real.log (1 + κν / κψ) + 1))) 1 + 1) + κA) := by
  have hμ := h.mu_pos
  rcases (h.gap.nonneg 0).lt_or_eq with hΓ0 | hΓ0
  swap
  · -- the degenerate case `Γ_0 = 0`
    have hz := h.gap_eq_zero hΓ0.symm
    refine ⟨(lemma_5_3_1 h).2.2.2.1 hνμ, fun ε hε k _ => by rw [hz]; exact hε.le,
      fun ε hε k _ => by rw [hz]; exact hε.le, fun ε hε => ?_⟩
    obtain ⟨k, hk, hψ, hcard, hkle⟩ := h.exists_measure_le_of_gap_zero hΓ0.symm hε.le
    have hc : ((successSet S k).card : ℝ) ≤ 1 := by exact_mod_cast hcard
    have hm := le_max_right (ν * (1 / Real.log (1 + κν / κψ)) * |Real.log ε| +
      (1 / Real.log (1 + κν / κψ) * |Real.log κν| +
        (Real.log (f (x 0) - fstar) / Real.log (1 + κν / κψ) + 1))) 1
    refine ⟨k, hk, hψ, by linarith, hkle.trans ?_⟩
    nlinarith [h.one_le_kappaR]
  have hτ : ν / μ = 1 := by rw [hνμ, div_self hμ.ne']
  have hc : κν / κψ ^ (ν / μ) = κν / κψ := by rw [hτ, Real.rpow_one]
  have hcpos : 0 < κν / κψ := hc ▸ h.c_pos
  have hL : 0 < Real.log (1 + κν / κψ) := Real.log_pos (by linarith)
  set Γ0 := f (x 0) - fstar
  -- the gap count, for any `ε > 0`
  have hcount : ∀ ε, 0 < ε → ∀ k, 1 / Real.log (1 + κν / κψ) * |Real.log ε| +
      (Real.log Γ0 / Real.log (1 + κν / κψ) + 1) ≤ (successSet S k).card →
      f (x (k + 1)) - fstar ≤ ε := by
    intro ε hε k hk
    refine h.gap.le_of_linear_count hτ h.c_pos hε hΓ0 ?_
    rw [hc]
    refine le_trans ?_ hk
    have : -Real.log ε ≤ |Real.log ε| := neg_le_abs _
    rw [sub_div, one_div_mul_eq_div]
    have : -Real.log ε / Real.log (1 + κν / κψ) ≤ |Real.log ε| / Real.log (1 + κν / κψ) :=
      div_le_div_of_nonneg_right this hL.le
    rw [sub_eq_add_neg, ← neg_div]
    linarith
  refine ⟨(lemma_5_3_1 h).2.2.2.1 hνμ, hcount, fun ε hε k hk => hcount ε hε k
    (h.le_card (by linarith)), fun ε hε => ?_⟩
  have hεν : 0 < κν * ε ^ ν := mul_pos h.kappaNu_pos (Real.rpow_pos_of_pos hε _)
  set N := ν * (1 / Real.log (1 + κν / κψ)) * |Real.log ε| +
    (1 / Real.log (1 + κν / κψ) * |Real.log κν| + (Real.log Γ0 / Real.log (1 + κν / κψ) + 1))
  set y := (Real.log Γ0 - Real.log (κν * ε ^ ν)) / Real.log (1 + κν / κψ) with hy
  -- `|log (κν ε^ν)| ≤ |log κν| + ν |log ε|`
  have hlog : |Real.log (κν * ε ^ ν)| ≤ |Real.log κν| + ν * |Real.log ε| := by
    rw [Real.log_mul h.kappaNu_pos.ne' (Real.rpow_pos_of_pos hε _).ne', Real.log_rpow hε]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos h.nu_pos]
  have hyN : y + 1 ≤ N := by
    have h2 : -Real.log (κν * ε ^ ν) ≤ |Real.log κν| + ν * |Real.log ε| :=
      (neg_le_abs _).trans hlog
    have h4 := div_le_div_of_nonneg_right h2 hL.le
    have e1 : y = Real.log Γ0 / Real.log (1 + κν / κψ) +
        -Real.log (κν * ε ^ ν) / Real.log (1 + κν / κψ) := by rw [hy]; ring
    have e2 : (|Real.log κν| + ν * |Real.log ε|) / Real.log (1 + κν / κψ) =
        1 / Real.log (1 + κν / κψ) * |Real.log κν| +
          ν * (1 / Real.log (1 + κν / κψ)) * |Real.log ε| := by ring
    have eN : N = ν * (1 / Real.log (1 + κν / κψ)) * |Real.log ε| +
      (1 / Real.log (1 + κν / κψ) * |Real.log κν| +
        (Real.log Γ0 / Real.log (1 + κν / κψ) + 1)) := rfl
    linarith
  have hgc : ∀ k, ⌈y⌉₊ ≤ (successSet S k).card → f (x (k + 1)) - fstar ≤ κν * ε ^ ν := by
    intro k hk
    refine h.gap.le_of_linear_count hτ h.c_pos hεν hΓ0 ?_
    rw [hc]
    exact (Nat.le_ceil y).trans (by exact_mod_cast hk)
  obtain ⟨k, hk, hψ, hcard, hkle⟩ := ARSetting.exists_measure_le_nat h hε.le hgc
  have hnN : ((max ⌈y⌉₊ 1 + 1 : ℕ) : ℝ) ≤ max N 1 + 1 := by
    have hc : (⌈y⌉₊ : ℝ) ≤ max N 1 := by
      rcases le_or_gt y 0 with hy0 | hy0
      · rw [Nat.ceil_eq_zero.2 hy0, Nat.cast_zero]
        exact zero_le_one.trans (le_max_right _ _)
      · exact ((Nat.ceil_lt_add_one hy0.le).le.trans hyN).trans (le_max_left _ _)
    have : ((max ⌈y⌉₊ 1 : ℕ) : ℝ) ≤ max N 1 := by
      rw [Nat.cast_max, Nat.cast_one]; exact max_le hc (le_max_right _ _)
    push_cast at this ⊢
    linarith
  refine ⟨k, hk, hψ, (by exact_mod_cast hcard : ((successSet S k).card : ℝ) ≤
    ((max ⌈y⌉₊ 1 + 1 : ℕ) : ℝ)).trans hnN, hkle.trans ?_⟩
  have := mul_le_mul_of_nonneg_left hnN (by linarith [h.one_le_kappaR] : (0 : ℝ) ≤ κR)
  linarith


/-- **Theorem 5.3.5** of [cartis2022evaluation] (case $\nu > \mu$). Assume the standing hypotheses
of Section 5.3.2 and $\nu > \mu$. Let $\alpha = (\nu - \mu)/\mu$,
$c = \kappa_\nu/\kappa_\psi^{\nu/\mu}$ and
$$D = \min\left(\Gamma_0^{-\alpha}(2^\alpha - 1), \ \min(1, \alpha)\,c/2\right),$$
and let $\kappa^E = 1/D$ and $\kappa^F = -\kappa^E\Gamma_0^{-\alpha}$. Then:

* the gaps satisfy $\Gamma_{k+1} \le (\Gamma_0^{-\alpha} +
  D|\mathcal{S}_k|)^{-1/\alpha}$ for every $k$;
* for every $\epsilon > 0$, $\Gamma_{k+1} \le \epsilon$ for every $k$ with $|\mathcal{S}_k| \ge
  \kappa^E\epsilon^{-\alpha} + \kappa^F$ (5.3.25);
* for every $\epsilon > 0$, $\Gamma_{k+1} \le \epsilon$ for every $k \ge
  \kappa_R\kappa^E\epsilon^{-\alpha} + \kappa_R\kappa^F + \kappa_A$ (5.3.24);
* the measures converge to zero along the successful iterations: for every $\epsilon > 0$ there
  is $K$ such that $\psi(x_{k+1}) \le \epsilon$ for every successful $k \ge K$;
* for every $\epsilon > 0$, some successful iteration $k$ has $\psi(x_{k+1}) \le \epsilon$,
  $|\mathcal{S}_k| \le 2M + 2$ and $k \le \kappa_R(2M + 2) + \kappa_A$, where $M =
  D^{-\mu/\nu}\kappa_\nu^{-(\nu-\mu)/\nu}\epsilon^{-(\nu-\mu)}$ ((5.3.26)–(5.3.27)).

**Typo.** The constants of Appendix B are corrected. The constant $D$ is the corrected (B.5.15)
with $\beta = 1/2$, that is, $c\,\kappa_{\rm dom}$: it uses $\min(1, \alpha)$ in place of
$\alpha$, because (B.5.12) holds only for $\alpha \le 1$, and $\Gamma_0^{-\alpha}$ in place of
the printed $\kappa_\psi^{\nu/\mu}/\kappa_\nu$. The corrected halving argument gives $2M + 2$
successful iterations.

**Correction.** The rate bound and the stated convergence of the measures allow faster
convergence than the source's sublinear rate, as in `CartisGouldToint.Chapter05.lemma_5_3_1`.

**Generalization.** The appendix's constants use $\Gamma_0 > 0$. When $\Gamma_0 = 0$, every gap
vanishes, the bounds hold with the convention $0^{-\alpha} = 0$ (so $D = 0$), and the first
successful iteration satisfies the measure bound. -/
theorem theorem_5_3_5 (h : ARSetting f ψ fstar μ κψ κν ν κR κA x S) (hνμ : μ < ν) :
    (∀ k, f (x (k + 1)) - fstar ≤ ((f (x 0) - fstar) ^ (-((ν - μ) / μ)) +
      min ((f (x 0) - fstar) ^ (-((ν - μ) / μ)) * (2 ^ ((ν - μ) / μ) - 1))
        (min 1 ((ν - μ) / μ) * (κν / κψ ^ (ν / μ)) / 2) * (successSet S k).card) ^
          (-1 / ((ν - μ) / μ))) ∧
    (∀ ε, 0 < ε → ∀ k, 1 / min ((f (x 0) - fstar) ^ (-((ν - μ) / μ)) * (2 ^ ((ν - μ) / μ) - 1))
        (min 1 ((ν - μ) / μ) * (κν / κψ ^ (ν / μ)) / 2) * ε ^ (-((ν - μ) / μ)) +
        -(1 / min ((f (x 0) - fstar) ^ (-((ν - μ) / μ)) * (2 ^ ((ν - μ) / μ) - 1))
          (min 1 ((ν - μ) / μ) * (κν / κψ ^ (ν / μ)) / 2) * (f (x 0) - fstar) ^ (-((ν - μ) / μ)))
        ≤ (successSet S k).card → f (x (k + 1)) - fstar ≤ ε) ∧
    (∀ ε, 0 < ε → ∀ k : ℕ, κR * (1 / min ((f (x 0) - fstar) ^ (-((ν - μ) / μ)) *
          (2 ^ ((ν - μ) / μ) - 1)) (min 1 ((ν - μ) / μ) * (κν / κψ ^ (ν / μ)) / 2)) *
          ε ^ (-((ν - μ) / μ)) +
        (κR * -(1 / min ((f (x 0) - fstar) ^ (-((ν - μ) / μ)) * (2 ^ ((ν - μ) / μ) - 1))
          (min 1 ((ν - μ) / μ) * (κν / κψ ^ (ν / μ)) / 2) * (f (x 0) - fstar) ^ (-((ν - μ) / μ)))
          + κA) ≤ k → f (x (k + 1)) - fstar ≤ ε) ∧
    (∀ ε, 0 < ε → ∃ K, ∀ k ≥ K, S k → ψ (x (k + 1)) ≤ ε) ∧
    (∀ ε, 0 < ε → ∃ k, S k ∧ ψ (x (k + 1)) ≤ ε ∧
      ((successSet S k).card : ℝ) ≤
        2 * (min ((f (x 0) - fstar) ^ (-((ν - μ) / μ)) * (2 ^ ((ν - μ) / μ) - 1))
          (min 1 ((ν - μ) / μ) * (κν / κψ ^ (ν / μ)) / 2) ^ (-μ / ν) *
            κν ^ (-(ν - μ) / ν) * ε ^ (-(ν - μ))) + 2 ∧
      (k : ℝ) ≤ κR * (2 * (min ((f (x 0) - fstar) ^ (-((ν - μ) / μ)) * (2 ^ ((ν - μ) / μ) - 1))
          (min 1 ((ν - μ) / μ) * (κν / κψ ^ (ν / μ)) / 2) ^ (-μ / ν) *
            κν ^ (-(ν - μ) / ν) * ε ^ (-(ν - μ))) + 2) + κA) := by
  have hμ := h.mu_pos
  have hν := h.nu_pos
  have hα := sub_div_self_eq (ν := ν) hμ.ne'
  have hαpos : 0 < (ν - μ) / μ := div_pos (by linarith) hμ
  have hτ : 1 < ν / μ := (one_lt_div hμ).2 hνμ
  rcases (h.gap.nonneg 0).lt_or_eq with hΓ0 | hΓ0
  swap
  · -- the degenerate case `Γ_0 = 0`
    have hz := h.gap_eq_zero hΓ0.symm
    have hD : 0 ≤ min ((f (x 0) - fstar) ^ (-((ν - μ) / μ)) * (2 ^ ((ν - μ) / μ) - 1))
        (min 1 ((ν - μ) / μ) * (κν / κψ ^ (ν / μ)) / 2) := by
      rw [← hΓ0, Real.zero_rpow (neg_ne_zero.2 hαpos.ne'), zero_mul]
      exact le_min le_rfl (div_nonneg (mul_nonneg (le_min zero_le_one hαpos.le) h.c_pos.le)
        zero_le_two)
    refine ⟨fun k => ?_, fun ε hε k _ => by rw [hz]; exact hε.le,
      fun ε hε k _ => by rw [hz]; exact hε.le, fun ε hε => ?_, fun ε hε => ?_⟩
    · rw [hz]
      refine Real.rpow_nonneg (add_nonneg ?_ (mul_nonneg hD (Nat.cast_nonneg _))) _
      rw [← hΓ0, Real.zero_rpow (neg_ne_zero.2 hαpos.ne')]
    · have hεν : 0 < κν * ε ^ ν := mul_pos h.kappaNu_pos (Real.rpow_pos_of_pos hε _)
      obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_order.1 (lemma_5_3_1 h).2.1).2 _ hεν)
      exact ⟨K, fun k hk hSk => h.measure_le hSk hε.le (hK k hk).le⟩
    · obtain ⟨k, hk, hψ, hcard, hkle⟩ := h.exists_measure_le_of_gap_zero hΓ0.symm hε.le
      have hc : ((successSet S k).card : ℝ) ≤ 1 := by exact_mod_cast hcard
      have hM : 0 ≤ min ((f (x 0) - fstar) ^ (-((ν - μ) / μ)) * (2 ^ ((ν - μ) / μ) - 1))
          (min 1 ((ν - μ) / μ) * (κν / κψ ^ (ν / μ)) / 2) ^ (-μ / ν) *
            κν ^ (-(ν - μ) / ν) * ε ^ (-(ν - μ)) :=
        mul_nonneg (mul_nonneg (Real.rpow_nonneg hD _) (Real.rpow_nonneg h.kappaNu_pos.le _))
          (Real.rpow_nonneg hε.le _)
      refine ⟨k, hk, hψ, by linarith, hkle.trans ?_⟩
      nlinarith [h.one_le_kappaR]
  set α := (ν - μ) / μ with hαdef
  set c := κν / κψ ^ (ν / μ) with hcdef
  set Γ0 := f (x 0) - fstar with hΓ0def
  set D := min (Γ0 ^ (-α) * (2 ^ α - 1)) (min 1 α * c / 2) with hD
  have hDeq : c * IsImplicitGapDecrease.kappaDom c α Γ0 = D :=
    IsImplicitGapDecrease.mul_kappaDom h.c_pos
  have hDpos : 0 < D := by
    rw [← hDeq]; exact mul_pos h.c_pos (IsImplicitGapDecrease.kappaDom_pos h.c_pos hαpos hΓ0)
  -- the rate
  have hrate : ∀ k, f (x (k + 1)) - fstar ≤ (Γ0 ^ (-α) + D * (successSet S k).card) ^ (-1 / α) :=
    fun k => by
      have := h.gap.sublinear h.c_pos hτ hΓ0 k
      rw [hα] at this
      rw [← hDeq]
      exact this
  -- the gap count
  have hcount : ∀ ε, 0 < ε → ∀ k, 1 / D * ε ^ (-α) + -(1 / D * Γ0 ^ (-α)) ≤
      (successSet S k).card → f (x (k + 1)) - fstar ≤ ε := by
    intro ε hε k hk
    refine h.gap.le_of_sublinear_count h.c_pos hτ hΓ0 hε ?_
    rw [hα, hDeq, ← hΓ0def]
    refine le_trans (le_of_eq ?_) hk
    field_simp
    ring
  refine ⟨hrate, hcount, fun ε hε k hk => hcount ε hε k (h.le_card (by linarith)),
    fun ε hε => ?_, fun ε hε => ?_⟩
  · -- the measures converge to zero
    have hεν : 0 < κν * ε ^ ν := mul_pos h.kappaNu_pos (Real.rpow_pos_of_pos hε _)
    obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_order.1 (lemma_5_3_1 h).2.1).2 _ hεν)
    exact ⟨K, fun k hk hSk => h.measure_le hSk hε.le (hK k hk).le⟩
  · -- the halving argument
    have hα1 : α + 1 = ν / μ := by rw [hαdef]; field_simp; ring
    have e1 : -1 / (α + 1) = -μ / ν := by rw [hα1]; field_simp
    have e2 : -α / (α + 1) = -(ν - μ) / ν := by rw [hα1, hαdef]; field_simp
    have e3 : -ν * α / (α + 1) = -(ν - μ) := by rw [hα1, hαdef]; field_simp
    set M := D ^ (-1 / (α + 1)) * κν ^ (-α / (α + 1)) * ε ^ (-ν * α / (α + 1)) with hM
    have hM0 : 0 ≤ M := by have := hDpos; have := h.kappaNu_pos; positivity
    obtain ⟨k₀, hk₀⟩ := exists_le_card_successSet h.frequently (2 * (⌊M⌋₊ + 1))
    have hhalf := exists_le_of_halving (Γ := fun k => f (x k) - fstar) (S := S)
      (φ := fun k => ψ (x (k + 1))) hDpos hαpos h.kappaNu_pos hν hε h.gap.nonneg h.gap.eq_of_not
      (fun k hk => (hrate k).trans (Real.rpow_le_rpow_of_nonpos (by
          have : (1 : ℝ) ≤ (successSet S k).card := by exact_mod_cast hk
          positivity)
        (by have := Real.rpow_pos_of_pos hΓ0 (-α); linarith)
        (by rw [neg_div]; exact neg_nonpos.2 (div_nonneg zero_le_one hαpos.le))))
      (fun k hk => by have := h.run.decrease k hk; linarith) hk₀
    obtain ⟨j, -, hSj, hcard, hψ⟩ := hhalf
    rw [← hM] at hcard
    have hfloor : (2 * (⌊M⌋₊ + 1) : ℕ) ≤ 2 * M + 2 := by
      have := Nat.floor_le hM0
      push_cast; linarith
    have hcard' : ((successSet S j).card : ℝ) ≤ 2 * M + 2 :=
      (by exact_mod_cast hcard : ((successSet S j).card : ℝ) ≤ (2 * (⌊M⌋₊ + 1) : ℕ)).trans hfloor
    rw [hM, e1, e2, e3] at hcard'
    refine ⟨j, hSj, hψ, hcard', ?_⟩
    have := h.run.density j
    have : κR * ((successSet S j).card : ℝ) ≤ κR * (2 * (D ^ (-μ / ν) * κν ^ (-(ν - μ) / ν) *
        ε ^ (-(ν - μ))) + 2) := mul_le_mul_of_nonneg_left hcard' (by linarith [h.one_le_kappaR])
    linarith

end AR

/-! ### Trust-region-like methods -/

/-- The threshold $\Gamma_\square = (\kappa_\psi^{\nu/\mu}/\kappa_\nu)^{\mu/(\nu - \mu)}$ of Lemma
5.3.6 of [cartis2022evaluation], for $\nu \neq \mu$. For $\nu = \mu$ the exponent is $\mu/0 = 0$
by Lean's convention, and $\Gamma_\square = 1$. -/
noncomputable def gapBox (κψ κν μ ν : ℝ) : ℝ :=
  (κψ ^ (ν / μ) / κν) ^ (μ / (ν - μ))

/-- If $\kappa_\psi, \kappa_\nu, \mu > 0$ and $\nu \neq \mu$, then $\Gamma_\square = c^{-1/\alpha}$
with $c = \kappa_\nu/\kappa_\psi^{\nu/\mu}$ and $\alpha = \nu/\mu - 1$. -/
theorem gapBox_eq {κψ κν μ ν : ℝ} (hκψ : 0 < κψ) (hκν : 0 < κν) (hμ : 0 < μ) (hνμ : ν ≠ μ) :
    gapBox κψ κν μ ν = (κν / κψ ^ (ν / μ)) ^ (-1 / (ν / μ - 1)) := by
  have hc : 0 < κν / κψ ^ (ν / μ) := div_pos hκν (Real.rpow_pos_of_pos hκψ _)
  have h1 : κψ ^ (ν / μ) / κν = (κν / κψ ^ (ν / μ))⁻¹ := (inv_div _ _).symm
  have h2 : -1 / (ν / μ - 1) = -(μ / (ν - μ)) := by
    have : ν - μ ≠ 0 := sub_ne_zero.2 hνμ
    field_simp
  rw [gapBox, h1, Real.inv_rpow hc.le, h2, Real.rpow_neg hc.le]

/-- If $\kappa_\psi > 0$ and $\kappa_\nu > 0$, then $\Gamma_\square > 0$. -/
theorem gapBox_pos {κψ κν μ ν : ℝ} (hκψ : 0 < κψ) (hκν : 0 < κν) : 0 < gapBox κψ κν μ ν :=
  Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos hκψ _) hκν) _

/-- If $\kappa_\psi, \kappa_\nu, \mu > 0$ and $\nu \neq \mu$, then $c\,\Gamma_\square^\alpha = 1$
with $c = \kappa_\nu/\kappa_\psi^{\nu/\mu}$ and $\alpha = \nu/\mu - 1$. -/
theorem mul_gapBox_rpow {κψ κν μ ν : ℝ} (hκψ : 0 < κψ) (hκν : 0 < κν) (hμ : 0 < μ)
    (hνμ : ν ≠ μ) :
    κν / κψ ^ (ν / μ) * gapBox κψ κν μ ν ^ (ν / μ - 1) = 1 := by
  have hc : 0 < κν / κψ ^ (ν / μ) := div_pos hκν (Real.rpow_pos_of_pos hκψ _)
  have hα : ν / μ - 1 ≠ 0 := by
    rw [sub_ne_zero, ne_eq, div_eq_one_iff_eq hμ.ne']; exact hνμ
  rw [gapBox_eq hκψ hκν hμ hνμ, ← Real.rpow_mul hc.le, div_mul_cancel₀ _ hα, Real.rpow_neg_one,
    mul_inv_cancel₀ hc.ne']


namespace TRSetting

variable {f ψ : ℝⁿ → ℝ} {fstar μ κψ κν ν κR κA : ℝ} {x : ℕ → ℝⁿ} {S : ℕ → Prop}
  (h : TRSetting f ψ fstar μ κψ κν ν κR κA x S)
include h

/-- Under the standing hypotheses of Section 5.3.3, $\mu > 0$. -/
theorem mu_pos : 0 < μ := one_pos.trans_le h.one_le_mu

/-- Under the standing hypotheses of Section 5.3.3, $\nu > 0$. -/
theorem nu_pos : 0 < ν := one_pos.trans_le h.one_le_nu

/-- Under the standing hypotheses of Section 5.3.3, $c = \kappa_\nu/\kappa_\psi^{\nu/\mu} > 0$. -/
theorem c_pos : 0 < κν / κψ ^ (ν / μ) :=
  div_pos h.kappaNu_pos (Real.rpow_pos_of_pos h.kappaPsi_pos _)

/-- The recurrence (5.3.33). Under the standing hypotheses of Section 5.3.3, the gaps
$\Gamma_k = f(x_k) - f_*$ satisfy the explicit recurrence with
$c = \kappa_\nu/\kappa_\psi^{\nu/\mu}$ and $\tau = \nu/\mu$: $\Gamma_k \ge 0$,
$\Gamma_{k+1} = \Gamma_k$ at the unsuccessful iterations, and
$\Gamma_k - \Gamma_{k+1} \ge c\,\Gamma_k^\tau$ at the successful ones.

**Generalization.** Packages the same explicit recurrence under generalized run-local domination.
-/
theorem gap :
    IsExplicitGapDecrease (fun k => f (x k) - fstar) S (κν / κψ ^ (ν / μ)) (ν / μ) :=
  isExplicitGapDecrease_of_isTRLikeRun h.run h.psi_nonneg h.kappaPsi_pos h.mu_pos
    h.kappaNu_pos.le h.nu_pos.le h.dominated

/-- Under the standing hypotheses of Section 5.3.3, for every $N$ there is a successful iteration
$k \ge N$. -/
theorem frequently : ∀ N, ∃ k ≥ N, S k :=
  Optimization.frequently_of_density (by linarith [h.one_le_kappaR]) h.run.density

/-- Under the standing hypotheses of Section 5.3.3, if $\kappa_R N + \kappa_A \le k$, then
$N \le |\mathcal{S}_k|$, by (5.3.9). -/
theorem le_card {N : ℝ} {k : ℕ} (hk : κR * N + κA ≤ k) : N ≤ (successSet S k).card :=
  le_card_of_density (by linarith [h.one_le_kappaR]) h.run.density hk

/-- Measure counts from gap counts for TR methods. Assume the standing hypotheses of Section 5.3.3,
let $\epsilon \ge 0$ and $N \in \mathbb{R}$, and suppose that
$\Gamma_{k+1} \le \kappa_\nu \epsilon^\nu$ whenever $N \le |\mathcal{S}_k|$. Then there are
$i \le k$ with $k$ successful, $\psi(x_i) \le \epsilon$, $|\mathcal{S}_k| \le \max(N, 0) + 2$
and $k \le \kappa_R(\max(N, 0) + 2) + \kappa_A$.

**Reading.** Uses a past iterate attaining the minimum measure and includes the rounding allowance
for a real gap threshold.
-/
theorem exists_measure_le {ε N : ℝ} (hε : 0 ≤ ε)
    (hcount : ∀ k, N ≤ (successSet S k).card → f (x (k + 1)) - fstar ≤ κν * ε ^ ν) :
    ∃ i k, i ≤ k ∧ S k ∧ ψ (x i) ≤ ε ∧ ((successSet S k).card : ℝ) ≤ max N 0 + 2 ∧
      (k : ℝ) ≤ κR * (max N 0 + 2) + κA := by
  obtain ⟨k, hk, hφ, hcard⟩ := Optimization.exists_le_of_gap_count
    (φ := fun k => (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one (ψ ∘ x))
    (κν := κν) (ν := ν) h.gap.nonneg h.frequently hcount fun k hk => by
      have := h.run.decrease k hk; linarith
  obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_inf' (Finset.nonempty_range_add_one (n := k))
    (ψ ∘ x)
  refine ⟨i, k, Nat.lt_succ_iff.1 (Finset.mem_range.1 hi), hk, ?_, hcard, ?_⟩
  · have h3 : ((Finset.range (k + 1)).inf' Finset.nonempty_range_add_one (ψ ∘ x)) ^ ν ≤ ε ^ ν :=
      le_of_mul_le_mul_left hφ h.kappaNu_pos
    rw [hieq] at h3
    exact (Real.rpow_le_rpow_iff (h.psi_nonneg _) hε h.nu_pos).1 h3
  · have := h.run.density k
    have : κR * ((successSet S k).card : ℝ) ≤ κR * (max N 0 + 2) :=
      mul_le_mul_of_nonneg_left hcard (by linarith [h.one_le_kappaR])
    linarith

/-- Measure counts from integer gap counts for TR methods. Assume the standing hypotheses of Section
5.3.3, let $\epsilon \ge 0$ and $n \in \mathbb{N}$, and suppose that
$\Gamma_{k+1} \le \kappa_\nu \epsilon^\nu$ whenever $n \le |\mathcal{S}_k|$. Then there are
$i \le k$ with $k$ successful, $\psi(x_i) \le \epsilon$, $|\mathcal{S}_k| \le \max(n, 1) + 1$
and $k \le \kappa_R(\max(n, 1) + 1) + \kappa_A$.

**Reading.** Uses a past iterate attaining the minimum measure, with a natural-number threshold and
one further success.
-/
theorem exists_measure_le_nat {ε : ℝ} {n : ℕ} (hε : 0 ≤ ε)
    (hcount : ∀ k, n ≤ (successSet S k).card → f (x (k + 1)) - fstar ≤ κν * ε ^ ν) :
    ∃ i k, i ≤ k ∧ S k ∧ ψ (x i) ≤ ε ∧ (successSet S k).card ≤ max n 1 + 1 ∧
      (k : ℝ) ≤ κR * (max n 1 + 1 : ℕ) + κA := by
  obtain ⟨k, hk, hφ, hcard⟩ := Optimization.exists_le_of_gap_count_nat
    (φ := fun k => (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one (ψ ∘ x))
    (κν := κν) (ν := ν) h.gap.nonneg h.frequently hcount fun k hk => by
      have := h.run.decrease k hk; linarith
  obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_inf' (Finset.nonempty_range_add_one (n := k))
    (ψ ∘ x)
  refine ⟨i, k, Nat.lt_succ_iff.1 (Finset.mem_range.1 hi), hk, ?_, hcard, ?_⟩
  · have h3 : ((Finset.range (k + 1)).inf' Finset.nonempty_range_add_one (ψ ∘ x)) ^ ν ≤ ε ^ ν :=
      le_of_mul_le_mul_left hφ h.kappaNu_pos
    rw [hieq] at h3
    exact (Real.rpow_le_rpow_iff (h.psi_nonneg _) hε h.nu_pos).1 h3
  · have := h.run.density k
    have : κR * ((successSet S k).card : ℝ) ≤ κR * (max n 1 + 1 : ℕ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by linarith [h.one_le_kappaR])
    linarith

end TRSetting

section TR

variable {f ψ : ℝⁿ → ℝ} {fstar μ κψ κν ν κR κA : ℝ} {x : ℕ → ℝⁿ} {S : ℕ → Prop}

/-- **Lemma 5.3.6** of [cartis2022evaluation]. Assume the standing hypotheses of Section 5.3.3 and
$\Gamma_0 > 0$, and let $c = \kappa_\nu/\kappa_\psi^{\nu/\mu}$, $\alpha = (\nu - \mu)/\mu$ and
$\Gamma_\square = (\kappa_\psi^{\nu/\mu}/\kappa_\nu)^{\mu/(\nu-\mu)}$. Then every successful
iteration $k$ satisfies
$$0 \le \Gamma_{k+1} \le \Gamma_k\left(1 - c\,\Gamma_k^\alpha\right). \qquad (5.3.33)$$
Moreover:

* (i) if $\nu = \mu$, then $\kappa_\nu \le \kappa_\psi$; if $\kappa_\nu < \kappa_\psi$, the gaps
  converge linearly, $\Gamma_{k+1} \le (1 - \kappa_\nu/\kappa_\psi)\Gamma_k$ for every
  successful $k$; and if $\kappa_\nu = \kappa_\psi$, the gap vanishes after every successful
  iteration;
* (ii) if $\nu < \mu$, then $\Gamma_0 \ge \Gamma_\square$ (5.3.29); if
  $\Gamma_0 = \Gamma_\square$, the gap vanishes after every successful iteration; every
  successful $k$ has $\Gamma_k = 0$ or $\Gamma_k \ge \Gamma_\square$ (5.3.31); and the gap
  vanishes from some iteration on;
* (iii) if $\nu > \mu$, then $\Gamma_0 \le \Gamma_\square$ (5.3.32); if
  $\Gamma_0 = \Gamma_\square$, the gap vanishes after every successful iteration;
  $\Gamma_k \to 0$; and $\Gamma_{k+1} \le (\Gamma_0^{-\alpha} + \alpha
  c|\mathcal{S}_k|)^{-1/\alpha}$ for every $k$.

**Correction.** Part (iii) gives a polynomial upper bound. The decrease condition
also permits faster convergence. For instance, with $\mu=1$, $\nu=2$ and every
iteration successful, $\Gamma_k=\psi(x_k)=2^{-k}$ satisfies (5.3.1) and (5.3.28)
with $\kappa_\psi=1$ and $\kappa_\nu=1/2$.

**Typo.** In (ii) the book writes "a final value $\Gamma_{k_\square} \ge 1$". This means
$\Gamma_{k_\square} \ge \Gamma_\square$, that is, $\omega \ge 1$ for the scaled gap
$\omega = \Gamma/\Gamma_\square$.

In the equality cases the gap vanishes after every successful iteration, in particular after the
first one, as the book states. The threshold $\Gamma_\square$ is
`CartisGouldToint.Chapter05.gapBox κψ κν μ ν`. -/
theorem lemma_5_3_6 (h : TRSetting f ψ fstar μ κψ κν ν κR κA x S)
    (hΓ0 : 0 < f (x 0) - fstar) :
    (∀ k, S k → 0 ≤ f (x (k + 1)) - fstar ∧ f (x (k + 1)) - fstar ≤
      (f (x k) - fstar) * (1 - κν / κψ ^ (ν / μ) * (f (x k) - fstar) ^ ((ν - μ) / μ))) ∧
    (ν = μ → κν ≤ κψ ∧
      (κν < κψ → ∀ k, S k → f (x (k + 1)) - fstar ≤ (1 - κν / κψ) * (f (x k) - fstar)) ∧
      (κν = κψ → ∀ k, S k → f (x (k + 1)) - fstar = 0)) ∧
    (ν < μ → gapBox κψ κν μ ν ≤ f (x 0) - fstar ∧
      (f (x 0) - fstar = gapBox κψ κν μ ν → ∀ k, S k → f (x (k + 1)) - fstar = 0) ∧
      (∀ k, S k → f (x k) - fstar = 0 ∨ gapBox κψ κν μ ν ≤ f (x k) - fstar) ∧
      ∃ K, ∀ k ≥ K, f (x k) - fstar = 0) ∧
    (μ < ν → f (x 0) - fstar ≤ gapBox κψ κν μ ν ∧
      (f (x 0) - fstar = gapBox κψ κν μ ν → ∀ k, S k → f (x (k + 1)) - fstar = 0) ∧
      Tendsto (fun k => f (x k) - fstar) atTop (𝓝 0) ∧
      ∀ k, f (x (k + 1)) - fstar ≤ ((f (x 0) - fstar) ^ (-((ν - μ) / μ)) +
        (ν - μ) / μ * (κν / κψ ^ (ν / μ)) * (successSet S k).card) ^ (-1 / ((ν - μ) / μ))) := by
  have hμ := h.mu_pos
  have hν := h.nu_pos
  have hα := sub_div_self_eq (ν := ν) hμ.ne'
  have hc := h.c_pos
  have hτ0 : 0 < ν / μ := div_pos hν hμ
  have hS : ∃ k, S k := (h.frequently 0).imp fun _ hk => hk.2
  have hone := h.gap.mul_rpow_le_one hc.le hS hΓ0
  refine ⟨fun k hk => ⟨h.gap.nonneg (k + 1), ?_⟩, fun hνμ => ?_, fun hνμ => ?_, fun hνμ => ?_⟩
  · have := h.gap.le_mul hc.le hk
    rwa [hα] at this
  · -- (i)
    have hτ : ν / μ = 1 := by rw [hνμ, div_self hμ.ne']
    have hc1 : κν / κψ ^ (ν / μ) = κν / κψ := by rw [hτ, Real.rpow_one]
    rw [hc1, hτ, sub_self, Real.rpow_zero, mul_one] at hone
    have hle : κν ≤ κψ := by rwa [div_le_one h.kappaPsi_pos] at hone
    refine ⟨hle, fun hlt k hk => ?_, fun heq => ?_⟩
    · have := h.gap.le_mul hc.le hk
      rw [hc1, hτ, sub_self, Real.rpow_zero, mul_one] at this
      linarith
    · refine h.gap.eq_zero_of_one_le_mul_rpow hc.le hΓ0 ?_
      show 1 ≤ κν / κψ ^ (ν / μ) * (f (x 0) - fstar) ^ (ν / μ - 1)
      rw [hc1, hτ, sub_self, Real.rpow_zero, mul_one, heq, div_self h.kappaPsi_pos.ne']
  · -- (ii)
    have hτ1 : ν / μ < 1 := (div_lt_one hμ).2 hνμ
    obtain ⟨p1, p2, p3⟩ := h.gap.eq_zero_of_lt_one hc hτ1
    rw [← gapBox_eq h.kappaPsi_pos h.kappaNu_pos hμ hνμ.ne] at p1 p2 p3
    obtain ⟨k₀, hk₀⟩ := hS
    refine ⟨p2 hΓ0 k₀ hk₀, fun heq => h.gap.eq_zero_of_one_le_mul_rpow hc.le hΓ0 ?_,
      fun k hk => ?_, ?_⟩
    · show 1 ≤ κν / κψ ^ (ν / μ) * (f (x 0) - fstar) ^ (ν / μ - 1)
      rw [heq, mul_gapBox_rpow h.kappaPsi_pos h.kappaNu_pos hμ hνμ.ne]
    · rcases (h.gap.nonneg k).lt_or_eq with hpos | hzero
      · exact Or.inr (p1 k hk hpos)
      · exact Or.inl hzero.symm
    · obtain ⟨k, hk⟩ := exists_le_card_successSet h.frequently
        (⌈Real.log ((f (x 0) - fstar) / gapBox κψ κν μ ν) /
          |Real.log (1 - ((f (x 0) - fstar) / gapBox κψ κν μ ν) ^ (ν / μ - 1))|⌉₊ + 1)
      have hz := p3 hΓ0 k hk
      refine ⟨k + 1, fun j hj => le_antisymm ?_ (h.gap.nonneg j)⟩
      have hanti : Antitone (fun k => f (x k) - fstar) :=
        antitone_nat_of_succ_le (h.gap.le_self hc.le)
      exact (hanti hj).trans hz.le
  · -- (iii)
    have hτ1 : 1 < ν / μ := (one_lt_div hμ).2 hνμ
    have hαpos : 0 < ν / μ - 1 := by linarith
    have hbox := gapBox_eq h.kappaPsi_pos h.kappaNu_pos hμ hνμ.ne'
    refine ⟨?_, fun heq => h.gap.eq_zero_of_one_le_mul_rpow hc.le hΓ0 ?_,
      (h.gap.toImplicit hc.le hτ0.le).tendsto_zero hc hτ0 h.frequently, fun k => ?_⟩
    · -- `c Γ_0^α ≤ 1` gives `Γ_0 ≤ c^{-1/α}`
      rw [hbox]
      have h1 : (f (x 0) - fstar) ^ (ν / μ - 1) ≤ (κν / κψ ^ (ν / μ))⁻¹ := by
        rw [← one_div, le_div_iff₀ hc, mul_comm]; exact hone
      calc f (x 0) - fstar = ((f (x 0) - fstar) ^ (ν / μ - 1)) ^ (1 / (ν / μ - 1)) := by
            rw [← Real.rpow_mul hΓ0.le, mul_one_div_cancel hαpos.ne', Real.rpow_one]
        _ ≤ ((κν / κψ ^ (ν / μ))⁻¹) ^ (1 / (ν / μ - 1)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hΓ0.le _) h1 (by positivity)
        _ = _ := by rw [Real.inv_rpow hc.le, ← Real.rpow_neg hc.le, neg_div]
    · show 1 ≤ κν / κψ ^ (ν / μ) * (f (x 0) - fstar) ^ (ν / μ - 1)
      rw [heq, mul_gapBox_rpow h.kappaPsi_pos h.kappaNu_pos hμ hνμ.ne']
    · -- the sublinear rate (mean-value form, as in the proof of Theorem 5.3.9)
      have hbound := add_mul_card_le_rpow_neg (Γ := fun k => f (x k) - fstar)
        (h.gap.le_self hc.le) h.gap.eq_of_not
        (fun k hk hpos => h.gap.mul_le_sub hc hτ1 hk hpos) k
      rw [hα] at hbound
      have hαpos' : 0 < (ν - μ) / μ := hα ▸ hαpos
      rcases (h.gap.nonneg (k + 1)).lt_or_eq with hpos | hzero
      · have hB : 0 < (f (x 0) - fstar) ^ (-((ν - μ) / μ)) +
            (ν - μ) / μ * (κν / κψ ^ (ν / μ)) * (successSet S k).card := by
          have := Real.rpow_pos_of_pos hΓ0 (-((ν - μ) / μ))
          positivity
        calc f (x (k + 1)) - fstar =
              ((f (x (k + 1)) - fstar) ^ (-((ν - μ) / μ))) ^ (-1 / ((ν - μ) / μ)) := by
              rw [← Real.rpow_mul hpos.le]
              rw [show -((ν - μ) / μ) * (-1 / ((ν - μ) / μ)) = 1 by
                have : ν - μ ≠ 0 := sub_ne_zero.2 hνμ.ne'
                field_simp [this],
                Real.rpow_one]
          _ ≤ _ := Real.rpow_le_rpow_of_nonpos hB (hbound hpos) (by
              rw [neg_div]; exact neg_nonpos.2 (div_nonneg zero_le_one hαpos'.le))
      · rw [← hzero]
        exact Real.rpow_nonneg (by
          have := Real.rpow_nonneg hΓ0.le (-((ν - μ) / μ))
          positivity) _

/-- **Theorem 5.3.7** of [cartis2022evaluation] (case $\nu < \mu$). Assume the standing hypotheses
of Section 5.3.3, $\nu < \mu$ and $\Gamma_0 > 0$. Let $\omega_0 = \Gamma_0/\Gamma_\square$ and
$$\kappa^F = \left\lceil \frac{\log\omega_0}{|\log(1 - \omega_0^{(\nu-\mu)/\mu})|}
  \right\rceil_+ + 1,$$
where $\lceil t \rceil_+$ is the least natural number $n \ge t$. Then:

* the gap vanishes, $\Gamma_{k+1} = 0$, for every $k$ with $|\mathcal{S}_k| \ge \kappa^F$
  (5.3.36);
* $\Gamma_{k+1} = 0$ for every $k \ge \kappa_R\kappa^F + \kappa_A$ (5.3.35);
* some iterate $x_i$ has $\psi(x_i) = 0$, where $i \le k$ for a successful iteration $k$ with
  $|\mathcal{S}_k| \le \kappa^F + 1$ and $k \le \kappa_R(\kappa^F + 1) + \kappa_A$
  ((5.3.37)–(5.3.38)).

**Reading.** The constant $\kappa^F$ is an integer form of the book's
$\kappa^F_{\mathrm{TR},1}$.

**Correction.** The book writes $\psi(x_k) = 0$. The gap vanishes at $x_k$, and (5.3.28) then
forces only $\min_{i \le k}\psi(x_i) = 0$, so the iterate reached is $x_i$ with $i \le k$.

The ceiling $\lceil \cdot \rceil_+$ is `Nat.ceil`. -/
theorem theorem_5_3_7 (h : TRSetting f ψ fstar μ κψ κν ν κR κA x S) (hνμ : ν < μ)
    (hΓ0 : 0 < f (x 0) - fstar) :
    (∀ k, ((⌈Real.log ((f (x 0) - fstar) / gapBox κψ κν μ ν) /
        |Real.log (1 - ((f (x 0) - fstar) / gapBox κψ κν μ ν) ^ ((ν - μ) / μ))|⌉₊ + 1 : ℕ) : ℝ) ≤
          (successSet S k).card → f (x (k + 1)) - fstar = 0) ∧
    (∀ k : ℕ, κR * ((⌈Real.log ((f (x 0) - fstar) / gapBox κψ κν μ ν) /
        |Real.log (1 - ((f (x 0) - fstar) / gapBox κψ κν μ ν) ^ ((ν - μ) / μ))|⌉₊ + 1 : ℕ) : ℝ) +
          κA ≤ k → f (x (k + 1)) - fstar = 0) ∧
    ∃ i k, i ≤ k ∧ S k ∧ ψ (x i) = 0 ∧
      (successSet S k).card ≤ (⌈Real.log ((f (x 0) - fstar) / gapBox κψ κν μ ν) /
        |Real.log (1 - ((f (x 0) - fstar) / gapBox κψ κν μ ν) ^ ((ν - μ) / μ))|⌉₊ + 1) + 1 ∧
      (k : ℝ) ≤ κR * (((⌈Real.log ((f (x 0) - fstar) / gapBox κψ κν μ ν) /
        |Real.log (1 - ((f (x 0) - fstar) / gapBox κψ κν μ ν) ^ ((ν - μ) / μ))|⌉₊ + 1 : ℕ) : ℝ) +
          1) + κA := by
  have hμ := h.mu_pos
  have hα := sub_div_self_eq (ν := ν) hμ.ne'
  have hτ1 : ν / μ < 1 := (div_lt_one hμ).2 hνμ
  obtain ⟨-, -, p3⟩ := h.gap.eq_zero_of_lt_one h.c_pos hτ1
  rw [← gapBox_eq h.kappaPsi_pos h.kappaNu_pos hμ hνμ.ne, hα] at p3
  have hcount : ∀ k, ((⌈Real.log ((f (x 0) - fstar) / gapBox κψ κν μ ν) /
      |Real.log (1 - ((f (x 0) - fstar) / gapBox κψ κν μ ν) ^ ((ν - μ) / μ))|⌉₊ + 1 : ℕ) : ℝ) ≤
        (successSet S k).card → f (x (k + 1)) - fstar = 0 :=
    fun k hk => p3 hΓ0 k (by exact_mod_cast hk)
  refine ⟨hcount, fun k hk => hcount k (h.le_card hk), ?_⟩
  obtain ⟨i, k, hik, hSk, hψ, hcard, hkle⟩ := h.exists_measure_le_nat le_rfl fun k hk => by
    rw [hcount k (by exact_mod_cast hk), Real.zero_rpow h.nu_pos.ne', mul_zero]
  rw [max_eq_left (by omega)] at hcard hkle
  refine ⟨i, k, hik, hSk, le_antisymm hψ (h.psi_nonneg _), hcard, hkle.trans_eq ?_⟩
  push_cast; ring

/-- **Theorem 5.3.8** of [cartis2022evaluation] (case $\nu = \mu$). Assume the standing hypotheses
of Section 5.3.3, $\nu = \mu$ and $\Gamma_0 > 0$. If $\kappa_\nu = \kappa_\psi$, the gap
vanishes after every successful iteration. If $\kappa_\nu < \kappa_\psi$, let $\kappa^E =
1/|\log(1 - \kappa_\nu/\kappa_\psi)|$ and $\kappa^F = \log\Gamma_0/|\log(1 -
\kappa_\nu/\kappa_\psi)|$. Then:

* the gaps converge linearly: $\Gamma_{k+1} \le (1 - \kappa_\nu/\kappa_\psi)\Gamma_k$ for every
  successful $k$;
* for every $\epsilon > 0$, $\Gamma_{k+1} \le \epsilon$ for every $k$ with $|\mathcal{S}_k| \ge
  \kappa^E|\log\epsilon| + \kappa^F$ (5.3.40);
* for every $\epsilon > 0$, $\Gamma_{k+1} \le \epsilon$ for every $k \ge
  \kappa_R\kappa^E|\log\epsilon| + \kappa_R\kappa^F + \kappa_A$ (5.3.39);
* for every $\epsilon > 0$, some iterate $x_i$ has $\psi(x_i) \le \epsilon$, where $i \le k$ for
  a successful iteration $k$ with $|\mathcal{S}_k| \le M$ and $k \le \kappa_R M + \kappa_A$, and
  $M = \max(\nu\kappa^E|\log\epsilon| + \kappa^E|\log\kappa_\nu| + \kappa^F, 0) + 2$
  ((5.3.41)–(5.3.42)).

**Correction.** The book writes the measure bound for $x_k$; here the iterate is $x_i$ with
$i \le k$.

The book's $\kappa^F$ has no ceiling term, hence the $+2$ in $M$. By Lemma 5.3.6 (i),
$\kappa_\nu \le \kappa_\psi$, so the two cases cover all runs. -/
theorem theorem_5_3_8 (h : TRSetting f ψ fstar μ κψ κν ν κR κA x S) (hνμ : ν = μ)
    (hΓ0 : 0 < f (x 0) - fstar) :
    (κν = κψ → ∀ k, S k → f (x (k + 1)) - fstar = 0) ∧
    (κν < κψ →
      (∀ k, S k → f (x (k + 1)) - fstar ≤ (1 - κν / κψ) * (f (x k) - fstar)) ∧
      (∀ ε, 0 < ε → ∀ k, 1 / |Real.log (1 - κν / κψ)| * |Real.log ε| +
          Real.log (f (x 0) - fstar) / |Real.log (1 - κν / κψ)| ≤ (successSet S k).card →
        f (x (k + 1)) - fstar ≤ ε) ∧
      (∀ ε, 0 < ε → ∀ k : ℕ, κR * (1 / |Real.log (1 - κν / κψ)|) * |Real.log ε| +
          (κR * (Real.log (f (x 0) - fstar) / |Real.log (1 - κν / κψ)|) + κA) ≤ k →
        f (x (k + 1)) - fstar ≤ ε) ∧
      (∀ ε, 0 < ε → ∃ i k, i ≤ k ∧ S k ∧ ψ (x i) ≤ ε ∧
        ((successSet S k).card : ℝ) ≤ max (ν * (1 / |Real.log (1 - κν / κψ)|) * |Real.log ε| +
          (1 / |Real.log (1 - κν / κψ)| * |Real.log κν| +
            Real.log (f (x 0) - fstar) / |Real.log (1 - κν / κψ)|)) 0 + 2 ∧
        (k : ℝ) ≤ κR * (max (ν * (1 / |Real.log (1 - κν / κψ)|) * |Real.log ε| +
          (1 / |Real.log (1 - κν / κψ)| * |Real.log κν| +
            Real.log (f (x 0) - fstar) / |Real.log (1 - κν / κψ)|)) 0 + 2) + κA)) := by
  have hμ := h.mu_pos
  obtain ⟨-, hi, -, -⟩ := lemma_5_3_6 h hΓ0
  obtain ⟨-, hlin, heq⟩ := hi hνμ
  have hτ : ν / μ = 1 := by rw [hνμ, div_self hμ.ne']
  have hc : κν / κψ ^ (ν / μ) = κν / κψ := by rw [hτ, Real.rpow_one]
  refine ⟨heq, fun hlt => ?_⟩
  have hc1 : κν / κψ < 1 := (div_lt_one h.kappaPsi_pos).2 hlt
  have hcpos : 0 < κν / κψ := div_pos h.kappaNu_pos h.kappaPsi_pos
  have hL : 0 < |Real.log (1 - κν / κψ)| :=
    abs_pos.2 (Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith))
  set Γ0 := f (x 0) - fstar
  have hcount : ∀ ε, 0 < ε → ∀ k, 1 / |Real.log (1 - κν / κψ)| * |Real.log ε| +
      Real.log Γ0 / |Real.log (1 - κν / κψ)| ≤ (successSet S k).card →
      f (x (k + 1)) - fstar ≤ ε := by
    intro ε hε k hk
    refine h.gap.le_of_linear_count hτ h.c_pos (hc ▸ hc1) hε hΓ0 ?_
    rw [hc]
    refine le_trans ?_ hk
    have : -Real.log ε ≤ |Real.log ε| := neg_le_abs _
    have : -Real.log ε / |Real.log (1 - κν / κψ)| ≤ |Real.log ε| / |Real.log (1 - κν / κψ)| :=
      div_le_div_of_nonneg_right this hL.le
    rw [sub_div, one_div_mul_eq_div, sub_eq_add_neg, ← neg_div]
    linarith
  refine ⟨hlin hlt, hcount, fun ε hε k hk => hcount ε hε k (h.le_card (by linarith)),
    fun ε hε => ?_⟩
  have hεν : 0 < κν * ε ^ ν := mul_pos h.kappaNu_pos (Real.rpow_pos_of_pos hε _)
  obtain ⟨i, k, hik, hSk, hψ, hcard, hkle⟩ := h.exists_measure_le hε.le
    (N := ν * (1 / |Real.log (1 - κν / κψ)|) * |Real.log ε| +
      (1 / |Real.log (1 - κν / κψ)| * |Real.log κν| + Real.log Γ0 / |Real.log (1 - κν / κψ)|))
    fun k hk => hcount _ hεν k (le_trans (by
      have hlog : |Real.log (κν * ε ^ ν)| ≤ |Real.log κν| + ν * |Real.log ε| := by
        rw [Real.log_mul h.kappaNu_pos.ne' (Real.rpow_pos_of_pos hε _).ne', Real.log_rpow hε]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos h.nu_pos]
      have := mul_le_mul_of_nonneg_left hlog (one_div_pos.2 hL).le
      nlinarith) hk)
  exact ⟨i, k, hik, hSk, hψ, hcard, hkle⟩

/-- **Theorem 5.3.9** of [cartis2022evaluation] (case $\nu > \mu$). Assume the standing hypotheses
of Section 5.3.3, $\nu > \mu$ and $\Gamma_0 > 0$, and let $\alpha = (\nu - \mu)/\mu$ and
$c = \kappa_\nu/\kappa_\psi^{\nu/\mu}$. Let $\kappa^E = \mu\kappa_\psi^{\nu/\mu}/((\nu -
\mu)\kappa_\nu) = 1/(\alpha c)$ and $\kappa^F = -\kappa^E\Gamma_0^{-\alpha}$. Then:

* the gaps have the polynomial upper bound from Lemma 5.3.6 (iii): $\Gamma_{k+1} \le
  (\Gamma_0^{-\alpha} + \alpha c|\mathcal{S}_k|)^{-1/\alpha}$ for every $k$;
* for every $\epsilon > 0$, $\Gamma_{k+1} \le \epsilon$ for every $k$ with $|\mathcal{S}_k| \ge
  \kappa^E\epsilon^{-\alpha} + \kappa^F$ (5.3.43);
* for every $\epsilon > 0$, $\Gamma_{k+1} \le \epsilon$ for every $k \ge
  \kappa_R\kappa^E\epsilon^{-\alpha} + \kappa_R\kappa^F + \kappa_A$;
* for every $\epsilon > 0$, some iterate $x_i$ has $\psi(x_i) \le \epsilon$, where $i \le j$ for
  a successful iteration $j$ with $|\mathcal{S}_j| \le 2M + 2$ and
  $j \le \kappa_R(2M + 2) + \kappa_A$, and $M = (\alpha
  c)^{-\mu/\nu}\kappa_\nu^{-(\nu-\mu)/\nu}\epsilon^{-(\nu-\mu)}$, by a halving argument.

**Typo.** The book prints the exponent $\mu/\nu$ in $\kappa^E$, and $\kappa^B$ in place of
$\kappa^F$.

**Correction.** The book writes the measure bound for $x_k$; here the iterate is $x_i$ with
$i \le j$. The source also asserts sublinear convergence of the individual measures at
successful iterates. The decrease controls only their running minimum, which can tend
to zero while individual measures fail to converge. For example, take every iteration
successful, $\Gamma_k=2^{-k}$, $\psi(x_k)=2^{-k}$ at even $k$ and $\psi(x_k)=1$ at odd $k$.
These values satisfy (5.3.1) and (5.3.28) with $\mu=1$, $\nu=2$, $\kappa_\psi=1$ and
$\kappa_\nu=1/4$. -/
theorem theorem_5_3_9 (h : TRSetting f ψ fstar μ κψ κν ν κR κA x S) (hνμ : μ < ν)
    (hΓ0 : 0 < f (x 0) - fstar) :
    (∀ k, f (x (k + 1)) - fstar ≤ ((f (x 0) - fstar) ^ (-((ν - μ) / μ)) +
        (ν - μ) / μ * (κν / κψ ^ (ν / μ)) * (successSet S k).card) ^ (-1 / ((ν - μ) / μ))) ∧
    (∀ ε, 0 < ε → ∀ k, μ * κψ ^ (ν / μ) / ((ν - μ) * κν) * ε ^ (-((ν - μ) / μ)) +
        -(μ * κψ ^ (ν / μ) / ((ν - μ) * κν) * (f (x 0) - fstar) ^ (-((ν - μ) / μ))) ≤
          (successSet S k).card → f (x (k + 1)) - fstar ≤ ε) ∧
    (∀ ε, 0 < ε → ∀ k : ℕ, κR * (μ * κψ ^ (ν / μ) / ((ν - μ) * κν)) * ε ^ (-((ν - μ) / μ)) +
        (κR * -(μ * κψ ^ (ν / μ) / ((ν - μ) * κν) * (f (x 0) - fstar) ^ (-((ν - μ) / μ))) + κA) ≤
          k → f (x (k + 1)) - fstar ≤ ε) ∧
    (∀ ε, 0 < ε → ∃ i j, i ≤ j ∧ S j ∧ ψ (x i) ≤ ε ∧
      ((successSet S j).card : ℝ) ≤ 2 * (((ν - μ) / μ * (κν / κψ ^ (ν / μ))) ^ (-μ / ν) *
        κν ^ (-(ν - μ) / ν) * ε ^ (-(ν - μ))) + 2 ∧
      (j : ℝ) ≤ κR * (2 * (((ν - μ) / μ * (κν / κψ ^ (ν / μ))) ^ (-μ / ν) *
        κν ^ (-(ν - μ) / ν) * ε ^ (-(ν - μ))) + 2) + κA) := by
  have hμ := h.mu_pos
  have hν := h.nu_pos
  have hα := sub_div_self_eq (ν := ν) hμ.ne'
  have hαpos : 0 < (ν - μ) / μ := div_pos (by linarith) hμ
  have hτ : 1 < ν / μ := (one_lt_div hμ).2 hνμ
  obtain ⟨-, -, -, hiii⟩ := lemma_5_3_6 h hΓ0
  obtain ⟨-, -, -, hrate'⟩ := hiii hνμ
  set α := (ν - μ) / μ with hαdef
  set c := κν / κψ ^ (ν / μ) with hcdef
  set Γ0 := f (x 0) - fstar with hΓ0def
  have hκE : μ * κψ ^ (ν / μ) / ((ν - μ) * κν) = 1 / (α * c) := by
    have := h.kappaNu_pos.ne'
    have := (Real.rpow_pos_of_pos h.kappaPsi_pos (ν / μ)).ne'
    have : ν - μ ≠ 0 := by linarith
    rw [hαdef, hcdef]; field_simp
  have hA : 0 < α * c := mul_pos hαpos h.c_pos
  have hcount : ∀ ε, 0 < ε → ∀ k, μ * κψ ^ (ν / μ) / ((ν - μ) * κν) * ε ^ (-α) +
      -(μ * κψ ^ (ν / μ) / ((ν - μ) * κν) * Γ0 ^ (-α)) ≤ (successSet S k).card →
      f (x (k + 1)) - fstar ≤ ε := by
    intro ε hε k hk
    refine h.gap.le_of_sublinear_count h.c_pos hτ hε ?_
    rw [hα, ← hΓ0def]
    refine le_trans (le_of_eq ?_) hk
    rw [hκE]
    ring
  refine ⟨hrate', hcount, fun ε hε k hk => hcount ε hε k (h.le_card (by linarith)),
    fun ε hε => ?_⟩
  -- the halving argument with `φ_k = min_{i ≤ k} ψ(x_i)`
  have hα1 : α + 1 = ν / μ := by rw [hαdef]; field_simp; ring
  have e1 : -1 / (α + 1) = -μ / ν := by rw [hα1]; field_simp
  have e2 : -α / (α + 1) = -(ν - μ) / ν := by rw [hα1, hαdef]; field_simp
  have e3 : -ν * α / (α + 1) = -(ν - μ) := by rw [hα1, hαdef]; field_simp
  set M := (α * c) ^ (-1 / (α + 1)) * κν ^ (-α / (α + 1)) * ε ^ (-ν * α / (α + 1)) with hM
  have hM0 : 0 ≤ M := by have := h.kappaNu_pos; positivity
  obtain ⟨k₀, hk₀⟩ := exists_le_card_successSet h.frequently (2 * (⌊M⌋₊ + 1))
  have hhalf := exists_le_of_halving (Γ := fun k => f (x k) - fstar) (S := S)
    (φ := fun k => (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one (ψ ∘ x))
    hA hαpos h.kappaNu_pos hν hε h.gap.nonneg h.gap.eq_of_not
    (fun k hk => (hrate' k).trans (Real.rpow_le_rpow_of_nonpos (by
        have : (1 : ℝ) ≤ (successSet S k).card := by exact_mod_cast hk
        positivity)
      (by have := Real.rpow_pos_of_pos hΓ0 (-α); linarith)
      (by rw [neg_div]; exact neg_nonpos.2 (div_nonneg zero_le_one hαpos.le))))
    (fun k hk => by have := h.run.decrease k hk; linarith) hk₀
  obtain ⟨j, -, hSj, hcard, hφ⟩ := hhalf
  rw [← hM] at hcard
  obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_inf' (Finset.nonempty_range_add_one (n := j))
    (ψ ∘ x)
  have hψ : ψ (x i) ≤ ε := by
    have : ((Finset.range (j + 1)).inf' Finset.nonempty_range_add_one (ψ ∘ x)) ≤ ε := hφ
    rwa [hieq] at this
  have hfloor : (2 * (⌊M⌋₊ + 1) : ℕ) ≤ 2 * M + 2 := by
    have := Nat.floor_le hM0
    push_cast; linarith
  have hcard' : ((successSet S j).card : ℝ) ≤ 2 * M + 2 :=
    (by exact_mod_cast hcard : ((successSet S j).card : ℝ) ≤ (2 * (⌊M⌋₊ + 1) : ℕ)).trans hfloor
  rw [hM, e1, e2, e3] at hcard'
  refine ⟨i, j, Nat.lt_succ_iff.1 (Finset.mem_range.1 hi), hSj, hψ, hcard', ?_⟩
  have := h.run.density j
  have : κR * ((successSet S j).card : ℝ) ≤ κR * (2 * ((α * c) ^ (-μ / ν) *
      κν ^ (-(ν - μ) / ν) * ε ^ (-(ν - μ))) + 2) :=
    mul_le_mul_of_nonneg_left hcard' (by linarith [h.one_le_kappaR])
  linarith

end TR

/-! ### Uniformly full-rank least squares -/

section LeastSquares

variable {m : ℕ} {r : ℝⁿ → EuclideanSpace ℝ (Fin m)}

/-- **Equations (5.3.2)–(5.3.3)** of [cartis2022evaluation], Sections 5.3.1 and 5.3.4. Let
$r : \mathbb{R}^n \to \mathbb{R}^m$, $\ell > 1$, $\psi_{\min} > 0$ and
$A \subseteq \mathbb{R}^n$, and suppose that the full-rank condition (5.1.62)
$\psi_{\ell,1}(x) \ge \psi_{\min}$ holds at every $x \in A$ with $r(x) \neq 0$. Then $\Phi_\ell$
is dominated on $A$ for the measure $\|\nabla\Phi_\ell\|$, with the reference value $0$, the
level $\mu = \ell/(\ell - 1)$ and the constant $\kappa_\psi =
\psi_{\min}^{-\ell/(\ell-1)}/\ell$: for every $x \in A$,
$$0 \le \Phi_\ell(x) \le \kappa_\psi \|\nabla\Phi_\ell(x)\|^{\ell/(\ell-1)}.$$

**Generalization.** The book also claims $\min \Phi_\ell = 0$. Only the reference value $0$ is
needed. -/
theorem Phi_isMeasureDominated {ℓ ψmin : ℝ} {A : Set ℝⁿ} (hℓ : 1 < ℓ) (hψ : 0 < ψmin)
    (h : ∀ y ∈ A, r y ≠ 0 → ψmin ≤ psiOne r ℓ y) :
    IsMeasureDominated (Phi r ℓ) (fun y => ‖gradient (Phi r ℓ) y‖) 0 (ℓ / (ℓ - 1))
      (ψmin ^ (-(ℓ / (ℓ - 1))) / ℓ) A := by
  have key : ∀ y ∈ A, ψmin * ‖r y‖ ^ (ℓ - 1) ≤ ‖fderiv ℝ (Phi r ℓ) y‖ := by
    intro y hy
    rcases eq_or_ne (r y) 0 with h0 | h0
    · rw [h0, norm_zero, Real.zero_rpow (by linarith), mul_zero]; exact norm_nonneg _
    · have := h y hy h0
      rwa [psiOne_eq, le_div_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.2 h0) _)] at this
  have hfun : (fun y => ‖gradient (Phi r ℓ) y‖) = fun y => ‖fderiv ℝ (Phi r ℓ) y‖ :=
    funext fun y => norm_gradient_eq _ _
  rw [hfun]
  exact isMeasureDominated_residualPow hℓ hψ key

private theorem one_le_div_sub_one {ℓ : ℝ} (hℓ : 1 < ℓ) : 1 ≤ ℓ / (ℓ - 1) := by
  rw [le_div_iff₀ (by linarith)]; linarith

/-- **§5.3.4, application preceding Theorem 5.3.10** of [cartis2022evaluation].

**Reading.** Packages the domination and AR assumptions for a reference value zero, without evenness
or a minimizer premise.
-/
private theorem arSetting_Phi {ℓ ψmin κν ν κR κA : ℝ} {x : ℕ → ℝⁿ} {S : ℕ → Prop}
    (hℓ : 1 < ℓ) (hψ : 0 < ψmin)
    (hrun : IsARpsiNuRun (Phi r ℓ) (fun y => ‖gradient (Phi r ℓ) y‖) κν ν κR κA x S)
    (hκν : 0 < κν) (hν : 1 ≤ ν) (hκR : 1 ≤ κR) (hκA : 0 ≤ κA)
    (hfr : ∀ k, r (x k) ≠ 0 → ψmin ≤ psiOne r ℓ (x k)) :
    ARSetting (Phi r ℓ) (fun y => ‖gradient (Phi r ℓ) y‖) 0 (ℓ / (ℓ - 1))
      (ψmin ^ (-(ℓ / (ℓ - 1))) / ℓ) κν ν κR κA x S where
  psi_nonneg _ := norm_nonneg _
  one_le_mu := one_le_div_sub_one hℓ
  kappaPsi_pos := div_pos (Real.rpow_pos_of_pos hψ _) (by linarith)
  dominated := Phi_isMeasureDominated hℓ hψ fun _ ⟨k, hk⟩ => hk ▸ hfr k
  run := hrun
  kappaNu_pos := hκν
  one_le_nu := hν
  one_le_kappaR := hκR
  kappaA_nonneg := hκA

/-- **§5.3.4, application preceding Theorem 5.3.11** of [cartis2022evaluation].

**Reading.** Packages the domination and TR assumptions for a reference value zero, without evenness
or a minimizer premise.
-/
private theorem trSetting_Phi {ℓ ψmin κν ν κR κA : ℝ} {x : ℕ → ℝⁿ} {S : ℕ → Prop}
    (hℓ : 1 < ℓ) (hψ : 0 < ψmin)
    (hrun : IsTRpsiNuRun (Phi r ℓ) (fun y => ‖gradient (Phi r ℓ) y‖) κν ν κR κA x S)
    (hκν : 0 < κν) (hν : 1 ≤ ν) (hκR : 1 ≤ κR) (hκA : 0 ≤ κA)
    (hfr : ∀ k, r (x k) ≠ 0 → ψmin ≤ psiOne r ℓ (x k)) :
    TRSetting (Phi r ℓ) (fun y => ‖gradient (Phi r ℓ) y‖) 0 (ℓ / (ℓ - 1))
      (ψmin ^ (-(ℓ / (ℓ - 1))) / ℓ) κν ν κR κA x S where
  psi_nonneg _ := norm_nonneg _
  one_le_mu := one_le_div_sub_one hℓ
  kappaPsi_pos := div_pos (Real.rpow_pos_of_pos hψ _) (by linarith)
  dominated := Phi_isMeasureDominated hℓ hψ fun _ ⟨k, hk⟩ => hk ▸ hfr k
  run := hrun
  kappaNu_pos := hκν
  one_le_nu := hν
  one_le_kappaR := hκR
  kappaA_nonneg := hκA

/-- For a natural number $\ell \ge 1$ and $\epsilon_0 \ge 0$,
$\Phi_\ell(y) \le \epsilon_0^\ell/\ell$ implies $\|r(y)\| \le \epsilon_0$. -/
private theorem norm_le_of_Phi_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) {y : ℝⁿ}
    (h : Phi r ℓ y - 0 ≤ ε₀ ^ ℓ / ℓ) : ‖r y‖ ≤ ε₀ := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  rw [sub_zero, Phi_natCast, div_le_div_iff_of_pos_right hℓpos] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε₀ (by omega)).1 h

/-- For $\epsilon_0 \in (0, 1)$ and a natural number $\ell \ge 1$, $|\log(\epsilon_0^\ell/\ell)| =
\ell(|\log\epsilon_0| + \log\ell/\ell)$. -/
private theorem abs_log_pow_div {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1) :
    |Real.log (ε₀ ^ ℓ / ℓ)| = ℓ * (|Real.log ε₀| + Real.log ℓ / ℓ) := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg (by exact_mod_cast hℓ)
  have hlogε : Real.log ε₀ < 0 := Real.log_neg hε₀ hε₁
  rw [Real.log_div (by positivity) hℓpos.ne', Real.log_pow, abs_of_neg hlogε,
    abs_of_nonpos (by nlinarith)]
  field_simp
  ring

/-- For $\ell \ge 1$, $\log\max(1, \ell y) \le \log\ell + \log\max(1, y)$.

**Reading.** Moves the power coefficient into an additive term while clipping the log argument at
one.
-/
private theorem log_max_mul_le {ℓ y : ℝ} (hℓ : 1 ≤ ℓ) :
    Real.log (max 1 (ℓ * y)) ≤ Real.log ℓ + Real.log (max 1 y) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  refine Real.log_le_log (by positivity) (max_le ?_ ?_)
  · nlinarith [le_max_left 1 y]
  · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)

/-- **Theorem 5.3.10** of [cartis2022evaluation]. Let $2 \le \ell \le p$ be integers and
$\psi_{\min} > 0$. Let $x$ be a run in $\mathrm{AR}_{\psi,\nu}$ for $\Phi_\ell$, with the
success predicate $S$, the measure $\psi = \|\nabla\Phi_\ell\|$, the exponent $\nu = (p+1)/p$ of
the first-order case (5.3.6) of ARp, and constants $\kappa_\nu > 0$, $\kappa_R \ge 1$ and
$\kappa_A \ge 0$. Suppose that the full-rank condition (5.1.62)
$\psi_{\ell,1}(x_k) \ge \psi_{\min}$ holds whenever $r(x_k) \neq 0$. Let
$\mu = \ell/(\ell - 1)$, so that $\nu < \mu$, let $\kappa_\psi = \psi_{\min}^{-\mu}/\ell$ and
$c = \kappa_\nu/\kappa_\psi^{\nu/\mu}$, and let $\kappa^E = 1/(\log\mu - \log\nu)$ and
$\kappa^F$, the value of `Optimization.superlinearCountConst` at $(c, \nu/\mu, \Phi_\ell(x_0))$,
be the constants of Theorem 5.3.3. Then:

* $\|r(x_k)\|$ converges superlinearly along the successful iterations: for every $\eta > 0$
  there is $K$ such that $\|r(x_{k+1})\| \le \eta\|r(x_k)\|$ for every successful $k \ge K$;
* for every $\epsilon_0 \in (0, 1)$, $\|r(x_{k+1})\| \le \epsilon_0$ for every $k$ with
  $|\mathcal{S}_k| \ge N$ (5.3.45), where $N = \kappa^E\log\max(1, |\log\epsilon_0| +
  \log\ell/\ell) + \kappa^F + \kappa^E\log\ell$;
* for every $\epsilon_0 \in (0, 1)$, $\|r(x_{k+1})\| \le \epsilon_0$ for every
  $k \ge \kappa_R N + \kappa_A$ (5.3.44).

**Generalization.** The book takes $\ell$ even. This matters only for the smoothness of
$\Phi_\ell$. The Lean bound holds for any integral $\ell$ in the stated range.

**Reading.** The count is stated for $0<\epsilon_0<1$, with the logarithm clipped as in
`CartisGouldToint.Chapter05.theorem_5_3_3`. The class decrease uses the first-order ARp
exponent $(p+1)/p$ from the discussion preceding the source theorem. -/
theorem theorem_5_3_10 {ℓ p : ℕ} (hℓ2 : 2 ≤ ℓ) (hℓp : ℓ ≤ p)
    {ψmin κν κR κA : ℝ} (hψ : 0 < ψmin) {x : ℕ → ℝⁿ} {S : ℕ → Prop}
    (hrun : IsARpsiNuRun (Phi r ℓ) (fun y => ‖gradient (Phi r ℓ) y‖) κν (((p : ℝ) + 1) / p) κR
      κA x S)
    (hκν : 0 < κν) (hκR : 1 ≤ κR) (hκA : 0 ≤ κA)
    (hfr : ∀ k, r (x k) ≠ 0 → ψmin ≤ psiOne r ℓ (x k)) :
    (∀ η, 0 < η → ∃ K, ∀ k ≥ K, S k → ‖r (x (k + 1))‖ ≤ η * ‖r (x k)‖) ∧
    (∀ ε₀, 0 < ε₀ → ε₀ < 1 → ∀ k,
      1 / (Real.log ((ℓ : ℝ) / (ℓ - 1)) - Real.log (((p : ℝ) + 1) / p)) *
          Real.log (max 1 (|Real.log ε₀| + Real.log ℓ / ℓ)) +
        superlinearCountConst (κν / (ψmin ^ (-((ℓ : ℝ) / (ℓ - 1))) / ℓ) ^ ((((p : ℝ) + 1) / p) /
          ((ℓ : ℝ) / (ℓ - 1)))) ((((p : ℝ) + 1) / p) / ((ℓ : ℝ) / (ℓ - 1))) (Phi r ℓ (x 0)) +
        1 / (Real.log ((ℓ : ℝ) / (ℓ - 1)) - Real.log (((p : ℝ) + 1) / p)) * Real.log ℓ ≤
          (successSet S k).card → ‖r (x (k + 1))‖ ≤ ε₀) ∧
    (∀ ε₀, 0 < ε₀ → ε₀ < 1 → ∀ k : ℕ,
      κR * (1 / (Real.log ((ℓ : ℝ) / (ℓ - 1)) - Real.log (((p : ℝ) + 1) / p)) *
          Real.log (max 1 (|Real.log ε₀| + Real.log ℓ / ℓ)) +
        superlinearCountConst (κν / (ψmin ^ (-((ℓ : ℝ) / (ℓ - 1))) / ℓ) ^ ((((p : ℝ) + 1) / p) /
          ((ℓ : ℝ) / (ℓ - 1)))) ((((p : ℝ) + 1) / p) / ((ℓ : ℝ) / (ℓ - 1))) (Phi r ℓ (x 0)) +
        1 / (Real.log ((ℓ : ℝ) / (ℓ - 1)) - Real.log (((p : ℝ) + 1) / p)) * Real.log ℓ) + κA ≤
          k → ‖r (x (k + 1))‖ ≤ ε₀) := by
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hℓpos : (0 : ℝ) < ℓ := by linarith
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hν1 : (1 : ℝ) ≤ ((p : ℝ) + 1) / p := by rw [le_div_iff₀ (by linarith)]; linarith
  have h := arSetting_Phi hℓ1 hψ hrun hκν hν1 hκR hκA hfr
  -- `ν < μ` since `ℓ < p + 1`
  have hνμ : ((p : ℝ) + 1) / p < (ℓ : ℝ) / (ℓ - 1) := by
    have : (ℓ : ℝ) ≤ p := by exact_mod_cast hℓp
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hΓ : ∀ k, Phi r ℓ (x k) - 0 = ‖r (x k)‖ ^ ℓ / ℓ := fun k => by rw [sub_zero, Phi_natCast]
  set κE := 1 / (Real.log ((ℓ : ℝ) / (ℓ - 1)) - Real.log (((p : ℝ) + 1) / p))
  have hκE : 0 < κE := one_div_pos.2 (sub_pos.2 (Real.log_lt_log (by positivity) hνμ))
  rcases (h.gap.nonneg 0).lt_or_eq with hΓ0 | hΓ0
  · obtain ⟨hsup, hcount, -, -⟩ := theorem_5_3_3 h hνμ
    rw [sub_zero] at hcount
    -- the counts for `‖r‖`
    have hcount' : ∀ ε₀, 0 < ε₀ → ε₀ < 1 → ∀ k,
        κE * Real.log (max 1 (|Real.log ε₀| + Real.log ℓ / ℓ)) +
          superlinearCountConst (κν / (ψmin ^ (-((ℓ : ℝ) / (ℓ - 1))) / ℓ) ^ ((((p : ℝ) + 1) / p) /
            ((ℓ : ℝ) / (ℓ - 1)))) ((((p : ℝ) + 1) / p) / ((ℓ : ℝ) / (ℓ - 1))) (Phi r ℓ (x 0)) +
          κE * Real.log ℓ ≤ (successSet S k).card → ‖r (x (k + 1))‖ ≤ ε₀ := by
      intro ε₀ hε₀ hε₁ k hk
      have hε : 0 < ε₀ ^ ℓ / ℓ := by positivity
      refine norm_le_of_Phi_le (ℓ := ℓ) (by omega) hε₀.le (hcount _ hε k (le_trans ?_ hk))
      rw [abs_log_pow_div (by omega) hε₀ hε₁]
      have := mul_le_mul_of_nonneg_left (log_max_mul_le (y := |Real.log ε₀| + Real.log ℓ / ℓ)
        hℓ1.le) hκE.le
      linarith
    refine ⟨fun η hη => ?_, hcount', fun ε₀ hε₀ hε₁ k hk => hcount' ε₀ hε₀ hε₁ k
      (h.le_card (by linarith))⟩
    obtain ⟨K, hK⟩ := hsup (η ^ ℓ) (by positivity)
    refine ⟨K, fun k hk hSk => ?_⟩
    have := hK k hk hSk
    rw [hΓ, hΓ, ← mul_div_assoc, div_le_div_iff_of_pos_right hℓpos, ← mul_pow] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by omega)).1 this
  · -- `Γ_0 = 0`: the residual vanishes along the run
    have hzero : ∀ k, ‖r (x k)‖ = 0 := fun k => by
      have h1 : Phi r ℓ (x k) - 0 ≤ Phi r ℓ (x 0) - 0 :=
        h.gap.antitone h.c_pos.le (Nat.zero_le k)
      have h2 : 0 ≤ Phi r ℓ (x k) - 0 := h.gap.nonneg k
      rw [← hΓ0] at h1
      have h3 : ‖r (x k)‖ ^ ℓ / ℓ = 0 := by rw [← hΓ k]; linarith
      rw [div_eq_zero_iff] at h3
      rcases h3 with h3 | h3
      · exact pow_eq_zero_iff (by omega) |>.1 h3
      · exact absurd h3 hℓpos.ne'
    refine ⟨fun η _ => ⟨0, fun k _ _ => by rw [hzero, hzero, mul_zero]⟩,
      fun ε₀ hε₀ _ k _ => by rw [hzero]; exact hε₀.le,
      fun ε₀ hε₀ _ k _ => by rw [hzero]; exact hε₀.le⟩

/-- If $\Phi_\ell(x_0) = 0$, the residual vanishes along every run of $\Phi_\ell$ that satisfies the
standing hypotheses of Section 5.3.3. -/
private theorem TRSetting.norm_eq_zero_of_gap_zero {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {μ κψ κν ν κR κA : ℝ}
    {x : ℕ → ℝⁿ} {S : ℕ → Prop}
    (h : TRSetting (Phi r ℓ) (fun y => ‖gradient (Phi r ℓ) y‖) 0 μ κψ κν ν κR κA x S)
    (hΓ0 : 0 = Phi r ℓ (x 0) - 0) (k : ℕ) : ‖r (x k)‖ = 0 := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hanti : Antitone (fun k => Phi r ℓ (x k) - 0) :=
    antitone_nat_of_succ_le (h.gap.le_self h.c_pos.le)
  have h1 : Phi r ℓ (x k) - 0 ≤ Phi r ℓ (x 0) - 0 := hanti (Nat.zero_le k)
  have h2 : 0 ≤ Phi r ℓ (x k) - 0 := h.gap.nonneg k
  rw [← hΓ0, sub_zero, Phi_natCast] at h1
  rw [sub_zero, Phi_natCast] at h2
  have h3 : ‖r (x k)‖ ^ ℓ = 0 := by
    have := le_antisymm h1 h2
    rwa [div_eq_zero_iff, or_iff_left hℓpos.ne'] at this
  exact pow_eq_zero_iff (by omega) |>.1 h3

/-- **Theorem 5.3.11** of [cartis2022evaluation]. Let $\ell > 2$ be an integer and
$\psi_{\min} > 0$. Let $x$ be a run in $\mathrm{TR}_{\psi,\nu}$ for $\Phi_\ell$, with the
success predicate $S$, the measure $\|\nabla\Phi_\ell\|$, the exponent $\nu = 2$ and constants
$\kappa_\nu > 0$, $\kappa_R \ge 1$ and $\kappa_A \ge 0$. Suppose that the full-rank condition
(5.1.62) $\psi_{\ell,1}(x_k) \ge \psi_{\min}$ holds whenever $r(x_k) \neq 0$. Let
$\mu = \ell/(\ell - 1)$, so that $\mu < \nu$, let $\kappa_\psi = \psi_{\min}^{-\mu}/\ell$,
$c = \kappa_\nu/\kappa_\psi^{\nu/\mu}$ and $\alpha = (\nu - \mu)/\mu = (\ell - 2)/\ell$, and let
$\kappa^E = \mu\kappa_\psi^{\nu/\mu}/((\nu - \mu)\kappa_\nu)$ and
$\kappa^F = -\kappa^E\Phi_\ell(x_0)^{-\alpha}$ be the constants of Theorem 5.3.9. Then:

* $\|r(x_k)\| \to 0$, with the polynomial upper bound from Lemma 5.3.6 (iii):
  $\Phi_\ell(x_{k+1}) \le
  (\Phi_\ell(x_0)^{-\alpha} + \alpha c|\mathcal{S}_k|)^{-1/\alpha}$ for every $k$;
* for every $\epsilon_0 > 0$, $\|r(x_{k+1})\| \le \epsilon_0$ for every $k$ with
  $|\mathcal{S}_k| \ge N$, where $N = \ell^{(\ell-2)/\ell}\kappa^E\epsilon_0^{-(\ell-2)} +
  \kappa^F$;
* for every $\epsilon_0 > 0$, $\|r(x_{k+1})\| \le \epsilon_0$ for every
  $k \ge \kappa_R N + \kappa_A$.

**Generalization.** The book takes $\ell$ even. The bound applies to all integral $\ell>2$.

**Correction.** The source calls the residual sequence sublinear. Linear residual
convergence is possible under the same hypotheses, for example with $r(x)=x$,
$\ell=4$, $x_k=2^{-k}$ and every iteration successful. The gradient norm is
$|x_k|^3$ and (5.3.28) holds with $\kappa_\nu=(1-2^{-4})/4$ and $\nu=2$.

The counts are those of Theorem 5.3.9 for $\epsilon = \epsilon_0^\ell/\ell$. -/
theorem theorem_5_3_11 {ℓ : ℕ} (hℓ2 : 2 < ℓ) {ψmin κν κR κA : ℝ} (hψ : 0 < ψmin)
    {x : ℕ → ℝⁿ} {S : ℕ → Prop}
    (hrun : IsTRpsiNuRun (Phi r ℓ) (fun y => ‖gradient (Phi r ℓ) y‖) κν 2 κR κA x S)
    (hκν : 0 < κν) (hκR : 1 ≤ κR) (hκA : 0 ≤ κA)
    (hfr : ∀ k, r (x k) ≠ 0 → ψmin ≤ psiOne r ℓ (x k)) :
    Tendsto (fun k => ‖r (x k)‖) atTop (𝓝 0) ∧
    (∀ k, Phi r ℓ (x (k + 1)) ≤ (Phi r ℓ (x 0) ^ (-(((ℓ : ℝ) - 2) / ℓ)) +
        ((ℓ : ℝ) - 2) / ℓ * (κν / (ψmin ^ (-((ℓ : ℝ) / (ℓ - 1))) / ℓ) ^ (2 / ((ℓ : ℝ) / (ℓ - 1)))) *
          (successSet S k).card) ^ (-1 / (((ℓ : ℝ) - 2) / ℓ))) ∧
    (∀ ε₀, 0 < ε₀ → ∀ k, (ℓ : ℝ) ^ (((ℓ : ℝ) - 2) / ℓ) *
        ((ℓ : ℝ) / (ℓ - 1) * (ψmin ^ (-((ℓ : ℝ) / (ℓ - 1))) / ℓ) ^ (2 / ((ℓ : ℝ) / (ℓ - 1))) /
          ((2 - (ℓ : ℝ) / (ℓ - 1)) * κν)) * ε₀ ^ (-((ℓ : ℝ) - 2)) +
      -((ℓ : ℝ) / (ℓ - 1) * (ψmin ^ (-((ℓ : ℝ) / (ℓ - 1))) / ℓ) ^ (2 / ((ℓ : ℝ) / (ℓ - 1))) /
          ((2 - (ℓ : ℝ) / (ℓ - 1)) * κν) * Phi r ℓ (x 0) ^ (-(((ℓ : ℝ) - 2) / ℓ))) ≤
        (successSet S k).card → ‖r (x (k + 1))‖ ≤ ε₀) ∧
    (∀ ε₀, 0 < ε₀ → ∀ k : ℕ, κR * ((ℓ : ℝ) ^ (((ℓ : ℝ) - 2) / ℓ) *
        ((ℓ : ℝ) / (ℓ - 1) * (ψmin ^ (-((ℓ : ℝ) / (ℓ - 1))) / ℓ) ^ (2 / ((ℓ : ℝ) / (ℓ - 1))) /
          ((2 - (ℓ : ℝ) / (ℓ - 1)) * κν)) * ε₀ ^ (-((ℓ : ℝ) - 2)) +
      -((ℓ : ℝ) / (ℓ - 1) * (ψmin ^ (-((ℓ : ℝ) / (ℓ - 1))) / ℓ) ^ (2 / ((ℓ : ℝ) / (ℓ - 1))) /
          ((2 - (ℓ : ℝ) / (ℓ - 1)) * κν) * Phi r ℓ (x 0) ^ (-(((ℓ : ℝ) - 2) / ℓ)))) + κA ≤ k →
        ‖r (x (k + 1))‖ ≤ ε₀) := by
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hℓ2' : (2 : ℝ) < ℓ := by exact_mod_cast hℓ2
  have hℓpos : (0 : ℝ) < ℓ := by linarith
  have h := trSetting_Phi hℓ1 hψ hrun hκν one_le_two hκR hκA hfr
  have hμν : (ℓ : ℝ) / (ℓ - 1) < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
  have hαeq : (2 - (ℓ : ℝ) / (ℓ - 1)) / ((ℓ : ℝ) / (ℓ - 1)) = ((ℓ : ℝ) - 2) / ℓ := by
    have : (ℓ : ℝ) - 1 ≠ 0 := by linarith
    field_simp; ring
  rcases (h.gap.nonneg 0).lt_or_eq with hΓ0 | hΓ0
  · obtain ⟨-, hcount, -, -⟩ := theorem_5_3_9 h hμν hΓ0
    obtain ⟨-, -, -, hiii⟩ := lemma_5_3_6 h hΓ0
    obtain ⟨-, -, htend, hrate⟩ := hiii hμν
    rw [hαeq] at hcount hrate
    set κE := (ℓ : ℝ) / (ℓ - 1) * (ψmin ^ (-((ℓ : ℝ) / (ℓ - 1))) / ℓ) ^ (2 / ((ℓ : ℝ) / (ℓ - 1))) /
      ((2 - (ℓ : ℝ) / (ℓ - 1)) * κν) with hκE
    -- `ε^{-(ℓ-2)/ℓ} = ℓ^{(ℓ-2)/ℓ} ε₀^{-(ℓ-2)}` for `ε = ε₀^ℓ/ℓ`
    have hpow : ∀ ε₀ : ℝ, 0 < ε₀ → (ε₀ ^ ℓ / ℓ) ^ (-(((ℓ : ℝ) - 2) / ℓ)) =
        (ℓ : ℝ) ^ (((ℓ : ℝ) - 2) / ℓ) * ε₀ ^ (-((ℓ : ℝ) - 2)) := fun ε₀ hε₀ => by
      rw [Real.div_rpow (by positivity) hℓpos.le, ← Real.rpow_natCast,
        ← Real.rpow_mul hε₀.le, Real.rpow_neg hℓpos.le, div_inv_eq_mul, mul_comm]
      congr 2
      field_simp
    have hcount' : ∀ ε₀, 0 < ε₀ → ∀ k, (ℓ : ℝ) ^ (((ℓ : ℝ) - 2) / ℓ) * κE *
        ε₀ ^ (-((ℓ : ℝ) - 2)) + -(κE * Phi r ℓ (x 0) ^ (-(((ℓ : ℝ) - 2) / ℓ))) ≤
          (successSet S k).card → ‖r (x (k + 1))‖ ≤ ε₀ := by
      intro ε₀ hε₀ k hk
      refine norm_le_of_Phi_le (ℓ := ℓ) (by omega) hε₀.le
        (hcount (ε₀ ^ ℓ / ℓ) (by positivity) k ?_)
      rw [hpow ε₀ hε₀, sub_zero]
      linarith
    refine ⟨?_, fun k => by have := hrate k; rwa [sub_zero, sub_zero] at this, hcount',
      fun ε₀ hε₀ k hk => hcount' ε₀ hε₀ k (h.le_card hk)⟩
    -- `‖r‖ = (ℓ Φ_ℓ)^{1/ℓ}`
    have hcont : Tendsto (fun t : ℝ => (ℓ * t) ^ ((ℓ : ℝ)⁻¹)) (𝓝 0) (𝓝 ((ℓ * 0) ^ ((ℓ : ℝ)⁻¹))) :=
      ((continuous_const.mul continuous_id).rpow_const fun _ => Or.inr (by positivity)).tendsto 0
    rw [mul_zero, Real.zero_rpow (by positivity)] at hcont
    refine (hcont.comp htend).congr fun k => ?_
    simp only [Function.comp, sub_zero, Phi_natCast]
    rw [mul_div_cancel₀ _ hℓpos.ne', Real.pow_rpow_inv_natCast (norm_nonneg _) (by omega)]
  · have hz := TRSetting.norm_eq_zero_of_gap_zero (by omega) h hΓ0
    refine ⟨by simp only [hz]; exact tendsto_const_nhds, fun k => ?_,
      fun ε₀ hε₀ k _ => by rw [hz]; exact hε₀.le, fun ε₀ hε₀ k _ => by rw [hz]; exact hε₀.le⟩
    have hΦ0 : ∀ j, Phi r ℓ (x j) = 0 := fun j => by
      rw [Phi_natCast, hz, zero_pow (by omega), zero_div]
    rw [hΦ0, hΦ0, Real.zero_rpow (by
      have : (0 : ℝ) < ((ℓ : ℝ) - 2) / ℓ := div_pos (by linarith) hℓpos
      linarith), zero_add]
    have hα : 0 ≤ ((ℓ : ℝ) - 2) / ℓ := div_nonneg (by linarith) hℓpos.le
    exact Real.rpow_nonneg (mul_nonneg (mul_nonneg hα h.c_pos.le) (Nat.cast_nonneg _)) _

/-- **Theorem 5.3.12** of [cartis2022evaluation]. Let $\psi_{\min} > 0$, and let $x$ be a run in
$\mathrm{TR}_{\psi,\nu}$ for $\Phi_2 = \|r\|^2/2$, with the success predicate $S$, the measure
$\|\nabla\Phi_2\|$, the exponent $\nu = 2 = \mu$ and constants $\kappa_\nu > 0$,
$\kappa_R \ge 1$ and $\kappa_A \ge 0$. Suppose that the full-rank condition (5.1.62)
$\psi_{2,1}(x_k) \ge \psi_{\min}$ holds whenever $r(x_k) \neq 0$, and let
$\kappa_\psi = \psi_{\min}^{-2}/2$. If $\kappa_\nu = \kappa_\psi$, then $r(x_{k+1}) = 0$ after
every successful iteration $k$. If $\kappa_\nu < \kappa_\psi$, let $\kappa^E = 1/|\log(1 -
\kappa_\nu/\kappa_\psi)|$ and $\kappa^F = \log\Phi_2(x_0)/|\log(1 - \kappa_\nu/\kappa_\psi)|$ be
the constants of Theorem 5.3.8. Then:

* $\|r(x_k)\|^2$ converges linearly: $\|r(x_{k+1})\|^2 \le (1 -
  \kappa_\nu/\kappa_\psi)\|r(x_k)\|^2$ for every successful $k$;
* for every $\epsilon_0 \in (0, 1)$, $\|r(x_{k+1})\| \le \epsilon_0$ for every $k$ with
  $|\mathcal{S}_k| \ge N$, where $N = 2\kappa^E|\log\epsilon_0| + \kappa^E\log 2 + \kappa^F$;
* for every $\epsilon_0 \in (0, 1)$, $\|r(x_{k+1})\| \le \epsilon_0$ for every
  $k \ge \kappa_R N + \kappa_A$.

**Typo.** The book's display mixes $\kappa^C_{\mathrm{TR1,FRLS}}$ and
$\kappa^C_{\mathrm{TR,FRLS}}$; one constant is meant.

**Reading.** The count is stated for $0<\epsilon_0<1$. The factor $2$ and the
additive $\log 2$ in the count come from using $\epsilon=\epsilon_0^2/2$
in Theorem 5.3.8.

The counts are those of Theorem 5.3.8 for $\epsilon = \epsilon_0^2/2$. If $r(x_0) = 0$, the
residual vanishes along the run. -/
theorem theorem_5_3_12 {ψmin κν κR κA : ℝ} (hψ : 0 < ψmin) {x : ℕ → ℝⁿ} {S : ℕ → Prop}
    (hrun : IsTRpsiNuRun (Phi r 2) (fun y => ‖gradient (Phi r 2) y‖) κν 2 κR κA x S)
    (hκν : 0 < κν) (hκR : 1 ≤ κR) (hκA : 0 ≤ κA)
    (hfr : ∀ k, r (x k) ≠ 0 → ψmin ≤ psiOne r 2 (x k)) :
    (κν = ψmin ^ (-2 : ℝ) / 2 → ∀ k, S k → r (x (k + 1)) = 0) ∧
    (κν < ψmin ^ (-2 : ℝ) / 2 →
      (∀ k, S k → ‖r (x (k + 1))‖ ^ 2 ≤ (1 - κν / (ψmin ^ (-2 : ℝ) / 2)) * ‖r (x k)‖ ^ 2) ∧
      (∀ ε₀, 0 < ε₀ → ε₀ < 1 → ∀ k,
        2 * (1 / |Real.log (1 - κν / (ψmin ^ (-2 : ℝ) / 2))|) * |Real.log ε₀| +
          1 / |Real.log (1 - κν / (ψmin ^ (-2 : ℝ) / 2))| * Real.log 2 +
          Real.log (Phi r 2 (x 0)) / |Real.log (1 - κν / (ψmin ^ (-2 : ℝ) / 2))| ≤
            (successSet S k).card → ‖r (x (k + 1))‖ ≤ ε₀) ∧
      (∀ ε₀, 0 < ε₀ → ε₀ < 1 → ∀ k : ℕ,
        κR * (2 * (1 / |Real.log (1 - κν / (ψmin ^ (-2 : ℝ) / 2))|) * |Real.log ε₀| +
          1 / |Real.log (1 - κν / (ψmin ^ (-2 : ℝ) / 2))| * Real.log 2 +
          Real.log (Phi r 2 (x 0)) / |Real.log (1 - κν / (ψmin ^ (-2 : ℝ) / 2))|) + κA ≤ k →
            ‖r (x (k + 1))‖ ≤ ε₀)) := by
  have h2 : (2 : ℝ) / (2 - 1) = 2 := by norm_num
  have hΦ2 : ∀ y, Phi r 2 y = ‖r y‖ ^ 2 / 2 := fun y => by rw [Phi_apply, Real.rpow_two]
  have h := trSetting_Phi one_lt_two hψ hrun hκν one_le_two hκR hκA hfr
  rw [h2] at h
  have hr0 : ∀ y, Phi r 2 y - 0 = 0 → r y = 0 := fun y hy => by
    rw [sub_zero, hΦ2, div_eq_zero_iff, or_iff_left two_ne_zero] at hy
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hy)
  rcases (h.gap.nonneg 0).lt_or_eq with hΓ0 | hΓ0
  · obtain ⟨heq, hlt⟩ := theorem_5_3_8 h rfl hΓ0
    refine ⟨fun hκ k hk => hr0 _ (heq hκ k hk), fun hκ => ?_⟩
    obtain ⟨hlin, hcount, -, -⟩ := hlt hκ
    simp only [sub_zero] at hcount
    have hcount' : ∀ ε₀, 0 < ε₀ → ε₀ < 1 → ∀ k,
        2 * (1 / |Real.log (1 - κν / (ψmin ^ (-2 : ℝ) / 2))|) * |Real.log ε₀| +
          1 / |Real.log (1 - κν / (ψmin ^ (-2 : ℝ) / 2))| * Real.log 2 +
          Real.log (Phi r 2 (x 0)) / |Real.log (1 - κν / (ψmin ^ (-2 : ℝ) / 2))| ≤
            (successSet S k).card → ‖r (x (k + 1))‖ ≤ ε₀ := by
      intro ε₀ hε₀ hε₁ k hk
      have hε : 0 < ε₀ ^ 2 / 2 := by positivity
      have hle := hcount _ hε k (le_trans (le_of_eq ?_) hk)
      · rw [hΦ2, div_le_div_iff_of_pos_right two_pos] at hle
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε₀.le two_ne_zero).1 hle
      · have := abs_log_pow_div (ℓ := 2) (by norm_num) hε₀ hε₁
        push_cast at this
        rw [this]
        ring
    refine ⟨fun k hk => ?_, hcount', fun ε₀ hε₀ hε₁ k hk => hcount' ε₀ hε₀ hε₁ k
      (h.le_card hk)⟩
    have := hlin k hk
    rw [sub_zero, sub_zero, hΦ2, hΦ2] at this
    linarith
  · have hz := TRSetting.norm_eq_zero_of_gap_zero (ℓ := 2) (by norm_num) (by simpa using h)
      (by simpa using hΓ0)
    refine ⟨fun _ k _ => norm_eq_zero.1 (hz (k + 1)), fun _ => ⟨fun k _ => ?_,
      fun ε₀ hε₀ _ k _ => by rw [hz]; exact hε₀.le, fun ε₀ hε₀ _ k _ => by rw [hz]; exact hε₀.le⟩⟩
    rw [hz, hz]; norm_num

end LeastSquares

end CartisGouldToint.Chapter05
