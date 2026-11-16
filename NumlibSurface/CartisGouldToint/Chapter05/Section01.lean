/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Calculus.AnchoredLipschitzDerivs
import Numlib.Analysis.SpecialFunctions.Pow.Real
import Numlib.Optimization.ResidualPower
import NumlibSurface.CartisGouldToint.Chapter01.Section01

/-!
# Cartis, Gould and Toint, Section 5.1: Nonlinear least squares and least Euclidean norms

This module formalizes Section 5.1 of [cartis2022evaluation]. For a residual
$r : \mathbb{R}^n \to \mathbb{R}^m$, the problem of minimizing $\|r(x)\|$ is treated through the
objective $\Phi_\ell(x) = \|r(x)\|^\ell/\ell$ (5.1.3), with criticality measures scaled by
$\|r(x)\|^{\ell-1}$ (5.1.6)–(5.1.7). The ARpLE algorithm (Algorithm 5.1.1) is the ARp method of
Algorithm 4.1.1 applied to $\Phi_\ell$, with the residual-scaled termination tests (5.1.9)–(5.1.14).
Its evaluation complexity (Theorem 5.1.7) follows by telescoping the potential $\|r(x_k)\|^{1/2^i}$.
Lemmas 5.1.5 and 5.1.6 choose the exponents $\ell$ and $i$ so that the exponents $\iota_j$ of
(5.1.21), (5.1.23) and (5.1.25) are nonnegative. The proofs use the backbone modules
`Numlib.Optimization.ResidualPower` and `Numlib.Optimization.ModelBased.ARpRun`.

## Main definitions

* Equation (5.1.3), `CartisGouldToint.Chapter05.Phi`: the objective
  $\Phi_\ell(x) = \|r(x)\|^\ell/\ell$.
* Equations (5.1.6)–(5.1.7), `CartisGouldToint.Chapter05.psiOne`,
  `CartisGouldToint.Chapter05.psiTwo`, `CartisGouldToint.Chapter05.psiTwoDir`,
  `CartisGouldToint.Chapter05.psiThree` and `CartisGouldToint.Chapter05.zSet`: the scaled measures
  $\psi_{\ell,1}$, $\psi_{\ell,2}$, $\psi_{\ell,2}(\cdot, d)$, $\psi_{\ell,3}(\cdot, d)$ and the set
  $\mathcal{Z}_\epsilon$ of directions of small scaled curvature.
* Assumption $\Phi_\ell$.DpL, `CartisGouldToint.Chapter05.AssumptionPhiDpL`: the $p$-th derivative
  of $\Phi_\ell$ is Lipschitz continuous.
* Algorithm 5.1.1, `CartisGouldToint.Chapter05.ARpLEStop`, `CartisGouldToint.Chapter05.mdir` and
  `CartisGouldToint.Chapter05.algorithm_5_1_1`: the Step 1 test (5.1.9)–(5.1.14), the direction sets
  $\mathcal{M}_k$ and the ARpLE run predicate.
* Equations (5.1.21), (5.1.23) and (5.1.25), `CartisGouldToint.Chapter05.iota`: the exponents
  $\iota_j(p, \ell, i)$.

## Main results

* Lemma 5.1.1, `CartisGouldToint.Chapter05.lemma_5_1_1`: $\Phi_\ell$ is $C^p$ if $r$ is $C^p$ and
  $\ell$ is even or $\ell > 2p$.
* Lemma 5.1.2, `CartisGouldToint.Chapter05.lemma_5_1_2`: lower bounds on the decrease of
  $\|r\|^\ell$ at a successful iteration.
* Lemma 5.1.3, `CartisGouldToint.Chapter05.lemma_5_1_3`: the cascading-differences inequality for
  $a^{1/2^i} - b^{1/2^i}$.
* Lemma 5.1.4, `CartisGouldToint.Chapter05.lemma_5_1_4`: lower bounds on the decrease of the
  potential $\|r\|^{1/2^i}$.
* Lemma 5.1.5, `CartisGouldToint.Chapter05.lemma_5_1_5`: every $p \neq 0$ is uniquely $o \, 2^i$
  with $o$ odd.
* Lemma 5.1.6, `CartisGouldToint.Chapter05.lemma_5_1_6`: choices of $\ell$ and $i$ for which the
  exponents $\iota_j$ are positive or zero.
* Theorem 5.1.7, `CartisGouldToint.Chapter05.theorem_5_1_7_of_iota_nonneg` and
  `CartisGouldToint.Chapter05.theorem_5_1_7`: the evaluation complexity of ARpLE.
* Equations (5.1.62)–(5.1.64), `CartisGouldToint.Chapter05.psiOne_ge_of_jacobian`: if the adjoint of
  the Jacobian is bounded below by $s_0$, then $\psi_{\ell,1} \ge s_0$.

## Conventions

* The space $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`, and the residual is
  $r : \mathbb{R}^n \to \mathbb{R}^m$.
* The order $q \in \{1, 2, 3\}$ of criticality sought replaces the book's infinite tolerances:
  $\epsilon_2 = \epsilon_3 = \infty$ is $q = 1$, and $\epsilon_3 = \infty > \epsilon_2$ is $q = 2$.
  The tolerances of index greater than $q$ are not used.
* An iteration $k$ is successful if $\rho_k \ge \eta_1$, where $\rho_k$ is the ratio (4.1.15) for
  $\Phi_\ell$, `Optimization.taylorRatio (Phi r ℓ) p x s k`. An iteration $k$ is before termination
  if the test fails at every $j \le k$.
* The constants $\kappa_1$, $\kappa_2$, $\kappa_3$ and $\kappa_{s2}$ of (4.1.32), (4.1.34), (4.1.36)
  and (4.1.23), with $L = L_{\Phi_\ell,p}$, are `CartisGouldToint.Chapter05.kappa₁`,
  `CartisGouldToint.Chapter05.kappa₂`, `CartisGouldToint.Chapter05.kappa₃` and
  `CartisGouldToint.Chapter05.kappaS₂`.

## Implementation notes

* The objective $\Phi_\ell$ is `Optimization.residualPow r ℓ`, with a real exponent $\ell$. The
  ARpLE run is the backbone run predicate `Optimization.IsARpRun` for $\Phi_\ell$.
* Lemma 5.1.1 is proved for $\ell > 2p$, as stated. The backbone proves it for $\ell \ge 2p$.
* The evaluation counts are `Optimization.funEvalCount` and `Optimization.derivEvalCount`.

## Deviations from the source

* **Algorithm 5.1.1, third-order test** (correction). The book requires
  $\mathcal{M}_k \neq \emptyset$ in the third-order branch of the test. With that requirement the
  proof of Theorem 5.1.7 fails when $\mathcal{M}_{k+1} = \emptyset$, so the condition "for all
  $d \in \mathcal{M}_k$" is read vacuously. See `CartisGouldToint.Chapter05.ARpLEStop`.
* **Algorithm 5.1.1, existence of runs** (reading). For $q = 3$ an admissible step need not exist
  when the test fails. The complexity theorems are statements about runs, and runs are shown to
  exist for $q \le 2$. See `CartisGouldToint.Chapter05.algorithm_5_1_1.exists_run`.
* **Lemma 5.1.5** (reading). The book writes $p \in \mathbb{N}$. The statement needs $p \neq 0$. See
  `CartisGouldToint.Chapter05.lemma_5_1_5`.
* **Theorem 5.1.7** (typo). The multiplier in (5.1.44) is $\kappa^A$ (printed $\kappa^C$). In
  (5.1.51) the three conditions are alternatives (printed "and"), and the set $\mathcal{M}_{j+1}$
  there is that of (4.1.14) (printed (4.1.9)). See `CartisGouldToint.Chapter05.theorem_5_1_7`.
* **Theorem 5.1.7** (reading). The run may also stop by the strict-local-minimizer test (5.1.11),
  which is one of the branches of the termination test. See
  `CartisGouldToint.Chapter05.theorem_5_1_7`.
* **Theorem 5.1.7** (generalization). The book's hypothesis
  $(\epsilon_0, \dots, \epsilon_3) \in (0, 1]^4$ is used only as $\epsilon_j > 0$. A general form
  holds for every order $q \le 3$ and all $\ell$, $i$ with $\iota_j \ge 0$ for $j \le q$, and it
  covers the first- and second-order variants that the book mentions after its proof. See
  `CartisGouldToint.Chapter05.theorem_5_1_7_of_iota_nonneg`.
-/

open Set Optimization
open scoped Nat

namespace CartisGouldToint.Chapter05

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)
set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-! ### The objective $\Phi_\ell$ and the scaled criticality measures -/

/-- **Equation (5.1.3)** of [cartis2022evaluation]. For a residual
$r : \mathbb{R}^n \to \mathbb{R}^m$ and $\ell \in \mathbb{R}$, the objective is
$$\Phi_\ell(x) = \frac{\|r(x)\|^\ell}{\ell}.$$
For $\ell = 1$ it is the norm $\|r(x)\|$ of (5.1.1), and for $\ell = 2$ it is the least-squares
objective $\frac12\|r(x)\|^2$ of (5.1.2).

The definition is `Optimization.residualPow r ℓ`, with a real exponent. For $\ell = 0$, Lean's
division gives $\Phi_0 = 0$. -/
noncomputable abbrev Phi (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) : ℝⁿ → ℝ :=
  residualPow r ℓ

/-- For every $x$, $\Phi_\ell(x) = \|r(x)\|^\ell/\ell$ with the real power. -/
theorem Phi_apply (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (x : ℝⁿ) : Phi r ℓ x = ‖r x‖ ^ ℓ / ℓ :=
  rfl

/-- For a natural exponent $\ell$, $\Phi_\ell(x) = \|r(x)\|^\ell/\ell$ with the natural power. -/
theorem Phi_natCast (r : ℝⁿ → ℝᵐ) (ℓ : ℕ) (x : ℝⁿ) : Phi r ℓ x = ‖r x‖ ^ ℓ / ℓ :=
  residualPow_natCast r ℓ x

/-- **Lemma 5.1.1** of [cartis2022evaluation]. Let $r : \mathbb{R}^n \to \mathbb{R}^m$ be $p$ times
continuously differentiable, and let $\ell$ be either an even natural number or a real number
with $\ell > 2p$. Then $\Phi_\ell$ is $p$ times continuously differentiable.

An even natural number is written $\ell = 2k$ with $k \in \mathbb{N}$. The backbone proves the
second case for $\ell \ge 2p$. -/
theorem lemma_5_1_1 {r : ℝⁿ → ℝᵐ} {p : ℕ} {ℓ : ℝ} (hr : ContDiff ℝ p r)
    (hℓ : (∃ k : ℕ, ℓ = 2 * k) ∨ 2 * (p : ℝ) < ℓ) : ContDiff ℝ p (Phi r ℓ) :=
  contDiff_residualPow hr (hℓ.imp_right le_of_lt)

/-- **Equations (5.1.6)–(5.1.7)** of [cartis2022evaluation], first-order part. The **scaled
first-order measure** is
$$\psi_{\ell,1}(x) = \frac{\|\nabla\Phi_\ell(x)\|}{\|r(x)\|^{\ell-1}}.$$

Where $r(x) = 0$ and $\ell \neq 1$, the denominator is $0$ and Lean's division gives
$\psi_{\ell,1}(x) = 0$. For $\ell = 1$ the denominator is $0^0 = 1$. The test (5.1.9) excludes
the case $r(x) = 0$ before termination. -/
noncomputable def psiOne (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (x : ℝⁿ) : ℝ :=
  ‖gradient (Phi r ℓ) x‖ / ‖r x‖ ^ (ℓ - 1)

/-- The scaled second-order measure $\psi_{\ell,2}(x) =
\lambda_{\min}[\nabla^2\Phi_\ell(x)]/\|r(x)\|^{\ell-1}$ of Section 5.1.1 of
[cartis2022evaluation]. -/
noncomputable def psiTwo (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (x : ℝⁿ) : ℝ :=
  Chapter01.hessianMinEig (Phi r ℓ) x / ‖r x‖ ^ (ℓ - 1)

/-- The scaled curvature along $d$, $\psi_{\ell,2}(x, d) =
|\nabla^2\Phi_\ell(x)[d]^2|/\|r(x)\|^{\ell-1}$, of (5.1.7) of [cartis2022evaluation].
-/
noncomputable def psiTwoDir (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (x d : ℝⁿ) : ℝ :=
  |iteratedFDeriv ℝ 2 (Phi r ℓ) x (fun _ => d)| / ‖r x‖ ^ (ℓ - 1)

/-- The scaled third-order measure along $d$, $\psi_{\ell,3}(x, d) =
|\nabla^3\Phi_\ell(x)[d]^3|/\|r(x)\|^{\ell-1}$, of (5.1.6) of [cartis2022evaluation].
-/
noncomputable def psiThree (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (x d : ℝⁿ) : ℝ :=
  |iteratedFDeriv ℝ 3 (Phi r ℓ) x (fun _ => d)| / ‖r x‖ ^ (ℓ - 1)

/-- **Equation (5.1.7)** of [cartis2022evaluation]. The set of directions of small scaled curvature
at $x$ is
$$\mathcal{Z}_\epsilon = \{d \in \mathbb{R}^n : \|d\| = 1, \ \psi_{\ell,2}(x, d) \le
  \epsilon_2\}.$$
-/
def zSet (r : ℝⁿ → ℝᵐ) (ℓ ε₂ : ℝ) (x : ℝⁿ) : Set ℝⁿ :=
  {d | ‖d‖ = 1 ∧ psiTwoDir r ℓ x d ≤ ε₂}

section Measures

variable {r : ℝⁿ → ℝᵐ} {ℓ : ℝ} {x : ℝⁿ}

/-- A direction $d$ lies in $\mathcal{Z}_\epsilon$ if and only if $\|d\| = 1$ and
$\psi_{\ell,2}(x, d) \le \epsilon_2$. -/
theorem mem_zSet {ε₂ : ℝ} {d : ℝⁿ} : d ∈ zSet r ℓ ε₂ x ↔ ‖d‖ = 1 ∧ psiTwoDir r ℓ x d ≤ ε₂ :=
  Iff.rfl

private theorem scale_pos (hx : r x ≠ 0) : 0 < ‖r x‖ ^ (ℓ - 1) :=
  Real.rpow_pos_of_pos (norm_pos_iff.2 hx) _

/-- The measure $\psi_{\ell,1}(x)$ is the operator norm of the derivative $D\Phi_\ell(x)$ divided by
$\|r(x)\|^{\ell-1}$. -/
theorem psiOne_eq : psiOne r ℓ x = ‖fderiv ℝ (Phi r ℓ) x‖ / ‖r x‖ ^ (ℓ - 1) := by
  rw [psiOne, norm_gradient_eq]

/-- The measure $\psi_{\ell,2}(x)$ is the least curvature `minCurvature` of the second derivative of
$\Phi_\ell$ at $x$, divided by $\|r(x)\|^{\ell-1}$. -/
theorem psiTwo_eq :
    psiTwo r ℓ x = minCurvature (iteratedFDeriv ℝ 2 (Phi r ℓ) x) / ‖r x‖ ^ (ℓ - 1) :=
  rfl

/-- The measure $\psi_{\ell,1}(x)$ is nonnegative. -/
theorem psiOne_nonneg : 0 ≤ psiOne r ℓ x :=
  div_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)

/-- The measure $\psi_{\ell,2}(x, d)$ is nonnegative. -/
theorem psiTwoDir_nonneg {d : ℝⁿ} : 0 ≤ psiTwoDir r ℓ x d :=
  div_nonneg (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)

/-- The measure $\psi_{\ell,3}(x, d)$ is nonnegative. -/
theorem psiThree_nonneg {d : ℝⁿ} : 0 ≤ psiThree r ℓ x d :=
  div_nonneg (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)

/-- If $r(x) \neq 0$, then $\psi_{\ell,1}(x) \le \epsilon$ if and only if $\|\nabla\Phi_\ell(x)\|
\le \epsilon\|r(x)\|^{\ell-1}$. -/
theorem psiOne_le_iff (hx : r x ≠ 0) {ε : ℝ} :
    psiOne r ℓ x ≤ ε ↔ ‖fderiv ℝ (Phi r ℓ) x‖ ≤ ε * ‖r x‖ ^ (ℓ - 1) := by
  rw [psiOne_eq, div_le_iff₀ (scale_pos hx)]

/-- If $r(x) \neq 0$, then $\psi_{\ell,2}(x) < -\epsilon$ if and only if $\epsilon\|r(x)\|^{\ell-1}
< -\lambda_{\min}[\nabla^2\Phi_\ell(x)]$. -/
theorem psiTwo_lt_neg_iff (hx : r x ≠ 0) {ε : ℝ} :
    psiTwo r ℓ x < -ε ↔
      ε * ‖r x‖ ^ (ℓ - 1) < -minCurvature (iteratedFDeriv ℝ 2 (Phi r ℓ) x) := by
  rw [psiTwo_eq, div_lt_iff₀ (scale_pos hx)]
  constructor <;> intro h <;> linarith

/-- If $r(x) \neq 0$, then $\psi_{\ell,2}(x, d) \le \epsilon$ if and only if
$|\nabla^2\Phi_\ell(x)[d]^2| \le \epsilon\|r(x)\|^{\ell-1}$. -/
theorem psiTwoDir_le_iff (hx : r x ≠ 0) {ε : ℝ} {d : ℝⁿ} :
    psiTwoDir r ℓ x d ≤ ε ↔ |iteratedFDeriv ℝ 2 (Phi r ℓ) x (fun _ => d)| ≤ ε * ‖r x‖ ^ (ℓ - 1) :=
  div_le_iff₀ (scale_pos hx)

/-- If $r(x) \neq 0$, then $\psi_{\ell,3}(x, d) \le \epsilon$ if and only if
$|\nabla^3\Phi_\ell(x)[d]^3| \le \epsilon\|r(x)\|^{\ell-1}$. -/
theorem psiThree_le_iff (hx : r x ≠ 0) {ε : ℝ} {d : ℝⁿ} :
    psiThree r ℓ x d ≤ ε ↔ |iteratedFDeriv ℝ 3 (Phi r ℓ) x (fun _ => d)| ≤ ε * ‖r x‖ ^ (ℓ - 1) :=
  div_le_iff₀ (scale_pos hx)

/-- If $r(x) \neq 0$, then $\mathcal{Z}_\epsilon$ is the set of unit vectors $d$ with
$|\nabla^2\Phi_\ell(x)[d]^2| \le \epsilon_2\|r(x)\|^{\ell-1}$. -/
theorem zSet_eq (hx : r x ≠ 0) (ε₂ : ℝ) :
    zSet r ℓ ε₂ x = smallCurvatureDirections (iteratedFDeriv ℝ 2 (Phi r ℓ) x)
      (ε₂ * ‖r x‖ ^ (ℓ - 1)) := by
  ext d
  rw [mem_zSet, mem_smallCurvatureDirections, psiTwoDir_le_iff hx]

/-- For $\omega, b \ge 0$, $\nu > 0$ and any $e$, $(\omega/b^e)^\nu \, b^{e\nu} \le \omega^\nu$
(with equality if $b > 0$), which undoes the scaling of a measure. -/
private theorem div_rpow_mul_le {ω b e ν : ℝ} (hω : 0 ≤ ω) (hb : 0 ≤ b) (hν : 0 < ν) :
    (ω / b ^ e) ^ ν * b ^ (e * ν) ≤ ω ^ ν := by
  rcases hb.lt_or_eq with hb | hb
  · rw [Real.rpow_mul hb.le, ← Real.mul_rpow (div_nonneg hω (Real.rpow_nonneg hb.le _))
      (Real.rpow_nonneg hb.le _), div_mul_cancel₀ _ (Real.rpow_pos_of_pos hb _).ne']
  · subst hb
    rcases eq_or_ne e 0 with he | he
    · simp [he]
    · rw [Real.zero_rpow he, div_zero, Real.zero_rpow hν.ne', zero_mul]
      exact Real.rpow_nonneg hω _

end Measures

/-! ### The algorithm -/

/-- **Assumption $\Phi_\ell$.DpL** of [cartis2022evaluation], Section 5.1.2. The function
$\Phi_\ell$ is $p$ times continuously differentiable on $\mathbb{R}^n$, $L \ge 0$, and the
$p$-th derivative of $\Phi_\ell$ is Lipschitz continuous with constant $L$:
$$\|\nabla^p\Phi_\ell(x) - \nabla^p\Phi_\ell(y)\| \le L\|x - y\| \quad \text{for all } x, y \in
  \mathbb{R}^n.$$
The tensor norm is the operator norm of multilinear maps.

The assumption is the anchored smoothness assumption `LipschitzDerivsAnchored` of order $p$ for
$\Phi_\ell$ on the whole space, with the open set and the anchor set equal to $\mathbb{R}^n$,
together with $L \ge 0$. The form above is
`CartisGouldToint.Chapter05.AssumptionPhiDpL.lipschitz` and
`CartisGouldToint.Chapter05.AssumptionPhiDpL.of_lipschitz`. -/
abbrev AssumptionPhiDpL (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (p : ℕ) (L : ℝ) : Prop :=
  LipschitzDerivsAnchored (Phi r ℓ) univ univ p p (fun _ => L) ∧ 0 ≤ L

namespace AssumptionPhiDpL

variable {r : ℝⁿ → ℝᵐ} {ℓ : ℝ} {p : ℕ} {L : ℝ}

/-- Under assumption $\Phi_\ell$.DpL, $\Phi_\ell$ is $p$ times continuously differentiable. -/
theorem contDiff (h : AssumptionPhiDpL r ℓ p L) : ContDiff ℝ p (Phi r ℓ) :=
  h.1.contDiff

/-- The Lipschitz constant $L$ of assumption $\Phi_\ell$.DpL is nonnegative. -/
theorem nonneg (h : AssumptionPhiDpL r ℓ p L) : 0 ≤ L :=
  h.2

/-- Under assumption $\Phi_\ell$.DpL with constant $L$, the $p$-th derivative $\nabla^p\Phi_\ell$ is
$L$-Lipschitz on $\mathbb{R}^n$. -/
theorem lipschitz (h : AssumptionPhiDpL r ℓ p L) :
    IteratedFDerivLipschitzOn (Phi r ℓ) p L univ :=
  (lipschitzDerivsAnchored_univ_top_iff.1 h.1).2

/-- If $\Phi_\ell$ is $p$ times continuously differentiable, $L \ge 0$, and $\nabla^p\Phi_\ell$ is
$L$-Lipschitz on $\mathbb{R}^n$, then assumption $\Phi_\ell$.DpL holds with constant $L$. -/
theorem of_lipschitz (hf : ContDiff ℝ p (Phi r ℓ)) (hL0 : 0 ≤ L)
    (hL : IteratedFDerivLipschitzOn (Phi r ℓ) p L univ) : AssumptionPhiDpL r ℓ p L :=
  ⟨lipschitzDerivsAnchored_univ_top_iff.2 ⟨hf, hL⟩, hL0⟩

end AssumptionPhiDpL

/-- **Algorithm 5.1.1** of [cartis2022evaluation], Step 1: the termination test (5.1.9)–(5.1.14) of
ARpLE. Let $r : \mathbb{R}^n \to \mathbb{R}^m$, $\ell \in \mathbb{R}$, an order $q$, tolerances
$\epsilon_0, \epsilon_1, \epsilon_2, \epsilon_3$, a set $M = \mathcal{M}_k$ of directions and a
point $x$ be given. The test holds at $x$ if one of the following holds:

* $\|r(x)\| \le \epsilon_0$ (5.1.9);
* $q = 1$ and $\psi_{\ell,1}(x) \le \epsilon_1$ (5.1.10);
* $q \ge 2$, (5.1.10) holds, and $\psi_{\ell,2}(x) > \epsilon_2$, which is the
  strict-local-minimizer test (5.1.11);
* $q = 2$, (5.1.10) holds, and $\psi_{\ell,2}(x) \ge -\epsilon_2$ (5.1.12);
* $q = 3$, (5.1.10) and (5.1.12) hold, and $\psi_{\ell,3}(x, d) \le \epsilon_3$ and
  $\psi_{\ell,2}(x, d) \le \epsilon_2$ for all $d \in M$ (5.1.13)–(5.1.14).

**Correction.** The book also requires $\mathcal{M}_k \neq \emptyset$ in the last branch. With
that requirement the proof of Theorem 5.1.7 fails when $\mathcal{M}_{k+1} = \emptyset$: then
none of (5.1.48)–(5.1.49) or (5.1.51)–(5.1.52) needs to hold, and there is no guaranteed
decrease. The test here drops the requirement and reads the condition "for all
$d \in \mathcal{M}_k$" vacuously. The guarantee at termination, for all
$d \in \mathcal{M}_\epsilon$, is unchanged.

The book's tolerances $\epsilon_2 = \epsilon_3 = \infty$ correspond to $q = 1$, and
$\epsilon_3 = \infty > \epsilon_2$ to $q = 2$. The tolerances of index greater than $q$ are not
used. -/
def ARpLEStop (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (q : ℕ) (ε₀ ε₁ ε₂ ε₃ : ℝ) (M : Set ℝⁿ) (x : ℝⁿ) : Prop :=
  ‖r x‖ ≤ ε₀ ∨
    (q = 1 ∧ psiOne r ℓ x ≤ ε₁) ∨
    (2 ≤ q ∧ psiOne r ℓ x ≤ ε₁ ∧ ε₂ < psiTwo r ℓ x) ∨
    (q = 2 ∧ psiOne r ℓ x ≤ ε₁ ∧ -ε₂ ≤ psiTwo r ℓ x) ∨
    (q = 3 ∧ psiOne r ℓ x ≤ ε₁ ∧ -ε₂ ≤ psiTwo r ℓ x ∧
      ∀ d ∈ M, psiThree r ℓ x d ≤ ε₃ ∧ psiTwoDir r ℓ x d ≤ ε₂)

/-- The direction sets $\mathcal{M}_k$ of ARpLE: Step 0 and (4.1.14) of Algorithm 4.1.1 of
[cartis2022evaluation], applied to $f = \Phi_\ell$. The set $\mathcal{M}_0$ consists of the unit
vectors $d$ with $|\nabla^2\Phi_\ell(x_0)[d]^2| \le \epsilon_2$, and $\mathcal{M}_{k+1}$
consists of the unit vectors $d$ with $|\nabla^2 m_k(s_k)[d]^2| \le \theta_2\|s_k\|^{p-1}$,
where $m_k$ is the regularized Taylor model of $\Phi_\ell$ of degree $p$ at $x_k$ with weight
$\sigma_k$. -/
noncomputable def mdir (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (p : ℕ) (P : ARpParams) (ε₂ : ℝ) (x s : ℕ → ℝⁿ)
    (σ : ℕ → ℝ) : ℕ → Set ℝⁿ
  | 0 => smallCurvatureDirections (iteratedFDeriv ℝ 2 (Phi r ℓ) (x 0)) ε₂
  | k + 1 => smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ (Phi r ℓ) (x k)) p (σ k)) (s k))
      (P.θ₂ * ‖s k‖ ^ (p - 1))

/-- The set $\mathcal{M}_{k+1}$ consists of the unit vectors $d$ with $|\nabla^2 m_k(s_k)[d]^2| \le
\theta_2\|s_k\|^{p-1}$. -/
theorem mdir_succ (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (p : ℕ) (P : ARpParams) (ε₂ : ℝ) (x s : ℕ → ℝⁿ)
    (σ : ℕ → ℝ) (k : ℕ) :
    mdir r ℓ p P ε₂ x s σ (k + 1) = smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ (Phi r ℓ) (x k)) p (σ k)) (s k))
      (P.θ₂ * ‖s k‖ ^ (p - 1)) :=
  rfl

/-- Every element of $\mathcal{M}_k$ is a unit vector. -/
theorem norm_eq_one_of_mem_mdir {r : ℝⁿ → ℝᵐ} {ℓ : ℝ} {p : ℕ} {P : ARpParams} {ε₂ : ℝ}
    {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {k : ℕ} {d : ℝⁿ} (hd : d ∈ mdir r ℓ p P ε₂ x s σ k) : ‖d‖ = 1 := by
  cases k with
  | zero => exact hd.1
  | succ k => exact hd.1

/-- **Algorithm 5.1.1** of [cartis2022evaluation] (ARpLE), as a run predicate. Let
$r : \mathbb{R}^n \to \mathbb{R}^m$, $\ell \in \mathbb{R}$, $p \in \mathbb{N}$, the constants
$P$ ($\sigma_0$, $\sigma_{\min}$, $\eta_1$, $\eta_2$, $\gamma_1$, $\gamma_2$, $\gamma_3$,
$\theta_1$, $\theta_2$, $\theta_3$), an order $q$ and tolerances $\epsilon_0, \dots, \epsilon_3$
be given. Sequences of iterates $x_k$, steps $s_k$ and weights $\sigma_k$ form a **run of
ARpLE** if they form a run of the ARp method (Algorithm 4.1.1) for $f = \Phi_\ell$ with the
model (5.1.8), the order $q$, the constants $P$, and the Step 1 test
`CartisGouldToint.Chapter05.ARpLEStop` with the direction sets $\mathcal{M}_k$ of
`CartisGouldToint.Chapter05.mdir`. Iteration $k$ is successful if $\rho_k \ge \eta_1$, where
$\rho_k$ is the ratio (4.1.15) for $\Phi_\ell$.

The ARp run is `Optimization.IsARpRun`, and $\rho_k$ is
`Optimization.taylorRatio (Phi r ℓ) p x s k`. The test drops the book's requirement
$\mathcal{M}_k \neq \emptyset$; see `CartisGouldToint.Chapter05.ARpLEStop`. -/
def algorithm_5_1_1 (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (p : ℕ) (P : ARpParams) (q : ℕ)
    (ε₀ ε₁ ε₂ ε₃ : ℝ) (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) : Prop :=
  IsARpRun (Phi r ℓ) p P q
    (fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k)) x s σ

namespace algorithm_5_1_1

variable {r : ℝⁿ → ℝᵐ} {ℓ : ℝ} {p q : ℕ} {P : ARpParams} {ε₀ ε₁ ε₂ ε₃ : ℝ} {x s : ℕ → ℝⁿ}
  {σ : ℕ → ℝ}

/-- A run of ARpLE is a run of the ARp method for $\Phi_\ell$ with the termination test of ARpLE. -/
theorem isARpRun (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ) :
    IsARpRun (Phi r ℓ) p P q
      (fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k)) x s σ :=
  h

/-- Let $\ell > 0$. Along a run of ARpLE, the residual norm does not increase before termination: if
the test fails at every $j \le k$, then $\|r(x_{k+1})\| \le \|r(x_k)\|$. -/
theorem norm_succ_le (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ) (hℓ : 0 < ℓ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ j) (x j)) :
    ‖r (x (k + 1))‖ ≤ ‖r (x k)‖ := by
  have hk' : ∀ j ≤ k, ¬ IsARRun.Stop
      (fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k)) (fun _ => False) j :=
    fun j hj h' => h'.elim (hk j hj) id
  by_cases hs : P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k
  · obtain ⟨-, hdec⟩ := h.isARpRun.toIsARRun.sub_ge_of_succ_taylor hk'
      (h.isARpRun.step_spec hk).decrease hs
    have hσ : 0 ≤ σ k := (h.isARpRun.sigma_pos (k := k) fun j hj => hk j hj.le).le
    have : 0 ≤ P.η₁ * (σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1)) := by
      have := P.η₁_pos; positivity
    have hle : Phi r ℓ (x (k + 1)) ≤ Phi r ℓ (x k) := by linarith
    rw [Phi_apply, Phi_apply, div_le_div_iff_of_pos_right hℓ] at hle
    exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hℓ).1 hle
  · rw [h.isARpRun.eq_of_not_succ hk hs]

/-- Let $\ell > 0$. Along a run of ARpLE, $\|r(x_k)\| \le \|r(x_0)\|$ for every $k$ such that the
test fails at every $j < k$. -/
theorem norm_le_norm_zero (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ) (hℓ : 0 < ℓ) :
    ∀ k, (∀ j < k, ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ j) (x j)) →
      ‖r (x k)‖ ≤ ‖r (x 0)‖ := by
  intro k
  induction k with
  | zero => exact fun _ => le_rfl
  | succ k ih =>
    intro hk
    exact (h.norm_succ_le hℓ fun j hj => hk j (Nat.lt_succ_of_le hj)).trans
      (ih fun j hj => hk j (hj.trans k.lt_succ_self))

end algorithm_5_1_1

/-! ### Bounds on the residual decrease -/

/-- The constant
$$\kappa_1 = \frac{\eta_1\sigma_{\min}}{(p+1)!}\left(\frac{p!}{L + \sigma_{\max} + \theta_1
  p!}\right)^{(p+1)/p}$$
of (4.1.32) of [cartis2022evaluation], with $\sigma_{\max} = \max(\sigma_0, \gamma_3 L/(1 -
\eta_2))$ of (4.1.19). -/
noncomputable def kappa₁ (P : ARpParams) (L : ℝ) (p : ℕ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    ((p ! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₁ * p !)) ^ (((p : ℝ) + 1) / p)

/-- The constant $\kappa_{s2} = (p-1)!/(L + \sigma_{\max} + \theta_2 (p-1)!)$ of (4.1.23) of
[cartis2022evaluation]. -/
noncomputable def kappaS₂ (P : ARpParams) (L : ℝ) (p : ℕ) : ℝ :=
  ((p - 1)! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!)

/-- The constant $\kappa_2 = \frac{\eta_1\sigma_{\min}}{(p+1)!}\kappa_{s2}^{(p+1)/(p-1)}$ of
(4.1.34) of [cartis2022evaluation]. -/
noncomputable def kappa₂ (P : ARpParams) (L : ℝ) (p : ℕ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) * kappaS₂ P L p ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))

/-- The constant
$$\kappa_3 = \frac{\eta_1\sigma_{\min}}{(p+1)!}\left(\frac{(p-2)!}{L + \sigma_{\max} + \theta_3
  (p-2)!}\right)^{(p+1)/(p-2)}$$
of (4.1.36) of [cartis2022evaluation]. -/
noncomputable def kappa₃ (P : ARpParams) (L : ℝ) (p : ℕ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    (((p - 2)! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₃ * (p - 2)!)) ^
      (((p : ℝ) + 1) / ((p : ℝ) - 2))

section Constants

variable {P : ARpParams} {L : ℝ} {p : ℕ}

private theorem sum_pos (hL : 0 ≤ L) {θ : ℝ} (hθ : 0 < θ) (j : ℕ) :
    0 < L + arSigmaMax P.toARParams L + θ * (j ! : ℝ) := by
  have := arSigmaMax_pos P.toARParams L
  positivity

private theorem coef_nonneg : 0 ≤ P.η₁ * P.σmin / ((p + 1)! : ℝ) := by
  have := P.η₁_pos; have := P.σmin_nonneg; positivity

/-- If $L \ge 0$, then $\kappa_1 \ge 0$. -/
theorem kappa₁_nonneg (hL : 0 ≤ L) : 0 ≤ kappa₁ P L p := by
  have := sum_pos (P := P) hL P.θ₁_pos p
  have := coef_nonneg (P := P) (p := p)
  unfold kappa₁; positivity

/-- If $L \ge 0$, then $\kappa_{s2} > 0$. -/
theorem kappaS₂_pos (hL : 0 ≤ L) : 0 < kappaS₂ P L p := by
  have := sum_pos (P := P) hL P.θ₂_pos (p - 1)
  unfold kappaS₂; positivity

/-- If $L \ge 0$, then $\kappa_2 \ge 0$. -/
theorem kappa₂_nonneg (hL : 0 ≤ L) : 0 ≤ kappa₂ P L p := by
  have := (kappaS₂_pos (P := P) (p := p) hL).le
  have := coef_nonneg (P := P) (p := p)
  unfold kappa₂; positivity

/-- If $L \ge 0$, then $\kappa_3 \ge 0$. -/
theorem kappa₃_nonneg (hL : 0 ≤ L) : 0 ≤ kappa₃ P L p := by
  have := sum_pos (P := P) hL P.θ₃_pos (p - 2)
  have := coef_nonneg (P := P) (p := p)
  unfold kappa₃; positivity

/-- If $L \ge 0$ and $\sigma_{\min} > 0$, then $\kappa_1 > 0$. -/
theorem kappa₁_pos (hL : 0 ≤ L) (hσ : 0 < P.σmin) : 0 < kappa₁ P L p := by
  have := sum_pos (P := P) hL P.θ₁_pos p
  have := P.η₁_pos
  unfold kappa₁; positivity

/-- If $L \ge 0$ and $\sigma_{\min} > 0$, then $\kappa_2 > 0$. -/
theorem kappa₂_pos (hL : 0 ≤ L) (hσ : 0 < P.σmin) : 0 < kappa₂ P L p := by
  have := kappaS₂_pos (P := P) (p := p) hL
  have := P.η₁_pos
  unfold kappa₂; positivity

/-- If $L \ge 0$ and $\sigma_{\min} > 0$, then $\kappa_3 > 0$. -/
theorem kappa₃_pos (hL : 0 ≤ L) (hσ : 0 < P.σmin) : 0 < kappa₃ P L p := by
  have := sum_pos (P := P) hL P.θ₃_pos (p - 2)
  have := P.η₁_pos
  unfold kappa₃; positivity

end Constants

section Decrease

variable {r : ℝⁿ → ℝᵐ} {p q : ℕ} {P : ARpParams} {ε₀ ε₁ ε₂ ε₃ L : ℝ} {x s : ℕ → ℝⁿ}
  {σ : ℕ → ℝ}

/-- For $\omega, t \ge 0$, $(\omega/t) \, t \le \omega$. -/
private theorem div_mul_le_self {ω t : ℝ} (hω : 0 ≤ ω) (ht : 0 ≤ t) : ω / t * t ≤ ω := by
  rcases ht.lt_or_eq with ht | ht
  · rw [div_mul_cancel₀ _ ht.ne']
  · rw [← ht, mul_zero]; exact hω

/-- The decreases of Lemma 4.1.4 for $f = \Phi_\ell$, multiplied by $\ell$ and stated with the
unscaled measures at $x_{k+1}$, together with the step-length bound (4.1.37) with (4.1.23). -/
private theorem decrease_unscaled {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ) (hΦ : AssumptionPhiDpL r ℓ p L)
    (hp : 1 ≤ p) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ j) (x j))
    (hs : P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k) :
    ℓ * kappa₁ P L p * ‖fderiv ℝ (Phi r ℓ) (x (k + 1))‖ ^ (((p : ℝ) + 1) / p) ≤
        ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ ∧
    (2 ≤ q → ℓ * kappa₂ P L p *
        (max 0 (-minCurvature (iteratedFDeriv ℝ 2 (Phi r ℓ) (x (k + 1))))) ^
          (((p : ℝ) + 1) / ((p : ℝ) - 1)) ≤ ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ) ∧
    (3 ≤ q → ∀ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1), ℓ * kappa₃ P L p *
        |iteratedFDeriv ℝ 3 (Phi r ℓ) (x (k + 1)) (fun _ => d)| ^
          (((p : ℝ) + 1) / ((p : ℝ) - 2)) ≤ ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ) ∧
    (2 ≤ q → ∀ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1),
      |iteratedFDeriv ℝ 2 (Phi r ℓ) (x (k + 1)) (fun _ => d)| ≤ ‖s k‖ ^ (p - 1) / kappaS₂ P L p) ∧
    (2 ≤ q → ∀ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1), ℓ * kappa₂ P L p *
        |iteratedFDeriv ℝ 2 (Phi r ℓ) (x (k + 1)) (fun _ => d)| ^
          (((p : ℝ) + 1) / ((p : ℝ) - 1)) ≤ ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ) := by
  obtain ⟨d0, d1, d2, d3⟩ := h.isARpRun.decrease_ge hΦ.contDiff hΦ.lipschitz hΦ.nonneg hp hqp hk hs
  obtain ⟨-, -, -, -, b5⟩ :=
    h.isARpRun.step_lower_bounds hΦ.contDiff hΦ.lipschitz hΦ.nonneg hp hqp hk hs
  have hsub : Phi r ℓ (x k) - Phi r ℓ (x (k + 1)) =
      (‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ) / ℓ := by
    rw [Phi_apply, Phi_apply]; ring
  have hmul : ∀ {c : ℝ}, c ≤ Phi r ℓ (x k) - Phi r ℓ (x (k + 1)) →
      ℓ * c ≤ ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ := fun hc => by
    rw [hsub, le_div_iff₀ hℓ] at hc; linarith
  have hK2 := kappaS₂_pos (P := P) (p := p) hΦ.nonneg
  -- (4.1.23) in the form `|∇²Φ(x_{k+1})[d]²| ≤ ‖s_k‖^{p-1}/κ_{s2}`
  have h18 : 2 ≤ q → ∀ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1),
      |iteratedFDeriv ℝ 2 (Phi r ℓ) (x (k + 1)) (fun _ => d)| ≤
        ‖s k‖ ^ (p - 1) / kappaS₂ P L p := fun hq d hd => by
    have hfac : (0 : ℝ) < (p - 1)! := by positivity
    have hK := sum_pos (P := P) hΦ.nonneg P.θ₂_pos (p - 1)
    refine (b5 hq d hd).trans_eq ?_
    rw [kappaS₂]
    field_simp
  refine ⟨by rw [mul_assoc]; exact hmul d1, fun hq => by rw [mul_assoc]; exact hmul (d2 hq),
    fun hq d hd => by rw [mul_assoc]; exact hmul (d3 hq d hd), h18, fun hq d hd => ?_⟩
  -- (5.1.57): the decrease from `‖s_k‖^{p-1} ≥ κ_{s2} |∇²Φ[d]²|`
  have hp2 : 2 ≤ p := hq.trans hqp
  have hstep : kappaS₂ P L p * |iteratedFDeriv ℝ 2 (Phi r ℓ) (x (k + 1)) (fun _ => d)| ≤
      ‖s k‖ ^ (p - 1) := by
    have := h18 hq d hd
    rw [le_div_iff₀ hK2] at this; linarith
  have hn : ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) := by push_cast; ring
  have hm : ((p : ℝ) - 1) = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hpow := Real.rpow_div_le_pow_of_le_pow (n := p + 1) (by positivity) (norm_nonneg _)
    (by omega) hstep
  rw [← hn, ← hm, Real.mul_rpow hK2.le (abs_nonneg _)] at hpow
  have hc := coef_nonneg (P := P) (p := p)
  rw [mul_assoc]
  refine hmul (le_trans ?_ d0)
  rw [kappa₂, mul_assoc]
  exact mul_le_mul_of_nonneg_left hpow hc

private theorem max_zero_neg_div {a t : ℝ} (ht : 0 ≤ t) : max 0 (-(a / t)) = max 0 (-a) / t := by
  rw [← max_div_div_right ht, zero_div, neg_div]

/-- **Lemma 5.1.2** of [cartis2022evaluation]. Let $\ell > 0$, let $\Phi_\ell$ satisfy assumption
$\Phi_\ell$.DpL with constant $L$, let $p \ge 1$ and $q \le p$, and let $(x_k, s_k, \sigma_k)$
be a run of ARpLE. Let $k$ be a successful iteration ($\rho_k \ge \eta_1$) such that the test
fails at every $j \le k$. Let $\kappa_1$, $\kappa_2$, $\kappa_3$ and $\kappa_{s2}$ be the
constants of (4.1.32), (4.1.34), (4.1.36) and (4.1.23) for $L = L_{\Phi_\ell,p}$. Then
$$\|r(x_k)\|^\ell - \|r(x_{k+1})\|^\ell \ge \kappa_1 \ell \, \psi_{\ell,1}(x_{k+1})^{(p+1)/p} \,
  \|r(x_{k+1})\|^{(\ell-1)(p+1)/p}. \qquad (5.1.15)$$
If $q \ge 2$, then
$$\|r(x_k)\|^\ell - \|r(x_{k+1})\|^\ell \ge \kappa_2 \ell \, \max(0,
  -\psi_{\ell,2}(x_{k+1}))^{(p+1)/(p-1)} \, \|r(x_{k+1})\|^{(\ell-1)(p+1)/(p-1)}. \qquad
  (5.1.16)$$
If $q \ge 3$, then for every $d \in \mathcal{M}_{k+1}$
$$\|r(x_k)\|^\ell - \|r(x_{k+1})\|^\ell \ge \kappa_3 \ell \, \psi_{\ell,3}(x_{k+1},
  d)^{(p+1)/(p-2)} \, \|r(x_{k+1})\|^{(\ell-1)(p+1)/(p-2)}. \qquad (5.1.17)$$
If $q \ge 2$, then for every $d \in \mathcal{M}_{k+1}$
$$\psi_{\ell,2}(x_{k+1}, d) \, \|r(x_{k+1})\|^{\ell-1} \le \frac{\|s_k\|^{p-1}}{\kappa_{s2}}.
  \qquad (5.1.18)$$

The proof applies Lemma 4.1.4 to $f = \Phi_\ell$ and undoes the scaling of the measures. -/
theorem lemma_5_1_2 {ℓ : ℝ} (hℓ : 0 < ℓ) (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ)
    (hΦ : AssumptionPhiDpL r ℓ p L) (hp : 1 ≤ p) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ j) (x j))
    (hs : P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k) :
    kappa₁ P L p * ℓ * psiOne r ℓ (x (k + 1)) ^ (((p : ℝ) + 1) / p) *
        ‖r (x (k + 1))‖ ^ ((ℓ - 1) * (((p : ℝ) + 1) / p)) ≤
      ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ ∧
    (2 ≤ q → kappa₂ P L p * ℓ *
        max 0 (-psiTwo r ℓ (x (k + 1))) ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) *
        ‖r (x (k + 1))‖ ^ ((ℓ - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1))) ≤
      ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ) ∧
    (3 ≤ q → ∀ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1), kappa₃ P L p * ℓ *
        psiThree r ℓ (x (k + 1)) d ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)) *
        ‖r (x (k + 1))‖ ^ ((ℓ - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 2))) ≤
      ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ) ∧
    (2 ≤ q → ∀ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1),
      psiTwoDir r ℓ (x (k + 1)) d * ‖r (x (k + 1))‖ ^ (ℓ - 1) ≤
        ‖s k‖ ^ (p - 1) / kappaS₂ P L p) := by
  obtain ⟨d1, d2, d3, d4, -⟩ := decrease_unscaled hℓ h hΦ hp hqp hk hs
  have hb := norm_nonneg (r (x (k + 1)))
  have hL := hΦ.nonneg
  have hν : ∀ j : ℕ, j < p → (0 : ℝ) < ((p : ℝ) + 1) / ((p : ℝ) - j) := fun j hj => by
    have : (j : ℝ) < p := by exact_mod_cast hj
    exact div_pos (by positivity) (by linarith)
  -- undo the scaling
  have key : ∀ κ ω ν : ℝ, 0 ≤ κ → 0 ≤ ω → 0 < ν →
      ℓ * κ * ω ^ ν ≤ ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ →
      κ * ℓ * (ω / ‖r (x (k + 1))‖ ^ (ℓ - 1)) ^ ν * ‖r (x (k + 1))‖ ^ ((ℓ - 1) * ν) ≤
        ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ := fun κ ω ν hκ hω hν' hdec => by
    refine le_trans ?_ hdec
    rw [mul_comm κ ℓ, mul_assoc (ℓ * κ)]
    exact mul_le_mul_of_nonneg_left (div_rpow_mul_le hω hb hν') (by positivity)
  refine ⟨?_, fun hq => ?_, fun hq d hd => ?_, fun hq d hd => ?_⟩
  · rw [psiOne_eq]
    have := hν 0 (by omega)
    simp only [Nat.cast_zero, sub_zero] at this
    exact key _ _ _ (kappa₁_nonneg hL) (norm_nonneg _) this d1
  · rw [psiTwo_eq, max_zero_neg_div (Real.rpow_nonneg hb _)]
    have := hν 1 (by omega)
    simp only [Nat.cast_one] at this
    exact key _ _ _ (kappa₂_nonneg hL) (le_max_left _ _) this (d2 hq)
  · have := hν 2 (by omega)
    simp only [Nat.cast_ofNat] at this
    exact key _ _ _ (kappa₃_nonneg hL) (abs_nonneg _) this (d3 hq d hd)
  · exact (div_mul_le_self (abs_nonneg _) (Real.rpow_nonneg hb _)).trans (d4 hq d hd)

end Decrease

/-- **Lemma 5.1.3** of [cartis2022evaluation] (cascading differences). Let $a \ge b \ge 0$ be real
numbers, and let $i \ge 0$ and $\ell \ge 1$ be integers. Then
$$a^{1/2^i} - b^{1/2^i} \ge \frac{a^\ell - b^\ell}{2^i \, \ell \, a^{(2^i - 1)/2^i + \ell -
  1}}.$$

When $a = 0$, both sides vanish, by Lean's convention $x/0 = 0$. -/
theorem lemma_5_1_3 {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (i : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (a ^ ℓ - b ^ ℓ) / (2 ^ i * ℓ * a ^ (((2 : ℝ) ^ i - 1) / 2 ^ i + ℓ - 1)) ≤
      a ^ (1 / 2 ^ i : ℝ) - b ^ (1 / 2 ^ i : ℝ) :=
  rpow_inv_two_pow_sub_ge hb hba i hℓ

/-! ### Exponents -/

/-- **Equations (5.1.21), (5.1.23) and (5.1.25)** of [cartis2022evaluation]. For
$j, p, i \in \mathbb{N}$ and $\ell \in \mathbb{R}$, the exponent is
$$\iota_j(p, \ell, i) = \frac{2^i - 1}{2^i} - \frac{j(\ell - 1)}{p - j + 1}.$$
The book uses $j = 1$ in (5.1.21), $j = 2$ in (5.1.23) and $j = 3$ in (5.1.25). -/
noncomputable def iota (j p : ℕ) (ℓ : ℝ) (i : ℕ) : ℝ :=
  ((2 : ℝ) ^ i - 1) / 2 ^ i - j * (ℓ - 1) / ((p : ℝ) - j + 1)

/-- The exponent satisfies $\iota_j(p, \ell, i) = (2^i - 1)/2^i - j(\ell - 1)/(p - j + 1)$. -/
theorem iota_def (j p : ℕ) (ℓ : ℝ) (i : ℕ) :
    iota j p ℓ i = ((2 : ℝ) ^ i - 1) / 2 ^ i - j * (ℓ - 1) / ((p : ℝ) - j + 1) :=
  rfl

/-- If $p \ge 1$, then $\iota_1 = (2^i - 1)/2^i - (\ell - 1)((p+1)/p - 1)$. -/
theorem iota_one_eq {p : ℕ} (hp : 1 ≤ p) (ℓ : ℝ) (i : ℕ) :
    iota 1 p ℓ i = ((2 : ℝ) ^ i - 1) / 2 ^ i - (ℓ - 1) * (((p : ℝ) + 1) / p - 1) := by
  have : (p : ℝ) ≠ 0 := by positivity
  rw [iota]; push_cast; rw [sub_add_cancel]; field_simp; ring

/-- If $p \ge 2$, then $\iota_2 = (2^i - 1)/2^i - (\ell - 1)((p+1)/(p-1) - 1)$. -/
theorem iota_two_eq {p : ℕ} (hp : 2 ≤ p) (ℓ : ℝ) (i : ℕ) :
    iota 2 p ℓ i = ((2 : ℝ) ^ i - 1) / 2 ^ i - (ℓ - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1) - 1) := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) - 2 + 1 = (p : ℝ) - 1 := by ring
  rw [iota]; push_cast; rw [h2]; field_simp; ring

/-- If $p \ge 3$, then $\iota_3 = (2^i - 1)/2^i - (\ell - 1)((p+1)/(p-2) - 1)$. -/
theorem iota_three_eq {p : ℕ} (hp : 3 ≤ p) (ℓ : ℝ) (i : ℕ) :
    iota 3 p ℓ i = ((2 : ℝ) ^ i - 1) / 2 ^ i - (ℓ - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 2) - 1) := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have : (p : ℝ) - 2 ≠ 0 := by linarith
  have h2 : (p : ℝ) - 3 + 1 = (p : ℝ) - 2 := by ring
  rw [iota]; push_cast; rw [h2]; field_simp; ring

/-- **Equation (5.1.34)** of [cartis2022evaluation]. If $p \ge 2$, then $\iota_1 = \iota_2 + (\ell -
1)(p + 1)/(p(p - 1))$. -/
theorem iota_one_eq_iota_two_add {p : ℕ} (hp : 2 ≤ p) (ℓ : ℝ) (i : ℕ) :
    iota 1 p ℓ i = iota 2 p ℓ i + (ℓ - 1) * (p + 1) / (p * (p - 1)) := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  have : (p : ℝ) ≠ 0 := by linarith
  rw [iota_one_eq (by omega), iota_two_eq hp]; field_simp; ring

/-- **Equation (5.1.36)** of [cartis2022evaluation]. If $p \ge 3$, then $\iota_1 = \iota_3 +
2(\ell - 1)(p + 1)/(p(p - 2))$. -/
theorem iota_one_eq_iota_three_add {p : ℕ} (hp : 3 ≤ p) (ℓ : ℝ) (i : ℕ) :
    iota 1 p ℓ i = iota 3 p ℓ i + 2 * (ℓ - 1) * (p + 1) / (p * (p - 2)) := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have : (p : ℝ) - 2 ≠ 0 := by linarith
  have : (p : ℝ) ≠ 0 := by linarith
  rw [iota_one_eq (by omega), iota_three_eq hp]; field_simp; ring

/-- **Equation (5.1.37)** of [cartis2022evaluation]. If $p \ge 3$, then $\iota_2 = \iota_3 + (\ell -
1)(p + 1)/((p - 1)(p - 2))$. -/
theorem iota_two_eq_iota_three_add {p : ℕ} (hp : 3 ≤ p) (ℓ : ℝ) (i : ℕ) :
    iota 2 p ℓ i = iota 3 p ℓ i + (ℓ - 1) * (p + 1) / ((p - 1) * (p - 2)) := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have : (p : ℝ) - 2 ≠ 0 := by linarith
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [iota_two_eq (by omega), iota_three_eq hp]; field_simp; ring

/-! ### Lemma 5.1.4 -/

/-- The real-number core of (5.1.20), (5.1.22) and (5.1.24) in the proof of Lemma 5.1.4 of
[cartis2022evaluation]. Let $\ell \ge 1$ and $i$ be natural numbers, let $\nu > 0$,
$\iota = (2^i - 1)/2^i - (\ell - 1)(\nu - 1)$, $\beta > 0$ and $\kappa, \psi \ge 0$, and let
$0 \le b \le a$ with $b > \beta a$. If $a^\ell - b^\ell \ge \kappa \ell \psi^\nu
b^{(\ell-1)\nu}$, which is the form of Lemma 5.1.2, then
$$a^{1/2^i} - b^{1/2^i} \ge \frac{\kappa\beta^{(\ell-1)\nu}}{2^i} \, \frac{\psi^\nu}{a^\iota}.$$
-/
theorem rpow_inv_two_pow_sub_ge_of_decrease {ℓ i : ℕ} (hℓ : 1 ≤ ℓ) {ν ι β κ ψ a b : ℝ}
    (hν : 0 < ν) (hι : ι = ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) * (ν - 1)) (hβ : 0 < β)
    (hκ : 0 ≤ κ) (hψ : 0 ≤ ψ) (hb : 0 ≤ b) (hba : b ≤ a) (hβab : β * a < b)
    (hdec : κ * ℓ * ψ ^ ν * b ^ (((ℓ : ℝ) - 1) * ν) ≤ a ^ (ℓ : ℝ) - b ^ (ℓ : ℝ)) :
    κ * β ^ (((ℓ : ℝ) - 1) * ν) / 2 ^ i * ψ ^ ν / a ^ ι ≤
      a ^ (1 / 2 ^ i : ℝ) - b ^ (1 / 2 ^ i : ℝ) := by
  have ha : 0 < a := by
    rcases (hb.trans hba).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hβab; linarith
  set e := ((ℓ : ℝ) - 1) * ν with he_def
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have he : 0 ≤ e := mul_nonneg (by linarith) hν.le
  have hcasc := rpow_inv_two_pow_sub_ge hb hba i hℓ
  have hsplit : ((2 : ℝ) ^ i - 1) / 2 ^ i + ℓ - 1 = e + ι := by rw [hι, he_def]; ring
  rw [hsplit, Real.rpow_add ha] at hcasc
  rw [Real.rpow_natCast, Real.rpow_natCast] at hdec
  have hbe : (β * a) ^ e ≤ b ^ e := Real.rpow_le_rpow (by positivity) hβab.le he
  rw [Real.mul_rpow hβ.le ha.le] at hbe
  have hAe : 0 < a ^ e := Real.rpow_pos_of_pos ha _
  have hAι : 0 < a ^ ι := Real.rpow_pos_of_pos ha _
  have hℓpos : (0 : ℝ) < ℓ := by linarith
  have hψν : 0 ≤ ψ ^ ν := Real.rpow_nonneg hψ _
  calc κ * β ^ e / 2 ^ i * ψ ^ ν / a ^ ι
      = κ * ℓ * ψ ^ ν * (β ^ e * a ^ e) / (2 ^ i * ℓ * (a ^ e * a ^ ι)) := by
        field_simp
    _ ≤ κ * ℓ * ψ ^ ν * b ^ e / (2 ^ i * ℓ * (a ^ e * a ^ ι)) := by gcongr
    _ ≤ (a ^ ℓ - b ^ ℓ) / (2 ^ i * ℓ * (a ^ e * a ^ ι)) := by gcongr
    _ ≤ _ := hcasc

/-- The real-number core of (5.1.27) in Lemma 5.1.4 of [cartis2022evaluation]. If $0 \le b \le a$
and $b \le \beta a$ with $\beta \in [0, 1]$, then
$$a^{1/2^i} - b^{1/2^i} \ge (1 - \beta^{1/2^i}) \, a^{1/2^i} \ge (1 - \beta^{1/2^i}) \,
  b^{1/2^i}.$$
-/
theorem rpow_inv_two_pow_sub_ge_of_le_mul {i : ℕ} {β a b : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hb : 0 ≤ b) (hba : b ≤ a) (h : b ≤ β * a) :
    (1 - β ^ (1 / 2 ^ i : ℝ)) * a ^ (1 / 2 ^ i : ℝ) ≤
        a ^ (1 / 2 ^ i : ℝ) - b ^ (1 / 2 ^ i : ℝ) ∧
      (1 - β ^ (1 / 2 ^ i : ℝ)) * b ^ (1 / 2 ^ i : ℝ) ≤
        (1 - β ^ (1 / 2 ^ i : ℝ)) * a ^ (1 / 2 ^ i : ℝ) := by
  set α : ℝ := 1 / 2 ^ i
  have hα : 0 < α := by positivity
  have ha : 0 ≤ a := hb.trans hba
  have hbα : b ^ α ≤ β ^ α * a ^ α := by
    rw [← Real.mul_rpow hβ ha]; exact Real.rpow_le_rpow hb h hα.le
  have hβα : β ^ α ≤ 1 := Real.rpow_le_one hβ hβ1 hα.le
  refine ⟨?_, mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb hba hα.le) (by linarith)⟩
  have : (1 - β ^ α) * a ^ α = a ^ α - β ^ α * a ^ α := by ring
  linarith

section Decrease

variable {r : ℝⁿ → ℝᵐ} {p q : ℕ} {P : ARpParams} {ε₀ ε₁ ε₂ ε₃ L : ℝ} {x s : ℕ → ℝⁿ}
  {σ : ℕ → ℝ}

/-- The decrease (5.1.57) of [cartis2022evaluation] in the scaled form of Lemma 5.1.2. Under the
hypotheses of `CartisGouldToint.Chapter05.lemma_5_1_2`, if $q \ge 2$, then for every
$d \in \mathcal{M}_{k+1}$
$$\|r(x_k)\|^\ell - \|r(x_{k+1})\|^\ell \ge \kappa_2 \ell \, \psi_{\ell,2}(x_{k+1},
  d)^{(p+1)/(p-1)} \, \|r(x_{k+1})\|^{(\ell-1)(p+1)/(p-1)}.$$
It follows from (4.1.37) and (5.1.18). -/
theorem decrease_psiTwoDir {ℓ : ℝ} (hℓ : 0 < ℓ) (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ)
    (hΦ : AssumptionPhiDpL r ℓ p L) (hp : 1 ≤ p) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ j) (x j))
    (hs : P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k) (hq : 2 ≤ q) {d : ℝⁿ}
    (hd : d ∈ mdir r ℓ p P ε₂ x s σ (k + 1)) :
    kappa₂ P L p * ℓ * psiTwoDir r ℓ (x (k + 1)) d ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) *
        ‖r (x (k + 1))‖ ^ ((ℓ - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1))) ≤
      ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ := by
  obtain ⟨-, -, -, -, d5⟩ := decrease_unscaled hℓ h hΦ hp hqp hk hs
  have hb := norm_nonneg (r (x (k + 1)))
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hq.trans hqp
  have hν : (0 : ℝ) < ((p : ℝ) + 1) / ((p : ℝ) - 1) := div_pos (by positivity) (by linarith)
  refine le_trans ?_ (d5 hq d hd)
  rw [mul_comm (kappa₂ P L p) ℓ, mul_assoc (ℓ * kappa₂ P L p)]
  exact mul_le_mul_of_nonneg_left (div_rpow_mul_le (abs_nonneg _) hb hν)
    (mul_nonneg hℓ.le (kappa₂_nonneg hΦ.nonneg))

/-- **Lemma 5.1.4** of [cartis2022evaluation]. Let $\ell \ge 1$ be an integer, let $\Phi_\ell$
satisfy assumption $\Phi_\ell$.DpL with constant $L$, let $p \ge 1$ and $q \le p$, and let
$(x_k, s_k, \sigma_k)$ be a run of ARpLE. Let $k$ be a successful iteration such that the test
fails at every $j \le k$, let $\beta \in (0, 1)$ and let $i \ge 0$ be an integer. Write
$a = \|r(x_k)\|$, $b = \|r(x_{k+1})\|$, and
$$\kappa_{rj} = \frac{\kappa_j \beta^{(\ell-1)(p+1)/(p-j+1)}}{2^i} \quad (j = 1, 2, 3)$$
as in (5.1.21), (5.1.23) and (5.1.25), with $\iota_j = \iota_j(p, \ell, i)$. If $b > \beta a$
(5.1.19), then
$$a^{1/2^i} - b^{1/2^i} \ge \kappa_{r1} \frac{\psi_{\ell,1}(x_{k+1})^{(p+1)/p}}{a^{\iota_1}},
  \qquad (5.1.20)$$
if moreover $q \ge 2$, then
$$a^{1/2^i} - b^{1/2^i} \ge \kappa_{r2} \frac{\max(0,
  -\psi_{\ell,2}(x_{k+1}))^{(p+1)/(p-1)}}{a^{\iota_2}}, \qquad (5.1.22)$$
and if moreover $q \ge 3$, then for every $d \in \mathcal{M}_{k+1}$
$$a^{1/2^i} - b^{1/2^i} \ge \kappa_{r3} \frac{\psi_{\ell,3}(x_{k+1},
  d)^{(p+1)/(p-2)}}{a^{\iota_3}}. \qquad (5.1.24)$$
If $b \le \beta a$ (5.1.26), then with $\kappa_{r0} = 1 - \beta^{1/2^i}$ (5.1.28)
$$a^{1/2^i} - b^{1/2^i} \ge \kappa_{r0} \, a^{1/2^i} \ge \kappa_{r0} \, b^{1/2^i}. \qquad
  (5.1.27)$$
-/
theorem lemma_5_1_4 {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ)
    (hΦ : AssumptionPhiDpL r ℓ p L) (hp : 1 ≤ p) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ j) (x j))
    (hs : P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (i : ℕ) :
    (β * ‖r (x k)‖ < ‖r (x (k + 1))‖ →
      kappa₁ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i *
          psiOne r ℓ (x (k + 1)) ^ (((p : ℝ) + 1) / p) / ‖r (x k)‖ ^ iota 1 p ℓ i ≤
        ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ) - ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ) ∧
      (2 ≤ q → kappa₂ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1))) / 2 ^ i *
          max 0 (-psiTwo r ℓ (x (k + 1))) ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) /
            ‖r (x k)‖ ^ iota 2 p ℓ i ≤
        ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ) - ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ)) ∧
      (3 ≤ q → ∀ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1),
        kappa₃ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 2))) / 2 ^ i *
          psiThree r ℓ (x (k + 1)) d ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)) /
            ‖r (x k)‖ ^ iota 3 p ℓ i ≤
        ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ) - ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ))) ∧
    (‖r (x (k + 1))‖ ≤ β * ‖r (x k)‖ →
      (1 - β ^ (1 / 2 ^ i : ℝ)) * ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ) ≤
          ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ) - ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ) ∧
        (1 - β ^ (1 / 2 ^ i : ℝ)) * ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ) ≤
          (1 - β ^ (1 / 2 ^ i : ℝ)) * ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ)) := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  obtain ⟨l1, l2, l3, -⟩ := lemma_5_1_2 hℓpos h hΦ hp hqp hk hs
  have hba := h.norm_succ_le hℓpos hk
  have hb := norm_nonneg (r (x (k + 1)))
  have hL := hΦ.nonneg
  refine ⟨fun hβab => ⟨?_, fun hq => ?_, fun hq d hd => ?_⟩,
    fun hβab => rpow_inv_two_pow_sub_ge_of_le_mul hβ0.le hβ1.le hb hba hβab⟩
  · exact rpow_inv_two_pow_sub_ge_of_decrease hℓ (by positivity) (iota_one_eq hp _ i) hβ0
      (kappa₁_nonneg hL) psiOne_nonneg hb hba hβab l1
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hq.trans hqp
    exact rpow_inv_two_pow_sub_ge_of_decrease hℓ (div_pos (by positivity) (by linarith))
      (iota_two_eq (hq.trans hqp) _ i) hβ0 (kappa₂_nonneg hL) (le_max_left _ _) hb hba hβab
      (l2 hq)
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hq.trans hqp
    exact rpow_inv_two_pow_sub_ge_of_decrease hℓ (div_pos (by positivity) (by linarith))
      (iota_three_eq (hq.trans hqp) _ i) hβ0 (kappa₃_nonneg hL) psiThree_nonneg hb hba hβab
      (l3 hq d hd)

/-! ### Theorem 5.1.7 -/

/-- For $\kappa, \epsilon, \nu, \iota \ge 0$, $\epsilon \le \psi$ and $0 < a \le R$,
$\kappa\epsilon^\nu/\max(1, R^\iota) \le \kappa\psi^\nu/a^\iota$. -/
private theorem div_max_le_div {κ ε ψ ν ι a R : ℝ} (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hεψ : ε ≤ ψ)
    (hν : 0 ≤ ν) (hι : 0 ≤ ι) (ha : 0 < a) (haR : a ≤ R) :
    κ * ε ^ ν / max 1 (R ^ ι) ≤ κ * ψ ^ ν / a ^ ι := by
  have h1 : a ^ ι ≤ max 1 (R ^ ι) := (Real.rpow_le_rpow ha.le haR hι).trans (le_max_right _ _)
  have h2 : ε ^ ν ≤ ψ ^ ν := Real.rpow_le_rpow hε hεψ hν
  have : 0 ≤ κ * ε ^ ν := mul_nonneg hκ (Real.rpow_nonneg hε _)
  exact div_le_div₀ (mul_nonneg hκ (Real.rpow_nonneg (hε.trans hεψ) _))
    (mul_le_mul_of_nonneg_left h2 hκ) (Real.rpow_pos_of_pos ha _) h1

/-- **Theorem 5.1.7** of [cartis2022evaluation], general form, with the remark after its proof. Let
$q \in \{1, 2, 3\}$ with $q \le p$ and $p \ge 1$, let $\ell \ge 1$ and $i \ge 0$ be integers
with $\iota_j(p, \ell, i) \ge 0$ for $1 \le j \le q$, and let $\beta \in (0, 1)$. Let
$\Phi_\ell$ satisfy assumption $\Phi_\ell$.DpL with constant $L$, and let $(x_k, s_k, \sigma_k)$
be a run of ARpLE with $\epsilon_0 > 0$, $\epsilon_1 \ge 0$, $\epsilon_2 \ge 0$ if $q \ge 2$,
and $\epsilon_3 \ge 0$ if $q \ge 3$. Let $\delta > 0$ be a lower bound for the decreases
(5.1.58)–(5.1.59) of the potential $\|r(x_k)\|^{1/2^i}$:
$$\delta \le \kappa_{r0} \, \epsilon_0^{1/2^i}, \qquad \delta \le \frac{\kappa_{rj} \,
  \epsilon_j^{(p+1)/(p-j+1)}}{\max(1, \|r(x_0)\|^{\iota_j})} \quad (1 \le j \le q),$$
with $\kappa_{r0}$ and $\kappa_{rj}$ of Lemma 5.1.4. Then the run terminates: there is a first
index $k_\epsilon$ at which the test holds. The number of evaluations of $r$ is at most
$$A \, \frac{\|r(x_0)\|^{1/2^i}}{\delta} + \kappa^C, \qquad A = 1 +
  \frac{|\log\gamma_1|}{\log\gamma_2}, \quad \kappa^C = \frac{|\log\gamma_1| +
  \log(\sigma_{\max}/\sigma_0)}{\log\gamma_2} + 2,$$
and the number of evaluations of its derivatives is at most $\|r(x_0)\|^{1/2^i}/\delta + 2$.
Here $\sigma_{\max} = \max(\sigma_0, \gamma_3 L/(1 - \eta_2))$, and $\kappa^A = \kappa^S A$ in
the book's notation ((5.1.60)–(5.1.61)).

**Generalization.** The book's choice $\delta = \min_j \kappa_{rj} \cdot \min_j
\epsilon_j^{(p+1)/(p-j+1)}/\max(1, \|r(x_0)\|^{\iota_1}, \dots)$ gives Theorem 5.1.7
(`CartisGouldToint.Chapter05.theorem_5_1_7`). The cases $q = 1$ and $q = 2$ are the first- and
second-order variants that the book mentions after its proof.

A positive $\delta$ as above exists only if $\sigma_{\min} > 0$, because the constants
$\kappa_{rj}$ vanish when $\sigma_{\min} = 0$. The termination index is
`Optimization.IsFirstHit` for the test, and the counts are `Optimization.funEvalCount` and
`Optimization.derivEvalCount` with the successful iterations. -/
theorem theorem_5_1_7_of_iota_nonneg {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3)
    (hp : 1 ≤ p) (hqp : q ≤ p) (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ)
    (hΦ : AssumptionPhiDpL r ℓ p L) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (i : ℕ)
    (hι : ∀ j, 1 ≤ j → j ≤ q → 0 ≤ iota j p ℓ i) (hε₀ : 0 < ε₀) (hε₁ : 0 ≤ ε₁)
    (hε₂ : 2 ≤ q → 0 ≤ ε₂) (hε₃ : 3 ≤ q → 0 ≤ ε₃) {δ : ℝ} (hδ : 0 < δ)
    (hδ₀ : δ ≤ (1 - β ^ (1 / 2 ^ i : ℝ)) * ε₀ ^ (1 / 2 ^ i : ℝ))
    (hδ₁ : δ ≤ kappa₁ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i *
      ε₁ ^ (((p : ℝ) + 1) / p) / max 1 (‖r (x 0)‖ ^ iota 1 p ℓ i))
    (hδ₂ : 2 ≤ q → δ ≤ kappa₂ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1))) /
      2 ^ i * ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) / max 1 (‖r (x 0)‖ ^ iota 2 p ℓ i))
    (hδ₃ : 3 ≤ q → δ ≤ kappa₃ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 2))) /
      2 ^ i * ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)) / max 1 (‖r (x 0)‖ ^ iota 3 p ℓ i)) :
    ∃ kε, IsFirstHit (fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          (‖r (x 0)‖ ^ (1 / 2 ^ i : ℝ) / δ) +
        ((|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams L / P.σ₀)) / Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k) kε : ℝ) ≤
        ‖r (x 0)‖ ^ (1 / 2 ^ i : ℝ) / δ + 2 := by
  set test := fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k) with htest
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hL := hΦ.nonneg
  have hα : (0 : ℝ) < 1 / 2 ^ i := by positivity
  have hdec : ∀ k, (∀ j ≤ k + 1, ¬ IsARRun.Stop test (fun _ => False) j) →
      P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k →
      δ ≤ ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ) - ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ) := by
    intro k hk hs
    have hk' : ∀ j ≤ k + 1, ¬ test j := fun j hj h' => hk j hj (Or.inl h')
    have hkk : ∀ j ≤ k, ¬ test j := fun j hj => hk' j (hj.trans k.le_succ)
    have hba := h.norm_succ_le hℓpos hkk
    have haR := h.norm_le_norm_zero hℓpos k fun j hj => hkk j hj.le
    -- the test fails at `x_{k+1}`
    have hnot := hk' (k + 1) le_rfl
    have hb0 : ε₀ < ‖r (x (k + 1))‖ := lt_of_not_ge fun hle => hnot (Or.inl hle)
    have hbpos : 0 < ‖r (x (k + 1))‖ := hε₀.trans hb0
    obtain ⟨L4a, L4b⟩ := lemma_5_1_4 hℓ h hΦ hp hqp hkk hs hβ0 hβ1 i
    rcases le_or_gt ‖r (x (k + 1))‖ (β * ‖r (x k)‖) with hβab | hβab
    · obtain ⟨c1, c2⟩ := L4b hβab
      have hκ0 : 0 ≤ 1 - β ^ (1 / 2 ^ i : ℝ) := by
        have := Real.rpow_le_one hβ0.le hβ1.le hα.le; linarith
      have : ε₀ ^ (1 / 2 ^ i : ℝ) ≤ ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ) :=
        Real.rpow_le_rpow hε₀.le hb0.le hα.le
      calc δ ≤ (1 - β ^ (1 / 2 ^ i : ℝ)) * ε₀ ^ (1 / 2 ^ i : ℝ) := hδ₀
        _ ≤ (1 - β ^ (1 / 2 ^ i : ℝ)) * ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ) := by gcongr
        _ ≤ _ := c2.trans c1
    obtain ⟨A1, A2, A3⟩ := L4a hβab
    have ha : 0 < ‖r (x k)‖ := hbpos.trans_le hba
    -- which part of the test fails at `x_{k+1}`
    have hcase : ε₁ < psiOne r ℓ (x (k + 1)) ∨ (2 ≤ q ∧ psiTwo r ℓ (x (k + 1)) < -ε₂) ∨
        (3 ≤ q ∧ ∃ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1),
          ε₃ < psiThree r ℓ (x (k + 1)) d ∨ ε₂ < psiTwoDir r ℓ (x (k + 1)) d) := by
      by_contra hc
      simp only [not_or, not_and, not_lt, not_exists] at hc
      obtain ⟨c1, c2, c3⟩ := hc
      apply hnot
      simp only [htest, ARpLEStop]
      interval_cases q
      · exact Or.inr (Or.inl ⟨rfl, c1⟩)
      · rcases le_or_gt (psiTwo r ℓ (x (k + 1))) ε₂ with h2 | h2
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, c1, c2 le_rfl⟩)))
        · exact Or.inr (Or.inr (Or.inl ⟨le_rfl, c1, h2⟩))
      · rcases le_or_gt (psiTwo r ℓ (x (k + 1))) ε₂ with h2 | h2
        · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, c1, c2 (by norm_num), fun d hd => ?_⟩)))
          exact c3 (le_refl 3) d hd
        · exact Or.inr (Or.inr (Or.inl ⟨by norm_num, c1, h2⟩))
    have hνpos : ∀ j : ℕ, j < p → (0 : ℝ) < ((p : ℝ) + 1) / ((p : ℝ) - j) := fun j hj => by
      have : (j : ℝ) < p := by exact_mod_cast hj
      exact div_pos (by positivity) (by linarith)
    rcases hcase with h1 | ⟨hq, h2⟩ | ⟨hq, d, hd, h3 | h3⟩
    · have := hνpos 0 (by omega)
      simp only [Nat.cast_zero, sub_zero] at this
      refine hδ₁.trans ((div_max_le_div ?_ hε₁ h1.le this.le (hι 1 le_rfl hq1) ha haR).trans A1)
      have := kappa₁_nonneg (P := P) (p := p) hL; positivity
    · have := hνpos 1 (by omega)
      simp only [Nat.cast_one] at this
      refine (hδ₂ hq).trans ((div_max_le_div ?_ (hε₂ hq) (le_max_of_le_right (by linarith))
        this.le (hι 2 (by norm_num) hq) ha haR).trans (A2 hq))
      have := kappa₂_nonneg (P := P) (p := p) hL; positivity
    · have := hνpos 2 (by omega)
      simp only [Nat.cast_ofNat] at this
      refine (hδ₃ hq).trans ((div_max_le_div ?_ (hε₃ hq) h3.le this.le (hι 3 (by norm_num) hq) ha
        haR).trans (A3 hq d hd))
      have := kappa₃_nonneg (P := P) (p := p) hL; positivity
    · have hq2 : 2 ≤ q := by omega
      have := hνpos 1 (by omega)
      simp only [Nat.cast_one] at this
      have hdec := decrease_psiTwoDir hℓpos h hΦ hp hqp hkk hs hq2 hd
      have A4 := rpow_inv_two_pow_sub_ge_of_decrease hℓ this (iota_two_eq (hq2.trans hqp) _ i)
        hβ0 (kappa₂_nonneg hL) psiTwoDir_nonneg hbpos.le hba hβab hdec
      refine (hδ₂ hq2).trans ((div_max_le_div ?_ (hε₂ hq2) h3.le this.le (hι 2 (by norm_num) hq2)
        ha haR).trans A4)
      have := kappa₂_nonneg (P := P) (p := p) hL; positivity
  obtain ⟨kε, hfirst, hF, hD⟩ := h.isARpRun.toIsARRun.exists_isFirstHit_of_decrease
    (σmax := arSigmaMax P.toARParams L)
    (fun k hk => (h.isARpRun.sigma_le hΦ.contDiff hΦ.lipschitz (k := k)
      fun j hj h' => hk j hj (Or.inl h')).2)
    (V := fun k => ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ)) (Vlow := 0) hδ
    (fun k hk => Real.rpow_le_rpow (norm_nonneg _)
      (h.norm_succ_le hℓpos fun j hj h' => hk j hj (Or.inl h')) hα.le)
    (fun k _ => by positivity) hdec
  refine ⟨kε, IsARRun.isFirstHit_stop_iff.1 hfirst, ?_, ?_⟩
  · simpa using hF
  · simpa using hD

end Decrease

/-! ### The choice of $\ell$ and $i$ -/

/-- Odd factorizations are unique: if $o$ and $o'$ are odd and $o \, 2^i = o' \, 2^j$, then $o = o'$
and $i = j$. -/
theorem eq_of_odd_mul_two_pow_eq {o o' i j : ℕ} (ho : Odd o) (ho' : Odd o')
    (h : o * 2 ^ i = o' * 2 ^ j) : o = o' ∧ i = j := by
  wlog hij : i ≤ j generalizing o o' i j with H
  · obtain ⟨h1, h2⟩ := H ho' ho h.symm (le_of_not_ge hij)
    exact ⟨h1.symm, h2.symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have h'' : o * 2 ^ i = (o' * 2 ^ d) * 2 ^ i := by rw [h, pow_add]; ring
  have h' : o = o' * 2 ^ d := Nat.eq_of_mul_eq_mul_right (by positivity) h''
  cases d with
  | zero => simpa using h'
  | succ d =>
    exfalso
    have : Even o := h' ▸ Nat.even_mul.2 (Or.inr (Nat.even_pow.2 ⟨even_two, by omega⟩))
    exact (Nat.not_even_iff_odd.2 ho) this

/-- **Lemma 5.1.5** of [cartis2022evaluation] (odd factorization). Every natural number $p \neq 0$
can be written uniquely as $p = o \, 2^i$ with $o$ odd and $i \in \mathbb{N}$.

**Reading.** The book writes $p \in \mathbb{N}$. In Lean $\mathbb{N}$ contains $0$, which has no
such factorization, so $p = 0$ is excluded. -/
theorem lemma_5_1_5 {p : ℕ} (hp : p ≠ 0) : ∃! oi : ℕ × ℕ, Odd oi.1 ∧ p = oi.1 * 2 ^ oi.2 := by
  obtain ⟨i, o, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hp
  refine ⟨(o, i), ⟨ho, mul_comm _ _⟩, ?_⟩
  rintro ⟨o', i'⟩ ⟨ho', h⟩
  simp only at ho' h
  obtain ⟨h1, h2⟩ := eq_of_odd_mul_two_pow_eq ho' ho (by rw [← h, mul_comm])
  rw [h1, h2]

/-- The exponent satisfies $\iota_1 = (2^i - 1)/2^i - (\ell - 1)/p$. -/
theorem iota_one_eq' {p : ℕ} (ℓ : ℝ) (i : ℕ) :
    iota 1 p ℓ i = ((2 : ℝ) ^ i - 1) / 2 ^ i - (ℓ - 1) / p := by
  rw [iota]; push_cast; rw [sub_add_cancel, one_mul]

/-- The exponent satisfies $\iota_2 = (2^i - 1)/2^i - 2(\ell - 1)/(p - 1)$. -/
theorem iota_two_eq' {p : ℕ} (ℓ : ℝ) (i : ℕ) :
    iota 2 p ℓ i = ((2 : ℝ) ^ i - 1) / 2 ^ i - 2 * (ℓ - 1) / ((p : ℝ) - 1) := by
  rw [iota]; push_cast; rw [show (p : ℝ) - 2 + 1 = p - 1 by ring]

/-- The exponent satisfies $\iota_3 = (2^i - 1)/2^i - 3(\ell - 1)/(p - 2)$. -/
theorem iota_three_eq' {p : ℕ} (ℓ : ℝ) (i : ℕ) :
    iota 3 p ℓ i = ((2 : ℝ) ^ i - 1) / 2 ^ i - 3 * (ℓ - 1) / ((p : ℝ) - 2) := by
  rw [iota]; push_cast; rw [show (p : ℝ) - 3 + 1 = p - 2 by ring]

/-- For $b > 0$, $(2^i - 1)/2^i - a/b > 0$ if and only if $a \, 2^i < (2^i - 1) \, b$. -/
private theorem iota_pos_iff {i : ℕ} {a b : ℝ} (hb : 0 < b) :
    0 < ((2 : ℝ) ^ i - 1) / 2 ^ i - a / b ↔ a * 2 ^ i < (2 ^ i - 1) * b := by
  rw [sub_pos, div_lt_div_iff₀ hb (by positivity)]

/-- The identity $3 \sum_{k < j} 4^k + 1 = 4^j$. -/
private theorem three_mul_sum_four_pow (j : ℕ) : 3 * ∑ k ∈ Finset.range j, 4 ^ k + 1 = 4 ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- **Lemma 5.1.6** of [cartis2022evaluation] (good exponents). Let $p \ge 1$, and write $\iota_j$
for $\iota_j(p, \ell, i)$ with natural numbers $\ell$ and $i$. Then:

* (5.1.38) if $\ell = p$ and $p < 2^i$, then $\iota_1 > 0$;
* (5.1.39) if $p$ is even, $p = o \, 2^i$ with $o$ odd, and $\ell = 1 + o(2^i - 1)$, then
  $\iota_1 = 0$ and $\ell > 1$;
* (5.1.40) if $p$ is even, $\ell = p/2$ and $p - 1 < 2^i$, then $\iota_1 > 0$ and $\iota_2 > 0$;
* (5.1.41) if $4$ divides $p - 1$, $p - 1 = o_2 \, 2^{i+1}$ with $o_2$ odd, and
  $\ell = 1 + o_2(2^i - 1)$, then $\iota_2 = 0$, $\iota_1 > 0$ and $\ell > 1$;
* (5.1.42) if $\ell = p/3$ and $p - 2 < 2^i$, then $\iota_1 > 0$, $\iota_2 > 0$ and
  $\iota_3 > 0$;
* (5.1.43) if $p - 2 = o_3 \, 2^i$ with $o_3$ odd, $i \ge 2$ is even, and
  $\ell = 1 + o_3 \sum_{k < i/2} 4^k$, then $\iota_3 = 0$, $\iota_1 > 0$, $\iota_2 > 0$,
  $\ell > 1$ and $\ell$ is even.

The conditions $\ell = p/2$ and $\ell = p/3$ are stated as $2\ell = p$ and $3\ell = p$. -/
theorem lemma_5_1_6 {p : ℕ} (hp : 1 ≤ p) :
    (∀ ℓ i : ℕ, ℓ = p → p < 2 ^ i → 0 < iota 1 p ℓ i) ∧
    (∀ ℓ o i : ℕ, Even p → Odd o → p = o * 2 ^ i → ℓ = 1 + o * (2 ^ i - 1) →
      iota 1 p ℓ i = 0 ∧ 1 < ℓ) ∧
    (∀ ℓ i : ℕ, Even p → 2 * ℓ = p → p - 1 < 2 ^ i → 0 < iota 1 p ℓ i ∧ 0 < iota 2 p ℓ i) ∧
    (∀ ℓ o₂ i : ℕ, 4 ∣ p - 1 → Odd o₂ → p - 1 = o₂ * 2 ^ (i + 1) → ℓ = 1 + o₂ * (2 ^ i - 1) →
      iota 2 p ℓ i = 0 ∧ 0 < iota 1 p ℓ i ∧ 1 < ℓ) ∧
    (∀ ℓ i : ℕ, 3 * ℓ = p → p - 2 < 2 ^ i →
      0 < iota 1 p ℓ i ∧ 0 < iota 2 p ℓ i ∧ 0 < iota 3 p ℓ i) ∧
    (∀ ℓ o₃ i : ℕ, Odd o₃ → p - 2 = o₃ * 2 ^ i → 2 ≤ i → Even i →
      ℓ = 1 + o₃ * ∑ k ∈ Finset.range (i / 2), 4 ^ k →
      iota 3 p ℓ i = 0 ∧ 0 < iota 1 p ℓ i ∧ 0 < iota 2 p ℓ i ∧ 1 < ℓ ∧ Even ℓ) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h2i : ∀ i : ℕ, (0 : ℝ) < 2 ^ i := fun i => by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (5.1.38)
    intro ℓ i hℓp hi
    rw [hℓp]
    have hi' : (p : ℝ) < 2 ^ i := by exact_mod_cast hi
    rw [iota_one_eq', iota_pos_iff (by linarith)]
    nlinarith
  · -- (5.1.39)
    rintro ℓ o i hpe ho rfl rfl
    have hi : i ≠ 0 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 (by simpa using ho)) hpe
    have h2 : 2 ≤ 2 ^ i := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hi)
    have ho1 : 1 ≤ o := ho.pos
    have hm := Nat.mul_le_mul ho1 (show 1 ≤ 2 ^ i - 1 by omega)
    refine ⟨?_, by omega⟩
    rw [iota_one_eq']
    have ho0 : (o : ℝ) ≠ 0 := by positivity
    push_cast [Nat.cast_sub (Nat.one_le_two_pow)]
    field_simp
    ring
  · -- (5.1.40)
    rintro ℓ i hpe rfl hi
    have hℓ : 1 ≤ ℓ := by omega
    have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have hi' : (2 * (ℓ : ℝ)) - 1 < 2 ^ i := by
      have : ((2 * ℓ - 1 : ℕ) : ℝ) < 2 ^ i := by exact_mod_cast hi
      push_cast [Nat.cast_sub (show 1 ≤ 2 * ℓ by omega)] at this
      exact this
    have h2 : 0 < iota 2 (2 * ℓ) ℓ i := by
      rw [iota_two_eq', iota_pos_iff (by push_cast; linarith)]
      push_cast
      nlinarith
    refine ⟨?_, h2⟩
    rcases (Nat.lt_or_ge 1 (2 * ℓ)) with hp2 | hp2
    · rw [iota_one_eq_iota_two_add (by omega)]
      have : 0 ≤ ((ℓ : ℝ) - 1) * ((2 * ℓ : ℕ) + 1) / ((2 * ℓ : ℕ) * ((2 * ℓ : ℕ) - 1)) := by
        push_cast
        apply div_nonneg (mul_nonneg (by linarith) (by positivity))
        nlinarith
      linarith
    · omega
  · -- (5.1.41)
    rintro ℓ o₂ i h4 ho hp1 rfl
    have hi : i ≠ 0 := by
      rintro rfl
      rw [hp1] at h4
      obtain ⟨c, hc⟩ := h4
      have : Even o₂ := ⟨c, by omega⟩
      exact (Nat.not_even_iff_odd.2 ho) this
    have h2 : 2 ≤ 2 ^ i := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hi)
    have ho1 : 1 ≤ o₂ := ho.pos
    have hm := Nat.mul_le_mul ho1 (show 1 ≤ 2 ^ i - 1 by omega)
    have hℓ1 : 1 < 1 + o₂ * (2 ^ i - 1) := by omega
    have hpR' : (p : ℝ) - 1 = o₂ * 2 ^ (i + 1) := by
      have : ((p - 1 : ℕ) : ℝ) = ((o₂ * 2 ^ (i + 1) : ℕ) : ℝ) := by rw [hp1]
      push_cast [Nat.cast_sub hp] at this
      exact this
    have hι2 : iota 2 p ((1 + o₂ * (2 ^ i - 1) : ℕ) : ℝ) i = 0 := by
      rw [iota_two_eq', hpR']
      have ho0 : (o₂ : ℝ) ≠ 0 := by positivity
      push_cast [Nat.cast_sub (Nat.one_le_two_pow)]
      field_simp
      ring
    refine ⟨hι2, ?_, hℓ1⟩
    have hp5 : 2 ≤ p := by
      have : 4 ≤ o₂ * 2 ^ (i + 1) := by
        calc 4 = 1 * 2 ^ 2 := rfl
          _ ≤ o₂ * 2 ^ (i + 1) := Nat.mul_le_mul ho1 (Nat.pow_le_pow_right (by norm_num)
            (by omega))
      omega
    rw [iota_one_eq_iota_two_add hp5, hι2, zero_add]
    have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp5
    have hℓR : (1 : ℝ) < ((1 + o₂ * (2 ^ i - 1) : ℕ) : ℝ) := by exact_mod_cast hℓ1
    apply div_pos (mul_pos (by linarith) (by positivity))
    nlinarith
  · -- (5.1.42)
    rintro ℓ i rfl hi
    have hℓ : 1 ≤ ℓ := by omega
    have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have hi' : (3 * (ℓ : ℝ)) - 2 < 2 ^ i := by
      have : ((3 * ℓ - 2 : ℕ) : ℝ) < 2 ^ i := by exact_mod_cast hi
      push_cast [Nat.cast_sub (show 2 ≤ 3 * ℓ by omega)] at this
      exact this
    have h3 : 0 < iota 3 (3 * ℓ) ℓ i := by
      rw [iota_three_eq', iota_pos_iff (by push_cast; linarith)]
      push_cast
      nlinarith
    have hpp : 3 ≤ 3 * ℓ := by omega
    have hpR3 : (3 : ℝ) ≤ ((3 * ℓ : ℕ) : ℝ) := by exact_mod_cast hpp
    refine ⟨?_, ?_, h3⟩
    · rw [iota_one_eq_iota_three_add hpp]
      have : 0 ≤ 2 * ((ℓ : ℝ) - 1) * ((3 * ℓ : ℕ) + 1) / ((3 * ℓ : ℕ) * ((3 * ℓ : ℕ) - 2)) := by
        apply div_nonneg (mul_nonneg (by linarith) (by positivity))
        nlinarith
      linarith
    · rw [iota_two_eq_iota_three_add hpp]
      have : 0 ≤ ((ℓ : ℝ) - 1) * ((3 * ℓ : ℕ) + 1) / (((3 * ℓ : ℕ) - 1) * ((3 * ℓ : ℕ) - 2)) := by
        apply div_nonneg (mul_nonneg (by linarith) (by positivity))
        nlinarith
      linarith
  · -- (5.1.43)
    rintro ℓ o₃ i ho hp2 hi he rfl
    obtain ⟨j, rfl⟩ := he
    have hj : (j + j) / 2 = j := by omega
    rw [hj]
    have hj1 : 1 ≤ j := by omega
    set S := ∑ k ∈ Finset.range j, 4 ^ k with hS
    have h3S := three_mul_sum_four_pow j
    rw [← hS] at h3S
    have h4 : (4 : ℕ) ^ j = 2 ^ (j + j) := by rw [← two_mul, pow_mul]; norm_num
    have hS1 : 1 ≤ S := by
      have : 4 ≤ 4 ^ j := by
        calc 4 = 4 ^ 1 := rfl
          _ ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
      omega
    have ho1 : 1 ≤ o₃ := ho.pos
    have hℓ1 : 1 < 1 + o₃ * S := by nlinarith
    have hSodd : Odd S := by
      have : Odd (3 * S) := by
        have he4 : Even (4 ^ j) := Nat.even_pow.2 ⟨by decide, by omega⟩
        obtain ⟨c, hc⟩ := he4
        exact ⟨c - 1, by omega⟩
      exact (Nat.odd_mul.1 this).2
    have hpR' : (p : ℝ) - 2 = o₃ * 2 ^ (j + j) := by
      have hp6 : 2 ≤ p := by
        have : 1 ≤ o₃ * 2 ^ (j + j) := Nat.one_le_iff_ne_zero.2 (by positivity)
        omega
      have : ((p - 2 : ℕ) : ℝ) = ((o₃ * 2 ^ (j + j) : ℕ) : ℝ) := by rw [hp2]
      push_cast [Nat.cast_sub hp6] at this
      exact this
    have h3SR : (3 : ℝ) * S = 2 ^ (j + j) - 1 := by
      have : ((3 * S + 1 : ℕ) : ℝ) = ((2 ^ (j + j) : ℕ) : ℝ) := by rw [h3S, h4]
      push_cast at this
      linarith
    have hι3 : iota 3 p ((1 + o₃ * S : ℕ) : ℝ) (j + j) = 0 := by
      rw [iota_three_eq', hpR']
      have ho0 : (o₃ : ℝ) ≠ 0 := by positivity
      push_cast
      rw [show (1 : ℝ) + o₃ * S - 1 = o₃ * S by ring, show 3 * (o₃ * (S : ℝ)) = o₃ * (3 * S) by
        ring, h3SR]
      field_simp
      ring
    have hp3 : 3 ≤ p := by
      have : 4 ≤ o₃ * 2 ^ (j + j) := by
        calc 4 = 1 * 2 ^ 2 := rfl
          _ ≤ o₃ * 2 ^ (j + j) := Nat.mul_le_mul ho1 (Nat.pow_le_pow_right (by norm_num)
            (by omega))
      omega
    have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hℓR : (1 : ℝ) < ((1 + o₃ * S : ℕ) : ℝ) := by exact_mod_cast hℓ1
    refine ⟨hι3, ?_, ?_, hℓ1, ?_⟩
    · rw [iota_one_eq_iota_three_add hp3, hι3, zero_add]
      apply div_pos (mul_pos (by linarith) (by positivity))
      nlinarith
    · rw [iota_two_eq_iota_three_add hp3, hι3, zero_add]
      apply div_pos (mul_pos (by linarith) (by positivity))
      nlinarith
    · obtain ⟨c, hc⟩ := Nat.odd_mul.2 ⟨ho, hSodd⟩
      exact ⟨c + 1, by omega⟩

section Theorem517

variable {r : ℝⁿ → ℝᵐ} {p : ℕ} {P : ARpParams} {ε₀ ε₁ ε₂ ε₃ L : ℝ} {x s : ℕ → ℝⁿ}
  {σ : ℕ → ℝ}

/-- For $0 \le e \le E$, $k > 0$, $1/k \le K$ and $0 < m \le M$, $e/(KM) \le kE/m$. -/
private theorem div_mul_le_mul_div {e E K k M m : ℝ} (he : 0 ≤ e) (heE : e ≤ E) (hk : 0 < k)
    (hK : 1 / k ≤ K) (hm : 0 < m) (hmM : m ≤ M) : e / (K * M) ≤ k * E / m := by
  have hK0 : 0 < K := (one_div_pos.2 hk).trans_le hK
  have hM0 : 0 < M := hm.trans_le hmM
  have h1 : 1 / K ≤ k := by rw [div_le_iff₀ hK0]; rw [div_le_iff₀ hk] at hK; linarith
  calc e / (K * M) = e * (1 / K) * (1 / M) := by field_simp
    _ ≤ E * k * (1 / m) :=
        mul_le_mul (mul_le_mul heE h1 (by positivity) (he.trans heE))
          (one_div_le_one_div_of_le hm hmM) (by positivity) (by have := he.trans heE; positivity)
    _ = k * E / m := by ring

/-- **Theorem 5.1.7** of [cartis2022evaluation]. Let $\ell > 1$ and $i \ge 0$ be integers that
satisfy (5.1.42) or (5.1.43) for $p$: either $3\ell = p$ and $p - 2 < 2^i$, or
$p - 2 = o_3 \, 2^i$ with $o_3$ odd, $i \ge 2$ even and $\ell = 1 + o_3\sum_{k < i/2} 4^k$. Let
$\Phi_\ell$ satisfy assumption $\Phi_\ell$.DpL with constant $L$, let $\sigma_{\min} > 0$ and
$\beta \in (0, 1)$, and let $\epsilon_0, \epsilon_1, \epsilon_2, \epsilon_3 > 0$. Then every run
of ARpLE with $q = 3$ terminates at an index $k_\epsilon$, the first index at which the test
holds. That is, $\|r(x_\epsilon)\| \le \epsilon_0$, or
$\psi_{\ell,1}(x_\epsilon) \le \epsilon_1$ together with
$\psi_{\ell,2}(x_\epsilon) > \epsilon_2$, or $\psi_{\ell,1}(x_\epsilon) \le \epsilon_1$ together
with $\psi_{\ell,2}(x_\epsilon) \ge -\epsilon_2$ and
$\psi_{\ell,3}(x_\epsilon, d) \le \epsilon_3$, $\psi_{\ell,2}(x_\epsilon, d) \le \epsilon_2$ for
all $d \in \mathcal{M}_\epsilon$, so that $\mathcal{M}_\epsilon \subseteq \mathcal{Z}_\epsilon$.
Let
$$\kappa^S = \max\left(\frac{1}{\kappa_{r0}}, \frac{1}{\kappa_{r1}}, \frac{1}{\kappa_{r2}},
  \frac{1}{\kappa_{r3}}\right)$$
with the constants of Lemma 5.1.4, $\kappa^A = \kappa^S(1 + |\log\gamma_1|/\log\gamma_2)$,
$\kappa^C = (|\log\gamma_1| + \log(\sigma_{\max}/\sigma_0))/\log\gamma_2 + 2$
((5.1.60)–(5.1.61)), and
$$R = \frac{\max\left[\|r_0\|^{1/2^i}, \|r_0\|^{1 - (\ell-1)/p}, \|r_0\|^{1 - 2(\ell-1)/(p-1)},
  \|r_0\|^{1 - 3(\ell-1)/(p-2)}\right]}{\min\left[\epsilon_0^{1/2^i}, \epsilon_1^{(p+1)/p},
  \epsilon_2^{(p+1)/(p-1)}, \epsilon_3^{(p+1)/(p-2)}\right]},$$
where $r_0 = r(x_0)$. Then the number of evaluations of $r$ is at most $\kappa^A R + \kappa^C$
(5.1.44), and the number of evaluations of its derivatives is at most $\kappa^S R + 2$ (5.1.45).

**Typo.** The book prints the multiplier $\kappa^C$ in (5.1.44); it is $\kappa^A$. In (5.1.51)
the three conditions are alternatives ("or"), where the book prints "and". The set
$\mathcal{M}_{j+1}$ there is that of (4.1.14), where the book prints (4.1.9).

**Reading.** The run may also stop by the strict-local-minimizer test (5.1.11), which is one of
the branches of `CartisGouldToint.Chapter05.ARpLEStop`.

**Generalization.** The book's hypothesis $(\epsilon_0, \dots, \epsilon_3) \in (0, 1]^4$ is used
only as $\epsilon_j > 0$. The general form is
`CartisGouldToint.Chapter05.theorem_5_1_7_of_iota_nonneg`, from which this theorem follows with
Lemma 5.1.6. -/
theorem theorem_5_1_7 {ℓ i : ℕ} (hℓ : 1 < ℓ)
    (hpi : (3 * ℓ = p ∧ p - 2 < 2 ^ i) ∨
      (∃ o₃ : ℕ, Odd o₃ ∧ p - 2 = o₃ * 2 ^ i ∧ 2 ≤ i ∧ Even i ∧
        ℓ = 1 + o₃ * ∑ k ∈ Finset.range (i / 2), 4 ^ k))
    (h : algorithm_5_1_1 r ℓ p P 3 ε₀ ε₁ ε₂ ε₃ x s σ) (hΦ : AssumptionPhiDpL r ℓ p L)
    (hσ : 0 < P.σmin) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hε₃ : 0 < ε₃) :
    ∃ kε, IsFirstHit (fun k => ARpLEStop r ℓ 3 ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤
        max (max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (1 / (kappa₁ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i)))
          (max (1 / (kappa₂ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1))) / 2 ^ i))
            (1 / (kappa₃ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 2))) / 2 ^ i))) *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          max (max (‖r (x 0)‖ ^ (1 / 2 ^ i : ℝ)) (‖r (x 0)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)))
            (max (‖r (x 0)‖ ^ (1 - 2 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 1)))
              (‖r (x 0)‖ ^ (1 - 3 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 2)))) /
          min (min (ε₀ ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)))
            (min (ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))) (ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)))) +
        ((|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams L / P.σ₀)) / Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k) kε : ℝ) ≤
        max (max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (1 / (kappa₁ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i)))
          (max (1 / (kappa₂ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1))) / 2 ^ i))
            (1 / (kappa₃ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 2))) / 2 ^ i))) *
          max (max (‖r (x 0)‖ ^ (1 / 2 ^ i : ℝ)) (‖r (x 0)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)))
            (max (‖r (x 0)‖ ^ (1 - 2 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 1)))
              (‖r (x 0)‖ ^ (1 - 3 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 2)))) /
          min (min (ε₀ ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)))
            (min (ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))) (ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)))) +
        2 := by
  -- `p ≥ 3` and the exponents are nonnegative (Lemma 5.1.6)
  have hp3 : 3 ≤ p := by
    rcases hpi with ⟨h3, -⟩ | ⟨o₃, ho, hp2, hi, -, -⟩
    · omega
    · have : 4 ≤ o₃ * 2 ^ i := by
        calc 4 = 1 * 2 ^ 2 := rfl
          _ ≤ o₃ * 2 ^ i := Nat.mul_le_mul ho.pos (Nat.pow_le_pow_right (by norm_num) hi)
      omega
  have hp1 : 1 ≤ p := by omega
  obtain ⟨-, -, -, -, h42, h43⟩ := lemma_5_1_6 hp1
  have hι : ∀ j, 1 ≤ j → j ≤ 3 → 0 ≤ iota j p ℓ i := by
    have hpos : 0 ≤ iota 1 p ℓ i ∧ 0 ≤ iota 2 p ℓ i ∧ 0 ≤ iota 3 p ℓ i := by
      rcases hpi with ⟨h3, h2⟩ | ⟨o₃, ho, hp2, hi, he, hℓe⟩
      · obtain ⟨h1, h2, h3⟩ := h42 ℓ i h3 h2
        exact ⟨h1.le, h2.le, h3.le⟩
      · obtain ⟨h1, h2, h3, -⟩ := h43 ℓ o₃ i ho hp2 hi he hℓe
        exact ⟨h2.le, h3.le, h1.ge⟩
    intro j hj1 hj3
    interval_cases j
    · exact hpos.1
    · exact hpos.2.1
    · exact hpos.2.2
  have hL := hΦ.nonneg
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.le
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  set α : ℝ := 1 / 2 ^ i with hαdef
  have hα : 0 < α := by positivity
  set R := ‖r (x 0)‖ with hRdef
  have hR0 : 0 ≤ R := norm_nonneg _
  set κr0 := 1 - β ^ α with hκr0def
  set κr1 := kappa₁ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i
  set κr2 := kappa₂ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1))) / 2 ^ i
  set κr3 := kappa₃ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 2))) / 2 ^ i
  have hκr0 : 0 < κr0 := by have := Real.rpow_lt_one hβ0.le hβ1 hα; linarith
  have hκr1 : 0 < κr1 := by have := kappa₁_pos (P := P) (p := p) hL hσ; positivity
  have hκr2 : 0 < κr2 := by have := kappa₂_pos (P := P) (p := p) hL hσ; positivity
  have hκr3 : 0 < κr3 := by have := kappa₃_pos (P := P) (p := p) hL hσ; positivity
  set κS := max (max (1 / κr0) (1 / κr1)) (max (1 / κr2) (1 / κr3)) with hκS
  set εmin := min (min (ε₀ ^ α) (ε₁ ^ (((p : ℝ) + 1) / p)))
    (min (ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))) (ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2))))
    with hεmin_def
  have hεmin : 0 < εmin := by positivity
  set M1 := max (max 1 (R ^ iota 1 p ℓ i)) (max (R ^ iota 2 p ℓ i) (R ^ iota 3 p ℓ i)) with hM1
  have hM1one : 1 ≤ M1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hS0 : 1 / κr0 ≤ κS := le_trans (le_max_left _ _) (le_max_left _ _)
  have hS1 : 1 / κr1 ≤ κS := le_trans (le_max_right _ _) (le_max_left _ _)
  have hS2 : 1 / κr2 ≤ κS := le_trans (le_max_left _ _) (le_max_right _ _)
  have hS3 : 1 / κr3 ≤ κS := le_trans (le_max_right _ _) (le_max_right _ _)
  have hκSpos : 0 < κS := (one_div_pos.2 hκr0).trans_le hS0
  set δ := εmin / (κS * M1) with hδdef
  have hδ : 0 < δ := div_pos hεmin (mul_pos hκSpos (by linarith))
  obtain ⟨kε, hfirst, hF, hD⟩ := theorem_5_1_7_of_iota_nonneg (by omega) (by norm_num) le_rfl
    hp1 hp3 h hΦ hβ0 hβ1 i hι hε₀ hε₁.le (fun _ => hε₂.le) (fun _ => hε₃.le) hδ
    ((div_mul_le_mul_div hεmin.le (le_trans (min_le_left _ _) (min_le_left _ _)) hκr0 hS0
      one_pos hM1one).trans_eq (div_one _))
    (div_mul_le_mul_div hεmin.le (le_trans (min_le_left _ _) (min_le_right _ _)) hκr1 hS1
      (by positivity) (le_max_left _ _))
    (fun _ => div_mul_le_mul_div hεmin.le (le_trans (min_le_right _ _) (min_le_left _ _)) hκr2
      hS2 (by positivity) (max_le (hM1one) (le_trans (le_max_left _ _) (le_max_right _ _))))
    (fun _ => div_mul_le_mul_div hεmin.le (le_trans (min_le_right _ _) (min_le_right _ _)) hκr3
      hS3 (by positivity) (max_le (hM1one) (le_trans (le_max_right _ _) (le_max_right _ _))))
  -- `‖r_0‖^{1/2^i} max(1, ‖r_0‖^{ι_j}) ≤ max_j ‖r_0‖^{1/2^i + ι_j}`
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2' : (p : ℝ) - 2 ≠ 0 := by linarith
  have e1 : α + iota 1 p ℓ i = 1 - ((ℓ : ℝ) - 1) / p := by
    rw [iota_one_eq', hαdef]; field_simp; ring
  have e2 : α + iota 2 p ℓ i = 1 - 2 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 1) := by
    rw [iota_two_eq', hαdef]; field_simp; ring
  have e3 : α + iota 3 p ℓ i = 1 - 3 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 2) := by
    rw [iota_three_eq', hαdef]; field_simp; ring
  have hRM : R ^ α * M1 ≤ max (max (R ^ α) (R ^ (1 - ((ℓ : ℝ) - 1) / p)))
      (max (R ^ (1 - 2 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 1)))
        (R ^ (1 - 3 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 2)))) := by
    have hRα : 0 ≤ R ^ α := Real.rpow_nonneg hR0 _
    rw [hM1, mul_max_of_nonneg _ _ hRα, mul_max_of_nonneg _ _ hRα, mul_max_of_nonneg _ _ hRα,
      mul_one, ← e1, ← e2, ← e3]
    exact max_le_max (max_le_max le_rfl (Real.le_rpow_add hR0 _ _))
      (max_le_max (Real.le_rpow_add hR0 _ _) (Real.le_rpow_add hR0 _ _))
  set Rmax := max (max (R ^ α) (R ^ (1 - ((ℓ : ℝ) - 1) / p)))
    (max (R ^ (1 - 2 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 1)))
      (R ^ (1 - 3 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 2)))) with hRmax
  have hratio : R ^ α / δ ≤ κS * Rmax / εmin := by
    rw [hδdef, div_div_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hεmin.le
    calc R ^ α * (κS * M1) = κS * (R ^ α * M1) := by ring
      _ ≤ κS * Rmax := mul_le_mul_of_nonneg_left hRM hκSpos.le
  have hκA : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ := by
    have := P.log_γ₂_pos; positivity
  refine ⟨kε, hfirst, hF.trans ?_, hD.trans (by linarith)⟩
  have := mul_le_mul_of_nonneg_left hratio hκA
  calc (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (R ^ α / δ) +
        ((|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams L / P.σ₀)) / Real.log P.γ₂ + 2)
      ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (κS * Rmax / εmin) +
        ((|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams L / P.σ₀)) / Real.log P.γ₂ + 2) :=
        by linarith
    _ = _ := by ring

end Theorem517

/-! ### Termination guarantees and existence of runs -/

section Existence

variable {r : ℝⁿ → ℝᵐ} {ℓ : ℝ} {q : ℕ} {ε₀ ε₁ ε₂ ε₃ : ℝ}

/-- Let every element of a set $M$ of directions be a unit vector, and let
$\psi_{\ell,3}(x, d) \le \epsilon_3$ and $\psi_{\ell,2}(x, d) \le \epsilon_2$ for all $d \in M$.
Then $M \subseteq \mathcal{Z}_\epsilon$. At termination by the third-order branch of the test,
this gives $\mathcal{M}_\epsilon \subseteq \mathcal{Z}_\epsilon$, as in the remark after
Algorithm 5.1.1 and Theorem 5.1.7 of [cartis2022evaluation]. -/
theorem subset_zSet_of_forall {M : Set ℝⁿ} {x : ℝⁿ} (hM : ∀ d ∈ M, ‖d‖ = 1)
    (h : ∀ d ∈ M, psiThree r ℓ x d ≤ ε₃ ∧ psiTwoDir r ℓ x d ≤ ε₂) : M ⊆ zSet r ℓ ε₂ x :=
  fun d hd => ⟨hM d hd, (h d hd).2⟩

/-- For $q \le 2$ the termination test does not depend on the direction set: for all sets $M$, $M'$
and points $x$, the test holds with $M$ if and only if it holds with $M'$. -/
theorem arpLEStop_congr_of_le_two (hq : q ≤ 2) (M M' : Set ℝⁿ) (x : ℝⁿ) :
    ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ M x ↔ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ M' x := by
  have h3 : q ≠ 3 := by omega
  simp only [ARpLEStop, h3, false_and, or_false]

/-- Existence of ARpLE runs for $q \in \{1, 2\}$ (Algorithm 5.1.1 of [cartis2022evaluation]). Let
$p \ge 1$, $1 \le q \le 2$ and $q \le p$, let $\Phi_\ell$ be $p$ times continuously
differentiable, and let $\epsilon_0, \epsilon_1, \epsilon_2 \ge 0$. Then for every
$x_0 \in \mathbb{R}^n$ there is a run of ARpLE that starts at $x_0$.

When the test fails at $x_k$, then $r(x_k) \neq 0$, and either
$\psi_{\ell,1}(x_k) > \epsilon_1 \ge 0$ or, for $q = 2$,
$\psi_{\ell,2}(x_k) < -\epsilon_2 \le 0$. So $x_k$ is not a second-order critical point of
$\Phi_\ell$, and a global minimizer of the model is an admissible step. -/
theorem algorithm_5_1_1.exists_run (P : ARpParams) {p : ℕ} (hΦ : ContDiff ℝ p (Phi r ℓ))
    (hp : 1 ≤ p) (hq1 : 1 ≤ q) (hq : q ≤ 2) (hqp : q ≤ p) (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁)
    (hε₂ : 0 ≤ ε₂) (x₀ : ℝⁿ) :
    ∃ x s : ℕ → ℝⁿ, ∃ σ : ℕ → ℝ, x 0 = x₀ ∧ algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ := by
  have htest : ∀ y, ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ ∅ y →
      fderiv ℝ (Phi r ℓ) y ≠ 0 ∨
        (2 ≤ q ∧ minCurvature (iteratedFDeriv ℝ 2 (Phi r ℓ) y) < 0) := by
    intro y hy
    simp only [ARpLEStop, not_or, not_and, not_le, not_lt] at hy
    obtain ⟨h0, h1, h2, h3, -⟩ := hy
    have hy0 : r y ≠ 0 := norm_pos_iff.1 (hε₀.trans_lt h0)
    have hpos : 0 < ‖r y‖ ^ (ℓ - 1) := Real.rpow_pos_of_pos (hε₀.trans_lt h0) _
    rcases le_or_gt (psiOne r ℓ y) ε₁ with hψ | hψ
    · right
      interval_cases q
      · exact absurd hψ (not_le.2 (h1 rfl))
      · refine ⟨le_rfl, ?_⟩
        have hlt := h3 rfl hψ
        rw [psiTwo_eq, div_lt_iff₀ hpos] at hlt
        nlinarith
    · left
      intro h0'
      rw [psiOne_eq, h0', norm_zero, zero_div] at hψ
      linarith
  obtain ⟨x, s, σ, hx0, hrun⟩ := exists_isARpRun (f := Phi r ℓ) (q := q) P hΦ hp hq
    (fun h2 => h2.trans hqp) htest x₀
  refine ⟨x, s, σ, hx0, ?_⟩
  have heq : (fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k)) =
      fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ ∅ (x k) :=
    funext fun k => propext (arpLEStop_congr_of_le_two hq _ _ _)
  rw [algorithm_5_1_1, heq]
  exact hrun

/-- The direction set $\mathcal{M}_k$ read from the previous iteration, as
`Optimization.prevIterate` provides it: $\mathcal{M}_0$ from $\nabla^2\Phi_\ell(x_0)$ and
$\epsilon_2$, and $\mathcal{M}_{k+1}$ from the model of iteration $k$. -/
private noncomputable def mdirOfPrev (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (p : ℕ) (P : ARpParams) (ε₂ : ℝ) :
    Option (ℝⁿ × ℝ × ℝⁿ) → ℝⁿ → Set ℝⁿ
  | none, y => smallCurvatureDirections (iteratedFDeriv ℝ 2 (Phi r ℓ) y) ε₂
  | some (x', σ', s'), _ => smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ (Phi r ℓ) x') p σ') s')
      (P.θ₂ * ‖s'‖ ^ (p - 1))

/-- Existence of ARpLE runs for any $q$, under an explicit hypothesis (Algorithm 5.1.1 of
[cartis2022evaluation]). Suppose that an admissible ARp step (4.1.10)–(4.1.13) exists at every
point $y$ and weight $\sigma$ with $\sigma \ge \sigma_{\min}$ and $\sigma > 0$ at which the test
fails for some direction set $M$. Then for every $x_0 \in \mathbb{R}^n$ there is a run of ARpLE
that starts at $x_0$.

For $q = 3$ the hypothesis can fail (see `Numlib.Optimization.ModelBased.ARpRun`). For $q \le 2$
it holds, and `CartisGouldToint.Chapter05.algorithm_5_1_1.exists_run` applies. -/
theorem algorithm_5_1_1.exists_run_of_step (P : ARpParams) {p : ℕ}
    (hstep : ∀ (M : Set ℝⁿ) (y : ℝⁿ) (σ : ℝ), P.σmin ≤ σ → 0 < σ →
      ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ M y → ∃ s, IsARpStep (Phi r ℓ) p P q y σ s)
    (x₀ : ℝⁿ) :
    ∃ x s : ℕ → ℝⁿ, ∃ σ : ℕ → ℝ, x 0 = x₀ ∧ algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun⟩ := exists_isARpRun_prev (f := Phi r ℓ) (p := p) (q := q) P
    (test := fun prev y _ => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdirOfPrev r ℓ p P ε₂ prev y) y)
    (fun prev y σ hσ hσ0 ht => hstep _ y σ hσ hσ0 ht) x₀
  refine ⟨x, s, σ, hx0, ?_⟩
  have heq : (fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k)) =
      fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃
        (mdirOfPrev r ℓ p P ε₂ (prevIterate x s σ k) (x k)) (x k) := by
    funext k
    cases k <;> rfl
  rw [algorithm_5_1_1, heq]
  exact hrun

end Existence

/-! ### Full rank -/

/-- **Equation (5.1.63)** of [cartis2022evaluation]. Let $r$ be differentiable at $x$ with
$r(x) \neq 0$, and let $\ell > 1$. Then
$$\psi_{\ell,1}(x) = \frac{\|J(x)^T r(x)\|}{\|r(x)\|},$$
where $J(x)^T$ is the adjoint of the Jacobian of $r$ at $x$. In particular, $\psi_{\ell,1}(x)$
does not depend on $\ell$. -/
theorem psiOne_eq_of_jacobian {r : ℝⁿ → ℝᵐ} {ℓ : ℝ} (hℓ : 1 < ℓ) {x : ℝⁿ}
    (hr : DifferentiableAt ℝ r x) (hx : r x ≠ 0) :
    psiOne r ℓ x = ‖(ContinuousLinearMap.adjoint (fderiv ℝ r x)) (r x)‖ / ‖r x‖ := by
  rw [psiOne_eq]
  exact norm_fderiv_residualPow_div hr hℓ hx

/-- **Equations (5.1.62)–(5.1.64)** of [cartis2022evaluation]. Let $r$ be differentiable at $x$ with
$r(x) \neq 0$, and let $\ell > 1$. Suppose that the adjoint of the Jacobian satisfies the
full-rank condition
$$\|J(x)^T v\| \ge s_0\|v\| \quad \text{for all } v \in \mathbb{R}^m,$$
that is, its smallest singular value is at least $s_0$. Then $\psi_{\ell,1}(x) \ge s_0$.

The adjoint $J(x)^T$ is `ContinuousLinearMap.adjoint (fderiv ℝ r x)`. -/
theorem psiOne_ge_of_jacobian {r : ℝⁿ → ℝᵐ} {ℓ : ℝ} (hℓ : 1 < ℓ) {x : ℝⁿ}
    (hr : DifferentiableAt ℝ r x) (hx : r x ≠ 0) {s₀ : ℝ}
    (hs : ∀ v, s₀ * ‖v‖ ≤ ‖(ContinuousLinearMap.adjoint (fderiv ℝ r x)) v‖) :
    s₀ ≤ psiOne r ℓ x := by
  rw [psiOne_eq_of_jacobian hℓ hr hx, le_div_iff₀ (norm_pos_iff.2 hx)]
  exact hs _

end CartisGouldToint.Chapter05
