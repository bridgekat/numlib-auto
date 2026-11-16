/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Analysis.Calculus.PartialDeriv

/-!
# The linear transport equation and hyperbolic systems

This module studies classical solutions of the scalar transport equation
$$\partial_t u + a \, \partial_x u + a_0 u = f, \qquad u(\cdot, 0) = u_0,$$
on the closed half plane $\mathbb{R} \times [0, \infty)$, of the constant-coefficient system
$\partial_t u + A \, \partial_x u = 0$ with $u(x, t) \in \mathbb{R}^p$, and of the wave equation
$\partial_{tt} u = \gamma^2 \partial_{xx} u$ on a strip. The material is §13.5–13.6 of
[quarteroni2000numerical], together with the inflow problem (13.64) of §13.10. For the homogeneous
scalar equation with constant speed $a$, every solution is the travelling wave $u_0(x - at)$, and
$|u| \le \sup |u_0|$.

A matrix $A \in \mathbb{R}^{p \times p}$ is hyperbolic when $A = T \Lambda T^{-1}$ with $T$
invertible and $\Lambda = \operatorname{diag}(\lambda_1, \dots, \lambda_p)$ real, and strictly
hyperbolic when moreover the $\lambda_k$ are distinct. The columns $\omega^k$ of $T$ are then right
eigenvectors of $A$. For a hyperbolic system the characteristic variables $w = T^{-1} u$ solve $p$
decoupled scalar transport equations, which gives the solution formula
$$u(x, t) = \sum_k w_k(x - \lambda_k t, 0) \, \omega^k,$$
and shows that the value at $(\bar{x}, \bar{t})$ depends on the datum only at the $p$ points
$\bar{x} - \lambda_k \bar{t}$. The wave equation becomes such a system for the pair
$(\partial_x u, \partial_t u)$, with a strictly hyperbolic matrix with eigenvalues $\pm \gamma$.

## Main definitions

* `Transport.HasPartialsOn`: a function of $(x, t)$ is differentiable within a region, with given
  partial derivatives.
* `Transport.IsSolution`: a classical solution of the scalar transport equation (13.28).
* `Transport.IsCharacteristic`: a characteristic curve $x' = a(x, t)$, (13.27).
* `Transport.IsSystemSolutionOn` and `Transport.IsSystemSolution`: a classical solution of the
  system (13.30).
* `Transport.IsHyperbolic` and `Transport.IsStrictlyHyperbolic`: $A = T \Lambda T^{-1}$ with real,
  or real and distinct, eigenvalues.
* `Transport.domainOfDependence`: the domain of dependence (13.31).
* `Transport.waveMatrix`: the matrix (13.35) of the wave equation as a first-order system.
* `Transport.IsWaveSolution`: a classical solution of the wave equation (13.33)–(13.34).
* `Transport.IsInflowSolution`: a classical solution of the inflow problem (13.64).

## Main results

* `Transport.IsSolution.hasDerivAt_comp_characteristic`: along a characteristic,
  $\frac{d}{dt} u(x(t), t) = f - a_0 u$.
* `Transport.IsSolution.comp_characteristic_const`: for constant speed and $a_0 = f = 0$, a solution
  is constant along the characteristics.
* `Transport.isSolution_comp_sub` and `Transport.IsSolution.eq_comp_sub`: the travelling wave
  $u_0(x - at)$ is a solution, and it is the only one.
* `Transport.IsSolution.abs_le_sup`: the maximum principle $|u(x, t)| \le \sup_s |u_0(s)|$.
* `Transport.mulVec_col_eq_smul`: the columns of $T$ are right eigenvectors of
  $A = T \Lambda T^{-1}$.
* `Transport.IsSystemSolution.characteristicVariables`: the characteristic variables solve decoupled
  scalar equations.
* `Transport.isSystemSolution_sum` and `Transport.IsSystemSolution.eq_sum`: the solution formula
  gives a solution, and it is the only one.
* `Transport.IsSystemSolution.eq_of_eqOn_domainOfDependence`: the solution at a point depends on the
  datum only on the domain of dependence.
* `Transport.waveMatrix_isStrictlyHyperbolic`: the wave matrix is strictly hyperbolic for
  $\gamma \neq 0$.
* `Transport.IsWaveSolution.isSystemSolution`: the wave equation as a first-order system.

## Proof outline

All results follow from the chain rule. A characteristic is an integral curve $x' = a(x, t)$ of the
speed field, and along it a differentiable solution satisfies the ordinary differential equation
$\frac{d}{dt} u(x(t), t) = f - a_0 u$. For the homogeneous equation with constant speed the
characteristics are the lines $x_0 + at$, the solution is constant along them, and this gives the
travelling wave, its uniqueness and the bound by $\sup |u_0|$.

## Implementation notes

* A function of the two variables is curried, $u : \mathbb{R} \to \mathbb{R} \to \mathbb{R}$ with
  arguments $x$ and $t$. Its differentiability is that of the uncurried function
  `fun q : ℝ × ℝ => u q.1 q.2` within the closed region, so the one-sided derivative at $t = 0$
  needs no separate case.
* `Transport.HasPartialsOn` names the two partial derivatives as functions instead of `fderivWithin`
  expressions. The derivative at $(x, t)$ is `Transport.partialsCLM (ux x t) (ut x t)`, the
  functional $(y, s) \mapsto u_x y + u_t s$.
* Only differentiability is assumed, never continuity of the derivatives. Every result holds at that
  strength, and a $C^1$ solution in the sense of §13.5 of [quarteroni2000numerical] is in particular
  a solution here.
* `Transport.IsWaveSolution` is the only definition with second derivatives. It asks for the partial
  derivatives of $u_x$ and of $u_t$, with one function $u_{xt}$ for the two mixed partial
  derivatives. For a $C^2$ function this is no restriction, by the symmetry of the second derivative
  (`ContDiffWithinAt.isSymmSndFDerivWithinAt`), and it is what the change of variables to the
  first-order system uses.
* The column $\omega^k$ of a matrix $T$ is written `Tᵀ k`.
-/

open Set Matrix

namespace Transport

/-! ### Partial derivatives of a function of two real variables -/

/-- The continuous linear functional $(y, s) \mapsto u_x y + u_t s$ on
$\mathbb{R} \times \mathbb{R}$, for numbers $u_x, u_t$. It is the Fréchet derivative of a
function of $(x, t)$ whose partial derivatives are $u_x$ and $u_t$. -/
noncomputable def partialsCLM (ux ut : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  ux • ContinuousLinearMap.fst ℝ ℝ ℝ + ut • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The functional `Transport.partialsCLM ux ut` takes the value $u_x q_1 + u_t q_2$ at
$q = (q_1, q_2)$. -/
@[simp]
theorem partialsCLM_apply (ux ut : ℝ) (q : ℝ × ℝ) : partialsCLM ux ut q = ux * q.1 + ut * q.2 :=
  rfl

/-- The functional of the pair of partial derivatives $(0, 0)$ is the zero functional. -/
theorem partialsCLM_zero : partialsCLM 0 0 = 0 :=
  ContinuousLinearMap.ext fun q => by simp

/-- The functional of a pair of partial derivatives is additive in the pair: the sum of the
functionals of $(a, b)$ and $(c, d)$ is the functional of $(a + c, b + d)$. -/
theorem partialsCLM_add (a b c d : ℝ) :
    partialsCLM a b + partialsCLM c d = partialsCLM (a + c) (b + d) :=
  ContinuousLinearMap.ext fun q => by
    simp only [_root_.add_apply, partialsCLM_apply]
    ring

/-- The functional of a pair of partial derivatives is homogeneous in the pair: $r$ times the
functional of $(a, b)$ is the functional of $(ra, rb)$. -/
theorem partialsCLM_smul (r a b : ℝ) : r • partialsCLM a b = partialsCLM (r * a) (r * b) :=
  ContinuousLinearMap.ext fun q => by
    simp only [_root_.smul_apply, partialsCLM_apply, smul_eq_mul]
    ring

/-- For a finite index set $s$ and numbers $c_i$, the combination with coefficients $c_i$ of the
functionals of the pairs $(u_{x,i}, u_{t,i})$, $i \in s$, is the functional of the pair
$(\sum_{i \in s} c_i u_{x,i}, \sum_{i \in s} c_i u_{t,i})$. -/
theorem partialsCLM_sum {ι : Type*} (s : Finset ι) (c ux ut : ι → ℝ) :
    ∑ i ∈ s, c i • partialsCLM (ux i) (ut i)
      = partialsCLM (∑ i ∈ s, c i * ux i) (∑ i ∈ s, c i * ut i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using partialsCLM_zero.symm
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi, ih, partialsCLM_smul,
      partialsCLM_add]

/-- **A function of two variables with given partial derivatives on a region.** Let
$s \subseteq \mathbb{R} \times \mathbb{R}$ and let $u$, $u_x$, $u_t$ be functions of $(x, t)$.
The predicate holds if at every point $q \in s$ the function $(x, t) \mapsto u(x, t)$ has,
within $s$, the Fréchet derivative $(y, \tau) \mapsto u_x(q) y + u_t(q) \tau$.

The derivative within $s$ makes the one-sided derivatives at the boundary of $s$ the right
notion. The derivative is `Transport.partialsCLM`. -/
def HasPartialsOn (s : Set (ℝ × ℝ)) (u ux ut : ℝ → ℝ → ℝ) : Prop :=
  ∀ q ∈ s, HasFDerivWithinAt (fun r : ℝ × ℝ => u r.1 r.2)
    (partialsCLM (ux q.1 q.2) (ut q.1 q.2)) s q

/-- If $u$ has partial derivatives $u_x$, $u_t$ on a region $s$, then it has the same partial
derivatives on every subset of $s$. -/
theorem HasPartialsOn.mono {s t : Set (ℝ × ℝ)} {u ux ut : ℝ → ℝ → ℝ} (h : HasPartialsOn s u ux ut)
    (hts : t ⊆ s) : HasPartialsOn t u ux ut :=
  fun q hq => (h q (hts hq)).mono hts

/-- Let $S \subseteq \mathbb{R} \times \mathbb{R}$, let $s$ be a finite index set, and let
$c_i \in \mathbb{R}$. If each $u_i$ has partial derivatives $u_{x,i}$, $u_{t,i}$ on $S$ for
$i \in s$, then $\sum_{i \in s} c_i u_i$ has partial derivatives $\sum_{i \in s} c_i u_{x,i}$
and $\sum_{i \in s} c_i u_{t,i}$ on $S$. -/
theorem HasPartialsOn.sum {ι : Type*} {s : Finset ι} {S : Set (ℝ × ℝ)} {c : ι → ℝ}
    {u ux ut : ι → ℝ → ℝ → ℝ} (h : ∀ i ∈ s, HasPartialsOn S (u i) (ux i) (ut i)) :
    HasPartialsOn S (fun x t => ∑ i ∈ s, c i * u i x t) (fun x t => ∑ i ∈ s, c i * ux i x t)
      (fun x t => ∑ i ∈ s, c i * ut i x t) := by
  intro q hq
  have h0 := HasFDerivWithinAt.sum fun i (hi : i ∈ s) => (h i hi q hq).const_mul (c i)
  rw [show (∑ i ∈ s, fun r : ℝ × ℝ => c i * u i r.1 r.2)
      = fun r : ℝ × ℝ => ∑ i ∈ s, c i * u i r.1 r.2 from funext fun r => Finset.sum_apply r s _,
    partialsCLM_sum] at h0
  exact h0

/-- **Partial derivatives of a travelling wave.** Let $g : \mathbb{R} \to \mathbb{R}$ be
differentiable and $a \in \mathbb{R}$. On every region
$S \subseteq \mathbb{R} \times \mathbb{R}$, the function $(x, t) \mapsto g(x - at)$ has the
partial derivatives $g'(x - at)$ in $x$ and $-a \, g'(x - at)$ in $t$. -/
theorem hasPartialsOn_comp_sub {g : ℝ → ℝ} (hg : Differentiable ℝ g) (a : ℝ) (S : Set (ℝ × ℝ)) :
    HasPartialsOn S (fun x t => g (x - a * t)) (fun x t => deriv g (x - a * t))
      (fun x t => -(a * deriv g (x - a * t))) := by
  intro q _
  have h1 : HasFDerivAt (fun r : ℝ × ℝ => r.1 - a * r.2) (partialsCLM 1 (-a)) q := by
    refine ((hasFDerivAt_fst (𝕜 := ℝ)).sub ((hasFDerivAt_snd (𝕜 := ℝ)).const_mul a)).congr_fderiv ?_
    exact ContinuousLinearMap.ext fun r => by simp [sub_eq_add_neg]
  have h2 := ((hg (q.1 - a * q.2)).hasDerivAt.comp_hasFDerivAt q h1).hasFDerivWithinAt (s := S)
  refine h2.congr_fderiv (ContinuousLinearMap.ext fun r => ?_)
  simp only [_root_.smul_apply, smul_eq_mul, partialsCLM_apply]
  ring

/-! ### The scalar transport equation and its characteristics -/

/-- **A classical solution of the transport equation.** Let $a$, $a_0$ and $f$ be functions of
$(x, t)$ and let $u_0 : \mathbb{R} \to \mathbb{R}$. A function $u$ of $(x, t)$ is a solution of
$$\partial_t u + a \, \partial_x u + a_0 u = f, \qquad u(\cdot, 0) = u_0,$$
on the closed half plane $\mathbb{R} \times [0, \infty)$ if there are functions $u_x$, $u_t$
such that $u$ has partial derivatives $u_x$, $u_t$ on $\mathbb{R} \times [0, \infty)$, the
equation $u_t + a u_x + a_0 u = f$ holds at every point $(x, t)$ with $t \ge 0$, and
$u(x, 0) = u_0(x)$ for all $x$.

This is (13.28) of [quarteroni2000numerical], and (13.26) when $a_0 = f = 0$. -/
def IsSolution (a a₀ f : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ ux ut : ℝ → ℝ → ℝ, HasPartialsOn (univ ×ˢ Ici 0) u ux ut ∧
    (∀ x t : ℝ, 0 ≤ t → ut x t + a x t * ux x t + a₀ x t * u x t = f x t) ∧ ∀ x, u x 0 = u₀ x

/-- **A characteristic curve** of the speed field $a(x, t)$ through $x_0$ is a function
$x : \mathbb{R} \to \mathbb{R}$ with $x(0) = x_0$ that satisfies $x'(t) = a(x(t), t)$ for every
$t \ge 0$, the derivative being taken within $[0, \infty)$. This is (13.27) of
[quarteroni2000numerical]. -/
def IsCharacteristic (a : ℝ → ℝ → ℝ) (x₀ : ℝ) (x : ℝ → ℝ) : Prop :=
  x 0 = x₀ ∧ ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt x (a (x t) t) (Ici 0) t

/-- **The characteristics of a constant speed field are lines.** For $a, x_0 \in \mathbb{R}$, the
line $t \mapsto x_0 + at$ is a characteristic of the constant speed field $a$ through $x_0$. -/
theorem characteristic_const (a x₀ : ℝ) :
    IsCharacteristic (fun _ _ => a) x₀ (fun t => x₀ + a * t) := by
  refine ⟨by simp, fun t _ => ?_⟩
  simpa using (((hasDerivAt_id t).const_mul a).const_add x₀).hasDerivWithinAt

/-- A function whose derivative within $[0, \infty)$ vanishes at every $t \ge 0$ is constant on
$[0, \infty)$. -/
private theorem eq_zero_of_hasDerivWithinAt_zero {g : ℝ → ℝ}
    (hg : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt g 0 (Ici 0) t) {t : ℝ} (ht : 0 ≤ t) : g t = g 0 := by
  have hcont : ContinuousOn g (Icc 0 t) := fun s hs =>
    ((hg s hs.1).continuousWithinAt).mono (Icc_subset_Ici_self)
  refine constant_of_has_deriv_right_zero hcont (fun s hs => ?_) t (right_mem_Icc.2 ht)
  exact (hg s hs.1).mono (Ici_subset_Ici.2 hs.1)

/-- **Uniqueness of the characteristics of a constant speed field.** Let $a, x_0 \in \mathbb{R}$.
Every characteristic $x$ of the constant speed field $a$ through $x_0$ satisfies
$x(t) = x_0 + at$ for all $t \ge 0$. -/
theorem IsCharacteristic.eq_of_const {a x₀ : ℝ} {x : ℝ → ℝ}
    (hx : IsCharacteristic (fun _ _ => a) x₀ x) {t : ℝ} (ht : 0 ≤ t) : x t = x₀ + a * t := by
  have hg : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt (fun s => x s - a * s) 0 (Ici 0) s := fun s hs => by
    have h0 : HasDerivWithinAt x a (Ici 0) s := hx.2 s hs
    have h1 : HasDerivWithinAt (fun y : ℝ => a * y) a (Ici 0) s := by
      simpa using ((hasDerivAt_id s).const_mul a).hasDerivWithinAt
    have := h0.sub h1
    rwa [sub_self] at this
  have h := eq_zero_of_hasDerivWithinAt_zero hg ht
  simp only [mul_zero, sub_zero, hx.1] at h
  linarith

/-- **A solution satisfies an ordinary differential equation along a characteristic.** Let $u$ be a
classical solution of $\partial_t u + a \, \partial_x u + a_0 u = f$ with datum $u_0$, and let
$x$ be a characteristic of $a$ through some $x_0$. Then for every $t \ge 0$ the function
$t \mapsto u(x(t), t)$ has, within $[0, \infty)$, the derivative
$$\frac{d}{dt} u(x(t), t) = f(x(t), t) - a_0(x(t), t) \, u(x(t), t).$$
This is §13.5 of [quarteroni2000numerical]. The proof is the chain rule for
$t \mapsto (x(t), t)$. -/
theorem IsSolution.hasDerivAt_comp_characteristic {a a₀ f : ℝ → ℝ → ℝ} {u₀ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} (hu : IsSolution a a₀ f u₀ u) {x₀ : ℝ} {x : ℝ → ℝ}
    (hx : IsCharacteristic a x₀ x) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun t => u (x t) t) (f (x t) t - a₀ (x t) t * u (x t) t) (Ici 0) t := by
  obtain ⟨ux, ut, hd, hpde, -⟩ := hu
  have hcurve : HasDerivWithinAt (fun s => (x s, s)) (a (x t) t, 1) (Ici 0) t :=
    (hx.2 t ht).prodMk (hasDerivWithinAt_id t _)
  have hmaps : MapsTo (fun s => (x s, s)) (Ici (0 : ℝ)) (univ ×ˢ Ici 0) :=
    fun s hs => ⟨mem_univ _, hs⟩
  have h := (hd (x t, t) ⟨mem_univ _, ht⟩).comp_hasDerivWithinAt_of_eq
    (f := fun s => (x s, s)) t hcurve hmaps rfl
  have hval : partialsCLM (ux (x t) t) (ut (x t) t) (a (x t) t, 1)
      = f (x t) t - a₀ (x t) t * u (x t) t := by
    have := hpde (x t) t ht
    simp only [partialsCLM_apply, mul_one]
    linarith
  rw [hval] at h
  exact h

/-- **A solution is constant along the characteristics.** Let $a \in \mathbb{R}$ and let $u$ be a
classical solution of $\partial_t u + a \, \partial_x u = 0$ with datum $u_0$. If $x$ is a
characteristic of the constant speed field $a$ through $x_0$, then $u(x(t), t) = u_0(x_0)$ for
every $t \ge 0$. This is the equation $du/dt = 0$ of §13.5 of [quarteroni2000numerical]. -/
theorem IsSolution.comp_characteristic_const {a : ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : IsSolution (fun _ _ => a) 0 0 u₀ u) {x₀ : ℝ} {x : ℝ → ℝ}
    (hx : IsCharacteristic (fun _ _ => a) x₀ x) {t : ℝ} (ht : 0 ≤ t) : u (x t) t = u₀ x₀ := by
  have hg : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt (fun s => u (x s) s) 0 (Ici 0) s := fun s hs => by
    simpa using hu.hasDerivAt_comp_characteristic hx hs
  have hconst := eq_zero_of_hasDerivWithinAt_zero hg ht
  obtain ⟨-, -, -, -, hinit⟩ := hu
  rw [hconst, hx.1]
  exact hinit x₀

/-- **The travelling wave is a solution.** Let $a \in \mathbb{R}$ and let
$u_0 : \mathbb{R} \to \mathbb{R}$ be differentiable. Then $u(x, t) = u_0(x - at)$ is a classical
solution of $\partial_t u + a \, \partial_x u = 0$ with datum $u_0$, as in §13.5 of
[quarteroni2000numerical]. -/
theorem isSolution_comp_sub {a : ℝ} {u₀ : ℝ → ℝ} (hu₀ : Differentiable ℝ u₀) :
    IsSolution (fun _ _ => a) 0 0 u₀ fun x t => u₀ (x - a * t) := by
  exact ⟨_, _, hasPartialsOn_comp_sub hu₀ a _, fun x t _ => by simp, fun x => by simp⟩

/-- **Uniqueness for the transport equation.** Let $a \in \mathbb{R}$ and let $u$ be a classical
solution of $\partial_t u + a \, \partial_x u = 0$ with datum $u_0$. Then
$u(x, t) = u_0(x - at)$ for all $x$ and all $t \ge 0$, as in §13.5 of [quarteroni2000numerical]. -/
theorem IsSolution.eq_comp_sub {a : ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : IsSolution (fun _ _ => a) 0 0 u₀ u) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    u x t = u₀ (x - a * t) := by
  simpa using hu.comp_characteristic_const (characteristic_const a (x - a * t)) ht

/-- **The maximum principle for the transport equation.** Let $a \in \mathbb{R}$, let $u$ be a
classical solution of $\partial_t u + a \, \partial_x u = 0$ with datum $u_0$, and assume that
$|u_0|$ is bounded above. Then for all $x$ and all $t \ge 0$,
$$|u(x, t)| \le \sup_s |u_0(s)|.$$
This is §13.8.4 of [quarteroni2000numerical]. -/
theorem IsSolution.abs_le_sup {a : ℝ} {u₀ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hu : IsSolution (fun _ _ => a) 0 0 u₀ u) (hb : BddAbove (range fun s => |u₀ s|)) (x : ℝ)
    {t : ℝ} (ht : 0 ≤ t) : |u x t| ≤ ⨆ s, |u₀ s| := by
  rw [hu.eq_comp_sub x ht]
  exact le_ciSup hb _

/-! ### Hyperbolic systems -/

variable {p : ℕ}

/-- **A classical solution of a hyperbolic system on a region.** Let $s \subseteq \mathbb{R}$,
$A \in \mathbb{R}^{p \times p}$ and $u_0 : \mathbb{R} \to \mathbb{R}^p$. A function
$u(x, t) \in \mathbb{R}^p$ is a solution of $\partial_t u + A \, \partial_x u = 0$ with datum
$u_0$ on $s \times [0, \infty)$ if there are functions $u_x$, $u_t$ with values in
$\mathbb{R}^p$ such that each component $u_k$ has partial derivatives $(u_x)_k$, $(u_t)_k$ on
$s \times [0, \infty)$, the equation $u_t + A u_x = 0$ holds at every $(x, t)$ with $x \in s$
and $t \ge 0$, and $u(x, 0) = u_0(x)$ for $x \in s$. This is (13.30) of
[quarteroni2000numerical]. -/
def IsSystemSolutionOn (s : Set ℝ) (A : Matrix (Fin p) (Fin p) ℝ) (u₀ : ℝ → Fin p → ℝ)
    (u : ℝ → ℝ → Fin p → ℝ) : Prop :=
  ∃ ux ut : ℝ → ℝ → Fin p → ℝ,
    (∀ k, HasPartialsOn (s ×ˢ Ici 0) (fun x t => u x t k) (fun x t => ux x t k)
      fun x t => ut x t k) ∧
    (∀ x ∈ s, ∀ t : ℝ, 0 ≤ t → ut x t + A *ᵥ ux x t = 0) ∧ ∀ x ∈ s, u x 0 = u₀ x

/-- **A classical solution of a hyperbolic system** $\partial_t u + A \, \partial_x u = 0$ with
datum $u_0$ on the whole half plane $\mathbb{R} \times [0, \infty)$, that is,
`Transport.IsSystemSolutionOn` with $s = \mathbb{R}$. This is (13.30) of
[quarteroni2000numerical]. -/
def IsSystemSolution (A : Matrix (Fin p) (Fin p) ℝ) (u₀ : ℝ → Fin p → ℝ)
    (u : ℝ → ℝ → Fin p → ℝ) : Prop := IsSystemSolutionOn univ A u₀ u

/-- A matrix $A \in \mathbb{R}^{p \times p}$ is **hyperbolic** if it is diagonalizable over
$\mathbb{R}$: there are an invertible $T \in \mathbb{R}^{p \times p}$ and
$\lambda \in \mathbb{R}^p$ with
$$A = T \Lambda T^{-1}, \qquad \Lambda = \operatorname{diag}(\lambda_1, \dots, \lambda_p).$$
This is the definition of §13.6 of [quarteroni2000numerical]. -/
def IsHyperbolic (A : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  ∃ (T : Matrix (Fin p) (Fin p) ℝ) (lam : Fin p → ℝ), IsUnit T ∧ A = T * diagonal lam * T⁻¹

/-- A matrix $A \in \mathbb{R}^{p \times p}$ is **strictly hyperbolic** if $A = T \Lambda T^{-1}$
with $T$ invertible and $\Lambda = \operatorname{diag}(\lambda_1, \dots, \lambda_p)$ for
pairwise distinct real $\lambda_k$. This is the definition of §13.6 of
[quarteroni2000numerical]. -/
def IsStrictlyHyperbolic (A : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  ∃ (T : Matrix (Fin p) (Fin p) ℝ) (lam : Fin p → ℝ),
    IsUnit T ∧ Function.Injective lam ∧ A = T * diagonal lam * T⁻¹

/-- A strictly hyperbolic matrix is hyperbolic. -/
theorem IsStrictlyHyperbolic.isHyperbolic {A : Matrix (Fin p) (Fin p) ℝ}
    (h : IsStrictlyHyperbolic A) : IsHyperbolic A :=
  let ⟨T, lam, hT, _, hA⟩ := h; ⟨T, lam, hT, hA⟩

/-- For $T \in \mathbb{R}^{p \times p}$ and $v \in \mathbb{R}^p$, the product $Tv$ is the
combination $\sum_k v_k \omega^k$ of the columns $\omega^k$ of $T$. -/
theorem mulVec_eq_sum_smul_col (T : Matrix (Fin p) (Fin p) ℝ) (v : Fin p → ℝ) :
    T *ᵥ v = ∑ k, v k • Tᵀ k := by
  ext j
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- **The columns of $T$ are right eigenvectors.** Let $T \in \mathbb{R}^{p \times p}$ be
invertible, $\lambda \in \mathbb{R}^p$, and $A = T \Lambda T^{-1}$ with $\Lambda =
\operatorname{diag}(\lambda_1, \dots, \lambda_p)$. Then the column $\omega^k$ of $T$ satisfies
$A \omega^k = \lambda_k \omega^k$ for each $k$, as in §13.6 of [quarteroni2000numerical]. -/
theorem mulVec_col_eq_smul {A T : Matrix (Fin p) (Fin p) ℝ} {lam : Fin p → ℝ} (hT : IsUnit T)
    (hA : A = T * diagonal lam * T⁻¹) (k : Fin p) : A *ᵥ Tᵀ k = lam k • Tᵀ k := by
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 hT
  have hAT : A * T = T * diagonal lam := by
    rw [hA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  ext i
  have h1 : (A *ᵥ Tᵀ k) i = (A * T) i k := by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have h2 : (lam k • Tᵀ k) i = (T * diagonal lam) i k := by
    simp [Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]
  rw [h1, h2, hAT]

/-- **The characteristic variables decouple the system.** Let $T \in \mathbb{R}^{p \times p}$ be
invertible, $\lambda \in \mathbb{R}^p$, and $A = T \Lambda T^{-1}$ with $\Lambda =
\operatorname{diag}(\lambda_1, \dots, \lambda_p)$. Let $u$ be a classical solution of
$\partial_t u + A \, \partial_x u = 0$ on $\mathbb{R} \times [0, \infty)$ with datum $u_0$. Then
for each $k$, the component $w_k$ of $w = T^{-1} u$ is a classical solution of the scalar
transport equation $\partial_t w_k + \lambda_k \partial_x w_k = 0$ with datum $(T^{-1} u_0)_k$.
This is §13.6 of [quarteroni2000numerical]. -/
theorem IsSystemSolution.characteristicVariables {A T : Matrix (Fin p) (Fin p) ℝ}
    {lam : Fin p → ℝ} (hT : IsUnit T) (hA : A = T * diagonal lam * T⁻¹) {u₀ : ℝ → Fin p → ℝ}
    {u : ℝ → ℝ → Fin p → ℝ} (hu : IsSystemSolution A u₀ u) (k : Fin p) :
    IsSolution (fun _ _ => lam k) 0 0 (fun x => (T⁻¹ *ᵥ u₀ x) k) fun x t => (T⁻¹ *ᵥ u x t) k := by
  obtain ⟨ux, ut, hd, hpde, hinit⟩ := hu
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 hT
  have hTA : T⁻¹ * A = diagonal lam * T⁻¹ := by
    rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  refine ⟨fun x t => (T⁻¹ *ᵥ ux x t) k, fun x t => (T⁻¹ *ᵥ ut x t) k, ?_, fun x t ht => ?_,
    fun x => by change (T⁻¹ *ᵥ u x 0) k = (T⁻¹ *ᵥ u₀ x) k; rw [hinit x (mem_univ x)]⟩
  · have := HasPartialsOn.sum (s := (Finset.univ : Finset (Fin p))) (c := fun j => T⁻¹ k j)
      (u := fun j x t => u x t j) (ux := fun j x t => ux x t j) (ut := fun j x t => ut x t j)
      fun j _ => hd j
    simpa [Matrix.mulVec, dotProduct] using this
  · have hz := hpde x (mem_univ x) t ht
    have key : (T⁻¹ *ᵥ ut x t) k + lam k * (T⁻¹ *ᵥ ux x t) k = 0 := by
      have h1 : T⁻¹ *ᵥ (ut x t + A *ᵥ ux x t) = 0 := by rw [hz, Matrix.mulVec_zero]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hTA, ← Matrix.mulVec_mulVec] at h1
      have h2 := congrFun h1 k
      rwa [Pi.add_apply, Matrix.mulVec_diagonal, Pi.zero_apply] at h2
    simp only [Pi.zero_apply, zero_mul, add_zero]
    linarith

/-- **The solution formula for a hyperbolic system.** Let $T \in \mathbb{R}^{p \times p}$ be
invertible, $\lambda \in \mathbb{R}^p$, and $A = T \Lambda T^{-1}$ with $\Lambda =
\operatorname{diag}(\lambda_1, \dots, \lambda_p)$. Let $u_0 : \mathbb{R} \to \mathbb{R}^p$ be
such that each component of $x \mapsto T^{-1} u_0(x)$ is differentiable. Then
$$u(x, t) = \sum_k \bigl(T^{-1} u_0(x - \lambda_k t)\bigr)_k \, \omega^k,$$
where $\omega^k$ is the column $k$ of $T$, is a classical solution of
$\partial_t u + A \, \partial_x u = 0$ on $\mathbb{R} \times [0, \infty)$ with datum $u_0$. This
is §13.6 of [quarteroni2000numerical]. -/
theorem isSystemSolution_sum {A T : Matrix (Fin p) (Fin p) ℝ} {lam : Fin p → ℝ} (hT : IsUnit T)
    (hA : A = T * diagonal lam * T⁻¹) {u₀ : ℝ → Fin p → ℝ}
    (hu₀ : ∀ k, Differentiable ℝ fun x => (T⁻¹ *ᵥ u₀ x) k) :
    IsSystemSolution A u₀ fun x t => ∑ k, (T⁻¹ *ᵥ u₀ (x - lam k * t)) k • Tᵀ k := by
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 hT
  set c : Fin p → ℝ → ℝ := fun k x => (T⁻¹ *ᵥ u₀ x) k with hc
  refine ⟨fun x t j => ∑ k, deriv (c k) (x - lam k * t) * T j k,
    fun x t j => ∑ k, -(lam k * deriv (c k) (x - lam k * t)) * T j k, fun j => ?_,
    fun x _ t _ => ?_, fun x _ => ?_⟩
  · have := HasPartialsOn.sum (s := (Finset.univ : Finset (Fin p))) (c := fun k => T j k)
      (u := fun k x t => c k (x - lam k * t))
      (ux := fun k x t => deriv (c k) (x - lam k * t))
      (ut := fun k x t => -(lam k * deriv (c k) (x - lam k * t)))
      (S := (univ ×ˢ Ici 0 : Set (ℝ × ℝ)))
      fun k _ => hasPartialsOn_comp_sub (hu₀ k) (lam k) _
    simpa [hc, mul_comm] using this
  · ext j
    have hcol : ∀ k, (A *ᵥ Tᵀ k) j = lam k * T j k := fun k => by
      have := congrFun (mulVec_col_eq_smul hT hA k) j
      simpa using this
    have hAx : (A *ᵥ fun j => ∑ k, deriv (c k) (x - lam k * t) * T j k) j
        = ∑ k, deriv (c k) (x - lam k * t) * (lam k * T j k) := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hcol k]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [Pi.add_apply, Pi.zero_apply, hAx, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun k _ => by ring
  · have h0 : ∑ k, c k (x - lam k * 0) • Tᵀ k = T *ᵥ (T⁻¹ *ᵥ u₀ x) := by
      rw [mulVec_eq_sum_smul_col]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_zero, sub_zero]
    change ∑ k, c k (x - lam k * 0) • Tᵀ k = u₀ x
    rw [h0, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- **Uniqueness for a hyperbolic system.** Let $T \in \mathbb{R}^{p \times p}$ be invertible,
$\lambda \in \mathbb{R}^p$, and $A = T \Lambda T^{-1}$ with $\Lambda =
\operatorname{diag}(\lambda_1, \dots, \lambda_p)$. Every classical solution $u$ of
$\partial_t u + A \, \partial_x u = 0$ on $\mathbb{R} \times [0, \infty)$ with datum $u_0$
satisfies, for all $x$ and all $t \ge 0$,
$$u(x, t) = \sum_k \bigl(T^{-1} u_0(x - \lambda_k t)\bigr)_k \, \omega^k,$$
where $\omega^k$ is the column $k$ of $T$. This is §13.6 of [quarteroni2000numerical]. -/
theorem IsSystemSolution.eq_sum {A T : Matrix (Fin p) (Fin p) ℝ} {lam : Fin p → ℝ} (hT : IsUnit T)
    (hA : A = T * diagonal lam * T⁻¹) {u₀ : ℝ → Fin p → ℝ} {u : ℝ → ℝ → Fin p → ℝ}
    (hu : IsSystemSolution A u₀ u) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    u x t = ∑ k, (T⁻¹ *ᵥ u₀ (x - lam k * t)) k • Tᵀ k := by
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 hT
  have hw : ∀ k, (T⁻¹ *ᵥ u x t) k = (T⁻¹ *ᵥ u₀ (x - lam k * t)) k := fun k =>
    (hu.characteristicVariables hT hA k).eq_comp_sub x ht
  have hTT : u x t = T *ᵥ (T⁻¹ *ᵥ u x t) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  rw [hTT, mulVec_eq_sum_smul_col]
  exact Finset.sum_congr rfl fun k _ => by rw [hw k]

/-- The **domain of dependence** of the point $(\bar{x}, \bar{t})$ for the speeds
$\lambda_1, \dots, \lambda_p$ is the set
$$\{\bar{x} - \lambda_k \bar{t} : k = 1, \dots, p\}$$
of the feet of the characteristics through $(\bar{x}, \bar{t})$. This is (13.31) of
[quarteroni2000numerical]. -/
def domainOfDependence (lam : Fin p → ℝ) (xb tb : ℝ) : Set ℝ := range fun k => xb - lam k * tb

/-- **The solution depends on the datum only on the domain of dependence.** Let
$T \in \mathbb{R}^{p \times p}$ be invertible, $\lambda \in \mathbb{R}^p$, and
$A = T \Lambda T^{-1}$ with $\Lambda = \operatorname{diag}(\lambda_1, \dots, \lambda_p)$. Let
$u$ and $v$ be classical solutions of $\partial_t u + A \, \partial_x u = 0$ on
$\mathbb{R} \times [0, \infty)$ with data $u_0$ and $v_0$, and let $\bar{t} \ge 0$. If
$u_0 = v_0$ on the domain of dependence of $(\bar{x}, \bar{t})$, then
$u(\bar{x}, \bar{t}) = v(\bar{x}, \bar{t})$. This is §13.6 of [quarteroni2000numerical]. -/
theorem IsSystemSolution.eq_of_eqOn_domainOfDependence {A T : Matrix (Fin p) (Fin p) ℝ}
    {lam : Fin p → ℝ} (hT : IsUnit T) (hA : A = T * diagonal lam * T⁻¹)
    {u₀ v₀ : ℝ → Fin p → ℝ} {u v : ℝ → ℝ → Fin p → ℝ} (hu : IsSystemSolution A u₀ u)
    (hv : IsSystemSolution A v₀ v) {xb tb : ℝ} (htb : 0 ≤ tb)
    (h : EqOn u₀ v₀ (domainOfDependence lam xb tb)) : u xb tb = v xb tb := by
  rw [hu.eq_sum hT hA xb htb, hv.eq_sum hT hA xb htb]
  exact Finset.sum_congr rfl fun k _ => by rw [h ⟨k, rfl⟩]

/-! ### The wave equation as a first-order system -/

/-- The **matrix of the wave equation** for $\gamma \in \mathbb{R}$,
$$A = \begin{bmatrix} 0 & -1 \\ -\gamma^2 & 0 \end{bmatrix},$$
the coefficient of the first-order system for $(\partial_x u, \partial_t u)$. This is (13.35) of
[quarteroni2000numerical]. -/
def waveMatrix (γ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; -γ ^ 2, 0]

/-- **The wave equation is strictly hyperbolic.** For $\gamma \neq 0$, the matrix
`Transport.waveMatrix γ` is strictly hyperbolic, with eigenvalues $\gamma$ and $-\gamma$ and
eigenvectors $(1, -\gamma)$ and $(1, \gamma)$. This is §13.6.1 of [quarteroni2000numerical]. -/
theorem waveMatrix_isStrictlyHyperbolic {γ : ℝ} (hγ : γ ≠ 0) :
    IsStrictlyHyperbolic (waveMatrix γ) := by
  refine ⟨!![1, 1; -γ, γ], ![γ, -γ], ?_, ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_fin_two_of]
    intro h
    apply hγ
    linarith
  · have hne : γ ≠ -γ := fun h => hγ (by linarith)
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] at hij
      exact absurd hij hne
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] at hij
      exact absurd hij.symm hne
    · rfl
  · have hdet : IsUnit (!![(1 : ℝ), 1; -γ, γ]).det := by
      rw [isUnit_iff_ne_zero, Matrix.det_fin_two_of]
      intro h
      apply hγ
      linarith
    have hmul : waveMatrix γ * !![(1 : ℝ), 1; -γ, γ]
        = !![(1 : ℝ), 1; -γ, γ] * diagonal ![γ, -γ] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [waveMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply] <;> ring
    calc waveMatrix γ = waveMatrix γ * !![(1 : ℝ), 1; -γ, γ] * (!![(1 : ℝ), 1; -γ, γ])⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = !![(1 : ℝ), 1; -γ, γ] * diagonal ![γ, -γ] * (!![(1 : ℝ), 1; -γ, γ])⁻¹ := by rw [hmul]

/-- **A classical solution of the wave equation** on a strip. Let
$\gamma, \alpha, \beta \in \mathbb{R}$, let $f$ be a function of $(x, t)$, and let
$u_0, v_0 : \mathbb{R} \to \mathbb{R}$. A function $u$ of $(x, t)$ is a solution of
$$\partial_{tt} u - \gamma^2 \partial_{xx} u = f$$
on $[\alpha, \beta] \times [0, \infty)$, with initial displacement $u_0$, initial velocity $v_0$
and homogeneous Dirichlet conditions, if there are functions $u_x$, $u_t$, $u_{xx}$, $u_{xt}$,
$u_{tt}$ with the following properties. On $[\alpha, \beta] \times [0, \infty)$, $u$ has partial
derivatives $u_x$, $u_t$, $u_x$ has partial derivatives $u_{xx}$, $u_{xt}$, and $u_t$ has
partial derivatives $u_{xt}$, $u_{tt}$. The equation $u_{tt} - \gamma^2 u_{xx} = f$ holds for
$x \in [\alpha, \beta]$ and $t \ge 0$. For $x \in [\alpha, \beta]$, $u(x, 0) = u_0(x)$ and
$u_t(x, 0) = v_0(x)$. For $t \ge 0$, $u(\alpha, t) = u(\beta, t) = 0$. This is (13.33)–(13.34)
of [quarteroni2000numerical].

One function $u_{xt}$ serves for the two mixed partial derivatives. For a $C^2$ function this is
no restriction, by the symmetry of the second derivative. -/
def IsWaveSolution (γ : ℝ) (f : ℝ → ℝ → ℝ) (u₀ v₀ : ℝ → ℝ) (α β : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ ux ut uxx uxt utt : ℝ → ℝ → ℝ,
    HasPartialsOn (Icc α β ×ˢ Ici 0) u ux ut ∧ HasPartialsOn (Icc α β ×ˢ Ici 0) ux uxx uxt ∧
      HasPartialsOn (Icc α β ×ˢ Ici 0) ut uxt utt ∧
      (∀ x ∈ Icc α β, ∀ t : ℝ, 0 ≤ t → utt x t - γ ^ 2 * uxx x t = f x t) ∧
      (∀ x ∈ Icc α β, u x 0 = u₀ x ∧ ut x 0 = v₀ x) ∧
      ∀ t : ℝ, 0 ≤ t → u α t = 0 ∧ u β t = 0

/-- **The wave equation as a first-order system.** Let $u$ be a classical solution of the
homogeneous wave equation $\partial_{tt} u = \gamma^2 \partial_{xx} u$ on
$[\alpha, \beta] \times [0, \infty)$ with initial displacement $u_0$, initial velocity $v_0$ and
homogeneous Dirichlet conditions at $x = \alpha$ and $x = \beta$, that is,
`Transport.IsWaveSolution` with $f = 0$. Then there is a function $w(x, t) \in \mathbb{R}^2$
that is a classical solution of $\partial_t w + A \, \partial_x w = 0$ on
$[\alpha, \beta] \times [0, \infty)$, with $A$ = `Transport.waveMatrix γ` and datum
$w(\cdot, 0)$, such that for $x \in [\alpha, \beta]$ the first component of $w(x, 0)$ is the
derivative of $u_0$ at $x$ within $[\alpha, \beta]$ and the second component is $v_0(x)$. This
is (13.35) of [quarteroni2000numerical].

The proof takes $w = (\partial_x u, \partial_t u)$. The first row of the system is the symmetry
of the mixed partial derivatives, and the second row is the wave equation. -/
theorem IsWaveSolution.isSystemSolution {γ : ℝ} {u₀ v₀ : ℝ → ℝ} {α β : ℝ} {u : ℝ → ℝ → ℝ}
    (h : IsWaveSolution γ 0 u₀ v₀ α β u) :
    ∃ w : ℝ → ℝ → Fin 2 → ℝ, IsSystemSolutionOn (Icc α β) (waveMatrix γ) (fun x => w x 0) w ∧
      (∀ x ∈ Icc α β, HasDerivWithinAt u₀ (w x 0 0) (Icc α β) x) ∧
      ∀ x ∈ Icc α β, w x 0 1 = v₀ x := by
  obtain ⟨ux, ut, uxx, uxt, utt, h1, h2, h3, heq, hinit, -⟩ := h
  refine ⟨fun x t => ![ux x t, ut x t], ⟨fun x t => ![uxx x t, uxt x t],
    fun x t => ![uxt x t, utt x t], fun k => ?_, fun x hx t ht => ?_, fun _ _ => rfl⟩,
    fun x hx => ?_, fun x hx => (hinit x hx).2⟩
  · fin_cases k
    · exact h2
    · exact h3
  · ext k
    have hz := heq x hx t ht
    simp only [Pi.zero_apply] at hz
    fin_cases k <;>
      simp only [Fin.zero_eta, Fin.mk_one, Pi.add_apply, Pi.zero_apply, waveMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.of_apply] <;> linarith
  · have hmaps : MapsTo (fun s : ℝ => (s, (0 : ℝ))) (Icc α β) (Icc α β ×ˢ Ici 0) :=
      fun s hs => ⟨hs, by simp⟩
    have hcurve : HasDerivWithinAt (fun s : ℝ => (s, (0 : ℝ))) (1, 0) (Icc α β) x :=
      (hasDerivWithinAt_id x _).prodMk (hasDerivWithinAt_const x _ _)
    have hd := (h1 (x, 0) ⟨hx, by simp⟩).comp_hasDerivWithinAt_of_eq
      (f := fun s : ℝ => (s, (0 : ℝ))) x hcurve hmaps rfl
    simp only [partialsCLM_apply, mul_one, mul_zero, add_zero] at hd
    refine hd.congr (fun s hs => ((hinit s hs).1).symm) ?_
    exact ((hinit x hx).1).symm

/-! ### The inflow problem on a strip -/

/-- **The inflow problem** on a strip. Let $a : \mathbb{R} \to \mathbb{R}$, let $a_0$ and $f$ be
functions of $(x, t)$, let $\varphi, u_0 : \mathbb{R} \to \mathbb{R}$, and let
$\alpha, \beta, T \in \mathbb{R}$. A function $u$ of $(x, t)$ is a solution of
$$\partial_t u + a(x) \, \partial_x u + a_0 u = f \ \text{ on } [\alpha, \beta] \times [0, T],
  \qquad u(\alpha, t) = \varphi(t), \qquad u(x, 0) = u_0(x),$$
if there are functions $u_x$, $u_t$ such that $u$ has partial derivatives $u_x$, $u_t$ on
$[\alpha, \beta] \times [0, T]$, the equation holds at every point of
$[\alpha, \beta] \times [0, T]$, $u(\alpha, t) = \varphi(t)$ for $t \in [0, T]$, and
$u(x, 0) = u_0(x)$ for $x \in [\alpha, \beta]$. This is (13.64) of [quarteroni2000numerical].

The end $x = \alpha$ is the inflow end when $a > 0$. The definition imposes no condition on the
sign of $a$. -/
def IsInflowSolution (a : ℝ → ℝ) (a₀ f : ℝ → ℝ → ℝ) (φ u₀ : ℝ → ℝ) (α β T : ℝ)
    (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ ux ut : ℝ → ℝ → ℝ, HasPartialsOn (Icc α β ×ˢ Icc 0 T) u ux ut ∧
    (∀ x ∈ Icc α β, ∀ t ∈ Icc (0 : ℝ) T,
      ut x t + a x * ux x t + a₀ x t * u x t = f x t) ∧
    (∀ t ∈ Icc (0 : ℝ) T, u α t = φ t) ∧ ∀ x ∈ Icc α β, u x 0 = u₀ x

/-! ### Partial derivatives along the coordinate lines -/

/-- If $u$ has partial derivatives $u_x$, $u_t$ on the whole plane, then for all $x, t$ the function
$y \mapsto u(y, t)$ has derivative $u_x(x, t)$ at $x$, in the sense of `HasPartialDerivFst`. -/
theorem hasPartialDerivFst_of_hasPartialsOn {u ux ut : ℝ → ℝ → ℝ}
    (h : HasPartialsOn Set.univ u ux ut) : HasPartialDerivFst u ux := by
  intro x t
  have h0 : HasFDerivAt (fun r : ℝ × ℝ => u r.1 r.2)
      (partialsCLM (ux x t) (ut x t)) (x, t) := by
    have h1 := h (x, t) (Set.mem_univ _)
    rwa [hasFDerivWithinAt_univ] at h1
  have hline : HasDerivAt (fun y : ℝ => (y, t)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
  have h2 := h0.comp_hasDerivAt x hline
  simp only [partialsCLM_apply, mul_one, mul_zero, add_zero, Function.comp_def] at h2
  exact h2

/-- If $u$ has partial derivatives $u_x$, $u_t$ on the whole plane, then for all $x, t$ the function
$s \mapsto u(x, s)$ has derivative $u_t(x, t)$ at $t$, in the sense of `HasPartialDerivSnd`. -/
theorem hasPartialDerivSnd_of_hasPartialsOn {u ux ut : ℝ → ℝ → ℝ}
    (h : HasPartialsOn Set.univ u ux ut) : HasPartialDerivSnd u ut := by
  intro x t
  have h0 : HasFDerivAt (fun r : ℝ × ℝ => u r.1 r.2)
      (partialsCLM (ux x t) (ut x t)) (x, t) := by
    have h1 := h (x, t) (Set.mem_univ _)
    rwa [hasFDerivWithinAt_univ] at h1
  have hline : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have h2 := h0.comp_hasDerivAt t hline
  simp only [partialsCLM_apply, mul_one, mul_zero, zero_add, Function.comp_def] at h2
  exact h2

/-! ### The partial derivatives of a classical solution along the coordinate lines -/

/-- Let $s, t \subseteq \mathbb{R}$ and let $u$ have partial derivatives $u_x$, $u_t$ on
$s \times t$. For $y \in s$ and $\tau \in t$, the function $y \mapsto u(y, \tau)$ has derivative
$u_x(y, \tau)$ at $y$ within $s$. -/
theorem HasPartialsOn.hasDerivWithinAt_fst {s t : Set ℝ} {u ux ut : ℝ → ℝ → ℝ}
    (h : HasPartialsOn (s ×ˢ t) u ux ut) {y τ : ℝ} (hy : y ∈ s) (hτ : τ ∈ t) :
    HasDerivWithinAt (fun y => u y τ) (ux y τ) s y := by
  have h0 := h (y, τ) ⟨hy, hτ⟩
  have hline : HasDerivWithinAt (fun y : ℝ => (y, τ)) (1, 0) s y :=
    ((hasDerivAt_id y).prodMk (hasDerivAt_const y τ)).hasDerivWithinAt
  have h2 := h0.comp_hasDerivWithinAt y hline (fun z hz => Set.mk_mem_prod hz hτ)
  simp only [partialsCLM_apply, mul_one, mul_zero, add_zero, Function.comp_def] at h2
  exact h2

/-- Let $s, t \subseteq \mathbb{R}$ and let $u$ have partial derivatives $u_x$, $u_t$ on
$s \times t$. For $y \in s$ and $\tau \in t$, the function $\tau \mapsto u(y, \tau)$ has
derivative $u_t(y, \tau)$ at $\tau$ within $t$. -/
theorem HasPartialsOn.hasDerivWithinAt_snd {s t : Set ℝ} {u ux ut : ℝ → ℝ → ℝ}
    (h : HasPartialsOn (s ×ˢ t) u ux ut) {y τ : ℝ} (hy : y ∈ s) (hτ : τ ∈ t) :
    HasDerivWithinAt (fun τ => u y τ) (ut y τ) t τ := by
  have h0 := h (y, τ) ⟨hy, hτ⟩
  have hline : HasDerivWithinAt (fun τ : ℝ => (y, τ)) (0, 1) t τ :=
    ((hasDerivAt_const τ y).prodMk (hasDerivAt_id τ)).hasDerivWithinAt
  have h2 := h0.comp_hasDerivWithinAt τ hline (fun z hz => Set.mk_mem_prod hy hz)
  simp only [partialsCLM_apply, mul_one, mul_zero, zero_add, Function.comp_def] at h2
  exact h2

end Transport
