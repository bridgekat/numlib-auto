/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Complexity.GapRecurrence
import Numlib.Optimization.ModelBased.ARpRun

/-!
# Measure-dominated objectives and AR-like and TR-like methods

Let $\psi \ge 0$ be an optimality measure on a space $E$. An objective $f \colon E \to \mathbb{R}$
is $\psi$-dominated of level $\mu$ ([cartis2022evaluation], (5.3.1)) if
$f(x) - f_* \le \kappa_\psi \psi(x)^\mu$. For $\psi = \|\nabla f\|$ and $\mu \in [1, 2]$ this is the
Polyak–Łojasiewicz (gradient domination) property. Section 5.3 of [cartis2022evaluation] analyses
two abstract classes of monotone methods with a success set $\mathcal{S}$. In the class
$\mathrm{AR}_{\psi,\nu}$, successful iterations decrease $f$ by at least
$\kappa_\nu \psi(x_{k+1})^\nu$ (5.3.5), unsuccessful iterations keep the iterate, and the successes
are dense, $k \le \kappa_R |\mathcal{S}_k| + \kappa_A$ (5.3.9). The class $\mathrm{TR}_{\psi,\nu}$
is the same with the decrease $\kappa_\nu (\min_{i \le k} \psi(x_i))^\nu$ (5.3.28).

Runs are infinite sequences, and domination is required only at the iterates, as
[cartis2022evaluation] remarks after Lemma 5.3.1. The gap $\Gamma_k = f(x_k) - f_*$ then satisfies
the scalar recurrences `Optimization.IsImplicitGapDecrease` and `Optimization.IsExplicitGapDecrease`
of `Numlib.Optimization.Complexity.GapRecurrence` with $c = \kappa_\nu / \kappa_\psi^{\nu/\mu}$ and
$\tau = \nu / \mu$, and all rates and counts of §5.3 follow from these recurrences. The module also
shows that ARp runs belong to $\mathrm{AR}_{\psi,\nu}$, and gives concrete members of both classes.

## Main definitions

* `Optimization.IsMeasureDominated`: $f_* \le f(x)$ and $f(x) - f_* \le \kappa_\psi \psi(x)^\mu$ for
  $x \in A$.
* `Optimization.IsARLikeRun`: the class $\mathrm{AR}_{\psi,\nu}$.
* `Optimization.IsTRLikeRun`: the class $\mathrm{TR}_{\psi,\nu}$.
* `Optimization.softplus`: the function $y \mapsto \log(1 + e^y)$.

## Main results

* `Optimization.isImplicitGapDecrease_of_isARLikeRun`: along an $\mathrm{AR}_{\psi,\nu}$ run of a
  dominated objective, the gap satisfies the implicit recurrence (5.3.11), as in the proof of Lemma
  5.3.1.
* `Optimization.isExplicitGapDecrease_of_isTRLikeRun`: along a $\mathrm{TR}_{\psi,\nu}$ run of a
  dominated objective, the gap satisfies the explicit recurrence (5.3.33), as in the proof of Lemma
  5.3.6.
* `Optimization.isARLikeRun_of_isARpRun`: an ARp run (Algorithm 4.1.1) without termination test is
  in $\mathrm{AR}_{\psi,\nu}$ for the first-order measure (5.3.6).
* `Optimization.isARLikeRun_of_isARpRun_curvature`: if $q \ge 2$, it is also in
  $\mathrm{AR}_{\psi,\nu}$ for the second-order measure (5.3.7).
* `Optimization.exists_isARpRun_softplus`: for $f(y) = \log(1 + e^y)$ there is an ARp run that is
  AR-like, along which $f$ is dominated and the gap satisfies the implicit recurrence.
* `Optimization.isTRLikeRun_halving`: the gradient method with step $1/4$ on $f(y) = y^2$ is in
  $\mathrm{TR}_{\psi,\nu}$.

## Implementation notes

* The classes describe infinite runs, so the ARp run in `Optimization.isARLikeRun_of_isARpRun` has
  no termination test. A run without termination exists only if an admissible step exists at every
  iterate. For $q = 1$ this requires $\nabla f(x_k) \neq 0$ along the run
  (`Optimization.exists_isARpRun`), since an iterate at an exact critical point stops the method.
  Therefore the example uses a function without critical points: softplus has $f' > 0$, the value
  $f_* = 0$ is not attained, $f''$ is bounded, and softplus is dominated of level $1$ on its
  sublevel sets.
* The third-order measure (5.3.8) depends on the run through the set $\mathcal{M}_{k+1}$. It is not
  a function of the point, so it is not covered.
* No result places TR1 or TR2 runs in $\mathrm{TR}_{\psi,\nu}$. The density constant of Lemma 2.3.1
  involves $\log \Delta_{\min}$, where $\Delta_{\min}$ is proportional to a lower bound on the
  gradient along the run. So this constant is not uniform unless the gradient stays bounded away
  from zero, and in that case $f$ cannot be dominated with $f_* = \inf f$, so the gap analysis does
  not apply. `Optimization.isTRLikeRun_halving` gives a member of the class instead.
-/

open Finset
open scoped Nat

namespace Optimization

section Defs

variable {E : Type*}

/-- Let $f, \psi \colon E \to \mathbb{R}$, let $f_*, \mu, \kappa_\psi \in \mathbb{R}$ and let
$A \subseteq E$. The function $f$ is **$\psi$-dominated of level $\mu$** on $A$ with constant
$\kappa_\psi$ and value $f_*$ if for every $x \in A$
$$f_* \le f(x) \quad\text{and}\quad f(x) - f_* \le \kappa_\psi \psi(x)^\mu.$$

This is (5.3.1) of [cartis2022evaluation] on a set. The global notion of [cartis2022evaluation]
is the case $A = E$ with $f_* = \inf_x f(x)$. The theorems below use domination only at the
iterates, that is, on a set $A$ that contains the range of the run. The power $\psi(x)^\mu$ is
the real power `Real.rpow`. -/
def IsMeasureDominated (f ψ : E → ℝ) (fstar μ κψ : ℝ) (A : Set E) : Prop :=
  ∀ x ∈ A, fstar ≤ f x ∧ f x - fstar ≤ κψ * ψ x ^ μ

/-- Let $f, \psi \colon E \to \mathbb{R}$, let $\kappa_\nu, \nu, \kappa_R, \kappa_A \in \mathbb{R}$,
let $x \colon \mathbb{N} \to E$ be a run and let $S$ be its success predicate. The run is in the
**class $\mathrm{AR}_{\psi,\nu}$** of [cartis2022evaluation], §5.3.2, if
$$\kappa_\nu \psi(x_{k+1})^\nu \le f(x_k) - f(x_{k+1}) \quad \text{for every successful } k
  \qquad (5.3.5),$$
$x_{k+1} = x_k$ for every unsuccessful $k$, and the successful iterations are dense,
$$k \le \kappa_R |\mathcal{S}_k| + \kappa_A \quad \text{for every } k \qquad (5.3.9).$$

The standing assumptions $\kappa_\nu > 0$, $\nu \ge 1$, $\kappa_R \ge 1$, $\kappa_A \ge 0$ and
$\psi \ge 0$ of §5.3 are hypotheses of the theorems that need them. The density condition forces
$S$ to hold at infinitely many iterations. -/
structure IsARLikeRun (f ψ : E → ℝ) (κν ν κR κA : ℝ) (x : ℕ → E) (S : ℕ → Prop) : Prop where
  /-- The decrease (5.3.5) at the successful iterations: $\kappa_\nu \psi(x_{k+1})^\nu \le f(x_k) -
  f(x_{k+1})$. -/
  decrease : ∀ k, S k → κν * ψ (x (k + 1)) ^ ν ≤ f (x k) - f (x (k + 1))
  /-- Unsuccessful iterations keep the iterate: $x_{k+1} = x_k$. -/
  eq_of_not : ∀ k, ¬ S k → x (k + 1) = x k
  /-- The density (5.3.9) of the successful iterations: $k \le \kappa_R |\mathcal{S}_k| + \kappa_A$
  for every $k$. -/
  density : ∀ k : ℕ, (k : ℝ) ≤ κR * (successSet S k).card + κA

/-- Let $f, \psi \colon E \to \mathbb{R}$, let $\kappa_\nu, \nu, \kappa_R, \kappa_A \in \mathbb{R}$,
let $x \colon \mathbb{N} \to E$ be a run and let $S$ be its success predicate. The run is in the
**class $\mathrm{TR}_{\psi,\nu}$** of [cartis2022evaluation], §5.3.3, if
$$\kappa_\nu \Big( \min_{i \le k} \psi(x_i) \Big)^\nu \le f(x_k) - f(x_{k+1}) \quad \text{for
  every successful } k \qquad (5.3.28),$$
$x_{k+1} = x_k$ for every unsuccessful $k$, and the successful iterations are dense,
$k \le \kappa_R |\mathcal{S}_k| + \kappa_A$ for every $k$ (5.3.9).

The method need not stop when $\psi(x_k) = 0$: the decrease condition then asks only for a
nonnegative decrease. -/
structure IsTRLikeRun (f ψ : E → ℝ) (κν ν κR κA : ℝ) (x : ℕ → E) (S : ℕ → Prop) : Prop where
  /-- The decrease (5.3.28) at the successful iterations: $\kappa_\nu (\min_{i \le k} \psi(x_i))^\nu
  \le f(x_k) - f(x_{k+1})$. -/
  decrease : ∀ k, S k → κν * ((range (k + 1)).inf' nonempty_range_add_one (ψ ∘ x)) ^ ν ≤
    f (x k) - f (x (k + 1))
  /-- Unsuccessful iterations keep the iterate: $x_{k+1} = x_k$. -/
  eq_of_not : ∀ k, ¬ S k → x (k + 1) = x k
  /-- The density (5.3.9) of the successful iterations: $k \le \kappa_R |\mathcal{S}_k| + \kappa_A$
  for every $k$. -/
  density : ∀ k : ℕ, (k : ℝ) ≤ κR * (successSet S k).card + κA

variable {f ψ : E → ℝ} {fstar μ κψ : ℝ} {A A' : Set E}

/-- If $f$ is $\psi$-dominated on $A$ with value $f_*$, then $f_* \le f(x)$ for every $x \in A$. -/
theorem IsMeasureDominated.le (h : IsMeasureDominated f ψ fstar μ κψ A) {x : E} (hx : x ∈ A) :
    fstar ≤ f x :=
  (h x hx).1

/-- If $f$ is $\psi$-dominated of level $\mu$ on $A$ with constant $\kappa_\psi$ and value $f_*$,
then $f(x) - f_* \le \kappa_\psi \psi(x)^\mu$ for every $x \in A$; this is the inequality
(5.3.1). -/
theorem IsMeasureDominated.sub_le (h : IsMeasureDominated f ψ fstar μ κψ A) {x : E}
    (hx : x ∈ A) : f x - fstar ≤ κψ * ψ x ^ μ :=
  (h x hx).2

/-- Let $f, \psi \colon E \to \mathbb{R}$ and $A' \subseteq A \subseteq E$. If $f$ is
$\psi$-dominated of level $\mu$ on $A$ with constant $\kappa_\psi$ and value $f_*$, then $f$ is
$\psi$-dominated of level $\mu$ on $A'$ with the same constant and value. -/
theorem IsMeasureDominated.mono (h : IsMeasureDominated f ψ fstar μ κψ A) (hA : A' ⊆ A) :
    IsMeasureDominated f ψ fstar μ κψ A' :=
  fun x hx => h x (hA hx)

/-- Let $f, \psi \colon E \to \mathbb{R}$. The function $f$ is $\psi$-dominated of level $\mu$ on
all of $E$ with constant $\kappa_\psi$ and value $f_*$ if and only if for every $x \in E$
$$f_* \le f(x) \quad\text{and}\quad f(x) - f_* \le \kappa_\psi \psi(x)^\mu.$$
This is the global domination (5.3.1) of [cartis2022evaluation]. -/
theorem isMeasureDominated_univ_iff :
    IsMeasureDominated f ψ fstar μ κψ Set.univ ↔
      ∀ x, fstar ≤ f x ∧ f x - fstar ≤ κψ * ψ x ^ μ := by
  simp [IsMeasureDominated]

/-- If $f$ is $\psi$-dominated on all of $E$, then it is $\psi$-dominated, with the same level,
constant and value, on the range of every sequence $x \colon \mathbb{N} \to E$. -/
theorem IsMeasureDominated.range (h : IsMeasureDominated f ψ fstar μ κψ Set.univ) (x : ℕ → E) :
    IsMeasureDominated f ψ fstar μ κψ (Set.range x) :=
  h.mono (Set.subset_univ _)

end Defs

section Gap

variable {E : Type*} {f ψ : E → ℝ} {fstar μ κψ κν ν κR κA : ℝ} {x : ℕ → E} {S : ℕ → Prop}

/-- Domination turns a power of the measure into a power of the gap. Let $f$ be $\psi$-dominated of
level $\mu$ on $A$ with constant $\kappa_\psi > 0$ and value $f_*$, let $\mu > 0$ and
$\nu \ge 0$, and let $y \in A$ with $\psi(y) \ge 0$. Then
$$\frac{(f(y) - f_*)^{\nu/\mu}}{\kappa_\psi^{\nu/\mu}} \le \psi(y)^\nu.$$
-/
theorem div_rpow_le_rpow_of_isMeasureDominated {A : Set E}
    (hdom : IsMeasureDominated f ψ fstar μ κψ A) {y : E} (hy : y ∈ A) (hψ : 0 ≤ ψ y)
    (hκψ : 0 < κψ) (hμ : 0 < μ) (hν : 0 ≤ ν) :
    (f y - fstar) ^ (ν / μ) / κψ ^ (ν / μ) ≤ ψ y ^ ν := by
  have hg : 0 ≤ f y - fstar := sub_nonneg.2 (hdom.le hy)
  rw [← Real.div_rpow hg hκψ.le]
  have hle : (f y - fstar) / κψ ≤ ψ y ^ μ := by
    rw [div_le_iff₀ hκψ]; linarith [hdom.sub_le hy]
  calc ((f y - fstar) / κψ) ^ (ν / μ) ≤ (ψ y ^ μ) ^ (ν / μ) :=
        Real.rpow_le_rpow (div_nonneg hg hκψ.le) hle (div_nonneg hν hμ.le)
    _ = ψ y ^ ν := by
        rw [← Real.rpow_mul hψ, mul_div_cancel₀ _ hμ.ne']

/-- If $x$ is an $\mathrm{AR}_{\psi,\nu}$ run with $\kappa_\nu \ge 0$ and $\psi \ge 0$ everywhere,
then $f(x_{k+1}) \le f(x_k)$ for every $k$. -/
theorem IsARLikeRun.objective_succ_le (h : IsARLikeRun f ψ κν ν κR κA x S)
    (hψ : ∀ y, 0 ≤ ψ y) (hκν : 0 ≤ κν) (k : ℕ) : f (x (k + 1)) ≤ f (x k) := by
  by_cases hk : S k
  · have := h.decrease k hk
    have : 0 ≤ κν * ψ (x (k + 1)) ^ ν := mul_nonneg hκν (Real.rpow_nonneg (hψ _) _)
    linarith
  · rw [h.eq_of_not k hk]

/-- If $x$ is an $\mathrm{AR}_{\psi,\nu}$ run with $\kappa_\nu \ge 0$ and $\psi \ge 0$ everywhere,
then the sequence $k \mapsto f(x_k)$ is antitone. -/
theorem IsARLikeRun.objective_antitone (h : IsARLikeRun f ψ κν ν κR κA x S)
    (hψ : ∀ y, 0 ≤ ψ y) (hκν : 0 ≤ κν) : Antitone fun k => f (x k) :=
  antitone_nat_of_succ_le (h.objective_succ_le hψ hκν)

/-- Let $f, \psi \colon E \to \mathbb{R}$ with $\psi \ge 0$ everywhere, and let $x$ be an
$\mathrm{AR}_{\psi,\nu}$ run with success predicate $S$ and constants $\kappa_\nu \ge 0$ and
$\nu \ge 0$. Let $\kappa_\psi > 0$ and $\mu > 0$, and let $f$ be $\psi$-dominated of level $\mu$
on the range of $x$ with constant $\kappa_\psi$ and value $f_*$. Then the gap
$\Gamma_k = f(x_k) - f_*$ satisfies the implicit recurrence (5.3.11) with
$c = \kappa_\nu / \kappa_\psi^{\nu/\mu}$ and $\tau = \nu / \mu$: $\Gamma_k \ge 0$ for every $k$,
$\Gamma_{k+1} = \Gamma_k$ at the unsuccessful iterations, and
$$\frac{\kappa_\nu}{\kappa_\psi^{\nu/\mu}} \Gamma_{k+1}^{\nu/\mu} \le \Gamma_k - \Gamma_{k+1}$$
at the successful iterations.

This is (5.3.11) in the proof of Lemma 5.3.1 of [cartis2022evaluation]. Of the conditions on
$\mu$ in [cartis2022evaluation], only $\mu > 0$ is used. -/
theorem isImplicitGapDecrease_of_isARLikeRun (h : IsARLikeRun f ψ κν ν κR κA x S)
    (hψ : ∀ y, 0 ≤ ψ y) (hκψ : 0 < κψ) (hμ : 0 < μ) (hκν : 0 ≤ κν) (hν : 0 ≤ ν)
    (hdom : IsMeasureDominated f ψ fstar μ κψ (Set.range x)) :
    IsImplicitGapDecrease (fun k => f (x k) - fstar) S (κν / κψ ^ (ν / μ)) (ν / μ) where
  nonneg k := sub_nonneg.2 (hdom.le ⟨k, rfl⟩)
  eq_of_not k hk := by simp only [h.eq_of_not k hk]
  decrease k hk := by
    have h1 := div_rpow_le_rpow_of_isMeasureDominated hdom ⟨k + 1, rfl⟩ (hψ _) hκψ hμ hν
    have h2 := h.decrease k hk
    calc κν / κψ ^ (ν / μ) * (f (x (k + 1)) - fstar) ^ (ν / μ)
        = κν * ((f (x (k + 1)) - fstar) ^ (ν / μ) / κψ ^ (ν / μ)) := by ring
      _ ≤ κν * ψ (x (k + 1)) ^ ν := mul_le_mul_of_nonneg_left h1 hκν
      _ ≤ _ := by linarith

/-- If $x$ is a $\mathrm{TR}_{\psi,\nu}$ run with $\kappa_\nu \ge 0$ and $\psi \ge 0$ everywhere,
then $f(x_{k+1}) \le f(x_k)$ for every $k$. -/
theorem IsTRLikeRun.objective_succ_le (h : IsTRLikeRun f ψ κν ν κR κA x S)
    (hψ : ∀ y, 0 ≤ ψ y) (hκν : 0 ≤ κν) (k : ℕ) : f (x (k + 1)) ≤ f (x k) := by
  by_cases hk : S k
  · have := h.decrease k hk
    have : 0 ≤ κν * ((range (k + 1)).inf' nonempty_range_add_one (ψ ∘ x)) ^ ν :=
      mul_nonneg hκν (Real.rpow_nonneg ((le_inf'_iff _ _).2 fun i _ => hψ _) _)
    linarith
  · rw [h.eq_of_not k hk]

/-- Let $f, \psi \colon E \to \mathbb{R}$ with $\psi \ge 0$ everywhere, and let $x$ be a
$\mathrm{TR}_{\psi,\nu}$ run with success predicate $S$ and constants $\kappa_\nu \ge 0$ and
$\nu \ge 0$. Let $\kappa_\psi > 0$ and $\mu > 0$, and let $f$ be $\psi$-dominated of level $\mu$
on the range of $x$ with constant $\kappa_\psi$ and value $f_*$. Then the gap
$\Gamma_k = f(x_k) - f_*$ satisfies the explicit recurrence (5.3.33) with
$c = \kappa_\nu / \kappa_\psi^{\nu/\mu}$ and $\tau = \nu / \mu$: $\Gamma_k \ge 0$ for every $k$,
$\Gamma_{k+1} = \Gamma_k$ at the unsuccessful iterations, and
$$\frac{\kappa_\nu}{\kappa_\psi^{\nu/\mu}} \Gamma_k^{\nu/\mu} \le \Gamma_k - \Gamma_{k+1}$$
at the successful iterations.

This is (5.3.33) in the proof of Lemma 5.3.6 of [cartis2022evaluation]. The proof applies
domination at the earlier iterate that minimizes $\psi$, and then uses that $\Gamma$ is
nonincreasing. Of the conditions on $\mu$ in [cartis2022evaluation], only $\mu > 0$ is used. -/
theorem isExplicitGapDecrease_of_isTRLikeRun (h : IsTRLikeRun f ψ κν ν κR κA x S)
    (hψ : ∀ y, 0 ≤ ψ y) (hκψ : 0 < κψ) (hμ : 0 < μ) (hκν : 0 ≤ κν) (hν : 0 ≤ ν)
    (hdom : IsMeasureDominated f ψ fstar μ κψ (Set.range x)) :
    IsExplicitGapDecrease (fun k => f (x k) - fstar) S (κν / κψ ^ (ν / μ)) (ν / μ) where
  nonneg k := sub_nonneg.2 (hdom.le ⟨k, rfl⟩)
  eq_of_not k hk := by simp only [h.eq_of_not k hk]
  decrease k hk := by
    obtain ⟨i, hi, hieq⟩ := exists_mem_eq_inf' (nonempty_range_add_one (n := k)) (ψ ∘ x)
    have hik : i ≤ k := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have hanti : Antitone (fun k => f (x k)) :=
      antitone_nat_of_succ_le (h.objective_succ_le hψ hκν)
    have h1 := div_rpow_le_rpow_of_isMeasureDominated hdom ⟨i, rfl⟩ (hψ _) hκψ hμ hν
    have h2 := h.decrease k hk
    rw [hieq] at h2
    have hgk : 0 ≤ f (x k) - fstar := sub_nonneg.2 (hdom.le ⟨k, rfl⟩)
    have h3 : (f (x k) - fstar) ^ (ν / μ) ≤ (f (x i) - fstar) ^ (ν / μ) :=
      Real.rpow_le_rpow hgk (by linarith [hanti hik]) (div_nonneg hν hμ.le)
    calc κν / κψ ^ (ν / μ) * (f (x k) - fstar) ^ (ν / μ)
        = κν * ((f (x k) - fstar) ^ (ν / μ) / κψ ^ (ν / μ)) := by ring
      _ ≤ κν * ((f (x i) - fstar) ^ (ν / μ) / κψ ^ (ν / μ)) := by
          gcongr
      _ ≤ κν * ψ (x i) ^ ν := mul_le_mul_of_nonneg_left h1 hκν
      _ ≤ _ := by simpa using h2

end Gap

section ARp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} {p q : ℕ}
  {P : ARpParams} {x s : ℕ → E} {σ : ℕ → ℝ} {L : ℝ}

/-- **ARp is in $\mathrm{AR}_{\psi,\nu}$ for the first-order measure.** Let $E$ be a real inner
product space, let $p \ge 1$ and $q \le p$, and let $f \colon E \to \mathbb{R}$ be of class
$C^p$ with $\nabla^p f$ Lipschitz continuous on $E$ with constant $L \ge 0$. Let
$(x, s, \sigma)$ be a run of the ARp method (Algorithm 4.1.1 of [cartis2022evaluation]) of order
$q$ with the constants $P$ and without termination test. Then $x$ is in $\mathrm{AR}_{\psi,\nu}$
for the measure $\psi = \|\nabla f\|$ and the success predicate $\eta_1 \le \rho_k$, where
$\rho_k$ is the Taylor ratio (4.1.15), with
$$\nu = \frac{p + 1}{p}, \qquad \kappa_\nu = \frac{\eta_1 \sigma_{\min}}{(p + 1)!} \left(
  \frac{p!}{L + \sigma_{\max} + \theta_1 p!} \right)^{(p+1)/p},$$
$$\kappa_R = 1 + \frac{|\log \gamma_1|}{\log \gamma_2}, \qquad \kappa_A =
  \frac{\log(\sigma_{\max} / \sigma_0)}{\log \gamma_2},$$
where $\sigma_{\max} = \max(\sigma_0, \gamma_3 L / (1 - \eta_2))$ is the bound (4.1.19) and
$\kappa_\nu$ is the constant $\kappa_1$ of (4.1.32).

This gives (5.3.6) and (5.3.9) of [cartis2022evaluation], which remarks that "these properties
are obviously satisfied by the ARp algorithm". The run is `Optimization.IsARpRun` with a
termination test that never holds, and $\sigma_{\max}$ is `Optimization.arSigmaMax`. Such runs
exist only if no iterate is a critical point; see the module documentation and
`Optimization.exists_isARpRun_softplus`. -/
theorem isARLikeRun_of_isARpRun (h : IsARpRun f p P q (fun _ => False) x s σ)
    (hf : ContDiff ℝ p f) (hL : IteratedFDerivLipschitzOn f p L Set.univ) (hL0 : 0 ≤ L)
    (hp : 1 ≤ p) (hqp : q ≤ p) :
    IsARLikeRun f (fun y => ‖fderiv ℝ f y‖)
      (P.η₁ * P.σmin / ((p + 1)! : ℝ) *
        ((p ! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₁ * p !)) ^ (((p : ℝ) + 1) / p))
      (((p : ℝ) + 1) / p) (1 + |Real.log P.γ₁| / Real.log P.γ₂)
      (Real.log (arSigmaMax P.toARParams L / P.σ₀) / Real.log P.γ₂) x
      (fun k => P.η₁ ≤ taylorRatio f p x s k) where
  decrease k hk := (h.decrease_ge hf hL hL0 hp hqp (by simp) hk).2.1
  eq_of_not k hk := h.eq_of_not_succ (by simp) hk
  density k := h.density hf hL (by simp)

/-- **ARp is in $\mathrm{AR}_{\psi,\nu}$ for the second-order measure.** Let $E$ be a real inner
product space, let $p \ge 1$ and $2 \le q \le p$, and let $f \colon E \to \mathbb{R}$ be of
class $C^p$ with $\nabla^p f$ Lipschitz continuous on $E$ with constant $L \ge 0$. Let
$(x, s, \sigma)$ be a run of the ARp method of order $q$ with the constants $P$ and without
termination test. Then $x$ is in $\mathrm{AR}_{\psi,\nu}$ for the measure $\psi_2(y) = \max(0,
-\lambda_{\min}(\nabla^2 f(y)))$ and the success predicate $\eta_1 \le \rho_k$, with
$$\nu = \frac{p + 1}{p - 1}, \qquad \kappa_\nu = \frac{\eta_1 \sigma_{\min}}{(p + 1)!} \left(
  \frac{(p - 1)!}{L + \sigma_{\max} + \theta_2 (p - 1)!} \right)^{(p+1)/(p-1)},$$
and with $\kappa_R$, $\kappa_A$ and $\sigma_{\max}$ as in
`Optimization.isARLikeRun_of_isARpRun`. Here $\kappa_\nu$ is the constant $\kappa_2$ of
(4.1.34).

This gives (5.3.7) of [cartis2022evaluation]. The number $\lambda_{\min}$ is `minCurvature`. -/
theorem isARLikeRun_of_isARpRun_curvature (h : IsARpRun f p P q (fun _ => False) x s σ)
    (hf : ContDiff ℝ p f) (hL : IteratedFDerivLipschitzOn f p L Set.univ) (hL0 : 0 ≤ L)
    (hp : 1 ≤ p) (hqp : q ≤ p) (hq : 2 ≤ q) :
    IsARLikeRun f (fun y => max 0 (-minCurvature (iteratedFDeriv ℝ 2 f y)))
      (P.η₁ * P.σmin / ((p + 1)! : ℝ) *
        (((p - 1)! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!)) ^
          (((p : ℝ) + 1) / ((p : ℝ) - 1)))
      (((p : ℝ) + 1) / ((p : ℝ) - 1)) (1 + |Real.log P.γ₁| / Real.log P.γ₂)
      (Real.log (arSigmaMax P.toARParams L / P.σ₀) / Real.log P.γ₂) x
      (fun k => P.η₁ ≤ taylorRatio f p x s k) where
  decrease k hk := (h.decrease_ge hf hL hL0 hp hqp (by simp) hk).2.2.1 hq
  eq_of_not k hk := h.eq_of_not_succ (by simp) hk
  density k := h.density hf hL (by simp)

end ARp

/-! ### Examples -/

section Softplus

/-- The **softplus function** $y \mapsto \log(1 + e^y)$ on $\mathbb{R}$. Its derivative is positive
everywhere, its infimum $0$ is not attained, and its second derivative is bounded. -/
noncomputable def softplus (y : ℝ) : ℝ := Real.log (1 + Real.exp y)

private theorem one_add_exp_pos (y : ℝ) : 0 < 1 + Real.exp y := by positivity

/-- The derivative of softplus at $y$ is the logistic sigmoid $e^y / (1 + e^y)$. -/
theorem hasDerivAt_softplus (y : ℝ) :
    HasDerivAt softplus (Real.exp y / (1 + Real.exp y)) y :=
  ((Real.hasDerivAt_exp y).const_add 1).log (one_add_exp_pos y).ne'

/-- Softplus is $C^n$ for every smoothness order $n$, including $n = \infty$ and the analytic order.
-/
theorem contDiff_softplus {n : WithTop ℕ∞} : ContDiff ℝ n softplus :=
  (contDiff_const.add Real.contDiff_exp).log fun y => (one_add_exp_pos y).ne'

/-- The derivative of the logistic sigmoid $y \mapsto e^y / (1 + e^y)$ is
$(e^y (1 + e^y) - e^{2y}) / (1 + e^y)^2$. -/
private theorem hasDerivAt_sigmoid (y : ℝ) :
    HasDerivAt (fun y => Real.exp y / (1 + Real.exp y))
      ((Real.exp y * (1 + Real.exp y) - Real.exp y * Real.exp y) / (1 + Real.exp y) ^ 2) y :=
  (Real.hasDerivAt_exp y).div ((Real.hasDerivAt_exp y).const_add 1) (one_add_exp_pos y).ne'

/-- The Fréchet derivative of softplus at $y$ is the linear map $h \mapsto h \, e^y / (1 + e^y)$. -/
theorem fderiv_softplus (y : ℝ) :
    fderiv ℝ softplus y =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp y / (1 + Real.exp y)) :=
  (hasDerivAt_softplus y).hasFDerivAt.fderiv

/-- The norm of the derivative of softplus at $y$ is $e^y / (1 + e^y)$. -/
theorem norm_fderiv_softplus (y : ℝ) :
    ‖fderiv ℝ softplus y‖ = Real.exp y / (1 + Real.exp y) := by
  rw [fderiv_softplus, ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul,
    Real.norm_eq_abs, abs_of_pos (by have := one_add_exp_pos y; positivity)]

/-- Softplus has no critical point: its derivative is nonzero at every $y$. -/
theorem fderiv_softplus_ne_zero (y : ℝ) : fderiv ℝ softplus y ≠ 0 := by
  intro h
  have := norm_fderiv_softplus y
  rw [h, norm_zero] at this
  have : 0 < Real.exp y / (1 + Real.exp y) := by have := one_add_exp_pos y; positivity
  linarith

/-- The first derivative of softplus is Lipschitz continuous on $\mathbb{R}$ with constant $1$:
$$\|\nabla \mathrm{softplus}(x) - \nabla \mathrm{softplus}(y)\| \le |x - y| \quad \text{for all
  } x, y \in \mathbb{R}.$$
-/
theorem iteratedFDerivLipschitzOn_softplus :
    IteratedFDerivLipschitzOn softplus 1 1 Set.univ := by
  rw [iteratedFDerivLipschitzOn_iff]
  intro a _ b _
  rw [norm_iteratedFDeriv_one_sub, fderiv_softplus, fderiv_softplus]
  have hsub : ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp a / (1 + Real.exp a)) -
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp b / (1 + Real.exp b)) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (Real.exp a / (1 + Real.exp a) - Real.exp b / (1 + Real.exp b)) := by
    ext; simp
  rw [hsub, ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]
  refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hasDerivAt_sigmoid z).hasDerivWithinAt) (fun z _ => ?_) convex_univ
    (Set.mem_univ b) (Set.mem_univ a)
  have he := Real.exp_pos z
  rw [Real.norm_eq_abs, abs_le]
  have hd : 0 < (1 + Real.exp z) ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ hd]; nlinarith
  · rw [div_le_iff₀ hd]; nlinarith

/-- For every $c \in \mathbb{R}$, softplus is $\psi$-dominated of level $1$ on the sublevel set
$\{ y : \log(1 + e^y) \le c \}$, with $\psi(y) = \|\nabla \mathrm{softplus}(y)\| = e^y / (1 +
e^y)$, value $f_* = 0$ and constant $e^c$. That is, for every $y$ in the sublevel set,
$$0 \le \log(1 + e^y) \le e^c \frac{e^y}{1 + e^y}.$$

The proof is the chain $\log(1 + e^y) \le e^y = f'(y) (1 + e^y) \le e^c f'(y)$. -/
theorem isMeasureDominated_softplus (c : ℝ) :
    IsMeasureDominated softplus (fun y => ‖fderiv ℝ softplus y‖) 0 1 (Real.exp c)
      {y | softplus y ≤ c} := by
  intro y hy
  have h1 := one_add_exp_pos y
  refine ⟨Real.log_nonneg (by linarith [Real.exp_pos y]), ?_⟩
  rw [sub_zero, Real.rpow_one]
  simp only [norm_fderiv_softplus]
  have hle : softplus y ≤ Real.exp y := by
    have := Real.log_le_sub_one_of_pos h1
    simp only [softplus]; linarith
  have hc : 1 + Real.exp y ≤ Real.exp c := (Real.log_le_iff_le_exp h1).1 hy
  calc softplus y ≤ Real.exp y := hle
    _ = Real.exp y / (1 + Real.exp y) * (1 + Real.exp y) := by field_simp
    _ ≤ Real.exp y / (1 + Real.exp y) * Real.exp c := by gcongr
    _ = _ := mul_comm _ _

/-- **Non-vacuity of the results on ARp runs.** Let $P$ be constants of the ARp method with
$\sigma_{\min} > 0$, and let $x_0 \in \mathbb{R}$. Then there are sequences
$x, s, \sigma \colon \mathbb{N} \to \mathbb{R}$ with $x(0) = x_0$ that form a run of the ARp
method with $p = q = 1$ on softplus without termination test, and there are constants
$\kappa_\nu > 0$, $\kappa_R$ and $\kappa_A$, such that the following hold for the success
predicate $\eta_1 \le \rho_k$ and $\psi = \|\nabla \mathrm{softplus}\|$:
* $x$ is in $\mathrm{AR}_{\psi,\nu}$ with $\nu = 2$ and the constants $\kappa_\nu$, $\kappa_R$,
  $\kappa_A$;
* softplus is $\psi$-dominated of level $1$ on the range of $x$, with value $f_* = 0$ and
  constant $\kappa_\psi = e^{\mathrm{softplus}(x_0)}$;
* the gap $\Gamma_k = \mathrm{softplus}(x_k)$ satisfies the implicit recurrence (5.3.11) with
  $c = \kappa_\nu / (e^{\mathrm{softplus}(x_0)})^2$ and $\tau = 2$.

This shows that the results of §5.3.2 of [cartis2022evaluation] about ARp runs are not vacuous.
The run is infinite because softplus has no critical point. -/
theorem exists_isARpRun_softplus (P : ARpParams) (hσmin : 0 < P.σmin) (x₀ : ℝ) :
    ∃ x s σ : ℕ → ℝ, x 0 = x₀ ∧ IsARpRun softplus 1 P 1 (fun _ => False) x s σ ∧
      ∃ κν κR κA : ℝ, 0 < κν ∧
        IsARLikeRun softplus (fun y => ‖fderiv ℝ softplus y‖) κν 2 κR κA x
          (fun k => P.η₁ ≤ taylorRatio softplus 1 x s k) ∧
        IsMeasureDominated softplus (fun y => ‖fderiv ℝ softplus y‖) 0 1
          (Real.exp (softplus x₀)) (Set.range x) ∧
        IsImplicitGapDecrease (fun k => softplus (x k) - 0)
          (fun k => P.η₁ ≤ taylorRatio softplus 1 x s k) (κν / Real.exp (softplus x₀) ^ 2) 2 := by
  obtain ⟨x, s, σ, hx0, hrun⟩ := exists_isARpRun (f := softplus) (p := 1) (q := 1) P
    contDiff_softplus le_rfl (by omega) (by omega) (test := fun _ => False)
    (fun y _ => Or.inl (fderiv_softplus_ne_zero y)) x₀
  have hb := isARLikeRun_of_isARpRun hrun contDiff_softplus iteratedFDerivLipschitzOn_softplus
    zero_le_one le_rfl le_rfl
  have h2 : (((1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2] at hb
  set κν := P.η₁ * P.σmin / ((1 + 1)! : ℝ) *
    (((1 : ℕ)! : ℝ) / (1 + arSigmaMax P.toARParams 1 + P.θ₁ * ((1 : ℕ)! : ℝ))) ^ (2 : ℝ)
  have hκν : 0 < κν := by
    have := P.η₁_pos; have := arSigmaMax_pos P.toARParams 1; have := P.θ₁_pos
    positivity
  have hψ : ∀ y, 0 ≤ ‖fderiv ℝ softplus y‖ := fun _ => norm_nonneg _
  have hdom : IsMeasureDominated softplus (fun y => ‖fderiv ℝ softplus y‖) 0 1
      (Real.exp (softplus x₀)) (Set.range x) := by
    refine (isMeasureDominated_softplus (softplus x₀)).mono ?_
    rintro _ ⟨k, rfl⟩
    have := hb.objective_antitone hψ hκν.le (Nat.zero_le k)
    simp only [hx0] at this
    exact this
  have hgap := isImplicitGapDecrease_of_isARLikeRun hb hψ (Real.exp_pos _) one_pos hκν.le
    (by norm_num) hdom
  rw [div_one, Real.rpow_two] at hgap
  exact ⟨x, s, σ, hx0, hrun, κν, _, _, hκν, hb, hdom, hgap⟩

end Softplus

section Halving

/-- **A member of $\mathrm{TR}_{\psi,\nu}$.** For every $x_0 \in \mathbb{R}$, the sequence
$x_k = x_0 / 2^k$, with every iteration successful, is in $\mathrm{TR}_{\psi,\nu}$ for
$f(y) = y^2$ and $\psi(y) = |2y| = |f'(y)|$, with $\nu = 2$, $\kappa_\nu = 3/16$, $\kappa_R = 1$
and $\kappa_A = 0$.

The sequence is the gradient method with step $1/4$ on $f$, as in §5.3.3 of
[cartis2022evaluation]. Since $f$ is dominated of level $\mu = 2$ with $\kappa_\psi = 1/4$
(`Optimization.isMeasureDominated_sq`), the explicit recurrence (5.3.33) holds with $c = 3/4$
and $\tau = 1$. -/
theorem isTRLikeRun_halving (x₀ : ℝ) :
    IsTRLikeRun (fun y : ℝ => y ^ 2) (fun y => |2 * y|) (3 / 16) 2 1 0
      (fun k => x₀ / 2 ^ k) (fun _ => True) where
  decrease k _ := by
    set m := (range (k + 1)).inf' nonempty_range_add_one ((fun y : ℝ => |2 * y|) ∘
      fun k => x₀ / 2 ^ k)
    have hm0 : 0 ≤ m := (le_inf'_iff _ _).2 fun _ _ => abs_nonneg _
    have hmk : m ≤ |2 * (x₀ / 2 ^ k)| :=
      inf'_le _ (mem_range.2 (Nat.lt_succ_self k))
    have h2 : m ^ (2 : ℝ) ≤ |2 * (x₀ / 2 ^ k)| ^ (2 : ℝ) :=
      Real.rpow_le_rpow hm0 hmk (by norm_num)
    rw [Real.rpow_two, Real.rpow_two, sq_abs] at h2
    have e : (x₀ / 2 ^ k) ^ 2 - (x₀ / 2 ^ (k + 1)) ^ 2 = 3 / 16 * (2 * (x₀ / 2 ^ k)) ^ 2 := by
      rw [pow_succ]; ring
    rw [e, Real.rpow_two]
    gcongr
  eq_of_not _ h := absurd trivial h
  density k := by
    have : (successSet (fun _ => True) k).card = k + 1 := by simp [successSet]
    rw [this]; push_cast; linarith

/-- The function $f(y) = y^2$ on $\mathbb{R}$ is $\psi$-dominated of level $2$ on all of
$\mathbb{R}$ for $\psi(y) = |2y|$, with constant $1/4$ and value $f_* = 0$: for every $y$,
$$0 \le y^2 \le \tfrac{1}{4} |2y|^2.$$
-/
theorem isMeasureDominated_sq :
    IsMeasureDominated (fun y : ℝ => y ^ 2) (fun y => |2 * y|) 0 2 (1 / 4) Set.univ :=
  fun y _ => ⟨sq_nonneg y, by rw [Real.rpow_two, sq_abs]; ring_nf; rfl⟩

end Halving

end Optimization
