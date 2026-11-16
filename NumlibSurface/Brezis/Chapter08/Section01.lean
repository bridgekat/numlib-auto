/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Variational.EllipticInterval.BoundaryConditions

/-!
# Brezis, Section 8.1: Motivation

This module formalizes Section 8.1 of [brezis2011functional], which motivates the variational method
on the model Dirichlet problem (1),
$$-u'' + u = f \text{ on } [a, b], \qquad u(a) = u(b) = 0,$$
for a given $f \in C([a, b])$. A classical solution is a function $u \in C^2([a, b])$ that satisfies
(1). The provisional weak solution of the section is a function $u \in C^1([a, b])$ with the
property (2),
$$\int_a^b u' \varphi' + \int_a^b u \varphi = \int_a^b f \varphi \quad \text{for all } \varphi \in
  C^1([a, b]) \text{ with } \varphi(a) = \varphi(b) = 0.$$
The variational method has four steps. Step A: a classical solution is a weak solution (multiply (1)
by $\varphi$ and integrate by parts). Step B: a weak solution exists and is unique, by the
Lax–Milgram theorem in the completion $H_0^1$ of the $C^1$ functions that vanish at the endpoints.
Step C: the weak solution is $C^2$. Step D: a $C^2$ weak solution is a classical solution. The
section carries out Step D and leaves the other steps to Sections 8.2–8.4. It has no numbered
result.

Step D specializes `EllipticInterval.isClassicalSolution_of_forall_testFunction` of the backbone
module `Numlib.Variational.EllipticInterval.BoundaryConditions`.

## Main definitions

* Section 8.1, definition of a classical solution, `Brezis.Chapter08.IsClassicalSolution`:
  $u \in C^2([a, b])$ satisfies (1).
* Section 8.1, definition of a weak solution, `Brezis.Chapter08.IsWeakSolution`: $u \in C^1([a, b])$
  satisfies (2).

## Main results

* Section 8.1, Step D, `Brezis.Chapter08.dirichlet_stepD`: if $f$ is continuous and
  $u \in C^2([a, b])$ with $u(a) = u(b) = 0$ satisfies (2), then $u$ is a classical solution.

## Proof outline

Step D in the source integrates (2) by parts against a $C^1$ test function. The proof here restricts
(2) to the smooth test functions $\mathcal{D}((a, b))$, which are $C^1$ and vanish at the endpoints.
Then $-(u')' = f - u$ holds in the weak sense on $(a, b)$, hence almost everywhere by the
fundamental lemma of the calculus of variations, and hence everywhere on $(a, b)$ by continuity. The
identity extends to the endpoints by continuity (`eqOn_Icc_of_ae_eq`).

## Conventions

* The space $C^k([a, b])$ is `ContDiffMapIcc hab.le k` of the module
  `Numlib.Analysis.Calculus.ContDiffMapIcc`. An element is the tuple $(u, u', \dots, u^{(k)})$ of
  continuous functions on $[a, b]$, and `ContDiffMapIcc.deriv u j` is $u^{(j)}$.
* Integrals over $[a, b]$ are interval integrals of `ContDiffMapIcc.extend`, the extension of a
  function on $[a, b]$ to `ℝ` that is constant outside $[a, b]$.

## Implementation notes

* The definitive weak solution, in $H_0^1$, is the one of Section 8.4. The steps of the variational
  method for the general problem $-(\alpha u')' + \beta u' + \gamma u = f$ are backbone results:
  Step A is `EllipticInterval.isWeakSolution_of_classical`, Step B is
  `EllipticInterval.existsUnique_isWeakSolution` (its case for the model problem is Proposition 8.15
  of the source, `Brezis.Chapter08.proposition_8_15`), Step C is
  `EllipticInterval.mem_sobolevInterval_two_of_forall_testFunction` together with
  `EllipticInterval.exists_contDiffMapIcc_of_continuous`, and Step D is
  `EllipticInterval.isClassicalSolution_of_contDiffMapIcc`.
-/

open Set MeasureTheory TopologicalSpace intervalIntegral
open scoped Distributions

noncomputable section

namespace Brezis.Chapter08

variable {a b : ℝ}

/-!
### The inclusion $C^l([a, b]) \to C^k([a, b])$

The module `Numlib.Analysis.Calculus.ContDiffMapIcc` has the differentiation map $C^{k+1} \to C^k$
(`ContDiffMapIcc.shift`) but not the inclusion. A $C^2$ function is read as a $C^1$ function through
`ContDiffMapIcc.castLE`, which keeps the first $k$ derivatives of the tuple.
-/

/-- The inclusion $C^l([a, b]) \to C^k([a, b])$ for $k \le l$: it maps $u$ to the same function with
its first $k$ derivatives, $(u, u', \dots, u^{(k)})$. -/
def _root_.ContDiffMapIcc.castLE {hab : a ≤ b} {k l : ℕ} (h : k ≤ l)
    (u : ContDiffMapIcc hab l) : ContDiffMapIcc hab k :=
  ContDiffMapIcc.mk hab (fun j ↦ u.deriv (Fin.castLE (Nat.succ_le_succ h) j)) fun j ↦
    u.hasDerivIcc (Fin.castLE h j)

/-- The derivatives of the image of $u$ under the inclusion $C^l([a, b]) \to C^k([a, b])$ are the
derivatives of $u$: the $j$-th derivative is $u^{(j)}$ for $j \le k$. -/
@[simp]
theorem _root_.ContDiffMapIcc.deriv_castLE {hab : a ≤ b} {k l : ℕ} (h : k ≤ l)
    (u : ContDiffMapIcc hab l) (j : Fin (k + 1)) :
    (u.castLE h).deriv j = u.deriv (Fin.castLE (Nat.succ_le_succ h) j) := rfl

/-- The inclusion $C^l([a, b]) \to C^k([a, b])$ does not change the function: the extensions of $u$
and of its image to `ℝ` are equal. -/
theorem _root_.ContDiffMapIcc.castLE_extend {hab : a ≤ b} {k l : ℕ} (h : k ≤ l)
    (u : ContDiffMapIcc hab l) : (u.castLE h).extend = u.extend := rfl

/-- The inclusion $C^2([a, b]) \to C^1([a, b])$ does not change the derivative: the extensions of
$u'$ and of the derivative of the image of $u$ to `ℝ` are equal. -/
theorem _root_.ContDiffMapIcc.castLE_shift_extend {hab : a ≤ b} (u : ContDiffMapIcc hab 2) :
    (u.castLE one_le_two).shift.extend = u.shift.extend := rfl

/-! ### The definitions -/

/-- **Section 8.1** of [brezis2011functional], definition of a classical solution. Let $a < b$ and
$f : \mathbb{R} \to \mathbb{R}$. A **classical** (or strong) solution of problem (1) is a
function $u \in C^2([a, b])$ with
$$-u''(x) + u(x) = f(x) \quad \text{for all } x \in [a, b], \qquad u(a) = u(b) = 0.$$

The second derivative $u''$ on $[a, b]$, with one-sided derivatives at the endpoints, is
`ContDiffMapIcc.deriv u 2`. -/
def IsClassicalSolution (hab : a < b) (f : ℝ → ℝ) (u : ContDiffMapIcc hab.le 2) : Prop :=
  (∀ x : Icc a b, -u.deriv 2 x + u x = f x) ∧
    u ⟨a, left_mem_Icc.2 hab.le⟩ = 0 ∧ u ⟨b, right_mem_Icc.2 hab.le⟩ = 0

/-- **Section 8.1** of [brezis2011functional], definition of a weak solution. Let $a < b$ and
$f : \mathbb{R} \to \mathbb{R}$. A function $u \in C^1([a, b])$ is a **weak solution** of
problem (1) if it satisfies (2):
$$\int_a^b u' \varphi' + \int_a^b u \varphi = \int_a^b f \varphi \quad \text{for every } \varphi
  \in C^1([a, b]) \text{ with } \varphi(a) = \varphi(b) = 0.$$

This is the provisional weak solution of the section. The source notes that (2) makes sense as
soon as $u, u' \in L^1$, which leads to Section 8.2. The definitive weak solution, in $H_0^1$,
is the one of Section 8.4, `Brezis.Chapter08.IsWeakSolutionDirichlet`. The function $f$ is
arbitrary here; Step D assumes it continuous on $[a, b]$. -/
def IsWeakSolution (hab : a < b) (f : ℝ → ℝ) (u : ContDiffMapIcc hab.le 1) : Prop :=
  ∀ φ : ContDiffMapIcc hab.le 1, φ ⟨a, left_mem_Icc.2 hab.le⟩ = 0 →
    φ ⟨b, right_mem_Icc.2 hab.le⟩ = 0 →
    (∫ x in a..b, u.shift.extend x * φ.shift.extend x) + ∫ x in a..b, u.extend x * φ.extend x
      = ∫ x in a..b, f x * φ.extend x

/-! ### Step D -/

/-- Let $a < b$ and $u \in C^2([a, b])$. At every interior point $x \in (a, b)$, the derivative of
$u'$ is $u''(x)$.

Here $u'$ is read through its extension to `ℝ`. -/
theorem deriv_shift_extend (hab : a < b) (u : ContDiffMapIcc hab.le 2) {x : ℝ}
    (hx : x ∈ Ioo a b) : deriv u.shift.extend x = u.deriv 2 ⟨x, Ioo_subset_Icc_self hx⟩ :=
  ((u.shift.hasDerivWithinAt_extend ⟨x, Ioo_subset_Icc_self hx⟩).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)).deriv

/-- Let $a < b$, $f : \mathbb{R} \to \mathbb{R}$, and let $u \in C^2([a, b])$ be a weak solution of
problem (1), read as an element of $C^1([a, b])$. Then for every smooth test function
$\varphi \in \mathcal{D}((a, b))$,
$$\int_{(a, b)} (u' \varphi' + u \varphi) = \int_{(a, b)} f \varphi.$$
-/
theorem integral_eq_of_isWeakSolution (hab : a < b) {f : ℝ → ℝ} (u : ContDiffMapIcc hab.le 2)
    (hu : IsWeakSolution hab f (u.castLE one_le_two)) (φ : 𝓓(Opens.Ioo a b, ℝ)) :
    ∫ x in Ioo a b, (u.shift.extend x * deriv φ x + u.extend x * φ x)
      = ∫ x in Ioo a b, f x * φ x := by
  have hφ1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) φ := φ.contDiff.of_le (by simp)
  have hnot : ∀ x, x ∉ Ioo a b → φ x = 0 := fun x hx ↦
    φ.zero_on_compl (by rw [Opens.coe_Ioo]; exact hx)
  have hψa : ContDiffMapIcc.ofContDiff hab.le hφ1 ⟨a, left_mem_Icc.2 hab.le⟩ = 0 := by
    rw [ContDiffMapIcc.coe_ofContDiff]
    exact hnot a (by simp)
  have hψb : ContDiffMapIcc.ofContDiff hab.le hφ1 ⟨b, right_mem_Icc.2 hab.le⟩ = 0 := by
    rw [ContDiffMapIcc.coe_ofContDiff]
    exact hnot b (by simp)
  have e1 : ∀ x ∈ Ioo a b, (ContDiffMapIcc.ofContDiff hab.le hφ1).shift.extend x = deriv φ x :=
    fun x hx ↦ by
      rw [ContDiffMapIcc.extend_of_mem _ (Ioo_subset_Icc_self hx)]
      change (ContDiffMapIcc.ofContDiff hab.le hφ1).deriv 1 ⟨x, Ioo_subset_Icc_self hx⟩ = _
      rw [ContDiffMapIcc.deriv_ofContDiff]
      simp only [Fin.val_one, iteratedDeriv_one]
  have e0 : ∀ x ∈ Ioo a b, (ContDiffMapIcc.ofContDiff hab.le hφ1).extend x = φ x :=
    fun x hx ↦ by
      rw [ContDiffMapIcc.extend_of_mem _ (Ioo_subset_Icc_self hx), ContDiffMapIcc.coe_ofContDiff]
  have h := hu (ContDiffMapIcc.ofContDiff hab.le hφ1) hψa hψb
  have i1 : IntervalIntegrable
      (fun x ↦ u.shift.extend x * (ContDiffMapIcc.ofContDiff hab.le hφ1).shift.extend x)
      volume a b :=
    (u.shift.extend.continuous.mul
      (ContDiffMapIcc.ofContDiff hab.le hφ1).shift.extend.continuous).intervalIntegrable a b
  have i0 : IntervalIntegrable
      (fun x ↦ u.extend x * (ContDiffMapIcc.ofContDiff hab.le hφ1).extend x) volume a b :=
    (u.extend.continuous.mul
      (ContDiffMapIcc.ofContDiff hab.le hφ1).extend.continuous).intervalIntegrable a b
  rw [ContDiffMapIcc.castLE_shift_extend, ContDiffMapIcc.castLE_extend,
    ← intervalIntegral.integral_add i1 i0, integral_of_le hab.le, integral_of_le hab.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h
  refine (setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_).trans
    (h.trans (setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_))
  · rw [e1 x hx, e0 x hx]
  · rw [e0 x hx]

/-- **Section 8.1** of [brezis2011functional], Step D. Let $a < b$, let $f$ be continuous on
$[a, b]$, and let $u \in C^2([a, b])$ with $u(a) = u(b) = 0$. If $u$ satisfies (2), that is, $u$
is a weak solution of problem (1), then $u$ is a classical solution of (1).

The equation $-u'' + u = f$ holds on $(a, b)$ by the backbone's general Step D,
`EllipticInterval.isClassicalSolution_of_forall_testFunction` with $\alpha = \gamma = 1$ and
$\beta = 0$, and at the endpoints by continuity. -/
theorem dirichlet_stepD (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (u : ContDiffMapIcc hab.le 2) (hua : u ⟨a, left_mem_Icc.2 hab.le⟩ = 0)
    (hub : u ⟨b, right_mem_Icc.2 hab.le⟩ = 0) (hu : IsWeakSolution hab f (u.castLE one_le_two)) :
    IsClassicalSolution hab f u := by
  refine ⟨fun x ↦ ?_, hua, hub⟩
  -- the equation in the interior, from the general Step D
  have hint := EllipticInterval.isClassicalSolution_of_forall_testFunction hab
    (α := fun _ ↦ (1 : ℝ)) (β := fun _ ↦ (0 : ℝ)) (γ := fun _ ↦ (1 : ℝ)) contDiffOn_const
    continuousOn_const continuousOn_const hf u fun φ ↦ by
      simpa only [one_mul, zero_mul, add_zero] using integral_eq_of_isWeakSolution hab u hu φ
  simp only [one_mul, zero_mul, add_zero] at hint
  -- extension to the endpoints by continuity
  have hae : (fun x ↦ -u.shift.shift.extend x + u.extend x) =ᵐ[volume.restrict (Ioo a b)] f := by
    refine (ae_restrict_mem measurableSet_Ioo).mono fun x hx ↦ ?_
    change -u.shift.shift.extend x + u.extend x = f x
    have := hint x hx
    rw [deriv_shift_extend hab u hx] at this
    rw [ContDiffMapIcc.extend_of_mem _ (Ioo_subset_Icc_self hx)]
    exact this
  have hEq := eqOn_Icc_of_ae_eq hab
    (u.shift.shift.extend.continuous.neg.add u.extend.continuous).continuousOn hf hae x.2
  change -u.shift.shift.extend x + u.extend x = f x at hEq
  rw [ContDiffMapIcc.extend_val, ContDiffMapIcc.extend_val] at hEq
  exact hEq

end Brezis.Chapter08
