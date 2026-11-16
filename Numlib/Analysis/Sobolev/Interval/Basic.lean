/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/MultiIndex.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.TietzeExtension
import Numlib.Analysis.Convolution.Lp
import Numlib.Analysis.Sobolev.MultiIndex
import Numlib.MeasureTheory.Function.LpSpace.Convergence
import Numlib.MeasureTheory.Integral.IntervalIntegral

/-!
# Sobolev spaces on an open subset of the line

This module defines the weak derivative on an open set $I \subseteq \mathbb{R}$ and the Sobolev
space $W^{m,p}(I)$ for an arbitrary open $I$ and every exponent $1 \le p \le \infty$. A function $w$
is the $k$-th weak derivative of $f$ on $I$ if $f$ and $w$ are locally integrable on $I$ and $\int_I
\varphi^{(k)} f = (-1)^k \int_I \varphi\, w$ for every test function $\varphi$ on $I$. An element
$u \in W^{m,p}(I)$ has weak derivatives $u = u^{(0)}, u', \dots, u^{(m)}$ in $L^p(I)$. The
presentation follows §8.2 of [brezis2011functional], where $I$ is "an open interval, possibly
unbounded": the definition of $W^{1,p}(I)$, Remarks 2 and 4–8, Lemmas 8.1 and 8.2, Theorem 8.2,
Propositions 8.1 and 8.4, the Examples, and the paragraph on $W^{m,p}$.

The main one-dimensional facts hold on every open interval, bounded or not. By du Bois-Reymond's
lemma, a function with weak derivative $0$ is almost everywhere constant. The primitive
$c + \int_{y_0}^x w$ of a locally integrable function $w$ has the weak derivative $w$. Together,
these give the continuous representative: every $u \in W^{1,p}(I)$ agrees almost everywhere with a
function $\tilde u$ that is continuous on the closure $\bar I$ and satisfies
$\tilde u(y) - \tilde u(x) = \int_x^y u'$ for $x, y \in \bar I$. The module
`Numlib.Analysis.Sobolev.Interval` builds the bounded theory $H^m(a, b)$ for $p = 2$ on this layer.

## Main definitions

* `TopologicalSpace.Opens.Ioo`: the open interval $(a, b)$ as an open set of $\mathbb{R}$.
* `HasWeakDerivOn`, `HasWeakIteratedDerivOn`: the first-order and the $k$-th weak derivative on an
  open set $I$.
* `SobolevIntervalLp`: the space $W^{m,p}(I)$.
* `MemSobolevIntervalLp`: the predicate that a function belongs to $W^{m,p}(I)$.
* `SobolevIntervalLp.deriv`: the $j$-th weak derivative $u^{(j)} \in L^p(I)$ of $u \in W^{m,p}(I)$.
* `SobolevIntervalLpZero`: the closure $W_0^{m,p}(I)$ of the test functions in $W^{m,p}(I)$.
* `TestFunction.primitiveIic`: the primitive of a test function of zero mean on an open interval,
  which is again a test function.
* `SobolevIntervalLp.rep`: the canonical continuous representative $\tilde u$ of $u \in W^{1,p}(I)$,
  built from `SobolevIntervalLp.repConst`, `TopologicalSpace.Opens.basePoint` and
  `TopologicalSpace.Opens.testFunctionOne`.

## Main results

* `HasWeakDerivOn.exists_ae_eq_const`: du Bois-Reymond's lemma, Lemma 8.1 of [brezis2011functional];
  a function with weak derivative $0$ on an open interval is almost everywhere constant.
* `MeasureTheory.LocallyIntegrableOn.hasWeakDerivOn_integral`: Lemma 8.2; the primitive of a locally
  integrable function $w$ has the weak derivative $w$.
* `HasWeakDerivOn.exists_ae_eq_integral_of_mem` and
  `SobolevIntervalLp.exists_continuousOn_closure_ae_eq`: Theorem 8.2; the continuous representative.
* `SobolevIntervalLp.rep_sub_rep`: the fundamental theorem of calculus
  $\tilde u(y) - \tilde u(x) = \int_x^y u'$ in $W^{1,p}(I)$.
* `SobolevIntervalLp.rep_eq_of_continuousOn`: Remark 5; the continuous representative is unique.
* `hasWeakDerivOn_of_tendsto_eLpNorm`: Remark 4; the weak derivative is preserved under limits in
  $L^p$.
* `memSobolevIntervalLp_of_contDiffOn`, `memSobolevIntervalLp_of_piecewise_contDiffOn`,
  `memSobolevIntervalLp_abs`, `not_memSobolevIntervalLp_sign`: Remark 2 and the Examples of §8.2;
  $C^1$ and continuous piecewise $C^1$ functions lie in $W^{1,p}$, $|x| \in W^{1,p}(-1, 1)$, and the
  sign function does not.
* `SobolevIntervalLp.contDiffOn_rep_of_continuousOn_deriv`: Remark 6; the representative is $C^1$
  when the weak derivative is continuous.
* `SobolevIntervalLp.exists_contDiff_ae_eq`: an element of $W^{k+1,p}(I)$ has a $C^k$
  representative.
* `memSobolevIntervalLp_one_one_iff_absolutelyContinuousOnInterval`: Remark 8; $W^{1,1}(a, b)$ is
  the space of absolutely continuous functions.
* `memSobolevIntervalLp_top_iff_lipschitz`: Proposition 8.4; $W^{1,\infty}(I)$ is the space of
  Lipschitz functions.
* `SobolevIntervalLp.eLpNorm_translate_sub_le`: Proposition 8.5, (i) ⇒ (ii);
  $\|\tau_h u - u\|_p \le |h|\, \|u'\|_p$ on the line.
* `TopologicalSpace.Opens.eq_intervals_of_ordConnected`: an open interval of $\mathbb{R}$ is
  $\emptyset$, $\mathbb{R}$, a half-line or a bounded interval $(a, b)$.

## Implementation notes

* `SobolevIntervalLp m p I` is not a new type. It is the multi-index Sobolev space
  `SobolevMultiIndex ℝ (Module.Basis.singleton Unit ℝ) m p I volume` on $E = \mathbb{R}$ with the
  one-element basis, so that its components are the weak derivatives $u, u', \dots, u^{(m)}$ in
  $L^p(I)$. As an `abbrev`, it inherits the `NormedSpace ℝ` and `CompleteSpace` instances of that
  space for every $p$ with `[Fact (1 ≤ p)]`, and the `InnerProductSpace ℝ` instance at $p = 2$. The
  instance `Fact (1 ≤ ⊤)` is Mathlib's `fact_one_le_top_ennreal`.
* The norm is the $\ell^p$ sum $\|u\| = (\sum_{j \le m} \|u^{(j)}\|_p^p)^{1/p}$, and
  $\max_j \|u^{(j)}\|_\infty$ at $p = \infty$. This is the "equivalent norm" of
  [brezis2011functional] §8.2. The sum $\sum_j \|u^{(j)}\|_p$, which the source uses as the primary
  norm, is compared with it in `SobolevIntervalLp.norm_le_sum_norm_deriv` and
  `SobolevIntervalLp.sum_norm_deriv_le_mul_norm`.
* `SobolevInterval m a b` of `Numlib.Analysis.Sobolev.Interval` is the abbreviation
  `SobolevIntervalLp m 2 (TopologicalSpace.Opens.Ioo a b)`, and `SobolevIntervalZero a b` is
  `SobolevIntervalLpZero 1 2 (TopologicalSpace.Opens.Ioo a b)`.
* The hypothesis "$I$ is an interval" is `(hI : (I : Set ℝ).OrdConnected)`. It is written explicitly
  on every theorem that needs it: du Bois-Reymond's lemma, the representative, and every result that
  uses them. `Set.ordConnected_Ioo` and `Set.ordConnected_univ` give it for
  `TopologicalSpace.Opens.Ioo a b` and for the whole line `(⊤ : Opens ℝ)`.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace Interval Topology

noncomputable section

/-! ### The open interval as an open set -/

namespace TopologicalSpace.Opens

/-- The open interval $(a, b)$ as an open set of $\mathbb{R}$. -/
def Ioo (a b : ℝ) : Opens ℝ := ⟨Set.Ioo a b, isOpen_Ioo⟩

/-- The underlying set of `TopologicalSpace.Opens.Ioo a b` is the interval $(a, b)$, that is,
`Set.Ioo a b`. -/
@[simp]
theorem coe_Ioo (a b : ℝ) : (Opens.Ioo a b : Set ℝ) = Set.Ioo a b := rfl

end TopologicalSpace.Opens

/-! ### Weak derivatives on an open subset of the line -/

/-- **The $k$-th weak derivative** on an open set $I \subseteq \mathbb{R}$. The function $w$ is the
$k$-th weak derivative of $f$ on $I$ if $f$ and $w$ are locally integrable on $I$ and
$$\int_I \varphi^{(k)} f = (-1)^k \int_I \varphi\, w$$
for every test function $\varphi$ on $I$.

It is `HasWeakIteratedLineDerivOn` along the constant tuple of $k$ directions equal to $1$. -/
abbrev HasWeakIteratedDerivOn (k : ℕ) (f w : ℝ → ℝ) (I : Opens ℝ) : Prop :=
  HasWeakIteratedLineDerivOn (fun _ : Fin k ↦ (1 : ℝ)) f w I volume

/-- **The weak derivative** on an open set $I \subseteq \mathbb{R}$. The function $w$ is the weak
derivative of $f$ on $I$ if $f$ and $w$ are locally integrable on $I$ and
$$\int_I \varphi' f = -\int_I \varphi\, w$$
for every test function $\varphi$ on $I$.

It is `HasWeakIteratedDerivOn 1`, that is, `HasWeakIteratedLineDerivOn` along the single
direction $1$. -/
abbrev HasWeakDerivOn (f w : ℝ → ℝ) (I : Opens ℝ) : Prop :=
  HasWeakIteratedLineDerivOn (fun _ : Fin 1 ↦ (1 : ℝ)) f w I volume

section Chain

variable {I : Opens ℝ} {f v w : ℝ → ℝ} {k : ℕ}

/-- The function $w$ is the weak derivative of order $1$ of $f$ on $I$ (`HasWeakIteratedDerivOn 1`)
if and only if it is the weak derivative of $f$ on $I$ (`HasWeakDerivOn`). -/
theorem hasWeakIteratedDerivOn_one : HasWeakIteratedDerivOn 1 f w I ↔ HasWeakDerivOn f w I :=
  Iff.rfl

/-- The function $w$ is the $k$-th weak derivative of $f$ on the open set $I$ if and only if $f$ and
$w$ are locally integrable on $I$ and $\int_I \varphi^{(k)} f = (-1)^k \int_I \varphi\, w$ for
every test function $\varphi$ on $I$. -/
theorem hasWeakIteratedDerivOn_iff :
    HasWeakIteratedDerivOn k f w I ↔ LocallyIntegrableOn f I ∧ LocallyIntegrableOn w I ∧
      ∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), iteratedDeriv k φ x * f x
        = (-1) ^ k * ∫ x in (I : Set ℝ), φ x * w x := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun φ ↦ by
      simpa only [smul_eq_mul, iteratedDeriv_eq_iteratedFDeriv] using h3 φ⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun φ ↦ by
      simpa only [smul_eq_mul, iteratedDeriv_eq_iteratedFDeriv] using h3 φ⟩

/-- The function $w$ is the weak derivative of $f$ on the open set $I$ if and only if $f$ and $w$
are locally integrable on $I$ and $\int_I \varphi' f = -\int_I \varphi\, w$ for every test
function $\varphi$ on $I$. -/
theorem hasWeakDerivOn_iff :
    HasWeakDerivOn f w I ↔ LocallyIntegrableOn f I ∧ LocallyIntegrableOn w I ∧
      ∀ φ : 𝓓(I, ℝ), ∫ x in (I : Set ℝ), deriv φ x * f x = -∫ x in (I : Set ℝ), φ x * w x := by
  rw [← hasWeakIteratedDerivOn_one, hasWeakIteratedDerivOn_iff]
  simp only [iteratedDeriv_one, pow_one, neg_one_mul]

/-- If $w$ is the $k$-th weak derivative of $f$ on $I$, then $\int_I \varphi^{(k)} f = (-1)^k \int_I
\varphi\, w$ for every test function $\varphi$ on $I$. -/
theorem HasWeakIteratedDerivOn.integral_iteratedDeriv_mul (h : HasWeakIteratedDerivOn k f w I)
    (φ : 𝓓(I, ℝ)) :
    ∫ x in (I : Set ℝ), iteratedDeriv k φ x * f x = (-1) ^ k * ∫ x in (I : Set ℝ), φ x * w x :=
  (hasWeakIteratedDerivOn_iff.1 h).2.2 φ

/-- If $w$ is the weak derivative of $f$ on $I$, then $\int_I \varphi' f = -\int_I \varphi\, w$ for
every test function $\varphi$ on $I$. -/
theorem HasWeakDerivOn.integral_deriv_mul (h : HasWeakDerivOn f w I) (φ : 𝓓(I, ℝ)) :
    ∫ x in (I : Set ℝ), deriv φ x * f x = -∫ x in (I : Set ℝ), φ x * w x :=
  (hasWeakDerivOn_iff.1 h).2.2 φ

/-- For a test function $\varphi$ on an open set $I \subseteq \mathbb{R}$, the test function
`TestFunction.iteratedFDerivApply` of order $k$ along the constant tuple $1$ is the $k$-th
derivative $\varphi^{(k)}$. -/
theorem TestFunction.iteratedDerivApply_coe (φ : 𝓓(I, ℝ)) (k : ℕ) :
    (φ.iteratedFDerivApply k (fun _ ↦ (1 : ℝ)) : ℝ → ℝ) = iteratedDeriv k φ := rfl

/-- For a test function $\varphi$ on an open set $I \subseteq \mathbb{R}$, the test function
`TestFunction.fderivApply` in the direction $1$ is the derivative $\varphi'$. -/
theorem TestFunction.derivApply_coe (φ : 𝓓(I, ℝ)) : (φ.fderivApply 1 : ℝ → ℝ) = deriv φ := rfl

/-- **Chaining weak derivatives.** If $v$ is the weak derivative of $f$ on $I$ and $w$ is the $k$-th
weak derivative of $v$ on $I$, then $w$ is the $(k + 1)$-th weak derivative of $f$ on $I$.

The proof tests the first identity against $\varphi^{(k)}$, which is again a test function. -/
theorem HasWeakDerivOn.hasWeakIteratedDerivOn_succ (h : HasWeakDerivOn f v I)
    (h' : HasWeakIteratedDerivOn k v w I) : HasWeakIteratedDerivOn (k + 1) f w I := by
  refine hasWeakIteratedDerivOn_iff.2 ⟨h.locallyIntegrableOn, h'.locallyIntegrableOn_weakDeriv,
    fun φ ↦ ?_⟩
  have e1 := h.integral_deriv_mul (φ.iteratedFDerivApply k (fun _ ↦ 1))
  rw [TestFunction.iteratedDerivApply_coe] at e1
  rw [iteratedDeriv_succ, e1, h'.integral_iteratedDeriv_mul, pow_succ]
  ring

/-- If $v$ is the weak derivative of $f$ on $I$ and $w$ is the $(k + 1)$-th weak derivative of $f$
on $I$, then $w$ is the $k$-th weak derivative of $v$ on $I$. -/
theorem HasWeakDerivOn.hasWeakIteratedDerivOn_of_succ (h : HasWeakDerivOn f v I)
    (h' : HasWeakIteratedDerivOn (k + 1) f w I) : HasWeakIteratedDerivOn k v w I := by
  refine hasWeakIteratedDerivOn_iff.2 ⟨h.locallyIntegrableOn_weakDeriv,
    h'.locallyIntegrableOn_weakDeriv, fun φ ↦ ?_⟩
  have e1 := h.integral_deriv_mul (φ.iteratedFDerivApply k (fun _ ↦ 1))
  rw [TestFunction.iteratedDerivApply_coe, ← iteratedDeriv_succ,
    h'.integral_iteratedDeriv_mul] at e1
  rw [neg_eq_iff_eq_neg.1 e1.symm, pow_succ]
  ring

/-- If $v$ is the $k$-th weak derivative and $w$ the $(k + 1)$-th weak derivative of $f$ on $I$,
then $w$ is the weak derivative of $v$ on $I$.

This makes the weak derivatives of a function of $W^{m,p}(I)$ a chain, in which each is the weak
derivative of the one before. -/
theorem HasWeakIteratedDerivOn.hasWeakDerivOn_of_succ (h : HasWeakIteratedDerivOn k f v I)
    (h' : HasWeakIteratedDerivOn (k + 1) f w I) : HasWeakDerivOn v w I := by
  refine hasWeakDerivOn_iff.2 ⟨h.locallyIntegrableOn_weakDeriv,
    h'.locallyIntegrableOn_weakDeriv, fun φ ↦ ?_⟩
  have e1 := h.integral_iteratedDeriv_mul (φ.fderivApply 1)
  rw [TestFunction.derivApply_coe, ← iteratedDeriv_succ', h'.integral_iteratedDeriv_mul] at e1
  have hk : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  refine mul_left_cancel₀ hk ?_
  rw [← e1, pow_succ]
  ring

/-- Let $y \in \mathbb{R}^n$ have all entries equal to $1$, and let $n = k$. Then $w$ is the weak
derivative of $f$ on $I$ along the tuple of directions $y$ (`HasWeakIteratedLineDerivOn`) if and
only if $w$ is the $k$-th weak derivative of $f$ on $I$.

The length $n$ is only propositionally equal to $k$, as for the tuples `multiIndexTuple` that
name a multi-index. -/
theorem hasWeakIteratedLineDerivOn_iff_hasWeakIteratedDerivOn {n : ℕ} {y : Fin n → ℝ}
    (hy : ∀ j, y j = 1) (hn : n = k) :
    HasWeakIteratedLineDerivOn y f w I volume ↔ HasWeakIteratedDerivOn k f w I := by
  subst hn
  rw [show y = fun _ ↦ (1 : ℝ) from funext hy]

end Chain

/-! ### Classical derivatives are weak derivatives -/

section Classical

variable {I : Opens ℝ} {f : ℝ → ℝ}

/-- **A classical derivative is a weak derivative**, iterated form. Let $f$ be of class $C^N$ on the
open set $I$, with $N \in \mathbb{N} \cup \{\infty, \omega\}$, and let $k \le N$. Then the
$k$-th derivative $f^{(k)}$ (`iteratedDeriv k f`) is the $k$-th weak derivative of $f$ on $I$.

This is `ContDiffOn.hasWeakIteratedFDerivOn` read in the direction $1$. -/
theorem hasWeakIteratedDerivOn_of_contDiffOn {N : ℕ∞ω} {k : ℕ} (hf : ContDiffOn ℝ N f I)
    (hk : (k : ℕ∞ω) ≤ N) : HasWeakIteratedDerivOn k f (iteratedDeriv k f) I :=
  (ContDiffOn.hasWeakIteratedFDerivOn (Ω := I) (μ := volume) hf hk).lineDeriv _

/-- **A classical derivative is a weak derivative.** If $f$ is of class $C^1$ on the open set $I$,
then its derivative $f'$ is the weak derivative of $f$ on $I$. -/
theorem hasWeakDerivOn_of_contDiffOn (hf : ContDiffOn ℝ 1 f I) : HasWeakDerivOn f (deriv f) I := by
  have := hasWeakIteratedDerivOn_of_contDiffOn (k := 1) hf le_rfl
  rwa [iteratedDeriv_one] at this

end Classical

/-! ### The space $W^{m,p}(I)$ -/

/-- The tuple of directions `multiIndexTuple` that names a multi-index for the one-element basis of
$\mathbb{R}$ is constantly $1$. -/
theorem multiIndexTuple_singleton (α : Unit → ℕ) (j : Fin (∑ i, α i)) :
    multiIndexTuple (Module.Basis.singleton Unit ℝ) α j = 1 := by
  simp [multiIndexTuple, multiIndexDirections, List.getElem_replicate]

/-- **The Sobolev space** $W^{m,p}(I)$ on an open set $I \subseteq \mathbb{R}$, for
$p \in [0, \infty]$. An element consists of functions $u^{(0)}, \dots, u^{(m)} \in L^p(I)$ such
that $u^{(j)}$ is the $j$-th weak derivative of $u^{(0)}$ on $I$ for every $j \le m$. For
$1 \le p \le \infty$ it is a Banach space, and for $p = 2$ it is a Hilbert space $H^m(I)$ for
the inner product
$$(u, v)_{H^m} = \sum_{j=0}^m (u^{(j)}, v^{(j)})_{L^2(I)}.$$
This is the space of [brezis2011functional] §8.2 for $m = 1$, and of the paragraph on $W^{m,p}$
there for general $m$.

The type is the multi-index Sobolev space `SobolevMultiIndex` on $E = \mathbb{R}$ with the
one-element basis, whose multi-indices of order at most $m$ are the derivative orders
$0, \dots, m$. As an `abbrev`, it inherits the `NormedSpace ℝ` and `CompleteSpace` instances of
the multi-index space under `[Fact (1 ≤ p)]`, and its `InnerProductSpace ℝ` instance at $p = 2$.
The inner product formula is `SobolevIntervalLp.inner_eq`. -/
abbrev SobolevIntervalLp (m : ℕ) (p : ℝ≥0∞) (I : Opens ℝ) : Type :=
  SobolevMultiIndex ℝ (Module.Basis.singleton Unit ℝ) m p I volume

/-- A function $f : \mathbb{R} \to \mathbb{R}$ **belongs to $W^{m,p}(I)$** if $f \in L^p(I)$ and,
for every $j \le m$, $f$ has a $j$-th weak derivative on $I$ that lies in $L^p(I)$.

The definition is `MemSobolevMultiIndex` for the one-element basis of $\mathbb{R}$. The unfolded
form is `memSobolevIntervalLp_iff`. -/
def MemSobolevIntervalLp (f : ℝ → ℝ) (m : ℕ) (p : ℝ≥0∞) (I : Opens ℝ) : Prop :=
  MemSobolevMultiIndex (Module.Basis.singleton Unit ℝ) f m p I volume

/-- **The Sobolev space** $W_0^{m,p}(I)$, for $1 \le p \le \infty$: the closure in $W^{m,p}(I)$ of
the test functions $C_0^\infty(I)$. It is a closed subspace of the Banach space $W^{m,p}(I)$,
hence a Banach space, and for $p = 2$ a Hilbert space. This is the space of
[brezis2011functional] §8.3 for $m = 1$, and of Remark 18 there for general $m$.

The definition is `SobolevMultiIndexZero` on the open set $I$. -/
abbrev SobolevIntervalLpZero (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (I : Opens ℝ) :
    Submodule ℝ (SobolevIntervalLp m p I) :=
  SobolevMultiIndexZero ℝ (Module.Basis.singleton Unit ℝ) m p I volume

namespace SobolevIntervalLp

/-- The multi-index of the $j$-th derivative in one variable, for $j \le m$. -/
def derivIndex (m : ℕ) (j : Fin (m + 1)) : MultiIndexLE Unit m :=
  ⟨fun _ ↦ j, by simpa using Fin.is_le j⟩

/-- The bijection between the derivative orders $0, \dots, m$ and the multi-indices of order at most
$m$ in one variable. -/
def derivIndexEquiv (m : ℕ) : Fin (m + 1) ≃ MultiIndexLE Unit m where
  toFun := derivIndex m
  invFun α := ⟨α.1 (), by have := α.2; simpa using Nat.lt_succ_of_le this⟩
  left_inv j := rfl
  right_inv α := Subtype.ext (funext fun _ ↦ rfl)

end SobolevIntervalLp

/-! ### Membership of $W^{m,p}(I)$ -/

section Space

variable {m : ℕ} {p : ℝ≥0∞} {I : Opens ℝ} {f : ℝ → ℝ}

/-- A function $f$ lies in $W^{m,p}(I)$ if and only if $f \in L^p(I)$ and, for every $j \le m$,
there is a function $w \in L^p(I)$ that is the $j$-th weak derivative of $f$ on $I$. -/
theorem memSobolevIntervalLp_iff :
    MemSobolevIntervalLp f m p I ↔ MemLp f p (volume.restrict I) ∧ ∀ j ≤ m,
      ∃ w : ℝ → ℝ, HasWeakIteratedDerivOn j f w I ∧ MemLp w p (volume.restrict I) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj ↦ ?_⟩
    obtain ⟨w, hw, hwp⟩ := h2 (fun _ ↦ j) (by simpa using hj)
    exact ⟨w, (hasWeakIteratedLineDerivOn_iff_hasWeakIteratedDerivOn
      (multiIndexTuple_singleton _) (by simp)).1 hw, hwp⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun α hα ↦ ?_⟩
    obtain ⟨w, hw, hwp⟩ := h2 (α ()) (by simpa using hα)
    exact ⟨w, (hasWeakIteratedLineDerivOn_iff_hasWeakIteratedDerivOn
      (multiIndexTuple_singleton _) (by simp)).2 hw, hwp⟩

/-- If $f \in W^{m,p}(I)$ and $g = f$ almost everywhere on $I$, then $g \in W^{m,p}(I)$. This is the
first sentence of Remark 5 of [brezis2011functional] §8.2. -/
theorem MemSobolevIntervalLp.congr_ae {g : ℝ → ℝ} (h : MemSobolevIntervalLp f m p I)
    (hfg : f =ᵐ[volume.restrict I] g) : MemSobolevIntervalLp g m p I :=
  MemSobolevMultiIndex.congr_ae h hfg

/-- For $1 \le p \le \infty$, a function lies in $W^{0,p}(I)$ if and only if it lies in $L^p(I)$. -/
theorem memSobolevIntervalLp_zero_iff [Fact (1 ≤ p)] :
    MemSobolevIntervalLp f 0 p I ↔ MemLp f p (volume.restrict I) := by
  rw [memSobolevIntervalLp_iff]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun j hj ↦ ?_⟩⟩
  obtain rfl : j = 0 := Nat.le_zero.1 hj
  exact ⟨f, HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
    (h.locallyIntegrableOn Fact.out), h⟩

/-- **The recursive description of $W^{m+1,p}(I)$.** A function $f$ lies in $W^{m+1,p}(I)$ if and
only if $f \in L^p(I)$ and $f$ has a weak derivative $w$ on $I$ with $w \in W^{m,p}(I)$. This is
the inductive definition of $W^{m,p}$ in [brezis2011functional] §8.2.

In the forward direction, the weak derivatives of $f'$ of orders at most $m$ are those of $f$ of
orders at most $m + 1$. The backward direction is the chain rule
`HasWeakDerivOn.hasWeakIteratedDerivOn_succ`. -/
theorem memSobolevIntervalLp_succ_iff :
    MemSobolevIntervalLp f (m + 1) p I ↔ MemLp f p (volume.restrict I) ∧
      ∃ w : ℝ → ℝ, HasWeakDerivOn f w I ∧ MemSobolevIntervalLp w m p I := by
  simp only [memSobolevIntervalLp_iff]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨w, hw, hwp⟩ := h2 1 (by omega)
    refine ⟨h1, w, hw, hwp, fun j hj ↦ ?_⟩
    obtain ⟨w', hw', hwp'⟩ := h2 (j + 1) (by omega)
    exact ⟨w', HasWeakDerivOn.hasWeakIteratedDerivOn_of_succ hw hw', hwp'⟩
  · rintro ⟨h1, w, hw, hwp, h2⟩
    refine ⟨h1, fun j hj ↦ ?_⟩
    cases j with
    | zero =>
      exact ⟨f, HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _ hw.locallyIntegrableOn, h1⟩
    | succ j =>
      obtain ⟨w', hw', hwp'⟩ := h2 j (by omega)
      exact ⟨w', HasWeakDerivOn.hasWeakIteratedDerivOn_succ hw hw', hwp'⟩

/-- **The definition of $W^{1,p}(I)$** in [brezis2011functional] §8.2. For $1 \le p \le \infty$, a
function $f$ lies in $W^{1,p}(I)$ if and only if $f \in L^p(I)$ and $f$ has a weak derivative
$w$ on $I$ with $w \in L^p(I)$. -/
theorem memSobolevIntervalLp_one_iff [Fact (1 ≤ p)] :
    MemSobolevIntervalLp f 1 p I ↔ MemLp f p (volume.restrict I) ∧
      ∃ w : ℝ → ℝ, HasWeakDerivOn f w I ∧ MemLp w p (volume.restrict I) := by
  simp only [memSobolevIntervalLp_succ_iff, memSobolevIntervalLp_zero_iff]

end Space

/-! ### The weak derivatives of an element of $W^{m,p}(I)$ -/

namespace SobolevIntervalLp

variable {m : ℕ} {p : ℝ≥0∞} {I : Opens ℝ}

/-- The function $u^{(0)} : \mathbb{R} \to \mathbb{R}$ of an element $u \in W^{m,p}(I)$. -/
abbrev fn (u : SobolevIntervalLp m p I) : ℝ → ℝ := SobolevMultiIndex.fn u

/-- The $j$-th weak derivative $u^{(j)}$ of $u \in W^{m,p}(I)$, for $0 \le j \le m$, as an element
of $L^p(I)$. For $j = 0$ it is the function of $u$. -/
def deriv (u : SobolevIntervalLp m p I) (j : Fin (m + 1)) :
    Lp ℝ p (volume.restrict (I : Set ℝ)) :=
  SobolevMultiIndex.weakDeriv u (derivIndex m j)

/-- For $u \in W^{m,p}(I)$, the derivative $u^{(0)}$ of order $0$ is the function of $u$. -/
theorem deriv_zero (u : SobolevIntervalLp m p I) : ⇑(deriv u 0) = fn u := rfl

/-- For $u, v \in W^{m,p}(I)$ and $j \le m$, $(u + v)^{(j)} = u^{(j)} + v^{(j)}$. -/
theorem deriv_add (u v : SobolevIntervalLp m p I) (j : Fin (m + 1)) :
    deriv (u + v) j = deriv u j + deriv v j := rfl

/-- For $c \in \mathbb{R}$, $u \in W^{m,p}(I)$ and $j \le m$, $(c u)^{(j)} = c\, u^{(j)}$. -/
theorem deriv_smul (c : ℝ) (u : SobolevIntervalLp m p I) (j : Fin (m + 1)) :
    deriv (c • u) j = c • deriv u j := rfl

/-- For $u, v \in W^{m,p}(I)$ and $j \le m$, $(u - v)^{(j)} = u^{(j)} - v^{(j)}$. -/
theorem deriv_sub (u v : SobolevIntervalLp m p I) (j : Fin (m + 1)) :
    deriv (u - v) j = deriv u j - deriv v j := rfl

/-- For $j \le m$, the $j$-th weak derivative of $0 \in W^{m,p}(I)$ is $0$. -/
theorem deriv_zero_elem (j : Fin (m + 1)) : deriv (0 : SobolevIntervalLp m p I) j = 0 := rfl

/-- Let $u, v \in W^{m,p}(I)$. If $u^{(j)} = v^{(j)}$ in $L^p(I)$ for every $j \le m$, then $u = v$.
-/
theorem ext {u v : SobolevIntervalLp m p I} (h : ∀ j, deriv u j = deriv v j) : u = v :=
  Subtype.ext (PiLp.ext fun α ↦ h ((derivIndexEquiv m).symm α))

/-- For $u \in W^{m,p}(I)$ and $j \le m$, the element $u^{(j)}$ is the $j$-th weak derivative of the
function of $u$ on $I$. -/
theorem hasWeakIteratedDerivOn_deriv (u : SobolevIntervalLp m p I) (j : Fin (m + 1)) :
    HasWeakIteratedDerivOn j (fn u) (deriv u j) I :=
  (hasWeakIteratedLineDerivOn_iff_hasWeakIteratedDerivOn (multiIndexTuple_singleton _)
    (by simp [derivIndex])).1 (SobolevMultiIndex.hasWeakIteratedLineDerivOn u (derivIndex m j))

/-- For $u \in W^{m,p}(I)$ and $j < m$, the element $u^{(j+1)}$ is the weak derivative of $u^{(j)}$
on $I$. -/
theorem hasWeakDerivOn_deriv_succ (u : SobolevIntervalLp m p I) (j : Fin m) :
    HasWeakDerivOn (deriv u j.castSucc) (deriv u j.succ) I :=
  (hasWeakIteratedDerivOn_deriv u j.castSucc).hasWeakDerivOn_of_succ
    (hasWeakIteratedDerivOn_deriv u j.succ)

/-- For $u \in W^{1,p}(I)$, the function of $u$ has the weak derivative $u'$ on $I$. -/
theorem hasWeakDerivOn_fn (u : SobolevIntervalLp 1 p I) : HasWeakDerivOn (fn u) (deriv u 1) I := by
  have := hasWeakDerivOn_deriv_succ u 0
  rwa [Fin.castSucc_zero, Fin.succ_zero_eq_one, deriv_zero] at this

/-- For $u \in W^{m,p}(I)$, the function of $u$ belongs to $W^{m,p}(I)$ in the sense of
`MemSobolevIntervalLp`. -/
theorem memSobolevIntervalLp_fn (u : SobolevIntervalLp m p I) :
    MemSobolevIntervalLp (fn u) m p I :=
  SobolevMultiIndex.memSobolevMultiIndex u

/-- For $u \in W^{m,p}(I)$ and $j \le m$, the function $u^{(j)}$ lies in $L^p(I)$. -/
theorem memLp_deriv (u : SobolevIntervalLp m p I) (j : Fin (m + 1)) :
    MemLp (deriv u j) p (volume.restrict I) :=
  Lp.memLp _

/-- For $1 \le p \le \infty$, $u \in W^{m,p}(I)$ and $j \le m$, the function $u^{(j)}$ is locally
integrable on $I$. -/
theorem locallyIntegrableOn_deriv [Fact (1 ≤ p)] (u : SobolevIntervalLp m p I)
    (j : Fin (m + 1)) : LocallyIntegrableOn (deriv u j) I :=
  (memLp_deriv u j).locallyIntegrableOn Fact.out

/-- The element of $W^{m,p}(I)$ built from $v_0, \dots, v_m \in L^p(I)$ such that $v_j$ is the
$j$-th weak derivative of $v_0$ on $I$ for every $j \le m$. -/
def mk (v : Fin (m + 1) → Lp ℝ p (volume.restrict (I : Set ℝ)))
    (hv : ∀ j : Fin (m + 1), HasWeakIteratedDerivOn (j : ℕ) (v 0) (v j) I) :
    SobolevIntervalLp m p I :=
  ⟨WithLp.toLp p fun α ↦ v ((derivIndexEquiv m).symm α), fun α ↦
    (hasWeakIteratedLineDerivOn_iff_hasWeakIteratedDerivOn (multiIndexTuple_singleton _)
      (Fintype.sum_unique _)).2 (hv ((derivIndexEquiv m).symm α))⟩

/-- The weak derivatives of `SobolevIntervalLp.mk v hv` are the given functions: its $j$-th weak
derivative is $v_j$. -/
@[simp]
theorem deriv_mk (v : Fin (m + 1) → Lp ℝ p (volume.restrict (I : Set ℝ)))
    (hv : ∀ j : Fin (m + 1), HasWeakIteratedDerivOn (j : ℕ) (v 0) (v j) I) (j : Fin (m + 1)) :
    deriv (mk v hv) j = v j := rfl

/-- The function of `SobolevIntervalLp.mk v hv` is $v_0$. -/
theorem fn_mk (v : Fin (m + 1) → Lp ℝ p (volume.restrict (I : Set ℝ)))
    (hv : ∀ j : Fin (m + 1), HasWeakIteratedDerivOn (j : ℕ) (v 0) (v j) I) :
    fn (mk v hv) = v 0 := rfl

/-! ### The norm -/

variable [Fact (1 ≤ p)]

/-- **The norm of $W^{m,p}(I)$ for $p < \infty$.** Let $1 \le p < \infty$ and $u \in W^{m,p}(I)$.
Then
$$\|u\| = \Bigl(\sum_{j=0}^m \|u^{(j)}\|_{L^p(I)}^p\Bigr)^{1/p}.$$
This is the "equivalent norm" in the Notation of [brezis2011functional] §8.2. -/
theorem norm_eq_sum (hp : p ≠ ⊤) (u : SobolevIntervalLp m p I) :
    ‖u‖ = (∑ j : Fin (m + 1), ‖deriv u j‖ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [SobolevMultiIndex.norm_eq_sum hp, ← (derivIndexEquiv m).sum_comp]
  rfl

omit [Fact (1 ≤ p)] in
/-- **The norm of $W^{m,\infty}(I)$.** For $u \in W^{m,\infty}(I)$, $\|u\| = \max_{0 \le j \le m}
\|u^{(j)}\|_{L^\infty(I)}$. -/
theorem norm_eq_ciSup (u : SobolevIntervalLp m ⊤ I) : ‖u‖ = ⨆ j : Fin (m + 1), ‖deriv u j‖ := by
  rw [SobolevMultiIndex.norm_eq_ciSup, ← (derivIndexEquiv m).iSup_comp]
  rfl

/-- Let $1 \le p \le \infty$, $u \in W^{m,p}(I)$ and $j \le m$. Then
$\|u^{(j)}\|_{L^p(I)} \le \|u\|_{W^{m,p}}$. -/
theorem norm_deriv_le (u : SobolevIntervalLp m p I) (j : Fin (m + 1)) : ‖deriv u j‖ ≤ ‖u‖ := by
  rw [← Submodule.norm_coe]
  exact PiLp.norm_apply_le _ _

/-- Let $1 \le p \le \infty$ and $u \in W^{m,p}(I)$. Then
$\|u\| \le \sum_{j=0}^m \|u^{(j)}\|_{L^p(I)}$, so the norm of the source dominates the norm of
the type.

The $\ell^p$ norm of a tuple is at most its $\ell^1$ norm. -/
theorem norm_le_sum_norm_deriv (u : SobolevIntervalLp m p I) :
    ‖u‖ ≤ ∑ j : Fin (m + 1), ‖deriv u j‖ := by
  classical
  have e : (u : SobolevMultiIndexTuple ℝ Unit m p I volume)
      = ∑ j : Fin (m + 1), PiLp.single p (derivIndex m j) (deriv u j) := by
    refine PiLp.ext fun α ↦ ?_
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.ofLp_single]
    rw [Finset.sum_eq_single ((derivIndexEquiv m).symm α)]
    · have hα : derivIndex m ((derivIndexEquiv m).symm α) = α :=
        (derivIndexEquiv m).apply_symm_apply α
      rw [hα, Pi.single_eq_same]
      rfl
    · intro j _ hj
      apply Pi.single_eq_of_ne
      intro h
      exact hj (by rw [h]; exact ((derivIndexEquiv m).symm_apply_apply j).symm)
    · simp
  rw [← Submodule.norm_coe, e]
  refine (norm_sum_le _ _).trans ?_
  simp only [PiLp.norm_single, le_refl]

/-- Let $1 \le p \le \infty$ and $u \in W^{m,p}(I)$. Then
$$\sum_{j=0}^m \|u^{(j)}\|_{L^p(I)} \le (m + 1)\, \|u\|.$$

With `SobolevIntervalLp.norm_le_sum_norm_deriv`, this makes the norm
$\|u\|_{W^{m,p}} = \sum_{j \le m} \|D^j u\|_p$ of [brezis2011functional] §8.2 equivalent to the
norm of the type, for every $1 \le p \le \infty$. -/
theorem sum_norm_deriv_le_mul_norm (u : SobolevIntervalLp m p I) :
    ∑ j : Fin (m + 1), ‖deriv u j‖ ≤ (m + 1) * ‖u‖ := by
  calc ∑ j : Fin (m + 1), ‖deriv u j‖ ≤ ∑ _j : Fin (m + 1), ‖u‖ :=
        Finset.sum_le_sum fun j _ ↦ norm_deriv_le u j
    _ = (m + 1) * ‖u‖ := by simp

omit [Fact (1 ≤ p)] in
/-- **The inner product of $H^m(I)$.** For $u, v \in W^{m,2}(I)$,
$$(u, v)_{H^m} = \sum_{j=0}^m (u^{(j)}, v^{(j)})_{L^2(I)}.$$
This is the inner product in the Notation and the paragraph on $W^{m,p}$ of
[brezis2011functional] §8.2. -/
theorem inner_eq (u v : SobolevIntervalLp m 2 I) :
    ⟪u, v⟫_ℝ = ∑ j : Fin (m + 1), ⟪deriv u j, deriv v j⟫_ℝ := by
  rw [Submodule.coe_inner, PiLp.inner_apply, ← (derivIndexEquiv m).sum_comp]
  rfl

omit [Fact (1 ≤ p)] in
/-- **The inner product of $H^1(I)$ as an integral.** For $u, v \in W^{1,2}(I)$,
$$(u, v)_{H^1} = \int_I (u v + u' v').$$
This is the inner product in the Notation of [brezis2011functional] §8.2. -/
theorem inner_eq_integral (u v : SobolevIntervalLp 1 2 I) :
    ⟪u, v⟫_ℝ = ∫ x in (I : Set ℝ), (fn u x * fn v x + deriv u 1 x * deriv v 1 x) := by
  rw [inner_eq, Fin.sum_univ_two, L2.inner_def, L2.inner_def,
    ← integral_add (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp [RCLike.inner_apply, deriv_zero, mul_comm]

/-! ### Weak differentiation and the inclusions as bounded maps -/

variable (m p I) in
/-- For $1 \le p \le \infty$ and $j \le m$, the map $u \mapsto u^{(j)}$ as a continuous linear map
$W^{m,p}(I) \to L^p(I)$ of norm at most $1$. -/
def derivL (j : Fin (m + 1)) : SobolevIntervalLp m p I →L[ℝ] Lp ℝ p (volume.restrict (I : Set ℝ)) :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ deriv u j
      map_add' := fun u v ↦ deriv_add u v j
      map_smul' := fun c u ↦ deriv_smul c u j } 1 fun u ↦ by
    rw [one_mul]; exact norm_deriv_le u j

/-- The map `SobolevIntervalLp.derivL m p I j` sends $u$ to $u^{(j)}$. -/
@[simp]
theorem derivL_apply (j : Fin (m + 1)) (u : SobolevIntervalLp m p I) :
    derivL m p I j u = deriv u j :=
  rfl

/-- For $1 \le p \le \infty$ and $j \le m$, the operator norm of $u \mapsto u^{(j)}$,
$W^{m,p}(I) \to L^p(I)$, is at most $1$. -/
theorem norm_derivL_le (j : Fin (m + 1)) : ‖derivL m p I j‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

variable (m p I) in
/-- **The Sobolev seminorm** $|u|_{W^{m,p}(I)} = \|u^{(m)}\|_{L^p(I)}$ on $W^{m,p}(I)$, for
$1 \le p \le \infty$, bundled as a `Seminorm`. -/
def seminorm : Seminorm ℝ (SobolevIntervalLp m p I) :=
  (normSeminorm ℝ (Lp ℝ p (volume.restrict (I : Set ℝ)))).comp
    (derivL m p I (Fin.last m) : SobolevIntervalLp m p I →ₗ[ℝ] _)

/-- For $u \in W^{m,p}(I)$, $|u|_{W^{m,p}} = \|u^{(m)}\|_{L^p(I)}$. -/
theorem seminorm_apply (u : SobolevIntervalLp m p I) :
    seminorm m p I u = ‖deriv u (Fin.last m)‖ :=
  rfl

/-- For $u \in W^{m,p}(I)$, $|u|_{W^{m,p}} \le \|u\|_{W^{m,p}}$. -/
theorem seminorm_le_norm (u : SobolevIntervalLp m p I) : seminorm m p I u ≤ ‖u‖ :=
  norm_deriv_le u _

/-- Let $1 \le p \le \infty$, $u \in W^{m',p}(I)$ and $v \in W^{m,p}(I)$, and let
$e : \{0, \dots, m\} \to \{0, \dots, m'\}$ be injective. If $v^{(j)} = u^{(e(j))}$ for every
$j \le m$, then $\|v\| \le \|u\|$.

The norm is the $\ell^p$ norm of the tuple of the $L^p$ norms of the derivatives, and dropping
entries does not increase it. -/
theorem norm_le_of_deriv_eq {m' : ℕ} (u : SobolevIntervalLp m' p I) (v : SobolevIntervalLp m p I)
    {e : Fin (m + 1) → Fin (m' + 1)} (he : Function.Injective e)
    (hv : ∀ j, deriv v j = deriv u (e j)) : ‖v‖ ≤ ‖u‖ := by
  rcases eq_or_ne p ⊤ with rfl | hp
  · rw [norm_eq_ciSup, norm_eq_ciSup]
    exact ciSup_le fun j ↦ by
      rw [hv]
      exact le_ciSup (f := fun i ↦ ‖deriv u i‖) (Finite.bddAbove_range _) (e j)
  · rw [norm_eq_sum hp, norm_eq_sum hp]
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg (norm_nonneg _) _) ?_
      (by positivity)
    simp only [hv]
    calc ∑ j : Fin (m + 1), ‖deriv u (e j)‖ ^ p.toReal
        = ∑ i ∈ Finset.univ.map ⟨e, he⟩, ‖deriv u i‖ ^ p.toReal := by
          rw [Finset.sum_map]; rfl
      _ ≤ ∑ i : Fin (m' + 1), ‖deriv u i‖ ^ p.toReal :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun i _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _

variable (m p I) in
/-- Weak differentiation $W^{m+1,p}(I) \to W^{m,p}(I)$, $u \mapsto u'$, as a linear map. -/
def derivₗ : SobolevIntervalLp (m + 1) p I →ₗ[ℝ] SobolevIntervalLp m p I where
  toFun u := mk (fun j ↦ deriv u j.succ) fun j ↦ by
    have h0 := hasWeakDerivOn_deriv_succ u 0
    have h1 := hasWeakIteratedDerivOn_deriv u j.succ
    rw [Fin.castSucc_zero] at h0
    rw [Fin.val_succ, ← deriv_zero] at h1
    exact h0.hasWeakIteratedDerivOn_of_succ h1
  map_add' u v := ext fun j ↦ by simp only [deriv_mk, deriv_add]
  map_smul' c u := ext fun j ↦ by simp only [deriv_mk, deriv_smul, RingHom.id_apply]

omit [Fact (1 ≤ p)] in
/-- For $u \in W^{m+1,p}(I)$ and $j \le m$, the $j$-th weak derivative of $u'$
(`SobolevIntervalLp.derivₗ`) is $u^{(j+1)}$. -/
@[simp]
theorem deriv_derivₗ (u : SobolevIntervalLp (m + 1) p I) (j : Fin (m + 1)) :
    deriv (derivₗ m p I u) j = deriv u j.succ := rfl

/-- For $1 \le p \le \infty$ and $u \in W^{m+1,p}(I)$, $\|u'\|_{W^{m,p}} \le \|u\|_{W^{m+1,p}}$. -/
theorem norm_derivₗ_le (u : SobolevIntervalLp (m + 1) p I) : ‖derivₗ m p I u‖ ≤ ‖u‖ :=
  norm_le_of_deriv_eq u _ (Fin.succ_injective _) (deriv_derivₗ u)

variable (m p I) in
/-- **Weak differentiation** $d/dx : W^{m+1,p}(I) \to W^{m,p}(I)$, $u \mapsto u'$, as a continuous
linear map of norm at most $1$, for $1 \le p \le \infty$. -/
def derivCLM : SobolevIntervalLp (m + 1) p I →L[ℝ] SobolevIntervalLp m p I :=
  (derivₗ m p I).mkContinuous 1 fun u ↦ by rw [one_mul]; exact norm_derivₗ_le u

/-- For $u \in W^{m+1,p}(I)$ and $j \le m$, the $j$-th weak derivative of $u'$
(`SobolevIntervalLp.derivCLM`) is $u^{(j+1)}$. -/
@[simp]
theorem deriv_derivCLM (u : SobolevIntervalLp (m + 1) p I) (j : Fin (m + 1)) :
    deriv (derivCLM m p I u) j = deriv u j.succ := rfl

/-- For $1 \le p \le \infty$, the operator norm of $d/dx : W^{m+1,p}(I) \to W^{m,p}(I)$ is at most
$1$. -/
theorem norm_derivCLM_le : ‖derivCLM m p I‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

variable (m p I) in
/-- The inclusion $W^{m+1,p}(I) \to W^{m,p}(I)$, which forgets the top derivative, as a linear map.
-/
def inclusionₗ : SobolevIntervalLp (m + 1) p I →ₗ[ℝ] SobolevIntervalLp m p I where
  toFun u := mk (fun j ↦ deriv u j.castSucc) fun j ↦ by
    have h1 := hasWeakIteratedDerivOn_deriv u j.castSucc
    rw [Fin.val_castSucc, ← deriv_zero] at h1
    rw [Fin.castSucc_zero]
    exact h1
  map_add' u v := ext fun j ↦ by simp only [deriv_mk, deriv_add]
  map_smul' c u := ext fun j ↦ by simp only [deriv_mk, deriv_smul, RingHom.id_apply]

omit [Fact (1 ≤ p)] in
/-- For $u \in W^{m+1,p}(I)$ and $j \le m$, the $j$-th weak derivative of the image of $u$ under
`SobolevIntervalLp.inclusionₗ` is $u^{(j)}$. -/
@[simp]
theorem deriv_inclusionₗ (u : SobolevIntervalLp (m + 1) p I) (j : Fin (m + 1)) :
    deriv (inclusionₗ m p I u) j = deriv u j.castSucc := rfl

/-- For $1 \le p \le \infty$ and $u \in W^{m+1,p}(I)$, the image of $u$ in $W^{m,p}(I)$ has norm at
most $\|u\|_{W^{m+1,p}}$. -/
theorem norm_inclusionₗ_le (u : SobolevIntervalLp (m + 1) p I) : ‖inclusionₗ m p I u‖ ≤ ‖u‖ :=
  norm_le_of_deriv_eq u _ (Fin.castSucc_injective _) (deriv_inclusionₗ u)

variable (m p I) in
/-- **The inclusion** $W^{m+1,p}(I) \to W^{m,p}(I)$, which forgets the top derivative, as a
continuous linear map of norm at most $1$, for $1 \le p \le \infty$. -/
def inclusionCLM : SobolevIntervalLp (m + 1) p I →L[ℝ] SobolevIntervalLp m p I :=
  (inclusionₗ m p I).mkContinuous 1 fun u ↦ by rw [one_mul]; exact norm_inclusionₗ_le u

/-- For $u \in W^{m+1,p}(I)$ and $j \le m$, the $j$-th weak derivative of the image of $u$ under
`SobolevIntervalLp.inclusionCLM` is $u^{(j)}$. -/
@[simp]
theorem deriv_inclusionCLM (u : SobolevIntervalLp (m + 1) p I) (j : Fin (m + 1)) :
    deriv (inclusionCLM m p I u) j = deriv u j.castSucc := rfl

/-- For $u \in W^{m+1,p}(I)$, the image of $u$ in $W^{m,p}(I)$ has the same function as $u$. -/
theorem fn_inclusionCLM (u : SobolevIntervalLp (m + 1) p I) : fn (inclusionCLM m p I u) = fn u :=
  rfl

/-- For $1 \le p \le \infty$, the operator norm of the inclusion $W^{m+1,p}(I) \to W^{m,p}(I)$ is at
most $1$. -/
theorem norm_inclusionCLM_le : ‖inclusionCLM m p I‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end SobolevIntervalLp

/-! ### Test functions on an open subset of the line -/

namespace TestFunction

variable {I : Opens ℝ}

/-- A test function on an open set $I \subseteq \mathbb{R}$ is integrable on $\mathbb{R}$ for
Lebesgue measure. -/
theorem integrable_volume (φ : 𝓓(I, ℝ)) : Integrable φ :=
  φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

/-- For a test function $\psi$ on $I$ and any function $g$,
$\int_I \psi g = \int_{\mathbb{R}} \psi g$. -/
theorem integral_eq_setIntegral (ψ : 𝓓(I, ℝ)) (g : ℝ → ℝ) :
    ∫ x in (I : Set ℝ), ψ x * g x = ∫ x, ψ x * g x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
    rw [ψ.eq_zero_of_notMem hx, zero_mul]

/-- Let $\psi$ be a test function on $I$ with nonempty support. There are $l, h \in I$ with
$l \le h$ such that the support of $\psi$ lies in $[l, h]$. -/
theorem exists_mem_tsupport_subset_Icc (ψ : 𝓓(I, ℝ)) (hne : (tsupport ψ).Nonempty) :
    ∃ lo hi : ℝ, lo ∈ I ∧ hi ∈ I ∧ lo ≤ hi ∧ tsupport ψ ⊆ Icc lo hi := by
  obtain ⟨lo, hlo⟩ := ψ.hasCompactSupport.exists_isLeast hne
  obtain ⟨hi, hhi⟩ := ψ.hasCompactSupport.exists_isGreatest hne
  exact ⟨lo, hi, ψ.tsupport_subset hlo.1, ψ.tsupport_subset hhi.1, hlo.2 hhi.1,
    fun t ht ↦ ⟨hlo.2 ht, hhi.2 ht⟩⟩

/-- Let $\psi$ be a test function on $I$ and let $y_0 \in I$. There are $l, h \in I$ with $l \le h$
such that the support of $\psi$ lies in $(l, h)$, so that $\psi(l) = \psi(h) = 0$.

The point $y_0$ serves when the support is empty. -/
theorem exists_mem_tsupport_subset_Ioo (ψ : 𝓓(I, ℝ)) {y₀ : ℝ} (hy₀ : y₀ ∈ I) :
    ∃ lo hi : ℝ, lo ∈ I ∧ hi ∈ I ∧ lo ≤ hi ∧ tsupport ψ ⊆ Ioo lo hi := by
  obtain ⟨lo, hi, hlo, hhi, hlohi, hsupp⟩ : ∃ lo hi : ℝ, lo ∈ I ∧ hi ∈ I ∧ lo ≤ hi ∧
      tsupport ψ ⊆ Icc lo hi := by
    by_cases hne : (tsupport ψ).Nonempty
    · exact ψ.exists_mem_tsupport_subset_Icc hne
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨y₀, y₀, hy₀, hy₀, le_rfl, hne ▸ empty_subset _⟩
  obtain ⟨εl, hεl, hl⟩ := Metric.isOpen_iff.1 I.isOpen lo hlo
  obtain ⟨εh, hεh, hh⟩ := Metric.isOpen_iff.1 I.isOpen hi hhi
  refine ⟨lo - εl / 2, hi + εh / 2, hl ?_, hh ?_, by linarith, hsupp.trans ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  · exact Icc_subset_Ioo (by linarith) (by linarith)

/-- Let $\psi$ be a test function on $I$ with $\int_{\mathbb{R}} \psi = 0$, and let the support of
$\psi$ lie in $[l, h]$. Then the primitive $x \mapsto \int_{-\infty}^x \psi$ vanishes outside
$[l, h]$.

To the left of $l$ the integrand vanishes, and to the right of $h$ the total integral vanishes. -/
theorem support_integral_Iic_subset (ψ : 𝓓(I, ℝ)) (hψ : ∫ x, ψ x = 0) {lo hi : ℝ}
    (hsupp : tsupport ψ ⊆ Icc lo hi) :
    Function.support (fun x ↦ ∫ t in Iic x, ψ t) ⊆ Icc lo hi := by
  have hzero : ∀ t, t ∉ Icc lo hi → ψ t = 0 := fun t ht ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ ht (hsupp h)
  intro x hx
  by_contra hxI
  apply hx
  rcases not_and_or.1 (mem_Icc.not.1 hxI) with hxlo | hxhi
  · exact setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦
      hzero t fun htI ↦ hxlo (htI.1.trans ht)
  · change ∫ t in Iic x, ψ t = 0
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Iic x) fun t ht ↦
      hzero t fun htI ↦ hxhi ((not_le.1 ht).le.trans htI.2)]
    exact hψ

/-- For a test function $\psi$ on $I$, the primitive $x \mapsto \int_{-\infty}^x \psi$ is
differentiable at every $x$ with derivative $\psi(x)$. -/
theorem hasDerivAt_integral_Iic (ψ : 𝓓(I, ℝ)) (x : ℝ) :
    HasDerivAt (fun x ↦ ∫ t in Iic x, ψ t) (ψ x) x := by
  have e : (fun x ↦ ∫ t in Iic x, ψ t)
      = fun x ↦ (∫ t in Iic 0, ψ t) + ∫ t in (0 : ℝ)..x, ψ t := by
    funext x
    rw [← intervalIntegral.integral_Iic_sub_Iic ψ.integrable_volume.integrableOn
      ψ.integrable_volume.integrableOn]
    ring
  rw [e]
  exact (ψ.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt.const_add _

/-- **The primitive of a test function with zero mean is a test function, on any open interval.**
Let $I$ be an open interval and let $\psi$ be a test function on $I$ with
$\int_{\mathbb{R}} \psi = 0$. Then $x \mapsto \int_{-\infty}^x \psi$ is a test function on $I$.

The primitive is smooth with derivative $\psi$. It vanishes to the left of the support of
$\psi$, and to the right of it because the total integral vanishes. So its support lies in the
convex hull of the support of $\psi$, which lies in $I$ because $I$ is an interval. As a
consequence, the derivatives of the test functions are exactly the test functions of zero mean,
which is the fact behind du Bois-Reymond's lemma (the proof of Lemma 8.1 of
[brezis2011functional]). "Open interval" is the hypothesis `(I : Set ℝ).OrdConnected`. -/
def primitiveIic (hI : (I : Set ℝ).OrdConnected) (ψ : 𝓓(I, ℝ)) (hψ : ∫ x, ψ x = 0) :
    𝓓(I, ℝ) where
  toFun x := ∫ t in Iic x, ψ t
  contDiff' := by
    have hd : deriv (fun x ↦ ∫ t in Iic x, ψ t) = ψ :=
      funext fun x ↦ (ψ.hasDerivAt_integral_Iic x).deriv
    exact contDiff_infty_iff_deriv.2 ⟨fun x ↦ (ψ.hasDerivAt_integral_Iic x).differentiableAt,
      by rw [hd]; exact ψ.contDiff⟩
  hasCompactSupport' := by
    obtain ⟨lo, hi, hsupp⟩ : ∃ lo hi : ℝ, tsupport ψ ⊆ Icc lo hi := by
      obtain ⟨C, hC⟩ := ψ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      exact ⟨-C, C, hC.trans fun t ht ↦ by
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at ht; exact ht⟩
    exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (ψ.support_integral_Iic_subset hψ hsupp)
  tsupport_subset' := by
    by_cases hne : (tsupport ψ).Nonempty
    · obtain ⟨lo, hi, hlo, hhi, -, hsupp⟩ := ψ.exists_mem_tsupport_subset_Icc hne
      exact (closure_minimal (ψ.support_integral_Iic_subset hψ hsupp) isClosed_Icc).trans
        (hI.out hlo hhi)
    · rw [Set.not_nonempty_iff_eq_empty, tsupport_eq_empty_iff] at hne
      have : (fun x ↦ ∫ t in Iic x, ψ t) = 0 := by
        funext x
        simp [show (ψ : ℝ → ℝ) = 0 from hne]
      rw [this, tsupport_zero]
      exact empty_subset _

/-- The test function `TestFunction.primitiveIic hI ψ hψ` is the function
$x \mapsto \int_{-\infty}^x \psi$. -/
@[simp]
theorem primitiveIic_coe (hI : (I : Set ℝ).OrdConnected) (ψ : 𝓓(I, ℝ)) (hψ : ∫ x, ψ x = 0) :
    (primitiveIic hI ψ hψ : ℝ → ℝ) = fun x ↦ ∫ t in Iic x, ψ t := rfl

/-- The derivative of `TestFunction.primitiveIic hI ψ hψ` is $\psi$. -/
theorem deriv_primitiveIic (hI : (I : Set ℝ).OrdConnected) (ψ : 𝓓(I, ℝ)) (hψ : ∫ x, ψ x = 0) :
    deriv (primitiveIic hI ψ hψ) = ψ :=
  funext fun x ↦ (ψ.hasDerivAt_integral_Iic x).deriv

end TestFunction

namespace TopologicalSpace.Opens

variable {I : Opens ℝ}

/-- If the open set $I \subseteq \mathbb{R}$ is nonempty, there is a test function $\psi$ on $I$
with $\int_{\mathbb{R}} \psi = 1$. -/
theorem exists_testFunction_integral_eq_one (hI : (I : Set ℝ).Nonempty) :
    ∃ ψ : 𝓓(I, ℝ), ∫ x, ψ x = 1 := by
  obtain ⟨x₀, hx₀⟩ := hI
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 I.isOpen x₀ hx₀
  let φ : ContDiffBump x₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨⟨φ.normed volume, φ.contDiff_normed (n := ⊤), φ.hasCompactSupport_normed, ?_⟩,
    φ.integral_normed⟩
  rw [φ.tsupport_normed_eq]
  refine (Metric.closedBall_subset_ball ?_).trans hball
  change ε / 2 < ε
  linarith

variable (I) in
/-- A chosen test function on $I$ with integral $1$ if $I$ is nonempty, and $0$ if $I$ is empty.

It is the weight that defines the constant of the canonical continuous representative
`SobolevIntervalLp.rep`. -/
def testFunctionOne : 𝓓(I, ℝ) := by
  classical
  exact if h : (I : Set ℝ).Nonempty then Classical.choose (exists_testFunction_integral_eq_one h)
    else 0

/-- If $I$ is nonempty, the test function `TopologicalSpace.Opens.testFunctionOne I` has integral
$1$. -/
theorem integral_testFunctionOne (hI : (I : Set ℝ).Nonempty) :
    ∫ x, testFunctionOne I x = 1 := by
  simp only [testFunctionOne, hI, ↓reduceDIte]
  exact Classical.choose_spec (exists_testFunction_integral_eq_one hI)

variable (I) in
/-- A chosen point of $I$ if $I$ is nonempty, and $0$ if $I$ is empty.

It is the base point of the canonical continuous representative `SobolevIntervalLp.rep`. -/
def basePoint : ℝ := by
  classical
  exact if h : (I : Set ℝ).Nonempty then h.some else 0

/-- If $I$ is nonempty, the point `TopologicalSpace.Opens.basePoint I` lies in $I$. -/
theorem basePoint_mem (hI : (I : Set ℝ).Nonempty) : basePoint I ∈ I := by
  simp only [basePoint, hI, ↓reduceDIte]
  exact hI.some_mem

end TopologicalSpace.Opens

/-! ### du Bois-Reymond's lemma -/

/-- **du Bois-Reymond's lemma on an open interval.** Let $I$ be an open interval and let $f$ have
the weak derivative $0$ on $I$. Then there is a constant $c$ with $f = c$ almost everywhere on
$I$. This is Lemma 8.1 of [brezis2011functional].

The constant is $c = \int \psi_0 f$ for a fixed test function $\psi_0$ of integral $1$. For any
test function $\varphi$, the function $\varphi - (\int \varphi) \psi_0$ has zero mean, so its
primitive is a test function (`TestFunction.primitiveIic`) whose derivative it is. Testing the
hypothesis against that primitive gives $\int \varphi (f - c) = 0$, and the generalized
variational lemma `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` finishes the proof. -/
theorem HasWeakDerivOn.exists_ae_eq_const {I : Opens ℝ} (hI : (I : Set ℝ).OrdConnected)
    {f : ℝ → ℝ} (h : HasWeakDerivOn f 0 I) : ∃ c : ℝ, f =ᵐ[volume.restrict I] fun _ ↦ c := by
  rcases (I : Set ℝ).eq_empty_or_nonempty with hI0 | hne
  · refine ⟨0, ?_⟩
    rw [hI0, Measure.restrict_empty, ae_zero]
    exact Filter.eventually_bot
  obtain ⟨ψ₀, hψ₀⟩ := I.exists_testFunction_integral_eq_one hne
  refine ⟨∫ x in (I : Set ℝ), ψ₀ x * f x, ?_⟩
  set c := ∫ x in (I : Set ℝ), ψ₀ x * f x with hc
  have key : ∀ᵐ x, x ∈ (I : Set ℝ) → f x - c = 0 := by
    refine I.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (h.locallyIntegrableOn.sub (continuous_const.locallyIntegrable.locallyIntegrableOn _))
      fun g hg h'g hgs ↦ ?_
    set φ : 𝓓(I, ℝ) := ⟨g, hg, h'g, hgs⟩ with hφ
    set m := ∫ x, φ x with hm
    have hmean : ∫ x, (φ - m • ψ₀) x = 0 := by
      simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_sub φ.integrable_volume (ψ₀.integrable_volume.const_mul m), integral_const_mul,
        hψ₀]
      simp [hm]
    have hχ := h.integral_deriv_mul (TestFunction.primitiveIic hI (φ - m • ψ₀) hmean)
    rw [TestFunction.deriv_primitiveIic] at hχ
    simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, mul_zero, integral_zero, neg_zero, sub_mul, mul_assoc] at hχ
    have i1 : IntegrableOn (fun x ↦ φ x * f x) I := (h.integrable_smul φ).integrableOn
    have i2 : IntegrableOn (fun x ↦ ψ₀ x * f x) I := (h.integrable_smul ψ₀).integrableOn
    rw [integral_sub i1 (i2.const_mul m), integral_const_mul, sub_eq_zero] at hχ
    have i3 : Integrable (fun x ↦ g x * f x) := h.integrable_smul φ
    have i4 : Integrable (fun x ↦ g x * c) := φ.integrable_volume.mul_const c
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub i3 i4, integral_mul_const]
    change (∫ x, φ x * f x) - (∫ x, φ x) * c = 0
    rw [← φ.integral_eq_setIntegral, hχ, ← hm, sub_self]
  exact (ae_restrict_iff' I.isOpen.measurableSet).2
    (key.mono fun x hx hxI ↦ sub_eq_zero.1 (hx hxI))

/-! ### Primitives of locally integrable functions -/

section Primitive

variable {w : ℝ → ℝ} {y₀ : ℝ}

/-- Let $s \subseteq \mathbb{R}$ and $x_0 \in s$. There are $b_1, b_2 \in s$ with
$b_1 \le x_0 \le b_2$ such that $[b_1, b_2]$ is a neighbourhood of $x_0$ within $s$. -/
theorem exists_Icc_mem_nhdsWithin {s : Set ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ s) :
    ∃ b₁ ∈ s, ∃ b₂ ∈ s, b₁ ≤ x₀ ∧ x₀ ≤ b₂ ∧ Icc b₁ b₂ ∈ 𝓝[s] x₀ := by
  have left : ∃ b₁ ∈ s, b₁ ≤ x₀ ∧ ∃ l < x₀, ∀ y ∈ s, l < y → b₁ ≤ y := by
    by_cases h : ∃ b ∈ s, b < x₀
    · obtain ⟨b, hb, hbx⟩ := h
      exact ⟨b, hb, hbx.le, b, hbx, fun y _ hy ↦ hy.le⟩
    · push Not at h
      exact ⟨x₀, hx₀, le_rfl, x₀ - 1, by linarith, fun y hy _ ↦ h y hy⟩
  have right : ∃ b₂ ∈ s, x₀ ≤ b₂ ∧ ∃ r > x₀, ∀ y ∈ s, y < r → y ≤ b₂ := by
    by_cases h : ∃ b ∈ s, x₀ < b
    · obtain ⟨b, hb, hbx⟩ := h
      exact ⟨b, hb, hbx.le, b, hbx, fun y _ hy ↦ hy.le⟩
    · push Not at h
      exact ⟨x₀, hx₀, le_rfl, x₀ + 1, by linarith, fun y hy _ ↦ h y hy⟩
  obtain ⟨b₁, hb₁s, hb₁, l, hl, hl'⟩ := left
  obtain ⟨b₂, hb₂s, hb₂, r, hr, hr'⟩ := right
  refine ⟨b₁, hb₁s, b₂, hb₂s, hb₁, hb₂, mem_nhdsWithin.2 ⟨Ioo l r, isOpen_Ioo, ⟨hl, hr⟩, ?_⟩⟩
  rintro y ⟨hyU, hys⟩
  exact ⟨hl' y hys hyU.1, hr' y hys hyU.2⟩

/-- Let $w$ be integrable between any two points of a set $s \subseteq \mathbb{R}$, and let
$x, y, z \in s$. Then $w$ is integrable between $\min\{x, y, z\}$ and $\max\{x, y, z\}$. -/
theorem intervalIntegrable_min_max_of_forall {s : Set ℝ}
    (hw : ∀ x ∈ s, ∀ y ∈ s, IntervalIntegrable w volume x y) {x y z : ℝ} (hx : x ∈ s)
    (hy : y ∈ s) (hz : z ∈ s) :
    IntervalIntegrable w volume (min x (min y z)) (max x (max y z)) := by
  refine hw _ ?_ _ ?_
  · rcases min_choice x (min y z) with h | h
    · rw [h]; exact hx
    · rw [h]; rcases min_choice y z with h' | h' <;> rw [h'] <;> assumption
  · rcases max_choice x (max y z) with h | h
    · rw [h]; exact hx
    · rw [h]; rcases max_choice y z with h' | h' <;> rw [h'] <;> assumption

/-- Let $w$ be integrable between any two points of a set $s \subseteq \mathbb{R}$, and let
$y_0 \in s$. For every constant $c$, the primitive $x \mapsto c + \int_{y_0}^x w$ is continuous
on $s$. -/
theorem continuousOn_integral_of_intervalIntegrable {s : Set ℝ} (hy₀ : y₀ ∈ s)
    (hw : ∀ x ∈ s, ∀ y ∈ s, IntervalIntegrable w volume x y) (c : ℝ) :
    ContinuousOn (fun x ↦ c + ∫ t in y₀..x, w t) s := by
  intro x₀ hx₀
  obtain ⟨b₁, hb₁s, b₂, hb₂s, -, -, hmem⟩ := exists_Icc_mem_nhdsWithin hx₀
  refine continuousWithinAt_const.add ?_
  refine (intervalIntegral.continuousWithinAt_primitive (measure_singleton x₀)
    ?_).mono_of_mem_nhdsWithin hmem
  refine hw _ ?_ _ ?_
  · rcases min_choice y₀ b₁ with h | h <;> rw [h] <;> assumption
  · rcases max_choice y₀ b₂ with h | h <;> rw [h] <;> assumption

/-- Let $w$ be integrable between any two points of a set $s \subseteq \mathbb{R}$, and let
$y_0 \in s$. For every constant $c$ and all $x, y \in s$, the primitive
$t \mapsto c + \int_{y_0}^t w$ is absolutely continuous on the interval between $x$ and $y$. -/
theorem absolutelyContinuousOnInterval_integral_of_intervalIntegrable {s : Set ℝ} (hy₀ : y₀ ∈ s)
    (hw : ∀ x ∈ s, ∀ y ∈ s, IntervalIntegrable w volume x y) (c : ℝ) {x y : ℝ} (hx : x ∈ s)
    (hy : y ∈ s) : AbsolutelyContinuousOnInterval (fun t ↦ c + ∫ r in y₀..t, w r) x y := by
  have h := intervalIntegrable_min_max_of_forall hw hy₀ hx hy
  have hle : min y₀ (min x y) ≤ max y₀ (max x y) :=
    (min_le_left _ _).trans (le_max_left _ _)
  have hmem : ∀ z, z = y₀ ∨ z = x ∨ z = y → z ∈ uIcc (min y₀ (min x y)) (max y₀ (max x y)) := by
    rintro z (rfl | rfl | rfl) <;> rw [uIcc_of_le hle]
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
    · exact ⟨(min_le_right _ _).trans (min_le_left _ _), (le_max_left _ _).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (min_le_right _ _),
        (le_max_right _ _).trans (le_max_right _ _)⟩
  refine (contDiffOn_const (c := c)).absolutelyContinuousOnInterval.fun_add
    ((h.absolutelyContinuousOnInterval_intervalIntegral (hmem y₀ (Or.inl rfl))).mono
      (uIcc_subset_uIcc (hmem x (Or.inr (Or.inl rfl))) (hmem y (Or.inr (Or.inr rfl)))))

/-- Let $I \subseteq \mathbb{R}$ be open and let $P$ be a property of points. If, for all rationals
$q, r \in I$, $P$ holds almost everywhere on $[q, r]$, then $P$ holds almost everywhere on $I$. -/
theorem ae_of_forall_ae_Icc_rat {I : Set ℝ} (hI : IsOpen I) {P : ℝ → Prop}
    (h : ∀ q r : ℚ, (q : ℝ) ∈ I → (r : ℝ) ∈ I → ∀ᵐ x, x ∈ Icc (q : ℝ) r → P x) :
    ∀ᵐ x, x ∈ I → P x := by
  have h' : ∀ᵐ x, ∀ q r : ℚ, (q : ℝ) ∈ I → (r : ℝ) ∈ I → x ∈ Icc (q : ℝ) r → P x := by
    rw [ae_all_iff]
    intro q
    rw [ae_all_iff]
    intro r
    by_cases hq : (q : ℝ) ∈ I
    · by_cases hr : (r : ℝ) ∈ I
      · exact (h q r hq hr).mono fun x hx _ _ ↦ hx
      · exact Eventually.of_forall fun x _ hr' ↦ absurd hr' hr
    · exact Eventually.of_forall fun x hq' ↦ absurd hq' hq
  filter_upwards [h'] with x hx hxI
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hI x hxI
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x - ε < x by linarith)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show x < x + ε by linarith)
  have hq : (q : ℝ) ∈ I := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  have hr : (r : ℝ) ∈ I := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  exact hx q r hq hr ⟨hq2.le, hr1.le⟩

/-- Let $I$ be an open set, let $y_0 \in I$, and let $w$ be integrable between any two points of
$I$. For every constant $c$, the classical derivative of $x \mapsto c + \int_{y_0}^x w$ equals
$w(x)$ for almost every $x \in I$.

This is the Lebesgue differentiation theorem. -/
theorem ae_deriv_integral_eq_of_intervalIntegrable {I : Opens ℝ} (hy₀ : y₀ ∈ I)
    (hw : ∀ x ∈ (I : Set ℝ), ∀ y ∈ (I : Set ℝ), IntervalIntegrable w volume x y) (c : ℝ) :
    ∀ᵐ x, x ∈ (I : Set ℝ) → deriv (fun x ↦ c + ∫ t in y₀..x, w t) x = w x := by
  refine ae_of_forall_ae_Icc_rat I.isOpen fun q r hq hr ↦ ?_
  have h := intervalIntegrable_min_max_of_forall hw hy₀ hq hr
  have hle : min y₀ (min (q : ℝ) r) ≤ max y₀ (max (q : ℝ) r) :=
    (min_le_left _ _).trans (le_max_left _ _)
  filter_upwards [h.ae_hasDerivAt_integral] with x hx hxqr
  rw [uIcc_of_le hle] at hx
  have hx' : x ∈ Icc (min y₀ (min (q : ℝ) r)) (max y₀ (max (q : ℝ) r)) :=
    ⟨((min_le_right _ _).trans (min_le_left _ _)).trans hxqr.1,
      hxqr.2.trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  exact ((hx hx' y₀ ⟨min_le_left _ _, le_max_left _ _⟩).const_add c).deriv

/-- Let $I \subseteq \mathbb{R}$ be an interval and let $w$ be locally integrable on $I$. Then $w$
is integrable between any two points of $I$. -/
theorem MeasureTheory.LocallyIntegrableOn.intervalIntegrable_of_ordConnected {I : Set ℝ}
    (hI : I.OrdConnected) (hw : LocallyIntegrableOn w I) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    IntervalIntegrable w volume x y :=
  (hw.integrableOn_compact_subset (hI.uIcc_subset hx hy) isCompact_uIcc).intervalIntegrable

/-- Let $I$ be an open interval, let $w$ be locally integrable on $I$, and let $y_0 \in I$. For
every constant $c$, the primitive $x \mapsto c + \int_{y_0}^x w$ is continuous on $I$. This is
the statement $v \in C(I)$ of Lemma 8.2 of [brezis2011functional]. -/
theorem MeasureTheory.LocallyIntegrableOn.continuousOn_integral {I : Opens ℝ}
    (hI : (I : Set ℝ).OrdConnected) (hw : LocallyIntegrableOn w I) (hy₀ : y₀ ∈ I) (c : ℝ) :
    ContinuousOn (fun x ↦ c + ∫ t in y₀..x, w t) I :=
  continuousOn_integral_of_intervalIntegrable hy₀
    (fun _ hx _ hy ↦ hw.intervalIntegrable_of_ordConnected hI hx hy) c

/-- Let $I$ be an open interval, let $w$ be locally integrable on $I$, and let $y_0 \in I$. For
every constant $c$ and all $x, y \in I$, the primitive $t \mapsto c + \int_{y_0}^t w$ is
absolutely continuous on the interval between $x$ and $y$. -/
theorem MeasureTheory.LocallyIntegrableOn.absolutelyContinuousOnInterval_integral {I : Opens ℝ}
    (hI : (I : Set ℝ).OrdConnected) (hw : LocallyIntegrableOn w I) (hy₀ : y₀ ∈ I) (c : ℝ)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    AbsolutelyContinuousOnInterval (fun t ↦ c + ∫ r in y₀..t, w r) x y :=
  absolutelyContinuousOnInterval_integral_of_intervalIntegrable hy₀
    (fun _ hx _ hy ↦ hw.intervalIntegrable_of_ordConnected hI hx hy) c hx hy

/-- Let $I$ be an open interval, let $w$ be locally integrable on $I$, and let $y_0 \in I$. For
every constant $c$, the classical derivative of $x \mapsto c + \int_{y_0}^x w$ equals $w(x)$ for
almost every $x \in I$.

This is the Lebesgue differentiation theorem. -/
theorem MeasureTheory.LocallyIntegrableOn.ae_deriv_integral_eq {I : Opens ℝ}
    (hI : (I : Set ℝ).OrdConnected) (hw : LocallyIntegrableOn w I) (hy₀ : y₀ ∈ I) (c : ℝ) :
    ∀ᵐ x, x ∈ (I : Set ℝ) → deriv (fun x ↦ c + ∫ t in y₀..x, w t) x = w x :=
  ae_deriv_integral_eq_of_intervalIntegrable hy₀
    (fun _ hx _ hy ↦ hw.intervalIntegrable_of_ordConnected hI hx hy) c

/-- **The primitive of a locally integrable function is weakly differentiable.** Let $I$ be an open
interval, let $w$ be locally integrable on $I$, and let $y_0 \in I$. For every constant $c$, the
function $w$ is the weak derivative of $x \mapsto c + \int_{y_0}^x w$ on $I$. This is Lemma 8.2
of [brezis2011functional].

The proof is integration by parts for absolutely continuous functions against a test function,
on a compact subinterval of $I$ that contains its support, together with the Lebesgue
differentiation theorem. The Fubini argument of the source is not needed. -/
theorem MeasureTheory.LocallyIntegrableOn.hasWeakDerivOn_integral {I : Opens ℝ}
    (hI : (I : Set ℝ).OrdConnected) (hw : LocallyIntegrableOn w I) (hy₀ : y₀ ∈ I) (c : ℝ) :
    HasWeakDerivOn (fun x ↦ c + ∫ t in y₀..x, w t) w I := by
  have hwi : ∀ x ∈ (I : Set ℝ), ∀ y ∈ (I : Set ℝ), IntervalIntegrable w volume x y :=
    fun _ hx _ hy ↦ hw.intervalIntegrable_of_ordConnected hI hx hy
  refine hasWeakDerivOn_iff.2 ⟨(hw.continuousOn_integral hI hy₀ c).locallyIntegrableOn
    I.isOpen.measurableSet, hw, fun φ ↦ ?_⟩
  obtain ⟨lo, hi, hlo, hhi, hlohi, hsupp⟩ := φ.exists_mem_tsupport_subset_Ioo hy₀
  have hφ : AbsolutelyContinuousOnInterval φ lo hi :=
    (φ.contDiff.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have key := hφ.integral_mul_deriv_eq_deriv_mul
    (hw.absolutelyContinuousOnInterval_integral hI hy₀ c hlo hhi)
  have hφlo : φ lo = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).1.ne rfl
  have hφhi : φ hi = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hsupp h).2.ne rfl
  rw [hφlo, hφhi, zero_mul, zero_mul, sub_zero, zero_sub] at key
  have e1 : ∫ x in lo..hi, φ x * deriv (fun x ↦ c + ∫ t in y₀..x, w t) x
      = ∫ x in lo..hi, φ x * w x := by
    refine intervalIntegral.integral_congr_ae ?_
    have h := intervalIntegrable_min_max_of_forall hwi hy₀ hlo hhi
    have hle : min y₀ (min lo hi) ≤ max y₀ (max lo hi) :=
      (min_le_left _ _).trans (le_max_left _ _)
    filter_upwards [h.ae_hasDerivAt_integral] with x hx hxI
    rw [uIoc_of_le hlohi] at hxI
    rw [uIcc_of_le hle] at hx
    have hx' : x ∈ Icc (min y₀ (min lo hi)) (max y₀ (max lo hi)) :=
      ⟨((min_le_right _ _).trans (min_le_left _ _)).trans hxI.1.le,
        hxI.2.trans ((le_max_right _ _).trans (le_max_right _ _))⟩
    rw [((hx hx' y₀ ⟨min_le_left _ _, le_max_left _ _⟩).const_add c).deriv]
  have hsub : Ioo lo hi ⊆ (I : Set ℝ) := Ioo_subset_Icc_self.trans (hI.out hlo hhi)
  have e2 : ∫ x in (I : Set ℝ), deriv φ x * (c + ∫ t in y₀..x, w t)
      = ∫ x in lo..hi, deriv φ x * (c + ∫ t in y₀..x, w t) := by
    rw [intervalIntegral.integral_of_le hlohi, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero I.isOpen.measurableSet hsub
      fun x hx ↦ ?_
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx.2 (hsupp (tsupport_deriv_subset h)), zero_mul]
  have e3 : ∫ x in (I : Set ℝ), φ x * w x = ∫ x in lo..hi, φ x * w x := by
    rw [intervalIntegral.integral_of_le hlohi, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero I.isOpen.measurableSet hsub
      fun x hx ↦ ?_
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx.2 (hsupp h), zero_mul]
  rw [e2, e3, ← e1, key, neg_neg]

end Primitive

/-! ### The absolutely continuous representative -/

section Representative

variable {I : Opens ℝ} {p : ℝ≥0∞} {f w : ℝ → ℝ} {y₀ : ℝ}

/-- **The representation of a weakly differentiable function by a primitive.** Let $I$ be an open
interval, let $f$ have the weak derivative $w$ on $I$, and let $y_0 \in I$. Then there is a
constant $c$ such that
$$f(x) = c + \int_{y_0}^x w(t)\, dt \quad \text{for almost every } x \in I.$$
This is the core of Theorem 8.2 of [brezis2011functional].

The difference of $f$ and the primitive has weak derivative $0$ by Lemma 8.2, so it is almost
everywhere constant by du Bois-Reymond's lemma (Lemma 8.1). -/
theorem HasWeakDerivOn.exists_ae_eq_integral_of_mem (hI : (I : Set ℝ).OrdConnected)
    (h : HasWeakDerivOn f w I) (hy₀ : y₀ ∈ I) :
    ∃ c : ℝ, f =ᵐ[volume.restrict I] fun x ↦ c + ∫ t in y₀..x, w t := by
  have h1 := h.locallyIntegrableOn_weakDeriv.hasWeakDerivOn_integral hI hy₀ 0
  have h2 : HasWeakDerivOn (fun x ↦ f x - (0 + ∫ t in y₀..x, w t)) 0 I :=
    (h.sub h1).congr_ae (Eventually.of_forall fun x ↦ rfl)
      (Eventually.of_forall fun x ↦ sub_self _)
  obtain ⟨c, hc⟩ := h2.exists_ae_eq_const hI
  refine ⟨c, hc.mono fun x hx ↦ ?_⟩
  simp only [zero_add] at hx ⊢
  linarith

/-- Let $1 \le p \le \infty$, let $I$ be an open interval, let $w \in L^p(I)$, let $y_0 \in I$ and
$c \in \mathbb{R}$, and put $v(x) = c + \int_{y_0}^x w$. If $v \in L^p(I)$, then
$v \in W^{1,p}(I)$ and $w$ is the weak derivative of $v$ on $I$. This is Remark 7 of
[brezis2011functional] §8.2. -/
theorem memSobolevIntervalLp_integral [Fact (1 ≤ p)] (hI : (I : Set ℝ).OrdConnected)
    (hw : MemLp w p (volume.restrict I)) (hy₀ : y₀ ∈ I) {c : ℝ}
    (hv : MemLp (fun x ↦ c + ∫ t in y₀..x, w t) p (volume.restrict I)) :
    MemSobolevIntervalLp (fun x ↦ c + ∫ t in y₀..x, w t) 1 p I ∧
      HasWeakDerivOn (fun x ↦ c + ∫ t in y₀..x, w t) w I :=
  have hweak := (hw.locallyIntegrableOn Fact.out).hasWeakDerivOn_integral hI hy₀ c
  ⟨memSobolevIntervalLp_one_iff.2 ⟨hv, w, hweak, hw⟩, hweak⟩

end Representative

/-! ### Open intervals -/

namespace TopologicalSpace.Opens

variable {I : Opens ℝ}

/-- **An open interval of $\mathbb{R}$ is one of five kinds.** Let $I \subseteq \mathbb{R}$ be open
and order connected. Then $I$ is empty, or $I = \mathbb{R}$, or $I = (a, \infty)$ for some $a$,
or $I = (-\infty, b)$ for some $b$, or $I = (a, b)$ for some $a < b$.

Mathlib's `IsPreconnected.mem_intervals` lists the ten shapes of a preconnected set, and
openness excludes the five that contain a finite endpoint. Every argument about unbounded
intervals starts with this case split. -/
theorem eq_intervals_of_ordConnected (hI : (I : Set ℝ).OrdConnected) :
    (I : Set ℝ) = ∅ ∨ (I : Set ℝ) = univ ∨ (∃ a, (I : Set ℝ) = Ioi a) ∨
      (∃ b, (I : Set ℝ) = Iio b) ∨ ∃ a b, a < b ∧ (I : Set ℝ) = Set.Ioo a b := by
  have hmem := hI.isPreconnected.mem_intervals
  simp only [mem_insert_iff, mem_singleton_iff] at hmem
  set a := sInf (I : Set ℝ) with ha
  set b := sSup (I : Set ℝ) with hb
  have hint : interior (I : Set ℝ) = I := I.isOpen.interior_eq
  rcases hmem with h | h | h | h | h | h | h | h | h | h
  · rcases le_or_gt a b with hle | hlt
    · exfalso
      have h1 : a ∈ interior (Icc a b) := by rw [← h, hint, h]; exact left_mem_Icc.2 hle
      rw [interior_Icc] at h1
      exact lt_irrefl _ h1.1
    · exact Or.inl (h.trans (Icc_eq_empty_of_lt hlt))
  · rcases lt_or_ge a b with hlt | hle
    · exfalso
      have h1 : a ∈ interior (Ico a b) := by rw [← h, hint, h]; exact left_mem_Ico.2 hlt
      rw [interior_Ico] at h1
      exact lt_irrefl _ h1.1
    · exact Or.inl (h.trans (Ico_eq_empty_of_le hle))
  · rcases lt_or_ge a b with hlt | hle
    · exfalso
      have h1 : b ∈ interior (Ioc a b) := by rw [← h, hint, h]; exact right_mem_Ioc.2 hlt
      rw [interior_Ioc] at h1
      exact lt_irrefl _ h1.2
    · exact Or.inl (h.trans (Ioc_eq_empty_of_le hle))
  · rcases lt_or_ge a b with hlt | hle
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, hlt, h⟩)))
    · exact Or.inl (h.trans (Set.Ioo_eq_empty_of_le hle))
  · exfalso
    have h1 : a ∈ interior (Ici a) := by rw [← h, hint, h]; exact self_mem_Ici
    rw [interior_Ici] at h1
    exact lt_irrefl _ (mem_Ioi.1 h1)
  · exact Or.inr (Or.inr (Or.inl ⟨_, h⟩))
  · exfalso
    have h1 : b ∈ interior (Iic b) := by rw [← h, hint, h]; exact self_mem_Iic
    rw [interior_Iic] at h1
    exact lt_irrefl _ (mem_Iio.1 h1)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, h⟩)))
  · exact Or.inr (Or.inl h)
  · exact Or.inl h

/-- Let $I$ be an open interval and $c, d \in \mathbb{R}$. Then $I \cap (c, d)$ is empty or equal to
$(a, b)$ for some $a < b$. -/
theorem inf_Ioo_eq_empty_or_exists_eq_Ioo (hI : (I : Set ℝ).OrdConnected) (c d : ℝ) :
    ((I ⊓ Opens.Ioo c d : Opens ℝ) : Set ℝ) = ∅ ∨
      ∃ a b, a < b ∧ ((I ⊓ Opens.Ioo c d : Opens ℝ) : Set ℝ) = Set.Ioo a b := by
  have hKI : ((I ⊓ Opens.Ioo c d : Opens ℝ) : Set ℝ) = (I : Set ℝ) ∩ Set.Ioo c d := rfl
  have hKord : ((I ⊓ Opens.Ioo c d : Opens ℝ) : Set ℝ).OrdConnected := by
    rw [hKI]; exact hI.inter ordConnected_Ioo
  rcases eq_intervals_of_ordConnected hKord with h | h | ⟨a, h⟩ | ⟨b, h⟩ | ⟨a, b, hab, h⟩
  · exact Or.inl h
  · exfalso
    rw [hKI] at h
    have : max c d + 1 ∈ (I : Set ℝ) ∩ Set.Ioo c d := by rw [h]; exact mem_univ _
    linarith [this.2.2, le_max_right c d]
  · exfalso
    rw [hKI] at h
    have : max a d + 1 ∈ (I : Set ℝ) ∩ Set.Ioo c d := by
      rw [h]; exact show a < max a d + 1 by linarith [le_max_left a d]
    linarith [this.2.2, le_max_right a d]
  · exfalso
    rw [hKI] at h
    have : min b c - 1 ∈ (I : Set ℝ) ∩ Set.Ioo c d := by
      rw [h]; exact show min b c - 1 < b by linarith [min_le_left b c]
    linarith [this.2.1, min_le_right b c]
  · exact Or.inr ⟨a, b, hab, h⟩

/-- The frontier of an open interval $I$ is finite. It is the set of the finite endpoints of $I$:
$\{a, b\}$ for $(a, b)$, $\{a\}$ for $(a, \infty)$, $\{b\}$ for $(-\infty, b)$, and empty for
$\mathbb{R}$ and for $\emptyset$. -/
theorem finite_frontier_of_ordConnected (hI : (I : Set ℝ).OrdConnected) :
    (frontier (I : Set ℝ)).Finite := by
  rcases eq_intervals_of_ordConnected hI with h | h | ⟨a, h⟩ | ⟨b, h⟩ | ⟨a, b, hab, h⟩ <;> rw [h]
  · simp
  · simp
  · rw [frontier_Ioi]; exact finite_singleton a
  · rw [frontier_Iio]; exact finite_singleton b
  · rw [_root_.frontier_Ioo hab]; exact (finite_singleton b).insert a

/-- For an open interval $I$, the set $\bar I \setminus I$ has Lebesgue measure $0$. -/
theorem volume_closure_diff_eq_zero (hI : (I : Set ℝ).OrdConnected) :
    volume (closure (I : Set ℝ) \ I) = 0 := by
  have e : closure (I : Set ℝ) \ I = frontier (I : Set ℝ) := by
    rw [frontier, I.isOpen.interior_eq]
  rw [e]
  exact (finite_frontier_of_ordConnected hI).measure_zero volume

/-- The closure of an open interval is an interval. -/
theorem ordConnected_closure (hI : (I : Set ℝ).OrdConnected) :
    (closure (I : Set ℝ)).OrdConnected :=
  hI.isPreconnected.closure.ordConnected

end TopologicalSpace.Opens

/-- Let $1 \le p \le \infty$, let $I$ be an open interval, and let $w \in L^p(I)$. Then $w$ is
integrable between any two points of the closure $\bar I$.

On the bounded piece $[x, y] \cap I$, $L^p \subseteq L^1$, and $[x, y] \setminus I$ is a null
set. -/
theorem MeasureTheory.MemLp.intervalIntegrable_of_mem_closure {I : Opens ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hI : (I : Set ℝ).OrdConnected) {w : ℝ → ℝ} (hw : MemLp w p (volume.restrict I))
    {x y : ℝ} (hx : x ∈ closure (I : Set ℝ)) (hy : y ∈ closure (I : Set ℝ)) :
    IntervalIntegrable w volume x y := by
  have hsub : uIcc x y ⊆ closure (I : Set ℝ) := (I.ordConnected_closure hI).uIcc_subset hx hy
  refine IntegrableOn.intervalIntegrable ?_
  have h1 : IntegrableOn w (uIcc x y ∩ I) := by
    have := hw.restrict (uIcc x y)
    rw [Measure.restrict_restrict measurableSet_uIcc] at this
    have hfin : Fact (volume (uIcc x y ∩ I) < ⊤) :=
      ⟨(measure_mono inter_subset_left).trans_lt measure_Icc_lt_top⟩
    exact this.integrable Fact.out
  have h2 : IntegrableOn w (uIcc x y \ I) := by
    have : volume (uIcc x y \ I) = 0 :=
      measure_mono_null (sdiff_subset_sdiff_left hsub) (I.volume_closure_diff_eq_zero hI)
    rw [IntegrableOn, Measure.restrict_eq_zero.2 this]
    exact integrable_zero_measure
  simpa only [inter_union_sdiff] using h1.union h2

/-! ### The continuous representative -/

namespace SobolevIntervalLp

variable {m : ℕ} {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

/-- Let $1 \le p \le \infty$, let $I$ be an open interval, let $u \in W^{m,p}(I)$ and $j \le m$.
Then $u^{(j)}$ is integrable between any two points of the closure $\bar I$. -/
theorem intervalIntegrable_deriv (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp m p I)
    (j : Fin (m + 1)) {x y : ℝ} (hx : x ∈ closure (I : Set ℝ)) (hy : y ∈ closure (I : Set ℝ)) :
    IntervalIntegrable (deriv u j) volume x y :=
  (memLp_deriv u j).intervalIntegrable_of_mem_closure hI hx hy

/-- **The continuous representative.** Let $1 \le p \le \infty$, let $I$ be an open interval,
bounded or not, and let $u \in W^{1,p}(I)$. There is a function $g$, continuous on the closure
$\bar I$, that agrees with $u$ almost everywhere on $I$ and satisfies
$$g(y) - g(x) = \int_x^y u'(t)\, dt \quad \text{for all } x, y \in \bar I.$$
This is Theorem 8.2 of [brezis2011functional].

The core is `HasWeakDerivOn.exists_ae_eq_integral_of_mem`. Continuity up to a finite endpoint
holds because $u' \in L^p(I)$ is integrable on every bounded piece of $I$. The canonical choice
of $g$, linear in $u$, is `SobolevIntervalLp.rep`. -/
theorem exists_continuousOn_closure_ae_eq (hI : (I : Set ℝ).OrdConnected)
    (u : SobolevIntervalLp 1 p I) :
    ∃ g : ℝ → ℝ, ContinuousOn g (closure (I : Set ℝ)) ∧ fn u =ᵐ[volume.restrict I] g ∧
      ∀ x ∈ closure (I : Set ℝ), ∀ y ∈ closure (I : Set ℝ),
        g y - g x = ∫ t in x..y, deriv u 1 t := by
  rcases (I : Set ℝ).eq_empty_or_nonempty with hI0 | hne
  · refine ⟨0, continuousOn_const, ?_, fun x hx ↦ ?_⟩
    · rw [hI0, Measure.restrict_empty, ae_zero]
      exact Filter.eventually_bot
    · rw [hI0, closure_empty] at hx
      exact absurd hx (notMem_empty x)
  have hy₀ : I.basePoint ∈ closure (I : Set ℝ) := subset_closure (I.basePoint_mem hne)
  obtain ⟨c, hc⟩ := (hasWeakDerivOn_fn u).exists_ae_eq_integral_of_mem hI (I.basePoint_mem hne)
  have hwi : ∀ x ∈ closure (I : Set ℝ), ∀ y ∈ closure (I : Set ℝ),
      IntervalIntegrable (deriv u 1) volume x y :=
    fun _ hx _ hy ↦ intervalIntegrable_deriv hI u 1 hx hy
  refine ⟨_, continuousOn_integral_of_intervalIntegrable hy₀ hwi c, hc, fun x hx y hy ↦ ?_⟩
  rw [add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hwi _ hy₀ _ hy) (hwi _ hy₀ _ hx)]

/-- The constant of the canonical continuous representative of $u \in W^{1,p}(I)$:
$$\int_{\mathbb{R}} \psi_0(x) \Bigl(u(x) - \int_{y_0}^x u'\Bigr)\, dx,$$
where $\psi_0$ is the test function `TopologicalSpace.Opens.testFunctionOne I` of integral $1$
and $y_0$ is `TopologicalSpace.Opens.basePoint I`.

This choice makes the constant depend linearly on $u$. -/
def repConst (u : SobolevIntervalLp 1 p I) : ℝ :=
  ∫ x, I.testFunctionOne x * (fn u x - ∫ t in I.basePoint..x, deriv u 1 t)

/-- **The canonical continuous representative** $\tilde u$ of $u \in W^{1,p}(I)$, as a function on
all of $\mathbb{R}$: $\tilde u(x) = c_u + \int_{y_0}^x u'$, where $c_u$ is
`SobolevIntervalLp.repConst u` and $y_0$ is `TopologicalSpace.Opens.basePoint I`.

On an open interval $I$, the function $\tilde u$ agrees with $u$ almost everywhere on $I$
(`SobolevIntervalLp.fn_ae_eq_rep`), is continuous on the closure $\bar I$, is absolutely
continuous between any two points of $\bar I$, and satisfies
$\tilde u(y) - \tilde u(x) = \int_x^y u'$ for $x, y \in \bar I$
(`SobolevIntervalLp.rep_sub_rep`). It is the function $\tilde u$ of Theorem 8.2 of
[brezis2011functional], which is unique by Remark 5 there
(`SobolevIntervalLp.rep_eq_of_continuousOn`). -/
def rep (u : SobolevIntervalLp 1 p I) (x : ℝ) : ℝ :=
  repConst u + ∫ t in I.basePoint..x, deriv u 1 t

omit [Fact (1 ≤ p)] in
/-- For $u \in W^{1,p}(I)$, the continuous representative is $\tilde u(x) = c_u + \int_{y_0}^x u'$,
with $c_u$ = `SobolevIntervalLp.repConst u` and $y_0$ = `TopologicalSpace.Opens.basePoint I`. -/
theorem rep_apply (u : SobolevIntervalLp 1 p I) (x : ℝ) :
    rep u x = repConst u + ∫ t in I.basePoint..x, deriv u 1 t := rfl

omit [Fact (1 ≤ p)] in
/-- If a point lies in the closure of an open set $I \subseteq \mathbb{R}$, then $I$ is nonempty. -/
theorem _root_.TopologicalSpace.Opens.nonempty_of_mem_closure {x : ℝ}
    (hx : x ∈ closure (I : Set ℝ)) : (I : Set ℝ).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  rw [h, closure_empty] at hx
  exact hx

/-- Let $1 \le p \le \infty$, let $I$ be an open interval and $u \in W^{1,p}(I)$. The continuous
representative $\tilde u$ is continuous on the closure $\bar I$. -/
theorem continuousOn_rep (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) :
    ContinuousOn (rep u) (closure (I : Set ℝ)) := by
  rcases (I : Set ℝ).eq_empty_or_nonempty with hI0 | hne
  · rw [hI0, closure_empty]
    exact continuousOn_empty _
  exact continuousOn_integral_of_intervalIntegrable (subset_closure (I.basePoint_mem hne))
    (fun _ hx _ hy ↦ intervalIntegrable_deriv hI u 1 hx hy) _

/-- Let $1 \le p \le \infty$, let $I$ be an open interval and $u \in W^{1,p}(I)$. For all
$x, y \in \bar I$, the continuous representative $\tilde u$ is absolutely continuous on the
interval between $x$ and $y$. -/
theorem absolutelyContinuousOnInterval_rep (hI : (I : Set ℝ).OrdConnected)
    (u : SobolevIntervalLp 1 p I) {x y : ℝ} (hx : x ∈ closure (I : Set ℝ))
    (hy : y ∈ closure (I : Set ℝ)) : AbsolutelyContinuousOnInterval (rep u) x y :=
  absolutelyContinuousOnInterval_integral_of_intervalIntegrable
    (subset_closure (I.basePoint_mem (I.nonempty_of_mem_closure hx)))
    (fun _ hx _ hy ↦ intervalIntegrable_deriv hI u 1 hx hy) _ hx hy

/-- **The fundamental theorem of calculus in $W^{1,p}(I)$.** Let $1 \le p \le \infty$, let $I$ be an
open interval and $u \in W^{1,p}(I)$. For all $x, y$ in the closure $\bar I$,
$$\tilde u(y) - \tilde u(x) = \int_x^y u'(t)\, dt.$$
This is the identity of Theorem 8.2 of [brezis2011functional]. -/
theorem rep_sub_rep (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) {x y : ℝ}
    (hx : x ∈ closure (I : Set ℝ)) (hy : y ∈ closure (I : Set ℝ)) :
    rep u y - rep u x = ∫ t in x..y, deriv u 1 t := by
  have hy₀ : I.basePoint ∈ closure (I : Set ℝ) :=
    subset_closure (I.basePoint_mem (I.nonempty_of_mem_closure hx))
  simp only [rep_apply]
  rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_deriv hI u 1 hy₀ hy) (intervalIntegrable_deriv hI u 1 hy₀ hx)]

omit [Fact (1 ≤ p)] in
/-- Let $I$ be an open interval and $u \in W^{1,p}(I)$. The function of $u$ agrees with its
continuous representative $\tilde u$ almost everywhere on $I$.

The constant of `HasWeakDerivOn.exists_ae_eq_integral_of_mem` is `SobolevIntervalLp.repConst u`,
as one sees by integrating the identity against the test function of integral $1$. -/
theorem fn_ae_eq_rep (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) :
    fn u =ᵐ[volume.restrict I] rep u := by
  rcases (I : Set ℝ).eq_empty_or_nonempty with hI0 | hne
  · rw [hI0, Measure.restrict_empty, ae_zero]
    exact Filter.eventually_bot
  obtain ⟨c, hc⟩ := (hasWeakDerivOn_fn u).exists_ae_eq_integral_of_mem hI (I.basePoint_mem hne)
  have hcc : repConst u = c := by
    have e : ∫ x, I.testFunctionOne x * (fn u x - ∫ t in I.basePoint..x, deriv u 1 t)
        = ∫ x, I.testFunctionOne x * c := by
      refine integral_congr_ae ?_
      filter_upwards [(ae_restrict_iff' I.isOpen.measurableSet).1 hc] with x hx
      by_cases hxI : x ∈ (I : Set ℝ)
      · rw [hx hxI]; ring
      · rw [I.testFunctionOne.eq_zero_of_notMem hxI, zero_mul, zero_mul]
    rw [repConst, e, integral_mul_const, I.integral_testFunctionOne hne, one_mul]
  exact hc.trans (Eventually.of_forall fun x ↦ by rw [rep_apply, hcc])

/-- **The continuous representative is unique.** Let $1 \le p \le \infty$, let $I$ be an open
interval and $u \in W^{1,p}(I)$. If $g$ is continuous on the closure $\bar I$ and agrees with
$u$ almost everywhere on $I$, then $\tilde u = g$ on $\bar I$. This is Remark 5 of
[brezis2011functional] §8.2. -/
theorem rep_eq_of_continuousOn (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I)
    {g : ℝ → ℝ} (hg : ContinuousOn g (closure (I : Set ℝ)))
    (hu : fn u =ᵐ[volume.restrict I] g) : EqOn (rep u) g (closure (I : Set ℝ)) :=
  (Measure.eqOn_open_of_ae_eq ((fn_ae_eq_rep hI u).symm.trans hu) I.isOpen
    ((continuousOn_rep hI u).mono subset_closure) (hg.mono subset_closure)).of_subset_closure
    (continuousOn_rep hI u) hg subset_closure subset_rfl

omit [Fact (1 ≤ p)] in
/-- Let $I$ be an open interval and $u \in W^{1,p}(I)$. The continuous representative $\tilde u$ has
the weak derivative $u'$ on $I$. -/
theorem hasWeakDerivOn_rep (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) :
    HasWeakDerivOn (rep u) (deriv u 1) I :=
  (hasWeakDerivOn_fn u).congr_ae (fn_ae_eq_rep hI u) (EventuallyEq.refl _ _)

/-- Let $1 \le p \le \infty$, let $I$ be an open interval and $u \in W^{1,p}(I)$. The classical
derivative of the continuous representative $\tilde u$ equals $u'(x)$ for almost every
$x \in I$. -/
theorem ae_deriv_rep_eq (hI : (I : Set ℝ).OrdConnected) (u : SobolevIntervalLp 1 p I) :
    ∀ᵐ x, x ∈ (I : Set ℝ) → _root_.deriv (rep u) x = deriv u 1 x := by
  rcases (I : Set ℝ).eq_empty_or_nonempty with hI0 | hne
  · exact Eventually.of_forall fun x hx ↦ absurd hx (by rw [hI0]; exact notMem_empty x)
  exact ae_deriv_integral_eq_of_intervalIntegrable (I.basePoint_mem hne)
    (fun _ hx _ hy ↦ intervalIntegrable_deriv hI u 1 (subset_closure hx) (subset_closure hy)) _

/-- Let $1 \le p \le \infty$, let $I$ be an open interval and $u, v \in W^{1,p}(I)$. Then
$\widetilde{u + v} = \tilde u + \tilde v$ on the closure $\bar I$. -/
theorem rep_add (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I) :
    EqOn (rep (u + v)) (rep u + rep v) (closure (I : Set ℝ)) :=
  rep_eq_of_continuousOn hI (u + v) ((continuousOn_rep hI u).add (continuousOn_rep hI v))
    ((SobolevMultiIndex.fn_add u v).trans ((fn_ae_eq_rep hI u).add (fn_ae_eq_rep hI v)))

/-- Let $1 \le p \le \infty$, let $I$ be an open interval, $c \in \mathbb{R}$ and
$u \in W^{1,p}(I)$. Then $\widetilde{c u} = c\, \tilde u$ on the closure $\bar I$. -/
theorem rep_smul (hI : (I : Set ℝ).OrdConnected) (c : ℝ) (u : SobolevIntervalLp 1 p I) :
    EqOn (rep (c • u)) (c • rep u) (closure (I : Set ℝ)) :=
  rep_eq_of_continuousOn hI (c • u) ((continuousOn_rep hI u).const_smul c)
    ((SobolevMultiIndex.fn_smul c u).trans ((fn_ae_eq_rep hI u).const_smul c))

/-- Let $1 \le p \le \infty$, let $I$ be an open interval and $u, v \in W^{1,p}(I)$. Then
$\widetilde{u - v} = \tilde u - \tilde v$ on the closure $\bar I$. -/
theorem rep_sub (hI : (I : Set ℝ).OrdConnected) (u v : SobolevIntervalLp 1 p I) :
    EqOn (rep (u - v)) (rep u - rep v) (closure (I : Set ℝ)) := by
  intro x hx
  have h1 := rep_add hI (u - v) v hx
  rw [sub_add_cancel] at h1
  simp only [Pi.add_apply] at h1
  simp only [Pi.sub_apply]
  linarith

/-- Let $1 \le p \le \infty$, let $I$ be an open interval, let $s$ be a finite index set, and let
$c_j \in \mathbb{R}$ and $\varphi_j \in W^{1,p}(I)$ for $j \in s$. For every $x \in \bar I$, the
continuous representative of $\sum_{j \in s} c_j \varphi_j$ takes the value
$\sum_{j \in s} c_j \tilde\varphi_j(x)$ at $x$. -/
theorem rep_finset_sum (hI : (I : Set ℝ).OrdConnected) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (φ : ι → SobolevIntervalLp 1 p I) {x : ℝ} (hx : x ∈ closure (I : Set ℝ)) :
    rep (∑ j ∈ s, c j • φ j) x = ∑ j ∈ s, c j * rep (φ j) x := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact rep_eq_of_continuousOn hI 0 continuousOn_const SobolevMultiIndex.fn_zero hx
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, rep_add hI _ _ hx, Pi.add_apply,
        rep_smul hI _ _ hx, Pi.smul_apply, smul_eq_mul, ih]

end SobolevIntervalLp

/-! ### Piecewise $C^1$ functions -/

section Piecewise

variable {a : ℝ}

/-- **The fundamental theorem of calculus for a continuous piecewise $C^1$ function.** Let
$a = x_0 < x_1 < \dots < x_{N+1}$, let $g$ be continuous on $[a, x_{N+1}]$ and of class $C^1$ on
each open panel $(x_i, x_{i+1})$, and let $|g'(t)| \le C$ for every $t$ in every open panel.
Then for every node index $j \le N + 1$, $|g'| \le C$ almost everywhere on $(a, x_j)$, and
$$g(t) = g(a) + \int_a^t g'(s)\, ds \quad \text{for all } t \in [a, x_j].$$

Here $g'$ is the classical derivative `deriv g`. The proof is by induction on $j$. The step is
the fundamental theorem of calculus on one panel, where $g$ is continuous up to the ends and
differentiable inside, and continuity of $g$ at the nodes glues the panels. -/
theorem eq_add_integral_deriv_of_piecewise {N : ℕ} {x : Fin (N + 2) → ℝ} (hx : StrictMono x)
    (hxa : x 0 = a) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a (x (Fin.last (N + 1)))))
    (hg' : ∀ j : Fin (N + 1), ContDiffOn ℝ 1 g (Ioo (x j.castSucc) (x j.succ)))
    {C : ℝ} (hbdd : ∀ j : Fin (N + 1), ∀ t ∈ Ioo (x j.castSucc) (x j.succ), |deriv g t| ≤ C) :
    ∀ j : Fin (N + 2), (∀ᵐ t, t ∈ Ioo a (x j) → |deriv g t| ≤ C) ∧
      ∀ t ∈ Icc a (x j), g t = g a + ∫ s in a..t, deriv g s := by
  have hmono : Monotone x := hx.monotone
  have hxa' : ∀ j, a ≤ x j := fun j ↦ hxa ▸ hmono (Fin.zero_le j)
  have hxb' : ∀ j, x j ≤ x (Fin.last (N + 1)) := fun j ↦ hmono (Fin.le_last j)
  intro j
  induction j using Fin.induction with
  | zero =>
    refine ⟨?_, fun t ht ↦ ?_⟩
    · rw [hxa, Ioo_self]
      exact Eventually.of_forall fun t ht ↦ absurd ht (notMem_empty t)
    · rw [hxa, Icc_self, mem_singleton_iff] at ht
      rw [ht, intervalIntegral.integral_same, add_zero]
  | succ j ih =>
    obtain ⟨ihae, ihfun⟩ := ih
    have hlt : x j.castSucc < x j.succ := hx (Fin.castSucc_lt_succ (i := j))
    -- the bound on the new panel, almost everywhere
    have hae : ∀ᵐ t, t ∈ Ioo a (x j.succ) → |deriv g t| ≤ C := by
      have hne : ∀ᵐ t : ℝ, t ≠ x j.castSucc := by simp [ae_iff, measure_singleton]
      filter_upwards [ihae, hne] with t ht htne htI
      rcases lt_or_gt_of_ne htne with h | h
      · exact ht ⟨htI.1, h⟩
      · exact hbdd j t ⟨h, htI.2⟩
    refine ⟨hae, fun t ht ↦ ?_⟩
    rcases le_or_gt t (x j.castSucc) with htj | htj
    · exact ihfun t ⟨ht.1, htj⟩
    -- integrability of the derivative on `(a, x (j+1))`
    have hint : IntegrableOn (deriv g) (Ioo a (x j.succ)) :=
      Measure.integrableOn_of_bounded (M := C) (by simp) (measurable_deriv g).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioo).2 (hae.mono fun t ht htI ↦ by
          rw [Real.norm_eq_abs]; exact ht htI))
    have hint' : ∀ y z, y ∈ Icc a (x j.succ) → z ∈ Icc a (x j.succ) →
        IntervalIntegrable (deriv g) volume y z := fun y z hy hz ↦
      (hint.integrableOn_Icc_of_Ioo.mono_set (uIcc_subset_Icc hy hz)).intervalIntegrable
    -- the fundamental theorem of calculus on `[x j, t]`
    have hftc : ∫ s in (x j.castSucc)..t, deriv g s = g t - g (x j.castSucc) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htj.le
        (hg.mono (Icc_subset_Icc (hxa' _) (ht.2.trans (hxb' _)))) (fun s hs ↦ ?_)
        (hint' _ _ ⟨hxa' _, hlt.le⟩ ht)
      have hs' : s ∈ Ioo (x j.castSucc) (x j.succ) := ⟨hs.1, hs.2.trans_le ht.2⟩
      exact (((hg' j).differentiableOn one_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hs')).hasDerivAt
    have hj := ihfun (x j.castSucc) ⟨hxa' _, le_rfl⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint' _ _ ⟨le_rfl, hxa' _⟩
      ⟨hxa' _, hlt.le⟩) (hint' _ _ ⟨hxa' _, hlt.le⟩ ht), hftc, ← add_assoc, ← hj]
    ring

end Piecewise


section Api

variable {m : ℕ} {p : ℝ≥0∞} {I : Opens ℝ} {f : ℝ → ℝ}

/-- If $f \in W^{m,p}(I)$, then there is an element $u$ of the type `SobolevIntervalLp m p I` whose
function agrees with $f$ almost everywhere on $I$. -/
theorem MemSobolevIntervalLp.exists_sobolevIntervalLp
    (h : MemSobolevIntervalLp f m p I) :
    ∃ u : SobolevIntervalLp m p I, SobolevIntervalLp.fn u =ᵐ[volume.restrict I] f :=
  MemSobolevMultiIndex.exists_sobolevMultiIndex h

end Api

/-! ### Closedness of the weak derivative under limits in $L^p$ -/

section Limits

variable {I : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The derivative of a test function on $I$ lies in $L^q(I)$ for every $q \in [0, \infty]$. -/
theorem TestFunction.memLp_deriv (φ : 𝓓(I, ℝ)) (q : ℝ≥0∞) :
    MemLp (deriv φ) q (volume.restrict I) :=
  (φ.contDiff.continuous_deriv (by simp)).memLp_of_hasCompactSupport φ.hasCompactSupport.deriv

/-- A test function on $I$ lies in $L^q(I)$ for every $q \in [0, \infty]$. -/
theorem TestFunction.memLp' (φ : 𝓓(I, ℝ)) (q : ℝ≥0∞) : MemLp φ q (volume.restrict I) :=
  φ.memLp q _

/-- Every exponent $1 \le p \le \infty$ has the Hölder conjugate exponent $(1 - p^{-1})^{-1}$, which
is $\infty$ for $p = 1$ and $1$ for $p = \infty$. -/
theorem ENNReal.holderConjugate_sub_inv_inv : ENNReal.HolderConjugate p (1 - p⁻¹)⁻¹ := by
  rw [ENNReal.holderConjugate_iff, inv_inv, add_tsub_cancel_of_le (ENNReal.inv_le_one.2 Fact.out)]

/-- **The weak derivative is preserved under limits in $L^p$.** Let $1 \le p \le \infty$, let $w_n$
be the weak derivative of $u_n$ on $I$ for every $n$, and let $u_0, w_0 \in L^p(I)$. If
$u_n \to u_0$ and $w_n \to w_0$ in $L^p(I)$, then $w_0$ is the weak derivative of $u_0$ on $I$.
This is the first clause of Remark 4 of [brezis2011functional] §8.2.

Each side of $\int u_n \varphi' = -\int w_n \varphi$ converges for the fixed test function
$\varphi$ by Hölder's inequality (`MeasureTheory.tendsto_integral_mul_of_tendsto_eLpNorm`),
which also covers $p = \infty$. -/
theorem hasWeakDerivOn_of_tendsto_eLpNorm {u w : ℕ → ℝ → ℝ} {u₀ w₀ : ℝ → ℝ}
    (hu : ∀ n, HasWeakDerivOn (u n) (w n) I) (hu₀ : MemLp u₀ p (volume.restrict I))
    (hw₀ : MemLp w₀ p (volume.restrict I))
    (hlu : Tendsto (fun n ↦ eLpNorm (u n - u₀) p (volume.restrict I)) atTop (𝓝 0))
    (hlw : Tendsto (fun n ↦ eLpNorm (w n - w₀) p (volume.restrict I)) atTop (𝓝 0)) :
    HasWeakDerivOn u₀ w₀ I := by
  -- along a tail, `u n` and `w n` lie in `L^p(I)`
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((hlu.eventually_lt_const zero_lt_one).and (hlw.eventually_lt_const zero_lt_one))
  have hun : ∀ n, MemLp (u (n + N)) p (volume.restrict I) := fun n ↦ by
    have h : MemLp (u (n + N) - u₀) p (volume.restrict I) :=
      memLp_iff.2 ((hN _ (Nat.le_add_left N n)).1.trans ENNReal.one_lt_top)
    simpa only [sub_add_cancel] using h.add hu₀
  have hwn : ∀ n, MemLp (w (n + N)) p (volume.restrict I) := fun n ↦ by
    have h : MemLp (w (n + N) - w₀) p (volume.restrict I) :=
      memLp_iff.2 ((hN _ (Nat.le_add_left N n)).2.trans ENNReal.one_lt_top)
    simpa only [sub_add_cancel] using h.add hw₀
  have hpq : ENNReal.HolderConjugate p (1 - p⁻¹)⁻¹ := ENNReal.holderConjugate_sub_inv_inv
  have hlu' : Tendsto (fun n ↦ eLpNorm (fun x ↦ u (n + N) x - u₀ x) p (volume.restrict I)) atTop
      (𝓝 0) := hlu.comp (tendsto_add_atTop_nat N)
  have hlw' : Tendsto (fun n ↦ eLpNorm (fun x ↦ w (n + N) x - w₀ x) p (volume.restrict I)) atTop
      (𝓝 0) := hlw.comp (tendsto_add_atTop_nat N)
  refine hasWeakDerivOn_iff.2 ⟨hu₀.locallyIntegrableOn Fact.out, hw₀.locallyIntegrableOn Fact.out,
    fun φ ↦ ?_⟩
  have h1 : Tendsto (fun n ↦ ∫ x in (I : Set ℝ), deriv φ x * u (n + N) x) atTop
      (𝓝 (∫ x in (I : Set ℝ), deriv φ x * u₀ x)) :=
    tendsto_integral_mul_of_tendsto_eLpNorm (μ := volume.restrict I) (q := (1 - p⁻¹)⁻¹)
      (a := fun n ↦ u (n + N)) hun hu₀ (φ.memLp_deriv _) hlu'
  have h2 : Tendsto (fun n ↦ ∫ x in (I : Set ℝ), φ x * w (n + N) x) atTop
      (𝓝 (∫ x in (I : Set ℝ), φ x * w₀ x)) :=
    tendsto_integral_mul_of_tendsto_eLpNorm (μ := volume.restrict I) (q := (1 - p⁻¹)⁻¹)
      (a := fun n ↦ w (n + N)) hwn hw₀ (φ.memLp' _) hlw'
  have e : (fun n ↦ ∫ x in (I : Set ℝ), deriv φ x * u (n + N) x)
      = fun n ↦ -∫ x in (I : Set ℝ), φ x * w (n + N) x :=
    funext fun n ↦ (hu _).integral_deriv_mul φ
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2.neg

/-- Let $1 \le p \le \infty$, and let $u_n, u_0 \in W^{m,p}(I)$. If $u_n^{(j)} \to u_0^{(j)}$ in
$L^p(I)$ for every $j \le m$, then $u_n \to u_0$ in $W^{m,p}(I)$.

The norm is dominated by the sum of the norms of the derivatives
(`SobolevIntervalLp.norm_le_sum_norm_deriv`). With `hasWeakDerivOn_of_tendsto_eLpNorm`, this is
the second clause of Remark 4 of [brezis2011functional] §8.2, $\|u_n - u\|_{W^{1,p}} \to 0$. -/
theorem SobolevIntervalLp.tendsto_of_tendsto_deriv {m : ℕ} {u : ℕ → SobolevIntervalLp m p I}
    {u₀ : SobolevIntervalLp m p I}
    (h : ∀ j, Tendsto (fun n ↦ SobolevIntervalLp.deriv (u n) j) atTop
      (𝓝 (SobolevIntervalLp.deriv u₀ j))) :
    Tendsto u atTop (𝓝 u₀) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _)
    (fun n ↦ SobolevIntervalLp.norm_le_sum_norm_deriv (u n - u₀)) ?_
  have : Tendsto (fun n ↦ ∑ j : Fin (m + 1), ‖SobolevIntervalLp.deriv (u n - u₀) j‖) atTop
      (𝓝 (∑ _j : Fin (m + 1), (0 : ℝ))) := by
    refine tendsto_finsetSum _ fun j _ ↦ ?_
    simp only [SobolevIntervalLp.deriv_sub]
    exact tendsto_iff_norm_sub_tendsto_zero.1 (h j)
  simpa using this

end Limits

/-! ### Classical and piecewise classical functions -/

section ClassicalMem

variable {I : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **$C^1$ functions with $L^p$ function and derivative lie in $W^{1,p}(I)$.** Let
$1 \le p \le \infty$, and let $u$ be of class $C^1$ on the open set $I$ with $u \in L^p(I)$ and
$u' \in L^p(I)$. Then $u \in W^{1,p}(I)$, and its classical derivative $u'$ is its weak
derivative on $I$. This is Remark 2 of [brezis2011functional] §8.2. -/
theorem memSobolevIntervalLp_of_contDiffOn {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u I)
    (hup : MemLp u p (volume.restrict I)) (hup' : MemLp (deriv u) p (volume.restrict I)) :
    MemSobolevIntervalLp u 1 p I ∧ HasWeakDerivOn u (deriv u) I :=
  ⟨memSobolevIntervalLp_one_iff.2 ⟨hup, _, hasWeakDerivOn_of_contDiffOn hu, hup'⟩,
    hasWeakDerivOn_of_contDiffOn hu⟩

/-- **$C^1(\bar I) \subseteq W^{1,p}(I)$ for a bounded interval.** Let $a < b$,
$1 \le p \le \infty$, and let $u$ be of class $C^1$ on $[a, b]$. Then $u \in W^{1,p}(a, b)$, and
its classical derivative $u'$ is its weak derivative on $(a, b)$. This is Remark 2 of
[brezis2011functional] §8.2. -/
theorem memSobolevIntervalLp_of_contDiffOn_Icc {a b : ℝ} (hab : a < b) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Icc a b)) :
    MemSobolevIntervalLp u 1 p (Opens.Ioo a b) ∧ HasWeakDerivOn u (deriv u) (Opens.Ioo a b) := by
  have hcont : ContinuousOn (derivWithin u (Icc a b)) (Icc a b) :=
    hu.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  have hae : deriv u =ᵐ[volume.restrict (Ioo a b)] derivWithin u (Icc a b) :=
    (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦
      (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm)
  exact memSobolevIntervalLp_of_contDiffOn (hu.mono Ioo_subset_Icc_self)
    (hu.continuousOn.memLp_top_restrict_Ioo.mono_exponent le_top)
    ((hcont.memLp_top_restrict_Ioo.mono_exponent le_top).ae_eq hae.symm)

/-- **Continuous piecewise $C^1$ functions lie in $W^{1,p}(a, b)$.** Let $1 \le p \le \infty$ and
let $a = x_0 < x_1 < \dots < x_{N+1} = b$ be a partition. Let $g$ be continuous on $[a, b]$ and
of class $C^1$ on each open panel $(x_j, x_{j+1})$, and assume that there is a constant $C$ with
$|g'(t)| \le C$ for every $t$ in every open panel. Then $g \in W^{1,p}(a, b)$, and the classical
derivative $g'$ is the weak derivative of $g$ on $(a, b)$. This is the sentence "more generally"
of the Examples of [brezis2011functional] §8.2.

The values of $g'$ at the nodes do not matter. -/
theorem memSobolevIntervalLp_of_piecewise_contDiffOn {a b : ℝ} {N : ℕ} {x : Fin (N + 2) → ℝ}
    (hx : StrictMono x) (hxa : x 0 = a) (hxb : x (Fin.last (N + 1)) = b) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ j : Fin (N + 1), ContDiffOn ℝ 1 g (Ioo (x j.castSucc) (x j.succ)))
    (hbdd : ∃ C, ∀ j : Fin (N + 1), ∀ t ∈ Ioo (x j.castSucc) (x j.succ), |deriv g t| ≤ C) :
    MemSobolevIntervalLp g 1 p (Opens.Ioo a b) ∧ HasWeakDerivOn g (deriv g) (Opens.Ioo a b) := by
  obtain ⟨C, hC⟩ := hbdd
  have hab : a < b := hxa ▸ hxb ▸ hx Fin.last_pos'
  obtain ⟨hae, hfun⟩ := eq_add_integral_deriv_of_piecewise hx hxa (hxb ▸ hg) hg' hC
    (Fin.last (N + 1))
  rw [hxb] at hae hfun
  have hmem : MemLp (deriv g) p (volume.restrict (Ioo a b)) :=
    MemLp.of_bound (measurable_deriv g).aestronglyMeasurable C
      ((ae_restrict_iff' measurableSet_Ioo).2 (hae.mono fun t ht htI ↦ by
        rw [Real.norm_eq_abs]; exact ht htI))
  have hint : IntegrableOn (deriv g) (Icc a b) :=
    IntegrableOn.integrableOn_Icc_of_Ioo (hmem.integrable Fact.out)
  have hii : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, IntervalIntegrable (deriv g) volume s t :=
    fun s hs t ht ↦ (hint.mono_set (uIcc_subset_Icc hs ht)).intervalIntegrable
  set y₀ := (a + b) / 2 with hy₀
  have hy₀I : y₀ ∈ Ioo a b := ⟨by rw [hy₀]; linarith, by rw [hy₀]; linarith⟩
  have hweak := (hmem.locallyIntegrableOn Fact.out (Ω := Opens.Ioo a b)).hasWeakDerivOn_integral
    Set.ordConnected_Ioo hy₀I (g y₀)
  have hweak' : HasWeakDerivOn g (deriv g) (Opens.Ioo a b) := by
    refine hweak.congr_ae ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall
      fun t ht ↦ ?_)) (EventuallyEq.refl _ _)
    dsimp only
    rw [hfun t (Ioo_subset_Icc_self ht), hfun y₀ (Ioo_subset_Icc_self hy₀I), add_assoc,
      intervalIntegral.integral_add_adjacent_intervals (hii _ (left_mem_Icc.2 hab.le) _
        (Ioo_subset_Icc_self hy₀I)) (hii _ (Ioo_subset_Icc_self hy₀I) _ (Ioo_subset_Icc_self ht))]
  exact ⟨memSobolevIntervalLp_one_iff.2 ⟨hg.memLp_top_restrict_Ioo.mono_exponent le_top, _, hweak',
    hmem⟩, hweak'⟩

/-- **$|x| \in W^{1,p}(-1, 1)$ for every $1 \le p \le \infty$.** The function $x \mapsto |x|$ lies
in $W^{1,p}(-1, 1)$, and its weak derivative on $(-1, 1)$ is the sign function $g(x) = 1$ for
$x > 0$, $g(x) = -1$ for $x \le 0$. This is Example (i) of [brezis2011functional] §8.2.

The function $|x|$ is continuous and piecewise $C^1$ on the partition $-1 < 0 < 1$. -/
theorem memSobolevIntervalLp_abs :
    MemSobolevIntervalLp (fun x : ℝ ↦ |x|) 1 p (Opens.Ioo (-1) 1) ∧
      HasWeakDerivOn (fun x : ℝ ↦ |x|) (fun x ↦ if 0 < x then 1 else -1) (Opens.Ioo (-1) 1) := by
  have hx : StrictMono (![-1, 0, 1] : Fin 3 → ℝ) := by
    refine Fin.strictMono_iff_lt_succ.2 fun i ↦ ?_
    fin_cases i <;> norm_num
  have hder : ∀ t : ℝ, t ≠ 0 → deriv (fun x : ℝ ↦ |x|) t = if 0 < t then 1 else -1 := by
    intro t ht
    rcases ht.lt_or_gt with h | h
    · rw [(hasDerivAt_abs_neg h).deriv, ite_eq_right (not_lt.2 h.le)]
    · rw [(hasDerivAt_abs_pos h).deriv, ite_eq_left h]
  have hg' : ∀ j : Fin 2, ContDiffOn ℝ 1 (fun x : ℝ ↦ |x|)
      (Ioo ((![-1, 0, 1] : Fin 3 → ℝ) j.castSucc) ((![-1, 0, 1] : Fin 3 → ℝ) j.succ)) := by
    intro j
    fin_cases j
    · exact contDiffOn_abs fun t ht ↦ (show t < 0 from ht.2).ne
    · exact contDiffOn_abs fun t ht ↦ (show 0 < t from ht.1).ne'
  have hbdd : ∃ C, ∀ j : Fin 2, ∀ t ∈ Ioo ((![-1, 0, 1] : Fin 3 → ℝ) j.castSucc)
      ((![-1, 0, 1] : Fin 3 → ℝ) j.succ), |deriv (fun x : ℝ ↦ |x|) t| ≤ C := by
    refine ⟨1, fun j t ht ↦ ?_⟩
    have ht0 : t ≠ 0 := by
      fin_cases j
      · exact (show t < 0 from ht.2).ne
      · exact (show 0 < t from ht.1).ne'
    rw [hder t ht0]
    split_ifs <;> simp
  obtain ⟨hmem, hweak⟩ := memSobolevIntervalLp_of_piecewise_contDiffOn (p := p) hx rfl rfl
    continuous_abs.continuousOn hg' hbdd
  refine ⟨hmem, hweak.congr_ae (EventuallyEq.refl _ _) ?_⟩
  have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
  exact ae_restrict_of_ae (h0.mono fun t ht ↦ hder t ht)

/-- **The sign function is not in $W^{1,p}(-1, 1)$ for any $1 \le p \le \infty$.** The function
$g(x) = 1$ for $x > 0$, $g(x) = -1$ for $x \le 0$, does not lie in $W^{1,p}(-1, 1)$. This is
Example (ii) of [brezis2011functional] §8.2.

If it did, it would agree almost everywhere with a function continuous on $[-1, 1]$, whose value
at $0$ would have to be both $1$ and $-1$. -/
theorem not_memSobolevIntervalLp_sign :
    ¬ MemSobolevIntervalLp (fun x : ℝ ↦ if 0 < x then (1 : ℝ) else -1) 1 p (Opens.Ioo (-1) 1) := by
  intro hmem
  obtain ⟨u, hu⟩ := hmem.exists_sobolevIntervalLp
  have hI : ((Opens.Ioo (-1) 1 : Opens ℝ) : Set ℝ).OrdConnected := Set.ordConnected_Ioo
  have hrep := (SobolevIntervalLp.fn_ae_eq_rep hI u).symm.trans hu
  have hcont : ContinuousOn (SobolevIntervalLp.rep u) (Icc (-1) 1) := by
    have := SobolevIntervalLp.continuousOn_rep hI u
    rwa [Opens.coe_Ioo, closure_Ioo (by norm_num)] at this
  -- on `(0, 1)` the representative is `1`, on `(-1, 0)` it is `-1`
  have hpos : EqOn (SobolevIntervalLp.rep u) (fun _ ↦ (1 : ℝ)) (Icc 0 1) := by
    refine eqOn_Icc_of_ae_eq (by norm_num)
      (hcont.mono (Icc_subset_Icc (by norm_num : (-1 : ℝ) ≤ 0) le_rfl)) continuousOn_const ?_
    have hsub : Ioo (0 : ℝ) 1 ⊆ Ioo (-1) 1 := Ioo_subset_Ioo (by norm_num) le_rfl
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hrep,
      ae_restrict_mem measurableSet_Ioo] with t ht htI
    rw [ht, ite_eq_left htI.1]
  have hneg : EqOn (SobolevIntervalLp.rep u) (fun _ ↦ (-1 : ℝ)) (Icc (-1) 0) := by
    refine eqOn_Icc_of_ae_eq (by norm_num)
      (hcont.mono (Icc_subset_Icc le_rfl (by norm_num : (0 : ℝ) ≤ 1))) continuousOn_const ?_
    have hsub : Ioo (-1 : ℝ) 0 ⊆ Ioo (-1) 1 := Ioo_subset_Ioo le_rfl (by norm_num)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hrep,
      ae_restrict_mem measurableSet_Ioo] with t ht htI
    rw [ht, ite_eq_right (not_lt.2 htI.2.le)]
  have h1 := hpos (left_mem_Icc.2 zero_le_one)
  have h2 := hneg (right_mem_Icc.2 (by norm_num))
  simp only at h1 h2
  linarith

end ClassicalMem


section Helpers

variable {I : Opens ℝ} {p : ℝ≥0∞}

/-- If $s = \emptyset$, every property holds almost everywhere for the restriction of a measure
$\mu$ to $s$. -/
theorem MeasureTheory.ae_restrict_of_eq_empty {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : s = ∅) {P : α → Prop} : ∀ᵐ x ∂(μ.restrict s), P x := by
  subst hs
  rw [Measure.restrict_empty, ae_zero]
  exact Filter.eventually_bot

/-- Let $I$ be an open interval and let $P$ hold almost everywhere on $I$. For all $x, y$ in the
closure $\bar I$, $P$ holds almost everywhere on the interval between $x$ and $y$. -/
theorem ae_uIoc_of_ae_restrict (hI : (I : Set ℝ).OrdConnected) {P : ℝ → Prop}
    (h : ∀ᵐ t ∂(volume.restrict I), P t) {x y : ℝ} (hx : x ∈ closure (I : Set ℝ))
    (hy : y ∈ closure (I : Set ℝ)) : ∀ᵐ t, t ∈ Ι x y → P t := by
  have hsub : uIcc x y ⊆ closure (I : Set ℝ) := (I.ordConnected_closure hI).uIcc_subset hx hy
  have hnull : ∀ᵐ t : ℝ, t ∉ closure (I : Set ℝ) \ I :=
    measure_eq_zero_iff_ae_notMem.1 (I.volume_closure_diff_eq_zero hI)
  filter_upwards [(ae_restrict_iff' I.isOpen.measurableSet).1 h, hnull] with t ht htn htI
  by_cases hmem : t ∈ (I : Set ℝ)
  · exact ht hmem
  · exact absurd ⟨hsub (uIoc_subset_uIcc htI), hmem⟩ htn

/-- Let $I$ be an open interval, let $f = g$ almost everywhere on $I$, and let $x, y$ lie in the
closure $\bar I$. Then $\int_x^y f = \int_x^y g$. -/
theorem intervalIntegral_congr_ae_of_mem_closure (hI : (I : Set ℝ).OrdConnected) {f g : ℝ → ℝ}
    (h : f =ᵐ[volume.restrict I] g) {x y : ℝ} (hx : x ∈ closure (I : Set ℝ))
    (hy : y ∈ closure (I : Set ℝ)) : ∫ t in x..y, f t = ∫ t in x..y, g t :=
  intervalIntegral.integral_congr_ae (ae_uIoc_of_ae_restrict hI h hx hy)

/-- Let $1 \le p \le \infty$ and $w \in L^p(I)$. For all $x, y \in \mathbb{R}$, $w$ is integrable on
$[x, y] \cap I$, where $[x, y]$ is the closed interval between $x$ and $y$. -/
theorem MeasureTheory.MemLp.integrableOn_uIcc_inter [Fact (1 ≤ p)] {w : ℝ → ℝ}
    (hw : MemLp w p (volume.restrict I)) (x y : ℝ) : IntegrableOn w (uIcc x y ∩ I) := by
  have := hw.restrict (uIcc x y)
  rw [Measure.restrict_restrict measurableSet_uIcc] at this
  have hfin : Fact (volume (uIcc x y ∩ I) < ⊤) :=
    ⟨(measure_mono inter_subset_left).trans_lt measure_Icc_lt_top⟩
  exact this.integrable Fact.out

/-- Let $1 \le p \le \infty$ and $w \in L^p(I)$. The extension of $w$ by zero off $I$ is integrable
on every bounded interval of $\mathbb{R}$. -/
theorem MeasureTheory.MemLp.intervalIntegrable_indicator [Fact (1 ≤ p)] {w : ℝ → ℝ}
    (hw : MemLp w p (volume.restrict I)) (x y : ℝ) :
    IntervalIntegrable ((I : Set ℝ).indicator w) volume x y := by
  refine IntegrableOn.intervalIntegrable ?_
  rw [IntegrableOn, integrable_indicator_iff I.isOpen.measurableSet, IntegrableOn,
    Measure.restrict_restrict I.isOpen.measurableSet, inter_comm]
  exact hw.integrableOn_uIcc_inter x y

end Helpers

/-! ### The $C^1$ and $C^k$ representatives -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- **The representative is $C^1$ when the derivative is continuous.** Let $I$ be an open interval
and $u \in W^{1,p}(I)$, and let $u' = g$ almost everywhere on $I$ for a function $g$ continuous
on the closure $\bar I$. Then the continuous representative $\tilde u$ is of class $C^1$ on
$\bar I$, and its derivative within $\bar I$ at every $x \in \bar I$ is $g(x)$. This is Remark 6
of [brezis2011functional] §8.2.

The proof extends $g$ continuously to $\mathbb{R}$ by the Tietze extension theorem and compares
$\tilde u$ with the $C^1$ primitive of the extension. -/
theorem contDiffOn_rep_of_continuousOn_deriv (hI : (I : Set ℝ).OrdConnected)
    (u : SobolevIntervalLp 1 p I) {g : ℝ → ℝ} (hg : ContinuousOn g (closure (I : Set ℝ)))
    (hu : deriv u 1 =ᵐ[volume.restrict I] g) :
    ContDiffOn ℝ 1 (rep u) (closure (I : Set ℝ)) ∧
      ∀ x ∈ closure (I : Set ℝ), HasDerivWithinAt (rep u) (g x) (closure (I : Set ℝ)) x := by
  rcases (I : Set ℝ).eq_empty_or_nonempty with hI0 | hne
  · rw [hI0, closure_empty]
    exact ⟨contDiffOn_empty, fun x hx ↦ absurd hx (notMem_empty x)⟩
  have hy₀ : I.basePoint ∈ closure (I : Set ℝ) := subset_closure (I.basePoint_mem hne)
  -- extend `g` continuously to the line
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq isClosed_closure
    (⟨fun x : closure (I : Set ℝ) ↦ g x, hg.comp_continuous continuous_subtype_val fun x ↦ x.2⟩ :
      C(closure (I : Set ℝ), ℝ))
  have hGg : ∀ x ∈ closure (I : Set ℝ), G x = g x := fun x hx ↦ by
    have := congrArg (fun f : C(closure (I : Set ℝ), ℝ) ↦ f ⟨x, hx⟩) hG
    simpa using this
  set F : ℝ → ℝ := fun z ↦ repConst u + ∫ t in I.basePoint..z, G t with hF
  have hFd : ∀ z, HasDerivAt F (G z) z := fun z ↦
    (G.continuous.integral_hasStrictDerivAt I.basePoint z).hasDerivAt.const_add _
  have hFC : ContDiff ℝ 1 F :=
    contDiff_one_iff_deriv.2 ⟨fun z ↦ (hFd z).differentiableAt,
      (funext fun z ↦ (hFd z).deriv : _root_.deriv F = G) ▸ G.continuous⟩
  have hFrep : ∀ z ∈ closure (I : Set ℝ), rep u z = F z := fun z hz ↦ by
    rw [rep_apply, hF]
    dsimp only
    congr 1
    refine (intervalIntegral_congr_ae_of_mem_closure hI hu hy₀ hz).trans ?_
    refine intervalIntegral.integral_congr fun t ht ↦ (hGg t ?_).symm
    exact (I.ordConnected_closure hI).uIcc_subset hy₀ hz ht
  refine ⟨hFC.contDiffOn.congr hFrep, fun x hx ↦ ?_⟩
  rw [← hGg x hx]
  exact (hFd x).hasDerivWithinAt.congr hFrep (hFrep x hx)

/-- **The $C^k$ representative of an element of $W^{k+1,p}(I)$.** Let $1 \le p \le \infty$, let $I$
be an open interval and $u \in W^{k+1,p}(I)$. There is a function $f \in C^k(\mathbb{R})$ such
that $f^{(j)} = u^{(j)}$ almost everywhere on $I$ for every $j \le k$, and
$$f^{(k)}(t) - f^{(k)}(s) = \int_s^t u^{(k+1)}(r)\, dr \quad \text{for all } s, t \in \bar I.$$
This is what the paragraph on $W^{m,p}$ of [brezis2011functional] §8.2 means by
$W^{m,p}(I) \subseteq C^{m-1}(\bar I)$.

The proof is by induction on $k$ and integrates the representative of the weak derivative
$u' \in W^{k,p}(I)$. The base case is the primitive of the extension of $u'$ by zero. -/
theorem exists_contDiff_ae_eq (hI : (I : Set ℝ).OrdConnected) {k : ℕ}
    (u : SobolevIntervalLp (k + 1) p I) :
    ∃ f : ℝ → ℝ, ContDiff ℝ k f ∧
      (∀ j : Fin (k + 1), deriv u j.castSucc =ᵐ[volume.restrict I] iteratedDeriv j f) ∧
      ∀ s ∈ closure (I : Set ℝ), ∀ t ∈ closure (I : Set ℝ),
        iteratedDeriv k f t - iteratedDeriv k f s = ∫ r in s..t, deriv u (Fin.last (k + 1)) r := by
  rcases (I : Set ℝ).eq_empty_or_nonempty with hI0 | hne
  · refine ⟨0, contDiff_const, fun j ↦ ?_, fun s hs ↦ ?_⟩
    · exact ae_restrict_of_eq_empty hI0
    · rw [hI0, closure_empty] at hs
      exact absurd hs (notMem_empty s)
  have hy₀I := I.basePoint_mem hne
  have hy₀ : I.basePoint ∈ closure (I : Set ℝ) := subset_closure hy₀I
  induction k with
  | zero =>
    -- the primitive of the extension by zero of the weak derivative
    set w : ℝ → ℝ := (I : Set ℝ).indicator (deriv u 1) with hw
    have hwae : (deriv u 1 : ℝ → ℝ) =ᵐ[volume.restrict I] w :=
      (ae_restrict_iff' I.isOpen.measurableSet).2 (Eventually.of_forall fun t ht ↦ by
        rw [hw, indicator_of_mem ht])
    have hwint : ∀ a b : ℝ, IntervalIntegrable w volume a b := fun a b ↦
      (memLp_deriv u 1).intervalIntegrable_indicator a b
    obtain ⟨c, hc⟩ := (hasWeakDerivOn_fn u).exists_ae_eq_integral_of_mem hI hy₀I
    refine ⟨fun x ↦ c + ∫ t in I.basePoint..x, w t, ?_, fun j ↦ ?_, fun s hs t ht ↦ ?_⟩
    · rw [Nat.cast_zero, contDiff_zero]
      exact continuous_const.add (intervalIntegral.continuous_primitive hwint _)
    · obtain rfl : j = 0 := Fin.ext (by omega)
      refine hc.trans ((ae_restrict_iff' I.isOpen.measurableSet).2 (Eventually.of_forall
        fun x hx ↦ ?_))
      simp only [Fin.val_zero, iteratedDeriv_zero]
      rw [intervalIntegral_congr_ae_of_mem_closure hI hwae hy₀ (subset_closure hx)]
    · simp only [iteratedDeriv_zero]
      rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left (hwint _ _)
        (hwint _ _), intervalIntegral_congr_ae_of_mem_closure hI hwae.symm hs ht]
      rfl
  | succ k ih =>
    obtain ⟨f', hf', hae', hftc'⟩ := ih (derivCLM (k + 1) p I u)
    simp only [deriv_derivCLM, Fin.succ_last] at hae' hftc'
    have hcont : Continuous f' := hf'.continuous
    -- the representative of `u` is an antiderivative of the representative of `u'`
    obtain ⟨c, hc⟩ := (hasWeakDerivOn_deriv_succ u 0).exists_ae_eq_integral_of_mem hI hy₀I
    have h1 : (deriv u (0 : Fin (k + 2)).succ : ℝ → ℝ) =ᵐ[volume.restrict I] f' := by
      simpa only [Fin.succ_zero_eq_one, Fin.castSucc_zero, Fin.val_zero, iteratedDeriv_zero]
        using hae' 0
    set f : ℝ → ℝ := fun x ↦ c + ∫ t in I.basePoint..x, f' t with hf
    have hderiv : ∀ x, HasDerivAt f (f' x) x := fun x ↦
      (hcont.integral_hasStrictDerivAt I.basePoint x).hasDerivAt.const_add c
    have hderiv' : _root_.deriv f = f' := funext fun x ↦ (hderiv x).deriv
    have hfC : ContDiff ℝ (k + 1) f :=
      contDiff_succ_iff_deriv.2 ⟨fun x ↦ (hderiv x).differentiableAt, by simp, hderiv' ▸ hf'⟩
    have hiter : ∀ j, iteratedDeriv (j + 1) f = iteratedDeriv j f' := fun j ↦ by
      rw [iteratedDeriv_succ', hderiv']
    refine ⟨f, hfC, fun j ↦ ?_, fun s hs t ht ↦ ?_⟩
    · induction j using Fin.cases with
      | zero =>
        refine hc.trans ((ae_restrict_iff' I.isOpen.measurableSet).2 (Eventually.of_forall
          fun x hx ↦ ?_))
        simp only [Fin.val_zero, iteratedDeriv_zero, hf]
        rw [intervalIntegral_congr_ae_of_mem_closure hI h1 hy₀ (subset_closure hx)]
      | succ i =>
        rw [Fin.val_succ, hiter, ← Fin.succ_castSucc]
        exact hae' i
    · rw [hiter]
      exact hftc' s hs t ht

end SobolevIntervalLp


section Helpers2

variable {I : Opens ℝ}

/-- On an empty open set $I$, every function $w$ is the weak derivative of every function $f$. -/
theorem hasWeakDerivOn_of_eq_empty (hI : (I : Set ℝ) = ∅) (f w : ℝ → ℝ) :
    HasWeakDerivOn f w I := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_, fun φ ↦ ?_⟩
  · rw [hI] at hx; exact absurd hx (notMem_empty x)
  · rw [hI] at hx; exact absurd hx (notMem_empty x)
  · rw [hI]; simp

end Helpers2

/-! ### Absolutely continuous and Lipschitz functions -/

section ACLip

variable {I : Opens ℝ}

/-- **$W^{1,1}(a, b)$ is the space of absolutely continuous functions.** Let $a < b$. A function $u$
lies in $W^{1,1}(a, b)$ if and only if it agrees almost everywhere on $(a, b)$ with a function
that is absolutely continuous on $[a, b]$. This is the absolutely continuous half of Remark 8 of
[brezis2011functional] §8.2.

In the forward direction, the continuous representative is absolutely continuous. In the
backward direction, an absolutely continuous $g$ is differentiable almost everywhere with
integrable derivative and $g(x) = g(y_0) + \int_{y_0}^x g'$, so Lemma 8.2 gives its weak
derivative. -/
theorem memSobolevIntervalLp_one_one_iff_absolutelyContinuousOnInterval {a b : ℝ} (hab : a < b)
    {u : ℝ → ℝ} :
    MemSobolevIntervalLp u 1 1 (Opens.Ioo a b) ↔
      ∃ g : ℝ → ℝ, AbsolutelyContinuousOnInterval g a b ∧ u =ᵐ[volume.restrict (Ioo a b)] g := by
  have hI : ((Opens.Ioo a b : Opens ℝ) : Set ℝ).OrdConnected := Set.ordConnected_Ioo
  have hcl : closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) = Icc a b := by
    rw [Opens.coe_Ioo, closure_Ioo hab.ne]
  constructor
  · intro hmem
    obtain ⟨v, hv⟩ := hmem.exists_sobolevIntervalLp
    refine ⟨SobolevIntervalLp.rep v, ?_, hv.symm.trans (SobolevIntervalLp.fn_ae_eq_rep hI v)⟩
    exact SobolevIntervalLp.absolutelyContinuousOnInterval_rep hI v
      (hcl ▸ left_mem_Icc.2 hab.le) (hcl ▸ right_mem_Icc.2 hab.le)
  · rintro ⟨g, hg, hug⟩
    refine MemSobolevIntervalLp.congr_ae ?_ hug.symm
    set y₀ := (a + b) / 2 with hy₀
    have hy₀I : y₀ ∈ Ioo a b := ⟨by rw [hy₀]; linarith, by rw [hy₀]; linarith⟩
    have hmem' : MemLp (deriv g) 1 (volume.restrict (Ioo a b)) := by
      rw [memLp_one_iff_integrable]
      exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).1 hg.intervalIntegrable_deriv
    have hweak := (hmem'.locallyIntegrableOn le_rfl (Ω := Opens.Ioo a b)).hasWeakDerivOn_integral
      hI hy₀I (g y₀)
    have hweak' : HasWeakDerivOn g (deriv g) (Opens.Ioo a b) := by
      refine hweak.congr_ae ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall
        fun t ht ↦ ?_)) (EventuallyEq.refl _ _)
      dsimp only
      have hmem : ∀ z ∈ Ioo a b, z ∈ uIcc a b := fun z hz ↦ by
        rw [uIcc_of_le hab.le]; exact Ioo_subset_Icc_self hz
      rw [(hg.mono (uIcc_subset_uIcc (hmem _ hy₀I) (hmem _ ht))).integral_deriv_eq_sub]
      ring
    have hgc : ContinuousOn g (Icc a b) := by
      have := hg.continuousOn
      rwa [uIcc_of_le hab.le] at this
    exact memSobolevIntervalLp_one_iff.2 ⟨hgc.memLp_top_restrict_Ioo.mono_exponent le_top, _,
      hweak', hmem'⟩

/-- **$W^{1,\infty}(I)$ is the space of Lipschitz functions.** Let $I$ be an open interval and
$u \in L^\infty(I)$. Then $u \in W^{1,\infty}(I)$ if and only if there is a constant $C$ such
that, for almost every $x \in I$ and almost every $y \in I$,
$$|u(x) - u(y)| \le C\, |x - y|.$$
This is Proposition 8.4 of [brezis2011functional].

In the forward direction the proof takes $C = \|u'\|_\infty$, since the continuous
representative satisfies $|\tilde u(x) - \tilde u(y)| = |\int_y^x u'| \le \|u'\|_\infty |x -
y|$. In the backward direction, $u$ is Lipschitz on the set of full measure of the points $x$
with $|u(x) - u(y)| \le C |x - y|$ for almost every $y$. So it extends to a Lipschitz function
$g$ on $\mathbb{R}$ (McShane) that agrees with $u$ almost everywhere. Then $g$ is absolutely
continuous with $|g'| \le C$ and $g(x) = g(y_0) + \int_{y_0}^x g'$, and Lemma 8.2 gives
$g \in W^{1,\infty}(I)$. In one dimension the route of the source through Proposition 8.3 and
the duality $(L^1)^* = L^\infty$ is not needed. -/
theorem memSobolevIntervalLp_top_iff_lipschitz (hI : (I : Set ℝ).OrdConnected) {u : ℝ → ℝ}
    (hu : MemLp u ⊤ (volume.restrict I)) :
    MemSobolevIntervalLp u 1 ⊤ I ↔ ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict I),
      ∀ᵐ y ∂(volume.restrict I), |u x - u y| ≤ C * |x - y| := by
  constructor
  · intro hmem
    obtain ⟨v, hv⟩ := hmem.exists_sobolevIntervalLp
    refine ⟨‖SobolevIntervalLp.deriv v 1‖, ?_⟩
    have hbound : ∀ x ∈ closure (I : Set ℝ), ∀ y ∈ closure (I : Set ℝ),
        |SobolevIntervalLp.rep v x - SobolevIntervalLp.rep v y|
          ≤ ‖SobolevIntervalLp.deriv v 1‖ * |x - y| := by
      intro x hx y hy
      rw [SobolevIntervalLp.rep_sub_rep hI v hy hx]
      have := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := y) (b := x)
        (f := SobolevIntervalLp.deriv v 1) (C := ‖SobolevIntervalLp.deriv v 1‖)
        (ae_uIoc_of_ae_restrict hI (Lp.ae_norm_le_norm_top _) hy hx)
      simpa only [Real.norm_eq_abs] using this
    have hrep := hv.symm.trans (SobolevIntervalLp.fn_ae_eq_rep hI v)
    filter_upwards [hrep, ae_restrict_mem I.isOpen.measurableSet] with x hx hxI
    filter_upwards [hrep, ae_restrict_mem I.isOpen.measurableSet] with y hy hyI
    rw [hx, hy]
    exact hbound x (subset_closure hxI) y (subset_closure hyI)
  · rintro ⟨C, hC⟩
    set C' : ℝ := max C 0 with hC'
    have hC'0 : 0 ≤ C' := le_max_right _ _
    have hC2 : ∀ᵐ x ∂(volume.restrict I), ∀ᵐ y ∂(volume.restrict I),
        |u x - u y| ≤ C' * |x - y| :=
      hC.mono fun x hx ↦ hx.mono fun y hy ↦
        hy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    set S : Set ℝ := {x | x ∈ (I : Set ℝ) ∧ ∀ᵐ y ∂(volume.restrict I), |u x - u y| ≤ C' * |x - y|}
      with hS
    have hSae : ∀ᵐ x ∂(volume.restrict I), x ∈ S := by
      filter_upwards [hC2, ae_restrict_mem I.isOpen.measurableSet] with x hx hxI
      exact ⟨hxI, hx⟩
    -- `u` is Lipschitz on `S`
    have hlip : LipschitzOnWith ⟨C', hC'0⟩ u S := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' ↦ ?_
      rw [Real.dist_eq, Real.dist_eq]
      change |u x - u x'| ≤ C' * |x - x'|
      refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
      set δ := ε / (2 * C' + 2) with hδ
      have hδ0 : 0 < δ := by positivity
      have hs : (volume.restrict (I : Set ℝ)) (Ioo (x - δ) (x + δ)) ≠ 0 := by
        rw [Measure.restrict_apply measurableSet_Ioo]
        exact ((isOpen_Ioo.inter I.isOpen).measure_pos volume
          ⟨x, ⟨by linarith, by linarith⟩, hx.1⟩).ne'
      obtain ⟨y, hy, hy1, hy2⟩ :=
        Measure.exists_mem_of_measure_ne_zero_of_ae hs (ae_restrict_of_ae (hx.2.and hx'.2))
      have hxy : |x - y| < δ := by
        rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]
      have hx'y : |x' - y| ≤ |x' - x| + |x - y| := abs_sub_le _ _ _
      have h2C : 2 * C' * δ < ε := by
        rw [hδ, mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      calc |u x - u x'| ≤ |u x - u y| + |u y - u x'| := abs_sub_le _ _ _
        _ = |u x - u y| + |u x' - u y| := by rw [abs_sub_comm (u y) (u x')]
        _ ≤ C' * |x - y| + C' * |x' - y| := add_le_add hy1 hy2
        _ ≤ C' * δ + C' * (|x' - x| + δ) := by
          gcongr
          linarith
        _ = C' * |x - x'| + 2 * C' * δ := by rw [abs_sub_comm x' x]; ring
        _ < C' * |x - x'| + ε := by linarith
    obtain ⟨g, hg, hug⟩ := hlip.extend_real
    have hug' : u =ᵐ[volume.restrict I] g := hSae.mono fun x hx ↦ hug hx
    refine MemSobolevIntervalLp.congr_ae ?_ hug'.symm
    have hderiv_bound : ∀ x, |deriv g x| ≤ C' := fun x ↦ by
      by_cases hd : DifferentiableAt ℝ g x
      · have := hd.hasDerivAt.le_of_lipschitz hg
        rw [Real.norm_eq_abs] at this
        exact this
      · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
        exact hC'0
    have hmemLp : MemLp (deriv g) ⊤ (volume.restrict I) :=
      memLp_top_of_bound (measurable_deriv g).aestronglyMeasurable C'
        (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hderiv_bound x)
    have hgLp : MemLp g ⊤ (volume.restrict I) := hu.ae_eq hug'
    rcases (I : Set ℝ).eq_empty_or_nonempty with hI0 | hne
    · exact memSobolevIntervalLp_one_iff.2 ⟨hgLp, _, hasWeakDerivOn_of_eq_empty hI0 g (deriv g),
        hmemLp⟩
    have hy₀I := I.basePoint_mem hne
    have hweak := (hmemLp.locallyIntegrableOn le_top).hasWeakDerivOn_integral hI hy₀I
      (g I.basePoint)
    have hweak' : HasWeakDerivOn g (deriv g) I := by
      refine hweak.congr_ae (Eventually.of_forall fun t ↦ ?_) (EventuallyEq.refl _ _)
      dsimp only
      rw [(LipschitzOnWith.absolutelyContinuousOnInterval
        (hg.lipschitzOnWith (s := uIcc I.basePoint t))).integral_deriv_eq_sub]
      ring
    exact memSobolevIntervalLp_one_iff.2 ⟨hgLp, _, hweak', hmemLp⟩

end ACLip


/-! ### Translations -/

section Translate

/-- For $x, h, s \in \mathbb{R}$, $x + s$ lies in the interval
$(\min\{x, x + h\}, \max\{x, x + h\}]$ if and only if $s$ lies in
$(\min\{0, h\}, \max\{0, h\}]$. -/
theorem mem_uIoc_add_left_iff {x h s : ℝ} : x + s ∈ Ι x (x + h) ↔ s ∈ Ι 0 h := by
  simp only [mem_uIoc]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩

/-- For a function $g : \mathbb{R} \to [0, \infty]$ and $x, h \in \mathbb{R}$, the integral of $g$
over the interval $(\min\{x, x + h\}, \max\{x, x + h\}]$ equals $\int_{\mathbb{R}}
\mathbf{1}_{J}(s)\, g(x + s)\, ds$, where $J = (\min\{0, h\}, \max\{0, h\}]$. -/
theorem lintegral_uIoc_add_left (g : ℝ → ℝ≥0∞) (x h : ℝ) :
    ∫⁻ t in Ι x (x + h), g t = ∫⁻ s, (Ι 0 h).indicator (fun s ↦ g (x + s)) s := by
  rw [← lintegral_indicator measurableSet_uIoc, ← lintegral_add_left_eq_self _ x]
  refine lintegral_congr fun s ↦ ?_
  by_cases hs : s ∈ Ι 0 h
  · rw [indicator_of_mem hs, indicator_of_mem (mem_uIoc_add_left_iff.2 hs)]
  · rw [indicator_of_notMem hs, indicator_of_notMem (mt mem_uIoc_add_left_iff.1 hs)]

end Translate

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Translations of a function of $W^{1,p}(\mathbb{R})$.** Let $1 \le p \le \infty$,
$u \in W^{1,p}(\mathbb{R})$ and $h \in \mathbb{R}$. Then
$$\|\tau_h u - u\|_{L^p(\mathbb{R})} \le |h|\, \|u'\|_{L^p(\mathbb{R})},$$
where $(\tau_h u)(x) = \tilde u(x + h)$ and $u$ is read as its continuous representative
$\tilde u$. This is the implication (i) ⇒ (ii) of Proposition 8.5 of [brezis2011functional].

Since $\tilde u(x + h) - \tilde u(x) = \int_x^{x+h} u'$, the left side is at most the $L^p$ norm
in $x$ of $\int_0^h |u'(x + s)|\, ds$. Minkowski's integral inequality
(`ENNReal.lintegral_rpow_lintegral_le`) and translation invariance bound this by
$|h|\, \|u'\|_p$. For $p = \infty$ it is the Lipschitz bound of Proposition 8.4. The norms are
the extended norms `eLpNorm`, and the line is the open set `⊤`. -/
theorem eLpNorm_translate_sub_le (u : SobolevIntervalLp 1 p ⊤) (h : ℝ) :
    eLpNorm (fun x ↦ rep u (x + h) - rep u x) p volume
      ≤ ENNReal.ofReal |h| * eLpNorm (deriv u 1) p volume := by
  have hI : ((⊤ : Opens ℝ) : Set ℝ).OrdConnected := by
    rw [Opens.coe_top]; exact ordConnected_univ
  have hcl : ∀ x : ℝ, x ∈ closure ((⊤ : Opens ℝ) : Set ℝ) := fun x ↦ by
    rw [Opens.coe_top, closure_univ]; exact mem_univ x
  set w : ℝ → ℝ := (deriv u 1 : ℝ → ℝ) with hw
  have hwm : StronglyMeasurable w := Lp.stronglyMeasurable _
  have hsub : ∀ x, rep u (x + h) - rep u x = ∫ t in x..x + h, w t := fun x ↦
    rep_sub_rep hI u (hcl x) (hcl (x + h))
  have hcont : Continuous fun x ↦ rep u (x + h) - rep u x := by
    have hc : Continuous (rep u) := by
      have := continuousOn_rep hI u
      rwa [Opens.coe_top, closure_univ, continuousOn_univ] at this
    exact (hc.comp (continuous_id.add continuous_const)).sub hc
  -- the pointwise bound by the integral of `|u'|` over the translated segment
  have hpt : ∀ x, ‖rep u (x + h) - rep u x‖ₑ
      ≤ ∫⁻ s, (Ι 0 h).indicator (fun s ↦ ‖w (x + s)‖ₑ) s := fun x ↦ by
    rw [hsub, ← lintegral_uIoc_add_left (fun t ↦ ‖w t‖ₑ) x h, ← ofReal_norm,
      intervalIntegral.norm_integral_eq_norm_integral_uIoc, ofReal_norm]
    exact enorm_integral_le_lintegral_enorm _
  have hvol : volume (Ι 0 h) = ENNReal.ofReal |h| := by rw [Real.volume_uIoc, sub_zero]
  rcases eq_or_ne p ⊤ with rfl | hp
  · -- `p = ∞`: the Lipschitz bound
    have hbound : ∀ᵐ t : ℝ, ‖w t‖ₑ ≤ eLpNorm w ⊤ volume := by
      rw [eLpNorm_exponent_top hwm.aestronglyMeasurable]
      exact ae_le_eLpNormEssSup
    have hpt' : ∀ x, ‖rep u (x + h) - rep u x‖ₑ ≤ ENNReal.ofReal |h| * eLpNorm w ⊤ volume := by
      intro x
      refine (hpt x).trans ?_
      have hb : ∀ᵐ s : ℝ, (Ι 0 h).indicator (fun s ↦ ‖w (x + s)‖ₑ) s
          ≤ (Ι 0 h).indicator (fun _ ↦ eLpNorm w ⊤ volume) s := by
        filter_upwards [(measurePreserving_add_left volume x).quasiMeasurePreserving.ae hbound]
          with s hs
        by_cases hsI : s ∈ Ι 0 h
        · rw [indicator_of_mem hsI, indicator_of_mem hsI]; exact hs
        · rw [indicator_of_notMem hsI, indicator_of_notMem hsI]
      refine (lintegral_mono_ae hb).trans ?_
      rw [lintegral_indicator_const measurableSet_uIoc, hvol, mul_comm]
    have := eLpNorm_le_of_ae_enorm_bound (p := ⊤) (μ := volume) hcont.aestronglyMeasurable
      (Eventually.of_forall hpt')
    simpa using this
  · -- `p < ∞`: Minkowski's integral inequality
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
    have hp1 : (1 : ℝ) ≤ p.toReal := by
      rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hp Fact.out
    have hpr : (0 : ℝ) < p.toReal := zero_lt_one.trans_le hp1
    set H : ℝ → ℝ → ℝ≥0∞ := fun x s ↦ (Ι 0 h).indicator (fun s ↦ ‖w (x + s)‖ₑ) s with hH
    have hHm : Measurable (Function.uncurry H) := by
      refine Measurable.indicator ?_ (measurableSet_uIoc.preimage measurable_snd)
      exact (hwm.measurable.comp (measurable_fst.add measurable_snd)).enorm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hcont.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hwm.aestronglyMeasurable]
    calc (∫⁻ x, ‖rep u (x + h) - rep u x‖ₑ ^ p.toReal) ^ (1 / p.toReal)
        ≤ (∫⁻ x, (∫⁻ s, H x s) ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr with x
          exact hpt x
      _ ≤ ∫⁻ s, (∫⁻ x, H x s ^ p.toReal) ^ (1 / p.toReal) :=
          ENNReal.lintegral_rpow_lintegral_le hp1 hHm.aemeasurable
      _ = ∫⁻ s, (Ι 0 h).indicator (fun _ ↦ (∫⁻ x, ‖w x‖ₑ ^ p.toReal) ^ (1 / p.toReal)) s := by
          refine lintegral_congr fun s ↦ ?_
          by_cases hs : s ∈ Ι 0 h
          · simp only [hH, indicator_of_mem hs]
            rw [lintegral_add_right_eq_self (fun x ↦ ‖w x‖ₑ ^ p.toReal) s]
          · simp only [hH, indicator_of_notMem hs, ENNReal.zero_rpow_of_pos hpr, lintegral_zero,
              ENNReal.zero_rpow_of_pos (by positivity : (0 : ℝ) < 1 / p.toReal)]
      _ = ENNReal.ofReal |h| * (∫⁻ x, ‖w x‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
          rw [lintegral_indicator_const measurableSet_uIoc, hvol, mul_comm]

end SobolevIntervalLp

end
