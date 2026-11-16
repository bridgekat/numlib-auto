/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Convex.Deriv
import Numlib.Analysis.Convex.Gateaux
import Numlib.Analysis.Convex.Homogeneous
import Numlib.Analysis.Convex.Line
import Numlib.Analysis.Convex.Saddle.Differential
import Numlib.Analysis.Convex.Subdifferential.Gradient
import NumlibSurface.Rockafellar.Common.Euclidean

/-!
# Rockafellar, Section 4: Convex functions

This module formalizes Section 4 of [rockafellar1970convex]: convex functions on $\mathbb{R}^n$ with
values in $[-\infty, +\infty]$. A function $f$ on $\mathbb{R}^n$ is convex when its epigraph
$\{(x, \mu) \mid \mu \ge f(x)\}$ is a convex subset of $\mathbb{R}^{n+1}$, which is exactly the
backbone predicate `ConvexAnalysis.ConvexFn`. The section characterizes convexity by the secant
inequality, by a strict inequality that is valid for both infinite values, and by Jensen's
inequality; it gives the second-derivative tests for twice continuously differentiable functions; it
shows that the level sets of a convex function are convex; and it studies positively homogeneous
convex functions, which are convex exactly when they are subadditive.

All 11 numbered results of Section 4 are formalized.

## Main results

* Theorem 4.1, `Rockafellar.theorem_4_1`: a function $f : C \to (-\infty, +\infty]$ on a convex set
  $C$ is convex on $C$ if and only if it satisfies the secant inequality on $C$.
* Theorem 4.2, `Rockafellar.theorem_4_2`: $f : \mathbb{R}^n \to [-\infty, +\infty]$ is convex if and
  only if $f(x) < \alpha$ and $f(y) < \beta$ imply $f((1 - \lambda) x + \lambda y) < (1 - \lambda)
  \alpha + \lambda \beta$ for $0 < \lambda < 1$.
* Theorem 4.3, `Rockafellar.theorem_4_3`: Jensen's inequality characterizes convexity of
  $f : \mathbb{R}^n \to (-\infty, +\infty]$.
* Theorem 4.4, `Rockafellar.theorem_4_4`: a twice continuously differentiable real function on an
  open interval is convex if and only if $f'' \ge 0$ there.
* Theorem 4.5, `Rockafellar.theorem_4_5`: a twice continuously differentiable real function on an
  open convex set is convex if and only if its Hessian is positive semidefinite there.
* Theorem 4.6, `Rockafellar.theorem_4_6`: the level sets $\{x \mid f(x) < \alpha\}$ and
  $\{x \mid f(x) \le \alpha\}$ of a convex function are convex.
* Corollary 4.6.1, `Rockafellar.corollary_4_6_1`: the solution set of an arbitrary system of convex
  inequalities $f_i(x) \le \alpha_i$ is convex.
* Theorem 4.7, `Rockafellar.theorem_4_7`: a positively homogeneous
  $f : \mathbb{R}^n \to (-\infty, +\infty]$ is convex if and only if it is subadditive.
* Corollary 4.7.1, `Rockafellar.corollary_4_7_1`: a positively homogeneous proper convex function
  satisfies $f(\lambda_1 x_1 + \dots + \lambda_m x_m) \le \lambda_1 f(x_1) + \dots + \lambda_m
  f(x_m)$ for $\lambda_i > 0$.
* Corollary 4.7.2, `Rockafellar.corollary_4_7_2`: a positively homogeneous proper convex function
  satisfies $f(-x) \ge -f(x)$.
* Theorem 4.8, `Rockafellar.theorem_4_8`, `Rockafellar.theorem_4_8_basis`: a positively homogeneous
  proper convex function is linear on a subspace $L$ if and only if $f(-x) = -f(x)$ for all
  $x \in L$, and it suffices to check this on a spanning set of $L$.

## Conventions

* A convex function is defined on all of $\mathbb{R}^n$, with values in `EReal`, and is convex when
  its epigraph is convex: `ConvexAnalysis.ConvexFn`. Only Theorems 4.4 and 4.5, which are about
  twice continuously differentiable functions, take a real-valued `f`. Properness
  (`ConvexAnalysis.ProperConvex`) is assumed only where the book assumes it: in Corollaries 4.7.1
  and 4.7.2 and Theorem 4.8.
* The book sets $0 \cdot \infty = 0$. This holds for the Mathlib type `EReal`, and Theorem 4.3
  depends on it: the sum $\lambda_1 f(x_1) + \dots + \lambda_m f(x_m)$ is well defined at an index
  with $\lambda_i = 0$ and $f(x_i) = +\infty$ only because that term is $0$.
* The book sets $\inf \emptyset = +\infty$. The backbone function
  `ConvexAnalysis.convexRestrict C f` is the infimum of $f(x)$ over the condition $x \in C$, which
  is $f(x)$ for $x \in C$ and $\inf \emptyset = +\infty$ for $x \notin C$. It uses this convention
  to extend a function given on $C$ by $+\infty$ off $C$, as the book does. Theorem 4.1 is stated
  through it.
* The book leaves $\infty - \infty$ undefined, but `EReal` gives the sum $+\infty + (-\infty)$ the
  value $-\infty$. No statement here depends on that value. Each statement whose right-hand side
  could contain this sum carries the hypothesis of the book that $f$ never takes the value
  $-\infty$. Theorem 4.2, the only characterization for the full range $[-\infty, +\infty]$,
  compares with real numbers $\alpha, \beta$, so no infinite sum occurs. Theorem 4.6 and Corollary
  4.6.1 are about level sets, where no sum occurs.

## Implementation notes

* Theorem 4.5 states that the Hessian is positive semidefinite in the coordinate-free form
  `0 ≤ fderiv ℝ (fderiv ℝ f) x z z` for all $z$, not through the matrix of second partial
  derivatives.

## Deviations from the source

* **Corollary 4.7.1** (reading). The book writes $\lambda_1, \dots, \lambda_m$, which implies
  $m \ge 1$. The statement assumes $m > 0$ explicitly, because for $m = 0$ it would assert
  $f(0) \le 0$, which can fail. See `Rockafellar.corollary_4_7_1`.
* **Theorem 4.8**, last sentence (correction). The book says that it suffices to check
  $f(-b_i) = -f(b_i)$ on a basis of $L$. For $L = \{0\}$ the basis is empty, and the claim fails
  when $f(0) = +\infty$. The statement requires a non-empty set. See
  `Rockafellar.theorem_4_8_basis`.
* **Theorem 4.8**, last sentence (generalization). The statement uses an arbitrary non-empty
  spanning set of $L$ instead of a basis. See `Rockafellar.theorem_4_8_basis`.
-/

namespace Rockafellar

open ConvexAnalysis

/-! ### Theorem 4.1 -/

/-- **Theorem 4.1** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be convex, and let
$f$ be a function with values in $(-\infty, +\infty]$. Then $f$ is convex on $C$ if and only if
$$f((1 - \lambda) x + \lambda y) \le (1 - \lambda) f(x) + \lambda f(y), \qquad 0 < \lambda <
  1,$$
for every $x$ and $y$ in $C$.

The book takes $f$ defined on $C$ only. Here $f$ is defined on $\mathbb{R}^n$, and "convex on
$C$" means that `ConvexAnalysis.convexRestrict C f`, the function equal to $f$ on $C$ and to
$+\infty$ off $C$, is convex. This is the convention of the book for a function given on $C$.
The hypothesis that $f$ never takes the value $-\infty$ is "values in $(-\infty, +\infty]$"; it
excludes the undefined sum $\infty - \infty$ on the right-hand side. The coefficients
$1 - \lambda$ and $\lambda$ are `a` and `b`, with $a, b > 0$ and $a + b = 1$. -/
theorem theorem_4_1 {n : ℕ} {C : Set (Rn n)} (hC : Convex ℝ C) {f : Rn n → EReal}
    (hbot : ∀ x, f x ≠ ⊥) :
    ConvexFn (convexRestrict C f) ↔ ∀ x ∈ C, ∀ y ∈ C, ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y := by
  have hrb : ∀ x, convexRestrict C f x ≠ ⊥ := by
    intro x
    by_cases hx : x ∈ C <;> simp [hx, hbot x]
  rw [convexFn_iff_le hrb]
  constructor
  · intro h x hx y hy a b ha hb hab
    have hmem : a • x + b • y ∈ C := hC hx hy ha.le hb.le hab
    have hkey := h x y a b ha hb hab
    rwa [convexRestrict_of_mem hx, convexRestrict_of_mem hy, convexRestrict_of_mem hmem] at hkey
  · intro h x y a b ha hb hab
    by_cases hx : x ∈ C
    · by_cases hy : y ∈ C
      · have hmem : a • x + b • y ∈ C := hC hx hy ha.le hb.le hab
        rw [convexRestrict_of_mem hx, convexRestrict_of_mem hy, convexRestrict_of_mem hmem]
        exact h x hx y hy a b ha hb hab
      · rw [convexRestrict_of_notMem hy, EReal.coe_mul_top_of_pos hb,
          EReal.add_top_of_ne_bot (EReal.coe_mul_ne_bot ha.le (hrb x))]
        exact le_top
    · rw [convexRestrict_of_notMem hx, EReal.coe_mul_top_of_pos ha,
        EReal.top_add_of_ne_bot (EReal.coe_mul_ne_bot hb.le (hrb y))]
      exact le_top

/-! ### Theorem 4.2 -/

/-- **Theorem 4.2** of [rockafellar1970convex]. Let $f$ be a function from $\mathbb{R}^n$ to
$[-\infty, +\infty]$. Then $f$ is convex if and only if
$$f((1 - \lambda) x + \lambda y) < (1 - \lambda) \alpha + \lambda \beta, \qquad 0 < \lambda <
  1,$$
whenever $f(x) < \alpha$ and $f(y) < \beta$, for $x, y \in \mathbb{R}^n$ and real numbers
$\alpha, \beta$.

This characterization holds for functions that take both infinite values, and the book remarks
that it could serve as the definition of convexity in general. The numbers $\alpha$ and $\beta$
are real, so no infinite sum occurs. The coefficients $1 - \lambda$ and $\lambda$ are `a` and
`b`, with $a, b > 0$ and $a + b = 1$. -/
theorem theorem_4_2 {n : ℕ} (f : Rn n → EReal) :
    ConvexFn f ↔ ∀ (x y : Rn n) (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      ∀ α β : ℝ, f x < (α : EReal) → f y < (β : EReal) →
        f (a • x + b • y) < ((a * α + b * β : ℝ) : EReal) :=
  convexFn_iff_forall_lt f

/-! ### Theorem 4.3 -/

/-- **Theorem 4.3** of [rockafellar1970convex] (Jensen's inequality). Let $f$ be a function from
$\mathbb{R}^n$ to $(-\infty, +\infty]$. Then $f$ is convex if and only if
$$f(\lambda_1 x_1 + \dots + \lambda_m x_m) \le \lambda_1 f(x_1) + \dots + \lambda_m f(x_m)$$
whenever $x_1, \dots, x_m \in \mathbb{R}^n$, $\lambda_1 \ge 0, \dots, \lambda_m \ge 0$ and
$\lambda_1 + \dots + \lambda_m = 1$.

The right-hand side is a sum in `EReal`. It is well defined only with the convention
$0 \cdot \infty = 0$: an index with $\lambda_i = 0$ and $f(x_i) = +\infty$ contributes $0$. -/
theorem theorem_4_3 {n : ℕ} {f : Rn n → EReal} (hbot : ∀ x, f x ≠ ⊥) :
    ConvexFn f ↔ ∀ (m : ℕ) (l : Fin m → ℝ) (x : Fin m → Rn n), (∀ i, 0 ≤ l i) →
      ∑ i, l i = 1 → f (∑ i, l i • x i) ≤ ∑ i, (l i : EReal) * f (x i) := by
  classical
  constructor
  · intro hconv m l x hl hl1
    set t : Finset (Fin m) := Finset.univ.filter fun i => l i ≠ 0 with ht
    have hzero : ∀ i ∈ (Finset.univ : Finset (Fin m)), i ∉ t → l i = 0 := by
      intro i _ hi
      simpa [ht] using hi
    have hsub : t ⊆ (Finset.univ : Finset (Fin m)) := Finset.filter_subset _ _
    have hsx : ∑ i ∈ t, l i • x i = ∑ i, l i • x i :=
      Finset.sum_subset hsub fun i hi hi' => by rw [hzero i hi hi', zero_smul]
    have hsf : ∑ i ∈ t, (l i : EReal) * f (x i) = ∑ i, (l i : EReal) * f (x i) :=
      Finset.sum_subset hsub fun i hi hi' => by
        rw [hzero i hi hi', EReal.coe_zero, zero_mul]
    have hs1 : ∑ i ∈ t, l i = 1 :=
      (Finset.sum_subset hsub fun i hi hi' => hzero i hi hi').trans hl1
    rw [← hsx, ← hsf]
    by_cases htop : ∑ i ∈ t, (l i : EReal) * f (x i) = ⊤
    · rw [htop]; exact le_top
    have hnb : ∀ i ∈ t, (l i : EReal) * f (x i) ≠ ⊥ :=
      fun i _ => EReal.coe_mul_ne_bot (hl i) (hbot (x i))
    have hnt := EReal.forall_ne_top_of_sum_ne_top t _ hnb htop
    have hfin : ∀ i ∈ t, f (x i) = ((f (x i)).toReal : EReal) := by
      intro i hi
      have hli : 0 < l i := lt_of_le_of_ne (hl i) (Ne.symm (by simpa [ht] using hi))
      refine (EReal.coe_toReal ?_ (hbot (x i))).symm
      intro hc
      exact hnt i hi (by rw [hc, EReal.coe_mul_top_of_pos hli])
    have key := hconv.sum_le t x (fun i => (f (x i)).toReal) l
      (fun i hi => le_of_eq (hfin i hi)) (fun i _ => hl i) hs1
    refine key.trans (le_of_eq ?_)
    rw [EReal.coe_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [EReal.coe_mul, ← hfin i hi]
  · intro h
    rw [convexFn_iff_le hbot]
    intro x y a b ha hb hab
    have key := h 2 ![a, b] ![x, y] (fun i => by fin_cases i <;> simp [ha.le, hb.le])
      (by simpa [Fin.sum_univ_two] using hab)
    simpa [Fin.sum_univ_two] using key

/-! ### Theorem 4.4 -/

/-- **Theorem 4.4** of [rockafellar1970convex]. Let $f$ be a twice continuously differentiable
real-valued function on an open interval $(\alpha, \beta)$. Then $f$ is convex on
$(\alpha, \beta)$ if and only if its second derivative $f''$ is non-negative throughout
$(\alpha, \beta)$.

This is one of the two results of Section 4 about a finite function, so $f$ is a function
`ℝ → ℝ`. The interval is open, so $f''$ is `deriv (deriv f)`. -/
theorem theorem_4_4 {α β : ℝ} {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo α β)) :
    ConvexOn ℝ (Set.Ioo α β) f ↔ ∀ x ∈ Set.Ioo α β, 0 ≤ deriv (deriv f) x := by
  have hd1 : DifferentiableOn ℝ f (Set.Ioo α β) := hf.differentiableOn (by norm_num)
  have hd2 : DifferentiableOn ℝ (deriv f) (Set.Ioo α β) :=
    (hf.deriv_of_isOpen (m := 1) isOpen_Ioo (by norm_num)).differentiableOn (by norm_num)
  constructor
  · intro hconv x hx
    have hmono : MonotoneOn (deriv f) (Set.Ioo α β) :=
      hconv.monotoneOn_deriv fun y hy => (hd1 y hy).differentiableAt (isOpen_Ioo.mem_nhds hy)
    have h := hmono.derivWithin_nonneg (x := x)
    rwa [derivWithin_of_isOpen isOpen_Ioo hx] at h
  · intro h
    exact convexOn_of_deriv2_nonneg' (convex_Ioo α β) hd1 hd2 h

/-!
### Theorem 4.5

The reduction to lines uses the backbone results `ConvexAnalysis.convexOn_iff_lines` and
`ConvexAnalysis.isOpen_line_steps` in `Numlib.Analysis.Convex.Line`. The derivative of a restriction
to a line is `HasLineDerivAt.hasDerivAt_line` in `Numlib.Analysis.Convex.Gateaux`. The lemmas below
compute the second derivative of $t \mapsto f(y + tz)$, which the book calls a straightforward
calculation.
-/

section Lines

variable {n : ℕ} {C : Set (Rn n)} {f : Rn n → ℝ} {y z : Rn n}

/-- A twice continuously differentiable function on an open set $C$ has a Fréchet derivative at each
point of $C$. -/
private theorem hasFDerivAt_of_contDiffOn (hCopen : IsOpen C) (hf : ContDiffOn ℝ 2 f C) {u : Rn n}
    (hu : u ∈ C) : HasFDerivAt f (fderiv ℝ f u) u :=
  (((hf.differentiableOn (by norm_num)) u hu).differentiableAt
    (hCopen.mem_nhds hu)).hasFDerivAt

/-- The derivative of a twice continuously differentiable function on an open set $C$ has a Fréchet
derivative at each point of $C$. -/
private theorem hasFDerivAt_fderiv_of_contDiffOn (hCopen : IsOpen C) (hf : ContDiffOn ℝ 2 f C)
    {u : Rn n} (hu : u ∈ C) : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) u) u :=
  ((((hf.fderiv_of_isOpen (m := 1) hCopen (by norm_num)).differentiableOn
    (by norm_num)) u hu).differentiableAt (hCopen.mem_nhds hu)).hasFDerivAt

/-- Let $g(t) = f(y + tz)$. If $y + tz \in C$, then near $t$ the derivative $g'(s)$ is
$\langle \nabla f(y + sz), z \rangle$. -/
private theorem deriv_comp_line_eventuallyEq (hCopen : IsOpen C) (hf : ContDiffOn ℝ 2 f C) {t : ℝ}
    (ht : y + t • z ∈ C) :
    (deriv fun s : ℝ => f (y + s • z)) =ᶠ[nhds t] fun s : ℝ => fderiv ℝ f (y + s • z) z := by
  filter_upwards [(isOpen_line_steps hCopen y z).mem_nhds
    (show t ∈ {t : ℝ | y + t • z ∈ C} from ht)] with s hs
  exact ((hasFDerivAt_of_contDiffOn hCopen hf hs).hasLineDerivAt z).hasDerivAt_line.deriv

/-- Let $g(t) = f(y + tz)$ and $x = y + tz \in C$. Then $g''(t) = \langle z, Q_x z \rangle$, where
$Q_x$ is the second Fréchet derivative of $f$ at $x$. -/
private theorem hasDerivAt_deriv_comp_line (hCopen : IsOpen C) (hf : ContDiffOn ℝ 2 f C) {t : ℝ}
    (ht : y + t • z ∈ C) :
    HasDerivAt (deriv fun s : ℝ => f (y + s • z))
      (fderiv ℝ (fderiv ℝ f) (y + t • z) z z) t := by
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ f (y + s • z))
      (fderiv ℝ (fderiv ℝ f) (y + t • z) z) t :=
    ((hasFDerivAt_fderiv_of_contDiffOn hCopen hf ht).hasLineDerivAt z).hasDerivAt_line
  have h2 : HasDerivAt (fun s : ℝ => (fderiv ℝ f (y + s • z)) z)
      (fderiv ℝ (fderiv ℝ f) (y + t • z) z z) t :=
    (ContinuousLinearMap.apply ℝ ℝ z).hasFDerivAt.comp_hasDerivAt t h1
  exact h2.congr_of_eventuallyEq (deriv_comp_line_eventuallyEq hCopen hf ht)

end Lines

/-- **Theorem 4.5** of [rockafellar1970convex]. Let $f$ be a twice continuously differentiable
real-valued function on an open convex set $C$ in $\mathbb{R}^n$. Then $f$ is convex on $C$ if
and only if its Hessian matrix $Q_x$ is positive semidefinite for every $x \in C$, that is,
$\langle z, Q_x z \rangle \ge 0$ for every $z \in \mathbb{R}^n$.

The quadratic form $\langle z, Q_x z \rangle$ is the second Fréchet derivative
`fderiv ℝ (fderiv ℝ f) x z z`, and the condition is stated in this form. -/
theorem theorem_4_5 {n : ℕ} {C : Set (Rn n)} (hC : Convex ℝ C) (hCopen : IsOpen C)
    {f : Rn n → ℝ} (hf : ContDiffOn ℝ 2 f C) :
    ConvexOn ℝ C f ↔ ∀ x ∈ C, ∀ z : Rn n, 0 ≤ fderiv ℝ (fderiv ℝ f) x z z := by
  have hderiv : ∀ {y z : Rn n} {s : ℝ}, y + s • z ∈ C →
      HasDerivAt (fun s : ℝ => f (y + s • z)) (fderiv ℝ f (y + s • z) z) s := fun hs =>
    ((hasFDerivAt_of_contDiffOn hCopen hf hs).hasLineDerivAt _).hasDerivAt_line
  rw [convexOn_iff_lines hC]
  constructor
  · intro h x hx z
    have h0 : x + (0 : ℝ) • z ∈ C := by simpa using hx
    have hmono : MonotoneOn (deriv fun s : ℝ => f (x + s • z)) {t : ℝ | x + t • z ∈ C} :=
      (h x z).monotoneOn_deriv fun s hs => (hderiv hs).differentiableAt
    have hnn := hmono.derivWithin_nonneg (x := (0 : ℝ))
    rw [derivWithin_of_isOpen (isOpen_line_steps hCopen x z) h0,
      (hasDerivAt_deriv_comp_line hCopen hf h0).deriv] at hnn
    simpa using hnn
  · intro h y z
    refine convexOn_of_deriv2_nonneg' (hC.line_steps y z)
      (fun s hs => (hderiv hs).differentiableAt.differentiableWithinAt)
      (fun s hs =>
        (hasDerivAt_deriv_comp_line hCopen hf hs).differentiableAt.differentiableWithinAt)
      fun s hs => ?_
    change (0 : ℝ) ≤ deriv (deriv fun s : ℝ => f (y + s • z)) s
    rw [(hasDerivAt_deriv_comp_line hCopen hf hs).deriv]
    exact h _ hs z

/-! ### Theorem 4.6 and Corollary 4.6.1 -/

/-- **Theorem 4.6** of [rockafellar1970convex]. For any convex function $f$ on $\mathbb{R}^n$ and
any $\alpha \in [-\infty, +\infty]$, the level sets $\{x \mid f(x) < \alpha\}$ and
$\{x \mid f(x) \le \alpha\}$ are convex.

The value $\alpha$ ranges over `EReal`, including $\pm\infty$. No hypothesis of properness or
finiteness is needed. -/
theorem theorem_4_6 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (α : EReal) :
    Convex ℝ {x | f x < α} ∧ Convex ℝ {x | f x ≤ α} :=
  ⟨hf.convex_lt α, hf.convex_le α⟩

/-- **Corollary 4.6.1** of [rockafellar1970convex]. Let $f_i$ be a convex function on $\mathbb{R}^n$
and $\alpha_i$ a real number for each $i \in I$, where $I$ is an arbitrary index set. Then
$$C = \{x \mid f_i(x) \le \alpha_i,\ \forall i \in I\}$$
is a convex set. -/
theorem corollary_4_6_1 {n : ℕ} {I : Type*} {f : I → Rn n → EReal} (hf : ∀ i, ConvexFn (f i))
    (α : I → ℝ) : Convex ℝ {x : Rn n | ∀ i, f i x ≤ ((α i : ℝ) : EReal)} := by
  have hEq : {x : Rn n | ∀ i, f i x ≤ ((α i : ℝ) : EReal)}
      = ⋂ i, {x : Rn n | f i x ≤ ((α i : ℝ) : EReal)} := by
    ext x; simp
  rw [hEq]
  exact convex_iInter fun i => (hf i).convex_le _

/-! ### Theorem 4.7 and its corollaries -/

/-- **Theorem 4.7** of [rockafellar1970convex]. A positively homogeneous function $f$ from
$\mathbb{R}^n$ to $(-\infty, +\infty]$ is convex if and only if
$$f(x + y) \le f(x) + f(y)$$
for every $x$ and $y$.

Positive homogeneity is `ConvexAnalysis.PosHomogeneous`: $f(\lambda x) = \lambda f(x)$ for all
$x$ and $\lambda > 0$. -/
theorem theorem_4_7 {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hbot : ∀ x, f x ≠ ⊥) :
    ConvexFn f ↔ ∀ x y : Rn n, f (x + y) ≤ f x + f y :=
  hf.convexFn_iff_subadditive hbot

/-- **Corollary 4.7.1** of [rockafellar1970convex]. Let $f$ be a positively homogeneous proper
convex function on $\mathbb{R}^n$, let $m \ge 1$, and let $x_1, \dots, x_m \in \mathbb{R}^n$ and
$\lambda_1 > 0, \dots, \lambda_m > 0$. Then
$$f(\lambda_1 x_1 + \dots + \lambda_m x_m) \le \lambda_1 f(x_1) + \dots + \lambda_m f(x_m).$$

**Reading.** The book writes $\lambda_1, \dots, \lambda_m$, which implies $m \ge 1$. The
statement assumes it explicitly. For $m = 0$ the inequality would read $f(0) \le 0$, and this
can fail: the indicator function $\delta(\cdot \mid C)$ of a non-empty convex cone $C$ that does
not contain the origin is positively homogeneous, proper and convex, with $f(0) = +\infty$. -/
theorem corollary_4_7_1 {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hconv : ConvexFn f)
    (hproper : ProperConvex f) {m : ℕ} (hm : 0 < m) {l : Fin m → ℝ} (hl : ∀ i, 0 < l i)
    (x : Fin m → Rn n) : f (∑ i, l i • x i) ≤ ∑ i, (l i : EReal) * f (x i) :=
  hf.sum_le hconv hproper.ne_bot ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i _ => hl i) x

/-- **Corollary 4.7.2** of [rockafellar1970convex]. Let $f$ be a positively homogeneous proper
convex function on $\mathbb{R}^n$. Then $f(-x) \ge -f(x)$ for every $x$. -/
theorem corollary_4_7_2 {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hconv : ConvexFn f)
    (hproper : ProperConvex f) (x : Rn n) : -(f x) ≤ f (-x) :=
  hf.neg_le hconv hproper.ne_bot x

/-! ### Theorem 4.8 -/

/-- **Theorem 4.8** of [rockafellar1970convex]. Let $f$ be a positively homogeneous proper convex
function on $\mathbb{R}^n$, and let $L$ be a subspace of $\mathbb{R}^n$. Then $f$ is linear on
$L$ if and only if $f(-x) = -f(x)$ for every $x \in L$.

"Linear on $L$" means that there is a linear functional $g : L \to \mathbb{R}$ with
$f(x) = g(x)$ for all $x \in L$. The construction of $g$ is part of the content: a function with
$f(-x) = -f(x)$ is finite at $x$, because $f$ is proper. -/
theorem theorem_4_8 {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hconv : ConvexFn f)
    (hproper : ProperConvex f) (L : Submodule ℝ (Rn n)) :
    (∃ g : L →ₗ[ℝ] ℝ, ∀ x : L, f x = ((g x : ℝ) : EReal)) ↔ ∀ x ∈ L, f (-x) = -(f x) :=
  hf.exists_linearMap_iff hconv hproper.ne_bot L

/-- **Theorem 4.8** of [rockafellar1970convex], last sentence. Let $f$ be a positively homogeneous
proper convex function on $\mathbb{R}^n$, let $L$ be a subspace of $\mathbb{R}^n$, and let $B$
be a non-empty set that spans $L$. If $f(-b) = -f(b)$ for every $b \in B$, then $f(-x) = -f(x)$
for every $x \in L$.

**Correction.** The book states that it suffices to check $f(-b_i) = -f(b_i)$ for the vectors
$b_i$ of a basis of $L$. The argument of the book uses $f(0) = 0$, which follows only once some
vector $b$ satisfies the condition. For $L = \{0\}$ the basis is empty, and the claim fails: a
positively homogeneous proper convex function can have $f(0) = +\infty$. The statement therefore
requires $B$ to be non-empty.

**Generalization.** The statement allows an arbitrary non-empty spanning set of $L$ instead of a
basis. -/
theorem theorem_4_8_basis {n : ℕ} {f : Rn n → EReal} (hf : PosHomogeneous f) (hconv : ConvexFn f)
    (hproper : ProperConvex f) {L : Submodule ℝ (Rn n)} {b : Set (Rn n)} (hb : b.Nonempty)
    (hspan : Submodule.span ℝ b = L) (hodd : ∀ v ∈ b, f (-v) = -(f v)) :
    ∀ x ∈ L, f (-x) = -(f x) := by
  subst hspan
  exact fun x hx => hf.neg_eq_of_mem_span hconv hproper.ne_bot hb hodd hx

end Rockafellar
