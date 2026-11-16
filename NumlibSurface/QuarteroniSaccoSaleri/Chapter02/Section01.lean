/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Numlib.Algebra.Polynomial.Roots
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Conditioning.Problem

/-!
# Quarteroni, Sacco and Saleri, Section 2.1: Well-posedness and Condition Number of a Problem

This module formalizes Section 2.1 of [quarteroni2000numerical]. The book considers a problem
$F(x, d) = 0$ with datum $d$ and solution $x = G(d)$, where $G$ is the resolvent of the problem. A
perturbation $\delta d$ of the datum changes the solution by $\delta x = G(d + \delta d) - G(d)$.
The continuous-dependence condition (2.3) asks for $\|\delta x\| \le K \|\delta d\|$ for small
$\delta d$. Definition 2.1 gives the relative condition number (2.4), the supremum of $(\|\delta x\|
/ \|x\|) / (\|\delta d\| / \|d\|)$, and the absolute condition number (2.5), the supremum of
$\|\delta x\| / \|\delta d\|$. For a differentiable resolvent, (2.7) gives
$K_{abs}(d) \simeq \|G'(d)\|$ and $K(d) \simeq \|G'(d)\| \|d\| / \|G(d)\|$. The examples compute
these numbers for the number of real roots of a polynomial, the roots of $x^2 - 2px + 1$, a linear
system perturbed in its right-hand side, and a root of a nonlinear equation. The example that closes
the section shows that the first-order formula can underestimate the condition number.

The definitions are those of the backbone module `Numlib.Conditioning.Problem`, here over
$\mathbb{R}$ and on the concrete data of the book.

## Main definitions

* Example 2.1, `QuarteroniSaccoSaleri.Chapter02.example_2_1_polynomial`: the polynomial
  $x^4 - x^2(2a - 1) + a(a - 1)$.
* Definition 2.1, `QuarteroniSaccoSaleri.Chapter02.definition_2_1_rel`: the relative condition
  number (2.4) over a set of perturbations.
* Definition 2.1, `QuarteroniSaccoSaleri.Chapter02.definition_2_1_abs`: the absolute condition
  number (2.5) over a set of perturbations.
* Example 2.2, `QuarteroniSaccoSaleri.Chapter02.example_2_2_resolvent`: the roots
  $p \pm \sqrt{p^2 - 1}$ of $x^2 - 2px + 1$ as a function of $p$.

## Main results

* Example 2.1, `QuarteroniSaccoSaleri.Chapter02.example_2_1`: the number of real roots of the
  polynomial is $4$, $2$ or $0$, and it jumps as $a$ varies.
* Definition 2.1, `QuarteroniSaccoSaleri.Chapter02.definition_2_1_rel_eq_abs_mul`:
  $K(d) = K_{abs}(d) \|d\| / \|G(d)\|$.
* Equation (2.3), `QuarteroniSaccoSaleri.Chapter02.equation_2_3_iff`: the Lipschitz condition (2.3)
  holds at radius $\eta$ if and only if the absolute condition number over the perturbations of size
  less than $\eta$ is finite.
* Equation (2.7), `QuarteroniSaccoSaleri.Chapter02.equation_2_7_abs`: the first-order absolute
  condition number is $\|G'(d)\|$.
* Equation (2.7), `QuarteroniSaccoSaleri.Chapter02.equation_2_7_rel`: the first-order relative
  condition number is $\|G'(d)\| \|d\| / \|G(d)\|$.
* Equation (2.7), `QuarteroniSaccoSaleri.Chapter02.equation_2_7_rel_deriv`: the relative form for a
  scalar datum, as a real number.
* Equation (2.7), `QuarteroniSaccoSaleri.Chapter02.equation_2_7_jacobian`: for
  $G : \mathbb{R}^n \to \mathbb{R}^m$ with Jacobian matrix $J$, the absolute condition number is
  $\|J\|_2$.
* Example 2.2, `QuarteroniSaccoSaleri.Chapter02.example_2_2_hasDerivAt`: the derivative of the roots
  with respect to $p$.
* Example 2.2, `QuarteroniSaccoSaleri.Chapter02.example_2_2`: equation (2.8),
  $K(p) = |p| / \sqrt{p^2 - 1}$ in the Euclidean norm.
* Example 2.2, `QuarteroniSaccoSaleri.Chapter02.example_2_2_le_sqrt_two`: for separated roots,
  $p \ge \sqrt{2}$, the condition number is at most $\sqrt{2}$.
* Example 2.2, `QuarteroniSaccoSaleri.Chapter02.example_2_2_reparam`: the reparametrized problem has
  condition number $1$.
* Remark 2.1, `QuarteroniSaccoSaleri.Chapter02.remark_2_1`: the roots depend continuously on
  $p \ge 1$, but the condition number at the double root $p = 1$ is infinite.
* Example 2.3, `QuarteroniSaccoSaleri.Chapter02.example_2_3_eq`: the first equality of (2.9),
  $K(b) = \|A^{-1}\| \|b\| / \|A^{-1} b\|$.
* Example 2.3, `QuarteroniSaccoSaleri.Chapter02.example_2_3`: equation (2.9),
  $K(b) \le \|A\| \|A^{-1}\| = K(A)$.
* Example 2.4, `QuarteroniSaccoSaleri.Chapter02.example_2_4`: equation (2.11),
  $K_{abs}(d) = |\varphi'(x)|^{-1}$ for the root of $\varphi(x) = d$.
* Example 2.4, `QuarteroniSaccoSaleri.Chapter02.example_2_4_rel`: equation (2.10),
  $K(d) = (|d| / |x|) |\varphi'(x)|^{-1}$.
* Example 2.4, `QuarteroniSaccoSaleri.Chapter02.example_2_4_multiple_root`: at a multiple root the
  absolute condition number is infinite.
* Section 2.1, `QuarteroniSaccoSaleri.Chapter02.cosSubOne_absCondNumberWithin`: for
  $G(d) = \cos d - 1$, $K_{abs}(0) = 2/\pi$ while $G'(0) = 0$.

## Implementation notes

* Condition numbers take values in $[0, \infty]$ (`ℝ≥0∞`), as in the backbone, so that an infinite
  condition number (Remark 2.1) is a value. The real values of the book appear through
  `ENNReal.ofReal`.
* `QuarteroniSaccoSaleri.Chapter02.definition_2_1_rel` and
  `QuarteroniSaccoSaleri.Chapter02.definition_2_1_abs` are the backbone's
  `Conditioning.relCondNumberOn` and `Conditioning.absCondNumberOn` by definition
  (`QuarteroniSaccoSaleri.Chapter02.definition_2_1_rel_eq`,
  `QuarteroniSaccoSaleri.Chapter02.definition_2_1_abs_eq`).
* The first-order condition numbers `Conditioning.absCondNumber` and `Conditioning.relCondNumber`
  are the limits, as $\eta \to 0^+$, of the condition numbers over the admissible perturbations of
  size less than $\eta$. This is the quantity that the book's $\simeq$ in (2.7) computes.

## Deviations from the source

* **Equations (2.7)–(2.11)** (reading). The book writes $\simeq$. The statements are equalities for
  the first-order condition numbers. See `QuarteroniSaccoSaleri.Chapter02.equation_2_7_abs`.
* **Example 2.4, multiple root** (reading). The book says that the problem is ill posed if $x$ is a
  multiple root. This is read as infinite conditioning, because the root may depend continuously on
  the datum (Remark 2.1). See `QuarteroniSaccoSaleri.Chapter02.example_2_4_multiple_root`.
-/

open Conditioning Filter Polynomial Set Topology
open scoped ENNReal Real

namespace QuarteroniSaccoSaleri.Chapter02

/-! ### Example 2.1: counting real roots is ill posed -/

/-- **Example 2.1** of [quarteroni2000numerical], the polynomial. For $a \in \mathbb{R}$, this is
the real polynomial
$$x^4 - x^2 (2a - 1) + a (a - 1) = (x^2 - a)(x^2 - (a - 1)).$$
-/
noncomputable def example_2_1_polynomial (a : ℝ) : ℝ[X] :=
  X ^ 4 - C (2 * a - 1) * X ^ 2 + C (a * (a - 1))

/-- **Example 2.1** of [quarteroni2000numerical]. Let $a \in \mathbb{R}$. The number of real roots
of $x^4 - x^2(2a - 1) + a(a - 1)$, counted with multiplicity, is $4$ if $a \ge 1$, $2$ if
$0 \le a < 1$, and $0$ if $a < 0$. The number changes discontinuously as $a$ varies
continuously, so finding the number of real roots of a polynomial is an ill-posed problem.

The polynomial is $(x^2 - a)(x^2 - (a - 1))$. The count is the cardinality of the multiset
`Polynomial.roots`. At $a = 1$ the roots are $\pm 1$ and the double root $0$. -/
theorem example_2_1 (a : ℝ) :
    Multiset.card (example_2_1_polynomial a).roots =
      if 1 ≤ a then 4 else if 0 ≤ a then 2 else 0 := by
  have h : example_2_1_polynomial a = (X ^ 2 - C a) * (X ^ 2 - C (a - 1)) := by
    simp only [example_2_1_polynomial, map_sub, map_mul, map_one, map_ofNat]; ring
  rw [h, roots_mul (mul_ne_zero (X_pow_sub_C_ne_zero two_pos _) (X_pow_sub_C_ne_zero two_pos _)),
    Multiset.card_add, card_roots_X_sq_sub_C, card_roots_X_sq_sub_C]
  split_ifs <;> first | (exfalso; linarith) | norm_num

/-! ### Definition 2.1 and the condition (2.3) -/

section Definition21

variable {D X : Type*} [NormedAddCommGroup D] [NormedAddCommGroup X]

/-- **Definition 2.1** of [quarteroni2000numerical], equation (2.4). Let $D$ and $X$ be normed
abelian groups, let $G : D \to X$ be the resolvent of a problem, let $N \subseteq D$ be a set of
admissible perturbations, and let $d \in D$. With $x = G(d)$ and
$\delta x = G(d + \delta d) - G(d)$, the **relative condition number** of the problem at $d$ is
$$K(d) = \sup_{\delta d \in N,\ \delta d \neq 0} \frac{\|\delta x\| / \|x\|}{\|\delta d\| /
  \|d\|}.$$

The value is in $[0, \infty]$, and the quotients are computed in `ℝ≥0∞`, where $a / 0 = \infty$
for $a \neq 0$ and $0 / 0 = 0$. This is the backbone's `Conditioning.relCondNumberOn`
(`QuarteroniSaccoSaleri.Chapter02.definition_2_1_rel_eq`). -/
noncomputable def definition_2_1_rel (G : D → X) (N : Set D) (d : D) : ℝ≥0∞ :=
  ⨆ (δd : D) (_ : δd ∈ N) (_ : δd ≠ 0), (‖G (d + δd) - G d‖ₑ / ‖G d‖ₑ) / (‖δd‖ₑ / ‖d‖ₑ)

/-- The relative condition number (2.4) of Definition 2.1 of [quarteroni2000numerical] is the
backbone's relative condition number: `QuarteroniSaccoSaleri.Chapter02.definition_2_1_rel G N d`
equals `Conditioning.relCondNumberOn G N d`. -/
theorem definition_2_1_rel_eq (G : D → X) (N : Set D) (d : D) :
    definition_2_1_rel G N d = relCondNumberOn G N d :=
  rfl

/-- **Definition 2.1** of [quarteroni2000numerical], equation (2.5). Let $G : D \to X$,
$N \subseteq D$ and $d \in D$ be as in (2.4), with $\delta x = G(d + \delta d) - G(d)$. The
**absolute condition number** of the problem at $d$ is
$$K_{abs}(d) = \sup_{\delta d \in N,\ \delta d \neq 0} \frac{\|\delta x\|}{\|\delta d\|}.$$
The book introduces it as "necessary whenever $d = 0$ or $x = 0$".

The value is in $[0, \infty]$. This is the backbone's `Conditioning.absCondNumberOn`
(`QuarteroniSaccoSaleri.Chapter02.definition_2_1_abs_eq`). -/
noncomputable def definition_2_1_abs (G : D → X) (N : Set D) (d : D) : ℝ≥0∞ :=
  ⨆ (δd : D) (_ : δd ∈ N) (_ : δd ≠ 0), ‖G (d + δd) - G d‖ₑ / ‖δd‖ₑ

/-- The absolute condition number (2.5) of Definition 2.1 of [quarteroni2000numerical] is the
backbone's absolute condition number: `QuarteroniSaccoSaleri.Chapter02.definition_2_1_abs G N d`
equals `Conditioning.absCondNumberOn G N d`. -/
theorem definition_2_1_abs_eq (G : D → X) (N : Set D) (d : D) :
    definition_2_1_abs G N d = absCondNumberOn G N d :=
  rfl

/-- The two condition numbers of Definition 2.1 of [quarteroni2000numerical] differ by a scale
factor. For $G : D \to X$, $N \subseteq D$ and $d \in D$,
$$K(d) = K_{abs}(d) \, \frac{\|d\|}{\|G(d)\|}.$$

In `ℝ≥0∞` the identity holds without hypotheses. It is meaningful when $d \neq 0$ and
$G(d) \neq 0$, which is why the book uses the absolute number when $d = 0$ or $x = 0$. -/
theorem definition_2_1_rel_eq_abs_mul (G : D → X) (N : Set D) (d : D) :
    definition_2_1_rel G N d = definition_2_1_abs G N d * (‖d‖ₑ / ‖G d‖ₑ) :=
  relCondNumberOn_eq G N d

/-- **Equation (2.3)** of [quarteroni2000numerical], as finiteness of a condition number. Let
$G : D \to X$ be the resolvent on the admissible data $S \subseteq D$, let $d \in D$ and let
$\eta \in \mathbb{R}$. There is a constant $K \in \mathbb{R}$ with
$$\|\delta d\| < \eta \text{ and } d + \delta d \in S \implies \|G(d + \delta d) - G(d)\| \le K
  \|\delta d\|$$
if and only if the absolute condition number of $G$ at $d$ over the admissible perturbations of
size less than $\eta$ is finite.

The book's condition (2.3) is this property for every $\eta > 0$. The condition number is
`Conditioning.absCondNumberWithin G S d η`, which is `Conditioning.absCondNumberOn` over the set
`Conditioning.perturbations S d η`. -/
theorem equation_2_3_iff (G : D → X) (S : Set D) (d : D) (η : ℝ) :
    (∃ K : ℝ, ∀ δd, ‖δd‖ < η → d + δd ∈ S → ‖G (d + δd) - G d‖ ≤ K * ‖δd‖) ↔
      absCondNumberWithin G S d η ≠ ⊤ :=
  (absCondNumberWithin_ne_top_iff G S d η).symm

end Definition21

/-! ### The first-order formula (2.7) -/

section Equation27

variable {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup X]
  [NormedSpace ℝ X] {G : D → X} {G' : D →L[ℝ] X} {d : D} {S : Set D}

/-- **Equation (2.7)** of [quarteroni2000numerical], absolute form. Let $D$ and $X$ be real normed
spaces, let $G : D \to X$ be the resolvent on the admissible data $S \subseteq D$, and let $S$
be a neighbourhood of the datum $d$. If $G$ has the derivative $G'(d)$ at $d$, then
$$K_{abs}(d) = \|G'(d)\|,$$
where $K_{abs}(d)$ is the first-order absolute condition number.

**Reading.** The book writes $K_{abs}(d) \simeq \|G'(d)\|$. The statement is an equality for the
first-order absolute condition number, the limit as $\eta \to 0^+$ of the absolute condition
number over the admissible perturbations of size less than $\eta$. The same reading applies to
(2.8)–(2.11).

The first-order number is `Conditioning.absCondNumber G S d`, and $\|G'(d)\|$ is the operator
norm, taken in `ℝ≥0∞`. -/
theorem equation_2_7_abs (hG : HasFDerivAt G G' d) (hS : S ∈ 𝓝 d) :
    absCondNumber G S d = ‖G'‖ₑ :=
  absCondNumber_eq_enorm_fderiv hG hS

/-- **Equation (2.7)** of [quarteroni2000numerical], relative form. Under the hypotheses of
`QuarteroniSaccoSaleri.Chapter02.equation_2_7_abs`, assume also $d \neq 0$ and $G(d) \neq 0$.
Then the first-order relative condition number is
$$K(d) = \|G'(d)\| \, \frac{\|d\|}{\|G(d)\|}.$$

**Reading.** The book writes $\simeq$; the statement is an equality for the first-order
condition number `Conditioning.relCondNumber G S d`. -/
theorem equation_2_7_rel (hG : HasFDerivAt G G' d) (hS : S ∈ 𝓝 d) (hd : d ≠ 0) (hx : G d ≠ 0) :
    relCondNumber G S d = ‖G'‖ₑ * (‖d‖ₑ / ‖G d‖ₑ) :=
  relCondNumber_eq_enorm_fderiv hG hS hd hx

/-- **Equation (2.7)** of [quarteroni2000numerical], relative form for a scalar datum. Let $E$ be a
real normed space, let $G : \mathbb{R} \to E$ have the derivative $v \in E$ at $d$, and assume
$d \neq 0$ and $G(d) \neq 0$. With all of $\mathbb{R}$ as admissible data, the first-order
relative condition number is the real number
$$K(d) = \frac{\|v\| \, |d|}{\|G(d)\|}.$$
This is how the examples of the book read (2.7) when the datum is a single number.

**Reading.** The book writes $\simeq$; the statement is an equality for the first-order
condition number. -/
theorem equation_2_7_rel_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : ℝ → E}
    {v : E} {d : ℝ} (hG : HasDerivAt G v d) (hd : d ≠ 0) (hx : G d ≠ 0) :
    relCondNumber G univ d = ENNReal.ofReal (‖v‖ * |d| / ‖G d‖) := by
  rw [relCondNumber_eq_enorm_fderiv hG.hasFDerivAt univ_mem hd hx, ← ofReal_norm, ← ofReal_norm,
    ← ofReal_norm, ← ENNReal.ofReal_div_of_pos (norm_pos_iff.2 hx),
    ← ENNReal.ofReal_mul (norm_nonneg _), ContinuousLinearMap.norm_toSpanSingleton,
    Real.norm_eq_abs, mul_div_assoc]

open scoped Matrix.Norms.L2Operator in
/-- **Equation (2.7)** of [quarteroni2000numerical], for $G : \mathbb{R}^n \to \mathbb{R}^m$. Let
$S \subseteq \mathbb{R}^n$ be a neighbourhood of $d$. If $G$ is differentiable at $d$ and its
derivative is the Jacobian matrix $J \in \mathbb{R}^{m \times n}$, then the first-order absolute
condition number is
$$K_{abs}(d) = \|J\|_2,$$
the matrix norm associated with the vector norm (1.19).

**Reading.** The book writes $\simeq$; the statement is an equality for the first-order
condition number.

The spaces are `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin m)`, the derivative is
`Matrix.toEuclideanLin J`, and $\|J\|_2$ is the operator norm of Mathlib's scoped
`Matrix.Norms.L2Operator`. -/
theorem equation_2_7_jacobian {m n : ℕ} {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {J : Matrix (Fin m) (Fin n) ℝ} {d : EuclideanSpace ℝ (Fin n)}
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (hG : HasFDerivAt G (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin J)) d)
    (hS : S ∈ 𝓝 d) : absCondNumber G S d = ENNReal.ofReal ‖J‖ := by
  rw [equation_2_7_abs hG hS, ← ofReal_norm, Matrix.l2_opNorm_def]
  rfl

end Equation27

/-! ### Example 2.2: the roots of $x^2 - 2px + 1$ -/

/-- The Euclidean norm of $(a, b) \in \mathbb{R}^2$ is $\sqrt{a^2 + b^2}$. -/
private theorem norm_fin_two (a b : ℝ) :
    ‖(!₂[a, b] : EuclideanSpace ℝ (Fin 2))‖ = √(a ^ 2 + b ^ 2) := by
  rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two]

/-- **Example 2.2** of [quarteroni2000numerical], the resolvent. This is the map
$G : \mathbb{R} \to \mathbb{R}^2$, $G(p) = (x_+, x_-)$ with $x_\pm = p \pm \sqrt{p^2 - 1}$, the
roots of $x^2 - 2px + 1 = 0$.

It is a resolvent of the problem for $p \ge 1$. The map is total because `Real.sqrt` is $0$ on
negative numbers. The values are in `EuclideanSpace ℝ (Fin 2)`, with the Euclidean norm. -/
noncomputable def example_2_2_resolvent (p : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[p + √(p ^ 2 - 1), p - √(p ^ 2 - 1)]

/-- For $p > 1$, the resolvent $G$ of Example 2.2 of [quarteroni2000numerical] has the derivative
$$G'(p) = \Bigl(1 + \frac{p}{\sqrt{p^2 - 1}},\ 1 - \frac{p}{\sqrt{p^2 - 1}}\Bigr).$$
-/
theorem example_2_2_hasDerivAt {p : ℝ} (hp : 1 < p) :
    HasDerivAt example_2_2_resolvent !₂[1 + p / √(p ^ 2 - 1), 1 - p / √(p ^ 2 - 1)] p := by
  have h1 : p ^ 2 - 1 ≠ 0 := by nlinarith
  have hs : HasDerivAt (fun x : ℝ => √(x ^ 2 - 1)) (p / √(p ^ 2 - 1)) p := by
    have := ((hasDerivAt_pow 2 p).sub_const 1).sqrt h1
    convert this using 1
    field_simp
    ring
  have hg : HasDerivAt (fun x : ℝ => ![x + √(x ^ 2 - 1), x - √(x ^ 2 - 1)])
      ![1 + p / √(p ^ 2 - 1), 1 - p / √(p ^ 2 - 1)] p := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact (hasDerivAt_id' p).add hs
    · exact (hasDerivAt_id' p).sub hs
  exact (PiLp.hasFDerivAt_toLp 2 _).comp_hasDerivAt p hg

/-- **Example 2.2** of [quarteroni2000numerical], equation (2.8). Let $p > 1$. In the Euclidean norm
of $\mathbb{R}^2$, the first-order relative condition number of the roots of $x^2 - 2px + 1 = 0$
with respect to the coefficient $p$ is
$$K(p) = \frac{|p|}{\sqrt{p^2 - 1}}.$$

**Reading.** The book writes $\simeq$. In the Euclidean norm, (2.7) gives an equality:
$\|G'(p)\|^2 = 2(2p^2 - 1)/(p^2 - 1)$ and $\|G(p)\|^2 = 4p^2 - 2$, so $\|G'(p)\| \, |p| /
\|G(p)\| = |p| / \sqrt{p^2 - 1}$.

The condition number is `Conditioning.relCondNumber` of
`QuarteroniSaccoSaleri.Chapter02.example_2_2_resolvent`, with all of $\mathbb{R}$ as admissible
data. -/
theorem example_2_2 {p : ℝ} (hp : 1 < p) :
    relCondNumber example_2_2_resolvent univ p = ENNReal.ofReal (|p| / √(p ^ 2 - 1)) := by
  have h1 : 0 < p ^ 2 - 1 := by nlinarith
  have hs : 0 < √(p ^ 2 - 1) := Real.sqrt_pos.2 h1
  have hp0 : 0 < p := by linarith
  have hG : example_2_2_resolvent p ≠ 0 := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h
    simp [example_2_2_resolvent] at this
    linarith
  rw [equation_2_7_rel_deriv (example_2_2_hasDerivAt hp) hp0.ne' hG]
  congr 1
  rw [example_2_2_resolvent, norm_fin_two, norm_fin_two, abs_of_pos hp0]
  have hA : (1 + p / √(p ^ 2 - 1)) ^ 2 + (1 - p / √(p ^ 2 - 1)) ^ 2 =
      ((p + √(p ^ 2 - 1)) ^ 2 + (p - √(p ^ 2 - 1)) ^ 2) / √(p ^ 2 - 1) ^ 2 := by
    field_simp
    ring
  have hB : 0 < (p + √(p ^ 2 - 1)) ^ 2 + (p - √(p ^ 2 - 1)) ^ 2 := by positivity
  rw [hA, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hs.le]
  field_simp

/-- **Example 2.2** of [quarteroni2000numerical], separated roots. If $p \ge \sqrt{2}$, then the
first-order relative condition number of Example 2.2 satisfies $K(p) \le \sqrt{2}$. In the words
of the book, "in the case of separated roots (say, if $p \ge \sqrt{2}$) the problem is well
conditioned".

The bound holds because $|p| / \sqrt{p^2 - 1} \le \sqrt{2}$ if and only if $2 \le p^2$. -/
theorem example_2_2_le_sqrt_two {p : ℝ} (hp : √2 ≤ p) :
    relCondNumber example_2_2_resolvent univ p ≤ ENNReal.ofReal (√2) := by
  have h2 : (1 : ℝ) < √2 := by rw [Real.lt_sqrt] <;> norm_num
  have hp1 : 1 < p := h2.trans_le hp
  have hsq : 2 ≤ p ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  rw [example_2_2 hp1]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (Real.sqrt_pos.2 (by nlinarith)), abs_of_pos (by linarith),
    ← Real.sqrt_mul (by norm_num), Real.le_sqrt (by linarith) (by nlinarith)]
  nlinarith

/-- **Example 2.2** of [quarteroni2000numerical], the reparametrized problem. With
$t = p + \sqrt{p^2 - 1}$, the two roots are $t$ and $1/t$, regular functions of $t$. For
$t \neq 0$, the map $t \mapsto (t, 1/t) \in \mathbb{R}^2$ has first-order relative condition
number $1$ in the Euclidean norm. The transformed problem is well conditioned, and at $t = 1$
the double root is no longer singular.

**Reading.** The book writes $K(t) \simeq 1$ "for any value of $t$". Here (2.7) gives an
equality: $\|G'(t)\| \, |t| / \|G(t)\| = \sqrt{1 + t^{-4}} \, |t| / \sqrt{t^2 + t^{-2}} = 1$. -/
theorem example_2_2_reparam {t : ℝ} (ht : t ≠ 0) :
    relCondNumber (fun t : ℝ => (!₂[t, 1 / t] : EuclideanSpace ℝ (Fin 2))) univ t = 1 := by
  have hd : HasDerivAt (fun t : ℝ => (!₂[t, 1 / t] : EuclideanSpace ℝ (Fin 2)))
      !₂[1, -1 / t ^ 2] t := by
    have hg : HasDerivAt (fun x : ℝ => ![x, 1 / x]) ![1, -1 / t ^ 2] t := by
      rw [hasDerivAt_pi]
      intro i
      fin_cases i
      · exact hasDerivAt_id' t
      · simpa [one_div, neg_div] using hasDerivAt_inv ht
    exact (PiLp.hasFDerivAt_toLp 2 _).comp_hasDerivAt t hg
  have hG : (!₂[t, 1 / t] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h)
  rw [equation_2_7_rel_deriv hd ht hG, norm_fin_two, norm_fin_two, ENNReal.ofReal_eq_one,
    div_eq_one_iff_eq (by positivity), ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

/-- **Remark 2.1** of [quarteroni2000numerical] (ill-posed problems). The resolvent of Example 2.2
is continuous on $[1, \infty)$, so the problem is well posed for the admissible data $p \ge 1$.
Yet at the double root $p = 1$, the first-order absolute condition number within $[1, \infty)$
is infinite. This is the remark of the book that "there exist well posed problems (for instance,
the search of multiple roots of algebraic equations, see Example 2.2) for which the condition
number is infinite".

The second clause is an instance of the backbone's
`Conditioning.absCondNumber_eq_top_of_fderiv_eq_zero` with $\varphi(x_+) = (x_+^2 + 1)/(2 x_+)$
and $\varphi'(1) = 0$. It is stated within $S = [1, \infty)$, because the roots exist only on
one side of $p = 1$. -/
theorem remark_2_1 :
    ContinuousOn example_2_2_resolvent (Ici 1) ∧
      absCondNumber example_2_2_resolvent (Ici 1) 1 = ⊤ := by
  have hcont : Continuous example_2_2_resolvent := by unfold example_2_2_resolvent; fun_prop
  refine ⟨hcont.continuousOn, ?_⟩
  have : NeBot (𝓝[Ici (1 : ℝ) \ {1}] 1) := by rw [Set.Ici_sdiff_left]; infer_instance
  set ψ : ℝ → ℝ := fun u => (u ^ 2 + 1) / (2 * u) with hψdef
  have h0 : example_2_2_resolvent 1 0 = 1 := by simp [example_2_2_resolvent]
  have hψ : HasDerivAt ψ 0 (example_2_2_resolvent 1 0) := by
    rw [h0]
    have h := ((hasDerivAt_pow 2 (1 : ℝ)).add_const 1).div
      ((hasDerivAt_id' (1 : ℝ)).const_mul 2) (by norm_num)
    exact h.congr_deriv (by norm_num)
  refine absCondNumber_eq_top_of_fderiv_eq_zero (𝕜 := ℝ)
    (φ := fun x : EuclideanSpace ℝ (Fin 2) => ψ (x 0)) hcont.continuousWithinAt ?_ ?_
  · have := hψ.comp_hasFDerivAt (example_2_2_resolvent 1)
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (example_2_2_resolvent 1) 0)
    rw [zero_smul] at this
    exact this
  · filter_upwards [eventually_mem_nhdsWithin] with y (hy : 1 ≤ y)
    have hs : √(y ^ 2 - 1) ^ 2 = y ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
    have hpos : 0 < y + √(y ^ 2 - 1) := by positivity
    simp only [example_2_2_resolvent, hψdef, PiLp.toLp_apply, Matrix.cons_val_zero]
    rw [div_eq_iff (by positivity)]
    linear_combination hs

/-! ### Example 2.3: a linear system perturbed in its right-hand side -/

section Example23

open scoped Matrix.Norms.L2Operator

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Example 2.3** of [quarteroni2000numerical], the first equality of (2.9). Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular and let $b \in \mathbb{R}^n$, $b \neq 0$. The
problem $Ax = b$, perturbed in the right-hand side $b$ only, has the resolvent $G(b) = A^{-1} b$
with $G'(b) = A^{-1}$. In the Euclidean norms, its first-order relative condition number is
$$K(b) = \|A^{-1}\|_2 \, \frac{\|b\|_2}{\|A^{-1} b\|_2}.$$

**Reading.** The book writes $\simeq$; the statement is an equality for the first-order
condition number.

The resolvent is `Matrix.toEuclideanCLM A⁻¹`, all of $\mathbb{R}^n$ is admissible, and
$\|A^{-1}\|_2$ is the operator norm of Mathlib's scoped `Matrix.Norms.L2Operator`. -/
theorem example_2_3_eq (hA : IsUnit A) {b : EuclideanSpace ℝ (Fin n)} (hb : b ≠ 0) :
    relCondNumber (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹) univ b =
      ENNReal.ofReal (‖A⁻¹‖ * ‖b‖ / ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ b‖) := by
  have hAb : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ b ≠ 0 := by
    intro h
    have := Matrix.toEuclideanLin_mul_nonsing_inv_apply hA b
    change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ b) = b at this
    rw [h, map_zero] at this
    exact hb this.symm
  rw [relCondNumber_eq _ _ hb hAb, absCondNumber_continuousLinearMap _ univ_mem, ← ofReal_norm,
    ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_div_of_pos (norm_pos_iff.2 hAb),
    ← ENNReal.ofReal_mul (norm_nonneg _), Matrix.cstar_norm_def, mul_div_assoc]

/-- **Example 2.3** of [quarteroni2000numerical], equation (2.9). Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular and let $b \in \mathbb{R}^n$, $b \neq 0$. The
first-order relative condition number of the problem $Ax = b$ with respect to $b$ satisfies
$$K(b) \le \|A\|_2 \|A^{-1}\|_2 = K(A),$$
the condition number of $A$ in the Euclidean operator norm. In the words of the book, "if $A$ is
well conditioned, solving the linear system $Ax = b$ is a stable problem with respect to
perturbations of the right-hand side $b$".

$K(A)$ is `NormedRing.condNumber A` for the scoped `Matrix.Norms.L2Operator` norm. -/
theorem example_2_3 (hA : IsUnit A) {b : EuclideanSpace ℝ (Fin n)} (hb : b ≠ 0) :
    relCondNumber (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹) univ b ≤
      ENNReal.ofReal (NormedRing.condNumber A) := by
  have hu : IsUnit (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) := hA.map _
  set e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofUnit hu.unit with he_def
  have he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A := by
    ext x; rfl
  have hsymm : (e.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ := by
    rw [← ContinuousLinearEquiv.ring_inverse_coe, he, Matrix.toEuclideanCLM_nonsing_inv hA]
  have hκ : e.condNumber = NormedRing.condNumber A := by
    rw [ContinuousLinearEquiv.condNumber, he, hsymm, NormedRing.condNumber,
      ← Matrix.nonsing_inv_eq_ringInverse]
    rfl
  have hfun : (⇑e.symm : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
      ⇑(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹) := by
    rw [← hsymm]; rfl
  rw [← hfun, ← hκ]
  exact relCondNumber_symm_le_condNumber e hb

end Example23

/-! ### Example 2.4: the root of a nonlinear equation -/

section Example24

variable {φ G : ℝ → ℝ} {d : ℝ}

/-- **Example 2.4** of [quarteroni2000numerical], equation (2.11). Let
$\varphi : \mathbb{R} \to \mathbb{R}$ be of class $C^1$, consider the equation $\varphi(x) = d$,
and let $G : \mathbb{R} \to \mathbb{R}$ be continuous at $d$ with $\varphi(G(y)) = y$ for all
$y$ near $d$. If the root $x = G(d)$ is simple, $\varphi'(x) \neq 0$, then the first-order
absolute condition number is
$$K_{abs}(d) = |\varphi'(x)|^{-1}.$$
The problem "is ill conditioned when $\varphi'(x)$ is small, well conditioned when $\varphi'(x)$
is large".

**Reading.** The book writes $\simeq$; the statement is an equality for the first-order
condition number, with all of $\mathbb{R}$ as admissible data.

$G$ is a continuous local inverse of $\varphi$ near $d$. -/
theorem example_2_4 (hφ : ContDiff ℝ 1 φ) (hG : ContinuousAt G d)
    (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y) (hφ' : deriv φ (G d) ≠ 0) :
    absCondNumber G univ d = ENNReal.ofReal |deriv φ (G d)|⁻¹ := by
  rw [absCondNumber_of_local_left_inverse hG (ContDiffAt.hasStrictDerivAt hφ.contDiffAt one_ne_zero)
    hφ' hinv, ← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_inv_of_pos (abs_pos.2 hφ')]

/-- **Example 2.4** of [quarteroni2000numerical], equation (2.10). Under the hypotheses of
`QuarteroniSaccoSaleri.Chapter02.example_2_4`, assume also $d \neq 0$ and $x = G(d) \neq 0$.
Then the first-order relative condition number is
$$K(d) = \frac{|d|}{|x|} \, |\varphi'(x)|^{-1}.$$

**Reading.** The book writes $\simeq$; the statement is an equality for the first-order
condition number. -/
theorem example_2_4_rel (hφ : ContDiff ℝ 1 φ) (hG : ContinuousAt G d)
    (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y) (hφ' : deriv φ (G d) ≠ 0) (hd : d ≠ 0) (hx : G d ≠ 0) :
    relCondNumber G univ d = ENNReal.ofReal (|d| / |G d| * |deriv φ (G d)|⁻¹) := by
  rw [relCondNumber_of_local_left_inverse hG (ContDiffAt.hasStrictDerivAt hφ.contDiffAt one_ne_zero)
    hφ' hinv hd hx, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs, ← ENNReal.ofReal_inv_of_pos (abs_pos.2 hφ'),
    ← ENNReal.ofReal_div_of_pos (abs_pos.2 hx), ← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- **Example 2.4** of [quarteroni2000numerical], the multiple root. Let $\varphi$ and $G$ be as in
`QuarteroniSaccoSaleri.Chapter02.example_2_4`, but with $\varphi'(x) = 0$ at the root
$x = G(d)$. Then the first-order absolute condition number is infinite, $K_{abs}(d) = \infty$.

**Reading.** The book says "the problem is thus ill posed if $x$ is a multiple root". The
statement reads this as infinite conditioning: $G$ is continuous at $d$ by hypothesis, so the
problem may be well posed, as Remark 2.1 observes. -/
theorem example_2_4_multiple_root (hφ : ContDiff ℝ 1 φ) (hG : ContinuousAt G d)
    (hinv : ∀ᶠ y in 𝓝 d, φ (G y) = y) (hφ' : deriv φ (G d) = 0) :
    absCondNumber G univ d = ⊤ := by
  have : NeBot (𝓝[(univ : Set ℝ) \ {d}] d) := by rw [← Set.compl_eq_univ_sdiff]; infer_instance
  refine absCondNumber_eq_top_of_deriv_eq_zero hG.continuousWithinAt ?_ (by rwa [nhdsWithin_univ])
  have h : HasDerivAt φ (deriv φ (G d)) (G d) :=
    (ContDiffAt.hasStrictDerivAt hφ.contDiffAt one_ne_zero).hasDerivAt
  rwa [hφ'] at h

end Example24

/-! ### The first-order condition number can underestimate the true one -/

/-- **Section 2.1** of [quarteroni2000numerical], the example that closes the section. Let
$G(d) = \cos d - 1$. The absolute condition number of $G$ at $d = 0$ over the perturbations with
$|\delta d| < \pi/2$ is
$$K_{abs}(0) = \frac{2}{\pi},$$
while $G'(0) = 0$. So the first-order absolute condition number $\|G'(d)\|$ "does not always
provide a sound estimate of the condition number $K_{abs}(d)$".

The ratio $(1 - \cos \delta d) / |\delta d|$ is bounded by $2/\pi$, the slope of the chord of
the convex function $1 - \cos$ from $0$ to $\pi/2$, and it tends to $2/\pi$ as
$\delta d \to \pi/2$. So the supremum over the open interval is $2/\pi$, and it is not attained.
The condition number is `Conditioning.absCondNumberWithin` with all of $\mathbb{R}$ as
admissible data. The result agrees with the backbone's
`Conditioning.enorm_fderiv_le_absCondNumberWithin`, since $0 \le 2/\pi$, and with the
first-order value `Conditioning.absCondNumber G univ 0 = 0` from (2.7). -/
theorem cosSubOne_absCondNumberWithin :
    absCondNumberWithin (fun d : ℝ => Real.cos d - 1) univ 0 (π / 2) =
      ENNReal.ofReal (2 / π) := by
  refine le_antisymm ?_ ?_
  · refine absCondNumberOn_le_of_forall_norm_sub_le (by positivity) fun δd hδd _ => ?_
    have h1 : |δd| ≤ π / 2 := (Real.norm_eq_abs δd ▸ hδd.1).le
    simp only [zero_add, Real.cos_zero, sub_self, sub_zero, Real.norm_eq_abs]
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (Real.cos_le_one _)), ← Real.cos_abs]
    linarith [Real.one_sub_mul_le_cos (abs_nonneg δd) h1]
  · have hlim : Tendsto (fun x : ℝ => ‖(Real.cos (0 + x) - 1) - (Real.cos 0 - 1)‖ₑ / ‖x‖ₑ)
        (𝓝[<] (π / 2)) (𝓝 (ENNReal.ofReal (2 / π))) := by
      have hnum : Tendsto (fun x : ℝ => ‖(Real.cos (0 + x) - 1) - (Real.cos 0 - 1)‖ₑ)
          (𝓝[<] (π / 2)) (𝓝 ‖(Real.cos (0 + π / 2) - 1) - (Real.cos 0 - 1)‖ₑ) :=
        ((continuous_enorm.comp (by fun_prop)).tendsto _).mono_left nhdsWithin_le_nhds
      have hden : Tendsto (fun x : ℝ => ‖x‖ₑ) (𝓝[<] (π / 2)) (𝓝 ‖π / 2‖ₑ) :=
        (continuous_enorm.tendsto _).mono_left nhdsWithin_le_nhds
      have := ENNReal.Tendsto.div hnum (Or.inr (enorm_ne_zero.2 (by positivity))) hden
        (Or.inl enorm_ne_top)
      convert this using 2
      simp only [zero_add, Real.cos_pi_div_two, Real.cos_zero, sub_self, sub_zero, zero_sub,
        enorm_neg, enorm_one]
      rw [Real.enorm_eq_ofReal (by positivity), one_div,
        ← ENNReal.ofReal_inv_of_pos (by positivity)]
      congr 1
      field_simp
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT (by positivity : (0 : ℝ) < π / 2)] with x hx
    refine le_absCondNumberOn (G := fun d : ℝ => Real.cos d - 1)
      (N := perturbations univ 0 (π / 2)) (d := 0) ?_ hx.1.ne'
    exact ⟨by rw [Real.norm_eq_abs, abs_of_pos hx.1]; exact hx.2, mem_univ _⟩

end QuarteroniSaccoSaleri.Chapter02
