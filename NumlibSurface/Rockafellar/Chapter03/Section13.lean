/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Barrier
import Numlib.Analysis.Convex.Duality.Level
import Numlib.Analysis.Convex.Duality.SupportRelint
import Numlib.Analysis.Convex.Recession.Conjugate
import Numlib.Analysis.Convex.Subdifferential.Convergence
import NumlibSurface.Rockafellar.Chapter01.Section01

/-!
# Rockafellar, Section 13: Support functions

This module formalizes Section 13 of [rockafellar1970convex]. The support function of a set
$C \subseteq \mathbb{R}^n$ is $\delta^*(x^* \mid C) = \sup \{\langle x, x^* \rangle \mid x \in C\}$,
the conjugate of the indicator function of $C$. The section reads the closure, relative interior,
interior and affine hull of a convex set off its support function, shows that the support functions
of non-empty convex sets are exactly the closed proper positively homogeneous convex functions, and
expresses the support functions of $\operatorname{dom} f$, of $\operatorname{dom} f^*$ and of a
level set $\{x \mid f(x) \le 0\}$ through the conjugate $f^*$ and the recession function. All 15
numbered results of the section are formalized. The proofs specialize
`Numlib.Analysis.Convex.Duality.Support`, `Numlib.Analysis.Convex.Duality.Level` and
`Numlib.Analysis.Convex.Recession.Conjugate` to the self-pairing of $\mathbb{R}^n$.

The unnumbered text of the section is formalized as well: the formula $\inf \{\langle x, x^* \rangle
\mid x \in C\} = -\delta^*(-x^* \mid C)$, the description of the closed half-spaces that contain
$C$, the identities $\delta^*(\cdot \mid C) = \delta^*(\cdot \mid \operatorname{cl} C) =
\delta^*(\cdot \mid \operatorname{ri} C)$ and $\delta^*(\cdot \mid C_1 + C_2) = \delta^*(\cdot \mid
C_1) + \delta^*(\cdot \mid C_2)$, the recovery of a closed convex set from its support function, the
subadditivity of support functions, and the Euclidean norm as the support function of the unit ball.

## Main definitions

* `Rockafellar.barrierCone`: the barrier cone of $C$, the effective domain of
  $\delta^*(\cdot \mid C)$.
* `Rockafellar.rankFn`: the rank of a convex function, $\operatorname{rank} f =
  \dim(\operatorname{dom} f) - \operatorname{lineality} f$.

## Main results

* Theorem 13.1, `Rockafellar.theorem_13_1_cl`, `Rockafellar.theorem_13_1_ri`,
  `Rockafellar.theorem_13_1_int`, `Rockafellar.theorem_13_1_aff`: membership of $x$ in
  $\operatorname{cl} C$, $\operatorname{ri} C$, $\operatorname{int} C$ and $\operatorname{aff} C$ in
  terms of $\delta^*(\cdot \mid C)$.
* Corollary 13.1.1, `Rockafellar.corollary_13_1_1`: for convex $C_1, C_2$, $\operatorname{cl} C_1
  \subseteq \operatorname{cl} C_2$ if and only if $\delta^*(\cdot \mid C_1) \le \delta^*(\cdot \mid
  C_2)$.
* Theorem 13.2, `Rockafellar.theorem_13_2_conj_indicator`, `Rockafellar.theorem_13_2_conj`,
  `Rockafellar.theorem_13_2`, `Rockafellar.theorem_13_2_correspondence`: the indicator function and
  the support function of a closed convex set are conjugate, and the support functions of non-empty
  convex sets are exactly the closed proper positively homogeneous convex functions.
* Corollary 13.2.1, `Rockafellar.corollary_13_2_1`: the closure of a positively homogeneous convex
  function that is not identically $+\infty$ is a support function.
* Corollary 13.2.2, `Rockafellar.corollary_13_2_2`: the support functions of the non-empty bounded
  convex sets are the finite positively homogeneous convex functions.
* Theorem 13.3, `Rockafellar.theorem_13_3`, `Rockafellar.theorem_13_3_dual`: the support function of
  $\operatorname{dom} f$ is $f^* 0^+$, and the support function of $\operatorname{dom} f^*$ is
  $f 0^+$ for closed $f$.
* Corollary 13.3.1, `Rockafellar.corollary_13_3_1`: $f^*$ is finite everywhere if and only if $f$ is
  co-finite.
* Corollary 13.3.2, `Rockafellar.corollary_13_3_2`: $\operatorname{dom} f^*$ is affine if and only
  if $(f 0^+)(y) = +\infty$ for every $y$ outside the lineality space of $f$.
* Corollary 13.3.3, `Rockafellar.corollary_13_3_3`, `Rockafellar.corollary_13_3_3_finite`,
  `Rockafellar.corollary_13_3_3_least`: $\operatorname{dom} f^*$ is bounded if and only if $f$ is
  finite and satisfies a global Lipschitz condition, and the least Lipschitz constant is $\sup
  \{|x^*| \mid x^* \in \operatorname{dom} f^*\}$.
* Corollary 13.3.4, `Rockafellar.corollary_13_3_4_a`, `Rockafellar.corollary_13_3_4_b`,
  `Rockafellar.corollary_13_3_4_c`, `Rockafellar.corollary_13_3_4_d`: membership of $x^*$ in the
  closure, relative interior, interior and affine hull of $\operatorname{dom} f^*$ in terms of
  $f 0^+$.
* Theorem 13.4, `Rockafellar.theorem_13_4`, `Rockafellar.theorem_13_4_dual`,
  `Rockafellar.theorem_13_4_lineality`, `Rockafellar.theorem_13_4_dimension`: the lineality space of
  $f^*$ and the affine hull of $\operatorname{dom} f$ are orthogonal, and
  $\operatorname{lineality} f^* = n - \dim f$, $\dim f^* = n - \operatorname{lineality} f$.
* Corollary 13.4.1, `Rockafellar.corollary_13_4_1`: conjugate closed proper convex functions have
  the same rank.
* Corollary 13.4.2, `Rockafellar.corollary_13_4_2`: $\operatorname{int}(\operatorname{dom} f^*) \ne
  \emptyset$ if and only if there is no line along which $f$ is affine.
* Theorem 13.5, `Rockafellar.theorem_13_5`, `Rockafellar.theorem_13_5_dual`: the support function of
  $\{x \mid f(x) \le 0\}$ is the closure of the positively homogeneous convex function generated by
  $f^*$, and dually.
* Corollary 13.5.1, `Rockafellar.corollary_13_5_1`: the closure of the homogenization of $f$ is the
  support function of $\{(\lambda^*, x^*) \mid \lambda^* \le -f^*(x^*)\}$.

## Conventions

* The support function $\delta^*(\cdot \mid C)$ is
  `ConvexAnalysis.supportFn (Rockafellar.pairing n) C`. The supremum of the empty set is $-\infty$,
  so $\delta^*(\cdot \mid \emptyset) \equiv -\infty$.
* The relative interior $\operatorname{ri} C$ is `intrinsicInterior ℝ C`.
* The affine hull $\operatorname{aff} C$ is `affineSpan ℝ C`, and the subspace parallel to it is
  `vectorSpan ℝ C`.
* The recession function $f 0^+$ is `ConvexAnalysis.recessionFn f`, the lineality space of $f$ is
  `ConvexAnalysis.linealitySpaceFn f`, and the lineality of $f$ is `ConvexAnalysis.linealityFn f`.
  The dimension of a set is `Rockafellar.dim` of Section 1, with $\dim \emptyset = -1$.

## Implementation notes

* The backbone results behind Theorems 13.3 and 13.4 ask, besides properness of $f$, for $f^*$ to be
  proper. On $\mathbb{R}^n$ this is automatic by Theorem 12.2 and Theorem 7.4, so the surface
  statements carry only the hypotheses of the book.

## Deviations from the source

* **Section 13, support and barrier cones** (generalization). The support formula, barrier cone,
  infimum and containment formulas, closure invariance, additivity, and subadditivity are stated
  for sets without a convexity hypothesis. The addition formula also admits empty sets.
* **Section 8, rank** (generalization). `Rockafellar.rankFn` extends the dimension-minus-lineality
  formula from proper convex functions to all ambient functions.
* **Theorem 13.1**, interior clause (correction). The book omits the hypothesis $C \ne \emptyset$,
  and the clause is false without it. See `Rockafellar.theorem_13_1_int`.
* **Theorem 13.1**, affine hull clause (generalization). The set $C$ need not be convex. See
  `Rockafellar.theorem_13_1_aff`.
* **Theorem 13.2**, $\delta(\cdot \mid C)^* = \delta^*(\cdot \mid C)$ (generalization). This
  direction holds for every set $C$. See `Rockafellar.theorem_13_2_conj_indicator`.
* **Corollary 13.2.2** (reading). The representing bounded set may be nonconvex, and the output
  is explicitly closed. Taking the convex hull preserves the support function and boundedness,
  and every finite convex function on $\mathbb{R}^n$ is closed.
* **Corollary 13.3.1** (reading). The book assumes closed convexity and states finiteness of
  $f^*$. The Lean result assumes properness of $f$ as well so that the condition
  $\operatorname{dom} f^* = \mathbb{R}^n$ implies finiteness.
* **Corollary 13.3.2**, affine characterization in proof (reading). The support-function
  formulation assumes a nonempty convex set so its finite upper bounds correspond to finite
  suprema. See `Rockafellar.affine_iff_forall_reversible`.
* **Theorem 13.5** (generalization). The first assertion needs $f$ closed and convex but not proper,
  and the dual assertion needs no hypothesis. See `Rockafellar.theorem_13_5` and
  `Rockafellar.theorem_13_5_dual`.
* **Corollary 13.5.1** (reading). The three-case function $k$ of the book is stated as the closure
  of the homogenization `ConvexAnalysis.hom f`. See `Rockafellar.corollary_13_5_1`.
* **Corollary 13.5.1** (generalization). The function $f$ need only be convex with non-empty
  effective domain. See `Rockafellar.corollary_13_5_1`.

## Not formalized

* **Corollary 13.3.3 for a nonclosed proper convex function.** The declarations assume $f$ closed.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ}

/-! ### The definitions of Section 13 -/

/-- **Section 13** of [rockafellar1970convex], the support function (p. 112). For
$C \subseteq \mathbb{R}^n$ and $x^* \in \mathbb{R}^n$,
$$\delta^*(x^* \mid C) = \sup \{\langle x, x^* \rangle \mid x \in C\}.$$

The support function is `ConvexAnalysis.supportFn (Rockafellar.pairing n) C`.

**Generalization.** The book introduces the formula for a convex set. The formula here
applies to every set. -/
theorem supportFn_apply_rn (C : Set (Rn n)) (y : Rn n) :
    supportFn (pairing n) C y = ⨆ x ∈ C, ((inner ℝ x y : ℝ) : EReal) :=
  supportFn_apply (pairing n) C y

/-- **Section 13** of [rockafellar1970convex], the barrier cone (p. 112). The **barrier cone** of
$C \subseteq \mathbb{R}^n$ is the effective domain of $\delta^*(\cdot \mid C)$: the set of $x^*$
such that the linear function $\langle \cdot, x^* \rangle$ is bounded above on $C$.

**Generalization.** The book introduces the barrier cone for convex $C$. This definition
applies to arbitrary $C$. -/
noncomputable def barrierCone (C : Set (Rn n)) : Set (Rn n) := convexDom (supportFn (pairing n) C)

/-- The barrier cone of $C$ is the effective domain $\{x^* \mid \delta^*(x^* \mid C) < +\infty\}$ of
the support function of $C$.

**Generalization.** This also applies to the nonconvex inputs of `Rockafellar.barrierCone`. -/
theorem barrierCone_eq_convexDom_supportFn (C : Set (Rn n)) :
    barrierCone C = convexDom (supportFn (pairing n) C) := rfl

/-- A vector $x^*$ lies in the barrier cone of $C$ if and only if there is $c \in \mathbb{R}$ with
$\langle x, x^* \rangle \le c$ for every $x \in C$.

**Generalization.** The book gives the characterization for convex sets. It also holds for
arbitrary sets. -/
theorem mem_barrierCone_iff (C : Set (Rn n)) (y : Rn n) :
    y ∈ barrierCone C ↔ ∃ c : ℝ, ∀ x ∈ C, inner ℝ x y ≤ c := by
  rw [barrierCone_eq_convexDom_supportFn, convexDom_supportFn]
  exact Iff.rfl

/-- **Section 13** of [rockafellar1970convex], co-finite functions (p. 116). A function $f$ on
$\mathbb{R}^n$ is co-finite (`ConvexAnalysis.Cofinite`) if and only if $f$ is a closed proper
convex function and $(f 0^+)(y) = +\infty$ for every $y \ne 0$, that is, the epigraph of $f$
contains no non-vertical half-line. -/
theorem cofinite_iff_rn (f : Rn n → EReal) :
    Cofinite f ↔ ClosedProperConvexFn f ∧ ∀ y : Rn n, y ≠ 0 → recessionFn f y = ⊤ :=
  ⟨fun h => ⟨h.toClosedProperConvexFn, h.recessionFn_eq_top⟩,
    fun h => { h.1 with recessionFn_eq_top := h.2 }⟩

/-- **Section 8** of [rockafellar1970convex], the rank of a convex function (p. 70). The **rank** of
$f$ is
$$\operatorname{rank} f = \dim f - \operatorname{lineality} f,$$
where $\dim f$ is the dimension of $\operatorname{dom} f$ and $\operatorname{lineality} f$ is
the dimension of the lineality space of $f$.

The value is an integer, and $\dim \emptyset = -1$. The definition uses `Rockafellar.dim` of
Section 1. Corollary 13.4.1 is the first result that uses it.

**Generalization.** The book defines rank for proper convex functions. The Lean formula
is defined on all extended-real functions. -/
noncomputable def rankFn (f : Rn n → EReal) : ℤ := dim (convexDom f) - (linealityFn f : ℤ)

/-!
### Properness of the conjugate

The book states Theorems 13.3 and 13.4 for a proper convex $f$. The backbone results ask in addition
that $f^*$ be proper. On $\mathbb{R}^n$ this follows from Theorem 12.2 and Theorem 7.4.
-/

/-! ### The unnumbered running text of pp. 112–114 -/

/-- **Section 13** of [rockafellar1970convex], minimization of linear functions (p. 112). For
$C \subseteq \mathbb{R}^n$ and $x^* \in \mathbb{R}^n$,
$$\inf \{\langle x, x^* \rangle \mid x \in C\} = -\delta^*(-x^* \mid C).$$

**Generalization.** The formula also applies to nonconvex sets.
-/
theorem infimum_eq_neg_supportFn_neg (C : Set (Rn n)) (y : Rn n) :
    ⨅ x ∈ C, ((inner ℝ x y : ℝ) : EReal) = -supportFn (pairing n) C (-y) := by
  rw [supportFn_apply_rn, EReal.neg_iSup]
  refine iInf_congr fun x => ?_
  rw [EReal.neg_iSup]
  refine iInf_congr fun _ => ?_
  rw [inner_neg_right, EReal.coe_neg, neg_neg]

/-- **Section 13** of [rockafellar1970convex], half-spaces that contain $C$ (p. 112). For
$C \subseteq \mathbb{R}^n$, $x^* \in \mathbb{R}^n$ and $\beta \in \mathbb{R}$, one has $C
\subseteq \{x \mid \langle x, x^* \rangle \le \beta\}$ if and only if
$\delta^*(x^* \mid C) \le \beta$.

**Generalization.** The formula also applies to nonconvex sets and to inequalities with
zero normal. -/
theorem subset_halfspace_iff (C : Set (Rn n)) (y : Rn n) (β : ℝ) :
    C ⊆ {x : Rn n | inner ℝ x y ≤ β} ↔ supportFn (pairing n) C y ≤ (β : EReal) :=
  ⟨fun h => supportFn_le_coe_iff.2 fun _ hx => h hx, fun h _ hx => supportFn_le_coe_iff.1 h _ hx⟩

/-- **Section 13** of [rockafellar1970convex] (p. 112). For every $C \subseteq \mathbb{R}^n$,
$\delta^*(\cdot \mid \operatorname{cl} C) = \delta^*(\cdot \mid C)$.

**Generalization.** The book assumes convexity. Closure invariance uses only continuity of
the linear function. -/
theorem supportFn_closure_rn (C : Set (Rn n)) :
    supportFn (pairing n) (closure C) = supportFn (pairing n) C :=
  supportFn_closure C

/-- **Section 13** of [rockafellar1970convex] (p. 112). For every convex $C \subseteq \mathbb{R}^n$,
$\delta^*(\cdot \mid \operatorname{ri} C) = \delta^*(\cdot \mid C)$. -/
theorem supportFn_relint_rn {C : Set (Rn n)} (hC : Convex ℝ C) :
    supportFn (pairing n) (ri C) = supportFn (pairing n) C := by
  rw [← supportFn_closure (B := pairing n) (ri C), hC.closure_relint, supportFn_closure]

/-- **Section 13** of [rockafellar1970convex] (p. 113). For all $C_1, C_2 \subseteq \mathbb{R}^n$,
$\delta^*(\cdot \mid C_1 + C_2) = \delta^*(\cdot \mid C_1) + \delta^*(\cdot \mid C_2)$.

**Generalization.** The book assumes two nonempty convex sets. The Lean result applies to
arbitrary sets. The sum uses `EReal`, where $-\infty$ is absorbing under addition, as required
if one of the sets is empty. -/
theorem supportFn_add_rn (C₁ C₂ : Set (Rn n)) :
    supportFn (pairing n) (C₁ + C₂) = supportFn (pairing n) C₁ + supportFn (pairing n) C₂ :=
  supportFn_add (pairing n) C₁ C₂

/-- **Section 13** of [rockafellar1970convex], a closed convex set is determined by its support
function (p. 113). Let $C \subseteq \mathbb{R}^n$ be closed and convex. Then
$$C = \{x \mid \langle x, x^* \rangle \le \delta^*(x^* \mid C) \text{ for every } x^*\}.$$
-/
theorem eq_setOf_le_supportFn {C : Set (Rn n)} (hC : Convex ℝ C) (hCcl : IsClosed C) :
    C = {x : Rn n | ∀ y : Rn n, ((inner ℝ x y : ℝ) : EReal) ≤ supportFn (pairing n) C y} := by
  ext x
  have h := mem_closure_convexHull_iff_le_supportFn (B := pairing n) C x
  rw [hC.convexHull_eq, hCcl.closure_eq] at h
  exact h

/-- **Section 13** of [rockafellar1970convex], the Euclidean norm (p. 114). Let $B$ be the closed
Euclidean unit ball of $\mathbb{R}^n$. Then $\delta^*(x \mid B) = |x|$ for every $x$. -/
theorem supportFn_unitBall (x : Rn n) :
    supportFn (pairing n) (Metric.closedBall (0 : Rn n) 1) x = ((‖x‖ : ℝ) : EReal) := by
  rw [supportFn_closedBall zero_le_one, one_mul]

/-- **Section 13** of [rockafellar1970convex], support function of a ball (p. 114). Let
$a \in \mathbb{R}^n$, $\lambda \ge 0$, and let $B$ be the closed Euclidean unit ball. Then
$\delta^*(x \mid a + \lambda B) = \langle a, x \rangle + \lambda |x|$ for every $x$.

The set $a + \lambda B$ is written as $\{a\} + \bar B(0, \lambda)$. -/
theorem supportFn_ball (a : Rn n) {lam : ℝ} (hlam : 0 ≤ lam) (x : Rn n) :
    supportFn (pairing n) ({a} + Metric.closedBall (0 : Rn n) lam) x =
      ((inner ℝ a x : ℝ) : EReal) + ((lam * ‖x‖ : ℝ) : EReal) := by
  rw [supportFn_add, Pi.add_apply, supportFn_singleton, supportFn_closedBall hlam]
  rfl

/-! ### Theorem 13.1 -/

/-- **Theorem 13.1** of [rockafellar1970convex], closure. Let $C \subseteq \mathbb{R}^n$ be convex.
Then $x \in \operatorname{cl} C$ if and only if $\langle x, x^* \rangle \le \delta^*(x^* \mid
C)$ for every $x^* \in \mathbb{R}^n$.

The proof specializes `ConvexAnalysis.mem_closure_convexHull_iff_le_supportFn`, which is
Corollary 11.5.1 read through the pairing. -/
theorem theorem_13_1_cl {C : Set (Rn n)} (hC : Convex ℝ C) (x : Rn n) :
    x ∈ closure C ↔ ∀ y : Rn n, ((inner ℝ x y : ℝ) : EReal) ≤ supportFn (pairing n) C y := by
  have h := mem_closure_convexHull_iff_le_supportFn (B := pairing n) C x
  rw [hC.convexHull_eq] at h
  exact h

/-- **Theorem 13.1** of [rockafellar1970convex], relative interior. Let $C \subseteq \mathbb{R}^n$
be convex. Then $x \in \operatorname{ri} C$ if and only if $\langle x, x^* \rangle \le
\delta^*(x^* \mid C)$ for every $x^*$, with strict inequality for every $x^*$ such that
$-\delta^*(-x^* \mid C) \ne \delta^*(x^* \mid C)$.

The proof specializes `ConvexAnalysis.mem_relint_iff_lt_supportFn`, which is Corollary 11.6.2
read through the pairing. -/
theorem theorem_13_1_ri {C : Set (Rn n)} (hC : Convex ℝ C) (x : Rn n) :
    x ∈ ri C ↔ (∀ y : Rn n, ((inner ℝ x y : ℝ) : EReal) ≤ supportFn (pairing n) C y) ∧
      ∀ y : Rn n, -supportFn (pairing n) C (-y) ≠ supportFn (pairing n) C y →
        ((inner ℝ x y : ℝ) : EReal) < supportFn (pairing n) C y :=
  mem_relint_iff_lt_supportFn (B := pairing n) hC x

/-- **Theorem 13.1** of [rockafellar1970convex], interior. Let $C \subseteq \mathbb{R}^n$ be convex
and non-empty. Then $x \in \operatorname{int} C$ if and only if
$\langle x, x^* \rangle < \delta^*(x^* \mid C)$ for every $x^* \ne 0$.

**Correction.** The book omits the hypothesis $C \ne \emptyset$, and the clause is false without
it. For $n = 0$ and $C = \emptyset$ there is no $x^* \ne 0$, so the condition holds for the only
point $x = 0$, but $\operatorname{int} \emptyset = \emptyset$. -/
theorem theorem_13_1_int {C : Set (Rn n)} (hC : Convex ℝ C) (hne : C.Nonempty) (x : Rn n) :
    x ∈ interior C ↔
      ∀ y : Rn n, y ≠ 0 → ((inner ℝ x y : ℝ) : EReal) < supportFn (pairing n) C y := by
  exact mem_interior_iff_lt_supportFn (B := pairing n) hC hne (separatingRight_pairing n) x

/-- **Theorem 13.1** of [rockafellar1970convex], affine hull. Let $C \subseteq \mathbb{R}^n$ be
non-empty. Then $x \in \operatorname{aff} C$ if and only if
$\langle x, x^* \rangle = \delta^*(x^* \mid C)$ for every $x^*$ such that
$-\delta^*(-x^* \mid C) = \delta^*(x^* \mid C)$.

**Generalization.** The book states the theorem for a convex set $C$. Convexity is not needed:
the vectors $x^*$ with $-\delta^*(-x^* \mid C) = \delta^*(x^* \mid C)$ describe the hyperplanes
that contain $C$, and Corollary 1.4.1 intersects them. -/
theorem theorem_13_1_aff {C : Set (Rn n)} (hne : C.Nonempty) (x : Rn n) :
    x ∈ affineSpan ℝ C ↔ ∀ y : Rn n, -supportFn (pairing n) C (-y) = supportFn (pairing n) C y →
      ((inner ℝ x y : ℝ) : EReal) = supportFn (pairing n) C y :=
  mem_affineSpan_iff_eq_supportFn (B := pairing n) hne x

/-- **Corollary 13.1.1** of [rockafellar1970convex]. Let $C_1, C_2 \subseteq \mathbb{R}^n$ be
convex. Then $\operatorname{cl} C_1 \subseteq \operatorname{cl} C_2$ if and only if
$\delta^*(\cdot \mid C_1) \le \delta^*(\cdot \mid C_2)$ pointwise. -/
theorem corollary_13_1_1 {C₁ C₂ : Set (Rn n)} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂) :
    closure C₁ ⊆ closure C₂ ↔ supportFn (pairing n) C₁ ≤ supportFn (pairing n) C₂ := by
  have h := closure_convexHull_subset_iff_supportFn_le (B := pairing n) C₁ C₂
  rw [h₁.convexHull_eq, h₂.convexHull_eq] at h
  exact h

/-! ### Theorem 13.2 -/

/-- **Theorem 13.2** of [rockafellar1970convex], conjugate of the indicator function. For every
$C \subseteq \mathbb{R}^n$, the conjugate of the indicator function $\delta(\cdot \mid C)$ is
the support function: $\delta(\cdot \mid C)^* = \delta^*(\cdot \mid C)$.

**Generalization.** The book states the conjugacy for a closed convex set $C$. This direction
holds for every set.

The indicator function is `ConvexAnalysis.indicatorFn C`, which is $0$ on $C$ and $+\infty$ off
$C$. -/
theorem theorem_13_2_conj_indicator (C : Set (Rn n)) :
    convexConj (pairing n) (indicatorFn C) = supportFn (pairing n) C :=
  (supportFn_eq_convexConj_indicatorFn (pairing n) C).symm

/-- **Theorem 13.2** of [rockafellar1970convex], conjugate of the support function. Let
$C \subseteq \mathbb{R}^n$ be closed and convex. Then $\delta^*(\cdot \mid C)^* = \delta(\cdot
\mid C)$. Together with `Rockafellar.theorem_13_2_conj_indicator`, the indicator function and
the support function of $C$ are conjugate to each other. -/
theorem theorem_13_2_conj {C : Set (Rn n)} (hC : Convex ℝ C) (hCcl : IsClosed C) :
    convexConj (pairing n) (supportFn (pairing n) C) = indicatorFn C := by
  have h := convexConj_supportFn (B := pairing n) hC hCcl
  rwa [flip_pairing] at h

/-- **Theorem 13.2** of [rockafellar1970convex], characterization of support functions. A function
$g : \mathbb{R}^n \to [-\infty, +\infty]$ is the support function of a non-empty closed convex
set if and only if $g$ is a closed proper convex function that is positively homogeneous.

The book speaks of non-empty convex sets. The support function does not change when $C$ is
replaced by $\operatorname{cl} C$, so the class of sets can be narrowed to the non-empty closed
convex sets without changing the class of functions. This is what makes the correspondence
`Rockafellar.theorem_13_2_correspondence` one-to-one. -/
theorem theorem_13_2 (g : Rn n → EReal) :
    (∃ C : Set (Rn n), C.Nonempty ∧ Convex ℝ C ∧ IsClosed C ∧ g = supportFn (pairing n) C) ↔
      ClosedProperConvexFn g ∧ PosHomogeneous g :=
  exists_supportFn_iff

/-- **Theorem 13.2** of [rockafellar1970convex], the correspondence. The map
$C \mapsto \delta^*(\cdot \mid C)$ is a one-to-one correspondence between the non-empty closed
convex sets in $\mathbb{R}^n$ and the closed proper positively homogeneous convex functions on
$\mathbb{R}^n$. The book calls it an "important one-to-one correspondence between the closed
convex sets in $\mathbb{R}^n$ and objects of quite a different sort, certain functions on
$\mathbb{R}^n$".

The correspondence is `ConvexAnalysis.supportEquiv` for `Rockafellar.pairing n`. -/
noncomputable def theorem_13_2_correspondence (n : ℕ) :
    {C : Set (Rn n) // C.Nonempty ∧ Convex ℝ C ∧ IsClosed C} ≃
      {g : Rn n → EReal // ClosedProperConvexFn g ∧ PosHomogeneous g} :=
  supportEquiv (pairing n)

/-- **Section 13** of [rockafellar1970convex], subadditivity of support functions (p. 115). Let
$C \subseteq \mathbb{R}^n$ be non-empty. Then for all $y_1, y_2$,
$$\delta^*(y_1 + y_2 \mid C) \le \delta^*(y_1 \mid C) + \delta^*(y_2 \mid C).$$

**Generalization.** The book draws this consequence for support functions of nonempty convex
sets. The same inequality holds for nonempty sets without convexity. -/
theorem theorem_13_2_subadditive {C : Set (Rn n)} (hne : C.Nonempty) (y₁ y₂ : Rn n) :
    supportFn (pairing n) C (y₁ + y₂) ≤
      supportFn (pairing n) C y₁ + supportFn (pairing n) C y₂ :=
  supportFn_add_le hne y₁ y₂

/-- **Corollary 13.2.1** of [rockafellar1970convex]. Let $f$ be a positively homogeneous convex
function on $\mathbb{R}^n$ that is not identically $+\infty$. Then $\operatorname{cl} f$ is the
support function of the closed convex set
$$C = \{x^* \mid \langle x, x^* \rangle \le f(x) \text{ for every } x\}.$$

The improper case is included: if $f$ takes the value $-\infty$, then
$\operatorname{cl} f \equiv -\infty$, the set $C$ is empty, and both sides equal
$\delta^*(\cdot \mid \emptyset) \equiv -\infty$. -/
theorem corollary_13_2_1 {f : Rn n → EReal} (hf : PosHomogeneous f) (hconv : ConvexFn f)
    (hne : ∃ x, f x ≠ ⊤) :
    convexCl f =
      supportFn (pairing n) {y : Rn n | ∀ x : Rn n, ((inner ℝ x y : ℝ) : EReal) ≤ f x} := by
  have h := convexCl_eq_supportFn_of_posHomogeneous (B := pairing n) hf hconv hne
  rwa [flip_pairing] at h

/-- **Corollary 13.2.2** of [rockafellar1970convex]. A function
$g : \mathbb{R}^n \to [-\infty, +\infty]$ is the support function of a non-empty bounded set if
and only if $g$ is finite everywhere, convex, closed and positively homogeneous.

**Reading.** The book uses a convex representing set and does not list closedness of $g$.
The convex hull of a bounded set has the same support function and is bounded. Closedness of
$g$ follows from convexity and finiteness on $\mathbb{R}^n$ by Corollary 7.4.2. -/
theorem corollary_13_2_2 (g : Rn n → EReal) :
    (∃ C : Set (Rn n), C.Nonempty ∧ Bornology.IsBounded C ∧ g = supportFn (pairing n) C) ↔
      ((∀ y, g y ≠ ⊥) ∧ (∀ y, g y ≠ ⊤) ∧ ConvexFn g ∧ ClosedConvex g ∧ PosHomogeneous g) := by
  rw [← exists_supportFn_finite_iff (B := pairing n) (g := g)]
  exact exists_congr fun C => and_congr_right fun _ =>
    and_congr_left fun _ => isBounded_iff_forall_bddAbove

/-! ### Theorem 13.3 -/

/-- **Theorem 13.3** of [rockafellar1970convex], first assertion. Let $f$ be a proper convex
function on $\mathbb{R}^n$. Then the support function of $\operatorname{dom} f$ is the recession
function $f^* 0^+$ of $f^*$:
$$\delta^*(\cdot \mid \operatorname{dom} f) = f^* 0^+.$$

The backbone result also needs $f^*$ to be proper. Here this follows from
`ConvexAnalysis.properConvex_convexConj_of_properConvex`. -/
theorem theorem_13_3 {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f) :
    supportFn (pairing n) (convexDom f) = recessionFn (convexConj (pairing n) f) :=
  (recessionFn_convexConj hp (properConvex_convexConj_of_properConvex hf hp)).symm

/-- **Theorem 13.3** of [rockafellar1970convex], second assertion. Let $f$ be a closed proper convex
function on $\mathbb{R}^n$. Then the support function of $\operatorname{dom} f^*$ is the
recession function $f 0^+$ of $f$:
$$\delta^*(\cdot \mid \operatorname{dom} f^*) = f 0^+.$$
-/
theorem theorem_13_3_dual {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    supportFn (pairing n) (convexDom (convexConj (pairing n) f)) = recessionFn f := by
  have h := recessionFn_eq_supportFn_convexDom_convexConj (B := pairing n) hf
  rw [flip_pairing] at h
  exact h.symm

/-- **Corollary 13.3.1** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$. Then $f^*$ is finite everywhere, that is
$\operatorname{dom} f^* = \mathbb{R}^n$, if and only if $f$ is co-finite.

Co-finite is `ConvexAnalysis.Cofinite`. See `Rockafellar.cofinite_iff_rn`.

**Reading.** The book assumes closed convexity and states that $f^*$ is finite everywhere.
The Lean result also assumes properness of $f$ so the full effective domain of $f^*$
forces finiteness. For instance, $f \equiv +\infty$ has $f^* \equiv -\infty$, which has
full effective domain without being finite. -/
theorem corollary_13_3_1 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    convexDom (convexConj (pairing n) f) = univ ↔ Cofinite f :=
  (cofinite_iff_convexDom_convexConj_eq_univ hf).symm

/-!
### Corollary 13.3.2

The book leaves a key step as an exercise: a non-empty convex set is affine if and only if every
linear function that is bounded above on it is constant on it. This step is
`Rockafellar.affine_iff_forall_reversible` below.
-/

/-- The step of Corollary 13.3.2 that the book leaves as an exercise. Let $C \subseteq \mathbb{R}^n$
be non-empty and convex. Then $C$ is affine, that is $\operatorname{aff} C = C$, if and only if
every linear function that is bounded above on $C$ is constant on $C$:
$-\delta^*(-x^* \mid C) = \delta^*(x^* \mid C)$ whenever $\delta^*(x^* \mid C) < +\infty$.

**Reading.** The book gives the criterion in terms of bounded and constant linear functions.
The Lean formulation uses equality of the supremum and infimum, which requires nonemptiness.
For the empty set the supremum and infimum are opposite infinities. -/
theorem affine_iff_forall_reversible {C : Set (Rn n)} (hC : Convex ℝ C) (hne : C.Nonempty) :
    (affineSpan ℝ C : Set (Rn n)) = C ↔
      ∀ y : Rn n, supportFn (pairing n) C y ≠ ⊤ →
        -supportFn (pairing n) C (-y) = supportFn (pairing n) C y := by
  constructor
  · intro haff y hy
    refine (neg_supportFn_neg_eq_iff (B := pairing n) hne y).2 ?_
    obtain ⟨x₀, hx₀⟩ := hne
    have hmemdom : y ∈ convexDom (supportFn (pairing n) C) :=
        mem_convexDom.2 (lt_top_iff_ne_top.2 hy)
    rw [convexDom_supportFn] at hmemdom
    obtain ⟨c, hc⟩ := hmemdom
    refine ⟨inner ℝ x₀ y, fun x hx => ?_⟩
    by_contra hne'
    set d : ℝ := (inner ℝ x y : ℝ) - (inner ℝ x₀ y : ℝ) with hd
    have hd0 : d ≠ 0 := sub_ne_zero.2 hne'
    have hmem : ∀ t : ℝ, t • (x - x₀) + x₀ ∈ C := by
      intro t
      have hstep := (affineSpan ℝ C).smul_vsub_vadd_mem t (subset_affineSpan ℝ C hx)
        (subset_affineSpan ℝ C hx₀) (subset_affineSpan ℝ C hx₀)
      rw [← haff]
      exact hstep
    set t : ℝ := (|c - (inner ℝ x₀ y : ℝ)| + 1) / d with ht
    have hval : (inner ℝ (t • (x - x₀) + x₀) y : ℝ) = t * d + (inner ℝ x₀ y : ℝ) := by
      rw [inner_add_left, real_inner_smul_left, inner_sub_left, hd]
    have hle := hc _ (hmem t)
    rw [show (pairing n) (t • (x - x₀) + x₀) y = (inner ℝ (t • (x - x₀) + x₀) y : ℝ) from rfl,
      hval, ht, div_mul_cancel₀ _ hd0] at hle
    have hab : c - (inner ℝ x₀ y : ℝ) ≤ |c - (inner ℝ x₀ y : ℝ)| := le_abs_self _
    linarith
  · intro hrev
    refine subset_antisymm (fun x hx => ?_) (subset_affineSpan ℝ C)
    have hclosure : ∀ z : Rn n, z ∈ affineSpan ℝ C → z ∈ closure C := by
      intro z hz
      rw [theorem_13_1_cl hC]
      intro y
      by_cases hy : supportFn (pairing n) C y = ⊤
      · rw [hy]
        exact le_top
      · exact le_of_eq ((theorem_13_1_aff hne z).1 hz y (hrev y hy))
    obtain ⟨x₀, hx₀⟩ := hC.relint_nonempty hne
    have hxa : x₀ ∈ affineSpan ℝ C := subset_affineSpan ℝ C (intrinsicInterior_subset hx₀)
    have hz : (2 : ℝ) • (x - x₀) + x₀ ∈ affineSpan ℝ C :=
      (affineSpan ℝ C).smul_vsub_vadd_mem 2 hx hxa hxa
    have hmid : (1 - (2 : ℝ)⁻¹) • x₀ + (2 : ℝ)⁻¹ • ((2 : ℝ) • (x - x₀) + x₀) = x := by
      module
    have hseg := hC.segment_mem_relint hx₀ (hclosure _ hz) (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    rw [hmid] at hseg
    exact intrinsicInterior_subset hseg

/-- **Corollary 13.3.2** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$. Then $\operatorname{dom} f^*$ is an affine set if and only if
$(f 0^+)(y) = +\infty$ for every $y$ that is not in the lineality space of $f$.

The book leaves a step of the proof as an exercise; it is
`Rockafellar.affine_iff_forall_reversible`. The lineality space of $f$ is
`ConvexAnalysis.linealitySpaceFn f`, the set of $y$ with $(f 0^+)(-y) = -(f 0^+)(y)$. -/
theorem corollary_13_3_2 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    (affineSpan ℝ (convexDom (convexConj (pairing n) f)) : Set (Rn n))
        = convexDom (convexConj (pairing n) f) ↔
      ∀ y : Rn n, y ∉ linealitySpaceFn f → recessionFn f y = ⊤ := by
  have hconv : Convex ℝ (convexDom (convexConj (pairing n) f)) :=
      (convexFn_convexConj (pairing n) f).convex_convexDom
  have hne : (convexDom (convexConj (pairing n) f)).Nonempty :=
      (properConvex_convexConj hf).convexDom_nonempty
  rw [affine_iff_forall_reversible hconv hne, theorem_13_3_dual hf]
  constructor
  · intro h y hy
    by_contra hy'
    exact hy (mem_linealitySpaceFn.2 (neg_eq_iff_eq_neg.1 (h y hy')))
  · intro h y hy
    refine neg_eq_iff_eq_neg.2 (mem_linealitySpaceFn.1 ?_)
    by_contra hmem
    exact hy (h y hmem)

/-! ### Corollary 13.3.3 -/

/-- **Corollary 13.3.3** of [rockafellar1970convex], the least Lipschitz constant. Let $f$ be a
closed proper convex function on $\mathbb{R}^n$ and let $\alpha \ge 0$. Then
$f(z) \le f(x) + \alpha |z - x|$ for all $x, z$ if and only if $\operatorname{dom} f^*$ is
contained in the closed ball of radius $\alpha$ about the origin.

The criterion identifies the admissible constants $\alpha$ as the upper bounds on the norms
of elements of $\operatorname{dom} f^*$. When such constants exist, their least value is the
supremum stated in the book. This declaration uses the closed case of the corollary.

**Reading.** Assumes closedness. The radius equivalence determines the infimal admissible constant
by the supremum of norms.
-/
theorem corollary_13_3_3_least {f : Rn n → EReal} (hf : ClosedProperConvexFn f) {α : ℝ}
    (hα : 0 ≤ α) :
    (∀ x z : Rn n, f z ≤ f x + ((α * ‖z - x‖ : ℝ) : EReal)) ↔
      convexDom (convexConj (pairing n) f) ⊆ Metric.closedBall (0 : Rn n) α := by
  have hball : supportFn (pairing n) (Metric.closedBall (0 : Rn n) α) =
      fun y => ((α * ‖y‖ : ℝ) : EReal) := funext fun y => supportFn_closedBall hα y
  constructor
  · intro hlip
    have hle : recessionFn f ≤ fun y => ((α * ‖y‖ : ℝ) : EReal) :=
      (recessionFn_isLeast hf.convex hf.proper).2 fun x z => hlip x z
    have hsub : closure (convexDom (convexConj (pairing n) f)) ⊆
        closure (Metric.closedBall (0 : Rn n) α) := by
      refine (corollary_13_1_1 (convexFn_convexConj (pairing n) f).convex_convexDom
        (convex_closedBall 0 α)).2 ?_
      rw [theorem_13_3_dual hf, hball]
      exact hle
    intro y hy
    have hmem := hsub (subset_closure hy)
    rwa [Metric.isClosed_closedBall.closure_eq] at hmem
  · intro hsub x z
    have hle : recessionFn f ≤ fun y => ((α * ‖y‖ : ℝ) : EReal) := by
      rw [← hball, ← theorem_13_3_dual hf]
      exact (corollary_13_1_1 (convexFn_convexConj (pairing n) f).convex_convexDom
        (convex_closedBall 0 α)).1 (closure_mono hsub)
    exact ((recessionFn_isLeast hf.convex hf.proper).1 x z).trans
      (add_le_add le_rfl (hle (z - x)))

/-- **Corollary 13.3.3** of [rockafellar1970convex], first assertion. Let $f$ be a closed proper
convex function on $\mathbb{R}^n$. Then $\operatorname{dom} f^*$ is bounded if and only if there
is $\alpha \ge 0$ with
$$f(z) \le f(x) + \alpha |z - x| \quad \text{for all } x, z \in \mathbb{R}^n.$$

The book states the Lipschitz condition as $|f(z) - f(x)| \le \alpha |z - x|$ for a function $f$
that is finite everywhere. The one-sided inequality for all $x, z$ is equivalent: it makes $f$
finite (`Rockafellar.corollary_13_3_3_finite`), and exchanging $x$ and $z$ gives the two-sided
form. The inequality is in `EReal`. The book starts with a proper convex function and reduces
to the closed case. This declaration states the closed case.

**Reading.** Assumes closedness. The one-sided inequality over all ordered pairs forces finiteness
and gives the two-sided Lipschitz bound.
-/
theorem corollary_13_3_3 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    Bornology.IsBounded (convexDom (convexConj (pairing n) f)) ↔
      ∃ α : ℝ, 0 ≤ α ∧ ∀ x z : Rn n, f z ≤ f x + ((α * ‖z - x‖ : ℝ) : EReal) := by
  constructor
  · intro hb
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Rn n)).1 hb
    obtain ⟨y₀, hy₀⟩ := (properConvex_convexConj (B := pairing n) hf).convexDom_nonempty
    have hr0 : 0 ≤ r := by
      have hmem := hr hy₀
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      exact le_trans (norm_nonneg _) hmem
    exact ⟨r, hr0, (corollary_13_3_3_least hf hr0).2 hr⟩
  · rintro ⟨α, hα, hlip⟩
    exact (Metric.isBounded_iff_subset_closedBall (0 : Rn n)).2
      ⟨α, (corollary_13_3_3_least hf hα).1 hlip⟩

/-- **Corollary 13.3.3** of [rockafellar1970convex], finiteness. Let $f$ be a closed proper convex
function on $\mathbb{R}^n$, and let $\alpha \in \mathbb{R}$ satisfy
$f(z) \le f(x) + \alpha |z - x|$ for all $x, z$. Then $f$ is finite everywhere:
$f(z) \ne +\infty$ and $f(z) \ne -\infty$ for every $z$. -/
theorem corollary_13_3_3_finite {f : Rn n → EReal} (hf : ClosedProperConvexFn f) {α : ℝ}
    (hlip : ∀ x z : Rn n, f z ≤ f x + ((α * ‖z - x‖ : ℝ) : EReal)) (z : Rn n) :
    f z ≠ ⊤ ∧ f z ≠ ⊥ := by
  obtain ⟨x₀, hx₀⟩ := hf.proper.convexDom_nonempty
  refine ⟨?_, hf.proper.ne_bot z⟩
  obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x₀) hx₀
  have hstep := hlip x₀ z
  rw [hc, ← EReal.coe_add] at hstep
  exact (lt_of_le_of_lt hstep (EReal.coe_lt_top _)).ne

/-!
### Corollary 13.3.4

For a given $x^*$ the book sets $g(x) = f(x) - \langle x, x^* \rangle$, so that $(g 0^+)(y) = (f
0^+)(y) - \langle y, x^* \rangle$. The four clauses below are stated through $f 0^+$ and
$\langle y, x^* \rangle$ directly, so that the translation by $-x^*$ disappears. For this reason the
exceptional set of directions in clause (b) does not depend on $x^*$.
-/

/-- **Corollary 13.3.4(a)** of [rockafellar1970convex]. Let $f$ be a closed proper convex function
on $\mathbb{R}^n$ and let $x^* \in \mathbb{R}^n$. Then $x^* \in
\operatorname{cl}(\operatorname{dom} f^*)$ if and only if
$\langle y, x^* \rangle \le (f 0^+)(y)$ for every $y$, that is, $(g 0^+)(y) \ge 0$ for every
$y$, where $g(x) = f(x) - \langle x, x^* \rangle$.

The vector $x^*$ is `y₀`. The proof specializes
`ConvexAnalysis.mem_closure_convexDom_convexConj_iff`. -/
theorem corollary_13_3_4_a {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (y₀ : Rn n) :
    y₀ ∈ closure (convexDom (convexConj (pairing n) f)) ↔
      ∀ y : Rn n, ((inner ℝ y y₀ : ℝ) : EReal) ≤ recessionFn f y :=
  mem_closure_convexDom_convexConj_iff hf y₀

/-- **Corollary 13.3.4(b)** of [rockafellar1970convex]. Let $f$ be a closed proper convex function
on $\mathbb{R}^n$ and let $x^* \in \mathbb{R}^n$. Then $x^* \in
\operatorname{ri}(\operatorname{dom} f^*)$ if and only if
$\langle y, x^* \rangle \le (f 0^+)(y)$ for every $y$, with strict inequality for every $y$ such
that $-(f 0^+)(-y) \ne (f 0^+)(y)$.

The book states the condition as $(g 0^+)(y) > 0$ for all $y$ except those with
$-(g 0^+)(-y) = (g 0^+)(y) = 0$, where $g(x) = f(x) - \langle x, x^* \rangle$. Under the first
condition the two forms agree. The vector $x^*$ is `y₀`. The proof specializes
`ConvexAnalysis.mem_relint_convexDom_convexConj_iff`. -/
theorem corollary_13_3_4_b {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (y₀ : Rn n) :
    y₀ ∈ ri (convexDom (convexConj (pairing n) f)) ↔
      (∀ y : Rn n, ((inner ℝ y y₀ : ℝ) : EReal) ≤ recessionFn f y) ∧
      ∀ y : Rn n, -recessionFn f (-y) ≠ recessionFn f y →
        ((inner ℝ y y₀ : ℝ) : EReal) < recessionFn f y :=
  mem_relint_convexDom_convexConj_iff hf y₀

/-- **Corollary 13.3.4(c)** of [rockafellar1970convex]. Let $f$ be a closed proper convex function
on $\mathbb{R}^n$ and let $x^* \in \mathbb{R}^n$. Then $x^* \in
\operatorname{int}(\operatorname{dom} f^*)$ if and only if $\langle y, x^* \rangle < (f 0^+)(y)$
for every $y \ne 0$, that is, $(g 0^+)(y) > 0$ for every $y \ne 0$, where
$g(x) = f(x) - \langle x, x^* \rangle$.

The vector $x^*$ is `y₀`. The proof specializes
`ConvexAnalysis.mem_interior_convexDom_convexConj_iff`. -/
theorem corollary_13_3_4_c {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (y₀ : Rn n) :
    y₀ ∈ interior (convexDom (convexConj (pairing n) f)) ↔
      ∀ y : Rn n, y ≠ 0 → ((inner ℝ y y₀ : ℝ) : EReal) < recessionFn f y :=
  mem_interior_convexDom_convexConj_iff hf y₀

/-- **Corollary 13.3.4(d)** of [rockafellar1970convex]. Let $f$ be a closed proper convex function
on $\mathbb{R}^n$ and let $x^* \in \mathbb{R}^n$. Then $x^* \in
\operatorname{aff}(\operatorname{dom} f^*)$ if and only if $\langle y, x^* \rangle = (f 0^+)(y)$
for every $y$ such that $-(f 0^+)(-y) = (f 0^+)(y)$, that is, $(g 0^+)(y) = 0$ for every $y$
with $-(g 0^+)(-y) = (g 0^+)(y)$, where $g(x) = f(x) - \langle x, x^* \rangle$.

The vector $x^*$ is `y₀`. The proof specializes
`ConvexAnalysis.mem_affineSpan_convexDom_convexConj_iff`. -/
theorem corollary_13_3_4_d {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (y₀ : Rn n) :
    y₀ ∈ affineSpan ℝ (convexDom (convexConj (pairing n) f)) ↔
      ∀ y : Rn n, -recessionFn f (-y) = recessionFn f y →
        ((inner ℝ y y₀ : ℝ) : EReal) = recessionFn f y :=
  mem_affineSpan_convexDom_convexConj_iff hf y₀

/-! ### Theorem 13.4 -/

/-- **Theorem 13.4** of [rockafellar1970convex], first assertion. Let $f$ be a proper convex
function on $\mathbb{R}^n$. Then the lineality space of $f^*$ is the orthogonal complement of
the subspace parallel to $\operatorname{aff}(\operatorname{dom} f)$.

The subspace parallel to $\operatorname{aff}(\operatorname{dom} f)$ is
`vectorSpan ℝ (ConvexAnalysis.convexDom f)`, and the orthogonal complement is Mathlib's
`Submodule.orthogonal`. -/
theorem theorem_13_4 {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f) :
    linealitySpaceFn (convexConj (pairing n) f) = ((vectorSpan ℝ (convexDom f))ᗮ : Set (Rn n)) := by
  rw [linealitySpaceFn_convexConj_eq_annihilator hp (properConvex_convexConj_of_properConvex hf hp)]
  ext y
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_orthogonal]
  exact forall₂_congr fun v _ => by rw [pairing_apply, real_inner_comm]

/-- **Theorem 13.4** of [rockafellar1970convex], second assertion. Let $f$ be a closed proper convex
function on $\mathbb{R}^n$. Then the subspace parallel to
$\operatorname{aff}(\operatorname{dom} f^*)$ is the orthogonal complement of the lineality space
of $f$.

The Lean statement has the equivalent form: the lineality space of $f$ is the orthogonal
complement of the subspace parallel to $\operatorname{aff}(\operatorname{dom} f^*)$. The two
forms agree because a subspace of $\mathbb{R}^n$ is its own double orthogonal complement. -/
theorem theorem_13_4_dual {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    linealitySpaceFn f = ((vectorSpan ℝ (convexDom (convexConj (pairing n) f)))ᗮ : Set (Rn n)) := by
  rw [linealitySpaceFn_eq_annihilator_convexDom_convexConj (B := pairing n) hf]
  ext x
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_orthogonal]
  exact forall₂_congr fun v _ => by rw [pairing_apply, real_inner_comm]

/-- **Theorem 13.4** of [rockafellar1970convex], first dimension formula. Let $f$ be a proper convex
function on $\mathbb{R}^n$. Then
$$\operatorname{lineality} f^* = n - \dim f,$$
where $\dim f$ is the dimension of $\operatorname{dom} f$. Both sides are integers. -/
theorem theorem_13_4_lineality {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f) :
    (linealityFn (convexConj (pairing n) f) : ℤ) = (n : ℤ) - dim (convexDom f) := by
  have hsub : linealitySubmoduleFn (convexConj (pairing n) f) = (vectorSpan ℝ (convexDom f))ᗮ :=
    SetLike.ext' (by
      rw [coe_linealitySubmoduleFn (properConvex_convexConj_of_properConvex hf hp),
          theorem_13_4 hf hp])
  have hcount := Submodule.finrank_add_finrank_orthogonal (K := vectorSpan ℝ (convexDom f))
  rw [finrank_euclideanSpace_fin] at hcount
  rw [linealityFn, hsub, dim_of_nonempty hp.convexDom_nonempty]
  omega

/-- **Theorem 13.4** of [rockafellar1970convex], second dimension formula. Let $f$ be a closed
proper convex function on $\mathbb{R}^n$. Then
$$\dim f^* = n - \operatorname{lineality} f,$$
where $\dim f^*$ is the dimension of $\operatorname{dom} f^*$. Both sides are integers. -/
theorem theorem_13_4_dimension {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    dim (convexDom (convexConj (pairing n) f)) = (n : ℤ) - (linealityFn f : ℤ) := by
  have hsub : linealitySubmoduleFn f = (vectorSpan ℝ (convexDom (convexConj (pairing n) f)))ᗮ :=
    SetLike.ext' (by rw [coe_linealitySubmoduleFn hf.proper, theorem_13_4_dual hf])
  have hcount := Submodule.finrank_add_finrank_orthogonal
    (K := vectorSpan ℝ (convexDom (convexConj (pairing n) f)))
  rw [finrank_euclideanSpace_fin] at hcount
  rw [linealityFn, hsub,
      dim_of_nonempty (properConvex_convexConj (B := pairing n) hf).convexDom_nonempty]
  omega

/-- **Corollary 13.4.1** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$. Then $f$ and $f^*$ have the same rank: $\operatorname{rank} f^* =
\operatorname{rank} f$.

The proof combines the two dimension formulas of Theorem 13.4 with the definition of rank:
$\operatorname{rank} f^* = (n - \operatorname{lineality} f) - (n - \dim f) = \operatorname{rank}
f$. -/
theorem corollary_13_4_1 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    rankFn (convexConj (pairing n) f) = rankFn f := by
  rw [rankFn, rankFn, theorem_13_4_dimension hf, theorem_13_4_lineality hf.convex hf.proper]
  omega

/-- **Corollary 13.4.2** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$. Then $\operatorname{dom} f^*$ has a non-empty interior if and only if there is
no line along which $f$ is (finite and) affine, that is, the lineality space of $f$ is $\{0\}$. -/
theorem corollary_13_4_2 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    (interior (convexDom (convexConj (pairing n) f))).Nonempty ↔ linealitySpaceFn f = {0} :=
  interior_convexDom_convexConj_nonempty_iff hf

/-! ### Theorem 13.5 -/

/-- **Theorem 13.5** of [rockafellar1970convex], first assertion. Let $f$ be a closed convex
function on $\mathbb{R}^n$. Then the support function of $\{x \mid f(x) \le 0\}$ is
$\operatorname{cl} g$, where $g$ is the positively homogeneous convex function generated by
$f^*$.

**Generalization.** The book states the theorem for a closed proper convex function. Properness
is not needed, because the Fenchel–Moreau theorem in the form
`ConvexAnalysis.convexBiconj_eq_self` also covers the improper cases.

The positively homogeneous convex function generated by $h$ is `ConvexAnalysis.posHomGen h`, the
function whose epigraph is the convex cone generated by $\operatorname{epi} h$. -/
theorem theorem_13_5 {f : Rn n → EReal} (hf : ConvexFn f) (hc : ClosedConvex f) :
    supportFn (pairing n) {x : Rn n | f x ≤ 0} = convexCl (posHomGen (convexConj (pairing n) f)) :=
  supportFn_setOf_le_zero hf hc

/-- **Theorem 13.5** of [rockafellar1970convex], second assertion. Let
$f : \mathbb{R}^n \to [-\infty, +\infty]$ be any function, and let $k$ be the positively
homogeneous convex function generated by $f$. Then $\operatorname{cl} k$ is the support function
of $\{x^* \mid f^*(x^*) \le 0\}$.

**Generalization.** The book states the theorem for a closed proper convex function. This
assertion needs no hypothesis on $f$. -/
theorem theorem_13_5_dual (f : Rn n → EReal) :
    convexCl (posHomGen f) = supportFn (pairing n) {y : Rn n | convexConj (pairing n) f y ≤ 0} := by
  have h := convexCl_posHomGen (B := pairing n) f
  rwa [flip_pairing] at h

/-- **Corollary 13.5.1** of [rockafellar1970convex]. Let $f$ be a convex function on $\mathbb{R}^n$
with $\operatorname{dom} f \ne \emptyset$, and let $\operatorname{hom} f$ be the function on
$\mathbb{R}^{n+1} = \mathbb{R} \times \mathbb{R}^n$ with $(\operatorname{hom} f)(\lambda, x) =
(f\lambda)(x)$ for $\lambda \ge 0$ and $+\infty$ for $\lambda < 0$. Then
$\operatorname{cl}(\operatorname{hom} f)$ is the support function of
$$C = \{(\lambda^*, x^*) \mid \lambda^* \le -f^*(x^*)\}.$$

**Reading.** The book states the corollary for the function $k$ on $\mathbb{R}^{n+1}$ given by
$k(\lambda, x) = (f\lambda)(x)$ for $\lambda > 0$, $k(0, x) = (f 0^+)(x)$, and
$k(\lambda, x) = +\infty$ for $\lambda < 0$. The Lean statement uses
$\operatorname{cl}(\operatorname{hom} f)$ in place of $k$. For a closed proper convex $f$ the
identity $k = \operatorname{cl}(\operatorname{hom} f)$ is Corollary 8.5.2, a result of Section
8, and it is not repeated here.

**Generalization.** The book states the corollary for a closed proper convex function $f$. The
Lean statement only needs $f$ convex with non-empty effective domain.

The function $\operatorname{hom} f$ is `ConvexAnalysis.hom f`, and $f\lambda$ is the right
scalar multiple `ConvexAnalysis.smulRight f λ`, with $f0$ the indicator function of $\{0\}$.

The pairing of $\mathbb{R} \times \mathbb{R}^n$ with itself is $\langle (\lambda, x),
(\lambda^*, x^*) \rangle = \lambda \lambda^* + \langle x, x^* \rangle$, built with
`ConvexAnalysis.prodPairing`. The condition $\lambda^* \le -f^*(x^*)$ is written
$f^*(x^*) \le -\lambda^*$ in `EReal`. -/
theorem corollary_13_5_1 {f : Rn n → EReal} (hf : ConvexFn f) (hdom : (convexDom f).Nonempty) :
    convexCl (hom f) = supportFn (prodPairing (innerₗ ℝ) (pairing n)).flip
      {q : ℝ × Rn n | convexConj (pairing n) f q.2 ≤ ((-q.1 : ℝ) : EReal)} :=
  convexCl_hom hf hdom

end Rockafellar
