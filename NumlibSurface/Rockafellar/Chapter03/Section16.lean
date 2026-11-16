/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Exact
import Numlib.Analysis.Convex.Duality.FiniteProduct
import Numlib.Analysis.Convex.Duality.Ops
import Numlib.Analysis.Convex.Duality.Polar
import Numlib.Analysis.Convex.Duality.Relint
import Numlib.Analysis.Convex.Duality.RelintSeparation
import Numlib.Analysis.Convex.Polyhedral.Duality
import Numlib.Analysis.Convex.Recession.Closedness
import NumlibSurface.Rockafellar.Chapter03.Section13

/-!
# Rockafellar, Section 16: Dual operations

This module formalizes §16 of [rockafellar1970convex]. Each operation on convex functions of §5 has
a dual operation, and conjugation exchanges the two: left and right scalar multiplication (Theorem
16.1), image and inverse image under a linear map $A$ (Theorem 16.3), infimal convolution and
addition (Theorem 16.4), and the convex hull of a family and the pointwise supremum (Theorem 16.5).
Lemma 16.2 and its corollaries give the relative-interior qualifications in dual form, and the
corollaries of each theorem specialize it to support functions $\delta^*(\cdot \mid C)$ and polars
$C^\circ$. All 15 numbered results of §16 are formalized. The proofs specialize the backbone modules
`Numlib.Analysis.Convex.Duality.Ops`, `Numlib.Analysis.Convex.Duality.Exact` and
`Numlib.Analysis.Convex.Polyhedral.Duality`.

Each of the four theorems has three forms, and the module states them separately. The identity, such
as $(Af)^* = f^* A^*$ or $(f_1 \mathbin{\square} f_2)^* = f_1^* + f_2^*$, holds for arbitrary
functions with no hypothesis and no closure. The closure form, such as $(\operatorname{cl} f_1 +
\operatorname{cl} f_2)^* = \operatorname{cl}(f_1^* \mathbin{\square} f_2^*)$, holds for all convex
functions. The exact form drops the closure and states that the infimum in the dual operation is
attained, under a relative-interior qualification. For a polyhedral function the qualification
weakens to a domain condition; the source states this as a remark after Corollary 16.3.1 and proves
it in §19.

## Main results

* Theorem 16.1, `Rockafellar.theorem_16_1_left`, `Rockafellar.theorem_16_1_right`,
  `Rockafellar.theorem_16_1_left_zero`, `Rockafellar.theorem_16_1_right_zero`:
  $(\lambda f)^* = f^* \lambda$ and $(f \lambda)^* = \lambda f^*$ for $\lambda > 0$, and for
  $\lambda = 0$ when $f$ is proper and convex.
* Corollary 16.1.1, `Rockafellar.corollary_16_1_1`: $\delta^*(x^* \mid \lambda C) = \lambda
  \delta^*(x^* \mid C)$ for non-empty $C$ and $\lambda \ge 0$.
* Corollary 16.1.2, `Rockafellar.corollary_16_1_2`: $(\lambda C)^\circ = \lambda^{-1} C^\circ$ for
  $\lambda > 0$.
* Lemma 16.2, `Rockafellar.lemma_16_2`: a subspace $L$ meets
  $\operatorname{ri}(\operatorname{dom} f)$ if and only if no $x^* \in L^\perp$ has
  $(f^* 0^+)(x^*) \le 0 < (f^* 0^+)(-x^*)$.
* Corollary 16.2.1, `Rockafellar.corollary_16_2_1`: the dual form of the condition
  $Ax \in \operatorname{ri}(\operatorname{dom} g)$ for some $x$.
* Corollary 16.2.2, `Rockafellar.corollary_16_2_2`: the dual form of the condition $\bigcap_i
  \operatorname{ri}(\operatorname{dom} f_i) \neq \emptyset$.
* Theorem 16.3, `Rockafellar.theorem_16_3_image`, `Rockafellar.theorem_16_3_closure`,
  `Rockafellar.theorem_16_3_exact`, `Rockafellar.theorem_16_3_attained`: $(Af)^* = f^* A^*$,
  $((\operatorname{cl} g) A)^* = \operatorname{cl}(A^* g^*)$, and $(gA)^* = A^* g^*$ with attainment
  when $Ax \in \operatorname{ri}(\operatorname{dom} g)$ for some $x$.
* Corollary 16.3.1, `Rockafellar.corollary_16_3_1_image`, `Rockafellar.corollary_16_3_1_closure`,
  `Rockafellar.corollary_16_3_1_exact`: the same three forms for support functions of $AC$ and
  $A^{-1} D$.
* Remark after Corollary 16.3.1, `Rockafellar.theorem_16_3_polyhedral`,
  `Rockafellar.theorem_16_3_polyhedral_attained`: for polyhedral $g$ the qualification of Theorem
  16.3 weakens to $Ax \in \operatorname{dom} g$.
* Corollary 16.3.2, `Rockafellar.corollary_16_3_2_image`, `Rockafellar.corollary_16_3_2_preimage`:
  $(AC)^\circ = (A^*)^{-1}(C^\circ)$, and $A^*(D^\circ) \subseteq (A^{-1} D)^\circ$.
* Theorem 16.4, `Rockafellar.theorem_16_4_infConv`, `Rockafellar.theorem_16_4_infConv_finset`,
  `Rockafellar.theorem_16_4_closure`, `Rockafellar.theorem_16_4_exact`,
  `Rockafellar.theorem_16_4_attained`, `Rockafellar.theorem_16_4_exact_finset`,
  `Rockafellar.theorem_16_4_attained_finset`: $(f_1 \mathbin{\square} \cdots \mathbin{\square}
  f_m)^* = f_1^* + \cdots + f_m^*$, its closure form, and $(f_1 + \cdots + f_m)^* = f_1^*
  \mathbin{\square} \cdots \mathbin{\square} f_m^*$ with attainment under a common relative-interior
  point.
* Corollary 16.4.1, `Rockafellar.corollary_16_4_1_add`, `Rockafellar.corollary_16_4_1_add_finset`,
  `Rockafellar.corollary_16_4_1_closure`, `Rockafellar.corollary_16_4_1_exact`,
  `Rockafellar.corollary_16_4_1_exact_finset`, `Rockafellar.corollary_16_4_1_attained_finset`: the
  same forms for support functions of sums and intersections of sets.
* Corollary 16.4.2, `Rockafellar.corollary_16_4_2_add`:
  $(K_1 + K_2)^\circ = K_1^\circ \cap K_2^\circ$ for non-empty cones.
* Theorem 16.5, `Rockafellar.theorem_16_5_convFn`, `Rockafellar.theorem_16_5_closure`:
  $(\operatorname{conv}\{f_i\})^* = \sup_i f_i^*$ and $(\sup_i \operatorname{cl} f_i)^* =
  \operatorname{cl}(\operatorname{conv}\{f_i^*\})$.
* Corollary 16.5.1, `Rockafellar.corollary_16_5_1_hull`, `Rockafellar.corollary_16_5_1_closure`: the
  same two formulas for support functions of $\operatorname{conv} \bigcup_i C_i$ and
  $\bigcap_i \operatorname{cl} C_i$.
* Corollary 16.5.2, `Rockafellar.corollary_16_5_2_hull`, `Rockafellar.corollary_16_5_2_inter`:
  $(\operatorname{conv} \bigcup_i C_i)^\circ = \bigcap_i C_i^\circ$, and
  $C_i^\circ \subseteq (\bigcap_j C_j)^\circ$.

## Conventions

* The adjoint $A^*$ of a linear map $A \colon \mathbb{R}^n \to \mathbb{R}^m$ is
  `LinearMap.adjoint A`. The backbone states its results for any adjoint pair of maps, and
  `ConvexAnalysis.isAdjointPair_adjoint` supplies that hypothesis, so no statement here carries it.
* Left scalar multiplication $\lambda f$ is `fun x => (l : EReal) * f x`, and right scalar
  multiplication $f \lambda$ is `ConvexAnalysis.smulRight f l`, the function whose epigraph is
  $\lambda \cdot \operatorname{epi} f$.
* The image $Af$ is `ConvexAnalysis.mapLin A f`, the inverse image $gA$ is
  `ConvexAnalysis.compLin g A`, the infimal convolution $f \mathbin{\square} g$ is
  `ConvexAnalysis.infConv f g`, and the convex hull $\operatorname{conv}\{f_i\}$ of a family is
  `ConvexAnalysis.convFn f`.
* The recession function $f^* 0^+$ of the conjugate is `ConvexAnalysis.recessionFn` applied to
  `ConvexAnalysis.convexConj (pairing n) f`.
* The orthogonal complement $L^\perp$ of a subspace is `Lᗮ` of Mathlib, which is the annihilator of
  $L$ for the pairing.

## Implementation notes

* An $m$-ary form indexes the family by a `Finset` instead of `Fin m`. The infimal convolution $f_1
  \mathbin{\square} \cdots \mathbin{\square} f_m$ is a sum in the commutative monoid
  `ConvexAnalysis.InfConvFn`, whose zero is $\delta(\cdot \mid 0)$. The empty family is allowed
  where the statement holds for it, and the source's $m \ge 1$ is a non-emptiness hypothesis
  elsewhere.

## Deviations from the source

* **Theorem 16.1** (generalization). For $\lambda > 0$ the source assumes $f$ proper convex; the
  formulas hold for every $f$. See `Rockafellar.theorem_16_1_left`.
* **Corollary 16.1.1** (generalization). The source assumes $C$ convex; only non-emptiness is used.
  See `Rockafellar.corollary_16_1_1`.
* **Corollary 16.1.2** (generalization). The source assumes $C$ non-empty and convex; the formula
  holds for every set. See `Rockafellar.corollary_16_1_2`.
* **Theorem 16.3**, first formula (generalization). The source assumes $f$ convex; the formula holds
  for every $f$. See `Rockafellar.theorem_16_3_image`.
* **Corollary 16.3.1**, first formula (generalization). The source assumes $C$ convex; the formula
  holds for every set. See `Rockafellar.corollary_16_3_1_image`.
* **Corollary 16.3.2**, first formula (generalization). The source assumes $C$ convex; the formula
  holds for every set. See `Rockafellar.corollary_16_3_2_image`.
* **Corollary 16.4.2** (generalization). The source assumes convex cones; convexity is not used. See
  `Rockafellar.corollary_16_4_2_add`.
* **Corollary 16.5.1**, second formula (reading). The formula fails for an empty family, so the
  index set is assumed non-empty. See `Rockafellar.corollary_16_5_1_closure`.

## Not formalized

* **Corollary 16.3.1**, attainment of the infimum in the exact form.
* **Corollary 16.3.2**, second formula as an equality. Only the inclusion
  $A^*(D^\circ) \subseteq (A^{-1} D)^\circ$ is formalized.
* **Corollary 16.4.2**, the formulas after the first.
* **Corollary 16.5.2**, second formula as an equality. Only the inclusion
  $C_i^\circ \subseteq (\bigcap_j C_j)^\circ$ is formalized.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {m n : ℕ}

/-!
### The conjugate of the zero function

The proof of Theorem 16.1 at $\lambda = 0$ in the source is the single sentence "the constant
function $0$ is conjugate to the indicator function $\delta(\cdot \mid 0)$". Both halves of that
sentence are used below.
-/

/-- The conjugate of the constant function $0$ on $\mathbb{R}^n$ is the indicator function
$\delta(\cdot \mid 0)$ of the origin. This is the first half of the sentence on page 141 of
[rockafellar1970convex] that proves Theorem 16.1 at $\lambda = 0$.

The proof uses that `Rockafellar.Rn n` has a separating dual. -/
theorem convexConj_zero_rn : convexConj (pairing n)
    (0 : Rn n → EReal) = indicatorFn ({0} : Set (Rn n)) := by
  have h := convexConj_zero_eq_indicatorFn (B := pairing n) (E := Rn n) (F := Rn n)
  rwa [flip_pairing] at h

/-- The conjugate of the indicator function $\delta(\cdot \mid 0)$ of the origin of $\mathbb{R}^n$
is the constant function $0$. This is the second half of the sentence that proves Theorem 16.1
at $\lambda = 0$, and specializes `ConvexAnalysis.convexConj_indicatorFn_zero`. -/
theorem convexConj_indicatorFn_zero_rn :
    convexConj (pairing n) (indicatorFn ({0} : Set (Rn n))) = 0 :=
  convexConj_indicatorFn_zero (pairing n)

/-- For every $y \in \mathbb{R}^n$ the half-space $\{x \mid \langle x, y \rangle \le 1\}$ is convex.
Polar sets are intersections of such half-spaces, which is why the polar of a set does not
change when the set is replaced by its convex hull. -/
theorem convex_setOf_pairing_le_one (y : Rn n) : Convex ℝ {x : Rn n | pairing n x y ≤ 1} := by
  have hlin : IsLinearMap ℝ fun x : Rn n => pairing n x y :=
    ⟨fun a b => by simp, fun c a => by simp⟩
  exact convex_halfSpace_le hlin 1

/-! ### Theorem 16.1: scalar multiplication -/

/-- **Theorem 16.1** of [rockafellar1970convex], left multiplication. Let $f$ be any function on
$\mathbb{R}^n$ with values in $[-\infty, +\infty]$, and let $0 < \lambda < \infty$. Then
$$(\lambda f)^* = f^* \lambda.$$

**Generalization.** The source states the formula for a proper convex function $f$ and
$0 \le \lambda < \infty$. For $\lambda > 0$ no hypothesis on $f$ is needed. The case
$\lambda = 0$ is `Rockafellar.theorem_16_1_left_zero`.

Here $\lambda f$ is `fun x => (l : EReal) * f x`, and $f^* \lambda$ is
`ConvexAnalysis.smulRight` applied to the conjugate. -/
theorem theorem_16_1_left (f : Rn n → EReal) {l : ℝ} (hl : 0 < l) :
    convexConj (pairing n) (fun x => (l : EReal) * f x) = smulRight (convexConj (pairing n) f) l :=
  convexConj_smul hl (pairing n) f

/-- **Theorem 16.1** of [rockafellar1970convex], right multiplication. Let $f$ be any function on
$\mathbb{R}^n$ with values in $[-\infty, +\infty]$, and let $0 < \lambda < \infty$. Then
$$(f \lambda)^* = \lambda f^*.$$

**Generalization.** The source assumes $f$ proper convex. For $\lambda > 0$ no hypothesis on $f$
is needed. The case $\lambda = 0$ is `Rockafellar.theorem_16_1_right_zero`. -/
theorem theorem_16_1_right (f : Rn n → EReal) {l : ℝ} (hl : 0 < l) :
    convexConj (pairing n) (smulRight f l) = fun y => (l : EReal) * convexConj (pairing n) f y :=
  convexConj_smulRight hl (pairing n) f

/-- **Theorem 16.1** of [rockafellar1970convex], left multiplication at $\lambda = 0$. Let $f$ be a
proper convex function on $\mathbb{R}^n$. Then $(0 f)^* = f^* 0$.

With the convention $0 \cdot (\pm\infty) = 0$ of `EReal`, the function $0 f$ is the constant
function $0$. Since $f^*$ is proper, $f^* 0$ is the indicator function $\delta(\cdot \mid 0)$,
and the two are conjugate. This is the case that the proof in the source treats separately. -/
theorem theorem_16_1_left_zero {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f) :
    convexConj (pairing n) (fun x => (0 : EReal) * f x)
        = smulRight (convexConj (pairing n) f) 0 := by
  have hdom : (convexDom (convexConj (pairing n) f)).Nonempty :=
    (properConvex_convexConj_of_properConvex hf hp).convexDom_nonempty
  simp only [zero_mul]
  rw [smulRight_zero hdom]
  exact convexConj_zero_rn

/-- **Theorem 16.1** of [rockafellar1970convex], right multiplication at $\lambda = 0$. Let $f$ be a
proper function on $\mathbb{R}^n$. Then $(f 0)^* = 0 f^*$.

Here $f 0$ is the indicator function $\delta(\cdot \mid 0)$, and $0 f^*$ is the constant
function $0$, by the convention $0 \cdot (\pm\infty) = 0$ of `EReal`. Convexity of $f$ is not
assumed. -/
theorem theorem_16_1_right_zero {f : Rn n → EReal} (hp : ProperConvex f) :
    convexConj (pairing n) (smulRight f 0) = fun y => (0 : EReal) * convexConj (pairing n) f y := by
  rw [smulRight_zero hp.convexDom_nonempty, convexConj_indicatorFn_zero_rn]
  funext y
  simp

/-- **Corollary 16.1.1** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be non-empty and
let $0 \le \lambda < \infty$. Then for every $x^* \in \mathbb{R}^n$
$$\delta^*(x^* \mid \lambda C) = \lambda \, \delta^*(x^* \mid C).$$

**Generalization.** The source assumes $C$ convex. Convexity is not used.

The proof specializes `ConvexAnalysis.supportFn_smul` for $\lambda > 0$, and uses
$0 \cdot C = \{0\}$ for $\lambda = 0$. -/
theorem corollary_16_1_1 {C : Set (Rn n)} (hC : C.Nonempty) {l : ℝ} (hl : 0 ≤ l) (y : Rn n) :
    supportFn (pairing n) (l • C) y = (l : EReal) * supportFn (pairing n) C y := by
  rcases hl.lt_or_eq with hlt | heq
  · exact supportFn_smul (pairing n) hlt C y
  · rw [← heq, zero_smul_set hC, ← Set.singleton_zero, supportFn_singleton]
    simp

/-- **Corollary 16.1.2** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ and
$0 < \lambda < \infty$. Then
$$(\lambda C)^\circ = \lambda^{-1} C^\circ.$$

**Generalization.** The source assumes $C$ non-empty and convex. The formula holds for every
set.

The source derives the formula from Corollary 16.1.1 through $C^\circ = \{x^* \mid \delta^*(x^*
\mid C) \le 1\}$. Here it follows from the definition `ConvexAnalysis.polarSet` and $\langle
\lambda x, x^* \rangle = \langle x, \lambda x^* \rangle$. -/
theorem corollary_16_1_2 (C : Set (Rn n)) {l : ℝ} (hl : 0 < l) :
    polarSet (pairing n) (l • C) = l⁻¹ • polarSet (pairing n) C := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hl.ne'), inv_inv, mem_polarSet,
    mem_polarSet]
  have key : ∀ x : Rn n, pairing n (l • x) y = pairing n x (l • y) := fun x => by
    simp only [pairing_apply, real_inner_smul_left, real_inner_smul_right]
  constructor
  · intro h x hx
    have hx' := h (l • x) (Set.smul_mem_smul_set hx)
    rwa [key] at hx'
  · rintro h _ ⟨x, hx, rfl⟩
    change pairing n (l • x) y ≤ 1
    rw [key]
    exact h x hx

/-! ### Lemma 16.2: the constraint qualifications of §9 in dual form -/

/-- **Lemma 16.2** of [rockafellar1970convex]. Let $L$ be a subspace of $\mathbb{R}^n$ and let $f$
be a proper convex function on $\mathbb{R}^n$. Then $L$ meets
$\operatorname{ri}(\operatorname{dom} f)$ if and only if there is no vector $x^* \in L^\perp$
with
$$(f^* 0^+)(x^*) \le 0 \quad \text{and} \quad (f^* 0^+)(-x^*) > 0.$$

Here $f^* 0^+$ is the recession function `ConvexAnalysis.recessionFn` of the conjugate, and
$L^\perp$ is the orthogonal complement `Lᗮ`, which is the annihilator of $L$ for the pairing. -/
theorem lemma_16_2 (L : Submodule ℝ (Rn n)) {f : Rn n → EReal} (hf : ConvexFn f)
    (hp : ProperConvex f) :
    ((L : Set (Rn n)) ∩ ri (convexDom f)).Nonempty ↔
      ¬ ∃ x' ∈ Lᗮ, recessionFn (convexConj (pairing n) f) x' ≤ 0 ∧
        0 < recessionFn (convexConj (pairing n) f) (-x') :=
  submodule_inter_relint_convexDom_nonempty_iff (B := pairing n) L hf
      hp (properConvex_convexConj_of_properConvex hf hp)

/-- **Corollary 16.2.1** of [rockafellar1970convex]. Let $A$ be a linear transformation from
$\mathbb{R}^n$ to $\mathbb{R}^m$ and let $g$ be a proper convex function on $\mathbb{R}^m$.
There is no vector $y^* \in \mathbb{R}^m$ with
$$A^* y^* = 0, \quad (g^* 0^+)(y^*) \le 0, \quad (g^* 0^+)(-y^*) > 0$$
if and only if $Ax \in \operatorname{ri}(\operatorname{dom} g)$ for at least one
$x \in \mathbb{R}^n$.

This is Lemma 16.2 for the subspace $L = \operatorname{range} A$, whose orthogonal complement is
$\ker A^*$. -/
theorem corollary_16_2_1 (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : ConvexFn g)
    (hp : ProperConvex g) :
    (¬ ∃ y' : Rn m, LinearMap.adjoint A y' = 0 ∧
        recessionFn (convexConj (pairing m) g) y' ≤ 0 ∧
        0 < recessionFn (convexConj (pairing m) g) (-y')) ↔ ∃ x, A x ∈ ri (convexDom g) :=
  (exists_apply_mem_relint_convexDom_iff (separatingRight_pairing n) (isAdjointPair_adjoint A) hg hp
    (properConvex_convexConj_of_properConvex hg hp)).symm

/-- **Corollary 16.2.2** of [rockafellar1970convex]. Let $f_1, \dots, f_m$ be proper convex
functions on $\mathbb{R}^n$. There are no vectors $x_1^*, \dots, x_m^*$ with
$$x_1^* + \cdots + x_m^* = 0, \quad \sum_{i=1}^m (f_i^* 0^+)(x_i^*) \le 0, \quad \sum_{i=1}^m
  (f_i^* 0^+)(-x_i^*) > 0$$
if and only if $\operatorname{ri}(\operatorname{dom} f_1) \cap \cdots \cap
\operatorname{ri}(\operatorname{dom} f_m) \neq \emptyset$.

The functions are indexed by a finite type `ι`, which can be empty. The proof applies Lemma 16.2
in $(\mathbb{R}^n)^m$ to the diagonal subspace $L = \{x \mid x_1 = \cdots = x_m\}$, whose
orthogonal complement is $\{x^* \mid x_1^* + \cdots + x_m^* = 0\}$. -/
theorem corollary_16_2_2 {ι : Type*} [Fintype ι] (f : ι → Rn n → EReal)
    (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, ProperConvex (f i)) :
    (¬ ∃ x' : ι → Rn n, (∑ i, x' i = 0) ∧
        (∑ i, recessionFn (convexConj (pairing n) (f i)) (x' i)) ≤ 0 ∧
        0 < ∑ i, recessionFn (convexConj (pairing n) (f i)) (-(x' i)))
      ↔ (⋂ i, ri (convexDom (f i))).Nonempty :=
  (iInter_relint_convexDom_nonempty_iff (separatingRight_pairing n) f hf hp
    fun i => properConvex_convexConj_of_properConvex (hf i) (hp i)).symm

/-! ### Theorem 16.3: linear transformations -/

/-- **Theorem 16.3** of [rockafellar1970convex], first formula. Let $A$ be a linear transformation
from $\mathbb{R}^n$ to $\mathbb{R}^m$ and let $f$ be any function on $\mathbb{R}^n$ with values
in $[-\infty, +\infty]$. Then
$$(Af)^* = f^* A^*.$$

**Generalization.** The source assumes $f$ convex. The formula holds with no hypothesis on $f$:
no convexity, no properness and no closure.

The proof specializes `ConvexAnalysis.convexConj_mapLin`, whose only hypothesis is the adjoint
pair, which `ConvexAnalysis.isAdjointPair_adjoint` supplies. -/
theorem theorem_16_3_image (A : Rn n →ₗ[ℝ] Rn m) (f : Rn n → EReal) :
    convexConj (pairing m) (mapLin A f)
        = compLin (convexConj (pairing n) f) (LinearMap.adjoint A) :=
  convexConj_mapLin (isAdjointPair_adjoint A) f

/-- **Theorem 16.3** of [rockafellar1970convex], second formula. Let $A$ be a linear transformation
from $\mathbb{R}^n$ to $\mathbb{R}^m$ and let $g$ be a convex function on $\mathbb{R}^m$. Then
$$((\operatorname{cl} g) A)^* = \operatorname{cl}(A^* g^*).$$

The proof applies `ConvexAnalysis.convexConj_compLin_eq_convexCl_mapLin` to the closed convex
function $\operatorname{cl} g$ and uses $(\operatorname{cl} g)^* = g^*$. -/
theorem theorem_16_3_closure (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : ConvexFn g) :
    convexConj (pairing n) (compLin (convexCl g) A)
      = convexCl (mapLin (LinearMap.adjoint A) (convexConj (pairing m) g)) := by
  rw [convexConj_compLin_eq_convexCl_mapLin (isAdjointPair_adjoint A) (convexFn_convexCl hg)
    (closedConvex_convexCl g), convexConj_convexCl]

/-- **Theorem 16.3** of [rockafellar1970convex], exact form. Let $A$ be a linear transformation from
$\mathbb{R}^n$ to $\mathbb{R}^m$ and let $g$ be a proper convex function on $\mathbb{R}^m$. If
$Ax \in \operatorname{ri}(\operatorname{dom} g)$ for some $x \in \mathbb{R}^n$, then the closure
in the second formula can be omitted:
$$(gA)^* = A^* g^*.$$

As in the source, $g$ need not be closed. -/
theorem theorem_16_3_exact (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : ConvexFn g)
    (hp : ProperConvex g) {x₀ : Rn n} (hx₀ : A x₀ ∈ ri (convexDom g)) :
    convexConj (pairing n) (compLin g A)
        = mapLin (LinearMap.adjoint A) (convexConj (pairing m) g) :=
  (IsExactImage.of_relint (isAdjointPair_adjoint A) hg hp hx₀).convexConj_compLin

/-- **Theorem 16.3** of [rockafellar1970convex], attainment. Let $A$ be a linear transformation from
$\mathbb{R}^n$ to $\mathbb{R}^m$, let $g$ be a proper convex function on $\mathbb{R}^m$, and let
$Ax \in \operatorname{ri}(\operatorname{dom} g)$ for some $x \in \mathbb{R}^n$. If
$(gA)^*(x^*) < +\infty$, then there is $y^* \in \mathbb{R}^m$ with $A^* y^* = x^*$ and
$g^*(y^*) = (gA)^*(x^*)$, so the infimum
$$(A^* g^*)(x^*) = \inf \{ g^*(y^*) \mid A^* y^* = x^* \}$$
is attained.

The source says that the infimum is attained or is $+\infty$ vacuously. The hypothesis
$(gA)^*(x^*) < +\infty$ excludes the second case. -/
theorem theorem_16_3_attained (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : ConvexFn g)
    (hp : ProperConvex g) {x₀ : Rn n} (hx₀ : A x₀ ∈ ri (convexDom g)) {y : Rn n}
    (hy : convexConj (pairing n) (compLin g A) y < ⊤) :
    ∃ z : Rn m, LinearMap.adjoint A z = y ∧
      convexConj (pairing m) g z = convexConj (pairing n) (compLin g A) y :=
  (IsExactImage.of_relint (isAdjointPair_adjoint A) hg hp hx₀).exists_convexConj_compLin_eq hy

/-- **Section 16** of [rockafellar1970convex], the remark after Corollary 16.3.1, exact form. Let
$A$ be a linear transformation from $\mathbb{R}^n$ to $\mathbb{R}^m$ and let $g$ be a proper
polyhedral convex function on $\mathbb{R}^m$. If $Ax \in \operatorname{dom} g$ for some
$x \in \mathbb{R}^n$, then
$$(gA)^* = A^* g^*.$$
So for polyhedral $g$ the qualification $Ax \in \operatorname{ri}(\operatorname{dom} g)$ of
Theorem 16.3 weakens to $Ax \in \operatorname{dom} g$.

The source proves the remark in Corollary 19.3.1: $g^*$ is polyhedral by Theorem 19.2, so
$A^* g^*$ is polyhedral and hence closed, and the closure in the second formula of Theorem 16.3
changes nothing. -/
theorem theorem_16_3_polyhedral (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal} (hg : PolyhedralFn g)
    (hp : ProperConvex g) {x₀ : Rn n} (hx₀ : A x₀ ∈ convexDom g) :
    convexConj (pairing n) (compLin g A)
        = mapLin (LinearMap.adjoint A) (convexConj (pairing m) g) :=
  (IsExactImage.of_polyhedral (isAdjointPair_adjoint A) hg hp hx₀).convexConj_compLin

/-- **Section 16** of [rockafellar1970convex], the remark after Corollary 16.3.1, attainment. Let
$A$ be a linear transformation from $\mathbb{R}^n$ to $\mathbb{R}^m$, let $g$ be a proper
polyhedral convex function on $\mathbb{R}^m$, and let $Ax \in \operatorname{dom} g$ for some
$x \in \mathbb{R}^n$. If $(gA)^*(x^*) < +\infty$, then there is $y^* \in \mathbb{R}^m$ with
$A^* y^* = x^*$ and $g^*(y^*) = (gA)^*(x^*)$, so the infimum
$\inf \{ g^*(y^*) \mid A^* y^* = x^* \}$ is attained. -/
theorem theorem_16_3_polyhedral_attained (A : Rn n →ₗ[ℝ] Rn m) {g : Rn m → EReal}
    (hg : PolyhedralFn g) (hp : ProperConvex g) {x₀ : Rn n} (hx₀ : A x₀ ∈ convexDom g) {y : Rn n}
    (hy : convexConj (pairing n) (compLin g A) y < ⊤) :
    ∃ z : Rn m, LinearMap.adjoint A z = y ∧
      convexConj (pairing m) g z = convexConj (pairing n) (compLin g A) y :=
  (IsExactImage.of_polyhedral (isAdjointPair_adjoint A) hg hp hx₀).exists_convexConj_compLin_eq hy

/-- **Corollary 16.3.1** of [rockafellar1970convex], first formula. Let $A$ be a linear
transformation from $\mathbb{R}^n$ to $\mathbb{R}^m$ and let $C \subseteq \mathbb{R}^n$. Then
for every $y^* \in \mathbb{R}^m$
$$\delta^*(y^* \mid AC) = \delta^*(A^* y^* \mid C).$$

**Generalization.** The source assumes $C$ convex. Convexity is not used.

This is the case of indicator functions of `Rockafellar.theorem_16_3_image`, through
`ConvexAnalysis.mapLin_indicatorFn`. -/
theorem corollary_16_3_1_image (A : Rn n →ₗ[ℝ] Rn m) (C : Set (Rn n)) (y : Rn m) :
    supportFn (pairing m) (A '' C) y = supportFn (pairing n) C (LinearMap.adjoint A y) := by
  have h : supportFn (pairing m) (A '' C)
      = compLin (supportFn (pairing n) C) (LinearMap.adjoint A) := by
    rw [supportFn_eq_convexConj_indicatorFn, supportFn_eq_convexConj_indicatorFn,
        ← mapLin_indicatorFn,
      theorem_16_3_image]
  rw [h, compLin_apply]

/-- **Corollary 16.3.1** of [rockafellar1970convex], second formula. Let $A$ be a linear
transformation from $\mathbb{R}^n$ to $\mathbb{R}^m$ and let $D \subseteq \mathbb{R}^m$ be
convex. Then
$$\delta^*(\cdot \mid A^{-1}(\operatorname{cl} D)) = \operatorname{cl}(A^* \delta^*(\cdot \mid
  D)).$$

This is the case of indicator functions of `Rockafellar.theorem_16_3_closure`, through
`ConvexAnalysis.convexCl_indicatorFn` and `ConvexAnalysis.compLin_indicatorFn`. -/
theorem corollary_16_3_1_closure (A : Rn n →ₗ[ℝ] Rn m) {D : Set (Rn m)} (hD : Convex ℝ D) :
    supportFn (pairing n) (A ⁻¹' closure D)
      = convexCl (mapLin (LinearMap.adjoint A) (supportFn (pairing m) D)) := by
  rw [supportFn_eq_convexConj_indicatorFn, supportFn_eq_convexConj_indicatorFn,
      ← compLin_indicatorFn,
    ← convexCl_indicatorFn]
  exact theorem_16_3_closure A (convexFn_indicatorFn.2 hD)

/-- **Corollary 16.3.1** of [rockafellar1970convex], exact form. Let $A$ be a linear transformation
from $\mathbb{R}^n$ to $\mathbb{R}^m$ and let $D \subseteq \mathbb{R}^m$ be non-empty and
convex. If $Ax \in \operatorname{ri} D$ for some $x \in \mathbb{R}^n$, then the closure can be
omitted: for every $x^* \in \mathbb{R}^n$
$$\delta^*(x^* \mid A^{-1} D) = \inf \{ \delta^*(y^* \mid D) \mid A^* y^* = x^* \}.$$

The source also states that the infimum is attained. This declaration does not state the
attainment. -/
theorem corollary_16_3_1_exact (A : Rn n →ₗ[ℝ] Rn m) {D : Set (Rn m)} (hD : Convex ℝ D)
    (hne : D.Nonempty) {x₀ : Rn n} (hx₀ : A x₀ ∈ ri D) :
    supportFn (pairing n) (A ⁻¹' D)
      = mapLin (LinearMap.adjoint A) (supportFn (pairing m) D) := by
  rw [supportFn_eq_convexConj_indicatorFn, supportFn_eq_convexConj_indicatorFn,
      ← compLin_indicatorFn]
  refine theorem_16_3_exact A (convexFn_indicatorFn.2 hD)
    ⟨by rw [convexDom_indicatorFn]; exact hne, indicatorFn_ne_bot D⟩ (x₀ := x₀) ?_
  rw [convexDom_indicatorFn]
  exact hx₀

/-- **Corollary 16.3.2** of [rockafellar1970convex], first formula. Let $A$ be a linear
transformation from $\mathbb{R}^n$ to $\mathbb{R}^m$ and let $C \subseteq \mathbb{R}^n$. Then
$$(AC)^\circ = (A^*)^{-1}(C^\circ).$$

**Generalization.** The source assumes $C$ convex. The formula holds for every set.

The proof unfolds `ConvexAnalysis.polarSet` and uses $\langle Ax, y^* \rangle = \langle x, A^*
y^* \rangle$. -/
theorem corollary_16_3_2_image (A : Rn n →ₗ[ℝ] Rn m) (C : Set (Rn n)) :
    polarSet (pairing m) (A '' C) = LinearMap.adjoint A ⁻¹' polarSet (pairing n) C := by
  ext y
  simp only [mem_polarSet, Set.mem_preimage, Set.forall_mem_image]
  exact forall₂_congr fun x _ => by rw [isAdjointPair_adjoint A x y]

/-- **Corollary 16.3.2** of [rockafellar1970convex], second formula, one inclusion. Let $A$ be a
linear transformation from $\mathbb{R}^n$ to $\mathbb{R}^m$ and let $D \subseteq \mathbb{R}^m$.
Then
$$A^*(D^\circ) \subseteq (A^{-1} D)^\circ.$$

The source states an equality, after a closure, and without the closure under the qualification
of Corollary 16.3.1. The equality is not formalized. -/
theorem corollary_16_3_2_preimage (A : Rn n →ₗ[ℝ] Rn m) (D : Set (Rn m)) :
    LinearMap.adjoint A '' polarSet (pairing m) D ⊆ polarSet (pairing n) (A ⁻¹' D) := by
  rintro _ ⟨y, hy, rfl⟩ x hx
  rw [← isAdjointPair_adjoint A x y]
  exact hy (A x) hx

/-! ### Theorem 16.4: addition and infimal convolution -/

/-- **Theorem 16.4** of [rockafellar1970convex], first formula for $m$ functions. Let
$f_1, \dots, f_m$ be any functions on $\mathbb{R}^n$ with values in $[-\infty, +\infty]$. Then
$$(f_1 \mathbin{\square} \cdots \mathbin{\square} f_m)^* = f_1^* + \cdots + f_m^*.$$

The functions are indexed by a `Finset`. The infimal convolution of the family is the sum in the
commutative monoid `ConvexAnalysis.InfConvFn`, whose zero is $\delta(\cdot \mid 0)$, so the
empty family is allowed. Properness is not assumed, and must not be assumed at intermediate
stages, since infimal convolution does not preserve it. -/
theorem theorem_16_4_infConv_finset {ι : Type*} (s : Finset ι) (f : ι → Rn n → EReal) :
    convexConj (pairing n) (ofInfConvFn (∑ i ∈ s, toInfConvFn (f i)))
      = ∑ i ∈ s, convexConj (pairing n) (f i) :=
  convexConj_sum_toInfConvFn (pairing n) s f

/-- **Theorem 16.4** of [rockafellar1970convex], first formula for two functions. Let $f$ and $g$ be
any functions on $\mathbb{R}^n$ with values in $[-\infty, +\infty]$. Then
$$(f \mathbin{\square} g)^* = f^* + g^*.$$
-/
theorem theorem_16_4_infConv (f g : Rn n → EReal) :
    convexConj (pairing n) (infConv f g) = convexConj (pairing n) f + convexConj (pairing n) g :=
  convexConj_infConv (pairing n) f g

/-- **Theorem 16.4** of [rockafellar1970convex], second formula. Let $f$ and $g$ be convex functions
on $\mathbb{R}^n$. Then
$$(\operatorname{cl} f + \operatorname{cl} g)^* = \operatorname{cl}(f^* \mathbin{\square}
  g^*).$$

The proof applies `ConvexAnalysis.convexConj_add_eq_convexCl_infConv` to the closures. -/
theorem theorem_16_4_closure {f g : Rn n → EReal} (hf : ConvexFn f) (hg : ConvexFn g) :
    convexConj (pairing n) (convexCl f + convexCl g)
      = convexCl (infConv (convexConj (pairing n) f) (convexConj (pairing n) g)) := by
  rw [convexConj_add_eq_convexCl_infConv (convexFn_convexCl hf) (closedConvex_convexCl f)
      (convexFn_convexCl hg)
    (closedConvex_convexCl g), convexConj_convexCl, convexConj_convexCl]

/-- **Theorem 16.4** of [rockafellar1970convex], exact form for two functions. Let $f$ and $g$ be
proper convex functions on $\mathbb{R}^n$. If $\operatorname{ri}(\operatorname{dom} f)$ and
$\operatorname{ri}(\operatorname{dom} g)$ have a point in common, then the closure in the second
formula can be omitted:
$$(f + g)^* = f^* \mathbin{\square} g^*.$$

As in the source, $f$ and $g$ need not be closed. -/
theorem theorem_16_4_exact {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : ProperConvex f)
    (hg : ConvexFn g) (hpg : ProperConvex g) {x₀ : Rn n} (hxf : x₀ ∈ ri (convexDom f))
    (hxg : x₀ ∈ ri (convexDom g)) :
    convexConj (pairing n) (f + g)
        = infConv (convexConj (pairing n) f) (convexConj (pairing n) g) :=
  (IsExactSum.of_relint hf hpf hg hpg hxf hxg).convexConj_add

/-- **Theorem 16.4** of [rockafellar1970convex], attainment for two functions. Let $f$ and $g$ be
proper convex functions on $\mathbb{R}^n$ such that $\operatorname{ri}(\operatorname{dom} f)$
and $\operatorname{ri}(\operatorname{dom} g)$ have a point in common. Then for every
$x^* \in \mathbb{R}^n$ there are $x_1^*, x_2^*$ with $x_1^* + x_2^* = x^*$ and
$$f^*(x_1^*) + g^*(x_2^*) = (f + g)^*(x^*),$$
so the infimum $\inf \{ f^*(x_1^*) + g^*(x_2^*) \mid x_1^* + x_2^* = x^* \}$ is attained. -/
theorem theorem_16_4_attained {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : ProperConvex f)
    (hg : ConvexFn g) (hpg : ProperConvex g) {x₀ : Rn n} (hxf : x₀ ∈ ri (convexDom f))
    (hxg : x₀ ∈ ri (convexDom g)) (y : Rn n) :
    ∃ y₁ y₂ : Rn n, y₁ + y₂ = y ∧
      convexConj (pairing n) f y₁ + convexConj (pairing n) g y₂
          = convexConj (pairing n) (f + g) y :=
  (IsExactSum.of_relint hf hpf hg hpg hxf hxg).exists_convexConj_add_eq y

/-- **Corollary 16.4.1** of [rockafellar1970convex], first formula for two sets. Let
$C_1, C_2 \subseteq \mathbb{R}^n$. Then
$$\delta^*(\cdot \mid C_1 + C_2) = \delta^*(\cdot \mid C_1) + \delta^*(\cdot \mid C_2).$$

Unlike the statement for functions, this needs no hypothesis: two suprema over sets never
produce the expression $\infty - \infty$. -/
theorem corollary_16_4_1_add (C D : Set (Rn n)) :
    supportFn (pairing n) (C + D) = supportFn (pairing n) C + supportFn (pairing n) D :=
  supportFn_add_rn C D

/-- **Corollary 16.4.1** of [rockafellar1970convex], first formula for $m$ sets. Let
$C_1, \dots, C_m \subseteq \mathbb{R}^n$. Then
$$\delta^*(\cdot \mid C_1 + \cdots + C_m) = \delta^*(\cdot \mid C_1) + \cdots + \delta^*(\cdot
  \mid C_m).$$

The sets are indexed by a `Finset`, and the empty family is allowed. -/
theorem corollary_16_4_1_add_finset {ι : Type*} (s : Finset ι) (C : ι → Set (Rn n)) :
    supportFn (pairing n) (∑ i ∈ s, C i) = ∑ i ∈ s, supportFn (pairing n) (C i) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, ← Set.singleton_zero, supportFn_singleton]
    funext y
    simp
  | cons i t hi ih => rw [Finset.sum_cons, Finset.sum_cons, corollary_16_4_1_add, ih]

/-- **Corollary 16.4.1** of [rockafellar1970convex], second formula. Let
$C_1, C_2 \subseteq \mathbb{R}^n$ be convex. Then
$$\delta^*(\cdot \mid \operatorname{cl} C_1 \cap \operatorname{cl} C_2) =
  \operatorname{cl}(\delta^*(\cdot \mid C_1) \mathbin{\square} \delta^*(\cdot \mid C_2)).$$

This is the case of indicator functions of `Rockafellar.theorem_16_4_closure`: the sum of two
indicator functions is the indicator function of the intersection. -/
theorem corollary_16_4_1_closure {C D : Set (Rn n)} (hC : Convex ℝ C) (hD : Convex ℝ D) :
    supportFn (pairing n) (closure C ∩ closure D)
      = convexCl (infConv (supportFn (pairing n) C) (supportFn (pairing n) D)) := by
  rw [supportFn_eq_convexConj_indicatorFn, supportFn_eq_convexConj_indicatorFn,
    supportFn_eq_convexConj_indicatorFn, ← indicatorFn_add, ← convexCl_indicatorFn,
        ← convexCl_indicatorFn]
  exact theorem_16_4_closure (convexFn_indicatorFn.2 hC) (convexFn_indicatorFn.2 hD)

/-- **Corollary 16.4.1** of [rockafellar1970convex], exact form for two sets. Let
$C_1, C_2 \subseteq \mathbb{R}^n$ be non-empty and convex. If $\operatorname{ri} C_1$ and
$\operatorname{ri} C_2$ have a point in common, then for every $x^* \in \mathbb{R}^n$
$$\delta^*(x^* \mid C_1 \cap C_2) = \inf \{ \delta^*(x_1^* \mid C_1) + \delta^*(x_2^* \mid C_2)
  \mid x_1^* + x_2^* = x^* \}.$$

This declaration does not state that the infimum is attained. The attainment, for any number of
sets, is `Rockafellar.corollary_16_4_1_attained_finset`. -/
theorem corollary_16_4_1_exact {C D : Set (Rn n)} (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) {x₀ : Rn n} (hxC : x₀ ∈ ri C) (hxD : x₀ ∈ ri D) :
    supportFn (pairing n) (C ∩ D)
      = infConv (supportFn (pairing n) C) (supportFn (pairing n) D) := by
  rw [supportFn_eq_convexConj_indicatorFn, supportFn_eq_convexConj_indicatorFn,
    supportFn_eq_convexConj_indicatorFn, ← indicatorFn_add]
  refine theorem_16_4_exact (convexFn_indicatorFn.2 hC)
    ⟨by rw [convexDom_indicatorFn]; exact hCne, indicatorFn_ne_bot C⟩ (convexFn_indicatorFn.2 hD)
    ⟨by rw [convexDom_indicatorFn]; exact hDne, indicatorFn_ne_bot D⟩ (x₀ := x₀) ?_ ?_
  · rw [convexDom_indicatorFn]; exact hxC
  · rw [convexDom_indicatorFn]; exact hxD

/-- **Corollary 16.4.2** of [rockafellar1970convex], first formula. Let
$K_1, K_2 \subseteq \mathbb{R}^n$ be non-empty cones, that is, $\lambda K_i = K_i$ for every
$\lambda > 0$. Then
$$(K_1 + K_2)^\circ = K_1^\circ \cap K_2^\circ,$$
where $K^\circ = \{x^* \mid \langle x, x^* \rangle \le 0 \text{ for all } x \in K\}$ is the
polar cone.

**Generalization.** The source assumes convex cones. Only the cone property is used.

The support function of a cone is the indicator function of its polar, the sum of two indicator
functions is the indicator function of the intersection, and an indicator function determines
its set. -/
theorem corollary_16_4_2_add {K L : Set (Rn n)} (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hK : ∀ a : ℝ, 0 < a → a • K = K) (hL : ∀ a : ℝ, 0 < a → a • L = L) :
    polarCone (pairing n) (K + L)
      = polarCone (pairing n) K ∩ polarCone (pairing n) L := by
  have hdist : ∀ (a : ℝ) (s t : Set (Rn n)), a • (s + t) = a • s + a • t := by
    intro a s t
    ext z
    simp only [Set.mem_smul_set, Set.mem_add]
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨a • x, ⟨x, hx, rfl⟩, a • y, ⟨y, hy, rfl⟩, (smul_add a x y).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x + y, ⟨x, hx, y, hy, rfl⟩, smul_add a x y⟩
  have hKL : ∀ a : ℝ, 0 < a → a • (K + L) = K + L := fun a ha => by
    rw [hdist, hK a ha, hL a ha]
  have h := corollary_16_4_1_add K L
  rw [supportFn_eq_indicatorFn_polarCone (isCone_iff_smul_eq.2 hKL) (hKne.add hLne),
    supportFn_eq_indicatorFn_polarCone (isCone_iff_smul_eq.2 hK) hKne,
    supportFn_eq_indicatorFn_polarCone (isCone_iff_smul_eq.2 hL) hLne, indicatorFn_add] at h
  ext y
  have hy := congrFun h y
  constructor
  · intro h₁
    by_contra h₂
    rw [indicatorFn_of_mem h₁, indicatorFn_of_notMem h₂] at hy
    exact absurd hy (by simp)
  · intro h₂
    by_contra h₁
    rw [indicatorFn_of_notMem h₁, indicatorFn_of_mem h₂] at hy
    exact absurd hy (by simp)

/-- **Theorem 16.4** of [rockafellar1970convex], exact form for $m$ functions. Let $f_1, \dots, f_m$
be proper convex functions on $\mathbb{R}^n$ with $m \ge 1$. If the sets
$\operatorname{ri}(\operatorname{dom} f_i)$, $i = 1, \dots, m$, have a point in common, then the
closure can be omitted:
$$(f_1 + \cdots + f_m)^* = f_1^* \mathbin{\square} \cdots \mathbin{\square} f_m^*.$$

The functions are indexed by a non-empty `Finset`, and the condition $m \ge 1$ is the hypothesis
`hs`. -/
theorem theorem_16_4_exact_finset {ι : Type*} {s : Finset ι} {f : ι → Rn n → EReal}
    (hs : s.Nonempty) (hf : ∀ i ∈ s, ConvexFn (f i)) (hpf : ∀ i ∈ s, ProperConvex (f i))
    {x₀ : Rn n} (hx₀ : ∀ i ∈ s, x₀ ∈ ri (convexDom (f i))) :
    convexConj (pairing n) (∑ i ∈ s, f i)
      = ofInfConvFn (∑ i ∈ s, toInfConvFn (convexConj (pairing n) (f i))) :=
  (IsExactFinsetSum.of_relint (B := pairing n) hs hf hpf hx₀).convexConj_finsetSum

/-- **Theorem 16.4** of [rockafellar1970convex], attainment for $m$ functions. Let $f_1, \dots, f_m$
be proper convex functions on $\mathbb{R}^n$ with $m \ge 1$, such that the sets
$\operatorname{ri}(\operatorname{dom} f_i)$ have a point in common. Then for every
$x^* \in \mathbb{R}^n$ there are $x_1^*, \dots, x_m^*$ with $x_1^* + \cdots + x_m^* = x^*$ and
$$f_1^*(x_1^*) + \cdots + f_m^*(x_m^*) = (f_1 + \cdots + f_m)^*(x^*).$$
-/
theorem theorem_16_4_attained_finset {ι : Type*} {s : Finset ι} {f : ι → Rn n → EReal}
    (hs : s.Nonempty) (hf : ∀ i ∈ s, ConvexFn (f i)) (hpf : ∀ i ∈ s, ProperConvex (f i))
    {x₀ : Rn n} (hx₀ : ∀ i ∈ s, x₀ ∈ ri (convexDom (f i))) (y : Rn n) :
    ∃ y' : ι → Rn n, ∑ i ∈ s, y' i = y ∧
      ∑ i ∈ s, convexConj (pairing n) (f i) (y' i) = convexConj (pairing n) (∑ i ∈ s, f i) y :=
  (IsExactFinsetSum.of_relint (B := pairing n) hs hf hpf hx₀).exists_convexConj_finsetSum_eq y

/-- The sum of the indicator functions of a finite family of sets is the indicator function of their
intersection; for the empty family both sides are the zero function. -/
private theorem sum_indicatorFn_finset {ι : Type*} (s : Finset ι) (C : ι → Set (Rn n)) :
    ∑ i ∈ s, indicatorFn (C i) = indicatorFn (⋂ i ∈ s, C i) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty]
    funext x
    simp
  | cons i t hi ih =>
    rw [Finset.sum_cons, ih, indicatorFn_add]
    congr 1
    ext x
    simp [Finset.mem_cons]

/-- **Corollary 16.4.1** of [rockafellar1970convex], exact form for $m$ sets. Let
$C_1, \dots, C_m \subseteq \mathbb{R}^n$ be convex with $m \ge 1$. If the sets
$\operatorname{ri} C_i$ have a point in common, then the closure can be omitted:
$$\delta^*(\cdot \mid C_1 \cap \cdots \cap C_m) = \delta^*(\cdot \mid C_1) \mathbin{\square}
  \cdots \mathbin{\square} \delta^*(\cdot \mid C_m).$$

The source also assumes the sets $C_i$ non-empty. That hypothesis is omitted here because the
common point of the relative interiors implies it. -/
theorem corollary_16_4_1_exact_finset {ι : Type*} {s : Finset ι} {C : ι → Set (Rn n)}
    (hs : s.Nonempty) (hC : ∀ i ∈ s, Convex ℝ (C i)) {x₀ : Rn n} (hx₀ : ∀ i ∈ s, x₀ ∈ ri (C i)) :
    supportFn (pairing n) (⋂ i ∈ s, C i)
      = ofInfConvFn (∑ i ∈ s, toInfConvFn (supportFn (pairing n) (C i))) := by
  have hconj : ∀ i, supportFn (pairing n) (C i) = convexConj (pairing n) (indicatorFn (C i)) :=
    fun i => supportFn_eq_convexConj_indicatorFn (pairing n) (C i)
  rw [supportFn_eq_convexConj_indicatorFn, ← sum_indicatorFn_finset,
    theorem_16_4_exact_finset (f := fun i => indicatorFn (C i)) hs
      (fun i hi => convexFn_indicatorFn.2 (hC i hi))
      (fun i hi => ⟨⟨x₀, by rw [convexDom_indicatorFn]; exact intrinsicInterior_subset (hx₀ i hi)⟩,
        indicatorFn_ne_bot (C i)⟩)
      (fun i hi => by rw [convexDom_indicatorFn]; exact hx₀ i hi)]
  simp only [hconj]

/-- **Corollary 16.4.1** of [rockafellar1970convex], attainment for $m$ sets. Let
$C_1, \dots, C_m \subseteq \mathbb{R}^n$ be convex with $m \ge 1$, such that the sets
$\operatorname{ri} C_i$ have a point in common. Then for every $x^* \in \mathbb{R}^n$ there are
$x_1^*, \dots, x_m^*$ with $x_1^* + \cdots + x_m^* = x^*$ and
$$\delta^*(x_1^* \mid C_1) + \cdots + \delta^*(x_m^* \mid C_m) = \delta^*(x^* \mid C_1 \cap
  \cdots \cap C_m).$$
-/
theorem corollary_16_4_1_attained_finset {ι : Type*} {s : Finset ι} {C : ι → Set (Rn n)}
    (hs : s.Nonempty) (hC : ∀ i ∈ s, Convex ℝ (C i)) {x₀ : Rn n} (hx₀ : ∀ i ∈ s, x₀ ∈ ri (C i))
    (y : Rn n) :
    ∃ y' : ι → Rn n, ∑ i ∈ s, y' i = y ∧
      ∑ i ∈ s, supportFn (pairing n) (C i) (y' i)
        = supportFn (pairing n) (⋂ i ∈ s, C i) y := by
  have hconj : ∀ i, supportFn (pairing n) (C i) = convexConj (pairing n) (indicatorFn (C i)) :=
    fun i => supportFn_eq_convexConj_indicatorFn (pairing n) (C i)
  obtain ⟨y', hy', hval⟩ :=
    theorem_16_4_attained_finset (f := fun i => indicatorFn (C i)) hs
      (fun i hi => convexFn_indicatorFn.2 (hC i hi))
      (fun i hi => ⟨⟨x₀, by rw [convexDom_indicatorFn]; exact intrinsicInterior_subset (hx₀ i hi)⟩,
        indicatorFn_ne_bot (C i)⟩)
      (fun i hi => by rw [convexDom_indicatorFn]; exact hx₀ i hi) y
  refine ⟨y', hy', ?_⟩
  rw [supportFn_eq_convexConj_indicatorFn, ← sum_indicatorFn_finset, ← hval]
  simp only [hconj]

/-! ### Theorem 16.5: pointwise suprema and convex hulls -/

/-- **Theorem 16.5** of [rockafellar1970convex], first formula. Let $\{f_i \mid i \in I\}$ be any
family of functions on $\mathbb{R}^n$ with values in $[-\infty, +\infty]$, over an arbitrary
index set $I$. Then
$$(\operatorname{conv} \{f_i \mid i \in I\})^* = \sup \{f_i^* \mid i \in I\}.$$

No hypothesis is placed on the functions, and the empty family is allowed. The proof specializes
`ConvexAnalysis.convexConj_convFn`. -/
theorem theorem_16_5_convFn {ι : Sort*} (f : ι → Rn n → EReal) :
    convexConj (pairing n) (convFn f) = ⨆ i, convexConj (pairing n) (f i) :=
  convexConj_convFn (pairing n) f

/-- **Theorem 16.5** of [rockafellar1970convex], second formula. Let $\{f_i \mid i \in I\}$ be a
family of convex functions on $\mathbb{R}^n$. Then
$$(\sup \{\operatorname{cl} f_i \mid i \in I\})^* = \operatorname{cl}(\operatorname{conv}
  \{f_i^* \mid i \in I\}).$$

The proof applies `ConvexAnalysis.convexConj_iSup_eq_convexCl_convFn` to the closures. -/
theorem theorem_16_5_closure {ι : Sort*} {f : ι → Rn n → EReal} (hf : ∀ i, ConvexFn (f i)) :
    convexConj (pairing n) (⨆ i, convexCl (f i))
      = convexCl (convFn fun i => convexConj (pairing n) (f i)) := by
  rw [convexConj_iSup_eq_convexCl_convFn (fun i => convexFn_convexCl (hf i))
      (fun i => closedConvex_convexCl (f i))]
  simp only [convexConj_convexCl]

/-- **Corollary 16.5.1** of [rockafellar1970convex], first formula. Let $\{C_i \mid i \in I\}$ be
any family of subsets of $\mathbb{R}^n$, and let $D$ be the convex hull of their union. Then
$$\delta^*(\cdot \mid D) = \sup \{\delta^*(\cdot \mid C_i) \mid i \in I\}.$$
-/
theorem corollary_16_5_1_hull {ι : Sort*} (C : ι → Set (Rn n)) :
    supportFn (pairing n) (convexHull ℝ (⋃ i, C i))
      = fun y => ⨆ i, supportFn (pairing n) (C i) y := by
  rw [supportFn_convexHull, supportFn_iUnion]

/-- **Corollary 16.5.1** of [rockafellar1970convex], second formula. Let $\{C_i \mid i \in I\}$ be a
family of convex subsets of $\mathbb{R}^n$ with $I$ non-empty. Then
$$\delta^*\Bigl(\cdot \Bigm| \bigcap_{i \in I} \operatorname{cl} C_i\Bigr) =
  \operatorname{cl}(\operatorname{conv} \{\delta^*(\cdot \mid C_i) \mid i \in I\}).$$

**Reading.** The source does not exclude an empty index set. For an empty family the left side
is $\delta^*(\cdot \mid \mathbb{R}^n) = \delta(\cdot \mid 0)$ and the right side is the constant
$+\infty$, so the declaration assumes $I$ non-empty.

This is the case of indicator functions of `Rockafellar.theorem_16_5_closure`. -/
theorem corollary_16_5_1_closure {ι : Sort*} [Nonempty ι] {C : ι → Set (Rn n)}
    (hC : ∀ i, Convex ℝ (C i)) :
    supportFn (pairing n) (⋂ i, closure (C i))
      = convexCl (convFn fun i => supportFn (pairing n) (C i)) := by
  have hind : (⨆ i, convexCl (indicatorFn (C i))) = indicatorFn (⋂ i, closure (C i)) := by
    simp only [convexCl_indicatorFn]
    funext x
    rw [iSup_apply]
    by_cases hx : x ∈ ⋂ i, closure (C i)
    · rw [indicatorFn_of_mem hx]
      refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le (Classical.arbitrary ι) ?_)
      · rw [indicatorFn_of_mem (Set.mem_iInter.1 hx i)]
      · rw [indicatorFn_of_mem (Set.mem_iInter.1 hx _)]
    · rw [indicatorFn_of_notMem hx]
      obtain ⟨i, hi⟩ := not_forall.1 (fun h => hx (Set.mem_iInter.2 h))
      exact le_antisymm le_top (le_iSup_of_le i (by rw [indicatorFn_of_notMem hi]))
  simp only [supportFn_eq_convexConj_indicatorFn]
  rw [← hind]
  exact theorem_16_5_closure fun i => convexFn_indicatorFn.2 (hC i)

/-- **Corollary 16.5.2** of [rockafellar1970convex], first formula. Let $\{C_i \mid i \in I\}$ be
any family of subsets of $\mathbb{R}^n$. Then
$$\Bigl(\operatorname{conv} \bigcup_{i \in I} C_i\Bigr)^\circ = \bigcap_{i \in I} C_i^\circ.$$

Polarity reverses inclusion, and each half-space $\{x \mid \langle x, x^* \rangle \le 1\}$ is
convex, so the convex hull does not change the polar. This is the second proof in the source. -/
theorem corollary_16_5_2_hull {ι : Sort*} (C : ι → Set (Rn n)) :
    polarSet (pairing n) (convexHull ℝ (⋃ i, C i)) = ⋂ i, polarSet (pairing n) (C i) := by
  ext y
  simp only [Set.mem_iInter, mem_polarSet]
  constructor
  · intro hy i x hx
    exact hy x (subset_convexHull ℝ _ (Set.mem_iUnion.2 ⟨i, hx⟩))
  · intro hy
    have hsub : (⋃ i, C i) ⊆ {x : Rn n | pairing n x y ≤ 1} := by
      rintro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact hy i x hi
    exact fun x hx => convexHull_min hsub (convex_setOf_pairing_le_one y) hx

/-- **Corollary 16.5.2** of [rockafellar1970convex], second formula, one inclusion. Let
$\{C_j \mid j \in I\}$ be any family of subsets of $\mathbb{R}^n$. Then for each $i \in I$
$$C_i^\circ \subseteq \Bigl(\bigcap_{j \in I} C_j\Bigr)^\circ.$$

Each $C_i^\circ$ is contained in the polar of the intersection, and so is the convex hull of
their union. The source states an equality for the polar of $\bigcap_j \operatorname{cl} C_j$,
which holds after a closure. The equality is not formalized. -/
theorem corollary_16_5_2_inter {ι : Sort*} (C : ι → Set (Rn n)) (i : ι) :
    polarSet (pairing n) (C i) ⊆ polarSet (pairing n) (⋂ j, C j) :=
  polarSet_anti (Set.iInter_subset C i)

end Rockafellar
