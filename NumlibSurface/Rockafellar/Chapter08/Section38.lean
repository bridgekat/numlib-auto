/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Bifunction.Cofinite
import NumlibSurface.Rockafellar.Chapter06.Section30

/-!
# Rockafellar, Section 38: The algebra of bifunctions

This module formalizes Section 38 of [rockafellar1970convex] (pages 401–412). The section defines
four operations on convex bifunctions and shows how each behaves under the adjoint. The **sum**
$F_1 \square F_2$ is infimal convolution in the second variable,
$(F_1 \square F_2)u = F_1 u \square F_2 u$, and $(F_1 \square F_2)^* = F_1^* \square F_2^*$. The
**scalar multiple** $F\lambda$ is $((F\lambda)u)(x) = \lambda (Fu)(\lambda^{-1} x)$ for
$\lambda > 0$, and $(F\lambda)^* = F^*\lambda$. The **image** of a convex function $f$ is
$(Ff)(x) = \inf_u \{f(u) + (Fu)(x)\}$, and $(Ff)^* = F_*^* f^*$. The **product** is
$((GF)u)(y) = \inf_x \{(Fu)(x) + (Gx)(y)\}$, and $(GF)^* = F^* G^*$. These formulas extend
$(A_1 + A_2)^* = A_1^* + A_2^*$, $(A\lambda)^* = A^*\lambda$ and $(BA)^* = A^* B^*$ for linear maps.
The section also defines the inner product $\langle f, g \rangle$ of a convex function $f$ and a
concave function $g$, and shows that an adjoint moves across it: $\langle Ff, x^* \rangle = \langle
f, F^* x^* \rangle$. It closes with co-finite bifunctions, for which every qualification disappears.

All twelve numbered results of Section 38 are formalized: Theorems 38.1–38.5 and 38.7, Lemma 38.6,
and Corollaries 38.2.1, 38.4.1, 38.5.1, 38.7.1 and 38.7.2. The proofs specialize
`Numlib.Analysis.Convex.Bifunction.Algebra` and `Numlib.Analysis.Convex.Bifunction.Cofinite`.

## Main definitions

* Theorem 38.1, `Rockafellar.convexAdd` and `Rockafellar.concaveAdd`: the two conventions
  $\infty - \infty = -\infty$ and $\infty - \infty = +\infty$ under which Theorem 38.1 holds for
  convex and for concave bifunctions.
* Section 38, `Rockafellar.HasInnerProduct` and `Rockafellar.innerProduct`: the condition for the
  inner product $\langle f, g \rangle$ to exist, and its value.
* `Rockafellar.IsExactSumCor3821`, `Rockafellar.IsExactSumCor3841`, `Rockafellar.IsExactSumCor3851`:
  the exactness hypotheses of Corollaries 38.2.1, 38.4.1 and 38.5.1.

## Main results

* Theorem 38.1, `Rockafellar.theorem_38_1_convex`, `Rockafellar.theorem_38_1_dom`,
  `Rockafellar.theorem_38_1_bracket`, `Rockafellar.theorem_38_1_bracket_concave`: $F_1 \square F_2$
  is convex, $\operatorname{dom}(F_1 \square F_2) = \operatorname{dom} F_1 \cap \operatorname{dom}
  F_2$, and $\langle (F_1 \square F_2)u, x^* \rangle = \langle F_1 u, x^* \rangle + \langle F_2 u,
  x^* \rangle$ in the convex and in the concave orientation.
* Theorem 38.2, `Rockafellar.theorem_38_2`: $(F_1 \square F_2)^* = F_1^* \square F_2^*$.
* Corollary 38.2.1, `Rockafellar.corollary_38_2_1_closed`, `Rockafellar.corollary_38_2_1_adjoint`:
  $F_1 \square F_2$ is closed, and $(F_1 \square F_2)^* = \operatorname{cl}(F_1^* \square F_2^*)$.
* Theorem 38.3, `Rockafellar.theorem_38_3_convex`, `Rockafellar.theorem_38_3_bracket`,
  `Rockafellar.theorem_38_3_adjoint`, `Rockafellar.theorem_38_3_closed`,
  `Rockafellar.theorem_38_3_proper`: $F\lambda$ is convex, closed and proper with $F$, $\langle
  (F\lambda)u, x^* \rangle = \lambda \langle Fu, x^* \rangle$, and $(F\lambda)^* = F^*\lambda$.
* Theorem 38.4, `Rockafellar.theorem_38_4_convex`, `Rockafellar.theorem_38_4_conj`,
  `Rockafellar.theorem_38_4_attained`: $Ff$ is convex, and $(Ff)^* = F_*^* f^*$ with the infimum
  attained.
* Corollary 38.4.1, `Rockafellar.corollary_38_4_1_closed`, `Rockafellar.corollary_38_4_1_attained`,
  `Rockafellar.corollary_38_4_1_conj`: $Ff$ is closed, the infimum defining it is attained, and
  $(Ff)^* = \operatorname{cl}(F_*^* f^*)$.
* Theorem 38.5, `Rockafellar.theorem_38_5_convex`, `Rockafellar.theorem_38_5_adjoint`,
  `Rockafellar.theorem_38_5_attained`: $GF$ is convex, and $(GF)^* = F^* G^*$ with the supremum
  attained.
* Corollary 38.5.1, `Rockafellar.corollary_38_5_1_closed`, `Rockafellar.corollary_38_5_1_attained`,
  `Rockafellar.corollary_38_5_1_adjoint`: $GF$ is closed, the infimum defining it is attained, and
  $(GF)^* = \operatorname{cl}(F^* G^*)$.
* Lemma 38.6, `Rockafellar.lemma_38_6_exists`, `Rockafellar.lemma_38_6`: if $\langle f, g \rangle$
  exists, then $\langle f^*, g^* \rangle$ exists and equals $-\langle f, g \rangle$.
* Corollary 38.7.1, `Rockafellar.corollary_38_7_1_exists`, `Rockafellar.corollary_38_7_1`: $\langle
  Ff, x^* \rangle = \langle f, F^* x^* \rangle$.
* Theorem 38.7, `Rockafellar.theorem_38_7`, `Rockafellar.theorem_38_7_third`: $\langle Ff, g^*
  \rangle = \langle f, F^* g^* \rangle$ and $\langle F_*^* f^*, g \rangle = -\langle Ff, g^*
  \rangle$.
* Corollary 38.7.2, `Rockafellar.corollary_38_7_2_exists`, `Rockafellar.corollary_38_7_2_first`,
  `Rockafellar.corollary_38_7_2_second`: $\langle GFu, y^* \rangle = \langle Fu, G^* y^* \rangle =
  \langle u, F^* G^* y^* \rangle$.

## Conventions

* For a bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$,
  $\langle Fu, x^* \rangle = (Fu)^*(x^*)$ is `ConvexAnalysis.bracket (pairing n) F u x*`, and
  $F_*^*$, the adjoint of the inverse, is `ConvexAnalysis.lowerAdjointBifun`. The statements of the
  closed case use $F_*^*$, which is a convex bifunction, in place of the concave $F^*$.
* The inner product $\langle f, g \rangle$ is a partial operation. The book states the condition for
  it to exist in words and then writes $\langle f, g \rangle$ freely. Here
  `Rockafellar.HasInnerProduct` is that condition, and it is an explicit hypothesis wherever an
  inner product is claimed to exist. `Rockafellar.innerProduct` is the value of the infimum side,
  which is the inner product only under this condition.

## Implementation notes

* The two conventions for $\infty - \infty$ in Theorem 38.1 are two different operations on
  $[-\infty, +\infty]$. `Rockafellar.convexAdd` is the addition of `EReal`, and
  `Rockafellar.concaveAdd` is not. `Rockafellar.theorem_38_1_bracket_concave` is false with
  `Rockafellar.convexAdd` in place of `Rockafellar.concaveAdd`.
* Several statements assume only that $f$, $g$ or $F$ is proper, and not that it is convex or
  concave, where the proof does not need convexity.

## Deviations from the source

* **Theorem 38.1** (typo). The book prints $\operatorname{dom}(F_1 \cap F_2)$ on the left-hand side
  of the domain formula. The operation meant is $\square$, as the proof of the book shows. See
  `Rockafellar.theorem_38_1_dom`.
* **Relative interior hypotheses** (reading). Every condition of the book of the form
  "$\operatorname{ri}(\operatorname{dom} \cdot)$ and $\operatorname{ri}(\operatorname{dom} \cdot)$
  have a point in common" is the hypothesis of Theorem 16.4. Each statement here assumes instead the
  conclusion of Theorem 16.4, that the two functions add exactly (`ConvexAnalysis.IsExactSum`). This
  hypothesis is required for each dual vector separately, where the condition of the book is
  uniform, and it includes the properness of both summands, which is the main case of the book. This
  applies to Theorems 38.2, 38.4, 38.5 and 38.7 and to Corollaries 38.2.1, 38.4.1, 38.5.1, 38.7.1
  and 38.7.2. See `Rockafellar.theorem_38_2`.
* **Commutativity and associativity of $\square$** (generalization). The book says that $\square$ is
  commutative and associative "to the extent that it is defined". Infimal convolution is defined for
  all functions with values in $[-\infty, +\infty]$, so the laws hold for all bifunctions, improper
  ones included. See `Rockafellar.infConvBifun_comm'` and `Rockafellar.infConvBifun_assoc'`.

## Not formalized

* **The caveat on the product of bifunctions.** The book's restriction "to the extent that it is
  defined" for the multiplication of bifunctions is not discharged.
* **Lemma 38.6**, the second assertion: $\langle \operatorname{cl} f, \operatorname{cl} g \rangle$
  then exists and equals $\langle f, g \rangle$.
* **Theorem 38.7**, the middle member $-\langle f^*, F_* g \rangle$ of the chain of equalities.
-/

open Set

namespace Rockafellar

open ConvexAnalysis

/-! ### The two conventions for $\infty - \infty$ in Theorem 38.1 -/

/-- The **convex convention** $\infty - \infty = -\infty + \infty = -\infty$ of Theorem 38.1 of
[rockafellar1970convex]: the sum $a + b$ of $a, b \in [-\infty, +\infty]$ with
$(+\infty) + (-\infty) = -\infty$. Under this convention the identity of Theorem 38.1 holds for
convex bifunctions.

On `EReal` this is the usual addition. The definition gives the convention a name that differs
from the one of the concave convention. -/
noncomputable def convexAdd (a b : EReal) : EReal := a + b

/-- The **concave convention** $\infty - \infty = -\infty + \infty = +\infty$ of Theorem 38.1 of
[rockafellar1970convex]: the sum of $a, b \in [-\infty, +\infty]$ defined by $-((-a) + (-b))$,
so that $(+\infty) + (-\infty) = +\infty$. Under this convention the identity of Theorem 38.1
holds for concave bifunctions.

This is not the addition of `EReal`: it is addition read through negation. -/
noncomputable def concaveAdd (a b : EReal) : EReal := -(-a + -b)

/-- For $a, b \in [-\infty, +\infty]$, the convex convention gives $a + b$, the usual sum in
`EReal`. -/
theorem convexAdd_apply (a b : EReal) : convexAdd a b = a + b := rfl

/-- For $a, b \in [-\infty, +\infty]$, the concave convention gives $-((-a) + (-b))$. -/
theorem concaveAdd_apply (a b : EReal) : concaveAdd a b = -(-a + -b) := rfl

/-- The convex convention gives $(+\infty) + (-\infty) = -\infty$. -/
@[simp] theorem convexAdd_top_bot : convexAdd ⊤ ⊥ = ⊥ := by
  rw [convexAdd_apply, EReal.add_bot]

/-- The concave convention gives $(+\infty) + (-\infty) = +\infty$. -/
@[simp] theorem concaveAdd_top_bot : concaveAdd ⊤ ⊥ = ⊤ := by
  rw [concaveAdd_apply, EReal.neg_top, EReal.neg_bot, EReal.bot_add,
    EReal.neg_bot]

/-- The convex and the concave conventions are different operations: they differ at
$((+\infty), (-\infty))$. This is why they have different names here, where the notation
$\langle \cdot, \cdot \rangle$ of the book carries both. -/
theorem convexAdd_ne_concaveAdd : convexAdd ⊤ ⊥ ≠ concaveAdd ⊤ ⊥ := by
  rw [convexAdd_top_bot, concaveAdd_top_bot]
  exact bot_ne_top

/-- Let $a, b \in [-\infty, +\infty]$. If $\{a, b\}$ is not $\{+\infty, -\infty\}$, that is, if
$a \neq +\infty$ or $b \neq -\infty$, and $a \neq -\infty$ or $b \neq +\infty$, then the convex
and the concave conventions give the same sum. -/
theorem concaveAdd_eq_convexAdd {a b : EReal} (h₁ : a ≠ ⊤ ∨ b ≠ ⊥) (h₂ : a ≠ ⊥ ∨ b ≠ ⊤) :
    concaveAdd a b = convexAdd a b := by
  have hn₁ : -a ≠ ⊥ ∨ -b ≠ ⊤ := by
    rcases h₁ with h | h
    · exact Or.inl (by rw [Ne, EReal.neg_eq_bot_iff]; exact h)
    · exact Or.inr (by rw [Ne, EReal.neg_eq_top_iff]; exact h)
  have hn₂ : -a ≠ ⊤ ∨ -b ≠ ⊥ := by
    rcases h₂ with h | h
    · exact Or.inl (by rw [Ne, EReal.neg_eq_top_iff]; exact h)
    · exact Or.inr (by rw [Ne, EReal.neg_eq_bot_iff]; exact h)
  have hna : -(-a + -b) = - -a + - -b := EReal.neg_add hn₁ hn₂
  have hb₁ : (- -a : EReal) = a := neg_neg a
  have hb₂ : (- -b : EReal) = b := neg_neg b
  rw [concaveAdd_apply, convexAdd_apply, hna, hb₁, hb₂]

/-! ### The inner product of a convex and a concave function -/

/-- **Section 38** of [rockafellar1970convex], existence of the inner product. For
$f, g : \mathbb{R}^n \to [-\infty, +\infty]$, the inner product $\langle f, g \rangle$
**exists** if
$$\sup_x \{g^*(x) - f(x)\} = \inf_y \{f^*(y) - g(y)\},$$
where $f^*$ is the convex conjugate of $f$ and $g^*$ is the concave conjugate of $g$. The book
leaves $\langle f, g \rangle$ undefined when the two extrema differ.

This predicate is the side condition of every statement below that says that an inner product
exists. The definition is `ConvexAnalysis.HasFenchelPairing` for the Euclidean pairing. -/
abbrev HasInnerProduct {n : ℕ} (f g : Rn n → EReal) : Prop :=
  HasFenchelPairing (pairing n) f g

/-- **Section 38** of [rockafellar1970convex], the value of the inner product. For
$f, g : \mathbb{R}^n \to [-\infty, +\infty]$, this is the infimum side
$$\inf_y \{f^*(y) - g(y)\}$$
of $\langle f, g \rangle$. It is the inner product of the book only when
`Rockafellar.HasInnerProduct f g` holds. -/
noncomputable abbrev innerProduct {n : ℕ} (f g : Rn n → EReal) : EReal :=
  fenchelPairing (pairing n) f g

variable {m n k : ℕ}

/-- For $f, g : \mathbb{R}^n \to [-\infty, +\infty]$, the value `Rockafellar.innerProduct f g` is
$\inf_y \{f^*(y) - g(y)\}$. -/
theorem innerProduct_eq (f g : Rn n → EReal) :
    innerProduct f g = ⨅ y, (convexConj (pairing n) f y - g y) := rfl

/-- For $f, g : \mathbb{R}^n \to [-\infty, +\infty]$, the inner product $\langle f, g \rangle$
exists if and only if $\sup_x \{g^*(x) - f(x)\} = \inf_y \{f^*(y) - g(y)\}$. This is the
condition of the book in its own two extrema. -/
theorem hasInnerProduct_iff (f g : Rn n → EReal) :
    HasInnerProduct f g ↔
      (⨆ x, (concaveConj (pairing n) g x - f x)) = ⨅ y, (convexConj (pairing n) f y - g y) := by
  rw [← fenchelInf_apply (pairing n) f g]
  have h : (⨆ x, (concaveConj (pairing n) g x - f x)) = fenchelSup (pairing n) f g := by
    rw [fenchelSup_apply, flip_pairing]
  rw [h]
  exact Iff.rfl

/-- Weak duality: for all $f, g : \mathbb{R}^n \to [-\infty, +\infty]$,
$$\sup_x \{g^*(x) - f(x)\} \le \inf_y \{f^*(y) - g(y)\}.$$
No hypothesis is needed. So every claim below that an inner product exists reduces to the
reverse inequality. -/
theorem fenchelSup_le_innerProduct (f g : Rn n → EReal) :
    (⨆ x, (concaveConj (pairing n) g x - f x)) ≤ innerProduct f g := by
  have h : (⨆ x, (concaveConj (pairing n) g x - f x)) = fenchelSup (pairing n) f g := by
    rw [fenchelSup_apply, flip_pairing]
  rw [h]
  exact fenchelSup_le_fenchelInf (pairing n) f g

/-! ### Theorem 38.1 -/

/-- **Theorem 38.1** of [rockafellar1970convex], convexity. Let $F_1$ and $F_2$ be proper convex
bifunctions from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then the bifunction $F_1 \square F_2$,
defined by $(F_1 \square F_2)u = F_1 u \square F_2 u$, is convex.

$F_1 \square F_2$ is `ConvexAnalysis.infConvBifun F₁ F₂`, the infimal convolution in the second
variable for each fixed first variable. -/
theorem theorem_38_1_convex {F₁ F₂ : Bifun (Rn m) (Rn n)} (hp₁ : ProperConvex (graphFn F₁))
    (hp₂ : ProperConvex (graphFn F₂)) (hc₁ : ConvexBifun F₁) (hc₂ : ConvexBifun F₂) :
    ConvexBifun (infConvBifun F₁ F₂) :=
  convexBifun_infConvBifun (fun u x => hp₁.ne_bot (u, x)) (fun u x => hp₂.ne_bot (u, x)) hc₁ hc₂

/-- **Theorem 38.1** of [rockafellar1970convex], the effective domain. For all bifunctions $F_1$ and
$F_2$ from $\mathbb{R}^m$ to $\mathbb{R}^n$,
$$\operatorname{dom}(F_1 \square F_2) = \operatorname{dom} F_1 \cap \operatorname{dom} F_2.$$
No hypothesis is needed.

**Typo.** The book prints the left-hand side as $\operatorname{dom}(F_1 \cap F_2)$. The
operation meant is $\square$, as the proof of the book shows. -/
theorem theorem_38_1_dom (F₁ F₂ : Bifun (Rn m) (Rn n)) :
    convexDomBifun (infConvBifun F₁ F₂) = convexDomBifun F₁ ∩ convexDomBifun F₂ :=
  convexDomBifun_infConvBifun F₁ F₂

/-- **Theorem 38.1** of [rockafellar1970convex], the inner product identity. For all bifunctions
$F_1$ and $F_2$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, all $u \in \mathbb{R}^m$ and all
$x^* \in \mathbb{R}^n$,
$$\langle (F_1 \square F_2)u, x^* \rangle = \langle F_1 u, x^* \rangle + \langle F_2 u, x^*
  \rangle,$$
where the sum uses the convex convention $\infty - \infty = -\infty$.

No hypothesis is needed. The identity is the formula $(f \square g)^* = f^* + g^*$ of Theorem
16.4, which holds without hypotheses, applied to each slice. -/
theorem theorem_38_1_bracket (F₁ F₂ : Bifun (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    bracket (pairing n) (infConvBifun F₁ F₂) u y
      = convexAdd (bracket (pairing n) F₁ u y) (bracket (pairing n) F₂ u y) :=
  congrFun (bracket_infConvBifun (pairing n) F₁ F₂ u) y

/-- **Theorem 38.1** of [rockafellar1970convex], the concave orientation. For all bifunctions $G_1$
and $G_2$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, all $u \in \mathbb{R}^m$ and all
$x^* \in \mathbb{R}^n$, the concave conjugate of the supremal convolution $G_1 u \square G_2 u$
at $x^*$ is the sum of the concave conjugates of $G_1 u$ and $G_2 u$ at $x^*$, where the sum
uses the concave convention $\infty - \infty = +\infty$.

For concave bifunctions, $\square$ is supremal convolution and $\langle G u, x^* \rangle$ is the
concave conjugate of the slice $Gu$. The statement is false with the convex convention in place
of the concave one. No hypothesis is needed. -/
theorem theorem_38_1_bracket_concave (G₁ G₂ : Bifun (Rn m) (Rn n)) (u : Rn m) (y : Rn n) :
    concaveConj (pairing n) (supConv (G₁ u) (G₂ u)) y
      = concaveAdd (concaveConj (pairing n) (G₁ u) y) (concaveConj (pairing n) (G₂ u) y) :=
  congrFun (concaveConj_supConv (pairing n) (G₁ u) (G₂ u)) y

/-! ### The algebra of the operation $\square$ -/

/-- For all bifunctions $F_1$ and $F_2$ from $\mathbb{R}^m$ to $\mathbb{R}^n$,
$F_1 \square F_2 = F_2 \square F_1$.

**Generalization.** The book says that $\square$ is commutative "in the class of convex
bifunctions from $\mathbb{R}^m$ to $\mathbb{R}^n$ to the extent that it is defined". Infimal
convolution is defined for all functions with values in $[-\infty, +\infty]$, so the law holds
for arbitrary bifunctions, improper ones included. -/
theorem infConvBifun_comm' (F₁ F₂ : Bifun (Rn m) (Rn n)) :
    infConvBifun F₁ F₂ = infConvBifun F₂ F₁ :=
  infConvBifun_comm F₁ F₂

/-- For all bifunctions $F_1$, $F_2$ and $F_3$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, $(F_1 \square
F_2) \square F_3 = F_1 \square (F_2 \square F_3)$.

**Generalization.** As for commutativity, the law holds for arbitrary bifunctions, where the
book restricts it to the extent that $\square$ is defined. -/
theorem infConvBifun_assoc' (F₁ F₂ F₃ : Bifun (Rn m) (Rn n)) :
    infConvBifun (infConvBifun F₁ F₂) F₃ = infConvBifun F₁ (infConvBifun F₂ F₃) :=
  infConvBifun_assoc F₁ F₂ F₃

/-! ### Theorem 38.2 -/

/-- **Theorem 38.2** of [rockafellar1970convex]. Let $F_1$ and $F_2$ be bifunctions from
$\mathbb{R}^m$ to $\mathbb{R}^n$. Assume that for every $x^* \in \mathbb{R}^n$ the convex
functions $u \mapsto -\langle F_1 u, x^* \rangle$ and $u \mapsto -\langle F_2 u, x^* \rangle$
add exactly. Then
$$(F_1 \square F_2)^* = F_1^* \square F_2^*,$$
where $\square$ on the right is supremal convolution of the concave bifunctions $F_i^*$.

**Reading.** The book assumes that $\operatorname{ri}(\operatorname{dom} F_1)$ and
$\operatorname{ri}(\operatorname{dom} F_2)$ have a point in common, the hypothesis of Theorem
16.4. The statement here assumes the conclusion of Theorem 16.4 (`ConvexAnalysis.IsExactSum`),
once for each $x^*$: both functions are proper, and the conjugate of their sum is the infimal
convolution of their conjugates, with the infimum attained.

This is the analogue for bifunctions of the formula $(A_1 + A_2)^* = A_1^* + A_2^*$ for linear
maps. -/
theorem theorem_38_2 (F₁ F₂ : Bifun (Rn m) (Rn n))
    (hex : ∀ y : Rn n, IsExactSum (pairing m) (fun u => -(bracket (pairing n) F₁ u y))
      (fun u => -(bracket (pairing n) F₂ u y))) :
    dualProgram (infConvBifun F₁ F₂) = supConvBifun (dualProgram F₁) (dualProgram F₂) :=
  convexAdjointBifun_infConvBifun_eq_supConvBifun (pairing m) (pairing n) F₁ F₂ hex

/-! ### Corollary 38.2.1 -/

/-- The exactness hypothesis of Corollary 38.2.1. For bifunctions $F_1$ and $F_2$ from
$\mathbb{R}^m$ to $\mathbb{R}^n$, it says that for every $u \in \mathbb{R}^m$ the convex
functions $x^* \mapsto \langle u, F_1^* x^* \rangle$ and
$x^* \mapsto \langle u, F_2^* x^* \rangle$ add exactly (`ConvexAnalysis.IsExactSum`).

The book's condition is that $\operatorname{ri}(\operatorname{dom} F_1^*)$ and
$\operatorname{ri}(\operatorname{dom} F_2^*)$ have a point in common. The bifunction $F_i^*$ is
written as the inverse of $F_{i*}^*$. -/
abbrev IsExactSumCor3821 (F₁ F₂ : Bifun (Rn m) (Rn n)) : Prop :=
  ∀ u : Rn m, IsExactSum (pairing n)
    (concaveBracket (pairing m)
      (inverseBifun (lowerAdjointBifun (pairing m) (pairing n) F₁)) u)
    (concaveBracket (pairing m)
      (inverseBifun (lowerAdjointBifun (pairing m) (pairing n) F₂)) u)

/-- **Corollary 38.2.1** of [rockafellar1970convex], closedness. Let $F_1$ and $F_2$ be closed
convex bifunctions from $\mathbb{R}^m$ to $\mathbb{R}^n$ that satisfy the exactness hypothesis
`Rockafellar.IsExactSumCor3821`. Then $F_1 \square F_2$ is closed.

**Reading.** The book assumes that $\operatorname{ri}(\operatorname{dom} F_1^*)$ and
$\operatorname{ri}(\operatorname{dom} F_2^*)$ have a point in common. The statement here assumes
the exactness that Theorem 16.4 derives from this condition.

The proof differs from the one of the book: it shows that $F_1 \square F_2$ is a lower adjoint
$H_*^*$, and every lower adjoint is closed. -/
theorem corollary_38_2_1_closed {F₁ F₂ : Bifun (Rn m) (Rn n)} (hc₁ : ConvexBifun F₁)
    (hcl₁ : ClosedConvexBifun F₁) (hc₂ : ConvexBifun F₂) (hcl₂ : ClosedConvexBifun F₂)
    (hex : IsExactSumCor3821 F₁ F₂) : ClosedConvexBifun (infConvBifun F₁ F₂) := by
  refine closedConvexBifun_infConvBifun (Bu := pairing m) (Bx := pairing n) hc₁ hcl₁ hc₂ hcl₂ ?_
  simpa using hex

/-- **Corollary 38.2.1** of [rockafellar1970convex], the adjoint. Let $F_1$ and $F_2$ be closed
proper convex bifunctions from $\mathbb{R}^m$ to $\mathbb{R}^n$ that satisfy the exactness
hypothesis `Rockafellar.IsExactSumCor3821`. Then
$$(F_1 \square F_2)_*^* = \operatorname{cl}(F_{1*}^* \mathbin{\square_1} F_{2*}^*),$$
where $\square_1$ is infimal convolution in the first variable.

**Reading.** As in `Rockafellar.corollary_38_2_1_closed`, the relative interior condition of the
book is replaced by exactness.

The book states $(F_1 \square F_2)^* = \operatorname{cl}(F_1^* \square F_2^*)$ for the concave
adjoints. The statement here is that formula with the negations moved outside, so that all
bifunctions are convex; the concave $\square$ on the right then becomes convolution in the first
variable (`ConvexAnalysis.infConvFstBifun`). -/
theorem corollary_38_2_1_adjoint {F₁ F₂ : Bifun (Rn m) (Rn n)}
    (h₁ : ClosedProperConvexFn (graphFn F₁)) (h₂ : ClosedProperConvexFn (graphFn F₂))
    (hex : IsExactSumCor3821 F₁ F₂) :
    lowerAdjointBifun (pairing m) (pairing n) (infConvBifun F₁ F₂)
      = convexClBifun (infConvFstBifun (lowerAdjointBifun (pairing m) (pairing n) F₁)
          (lowerAdjointBifun (pairing m) (pairing n) F₂)) := by
  refine lowerAdjointBifun_infConvBifun_eq_convexClBifun (Bu := pairing m)
      (Bx := pairing n) h₁ h₂ ?_
  simpa using hex

/-! ### Theorem 38.3 -/

/-- **Theorem 38.3** of [rockafellar1970convex], convexity. Let $F$ be a convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$ and $\lambda > 0$. Then the bifunction $F\lambda$, defined by
$((F\lambda)u)(x) = \lambda (Fu)(\lambda^{-1} x)$, is convex. -/
theorem theorem_38_3_convex {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l)
    (hF : ConvexBifun F) : ConvexBifun (smulRightBifun F l) :=
  convexBifun_smulRightBifun hl hF

/-- **Theorem 38.3** of [rockafellar1970convex], the inner product identity. Let $F$ be a bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $\lambda > 0$. Then for all $u \in \mathbb{R}^m$ and
$x^* \in \mathbb{R}^n$,
$$\langle (F\lambda)u, x^* \rangle = \lambda \langle Fu, x^* \rangle.$$
-/
theorem theorem_38_3_bracket {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l) (u : Rn m)
    (y : Rn n) :
    bracket (pairing n) (smulRightBifun F l) u y = (l : EReal) * bracket (pairing n) F u y :=
  congrFun (bracket_smulRightBifun hl (pairing n) F u) y

/-- **Theorem 38.3** of [rockafellar1970convex], the adjoint. Let $F$ be a bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$ and $\lambda > 0$. Then $(F\lambda)^* = F^*\lambda$. No other
hypothesis is needed. -/
theorem theorem_38_3_adjoint {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l) :
    dualProgram (smulRightBifun F l) = smulRightBifun (dualProgram F) l :=
  funext fun y => funext fun v => convexAdjointBifun_smulRightBifun hl (pairing m) (pairing n) F y v

/-- **Theorem 38.3** of [rockafellar1970convex], closedness. Let $F$ be a closed convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $\lambda > 0$. Then $F\lambda$ is closed. -/
theorem theorem_38_3_closed {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l) (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) : ClosedConvexBifun (smulRightBifun F l) := by
  have hcont : Continuous (scaleFst (Rn n) l : Rn m × Rn n →ₗ[ℝ] Rn m × Rn n) := by
    change Continuous fun p : Rn m × Rn n => ((l • p.1, p.2) : Rn m × Rn n)
    exact (continuous_fst.const_smul l).prodMk continuous_snd
  refine closedConvexBifun_iff.2 ?_
  rw [graphFn_smulRightBifun hl F]
  exact closedConvex_smulRight (pairingProd m n) (convexFn_compLin _ hF)
    (closedConvex_compLin (closedConvexBifun_iff.1 hcl) hcont) hl

/-- **Theorem 38.3** of [rockafellar1970convex], properness. Let $F$ be a proper bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$ and $\lambda > 0$. Then $F\lambda$ is proper. -/
theorem theorem_38_3_proper {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hl : 0 < l)
    (hp : ProperConvex (graphFn F)) : ProperConvex (graphFn (smulRightBifun F l)) := by
  rw [graphFn_smulRightBifun hl F]
  refine properConvex_smulRight ⟨?_, fun p => hp.ne_bot _⟩ hl
  obtain ⟨p₀, hp₀⟩ := hp.convexDom_nonempty
  refine ⟨(l⁻¹ • p₀.1, p₀.2), ?_⟩
  have hq : ((l • (l⁻¹ • p₀.1), p₀.2) : Rn m × Rn n) = p₀ := by
    rw [smul_inv_smul₀ hl.ne']
  change compLin (graphFn F) (scaleFst (Rn n) l) (l⁻¹ • p₀.1, p₀.2) < ⊤
  rw [compLin_apply, scaleFst_apply, hq]
  exact mem_convexDom.1 hp₀

/-! ### Theorem 38.4 -/

/-- **Theorem 38.4** of [rockafellar1970convex], convexity. Let $F$ be a proper convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$, and let $f$ be a proper convex function on
$\mathbb{R}^m$. Then the image
$$(Ff)(x) = \inf_u \{f(u) + (Fu)(x)\}$$
is a convex function on $\mathbb{R}^n$. -/
theorem theorem_38_4_convex {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : ProperConvex (graphFn F)) (hfp : ProperConvex f) (hF : ConvexBifun F) (hf : ConvexFn f) :
    ConvexFn (imageBifun F f) :=
  convexFn_imageBifun (fun u x => hFp.ne_bot (u, x)) hfp.ne_bot hF hf

/-- **Theorem 38.4** of [rockafellar1970convex], the conjugate. Let $F$ be a proper bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$, let $f$ be a proper function on $\mathbb{R}^m$, and let
$x^* \in \mathbb{R}^n$. Assume that $f$ and the convex function
$u \mapsto -\langle Fu, x^* \rangle$ add exactly. Then
$$(Ff)^*(x^*) = (F_*^* f^*)(x^*) = \inf_{u^*} \{f^*(u^*) + (F_*^* u^*)(x^*)\}.$$

**Reading.** The book assumes that $\operatorname{ri}(\operatorname{dom} f)$ and
$\operatorname{ri}(\operatorname{dom} F)$ have a point in common. The statement here assumes the
exactness that Theorem 16.4 derives from this condition. The properness of
$u \mapsto -\langle Fu, x^* \rangle$, which is part of exactness, is the side condition
$x^* \in \operatorname{dom} F^*$ of the book. -/
theorem theorem_38_4_conj {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : ProperConvex (graphFn F)) (hf : ProperConvex f) {y : Rn n}
    (hex : IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    convexConj (pairing n) (imageBifun F f) y
      = imageBifun (lowerAdjointBifun (pairing m) (pairing n) F) (convexConj (pairing m) f) y :=
  convexConj_imageBifun_eq_imageBifun (fun u x => hFp.ne_bot (u, x)) hf hex

/-- **Theorem 38.4** of [rockafellar1970convex], attainment. Under the hypotheses of
`Rockafellar.theorem_38_4_conj`, the infimum that defines $(F_*^* f^*)(x^*)$ is attained: there
is a $u^* \in \mathbb{R}^m$ with
$$f^*(u^*) - (F^* x^*)(u^*) = (Ff)^*(x^*).$$

**Reading.** As in `Rockafellar.theorem_38_4_conj`, the relative interior condition of the book
is replaced by exactness. -/
theorem theorem_38_4_attained {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : ProperConvex (graphFn F)) (hf : ProperConvex f) {y : Rn n}
    (hex : IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    ∃ v : Rn m, convexConj (pairing m) f v - dualProgram F y v
      = convexConj (pairing n) (imageBifun F f) y :=
  exists_convexConj_imageBifun_eq (fun u x => hFp.ne_bot (u, x)) hf hex

/-! ### Corollary 38.4.1 -/

/-- The exactness hypothesis of Corollary 38.4.1. For a bifunction $F$ from $\mathbb{R}^m$ to
$\mathbb{R}^n$ and a function $f$ on $\mathbb{R}^m$, it says that for every $x \in \mathbb{R}^n$
the functions $f^*$ and $u^* \mapsto -\langle F_*^* u^*, x \rangle$ add exactly
(`ConvexAnalysis.IsExactSum`).

The book's condition is that $\operatorname{ri}(\operatorname{dom} f^*)$ and
$\operatorname{ri}(\operatorname{dom} F_*^*)$ have a point in common. -/
abbrev IsExactSumCor3841 (F : Bifun (Rn m) (Rn n)) (f : Rn m → EReal) : Prop :=
  ∀ x : Rn n, IsExactSum (pairing m) (convexConj (pairing m) f)
    (fun v => -(bracket (pairing n) (lowerAdjointBifun (pairing m) (pairing n) F) v x))

/-- **Corollary 38.4.1** of [rockafellar1970convex], closedness. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ with $(Fu_0)(x_0) < +\infty$ for some $u_0$ and
$x_0$, let $f$ be a closed proper convex function on $\mathbb{R}^m$, and assume the exactness
hypothesis `Rockafellar.IsExactSumCor3841`. Then $Ff$ is closed.

**Reading.** The book assumes that $\operatorname{ri}(\operatorname{dom} f^*)$ and
$\operatorname{ri}(\operatorname{dom} F_*^*)$ have a point in common. The statement here assumes
the exactness that Theorem 16.4 derives from this condition.

The proof shows that $Ff$ is a conjugate. -/
theorem corollary_38_4_1_closed {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal} (hF : ConvexBifun F)
    (hFcl : ClosedConvexBifun F) {u₀ : Rn m} {x₀ : Rn n} (hFp : F u₀ x₀ ≠ ⊤)
    (hf : ClosedProperConvexFn f)
        (hex : IsExactSumCor3841 F f) : ClosedConvex (imageBifun F f) := by
  refine closedConvex_imageBifun (Bu := pairing m) (Bx := pairing n) hF hFcl hFp hf ?_
  simpa using hex

/-- **Corollary 38.4.1** of [rockafellar1970convex], attainment. Under the hypotheses of
`Rockafellar.corollary_38_4_1_closed`, for every $x \in \mathbb{R}^n$ the infimum that defines
$(Ff)(x)$ is attained: there is a $u$ with $f(u) + (Fu)(x) = (Ff)(x)$.

**Reading.** As in `Rockafellar.corollary_38_4_1_closed`, the relative interior condition of the
book is replaced by exactness. -/
theorem corollary_38_4_1_attained {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hF : ConvexBifun F) (hFcl : ClosedConvexBifun F) {u₀ : Rn m} {x₀ : Rn n} (hFp : F u₀ x₀ ≠ ⊤)
    (hf : ClosedProperConvexFn f) (hex : IsExactSumCor3841 F f) {x : Rn n} :
    ∃ u : Rn m, f u + F u x = imageBifun F f x := by
  refine exists_imageBifun_eq (Bu := pairing m) (Bx := pairing n) hF hFcl hFp hf ?_
  simpa using hex x

/-- **Corollary 38.4.1** of [rockafellar1970convex], the conjugate. Under the hypotheses of
`Rockafellar.corollary_38_4_1_closed`,
$$(Ff)^* = \operatorname{cl}(F_*^* f^*).$$

**Reading.** As in `Rockafellar.corollary_38_4_1_closed`, the relative interior condition of the
book is replaced by exactness. -/
theorem corollary_38_4_1_conj {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal} (hF : ConvexBifun F)
    (hFcl : ClosedConvexBifun F) {u₀ : Rn m} {x₀ : Rn n} (hFp : F u₀ x₀ ≠ ⊤)
    (hf : ClosedProperConvexFn f) (hex : IsExactSumCor3841 F f) :
    convexConj (pairing n) (imageBifun F f)
      = convexCl
          (imageBifun (lowerAdjointBifun (pairing m) (pairing n) F)
              (convexConj (pairing m) f)) := by
  refine convexConj_imageBifun_eq_convexCl (Bu := pairing m) (Bx := pairing n) hF hFcl hFp hf ?_
  simpa using hex

/-! ### Theorem 38.5 -/

/-- Let $F$ be a proper bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $G$ a proper bifunction
from $\mathbb{R}^n$ to $\mathbb{R}^p$. Then $(GF)_* = F_* G_*$, where the product of the concave
bifunctions on the right is taken with a supremum. Inversion reverses the order of a product. -/
theorem inverseBifun_compBifun' (G : Bifun (Rn n) (Rn k)) (F : Bifun (Rn m) (Rn n))
    (hFp : ProperConvex (graphFn F)) (hGp : ProperConvex (graphFn G)) :
    inverseBifun (compBifun G F) = concaveCompBifun (inverseBifun G) (inverseBifun F) :=
  inverseBifun_compBifun G F (fun u x => hFp.ne_bot (u, x)) (fun x y => hGp.ne_bot (x, y))

/-- **Theorem 38.5** of [rockafellar1970convex], convexity. Let $F$ be a proper convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $G$ a proper convex bifunction from $\mathbb{R}^n$ to
$\mathbb{R}^p$. Then the product
$$((GF)u)(y) = \inf_x \{(Fu)(x) + (Gx)(y)\}$$
is a convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^p$. -/
theorem theorem_38_5_convex {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hFp : ProperConvex (graphFn F)) (hGp : ProperConvex (graphFn G)) (hF : ConvexBifun F)
    (hG : ConvexBifun G) : ConvexBifun (compBifun G F) :=
  convexBifun_compBifun (fun u x => hFp.ne_bot (u, x)) (fun x y => hGp.ne_bot (x, y)) hF hG

/-- **Theorem 38.5** of [rockafellar1970convex], the adjoint. Let $F$ be a proper bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$ and $G$ a bifunction from $\mathbb{R}^n$ to $\mathbb{R}^p$, and
let $y^* \in \mathbb{R}^p$ and $u^* \in \mathbb{R}^m$. Assume that the functions
$x \mapsto \langle u^*, F_* x \rangle$ and $x \mapsto -\langle Gx, y^* \rangle$ add exactly.
Then
$$((GF)^* y^*)(u^*) = ((F^* G^*) y^*)(u^*) = \sup_x \{(G^* y^*)(x) + (F^* x)(u^*)\}.$$

**Reading.** The book assumes that $\operatorname{ri}(\operatorname{dom} F_*)$ and
$\operatorname{ri}(\operatorname{dom} G)$ have a point in common. The statement here assumes the
exactness that Theorem 16.4 derives from this condition, once for each pair $(y^*, u^*)$.

The product $F^* G^*$ of the concave adjoints is `ConvexAnalysis.concaveCompBifun`, the product
with a supremum. -/
theorem theorem_38_5_adjoint {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hFp : ProperConvex (graphFn F)) {z : Rn k} {v : Rn m}
    (hex : IsExactSum (pairing n) (concaveBracket (pairing m) (inverseBifun F) v)
      (fun x => -(bracket (pairing k) G x z))) :
    dualProgram (compBifun G F) z v
      = concaveCompBifun (dualProgram G) (dualProgram F) z v := by
  refine convexAdjointBifun_compBifun (pairing m) (pairing n) (pairing k)
    (fun u x => hFp.ne_bot (u, x)) ?_
  simpa using hex

/-- **Theorem 38.5** of [rockafellar1970convex], attainment. Under the hypotheses of
`Rockafellar.theorem_38_5_adjoint`, the supremum that defines $((F^* G^*) y^*)(u^*)$ is
attained: there is an $x \in \mathbb{R}^n$ with
$$(G^* y^*)(x) + (F^* x)(u^*) = ((GF)^* y^*)(u^*).$$

**Reading.** As in `Rockafellar.theorem_38_5_adjoint`, the relative interior condition of the
book is replaced by exactness. -/
theorem theorem_38_5_attained {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hFp : ProperConvex (graphFn F)) {z : Rn k} {v : Rn m}
    (hex : IsExactSum (pairing n) (concaveBracket (pairing m) (inverseBifun F) v)
      (fun x => -(bracket (pairing k) G x z))) :
    ∃ x : Rn n, dualProgram G z x + dualProgram F x v = dualProgram (compBifun G F) z v := by
  refine exists_convexAdjointBifun_compBifun_eq (pairing m) (pairing n) (pairing k)
    (fun u x => hFp.ne_bot (u, x)) ?_
  simpa using hex

/-! ### Corollary 38.5.1 -/

/-- The exactness hypothesis of Corollary 38.5.1. For bifunctions $F$ from $\mathbb{R}^m$ to
$\mathbb{R}^n$ and $G$ from $\mathbb{R}^n$ to $\mathbb{R}^p$, it says that for every
$u \in \mathbb{R}^m$ and $y \in \mathbb{R}^p$ the functions
$x^* \mapsto \langle u, F^* x^* \rangle$ and $x^* \mapsto -\langle G_*^* x^*, y \rangle$ add
exactly (`ConvexAnalysis.IsExactSum`).

The book's condition is that $\operatorname{ri}(\operatorname{dom} F^*)$ and
$\operatorname{ri}(\operatorname{dom} G_*^*)$ have a point in common. The bifunction $F^*$ is
written as the inverse of $F_*^*$. -/
abbrev IsExactSumCor3851 (F : Bifun (Rn m) (Rn n)) (G : Bifun (Rn n) (Rn k)) : Prop :=
  ∀ (u : Rn m) (y : Rn k), IsExactSum (pairing n)
    (concaveBracket (pairing m) (inverseBifun (lowerAdjointBifun (pairing m) (pairing n) F)) u)
    (fun w => -(bracket (pairing k) (lowerAdjointBifun (pairing n) (pairing k) G) w y))

/-- **Corollary 38.5.1** of [rockafellar1970convex], closedness. Let $F$ be a closed proper convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $G$ a closed proper convex bifunction from
$\mathbb{R}^n$ to $\mathbb{R}^p$ that satisfy the exactness hypothesis
`Rockafellar.IsExactSumCor3851`. Then $GF$ is closed.

**Reading.** The book assumes that $\operatorname{ri}(\operatorname{dom} F^*)$ and
$\operatorname{ri}(\operatorname{dom} G_*^*)$ have a point in common. The statement here assumes
the exactness that Theorem 16.4 derives from this condition.

The proof shows that $GF$ is a lower adjoint. -/
theorem corollary_38_5_1_closed {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hF : ClosedProperConvexFn (graphFn F)) (hG : ClosedProperConvexFn (graphFn G))
    (hex : IsExactSumCor3851 F G) : ClosedConvexBifun (compBifun G F) := by
  refine closedConvexBifun_compBifun (Bu := pairing m) (Bx := pairing n) (By := pairing k) hF hG ?_
  intro u y
  simpa using hex u y

/-- **Corollary 38.5.1** of [rockafellar1970convex], attainment. Under the hypotheses of
`Rockafellar.corollary_38_5_1_closed`, for all $u \in \mathbb{R}^m$ and $y \in \mathbb{R}^p$ the
infimum that defines $((GF)u)(y)$ is attained: there is an $x$ with
$(Fu)(x) + (Gx)(y) = ((GF)u)(y)$.

**Reading.** As in `Rockafellar.corollary_38_5_1_closed`, the relative interior condition of the
book is replaced by exactness. -/
theorem corollary_38_5_1_attained {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hF : ClosedProperConvexFn (graphFn F)) (hG : ClosedProperConvexFn (graphFn G))
    (hex : IsExactSumCor3851 F G) {u : Rn m} {y : Rn k} :
    ∃ x : Rn n, F u x + G x y = compBifun G F u y := by
  refine exists_compBifun_eq (Bu := pairing m) (Bx := pairing n) (By := pairing k) hF hG ?_
  simpa using hex u y

/-- **Corollary 38.5.1** of [rockafellar1970convex], the adjoint. Under the hypotheses of
`Rockafellar.corollary_38_5_1_closed`,
$$(GF)_*^* = \operatorname{cl}(G_*^* F_*^*).$$
This is the formula $(GF)^* = \operatorname{cl}(F^* G^*)$ of the book, written with the convex
bifunctions $H_*^*$. Inversion reverses the order of a product twice, so the product on the
right is in the same order as $GF$.

**Reading.** As in `Rockafellar.corollary_38_5_1_closed`, the relative interior condition of the
book is replaced by exactness. -/
theorem corollary_38_5_1_adjoint {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hF : ClosedProperConvexFn (graphFn F)) (hG : ClosedProperConvexFn (graphFn G))
    (hex : IsExactSumCor3851 F G) :
    lowerAdjointBifun (pairing m) (pairing k) (compBifun G F)
      = convexClBifun (compBifun (lowerAdjointBifun (pairing n) (pairing k) G)
          (lowerAdjointBifun (pairing m) (pairing n) F)) := by
  refine lowerAdjointBifun_compBifun_eq_convexClBifun (Bu := pairing m) (Bx := pairing n)
    (By := pairing k) hF hG ?_
  intro u y
  simpa using hex u y

/-! ### Lemma 38.6 -/

/-- **Lemma 38.6** of [rockafellar1970convex], existence. Let $f$ be a proper function on
$\mathbb{R}^n$, and let $g$ be a function on $\mathbb{R}^n$ that is proper in the concave sense:
finite somewhere and nowhere $+\infty$. If $\langle f, g \rangle$ exists, then
$\langle f^*, g^* \rangle$ exists.

The proof of the book is the chain $-\langle f, g \rangle \le \sup \text{side of } \langle f^*,
g^* \rangle \le \inf \text{side of } \langle f^*, g^* \rangle \le -\langle f, g \rangle$, whose
middle inequality is weak duality. -/
theorem lemma_38_6_exists {f g : Rn n → EReal} (hf : ProperConvex f) (hg : ProperConcave g)
    (h : HasInnerProduct f g) :
    HasInnerProduct (convexConj (pairing n) f) (concaveConj (pairing n) g) := by
  simpa using hasFenchelPairing_convexConj (B := pairing n) hf hg h

/-- **Lemma 38.6** of [rockafellar1970convex]. Let $f$ be a proper function on $\mathbb{R}^n$, and
let $g$ be a function on $\mathbb{R}^n$ that is proper in the concave sense: finite somewhere
and nowhere $+\infty$. If $\langle f, g \rangle$ exists, then
$$\langle f^*, g^* \rangle = -\langle f, g \rangle.$$

The second assertion of the lemma, that $\langle \operatorname{cl} f, \operatorname{cl} g
\rangle$ then exists and equals $\langle f, g \rangle$, is not formalized. The values are the
infimum sides (`Rockafellar.innerProduct`); `Rockafellar.lemma_38_6_exists` gives the existence
of $\langle f^*, g^* \rangle$. -/
theorem lemma_38_6 {f g : Rn n → EReal} (hf : ProperConvex f) (hg : ProperConcave g)
    (h : HasInnerProduct f g) :
    innerProduct (convexConj (pairing n) f) (concaveConj (pairing n) g) = -(innerProduct f g) := by
  simpa using fenchelPairing_convexConj (B := pairing n) hf hg h

/-! ### Theorem 38.7 and Corollary 38.7.1 -/

/-- **Corollary 38.7.1** of [rockafellar1970convex], existence. Let $F$ be a proper bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$, let $f$ be a proper function on $\mathbb{R}^m$, and let
$x^* \in \mathbb{R}^n$. Assume that $f$ and $u \mapsto -\langle Fu, x^* \rangle$ add exactly.
Then $\langle f, F^* x^* \rangle$ exists.

**Reading.** The book's relative interior condition is replaced by exactness, as in Theorem
38.4.

Weak duality gives one inequality, and Theorem 38.4 gives the other. -/
theorem corollary_38_7_1_exists {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : ProperConvex (graphFn F)) (hf : ProperConvex f) {y : Rn n}
    (hex : IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    HasInnerProduct f (dualProgram F y) :=
  hasFenchelPairing_convexAdjointBifun (fun u x => hFp.ne_bot (u, x)) hf hex

/-- **Corollary 38.7.1** of [rockafellar1970convex]. Let $F$ be a proper bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$, let $f$ be a proper function on $\mathbb{R}^m$, and let
$x^* \in \mathbb{R}^n$. Assume that $f$ and $u \mapsto -\langle Fu, x^* \rangle$ add exactly.
Then
$$\langle Ff, x^* \rangle = \langle f, F^* x^* \rangle.$$
That is, an adjoint moves across the inner product. The left-hand side is $(Ff)^*(x^*)$; the
right-hand side is the inner product of $f$ with the concave function $F^* x^*$.

**Reading.** The book's relative interior condition is replaced by exactness, as in Theorem
38.4. -/
theorem corollary_38_7_1 {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal}
    (hFp : ProperConvex (graphFn F)) (hf : ProperConvex f) {y : Rn n}
    (hex : IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    convexConj (pairing n) (imageBifun F f) y = innerProduct f (dualProgram F y) :=
  convexConj_imageBifun_eq_fenchelPairing (fun u x => hFp.ne_bot (u, x)) hf hex

/-- **Theorem 38.7** of [rockafellar1970convex], the first equality. Let $F$ be a proper bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $f$ be a proper function on $\mathbb{R}^m$, and let
$g$ be a function on $\mathbb{R}^n$ with $g > -\infty$ somewhere. Assume that there are
$u_0 \in \mathbb{R}^m$ and $x_0 \in \mathbb{R}^n$ with $(Fu_0)(x_0) < +\infty$,
$f(u_0) < +\infty$ and $g(x_0)$ finite, and that for every $x^* \in \mathbb{R}^n$ the functions
$f$ and $u \mapsto -\langle Fu, x^* \rangle$ add exactly. Then
$$\langle Ff, g^* \rangle = \langle f, F^* g^* \rangle,$$
where $(F^* g^*)(u^*) = \sup_{x^*} \{g^*(x^*) + (F^* x^*)(u^*)\}$. Both sides are infimum sides
(`Rockafellar.innerProduct`).

**Reading.** The book assumes that some $u \in \operatorname{ri}(\operatorname{dom} f) \cap
\operatorname{ri}(\operatorname{dom} F)$ has $\operatorname{ri}(\operatorname{dom}(Fu))$ meeting
$\operatorname{ri}(\operatorname{dom} g)$. The statement here assumes exactness together with a
point at which $f$, $F$ and $g$ are all finite.

The middle member $-\langle f^*, F_* g \rangle$ of the chain of equalities of the book is not
formalized. -/
theorem theorem_38_7 {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal} {g : Rn n → EReal}
    (hFp : ProperConvex (graphFn F)) (hf : ProperConvex f) (hgd : (concaveDom g).Nonempty)
        {u₀ : Rn m}
    {x₀ : Rn n} (hF : F u₀ x₀ ≠ ⊤) (hfu : f u₀ ≠ ⊤) (hgb : g x₀ ≠ ⊥) (hgt : g x₀ ≠ ⊤)
    (hex : ∀ y : Rn n, IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    innerProduct (imageBifun F f) (concaveConj (pairing n) g)
      = innerProduct f (concaveImageBifun (dualProgram F) (concaveConj (pairing n) g)) :=
  fenchelInf_imageBifun_eq_fenchelInf_concaveImageBifun (Bu := pairing m) (Bx := pairing n)
    (fun u x => hFp.ne_bot (u, x)) hf hgd hF hfu hgb hgt hex

/-- **Theorem 38.7** of [rockafellar1970convex], the last equality. Under the hypotheses of
`Rockafellar.theorem_38_7`, except that $g(x_0)$ need not be finite,
$$\sup_x \{g^*(x) - (F_*^* f^*)(x)\} = -\langle Ff, g^* \rangle.$$
The left-hand side is the supremum side of $\langle F_*^* f^*, g \rangle$, and the right-hand
side uses the infimum side of $\langle Ff, g^* \rangle$. Both sides reduce to the same double
extremum.

**Reading.** The book's relative interior condition is replaced by exactness, as in
`Rockafellar.theorem_38_7`. -/
theorem theorem_38_7_third {F : Bifun (Rn m) (Rn n)} {f : Rn m → EReal} {g : Rn n → EReal}
    (hFp : ProperConvex (graphFn F)) (hf : ProperConvex f) (hgd : (concaveDom g).Nonempty)
        {u₀ : Rn m}
    {x₀ : Rn n} (hF : F u₀ x₀ ≠ ⊤) (hfu : f u₀ ≠ ⊤)
    (hex : ∀ y : Rn n, IsExactSum (pairing m) f (fun u => -(bracket (pairing n) F u y))) :
    fenchelSup (pairing n)
        (imageBifun (lowerAdjointBifun (pairing m) (pairing n) F) (convexConj (pairing m) f)) g
      = -(innerProduct (imageBifun F f) (concaveConj (pairing n) g)) := by
  have h := fenchelSup_imageBifun_lowerAdjointBifun_eq_neg (Bu := pairing m) (Bx := pairing n)
    (F := F) (f := f) (g := g) (fun u x => hFp.ne_bot (u, x)) hf hgd hF hfu hex
  rw [flip_pairing] at h
  exact h

/-! ### Corollary 38.7.2 -/

/-- **Corollary 38.7.2** of [rockafellar1970convex], existence. Let $G$ be a proper bifunction from
$\mathbb{R}^n$ to $\mathbb{R}^p$, let $u \in \mathbb{R}^m$ with $Fu$ proper, and let
$y^* \in \mathbb{R}^p$. Assume that $Fu$ and $x \mapsto -\langle Gx, y^* \rangle$ add exactly.
Then $\langle Fu, G^* y^* \rangle$ exists.

**Reading.** The book derives this exactness from its relative interior conditions, by "a pithy
exercise in the calculus of relative interiors" that it leaves to the reader. The statement here
assumes it. -/
theorem corollary_38_7_2_exists {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hGp : ProperConvex (graphFn G)) {u : Rn m} (hFu : ProperConvex (F u)) {z : Rn k}
    (hex : IsExactSum (pairing n) (F u) (fun x => -(bracket (pairing k) G x z))) :
    HasInnerProduct (F u) (dualProgram G z) :=
  hasFenchelPairing_convexAdjointBifun_slice (pairing n) (pairing k)
    (fun x y => hGp.ne_bot (x, y)) hFu hex

/-- **Corollary 38.7.2** of [rockafellar1970convex], the first equality. Let $G$ be a proper
bifunction from $\mathbb{R}^n$ to $\mathbb{R}^p$, let $u \in \mathbb{R}^m$ with $Fu$ proper, and
let $y^* \in \mathbb{R}^p$. Assume that $Fu$ and $x \mapsto -\langle Gx, y^* \rangle$ add
exactly. Then
$$\langle (GF)u, y^* \rangle = \langle Fu, G^* y^* \rangle.$$
This is Corollary 38.7.1 for the function $Fu$, since $(GF)u = G(Fu)$.

**Reading.** The book derives the exactness by "a pithy exercise in the calculus of relative
interiors" that it leaves to the reader. The statement here assumes it. -/
theorem corollary_38_7_2_first {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hGp : ProperConvex (graphFn G)) {u : Rn m} (hFu : ProperConvex (F u)) {z : Rn k}
    (hex : IsExactSum (pairing n) (F u) (fun x => -(bracket (pairing k) G x z))) :
    bracket (pairing k) (compBifun G F) u z = innerProduct (F u) (dualProgram G z) :=
  bracket_compBifun_eq_fenchelPairing (pairing n) (pairing k)
    (fun x y => hGp.ne_bot (x, y)) hFu hex

/-- **Corollary 38.7.2** of [rockafellar1970convex], the second equality. Let $F$ be a proper
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $G$ a bifunction from $\mathbb{R}^n$ to
$\mathbb{R}^p$ such that $GF$ is convex, let $u \in \operatorname{ri}(\operatorname{dom}(GF))$,
and let $y^* \in \mathbb{R}^p$. Assume that for every $u^* \in \mathbb{R}^m$ the functions
$x \mapsto \langle u^*, F_* x \rangle$ and $x \mapsto -\langle Gx, y^* \rangle$ add exactly.
Then
$$\langle (GF)u, y^* \rangle = \langle u, F^* G^* y^* \rangle.$$

**Reading.** The book's relative interior condition is replaced by exactness, as in Theorem
38.5.

The proof combines Corollary 33.2.1 with Theorem 38.5. Unlike the first equality, this one needs
$u$ in the relative interior. -/
theorem corollary_38_7_2_second {F : Bifun (Rn m) (Rn n)} {G : Bifun (Rn n) (Rn k)}
    (hFp : ProperConvex (graphFn F)) (hGF : ConvexBifun (compBifun G F)) {u : Rn m}
    (hu : u ∈ ri (convexDomBifun (compBifun G F))) {z : Rn k}
    (hex : ∀ v : Rn m, IsExactSum (pairing n) (concaveBracket (pairing m) (inverseBifun F) v)
      (fun x => -(bracket (pairing k) G x z))) :
    bracket (pairing k) (compBifun G F) u z
      = concaveBracket (pairing m) (concaveCompBifun (dualProgram G) (dualProgram F)) u z := by
  refine bracket_compBifun_eq_concaveBracket_concaveCompBifun (pairing m) (pairing n) (pairing k)
    (fun u x => hFp.ne_bot (u, x)) hGF hu ?_
  intro v
  simpa using hex v

/-! ### The closing discussion: co-finite bifunctions -/

/-- Let $F$ be a co-finite convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then
$\langle Fu, x^* \rangle$ is finite for all $u \in \mathbb{R}^m$ and $x^* \in \mathbb{R}^n$.
This is Corollary 13.3.1 for the slice $Fu$.

A bifunction is co-finite (`ConvexAnalysis.CofiniteBifun`) if it is convex and every slice $Fu$
is a co-finite convex function: closed, proper, and with recession function $+\infty$ in every
direction $y \neq 0$. -/
theorem cofiniteBifun_bracket_finite {F : Bifun (Rn m) (Rn n)} (hF : CofiniteBifun F) (u : Rn m)
    (y : Rn n) : bracket (pairing n) F u y ≠ ⊥ ∧ bracket (pairing n) F u y ≠ ⊤ :=
  ⟨CofiniteBifun.bracket_ne_bot (Bx := pairing n) hF u y,
    (CofiniteBifun.bracket_lt_top (Bx := pairing n) hF u y).ne⟩

/-- Let $F$ be a convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ such that every slice $Fu$
is closed proper convex. Then $F$ is co-finite if and only if
$\langle Fu, x^* \rangle < +\infty$ for all $u \in \mathbb{R}^m$ and $x^* \in \mathbb{R}^n$. -/
theorem cofinite_iff_forall_bracket_finite {F : Bifun (Rn m) (Rn n)} (hF : ConvexBifun F)
    (hcl : ∀ u, ClosedProperConvexFn (F u)) :
    CofiniteBifun F ↔ ∀ (u : Rn m) (y : Rn n), bracket (pairing n) F u y < ⊤ :=
  ⟨fun h u y => CofiniteBifun.bracket_lt_top (Bx := pairing n) h u y,
    cofiniteBifun_of_forall_bracket_lt_top hF hcl⟩

/-- Let $F$ be a co-finite convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then $\langle
Fu, x^* \rangle = \langle u, F^* x^* \rangle$ for every $u \in \mathbb{R}^m$ and
$x^* \in \mathbb{R}^n$. This is Corollary 33.2.1 with $\operatorname{ri}(\operatorname{dom} F) =
\mathbb{R}^m$. -/
theorem cofiniteBifun_bracket_eq {F : Bifun (Rn m) (Rn n)} (hF : CofiniteBifun F) (u : Rn m)
    (y : Rn n) :
    bracket (pairing n) F u y = concaveBracket (pairing m) (dualProgram F) u y :=
  CofiniteBifun.bracket_eq_concaveBracket_convexAdjointBifun (pairing m) (pairing n) hF u y

/-- If $F_1$ and $F_2$ are co-finite convex bifunctions from $\mathbb{R}^m$ to $\mathbb{R}^n$, then
$F_1 \square F_2$ is co-finite. -/
theorem cofinite_infConvBifun' {F₁ F₂ : Bifun (Rn m) (Rn n)} (hF₁ : CofiniteBifun F₁)
    (hF₂ : CofiniteBifun F₂) : CofiniteBifun (infConvBifun F₁ F₂) :=
  cofiniteBifun_infConvBifun (pairing n) hF₁ hF₂

/-- If $F_1$ and $F_2$ are co-finite convex bifunctions from $\mathbb{R}^m$ to $\mathbb{R}^n$, then
$(F_1 \square F_2)^* = F_1^* \square F_2^*$. The relative interior hypothesis of Theorem 38.2 is
not needed, because the inner products $\langle F_i u, x^* \rangle$ are finite everywhere. -/
theorem cofinite_adjoint_infConvBifun {F₁ F₂ : Bifun (Rn m) (Rn n)} (hF₁ : CofiniteBifun F₁)
    (hF₂ : CofiniteBifun F₂) :
    dualProgram (infConvBifun F₁ F₂) = supConvBifun (dualProgram F₁) (dualProgram F₂) :=
  convexAdjointBifun_infConvBifun_of_cofinite (pairing m) (pairing n) hF₁ hF₂

/-- If $F$ is a co-finite convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $\lambda > 0$,
then $F\lambda$ is co-finite. -/
theorem cofinite_smulRightBifun' {F : Bifun (Rn m) (Rn n)} {l : ℝ} (hF : CofiniteBifun F)
    (hl : 0 < l) : CofiniteBifun (smulRightBifun F l) :=
  cofiniteBifun_smulRightBifun (pairing n) hF hl

/-- Let $F$ be a closed proper convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then $F$ is
co-finite if and only if $\operatorname{dom} F = \mathbb{R}^m$ and
$\operatorname{dom} F^* = \mathbb{R}^n$.

The book cites Theorem 34.2. The proof here does not use the correspondence with
saddle-functions; it applies Corollary 13.3.1 to each slice. -/
theorem cofiniteBifun_of_convexDomBifun_eq_univ' {F : Bifun (Rn m) (Rn n)} (hF : ConvexBifun F)
    (hcl : ClosedConvexBifun F) (hp : ProperConvex (graphFn F)) :
    CofiniteBifun F ↔ convexDomBifun F = univ ∧ concaveDomBifun (dualProgram F) = univ :=
  cofiniteBifun_iff_convexDomBifun_eq_univ (Bu := pairing m) (Bx := pairing n) hF hcl hp

end Rockafellar
