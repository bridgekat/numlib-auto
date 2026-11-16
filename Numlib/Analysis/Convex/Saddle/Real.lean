/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Saddle.Minimax

/-!
# Saddle-points relative to a product set, and real-valued saddle-functions

Let $K : U \times X \to [-\infty, +\infty]$ and let $C \subseteq U$, $D \subseteq X$. A point
$p = (\bar u, \bar x) \in C \times D$ is a saddle-point of $K$ relative to $C \times D$ when $K(u,
\bar x) \le K(\bar u, \bar x) \le K(\bar u, x)$ for all $u \in C$ and $x \in D$
(`ConvexAnalysis.IsSaddlePointOn`). The minimax theory of `Numlib.Analysis.Convex.Saddle.Minimax` is
stated over the whole space. This module transfers it to $C \times D$, and then reads it for a
real-valued $L : U \times X \to \mathbb{R}$. For such $L$ the two iterated extrema become real
suprema and infima, and these need boundedness hypotheses. The presentation follows
[rockafellar1970convex], §36.

The convention is Rockafellar's: the first variable is maximized over $C$, the second minimized over
$D$. A saddle-point in the opposite convention, with the minimum in the first variable and the
maximum in the second, as in Definition 8.6.1 of [han2009theoretical], is
`ConvexAnalysis.IsSaddlePointOn` of the transposed function `fun q => L (q.2, q.1)` on $D \times C$,
by definition. Under this transposition the real-valued statements below are Proposition 8.6.2 and
(8.6.12)–(8.6.14) of [han2009theoretical].

## Main results

* `ConvexAnalysis.isSaddlePointOn_iff_isSaddlePoint_subtype`: a saddle-point of $K$ relative to
  $C \times D$ is a saddle-point of the restriction of $K$ to $C \times D$;
  `ConvexAnalysis.maximin_subtype` and `ConvexAnalysis.minimax_subtype` identify the iterated
  extrema of the restriction with $\sup_{u \in C} \inf_{x \in D} K(u, x)$ and
  $\inf_{x \in D} \sup_{u \in C} K(u, x)$.
* `ConvexAnalysis.isSaddlePointOn_iff_attained`: $p$ is a saddle-point relative to $C \times D$ if
  and only if the outer extrema of $\sup \inf$ and $\inf \sup$ over $C \times D$ are attained at
  $\bar u$ and $\bar x$ and are equal; `ConvexAnalysis.IsSaddlePointOn.biSup_biInf_eq` and
  `ConvexAnalysis.IsSaddlePointOn.biInf_biSup_eq` say that both then equal $K(p)$.
* `ConvexAnalysis.IsSaddlePointOn.isGreatest_image_coe`,
  `ConvexAnalysis.IsSaddlePointOn.isLeast_image_coe`,
  `ConvexAnalysis.IsSaddlePointOn.sSup_image_coe_eq`,
  `ConvexAnalysis.IsSaddlePointOn.sInf_image_coe_eq`: the two partial extrema of a real-valued $L$
  at a saddle-point.
* `ConvexAnalysis.IsSaddlePointOn.isLeast_sSup_coe`,
  `ConvexAnalysis.IsSaddlePointOn.isGreatest_sInf_coe`: at a saddle-point the primal problem
  $\inf_{x \in D} \sup_{u \in C} L(u, x)$ is solved at $\bar x$ and the dual problem
  $\sup_{u \in C} \inf_{x \in D} L(u, x)$ at $\bar u$, both with the value $L(p)$.
* `ConvexAnalysis.IsSaddlePointOn.sInf_sSup_eq_sSup_sInf_coe`: the minimax equality, with no duality
  gap.
* `ConvexAnalysis.isSaddlePointOn_coe_of_isLeast_of_isGreatest`: the converse.

## Implementation notes

* A real-valued $L$ is read in `EReal` through the coercion, as `fun q => (L q : EReal)`.
* The only order facts needed are `EReal.coe_sSup_of_bddAbove` and `EReal.coe_sInf_of_bddBelow` of
  `Numlib.Order.EReal`: the coercion `ℝ → EReal` carries the supremum of a nonempty set of reals
  that is bounded above to the supremum in `EReal`, and similarly for the infimum. With them each
  real statement follows from its `EReal` form instead of being proved again.
* The hypotheses `BddAbove` and `BddBelow` are necessary: `sSup` and `sInf` take the value $0$ on
  unbounded sets of reals. The `EReal` statements need no such hypothesis, because $+\infty$ and
  $-\infty$ are available there.
-/

open Set

namespace ConvexAnalysis

/-! ### Transfer to the subtype product -/

section Subtype

variable {U X : Type*} {K : U × X → EReal} {C : Set U} {D : Set X} {p : U × X}

/-- Let $K : U \times X \to [-\infty, +\infty]$, $C \subseteq U$, $D \subseteq X$, and
$p = (\bar u, \bar x)$ with $\bar u \in C$ and $\bar x \in D$. Then $p$ is a saddle-point of $K$
relative to $C \times D$ if and only if $(\bar u, \bar x)$ is a saddle-point, over all of
$C \times D$, of the restriction of $K$ to $C \times D$.

The restriction is the function `fun q : C × D => K (q.1, q.2)` on the product of the two
subtypes. -/
theorem isSaddlePointOn_iff_isSaddlePoint_subtype (h₁ : p.1 ∈ C) (h₂ : p.2 ∈ D) :
    IsSaddlePointOn K C D p ↔
      IsSaddlePoint (fun q : C × D => K (q.1, q.2)) (⟨p.1, h₁⟩, ⟨p.2, h₂⟩) := by
  simp only [IsSaddlePointOn, IsSaddlePoint, h₁, h₂, true_and, SetCoe.forall]

/-- The $\sup \inf$ of the restriction of $K$ to $C \times D$ is
$$\sup_{u \in C} \inf_{x \in D} K(u, x).$$
-/
theorem maximin_subtype (K : U × X → EReal) (C : Set U) (D : Set X) :
    maximin (fun q : C × D => K (q.1, q.2)) = ⨆ u ∈ C, ⨅ x ∈ D, K (u, x) := by
  rw [maximin_apply, iSup_subtype]
  exact iSup_congr fun u => iSup_congr fun _ => iInf_subtype

/-- The $\inf \sup$ of the restriction of $K$ to $C \times D$ is
$$\inf_{x \in D} \sup_{u \in C} K(u, x).$$
-/
theorem minimax_subtype (K : U × X → EReal) (C : Set U) (D : Set X) :
    minimax (fun q : C × D => K (q.1, q.2)) = ⨅ x ∈ D, ⨆ u ∈ C, K (u, x) := by
  rw [minimax_apply, iInf_subtype]
  exact iInf_congr fun x => iInf_congr fun _ => iSup_subtype

/-- Let $K : U \times X \to [-\infty, +\infty]$, $C \subseteq U$, $D \subseteq X$, and
$p = (\bar u, \bar x)$ with $\bar u \in C$ and $\bar x \in D$. Then $p$ is a saddle-point of $K$
relative to $C \times D$ if and only if the three equations
$$\inf_{x \in D} K(\bar u, x) = \sup_{u \in C} \inf_{x \in D} K(u, x),$$
$$\sup_{u \in C} K(u, \bar x) = \inf_{x \in D} \sup_{u \in C} K(u, x),$$
$$\sup_{u \in C} \inf_{x \in D} K(u, x) = \inf_{x \in D} \sup_{u \in C} K(u, x)$$
hold. That is, the outer supremum of $\sup \inf$ is attained at $\bar u$, the outer infimum of
$\inf \sup$ is attained at $\bar x$, and the two extrema are equal. -/
theorem isSaddlePointOn_iff_attained (h₁ : p.1 ∈ C) (h₂ : p.2 ∈ D) :
    IsSaddlePointOn K C D p ↔
      (⨅ x ∈ D, K (p.1, x)) = (⨆ u ∈ C, ⨅ x ∈ D, K (u, x)) ∧
        (⨆ u ∈ C, K (u, p.2)) = (⨅ x ∈ D, ⨆ u ∈ C, K (u, x)) ∧
          (⨆ u ∈ C, ⨅ x ∈ D, K (u, x)) = ⨅ x ∈ D, ⨆ u ∈ C, K (u, x) := by
  rw [isSaddlePointOn_iff_isSaddlePoint_subtype h₁ h₂, isSaddlePoint_iff_attained,
    hasSaddleValue_iff, maximin_subtype, minimax_subtype, iInf_subtype, iSup_subtype]

/-- If $p = (\bar u, \bar x)$ is a saddle-point of $K$ relative to $C \times D$, then
$\sup_{u \in C} K(u, \bar x) = K(p)$. -/
theorem IsSaddlePointOn.biSup_eq (h : IsSaddlePointOn K C D p) :
    (⨆ u ∈ C, K (u, p.2)) = K p :=
  le_antisymm (iSup₂_le h.2.2.1) (le_iSup₂ (f := fun u (_ : u ∈ C) => K (u, p.2)) p.1 h.1)

/-- If $p = (\bar u, \bar x)$ is a saddle-point of $K$ relative to $C \times D$, then
$\inf_{x \in D} K(\bar u, x) = K(p)$. -/
theorem IsSaddlePointOn.biInf_eq (h : IsSaddlePointOn K C D p) :
    (⨅ x ∈ D, K (p.1, x)) = K p :=
  le_antisymm (iInf₂_le (f := fun x (_ : x ∈ D) => K (p.1, x)) p.2 h.2.1) (le_iInf₂ h.2.2.2)

/-- If $p$ is a saddle-point of $K$ relative to $C \times D$, then
$$\sup_{u \in C} \inf_{x \in D} K(u, x) = K(p).$$
-/
theorem IsSaddlePointOn.biSup_biInf_eq (h : IsSaddlePointOn K C D p) :
    (⨆ u ∈ C, ⨅ x ∈ D, K (u, x)) = K p :=
  ((isSaddlePointOn_iff_attained h.1 h.2.1).1 h).1.symm.trans h.biInf_eq

/-- If $p$ is a saddle-point of $K$ relative to $C \times D$, then
$$\inf_{x \in D} \sup_{u \in C} K(u, x) = K(p).$$
-/
theorem IsSaddlePointOn.biInf_biSup_eq (h : IsSaddlePointOn K C D p) :
    (⨅ x ∈ D, ⨆ u ∈ C, K (u, x)) = K p :=
  ((isSaddlePointOn_iff_attained h.1 h.2.1).1 h).2.1.symm.trans h.biSup_eq

end Subtype

/-! ### Real-valued saddle-functions -/

section Real

variable {U X : Type*} {L : U × X → ℝ} {C : Set U} {D : Set X} {p : U × X}

/-- Let $L : U \times X \to \mathbb{R}$, and let $p = (\bar u, \bar x)$ be a saddle-point of $L$
relative to $C \times D$. Then $L(\cdot, \bar x)$ attains its maximum over $C$ at $\bar u$:
$L(p)$ is the greatest element of $\{L(u, \bar x) \mid u \in C\}$. -/
theorem IsSaddlePointOn.isGreatest_image_coe (h : IsSaddlePointOn (fun q => (L q : EReal)) C D p) :
    IsGreatest ((fun u => L (u, p.2)) '' C) (L p) :=
  ⟨⟨p.1, h.1, rfl⟩, by
    rintro _ ⟨u, hu, rfl⟩
    exact EReal.coe_le_coe_iff.1 (h.2.2.1 u hu)⟩

/-- Let $L : U \times X \to \mathbb{R}$, and let $p = (\bar u, \bar x)$ be a saddle-point of $L$
relative to $C \times D$. Then $L(\bar u, \cdot)$ attains its minimum over $D$ at $\bar x$:
$L(p)$ is the least element of $\{L(\bar u, x) \mid x \in D\}$. -/
theorem IsSaddlePointOn.isLeast_image_coe (h : IsSaddlePointOn (fun q => (L q : EReal)) C D p) :
    IsLeast ((fun x => L (p.1, x)) '' D) (L p) :=
  ⟨⟨p.2, h.2.1, rfl⟩, by
    rintro _ ⟨x, hx, rfl⟩
    exact EReal.coe_le_coe_iff.1 (h.2.2.2 x hx)⟩

/-- Let $L : U \times X \to \mathbb{R}$, and let $p = (\bar u, \bar x)$ be a saddle-point of $L$
relative to $C \times D$. Then $\sup_{u \in C} L(u, \bar x) = L(p)$, with the supremum taken in
$\mathbb{R}$. -/
theorem IsSaddlePointOn.sSup_image_coe_eq (h : IsSaddlePointOn (fun q => (L q : EReal)) C D p) :
    sSup ((fun u => L (u, p.2)) '' C) = L p :=
  h.isGreatest_image_coe.csSup_eq

/-- Let $L : U \times X \to \mathbb{R}$, and let $p = (\bar u, \bar x)$ be a saddle-point of $L$
relative to $C \times D$. Then $\inf_{x \in D} L(\bar u, x) = L(p)$, with the infimum taken in
$\mathbb{R}$. -/
theorem IsSaddlePointOn.sInf_image_coe_eq (h : IsSaddlePointOn (fun q => (L q : EReal)) C D p) :
    sInf ((fun x => L (p.1, x)) '' D) = L p :=
  h.isLeast_image_coe.csInf_eq

/-- **The primal problem is solved at a saddle-point.** Let $L : U \times X \to \mathbb{R}$ be such
that $L(\cdot, x)$ is bounded above on $C$ for every $x \in D$, and let $p = (\bar u, \bar x)$
be a saddle-point of $L$ relative to $C \times D$. Then the function
$x \mapsto \sup_{u \in C} L(u, x)$ attains its least value over $D$ at $\bar x$, and this value
is $L(p)$.

This is `ConvexAnalysis.IsSaddlePointOn.biInf_biSup_eq` read in $\mathbb{R}$. The boundedness
makes each `sSup` the real supremum. -/
theorem IsSaddlePointOn.isLeast_sSup_coe (h : IsSaddlePointOn (fun q => (L q : EReal)) C D p)
    (hbdd : ∀ x ∈ D, BddAbove ((fun u => L (u, x)) '' C)) :
    IsLeast ((fun x => sSup ((fun u => L (u, x)) '' C)) '' D) (L p) := by
  have hcoe : ∀ x ∈ D, ((sSup ((fun u => L (u, x)) '' C) : ℝ) : EReal) =
      ⨆ u ∈ C, ((L (u, x) : ℝ) : EReal) := fun x hx => by
    rw [EReal.coe_sSup_of_bddAbove ((nonempty_of_mem h.1).image _) (hbdd x hx), ← sSup_image,
      ← sSup_image,
      image_image]
  refine ⟨⟨p.2, h.2.1, h.sSup_image_coe_eq⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  refine EReal.coe_le_coe_iff.1 ?_
  rw [hcoe x hx, ← h.biInf_biSup_eq]
  exact iInf₂_le (f := fun x (_ : x ∈ D) => ⨆ u ∈ C, ((L (u, x) : ℝ) : EReal)) x hx

/-- **The dual problem is solved at a saddle-point.** Let $L : U \times X \to \mathbb{R}$ be such
that $L(u, \cdot)$ is bounded below on $D$ for every $u \in C$, and let $p = (\bar u, \bar x)$
be a saddle-point of $L$ relative to $C \times D$. Then the function
$u \mapsto \inf_{x \in D} L(u, x)$ attains its greatest value over $C$ at $\bar u$, and this
value is $L(p)$.

With `ConvexAnalysis.IsSaddlePointOn.isLeast_sSup_coe` this gives the minimax equality
`ConvexAnalysis.IsSaddlePointOn.sInf_sSup_eq_sSup_sInf_coe`. -/
theorem IsSaddlePointOn.isGreatest_sInf_coe (h : IsSaddlePointOn (fun q => (L q : EReal)) C D p)
    (hbdd : ∀ u ∈ C, BddBelow ((fun x => L (u, x)) '' D)) :
    IsGreatest ((fun u => sInf ((fun x => L (u, x)) '' D)) '' C) (L p) := by
  have hcoe : ∀ u ∈ C, ((sInf ((fun x => L (u, x)) '' D) : ℝ) : EReal) =
      ⨅ x ∈ D, ((L (u, x) : ℝ) : EReal) := fun u hu => by
    rw [EReal.coe_sInf_of_bddBelow ((nonempty_of_mem h.2.1).image _) (hbdd u hu), ← sInf_image,
      ← sInf_image,
      image_image]
  refine ⟨⟨p.1, h.1, h.sInf_image_coe_eq⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  refine EReal.coe_le_coe_iff.1 ?_
  rw [hcoe u hu, ← h.biSup_biInf_eq]
  exact le_iSup₂ (f := fun u (_ : u ∈ C) => ⨅ x ∈ D, ((L (u, x) : ℝ) : EReal)) u hu

/-- **No duality gap.** Let $L : U \times X \to \mathbb{R}$ be such that $L(\cdot, x)$ is bounded
above on $C$ for every $x \in D$ and $L(u, \cdot)$ is bounded below on $D$ for every $u \in C$.
If $L$ has a saddle-point $p$ relative to $C \times D$, then
$$\inf_{x \in D} \sup_{u \in C} L(u, x) = \sup_{u \in C} \inf_{x \in D} L(u, x).$$

The statement gives only the equality. Both values are $L(p)$, by
`ConvexAnalysis.IsSaddlePointOn.isLeast_sSup_coe` and
`ConvexAnalysis.IsSaddlePointOn.isGreatest_sInf_coe`. -/
theorem IsSaddlePointOn.sInf_sSup_eq_sSup_sInf_coe
    (h : IsSaddlePointOn (fun q => (L q : EReal)) C D p)
    (hbddA : ∀ x ∈ D, BddAbove ((fun u => L (u, x)) '' C))
    (hbddB : ∀ u ∈ C, BddBelow ((fun x => L (u, x)) '' D)) :
    sInf ((fun x => sSup ((fun u => L (u, x)) '' C)) '' D) =
      sSup ((fun u => sInf ((fun x => L (u, x)) '' D)) '' C) :=
  (h.isLeast_sSup_coe hbddA).csInf_eq.trans (h.isGreatest_sInf_coe hbddB).csSup_eq.symm

/-- **The converse.** Let $L : U \times X \to \mathbb{R}$ and $p = (\bar u, \bar x)$ with
$\bar u \in C$ and $\bar x \in D$. Assume that $L(\cdot, \bar x)$ is bounded above on $C$ and
$L(\bar u, \cdot)$ is bounded below on $D$. If the primal objective
$x \mapsto \sup_{u \in C} L(u, x)$ attains its minimum over $D$ at $\bar x$, the dual objective
$u \mapsto \inf_{x \in D} L(u, x)$ attains its maximum over $C$ at $\bar u$, and
$$\inf_{x \in D} \sup_{u \in C} L(u, x) = \sup_{u \in C} \inf_{x \in D} L(u, x),$$
then $p$ is a saddle-point of $L$ relative to $C \times D$.

The suprema and infima are the real `sSup` and `sInf`, which take the value $0$ on a set that is
not bounded. The boundedness hypotheses are needed only at $p$, to read the two extremal values
as real numbers. -/
theorem isSaddlePointOn_coe_of_isLeast_of_isGreatest (h₁ : p.1 ∈ C) (h₂ : p.2 ∈ D)
    (hbddA : BddAbove ((fun u => L (u, p.2)) '' C)) (hbddB : BddBelow ((fun x => L (p.1, x)) '' D))
    (hleast : IsLeast ((fun x => sSup ((fun u => L (u, x)) '' C)) '' D)
      (sSup ((fun u => L (u, p.2)) '' C)))
    (hgreatest : IsGreatest ((fun u => sInf ((fun x => L (u, x)) '' D)) '' C)
      (sInf ((fun x => L (p.1, x)) '' D)))
    (heq : sInf ((fun x => sSup ((fun u => L (u, x)) '' C)) '' D) =
      sSup ((fun u => sInf ((fun x => L (u, x)) '' D)) '' C)) :
    IsSaddlePointOn (fun q => (L q : EReal)) C D p := by
  have hval : sSup ((fun u => L (u, p.2)) '' C) = sInf ((fun x => L (p.1, x)) '' D) := by
    rw [← hleast.csInf_eq, heq, hgreatest.csSup_eq]
  refine (isSaddlePointOn_iff_biSup_eq_biInf h₁ h₂).2 ?_
  have hS := EReal.coe_sSup_of_bddAbove ((nonempty_of_mem h₁).image _) hbddA
  have hI := EReal.coe_sInf_of_bddBelow ((nonempty_of_mem h₂).image _) hbddB
  simp only [iSup_image] at hS
  simp only [iInf_image] at hI
  rw [← hS, ← hI, hval]

end Real

end ConvexAnalysis
