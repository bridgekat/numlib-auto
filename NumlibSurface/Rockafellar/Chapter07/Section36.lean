/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Saddle.Subdifferential
import NumlibSurface.Rockafellar.Chapter07.Section33

/-!
# Rockafellar, Section 36: Minimax problems

This module formalizes Section 36 of [rockafellar1970convex] (pages 379–387). For a function $K :
\mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$ the section compares the two iterated
extrema $\sup_u \inf_v K(u, v)$ and $\inf_v \sup_u K(u, v)$. The first is never larger than the
second (Lemma 36.1). When they are equal, their common value is the **saddle-value**, and a
**saddle-point** is a pair $(\bar u, \bar v)$ with $K(u, \bar v) \le K(\bar u, \bar v) \le K(\bar u,
v)$ for all $u$ and $v$. The section reduces a minimax problem on $C \times D$ to one on all of
$\mathbb{R}^m \times \mathbb{R}^n$ (Theorem 36.3), shows that equivalent saddle-functions have the
same minimax data (Theorem 36.4), introduces the inverse $F_*$ of a bifunction $F$, identifies the
Lagrangians of closed convex programs with the upper closed concave-convex functions (Theorem 36.5),
and states the Kuhn–Tucker condition $(0, 0) \in \partial L(\bar u^*, \bar x)$ as a saddle-point
condition (Theorem 36.6).

All seven numbered results of Section 36 are formalized: Lemmas 36.1 and 36.2, Theorems 36.3–36.6
and Corollary 36.3.1. The proofs specialize `Numlib.Analysis.Convex.Saddle.Minimax` and
`Numlib.Analysis.Convex.Saddle.Subdifferential`. Supporting results unfold the definitions
(`Rockafellar.hasSaddleValue_iff_maximin_eq`, `Rockafellar.isSaddlePoint_iff_forall`), restrict the
outer extrema to the effective domains (`Rockafellar.maximin_restricted`,
`Rockafellar.minimax_restricted`), give the algebra of $F_*$ (`Rockafellar.inverseBifun_involutive`,
`Rockafellar.concaveAdjointBifun_inverseBifun`), and translate $(0, 0) \in \partial K(u, v)$ into a
saddle-point condition (`Rockafellar.zero_mem_saddleSubdifferential_iff_isSaddlePoint`,
`Rockafellar.kuhnTucker_condition_iff`).

## Main definitions

* Section 36, `Rockafellar.inverseBifunBracket`: the function
  $(u^*, x) \mapsto \langle u^*, F_* x \rangle$, which is the Lagrangian of the convex program
  associated with $F$.

## Main results

* Lemma 36.1, `Rockafellar.lemma_36_1`, `Rockafellar.lemma_36_1_on`: $\sup_u \inf_v K(u, v) \le
  \inf_v \sup_u K(u, v)$ for every $K$, also over arbitrary subsets $C$ and $D$.
* Lemma 36.2, `Rockafellar.lemma_36_2`, `Rockafellar.lemma_36_2_saddleValue`: $(\bar u, \bar v)$ is
  a saddle-point if and only if both outer extrema are attained there and the saddle-value exists;
  then both extrema equal $K(\bar u, \bar v)$.
* Theorem 36.3, `Rockafellar.theorem_36_3_maximin`, `Rockafellar.theorem_36_3_minimax`,
  `Rockafellar.theorem_36_3_saddlePoint`: for a closed proper concave-convex $K$, the minimax
  problem on $\mathbb{R}^m \times \mathbb{R}^n$ has the same iterated extrema and the same
  saddle-points as the problem on $\operatorname{dom}_1 K \times \operatorname{dom}_2 K$.
* Corollary 36.3.1, `Rockafellar.corollary_36_3_1_mem_dom`, `Rockafellar.corollary_36_3_1_finite`: a
  saddle-point of a proper saddle-function lies in $\operatorname{dom} K$, and the saddle-value is
  then finite.
* Theorem 36.4, `Rockafellar.theorem_36_4_maximin`, `Rockafellar.theorem_36_4_minimax`,
  `Rockafellar.theorem_36_4_hasSaddleValue`, `Rockafellar.theorem_36_4_saddlePoint`: equivalent
  saddle-functions have the same iterated extrema, the same saddle-value and the same saddle-points.
* Theorem 36.5, `Rockafellar.theorem_36_5`, `Rockafellar.theorem_36_5_upperClosed`,
  `Rockafellar.theorem_36_5_unique`: the Lagrangians of the convex programs associated with closed
  convex bifunctions are exactly the upper closed concave-convex functions, and each such function
  is the Lagrangian of exactly one such bifunction.
* Theorem 36.6, `Rockafellar.theorem_36_6_stronglyConsistent`,
  `Rockafellar.theorem_36_6_strictlyConsistent`, `Rockafellar.theorem_36_6_polyhedral`,
  `Rockafellar.theorem_36_6_kuhnTucker`: under each of three constraint qualifications, $\bar x$ is
  an optimal solution if and only if $(0, 0) \in \partial L(\bar u^*, \bar x)$ for some $\bar u^*$,
  and the vectors $\bar u^*$ that occur are the Kuhn–Tucker vectors.

## Conventions

* From this section to the end of the book, minimization takes place in the convex argument and
  maximization in the concave argument. For $K(u, v)$ concave in $u$ and convex in $v$,
  `ConvexAnalysis.maximin K` and `ConvexAnalysis.minimax K` are $\sup_u \inf_v K(u, v)$ and
  $\inf_v \sup_u K(u, v)$, respectively, and Lemma 36.1 is the inequality between these two extrema.
  A saddle-point maximizes in the first argument and minimizes in the second; it is
  `ConvexAnalysis.IsSaddlePoint`. Theorems 36.3–36.6 and all results of Section 37 are false as
  printed under the opposite convention.
* `ConvexAnalysis.HasSaddleValue K` is the equality of the two iterated extrema. It does not say
  that the common value is finite; finiteness is a separate conclusion, drawn in Corollary 36.3.1 as
  in the book.

## Deviations from the source

* **Lemma 36.1** (generalization). The book assumes that $C$ and $D$ are non-empty.
  `Rockafellar.lemma_36_1_on` holds for arbitrary subsets.
* **Corollary 36.3.1** (generalization). The book assumes a closed proper saddle-function. The
  statements here assume only that $K$ is proper. See `Rockafellar.corollary_36_3_1_mem_dom`.
* **Theorem 36.4** (generalization). The equivalence of saddle values and saddle points,
  and equality of the individual iterated extrema, hold whenever the partial closures
  coincide. Lean omits the saddle-function hypothesis.
* **Theorem 36.6**, multiplier characterization (generalization). For a given optimal
  solution, the zero-subgradient test characterizes the multiplier vectors without
  a constraint qualification.

## Not formalized

* **Lemma 36.2** for a function on a general product $C \times D$. Only the case
  $C \times D = \mathbb{R}^m \times \mathbb{R}^n$ is formalized; `ConvexAnalysis.IsSaddlePointOn`
  gives the relative notion of saddle-point.
-/

namespace Rockafellar

open ConvexAnalysis

/-! ### The saddle-value and the saddle-point -/

section Defs

variable {m n : ℕ}

/-- Let $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$. The **saddle-value** of $K$
exists if and only if
$$\sup_{u} \inf_{v} K(u, v) = \inf_{v} \sup_{u} K(u, v).$$
The saddle-value is then this common value, which can be infinite. -/
theorem hasSaddleValue_iff_maximin_eq (K : Rn m × Rn n → EReal) :
    HasSaddleValue K ↔ (⨆ u : Rn m, ⨅ v : Rn n, K (u, v)) = ⨅ v : Rn n, ⨆ u : Rn m, K (u, v) :=
  Iff.rfl

/-- Let $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$. A pair $(\bar u, \bar v)$ is
a **saddle-point** of $K$ if and only if
$$K(u, \bar v) \le K(\bar u, \bar v) \le K(\bar u, v) \qquad \text{for all } u \in \mathbb{R}^m,
  v \in \mathbb{R}^n.$$
$K$ is maximized in the first argument and minimized in the second. -/
theorem isSaddlePoint_iff_forall (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    IsSaddlePoint K p ↔ ∀ u : Rn m, ∀ v : Rn n, K (u, p.2) ≤ K p ∧ K p ≤ K (p.1, v) :=
  ⟨fun h u v => ⟨h.1 u, h.2 v⟩, fun h => ⟨fun u => (h u 0).1, fun v => (h 0 v).2⟩⟩

end Defs

/-! ### Lemma 36.1 -/

section Lemma361

variable {m n : ℕ}

/-- **Lemma 36.1** of [rockafellar1970convex]. For every $K : \mathbb{R}^m \times \mathbb{R}^n \to
[-\infty, +\infty]$,
$$\sup_{u} \inf_{v} K(u, v) \le \inf_{v} \sup_{u} K(u, v).$$
No hypothesis on $K$ is needed. -/
theorem lemma_36_1 (K : Rn m × Rn n → EReal) : maximin K ≤ minimax K :=
  maximin_le_minimax K

/-- **Lemma 36.1** of [rockafellar1970convex], for subsets. Let $C \subseteq \mathbb{R}^m$,
$D \subseteq \mathbb{R}^n$ and $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$.
Then
$$\sup_{u \in C} \inf_{v \in D} K(u, v) \le \inf_{v \in D} \sup_{u \in C} K(u, v).$$

**Generalization.** The book assumes that $C$ and $D$ are non-empty. The inequality holds
without this assumption, with $\sup \emptyset = -\infty$ and $\inf \emptyset = +\infty$. -/
theorem lemma_36_1_on (C : Set (Rn m)) (D : Set (Rn n)) (K : Rn m × Rn n → EReal) :
    (⨆ u ∈ C, ⨅ v ∈ D, K (u, v)) ≤ ⨅ v ∈ D, ⨆ u ∈ C, K (u, v) :=
  iSup₂_le fun u hu => le_iInf₂ fun v hv =>
    (iInf₂_le (f := fun v (_ : v ∈ D) => K (u, v)) v hv).trans
      (le_iSup₂ (f := fun u (_ : u ∈ C) => K (u, v)) u hu)

end Lemma361

/-! ### Lemma 36.2 -/

section Lemma362

variable {m n : ℕ} {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- **Lemma 36.2** of [rockafellar1970convex]. Let $K : \mathbb{R}^m \times \mathbb{R}^n \to
[-\infty, +\infty]$ and $(\bar u, \bar v) \in \mathbb{R}^m \times \mathbb{R}^n$. Then
$(\bar u, \bar v)$ is a saddle-point of $K$ if and only if
$$\inf_{v} K(\bar u, v) = \sup_{u} \inf_{v} K(u, v), \qquad \sup_{u} K(u, \bar v) = \inf_{v}
  \sup_{u} K(u, v),$$
and the saddle-value of $K$ exists. That is, the supremum in $\sup \inf$ is attained at
$\bar u$, the infimum in $\inf \sup$ is attained at $\bar v$, and the two extrema are equal.

The book states the lemma for a function on a product $C \times D$. The statement here is the
case $C \times D = \mathbb{R}^m \times \mathbb{R}^n$; the relative form is not formalized.
`ConvexAnalysis.IsSaddlePointOn` gives the relative notion of saddle-point.

**Reading.** Specializes the relative equivalence to the whole product of Euclidean spaces.
-/
theorem lemma_36_2 (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    IsSaddlePoint K p ↔
      (⨅ v : Rn n, K (p.1, v)) = maximin K ∧ (⨆ u : Rn m, K (u, p.2)) = minimax K ∧
        HasSaddleValue K :=
  isSaddlePoint_iff_attained

/-- **Lemma 36.2** of [rockafellar1970convex], the last sentence. If $(\bar u, \bar v)$ is a
saddle-point of $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, then
$$\sup_{u} \inf_{v} K(u, v) = K(\bar u, \bar v) = \inf_{v} \sup_{u} K(u, v).$$
-/
theorem lemma_36_2_saddleValue (h : IsSaddlePoint K p) :
    maximin K = K p ∧ minimax K = K p :=
  ⟨IsSaddlePoint.maximin_eq h, IsSaddlePoint.minimax_eq h⟩

end Lemma362

/-! ### The reduction to the whole space -/

section Extension

variable {m n : ℕ}

/-- For every $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, the outer supremum in
$\sup \inf$ can be restricted to $\operatorname{dom}_1 K$:
$$\sup_{u} \inf_{v} K(u, v) = \sup_{u \in \operatorname{dom}_1 K} \inf_{v} K(u, v).$$
This holds because $\inf_v K(u, v) = -\infty$ for $u \notin \operatorname{dom}_1 K$. The book
uses it where it extends a finite function on $C \times D$ by $\pm\infty$.

Here $\operatorname{dom}_1 K$ (`ConvexAnalysis.dom₁`) is the set of $u$ with $K(u, v) > -\infty$
for all $v$. -/
theorem maximin_restricted (K : Rn m × Rn n → EReal) :
    maximin K = ⨆ u ∈ dom₁ K, ⨅ v : Rn n, K (u, v) :=
  maximin_eq_biSup_dom₁ K

/-- For every $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, the outer infimum in
$\inf \sup$ can be restricted to $\operatorname{dom}_2 K$:
$$\inf_{v} \sup_{u} K(u, v) = \inf_{v \in \operatorname{dom}_2 K} \sup_{u} K(u, v).$$

Here $\operatorname{dom}_2 K$ (`ConvexAnalysis.dom₂`) is the set of $v$ with $K(u, v) < +\infty$
for all $u$. -/
theorem minimax_restricted (K : Rn m × Rn n → EReal) :
    minimax K = ⨅ v ∈ dom₂ K, ⨆ u : Rn m, K (u, v) :=
  minimax_eq_biInf_dom₂ K

end Extension

/-! ### Theorem 36.3 -/

section Thm363

variable {m n : ℕ} {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- **Theorem 36.3** of [rockafellar1970convex], the first displayed equation. Let $K : \mathbb{R}^m
\times \mathbb{R}^n \to [-\infty, +\infty]$ be a closed proper concave-convex function, and let
$C = \operatorname{dom}_1 K$ and $D = \operatorname{dom}_2 K$. Then
$$\sup_{u \in \mathbb{R}^m} \inf_{v \in \mathbb{R}^n} K(u, v) = \sup_{u \in C} \inf_{v \in D}
  K(u, v).$$

Closed is `ConvexAnalysis.ClosedSaddleFn`: $\operatorname{cl}_1 K$ and $\operatorname{cl}_2 K$
are both equivalent to $K$. Proper is `ConvexAnalysis.ProperSaddleFn`: $C$ and $D$ are
non-empty. -/
theorem theorem_36_3_maximin (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hp : ProperSaddleFn K) :
    maximin K = ⨆ u ∈ dom₁ K, ⨅ v ∈ dom₂ K, K (u, v) :=
  maximin_eq_biSup_biInf hK (ClosedSaddleFn.saddleStructure hcl hK hp) hp

/-- **Theorem 36.3** of [rockafellar1970convex], the second displayed equation. Let $K :
\mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$ be a closed proper concave-convex
function, and let $C = \operatorname{dom}_1 K$ and $D = \operatorname{dom}_2 K$. Then
$$\inf_{v \in \mathbb{R}^n} \sup_{u \in \mathbb{R}^m} K(u, v) = \inf_{v \in D} \sup_{u \in C}
  K(u, v).$$
With `Rockafellar.theorem_36_3_maximin`, the minimax problems on
$\mathbb{R}^m \times \mathbb{R}^n$ and on $C \times D$ have the same pair of iterated extrema. -/
theorem theorem_36_3_minimax (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hp : ProperSaddleFn K) :
    minimax K = ⨅ v ∈ dom₂ K, ⨆ u ∈ dom₁ K, K (u, v) :=
  minimax_eq_biInf_biSup hK (ClosedSaddleFn.saddleStructure hcl hK hp) hp

/-- **Theorem 36.3** of [rockafellar1970convex], the last sentence. Let $K : \mathbb{R}^m \times
\mathbb{R}^n \to [-\infty, +\infty]$ be a closed proper concave-convex function, and let
$C = \operatorname{dom}_1 K$ and $D = \operatorname{dom}_2 K$. Then $(\bar u, \bar v)$ is a
saddle-point of $K$ if and only if it is a saddle-point of $K$ relative to $C \times D$, that
is, $\bar u \in C$, $\bar v \in D$ and $K(u, \bar v) \le K(\bar u, \bar v) \le K(\bar u, v)$ for
all $u \in C$ and $v \in D$. -/
theorem theorem_36_3_saddlePoint (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hp : ProperSaddleFn K) :
    IsSaddlePoint K p ↔ IsSaddlePointOn K (dom₁ K) (dom₂ K) p :=
  isSaddlePoint_iff_isSaddlePointOn_dom hK (ClosedSaddleFn.saddleStructure hcl hK hp) hp

end Thm363

/-! ### Corollary 36.3.1 -/

section Cor3631

variable {m n : ℕ} {K : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- **Corollary 36.3.1** of [rockafellar1970convex], the first assertion. Let $K : \mathbb{R}^m
\times \mathbb{R}^n \to [-\infty, +\infty]$ be proper. Then every saddle-point of $K$ lies in
$\operatorname{dom} K = \operatorname{dom}_1 K \times \operatorname{dom}_2 K$.

**Generalization.** The book states the corollary for a closed proper saddle-function. The
statement here assumes neither closedness nor concave-convexity. -/
theorem corollary_36_3_1_mem_dom (hp : ProperSaddleFn K) (h : IsSaddlePoint K p) :
    p ∈ domSaddle K :=
  IsSaddlePoint.mem_domSaddle hp h

/-- **Corollary 36.3.1** of [rockafellar1970convex], the second assertion. Let $K : \mathbb{R}^m
\times \mathbb{R}^n \to [-\infty, +\infty]$ be proper and have a saddle-point. Then
$\sup_u \inf_v K(u, v)$ is finite. By Lemma 36.2 this number is the saddle-value of $K$.

**Generalization.** The book states the corollary for a closed proper saddle-function. The
statement here assumes neither closedness nor concave-convexity. -/
theorem corollary_36_3_1_finite (hp : ProperSaddleFn K) (h : IsSaddlePoint K p) :
    ∃ r : ℝ, maximin K = (r : EReal) :=
  IsSaddlePoint.exists_maximin_eq_coe hp h

end Cor3631

/-! ### Theorem 36.4 -/

section Thm364

variable {m n : ℕ} {K L : Rn m × Rn n → EReal} {p : Rn m × Rn n}

/-- **Theorem 36.4** of [rockafellar1970convex], the supremum of the infimum. Let $K, L :
\mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$ be equivalent, that is,
$\operatorname{cl}_1 K = \operatorname{cl}_1 L$ and
$\operatorname{cl}_2 K = \operatorname{cl}_2 L$. Then
$$\sup_{u} \inf_{v} K(u, v) = \sup_{u} \inf_{v} L(u, v).$$

The equivalence is `ConvexAnalysis.SaddleEquiv`; no concavity or convexity of $K$ and $L$ is
assumed. The proof uses that two concave functions with the same closure have the same supremum.

**Reading.** Equal partial closures imply equal maximin for arbitrary functions.
-/
theorem theorem_36_4_maximin (h : SaddleEquiv K L) : maximin K = maximin L :=
  SaddleEquiv.maximin_eq h

/-- **Theorem 36.4** of [rockafellar1970convex], the infimum of the supremum. Let $K, L :
\mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$ be equivalent. Then
$$\inf_{v} \sup_{u} K(u, v) = \inf_{v} \sup_{u} L(u, v).$$

**Reading.** Equal partial closures imply equal minimax for arbitrary functions.
-/
theorem theorem_36_4_minimax (h : SaddleEquiv K L) : minimax K = minimax L :=
  SaddleEquiv.minimax_eq h

/-- **Theorem 36.4** of [rockafellar1970convex], the saddle-value. Let $K, L : \mathbb{R}^m \times
\mathbb{R}^n \to [-\infty, +\infty]$ be equivalent. Then the saddle-value of $K$ exists if and
only if the saddle-value of $L$ exists.

**Reading.** Existence of a saddle value is preserved by equivalence even without a saddle-function
hypothesis.
-/
theorem theorem_36_4_hasSaddleValue (h : SaddleEquiv K L) :
    HasSaddleValue K ↔ HasSaddleValue L :=
  SaddleEquiv.hasSaddleValue_iff h

/-- **Theorem 36.4** of [rockafellar1970convex], the saddle-points. Let $K, L : \mathbb{R}^m \times
\mathbb{R}^n \to [-\infty, +\infty]$ be equivalent. Then $K$ and $L$ have the same
saddle-points.

So minimax theory is a theory of equivalence classes of saddle-functions, and by Theorem 36.5 a
theory of convex programs.

**Reading.** Saddle points are preserved by equivalence of arbitrary functions.
-/
theorem theorem_36_4_saddlePoint (h : SaddleEquiv K L) :
    IsSaddlePoint K p ↔ IsSaddlePoint L p :=
  SaddleEquiv.isSaddlePoint_iff h

end Thm364

/-! ### The inverse bifunction $F_*$ -/

section Inverse

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- Let $F$ be a convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then its inverse $F_*$,
given by $(F_* x)(u) = -(Fu)(x)$, is a concave bifunction from $\mathbb{R}^n$ to $\mathbb{R}^m$. -/
theorem concaveBifun_inverseBifun (hF : ConvexBifun F) : ConcaveBifun (inverseBifun F) :=
  ConvexAnalysis.concaveBifun_inverseBifun hF

/-- The inverse operation is involutory: $(F_*)_* = F$ for every bifunction $F$ from $\mathbb{R}^m$
to $\mathbb{R}^n$. -/
theorem inverseBifun_involutive (F : Bifun (Rn m) (Rn n)) :
    inverseBifun (inverseBifun F) = F :=
  inverseBifun_inverseBifun F

/-- The inverse operation commutes with the adjoint: for every bifunction $F$ from $\mathbb{R}^m$ to
$\mathbb{R}^n$, $(F_*)^* = (F^*)_*$, so one can write $F_*^*$ for both. On the left is the
adjoint of the concave bifunction $F_*$ (`ConvexAnalysis.concaveAdjointBifun`); on the right is
the inverse of the adjoint $F^*$ (`Rockafellar.dualProgram`).

The book compares this with the identity $(A^{-1})^* = (A^*)^{-1}$ for a non-singular linear map
$A$. -/
theorem concaveAdjointBifun_inverseBifun (F : Bifun (Rn m) (Rn n)) :
    concaveAdjointBifun (pairing m) (pairing n) (inverseBifun F)
      = inverseBifun (dualProgram F) := by
  have hlow : lowerAdjointBifun (pairing m) (pairing n) F = inverseBifun (dualProgram F) := rfl
  have h := lowerAdjointBifun_eq_concaveAdjointBifun (pairing m) (pairing n) F
  rw [hlow] at h
  simpa only [flip_pairing] using h.symm

/-- **Section 36** of [rockafellar1970convex], the bracket of the inverse bifunction. For a
bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, this is the function
$$(u^*, x) \mapsto \langle u^*, F_* x \rangle$$
on $\mathbb{R}^m \times \mathbb{R}^n$, where $\langle u^*, F_* x \rangle$ is the concave
conjugate of the function $F_* x$ at $u^*$. It is the Lagrangian of the program associated with
$F$ (`Rockafellar.saddleLagrangian_eq_inverseBifunBracket`). By Theorem 37.1 it is also the
upper conjugate $\bar K^*$ of every member $K$ of the class $\Omega(F)$.

The definition is `Rockafellar.concaveBifunBracket` for the bifunction
`ConvexAnalysis.inverseBifun F`. -/
noncomputable abbrev inverseBifunBracket (F : Bifun (Rn m) (Rn n)) : Rn m × Rn n → EReal :=
  concaveBifunBracket (inverseBifun F)

/-- For a bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$ and
$(u^*, x) \in \mathbb{R}^m \times \mathbb{R}^n$,
$$\langle u^*, F_* x \rangle = \inf_{u} \{\langle u^*, u \rangle - (F_* x)(u)\} = \inf_{u}
  \{\langle u^*, u \rangle + (Fu)(x)\}.$$
This is the defining formula of the book. -/
theorem inverseBifunBracket_apply (F : Bifun (Rn m) (Rn n)) (p : Rn m × Rn n) :
    inverseBifunBracket F p = ⨅ u : Rn m, ((pairing m p.1 u : ℝ) : EReal) - inverseBifun F p.2 u :=
  rfl

end Inverse

/-! ### Theorem 36.5 -/

section Thm365

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {L : Rn m × Rn n → EReal}

/-- For a bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, the Lagrangian $L(u^*, x) = \inf_u
\{\langle u, u^* \rangle + (Fu)(x)\}$ of the program associated with $F$ is the function
$(u^*, x) \mapsto \langle u^*, F_* x \rangle$. The only step that does not hold by definition is
the symmetry of the Euclidean inner product. -/
theorem saddleLagrangian_eq_inverseBifunBracket (F : Bifun (Rn m) (Rn n)) :
    saddleLagrangian (pairing m) F = inverseBifunBracket F := by
  funext p
  rw [saddleLagrangian_apply, lagrangian_apply, inverseBifunBracket_apply]
  refine iInf_congr fun u => ?_
  rw [inverseBifun_apply, pairing_comm, sub_eq_add_neg, neg_neg]

/-- The Lagrangian of the program associated with a convex bifunction $F$ from $\mathbb{R}^m$ to
$\mathbb{R}^n$ is concave-convex: concave in $u^* \in \mathbb{R}^m$ and convex in
$x \in \mathbb{R}^n$. -/
theorem saddleLagrangian_concaveConvex (hF : ConvexBifun F) :
    ConcaveConvexFn (saddleLagrangian (pairing m) F) :=
  concaveConvexFn_saddleLagrangian (pairing m) hF

/-- **Theorem 36.5** of [rockafellar1970convex]. A function $L : \mathbb{R}^m \times \mathbb{R}^n
\to [-\infty, +\infty]$ is the Lagrangian of the convex program associated with some closed
convex bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$ if and only if $L$ is an upper
closed concave-convex function.

Upper closed is `ConvexAnalysis.UpperClosedFn`: $\operatorname{cl}_1 \operatorname{cl}_2 L = L$.
So the minimax problems of this section and the closed convex programs of Sections 29 and 30 are
the same objects, related by the Lagrangian. With Corollary 34.2.2, which gives a unique upper
closed member of each equivalence class, the theorem names a canonical representative of each
class. -/
theorem theorem_36_5 (L : Rn m × Rn n → EReal) :
    (∃ F : Bifun (Rn m) (Rn n),
        ConvexBifun F ∧ ClosedConvexBifun F ∧ saddleLagrangian (pairing m) F = L)
      ↔ ConcaveConvexFn L ∧ UpperClosedFn L := by
  constructor
  · rintro ⟨F, hF, hcl, rfl⟩
    exact ⟨concaveConvexFn_saddleLagrangian (pairing m) hF,
      upperClosedFn_saddleLagrangian (pairing m) (pairing n) hF hcl⟩
  · rintro ⟨hL, huc⟩
    obtain ⟨G, hG, -⟩ :=
      exists_unique_closedConvexBifun_saddleLagrangian_eq (pairing m) (pairing n) hL huc
    exact ⟨G, hG⟩

/-- **Theorem 36.5** of [rockafellar1970convex], necessity. Let $F$ be a closed convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then the Lagrangian of the program associated with $F$ is
upper closed. -/
theorem theorem_36_5_upperClosed (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    UpperClosedFn (saddleLagrangian (pairing m) F) :=
  upperClosedFn_saddleLagrangian (pairing m) (pairing n) hF hcl

/-- **Theorem 36.5** of [rockafellar1970convex], uniqueness. Let $L : \mathbb{R}^m \times
\mathbb{R}^n \to [-\infty, +\infty]$ be an upper closed concave-convex function. Then there is
exactly one closed convex bifunction $G$ from $\mathbb{R}^m$ to $\mathbb{R}^n$ whose Lagrangian
is $L$.

The book gives $G$ explicitly by $(Gu)(x) = \sup_{u^*} \{L(u^*, x) - \langle u^*, u \rangle\}$.
The statement here asserts existence and uniqueness without this formula. -/
theorem theorem_36_5_unique (hL : ConcaveConvexFn L) (huc : UpperClosedFn L) :
    ∃! G : Bifun (Rn m) (Rn n),
      ConvexBifun G ∧ ClosedConvexBifun G ∧ saddleLagrangian (pairing m) G = L :=
  exists_unique_closedConvexBifun_saddleLagrangian_eq (pairing m) (pairing n) hL huc

end Thm365

/-! ### The Kuhn–Tucker condition, and Theorem 36.6 -/

section Thm366

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {x : Rn n}

/-- Let $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$ and
$(u, v) \in \mathbb{R}^m \times \mathbb{R}^n$. Then $(0, 0) \in \partial K(u, v)$ if and only if
$(u, v)$ is a saddle-point of $K$, that is, $K(\cdot, v)$ attains its maximum at $u$ and
$K(u, \cdot)$ attains its minimum at $v$. No hypothesis on $K$ is needed. -/
theorem zero_mem_saddleSubdifferential_iff_isSaddlePoint (K : Rn m × Rn n → EReal)
    (p : Rn m × Rn n) :
    (0 : Rn m × Rn n) ∈ saddleSubdifferential (pairing m) (pairing n) K p ↔ IsSaddlePoint K p := by
  rw [mem_saddleSubdifferential_iff_isSaddlePoint, saddleTilt_zero]

/-- The Kuhn–Tucker condition for the program $(P)$. Let $F$ be a closed proper convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$ with Lagrangian $L$, and let $\bar u^* \in \mathbb{R}^m$
and $\bar x \in \mathbb{R}^n$. Then $(0, 0) \in \partial L(\bar u^*, \bar x)$ if and only if
$\bar u^*$ is a Kuhn–Tucker vector for $(P)$ and $\bar x$ is an optimal solution to $(P)$.

Proper means that the function $(u, x) \mapsto (Fu)(x)$ is proper. -/
theorem kuhnTucker_condition_iff (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (v : Rn m) (x : Rn n) :
    (0 : Rn m × Rn n) ∈ saddleSubdifferential (pairing m) (pairing n)
        (saddleLagrangian (pairing m) F) (v, x)
      ↔ v ∈ KuhnTucker (pairing m) F ∧ IsOptimalSolution F x := by
  rw [zero_mem_saddleSubdifferential_iff_isSaddlePoint]
  exact theorem_29_3_isSaddlePoint hF hcl hpr

/-- **Theorem 36.6** of [rockafellar1970convex], the strongly consistent case. Let $(P)$ be the
convex program associated with a closed proper convex bifunction $F$ from $\mathbb{R}^m$ to
$\mathbb{R}^n$, with Lagrangian $L$, and assume that $(P)$ is strongly consistent, that is,
$0 \in \operatorname{ri}(\operatorname{dom} F)$. Then $\bar x \in \mathbb{R}^n$ is an optimal
solution to $(P)$ if and only if $(0, 0) \in \partial L(\bar u^*, \bar x)$ for some
$\bar u^* \in \mathbb{R}^m$.

The book prints no proof. The statement follows from the Kuhn–Tucker theorem, Corollary 29.3.1,
through `Rockafellar.kuhnTucker_condition_iff`. -/
theorem theorem_36_6_stronglyConsistent (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hs : StronglyConsistent F) :
    IsOptimalSolution F x ↔ ∃ v : Rn m, (0 : Rn m × Rn n) ∈
      saddleSubdifferential (pairing m) (pairing n) (saddleLagrangian (pairing m) F) (v, x) := by
  rw [corollary_29_3_1_stronglyConsistent hF hcl hpr hs]
  exact exists_congr fun v =>
    (zero_mem_saddleSubdifferential_iff_isSaddlePoint (saddleLagrangian (pairing m) F) (v, x)).symm

/-- **Theorem 36.6** of [rockafellar1970convex], the strictly consistent case. Let $(P)$ be the
convex program associated with a closed proper convex bifunction $F$ from $\mathbb{R}^m$ to
$\mathbb{R}^n$, with Lagrangian $L$, and assume that $(P)$ is strictly consistent, that is,
$0 \in \operatorname{int}(\operatorname{dom} F)$. Then $\bar x \in \mathbb{R}^n$ is an optimal
solution to $(P)$ if and only if $(0, 0) \in \partial L(\bar u^*, \bar x)$ for some
$\bar u^* \in \mathbb{R}^m$.

A strictly consistent program is strongly consistent, so this follows from
`Rockafellar.theorem_36_6_stronglyConsistent`. -/
theorem theorem_36_6_strictlyConsistent (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hs : StrictlyConsistent F) :
    IsOptimalSolution F x ↔ ∃ v : Rn m, (0 : Rn m × Rn n) ∈
      saddleSubdifferential (pairing m) (pairing n) (saddleLagrangian (pairing m) F) (v, x) :=
  theorem_36_6_stronglyConsistent hF hcl hpr hs.stronglyConsistent

/-- **Theorem 36.6** of [rockafellar1970convex], the polyhedral case. Let $(P)$ be the convex
program associated with a closed proper polyhedral convex bifunction $F$ from $\mathbb{R}^m$ to
$\mathbb{R}^n$, with Lagrangian $L$, and assume that $(P)$ is consistent, that is,
$0 \in \operatorname{dom} F$. Then $\bar x \in \mathbb{R}^n$ is an optimal solution to $(P)$ if
and only if $(0, 0) \in \partial L(\bar u^*, \bar x)$ for some $\bar u^* \in \mathbb{R}^m$.

Theorem 29.2 supplies a Kuhn–Tucker vector without a hypothesis of relative interiority. -/
theorem theorem_36_6_polyhedral (hF : PolyhedralBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hc : Consistent F) :
    IsOptimalSolution F x ↔ ∃ v : Rn m, (0 : Rn m × Rn n) ∈
      saddleSubdifferential (pairing m) (pairing n) (saddleLagrangian (pairing m) F) (v, x) := by
  rw [corollary_29_3_1_polyhedral hF hcl hpr hc]
  exact exists_congr fun v =>
    (zero_mem_saddleSubdifferential_iff_isSaddlePoint (saddleLagrangian (pairing m) F) (v, x)).symm

/-- **Theorem 36.6** of [rockafellar1970convex], the last sentence. Let $(P)$ be the convex program
associated with a closed proper convex bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$,
with Lagrangian $L$, and let $\bar x$ be an optimal solution to $(P)$. Then for
$\bar u^* \in \mathbb{R}^m$, $(0, 0) \in \partial L(\bar u^*, \bar x)$ if and only if $\bar u^*$
is a Kuhn–Tucker vector for $(P)$. No constraint qualification is needed.

**Reading.** No constraint qualification is needed once the primal point is known to be optimal.
-/
theorem theorem_36_6_kuhnTucker (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hx : IsOptimalSolution F x) (v : Rn m) :
    (0 : Rn m × Rn n) ∈ saddleSubdifferential (pairing m) (pairing n)
        (saddleLagrangian (pairing m) F) (v, x)
      ↔ v ∈ KuhnTucker (pairing m) F := by
  rw [kuhnTucker_condition_iff hF hcl hpr]
  exact ⟨And.left, fun h => ⟨h, hx⟩⟩

end Thm366

end Rockafellar
