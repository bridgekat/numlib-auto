/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Saddle.Conjugate
import Numlib.Analysis.Convex.Saddle.Existence
import Numlib.Analysis.Convex.Saddle.Monotone
import NumlibSurface.Rockafellar.Chapter07.Section34
import NumlibSurface.Rockafellar.Chapter07.Section35
import NumlibSurface.Rockafellar.Chapter07.Section36

/-!
# Rockafellar, Section 37: Conjugate saddle-functions and minimax theorems

This module formalizes Section 37 of [rockafellar1970convex] (pages 388–400). For $K : \mathbb{R}^m
\times \mathbb{R}^n \to [-\infty, +\infty]$ the **lower conjugate** and the **upper conjugate** are
$$\underline{K}^*(u^*, v^*) = \sup_v \inf_u \{\langle u, u^* \rangle + \langle v, v^* \rangle - K(u,
  v)\}, \qquad \overline{K}^*(u^*, v^*) = \inf_u \sup_v \{\langle u, u^* \rangle + \langle v, v^*
  \rangle - K(u, v)\}.$$
For $K$ in the class $\Omega(F)$ of a closed convex bifunction $F$ (Section 34), both conjugates lie
in the conjugate class $\Omega(F_*^*)$, are equivalent to each other, and have the common effective
domain $C^* \times D^*$. Since $\inf_v \sup_u K = -\underline{K}^*(0, 0)$ and
$\sup_u \inf_v K = -\overline{K}^*(0, 0)$, minimax theory is this conjugacy correspondence read at
the origin. The section derives existence theorems for the saddle-value and for a saddle-point from
conditions on directions of recession, studies the subdifferential $\partial K$ (Theorems 37.4 and
37.5), and obtains the two minimax theorems for a continuous finite concave-convex function on a
product of closed bounded convex sets.

All eighteen numbered results of Section 37 are formalized: Theorems 37.1–37.6 and Corollaries
37.1.1, 37.1.2, 37.1.3, 37.2.1, 37.3.1, 37.3.2, 37.4.1, 37.5.1, 37.5.2, 37.5.3, 37.6.1 and 37.6.2.
The proofs specialize `Numlib.Analysis.Convex.Saddle.Minimax`,
`Numlib.Analysis.Convex.Saddle.Conjugate`, `Numlib.Analysis.Convex.Saddle.Existence`,
`Numlib.Analysis.Convex.Saddle.Subdifferential` and `Numlib.Analysis.Convex.Saddle.Monotone`.

## Main definitions

* Section 37, `Rockafellar.lowerConj`: the lower conjugate $\underline{K}^*$.
* Section 37, `Rockafellar.upperConj`: the upper conjugate $\overline{K}^*$.
* Section 37, `Rockafellar.domSubdiff`: the set $\operatorname{dom} \partial K$ of the points where
  $\partial K$ is non-empty.

## Main results

* Theorem 37.1, `Rockafellar.theorem_37_1_upper`, `Rockafellar.theorem_37_1_lower`,
  `Rockafellar.theorem_37_1_conj_upper`, `Rockafellar.theorem_37_1_conj_lower`: four formulas for
  the conjugates of the members of $\Omega(F)$ and of $\Omega(F_*^*)$ in terms of $F$.
* Corollary 37.1.1, `Rockafellar.corollary_37_1_1_lower_concaveConvex` and the twelve other
  declarations for its parts: the conjugates are concave-convex, lower and upper closed, closed,
  equivalent to each other, proper when $K$ is proper, depend only on the class of $K$, and
  conjugacy is involutive up to equivalence.
* Corollary 37.1.2, `Rockafellar.corollary_37_1_2_cl₁`, `Rockafellar.corollary_37_1_2_cl₂`,
  `Rockafellar.corollary_37_1_2_dom`, `Rockafellar.corollary_37_1_2_structure`,
  `Rockafellar.corollary_37_1_2_eq_of_mem_relint_dom₁`,
  `Rockafellar.corollary_37_1_2_eq_of_mem_relint_dom₂`: $\operatorname{cl}_1 \underline{K}^* =
  \overline{K}^*$ and $\operatorname{cl}_2 \overline{K}^* = \underline{K}^*$, $C^* \times D^*$ is
  the effective domain of both conjugates, and they agree where one argument is in the relative
  interior.
* Corollary 37.1.3, `Rockafellar.corollary_37_1_3_dom₁`, `Rockafellar.corollary_37_1_3_dom₂`,
  `Rockafellar.corollary_37_1_3_finite`: the saddle-value exists if $0 \in \operatorname{ri} C^*$ or
  $0 \in \operatorname{ri} D^*$, and it is finite if both hold.
* Theorem 37.2, `Rockafellar.theorem_37_2_dom₂`, `Rockafellar.theorem_37_2_dom₂_recessionFn`: a
  formula for the support function of $D^*$.
* Corollary 37.2.1, `Rockafellar.corollary_37_2_1_dom₂`, `Rockafellar.corollary_37_2_1_dom₁`:
  $0 \in \operatorname{int} D^*$, or $0 \in \operatorname{int} C^*$, if and only if a family of
  slices of $K$ has no common direction of recession.
* Theorem 37.3, `Rockafellar.theorem_37_3_a`, `Rockafellar.theorem_37_3_b`,
  `Rockafellar.theorem_37_3_finite`: the existence theorem for the saddle-value.
* Corollary 37.3.1, `Rockafellar.corollary_37_3_1_dom₂`, `Rockafellar.corollary_37_3_1_dom₁`: the
  saddle-value exists if $\operatorname{dom}_2 K$ or $\operatorname{dom}_1 K$ is bounded.
* Corollary 37.3.2, `Rockafellar.corollary_37_3_2_right`, `Rockafellar.corollary_37_3_2_left`: the
  minimax equality for a continuous finite concave-convex function on $C \times D$ with $C$ or $D$
  bounded.
* Theorem 37.4, `Rockafellar.theorem_37_4`, `Rockafellar.theorem_37_4_convex`,
  `Rockafellar.theorem_37_4_isClosed`, `Rockafellar.theorem_37_4_relint`,
  `Rockafellar.theorem_37_4_dom`: $(u^*, v^*) \in \partial K(u, v)$ if and only if $(u, v)$ is a
  saddle-point of the tilted function; $\partial K(u, v)$ is closed and convex; and
  $\operatorname{ri}(\operatorname{dom} K) \subseteq \operatorname{dom} \partial K \subseteq
  \operatorname{dom} K$.
* Corollary 37.4.1, `Rockafellar.corollary_37_4_1_subdiff`, `Rockafellar.corollary_37_4_1_eq`:
  equivalent saddle-functions have the same subdifferential and agree on
  $\operatorname{dom} \partial K$.
* Theorem 37.5, `Rockafellar.theorem_37_5_f`, `Rockafellar.theorem_37_5_a`,
  `Rockafellar.theorem_37_5_b`, `Rockafellar.theorem_37_5_c`, `Rockafellar.theorem_37_5_d`: four
  equivalent conditions that relate $\partial K$, $\partial \overline{K}^*$ and the subdifferential
  of the graph function $f$ of $F$.
* Corollary 37.5.1, `Rockafellar.corollary_37_5_1_isClosed`,
  `Rockafellar.corollary_37_5_1_homeomorph`, `Rockafellar.corollary_37_5_1_exists_homeomorph`: the
  graph of $\partial K$ is closed and homeomorphic to $\mathbb{R}^m \times \mathbb{R}^n$.
* Corollary 37.5.2, `Rockafellar.corollary_37_5_2`, `Rockafellar.corollary_37_5_2_gradient`: the
  mapping $(u, v) \mapsto \{(-u^*, v^*) \mid (u^*, v^*) \in \partial K(u, v)\}$ is maximal monotone.
* Corollary 37.5.3, `Rockafellar.corollary_37_5_3`, `Rockafellar.corollary_37_5_3_convex`,
  `Rockafellar.corollary_37_5_3_isClosed`, `Rockafellar.corollary_37_5_3_exists_iff`,
  `Rockafellar.corollary_37_5_3_exists_of_relint`: the set of saddle-points of $K$ is
  $\partial \overline{K}^*(0, 0)$, a closed convex set.
* Theorem 37.6, `Rockafellar.theorem_37_6`, `Rockafellar.theorem_37_6_mem_dom`: the existence
  theorem for a saddle-point.
* Corollary 37.6.1, `Rockafellar.corollary_37_6_1`, `Rockafellar.corollary_37_6_1_finite`: a
  saddle-point exists if $\operatorname{dom}_1 K$ and $\operatorname{dom}_2 K$ are bounded.
* Corollary 37.6.2, `Rockafellar.corollary_37_6_2`: the minimax theorem, existence of a saddle-point
  for a continuous finite concave-convex function on a product of non-empty closed bounded convex
  sets.

## Conventions

* In the lower conjugate the supremum over the convex variable is outside, and in the upper
  conjugate the infimum over the concave variable is outside. Lemma 36.1 gives
  $\underline{K}^* \le \overline{K}^*$. The closures $\operatorname{cl}_1$ and $\operatorname{cl}_2$
  of Section 33 and the orientation of Section 36 (minimize in the convex argument, maximize in the
  concave argument) are in force.
* By Corollary 37.1.1 the conjugates depend only on the equivalence class of $K$. So the results are
  stated for a member $K$ of $\Omega(F)$ (`Rockafellar.Ω`) for a closed convex bifunction $F$, or
  for a closed concave-convex $K$; `Rockafellar.exists_mem_Ω_of_closed` gives $F$ from $K$.
* $C^* \times D^*$ is the effective domain of the conjugates. The statements write it as
  `dom₁ (lowerConj K)` and `dom₂ (lowerConj K)`, or as `dom₂ (upperConj K)`; by Corollary 37.1.2
  these sets agree.

## Implementation notes

* Corollaries 37.3.2 and 37.6.2 assume that $C$ or $D$ is closed and bounded. The analogous minimax
  theorems in infinite dimensions (Kneser–Fan, Sion) need compactness; in $\mathbb{R}^n$ the two
  conditions agree by the Heine–Borel theorem.
* The homeomorphism of Corollary 37.5.1 is $(u, v, u^*, v^*) \mapsto (u - u^*, v^* + v)$. The book
  prints the second component as $v + v^*$, which is the same vector.

## Deviations from the source

* **Theorem 37.4** (generalization). The book assumes that $K$ is concave-convex.
  `Rockafellar.theorem_37_4` has no hypothesis on $K$.
* **Corollaries 37.3.2 and 37.6.2** (reading). The hypotheses of concavity, convexity and continuity
  are read slice by slice: $K(\cdot, v)$ is concave and continuous on $C$ for each $v \in D$, and
  $K(u, \cdot)$ is convex and continuous on $D$ for each $u \in C$. Separate continuity is weaker
  than joint continuity. See `Rockafellar.corollary_37_3_2_right` and
  `Rockafellar.corollary_37_6_2`.

## Not formalized

* **Theorem 37.2**, the formula for the support function of $C^*$. Its formula for $D^*$ is
  `Rockafellar.theorem_37_2_dom₂`, and no later result depends on the formula for $C^*$.
* **Corollary 37.4.1** for a function $K$ that is not closed. The book does not assume closedness;
  the statements here assume that $K$ is closed. See `Rockafellar.corollary_37_4_1_subdiff`.
-/

namespace Rockafellar

open ConvexAnalysis

/-! ### The two conjugates of a saddle-function -/

section Defs

variable {m n : ℕ}

/-- **Section 37** of [rockafellar1970convex], definition of the lower conjugate. For $K :
\mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, the **lower conjugate** of $K$ is
$$\underline{K}^*(u^*, v^*) = \sup_{v} \inf_{u} \{\langle u, u^* \rangle + \langle v, v^*
  \rangle - K(u, v)\}.$$
The supremum over the convex variable $v$ is outside.

The definition is `ConvexAnalysis.lowerConjSaddle` for the Euclidean pairings. -/
noncomputable abbrev lowerConj (K : Rn m × Rn n → EReal) : Rn m × Rn n → EReal :=
  lowerConjSaddle (pairing m) (pairing n) K

/-- **Section 37** of [rockafellar1970convex], definition of the upper conjugate. For $K :
\mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$, the **upper conjugate** of $K$ is
$$\overline{K}^*(u^*, v^*) = \inf_{u} \sup_{v} \{\langle u, u^* \rangle + \langle v, v^*
  \rangle - K(u, v)\}.$$
The infimum over the concave variable $u$ is outside.

The definition is `ConvexAnalysis.upperConjSaddle` for the Euclidean pairings. -/
noncomputable abbrev upperConj (K : Rn m × Rn n → EReal) : Rn m × Rn n → EReal :=
  upperConjSaddle (pairing m) (pairing n) K

/-- For $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$ and $(u^*, v^*) \in
\mathbb{R}^m \times \mathbb{R}^n$, $\underline{K}^*(u^*, v^*) = \sup_v \inf_u \{\langle u, u^*
\rangle + \langle v^*, v \rangle - K(u, v)\}$. This is the defining formula of the book. -/
theorem lowerConj_apply (K : Rn m × Rn n → EReal) (q : Rn m × Rn n) :
    lowerConj K q
      = ⨆ v : Rn n, ⨅ u : Rn m, (((pairing m u q.1 + pairing n q.2 v : ℝ) : EReal) - K (u, v)) :=
  rfl

/-- For $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$ and $(u^*, v^*) \in
\mathbb{R}^m \times \mathbb{R}^n$, $\overline{K}^*(u^*, v^*) = \inf_u \sup_v \{\langle u, u^*
\rangle + \langle v^*, v \rangle - K(u, v)\}$. This is the defining formula of the book. -/
theorem upperConj_apply (K : Rn m × Rn n → EReal) (q : Rn m × Rn n) :
    upperConj K q
      = ⨅ u : Rn m, ⨆ v : Rn n, (((pairing m u q.1 + pairing n q.2 v : ℝ) : EReal) - K (u, v)) :=
  rfl

/-- For every $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$,
$\underline{K}^* \le \overline{K}^*$ everywhere. The book says that this holds "of course, by
Lemma 36.1". -/
theorem lowerConj_le_upperConj (K : Rn m × Rn n → EReal) : lowerConj K ≤ upperConj K :=
  lowerConjSaddle_le_upperConjSaddle (pairing m) (pairing n) K

/-- **Section 37** of [rockafellar1970convex], the domain of the subdifferential. For $K :
\mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$,
$$\operatorname{dom} \partial K = \{(u, v) \mid \partial K(u, v) \neq \emptyset\}.$$
-/
noncomputable abbrev domSubdiff (K : Rn m × Rn n → EReal) : Set (Rn m × Rn n) :=
  domSaddleSubdifferential (pairing m) (pairing n) K

/-- For $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$,
$(u, v) \in \operatorname{dom} \partial K$ if and only if $\partial K(u, v)$ is non-empty. -/
theorem mem_domSubdiff {K : Rn m × Rn n → EReal} {p : Rn m × Rn n} :
    p ∈ domSubdiff K ↔ (subdiff K p).Nonempty := Iff.rfl

/-- The Euclidean inner product on $\mathbb{R}^n$ separates points on the left: if
$\langle x, y \rangle = 0$ for all $y \in \mathbb{R}^n$, then $x = 0$. -/
theorem separatingLeft_pairing (n : ℕ) : (pairing n).SeparatingLeft :=
  fun _ hx => inner_self_eq_zero.1 (hx _)

/-- Theorem 34.2 in the form that this section uses. Let $K : \mathbb{R}^m \times \mathbb{R}^n \to
[-\infty, +\infty]$ be a closed concave-convex function. Then there is a closed convex
bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$ with $K \in \Omega(F)$.

$K$ need not be proper. The graph function of $F$ is proper exactly when $K$ is proper. Theorem
34.2 also says that $F$ is unique; this statement gives only existence. -/
theorem exists_mem_Ω_of_closed {K : Rn m × Rn n → EReal} (hK : ConcaveConvexFn K)
    (hcl : ClosedSaddleFn K) :
    ∃ F : Bifun (Rn m) (Rn n), ConvexBifun F ∧ ClosedConvexBifun F ∧ K ∈ Ω F := by
  obtain ⟨F, ⟨hFconv, hFcl, hlow, hup⟩, -⟩ := theorem_34_2_converse hK hcl
  exact ⟨F, hFconv, hFcl, theorem_34_2_mem_self hK hlow hup⟩

end Defs

/-! ### Theorem 37.1 -/

section Thm371

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- **Theorem 37.1** of [rockafellar1970convex], the first equation. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, and let $K \in \Omega(F)$. Then for all
$(u^*, x) \in \mathbb{R}^m \times \mathbb{R}^n$,
$$\overline{K}^*(u^*, x) = \inf_u \sup_{x^*} \{\langle u, u^* \rangle + \langle x, x^* \rangle -
  K(u, x^*)\} = \langle u^*, F_* x \rangle.$$
So the upper conjugate is the Lagrangian of the program associated with $F$, which is the
concave bracket of the inverse bifunction (`Rockafellar.inverseBifunBracket`). -/
theorem theorem_37_1_upper (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F) :
    upperConj K = inverseBifunBracket F :=
  (upperConjSaddle_eq_saddleLagrangian (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK)).trans (saddleLagrangian_eq_inverseBifunBracket F)

/-- **Theorem 37.1** of [rockafellar1970convex], the second equation. Let $F$ be a convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$, and let $K \in \Omega(F)$. Then for all
$(u^*, x) \in \mathbb{R}^m \times \mathbb{R}^n$,
$$\underline{K}^*(u^*, x) = \sup_{x^*} \inf_u \{\langle u, u^* \rangle + \langle x, x^*
  \rangle - K(u, x^*)\} = \langle F_*^* u^*, x \rangle,$$
where $F_*^* = (F^*)_*$ is the bifunction of the conjugate class.

The statement does not need $F$ to be closed. $F_*^*$ is `ConvexAnalysis.inverseBifun
(Rockafellar.dualProgram F)`, and the bracket $\langle G u^*, x \rangle$ is
`Rockafellar.bifunBracket`. -/
theorem theorem_37_1_lower (hF : ConvexBifun F) (hK : K ∈ Ω F) :
    lowerConj K = bifunBracket (inverseBifun (dualProgram F)) := by
  have h := lowerConjSaddle_eq_bracket_lowerAdjointBifun (pairing m) (pairing n) hF
    (mem_bifunSaddleClass_of_mem_Ω hK)
  simp only [flip_pairing] at h
  exact h

/-- For every bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, the bifunction $F_*^* = (F^*)_*$
is a convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Its class $\Omega(F_*^*)$ is the
class conjugate to $\Omega(F)$. -/
theorem convexBifun_conjBifun (F : Bifun (Rn m) (Rn n)) :
    ConvexBifun (inverseBifun (dualProgram F)) :=
  convexBifun_lowerAdjointBifun (pairing m) (pairing n) F

/-- For every bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, the bifunction $F_*^* = (F^*)_*$
is closed. -/
theorem closedConvexBifun_conjBifun (F : Bifun (Rn m) (Rn n)) :
    ClosedConvexBifun (inverseBifun (dualProgram F)) :=
  haveI := isContinuousPairing_prodPairing_flip (pairing m) (pairing n)
  closedConvexBifun_lowerAdjointBifun

/-- For every bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, $(F_*^*)_* = F^*$, because the
inverse operation is involutory. -/
theorem inverseBifun_conjBifun (F : Bifun (Rn m) (Rn n)) :
    inverseBifun (inverseBifun (dualProgram F)) = dualProgram F :=
  inverseBifun_inverseBifun _

/-- The biadjoint identity: for a closed convex bifunction $F$ from $\mathbb{R}^m$ to
$\mathbb{R}^n$, $(F_*^*)^* = F_*$. -/
theorem dualProgram_conjBifun (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    dualProgram (inverseBifun (dualProgram F)) = inverseBifun F := by
  have h := convexAdjointBifun_flip_lowerAdjointBifun (Bu := pairing m) (Bx := pairing n) hF hcl
  simp only [flip_pairing] at h
  exact h

/-- **Theorem 37.1** of [rockafellar1970convex], the third equation. Let $F$ be a bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$, and let $K^* \in \Omega(F_*^*)$. Then for all
$(u, x^*) \in \mathbb{R}^m \times \mathbb{R}^n$,
$$\overline{K^*}^*(u, x^*) = \inf_{u^*} \sup_{x} \{\langle u, u^* \rangle + \langle x, x^*
  \rangle - K^*(u^*, x)\} = \langle u, F^* x^* \rangle.$$
This is the first equation for the bifunction $F_*^*$.

No hypothesis on $F$ is needed. The bracket $\langle u, F^* x^* \rangle$ is
`Rockafellar.adjointBracket F`. -/
theorem theorem_37_1_conj_upper (F : Bifun (Rn m) (Rn n))
    (hL : L ∈ Ω (inverseBifun (dualProgram F))) : upperConj L = adjointBracket F := by
  have h := theorem_37_1_upper (convexBifun_conjBifun F) (closedConvexBifun_conjBifun F) hL
  have h2 : inverseBifunBracket (inverseBifun (dualProgram F)) = adjointBracket F := by
    change concaveBifunBracket (inverseBifun (inverseBifun (dualProgram F))) = adjointBracket F
    rw [inverseBifun_conjBifun]
  exact h.trans h2

/-- **Theorem 37.1** of [rockafellar1970convex], the fourth equation. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, and let $K^* \in \Omega(F_*^*)$. Then for all
$(u, x^*) \in \mathbb{R}^m \times \mathbb{R}^n$,
$$\underline{K^*}^*(u, x^*) = \sup_{x} \inf_{u^*} \{\langle u, u^* \rangle + \langle x, x^*
  \rangle - K^*(u^*, x)\} = \langle F u, x^* \rangle.$$

This is the second equation for the bifunction $F_*^*$, together with $(F_*^*)^* = F_*$. That
identity is where the closedness of $F$ is used. -/
theorem theorem_37_1_conj_lower (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hL : L ∈ Ω (inverseBifun (dualProgram F))) : lowerConj L = bifunBracket F := by
  have h := theorem_37_1_lower (convexBifun_conjBifun F) hL
  rw [dualProgram_conjBifun hF hcl, inverseBifun_inverseBifun] at h
  exact h

end Thm371

/-! ### Corollary 37.1.1 -/

section Cor3711

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- Let $F$ be a closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and
$K \in \Omega(F)$. Then $\overline{K}^* \in \Omega(F_*^*)$. -/
theorem upperConj_mem_Ω (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F) :
    upperConj K ∈ Ω (inverseBifun (dualProgram F)) := by
  refine ⟨concaveConvexFn_upperConjSaddle (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK), ?_⟩
  have hmem : upperConjSaddle (pairing m) (pairing n) K
      ∈ bifunSaddleClass (pairing m).flip (pairing n).flip
        (lowerAdjointBifun (pairing m) (pairing n) F) := by
    rw [saddleClass_conjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)]
    exact mem_saddleClass_right (partialCl₂_upperConjSaddle (pairing m) (pairing n) hF hcl
      (mem_bifunSaddleClass_of_mem_Ω hK))
  have hmem' : upperConjSaddle (pairing m) (pairing n) K
      ∈ bifunSaddleClass (pairing m) (pairing n) (inverseBifun (dualProgram F)) := by
    simp only [flip_pairing] at hmem
    exact hmem
  exact hmem'

/-- Let $F$ be a closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and
$K \in \Omega(F)$. Then $\underline{K}^* \in \Omega(F_*^*)$. -/
theorem lowerConj_mem_Ω (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F) :
    lowerConj K ∈ Ω (inverseBifun (dualProgram F)) := by
  refine ⟨concaveConvexFn_lowerConjSaddle (pairing m) (pairing n) hF
    (mem_bifunSaddleClass_of_mem_Ω hK), ?_⟩
  have hmem : lowerConjSaddle (pairing m) (pairing n) K
      ∈ bifunSaddleClass (pairing m).flip (pairing n).flip
        (lowerAdjointBifun (pairing m) (pairing n) F) := by
    rw [saddleClass_conjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)]
    exact mem_saddleClass_left (partialCl₂_upperConjSaddle (pairing m) (pairing n) hF hcl
      (mem_bifunSaddleClass_of_mem_Ω hK))
  have hmem' : lowerConjSaddle (pairing m) (pairing n) K
      ∈ bifunSaddleClass (pairing m) (pairing n) (inverseBifun (dualProgram F)) := by
    simp only [flip_pairing] at hmem
    exact hmem
  exact hmem'

/-- **Corollary 37.1.1** of [rockafellar1970convex], concave-convexity of the lower conjugate. Let
$F$ be a convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then
$\underline{K}^*$ is concave-convex. -/
theorem corollary_37_1_1_lower_concaveConvex (hF : ConvexBifun F) (hK : K ∈ Ω F) :
    ConcaveConvexFn (lowerConj K) :=
  concaveConvexFn_lowerConjSaddle (pairing m) (pairing n) hF (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.1** of [rockafellar1970convex], lower closedness of the lower conjugate. Let
$F$ be a closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$.
Then $\underline{K}^*$ is lower closed: $\operatorname{cl}_2 \operatorname{cl}_1
\underline{K}^* = \underline{K}^*$.

The proof is Theorem 33.3 for the bifunction $F_*^*$; it does not use the closedness of $F$. -/
theorem corollary_37_1_1_lower_lowerClosed (hF : ConvexBifun F) (_hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F) : LowerClosedFn (lowerConj K) :=
  lowerClosedFn_lowerConjSaddle (pairing m) (pairing n) hF (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.1** of [rockafellar1970convex], concave-convexity of the upper conjugate. Let
$F$ be a closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$.
Then $\overline{K}^*$ is concave-convex. -/
theorem corollary_37_1_1_upper_concaveConvex (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F) : ConcaveConvexFn (upperConj K) :=
  concaveConvexFn_upperConjSaddle (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.1** of [rockafellar1970convex], upper closedness of the upper conjugate. Let
$F$ be a closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$.
Then $\overline{K}^*$ is upper closed: $\operatorname{cl}_1 \operatorname{cl}_2 \overline{K}^* =
\overline{K}^*$. -/
theorem corollary_37_1_1_upper_upperClosed (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F) : UpperClosedFn (upperConj K) :=
  upperClosedFn_upperConjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.1** of [rockafellar1970convex], equivalence of the two conjugates. Let $F$ be a
closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then
$\underline{K}^*$ and $\overline{K}^*$ are equivalent.

By Theorem 36.4 they therefore have the same iterated extrema and the same saddle-points. -/
theorem corollary_37_1_1_equiv (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F) :
    SaddleEquiv (lowerConj K) (upperConj K) :=
  saddleEquiv_lowerConjSaddle_upperConjSaddle (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.1** of [rockafellar1970convex], closedness of the lower conjugate. Let $F$ be a
closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then
$\underline{K}^*$ is a closed saddle-function.

The two conjugates are the lower and the upper end of the class $\Omega(F_*^*)$. -/
theorem corollary_37_1_1_closed_lower (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F) :
    ClosedSaddleFn (lowerConj K) :=
  theorem_34_2_closed (convexBifun_conjBifun F) (closedConvexBifun_conjBifun F)
    (lowerConj_mem_Ω hF hcl hK)

/-- **Corollary 37.1.1** of [rockafellar1970convex], closedness of the upper conjugate. Let $F$ be a
closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then
$\overline{K}^*$ is a closed saddle-function. -/
theorem corollary_37_1_1_closed_upper (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F) :
    ClosedSaddleFn (upperConj K) :=
  theorem_34_2_closed (convexBifun_conjBifun F) (closedConvexBifun_conjBifun F)
    (upperConj_mem_Ω hF hcl hK)

/-- **Corollary 37.1.1** of [rockafellar1970convex], the lower conjugate depends only on the class.
Let $F$ be a convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K, L \in \Omega(F)$.
Then $\underline{K}^* = \underline{L}^*$. -/
theorem corollary_37_1_1_lower_class (hF : ConvexBifun F) (hK : K ∈ Ω F) (hL : L ∈ Ω F) :
    lowerConj K = lowerConj L :=
  (theorem_37_1_lower hF hK).trans (theorem_37_1_lower hF hL).symm

/-- **Corollary 37.1.1** of [rockafellar1970convex], the upper conjugate depends only on the class.
Let $F$ be a closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and
$K, L \in \Omega(F)$. Then $\overline{K}^* = \overline{L}^*$. -/
theorem corollary_37_1_1_upper_class (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hL : L ∈ Ω F) : upperConj K = upperConj L :=
  (theorem_37_1_upper hF hcl hK).trans (theorem_37_1_upper hF hcl hL).symm

/-- **Corollary 37.1.1** of [rockafellar1970convex], properness of the upper conjugate. Let $F$ be a
closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let $K \in \Omega(F)$ be
proper. Then $\overline{K}^*$ is proper.

The only improper closed saddle-functions are the constants $+\infty$ and $-\infty$, and these
are conjugate to each other. -/
theorem corollary_37_1_1_proper_upper (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) : ProperSaddleFn (upperConj K) :=
  properSaddleFn_upperConjSaddle (pairing m) (pairing n) hF hcl
    (properConvex_graphFn_of_properSaddleFn (pairing m) (pairing n)
        (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.1** of [rockafellar1970convex], properness of the lower conjugate. Let $F$ be a
closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let $K \in \Omega(F)$ be
proper. Then $\underline{K}^*$ is proper. -/
theorem corollary_37_1_1_proper_lower (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) : ProperSaddleFn (lowerConj K) :=
  properSaddleFn_lowerConjSaddle (pairing m) (pairing n) hF hcl
    (properConvex_graphFn_of_properSaddleFn (pairing m) (pairing n)
        (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.1** of [rockafellar1970convex], the last sentence, for the lower conjugate. Let
$F$ be a closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$.
Then the lower conjugate of $\overline{K}^*$ is equivalent to $K$. So conjugacy is involutive up
to equivalence.

The lower conjugate of $\overline{K}^*$ is $\langle F u, x^* \rangle$, the lower end of
$\Omega(F)$. -/
theorem corollary_37_1_1_biconj_lower (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F) :
    SaddleEquiv (lowerConj (upperConj K)) K := by
  rw [theorem_37_1_conj_lower hF hcl (upperConj_mem_Ω hF hcl hK)]
  exact theorem_34_2_equiv hF hcl (theorem_34_2_lower_mem hF hcl) hK

/-- **Corollary 37.1.1** of [rockafellar1970convex], the last sentence, for the upper conjugate. Let
$F$ be a closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$.
Then the upper conjugate of $\overline{K}^*$ is equivalent to $K$.

The upper conjugate of $\overline{K}^*$ is $\langle u, F^* x^* \rangle$, the upper end of
$\Omega(F)$. -/
theorem corollary_37_1_1_biconj_upper (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F) :
    SaddleEquiv (upperConj (upperConj K)) K := by
  rw [theorem_37_1_conj_upper F (upperConj_mem_Ω hF hcl hK)]
  exact theorem_34_2_equiv hF hcl (theorem_34_2_upper_mem hF hcl) hK

end Cor3711

/-! ### Corollary 37.1.2 -/

section Cor3712

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Corollary 37.1.2** of [rockafellar1970convex], the first equation. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then
$\operatorname{cl}_1 \underline{K}^* = \overline{K}^*$. -/
theorem corollary_37_1_2_cl₁ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F) :
    cl₁ (lowerConj K) = upperConj K :=
  partialCl₁_lowerConjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.2** of [rockafellar1970convex], the second equation. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then
$\operatorname{cl}_2 \overline{K}^* = \underline{K}^*$. -/
theorem corollary_37_1_2_cl₂ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F) :
    cl₂ (upperConj K) = lowerConj K :=
  partialCl₂_upperConjSaddle (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.2** of [rockafellar1970convex], the common effective domain. Let $F$ be a
closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let $K \in \Omega(F)$ be
proper. Then $\underline{K}^*$ and $\overline{K}^*$ have the same effective domain
$C^* \times D^*$.

The effective domain is `ConvexAnalysis.domSaddle`, the product $\operatorname{dom}_1 \times
\operatorname{dom}_2$. -/
theorem corollary_37_1_2_dom (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) : domSaddle (lowerConj K) = domSaddle (upperConj K) :=
  domSaddle_conjSaddle_eq (pairing m) (pairing n) hF hcl
    (properConvex_graphFn_of_properSaddleFn (pairing m) (pairing n)
        (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.1.2** of [rockafellar1970convex], the first sentence. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and let $K \in \Omega(F)$ be proper. Then
$\overline{K}^*$ has the structure that Theorem 34.3 describes, with respect to its effective
domain $C^* \times D^*$: for $u^* \in C^*$ the slice $\overline{K}^*(u^*, \cdot)$ is a proper
convex function; for $u^* \in \operatorname{ri} C^*$ it is closed with effective domain $D^*$;
for $u^* \in C^*$ its effective domain lies in $\operatorname{cl} D^*$; for $u^* \notin C^*$ it
is $-\infty$ on $\operatorname{ri} D^*$; and for $u^* \notin \operatorname{cl} C^*$ it is
$-\infty$ on $D^*$. The same holds for the concave slices $\overline{K}^*(\cdot, v^*)$, with the
roles of the two arguments exchanged and with $+\infty$ in place of $-\infty$.

The structure is `ConvexAnalysis.SaddleStructure`: `ConvexAnalysis.ConvexSliceStructure` for
$\overline{K}^*$ and for the swapped function `ConvexAnalysis.saddleSwap`. -/
theorem corollary_37_1_2_structure (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) : SaddleStructure (upperConj K) :=
  (theorem_34_3 (corollary_37_1_1_upper_concaveConvex hF hcl hK)
    (corollary_37_1_1_proper_upper hF hcl hK hp)).1 (corollary_37_1_1_closed_upper hF hcl hK)

/-- **Corollary 37.1.2** of [rockafellar1970convex], the last clause, in the first argument. Let $F$
be a closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$ be
proper, and let $C^* \times D^*$ be the effective domain of $\underline{K}^*$. If
$u^* \in \operatorname{ri} C^*$, then $\underline{K}^*(u^*, v^*) = \overline{K}^*(u^*, v^*)$ for
every $v^* \in \mathbb{R}^n$. -/
theorem corollary_37_1_2_eq_of_mem_relint_dom₁ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F) (hp : ProperSaddleFn K) {u : Rn m} (hu : u ∈ ri (dom₁ (lowerConj K)))
    (v : Rn n) : lowerConj K (u, v) = upperConj K (u, v) :=
  lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₁ (pairing m) (pairing n) hF hcl
    (properConvex_graphFn_of_properSaddleFn (pairing m) (pairing n)
        (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) hu v

/-- **Corollary 37.1.2** of [rockafellar1970convex], the last clause, in the second argument. Let
$F$ be a closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$
be proper, and let $C^* \times D^*$ be the effective domain of $\underline{K}^*$. If
$v^* \in \operatorname{ri} D^*$, then $\underline{K}^*(u^*, v^*) = \overline{K}^*(u^*, v^*)$ for
every $u^* \in \mathbb{R}^m$. -/
theorem corollary_37_1_2_eq_of_mem_relint_dom₂ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F) (hp : ProperSaddleFn K) {v : Rn n} (hv : v ∈ ri (dom₂ (lowerConj K)))
    (u : Rn m) : lowerConj K (u, v) = upperConj K (u, v) :=
  lowerConjSaddle_eq_upperConjSaddle_of_mem_relint_dom₂ (pairing m) (pairing n) hF hcl
    (properConvex_graphFn_of_properSaddleFn (pairing m) (pairing n)
        (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) hv u

end Cor3712

/-! ### The saddle-value read at the origin, and Corollary 37.1.3 -/

section Cor3713

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- For every $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$,
$$\inf_v \sup_u K(u, v) = -\underline{K}^*(0, 0).$$
-/
theorem minimax_eq_neg_lowerConj_zero (K : Rn m × Rn n → EReal) :
    minimax K = -(lowerConj K 0) :=
  minimax_eq_neg_lowerConjSaddle_zero (pairing m) (pairing n) K

/-- For every $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$,
$$\sup_u \inf_v K(u, v) = -\overline{K}^*(0, 0).$$
-/
theorem maximin_eq_neg_upperConj_zero (K : Rn m × Rn n → EReal) :
    maximin K = -(upperConj K 0) :=
  maximin_eq_neg_upperConjSaddle_zero (pairing m) (pairing n) K

/-- **Corollary 37.1.3** of [rockafellar1970convex], the condition on $C^*$. Let $F$ be a closed
convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$ be proper, and
let $C^* \times D^*$ be the effective domain of $\underline{K}^*$. If
$0 \in \operatorname{ri} C^*$, then the saddle-value of $K$ exists:
$$\inf_v \sup_u K(u, v) = \sup_u \inf_v K(u, v).$$

The book prints no proof. By `Rockafellar.minimax_eq_neg_lowerConj_zero` and
`Rockafellar.maximin_eq_neg_upperConj_zero`, the saddle-value exists exactly when the two
conjugates agree at the origin, and Corollary 37.1.2 makes them agree on
$\operatorname{ri} C^* \times \mathbb{R}^n$. -/
theorem corollary_37_1_3_dom₁ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (h0 : (0 : Rn m) ∈ ri (dom₁ (lowerConj K))) : HasSaddleValue K :=
  hasSaddleValue_of_mem_relint_dom₁_lowerConjSaddle (pairing m) (pairing n) hF hcl
    (properConvex_graphFn_of_properSaddleFn (pairing m) (pairing n)
        (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) h0

/-- **Corollary 37.1.3** of [rockafellar1970convex], the condition on $D^*$. Let $F$ be a closed
convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$ be proper, and
let $C^* \times D^*$ be the effective domain of $\underline{K}^*$. If
$0 \in \operatorname{ri} D^*$, then the saddle-value of $K$ exists. -/
theorem corollary_37_1_3_dom₂ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (h0 : (0 : Rn n) ∈ ri (dom₂ (lowerConj K))) : HasSaddleValue K :=
  hasSaddleValue_of_mem_relint_dom₂_lowerConjSaddle (pairing m) (pairing n) hF hcl
    (properConvex_graphFn_of_properSaddleFn (pairing m) (pairing n)
        (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) h0

/-- **Corollary 37.1.3** of [rockafellar1970convex], the last sentence. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$ be proper, and let
$C^* \times D^*$ be the effective domain of $\underline{K}^*$. If $0 \in \operatorname{ri} C^*$
and $0 \in \operatorname{ri} D^*$, then $\sup_u \inf_v K(u, v)$ is finite, so the saddle-value
of $K$ is finite. -/
theorem corollary_37_1_3_finite (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (h1 : (0 : Rn m) ∈ ri (dom₁ (lowerConj K)))
    (h2 : (0 : Rn n) ∈ ri (dom₂ (lowerConj K))) : ∃ r : ℝ, maximin K = (r : EReal) :=
  exists_maximin_eq_coe_of_mem_relint_domSaddle (pairing m) (pairing n) hF hcl
    (properConvex_graphFn_of_properSaddleFn (pairing m) (pairing n)
        (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK) h1 h2

end Cor3713

/-! ### Theorem 37.2 and Corollary 37.2.1 -/

section Thm372

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Theorem 37.2** of [rockafellar1970convex], the formula for $D^*$. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$ be closed and proper,
and let $C = \operatorname{dom}_1 K$, $D = \operatorname{dom}_2 K$ and
$D^* = \operatorname{dom}_2 \overline{K}^*$. Then for every $w \in \mathbb{R}^n$,
$$\delta^*(w \mid D^*) = \sup_{u \in \operatorname{ri} C} \sup_{v \in D} \{K(u, v + w) - K(u,
  v)\}.$$

The formula for the support function of $C^*$ is not formalized. -/
theorem theorem_37_2_dom₂ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (w : Rn n) :
    supportFn (pairing n) (dom₂ (upperConj K)) w
      = ⨆ u ∈ ri (dom₁ K), ⨆ v ∈ dom₂ K, (K (u, v + w) - K (u, v)) :=
  supportFn_dom₂_upperConjSaddle (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp.dom₂_nonempty
    ((theorem_34_3 hK.1 hp).1 hcls).1 w

/-- **Theorem 37.2** of [rockafellar1970convex], the formula for $D^*$ with recession functions. Let
$F$ be a closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$
be closed and proper, and let $C = \operatorname{dom}_1 K$ and
$D^* = \operatorname{dom}_2 \overline{K}^*$. Then for every $w \in \mathbb{R}^n$,
$$\delta^*(w \mid D^*) = \sup_{u \in \operatorname{ri} C} (k_u 0^+)(w),$$
where $k_u 0^+$ is the recession function of the convex function $k_u = K(u, \cdot)$. -/
theorem theorem_37_2_dom₂_recessionFn (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (w : Rn n) :
    supportFn (pairing n) (dom₂ (upperConj K)) w
      = ⨆ u ∈ ri (dom₁ K), recessionFn (fun v => K (u, v)) w :=
  supportFn_dom₂_upperConjSaddle_eq_iSup_recessionFn (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp.dom₂_nonempty
    ((theorem_34_3 hK.1 hp).1 hcls).1 w

/-- **Corollary 37.2.1** of [rockafellar1970convex], the condition on $D^*$. Let $F$ be a closed
convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$ be closed and
proper, and let $C = \operatorname{dom}_1 K$ and $D^* = \operatorname{dom}_2 \overline{K}^*$.
Then $0 \in \operatorname{int} D^*$ if and only if the convex functions $K(u, \cdot)$,
$u \in \operatorname{ri} C$, have no common direction of recession, that is, for every
$w \neq 0$ there is a $u \in \operatorname{ri} C$ with $(K(u, \cdot) 0^+)(w) > 0$. -/
theorem corollary_37_2_1_dom₂ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) :
    (0 : Rn n) ∈ interior (dom₂ (upperConj K)) ↔
      ∀ w : Rn n, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun v => K (u, v)) w :=
  zero_mem_interior_dom₂_upperConjSaddle_iff (pairing m) (pairing n) (separatingRight_pairing n)
    hF hcl (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp ((theorem_34_3 hK.1 hp).1 hcls)

/-- **Corollary 37.2.1** of [rockafellar1970convex], the condition on $C^*$. Let $F$ be a closed
convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$ be closed and
proper, and let $D = \operatorname{dom}_2 K$ and $C^* = \operatorname{dom}_1 \underline{K}^*$.
Then $0 \in \operatorname{int} C^*$ if and only if the convex functions $-K(\cdot, v)$,
$v \in \operatorname{ri} D$, have no common direction of recession, that is, for every
$z \neq 0$ there is a $v \in \operatorname{ri} D$ with $(-K(\cdot, v) 0^+)(z) > 0$. -/
theorem corollary_37_2_1_dom₁ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) :
    (0 : Rn m) ∈ interior (dom₁ (lowerConj K)) ↔
      ∀ z : Rn m, z ≠ 0 → ∃ v ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, v))) z := by
  rw [dom₁_conjSaddle_eq (pairing m) (pairing n) hF hcl
    (properConvex_graphFn_of_properSaddleFn (pairing m) (pairing n)
        (mem_bifunSaddleClass_of_mem_Ω hK)
      hp) (mem_bifunSaddleClass_of_mem_Ω hK)]
  exact zero_mem_interior_dom₁_upperConjSaddle_iff (pairing m) (pairing n)
    (separatingLeft_pairing m) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp
    ((theorem_34_3 hK.1 hp).1 hcls)

end Thm372

/-! ### Theorem 37.3 and its two corollaries -/

section Thm373

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Theorem 37.3(a)** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$ be closed and proper, and let
$C = \operatorname{dom}_1 K$. If the convex functions $K(u, \cdot)$,
$u \in \operatorname{ri} C$, have no common direction of recession, that is, for every
$w \neq 0$ there is a $u \in \operatorname{ri} C$ with $(K(u, \cdot) 0^+)(w) > 0$, then the
saddle-value of $K$ exists.

The proof combines Corollaries 37.1.3 and 37.2.1. -/
theorem theorem_37_3_a (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K)
    (hrec : ∀ w : Rn n, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun v => K (u, v)) w) :
    HasSaddleValue K :=
  hasSaddleValue_of_no_common_direction_of_recession_snd (pairing m) (pairing n)
    (separatingRight_pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp
    ((theorem_34_3 hK.1 hp).1 hcls) hrec

/-- **Theorem 37.3(b)** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$ be closed and proper, and let
$D = \operatorname{dom}_2 K$. If the convex functions $-K(\cdot, v)$,
$v \in \operatorname{ri} D$, have no common direction of recession, that is, for every
$z \neq 0$ there is a $v \in \operatorname{ri} D$ with $(-K(\cdot, v) 0^+)(z) > 0$, then the
saddle-value of $K$ exists. -/
theorem theorem_37_3_b (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K)
    (hrec : ∀ z : Rn m, z ≠ 0 → ∃ v ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, v))) z) :
    HasSaddleValue K :=
  hasSaddleValue_of_no_common_direction_of_recession_fst (pairing m) (pairing n)
    (separatingLeft_pairing m) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp
    ((theorem_34_3 hK.1 hp).1 hcls) hrec

/-- **Theorem 37.3** of [rockafellar1970convex], the last sentence. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, and let $K \in \Omega(F)$ be closed and
proper. If both conditions (a) and (b) hold, then $\sup_u \inf_v K(u, v)$ is finite, so the
saddle-value of $K$ is finite.

Corollary 37.2.1 turns the two conditions into $0 \in \operatorname{int} C^*$ and
$0 \in \operatorname{int} D^*$. -/
theorem theorem_37_3_finite (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K)
    (hrec₂ : ∀ w : Rn n, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun v => K (u, v)) w)
    (hrec₁ : ∀ z : Rn m, z ≠ 0 → ∃ v ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, v))) z) :
    ∃ r : ℝ, maximin K = (r : EReal) := by
  have hpr := properConvex_graphFn_of_properSaddleFn (pairing m) (pairing n)
    (mem_bifunSaddleClass_of_mem_Ω hK) hp
  have h1 : (0 : Rn m) ∈ ri (dom₁ (lowerConj K)) :=
    interior_subset_intrinsicInterior ((corollary_37_2_1_dom₁ hF hcl hK hp hcls).2 hrec₁)
  have h2 : (0 : Rn n) ∈ ri (dom₂ (lowerConj K)) := by
    rw [dom₂_conjSaddle_eq (pairing m) (pairing n) hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK)]
    exact interior_subset_intrinsicInterior ((corollary_37_2_1_dom₂ hF hcl hK hp hcls).2 hrec₂)
  exact corollary_37_1_3_finite hF hcl hK hp h1 h2

/-- **Corollary 37.3.1** of [rockafellar1970convex], the case where $D$ is bounded. Let $F$ be a
closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, and let $K \in \Omega(F)$ be
closed and proper. If $D = \operatorname{dom}_2 K$ is bounded, then the saddle-value of $K$
exists.

For every $u \in \operatorname{ri}(\operatorname{dom}_1 K)$ the effective domain of
$K(u, \cdot)$ is $D$ (Theorem 34.3), so a bounded $D$ satisfies condition (a) of Theorem 37.3. -/
theorem corollary_37_3_1_dom₂ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (hbd : Bornology.IsBounded (dom₂ K)) :
    HasSaddleValue K :=
  hasSaddleValue_of_isBounded_dom₂ (pairing m) (pairing n) (separatingRight_pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp ((theorem_34_3 hK.1 hp).1 hcls) hbd

/-- **Corollary 37.3.1** of [rockafellar1970convex], the case where $C$ is bounded. Let $F$ be a
closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, and let $K \in \Omega(F)$ be
closed and proper. If $C = \operatorname{dom}_1 K$ is bounded, then the saddle-value of $K$
exists. A bounded $C$ satisfies condition (b) of Theorem 37.3. -/
theorem corollary_37_3_1_dom₁ (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (hbd : Bornology.IsBounded (dom₁ K)) :
    HasSaddleValue K :=
  hasSaddleValue_of_isBounded_dom₁ (pairing m) (pairing n) (separatingLeft_pairing m) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp ((theorem_34_3 hK.1 hp).1 hcls) hbd

end Thm373

/-! ### Corollary 37.3.2: the minimax theorem for a finite continuous saddle-function -/

section Cor3732

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Corollary 37.3.2** of [rockafellar1970convex], the case where $D$ is bounded. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be non-empty closed convex sets, and
let $K : \mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be such that $K(\cdot, v)$ is concave
and continuous on $C$ for each $v \in D$, and $K(u, \cdot)$ is convex and continuous on $D$ for
each $u \in C$. If $D$ is bounded, then
$$\sup_{u \in C} \inf_{v \in D} K(u, v) = \inf_{v \in D} \sup_{u \in C} K(u, v).$$

**Reading.** The book asks for a continuous finite concave-convex function on $C \times D$. The
statement here reads the hypotheses slice by slice. Continuity in each variable separately is
weaker than joint continuity.

The extrema are taken in $[-\infty, +\infty]$, because when only one of $C$ and $D$ is bounded,
both extrema can be infinite: for $C = \{0\}$, $D = \mathbb{R}$ and $K(u, v) = v$ both are
$-\infty$. The convexity of $D$ is part of the hypothesis that each $K(u, \cdot)$ is convex on
$D$. -/
theorem corollary_37_3_2_right (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun v => K (u, v))
    (hconc : ∀ v ∈ D, ConcaveOn ℝ C fun u => K (u, v))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C)
    (hbd : Bornology.IsBounded D) :
    (⨆ u ∈ C, ⨅ v ∈ D, ((K (u, v) : ℝ) : EReal))
      = ⨅ v ∈ D, ⨆ u ∈ C, ((K (u, v) : ℝ) : EReal) :=
  biSup_biInf_eq_biInf_biSup_of_isBounded_right (pairing m) (pairing n)
    (separatingRight_pairing n) hC hCcl hDcl hCne hDne ⟨hconc, hconv⟩ hcontD hcontC hbd

/-- **Corollary 37.3.2** of [rockafellar1970convex], the case where $C$ is bounded. Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be non-empty closed convex sets, and
let $K : \mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be such that $K(\cdot, v)$ is concave
and continuous on $C$ for each $v \in D$, and $K(u, \cdot)$ is convex and continuous on $D$ for
each $u \in C$. If $C$ is bounded, then
$$\sup_{u \in C} \inf_{v \in D} K(u, v) = \inf_{v \in D} \sup_{u \in C} K(u, v).$$

**Reading.** As in `Rockafellar.corollary_37_3_2_right`, the hypotheses are read slice by slice. -/
theorem corollary_37_3_2_left (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun v => K (u, v))
    (hconc : ∀ v ∈ D, ConcaveOn ℝ C fun u => K (u, v))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C)
    (hbd : Bornology.IsBounded C) :
    (⨆ u ∈ C, ⨅ v ∈ D, ((K (u, v) : ℝ) : EReal))
      = ⨅ v ∈ D, ⨆ u ∈ C, ((K (u, v) : ℝ) : EReal) :=
  biSup_biInf_eq_biInf_biSup_of_isBounded_left (pairing m) (pairing n)
    (separatingLeft_pairing m) hC hCcl hDcl hCne hDne ⟨hconc, hconv⟩ hcontD hcontC hbd

end Cor3732

/-! ### Theorem 37.4: subgradients are saddle-points of the tilted function -/

section Thm374

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- **Theorem 37.4** of [rockafellar1970convex], the first sentence. Let $K : \mathbb{R}^m \times
\mathbb{R}^n \to [-\infty, +\infty]$ and $(u, v), (u^*, v^*) \in \mathbb{R}^m \times
\mathbb{R}^n$. Then $(u^*, v^*) \in \partial K(u, v)$ if and only if $(u, v)$ is a saddle-point
of the function
$$(x, y) \mapsto K(x, y) - \langle x, u^* \rangle - \langle y, v^* \rangle.$$

**Generalization.** The book assumes that $K$ is concave-convex. The statement here has no
hypothesis on $K$: neither concavity, convexity nor properness.

The tilted function is `ConvexAnalysis.saddleTilt`. It subtracts the real number $\langle x, u^*
\rangle + \langle y, v^* \rangle$ in one step, so that no expression $\infty - \infty$ occurs. -/
theorem theorem_37_4 (K : Rn m × Rn n → EReal) (p q : Rn m × Rn n) :
    q ∈ subdiff K p ↔ IsSaddlePoint (saddleTilt (pairing m) (pairing n) K q) p :=
  mem_saddleSubdifferential_iff_isSaddlePoint

/-- **Theorem 37.4** of [rockafellar1970convex], convexity. For every $K : \mathbb{R}^m \times
\mathbb{R}^n \to [-\infty, +\infty]$ and every $(u, v)$, the set $\partial K(u, v)$ is convex,
because it is a product of two convex sets. -/
theorem theorem_37_4_convex (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    Convex ℝ (subdiff K p) := convex_subdiff

private theorem isClosed_subdiff₁ (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    IsClosed (subdiff₁ K p) := by
  have h : subdiff₁ K p
      = (fun y : Rn m => -y) ⁻¹' subdifferential (pairing m) (fun u => -(K (u, p.2))) p.1 := by
    ext y
    exact mem_subdiff₁_iff_neg_mem_subdifferential_neg
  rw [h]
  exact (isClosed_subdifferential _ _).preimage continuous_neg

/-- **Theorem 37.4** of [rockafellar1970convex], closedness. For every $K : \mathbb{R}^m \times
\mathbb{R}^n \to [-\infty, +\infty]$ and every $(u, v)$, the set $\partial K(u, v)$ is closed.

The proof for the factor $\partial_1 K(u, v)$ uses
`Rockafellar.mem_subdiff₁_iff_neg_mem_subdifferential_neg` and
`ConvexAnalysis.isClosed_subdifferential`. -/
theorem theorem_37_4_isClosed (K : Rn m × Rn n → EReal) (p : Rn m × Rn n) :
    IsClosed (subdiff K p) :=
  (isClosed_subdiff₁ K p).prod (isClosed_subdifferential _ _)

/-- **Theorem 37.4** of [rockafellar1970convex], the first inclusion. Let $K : \mathbb{R}^m \times
\mathbb{R}^n \to [-\infty, +\infty]$ be a closed proper concave-convex function. Then
$$\operatorname{ri}(\operatorname{dom} K) \subseteq \operatorname{dom} \partial K.$$

For $u \in \operatorname{ri}(\operatorname{dom}_1 K)$ the slice $K(u, \cdot)$ is proper with
effective domain $\operatorname{dom}_2 K$ (Theorem 34.3), so Theorem 23.4 gives a subgradient.
The concave factor is the same statement for the swapped function `ConvexAnalysis.saddleSwap K`. -/
theorem theorem_37_4_relint (hK : ConcaveConvexFn K) (hp : ProperSaddleFn K)
    (hcl : ClosedSaddleFn K) : ri (domSaddle K) ⊆ domSubdiff K := by
  have h := kernelSet_subset_domSaddleSubdifferential (Bu := pairing m) (Bx := pairing n) hK
    ((theorem_34_3 hK hp).1 hcl)
  rwa [kernelSet_eq_relint_domSaddle] at h

/-- **Theorem 37.4** of [rockafellar1970convex], the second inclusion. Let $K : \mathbb{R}^m \times
\mathbb{R}^n \to [-\infty, +\infty]$ be proper. Then
$$\operatorname{dom} \partial K \subseteq \operatorname{dom} K.$$

Only properness is used: a subgradient pair makes the point a saddle-point of the tilted
function, and Corollary 36.3.1 puts that point in $\operatorname{dom} K$. -/
theorem theorem_37_4_dom (hp : ProperSaddleFn K) : domSubdiff K ⊆ domSaddle K :=
  domSaddleSubdifferential_subset_domSaddle hp

end Thm374

/-! ### Corollary 37.4.1 -/

section Cor3741

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K L : Rn m × Rn n → EReal}

/-- **Corollary 37.4.1** of [rockafellar1970convex], the first sentence. Let $K, L : \mathbb{R}^m
\times \mathbb{R}^n \to [-\infty, +\infty]$ be equivalent concave-convex functions, with $K$
closed. Then $\partial K = \partial L$. So one can speak of the subdifferential of an
equivalence class.

The book does not assume that $K$ is closed, and the corollary without this hypothesis is not
formalized. The book tilts both functions and applies Theorem 36.4, which needs
$\operatorname{cl}_1(K - \ell) = \operatorname{cl}_1 K - \ell$ for the linear function $\ell$.
The proof here uses the equivalence of conditions (a) and (d) of Theorem 37.5 instead, and this
route needs the closedness of $K$. -/
theorem corollary_37_4_1_subdiff (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hL : ConcaveConvexFn L) (h : SaddleEquiv K L) : subdiff K = subdiff L := by
  obtain ⟨F, hFconv, hFcl, hKmem⟩ := exists_mem_Ω_of_closed hK hcl
  have hLmem : L ∈ Ω F := theorem_34_2_maximal hFconv hFcl hKmem hL h
  have hpair : ∀ M : Rn m × Rn n → EReal, M ∈ Ω F → ∀ p q : Rn m × Rn n,
      (q ∈ subdiff M p ↔ IsBifunSubgradientPair (pairing m) (pairing n) F p q) := by
    intro M hM p q
    have hb := mem_saddleSubdifferential_iff_isBifunSubgradientPair (pairing m) (pairing n) hFconv
      hFcl (mem_bifunSaddleClass_of_mem_Ω hM) p q
    simpa only [flip_pairing] using hb
  funext p
  ext q
  exact (hpair K hKmem p q).trans (hpair L hLmem p q).symm

/-- **Corollary 37.4.1** of [rockafellar1970convex], the second sentence. Let $K, L : \mathbb{R}^m
\times \mathbb{R}^n \to [-\infty, +\infty]$ be equivalent concave-convex functions, with $K$
closed. Then $K(u, v) = L(u, v)$ for every $(u, v) \in \operatorname{dom} \partial K$.

A subgradient pair at $(u, v)$ says that the conjugate of the convex slice is attained, and this
conjugate is the same for every member of the class. The book does not assume that $K$ is
closed. -/
theorem corollary_37_4_1_eq (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hL : ConcaveConvexFn L) (h : SaddleEquiv K L) {p : Rn m × Rn n} (hp : p ∈ domSubdiff K) :
    K p = L p := by
  obtain ⟨F, hFconv, hFcl, hKmem⟩ := exists_mem_Ω_of_closed hK hcl
  have hLmem : L ∈ Ω F := theorem_34_2_maximal hFconv hFcl hKmem hL h
  obtain ⟨q, hq⟩ := hp
  have hqL : q ∈ subdiff L p := by
    rw [← corollary_37_4_1_subdiff hK hcl hL h]
    exact hq
  have key : ∀ M : Rn m × Rn n → EReal, M ∈ Ω F → q ∈ subdiff M p →
      ((pairing n p.2 q.2 : ℝ) : EReal) - F p.1 q.2 = M p := by
    intro M hM hqM
    have hA : convexConj (pairing n).flip (fun v => M (p.1, v)) = F p.1 :=
      congrFun (bifunOfSaddle_eq_of_mem_bifunSaddleClass (pairing m) (pairing n) hFconv hFcl
        (mem_bifunSaddleClass_of_mem_Ω hM)) p.1
    rw [flip_pairing] at hA
    have hsub : convexConj (pairing n) (fun v => M (p.1, v)) q.2
        = ((pairing n p.2 q.2 : ℝ) : EReal) - M (p.1, p.2) :=
      mem_subdifferential_iff_convexConj_eq.1 hqM.2
    rw [hA] at hsub
    exact eq_coe_sub_iff_coe_sub_eq.1 hsub
  exact (key K hKmem hq).symm.trans (key L hLmem hqL)

end Cor3741

/-! ### Theorem 37.5 -/

section Thm375

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Theorem 37.5** of [rockafellar1970convex], the function $f$. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then the graph function
$f(u, v^*) = (Fu)(v^*)$ of $F$ satisfies
$$f(u, v^*) = \sup_v \{\langle v, v^* \rangle - K(u, v)\}$$
for all $u \in \mathbb{R}^m$ and $v^* \in \mathbb{R}^n$. It is the function of Theorem 34.2.

The function $f$ is a closed convex function on $\mathbb{R}^{m+n}$, here read as a function on
$\mathbb{R}^m \times \mathbb{R}^n$. -/
theorem theorem_37_5_f (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F) (u : Rn m)
    (w : Rn n) : graphFn F (u, w) = ⨆ v : Rn n, (((pairing n v w : ℝ) : EReal) - K (u, v)) := by
  have hA : convexConj (pairing n).flip (fun v => K (u, v)) = F u :=
    congrFun (bifunOfSaddle_eq_of_mem_bifunSaddleClass (pairing m) (pairing n) hF hcl
      (mem_bifunSaddleClass_of_mem_Ω hK)) u
  rw [flip_pairing] at hA
  have hg : graphFn F (u, w) = F u w := rfl
  rw [hg, ← hA, convexConj_apply]

/-- **Theorem 37.5** of [rockafellar1970convex], condition (a) against condition (d). Let $F$ be a
closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then
$(u^*, v^*) \in \partial K(u, v)$ if and only if condition (d) holds:
$$(Fu)(v^*) - \langle v, v^* \rangle = (F^* v)(u^*) - \langle u, u^* \rangle.$$

Condition (d) is `ConvexAnalysis.IsBifunSubgradientPair` for $p = (u, v)$ and $q = (u^*, v^*)$.
It mentions only $F$, so this statement also says that $\partial K$ depends only on the
equivalence class of $K$. -/
theorem theorem_37_5_a (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (p q : Rn m × Rn n) :
    q ∈ subdiff K p ↔ IsBifunSubgradientPair (pairing m) (pairing n) F p q := by
  have h := mem_saddleSubdifferential_iff_isBifunSubgradientPair (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) p q
  simpa only [flip_pairing] using h

/-- **Theorem 37.5** of [rockafellar1970convex], condition (b) against condition (d). Let $F$ be a
closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then
$(u, v) \in \partial \overline{K}^*(u^*, v^*)$ if and only if condition (d) holds.

With condition (a), this says that the subdifferentials of two conjugate classes are inverse to
each other, as $\partial f^* = (\partial f)^{-1}$ for a closed convex function $f$. -/
theorem theorem_37_5_b (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (p q : Rn m × Rn n) :
    p ∈ subdiff (upperConj K) q ↔ IsBifunSubgradientPair (pairing m) (pairing n) F p q := by
  have h := mem_saddleSubdifferential_upperConjSaddle_iff (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) p q
  simpa only [flip_pairing] using h

/-- **Theorem 37.5** of [rockafellar1970convex], condition (c) against condition (d). Let $F$ be a
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ with graph function $f(u, v^*) = (Fu)(v^*)$.
Then condition (d) holds for $(u, v)$ and $(u^*, v^*)$ if and only if
$$(-u^*, v) \in \partial f(u, v^*).$$

So $\partial K$ is a partial inversion of $\partial f$: the second components of the point and
of the subgradient are exchanged, and the first component of the subgradient is negated. This
transfers closedness, the parametrization of Minty and maximal monotonicity to $\partial K$, and
it is the source of the asymmetry in Corollaries 37.5.1 and 37.5.2. The subdifferential
$\partial f$ is taken with respect to the product pairing `Rockafellar.pairingProd`. No
hypothesis on $F$ is needed. -/
theorem theorem_37_5_c (F : Bifun (Rn m) (Rn n)) (p q : Rn m × Rn n) :
    IsBifunSubgradientPair (pairing m) (pairing n) F p q ↔
      (-q.1, p.2) ∈ subdifferential (pairingProd m n) (graphFn F) (p.1, q.2) :=
  isBifunSubgradientPair_iff_mem_subdifferential_graphFn (pairing m) (pairing n) F p q

/-- **Theorem 37.5** of [rockafellar1970convex], condition (d). For every bifunction $F$ from
$\mathbb{R}^m$ to $\mathbb{R}^n$ and all $(u, v), (u^*, v^*) \in \mathbb{R}^m \times
\mathbb{R}^n$, condition (d) is the equation
$$(Fu)(v^*) - \langle v, v^* \rangle = (F^* v)(u^*) - \langle u, u^* \rangle.$$

It is the case of equality in the chain $\langle v, v^* \rangle - (Fu)(v^*) \le \langle F u, v
\rangle \le K(u, v) \le \langle u, F^* v \rangle \le \langle u, u^* \rangle - (F^* v)(u^*)$ for
$K \in \Omega(F)$. It mentions no member of the class, and conditions (a), (b) and (c) are
stated against it. -/
theorem theorem_37_5_d (F : Bifun (Rn m) (Rn n)) (p q : Rn m × Rn n) :
    IsBifunSubgradientPair (pairing m) (pairing n) F p q ↔
      F p.1 q.2 - ((pairing n q.2 p.2 : ℝ) : EReal)
        = dualProgram F p.2 q.1 - ((pairing m p.1 q.1 : ℝ) : EReal) := Iff.rfl

end Thm375

/-! ### Corollaries 37.5.1 and 37.5.2 -/

section Cor3751

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

private theorem continuous_pairing (n : ℕ) :
    Continuous fun r : Rn n × Rn n => pairing n r.1 r.2 := continuous_inner

/-- **Corollary 37.5.1** of [rockafellar1970convex], closedness. Let $F$ be a closed proper convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then the graph $\{((u,
v), (u^*, v^*)) \mid (u^*, v^*) \in \partial K(u, v)\}$ of $\partial K$ is closed.

By condition (c) of Theorem 37.5 the graph is the preimage of the graph of $\partial f$ under a
linear homeomorphism, and Theorem 24.4 applies. -/
theorem corollary_37_5_1_isClosed (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hK : K ∈ Ω F) :
    IsClosed {r : (Rn m × Rn n) × (Rn m × Rn n) | r.2 ∈ subdiff K r.1} := by
  have h := isClosed_setOf_mem_saddleSubdifferential (pairing m) (pairing n) (continuous_pairing m)
    (continuous_pairing n) hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK)
  simpa only [flip_pairing] using h

/-- **Corollary 37.5.1** of [rockafellar1970convex], the homeomorphism. Let $F$ be a closed proper
convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. This is a
homeomorphism from the graph of $\partial K$ onto $\mathbb{R}^m \times \mathbb{R}^n$, given by
$$((u, v), (u^*, v^*)) \mapsto (u - u^*, v^* + v)$$
(`Rockafellar.corollary_37_5_1_homeomorph_apply`).

The map is not symmetric in the two variables: it is the parametrization of Minty from Corollary
31.5.1 composed with the partial inversion of condition (c) of Theorem 37.5. $F$ is an explicit
argument because a homeomorphism is data; `Rockafellar.corollary_37_5_1_exists_homeomorph` is
the form of the book. -/
noncomputable def corollary_37_5_1_homeomorph (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hK : K ∈ Ω F) :
    ↥{r : (Rn m × Rn n) × (Rn m × Rn n) | r.2 ∈ subdiff K r.1} ≃ₜ (Rn m × Rn n) :=
  saddleSubdifferentialHomeomorph hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK)

/-- The homeomorphism `Rockafellar.corollary_37_5_1_homeomorph` maps $((u, v), (u^*, v^*))$ to
$(u - u^*, v^* + v)$. The book prints the second component as $v + v^*$, which is the same
vector. -/
theorem corollary_37_5_1_homeomorph_apply (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hK : K ∈ Ω F)
    (r : ↥{r : (Rn m × Rn n) × (Rn m × Rn n) | r.2 ∈ subdiff K r.1}) :
    corollary_37_5_1_homeomorph hF hcl hpr hK r = (r.1.1.1 - r.1.2.1, r.1.2.2 + r.1.1.2) :=
  saddleSubdifferentialHomeomorph_apply hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK) r

/-- **Corollary 37.5.1** of [rockafellar1970convex]. Let $K : \mathbb{R}^m \times \mathbb{R}^n \to
[-\infty, +\infty]$ be a closed proper concave-convex function. Then the graph of $\partial K$
is homeomorphic to $\mathbb{R}^m \times \mathbb{R}^n$. -/
theorem corollary_37_5_1_exists_homeomorph (hK : ConcaveConvexFn K) (hcl : ClosedSaddleFn K)
    (hp : ProperSaddleFn K) :
    Nonempty (↥{r : (Rn m × Rn n) × (Rn m × Rn n) | r.2 ∈ subdiff K r.1} ≃ₜ (Rn m × Rn n)) := by
  obtain ⟨F, hFconv, hFcl, hmem⟩ := exists_mem_Ω_of_closed hK hcl
  exact ⟨corollary_37_5_1_homeomorph hFconv hFcl
    (properConvex_graphFn_of_properSaddleFn (pairing m) (pairing n)
      (mem_bifunSaddleClass_of_mem_Ω hmem) hp) hmem⟩

/-- **Corollary 37.5.2** of [rockafellar1970convex]. Let $F$ be a closed proper convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then the mapping
$$\rho : (u, v) \mapsto \{(-u^*, v^*) \mid (u^*, v^*) \in \partial K(u, v)\}$$
is a maximal monotone mapping from $\mathbb{R}^m \times \mathbb{R}^n$ to itself.

The change of sign $u^* \mapsto -u^*$ is part of the definition of $\rho$. The set $\partial K$
is a set of supergradients in the first argument and of subgradients in the second, so
$\partial K$ itself is monotone in one variable and antitone in the other. Monotonicity is
`ConvexAnalysis.IsMaximalMonotoneRel` for the product pairing `Rockafellar.pairingProd`. -/
theorem corollary_37_5_2 (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F))
    (hK : K ∈ Ω F) :
    IsMaximalMonotoneRel (pairingProd m n)
      {r : (Rn m × Rn n) × (Rn m × Rn n) | (-r.2.1, r.2.2) ∈ subdiff K r.1} := by
  have h := isMaximalMonotoneRel_saddleMonotoneRel hF hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK)
  have he : saddleMonotoneRel (pairing m) (pairing n) K
      = {r : (Rn m × Rn n) × (Rn m × Rn n) | (-r.2.1, r.2.2) ∈ subdiff K r.1} := by
    ext r
    simp only [mem_saddleMonotoneRel, flip_pairing, Set.mem_ofPred_eq]
  rwa [he] at h

/-- **Corollary 37.5.2** of [rockafellar1970convex], the case of a differentiable function. Let $K :
\mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be concave-convex on all of
$\mathbb{R}^m \times \mathbb{R}^n$ and differentiable everywhere. Then the mapping $(u, v)
\mapsto (-\nabla_1 K(u, v), \nabla_2 K(u, v))$ is maximal monotone.

The gradient is a pair of vectors and not a vector of $\mathbb{R}^{m+n}$, because Mathlib gives
a product of inner product spaces the supremum norm; see `ConvexAnalysis.HasSaddleGradientAt`. -/
theorem corollary_37_5_2_gradient {K : Rn m × Rn n → ℝ}
    (hK : ConcaveConvexOn (Set.univ : Set (Rn m)) (Set.univ : Set (Rn n)) K)
    (hdiff : ∀ p : Rn m × Rn n, DifferentiableAt ℝ K p) :
    IsMaximalMonotoneRel (pairingProd m n)
      {r : (Rn m × Rn n) × (Rn m × Rn n) | HasSaddleGradientAt K (-r.2.1, r.2.2) r.1} :=
  isMaximalMonotoneRel_setOf_hasSaddleGradientAt hK hdiff

end Cor3751

/-! ### Corollary 37.5.3 -/

section Cor3753

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Corollary 37.5.3** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then
$(u, v) \in \partial \overline{K}^*(0, 0)$ if and only if $(u, v)$ is a saddle-point of $K$.

The proof is condition (b) of Theorem 37.5 at the origin, combined with Theorem 37.4, where the
tilt by the origin is $K$ itself. -/
theorem corollary_37_5_3 (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (p : Rn m × Rn n) : p ∈ subdiff (upperConj K) 0 ↔ IsSaddlePoint K p := by
  have h := mem_saddleSubdifferential_upperConjSaddle_zero_iff (pairing m) (pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) p
  simpa only [flip_pairing] using h

/-- **Corollary 37.5.3** of [rockafellar1970convex], convexity. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then the set of
saddle-points of $K$ is convex. It is a product set, since it is $\partial
\overline{K}^*(0, 0) = \partial_1 \overline{K}^*(0, 0) \times \partial_2 \overline{K}^*(0, 0)$. -/
theorem corollary_37_5_3_convex (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F) :
    Convex ℝ {p : Rn m × Rn n | IsSaddlePoint K p} :=
  convex_setOf_isSaddlePoint (pairing m) (pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK)

/-- **Corollary 37.5.3** of [rockafellar1970convex], closedness. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then the set of
saddle-points of $K$ is closed. -/
theorem corollary_37_5_3_isClosed (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F) :
    IsClosed {p : Rn m × Rn n | IsSaddlePoint K p} := by
  have hset : {p : Rn m × Rn n | IsSaddlePoint K p} = subdiff (upperConj K) 0 := by
    ext p
    exact (corollary_37_5_3 hF hcl hK p).symm
  rw [hset]
  exact theorem_37_4_isClosed _ _

/-- **Corollary 37.5.3** of [rockafellar1970convex], the last sentence. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. Then $K$ has a
saddle-point if and only if $(0, 0) \in \operatorname{dom} \partial \overline{K}^*$. -/
theorem corollary_37_5_3_exists_iff (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hK : K ∈ Ω F) :
    (∃ p, IsSaddlePoint K p) ↔ (0 : Rn m × Rn n) ∈ domSubdiff (upperConj K) := by
  have h := exists_isSaddlePoint_iff_zero_mem_domSaddleSubdifferential (pairing m) (pairing n) hF
    hcl (mem_bifunSaddleClass_of_mem_Ω hK)
  simpa only [flip_pairing] using h

/-- **Corollary 37.5.3** of [rockafellar1970convex], the sufficient condition. Let $F$ be a closed
proper convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ and $K \in \Omega(F)$. If $(0, 0)
\in \operatorname{ri}(\operatorname{dom} \overline{K}^*)$, then $K$ has a saddle-point. The
proof applies Theorem 37.4 to $\overline{K}^*$. -/
theorem corollary_37_5_3_exists_of_relint (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (hK : K ∈ Ω F)
    (h0 : (0 : Rn m × Rn n) ∈ ri (domSaddle (upperConj K))) : ∃ p, IsSaddlePoint K p := by
  refine exists_isSaddlePoint_of_zero_mem_kernelSet_upperConjSaddle (pairing m) (pairing n) hF
    hcl hpr (mem_bifunSaddleClass_of_mem_Ω hK) ?_
  rwa [← kernelSet_eq_relint_domSaddle] at h0

end Cor3753

/-! ### Theorem 37.6 and its two corollaries -/

section Thm376

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)} {K : Rn m × Rn n → EReal}

/-- **Theorem 37.6** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$, let $K \in \Omega(F)$ be closed and proper, and let
$C = \operatorname{dom}_1 K$ and $D = \operatorname{dom}_2 K$. Assume that the convex functions
$K(u, \cdot)$, $u \in \operatorname{ri} C$, have no common direction of recession, and that the
convex functions $-K(\cdot, v)$, $v \in \operatorname{ri} D$, have no common direction of
recession. Then $K$ has a saddle-point.

Corollary 37.2.1 turns the two conditions into $(0, 0) \in \operatorname{ri}(\operatorname{dom}
\overline{K}^*)$, and Corollary 37.5.3 gives the saddle-point. -/
theorem theorem_37_6 (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K)
    (hrec₂ : ∀ w : Rn n, w ≠ 0 → ∃ u ∈ ri (dom₁ K), 0 < recessionFn (fun v => K (u, v)) w)
    (hrec₁ : ∀ z : Rn m, z ≠ 0 → ∃ v ∈ ri (dom₂ K), 0 < recessionFn (fun u => -(K (u, v))) z) :
    ∃ q, IsSaddlePoint K q :=
  exists_isSaddlePoint_of_no_common_direction_of_recession (pairing m) (pairing n)
    (separatingLeft_pairing m) (separatingRight_pairing n) hF hcl
    (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp ((theorem_34_3 hK.1 hp).1 hcls) hrec₂ hrec₁

/-- **Theorem 37.6** of [rockafellar1970convex], the parenthetical remark. Every saddle-point of a
proper function $K : \mathbb{R}^m \times \mathbb{R}^n \to [-\infty, +\infty]$ lies in
$C \times D = \operatorname{dom} K$. -/
theorem theorem_37_6_mem_dom (hp : ProperSaddleFn K) {q : Rn m × Rn n} (hq : IsSaddlePoint K q) :
    q ∈ domSaddle K :=
  IsSaddlePoint.mem_domSaddle hp hq

/-- **Corollary 37.6.1** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$, and let $K \in \Omega(F)$ be closed and proper. If
$C = \operatorname{dom}_1 K$ and $D = \operatorname{dom}_2 K$ are both bounded, then $K$ has a
saddle-point.

For $u \in \operatorname{ri} C$ and $v \in \operatorname{ri} D$ the slices have the effective
domains $D$ and $C$ (Theorem 34.3), so both conditions of Theorem 37.6 hold. -/
theorem corollary_37_6_1 (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (hbd₁ : Bornology.IsBounded (dom₁ K))
    (hbd₂ : Bornology.IsBounded (dom₂ K)) : ∃ q, IsSaddlePoint K q :=
  exists_isSaddlePoint_of_isBounded_domSaddle (pairing m) (pairing n) (separatingLeft_pairing m)
    (separatingRight_pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp
    ((theorem_34_3 hK.1 hp).1 hcls) hbd₁ hbd₂

/-- **Corollary 37.6.1** of [rockafellar1970convex], the second clause. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, and let $K \in \Omega(F)$ be closed and
proper. If $\operatorname{dom}_1 K$ and $\operatorname{dom}_2 K$ are both bounded, then
$\sup_u \inf_v K(u, v)$ is finite, so the saddle-value is finite. It is the value of $K$ at a
saddle-point. -/
theorem corollary_37_6_1_finite (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hK : K ∈ Ω F)
    (hp : ProperSaddleFn K) (hcls : ClosedSaddleFn K) (hbd₁ : Bornology.IsBounded (dom₁ K))
    (hbd₂ : Bornology.IsBounded (dom₂ K)) : ∃ r : ℝ, maximin K = (r : EReal) :=
  exists_maximin_eq_coe_of_isBounded_domSaddle (pairing m) (pairing n) (separatingLeft_pairing m)
    (separatingRight_pairing n) hF hcl (mem_bifunSaddleClass_of_mem_Ω hK) hK.1 hp
    ((theorem_34_3 hK.1 hp).1 hcls) hbd₁ hbd₂

end Thm376

/-! ### Corollary 37.6.2: the minimax theorem -/

section Cor3762

variable {m n : ℕ} {C : Set (Rn m)} {D : Set (Rn n)} {K : Rn m × Rn n → ℝ}

/-- **Corollary 37.6.2** of [rockafellar1970convex] (the minimax theorem). Let
$C \subseteq \mathbb{R}^m$ and $D \subseteq \mathbb{R}^n$ be non-empty closed bounded convex
sets, and let $K : \mathbb{R}^m \times \mathbb{R}^n \to \mathbb{R}$ be such that $K(\cdot, v)$
is concave and continuous on $C$ for each $v \in D$, and $K(u, \cdot)$ is convex and continuous
on $D$ for each $u \in C$. Then there are $\bar u \in C$ and $\bar v \in D$ with
$$K(u, \bar v) \le K(\bar u, \bar v) \le K(\bar u, v) \qquad \text{for all } u \in C, v \in D.$$

**Reading.** The book asks for a continuous finite concave-convex function on $C \times D$. The
statement here reads the hypotheses slice by slice. Continuity in each variable separately is
weaker than joint continuity.

The lower simple extension of $K$ is a closed proper saddle-function with effective domain
$C \times D$. Corollary 37.6.1 gives it a saddle-point, and Corollary 36.3.1 puts that point in
$C \times D$. The convexity of $D$ is part of the hypothesis that each $K(u, \cdot)$ is convex
on $D$. -/
theorem corollary_37_6_2 (hC : Convex ℝ C) (hCcl : IsClosed C) (hDcl : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) (hconv : ∀ u ∈ C, ConvexOn ℝ D fun v => K (u, v))
    (hconc : ∀ v ∈ D, ConcaveOn ℝ C fun u => K (u, v))
    (hcontD : ∀ u ∈ C, ContinuousOn (fun v => K (u, v)) D)
    (hcontC : ∀ v ∈ D, ContinuousOn (fun u => K (u, v)) C)
    (hbdC : Bornology.IsBounded C) (hbdD : Bornology.IsBounded D) :
    ∃ q : Rn m × Rn n, q.1 ∈ C ∧ q.2 ∈ D ∧
      (∀ u ∈ C, K (u, q.2) ≤ K q) ∧ ∀ v ∈ D, K q ≤ K (q.1, v) :=
  exists_saddlePoint_of_isBounded (pairing m) (pairing n) (separatingLeft_pairing m)
    (separatingRight_pairing n) hC hCcl hDcl hCne hDne ⟨hconc, hconv⟩ hcontD hcontC hbdC hbdD

end Cor3762

end Rockafellar
