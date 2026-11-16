/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.HellyRefined
import NumlibSurface.Rockafellar.Common.Euclidean

/-!
# Rockafellar, Section 21: Helly's theorem and systems of inequalities

This module formalizes Section 21 of [rockafellar1970convex]: existence theorems for systems of
convex inequalities, stated as pairs of mutually exclusive alternatives, and the forms of Helly's
theorem that follow from them. A system of convex inequalities in $\mathbb{R}^n$ consists of
conditions $f_i(x) \le \alpha_i$ for $i \in I_1$ and $f_i(x) < \alpha_i$ for $i \in I_2$, with
arbitrary index sets and $-\infty \le \alpha_i \le +\infty$. The basic alternative (Theorem 21.1)
says that either the strict system $f_1(x) < 0, \dots, f_m(x) < 0$ has a solution in a convex set
$C$, or some nontrivial nonnegative combination $\lambda_1 f_1 + \dots + \lambda_m f_m$ is
nonnegative on $C$. Theorem 21.2 allows affine constraints in addition, Theorem 21.3 treats infinite
systems of weak inequalities under a recession hypothesis, and Theorems 21.4 and 21.5 weaken that
hypothesis when finitely many constraints are affine or polyhedral.

Helly's theorem appears in two forms. For an arbitrary collection of nonempty closed convex sets
with no common direction of recession, if every $n + 1$ or fewer of the sets meet, then all of them
meet (Corollary 21.3.2). For a finite collection of convex sets, neither closedness nor a recession
hypothesis is needed (Theorem 21.6). The proofs specialize `Numlib.Analysis.Convex.HellyRefined` and
the separation and recession theory of `Numlib.Analysis.Convex`.

## Main definitions

* `Rockafellar.ConvexSystem`: a system of weak and strict inequalities $f_i(x) \le \alpha_i$,
  $f_j(x) < \alpha_j$ with extended-real functions and right-hand sides.
* `Rockafellar.ConvexSystem.solutions`, `Rockafellar.ConvexSystem.Consistent`: the solution set of a
  system, and the condition that it is nonempty.
* `Rockafellar.IsAffineFn`: an extended-real function of the form
  $x \mapsto \langle x, b \rangle - \beta$.

## Main results

* Theorem 21.1, `Rockafellar.theorem_21_1`, `Rockafellar.theorem_21_1_exclusive`: either
  $f_1(x) < 0, \dots, f_m(x) < 0$ for some $x \in C$, or $\sum_i \lambda_i f_i \ge 0$ on $C$ for
  some $\lambda \ge 0$, $\lambda \ne 0$, and not both.
* Theorem 21.2, `Rockafellar.theorem_21_2`, `Rockafellar.theorem_21_2_exclusive`: the same
  alternative for a system with convex strict and affine weak constraints.
* Theorem 21.3, `Rockafellar.theorem_21_3`, `Rockafellar.theorem_21_3_exclusive`: the alternative
  for an infinite system of weak inequalities under a recession hypothesis, with at most $n + 1$
  nonzero multipliers.
* Corollary 21.3.1, `Rockafellar.corollary_21_3_1`: an infinite system is solvable if every
  subsystem of at most $n + 1$ inequalities is solvable to within every $\varepsilon > 0$.
* Corollary 21.3.2, `Rockafellar.corollary_21_3_2` (Helly's theorem): closed convex sets with no
  common direction of recession meet if every $n + 1$ or fewer of them meet.
* `Rockafellar.helly_recession_iff_exists_isBounded`: the exercise after Corollary 21.3.2; the
  recession hypothesis of Helly's theorem holds if and only if some finite subcollection has a
  bounded intersection.
* Theorem 21.4, `Rockafellar.theorem_21_4`, `Rockafellar.theorem_21_4_subsystem`: on
  $C = \mathbb{R}^n$, the recession hypothesis of Theorem 21.3 and Corollary 21.3.1 may be weakened
  when finitely many $f_i$ are affine.
* Theorem 21.5, `Rockafellar.theorem_21_5`: the recession hypothesis of Helly's theorem may be
  weakened when finitely many sets are polyhedral.
* Theorem 21.6, `Rockafellar.theorem_21_6`: Helly's theorem for a finite collection of convex sets.
* Corollary 21.6.1, `Rockafellar.corollary_21_6_1`: a finite system of strict and weak convex
  inequalities is solvable in $C$ if every subsystem of $n + 1$ or fewer inequalities is.
* Corollary 21.6.2, `Rockafellar.corollary_21_6_2`, `Rockafellar.corollary_21_6_2_affine`: in
  Theorems 21.1 and 21.2, at most $n + 1$ of the multipliers need be nonzero.

## Conventions

* $\mathbb{R}^n$ is `Rockafellar.Rn n`. The inner product $\langle x, y \rangle$ is
  `Rockafellar.pairing n x y`.
* The functions $f_i$ take values in `EReal`, and a weighted sum $\sum_i \lambda_i f_i(x)$ is formed
  in `EReal`, where $0 \cdot (+\infty) = 0$. Without this convention a zero multiplier could not
  remove a constraint whose function is $+\infty$ somewhere, and Corollary 21.6.2, which extends a
  short multiplier vector by zeros, would be false.
* The numbered theorems take right-hand sides $0$. A finite right-hand side reduces to this case by
  `Rockafellar.ConvexSystem.solutions_normalize`.
* "One and only one of the alternatives holds" is stated in two parts: `theorem_21_k` gives the
  disjunction, and `theorem_21_k_exclusive` says that the alternatives cannot both hold.

## Implementation notes

* Theorem 21.1 assumes $\operatorname{dom} f_i \supseteq \operatorname{ri} C$, not
  $\operatorname{dom} f_i \supseteq C$. This is the hypothesis of the source: separation gives the
  inequality only where every $f_i$ is finite, and Corollary 7.3.3 carries it from
  $\operatorname{ri} C$ to $\operatorname{cl} C \supseteq C$.
* Theorem 21.6 is proved from Radon's theorem, not from Corollary 21.3.2 as in the source. Therefore
  Corollaries 21.6.1 and 21.6.2 do not depend on Theorem 21.3.

## Deviations from the source

* **Comments and References for Part IV** (typo). The source cites a "Corollary 21.3.3", which does
  not exist; the intended reference is Corollary 21.3.2, Helly's theorem.
-/

open Set

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ}

/-! ### A system of convex inequalities -/

/-- **Section 21** of [rockafellar1970convex], system of convex inequalities. A **system of convex
inequalities** in $\mathbb{R}^n$ consists of functions
$f_i : \mathbb{R}^n \to [-\infty, +\infty]$ and right-hand sides
$\alpha_i \in [-\infty, +\infty]$, and asks for $x$ with
$$f_i(x) \le \alpha_i \quad (i \in I_1), \qquad f_j(x) < \alpha_j \quad (j \in I_2),$$
where the index sets $I_1$ and $I_2$ are arbitrary.

The index set $I_1$ is the type `ι` and $I_2$ is the type `κ`. Convexity of the $f_i$ is not
part of the structure: the statements about the solution set carry it as a hypothesis. -/
structure ConvexSystem (n : ℕ) (ι κ : Type*) where
  /-- The functions $f_i$, $i \in I_1$, of the weak inequalities $f_i(x) \le \alpha_i$. -/
  weakFn : ι → Rn n → EReal
  /-- The right-hand sides $\alpha_i \in [-\infty, +\infty]$ of the weak inequalities. -/
  weakBound : ι → EReal
  /-- The functions $f_j$, $j \in I_2$, of the strict inequalities $f_j(x) < \alpha_j$. -/
  strictFn : κ → Rn n → EReal
  /-- The right-hand sides $\alpha_j \in [-\infty, +\infty]$ of the strict inequalities. -/
  strictBound : κ → EReal

namespace ConvexSystem

variable {ι κ : Type*}

/-- **Section 21** of [rockafellar1970convex], solution set. The **solution set** of a system of
convex inequalities is the set of $x \in \mathbb{R}^n$ with $f_i(x) \le \alpha_i$ for every
$i \in I_1$ and $f_j(x) < \alpha_j$ for every $j \in I_2$. -/
def solutions (S : ConvexSystem n ι κ) : Set (Rn n) :=
  {x | (∀ i, S.weakFn i x ≤ S.weakBound i) ∧ ∀ j, S.strictFn j x < S.strictBound j}

/-- **Section 21** of [rockafellar1970convex], consistency. A system of convex inequalities is
**consistent** if its solution set is nonempty. -/
def Consistent (S : ConvexSystem n ι κ) : Prop := S.solutions.Nonempty

/-- **Section 21** of [rockafellar1970convex], p. 185. The solution set of a system of convex
inequalities is the intersection of the sets $\{x \mid f_i(x) \le \alpha_i\}$, $i \in I_1$, and
$\{x \mid f_j(x) < \alpha_j\}$, $j \in I_2$. -/
theorem solutions_eq_iInter (S : ConvexSystem n ι κ) :
    S.solutions = (⋂ i, {x | S.weakFn i x ≤ S.weakBound i})
      ∩ ⋂ j, {x | S.strictFn j x < S.strictBound j} := by
  ext x
  simp [solutions]

/-- **Section 21** of [rockafellar1970convex], p. 185. If every function $f_i$, $i \in I_1$, and
every function $f_j$, $j \in I_2$, of a system of convex inequalities is convex, then the
solution set is convex. -/
theorem convex_solutions (S : ConvexSystem n ι κ) (hw : ∀ i, ConvexFn (S.weakFn i))
    (hs : ∀ j, ConvexFn (S.strictFn j)) : Convex ℝ S.solutions := by
  rw [solutions_eq_iInter]
  exact Convex.inter (convex_iInter fun i => (hw i).convex_le _)
    (convex_iInter fun j => (hs j).convex_lt _)

/-- Let $f : \mathbb{R}^n \to [-\infty, +\infty]$ be closed. Then for every
$\alpha \in [-\infty, +\infty]$ the level set $\{x \mid f(x) \le \alpha\}$ is closed.

The level $\alpha$ may be infinite; `ConvexAnalysis.lowerSemicontinuous_iff_isClosed_le` covers
only finite levels. -/
theorem isClosed_setOf_le {f : Rn n → EReal} (hf : ClosedConvex f) (a : EReal) :
    IsClosed {x : Rn n | f x ≤ a} := by
  induction a using EReal.rec with
  | bot =>
    rcases closedConvex_iff.1 hf with rfl | ⟨-, hne⟩
    · simp
    · have hempty : {x : Rn n | f x ≤ ⊥} = (∅ : Set (Rn n)) := by
        ext x
        simpa using hne x
      rw [hempty]
      exact isClosed_empty
  | coe r => exact lowerSemicontinuous_iff_isClosed_le.1 hf.lowerSemicontinuous r
  | top => simp

/-- **Section 21** of [rockafellar1970convex], p. 185. If a system of convex inequalities has no
strict inequalities ($I_2 = \emptyset$) and every $f_i$, $i \in I_1$, is closed, then its
solution set is closed. -/
theorem isClosed_solutions [IsEmpty κ] (S : ConvexSystem n ι κ)
    (hw : ∀ i, ClosedConvex (S.weakFn i)) : IsClosed S.solutions := by
  rw [solutions_eq_iInter]
  have hstrict : (⋂ j, {x : Rn n | S.strictFn j x < S.strictBound j}) = (univ : Set (Rn n)) := by
    simp
  rw [hstrict, Set.inter_univ]
  exact isClosed_iInter fun i => isClosed_setOf_le (hw i) _

/-- **Section 21** of [rockafellar1970convex], p. 186. Let $f : \mathbb{R}^n \to [-\infty, +\infty]$
and let $\alpha \in \mathbb{R}$. Then $f(x) \le \alpha$ if and only if $f(x) - \alpha \le 0$,
and $f(x) < \alpha$ if and only if $f(x) - \alpha < 0$.

This justifies the right-hand sides $0$ in the numbered theorems. -/
theorem solutions_normalize (f : Rn n → EReal) (a : ℝ) (x : Rn n) :
    (f x ≤ (a : EReal) ↔ f x - (a : EReal) ≤ 0) ∧ (f x < (a : EReal) ↔ f x - (a : EReal) < 0) := by
  generalize f x = y
  induction y using EReal.rec with
  | bot => simp
  | coe r =>
    rw [← EReal.coe_sub]
    norm_cast
    exact ⟨⟨fun h => by linarith, fun h => by linarith⟩,
      ⟨fun h => by linarith, fun h => by linarith⟩⟩
  | top => simp

end ConvexSystem

/-- **Section 21** of [rockafellar1970convex], p. 186. A linear equation is a pair of linear
inequalities: for $x, b \in \mathbb{R}^n$ and $\beta \in \mathbb{R}$,
$$\langle x, b \rangle = \beta \iff \langle x, b \rangle \le \beta \text{ and } \langle x, -b
  \rangle \le -\beta.$$
-/
theorem pairing_eq_iff (x b : Rn n) (β : ℝ) :
    pairing n x b = β ↔ pairing n x b ≤ β ∧ pairing n x (-b) ≤ -β := by
  rw [map_neg]
  constructor
  · rintro h
    simp [h]
  · rintro ⟨h₁, h₂⟩
    linarith

/-! ### Theorem 21.1 -/

/-- **Theorem 21.1** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be convex, and let
$f_1, \dots, f_m$, $m \ge 1$, be proper convex functions on $\mathbb{R}^n$ with
$\operatorname{dom} f_i \supseteq \operatorname{ri} C$ for every $i$. Then at least one of the
following holds:

(a) there is $x \in C$ with $f_1(x) < 0, \dots, f_m(x) < 0$;

(b) there are real numbers $\lambda_1, \dots, \lambda_m \ge 0$, not all zero, such that
$$\lambda_1 f_1(x) + \dots + \lambda_m f_m(x) \ge 0 \quad \text{for every } x \in C.$$

The source says that exactly one of (a) and (b) holds. This declaration gives the disjunction,
and `Rockafellar.theorem_21_1_exclusive` shows that (a) and (b) cannot both hold. The index set
$\{1, \dots, m\}$ is a nonempty finite type `ι`, and the weighted sum is formed in `EReal`. -/
theorem theorem_21_1 {ι : Type*} [Fintype ι] [Nonempty ι] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
        (hp : ∀ i, ProperConvex (f i))
    (hdom : ∀ i, ri C ⊆ convexDom (f i)) :
    (∃ x ∈ C, ∀ i, f i x < 0) ∨
      ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ l ≠ 0 ∧
        ∀ x ∈ C, (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x :=
  alternative_of_convex_system hC hf hp hdom

/-- **Theorem 21.1** of [rockafellar1970convex], exclusivity. Let $C \subseteq \mathbb{R}^n$, let
$f_1, \dots, f_m$ be functions on $\mathbb{R}^n$ with values in $[-\infty, +\infty]$, and let
$\lambda_1, \dots, \lambda_m \ge 0$ be not all zero with $\sum_i \lambda_i f_i(x) \ge 0$ for
every $x \in C$. Then there is no $x \in C$ with $f_i(x) < 0$ for every $i$.

No hypothesis on $C$ or the $f_i$ is needed: at a point where every $f_i$ is negative, every
term $\lambda_i f_i(x)$ is nonpositive and the terms with $\lambda_i \ne 0$ are negative. -/
theorem theorem_21_1_exclusive {ι : Type*} [Fintype ι] {C : Set (Rn n)} {f : ι → Rn n → EReal}
    {l : ι → ℝ} (hl : ∀ i, 0 ≤ l i) (hl0 : l ≠ 0)
    (h : ∀ x ∈ C, (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x) :
    ¬ ∃ x ∈ C, ∀ i, f i x < 0 :=
  not_exists_forall_neg_of_forall_zero_le_weighted hl hl0 h

/-! ### Theorem 21.2 -/

/-- **Theorem 21.2** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be convex, let
$f_1, \dots, f_k$ be proper convex functions on $\mathbb{R}^n$ with $\operatorname{dom} f_i
\supseteq \operatorname{ri} C$, and let $f_{k+1}, \dots, f_m$ be affine functions such that the
system $f_{k+1}(x) \le 0, \dots, f_m(x) \le 0$ has a solution in $\operatorname{ri} C$. Then at
least one of the following holds:

(a) there is $x \in C$ with $f_1(x) < 0, \dots, f_k(x) < 0$ and
$f_{k+1}(x) \le 0, \dots, f_m(x) \le 0$;

(b) there are real numbers $\lambda_1, \dots, \lambda_m \ge 0$, at least one of
$\lambda_1, \dots, \lambda_k$ nonzero, such that
$$\lambda_1 f_1(x) + \dots + \lambda_m f_m(x) \ge 0 \quad \text{for every } x \in C.$$

The source says that exactly one of (a) and (b) holds; `Rockafellar.theorem_21_2_exclusive`
gives the exclusivity. The convex functions are indexed by a finite type `ι` and the affine
functions by a finite type `κ`, as real affine maps `Rn n →ᵃ[ℝ] ℝ`; the multipliers of the
affine functions are `μ`. Theorem 21.1 is the case $k = m$, but it is not derived from this
theorem: Theorem 21.1 needs only Theorem 11.3, and Theorem 21.2 needs the polyhedral separation
of Theorem 20.2. -/
theorem theorem_21_2 {ι κ : Type*} [Fintype ι] [Fintype κ] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} {a : κ → (Rn n →ᵃ[ℝ] ℝ)} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hp : ∀ i, ProperConvex (f i)) (hdom : ∀ i, ri C ⊆ convexDom (f i))
    (hfeas : ∃ x ∈ ri C, ∀ j, a j x ≤ 0) :
    (∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0) ∨
      ∃ (l : ι → ℝ) (μ : κ → ℝ), (∀ i, 0 ≤ l i) ∧ (∀ j, 0 ≤ μ j) ∧ l ≠ 0 ∧
        ∀ x ∈ C, (0 : EReal)
          ≤ (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal) :=
  alternative_of_convex_system_affine hC hf hp hdom hfeas

/-- **Theorem 21.2** of [rockafellar1970convex], exclusivity. Let $C \subseteq \mathbb{R}^n$, let
$f_1, \dots, f_k$ be functions with values in $[-\infty, +\infty]$, and let
$f_{k+1}, \dots, f_m$ be real affine functions. If $\lambda_1, \dots, \lambda_m \ge 0$, with
$\lambda_1, \dots, \lambda_k$ not all zero, satisfy $\sum_i \lambda_i f_i(x) \ge 0$ for every
$x \in C$, then there is no $x \in C$ with $f_i(x) < 0$ for $i \le k$ and $f_i(x) \le 0$ for
$i > k$.

At a solution of the mixed system the convex part of the weighted sum is negative and the affine
part is nonpositive. -/
theorem theorem_21_2_exclusive {ι κ : Type*} [Fintype ι] [Fintype κ] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} {a : κ → (Rn n →ᵃ[ℝ] ℝ)} {l : ι → ℝ} {μ : κ → ℝ}
    (hl : ∀ i, 0 ≤ l i) (hμ : ∀ j, 0 ≤ μ j) (hl0 : l ≠ 0)
    (h : ∀ x ∈ C, (0 : EReal)
      ≤ (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal)) :
    ¬ ∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0 := by
  rintro ⟨x, hx, hneg, haff⟩
  have hconv : ¬ (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x := by
    intro hle
    refine not_exists_forall_neg_of_forall_zero_le_weighted (C := ({x} : Set (Rn n))) hl hl0
      (fun y hy => ?_) ⟨x, rfl, hneg⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hle
  have haffsum : (∑ j, μ j * a j x) ≤ 0 := by
    refine Finset.sum_nonpos fun j _ => ?_
    have h₁ := hμ j
    have h₂ := haff j
    nlinarith
  have hlt : (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal) < 0 := by
    calc (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal)
        ≤ (∑ i, (l i : EReal) * f i x) + 0 := by
          have h0 : ((∑ j, μ j * a j x : ℝ) : EReal) ≤ 0 := by exact_mod_cast haffsum
          exact add_le_add le_rfl h0
      _ = ∑ i, (l i : EReal) * f i x := add_zero _
      _ < 0 := not_le.1 hconv
  exact absurd (h x hx) (not_le.2 hlt)

/-! ### Theorem 21.3 and its corollaries -/

/-- **Theorem 21.3** of [rockafellar1970convex]. Let $\{f_i \mid i \in I\}$ be a family of closed
proper convex functions on $\mathbb{R}^n$, with $I$ an arbitrary index set, and let $C$ be a
nonempty closed convex set in $\mathbb{R}^n$. Assume that the $f_i$ have no common direction of
recession that is also a direction of recession of $C$: if $(f_i 0^+)(y) \le 0$ for every $i$
and $y \in 0^+ C$, then $y = 0$. Then at least one of the following holds:

(a) there is $x \in C$ with $f_i(x) \le 0$ for every $i \in I$;

(b) there are real numbers $\lambda_i \ge 0$, only finitely many of them nonzero, and
$\varepsilon > 0$ such that
$$\sum_{i \in I} \lambda_i f_i(x) \ge \varepsilon \quad \text{for every } x \in C.$$

In case (b) the multipliers can be chosen with at most $n + 1$ of them nonzero.

The source says that exactly one of (a) and (b) holds; `Rockafellar.theorem_21_3_exclusive`
gives the exclusivity. The finitely many nonzero multipliers are those in a finite set `t` with
`t.card ≤ n + 1`. The recession function $f_i 0^+$ is `ConvexAnalysis.recessionFn`, and the
recession cone $0^+ C$ is `ConvexAnalysis.recessionCone`. -/
theorem theorem_21_3 {ι : Type*} {C : Set (Rn n)} {f : ι → Rn n → EReal}
    (hf : ∀ i, ClosedProperConvexFn (f i)) (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hrec : ∀ y : Rn n, (∀ i, recessionFn (f i) y ≤ 0) → y ∈ recessionCone C → y = 0) :
    (∃ x ∈ C, ∀ i, f i x ≤ 0) ∨
      ∃ (t : Finset ι) (l : ι → ℝ) (ε : ℝ), (∀ i, 0 ≤ l i) ∧ (∀ i ∉ t, l i = 0) ∧ 0 < ε ∧
        t.card ≤ n + 1 ∧ ∀ x ∈ C, (ε : EReal) ≤ ∑ i ∈ t, (l i : EReal) * f i x := by
  simpa only [finrank_euclideanSpace_fin] using
    alternative_infinite_system (B := pairing n) hf hC hCc hCne hrec

/-- **Theorem 21.3** of [rockafellar1970convex], exclusivity. Let $C \subseteq \mathbb{R}^n$, let
$\{f_i \mid i \in I\}$ be functions with values in $[-\infty, +\infty]$, let $t \subseteq I$ be
finite, and let $\lambda_i \ge 0$ and $\varepsilon > 0$ satisfy $\sum_{i \in t} \lambda_i f_i(x)
\ge \varepsilon$ for every $x \in C$. Then there is no $x \in C$ with $f_i(x) \le 0$ for every
$i \in I$.

At a solution of the weak system every term $\lambda_i f_i(x)$ is nonpositive, so the sum cannot
be bounded below by a positive $\varepsilon$. -/
theorem theorem_21_3_exclusive {ι : Type*} {C : Set (Rn n)} {f : ι → Rn n → EReal}
    {t : Finset ι} {l : ι → ℝ} {ε : ℝ} (hl : ∀ i, 0 ≤ l i) (hε : 0 < ε)
    (h : ∀ x ∈ C, (ε : EReal) ≤ ∑ i ∈ t, (l i : EReal) * f i x) :
    ¬ ∃ x ∈ C, ∀ i, f i x ≤ 0 := by
  rintro ⟨x, hx, hle⟩
  have hsum : ∑ i ∈ t, (l i : EReal) * f i x ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    calc (l i : EReal) * f i x
        ≤ (l i : EReal) * 0 := by
          refine mul_le_mul_of_nonneg_left (hle i) ?_
          exact_mod_cast hl i
      _ = 0 := by simp
  have hle0 : ((ε : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := by
    simpa using le_trans (h x hx) hsum
  exact absurd (EReal.coe_le_coe_iff.1 hle0) (not_le.2 hε)

/-- **Corollary 21.3.1** of [rockafellar1970convex]. Let $\{f_i \mid i \in I\}$ and $C$ satisfy the
hypotheses of Theorem 21.3: the $f_i$ are closed proper convex functions on $\mathbb{R}^n$, $C$
is a nonempty closed convex set, and the $f_i$ have no common direction of recession that is
also a direction of recession of $C$. Suppose that for every $\varepsilon > 0$ and every set of
indices $i_1, \dots, i_m$ with $m \le n + 1$ the system
$$f_{i_1}(x) < \varepsilon, \ \dots, \ f_{i_m}(x) < \varepsilon$$
has a solution $x \in C$. Then there is $x \in C$ with $f_i(x) \le 0$ for every $i \in I$. -/
theorem corollary_21_3_1 {ι : Type*} {C : Set (Rn n)} {f : ι → Rn n → EReal}
    (hf : ∀ i, ClosedProperConvexFn (f i)) (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hrec : ∀ y : Rn n, (∀ i, recessionFn (f i) y ≤ 0) → y ∈ recessionCone C → y = 0)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ S : Finset ι, S.card ≤ n + 1 →
      ∃ x ∈ C, ∀ i ∈ S, f i x < (ε : EReal)) :
    ∃ x ∈ C, ∀ i, f i x ≤ 0 := by
  refine exists_forall_le_zero_of_forall_subsystem (B := pairing n) hf hC hCc hCne hrec ?_
  simpa only [finrank_euclideanSpace_fin] using hsub

/-- **Corollary 21.3.2** of [rockafellar1970convex] (Helly's theorem). Let $\{C_i \mid i \in I\}$ be
a family of nonempty closed convex sets in $\mathbb{R}^n$, with $I$ an arbitrary index set, and
assume that the $C_i$ have no common direction of recession: if $y \in 0^+ C_i$ for every $i$,
then $y = 0$. If every subfamily of $n + 1$ or fewer sets has a nonempty intersection, then the
intersection of the whole family is nonempty.

The recession hypothesis cannot be omitted. Compare `Rockafellar.theorem_21_6`, where the family
is finite and neither closedness nor a recession hypothesis is needed. -/
theorem corollary_21_3_2 {ι : Type*} {K : ι → Set (Rn n)} (hconv : ∀ i, Convex ℝ (K i))
    (hcl : ∀ i, IsClosed (K i)) (hne : ∀ i, (K i).Nonempty)
    (hrec : ∀ y : Rn n, (∀ i, y ∈ recessionCone (K i)) → y = 0)
    (hinter : ∀ S : Finset ι, S.card ≤ n + 1 → (⋂ i ∈ S, K i).Nonempty) :
    (⋂ i, K i).Nonempty := by
  refine helly_of_no_common_recession (B := pairing n) hconv hcl hne hrec ?_
  simpa only [finrank_euclideanSpace_fin] using hinter

/-- **Section 21** of [rockafellar1970convex], the exercise after Corollary 21.3.2. Let
$\{C_i \mid i \in I\}$ be closed convex sets in $\mathbb{R}^n$ such that every finite subfamily
has a nonempty intersection. Then the $C_i$ have no common direction of recession if and only if
some finite subfamily has a bounded intersection.

The case of a subfamily $\{C_i\}$ with one member gives the remark before the exercise: the
recession hypothesis of Helly's theorem holds as soon as one $C_i$ is bounded. -/
theorem helly_recession_iff_exists_isBounded {ι : Type*} {K : ι → Set (Rn n)}
    (hconv : ∀ i, Convex ℝ (K i)) (hcl : ∀ i, IsClosed (K i))
    (hne : ∀ S : Finset ι, (⋂ i ∈ S, K i).Nonempty) :
    (∀ y : Rn n, (∀ i, y ∈ recessionCone (K i)) → y = 0) ↔
      ∃ S : Finset ι, Bornology.IsBounded (⋂ i ∈ S, K i) := by
  have hbridge : ⋂ i, recessionCone (K i) = {0} ↔
      ∀ y : Rn n, (∀ i, y ∈ recessionCone (K i)) → y = 0 := by
    simp [Set.eq_singleton_iff_unique_mem, mem_iInter]
  rw [← hbridge]
  exact iInter_recessionCone_eq_zero_iff_exists_isBounded hconv hcl hne

/-! ### Theorems 21.4 and 21.5: the polyhedral refinements -/

/-- **Section 21** of [rockafellar1970convex], affine functions. A function
$f : \mathbb{R}^n \to [-\infty, +\infty]$ is **affine** if there are $b \in \mathbb{R}^n$ and
$\beta \in \mathbb{R}$ with $f(x) = \langle x, b \rangle - \beta$ for every $x$.

In particular an affine function is finite everywhere. -/
def IsAffineFn (f : Rn n → EReal) : Prop :=
  ∃ (b : Rn n) (β : ℝ), ∀ x, f x = ((inner ℝ x b - β : ℝ) : EReal)

/-- A function $f : \mathbb{R}^n \to [-\infty, +\infty]$ is affine in the sense of
`Rockafellar.IsAffineFn` if and only if it equals `ConvexAnalysis.affineFn (Rockafellar.pairing
n) b β` for some $b \in \mathbb{R}^n$ and $\beta \in \mathbb{R}$. -/
theorem isAffineFn_iff_eq_affineFn {f : Rn n → EReal} :
    IsAffineFn f ↔ ∃ (b : Rn n) (β : ℝ), f = affineFn (pairing n) b β := by
  constructor
  · rintro ⟨b, β, h⟩
    exact ⟨b, β, funext fun x => by rw [h x, affineFn_eq_coe, pairing_apply]⟩
  · rintro ⟨b, β, rfl⟩
    exact ⟨b, β, fun x => by rw [affineFn_eq_coe, pairing_apply]⟩

/-- **Theorem 21.4** of [rockafellar1970convex]. Let $\{f_i \mid i \in I\}$ be a family of closed
proper convex functions on $\mathbb{R}^n$, and let $I_0 \subseteq I$ be a finite set such that
$f_i$ is affine for every $i \in I_0$. Assume that every common direction of recession of the
$f_i$ is a direction in which $f_i$ is constant for every $i \in I \setminus I_0$. Then the
alternative of Theorem 21.3 holds for $C = \mathbb{R}^n$: either there is $x \in \mathbb{R}^n$
with $f_i(x) \le 0$ for every $i$, or there are $\lambda_i \ge 0$, at most $n + 1$ of them
nonzero, and $\varepsilon > 0$ with $\sum_i \lambda_i f_i(x) \ge \varepsilon$ for every
$x \in \mathbb{R}^n$.

The source states that the recession hypothesis of Theorem 21.3 and of Corollary 21.3.1 may be
weakened in this way when $C = \mathbb{R}^n$; this declaration is the weakened Theorem 21.3, and
`Rockafellar.theorem_21_4_subsystem` is the weakened Corollary 21.3.1.

A common direction of recession is a $y$ with $(f_i 0^+)(y) \le 0$ for every $i$, and the
directions in which $f_i$ is constant form `ConvexAnalysis.constancySpace (f i)`. Theorem 21.3
for $C = \mathbb{R}^n$ is the case $I_0 = \emptyset$, since $0$ lies in every constancy space. -/
theorem theorem_21_4 {ι : Type*} {f : ι → Rn n → EReal} (hf : ∀ i, ClosedProperConvexFn (f i))
    (I₀ : Finset ι) (haff : ∀ i ∈ I₀, IsAffineFn (f i))
    (hrec : ∀ y : Rn n, (∀ i, recessionFn (f i) y ≤ 0) → ∀ i ∉ I₀, y ∈ constancySpace (f i)) :
    (∃ x : Rn n, ∀ i, f i x ≤ 0) ∨
      ∃ (t : Finset ι) (l : ι → ℝ) (ε : ℝ), (∀ i, 0 ≤ l i) ∧ (∀ i ∉ t, l i = 0) ∧ 0 < ε ∧
        t.card ≤ n + 1 ∧ ∀ x : Rn n, (ε : EReal) ≤ ∑ i ∈ t, (l i : EReal) * f i x := by
  have hB := separatingRight_pairing n
  simpa only [finrank_euclideanSpace_fin] using
    alternative_infinite_system_univ_of_affine_tail (B := pairing n) hB hf I₀
      (fun i hi => isAffineFn_iff_eq_affineFn.1 (haff i hi)) hrec

/-- **Theorem 21.4** of [rockafellar1970convex], the form of Corollary 21.3.1. Let
$\{f_i \mid i \in I\}$ and $I_0$ satisfy the hypotheses of `Rockafellar.theorem_21_4`. Suppose
that for every $\varepsilon > 0$ and every set $S \subseteq I$ of at most $n + 1$ indices there
is $x \in \mathbb{R}^n$ with $f_i(x) < \varepsilon$ for every $i \in S$. Then there is
$x \in \mathbb{R}^n$ with $f_i(x) \le 0$ for every $i \in I$. -/
theorem theorem_21_4_subsystem {ι : Type*} {f : ι → Rn n → EReal}
    (hf : ∀ i, ClosedProperConvexFn (f i)) (I₀ : Finset ι) (haff : ∀ i ∈ I₀, IsAffineFn (f i))
    (hrec : ∀ y : Rn n, (∀ i, recessionFn (f i) y ≤ 0) → ∀ i ∉ I₀, y ∈ constancySpace (f i))
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ S : Finset ι, S.card ≤ n + 1 →
      ∃ x : Rn n, ∀ i ∈ S, f i x < (ε : EReal)) :
    ∃ x : Rn n, ∀ i, f i x ≤ 0 := by
  have hB := separatingRight_pairing n
  refine exists_forall_le_zero_of_forall_subsystem_of_affine_tail (B := pairing n) hB hf I₀
    (fun i hi => isAffineFn_iff_eq_affineFn.1 (haff i hi)) hrec ?_
  simpa only [finrank_euclideanSpace_fin] using hsub

/-- **Theorem 21.5** of [rockafellar1970convex]. Let $\{C_i \mid i \in I\}$ be a family of nonempty
closed convex sets in $\mathbb{R}^n$, and let $I_0 \subseteq I$ be a finite set such that $C_i$
is polyhedral for every $i \in I_0$. Assume that every common direction of recession of the
$C_i$ is a direction in which $C_i$ is linear for every $i \in I \setminus I_0$. If every
subfamily of $n + 1$ or fewer sets has a nonempty intersection, then the intersection of the
whole family is nonempty.

The directions in which $C_i$ is linear form the lineality space
`ConvexAnalysis.linealitySpace (K i)`. The set $C_i$ is `K i`. -/
theorem theorem_21_5 {ι : Type*} {K : ι → Set (Rn n)} (hconv : ∀ i, Convex ℝ (K i))
    (hcl : ∀ i, IsClosed (K i)) (hne : ∀ i, (K i).Nonempty) (I₀ : Finset ι)
    (hpoly : ∀ i ∈ I₀, Polyhedral (K i))
    (hrec : ∀ y : Rn n, (∀ i, y ∈ recessionCone (K i)) → ∀ i ∉ I₀, y ∈ linealitySpace (K i))
    (hinter : ∀ S : Finset ι, S.card ≤ n + 1 → (⋂ i ∈ S, K i).Nonempty) :
    (⋂ i, K i).Nonempty := by
  have hB := separatingRight_pairing n
  refine helly_of_polyhedral_tail (B := pairing n) hB hconv hcl hne I₀ hpoly hrec ?_
  simpa only [finrank_euclideanSpace_fin] using hinter

/-! ### Theorem 21.6 and its corollaries: finite collections -/

/-- **Theorem 21.6** of [rockafellar1970convex] (Helly's theorem for finite collections). Let
$C_1, \dots, C_m$ be convex sets in $\mathbb{R}^n$, not necessarily closed. If every
subcollection of $n + 1$ or fewer sets has a nonempty intersection, then
$C_1 \cap \dots \cap C_m$ is nonempty.

The collection is indexed by a finite set `s`; for `s` empty the intersection is all of
$\mathbb{R}^n$. The source derives the theorem from Corollary 21.3.2. The proof here uses
Radon's theorem instead, so Corollaries 21.6.1 and 21.6.2 do not depend on Theorem 21.3. -/
theorem theorem_21_6 {ι : Type*} {K : ι → Set (Rn n)} {s : Finset ι}
    (hconv : ∀ i ∈ s, Convex ℝ (K i))
    (hinter : ∀ t ⊆ s, t.card ≤ n + 1 → (⋂ i ∈ t, K i).Nonempty) :
    (⋂ i ∈ s, K i).Nonempty := by
  refine helly_finite hconv ?_
  simpa only [finrank_euclideanSpace_fin] using hinter

/-- **Corollary 21.6.1** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be convex, and
let $f_1, \dots, f_m$ be convex functions on $\mathbb{R}^n$. Consider the system
$$f_1(x) < 0, \ \dots, \ f_k(x) < 0, \quad f_{k+1}(x) \le 0, \ \dots, \ f_m(x) \le 0.$$
If every subsystem of $n + 1$ or fewer of these inequalities has a solution in $C$, then the
whole system has a solution in $C$.

The strict inequalities are indexed by a finite type `ι` with functions `f`, and the weak ones
by a finite type `κ` with functions `g`. A subsystem is a pair of finite sets `S` and `T` with
`S.card + T.card ≤ n + 1`. -/
theorem corollary_21_6_1 {ι κ : Type*} [Finite ι] [Finite κ] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} {g : κ → Rn n → EReal} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hg : ∀ j, ConvexFn (g j))
    (hsub : ∀ (S : Finset ι) (T : Finset κ), S.card + T.card ≤ n + 1 →
      ∃ x ∈ C, (∀ i ∈ S, f i x < 0) ∧ ∀ j ∈ T, g j x ≤ 0) :
    ∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, g j x ≤ 0 := by
  refine exists_mem_of_forall_subsystem hC hf hg ?_
  simpa only [finrank_euclideanSpace_fin] using hsub

/-- **Corollary 21.6.2** of [rockafellar1970convex], for Theorem 21.1. Under the hypotheses of
Theorem 21.1 ($C \subseteq \mathbb{R}^n$ convex, $f_1, \dots, f_m$ proper convex with
$\operatorname{dom} f_i \supseteq \operatorname{ri} C$, $m \ge 1$), either there is $x \in C$
with $f_1(x) < 0, \dots, f_m(x) < 0$, or there are $\lambda_1, \dots, \lambda_m \ge 0$, not all
zero and at most $n + 1$ of them nonzero, with $\sum_i \lambda_i f_i(x) \ge 0$ for every
$x \in C$.

The source states the corollary for Theorem 21.2 as well; that part is
`Rockafellar.corollary_21_6_2_affine`. The bound on the nonzero multipliers is a finite set `S`
with `S.card ≤ n + 1` outside which every $\lambda_i$ is zero. Extending a short multiplier
vector by zeros is possible because $0 \cdot (+\infty) = 0$ in `EReal`. -/
theorem corollary_21_6_2 {ι : Type*} [Fintype ι] [Nonempty ι] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
        (hp : ∀ i, ProperConvex (f i))
    (hdom : ∀ i, ri C ⊆ convexDom (f i)) :
    (∃ x ∈ C, ∀ i, f i x < 0) ∨
      ∃ (S : Finset ι) (l : ι → ℝ), S.card ≤ n + 1 ∧ (∀ i ∉ S, l i = 0) ∧
        (∀ i, 0 ≤ l i) ∧ l ≠ 0 ∧ ∀ x ∈ C, (0 : EReal) ≤ ∑ i, (l i : EReal) * f i x := by
  simpa only [finrank_euclideanSpace_fin] using
    sparse_alternative_of_convex_system hC hf hp hdom

/-- Let $g : \mathbb{R}^n \to \mathbb{R}$ be affine. Then $g$, as a function with values in
$[-\infty, +\infty]$, is convex.

This lets the affine constraints of Theorem 21.2 enter the collection of convex sets in
Corollary 21.6.1. -/
theorem convexFn_coe_affineMap (g : Rn n →ᵃ[ℝ] ℝ) : ConvexFn (fun x => ((g x : ℝ) : EReal)) := by
  refine convexFn_of_epi_combo fun x y p q hx hy s t hs ht hst => ?_
  rw [EReal.coe_le_coe_iff] at hx hy ⊢
  rw [Convex.combo_affine_apply hst]
  simp only [smul_eq_mul]
  nlinarith

/-- **Corollary 21.6.2** of [rockafellar1970convex], for Theorem 21.2. Under the hypotheses of
Theorem 21.2, either alternative (a) of Theorem 21.2 holds, or there are
$\lambda_1, \dots, \lambda_m \ge 0$, at least one of $\lambda_1, \dots, \lambda_k$ nonzero and
at most $n + 1$ of $\lambda_1, \dots, \lambda_m$ nonzero, with $\lambda_1 f_1(x) + \dots +
\lambda_m f_m(x) \ge 0$ for every $x \in C$.

The count of nonzero multipliers includes the multipliers `μ` of the affine functions, because
$\lambda_1, \dots, \lambda_m$ is one list in the source; it is the condition
`S.card + T.card ≤ n + 1`. The proof is that of the source: if (a) fails, it fails already for a
subsystem of at most $n + 1$ inequalities (Corollary 21.6.1), and Theorem 21.2 for that
subsystem gives multipliers that extend by zero. -/
theorem corollary_21_6_2_affine {ι κ : Type*} [Fintype ι] [Fintype κ] {C : Set (Rn n)}
    {f : ι → Rn n → EReal} {a : κ → (Rn n →ᵃ[ℝ] ℝ)} (hC : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hp : ∀ i, ProperConvex (f i)) (hdom : ∀ i, ri C ⊆ convexDom (f i))
    (hfeas : ∃ x ∈ ri C, ∀ j, a j x ≤ 0) :
    (∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0) ∨
      ∃ (S : Finset ι) (T : Finset κ) (l : ι → ℝ) (μ : κ → ℝ),
        S.card + T.card ≤ n + 1 ∧ (∀ i ∉ S, l i = 0) ∧ (∀ j ∉ T, μ j = 0) ∧
          (∀ i, 0 ≤ l i) ∧ (∀ j, 0 ≤ μ j) ∧ l ≠ 0 ∧
          ∀ x ∈ C, (0 : EReal)
            ≤ (∑ i, (l i : EReal) * f i x) + ((∑ j, μ j * a j x : ℝ) : EReal) := by
  classical
  by_cases halt : ∃ x ∈ C, (∀ i, f i x < 0) ∧ ∀ j, a j x ≤ 0
  · exact Or.inl halt
  refine Or.inr ?_
  have hsmall : ∃ (S : Finset ι) (T : Finset κ), S.card + T.card ≤ n + 1 ∧
      ¬ ∃ x ∈ C, (∀ i ∈ S, f i x < 0) ∧ ∀ j ∈ T, a j x ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : ∀ (S : Finset ι) (T : Finset κ), S.card + T.card ≤ n + 1 →
        ∃ x ∈ C, (∀ i ∈ S, f i x < 0) ∧ ∀ j ∈ T, ((a j x : ℝ) : EReal) ≤ 0 := by
      intro S T hST
      obtain ⟨x, hx, hxf, hxa⟩ := hcon S T hST
      exact ⟨x, hx, hxf, fun j hj => by exact_mod_cast hxa j hj⟩
    obtain ⟨x, hx, hxf, hxa⟩ :=
      corollary_21_6_1 (g := fun j x => ((a j x : ℝ) : EReal)) hC hf
        (fun j => convexFn_coe_affineMap (a j)) hsub
    exact halt ⟨x, hx, hxf, fun j => by exact_mod_cast hxa j⟩
  obtain ⟨S, T, hcard, hSalt⟩ := hsmall
  obtain ⟨y₀, hy₀, hy₀a⟩ := hfeas
  rcases theorem_21_2 (ι := ↥S) (κ := ↥T) (f := fun i : ↥S => f i) (a := fun j : ↥T => a j) hC
      (fun i => hf i) (fun i => hp i) (fun i => hdom i) ⟨y₀, hy₀, fun j => hy₀a j⟩ with
    ⟨x, hx, hxf, hxa⟩ | ⟨l', μ', hl'0, hμ'0, hl'ne, hl'⟩
  · exact absurd ⟨x, hx, fun i hi => hxf ⟨i, hi⟩, fun j hj => hxa ⟨j, hj⟩⟩ hSalt
  refine ⟨S, T, fun i => if h : i ∈ S then l' ⟨i, h⟩ else 0,
    fun j => if h : j ∈ T then μ' ⟨j, h⟩ else 0, hcard, fun i hi => by simp [hi],
    fun j hj => by simp [hj], ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i ∈ S
    · simpa [h] using hl'0 ⟨i, h⟩
    · simp [h]
  · intro j
    by_cases h : j ∈ T
    · simpa [h] using hμ'0 ⟨j, h⟩
    · simp [h]
  · intro hzero
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ↥S, l' i₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hl'ne (funext hcon)
    have h := congrFun hzero (i₀ : ι)
    simp only [i₀.2, Pi.zero_apply, Subtype.coe_eta, ↓reduceDIte] at h
    exact hi₀ h
  · intro x hx
    have hshrinkl : ∑ i, ((if h : i ∈ S then l' ⟨i, h⟩ else 0 : ℝ) : EReal) * f i x
        = ∑ i ∈ S, ((if h : i ∈ S then l' ⟨i, h⟩ else 0 : ℝ) : EReal) * f i x := by
      refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
      intro i _ hi
      simp [hi]
    have hshrinkm : ∑ j, (if h : j ∈ T then μ' ⟨j, h⟩ else 0 : ℝ) * a j x
        = ∑ j ∈ T, (if h : j ∈ T then μ' ⟨j, h⟩ else 0 : ℝ) * a j x := by
      refine (Finset.sum_subset (Finset.subset_univ T) ?_).symm
      intro j _ hj
      simp [hj]
    rw [hshrinkl, hshrinkm, ← Finset.sum_coe_sort S, ← Finset.sum_coe_sort T]
    have hcl : ∀ i : ↥S, ((if h : (i : ι) ∈ S then l' ⟨(i : ι), h⟩ else 0 : ℝ) : EReal)
        * f i x = (l' i : EReal) * f i x := by
      intro i
      simp only [i.2, Subtype.coe_eta, ↓reduceDIte]
    have hcm : ∀ j : ↥T, (if h : (j : κ) ∈ T then μ' ⟨(j : κ), h⟩ else 0 : ℝ) * a j x
        = μ' j * a j x := by
      intro j
      simp only [j.2, Subtype.coe_eta, ↓reduceDIte]
    rw [Finset.sum_congr rfl fun i _ => hcl i, Finset.sum_congr rfl fun j _ => hcm j]
    exact hl' x hx

end Rockafellar
