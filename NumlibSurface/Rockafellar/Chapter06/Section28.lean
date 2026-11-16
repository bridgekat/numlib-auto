/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Extremum.Lagrangian
import Numlib.Analysis.Convex.Extremum.Program
import Numlib.Analysis.Convex.Saddle.Minimax
import NumlibSurface.Rockafellar.Common.Euclidean
import NumlibSurface.Rockafellar.Chapter05.Section23

/-!
# Rockafellar, Section 28: Ordinary convex programs and Lagrange multipliers

This module formalizes Section 28 (pp. 273–290) of [rockafellar1970convex]. An ordinary convex
program $(P)$ asks to minimize a proper convex function $f_0$ over the points $x$ of a convex set
$C \subseteq \mathbb{R}^n$ that satisfy $f_i(x) \le 0$ for $i = 1, \dots, r$ and $f_i(x) = 0$ for
$i = r + 1, \dots, m$. A Kuhn–Tucker vector is a vector $(\lambda_1, \dots, \lambda_m)$ with
$\lambda_i \ge 0$ for $i \le r$ such that the infimum of $h = f_0 + \lambda_1 f_1 + \dots +
\lambda_m f_m$ over $\mathbb{R}^n$ is finite and equal to the optimal value in $(P)$. The section
shows that a Kuhn–Tucker vector turns $(P)$ into the unconstrained minimization of $h$, gives
constraint qualifications under which a Kuhn–Tucker vector exists, and shows that the pairs of a
Kuhn–Tucker vector and an optimal solution are exactly the saddle-points of the Lagrangian $L$ of
$(P)$, and exactly the solutions of the Kuhn–Tucker conditions.

The section also states the decomposition principle and gives two programs that have a unique
optimal solution and no Kuhn–Tucker vector. All nine numbered results of Section 28 are formalized:
Theorems 28.1–28.4 and Corollaries 28.1.1, 28.2.1, 28.2.2, 28.3.1 and 28.4.1. The book prints
Corollaries 28.2.2, 28.3.1 and 28.4.1 with no proof. The proofs specialize the backbone modules
`Numlib.Analysis.Convex.Extremum.Program`, `Numlib.Analysis.Convex.Extremum.Lagrangian` and
`Numlib.Analysis.Convex.Saddle.Minimax`.

## Main definitions

* `Rockafellar.OrdinaryConvexProgram`: an ordinary convex program, the $(m + 3)$-tuple
  $(C, f_0, f_1, \dots, f_m, r)$ with the standing assumptions of the book.
* `Rockafellar.OrdinaryConvexProgram.feasibleSet`, `Rockafellar.OrdinaryConvexProgram.objective`,
  `Rockafellar.OrdinaryConvexProgram.optimalValue`,
  `Rockafellar.OrdinaryConvexProgram.optimalSolutions`: the set $C_0$ of feasible solutions, the
  objective function $f = f_0 + \delta(\cdot \mid C_0)$, the optimal value $\inf f$, and the set of
  optimal solutions.
* `Rockafellar.OrdinaryConvexProgram.lagrangeFn`: the function $h = f_0 + \lambda_1 f_1 + \dots +
  \lambda_m f_m$, which is not the Lagrangian.
* `Rockafellar.OrdinaryConvexProgram.IsKuhnTuckerVector`: the Kuhn–Tucker vectors for $(P)$.
* `Rockafellar.OrdinaryConvexProgram.ineqBifun`, `Rockafellar.OrdinaryConvexProgram.perturbFn`: the
  bifunction $F$ of $(P)$ and the perturbation function $p = \inf F$.
* `Rockafellar.OrdinaryConvexProgram.multiplierCone`,
  `Rockafellar.OrdinaryConvexProgram.programLagrangian`,
  `Rockafellar.OrdinaryConvexProgram.saddleFn`: the cone $E_r$ of multiplier vectors, the Lagrangian
  $L$ of $(P)$, and $L$ as a function on $\mathbb{R}^m \times \mathbb{R}^n$.
* `Rockafellar.activeIndices`: the indices $i$ with $\lambda_i \neq 0$.
* `Rockafellar.OrdinaryConvexProgram.dualFn`: the concave function $g(u^*) = \inf_x L(u^*, x)$.
* `Rockafellar.ex1`, `Rockafellar.ex2`: the two programs of the section that have no Kuhn–Tucker
  vector.

## Main results

* Theorem 28.1, `Rockafellar.theorem_28_1`: for a Kuhn–Tucker vector
  $(\lambda_1, \dots, \lambda_m)$, the optimal solutions of $(P)$ are the minimizers of $h$ that
  satisfy the constraints with $\lambda_i = 0$ and satisfy with equality the other constraints.
* Corollary 28.1.1, `Rockafellar.corollary_28_1_1`: if $f_0, \dots, f_r$ are closed and $h$ has a
  unique minimizer $w$, then $w$ is the unique optimal solution of $(P)$.
* Theorem 28.2, `Rockafellar.theorem_28_2`: a Kuhn–Tucker vector exists if the optimal value is not
  $-\infty$ and some feasible solution in $\operatorname{ri} C$ satisfies the non-affine inequality
  constraints strictly.
* Corollary 28.2.1, `Rockafellar.corollary_28_2_1`: for a program with inequality constraints only,
  a point of $C$ that satisfies every constraint strictly is enough.
* Corollary 28.2.2, `Rockafellar.corollary_28_2_2`: for a program with linear constraints only, a
  feasible solution in $\operatorname{ri} C$ is enough.
* Theorem 28.3, `Rockafellar.OrdinaryConvexProgram.theorem_28_3`,
  `Rockafellar.OrdinaryConvexProgram.theorem_28_3_kuhnTucker`: $\bar u^*$ is a Kuhn–Tucker vector
  and $\bar x$ is an optimal solution if and only if $(\bar u^*, \bar x)$ is a saddle-point of $L$,
  and if and only if the Kuhn–Tucker conditions (a), (b), (c) hold.
* Corollary 28.3.1, `Rockafellar.OrdinaryConvexProgram.corollary_28_3_1`,
  `Rockafellar.OrdinaryConvexProgram.corollary_28_3_1_kuhnTucker` (the Kuhn–Tucker theorem): if a
  Kuhn–Tucker vector exists, then $\bar x$ is optimal if and only if some $\bar u^*$ makes
  $(\bar u^*, \bar x)$ a saddle-point of $L$, or equivalently satisfies the Kuhn–Tucker conditions
  together with $\bar x$.
* Theorem 28.4, `Rockafellar.OrdinaryConvexProgram.theorem_28_4`,
  `Rockafellar.OrdinaryConvexProgram.theorem_28_4_saddleValue`,
  `Rockafellar.OrdinaryConvexProgram.theorem_28_4_value`: $\bar u^*$ is a Kuhn–Tucker vector if and
  only if $-\infty < \inf_x L(\bar u^*, x) = \sup_{u^*} \inf_x L = \inf_x \sup_{u^*} L$, and then
  this common value is the optimal value of $(P)$.
* Corollary 28.4.1, `Rockafellar.OrdinaryConvexProgram.corollary_28_4_1`: if a Kuhn–Tucker vector
  exists, the Kuhn–Tucker vectors are exactly the maximizers of $g$.
* `Rockafellar.OrdinaryConvexProgram.decomposition_C`,
  `Rockafellar.OrdinaryConvexProgram.decomposition_argmin_lagrangeFn`: the decomposition principle.
  If $h$ is separable in a splitting $x = (x_1, \dots, x_s)$ of the coordinates, then $C$ and the
  set of minimizers of $h$ split into products.
* `Rockafellar.ex1_not_exists_isKuhnTuckerVector`, `Rockafellar.ex2_not_exists_isKuhnTuckerVector`:
  a unique optimal solution and a finite optimal value do not imply that a Kuhn–Tucker vector
  exists.

## Conventions

* The number $r$ counts the inequality constraints: the constraints are
  $f_1 \le 0, \dots, f_r \le 0$ and $f_{r+1} = 0, \dots, f_m = 0$.
* The constraint functions are indexed by `Fin m`, which starts at $0$. The book's $f_i$ for
  $i = 1, \dots, m$ is `P.f` at the index $i - 1$, the condition $i \le r$ of the book is
  `(i : ℕ) < P.r`, and the condition $i > r$ is `P.r ≤ (i : ℕ)`. The doc comments use the numbering
  of the book.
* One vector `u : Rn m` stands both for the Kuhn–Tucker coefficients $(\lambda_1, \dots, \lambda_m)$
  and for the variable $u^* = (v_1^*, \dots, v_m^*)$ of the Lagrangian.
* Functions take values in the extended reals $[-\infty, +\infty]$ (`EReal`). A product
  $\lambda_i f_i(x)$ is taken in `EReal`, where $0 \cdot (\pm\infty) = 0$.

## Implementation notes

* A program is the tuple $(C, f_0, f_1, \dots, f_m, r)$, not its objective function. Two programs
  with the same objective function $f_0 + \delta(\cdot \mid C_0)$ can have different Kuhn–Tucker
  vectors. The Lagrangian determines the tuple on $C$
  (`Rockafellar.OrdinaryConvexProgram.eq_of_programLagrangian_eq`).
* The set of optimal solutions is the set of minimizers of the objective function. If $(P)$ has no
  feasible solution, this set is all of $\mathbb{R}^n$, while the book does not speak of optimal
  solutions in this case. Each theorem here about optimal solutions also assumes or concludes that a
  Kuhn–Tucker vector exists, which excludes this case.
* Condition (c) of Theorem 28.3 sums only over `Rockafellar.activeIndices`, the indices with
  $\lambda_i \neq 0$. This matters: $\partial f_i(\bar x)$ can be empty at a boundary point of
  $\operatorname{dom} f_i$, and then $0 \cdot \partial f_i(\bar x)$ is empty, not $\{0\}$.
* The Lagrangian `Rockafellar.OrdinaryConvexProgram.programLagrangian` is the Lagrangian of the
  bifunction `Rockafellar.OrdinaryConvexProgram.ineqBifun` in the sense of Section 29
  (`Rockafellar.OrdinaryConvexProgram.lagrangian_ineqBifun`), so the results of
  `Numlib.Analysis.Convex.Extremum.Lagrangian` apply to it.
* In the decomposition principle, the splitting of the coordinates is a linear equivalence $e :
  \mathbb{R}^{n_1} \times \dots \times \mathbb{R}^{n_s} \to \mathbb{R}^n$. Linearity carries the
  condition $n_1 + \dots + n_s = n$, because a bijection between these two types exists for all
  $n_k$. The separability of $h$ is a hypothesis, in the form that the book states. It is not
  derived from the separability of each $f_i$, because the distribution of $\lambda_i$ over a sum
  $\sum_k f_{ik}(x_k)$ would need `EReal` to be a semiring.

## Deviations from the source

* **Corollary 28.3.1** (generalization). The book assumes the hypotheses of Theorem 28.2. The
  statement assumes only the conclusion of Theorem 28.2, that a Kuhn–Tucker vector exists. See
  `Rockafellar.OrdinaryConvexProgram.corollary_28_3_1`.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {m n : ℕ}

/-! ### The ordinary convex program -/

/-- **Section 28** of [rockafellar1970convex], definition of an ordinary convex program. An
**ordinary convex program** $(P)$ in $\mathbb{R}^n$ with $m$ constraints is an $(m + 3)$-tuple
$(C, f_0, f_1, \dots, f_m, r)$ with $0 \le r \le m$, where $C \subseteq \mathbb{R}^n$, and
$f_0, f_1, \dots, f_m$ are functions from $\mathbb{R}^n$ to $[-\infty, +\infty]$, such that:
$f_0$ is a proper convex function with $\operatorname{dom} f_0 = C$; for $i = 1, \dots, r$,
$f_i$ is a proper convex function with $C \subseteq \operatorname{dom} f_i$ and
$\operatorname{ri} C \subseteq \operatorname{ri}(\operatorname{dom} f_i)$; and for
$i = r + 1, \dots, m$, $f_i$ is a real-valued affine function on all of $\mathbb{R}^n$. The
program is to minimize $f_0(x)$ over the $x \in C$ with $f_i(x) \le 0$ for $i = 1, \dots, r$ and
$f_i(x) = 0$ for $i = r + 1, \dots, m$.

The conditions on the domains are the extension conventions (a), (b), (c) of the book. The set
$C$ is convex and nonempty because it is the effective domain of a proper convex function
(`Rockafellar.OrdinaryConvexProgram.convex_C`, `Rockafellar.OrdinaryConvexProgram.nonempty_C`).
The constraint functions are indexed by `Fin m`, starting at $0$. -/
structure OrdinaryConvexProgram (n m : ℕ) where
  /-- The set $C$ over which the objective is minimized. -/
  C : Set (Rn n)
  /-- The objective $f_0$. -/
  f₀ : Rn n → EReal
  /-- The constraint functions $f_1, \dots, f_m$, indexed by `Fin m`. -/
  f : Fin m → Rn n → EReal
  /-- The number $r$ of inequality constraints: the constraints are $f_1 \le 0, \dots, f_r \le 0$
  and $f_{r+1} = 0, \dots, f_m = 0$. -/
  r : ℕ
  /-- The number of inequality constraints satisfies $r \le m$. -/
  r_le : r ≤ m
  /-- The objective $f_0$ is convex. -/
  convexFn_f₀ : ConvexFn f₀
  /-- The objective $f_0$ is proper. -/
  properConvex_f₀ : ProperConvex f₀
  /-- Extension convention (a) of the book: $\operatorname{dom} f_0 = C$. -/
  convexDom_f₀ : convexDom f₀ = C
  /-- The inequality constraint functions $f_1, \dots, f_r$ are convex. -/
  convexFn_f : ∀ i : Fin m, (i : ℕ) < r → ConvexFn (f i)
  /-- The inequality constraint functions $f_1, \dots, f_r$ are proper. -/
  properConvex_f : ∀ i : Fin m, (i : ℕ) < r → ProperConvex (f i)
  /-- Extension convention (b) of the book, first half: $C \subseteq \operatorname{dom} f_i$ for
  $i = 1, \dots, r$. -/
  subset_convexDom_f : ∀ i : Fin m, (i : ℕ) < r → C ⊆ convexDom (f i)
  /-- Extension convention (b) of the book, second half: $\operatorname{ri} C \subseteq
  \operatorname{ri}(\operatorname{dom} f_i)$ for $i = 1, \dots, r$. -/
  relint_subset : ∀ i : Fin m, (i : ℕ) < r → ri C ⊆ ri (convexDom (f i))
  /-- Extension convention (c) of the book: for $i = r + 1, \dots, m$, the function $f_i$ is a
  real-valued affine function on all of $\mathbb{R}^n$. -/
  exists_affine :
    ∀ i : Fin m, r ≤ (i : ℕ) → ∃ a : Rn n →ᵃ[ℝ] ℝ, ∀ x, f i x = ((a x : ℝ) : EReal)

namespace OrdinaryConvexProgram

variable (P : OrdinaryConvexProgram n m)

/-- The set $C$ of an ordinary convex program is convex, because it is the effective domain of the
convex function $f_0$. -/
theorem convex_C : Convex ℝ P.C := by
  rw [← P.convexDom_f₀]; exact P.convexFn_f₀.convex_convexDom

/-- The set $C$ of an ordinary convex program is nonempty, because it is the effective domain of the
proper function $f_0$. -/
theorem nonempty_C : P.C.Nonempty := by
  rw [← P.convexDom_f₀]; exact P.properConvex_f₀.convexDom_nonempty

/-- The set $C$ of an ordinary convex program has a nonempty relative interior (Theorem 6.2). -/
theorem relint_C_nonempty : (ri P.C).Nonempty :=
  Convex.relint_nonempty P.convex_C P.nonempty_C

/-- A point $x$ lies in $C$ if and only if $f_0(x) < +\infty$. -/
@[simp] theorem mem_C_iff {x : Rn n} : x ∈ P.C ↔ P.f₀ x < ⊤ := by
  rw [← P.convexDom_f₀]; exact mem_convexDom

/-- If $x \notin C$, then $f_0(x) = +\infty$. -/
theorem f₀_eq_top_of_notMem {x : Rn n} (hx : x ∉ P.C) : P.f₀ x = ⊤ := by
  by_contra hc
  exact hx (P.mem_C_iff.2 (lt_of_le_of_ne le_top hc))

/-- No constraint function takes the value $-\infty$: $f_i(x) \neq -\infty$ for all $i$ and all $x$,
because $f_1, \dots, f_r$ are proper and $f_{r+1}, \dots, f_m$ are real-valued. -/
theorem f_ne_bot (i : Fin m) (x : Rn n) : P.f i x ≠ ⊥ := by
  rcases lt_or_ge (i : ℕ) P.r with hi | hi
  · exact (P.properConvex_f i hi).ne_bot x
  · obtain ⟨a, ha⟩ := P.exists_affine i hi
    rw [ha x]; exact EReal.coe_ne_bot _

/-- Every constraint function is finite on $C$: for $x \in C$ and each $i$, $f_i(x)$ is a real
number. This follows from extension convention (b) for $i \le r$, and from convention (c) for
$i > r$. -/
theorem exists_coe_f {x : Rn n} (hx : x ∈ P.C) (i : Fin m) : ∃ c : ℝ, P.f i x = (c : EReal) := by
  rcases lt_or_ge (i : ℕ) P.r with hi | hi
  · exact EReal.exists_coe_of_ne_bot_of_lt_top ((P.properConvex_f i hi).ne_bot x)
      (mem_convexDom.1 (P.subset_convexDom_f i hi hx))
  · obtain ⟨a, ha⟩ := P.exists_affine i hi
    exact ⟨a x, ha x⟩

/-! ### Feasible solutions, the objective function and the optimal value -/

/-- **Section 28** of [rockafellar1970convex], definition of the feasible set. The set $C_0$ of
**feasible solutions** to $(P)$ is the set of $x \in C$ with $f_i(x) \le 0$ for
$i = 1, \dots, r$ and $f_i(x) = 0$ for $i = r + 1, \dots, m$. -/
def feasibleSet : Set (Rn n) :=
  {x | x ∈ P.C ∧ (∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ 0) ∧
    ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = 0}

/-- A point $x$ is a feasible solution if and only if $x \in C$, $f_i(x) \le 0$ for $i \le r$, and
$f_i(x) = 0$ for $i > r$. -/
@[simp] theorem mem_feasibleSet {x : Rn n} :
    x ∈ P.feasibleSet ↔ x ∈ P.C ∧ (∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ 0) ∧
      ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = 0 := Iff.rfl

/-- Every feasible solution lies in $C$: $C_0 \subseteq C$. -/
theorem feasibleSet_subset_C : P.feasibleSet ⊆ P.C := fun _ hx => hx.1

/-- **Section 28** of [rockafellar1970convex], the sets cut out by the constraints. This is the
intersection $C_1 \cap \dots \cap C_m$, where $C_i = \{x \mid f_i(x) \le 0\}$ for
$i = 1, \dots, r$ and $C_i = \{x \mid f_i(x) = 0\}$ for $i = r + 1, \dots, m$.

The feasible set is $C_0 = C \cap C_1 \cap \dots \cap C_m$
(`Rockafellar.OrdinaryConvexProgram.feasibleSet_eq_inter`). -/
def constraintSet : Set (Rn n) :=
  {x | (∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ 0) ∧ ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = 0}

/-- The feasible set is $C_0 = C \cap C_1 \cap \dots \cap C_m$. -/
theorem feasibleSet_eq_inter : P.feasibleSet = P.C ∩ P.constraintSet := rfl

/-- The set $C_1 \cap \dots \cap C_m$ is convex, because the inequality constraint functions are
convex and the equality constraint functions are affine. -/
theorem convex_constraintSet : Convex ℝ P.constraintSet := by
  rintro x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ a b ha hb hab
  refine ⟨fun i hi => (P.convexFn_f i hi).convex_le 0 (hx₁ i hi) (hy₁ i hi) ha hb hab,
    fun i hi => ?_⟩
  obtain ⟨g, hg⟩ := P.exists_affine i hi
  have hxg : g x = 0 := by
    have := hx₂ i hi; rw [hg] at this; exact_mod_cast this
  have hyg : g y = 0 := by
    have := hy₂ i hi; rw [hg] at this; exact_mod_cast this
  have hab' : a • x + b • y = (1 - b) • x + b • y := by rw [show (1 : ℝ) - b = a by linarith]
  rw [hg, hab', affineMap_segment g x y b, hxg, hyg]
  norm_num

/-- **Section 28** of [rockafellar1970convex], definition of the objective function. The **objective
function** of $(P)$ is $f = f_0 + \delta(\cdot \mid C_0)$: it is $f_0(x)$ for a feasible
solution $x$, and $+\infty$ otherwise. -/
noncomputable def objective : Rn n → EReal := fun x => P.f₀ x + indicatorFn P.feasibleSet x

/-- At a feasible solution $x$, the objective function is $f(x) = f_0(x)$. -/
@[simp] theorem objective_of_mem {x : Rn n} (hx : x ∈ P.feasibleSet) :
    P.objective x = P.f₀ x := by
  rw [objective, indicatorFn_of_mem hx, add_zero]

/-- At a point $x$ that is not a feasible solution, the objective function is $f(x) = +\infty$. -/
@[simp] theorem objective_of_notMem {x : Rn n} (hx : x ∉ P.feasibleSet) : P.objective x = ⊤ := by
  rw [objective, indicatorFn_of_notMem hx,
    EReal.add_top_of_ne_bot (P.properConvex_f₀.ne_bot x)]

/-- The objective function is $f_0$ restricted to $C_1 \cap \dots \cap C_m$ and extended by
$+\infty$. The condition $x \in C$ is not needed, because $f_0$ is already $+\infty$ off $C$. In
this form the convexity and the closedness of $f$ follow from those of $f_0$. -/
theorem objective_eq_convexRestrict :
    P.objective = ConvexAnalysis.convexRestrict P.constraintSet P.f₀ := by
  funext x
  by_cases hx : x ∈ P.constraintSet
  · by_cases hC : x ∈ P.C
    · rw [P.objective_of_mem ⟨hC, hx⟩, convexRestrict_of_mem hx]
    · rw [P.objective_of_notMem (fun h => hC h.1), convexRestrict_of_mem hx,
        P.f₀_eq_top_of_notMem hC]
  · rw [P.objective_of_notMem (fun h => hx h.2), convexRestrict_of_notMem hx]

/-- The objective function of an ordinary convex program is convex. -/
theorem convexFn_objective : ConvexFn P.objective := by
  rw [P.objective_eq_convexRestrict]
  exact P.convexFn_f₀.convexRestrict P.convex_constraintSet

/-- **Section 28** of [rockafellar1970convex]: if $f_0, f_1, \dots, f_r$ are closed, then the
objective function $f$ is closed. -/
theorem closedConvex_objective (hcl₀ : ClosedConvex P.f₀)
    (hcl : ∀ i : Fin m, (i : ℕ) < P.r → ClosedConvex (P.f i)) : ClosedConvex P.objective := by
  have hclosed : IsClosed P.constraintSet := by
    have h₁ : P.constraintSet = (⋂ i : Fin m, ⋂ _ : (i : ℕ) < P.r, {x | P.f i x ≤ 0})
        ∩ ⋂ i : Fin m, ⋂ _ : P.r ≤ (i : ℕ), {x | P.f i x = 0} := by
      ext x; simp only [constraintSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [h₁]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun hi => ?_)
      (isClosed_iInter fun i => isClosed_iInter fun hi => ?_)
    · exact lowerSemicontinuous_iff_isClosed_le.1
        ((closedConvex_iff_lowerSemicontinuous (P.properConvex_f i hi).ne_bot).1 (hcl i hi)) 0
    · obtain ⟨g, hg⟩ := P.exists_affine i hi
      have hset : {x : Rn n | P.f i x = 0} = g ⁻¹' {0} := by
        ext x
        rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, hg]
        exact ⟨fun h => by exact_mod_cast h, fun h => by rw [h]; rfl⟩
      rw [hset]
      exact IsClosed.preimage g.continuous_of_finiteDimensional isClosed_singleton
  rw [P.objective_eq_convexRestrict]
  exact ClosedConvex.convexRestrict hcl₀ P.properConvex_f₀.ne_bot hclosed

/-- The objective function never takes the value $-\infty$. -/
theorem objective_ne_bot (x : Rn n) : P.objective x ≠ ⊥ := by
  by_cases hx : x ∈ P.feasibleSet
  · rw [P.objective_of_mem hx]; exact P.properConvex_f₀.ne_bot x
  · rw [P.objective_of_notMem hx]; exact top_ne_bot

/-- **Section 28** of [rockafellar1970convex], definition of the optimal value. The **optimal
value** in $(P)$ is the infimum of the objective function $f$ over $\mathbb{R}^n$, an element of
$[-\infty, +\infty]$. It is $+\infty$ if $(P)$ has no feasible solution. -/
noncomputable def optimalValue : EReal := ⨅ x, P.objective x

/-- The optimal value is the infimum of $f_0$ over the feasible solutions:
$\inf f = \inf \{f_0(x) \mid x \in C_0\}$. -/
theorem optimalValue_eq_biInf : P.optimalValue = ⨅ x ∈ P.feasibleSet, P.f₀ x := by
  refine le_antisymm (le_iInf₂ fun x hx => ?_) (le_iInf fun x => ?_)
  · exact (iInf_le _ x).trans (le_of_eq (P.objective_of_mem hx))
  · by_cases hx : x ∈ P.feasibleSet
    · exact (iInf₂_le x hx).trans (le_of_eq (P.objective_of_mem hx).symm)
    · rw [P.objective_of_notMem hx]; exact le_top

/-- The optimal value is at most $f_0(x)$ for every feasible solution $x$. -/
theorem optimalValue_le {x : Rn n} (hx : x ∈ P.feasibleSet) : P.optimalValue ≤ P.f₀ x := by
  rw [P.optimalValue_eq_biInf]; exact iInf₂_le x hx

/-- **Section 28** of [rockafellar1970convex], definition of the optimal solutions. The **optimal
solutions** to $(P)$ are the points at which the objective function $f$ attains its infimum over
$\mathbb{R}^n$.

The book adds the proviso "provided that $f$ is not identically $+\infty$". Here the set is
defined in all cases: if $(P)$ has no feasible solution, every point of $\mathbb{R}^n$ is an
optimal solution. Each theorem about optimal solutions has a hypothesis that excludes this case.
The set is `ConvexAnalysis.argmin` of `Rockafellar.OrdinaryConvexProgram.objective`. -/
noncomputable def optimalSolutions : Set (Rn n) := argmin P.objective

/-- A point $x$ is an optimal solution if and only if $f(x)$ equals the optimal value. -/
theorem mem_optimalSolutions_iff {x : Rn n} :
    x ∈ P.optimalSolutions ↔ P.objective x = P.optimalValue :=
  ⟨fun hx => (iInf_eq_of_mem_argmin hx).symm, fun hx z => by
    rw [hx, optimalValue]; exact iInf_le _ z⟩

/-- If the optimal value is not $+\infty$, then $x$ is an optimal solution if and only if $x$ is a
feasible solution and $f_0(x)$ equals the optimal value. -/
theorem mem_optimalSolutions_iff_of_ne_top (h : P.optimalValue ≠ ⊤) {x : Rn n} :
    x ∈ P.optimalSolutions ↔ x ∈ P.feasibleSet ∧ P.f₀ x = P.optimalValue := by
  rw [P.mem_optimalSolutions_iff]
  constructor
  · intro hx
    by_cases hf : x ∈ P.feasibleSet
    · exact ⟨hf, by rwa [P.objective_of_mem hf] at hx⟩
    · exact absurd (by rw [← hx, P.objective_of_notMem hf]) h
  · rintro ⟨hf, hv⟩; rw [P.objective_of_mem hf, hv]

/-! ### Kuhn–Tucker vectors -/

/-- **Section 28** of [rockafellar1970convex], the function $h$. For $\lambda = (\lambda_1, \dots,
\lambda_m) \in \mathbb{R}^m$ it is
$$h(x) = f_0(x) + \lambda_1 f_1(x) + \dots + \lambda_m f_m(x), \qquad x \in \mathbb{R}^n.$$
A Kuhn–Tucker vector is a vector $\lambda$ for which the infimum of $h$ is the optimal value in
$(P)$.

The sum and the products are taken in `EReal`, where $0 \cdot (\pm\infty) = 0$. The function $h$
is not the Lagrangian of $(P)$, which is `Rockafellar.OrdinaryConvexProgram.programLagrangian`. -/
noncomputable def lagrangeFn (u : Rn m) : Rn n → EReal :=
  fun x => P.f₀ x + ∑ i, (u i : EReal) * P.f i x

/-- The defining formula $h(x) = f_0(x) + \sum_i \lambda_i f_i(x)$. -/
theorem lagrangeFn_apply (u : Rn m) (x : Rn n) :
    P.lagrangeFn u x = P.f₀ x + ∑ i, (u i : EReal) * P.f i x := rfl

/-- **Section 28** of [rockafellar1970convex], definition of Kuhn–Tucker coefficients. A vector
$(\lambda_1, \dots, \lambda_m) \in \mathbb{R}^m$ is a vector of **Kuhn–Tucker coefficients** for
$(P)$, or a **Kuhn–Tucker vector**, if $\lambda_i \ge 0$ for $i = 1, \dots, r$ and the infimum
of $h = f_0 + \lambda_1 f_1 + \dots + \lambda_m f_m$ over $\mathbb{R}^n$ is finite and equal to
the optimal value in $(P)$.

This is the definition of Section 28, not the equivalent condition on the perturbation function
of Section 29. The equivalence of the two is not stated in this module. -/
structure IsKuhnTuckerVector (P : OrdinaryConvexProgram n m) (u : Rn m) : Prop where
  /-- The multipliers of the inequality constraints are nonnegative: $\lambda_i \ge 0$ for
  $i = 1, \dots, r$. -/
  nonneg : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i
  /-- The infimum of $h$ over $\mathbb{R}^n$ is not $-\infty$. -/
  ne_bot : (⨅ x, P.lagrangeFn u x) ≠ ⊥
  /-- The infimum of $h$ over $\mathbb{R}^n$ is not $+\infty$. -/
  ne_top : (⨅ x, P.lagrangeFn u x) ≠ ⊤
  /-- The infimum of $h$ over $\mathbb{R}^n$ is the optimal value in $(P)$. -/
  iInf_eq : (⨅ x, P.lagrangeFn u x) = P.optimalValue

/-! ### The function $h$ as a finite sum, and its convexity, properness and closedness -/

/-- The $m + 1$ summands of $h = f_0 + \lambda_1 f_1 + \dots + \lambda_m f_m$: the summand at index
$0$ is $f_0$, and the summand at index $i$ is $\lambda_i f_i$.

The summands are indexed by `Option (Fin m)`, with $f_0$ at `none`. Theorem 23.8 is stated for a
finite family of functions, and this is the form in which the subdifferential of $h$ is
computed. -/
noncomputable def lagrangeSummand (u : Rn m) (i : Option (Fin m)) : Rn n → EReal :=
  i.elim P.f₀ fun j x => (u j : EReal) * P.f j x

/-- The summand of $h$ at index $0$ is $f_0$. -/
@[simp] theorem lagrangeSummand_none (u : Rn m) : P.lagrangeSummand u none = P.f₀ := rfl

/-- The summand of $h$ at index $i$ is $\lambda_i f_i$. -/
@[simp] theorem lagrangeSummand_some (u : Rn m) (j : Fin m) :
    P.lagrangeSummand u (some j) = fun x => (u j : EReal) * P.f j x := rfl

/-- The function $h$ is the sum of its $m + 1$ summands $f_0, \lambda_1 f_1, \dots, \lambda_m f_m$.
-/
theorem lagrangeFn_eq_finsetSum (u : Rn m) :
    P.lagrangeFn u = ∑ i : Option (Fin m), P.lagrangeSummand u i := by
  funext x
  rw [Finset.sum_apply, Fintype.sum_option]
  rfl

/-- If $\lambda_i \ge 0$ for $i \le r$, then every summand
$f_0, \lambda_1 f_1, \dots, \lambda_m f_m$ of $h$ is convex. -/
theorem convexFn_lagrangeSummand {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i)
    (i : Option (Fin m)) : ConvexFn (P.lagrangeSummand u i) := by
  cases i with
  | none => exact P.convexFn_f₀
  | some j =>
    rcases lt_or_ge (j : ℕ) P.r with hj | hj
    · exact convexFn_coe_mul (hu j hj) (P.convexFn_f j hj)
    · obtain ⟨g, hg⟩ := P.exists_affine j hj
      have hrw : P.lagrangeSummand u (some j) = fun x => (((u j • g) x : ℝ) : EReal) := by
        funext x
        simp only [lagrangeSummand_some]
        rw [hg x, ← EReal.coe_mul, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [hrw]
      exact (closedProperConvexFn_coe_affineMap
        (u j • g).continuous_of_finiteDimensional).convex

/-- If $\lambda_i \ge 0$ for $i \le r$, then every summand
$f_0, \lambda_1 f_1, \dots, \lambda_m f_m$ of $h$ is proper. -/
theorem properConvex_lagrangeSummand {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i)
    (i : Option (Fin m)) : ProperConvex (P.lagrangeSummand u i) := by
  cases i with
  | none => exact P.properConvex_f₀
  | some j =>
    rcases lt_or_ge (j : ℕ) P.r with hj | hj
    · exact properConvex_coe_mul (hu j hj) (P.properConvex_f j hj)
    · obtain ⟨g, hg⟩ := P.exists_affine j hj
      have hrw : P.lagrangeSummand u (some j) = fun x => (((u j • g) x : ℝ) : EReal) := by
        funext x
        simp only [lagrangeSummand_some]
        rw [hg x, ← EReal.coe_mul, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [hrw]
      exact (closedProperConvexFn_coe_affineMap
        (u j • g).continuous_of_finiteDimensional).proper

/-- If $f_0, f_1, \dots, f_r$ are closed and $\lambda_i \ge 0$ for $i \le r$, then every summand
$f_0, \lambda_1 f_1, \dots, \lambda_m f_m$ of $h$ is closed. -/
theorem closedConvex_lagrangeSummand (hcl₀ : ClosedConvex P.f₀)
    (hcl : ∀ i : Fin m, (i : ℕ) < P.r → ClosedConvex (P.f i)) {u : Rn m}
    (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) (i : Option (Fin m)) :
    ClosedConvex (P.lagrangeSummand u i) := by
  cases i with
  | none => exact hcl₀
  | some j =>
    rcases lt_or_ge (j : ℕ) P.r with hj | hj
    · exact closedConvex_coe_mul (hu j hj) (hcl j hj) (P.properConvex_f j hj).ne_bot
    · obtain ⟨g, hg⟩ := P.exists_affine j hj
      have hrw : P.lagrangeSummand u (some j) = fun x => (((u j • g) x : ℝ) : EReal) := by
        funext x
        simp only [lagrangeSummand_some]
        rw [hg x, ← EReal.coe_mul, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [hrw]
      exact (closedProperConvexFn_coe_affineMap
        (u j • g).continuous_of_finiteDimensional).closed

/-- Every point of $C$ lies in the effective domain of every summand of $h$, for every $\lambda$. -/
theorem mem_convexDom_lagrangeSummand (u : Rn m) {x : Rn n} (hx : x ∈ P.C) (i : Option (Fin m)) :
    x ∈ convexDom (P.lagrangeSummand u i) := by
  cases i with
  | none => rw [lagrangeSummand_none, P.convexDom_f₀]; exact hx
  | some j =>
    obtain ⟨c, hc⟩ := P.exists_coe_f hx j
    rw [mem_convexDom]
    simp only [lagrangeSummand_some]
    rw [hc, ← EReal.coe_mul]
    exact EReal.coe_lt_top _

/-- If $\lambda_i \ge 0$ for $i \le r$, then $h$ is convex. -/
theorem convexFn_lagrangeFn {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) :
    ConvexFn (P.lagrangeFn u) := by
  obtain ⟨x₀, hx₀⟩ := P.nonempty_C
  rw [P.lagrangeFn_eq_finsetSum u]
  exact (properConvexFn_finsetSum (fun i _ => P.convexFn_lagrangeSummand hu i)
    (fun i _ => P.properConvex_lagrangeSummand hu i)
    (fun i _ => P.mem_convexDom_lagrangeSummand u hx₀ i)).1

/-- If $\lambda_i \ge 0$ for $i \le r$, then $h$ is proper. -/
theorem properConvex_lagrangeFn {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) :
    ProperConvex (P.lagrangeFn u) := by
  obtain ⟨x₀, hx₀⟩ := P.nonempty_C
  rw [P.lagrangeFn_eq_finsetSum u]
  exact (properConvexFn_finsetSum (fun i _ => P.convexFn_lagrangeSummand hu i)
    (fun i _ => P.properConvex_lagrangeSummand hu i)
    (fun i _ => P.mem_convexDom_lagrangeSummand u hx₀ i)).2.1

/-- If $f_0, f_1, \dots, f_r$ are closed and $\lambda_i \ge 0$ for $i \le r$, then $h$ is a closed
proper convex function. This is the first step of the proof of Corollary 28.1.1. -/
theorem closedProperConvexFn_lagrangeFn (hcl₀ : ClosedConvex P.f₀)
    (hcl : ∀ i : Fin m, (i : ℕ) < P.r → ClosedConvex (P.f i)) {u : Rn m}
    (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) : ClosedProperConvexFn (P.lagrangeFn u) := by
  obtain ⟨x₀, hx₀⟩ := P.nonempty_C
  rw [P.lagrangeFn_eq_finsetSum u]
  exact closedProperConvexFn_finsetSum
    (fun i _ => ⟨P.convexFn_lagrangeSummand hu i, P.closedConvex_lagrangeSummand hcl₀ hcl hu i,
      P.properConvex_lagrangeSummand hu i⟩)
    (fun i _ => P.mem_convexDom_lagrangeSummand u hx₀ i)

/-! ### Elementary properties of $h$ -/

/-- If $\lambda_i \ge 0$ for $i \le r$, then $\lambda_1 f_1(x) + \dots + \lambda_m f_m(x) \neq
-\infty$ for every $x$. -/
theorem sum_coe_mul_f_ne_bot {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) (x : Rn n) :
    (∑ i, (u i : EReal) * P.f i x) ≠ ⊥ := by
  refine EReal.sum_ne_bot fun i _ => ?_
  rcases lt_or_ge (i : ℕ) P.r with hi | hi
  · exact EReal.coe_mul_ne_bot (hu i hi) (P.f_ne_bot i x)
  · obtain ⟨g, hg⟩ := P.exists_affine i hi
    rw [hg x, ← EReal.coe_mul]
    exact EReal.coe_ne_bot _

/-- If $\lambda_i \ge 0$ for $i \le r$, then $h(x) \neq -\infty$ for every $x$. -/
theorem lagrangeFn_ne_bot {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) (x : Rn n) :
    P.lagrangeFn u x ≠ ⊥ :=
  EReal.add_ne_bot_iff.2 ⟨P.properConvex_f₀.ne_bot x, P.sum_coe_mul_f_ne_bot hu x⟩

/-- If $\lambda_i \ge 0$ for $i \le r$ and $x \notin C$, then $h(x) = +\infty$. -/
theorem lagrangeFn_eq_top_of_notMem_C {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i)
    {x : Rn n} (hx : x ∉ P.C) : P.lagrangeFn u x = ⊤ := by
  rw [lagrangeFn_apply, P.f₀_eq_top_of_notMem hx,
    EReal.top_add_of_ne_bot (P.sum_coe_mul_f_ne_bot hu x)]

/-- If $f_0(x) = c_0$ and $f_i(x) = c_i$ are real numbers, then $h(x)$ is the real number
$c_0 + \sum_i \lambda_i c_i$. -/
theorem lagrangeFn_eq_coe {u : Rn m} {x : Rn n} {c₀ : ℝ} (h₀ : P.f₀ x = (c₀ : EReal))
    {c : Fin m → ℝ} (hc : ∀ i, P.f i x = (c i : EReal)) :
    P.lagrangeFn u x = ((c₀ + ∑ i, u i * c i : ℝ) : EReal) := by
  rw [lagrangeFn_apply, h₀,
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [hc i, ← EReal.coe_mul]),
    ← EReal.coe_sum, ← EReal.coe_add]

/-- If $\lambda_i f_i(x) = 0$ for every $i$, then $h(x) = f_0(x)$. -/
theorem lagrangeFn_eq_f₀ {u : Rn m} {x : Rn n} (h : ∀ i : Fin m, (u i : EReal) * P.f i x = 0) :
    P.lagrangeFn u x = P.f₀ x := by
  rw [lagrangeFn_apply, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h i),
    Finset.sum_const_zero, add_zero]

/-- If $\lambda_i \ge 0$ for $i \le r$, then $h(x) \le f_0(x)$ at every feasible solution $x$,
because each term $\lambda_i f_i(x)$ is then nonpositive. The proof of Theorem 28.1 rests on
this inequality. -/
theorem lagrangeFn_le_f₀ {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) {x : Rn n}
    (hx : x ∈ P.feasibleSet) : P.lagrangeFn u x ≤ P.f₀ x := by
  have hsum : (∑ i, (u i : EReal) * P.f i x) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    rcases lt_or_ge (i : ℕ) P.r with hi | hi
    · exact coe_mul_nonpos (hu i hi) (hx.2.1 i hi)
    · rw [hx.2.2 i hi]; simp
  calc P.lagrangeFn u x ≤ P.f₀ x + 0 := add_le_add (le_refl _) hsum
    _ = P.f₀ x := add_zero _

/-- If $\lambda_i \ge 0$ for $i \le r$, then $h \le f$ everywhere, where $f$ is the objective
function: at a feasible solution by `Rockafellar.OrdinaryConvexProgram.lagrangeFn_le_f₀`, and
elsewhere because $f$ is $+\infty$ there. -/
theorem lagrangeFn_le_objective {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i)
    (x : Rn n) : P.lagrangeFn u x ≤ P.objective x := by
  by_cases hx : x ∈ P.feasibleSet
  · rw [P.objective_of_mem hx]; exact P.lagrangeFn_le_f₀ hu hx
  · rw [P.objective_of_notMem hx]; exact le_top

/-- If $\lambda_i \ge 0$ for $i \le r$, then the infimum of $h$ over $\mathbb{R}^n$ is at most the
optimal value in $(P)$. -/
theorem iInf_lagrangeFn_le_optimalValue {u : Rn m}
    (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) : (⨅ x, P.lagrangeFn u x) ≤ P.optimalValue :=
  le_iInf fun x => (iInf_le _ x).trans (P.lagrangeFn_le_objective hu x)

/-- If $(P)$ has a Kuhn–Tucker vector, then its optimal value is not $+\infty$. -/
theorem IsKuhnTuckerVector.optimalValue_ne_top {u : Rn m} (hu : P.IsKuhnTuckerVector u) :
    P.optimalValue ≠ ⊤ := by rw [← hu.iInf_eq]; exact hu.ne_top

/-- If $(P)$ has a Kuhn–Tucker vector, then its optimal value is not $-\infty$. -/
theorem IsKuhnTuckerVector.optimalValue_ne_bot {u : Rn m} (hu : P.IsKuhnTuckerVector u) :
    P.optimalValue ≠ ⊥ := by rw [← hu.iInf_eq]; exact hu.ne_bot

end OrdinaryConvexProgram

variable (P : OrdinaryConvexProgram n m)

/-! ### Theorem 28.1: solving $(P)$ by minimizing $h$ -/

/-- **Theorem 28.1** of [rockafellar1970convex]. Let $(\lambda_1, \dots, \lambda_m)$ be a
Kuhn–Tucker vector for $(P)$, and let $h = f_0 + \lambda_1 f_1 + \dots + \lambda_m f_m$. Let $I$
be the set of indices $i \le r$ with $\lambda_i = 0$, and let $J$ be the complement of $I$ in
$\{1, \dots, m\}$. Then a point $\bar x$ is an optimal solution to $(P)$ if and only if $\bar x$
minimizes $h$ over $\mathbb{R}^n$, $f_i(\bar x) \le 0$ for every $i \in I$, and
$f_i(\bar x) = 0$ for every $i \in J$.

The book summarizes the proof as "$h \le f$ everywhere, with equality if and only if $x$ is a
feasible solution such that $\lambda_i f_i(x) = 0$". This summary is slightly too strong:
outside $C$ both functions are $+\infty$, so equality also holds at these points, which are not
feasible. The theorem is not affected, because the infimum of $h$ is finite, so no such point
minimizes $h$ or $f$. -/
theorem theorem_28_1 {u : Rn m} (hu : P.IsKuhnTuckerVector u) :
    {x : Rn n | x ∈ argmin (P.lagrangeFn u) ∧
        (∀ i : Fin m, ((i : ℕ) < P.r ∧ u i = 0) → P.f i x ≤ 0) ∧
        ∀ i : Fin m, ¬((i : ℕ) < P.r ∧ u i = 0) → P.f i x = 0}
      = P.optimalSolutions := by
  ext x
  constructor
  · rintro ⟨hD, hI, hJ⟩
    have hhx : P.lagrangeFn u x = ⨅ z, P.lagrangeFn u z := (iInf_eq_of_mem_argmin hD).symm
    have hxC : x ∈ P.C := by
      by_contra hc
      rw [P.lagrangeFn_eq_top_of_notMem_C hu.nonneg hc] at hhx
      exact hu.ne_top hhx.symm
    have hfeas : x ∈ P.feasibleSet := by
      refine ⟨hxC, fun i hi => ?_, fun i hi => hJ i fun hc => absurd hc.1 (by omega)⟩
      by_cases h0 : u i = 0
      · exact hI i ⟨hi, h0⟩
      · exact le_of_eq (hJ i fun hc => h0 hc.2)
    have hcs : ∀ i : Fin m, (u i : EReal) * P.f i x = 0 := by
      intro i
      by_cases h0 : (i : ℕ) < P.r ∧ u i = 0
      · rw [h0.2]; simp
      · rw [hJ i h0]; simp
    have hf₀ : P.f₀ x = P.optimalValue := by
      rw [← P.lagrangeFn_eq_f₀ hcs, hhx, hu.iInf_eq]
    rw [P.mem_optimalSolutions_iff, P.objective_of_mem hfeas, hf₀]
  · intro hx
    obtain ⟨hfeas, hf₀⟩ := (P.mem_optimalSolutions_iff_of_ne_top hu.optimalValue_ne_top).1 hx
    have hD : x ∈ argmin (P.lagrangeFn u) := by
      refine mem_argmin_iff_le_iInf.2 ?_
      rw [hu.iInf_eq, ← hf₀]
      exact P.lagrangeFn_le_f₀ hu.nonneg hfeas
    have heq : P.lagrangeFn u x = P.f₀ x := by
      refine le_antisymm (P.lagrangeFn_le_f₀ hu.nonneg hfeas) ?_
      rw [hf₀, ← hu.iInf_eq]
      exact iInf_le _ x
    -- read the identity `h x = f₀ x` as an identity between real numbers
    obtain ⟨c₀, hc₀⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (P.properConvex_f₀.ne_bot x)
      (P.mem_C_iff.1 hfeas.1)
    choose c hc using P.exists_coe_f hfeas.1
    have hzero : ∑ i, u i * c i = 0 := by
      have h := P.lagrangeFn_eq_coe (u := u) hc₀ hc
      rw [heq, hc₀, EReal.coe_eq_coe_iff] at h
      linarith
    have hnonpos : ∀ i ∈ Finset.univ, u i * c i ≤ 0 := by
      intro i _
      rcases lt_or_ge (i : ℕ) P.r with hi | hi
      · have hci : c i ≤ 0 := by
          have := hfeas.2.1 i hi
          rw [hc i] at this
          exact_mod_cast this
        exact mul_nonpos_of_nonneg_of_nonpos (hu.nonneg i hi) hci
      · have hci : c i = 0 := by
          have := hfeas.2.2 i hi
          rw [hc i] at this
          exact_mod_cast this
        rw [hci, mul_zero]
    have hterm := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).1 hzero
    refine ⟨hD, fun i hi => hfeas.2.1 i hi.1, fun i hi => ?_⟩
    rcases lt_or_ge (i : ℕ) P.r with h | h
    · have h0 : u i ≠ 0 := fun hc' => hi ⟨h, hc'⟩
      have := hterm i (Finset.mem_univ i)
      rw [hc i]
      exact_mod_cast (mul_eq_zero.1 this).resolve_left h0
    · exact hfeas.2.2 i h

/-- **Corollary 28.1.1** of [rockafellar1970convex]. Let $(\lambda_1, \dots, \lambda_m)$ be a
Kuhn–Tucker vector for $(P)$, and let $f_0, f_1, \dots, f_r$ be closed. If $h = f_0 + \lambda_1
f_1 + \dots + \lambda_m f_m$ attains its infimum over $\mathbb{R}^n$ at a unique point $w$, then
$w$ is the unique optimal solution to $(P)$.

The equality constraint functions are affine, so they are closed without a hypothesis.
Uniqueness follows from Theorem 28.1. Existence is the content: since $\operatorname{epi} f
\subseteq \operatorname{epi} h$, the objective function $f$ has no direction of recession, and
Theorem 27.2 applies. -/
theorem corollary_28_1_1 (hcl₀ : ClosedConvex P.f₀)
    (hcl : ∀ i : Fin m, (i : ℕ) < P.r → ClosedConvex (P.f i)) {u : Rn m}
    (hu : P.IsKuhnTuckerVector u) {w : Rn n} (hmin : argmin (P.lagrangeFn u) = {w}) :
    P.optimalSolutions = {w} := by
  have hh : ClosedProperConvexFn (P.lagrangeFn u) :=
    P.closedProperConvexFn_lagrangeFn hcl₀ hcl hu.nonneg
  have hw : w ∈ argmin (P.lagrangeFn u) := by rw [hmin]; rfl
  have hwval : P.lagrangeFn u w = P.optimalValue := by
    rw [(iInf_eq_of_mem_argmin hw).symm, hu.iInf_eq]
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hh.proper.ne_bot w)
    (by rw [hwval]; exact lt_of_le_of_ne le_top hu.optimalValue_ne_top)
  -- `h` has no directions of recession, because its minimum set is a single point
  have hneμ : {z : Rn n | P.lagrangeFn u z ≤ (μ : EReal)}.Nonempty := ⟨w, le_of_eq hμ⟩
  have hrec : recessionConeFn (P.lagrangeFn u) = {(0 : Rn n)} := by
    rw [← recessionCone_setOf_le hh.convex hh.isClosed_epi hneμ, ← argmin_eq_setOf_le hw hμ, hmin]
    exact (isCompact_iff_recessionCone_eq_zero (convex_singleton w) isClosed_singleton
      ⟨w, rfl⟩).1 isCompact_singleton
  -- a level set of the objective at a level above the optimal value
  have hlt : P.optimalValue < ((μ + 1 : ℝ) : EReal) := by
    rw [← hwval, hμ, EReal.coe_lt_coe_iff]; linarith
  obtain ⟨z₀, hz₀⟩ : ∃ z, P.objective z < ((μ + 1 : ℝ) : EReal) := iInf_lt_iff.1 hlt
  have hfobj : ClosedProperConvexFn P.objective :=
    ⟨P.convexFn_objective, P.closedConvex_objective hcl₀ hcl,
      ⟨⟨z₀, mem_convexDom.2 (hz₀.trans (EReal.coe_lt_top _))⟩, P.objective_ne_bot⟩⟩
  have hneβ : {z : Rn n | P.objective z ≤ ((μ + 1 : ℝ) : EReal)}.Nonempty := ⟨z₀, hz₀.le⟩
  have hneβh : {z : Rn n | P.lagrangeFn u z ≤ ((μ + 1 : ℝ) : EReal)}.Nonempty :=
    ⟨z₀, (P.lagrangeFn_le_objective hu.nonneg z₀).trans hz₀.le⟩
  have hclosedf : IsClosed {z : Rn n | P.objective z ≤ ((μ + 1 : ℝ) : EReal)} :=
    lowerSemicontinuous_iff_isClosed_le.1 hfobj.lowerSemicontinuous _
  have hcomph : IsCompact {z : Rn n | P.lagrangeFn u z ≤ ((μ + 1 : ℝ) : EReal)} :=
    isCompact_setOf_le hh.convex hh.closed hh.proper hrec hneβh
  have hcompf : IsCompact {z : Rn n | P.objective z ≤ ((μ + 1 : ℝ) : EReal)} :=
    hcomph.of_isClosed_subset hclosedf
      fun z hz => (P.lagrangeFn_le_objective hu.nonneg z).trans hz
  have hrecf : recessionConeFn P.objective = {(0 : Rn n)} := by
    rw [← recessionCone_setOf_le hfobj.convex hfobj.isClosed_epi hneβ]
    exact (isCompact_iff_recessionCone_eq_zero (hfobj.convex.convex_le _) hclosedf hneβ).1 hcompf
  have hne' : P.optimalSolutions.Nonempty :=
    argmin_nonempty_of_recessionConeFn_eq_zero hfobj.convex hfobj.closed hfobj.proper hrecf
  refine (hne'.subset_singleton_iff).1 ?_
  rw [← theorem_28_1 P hu]
  rintro x ⟨hD, -, -⟩
  rw [← hmin]
  exact hD

/-! ### The perturbation function and the bifunction of $(P)$ -/

namespace OrdinaryConvexProgram

/-- **Section 28** of [rockafellar1970convex], the bifunction of an ordinary convex program. For
$u = (v_1, \dots, v_m) \in \mathbb{R}^m$ and $x \in \mathbb{R}^n$, $F(u, x) = f_0(x)$ if
$f_i(x) \le v_i$ for $i = 1, \dots, r$ and $f_i(x) = v_i$ for $i = r + 1, \dots, m$, and
$F(u, x) = +\infty$ otherwise. Thus $F(u, \cdot)$ is the objective function of the perturbed
program $(P_u)$, and $(P)$ is a generalized convex program in the sense of Section 29.

The condition $x \in C$ is not imposed, because $f_0$ is already $+\infty$ off $C$. -/
noncomputable def ineqBifun : Bifun (Rn m) (Rn n) := fun u =>
  ConvexAnalysis.convexRestrict
    {y | (∀ i : Fin m, (i : ℕ) < P.r → P.f i y ≤ (u i : EReal)) ∧
      ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i y = (u i : EReal)} P.f₀

/-- If $x$ satisfies the constraints of the perturbed program $(P_u)$, then $F(u, x) = f_0(x)$. -/
theorem ineqBifun_of_mem {u : Rn m} {x : Rn n}
    (h : (∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ (u i : EReal)) ∧
      ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = (u i : EReal)) :
    P.ineqBifun u x = P.f₀ x := convexRestrict_of_mem h

/-- If $x$ does not satisfy the constraints of the perturbed program $(P_u)$, then
$F(u, x) = +\infty$. -/
theorem ineqBifun_of_notMem {u : Rn m} {x : Rn n}
    (h : ¬((∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ (u i : EReal)) ∧
      ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = (u i : EReal))) :
    P.ineqBifun u x = ⊤ := convexRestrict_of_notMem h

/-- If $x \notin C$, then $F(u, x) = +\infty$ for every $u$. -/
theorem ineqBifun_eq_top_of_notMem_C {x : Rn n} (hx : x ∉ P.C) (u : Rn m) :
    P.ineqBifun u x = ⊤ := by
  by_cases h : (∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ (u i : EReal)) ∧
      ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = (u i : EReal)
  · rw [P.ineqBifun_of_mem h]; exact P.f₀_eq_top_of_notMem hx
  · exact P.ineqBifun_of_notMem h

/-- At $u = 0$, the bifunction is the objective function of $(P)$: $F(0, \cdot) = f$. -/
@[simp] theorem ineqBifun_zero : P.ineqBifun 0 = P.objective := by
  have hz : ∀ i : Fin m, ((0 : Rn m) i : EReal) = 0 := fun i => by norm_num
  rw [P.objective_eq_convexRestrict]
  funext x
  by_cases hx : x ∈ P.constraintSet
  · rw [P.ineqBifun_of_mem ⟨fun i hi => by rw [hz i]; exact hx.1 i hi,
      fun i hi => by rw [hz i]; exact hx.2 i hi⟩, convexRestrict_of_mem hx]
  · refine (P.ineqBifun_of_notMem fun hc => hx ⟨fun i hi => ?_, fun i hi => ?_⟩).trans
      (convexRestrict_of_notMem hx).symm
    · have := hc.1 i hi; rwa [hz i] at this
    · have := hc.2 i hi; rwa [hz i] at this

/-- **Section 28** of [rockafellar1970convex], the perturbation function. The **perturbation
function** of $(P)$ is $p(u) = \inf_x F(u, x)$, the optimal value of the perturbed program
$(P_u)$. In particular $p(0)$ is the optimal value in $(P)$. -/
noncomputable def perturbFn : Rn m → EReal := infBifun P.ineqBifun

/-- The defining formula $p(u) = \inf_x F(u, x)$. -/
theorem perturbFn_apply (u : Rn m) : P.perturbFn u = ⨅ x, P.ineqBifun u x := rfl

/-- **Section 28** of [rockafellar1970convex]: "of course, $p(0)$ is the optimal value in $(P)$". -/
@[simp] theorem perturbFn_zero : P.perturbFn 0 = P.optimalValue := by
  rw [perturbFn_apply, P.ineqBifun_zero]; rfl

end OrdinaryConvexProgram

/-! ### Theorem 28.2: existence of Kuhn–Tucker vectors -/

namespace OrdinaryConvexProgram

/-- The optimal value is the infimum of $f_0$ over $C_1 \cap \dots \cap C_m$ instead of $C_0$. The
two infima agree because $f_0$ is $+\infty$ off $C$. This is the form of
`ConvexAnalysis.optimalValue`. -/
theorem optimalValue_eq_biInf_constraintSet :
    P.optimalValue = ⨅ x ∈ P.constraintSet, P.f₀ x := by
  have h : P.optimalValue = ⨅ x, P.objective x := rfl
  rw [h, P.objective_eq_convexRestrict]
  rfl

end OrdinaryConvexProgram

/-- **Theorem 28.2** of [rockafellar1970convex]. Let $(P)$ be an ordinary convex program, and let
$I \subseteq \{1, \dots, r\}$ be a set of indices such that $f_i$ is affine for every $i \le r$
with $i \notin I$. Assume that the optimal value in $(P)$ is not $-\infty$, and that $(P)$ has a
feasible solution $x \in \operatorname{ri} C$ with $f_i(x) < 0$ for every $i \in I$. Then $(P)$
has a Kuhn–Tucker vector.

The set $I$ is a `Finset (Fin m)`. The book's condition on $I$ is split into two hypotheses: $I$
contains no index $i > r$, and each $f_i$ with $i \le r$ and $i \notin I$ is affine. The proof
replaces each equality constraint by two inequalities and applies
`ConvexAnalysis.exists_isKuhnTuckerVector_of_slater`. The multiplier of an equality constraint
is then the difference of the two multipliers, as in the reduction of the book. -/
theorem theorem_28_2 {I : Finset (Fin m)}
    (hIr : ∀ i : Fin m, P.r ≤ (i : ℕ) → i ∉ I)
    (hIaff : ∀ i : Fin m, (i : ℕ) < P.r → i ∉ I →
      ∃ a : Rn n →ᵃ[ℝ] ℝ, ∀ x, P.f i x = ((a x : ℝ) : EReal))
    (hbot : P.optimalValue ≠ ⊥)
    (hslater : ∃ x ∈ ri P.C, (∀ i ∈ I, P.f i x < 0) ∧ x ∈ P.constraintSet) :
    ∃ u : Rn m, P.IsKuhnTuckerVector u := by
  classical
  have hIlt : ∀ i : Fin m, i ∈ I → (i : ℕ) < P.r := fun i hi => by
    by_contra hc; exact hIr i (not_lt.1 hc) hi
  -- a total affine datum, with junk on `I`
  have haff : ∀ i : Fin m, ∃ a : Rn n →ᵃ[ℝ] ℝ, i ∉ I → ∀ x, P.f i x = ((a x : ℝ) : EReal) := by
    intro i
    by_cases hI : i ∈ I
    · exact ⟨AffineMap.const ℝ (Rn n) 0, fun hc => absurd hI hc⟩
    · rcases lt_or_ge (i : ℕ) P.r with hi | hi
      · obtain ⟨a, hax⟩ := hIaff i hi hI; exact ⟨a, fun _ => hax⟩
      · obtain ⟨a, hax⟩ := P.exists_affine i hi; exact ⟨a, fun _ => hax⟩
  choose a ha using haff
  -- the backbone's two families
  set g : {i : Fin m // i ∈ I} → Rn n → EReal := fun i => P.f i with hgdef
  set b : Fin m ⊕ Fin m → Rn n →ᵃ[ℝ] ℝ :=
    Sum.elim (fun i => if i ∈ I then 0 else a i)
      (fun i => if (i : ℕ) < P.r then 0 else -(a i)) with hbdef
  have hbl : ∀ (i : Fin m), i ∈ I → ∀ x, b (Sum.inl i) x = 0 := by
    intro i hi x; simp [hbdef, hi]
  have hbl' : ∀ (i : Fin m), i ∉ I → ∀ x, b (Sum.inl i) x = a i x := by
    intro i hi x; simp [hbdef, hi]
  have hbr : ∀ (i : Fin m), (i : ℕ) < P.r → ∀ x, b (Sum.inr i) x = 0 := by
    intro i hi x; simp [hbdef, hi]
  have hbr' : ∀ (i : Fin m), P.r ≤ (i : ℕ) → ∀ x, b (Sum.inr i) x = -(a i x) := by
    intro i hi x; simp [hbdef, not_lt.2 hi]
  -- the two descriptions of the feasible set agree
  have hfeas : ConvexAnalysis.feasibleSet g b = P.constraintSet := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · by_cases hI : i ∈ I
        · exact h1 ⟨i, hI⟩
        · have hb := h2 (Sum.inl i)
          rw [hbl' i hI x] at hb
          rw [ha i hI x]
          exact_mod_cast hb
      · have hI : i ∉ I := hIr i hi
        have h₁ := h2 (Sum.inl i)
        have h₂ := h2 (Sum.inr i)
        rw [hbl' i hI x] at h₁
        rw [hbr' i hi x] at h₂
        have hzero : a i x = 0 := by linarith
        rw [ha i hI x, hzero]
        rfl
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => h1 (i : Fin m) (hIlt i i.2), fun j => ?_⟩
      cases j with
      | inl i =>
        by_cases hI : i ∈ I
        · rw [hbl i hI x]
        · rw [hbl' i hI x]
          rcases lt_or_ge (i : ℕ) P.r with hi | hi
          · have hb := h1 i hi; rw [ha i hI x] at hb; exact_mod_cast hb
          · have hb := h2 i hi
            rw [ha i hI x] at hb
            have hz : a i x = 0 := by exact_mod_cast hb
            rw [hz]
      | inr i =>
        rcases lt_or_ge (i : ℕ) P.r with hi | hi
        · rw [hbr i hi x]
        · rw [hbr' i hi x]
          have hI : i ∉ I := hIr i hi
          have hb := h2 i hi
          rw [ha i hI x] at hb
          have hz : a i x = 0 := by exact_mod_cast hb
          rw [hz, neg_zero]
  have hoval : ConvexAnalysis.optimalValue P.f₀ g b = P.optimalValue := by
    have h : ConvexAnalysis.optimalValue P.f₀ g b
        = ⨅ x ∈ ConvexAnalysis.feasibleSet g b, P.f₀ x := rfl
    rw [h, hfeas, P.optimalValue_eq_biInf_constraintSet]
  obtain ⟨x₀, hx₀ri, hx₀I, hx₀C⟩ := hslater
  have hx₀feas : x₀ ∈ ConvexAnalysis.feasibleSet g b := by rw [hfeas]; exact hx₀C
  obtain ⟨l, μ, hkt⟩ := exists_isKuhnTuckerVector_of_slater (f₀ := P.f₀) (f := g) (b := b)
    P.convexFn_f₀ P.properConvex_f₀ (fun i => P.convexFn_f (i : Fin m) (hIlt i i.2))
    (fun i => P.properConvex_f (i : Fin m) (hIlt i i.2))
    (fun i => by rw [P.convexDom_f₀]; exact P.subset_convexDom_f (i : Fin m) (hIlt i i.2))
    (by rw [hoval]; exact hbot)
    ⟨x₀, by rw [P.convexDom_f₀]; exact hx₀ri, fun i => hx₀I (i : Fin m) i.2, hx₀feas.2⟩
  -- assemble the Kuhn–Tucker vector of `(P)`
  set uv : Fin m → ℝ := fun i =>
    if h : i ∈ I then l ⟨i, h⟩
    else if (i : ℕ) < P.r then μ (Sum.inl i) else μ (Sum.inl i) - μ (Sum.inr i) with huv
  have huvI : ∀ (i : Fin m) (h : i ∈ I), uv i = l ⟨i, h⟩ := fun i h => by simp [huv, h]
  have huvLt : ∀ i : Fin m, i ∉ I → (i : ℕ) < P.r → uv i = μ (Sum.inl i) := by
    intro i hI hi; simp [huv, hI, hi]
  have huvGe : ∀ i : Fin m, i ∉ I → P.r ≤ (i : ℕ) →
      uv i = μ (Sum.inl i) - μ (Sum.inr i) := by
    intro i hI hi; simp [huv, hI, not_lt.2 hi]
  have hnn : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ (WithLp.toLp 2 uv : Rn m) i := by
    intro i hi
    change 0 ≤ uv i
    by_cases hI : i ∈ I
    · rw [huvI i hI]; exact hkt.nonneg _
    · rw [huvLt i hI hi]; exact hkt.nonneg_affine _
  -- the two Lagrangians agree
  have hlag : P.lagrangeFn (WithLp.toLp 2 uv)
      = ConvexAnalysis.programLagrangian P.f₀ g b l μ := by
    funext x
    by_cases hxC : x ∈ P.C
    · obtain ⟨c₀, hc₀⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (P.properConvex_f₀.ne_bot x)
        (P.mem_C_iff.1 hxC)
      choose c hc using P.exists_coe_f hxC
      have hac : ∀ i : Fin m, i ∉ I → a i x = c i := by
        intro i hI
        have h := ha i hI x
        rw [hc i] at h
        exact_mod_cast h.symm
      have key : ∀ i : Fin m,
          (if i ∈ I then uv i * c i else 0) + (μ (Sum.inl i) * b (Sum.inl i) x
            + μ (Sum.inr i) * b (Sum.inr i) x) = uv i * c i := by
        intro i
        by_cases hI : i ∈ I
        · rw [hbl i hI x, hbr i (hIlt i hI) x]
          simp [hI]
        · rcases lt_or_ge (i : ℕ) P.r with hi | hi
          · rw [hbl' i hI x, hbr i hi x, hac i hI, huvLt i hI hi]
            simp [hI]
          · rw [hbl' i hI x, hbr' i hi x, hac i hI, huvGe i hI hi]
            simp [hI]
            ring
      have hA : ∑ i : Fin m, (if i ∈ I then uv i * c i else 0)
          = ∑ i : {i : Fin m // i ∈ I}, l i * c (i : Fin m) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter,
          ← Finset.sum_coe_sort I fun i => uv i * c i]
        exact Finset.sum_congr rfl fun i _ => by rw [huvI (i : Fin m) i.2]
      have hBC : (∑ j, μ j * b j x)
          = (∑ i : Fin m, μ (Sum.inl i) * b (Sum.inl i) x)
            + ∑ i : Fin m, μ (Sum.inr i) * b (Sum.inr i) x := Fintype.sum_sum_type _
      have hsplit : ∑ i : Fin m, uv i * c i
          = (∑ i : {i : Fin m // i ∈ I}, l i * c (i : Fin m)) + ∑ j, μ j * b j x :=
        calc ∑ i : Fin m, uv i * c i
            = ∑ i : Fin m, ((if i ∈ I then uv i * c i else 0)
                + (μ (Sum.inl i) * b (Sum.inl i) x
                  + μ (Sum.inr i) * b (Sum.inr i) x)) :=
              Finset.sum_congr rfl fun i _ => (key i).symm
          _ = (∑ i : Fin m, (if i ∈ I then uv i * c i else 0))
                + ∑ i : Fin m, (μ (Sum.inl i) * b (Sum.inl i) x
                  + μ (Sum.inr i) * b (Sum.inr i) x) := Finset.sum_add_distrib
          _ = (∑ i : {i : Fin m // i ∈ I}, l i * c (i : Fin m)) + ∑ j, μ j * b j x := by
              rw [hA, hBC, Finset.sum_add_distrib]
      rw [P.lagrangeFn_eq_coe hc₀ hc,
        programLagrangian_eq_coe (f := g) (b := b) (l := l) (μ := μ) hc₀
          (r := fun i : {i : Fin m // i ∈ I} => c (i : Fin m)) (fun i => hc (i : Fin m)),
        EReal.coe_eq_coe_iff, hsplit]
      ring
    · rw [P.lagrangeFn_eq_top_of_notMem_C hnn hxC,
        programLagrangian_eq_top (f := g) (b := b) (μ := μ) hkt.nonneg
          (fun i y => P.f_ne_bot (i : Fin m) y) (P.f₀_eq_top_of_notMem hxC)]
  exact ⟨WithLp.toLp 2 uv, hnn, by rw [hlag]; exact hkt.ne_bot, by rw [hlag]; exact hkt.ne_top,
    by rw [hlag, hkt.iInf_eq, hoval]⟩

/-- **Corollary 28.2.1** of [rockafellar1970convex]. Let $(P)$ be an ordinary convex program with
inequality constraints only ($r = m$). If the optimal value in $(P)$ is not $-\infty$ and some
$x \in C$ satisfies $f_1(x) < 0, \dots, f_m(x) < 0$, then $(P)$ has a Kuhn–Tucker vector.

Here the point $x$ need not lie in $\operatorname{ri} C$. The corollary is a special case of
Theorem 28.2 and does not replace it, because it needs $r = m$ and a point that satisfies every
constraint strictly. -/
theorem corollary_28_2_1 (hrm : P.r = m) (hbot : P.optimalValue ≠ ⊥)
    (hslater : ∃ x ∈ P.C, ∀ i : Fin m, P.f i x < 0) :
    ∃ u : Rn m, P.IsKuhnTuckerVector u := by
  have hlt : ∀ i : Fin m, (i : ℕ) < P.r := fun i => by rw [hrm]; exact i.isLt
  set b : Empty → Rn n →ᵃ[ℝ] ℝ := fun j => j.elim with hbdef
  have hfeas : ConvexAnalysis.feasibleSet P.f b = P.constraintSet := by
    ext x
    exact ⟨fun h => ⟨fun i _ => h.1 i, fun i hi => absurd (hlt i) (not_lt.2 hi)⟩,
      fun h => ⟨fun i => h.1 i (hlt i), fun j => j.elim⟩⟩
  have hoval : ConvexAnalysis.optimalValue P.f₀ P.f b = P.optimalValue := by
    have h : ConvexAnalysis.optimalValue P.f₀ P.f b
        = ⨅ x ∈ ConvexAnalysis.feasibleSet P.f b, P.f₀ x := rfl
    rw [h, hfeas, P.optimalValue_eq_biInf_constraintSet]
  obtain ⟨x₀, hx₀C, hx₀⟩ := hslater
  obtain ⟨l, μ, hkt⟩ := exists_isKuhnTuckerVector_of_mem_convexDom (f₀ := P.f₀) (f := P.f) (b := b)
    P.convexFn_f₀ P.properConvex_f₀ (fun i => P.convexFn_f i (hlt i))
        (fun i => P.properConvex_f i (hlt i))
    (fun i => by rw [P.convexDom_f₀]; exact P.subset_convexDom_f i (hlt i))
    (fun i => by rw [P.convexDom_f₀]; exact P.relint_subset i (hlt i))
    (by rw [hoval]; exact hbot)
    ⟨x₀, by rw [P.convexDom_f₀]; exact hx₀C, hx₀, fun j => j.elim⟩
  have hlag : P.lagrangeFn (WithLp.toLp 2 l)
      = ConvexAnalysis.programLagrangian P.f₀ P.f b l μ := by
    funext x
    rw [OrdinaryConvexProgram.lagrangeFn_apply, programLagrangian_apply]
    simp
  exact ⟨WithLp.toLp 2 l, fun i _ => hkt.nonneg i, by rw [hlag]; exact hkt.ne_bot,
    by rw [hlag]; exact hkt.ne_top, by rw [hlag, hkt.iInf_eq, hoval]⟩

/-- The affine function $x \mapsto \langle a, x \rangle - \alpha$ on $\mathbb{R}^n$, for
$a \in \mathbb{R}^n$ and $\alpha \in \mathbb{R}$. This is the form of a linear constraint in
Corollary 28.2.2. -/
noncomputable def linConstraint (v : Rn n) (α : ℝ) : Rn n →ᵃ[ℝ] ℝ :=
  (linFn v).toLinearMap.toAffineMap - AffineMap.const ℝ (Rn n) α

/-- The value of the linear constraint function: $\langle a, x \rangle - \alpha$. -/
@[simp] theorem linConstraint_apply (v : Rn n) (α : ℝ) (x : Rn n) :
    linConstraint v α x = pairing n x v - α := by
  simp only [linConstraint, AffineMap.coe_sub, Pi.sub_apply, AffineMap.const_apply,
    LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe, linFn_apply]

/-- **Corollary 28.2.2** of [rockafellar1970convex]. Let $(P)$ be an ordinary convex program whose
constraint functions are all linear: $f_i(x) = \langle a_i, x \rangle - \alpha_i$ for
$i = 1, \dots, m$. If the optimal value in $(P)$ is not $-\infty$ and $(P)$ has a feasible
solution in $\operatorname{ri} C$, then $(P)$ has a Kuhn–Tucker vector.

The book prints no proof. The corollary is Theorem 28.2 with $I = \emptyset$: no constraint is
non-affine, so no constraint has to hold strictly. -/
theorem corollary_28_2_2
    (hlin : ∀ i : Fin m, ∃ (v : Rn n) (α : ℝ), ∀ x, P.f i x = ((pairing n x v - α : ℝ) : EReal))
    (hbot : P.optimalValue ≠ ⊥) (hfeas : ∃ x ∈ ri P.C, x ∈ P.constraintSet) :
    ∃ u : Rn m, P.IsKuhnTuckerVector u := by
  obtain ⟨x₀, hx₀ri, hx₀C⟩ := hfeas
  refine theorem_28_2 P (I := ∅) (fun i _ => Finset.notMem_empty i)
    (fun i _ _ => ?_) hbot ⟨x₀, hx₀ri, fun i hi => absurd hi (Finset.notMem_empty i), hx₀C⟩
  obtain ⟨v, α, hv⟩ := hlin i
  exact ⟨linConstraint v α, fun x => by rw [hv x, linConstraint_apply]⟩

/-! ### The Lagrangian of an ordinary convex program -/

namespace OrdinaryConvexProgram

/-- **Section 28** of [rockafellar1970convex], the cone of multiplier vectors. It is
$$E_r = \{u^* = (v_1^*, \dots, v_m^*) \in \mathbb{R}^m \mid v_i^* \ge 0 \text{ for } i = 1,
  \dots, r\}.$$
The number $v_i^*$ is the **Lagrange multiplier** associated with the $i$-th constraint of
$(P)$. -/
def multiplierCone : Set (Rn m) := {u | ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i}

/-- A vector $u^*$ lies in $E_r$ if and only if $v_i^* \ge 0$ for $i = 1, \dots, r$. -/
@[simp] theorem mem_multiplierCone {u : Rn m} :
    u ∈ P.multiplierCone ↔ ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i := Iff.rfl

/-- The zero vector lies in $E_r$. -/
theorem zero_mem_multiplierCone : (0 : Rn m) ∈ P.multiplierCone := by intro i _; simp

/-- **Section 28** of [rockafellar1970convex], the unit vectors. For $i = 1, \dots, m$,
$e_i \in \mathbb{R}^m$ is the $i$-th row of the $m \times m$ identity matrix: its $i$-th
coordinate is $1$ and its other coordinates are $0$. -/
noncomputable def unitVec (m : ℕ) (i : Fin m) : Rn m := EuclideanSpace.single i (1 : ℝ)

/-- The $j$-th coordinate of $e_i$ is $1$ if $j = i$ and $0$ otherwise. -/
@[simp] theorem unitVec_apply (m : ℕ) (i j : Fin m) :
    unitVec m i j = if j = i then (1 : ℝ) else 0 := by
  simp [unitVec]

/-- Every unit vector $e_i$ lies in $E_r$. -/
theorem unitVec_mem_multiplierCone (i : Fin m) : unitVec m i ∈ P.multiplierCone := by
  intro j _
  rw [unitVec_apply]
  by_cases h : j = i <;> simp [h]

/-- The objective $f_0$ is finite on $C$: for $x \in C$, $f_0(x)$ is a real number. -/
theorem exists_coe_f₀ {x : Rn n} (hx : x ∈ P.C) : ∃ c : ℝ, P.f₀ x = (c : EReal) :=
  EReal.exists_coe_of_ne_bot_of_lt_top (P.properConvex_f₀.ne_bot x) (P.mem_C_iff.1 hx)

/-- For every $\lambda \in \mathbb{R}^m$, the function $h = f_0 + \lambda_1 f_1 + \dots + \lambda_m
f_m$ is finite at every point of $C$. -/
theorem exists_coe_lagrangeFn (u : Rn m) {x : Rn n} (hx : x ∈ P.C) :
    ∃ c : ℝ, P.lagrangeFn u x = (c : EReal) := by
  obtain ⟨c₀, h₀⟩ := P.exists_coe_f₀ hx
  choose c hc using P.exists_coe_f hx
  exact ⟨c₀ + ∑ i, u i * c i, P.lagrangeFn_eq_coe h₀ hc⟩

/-- At $\lambda = 0$, $h = f_0$. -/
@[simp] theorem lagrangeFn_zero (x : Rn n) : P.lagrangeFn 0 x = P.f₀ x := by
  refine P.lagrangeFn_eq_f₀ fun i => ?_
  have h : (((0 : Rn m) i : ℝ) : EReal) = 0 := by simp
  rw [h, zero_mul]

/-- At $\lambda = e_i$, $h = f_0 + f_i$. -/
theorem lagrangeFn_unitVec (i : Fin m) (x : Rn n) :
    P.lagrangeFn (unitVec m i) x = P.f₀ x + P.f i x := by
  rw [lagrangeFn_apply]
  congr 1
  have hsum : (∑ j, ((unitVec m i j : ℝ) : EReal) * P.f j x)
      = ((unitVec m i i : ℝ) : EReal) * P.f i x := by
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun hj => absurd (Finset.mem_univ i) hj)
    have h : ((unitVec m i j : ℝ) : EReal) = 0 := by rw [unitVec_apply]; simp [hj]
    rw [h, zero_mul]
  rw [hsum]
  have h1 : ((unitVec m i i : ℝ) : EReal) = 1 := by rw [unitVec_apply]; simp
  rw [h1, one_mul]

/-- **Section 28** of [rockafellar1970convex], definition of the Lagrangian. The **Lagrangian** of
$(P)$ is the function $L$ on $\mathbb{R}^m \times \mathbb{R}^n$ given by
$$L(u^*, x) = \begin{cases} f_0(x) + v_1^* f_1(x) + \dots + v_m^* f_m(x) & \text{if } u^* \in
  E_r \text{ and } x \in C, \\ -\infty & \text{if } u^* \notin E_r \text{ and } x \in C, \\
  +\infty & \text{if } x \notin C. \end{cases}$$

The Lean term is `⨅ _ : x ∈ P.C, ⨆ _ : u ∈ P.multiplierCone, P.lagrangeFn u x`, which needs no
decidability: an infimum over an empty index type is $+\infty$, and a supremum over an empty
index type is $-\infty$. The value in the first case is
`Rockafellar.OrdinaryConvexProgram.lagrangeFn` at $u^*$. -/
noncomputable def programLagrangian (u : Rn m) (x : Rn n) : EReal :=
  ⨅ _ : x ∈ P.C, ⨆ _ : u ∈ P.multiplierCone, P.lagrangeFn u x

/-- For $x \in C$ and $u^* \in E_r$, $L(u^*, x) = h(x)$, where
$h = f_0 + v_1^* f_1 + \dots + v_m^* f_m$. -/
theorem programLagrangian_eq_lagrangeFn {u : Rn m} {x : Rn n} (hx : x ∈ P.C)
    (hu : u ∈ P.multiplierCone) : P.programLagrangian u x = P.lagrangeFn u x := by
  rw [programLagrangian, iInf_pos hx, iSup_pos hu]

/-- For $x \in C$ and $u^* \notin E_r$, $L(u^*, x) = -\infty$. -/
theorem programLagrangian_eq_bot {u : Rn m} {x : Rn n} (hx : x ∈ P.C)
    (hu : u ∉ P.multiplierCone) : P.programLagrangian u x = ⊥ := by
  rw [programLagrangian, iInf_pos hx, iSup_neg hu]

/-- For $x \notin C$, $L(u^*, x) = +\infty$ for every $u^*$. -/
theorem programLagrangian_eq_top {x : Rn n} (hx : x ∉ P.C) (u : Rn m) :
    P.programLagrangian u x = ⊤ := by
  rw [programLagrangian, iInf_neg hx]

/-- The Lagrangian $L$ of $(P)$ as a function $K(u^*, x)$ of one argument in
$\mathbb{R}^m \times \mathbb{R}^n$. This is the form of the minimax theory of Section 36 and of
`ConvexAnalysis.IsSaddlePoint`, `ConvexAnalysis.maximin` and `ConvexAnalysis.minimax`. -/
noncomputable def saddleFn : Rn m × Rn n → EReal := fun q => P.programLagrangian q.1 q.2

/-- The defining formula $K(u^*, x) = L(u^*, x)$. -/
theorem saddleFn_apply (q : Rn m × Rn n) : P.saddleFn q = P.programLagrangian q.1 q.2 := rfl

/-!
### The program is recovered from its Lagrangian

The book states that "$L$ reflects all the structure of $(P)$, because the $(m + 3)$-tuple
$(C, f_0, \dots, f_m, r)$ can be recovered completely from $L$". This is stated here as three
theorems and one consequence.
-/

/-- A point $x$ lies in $C$ if and only if $L(0, x) \neq +\infty$. -/
theorem mem_C_iff_programLagrangian_ne_top {x : Rn n} :
    x ∈ P.C ↔ P.programLagrangian 0 x ≠ ⊤ := by
  constructor
  · intro hx
    rw [P.programLagrangian_eq_lagrangeFn hx P.zero_mem_multiplierCone, P.lagrangeFn_zero]
    exact (P.mem_C_iff.1 hx).ne
  · intro hne
    by_contra hx
    exact hne (P.programLagrangian_eq_top hx 0)

/-- For $x \in C$, a vector $u^*$ lies in $E_r$ if and only if $L(u^*, x) \neq -\infty$. -/
theorem mem_multiplierCone_iff_programLagrangian_ne_bot {u : Rn m} {x : Rn n} (hx : x ∈ P.C) :
    u ∈ P.multiplierCone ↔ P.programLagrangian u x ≠ ⊥ := by
  constructor
  · intro hu
    obtain ⟨c, hc⟩ := P.exists_coe_lagrangeFn u hx
    rw [P.programLagrangian_eq_lagrangeFn hx hu, hc]
    exact EReal.coe_ne_bot c
  · intro hne
    by_contra hu
    exact hne (P.programLagrangian_eq_bot hx hu)

/-- **Section 28** of [rockafellar1970convex]: "the set of points where $L$ is finite is
$E_r \times C$". -/
theorem setOf_programLagrangian_finite :
    {q : Rn m × Rn n | P.programLagrangian q.1 q.2 ≠ ⊥ ∧ P.programLagrangian q.1 q.2 ≠ ⊤}
      = P.multiplierCone ×ˢ P.C := by
  ext q
  rw [Set.mem_ofPred_eq, Set.mem_prod]
  constructor
  · rintro ⟨hb, ht⟩
    have hC : q.2 ∈ P.C := by
      by_contra hc
      exact ht (P.programLagrangian_eq_top hc q.1)
    exact ⟨(P.mem_multiplierCone_iff_programLagrangian_ne_bot hC).2 hb, hC⟩
  · rintro ⟨hu, hC⟩
    obtain ⟨c, hc⟩ := P.exists_coe_lagrangeFn q.1 hC
    rw [P.programLagrangian_eq_lagrangeFn hC hu, hc]
    exact ⟨EReal.coe_ne_bot c, EReal.coe_ne_top c⟩

/-- **Section 28** of [rockafellar1970convex]: $f_0(x) = L(0, x)$ for $x \in C$. -/
theorem f₀_eq_programLagrangian {x : Rn n} (hx : x ∈ P.C) : P.f₀ x = P.programLagrangian 0 x := by
  rw [P.programLagrangian_eq_lagrangeFn hx P.zero_mem_multiplierCone, P.lagrangeFn_zero]

/-- **Section 28** of [rockafellar1970convex]: $f_i(x) = L(e_i, x) - L(0, x)$ for $x \in C$ and
$i = 1, \dots, m$. -/
theorem f_eq_programLagrangian_sub {x : Rn n} (hx : x ∈ P.C) (i : Fin m) :
    P.f i x = P.programLagrangian (unitVec m i) x - P.programLagrangian 0 x := by
  obtain ⟨c₀, h₀⟩ := P.exists_coe_f₀ hx
  obtain ⟨c, hc⟩ := P.exists_coe_f hx i
  rw [P.programLagrangian_eq_lagrangeFn hx (P.unitVec_mem_multiplierCone i),
    P.programLagrangian_eq_lagrangeFn hx P.zero_mem_multiplierCone, P.lagrangeFn_zero,
    P.lagrangeFn_unitVec, h₀, hc, ← EReal.coe_add, ← EReal.coe_sub]
  norm_num

private theorem r_le_of_multiplierCone_subset {P₁ P₂ : OrdinaryConvexProgram n m}
    (h : P₁.multiplierCone ⊆ P₂.multiplierCone) : P₂.r ≤ P₁.r := by
  by_contra hlt
  have hc : P₁.r < P₂.r := by omega
  have him : P₁.r < m := lt_of_lt_of_le hc P₂.r_le
  set i : Fin m := ⟨P₁.r, him⟩ with hi
  have hmem : -unitVec m i ∈ P₁.multiplierCone := by
    intro j hj
    have hne : j ≠ i := by
      rintro rfl
      exact absurd hj (by rw [hi]; exact lt_irrefl _)
    have hval : (-unitVec m i) j = -(unitVec m i j) := rfl
    rw [hval, unitVec_apply]
    simp [hne]
  have hneg := h hmem i (by rw [hi]; exact hc)
  have hval : (-unitVec m i) i = -(unitVec m i i) := rfl
  rw [hval, unitVec_apply] at hneg
  norm_num at hneg

/-- Two ordinary convex programs with the same cone $E_r$ have the same number $r$ of inequality
constraints. So $L$ determines $r$, because it determines $E_r$. -/
theorem r_eq_of_multiplierCone_eq {P₁ P₂ : OrdinaryConvexProgram n m}
    (h : P₁.multiplierCone = P₂.multiplierCone) : P₁.r = P₂.r :=
  le_antisymm (r_le_of_multiplierCone_subset h.symm.subset)
    (r_le_of_multiplierCone_subset h.subset)

/-- **Section 28** of [rockafellar1970convex]: "There is thus a one-to-one correspondence between
ordinary convex programs and their Lagrangians." If two ordinary convex programs with $n$
variables and $m$ constraints have the same Lagrangian, then they have the same set $C$ and the
same number $r$, and their functions $f_0, f_1, \dots, f_m$ agree on $C$.

The values of $f_i$ off $C$ do not matter for $(P)$, so this is all the data of the tuple. -/
theorem eq_of_programLagrangian_eq {P₁ P₂ : OrdinaryConvexProgram n m}
    (h : P₁.programLagrangian = P₂.programLagrangian) :
    P₁.C = P₂.C ∧ P₁.r = P₂.r ∧ (∀ x ∈ P₁.C, P₁.f₀ x = P₂.f₀ x) ∧
      ∀ x ∈ P₁.C, ∀ i : Fin m, P₁.f i x = P₂.f i x := by
  have hC : P₁.C = P₂.C := by
    ext x
    rw [P₁.mem_C_iff_programLagrangian_ne_top, P₂.mem_C_iff_programLagrangian_ne_top,
      show P₁.programLagrangian 0 x = P₂.programLagrangian 0 x from by rw [h]]
  obtain ⟨x₀, hx₀⟩ := P₁.nonempty_C
  have hcone : P₁.multiplierCone = P₂.multiplierCone := by
    ext u
    rw [P₁.mem_multiplierCone_iff_programLagrangian_ne_bot hx₀,
      P₂.mem_multiplierCone_iff_programLagrangian_ne_bot (hC ▸ hx₀),
      show P₁.programLagrangian u x₀ = P₂.programLagrangian u x₀ from by rw [h]]
  refine ⟨hC, r_eq_of_multiplierCone_eq hcone, fun x hx => ?_, fun x hx i => ?_⟩
  · rw [P₁.f₀_eq_programLagrangian hx, P₂.f₀_eq_programLagrangian (hC ▸ hx), h]
  · rw [P₁.f_eq_programLagrangian_sub hx i, P₂.f_eq_programLagrangian_sub (hC ▸ hx) i, h]

end OrdinaryConvexProgram

/-!
### The Lagrangian of $(P)$ is the Lagrangian of its bifunction

The book's formula $L(u^*, x) = \inf \{f_0(x) + v_1^* v_1 + \dots + v_m^* v_m \mid u \in U_x\}$ is
the definition of Section 29 of the Lagrangian of the bifunction of $(P)$. So
`Rockafellar.OrdinaryConvexProgram.programLagrangian` agrees with the backbone's
`ConvexAnalysis.lagrangian`, and everything that Section 29 proves about the latter applies.
-/

namespace OrdinaryConvexProgram

private theorem pairing_unitVec {k : ℕ} (i : Fin k) (u : Rn k) :
    pairing k (unitVec k i) u = u i := by
  rw [pairing_eq_sum]
  refine (Finset.sum_eq_single i (fun j _ hj => ?_)
    (fun hj => absurd (Finset.mem_univ i) hj)).trans ?_
  · rw [unitVec_apply]; simp [hj]
  · rw [unitVec_apply]; simp

/-- **Section 28** of [rockafellar1970convex]: the Lagrangian $L$ of $(P)$ is the Lagrangian of the
bifunction $F$ of $(P)$ in the sense of Section 29, $L(u^*, x) = \inf_u \{\langle u, u^*
\rangle + F(u, x)\}$, with the Euclidean inner product on $\mathbb{R}^m$. -/
theorem lagrangian_ineqBifun :
    ConvexAnalysis.lagrangian (pairing m) P.ineqBifun = P.programLagrangian := by
  funext u x
  rw [lagrangian_apply]
  by_cases hx : x ∈ P.C
  · obtain ⟨c₀, h₀⟩ := P.exists_coe_f₀ hx
    choose c hc using P.exists_coe_f hx
    set cVec : Rn m := WithLp.toLp 2 c with hcVec
    have hcApp : ∀ i, cVec i = c i := fun _ => rfl
    have hcMem : ∀ w : Rn m, (∀ i : Fin m, (i : ℕ) < P.r → c i ≤ w i) →
        (∀ i : Fin m, P.r ≤ (i : ℕ) → c i = w i) →
        (∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ ((w i : ℝ) : EReal)) ∧
          ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = ((w i : ℝ) : EReal) :=
      fun w h1 h2 => ⟨fun i hi => by rw [hc i]; exact_mod_cast h1 i hi,
        fun i hi => by rw [hc i]; exact_mod_cast h2 i hi⟩
    by_cases hu : u ∈ P.multiplierCone
    · rw [P.programLagrangian_eq_lagrangeFn hx hu, P.lagrangeFn_eq_coe h₀ hc]
      refine le_antisymm ?_ (le_iInf fun w => ?_)
      · refine le_trans (iInf_le _ cVec) (le_of_eq ?_)
        rw [P.ineqBifun_of_mem (hcMem cVec (fun i _ => le_of_eq (hcApp i).symm)
          (fun i _ => (hcApp i).symm)), h₀, pairing_eq_sum, ← EReal.coe_add]
        congr 1
        rw [add_comm]
        exact congrArg (fun t => c₀ + t)
          (Finset.sum_congr rfl fun i _ => by rw [hcApp i]; ring)
      · by_cases hw : (∀ i : Fin m, (i : ℕ) < P.r → P.f i x ≤ ((w i : ℝ) : EReal)) ∧
            ∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = ((w i : ℝ) : EReal)
        · rw [P.ineqBifun_of_mem hw, h₀, pairing_eq_sum, ← EReal.coe_add,
            EReal.coe_le_coe_iff]
          have hle : ∑ i, u i * c i ≤ ∑ i, w i * u i := by
            refine Finset.sum_le_sum fun i _ => ?_
            rcases lt_or_ge (i : ℕ) P.r with hi | hi
            · have h1 : c i ≤ w i := by
                have := hw.1 i hi; rw [hc i] at this; exact_mod_cast this
              rw [mul_comm (w i)]
              exact mul_le_mul_of_nonneg_left h1 (hu i hi)
            · have h1 : c i = w i := by
                have := hw.2 i hi; rw [hc i] at this; exact_mod_cast this
              rw [h1, mul_comm]
          linarith
        · rw [P.ineqBifun_of_notMem hw, EReal.coe_add_top]
          exact le_top
    · rw [P.programLagrangian_eq_bot hx hu]
      obtain ⟨i₀, hi₀r, hi₀neg⟩ : ∃ i : Fin m, (i : ℕ) < P.r ∧ u i < 0 := by
        by_contra hcon
        exact hu fun i hi => by
          by_contra hlt
          exact hcon ⟨i, hi, not_le.1 hlt⟩
      have hkey : ∀ β : ℝ, ∃ w : Rn m,
          ((pairing m w u : ℝ) : EReal) + P.ineqBifun w x < ((β : ℝ) : EReal) := by
        intro β
        set S : ℝ := ∑ i, c i * u i with hS
        set K : ℝ := (β - S - c₀) / u i₀ with hK
        set t : ℝ := max 0 (K + 1) with hT
        have ht0 : 0 ≤ t := le_max_left _ _
        have htK : K < t := lt_of_lt_of_le (lt_add_one K) (le_max_right _ _)
        refine ⟨cVec + t • unitVec m i₀, ?_⟩
        have hwApp : ∀ i : Fin m, (cVec + t • unitVec m i₀ : Rn m) i
            = c i + t * unitVec m i₀ i := fun _ => rfl
        have hmem1 : ∀ i : Fin m, (i : ℕ) < P.r → c i ≤ (cVec + t • unitVec m i₀ : Rn m) i := by
          intro i _
          rw [hwApp i]
          have hnn : (0 : ℝ) ≤ t * unitVec m i₀ i := by
            rw [unitVec_apply]
            by_cases h : i = i₀ <;> simp [h, ht0]
          linarith
        have hmem2 : ∀ i : Fin m, P.r ≤ (i : ℕ) → c i = (cVec + t • unitVec m i₀ : Rn m) i := by
          intro i hi
          rw [hwApp i]
          have hne : i ≠ i₀ := fun hie => absurd (hie ▸ hi₀r) (by omega)
          rw [unitVec_apply]
          simp [hne]
        rw [P.ineqBifun_of_mem (hcMem _ hmem1 hmem2), h₀]
        have hp : pairing m (cVec + t • unitVec m i₀) u = S + t * u i₀ := by
          rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
            pairing_unitVec, pairing_eq_sum]
        rw [hp, ← EReal.coe_add, EReal.coe_lt_coe_iff]
        have hmul : t * u i₀ < K * u i₀ := mul_lt_mul_of_neg_right htK hi₀neg
        have hKu : K * u i₀ = β - S - c₀ := div_mul_cancel₀ _ (ne_of_lt hi₀neg)
        linarith
      refine iInf_eq_bot.2 fun b hb => ?_
      induction b using EReal.rec with
      | bot => exact absurd hb (lt_irrefl _)
      | coe β => obtain ⟨w, hw⟩ := hkey β; exact ⟨w, hw⟩
      | top =>
        obtain ⟨w, hw⟩ := hkey 0
        exact ⟨w, lt_trans hw (EReal.coe_lt_top 0)⟩
  · rw [P.programLagrangian_eq_top hx u]
    refine le_antisymm le_top (le_iInf fun w => ?_)
    rw [P.ineqBifun_eq_top_of_notMem_C hx w, EReal.coe_add_top]

/-- The Lagrangian of the bifunction of $(P)$ in the sense of Section 29, as a function on
$\mathbb{R}^m \times \mathbb{R}^n$, is $(u^*, x) \mapsto L(u^*, x)$. -/
theorem saddleLagrangian_ineqBifun :
    ConvexAnalysis.saddleLagrangian (pairing m) P.ineqBifun
      = fun q : Rn m × Rn n => P.programLagrangian q.1 q.2 := by
  funext q
  rw [saddleLagrangian_apply, show ConvexAnalysis.lagrangian (pairing m) P.ineqBifun q.1 q.2
    = P.programLagrangian q.1 q.2 from by rw [P.lagrangian_ineqBifun]]

/-- **Section 28** of [rockafellar1970convex]: "$L$ is concave in $u^*$ for each $x$". This follows
from Section 29: the Lagrangian of a bifunction is a concave conjugate in the variable $u^*$. -/
theorem concaveFn_programLagrangian (x : Rn n) :
    ConcaveFn fun u : Rn m => P.programLagrangian u x := by
  rw [show (fun u : Rn m => P.programLagrangian u x)
    = fun u : Rn m => ConvexAnalysis.lagrangian (pairing m) P.ineqBifun u x from
      funext fun u => by rw [P.lagrangian_ineqBifun]]
  exact concaveFn_lagrangian (pairing m) P.ineqBifun x

end OrdinaryConvexProgram

/-! ### Theorem 28.3: saddle-points of the Lagrangian and the Kuhn–Tucker conditions -/

/-- The set of indices $i$ with $\lambda_i \neq 0$, for $\lambda \in \mathbb{R}^m$. It encodes the
parenthesis "(Omit terms with $\lambda_i = 0$.)" in condition (c) of Theorem 28.3 of
[rockafellar1970convex].

The omission matters: $\partial f_i(\bar x)$ can be empty at a boundary point of
$\operatorname{dom} f_i$, and then $0 \cdot \partial f_i(\bar x)$ is empty, not $\{0\}$. -/
noncomputable def activeIndices {m : ℕ} (u : Rn m) : Finset (Fin m) :=
  @Finset.filter _ (fun i => u i ≠ 0) (Classical.decPred _) Finset.univ

/-- An index $i$ lies in the set of active indices if and only if $\lambda_i \neq 0$. -/
theorem mem_activeIndices {m : ℕ} {u : Rn m} {i : Fin m} :
    i ∈ activeIndices u ↔ u i ≠ 0 := by
  simp [activeIndices]

namespace OrdinaryConvexProgram

/-- **Section 28** of [rockafellar1970convex]: $\sup_{u^*} L(u^*, x) = f_0(x) + \delta(x \mid C_0)$
for every $x \in \mathbb{R}^n$. That is, the supremum of the Lagrangian over
$u^* \in \mathbb{R}^m$ is the objective function of $(P)$. -/
theorem iSup_programLagrangian (x : Rn n) :
    (⨆ u : Rn m, P.programLagrangian u x) = P.objective x := by
  by_cases hC : x ∈ P.C
  · by_cases hF : x ∈ P.feasibleSet
    · rw [P.objective_of_mem hF]
      refine le_antisymm (iSup_le fun u => ?_) ?_
      · by_cases hu : u ∈ P.multiplierCone
        · rw [P.programLagrangian_eq_lagrangeFn hC hu]
          exact P.lagrangeFn_le_f₀ hu hF
        · rw [P.programLagrangian_eq_bot hC hu]
          exact bot_le
      · refine le_trans (le_of_eq ?_) (le_iSup (fun u => P.programLagrangian u x) (0 : Rn m))
        rw [P.programLagrangian_eq_lagrangeFn hC P.zero_mem_multiplierCone, P.lagrangeFn_zero]
    · rw [P.objective_of_notMem hF]
      obtain ⟨c₀, h₀⟩ := P.exists_coe_f₀ hC
      choose c hc using P.exists_coe_f hC
      have hmemA : ∀ (i : Fin m) (t s : ℝ), 0 ≤ t → 0 ≤ s →
          (t * s) • unitVec m i ∈ P.multiplierCone := by
        intro i t s ht hs j _
        have hval : ((t * s) • unitVec m i : Rn m) j = (t * s) * unitVec m i j := rfl
        rw [hval, unitVec_apply]
        by_cases h : j = i <;> simp [h, mul_nonneg ht hs]
      have hmemB : ∀ i : Fin m, P.r ≤ (i : ℕ) → ∀ t s : ℝ,
          (t * s) • unitVec m i ∈ P.multiplierCone := by
        intro i hi t s j hj
        have hval : ((t * s) • unitVec m i : Rn m) j = (t * s) * unitVec m i j := rfl
        have hne : j ≠ i := fun hje => absurd (hje ▸ hj) (by omega)
        rw [hval, unitVec_apply]
        simp [hne]
      obtain ⟨i, s, hsmem, hspos⟩ : ∃ (i : Fin m) (s : ℝ),
          (∀ t : ℝ, 0 ≤ t → (t * s) • unitVec m i ∈ P.multiplierCone) ∧ 0 < s * c i := by
        by_contra hcon
        refine hF ⟨hC, fun i hi => ?_, fun i hi => ?_⟩
        · rw [hc i]
          have hle : c i ≤ 0 := by
            by_contra hpos
            exact hcon ⟨i, 1, fun t ht => hmemA i t 1 ht zero_le_one,
              by rw [one_mul]; exact not_le.1 hpos⟩
          exact_mod_cast hle
        · rw [hc i]
          have heq : c i = 0 := by
            by_contra hne
            rcases lt_or_gt_of_ne hne with hneg | hpos
            · exact hcon ⟨i, -1, fun t _ => hmemB i hi t (-1), by nlinarith⟩
            · exact hcon ⟨i, 1, fun t _ => hmemB i hi t 1, by nlinarith⟩
          rw [heq]
          norm_num
      refine iSup_eq_top.2 fun b hb => ?_
      induction b using EReal.rec with
      | bot =>
        refine ⟨0, ?_⟩
        rw [P.programLagrangian_eq_lagrangeFn hC P.zero_mem_multiplierCone, P.lagrangeFn_zero, h₀]
        exact EReal.bot_lt_coe c₀
      | coe β =>
        set K : ℝ := (β - c₀) / (s * c i) with hK
        set t : ℝ := max 0 (K + 1) with hT
        refine ⟨(t * s) • unitVec m i, ?_⟩
        rw [P.programLagrangian_eq_lagrangeFn hC (hsmem t (le_max_left _ _)),
          P.lagrangeFn_eq_coe h₀ hc, EReal.coe_lt_coe_iff]
        have hsum : (∑ j, ((t * s) • unitVec m i : Rn m) j * c j) = (t * s) * c i := by
          have h1 : (∑ j, ((t * s) • unitVec m i : Rn m) j * c j)
              = ((t * s) • unitVec m i : Rn m) i * c i := by
            refine Finset.sum_eq_single i (fun j _ hj => ?_)
              (fun hj => absurd (Finset.mem_univ i) hj)
            have hval : ((t * s) • unitVec m i : Rn m) j = (t * s) * unitVec m i j := rfl
            rw [hval, unitVec_apply]
            simp [hj]
          rw [h1]
          have hval : ((t * s) • unitVec m i : Rn m) i = (t * s) * unitVec m i i := rfl
          rw [hval, unitVec_apply]
          simp
        rw [hsum]
        have hKu : K * (s * c i) = β - c₀ := div_mul_cancel₀ _ (ne_of_gt hspos)
        have htK : K + 1 ≤ t := le_max_right _ _
        have hmono : (K + 1) * (s * c i) ≤ t * (s * c i) :=
          mul_le_mul_of_nonneg_right htK (le_of_lt hspos)
        nlinarith
      | top => exact absurd hb (lt_irrefl _)
  · rw [P.objective_of_notMem fun hc => hC hc.1]
    refine le_antisymm le_top (le_trans (le_of_eq (P.programLagrangian_eq_top hC 0).symm)
      (le_iSup (fun u => P.programLagrangian u x) (0 : Rn m)))

/-- **Section 28** of [rockafellar1970convex], the case $\bar u^* \in E_r$: the infimum of
$L(\bar u^*, \cdot)$ over $\mathbb{R}^n$ is the infimum of $h = f_0 + \bar v_1^* f_1 + \dots +
\bar v_m^* f_m$. -/
theorem iInf_programLagrangian_of_mem {u : Rn m} (hu : u ∈ P.multiplierCone) :
    (⨅ x, P.programLagrangian u x) = ⨅ x, P.lagrangeFn u x := by
  refine iInf_congr fun x => ?_
  by_cases hC : x ∈ P.C
  · exact P.programLagrangian_eq_lagrangeFn hC hu
  · rw [P.programLagrangian_eq_top hC u, P.lagrangeFn_eq_top_of_notMem_C hu hC]

/-- **Section 28** of [rockafellar1970convex], the case $\bar u^* \notin E_r$: the infimum of
$L(\bar u^*, \cdot)$ over $\mathbb{R}^n$ is $-\infty$. -/
theorem iInf_programLagrangian_of_notMem {u : Rn m} (hu : u ∉ P.multiplierCone) :
    (⨅ x, P.programLagrangian u x) = ⊥ := by
  obtain ⟨x₀, hx₀⟩ := P.nonempty_C
  exact le_bot_iff.1 ((iInf_le (fun x => P.programLagrangian u x) x₀).trans
    (le_of_eq (P.programLagrangian_eq_bot hx₀ hu)))

/-- For every $\lambda \in \mathbb{R}^m$, the infimum of $h$ over $\mathbb{R}^n$ is not $+\infty$,
because $h$ is finite on the nonempty set $C$. -/
theorem iInf_lagrangeFn_ne_top (u : Rn m) : (⨅ z, P.lagrangeFn u z) ≠ ⊤ := by
  obtain ⟨x₀, hx₀⟩ := P.nonempty_C
  obtain ⟨c, hcc⟩ := P.exists_coe_lagrangeFn u hx₀
  refine ne_of_lt (lt_of_le_of_lt (iInf_le (fun z => P.lagrangeFn u z) x₀) ?_)
  rw [hcc]
  exact EReal.coe_lt_top c

/-- **Section 28** of [rockafellar1970convex], condition (d): $(\bar u^*, \bar x)$ is a saddle-point
of $L$ if and only if $\bar u^* \in E_r$, $\bar x$ is a feasible solution, and the infimum of
$h = f_0 + \bar v_1^* f_1 + \dots + \bar v_m^* f_m$ over $\mathbb{R}^n$ equals $f_0(\bar x)$. -/
theorem isSaddlePoint_programLagrangian_iff {u : Rn m} {x : Rn n} :
    IsSaddlePoint P.saddleFn (u, x) ↔
      u ∈ P.multiplierCone ∧ x ∈ P.feasibleSet ∧ (⨅ z, P.lagrangeFn u z) = P.f₀ x := by
  rw [isSaddlePoint_iff_iSup_eq_iInf]
  have hsup : (⨆ u' : Rn m, P.programLagrangian u' x) = P.objective x := P.iSup_programLagrangian x
  constructor
  · intro h
    have h' : P.objective x = ⨅ z, P.programLagrangian u z := by rw [← hsup]; exact h
    by_cases hu : u ∈ P.multiplierCone
    · rw [P.iInf_programLagrangian_of_mem hu] at h'
      have hne : P.objective x ≠ ⊤ := by rw [h']; exact P.iInf_lagrangeFn_ne_top u
      have hF : x ∈ P.feasibleSet := by
        by_contra hc
        exact hne (P.objective_of_notMem hc)
      exact ⟨hu, hF, by rw [← h', P.objective_of_mem hF]⟩
    · rw [P.iInf_programLagrangian_of_notMem hu] at h'
      exact absurd h' (P.objective_ne_bot x)
  · rintro ⟨hu, hF, heq⟩
    change (⨆ u' : Rn m, P.programLagrangian u' x) = ⨅ z, P.programLagrangian u z
    rw [hsup, P.iInf_programLagrangian_of_mem hu, heq, P.objective_of_mem hF]

/-- **Theorem 28.3** of [rockafellar1970convex]. Let $(P)$ be an ordinary convex program with
Lagrangian $L$, and let $\bar u^* \in \mathbb{R}^m$ and $\bar x \in \mathbb{R}^n$. Then
$\bar u^*$ is a Kuhn–Tucker vector for $(P)$ and $\bar x$ is an optimal solution to $(P)$ if and
only if $(\bar u^*, \bar x)$ is a saddle-point of $L$, that is,
$$L(u^*, \bar x) \le L(\bar u^*, \bar x) \le L(\bar u^*, x) \qquad \text{for all } u^* \in
  \mathbb{R}^m, \ x \in \mathbb{R}^n.$$

The saddle-point is `ConvexAnalysis.IsSaddlePoint` for
`Rockafellar.OrdinaryConvexProgram.saddleFn`. -/
theorem theorem_28_3 {u : Rn m} {x : Rn n} :
    (P.IsKuhnTuckerVector u ∧ x ∈ P.optimalSolutions) ↔
      IsSaddlePoint P.saddleFn (u, x) := by
  rw [P.isSaddlePoint_programLagrangian_iff]
  constructor
  · rintro ⟨hkt, hopt⟩
    obtain ⟨hF, hval⟩ := (P.mem_optimalSolutions_iff_of_ne_top hkt.optimalValue_ne_top).1 hopt
    exact ⟨hkt.nonneg, hF, by rw [hkt.iInf_eq, hval]⟩
  · rintro ⟨hu, hF, heq⟩
    have hle : (⨅ z, P.lagrangeFn u z) ≤ P.optimalValue := P.iInf_lagrangeFn_le_optimalValue hu
    have hge : P.optimalValue ≤ P.f₀ x := P.optimalValue_le hF
    have h1 : (⨅ z, P.lagrangeFn u z) = P.optimalValue :=
      le_antisymm hle (by rw [heq]; exact hge)
    have hkt : P.IsKuhnTuckerVector u :=
      { nonneg := hu
        ne_bot := by rw [heq]; exact P.properConvex_f₀.ne_bot x
        ne_top := P.iInf_lagrangeFn_ne_top u
        iInf_eq := h1 }
    refine ⟨hkt, P.mem_optimalSolutions_iff.2 ?_⟩
    rw [P.objective_of_mem hF, ← heq, h1]

/-! ### The Kuhn–Tucker conditions (a), (b), (c) -/

/-- Let $\lambda \in E_r$ and $x_0 \in \operatorname{ri} C$. Then each summand $\lambda_i f_i$ of
$h$ is admissible at $x_0$ in the sense of `ConvexAnalysis.IsLagrangeSummand`. For $i \le r$,
$f_i$ is convex and proper, $\lambda_i \ge 0$, and $x_0 \in \operatorname{ri}(\operatorname{dom}
f_i)$ by extension convention (b). For $i > r$, $f_i$ is affine, and its linear part is
$\langle \cdot, a \rangle$ for a vector $a \in \mathbb{R}^n$ by the Fréchet–Riesz theorem. -/
theorem isLagrangeSummand {u : Rn m} (hu : u ∈ P.multiplierCone) {x₀ : Rn n}
    (hx₀ : x₀ ∈ ri P.C) (i : Fin m) : IsLagrangeSummand (pairing n) x₀ (u i) (P.f i) := by
  rcases lt_or_ge (i : ℕ) P.r with hi | hi
  · exact Or.inl ⟨hu i hi, P.convexFn_f i hi, P.properConvex_f i hi, P.relint_subset i hi hx₀⟩
  · obtain ⟨a, ha⟩ := P.exists_affine i hi
    obtain ⟨b, hb⟩ := exists_linFn (LinearMap.toContinuousLinearMap a.linear)
    exact Or.inr ⟨a, b, ha, fun w => by rw [← linFn_apply b w, hb]; rfl⟩

/-- **Section 28** of [rockafellar1970convex], the subdifferential of $h$ by Theorem 23.8. For
$\lambda \in E_r$ and every $x \in \mathbb{R}^n$,
$$\partial h(x) = \partial f_0(x) + \sum_{i : \lambda_i \neq 0} \lambda_i \partial f_i(x).$$
The terms with $\lambda_i = 0$ are omitted, as the parenthesis in condition (c) of Theorem 28.3
says.

This specializes `ConvexAnalysis.subdifferential_add_sum_coe_mul` to the family
$f_1, \dots, f_m$. -/
theorem subdifferential_lagrangeFn {u : Rn m} (hu : u ∈ P.multiplierCone) (x : Rn n) :
    subdifferential (pairing n) (P.lagrangeFn u) x
      = subdifferential (pairing n) P.f₀ x
        + ∑ i ∈ activeIndices u, u i • subdifferential (pairing n) (P.f i) x := by
  obtain ⟨x₀, hx₀⟩ := P.relint_C_nonempty
  have hsep : Function.Injective (pairing n).flip :=
    LinearMap.ker_eq_bot.1
      (LinearMap.separatingRight_iff_flip_ker_eq_bot.1 (separatingRight_pairing n))
  have hactive : activeIndices u = Finset.univ.filter fun i => u i ≠ 0 :=
    Finset.ext fun i => by simp [activeIndices]
  have hfn : P.lagrangeFn u = fun y => P.f₀ y + ∑ i, (u i : EReal) * P.f i y :=
    funext fun y => P.lagrangeFn_apply u y
  rw [hactive, hfn]
  exact subdifferential_add_sum_coe_mul hsep P.convexFn_f₀ P.properConvex_f₀ (P.convexDom_f₀ ▸ hx₀)
    (fun i _ => P.isLagrangeSummand hu hx₀ i) x

/-- **Theorem 28.3** of [rockafellar1970convex], the Kuhn–Tucker conditions. A vector
$\bar u^* = (\lambda_1, \dots, \lambda_m)$ is a Kuhn–Tucker vector for $(P)$ and $\bar x$ is an
optimal solution to $(P)$ if and only if $\bar x$ and the $\lambda_i$ satisfy the **Kuhn–Tucker
conditions**:

* (a) $\lambda_i \ge 0$, $f_i(\bar x) \le 0$ and $\lambda_i f_i(\bar x) = 0$ for
  $i = 1, \dots, r$;
* (b) $f_i(\bar x) = 0$ for $i = r + 1, \dots, m$;
* (c) $0 \in \partial f_0(\bar x) + \lambda_1 \partial f_1(\bar x) + \dots + \lambda_m \partial
  f_m(\bar x)$, with the terms with $\lambda_i = 0$ omitted.

By `Rockafellar.OrdinaryConvexProgram.theorem_28_3`, the conditions are also equivalent to
$(\bar u^*, \bar x)$ being a saddle-point of $L$. The condition $\bar x \in C$ is not a separate
clause: it follows from (c), because $\partial f_0(\bar x)$ is then nonempty and
$\operatorname{dom} f_0 = C$. The omitted terms are those outside `Rockafellar.activeIndices`. -/
theorem theorem_28_3_kuhnTucker {u : Rn m} {x : Rn n} :
    (P.IsKuhnTuckerVector u ∧ x ∈ P.optimalSolutions) ↔
      ((∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i ∧ P.f i x ≤ 0 ∧ (u i : EReal) * P.f i x = 0) ∧
        (∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = 0) ∧
        (0 : Rn n) ∈ subdifferential (pairing n) P.f₀ x
          + ∑ i ∈ activeIndices u, u i • subdifferential (pairing n) (P.f i) x) := by
  rw [P.theorem_28_3, P.isSaddlePoint_programLagrangian_iff]
  constructor
  · rintro ⟨hu, hF, heq⟩
    obtain ⟨c₀, h₀⟩ := P.exists_coe_f₀ hF.1
    choose c hc using P.exists_coe_f hF.1
    -- `h(x̄) = f₀(x̄)`, so every multiplier term vanishes
    have hhx : P.lagrangeFn u x = P.f₀ x :=
      le_antisymm (P.lagrangeFn_le_f₀ hu hF)
        (by rw [← heq]; exact iInf_le (fun z => P.lagrangeFn u z) x)
    have hsum : ∑ i, u i * c i = 0 := by
      have h1 : ((c₀ + ∑ i, u i * c i : ℝ) : EReal) = ((c₀ : ℝ) : EReal) := by
        rw [← P.lagrangeFn_eq_coe h₀ hc, hhx, h₀]
      have h2 : c₀ + ∑ i, u i * c i = c₀ := by exact_mod_cast h1
      linarith
    have hnonpos : ∀ i ∈ (Finset.univ : Finset (Fin m)), u i * c i ≤ 0 := by
      intro i _
      rcases lt_or_ge (i : ℕ) P.r with hi | hi
      · have h1 : c i ≤ 0 := by have := hF.2.1 i hi; rw [hc i] at this; exact_mod_cast this
        exact mul_nonpos_of_nonneg_of_nonpos (hu i hi) h1
      · have h1 : c i = 0 := by have := hF.2.2 i hi; rw [hc i] at this; exact_mod_cast this
        rw [h1, mul_zero]
    have hzero : ∀ i : Fin m, u i * c i = 0 :=
      fun i => (Finset.sum_eq_zero_iff_of_nonpos hnonpos).1 hsum i (Finset.mem_univ i)
    refine ⟨fun i hi => ⟨hu i hi, hF.2.1 i hi, ?_⟩, fun i hi => hF.2.2 i hi, ?_⟩
    · rw [hc i, ← EReal.coe_mul, hzero i]
      norm_num
    · rw [← P.subdifferential_lagrangeFn hu x,
        ← mem_argmin_iff_zero_mem_subdifferential (pairing n) (P.lagrangeFn u) x]
      intro z
      rw [hhx, ← heq]
      exact iInf_le (fun w => P.lagrangeFn u w) z
  · rintro ⟨ha, hb, hcond⟩
    -- `x̄ ∈ C`, because `∂f₀(x̄)` is non-empty
    obtain ⟨v₀, hv₀, -, -, -⟩ := Set.mem_add.1 hcond
    have hxC : x ∈ P.C := by
      rw [← P.convexDom_f₀]
      exact mem_convexDom_of_mem_subdifferential P.properConvex_f₀ hv₀
    have hu : u ∈ P.multiplierCone := fun i hi => (ha i hi).1
    have hF : x ∈ P.feasibleSet := ⟨hxC, fun i hi => (ha i hi).2.1, hb⟩
    have hhx : P.lagrangeFn u x = P.f₀ x := by
      refine P.lagrangeFn_eq_f₀ fun i => ?_
      rcases lt_or_ge (i : ℕ) P.r with hi | hi
      · exact (ha i hi).2.2
      · rw [hb i hi, mul_zero]
    have hmin : x ∈ argmin (P.lagrangeFn u) := by
      rw [mem_argmin_iff_zero_mem_subdifferential (pairing n) (P.lagrangeFn u) x,
        P.subdifferential_lagrangeFn hu x]
      exact hcond
    exact ⟨hu, hF, by rw [← hhx]; exact iInf_eq_of_mem_argmin hmin⟩

/-- **Corollary 28.3.1** of [rockafellar1970convex] (the Kuhn–Tucker theorem). Let $(P)$ be an
ordinary convex program that has at least one Kuhn–Tucker vector. Then $\bar x$ is an optimal
solution to $(P)$ if and only if there is a vector $\bar u^*$ such that $(\bar u^*, \bar x)$ is
a saddle-point of the Lagrangian $L$ of $(P)$.

**Generalization.** The book assumes that $(P)$ satisfies the hypotheses of Theorem 28.2. The
proof uses only the conclusion of Theorem 28.2, that a Kuhn–Tucker vector exists, and this is
the hypothesis here.

The book prints no proof. -/
theorem corollary_28_3_1 (hkt : ∃ u : Rn m, P.IsKuhnTuckerVector u) {x : Rn n} :
    x ∈ P.optimalSolutions ↔
      ∃ u : Rn m, IsSaddlePoint P.saddleFn (u, x) := by
  constructor
  · rintro hx
    obtain ⟨u, hu⟩ := hkt
    exact ⟨u, (P.theorem_28_3).1 ⟨hu, hx⟩⟩
  · rintro ⟨u, hs⟩
    exact ((P.theorem_28_3).2 hs).2

/-- **Corollary 28.3.1** of [rockafellar1970convex], second form. Let $(P)$ have at least one
Kuhn–Tucker vector. Then $\bar x$ is an optimal solution to $(P)$ if and only if there are
numbers $\lambda_1, \dots, \lambda_m$ that satisfy the Kuhn–Tucker conditions (a), (b), (c) of
Theorem 28.3 together with $\bar x$. -/
theorem corollary_28_3_1_kuhnTucker (hkt : ∃ u : Rn m, P.IsKuhnTuckerVector u) {x : Rn n} :
    x ∈ P.optimalSolutions ↔
      ∃ u : Rn m,
        (∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i ∧ P.f i x ≤ 0 ∧ (u i : EReal) * P.f i x = 0) ∧
        (∀ i : Fin m, P.r ≤ (i : ℕ) → P.f i x = 0) ∧
        (0 : Rn n) ∈ subdifferential (pairing n) P.f₀ x
          + ∑ i ∈ activeIndices u, u i • subdifferential (pairing n) (P.f i) x := by
  constructor
  · intro hx
    obtain ⟨u, hu⟩ := hkt
    exact ⟨u, (P.theorem_28_3_kuhnTucker).1 ⟨hu, hx⟩⟩
  · rintro ⟨u, hs⟩
    exact ((P.theorem_28_3_kuhnTucker).2 hs).2

end OrdinaryConvexProgram

/-! ### Theorem 28.4: the optimal value as a saddle-value -/

namespace OrdinaryConvexProgram

/-- **Section 28** of [rockafellar1970convex], the dual function. It is the concave function
$$g(u^*) = \inf_x L(u^*, x), \qquad u^* \in \mathbb{R}^m,$$
whose maximization over $\mathbb{R}^m$ is dual to $(P)$. -/
noncomputable def dualFn : Rn m → EReal := fun u => ⨅ x, P.programLagrangian u x

/-- The defining formula $g(u^*) = \inf_x L(u^*, x)$. -/
theorem dualFn_apply (u : Rn m) : P.dualFn u = ⨅ x, P.programLagrangian u x := rfl

/-- **Section 28** of [rockafellar1970convex]: $\inf_x \sup_{u^*} L(u^*, x)$ is the optimal value in
$(P)$. -/
theorem minimax_saddleFn : minimax P.saddleFn = P.optimalValue := by
  rw [minimax_apply]
  refine iInf_congr fun x => ?_
  exact P.iSup_programLagrangian x

/-- The quantity $\sup_{u^*} \inf_x L(u^*, x)$ is the supremum of $g$ over $\mathbb{R}^m$. -/
theorem maximin_saddleFn_eq_iSup_dualFn : maximin P.saddleFn = ⨆ u, P.dualFn u := rfl

/-- Weak duality: $\sup_{u^*} \inf_x L(u^*, x) \le \inf_x \sup_{u^*} L(u^*, x)$, and the right side
is the optimal value in $(P)$. -/
theorem maximin_saddleFn_le : maximin P.saddleFn ≤ P.optimalValue :=
  le_of_le_of_eq (maximin_le_minimax P.saddleFn) P.minimax_saddleFn

/-- **Theorem 28.4** of [rockafellar1970convex], first sentence. If $\bar u^*$ is a Kuhn–Tucker
vector for $(P)$ and $\bar x$ is an optimal solution to $(P)$, then the saddle-value
$L(\bar u^*, \bar x)$ is the optimal value in $(P)$. -/
theorem theorem_28_4_saddleValue {u : Rn m} {x : Rn n} (hu : P.IsKuhnTuckerVector u)
    (hx : x ∈ P.optimalSolutions) : P.programLagrangian u x = P.optimalValue := by
  have hs := (P.theorem_28_3).1 ⟨hu, hx⟩
  have h1 : (⨅ x' : Rn n, P.programLagrangian u x') = P.programLagrangian u x := hs.iInf_eq
  rw [← h1, P.iInf_programLagrangian_of_mem hu.nonneg, hu.iInf_eq]

/-- **Theorem 28.4** of [rockafellar1970convex]. A vector $\bar u^* \in \mathbb{R}^m$ is a
Kuhn–Tucker vector for $(P)$ if and only if
$$-\infty < \inf_x L(\bar u^*, x) = \sup_{u^*} \inf_x L(u^*, x) = \inf_x \sup_{u^*} L(u^*, x).$$

The two iterated extrema are `ConvexAnalysis.maximin` and `ConvexAnalysis.minimax` of
`Rockafellar.OrdinaryConvexProgram.saddleFn`. The book adds that the common value is then the
optimal value in $(P)$; this is `Rockafellar.OrdinaryConvexProgram.theorem_28_4_value`. -/
theorem theorem_28_4 {u : Rn m} :
    P.IsKuhnTuckerVector u ↔
      (⊥ < ⨅ x, P.programLagrangian u x) ∧
        (⨅ x, P.programLagrangian u x) = maximin P.saddleFn ∧
        maximin P.saddleFn = minimax P.saddleFn := by
  constructor
  · intro hu
    have hi : (⨅ x, P.programLagrangian u x) = P.optimalValue := by
      rw [P.iInf_programLagrangian_of_mem hu.nonneg, hu.iInf_eq]
    have hmax : maximin P.saddleFn = P.optimalValue := by
      refine le_antisymm P.maximin_saddleFn_le ?_
      rw [← hi]
      exact iInf_slice_le_maximin P.saddleFn u
    refine ⟨?_, by rw [hi, hmax], by rw [hmax, P.minimax_saddleFn]⟩
    rw [hi]
    exact lt_of_le_of_ne bot_le (Ne.symm hu.optimalValue_ne_bot)
  · rintro ⟨hbot, h1, h2⟩
    have hu : u ∈ P.multiplierCone := by
      by_contra hc
      rw [P.iInf_programLagrangian_of_notMem hc] at hbot
      exact absurd hbot (lt_irrefl _)
    have hval : (⨅ x, P.programLagrangian u x) = P.optimalValue := by
      rw [h1, h2, P.minimax_saddleFn]
    rw [P.iInf_programLagrangian_of_mem hu] at hval hbot
    exact ⟨hu, hbot.ne', P.iInf_lagrangeFn_ne_top u, hval⟩

/-- **Theorem 28.4** of [rockafellar1970convex], the common value. If $(P)$ has a Kuhn–Tucker
vector, then $\sup_{u^*} \inf_x L(u^*, x)$ and $\inf_x \sup_{u^*} L(u^*, x)$ both equal the
optimal value in $(P)$. -/
theorem theorem_28_4_value {u : Rn m} (hu : P.IsKuhnTuckerVector u) :
    maximin P.saddleFn = P.optimalValue ∧ minimax P.saddleFn = P.optimalValue := by
  obtain ⟨-, h1, h2⟩ := (P.theorem_28_4).1 hu
  have hi : (⨅ x, P.programLagrangian u x) = P.optimalValue := by
    rw [P.iInf_programLagrangian_of_mem hu.nonneg, hu.iInf_eq]
  exact ⟨by rw [← h1, hi], P.minimax_saddleFn⟩

/-- The dual function is the concave conjugate of $-p$, where $p$ is the perturbation function:
$g(u^*) = \inf_u \{\langle u, u^* \rangle + p(u)\}$. This is the remark of the book in the form
of `ConvexAnalysis.concaveConj`. -/
theorem dualFn_eq_concaveConj :
    P.dualFn = concaveConj (pairing m) fun w => -(P.perturbFn w) := by
  funext u
  have h : (fun x => P.programLagrangian u x)
      = fun x => ConvexAnalysis.lagrangian (pairing m) P.ineqBifun u x :=
    funext fun x => by rw [P.lagrangian_ineqBifun]
  rw [dualFn_apply, h, iInf_lagrangian, concaveConj_apply]
  refine iInf_congr fun w => ?_
  rw [sub_eq_add_neg, neg_neg]
  rfl

/-- **Section 28** of [rockafellar1970convex]: the dual function $g$ is concave. The book calls this
immediate. Here it follows from Section 29, because $g$ is a concave conjugate. -/
theorem concaveFn_dualFn : ConcaveFn P.dualFn := by
  rw [P.dualFn_eq_concaveConj]
  exact concaveFn_concaveConj (pairing m) _

/-- **Section 28** of [rockafellar1970convex]: $g(u^*) = -p^*(-u^*)$, where $p^*$ is the convex
conjugate of the perturbation function $p$ of $(P)$. -/
theorem dualFn_eq_neg_convexConj_perturbFn (u : Rn m) :
    P.dualFn u = -(convexConj (pairing m) P.perturbFn (-u)) := by
  rw [P.dualFn_eq_concaveConj, concaveConj_eq_neg_convexConj_neg]
  simp only [neg_neg]

/-- **Corollary 28.4.1** of [rockafellar1970convex]. Let $(P)$ be an ordinary convex program that
has at least one Kuhn–Tucker vector. Then the Kuhn–Tucker vectors for $(P)$ are exactly the
points at which the concave function $g(u^*) = \inf_x L(u^*, x)$ attains its supremum over
$\mathbb{R}^m$.

The book prints no proof. Weak duality gives $g \le \alpha$ everywhere, where $\alpha$ is the
optimal value. The assumed Kuhn–Tucker vector gives a point where $g = \alpha$. A point
$\bar u^*$ with $g(\bar u^*) = \alpha$ and $\alpha$ finite is a Kuhn–Tucker vector by
definition. -/
theorem corollary_28_4_1 (hkt : ∃ u : Rn m, P.IsKuhnTuckerVector u) {u : Rn m} :
    P.IsKuhnTuckerVector u ↔ u ∈ argmax P.dualFn := by
  have hweak : ∀ v : Rn m, P.dualFn v ≤ P.optimalValue := by
    intro v
    by_cases hv : v ∈ P.multiplierCone
    · rw [dualFn_apply, P.iInf_programLagrangian_of_mem hv]
      exact P.iInf_lagrangeFn_le_optimalValue hv
    · rw [dualFn_apply, P.iInf_programLagrangian_of_notMem hv]
      exact bot_le
  constructor
  · intro hu v
    have hgu : P.dualFn u = P.optimalValue := by
      rw [dualFn_apply, P.iInf_programLagrangian_of_mem hu.nonneg, hu.iInf_eq]
    rw [hgu]
    exact hweak v
  · intro hmax
    obtain ⟨u₀, hu₀⟩ := hkt
    have hgu₀ : P.dualFn u₀ = P.optimalValue := by
      rw [dualFn_apply, P.iInf_programLagrangian_of_mem hu₀.nonneg, hu₀.iInf_eq]
    have heq : P.dualFn u = P.optimalValue :=
      le_antisymm (hweak u) (by rw [← hgu₀]; exact hmax u₀)
    have hu : u ∈ P.multiplierCone := by
      by_contra hc
      rw [dualFn_apply, P.iInf_programLagrangian_of_notMem hc] at heq
      have hnb := hu₀.optimalValue_ne_bot
      exact hnb heq.symm
    rw [dualFn_apply, P.iInf_programLagrangian_of_mem hu] at heq
    have hnb : (⨅ z, P.lagrangeFn u z) ≠ ⊥ := by
      rw [heq]; exact hu₀.optimalValue_ne_bot
    exact ⟨hu, hnb, P.iInf_lagrangeFn_ne_top u, heq⟩

end OrdinaryConvexProgram

/-!
### The decomposition principle

Suppose that the coordinates of $\mathbb{R}^n$ split as $x = (x_1, \dots, x_s)$ with
$x_k \in \mathbb{R}^{n_k}$, and that every $f_i$ is separable in this splitting. Once a Kuhn–Tucker
vector has reduced $(P)$ to the minimization of $h = f_0 + \lambda_1 f_1 + \dots + \lambda_m f_m$
over $C$ (Theorem 28.1), $h$ is separable too, $h(x) = h_1(x_1) + \dots + h_s(x_s)$. The problem
then splits into the $s$ independent problems of minimizing $h_k$ over
$C^k = \operatorname{dom} h_k$.
-/

namespace OrdinaryConvexProgram

variable {s : ℕ} {nk : Fin s → ℕ}

/-- If $\lambda_i \ge 0$ for $i \le r$, then the effective domain of $h = f_0 + \lambda_1 f_1 +
\dots + \lambda_m f_m$ is $C$.

Off $C$, $h$ is $+\infty$ because $f_0$ is $+\infty$ there and the multipliers of the inequality
constraints are nonnegative. On $C$, $h$ is a real number, because extension convention (b)
makes every $f_i$ finite there. In this sense the minimization of $h$ over $C$ is an
unconstrained problem. -/
theorem convexDom_lagrangeFn {u : Rn m} (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) :
    convexDom (P.lagrangeFn u) = P.C := by
  ext x
  refine ⟨fun hx => ?_, fun hx => mem_convexDom.2 ?_⟩
  · by_contra hc
    exact absurd (P.lagrangeFn_eq_top_of_notMem_C hu hc) (mem_convexDom.1 hx).ne
  · obtain ⟨c₀, hc₀⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (P.properConvex_f₀.ne_bot x)
      (P.mem_C_iff.1 hx)
    choose c hc using fun i => P.exists_coe_f hx i
    rw [P.lagrangeFn_eq_coe hc₀ hc]
    exact EReal.coe_lt_top _

/-- **Section 28** of [rockafellar1970convex], decomposition of $C$. Let $e : \mathbb{R}^{n_1}
\times \dots \times \mathbb{R}^{n_s} \to \mathbb{R}^n$ be a linear equivalence, let
$\lambda_i \ge 0$ for $i \le r$, and let $h_k : \mathbb{R}^{n_k} \to [-\infty, +\infty]$ be
functions that never take the value $-\infty$, such that $h(e(x_1, \dots, x_s)) = h_1(x_1) +
\dots + h_s(x_s)$ for all $x$. Then, in the coordinates $x = (x_1, \dots, x_s)$, the set $C$ is
the product of the sets $C^k = \operatorname{dom} h_k$:
$e^{-1}(C) = C^1 \times \dots \times C^s$.

This is `ConvexAnalysis.convexDom_sepSum` read through $e$, together with
`Rockafellar.OrdinaryConvexProgram.convexDom_lagrangeFn`. The $h_k$ need not be proper. -/
theorem decomposition_C (e : (∀ k, Rn (nk k)) ≃ₗ[ℝ] Rn n) {u : Rn m}
    (hu : ∀ i : Fin m, (i : ℕ) < P.r → 0 ≤ u i) {h : ∀ k, Rn (nk k) → EReal}
    (hb : ∀ k (z : Rn (nk k)), h k z ≠ ⊥)
    (hsep : ∀ x, P.lagrangeFn u (e x) = ∑ k, h k (x k)) :
    ⇑e ⁻¹' P.C = univ.pi fun k => convexDom (h k) := by
  rw [← P.convexDom_lagrangeFn hu, ← convexDom_sepSum hb]
  exact congrArg convexDom (funext hsep)

/-- **Section 28** of [rockafellar1970convex], the decomposition principle. Let $e :
\mathbb{R}^{n_1} \times \dots \times \mathbb{R}^{n_s} \to \mathbb{R}^n$ be a linear equivalence,
and let $h_k : \mathbb{R}^{n_k} \to [-\infty, +\infty]$ be proper convex functions such that
$h(e(x_1, \dots, x_s)) = h_1(x_1) + \dots + h_s(x_s)$ for all $x$. Then $x = e(x_1, \dots, x_s)$
minimizes $h$ over $\mathbb{R}^n$ if and only if each $x_k$ minimizes $h_k$ over
$\mathbb{R}^{n_k}$.

With `Rockafellar.theorem_28_1`, this is the statement about $(P)$: the optimal solutions of
$(P)$ are the minimizers of $h$ that satisfy the complementary slackness conditions, and the set
of minimizers of $h$ is a product. Each factor is a problem in $\mathbb{R}^{n_k}$, while by
Corollary 28.4.1 the search for $\lambda$ is a problem in $\mathbb{R}^m$. This is the reduction
in dimension that the passage of the book is about. -/
theorem decomposition_argmin_lagrangeFn (e : (∀ k, Rn (nk k)) ≃ₗ[ℝ] Rn n) {u : Rn m}
    {h : ∀ k, Rn (nk k) → EReal} (hp : ∀ k, ProperConvex (h k))
    (hsep : ∀ x, P.lagrangeFn u (e x) = ∑ k, h k (x k)) :
    ⇑e ⁻¹' argmin (P.lagrangeFn u) = univ.pi fun k => argmin (h k) := by
  rw [← argmin_comp_of_surjective (g := P.lagrangeFn u) e.surjective, ← argmin_sepSum hp]
  exact congrArg argmin (funext hsep)

end OrdinaryConvexProgram

/-!
### Two programs with no Kuhn–Tucker vector

These are two unnumbered counterexamples of Section 28, which show that the constraint qualification
in Theorem 28.2 is needed. The first program has a unique optimal solution, a finite optimal value
and no Kuhn–Tucker vector. The second has only linear constraints, so it satisfies every hypothesis
of Corollary 28.2.2 except the existence of a feasible solution in $\operatorname{ri} C$, and it has
no Kuhn–Tucker vector either.
-/

/-- The $j$-th coordinate function $x \mapsto \xi_j$ on $\mathbb{R}^n$, as an affine function. -/
noncomputable def coordAffine (n : ℕ) (j : Fin n) : Rn n →ᵃ[ℝ] ℝ :=
  LinearMap.toAffineMap ⟨⟨fun x => x j, fun _ _ => rfl⟩, fun _ _ => rfl⟩

/-- The value of the $j$-th coordinate function at $x$ is the $j$-th coordinate of $x$. -/
@[simp] theorem coordAffine_apply (n : ℕ) (j : Fin n) (x : Rn n) : coordAffine n j x = x j := rfl

private theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases i with ⟨_ | _ | k, hk⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

/-- The function $\xi_1^2 - \xi_2$ is convex on $\mathbb{R}^2$. -/
private theorem convexOn_sqSub : ConvexOn ℝ Set.univ fun x : Rn 2 => x 0 ^ 2 - x 1 := by
  refine ⟨convex_univ, fun u _ v _ a b ha hb _ => ?_⟩
  have h0 : (a • u + b • v) 0 = a * u 0 + b * v 0 := rfl
  have h1 : (a • u + b • v) 1 = a * u 1 + b * v 1 := rfl
  simp only [h0, h1, smul_eq_mul]
  nlinarith [sq_nonneg (u 0 - v 0), mul_nonneg ha hb]

/-! ### A program with a unique optimal solution and no Kuhn–Tucker vector -/

/-- The constraint function $f_1(\xi_1, \xi_2) = \xi_2$ of the first counterexample. -/
noncomputable def ex1Constraint₁ : Rn 2 → EReal := fun x => ((x 1 : ℝ) : EReal)

/-- The constraint function $f_2(\xi_1, \xi_2) = \xi_1^2 - \xi_2$ of the first counterexample. -/
noncomputable def ex1Constraint₂ : Rn 2 → EReal := fun x => ((x 0 ^ 2 - x 1 : ℝ) : EReal)

private theorem ex1_convexDom_f (i : Fin 2) :
    convexDom (![ex1Constraint₁, ex1Constraint₂] i) = Set.univ := by
  rcases fin_two_cases i with rfl | rfl
  · exact convexDom_coe (fun x : Rn 2 => x 1)
  · exact convexDom_coe (fun x : Rn 2 => x 0 ^ 2 - x 1)

/-- **Section 28** of [rockafellar1970convex], first counterexample. This is the ordinary convex
program in $\mathbb{R}^2$ with $C = \mathbb{R}^2$, $f_0(\xi_1, \xi_2) = \xi_1$,
$f_1(\xi_1, \xi_2) = \xi_2$, $f_2(\xi_1, \xi_2) = \xi_1^2 - \xi_2$ and $r = 2$, that is, the
minimization of $\xi_1$ subject to $\xi_2 \le 0$ and $\xi_1^2 - \xi_2 \le 0$.

Its only feasible solution, and hence its unique optimal solution, is the origin, and its
optimal value is $0$. It has no Kuhn–Tucker vector
(`Rockafellar.ex1_not_exists_isKuhnTuckerVector`). Theorem 28.2 does not apply, because no point
satisfies $f_1 \le 0$ and $f_2 < 0$. -/
noncomputable def ex1 : OrdinaryConvexProgram 2 2 where
  C := Set.univ
  f₀ := fun x => ((x 0 : ℝ) : EReal)
  f := ![ex1Constraint₁, ex1Constraint₂]
  r := 2
  r_le := le_refl 2
  convexFn_f₀ :=
    (closedProperConvexFn_coe_affineMap
      (coordAffine 2 0).continuous_of_finiteDimensional).convex
  properConvex_f₀ := properConvex_coe _
  convexDom_f₀ := convexDom_coe _
  convexFn_f := by
    intro i _
    rcases fin_two_cases i with rfl | rfl
    · exact (closedProperConvexFn_coe_affineMap
        (coordAffine 2 1).continuous_of_finiteDimensional).convex
    · exact convexOn_sqSub.convexFn_coe
  properConvex_f := by
    intro i _
    rcases fin_two_cases i with rfl | rfl
    · exact properConvex_coe (fun x : Rn 2 => x 1)
    · exact properConvex_coe (fun x : Rn 2 => x 0 ^ 2 - x 1)
  subset_convexDom_f := fun i _ => (ex1_convexDom_f i).ge
  relint_subset := fun i _ => by rw [ex1_convexDom_f i]
  exists_affine := by intro i hi; exact absurd i.isLt (by omega)

/-- The set $C$ of the first counterexample is $\mathbb{R}^2$. -/
@[simp] theorem ex1_C : ex1.C = Set.univ := rfl

/-- The first counterexample has $r = 2$ inequality constraints. -/
@[simp] theorem ex1_r : ex1.r = 2 := rfl

/-- The objective of the first counterexample is $f_0(\xi_1, \xi_2) = \xi_1$. -/
@[simp] theorem ex1_f₀ (x : Rn 2) : ex1.f₀ x = ((x 0 : ℝ) : EReal) := rfl

/-- The first constraint function of the first counterexample is $f_1(\xi_1, \xi_2) = \xi_2$. -/
@[simp] theorem ex1_f_zero (x : Rn 2) : ex1.f 0 x = ((x 1 : ℝ) : EReal) := rfl

/-- The second constraint function of the first counterexample is
$f_2(\xi_1, \xi_2) = \xi_1^2 - \xi_2$. -/
@[simp] theorem ex1_f_one (x : Rn 2) : ex1.f 1 x = ((x 0 ^ 2 - x 1 : ℝ) : EReal) := rfl

/-- The feasible set of the first counterexample is $\{0\}$: the only point with $\xi_2 \le 0$ and
$\xi_1^2 - \xi_2 \le 0$ is the origin. -/
theorem ex1_feasibleSet : ex1.feasibleSet = {0} := by
  ext x
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, h1, -⟩
    have hA : x 1 ≤ 0 := by
      have h := h1 0 (by norm_num)
      rw [ex1_f_zero] at h
      exact EReal.coe_nonpos.1 h
    have hB : x 0 ^ 2 - x 1 ≤ 0 := by
      have h := h1 1 (by norm_num)
      rw [ex1_f_one] at h
      exact EReal.coe_nonpos.1 h
    have h10 : x 1 = 0 := by nlinarith [sq_nonneg (x 0)]
    have h00 : x 0 = 0 := by nlinarith [sq_nonneg (x 0)]
    ext i
    rcases fin_two_cases i with rfl | rfl
    · simpa using h00
    · simpa using h10
  · rintro rfl
    refine ⟨trivial, fun i _ => ?_, fun i hi => ?_⟩
    · rcases fin_two_cases i with rfl | rfl
      · rw [ex1_f_zero]; exact EReal.coe_nonpos.2 (le_of_eq rfl)
      · rw [ex1_f_one]; exact EReal.coe_nonpos.2 (by norm_num)
    · rw [ex1_r] at hi; exact absurd i.isLt (by omega)

/-- The optimal value of the first counterexample is $0$. -/
theorem ex1_optimalValue : ex1.optimalValue = 0 := by
  rw [ex1.optimalValue_eq_biInf, ex1_feasibleSet]
  have h0 : (0 : Rn 2) ∈ ({0} : Set (Rn 2)) := rfl
  refine le_antisymm ?_ (le_iInf₂ fun x hx => ?_)
  · refine le_trans (iInf_le _ (0 : Rn 2)) (le_trans (iInf_le _ h0) ?_)
    rw [ex1_f₀]; norm_num
  · rw [Set.mem_singleton_iff] at hx
    rw [hx, ex1_f₀]
    norm_num

/-- **Section 28** of [rockafellar1970convex]: the first counterexample has the origin $(0, 0)$ as
its unique optimal solution. -/
theorem ex1_optimalSolutions : ex1.optimalSolutions = {0} := by
  have hne : ex1.optimalValue ≠ ⊤ := by rw [ex1_optimalValue]; exact (EReal.zero_lt_top).ne
  rw [← ex1_feasibleSet]
  ext x
  rw [ex1.mem_optimalSolutions_iff_of_ne_top hne]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [ex1_feasibleSet, Set.mem_singleton_iff] at h
  rw [h, ex1_f₀, ex1_optimalValue]
  norm_num

private theorem ex1_lagrangeFn (u : Rn 2) (x : Rn 2) :
    ex1.lagrangeFn u x = ((x 0 + u 0 * x 1 + u 1 * (x 0 ^ 2 - x 1) : ℝ) : EReal) := by
  rw [OrdinaryConvexProgram.lagrangeFn_apply, Fin.sum_univ_two, ex1_f₀, ex1_f_zero, ex1_f_one,
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ←
    EReal.coe_add]
  congr 1
  ring

/-- **Section 28** of [rockafellar1970convex]: the first counterexample has no Kuhn–Tucker vector,
although its optimal value is finite and its optimal solution is unique.

If $(\lambda_1, \lambda_2)$ were one, then $\xi_1 + \lambda_1 \xi_2 + \lambda_2 (\xi_1^2 -
\xi_2) \ge 0$ for every $(\xi_1, \xi_2)$. The choice $\xi_1 = 0$,
$\xi_2 = \lambda_2 - \lambda_1$ forces $\lambda_1 = \lambda_2 =: \lambda$. Then
$\xi_1 = -1/(\lambda + 1)$, $\xi_2 = 0$ makes the left side $-1/(\lambda + 1)^2 < 0$. -/
theorem ex1_not_exists_isKuhnTuckerVector : ¬ ∃ u : Rn 2, ex1.IsKuhnTuckerVector u := by
  rintro ⟨u, hu⟩
  have hreal : ∀ x : Rn 2, 0 ≤ x 0 + u 0 * x 1 + u 1 * (x 0 ^ 2 - x 1) := by
    intro x
    have h : (0 : EReal) ≤ ex1.lagrangeFn u x := by
      rw [← ex1_optimalValue, ← hu.iInf_eq]
      exact iInf_le _ x
    rw [ex1_lagrangeFn] at h
    exact EReal.coe_nonneg.1 h
  have hnn : (0 : ℝ) ≤ u 0 := hu.nonneg 0 (by norm_num)
  -- the two multipliers must agree
  have heq : u 0 = u 1 := by
    have h := hreal (WithLp.toLp 2 ![0, -(u 0 - u 1)])
    have e0 : (WithLp.toLp 2 ![(0 : ℝ), -(u 0 - u 1)] : Rn 2) 0 = 0 := rfl
    have e1 : (WithLp.toLp 2 ![(0 : ℝ), -(u 0 - u 1)] : Rn 2) 1 = -(u 0 - u 1) := rfl
    rw [e0, e1] at h
    nlinarith [sq_nonneg (u 0 - u 1)]
  -- and then no such multiplier can exist
  have hd : (0 : ℝ) < u 0 + 1 := by linarith
  have h := hreal (WithLp.toLp 2 ![-(1 / (u 0 + 1)), 0])
  have e0 : (WithLp.toLp 2 ![-(1 / (u 0 + 1)), (0 : ℝ)] : Rn 2) 0 = -(1 / (u 0 + 1)) := rfl
  have e1 : (WithLp.toLp 2 ![-(1 / (u 0 + 1)), (0 : ℝ)] : Rn 2) 1 = 0 := rfl
  rw [e0, e1, ← heq] at h
  have hexpr : -(1 / (u 0 + 1)) + u 0 * 0 + u 0 * ((-(1 / (u 0 + 1))) ^ 2 - 0)
      = -(1 / (u 0 + 1) ^ 2) := by
    field_simp
    ring
  rw [hexpr] at h
  have hpos : (0 : ℝ) < 1 / (u 0 + 1) ^ 2 := by positivity
  linarith

/-! ### A program with linear constraints and no Kuhn–Tucker vector -/

/-- The set $C = \{(\xi_1, \xi_2) \mid \xi_1^2 - \xi_2 \le 0\}$ of the second counterexample. It is
a parabolic region whose relative interior does not meet the feasible set
$\{(\xi_1, \xi_2) \in C \mid \xi_2 = 0\}$. -/
def ex2Set : Set (Rn 2) := {x | x 0 ^ 2 - x 1 ≤ 0}

/-- A point $(\xi_1, \xi_2)$ lies in the set $C$ of the second counterexample if and only if
$\xi_1^2 - \xi_2 \le 0$. -/
theorem mem_ex2Set {x : Rn 2} : x ∈ ex2Set ↔ x 0 ^ 2 - x 1 ≤ 0 := Iff.rfl

/-- The set $C = \{(\xi_1, \xi_2) \mid \xi_1^2 - \xi_2 \le 0\}$ of the second counterexample is
convex. -/
theorem convex_ex2Set : Convex ℝ ex2Set := by
  have h := convexOn_sqSub.convex_le 0
  have he : {x ∈ (Set.univ : Set (Rn 2)) | x 0 ^ 2 - x 1 ≤ 0} = ex2Set := by
    ext x; simp only [Set.mem_univ, true_and, mem_ex2Set, Set.mem_ofPred_eq]
  rwa [he] at h

/-- **Section 28** of [rockafellar1970convex], second counterexample. This is the ordinary convex
program in $\mathbb{R}^2$ with $C = \{(\xi_1, \xi_2) \mid \xi_1^2 - \xi_2 \le 0\}$,
$f_0(\xi_1, \xi_2) = \xi_1$ on $C$ (and $+\infty$ off $C$), the single constraint function
$f_1(\xi_1, \xi_2) = \xi_2$, and $r = 0$, that is, the minimization of $\xi_1$ over $C$ subject
to $\xi_2 = 0$.

The objective is linear on $C$ and the constraint is a linear equation, so every hypothesis of
Corollary 28.2.2 holds except the existence of a feasible solution in $\operatorname{ri} C$: the
feasible set is $\{0\}$ and $0 \notin \operatorname{ri} C$. The origin is again the unique
optimal solution, the optimal value is $0$, and there is no Kuhn–Tucker vector
(`Rockafellar.ex2_not_exists_isKuhnTuckerVector`). So the relative interior condition in Theorem
28.2 and Corollary 28.2.2 cannot be dropped. -/
noncomputable def ex2 : OrdinaryConvexProgram 2 1 where
  C := ex2Set
  f₀ := ConvexAnalysis.convexRestrict ex2Set fun x => ((x 0 : ℝ) : EReal)
  f := fun _ x => ((x 1 : ℝ) : EReal)
  r := 0
  r_le := Nat.zero_le 1
  convexFn_f₀ := (convexOn_iff_convexFn ex2Set _).1
    ⟨convex_ex2Set, fun _ _ _ _ _ _ _ _ _ => le_of_eq rfl⟩
  properConvex_f₀ := properConvex_convexRestrict_coe ⟨0, by rw [mem_ex2Set]; norm_num⟩ _
  convexDom_f₀ := convexDom_convexRestrict_coe _ _
  convexFn_f := fun _ hi => absurd hi (by omega)
  properConvex_f := fun _ hi => absurd hi (by omega)
  subset_convexDom_f := fun _ hi => absurd hi (by omega)
  relint_subset := fun _ hi => absurd hi (by omega)
  exists_affine := fun _ _ => ⟨coordAffine 2 1, fun _ => rfl⟩

/-- The set $C$ of the second counterexample is $\{(\xi_1, \xi_2) \mid \xi_1^2 - \xi_2 \le 0\}$. -/
@[simp] theorem ex2_C : ex2.C = ex2Set := rfl

/-- The second counterexample has $r = 0$ inequality constraints: its one constraint is an equation.
-/
@[simp] theorem ex2_r : ex2.r = 0 := rfl

/-- The constraint function of the second counterexample is $f_1(\xi_1, \xi_2) = \xi_2$. -/
@[simp] theorem ex2_f (i : Fin 1) (x : Rn 2) : ex2.f i x = ((x 1 : ℝ) : EReal) := rfl

/-- On $C$, the objective of the second counterexample is $f_0(\xi_1, \xi_2) = \xi_1$. -/
theorem ex2_f₀_of_mem {x : Rn 2} (hx : x ∈ ex2Set) : ex2.f₀ x = ((x 0 : ℝ) : EReal) :=
  convexRestrict_of_mem (f := fun y : Rn 2 => ((y 0 : ℝ) : EReal)) hx

/-- The feasible set of the second counterexample is $\{0\}$: the only point of $C$ with $\xi_2 = 0$
is the origin. -/
theorem ex2_feasibleSet : ex2.feasibleSet = {0} := by
  ext x
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hC, -, h2⟩
    have hB : x 0 ^ 2 - x 1 ≤ 0 := mem_ex2Set.1 hC
    have h10 : x 1 = 0 := by
      have h := h2 0 (Nat.zero_le _)
      rw [ex2_f] at h
      exact_mod_cast h
    have h00 : x 0 = 0 := by nlinarith [sq_nonneg (x 0)]
    ext i
    rcases fin_two_cases i with rfl | rfl
    · simpa using h00
    · simpa using h10
  · rintro rfl
    refine ⟨by rw [ex2_C, mem_ex2Set]; norm_num, fun i hi => ?_, fun i _ => ?_⟩
    · rw [ex2_r] at hi; exact absurd hi (Nat.not_lt_zero _)
    rw [ex2_f]
    norm_num

/-- The optimal value of the second counterexample is $0$. -/
theorem ex2_optimalValue : ex2.optimalValue = 0 := by
  have h0 : (0 : Rn 2) ∈ ({0} : Set (Rn 2)) := rfl
  have hC : (0 : Rn 2) ∈ ex2Set := by rw [mem_ex2Set]; norm_num
  rw [ex2.optimalValue_eq_biInf, ex2_feasibleSet]
  refine le_antisymm ?_ (le_iInf₂ fun x hx => ?_)
  · refine le_trans (iInf_le _ (0 : Rn 2)) (le_trans (iInf_le _ h0) ?_)
    rw [ex2_f₀_of_mem hC]; norm_num
  · rw [Set.mem_singleton_iff] at hx
    rw [hx, ex2_f₀_of_mem hC]
    norm_num

/-- **Section 28** of [rockafellar1970convex]: the second counterexample has the origin $(0, 0)$ as
its unique optimal solution. -/
theorem ex2_optimalSolutions : ex2.optimalSolutions = {0} := by
  have hne : ex2.optimalValue ≠ ⊤ := by rw [ex2_optimalValue]; exact (EReal.zero_lt_top).ne
  have hC : (0 : Rn 2) ∈ ex2Set := by rw [mem_ex2Set]; norm_num
  rw [← ex2_feasibleSet]
  ext x
  rw [ex2.mem_optimalSolutions_iff_of_ne_top hne]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [ex2_feasibleSet, Set.mem_singleton_iff] at h
  rw [h, ex2_f₀_of_mem hC, ex2_optimalValue]
  norm_num

private theorem ex2_lagrangeFn_of_mem (u : Rn 1) {x : Rn 2} (hx : x ∈ ex2Set) :
    ex2.lagrangeFn u x = ((x 0 + u 0 * x 1 : ℝ) : EReal) := by
  rw [OrdinaryConvexProgram.lagrangeFn_apply, Fin.sum_univ_one, ex2_f₀_of_mem hx, ex2_f,
    ← EReal.coe_mul, ← EReal.coe_add]

/-- **Section 28** of [rockafellar1970convex]: the second counterexample has no Kuhn–Tucker vector,
although its objective is linear on $C$ and its only constraint is a linear equation.

A Kuhn–Tucker vector would be a single number $\lambda_1$ with $0 \le \xi_1 + \lambda_1 \xi_2$
for every $(\xi_1, \xi_2) \in C$. The points $(-t, t^2)$ lie in $C$ for every $t > 0$, and there
the inequality gives $t \le \lambda_1 t^2$, that is, $\lambda_1 t \ge 1$. This fails at
$t = 1/(|\lambda_1| + 1)$. -/
theorem ex2_not_exists_isKuhnTuckerVector : ¬ ∃ u : Rn 1, ex2.IsKuhnTuckerVector u := by
  rintro ⟨u, hu⟩
  have hreal : ∀ x : Rn 2, x ∈ ex2Set → 0 ≤ x 0 + u 0 * x 1 := by
    intro x hx
    have h : (0 : EReal) ≤ ex2.lagrangeFn u x := by
      rw [← ex2_optimalValue, ← hu.iInf_eq]
      exact iInf_le _ x
    rw [ex2_lagrangeFn_of_mem u hx] at h
    exact EReal.coe_nonneg.1 h
  have hd : (0 : ℝ) < |u 0| + 1 := by positivity
  set t : ℝ := 1 / (|u 0| + 1) with ht
  have htpos : (0 : ℝ) < t := by rw [ht]; positivity
  have e0 : (WithLp.toLp 2 ![-t, t ^ 2] : Rn 2) 0 = -t := rfl
  have e1 : (WithLp.toLp 2 ![-t, t ^ 2] : Rn 2) 1 = t ^ 2 := rfl
  have hmem : (WithLp.toLp 2 ![-t, t ^ 2] : Rn 2) ∈ ex2Set := by
    rw [mem_ex2Set, e0, e1]; ring_nf; exact le_refl 0
  have h := hreal _ hmem
  rw [e0, e1] at h
  have habs : |u 0| * t = 1 - t := by
    rw [ht]; field_simp; ring
  have h1 : u 0 * t ^ 2 ≤ |u 0| * t ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg t)
  have h2 : |u 0| * t ^ 2 = t - t ^ 2 := by
    calc |u 0| * t ^ 2 = |u 0| * t * t := by ring
      _ = (1 - t) * t := by rw [habs]
      _ = t - t ^ 2 := by ring
  have h3 : (0 : ℝ) < t ^ 2 := by positivity
  linarith

end Rockafellar
