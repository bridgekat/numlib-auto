/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Function

/-!
# Convexity along a line

Let $E$ be a real vector space, $S \subseteq E$, $f : E \to \mathbb{R}$, and $x, d \in E$. The
restriction of $f$ to the line through $x$ in the direction $d$ is the function
$t \mapsto f(x + t d)$ of one real variable, on the set $\{t \in \mathbb{R} \mid x + t d \in S\}$ of
steps that keep the point in $S$. Restriction to a line preserves convexity, and for convex $S$ it
also detects convexity: $f$ is convex on $S$ if and only if all its restrictions to lines are
convex. The converse turns a statement about a function on a vector space into statements about
functions of one real variable, where the calculus of a single derivative applies. The
second-derivative criterion for convexity on $\mathbb{R}^n$ is proved in this way from the criterion
on an interval. The presentation follows [rockafellar1970convex], §4.

## Main results

* `Convex.line_steps`: for convex $S$, the set of steps $\{t \mid x + t d \in S\}$ is convex.
* `ConvexAnalysis.convexOn_comp_line`, `ConvexAnalysis.concaveOn_comp_line`: the restriction of a
  convex (concave) function to a line is convex (concave).
* `ConvexAnalysis.convexOn_iff_lines`, `ConvexAnalysis.concaveOn_iff_lines`: for convex $S$, $f$ is
  convex (concave) on $S$ if and only if all its restrictions to lines are.
* `ConvexAnalysis.isOpen_line_steps`: for open $S$, the set of steps is open.
* `ConvexAnalysis.continuousAt_comp_line_of_convexOn`,
  `ConvexAnalysis.continuousAt_comp_line_of_concaveOn`: a convex or concave function on an open set
  is continuous along each line through a point of the set.

## Implementation notes

* The set of steps is written `{t | x + t • d ∈ S}` and not as an interval. It is an interval only
  when $S$ is convex, and the results that go from $f$ to its restrictions do not need this
  hypothesis.
-/

namespace ConvexAnalysis

/-! ### The restriction to a line -/

section Line

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E} {f : E → ℝ} {x d : E}

/-- For $x, d \in E$, real numbers $a, b$ with $a + b = 1$, and $t_1, t_2 \in \mathbb{R}$,
$$x + (a t_1 + b t_2) d = a (x + t_1 d) + b (x + t_2 d).$$
So a convex combination of two points of the line $t \mapsto x + t d$ is the point of the line
at the same convex combination of the steps. -/
theorem add_combo_smul_eq_combo (x d : E) {a b : ℝ} (hab : a + b = 1) (t₁ t₂ : ℝ) :
    x + (a • t₁ + b • t₂) • d = a • (x + t₁ • d) + b • (x + t₂ • d) := by
  rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, hab, one_smul,
    smul_eq_mul, smul_eq_mul, ← add_smul]

/-- Let $S \subseteq E$ be convex and $x, d \in E$. Then the set of steps
$\{t \in \mathbb{R} \mid x + t d \in S\}$ is a convex subset of $\mathbb{R}$. -/
theorem _root_.Convex.line_steps (hS : Convex ℝ S) (x d : E) :
    Convex ℝ {t : ℝ | x + t • d ∈ S} := by
  intro t₁ h₁ t₂ h₂ a b ha hb hab
  change x + (a • t₁ + b • t₂) • d ∈ S
  rw [add_combo_smul_eq_combo x d hab]
  exact hS h₁ h₂ ha hb hab

/-- **A convex function stays convex along a line.** Let $f$ be convex on $S \subseteq E$, and let
$x, d \in E$. Then $t \mapsto f(x + t d)$ is convex on
$\{t \in \mathbb{R} \mid x + t d \in S\}$. -/
theorem convexOn_comp_line (hf : ConvexOn ℝ S f) (x d : E) :
    ConvexOn ℝ {t : ℝ | x + t • d ∈ S} fun t => f (x + t • d) := by
  refine ⟨hf.1.line_steps x d, ?_⟩
  · intro t₁ h₁ t₂ h₂ a b ha hb hab
    change f (x + (a • t₁ + b • t₂) • d) ≤ a • f (x + t₁ • d) + b • f (x + t₂ • d)
    rw [add_combo_smul_eq_combo x d hab]
    exact hf.2 h₁ h₂ ha hb hab

/-- **A concave function stays concave along a line.** Let $f$ be concave on $S \subseteq E$, and
let $x, d \in E$. Then $t \mapsto f(x + t d)$ is concave on
$\{t \in \mathbb{R} \mid x + t d \in S\}$.

The proof applies `ConvexAnalysis.convexOn_comp_line` to $-f$. -/
theorem concaveOn_comp_line (hf : ConcaveOn ℝ S f) (x d : E) :
    ConcaveOn ℝ {t : ℝ | x + t • d ∈ S} fun t => f (x + t • d) :=
  neg_convexOn_iff.1 (convexOn_comp_line hf.neg x d)

/-- **The restrictions to lines detect convexity.** Let $S \subseteq E$ be convex and
$f : E \to \mathbb{R}$. Then $f$ is convex on $S$ if and only if, for all $x, d \in E$, the
function $t \mapsto f(x + t d)$ is convex on $\{t \in \mathbb{R} \mid x + t d \in S\}$.

For the converse direction, take $x, y \in S$. The line through $x$ in the direction $y - x$
gives the convexity inequality for the pair $x, y$ at the steps $0$ and $1$. -/
theorem convexOn_iff_lines (hS : Convex ℝ S) :
    ConvexOn ℝ S f ↔ ∀ x d : E, ConvexOn ℝ {t : ℝ | x + t • d ∈ S} fun t => f (x + t • d) := by
  refine ⟨fun hf x d => convexOn_comp_line hf x d,
    fun h => ⟨hS, fun {x} hx {y} hy a b ha hb hab => ?_⟩⟩
  have h0 : (0 : ℝ) ∈ {t : ℝ | x + t • (y - x) ∈ S} := by simpa using hx
  have h1 : (1 : ℝ) ∈ {t : ℝ | x + t • (y - x) ∈ S} := by simpa using hy
  -- The type ascription is what beta-reduces `(fun t => f (x + t • (y - x))) (a • 0 + b • 1)`;
  -- without it `rw` cannot see through the redex.
  have hmain : f (x + (a • (0 : ℝ) + b • (1 : ℝ)) • (y - x))
      ≤ a • f (x + (0 : ℝ) • (y - x)) + b • f (x + (1 : ℝ) • (y - x)) :=
    (h x (y - x)).2 h0 h1 ha hb hab
  have e1 : a • (0 : ℝ) + b • (1 : ℝ) = b := by simp
  have e2 : x + (0 : ℝ) • (y - x) = x := by simp
  have e3 : x + (1 : ℝ) • (y - x) = y := by simp
  rw [e1, e2, e3] at hmain
  have hpt : x + b • (y - x) = a • x + b • y := by
    have ha' : a = 1 - b := by linarith
    subst ha'
    module
  rwa [hpt] at hmain

/-- **The restrictions to lines detect concavity.** Let $S \subseteq E$ be convex and
$f : E \to \mathbb{R}$. Then $f$ is concave on $S$ if and only if, for all $x, d \in E$, the
function $t \mapsto f(x + t d)$ is concave on $\{t \in \mathbb{R} \mid x + t d \in S\}$.

This is the concave form of `ConvexAnalysis.convexOn_iff_lines`. -/
theorem concaveOn_iff_lines (hS : Convex ℝ S) :
    ConcaveOn ℝ S f ↔ ∀ x d : E, ConcaveOn ℝ {t : ℝ | x + t • d ∈ S} fun t => f (x + t • d) :=
  ⟨fun hf x d => concaveOn_comp_line hf x d,
    fun h => neg_convexOn_iff.1 ((convexOn_iff_lines hS).2 fun x d => neg_convexOn_iff.2 (h x d))⟩

end Line

/-! ### Topology along a line -/

section LineTopology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E] {S : Set E} {f : E → ℝ} {x d : E}

/-- Let $E$ be a topological vector space over $\mathbb{R}$, $S \subseteq E$ open and $x, d \in E$.
Then the set of steps $\{t \in \mathbb{R} \mid x + t d \in S\}$ is open. -/
theorem isOpen_line_steps (hS : IsOpen S) (x d : E) : IsOpen {t : ℝ | x + t • d ∈ S} :=
  hS.preimage (continuous_const.add (continuous_id.smul continuous_const))

/-- Let $E$ be a topological vector space over $\mathbb{R}$, let $S \subseteq E$ be open, let $f$ be
convex on $S$, and let $x \in S$ and $d \in E$. Then $t \mapsto f(x + t d)$ is continuous at
$t = 0$.

The proof applies the one-dimensional result `ConvexOn.continuousOn` of Mathlib to the
restriction of $f$ to the line, on the open set of steps. -/
theorem continuousAt_comp_line_of_convexOn (hS : IsOpen S) (hf : ConvexOn ℝ S f) (hx : x ∈ S)
    (d : E) : ContinuousAt (fun t : ℝ => f (x + t • d)) 0 := by
  have hI : IsOpen {t : ℝ | x + t • d ∈ S} := isOpen_line_steps hS x d
  have h0 : (0 : ℝ) ∈ {t : ℝ | x + t • d ∈ S} := by simpa using hx
  exact ((convexOn_comp_line hf x d).continuousOn hI).continuousAt (hI.mem_nhds h0)

/-- Let $E$ be a topological vector space over $\mathbb{R}$, let $S \subseteq E$ be open, let $f$ be
concave on $S$, and let $x \in S$ and $d \in E$. Then $t \mapsto f(x + t d)$ is continuous at
$t = 0$. -/
theorem continuousAt_comp_line_of_concaveOn (hS : IsOpen S) (hf : ConcaveOn ℝ S f) (hx : x ∈ S)
    (d : E) : ContinuousAt (fun t : ℝ => f (x + t • d)) 0 := by
  refine (continuousAt_comp_line_of_convexOn hS hf.neg hx d).neg.congr
    (Filter.Eventually.of_forall fun t => ?_)
  simp

end LineTopology

end ConvexAnalysis
