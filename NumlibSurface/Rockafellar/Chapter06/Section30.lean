/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Saddle.Correspondence
import Numlib.Analysis.Convex.Saddle.Minimax
import NumlibSurface.Rockafellar.Chapter06.Section29

/-!
# Rockafellar, Section 30: Adjoint bifunctions and dual programs

This module formalizes Section 30 of [rockafellar1970convex]. A bifunction $F$ from $\mathbb{R}^m$
to $\mathbb{R}^n$ assigns to each $u \in \mathbb{R}^m$ a function
$Fu : \mathbb{R}^n \to [-\infty, +\infty]$. A convex bifunction defines the convex program $(P)$ of
minimizing $F0$, with perturbation function $(\inf F)(u) = \inf_x (Fu)(x)$. The **adjoint** of $F$
is the concave bifunction $F^*$ from $\mathbb{R}^n$ to $\mathbb{R}^m$ given by
$$(F^* x^*)(u^*) = \inf_{u, x} \{(Fu)(x) - \langle x, x^* \rangle + \langle u, u^* \rangle\},$$
and the **dual program** $(P^*)$ is the concave program of maximizing $F^* 0$, with
$(\sup F^*)(x^*) = \sup_{u^*} (F^* x^*)(u^*)$. The section shows that the adjoint is a one-to-one
correspondence between closed proper convex and closed proper concave bifunctions, relates the
objective functions and the perturbation functions of $(P)$ and $(P^*)$ by conjugacy, and proves
weak duality $\inf F0 \ge \sup F^* 0$. The program $(P)$ is **normal** if $\inf F$ agrees with its
closure at $u = 0$; normality of $(P)$, normality of $(P^*)$ and the equality $\inf F0 = \sup F^* 0$
are equivalent for closed $F$. The section then gives ten sufficient conditions for normality, shows
that the Kuhn–Tucker vectors of each program are the optimal solutions of the other, and
characterizes the optimal pairs as the saddle-points of the Lagrangian.

All 10 numbered results of Section 30 are formalized, with one declaration for each clause of a
result with several clauses. The module also formalizes the Gale–Kuhn–Tucker duality theorem, which
the book names in the text without a number, the adjoint of the indicator bifunction of a linear
transformation, the Lagrangian form of the two objective functions, and the two unnumbered examples
of the section. The proofs specialize the duality theory of bifunctions in
`Numlib.Analysis.Convex.Extremum.Adjoint`, `Numlib.Analysis.Convex.Extremum.Normal` and
`Numlib.Analysis.Convex.Saddle.Minimax`.

## Main definitions

* Definition of the adjoint, `Rockafellar.dualProgram`: the adjoint bifunction $F^*$, which defines
  the dual program $(P^*)$.
* Example of an abnormal program, `Rockafellar.abnormalBifun`: $(Fu)(x) = e^{-\sqrt{ux}}$ for
  $u \ge 0$, $x \ge 0$, and $+\infty$ otherwise.
* Example of a normal program whose dual has no optimal solution, `Rockafellar.noDualSolutionBifun`:
  $(Fu)(x) = x$ for $x^2 \le u$, and $+\infty$ otherwise.

## Main results

* Theorem 30.1, `Rockafellar.theorem_30_1_concave`, `Rockafellar.theorem_30_1_closed`,
  `Rockafellar.theorem_30_1_proper`, `Rockafellar.theorem_30_1_biadjoint`,
  `Rockafellar.theorem_30_1_biadjoint_closed`, `Rockafellar.theorem_30_1_injective`,
  `Rockafellar.theorem_30_1_surjective`, `Rockafellar.theorem_30_1_polyhedral`: $F^*$ is a closed
  concave bifunction, $F^{**} = \operatorname{cl} F$ for convex $F$, the adjoint is a one-to-one
  correspondence between closed proper convex and closed proper concave bifunctions, and $F^*$ is
  polyhedral when $F$ is.
* Theorem 30.2, `Rockafellar.theorem_30_2_first`, `Rockafellar.theorem_30_2_second`,
  `Rockafellar.theorem_30_2_third`, `Rockafellar.theorem_30_2_fourth`: the conjugacy formulas
  $(-\inf F)^* = F^* 0$, $(F^* 0)^* = -\operatorname{cl}(\inf F)$, $(-\sup F^*)^* = F0$ and
  $(F0)^* = -\operatorname{cl}(\sup F^*)$.
* Corollary 30.2.1, `Rockafellar.corollary_30_2_1_dual`, `Rockafellar.corollary_30_2_1_dual'`,
  `Rockafellar.corollary_30_2_1_primal`, `Rockafellar.corollary_30_2_1_primal'`: $(P^*)$ is
  inconsistent if and only if $(\inf F)(u) = -\infty$ for some $u$, and $(P)$ is inconsistent if and
  only if $(\sup F^*)(x^*) = +\infty$ for some $x^*$.
* Corollary 30.2.2, `Rockafellar.corollary_30_2_2_first`, `Rockafellar.corollary_30_2_2_second`,
  `Rockafellar.corollary_30_2_2_weak`: $(\operatorname{cl}(\inf F))(0) = \sup F^* 0$,
  $(\operatorname{cl}(\sup F^*))(0) = \inf F0$, and $\inf F0 \ge \sup F^* 0$.
* Corollary 30.2.3, `Rockafellar.corollary_30_2_3_first`, `Rockafellar.corollary_30_2_3_second`:
  unless both programs are inconsistent, $\liminf_{u \to 0} (\inf F)(u) = \sup F^* 0$ and
  $\limsup_{x^* \to 0} (\sup F^*)(x^*) = \inf F0$.
* Theorem 30.3, `Rockafellar.theorem_30_3`: for a closed convex $F$, $(P)$ is normal, $(P^*)$ is
  normal, and $\inf F0 = \sup F^* 0$ are equivalent.
* Theorem 30.4, `Rockafellar.theorem_30_4_a` to `Rockafellar.theorem_30_4_j`: ten sufficient
  conditions for normality.
* Theorem 30.5, `Rockafellar.theorem_30_5`: if $(P)$ is normal with finite optimal value, the
  Kuhn–Tucker vectors for $(P)$ are the optimal solutions to $(P^*)$.
* Corollary 30.5.1, `Rockafellar.corollary_30_5_1`: for a closed proper convex $F$,
  $(\bar u^*, \bar x)$ is a saddle-point of the Lagrangian if and only if $(P)$ is normal and
  $\bar x$, $\bar u^*$ are optimal solutions to $(P)$ and $(P^*)$, if and only if
  $(F0)(\bar x) \le (F^* 0)(\bar u^*)$.
* Corollary 30.5.2, `Rockafellar.corollary_30_5_2`: if $(P)$ is consistent and $(P^*)$ is strongly
  consistent, then $(P)$ has an optimal solution.
* Unnumbered result, `Rockafellar.gale_kuhn_tucker_duality`: the Gale–Kuhn–Tucker duality theorem,
  $\inf F0 = \sup F^* 0$ for a closed polyhedral convex $F$ unless both programs are inconsistent.
* Unnumbered result, `Rockafellar.abnormalBifun_duality_gap`: the abnormal example has $\inf F0 = 1$
  and $\sup F^* 0 = 0$.
* Unnumbered result, `Rockafellar.argmax_dualProgram_noDualSolutionBifun`: the dual of the normal
  program `Rockafellar.noDualSolutionBifun` has no optimal solution.

## Conventions

* The adjoint $F^*$ is `Rockafellar.dualProgram F`.
* The perturbation function $\inf F$ is `ConvexAnalysis.infBifun F`.
* For a concave bifunction $G$, the function $\sup G$ is `ConvexAnalysis.supBifun G`.
* A convex property of a bifunction, such as convexity, closedness or properness, is the property of
  its graph function $(u, x) \mapsto (Fu)(x)$, which is `ConvexAnalysis.graphFn F`.
* The optimal solutions to $(P)$ are `ConvexAnalysis.argmin (F 0)`, and those to $(P^*)$ are
  `ConvexAnalysis.argmax (Rockafellar.dualProgram F 0)`.
* Normality of $(P)$ and of $(P^*)$ is `ConvexAnalysis.Normal` and `ConvexAnalysis.ConcaveNormal`;
  consistency, strong consistency and Kuhn–Tucker vectors are `ConvexAnalysis.Consistent`,
  `ConvexAnalysis.StronglyConsistent` and `ConvexAnalysis.KuhnTucker`, with the concave versions for
  $(P^*)$.

## Implementation notes

* `Rockafellar.dualProgram F` is an `abbrev` for `ConvexAnalysis.convexAdjointBifun` at the two
  Euclidean pairings, so every backbone theorem about `ConvexAnalysis.convexAdjointBifun` applies to
  it. The other notions above are the backbone ones, under the definitions of the book.
* The two unnumbered examples come at the end of the module, because each of them uses a theorem
  that comes later in the section.

## Deviations from the source

* **Corollary 30.2.1**, first half (generalization). The book assumes $F$ closed. The statement does
  not. See `Rockafellar.corollary_30_2_1_dual`.
* **Corollary 30.2.2**, first formula (generalization). The book assumes $F$ closed. The statement
  does not. See `Rockafellar.corollary_30_2_2_first`.
* **Corollary 30.2.3**, first formula (generalization). The book assumes $F$ closed. The statement
  does not. See `Rockafellar.corollary_30_2_3_first`.
* **Theorem 30.3**, (a) if and only if (c) (generalization). The book assumes $F$ closed. The
  statement does not. See `Rockafellar.theorem_30_3_a_iff_c`.
* **Theorem 30.4(i)** (correction). The book obtains (i) from (g), which needs $F0$ proper. The
  statement assumes that $F0$ is proper. See `Rockafellar.theorem_30_4_i`.
* **Theorem 30.4(j)** (correction). The book obtains (j) from (h), which needs $F^* 0$ proper. The
  statement assumes that $F^* 0$ is proper. See `Rockafellar.theorem_30_4_j`.

## Not formalized

* **Convexity of the abnormal example.** The book calls `Rockafellar.abnormalBifun` a closed proper
  convex bifunction. This is not proved here.
-/

open Filter Set Topology

namespace Rockafellar

open ConvexAnalysis

/-! ### The adjoint bifunction and the dual program -/

/-- **Section 30** of [rockafellar1970convex], definition of the adjoint. Let $F$ be a bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$. The **adjoint** of $F$ is the bifunction $F^*$ from
$\mathbb{R}^n$ to $\mathbb{R}^m$ given by
$$(F^* x^*)(u^*) = \inf_{u, x} \{(Fu)(x) - \langle x, x^* \rangle + \langle u, u^* \rangle\}.$$
It is the bifunction of the **dual program** $(P^*)$, the maximization of $F^* 0$.

The definition is an `abbrev` for `ConvexAnalysis.convexAdjointBifun` at the two Euclidean
pairings. -/
noncomputable abbrev dualProgram {m n : ℕ} (F : Bifun (Rn m) (Rn n)) : Bifun (Rn n) (Rn m) :=
  convexAdjointBifun (pairing m) (pairing n) F

variable {m n : ℕ} {F : Bifun (Rn m) (Rn n)}

/-- The defining formula of `Rockafellar.dualProgram`: for $x^* \in \mathbb{R}^n$ and
$u^* \in \mathbb{R}^m$,
$$(F^* x^*)(u^*) = \inf_{(u, x)} \bigl((Fu)(x) + (\langle u, u^* \rangle - \langle x, x^*
  \rangle)\bigr).$$

The book writes the two inner products as $-\langle x, x^* \rangle + \langle u, u^* \rangle$.
Here they form one real number, so that the sum never meets $\infty - \infty$. -/
theorem dualProgram_apply (F : Bifun (Rn m) (Rn n)) (y : Rn n) (v : Rn m) :
    dualProgram F y v
      = ⨅ p : Rn m × Rn n, (F p.1 p.2 + ((pairing m p.1 v - pairing n p.2 y : ℝ) : EReal)) :=
  rfl

/-- The objective function of $(P^*)$: $(F^* 0)(u^*) = \inf_u \{\langle u, u^* \rangle + (\inf
F)(u)\}$ for every $u^* \in \mathbb{R}^m$. -/
theorem dualProgram_zero_apply (F : Bifun (Rn m) (Rn n)) (v : Rn m) :
    dualProgram F 0 v = ⨅ u : Rn m, (((pairing m u v : ℝ) : EReal) + infBifun F u) :=
  convexAdjointBifun_zero_apply (pairing m) (pairing n) F v

/-- The definition of a normal program in [rockafellar1970convex]: $(P)$ is **normal** if and only
if $(\operatorname{cl}(\inf F))(0) = (\inf F)(0)$. This unfolds `ConvexAnalysis.Normal`. -/
theorem normal_iff_convexCl_infBifun_zero (F : Bifun (Rn m) (Rn n)) :
    Normal F ↔ convexCl (infBifun F) 0 = infBifun F 0 := Iff.rfl

/-- Normality of the dual program: a concave bifunction $G$ from $\mathbb{R}^n$ to $\mathbb{R}^m$ is
normal if and only if $(\operatorname{cl}(\sup G))(0) = (\sup G)(0)$, where $\operatorname{cl}$
is the concave closure. This unfolds `ConvexAnalysis.ConcaveNormal`. -/
theorem concaveNormal_iff_concaveCl_supBifun_zero (G : Bifun (Rn n) (Rn m)) :
    ConcaveNormal G ↔ concaveCl (supBifun G) 0 = supBifun G 0 := Iff.rfl

/-! ### Theorem 30.1 -/

/-- **Theorem 30.1** of [rockafellar1970convex], concavity. For every bifunction $F$ from
$\mathbb{R}^m$ to $\mathbb{R}^n$, the adjoint $F^*$ is a concave bifunction from $\mathbb{R}^n$
to $\mathbb{R}^m$.

No hypothesis on $F$ is needed. -/
theorem theorem_30_1_concave (F : Bifun (Rn m) (Rn n)) : ConcaveBifun (dualProgram F) :=
  concaveBifun_convexAdjointBifun (pairing m) (pairing n) F

/-- **Theorem 30.1** of [rockafellar1970convex], closedness. For every bifunction $F$ from
$\mathbb{R}^m$ to $\mathbb{R}^n$, the adjoint $F^*$ is a closed concave bifunction: its graph
function equals its concave closure.

No hypothesis on $F$ is needed. -/
theorem theorem_30_1_closed (F : Bifun (Rn m) (Rn n)) :
    ClosedConcave (graphFn (dualProgram F)) :=
  closedConcave_graphFn_convexAdjointBifun (Bu := pairing m) (Bx := pairing n) (F := F)

/-- **Theorem 30.1** of [rockafellar1970convex], properness. Let $F$ be a closed convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then $F^*$ is proper if and only if $F$ is proper. -/
theorem theorem_30_1_proper (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    ProperConcave (graphFn (dualProgram F)) ↔ ProperConvex (graphFn F) :=
  properConcave_graphFn_convexAdjointBifun_iff (Bu := pairing m) (Bx := pairing n) hF hcl

/-- **Theorem 30.1** of [rockafellar1970convex], biadjoint. Let $F$ be a convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. Then $F^{**} = \operatorname{cl} F$.

The second adjoint $F^{**}$ is `ConvexAnalysis.concaveAdjointBifun` applied to $F^*$, and
$\operatorname{cl} F$ is `ConvexAnalysis.convexClBifun F`, the bifunction whose graph function
is the closure of the graph function of $F$. -/
theorem theorem_30_1_biadjoint (hF : ConvexBifun F) :
    concaveAdjointBifun (pairing m) (pairing n) (dualProgram F) = convexClBifun F :=
  concaveAdjointBifun_convexAdjointBifun_eq_convexClBifun hF

/-- **Theorem 30.1** of [rockafellar1970convex], biadjoint of a closed bifunction. If $F$ is a
closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, then $F^{**} = F$. This is why
the program dual to $(P^*)$ is $(P)$ again. -/
theorem theorem_30_1_biadjoint_closed (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    concaveAdjointBifun (pairing m) (pairing n) (dualProgram F) = F :=
  concaveAdjointBifun_convexAdjointBifun_eq_self hF hcl

/-- **Theorem 30.1** of [rockafellar1970convex], injectivity of the adjoint. Let $F_1$ and $F_2$ be
closed convex bifunctions from $\mathbb{R}^m$ to $\mathbb{R}^n$. If $F_1^* = F_2^*$, then
$F_1 = F_2$.

Together with `Rockafellar.theorem_30_1_surjective` this is the statement of the book that the
adjoint operation is a one-to-one correspondence between the closed proper convex and the closed
proper concave bifunctions. -/
theorem theorem_30_1_injective {F₁ F₂ : Bifun (Rn m) (Rn n)} (hF₁ : ConvexBifun F₁)
    (hcl₁ : ClosedConvexBifun F₁) (hF₂ : ConvexBifun F₂) (hcl₂ : ClosedConvexBifun F₂)
    (h : dualProgram F₁ = dualProgram F₂) : F₁ = F₂ := by
  rw [← theorem_30_1_biadjoint_closed hF₁ hcl₁, ← theorem_30_1_biadjoint_closed hF₂ hcl₂, h]

/-- **Theorem 30.1** of [rockafellar1970convex], surjectivity of the adjoint. Let $G$ be a closed
proper concave bifunction from $\mathbb{R}^n$ to $\mathbb{R}^m$. Then there is a closed proper
convex bifunction $F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$ with $F^* = G$.

The bifunction $F$ is the lower adjoint of $G$, `ConvexAnalysis.lowerAdjointBifun` applied to
the inverse of $G$. -/
theorem theorem_30_1_surjective {G : Bifun (Rn n) (Rn m)} (hG : ConcaveBifun G)
    (hclG : ClosedConcave (graphFn G)) (hpG : ProperConcave (graphFn G)) :
    ∃ F : Bifun (Rn m) (Rn n),
      ConvexBifun F ∧ ClosedConvexBifun F ∧ ProperConvex (graphFn F) ∧ dualProgram F = G := by
  have hconv : ConvexBifun (inverseBifun G) := convexBifun_inverseBifun hG
  have hclosed : ClosedConvexBifun (inverseBifun G) := closedConvexBifun_inverseBifun hclG
  have hdual : dualProgram (lowerAdjointBifun (pairing m) (pairing n) (inverseBifun G)) = G := by
    have h :=
        convexAdjointBifun_flip_lowerAdjointBifun (Bu := pairing m) (Bx := pairing n) hconv hclosed
    simp only [flip_pairing, inverseBifun_inverseBifun] at h
    exact h
  have hconvF : ConvexBifun (lowerAdjointBifun (pairing m) (pairing n) (inverseBifun G)) :=
    convexBifun_lowerAdjointBifun (pairing m) (pairing n) (inverseBifun G)
  have hclF : ClosedConvexBifun (lowerAdjointBifun (pairing m) (pairing n) (inverseBifun G)) :=
    closedConvexBifun_lowerAdjointBifun
  refine ⟨lowerAdjointBifun (pairing m) (pairing n) (inverseBifun G), hconvF, hclF, ?_, hdual⟩
  exact (theorem_30_1_proper hconvF hclF).1 (by rw [hdual]; exact hpG)

/-- **Theorem 30.1** of [rockafellar1970convex], polyhedrality. If $F$ is a polyhedral convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, then $F^*$ is a polyhedral concave bifunction.

The book derives this from Theorem 19.2. Neither properness nor closedness of $F$ is needed. -/
theorem theorem_30_1_polyhedral (hF : PolyhedralBifun F) :
    ConcavePolyhedralBifun (dualProgram F) :=
  polyhedralFn_neg_graphFn_convexAdjointBifun (pairing m) (pairing n) hF

/-!
### The adjoint of an indicator bifunction

The first example of the adjoint operation in [rockafellar1970convex], and the one that justifies
its name: "the adjoint operation for bifunctions can rightly be viewed as a generalization of the
adjoint operation for linear transformations". The bifunction `Rockafellar.linearIndicatorBifun` is
defined in Section 29.
-/

/-- The indicator bifunction of a linear map $A : \mathbb{R}^m \to \mathbb{R}^n$ takes the value $0$
at $(u, Au)$. -/
@[simp] theorem linearIndicatorBifun_self (A : Rn m →ₗ[ℝ] Rn n) (u : Rn m) :
    linearIndicatorBifun A u (A u) = 0 := by
  rw [linearIndicatorBifun_apply]
  exact indicatorFn_of_mem (Set.mem_singleton _)

/-- The indicator bifunction of a linear map $A : \mathbb{R}^m \to \mathbb{R}^n$ takes the value
$+\infty$ at $(u, x)$ when $x \neq Au$. -/
theorem linearIndicatorBifun_of_ne (A : Rn m →ₗ[ℝ] Rn n) {u : Rn m} {x : Rn n} (h : x ≠ A u) :
    linearIndicatorBifun A u x = ⊤ := by
  rw [linearIndicatorBifun_apply]
  exact indicatorFn_of_notMem (by simpa using h)

private theorem iInf_linearIndicatorBifun_slice (A : Rn m →ₗ[ℝ] Rn n) (u v : Rn m) (y : Rn n) :
    (⨅ x : Rn n, (linearIndicatorBifun A u x + ((pairing m u v - pairing n x y : ℝ) : EReal)))
      = ((pairing m u (v - LinearMap.adjoint A y) : ℝ) : EReal) := by
  have hval : (pairing m u v - pairing n (A u) y : ℝ)
      = pairing m u (v - LinearMap.adjoint A y) := by
    rw [map_sub, isAdjointPair_adjoint A u y]
  refine le_antisymm (le_trans (iInf_le _ (A u)) (le_of_eq ?_)) (le_iInf fun x => ?_)
  · rw [linearIndicatorBifun_self, zero_add, hval]
  · by_cases hx : x = A u
    · subst hx
      rw [linearIndicatorBifun_self, zero_add, hval]
    · rw [linearIndicatorBifun_of_ne A hx, EReal.top_add_coe]
      exact le_top

private theorem iInf_pairing_coe (w : Rn m) :
    (⨅ u : Rn m, ((pairing m u w : ℝ) : EReal)) = ⨆ _ : w = 0, (0 : EReal) := by
  by_cases hw : w = 0
  · rw [iSup_pos hw, hw]
    simp
  · rw [iSup_neg hw]
    refine iInf_eq_bot.2 fun b hb => ?_
    obtain ⟨c, -, hcb⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    have hpos : 0 < pairing m w w := by
      rw [pairing_apply]
      exact real_inner_self_pos.2 hw
    refine ⟨((c - 1) / (pairing m w w)) • w, ?_⟩
    have hval : pairing m (((c - 1) / (pairing m w w)) • w) w = c - 1 := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hpos.ne']
    rw [hval]
    refine lt_trans ?_ hcb
    exact_mod_cast (by linarith : c - 1 < c)

/-- **Section 30** of [rockafellar1970convex], the adjoint of the indicator bifunction of a linear
map. Let $A : \mathbb{R}^m \to \mathbb{R}^n$ be linear and let $F$ be its convex indicator
bifunction, $(Fu)(x) = \delta(x \mid Au)$. Then $F^*$ is the concave indicator bifunction of the
adjoint map $A^*$:
$$(F^* x^*)(u^*) = -\delta(u^* \mid A^* x^*),$$
which is $0$ if $u^* = A^* x^*$ and $-\infty$ otherwise.

The map $A^*$ is `LinearMap.adjoint A`. On $\mathbb{R}^n$ the adjoint is canonical, so it is not
an argument. -/
theorem dualProgram_linearIndicatorBifun (A : Rn m →ₗ[ℝ] Rn n) (y : Rn n) (v : Rn m) :
    dualProgram (linearIndicatorBifun A) y v = ⨆ _ : v = LinearMap.adjoint A y, (0 : EReal) := by
  rw [dualProgram_apply, iInf_prod]
  rw [iInf_congr fun u : Rn m => iInf_linearIndicatorBifun_slice A u v y, iInf_pairing_coe]
  by_cases h : v = LinearMap.adjoint A y
  · rw [iSup_pos h, iSup_pos (sub_eq_zero.2 h)]
  · rw [iSup_neg h, iSup_neg (fun hc => h (sub_eq_zero.1 hc))]

/-! ### Theorem 30.2 -/

/-- **Theorem 30.2** of [rockafellar1970convex], first formula. For every bifunction $F$ from
$\mathbb{R}^m$ to $\mathbb{R}^n$,
$$(-\inf F)^* = F^* 0,$$
where $(-\inf F)^*$ is the concave conjugate $u^* \mapsto \inf_u \{\langle u, u^* \rangle +
(\inf F)(u)\}$ of the concave function $-\inf F$.

The conjugate is `ConvexAnalysis.concaveConj`, not `ConvexAnalysis.convexConj`: for a concave
$g$ the concave conjugate $g^*$ is not $-(-g)^*$. -/
theorem theorem_30_2_first (F : Bifun (Rn m) (Rn n)) :
    concaveConj (pairing m) (fun u => -(infBifun F u)) = dualProgram F 0 :=
  (convexAdjointBifun_zero_eq_concaveConj (pairing m) (pairing n) F).symm

/-- **Theorem 30.2** of [rockafellar1970convex], second formula. Let $F$ be a convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. Then the concave conjugate of the objective function of
$(P^*)$ is
$$(F^* 0)^* = -\operatorname{cl}(\inf F).$$
-/
theorem theorem_30_2_second (hF : ConvexBifun F) :
    concaveConj (pairing m) (dualProgram F 0) = fun u => -(convexCl (infBifun F) u) := by
  have hconc : ConcaveFn (fun u => -(infBifun F u)) :=
    concaveFn_iff_convexFn_neg.2 (by simpa using convexFn_infBifun hF)
  have hbi := concaveBiconj_eq_concaveCl (B := pairing m) hconc
  rw [← theorem_30_2_first F]
  have hflip : concaveConj (pairing m) (concaveConj (pairing m) (fun u => -(infBifun F u)))
      = concaveBiconj (pairing m) (fun u => -(infBifun F u)) := by
    rw [concaveBiconj, flip_pairing]
  rw [hflip, hbi]
  funext u
  rw [concaveCl_apply]
  simp only [neg_neg]

/-- **Theorem 30.2** of [rockafellar1970convex], third formula. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then the objective function of $(P)$ is the
convex conjugate of the convex function $-\sup F^*$:
$$(-\sup F^*)^* = F0.$$
-/
theorem theorem_30_2_third (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    convexConj (pairing n) (fun y => -(supBifun (dualProgram F) y)) = F 0 := by
  have h :=
      concaveAdjointBifun_convexAdjointBifun_eq_self (Bu := pairing m) (Bx := pairing n) hF hcl
  have h2 := concaveAdjointBifun_zero_eq_convexConj (pairing m) (pairing n) (dualProgram F)
  rw [flip_pairing] at h2
  rw [← h2, h]

/-- **Theorem 30.2** of [rockafellar1970convex], fourth formula. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then
$$(F0)^* = -\operatorname{cl}(\sup F^*),$$
where $\operatorname{cl}$ is the concave closure. -/
theorem theorem_30_2_fourth (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    convexConj (pairing n) (F 0) = fun y => -(concaveCl (supBifun (dualProgram F)) y) := by
  have hconv : ConvexFn (fun y => -(supBifun (dualProgram F) y)) :=
    convexFn_neg_supBifun (concaveBifun_convexAdjointBifun (pairing m) (pairing n) F)
  have hbi := convexBiconj_eq_convexCl (B := (pairing n).flip) hconv
  rw [← theorem_30_2_third hF hcl]
  have hflip :
      convexConj (pairing n) (convexConj (pairing n) (fun y => -(supBifun (dualProgram F) y)))
      = convexBiconj (pairing n).flip (fun y => -(supBifun (dualProgram F) y)) := by
    rw [convexBiconj, flip_pairing, flip_pairing]
  rw [hflip, hbi]
  funext y
  rw [concaveCl_apply]
  simp only [neg_neg]

/-!
### The Lagrangian form of the two objective functions

The Lagrangian of $(P)$ is $L(u^*, x) = \inf_u \{\langle u, u^* \rangle + (Fu)(x)\}$, which is
`ConvexAnalysis.lagrangian (Rockafellar.pairing m) F`.
-/

/-- **Section 30** of [rockafellar1970convex], the remark after Theorem 30.2. For every bifunction
$F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, the objective function of $(P^*)$ is the infimum of
the Lagrangian of $(P)$ over the primal variable:
$$(F^* 0)(u^*) = \inf_x L(u^*, x).$$
-/
theorem dualProgram_zero_eq_iInf_lagrangian (F : Bifun (Rn m) (Rn n)) (v : Rn m) :
    dualProgram F 0 v = ⨅ x : Rn n, lagrangian (pairing m) F v x :=
  (iInf_lagrangian_eq_convexAdjointBifun_zero (Bu := pairing m) (pairing n)).symm

/-- **Section 30** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. Then the objective function of $(P)$ is the supremum of the
Lagrangian over the dual variable:
$$(F0)(x) = \sup_{u^*} L(u^*, x).$$
-/
theorem objective_eq_iSup_lagrangian (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (x : Rn n) :
    F 0 x = ⨆ v : Rn m, lagrangian (pairing m) F v x :=
  (iSup_lagrangian_eq (Bu := pairing m) hF hcl).symm

/-- **Section 30** of [rockafellar1970convex]. For every bifunction $F$ from $\mathbb{R}^m$ to
$\mathbb{R}^n$, the optimal value of $(P^*)$ is
$$\sup F^* 0 = \sup_{u^*} \inf_x L(u^*, x).$$

The right side is `ConvexAnalysis.maximin` of `ConvexAnalysis.saddleLagrangian`, the Lagrangian
as a function on $\mathbb{R}^m \times \mathbb{R}^n$. -/
theorem supBifun_dualProgram_eq_maximin (F : Bifun (Rn m) (Rn n)) :
    supBifun (dualProgram F) 0 = maximin (saddleLagrangian (pairing m) F) := by
  rw [supBifun_apply, maximin_apply]
  exact iSup_congr fun v => dualProgram_zero_eq_iInf_lagrangian F v

/-- **Section 30** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. Then the optimal value of $(P)$ is
$$\inf F0 = \inf_x \sup_{u^*} L(u^*, x).$$

Together with `Rockafellar.supBifun_dualProgram_eq_maximin`, this shows that normality is the
existence of a saddle-value of $L$, which Section 36 takes up. The right side is
`ConvexAnalysis.minimax` of `ConvexAnalysis.saddleLagrangian (Rockafellar.pairing m) F`. -/
theorem infBifun_eq_minimax (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    infBifun F 0 = minimax (saddleLagrangian (pairing m) F) := by
  rw [infBifun_apply, minimax_apply]
  exact iInf_congr fun x => objective_eq_iSup_lagrangian hF hcl x

/-! ### Corollary 30.2.1 -/

/-- **Corollary 30.2.1** of [rockafellar1970convex], first half. Let $F$ be a convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. Then $(P^*)$ is inconsistent if and only if
$(\inf F)(u) = -\infty$ for some $u \in \mathbb{R}^m$.

**Generalization.** The book assumes $F$ closed for the whole corollary. This half does not need
it, because the adjoint does not distinguish $F$ from $\operatorname{cl} F$. -/
theorem corollary_30_2_1_dual (hF : ConvexBifun F) :
    ¬ ConcaveConsistent (dualProgram F) ↔ ∃ u : Rn m, infBifun F u = ⊥ :=
  not_concaveConsistent_convexAdjointBifun_iff (Bu := pairing m) (pairing n) hF

/-- **Corollary 30.2.1** of [rockafellar1970convex], first half, in positive form. Let $F$ be a
convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then $(P^*)$ is consistent if and only
if $(\inf F)(u) \neq -\infty$ for every $u \in \mathbb{R}^m$.

**Generalization.** The book assumes $F$ closed. The statement does not, as in
`Rockafellar.corollary_30_2_1_dual`. -/
theorem corollary_30_2_1_dual' (hF : ConvexBifun F) :
    ConcaveConsistent (dualProgram F) ↔ ∀ u : Rn m, infBifun F u ≠ ⊥ :=
  concaveConsistent_convexAdjointBifun_iff (Bu := pairing m) (pairing n) hF

/-- **Corollary 30.2.1** of [rockafellar1970convex], second half. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then $(P)$ is inconsistent if and only if
$(\sup F^*)(x^*) = +\infty$ for some $x^* \in \mathbb{R}^n$.

This half needs $F$ closed: it is the first half applied to the dual pair, and $F^{**} = F$
identifies the objective function of $(P)$. -/
theorem corollary_30_2_1_primal (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    ¬ Consistent F ↔ ∃ y : Rn n, supBifun (dualProgram F) y = ⊤ :=
  not_consistent_iff_exists_supBifun_eq_top (Bu := pairing m) (Bx := pairing n) hF hcl

/-- **Corollary 30.2.1** of [rockafellar1970convex], second half, in positive form. Let $F$ be a
closed convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then $(P)$ is consistent if and
only if $(\sup F^*)(x^*) \neq +\infty$ for every $x^* \in \mathbb{R}^n$. -/
theorem corollary_30_2_1_primal' (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    Consistent F ↔ ∀ y : Rn n, supBifun (dualProgram F) y ≠ ⊤ :=
  consistent_iff_forall_supBifun_ne_top (Bu := pairing m) (Bx := pairing n) hF hcl

/-! ### Corollary 30.2.2 -/

/-- **Corollary 30.2.2** of [rockafellar1970convex], first formula. Let $F$ be a convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then
$$(\operatorname{cl}(\inf F))(0) = \sup F^* 0.$$

**Generalization.** The book assumes $F$ closed. The formula does not need it: it is the
Fenchel–Moreau theorem for $\inf F$, and $F^*$ does not distinguish $F$ from
$\operatorname{cl} F$. -/
theorem corollary_30_2_2_first (hF : ConvexBifun F) :
    convexCl (infBifun F) 0 = supBifun (dualProgram F) 0 := by
  rw [supBifun_apply]
  exact convexCl_infBifun_zero_eq_iSup_convexAdjointBifun (Bu := pairing m) (pairing n) hF

/-- **Corollary 30.2.2** of [rockafellar1970convex], second formula. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then
$$(\operatorname{cl}(\sup F^*))(0) = \inf F0,$$
where $\operatorname{cl}$ is the concave closure.

Closedness of $F$ is used to turn $F^{**}$ back into $F$. -/
theorem corollary_30_2_2_second (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    concaveCl (supBifun (dualProgram F)) 0 = infBifun F 0 :=
  concaveCl_supBifun_convexAdjointBifun_zero_eq (Bu := pairing m) (Bx := pairing n) hF hcl

/-- **Corollary 30.2.2** of [rockafellar1970convex], weak duality. For every bifunction $F$ from
$\mathbb{R}^m$ to $\mathbb{R}^n$,
$$\sup F^* 0 \le \inf F0.$$

No hypothesis is needed: every value $(F^* 0)(u^*) = \inf_u \{\langle u, u^* \rangle + (\inf
F)(u)\}$ is at most the value of the bracket at $u = 0$. -/
theorem corollary_30_2_2_weak (F : Bifun (Rn m) (Rn n)) :
    supBifun (dualProgram F) 0 ≤ infBifun F 0 := by
  rw [supBifun_apply]
  exact iSup_convexAdjointBifun_zero_le (pairing m) (pairing n) F

/-! ### Corollary 30.2.3 -/

/-- **Corollary 30.2.3** of [rockafellar1970convex], first formula. Let $F$ be a convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$, and assume that $(P)$ or $(P^*)$ is consistent. Then
$$\liminf_{u \to 0} (\inf F)(u) = \sup F^* 0.$$

**Generalization.** The book assumes $F$ closed. The statement does not.

The lower limit is `Filter.liminf` along the neighbourhood filter of $0$, which includes
$u = 0$. The excluded case is the one of the book: the two sides differ only when
$\operatorname{cl}(\inf F)$ is $-\infty$, so that $(P^*)$ is inconsistent, and the lower limit
is $+\infty$, so that $(P)$ is inconsistent. -/
theorem corollary_30_2_3_first (hF : ConvexBifun F)
    (h : Consistent F ∨ ConcaveConsistent (dualProgram F)) :
    Filter.liminf (infBifun F) (𝓝 (0 : Rn m)) = supBifun (dualProgram F) 0 := by
  rw [supBifun_apply]
  exact liminf_infBifun_eq_iSup_convexAdjointBifun (Bu := pairing m) (pairing n) hF h

/-- **Corollary 30.2.3** of [rockafellar1970convex], second formula. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, and assume that $(P)$ or $(P^*)$ is
consistent. Then
$$\limsup_{x^* \to 0} (\sup F^*)(x^*) = \inf F0.$$

The upper limit is `Filter.limsup` along the neighbourhood filter of $0$, which includes
$x^* = 0$. -/
theorem corollary_30_2_3_second (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (h : Consistent F ∨ ConcaveConsistent (dualProgram F)) :
    Filter.limsup (supBifun (dualProgram F)) (𝓝 (0 : Rn n)) = infBifun F 0 :=
  limsup_supBifun_convexAdjointBifun_eq (Bu := pairing m) (Bx := pairing n) hF hcl h

/-! ### Theorem 30.3 -/

/-- **Theorem 30.3** of [rockafellar1970convex], equivalence of (a) and (c). Let $F$ be a convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then $(P)$ is normal if and only if
$\inf F0 = \sup F^* 0$.

**Generalization.** The book assumes $F$ closed. The proof uses only the first formula of
Corollary 30.2.2, which does not need it. -/
theorem theorem_30_3_a_iff_c (hF : ConvexBifun F) :
    Normal F ↔ infBifun F 0 = supBifun (dualProgram F) 0 := by
  rw [normal_iff_iSup_convexAdjointBifun_eq (Bu := pairing m) (pairing n) hF, supBifun_apply]
  exact eq_comm

/-- **Theorem 30.3** of [rockafellar1970convex], equivalence of (b) and (c). Let $F$ be a closed
convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then $(P^*)$ is normal if and only if
$\inf F0 = \sup F^* 0$. -/
theorem theorem_30_3_b_iff_c (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    ConcaveNormal (dualProgram F) ↔ infBifun F 0 = supBifun (dualProgram F) 0 := by
  rw [concaveNormal_convexAdjointBifun_iff (Bu := pairing m) (Bx := pairing n) hF hcl,
      supBifun_apply]
  exact eq_comm

/-- **Theorem 30.3** of [rockafellar1970convex], equivalence of (a) and (b). Let $F$ be a closed
convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. Then $(P)$ is normal if and only if
$(P^*)$ is normal. -/
theorem theorem_30_3_a_iff_b (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    Normal F ↔ ConcaveNormal (dualProgram F) :=
  normal_iff_concaveNormal_convexAdjointBifun (Bu := pairing m) (Bx := pairing n) hF hcl

/-- **Theorem 30.3** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. The following are equivalent:

(a) $(P)$ is normal;

(b) $(P^*)$ is normal;

(c) $\inf F0 = \sup F^* 0$. -/
theorem theorem_30_3 (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) :
    [Normal F, ConcaveNormal (dualProgram F),
      infBifun F 0 = supBifun (dualProgram F) 0].TFAE := by
  tfae_have 1 ↔ 2 := theorem_30_3_a_iff_b hF hcl
  tfae_have 1 ↔ 3 := theorem_30_3_a_iff_c hF
  tfae_finish

/-!
### Theorem 30.4

The book proves clauses (a), (c) and (e), says "Dually, (b), (d) and (f) imply that normality
holds", gives one sentence for (g), and treats (h), (i) and (j) as "special cases" and as "of course
… contained in" (g) and (h). Each declaration below says what the book gives for its clause.
-/

/-- **Theorem 30.4(a)** of [rockafellar1970convex]. Let $F$ be a convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. If $(P)$ is strongly consistent, that is,
$0 \in \operatorname{ri}(\operatorname{dom} F)$, then $(P)$ is normal.

The book proves this clause, by the argument used here: $0 \in
\operatorname{ri}(\operatorname{dom}(\inf F))$ by Theorem 29.1, and a convex function agrees
with its closure on the relative interior of its effective domain. -/
theorem theorem_30_4_a (hs : StronglyConsistent F) (hF : ConvexBifun F) : Normal F :=
  StronglyConsistent.normal hs hF

/-- **Theorem 30.4(a)** of [rockafellar1970convex], the strict form in parentheses. Let $F$ be a
convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. If $(P)$ is strictly consistent, that
is, $0 \in \operatorname{int}(\operatorname{dom} F)$, then $(P)$ is normal. -/
theorem theorem_30_4_a' (hs : StrictlyConsistent F) (hF : ConvexBifun F) : Normal F :=
  StrictlyConsistent.normal hs hF

/-- **Theorem 30.4(b)** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. If $(P^*)$ is strongly consistent, that is, $0 \in
\operatorname{ri}(\operatorname{dom} F^*)$, then $(P)$ is normal.

The book does not argue this clause: "Dually, (b), (d) and (f) imply that normality holds". The
proof here is the dual of (a) followed by the equivalence of (a) and (b) in Theorem 30.3. -/
theorem theorem_30_4_b (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hs : ConcaveStronglyConsistent (dualProgram F)) : Normal F :=
  normal_of_concaveStronglyConsistent_convexAdjointBifun (Bu := pairing m)
      (Bx := pairing n) hF hcl hs

/-- **Theorem 30.4(c)** of [rockafellar1970convex]. Let $F$ be a convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. If $(P)$ has a Kuhn–Tucker vector, then $(P)$ is normal.

A Kuhn–Tucker vector is a $u^*$ with $\inf_u \{\langle u, u^* \rangle + (\inf F)(u)\} = (\inf
F)(0)$, and by definition the optimal value $(\inf F)(0)$ is finite. The book proves this clause
from Theorem 29.1 and Corollary 23.5.2. The proof here uses weak duality instead, which fixes
the optimal value of $(P^*)$. -/
theorem theorem_30_4_c (hF : ConvexBifun F) (h : (KuhnTucker (pairing m) F).Nonempty) :
    Normal F :=
  normal_of_kuhnTucker_nonempty (Bu := pairing m) (pairing n) hF h

/-- **Theorem 30.4(d)** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. If $(P^*)$ has a Kuhn–Tucker vector, then $(P)$ is normal.

The book does not argue this clause. -/
theorem theorem_30_4_d (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (h : (ConcaveKuhnTucker (pairing n) (dualProgram F)).Nonempty) : Normal F := by
  refine normal_of_concaveKuhnTucker_convexAdjointBifun_nonempty (Bu := pairing m) (Bx := pairing n)
    hF hcl ?_
  rwa [flip_pairing]

/-- **Theorem 30.4(e)** of [rockafellar1970convex]. Let $F$ be a polyhedral convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. If $(P)$ is consistent, then $(P)$ is normal.

The book proves this clause: by Theorem 29.2 the function $\inf F$ is polyhedral, and a
polyhedral convex function agrees with its closure on its effective domain. -/
theorem theorem_30_4_e (hF : PolyhedralBifun F) (hc : Consistent F) : Normal F :=
  PolyhedralBifun.normal hF hc

/-- **Theorem 30.4(f)** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. If $F^*$ is polyhedral and $(P^*)$ is consistent, then $(P)$
is normal.

The book does not argue this clause. By `Rockafellar.theorem_30_1_polyhedral`, $F^*$ is
polyhedral when $F$ is, and `Rockafellar.gale_kuhn_tucker_duality` uses the clause in this way. -/
theorem theorem_30_4_f (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hG : ConcavePolyhedralBifun (dualProgram F)) (hc : ConcaveConsistent (dualProgram F)) :
    Normal F :=
  normal_of_concavePolyhedral_convexAdjointBifun (Bu := pairing m) (Bx := pairing n) hF hcl hG hc

/-- **Theorem 30.4(g)** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. If for some $\alpha \in \mathbb{R}$ the level set
$\{x \mid (F0)(x) \le \alpha\}$ is non-empty and bounded, then $(P)$ is normal.

The book gives one sentence: "Condition (g) is equivalent by Theorem 27.1(d) to having $0 \in
\operatorname{int}(\operatorname{dom}(F0)^*)$, i.e. $(P^*)$ strictly consistent." The step after
"i.e." is not immediate, because strict consistency of $(P^*)$ is an interior condition on the
effective domain of $F^*$, which involves all perturbations. It holds because all slices $Fu$ of
a closed convex bifunction have the same recession function, so the two sets are equal. No
properness of $F$ is assumed: a closed convex bifunction that takes the value $-\infty$ has
$\inf F0 = -\infty$ and is normal. -/
theorem theorem_30_4_g (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (h : ∃ α : ℝ, {x : Rn n | F 0 x ≤ (α : EReal)}.Nonempty ∧
      Bornology.IsBounded {x : Rn n | F 0 x ≤ (α : EReal)}) : Normal F :=
  normal_of_exists_setOf_le (Bu := pairing m) (Bx := pairing n) hF hcl h

/-- **Theorem 30.4(h)** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$. If for some $\alpha \in \mathbb{R}$ the upper level set
$\{u^* \mid (F^* 0)(u^*) \ge \alpha\}$ is non-empty and bounded, then $(P)$ is normal.

The book does not argue this clause. The proof here differs from the book's approach: $-F^*$ is
a closed convex bifunction for every $F$, so clause (g) applies to it, and Theorem 30.3 carries
the conclusion back to $(P)$. -/
theorem theorem_30_4_h (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (h : ∃ α : ℝ, {v : Rn m | (α : EReal) ≤ dualProgram F 0 v}.Nonempty ∧
      Bornology.IsBounded {v : Rn m | (α : EReal) ≤ dualProgram F 0 v}) : Normal F :=
  normal_of_exists_setOf_ge_convexAdjointBifun (Bu := pairing m) (Bx := pairing n) hF hcl h

/-- **Theorem 30.4(i)** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$ such that $F0$ is proper. If the set of optimal solutions to
$(P)$ is non-empty and bounded, then $(P)$ is normal. In particular this holds if $(P)$ has
exactly one optimal solution.

**Correction.** The book says that (i) is contained in (g). The containment needs $F0$ to be
proper: if $F0 \equiv +\infty$ on $\mathbb{R}^0$, the set of optimal solutions is $\{0\}$, which
is non-empty and bounded, but no level set $\{x \mid (F0)(x) \le \alpha\}$ is non-empty. The
statement therefore assumes that $F0$ is proper. Then the set of optimal solutions is the level
set of $F0$ at its minimum value, and (g) applies. -/
theorem theorem_30_4_i (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hp : ProperConvex (F 0))
    (hne : (argmin (F 0)).Nonempty) (hbd : Bornology.IsBounded (argmin (F 0))) : Normal F :=
  normal_of_argmin_nonempty_and_isBounded (Bu := pairing m) (Bx := pairing n) hF hcl hp hne hbd

/-- **Theorem 30.4(j)** of [rockafellar1970convex]. Let $F$ be a closed convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$ such that $F^* 0$ is a proper concave function. If the set of
optimal solutions to $(P^*)$ is non-empty and bounded, then $(P)$ is normal.

**Correction.** As in (i), the containment in (h) that the book asserts needs the dual objective
$F^* 0$ to be proper. The statement assumes it.

Properness of $F^* 0$ is stated as properness of the convex function
$u^* \mapsto -(F^* 0)(u^*)$. -/
theorem theorem_30_4_j (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hp : ProperConvex fun v => -(dualProgram F 0 v))
    (hne : (argmax (dualProgram F 0)).Nonempty)
    (hbd : Bornology.IsBounded (argmax (dualProgram F 0))) : Normal F :=
  normal_of_argmax_convexAdjointBifun_nonempty_and_isBounded (Bu := pairing m) (Bx := pairing n)
    hF hcl hp hne hbd

/-- The **Gale–Kuhn–Tucker duality theorem**, which [rockafellar1970convex] names in the text of
Section 30 without a number. Let $F$ be a closed polyhedral convex bifunction from
$\mathbb{R}^m$ to $\mathbb{R}^n$, and assume that $(P)$ or $(P^*)$ is consistent. Then
$\inf F0 = \sup F^* 0$.

The book applies the argument to a particular dual pair of linear programs: "these are
polyhedral convex programs, so it follows". The statement here has the generality of the
argument. Clause (e) of Theorem 30.4 covers a consistent $(P)$, and clause (f), with
`Rockafellar.theorem_30_1_polyhedral`, covers a consistent $(P^*)$. In the application of the
book closedness is automatic, because a proper polyhedral convex bifunction is closed. -/
theorem gale_kuhn_tucker_duality (hF : PolyhedralBifun F) (hcl : ClosedConvexBifun F)
    (h : Consistent F ∨ ConcaveConsistent (dualProgram F)) :
    infBifun F 0 = supBifun (dualProgram F) 0 := by
  refine (theorem_30_3_a_iff_c hF.convexBifun).1 ?_
  rcases h with hc | hc
  · exact theorem_30_4_e hF hc
  · exact theorem_30_4_f hF.convexBifun hcl (theorem_30_1_polyhedral hF) hc

/-! ### Theorem 30.5 -/

/-- **Theorem 30.5** of [rockafellar1970convex], first assertion. Let $F$ be a convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$ such that $(P)$ is normal and its optimal value $\inf F0$
is finite. Then $u^* \in \mathbb{R}^m$ is a Kuhn–Tucker vector for $(P)$ if and only if $u^*$ is
an optimal solution to $(P^*)$. -/
theorem theorem_30_5 (hF : ConvexBifun F) (hn : Normal F) (ht : infBifun F 0 ≠ ⊤)
    (hb : infBifun F 0 ≠ ⊥) (v : Rn m) :
    v ∈ KuhnTucker (pairing m) F ↔ v ∈ argmax (dualProgram F 0) := by
  rw [mem_kuhnTucker_iff_convexAdjointBifun_zero_eq_iSup (Bu := pairing m) (pairing n) hF hn ht hb,
    mem_argmax_iff_eq_iSup]

/-- **Theorem 30.5** of [rockafellar1970convex], second assertion. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ such that $(P)$ is normal and $\inf F0$ is
finite. Then $x \in \mathbb{R}^n$ is a Kuhn–Tucker vector for $(P^*)$ if and only if $x$ is an
optimal solution to $(P)$.

The book says only that "the proof of the dual assertion of the theorem is parallel". -/
theorem theorem_30_5_dual (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hn : Normal F)
    (ht : infBifun F 0 ≠ ⊤) (hb : infBifun F 0 ≠ ⊥) (x : Rn n) :
    x ∈ ConcaveKuhnTucker (pairing n) (dualProgram F) ↔ x ∈ argmin (F 0) := by
  have h :=
      mem_concaveKuhnTucker_convexAdjointBifun_iff_mem_argmin (Bu := pairing m) (Bx := pairing n)
    (x := x) hF hcl hn ht hb
  rw [flip_pairing] at h
  exact h

/-! ### Corollary 30.5.1 -/

/-- **Corollary 30.5.1** of [rockafellar1970convex], equivalence of (b) and (c). Let $F$ be a closed
convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ with Lagrangian $L$, and let
$\bar u^* \in \mathbb{R}^m$ and $\bar x \in \mathbb{R}^n$. Then $(\bar u^*, \bar x)$ is a
saddle-point of $L$ if and only if $(F0)(\bar x) \le (F^* 0)(\bar u^*)$. In that case weak
duality gives equality.

A saddle-point is `ConvexAnalysis.IsSaddlePoint` of `ConvexAnalysis.saddleLagrangian`: $L(u^*,
\bar x) \le L(\bar u^*, \bar x) \le L(\bar u^*, x)$ for all $u^*$ and $x$. -/
theorem corollary_30_5_1_b_iff_c (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (v : Rn m)
    (x : Rn n) :
    IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x) ↔ F 0 x ≤ dualProgram F 0 v :=
  isSaddlePoint_lagrangian_iff_le_convexAdjointBifun (Bu := pairing m) (pairing n) hF hcl

/-- **Corollary 30.5.1** of [rockafellar1970convex], equivalence of (a) and (b). Let $F$ be a closed
proper convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ with Lagrangian $L$, and let
$\bar u^* \in \mathbb{R}^m$ and $\bar x \in \mathbb{R}^n$. Then $(\bar u^*, \bar x)$ is a
saddle-point of $L$ if and only if $(P)$ is normal, $\bar x$ is an optimal solution to $(P)$ and
$\bar u^*$ is an optimal solution to $(P^*)$.

The book's proof is "immediate from Theorem 29.3": the existence of a Kuhn–Tucker vector implies
normality. -/
theorem corollary_30_5_1_a_iff_b (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (v : Rn m) (x : Rn n) :
    IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x)
      ↔ Normal F ∧ x ∈ argmin (F 0) ∧ v ∈ argmax (dualProgram F 0) := by
  rw [isSaddlePoint_lagrangian_iff_normal_and_optimal (Bu := pairing m) (pairing n) hF hcl hpr,
    mem_argmax_iff_eq_iSup]

/-- **Corollary 30.5.1** of [rockafellar1970convex], equivalence of (a) and (c). Let $F$ be a closed
proper convex bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$, and let
$\bar u^* \in \mathbb{R}^m$ and $\bar x \in \mathbb{R}^n$. Then $(P)$ is normal, $\bar x$ is an
optimal solution to $(P)$ and $\bar u^*$ is an optimal solution to $(P^*)$, if and only if
$(F0)(\bar x) \le (F^* 0)(\bar u^*)$. -/
theorem corollary_30_5_1_a_iff_c (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F)) (v : Rn m) (x : Rn n) :
    (Normal F ∧ x ∈ argmin (F 0) ∧ v ∈ argmax (dualProgram F 0))
      ↔ F 0 x ≤ dualProgram F 0 v :=
  (corollary_30_5_1_a_iff_b hF hcl hpr v x).symm.trans (corollary_30_5_1_b_iff_c hF hcl v x)

/-- **Corollary 30.5.1** of [rockafellar1970convex]. Let $F$ be a closed proper convex bifunction
from $\mathbb{R}^m$ to $\mathbb{R}^n$ with Lagrangian $L$, and let $\bar u^* \in \mathbb{R}^m$
and $\bar x \in \mathbb{R}^n$. The following are equivalent:

(a) $(P)$ is normal, $\bar x$ is an optimal solution to $(P)$, and $\bar u^*$ is an optimal
solution to $(P^*)$;

(b) $(\bar u^*, \bar x)$ is a saddle-point of $L$;

(c) $(F0)(\bar x) \le (F^* 0)(\bar u^*)$.

The saddle-point is `ConvexAnalysis.IsSaddlePoint` of `ConvexAnalysis.saddleLagrangian` at
$(\bar u^*, \bar x)$. -/
theorem corollary_30_5_1 (hF : ConvexBifun F) (hcl : ClosedConvexBifun F)
    (hpr : ProperConvex (graphFn F))
    (v : Rn m) (x : Rn n) :
    [Normal F ∧ x ∈ argmin (F 0) ∧ v ∈ argmax (dualProgram F 0),
      IsSaddlePoint (saddleLagrangian (pairing m) F) (v, x),
      F 0 x ≤ dualProgram F 0 v].TFAE := by
  tfae_have 1 ↔ 2 := (corollary_30_5_1_a_iff_b hF hcl hpr v x).symm
  tfae_have 2 ↔ 3 := corollary_30_5_1_b_iff_c hF hcl v x
  tfae_finish

/-- **Corollary 30.5.1** of [rockafellar1970convex], the remark in parentheses. For every bifunction
$F$ from $\mathbb{R}^m$ to $\mathbb{R}^n$, if $(F0)(\bar x) \le (F^* 0)(\bar u^*)$, then
$(F0)(\bar x) = (F^* 0)(\bar u^*)$.

This is weak duality (Corollary 30.2.2) in the other direction. -/
theorem corollary_30_5_1_eq (F : Bifun (Rn m) (Rn n)) (v : Rn m) (x : Rn n)
    (h : F 0 x ≤ dualProgram F 0 v) : F 0 x = dualProgram F 0 v :=
  le_antisymm h ((convexAdjointBifun_zero_le (pairing m) (pairing n) F v).trans
    (iInf_le (fun z => F 0 z) x))

/-! ### Corollary 30.5.2 -/

/-- The optimal value of a consistent program is not $+\infty$. -/
private theorem infBifun_zero_ne_top (hc : Consistent F) : infBifun F 0 ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hc
  rw [infBifun_apply]
  intro hcon
  exact hx (iInf_eq_top.1 hcon x)

/-- If $F$ is convex, $(P)$ is normal and $(P^*)$ is consistent, then the optimal value of $(P)$ is
not $-\infty$. -/
private theorem infBifun_zero_ne_bot (hF : ConvexBifun F) (hn : Normal F)
    (hc : ConcaveConsistent (dualProgram F)) : infBifun F 0 ≠ ⊥ := by
  obtain ⟨v, hv⟩ := hc
  rw [(theorem_30_3_a_iff_c hF).1 hn, supBifun_apply]
  intro hcon
  exact hv (iSup_eq_bot.1 hcon v)

/-- **Corollary 30.5.2** of [rockafellar1970convex], second assertion. Let $F$ be a convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. If $(P)$ is strongly consistent and $(P^*)$ is
consistent, then $(P^*)$ has an optimal solution.

Theorem 30.4(a) gives normality, so the common optimal value is finite. Corollary 29.1.4 then
gives a Kuhn–Tucker vector, and Theorem 30.5 makes it an optimal solution to $(P^*)$. -/
theorem corollary_30_5_2_dual (hF : ConvexBifun F) (hs : StronglyConsistent F)
    (hc : ConcaveConsistent (dualProgram F)) : (argmax (dualProgram F 0)).Nonempty := by
  have hn : Normal F := theorem_30_4_a hs hF
  have ht : infBifun F 0 ≠ ⊤ := infBifun_zero_ne_top hs.consistent
  have hb : infBifun F 0 ≠ ⊥ := infBifun_zero_ne_bot hF hn hc
  obtain ⟨v, hv⟩ := kuhnTucker_nonempty_of_stronglyConsistent (B := pairing m) hF
    (properConvex_infBifun_of_stronglyConsistent hF hs hb) hs ht
  exact ⟨v, (theorem_30_5 hF hn ht hb v).1 hv⟩

/-- **Corollary 30.5.2** of [rockafellar1970convex], first assertion. Let $F$ be a closed convex
bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$. If $(P)$ is consistent and $(P^*)$ is strongly
consistent, then $(P)$ has an optimal solution.

The book proves this assertion through the concave form of Corollary 29.1.4. The proof here
applies the convex form to $-F^*$ instead. -/
theorem corollary_30_5_2 (hF : ConvexBifun F) (hcl : ClosedConvexBifun F) (hc : Consistent F)
    (hs : ConcaveStronglyConsistent (dualProgram F)) : (argmin (F 0)).Nonempty := by
  have hn : Normal F := theorem_30_4_b hF hcl hs
  have hb : infBifun F 0 ≠ ⊥ := infBifun_zero_ne_bot hF hn hs.concaveConsistent
  obtain ⟨x, hx⟩ := exists_infBifun_eq_of_concaveStronglyConsistent (Bu := pairing m)
    (Bx := pairing n) hF hcl hc hb hs
  exact ⟨x, mem_argmin_iff_eq_iInf.2 (hx.trans (infBifun_apply F 0))⟩

/-!
### Tools for the two examples of the section

Both unnumbered examples of the section are bifunctions from $\mathbb{R}$ to $\mathbb{R}$, so both
are stated on $\mathbb{R}^1$. The private lemmas below handle the single coordinate.
-/

/-- The point of $\mathbb{R}^1$ with coordinate $t$. -/
private noncomputable def coord1 (t : ℝ) : Rn 1 := WithLp.toLp 2 ![t]

@[simp] private theorem coord1_apply (t : ℝ) : coord1 t 0 = t := rfl

@[simp] private theorem zero_coord (i : Fin 1) : (0 : Rn 1) i = 0 := rfl

private theorem ext_one {x y : Rn 1} (h : x 0 = y 0) : x = y := by
  ext i
  fin_cases i
  exact h

private theorem pairing_one (u v : Rn 1) : pairing 1 u v = u 0 * v 0 := by
  simp [PiLp.inner_apply, mul_comm]

private theorem smul_coord (a : ℝ) (x : Rn 1) : (a • x) 0 = a * x 0 := rfl

private theorem tendsto_coord1 :
    Filter.Tendsto (fun k : ℕ => ((1 / (k + 1) : ℝ)) • coord1 1) Filter.atTop (nhds 0) := by
  have hc : Continuous fun c : ℝ => c • coord1 1 := continuous_id.smul continuous_const
  have h := (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  rw [zero_smul] at h
  exact h

/-!
### An unnumbered example: an abnormal program with a duality gap

"There do exist convex programs which are not normal … For an example of abnormality consider the
closed proper convex bifunction $F$ from $R$ to $R$ defined by $(Fu)(x) = \exp(-\sqrt{ux})$ if
$u \ge 0, x \ge 0$, and $+\infty$ otherwise."
-/

/-- **Section 30** of [rockafellar1970convex], the example of an abnormal program. The bifunction
$F$ from $\mathbb{R}$ to $\mathbb{R}$ is
$$(Fu)(x) = \begin{cases} e^{-\sqrt{ux}} & \text{if } u \ge 0 \text{ and } x \ge 0, \\ +\infty &
  \text{otherwise.} \end{cases}$$

The book calls this "the closed proper convex bifunction $F$". Convexity is not proved here: it
is the concavity of the geometric mean on the first quadrant composed with $\exp$, an elementary
fact of real analysis in two variables with no content from convex analysis. What is proved is
the perturbation function that the book displays, the duality gap $\inf F0 = 1$ against
$\sup F^* 0 = 0$ (`Rockafellar.abnormalBifun_duality_gap`), and the failure of normality, which
follows from the perturbation function alone.

The domain condition is an infimum over a proposition, so that no `Decidable` instance appears
in the definition. The space $\mathbb{R}$ is $\mathbb{R}^1$, with coordinate `u 0`. -/
noncomputable def abnormalBifun (u x : Rn 1) : EReal :=
  ⨅ _ : 0 ≤ u 0 ∧ 0 ≤ x 0, ((Real.exp (-Real.sqrt (u 0 * x 0)) : ℝ) : EReal)

/-- On the first quadrant $u \ge 0$, $x \ge 0$, the abnormal example has the value
$(Fu)(x) = e^{-\sqrt{ux}}$. -/
theorem abnormalBifun_of_mem {u x : Rn 1} (h : 0 ≤ u 0 ∧ 0 ≤ x 0) :
    abnormalBifun u x = ((Real.exp (-Real.sqrt (u 0 * x 0)) : ℝ) : EReal) :=
  iInf_pos h

/-- Off the first quadrant, the abnormal example has the value $+\infty$. -/
theorem abnormalBifun_of_notMem {u x : Rn 1} (h : ¬ (0 ≤ u 0 ∧ 0 ≤ x 0)) :
    abnormalBifun u x = ⊤ :=
  iInf_neg h

/-- Every value of the abnormal example is non-negative, because the exponential function is
positive. -/
theorem zero_le_abnormalBifun (u x : Rn 1) : 0 ≤ abnormalBifun u x := by
  by_cases h : 0 ≤ u 0 ∧ 0 ≤ x 0
  · rw [abnormalBifun_of_mem h]
    exact_mod_cast (Real.exp_pos _).le
  · rw [abnormalBifun_of_notMem h]
    exact le_top

/-- Every value of the perturbation function $\inf F$ of the abnormal example is non-negative. -/
theorem zero_le_infBifun_abnormalBifun (u : Rn 1) : 0 ≤ infBifun abnormalBifun u :=
  le_iInf fun x => zero_le_abnormalBifun u x

/-- **Section 30** of [rockafellar1970convex]. The optimal value of $(P)$ for the abnormal example
is $\inf F0 = 1$: at $u = 0$ the objective function is $e^{-\sqrt 0} = 1$ on the whole
non-negative axis. -/
theorem infBifun_abnormalBifun_zero : infBifun abnormalBifun 0 = 1 := by
  refine le_antisymm ?_ (le_iInf fun x => ?_)
  · refine le_trans (iInf_le _ (0 : Rn 1)) (le_of_eq ?_)
    rw [abnormalBifun_of_mem (u := (0 : Rn 1)) (x := (0 : Rn 1)) ⟨le_rfl, le_rfl⟩]
    norm_num
  · by_cases h : 0 ≤ (0 : Rn 1) 0 ∧ 0 ≤ x 0
    · rw [abnormalBifun_of_mem h, zero_coord, zero_mul, Real.sqrt_zero, neg_zero, Real.exp_zero]
      exact le_rfl
    · rw [abnormalBifun_of_notMem h]
      exact le_top

/-- For $\varepsilon > 0$, $e^{-1/\varepsilon} \le \varepsilon$. This follows from $1 + r \le e^r$,
and it is the analytic content of the example: $e^{-\sqrt{ux}}$ becomes smaller than any
positive number when $x$ grows. -/
private theorem exp_neg_le {ε : ℝ} (hε : 0 < ε) : Real.exp (-(1 / ε)) ≤ ε := by
  have hexp : 0 < Real.exp (1 / ε) := Real.exp_pos _
  have hkey : 1 / ε + 1 ≤ Real.exp (1 / ε) := Real.add_one_le_exp _
  have h1 : ε * (1 / ε) = 1 := by field_simp
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ hexp]
  nlinarith [mul_le_mul_of_nonneg_left hkey hε.le]

/-- **Section 30** of [rockafellar1970convex]. For the abnormal example, $(\inf F)(u) = 0$ for every
$u > 0$. -/
theorem infBifun_abnormalBifun_of_pos {u : Rn 1} (hu : 0 < u 0) :
    infBifun abnormalBifun u = 0 := by
  refine le_antisymm (EReal.le_zero_of_forall_le_pos fun ε hε => ?_)
    (zero_le_infBifun_abnormalBifun u)
  refine le_trans (iInf_le _ (coord1 ((1 / ε) ^ 2 / u 0))) ?_
  have hx : 0 ≤ (1 / ε) ^ 2 / u 0 := by positivity
  rw [abnormalBifun_of_mem (u := u) (x := coord1 ((1 / ε) ^ 2 / u 0))
    ⟨hu.le, by rw [coord1_apply]; exact hx⟩, coord1_apply]
  have hval : u 0 * ((1 / ε) ^ 2 / u 0) = (1 / ε) ^ 2 := by field_simp
  rw [hval, Real.sqrt_sq (by positivity)]
  exact EReal.coe_le_coe_iff.2 (exp_neg_le hε)

/-- **Section 30** of [rockafellar1970convex]. For the abnormal example, $(\inf F)(u) = +\infty$ for
every $u < 0$: the program is inconsistent for negative perturbations. -/
theorem infBifun_abnormalBifun_of_neg {u : Rn 1} (hu : u 0 < 0) :
    infBifun abnormalBifun u = ⊤ :=
  le_antisymm le_top (le_iInf fun x => by
    rw [abnormalBifun_of_notMem (fun h => absurd h.1 (not_le.2 hu))])

/-- **Section 30** of [rockafellar1970convex]. For the abnormal example, the optimal value of
$(P^*)$ is $\sup F^* 0 = 0$. Since $\inf F0 = 1$, the two programs have a duality gap. -/
theorem supBifun_dualProgram_abnormalBifun_zero :
    supBifun (dualProgram abnormalBifun) 0 = 0 := by
  refine le_antisymm ?_ ?_
  · rw [supBifun_apply]
    refine iSup_le fun v => EReal.le_zero_of_forall_le_pos fun ε hε => ?_
    rw [dualProgram_zero_apply]
    set t : ℝ := ε / (|v 0| + 1) with ht
    have hden : 0 < |v 0| + 1 := by positivity
    have htpos : 0 < t := by rw [ht]; positivity
    refine le_trans (iInf_le _ (coord1 t)) ?_
    rw [pairing_one, coord1_apply,
      infBifun_abnormalBifun_of_pos (u := coord1 t) (by rw [coord1_apply]; exact htpos), add_zero]
    have hle : t * v 0 ≤ ε := by
      have h1 : v 0 ≤ |v 0| := le_abs_self _
      have h2 : t * (|v 0| + 1) = ε := by rw [ht]; field_simp
      nlinarith [htpos.le]
    exact_mod_cast hle
  · refine le_trans ?_ (le_iSup (fun v => dualProgram abnormalBifun 0 v) (0 : Rn 1))
    rw [dualProgram_zero_apply]
    refine le_iInf fun u => ?_
    rw [pairing_one, zero_coord, mul_zero]
    simpa using zero_le_infBifun_abnormalBifun u

/-- **Section 30** of [rockafellar1970convex]. The abnormal example has a duality gap:
$\sup F^* 0 \neq \inf F0$. -/
theorem abnormalBifun_duality_gap :
    supBifun (dualProgram abnormalBifun) 0 ≠ infBifun abnormalBifun 0 := by
  rw [supBifun_dualProgram_abnormalBifun_zero, infBifun_abnormalBifun_zero]
  exact fun h => absurd h.symm one_ne_zero

/-- **Section 30** of [rockafellar1970convex]. The abnormal example is not normal:
$(\operatorname{cl}(\inf F))(0) = 0$, while $(\inf F)(0) = 1$.

The proof uses only the perturbation function and not convexity of $F$: the closure is at most
the lower semicontinuous hull, and $\inf F$ vanishes along $u_k = 1/(k+1) \to 0$. -/
theorem not_normal_abnormalBifun : ¬ Normal abnormalBifun := by
  intro hn
  rw [normal_iff_convexCl_infBifun_zero, infBifun_abnormalBifun_zero] at hn
  have hle : convexCl (infBifun abnormalBifun) 0 ≤ 0 := by
    refine le_trans (convexCl_le_lscHull _ 0) ?_
    rw [lscHull_eq_liminf, Filter.liminf_eq]
    refine sSup_le fun a ha => ?_
    obtain ⟨k, hk⟩ := (tendsto_coord1.eventually ha).exists
    rwa [infBifun_abnormalBifun_of_pos (u := ((1 / (k + 1) : ℝ)) • coord1 1)
      (by rw [smul_coord, coord1_apply, mul_one]; positivity)] at hk
  rw [hn] at hle
  exact absurd hle (by norm_num)

/-!
### An unnumbered example: a normal program whose dual has no optimal solution

"An example of a normal convex program $(P)$, such that $(P)$ has an optimal solution but $(P^*)$
has no optimal solution, is obtained when $F$ is the closed convex bifunction from $R$ to $R$ given
by $(Fu)(x) = x$ if $x^2 \le u$, $+\infty$ if $x^2 > u$."
-/

/-- **Section 30** of [rockafellar1970convex], the example of a normal program whose dual has no
optimal solution. The bifunction $F$ from $\mathbb{R}$ to $\mathbb{R}$ is
$$(Fu)(x) = \begin{cases} x & \text{if } x^2 \le u, \\ +\infty & \text{if } x^2 > u.
  \end{cases}$$

The domain condition is an infimum over a proposition, as in `Rockafellar.abnormalBifun`. The
space $\mathbb{R}$ is $\mathbb{R}^1$, with coordinate `x 0`. -/
noncomputable def noDualSolutionBifun (u x : Rn 1) : EReal :=
  ⨅ _ : (x 0) ^ 2 ≤ u 0, ((x 0 : ℝ) : EReal)

/-- If $x^2 \le u$, the example has the value $(Fu)(x) = x$. -/
theorem noDualSolutionBifun_of_le {u x : Rn 1} (h : (x 0) ^ 2 ≤ u 0) :
    noDualSolutionBifun u x = ((x 0 : ℝ) : EReal) :=
  iInf_pos h

/-- If $u < x^2$, the example has the value $(Fu)(x) = +\infty$. -/
theorem noDualSolutionBifun_of_lt {u x : Rn 1} (h : u 0 < (x 0) ^ 2) :
    noDualSolutionBifun u x = ⊤ :=
  iInf_neg (not_le.2 h)

private theorem noDualSolutionBifun_ne_bot (u x : Rn 1) : noDualSolutionBifun u x ≠ ⊥ := by
  by_cases h : (x 0) ^ 2 ≤ u 0
  · rw [noDualSolutionBifun_of_le h]
    exact EReal.coe_ne_bot _
  · rw [noDualSolutionBifun_of_lt (not_le.1 h)]
    exact top_ne_bot

/-- The objective function $F0$ of the example vanishes at the origin. -/
theorem noDualSolutionBifun_zero_zero : noDualSolutionBifun 0 (0 : Rn 1) = 0 := by
  rw [noDualSolutionBifun_of_le (u := (0 : Rn 1)) (x := (0 : Rn 1)) (by simp)]
  simp

/-- The objective function $F0$ of the example is $+\infty$ at every $x \neq 0$, because $x^2 \le 0$
forces $x = 0$. -/
theorem noDualSolutionBifun_zero_of_ne {x : Rn 1} (hx : x ≠ 0) :
    noDualSolutionBifun 0 x = ⊤ := by
  refine noDualSolutionBifun_of_lt ?_
  rw [zero_coord]
  by_contra hcon
  rw [not_lt] at hcon
  have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0)]
  exact hx (ext_one (by rw [hx0, zero_coord]))

/-- **Section 30** of [rockafellar1970convex]. For the example, $x = 0$ is the unique optimal
solution to $(P)$. -/
theorem argmin_noDualSolutionBifun : argmin (noDualSolutionBifun 0) = {(0 : Rn 1)} := by
  ext x
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hx
    by_contra hne
    have h := hx 0
    rw [noDualSolutionBifun_zero_of_ne hne, noDualSolutionBifun_zero_zero] at h
    exact absurd h (by simp)
  · rintro rfl
    intro z
    rw [noDualSolutionBifun_zero_zero]
    by_cases hz : z = 0
    · rw [hz, noDualSolutionBifun_zero_zero]
    · rw [noDualSolutionBifun_zero_of_ne hz]
      exact le_top

/-- For the example, the optimal value of $(P)$ is $\inf F0 = 0$. -/
theorem infBifun_noDualSolutionBifun_zero : infBifun noDualSolutionBifun 0 = 0 := by
  rw [infBifun_apply]
  refine le_antisymm (le_trans (iInf_le _ (0 : Rn 1))
    (le_of_eq noDualSolutionBifun_zero_zero)) (le_iInf fun z => ?_)
  by_cases hz : z = 0
  · rw [hz, noDualSolutionBifun_zero_zero]
  · rw [noDualSolutionBifun_zero_of_ne hz]
    exact le_top

private theorem convex_noDualSolutionSet :
    Convex ℝ {p : Rn 1 × Rn 1 | (p.2 0) ^ 2 ≤ p.1 0} := by
  intro p hp q hq a b ha hb hab
  have hp' : (p.2 0) ^ 2 ≤ p.1 0 := hp
  have hq' : (q.2 0) ^ 2 ≤ q.1 0 := hq
  change ((a • p + b • q).2 0) ^ 2 ≤ (a • p + b • q).1 0
  have h1 : (a • p + b • q).1 0 = a * p.1 0 + b * q.1 0 := rfl
  have h2 : (a • p + b • q).2 0 = a * p.2 0 + b * q.2 0 := rfl
  rw [h1, h2]
  have key : a * p.2 0 ^ 2 + b * q.2 0 ^ 2 - (a * p.2 0 + b * q.2 0) ^ 2
      = a * b * (p.2 0 - q.2 0) ^ 2 := by
    linear_combination (-(a * p.2 0 ^ 2 + b * q.2 0 ^ 2)) * hab
  have hnn : 0 ≤ a * b * (p.2 0 - q.2 0) ^ 2 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  have h3 : a * p.2 0 ^ 2 ≤ a * p.1 0 := mul_le_mul_of_nonneg_left hp' ha
  have h4 : b * q.2 0 ^ 2 ≤ b * q.1 0 := mul_le_mul_of_nonneg_left hq' hb
  linarith

private theorem graphFn_noDualSolutionBifun :
    graphFn noDualSolutionBifun
      = fun p : Rn 1 × Rn 1 =>
          indicatorFn {q : Rn 1 × Rn 1 | (q.2 0) ^ 2 ≤ q.1 0} p + ((p.2 0 : ℝ) : EReal) := by
  funext p
  by_cases h : (p.2 0) ^ 2 ≤ p.1 0
  · rw [indicatorFn_of_mem (s := {q : Rn 1 × Rn 1 | (q.2 0) ^ 2 ≤ q.1 0}) h, zero_add]
    exact noDualSolutionBifun_of_le h
  · rw [indicatorFn_of_notMem (s := {q : Rn 1 × Rn 1 | (q.2 0) ^ 2 ≤ q.1 0}) h,
      EReal.top_add_coe]
    exact noDualSolutionBifun_of_lt (not_le.1 h)

/-- The example is a convex bifunction: its graph function is the indicator function of the convex
set $\{(u, x) \mid x^2 \le u\}$ plus the linear function $(u, x) \mapsto x$. -/
theorem convexBifun_noDualSolutionBifun : ConvexBifun noDualSolutionBifun := by
  rw [convexBifun_iff, graphFn_noDualSolutionBifun]
  exact convexFn_add_coe (l := fun p : Rn 1 × Rn 1 => p.2 0)
    (convexFn_indicatorFn.2 convex_noDualSolutionSet) fun _ _ _ _ _ => rfl

/-- The example is a closed bifunction: its epigraph is defined by two inequalities between
continuous functions. -/
theorem closedConvexBifun_noDualSolutionBifun : ClosedConvexBifun noDualSolutionBifun := by
  have hne : ∀ p : Rn 1 × Rn 1, graphFn noDualSolutionBifun p ≠ ⊥ := fun p =>
    noDualSolutionBifun_ne_bot p.1 p.2
  rw [closedConvexBifun_iff, closedConvex_iff_lowerSemicontinuous hne,
    lowerSemicontinuous_iff_isClosed_epi]
  have hc1 : Continuous fun q : (Rn 1 × Rn 1) × ℝ => q.1.2 0 :=
    (continuous_coord 0).comp (continuous_snd.comp continuous_fst)
  have hc2 : Continuous fun q : (Rn 1 × Rn 1) × ℝ => q.1.1 0 :=
    (continuous_coord 0).comp (continuous_fst.comp continuous_fst)
  have hset : epi (graphFn noDualSolutionBifun)
      = {q : (Rn 1 × Rn 1) × ℝ | (q.1.2 0) ^ 2 ≤ q.1.1 0} ∩ {q | q.1.2 0 ≤ q.2} := by
    ext q
    constructor
    · intro hq
      have hq' : graphFn noDualSolutionBifun q.1 ≤ ((q.2 : ℝ) : EReal) := hq
      by_cases hm : (q.1.2 0) ^ 2 ≤ q.1.1 0
      · refine ⟨hm, ?_⟩
        have hval : graphFn noDualSolutionBifun q.1 = ((q.1.2 0 : ℝ) : EReal) :=
          noDualSolutionBifun_of_le hm
        rw [hval] at hq'
        exact_mod_cast hq'
      · exfalso
        have hval : graphFn noDualSolutionBifun q.1 = ⊤ :=
          noDualSolutionBifun_of_lt (not_le.1 hm)
        rw [hval] at hq'
        exact absurd (top_le_iff.1 hq') (by simp)
    · rintro ⟨hm, hle⟩
      have hval : graphFn noDualSolutionBifun q.1 = ((q.1.2 0 : ℝ) : EReal) :=
        noDualSolutionBifun_of_le hm
      change graphFn noDualSolutionBifun q.1 ≤ ((q.2 : ℝ) : EReal)
      rw [hval]
      exact_mod_cast hle
  rw [hset]
  exact (isClosed_le (hc1.pow 2) hc2).inter (isClosed_le hc1 continuous_snd)

/-- The objective function $F0$ of the example is a proper convex function. -/
theorem properConvex_noDualSolutionBifun_zero : ProperConvex (noDualSolutionBifun 0) :=
  ⟨⟨0, by rw [mem_convexDom, noDualSolutionBifun_zero_zero]; simp⟩,
    fun x => noDualSolutionBifun_ne_bot 0 x⟩

/-- **Section 30** of [rockafellar1970convex]. The example is normal.

The book derives this from the lower semicontinuity of $(\inf F)(u) = -\sqrt u$ at $u = 0$. Here
it follows from Theorem 30.4(i), because the set of optimal solutions is the single point $0$. -/
theorem normal_noDualSolutionBifun : Normal noDualSolutionBifun :=
  theorem_30_4_i convexBifun_noDualSolutionBifun closedConvexBifun_noDualSolutionBifun
    properConvex_noDualSolutionBifun_zero
    (by rw [argmin_noDualSolutionBifun]; exact Set.singleton_nonempty _)
    (by rw [argmin_noDualSolutionBifun]; exact Bornology.isBounded_singleton)

/-- **Section 30** of [rockafellar1970convex]. For the example, $(\inf F)(u) \le -\sqrt u$ for every
$u \ge 0$.

The value $-\sqrt u$ is attained at $x = -\sqrt u$, the left end point of
$\{x \mid x^2 \le u\}$. Only this half of the formula of the book is needed. -/
theorem infBifun_noDualSolutionBifun_le {t : ℝ} (ht : 0 ≤ t) :
    infBifun noDualSolutionBifun (coord1 t) ≤ ((-Real.sqrt t : ℝ) : EReal) := by
  have hcond : (coord1 (-Real.sqrt t) 0) ^ 2 ≤ coord1 t 0 := by
    rw [coord1_apply, coord1_apply, neg_pow, Real.sq_sqrt ht]
    simp
  refine le_trans (iInf_le _ (coord1 (-Real.sqrt t))) (le_of_eq ?_)
  rw [noDualSolutionBifun_of_le hcond, coord1_apply]

/-- **Section 30** of [rockafellar1970convex]. For the example, $(P)$ has no Kuhn–Tucker vector.

The perturbation function $-\sqrt u$ is lower semicontinuous at $0$ but has derivative $-\infty$
there, so it has no affine minorant that is exact at $0$. For each $u^*$, the value
$\langle u, u^* \rangle + (\inf F)(u)$ is less than $\inf F0 = 0$ at $u = s^2$ with
$s = 1/(1 + |u^*|)$. -/
theorem kuhnTucker_noDualSolutionBifun :
    KuhnTucker (pairing 1) noDualSolutionBifun = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  rw [mem_kuhnTucker_iff_forall_le] at hv
  obtain ⟨-, -, hle⟩ := hv
  have habs : (0 : ℝ) < 1 + |v 0| := by positivity
  set s : ℝ := 1 / (1 + |v 0|) with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have h := hle (coord1 (s ^ 2))
  rw [infBifun_noDualSolutionBifun_zero, pairing_one, coord1_apply] at h
  have hb := infBifun_noDualSolutionBifun_le (t := s ^ 2) (by positivity)
  rw [Real.sqrt_sq hs0.le] at hb
  have hchain : ((s ^ 2 * v 0 : ℝ) : EReal)
      + infBifun noDualSolutionBifun (coord1 (s ^ 2)) ≤ ((s ^ 2 * v 0 + -s : ℝ) : EReal) := by
    rw [EReal.coe_add]
    exact add_le_add le_rfl hb
  have hfin : (0 : EReal) ≤ ((s ^ 2 * v 0 + -s : ℝ) : EReal) := le_trans h hchain
  have hreal : (0 : ℝ) ≤ s ^ 2 * v 0 + -s := by exact_mod_cast hfin
  have hsv : s * v 0 < 1 := by
    rw [hs, div_mul_eq_mul_div, one_mul, div_lt_one habs]
    linarith [le_abs_self (v 0)]
  nlinarith [mul_lt_mul_of_pos_left hsv hs0]

/-- **Section 30** of [rockafellar1970convex]. For the example, the dual program $(P^*)$ has no
optimal solution, although $(P)$ is normal and has an optimal solution.

By Theorem 30.5 the optimal solutions to $(P^*)$ are the Kuhn–Tucker vectors for $(P)$, and
there are none. -/
theorem argmax_dualProgram_noDualSolutionBifun :
    argmax (dualProgram noDualSolutionBifun 0) = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  have ht : infBifun noDualSolutionBifun 0 ≠ ⊤ := by
    rw [infBifun_noDualSolutionBifun_zero]; simp
  have hb : infBifun noDualSolutionBifun 0 ≠ ⊥ := by
    rw [infBifun_noDualSolutionBifun_zero]; simp
  have h := (theorem_30_5 convexBifun_noDualSolutionBifun normal_noDualSolutionBifun ht hb v).2 hv
  rw [kuhnTucker_noDualSolutionBifun] at h
  exact h

end Rockafellar
