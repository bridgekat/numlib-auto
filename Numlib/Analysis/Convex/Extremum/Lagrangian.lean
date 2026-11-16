/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Extremum.Perturbation

/-!
# Lagrangians of generalized convex programs

Let $U$ and $V$ be real vector spaces in duality through a pairing $\langle u, v \rangle$, and let
$F$ be a bifunction from $U$ to a set $X$, so that $F(u, x) \in [-\infty, +\infty]$. The
**Lagrangian** of the program associated with $F$ is
$$L(v, x) = \inf_u \bigl\{ \langle u, v \rangle + F(u, x) \bigr\},$$
the partial concave conjugate of $-F$ in the perturbation variable $u$. This follows
[rockafellar1970convex], §29. The main step is the exchange of infima $\inf_x L(v, x) = \inf_u
\{\langle u, v \rangle + \inf F u\}$, which turns the definition of a Kuhn–Tucker vector into a
statement about $L$. Dually, the supremum of $L(\cdot, x)$ is the closure of $u \mapsto F(u, x)$ at
the origin.

## Main definitions

* `ConvexAnalysis.lagrangian`: the Lagrangian $L$ of the program associated with $F$.

## Main results

* `ConvexAnalysis.lagrangian_eq_concaveConj`: $L(\cdot, x)$ is the concave conjugate of
  $u \mapsto -F(u, x)$.
* `ConvexAnalysis.iInf_lagrangian`: $\inf_x L(v, x) = \inf_u \{\langle u, v \rangle + \inf F u\}$.
* `ConvexAnalysis.iSup_lagrangian`: $\sup_v L(v, x) = \operatorname{cl}(F(\cdot, x))(0)$ for convex
  $F(\cdot, x)$, by `ConvexAnalysis.convexCl_zero_eq_iSup_iInf`, the Fenchel–Moreau theorem at the
  origin.
* `ConvexAnalysis.mem_kuhnTucker_iff_iInf_lagrangian`: $v$ is a Kuhn–Tucker vector if and only if
  $\inf_x L(v, x)$ is equal to the optimal value and the optimal value is finite.

## Implementation notes

* The Lagrangian is identified with a concave conjugate, so the concavity, closedness and
  biconjugation of $L(\cdot, x)$ follow from lemmas about the concave conjugate
  `ConvexAnalysis.concaveConj`, applied for each fixed $x$.
* For the equality-constrained program with perturbed constraints $h(x) = u$ and the dot product
  pairing, $L$ is the real-valued Lagrangian `Constrained.lagrangian` of
  `Numlib.Optimization.Constrained`, read in `EReal`. See `Constrained.coe_lagrangian_eq`.
-/

namespace ConvexAnalysis

section Defs

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X} {v : V} {x : X}

/-- The **Lagrangian** of the generalized convex program associated with a bifunction $F$ from $U$
to $X$ is the function on $V \times X$ given by
$$L(v, x) = \inf_{u \in U} \bigl\{ \langle u, v \rangle + F(u, x) \bigr\}.$$

This follows §29 of [rockafellar1970convex]. Consider the program of minimizing $f(x)$ subject
to $h(x) = 0$, with the perturbation $F(u, x) = f(x)$ if $h(x) = u$ and $F(u, x) = +\infty$
otherwise, and the dot product pairing. For this program, $L(v, x) = f(x) + \sum_i v_i h_i(x)$,
which is the real-valued `Constrained.lagrangian f h x v` read in `EReal`, by
`Constrained.coe_lagrangian_eq`. -/
noncomputable def lagrangian (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) : V → X → EReal :=
  fun v x => ⨅ u, ((B u v : ℝ) : EReal) + F u x

/-- The value of the Lagrangian is $L(v, x) = \inf_u \{\langle u, v \rangle + F(u, x)\}$. -/
theorem lagrangian_apply (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) (x : X) :
    lagrangian B F v x = ⨅ u, ((B u v : ℝ) : EReal) + F u x := rfl

/-- **The Lagrangian is a concave conjugate.** For every bifunction $F$ from $U$ to $X$ and every
$x \in X$, the function $L(\cdot, x)$ is the concave conjugate of $u \mapsto -F(u, x)$:
$$L(v, x) = \inf_u \bigl\{ \langle u, v \rangle - (-F(u, x)) \bigr\}.$$

The concave conjugate is `ConvexAnalysis.concaveConj`. -/
theorem lagrangian_eq_concaveConj (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) (x : X) :
    lagrangian B F v x = concaveConj B (fun u => -(F u x)) v := by
  rw [lagrangian_apply, concaveConj_apply]
  exact iInf_congr fun u => by rw [sub_eq_add_neg, neg_neg]

/-- The Lagrangian is at most the objective: $L(v, x) \le F(0, x)$ for all $v$ and $x$. -/
theorem lagrangian_le (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) (x : X) :
    lagrangian B F v x ≤ F 0 x := by
  refine le_trans (iInf_le _ 0) (le_of_eq ?_)
  rw [map_zero, LinearMap.zero_apply, EReal.coe_zero, zero_add]

/-- **Minimizing the Lagrangian prices the perturbations.** For every bifunction $F$ from $U$ to $X$
and every $v \in V$,
$$\inf_x L(v, x) = \inf_u \bigl\{ \langle u, v \rangle + \inf_x F(u, x) \bigr\}.$$
-/
theorem iInf_lagrangian (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) :
    (⨅ x, lagrangian B F v x) = ⨅ u, (((B u v : ℝ) : EReal) + infBifun F u) := by
  rw [show (⨅ x, lagrangian B F v x) = ⨅ x, ⨅ u, (((B u v : ℝ) : EReal) + F u x) from rfl,
    iInf_comm]
  refine iInf_congr fun u => ?_
  rw [infBifun_apply, add_comm, EReal.iInf_add_coe]
  exact iInf_congr fun x => add_comm _ _

/-- **The Lagrangian description of Kuhn–Tucker vectors.** For every bifunction $F$ from $U$ to $X$,
a vector $v \in V$ is a Kuhn–Tucker vector of the program associated with $F$ if and only if the
optimal value $\inf_x F(0, x)$ is finite and
$$\inf_x L(v, x) = \inf_x F(0, x).$$

The Kuhn–Tucker vectors are `ConvexAnalysis.KuhnTucker`. -/
theorem mem_kuhnTucker_iff_iInf_lagrangian :
    v ∈ KuhnTucker B F ↔ infBifun F 0 ≠ ⊤ ∧ infBifun F 0 ≠ ⊥ ∧
      (⨅ x, lagrangian B F v x) = infBifun F 0 := by
  rw [KuhnTucker, Set.mem_ofPred_eq, iInf_lagrangian]

/-- **Weak duality.** For every $v \in V$, $\inf_x L(v, x) \le \inf_x F(0, x)$. -/
theorem iInf_lagrangian_le (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (v : V) :
    (⨅ x, lagrangian B F v x) ≤ infBifun F 0 := by
  rw [iInf_lagrangian]
  exact iInf_add_infBifun_le B F v

end Defs

/-! ### The closure of a convex function at the origin -/

section ClosureAtZero

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- **The Fenchel–Moreau theorem at the origin.** Let $E$ be a locally convex real topological
vector space in compatible duality with $F$, and let $f : E \to [-\infty, +\infty]$ be convex.
Then the closure of $f$ at the origin is
$$(\operatorname{cl} f)(0) = \sup_{y \in F} \inf_{x \in E} \bigl\{ \langle x, y \rangle + f(x)
  \bigr\}.$$

The closure is `ConvexAnalysis.convexCl`, and the compatibility is
`ConvexAnalysis.IsCompatiblePairing`. -/
theorem convexCl_zero_eq_iSup_iInf (hf : ConvexFn f) :
    convexCl f 0 = ⨆ y : F, ⨅ x : E, (((B x y : ℝ) : EReal) + f x) := by
  have hsurj : Function.Surjective (fun y : F => -y) := fun y => ⟨-y, neg_neg y⟩
  have hterm : ∀ y : F, ((B (0 : E) y : ℝ) : EReal) - convexConj B f y
      = ⨅ x : E, (((B x (-y) : ℝ) : EReal) + f x) := by
    intro y
    rw [map_zero, LinearMap.zero_apply, EReal.coe_zero, zero_sub, convexConj_apply,
      EReal.neg_iSup]
    refine iInf_congr fun x => ?_
    have hb : (B x (-y) : ℝ) = -(B x y) := by rw [map_neg]
    rw [EReal.neg_coe_sub, hb, EReal.coe_neg, sub_eq_add_neg, add_comm]
  rw [← convexBiconj_eq_convexCl (B := B) hf, convexBiconj_apply, iSup_congr hterm]
  exact hsurj.iSup_comp fun y : F => ⨅ x : E, (((B x y : ℝ) : EReal) + f x)

end ClosureAtZero

section LagrangianSup

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul ℝ U] [LocallyConvexSpace ℝ U]
  {Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} [IsCompatiblePairing Bu] {F : Bifun U X} {x : X}

/-- **Maximizing the Lagrangian gives the closure at the origin.** Let $U$ be a locally convex real
topological vector space in compatible duality with $V$, let $F$ be a bifunction from $U$ to
$X$, and let $x \in X$ be such that $u \mapsto F(u, x)$ is convex. Then
$$\sup_v L(v, x) = \operatorname{cl}\bigl(F(\cdot, x)\bigr)(0).$$

This is `ConvexAnalysis.convexCl_zero_eq_iSup_iInf` for the function $u \mapsto F(u, x)$. It is
the counterpart of `ConvexAnalysis.iInf_lagrangian`. -/
theorem iSup_lagrangian (hf : ConvexFn fun u => F u x) :
    (⨆ w, lagrangian Bu F w x) = convexCl (fun u => F u x) 0 :=
  (convexCl_zero_eq_iSup_iInf (B := Bu) hf).symm

end LagrangianSup


section Concave

variable {U V X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  {B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ} {F : Bifun U X} {x : X}

/-- For every bifunction $F$ and every $x \in X$, the function $v \mapsto L(v, x)$ is concave. -/
theorem concaveFn_lagrangian (B : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (F : Bifun U X) (x : X) :
    ConcaveFn (fun v => lagrangian B F v x) := by
  have h : (fun v => lagrangian B F v x) = concaveConj B (fun u => -(F u x)) :=
    funext fun v => lagrangian_eq_concaveConj B F v x
  rw [h]
  exact concaveFn_concaveConj B _

end Concave

end ConvexAnalysis
