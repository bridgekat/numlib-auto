/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Polyhedral.Ops
import Numlib.Analysis.Convex.Recession.Closedness

/-!
# The recession cone of a polyhedral set

The recession cone $0^+ C$ of a convex set $C$ is the set of directions $y$ such that $x + ay \in C$
for every $x \in C$ and $a \ge 0$. Both descriptions of a nonempty polyhedral set give its recession
cone directly ([rockafellar1970convex], §19). On the side of inequalities, dropping the right-hand
sides of the system $\varphi_i(x) \le b_i$ gives $0^+ C = \{ y \mid \varphi_i(y) \le 0 \text{ for
every } i \}$. On the side of generators, the recession cone of a nonempty finitely generated set
$\operatorname{conv} P + \operatorname{cone} D$ is $\operatorname{cone} D$.

A consequence of the second description is that a linear map $A$ commutes with $0^+$ on nonempty
polyhedral sets, $0^+(AC) = A(0^+ C)$, with no hypothesis on $A$. The general recession calculus
cannot give this: it computes $0^+(AC)$ only when $A$ maps no nonzero direction of recession of $C$
to $0$.

## Main results

* `ConvexAnalysis.recessionCone_polyhedral_system`,
  `ConvexAnalysis.Polyhedral.polyhedralCone_recessionCone`: the recession cone of a nonempty
  polyhedral set is the polyhedral cone obtained by dropping the right-hand sides.
* `ConvexAnalysis.recessionCone_of_finitelyGenerated`,
  `ConvexAnalysis.FinitelyGenerated.finitelyGeneratedCone_recessionCone`: the recession cone of a
  nonempty set $\operatorname{conv} P + \operatorname{cone} D$ is $\operatorname{cone} D$, a
  finitely generated cone.
* `ConvexAnalysis.Polyhedral.recessionCone_image`: $0^+(AC) = A(0^+ C)$ for a nonempty polyhedral
  set $C$ and any linear map $A$.
-/

open Set Pointwise

namespace ConvexAnalysis

/-! ### The side of inequalities -/

section Inequalities

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Let $s$ be a finite set of pairs $(\varphi, b)$ of a linear functional $\varphi$ on $E$ and a
real number $b$, and let $C = \{ x \mid \varphi(x) \le b \text{ for every } (\varphi, b) \in s
\}$ be nonempty. Then $$0^+ C = \{ y \in E \mid \varphi(y) \le 0 \text{ for every } (\varphi, b)
\in s \}.$$

This is `ConvexAnalysis.recessionCone_setOf_forall_le` with the inequalities reversed, which is
where the two negations in the proof come from. -/
theorem recessionCone_polyhedral_system {s : Finset ((E →ₗ[ℝ] ℝ) × ℝ)}
    (hne : {x : E | ∀ q ∈ s, q.1 x ≤ q.2}.Nonempty) :
    recessionCone {x : E | ∀ q ∈ s, q.1 x ≤ q.2} = {y : E | ∀ q ∈ s, q.1 y ≤ 0} := by
  have hset : {x : E | ∀ q ∈ s, q.1 x ≤ q.2}
      = {x : E | ∀ i : {q : (E →ₗ[ℝ] ℝ) × ℝ // q ∈ s}, -(i : (E →ₗ[ℝ] ℝ) × ℝ).2
          ≤ (-(i : (E →ₗ[ℝ] ℝ) × ℝ).1 : E →ₗ[ℝ] ℝ) x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Subtype.forall, LinearMap.neg_apply, neg_le_neg_iff]
  rw [hset, recessionCone_setOf_forall_le _ _ (by rw [← hset]; exact hne)]
  ext y
  simp only [Set.mem_ofPred_eq, Subtype.forall, LinearMap.neg_apply, Left.nonneg_neg_iff]

/-- The recession cone of a nonempty polyhedral set $C$ is a polyhedral cone. This is
`ConvexAnalysis.recessionCone_polyhedral_system` in a form that does not name the system of
inequalities. -/
theorem Polyhedral.polyhedralCone_recessionCone {C : Set E} (hC : Polyhedral C)
    (hne : C.Nonempty) : PolyhedralCone (recessionCone C) := by
  classical
  obtain ⟨s, rfl⟩ := hC
  rw [recessionCone_polyhedral_system hne]
  refine ⟨s.image Prod.fst, ?_⟩
  ext y
  simp only [Set.mem_ofPred_eq, Finset.mem_image]
  constructor
  · intro h φ hφ
    obtain ⟨q, hq, rfl⟩ := hφ
    exact h q hq
  · intro h q hq
    exact h q.1 ⟨q, hq, rfl⟩

end Inequalities

/-! ### The side of generators -/

section Generators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Let $E$ be a finite-dimensional real normed space, let $P, D \subseteq E$ be finite, and let
$C = \operatorname{conv} P + \operatorname{cone} D$ be nonempty. Then
$0^+ C = \operatorname{cone} D$.

The inclusion $0^+ C \supseteq \operatorname{cone} D$ needs no hypothesis. The inclusion
$\subseteq$ is the formula for the recession cone of a sum, whose hypothesis holds because
$\operatorname{conv} P$ is compact. -/
theorem recessionCone_of_finitelyGenerated {C : Set E} {P D : Finset E}
    (hPD : C = convexHull ℝ (P : Set E) + (PointedCone.hull ℝ (D : Set E) : Set E))
    (hne : C.Nonempty) :
    recessionCone C = (PointedCone.hull ℝ (D : Set E) : Set E) := by
  obtain ⟨x, hx⟩ := hne
  rw [hPD] at hx
  obtain ⟨u, hu, v, -, -⟩ := hx
  have hPne : (convexHull ℝ (P : Set E)).Nonempty := ⟨u, hu⟩
  have hDne : ((PointedCone.hull ℝ (D : Set E) : Set E)).Nonempty :=
    ⟨0, (PointedCone.hull ℝ (D : Set E)).zero_mem⟩
  have hPcomp : IsCompact (convexHull ℝ (P : Set E)) :=
    P.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hPrec : recessionCone (convexHull ℝ (P : Set E)) = {0} :=
    (isCompact_iff_recessionCone_eq_zero (convex_convexHull ℝ _) hPcomp.isClosed hPne).1 hPcomp
  have hDcl : IsClosed ((PointedCone.hull ℝ (D : Set E) : Set E)) :=
    FinitelyGeneratedCone.isClosed ⟨D, rfl⟩
  have hDconv : Convex ℝ ((PointedCone.hull ℝ (D : Set E) : Set E)) :=
    ((PointedCone.hull ℝ (D : Set E) : ConvexCone ℝ E)).convex
  rw [hPD, Convex.recessionCone_add_of_neg_notMem_recessionCone (convex_convexHull ℝ _)
      hPcomp.isClosed hPne hDconv hDcl hDne
      (fun z hz _ => by rw [hPrec] at hz; exact hz),
    hPrec, recessionCone_coe_pointedCone]
  ext y
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    simpa using hb
  · exact fun hy => ⟨0, rfl, y, hy, zero_add y⟩

/-- In a finite-dimensional real normed space, the recession cone of a nonempty finitely generated
convex set is a finitely generated cone. This is the counterpart of
`ConvexAnalysis.Polyhedral.polyhedralCone_recessionCone`, in a form that does not name the
generators. -/
theorem FinitelyGenerated.finitelyGeneratedCone_recessionCone {C : Set E}
    (hC : FinitelyGenerated C) (hne : C.Nonempty) : FinitelyGeneratedCone (recessionCone C) :=
  let ⟨_, D, hPD⟩ := hC
  ⟨D, recessionCone_of_finitelyGenerated hPD hne⟩

/-- **A linear map commutes with the recession cone on polyhedral sets.** Let $E$ and $F$ be
finite-dimensional real normed spaces, let $C \subseteq E$ be a nonempty polyhedral set, and let
$A \colon E \to F$ be a linear map. Then $$0^+(A C) = A(0^+ C).$$

No hypothesis on $A$ is needed. For a general closed convex set $C$ this fails, and the image
$AC$ need not even be closed. The general criterion gives the identity only when
$0^+ C \cap \ker A = \{0\}$. -/
theorem Polyhedral.recessionCone_image {C : Set E} (hC : Polyhedral C) (hne : C.Nonempty)
    (A : E →ₗ[ℝ] F) : recessionCone (A '' C) = A '' recessionCone C := by
  classical
  obtain ⟨P, D, hPD⟩ := hC.finitelyGenerated
  have himg : A '' C = convexHull ℝ ((P.image A : Finset F) : Set F)
      + (PointedCone.hull ℝ ((D.image A : Finset F) : Set F) : Set F) := by
    rw [hPD, Set.image_add A, LinearMap.image_convexHull, ← coe_hull_image, Finset.coe_image,
      Finset.coe_image]
  rw [recessionCone_of_finitelyGenerated himg (hne.image A),
    recessionCone_of_finitelyGenerated hPD hne, Finset.coe_image, coe_hull_image]

end Generators

end ConvexAnalysis
