/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Saad, Section 2.4: Mesh generation and refinement

Section 2.4 of [saad2003iterative] is descriptive: it explains how a triangulation of a planar
domain is produced and then refined, and its content is Figures 2.10 and 2.11 rather than displayed
formulas. The one mathematical claim of the section is that the standard refinement, which joins the
three midpoints of every triangle and so produces four triangles, preserves the angles, so that
repeated refinement of a good triangulation stays good. This module proves that claim as elementary
geometry in the Euclidean plane, with no triangulation: all four children of a triangle $ABC$ are
similar to it, because every edge of a child is half of a segment of the parent.

## Main results

* §2.4, `SaadSparse.Chapter02.medialTriangle_angle_eq`: the medial triangle on the three midpoints
  has the same three angles as $ABC$.
* §2.4, `SaadSparse.Chapter02.cornerTriangle_angle_eq`: the corner triangle at the vertex $A$ has
  the same three angles as $ABC$.

## Implementation notes

* The four children are the medial triangle on the three midpoints and the three corner triangles,
  one at each vertex. The three corner triangles need one statement only. The corner at $B$ of $ABC$
  is the corner at the first vertex of $BAC$, and `midpoint` is symmetric in its two arguments, so
  `SaadSparse.Chapter02.cornerTriangle_angle_eq B A C` and
  `SaadSparse.Chapter02.cornerTriangle_angle_eq C A B` give the other two.

## Not formalized

* **Triangulations, their mesh size and their successive refinements.** This is the same missing
  geometry that keeps the finite element space of §2.3 out of the library
  (`NumlibSurface.SaadSparse.Chapter02.Section03`): Mathlib has simplicial complexes, but nothing
  that relates one to a domain $\Omega$, and nothing that integrates over its cells.
* **The angle bounds for a usable refinement.** The source says that the angles of a mesh "must
  satisfy certain bounds", but it never writes such a bound down, so there is no shape-regularity
  condition to state.
-/

open EuclideanGeometry

namespace SaadSparse.Chapter02

variable (A B C : EuclideanSpace ℝ (Fin 2))

/-- If $c \neq 0$, $p_1 - p_2 = c(q_1 - q_2)$ and $p_3 - p_2 = c(q_3 - q_2)$, then
$\angle p_1 p_2 p_3 = \angle q_1 q_2 q_3$, because a homothety preserves angles. -/
private theorem angle_eq_of_sub_eq_smul {p₁ p₂ p₃ q₁ q₂ q₃ : EuclideanSpace ℝ (Fin 2)} {c : ℝ}
    (hc : c ≠ 0) (h₁ : p₁ - p₂ = c • (q₁ - q₂)) (h₃ : p₃ - p₂ = c • (q₃ - q₂)) :
    ∠ p₁ p₂ p₃ = ∠ q₁ q₂ q₃ := by
  simp only [EuclideanGeometry.angle, vsub_eq_sub, h₁, h₃]
  exact InnerProductGeometry.angle_smul_smul hc _ _

/-- For points $a, b, c, d$ of the plane, $\operatorname{mid}(a, b) - \operatorname{mid}(c, d) =
\frac{1}{2}(a + b - c - d)$, where $\operatorname{mid}$ is the midpoint. -/
private theorem midpoint_sub_midpoint' (a b c d : EuclideanSpace ℝ (Fin 2)) :
    midpoint ℝ a b - midpoint ℝ c d = (2⁻¹ : ℝ) • (a + b - c - d) := by
  simp only [midpoint_eq_smul_add, invOf_eq_inv]
  module

/-- **Section 2.4** of [saad2003iterative]: the medial triangle of the midpoint refinement has the
same three angles as the triangle that it refines. Let $A, B, C$ be points of the Euclidean
plane, and let $M_A$, $M_B$ and $M_C$ be the midpoints of $BC$, $AC$ and $AB$. Then
$$\angle M_B M_A M_C = \angle BAC, \qquad \angle M_A M_B M_C = \angle ABC, \qquad \angle M_A M_C
  M_B = \angle ACB.$$

Every edge of the medial triangle is half of a side of $ABC$ with the opposite sign, so the
medial triangle is the image of $ABC$ under the homothety of ratio $-1/2$ about the centroid. No
hypothesis is needed, so the statement also holds for degenerate triangles. The angle is the
unoriented angle `EuclideanGeometry.angle`. -/
theorem medialTriangle_angle_eq :
    ∠ (midpoint ℝ A C) (midpoint ℝ B C) (midpoint ℝ A B) = ∠ B A C ∧
      ∠ (midpoint ℝ B C) (midpoint ℝ A C) (midpoint ℝ A B) = ∠ A B C ∧
      ∠ (midpoint ℝ B C) (midpoint ℝ A B) (midpoint ℝ A C) = ∠ A C B := by
  refine ⟨angle_eq_of_sub_eq_smul (c := -(2⁻¹ : ℝ)) (by norm_num) ?_ ?_,
    angle_eq_of_sub_eq_smul (c := -(2⁻¹ : ℝ)) (by norm_num) ?_ ?_,
    angle_eq_of_sub_eq_smul (c := -(2⁻¹ : ℝ)) (by norm_num) ?_ ?_⟩ <;>
    rw [midpoint_sub_midpoint'] <;> module

/-- **Section 2.4** of [saad2003iterative]: the corner triangle of the midpoint refinement at a
vertex has the same three angles as the triangle that it refines. Let $A, B, C$ be points of the
Euclidean plane, and let $M_B$ and $M_C$ be the midpoints of $AC$ and $AB$. Then the triangle
$A M_C M_B$ satisfies
$$\angle M_C A M_B = \angle BAC, \qquad \angle A M_C M_B = \angle ABC, \qquad \angle A M_B M_C =
  \angle ACB.$$

The corner triangle is the image of $ABC$ under the homothety of ratio $1/2$ about $A$. The
corner triangles at $B$ and at $C$ are this statement read at $BAC$ and at $CAB$, because
`midpoint` is symmetric in its two arguments. -/
theorem cornerTriangle_angle_eq :
    ∠ (midpoint ℝ A B) A (midpoint ℝ A C) = ∠ B A C ∧
      ∠ A (midpoint ℝ A B) (midpoint ℝ A C) = ∠ A B C ∧
      ∠ A (midpoint ℝ A C) (midpoint ℝ A B) = ∠ A C B := by
  have hA : ∀ x y : EuclideanSpace ℝ (Fin 2), x - midpoint ℝ x y = (2⁻¹ : ℝ) • (x - y) :=
    fun x y => by
      simp only [midpoint_eq_smul_add, invOf_eq_inv]
      module
  have hB : ∀ x y : EuclideanSpace ℝ (Fin 2), midpoint ℝ x y - x = (2⁻¹ : ℝ) • (y - x) :=
    fun x y => by
      simp only [midpoint_eq_smul_add, invOf_eq_inv]
      module
  refine ⟨angle_eq_of_sub_eq_smul (c := (2⁻¹ : ℝ)) (by norm_num) (hB A B) (hB A C),
    angle_eq_of_sub_eq_smul (c := (2⁻¹ : ℝ)) (by norm_num) (hA A B) ?_,
    angle_eq_of_sub_eq_smul (c := (2⁻¹ : ℝ)) (by norm_num) (hA A C) ?_⟩ <;>
    rw [midpoint_sub_midpoint'] <;> module

end SaadSparse.Chapter02
