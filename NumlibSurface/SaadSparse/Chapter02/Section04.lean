import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Saad §2.4: mesh generation and refinement

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM,
2003, §2.4.

The section is descriptive: it explains how a triangulation of a planar domain is produced and then
refined, and its content is Figures 2.10 and 2.11 rather than displayed formulas. Two things about
it are worth recording here.

**What is not formalized, and why.** The section's subject — a triangulation `Ω_h = ∪ K_i` of a
planar domain, its mesh size, and the successive refinements of one — is the same missing geometry
that keeps §2.3's finite element space out of the library, and it is named there
(`NumlibSurface/SaadSparse/Chapter02/Section03.lean`): Mathlib has simplicial complexes but nothing
that relates one to a domain `Ω`, and nothing that integrates over its cells. The section also says
that the angles of a mesh "must satisfy certain bounds" for the refinement to stay usable, but it
never writes such a bound down, so there is no shape-regularity condition to state.

**What is.** The one mathematical claim §2.4 does make is that the standard refinement — join the
three midpoints of every triangle, producing four — preserves the angles, so that repeated
refinement of a good triangulation stays good. That is elementary geometry with no triangulation in
sight, and it is `SaadSparse.Chapter02.medialTriangle_angle_eq` and
`SaadSparse.Chapter02.cornerTriangle_angle_eq` below: all four children of `A B C` are similar to
it, because every edge of a child is half of a segment of the parent.

The four children are the *medial* triangle on the three midpoints and the three *corner*
triangles, one at each vertex. The three corner triangles are one statement, not three: the corner
at `B` of `A B C` is the corner at the first vertex of `B A C`, and `midpoint` is symmetric in its
two arguments, so `cornerTriangle_angle_eq B A C` and `cornerTriangle_angle_eq C A B` give the
other two.

## References

Saad, *Iterative Methods for Sparse Linear Systems*, 2nd ed., §2.4 [saad2003iterative]: uniform
midpoint refinement and the preservation of the angles.
-/

open EuclideanGeometry

namespace SaadSparse.Chapter02

variable (A B C : EuclideanSpace ℝ (Fin 2))

/-- Two angles agree as soon as the two pairs of edge vectors are the *same* nonzero multiple of
each other: the triangle at `p₂` is then the image of the one at `q₂` under a homothety, and a
homothety preserves angles. -/
private theorem angle_eq_of_sub_eq_smul {p₁ p₂ p₃ q₁ q₂ q₃ : EuclideanSpace ℝ (Fin 2)} {c : ℝ}
    (hc : c ≠ 0) (h₁ : p₁ - p₂ = c • (q₁ - q₂)) (h₃ : p₃ - p₂ = c • (q₃ - q₂)) :
    ∠ p₁ p₂ p₃ = ∠ q₁ q₂ q₃ := by
  simp only [EuclideanGeometry.angle, vsub_eq_sub, h₁, h₃]
  exact InnerProductGeometry.angle_smul_smul hc _ _

/-- Every edge of the midpoint refinement is half of a segment of the parent triangle: this is the
one computation the section needs, and `module` does it once the midpoints are expanded. -/
private theorem midpoint_sub_midpoint' (a b c d : EuclideanSpace ℝ (Fin 2)) :
    midpoint ℝ a b - midpoint ℝ c d = (2⁻¹ : ℝ) • (a + b - c - d) := by
  simp only [midpoint_eq_smul_add, invOf_eq_inv]
  module

/-- **Saad §2.4**: the medial triangle of the midpoint refinement has the same three angles as the
triangle it refines. Its vertex `midpoint ℝ B C` corresponds to `A`, `midpoint ℝ A C` to `B` and
`midpoint ℝ A B` to `C`; every edge of it is half of a side of `A B C` taken with the opposite
sign, so the medial triangle is the image of `A B C` under the homothety of ratio `-1/2` about the
centroid. -/
theorem medialTriangle_angle_eq :
    ∠ (midpoint ℝ A C) (midpoint ℝ B C) (midpoint ℝ A B) = ∠ B A C ∧
      ∠ (midpoint ℝ B C) (midpoint ℝ A C) (midpoint ℝ A B) = ∠ A B C ∧
      ∠ (midpoint ℝ B C) (midpoint ℝ A B) (midpoint ℝ A C) = ∠ A C B := by
  refine ⟨angle_eq_of_sub_eq_smul (c := -(2⁻¹ : ℝ)) (by norm_num) ?_ ?_,
    angle_eq_of_sub_eq_smul (c := -(2⁻¹ : ℝ)) (by norm_num) ?_ ?_,
    angle_eq_of_sub_eq_smul (c := -(2⁻¹ : ℝ)) (by norm_num) ?_ ?_⟩ <;>
    rw [midpoint_sub_midpoint'] <;> module

/-- **Saad §2.4**: the corner triangle of the midpoint refinement at the vertex `A` — the triangle
`A`, `midpoint ℝ A B`, `midpoint ℝ A C` — has the same three angles as `A B C`, being its image
under the homothety of ratio `1/2` about `A`.

The corner triangles at `B` and at `C` are this statement read at `B A C` and at `C A B`, since
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
