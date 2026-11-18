/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.BottDuffin
import NumlibSurface.BenIsraelGreville.Chapter02.Section07

/-!
# The Bott–Duffin inverse

Section 2.10 of [benIsrael2003generalized] solves the constrained system $Ax+y=b$ with
$x$ in $L$ and $y$ in its orthogonal complement. When $AP_L+I-P_L$ is nonsingular,
the Bott–Duffin inverse gives the unique constrained solution for each right-hand side.
-/

namespace BenIsraelGreville.Chapter02

open Matrix
open scoped InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Definition 3** of [benIsrael2003generalized], Chapter 2. For the orthogonal projector
$P_L$ onto $L$, the Bott–Duffin inverse is $P_L(AP_L+I-P_L)^{-1}$ when the ordinary
inverse exists. -/
noncomputable abbrev definition_3 (A : Matrix n n ℂ) (L : Submodule ℂ (EuclideanSpace ℂ n)) :
    Matrix n n ℂ :=
  A.bottDuffin (orthogonalProjector L)

/-- **Theorem 16** of [benIsrael2003generalized], Chapter 2. When $AP+I-P$ is invertible,
the constrained solution is uniquely $x=Bb$ and $y=(I-AB)b$, where $B$ is the Bott–Duffin
inverse and $P$ projects orthogonally onto $L$. The inverse also satisfies
$BAP=P=PAB$ and $PB=B=BP$. -/
theorem theorem_16 (A : Matrix n n ℂ) (L : Submodule ℂ (EuclideanSpace ℂ n))
    (hU : IsUnit (A * orthogonalProjector L + (1 - orthogonalProjector L))) :
    let P := orthogonalProjector L
    let B := definition_3 A L
    (∀ b : EuclideanSpace ℂ n,
      let x := toEuclideanLin B b
      let y := toEuclideanLin (1 - A * B) b
      (x ∈ L ∧ y ∈ Lᗮ ∧ toEuclideanLin A x + y = b) ∧
        ∀ x' ∈ L, ∀ y' ∈ Lᗮ, toEuclideanLin A x' + y' = b → x' = x ∧ y' = y) ∧
      (B * A * P = P ∧ P * A * B = P ∧ P * B = B ∧ B * P = B) := by
  dsimp only
  let P := orthogonalProjector L
  let M := A * P + (1 - P)
  let B := definition_3 A L
  have hid := isIdempotentElem_orthogonalProjector L
  have hp := toEuclideanLin_orthogonalProjector L
  have hm (v : EuclideanSpace ℂ n) :
      toEuclideanLin M v = toEuclideanLin A (toEuclideanLin P v) +
        (v - toEuclideanLin P v) := by
    change toEuclideanLin (A * P + (1 - P)) v = _
    rw [map_add, LinearMap.add_apply, toEuclideanLin_mul_apply,
      toEuclideanLin_sub_apply, toEuclideanLin_one_apply]
  have hdet := (isUnit_iff_isUnit_det M).mp hU
  refine ⟨?_, bottDuffin_identities hid hU⟩
  intro b
  let u := toEuclideanLin M⁻¹ b
  let x := toEuclideanLin B b
  let y := toEuclideanLin (1 - A * B) b
  have hx : x = toEuclideanLin P u := by
    change toEuclideanLin (P * M⁻¹) b = _
    rw [toEuclideanLin_mul_apply]
  have hy : y = b - toEuclideanLin A x := by
    change toEuclideanLin (1 - A * B) b = _
    rw [toEuclideanLin_sub_apply, toEuclideanLin_one_apply, toEuclideanLin_mul_apply]
  have hsol : toEuclideanLin A x + y = b := by rw [hy, add_sub_cancel]
  have hMu : toEuclideanLin M u = b := by
    change toEuclideanLin M (toEuclideanLin M⁻¹ b) = b
    rw [← toEuclideanLin_mul_apply, mul_nonsing_inv _ hdet, toEuclideanLin_one_apply]
  have hyu : y = u - toEuclideanLin P u := by
    rw [hy, ← hMu, hm, hx, add_sub_cancel_left]
  have hxmem : x ∈ L := by rw [hx, hp]; exact L.starProjection_apply_mem _
  have hymem : y ∈ Lᗮ := by rw [hyu, hp]; exact L.sub_starProjection_mem_orthogonal _
  refine ⟨⟨hxmem, hymem, hsol⟩, ?_⟩
  intro x' hx' y' hy' hxy
  change x' = x ∧ y' = y
  have hproj : toEuclideanLin P (x' + y') = x' := by
    rw [hp, map_add]
    change L.starProjection x' + L.starProjection y' = x'
    rw [L.starProjection_eq_self_iff.mpr hx',
      L.starProjection_apply_eq_zero_iff.mpr hy', add_zero]
  have hu' : toEuclideanLin M (x' + y') = b := by
    rw [hm, hproj, add_sub_cancel_left, hxy]
  have hsum : x' + y' = u := calc
    x' + y' = toEuclideanLin M⁻¹ (toEuclideanLin M (x' + y')) := by
      rw [← toEuclideanLin_mul_apply, nonsing_inv_mul _ hdet, toEuclideanLin_one_apply]
    _ = u := by rw [hu']
  exact ⟨hproj.symm.trans (by rw [hsum, hx]),
    by
      rw [hyu, ← hsum, hproj, add_sub_cancel_left]⟩

/-- **Corollary 12** of [benIsrael2003generalized], Chapter 2. The Bott–Duffin inverse is a
reflexive inverse of $AP$, $PA$, and $PAP$, with range $L$ and kernel $L^\perp$.
Applying it twice at the same subspace gives $PAP$. -/
theorem corollary_12 (A : Matrix n n ℂ) (L : Submodule ℂ (EuclideanSpace ℂ n))
    (hU : IsUnit (A * orthogonalProjector L + (1 - orthogonalProjector L))) :
    let P := orthogonalProjector L
    let B := definition_3 A L
    (∀ C ∈ ({A * P, P * A, P * A * P} : Set (Matrix n n ℂ)),
      C.IsInnerInverse B ∧ C.IsOuterInverse B) ∧
      LinearMap.range (toEuclideanLin B) = L ∧ LinearMap.ker (toEuclideanLin B) = Lᗮ ∧
      IsUnit (B * P + (1 - P)) ∧ definition_3 B L = P * A * P := by
  dsimp only
  let P := orthogonalProjector L
  let B := definition_3 A L
  have hp := toEuclideanLin_orthogonalProjector L
  have hid := isIdempotentElem_orthogonalProjector L
  have ⟨hBAP, hPAB, hPB, hBP⟩ := bottDuffin_identities hid hU
  change B * A * P = P at hBAP
  change P * A * B = P at hPAB
  change P * B = B at hPB
  change B * P = B at hBP
  refine ⟨bottDuffin_reflexive hid hU, ?_, ?_, bottDuffin_bottDuffin hid hU⟩
  · have hRange : LinearMap.range (toEuclideanLin B) =
        LinearMap.range (toEuclideanLin P) := by
      refine le_antisymm ?_ ?_
      · rw [← hPB, toEuclideanLin_mul]
        exact LinearMap.range_comp_le_range _ _
      · rw [← hBAP, mul_assoc B, toEuclideanLin_mul]
        exact LinearMap.range_comp_le_range _ _
    rw [hRange, hp, Submodule.range_starProjection]
  · have hKer : LinearMap.ker (toEuclideanLin B) = LinearMap.ker (toEuclideanLin P) := by
      ext v
      simp only [LinearMap.mem_ker]
      constructor
      · intro hv
        rw [← hPAB, toEuclideanLin_mul_apply, hv, map_zero]
      · intro hv
        rw [← hBP, toEuclideanLin_mul_apply, hv, map_zero]
    rw [hKer, hp, Submodule.ker_starProjection]

end BenIsraelGreville.Chapter02
