/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import NumlibSurface.BenIsraelGreville.Chapter01.Section05
import NumlibSurface.BenIsraelGreville.Chapter01.Section06
import NumlibSurface.BenIsraelGreville.Chapter02.Section07

/-!
# Intersections of affine manifolds

Section 5.3 of [benIsrael2003generalized] characterizes intersections of
translates and describes their canonical representatives by orthogonal
projection.
-/

namespace BenIsraelGreville.Chapter05

open scoped InnerProductSpace

section Affine

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Equation (44)** of [benIsrael2003generalized], Chapter 5. The affine
manifold with base point $f$ and direction $L$ consists of the translates of
$f$ by vectors in $L$. -/
def affineManifold (f : E) (L : Submodule 𝕜 E) : AffineSubspace 𝕜 E :=
  AffineSubspace.mk' f L

/-- Membership in an affine manifold is membership of the difference in its direction. -/
@[simp]
theorem mem_affineManifold {x f : E} {L : Submodule 𝕜 E} :
    x ∈ affineManifold f L ↔ x - f ∈ L := Iff.rfl

/-- **Equation (56)** of [benIsrael2003generalized], Chapter 5. Two translates
intersect exactly when the difference of their base points is in the sum of
their directions. -/
theorem affineManifold_inter_nonempty_iff (f g : E) (L M : Submodule 𝕜 E) :
    ((affineManifold f L : Set E) ∩ (affineManifold g M : Set E)).Nonempty ↔
      g - f ∈ L ⊔ M := by
  constructor
  · rintro ⟨x, hxL, hxM⟩
    have hs := Submodule.sub_mem_sup (mem_affineManifold.mp hxL) (mem_affineManifold.mp hxM)
    convert hs using 1
    abel
  · intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h
    refine ⟨f + y, mem_affineManifold.mpr ?_, mem_affineManifold.mpr ?_⟩
    · simpa [add_comm f y] using hy
    · have he : f + y - g = -z := calc
        f + y - g = y - (g - f) := by abel
        _ = -z := by rw [← hyz]; abel
      exact he ▸ M.neg_mem hz

/-- **Theorem 5** of [benIsrael2003generalized], Chapter 5. At any common point,
the intersection has direction the intersection of the two directions. -/
theorem affineManifold_inter_eq (f g x : E) (L M : Submodule 𝕜 E)
    (hxL : x ∈ affineManifold f L) (hxM : x ∈ affineManifold g M) :
    (affineManifold f L : Set E) ∩ (affineManifold g M : Set E) =
      (affineManifold x (L ⊓ M) : Set E) := by
  have hL : x - f ∈ L := mem_affineManifold.mp hxL
  have hM : x - g ∈ M := mem_affineManifold.mp hxM
  ext y
  change (y - f ∈ L ∧ y - g ∈ M) ↔ (y - x ∈ L ∧ y - x ∈ M)
  have h (S : Submodule 𝕜 E) (a : E) (ha : x - a ∈ S) :
      y - a ∈ S ↔ y - x ∈ S := by
    rw [show y - a = (y - x) + (x - a) by abel]
    exact S.add_mem_iff_left ha
  exact and_congr (h L f hL) (h M g hM)

end Affine

section Orthogonal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- **Equation (45)** of [benIsrael2003generalized], Chapter 5. An orthogonal
representation has its base point perpendicular to the direction. -/
def orthogonalRepresentation (f : E) (L : Submodule 𝕜 E) : Prop :=
  f ∈ Lᗮ

/-- Projecting the base point onto the orthogonal complement gives an
orthogonal representation of the same affine manifold. -/
theorem affineManifold_orthogonalRepresentation (f : E) (L : Submodule 𝕜 E) :
    let p := Lᗮ.starProjection f
    orthogonalRepresentation p L ∧ affineManifold p L = affineManifold f L := by
  dsimp only
  let p := Lᗮ.starProjection f
  have hfp : f - p ∈ L := by
    rw [← L.orthogonal_orthogonal]
    exact Lᗮ.sub_starProjection_mem_orthogonal f
  refine ⟨Lᗮ.starProjection_apply_mem f, ?_⟩
  ext x
  change x - p ∈ L ↔ x - f ∈ L
  rw [show x - p = (x - f) + (f - p) by abel]
  exact L.add_mem_iff_left hfp

/-- **Section 5.3** of [benIsrael2003generalized]. The orthogonal base point
is the unique vector of least norm in its affine manifold. -/
theorem isLeastNorm_orthogonalRepresentation (f : E) (L : Submodule 𝕜 E) :
    let p := Lᗮ.starProjection f
    p ∈ affineManifold f L ∧
      ∀ x ∈ affineManifold f L, ‖p‖ ≤ ‖x‖ ∧ (‖x‖ = ‖p‖ → x = p) := by
  dsimp only
  let p := Lᗮ.starProjection f
  obtain ⟨hp, hrepr⟩ := affineManifold_orthogonalRepresentation f L
  rw [← hrepr]
  refine ⟨AffineSubspace.self_mem_mk' p L, ?_⟩
  intro x hx
  have hOrth : ⟪x - p, p⟫_𝕜 = 0 :=
    L.inner_right_of_mem_orthogonal (mem_affineManifold.mp hx) hp
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x - p) p hOrth
  rw [sub_add_cancel] at hn
  constructor
  · by_contra! h
    have hsq : ‖x‖ ^ 2 < ‖p‖ ^ 2 := by
      nlinarith [norm_nonneg x, norm_nonneg p]
    nlinarith only [hn, hsq, sq_nonneg ‖x - p‖]
  · intro h
    rw [h] at hn
    have hz : ‖x - p‖ = 0 := by
      nlinarith only [hn, norm_nonneg (x - p), sq_nonneg ‖x - p‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- **Corollary 2** of [benIsrael2003generalized], Chapter 5. Every pair of
translates of two directions intersects exactly when their orthogonal
complements have zero intersection. -/
theorem corollary_5_2 (L M : Submodule 𝕜 E) :
    (∀ f g : E, ((affineManifold f L : Set E) ∩ (affineManifold g M : Set E)).Nonempty) ↔
      Lᗮ ⊓ Mᗮ = ⊥ := by
  simp only [affineManifold_inter_nonempty_iff, Submodule.inf_orthogonal,
    Submodule.orthogonal_eq_bot_iff]
  exact ⟨fun h => eq_top_iff.mpr fun x _ => by simpa using h 0 x,
    fun h f g => h ▸ Submodule.mem_top⟩

private theorem ker_add_starProjection (L M : Submodule 𝕜 E) :
    (L.starProjection.toLinearMap + M.starProjection.toLinearMap).ker = Lᗮ ⊓ Mᗮ := by
  ext x
  rw [← L.ker_starProjection, ← M.ker_starProjection]
  change L.starProjection x + M.starProjection x = 0 ↔
    L.starProjection x = 0 ∧ M.starProjection x = 0
  refine ⟨?_, fun ⟨hL, hM⟩ => by rw [hL, hM, add_zero]⟩
  intro h
  have hSq : ‖L.orthogonalProjectionOnto x‖ ^ 2 + ‖M.orthogonalProjectionOnto x‖ ^ 2 = 0 :=
    calc
      _ = RCLike.re ⟪L.starProjection x, x⟫_𝕜 +
          RCLike.re ⟪M.starProjection x, x⟫_𝕜 := by
        rw [L.re_inner_starProjection_eq_normSq, M.re_inner_starProjection_eq_normSq]
      _ = RCLike.re ⟪L.starProjection x + M.starProjection x, x⟫_𝕜 := by
        rw [inner_add_left, map_add]
      _ = 0 := by rw [h]; simp
  obtain ⟨hL, hM⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hSq
  exact ⟨congrArg Subtype.val (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hL)),
    congrArg Subtype.val (norm_eq_zero.mp (eq_zero_of_pow_eq_zero hM))⟩

private theorem range_add_starProjection (L M : Submodule 𝕜 E) :
    (L.starProjection.toLinearMap + M.starProjection.toLinearMap).range = L ⊔ M := by
  let P := L.starProjection.toLinearMap + M.starProjection.toLinearMap
  change P.range = L ⊔ M
  have hSym : P.IsSymmetric := L.starProjection_isSymmetric.add M.starProjection_isSymmetric
  calc
    P.range = P.adjoint.kerᗮ := by
      rw [← LinearMap.orthogonal_range, Submodule.orthogonal_orthogonal]
    _ = L ⊔ M := by
      rw [hSym.adjoint_eq]
      change (L.starProjection.toLinearMap + M.starProjection.toLinearMap).kerᗮ = L ⊔ M
      rw [ker_add_starProjection, Submodule.inf_orthogonal,
        Submodule.orthogonal_orthogonal]

private theorem ker_one_sub_starProjection_mul (L M : Submodule 𝕜 E) :
    ((1 : Module.End 𝕜 E) - L.starProjection.toLinearMap * M.starProjection.toLinearMap).ker =
      L ⊓ M := by
  ext x
  change x - L.starProjection (M.starProjection x) = 0 ↔ x ∈ L ∧ x ∈ M
  rw [sub_eq_zero]
  constructor
  · intro h
    refine ⟨h.symm ▸ L.starProjection_apply_mem _, (M.mem_iff_norm_starProjection x).mpr ?_⟩
    refine le_antisymm (M.norm_starProjection_apply_le x) ?_
    simpa only [← h] using L.norm_starProjection_apply_le (M.starProjection x)
  · rintro ⟨hL, hM⟩
    rw [M.starProjection_eq_self_iff.mpr hM, L.starProjection_eq_self_iff.mpr hL]

/-- **Theorem 4(a)** of [benIsrael2003generalized], Chapter 5. The image of
the kernel of the difference of the two block projections is their common
range. Either block projection gives the same image. -/
theorem theorem_5_4_a (L M : Submodule 𝕜 E) :
    let P := L.starProjection.toLinearMap.comp (LinearMap.fst 𝕜 E E)
    let Q := M.starProjection.toLinearMap.comp (LinearMap.snd 𝕜 E E)
    Submodule.map P (P - Q).ker = L ⊓ M ∧ Submodule.map Q (P - Q).ker = L ⊓ M := by
  dsimp only
  let P := L.starProjection.toLinearMap.comp (LinearMap.fst 𝕜 E E)
  let Q := M.starProjection.toLinearMap.comp (LinearMap.snd 𝕜 E E)
  have hEq {y : E × E} (h : y ∈ (P - Q).ker) : P y = Q y :=
    sub_eq_zero.mp (LinearMap.mem_ker.mp h)
  have hP : Submodule.map P (P - Q).ker = L ⊓ M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨L.starProjection_apply_mem y.1, ?_⟩
      rw [hEq hy]
      exact M.starProjection_apply_mem y.2
    · rintro ⟨hL, hM⟩
      have hPx : P (x, x) = x := L.starProjection_eq_self_iff.mpr hL
      have hQx : Q (x, x) = x := M.starProjection_eq_self_iff.mpr hM
      refine ⟨(x, x), LinearMap.mem_ker.mpr ?_, hPx⟩
      change P (x, x) - Q (x, x) = 0
      rw [hPx, hQx, sub_self]
  refine ⟨hP, ?_⟩
  rw [← hP]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, hEq hy⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (hEq hy).symm⟩

/-- **Theorem 4(b,c)** of [benIsrael2003generalized], Chapter 5. The
intersection is the zero space of the sum of the projections onto the
complements, and the fixed-point space of either order of composition. -/
theorem theorem_5_4 (L M : Submodule 𝕜 E) :
    (Lᗮ.starProjection.toLinearMap + Mᗮ.starProjection.toLinearMap).ker = L ⊓ M ∧
      ((1 : Module.End 𝕜 E) - L.starProjection.toLinearMap * M.starProjection.toLinearMap).ker =
        L ⊓ M ∧
      ((1 : Module.End 𝕜 E) - M.starProjection.toLinearMap * L.starProjection.toLinearMap).ker =
        L ⊓ M := by
  refine ⟨?_, ker_one_sub_starProjection_mul L M, ?_⟩
  · rw [ker_add_starProjection, L.orthogonal_orthogonal, M.orthogonal_orthogonal]
  · rw [ker_one_sub_starProjection_mul, inf_comm]

/-- **Exercise 13** of [benIsrael2003generalized], Chapter 5. Taking
orthogonal complements interchanges sums and intersections of subspaces. -/
theorem exercise_13 (L M : Submodule 𝕜 E) :
    (L ⊓ M)ᗮ = Lᗮ ⊔ Mᗮ ∧ (Lᗮ ⊓ Mᗮ)ᗮ = L ⊔ M := by
  have h : (Lᗮ ⊔ Mᗮ)ᗮ = L ⊓ M := by
    rw [← Submodule.inf_orthogonal, L.orthogonal_orthogonal, M.orthogonal_orthogonal]
  constructor
  · rw [← h, Submodule.orthogonal_orthogonal]
  · rw [Submodule.inf_orthogonal, Submodule.orthogonal_orthogonal]

end Orthogonal

section ProjectorFormulas

open Matrix Chapter02

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Lemma 2** of [benIsrael2003generalized], Chapter 5. The sum of the two
orthogonal projectors has range equal to the sum of their ranges. Its two
products with its Moore–Penrose inverse are the projector onto that sum. -/
theorem lemma_5_2 (L M : Submodule ℂ (EuclideanSpace ℂ n)) :
    let S := orthogonalProjector L + orthogonalProjector M
    orthogonalProjector (L ⊔ M) = S * S.pinv ∧
      orthogonalProjector (L ⊔ M) = S.pinv * S := by
  let S := orthogonalProjector L + orthogonalProjector M
  change orthogonalProjector (L ⊔ M) = S * S.pinv ∧
    orthogonalProjector (L ⊔ M) = S.pinv * S
  have hSym : S.IsHermitian :=
    (isHermitian_orthogonalProjector L).add (isHermitian_orthogonalProjector M)
  have hRange : (toEuclideanLin S).range = L ⊔ M := by
    simpa only [← toEuclideanLin_orthogonalProjector, ← map_add] using
      range_add_starProjection L M
  constructor
  · apply toEuclideanLin.injective
    rw [toEuclideanLin_orthogonalProjector, S.mul_pinv_eq_starProjection]
    exact congrArg (fun T : Submodule ℂ (EuclideanSpace ℂ n) =>
      T.starProjection.toLinearMap) hRange.symm
  · apply toEuclideanLin.injective
    rw [toEuclideanLin_orthogonalProjector, S.pinv_mul_eq_starProjection]
    exact congrArg (fun T : Submodule ℂ (EuclideanSpace ℂ n) => T.starProjection.toLinearMap)
      ((congrArg (fun A : Matrix n n ℂ => (toEuclideanLin A).range) hSym.eq).trans hRange).symm

/-- Orthogonal projectors onto nested subspaces compose to the smaller
projector in either order. -/
theorem orthogonalProjector_mul_of_le {L M : Submodule ℂ (EuclideanSpace ℂ n)}
    (h : L ≤ M) :
    orthogonalProjector L * orthogonalProjector M = orthogonalProjector L ∧
      orthogonalProjector M * orthogonalProjector L = orthogonalProjector L := by
  constructor
  · apply toEuclideanLin.injective
    rw [toEuclideanLin_mul, toEuclideanLin_orthogonalProjector, toEuclideanLin_orthogonalProjector]
    exact congrArg ContinuousLinearMap.toLinearMap
      (Submodule.starProjection_comp_starProjection_of_le h)
  · apply toEuclideanLin.injective
    rw [toEuclideanLin_mul, toEuclideanLin_orthogonalProjector, toEuclideanLin_orthogonalProjector]
    exact LinearMap.ext fun x => M.starProjection_eq_self_iff.mpr (h (L.starProjection_apply_mem x))

/-- **Theorem 3** of [benIsrael2003generalized], Chapter 5. The orthogonal
projector onto the intersection is twice the parallel sum of the two
orthogonal projectors. -/
theorem theorem_5_3 (L M : Submodule ℂ (EuclideanSpace ℂ n)) :
    let P := orthogonalProjector L
    let Q := orthogonalProjector M
    let D := (P + Q).pinv
    orthogonalProjector (L ⊓ M) = (2 : ℂ) • (P * D * Q) ∧
      orthogonalProjector (L ⊓ M) = (2 : ℂ) • (Q * D * P) := by
  let P := orthogonalProjector L
  let Q := orthogonalProjector M
  let D := (P + Q).pinv
  let H := P * D * Q
  let R := orthogonalProjector (L ⊓ M)
  change R = (2 : ℂ) • H ∧ R = (2 : ℂ) • (Q * D * P)
  have ⟨hSum, hSum'⟩ := lemma_5_2 L M
  change orthogonalProjector (L ⊔ M) = (P + Q) * D at hSum
  change orthogonalProjector (L ⊔ M) = D * (P + Q) at hSum'
  have hQ₁ : (P + Q) * D * Q = Q := by
    rw [← hSum]
    exact (orthogonalProjector_mul_of_le (L := M) le_sup_right).2
  have hQ₂ : Q * D * (P + Q) = Q := by
    rw [Matrix.mul_assoc, ← hSum']
    exact (orthogonalProjector_mul_of_le (L := M) le_sup_right).1
  have hPQ : H = Q * D * P := by
    simp only [Matrix.add_mul] at hQ₁
    rw [Matrix.mul_add] at hQ₂
    exact add_right_cancel (hQ₁.trans hQ₂.symm)
  have hRH : R * H = H := by
    apply toEuclideanLin.injective
    refine LinearMap.ext fun x => ?_
    rw [toEuclideanLin_mul_apply, show R = orthogonalProjector (L ⊓ M) from rfl,
      toEuclideanLin_orthogonalProjector]
    apply (L ⊓ M).starProjection_eq_self_iff.mpr
    constructor
    · rw [show H = orthogonalProjector L * (D * Q) by simp [H, P, Matrix.mul_assoc],
        toEuclideanLin_mul_apply, toEuclideanLin_orthogonalProjector]
      exact L.starProjection_apply_mem _
    · rw [hPQ, Matrix.mul_assoc, show Q = orthogonalProjector M from rfl,
        toEuclideanLin_mul_apply, toEuclideanLin_orthogonalProjector]
      exact M.starProjection_apply_mem _
  have hRP : R * P = R := (orthogonalProjector_mul_of_le inf_le_left).1
  have hRQ : R * Q = R := (orthogonalProjector_mul_of_le inf_le_right).1
  have hR : (2 : ℂ) • H = R := calc
    (2 : ℂ) • H = R * H + R * (Q * D * P) := by rw [two_smul, ← hPQ, hRH]
    _ = (R * P) * D * Q + (R * Q) * D * P := by simp only [H, Matrix.mul_assoc]
    _ = R * (D * (P + Q)) := by rw [hRP, hRQ]; simp [Matrix.mul_add, Matrix.mul_assoc, add_comm]
    _ = R := by
      rw [← hSum']
      exact (orthogonalProjector_mul_of_le (inf_le_left.trans le_sup_left)).1
  exact ⟨hR.symm, hPQ ▸ hR.symm⟩

private theorem affineManifold_inter_eq_pinv
    {f g z b : EuclideanSpace ℂ n} {L M : Submodule ℂ (EuclideanSpace ℂ n)}
    (A : Matrix n n ℂ) (hKer : (toEuclideanLin A).ker = L ⊓ M)
    (hzL : z ∈ affineManifold f L) (hzM : z ∈ affineManifold g M)
    (hz : toEuclideanLin A (z - f) = b) :
    (affineManifold f L : Set _) ∩ (affineManifold g M : Set _) =
      (affineManifold (f + toEuclideanLin A.pinv b) (L ⊓ M) : Set (EuclideanSpace ℂ n)) := by
  let x := f + toEuclideanLin A.pinv b
  have hSolve : toEuclideanLin A (toEuclideanLin A.pinv b) = b := by
    rw [← hz, ← toEuclideanLin_mul_apply A.pinv A, ← toEuclideanLin_mul_apply,
      ← Matrix.mul_assoc, A.mul_pinv_mul_self]
  have hDiff : x - z ∈ L ⊓ M := by
    rw [← hKer, LinearMap.mem_ker, show x - z = toEuclideanLin A.pinv b - (z - f) by
      dsimp only [x]
      abel, map_sub, hSolve, hz, sub_self]
  refine affineManifold_inter_eq f g x L M (mem_affineManifold.mpr ?_) (mem_affineManifold.mpr ?_)
  · rw [show x - f = (x - z) + (z - f) by abel]
    exact L.add_mem hDiff.1 (mem_affineManifold.mp hzL)
  · rw [show x - g = (x - z) + (z - g) by abel]
    exact M.add_mem hDiff.2 (mem_affineManifold.mp hzM)

private theorem orthogonalProjector_sum_pinv_apply (L M : Submodule ℂ (EuclideanSpace ℂ n))
    (d : EuclideanSpace ℂ n) (hd : d ∈ L ⊔ M) :
    let P := orthogonalProjector L
    let Q := orthogonalProjector M
    let D := (P + Q).pinv
    let v := toEuclideanLin D d
    toEuclideanLin P v + toEuclideanLin Q v = d := by
  dsimp only
  rw [← LinearMap.add_apply, ← map_add, ← toEuclideanLin_mul_apply, ← (lemma_5_2 L M).1,
    toEuclideanLin_orthogonalProjector]
  exact (L ⊔ M).starProjection_eq_self_iff.mpr hd

/-- **Theorem 5(a,b,c)** of [benIsrael2003generalized], Chapter 5. If the
translates intersect, three pseudoinverse formulas give base points of the
same affine manifold, with direction $L\cap M$. -/
theorem theorem_5_5 (f g : EuclideanSpace ℂ n) (L M : Submodule ℂ (EuclideanSpace ℂ n))
    (hd : g - f ∈ L ⊔ M) :
    let P := orthogonalProjector L
    let Q := orthogonalProjector M
    let U := orthogonalProjector Lᗮ
    let V := orthogonalProjector Mᗮ
    let d := g - f
    let I := (affineManifold f L).carrier ∩ (affineManifold g M).carrier
    I = (affineManifold (f + toEuclideanLin (P * (P + Q).pinv) d) (L ⊓ M)).carrier ∧
      I = (affineManifold (f + toEuclideanLin ((U + V).pinv * V) d) (L ⊓ M)).carrier ∧
      I = (affineManifold (f + toEuclideanLin ((1 - Q * P).pinv * V) d) (L ⊓ M)).carrier := by
  dsimp only
  let P := orthogonalProjector L
  let Q := orthogonalProjector M
  let U := orthogonalProjector Lᗮ
  let V := orthogonalProjector Mᗮ
  let d := g - f
  let D := (P + Q).pinv
  let v := toEuclideanLin D d
  let x := f + toEuclideanLin P v
  let N := U + V
  let R := 1 - Q * P
  have hSum : toEuclideanLin P v + toEuclideanLin Q v = d :=
    orthogonalProjector_sum_pinv_apply L M d hd
  have hxL : x ∈ affineManifold f L := by
    apply mem_affineManifold.mpr
    rw [show x - f = toEuclideanLin P v by dsimp only [x]; abel,
      show P = orthogonalProjector L from rfl, toEuclideanLin_orthogonalProjector]
    exact L.starProjection_apply_mem v
  have hxM : x ∈ affineManifold g M := by
    apply mem_affineManifold.mpr
    rw [show x - g = toEuclideanLin P v - d by dsimp only [x, d]; abel, ← hSum,
      show Q = orthogonalProjector M from rfl, toEuclideanLin_orthogonalProjector]
    simp
  have hFirst := affineManifold_inter_eq f g x L M hxL hxM
  have hNu : toEuclideanLin N =
      Lᗮ.starProjection.toLinearMap + Mᗮ.starProjection.toLinearMap := by
    change toEuclideanLin (orthogonalProjector Lᗮ + orthogonalProjector Mᗮ) = _
    rw [map_add, toEuclideanLin_orthogonalProjector, toEuclideanLin_orthogonalProjector]
  have hRu : toEuclideanLin R =
      (1 : Module.End ℂ (EuclideanSpace ℂ n)) -
        M.starProjection.toLinearMap * L.starProjection.toLinearMap := by
    change toEuclideanLin (1 - orthogonalProjector M * orthogonalProjector L) = _
    rw [map_sub, toEuclideanLin_one, toEuclideanLin_mul,
      toEuclideanLin_orthogonalProjector, toEuclideanLin_orthogonalProjector]
    rfl
  have hNKer : (toEuclideanLin N).ker = L ⊓ M := by rw [hNu, (theorem_5_4 L M).1]
  have hRKer : (toEuclideanLin R).ker = L ⊓ M := by rw [hRu, (theorem_5_4 L M).2.2]
  have hxDiff : toEuclideanLin V (x - f) = toEuclideanLin V d := by
    have h : Mᗮ.starProjection (x - g) = 0 :=
      M.starProjection_orthogonal_apply_eq_zero (mem_affineManifold.mp hxM)
    rw [show x - g = (x - f) - d by dsimp only [d]; abel, map_sub, sub_eq_zero] at h
    rw [show V = orthogonalProjector Mᗮ from rfl, toEuclideanLin_orthogonalProjector]
    exact h
  have hNx : toEuclideanLin N (x - f) = toEuclideanLin V d := by
    change toEuclideanLin (U + V) (x - f) = _
    rw [map_add, LinearMap.add_apply, show U = orthogonalProjector Lᗮ from rfl,
      toEuclideanLin_orthogonalProjector]
    change Lᗮ.starProjection (x - f) + toEuclideanLin V (x - f) = _
    rw [L.starProjection_orthogonal_apply_eq_zero (mem_affineManifold.mp hxL), zero_add]
    exact hxDiff
  have hRx : toEuclideanLin R (x - f) = toEuclideanLin V d := by
    rw [hRu]
    change (x - f) - M.starProjection (L.starProjection (x - f)) = _
    rw [L.starProjection_eq_self_iff.mpr (mem_affineManifold.mp hxL),
      ← M.starProjection_orthogonal_val]
    rw [show V = orthogonalProjector Mᗮ from rfl, toEuclideanLin_orthogonalProjector]
      at hxDiff ⊢
    exact hxDiff
  refine ⟨?_, ?_, ?_⟩
  · simpa only [x, v, P, D, Q, d, toEuclideanLin_mul_apply, AffineSubspace.carrier_eq_coe]
      using hFirst
  · simpa only [N, U, V, d, toEuclideanLin_mul_apply, AffineSubspace.carrier_eq_coe] using
      affineManifold_inter_eq_pinv N hNKer hxL hxM hNx
  · simpa only [R, V, Q, P, d, toEuclideanLin_mul_apply, AffineSubspace.carrier_eq_coe] using
      affineManifold_inter_eq_pinv R hRKer hxL hxM hRx

/-- **Theorem 5(a′,b′,c′)** of [benIsrael2003generalized], Chapter 5. The
same base-point formulas can start from the second translate. -/
theorem theorem_5_5_swapped (f g : EuclideanSpace ℂ n)
    (L M : Submodule ℂ (EuclideanSpace ℂ n))
    (hd : g - f ∈ L ⊔ M) :
    let P := orthogonalProjector L
    let Q := orthogonalProjector M
    let U := orthogonalProjector Lᗮ
    let V := orthogonalProjector Mᗮ
    let d := g - f
    let I := (affineManifold f L).carrier ∩ (affineManifold g M).carrier
    I = (affineManifold (g - toEuclideanLin (Q * (P + Q).pinv) d) (L ⊓ M)).carrier ∧
      I = (affineManifold (g - toEuclideanLin ((U + V).pinv * U) d) (L ⊓ M)).carrier ∧
      I = (affineManifold (g - toEuclideanLin ((1 - P * Q).pinv * U) d) (L ⊓ M)).carrier := by
  have h : f - g ∈ M ⊔ L := by
    rw [sup_comm, ← neg_sub]
    exact (L ⊔ M).neg_mem hd
  have he := theorem_5_5 g f M L h
  dsimp only at he ⊢
  rw [Set.inter_comm, inf_comm] at he
  rw [add_comm (orthogonalProjector M), add_comm (orthogonalProjector Mᗮ)] at he
  simpa only [show f - g = -(g - f) by abel, map_neg, ← sub_eq_add_neg] using he

/-- **Equation (62)** of [benIsrael2003generalized], Chapter 5. The first
formula gives the same base point from either translate. -/
theorem equation_62 (f g : EuclideanSpace ℂ n) (L M : Submodule ℂ (EuclideanSpace ℂ n))
    (hd : g - f ∈ L ⊔ M) :
    let P := orthogonalProjector L
    let Q := orthogonalProjector M
    let D := (P + Q).pinv
    let d := g - f
    f + toEuclideanLin (P * D) d = g - toEuclideanLin (Q * D) d := by
  dsimp only
  rw [eq_sub_iff_add_eq, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, add_assoc,
    orthogonalProjector_sum_pinv_apply L M _ hd]
  abel

private theorem pinv_apply_mem_ker_orthogonal (A : Matrix n n ℂ) (b : EuclideanSpace ℂ n) :
    toEuclideanLin A.pinv b ∈ (toEuclideanLin A).kerᗮ := by
  rw [LinearMap.orthogonal_ker, ← toEuclideanLin_conjTranspose_eq_adjoint]
  have h : toEuclideanLin (A.pinv * A) (toEuclideanLin A.pinv b) = toEuclideanLin A.pinv b := by
    rw [← toEuclideanLin_mul_apply, A.pinv_mul_self_mul_pinv]
  rw [← h, A.pinv_mul_eq_starProjection]
  exact Submodule.starProjection_apply_mem _ _

/-- **Corollary 1(a,b)** of [benIsrael2003generalized], Chapter 5. The first
two formulas give orthogonal representations when both inputs are orthogonal. -/
theorem corollary_5_1 {f g : EuclideanSpace ℂ n} {L M : Submodule ℂ (EuclideanSpace ℂ n)}
    (hf : orthogonalRepresentation f L) (hg : orthogonalRepresentation g M)
    (hd : g - f ∈ L ⊔ M) :
    let P := orthogonalProjector L
    let Q := orthogonalProjector M
    let U := orthogonalProjector Lᗮ
    let V := orthogonalProjector Mᗮ
    let d := g - f
    orthogonalRepresentation (f + toEuclideanLin (P * (P + Q).pinv) d) (L ⊓ M) ∧
      orthogonalRepresentation (f + toEuclideanLin ((U + V).pinv * V) d) (L ⊓ M) := by
  let P := orthogonalProjector L
  let Q := orthogonalProjector M
  let R := orthogonalProjector (L ⊓ M)
  let U := orthogonalProjector Lᗮ
  let V := orthogonalProjector Mᗮ
  let d := g - f
  let v := toEuclideanLin (P + Q).pinv d
  have hF : f ∈ (L ⊓ M)ᗮ := Submodule.orthogonal_le inf_le_left hf
  have hG : g ∈ (L ⊓ M)ᗮ := Submodule.orthogonal_le inf_le_right hg
  have hRZero (y : EuclideanSpace ℂ n) : toEuclideanLin R y = 0 ↔ y ∈ (L ⊓ M)ᗮ := by
    change toEuclideanLin (orthogonalProjector (L ⊓ M)) y = 0 ↔ _
    rw [toEuclideanLin_orthogonalProjector]
    exact (L ⊓ M).starProjection_apply_eq_zero_iff
  have hD : toEuclideanLin R d = 0 := (hRZero d).mpr ((L ⊓ M)ᗮ.sub_mem hG hF)
  have hRP : R * P = R := (orthogonalProjector_mul_of_le inf_le_left).1
  have hRQ : R * Q = R := (orthogonalProjector_mul_of_le inf_le_right).1
  have hSum : toEuclideanLin P v + toEuclideanLin Q v = d :=
    orthogonalProjector_sum_pinv_apply L M d hd
  have hRv := congrArg (toEuclideanLin R) hSum
  rw [map_add, ← toEuclideanLin_mul_apply R P, ← toEuclideanLin_mul_apply R Q,
    hRP, hRQ, hD] at hRv
  have hv : toEuclideanLin R v = 0 :=
    (smul_eq_zero.mp (show (2 : ℂ) • toEuclideanLin R v = 0 by rwa [two_smul])).resolve_left
      two_ne_zero
  change f + toEuclideanLin (P * (P + Q).pinv) d ∈ (L ⊓ M)ᗮ ∧
    f + toEuclideanLin ((U + V).pinv * V) d ∈ (L ⊓ M)ᗮ
  constructor
  · refine (L ⊓ M)ᗮ.add_mem hF ((hRZero _).mp ?_)
    rw [← toEuclideanLin_mul_apply, ← Matrix.mul_assoc, hRP, toEuclideanLin_mul_apply]
    exact hv
  · have hNU : (toEuclideanLin (U + V)).ker = L ⊓ M := by
      change (toEuclideanLin (orthogonalProjector Lᗮ + orthogonalProjector Mᗮ)).ker = _
      rw [map_add, toEuclideanLin_orthogonalProjector, toEuclideanLin_orthogonalProjector]
      exact (theorem_5_4 L M).1
    refine (L ⊓ M)ᗮ.add_mem hF ?_
    rw [toEuclideanLin_mul_apply, ← hNU]
    exact pinv_apply_mem_ker_orthogonal (U + V) _

/-- **Corollary 1(a′,b′)** of [benIsrael2003generalized], Chapter 5.
The first two formulas starting from the second input are also orthogonal. -/
theorem corollary_5_1_swapped {f g : EuclideanSpace ℂ n}
    {L M : Submodule ℂ (EuclideanSpace ℂ n)}
    (hf : orthogonalRepresentation f L) (hg : orthogonalRepresentation g M)
    (hd : g - f ∈ L ⊔ M) :
    let P := orthogonalProjector L
    let Q := orthogonalProjector M
    let U := orthogonalProjector Lᗮ
    let V := orthogonalProjector Mᗮ
    let d := g - f
    orthogonalRepresentation (g - toEuclideanLin (Q * (P + Q).pinv) d) (L ⊓ M) ∧
      orthogonalRepresentation (g - toEuclideanLin ((U + V).pinv * U) d) (L ⊓ M) := by
  have he : f - g ∈ M ⊔ L := by
    rw [sup_comm, ← neg_sub]
    exact (L ⊔ M).neg_mem hd
  have h := corollary_5_1 hg hf he
  dsimp only at h ⊢
  rw [inf_comm, add_comm (orthogonalProjector M), add_comm (orthogonalProjector Mᗮ)] at h
  simpa only [show f - g = -(g - f) by abel, map_neg, ← sub_eq_add_neg] using h

private theorem pinv_eq_adjoint_mul_gram_pinv {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix n m ℂ) : A.pinv = Aᴴ * (A * Aᴴ).pinv := by
  have hp : (A * Aᴴ).pinv ∈ Chapter01.definition_1 (A * Aᴴ) {.inner} :=
    Chapter01.mem_one_iff.mpr (A * Aᴴ).mul_pinv_mul_self
  have h := Chapter01.theorem_3_b A hp
  rw [mem_penroseInverses_iff] at h
  refine (A.pinv_unique (h .inner (by simp)) (h .outer (by simp)) ?_
    (h .hermitianMulRev (by simp))).symm
  rw [← Matrix.mul_assoc]
  exact (A * Aᴴ).isHermitian_mul_pinv

/-- **Exercise 12** of [benIsrael2003generalized], Chapter 5, Equation (70).
Either sign in the block row gives the same Gram matrix, with the sign
retained in the leading block column of the Moore–Penrose formula. -/
theorem exercise_12 (L M : Submodule ℂ (EuclideanSpace ℂ n)) :
    let P := orthogonalProjector L
    let Q := orthogonalProjector M
    (fromCols P Q).pinv = fromRows P Q * (P + Q).pinv ∧
      (fromCols P (-Q)).pinv = fromRows P (-Q) * (P + Q).pinv := by
  dsimp only
  have hP := (isHermitian_orthogonalProjector L).eq
  have hQ := (isHermitian_orthogonalProjector M).eq
  have hPP := (isIdempotentElem_orthogonalProjector L).eq
  have hQQ := (isIdempotentElem_orthogonalProjector M).eq
  constructor <;> rw [pinv_eq_adjoint_mul_gram_pinv] <;>
    simp [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows,
      hP, hQ, hPP, hQQ]

end ProjectorFormulas

section PalindromicProjectors

open Matrix Chapter02
open scoped ComplexOrder Topology InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Equation (71)** of [benIsrael2003generalized], Chapter 5.
The first member of the list gives the two outer projector factors.
The empty product is the identity and the one-projector product simplifies
by idempotence. -/
noncomputable def palindromicProjectorProduct :
    List (Submodule ℂ (EuclideanSpace ℂ n)) → Matrix n n ℂ
  | [] => 1
  | L :: Ls => orthogonalProjector L * palindromicProjectorProduct Ls * orthogonalProjector L

@[simp]
theorem palindromicProjectorProduct_nil :
    palindromicProjectorProduct ([] : List (Submodule ℂ (EuclideanSpace ℂ n))) = 1 := rfl

@[simp]
theorem palindromicProjectorProduct_cons
    (L : Submodule ℂ (EuclideanSpace ℂ n))
    (Ls : List (Submodule ℂ (EuclideanSpace ℂ n))) :
    palindromicProjectorProduct (L :: Ls) =
      orthogonalProjector L * palindromicProjectorProduct Ls * orthogonalProjector L := rfl

private theorem toEuclideanLin_palindromicProjectorProduct_cons
    (L : Submodule ℂ (EuclideanSpace ℂ n))
    (Ls : List (Submodule ℂ (EuclideanSpace ℂ n))) (x : EuclideanSpace ℂ n) :
    toEuclideanLin (palindromicProjectorProduct (L :: Ls)) x =
      L.starProjection (toEuclideanLin (palindromicProjectorProduct Ls)
        (L.starProjection x)) := by
  rw [palindromicProjectorProduct_cons, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    toEuclideanLin_orthogonalProjector]
  rfl

/-- The palindrome is positive semidefinite by repeated projector congruence. -/
theorem palindromicProjectorProduct_posSemidef
    (Ls : List (Submodule ℂ (EuclideanSpace ℂ n))) :
    (palindromicProjectorProduct Ls).PosSemidef := by
  induction Ls with
  | nil => simpa only [palindromicProjectorProduct_nil] using
      (PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef)
  | cons L Ls h =>
    simpa only [palindromicProjectorProduct_cons, (isHermitian_orthogonalProjector L).eq] using
      h.conjTranspose_mul_mul_same (orthogonalProjector L)

/-- The palindrome is a contraction for the Euclidean norm. -/
theorem norm_palindromicProjectorProduct_le
    (Ls : List (Submodule ℂ (EuclideanSpace ℂ n))) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanLin (palindromicProjectorProduct Ls) x‖ ≤ ‖x‖ := by
  induction Ls generalizing x with
  | nil => simp
  | cons L Ls h =>
    rw [toEuclideanLin_palindromicProjectorProduct_cons]
    exact (L.norm_starProjection_apply_le _).trans ((h _).trans (L.norm_starProjection_apply_le x))

private theorem palindromicProjectorProduct_apply_of_mem
    (Ls : List (Submodule ℂ (EuclideanSpace ℂ n))) (x : EuclideanSpace ℂ n)
    (hx : ∀ L ∈ Ls, x ∈ L) :
    toEuclideanLin (palindromicProjectorProduct Ls) x = x := by
  induction Ls with
  | nil => simp
  | cons L Ls ih =>
    have hL := L.starProjection_eq_self_iff.mpr (hx L List.mem_cons_self)
    rw [toEuclideanLin_palindromicProjectorProduct_cons, hL,
      ih (fun M hm => hx M (List.mem_cons_of_mem L hm)), hL]

private theorem mem_of_norm_palindromicProjectorProduct_eq
    (Ls : List (Submodule ℂ (EuclideanSpace ℂ n))) (x : EuclideanSpace ℂ n)
    (hx : ‖toEuclideanLin (palindromicProjectorProduct Ls) x‖ = ‖x‖) :
    ∀ L ∈ Ls, x ∈ L := by
  induction Ls generalizing x with
  | nil => simp
  | cons L Ls ih =>
    rw [toEuclideanLin_palindromicProjectorProduct_cons] at hx
    have hP : ‖L.starProjection x‖ = ‖x‖ := le_antisymm (L.norm_starProjection_apply_le _) <|
      hx.symm.le.trans ((L.norm_starProjection_apply_le _).trans
        (norm_palindromicProjectorProduct_le Ls _))
    have hL := (L.mem_iff_norm_starProjection x).mpr hP
    rw [L.starProjection_eq_self_iff.mpr hL] at hx
    have ht : ‖toEuclideanLin (palindromicProjectorProduct Ls) x‖ = ‖x‖ :=
      le_antisymm (norm_palindromicProjectorProduct_le Ls _) <|
        hx.symm.le.trans (L.norm_starProjection_apply_le _)
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hM
    · exact hL
    · exact ih x ht M hM

/-- The vectors fixed by the palindrome form the intersection of the given subspaces. -/
theorem palindromicProjectorProduct_apply_eq_self_iff
    (Ls : List (Submodule ℂ (EuclideanSpace ℂ n))) (x : EuclideanSpace ℂ n) :
    toEuclideanLin (palindromicProjectorProduct Ls) x = x ↔
      x ∈ sInf {L | L ∈ Ls} := by
  rw [Submodule.mem_sInf]
  exact ⟨fun hx => mem_of_norm_palindromicProjectorProduct_eq Ls x (congrArg norm hx),
    palindromicProjectorProduct_apply_of_mem Ls x⟩

private theorem palindromic_eigenvalues_mem_Icc
    (Ls : List (Submodule ℂ (EuclideanSpace ℂ n))) (i : n) :
    (palindromicProjectorProduct_posSemidef Ls).isHermitian.eigenvalues i ∈ Set.Icc 0 1 := by
  let h := palindromicProjectorProduct_posSemidef Ls
  let x := h.isHermitian.eigenvectorBasis i
  let eigenvalue := h.isHermitian.eigenvalues i
  have heigen : 0 ≤ eigenvalue := h.eigenvalues_nonneg i
  have hEig : toEuclideanLin (palindromicProjectorProduct Ls) x = (eigenvalue : ℂ) • x := by
    apply WithLp.ofLp_injective 2
    simpa only [ofLp_toEuclideanLin, WithLp.ofLp_smul, RCLike.real_smul_eq_coe_smul
      (K := ℂ), RCLike.ofReal_eq_complex_ofReal] using h.isHermitian.mulVec_eigenvectorBasis i
  have hx : ‖x‖ = 1 := h.isHermitian.eigenvectorBasis.orthonormal.1 i
  have he := norm_palindromicProjectorProduct_le Ls x
  rw [hEig, norm_smul, Complex.norm_real, Real.norm_of_nonneg heigen, hx, mul_one] at he
  exact ⟨heigen, he⟩

private theorem toEuclideanLin_eigenvector_conjugate_diagonal
    {Q : Matrix n n ℂ} (h : Q.IsHermitian) (d : n → ℂ) (i : n) :
    toEuclideanLin (Unitary.conjStarAlgAut ℂ _ h.eigenvectorUnitary (diagonal d))
      (h.eigenvectorBasis i) = d i • h.eigenvectorBasis i := by
  apply WithLp.ofLp_injective 2
  rw [ofLp_toEuclideanLin, WithLp.ofLp_smul, Unitary.conjStarAlgAut_apply,
    ← mulVec_mulVec, ← mulVec_mulVec, h.star_eigenvectorUnitary_mulVec,
    Matrix.diagonal_mulVec_single, show Pi.single i (d i * 1) = d i • Pi.single i 1 from
      Pi.single_smul' i (d i) (1 : ℂ), mulVec_smul, h.eigenvectorUnitary_mulVec]

private theorem palindromic_projector_eq_conjugate_diagonal
    (Ls : List (Submodule ℂ (EuclideanSpace ℂ n))) :
    let h := (palindromicProjectorProduct_posSemidef Ls).isHermitian
    orthogonalProjector (sInf {L | L ∈ Ls}) =
      Unitary.conjStarAlgAut ℂ _ h.eigenvectorUnitary
        (diagonal fun i => if h.eigenvalues i = 1 then 1 else 0) := by
  dsimp only
  let Q := palindromicProjectorProduct Ls
  let H : Submodule ℂ (EuclideanSpace ℂ n) := sInf {L | L ∈ Ls}
  let h := (palindromicProjectorProduct_posSemidef Ls).isHermitian
  let d (i : n) : ℂ := if h.eigenvalues i = 1 then 1 else 0
  change orthogonalProjector H = Unitary.conjStarAlgAut ℂ _ h.eigenvectorUnitary (diagonal d)
  apply toEuclideanLin.injective
  apply h.eigenvectorBasis.toBasis.ext
  intro i
  change toEuclideanLin (orthogonalProjector H) (h.eigenvectorBasis i) =
    toEuclideanLin (Unitary.conjStarAlgAut ℂ _ h.eigenvectorUnitary (diagonal d))
      (h.eigenvectorBasis i)
  rw [toEuclideanLin_orthogonalProjector, toEuclideanLin_eigenvector_conjugate_diagonal]
  let x := h.eigenvectorBasis i
  have hEig : toEuclideanLin Q x = (h.eigenvalues i : ℂ) • x := by
    apply WithLp.ofLp_injective 2
    simpa only [ofLp_toEuclideanLin, WithLp.ofLp_smul, RCLike.real_smul_eq_coe_smul
      (K := ℂ), RCLike.ofReal_eq_complex_ofReal] using h.mulVec_eigenvectorBasis i
  change H.starProjection x = d i • x
  by_cases hi : h.eigenvalues i = 1
  · rw [hi, Complex.ofReal_one, one_smul] at hEig
    have hx : x ∈ H := (palindromicProjectorProduct_apply_eq_self_iff Ls x).mp hEig
    simp [d, hi, H.starProjection_eq_self_iff.mpr hx]
  · simp only [d, ite_eq_right hi, zero_smul]
    apply H.starProjection_apply_eq_zero_iff.mpr
    apply (H.mem_orthogonal x).mpr
    intro y hy
    have hy' := (palindromicProjectorProduct_apply_eq_self_iff Ls y).mpr hy
    have hsym := (isSymmetric_toEuclideanLin_iff.mpr h) y x
    change ⟪toEuclideanLin Q y, x⟫_ℂ = ⟪y, toEuclideanLin Q x⟫_ℂ at hsym
    rw [hy', hEig, inner_smul_right] at hsym
    have hm : ((h.eigenvalues i : ℂ) - 1) * ⟪y, x⟫_ℂ = 0 := by
      rw [sub_mul, one_mul, ← hsym, sub_self]
    have hne : (h.eigenvalues i : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hi)
    exact (mul_eq_zero.mp hm).resolve_left hne

open Filter in
/-- **Exercise 14** of [benIsrael2003generalized], Chapter 5.
The powers of the palindromic product tend to the orthogonal projector
onto the common subspace. -/
theorem exercise_14 (Ls : List (Submodule ℂ (EuclideanSpace ℂ n))) :
    Tendsto (fun k : ℕ => palindromicProjectorProduct Ls ^ k) atTop
      (𝓝 (orthogonalProjector (sInf {L | L ∈ Ls}))) := by
  let h := (palindromicProjectorProduct_posSemidef Ls).isHermitian
  let f := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) h.eigenvectorUnitary
  let z (i : n) : ℂ := h.eigenvalues i
  let d (i : n) : ℂ := if h.eigenvalues i = 1 then 1 else 0
  have hQ : palindromicProjectorProduct Ls = f (diagonal z) := h.spectral_theorem
  have hf : Continuous f := by
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hd : Tendsto (fun k : ℕ => diagonal (fun i => z i ^ k)) atTop (𝓝 (diagonal d)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq]
      by_cases hi : h.eigenvalues i = 1
      · simp [z, d, hi]
      · have hI := palindromic_eigenvalues_mem_Icc Ls i
        have hz : ‖z i‖ < 1 := by
          change ‖(h.eigenvalues i : ℂ)‖ < 1
          rw [Complex.norm_real, Real.norm_of_nonneg hI.1]
          exact lt_of_le_of_ne hI.2 hi
        simpa [d, hi] using tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz
    · simp [diagonal_apply_ne _ hij]
  have hPower (k : ℕ) : palindromicProjectorProduct Ls ^ k =
      f (diagonal fun i => z i ^ k) := by
    rw [hQ, ← map_pow, diagonal_pow]
    rfl
  rw [palindromic_projector_eq_conjugate_diagonal Ls]
  simp_rw [hPower]
  exact hf.continuousAt.tendsto.comp hd

/-- **Exercise 15** of [benIsrael2003generalized], Chapter 5.
The eigenvalues lie in the unit interval, and the spectral projector at
one is the orthogonal projector onto the common subspace. This subspace
is nonzero exactly when one is an eigenvalue. -/
theorem exercise_15 (Ls : List (Submodule ℂ (EuclideanSpace ℂ n))) :
    let h := (palindromicProjectorProduct_posSemidef Ls).isHermitian
    (∀ i, h.eigenvalues i ∈ Set.Icc 0 1) ∧
      ((sInf {L | L ∈ Ls} : Submodule ℂ (EuclideanSpace ℂ n)) ≠ ⊥ ↔
        ∃ i, h.eigenvalues i = 1) ∧
      orthogonalProjector (sInf {L | L ∈ Ls}) =
        Unitary.conjStarAlgAut ℂ _ h.eigenvectorUnitary
          (diagonal fun i => if h.eigenvalues i = 1 then 1 else 0) := by
  dsimp only
  let h := (palindromicProjectorProduct_posSemidef Ls).isHermitian
  let H : Submodule ℂ (EuclideanSpace ℂ n) := sInf {L | L ∈ Ls}
  have hP := palindromic_projector_eq_conjugate_diagonal Ls
  refine ⟨palindromic_eigenvalues_mem_Icc Ls, ?_, hP⟩
  constructor
  · intro hH
    by_contra! hs
    have hz : orthogonalProjector H = 0 := by
      rw [hP]
      simp [hs]
    apply hH
    rw [Submodule.eq_bot_iff]
    intro x hx
    have he : H.starProjection x = x := H.starProjection_eq_self_iff.mpr hx
    rwa [← show (toEuclideanLin (orthogonalProjector H)) x = H.starProjection x from
      DFunLike.congr_fun (toEuclideanLin_orthogonalProjector H) x,
      hz, map_zero, LinearMap.zero_apply, eq_comm] at he
  · rintro ⟨i, hi⟩ hH
    have hp :
        toEuclideanLin (orthogonalProjector H) (h.eigenvectorBasis i) = h.eigenvectorBasis i := by
      rw [hP, toEuclideanLin_eigenvector_conjugate_diagonal, ite_eq_left hi, one_smul]
    have hx : h.eigenvectorBasis i ∈ H := by
      rw [toEuclideanLin_orthogonalProjector] at hp
      exact H.starProjection_eq_self_iff.mp hp
    have hz : h.eigenvectorBasis i ≠ 0 := (h.eigenvectorBasis.toBasis.ne_zero i)
    change H = ⊥ at hH
    rw [hH, Submodule.mem_bot] at hx
    exact hz hx

/-- The complex spectrum of the palindrome is contained in the real unit interval. -/
theorem spectrum_palindromicProjectorProduct (Ls : List (Submodule ℂ (EuclideanSpace ℂ n))) :
    spectrum ℂ (palindromicProjectorProduct Ls) ⊆ Complex.ofReal '' Set.Icc 0 1 := by
  let h := (palindromicProjectorProduct_posSemidef Ls).isHermitian
  have he := h.spectral_theorem
  rw [he, Unitary.conjStarAlgAut_apply, Unitary.spectrum_star_right_conjugate, spectrum_diagonal]
  rintro z ⟨i, rfl⟩
  exact ⟨h.eigenvalues i, palindromic_eigenvalues_mem_Icc Ls i, rfl⟩

private theorem pinv_conjugate_unitary (U : unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).pinv = Unitary.conjStarAlgAut ℂ _ U A.pinv := by
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_eq_conjTranspose,
    conjTranspose_conjTranspose] using
    Chapter01.pinv_unitary_mul A (U : Matrix n n ℂ) ((star U : unitaryGroup n ℂ) : Matrix n n ℂ)
      U.prop (star U).prop

private theorem pyle_scalar (t : ℝ) (k : ℕ) (he : 0 < k ∨ t ≠ 0) :
    t ^ (k + 1) + ((t ^ (k + 1 + 1) - t ^ (k + 1))⁻¹ -
      (t ^ (k + 1) - t ^ k)⁻¹)⁻¹ = if t = 1 then 1 else 0 := by
  by_cases h1 : t = 1
  · simp [h1]
  by_cases h0 : t = 0
  · obtain hk | ht := he
    · simp [h0, Nat.ne_of_gt hk]
    · exact (ht h0).elim
  have hk : t ^ k ≠ 0 := pow_ne_zero _ h0
  have ht : t - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hUpper : t ^ (k + 1 + 1) - t ^ (k + 1) = t ^ k * t * (t - 1) := by
    rw [pow_succ, pow_succ t k]
    ring
  have hLower : t ^ (k + 1) - t ^ k = t ^ k * (t - 1) := by
    rw [pow_succ]
    ring
  have hDiff : (t ^ k * t * (t - 1))⁻¹ - (t ^ k * (t - 1))⁻¹ = -(t ^ k * t)⁻¹ := by
    field_simp
    ring
  rw [hUpper, hLower, hDiff, inv_neg, inv_inv, pow_succ, add_neg_cancel, ite_eq_right h1]

/-- **Exercise 16**, Equation (72) of [benIsrael2003generalized], Chapter 5.
Three successive powers and their Moore–Penrose inverses give the
orthogonal projector onto the common subspace. The exponent $k+1$
can be one when the palindromic product is invertible. -/
theorem exercise_16 (Ls : List (Submodule ℂ (EuclideanSpace ℂ n))) (k : ℕ)
    (hk : 0 < k ∨ IsUnit (palindromicProjectorProduct Ls)) :
    let Q := palindromicProjectorProduct Ls
    orthogonalProjector (sInf {L | L ∈ Ls}) =
      Q ^ (k + 1) + ((Q ^ (k + 1 + 1) - Q ^ (k + 1)).pinv -
        (Q ^ (k + 1) - Q ^ k).pinv).pinv := by
  dsimp only
  let h := (palindromicProjectorProduct_posSemidef Ls).isHermitian
  let f := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) h.eigenvectorUnitary
  let z (i : n) : ℂ := h.eigenvalues i
  let d (i : n) : ℂ := if h.eigenvalues i = 1 then 1 else 0
  have hQ : palindromicProjectorProduct Ls = f (diagonal z) := h.spectral_theorem
  have hPower (a : ℕ) : palindromicProjectorProduct Ls ^ a =
      f (diagonal fun i => z i ^ a) := by
    rw [hQ, ← map_pow, diagonal_pow]
    rfl
  have hNz (i : n) : 0 < k ∨ h.eigenvalues i ≠ 0 := by
    rcases hk with hk | hQunit
    · exact Or.inl hk
    · apply Or.inr
      have hD : IsUnit (diagonal z) := (isUnit_map_iff f _).mp (hQ ▸ hQunit)
      have hDet := isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp hD)
      rw [det_diagonal] at hDet
      have hz := Finset.prod_ne_zero_iff.mp hDet i (Finset.mem_univ i)
      exact fun hi => hz (by simp [z, hi])
  rw [palindromic_projector_eq_conjugate_diagonal Ls]
  change f (diagonal d) = _
  rw [hPower, hPower, hPower]
  simp only [f, ← map_sub, pinv_conjugate_unitary, ← map_add, diagonal_sub,
    Chapter01.pinv_diagonal, diagonal_add]
  apply congrArg (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) h.eigenvectorUnitary)
  apply congrArg diagonal
  funext i
  have he := congrArg Complex.ofReal (pyle_scalar (h.eigenvalues i) k (hNz i))
  by_cases hi : h.eigenvalues i = 1
  · simp [z, d, hi]
  · simpa [z, d, hi, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_pow,
      Complex.ofReal_inv] using he.symm

end PalindromicProjectors

end BenIsraelGreville.Chapter05
