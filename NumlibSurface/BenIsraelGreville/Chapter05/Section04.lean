/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter05.Section03
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Common solutions of partitioned linear systems

Section 5.4 of [benIsrael2003generalized] describes the common solutions of
two systems by intersecting their affine solution spaces. The resulting
formulas give generalized inverses of vertically stacked matrices.

## Deviations from the source

* **Exercise 19** (correction). The concatenated reciprocals have numerator
  $[5,2;5,4]$ over ten. The printed intermediate multiplication repeats
  the numerator of the Gram sum.
-/

namespace BenIsraelGreville.Chapter05

open Matrix Chapter02

variable {m p n : Type*} [Fintype m] [Fintype p] [Fintype n]
  [DecidableEq m] [DecidableEq p] [DecidableEq n]

/-- **Equations (48a)–(48b)** of [benIsrael2003generalized], Chapter 5. The
solutions of a consistent equation form the translate of the kernel by the
minimum-norm solution. -/
theorem solutionSet_eq_affineManifold (A : Matrix m n ℂ) (a : EuclideanSpace ℂ m)
    (ha : a ∈ (toEuclideanLin A).range) :
    {x | toEuclideanLin A x = a} =
      (affineManifold (toEuclideanLin A.pinv a) (toEuclideanLin A).ker).carrier := by
  have hf : toEuclideanLin A (toEuclideanLin A.pinv a) = a := by
    obtain ⟨y, rfl⟩ := ha
    change toEuclideanLin A (toEuclideanLin A.pinv (toEuclideanLin A y)) = toEuclideanLin A y
    rw [← toEuclideanLin_mul_apply A.pinv A, ← toEuclideanLin_mul_apply,
      ← Matrix.mul_assoc, A.mul_pinv_mul_self]
  ext x
  change toEuclideanLin A x = a ↔ toEuclideanLin A (x - toEuclideanLin A.pinv a) = 0
  rw [map_sub, hf, sub_eq_zero]

omit [DecidableEq m] in
/-- The orthogonal projector onto the complement of the kernel is
the product of the Moore–Penrose inverse with the matrix. -/
theorem orthogonalProjector_kerComplement_eq_pinv_mul (A : Matrix m n ℂ) :
    orthogonalProjector ((toEuclideanLin A).kerᗮ) = A.pinv * A := by
  classical
  apply toEuclideanLin.injective
  rw [toEuclideanLin_orthogonalProjector, A.pinv_mul_eq_starProjection]
  have h : (toEuclideanLin A).kerᗮ = (toEuclideanLin Aᴴ).range := by
    rw [LinearMap.orthogonal_ker, toEuclideanLin_conjTranspose_eq_adjoint]
  exact congrArg (fun L : Submodule ℂ (EuclideanSpace ℂ n) => L.starProjection.toLinearMap) h

omit [DecidableEq m] in
/-- The projector onto the kernel is the complementary projector to
the product of the Moore–Penrose inverse with the matrix. -/
theorem orthogonalProjector_ker_eq_one_sub_pinv_mul (A : Matrix m n ℂ) :
    orthogonalProjector ((toEuclideanLin A).ker) = 1 - A.pinv * A := by
  rw [← orthogonalProjector_kerComplement_eq_pinv_mul, ← Chapter02.exercise_56,
    Submodule.orthogonal_orthogonal]

private theorem pinv_apply_mem_kerComplement (A : Matrix m n ℂ) (a : EuclideanSpace ℂ m) :
    toEuclideanLin A.pinv a ∈ (toEuclideanLin A).kerᗮ := by
  have h : toEuclideanLin (A.pinv * A) (toEuclideanLin A.pinv a) = toEuclideanLin A.pinv a := by
    rw [← toEuclideanLin_mul_apply, A.pinv_mul_self_mul_pinv]
  rw [← orthogonalProjector_kerComplement_eq_pinv_mul, toEuclideanLin_orthogonalProjector] at h
  exact ((toEuclideanLin A).kerᗮ.starProjection_eq_self_iff).mp h

/-- **Corollary 3** of [benIsrael2003generalized], Chapter 5. The difference of
the two minimum-norm solutions tests consistency of the joint system. If the
test holds, each of the three formulas gives a base point for its solution set. -/
theorem corollary_5_3 (A : Matrix m n ℂ) (B : Matrix p n ℂ)
    (a : EuclideanSpace ℂ m) (b : EuclideanSpace ℂ p)
    (ha : a ∈ (toEuclideanLin A).range) (hb : b ∈ (toEuclideanLin B).range) :
    let L := (toEuclideanLin A).ker
    let M := (toEuclideanLin B).ker
    let P := orthogonalProjector L
    let Q := orthogonalProjector M
    let f := toEuclideanLin A.pinv a
    let g := toEuclideanLin B.pinv b
    let d := g - f
    let Z := (A.pinv * A + B.pinv * B).pinv
    let S := {x | toEuclideanLin A x = a ∧ toEuclideanLin B x = b}
    (S.Nonempty ↔ d ∈ L ⊔ M) ∧ (d ∈ L ⊔ M →
      S = (affineManifold (f + toEuclideanLin (P * (P + Q).pinv) d) (L ⊓ M)).carrier ∧
      S = (affineManifold (g - toEuclideanLin (Q * (P + Q).pinv) d) (L ⊓ M)).carrier ∧
      S = (affineManifold (toEuclideanLin Z (f + g)) (L ⊓ M)).carrier) := by
  let L := (toEuclideanLin A).ker
  let M := (toEuclideanLin B).ker
  let P := orthogonalProjector L
  let Q := orthogonalProjector M
  let U := orthogonalProjector Lᗮ
  let V := orthogonalProjector Mᗮ
  let W := U + V
  let f := toEuclideanLin A.pinv a
  let g := toEuclideanLin B.pinv b
  let d := g - f
  let S := {x | toEuclideanLin A x = a ∧ toEuclideanLin B x = b}
  have hS : S = (affineManifold f L).carrier ∩ (affineManifold g M).carrier := by
    change {x | toEuclideanLin A x = a} ∩ {x | toEuclideanLin B x = b} = _
    rw [solutionSet_eq_affineManifold A a ha, solutionSet_eq_affineManifold B b hb]
  change (S.Nonempty ↔ d ∈ L ⊔ M) ∧ _
  refine ⟨by rw [hS, AffineSubspace.carrier_eq_coe, AffineSubspace.carrier_eq_coe,
    affineManifold_inter_nonempty_iff], fun hd => ?_⟩
  refine ⟨hS.trans (theorem_5_5 f g L M hd).1, hS.trans (theorem_5_5_swapped f g L M hd).1, ?_⟩
  have hU : U = A.pinv * A := orthogonalProjector_kerComplement_eq_pinv_mul A
  have hV : V = B.pinv * B := orthogonalProjector_kerComplement_eq_pinv_mul B
  have hUf : toEuclideanLin U f = f := by
    rw [hU]
    change toEuclideanLin (A.pinv * A) (toEuclideanLin A.pinv a) = _
    rw [← toEuclideanLin_mul_apply, A.pinv_mul_self_mul_pinv]
  have hVg : toEuclideanLin V g = g := by
    rw [hV]
    change toEuclideanLin (B.pinv * B) (toEuclideanLin B.pinv b) = _
    rw [← toEuclideanLin_mul_apply, B.pinv_mul_self_mul_pinv]
  have hWf : toEuclideanLin W f = f + toEuclideanLin V f := by
    change toEuclideanLin (U + V) f = _
    rw [map_add, LinearMap.add_apply, hUf]
  have hProj : toEuclideanLin (W.pinv * W) f = f := by
    change toEuclideanLin ((U + V).pinv * (U + V)) f = f
    rw [← (lemma_5_2 Lᗮ Mᗮ).2, toEuclideanLin_orthogonalProjector]
    exact (Lᗮ ⊔ Mᗮ).starProjection_eq_self_iff.mpr
      (Submodule.mem_sup_left (pinv_apply_mem_kerComplement A a))
  have hAB : f + toEuclideanLin (W.pinv * V) d = toEuclideanLin W.pinv (f + g) := by
    have hf : f = toEuclideanLin W.pinv f + toEuclideanLin W.pinv (toEuclideanLin V f) := calc
      f = toEuclideanLin (W.pinv * W) f := hProj.symm
      _ = _ := by rw [toEuclideanLin_mul_apply, hWf, map_add]
    change f + toEuclideanLin (W.pinv * V) (g - f) = _
    rw [toEuclideanLin_mul_apply, map_sub, hVg, map_sub, map_add]
    calc
      _ = (toEuclideanLin W.pinv f + toEuclideanLin W.pinv (toEuclideanLin V f)) +
          (toEuclideanLin W.pinv g - toEuclideanLin W.pinv (toEuclideanLin V f)) := by
        rw [← hf]
      _ = _ := by abel
  have h := (theorem_5_5 f g L M hd).2.1
  change _ = (affineManifold (f + toEuclideanLin (W.pinv * V) d) (L ⊓ M)).carrier at h
  rw [hAB] at h
  refine hS.trans (h.trans ?_)
  rw [show W = A.pinv * A + B.pinv * B by change U + V = _; rw [hU, hV]]

omit [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p] in
/-- The null space of a vertical block matrix is the intersection of the null spaces. -/
theorem ker_toEuclideanLin_fromRows (A : Matrix m n ℂ) (B : Matrix p n ℂ) :
    (toEuclideanLin (fromRows A B)).ker = (toEuclideanLin A).ker ⊓ (toEuclideanLin B).ker := by
  ext x
  change toEuclideanLin (fromRows A B) x = 0 ↔ toEuclideanLin A x = 0 ∧ toEuclideanLin B x = 0
  have hz : Sum.elim (0 : m → ℂ) (0 : p → ℂ) = 0 := by
    ext i
    cases i <;> rfl
  simp only [toEuclideanLin_apply, WithLp.toLp_eq_zero, fromRows_mulVec, ← hz, Sum.elim_eq_iff]

omit [DecidableEq m] in
private theorem projector_mul_pinv_eq_zero {L : Submodule ℂ (EuclideanSpace ℂ n)}
    (A : Matrix m n ℂ) (h : L ≤ (toEuclideanLin A).ker) :
    orthogonalProjector L * A.pinv = 0 := by
  classical
  apply toEuclideanLin.injective
  refine LinearMap.ext fun x => ?_
  rw [toEuclideanLin_mul_apply, toEuclideanLin_orthogonalProjector, map_zero, LinearMap.zero_apply]
  exact L.starProjection_apply_eq_zero_iff.mpr (Submodule.orthogonal_le h
    (pinv_apply_mem_kerComplement A x))

private theorem projector_mul_pinv_sub (L M : Submodule ℂ (EuclideanSpace ℂ n)) :
    let P := orthogonalProjector L
    let Q := orthogonalProjector M
    P * (P + Q).pinv * (P - Q) = P - orthogonalProjector (L ⊓ M) := by
  let P := orthogonalProjector L
  let Q := orthogonalProjector M
  let D := (P + Q).pinv
  let R := orthogonalProjector (L ⊓ M)
  change P * D * (P - Q) = P - R
  have hSum := (lemma_5_2 L M).2
  change orthogonalProjector (L ⊔ M) = D * (P + Q) at hSum
  have hInner : P * D * (P + Q) = P := by
    rw [Matrix.mul_assoc, ← hSum]
    exact (orthogonalProjector_mul_of_le (L := L) le_sup_left).1
  have hInter : R = (2 : ℂ) • (P * D * Q) := (theorem_5_3 L M).1
  calc
    P * D * (P - Q) = P * D * (P + Q) - (2 : ℂ) • (P * D * Q) := by
      rw [Matrix.mul_sub, Matrix.mul_add, two_smul]
      abel
    _ = P - R := by rw [hInner, ← hInter]

private theorem projector_inter_mul_pinv_sum (L M : Submodule ℂ (EuclideanSpace ℂ n)) :
    let P := orthogonalProjector L
    let Q := orthogonalProjector M
    let R := orthogonalProjector (L ⊓ M)
    (2 : ℂ) • (R * (P + Q).pinv) = R := by
  let P := orthogonalProjector L
  let Q := orthogonalProjector M
  let R := orthogonalProjector (L ⊓ M)
  let D := (P + Q).pinv
  change (2 : ℂ) • (R * D) = R
  have hRP : R * P = R := (orthogonalProjector_mul_of_le inf_le_left).1
  have hRQ : R * Q = R := (orthogonalProjector_mul_of_le inf_le_right).1
  have hSum := (lemma_5_2 L M).1
  change orthogonalProjector (L ⊔ M) = (P + Q) * D at hSum
  calc
    (2 : ℂ) • (R * D) = R * (P + Q) * D := by
      rw [two_smul, Matrix.mul_add, hRP, hRQ, Matrix.add_mul]
    _ = R := by
      rw [Matrix.mul_assoc, ← hSum]
      exact (orthogonalProjector_mul_of_le (inf_le_left.trans le_sup_left)).1

private def leftBlockVector (v : EuclideanSpace ℂ (m ⊕ p)) : EuclideanSpace ℂ m :=
  WithLp.toLp 2 (WithLp.ofLp v ∘ Sum.inl)

private def rightBlockVector (v : EuclideanSpace ℂ (m ⊕ p)) : EuclideanSpace ℂ p :=
  WithLp.toLp 2 (WithLp.ofLp v ∘ Sum.inr)

omit [Fintype n] [DecidableEq n] in
private theorem toEuclideanLin_fromCols_apply (X : Matrix n m ℂ) (Y : Matrix n p ℂ)
    (v : EuclideanSpace ℂ (m ⊕ p)) :
    toEuclideanLin (fromCols X Y) v =
      toEuclideanLin X (leftBlockVector v) + toEuclideanLin Y (rightBlockVector v) := by
  apply WithLp.ofLp_injective 2
  simp only [ofLp_toEuclideanLin, WithLp.ofLp_add, leftBlockVector, rightBlockVector]
  rw [← Sum.elim_comp_inl_inr (WithLp.ofLp v), fromCols_mulVec_sumElim,
    Sum.elim_comp_inl, Sum.elim_comp_inr]

private theorem pinv_apply_eq_zero_of_adjoint_apply_eq_zero (A : Matrix m n ℂ)
    (v : EuclideanSpace ℂ m) (hv : toEuclideanLin Aᴴ v = 0) :
    toEuclideanLin A.pinv v = 0 := by
  have hp : toEuclideanLin (A * A.pinv) v = 0 := by
    rw [A.mul_pinv_eq_starProjection]
    change (toEuclideanLin A).range.starProjection v = 0
    rw [Submodule.starProjection_apply_eq_zero_iff, LinearMap.orthogonal_range,
      ← toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.mem_ker]
    exact hv
  have h := congrArg (toEuclideanLin A.pinv) hp
  rw [← toEuclideanLin_mul_apply, ← Matrix.mul_assoc, A.pinv_mul_self_mul_pinv, map_zero] at h
  exact h

private theorem eq_pinv_of_mul_eq_and_ker_le (C : Matrix (m ⊕ p) n ℂ)
    (X : Matrix n (m ⊕ p) ℂ) (hX : X * C = C.pinv * C)
    (hKer : (toEuclideanLin Cᴴ).ker ≤ (toEuclideanLin X).ker) : X = C.pinv := by
  apply toEuclideanLin.injective
  refine LinearMap.ext fun v => ?_
  let w := toEuclideanLin (C * C.pinv) v
  have h : v - w ∈ (toEuclideanLin Cᴴ).ker := by
    rw [toEuclideanLin_conjTranspose_eq_adjoint, ← LinearMap.orthogonal_range]
    change v - toEuclideanLin (C * C.pinv) v ∈ (toEuclideanLin C).rangeᗮ
    rw [C.mul_pinv_eq_starProjection]
    exact (toEuclideanLin C).range.sub_starProjection_mem_orthogonal v
  calc
    toEuclideanLin X v = toEuclideanLin X (w + (v - w)) := by
      congr 1
      abel
    _ = toEuclideanLin X w := by rw [map_add, LinearMap.mem_ker.mp (hKer h), add_zero]
    _ = toEuclideanLin C.pinv v := by
      change toEuclideanLin X (toEuclideanLin (C * C.pinv) v) = _
      rw [← toEuclideanLin_mul_apply, ← Matrix.mul_assoc, hX, C.pinv_mul_self_mul_pinv]

/-- **Theorem 6** of [benIsrael2003generalized], Chapter 5, Equations (77)–(80).
The three row-partition formulas give reflexive generalized inverses with a
Hermitian right product. They are Moore–Penrose inverses when the two row
spaces have zero intersection. -/
theorem theorem_5_6 (A : Matrix m n ℂ) (B : Matrix p n ℂ) :
    let C := fromRows A B
    let P := orthogonalProjector ((toEuclideanLin A).ker)
    let Q := orthogonalProjector ((toEuclideanLin B).ker)
    let T := fromCols (-A.pinv) B.pinv
    let X := fromCols A.pinv (0 : Matrix n p ℂ) + P * (P + Q).pinv * T
    let Y := fromCols (0 : Matrix n m ℂ) B.pinv - Q * (P + Q).pinv * T
    let Z := (A.pinv * A + B.pinv * B).pinv * fromCols A.pinv B.pinv
    let s : Set PenroseCondition := {.inner, .outer, .hermitianMulRev}
    X ∈ Chapter01.definition_1 C s ∧ Y ∈ Chapter01.definition_1 C s ∧
      Z ∈ Chapter01.definition_1 C s ∧
        ((toEuclideanLin Aᴴ).range ⊓ (toEuclideanLin Bᴴ).range = ⊥ →
          X = C.pinv ∧ Y = C.pinv ∧ Z = C.pinv) := by
  let C := fromRows A B
  let L := (toEuclideanLin A).ker
  let M := (toEuclideanLin B).ker
  let P := orthogonalProjector L
  let Q := orthogonalProjector M
  let R := orthogonalProjector (L ⊓ M)
  let D := (P + Q).pinv
  let U := A.pinv * A
  let V := B.pinv * B
  let W := U + V
  let F := fromCols A.pinv (0 : Matrix n p ℂ)
  let H := fromCols (0 : Matrix n m ℂ) B.pinv
  let T := fromCols (-A.pinv) B.pinv
  let J := fromCols A.pinv B.pinv
  let X := F + P * D * T
  let Y := H - Q * D * T
  let Z := W.pinv * J
  let s : Set PenroseCondition := {.inner, .outer, .hermitianMulRev}
  change X ∈ Chapter01.definition_1 C s ∧ Y ∈ Chapter01.definition_1 C s ∧
    Z ∈ Chapter01.definition_1 C s ∧
      ((toEuclideanLin Aᴴ).range ⊓ (toEuclideanLin Bᴴ).range = ⊥ →
        X = C.pinv ∧ Y = C.pinv ∧ Z = C.pinv)
  have hP : P = 1 - U := orthogonalProjector_ker_eq_one_sub_pinv_mul A
  have hQ : Q = 1 - V := orthogonalProjector_ker_eq_one_sub_pinv_mul B
  have hTC : T * C = P - Q := by
    rw [show T * C = (-A.pinv) * A + B.pinv * B from fromCols_mul_fromRows _ _ _ _,
      Matrix.neg_mul, hP, hQ]
    change -U + V = (1 - U) - (1 - V)
    abel
  have hFC : F * C = U := by simp [F, C, U, fromCols_mul_fromRows]
  have hHC : H * C = V := by simp [H, C, V, fromCols_mul_fromRows]
  have hJC : J * C = W := fromCols_mul_fromRows _ _ _ _
  have hXC : X * C = 1 - R := by
    change (F + P * D * T) * C = _
    rw [Matrix.add_mul, hFC, Matrix.mul_assoc (P * D), hTC]
    have he : P * D * (P - Q) = P - R := projector_mul_pinv_sub L M
    rw [he, hP]
    abel
  have hYC : Y * C = 1 - R := by
    change (H - Q * D * T) * C = _
    rw [Matrix.sub_mul, hHC, Matrix.mul_assoc (Q * D), hTC]
    have he : Q * D * (Q - P) = Q - R := by
      have he := projector_mul_pinv_sub M L
      change Q * (Q + P).pinv * (Q - P) = Q - orthogonalProjector (M ⊓ L) at he
      rw [add_comm Q P, inf_comm M L] at he
      exact he
    rw [show P - Q = -(Q - P) by abel, mul_neg, he, hQ]
    abel
  have hZC₀ : Z * C = W.pinv * W := by
    change W.pinv * J * C = _
    rw [Matrix.mul_assoc, hJC]
  have hZC : Z * C = 1 - R := calc
    Z * C = W.pinv * W := hZC₀
    _ = orthogonalProjector (Lᗮ ⊔ Mᗮ) := by
      rw [show W = orthogonalProjector Lᗮ + orthogonalProjector Mᗮ by
        exact congrArg₂ (· + ·) (orthogonalProjector_kerComplement_eq_pinv_mul A).symm
          (orthogonalProjector_kerComplement_eq_pinv_mul B).symm]
      exact (lemma_5_2 Lᗮ Mᗮ).2.symm
    _ = 1 - R := by rw [← (exercise_13 L M).1]; exact Chapter02.exercise_56 (L ⊓ M)
  have hRA : R * A.pinv = 0 := projector_mul_pinv_eq_zero A inf_le_left
  have hRB : R * B.pinv = 0 := projector_mul_pinv_eq_zero B inf_le_right
  have hRF : R * F = 0 := by simp [F, mul_fromCols, hRA]
  have hRH : R * H = 0 := by simp [H, mul_fromCols, hRB]
  have hRT : R * T = 0 := by simp [T, mul_fromCols, hRA, hRB]
  have hRDT : R * D * T = 0 := by
    apply (smul_eq_zero.mp (show (2 : ℂ) • (R * D * T) = 0 from ?_)).resolve_left two_ne_zero
    rw [two_smul, ← Matrix.add_mul, ← two_smul ℂ, projector_inter_mul_pinv_sum L M, hRT]
  have hRX : R * X = 0 := by
    change R * (F + P * D * T) = _
    rw [Matrix.mul_add, hRF, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      (orthogonalProjector_mul_of_le (L := L ⊓ M) inf_le_left).1, hRDT, zero_add]
  have hRY : R * Y = 0 := by
    change R * (H - Q * D * T) = _
    rw [Matrix.mul_sub, hRH, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      (orthogonalProjector_mul_of_le (L := L ⊓ M) inf_le_right).1, hRDT, sub_self]
  have hZOuter : Z * C * Z = Z := by
    rw [hZC₀]
    change W.pinv * W * (W.pinv * J) = _
    rw [← Matrix.mul_assoc, W.pinv_mul_self_mul_pinv]
  have hRZ : R * Z = 0 := by
    rwa [hZC, Matrix.sub_mul, Matrix.one_mul, sub_eq_self] at hZOuter
  have hProj : C.pinv * C = 1 - R := calc
    C.pinv * C = orthogonalProjector (toEuclideanLin C).kerᗮ :=
      (orthogonalProjector_kerComplement_eq_pinv_mul C).symm
    _ = 1 - R := by
      rw [show (toEuclideanLin C).ker = L ⊓ M from ker_toEuclideanLin_fromRows A B]
      exact Chapter02.exercise_56 (L ⊓ M)
  have hClass (N : Matrix n (m ⊕ p) ℂ) (hNC : N * C = 1 - R) (hRN : R * N = 0) :
      N ∈ Chapter01.definition_1 C s := by
    rw [mem_penroseInverses_iff]
    change ∀ c ∈ ({.inner, .outer, .hermitianMulRev} : Set PenroseCondition), c.Holds C N
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_, ?_⟩
    · change C * N * C = C
      rw [Matrix.mul_assoc, hNC, ← hProj, ← Matrix.mul_assoc, C.mul_pinv_mul_self]
    · change N * C * N = N
      rw [hNC, Matrix.sub_mul, Matrix.one_mul, hRN, sub_zero]
    · change (N * C).IsHermitian
      rw [hNC]
      exact isHermitian_one.sub (isHermitian_orthogonalProjector (L ⊓ M))
  refine ⟨hClass X hXC hRX, hClass Y hYC hRY, hClass Z hZC hRZ, ?_⟩
  intro hRange
  have hBlocks (v : EuclideanSpace ℂ (m ⊕ p)) (hv : v ∈ (toEuclideanLin Cᴴ).ker) :
      toEuclideanLin A.pinv (leftBlockVector v) = 0 ∧
        toEuclideanLin B.pinv (rightBlockVector v) = 0 := by
    have hCv := LinearMap.mem_ker.mp hv
    rw [show Cᴴ = fromCols Aᴴ Bᴴ by
      simp [C, conjTranspose_fromRows_eq_fromCols_conjTranspose],
      toEuclideanLin_fromCols_apply] at hCv
    have hA₀ : toEuclideanLin Aᴴ (leftBlockVector v) = 0 := by
      have hMem : toEuclideanLin Aᴴ (leftBlockVector v) ∈
          (toEuclideanLin Aᴴ).range ⊓ (toEuclideanLin Bᴴ).range := by
        refine ⟨LinearMap.mem_range_self _ _, ?_⟩
        rw [eq_neg_iff_add_eq_zero.mpr hCv]
        exact Submodule.neg_mem _ (LinearMap.mem_range_self _ _)
      rwa [hRange, Submodule.mem_bot] at hMem
    have hB₀ : toEuclideanLin Bᴴ (rightBlockVector v) = 0 := by
      rwa [hA₀, zero_add] at hCv
    exact ⟨pinv_apply_eq_zero_of_adjoint_apply_eq_zero A _ hA₀,
      pinv_apply_eq_zero_of_adjoint_apply_eq_zero B _ hB₀⟩
  refine ⟨eq_pinv_of_mul_eq_and_ker_le C X (hXC.trans hProj.symm) ?_,
    eq_pinv_of_mul_eq_and_ker_le C Y (hYC.trans hProj.symm) ?_,
    eq_pinv_of_mul_eq_and_ker_le C Z (hZC.trans hProj.symm) ?_⟩
  all_goals
    intro v hv
    obtain ⟨ha, hb⟩ := hBlocks v hv
    apply LinearMap.mem_ker.mpr
    simp [X, Y, Z, F, H, T, J, toEuclideanLin_fromCols_apply, ha, hb]

omit [DecidableEq m] [DecidableEq n] in
/-- **Equation (89)** of [benIsrael2003generalized], Chapter 5. Taking
adjoints preserves the first two Penrose equations and interchanges the two
Hermitian-product conditions. -/
theorem equation_89 (A : Matrix m n ℂ) (X : Matrix n m ℂ) :
    (Aᴴ.IsInnerInverse Xᴴ ↔ A.IsInnerInverse X) ∧
      (Aᴴ.IsOuterInverse Xᴴ ↔ A.IsOuterInverse X) ∧
      ((Aᴴ * Xᴴ).IsHermitian ↔ (X * A).IsHermitian) ∧
      ((Xᴴ * Aᴴ).IsHermitian ↔ (A * X).IsHermitian) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      Aᴴ.IsInnerInverse Xᴴ ↔ (A * X * A)ᴴ = Aᴴ := by
        simp only [isInnerInverse_iff, conjTranspose_mul, Matrix.mul_assoc]
      _ ↔ A.IsInnerInverse X := conjTranspose_injective.eq_iff
  · calc
      Aᴴ.IsOuterInverse Xᴴ ↔ (X * A * X)ᴴ = Xᴴ := by
        simp only [isOuterInverse_iff, conjTranspose_mul, Matrix.mul_assoc]
      _ ↔ A.IsOuterInverse X := conjTranspose_injective.eq_iff
  · rw [← conjTranspose_mul, isHermitian_conjTranspose_iff]
  · rw [← conjTranspose_mul, isHermitian_conjTranspose_iff]

omit [DecidableEq m] [DecidableEq n] in
private theorem adjoint_mem_inverse_class {A : Matrix m n ℂ} {X : Matrix n m ℂ} :
    Xᴴ ∈ Chapter01.definition_1 Aᴴ {.inner, .outer, .hermitianMul} ↔
      X ∈ Chapter01.definition_1 A {.inner, .outer, .hermitianMulRev} := by
  obtain ⟨hi, ho, hh, -⟩ := equation_89 A X
  simp only [mem_penroseInverses_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, PenroseCondition.Holds, hi, ho, hh]

/-- **Corollary 4** of [benIsrael2003generalized], Chapter 5, Equations
(90)–(93). Adjointing the row-partition formulas gives three reflexive
inverses with a Hermitian left product for a horizontally partitioned matrix.
They equal the Moore–Penrose inverse when the two column spaces intersect trivially. -/
theorem corollary_5_4 (A : Matrix n m ℂ) (B : Matrix n p ℂ) :
    let C := fromCols A B
    let P := orthogonalProjector ((toEuclideanLin Aᴴ).ker)
    let Q := orthogonalProjector ((toEuclideanLin Bᴴ).ker)
    let T := fromRows (-A.pinv) B.pinv
    let X := fromRows A.pinv (0 : Matrix p n ℂ) + T * (P + Q).pinv * P
    let Y := fromRows (0 : Matrix m n ℂ) B.pinv - T * (P + Q).pinv * Q
    let Z := fromRows A.pinv B.pinv * (A * A.pinv + B * B.pinv).pinv
    let s : Set PenroseCondition := {.inner, .outer, .hermitianMul}
    X ∈ Chapter01.definition_1 C s ∧ Y ∈ Chapter01.definition_1 C s ∧
      Z ∈ Chapter01.definition_1 C s ∧
        ((toEuclideanLin A).range ⊓ (toEuclideanLin B).range = ⊥ →
          X = C.pinv ∧ Y = C.pinv ∧ Z = C.pinv) := by
  dsimp only
  have hP := (isHermitian_orthogonalProjector ((toEuclideanLin Aᴴ).ker)).eq
  have hQ := (isHermitian_orthogonalProjector ((toEuclideanLin Bᴴ).ker)).eq
  have hD : (orthogonalProjector ((toEuclideanLin Aᴴ).ker) +
      orthogonalProjector ((toEuclideanLin Bᴴ).ker)).pinvᴴ =
        (orthogonalProjector ((toEuclideanLin Aᴴ).ker) +
          orthogonalProjector ((toEuclideanLin Bᴴ).ker)).pinv := by
    rw [← pinv_conjTranspose, conjTranspose_add, hP, hQ]
  have hAp : Aᴴ.pinvᴴ = A.pinv := by rw [← pinv_conjTranspose, conjTranspose_conjTranspose]
  have hBp : Bᴴ.pinvᴴ = B.pinv := by rw [← pinv_conjTranspose, conjTranspose_conjTranspose]
  have hW : (Aᴴ.pinv * Aᴴ + Bᴴ.pinv * Bᴴ).pinvᴴ = (A * A.pinv + B * B.pinv).pinv := by
    rw [← pinv_conjTranspose, conjTranspose_add, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, conjTranspose_conjTranspose, hAp, hBp]
  obtain ⟨hX, hY, hZ, hMoore⟩ := theorem_5_6 Aᴴ Bᴴ
  have hX' := adjoint_mem_inverse_class.mpr hX
  have hY' := adjoint_mem_inverse_class.mpr hY
  have hZ' := adjoint_mem_inverse_class.mpr hZ
  simp only [conjTranspose_fromCols_eq_fromRows_conjTranspose,
    conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_add, conjTranspose_sub,
    conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_neg, conjTranspose_zero,
    hAp, hBp, hD, hW, hP, hQ, Matrix.mul_assoc] at hX' hY' hZ'
  refine ⟨by simpa only [Matrix.mul_assoc] using hX',
    by simpa only [Matrix.mul_assoc] using hY', hZ', ?_⟩
  intro h
  obtain ⟨hXeq, hYeq, hZeq⟩ := hMoore (by simpa only [conjTranspose_conjTranspose] using h)
  have hx := congrArg Matrix.conjTranspose hXeq
  have hy := congrArg Matrix.conjTranspose hYeq
  have hz := congrArg Matrix.conjTranspose hZeq
  simp only [conjTranspose_fromCols_eq_fromRows_conjTranspose,
    conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_add, conjTranspose_sub,
    conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_neg, conjTranspose_zero,
    hAp, hBp, hD, hW, hP, hQ, ← pinv_conjTranspose, Matrix.mul_assoc] at hx hy hz
  simpa only [Matrix.mul_assoc] using And.intro hx (And.intro hy hz)

omit [DecidableEq m] [DecidableEq p] in
/-- **Exercise 17(a)** of [benIsrael2003generalized], Chapter 5, Equation
(94). An inner inverse of the residual block gives a second inner
inverse factor for the stacked matrix. -/
theorem exercise_17_a (A : Matrix m n ℂ) (B : Matrix p n ℂ)
    (U : Matrix n m ℂ) (V : Matrix n p ℂ)
    (hU : A.IsInnerInverse U) (hV : (B - B * U * A).IsInnerInverse V) :
    let Y := (1 - U * A) * V
    let X := U - Y * B * U
    (fromRows A B).IsInnerInverse (fromCols X Y) := by
  let D := B - B * U * A
  let N := 1 - U * A
  let Y := N * V
  let X := U - Y * B * U
  have hA : A * U * A = A := hU
  have hD : D * V * D = D := hV
  have hAN : A * N = 0 := by
    change A * (1 - U * A) = _
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hA, sub_self]
  have hBN : B * N = D := by
    change B * (1 - U * A) = _
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc]
  have hXY : fromCols X Y * fromRows A B = U * A + N * V * D := by
    rw [fromCols_mul_fromRows]
    change (U - Y * B * U) * A + Y * B = U * A + Y * D
    rw [Matrix.sub_mul, show Y * B * U * A = Y * (B * U * A) by
      simp only [Matrix.mul_assoc]]
    change _ = U * A + Y * (B - B * U * A)
    rw [Matrix.mul_sub]
    abel
  change fromRows A B * fromCols X Y * fromRows A B = fromRows A B
  rw [Matrix.mul_assoc, hXY, fromRows_mul]
  congr 1
  · rw [Matrix.mul_add, ← Matrix.mul_assoc A U,
      show A * (N * V * D) = A * N * V * D by simp only [Matrix.mul_assoc],
      hA, hAN, Matrix.zero_mul, Matrix.zero_mul, add_zero]
  · rw [Matrix.mul_add, ← Matrix.mul_assoc B U,
      show B * (N * V * D) = B * N * V * D by simp only [Matrix.mul_assoc], hBN, hD]
    change B * U * A + (B - B * U * A) = B
    abel

omit [DecidableEq m] [DecidableEq p] in
/-- **Exercise 17(b)** of [benIsrael2003generalized], Chapter 5, Equation
(95). The same inner inverse construction applies to a horizontal partition
by taking conjugate transposes. -/
theorem exercise_17_b (A : Matrix n m ℂ) (B : Matrix n p ℂ)
    (U : Matrix m n ℂ) (V : Matrix p n ℂ)
    (hU : A.IsInnerInverse U) (hV : (B - A * U * B).IsInnerInverse V) :
    let Y := V * (1 - A * U)
    let X := U - U * B * Y
    (fromCols A B).IsInnerInverse (fromRows X Y) := by
  classical
  have hU' := (equation_89 A U).1.mpr hU
  have hV' := (equation_89 (B - A * U * B) V).1.mpr hV
  have hV'' : (Bᴴ - Bᴴ * Uᴴ * Aᴴ).IsInnerInverse Vᴴ := by
    simpa only [conjTranspose_sub, conjTranspose_mul, Matrix.mul_assoc] using hV'
  have h := exercise_17_a Aᴴ Bᴴ Uᴴ Vᴴ hU' hV''
  have h' := (equation_89 _ _).1.mpr h
  simpa only [conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_fromCols_eq_fromRows_conjTranspose, conjTranspose_sub, conjTranspose_mul,
    conjTranspose_one, conjTranspose_conjTranspose, Matrix.mul_assoc] using h'

private theorem range_adjoint_inf_eq_bot_of_isUnit_fromRows
    (A : Matrix m (m ⊕ p) ℂ) (B : Matrix p (m ⊕ p) ℂ)
    (h : IsUnit (fromRows A B)) :
    (toEuclideanLin Aᴴ).range ⊓ (toEuclideanLin Bᴴ).range = ⊥ := by
  let C := fromRows A B
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  obtain ⟨hy, hz⟩ := hx
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hy
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hz
  let v : EuclideanSpace ℂ (m ⊕ p) := WithLp.toLp 2 (Sum.elim (WithLp.ofLp y) (-WithLp.ofLp z))
  have hCv : toEuclideanLin Cᴴ v = 0 := by
    rw [show Cᴴ = fromCols Aᴴ Bᴴ by simp [C, conjTranspose_fromRows_eq_fromCols_conjTranspose],
      toEuclideanLin_fromCols_apply]
    change toEuclideanLin Aᴴ y + toEuclideanLin Bᴴ (-z) = 0
    rw [map_neg, hy, hz, add_neg_cancel]
  have h₀ := congrArg WithLp.ofLp hCv
  rw [ofLp_toEuclideanLin, WithLp.ofLp_zero] at h₀
  have hv : WithLp.ofLp v = 0 :=
    mulVec_injective_of_isUnit ((isUnit_conjTranspose C).mpr h) (h₀.trans (mulVec_zero _).symm)
  have hy₀ : y = 0 := WithLp.ofLp_injective 2
    (congrArg (fun w : m ⊕ p → ℂ => w ∘ Sum.inl) hv)
  rw [hy₀, map_zero] at hy
  exact hy.symm

private theorem isUnit_sum_of_orthogonalProjectors_of_sup_eq_top
    {L M : Submodule ℂ (EuclideanSpace ℂ n)} (h : L ⊔ M = ⊤) :
    IsUnit (orthogonalProjector L + orthogonalProjector M) := by
  have hTop : orthogonalProjector (⊤ : Submodule ℂ (EuclideanSpace ℂ n)) = 1 := by
    apply toEuclideanLin.injective
    rw [toEuclideanLin_orthogonalProjector, toEuclideanLin_one]
    exact LinearMap.ext fun x => Submodule.starProjection_eq_self_iff.mpr Submodule.mem_top
  have he := (lemma_5_2 L M).1
  rw [h, hTop] at he
  exact isUnit_iff_exists_inv.mpr ⟨_, he.symm⟩

/-- **Exercise 18** of [benIsrael2003generalized], Chapter 5. For a
nonsingular stacked matrix, the three generalized inverse formulas use only
ordinary inverses of their square projector sums. -/
theorem exercise_18 (A : Matrix m (m ⊕ p) ℂ) (B : Matrix p (m ⊕ p) ℂ)
    (h : IsUnit (fromRows A B)) :
    let C := fromRows A B
    let P := orthogonalProjector ((toEuclideanLin A).ker)
    let Q := orthogonalProjector ((toEuclideanLin B).ker)
    let T := fromCols (-A.pinv) B.pinv
    IsUnit (P + Q) ∧ IsUnit (A.pinv * A + B.pinv * B) ∧
      C⁻¹ = fromCols A.pinv (0 : Matrix (m ⊕ p) p ℂ) + P * (P + Q)⁻¹ * T ∧
      C⁻¹ = fromCols (0 : Matrix (m ⊕ p) m ℂ) B.pinv - Q * (P + Q)⁻¹ * T ∧
      C⁻¹ = (A.pinv * A + B.pinv * B)⁻¹ * fromCols A.pinv B.pinv := by
  let C := fromRows A B
  let L := (toEuclideanLin A).ker
  let M := (toEuclideanLin B).ker
  let P := orthogonalProjector L
  let Q := orthogonalProjector M
  let W := A.pinv * A + B.pinv * B
  let T := fromCols (-A.pinv) B.pinv
  have hRow := range_adjoint_inf_eq_bot_of_isUnit_fromRows A B h
  have hLM : L ⊔ M = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    rw [← Submodule.inf_orthogonal]
    change (toEuclideanLin A).kerᗮ ⊓ (toEuclideanLin B).kerᗮ = _
    rw [LinearMap.orthogonal_ker, LinearMap.orthogonal_ker,
      ← toEuclideanLin_conjTranspose_eq_adjoint, ← toEuclideanLin_conjTranspose_eq_adjoint]
    exact hRow
  have hKer : (toEuclideanLin C).ker = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    apply WithLp.ofLp_injective 2
    exact mulVec_injective_of_isUnit h (congrArg WithLp.ofLp hxy)
  have hOrtho : Lᗮ ⊔ Mᗮ = ⊤ := by
    rw [← (exercise_13 L M).1]
    change ((toEuclideanLin A).ker ⊓ (toEuclideanLin B).ker)ᗮ = _
    rw [← ker_toEuclideanLin_fromRows, hKer, Submodule.bot_orthogonal_eq_top]
  have hP : IsUnit (P + Q) := isUnit_sum_of_orthogonalProjectors_of_sup_eq_top hLM
  have hW : IsUnit W := by
    change IsUnit (A.pinv * A + B.pinv * B)
    rw [← orthogonalProjector_kerComplement_eq_pinv_mul,
      ← orthogonalProjector_kerComplement_eq_pinv_mul]
    exact isUnit_sum_of_orthogonalProjectors_of_sup_eq_top hOrtho
  obtain ⟨hX, hY, hZ⟩ := (theorem_5_6 A B).2.2.2 hRow
  change fromCols A.pinv 0 + P * (P + Q).pinv * T = C.pinv at hX
  change fromCols 0 B.pinv - Q * (P + Q).pinv * T = C.pinv at hY
  change W.pinv * fromCols A.pinv B.pinv = C.pinv at hZ
  rw [Matrix.pinv_eq_inv hP, Matrix.pinv_eq_inv (show IsUnit C from h)] at hX hY
  rw [Matrix.pinv_eq_inv hW, Matrix.pinv_eq_inv (show IsUnit C from h)] at hZ
  exact ⟨hP, hW, hX.symm, hY.symm, hZ.symm⟩

section WorkedStackedInverse

/-- **Exercise 19** of [benIsrael2003generalized], Chapter 5.
The rows $[1,1]$ and $[1,2]$ give the indicated reciprocals, Gram sum,
and ordinary inverse through the stacked formula. -/
theorem exercise_19 :
    let A : Matrix (Fin 1) (Fin 2) ℂ := !![1, 1]
    let B : Matrix (Fin 1) (Fin 2) ℂ := !![1, 2]
    let C : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, 2]
    let S := A.pinv * A + B.pinv * B
    let T : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 5; 1 / 2, 2 / 5]
    IsUnit C ∧ A.pinv = !![1 / 2; 1 / 2] ∧ B.pinv = !![1 / 5; 2 / 5] ∧
      S = !![7 / 10, 9 / 10; 9 / 10, 13 / 10] ∧ S⁻¹ = !![13, -9; -9, 7] ∧
      C⁻¹ = S⁻¹ * T ∧ C⁻¹ = !![2, -1; -1, 1] := by
  intro A B C S T
  let U : Matrix (Fin 2) (Fin 1) ℂ := !![1 / 2; 1 / 2]
  let V : Matrix (Fin 2) (Fin 1) ℂ := !![1 / 5; 2 / 5]
  have hU : A.pinv = U := by
    symm
    apply A.pinv_unique
    all_goals
      try change (A * U)ᴴ = A * U
      try change (U * A)ᴴ = U * A
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [A, U, Matrix.mul_apply, Fin.sum_univ_succ, conjTranspose_apply]
  have hV : B.pinv = V := by
    symm
    apply B.pinv_unique
    all_goals
      try change (B * V)ᴴ = B * V
      try change (V * B)ᴴ = V * B
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [B, V, Matrix.mul_apply, Fin.sum_univ_succ, conjTranspose_apply]
  let S₀ : Matrix (Fin 2) (Fin 2) ℂ := !![7 / 10, 9 / 10; 9 / 10, 13 / 10]
  let Si : Matrix (Fin 2) (Fin 2) ℂ := !![13, -9; -9, 7]
  let Ci : Matrix (Fin 2) (Fin 2) ℂ := !![2, -1; -1, 1]
  have hS : S = S₀ := by
    change A.pinv * A + B.pinv * B = _
    rw [hU, hV]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [S₀, A, B, U, V, Matrix.mul_apply, Fin.sum_univ_succ]
  have hSi : S₀ * Si = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [S₀, Si, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  have hCi : C * Ci = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [C, Ci, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  have hI : Si * T = Ci := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [T, Si, Ci, Matrix.mul_apply, Fin.sum_univ_two]
  have hS' : S⁻¹ = Si := by rw [hS, inv_eq_right_inv hSi]
  have hC' : C⁻¹ = Ci := inv_eq_right_inv hCi
  refine ⟨isUnit_iff_exists_inv.mpr ⟨Ci, hCi⟩, hU, hV, hS, hS', ?_, hC'⟩
  rw [hS', hC', hI]

end WorkedStackedInverse

section StackedNeumannSeries

open scoped Matrix.Norms.L2Operator ComplexOrder

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

omit [DecidableEq a] in
private theorem posSemidef_of_hermitian_idempotent {X : Matrix a a ℂ}
    (hh : X.IsHermitian) (hi : IsIdempotentElem X) : X.PosSemidef := by
  simpa only [hh.eq, hi.eq] using posSemidef_conjTranspose_mul_self X

private theorem norm_lt_one_of_posDef_one_add_sub
    (X : Matrix a a ℂ) (hX : X.IsHermitian)
    (hp : (1 + X).PosDef) (hm : (1 - X).PosDef) : ‖X‖ < 1 := by
  let U := hX.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ (Matrix a a ℂ) (star U)
  let z (i : a) : ℂ := hX.eigenvalues i
  have hz : f X = diagonal z := hX.conjStarAlgAut_star_eigenvectorUnitary
  have hpd (M : Matrix a a ℂ) (hM : M.PosDef) : (f M).PosDef := by
    dsimp only [f]
    rw [Unitary.conjStarAlgAut_star_apply]
    exact (Unitary.isUnit_coe (U := U)).posDef_star_left_conjugate_iff.mpr hM
  have hplus : (diagonal fun i => 1 + z i).PosDef := by
    have h := hpd (1 + X) hp
    rw [map_add, map_one, hz, ← diagonal_one, diagonal_add] at h
    exact h
  have hminus : (diagonal fun i => 1 - z i).PosDef := by
    have h := hpd (1 - X) hm
    rw [map_sub, map_one, hz, ← diagonal_one, diagonal_sub] at h
    exact h
  have hnorm : ‖X‖ = ‖f X‖ := by
    dsimp only [f]
    rw [Unitary.conjStarAlgAut_star_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul]
  rw [hnorm, hz, l2_opNorm_diagonal, pi_norm_lt_iff zero_lt_one]
  intro i
  have hlt := (Complex.pos_iff.mp (posDef_diagonal_iff.mp hminus i)).1
  have hgt := (Complex.pos_iff.mp (posDef_diagonal_iff.mp hplus i)).1
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, z, Complex.ofReal_re] at hlt hgt
  change ‖(hX.eigenvalues i : ℂ)‖ < 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- **Exercise 20**, Equations (96)–(101), of [benIsrael2003generalized],
Chapter 5. The two projector sums have convergent Neumann series, yielding
the two ordinary inverse expansions for the nonsingular stacked matrix. -/
theorem exercise_20 (A : Matrix a (a ⊕ b) ℂ) (B : Matrix b (a ⊕ b) ℂ)
    (h : IsUnit (fromRows A B)) :
    let C := fromRows A B
    let S := A.pinv * A + B.pinv * B
    let P := 1 - A.pinv * A
    let Q := 1 - B.pinv * B
    let K := S - 1
    let T := fromCols A.pinv B.pinv
    let V := fromCols (-A.pinv) B.pinv
    K.IsHermitian ∧ ‖K‖ < 1 ∧
      HasSum (fun j : ℕ => (-K) ^ j) S⁻¹ ∧
      HasSum (fun j : ℕ => K ^ j) (P + Q)⁻¹ ∧
      HasSum (fun j : ℕ => (-K) ^ j * T) C⁻¹ ∧
      HasSum (fun j : ℕ => P * K ^ j * V) (C⁻¹ - fromCols A.pinv (0 : Matrix (a ⊕ b) b ℂ)) := by
  intro C S P Q K T V
  have hP : P = orthogonalProjector (toEuclideanLin A).ker :=
    (orthogonalProjector_ker_eq_one_sub_pinv_mul A).symm
  have hQ : Q = orthogonalProjector (toEuclideanLin B).ker :=
    (orthogonalProjector_ker_eq_one_sub_pinv_mul B).symm
  have hS : S.PosSemidef :=
    (posSemidef_of_hermitian_idempotent A.isHermitian_pinv_mul
      ((isInnerInverse_iff.mpr A.mul_pinv_mul_self).isIdempotentElem_mul_rev)).add
    (posSemidef_of_hermitian_idempotent B.isHermitian_pinv_mul
      ((isInnerInverse_iff.mpr B.mul_pinv_mul_self).isIdempotentElem_mul_rev))
  have hPQ : (P + Q).PosSemidef := by
    rw [hP, hQ]
    exact (posSemidef_of_hermitian_idempotent (isHermitian_orthogonalProjector _)
      (isIdempotentElem_orthogonalProjector _)).add
      (posSemidef_of_hermitian_idempotent (isHermitian_orthogonalProjector _)
        (isIdempotentElem_orthogonalProjector _))
  have hK : K.IsHermitian := hS.isHermitian.sub isHermitian_one
  have hPlus : 1 + K = S := by
    change 1 + (S - 1) = S
    abel
  have hMinus : 1 - K = P + Q := by
    change 1 - (A.pinv * A + B.pinv * B - 1) = 1 - A.pinv * A + (1 - B.pinv * B)
    abel
  obtain ⟨hUnitPQ, hUnitS, hInv1, _, hInv2⟩ := exercise_18 A B h
  rw [← hP, ← hQ] at hUnitPQ hInv1
  have hn : ‖K‖ < 1 := by
    apply norm_lt_one_of_posDef_one_add_sub K hK
    · rw [hPlus]
      exact hS.posDef_iff_isUnit.mpr hUnitS
    · rw [hMinus]
      exact hPQ.posDef_iff_isUnit.mpr hUnitPQ
  have hsum1 : HasSum (fun j : ℕ => (-K) ^ j) S⁻¹ := by
    simpa only [sub_neg_eq_add, hPlus, ← Matrix.nonsing_inv_eq_ringInverse] using
      hasSum_geom_series_inverse (-K) (by rwa [norm_neg])
  have hsum2 : HasSum (fun j : ℕ => K ^ j) (P + Q)⁻¹ := by
    simpa only [hMinus, ← Matrix.nonsing_inv_eq_ringInverse] using hasSum_geom_series_inverse K hn
  refine ⟨hK, hn, hsum1, hsum2, ?_, ?_⟩
  · rw [hInv2]
    exact hsum1.mul_right T
  · rw [hInv1, add_sub_cancel_left]
    exact (hsum2.mul_left P).mul_right V

/-- **Exercise 21**, Equations (102)–(103), of [benIsrael2003generalized],
Chapter 5. Applying the two stacked inverse expansions to the right-hand
side gives the two Neumann series for its solution. -/
theorem exercise_21 (A : Matrix a (a ⊕ b) ℂ) (B : Matrix b (a ⊕ b) ℂ)
    (h : IsUnit (fromRows A B)) (v : EuclideanSpace ℂ (a ⊕ b)) :
    let C := fromRows A B
    let K := A.pinv * A + B.pinv * B - 1
    let P := 1 - A.pinv * A
    let x := toEuclideanLin C⁻¹ v
    let w := toEuclideanLin (fromCols A.pinv B.pinv) v
    let z := toEuclideanLin (fromCols (-A.pinv) B.pinv) v
    let y := toEuclideanLin (fromCols A.pinv (0 : Matrix (a ⊕ b) b ℂ)) v
    toEuclideanLin C x = v ∧
      HasSum (fun j : ℕ => toEuclideanLin ((-K) ^ j) w) x ∧
      HasSum (fun j : ℕ => toEuclideanLin (P * K ^ j) z) (x - y) := by
  intro C K P x w z y
  let E : Matrix (a ⊕ b) (a ⊕ b) ℂ →ₗ[ℂ] EuclideanSpace ℂ (a ⊕ b) :=
    ((LinearMap.applyₗ (R := ℂ) (M₂ := EuclideanSpace ℂ (a ⊕ b))) v).comp
      toEuclideanLin.toLinearMap
  let hE : Continuous E := E.continuous_of_finiteDimensional
  obtain ⟨-, -, -, -, s₁, s₂⟩ := exercise_20 A B h
  have h₁ := s₁.map E.toAddMonoidHom hE
  have h₂ := s₂.map E.toAddMonoidHom hE
  change HasSum (fun j : ℕ => toEuclideanLin ((-K) ^ j * fromCols A.pinv B.pinv) v) x at h₁
  have (j : ℕ) : toEuclideanLin ((-K) ^ j * fromCols A.pinv B.pinv) v =
      toEuclideanLin ((-K) ^ j) w := toEuclideanLin_mul_apply _ _ _
  simp_rw [this] at h₁
  change HasSum (fun j : ℕ => toEuclideanLin (P * K ^ j * fromCols (-A.pinv) B.pinv) v)
    (E (C⁻¹ - fromCols A.pinv (0 : Matrix (a ⊕ b) b ℂ))) at h₂
  rw [map_sub] at h₂
  have he₂ (j : ℕ) : toEuclideanLin (P * K ^ j * fromCols (-A.pinv) B.pinv) v =
      toEuclideanLin (P * K ^ j) z := toEuclideanLin_mul_apply _ _ _
  simp_rw [he₂] at h₂
  refine ⟨?_, h₁, h₂⟩
  change toEuclideanLin C (toEuclideanLin C⁻¹ v) = v
  rw [← toEuclideanLin_mul_apply, mul_nonsing_inv C ((isUnit_iff_isUnit_det C).mp h),
    toEuclideanLin_one, LinearMap.id_apply]

end StackedNeumannSeries

section FiniteCommonSolutions

variable {p q r : Type*} [Fintype p] [Fintype q] [DecidableEq q]

/-- The representative and homogeneous map after processing a list of matrix
equations, together with the successive consistency conditions. -/
structure CommonSolutionState (q r : Type*) where
  /-- The representative of the affine solution set. -/
  representative : Matrix q r ℂ
  /-- The linear map that acts on the free matrix parameter. -/
  homogeneous : Matrix q q ℂ
  /-- The residual consistency condition at each step, in source order. -/
  conditions : List Prop

private noncomputable def commonSolutionRecurrenceFrom
    (E : Matrix q r ℂ) (F : Matrix q q ℂ) :
    List (Matrix p q ℂ × Matrix p r ℂ) → CommonSolutionState q r
  | [] => ⟨E, F, []⟩
  | (A, B) :: rest =>
    let C := A * F
    let D := B - A * E
    let result := commonSolutionRecurrenceFrom (E + F * C.pinv * D)
      (F * (1 - C.pinv * C)) rest
    ⟨result.representative, result.homogeneous, (C * C.pinv * D = D) :: result.conditions⟩

/-- **Equations (104)–(106)** of [benIsrael2003generalized], Chapter 5.
The recurrence starts at the zero representative and the identity free map,
and records the compatibility condition from each residual equation. -/
noncomputable def commonSolutionRecurrence :
    List (Matrix p q ℂ × Matrix p r ℂ) → CommonSolutionState q r :=
  commonSolutionRecurrenceFrom 0 1

private theorem commonSolutionStep_iff
    (E X : Matrix q r ℂ) (F : Matrix q q ℂ)
    (A : Matrix p q ℂ) (B : Matrix p r ℂ) :
    let C := A * F
    let D := B - A * E
    ((∃ Z : Matrix q r ℂ, X = E + F * Z) ∧ A * X = B) ↔
      C * C.pinv * D = D ∧
        ∃ Z : Matrix q r ℂ, X = (E + F * C.pinv * D) + F * (1 - C.pinv * C) * Z := by
  intro C D
  have hzero : C * (1 - C.pinv * C) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, C.mul_pinv_mul_self, sub_self]
  constructor
  · rintro ⟨⟨Z, rfl⟩, h⟩
    have hZ : C * Z = D := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc] at h
      exact eq_sub_of_add_eq' h
    have hD : C * C.pinv * D = D := by
      rw [← hZ, ← Matrix.mul_assoc, C.mul_pinv_mul_self]
    refine ⟨hD, Z, ?_⟩
    have hSplit : C.pinv * D + (1 - C.pinv * C) * Z = Z := by
      rw [← hZ, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc C.pinv C Z]
      abel
    conv_lhs => rw [← hSplit]
    simp only [Matrix.mul_add, Matrix.mul_assoc, add_assoc]
  · rintro ⟨hD, Z, rfl⟩
    let Y := C.pinv * D + (1 - C.pinv * C) * Z
    have hy : C * Y = D := by
      simp only [Y, Matrix.mul_add, ← Matrix.mul_assoc, hD, hzero, Matrix.zero_mul, add_zero]
    have he : (E + F * C.pinv * D) + F * (1 - C.pinv * C) * Z = E + F * Y := by
      simp only [Y, Matrix.mul_add, Matrix.mul_assoc, add_assoc]
    rw [he]
    refine ⟨⟨Y, rfl⟩, ?_⟩
    have hAy : A * (E + F * Y) = A * E + C * Y := by rw [Matrix.mul_add, Matrix.mul_assoc]
    rw [hAy, hy]
    simp [D]

private theorem commonSolutionRecurrenceFrom_iff
    (eqs : List (Matrix p q ℂ × Matrix p r ℂ)) (E X : Matrix q r ℂ) (F : Matrix q q ℂ) :
    let result := commonSolutionRecurrenceFrom E F eqs
    ((∃ Z : Matrix q r ℂ, X = E + F * Z) ∧ ∀ pair ∈ eqs, pair.1 * X = pair.2) ↔
      (∀ condition ∈ result.conditions, condition) ∧
        ∃ Z : Matrix q r ℂ, X = result.representative + result.homogeneous * Z := by
  induction eqs generalizing E F with
  | nil => simp [commonSolutionRecurrenceFrom, and_comm]
  | cons head eqs ih =>
    obtain ⟨A, B⟩ := head
    let C := A * F
    let D := B - A * E
    let E' := E + F * C.pinv * D
    let F' := F * (1 - C.pinv * C)
    let result := commonSolutionRecurrenceFrom E' F' eqs
    have hStep := commonSolutionStep_iff E X F A B
    have hTail := ih E' F'
    simp only [commonSolutionRecurrenceFrom, List.forall_mem_cons]
    constructor
    · rintro ⟨he, hh, ht⟩
      obtain ⟨hC, he'⟩ := hStep.mp ⟨he, hh⟩
      obtain ⟨hCond, hs⟩ := hTail.mp ⟨he', ht⟩
      exact ⟨⟨hC, hCond⟩, hs⟩
    · rintro ⟨⟨hC, hCond⟩, hs⟩
      obtain ⟨he', ht⟩ := hTail.mpr ⟨hCond, hs⟩
      obtain ⟨he, hh⟩ := hStep.mpr ⟨hC, he'⟩
      exact ⟨he, hh, ht⟩

/-- **Exercise 22**, Equations (106)–(107) of [benIsrael2003generalized],
Chapter 5. A common solution exists exactly when every residual is
compatible. The recurrence then gives all common solutions. -/
theorem exercise_22 (eqs : List (Matrix p q ℂ × Matrix p r ℂ)) :
    let result := commonSolutionRecurrence eqs
    ((∃ X, ∀ pair ∈ eqs, pair.1 * X = pair.2) ↔
      ∀ condition ∈ result.conditions, condition) ∧
      ((∀ condition ∈ result.conditions, condition) →
        ∀ X, (∀ pair ∈ eqs, pair.1 * X = pair.2) ↔
          ∃ Z : Matrix q r ℂ, X = result.representative + result.homogeneous * Z) := by
  intro result
  have he (X : Matrix q r ℂ) :
      (∀ pair ∈ eqs, pair.1 * X = pair.2) ↔
        (∀ c ∈ result.conditions, c) ∧
          ∃ Z : Matrix q r ℂ, X = result.representative + result.homogeneous * Z := by
    have hr := commonSolutionRecurrenceFrom_iff eqs 0 X (1 : Matrix q q ℂ)
    simpa [commonSolutionRecurrence, result] using hr
  constructor
  · constructor
    · rintro ⟨X, hX⟩
      exact ((he X).mp hX).1
    · intro hc
      exact ⟨result.representative + result.homogeneous * 0,
        (he _).mpr ⟨hc, 0, rfl⟩⟩
  · intro hc X
    exact (he X).trans (and_iff_right hc)

end FiniteCommonSolutions

end BenIsraelGreville.Chapter05
