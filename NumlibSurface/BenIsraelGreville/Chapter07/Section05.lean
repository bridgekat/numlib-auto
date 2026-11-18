/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter01.Section03
import NumlibSurface.BenIsraelGreville.Chapter02.Section07
import NumlibSurface.BenIsraelGreville.Chapter05.Section02
import NumlibSurface.BenIsraelGreville.Chapter07.Section04
import Numlib.Data.Fin.Sum
import Numlib.LinearAlgebra.Matrix.LeastSquares

/-!
# Greville's pseudoinverse update

Section 7.5 of [benIsrael2003generalized] appends one column or one row to
a matrix whose Moore–Penrose inverse is known. The row formula also yields
the minimum-norm least-squares update when one observation is appended.

## Deviations from the source

In **Equation (35)**, the first term in the upper-left block of the product
is the domain projection `A† * A`.
-/

namespace BenIsraelGreville.Chapter07

open Matrix
open scoped ComplexOrder

section Column

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Equations (21)–(22)** of [benIsrael2003generalized], Chapter 7.
The residual column after applying the old column-range projector. -/
noncomputable def grevilleColumnResidual (A : Matrix m n ℂ)
    (a : Matrix m Unit ℂ) : Matrix m Unit ℂ :=
  a - A * (A.pinv * a)

/-- **Equations (24a)–(24b)** of [benIsrael2003generalized], Chapter 7.
The inverse row for a newly appended column. The denominator in the
dependent case is represented as a one-by-one matrix. -/
noncomputable def grevilleColumnCoefficient [DecidableEq m] (A : Matrix m n ℂ)
    (a : Matrix m Unit ℂ) : Matrix Unit m ℂ := by
  classical
  let d := A.pinv * a
  let c := grevilleColumnResidual A a
  exact if c = 0 then (1 + dᴴ * d)⁻¹ * dᴴ * A.pinv else c.pinv

/-- **Equation (22)** of [benIsrael2003generalized], Chapter 7.
The residual is in the kernel of the old conjugate transpose. -/
theorem grevilleColumnResidual_orthogonal (A : Matrix m n ℂ) (a : Matrix m Unit ℂ) :
    Aᴴ * grevilleColumnResidual A a = 0 := by
  rw [grevilleColumnResidual, Matrix.mul_sub, ← Matrix.mul_assoc Aᴴ A,
    ← Matrix.mul_assoc (Aᴴ * A) A.pinv, Matrix.mul_assoc Aᴴ A A.pinv,
    A.conjTranspose_mul_mul_pinv, sub_self]

/-- **Equation (22)** of [benIsrael2003generalized], Chapter 7.
The residual is the orthogonal projection of the appended column onto
the kernel of the old adjoint. -/
theorem grevilleColumnResidual_eq_orthogonalProjector [DecidableEq m]
    (A : Matrix m n ℂ) (a : Matrix m Unit ℂ) :
    grevilleColumnResidual A a = Chapter02.orthogonalProjector
      (LinearMap.ker Aᴴ.toEuclideanLin) * a := by
  let L := LinearMap.range A.toEuclideanLin
  have hL : Lᗮ = LinearMap.ker Aᴴ.toEuclideanLin := by
    change (LinearMap.range A.toEuclideanLin)ᗮ = _
    rw [LinearMap.orthogonal_range, toEuclideanLin_conjTranspose_eq_adjoint]
  have hp : Chapter02.orthogonalProjector Lᗮ = 1 - A * A.pinv := by
    apply toEuclideanLin.injective
    rw [Chapter02.toEuclideanLin_orthogonalProjector, map_sub, toEuclideanLin_one,
      A.mul_pinv_eq_starProjection]
    exact congrArg ContinuousLinearMap.toLinearMap (Submodule.starProjection_orthogonal L)
  rw [← hL, hp, grevilleColumnResidual, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]

omit [Fintype m] in
private theorem injective_column_mulVec (c : Matrix m Unit ℂ) (hc : c ≠ 0) :
    Function.Injective c.mulVec := by
  obtain ⟨i, hi⟩ : ∃ i, c i () ≠ 0 := by
    by_contra! h
    apply hc
    ext j u
    cases u
    exact h j
  intro x y h
  funext u
  cases u
  apply mul_left_cancel₀ hi
  simpa [mulVec, dotProduct] using congrFun h i

private theorem greville_independent_cancellation (A : Matrix m n ℂ)
    (a : Matrix m Unit ℂ) (hc : grevilleColumnResidual A a ≠ 0) :
    let c := grevilleColumnResidual A a
    c.pinv * A = 0 ∧ c.pinv * c = 1 := by
  dsimp only
  let c := grevilleColumnResidual A a
  have hOrth : cᴴ * A = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg Matrix.conjTranspose (grevilleColumnResidual_orthogonal A a)
  constructor
  · change c.pinv * A = 0
    rw [c.pinv_def, Matrix.mul_assoc, hOrth, Matrix.mul_zero]
  · have hr := mulVec_injective_iff_rank_eq_card.mp (injective_column_mulVec c hc)
    exact (Chapter01.lemma_2_a (Chapter01.mem_one_iff.mpr c.mul_pinv_mul_self)).mpr hr

variable [DecidableEq m]

omit [DecidableEq m] in
private theorem greville_pinv_independent (A : Matrix m n ℂ) (a : Matrix m Unit ℂ)
    (hc : grevilleColumnResidual A a ≠ 0) :
    (fromCols A a).pinv =
      fromRows (A.pinv - (A.pinv * a) * (grevilleColumnResidual A a).pinv)
        (grevilleColumnResidual A a).pinv := by
  let d := A.pinv * a
  let c := grevilleColumnResidual A a
  let b := c.pinv
  let B := fromCols A a
  let X := fromRows (A.pinv - d * b) b
  change B.pinv = X
  obtain ⟨hbA, hbc⟩ := greville_independent_cancellation A a hc
  change b * A = 0 at hbA
  change b * c = 1 at hbc
  have h₀ : a = c + A * d := (sub_add_cancel a (A * d)).symm
  have hba : b * a = 1 := by
    rw [h₀, Matrix.mul_add, hbc, ← Matrix.mul_assoc, hbA, Matrix.zero_mul, add_zero]
  have hBX : B * X = A * A.pinv + c * b := by
    change fromCols A a * fromRows (A.pinv - d * b) b = _
    rw [fromCols_mul_fromRows, Matrix.mul_sub, ← Matrix.mul_assoc A d b,
      sub_add_eq_add_sub, add_sub_assoc, ← Matrix.sub_mul]
    rfl
  have hXB : X * B = fromBlocks (A.pinv * A) 0 0 1 := by
    change fromRows (A.pinv - d * b) b * fromCols A a = _
    rw [fromRows_mul_fromCols, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.mul_assoc d b A, Matrix.mul_assoc d b a, hbA, hba, Matrix.mul_zero,
      Matrix.mul_one, sub_zero, show A.pinv * a = d from rfl, sub_self]
  have hPa : (A * A.pinv) * a = A * d := Matrix.mul_assoc _ _ _
  have hTop : (A.pinv * A) * (A.pinv - d * b) = A.pinv - d * b := by
    rw [Matrix.mul_sub, A.pinv_mul_self_mul_pinv, ← Matrix.mul_assoc,
      show (A.pinv * A) * d = d by
        change (A.pinv * A) * (A.pinv * a) = A.pinv * a
        rw [← Matrix.mul_assoc, A.pinv_mul_self_mul_pinv]]
  symm
  apply B.pinv_unique
  · rw [hBX, mul_fromCols, Matrix.add_mul, Matrix.add_mul, A.mul_pinv_mul_self,
      hPa, Matrix.mul_assoc c b A, Matrix.mul_assoc c b a, hbA, hba, Matrix.mul_zero,
      Matrix.mul_one, add_zero, add_comm (A * d) c, ← h₀]
  · rw [hXB]
    change fromBlocks (A.pinv * A) 0 0 1 * fromRows (A.pinv - d * b) b = X
    rw [fromBlocks_mul_fromRows, hTop, Matrix.zero_mul, Matrix.zero_mul, Matrix.one_mul,
      add_zero, zero_add]
  · rw [hBX]
    exact A.isHermitian_mul_pinv.add c.isHermitian_mul_pinv
  · rw [hXB]
    exact A.isHermitian_pinv_mul.fromBlocks (conjTranspose_zero) isHermitian_one

omit [DecidableEq m] in
private theorem greville_pinv_dependent (A : Matrix m n ℂ) (a : Matrix m Unit ℂ)
    (hc : grevilleColumnResidual A a = 0) :
    let d := A.pinv * a
    let b := (1 + dᴴ * d)⁻¹ * dᴴ * A.pinv
    (fromCols A a).pinv = fromRows (A.pinv - d * b) b := by
  dsimp only
  let d := A.pinv * a
  let R := 1 + dᴴ * d
  let q := R⁻¹
  let b := q * dᴴ * A.pinv
  let B := fromCols A a
  let X := fromRows (A.pinv - d * b) b
  let P := A.pinv * A
  change B.pinv = X
  have ha : a = A * d := sub_eq_zero.mp hc
  have hP : P.IsHermitian := A.isHermitian_pinv_mul
  have hPd : P * d = d := by
    change (A.pinv * A) * (A.pinv * a) = _
    rw [← Matrix.mul_assoc, A.pinv_mul_self_mul_pinv]
  have hdP : dᴴ * P = dᴴ := by
    simpa only [conjTranspose_mul, hP.eq] using congrArg Matrix.conjTranspose hPd
  have hq : q.IsHermitian :=
    (isHermitian_one.add (isHermitian_conjTranspose_mul_self d)).inv
  have hR : IsUnit R := by
    exact (PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self d)).isUnit
  have hqR : q * R = 1 := nonsing_inv_mul R ((isUnit_iff_isUnit_det R).mp hR)
  have hbA : b * A = q * dᴴ := by
    change (q * dᴴ * A.pinv) * A = _
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← show P = A.pinv * A from rfl, hdP]
  have hba : b * a = 1 - q := by
    rw [ha, ← Matrix.mul_assoc, hbA, Matrix.mul_assoc, ← add_right_inj q]
    calc
      q + q * (dᴴ * d) = q * R := by
        change _ = q * (1 + dᴴ * d)
        rw [Matrix.mul_add, Matrix.mul_one]
      _ = 1 := hqR
      _ = q + (1 - q) := by abel
  have hBX : B * X = A * A.pinv := by
    change fromCols A a * fromRows (A.pinv - d * b) b = _
    rw [fromCols_mul_fromRows, Matrix.mul_sub, ← Matrix.mul_assoc A d b, ← ha,
      sub_add_cancel]
  have hXB : X * B = fromBlocks (P - d * q * dᴴ) (d * q) (q * dᴴ) (1 - q) := by
    change fromRows (A.pinv - d * b) b * fromCols A a = _
    rw [fromRows_mul_fromCols, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc d b A,
      Matrix.mul_assoc d b a, hbA, hba, ← Matrix.mul_assoc, show A.pinv * a = d from rfl,
      Matrix.mul_sub, Matrix.mul_one, sub_sub_cancel]
  have hbP : b * (A * A.pinv) = b := by
    change (q * dᴴ * A.pinv) * (A * A.pinv) = _
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc A.pinv A A.pinv, A.pinv_mul_self_mul_pinv]
    exact (Matrix.mul_assoc q dᴴ A.pinv).symm
  symm
  apply B.pinv_unique
  · rw [hBX, mul_fromCols, A.mul_pinv_mul_self, Matrix.mul_assoc,
      ← show d = A.pinv * a from rfl, ← ha]
  · rw [Matrix.mul_assoc, hBX]
    change fromRows (A.pinv - d * b) b * (A * A.pinv) = X
    rw [fromRows_mul, hbP, Matrix.sub_mul, Matrix.mul_assoc d b (A * A.pinv), hbP,
      ← Matrix.mul_assoc A.pinv A A.pinv, A.pinv_mul_self_mul_pinv]
  · rw [hBX]
    exact A.isHermitian_mul_pinv
  · rw [hXB]
    exact (hP.sub (by
      change (d * q * dᴴ)ᴴ = d * q * dᴴ
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, hq.eq,
        Matrix.mul_assoc])).fromBlocks
        (by rw [conjTranspose_mul, hq.eq]) (isHermitian_one.sub hq)

/-- **Theorem 2**, Equations (23)–(24) of [benIsrael2003generalized], Chapter 7.
Greville's column update applies whether the new column is independent
of the old columns or lies in their span. -/
theorem theorem_2 (A : Matrix m n ℂ) (a : Matrix m Unit ℂ) :
    (fromCols A a).pinv =
      fromRows (A.pinv - (A.pinv * a) * grevilleColumnCoefficient A a)
        (grevilleColumnCoefficient A a) := by
  classical
  dsimp only [grevilleColumnCoefficient]
  split_ifs with h
  · exact greville_pinv_dependent A a h
  · exact greville_pinv_independent A a h

/-- **Equation (40)** of [benIsrael2003generalized], Chapter 7.
Greville's update can act on any family of right-hand sides, so that
their images can be computed without constructing the updated inverse. -/
theorem grevilleColumnAction {p : Type*} (A : Matrix m n ℂ) (a : Matrix m Unit ℂ)
    (Y : Matrix m p ℂ) :
    let b := grevilleColumnCoefficient A a
    (fromCols A a).pinv * Y = fromRows (A.pinv * Y - (A.pinv * a) * (b * Y)) (b * Y) := by
  dsimp only
  rw [theorem_2, fromRows_mul, Matrix.sub_mul, Matrix.mul_assoc]

/-- **Equation (41)** of [benIsrael2003generalized], Chapter 7.
For a dependent column, the new row applied to the right-hand sides
uses the previous inverse only through its action on those columns. -/
theorem grevilleColumnAction_dependent {p : Type*} (A : Matrix m n ℂ)
    (a : Matrix m Unit ℂ) (Y : Matrix m p ℂ) (h : grevilleColumnResidual A a = 0) :
    let d := A.pinv * a
    grevilleColumnCoefficient A a * Y = (1 + dᴴ * d)⁻¹ * dᴴ * (A.pinv * Y) := by
  classical
  simp only [grevilleColumnCoefficient, h, ite_true, Matrix.mul_assoc]

/-- **Equation (42)** of [benIsrael2003generalized], Chapter 7.
For an independent column, the new row is the adjoint residual
normalized by its squared length. -/
theorem grevilleColumnAction_independent {p : Type*} (A : Matrix m n ℂ)
    (a : Matrix m Unit ℂ) (Y : Matrix m p ℂ) (h : grevilleColumnResidual A a ≠ 0) :
    let c := grevilleColumnResidual A a
    grevilleColumnCoefficient A a * Y = (cᴴ * c)⁻¹ * (cᴴ * Y) := by
  classical
  let c := grevilleColumnResidual A a
  change grevilleColumnCoefficient A a * Y = (cᴴ * c)⁻¹ * (cᴴ * Y)
  have hRank := mulVec_injective_iff_rank_eq_card.mp (injective_column_mulVec c h)
  have hUnit : IsUnit (cᴴ * c) :=
    mulVec_surjective_iff_isUnit.mp (mulVec_surjective_iff_rank_eq_card.mpr
      (c.rank_conjTranspose_mul_self.trans hRank))
  simp only [grevilleColumnCoefficient, h, ite_false]
  change c.pinv * Y = _
  rw [pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit hUnit, Matrix.mul_assoc]

omit [DecidableEq m] in
/-- **Equation (43)** of [benIsrael2003generalized], Chapter 7.
The normalizer equals the entry of the adjoint residual applied to the
original appended column. -/
theorem grevilleColumnResidual_normalizer (A : Matrix m n ℂ) (a : Matrix m Unit ℂ) :
    let c := grevilleColumnResidual A a
    cᴴ * c = cᴴ * a := by
  let c := grevilleColumnResidual A a
  change cᴴ * c = cᴴ * a
  have hOrth : cᴴ * A = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg Matrix.conjTranspose (grevilleColumnResidual_orthogonal A a)
  calc
    cᴴ * c = cᴴ * (a - A * (A.pinv * a)) := rfl
    _ = cᴴ * a := by rw [Matrix.mul_sub, ← Matrix.mul_assoc, hOrth, Matrix.zero_mul, sub_zero]

/-- **Equations (21)–(24)** of [benIsrael2003generalized], Chapter 7.
The next inverse row computed from a supplied previous inverse.
Only scalar inversion is required in either branch. -/
noncomputable def grevilleColumnCoefficientFrom (A : Matrix m n ℂ)
    (a : Matrix m Unit ℂ) (X : Matrix n m ℂ) : Matrix Unit m ℂ := by
  classical
  let d := X * a
  let c := a - A * d
  exact if c = 0 then (1 + dᴴ * d)⁻¹ * dᴴ * X else (cᴴ * c)⁻¹ * cᴴ

/-- When the supplied inverse is the Moore–Penrose inverse, the arithmetic
update agrees with the coefficient in Greville's theorem. -/
theorem grevilleColumnCoefficientFrom_pinv (A : Matrix m n ℂ) (a : Matrix m Unit ℂ) :
    grevilleColumnCoefficientFrom A a A.pinv = grevilleColumnCoefficient A a := by
  classical
  have he : a - A * (A.pinv * a) = grevilleColumnResidual A a := rfl
  by_cases h : grevilleColumnResidual A a = 0
  · simp only [grevilleColumnCoefficientFrom, grevilleColumnCoefficient, he, h, ite_true]
  · have hc := grevilleColumnAction_independent A a (1 : Matrix m m ℂ) h
    simp only [grevilleColumnCoefficientFrom, he, h, ite_false, Matrix.mul_one] at hc ⊢
    exact hc.symm

/-- **Exercise 12**, Equation (61) of [benIsrael2003generalized], Chapter 7.
Deleting the last column of a full-column-rank matrix updates the
pseudoinverse by subtracting a rank-one term. -/
theorem exercise_12 (A : Matrix m n ℂ) (a : Matrix m Unit ℂ)
    (hB : (fromCols A a).rank = Fintype.card (n ⊕ Unit)) :
    let b := grevilleColumnCoefficient A a
    fromRows A.pinv (0 : Matrix Unit m ℂ) =
      (fromCols A a).pinv - (fromCols A a).pinv * bᴴ * (b * bᴴ)⁻¹ * b := by
  let B := fromCols A a
  let c := grevilleColumnResidual A a
  let d := A.pinv * a
  let b := grevilleColumnCoefficient A a
  change fromRows A.pinv 0 = B.pinv - B.pinv * bᴴ * (b * bᴴ)⁻¹ * b
  have hc : c ≠ 0 := by
    intro hz
    have ha : a = A * d := sub_eq_zero.mp hz
    let w := fromRows (-d) (1 : Matrix Unit Unit ℂ)
    have hw : B * w = 0 := by
      change fromCols A a * fromRows (-d) (1 : Matrix Unit Unit ℂ) = 0
      rw [fromCols_mul_fromRows, Matrix.mul_neg, Matrix.mul_one, ha, neg_add_cancel]
    let z : n ⊕ Unit → ℂ := fun i => w i ()
    have hzero : B *ᵥ z = 0 := by
      ext i
      exact congrFun (congrFun hw i) ()
    have hinj := mulVec_injective_iff_rank_eq_card.mpr hB
    have hz' : z = 0 := hinj (hzero.trans (mulVec_zero B).symm)
    have hh := congrFun hz' (Sum.inr ())
    simp [z, w] at hh
  have hb : b = c.pinv := by
    classical
    change grevilleColumnCoefficient A a = c.pinv
    simp only [grevilleColumnCoefficient, show grevilleColumnResidual A a ≠ 0 from hc,
      ite_false]
    rfl
  obtain ⟨hbA, hbc⟩ := greville_independent_cancellation A a hc
  change c.pinv * A = 0 at hbA
  change c.pinv * c = 1 at hbc
  rw [← hb] at hbA hbc
  have hAdj : Aᴴ * bᴴ = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_zero] using
      congrArg Matrix.conjTranspose hbA
  have hAz : A.pinv * bᴴ = 0 := by
    rw [A.pinv_def, Matrix.mul_assoc, hAdj, Matrix.mul_zero]
  have hbne : b ≠ 0 := by
    intro hz
    have hh := congrFun (congrFun hbc ()) ()
    simp [hz] at hh
  have hGram : IsUnit (b * bᴴ) := by
    have hf := mulVec_injective_iff_rank_eq_card.mp
      (injective_column_mulVec bᴴ (fun h => hbne (conjTranspose_eq_zero.mp h)))
    apply mulVec_surjective_iff_isUnit.mp
    apply mulVec_surjective_iff_rank_eq_card.mpr
    simpa only [conjTranspose_conjTranspose] using bᴴ.rank_conjTranspose_mul_self.trans hf
  have hp : B.pinv = fromRows (A.pinv - d * b) b := theorem_2 A a
  have hProd : B.pinv * bᴴ * (b * bᴴ)⁻¹ * b = fromRows (-(d * b)) b := by
    rw [hp, fromRows_mul, fromRows_mul, fromRows_mul, Matrix.sub_mul, hAz, zero_sub]
    simp only [Matrix.neg_mul, Matrix.mul_assoc d b bᴴ]
    rw [Matrix.mul_assoc d (b * bᴴ) (b * bᴴ)⁻¹,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hGram), Matrix.mul_one, Matrix.one_mul]
  rw [hProd, hp, fromRows_sub, sub_neg_eq_add, sub_add_cancel, sub_self]

end Column

section Recursion

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Section 7.5** of [benIsrael2003generalized].
Greville's algorithm recursively computes the inverse of the leading
columns and appends the last column using scalar inversion. -/
noncomputable def grevilleInverse : ∀ {k : ℕ}, Matrix m (Fin k) ℂ → Matrix (Fin k) m ℂ
  | 0, _ => 0
  | k + 1, A =>
      let B := A.submatrix id Fin.castSucc
      let a : Matrix m Unit ℂ := Matrix.of fun i _ => A i (Fin.last k)
      let X := grevilleInverse B
      let b := grevilleColumnCoefficientFrom B a X
      (fromRows (X - (X * a) * b) b).submatrix (finSuccEquivLastSumUnit k) id

omit [DecidableEq m] in
/-- Every step of the Greville recursion produces the Moore–Penrose
inverse of the corresponding leading-column matrix. -/
theorem grevilleInverse_eq_pinv {k : ℕ} (A : Matrix m (Fin k) ℂ) :
    grevilleInverse A = A.pinv := by
  classical
  induction k with
  | zero => ext i; exact Fin.elim0 i
  | succ k ih =>
    let e := finSuccEquivLastSumUnit k
    let B := A.submatrix id Fin.castSucc
    let a : Matrix m Unit ℂ := Matrix.of fun i _ => A i (Fin.last k)
    have hA : A.submatrix (Equiv.refl m) e.symm = fromCols B a := by
      ext i (j | j)
      · simp only [e, submatrix_apply, Equiv.refl_apply, finSuccEquivLastSumUnit_symm_inl,
          fromCols_apply_inl, B, id_eq]
      · simp only [e, submatrix_apply, Equiv.refl_apply, finSuccEquivLastSumUnit_symm_inr,
          fromCols_apply_inr, a, of_apply]
    have hP : (fromCols B a).pinv = A.pinv.submatrix e.symm (Equiv.refl m) := by
      rw [← hA, Chapter05.pinv_submatrix_equiv]
    calc
      grevilleInverse A = ((fromCols B a).pinv).submatrix e id := by
        change (fromRows
          (grevilleInverse B - (grevilleInverse B * a) *
            grevilleColumnCoefficientFrom B a (grevilleInverse B))
          (grevilleColumnCoefficientFrom B a (grevilleInverse B))).submatrix e id = _
        rw [ih, grevilleColumnCoefficientFrom_pinv, theorem_2]
      _ = A.pinv := by
        rw [hP]
        ext i j
        simp only [submatrix_apply, Equiv.symm_apply_apply, Equiv.refl_apply, id_eq]

/-- **Exercise 11** of [benIsrael2003generalized], Chapter 7.
The finite Greville recursion returns the exact pseudoinverse of the
matrix in Exercise 5. -/
theorem exercise_11 :
    grevilleInverse exercise_7_5_matrix = exercise_7_5_inverse :=
  (grevilleInverse_eq_pinv exercise_7_5_matrix).trans exercise_9_zlobec.2

end Recursion

section Row

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Equations (53)–(54)** of [benIsrael2003generalized], Chapter 7.
The residual row after applying the old row-range projector. -/
noncomputable def grevilleRowResidual (A : Matrix m n ℂ) (a : Matrix Unit n ℂ) :
    Matrix Unit n ℂ := a - (a * A.pinv) * A

/-- **Equations (56)–(57)** of [benIsrael2003generalized], Chapter 7.
The inverse column for a newly appended row. -/
noncomputable def grevilleRowCoefficient (A : Matrix m n ℂ) (a : Matrix Unit n ℂ) :
    Matrix n Unit ℂ := by
  classical
  let d := a * A.pinv
  let c := grevilleRowResidual A a
  exact if c = 0 then A.pinv * dᴴ * (1 + d * dᴴ)⁻¹ else c.pinv

private theorem grevilleColumnResidual_adjoint (A : Matrix m n ℂ) (a : Matrix Unit n ℂ) :
    grevilleColumnResidual Aᴴ aᴴ = (grevilleRowResidual A a)ᴴ := by
  simp only [grevilleColumnResidual, grevilleRowResidual, conjTranspose_sub, conjTranspose_mul,
    Matrix.pinv_conjTranspose]

private theorem grevilleColumnCoefficient_adjoint (A : Matrix m n ℂ)
    (a : Matrix Unit n ℂ) :
    (grevilleColumnCoefficient Aᴴ aᴴ)ᴴ = grevilleRowCoefficient A a := by
  classical
  dsimp only [grevilleColumnCoefficient, grevilleRowCoefficient]
  rw [grevilleColumnResidual_adjoint]
  by_cases h : grevilleRowResidual A a = 0
  · simp only [h, conjTranspose_zero, ite_true, Matrix.pinv_conjTranspose, conjTranspose_mul,
      conjTranspose_nonsing_inv, conjTranspose_add, conjTranspose_one,
      conjTranspose_conjTranspose, Matrix.mul_assoc]
  · have hc : (grevilleRowResidual A a)ᴴ ≠ 0 := by
      intro hz
      apply h
      simpa only [conjTranspose_conjTranspose, conjTranspose_zero] using
        congrArg Matrix.conjTranspose hz
    simp only [h, hc, ite_false, Matrix.pinv_conjTranspose, conjTranspose_conjTranspose]

omit [DecidableEq m] in
/-- **Corollary 1**, Equations (55)–(57) of [benIsrael2003generalized],
Chapter 7. Greville's update for an appended row follows by taking adjoints. -/
theorem corollary_1 (A : Matrix m n ℂ) (a : Matrix Unit n ℂ) :
    (fromRows A a).pinv =
      fromCols (A.pinv - grevilleRowCoefficient A a * (a * A.pinv))
        (grevilleRowCoefficient A a) := by
  classical
  have h := congrArg Matrix.conjTranspose (theorem_2 Aᴴ aᴴ)
  simpa only [conjTranspose_fromCols_eq_fromRows_conjTranspose,
    conjTranspose_fromRows_eq_fromCols_conjTranspose, ← Matrix.pinv_conjTranspose,
    conjTranspose_conjTranspose, conjTranspose_sub, conjTranspose_mul,
    grevilleColumnCoefficient_adjoint] using h

omit [DecidableEq m] in
/-- **Corollary 2**, Equations (58)–(60) of [benIsrael2003generalized],
Chapter 7. Appending one observation changes the minimum-norm estimate
by the new residual times the inverse column. -/
theorem corollary_2 (A : Matrix m n ℂ) (a : Matrix Unit n ℂ) (y : m → ℂ) (t : ℂ) :
    let b := grevilleRowCoefficient A a
    let x := A.pinv *ᵥ y
    (fromRows A a).pinv *ᵥ Sum.elim y (fun _ : Unit => t) =
      x + (t - (a *ᵥ x) ()) • (fun i => b i ()) := by
  dsimp only
  rw [corollary_1, fromCols_mulVec_sumElim, sub_mulVec, ← mulVec_mulVec,
    ← mulVec_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have h (z : Unit → ℂ) : (grevilleRowCoefficient A a *ᵥ z) i =
      grevilleRowCoefficient A a i () * z () := by
    simp [mulVec, dotProduct]
  rw [h, h]
  ring

open scoped Classical in
omit [DecidableEq m] in
/-- **Corollary 2** of [benIsrael2003generalized], Chapter 7.
The updated vector is a minimum-norm least-squares solution for the
augmented observation system. -/
theorem corollary_2_isMinNormLeastSquaresSolution (A : Matrix m n ℂ)
    (a : Matrix Unit n ℂ) (y : m → ℂ) (t : ℂ) :
    let b := grevilleRowCoefficient A a
    let x := A.pinv *ᵥ y
    IsMinNormLeastSquaresSolution (fromRows A a) (WithLp.toLp 2 (Sum.elim y (fun _ => t)))
      (WithLp.toLp 2 (x + (t - (a *ᵥ x) ()) • (fun i => b i ()))) := by
  dsimp only
  rw [← corollary_2]
  simpa only [toEuclideanLin_toLp] using
    isMinNormLeastSquaresSolution_pinv (fromRows A a)
      (WithLp.toLp 2 (Sum.elim y (fun _ : Unit => t)))

end Row

section PolynomialFit

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Equations (44)–(47)** of [benIsrael2003generalized], Chapter 7.
For the discrete polynomial fit, each column evaluates one monomial
at the sample points, beginning with the constant monomial. -/
def polynomialEvaluationMatrix (t : m → ℝ) (k : ℕ) : Matrix m (Fin k) ℝ :=
  Matrix.of fun i j => t i ^ (j : ℕ)

/-- **Equations (46)–(49)** of [benIsrael2003generalized], Chapter 7.
A fit of the specified degree achieves the tolerance exactly when
the pseudoinverse fit achieves it. -/
theorem polynomialFit_iff_pinv_residual_le (t : m → ℝ) (k : ℕ)
    (y : EuclideanSpace ℝ m) (ε : ℝ) :
    let A := polynomialEvaluationMatrix t k
    (∃ x, ‖A.toEuclideanLin x - y‖ ≤ ε) ↔
      ‖A.toEuclideanLin (A.pinv.toEuclideanLin y) - y‖ ≤ ε := by
  let A := polynomialEvaluationMatrix t k
  change (∃ x, ‖A.toEuclideanLin x - y‖ ≤ ε) ↔
    ‖A.toEuclideanLin (A.pinv.toEuclideanLin y) - y‖ ≤ ε
  constructor
  · rintro ⟨x, hx⟩
    exact (isLeastSquaresSolution_pinv A y x).trans hx
  · intro h
    exact ⟨A.pinv.toEuclideanLin y, h⟩

end PolynomialFit

private theorem pinv_eq_of_column (a : Matrix (Fin 3) Unit ℂ) (b : Matrix Unit (Fin 3) ℂ)
    (h : b * a = 1) (hH : (a * b).IsHermitian) : a.pinv = b := by
  symm
  refine a.pinv_unique ?_ ?_ hH (h ▸ isHermitian_one)
  · rw [Matrix.mul_assoc, h, Matrix.mul_one]
  · rw [h, Matrix.one_mul]

/-- **Exercise 13** of [benIsrael2003generalized], Chapter 7.
The two independent columns give the displayed Greville residual and
pseudoinverse. The second column alone has the inverse row shown by
deleting the first column. -/
theorem exercise_13 :
    let a₁ : Matrix (Fin 3) Unit ℂ := Matrix.of (fun i _ => (![1, 2, 0] : Fin 3 → ℂ) i)
    let a₂ : Matrix (Fin 3) Unit ℂ := Matrix.of (fun i _ => (![0, 1, -1] : Fin 3 → ℂ) i)
    let c : Matrix (Fin 3) Unit ℂ := Matrix.of (fun i _ => (![-2/5, 1/5, -1] : Fin 3 → ℂ) i)
    let b : Matrix Unit (Fin 3) ℂ := Matrix.of (fun _ j => (![-1/3, 1/6, -5/6] : Fin 3 → ℂ) j)
    grevilleColumnResidual a₁ a₂ = c ∧
      grevilleColumnCoefficient a₁ a₂ = b ∧
      (fromCols a₁ a₂).pinv =
        fromRows (Matrix.of (fun _ j => (![1/3, 1/3, 1/3] : Fin 3 → ℂ) j)) b ∧
      a₂.pinv = Matrix.of (fun _ j => (![0, 1/2, -1/2] : Fin 3 → ℂ) j) := by
  dsimp only
  let a₁ : Matrix (Fin 3) Unit ℂ := Matrix.of (fun i _ => (![1, 2, 0] : Fin 3 → ℂ) i)
  let a₂ : Matrix (Fin 3) Unit ℂ := Matrix.of (fun i _ => (![0, 1, -1] : Fin 3 → ℂ) i)
  let c : Matrix (Fin 3) Unit ℂ := Matrix.of (fun i _ => (![-2/5, 1/5, -1] : Fin 3 → ℂ) i)
  let b : Matrix Unit (Fin 3) ℂ := Matrix.of (fun _ j => (![-1/3, 1/6, -5/6] : Fin 3 → ℂ) j)
  let b₁ : Matrix Unit (Fin 3) ℂ := Matrix.of (fun _ j => (![1/5, 2/5, 0] : Fin 3 → ℂ) j)
  let b₂ : Matrix Unit (Fin 3) ℂ := Matrix.of (fun _ j => (![0, 1/2, -1/2] : Fin 3 → ℂ) j)
  change grevilleColumnResidual a₁ a₂ = c ∧
    grevilleColumnCoefficient a₁ a₂ = b ∧
    (fromCols a₁ a₂).pinv = fromRows (Matrix.of (fun _ j => (![1/3, 1/3, 1/3] : Fin 3 → ℂ) j)) b ∧
    a₂.pinv = b₂
  have h₁ : a₁.pinv = b₁ := by
    apply pinv_eq_of_column
    · ext ⟨⟩ ⟨⟩
      norm_num [a₁, b₁, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ]
    · rw [Matrix.IsHermitian]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [a₁, b₁, Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.of_apply]
  have h₂ : a₂.pinv = b₂ := by
    apply pinv_eq_of_column
    · ext ⟨⟩ ⟨⟩
      norm_num [a₂, b₂, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ]
    · rw [Matrix.IsHermitian]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [a₂, b₂, Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.of_apply]
  have hCinv : c.pinv = b := by
    apply pinv_eq_of_column
    · ext ⟨⟩ ⟨⟩
      norm_num [c, b, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ]
    · rw [Matrix.IsHermitian]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [c, b, Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.of_apply]
  have hD : a₁.pinv * a₂ = Matrix.of (fun _ _ => 2/5) := by
    rw [h₁]
    ext ⟨⟩ ⟨⟩
    norm_num [a₂, b₁, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_succ]
  have hC : grevilleColumnResidual a₁ a₂ = c := by
    rw [grevilleColumnResidual, hD]
    ext i ⟨⟩
    fin_cases i <;> norm_num [a₁, a₂, c, Matrix.mul_apply, Matrix.of_apply, Matrix.sub_apply]
  have hc : c ≠ 0 := by
    intro hz
    have h := congrFun (congrFun hz (2 : Fin 3)) ()
    norm_num [c, Matrix.of_apply] at h
  have hB : grevilleColumnCoefficient a₁ a₂ = b := by
    classical
    simp only [grevilleColumnCoefficient, hC, hc, ite_false, hCinv]
  refine ⟨hC, hB, ?_, h₂⟩
  rw [theorem_2, hD, h₁, hB]
  congr 1
  ext ⟨⟩ j
  fin_cases j <;> norm_num [b₁, b, Matrix.mul_apply, Matrix.of_apply, Matrix.sub_apply]

/-- **Exercise 13** of [benIsrael2003generalized], Chapter 7.
After swapping the two columns, the last inverse row has squared
length `1/3`. The rank-one deletion subtracts its contribution and
recovers the inverse row of the second original column. -/
theorem exercise_13_deletion :
    let a₁ : Matrix (Fin 3) Unit ℂ := Matrix.of fun i _ => (![1, 2, 0] : Fin 3 → ℂ) i
    let a₂ : Matrix (Fin 3) Unit ℂ := Matrix.of fun i _ => (![0, 1, -1] : Fin 3 → ℂ) i
    let B := fromCols a₂ a₁
    let b := grevilleColumnCoefficient a₂ a₁
    b * bᴴ = Matrix.of (fun _ _ => 1/3) ∧
      B.pinv * bᴴ =
        fromRows (Matrix.of (fun _ _ => -1/3)) (Matrix.of (fun _ _ => 1/3)) ∧
      B.pinv - B.pinv * bᴴ * (b * bᴴ)⁻¹ * b =
        fromRows (Matrix.of (fun _ j => (![0, 1/2, -1/2] : Fin 3 → ℂ) j)) 0 := by
  let a₁ : Matrix (Fin 3) Unit ℂ := Matrix.of fun i _ => (![1, 2, 0] : Fin 3 → ℂ) i
  let a₂ : Matrix (Fin 3) Unit ℂ := Matrix.of fun i _ => (![0, 1, -1] : Fin 3 → ℂ) i
  let B := fromCols a₂ a₁
  let b := grevilleColumnCoefficient a₂ a₁
  let R : Matrix Unit (Fin 3) ℂ := Matrix.of fun _ j => (![1/3, 1/3, 1/3] : Fin 3 → ℂ) j
  let S : Matrix Unit (Fin 3) ℂ := Matrix.of fun _ j => (![-1/3, 1/6, -5/6] : Fin 3 → ℂ) j
  let swap := Equiv.sumComm Unit Unit
  change b * bᴴ = _ ∧ B.pinv * bᴴ = _ ∧
    B.pinv - B.pinv * bᴴ * (b * bᴴ)⁻¹ * b = _
  have hOld : (fromCols a₁ a₂).pinv = fromRows R S := exercise_13.2.2.1
  have hSwap : (fromCols a₁ a₂).submatrix (Equiv.refl (Fin 3)) swap = B := by
    ext i (j | j) <;> rfl
  have hP : B.pinv = fromRows S R := by
    rw [← hSwap, Chapter05.pinv_submatrix_equiv, hOld]
    ext (i | i) j <;> rfl
  have hLast : b = R := by
    have h := theorem_2 a₂ a₁
    change B.pinv = fromRows (a₂.pinv - (a₂.pinv * a₁) * b) b at h
    rw [hP] at h
    ext i j
    exact (congrFun (congrFun h (Sum.inr i)) j).symm
  have hLeft : B.pinv * B = 1 := by
    rw [hP]
    ext (i | i) (j | j)
    all_goals
      cases i
      cases j
      norm_num [B, a₁, a₂, R, S, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]
  have hRank : B.rank = Fintype.card (Unit ⊕ Unit) :=
    (Chapter01.lemma_2_a (Chapter01.mem_one_iff.mpr B.mul_pinv_mul_self)).mp hLeft
  refine ⟨?_, ?_, ?_⟩
  · rw [hLast]
    ext ⟨⟩ ⟨⟩
    norm_num [R, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_succ, map_ofNat]
  · rw [hLast, hP]
    ext (i | i) ⟨⟩ <;> cases i <;>
      norm_num [R, S, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_succ, map_ofNat]
  · have h₂ := exercise_13.2.2.2
    change a₂.pinv = Matrix.of (fun _ j => (![0, 1/2, -1/2] : Fin 3 → ℂ) j) at h₂
    rw [← h₂]
    exact (exercise_12 a₂ a₁ hRank).symm

end BenIsraelGreville.Chapter07
