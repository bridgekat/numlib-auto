import Numlib.LinearAlgebra.Matrix.WeightedAdjoint.Complexify
import NumlibSurface.LiesenStrakos.Chapter04.Section06

/-!
# Liesen and Strakoš, Section 4.6: Real matrices

The eigendecomposition of a real matrix uses the complexification of the matrix and
its metric. Real and complex polynomial representations have the same least degree
when both the argument and the value are real.

## Main results

* Theorem 4.6.3, `LiesenStrakos.theorem_4_6_3_real`: the eigenbasis and interpolation
  characterization for real matrices and real positive definite weights.
* Corollary 4.6.4, `LiesenStrakos.corollary_4_6_4_real`: the real minimal-polynomial
  bound and the weighted adjoint in a complex eigenbasis.
* Theorem 4.6.5 (2), `LiesenStrakos.theorem_4_6_5_one_real`: weighted normality of degree
  one with a real metric is characterized by diagonalizability, minimal polynomial degree
  at least two, and collinear complex eigenvalues.
-/

open Polynomial
open scoped Matrix ComplexOrder

namespace LiesenStrakos

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real and complex arithmetic give the same degree of weighted normality for
a real matrix and a real weight. -/
theorem isBNormalOfDegree_complexify_iff (A B : Matrix n n ℝ) (s : ℕ) :
    IsBNormalOfDegree A.complexify B.complexify s ↔ IsBNormalOfDegree A B s := by
  unfold IsBNormalOfDegree
  rw [Matrix.posDef_complexify_iff, ← Matrix.complexify_weightedAdjoint,
    Matrix.isMinDegreeRepresentation_complexify_iff]

/-- A real matrix is weighted normal exactly when its complex eigenbasis has an
admissible metric factorization and the eigenvalues have a unique least-degree
conjugation interpolant. This is the real case of Theorem 4.6.3 of [liesen2013krylov]. -/
theorem theorem_4_6_3_real (A B : Matrix n n ℝ) (hB : B.PosDef) (s : ℕ) :
    IsBNormalOfDegree A B s ↔
      ∃ (Y : Matrix n n ℂ) (d : n → ℂ), IsUnit Y ∧
        A.complexify = Y * Matrix.diagonal d * Y⁻¹ ∧
        AdmissibleEigenbasisMetric B.complexify Y d ∧
        ∃! p : ℂ[X], p.degree = s ∧ aeval (Matrix.diagonal d) p = (Matrix.diagonal d)ᴴ ∧
          ∀ q : ℂ[X], aeval (Matrix.diagonal d) q = (Matrix.diagonal d)ᴴ →
            (s : WithBot ℕ) ≤ q.degree := by
  rw [← isBNormalOfDegree_complexify_iff, theorem_4_6_3 A.complexify B.complexify
    (Matrix.posDef_complexify_iff.2 hB)]

/-- For a real weighted-normal matrix, the degree of the interpolant is determined
by the complex eigenvalues and is at most one less than the degree of the real
minimal polynomial. The real weight and adjoint have the same factorization in the
complex eigenbasis as in the complex case. This is Corollary 4.6.4 of [liesen2013krylov]
for real matrices. -/
theorem corollary_4_6_4_real {A B : Matrix n n ℝ} {s : ℕ}
    (h : IsBNormalOfDegree A B s) :
    s ≤ (minpoly ℝ A).natDegree - 1 ∧
      ∃ (Y : Matrix n n ℂ) (d : n → ℂ), IsUnit Y ∧
        A.complexify = Y * Matrix.diagonal d * Y⁻¹ ∧ AdmissibleEigenbasisMetric B.complexify Y d ∧
        (A.weightedAdjoint B).complexify = Y * (Matrix.diagonal d)ᴴ * Y⁻¹ ∧
        ∀ t : ℕ, (∃ p : ℂ[X], p.degree = t ∧ (∀ i, p.eval (d i) = star (d i)) ∧
          ∀ q : ℂ[X], (∀ i, q.eval (d i) = star (d i)) → (t : WithBot ℕ) ≤ q.degree) ↔
          t = s := by
  have hInt := IsIntegral.of_finite ℝ A
  have hlt := h.2.degree_lt_minpoly hInt
  rw [degree_eq_natDegree (minpoly.ne_zero hInt)] at hlt
  have hs : s < (minpoly ℝ A).natDegree := WithBot.coe_lt_coe.mp hlt
  refine ⟨by omega, ?_⟩
  have hComplex := (isBNormalOfDegree_complexify_iff A B s).2 h
  simpa only [Matrix.complexify_weightedAdjoint] using (corollary_4_6_4 hComplex).2

private theorem mul_weightedAdjoint_eq {A B : Matrix n n ℂ} (hB : B.PosDef) :
    B * A.weightedAdjoint B = Aᴴ * B := by
  have hdet := (Matrix.isUnit_iff_isUnit_det B).1 hB.isUnit
  rw [Matrix.weightedAdjoint, ← Matrix.mul_assoc B (B⁻¹ * Aᴴ) B,
    ← Matrix.mul_assoc B B⁻¹ Aᴴ, Matrix.mul_nonsing_inv B hdet, one_mul]

private theorem weightedAdjoint_eq_of_mul_eq {A B T : Matrix n n ℂ} (hB : B.PosDef)
    (hT : B * T = Aᴴ * B) : A.weightedAdjoint B = T := by
  have hdet := (Matrix.isUnit_iff_isUnit_det B).1 hB.isUnit
  rw [Matrix.weightedAdjoint, Matrix.mul_assoc, ← hT,
    Matrix.nonsing_inv_mul_cancel_left B T hdet]

/-- If a complex positive definite weight makes the complexification of a real matrix
weighted normal of degree $s$, there is a real positive definite weight of the same
degree. -/
theorem exists_isBNormalOfDegree_complexify_iff (A : Matrix n n ℝ) (s : ℕ) :
    (∃ B : Matrix n n ℂ, IsBNormalOfDegree A.complexify B s) ↔
      ∃ B : Matrix n n ℝ, IsBNormalOfDegree A B s := by
  constructor
  · rintro ⟨B, h⟩
    let X := A.complexify
    let σ : Matrix n n ℂ →+* Matrix n n ℂ := (starRingEnd ℂ).mapMatrix
    let T := X.weightedAdjoint B
    have hX : σ X = X := Matrix.star_map_complexify A
    have hXH : σ Xᴴ = Xᴴ := by
      change σ A.complexifyᴴ = A.complexifyᴴ
      rw [← Matrix.complexify_conjTranspose]
      exact Matrix.star_map_complexify Aᴴ
    have hInv (M : Matrix n n ℂ) : σ (σ M) = M := by
      ext i j
      simp [σ, Matrix.map_apply]
    have hTranspose : σ B = Bᵀ := by
      ext i j
      have he := congrArg (fun M : Matrix n n ℂ => M j i) h.1.1.eq
      simpa [σ, Matrix.map_apply] using he
    have hPos : (σ B).PosDef := by rw [hTranspose]; exact h.1.transpose
    have hRel : B * T = Xᴴ * B := mul_weightedAdjoint_eq h.1
    have hRelConj : σ B * σ T = Xᴴ * σ B := by
      have hEq := congrArg σ hRel
      rwa [map_mul, map_mul, hXH] at hEq
    have hAdjConj : X.weightedAdjoint (σ B) = σ T := weightedAdjoint_eq_of_mul_eq hPos hRelConj
    have hEval (p : ℂ[X]) : σ (aeval X p) = aeval X (p.map (starRingEnd ℂ)) := by
      have he := Matrix.star_map_aeval X p
      change σ (aeval X p) = aeval (σ X) (p.map (starRingEnd ℂ)) at he
      rwa [hX] at he
    have hmap (p : ℂ[X]) : (p.map (starRingEnd ℂ)).degree = p.degree :=
      degree_map_eq_of_injective (f := starRingEnd ℂ) star_injective p
    obtain ⟨p, hpd, hp, hpmin⟩ := h.2
    change aeval X p = T at hp
    change ∀ q : ℂ[X], aeval X q = T → (s : WithBot ℕ) ≤ q.degree at hpmin
    have hConj : IsBNormalOfDegree X (σ B) s := by
      refine ⟨hPos, p.map (starRingEnd ℂ), (hmap p).trans hpd, ?_, ?_⟩
      · rw [hAdjConj, ← hEval p, hp]
      · intro q hq
        rw [hAdjConj] at hq
        exact (hpmin _ (by rw [← hEval q, hq, hInv])).trans_eq (hmap q)
    obtain ⟨Y, d, hY, hdiag, -⟩ := (theorem_4_6_3 X B h.1 s).1 h
    have hSame : σ T = T := hAdjConj.symm.trans
      ((hConj.eigenbasis hY hdiag).2.1.trans (h.eigenbasis hY hdiag).2.1.symm)
    let R : Matrix n n ℝ := B.map Complex.re
    let D : Matrix n n ℂ := (1/2 : ℝ) • (B + σ B)
    have hRC : R.complexify = D := by
      ext i j
      change ((B i j).re : ℂ) = (1/2 : ℝ) • (B i j + star (B i j))
      apply Complex.ext <;> simp [Complex.real_smul]
      ring
    have hD : D.PosDef := (h.1.add hPos).smul (show 0 < (1/2 : ℝ) by norm_num)
    have hDT : D * T = Xᴴ * D := by
      change ((1/2 : ℝ) • (B + σ B)) * T = Xᴴ * ((1/2 : ℝ) • (B + σ B))
      rw [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hRel, ← hSame, hRelConj]
    have hT : X.weightedAdjoint D = T := weightedAdjoint_eq_of_mul_eq hD hDT
    have hNormalD : IsBNormalOfDegree X D s := by
      refine ⟨hD, ?_⟩
      rw [hT]
      exact h.2
    exact ⟨R, (isBNormalOfDegree_complexify_iff A R s).1 (by rwa [hRC])⟩
  · rintro ⟨B, hB⟩
    exact ⟨B.complexify, (isBNormalOfDegree_complexify_iff A B s).2 hB⟩

/-- A real matrix admits a real positive definite weight for which it is weighted
normal of degree one if and only if its complexification is diagonalizable with
collinear eigenvalues and the real minimal polynomial has degree at least two.
This is the real case of Theorem 4.6.5 (2) of [liesen2013krylov]. -/
theorem theorem_4_6_5_one_real (A : Matrix n n ℝ) :
    (∃ B : Matrix n n ℝ, IsBNormalOfDegree A B 1) ↔
      ∃ (Y : Matrix n n ℂ) (d : n → ℂ), IsUnit Y ∧
        A.complexify = Y * Matrix.diagonal d * Y⁻¹ ∧
        2 ≤ (minpoly ℝ A).natDegree ∧
        ∃ z w : ℂ, w ≠ 0 ∧ ∀ i, ∃ t : ℝ, d i = z + (t : ℂ) * w := by
  rw [← exists_isBNormalOfDegree_complexify_iff, theorem_4_6_5_one,
    Matrix.minpoly_complexify, natDegree_map_eq_of_injective Complex.ofReal_injective]
  rfl

end LiesenStrakos
