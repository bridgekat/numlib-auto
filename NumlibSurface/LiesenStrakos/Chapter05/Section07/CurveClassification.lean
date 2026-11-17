/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Convergence.GMRES.CurveClassification
import Numlib.Krylov.Convergence.GMRES.CurveFactor

/-!
# Liesen and Strakoš, §5.7.4: Classification of prescribed GMRES curves

Theorem 5.7.8 characterizes all systems with prescribed eigenvalues and GMRES
residual norms. The upper triangular factor constrained by the normalized
characteristic polynomial is equivalent to a free upper triangular block.
-/

open Krylov Matrix Polynomial
open scoped Matrix

namespace LiesenStrakos.Chapter05

/-- **Theorem 5.7.8** of [liesen2013krylov]. Let $N=n+1$, let $f$ be a positive
nonincreasing sequence of $N$ residual norms, and let $\mu$ be a list of $N$
nonzero eigenvalues counted with multiplicity. The following conditions are
equivalent.

1. The characteristic polynomial is $p(z)=\prod_i(z-\mu_i)$ and the GMRES
   residual norms, starting at zero, are $f_0,\ldots,f_{N-1}$.
2. $A=WTC T^{-1}W^*$ and $b=Wh$, with $W$ unitary, $T$ nonsingular upper
   triangular, $Ts=h$, and $s$ the negated nonconstant coefficients of
   $p(z)/p(0)$. Here $C$ is the last-column companion matrix of $p$, and
   the coordinates of $h$ are $\sqrt{f_i^2-f_{i+1}^2}$ with $f_N=0$.
3. $A=WYC Y^{-1}W^*$ and $b=Wh$, where $W$ is unitary and
   $Y=[h,\binom{R}{0}]$ with an arbitrary nonsingular upper triangular
   block $R$ of order $N-1$. -/
theorem theorem_5_7_8 (n : ℕ) (f : Fin (n + 1) → ℝ)
    (hf : Antitone f) (hpos : 0 < f (Fin.last n))
    (μ : Fin (n + 1) → ℂ) (hμ : ∀ i, μ i ≠ 0)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (b : Fin (n + 1) → ℂ) :
    let p : ℂ[X] := ∏ i, (X - C (μ i))
    let M := Matrix.companionLastColumn n p
    let s := gmresCompanionCoefficients n p
    let h := WithLp.ofLp (gmresCurveCoordinates f)
    let realizes := A.charpoly = p ∧
      ∀ k : Fin (n + 1), ∃ x : EuclideanSpace ℂ (Fin (n + 1)),
        IsMinResidualIterate (Matrix.toEuclideanLin A) (WithLp.toLp 2 b) 0 k.val x ∧
        ‖WithLp.toLp 2 b - Matrix.toEuclideanLin A x‖ = f k
    let triangular := ∃ W T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      W ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ ∧ T.IsUpperTriangular ∧ IsUnit T ∧
      T *ᵥ s = h ∧ b = W *ᵥ h ∧ A = W * T * M * T⁻¹ * Wᴴ
    let block := ∃ (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (R : Matrix (Fin n) (Fin n) ℂ),
      W ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ ∧ R.IsUpperTriangular ∧ IsUnit R ∧
      b = W *ᵥ h ∧
      A = W * gmresCompanionBlock h R * M * (gmresCompanionBlock h R)⁻¹ * Wᴴ
    (realizes ↔ triangular) ∧ (triangular ↔ block) := by
  intro p M s h realizes triangular block
  have hp : p.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (μ i)
  have hd : p.natDegree = n + 1 := by simp [p, natDegree_finsetProd_X_sub_C_eq_card]
  have h0 : p.eval 0 ≠ 0 := by
    simp only [p, eval_prod, eval_sub, eval_X, eval_C, zero_sub]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => neg_ne_zero.mpr (hμ i)
  have hs : M *ᵥ s = Pi.single 0 1 :=
    companionLastColumn_mul_gmresCompanionCoefficients n p hp hd h0
  have hMu : IsUnit M := isUnit_companionLastColumn n p hp hd h0
  have hh : h (Fin.last n) ≠ 0 := by
    change gmresCurveCoordinates f (Fin.last n) ≠ 0
    rw [gmresCurveCoordinates_last f hpos.le]
    exact Complex.ofReal_ne_zero.mpr hpos.ne'
  have hfactor (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :=
    gmres_companion_factor_iff hMu (Matrix.companionLastColumn_castSucc n p) hs hh B
  refine ⟨gmres_curve_iff_companion A b p hp hd h0 f hf hpos, ?_⟩
  constructor
  · rintro ⟨W, T, hW, hT, hTu, hTs, hb, hA⟩
    obtain ⟨R, hR, hRu, he⟩ := (hfactor (T * M * T⁻¹)).1 ⟨T, hT, hTu, hTs, rfl⟩
    refine ⟨W, R, hW, hR, hRu, hb, ?_⟩
    have he' := congrArg (fun B => W * B * Wᴴ) he
    rw [hA]
    simpa only [Matrix.mul_assoc] using he'
  · rintro ⟨W, R, hW, hR, hRu, hb, hA⟩
    let Y := gmresCompanionBlock h R
    obtain ⟨T, hT, hTu, hTs, he⟩ := (hfactor (Y * M * Y⁻¹)).2 ⟨R, hR, hRu, rfl⟩
    refine ⟨W, T, hW, hT, hTu, hTs, hb, ?_⟩
    have he' := congrArg (fun B => W * B * Wᴴ) he
    rw [hA]
    simpa only [Matrix.mul_assoc] using he'

end LiesenStrakos.Chapter05
