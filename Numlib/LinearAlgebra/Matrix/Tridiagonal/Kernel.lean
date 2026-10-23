/-
Upstreaming candidate: general material with no numerical-analysis-specific content.
Natural home: `Mathlib.LinearAlgebra.Matrix`.
-/
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.Analysis.Matrix.SpectralExtrema
import Mathlib.Tactic
open scoped Matrix BigOperators ComplexOrder

/-!
# Kernels of unreduced tridiagonal matrices

A zero first coordinate propagates through an unreduced tridiagonal kernel.
A positive - semidefinite system with a nonzero first - coordinate right side is
therefore positive definite whenever the actual system has a solution.
-/

namespace Matrix

/-- A kernel vector of an unreduced tridiagonal matrix with zero first coordinate vanishes. -/
theorem eq_zero_of_tridiagonal_kernel_first_zero {R : Type*} [Semiring R] [NoZeroDivisors R]
    {m : ℕ}
    {T : Matrix (Fin (m + 1)) (Fin (m + 1)) R} (htri : T.IsTridiagonal)
    (hoff : ∀ j : Fin m, T j.castSucc j.succ ≠ 0)
    {v : Fin (m + 1) → R} (hv : T *ᵥ v = 0) (hv0 : v 0 = 0) : v = 0 := by
  have hprefix : ∀ k : ℕ, ∀ i : Fin (m + 1), i.val ≤ k → v i = 0 := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have he : i = 0 := Fin.ext (by simpa using Nat.eq_zero_of_le_zero hi)
      simpa only [he] using hv0
    | succ k ih =>
      intro i hi
      by_cases hik : i.val ≤ k
      · exact ih i hik
      · have hie : i.val = k + 1 := by omega
        have hkm : k < m := by omega
        let j : Fin m := ⟨k, hkm⟩
        have hij : i = j.succ := Fin.ext (by simp [j]; omega)
        rw [hij]
        have hrow := congrFun hv j.castSucc
        change (∑ l, T j.castSucc l * v l) = 0 at hrow
        have hsum : (∑ l, T j.castSucc l * v l) = T j.castSucc j.succ * v j.succ := by
          apply Finset.sum_eq_single j.succ
          · intro l hl hlj
            by_cases hlk : l.val ≤ k
            · rw [ih l hlk, mul_zero]
            · have hfar : k + 1 < l.val := by
                have hne : l.val ≠ k + 1 := by
                  intro he
                  exact hlj (Fin.ext (by simpa [j] using he))
                omega
              have he : T j.castSucc l = 0 :=
                (isTridiagonal_iff_fin.mp htri) j.castSucc l (Or.inr (by simpa [j] using hfar))
              rw [he, zero_mul]
          · simp
        rw [hsum] at hrow
        exact (mul_eq_zero.mp hrow).resolve_left (hoff j)
  funext i
  exact hprefix i.val i le_rfl


/-- Solvability with a nonzero coordinate right side makes an unreduced semidefinite matrix
definite. -/
theorem posDef_of_tridiagonal_solve {m : ℕ}
    {T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (htri : T.IsTridiagonal)
    (hoff : ∀ j : Fin m, T j.castSucc j.succ ≠ 0) (hPSD : T.PosSemidef)
    {b : ℝ} (hb : b ≠ 0) (y : EuclideanSpace ℝ (Fin (m + 1)))
    (hsolve : toEuclideanLin T y = b • PiLp.single 2 (0 : Fin (m + 1)) (1 : ℝ)) : T.PosDef := by
  apply hPSD.posDef_iff_mulVec_injective.mpr
  intro u v huv
  have hker : T *ᵥ (u - v) = 0 := by simp only [mulVec_sub, huv, sub_self]
  let w : EuclideanSpace ℝ (Fin (m + 1)) := WithLp.toLp 2 (u - v)
  have hw : toEuclideanLin T w = 0 := by
    change WithLp.toLp 2 (T *ᵥ (u - v)) = 0
    rw [hker]; rfl
  have he := (isSymmetric_toEuclideanLin_iff.mpr hPSD.isHermitian) y w
  rw [hsolve, hw, inner_zero_right] at he
  have hw0 : (u - v) 0 = 0 := by
    have hh : w 0 * b = 0 := by simpa [PiLp.inner_apply, PiLp.single_apply] using he
    exact (mul_eq_zero.mp hh).resolve_right hb
  have hz := eq_zero_of_tridiagonal_kernel_first_zero htri hoff hker hw0
  exact sub_eq_zero.mp hz

end Matrix
