import Numlib.Krylov.Lanczos.Monotonicity
import Numlib.Krylov.Convergence.CG
import Numlib.Analysis.Matrix.SpectralExtrema
import Mathlib.Tactic
/-!
# Actual Lanczos condition numbers and their finite maximum

The maximum ranges over exactly the positive projected dimensions. A condition
number of one forces an unreduced projected matrix to have dimension one;
applying this at the full grade justifies genuine one-step termination.
-/

open scoped Matrix ComplexOrder
namespace Lanczos
open Krylov
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An unreduced shifted Lanczos matrix of condition number one has dimension one. -/
theorem eq_zero_of_shifted_condition_eq_one (A : E →ₗ[ℝ] E) (g : E)
    {m : ℕ} (hm : m + 1 ≤ grade A g) (τ : ℝ)
    (hPD : (tridiag A g (m + 1) + τ • 1).PosDef)
    (hκ : (shifted_tridiag_isHermitian A g (m + 1) τ).greatestEigenvalue /
      (shifted_tridiag_isHermitian A g (m + 1) τ).leastEigenvalue = 1) : m = 0 := by
  let T := tridiag A g (m + 1) + τ • 1
  let hT := shifted_tridiag_isHermitian A g (m + 1) τ
  have hlo : 0 < hT.leastEigenvalue := hT.leastEigenvalue_pos hPD
  have heq : hT.greatestEigenvalue = hT.leastEigenvalue :=
    (div_eq_one_iff_eq hlo.ne').mp hκ
  have hb : (Matrix.toEuclideanLin T).IsSymmetricBoundedBy
      hT.leastEigenvalue hT.leastEigenvalue := by
    have hh := hT.isSymmetricBoundedBy_extrema
    rw [heq] at hh
    exact hh
  by_contra hnot
  have hmpos : 0 < m := Nat.pos_of_ne_zero hnot
  let j : Fin m := ⟨0, hmpos⟩
  have he := hb.apply_eq_smul (PiLp.single 2 j.succ (1 : ℝ))
  have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin (m + 1)) => v j.castSucc) he
  have hne : j.castSucc ≠ j.succ := by simp [Fin.ext_iff]
  have hzero : T j.castSucc j.succ = 0 := by
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, PiLp.single_apply,
      Matrix.mulVec, dotProduct, hne] using hcoord
  exact shifted_tridiag_offdiag_ne A g hm τ j hzero

/-- The actual extreme-eigenvalue condition number of a shifted Lanczos matrix. -/
noncomputable def conditionNumber (A : E →ₗ[ℝ] E) (g : E) (m : ℕ) (τ : ℝ) : ℝ :=
  let hT := shifted_tridiag_isHermitian A g (m + 1) τ
  hT.greatestEigenvalue / hT.leastEigenvalue

omit [FiniteDimensional ℝ E] in
/-- Positive-definite shifted Lanczos matrices have condition number at least one. -/
theorem one_le_conditionNumber (A : E →ₗ[ℝ] E) (g : E) (m : ℕ) (τ : ℝ)
    (hPD : (tridiag A g (m + 1) + τ • 1).PosDef) : 1 ≤ conditionNumber A g m τ := by
  exact (one_le_div (hPD.isHermitian.leastEigenvalue_pos hPD)).mpr
    hPD.isHermitian.leastEigenvalue_le_greatest

/-- The maximum of all actual shifted projected condition numbers in a finite sequence. -/
noncomputable def maxCondition (A : E →ₗ[ℝ] E) (g : E) (G : ℕ)
    (shifts : Fin (G + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => conditionNumber A g i.val (shifts i))

omit [FiniteDimensional ℝ E] in
/-- Each actual projected condition number is bounded by its genuine finite maximum. -/
theorem conditionNumber_le_maxCondition (A : E →ₗ[ℝ] E) (g : E) (G : ℕ)
    (shifts : Fin (G + 1) → ℝ) (i : Fin (G + 1)) :
    conditionNumber A g i.val (shifts i) ≤ maxCondition A g G shifts := by
  exact Finset.le_sup' (fun j : Fin (G + 1) => conditionNumber A g j.val (shifts j))
    (Finset.mem_univ i)

omit [FiniteDimensional ℝ E] in
/-- A finite maximum of positive-definite projected condition numbers is at least one. -/
theorem one_le_maxCondition (A : E →ₗ[ℝ] E) (g : E) (G : ℕ)
    (shifts : Fin (G + 1) → ℝ)
    (hPD : ∀ i, (tridiag A g (i.val + 1) + shifts i • 1).PosDef) :
    1 ≤ maxCondition A g G shifts :=
  (one_le_conditionNumber A g 0 (shifts 0) (hPD 0)).trans
    (conditionNumber_le_maxCondition A g G shifts 0)

/-- If the genuine maximum condition number through the grade is one, the grade is one. -/
theorem eq_zero_of_maxCondition_eq_one (A : E →ₗ[ℝ] E) (g : E) (G : ℕ)
    (hG : G + 1 ≤ grade A g) (shifts : Fin (G + 1) → ℝ)
    (hPD : (tridiag A g (G + 1) + shifts (Fin.last G) • 1).PosDef)
    (heq : maxCondition A g G shifts = 1) : G = 0 := by
  have hle := conditionNumber_le_maxCondition A g G shifts (Fin.last G)
  rw [heq] at hle
  have hone : conditionNumber A g G (shifts (Fin.last G)) = 1 :=
    le_antisymm hle (one_le_conditionNumber A g G _ hPD)
  exact eq_zero_of_shifted_condition_eq_one A g hG _ hPD hone
end Lanczos
