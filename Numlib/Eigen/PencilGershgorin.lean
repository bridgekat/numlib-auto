import Numlib.Eigen.Pencil
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# Row bounds for real matrix pencils

Gershgorin's theorem applied to the singular shifted matrix gives row regions for a
real matrix pencil. A positive strictly dominant diagonal in its second matrix turns
each region into a bounded interval with sign-correct endpoints.
-/

open Finset
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The absolute off-diagonal row sum. -/
noncomputable def offDiagonalRowSum (A : Matrix ι ι ℝ) (i : ι) : ℝ :=
  ∑ j ∈ univ.erase i, |A i j|

/-- Absolute off-diagonal row sums are nonnegative. -/
theorem offDiagonalRowSum_nonneg (A : Matrix ι ι ℝ) (i : ι) :
    0 ≤ offDiagonalRowSum A i := Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Every real pencil eigenvalue belongs to one of the generalized Gershgorin row regions.
No symmetry or definiteness is needed for this inclusion. -/
theorem exists_row_abs_sub_le_of_mem_pencilSpectrum {A B : Matrix ι ι ℝ} {μ : ℝ}
    (hμ : μ ∈ pencilSpectrum A B) :
    ∃ i, |A i i - μ * B i i| ≤ offDiagonalRowSum A i + |μ| * offDiagonalRowSum B i := by
  have hd : (A - μ • B).det = 0 := hμ
  have hr : ∃ i, |A i i - μ * B i i| ≤ offDiagonalRowSum (A - μ • B) i := by
    by_contra! h
    apply det_ne_zero_of_sum_row_lt_diag (A := A - μ • B) _ hd
    intro i
    simpa only [offDiagonalRowSum, Real.norm_eq_abs, sub_apply, smul_apply, smul_eq_mul] using h i
  obtain ⟨i, hi⟩ := hr
  refine ⟨i, hi.trans ?_⟩
  unfold offDiagonalRowSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  simpa only [sub_apply, smul_apply, smul_eq_mul, abs_mul] using
    abs_sub (A i j) (μ * B i j)

/-- Solving a generalized Gershgorin row inequality requires both denominator signs.
Taking their minimum and maximum handles either sign of the eigenvalue and numerators. -/
theorem pencil_row_interval {h m a b μ : ℝ} (hb : 0 ≤ b) (hm : b < m)
    (hμ : |h - μ * m| ≤ a + |μ| * b) :
    min ((h - a) / (m - b)) ((h - a) / (m + b)) ≤ μ ∧
      μ ≤ max ((h + a) / (m - b)) ((h + a) / (m + b)) := by
  have hminus : 0 < m - b := sub_pos.mpr hm
  have hplus : 0 < m + b := by linarith
  rcases le_or_gt 0 μ with hpos | hneg
  · rw [abs_of_nonneg hpos, abs_le] at hμ
    constructor
    · apply (min_le_right _ _).trans
      apply (div_le_iff₀ hplus).mpr
      nlinarith [hμ.2]
    · apply le_trans _ (le_max_left _ _)
      apply (le_div_iff₀ hminus).mpr
      nlinarith [hμ.1]
  · rw [abs_of_neg hneg, abs_le] at hμ
    constructor
    · apply (min_le_left _ _).trans
      apply (div_le_iff₀ hminus).mpr
      nlinarith [hμ.2]
    · apply le_trans _ (le_max_right _ _)
      apply (le_div_iff₀ hplus).mpr
      nlinarith [hμ.1]

/-- Positive strict row dominance bounds every real pencil eigenvalue between the two
sign-correct endpoints of a row region. -/
theorem exists_row_interval_of_mem_pencilSpectrum {A B : Matrix ι ι ℝ} {μ : ℝ}
    (hB : ∀ i, offDiagonalRowSum B i < B i i) (hμ : μ ∈ pencilSpectrum A B) :
    ∃ i,
      min ((A i i - offDiagonalRowSum A i) / (B i i - offDiagonalRowSum B i))
        ((A i i - offDiagonalRowSum A i) / (B i i + offDiagonalRowSum B i)) ≤ μ ∧
      μ ≤ max ((A i i + offDiagonalRowSum A i) / (B i i - offDiagonalRowSum B i))
        ((A i i + offDiagonalRowSum A i) / (B i i + offDiagonalRowSum B i)) := by
  obtain ⟨i, hi⟩ := exists_row_abs_sub_le_of_mem_pencilSpectrum hμ
  exact ⟨i, pencil_row_interval (offDiagonalRowSum_nonneg B i) (hB i) hi⟩

end Matrix
