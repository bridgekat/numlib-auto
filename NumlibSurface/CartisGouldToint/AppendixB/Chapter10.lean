import Numlib.LinearAlgebra.Matrix.InverseDecay
import Numlib.Analysis.Matrix.SpectralExtrema

/-!
# Inverse decay for symmetric positive-definite tridiagonal matrices

The eigenvalue endpoints are actual finite spectral extrema. The ordinary
nonsingular inverse is used. The Chebyshev estimate includes equal spectral
endpoints: the decay factor is then zero, off-diagonal entries vanish, and
zero distance retains the usual zeroth-power convention.
-/

namespace CartisGouldToint

/-- Lemma B.10.1: the ordinary inverse has the exact printed exponential
entry bound, including a single eigenvalue and diagonal index distance zero. -/
theorem lemma_B_10_1 {n : ℕ} [NeZero n] (T : Matrix (Fin n) (Fin n) ℝ)
    (hpos : T.PosDef) (htri : T.IsTridiagonal) (i j : Fin n) :
    let lo := hpos.isHermitian.leastEigenvalue
    let hi := hpos.isHermitian.greatestEigenvalue
    |T⁻¹ i j| ≤ 2 / lo *
      ((Real.sqrt (hi / lo) - 1) / (Real.sqrt (hi / lo) + 1)) ^ Nat.dist i.val j.val := by
  simpa only [Real.norm_eq_abs] using
    Matrix.inverse_entry_decay htri hpos.isUnit (hpos.isHermitian.leastEigenvalue_pos hpos)
      hpos.isHermitian.leastEigenvalue_le_greatest
      hpos.isHermitian.isSymmetricBoundedBy_extrema i j

end CartisGouldToint
