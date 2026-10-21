import Numlib.Analysis.Calculus.NormPowerSharpBounds
import NumlibSurface.CartisGouldToint.AppendixA.Section08.FractionalFactorial

/-!
# Derivatives of radial regularizers

The higher derivative clause of Cartis, Gould and Toint, Lemma B.4.1 has a false
fractional-power norm formula. The valid replacement below gives an explicit
coefficient bound independent of dimension, and keeps the exact radial evaluation
separate. The sharp lower-order diagonal norm and the repeated-base-vector evaluation hold
through the origin, including in zero dimension.
-/

noncomputable section

namespace CartisGouldToint.AppendixB.Chapter04

/-- Equations (B.4.1) and (B.4.2), with the diagonal tensor norm defined in (B.4.4).
The factorial quotient is the book's finite product, and both identities include `s = 0`.
The proof holds also for `p = 0` and the zero-dimensional Euclidean space. -/
theorem lemma_B_4_1_lower_derivatives {d p j : ℕ} {β : ℝ}
    (hβ : β ∈ Set.Ioc 0 1) (hj : j ≤ p) (s : EuclideanSpace ℝ (Fin d)) :
    (iteratedFDeriv ℝ j (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖ ^ ((p : ℝ) + β))
      s).diagonalNorm =
        AppendixA.Section08.fractionalFactorial p β /
          AppendixA.Section08.fractionalFactorial (p - j) β *
            ‖s‖ ^ (((p - j : ℕ) : ℝ) + β) ∧
      iteratedFDeriv ℝ j (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖ ^ ((p : ℝ) + β))
        s (fun _ => s) =
          AppendixA.Section08.fractionalFactorial p β /
            AppendixA.Section08.fractionalFactorial (p - j) β * ‖s‖ ^ ((p : ℝ) + β) := by
  have hn : (j : ℝ) < (p : ℝ) + β := by
    have : (j : ℝ) ≤ p := by exact_mod_cast hj
    linarith [hβ.1]
  have hprod := AppendixA.Section08.fallingProduct_eq_fractionalFactorial_div hβ.1 hj
  have he : (p : ℝ) + β - j = ((p - j : ℕ) : ℝ) + β := by
    rw [Nat.cast_sub hj]
    ring
  constructor
  · simpa only [hprod, he] using diagonalNorm_iteratedFDeriv_normRpow hn s
  · simpa only [hprod] using iteratedFDeriv_normRpow_apply_self hn s

/-- A corrected replacement for (B.4.3): off the origin the regularizer is smooth and
its next derivative has an explicit bound obtained from the actual directional
coefficient recurrence. The coefficient depends only on `p` and `β`. This holds for
all real `β`, hence in particular for the source range `0 < β ≤ 1`. -/
theorem lemma_B_4_1_higher_derivative_bound {d : ℕ} (p : ℕ) (β : ℝ)
    {s : EuclideanSpace ℝ (Fin d)} (hs : s ≠ 0) :
    ContDiffAt ℝ (p + 1) (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖ ^ ((p : ℝ) + β)) s ∧
      ‖iteratedFDeriv ℝ (p + 1)
        (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖ ^ ((p : ℝ) + β)) s‖ ≤
        normRpowDerivativeBound ((p : ℝ) + β) (p + 1) * ‖s‖ ^ (β - 1) := by
  refine ⟨(contDiffOn_normRpow ((p : ℝ) + β) (p + 1)).contDiffAt
    (isOpen_compl_singleton.mem_nhds hs), ?_⟩
  have he : (p : ℝ) + β - ((p + 1 : ℕ) : ℝ) = β - 1 := by push_cast; ring
  simpa only [he] using
    norm_iteratedFDeriv_normRpow_le_coefficient ((p : ℝ) + β) (p + 1) hs

/-- The exact radial evaluation in the corrected higher-order clause. Its coefficient
is generally smaller than the full derivative norm and is not used as an upper bound. -/
theorem lemma_B_4_1_higher_radial_evaluation {d : ℕ} (p : ℕ) (β : ℝ)
    {s : EuclideanSpace ℝ (Fin d)} (hs : s ≠ 0) :
    iteratedFDeriv ℝ (p + 1)
        (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖ ^ ((p : ℝ) + β)) s
        (fun _ => ‖s‖⁻¹ • s) =
      (∏ i : Fin (p + 1), ((p : ℝ) + β - i)) * ‖s‖ ^ (β - 1) := by
  have he : (p : ℝ) + β - ((p + 1 : ℕ) : ℝ) = β - 1 := by push_cast; ring
  simpa only [he] using iteratedFDeriv_normRpow_apply_unit ((p : ℝ) + β) (p + 1) hs

end CartisGouldToint.AppendixB.Chapter04
