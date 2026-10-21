import Numlib.Nonlinear.TransformedNewton
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Monotonicity of transformed secular Newton corrections

The correction is the actual Newton increment of the actual matrix secular function.
The zero exponent is excluded, as its power equation is identically zero; the quotient's
continuous logarithmic extension is a separate convention.
-/

noncomputable section
open Filter Topology Set
open CartisGouldToint.Chapter08.Section02

namespace CartisGouldToint.AppendixB.Chapter08

/-- The actual Newton increment for the power-transformed trust-region secular equation. -/
def transformedTrustRegionNewtonCorrection {n : ℕ} (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (Δ lambda β : ℝ) : ℝ :=
  Newton.scalarStep (fun t => transformedSecularFunction g H M β t - (Δ ^ 2) ^ β)
    (deriv (fun t => transformedSecularFunction g H M β t - (Δ ^ 2) ^ β)) lambda - lambda

/-- Lemma B.8.2: the actual transformed secular Newton increment is antitone on
nonzero exponents, has formula (B.8.7), and is largest at `-1/2` among admissible
nonzero exponents at least `-1/2`. The gradient and trust-region radius are nonzero. -/
theorem lemma_B_8_2 {n : ℕ} {g : EuclideanSpace ℝ (Fin n)}
    {H M : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) (hM : M.PosDef) (hg : g ≠ 0)
    {Δ lambda : ℝ} (hΔ : 0 < Δ) (hlambda : secularThreshold hH hM < lambda) :
    AntitoneOn (transformedTrustRegionNewtonCorrection g H M Δ lambda) ({0}ᶜ : Set ℝ) ∧
    (∀ β ≠ 0, transformedTrustRegionNewtonCorrection g H M Δ lambda β =
      (-secularData g H M lambda / deriv (secularData g H M) lambda) *
        ((1 - (Δ ^ 2 / secularData g H M lambda) ^ β) / β)) ∧
    (∀ β, -(1 / 2 : ℝ) ≤ β → β ≠ 0 →
      transformedTrustRegionNewtonCorrection g H M Δ lambda β ≤
        transformedTrustRegionNewtonCorrection g H M Δ lambda (-(1 / 2 : ℝ))) := by
  have hh := secularHessian_isSymmetric hH hM
  have hn := Optimization.SecularResolvent.toEnergy_inv_ne_zero
    hM.isPreconditioner_toEuclideanLin hg
  have ha := secular_admissible hH hM hlambda
  have he : secularData g H M =ᶠ[𝓝 lambda]
      Optimization.SecularResolvent.normSqResolvent (secularHessian H hM)
        (hM.isPreconditioner_toEuclideanLin.toEnergy (Matrix.toEuclideanLin M⁻¹ g)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hlambda] with t ht
    exact secularData_eq_resolvent hH hM ht
  have hpos : 0 < secularData g H M lambda := by
    rw [he.self_of_nhds]
    exact Optimization.SecularResolvent.normSqResolvent_pos hh hn (fun i => (ha i).ne')
  have hdiff : DifferentiableAt ℝ (secularData g H M) lambda :=
    ((Optimization.SecularResolvent.contDiffAt_normSqResolvent hh _
      (fun i => (ha i).ne') 1).differentiableAt (by norm_num)).congr_of_eventuallyEq he
  have hd : deriv (secularData g H M) lambda < 0 := by
    rw [he.deriv_eq]
    exact Optimization.SecularResolvent.deriv_normSqResolvent_neg hh hn ha
  have hmono : AntitoneOn (transformedTrustRegionNewtonCorrection g H M Δ lambda)
      ({0}ᶜ : Set ℝ) := by
    exact Newton.antitoneOn_power_scalarStep_sub hdiff hpos (sq_pos_of_pos hΔ) hd
  refine ⟨hmono, ?_, ?_⟩
  · intro β hβ
    exact Newton.power_scalarStep_sub hdiff hpos (sq_pos_of_pos hΔ) hβ hd.ne
  · intro β hβ hβ0
    exact hmono (by norm_num) (by simpa using hβ0) hβ

end CartisGouldToint.AppendixB.Chapter08
