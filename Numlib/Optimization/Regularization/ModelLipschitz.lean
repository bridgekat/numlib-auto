import Numlib.Optimization.Regularization.ModelCriticality
import Numlib.Analysis.Calculus.TaylorModel.JetDerivative
import Numlib.Analysis.InnerProductSpace.NormPow.Lipschitz
import Mathlib.Tactic

/-!
# Highest-derivative Lipschitz regularity of actual regularized finite models

The finite tensor polynomial has a constant highest derivative. Thus the
highest derivative variation comes solely from the actual norm-power penalty.
The derived Lipschitz constant is uniform over all supplied tensor jets.
-/

namespace ModelDecrease
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The highest actual derivative of the norm-regularized finite model is
globally Lipschitz, with its constant chosen before the supplied tensor jet. -/
theorem exists_lipschitz_iteratedFDeriv_penalized_ofJet (p : ℕ) (σ : ℝ) :
    ∃ L ≥ 0, ∀ (A : FormalMultilinearSeries ℝ E ℝ) (x y : E),
      ‖iteratedFDeriv ℝ p (penalized (TaylorModel.ofJet A p) p σ) x -
        iteratedFDeriv ℝ p (penalized (TaylorModel.ofJet A p) p σ) y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨L, hL, hbound⟩ := exists_lipschitz_iteratedFDeriv_normPow (E := E) p
  let c : ℝ := σ / ((p + 1).factorial : ℝ)
  refine ⟨|c| * L, mul_nonneg (abs_nonneg _) hL, ?_⟩
  intro A x y
  have hpoly : ContDiff ℝ p (TaylorModel.ofJet A p) := TaylorModel.contDiff_ofJet A p p
  have hpow : ContDiff ℝ p (fun z : E => ‖z‖ ^ (p + 1)) := by
    have hp : (p : ℝ) < ((p + 1 : ℕ) : ℝ) := by push_cast; linarith
    simpa only [Real.rpow_natCast] using (contDiff_normRpow_of_nat_lt (E := E) hp)
  have hder (z : E) :
      iteratedFDeriv ℝ p (penalized (TaylorModel.ofJet A p) p σ) z =
        iteratedFDeriv ℝ p (TaylorModel.ofJet A p) z +
          c • iteratedFDeriv ℝ p (fun w : E => ‖w‖ ^ (p + 1)) z := by
    have hadd := iteratedFDeriv_add_apply (x := z) hpoly.contDiffAt (hpow.contDiffAt.const_smul c)
    have hscale := iteratedFDeriv_const_smul_apply' (x := z) (a := c) hpow.contDiffAt
    rw [hscale] at hadd
    convert! hadd using 1
  rw [hder x, hder y, TaylorModel.iteratedFDeriv_ofJet_top_eq A p x y]
  have he : (iteratedFDeriv ℝ p (TaylorModel.ofJet A p) y +
        c • iteratedFDeriv ℝ p (fun w : E => ‖w‖ ^ (p + 1)) x) -
      (iteratedFDeriv ℝ p (TaylorModel.ofJet A p) y +
        c • iteratedFDeriv ℝ p (fun w : E => ‖w‖ ^ (p + 1)) y) =
      c • (iteratedFDeriv ℝ p (fun w : E => ‖w‖ ^ (p + 1)) x -
        iteratedFDeriv ℝ p (fun w : E => ‖w‖ ^ (p + 1)) y) := by
    rw [smul_sub]
    abel
  rw [he, norm_smul, Real.norm_eq_abs]
  calc _ ≤ |c| * (L * ‖x - y‖) := mul_le_mul_of_nonneg_left (hbound x y) (abs_nonneg _)
    _ = _ := by ring

end ModelDecrease
