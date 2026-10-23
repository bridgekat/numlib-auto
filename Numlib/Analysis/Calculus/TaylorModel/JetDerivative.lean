import Numlib.Analysis.Calculus.TaylorModel.JetBounds
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Exact degree bounds for arbitrary finite tensor jets

The chain rule for the diagonal map and the actual derivatives of a continuous
multilinear map show that derivatives above the jet degree vanish. Consequently
the actual highest derivative is constant. No symmetry or compatibility with
derivatives of an underlying function is required of the supplied tensors.
-/

namespace TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An actual derivative above the degree of a diagonal multilinear map vanishes. -/
theorem iteratedFDeriv_diagonal_eq_zero_of_lt {i n : ℕ}
    (A : E [×i]→L[ℝ] F) (hin : i < n) (x : E) :
    iteratedFDeriv ℝ n (fun y : E => A (fun _ => y)) x = 0 := by
  apply norm_eq_zero.mp
  have hh := norm_iteratedFDeriv_diagonal_le (n := n) A x
  simp only [Nat.descFactorial_eq_zero_iff_lt.mpr hin, Nat.cast_zero, zero_mul] at hh
  exact le_antisymm hh (norm_nonneg _)

/-- Every actual derivative above the degree of a finite tensor jet vanishes. -/
theorem iteratedFDeriv_ofJet_eq_zero_of_lt (A : FormalMultilinearSeries ℝ E F)
    {p n : ℕ} (hpn : p < n) (x : E) : iteratedFDeriv ℝ n (ofJet A p) x = 0 := by
  have he : ofJet A p = fun y => ∑ i ∈ Finset.range (p + 1),
      ((i.factorial : ℝ)⁻¹) • A i (fun _ => y) := funext (ofJet_eq_sum A p)
  rw [he, iteratedFDeriv_fun_sum_apply]
  · apply Finset.sum_eq_zero
    intro i hi
    have hd : ContDiff ℝ n (fun y : E => A i (fun _ => y)) :=
      (A i).contDiff.comp (contDiff_pi.mpr fun _ => contDiff_id)
    rw [iteratedFDeriv_const_smul_apply' hd.contDiffAt,
      iteratedFDeriv_diagonal_eq_zero_of_lt (A i) (by have := Finset.mem_range.mp hi; omega),
      smul_zero]
  · intro i hi
    exact ((A i).contDiff.comp (contDiff_pi.mpr fun _ => contDiff_id)).contDiffAt.const_smul _

/-- The actual highest derivative of a finite tensor jet is independent of
its evaluation point, including for nonsymmetric supplied tensors. -/
theorem iteratedFDeriv_ofJet_top_eq (A : FormalMultilinearSeries ℝ E F)
    (p : ℕ) (x y : E) :
    iteratedFDeriv ℝ p (ofJet A p) x = iteratedFDeriv ℝ p (ofJet A p) y := by
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ p (ofJet A p)) :=
    (contDiff_ofJet A p (p + 1)).differentiable_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self p)
  have hzero : ∀ z, fderiv ℝ (iteratedFDeriv ℝ p (ofJet A p)) z = 0 := by
    intro z
    have hh : ‖fderiv ℝ (iteratedFDeriv ℝ p (ofJet A p)) z‖ = 0 := by
      rw [norm_fderiv_iteratedFDeriv, iteratedFDeriv_ofJet_eq_zero_of_lt A (Nat.lt_succ_self p),
        norm_zero]
    exact (ContinuousLinearMap.opNorm_zero_iff _).mp hh
  exact is_const_of_fderiv_eq_zero hdiff hzero x y

end TaylorModel
