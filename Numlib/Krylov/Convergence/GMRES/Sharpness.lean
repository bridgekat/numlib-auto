/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.FiniteMinimaxWeights
import Numlib.Eigen.KrylovEigen
import Numlib.Krylov.Iterate

/-!
# Sharpness of the spectral GMRES bound for normal operators

Weighted squared polynomial values are residual norms for a suitable
choice of initial residual in the orthonormal eigenbasis. The minimax
weights furnish an initial residual attaining the spectral bound.
-/

open Finset Polynomial

namespace Krylov

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [Fintype ι] [Nonempty ι]

/-- For an invertible operator with a nonempty finite orthonormal eigenbasis
and any fixed step $n$, there is an initial approximation for which GMRES
attains the spectral minimax bound. -/
theorem exists_norm_residual_eq_spectralMinimax {A : E →ₗ[𝕜] E}
    (basis : OrthonormalBasis ι 𝕜 E) (μ : ι → 𝕜)
    (hμ : ∀ i, A (basis i) = μ i • basis i) (hA : Function.Surjective A)
    (b : E) (n : ℕ) :
    ∃ x₀ xₙ : E, b - A x₀ ≠ 0 ∧ IsMinResidualIterate A b x₀ n xₙ ∧
      ‖b - A xₙ‖ / ‖b - A x₀‖ =
        ⨅ p : {p : 𝕜[X] // p.degree ≤ n ∧ p.eval 0 = 1}, ⨆ i, ‖p.1.eval (μ i)‖ := by
  obtain ⟨w, hw, hsum, hweights⟩ := Polynomial.exists_probability_weights_eval_minimax_sq_le μ n
  let r := basis.repr.symm (WithLp.toLp 2 fun i => (Real.sqrt (w i) : 𝕜))
  have hcoord (i : ι) : ‖basis.repr r i‖ ^ 2 = w i := by
    dsimp only [r]
    rw [LinearIsometryEquiv.apply_symm_apply]
    change ‖(Real.sqrt (w i) : 𝕜)‖ ^ 2 = w i
    rw [RCLike.norm_ofReal, sq_abs, Real.sq_sqrt (hw i)]
  have hnorm_sq : ‖r‖ ^ 2 = 1 := by
    rw [← basis.repr.norm_map r, EuclideanSpace.norm_sq_eq]
    simpa only [hcoord] using hsum
  have hnorm : ‖r‖ = 1 :=
    (sq_eq_sq₀ (norm_nonneg r) zero_le_one).1 (by simpa using hnorm_sq)
  have hsq (p : 𝕜[X]) : ‖aeval A p r‖ ^ 2 = ∑ i, w i * ‖p.eval (μ i)‖ ^ 2 := by
    rw [← basis.repr.norm_map (aeval A p r), EuclideanSpace.norm_sq_eq]
    refine sum_congr rfl fun i _ => ?_
    rw [basis.repr_aeval_apply_of_apply_eq_smul hμ, norm_mul, mul_pow, hcoord, mul_comm]
  obtain ⟨x₀, hx₀⟩ := hA (b - r)
  have hr : b - A x₀ = r := by rw [hx₀, sub_sub_cancel]
  obtain ⟨xₙ, hxₙ⟩ := exists_isMinResidualIterate A b x₀ n
  refine ⟨x₀, xₙ, ?_, hxₙ, ?_⟩
  · rw [hr, ← norm_ne_zero_iff, hnorm]
    exact one_ne_zero
  rw [hr, hnorm, div_one]
  let P := {p : 𝕜[X] // p.degree ≤ n ∧ p.eval 0 = 1}
  have : Nonempty P := ⟨⟨1, by simp, by simp⟩⟩
  have hc (p : P) (i : ι) : ‖p.1.eval (μ i)‖ ≤ ⨆ j, ‖p.1.eval (μ j)‖ :=
    le_ciSup (f := fun j => ‖p.1.eval (μ j)‖) (Finite.bddAbove_range _) i
  have hnonneg (p : P) : 0 ≤ ⨆ j, ‖p.1.eval (μ j)‖ :=
    (norm_nonneg _).trans (hc p (Classical.choice ‹Nonempty ι›))
  apply le_antisymm
  · refine le_ciInf fun p : P => ?_
    calc
      ‖b - A xₙ‖ ≤ ‖aeval A p.1 r‖ :=
        hr ▸ hxₙ.norm_residual_le_norm_aeval p.1 p.2.1 p.2.2
      _ ≤ (⨆ i, ‖p.1.eval (μ i)‖) * ‖r‖ :=
        basis.norm_aeval_apply_le_of_forall_repr hμ p.1 (hnonneg p) (fun i _ => hc p i)
      _ = ⨆ i, ‖p.1.eval (μ i)‖ := by rw [hnorm, mul_one]
  · obtain ⟨p, hp, hp0, hey⟩ := exists_residual_poly hxₙ.mem
    have hmin : 0 ≤ (⨅ q : P, ⨆ i, ‖q.1.eval (μ i)‖) := le_ciInf hnonneg
    apply (sq_le_sq₀ hmin (norm_nonneg _)).1
    rw [hey, hr, hsq]
    exact hweights p hp hp0

end Krylov
