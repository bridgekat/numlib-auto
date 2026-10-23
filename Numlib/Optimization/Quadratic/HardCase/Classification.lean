import Numlib.Optimization.Quadratic.HardCase.Solutions

/-!
# Complete easy- and hard-case quadratic minimizer classifications

Actual global optimality gives a compatible generalized-inverse particular
solution and a correction in the entire shifted kernel. The minimum-value
identities include zero regularization minimizers and singular interior
trust-region minimizers. Repeated least eigenvalues are retained.
-/

namespace QuadraticSecular.PencilBasis
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {H M : E →L[ℝ] E} (B : PencilBasis (ι := ι) H M)

/-- Every actual global minimizer of a weighted regularized quadratic has its precise norm-power
  multiplier, a compatible metric generalized-inverse particular vector, and a full-kernel
  correction. Include the exact radius and minimum-value formula, the entire least eigenspace at a
  singular shift, and unique equality to the particular solution for every strictly larger shift.
-/
theorem regularization_classification (hH : H.toLinearMap.IsSymmetric)
    (hM : M.toLinearMap.IsSymmetricCoercive) (g s : E) {r σ : ℝ}
    (hr : 2 < r) (hσ : 0 < σ)
    (hmin : ∀ t : E, (QuadraticOptimality.model H g s + σ / r * energyNorm M.toLinearMap s ^ r)
      ≤
      (QuadraticOptimality.model H g t + σ / r * energyNorm M.toLinearMap t ^ r)) :
    let τ := σ * energyNorm M.toLinearMap s ^ (r - 2)
    0 ≤ τ ∧ -B.leftmost ≤ τ ∧ (H + τ • M) (B.particular g τ) = -g ∧
      (∃ v : E, (H + τ • M) v = 0 ∧ s = B.particular g τ + v ∧
        (τ = -B.leftmost → H v = B.leftmost • M v)) ∧
      energyNorm M.toLinearMap s = (τ / σ) ^ (1 / (r - 2)) ∧
      (QuadraticOptimality.model H g s + σ / r * energyNorm M.toLinearMap s ^ r) = 
        (inner ℝ g (B.particular g τ) - (r - 2) / r * τ * (τ / σ) ^ (2 / (r - 2))) / 2 ∧
      (-B.leftmost < τ → s = B.particular g τ ∧
        ∀ t : E, (QuadraticOptimality.model H g t + σ / r * energyNorm M.toLinearMap t ^ r) ≤
          (QuadraticOptimality.model H g s + σ / r * energyNorm M.toLinearMap s ^ r) → t = s)
            := by
  let τ := σ * energyNorm M.toLinearMap s ^ (r - 2)
  have hm : ∀ t : E,
      inner ℝ g s + inner ℝ (H s) s / 2 + σ / r * energyNorm M.toLinearMap s ^ r ≤
      inner ℝ g t + inner ℝ (H t) t / 2 + σ / r * energyNorm M.toLinearMap t ^ r := by
    intro t
    simpa only [QuadraticOptimality.model_eq] using hmin t
  have hc := (QuadraticOptimality.Metric.regularized_iff M hM hH g s hr hσ.le).mp hm
  have hsolve : (H + τ • M) s = -g := hc.1
  have hPSD : ∀ v, 0 ≤ inner ℝ ((H + τ • M) v) v := hc.2
  obtain ⟨v, hv, hs⟩ := B.kernel_decomposition g s τ hsolve
  refine ⟨mul_nonneg hσ.le (Real.rpow_nonneg (energyNorm_nonneg _ _) _),
    B.shift_ge_neg_leftmost τ hPSD, B.particular_solves g s τ hsolve,
    ⟨v, hv, hs, fun ht => B.kernel_eigenvector ht hv⟩,
    radius_of_multiplier M s hr hσ rfl, B.regularization_value hH hM g s hr hσ hsolve rfl, ?_⟩
  intro ht
  have hpos := B.denom_pos_of_gt_neg_leftmost ht
  refine ⟨B.particular_eq_of_positive g s τ hsolve hpos, ?_⟩
  intro t htval
  apply QuadraticOptimality.Metric.unique_regularized M hM hH g s hr hσ.le hsolve
    (B.shifted_positive τ hpos) t
  simpa only [QuadraticOptimality.model_eq] using htval

/-- Every feasible actual global trust-region minimizer admits a nonnegative shift at least minus
  the least eigenvalue, a compatible metric generalized-inverse particular vector, and a
  full-kernel correction. Include complementarity, the exact minimum-value formula, boundary
  equality for positive shifts, arbitrary feasible kernel corrections at zero shift, and unique
  equality to the particular solution for strictly larger shifts. -/
theorem trust_region_classification (hH : H.toLinearMap.IsSymmetric)
    (hM : M.toLinearMap.IsSymmetricCoercive) (g s : E) {Δ : ℝ} (hΔ : 0 < Δ)
    (hs : energyNorm M.toLinearMap s ≤ Δ)
    (hmin : ∀ t : E, energyNorm M.toLinearMap t ≤ Δ →
      QuadraticOptimality.model H g s ≤ QuadraticOptimality.model H g t) :
    ∃ τ : ℝ, 0 ≤ τ ∧ -B.leftmost ≤ τ ∧ (H + τ • M) (B.particular g τ) = -g ∧
      (∃ v : E, (H + τ • M) v = 0 ∧ s = B.particular g τ + v ∧
        (τ = -B.leftmost → H v = B.leftmost • M v)) ∧
      τ * (energyNorm M.toLinearMap s ^ 2 - Δ ^ 2) = 0 ∧
      (0 < τ → energyNorm M.toLinearMap s = Δ) ∧
      QuadraticOptimality.model H g s = (inner ℝ g (B.particular g τ) - τ * Δ ^ 2) / 2 ∧
      (-B.leftmost < τ → s = B.particular g τ ∧
        ∀ t : E, energyNorm M.toLinearMap t ≤ Δ →
          QuadraticOptimality.model H g t ≤ QuadraticOptimality.model H g s → t = s) := by
  have hm : ∀ t : E, energyNorm M.toLinearMap t ≤ Δ →
      inner ℝ g s + inner ℝ (H s) s / 2 ≤ inner ℝ g t + inner ℝ (H t) t / 2 := by
    simpa only [QuadraticOptimality.model_eq] using hmin
  obtain ⟨τ, hτ, hsolve, hPSD, hcomp⟩ :=
    (QuadraticOptimality.Metric.trust_region_iff M hM hH g s hΔ hs).mp hm
  obtain ⟨v, hv, hsv⟩ := B.kernel_decomposition g s τ hsolve
  refine ⟨τ, hτ, B.shift_ge_neg_leftmost τ hPSD, B.particular_solves g s τ hsolve,
    ⟨v, hv, hsv, fun ht => B.kernel_eigenvector ht hv⟩, hcomp, ?_,
    B.trust_region_value hH hM g s hsolve hcomp, ?_⟩
  · intro ht
    have he : energyNorm M.toLinearMap s ^ 2 = Δ ^ 2 := by nlinarith
    exact (sq_eq_sq₀ (energyNorm_nonneg _ _) hΔ.le).mp he
  · intro ht
    have hpos := B.denom_pos_of_gt_neg_leftmost ht
    refine ⟨B.particular_eq_of_positive g s τ hsolve hpos, ?_⟩
    intro t htfeas htval
    apply QuadraticOptimality.Metric.unique_trust_region M hM hH g s hτ hsolve
      (B.shifted_positive τ hpos) hcomp t htfeas
    simpa only [QuadraticOptimality.model_eq] using htval

end QuadraticSecular.PencilBasis
