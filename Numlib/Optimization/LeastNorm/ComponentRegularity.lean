import Numlib.Optimization.LeastNorm.Regularity
import Numlib.Optimization.Composite.DerivativeBounds
/-!
# Local derivative bounds from scalar residual components

Coordinate projections commute with the actual derivatives on an open domain.
Euclidean operator norm comparison then gives the square-root dimension factor
for both bounded derivatives and their Lipschitz differences.
-/

namespace LeastNorm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Component bounds give the actual vector derivative bound on an open domain. -/
theorem norm_iteratedFDeriv_le_components_on {m p j : ℕ}
    {c : E → EuclideanSpace ℝ (Fin m)} {S : Set E}
    (hc : ContDiffOn ℝ p c S) (hS : IsOpen S) (hjp : j ≤ p)
    {B : ℝ} (hB : 0 ≤ B)
    (hbc : ∀ i, ∀ x ∈ S, ‖iteratedFDeriv ℝ j (fun z => c z i) x‖ ≤ B)
    {x : E} (hx : x ∈ S) :
    ‖iteratedFDeriv ℝ j c x‖ ≤ Real.sqrt m * B := by
  apply Composite.norm_multilinear_le_sqrt_dim_mul _ hB
  intro i
  have he := (EuclideanSpace.proj (𝕜 := ℝ) i).iteratedFDeriv_comp_left
    (x := x) ((hc.of_le (by exact_mod_cast hjp)).contDiffAt (hS.mem_nhds hx)) le_rfl
  rw [←he]
  exact hbc i x hx

/-- Component derivative differences give the actual vector Lipschitz bound. -/
theorem norm_iteratedFDeriv_sub_le_components_on {m p j : ℕ}
    {c : E → EuclideanSpace ℝ (Fin m)} {S : Set E}
    (hc : ContDiffOn ℝ p c S) (hS : IsOpen S) (hjp : j ≤ p)
    {L : ℝ} (hL : 0 ≤ L)
    (hlc : ∀ i, ∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ j (fun z => c z i) x -
        iteratedFDeriv ℝ j (fun z => c z i) y‖ ≤ L * ‖x - y‖)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖iteratedFDeriv ℝ j c x - iteratedFDeriv ℝ j c y‖ ≤ Real.sqrt m * L * ‖x - y‖ := by
  have hb := Composite.norm_multilinear_le_sqrt_dim_mul
    (iteratedFDeriv ℝ j c x - iteratedFDeriv ℝ j c y)
    (mul_nonneg hL (norm_nonneg (x - y))) (fun i => by
      let P := EuclideanSpace.proj (𝕜 := ℝ) i
      have he : P.compContinuousMultilinearMap
          (iteratedFDeriv ℝ j c x - iteratedFDeriv ℝ j c y) =
          P.compContinuousMultilinearMap (iteratedFDeriv ℝ j c x) -
            P.compContinuousMultilinearMap (iteratedFDeriv ℝ j c y) := by
        ext w
        simp [P]
      have hx' : ContDiffAt ℝ j c x := (hc.of_le (by exact_mod_cast hjp)).contDiffAt
        (hS.mem_nhds hx)
      have hy' : ContDiffAt ℝ j c y := (hc.of_le (by exact_mod_cast hjp)).contDiffAt
        (hS.mem_nhds hy)
      rw [he, ←P.iteratedFDeriv_comp_left hx' le_rfl,
        ←P.iteratedFDeriv_comp_left hy' le_rfl]
      exact hlc i x hx y hy)
  convert hb using 1
  ring
end LeastNorm
