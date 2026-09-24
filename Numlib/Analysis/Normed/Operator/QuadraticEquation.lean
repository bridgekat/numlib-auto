import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Linear-plus-quadratic equations in a Banach space

Stewart's lemma on the equation `L x + φ x = g`, where `L` is an invertible bounded operator and `φ`
is a "quadratic" perturbation: `φ 0 = 0` and `φ` is Lipschitz on each ball with a constant
proportional to the radius, `‖φ x - φ y‖ ≤ η (‖x‖ + ‖y‖) ‖x - y‖`. If `‖L⁻¹‖ ≤ 1/δ` and
`4 ‖g‖ η < δ²`, the equation has a solution of norm at most `2 ‖g‖ / δ`
(`ContinuousLinearEquiv.exists_apply_add_eq_of_quadratic`).

This is the fixed-point engine of the perturbation theory of invariant and singular subspaces: in
[golub2013matrix] Theorem 7.2.4 (and its singular-subspace analogue Theorem 8.6.5) the unknown is
the matrix `P` describing the perturbed subspace as a graph, `L` is a Sylvester operator whose
inverse is bounded by `1 / sep`, and `φ P = P E₁₂ P` is quadratic. The statement and the proof
follow G. W. Stewart, *Error and perturbation bounds for subspaces associated with certain
eigenvalue problems*, SIAM Rev. 15 (1973), Theorem 3.1: the map `x ↦ L⁻¹ (g - φ x)` sends the
closed ball of radius `2 ‖g‖ / δ` into itself and contracts there with constant `4 ‖g‖ η / δ² < 1`,
so the Banach fixed point theorem (`ContractingWith.exists_fixedPoint'`) applies on that complete
ball.

Upstreaming candidate; natural home `Mathlib.Analysis.Normed.Operator` or
`Mathlib.Topology.MetricSpace.Contracting`.
-/

open Metric Set

namespace ContinuousLinearEquiv

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F]

/-- **Stewart's quadratic-equation lemma** ([golub2013matrix] Theorem 7.2.4, the lemma behind it;
Stewart 1973, Theorem 3.1). In a Banach space, let `L` be an invertible bounded operator with
`‖L⁻¹‖ ≤ 1 / δ`, let `‖g‖ ≤ γ`, and let `φ` vanish at `0` and satisfy
`‖φ x - φ y‖ ≤ η (‖x‖ + ‖y‖) ‖x - y‖`. If `4 γ η < δ²`, then `L x + φ x = g` has a solution with
`‖x‖ ≤ 2 γ / δ`. -/
theorem exists_apply_add_eq_of_quadratic (L : F ≃L[𝕜] F) {δ γ η : ℝ} (hδ : 0 < δ)
    (hL : ‖(L.symm : F →L[𝕜] F)‖ ≤ 1 / δ) {g : F} (hg : ‖g‖ ≤ γ) {φ : F → F} (hφ0 : φ 0 = 0)
    (hφ : ∀ x y, ‖φ x - φ y‖ ≤ η * (‖x‖ + ‖y‖) * ‖x - y‖) (h : 4 * γ * η < δ ^ 2) :
    ∃ x, L x + φ x = g ∧ ‖x‖ ≤ 2 * γ / δ := by
  -- Work with `η₊ = max η 0`, for which the Lipschitz hypothesis still holds.
  set η' := max η 0 with hη'
  have hη'0 : 0 ≤ η' := le_max_right _ _
  have hφ' : ∀ x y, ‖φ x - φ y‖ ≤ η' * (‖x‖ + ‖y‖) * ‖x - y‖ := fun x y =>
    (hφ x y).trans (by gcongr; exact le_max_left _ _)
  have hγ : 0 ≤ γ := (norm_nonneg g).trans hg
  have h' : 4 * γ * η' < δ ^ 2 := by
    rcases le_total η 0 with hη | hη
    · rw [hη', max_eq_right hη, mul_zero]; positivity
    · rwa [hη', max_eq_left hη]
  set ρ := 2 * γ / δ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  -- The contraction constant `κ = 4 γ η₊ / δ² < 1`.
  set κ := 4 * γ * η' / δ ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ < 1 := by rw [hκ, div_lt_one (by positivity)]; exact h'
  have hηρ : η' * ρ ^ 2 ≤ γ := by
    have : η' * ρ ^ 2 = γ * κ := by rw [hρ, hκ]; field_simp; ring
    rw [this]; exact mul_le_of_le_one_right hγ hκ1.le
  set T : F → F := fun x => L.symm (g - φ x) with hT
  have hLs : ∀ v, ‖L.symm v‖ ≤ ‖v‖ / δ := fun v => by
    calc ‖L.symm v‖ = ‖(L.symm : F →L[𝕜] F) v‖ := rfl
      _ ≤ ‖(L.symm : F →L[𝕜] F)‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 / δ * ‖v‖ := by gcongr
      _ = ‖v‖ / δ := by ring
  have hmaps : MapsTo T (closedBall 0 ρ) (closedBall 0 ρ) := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    have hφx : ‖φ x‖ ≤ η' * ρ ^ 2 := by
      have := hφ' x 0
      rw [hφ0, sub_zero, norm_zero, add_zero, sub_zero] at this
      calc ‖φ x‖ ≤ η' * ‖x‖ * ‖x‖ := this
        _ ≤ η' * ρ * ρ := by gcongr
        _ = η' * ρ ^ 2 := by ring
    calc ‖T x‖ ≤ ‖g - φ x‖ / δ := hLs _
      _ ≤ (γ + γ) / δ := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add hg (hφx.trans hηρ))
      _ = ρ := by rw [hρ]; ring
  have hcontr : ∀ x ∈ closedBall (0 : F) ρ, ∀ y ∈ closedBall (0 : F) ρ,
      dist (T x) (T y) ≤ κ * dist x y := by
    intro x hx y hy
    rw [mem_closedBall_zero_iff] at hx hy
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : T x - T y = L.symm (φ y - φ x) := by
      simp only [hT, ← map_sub]; congr 1; abel
    rw [hsub]
    calc ‖L.symm (φ y - φ x)‖ ≤ ‖φ y - φ x‖ / δ := hLs _
      _ ≤ η' * (‖y‖ + ‖x‖) * ‖y - x‖ / δ := by gcongr; exact hφ' y x
      _ ≤ η' * (ρ + ρ) * ‖x - y‖ / δ := by rw [norm_sub_rev]; gcongr
      _ = κ * ‖x - y‖ := by rw [hκ, hρ]; field_simp; ring
  have hC : ContractingWith ⟨κ, hκ0⟩ (hmaps.restrict T _ _) := by
    refine ⟨show (⟨κ, hκ0⟩ : NNReal) < 1 from hκ1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    exact hcontr x.1 x.2 y.1 y.2
  obtain ⟨x, hx, hfix, -⟩ := hC.exists_fixedPoint' isClosed_closedBall.isComplete hmaps
    (x := 0) (mem_closedBall_self hρ0) (edist_ne_top _ _)
  refine ⟨x, ?_, mem_closedBall_zero_iff.1 hx⟩
  have hx' : L.symm (g - φ x) = x := hfix
  calc L x + φ x = L (L.symm (g - φ x)) + φ x := by rw [hx']
    _ = g := by rw [L.apply_symm_apply]; abel

end ContinuousLinearEquiv
