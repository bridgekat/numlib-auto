import Numlib.Optimization.CompositeRegularization
import Numlib.Optimization.HigherOrderRegularizationModelBounds
import Numlib.Optimization.TaylorModelTruncation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual composite decrease from generalized Taylor decrements

Taylor truncation errors of the smooth scalar and vector parts combine through the Lipschitz
outer composition. The outer map is retained exactly; no derivative of it is used.
-/

noncomputable section
open scoped Nat NNReal
namespace Optimization
open RegularizedTaylorModel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The omitted coefficients and the top remainder bound control a lower Taylor error. -/
theorem HigherOrderRegularization.DiagonalLipschitz.value_remainder_of_coefficients
    {f : E → ℝ} {p j : ℕ} {σ M δ : ℝ} (hf : DiagonalLipschitz f p σ)
    (hp : 1 ≤ p) (hjp : j ≤ p) (hM : 0 ≤ M) (hσ : σ ≤ M)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (x d : E) (hd : ‖d‖ ≤ δ)
    (hb : ∀ i ∈ Finset.Icc (j + 1) p, ‖iteratedFDeriv ℝ i f x‖ ≤ M) :
    |f (x + d) - taylorModel f j x d| ≤ 2 * M * δ ^ (j + 1) / (j ! : ℝ) := by
  apply norm_sub_taylorModel_le_of_tail hjp hM hδ hd hb
  calc
    _ ≤ σ / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1) := by
      simpa only [Real.norm_eq_abs] using hf.value_remainder hp x d
    _ ≤ M / ((p + 1)! : ℝ) * δ ^ (p + 1) :=
      mul_le_mul (div_le_div_of_nonneg_right hσ (by positivity))
        (pow_le_pow_left₀ (norm_nonneg d) hd _) (pow_nonneg (norm_nonneg d) _)
        (div_nonneg hM (by positivity))
    _ = _ := by ring

/-- A scalar Taylor polynomial has vanishing highest-derivative Lipschitz constant. -/
theorem HigherOrderRegularization.diagonalLipschitz_taylorModel {f : E → ℝ} {p : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) : DiagonalLipschitz (taylorModel f p x) p 0 := by
  apply DiagonalLipschitz.of_operator (contDiff_taylorModel f p x p) le_rfl
  intro s t
  rw [iteratedFDeriv_taylorModel_top hf, iteratedFDeriv_taylorModel_top hf, sub_self]
  simp

/-- Scalar and vector truncation errors transfer a generalized Taylor decrement to actual
composite decrease. The radius test includes vanishing error constants without division. -/
theorem CompositeTaylorModels.half_decrease_of_errors {g : E → ℝ} {v : E → F}
    {h : F → ℝ} {K : ℝ≥0} (hh : LipschitzWith K h) {j : ℕ} {s d : E}
    {A B δ α : ℝ} (hδ : 0 ≤ δ)
    (hg : |g (s + d) - taylorModel g j s d| ≤ 2 * A * δ ^ (j + 1) / (j ! : ℝ))
    (hv : ‖v (s + d) - taylorModel v j s d‖ ≤ 2 * B * δ ^ (j + 1) / (j ! : ℝ))
    (hsmall : 4 * (A + K * B) * δ ≤ α)
    (hdec : α * δ ^ j / (j ! : ℝ) ≤ decrement g v h j s d) :
    α * δ ^ j / (2 * (j ! : ℝ)) ≤ g s + h (v s) - (g (s + d) + h (v (s + d))) := by
  have hLip : |h (v (s + d)) - h (taylorModel v j s d)| ≤
      K * (2 * B * δ ^ (j + 1) / (j ! : ℝ)) := by
    have hl := hh.dist_le_mul (v (s + d)) (taylorModel v j s d)
    rw [Real.dist_eq, dist_eq_norm] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left hv K.coe_nonneg)
  have herror : g (s + d) + h (v (s + d)) - model g v h j s d ≤
      2 * (A + K * B) * δ ^ (j + 1) / (j ! : ℝ) := by
    have hg' := (abs_le.mp hg).2
    have hh' := (abs_le.mp hLip).2
    calc
      _ = (g (s + d) - taylorModel g j s d) +
          (h (v (s + d)) - h (taylorModel v j s d)) := by dsimp [model]; ring
      _ ≤ _ := add_le_add hg' hh'
      _ = _ := by ring
  have hscale := mul_le_mul_of_nonneg_right hsmall
    (div_nonneg (pow_nonneg hδ j) (Nat.cast_nonneg j.factorial))
  rw [decrement_eq] at hdec
  rw [pow_succ] at herror
  ring_nf at herror hscale hdec ⊢
  linarith only [herror, hscale, hdec]

/-- The scalar part of a regularized composite model is the canonical smooth radial model. -/
theorem CompositeRegularization.smoothModel_eq_regularization (f : E → ℝ)
    (p : ℕ) (x s : E) (σ : ℝ) :
    CompositeRegularization.smoothModel f p x σ s =
      HigherOrderRegularization.model f p x σ s := by
  dsimp [CompositeRegularization.smoothModel, HigherOrderRegularization.model]
  ring

/-- Euclidean component projections commute with the actual vector Taylor polynomial. -/
theorem RegularizedTaylorModel.taylorModel_euclidean_component {m : ℕ}
    {c : E → EuclideanSpace ℝ (Fin m)}
    {j : ℕ} {x : E} (hc : ContDiffAt ℝ j c x)
    (s : E) (i : Fin m) :
    Optimization.RegularizedTaylorModel.taylorModel c j x s i =
      Optimization.RegularizedTaylorModel.taylorModel (fun y ↦ c y i) j x s := by
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin m ↦ ℝ) i
  change L (Optimization.RegularizedTaylorModel.taylorModel c j x s) =
    Optimization.RegularizedTaylorModel.taylorModel (L ∘ c) j x s
  simp only [Optimization.RegularizedTaylorModel.taylorModel, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [L.iteratedFDeriv_comp_left hc (by
    exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
  rfl

/-- A Euclidean norm is bounded by the common component bound times the square root
of the number of components. -/
theorem euclidean_norm_le_sqrt_mul {m : ℕ} {z : EuclideanSpace ℝ (Fin m)} {B : ℝ}
    (hB : 0 ≤ B) (hz : ∀ i : Fin m, |z i| ≤ B) : ‖z‖ ≤ Real.sqrt m * B := by
  rw [EuclideanSpace.norm_eq]
  calc
    _ ≤ Real.sqrt (∑ _ : Fin m, B ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg (z i)) (hz i) 2
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq hB]


open CompositeRegularization

/-- Actual lower-order errors of a Euclidean vector Taylor model have the common
component derivative factor and the exact factorial tail. -/
theorem CompositeRegularization.vectorModel_error {n m p j : ℕ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {L : ℕ → ℝ}
    (hc : ∀ i : Fin m, HigherOrderDerivativeFamily (fun y => c y i) p L)
    (hL : ∀ k, 1 ≤ k → k ≤ p → 0 ≤ L k)
    (hp : 1 ≤ p) (hj : 1 ≤ j) (hjp : j ≤ p) (x s d : EuclideanSpace ℝ (Fin n))
    (hs : ‖s‖ ≤ 1) {δ : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (hd : ‖d‖ ≤ δ)
    (hcsm : ContDiffAt ℝ p c x) :
    ‖vectorModel c p x (s + d) - taylorModel (vectorModel c p x) j s d‖ ≤
      2 * (3 * Real.sqrt m * HigherOrderDerivativeFamily.maxConstant p L) *
        δ ^ (j + 1) / (j ! : ℝ) := by
  let B := HigherOrderDerivativeFamily.maxConstant p L
  have hB : 0 ≤ B := (hL 1 le_rfl hp).trans
    (HigherOrderDerivativeFamily.le_maxConstant L le_rfl hp)
  have hbound : ∀ i : Fin m,
      |(vectorModel c p x (s + d) - taylorModel (vectorModel c p x) j s d) i| ≤
        2 * (3 * B) * δ ^ (j + 1) / (j ! : ℝ) := by
    intro i
    have hi := (HigherOrderRegularization.diagonalLipschitz_taylorModel
      (hc i).smooth.contDiffAt).value_remainder_of_coefficients hp hjp
      (by positivity : 0 ≤ 3 * B) (by positivity : (0 : ℝ) ≤ 3 * B)
      hδ s d hd (fun k hk => (hc i).norm_iteratedFDeriv_taylorModel_le
        (by have := (Finset.mem_Icc.mp hk).1; omega) (Finset.mem_Icc.mp hk).2 x s hs)
    have hvc : ContDiffAt ℝ j (vectorModel c p x) s :=
      (contDiff_taylorModel c p x j).contDiffAt
    simpa only [PiLp.sub_apply, taylorModel_euclidean_component hvc,
      taylorModel_euclidean_component hcsm, vectorModel] using hi
  have he := euclidean_norm_le_sqrt_mul (z := vectorModel c p x (s + d) -
    taylorModel (vectorModel c p x) j s d) (by have := hδ.1; positivity :
      0 ≤ 2 * (3 * B) * δ ^ (j + 1) / (j ! : ℝ)) hbound
  exact he.trans_eq (by dsimp [B]; ring)

/-- Actual lower-order Taylor errors of the smooth regularized component have the
common derivative constant plus its radial regularization parameter. -/
theorem CompositeRegularization.smoothModel_error {G : Type} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] {f : G → ℝ} {L : ℕ → ℝ}
    {p j : ℕ} (hf : HigherOrderDerivativeFamily f p L)
    (hp : 1 ≤ p) (_hj : 1 ≤ j) (hjp : j ≤ p) (x s d : G)
    (hs : ‖s‖ ≤ 1) {σ δ : ℝ} (hσ : 0 ≤ σ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (hd : ‖d‖ ≤ δ) :
    |smoothModel f p x σ (s + d) - taylorModel (smoothModel f p x σ) j s d| ≤
      2 * (3 * HigherOrderDerivativeFamily.maxConstant p L + σ) *
        δ ^ (j + 1) / (j ! : ℝ) := by
  have hL := hf.maxConstant_nonneg
  have hm := HigherOrderRegularization.diagonalLipschitz_model (x := x) hf.smooth.contDiffAt hσ
  have he := hm.value_remainder_of_coefficients hp hjp (by positivity :
      0 ≤ 3 * HigherOrderDerivativeFamily.maxConstant p L + σ)
    (by linarith : σ ≤ 3 * HigherOrderDerivativeFamily.maxConstant p L + σ)
    hδ s d hd (fun k hk => hf.norm_iteratedFDeriv_model_le
      (by have := (Finset.mem_Icc.mp hk).1; omega) (Finset.mem_Icc.mp hk).2 x s hσ hs)
  have heq : smoothModel f p x σ = HigherOrderRegularization.model f p x σ := by
    funext t
    exact smoothModel_eq_regularization f p x t σ
  simpa only [heq] using he

end Optimization
