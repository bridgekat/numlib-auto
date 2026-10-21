import Numlib.Analysis.Calculus.BoundedLipschitzJets
import Numlib.Optimization.TargetLeastSquares
import Numlib.Optimization.ResidualPowerObjective
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Componentwise sufficient smoothness for residual objectives

Component jets are bounded and Lipschitz on a convex set, with a smooth open extension.
Polynomial closure gives every even residual-norm power and squared scalar-target residual.
Uniformity in bounded target families follows from the actual affine target identity.
-/

noncomputable section
namespace BoundedLipschitzJets
open Optimization.ConstrainedRegularization
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {p : ℕ} {C : Set E} {M L : ℝ}

/-- A full jet envelope supplies the actual highest-derivative smoothness interface. -/
theorem On.toSmoothOn (hf : On f p C M L) (hp : 1 ≤ p) : SmoothOn f C p L where
  degree_pos := hp
  nonneg := hf.lipschitz_nonneg
  neighborhood := hf.neighborhood
  lipschitz x hx y hy := hf.lipschitz p le_rfl y hy x hx

end BoundedLipschitzJets

namespace Optimization.ComponentSmoothness
open BoundedLipschitzJets ConstrainedRegularization
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type} [Fintype ι] {p : ℕ} {C : Set E}
  {c : E → EuclideanSpace ℝ ι} {M L : ι → ℝ} {R : ℝ}

/-- Bounded residual values complete scalar component jets, and their squared sum has an
actual full jet envelope. Quantitative hypotheses hold on `C` alone. -/
theorem norm_sq_jets (hp : 1 ≤ p) (hC : Convex ℝ C)
    (hc : ∀ i, PositiveOn (fun x => c x i) p C (M i) (L i))
    (hR : ∀ x ∈ C, ‖c x‖ ≤ R) :
    ∃ B A : ℝ, On (fun x => ‖c x‖ ^ 2) p C B A := by
  classical
  have hcomp (i : ι) : On (fun x => c x i) p C (max R (M i)) (max (M i) (L i)) := by
    apply (hc i).with_value_bound hp hC
    intro x hx
    exact (PiLp.norm_apply_le (c x) i).trans (hR x hx)
  choose B A h using fun i => (hcomp i).pow 2
  refine ⟨∑ i, B i, ∑ i, A i, ?_⟩
  simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using
    (On.sum Finset.univ (fun i _ => h i))

/-- Every natural even residual power has a full jet envelope, including at residual zeros.
The exponent can be smaller than the derivative order. -/
theorem residualPower_jets_even (hp : 1 ≤ p) (hC : Convex ℝ C)
    (hc : ∀ i, PositiveOn (fun x => c x i) p C (M i) (L i))
    (hR : ∀ x ∈ C, ‖c x‖ ≤ R) (k : ℕ) :
    ∃ B A : ℝ, On (residualPowerObjective c (2 * (k : ℝ))) p C B A := by
  obtain ⟨B, A, h⟩ := norm_sq_jets hp hC hc hR
  obtain ⟨B', A', hk⟩ := h.pow k
  have hd := hk.const_mul (2 * (k : ℝ))⁻¹
  refine ⟨|(2 * (k : ℝ))⁻¹| * B', |(2 * (k : ℝ))⁻¹| * A', ?_⟩
  convert hd using 1
  funext x
  rw [residualPowerObjective_eq_sq_norm_rpow]
  rw [show (2 * (k : ℝ)) / 2 = (k : ℝ) by ring, Real.rpow_natCast]
  ring

/-- Componentwise bounded Lipschitz jets and a residual bound suffice for highest-derivative
Lipschitz continuity of every even norm-power objective. -/
theorem smoothOn_residualPower_even (hp : 1 ≤ p) (hC : Convex ℝ C)
    (hc : ∀ i, PositiveOn (fun x => c x i) p C (M i) (L i))
    (hR : ∀ x ∈ C, ‖c x‖ ≤ R) (k : ℕ) :
    ∃ A : ℝ, SmoothOn (residualPowerObjective c (2 * (k : ℝ))) C p A := by
  obtain ⟨B, A, h⟩ := residualPower_jets_even hp hC hc hR k
  exact ⟨A, h.toSmoothOn hp⟩

/-- A bound on one fixed objective-target residual, together with actual positive component
jets, gives a full envelope for the actual least-squares target objective. -/
theorem target_jets (hp : 1 ≤ p) (hC : Convex ℝ C)
    (hc : ∀ i, PositiveOn (fun x => c x i) p C (M i) (L i))
    (hR : ∀ x ∈ C, ‖c x‖ ≤ R) {f : E → ℝ} {Mf Lf : ℝ}
    (hf : PositiveOn f p C Mf Lf) (t : ℝ) {Rt : ℝ}
    (ht : ∀ x ∈ C, ‖f x - t‖ ≤ Rt) :
    ∃ B A : ℝ, On (TargetLeastSquares.objective f c t) p C B A := by
  obtain ⟨B, A, hq⟩ := norm_sq_jets hp hC hc hR
  have hft := (hf.sub_const t).with_value_bound hp hC ht
  obtain ⟨B', A', hsq⟩ := hft.pow 2
  have h := (hq.add hsq).const_mul (1 / 2)
  refine ⟨|(1 / 2 : ℝ)| * (B + B'), |(1 / 2 : ℝ)| * (A + A'), ?_⟩
  convert h using 1
  funext x
  unfold TargetLeastSquares.objective
  ring

/-- For a fixed target, component assumptions and the two actual residual value bounds imply
highest-derivative Lipschitz continuity, without any target-objective smoothness assumption. -/
theorem smoothOn_target (hp : 1 ≤ p) (hC : Convex ℝ C)
    (hc : ∀ i, PositiveOn (fun x => c x i) p C (M i) (L i))
    (hR : ∀ x ∈ C, ‖c x‖ ≤ R) {f : E → ℝ} {Mf Lf : ℝ}
    (hf : PositiveOn f p C Mf Lf) (t : ℝ) {Rt : ℝ}
    (ht : ∀ x ∈ C, ‖f x - t‖ ≤ Rt) :
    ∃ A : ℝ, SmoothOn (TargetLeastSquares.objective f c t) C p A := by
  obtain ⟨B, A, h⟩ := target_jets hp hC hc hR hf t ht
  exact ⟨A, h.toSmoothOn hp⟩

/-- A bounded scalar objective yields actual smoothness of the entire target family. -/
theorem smoothOn_all_targets (hp : 1 ≤ p) (hC : Convex ℝ C)
    (hc : ∀ i, PositiveOn (fun x => c x i) p C (M i) (L i))
    (hR : ∀ x ∈ C, ‖c x‖ ≤ R) {f : E → ℝ} {Mf Lf Rf : ℝ}
    (hf : PositiveOn f p C Mf Lf) (hfvalue : ∀ x ∈ C, ‖f x‖ ≤ Rf) :
    ∀ t : ℝ, ∃ A : ℝ, SmoothOn (TargetLeastSquares.objective f c t) C p A := by
  intro t
  apply smoothOn_target hp hC hc hR hf t (Rt := Rf + ‖t‖)
  intro x hx
  exact (norm_sub_le _ _).trans (add_le_add (hfvalue x hx) le_rfl)

/-- Constants at targets zero and one are chosen before every bounded target interval.
Their affine combination controls the whole target family uniformly. -/
theorem smoothOn_targets_uniform (hp : 1 ≤ p) (hC : Convex ℝ C)
    (hc : ∀ i, PositiveOn (fun x => c x i) p C (M i) (L i))
    (hR : ∀ x ∈ C, ‖c x‖ ≤ R) {f : E → ℝ} {Mf Lf Rf : ℝ}
    (hf : PositiveOn f p C Mf Lf) (hfvalue : ∀ x ∈ C, ‖f x‖ ≤ Rf) :
    ∃ A₀ A₁ : ℝ, SmoothOn (TargetLeastSquares.objective f c 0) C p A₀ ∧
      SmoothOn (TargetLeastSquares.objective f c 1) C p A₁ ∧
      ∀ B t : ℝ, |t| ≤ B → SmoothOn (TargetLeastSquares.objective f c t) C p
        ((1 + B) * A₀ + B * A₁) := by
  obtain ⟨A₀, h₀⟩ := smoothOn_all_targets hp hC hc hR hf hfvalue 0
  obtain ⟨A₁, h₁⟩ := smoothOn_all_targets hp hC hc hR hf hfvalue 1
  exact ⟨A₀, A₁, h₀, h₁, fun _ _ ht => TargetLeastSquares.smoothOn_of_abs_target_le h₀ h₁ ht⟩

end Optimization.ComponentSmoothness
