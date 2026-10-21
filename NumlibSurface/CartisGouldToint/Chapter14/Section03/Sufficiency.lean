import Numlib.Optimization.LagrangianLipschitzScale
import Numlib.Optimization.LagrangianTaylorRemainder
import NumlibSurface.CartisGouldToint.Chapter14.Section03

/-!
# Chapter 14, Section 3: Lagrangian sufficiency with actual derivative regularity

The test uses the genuine finite Euclidean norm of `(1,y)`, an arbitrary subset of feasible
perturbations, and actual objective/constraint smoothness and highest-jet Lipschitz bounds.
The tested neighborhood is a ball of radius `δ`, as in (14.3.9–11); the OCR prose's diameter
wording is interpreted consistently with those formulas. In the signed alternative, the
OCR's `s` is the same tested displacement `d`. When both Lipschitz constants vanish, the
extra radius restriction disappears, as required by footnote111. No compactness of `V` is
imposed: continuous Taylor polynomials are bounded on the full tested compact ball.
-/

open Set Metric Optimization
open scoped InnerProductSpace Nat NNReal
noncomputable section
namespace CartisGouldToint.Chapter14.Section03
variable {n m : ℕ}
/-- The actual finite Euclidean augmented multiplier vector `(1,y)`. -/
def augmentedMultiplier (y : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.cons 1 (fun i => y i))
/-- The leading augmented coordinate is the scalar one. -/
@[simp] theorem augmentedMultiplier_apply_zero (y : EuclideanSpace ℝ (Fin m)) :
    augmentedMultiplier y 0 = 1 := rfl

/-- Every remaining augmented coordinate is its actual multiplier coordinate. -/
@[simp] theorem augmentedMultiplier_apply_succ (y : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    augmentedMultiplier y i.succ = y i := rfl

/-- The augmented multiplier has its actual Euclidean norm, rather than a product maximum norm. -/
theorem norm_augmentedMultiplier (y : EuclideanSpace ℝ (Fin m)) :
    ‖augmentedMultiplier y‖ = Real.sqrt (1 + ‖y‖ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (augmentedMultiplier y))]
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp only [augmentedMultiplier, Fin.cons_zero, one_pow, Fin.cons_succ]
  rw [EuclideanSpace.real_norm_sq_eq]

/-- Theorem 14.3.2: the actual Lagrangian gap controls nearly feasible objective values,
including both signed zero-penalty alternatives. Constants may vanish; the explicit first
radius branch then removes division by zero. The source closed-set and feasibility
hypotheses are retained, although Taylor boundedness itself needs only the tested ball. -/
theorem theorem_14_3_2 {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {X U V : Set (EuclideanSpace ℝ (Fin n))} {x d : EuclideanSpace ℝ (Fin n)}
    {j : ℕ} {ε₀ ε δ η : ℝ} (y : EuclideanSpace ℝ (Fin m))
    (_hX : IsClosed X) (_hx : x ∈ X) (_hV : V ⊆ Section02.feasibleDisplacements X x)
    (hj : j ∈ Finset.Icc 1 3) (hε : 0 < ε) (hδ : 0 < δ) (_hη : 0 ≤ η)
    (hU : IsOpen U) (hball : closedBall x δ ⊆ U)
    (hf : ContDiffOn ℝ j f U) (hc : ContDiffOn ℝ j c U) (Lf Lc : ℝ≥0)
    (hLf : LipschitzOnWith Lf (iteratedFDeriv ℝ j f) U)
    (hLc : LipschitzOnWith Lc (iteratedFDeriv ℝ j c) U)
    (hcx : ‖c x‖ ≤ ε₀)
    (hgap : lagrangianTaylorGap f c y V j x δ ≤
      ε * ‖augmentedMultiplier y‖ * δ ^ j / (j ! : ℝ) + η)
    (hd : d ∈ V) (hcd : ‖c (x + d)‖ ≤ ε₀) (hdδ : ‖d‖ ≤ δ)
    (hsmall : max (Lf : ℝ) (Lc : ℝ) = 0 ∨
      ‖d‖ ≤ ((j + 1 : ℕ) : ℝ) * ε / (Real.sqrt 2 * max (Lf : ℝ) (Lc : ℝ))) :
    f x - 2 * ε₀ * ‖y‖ - 2 * ε * ‖augmentedMultiplier y‖ * δ ^ j / (j ! : ℝ) - η ≤
      f (x + d) ∧
      ((c (x + d) = 0 ∧ inner ℝ y (c x) ≤ 0) ∨ c (x + d) = c x →
        f x - 2 * ε * ‖augmentedMultiplier y‖ * δ ^ j / (j ! : ℝ) - η ≤ f (x + d)) := by
  have hb := ConstrainedTaylorCriticality.weighted_constant_mul_le_scale
    Lf.coe_nonneg Lc.coe_nonneg (norm_nonneg y) (norm_nonneg d)
    (by positivity : 0 ≤ ((j + 1 : ℕ) : ℝ) * ε) hsmall
  have hs : ((Lf : ℝ) + ‖y‖ * Lc) * ‖d‖ ≤
      ((j + 1 : ℕ) : ℝ) * (ε * ‖augmentedMultiplier y‖) := by
    simpa only [norm_augmentedMultiplier, mul_assoc] using hb
  have h := ConstrainedTaylorCriticality.lagrangian_value_stability_signed_on_ball
    (Finset.mem_Icc.mp hj).1 (mul_nonneg hε.le (norm_nonneg _)) hδ.le y hU hball
    hf hc Lf Lc hLf hLc ⟨hd, by simpa using hdδ⟩ hgap hs
  have hsign : f x + inner ℝ y (c (x + d) - c x) -
      2 * ε * ‖augmentedMultiplier y‖ * δ ^ j / (j ! : ℝ) - η ≤ f (x + d) := by
    convert h using 1
    ring
  constructor
  · have hres : ‖c (x + d) - c x‖ ≤ 2 * ε₀ := by
      have hh := norm_sub_le (c (x + d)) (c x)
      linarith
    have hm := mul_le_mul_of_nonneg_left hres (norm_nonneg y)
    have hi := (abs_le.mp (abs_real_inner_le_norm y (c (x + d) - c x))).1
    nlinarith only [hsign, hm, hi]
  · rintro (⟨hzero, hnonpos⟩ | hsame)
    · have hi : 0 ≤ inner ℝ y (c (x + d) - c x) := by
        simp only [hzero, zero_sub, inner_neg_right]
        linarith
      linarith
    · simpa only [hsame, sub_self, inner_zero_right, add_zero] using hsign

end CartisGouldToint.Chapter14.Section03
