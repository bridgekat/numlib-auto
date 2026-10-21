import NumlibSurface.CartisGouldToint.Chapter12.Section01
import NumlibSurface.CartisGouldToint.Chapter01.Section01
import Numlib.Optimization.TaylorCriticalityCriteria

/-!
# Taylor-gap necessary and approximate optimality conditions

The source's actual Taylor gaps detect first, second, and third derivative conditions, vanish
at low-order local minima, and cascade to the preceding order at controlled radii.
-/

noncomputable section
open scoped Nat
open Set Metric Filter Topology Optimization
open CartisGouldToint.Chapter01.Section03
namespace CartisGouldToint.Chapter12.Section01
variable {n : ℕ}

/-- Theorem 12.1.3: the first Taylor measure is the radius times the gradient norm; a zero
quadratic gap gives the exact first and second conditions; the cubic tensor projected to their
common kernel is controlled by the cubic gap, and vanishes there when its normalized gap tends
to zero. The common diagonal kernel agrees with the bundled projection subspace by positive
semidefiniteness of the Hessian. -/
theorem theorem_12_1_3 (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∀ δ : ℝ, 0 < δ →
      ‖gradient f x‖ = taylorCriticality f 1 δ x / δ ∧
      (taylorCriticality f 1 δ x = 0 ↔ gradient f x = 0)) ∧
    (ContDiff ℝ 2 f → ∀ δ : ℝ, 0 < δ → taylorCriticality f 2 δ x = 0 →
      gradient f x = 0 ∧ ∀ d, 0 ≤ fderiv ℝ (fderiv ℝ f) x d d) ∧
    (ContDiff ℝ 3 f → gradient f x = 0 →
      (∀ d, 0 ≤ fderiv ℝ (fderiv ℝ f) x d d) →
      (∀ d, d ∈ TaylorCriticality.derivativeKernel f x ↔
        fderiv ℝ f x d = 0 ∧ fderiv ℝ (fderiv ℝ f) x d d = 0) ∧
      (∀ δ : ℝ, 0 < δ → (TaylorCriticality.projectedCubic f x).diagonalNorm ≤
        6 * taylorCriticality f 3 δ x / δ ^ 3) ∧
      (Tendsto (fun δ : ℝ => taylorCriticality f 3 δ x / δ ^ 3) (𝓝[>] 0) (𝓝 0) →
        ∀ d, fderiv ℝ (fderiv ℝ f) x d d = 0 →
          fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x d d d = 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro δ hδ
    rw [taylorCriticality_one f hδ.le x]
    constructor
    · field_simp
    · simp only [mul_eq_zero, ne_of_gt hδ, false_or, norm_eq_zero]
  · intro hf δ hδ hgap
    obtain ⟨hg, hH⟩ :=
      (TaylorCriticality.gapOn_taylorDecrement_two_eq_zero_iff hf.contDiffAt hδ).mp hgap
    exact ⟨by simp [gradient, hg], hH⟩
  · intro hf hg hH
    have hf2 : ContDiffAt ℝ 2 f x := (hf.of_le (by norm_num)).contDiffAt
    refine ⟨fun _ => TaylorCriticality.mem_derivativeKernel_iff hf2 hH,
      fun _ hδ => TaylorCriticality.projectedCubic_diagonalNorm_le hδ, ?_⟩
    intro hlim d hd
    have hg0 : fderiv ℝ f x = 0 := by
      simpa only [gradient, EmbeddingLike.map_eq_zero_iff] using hg
    rw [← TaylorCriticality.iteratedFDeriv_three_diagonal]
    apply TaylorCriticality.cubic_eq_zero_of_tendsto_gap_div_cube hlim d
    exact (TaylorCriticality.mem_derivativeKernel_iff hf2 hH).mpr ⟨by simp [hg0], hd⟩

/-- Theorem 12.1.4: at a smooth local minimum the first and second Taylor gaps vanish at every
positive radius, and the order-j gap divided by the radius to order j tends to zero. -/
theorem theorem_12_1_4 {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {j : ℕ} (hj : 1 ≤ j)
    (hf : ContDiff ℝ j f) (hmin : IsLocalMin f x) :
    ((j = 1 ∨ j = 2) → ∀ δ : ℝ, 0 < δ → taylorCriticality f j δ x = 0) ∧
    Tendsto (fun δ : ℝ => taylorCriticality f j δ x / δ ^ j) (𝓝[>] 0) (𝓝 0) := by
  constructor
  · rintro (rfl | rfl) δ hδ
    · rw [taylorCriticality_one f hδ.le x]
      have hg := (CartisGouldToint.Chapter01.Section01.theorem_1_1_1 f x).1 hf hmin
      simp [hg]
    · apply (TaylorCriticality.gapOn_taylorDecrement_two_eq_zero_iff hf.contDiffAt hδ).mpr
      refine ⟨hmin.fderiv_eq_zero, ?_⟩
      exact (CartisGouldToint.Chapter01.Section01.theorem_1_1_1 f x).2.1 hf hmin
  · exact TaylorCriticality.tendsto_gapOn_taylorDecrement_div_pow hj hf.contDiffAt hmin

/-- Theorem 12.1.6: first-order gap control bounds the actual gradient; second-order gap
control bounds every Hessian Rayleigh quotient and the gradient with the explicit constant
κ(H)=(1+‖H‖)/2. The constant is valid for indefinite and zero Hessians as well. -/
theorem theorem_12_1_6 (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∀ δ ε : ℝ, 0 < δ → taylorCriticality f 1 δ x ≤ ε * δ → ‖gradient f x‖ ≤ ε) ∧
    (∀ δ ε : ℝ, 0 < δ → 0 < ε → ε ≤ 1 →
      taylorCriticality f 2 δ x ≤ ε * δ ^ 2 / 2 →
      (∀ d, -ε * ‖d‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x d d) ∧
      (0 < n → -ε ≤ leastCurvature (fderiv ℝ (fderiv ℝ f) x)) ∧
      ‖gradient f x‖ ≤ δ * ((1 + ‖fderiv ℝ (fderiv ℝ f) x‖) / 2) * Real.sqrt ε) := by
  constructor
  · intro δ ε hδ hgap
    rw [taylorCriticality_one f hδ.le x] at hgap
    nlinarith
  · intro δ ε hδ hε hε1 hgap
    refine ⟨TaylorCriticality.quadratic_curvature_lower_bound hδ hgap, ?_,
      (EuclideanSpace.norm_gradient_eq x).trans_le
        (TaylorCriticality.norm_fderiv_le_of_quadratic_gap hδ hε hε1 hgap)⟩
    intro hn
    let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact TaylorCriticality.leastCurvature_lower_bound_of_quadratic_gap hδ hgap

/-- Theorem 12.1.7: a sufficiently small radius transfers the order-j approximate gap test to
order j-1. The multiplicative radius condition includes the zero highest-derivative case. -/
theorem theorem_12_1_7 {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {j q : ℕ} {ε δ : ℕ → ℝ}
    (hj : 2 ≤ j) (_hjq : j ≤ q) (hε : 0 < ε j) (_hε1 : ε j ≤ 1)
    (hδ : 0 < δ j) (hδ1 : δ j ≤ 1) (hεmono : ε j ≤ ε (j - 1))
    (hgap : taylorCriticality f j (δ j) x ≤ ε j * δ j ^ j / (j ! : ℝ))
    (hsmall : 2 * (iteratedFDeriv ℝ j f x).diagonalNorm * δ j ≤ (j : ℝ) * ε j) :
    taylorCriticality f (j - 1) (δ j) x ≤
      ε (j - 1) * δ j ^ (j - 1) / ((j - 1)! : ℝ) := by
  have heq : j - 1 + 1 = j := by omega
  apply TaylorCriticality.gapOn_taylorDecrement_pred_le (f := f) (x := x)
    (p := j - 1) (δ := δ j) (ε := ε j) (η := ε (j - 1))
    (by omega) hδ hδ1 hε.le hεmono
  · convert hsmall using 1 <;> rw [heq]
  · simpa only [heq, taylorCriticality, taylorDecrement] using hgap

end CartisGouldToint.Chapter12.Section01
