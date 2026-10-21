import Numlib.Optimization.TaylorModelLinear
import Numlib.Optimization.ConstrainedTaylorCriticality
import Numlib.Optimization.TaylorModelRemainder

/-!
# Actual Lagrangian Taylor remainders

Linear Taylor identities transfer genuine scalar and vector Taylor remainders to the signed
fixed-multiplier Lagrangian. The estimates use the original objective and constraint jets.
-/

noncomputable section
open Set
open scoped InnerProductSpace Nat NNReal
namespace Optimization.ConstrainedTaylorCriticality
open RegularizedTaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The actual Lagrangian Taylor model is the objective model minus the paired constraint model. -/
theorem taylorModel_residualLagrangian {f : E → ℝ} {c : E → F} {x : E} {p : ℕ}
    (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x) (y : F) (d : E) :
    taylorModel (residualLagrangian f c y) p x d =
      taylorModel f p x d - ⟪y, taylorModel c p x d⟫_ℝ := by
  change taylorModel (f - ((innerSL ℝ y) ∘ c)) p x d = _
  rw [taylorModel_sub hf ((innerSL ℝ y).contDiff.contDiffAt.comp x hc),
    taylorModel_comp_continuousLinearMap hc]
  rfl

/-- Genuine component remainders bound the actual signed Lagrangian remainder. -/
theorem abs_residualLagrangian_sub_taylorModel_le {f : E → ℝ} {c : E → F}
    {x : E} {p : ℕ} (hf : ContDiffAt ℝ p f x) (hc : ContDiffAt ℝ p c x)
    (y : F) (d : E) :
    |residualLagrangian f c y (x + d) - taylorModel (residualLagrangian f c y) p x d| ≤
      |f (x + d) - taylorModel f p x d| + ‖y‖ * ‖c (x + d) - taylorModel c p x d‖ := by
  rw [taylorModel_residualLagrangian hf hc]
  have he : residualLagrangian f c y (x + d) -
      (taylorModel f p x d - ⟪y, taylorModel c p x d⟫_ℝ) =
      (f (x + d) - taylorModel f p x d) - ⟪y, c (x + d) - taylorModel c p x d⟫_ℝ := by
    simp only [residualLagrangian, inner_sub_right]
    ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add le_rfl (abs_real_inner_le_norm _ _))

/-- Actual segment smoothness and diagonal Lipschitz jets imply the sharp factorial
Lagrangian remainder, with constant `Lf + ‖y‖ * Lc`. -/
theorem abs_residualLagrangian_sub_taylorModel_le_lipschitz [CompleteSpace F]
    {f : E → ℝ} {c : E → F} {x d : E} {p : ℕ} {Lf Lc : ℝ} (hp : 1 ≤ p)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ p f (x + t • d))
    (hc : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ p c (x + t • d))
    (hLf : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(iteratedFDeriv ℝ p f (x + t • d) - iteratedFDeriv ℝ p f x) (fun _ => d)‖ ≤
        Lf * ‖t • d‖ * ‖d‖ ^ p)
    (hLc : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(iteratedFDeriv ℝ p c (x + t • d) - iteratedFDeriv ℝ p c x) (fun _ => d)‖ ≤
        Lc * ‖t • d‖ * ‖d‖ ^ p) (y : F) :
    |residualLagrangian f c y (x + d) - taylorModel (residualLagrangian f c y) p x d| ≤
      (Lf + ‖y‖ * Lc) / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1) := by
  have hf0 : ContDiffAt ℝ p f x := by simpa using hf 0 (by constructor <;> norm_num)
  have hc0 : ContDiffAt ℝ p c x := by simpa using hc 0 (by constructor <;> norm_num)
  have hrf := norm_sub_taylorModel_le_of_lipschitz_diagonal hp hf hLf
  have hrc := norm_sub_taylorModel_le_of_lipschitz_diagonal hp hc hLc
  have h := (abs_residualLagrangian_sub_taylorModel_le hf0 hc0 y d).trans
    (add_le_add (by simpa only [Real.norm_eq_abs] using hrf)
      (mul_le_mul_of_nonneg_left hrc (norm_nonneg y)))
  convert h using 1
  ring

/-- Actual component regularity and a bounded-radius Taylor gap give the signed objective
bound on any displacement subset. Compactness of that subset is not required. -/
theorem lagrangian_value_stability_signed_of_lipschitz [CompleteSpace F] [ProperSpace E]
    {f : E → ℝ} {c : E → F} {x d : E} {p : ℕ} {Lf Lc ε δ η : ℝ} {V : Set E}
    (hp : 1 ≤ p) (hε : 0 ≤ ε) (y : F)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ p f (x + t • d))
    (hc : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ p c (x + t • d))
    (hLf : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(iteratedFDeriv ℝ p f (x + t • d) - iteratedFDeriv ℝ p f x) (fun _ => d)‖ ≤
        Lf * ‖t • d‖ * ‖d‖ ^ p)
    (hLc : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(iteratedFDeriv ℝ p c (x + t • d) - iteratedFDeriv ℝ p c x) (fun _ => d)‖ ≤
        Lc * ‖t • d‖ * ‖d‖ ^ p)
    (hd : d ∈ V ∩ Metric.closedBall 0 δ)
    (hgap : TaylorCriticality.gapOn
      (TaylorCriticality.taylorDecrement (residualLagrangian f c y) p x)
      (V ∩ Metric.closedBall 0 δ) ≤ ε * δ ^ p / (p ! : ℝ) + η)
    (hsmall : (Lf + ‖y‖ * Lc) * ‖d‖ ≤ ((p + 1 : ℕ) : ℝ) * ε) :
    f x + ⟪y, c (x + d) - c x⟫_ℝ - 2 * ε * δ ^ p / (p ! : ℝ) - η ≤ f (x + d) := by
  have hb : BddAbove (TaylorCriticality.taylorDecrement (residualLagrangian f c y) p x ''
      (V ∩ Metric.closedBall 0 δ)) :=
    ((isCompact_closedBall (0 : E) δ).image
      (TaylorCriticality.continuous_taylorDecrement (residualLagrangian f c y) p x)).bddAbove.mono
        (image_mono inter_subset_right)
  have h := TaylorCriticality.value_lower_bound_of_gap_le_of_bddAbove hb hd hε
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hd.2) hgap
    (abs_residualLagrangian_sub_taylorModel_le_lipschitz hp hf hc hLf hLc y) hsmall
  simp only [residualLagrangian, inner_sub_right] at h ⊢
  linarith

/-- Open-neighborhood smoothness and genuine Lipschitz highest jets give signed stability
on any tested displacement subset; no compactness of the subset is assumed. -/
theorem lagrangian_value_stability_signed_on_ball [CompleteSpace F] [ProperSpace E]
    {f : E → ℝ} {c : E → F} {x d : E} {p : ℕ} {ε δ η : ℝ} {U V : Set E}
    (hp : 1 ≤ p) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (y : F) (hU : IsOpen U)
    (hball : Metric.closedBall x δ ⊆ U)
    (hf : ContDiffOn ℝ p f U) (hc : ContDiffOn ℝ p c U) (Lf Lc : ℝ≥0)
    (hLf : LipschitzOnWith Lf (iteratedFDeriv ℝ p f) U)
    (hLc : LipschitzOnWith Lc (iteratedFDeriv ℝ p c) U)
    (hd : d ∈ V ∩ Metric.closedBall 0 δ)
    (hgap : TaylorCriticality.gapOn
      (TaylorCriticality.taylorDecrement (residualLagrangian f c y) p x)
      (V ∩ Metric.closedBall 0 δ) ≤ ε * δ ^ p / (p ! : ℝ) + η)
    (hsmall : ((Lf : ℝ) + ‖y‖ * Lc) * ‖d‖ ≤ ((p + 1 : ℕ) : ℝ) * ε) :
    f x + ⟪y, c (x + d) - c x⟫_ℝ - 2 * ε * δ ^ p / (p ! : ℝ) - η ≤ f (x + d) := by
  have hxU : x ∈ U := hball (by simpa using hδ)
  have hdδ : ‖d‖ ≤ δ := by simpa using hd.2
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • d ∈ U := by
    apply hball
    have htd : ‖t • d‖ ≤ δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg d)).trans (by simpa using hdδ)
    simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] using htd
  apply lagrangian_value_stability_signed_of_lipschitz hp hε y
    (fun t ht => (hf.contDiffAt (hU.mem_nhds (hseg t ht))))
    (fun t ht => (hc.contDiffAt (hU.mem_nhds (hseg t ht)))) ?_ ?_ hd hgap hsmall
  · intro t ht
    have hl : ‖iteratedFDeriv ℝ p f (x + t • d) - iteratedFDeriv ℝ p f x‖ ≤
        (Lf : ℝ) * ‖t • d‖ := by
      simpa only [dist_eq_norm, add_sub_cancel_left] using hLf.dist_le_mul _ (hseg t ht) x hxU
    calc
      _ ≤ ‖iteratedFDeriv ℝ p f (x + t • d) - iteratedFDeriv ℝ p f x‖ * ‖d‖ ^ p := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          (iteratedFDeriv ℝ p f (x + t • d) - iteratedFDeriv ℝ p f x).le_opNorm (fun _ => d)
      _ ≤ _ := mul_le_mul_of_nonneg_right hl (pow_nonneg (norm_nonneg d) p)
  · intro t ht
    have hl : ‖iteratedFDeriv ℝ p c (x + t • d) - iteratedFDeriv ℝ p c x‖ ≤
        (Lc : ℝ) * ‖t • d‖ := by
      simpa only [dist_eq_norm, add_sub_cancel_left] using hLc.dist_le_mul _ (hseg t ht) x hxU
    calc
      _ ≤ ‖iteratedFDeriv ℝ p c (x + t • d) - iteratedFDeriv ℝ p c x‖ * ‖d‖ ^ p := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          (iteratedFDeriv ℝ p c (x + t • d) - iteratedFDeriv ℝ p c x).le_opNorm (fun _ => d)
      _ ≤ _ := mul_le_mul_of_nonneg_right hl (pow_nonneg (norm_nonneg d) p)

end Optimization.ConstrainedTaylorCriticality
