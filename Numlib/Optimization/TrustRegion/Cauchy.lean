import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# The Cauchy decrease for quadratic trust-region models

The Cauchy point minimizes the actual quadratic model on the feasible
negative-gradient ray. Comparing with a single explicit feasible ray point gives
the standard decrease bound without solving the ray minimization explicitly.
-/

namespace QuadraticTrustRegion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A quadratic model with linear term `g` and quadratic operator `B`. -/
noncomputable def model (f₀ : ℝ) (g : E) (B : E →L[ℝ] E) (s : E) : ℝ :=
  f₀ + inner ℝ g s + (1 / 2 : ℝ) * inner ℝ s (B s)

/-- The Cauchy point minimizes the quadratic model on the feasible
negative-gradient ray. This definition specifies an actual minimizer. -/
def IsCauchyPoint (f₀ : ℝ) (g : E) (B : E →L[ℝ] E) (Δ : ℝ) (s : E) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ ‖t • g‖ ≤ Δ ∧ s = -(t • g) ∧
    IsMinOn (fun u : ℝ => model f₀ g B (-(u • g)))
      {u | 0 ≤ u ∧ ‖u • g‖ ≤ Δ} t

/-- A Cauchy point exists for every nonnegative radius, including a zero
model gradient. No coercivity or definiteness of the quadratic operator is needed. -/
theorem exists_cauchyPoint (f₀ : ℝ) (g : E) (B : E →L[ℝ] E) {Δ : ℝ}
    (hΔ : 0 ≤ Δ) : ∃ s, IsCauchyPoint f₀ g B Δ s := by
  by_cases hg : g = 0
  · subst g
    refine ⟨0, 0, le_rfl, ?_, by simp, ?_⟩
    · simpa using hΔ
    · intro u hu
      simp [model]
  have hgp : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hset : {u : ℝ | 0 ≤ u ∧ ‖u • g‖ ≤ Δ} = Set.Icc 0 (Δ / ‖g‖) := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    constructor
    · rintro ⟨hu, hud⟩
      rw [norm_smul, Real.norm_of_nonneg hu] at hud
      exact ⟨hu, (le_div_iff₀ hgp).mpr hud⟩
    · rintro ⟨hu, hud⟩
      refine ⟨hu, ?_⟩
      rw [norm_smul, Real.norm_of_nonneg hu]
      exact (le_div_iff₀ hgp).mp hud
  have hcont : Continuous (fun u : ℝ => model f₀ g B (-(u • g))) := by
    unfold model
    fun_prop
  obtain ⟨t, ht, hm⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (div_nonneg hΔ hgp.le)) hcont.continuousOn
  rw [← hset] at ht hm
  exact ⟨-(t • g), t, ht.1, ht.2, rfl, hm⟩

/-- The quadratic term is bounded above by the operator norm. -/
theorem inner_operator_le (B : E →L[ℝ] E) (s : E) :
    inner ℝ s (B s) ≤ ‖B‖ * ‖s‖ ^ 2 := by
  calc
    inner ℝ s (B s) ≤ ‖s‖ * ‖B s‖ := real_inner_le_norm _ _
    _ ≤ ‖s‖ * (‖B‖ * ‖s‖) :=
      mul_le_mul_of_nonneg_left (B.le_opNorm s) (norm_nonneg _)
    _ = _ := by ring

/-- A Cauchy point achieves the standard norm-based model decrease. -/
theorem cauchy_decrease {f₀ : ℝ} {g sC : E} {B : E →L[ℝ] E} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hc : IsCauchyPoint f₀ g B Δ sC) :
    (1 / 2 : ℝ) * ‖g‖ * min (‖g‖ / (1 + ‖B‖)) Δ ≤
      model f₀ g B 0 - model f₀ g B sC := by
  rcases hc with ⟨t, ht, htd, hsC, hmin⟩
  by_cases hg : g = 0
  · subst g
    simp only [smul_zero, neg_zero] at hsC
    subst sC
    simp [model]
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
  let r := min (‖g‖ / (1 + ‖B‖)) Δ
  have hBpos : 0 < 1 + ‖B‖ := by positivity
  have hr0 : 0 ≤ r := le_min (div_nonneg (norm_nonneg _) hBpos.le) hΔ
  have hrΔ : r ≤ Δ := min_le_right _ _
  have hrB : (1 + ‖B‖) * r ≤ ‖g‖ := by
    have h := (le_div_iff₀ hBpos).mp (min_le_left (‖g‖ / (1 + ‖B‖)) Δ)
    dsimp [r]
    nlinarith
  have hnorm : ‖(r / ‖g‖) • g‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hr0 hgpos.le)]
    exact div_mul_cancel₀ _ hgpos.ne'
  have hm := hmin (show r / ‖g‖ ∈ {u : ℝ | 0 ≤ u ∧ ‖u • g‖ ≤ Δ} from
    ⟨div_nonneg hr0 hgpos.le, by rwa [hnorm]⟩)
  change model f₀ g B (-(t • g)) ≤ model f₀ g B (-((r / ‖g‖) • g)) at hm
  rw [hsC]
  have hi : inner ℝ g (-((r / ‖g‖) • g)) = -r * ‖g‖ := by
    rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hquad := inner_operator_le B (-((r / ‖g‖) • g))
  rw [norm_neg, hnorm] at hquad
  have hdecr : (1 / 2 : ℝ) * ‖g‖ * r ≤
      model f₀ g B 0 - model f₀ g B (-((r / ‖g‖) • g)) := by
    simp only [model, inner_zero_right, map_zero, add_zero, mul_zero,
      hi]
    have hb : ‖B‖ * r ≤ ‖g‖ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hb hr0]
  linarith

/-- Nonzero gradients and a positive radius give a strictly positive predicted
decrease at every point that improves on the Cauchy point. -/
theorem predicted_decrease_pos {f₀ : ℝ} {g sC s : E} {B : E →L[ℝ] E} {Δ : ℝ}
    (hΔ : 0 < Δ) (hg : g ≠ 0) (hc : IsCauchyPoint f₀ g B Δ sC)
    (hs : model f₀ g B s ≤ model f₀ g B sC) :
    0 < model f₀ g B 0 - model f₀ g B s := by
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hmin : 0 < min (‖g‖ / (1 + ‖B‖)) Δ :=
    lt_min (div_pos hgpos (by positivity)) hΔ
  have hp : 0 < (1 / 2 : ℝ) * ‖g‖ * min (‖g‖ / (1 + ‖B‖)) Δ := by positivity
  have hd := cauchy_decrease hΔ.le hc
  linarith

end QuadraticTrustRegion
