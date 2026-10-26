import Numlib.Optimization.Constrained.ModelComparison
import Numlib.Analysis.Calculus.TaylorModel.Peano

/-!
# Finite-order Taylor criticality at constrained local minima

A constrained local minimum controls actual feasible values near its center.
The genuine C^k Peano remainder then bounds Taylor criticality on every small
feasible ball. No convexity, interiority or constraint qualification is needed.
-/

namespace TaylorModel
open Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- Exactly C^k regularity and actual constrained local minimality make the
constrained degree-k Taylor criticality uniformly little-o of the radius power. -/
theorem exists_pos_constrainedCriticality_le_mul_pow {f : E → ℝ} {k : ℕ}
    (hk : 0 < k) (hf : ContDiff ℝ k f) {X : Set E} (hX : IsClosed X)
    {x : E} (hx : x ∈ X) (hmin : IsLocalMinOn f X x) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ δ : ℝ, 0 ≤ δ → δ < r →
      constrainedCriticality f k X x δ ≤ ε * δ ^ k := by
  obtain ⟨rR, hrR, hR⟩ := exists_pos_abs_sub_eval_le hk hf x hε
  obtain ⟨rL, hrL, hL⟩ := Metric.mem_nhdsWithin_iff.mp hmin
  refine ⟨min rR rL, lt_min hrR hrL, ?_⟩
  intro δ hδ hδr
  obtain ⟨d, hd, hn, he⟩ := exists_decrement_eq_constrainedCriticality f k hX hx hδ
  have hdR : ‖d‖ < rR := hn.trans_lt (hδr.trans_le (min_le_left _ _))
  have hdL : dist (x + d) x < rL := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact hn.trans_lt (hδr.trans_le (min_le_right _ _))
  have hlocal : f x ≤ f (x + d) := hL ⟨hdL, hd⟩
  have herr := (abs_le.mp (hR d hdR)).2
  have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg d) hn k) hε.le
  rw [←he, decrement_eq]
  linarith

/-- At a constrained local minimum, actual constrained Taylor criticality
normalized by delta^k tends to zero as the positive radius tends to zero. -/
theorem tendsto_constrainedCriticality_div_pow {f : E → ℝ} {k : ℕ}
    (hk : 0 < k) (hf : ContDiff ℝ k f) {X : Set E} (hX : IsClosed X)
    {x : E} (hx : x ∈ X) (hmin : IsLocalMinOn f X x) :
    Tendsto (fun δ : ℝ => constrainedCriticality f k X x δ / δ ^ k)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨r, hr, hb⟩ := exists_pos_constrainedCriticality_le_mul_pow hk hf hX hx hmin
    (half_pos hε)
  have hs : ∀ᶠ δ : ℝ in nhdsWithin 0 (Ioi 0), δ < r :=
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hs] with δ hδ hδr
  have hδ0 : 0 < δ := hδ
  have hn : 0 ≤ constrainedCriticality f k X x δ / δ ^ k :=
    div_nonneg (constrainedCriticality_nonneg f k hX hx hδ0.le) (pow_nonneg hδ0.le _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  have hratio : constrainedCriticality f k X x δ / δ ^ k ≤ ε / 2 :=
    (div_le_iff₀ (pow_pos hδ0 k)).2 (hb δ hδ0.le hδr)
  linarith

/-- Every requested positive finite order at a genuine constrained minimum
admits positive testing radii and actual feasible attaining directions passing
all normalized Taylor tests. No uniform quantitative radius floor is asserted. -/
theorem exists_constrained_criticality_radii_of_isMinOn {ι : Type*}
    {f : E → ℝ} {X : Set E} (hX : IsClosed X) {x : E} (hx : x ∈ X)
    (hmin : IsMinOn f X x) (order : ι → ℕ) (horder : ∀ a, 0 < order a)
    (hf : ∀ a, ContDiff ℝ (order a) f) {θ ζ : ℝ} (hθ : 0 < θ) (hζ : ζ ≤ 1)
    (ε : ι → ℝ) (hε : ∀ a, 0 < ε a) :
    ∃ (δ : ι → ℝ) (d : ι → E), (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧
      ∀ a, x + d a ∈ X ∧ ‖d a‖ ≤ δ a ∧
        ζ * constrainedCriticality f (order a) X x (δ a) ≤
          decrement f (order a) x (d a) ∧
        decrement f (order a) x (d a) ≤
          θ * ε a * δ a ^ order a / (order a).factorial := by
  classical
  have hex : ∀ a, ∃ δ : ℝ, (0 < δ ∧ δ ≤ 1) ∧
      constrainedCriticality f (order a) X x δ ≤
        θ * ε a * δ ^ order a / (order a).factorial := by
    intro a
    obtain ⟨r, hr, hb⟩ := exists_pos_constrainedCriticality_le_mul_pow (horder a) (hf a)
      hX hx hmin.isLocalMinOn
      (div_pos (mul_pos hθ (hε a)) (by positivity : (0 : ℝ) < (order a).factorial))
    refine ⟨min 1 (r / 2), ⟨lt_min zero_lt_one (half_pos hr), min_le_left _ _⟩, ?_⟩
    convert hb (min 1 (r / 2)) (le_min zero_le_one (half_pos hr).le)
      ((min_le_right _ _).trans_lt (half_lt_self hr)) using 1
    ring
  choose δ hδ hb using hex
  have hmax : ∀ a, ∃ d, x + d ∈ X ∧ ‖d‖ ≤ δ a ∧
      decrement f (order a) x d = constrainedCriticality f (order a) X x (δ a) :=
    fun a => exists_decrement_eq_constrainedCriticality f (order a) hX hx (hδ a).1.le
  choose d hd hn he using hmax
  refine ⟨δ, d, hδ, fun a => ⟨hd a, hn a, ?_, ?_⟩⟩
  · rw [he a]
    exact mul_le_of_le_one_left
      (constrainedCriticality_nonneg f (order a) hX hx (hδ a).1.le) hζ
  · rw [he a]
    exact hb a

end TaylorModel
