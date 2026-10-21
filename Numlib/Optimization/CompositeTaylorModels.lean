import Numlib.Optimization.RegularizedTaylorModel
import Numlib.Optimization.TaylorCriticality
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.LocalExtr

/-!
# Generalized Taylor models of composite objectives

For `f + h ∘ c`, only the smooth maps `f` and `c` are expanded. The outer map `h` is retained
exactly. Lipschitz continuity controls value errors; convexity yields first-order necessary
optimality even when `h` is nonsmooth. Subadditivity is bundled separately for higher-order
composite model estimates.
-/

noncomputable section

open scoped Nat Topology NNReal
open Filter Asymptotics
open Optimization.RegularizedTaylorModel

namespace Optimization.CompositeTaylorModels

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A globally Lipschitz, subadditive scalar composition, normalized to vanish at zero.
Convexity is a separate hypothesis and is not implied by this interface. -/
structure LipschitzSubadditiveComposition (F : Type*) [NormedAddCommGroup F] where
  toFun : F → ℝ
  constant : ℝ≥0
  lipschitz : LipschitzWith constant toFun
  map_zero : toFun 0 = 0
  map_add_le : ∀ u v, toFun (u + v) ≤ toFun u + toFun v

namespace LipschitzSubadditiveComposition

instance : CoeFun (LipschitzSubadditiveComposition F) (fun _ ↦ F → ℝ) := ⟨toFun⟩

omit [NormedSpace ℝ F] in
@[simp] theorem apply_zero (h : LipschitzSubadditiveComposition F) : h 0 = 0 := h.map_zero

omit [NormedSpace ℝ F] in
/-- Normalization and Lipschitz continuity bound the absolute composition value. -/
theorem abs_apply_le (h : LipschitzSubadditiveComposition F) (u : F) :
    |h u| ≤ h.constant * ‖u‖ := by
  simpa [Real.dist_eq, h.apply_zero] using h.lipschitz.dist_le_mul u 0

/-- The sum of two admissible composition functions remains admissible. -/
def add (h k : LipschitzSubadditiveComposition F) : LipschitzSubadditiveComposition F where
  toFun u := h u + k u
  constant := h.constant + k.constant
  lipschitz := h.lipschitz.add k.lipschitz
  map_zero := by simp
  map_add_le u v := by linarith [h.map_add_le u v, k.map_add_le u v]

omit [NormedSpace ℝ F] in
@[simp] theorem add_apply (h k : LipschitzSubadditiveComposition F) (u : F) :
    h.add k u = h u + k u := rfl

omit [NormedSpace ℝ F] in
/-- Subadditivity extends to every finite sum of input vectors. -/
theorem map_sum_le {ι : Type*} (h : LipschitzSubadditiveComposition F)
    (S : Finset ι) (u : ι → F) : h (∑ i ∈ S, u i) ≤ ∑ i ∈ S, h (u i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi] using (h.map_add_le (u i) (∑ j ∈ S, u j)).trans
      (add_le_add le_rfl ih)

end LipschitzSubadditiveComposition

/-- The generalized degree-`p` Taylor model, retaining the outer composition exactly. -/
def model (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x s : E) : ℝ :=
  taylorModel f p x s + h (taylorModel c p x s)

@[simp] theorem model_zero (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x : E) :
    model f c h p x 0 = f x + h (c x) := by simp [model]

@[simp] theorem model_one (f : E → ℝ) (c : E → F) (h : F → ℝ) (x s : E) :
    model f c h 1 x s = f x + fderiv ℝ f x s + h (c x + fderiv ℝ c x s) := by
  simp [model]

/-- The generalized Taylor decrement relative to the zero displacement. -/
def decrement (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x s : E) : ℝ :=
  model f c h p x 0 - model f c h p x s

@[simp] theorem decrement_zero (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x : E) :
    decrement f c h p x 0 = 0 := sub_self _

/-- Lipschitz continuity of the outer map makes the generalized model continuous in the step. -/
theorem continuous_model (f : E → ℝ) (c : E → F) {h : F → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (p : ℕ) (x : E) : Continuous (model f c h p x) :=
  (contDiff_taylorModel f p x 0).continuous.add
    (hh.continuous.comp (contDiff_taylorModel c p x 0).continuous)

/-- The generalized decrement is continuous whenever the outer composition is Lipschitz. -/
theorem continuous_decrement (f : E → ℝ) (c : E → F) {h : F → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) (p : ℕ) (x : E) : Continuous (decrement f c h p x) :=
  continuous_const.sub (continuous_model f c hh p x)

/-- The decrement compares the actual objective value at the base point with its model. -/
theorem decrement_eq (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ) (x s : E) :
    decrement f c h p x s = f x + h (c x) - model f c h p x s := by
  simp [decrement]

/-- Scalar and vector Taylor remainders combine through the Lipschitz constant of `h`.
Neither convexity nor subadditivity of `h` is needed. -/
theorem model_error_le {f : E → ℝ} {c : E → F} {h : F → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) {p : ℕ} {x s : E} {A B : ℝ}
    (hf : |f (x + s) - taylorModel f p x s| ≤ A * ‖s‖ ^ (p + 1))
    (hc : ‖c (x + s) - taylorModel c p x s‖ ≤ B * ‖s‖ ^ (p + 1)) :
    |f (x + s) + h (c (x + s)) - model f c h p x s| ≤
      (A + K * B) * ‖s‖ ^ (p + 1) := by
  have hLip : |h (c (x + s)) - h (taylorModel c p x s)| ≤
      K * ‖c (x + s) - taylorModel c p x s‖ := by
    simpa [Real.dist_eq, dist_eq_norm] using
      hh.dist_le_mul (c (x + s)) (taylorModel c p x s)
  calc
    _ = |(f (x + s) - taylorModel f p x s) +
        (h (c (x + s)) - h (taylorModel c p x s))| := by congr 1; simp [model]; ring
    _ ≤ |f (x + s) - taylorModel f p x s| +
        |h (c (x + s)) - h (taylorModel c p x s)| := abs_add_le _ _
    _ ≤ A * ‖s‖ ^ (p + 1) + K * (B * ‖s‖ ^ (p + 1)) :=
      add_le_add hf (hLip.trans (mul_le_mul_of_nonneg_left hc K.coe_nonneg))
    _ = _ := by ring

/-- A local minimum of a differentiable smooth part plus a convex Lipschitz composition
minimizes its first generalized model globally. No derivative of the outer map is used. -/
theorem first_model_min_of_convex_localMin {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {K : ℝ≥0} {x : E} (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    (hLip : LipschitzWith K h) (hconv : ConvexOn ℝ Set.univ h)
    (hmin : IsLocalMin (fun y ↦ f y + h (c y)) x) (s : E) :
    model f c h 1 x 0 ≤ model f c h 1 x s := by
  by_contra hn
  have hgap : 0 < model f c h 1 x 0 - model f c h 1 x s := sub_pos.mpr (lt_of_not_ge hn)
  have hs : s ≠ 0 := by intro hs; simp [hs] at hgap
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs
  let ε : ℝ := (model f c h 1 x 0 - model f c h 1 x s) /
    (2 * (1 + K) * ‖s‖)
  have hK : 0 ≤ (K : ℝ) := K.coe_nonneg
  have hε : 0 < ε := div_pos hgap (by positivity)
  have hfb := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hf.hasFDerivAt).bound hε
  have hcb := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hc.hasFDerivAt).bound hε
  have htend : Tendsto (fun t : ℝ ↦ t • s) (𝓝 0) (𝓝 (0 : E)) := by
    have hh : Continuous (fun t : ℝ ↦ t • s) := by fun_prop
    simpa using hh.tendsto 0
  have hloc : ∀ᶠ t : ℝ in 𝓝 0,
      f x + h (c x) ≤ f (x + t • s) + h (c (x + t • s)) := by
    have ht : Tendsto (fun t : ℝ ↦ x + t • s) (𝓝 0) (𝓝 x) := by
      simpa using tendsto_const_nhds.add htend
    exact ht.eventually hmin
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0,
      0 < t ∧ t < 1 ∧
      ‖f (x + t • s) - f x - fderiv ℝ f x (t • s)‖ ≤ ε * ‖t • s‖ ∧
      ‖c (x + t • s) - c x - fderiv ℝ c x (t • s)‖ ≤ ε * ‖t • s‖ ∧
      f x + h (c x) ≤ f (x + t • s) + h (c (x + t • s)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds, (htend.eventually hfb).filter_mono nhdsWithin_le_nhds,
      (htend.eventually hcb).filter_mono nhdsWithin_le_nhds,
      hloc.filter_mono nhdsWithin_le_nhds] with t ht ht1 hft hct hlt
    exact ⟨ht, ht1, hft, hct, hlt⟩
  obtain ⟨t, ht, ht1, hft, hct, hlt⟩ := hevent.exists
  have hnorm : ‖t • s‖ = t * ‖s‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hft' : f (x + t • s) ≤ f x + t * fderiv ℝ f x s + ε * t * ‖s‖ := by
    rw [hnorm, map_smul, smul_eq_mul, Real.norm_eq_abs] at hft
    have := (abs_le.mp hft).2
    nlinarith
  have hct' : |h (c (x + t • s)) - h (c x + t • fderiv ℝ c x s)| ≤
      K * (ε * t * ‖s‖) := by
    have hh := hLip.dist_le_mul (c (x + t • s)) (c x + t • fderiv ℝ c x s)
    rw [Real.dist_eq, dist_eq_norm] at hh
    have hcc : ‖c (x + t • s) - (c x + t • fderiv ℝ c x s)‖ ≤ ε * t * ‖s‖ := by
      simpa [map_smul, hnorm, sub_sub, mul_assoc] using hct
    exact hh.trans (mul_le_mul_of_nonneg_left hcc hK)
  have hcv : h (c x + t • fderiv ℝ c x s) ≤
      (1 - t) * h (c x) + t * h (c x + fderiv ℝ c x s) := by
    have hh := hconv.2 (Set.mem_univ (c x)) (Set.mem_univ (c x + fderiv ℝ c x s))
      (sub_nonneg.mpr ht1.le) ht.le (by ring : (1 - t) + t = 1)
    have heq : (1 - t) • c x + t • (c x + fderiv ℝ c x s) =
        c x + t • fderiv ℝ c x s := by module
    rw [heq] at hh
    simpa only [smul_eq_mul] using hh
  have htotal : t * (model f c h 1 x 0 - model f c h 1 x s) ≤
      (1 + K) * ε * t * ‖s‖ := by
    have hh := (abs_le.mp hct').2
    simp only [model_zero, model_one] at *
    nlinarith
  have heq : (1 + (K : ℝ)) * ε * t * ‖s‖ =
      t * (model f c h 1 x 0 - model f c h 1 x s) / 2 := by
    dsimp [ε]
    field_simp
  rw [heq] at htotal
  nlinarith [mul_pos ht hgap]

/-- The generalized Taylor model with factorially normalized radial regularization. -/
def regularizedModel (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ)
    (x : E) (σ : ℝ) (s : E) : ℝ :=
  model f c h p x s + σ * ‖s‖ ^ (p + 1) / (p + 1)!

@[simp] theorem regularizedModel_zero (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (p : ℕ) (x : E) (σ : ℝ) : regularizedModel f c h p x σ 0 = f x + h (c x) := by
  simp [regularizedModel]

/-- Model nonincrease pays for the entire radial regularizer in the unregularized decrement. -/
theorem regularized_decrement_lower_bound {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {p : ℕ} {x s : E} {σ : ℝ}
    (hs : regularizedModel f c h p x σ s ≤ regularizedModel f c h p x σ 0) :
    σ * ‖s‖ ^ (p + 1) / (p + 1)! ≤ decrement f c h p x s := by
  simp only [regularizedModel, norm_zero, zero_pow (Nat.succ_ne_zero p), mul_zero,
    zero_div, add_zero] at hs
  dsimp [decrement]
  linarith

end Optimization.CompositeTaylorModels
