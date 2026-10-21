import Numlib.Optimization.SecularAsymptotics

/-!
# Asymptotics of actual stationary families

The equations of shifted quadratic subproblems determine the leading multiplier without
assuming convergence of that multiplier. The parameter domain and its filter are arbitrary.
-/

namespace Optimization.StationaryAsymptotics
open Filter Topology

section Normed
variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {l : Filter α} {A : E →L[ℝ] E} {g : E} {s : α → E} {t : α → ℝ}

/-- A nonzero right-hand side excludes a zero stationary step. -/
theorem stationary_ne_zero (hg : g ≠ 0) {x : E} {v : ℝ}
    (h : g + A x + v • x = 0) : x ≠ 0 := by
  intro hx
  simp only [hx, map_zero, smul_zero, add_zero] at h
  exact hg h

/-- Vanishing stationary steps determine the leading shift times step norm. -/
theorem tendsto_mul_norm_of_stationary
    (hstat : ∀ᶠ a in l, g + A (s a) + t a • s a = 0)
    (ht : ∀ᶠ a in l, 0 ≤ t a) (hs : Tendsto s l (𝓝 0)) :
    Tendsto (fun a => t a * ‖s a‖) l (𝓝 ‖g‖) := by
  have hA : Tendsto (fun a => A (s a)) l (𝓝 0) := by
    have h := (A.continuous.tendsto (0 : E)).comp hs
    rw [map_zero] at h
    exact h
  have hn := ((tendsto_const_nhds (x := g)).add hA).norm
  simp only [add_zero] at hn
  apply hn.congr'
  filter_upwards [hstat, ht] with a ha hta
  have he : g + A (s a) = -(t a • s a) := eq_neg_of_add_eq_zero_left ha
  rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hta]

/-- A positive limiting product with a vanishing nonnegative factor forces divergence. -/
theorem tendsto_atTop_of_mul_tendsto_pos {u v : α → ℝ} {c : ℝ}
    (hc : 0 < c) (hv : ∀ᶠ a in l, 0 ≤ v a)
    (hv0 : Tendsto v l (𝓝 0)) (hprod : Tendsto (fun a => u a * v a) l (𝓝 c)) :
    Tendsto u l atTop := by
  apply tendsto_atTop.2
  intro b
  have hsmall := hv0.eventually_lt_const (show 0 < c / (2 * (max b 1)) by positivity)
  have hlarge := hprod.eventually_const_lt (show c / 2 < c by linarith)
  filter_upwards [hv, hsmall, hlarge] with a hva hsa hla
  by_contra hb
  have hb' : u a < b := lt_of_not_ge hb
  have hB : 0 < max b 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hmul : u a * v a < c / 2 := calc
    u a * v a ≤ max b 1 * v a := mul_le_mul_of_nonneg_right
      (hb'.le.trans (le_max_left _ _)) hva
    _ < max b 1 * (c / (2 * max b 1)) := mul_lt_mul_of_pos_left hsa hB
    _ = c / 2 := by field_simp
  linarith

/-- The shift diverges along every shrinking stationary family with nonzero forcing. -/
theorem tendsto_atTop_of_stationary (hg : g ≠ 0)
    (hstat : ∀ᶠ a in l, g + A (s a) + t a • s a = 0)
    (ht : ∀ᶠ a in l, 0 ≤ t a) (hs : Tendsto s l (𝓝 0)) :
    Tendsto t l atTop :=
  tendsto_atTop_of_mul_tendsto_pos (norm_pos_iff.mpr hg)
    (Eventually.of_forall fun _ => norm_nonneg _) (by simpa using hs.norm)
    (tendsto_mul_norm_of_stationary hstat ht hs)

/-- The exact radius-to-weight conversion preserves the leading asymptotic coefficient. -/
theorem div_rpow_mul_rpow {x y p : ℝ} (hx : 0 < x) :
    (y / x ^ (p - 1)) * x ^ p = y * x := by
  rw [div_mul_eq_mul_div, mul_div_assoc, ← Real.rpow_sub hx]
  have he : p - (p - 1) = (1 : ℝ) := by ring
  rw [he, Real.rpow_one]

/-- The norm of the shift force is controlled by the forcing and operator norms. -/
theorem mul_norm_le_add_of_stationary {x : E} {v : ℝ} (hv : 0 ≤ v)
    (hstat : g + A x + v • x = 0) : v * ‖x‖ ≤ ‖g‖ + ‖A‖ * ‖x‖ := by
  have he : v • x = -(g + A x) := eq_neg_of_add_eq_zero_right hstat
  calc
    v * ‖x‖ = ‖v • x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hv]
    _ = ‖g + A x‖ := by rw [he, norm_neg]
    _ ≤ ‖g‖ + ‖A x‖ := norm_add_le _ _
    _ ≤ ‖g‖ + ‖A‖ * ‖x‖ := add_le_add le_rfl (A.le_opNorm x)

/-- Superquadratic regularization forces stationary steps to vanish even when the fixed
quadratic operator has negative curvature. -/
theorem tendsto_zero_of_superquadratic_stationary {σ : α → ℝ} {r : ℝ}
    (hr : 2 < r) (hσ : Tendsto σ l atTop)
    (hstat : ∀ᶠ a in l, g + A (s a) +
      (σ a * ‖s a‖ ^ (r - 2)) • s a = 0) : Tendsto s l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall fun a => hb.trans_le (norm_nonneg (s a))
  · intro b hb
    have hbp : 0 < b ^ (r - 2) := Real.rpow_pos_of_pos hb _
    have hbound : 0 ≤ (‖g‖ / b + ‖A‖) / b ^ (r - 2) := by positivity
    filter_upwards [hσ.eventually_gt_atTop ((‖g‖ / b + ‖A‖) / b ^ (r - 2)), hstat]
      with a hsa hsta
    have hsp : 0 < σ a := hbound.trans_lt hsa
    by_contra hnb
    have hbn : b ≤ ‖s a‖ := le_of_not_gt hnb
    have hn : 0 < ‖s a‖ := hb.trans_le hbn
    have hp := Real.rpow_le_rpow hb.le hbn (show 0 ≤ r - 2 by linarith)
    have hf := mul_norm_le_add_of_stationary
      (mul_nonneg hsp.le (Real.rpow_nonneg (norm_nonneg _) _)) hsta
    have hforce : σ a * ‖s a‖ ^ (r - 2) ≤ ‖g‖ / ‖s a‖ + ‖A‖ := by
      have hh := (div_le_div_of_nonneg_right hf hn.le)
      simpa only [mul_div_cancel_right₀ _ hn.ne', add_div] using hh
    have hdiv : ‖g‖ / ‖s a‖ ≤ ‖g‖ / b := div_le_div_of_nonneg_left (norm_nonneg _) hb hbn
    have hbig : ‖g‖ / b + ‖A‖ < σ a * b ^ (r - 2) := (div_lt_iff₀ hbp).mp hsa
    nlinarith [mul_le_mul_of_nonneg_left hp hsp.le]

/-- Exact normalization of a regularized multiplier in terms of its force product. -/
theorem regularized_normalization {σ x c p : ℝ} (hσ : 0 < σ) (hx : 0 < x)
    (hc : 0 < c) (hp : p ≠ 0) :
    (σ * x ^ (p - 1)) / (σ ^ (1 / p) * c ^ ((p - 1) / p)) =
      ((σ * x ^ (p - 1)) * x / c) ^ ((p - 1) / p) := by
  have hforce : (σ * x ^ (p - 1)) * x = σ * x ^ p := by
    rw [mul_assoc]
    congr 1
    calc
      x ^ (p - 1) * x = x ^ (p - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ p := by rw [← Real.rpow_add hx]; congr 1; ring
  rw [hforce, Real.div_rpow (mul_nonneg hσ.le (Real.rpow_nonneg hx.le _)) hc.le,
    Real.mul_rpow hσ.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
  have hxp : p * ((p - 1) / p) = p - 1 := by field_simp
  rw [hxp]
  have he : σ / σ ^ (1 / p) = σ ^ ((p - 1) / p) := by
    calc
      σ / σ ^ (1 / p) = σ ^ (1 : ℝ) / σ ^ (1 / p) := by rw [Real.rpow_one]
      _ = σ ^ (1 - 1 / p) := (Real.rpow_sub hσ _ _).symm
      _ = σ ^ ((p - 1) / p) := by congr 1; field_simp
  rw [div_mul_eq_div_div, mul_div_right_comm, he]

/-- The exact regularization relation converts a vanishing stationary family into the
normalized multiplier limit, without an assumed multiplier limit. -/
theorem tendsto_normalized_multiplier_of_stationary {σ : α → ℝ} {r : ℝ}
    (hg : g ≠ 0) (hr : r ≠ 1) (hσpos : ∀ᶠ a in l, 0 < σ a)
    (hs : Tendsto s l (𝓝 0))
    (hstat : ∀ᶠ a in l, g + A (s a) +
      (σ a * ‖s a‖ ^ (r - 2)) • s a = 0) :
    Tendsto (fun a => (σ a * ‖s a‖ ^ (r - 2)) /
      (σ a ^ (1 / (r - 1)) * ‖g‖ ^ ((r - 2) / (r - 1)))) l (𝓝 1) := by
  have ht : ∀ᶠ a in l, 0 ≤ σ a * ‖s a‖ ^ (r - 2) := by
    filter_upwards [hσpos] with a ha
    exact mul_nonneg ha.le (Real.rpow_nonneg (norm_nonneg _) _)
  have hforce := tendsto_mul_norm_of_stationary hstat ht hs
  have hquot := hforce.div_const ‖g‖
  rw [div_self (norm_ne_zero_iff.mpr hg)] at hquot
  have hpow := hquot.rpow_const (p := (r - 2) / (r - 1)) (Or.inl one_ne_zero)
  simp only [Real.one_rpow] at hpow
  apply hpow.congr'
  filter_upwards [hσpos, hstat] with a ha hsta
  have hx := norm_pos_iff.mpr (stationary_ne_zero hg hsta)
  have hp : r - 1 ≠ 0 := sub_ne_zero.mpr hr
  have he := regularized_normalization ha hx (norm_pos_iff.mpr hg) hp
  have hsub : r - 1 - 1 = r - 2 := by ring
  simpa only [hsub] using he.symm

/-- The normalized multiplier of an actual superquadratic stationary family tends to one.
No multiplier limit is assumed: the force bound first gives a vanishing step. -/
theorem tendsto_normalized_superquadratic_multiplier {σ : α → ℝ} {r : ℝ}
    (hg : g ≠ 0) (hr : 2 < r) (hσ : Tendsto σ l atTop)
    (hstat : ∀ᶠ a in l, g + A (s a) +
      (σ a * ‖s a‖ ^ (r - 2)) • s a = 0) :
    Tendsto (fun a => (σ a * ‖s a‖ ^ (r - 2)) /
      (σ a ^ (1 / (r - 1)) * ‖g‖ ^ ((r - 2) / (r - 1)))) l (𝓝 1) := by
  exact tendsto_normalized_multiplier_of_stationary hg (by linarith)
    (hσ.eventually_gt_atTop 0) (tendsto_zero_of_superquadratic_stationary hr hσ hstat) hstat

end Normed

section InnerProduct
variable {α E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {l : Filter α} {A : E →L[ℝ] E} {g : E} {s : α → E}

/-- Nonnegative quadratic curvature bounds the radial stationarity force by the forcing norm. -/
theorem mul_norm_le_of_stationary {x : E} {v : ℝ}
    (hA : 0 ≤ inner ℝ x (A x)) (hstat : g + A x + v • x = 0) :
    v * ‖x‖ ≤ ‖g‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he := congrArg (fun y => inner ℝ x y) hstat
  simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    inner_zero_right] at he
  have hi : -inner ℝ x g ≤ ‖x‖ * ‖g‖ := by
    calc
      -inner ℝ x g ≤ |inner ℝ x g| := neg_le_abs _
      _ ≤ ‖x‖ * ‖g‖ := abs_real_inner_le_norm _ _
  nlinarith

/-- Radial stationarity of a power-regularized quadratic implies its basic force bound. -/
theorem regularized_force_le {x : E} {σ r : ℝ} (hg : g ≠ 0)
    (hA : 0 ≤ inner ℝ x (A x))
    (hstat : g + A x + (σ * ‖x‖ ^ (r - 2)) • x = 0) :
    σ * ‖x‖ ^ (r - 1) ≤ ‖g‖ := by
  have hx := norm_pos_iff.mpr (stationary_ne_zero hg hstat)
  have he : ‖x‖ ^ (r - 2) * ‖x‖ = ‖x‖ ^ (r - 1) := by
    calc
      ‖x‖ ^ (r - 2) * ‖x‖ = ‖x‖ ^ (r - 2) * ‖x‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ‖x‖ ^ (r - 1) := by
        rw [← Real.rpow_add hx]
        congr 1
        ring
  simpa only [mul_assoc, he] using mul_norm_le_of_stationary hA hstat

/-- Increasing regularization weights force actual stationary steps to vanish when curvature
is nonnegative and the regularization order exceeds one. -/
theorem tendsto_zero_of_regularized_stationary {σ : α → ℝ} {r : ℝ}
    (hg : g ≠ 0) (hr : 1 < r) (hσ : Tendsto σ l atTop)
    (hA : ∀ᶠ a in l, 0 ≤ inner ℝ (s a) (A (s a)))
    (hstat : ∀ᶠ a in l, g + A (s a) +
      (σ a * ‖s a‖ ^ (r - 2)) • s a = 0) : Tendsto s l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall fun a => hb.trans_le (norm_nonneg (s a))
  · intro b hb
    have hbp : 0 < b ^ (r - 1) := Real.rpow_pos_of_pos hb _
    filter_upwards [hσ.eventually_gt_atTop (‖g‖ / b ^ (r - 1)), hA, hstat]
      with a hsa haa hsta
    have hforce := regularized_force_le hg haa hsta
    have hsp : 0 < σ a := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hbp.le) hsa
    by_contra hnb
    have hbn : b ≤ ‖s a‖ := le_of_not_gt hnb
    have hp := Real.rpow_le_rpow hb.le hbn (show 0 ≤ r - 1 by linarith)
    have hbig : ‖g‖ < σ a * b ^ (r - 1) := (div_lt_iff₀ hbp).mp hsa
    nlinarith [mul_le_mul_of_nonneg_left hp hsp.le]

/-- The normalized multiplier of an actual high-weight stationary family tends to one.
No multiplier limit is assumed: the force bound first gives a vanishing step. -/
theorem tendsto_normalized_regularized_multiplier {σ : α → ℝ} {r : ℝ}
    (hg : g ≠ 0) (hr : 1 < r) (hσ : Tendsto σ l atTop)
    (hA : ∀ᶠ a in l, 0 ≤ inner ℝ (s a) (A (s a)))
    (hstat : ∀ᶠ a in l, g + A (s a) +
      (σ a * ‖s a‖ ^ (r - 2)) • s a = 0) :
    Tendsto (fun a => (σ a * ‖s a‖ ^ (r - 2)) /
      (σ a ^ (1 / (r - 1)) * ‖g‖ ^ ((r - 2) / (r - 1)))) l (𝓝 1) := by
  exact tendsto_normalized_multiplier_of_stationary hg (ne_of_gt hr)
    (hσ.eventually_gt_atTop 0) (tendsto_zero_of_regularized_stationary hg hr hσ hA hstat)
    hstat

end InnerProduct

variable {α : Type*} {l : Filter α}

/-- Two positive radius-weight families with a common nonzero leading coefficient have
an asymptotic weight ratio equal to the reciprocal radius scale raised to the order. -/
theorem tendsto_weight_ratio {δ σ τ : α → ℝ} {c k p : ℝ} (hc : c ≠ 0)
    (hk : 0 < k) (hδ : ∀ᶠ a in l, 0 < δ a)
    (hσ : Tendsto (fun a => σ a * δ a ^ p) l (𝓝 c))
    (hτ : Tendsto (fun a => τ a * (δ a / k) ^ p) l (𝓝 c)) :
    Tendsto (fun a => τ a / σ a) l (𝓝 (k ^ p)) := by
  have hquot := (hτ.div hσ hc).mul_const (k ^ p)
  simp only [div_self hc, one_mul] at hquot
  apply hquot.congr'
  filter_upwards [hδ] with a ha
  change (τ a * (δ a / k) ^ p) / (σ a * δ a ^ p) * k ^ p = _
  rw [Real.div_rpow ha.le hk.le]
  have hd : δ a ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha _)
  have hkp : k ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hk _)
  field_simp

end Optimization.StationaryAsymptotics
