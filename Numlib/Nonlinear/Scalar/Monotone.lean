import Numlib.Nonlinear.ScalarNewton
import Numlib.Nonlinear.Secant
import Mathlib.Analysis.Convex.Deriv

/-!
# Monotone Newton and secant convergence from one side of a simple root

A continuous, nondecreasing negative derivative controls both Newton slopes and
secant slopes. The same scalar step estimate gives interval invariance and the
explicit uniform contraction factor. Keeping a root once reached handles finite
termination without dividing by a vanishing secant denominator.
-/

open Set Filter Topology

namespace MonotoneRoot

/-- Scalar data on the interval from the starting point to a simple root.
The nondecreasing derivative is the differentiable characterization of convexity. -/
structure Data (f f' : ℝ → ℝ) (a b : ℝ) : Prop where
  le_root : a ≤ b
  derivative : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x
  continuous_derivative : ContinuousOn f' (Icc a b)
  monotone_derivative : MonotoneOn f' (Icc a b)
  root : f b = 0
  derivative_root_neg : f' b < 0

variable {f f' : ℝ → ℝ} {a b : ℝ}

/-- Every derivative on the initial interval is negative. -/
theorem Data.derivative_neg (h : Data f f' a b) {x : ℝ} (hx : x ∈ Icc a b) : f' x < 0 :=
  (h.monotone_derivative hx ⟨h.le_root, le_rfl⟩ hx.2).trans_lt h.derivative_root_neg

/-- The function is squeezed between its two endpoint tangent lines. -/
theorem Data.tangent_bounds (h : Data f f' a b) {x : ℝ} (hx : x ∈ Icc a b) :
    f' b * (x - b) ≤ f x ∧ f x ≤ f' x * (x - b) := by
  rcases hx.2.eq_or_lt with rfl | hxb
  · simp [h.root]
  obtain ⟨ξ, hξ, heq⟩ := exists_hasDerivAt_eq_slope f f' hxb
    (fun y hy => (h.derivative y ⟨hx.1.trans hy.1, hy.2⟩).continuousAt.continuousWithinAt)
    (fun y hy => h.derivative y ⟨hx.1.trans hy.1.le, hy.2.le⟩)
  have hξmem : ξ ∈ Icc a b := ⟨hx.1.trans hξ.1.le, hξ.2.le⟩
  have hid : f x = f' ξ * (x - b) := by
    rw [heq, h.root]
    field_simp
    ring
  rw [hid]
  exact ⟨mul_le_mul_of_nonpos_right
    (h.monotone_derivative hξmem ⟨h.le_root, le_rfl⟩ hξ.2.le) (sub_nonpos.mpr hx.2),
    mul_le_mul_of_nonpos_right
      (h.monotone_derivative hx hξmem hξ.1.le) (sub_nonpos.mpr hx.2)⟩

/-- The objective value is nonnegative to the left of its root. -/
theorem Data.value_nonneg (h : Data f f' a b) {x : ℝ} (hx : x ∈ Icc a b) : 0 ≤ f x :=
  (mul_nonneg_of_nonpos_of_nonpos h.derivative_root_neg.le (sub_nonpos.mpr hx.2)).trans
    (h.tangent_bounds hx).1

/-- The fixed global contraction factor. -/
noncomputable def factor (f' : ℝ → ℝ) (a b : ℝ) : ℝ := 1 - f' b / f' a

/-- The contraction factor lies in `[0,1)`, including an affine objective. -/
theorem Data.factor_mem (h : Data f f' a b) : factor f' a b ∈ Ico (0 : ℝ) 1 := by
  have ha := h.derivative_neg ⟨le_rfl, h.le_root⟩
  have hab := h.monotone_derivative ⟨le_rfl, h.le_root⟩ ⟨h.le_root, le_rfl⟩ h.le_root
  have hp := div_pos_of_neg_of_neg h.derivative_root_neg ha
  have hle : f' b / f' a ≤ 1 := (div_le_iff_of_neg ha).mpr (by linarith)
  dsimp [factor]
  constructor <;> linarith

/-- A Newton or past-secant slope gives an increasing, root-preserving step and
both the local slope-ratio error bound and the fixed global contraction bound. -/
theorem Data.step_bounds (h : Data f f' a b) {x d : ℝ} (hx : x ∈ Icc a b)
    (hdlo : f' a ≤ d) (hdhi : d ≤ f' x) :
    x ≤ Newton.scalarStep f (fun _ => d) x ∧
      Newton.scalarStep f (fun _ => d) x ≤ b ∧
      b - Newton.scalarStep f (fun _ => d) x ≤ (1 - f' b / d) * (b - x) ∧
      (1 - f' b / d) * (b - x) ≤ factor f' a b * (b - x) := by
  have hdx : d < 0 := hdhi.trans_lt (h.derivative_neg hx)
  have hda := h.derivative_neg ⟨le_rfl, h.le_root⟩
  have hval := h.value_nonneg hx
  have ht := h.tangent_bounds hx
  have hstep : 0 ≤ -(f x / d) := neg_nonneg.mpr (div_nonpos_of_nonneg_of_nonpos hval hdx.le)
  have hupper : f x ≤ d * (x - b) := ht.2.trans
    (mul_le_mul_of_nonpos_right hdhi (sub_nonpos.mpr hx.2))
  have hdivlower : x - b ≤ f x / d := by
    apply (le_div_iff_of_neg hdx).mpr
    nlinarith
  have hdivupper : f x / d ≤ f' b * (x - b) / d :=
    div_le_div_of_nonpos_of_le hdx.le ht.1
  have hrat : f' b / f' a ≤ f' b / d := by
    have hr := div_le_div_of_nonneg_left (neg_nonneg.mpr h.derivative_root_neg.le)
      (neg_pos.mpr hdx) (neg_le_neg hdlo)
    simpa only [neg_div_neg_eq] using hr
  dsimp [Newton.scalarStep]
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · convert add_le_add_left hdivupper (b - x) using 1 <;> ring
  · exact mul_le_mul_of_nonneg_right (by dsimp [factor]; linarith) (sub_nonneg.mpr hx.2)

/-- The scalar Newton orbit, fixed at a root once it is reached. -/
noncomputable def newtonOrbit (f f' : ℝ → ℝ) (a : ℝ) (n : ℕ) : ℝ :=
  (Newton.scalarStep f f')^[n] a

/-- The Newton orbit starts at the prescribed initial point. -/
@[simp] theorem newtonOrbit_zero (f f' : ℝ → ℝ) (a : ℝ) : newtonOrbit f f' a 0 = a := rfl

/-- One genuine Newton update. -/
theorem newtonOrbit_succ (f f' : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    newtonOrbit f f' a (n + 1) = Newton.scalarStep f f' (newtonOrbit f f' a n) :=
  Function.iterate_succ_apply' _ _ _

/-- All Newton iterates lie between their initial point and the root. -/
theorem Data.newtonOrbit_mem (h : Data f f' a b) (n : ℕ) :
    newtonOrbit f f' a n ∈ Icc a b := by
  induction n with
  | zero => exact ⟨le_rfl, h.le_root⟩
  | succ n ih =>
    have hs := h.step_bounds ih (h.monotone_derivative ⟨le_rfl, h.le_root⟩ ih ih.1) le_rfl
    rw [newtonOrbit_succ]
    exact ⟨ih.1.trans hs.1, hs.2.1⟩

/-- Newton iterates increase monotonically and satisfy both explicit one-step
error estimates, including after finite termination. -/
theorem Data.newtonOrbit_bounds (h : Data f f' a b) (n : ℕ) :
    newtonOrbit f f' a n ≤ newtonOrbit f f' a (n + 1) ∧
      b - newtonOrbit f f' a (n + 1) ≤
        (1 - f' b / f' (newtonOrbit f f' a n)) * (b - newtonOrbit f f' a n) ∧
      (1 - f' b / f' (newtonOrbit f f' a n)) * (b - newtonOrbit f f' a n) ≤
        factor f' a b * (b - newtonOrbit f f' a n) := by
  have hm := h.newtonOrbit_mem n
  have hs := h.step_bounds hm (h.monotone_derivative ⟨le_rfl, h.le_root⟩ hm hm.1) le_rfl
  rw [newtonOrbit_succ]
  exact ⟨hs.1, hs.2.2⟩

/-- The Newton errors are bounded by the explicit geometric majorant. -/
theorem Data.newtonOrbit_error_le (h : Data f f' a b) (n : ℕ) :
    b - newtonOrbit f f' a n ≤ factor f' a b ^ n * (b - a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := (h.newtonOrbit_bounds n).2.1.trans (h.newtonOrbit_bounds n).2.2
    calc _ ≤ factor f' a b * (b - newtonOrbit f f' a n) := hs
         _ ≤ factor f' a b * (factor f' a b ^ n * (b - a)) :=
           mul_le_mul_of_nonneg_left ih h.factor_mem.1
         _ = _ := by ring

/-- The monotone Newton orbit converges globally to the root. -/
theorem Data.tendsto_newtonOrbit (h : Data f f' a b) :
    Tendsto (newtonOrbit f f' a) atTop (𝓝 b) := by
  have hgeom := (tendsto_pow_atTop_nhds_zero_of_lt_one h.factor_mem.1 h.factor_mem.2).mul_const
    (b - a)
  have he : Tendsto (fun n => b - newtonOrbit f f' a n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sub_nonneg.mpr (h.newtonOrbit_mem n).2)
      h.newtonOrbit_error_le
    simpa only [zero_mul] using hgeom
  convert (tendsto_const_nhds (x := b)).sub he using 1
  · ext n
    ring
  · simp only [sub_zero]

/-- The local slope-ratio multiplier tends to zero by continuity of the
actual derivative; twice differentiability is unnecessary. -/
theorem Data.tendsto_newton_multiplier (h : Data f f' a b) :
    Tendsto (fun n => 1 - f' b / f' (newtonOrbit f f' a n)) atTop (𝓝 0) := by
  have hd : Tendsto (fun n => f' (newtonOrbit f f' a n)) atTop (𝓝 (f' b)) :=
    (h.continuous_derivative b ⟨h.le_root, le_rfl⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨h.tendsto_newtonOrbit,
        Eventually.of_forall h.newtonOrbit_mem⟩)
  simpa only [Pi.div_apply, Pi.sub_apply, div_self h.derivative_root_neg.ne, sub_self] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := f' b)).div hd h.derivative_root_neg.ne)

/-- Newton convergence is ultimately Q-superlinear, with the error ratio
extended by zero after an exact root is reached. -/
theorem Data.tendsto_newton_error_ratio (h : Data f f' a b) :
    Tendsto (fun n => (b - newtonOrbit f f' a (n + 1)) /
      (b - newtonOrbit f f' a n)) atTop (𝓝 0) := by
  have hrat (n : ℕ) : (b - newtonOrbit f f' a (n + 1)) /
      (b - newtonOrbit f f' a n) ≤ 1 - f' b / f' (newtonOrbit f f' a n) := by
    have hm := h.newtonOrbit_mem n
    rcases hm.2.eq_or_lt with heq | hlt
    · rw [heq, sub_self, div_zero, div_self h.derivative_root_neg.ne, sub_self]
    · apply (div_le_iff₀ (sub_pos.mpr hlt)).mpr
      exact (h.newtonOrbit_bounds n).2.1
  exact squeeze_zero
    (fun n => div_nonneg (sub_nonneg.mpr (h.newtonOrbit_mem (n + 1)).2)
      (sub_nonneg.mpr (h.newtonOrbit_mem n).2)) hrat h.tendsto_newton_multiplier

/-- Positive values occur strictly before the simple root. -/
theorem Data.value_pos (h : Data f f' a b) {x : ℝ} (hx : x ∈ Icc a b) (hxb : x < b) :
    0 < f x :=
  (mul_pos_of_neg_of_neg h.derivative_root_neg (sub_neg.mpr hxb)).trans_le
    (h.tangent_bounds hx).1

/-- A permitted slope produces strict progress before the root. -/
theorem Data.lt_step (h : Data f f' a b) {x d : ℝ} (hx : x ∈ Icc a b) (hxb : x < b)
    (hd : d ≤ f' x) : x < Newton.scalarStep f (fun _ => d) x := by
  have hquot := div_neg_of_pos_of_neg (h.value_pos hx hxb) (hd.trans_lt (h.derivative_neg hx))
  dsimp [Newton.scalarStep]
  linarith

/-- Each actual past secant slope is an actual derivative at an intermediate
point, with the appropriate monotone derivative bounds. -/
theorem Data.secant_slope (h : Data f f' a b) {x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x < y) :
    ∃ ξ ∈ Ioo x y, (f y - f x) / (y - x) = f' ξ ∧
      f' a ≤ f' ξ ∧ f' ξ ≤ f' y := by
  obtain ⟨ξ, hξ, heq⟩ := exists_hasDerivAt_eq_slope f f' hxy
    (fun z hz => by
      have hm : z ∈ Icc a b := ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
      exact (h.derivative z hm).continuousAt.continuousWithinAt)
    (fun z hz => h.derivative z ⟨hx.1.trans hz.1.le, hz.2.le.trans hy.2⟩)
  have hξmem : ξ ∈ Icc a b := ⟨hx.1.trans hξ.1.le, hξ.2.le.trans hy.2⟩
  exact ⟨ξ, hξ, heq.symm,
    h.monotone_derivative ⟨le_rfl, h.le_root⟩ hξmem hξmem.1,
    h.monotone_derivative hξmem hy hξ.2.le⟩

/-- The actual secant state stays ordered inside the root interval. The
alternative allows the two coordinates to coincide after exact termination. -/
theorem Data.secant_state (h : Data f f' a b) {c : ℝ} (hac : a < c) (hcb : c ≤ b)
    (n : ℕ) :
    let z := (Secant.step f)^[n] (a, c)
    z.1 ∈ Icc a b ∧ z.2 ∈ Icc a b ∧ (z.1 < z.2 ∨ z.2 = b) := by
  induction n with
  | zero => exact ⟨⟨le_rfl, h.le_root⟩, ⟨hac.le, hcb⟩, Or.inl hac⟩
  | succ n ih =>
    let z := (Secant.step f)^[n] (a, c)
    change z.1 ∈ Icc a b ∧ z.2 ∈ Icc a b ∧ (z.1 < z.2 ∨ z.2 = b) at ih
    rw [Function.iterate_succ_apply']
    change (Secant.step f z).1 ∈ Icc a b ∧ (Secant.step f z).2 ∈ Icc a b ∧ _
    rcases ih.2.2 with hord | hroot
    · obtain ⟨ξ, _, hξeq, hlow, hhigh⟩ := h.secant_slope ih.1 ih.2.1 hord
      have hconvert : (Secant.step f z).2 = Newton.scalarStep f (fun _ => f' ξ) z.2 := by
        dsimp [Secant.step, Newton.scalarStep]
        rw [← hξeq]
        field_simp
      have hs := h.step_bounds ih.2.1 hlow hhigh
      refine ⟨ih.2.1, ⟨ih.2.1.1.trans (by simpa only [hconvert] using hs.1),
        by simpa only [hconvert] using hs.2.1⟩, ?_⟩
      rcases ih.2.1.2.eq_or_lt with hy | hy
      · right
        change (Secant.step f z).2 = b
        change z.2 - (z.2 - z.1) / (f z.2 - f z.1) * f z.2 = b
        rw [hy, h.root, mul_zero, sub_zero]
      · left
        change z.2 < (Secant.step f z).2
        rw [hconvert]
        exact h.lt_step ih.2.1 hy hhigh
    · have hfixed : Secant.step f z = (b, b) := by
        simp only [Secant.step, hroot, h.root, mul_zero, sub_zero]
      rw [hfixed]
      exact ⟨⟨h.le_root, le_rfl⟩, ⟨h.le_root, le_rfl⟩, Or.inr rfl⟩

/-- The real secant slope, assigned the root derivative after termination.
This assignment only removes a `0/0` in rate formulas and leaves the iteration unchanged. -/
noncomputable def secantSlope (f f' : ℝ → ℝ) (b : ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.2 = b then f' b else (f z.2 - f z.1) / (z.2 - z.1)

/-- The effective secant slopes satisfy the same bounds as Newton slopes. -/
theorem Data.secantSlope_bounds (h : Data f f' a b) {c : ℝ}
    (hac : a < c) (hcb : c ≤ b) (n : ℕ) :
    let z := (Secant.step f)^[n] (a, c)
    f' a ≤ secantSlope f f' b z ∧ secantSlope f f' b z ≤ f' z.2 := by
  let z := (Secant.step f)^[n] (a, c)
  have hs := h.secant_state hac hcb n
  change z.1 ∈ Icc a b ∧ z.2 ∈ Icc a b ∧ _ at hs
  change f' a ≤ secantSlope f f' b z ∧ secantSlope f f' b z ≤ f' z.2
  by_cases hz : z.2 = b
  · rw [secantSlope, ite_eq_left hz, hz]
    exact ⟨h.monotone_derivative ⟨le_rfl, h.le_root⟩ ⟨h.le_root, le_rfl⟩ h.le_root, le_rfl⟩
  · obtain ⟨ξ, _, heq, hlo, hhi⟩ := h.secant_slope hs.1 hs.2.1 (hs.2.2.resolve_right hz)
    rw [secantSlope, ite_eq_right hz, heq]
    exact ⟨hlo, hhi⟩

/-- Actual secant steps are scalar Newton steps with the actual secant slope,
including every update following finite termination. -/
theorem Data.secant_step_eq (h : Data f f' a b) {c : ℝ} (n : ℕ) :
    let z := (Secant.step f)^[n] (a, c)
    (Secant.step f z).2 = Newton.scalarStep f (fun _ => secantSlope f f' b z) z.2 := by
  let z := (Secant.step f)^[n] (a, c)
  change (Secant.step f z).2 = Newton.scalarStep f (fun _ => secantSlope f f' b z) z.2
  by_cases hz : z.2 = b
  · rw [secantSlope, ite_eq_left hz]
    change z.2 - (z.2 - z.1) / (f z.2 - f z.1) * f z.2 = z.2 - f z.2 / f' b
    rw [hz, h.root, zero_div, mul_zero, sub_zero]
  · rw [secantSlope, ite_eq_right hz]
    change z.2 - (z.2 - z.1) / (f z.2 - f z.1) * f z.2 =
      z.2 - f z.2 / ((f z.2 - f z.1) / (z.2 - z.1))
    field_simp

/-- The secant orbit is increasing and has the exact source contraction bound. -/
theorem Data.secantOrbit_bounds (h : Data f f' a b) {c : ℝ}
    (hac : a < c) (hcb : c ≤ b) (n : ℕ) :
    Secant.iterate f a c n ≤ Secant.iterate f a c (n + 1) ∧
      b - Secant.iterate f a c (n + 1) ≤
        (1 - f' b / secantSlope f f' b ((Secant.step f)^[n] (a, c))) *
          (b - Secant.iterate f a c n) ∧
      (1 - f' b / secantSlope f f' b ((Secant.step f)^[n] (a, c))) *
          (b - Secant.iterate f a c n) ≤ factor f' a b * (b - Secant.iterate f a c n) := by
  have hs := h.secant_state hac hcb n
  have hd := h.secantSlope_bounds hac hcb n
  have hb := h.step_bounds hs.2.1 hd.1 hd.2
  rw [Secant.iterate, Secant.iterate, Function.iterate_succ_apply', h.secant_step_eq]
  exact ⟨hb.1, hb.2.2⟩

/-- A geometric majorant for the secant errors, with the first two prescribed
points indexed as `a` and iterate zero `c`. -/
theorem Data.secantOrbit_error_le (h : Data f f' a b) {c : ℝ}
    (hac : a < c) (hcb : c ≤ b) (n : ℕ) :
    b - Secant.iterate f a c n ≤ factor f' a b ^ n * (b - c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := (h.secantOrbit_bounds hac hcb n).2.1.trans (h.secantOrbit_bounds hac hcb n).2.2
    calc _ ≤ factor f' a b * (b - Secant.iterate f a c n) := hs
         _ ≤ factor f' a b * (factor f' a b ^ n * (b - c)) :=
           mul_le_mul_of_nonneg_left ih h.factor_mem.1
         _ = _ := by ring

/-- The monotone secant orbit converges globally to the simple root. -/
theorem Data.tendsto_secantOrbit (h : Data f f' a b) {c : ℝ}
    (hac : a < c) (hcb : c ≤ b) :
    Tendsto (Secant.iterate f a c) atTop (𝓝 b) := by
  have hgeom := (tendsto_pow_atTop_nhds_zero_of_lt_one h.factor_mem.1 h.factor_mem.2).mul_const
    (b - c)
  have he : Tendsto (fun n => b - Secant.iterate f a c n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sub_nonneg.mpr (h.secant_state hac hcb n).2.1.2)
      (h.secantOrbit_error_le hac hcb)
    simpa only [zero_mul] using hgeom
  convert (tendsto_const_nhds (x := b)).sub he using 1
  · ext n
    ring
  · simp only [sub_zero]

/-- At any current point, a Lipschitz derivative on the remaining interval
gives a quadratic Newton error bound with a nonzero root derivative denominator. -/
theorem Data.newton_quadratic_bound (h : Data f f' a b) {x : ℝ} (hx : x ∈ Icc a b)
    {K : NNReal} (hlip : LipschitzOnWith K f' (Icc x b)) :
    b - Newton.scalarStep f f' x ≤ ((K : ℝ) / (-f' b)) * (b - x) ^ 2 := by
  rcases hx.2.eq_or_lt with rfl | hxb
  · simp [Newton.scalarStep, h.root]
  obtain ⟨ξ, hξ, heq⟩ := exists_hasDerivAt_eq_slope f f' hxb
    (fun y hy => (h.derivative y ⟨hx.1.trans hy.1, hy.2⟩).continuousAt.continuousWithinAt)
    (fun y hy => h.derivative y ⟨hx.1.trans hy.1.le, hy.2.le⟩)
  have hξmem : ξ ∈ Icc a b := ⟨hx.1.trans hξ.1.le, hξ.2.le⟩
  have hid : f x = f' ξ * (x - b) := by
    rw [heq, h.root]
    field_simp
    ring
  have hdiff : 0 ≤ f' ξ - f' x :=
    sub_nonneg.mpr (h.monotone_derivative hx hξmem hξ.1.le)
  have hd := hlip.dist_le_mul ξ (Ioo_subset_Icc_self hξ) x ⟨le_rfl, hx.2⟩
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg hdiff,
    abs_of_nonneg (sub_nonneg.mpr hξ.1.le)] at hd
  have hnum : (f' ξ - f' x) * (b - x) ≤ (K : ℝ) * (b - x) ^ 2 := by
    nlinarith [mul_nonneg K.coe_nonneg (sub_nonneg.mpr hξ.2.le)]
  have hden : -f' b ≤ -f' x := neg_le_neg
    (h.monotone_derivative hx ⟨h.le_root, le_rfl⟩ hx.2)
  have hbound := div_le_div₀ (by positivity : 0 ≤ (K : ℝ) * (b - x) ^ 2) hnum
    (neg_pos.mpr h.derivative_root_neg) hden
  rw [Newton.scalarStep, hid]
  convert hbound using 1
  · field_simp [(h.derivative_neg hx).ne]
    ring
  · ring

/-- Local Lipschitz continuity of the derivative strengthens the globally
convergent Newton orbit to an eventual Q-quadratic error estimate. -/
theorem Data.eventually_newton_quadratic (h : Data f f' a b) {K : NNReal} {r : ℝ}
    (hr : 0 < r) (hlip : LipschitzOnWith K f' (Metric.ball b r)) :
    ∀ᶠ n in atTop, b - newtonOrbit f f' a (n + 1) ≤
      ((K : ℝ) / (-f' b)) * (b - newtonOrbit f f' a n) ^ 2 := by
  have hnear := h.tendsto_newtonOrbit.eventually (Metric.ball_mem_nhds b hr)
  filter_upwards [hnear] with n hn
  have hsub : Icc (newtonOrbit f f' a n) b ⊆ Metric.ball b r :=
    (convex_ball b r).ordConnected.out hn (Metric.mem_ball_self hr)
  rw [newtonOrbit_succ]
  exact h.newton_quadratic_bound (h.newtonOrbit_mem n) (hlip.mono hsub)

/-- The actual secant slopes converge to the simple root derivative. -/
theorem Data.tendsto_secantSlope (h : Data f f' a b) {c : ℝ}
    (hac : a < c) (hcb : c ≤ b) :
    Tendsto (fun n => secantSlope f f' b ((Secant.step f)^[n] (a, c))) atTop (𝓝 (f' b)) := by
  classical
  have hrep (n : ℕ) : ∃ ξ : ℝ, ξ ∈ Icc a b ∧
      ((Secant.step f)^[n] (a, c)).1 ≤ ξ ∧ ξ ≤ b ∧
      secantSlope f f' b ((Secant.step f)^[n] (a, c)) = f' ξ := by
    let z := (Secant.step f)^[n] (a, c)
    have hs := h.secant_state hac hcb n
    change z.1 ∈ Icc a b ∧ z.2 ∈ Icc a b ∧ _ at hs
    change ∃ ξ, ξ ∈ Icc a b ∧ z.1 ≤ ξ ∧ ξ ≤ b ∧ secantSlope f f' b z = f' ξ
    by_cases hz : z.2 = b
    · exact ⟨b, ⟨h.le_root, le_rfl⟩, hs.1.2, le_rfl, by rw [secantSlope, ite_eq_left hz]⟩
    · obtain ⟨ξ, hξ, heq, _, _⟩ := h.secant_slope hs.1 hs.2.1 (hs.2.2.resolve_right hz)
      exact ⟨ξ, ⟨hs.1.1.trans hξ.1.le, hξ.2.le.trans hs.2.1.2⟩,
        hξ.1.le, hξ.2.le.trans hs.2.1.2, by rw [secantSlope, ite_eq_right hz, heq]⟩
  choose ξ hmem hlo hhi heq using hrep
  have hfirst : Tendsto (fun n => ((Secant.step f)^[n] (a, c)).1) atTop (𝓝 b) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Secant.fst_iterate_succ] using h.tendsto_secantOrbit hac hcb
  have hξ : Tendsto ξ atTop (𝓝 b) :=
    hfirst.squeeze tendsto_const_nhds hlo hhi
  have hder := (h.continuous_derivative b ⟨h.le_root, le_rfl⟩).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hξ, Eventually.of_forall hmem⟩)
  convert hder using 1
  ext n
  exact heq n

/-- Secant convergence is ultimately Q-superlinear, using zero error ratios
following finite termination. Only continuous differentiability is required. -/
theorem Data.tendsto_secant_error_ratio (h : Data f f' a b) {c : ℝ}
    (hac : a < c) (hcb : c ≤ b) :
    Tendsto (fun n => (b - Secant.iterate f a c (n + 1)) /
      (b - Secant.iterate f a c n)) atTop (𝓝 0) := by
  have hmult : Tendsto (fun n =>
      1 - f' b / secantSlope f f' b ((Secant.step f)^[n] (a, c))) atTop (𝓝 0) := by
    simpa only [Pi.div_apply, Pi.sub_apply, div_self h.derivative_root_neg.ne, sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_const_nhds (x := f' b)).div (h.tendsto_secantSlope hac hcb)
          h.derivative_root_neg.ne)
  have hrat (n : ℕ) : (b - Secant.iterate f a c (n + 1)) /
      (b - Secant.iterate f a c n) ≤
        1 - f' b / secantSlope f f' b ((Secant.step f)^[n] (a, c)) := by
    have hs := h.secant_state hac hcb n
    have hxn : Secant.iterate f a c n ≤ b := hs.2.1.2
    rcases hxn.eq_or_lt with heq | hlt
    · rw [heq, sub_self, div_zero]
      have hr : ((Secant.step f)^[n] (a, c)).2 = b := heq
      rw [secantSlope, ite_eq_left hr, div_self h.derivative_root_neg.ne, sub_self]
    · apply (div_le_iff₀ (sub_pos.mpr hlt)).mpr
      exact (h.secantOrbit_bounds hac hcb n).2.1
  exact squeeze_zero
    (fun n => div_nonneg (sub_nonneg.mpr (h.secant_state hac hcb (n + 1)).2.1.2)
      (sub_nonneg.mpr (h.secant_state hac hcb n).2.1.2)) hrat hmult

/-- All convergence and rate conclusions for the actual Newton and secant
updates. The secant indexing takes `a` as its first point and `c` as iterate zero. -/
structure Convergence (f f' : ℝ → ℝ) (a b : ℝ) : Prop where
  factor_mem : factor f' a b ∈ Ico (0 : ℝ) 1
  newton_mem : ∀ n, newtonOrbit f f' a n ∈ Icc a b
  newton_increasing : ∀ n, newtonOrbit f f' a n ≤ newtonOrbit f f' a (n + 1)
  newton_error : ∀ n, b - newtonOrbit f f' a (n + 1) ≤
    factor f' a b * (b - newtonOrbit f f' a n)
  newton_limit : Tendsto (newtonOrbit f f' a) atTop (𝓝 b)
  newton_superlinear : Tendsto (fun n => (b - newtonOrbit f f' a (n + 1)) /
    (b - newtonOrbit f f' a n)) atTop (𝓝 0)
  newton_quadratic : ∀ (K : NNReal) (r : ℝ), 0 < r →
    LipschitzOnWith K f' (Metric.ball b r) →
      ∀ᶠ n in atTop, b - newtonOrbit f f' a (n + 1) ≤
        ((K : ℝ) / |f' b|) * (b - newtonOrbit f f' a n) ^ 2
  secant_mem : ∀ c, a < c → c ≤ b → ∀ n, Secant.iterate f a c n ∈ Icc a b
  secant_increasing : ∀ c, a < c → c ≤ b → ∀ n,
    Secant.iterate f a c n ≤ Secant.iterate f a c (n + 1)
  secant_error : ∀ c, a < c → c ≤ b → ∀ n,
    b - Secant.iterate f a c (n + 1) ≤ factor f' a b * (b - Secant.iterate f a c n)
  secant_limit : ∀ c, a < c → c ≤ b → Tendsto (Secant.iterate f a c) atTop (𝓝 b)
  secant_superlinear : ∀ c, a < c → c ≤ b →
    Tendsto (fun n => (b - Secant.iterate f a c (n + 1)) /
      (b - Secant.iterate f a c n)) atTop (𝓝 0)

/-- Continuous monotone derivative data imply all global and ultimate rates. -/
theorem Data.convergence (h : Data f f' a b) : Convergence f f' a b where
  factor_mem := h.factor_mem
  newton_mem := h.newtonOrbit_mem
  newton_increasing n := (h.newtonOrbit_bounds n).1
  newton_error n := (h.newtonOrbit_bounds n).2.1.trans (h.newtonOrbit_bounds n).2.2
  newton_limit := h.tendsto_newtonOrbit
  newton_superlinear := h.tendsto_newton_error_ratio
  newton_quadratic K r hr hlip := by
    simpa only [abs_of_neg h.derivative_root_neg] using h.eventually_newton_quadratic hr hlip
  secant_mem c hac hcb n := (h.secant_state hac hcb n).2.1
  secant_increasing c hac hcb n := (h.secantOrbit_bounds hac hcb n).1
  secant_error c hac hcb n :=
    (h.secantOrbit_bounds hac hcb n).2.1.trans (h.secantOrbit_bounds hac hcb n).2.2
  secant_limit c hac hcb := h.tendsto_secantOrbit hac hcb
  secant_superlinear c hac hcb := h.tendsto_secant_error_ratio hac hcb

/-- Convexity supplies the monotonicity of the actual derivative. -/
theorem Data.of_convex (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hc : ContinuousOn f' (Icc a b)) (hconv : ConvexOn ℝ (Icc a b) f)
    (hroot : f b = 0) (hneg : f' b < 0) : Data f f' a b where
  le_root := hab
  derivative := hf
  continuous_derivative := hc
  monotone_derivative := by
    intro x hx y hy hxy
    have hm := hconv.monotoneOn_deriv (fun z hz => (hf z hz).differentiableAt) hx hy hxy
    rwa [(hf x hx).deriv, (hf y hy).deriv] at hm
  root := hroot
  derivative_root_neg := hneg

/-- Negating a scalar objective and its actual derivative leaves a Newton step unchanged. -/
theorem newtonStep_neg (f f' : ℝ → ℝ) :
    Newton.scalarStep (-f) (-f') = Newton.scalarStep f f' := by
  funext x
  simp only [Newton.scalarStep, Pi.neg_apply, neg_div_neg_eq]

/-- Newton orbits are invariant under simultaneous negation. -/
@[simp] theorem newtonOrbit_neg (f f' : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    newtonOrbit (-f) (-f') a n = newtonOrbit f f' a n := by
  simp only [newtonOrbit, newtonStep_neg]

/-- Negating the scalar objective leaves every actual secant update unchanged. -/
theorem secantStep_neg (f : ℝ → ℝ) : Secant.step (-f) = Secant.step f := by
  funext z
  apply Prod.ext
  · rfl
  · change z.2 - (z.2 - z.1) / (-f z.2 - (-f z.1)) * (-f z.2) =
      z.2 - (z.2 - z.1) / (f z.2 - f z.1) * f z.2
    rw [show -f z.2 - (-f z.1) = -(f z.2 - f z.1) by ring, div_neg]
    ring

/-- Secant orbits are invariant under negation. -/
@[simp] theorem secantOrbit_neg (f : ℝ → ℝ) (a c : ℝ) (n : ℕ) :
    Secant.iterate (-f) a c n = Secant.iterate f a c n := by
  simp only [Secant.iterate, secantStep_neg]

/-- The source's uniform derivative-ratio factor is invariant under negation. -/
@[simp] theorem factor_neg (f' : ℝ → ℝ) (a b : ℝ) : factor (-f') a b = factor f' a b := by
  simp only [factor, Pi.neg_apply, neg_div_neg_eq]

/-- All convergence conclusions transfer back from a negated objective. -/
theorem Convergence.of_neg (h : Convergence (-f) (-f') a b) : Convergence f f' a b where
  factor_mem := by simpa only [factor_neg] using h.factor_mem
  newton_mem n := by simpa only [newtonOrbit_neg] using h.newton_mem n
  newton_increasing n := by simpa only [newtonOrbit_neg] using h.newton_increasing n
  newton_error n := by simpa only [factor_neg, newtonOrbit_neg] using h.newton_error n
  newton_limit := by
    convert h.newton_limit using 1
    ext n
    exact (newtonOrbit_neg f f' a n).symm
  newton_superlinear := by simpa only [newtonOrbit_neg] using h.newton_superlinear
  newton_quadratic K r hr hlip := by
    have hneg : LipschitzOnWith K (-f') (Metric.ball b r) := hlip.neg
    simpa only [newtonOrbit_neg, Pi.neg_apply, abs_neg] using h.newton_quadratic K r hr hneg
  secant_mem c hac hcb n := by simpa only [secantOrbit_neg] using h.secant_mem c hac hcb n
  secant_increasing c hac hcb n := by
    simpa only [secantOrbit_neg] using h.secant_increasing c hac hcb n
  secant_error c hac hcb n := by
    simpa only [secantOrbit_neg, factor_neg] using h.secant_error c hac hcb n
  secant_limit c hac hcb := by
    convert h.secant_limit c hac hcb using 1
    ext n
    exact (secantOrbit_neg f a c n).symm
  secant_superlinear c hac hcb := by
    simpa only [secantOrbit_neg] using h.secant_superlinear c hac hcb

/-- The convex decreasing and concave increasing cases give identical rates.
The root derivative must be nonzero for ultimate superlinear convergence. -/
theorem convergence_of_convex_or_concave (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hc : ContinuousOn f' (Icc a b)) (hroot : f b = 0)
    (hshape : (ConvexOn ℝ (Icc a b) f ∧ f' b < 0) ∨
      (ConcaveOn ℝ (Icc a b) f ∧ 0 < f' b)) : Convergence f f' a b := by
  rcases hshape with ⟨hconv, hneg⟩ | ⟨hconc, hpos⟩
  · exact (Data.of_convex hab hf hc hconv hroot hneg).convergence
  · have hneg : Data (-f) (-f') a b := Data.of_convex hab
      (fun x hx => (hf x hx).neg) hc.neg hconc.neg (by simpa using hroot)
      (by simpa using neg_neg_of_pos hpos)
    exact hneg.convergence.of_neg

end MonotoneRoot
