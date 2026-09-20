import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Strict convexity of a normed space from strict convexity of a power of the norm

A real normed space is a `StrictConvexSpace ℝ V` as soon as some power `‖·‖ ^ p`, `p ≥ 1`, is a
strictly convex function on `V`: `StrictConvexSpace.of_strictConvexOn_norm_rpow`. This is the form
in which the hypothesis appears in the uniqueness theorem for best approximations from a convex set
of [han2009theoretical], whose conclusion is Mathlib's `StrictConvexSpace ℝ V` here.

On an inner product space the hypothesis holds with `p = 2`: `strictConvexOn_norm_sq`, in the
natural-power form, and `strictConvexOn_norm_rpow_two` in the real-power form the criterion above
consumes. The proof is the identity `a ‖x‖² + b ‖y‖² - ‖a x + b y‖² = a b ‖x - y‖²` for `a + b = 1`,
a form of the parallelogram law.
-/

section Rpow

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **`‖·‖^p` is strictly convex on a strictly convex space** for `p > 1`: for `x ≠ y` either
`‖x‖ ≠ ‖y‖` and the strict convexity of `t ↦ t^p` on `[0, ∞)` applies after the triangle
inequality, or `‖x‖ = ‖y‖ = r` and `‖a x + b y‖ < r` by strict convexity of the space. -/
theorem strictConvexOn_norm_rpow [StrictConvexSpace ℝ V] {p : ℝ} (hp : 1 < p) :
    StrictConvexOn ℝ Set.univ fun x : V ↦ ‖x‖ ^ p := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab ↦ ?_⟩
  have hp0 : 0 < p := by linarith
  have htri : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha.le, Real.norm_of_nonneg hb.le]
  simp only [smul_eq_mul]
  rcases eq_or_ne ‖x‖ ‖y‖ with hn | hn
  · -- equal norms: the combination is strictly shorter
    have hr : 0 < ‖x‖ := by
      rcases (norm_nonneg x).lt_or_eq with h | h
      · exact h
      · exfalso
        have hx0 : x = 0 := norm_eq_zero.1 h.symm
        have hy0 : y = 0 := norm_eq_zero.1 (hn ▸ h.symm)
        exact hxy (hx0.trans hy0.symm)
    have hlt : ‖a • x + b • y‖ < ‖x‖ := norm_combo_lt_of_ne le_rfl hn.symm.le hxy ha hb hab
    calc ‖a • x + b • y‖ ^ p < ‖x‖ ^ p := Real.rpow_lt_rpow (norm_nonneg _) hlt hp0
      _ = a * ‖x‖ ^ p + b * ‖y‖ ^ p := by rw [← hn, ← add_mul, hab, one_mul]
  · -- distinct norms: strict convexity of `t ↦ t^p`
    have hstrict := (strictConvexOn_rpow hp).2 (Set.mem_Ici.2 (norm_nonneg x))
      (Set.mem_Ici.2 (norm_nonneg y)) hn ha hb hab
    simp only [smul_eq_mul] at hstrict
    calc ‖a • x + b • y‖ ^ p ≤ (a * ‖x‖ + b * ‖y‖) ^ p :=
          Real.rpow_le_rpow (norm_nonneg _) htri hp0.le
      _ < a * ‖x‖ ^ p + b * ‖y‖ ^ p := hstrict

/-- If `fun v => ‖v‖ ^ p` is strictly convex on all of `V` for some real `p ≥ 1`, then `V` is a
strictly convex space.  Indeed for distinct unit vectors `x`, `y` strict convexity at the midpoint
gives `‖(x + y) / 2‖ ^ p < 1`, whence `‖(x + y) / 2‖ < 1` because `t ↦ t ^ p` is monotone. -/
theorem StrictConvexSpace.of_strictConvexOn_norm_rpow {p : ℝ} (hp : 1 ≤ p)
    (hconv : StrictConvexOn ℝ (Set.univ : Set V) fun v : V => ‖v‖ ^ p) :
    StrictConvexSpace ℝ V := by
  refine StrictConvexSpace.of_norm_combo_lt_one fun x y hx hy hne => ?_
  refine ⟨1 / 2, 1 / 2, by norm_num, ?_⟩
  have h := hconv.2 (Set.mem_univ x) (Set.mem_univ y) hne (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  simp only [hx, hy, Real.one_rpow, smul_eq_mul] at h
  by_contra hge
  rw [not_lt] at hge
  have hmono : (1 : ℝ) ^ p ≤ ‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y‖ ^ p :=
    Real.rpow_le_rpow zero_le_one hge (by linarith)
  rw [Real.one_rpow] at hmono
  linarith

end Rpow

section InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- On a real inner product space the squared norm is a strictly convex function, because `a ‖x‖² +
b ‖y‖² - ‖a x + b y‖² = a b ‖x - y‖²` whenever `a + b = 1`. -/
theorem strictConvexOn_norm_sq : StrictConvexOn ℝ (Set.univ : Set H) fun v : H => ‖v‖ ^ 2 := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have hexp : ‖a • x + b • y‖ ^ 2
      = a ^ 2 * ‖x‖ ^ 2 + 2 * (a * b) * inner ℝ x y + b ^ 2 * ‖y‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb]
    ring
  have hdiff : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := norm_sub_sq_real x y
  have hpos : 0 < a * b * ‖x - y‖ ^ 2 := by
    have hne : x - y ≠ 0 := sub_ne_zero.2 hxy
    have : 0 < ‖x - y‖ := norm_pos_iff.2 hne
    positivity
  have hkey : a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 - ‖a • x + b • y‖ ^ 2 = a * b * ‖x - y‖ ^ 2 := by
    have hb' : b = 1 - a := by linarith
    rw [hexp, hdiff, hb']
    ring
  simp only [smul_eq_mul]
  linarith

/-- `strictConvexOn_norm_sq` in the real-power form, the shape
`StrictConvexSpace.of_strictConvexOn_norm_rpow` consumes. -/
theorem strictConvexOn_norm_rpow_two :
    StrictConvexOn ℝ (Set.univ : Set H) fun v : H => ‖v‖ ^ (2 : ℝ) := by
  simpa only [Real.rpow_two] using (strictConvexOn_norm_sq (H := H))

/-- A real inner product space is a strictly convex space.  Mathlib reaches this by another route
(uniform convexity); it is recorded here only as the first instance of the criterion
`StrictConvexSpace.of_strictConvexOn_norm_rpow`. -/
example : StrictConvexSpace ℝ H :=
  StrictConvexSpace.of_strictConvexOn_norm_rpow one_le_two strictConvexOn_norm_rpow_two

end InnerProduct
