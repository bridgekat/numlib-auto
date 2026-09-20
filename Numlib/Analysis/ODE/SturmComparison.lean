/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.ODE.SturmComparison`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Sturm comparison theorem

For two second-order equations `u'' + q u = 0` and `v'' + Q v = 0` on an interval with `q ≤ Q`,
the zeros of `v` are at least as dense as those of `u`: between two consecutive zeros of `u` there
is a zero of `v`. This is **Sturm's comparison theorem**. The proof is the Wronskian identity
`(u v' − u' v)' = (q − Q) u v` (`IsSturmSolutionOn.hasDerivAt_wronskian`): with `u, v > 0` on
`(a, b)` and `u(a) = u(b) = 0` the Wronskian `W = u v' − u' v` is nonincreasing on `[a, b]`, while
`W(a) = −u'(a) v(a) ≤ 0 ≤ −u'(b) v(b) = W(b)` because `u'(a) ≥ 0 ≥ u'(b)` at the zeros of a
positive function. When `q < Q` on `(a, b)` the Wronskian is *strictly* decreasing and this is a
contradiction without any further hypothesis (`IsSturmSolutionOn.exists_zero_Ioo_of_lt`, the zero
of `v` lies in the open interval); when only `q ≤ Q`, the hypothesis `u'(a) ≠ 0` makes `W(a) < 0`
and the zero of `v` is found in the closed interval (`IsSturmSolutionOn.exists_zero_Icc_of_le`).
No uniqueness theorem for the equation is used: the statements are about any two functions with
the stated second derivatives, given as `HasDerivAt` hypotheses in first-order form.

Comparison with `sin (m (x − a))`, which solves `u'' + m² u = 0` with consecutive zeros `a` and
`a + π/m`, gives the two classical corollaries: if `q ≥ m² > 0` then every solution of
`u'' + q u = 0` has a zero in every closed interval of length `π/m`
(`IsSturmSolutionOn.exists_zero_Icc_of_sq_le`; in the open interval when `q > m²`,
`IsSturmSolutionOn.exists_zero_Ioo_of_sq_lt`), and if `q ≤ M²` then consecutive zeros are at least
`π/M` apart (`IsSturmSolutionOn.div_le_sub_of_le_sq`, from the strict theorem applied to a slightly
faster sine, so that again no uniqueness is needed).

## Main definitions and results

* `IsSturmSolutionOn q u du s` — `u' = du` and `du' = −q u` at every point of `s`.
* `IsSturmSolutionOn.hasDerivAt_wronskian` — `(u v' − u' v)' = (q − Q) u v`.
* `IsSturmSolutionOn.exists_zero_Ioo_of_lt` — Sturm comparison, strict form.
* `IsSturmSolutionOn.exists_zero_Icc_of_le` — Sturm comparison, `q ≤ Q` and `u'(a) ≠ 0`.
* `IsSturmSolutionOn.exists_zero_Icc_of_sq_le`, `IsSturmSolutionOn.exists_zero_Ioo_of_sq_lt` —
  `q ≥ m²` forces a zero in every interval of length `π/m`.
* `IsSturmSolutionOn.div_le_sub_of_le_sq` — `q ≤ M²` keeps consecutive zeros `π/M` apart.

## References

Hartman, *Ordinary Differential Equations*, Chapter XI, Theorem 3.1; Szegő, *Orthogonal
Polynomials*, §1.82.
-/

open Set Filter Topology

/-- `IsSturmSolutionOn q u du s` says that `u` solves the second-order equation `u'' + q u = 0`
on `s` in first-order form: `u' = du` and `du' = −q u` at every point of `s`. -/
structure IsSturmSolutionOn (q u du : ℝ → ℝ) (s : Set ℝ) : Prop where
  /-- `u' = du` on `s`. -/
  hasDerivAt : ∀ x ∈ s, HasDerivAt u (du x) x
  /-- `du' = −q u` on `s`. -/
  hasDerivAt_deriv : ∀ x ∈ s, HasDerivAt du (-(q x * u x)) x

/-! ### Sign lemmas at the endpoints -/

/-- A function vanishing at `a`, differentiable there and positive on `(a, b)` has a
nonnegative derivative at `a`. -/
theorem HasDerivAt.nonneg_of_pos_Ioo {u : ℝ → ℝ} {du a b : ℝ} (hab : a < b)
    (hu : HasDerivAt u du a) (ha : u a = 0) (hpos : ∀ x ∈ Ioo a b, 0 < u x) : 0 ≤ du := by
  refine ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.1 hu).2 ?_
  filter_upwards [Ioo_mem_nhdsGT hab] with x hx
  rw [slope_def_field, ha, sub_zero]
  exact div_nonneg (hpos x hx).le (by linarith [hx.1])

/-- A function vanishing at `b`, differentiable there and positive on `(a, b)` has a
nonpositive derivative at `b`. -/
theorem HasDerivAt.nonpos_of_pos_Ioo {u : ℝ → ℝ} {du a b : ℝ} (hab : a < b)
    (hu : HasDerivAt u du b) (hb : u b = 0) (hpos : ∀ x ∈ Ioo a b, 0 < u x) : du ≤ 0 := by
  refine le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.1 hu).1 ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with x hx
  rw [slope_def_field, hb, sub_zero]
  exact div_nonpos_of_nonneg_of_nonpos (hpos x hx).le (by linarith [hx.2])

/-- A function continuous at `a` and positive on `(a, b)` is nonnegative at `a`. -/
theorem ContinuousAt.nonneg_of_pos_Ioo_left {v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hv : ContinuousAt v a) (hpos : ∀ x ∈ Ioo a b, 0 < v x) : 0 ≤ v a := by
  have := left_nhdsWithin_Ioo_neBot hab
  exact ge_of_tendsto (hv.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun x hx => (hpos x hx).le)

/-- A function continuous at `b` and positive on `(a, b)` is nonnegative at `b`. -/
theorem ContinuousAt.nonneg_of_pos_Ioo_right {v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hv : ContinuousAt v b) (hpos : ∀ x ∈ Ioo a b, 0 < v x) : 0 ≤ v b := by
  have := right_nhdsWithin_Ioo_neBot hab
  exact ge_of_tendsto (hv.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun x hx => (hpos x hx).le)

/-- A continuous function without zeros on a preconnected set has constant sign there. -/
theorem IsPreconnected.forall_pos_or_forall_neg {v : ℝ → ℝ} {s : Set ℝ} (hs : IsPreconnected s)
    (hv : ContinuousOn v s) (h0 : ∀ x ∈ s, v x ≠ 0) :
    (∀ x ∈ s, 0 < v x) ∨ (∀ x ∈ s, v x < 0) := by
  by_contra h
  push Not at h
  obtain ⟨⟨x, hx, hvx⟩, ⟨y, hy, hvy⟩⟩ := h
  have hvx' : v x < 0 := lt_of_le_of_ne hvx (h0 x hx)
  have hvy' : 0 < v y := lt_of_le_of_ne hvy (h0 y hy).symm
  obtain ⟨z, hz, hvz⟩ := hs.intermediate_value hx hy hv ⟨hvx'.le, hvy'.le⟩
  exact h0 z hz hvz

namespace IsSturmSolutionOn

variable {q u du : ℝ → ℝ} {s : Set ℝ}

/-- A solution on `s` is a solution on every subset. -/
theorem mono (h : IsSturmSolutionOn q u du s) {t : Set ℝ} (hts : t ⊆ s) :
    IsSturmSolutionOn q u du t :=
  ⟨fun x hx => h.hasDerivAt x (hts hx), fun x hx => h.hasDerivAt_deriv x (hts hx)⟩

/-- `−u` solves the same equation. -/
theorem neg (h : IsSturmSolutionOn q u du s) : IsSturmSolutionOn q (-u) (-du) s :=
  ⟨fun x hx => (h.hasDerivAt x hx).neg,
    fun x hx => (h.hasDerivAt_deriv x hx).neg.congr_deriv (by simp only [Pi.neg_apply, mul_neg])⟩

/-- A solution is continuous on `s`. -/
theorem continuousOn (h : IsSturmSolutionOn q u du s) : ContinuousOn u s :=
  fun x hx => (h.hasDerivAt x hx).continuousAt.continuousWithinAt

/-- The derivative of a solution is continuous on `s`. -/
theorem continuousOn_deriv (h : IsSturmSolutionOn q u du s) : ContinuousOn du s :=
  fun x hx => (h.hasDerivAt_deriv x hx).continuousAt.continuousWithinAt

/-- **The Wronskian identity**: for solutions of `u'' + q u = 0` and `v'' + Q v = 0`,
`(u v' − u' v)' = (q − Q) u v`. -/
theorem hasDerivAt_wronskian {Q v dv : ℝ → ℝ} (hu : IsSturmSolutionOn q u du s)
    (hv : IsSturmSolutionOn Q v dv s) {x : ℝ} (hx : x ∈ s) :
    HasDerivAt (fun y => u y * dv y - du y * v y) ((q x - Q x) * (u x * v x)) x :=
  (((hu.hasDerivAt x hx).mul (hv.hasDerivAt_deriv x hx)).sub
    ((hu.hasDerivAt_deriv x hx).mul (hv.hasDerivAt x hx))).congr_deriv (by ring)

/-- **The Wronskian is nonincreasing** when `q ≤ Q` and `u v ≥ 0` on `(a, b)`. -/
theorem wronskian_apply_le {Q v dv : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hv : IsSturmSolutionOn Q v dv (Icc a b))
    (hqQ : ∀ x ∈ Ioo a b, q x ≤ Q x) (huv : ∀ x ∈ Ioo a b, 0 ≤ u x * v x) :
    u b * dv b - du b * v b ≤ u a * dv a - du a * v a := by
  have hW : ∀ x ∈ Icc a b,
      HasDerivAt (fun y => u y * dv y - du y * v y) ((q x - Q x) * (u x * v x)) x :=
    fun x hx => hu.hasDerivAt_wronskian hv hx
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (fun x hx => (hW x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hW x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => ?_) (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  rw [interior_Icc] at hx
  rw [(hW x (Ioo_subset_Icc_self hx)).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hqQ x hx]) (huv x hx)

/-- **The Wronskian is strictly decreasing** when `q < Q` and `u v > 0` on `(a, b)`. -/
theorem wronskian_apply_lt {Q v dv : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hv : IsSturmSolutionOn Q v dv (Icc a b))
    (hqQ : ∀ x ∈ Ioo a b, q x < Q x) (huv : ∀ x ∈ Ioo a b, 0 < u x * v x) :
    u b * dv b - du b * v b < u a * dv a - du a * v a := by
  have hW : ∀ x ∈ Icc a b,
      HasDerivAt (fun y => u y * dv y - du y * v y) ((q x - Q x) * (u x * v x)) x :=
    fun x hx => hu.hasDerivAt_wronskian hv hx
  refine strictAntiOn_of_deriv_neg (convex_Icc a b)
    (fun x hx => (hW x hx).continuousAt.continuousWithinAt)
    (fun x hx => ?_) (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab
  rw [interior_Icc] at hx
  rw [(hW x (Ioo_subset_Icc_self hx)).deriv]
  exact mul_neg_of_neg_of_pos (by linarith [hqQ x hx]) (huv x hx)

/-- The strict comparison in the positive case: `u, v > 0` on `(a, b)`, `u(a) = u(b) = 0` and
`q < Q` on `(a, b)` are contradictory. -/
private theorem not_pos_of_lt {Q v dv : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hv : IsSturmSolutionOn Q v dv (Icc a b))
    (hqQ : ∀ x ∈ Ioo a b, q x < Q x) (hua : u a = 0) (hub : u b = 0)
    (hupos : ∀ x ∈ Ioo a b, 0 < u x) (hvpos : ∀ x ∈ Ioo a b, 0 < v x) : False := by
  have hW := hu.wronskian_apply_lt hab hv hqQ fun x hx => mul_pos (hupos x hx) (hvpos x hx)
  have hdua : 0 ≤ du a :=
    (hu.hasDerivAt a (left_mem_Icc.2 hab.le)).nonneg_of_pos_Ioo hab hua hupos
  have hdub : du b ≤ 0 :=
    (hu.hasDerivAt b (right_mem_Icc.2 hab.le)).nonpos_of_pos_Ioo hab hub hupos
  have hva : 0 ≤ v a :=
    (hv.hasDerivAt a (left_mem_Icc.2 hab.le)).continuousAt.nonneg_of_pos_Ioo_left hab hvpos
  have hvb : 0 ≤ v b :=
    (hv.hasDerivAt b (right_mem_Icc.2 hab.le)).continuousAt.nonneg_of_pos_Ioo_right hab hvpos
  rw [hua, hub, zero_mul, zero_mul, zero_sub, zero_sub, neg_lt_neg_iff] at hW
  nlinarith [mul_nonneg hdua hva, mul_nonpos_of_nonpos_of_nonneg hdub hvb]

/-- **Sturm's comparison theorem, strict form.** Let `u'' + q u = 0` and `v'' + Q v = 0` on
`[a, b]` with `q < Q` on `(a, b)`. If `a < b` are consecutive zeros of `u` (`u` does not vanish
on `(a, b)`), then `v` has a zero in the open interval `(a, b)`. -/
theorem exists_zero_Ioo_of_lt {Q v dv : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hv : IsSturmSolutionOn Q v dv (Icc a b))
    (hqQ : ∀ x ∈ Ioo a b, q x < Q x) (hua : u a = 0) (hub : u b = 0)
    (hu0 : ∀ x ∈ Ioo a b, u x ≠ 0) : ∃ x ∈ Ioo a b, v x = 0 := by
  by_contra hne
  push Not at hne
  have hus := isPreconnected_Ioo.forall_pos_or_forall_neg
    (hu.continuousOn.mono Ioo_subset_Icc_self) hu0
  have hvs := isPreconnected_Ioo.forall_pos_or_forall_neg
    (hv.continuousOn.mono Ioo_subset_Icc_self) hne
  have hua' : (-u) a = 0 := by simp [hua]
  have hub' : (-u) b = 0 := by simp [hub]
  rcases hus with hupos | huneg <;> rcases hvs with hvpos | hvneg
  · exact not_pos_of_lt hab hu hv hqQ hua hub hupos hvpos
  · exact not_pos_of_lt hab hu hv.neg hqQ hua hub hupos
      fun x hx => by simpa using hvneg x hx
  · exact not_pos_of_lt hab hu.neg hv hqQ hua' hub' (fun x hx => by simpa using huneg x hx) hvpos
  · exact not_pos_of_lt hab hu.neg hv.neg hqQ hua' hub' (fun x hx => by simpa using huneg x hx)
      fun x hx => by simpa using hvneg x hx

/-- The non-strict comparison in the positive case: `u > 0` on `(a, b)`, `v > 0` on `[a, b]`,
`u(a) = u(b) = 0`, `u'(a) ≠ 0` and `q ≤ Q` on `(a, b)` are contradictory. -/
private theorem not_pos_of_le {Q v dv : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hv : IsSturmSolutionOn Q v dv (Icc a b))
    (hqQ : ∀ x ∈ Ioo a b, q x ≤ Q x) (hua : u a = 0) (hub : u b = 0) (hdua : du a ≠ 0)
    (hupos : ∀ x ∈ Ioo a b, 0 < u x) (hvpos : ∀ x ∈ Icc a b, 0 < v x) : False := by
  have hW := hu.wronskian_apply_le hab.le hv hqQ fun x hx =>
    (mul_pos (hupos x hx) (hvpos x (Ioo_subset_Icc_self hx))).le
  have hdua' : 0 ≤ du a :=
    (hu.hasDerivAt a (left_mem_Icc.2 hab.le)).nonneg_of_pos_Ioo hab hua hupos
  have hdub : du b ≤ 0 :=
    (hu.hasDerivAt b (right_mem_Icc.2 hab.le)).nonpos_of_pos_Ioo hab hub hupos
  have hva : 0 < v a := hvpos a (left_mem_Icc.2 hab.le)
  have hvb : 0 < v b := hvpos b (right_mem_Icc.2 hab.le)
  have hdua'' : 0 < du a := lt_of_le_of_ne hdua' (Ne.symm hdua)
  rw [hua, hub, zero_mul, zero_mul, zero_sub, zero_sub, neg_le_neg_iff] at hW
  nlinarith [mul_pos hdua'' hva, mul_nonpos_of_nonpos_of_nonneg hdub hvb.le]

/-- **Sturm's comparison theorem.** Let `u'' + q u = 0` and `v'' + Q v = 0` on `[a, b]` with
`q ≤ Q` on `(a, b)`. If `a < b` are consecutive zeros of `u` (`u` does not vanish on `(a, b)`)
and `u'(a) ≠ 0`, then `v` has a zero in `[a, b]`. The derivative hypothesis replaces the uniqueness
theorem for the equation (a solution with `u(a) = u'(a) = 0` would vanish identically); it holds
for every explicit comparison function such as `sin (m (x − a))`. -/
theorem exists_zero_Icc_of_le {Q v dv : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hv : IsSturmSolutionOn Q v dv (Icc a b))
    (hqQ : ∀ x ∈ Ioo a b, q x ≤ Q x) (hua : u a = 0) (hub : u b = 0)
    (hu0 : ∀ x ∈ Ioo a b, u x ≠ 0) (hdua : du a ≠ 0) : ∃ x ∈ Icc a b, v x = 0 := by
  by_contra hne
  push Not at hne
  have hus := isPreconnected_Ioo.forall_pos_or_forall_neg
    (hu.continuousOn.mono Ioo_subset_Icc_self) hu0
  have hvs := isPreconnected_Icc.forall_pos_or_forall_neg hv.continuousOn hne
  have hua' : (-u) a = 0 := by simp [hua]
  have hub' : (-u) b = 0 := by simp [hub]
  have hdua' : (-du) a ≠ 0 := by simpa using hdua
  rcases hus with hupos | huneg <;> rcases hvs with hvpos | hvneg
  · exact not_pos_of_le hab hu hv hqQ hua hub hdua hupos hvpos
  · exact not_pos_of_le hab hu hv.neg hqQ hua hub hdua hupos
      fun x hx => by simpa using hvneg x hx
  · exact not_pos_of_le hab hu.neg hv hqQ hua' hub' hdua'
      (fun x hx => by simpa using huneg x hx) hvpos
  · exact not_pos_of_le hab hu.neg hv.neg hqQ hua' hub' hdua'
      (fun x hx => by simpa using huneg x hx) fun x hx => by simpa using hvneg x hx

end IsSturmSolutionOn

/-! ### Comparison with the sine -/

open Real in
/-- `sin (m x + c)` solves `u'' + m² u = 0`. -/
theorem isSturmSolutionOn_sin (m c : ℝ) :
    IsSturmSolutionOn (fun _ => m ^ 2) (fun x => sin (m * x + c))
      (fun x => m * cos (m * x + c)) univ := by
  have hl : ∀ x : ℝ, HasDerivAt (fun x => m * x + c) m x := fun x => by
    simpa using ((hasDerivAt_id x).const_mul m).add_const c
  refine ⟨fun x _ => ?_, fun x _ => ?_⟩
  · exact ((Real.hasDerivAt_sin _).comp x (hl x)).congr_deriv (by ring)
  · exact (((Real.hasDerivAt_cos _).comp x (hl x)).const_mul m).congr_deriv (by ring)

namespace IsSturmSolutionOn

open Real

variable {q u du : ℝ → ℝ}

/-- **Every solution of `u'' + q u = 0` with `q ≥ m² > 0` has a zero in every closed interval of
length `π/m`**: comparison with `sin (m (x − a))`, whose consecutive zeros are `a` and
`a + π/m`. -/
theorem exists_zero_Icc_of_sq_le {a b m : ℝ} (hm : 0 < m) (hab : π / m ≤ b - a)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hq : ∀ x ∈ Icc a b, m ^ 2 ≤ q x) :
    ∃ x ∈ Icc a b, u x = 0 := by
  have hπ : 0 < π / m := div_pos pi_pos hm
  have hc : a + π / m ≤ b := by linarith
  have hsub : Icc a (a + π / m) ⊆ Icc a b := Icc_subset_Icc le_rfl hc
  have hsin : ∀ x ∈ Ioo a (a + π / m), sin (m * x + -(m * a)) ≠ 0 := by
    intro x hx
    refine (sin_pos_of_pos_of_lt_pi ?_ ?_).ne'
    · nlinarith [hx.1]
    · have : m * x < m * (a + π / m) := mul_lt_mul_of_pos_left hx.2 hm
      rw [mul_add, mul_div_cancel₀ _ hm.ne'] at this
      linarith
  obtain ⟨x, hx, hux⟩ := (isSturmSolutionOn_sin m (-(m * a))).mono (subset_univ _)
    |>.exists_zero_Icc_of_le (Q := q) (v := u) (dv := du) (by linarith) (hu.mono hsub)
      (fun x hx => hq x (hsub (Ioo_subset_Icc_self hx)))
      (by simp) (by rw [show m * (a + π / m) + -(m * a) = π by field_simp; ring]; exact sin_pi)
      hsin (by simp [hm.ne'])
  exact ⟨x, hsub hx, hux⟩

/-- **Every solution of `u'' + q u = 0` with `q > m² > 0` on `(a, b)` has a zero in the open
interval `(a, b)` when `b − a ≥ π/m`**: the strict comparison with `sin (m (x − a))`. -/
theorem exists_zero_Ioo_of_sq_lt {a b m : ℝ} (hm : 0 < m) (hab : π / m ≤ b - a)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hq : ∀ x ∈ Ioo a b, m ^ 2 < q x) :
    ∃ x ∈ Ioo a b, u x = 0 := by
  have hπ : 0 < π / m := div_pos pi_pos hm
  have hc : a + π / m ≤ b := by linarith
  have hsub : Icc a (a + π / m) ⊆ Icc a b := Icc_subset_Icc le_rfl hc
  have hsub' : Ioo a (a + π / m) ⊆ Ioo a b := Ioo_subset_Ioo le_rfl hc
  have hsin : ∀ x ∈ Ioo a (a + π / m), sin (m * x + -(m * a)) ≠ 0 := by
    intro x hx
    refine (sin_pos_of_pos_of_lt_pi ?_ ?_).ne'
    · nlinarith [hx.1]
    · have : m * x < m * (a + π / m) := mul_lt_mul_of_pos_left hx.2 hm
      rw [mul_add, mul_div_cancel₀ _ hm.ne'] at this
      linarith
  obtain ⟨x, hx, hux⟩ := (isSturmSolutionOn_sin m (-(m * a))).mono (subset_univ _)
    |>.exists_zero_Ioo_of_lt (Q := q) (v := u) (dv := du) (by linarith) (hu.mono hsub)
      (fun x hx => hq x (hsub' hx))
      (by simp) (by rw [show m * (a + π / m) + -(m * a) = π by field_simp; ring]; exact sin_pi)
      hsin
  exact ⟨x, hsub' hx, hux⟩

/-- **Consecutive zeros of a solution of `u'' + q u = 0` with `q ≤ M²` are at least `π/M`
apart.** If `b − a < π/M`, a sine `sin (M' (x − a) + δ)` with `M < M'`, `M'(b − a) < π` and a
small phase `δ > 0` is positive on `[a, b]` and solves `w'' + M'² w = 0` with `M'² > q`, which
the strict comparison theorem forbids. -/
theorem div_le_sub_of_le_sq {a b M : ℝ} (hM : 0 < M) (hab : a < b)
    (hu : IsSturmSolutionOn q u du (Icc a b)) (hq : ∀ x ∈ Ioo a b, q x ≤ M ^ 2)
    (hua : u a = 0) (hub : u b = 0) (hu0 : ∀ x ∈ Ioo a b, u x ≠ 0) : π / M ≤ b - a := by
  by_contra hlt
  push Not at hlt
  have hba : 0 < b - a := by linarith
  have hMab : M * (b - a) < π := by
    have := (lt_div_iff₀ hM).1 hlt
    linarith
  set M' : ℝ := (M + π / (b - a)) / 2 with hM'
  have hM'ab : M' * (b - a) = (M * (b - a) + π) / 2 := by
    rw [hM']; field_simp
  have hMM' : M < M' := by
    rw [hM']
    have : M < π / (b - a) := by rwa [lt_div_iff₀ hba]
    linarith
  have hM'π : M' * (b - a) < π := by linarith
  set δ : ℝ := (π - M' * (b - a)) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hM'pos : 0 < M' := hM.trans hMM'
  -- the comparison sine is positive on `[a, b]`
  have hwpos : ∀ x ∈ Icc a b, 0 < sin (M' * x + (δ - M' * a)) := by
    intro x hx
    refine sin_pos_of_pos_of_lt_pi ?_ ?_
    · nlinarith [hx.1]
    · have : M' * x ≤ M' * b := mul_le_mul_of_nonneg_left hx.2 hM'pos.le
      rw [hδ]; nlinarith
  obtain ⟨x, hx, hwx⟩ := hu.exists_zero_Ioo_of_lt hab
    ((isSturmSolutionOn_sin M' (δ - M' * a)).mono (subset_univ _))
    (fun x hx => (hq x hx).trans_lt (by gcongr)) hua hub hu0
  exact (hwpos x (Ioo_subset_Icc_self hx)).ne' hwx

end IsSturmSolutionOn
