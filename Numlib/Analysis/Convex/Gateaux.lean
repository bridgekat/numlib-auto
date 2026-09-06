import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Convex.Function

/-!
# Convexity of a functional through its directional derivatives

For `f : V → ℝ` on a convex set `K` of a real normed space, whose directional derivatives at every
point of `K` are represented by a bounded linear functional, `f' u : V →L[ℝ] ℝ`, three conditions
are equivalent:

* `f` is convex on `K`;
* the tangent functional at each point is a global minorant, `f u + f' u (v - u) ≤ f v`;
* the gradient is a monotone operator, `0 ≤ (f' v - f' u) (v - u)`.

`convexOn_iff_forall_add_lineDeriv_le` and `convexOn_iff_monotone_lineDeriv` are those equivalences,
`strictConvexOn_iff_forall_add_lineDeriv_lt` and `strictConvexOn_iff_forall_lineDeriv_sub_pos` their
strict forms.  A minimizer of `f` over `K` is then characterized by a variational inequality,
`isMinOn_iff_forall_lineDeriv_nonneg`, which collapses to a variational equation when `K` is a
subspace (`isMinOn_iff_forall_lineDeriv_eq_zero`) and survives the addition of a second, possibly
non-differentiable, convex term (`isMinOn_add_iff_forall_le`).  The last is what turns a constrained
convex minimization problem into an elliptic variational inequality.

The bounded linear representation `f' : V → V →L[ℝ] ℝ` is data rather than something derived:
`HasLineDerivAt` gives one scalar per direction and does not bundle those scalars into a functional,
and the classical Gâteaux derivative is required to be bounded and linear.  The hypothesis is
therefore always written out as `∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h`. There is no
separate `fderiv` version: `HasFDerivAt.hasLineDerivAt` specializes every statement below, and a
Fréchet derivative is a stronger hypothesis than the applications have.

`HasLineDerivAt.hasDerivAt_line` is the parameter translation that all of this rests on — a line
derivative at `u + t • h` is the derivative of `s ↦ f (u + s • h)` at `s = t` — and is stated here
for a general normed target because it belongs with the one-dimensional restriction argument and has
no other home yet.

The material is classical; it is stated as Theorems 5.3.17–5.3.19 and Theorem 11.2.1 of
[han2009theoretical].
-/

open Filter Set Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A line derivative at the point `u + t • h` in the direction `h` is the derivative of the
restriction `s ↦ f (u + s • h)` at `s = t`.  `HasLineDerivAt` itself only gives this at `t = 0`;
translating the parameter is what makes a mean value theorem along a segment available. -/
theorem HasLineDerivAt.hasDerivAt_line {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : V → W} {a : W} {u h : V} {t : ℝ} (hg : HasLineDerivAt ℝ g a (u + t • h) h) :
    HasDerivAt (fun s : ℝ => g (u + s • h)) a t := by
  have hg0 : HasDerivAt (fun s : ℝ => g (u + t • h + s • h)) a 0 := hg
  have h0 : HasDerivAt (fun s : ℝ => g (u + t • h + s • h)) a ((fun s : ℝ => s - t) t) := by
    simpa using hg0
  have h1 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h2 : HasDerivAt ((fun s : ℝ => g (u + t • h + s • h)) ∘ fun s : ℝ => s - t)
      ((1 : ℝ) • a) t := HasDerivAt.scomp t h0 h1
  have heq : ((fun s : ℝ => g (u + t • h + s • h)) ∘ fun s : ℝ => s - t)
      = fun s : ℝ => g (u + s • h) := by
    funext s
    simp only [Function.comp_apply]
    congr 1
    module
  rw [heq, one_smul] at h2
  exact h2

section Convexity

variable {K : Set V} {f j : V → ℝ} {f' : V → V →L[ℝ] ℝ}

/-- Mean value theorem along the segment `[u, v]` of a convex set: for an `f` whose directional
derivatives on `K` are the functionals `f'` there is an interior point `u + c • (v - u)` at which
the derivative in the direction `v - u` equals the slope `f v - f u`. -/
private theorem exists_lineDeriv_eq_sub (hK : Convex ℝ K)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) {u : V} (hu : u ∈ K) {v : V}
    (hv : v ∈ K) :
    ∃ c ∈ Ioo (0 : ℝ) 1, u + c • (v - u) ∈ K ∧ f' (u + c • (v - u)) (v - u) = f v - f u := by
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f (u + s • (v - u))) (f' (u + t • (v - u)) (v - u)) t :=
    fun t ht => (hG _ (hK.add_smul_sub_mem hu hv ht) (v - u)).hasDerivAt_line
  have hcont : ContinuousOn (fun s : ℝ => f (u + s • (v - u))) (Icc 0 1) :=
    fun t ht => ((hderiv t ht).continuousAt).continuousWithinAt
  obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => f (u + s • (v - u)))
    (fun t : ℝ => f' (u + t • (v - u)) (v - u)) zero_lt_one hcont
    (fun t ht => hderiv t ⟨ht.1.le, ht.2.le⟩)
  have h1v : u + (1 : ℝ) • (v - u) = v := by module
  have h0v : u + (0 : ℝ) • (v - u) = u := by module
  simp only [h1v, h0v, sub_zero, div_one] at hcslope
  exact ⟨c, hc, hK.add_smul_sub_mem hu hv ⟨hc.1.le, hc.2.le⟩, hcslope⟩

/-- A convex functional lies above each of its tangent functionals: if `f` is convex on `K` and has
the directional derivatives `A h` at `u ∈ K`, then `f u + A (v - u) ≤ f v` for every `v ∈ K`. -/
theorem ConvexOn.add_lineDeriv_le (hf : ConvexOn ℝ K f) {A : V →L[ℝ] ℝ} {u v : V} (hu : u ∈ K)
    (hv : v ∈ K) (hA : ∀ h, HasLineDerivAt ℝ f (A h) u h) : f u + A (v - u) ≤ f v := by
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (f (u + t • (v - u)) - f u)) (𝓝[>] (0 : ℝ))
      (𝓝 (A (v - u))) := (hA (v - u)).tendsto_slope_zero_right
  have hle : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t⁻¹ • (f (u + t • (v - u)) - f u) ≤ f v - f u := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    have hpt : (1 - t) • u + t • v = u + t • (v - u) := by module
    have hconv := hf.2 hu hv (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
    rw [hpt] at hconv
    simp only [smul_eq_mul] at hconv ⊢
    rw [inv_mul_le_iff₀ ht.1]
    have hexp : (1 - t) * f u + t * f v - f u = t * (f v - f u) := by ring
    linarith
  have hmain := le_of_tendsto hslope hle
  linarith

/-- A linear functional balances the displacements from a convex combination: writing `w = a • x + b
• y` with `a + b = 1`, the two displacements `x - w` and `y - w` cancel under the weights `a` and
`b`, so `a * A (x - w) + b * A (y - w) = 0`. -/
private theorem weighted_apply_sub_combo_eq_zero (A : V →L[ℝ] ℝ) (x y : V) {a b : ℝ}
    (hab : a + b = 1) :
    a * A (x - (a • x + b • y)) + b * A (y - (a • x + b • y)) = 0 := by
  have hz : a • (x - (a • x + b • y)) + b • (y - (a • x + b • y)) = 0 := by
    have hexp : a • (x - (a • x + b • y)) + b • (y - (a • x + b • y))
        = (a • x + b • y) - (a + b) • (a • x + b • y) := by module
    rw [hexp, hab, one_smul, sub_self]
  have hc := congrArg A hz
  rw [map_add, map_smul, map_smul, map_zero] at hc
  simpa [smul_eq_mul] using hc

/-- The tangent minorant inequality forces convexity: if `f u + f' u (v - u) ≤ f v` for all `u, v`
in a convex set `K`, then `f` is convex on `K`.  No differentiability is used — the functionals `f'`
are arbitrary. -/
theorem convexOn_of_add_lineDeriv_le (hK : Convex ℝ K)
    (h : ∀ u ∈ K, ∀ v ∈ K, f u + f' u (v - u) ≤ f v) : ConvexOn ℝ K f := by
  refine ⟨hK, ?_⟩
  intro x hx y hy a b ha hb hab
  have hwK : a • x + b • y ∈ K := hK hx hy ha hb hab
  have h1 := h _ hwK x hx
  have h2 := h _ hwK y hy
  have hlin := weighted_apply_sub_combo_eq_zero (f' (a • x + b • y)) x y hab
  have ha1 := mul_le_mul_of_nonneg_left h1 ha
  have hb1 := mul_le_mul_of_nonneg_left h2 hb
  have hsum : a * f (a • x + b • y) + b * f (a • x + b • y) = f (a • x + b • y) := by
    rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul]
  linarith

/-- Convexity of a functional with directional derivatives on a convex set is exactly the tangent
minorant inequality `f u + f' u (v - u) ≤ f v`. -/
theorem convexOn_iff_forall_add_lineDeriv_le (hK : Convex ℝ K)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) :
    ConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, f u + f' u (v - u) ≤ f v :=
  ⟨fun hf u hu _v hv => ConvexOn.add_lineDeriv_le hf hu hv (hG u hu),
    convexOn_of_add_lineDeriv_le hK⟩

/-- The tangent minorant inequality makes the gradient a monotone operator.  Adding the inequality
at `u` to the inequality at `v` cancels the values of `f`. -/
theorem monotone_lineDeriv_of_add_lineDeriv_le
    (h : ∀ u ∈ K, ∀ v ∈ K, f u + f' u (v - u) ≤ f v) {u : V} (hu : u ∈ K) {v : V} (hv : v ∈ K) :
    0 ≤ (f' v - f' u) (v - u) := by
  have h1 := h u hu v hv
  have h2 := h v hv u hu
  have h3 : f' v (u - v) = -f' v (v - u) := by rw [← map_neg, neg_sub]
  rw [h3] at h2
  rw [sub_apply]
  linarith

/-- A monotone gradient forces the tangent minorant inequality.  This is the one direction that
needs the mean value theorem: apply `exists_lineDeriv_eq_sub` on the segment `[u, v]` and compare
the derivative at the intermediate point with the derivative at `u`. -/
theorem add_lineDeriv_le_of_monotone_lineDeriv (hK : Convex ℝ K)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h)
    (h : ∀ u ∈ K, ∀ v ∈ K, 0 ≤ (f' v - f' u) (v - u)) {u : V} (hu : u ∈ K) {v : V} (hv : v ∈ K) :
    f u + f' u (v - u) ≤ f v := by
  obtain ⟨c, hc, hcmem, hcslope⟩ := exists_lineDeriv_eq_sub hK hG hu hv
  have hmono := h u hu _ hcmem
  rw [show u + c • (v - u) - u = c • (v - u) by abel, sub_apply, map_smul,
    map_smul, smul_eq_mul, smul_eq_mul] at hmono
  have hkey : f' u (v - u) ≤ f' (u + c • (v - u)) (v - u) := by nlinarith [hc.1]
  linarith

/-- Convexity of a functional with directional derivatives on a convex set is exactly monotonicity
of its gradient, `0 ≤ (f' v - f' u) (v - u)`. -/
theorem convexOn_iff_monotone_lineDeriv (hK : Convex ℝ K)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) :
    ConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, 0 ≤ (f' v - f' u) (v - u) :=
  (convexOn_iff_forall_add_lineDeriv_le hK hG).trans
    ⟨fun h _ hu _ hv => monotone_lineDeriv_of_add_lineDeriv_le h hu hv,
      fun h _ hu _ hv => add_lineDeriv_le_of_monotone_lineDeriv hK hG h hu hv⟩

/-- A strictly convex functional lies strictly above each of its tangent functionals at every other
point of `K`.  Applying the nonstrict inequality at the midpoint of `[u, v]` is what turns the
inequality strict. -/
theorem StrictConvexOn.add_lineDeriv_lt (hf : StrictConvexOn ℝ K f) {A : V →L[ℝ] ℝ} {u v : V}
    (hu : u ∈ K) (hv : v ∈ K) (huv : u ≠ v) (hA : ∀ h, HasLineDerivAt ℝ f (A h) u h) :
    f u + A (v - u) < f v := by
  have hw : (2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v ∈ K :=
    hf.1 hu hv (by norm_num) (by norm_num) (by norm_num)
  have hlt := hf.2 hu hv huv (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (0 : ℝ) < 2⁻¹)
    (by norm_num)
  have hb := ConvexOn.add_lineDeriv_le hf.convexOn hu hw hA
  have hwu : (2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v - u = (2 : ℝ)⁻¹ • (v - u) := by module
  rw [hwu, map_smul, smul_eq_mul] at hb
  simp only [smul_eq_mul] at hlt
  linarith

/-- The strict tangent minorant inequality forces strict convexity. -/
theorem strictConvexOn_of_add_lineDeriv_lt (hK : Convex ℝ K)
    (h : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → f u + f' u (v - u) < f v) : StrictConvexOn ℝ K f := by
  refine ⟨hK, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hwK : a • x + b • y ∈ K := hK hx hy ha.le hb.le hab
  have hwx : a • x + b • y ≠ x := by
    intro hcon
    have hb0 : b • (y - x) = 0 := by
      have hexp : b • (y - x) = a • x + b • y - (a + b) • x := by module
      rw [hexp, hab, one_smul, hcon, sub_self]
    rcases smul_eq_zero.mp hb0 with h' | h'
    · exact hb.ne' h'
    · exact hxy (sub_eq_zero.mp h').symm
  have hwy : a • x + b • y ≠ y := by
    intro hcon
    have ha0 : a • (x - y) = 0 := by
      have hexp : a • (x - y) = a • x + b • y - (a + b) • y := by module
      rw [hexp, hab, one_smul, hcon, sub_self]
    rcases smul_eq_zero.mp ha0 with h' | h'
    · exact ha.ne' h'
    · exact hxy (sub_eq_zero.mp h')
  have h1 := h _ hwK x hx hwx
  have h2 := h _ hwK y hy hwy
  have hlin := weighted_apply_sub_combo_eq_zero (f' (a • x + b • y)) x y hab
  have ha1 := mul_lt_mul_of_pos_left h1 ha
  have hb1 := mul_lt_mul_of_pos_left h2 hb
  have hsum : a * f (a • x + b • y) + b * f (a • x + b • y) = f (a • x + b • y) := by
    rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul]
  linarith

/-- Strict convexity of a functional with directional derivatives on a convex set is exactly the
strict tangent minorant inequality. -/
theorem strictConvexOn_iff_forall_add_lineDeriv_lt (hK : Convex ℝ K)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) :
    StrictConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, u ≠ v → f u + f' u (v - u) < f v :=
  ⟨fun hf u hu _v hv huv => StrictConvexOn.add_lineDeriv_lt hf hu hv huv (hG u hu),
    strictConvexOn_of_add_lineDeriv_lt hK⟩

/-- The strict tangent minorant inequality makes the gradient a strictly monotone operator. -/
theorem lineDeriv_sub_pos_of_add_lineDeriv_lt
    (h : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → f u + f' u (v - u) < f v) {u : V} (hu : u ∈ K) {v : V}
    (hv : v ∈ K) (huv : u ≠ v) : 0 < (f' v - f' u) (v - u) := by
  have h1 := h u hu v hv huv
  have h2 := h v hv u hu huv.symm
  have h3 : f' v (u - v) = -f' v (v - u) := by rw [← map_neg, neg_sub]
  rw [h3] at h2
  rw [sub_apply]
  linarith

/-- A strictly monotone gradient forces the strict tangent minorant inequality, again by the mean
value theorem on the segment `[u, v]`. -/
theorem add_lineDeriv_lt_of_lineDeriv_sub_pos (hK : Convex ℝ K)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h)
    (h : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → 0 < (f' v - f' u) (v - u)) {u : V} (hu : u ∈ K) {v : V}
    (hv : v ∈ K) (huv : u ≠ v) : f u + f' u (v - u) < f v := by
  obtain ⟨c, hc, hcmem, hcslope⟩ := exists_lineDeriv_eq_sub hK hG hu hv
  have hne : u ≠ u + c • (v - u) := by
    intro hcon
    have hz : c • (v - u) = 0 := by
      have hd : u + c • (v - u) - u = c • (v - u) := by abel
      rw [← hd, ← hcon, sub_self]
    rcases smul_eq_zero.mp hz with h' | h'
    · exact absurd h' (ne_of_gt hc.1)
    · exact huv (sub_eq_zero.mp h').symm
  have hmono := h u hu _ hcmem hne
  rw [show u + c • (v - u) - u = c • (v - u) by abel, sub_apply, map_smul,
    map_smul, smul_eq_mul, smul_eq_mul] at hmono
  have hkey : f' u (v - u) < f' (u + c • (v - u)) (v - u) := by nlinarith [hc.1]
  linarith

/-- Strict convexity of a functional with directional derivatives on a convex set is exactly strict
monotonicity of its gradient, `0 < (f' v - f' u) (v - u)` for `u ≠ v`. -/
theorem strictConvexOn_iff_forall_lineDeriv_sub_pos (hK : Convex ℝ K)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) :
    StrictConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, u ≠ v → 0 < (f' v - f' u) (v - u) :=
  (strictConvexOn_iff_forall_add_lineDeriv_lt hK hG).trans
    ⟨fun h _ hu _ hv huv => lineDeriv_sub_pos_of_add_lineDeriv_lt h hu hv huv,
      fun h _ hu _ hv huv => add_lineDeriv_lt_of_lineDeriv_sub_pos hK hG h hu hv huv⟩

/-- The variational inequality of a constrained minimizer, with a second convex term that need not
be differentiable: for `f` convex with directional derivatives `f'` and `j` convex on a convex set
`K`, a point `u ∈ K` minimizes `f + j` over `K` if and only if `0 ≤ f' u (v - u) + j v - j u` for
every `v ∈ K`.

This is the statement that turns a constrained convex minimization problem into an elliptic
variational inequality. -/
theorem isMinOn_add_iff_forall_le (hf : ConvexOn ℝ K f) (hj : ConvexOn ℝ K j)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) {u : V} (hu : u ∈ K) :
    IsMinOn (f + j) K u ↔ ∀ v ∈ K, 0 ≤ f' u (v - u) + j v - j u := by
  rw [isMinOn_iff]
  simp only [Pi.add_apply]
  constructor
  · intro hmin v hv
    have hslope : Tendsto (fun t : ℝ => t⁻¹ • (f (u + t • (v - u)) - f u)) (𝓝[>] (0 : ℝ))
        (𝓝 (f' u (v - u))) := (hG u hu (v - u)).tendsto_slope_zero_right
    have hge : j u - j v ≤ f' u (v - u) := by
      refine ge_of_tendsto hslope ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      have hpt : (1 - t) • u + t • v = u + t • (v - u) := by module
      have hjc := hj.2 hu hv (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
      rw [hpt] at hjc
      have hmem : u + t • (v - u) ∈ K :=
        hf.1.add_smul_sub_mem hu hv ⟨ht.1.le, (by linarith [ht.2] : t ≤ 1)⟩
      have hmin' := hmin _ hmem
      simp only [smul_eq_mul] at hjc ⊢
      rw [le_inv_mul_iff₀ ht.1]
      nlinarith
    linarith
  · intro h v hv
    have hb := ConvexOn.add_lineDeriv_le hf hu hv (hG u hu)
    have hv0 := h v hv
    linarith

/-- The variational inequality of a constrained minimizer: for `f` convex with directional
derivatives `f'` on a convex set `K`, a point `u ∈ K` minimizes `f` over `K` if and only if `0 ≤ f'
u (v - u)` for every `v ∈ K`.  The case `j = 0` of `isMinOn_add_iff_forall_le`. -/
theorem isMinOn_iff_forall_lineDeriv_nonneg (hf : ConvexOn ℝ K f)
    (hG : ∀ u ∈ K, ∀ h, HasLineDerivAt ℝ f (f' u h) u h) {u : V} (hu : u ∈ K) :
    IsMinOn f K u ↔ ∀ v ∈ K, 0 ≤ f' u (v - u) := by
  have hzero : ConvexOn ℝ K (0 : V → ℝ) := convexOn_const 0 hf.1
  simpa using isMinOn_add_iff_forall_le hf hzero hG hu

/-- Over a subspace the variational inequality of `isMinOn_iff_forall_lineDeriv_nonneg` collapses to
a variational equation: `u` minimizes `f` over the subspace `K` if and only if `f' u v = 0` for
every `v ∈ K`.  Both `v` and `-v` are admissible directions, which is what removes the inequality.
-/
theorem isMinOn_iff_forall_lineDeriv_eq_zero {K : Submodule ℝ V}
    (hf : ConvexOn ℝ (K : Set V) f)
    (hG : ∀ u ∈ (K : Set V), ∀ h, HasLineDerivAt ℝ f (f' u h) u h) {u : V} (hu : u ∈ K) :
    IsMinOn f (K : Set V) u ↔ ∀ v ∈ K, f' u v = 0 := by
  rw [isMinOn_iff_forall_lineDeriv_nonneg hf hG hu]
  constructor
  · intro h v hv
    have h1 := h (u + v) (K.add_mem hu hv)
    have h2 := h (u - v) (K.sub_mem hu hv)
    rw [show u + v - u = v by abel] at h1
    rw [show u - v - u = -v by abel, map_neg] at h2
    linarith
  · intro h v hv
    exact le_of_eq (h (v - u) (K.sub_mem hv hu)).symm

end Convexity
