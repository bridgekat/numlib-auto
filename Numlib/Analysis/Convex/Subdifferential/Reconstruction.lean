import Numlib.Analysis.Convex.Representation
import Numlib.Analysis.Convex.Subdifferential.Monotone
import Numlib.Analysis.Convex.Subdifferential.Rademacher
import Numlib.Analysis.Convex.Subdifferential.Uniqueness

/-!
# The subdifferential reconstructed from the gradient mapping

For a closed proper convex `f` whose effective domain has interior,

```
∂f x = cl (conv (S x)) + N_{dom f}(x)      for every x,
```

where `S x` is the set of limits of gradients `∇f xᵢ` at points of differentiability `xᵢ → x`.
Every subgradient, at a boundary point of `dom f` as much as at an interior one, is therefore
assembled out of honest gradients and normal directions.

## Main definitions

* `gradientLimits f x` — the set `S x`, as a set of *vectors*: gradients are recorded by their
  Riesz representatives, so that `S x` lives in the same space as `∂f x` does for `innerₗ E`.

## Main results

* `containsNoLine_subdifferential` — `∂f x` contains no line, when `dom f` has interior.
* `recessionCone_subdifferential_eq_normalCone` — the recession cone of `∂f x` is `N_{dom f}(x)`.
* `exists_mem_interior_convexDom_of_forall_normalCone` — the separation step: a direction making a
  strictly obtuse angle with every non-zero normal to `dom f` at `x` reaches `int (dom f)`.
* `exposedPoints_subset_gradientLimits` — the heart of the proof: every exposed point of `∂f x` is
  a limit of gradients.
* `subdifferential_eq_closure_convexHull_gradientLimits_add_normalCone` — the reconstruction itself
  ([rockafellar1970convex] Theorem 25.6).

## Implementation notes

The recession cone of `∂f x` never has to be computed. The classical proof identifies it with
`N_{dom f}(x)` and uses that three times — to see that `∂f x` contains no lines, to place extreme
directions in the normal cone, and to bound `⟨y, y*⟩` for normals `y*` — but each of those follows
more cheaply from the single inclusion `∂f x + N_{dom f}(x) ⊆ ∂f x` of
`Subdifferential/Calculus.lean` together with a "let `λ → ∞` in the subgradient inequality"
argument. So `recessionCone_subdifferential_eq_normalCone` is proved on its own and used nowhere
below.

## References

* [rockafellar1970convex] §25.
-/

namespace ConvexAnalysis

open Filter Metric Topology
open scoped Pointwise RealInnerProductSpace

section Reconstruction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

/-- The set `S x` of limits of gradients `∇f xᵢ` at points of differentiability `xᵢ` tending to
`x`, as a set of vectors: the gradient is an element of `StrongDual ℝ E`, and what is recorded here
is its Riesz representative, so that `S x` lives in the same space as `∂f x` for `innerₗ E`. -/
def gradientLimits (f : E → EReal) (x : E) : Set E :=
  {v | ∃ xs : ℕ → E, ∃ vs : ℕ → E, Tendsto xs atTop (𝓝 x) ∧
    (∀ i, HasGradientAtFn f (InnerProductSpace.toDual ℝ E (vs i)) (xs i)) ∧
    Tendsto vs atTop (𝓝 v)}

/-- A gradient at `x` itself is a limit of gradients, along the constant sequence. -/
theorem mem_gradientLimits_of_hasGradientAtFn {v : E}
    (h : HasGradientAtFn f (InnerProductSpace.toDual ℝ E v) x) : v ∈ gradientLimits f x :=
  ⟨fun _ => x, fun _ => v, tendsto_const_nhds, fun _ => h, tendsto_const_nhds⟩

/-- **`S x ⊆ ∂f x`**: the graph of `∂f` is closed, so a limit of gradients at points tending to `x`
is a subgradient at `x`. -/
theorem gradientLimits_subset_subdifferential (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) :
    gradientLimits f x ⊆ subdifferential (innerₗ E) f x := by
  rintro v ⟨xs, vs, hxs, hgrad, hvs⟩
  have hclosed : IsClosed (subgradientRel (innerₗ E) f) :=
    isClosed_subgradientRel continuous_inner hp (ClosedConvex.lowerSemicontinuous hcl)
  have hmem : ∀ i, (xs i, vs i) ∈ subgradientRel (innerₗ E) f := fun i => by
    have := subdifferential_innerL_eq_singleton hf (hgrad i)
    rw [LinearIsometryEquiv.symm_apply_apply] at this
    rw [mem_subgradientRel, this]
    rfl
  exact hclosed.mem_of_tendsto (hxs.prodMk_nhds hvs) (Eventually.of_forall hmem)

omit [FiniteDimensional ℝ E] in
/-- **A subgradient plus a multiple of a normal direction is a subgradient**, packaged for the
`innerₗ` pairing. -/
theorem add_smul_mem_subdifferential {v w : E} (hv : v ∈ subdifferential (innerₗ E) f x)
    (hw : w ∈ normalCone (innerₗ E) (convexDom f) x) {a : ℝ} (ha : 0 ≤ a) :
    v + a • w ∈ subdifferential (innerₗ E) f x := by
  refine subdifferential_add_normalCone_convexDom_subset (innerₗ E) f x ⟨v, hv, a • w, ?_, rfl⟩
  intro z hz
  have := hw z hz
  rw [map_smul, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos ha this

omit [FiniteDimensional ℝ E] in
/-- **The subgradient inequality at `v + a • w`, as a bound between real numbers.** Both `f z` and
`f x` are finite — the first because `z ∈ dom f`, the second because a subgradient exists at `x` —
so the `EReal` inequality is a real one, and the pairing splits by bilinearity. -/
theorem inner_add_smul_le_of_mem_subdifferential (hp : ProperConvex f) {v w z : E} {a : ℝ}
    (hmem : v + a • w ∈ subdifferential (innerₗ E) f x) (hz : z ∈ convexDom f) :
    ⟪z - x, v⟫ + a * ⟪z - x, w⟫ ≤ (f z).toReal - (f x).toReal := by
  have hle := hmem z
  have hval : (innerₗ E) (z - x) (v + a • w) = ⟪z - x, v⟫ + a * ⟪z - x, w⟫ := by
    rw [innerₗ_apply_apply, inner_add_right, real_inner_smul_right]
  have hfz : f z ≠ ⊤ := (mem_convexDom.1 hz).ne
  have hzb : f z ≠ ⊥ := hp.ne_bot z
  have hfx : f x ≠ ⊤ := (mem_convexDom.1 (mem_convexDom_of_mem_subdifferential hp hmem)).ne
  have hxb : f x ≠ ⊥ := hp.ne_bot x
  rw [hval, ← EReal.coe_toReal hfx hxb, ← EReal.coe_toReal hfz hzb,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
  linarith

omit [FiniteDimensional ℝ E] in
/-- **The subdifferential contains no line** once `dom f` has interior. If `v + t w ∈ ∂f x` for
every real `t`, the subgradient inequality forces `⟨z - x, w⟩ = 0` on all of `dom f`, and a set
with interior lies in no hyperplane. -/
theorem containsNoLine_subdifferential (hp : ProperConvex f)
    (hne : (interior (convexDom f)).Nonempty) :
    ContainsNoLine (subdifferential (innerₗ E) f x) := by
  intro v w hw
  by_contra hall
  push Not at hall
  -- `⟨z - x, w⟩ = 0` for every `z ∈ dom f`: otherwise a large `t` breaks the bound.
  have hzero : ∀ z ∈ convexDom f, ⟪z - x, w⟫ = 0 := by
    intro z hz
    by_contra hne'
    have hMle : ∀ t : ℝ, ⟪z - x, v⟫ + t * ⟪z - x, w⟫ ≤ (f z).toReal - (f x).toReal :=
      fun t => inner_add_smul_le_of_mem_subdifferential hp (hall t) hz
    have h1 := hMle (((f z).toReal - (f x).toReal - ⟪z - x, v⟫ + 1) / ⟪z - x, w⟫)
    rw [div_mul_cancel₀ _ hne'] at h1
    linarith
  -- A set with interior lies in no hyperplane.
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z₀ hz₀
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hw0 : ‖w‖ ≠ 0 := hwpos.ne'
  have hmem : z₀ + (r / (2 * ‖w‖)) • w ∈ convexDom f := by
    refine interior_subset (hball ?_)
    rw [mem_ball_iff_norm]
    have hcalc : ‖z₀ + (r / (2 * ‖w‖)) • w - z₀‖ = r / 2 := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ r / (2 * ‖w‖))]
      field_simp
    rw [hcalc]
    linarith
  have h1 := hzero _ hmem
  have h2 := hzero z₀ (interior_subset hz₀)
  have hsub : z₀ + (r / (2 * ‖w‖)) • w - x = (z₀ - x) + (r / (2 * ‖w‖)) • w := by abel
  rw [hsub, inner_add_left, real_inner_smul_left, h2, zero_add,
    real_inner_self_eq_norm_sq] at h1
  have hcontra : 0 < r / (2 * ‖w‖) * ‖w‖ ^ 2 := by positivity
  linarith

omit [FiniteDimensional ℝ E] in
/-- **A direction of recession of `∂f x` is normal to `dom f` at `x`.** Letting `λ → ∞` in the
subgradient inequality for `v + λ w` forces `⟨z - x, w⟩ ≤ 0` on `dom f`. -/
theorem recessionCone_subdifferential_subset_normalCone (hp : ProperConvex f) {v : E}
    (hv : v ∈ subdifferential (innerₗ E) f x) :
    recessionCone (subdifferential (innerₗ E) f x) ⊆ normalCone (innerₗ E) (convexDom f) x := by
  intro w hw z hz
  by_contra hpos
  push Not at hpos
  have hMle : ∀ a : ℝ, 0 ≤ a →
      ⟪z - x, v⟫ + a * ⟪z - x, w⟫ ≤ (f z).toReal - (f x).toReal :=
    fun a ha => inner_add_smul_le_of_mem_subdifferential hp (hw v hv a ha) hz
  have hgt : 0 < ⟪z - x, w⟫ := by
    rw [innerₗ_apply_apply] at hpos
    linarith
  have h0 := hMle 0 le_rfl
  rw [zero_mul, add_zero] at h0
  have h1 := hMle (((f z).toReal - (f x).toReal - ⟪z - x, v⟫ + 1) / ⟪z - x, w⟫)
    (div_nonneg (by linarith) hgt.le)
  rw [div_mul_cancel₀ _ hgt.ne'] at h1
  linarith

omit [FiniteDimensional ℝ E] in
/-- Wherever `∂f x` is non-empty, its recession cone *is* the normal cone to `dom f` at `x`. The
reconstruction below uses only the inclusion `recessionCone_subdifferential_subset_normalCone`, so
this equality is discharged here on its own: the other inclusion is `∂f x + N_{dom f}(x) ⊆ ∂f x`
read at a single normal direction. -/
theorem recessionCone_subdifferential_eq_normalCone (hp : ProperConvex f) {v : E}
    (hv : v ∈ subdifferential (innerₗ E) f x) :
    recessionCone (subdifferential (innerₗ E) f x) = normalCone (innerₗ E) (convexDom f) x :=
  Set.Subset.antisymm (recessionCone_subdifferential_subset_normalCone hp hv)
    fun _ hw _ hv' _ ha => add_smul_mem_subdifferential hv' hw ha

/-- **The separation step.** If every non-zero vector normal to `dom f` at `x` makes a strictly
obtuse angle with `y`, then the half-line from `x` in the direction `y` reaches `int (dom f)`.
Contrapositive plus `geometric_hahn_banach_open`: if the half-line missed the open convex set
`int (dom f)`, the separating functional would be a non-zero normal making a non-obtuse angle with
`y`. Proper separation is not needed. -/
theorem exists_mem_interior_convexDom_of_forall_normalCone (hf : ConvexFn f)
    (hne : (interior (convexDom f)).Nonempty) {y : E}
    (hy : ∀ w ∈ normalCone (innerₗ E) (convexDom f) x, w ≠ 0 → ⟪y, w⟫ < 0) :
    ∃ a : ℝ, 0 < a ∧ x + a • y ∈ interior (convexDom f) := by
  have hdom : Convex ℝ (convexDom f) := hf.convex_convexDom
  by_contra hcon
  push Not at hcon
  -- The half-line from `x` in the direction `y`.
  set R : Set E := {z | ∃ a : ℝ, 0 ≤ a ∧ z = x + a • y} with hR
  have hRconv : Convex ℝ R := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ s t hs ht hst
    refine ⟨s * a + t * b, add_nonneg (mul_nonneg hs ha) (mul_nonneg ht hb), ?_⟩
    have hx' : (s + t) • x = x := by rw [hst, one_smul]
    calc s • (x + a • y) + t • (x + b • y) = (s + t) • x + (s * a + t * b) • y := by module
      _ = x + (s * a + t * b) • y := by rw [hx']
  have hdisj : Disjoint (interior (convexDom f)) R := by
    rw [Set.disjoint_right]
    rintro _ ⟨a, ha, rfl⟩ hmem
    rcases eq_or_lt_of_le ha with rfl | hpos
    · -- `x` itself is interior, so a short step along `y` stays interior.
      rw [zero_smul, add_zero] at hmem
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hmem
      rcases eq_or_ne y 0 with rfl | hy0
      · exact hcon 1 one_pos (by simpa using hmem)
      · have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
        have hyne : ‖y‖ ≠ 0 := hypos.ne'
        refine hcon (r / (2 * ‖y‖)) (by positivity) (hball ?_)
        rw [mem_ball_iff_norm]
        have hcalc : ‖x + (r / (2 * ‖y‖)) • y - x‖ = r / 2 := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ r / (2 * ‖y‖))]
          field_simp
        rw [hcalc]
        linarith
    · exact hcon a hpos hmem
  obtain ⟨l, u, hlt, hge⟩ :=
    geometric_hahn_banach_open hdom.interior isOpen_interior hRconv hdisj
  obtain ⟨z₀, hz₀⟩ := hne
  have hx0 : x ∈ R := ⟨0, le_rfl, by simp⟩
  have hux : u ≤ l x := hge x hx0
  -- The separating functional is non-zero.
  have hl0 : l ≠ 0 := by
    rintro rfl
    have h1 : (0 : ℝ) < u := by simpa using hlt z₀ hz₀
    have h2 : u ≤ (0 : ℝ) := by simpa using hux
    linarith
  -- It is bounded above by `u` on all of `dom f`, not merely on the interior: a point of `dom f`
  -- can be nudged into the interior towards `z₀`, by an amount too small to change the sign.
  have hlex : ∀ z ∈ convexDom f, l z ≤ u := by
    intro z hz
    by_contra hgt
    push Not at hgt
    set c : ℝ := |l z₀ - l z| + 1 with hc
    have hcpos : 0 < c := by positivity
    set t : ℝ := min (1 / 2) ((l z - u) / (2 * c)) with htdef
    have htpos : 0 < t := lt_min (by norm_num) (by positivity)
    have htle : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have hmem : t • z₀ + (1 - t) • z ∈ interior (convexDom f) :=
      hdom.combo_interior_self_mem_interior hz₀ hz htpos (by linarith) (by ring)
    have hlt' := hlt _ hmem
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hlt'
    have hexp : t * l z₀ + (1 - t) * l z = l z + t * (l z₀ - l z) := by ring
    rw [hexp] at hlt'
    have habs : |t * (l z₀ - l z)| ≤ (l z - u) / 2 := by
      rw [abs_mul, abs_of_pos htpos]
      have h1 : t ≤ (l z - u) / (2 * c) := min_le_right _ _
      have h2 : |l z₀ - l z| ≤ c := by rw [hc]; linarith
      calc t * |l z₀ - l z| ≤ (l z - u) / (2 * c) * c :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = (l z - u) / 2 := by field_simp
    have hlow := (abs_le.1 habs).1
    linarith
  -- Its Riesz representative is a non-zero normal to `dom f` at `x`.
  set w : E := (InnerProductSpace.toDual ℝ E).symm l with hw
  have hlw : ∀ z : E, l z = ⟪w, z⟫ := fun z => by
    rw [hw, InnerProductSpace.toDual_symm_apply]
  have hwne : w ≠ 0 := by
    rw [hw]
    simpa using hl0
  have hwnormal : w ∈ normalCone (innerₗ E) (convexDom f) x := by
    intro z hz
    have hzx : l (z - x) ≤ 0 := by
      rw [map_sub]
      linarith [hlex z hz]
    rw [innerₗ_apply_apply, real_inner_comm w (z - x), ← hlw]
    exact hzx
  -- And it makes a non-obtuse angle with `y`, contradicting the hypothesis.
  have hly : 0 ≤ l y := by
    by_contra hnegy
    push Not at hnegy
    have hden : 0 < -l y := by linarith
    have ha : (0 : ℝ) ≤ (l x - u + 1) / (-l y) := div_nonneg (by linarith) hden.le
    have hbig := hge (x + ((l x - u + 1) / (-l y)) • y) ⟨(l x - u + 1) / (-l y), ha, rfl⟩
    rw [map_add, map_smul, smul_eq_mul] at hbig
    have hkey : ((l x - u + 1) / (-l y)) * l y = -(l x - u + 1) := by
      rw [div_mul_eq_mul_div, div_eq_iff hden.ne']
      ring
    rw [hkey] at hbig
    linarith
  have hcontra := hy w hwnormal hwne
  rw [real_inner_comm w y, ← hlw] at hcontra
  linarith

/-- **Points of differentiability approaching `x` from the direction `y`.** If the ray from `x` in
the unit direction `y` enters `int (dom f)`, density of the points of differentiability supplies
points arbitrarily close to it. The tolerance has to be `ε²` at distance `ε`, not `ε`:
it is the *direction* of approach that must converge to `y`. -/
theorem exists_seq_differentiableAtFn_tendsto_dir (hf : ConvexFn f) (hp : ProperConvex f)
    (hx : x ∈ convexDom f) {y : E} (hy : ‖y‖ = 1) {α : ℝ} (hα : 0 < α)
    (hαy : x + α • y ∈ interior (convexDom f)) :
    ∃ xs : ℕ → E, (∀ i, DifferentiableAtFn f (xs i)) ∧ (∀ i, xs i ≠ x) ∧
      Tendsto xs atTop (𝓝 x) ∧
      Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y) := by
  set ε : ℕ → ℝ := fun i => α / (i + 1) with hεdef
  have hεpos : ∀ i, 0 < ε i := fun i => by
    simp only [hεdef]
    positivity
  have hεle : ∀ i, ε i ≤ α := fun i => by
    simp only [hεdef]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) i, hα.le]
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have heq : ε = fun i : ℕ => α * (1 / ((i : ℝ) + 1)) := by
      funext i
      simp only [hεdef]
      ring
    rw [heq]
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul α
  set δ : ℕ → ℝ := fun i => min ((ε i) ^ 2) (ε i / 2) with hδdef
  have hδpos : ∀ i, 0 < δ i := fun i => lt_min (by positivity) (by positivity)
  have hδsq : ∀ i, δ i ≤ (ε i) ^ 2 := fun i => min_le_left _ _
  have hδhalf : ∀ i, δ i ≤ ε i / 2 := fun i => min_le_right _ _
  -- Points of differentiability within `δ i` of `x + ε i • y`, which is interior.
  have hcl : ∀ i, ∃ z, DifferentiableAtFn f z ∧ dist (x + (ε i) • y) z < δ i := fun i => by
    have hpt : x + (ε i) • y ∈ interior (convexDom f) :=
      mem_interior_convexDom_smul hf hx hα hαy (hεpos i) (hεle i)
    exact Metric.mem_closure_iff.1
      (interior_convexDom_subset_closure_differentiableAtFn hf hp hpt) (δ i) (hδpos i)
  choose xs hxsdiff hxsdist using hcl
  have hεy : ∀ i, ‖(ε i) • y‖ = ε i := fun i => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hεpos i), hy, mul_one]
  have hr : ∀ i, ‖xs i - x - (ε i) • y‖ < δ i := fun i => by
    have h := hxsdist i
    rw [dist_eq_norm] at h
    have heq : x + (ε i) • y - xs i = -(xs i - x - (ε i) • y) := by abel
    rwa [heq, norm_neg] at h
  have hlb : ∀ i, ε i / 2 < ‖xs i - x‖ := fun i => by
    have h2 : ‖(ε i) • y‖ ≤ ‖xs i - x‖ + ‖(ε i) • y - (xs i - x)‖ :=
      calc ‖(ε i) • y‖ = ‖(xs i - x) + ((ε i) • y - (xs i - x))‖ := by congr 1; abel
        _ ≤ ‖xs i - x‖ + ‖(ε i) • y - (xs i - x)‖ := norm_add_le _ _
    rw [hεy i, norm_sub_rev ((ε i) • y) (xs i - x)] at h2
    linarith [hr i, hδhalf i]
  have hub : ∀ i, ‖xs i - x‖ < ε i + δ i := fun i =>
    calc ‖xs i - x‖ = ‖(ε i) • y + (xs i - x - (ε i) • y)‖ := by congr 1; abel
      _ ≤ ‖(ε i) • y‖ + ‖xs i - x - (ε i) • y‖ := norm_add_le _ _
      _ < ε i + δ i := by rw [hεy i]; linarith [hr i]
  -- The direction of approach is within `4 ε i` of `y`.
  have hdir : ∀ i, ‖‖xs i - x‖⁻¹ • (xs i - x) - y‖ ≤ 4 * ε i := fun i => by
    have hnpos : 0 < ‖xs i - x‖ := lt_trans (by positivity) (hlb i)
    have hkey : ‖xs i - x‖⁻¹ • (xs i - x) - y
        = (‖xs i - x‖⁻¹ * ε i - 1) • y + ‖xs i - x‖⁻¹ • (xs i - x - (ε i) • y) := by
      module
    have h1 : ‖(‖xs i - x‖⁻¹ * ε i - 1) • y‖ = |‖xs i - x‖⁻¹ * ε i - 1| := by
      rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
    have h2 : ‖‖xs i - x‖⁻¹ • (xs i - x - (ε i) • y)‖
        = ‖xs i - x‖⁻¹ * ‖xs i - x - (ε i) • y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have habs : |‖xs i - x‖⁻¹ * ε i - 1| ≤ ‖xs i - x‖⁻¹ * ‖xs i - x - (ε i) • y‖ := by
      have hne : |ε i - ‖xs i - x‖| ≤ ‖xs i - x - (ε i) • y‖ := by
        have h := abs_norm_sub_norm_le ((ε i) • y) (xs i - x)
        rwa [hεy i, norm_sub_rev ((ε i) • y) (xs i - x)] at h
      have hrw : ‖xs i - x‖⁻¹ * ε i - 1 = ‖xs i - x‖⁻¹ * (ε i - ‖xs i - x‖) := by
        field_simp
      rw [hrw, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ‖xs i - x‖⁻¹)]
      exact mul_le_mul_of_nonneg_left hne (by positivity)
    have hfin : ‖xs i - x‖⁻¹ * ‖xs i - x - (ε i) • y‖ ≤ 2 * ε i := by
      have h3 : ‖xs i - x‖⁻¹ * ‖xs i - x - (ε i) • y‖ ≤ ‖xs i - x‖⁻¹ * (ε i) ^ 2 :=
        mul_le_mul_of_nonneg_left ((hr i).le.trans (hδsq i)) (by positivity)
      have h4 : ‖xs i - x‖⁻¹ * (ε i) ^ 2 ≤ 2 * ε i := by
        rw [inv_mul_eq_div, div_le_iff₀ hnpos]
        nlinarith [hlb i, hεpos i]
      linarith
    rw [hkey]
    calc ‖(‖xs i - x‖⁻¹ * ε i - 1) • y + ‖xs i - x‖⁻¹ • (xs i - x - (ε i) • y)‖
        ≤ ‖(‖xs i - x‖⁻¹ * ε i - 1) • y‖ + ‖‖xs i - x‖⁻¹ • (xs i - x - (ε i) • y)‖ :=
          norm_add_le _ _
      _ = |‖xs i - x‖⁻¹ * ε i - 1| + ‖xs i - x‖⁻¹ * ‖xs i - x - (ε i) • y‖ := by rw [h1, h2]
      _ ≤ 4 * ε i := by linarith
  refine ⟨xs, hxsdiff, fun i hcon => ?_, ?_, ?_⟩
  · have h := hlb i
    rw [hcon, sub_self, norm_zero] at h
    linarith [hεpos i]
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun i => norm_nonneg _)
      (fun i => (hub i).le.trans (by linarith [hδhalf i, hεpos i] : ε i + δ i ≤ 2 * ε i)) ?_
    simpa using hεlim.const_mul (2 : ℝ)
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun i => norm_nonneg _) hdir ?_
    simpa using hεlim.const_mul (4 : ℝ)

/-- **The substantive step**: an exposed point of `∂f x` is a limit of gradients.

If the functional exposing `x*` is zero the subdifferential is the single point `x*`, and a lone
subgradient makes `f` differentiable at `x` itself. Otherwise its Riesz representative `y`,
normalised, makes a strictly obtuse angle with every non-zero normal to `dom f` at `x`, so the ray
`x + α y` enters `int (dom f)`; density supplies points of differentiability approaching `x` in the
direction `y`, and the boundary convergence theorem collapses their subdifferentials onto the face
of `∂f x` exposed by `y`, which is `{x*}`. -/
theorem exposedPoints_subset_gradientLimits (hf : ConvexFn f) (hp : ProperConvex f)
    (hne : (interior (convexDom f)).Nonempty) :
    (subdifferential (innerₗ E) f x).exposedPoints ℝ ⊆ gradientLimits f x := by
  intro v hvmem
  obtain ⟨hv, l, hl⟩ := hvmem
  have hx : x ∈ convexDom f := mem_convexDom_of_mem_subdifferential hp hv
  set y₀ : E := (InnerProductSpace.toDual ℝ E).symm l with hy₀
  have hlw : ∀ z : E, l z = ⟪y₀, z⟫ := fun z => by
    rw [hy₀, InnerProductSpace.toDual_symm_apply]
  by_cases hzero : y₀ = 0
  · -- A zero functional exposes `v` only if `∂f x = {v}`, and then `f` is differentiable at `x`.
    have hl0 : ∀ z : E, l z = 0 := fun z => by rw [hlw, hzero, inner_zero_left]
    have hsingle : subdifferential (innerₗ E) f x = {v} :=
      Set.eq_singleton_iff_unique_mem.2 ⟨hv, fun z hz => (hl z hz).2 (by rw [hl0, hl0])⟩
    exact mem_gradientLimits_of_hasGradientAtFn
      (hasGradientAtFn_toDual_of_subdifferential_eq_singleton hf hp hsingle)
  · -- Otherwise, normalise the exposing direction.
    have hy₀pos : 0 < ‖y₀‖ := norm_pos_iff.2 hzero
    set y : E := ‖y₀‖⁻¹ • y₀ with hydef
    have hynorm : ‖y‖ = 1 := by
      rw [hydef, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
        inv_mul_cancel₀ hy₀pos.ne']
    have hyinner : ∀ z : E, ⟪y, z⟫ = ‖y₀‖⁻¹ * l z := fun z => by
      rw [hydef, real_inner_smul_left, hlw]
    have hinvpos : (0 : ℝ) < ‖y₀‖⁻¹ := by positivity
    -- Every non-zero normal to `dom f` at `x` makes a strictly obtuse angle with `y`.
    have hnormal : ∀ w ∈ normalCone (innerₗ E) (convexDom f) x, w ≠ 0 → ⟪y, w⟫ < 0 := by
      intro w hw hw0
      have hmem : v + w ∈ subdifferential (innerₗ E) f x := by
        have h := add_smul_mem_subdifferential hv hw zero_le_one
        rwa [one_smul] at h
      have hle := (hl _ hmem).1
      rw [map_add] at hle
      have hlwne : l w ≠ 0 := fun h0 => hw0 (by
        have heq : v + w = v := (hl _ hmem).2 (by rw [map_add, h0, add_zero])
        simpa using heq)
      rw [hyinner]
      exact mul_neg_of_pos_of_neg hinvpos (lt_of_le_of_ne (by linarith) hlwne)
    obtain ⟨α, hα, hαy⟩ := exists_mem_interior_convexDom_of_forall_normalCone hf hne hnormal
    obtain ⟨xs, hxsdiff, hxsne, hxslim, hxsdir⟩ :=
      exists_seq_differentiableAtFn_tendsto_dir hf hp hx hynorm hα hαy
    choose G hG using hxsdiff
    set vs : ℕ → E := fun i => (InnerProductSpace.toDual ℝ E).symm (G i) with hvsdef
    -- The face of `∂f x` exposed by `y` is the single point `v`.
    have hface : {w ∈ subdifferential (innerₗ E) f x |
        ∀ z ∈ subdifferential (innerₗ E) f x, ⟪y, z⟫ ≤ ⟪y, w⟫} = {v} := by
      refine Set.eq_singleton_iff_unique_mem.2 ⟨Set.mem_sep_iff.2 ⟨hv, fun z hz => ?_⟩, ?_⟩
      · rw [hyinner, hyinner]
        exact mul_le_mul_of_nonneg_left (hl z hz).1 hinvpos.le
      · rintro w ⟨hw, hwmax⟩
        have h1 := hwmax v hv
        rw [hyinner, hyinner] at h1
        exact (hl w hw).2 (le_of_mul_le_mul_left h1 hinvpos)
    -- The directional derivative is finite in the direction `y`, as the collapse step requires.
    have hdirbot : dirDeriv f x y ≠ ⊥ := by
      have h := (mem_subdifferential_iff_le_dirDeriv (B := innerₗ E) (mem_convexDom.1 hx).ne
        (hp.ne_bot x)).1 hv y
      intro hbot
      rw [hbot, le_bot_iff] at h
      exact (EReal.coe_ne_bot _) h
    refine ⟨xs, vs, hxslim, fun i => ?_, ?_⟩
    · rw [hvsdef, LinearIsometryEquiv.apply_symm_apply]
      exact hG i
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    have hev := eventually_subdifferential_subset_exposed_add_closedBall hf hp hx
      (fun i => interior_subset (hG i).mem_interior_convexDom) hxsne hxslim hxsdir hdirbot hα hαy
      (half_pos hε)
    rw [hface] at hev
    filter_upwards [hev] with i hi
    have hvsmem : vs i ∈ subdifferential (innerₗ E) f (xs i) := by
      rw [hvsdef, subdifferential_innerL_eq_singleton hf (hG i)]
      rfl
    obtain ⟨c, hc, d, hd, hcd⟩ := hi hvsmem
    rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [mem_closedBall_zero_iff] at hd
    rw [dist_eq_norm, ← hcd, add_sub_cancel_left]
    exact lt_of_le_of_lt hd (half_lt_self hε)

/-- For a closed proper convex function whose effective domain has interior, the subdifferential at
*any* point is reconstructed from the gradient mapping,

```
∂f x = cl (conv S(x)) + N_{dom f}(x),
```

where `S(x)` is the set of limits of gradients at points of differentiability tending to `x`.

The inclusion `⊇` is closedness and convexity of `∂f x` together with
`∂f x + N_{dom f}(x) ⊆ ∂f x`. The inclusion `⊆` is the extreme-point representation of a line-free
closed convex set — `∂f x` contains no lines, so it is the convex hull of its extreme points and
extreme directions — with **Straszewicz's theorem** carrying the extreme points into the closure of
the exposed ones, which `exposedPoints_subset_gradientLimits` places in `S(x)`, and
`recessionCone_subdifferential_subset_normalCone` carrying the extreme directions into the normal
cone. -/
theorem subdifferential_eq_closure_convexHull_gradientLimits_add_normalCone (hf : ConvexFn f)
    (hp : ProperConvex f) (hcl : ClosedConvex f) (hne : (interior (convexDom f)).Nonempty) :
    subdifferential (innerₗ E) f x
      = closure (convexHull ℝ (gradientLimits f x)) + normalCone (innerₗ E) (convexDom f) x := by
  have hflip : IsContinuousPairing ((innerₗ E).flip) := by rw [flip_innerₗ]; infer_instance
  have hSsub : gradientLimits f x ⊆ subdifferential (innerₗ E) f x :=
    gradientLimits_subset_subdifferential hf hp hcl
  have hconv : Convex ℝ (subdifferential (innerₗ E) f x) := convex_subdifferential _ f x
  have hclosed : IsClosed (subdifferential (innerₗ E) f x) := isClosed_subdifferential f x
  have hhull : closure (convexHull ℝ (gradientLimits f x)) ⊆ subdifferential (innerₗ E) f x :=
    closure_minimal (convexHull_min hSsub hconv) hclosed
  refine subset_antisymm ?_ ?_
  · -- `⊆`: the extreme-point representation, then Straszewicz's theorem and exposed points.
    rcases (subdifferential (innerₗ E) f x).eq_empty_or_nonempty with hempty | ⟨v₀, hv₀⟩
    · rw [hempty]
      exact Set.empty_subset _
    have hnl : ContainsNoLine (subdifferential (innerₗ E) f x) :=
      containsNoLine_subdifferential hp hne
    have hEP : (subdifferential (innerₗ E) f x).extremePoints ℝ
        ⊆ closure (convexHull ℝ (gradientLimits f x)) :=
      calc (subdifferential (innerₗ E) f x).extremePoints ℝ
          ⊆ closure ((subdifferential (innerₗ E) f x).exposedPoints ℝ) :=
            extremePoints_subset_closure_exposedPoints hconv hclosed
        _ ⊆ closure (convexHull ℝ (gradientLimits f x)) :=
            closure_mono ((exposedPoints_subset_gradientLimits hf hp hne).trans
              (subset_convexHull ℝ _))
    have hhullEP : convexHull ℝ ((subdifferential (innerₗ E) f x).extremePoints ℝ)
        ⊆ closure (convexHull ℝ (gradientLimits f x)) :=
      convexHull_min hEP (convex_convexHull ℝ _).closure
    have hED : (PointedCone.hull ℝ (extremeDirections (subdifferential (innerₗ E) f x)) : Set E)
        ⊆ normalCone (innerₗ E) (convexDom f) x :=
      Submodule.span_le.2 ((extremeDirections_subset_recessionCone hconv hclosed).trans
        (recessionCone_subdifferential_subset_normalCone hp hv₀) :
          extremeDirections (subdifferential (innerₗ E) f x)
            ⊆ (normalPointedCone (innerₗ E) (convexDom f) x : Set E))
    calc subdifferential (innerₗ E) f x
        = convexHullPD ((subdifferential (innerₗ E) f x).extremePoints ℝ)
            (extremeDirections (subdifferential (innerₗ E) f x)) :=
          (convexHullPD_extremePoints_extremeDirections hconv hclosed hnl).symm
      _ ⊆ closure (convexHull ℝ (gradientLimits f x)) + normalCone (innerₗ E) (convexDom f) x :=
          Set.add_subset_add hhullEP hED
  · -- `⊇`: the hull is inside `∂f x`, which absorbs normal directions.
    exact (Set.add_subset_add_right hhull).trans
      (subdifferential_add_normalCone_convexDom_subset (innerₗ E) f x)

end Reconstruction

end ConvexAnalysis
