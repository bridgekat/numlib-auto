/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Reflection.lean` and `Numlib/Analysis/Sobolev/Chart.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.Reflection

/-!
# The extension operator for a `C^1` domain with bounded boundary

Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Theorem 9.7:
for an open set `Ω ⊆ ℝ^N` of class `C^1` with bounded boundary and `1 ≤ p ≤ ∞`, there is a
bounded linear extension operator `P : W^{1,p}(Ω) → W^{1,p}(ℝ^N)` with `P u = u` on `Ω`,
`‖P u‖_{L^p(ℝ^N)} ≤ C ‖u‖_{L^p(Ω)}` and `‖P u‖_{W^{1,p}(ℝ^N)} ≤ C ‖u‖_{W^{1,p}(Ω)}`; with
Corollary 9.8, the density of the restrictions of `C_c^∞(ℝ^N)` functions in `W^{1,p}(Ω)`.

## The proof

The book's, assembled from the typed operators of the modules below this one, each a
`ContinuousLinearMap` with an almost-everywhere formula for its function and an `L^p` bound:

* the finite atlas `(U_i, H_i)_{i < k}` of the compact boundary
  (`IsContDiffChartDomain.exists_finite_atlas`) and the partition of unity `θ₀, θ_i` of Lemma 9.3
  (`IsCompact.exists_contDiff_partitionOfUnity`);
* step (a): `ū₀ = θ₀ u` extended by zero is `SobolevMultiIndex.extendZeroMulL` with the cut-off
  `θ₀`, which is a `IsSobolevCutoff` for `Ω` because `∇θ₀ = −∑ ∇θ_i` is compactly supported and
  `θ₀` vanishes near the boundary;
* step (b): for each chart, restrict to `U_i ∩ Ω` (`SobolevMultiIndex.restrictL`), transfer to
  `Q₊` along `H_i` (`SobolevMultiIndex.compDiffeoL`, Proposition 9.6), reflect to `Q`
  (`SobolevMultiIndex.evenReflectionL`, Lemma 9.2), transfer back to `U_i` along `H_i⁻¹`, and
  multiply by `θ_i` extended by zero; this is `SobolevEuclidean.chartExtendL`;
* step (c): `P u = ū₀ + ∑ û_i`, whose restriction to `Ω` is `∑ θ_i u = u` and whose norms are
  bounded by the products of the step constants.

The theorem is stated existentially, `∃ P C, …`, as the book states it: its consumers only ever
`obtain` an operator. The assembly is factored through
`SobolevEuclidean.exists_extensionL_of_atlas`, which takes an explicit finite atlas covering a
compact piece `K` of the boundary and a cut-off `χ` with `tsupport χ ∩ ∂Ω ⊆ K`, and extends the
functions with `u = χ u`; Theorem 9.7 is `K = ∂Ω`, `χ = 1`.

Remark 9, the extension operator for the unit square `(0, 1)²` — which is not of class `C^1` —
is `SobolevEuclidean.exists_extensionL_unitSquare`: four reflections across the sides
(`SobolevEuclidean.exists_reflectionStep`, a reflection across a translated hyperplane) reach
`W^{1,p}((−1, 3)²)`, and a cut-off extends by zero; the assembly is
`SobolevEuclidean.exists_extensionL_of_steps`.

## Elaboration

Every identity about the composites is proved first for *variables* standing for the operators
(`SobolevEuclidean.chartExtend_fn_of_ops`, `SobolevEuclidean.exists_extensionL_of_ops`) and
instantiated once: with the concrete `compDiffeoL`/`evenReflectionL` terms in place, each
rewrite in a goal costs a second of unification and the default heartbeat budget runs out.

## References

[brezis2011functional], §9.2, Theorem 9.7 and its proof, Corollary 9.8, Remark 9.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace EuclideanSpace
open scoped ContDiff Distributions ENNReal Topology RealInnerProductSpace

noncomputable section

/-! ### The cylinder under the reflection across `x_N = 0` -/

section Cylinder

variable {d : ℕ}

/-- The reflection across the hyperplane `v^⊥` of a unit vector `v`, explicitly:
`σ x = x − 2 ⟪x, v⟫ v`. -/
theorem hyperplaneReflection_apply_of_norm_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : E} (hv : ‖v‖ = 1) (x : E) :
    hyperplaneReflection v x = x - (2 * ⟪x, v⟫) • v := by
  rw [hyperplaneReflection, Submodule.reflection_apply, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton, hv, real_inner_comm]
  simp only [one_pow, two_smul, mul_smul, RCLike.ofReal_one, div_one]
  abel

/-- The reflection across `x_N = 0` in coordinates. -/
theorem hyperplaneReflection_single_last_apply (x : EuclideanSpace ℝ (Fin (d + 1)))
    (i : Fin (d + 1)) :
    hyperplaneReflection (single (Fin.last d) (1 : ℝ)) x i
      = if i = Fin.last d then -x (Fin.last d) else x i := by
  rw [hyperplaneReflection_apply_of_norm_eq_one EuclideanSpace.norm_single_last_one,
    EuclideanSpace.inner_single_last_one, PiLp.sub_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h; ring
  · ring

/-- The reflection across `x_N = 0` keeps the first `N − 1` coordinates. -/
theorem init_hyperplaneReflection_single_last (x : EuclideanSpace ℝ (Fin (d + 1))) :
    init (hyperplaneReflection (single (Fin.last d) (1 : ℝ)) x) = init x := by
  ext i
  simp [hyperplaneReflection_single_last_apply, Fin.castSucc_ne_last]

/-- The reflection across `x_N = 0` negates the last coordinate. -/
theorem hyperplaneReflection_single_last_apply_last (x : EuclideanSpace ℝ (Fin (d + 1))) :
    hyperplaneReflection (single (Fin.last d) (1 : ℝ)) x (Fin.last d) = -x (Fin.last d) := by
  simp [hyperplaneReflection_single_last_apply]

/-- The cylinder `Q` is invariant under the reflection across `x_N = 0`. -/
theorem mem_unitChartCube_hyperplaneReflection_iff (x : EuclideanSpace ℝ (Fin (d + 1))) :
    hyperplaneReflection (single (Fin.last d) (1 : ℝ)) x ∈ unitChartCube d ↔
      x ∈ unitChartCube d := by
  simp [mem_unitChartCube, init_hyperplaneReflection_single_last,
    hyperplaneReflection_single_last_apply_last]

/-- The cube `Q` is symmetric under the reflection across `x_N = 0`: `σ '' Q = Q`. -/
theorem hyperplaneReflection_image_unitChartCube :
    hyperplaneReflection (single (Fin.last d) (1 : ℝ)) '' unitChartCube d = unitChartCube d := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_unitChartCube_hyperplaneReflection_iff y).2 hy
  · intro hx
    exact ⟨hyperplaneReflection _ x, (mem_unitChartCube_hyperplaneReflection_iff x).2 hx,
      hyperplaneReflection_hyperplaneReflection _ x⟩

/-- The cylinder as an `Opens`. -/
def unitChartCubeOpens (d : ℕ) : Opens (EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨unitChartCube d, isOpen_unitChartCube⟩

/-- The underlying set of `unitChartCubeOpens d` is `unitChartCube d`. -/
@[simp]
theorem coe_unitChartCubeOpens : (unitChartCubeOpens d : Set _) = unitChartCube d := rfl

/-- `σ '' Q = Q` for the open `Q`. -/
theorem hyperplaneReflection_image_unitChartCubeOpens :
    hyperplaneReflection (single (Fin.last d) (1 : ℝ)) '' (unitChartCubeOpens d : Set _)
      = unitChartCubeOpens d :=
  hyperplaneReflection_image_unitChartCube

/-- The positive half of the cylinder for `v = e_N` is `Q₊`. -/
theorem coe_posHalf_unitChartCubeOpens :
    (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d) : Set _)
      = unitChartCubePos d := by
  ext x
  simp [coe_posHalf, unitChartCubePos, EuclideanSpace.inner_single_last_one]

end Cylinder

/-- The image of a set under an involution which preserves membership is the set. -/
theorem Function.Involutive.image_eq_of_forall_mem_iff {α : Type*} {σ : α → α}
    (hσ : Function.Involutive σ) {s : Set α} (h : ∀ x, σ x ∈ s ↔ x ∈ s) : σ '' s = s := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (h y).2 hy
  · intro hx
    exact ⟨σ x, (h x).2 hx, hσ x⟩

/-! ### Scaling the last coordinate, and the cylinders `Q_r` -/

section ScaleLast

variable {d : ℕ}

/-- `scaleLast l : (x', x_N) ↦ (x', l x_N)`, the linear map of `ℝ^{d+1}` scaling the last
coordinate by `l`. For `l < 0` it sends the lower half space into the upper one; the higher-order
reflection is a linear combination of the composites with `scaleLast (l j)`. -/
def scaleLast (l : ℝ) : EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
  ContinuousLinearMap.id ℝ _ +
    (l - 1) • (EuclideanSpace.proj (Fin.last d)).smulRight (single (Fin.last d) (1 : ℝ))

/-- The coordinates of `scaleLast l x`. -/
theorem scaleLast_apply (l : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin (d + 1)) :
    scaleLast l x i = if i = Fin.last d then l * x (Fin.last d) else x i := by
  simp only [scaleLast, add_apply, ContinuousLinearMap.id_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, PiLp.add_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h; ring
  · ring

/-- The last coordinate of `scaleLast l x` is `l x_N`. -/
@[simp]
theorem scaleLast_apply_last (l : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    scaleLast l x (Fin.last d) = l * x (Fin.last d) := by
  simp [scaleLast_apply]

/-- `scaleLast l` keeps the first `d` coordinates. -/
@[simp]
theorem init_scaleLast (l : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    init (scaleLast l x) = init x := by
  ext i
  simp [scaleLast_apply, Fin.castSucc_ne_last]

/-- `scaleLast l ∘ scaleLast l' = scaleLast (l l')`. -/
theorem scaleLast_scaleLast (l l' : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    scaleLast l (scaleLast l' x) = scaleLast (l * l') x := by
  ext i
  simp only [scaleLast_apply]
  split_ifs with h
  · subst h; simp [mul_assoc]
  · rfl

/-- `scaleLast 1` is the identity. -/
theorem scaleLast_one (x : EuclideanSpace ℝ (Fin (d + 1))) : scaleLast 1 x = x := by
  ext i
  simp only [scaleLast_apply]
  split_ifs with h
  · subst h; ring
  · rfl

/-- `scaleLast l` fixes the hyperplane `x_N = 0`. -/
theorem scaleLast_of_apply_last_eq_zero (l : ℝ) {x : EuclideanSpace ℝ (Fin (d + 1))}
    (hx : x (Fin.last d) = 0) : scaleLast l x = x := by
  ext i
  simp only [scaleLast_apply]
  split_ifs with h
  · subst h; rw [hx, mul_zero]
  · rfl

/-- `scaleLast l` as a continuous linear equivalence, `l ≠ 0`, with inverse `scaleLast l⁻¹`. -/
def scaleLastEquiv {l : ℝ} (hl : l ≠ 0) :
    EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
  ContinuousLinearEquiv.equivOfInverse (scaleLast l) (scaleLast l⁻¹)
    (fun x ↦ by rw [scaleLast_scaleLast, inv_mul_cancel₀ hl, scaleLast_one])
    (fun x ↦ by rw [scaleLast_scaleLast, mul_inv_cancel₀ hl, scaleLast_one])

/-- `scaleLastEquiv hl` is `scaleLast l`. -/
@[simp]
theorem scaleLastEquiv_apply {l : ℝ} (hl : l ≠ 0) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    scaleLastEquiv hl x = scaleLast l x :=
  rfl

/-- The inverse of `scaleLastEquiv hl` is `scaleLast l⁻¹`. -/
@[simp]
theorem scaleLastEquiv_symm_apply {l : ℝ} (hl : l ≠ 0) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    (scaleLastEquiv hl).symm x = scaleLast l⁻¹ x :=
  rfl

/-- The linear map `scaleLast l`, for `l ≠ 0`, is a `C^1` diffeomorphism of `scaleLast l ⁻¹' Ω`
onto `Ω` with bounded Jacobians, for every open `Ω`. -/
theorem scaleLast_isDiffeoOnWithBoundedJacobian {l : ℝ} (hl : l ≠ 0)
    (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
    ∃ M, IsDiffeoOnWithBoundedJacobian (scaleLast l) (scaleLast l⁻¹)
      (scaleLast l ⁻¹' (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) M := by
  have h := isDiffeoOnWithBoundedJacobian_affine (scaleLastEquiv hl) 0 Ω
  simp only [scaleLastEquiv_apply, add_zero, scaleLastEquiv_symm_apply, sub_zero] at h
  exact ⟨_, h⟩

end ScaleLast

section CylinderR

variable {d : ℕ}

/-- **The cylinder `Q_r = {(x', x_N) : ‖x'‖ < r, |x_N| < r}`** of radius `r`, an open subset of
the unit cylinder `Q` for `r ≤ 1`, with compact closure inside `Q` for `r < 1`. The chart-local
extensions of the higher-order theorem live on these: a chart is `C^k` on the closure of `Q` only,
and the transport of `W^{k,p}` along it needs `C^k` on an open neighbourhood of the closure of the
source, which `Q_r`, `r < 1`, has. -/
def cylinder (d : ℕ) (r : ℝ) : Opens (EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨{x | ‖init x‖ < r ∧ |x (Fin.last d)| < r},
    (isOpen_lt continuous_init.norm continuous_const).inter
      (isOpen_lt continuous_abs_apply_last continuous_const)⟩

/-- Membership of the cylinder `Q_r`. -/
theorem mem_cylinder {r : ℝ} {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ cylinder d r ↔ ‖init x‖ < r ∧ |x (Fin.last d)| < r :=
  Iff.rfl

/-- The cylinder `Q_r`, `r ≤ 1`, lies in the unit cylinder. -/
theorem cylinder_subset_unitChartCube {r : ℝ} (hr : r ≤ 1) :
    (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ unitChartCube d :=
  fun _ hx ↦ ⟨hx.1.trans_le hr, hx.2.trans_le hr⟩

/-- The closure of `Q_r` lies in the closed cylinder of radius `r`. -/
theorem closure_cylinder_subset (r : ℝ) :
    closure (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))
      ⊆ {x | ‖init x‖ ≤ r ∧ |x (Fin.last d)| ≤ r} :=
  closure_minimal (fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩)
    ((isClosed_le continuous_init.norm continuous_const).inter
      (isClosed_le continuous_abs_apply_last continuous_const))

/-- The closure of `Q_r`, `r < 1`, lies in the open unit cylinder `Q`. -/
theorem closure_cylinder_subset_unitChartCube {r : ℝ} (hr : r < 1) :
    closure (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ unitChartCube d :=
  fun _ hx ↦ ⟨(closure_cylinder_subset r hx).1.trans_lt hr,
    (closure_cylinder_subset r hx).2.trans_lt hr⟩

/-- The cylinder `Q_r` is bounded. -/
theorem isBounded_cylinder (r : ℝ) :
    Bornology.IsBounded (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) := by
  refine (isBounded_iff_forall_norm_le.2 ⟨2 * |r|, fun x hx ↦ ?_⟩)
  have h1 : ‖x‖ ^ 2 ≤ (2 * |r|) ^ 2 := by
    rw [norm_sq_eq_init_add_last]
    have hr : 0 ≤ |r| := abs_nonneg r
    have hi : ‖init x‖ ≤ |r| := hx.1.le.trans (le_abs_self r)
    have hl : |x (Fin.last d)| ≤ |r| := hx.2.le.trans (le_abs_self r)
    nlinarith [sq_abs (x (Fin.last d)), abs_nonneg (x (Fin.last d)), norm_nonneg (init x)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

/-- The closure of `Q_r` is compact. -/
theorem isCompact_closure_cylinder (r : ℝ) :
    IsCompact (closure (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  (isBounded_cylinder r).isCompact_closure

/-- The cylinder has finite volume. -/
theorem volume_cylinder_lt_top (r : ℝ) :
    volume (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) < ⊤ :=
  (isBounded_cylinder r).measure_lt_top

/-- The cylinder is convex. -/
theorem convex_cylinder (r : ℝ) :
    Convex ℝ (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) := by
  have e1 : {x : EuclideanSpace ℝ (Fin (d + 1)) | ‖init x‖ < r}
      = initL.toLinearMap ⁻¹' ball (0 : EuclideanSpace ℝ (Fin d)) r := by
    ext x; simp [initL_apply, mem_ball, dist_zero_right]
  have e2 : {x : EuclideanSpace ℝ (Fin (d + 1)) | |x (Fin.last d)| < r}
      = (EuclideanSpace.proj (Fin.last d)).toLinearMap ⁻¹' ball (0 : ℝ) r := by
    ext x; simp [mem_ball]
  have h1 : Convex ℝ {x : EuclideanSpace ℝ (Fin (d + 1)) | ‖init x‖ < r} := by
    rw [e1]; exact (convex_ball _ _).linear_preimage _
  have h2 : Convex ℝ {x : EuclideanSpace ℝ (Fin (d + 1)) | |x (Fin.last d)| < r} := by
    rw [e2]; exact (convex_ball _ _).linear_preimage _
  exact h1.inter h2

/-- The cylinder is symmetric under the reflection across `x_N = 0`. -/
theorem hyperplaneReflection_image_cylinder (r : ℝ) :
    hyperplaneReflection (single (Fin.last d) (1 : ℝ)) '' (cylinder d r : Set _) = cylinder d r :=
      by
  refine Function.Involutive.image_eq_of_forall_mem_iff (hyperplaneReflection_hyperplaneReflection
    _)
    fun x ↦ ?_
  simp [mem_cylinder, init_hyperplaneReflection_single_last,
    hyperplaneReflection_single_last_apply_last]

/-- `scaleLast l`, `|l| ≤ 1`, maps the cylinder into itself. -/
theorem scaleLast_mem_cylinder {l r : ℝ} (hl : |l| ≤ 1) {x : EuclideanSpace ℝ (Fin (d + 1))}
    (hx : x ∈ cylinder d r) : scaleLast l x ∈ cylinder d r := by
  refine ⟨by rw [init_scaleLast]; exact hx.1, ?_⟩
  rw [scaleLast_apply_last, abs_mul]
  calc |l| * |x (Fin.last d)| ≤ 1 * |x (Fin.last d)| :=
        mul_le_mul_of_nonneg_right hl (abs_nonneg _)
    _ = |x (Fin.last d)| := one_mul _
    _ < r := hx.2

/-- The positive half of the cylinder for `v = e_N` is `Q_r ∩ {x_N > 0}`. -/
theorem coe_posHalf_cylinder (r : ℝ) :
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))
      = (cylinder d r : Set _) ∩ {x | 0 < x (Fin.last d)} := by
  rw [coe_posHalf]
  ext x
  simp [EuclideanSpace.inner_single_last_one]

/-- A compact subset of the unit cylinder lies in a cylinder `Q_r` with `r < 1`. -/
theorem exists_lt_one_subset_cylinder {K : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hK : IsCompact K) (hKQ : K ⊆ unitChartCube d) : ∃ r, r < 1 ∧ K ⊆ cylinder d r := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, zero_lt_one, empty_subset _⟩
  obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hne
    (continuous_init.norm.max continuous_abs_apply_last).continuousOn
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max ‖init x₀‖ |x₀ (Fin.last d)| := ⟨_, rfl⟩
  have hm1 : m < 1 := by rw [hm]; exact max_lt (hKQ hx₀).1 (hKQ hx₀).2
  refine ⟨(m + 1) / 2, by linarith, fun x hx ↦ ?_⟩
  have h : max ‖init x‖ |x (Fin.last d)| ≤ m := by rw [hm]; exact hmax hx
  exact ⟨by linarith [le_max_left ‖init x‖ |x (Fin.last d)|],
    by linarith [le_max_right ‖init x‖ |x (Fin.last d)|]⟩

end CylinderR

/-! ### The chart-local extension -/

section ChartLocal

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

namespace ContDiffChart

variable (c : ContDiffChart 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- The range `U` of a chart as an `Opens`. -/
def opensU : Opens (EuclideanSpace ℝ (Fin (d + 1))) := ⟨c.U, c.isOpen_U⟩

/-- The underlying set of `c.opensU` is `c.U`. -/
@[simp]
theorem coe_opensU : (c.opensU : Set _) = c.U := rfl

/-- `U ∩ Ω` as an `Opens`. -/
def opensInter : Opens (EuclideanSpace ℝ (Fin (d + 1))) := ⟨c.U ∩ Ω, c.isOpen_U.inter Ω.isOpen⟩

/-- The underlying set of `c.opensInter` is `c.U ∩ Ω`. -/
@[simp]
theorem coe_opensInter : (c.opensInter : Set _) = c.U ∩ Ω := rfl

/-- `U ∩ Ω ≤ Ω`. -/
theorem opensInter_le : c.opensInter ≤ Ω := fun _ hx ↦ hx.2

/-- `U ∩ Ω ≤ U`. -/
theorem opensInter_le_opensU : c.opensInter ≤ c.opensU := fun _ hx ↦ hx.1

/-- A chart restricted to `Q₊`, read on the positive half `posHalf e_N Q` of the cylinder, is a
`C^1` diffeomorphism onto `U ∩ Ω` with bounded Jacobians. -/
theorem exists_isDiffeoOnWithBoundedJacobian_posHalf :
    ∃ M, IsDiffeoOnWithBoundedJacobian c.toFun c.invFun
      (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d) : Set _)
      (c.opensInter : Set _) M := by
  rw [coe_posHalf_unitChartCubeOpens, coe_opensInter]
  exact c.isDiffeoOnWithBoundedJacobian_pos le_rfl Ω.isOpen

/-- The inverse of a chart is a `C^1` diffeomorphism of `U` onto `Q` with bounded Jacobians. -/
theorem exists_isDiffeoOnWithBoundedJacobian_invFun :
    ∃ M, IsDiffeoOnWithBoundedJacobian c.invFun c.toFun (c.opensU : Set _)
      (unitChartCubeOpens d : Set _) M := by
  obtain ⟨M, hM⟩ := c.isDiffeoOnWithBoundedJacobian le_rfl
  exact ⟨M, hM.symm⟩

end ContDiffChart

namespace SobolevEuclidean

variable (p) (c : ContDiffChart 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- The restriction `W^{1,p}(Ω) → W^{1,p}(U ∩ Ω)` of step (b). -/
def chartRestrictL :
    SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p c.opensInter :=
  SobolevMultiIndex.restrictL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p volume
    c.opensInter_le

/-- The transfer `v = u ∘ H : W^{1,p}(U ∩ Ω) → W^{1,p}(Q₊)` of step (b). -/
def chartTransferL : SobolevEuclidean (d + 1) 1 p c.opensInter →L[ℝ]
    SobolevEuclidean (d + 1) 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d)) :=
  SobolevMultiIndex.compDiffeoL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume
    c.exists_isDiffeoOnWithBoundedJacobian_posHalf.choose_spec

/-- The reflection `v ↦ v^⋆ : W^{1,p}(Q₊) → W^{1,p}(Q)` of step (b). -/
def cubeReflectL : SobolevEuclidean (d + 1) 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d)) →L[ℝ]
    SobolevEuclidean (d + 1) 1 p (unitChartCubeOpens d) :=
  SobolevEuclidean.evenReflectionL EuclideanSpace.norm_single_last_one
    hyperplaneReflection_image_unitChartCubeOpens

/-- The retransfer `w = v^⋆ ∘ H⁻¹ : W^{1,p}(Q) → W^{1,p}(U)` of step (b). -/
def chartRetransferL : SobolevEuclidean (d + 1) 1 p (unitChartCubeOpens d) →L[ℝ]
    SobolevEuclidean (d + 1) 1 p c.opensU :=
  SobolevMultiIndex.compDiffeoL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume
    c.exists_isDiffeoOnWithBoundedJacobian_invFun.choose_spec

/-- **The chart-local extension of step (b) of the proof of Theorem 9.7**, as a bounded linear
map `W^{1,p}(Ω) → W^{1,p}(U)`: restrict to `U ∩ Ω`, transfer to `Q₊` along `H`, reflect to `Q`,
transfer back to `U` along `H⁻¹`. Its function agrees with `u` on `U ∩ Ω`
(`SobolevEuclidean.chartExtendL_fn_ae_eq`) and its `L^p(U)` norm is bounded by a multiple of
`‖u‖_{L^p(U ∩ Ω)}` (`SobolevEuclidean.exists_eLpNorm_fn_chartExtendL_le`) — the book's
`w_i ∈ W^{1,p}(U_i)`, `w_i = u` on `U_i ∩ Ω`, `‖w_i‖_{W^{1,p}(U_i)} ≤ C ‖u‖_{W^{1,p}(U_i ∩ Ω)}`. -/
def chartExtendL : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p c.opensU :=
  chartRetransferL p c ∘L cubeReflectL p ∘L chartTransferL p c ∘L chartRestrictL p c

/-- `chartExtendL` is the composite of the four maps of step (b). -/
theorem chartExtendL_apply (u : SobolevEuclidean (d + 1) 1 p Ω) :
    chartExtendL p c u = chartRetransferL p c (cubeReflectL p (chartTransferL p c
      (chartRestrictL p c u))) :=
  rfl

/-- The function of the restriction. -/
theorem fn_chartRestrictL (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (chartRestrictL p c u) =ᵐ[volume.restrict (c.opensInter : Set _)]
      SobolevMultiIndex.fn u :=
  SobolevMultiIndex.fn_restrictL _ _

/-- The function of the transfer is `u ∘ H`. -/
theorem fn_chartTransferL (v : SobolevEuclidean (d + 1) 1 p c.opensInter) :
    SobolevMultiIndex.fn (chartTransferL p c v)
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d) : Set _)]
        fun y ↦ SobolevMultiIndex.fn v (c.toFun y) :=
  SobolevMultiIndex.fn_compDiffeoL _ _

/-- The `L^p` bound of the transfer. -/
theorem exists_eLpNorm_fn_chartTransferL_le : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ v : SobolevEuclidean (d + 1) 1 p c.opensInter,
      eLpNorm (SobolevMultiIndex.fn (chartTransferL p c v)) p
        (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d) : Set _))
        ≤ C * eLpNorm (SobolevMultiIndex.fn v) p (volume.restrict (c.opensInter : Set _)) :=
  SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le _

/-- On `Q₊`, the reflected function is the function. -/
theorem fn_cubeReflectL_restrict
    (w : SobolevEuclidean (d + 1) 1 p
      (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d))) :
    SobolevMultiIndex.fn (cubeReflectL p w)
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d) : Set _)]
        SobolevMultiIndex.fn w :=
  SobolevMultiIndex.fn_evenReflectionL_restrict _ _ _

/-- The `L^p` bound of the reflection. -/
theorem eLpNorm_fn_cubeReflectL_le
    (w : SobolevEuclidean (d + 1) 1 p
      (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d))) :
    eLpNorm (SobolevMultiIndex.fn (cubeReflectL p w)) p
        (volume.restrict (unitChartCubeOpens d : Set _))
      ≤ 2 * eLpNorm (SobolevMultiIndex.fn w) p
        (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d) : Set _)) :=
  SobolevMultiIndex.eLpNorm_fn_evenReflectionL_le _ _ _

/-- The function of the retransfer is `w ∘ H⁻¹`. -/
theorem fn_chartRetransferL (w : SobolevEuclidean (d + 1) 1 p (unitChartCubeOpens d)) :
    SobolevMultiIndex.fn (chartRetransferL p c w) =ᵐ[volume.restrict (c.opensU : Set _)]
      fun x ↦ SobolevMultiIndex.fn w (c.invFun x) :=
  SobolevMultiIndex.fn_compDiffeoL _ _

/-- The `L^p` bound of the retransfer. -/
theorem exists_eLpNorm_fn_chartRetransferL_le : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ w : SobolevEuclidean (d + 1) 1 p (unitChartCubeOpens d),
      eLpNorm (SobolevMultiIndex.fn (chartRetransferL p c w)) p (volume.restrict (c.opensU : Set _))
        ≤ C * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (unitChartCubeOpens d : Set _)) :=
  SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le _

/-- Almost everywhere statements on `Q₊` pull back along `H⁻¹` to `U ∩ Ω`. -/
theorem ae_comp_chart_invFun {P : EuclideanSpace ℝ (Fin (d + 1)) → Prop}
    (hP : ∀ᵐ y ∂volume.restrict
      (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d) : Set _), P y) :
    ∀ᵐ x ∂volume.restrict (c.opensInter : Set _), P (c.invFun x) :=
  c.exists_isDiffeoOnWithBoundedJacobian_posHalf.choose_spec.symm.ae_comp_restrict hP

end SobolevEuclidean

end ChartLocal

/-! ### The chart-local extension: identity and bound -/

section ChartLocalSpec

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The function of a restrict–transfer–reflect–retransfer composite**, with the four operators
as variables: on `U ∩ Ω` it is the function of `u`. The transports of almost everywhere
statements from `Q₊` to `U ∩ Ω` along `H⁻¹` are a hypothesis (`htrans`). -/
theorem SobolevEuclidean.chartExtend_fn_of_ops
    {Ω Ωc Qp Q U : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    {H Hinv : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (R : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p Ωc)
    (T₁ : SobolevEuclidean (d + 1) 1 p Ωc →L[ℝ] SobolevEuclidean (d + 1) 1 p Qp)
    (S : SobolevEuclidean (d + 1) 1 p Qp →L[ℝ] SobolevEuclidean (d + 1) 1 p Q)
    (T₂ : SobolevEuclidean (d + 1) 1 p Q →L[ℝ] SobolevEuclidean (d + 1) 1 p U)
    (hRfn : ∀ u, SobolevMultiIndex.fn (R u) =ᵐ[volume.restrict (Ωc : Set _)] SobolevMultiIndex.fn u)
    (hT₁fn : ∀ v, SobolevMultiIndex.fn (T₁ v) =ᵐ[volume.restrict (Qp : Set _)]
      fun y ↦ SobolevMultiIndex.fn v (H y))
    (hSfn : ∀ w, SobolevMultiIndex.fn (S w) =ᵐ[volume.restrict (Qp : Set _)] SobolevMultiIndex.fn w)
    (hT₂fn : ∀ w, SobolevMultiIndex.fn (T₂ w) =ᵐ[volume.restrict (U : Set _)]
      fun x ↦ SobolevMultiIndex.fn w (Hinv x))
    (htrans : ∀ {P : EuclideanSpace ℝ (Fin (d + 1)) → Prop},
      (∀ᵐ y ∂volume.restrict (Qp : Set _), P y) → ∀ᵐ x ∂volume.restrict (Ωc : Set _), P (Hinv x))
    (hΩcU : Ωc ≤ U) (hHinv : ∀ x ∈ (Ωc : Set _), H (Hinv x) = x)
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (T₂ (S (T₁ (R u)))) =ᵐ[volume.restrict (Ωc : Set _)]
      SobolevMultiIndex.fn u := by
  have h1 : ∀ᵐ x ∂volume.restrict (Ωc : Set _), SobolevMultiIndex.fn (T₂ (S (T₁ (R u)))) x
      = SobolevMultiIndex.fn (S (T₁ (R u))) (Hinv x) :=
    ae_restrict_of_ae_restrict_of_subset hΩcU (hT₂fn (S (T₁ (R u))))
  have h2 : ∀ᵐ x ∂volume.restrict (Ωc : Set _), SobolevMultiIndex.fn (S (T₁ (R u))) (Hinv x)
      = SobolevMultiIndex.fn (T₁ (R u)) (Hinv x) := htrans (hSfn (T₁ (R u)))
  have h3 : ∀ᵐ x ∂volume.restrict (Ωc : Set _), SobolevMultiIndex.fn (T₁ (R u)) (Hinv x)
      = SobolevMultiIndex.fn (R u) (H (Hinv x)) := htrans (hT₁fn (R u))
  filter_upwards [h1, h2, h3, hRfn u, ae_restrict_mem Ωc.isOpen.measurableSet]
    with x hx1 hx2 hx3 hx4 hxΩc
  rw [hx1, hx2, hx3, hHinv x hxΩc, hx4]

/-- **The `L^p` bound of a restrict–transfer–reflect–retransfer composite**, with the operators
as variables. -/
theorem SobolevEuclidean.eLpNorm_chartExtend_of_ops
    {Ω Ωc Qp Q U : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (R : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p Ωc)
    (T₁ : SobolevEuclidean (d + 1) 1 p Ωc →L[ℝ] SobolevEuclidean (d + 1) 1 p Qp)
    (S : SobolevEuclidean (d + 1) 1 p Qp →L[ℝ] SobolevEuclidean (d + 1) 1 p Q)
    (T₂ : SobolevEuclidean (d + 1) 1 p Q →L[ℝ] SobolevEuclidean (d + 1) 1 p U)
    (hRfn : ∀ u, SobolevMultiIndex.fn (R u) =ᵐ[volume.restrict (Ωc : Set _)] SobolevMultiIndex.fn u)
    {C₁ C₂ : ℝ≥0∞}
    (hT₁Lp : ∀ v, eLpNorm (SobolevMultiIndex.fn (T₁ v)) p (volume.restrict (Qp : Set _))
      ≤ C₁ * eLpNorm (SobolevMultiIndex.fn v) p (volume.restrict (Ωc : Set _)))
    (hSLp : ∀ w, eLpNorm (SobolevMultiIndex.fn (S w)) p (volume.restrict (Q : Set _))
      ≤ 2 * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (Qp : Set _)))
    (hT₂Lp : ∀ w, eLpNorm (SobolevMultiIndex.fn (T₂ w)) p (volume.restrict (U : Set _))
      ≤ C₂ * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (Q : Set _)))
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    eLpNorm (SobolevMultiIndex.fn (T₂ (S (T₁ (R u))))) p (volume.restrict (U : Set _))
      ≤ C₂ * (2 * C₁) * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ωc : Set _)) := by
  calc eLpNorm (SobolevMultiIndex.fn (T₂ (S (T₁ (R u))))) p (volume.restrict (U : Set _))
      ≤ C₂ * eLpNorm (SobolevMultiIndex.fn (S (T₁ (R u)))) p (volume.restrict (Q : Set _)) :=
        hT₂Lp _
    _ ≤ C₂ * (2 * eLpNorm (SobolevMultiIndex.fn (T₁ (R u))) p (volume.restrict (Qp : Set _))) := by
        gcongr; exact hSLp _
    _ ≤ C₂ * (2 * (C₁ * eLpNorm (SobolevMultiIndex.fn (R u)) p
          (volume.restrict (Ωc : Set _)))) := by
        gcongr; exact hT₁Lp _
    _ = C₂ * (2 * C₁) * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ωc : Set _)) := by
        rw [eLpNorm_congr_ae (hRfn u)]; ring

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  (c : ContDiffChart 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- **The chart-local extension agrees with `u` on `U ∩ Ω`**: the book's `w_i = u` on
`U_i ∩ Ω`. -/
theorem SobolevEuclidean.chartExtendL_fn_ae_eq (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (SobolevEuclidean.chartExtendL p c u)
      =ᵐ[volume.restrict (c.opensInter : Set _)] SobolevMultiIndex.fn u := by
  rw [SobolevEuclidean.chartExtendL_apply]
  exact SobolevEuclidean.chartExtend_fn_of_ops (SobolevEuclidean.chartRestrictL p c)
    (SobolevEuclidean.chartTransferL p c) (SobolevEuclidean.cubeReflectL p)
    (SobolevEuclidean.chartRetransferL p c) (SobolevEuclidean.fn_chartRestrictL p c)
    (SobolevEuclidean.fn_chartTransferL p c) (SobolevEuclidean.fn_cubeReflectL_restrict p)
    (SobolevEuclidean.fn_chartRetransferL p c) (fun h ↦ SobolevEuclidean.ae_comp_chart_invFun c h)
    c.opensInter_le_opensU (fun x hx ↦ c.toFun_invFun hx.1) u

/-- **The `L^p` bound of the chart-local extension**:
`‖w_i‖_{L^p(U_i)} ≤ C ‖u‖_{L^p(U_i ∩ Ω)}`. -/
theorem SobolevEuclidean.exists_eLpNorm_fn_chartExtendL_le : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      eLpNorm (SobolevMultiIndex.fn (SobolevEuclidean.chartExtendL p c u)) p
        (volume.restrict (c.opensU : Set _))
        ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (c.opensInter : Set _)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := SobolevEuclidean.exists_eLpNorm_fn_chartTransferL_le p c
  obtain ⟨C₂, hC₂, h₂⟩ := SobolevEuclidean.exists_eLpNorm_fn_chartRetransferL_le p c
  refine ⟨C₂ * (2 * C₁), ENNReal.mul_ne_top hC₂ (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hC₁),
    fun u ↦ ?_⟩
  rw [SobolevEuclidean.chartExtendL_apply]
  exact SobolevEuclidean.eLpNorm_chartExtend_of_ops (SobolevEuclidean.chartRestrictL p c)
    (SobolevEuclidean.chartTransferL p c) (SobolevEuclidean.cubeReflectL p)
    (SobolevEuclidean.chartRetransferL p c) (SobolevEuclidean.fn_chartRestrictL p c) h₁
    (SobolevEuclidean.eLpNorm_fn_cubeReflectL_le p) h₂ u

end ChartLocalSpec

/-! ### The assembly over an atlas -/

section Assembly

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞}
  {Ω : Opens E} {μ : Measure E}

/-- The function of a finite sum is, off a null set of `Ω`, the sum of the functions. -/
theorem SobolevMultiIndex.fn_finset_sum {κ : Type*} (s : Finset κ)
    (w : κ → SobolevMultiIndex F b k p Ω μ) :
    SobolevMultiIndex.fn (∑ i ∈ s, w i) =ᵐ[μ.restrict (Ω : Set E)]
      ∑ i ∈ s, SobolevMultiIndex.fn (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using SobolevMultiIndex.fn_zero (F := F) (b := b) (k := k) (p := p) (Ω := Ω) (μ := μ)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (SobolevMultiIndex.fn_add _ _).trans ((EventuallyEq.refl _ _).add ih)

end Assembly


section Atlas

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {k : ℕ} {U Ωc : Fin k → Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {E₀ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤}
  {E : ∀ i, SobolevEuclidean (d + 1) 1 p (U i) →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤}
  {C : ∀ i, SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p (U i)}
  {P : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤}

/-- The function of `P u = E₀ u + ∑ i, E i (C i u)`. -/
theorem SobolevEuclidean.fn_extension_of_ops (hP : ∀ u, P u = E₀ u + ∑ i, E i (C i u))
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (P u) =ᵐ[volume]
      SobolevMultiIndex.fn (E₀ u) + ∑ i, SobolevMultiIndex.fn (E i (C i u)) := by
  rw [hP u]
  exact eventuallyEq_restrict_coe_top_iff.1 ((SobolevMultiIndex.fn_add _ _).trans
    ((EventuallyEq.refl _ _).add (SobolevMultiIndex.fn_finset_sum _ _)))

/-- **Step (c) of the proof of Theorem 9.7, the identity `P u = u` on `Ω`**, with the operators
as variables: `E₀` the zero extension of `α₀ u`, `C i` the chart-local extension to `U i`,
`E i` the zero extension of `α i ·` from `U i`, and `α₀ + ∑ α i = χ` on `Ω`; for `u = χ u`
on `Ω`, `P u = u` on `Ω`. -/
theorem SobolevEuclidean.fn_extension_ae_eq_of_ops
    (hΩc : ∀ i, (Ωc i : Set (EuclideanSpace ℝ (Fin (d + 1))))
      = (U i : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {α₀ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {α : Fin k → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {χ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hsum : ∀ x ∈ (Ω : Set _), α₀ x + ∑ i, α i x = χ x)
    (hα : ∀ i x, x ∉ (U i : Set _) → α i x = 0)
    (hE₀fn : ∀ u, SobolevMultiIndex.fn (E₀ u) =ᵐ[volume]
      (Ω : Set _).indicator fun x ↦ α₀ x • SobolevMultiIndex.fn u x)
    (hEfn : ∀ i w, SobolevMultiIndex.fn (E i w) =ᵐ[volume]
      (U i : Set _).indicator fun x ↦ α i x • SobolevMultiIndex.fn w x)
    (hCfn : ∀ i u, SobolevMultiIndex.fn (C i u) =ᵐ[volume.restrict (Ωc i : Set _)]
      SobolevMultiIndex.fn u)
    (hP : ∀ u, P u = E₀ u + ∑ i, E i (C i u)) (u : SobolevEuclidean (d + 1) 1 p Ω)
    (hu : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set _)]
      fun x ↦ χ x * SobolevMultiIndex.fn u x) :
    SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u := by
  have hΩmeas : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := Ω.isOpen.measurableSet
  have h1 : ∀ᵐ x ∂volume, x ∈ (Ω : Set _) →
      SobolevMultiIndex.fn (E₀ u) x = α₀ x • SobolevMultiIndex.fn u x := by
    filter_upwards [hE₀fn u] with x hx hxΩ
    rw [hx, Set.indicator_of_mem hxΩ]
  have h2 : ∀ᵐ x ∂volume, ∀ i, x ∈ (Ω : Set _) →
      SobolevMultiIndex.fn (E i (C i u)) x = α i x • SobolevMultiIndex.fn u x := by
    rw [ae_all_iff]
    intro i
    filter_upwards [hEfn i (C i u), (ae_restrict_iff' (Ωc i).isOpen.measurableSet).1 (hCfn i u)]
      with x hx hx' hxΩ
    rw [hx]
    by_cases hxU : x ∈ (U i : Set _)
    · rw [Set.indicator_of_mem hxU, hx' (by rw [hΩc i]; exact ⟨hxU, hxΩ⟩)]
    · rw [Set.indicator_of_notMem hxU, hα i x hxU, zero_smul]
  filter_upwards [ae_restrict_of_ae (SobolevEuclidean.fn_extension_of_ops hP u),
    ae_restrict_of_ae h1, ae_restrict_of_ae h2, ae_restrict_mem hΩmeas, hu]
    with x hx hx1 hx2 hxΩ hxu
  rw [hx, Pi.add_apply, Finset.sum_apply, hx1 hxΩ]
  simp_rw [hx2 _ hxΩ]
  rw [← Finset.sum_smul, ← add_smul, hsum x hxΩ, smul_eq_mul, ← hxu]

/-- **Step (c) of the proof of Theorem 9.7, the `L^p` bound**, with the operators as
variables: `‖P u‖_{L^p} ≤ (A₀ + ∑ A i B i) ‖u‖_{L^p(Ω)}`. -/
theorem SobolevEuclidean.eLpNorm_fn_extension_le_of_ops
    (hΩc : ∀ i, (Ωc i : Set (EuclideanSpace ℝ (Fin (d + 1))))
      = (U i : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {A₀ : ℝ≥0∞} {A B : Fin k → ℝ≥0∞}
    (hE₀Lp : ∀ u, eLpNorm (SobolevMultiIndex.fn (E₀ u)) p volume
      ≤ A₀ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)))
    (hELp : ∀ i w, eLpNorm (SobolevMultiIndex.fn (E i w)) p volume
      ≤ A i * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (U i : Set _)))
    (hCLp : ∀ i u, eLpNorm (SobolevMultiIndex.fn (C i u)) p (volume.restrict (U i : Set _))
      ≤ B i * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ωc i : Set _)))
    (hP : ∀ u, P u = E₀ u + ∑ i, E i (C i u)) (u : SobolevEuclidean (d + 1) 1 p Ω) :
    eLpNorm (SobolevMultiIndex.fn (P u)) p volume
      ≤ (A₀ + ∑ i, A i * B i)
        * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)) := by
  have hΩcΩ : ∀ i, (Ωc i : Set (EuclideanSpace ℝ (Fin (d + 1))))
      ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := fun i ↦ by
    rw [hΩc i]; exact inter_subset_right
  rw [eLpNorm_congr_ae (SobolevEuclidean.fn_extension_of_ops hP u), add_mul, Finset.sum_mul]
  refine (eLpNorm_add_le Fact.out).trans (add_le_add (hE₀Lp u) ?_)
  refine (eLpNorm_sum_le Fact.out).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  refine (hELp i (C i u)).trans ?_
  rw [mul_assoc]
  gcongr
  refine (hCLp i u).trans ?_
  gcongr
  exact hΩcΩ i

/-- **The assembly `P u = ū₀ + ∑ û_i` of step (c) of the proof of Theorem 9.7**, with the
operators as variables: `E₀` the zero extension of `α₀ u`, `C i` the chart-local extension to
`U i`, `E i` the zero extension of `α i ·` from `U i`, and `α₀ + ∑ α i = χ` on `Ω`. For every `u`
with `u = χ u` on `Ω`, `P u = u` on `Ω`, `‖P u‖_{L^p} ≤ K ‖u‖_{L^p(Ω)}` and `‖P u‖ ≤ K ‖u‖`. -/
theorem SobolevEuclidean.exists_extensionL_of_ops
    (hΩc : ∀ i, (Ωc i : Set (EuclideanSpace ℝ (Fin (d + 1))))
      = (U i : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (E₀ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤)
    (E : ∀ i, SobolevEuclidean (d + 1) 1 p (U i) →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤)
    (C : ∀ i, SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p (U i))
    {α₀ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {α : Fin k → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {χ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hsum : ∀ x ∈ (Ω : Set _), α₀ x + ∑ i, α i x = χ x)
    (hα : ∀ i x, x ∉ (U i : Set _) → α i x = 0)
    (hE₀fn : ∀ u, SobolevMultiIndex.fn (E₀ u) =ᵐ[volume]
      (Ω : Set _).indicator fun x ↦ α₀ x • SobolevMultiIndex.fn u x)
    (hEfn : ∀ i w, SobolevMultiIndex.fn (E i w) =ᵐ[volume]
      (U i : Set _).indicator fun x ↦ α i x • SobolevMultiIndex.fn w x)
    (hCfn : ∀ i u, SobolevMultiIndex.fn (C i u) =ᵐ[volume.restrict (Ωc i : Set _)]
      SobolevMultiIndex.fn u)
    {A₀ : ℝ≥0∞} {A B : Fin k → ℝ≥0∞} (hA₀ : A₀ ≠ ⊤) (hA : ∀ i, A i ≠ ⊤) (hB : ∀ i, B i ≠ ⊤)
    (hE₀Lp : ∀ u, eLpNorm (SobolevMultiIndex.fn (E₀ u)) p volume
      ≤ A₀ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)))
    (hELp : ∀ i w, eLpNorm (SobolevMultiIndex.fn (E i w)) p volume
      ≤ A i * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (U i : Set _)))
    (hCLp : ∀ i u, eLpNorm (SobolevMultiIndex.fn (C i u)) p (volume.restrict (U i : Set _))
      ≤ B i * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ωc i : Set _))) :
    ∃ (P : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤) (K : ℝ),
      ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set _)]
          (fun x ↦ χ x * SobolevMultiIndex.fn u x) →
        SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal K * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)) ∧
        ‖P u‖ ≤ K * ‖u‖ := by
  obtain ⟨P, hP⟩ : ∃ P : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤,
      ∀ u, P u = E₀ u + ∑ i, E i (C i u) :=
    ⟨E₀ + ∑ i, (E i).comp (C i), fun u ↦ by
      simp only [add_apply, sum_apply, ContinuousLinearMap.comp_apply]⟩
  have hK₀ : A₀ + ∑ i, A i * B i ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hA₀, ENNReal.sum_ne_top.2 fun i _ ↦ ENNReal.mul_ne_top (hA i) (hB i)⟩
  refine ⟨P, max (A₀ + ∑ i, A i * B i).toReal ‖P‖, fun u hu ↦
    ⟨SobolevEuclidean.fn_extension_ae_eq_of_ops hΩc hsum hα hE₀fn hEfn hCfn hP u hu, ?_, ?_⟩⟩
  · refine (SobolevEuclidean.eLpNorm_fn_extension_le_of_ops hΩc hE₀Lp hELp hCLp hP u).trans ?_
    gcongr
    calc A₀ + ∑ i, A i * B i = ENNReal.ofReal (A₀ + ∑ i, A i * B i).toReal :=
          (ENNReal.ofReal_toReal hK₀).symm
      _ ≤ ENNReal.ofReal (max (A₀ + ∑ i, A i * B i).toReal ‖P‖) :=
          ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end Atlas

/-! ### Theorem 9.7 -/

section Theorem97

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of the `θ₀ = 1 - ∑ i, θ i` of a partition of unity is `-∑ i, ∇θ i`. -/
theorem fderiv_eq_neg_sum_of_add_sum_eq_one {ι : Type*} [Fintype ι] {θ₀ : E → ℝ}
    {θ : ι → E → ℝ} (hθ : ∀ i, ContDiff ℝ ∞ (θ i)) (hsum : ∀ x, θ₀ x + ∑ i, θ i x = 1) (x : E) :
    fderiv ℝ θ₀ x = -∑ i, fderiv ℝ (θ i) x := by
  have hθ₀ : θ₀ = fun x ↦ 1 - ∑ i, θ i x := funext fun x ↦ eq_sub_of_add_eq (hsum x)
  have : HasFDerivAt θ₀ (0 - ∑ i, fderiv ℝ (θ i) x) x := by
    rw [hθ₀]
    exact (hasFDerivAt_const (1 : ℝ) x).sub
      (HasFDerivAt.fun_sum fun i _ ↦ ((hθ i).differentiable (by simp) x).hasFDerivAt)
  rw [this.fderiv, zero_sub]

/-- **`θ₀ χ` is a cut-off for `Ω`**, for the `θ₀` of Lemma 9.3 on a compact `K ⊆ ∂Ω` and a smooth
`χ`, bounded with bounded derivative, with `tsupport χ ∩ ∂Ω ⊆ K`: it is smooth; bounded since
`|θ₀| ≤ 1`; with bounded derivative since `∇θ₀ = -∑ i, ∇θ i` is compactly supported; and its
support misses `∂Ω`, because `tsupport (θ₀ χ) ∩ ∂Ω ⊆ tsupport θ₀ ∩ K = ∅`. -/
theorem IsSobolevCutoff.mul_of_partition {ι : Type*} [Fintype ι] {Ω : Opens E} {K : Set E}
    {θ₀ : E → ℝ} {θ : ι → E → ℝ} {χ : E → ℝ} (hθ₀ : ContDiff ℝ ∞ θ₀)
    (hθ : ∀ i, ContDiff ℝ ∞ (θ i)) (hθ₀1 : ∀ x, |θ₀ x| ≤ 1)
    (hsum : ∀ x, θ₀ x + ∑ i, θ i x = 1) (hθc : ∀ i, HasCompactSupport (θ i))
    (hθ₀K : Disjoint (tsupport θ₀) K) (hχ : ContDiff ℝ ∞ χ)
    (hχb : ∃ M, ∀ x, |χ x| ≤ M ∧ ‖fderiv ℝ χ x‖ ≤ M)
    (hχK : tsupport χ ∩ frontier (Ω : Set E) ⊆ K) :
    IsSobolevCutoff Ω fun x ↦ θ₀ x * χ x where
  contDiff := hθ₀.mul hχ
  exists_bound := by
    obtain ⟨Mχ, hMχ⟩ := hχb
    choose Mθ hMθ using fun i ↦
      ((hθc i).fderiv ℝ).exists_bound_of_continuous ((hθ i).continuous_fderiv (by simp))
    have hMχ0 : 0 ≤ Mχ := (abs_nonneg _).trans (hMχ 0).1
    have hMθ0 : 0 ≤ ∑ i, Mθ i := Finset.sum_nonneg fun i _ ↦ (norm_nonneg _).trans (hMθ i 0)
    refine ⟨Mχ + Mχ * ∑ i, Mθ i, fun x ↦ ⟨?_, ?_⟩⟩
    · calc |θ₀ x * χ x| = |θ₀ x| * |χ x| := abs_mul _ _
        _ ≤ 1 * Mχ := mul_le_mul (hθ₀1 x) (hMχ x).1 (abs_nonneg _) zero_le_one
        _ ≤ Mχ + Mχ * ∑ i, Mθ i := by nlinarith [mul_nonneg hMχ0 hMθ0]
    · rw [fderiv_fun_mul (hθ₀.differentiable (by simp) x) (hχ.differentiable (by simp) x),
        fderiv_eq_neg_sum_of_add_sum_eq_one hθ hsum x]
      calc ‖θ₀ x • fderiv ℝ χ x + χ x • -∑ i, fderiv ℝ (θ i) x‖
          ≤ ‖θ₀ x • fderiv ℝ χ x‖ + ‖χ x • -∑ i, fderiv ℝ (θ i) x‖ := norm_add_le _ _
        _ ≤ 1 * Mχ + Mχ * ∑ i, Mθ i := by
          gcongr
          · rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul (hθ₀1 x) (hMχ x).2 (norm_nonneg _) zero_le_one
          · rw [norm_smul, Real.norm_eq_abs, norm_neg]
            exact mul_le_mul (hMχ x).1
              ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ hMθ i x)) (norm_nonneg _) hMχ0
        _ = Mχ + Mχ * ∑ i, Mθ i := by ring
  disjoint_frontier := Set.disjoint_left.2 fun x hx hxf ↦
    hθ₀K.notMem_of_mem_left (tsupport_mul_subset_left hx)
      (hχK ⟨tsupport_mul_subset_right hx, hxf⟩)

/-- **`θ χ` is a cut-off for `Ω`** for `θ` smooth and compactly supported in `Ω` and `χ` smooth:
the functions `θ_i χ` of the proof of Theorem 9.7. -/
theorem IsSobolevCutoff.mul_of_hasCompactSupport {Ω : Opens E} {θ χ : E → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) (hθΩ : tsupport θ ⊆ Ω)
    (hχ : ContDiff ℝ ∞ χ) : IsSobolevCutoff Ω fun x ↦ θ x * χ x :=
  IsSobolevCutoff.of_hasCompactSupport (hθ.mul hχ) hθc.mul_right
    (tsupport_mul_subset_left.trans hθΩ)

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **The assembly of Theorem 9.7 over an explicit atlas**: for a compact `K`, charts
`c i : ContDiffChart 1 Ω`, `i : Fin k`, with `K ⊆ ⋃ i, (c i).U`, and a smooth `χ`, bounded with
bounded derivative, with `tsupport χ ∩ ∂Ω ⊆ K`, there are
`P : W^{1,p}(Ω) →L[ℝ] W^{1,p}(ℝ^N)` and `C` such that for every `u` with `u = χ u` on `Ω`:
`P u = u` on `Ω`, `‖P u‖_{L^p(ℝ^N)} ≤ C ‖u‖_{L^p(Ω)}` and
`‖P u‖_{W^{1,p}(ℝ^N)} ≤ C ‖u‖_{W^{1,p}(Ω)}`.
The operator is `P u = θ₀ χ u + ∑ i, θ_i χ w_i` for the partition of unity `θ₀, θ_i` of Lemma 9.3
on `K` subordinate to the `U_i` (`IsCompact.exists_contDiff_partitionOfUnity`), the zero
extensions `SobolevMultiIndex.extendZeroMulL` with the cut-offs `θ₀ χ` for `Ω` and `θ_i χ` for
`U_i`, and the chart-local extensions `w_i = SobolevEuclidean.chartExtendL (c i) u`. Theorem 9.7
is the case `K = ∂Ω`, `χ = 1` (`SobolevEuclidean.exists_extensionL`); the general Corollary 9.8
is `K = ∂Ω ∩ closedBall 0 (3R)` with a cut-off `χ` equal to `1` on `ball 0 (2R)`. -/
theorem SobolevEuclidean.exists_extensionL_of_atlas {K : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hK : IsCompact K) {k : ℕ}
    (c : Fin k → ContDiffChart 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : K ⊆ ⋃ i, (c i).U) {χ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχb : ∃ M, ∀ x, |χ x| ≤ M ∧ ‖fderiv ℝ χ x‖ ≤ M)
    (hχK : tsupport χ ∩ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ K) :
    ∃ (P : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set _)]
          (fun x ↦ χ x * SobolevMultiIndex.fn u x) →
        SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)) ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨θ₀, θ, hθ₀, hθ, hθ₀01, -, hsum, hθc, hθU, hθ₀K⟩ :=
    hK.exists_contDiff_partitionOfUnity (fun i ↦ (c i).isOpen_U) hc
  have hα₀ : IsSobolevCutoff Ω fun x ↦ θ₀ x * χ x :=
    IsSobolevCutoff.mul_of_partition hθ₀ hθ
      (fun x ↦ abs_le.2 ⟨by linarith [(hθ₀01 x).1], (hθ₀01 x).2⟩) hsum hθc hθ₀K hχ hχb hχK
  have hα : ∀ i, IsSobolevCutoff (c i).opensU fun x ↦ θ i x * χ x := fun i ↦
    IsSobolevCutoff.mul_of_hasCompactSupport (hθ i) (hθc i) (hθU i) hχ
  obtain ⟨M₀, -, hM₀⟩ := hα₀.exists_nonneg_bound
  choose M hM0 hM using fun i ↦ (hα i).exists_nonneg_bound
  choose B hB hBu using fun i ↦ SobolevEuclidean.exists_eLpNorm_fn_chartExtendL_le (p := p) (c i)
  refine SobolevEuclidean.exists_extensionL_of_ops (U := fun i ↦ (c i).opensU)
    (Ωc := fun i ↦ (c i).opensInter) (fun i ↦ rfl)
    (SobolevMultiIndex.extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p
      volume hα₀)
    (fun i ↦ SobolevMultiIndex.extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      p volume (hα i))
    (fun i ↦ SobolevEuclidean.chartExtendL p (c i)) (fun x _ ↦ ?_) (fun i x hx ↦ ?_)
    (fun u ↦ SobolevMultiIndex.fn_extendZeroMulL hα₀ u)
    (fun i w ↦ SobolevMultiIndex.fn_extendZeroMulL (hα i) w)
    (fun i u ↦ SobolevEuclidean.chartExtendL_fn_ae_eq (c i) u)
    (A₀ := ENNReal.ofReal M₀) (A := fun i ↦ ENNReal.ofReal (M i)) ENNReal.ofReal_ne_top
    (fun i ↦ ENNReal.ofReal_ne_top) hB
    (fun u ↦ SobolevMultiIndex.eLpNorm_fn_extendZeroMulL_le hα₀ (fun x ↦ (hM₀ x).1) u)
    (fun i w ↦ SobolevMultiIndex.eLpNorm_fn_extendZeroMulL_le (hα i) (fun x ↦ (hM i x).1) w) hBu
  · rw [← Finset.sum_mul, ← add_mul, hsum x, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hθU i h), zero_mul]

/-- **Theorem 9.7 (the extension operator)** of [brezis2011functional] §9.2: for an open set `Ω`
of class `C^1` with bounded boundary and `1 ≤ p ≤ ∞`, there are a bounded linear
`P : W^{1,p}(Ω) →L[ℝ] W^{1,p}(ℝ^N)` and a constant `C` (depending on `Ω` and `p` only) with
`P u = u` on `Ω`, `‖P u‖_{L^p(ℝ^N)} ≤ C ‖u‖_{L^p(Ω)}` and
`‖P u‖_{W^{1,p}(ℝ^N)} ≤ C ‖u‖_{W^{1,p}(Ω)}`
for every `u`. This is `SobolevEuclidean.exists_extensionL_of_atlas` for `K = ∂Ω` (compact, as
closed and bounded), the finite atlas `IsContDiffChartDomain.exists_finite_atlas` and `χ = 1`. -/
theorem SobolevEuclidean.exists_extensionL
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ (P : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
        SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)) ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨k, c, hc⟩ := hΩ.exists_finite_atlas hΓ
  obtain ⟨P, C, hP⟩ := SobolevEuclidean.exists_extensionL_of_atlas (p := p)
    (Metric.isCompact_of_isClosed_isBounded isClosed_frontier hΓ) c hc
    (contDiff_const (c := (1 : ℝ))) ⟨1, fun x ↦ by simp⟩ inter_subset_right
  exact ⟨P, C, fun u ↦ hP u (Eventually.of_forall fun x ↦ (one_mul _).symm)⟩

/-- **Theorem 9.7 as an instance of the abstract predicate of `Cutoff.lean`**: an open set of
class `C^1` with bounded boundary is a `W^{1,p}`-extension domain for every `1 ≤ p ≤ ∞`. -/
theorem IsSobolevExtensionDomain.of_isContDiffChartDomain
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    IsSobolevExtensionDomain (d + 1) p Ω := by
  obtain ⟨P, C, hP⟩ := SobolevEuclidean.exists_extensionL (p := p) hΩ hΓ
  exact ⟨P.comp (Submodule.subtypeL _), fun u ↦ (hP u).1⟩

/-- **Theorem 9.7 for the graph domains of Atkinson–Han**: an `IsContDiffDomain 1 Ω` with bounded
boundary is a `W^{1,p}`-extension domain, through the bridge
`IsContDiffDomain.isContDiffChartDomain`. -/
theorem IsSobolevExtensionDomain.of_isContDiffDomain
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    IsSobolevExtensionDomain (d + 1) p Ω :=
  IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ.isContDiffChartDomain hΓ

/-- **Corollary 9.8 (density), bounded boundary**: for an open set `Ω` of class `C^1` with
bounded boundary and `1 ≤ p < ∞`, every `u ∈ W^{1,p}(Ω)` is the limit in `W^{1,p}(Ω)` of
restrictions of `C_c^∞(ℝ^N)` functions — the abstract density
`SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn` applied
to the extension operator of Theorem 9.7 ([brezis2011functional] Corollary 9.8, first paragraph
of the proof). -/
theorem SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_isBounded_frontier
    (hp' : p ≠ ⊤) (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧
      (∀ n, HasCompactSupport (v n)) ∧ ∃ w : ℕ → SobolevEuclidean (d + 1) 1 p Ω,
        (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume.restrict (Ω : Set _)] v n) ∧
        Tendsto w atTop (𝓝 u) :=
  SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn hp'
    (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ hΓ) ⟨u, Submodule.mem_top⟩

end Theorem97

/-! ### Corollary 9.8 on a general `C^1` domain -/

section Corollary98

/-- `‖c⁻¹ • x‖ ≤ r` if and only if `‖x‖ ≤ c r`, for `c > 0`. -/
theorem norm_inv_smul_le_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    (hc : 0 < c) (x : E) (r : ℝ) : ‖c⁻¹ • x‖ ≤ r ↔ ‖x‖ ≤ c * r := by
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hc, inv_mul_le_iff₀ hc]

/-- `‖c⁻¹ • x‖ < r` if and only if `‖x‖ < c r`, for `c > 0`. -/
theorem norm_inv_smul_lt_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    (hc : 0 < c) (x : E) (r : ℝ) : ‖c⁻¹ • x‖ < r ↔ ‖x‖ < c * r := by
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hc, inv_mul_lt_iff₀ hc]

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **Corollary 9.8 (density), one `ε` at a time**: for an open set `Ω` of class `C^1` (with no
boundedness of `∂Ω`), `1 ≤ p < ∞`, `u ∈ W^{1,p}(Ω)` and `ε > 0`, there are `v ∈ C_c^∞(ℝ^N)` and
`w ∈ W^{1,p}(Ω)` with `w = v` on `Ω` and `‖w − u‖ < ε`. The proof of [brezis2011functional]
Corollary 9.8, second paragraph: `‖ζ_R u − u‖ < ε/2` for `R` large
(`SobolevMultiIndex.tendsto_cutoff_smul`); `ζ_R u` vanishes off `ball 0 (2R)`, so the extension
operator of `SobolevEuclidean.exists_extensionL_of_atlas` for the compact
`K = ∂Ω ∩ closedBall 0 (4R)`, a finite atlas covering it, and a cut-off `χ` equal to `1` on
`closedBall 0 (2R)` and supported in `closedBall 0 (4R)` extends the line `ℝ ζ_R u`; the abstract
density `SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn`
on that line gives `v` and `w` with `‖w − ζ_R u‖ < ε/2`. -/
theorem SobolevEuclidean.exists_contDiff_hasCompactSupport_norm_sub_lt (hp' : p ≠ ⊤)
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (u : SobolevEuclidean (d + 1) 1 p Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) (w : SobolevEuclidean (d + 1) 1 p Ω),
      ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
        SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set _)] v ∧ ‖w - u‖ < ε := by
  obtain ⟨ζ, hζ, hζ1, hζs, hζ01⟩ :=
    exists_contDiff_eqOn_one_closedBall_one (EuclideanSpace ℝ (Fin (d + 1)))
  obtain ⟨V, hV, -, hVt⟩ := SobolevMultiIndex.tendsto_cutoff_smul hp' hζ hζ01 hζ1
    (hζs.trans ball_subset_closedBall) u
  obtain ⟨n, hn⟩ := (Metric.tendsto_atTop.1 hVt) (ε / 2) (half_pos hε)
  have hVn : ‖V n - u‖ < ε / 2 := by simpa [dist_eq_norm] using hn n le_rfl
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (n : ℝ) + 1 := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; positivity
  have h2R : 0 < 2 * R := mul_pos two_pos hR
  have hn1 : (0 : ℝ) < n + 1 := hRdef ▸ hR
  -- the cut-off `χ`, equal to `1` on `closedBall 0 (2R)` and supported in `closedBall 0 (4R)`
  obtain ⟨χ, hχdef⟩ : ∃ χ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
    χ = fun x ↦ ζ ((2 * R)⁻¹ • x) := ⟨_, rfl⟩
  have hχ : ContDiff ℝ ∞ χ := hχdef ▸ hζ.comp (contDiff_id.const_smul _)
  have hχ1 : ∀ x, ‖x‖ ≤ 2 * R → χ x = 1 := fun x hx ↦ by
    rw [hχdef]
    exact hζ1 (mem_closedBall_zero_iff.2 ((norm_inv_smul_le_iff h2R x 1).2 (by linarith)))
  have hχs : tsupport χ ⊆ closedBall 0 (4 * R) := by
    refine closure_minimal (fun x hx ↦ mem_closedBall_zero_iff.2 ?_) isClosed_closedBall
    have h0 : ζ ((2 * R)⁻¹ • x) ≠ 0 := by rw [hχdef] at hx; exact hx
    have h := (norm_inv_smul_lt_iff h2R x 2).1 (mem_ball_zero_iff.1 (hζs (subset_closure h0)))
    linarith
  have hχc : HasCompactSupport χ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall _ _) (isClosed_tsupport _) hχs
  have hχb : ∃ M, ∀ x, |χ x| ≤ M ∧ ‖fderiv ℝ χ x‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hχc.fderiv ℝ).exists_bound_of_continuous (hχ.continuous_fderiv (by simp))
    refine ⟨max 1 M, fun x ↦ ⟨?_, (hM x).trans (le_max_right _ _)⟩⟩
    rw [hχdef]
    exact (abs_le.2 ⟨by linarith [(hζ01 ((2 * R)⁻¹ • x)).1], (hζ01 ((2 * R)⁻¹ • x)).2⟩).trans
      (le_max_left _ _)
  -- the compact piece of the boundary and its atlas
  have hK : IsCompact
      (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ closedBall 0 (4 * R)) :=
    (isCompact_closedBall _ _).inter_left isClosed_frontier
  have hχK : tsupport χ ∩ frontier (Ω : Set _)
      ⊆ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ closedBall 0 (4 * R) :=
    fun x hx ↦ ⟨hx.2, hχs hx.1⟩
  obtain ⟨k, c, hc⟩ := hΩ.exists_finite_atlas_of_isCompact hK inter_subset_left
  obtain ⟨P, C, hP⟩ := SobolevEuclidean.exists_extensionL_of_atlas (p := p) hK c hc hχ hχb hχK
  -- the extension operator on the line `ℝ ζ_R u`
  have hχζ : ∀ (a t : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))),
      a * (ζ ((n + 1 : ℝ)⁻¹ • x) * t) = χ x * (a * (ζ ((n + 1 : ℝ)⁻¹ • x) * t)) := by
    intro a t x
    by_cases h0 : ζ ((n + 1 : ℝ)⁻¹ • x) = 0
    · rw [h0]; ring
    · have hmem := (norm_inv_smul_lt_iff hn1 x 2).1 (mem_ball_zero_iff.1 (hζs (subset_closure h0)))
      rw [hχ1 x (by rw [hRdef]; linarith), one_mul]
  have key : ∀ z : SobolevEuclidean (d + 1) 1 p Ω, (∃ a : ℝ, a • V n = z) →
      SobolevMultiIndex.fn z =ᵐ[volume.restrict (Ω : Set _)]
        fun x ↦ χ x * SobolevMultiIndex.fn z x := by
    rintro z ⟨a, rfl⟩
    filter_upwards [SobolevMultiIndex.fn_smul a (V n), hV n] with x hx hxV
    have hA : SobolevMultiIndex.fn (a • V n) x
        = a * (ζ ((n + 1 : ℝ)⁻¹ • x) * SobolevMultiIndex.fn u x) :=
      hx.trans (congrArg (a * ·) hxV)
    exact hA.trans ((hχζ a _ x).trans (congrArg (χ x * ·) hA.symm))
  have hS : HasSobolevExtensionOn (ℝ ∙ V n) :=
    ⟨P.comp (Submodule.subtypeL _), fun w ↦ (hP w (key w (Submodule.mem_span_singleton.1 w.2))).1⟩
  obtain ⟨vv, hvv, hvvc, ww, hww, hwwt⟩ :=
    SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn hp'
      hS ⟨V n, Submodule.mem_span_singleton_self _⟩
  obtain ⟨m, hm⟩ := (Metric.tendsto_atTop.1 hwwt) (ε / 2) (half_pos hε)
  refine ⟨vv m, ww m, hvv m, hvvc m, hww m, ?_⟩
  calc ‖ww m - u‖ ≤ ‖ww m - V n‖ + ‖V n - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by simpa [dist_eq_norm] using hm m le_rfl) hVn
    _ = ε := add_halves ε

/-- **Corollary 9.8 (density), general `C^1` domain** of [brezis2011functional]: for an open set
`Ω` of class `C^1` — its boundary need not be bounded — and `1 ≤ p < ∞`, every
`u ∈ W^{1,p}(Ω)` is the limit in `W^{1,p}(Ω)` of restrictions of `C_c^∞(ℝ^N)` functions. The
sequence is `SobolevEuclidean.exists_contDiff_hasCompactSupport_norm_sub_lt` at `ε = 1/(n+1)`. -/
theorem SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto (hp' : p ≠ ⊤)
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧
      (∀ n, HasCompactSupport (v n)) ∧ ∃ w : ℕ → SobolevEuclidean (d + 1) 1 p Ω,
        (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume.restrict (Ω : Set _)] v n) ∧
        Tendsto w atTop (𝓝 u) := by
  choose v w hv hvc hw hwu using fun n : ℕ ↦
    SobolevEuclidean.exists_contDiff_hasCompactSupport_norm_sub_lt hp' hΩ u
      (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨v, hv, hvc, w, hw, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ (hwu n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end Corollary98

/-! ### Remark 9: the square by four reflections -/

section Square

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Composition of two extension steps, with the composite as a variable: identities on `Ω`
compose, and the `L^p` bounds multiply. -/
theorem SobolevEuclidean.extension_step_comp {Ω Ω₀ Ω₁ Ω₂ : Opens (EuclideanSpace ℝ (Fin N))}
    (S : SobolevEuclidean N 1 p Ω₀ →L[ℝ] SobolevEuclidean N 1 p Ω₁)
    (S' : SobolevEuclidean N 1 p Ω₁ →L[ℝ] SobolevEuclidean N 1 p Ω₂)
    (S'' : SobolevEuclidean N 1 p Ω₀ →L[ℝ] SobolevEuclidean N 1 p Ω₂) (hS'' : ∀ u, S'' u = S' (S u))
    {C C' : ℝ≥0∞}
    (hS : ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
      eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (Ω₁ : Set _))
        ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₀ : Set _)))
    (hS' : ∀ w, SobolevMultiIndex.fn (S' w) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn w ∧
      eLpNorm (SobolevMultiIndex.fn (S' w)) p (volume.restrict (Ω₂ : Set _))
        ≤ C' * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (Ω₁ : Set _))) :
    ∀ u, SobolevMultiIndex.fn (S'' u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
      eLpNorm (SobolevMultiIndex.fn (S'' u)) p (volume.restrict (Ω₂ : Set _))
        ≤ C' * C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₀ : Set _)) := fun u ↦ by
  rw [hS'' u]
  exact ⟨(hS' (S u)).1.trans (hS u).1,
    (hS' (S u)).2.trans (by rw [mul_assoc]; gcongr; exact (hS u).2)⟩

/-- **A reflection across a translated hyperplane**, with the operators as variables: the
translation `T₁ : u ↦ u(· + c)` from `Ω₀` to `V₊ = posHalf v V`, the even reflection
`R : W^{1,p}(V₊) → W^{1,p}(V)`, and the translation back `T₂ : w ↦ w(· − c)` from `V` to `Ω₁`,
compose to an extension operator `Ω₀ → Ω₁` whose function agrees with `u` on `Ω₀`. -/
theorem SobolevEuclidean.exists_reflectionStep_of_ops {v c : EuclideanSpace ℝ (Fin N)}
    {V Ω₀ Ω₁ : Opens (EuclideanSpace ℝ (Fin N))}
    (h₀ : (posHalf v V : Set (EuclideanSpace ℝ (Fin N))) = (fun x ↦ x + c) ⁻¹' Ω₀)
    (h₁ : (Ω₁ : Set (EuclideanSpace ℝ (Fin N))) = (fun x ↦ x + -c) ⁻¹' V)
    (T₁ : SobolevEuclidean N 1 p Ω₀ →L[ℝ] SobolevEuclidean N 1 p (posHalf v V))
    (R : SobolevEuclidean N 1 p (posHalf v V) →L[ℝ] SobolevEuclidean N 1 p V)
    (T₂ : SobolevEuclidean N 1 p V →L[ℝ] SobolevEuclidean N 1 p Ω₁) {C₁ C₂ : ℝ≥0∞}
    (hT₁ : ∀ u, SobolevMultiIndex.fn (T₁ u) =ᵐ[volume.restrict (posHalf v V : Set _)]
      fun y ↦ SobolevMultiIndex.fn u (y + c))
    (hT₁L : ∀ u, eLpNorm (SobolevMultiIndex.fn (T₁ u)) p (volume.restrict (posHalf v V : Set _))
      ≤ C₁ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₀ : Set _)))
    (hR : ∀ w, SobolevMultiIndex.fn (R w) =ᵐ[volume.restrict (posHalf v V : Set _)]
      SobolevMultiIndex.fn w)
    (hRL : ∀ w, eLpNorm (SobolevMultiIndex.fn (R w)) p (volume.restrict (V : Set _))
      ≤ 2 * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (posHalf v V : Set _)))
    (hT₂ : ∀ w, SobolevMultiIndex.fn (T₂ w) =ᵐ[volume.restrict (Ω₁ : Set _)]
      fun y ↦ SobolevMultiIndex.fn w (y + -c))
    (hT₂L : ∀ w, eLpNorm (SobolevMultiIndex.fn (T₂ w)) p (volume.restrict (Ω₁ : Set _))
      ≤ C₂ * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (V : Set _))) :
    ∀ u, SobolevMultiIndex.fn (T₂ (R (T₁ u))) =ᵐ[volume.restrict (Ω₀ : Set _)]
        SobolevMultiIndex.fn u ∧
      eLpNorm (SobolevMultiIndex.fn (T₂ (R (T₁ u)))) p (volume.restrict (Ω₁ : Set _))
        ≤ C₂ * 2 * C₁ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₀ : Set _)) := by
  intro u
  have hΩ₀m : MeasurableSet (Ω₀ : Set (EuclideanSpace ℝ (Fin N))) := Ω₀.isOpen.measurableSet
  have hΩ₁m : MeasurableSet (Ω₁ : Set (EuclideanSpace ℝ (Fin N))) := Ω₁.isOpen.measurableSet
  have hPm : MeasurableSet (posHalf v V : Set (EuclideanSpace ℝ (Fin N))) :=
    (posHalf v V).isOpen.measurableSet
  -- membership bookkeeping
  have hmem : ∀ x, x ∈ (Ω₀ : Set _) → x + -c ∈ (posHalf v V : Set _) := fun x hx ↦ by
    rw [h₀]
    simpa using hx
  have hΩ₀₁ : (Ω₀ : Set (EuclideanSpace ℝ (Fin N))) ⊆ Ω₁ := fun x hx ↦ by
    rw [h₁]
    exact (hmem x hx).1
  refine ⟨?_, ?_⟩
  · -- the identity on `Ω₀`
    have h2 : ∀ᵐ x ∂volume, x ∈ (Ω₁ : Set _) →
        SobolevMultiIndex.fn (T₂ (R (T₁ u))) x = SobolevMultiIndex.fn (R (T₁ u)) (x + -c) :=
      (ae_restrict_iff' hΩ₁m).1 (hT₂ (R (T₁ u)))
    have h3 : ∀ᵐ y ∂volume, y ∈ (posHalf v V : Set _) →
        SobolevMultiIndex.fn (R (T₁ u)) y = SobolevMultiIndex.fn (T₁ u) y :=
      (ae_restrict_iff' hPm).1 (hR (T₁ u))
    have h4 : ∀ᵐ y ∂volume, y ∈ (posHalf v V : Set _) →
        SobolevMultiIndex.fn (T₁ u) y = SobolevMultiIndex.fn u (y + c) :=
      (ae_restrict_iff' hPm).1 (hT₁ u)
    have h3' := (measurePreserving_add_right volume (-c)).quasiMeasurePreserving.ae h3
    have h4' := (measurePreserving_add_right volume (-c)).quasiMeasurePreserving.ae h4
    rw [EventuallyEq, ae_restrict_iff' hΩ₀m]
    filter_upwards [h2, h3', h4'] with x hx2 hx3 hx4 hx
    rw [hx2 (hΩ₀₁ hx), hx3 (hmem x hx), hx4 (hmem x hx)]
    simp
  · -- the `L^p` bound
    calc eLpNorm (SobolevMultiIndex.fn (T₂ (R (T₁ u)))) p (volume.restrict (Ω₁ : Set _))
        ≤ C₂ * eLpNorm (SobolevMultiIndex.fn (R (T₁ u))) p (volume.restrict (V : Set _)) :=
          hT₂L _
      _ ≤ C₂ * (2 * eLpNorm (SobolevMultiIndex.fn (T₁ u)) p
          (volume.restrict (posHalf v V : Set _))) := by gcongr; exact hRL _
      _ ≤ C₂ * (2 * (C₁ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₀ : Set _)))) := by
          gcongr; exact hT₁L _
      _ = C₂ * 2 * C₁ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₀ : Set _)) := by
          ring

/-- **A reflection across a translated hyperplane**: for a unit vector `v`, a translation `c`, an
open `V` symmetric under the reflection `σ` across `v^⊥`, and opens `Ω₀`, `Ω₁` with
`V₊ = Ω₀ − c` and `Ω₁ = V + c`, there is a bounded linear `S : W^{1,p}(Ω₀) → W^{1,p}(Ω₁)` with
`S u = u` on `Ω₀` and `‖S u‖_{L^p(Ω₁)} ≤ C ‖u‖_{L^p(Ω₀)}`: translate by `c`
(`SobolevEuclidean.compDiffeoL` for the affine map), reflect (`SobolevEuclidean.evenReflectionL`),
translate back. This is one of the "four successive reflections" of [brezis2011functional]
Chapter 9, Remark 9. -/
theorem SobolevEuclidean.exists_reflectionStep {v c : EuclideanSpace ℝ (Fin N)} (hv : ‖v‖ = 1)
    {V Ω₀ Ω₁ : Opens (EuclideanSpace ℝ (Fin N))}
    (hV : hyperplaneReflection v '' (V : Set (EuclideanSpace ℝ (Fin N))) = V)
    (h₀ : (posHalf v V : Set (EuclideanSpace ℝ (Fin N))) = (fun x ↦ x + c) ⁻¹' Ω₀)
    (h₁ : (Ω₁ : Set (EuclideanSpace ℝ (Fin N))) = (fun x ↦ x + -c) ⁻¹' V) :
    ∃ (S : SobolevEuclidean N 1 p Ω₀ →L[ℝ] SobolevEuclidean N 1 p Ω₁) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω₀ : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (Ω₁ : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₀ : Set _)) := by
  -- the two translations as diffeomorphisms with bounded Jacobians
  have hd₁ := isDiffeoOnWithBoundedJacobian_affine
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N))) c Ω₀
  have hd₂ := isDiffeoOnWithBoundedJacobian_affine
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N))) (-c) V
  simp only [ContinuousLinearEquiv.coe_refl', id, ContinuousLinearEquiv.refl_symm] at hd₁ hd₂
  rw [← h₀] at hd₁
  rw [← h₁] at hd₂
  obtain ⟨C₁, hC₁, hT₁L⟩ := SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le
    (F := ℝ) (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (p := p) (μ := volume) hd₁
  obtain ⟨C₂, hC₂, hT₂L⟩ := SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le
    (F := ℝ) (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (p := p) (μ := volume) hd₂
  refine ⟨SobolevEuclidean.compDiffeoL hd₂ ∘L SobolevEuclidean.evenReflectionL hv hV ∘L
    SobolevEuclidean.compDiffeoL hd₁, C₂ * 2 * C₁,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hC₂ (by simp)) hC₁, ?_⟩
  exact SobolevEuclidean.exists_reflectionStep_of_ops h₀ h₁ (SobolevEuclidean.compDiffeoL hd₁)
    (SobolevEuclidean.evenReflectionL hv hV) (SobolevEuclidean.compDiffeoL hd₂)
    (fun u ↦ SobolevMultiIndex.fn_compDiffeoL hd₁ u) hT₁L
    (fun w ↦ SobolevMultiIndex.fn_evenReflectionL_restrict hv hV w)
    (fun w ↦ SobolevMultiIndex.eLpNorm_fn_evenReflectionL_le hv hV w)
    (fun w ↦ SobolevMultiIndex.fn_compDiffeoL hd₂ w) hT₂L


/-- An extension operator with an `ℝ≥0∞` constant has the shape of Theorem 9.7: the constant
`max C.toReal ‖P‖` serves both the `L^p` bound and the operator bound. -/
theorem SobolevEuclidean.exists_extensionL_of_ops' {Ω : Opens (EuclideanSpace ℝ (Fin N))}
    (P : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hP : ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
      eLpNorm (SobolevMultiIndex.fn (P u)) p
          (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _))
        ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _))) :
    ∃ (P : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)) ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  refine ⟨P, max C.toReal ‖P‖, fun u ↦ ⟨(hP u).1, ?_, ?_⟩⟩
  · rw [← eLpNorm_restrict_coe_top]
    refine (hP u).2.trans ?_
    gcongr
    exact (ENNReal.ofReal_toReal hC).symm.le.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · exact (P.le_opNorm u).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- **Assembly of an extension operator from four steps and a cut-off**, with the sets as
variables: extension steps `Ω → Ω₁ → Ω₂ → Ω₃ → Ω₄`, each the identity on its source, followed
by a cut-off `Ω₄ → ℝ^N` which is the identity on `Ω`, give an extension operator `Ω → ℝ^N` in
the shape of Theorem 9.7. -/
theorem SobolevEuclidean.exists_extensionL_of_steps
    {Ω Ω₁ Ω₂ Ω₃ Ω₄ : Opens (EuclideanSpace ℝ (Fin N))}
    (hΩ₁ : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ Ω₁)
    (hΩ₂ : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ Ω₂)
    (hΩ₃ : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ Ω₃)
    (h₁ : ∃ (S : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p Ω₁) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (Ω₁ : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)))
    (h₂ : ∃ (S : SobolevEuclidean N 1 p Ω₁ →L[ℝ] SobolevEuclidean N 1 p Ω₂) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω₁ : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (Ω₂ : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₁ : Set _)))
    (h₃ : ∃ (S : SobolevEuclidean N 1 p Ω₂ →L[ℝ] SobolevEuclidean N 1 p Ω₃) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω₂ : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (Ω₃ : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₂ : Set _)))
    (h₄ : ∃ (S : SobolevEuclidean N 1 p Ω₃ →L[ℝ] SobolevEuclidean N 1 p Ω₄) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω₃ : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (Ω₄ : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₃ : Set _)))
    (h₅ : ∃ E : SobolevEuclidean N 1 p Ω₄ →L[ℝ] SobolevEuclidean N 1 p ⊤, ∀ w,
      SobolevMultiIndex.fn (E w) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn w ∧
      eLpNorm (SobolevMultiIndex.fn (E w)) p
          (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _))
        ≤ ENNReal.ofReal 1 * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (Ω₄ : Set _))) :
    ∃ (P : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)) ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨S₁, C₁, hC₁, hS₁⟩ := h₁
  obtain ⟨S₂, C₂, hC₂, hS₂⟩ := h₂
  obtain ⟨S₃, C₃, hC₃, hS₃⟩ := h₃
  obtain ⟨S₄, C₄, hC₄, hS₄⟩ := h₄
  obtain ⟨E, hE⟩ := h₅
  have hres : ∀ {A B : Opens (EuclideanSpace ℝ (Fin N))}
      (h : (A : Set (EuclideanSpace ℝ (Fin N))) ⊆ (B : Set (EuclideanSpace ℝ (Fin N))))
      {f g : EuclideanSpace ℝ (Fin N) → ℝ},
      f =ᵐ[volume.restrict (B : Set _)] g → f =ᵐ[volume.restrict (A : Set _)] g := by
    intro _ _ h _ _ hfg
    exact hfg.filter_mono (ae_mono (Measure.restrict_mono h le_rfl))
  have hS₂' := fun u ↦ (hS₂ u).imp_left (hres hΩ₁)
  have hS₃' := fun u ↦ (hS₃ u).imp_left (hres hΩ₂)
  have hS₄' := fun u ↦ (hS₄ u).imp_left (hres hΩ₃)
  -- the composite, one operator at a time
  obtain ⟨P₂, hP₂⟩ : ∃ P₂ : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p Ω₂,
      ∀ u, P₂ u = S₂ (S₁ u) := ⟨S₂ ∘L S₁, fun u ↦ rfl⟩
  have h₂' := SobolevEuclidean.extension_step_comp S₁ S₂ P₂ hP₂ hS₁ hS₂'
  obtain ⟨P₃, hP₃⟩ : ∃ P₃ : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p Ω₃,
      ∀ u, P₃ u = S₃ (P₂ u) := ⟨S₃ ∘L P₂, fun u ↦ rfl⟩
  have h₃' := SobolevEuclidean.extension_step_comp P₂ S₃ P₃ hP₃ h₂' hS₃'
  obtain ⟨P₄, hP₄⟩ : ∃ P₄ : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p Ω₄,
      ∀ u, P₄ u = S₄ (P₃ u) := ⟨S₄ ∘L P₃, fun u ↦ rfl⟩
  have h₄' := SobolevEuclidean.extension_step_comp P₃ S₄ P₄ hP₄ h₃' hS₄'
  obtain ⟨P, hP⟩ : ∃ P : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤,
      ∀ u, P u = E (P₄ u) := ⟨E ∘L P₄, fun u ↦ rfl⟩
  have h₅' := SobolevEuclidean.extension_step_comp P₄ E P hP h₄' hE
  exact SobolevEuclidean.exists_extensionL_of_ops' P
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hC₄ (ENNReal.mul_ne_top hC₃
      (ENNReal.mul_ne_top hC₂ hC₁)))) h₅'

/-- The reflection across `x_i = 0` in coordinates: `σ x j = if j = i then −x i else x j`. -/
theorem hyperplaneReflection_single_apply (i : Fin N) (x : EuclideanSpace ℝ (Fin N)) (j : Fin N) :
    hyperplaneReflection (EuclideanSpace.single i (1 : ℝ)) x j
      = if j = i then -x i else x j := by
  rw [hyperplaneReflection_apply_of_norm_eq_one (by simp), EuclideanSpace.inner_single_right,
    PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  simp only [conj_trivial, one_mul]
  split_ifs with h
  · subst h; ring
  · ring

/-- The reflections across `v^⊥` and `(−v)^⊥` coincide. -/
theorem hyperplaneReflection_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) : hyperplaneReflection (-v) = hyperplaneReflection v := by
  have h : (ℝ ∙ -v) = (ℝ ∙ v) := by rw [← Set.neg_singleton, Submodule.span_neg]
  unfold hyperplaneReflection
  simp only [h]

/-- The open rectangle `(a₁, b₁) × (a₂, b₂)` of `ℝ²`. -/
def EuclideanSpace.rect (a₁ b₁ a₂ b₂ : ℝ) : Opens (EuclideanSpace ℝ (Fin 2)) :=
  ⟨{x | a₁ < x 0 ∧ x 0 < b₁ ∧ a₂ < x 1 ∧ x 1 < b₂}, by
    have h0 : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0 :=
      (EuclideanSpace.proj (0 : Fin 2)).continuous
    have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1 :=
      (EuclideanSpace.proj (1 : Fin 2)).continuous
    exact (isOpen_lt continuous_const h0).inter ((isOpen_lt h0 continuous_const).inter
      ((isOpen_lt continuous_const h1).inter (isOpen_lt h1 continuous_const)))⟩

/-- Membership of the rectangle, unfolded. -/
theorem EuclideanSpace.mem_rect {a₁ b₁ a₂ b₂ : ℝ} {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ (EuclideanSpace.rect a₁ b₁ a₂ b₂ : Set (EuclideanSpace ℝ (Fin 2)))
      ↔ a₁ < x 0 ∧ x 0 < b₁ ∧ a₂ < x 1 ∧ x 1 < b₂ :=
  Iff.rfl

/-- The norm of a point of `ℝ²` is at most the sum of the absolute values of its coordinates. -/
theorem EuclideanSpace.norm_le_abs_add_abs (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ≤ |x 0| + |x 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs]
  refine (Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq (by positivity))
  nlinarith [sq_abs (x 0), sq_abs (x 1), mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1))]

/-- A rectangle is bounded. -/
theorem EuclideanSpace.rect_subset_closedBall (a₁ b₁ a₂ b₂ : ℝ) :
    (EuclideanSpace.rect a₁ b₁ a₂ b₂ : Set (EuclideanSpace ℝ (Fin 2)))
      ⊆ closedBall 0 (max |a₁| |b₁| + max |a₂| |b₂|) := by
  intro x hx
  rw [EuclideanSpace.mem_rect] at hx
  rw [mem_closedBall_zero_iff]
  refine (EuclideanSpace.norm_le_abs_add_abs x).trans (add_le_add ?_ ?_)
  · exact abs_le.2 ⟨by linarith [neg_abs_le a₁, le_max_left |a₁| |b₁|],
      by linarith [le_abs_self b₁, le_max_right |a₁| |b₁|]⟩
  · exact abs_le.2 ⟨by linarith [neg_abs_le a₂, le_max_left |a₂| |b₂|],
      by linarith [le_abs_self b₂, le_max_right |a₂| |b₂|]⟩

/-- The closure of the unit square lies in the closed square, hence in `(−1, 3)²`. -/
theorem EuclideanSpace.closure_rect_unit_subset :
    closure (EuclideanSpace.rect 0 1 0 1 : Set (EuclideanSpace ℝ (Fin 2)))
      ⊆ {x | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1} := by
  have h0 : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0 :=
    (EuclideanSpace.proj (0 : Fin 2)).continuous
  have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1 :=
    (EuclideanSpace.proj (1 : Fin 2)).continuous
  refine closure_minimal (fun x hx ↦ ?_) ((isClosed_le continuous_const h0).inter
    ((isClosed_le h0 continuous_const).inter
      ((isClosed_le continuous_const h1).inter (isClosed_le h1 continuous_const))))
  rw [EuclideanSpace.mem_rect] at hx
  exact ⟨hx.1.le, hx.2.1.le, hx.2.2.1.le, hx.2.2.2.le⟩

/-- The reflection across `x_2 = 0` of Remark 9: an extension operator
`W^{1,p}(0 1 0 1) → W^{1,p}(0 1 −1 1)`. -/
theorem SobolevEuclidean.exists_extension_rect_step₁ :
    ∃ (S : SobolevEuclidean 2 1 p (EuclideanSpace.rect 0 1 0 1) →L[ℝ]
        SobolevEuclidean 2 1 p (EuclideanSpace.rect 0 1 (-1) 1)) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u)
          =ᵐ[volume.restrict (EuclideanSpace.rect 0 1 0 1 : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p
            (volume.restrict (EuclideanSpace.rect 0 1 (-1) 1 : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (EuclideanSpace.rect 0 1 0 1 : Set _)) := by
  have he : ∀ i : Fin 2, ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by simp
  have hne : ∀ i : Fin 2, ‖(-EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by rw [norm_neg]; exact he i
  have hinv : ∀ i : Fin 2, Function.Involutive
      (hyperplaneReflection (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))) :=
    fun i x ↦ hyperplaneReflection_hyperplaneReflection _ x
  exact SobolevEuclidean.exists_reflectionStep (p := p)
    (v := EuclideanSpace.single 1 (1 : ℝ)) (c := 0) (he 1)
    (V := EuclideanSpace.rect 0 1 (-1) 1) (Ω₀ := EuclideanSpace.rect 0 1 0 1)
    (Ω₁ := EuclideanSpace.rect 0 1 (-1) 1)
    (by
      refine (hinv 1).image_eq_of_forall_mem_iff fun x ↦ ?_
      simp only [EuclideanSpace.mem_rect, hyperplaneReflection_single_apply, Fin.isValue,
        zero_ne_one, ↓reduceIte]
      constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
    (by
      ext x
      simp only [coe_posHalf, EuclideanSpace.inner_single_right, conj_trivial, one_mul,
        Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, add_zero, EuclideanSpace.mem_rect]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨h1, h2, h5, h4⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨⟨h1, h2, by linarith, h4⟩, h3⟩)
    (by
      ext x
      simp)
/-- The reflection across `x_2 = 1` of Remark 9: an extension operator
`W^{1,p}(0 1 −1 1) → W^{1,p}(0 1 −1 3)`. -/
theorem SobolevEuclidean.exists_extension_rect_step₂ :
    ∃ (S : SobolevEuclidean 2 1 p (EuclideanSpace.rect 0 1 (-1) 1) →L[ℝ]
        SobolevEuclidean 2 1 p (EuclideanSpace.rect 0 1 (-1) 3)) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u)
          =ᵐ[volume.restrict (EuclideanSpace.rect 0 1 (-1) 1 : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p
            (volume.restrict (EuclideanSpace.rect 0 1 (-1) 3 : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (EuclideanSpace.rect 0 1 (-1) 1 : Set _)) := by
  have he : ∀ i : Fin 2, ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by simp
  have hne : ∀ i : Fin 2, ‖(-EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by rw [norm_neg]; exact he i
  have hinv : ∀ i : Fin 2, Function.Involutive
      (hyperplaneReflection (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))) :=
    fun i x ↦ hyperplaneReflection_hyperplaneReflection _ x
  exact SobolevEuclidean.exists_reflectionStep (p := p)
    (v := -EuclideanSpace.single 1 (1 : ℝ)) (c := EuclideanSpace.single 1 (1 : ℝ)) (hne 1)
    (V := EuclideanSpace.rect 0 1 (-2) 2) (Ω₀ := EuclideanSpace.rect 0 1 (-1) 1)
    (Ω₁ := EuclideanSpace.rect 0 1 (-1) 3)
    (by
      rw [hyperplaneReflection_neg]
      refine (hinv 1).image_eq_of_forall_mem_iff fun x ↦ ?_
      simp only [EuclideanSpace.mem_rect, hyperplaneReflection_single_apply, Fin.isValue,
        zero_ne_one, ↓reduceIte]
      constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
    (by
      ext x
      simp only [coe_posHalf, inner_neg_right, EuclideanSpace.inner_single_right, conj_trivial,
        one_mul, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, EuclideanSpace.mem_rect,
        PiLp.add_apply, PiLp.single_apply, Fin.isValue, zero_ne_one, ↓reduceIte, add_zero]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨h1, h2, by linarith, by linarith⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨⟨h1, h2, by linarith, by linarith⟩, by linarith⟩)
    (by
      ext x
      simp only [Set.mem_preimage, EuclideanSpace.mem_rect, PiLp.add_apply, PiLp.neg_apply,
        PiLp.single_apply, Fin.isValue, zero_ne_one, ↓reduceIte, neg_zero, add_zero]
      constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
/-- The reflection across `x_1 = 0` of Remark 9: an extension operator
`W^{1,p}(0 1 −1 3) → W^{1,p}(−1 1 −1 3)`. -/
theorem SobolevEuclidean.exists_extension_rect_step₃ :
    ∃ (S : SobolevEuclidean 2 1 p (EuclideanSpace.rect 0 1 (-1) 3) →L[ℝ]
        SobolevEuclidean 2 1 p (EuclideanSpace.rect (-1) 1 (-1) 3)) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u)
          =ᵐ[volume.restrict (EuclideanSpace.rect 0 1 (-1) 3 : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p
            (volume.restrict (EuclideanSpace.rect (-1) 1 (-1) 3 : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (EuclideanSpace.rect 0 1 (-1) 3 : Set _)) := by
  have he : ∀ i : Fin 2, ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by simp
  have hne : ∀ i : Fin 2, ‖(-EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by rw [norm_neg]; exact he i
  have hinv : ∀ i : Fin 2, Function.Involutive
      (hyperplaneReflection (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))) :=
    fun i x ↦ hyperplaneReflection_hyperplaneReflection _ x
  exact SobolevEuclidean.exists_reflectionStep (p := p)
    (v := EuclideanSpace.single 0 (1 : ℝ)) (c := 0) (he 0)
    (V := EuclideanSpace.rect (-1) 1 (-1) 3) (Ω₀ := EuclideanSpace.rect 0 1 (-1) 3)
    (Ω₁ := EuclideanSpace.rect (-1) 1 (-1) 3)
    (by
      refine (hinv 0).image_eq_of_forall_mem_iff fun x ↦ ?_
      simp only [EuclideanSpace.mem_rect, hyperplaneReflection_single_apply, Fin.isValue,
        one_ne_zero, ↓reduceIte]
      constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
    (by
      ext x
      simp only [coe_posHalf, EuclideanSpace.inner_single_right, conj_trivial, one_mul,
        Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, add_zero, EuclideanSpace.mem_rect]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨h5, h2, h3, h4⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨⟨by linarith, h2, h3, h4⟩, h1⟩)
    (by
      ext x
      simp)
/-- The reflection across `x_1 = 1` of Remark 9: an extension operator
`W^{1,p}(−1 1 −1 3) → W^{1,p}(−1 3 −1 3)`. -/
theorem SobolevEuclidean.exists_extension_rect_step₄ :
    ∃ (S : SobolevEuclidean 2 1 p (EuclideanSpace.rect (-1) 1 (-1) 3) →L[ℝ]
        SobolevEuclidean 2 1 p (EuclideanSpace.rect (-1) 3 (-1) 3)) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u)
          =ᵐ[volume.restrict (EuclideanSpace.rect (-1) 1 (-1) 3 : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p
            (volume.restrict (EuclideanSpace.rect (-1) 3 (-1) 3 : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (EuclideanSpace.rect (-1) 1 (-1) 3 : Set _)) := by
  have he : ∀ i : Fin 2, ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by simp
  have hne : ∀ i : Fin 2, ‖(-EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by rw [norm_neg]; exact he i
  have hinv : ∀ i : Fin 2, Function.Involutive
      (hyperplaneReflection (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))) :=
    fun i x ↦ hyperplaneReflection_hyperplaneReflection _ x
  exact SobolevEuclidean.exists_reflectionStep (p := p)
    (v := -EuclideanSpace.single 0 (1 : ℝ)) (c := EuclideanSpace.single 0 (1 : ℝ)) (hne 0)
    (V := EuclideanSpace.rect (-2) 2 (-1) 3) (Ω₀ := EuclideanSpace.rect (-1) 1 (-1) 3)
    (Ω₁ := EuclideanSpace.rect (-1) 3 (-1) 3)
    (by
      rw [hyperplaneReflection_neg]
      refine (hinv 0).image_eq_of_forall_mem_iff fun x ↦ ?_
      simp only [EuclideanSpace.mem_rect, hyperplaneReflection_single_apply, Fin.isValue,
        one_ne_zero, ↓reduceIte]
      constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
    (by
      ext x
      simp only [coe_posHalf, inner_neg_right, EuclideanSpace.inner_single_right, conj_trivial,
        one_mul, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, EuclideanSpace.mem_rect,
        PiLp.add_apply, PiLp.single_apply, Fin.isValue, one_ne_zero, ↓reduceIte, add_zero]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨by linarith, by linarith, h3, h4⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨⟨by linarith, by linarith, h3, h4⟩, by linarith⟩)
    (by
      ext x
      simp only [Set.mem_preimage, EuclideanSpace.mem_rect, PiLp.add_apply, PiLp.neg_apply,
        PiLp.single_apply, Fin.isValue, one_ne_zero, ↓reduceIte, neg_zero, add_zero]
      constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
/-- The cut-off of Remark 9: a bounded linear `E : W^{1,p}((−1, 3)²) → W^{1,p}(ℝ²)`, `w ↦ ψ w`
extended by zero for a smooth `ψ` equal to `1` on the unit square and supported in `(−1, 3)²`,
so that `E w = w` on the square and `‖E w‖_{L^p(ℝ²)} ≤ ‖w‖_{L^p((−1, 3)²)}`. -/
theorem SobolevEuclidean.exists_extension_rect_cutoff :
    ∃ E : SobolevEuclidean 2 1 p (EuclideanSpace.rect (-1) 3 (-1) 3) →L[ℝ]
      SobolevEuclidean 2 1 p ⊤, ∀ w,
      SobolevMultiIndex.fn (E w)
        =ᵐ[volume.restrict (EuclideanSpace.rect 0 1 0 1 : Set _)] SobolevMultiIndex.fn w ∧
      eLpNorm (SobolevMultiIndex.fn (E w)) p
          (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin 2))) : Set _))
        ≤ ENNReal.ofReal 1 * eLpNorm (SobolevMultiIndex.fn w) p
          (volume.restrict (EuclideanSpace.rect (-1) 3 (-1) 3 : Set _)) := by
  -- the cut-off
  have hKc : IsCompact (closure (EuclideanSpace.rect 0 1 0 1 : Set (EuclideanSpace ℝ (Fin 2)))) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (((Metric.isBounded_iff_subset_closedBall 0).2
        ⟨_, EuclideanSpace.rect_subset_closedBall 0 1 0 1⟩).closure)
  have hKV : closure (EuclideanSpace.rect 0 1 0 1 : Set (EuclideanSpace ℝ (Fin 2)))
      ⊆ EuclideanSpace.rect (-1) 3 (-1) 3 := fun x hx ↦ by
    have h := EuclideanSpace.closure_rect_unit_subset hx
    rw [SetLike.mem_coe, ← SetLike.mem_coe, EuclideanSpace.mem_rect]
    exact ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2.1], by linarith [h.2.2.2]⟩
  obtain ⟨ψ, hψs, hψ1, hψsupp, hψ01⟩ :=
    hKc.exists_contDiff_eqOn_one (EuclideanSpace.rect (-1) 3 (-1) 3).isOpen hKV
  have hψc : HasCompactSupport ψ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 _) (isClosed_tsupport ψ)
      (hψsupp.trans (EuclideanSpace.rect_subset_closedBall (-1) 3 (-1) 3))
  have hcut : IsSobolevCutoff (EuclideanSpace.rect (-1) 3 (-1) 3) ψ :=
    IsSobolevCutoff.of_hasCompactSupport hψs hψc hψsupp
  have hψM : ∀ x, |ψ x| ≤ 1 := fun x ↦
    abs_le.2 ⟨by linarith [(hψ01 x).1], (hψ01 x).2⟩
  have hΩ₄ : (EuclideanSpace.rect 0 1 0 1 : Set (EuclideanSpace ℝ (Fin 2)))
      ⊆ EuclideanSpace.rect (-1) 3 (-1) 3 := fun x hx ↦ by
    rw [EuclideanSpace.mem_rect] at hx ⊢
    exact ⟨by linarith [hx.1], by linarith [hx.2.1], by linarith [hx.2.2.1],
      by linarith [hx.2.2.2]⟩
  refine ⟨SobolevMultiIndex.extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis p
    volume hcut, fun w ↦ ⟨?_, ?_⟩⟩
  · have h := (SobolevMultiIndex.fn_extendZeroMulL_restrict hcut w).filter_mono
      (ae_mono (Measure.restrict_mono hΩ₄ le_rfl))
    rw [EventuallyEq, ae_restrict_iff' (EuclideanSpace.rect 0 1 0 1).isOpen.measurableSet] at h ⊢
    filter_upwards [h] with x hx hxΩ
    rw [hx hxΩ, hψ1 (subset_closure hxΩ), Pi.one_apply, one_smul]
  · rw [eLpNorm_restrict_coe_top]
    exact SobolevMultiIndex.eLpNorm_fn_extendZeroMulL_le hcut hψM w

/-- **Remark 9: the unit square has an extension operator**, although it is not of class `C^1`:
for `Ω = (0, 1) × (0, 1) ⊆ ℝ²` (`EuclideanSpace.rect 0 1 0 1`) and `1 ≤ p ≤ ∞` there are a
bounded linear `P : W^{1,p}(Ω) → W^{1,p}(ℝ²)` and a constant `C` with `P u = u` on `Ω`,
`‖P u‖_{L^p(ℝ²)} ≤ C ‖u‖_{L^p(Ω)}` and `‖P u‖_{W^{1,p}(ℝ²)} ≤ C ‖u‖_{W^{1,p}(Ω)}`, the shape of
`SobolevEuclidean.exists_extensionL`. By four successive reflections
(`SobolevEuclidean.exists_reflectionStep`) — across `x_2 = 0`, `x_2 = 1`, `x_1 = 0`, `x_1 = 1`,
reaching `W^{1,p}((−1, 3)²)` — followed by multiplication by a smooth `ψ` equal to `1` on the
square and supported in `(−1, 3)²`, extended by zero (`SobolevMultiIndex.extendZeroMulL`).
[brezis2011functional] Chapter 9, Remark 9 (Figure 6). -/
theorem SobolevEuclidean.exists_extensionL_unitSquare :
    ∃ (P : SobolevEuclidean 2 1 p (EuclideanSpace.rect 0 1 0 1) →L[ℝ]
        SobolevEuclidean 2 1 p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean 2 1 p (EuclideanSpace.rect 0 1 0 1),
        SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (EuclideanSpace.rect 0 1 0 1 : Set _)]
          SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (EuclideanSpace.rect 0 1 0 1 : Set _)) ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  refine SobolevEuclidean.exists_extensionL_of_steps ?_ ?_ ?_
    (SobolevEuclidean.exists_extension_rect_step₁ (p := p))
    (SobolevEuclidean.exists_extension_rect_step₂ (p := p))
    (SobolevEuclidean.exists_extension_rect_step₃ (p := p))
    (SobolevEuclidean.exists_extension_rect_step₄ (p := p))
    (SobolevEuclidean.exists_extension_rect_cutoff (p := p))
  · intro x hx
    rw [EuclideanSpace.mem_rect] at hx ⊢
    exact ⟨hx.1, hx.2.1, by linarith [hx.2.2.1], hx.2.2.2⟩
  · intro x hx
    rw [EuclideanSpace.mem_rect] at hx ⊢
    exact ⟨hx.1, hx.2.1, by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩
  · intro x hx
    rw [EuclideanSpace.mem_rect] at hx ⊢
    exact ⟨by linarith [hx.1], hx.2.1, by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩

end Square

/-! ### Extension domains from extension operators and extension steps -/

section Steps

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- An extension operator in the shape of Theorem 9.7 makes `Ω` a `W^{1,p}`-extension domain
(the `L^p` bound is not part of the predicate). -/
theorem IsSobolevExtensionDomain.of_exists_extensionL {Ω : Opens 𝔼}
    (h : ∃ (P : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼)) ∧
        ‖P u‖ ≤ C * ‖u‖) : IsSobolevExtensionDomain N p Ω := by
  obtain ⟨P, C, hP⟩ := h
  exact ⟨P.comp (Submodule.subtypeL ⊤), fun u ↦ (hP u.1).1⟩

/-- **An extension step into an extension domain**: if `Ω ⊆ Ω₁`, `Ω₁` is a `W^{1,p}`-extension
domain and `S : W^{1,p}(Ω) → W^{1,p}(Ω₁)` is a bounded linear map with `S u = u` on `Ω`, then `Ω`
is a `W^{1,p}`-extension domain (`u ↦ P (S u)`). -/
theorem IsSobolevExtensionDomain.of_extension_step {Ω Ω₁ : Opens 𝔼}
    (hΩ₁ : IsSobolevExtensionDomain N p Ω₁) (hle : Ω ≤ Ω₁)
    (S : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p Ω₁)
    (hS : ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      SobolevMultiIndex.fn u) : IsSobolevExtensionDomain N p Ω := by
  obtain ⟨P, hP⟩ := hΩ₁
  refine ⟨P ∘L (ContinuousLinearMap.id ℝ _).codRestrict ⊤ (fun _ ↦ Submodule.mem_top) ∘L S ∘L
    Submodule.subtypeL ⊤, fun u ↦ ?_⟩
  have h1 := hP ⟨S u.1, Submodule.mem_top⟩
  exact (h1.filter_mono
    (ae_mono (Measure.restrict_mono (SetLike.coe_subset_coe.2 hle) le_rfl))).trans (hS u.1)

end Steps
