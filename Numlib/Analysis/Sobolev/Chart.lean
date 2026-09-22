/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the boundary-regularity section of
`Numlib/Analysis/Sobolev/Domain.lean`; the partition of unity of Lemma 9.3 belongs beside
`Mathlib.Geometry.Manifold.PartitionOfUnity`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Numlib.Analysis.Sobolev.Domain

/-!
# Open sets of class `C^n` by local charts

The definition of a smooth open set of Brezis, *Functional Analysis, Sobolev Spaces and Partial
Differential Equations*, §9.2: `Ω ⊆ ℝ^N` is of class `C^1` if every boundary point has an open
neighbourhood `U` and a bijection `H : Q → U` with `H ∈ C^1(Q̄)`, `H⁻¹ ∈ C^1(Ū)`,
`H(Q₊) = U ∩ Ω` and `H(Q₀) = U ∩ ∂Ω`, where `Q = {(x', x_N) : |x'| < 1, |x_N| < 1}` is the unit
cylinder, `Q₊ = Q ∩ {x_N > 0}` its upper half and `Q₀ = Q ∩ {x_N = 0}` its equator. Here that is
the structure `ContDiffChart n Ω` (the data `U`, `H`, `H⁻¹` and the six conditions) and the
predicate `IsContDiffChartDomain n Ω`, for the same `n : WithTop ℕ∞` as the graph definition
`IsContDiffDomain` of `Numlib/Analysis/Sobolev/Domain.lean`.

Two definitions of a `C^n` domain coexist in this library. Atkinson–Han's `IsContDiffDomain` is by
local graphs after a rigid motion of the coordinates; Brezis's is by charts. They are equivalent,
but only the direction graph ⇒ chart is elementary — the chart is
`H(y', y_N) = T⁻¹(x₀' + εy', g(x₀' + εy') + εy_N)` — while chart ⇒ graph is the implicit function
theorem. The extension theorem of Brezis §9.2 is proved under the chart hypothesis because that is
what its proof uses (transfer to `Q₊` by `H`, reflect, transfer back), and the consumers holding a
graph hypothesis reach it through the bridge `IsContDiffDomain.isContDiffChartDomain` proved here.
The converse is not needed by anything and is not proved.

Pure geometry: no Sobolev space appears. The file also carries, because the Sobolev modules above
it all need them and none of them should import another: the half space `ℝ^N_+`; the
last-coordinate splitting `ℝ^{d+1} ≃ ℝ × ℝ^d` of Lebesgue measure, which is the Fubini step of
every "integrate in `x_N` first" argument; the finite atlas of a bounded boundary; the partition of
unity of Brezis Lemma 9.3, read off Mathlib's `SmoothPartitionOfUnity`; and the hypothesis bundle
`IsDiffeoOnWithBoundedJacobian` of Brezis Proposition 9.6 (a `C^1` diffeomorphism between open
sets with bounded Jacobians on both sides), of which a chart restricted to `Q₊` is an instance.

## Main definitions

* `EuclideanSpace.upperHalfSpace d`, the half space `{x_N > 0}` of `ℝ^{d+1}`;
* `unitChartCube d`, `unitChartCubePos d`, `unitChartCubeZero d`, the cylinder `Q` and its parts
  `Q₊`, `Q₀`;
* `EuclideanSpace.lastInitEquiv d : ℝ^{d+1} ≃ᵐ ℝ × ℝ^d`, `x ↦ (x_N, x')`, measure preserving;
* `ContDiffChart n Ω`, a local chart of class `C^n` of `Ω` at a boundary point, and
  `IsContDiffChartDomain n Ω`, the class-`C^n` condition by charts;
* `IsDiffeoOnWithBoundedJacobian H Hinv s t M`, the hypothesis bundle of Brezis Proposition 9.6.

## Main statements

* `IsContDiffDomain.isContDiffChartDomain`: a domain whose boundary is locally a `C^n` graph is a
  chart domain of class `C^n`;
* `IsContDiffChartDomain.exists_finite_atlas`: a bounded boundary is covered by finitely many
  charts;
* `IsCompact.exists_contDiff_partitionOfUnity`: Brezis Lemma 9.3, a smooth partition of unity
  `θ₀ + ∑ θᵢ = 1` subordinate to a finite open cover of a compact set, with `θ₀` vanishing near
  the set and the `θᵢ` compactly supported;
* `ContDiffChart.isDiffeoOnWithBoundedJacobian_pos`: a chart restricted to `Q₊` is a `C^1`
  diffeomorphism onto `U ∩ Ω` with bounded Jacobians.

## Implementation notes

`ContDiffChart` is a structure rather than Mathlib's `OpenPartialHomeomorph` because the source
of the chart is fixed to be `Q` and the regularity is asked on the closures `Q̄`, `Ū`, neither of
which that notion carries. The regularity `H⁻¹ ∈ C^1(Ū)` is `ContDiffOn ℝ n H⁻¹ (closure U)` in
Mathlib's sense; since `closure U` need not be uniquely differentiable at its boundary, the bound on
the derivative of `H⁻¹` on `U` is obtained from a covering argument
(`ContDiffOn.exists_norm_fderiv_le_of_isCompact`) rather than from the continuity of
`fderivWithin` on the closure.

## References

[brezis2011functional], §9.2: the Notation and Definition, Lemma 9.3, and footnote 6 of
Proposition 9.6.
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped ContDiff ENNReal InnerProductSpace Manifold Topology

noncomputable section

variable {d : ℕ}

/-! ### The half space, and the first coordinates as a linear map -/

namespace EuclideanSpace

/-- **The upper half space** `ℝ^N_+ = {x = (x', x_N) : x_N > 0}` of [brezis2011functional] §9.2,
Notation, in the coordinate convention of `IsBoundaryGraphAt`: the last coordinate is the one the
boundary is a graph over, and `isBoundaryOfClass_upperHalfSpace` uses the same set literal. -/
def upperHalfSpace (d : ℕ) : Set (EuclideanSpace ℝ (Fin (d + 1))) := {x | 0 < x (Fin.last d)}

theorem mem_upperHalfSpace {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ upperHalfSpace d ↔ 0 < x (Fin.last d) :=
  Iff.rfl

/-- The half space is open. -/
theorem isOpen_upperHalfSpace : IsOpen (upperHalfSpace d) :=
  isOpen_lt continuous_const (by fun_prop)

/-- The half space as an `Opens`, the shape the Sobolev spaces on it take. -/
def upperHalfSpaceOpens (d : ℕ) : Opens (EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨upperHalfSpace d, isOpen_upperHalfSpace⟩

@[simp]
theorem coe_upperHalfSpaceOpens : (upperHalfSpaceOpens d : Set _) = upperHalfSpace d := rfl

/-- The first `d` coordinates of a point of `ℝ^{d+1}`, `EuclideanSpace.init`, as a continuous
linear map. -/
def initL : EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearMap.toContinuousLinearMap
    { toFun := init
      map_add' := fun x y ↦ by ext i; simp
      map_smul' := fun c x ↦ by ext i; simp }

@[simp]
theorem initL_apply (x : EuclideanSpace ℝ (Fin (d + 1))) : initL x = init x := rfl

theorem continuous_init : Continuous (init : EuclideanSpace ℝ (Fin (d + 1)) → _) :=
  (initL (d := d)).continuous

theorem contDiff_init {n : WithTop ℕ∞} :
    ContDiff ℝ n (init : EuclideanSpace ℝ (Fin (d + 1)) → _) :=
  (initL (d := d)).contDiff

/-- The first coordinates of a sum, difference, or scalar multiple. -/
@[simp]
theorem init_add (x y : EuclideanSpace ℝ (Fin (d + 1))) : init (x + y) = init x + init y :=
  map_add initL x y

@[simp]
theorem init_sub (x y : EuclideanSpace ℝ (Fin (d + 1))) : init (x - y) = init x - init y :=
  map_sub initL x y

@[simp]
theorem init_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) : init (c • x) = c • init x :=
  map_smul initL c x

@[simp]
theorem init_zero : init (0 : EuclideanSpace ℝ (Fin (d + 1))) = 0 := map_zero initL

/-- The first coordinates of a multiple of the last basis vector vanish. -/
@[simp]
theorem init_single_last (a : ℝ) : init (single (Fin.last d) a) = 0 := by
  ext i
  simp [Fin.castSucc_ne_last]

/-- The Pythagorean splitting of the norm along the last coordinate. -/
theorem norm_sq_eq_init_add_last (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ‖x‖ ^ 2 = ‖init x‖ ^ 2 + x (Fin.last d) ^ 2 := by
  rw [real_norm_sq_eq, real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp

theorem norm_init_le (x : EuclideanSpace ℝ (Fin (d + 1))) : ‖init x‖ ≤ ‖x‖ :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by nlinarith [norm_sq_eq_init_add_last x, sq_nonneg (x (Fin.last d))])

theorem abs_apply_last_le (x : EuclideanSpace ℝ (Fin (d + 1))) : |x (Fin.last d)| ≤ ‖x‖ :=
  (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by nlinarith [norm_sq_eq_init_add_last x, sq_nonneg ‖init x‖, sq_abs (x (Fin.last d))])

end EuclideanSpace

/-! ### The unit cylinder `Q` and its parts `Q₊`, `Q₀` -/

open EuclideanSpace in
/-- **The unit cylinder** `Q = {x = (x', x_N) : |x'| < 1, |x_N| < 1}` of [brezis2011functional]
§9.2, Notation — the domain of every local chart. (The book calls it a cube; in the Euclidean norm
of `x'` it is a cylinder.) -/
def unitChartCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {x | ‖init x‖ < 1 ∧ |x (Fin.last d)| < 1}

/-- **The upper half cylinder** `Q₊ = Q ∩ ℝ^N_+` of [brezis2011functional] §9.2, Notation. -/
def unitChartCubePos (d : ℕ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {x ∈ unitChartCube d | 0 < x (Fin.last d)}

/-- **The equator** `Q₀ = {(x', 0) : |x'| < 1}` of the cylinder, [brezis2011functional] §9.2,
Notation: the part of the chart domain that a chart sends onto the boundary. -/
def unitChartCubeZero (d : ℕ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {x ∈ unitChartCube d | x (Fin.last d) = 0}

open EuclideanSpace

theorem mem_unitChartCube {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ unitChartCube d ↔ ‖init x‖ < 1 ∧ |x (Fin.last d)| < 1 :=
  Iff.rfl

theorem mem_unitChartCubePos {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ unitChartCubePos d ↔ x ∈ unitChartCube d ∧ 0 < x (Fin.last d) :=
  Iff.rfl

theorem mem_unitChartCubeZero {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ unitChartCubeZero d ↔ x ∈ unitChartCube d ∧ x (Fin.last d) = 0 :=
  Iff.rfl

theorem unitChartCubePos_subset : unitChartCubePos d ⊆ unitChartCube d := fun _ hx ↦ hx.1

theorem unitChartCubeZero_subset : unitChartCubeZero d ⊆ unitChartCube d := fun _ hx ↦ hx.1

/-- `Q₊ = Q ∩ ℝ^N_+`, as the book writes it. -/
theorem unitChartCubePos_eq_inter :
    unitChartCubePos d = unitChartCube d ∩ upperHalfSpace d :=
  rfl

theorem zero_mem_unitChartCube : (0 : EuclideanSpace ℝ (Fin (d + 1))) ∈ unitChartCube d := by
  simp [mem_unitChartCube]

theorem zero_mem_unitChartCubeZero :
    (0 : EuclideanSpace ℝ (Fin (d + 1))) ∈ unitChartCubeZero d :=
  ⟨zero_mem_unitChartCube, by simp⟩

theorem continuous_apply_last :
    Continuous fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦ x (Fin.last d) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last d)).continuous

theorem continuous_abs_apply_last :
    Continuous fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦ |x (Fin.last d)| :=
  continuous_apply_last.abs

theorem isOpen_unitChartCube : IsOpen (unitChartCube d) :=
  (isOpen_lt continuous_init.norm continuous_const).inter
    (isOpen_lt continuous_abs_apply_last continuous_const)

theorem isOpen_unitChartCubePos : IsOpen (unitChartCubePos d) :=
  isOpen_unitChartCube.inter isOpen_upperHalfSpace

/-- The cylinder lies in the ball of radius `2`. -/
theorem unitChartCube_subset_ball : unitChartCube d ⊆ Metric.ball 0 2 := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  have h := norm_sq_eq_init_add_last x
  have h1 : ‖init x‖ ^ 2 < 1 := by nlinarith [hx.1, norm_nonneg (init x)]
  have h2 : x (Fin.last d) ^ 2 < 1 := by
    nlinarith [hx.2, abs_nonneg (x (Fin.last d)), sq_abs (x (Fin.last d))]
  nlinarith [norm_nonneg x]

theorem isBounded_unitChartCube : Bornology.IsBounded (unitChartCube d) :=
  Metric.isBounded_ball.subset unitChartCube_subset_ball

/-- The closure of the cylinder is the closed cylinder `{‖x'‖ ≤ 1, |x_N| ≤ 1}`. -/
theorem closure_unitChartCube :
    closure (unitChartCube d) = {x | ‖init x‖ ≤ 1 ∧ |x (Fin.last d)| ≤ 1} := by
  apply Subset.antisymm
  · refine closure_minimal (fun x hx ↦ ⟨hx.1.le, hx.2.le⟩) ?_
    exact (isClosed_le continuous_init.norm continuous_const).inter
      (isClosed_le continuous_abs_apply_last continuous_const)
  · intro x hx
    have ht : Tendsto (fun n : ℕ ↦ (1 - 1 / ((n : ℝ) + 1)) • x) atTop (𝓝 x) := by
      have : Tendsto (fun n : ℕ ↦ (1 - 1 / ((n : ℝ) + 1))) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this.smul_const x
    refine mem_closure_of_tendsto ht (Eventually.of_forall fun n ↦ ?_)
    have h0 : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    have h1 : 1 - 1 / ((n : ℝ) + 1) < 1 := by
      rw [sub_lt_self_iff]; positivity
    refine ⟨?_, ?_⟩
    · rw [init_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
      calc (1 - 1 / ((n : ℝ) + 1)) * ‖init x‖ ≤ (1 - 1 / ((n : ℝ) + 1)) * 1 := by
            gcongr; exact hx.1
        _ < 1 := by linarith
    · rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg h0]
      calc (1 - 1 / ((n : ℝ) + 1)) * |x (Fin.last d)| ≤ (1 - 1 / ((n : ℝ) + 1)) * 1 := by
            gcongr; exact hx.2
        _ < 1 := by linarith

theorem isCompact_closure_unitChartCube : IsCompact (closure (unitChartCube d)) :=
  isBounded_unitChartCube.isCompact_closure

/-- The equator is the part of the frontier of `Q₊` inside `Q`: `Q ∩ ∂Q₊ = Q₀`. It is how
"`u = 0` on `Q₀`" is read for a function on `Q₊`. -/
theorem unitChartCube_inter_frontier_unitChartCubePos :
    unitChartCube d ∩ frontier (unitChartCubePos d) = unitChartCubeZero d := by
  have hproj : IsOpenMap (fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦ x (Fin.last d)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last d)).isOpenMap fun a ↦
      ⟨single (Fin.last d) a, by simp⟩
  have hfr : frontier (upperHalfSpace d) = {x | x (Fin.last d) = 0} := by
    have : upperHalfSpace d = (fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦ x (Fin.last d)) ⁻¹' Ioi 0 :=
      rfl
    rw [this, ← hproj.preimage_frontier_eq_frontier_preimage (by fun_prop), frontier_Ioi]
    rfl
  rw [unitChartCubePos_eq_inter, inter_comm, inter_comm (unitChartCube d),
    frontier_inter_open_inter isOpen_unitChartCube, hfr]
  ext x
  simp [mem_unitChartCubeZero, and_comm]

theorem unitChartCubeZero_subset_frontier_unitChartCubePos :
    unitChartCubeZero d ⊆ frontier (unitChartCubePos d) :=
  unitChartCube_inter_frontier_unitChartCubePos.symm.subset.trans inter_subset_right


/-! ### The last-coordinate splitting of Lebesgue measure

The map `x ↦ (x_N, x')` identifies `ℝ^{d+1}` with `ℝ × ℝ^d` and carries Lebesgue measure to the
product measure. It is the Fubini step of every "integrate in `x_N` first" argument. -/

namespace EuclideanSpace

/-- The point of `ℝ^{d+1}` with first coordinates `x'` and last coordinate `t`: the inverse of the
splitting `x ↦ (x_N, x')`. -/
def snocLast (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ ↦ ℝ) x' t)

@[simp]
theorem snocLast_apply_castSucc (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) (i : Fin d) :
    snocLast x' t i.castSucc = x' i := by
  simp [snocLast]

@[simp]
theorem snocLast_apply_last (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    snocLast x' t (Fin.last d) = t := by
  simp [snocLast]

@[simp]
theorem init_snocLast (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) : init (snocLast x' t) = x' := by
  ext i
  simp

@[simp]
theorem snocLast_init_last (x : EuclideanSpace ℝ (Fin (d + 1))) :
    snocLast (init x) (x (Fin.last d)) = x := by
  ext i
  induction i using Fin.lastCases <;> simp

/-- The splitting `x ↦ (x_N, x')` of `ℝ^{d+1}` as `ℝ × ℝ^d`, as a continuous linear
equivalence. -/
def lastInitL (d : ℕ) : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] ℝ × EuclideanSpace ℝ (Fin d) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x ↦ (x (Fin.last d), init x)
      invFun := fun p ↦ snocLast p.2 p.1
      map_add' := fun x y ↦ by simp
      map_smul' := fun c x ↦ by simp
      left_inv := fun x ↦ by simp
      right_inv := fun p ↦ by simp }

@[simp]
theorem lastInitL_apply (x : EuclideanSpace ℝ (Fin (d + 1))) :
    lastInitL d x = (x (Fin.last d), init x) :=
  rfl

@[simp]
theorem lastInitL_symm_apply (p : ℝ × EuclideanSpace ℝ (Fin d)) :
    (lastInitL d).symm p = snocLast p.2 p.1 :=
  rfl

theorem continuous_snocLast :
    Continuous fun p : EuclideanSpace ℝ (Fin d) × ℝ ↦ snocLast p.1 p.2 :=
  (lastInitL d).symm.continuous.comp continuous_swap

/-- The splitting `x ↦ (x_N, x')` as a measurable equivalence `ℝ^{d+1} ≃ᵐ ℝ × ℝ^d`. -/
def lastInitEquiv (d : ℕ) : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin d) :=
  (lastInitL d).toHomeomorph.toMeasurableEquiv

@[simp]
theorem lastInitEquiv_apply (x : EuclideanSpace ℝ (Fin (d + 1))) :
    lastInitEquiv d x = (x (Fin.last d), init x) :=
  rfl

@[simp]
theorem lastInitEquiv_symm_apply (p : ℝ × EuclideanSpace ℝ (Fin d)) :
    (lastInitEquiv d).symm p = snocLast p.2 p.1 :=
  rfl

/-- **The last-coordinate splitting of Lebesgue measure**: `x ↦ (x_N, x')` carries Lebesgue
measure on `ℝ^{d+1}` to the product of Lebesgue measures on `ℝ × ℝ^d`. -/
theorem measurePreserving_lastInit (d : ℕ) :
    MeasurePreserving (lastInitEquiv d) volume volume := by
  have h1 := PiLp.volume_preserving_ofLp (Fin (d + 1))
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d)
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin d))
  have h := (h3.comp h2).comp h1
  have hfun : ⇑(lastInitEquiv d) = Prod.map id (WithLp.toLp 2) ∘
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d) ∘ WithLp.ofLp := by
    funext x
    refine Prod.ext rfl ?_
    ext i
    simp [MeasurableEquiv.piFinSuccAbove, init, Fin.init]
  rw [hfun]
  exact h

/-- Fubini along the last coordinate, for the Lebesgue integral: `∫ f = ∫ x' ∫ t, f (x', t)`. -/
theorem lintegral_lastInit (f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ≥0∞) (hf : AEMeasurable f) :
    ∫⁻ x, f x = ∫⁻ x', ∫⁻ t, f (snocLast x' t) := by
  have h := (measurePreserving_lastInit d).symm (lastInitEquiv d)
  calc ∫⁻ x, f x
      = ∫⁻ p : ℝ × EuclideanSpace ℝ (Fin d), (f ∘ (lastInitEquiv d).symm) p
          ∂((volume : Measure ℝ).prod volume) :=
        (h.lintegral_comp_emb (lastInitEquiv d).symm.measurableEmbedding f).symm
    _ = ∫⁻ x', ∫⁻ t, (f ∘ (lastInitEquiv d).symm) (t, x') :=
        lintegral_prod_symm _ (hf.comp_quasiMeasurePreserving h.quasiMeasurePreserving)
    _ = ∫⁻ x', ∫⁻ t, f (snocLast x' t) := rfl

/-- Fubini along the last coordinate, for the Bochner integral: `∫ f = ∫ x' ∫ t, f (x', t)`. -/
theorem integral_lastInit {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : EuclideanSpace ℝ (Fin (d + 1)) → G) (hf : Integrable f) :
    ∫ x, f x = ∫ x', ∫ t, f (snocLast x' t) := by
  have h := (measurePreserving_lastInit d).symm (lastInitEquiv d)
  calc ∫ x, f x
      = ∫ p : ℝ × EuclideanSpace ℝ (Fin d), (f ∘ (lastInitEquiv d).symm) p
          ∂((volume : Measure ℝ).prod volume) :=
        (h.integral_comp' f).symm
    _ = ∫ x', ∫ t, (f ∘ (lastInitEquiv d).symm) (t, x') :=
        integral_prod_symm _ (h.integrable_comp_of_integrable hf)
    _ = ∫ x', ∫ t, f (snocLast x' t) := rfl

/-! #### The splitting `x ↦ (x', x_N)`, and the vertical lines of `ℝ^{d+1}`

The splitting in the order the implicit function theorem wants (`initLastL`, the factors of
`lastInitL` swapped), the derivative of a vertical line `t ↦ (x', t)`, and the norms and inner
products of `snocLast`. -/

/-- The splitting `x ↦ (x', x_N)` of `ℝ^{d+1}` as `ℝ^d × ℝ`, as a continuous linear equivalence;
`(lastInitL d).symm` with the factors swapped, the order that Mathlib's implicit function theorem
on a product `E₁ × E₂` solves for the second factor. -/
def initLastL (d : ℕ) :
    EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin d) × ℝ :=
  (lastInitL d).trans (ContinuousLinearEquiv.prodComm ℝ ℝ (EuclideanSpace ℝ (Fin d)))

/-- The splitting sends `x` to `(x', x_N)`. -/
@[simp]
theorem initLastL_apply (x : EuclideanSpace ℝ (Fin (d + 1))) :
    initLastL d x = (init x, x (Fin.last d)) :=
  rfl

/-- The inverse splitting sends `(x', t)` to `(x', t)` read in `ℝ^{d+1}`. -/
@[simp]
theorem initLastL_symm_apply (p : EuclideanSpace ℝ (Fin d) × ℝ) :
    (initLastL d).symm p = snocLast p.1 p.2 :=
  rfl

/-- The point `(0, 1)` of `ℝ^{d+1}` is the last basis vector. -/
theorem snocLast_zero_one :
    snocLast (0 : EuclideanSpace ℝ (Fin d)) 1 = single (Fin.last d) 1 := by
  ext i
  induction i using Fin.lastCases <;> simp [Fin.castSucc_ne_last]

/-- The vertical line `t ↦ (x', t)` has derivative `e_N`. -/
theorem hasDerivAt_snocLast (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun t ↦ snocLast x' t) (single (Fin.last d) 1) t := by
  have h : HasDerivAt (fun t : ℝ ↦ (x', t)) ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)) t :=
    (hasDerivAt_const t x').prodMk (hasDerivAt_id t)
  have := (initLastL d).symm.hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def, snocLast_zero_one] using this

/-- The vertical line `t ↦ (x', t)` is the affine line through `(x', 0)` and `(x', 1)`. -/
theorem snocLast_eq_lineMap (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    snocLast x' t = AffineMap.lineMap (snocLast x' 0) (snocLast x' 1) t := by
  rw [AffineMap.lineMap_apply_module]
  ext i
  induction i using Fin.lastCases
  · simp
  · simp only [PiLp.add_apply, PiLp.smul_apply, snocLast_apply_castSucc, smul_eq_mul]
    ring

/-- The first coordinates do not increase distances. -/
theorem dist_init_le (x y : EuclideanSpace ℝ (Fin (d + 1))) :
    dist (init x) (init y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← init_sub]
  exact norm_init_le _

/-- `‖(x', t)‖ ≤ ‖x'‖ + |t|`. -/
theorem norm_snocLast_le (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ‖snocLast x' t‖ ≤ ‖x'‖ + |t| := by
  have h := norm_sq_eq_init_add_last (snocLast x' t)
  rw [init_snocLast, snocLast_apply_last] at h
  have h2 : ‖snocLast x' t‖ ^ 2 ≤ (‖x'‖ + |t|) ^ 2 := by
    rw [h]; nlinarith [norm_nonneg x', abs_nonneg t, sq_abs t]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-- `‖(v, −1)‖ = √(1 + ‖v‖²)`. -/
theorem norm_snocLast_neg_one (v : EuclideanSpace ℝ (Fin d)) :
    ‖snocLast v (-1)‖ = Real.sqrt (1 + ‖v‖ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (snocLast v (-1))), norm_sq_eq_init_add_last]
  simp [add_comm]

/-- Two points of a vertical line: `‖(x', s) − (x', t)‖ = |s − t|`. -/
theorem norm_snocLast_sub_snocLast (x' : EuclideanSpace ℝ (Fin d)) (s t : ℝ) :
    ‖snocLast x' s - snocLast x' t‖ = |s - t| := by
  have h := norm_sq_eq_init_add_last (snocLast x' s - snocLast x' t)
  simp only [init_sub, init_snocLast, sub_self, norm_zero, PiLp.sub_apply, snocLast_apply_last,
    zero_pow two_ne_zero, zero_add] at h
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_sq_eq_abs]

/-- The inner product of two points of `ℝ^{d+1}` split along the last coordinate:
`⟪(x, s), (y, t)⟫ = ⟪x, y⟫ + s t`. -/
theorem inner_snocLast (x y : EuclideanSpace ℝ (Fin d)) (s t : ℝ) :
    ⟪snocLast x s, snocLast y t⟫_ℝ = ⟪x, y⟫_ℝ + s * t := by
  simp only [PiLp.inner_apply, Fin.sum_univ_castSucc, snocLast_apply_castSucc, snocLast_apply_last,
    RCLike.inner_apply, conj_trivial]
  ring

section Graph

variable {g : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The graph map `x' ↦ (x', g x')` is continuous. -/
theorem continuous_snocLast_graph (hg : Continuous g) :
    Continuous fun x' ↦ snocLast x' (g x') :=
  continuous_snocLast.comp (continuous_id.prodMk hg)

/-- The derivative of the map `x' ↦ (x', g x' + s)`. -/
theorem hasFDerivAt_snocLast_add (hg : ContDiff ℝ 1 g) (x' : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    HasFDerivAt (fun x' ↦ snocLast x' (g x' + s))
      (((initLastL d).symm : EuclideanSpace ℝ (Fin d) × ℝ →L[ℝ] _).comp
        ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ g x'))) x' := by
  have h1 : HasFDerivAt (fun x' ↦ (x', g x' + s))
      ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ g x')) x' :=
    (hasFDerivAt_id x').prodMk ((hg.differentiable one_ne_zero x').hasFDerivAt.add_const s)
  exact (initLastL d).symm.hasFDerivAt.comp x' h1

/-- The derivative of `x' ↦ (x', g x' + s)` in the direction `eᵢ` is `eᵢ + ∂ᵢg(x') e_N`. -/
theorem snocLast_add_fderiv_apply_single (x' : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    ((initLastL d).symm : EuclideanSpace ℝ (Fin d) × ℝ →L[ℝ] _).comp
        ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ g x')) (EuclideanSpace.single i 1)
      = EuclideanSpace.single i.castSucc 1
        + fderiv ℝ g x' (EuclideanSpace.single i 1)
          • EuclideanSpace.single (Fin.last d) (1 : ℝ) := by
  ext j
  induction j using Fin.lastCases <;> simp [Fin.castSucc_ne_last, Fin.castSucc_inj]

end Graph
end EuclideanSpace


/-! ### Local charts, and open sets of class `C^n` by charts -/

variable {n : WithTop ℕ∞} {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **A local chart of class `C^n`** of `Ω ⊆ ℝ^{d+1}` at a boundary point, [brezis2011functional]
§9.2, Definition: an open set `U` and a bijection `H : Q → U` from the unit cylinder
`Q = unitChartCube d` with `H ∈ C^n(Q̄)`, `H⁻¹ ∈ C^n(Ū)`, `H(Q₊) = U ∩ Ω` and `H(Q₀) = U ∩ ∂Ω`.
The regularity on the closures is Mathlib's `ContDiffOn` on `closure Q` and `closure U`; the maps
are total functions on `ℝ^{d+1}`, of which only the values on `Q` (for `H`) and on `U` (for `H⁻¹`)
matter. -/
structure ContDiffChart (n : WithTop ℕ∞) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) where
  /-- The open neighbourhood `U` of the boundary point. -/
  U : Set (EuclideanSpace ℝ (Fin (d + 1)))
  /-- The chart `H : Q → U`. -/
  toFun : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))
  /-- The inverse chart `H⁻¹ : U → Q`. -/
  invFun : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))
  isOpen_U : IsOpen U
  /-- `H ∈ C^n(Q̄)`. -/
  contDiffOn : ContDiffOn ℝ n toFun (closure (unitChartCube d))
  /-- `H⁻¹ ∈ C^n(Ū)`. -/
  contDiffOn_invFun : ContDiffOn ℝ n invFun (closure U)
  /-- `H` is a bijection of `Q` onto `U`. -/
  bijOn : BijOn toFun (unitChartCube d) U
  /-- `H⁻¹` inverts `H` on `Q` and on `U`. -/
  invOn : InvOn invFun toFun (unitChartCube d) U
  /-- `H(Q₊) = U ∩ Ω`. -/
  image_pos : toFun '' unitChartCubePos d = U ∩ Ω
  /-- `H(Q₀) = U ∩ ∂Ω`. -/
  image_zero : toFun '' unitChartCubeZero d = U ∩ frontier Ω

namespace ContDiffChart

variable (c : ContDiffChart n Ω)

/-- A chart of class `C^n` is a chart of class `C^m` for `m ≤ n`. -/
def ofLE {m : WithTop ℕ∞} (hmn : m ≤ n) : ContDiffChart m Ω :=
  { c with
    contDiffOn := c.contDiffOn.of_le hmn
    contDiffOn_invFun := c.contDiffOn_invFun.of_le hmn }

@[simp] theorem ofLE_U {m : WithTop ℕ∞} (hmn : m ≤ n) : (c.ofLE hmn).U = c.U := rfl

@[simp] theorem ofLE_toFun {m : WithTop ℕ∞} (hmn : m ≤ n) : (c.ofLE hmn).toFun = c.toFun := rfl

@[simp] theorem ofLE_invFun {m : WithTop ℕ∞} (hmn : m ≤ n) :
    (c.ofLE hmn).invFun = c.invFun := rfl

theorem continuousOn : ContinuousOn c.toFun (closure (unitChartCube d)) :=
  c.contDiffOn.continuousOn

theorem continuousOn_invFun : ContinuousOn c.invFun (closure c.U) :=
  c.contDiffOn_invFun.continuousOn

theorem mapsTo : MapsTo c.toFun (unitChartCube d) c.U := c.bijOn.mapsTo

theorem injOn : InjOn c.toFun (unitChartCube d) := c.bijOn.injOn

theorem surjOn : SurjOn c.toFun (unitChartCube d) c.U := c.bijOn.surjOn

/-- `H(Q) = U`. -/
theorem image_unitChartCube : c.toFun '' unitChartCube d = c.U := c.bijOn.image_eq

theorem invFun_toFun {y : EuclideanSpace ℝ (Fin (d + 1))} (hy : y ∈ unitChartCube d) :
    c.invFun (c.toFun y) = y :=
  c.invOn.1 hy

theorem toFun_invFun {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ c.U) :
    c.toFun (c.invFun x) = x :=
  c.invOn.2 hx

theorem mapsTo_invFun : MapsTo c.invFun c.U (unitChartCube d) :=
  c.invOn.1.mapsTo c.surjOn

/-- `H⁻¹` is a bijection of `U` onto `Q`. -/
theorem bijOn_invFun : BijOn c.invFun c.U (unitChartCube d) :=
  c.invOn.symm.bijOn c.mapsTo_invFun c.mapsTo

theorem injOn_invFun : InjOn c.invFun c.U := c.bijOn_invFun.injOn

/-- `H⁻¹(U ∩ Ω) = Q₊`. -/
theorem invFun_image_inter : c.invFun '' (c.U ∩ Ω) = unitChartCubePos d := by
  rw [← c.image_pos]
  exact (c.invOn.1.mono unitChartCubePos_subset).image_image

/-- `H⁻¹(U ∩ ∂Ω) = Q₀`. -/
theorem invFun_image_inter_frontier : c.invFun '' (c.U ∩ frontier Ω) = unitChartCubeZero d := by
  rw [← c.image_zero]
  exact (c.invOn.1.mono unitChartCubeZero_subset).image_image

/-- A point of `Q` is sent into `Ω` exactly when it lies in `Q₊`. -/
theorem toFun_mem_iff {y : EuclideanSpace ℝ (Fin (d + 1))} (hy : y ∈ unitChartCube d) :
    c.toFun y ∈ Ω ↔ y ∈ unitChartCubePos d := by
  constructor
  · intro h
    have : c.toFun y ∈ c.toFun '' unitChartCubePos d := c.image_pos ▸ ⟨c.mapsTo hy, h⟩
    obtain ⟨z, hz, hzy⟩ := this
    rwa [← c.injOn (unitChartCubePos_subset hz) hy hzy]
  · intro h
    exact (c.image_pos ▸ mem_image_of_mem c.toFun h : c.toFun y ∈ c.U ∩ Ω).2

/-- A point of `Q` is sent onto `∂Ω` exactly when it lies on the equator `Q₀`. -/
theorem toFun_mem_frontier_iff {y : EuclideanSpace ℝ (Fin (d + 1))} (hy : y ∈ unitChartCube d) :
    c.toFun y ∈ frontier Ω ↔ y ∈ unitChartCubeZero d := by
  constructor
  · intro h
    have : c.toFun y ∈ c.toFun '' unitChartCubeZero d := c.image_zero ▸ ⟨c.mapsTo hy, h⟩
    obtain ⟨z, hz, hzy⟩ := this
    rwa [← c.injOn (unitChartCubeZero_subset hz) hy hzy]
  · intro h
    exact (c.image_zero ▸ mem_image_of_mem c.toFun h : c.toFun y ∈ c.U ∩ frontier Ω).2

/-- A point of `U` lies in `Ω` exactly when its inverse image lies in `Q₊`. -/
theorem invFun_mem_pos_iff {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ c.U) :
    c.invFun x ∈ unitChartCubePos d ↔ x ∈ Ω := by
  rw [← c.toFun_mem_iff (c.mapsTo_invFun hx), c.toFun_invFun hx]

/-- A point of `U` lies on `∂Ω` exactly when its inverse image lies on the equator `Q₀`. -/
theorem invFun_mem_zero_iff {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ c.U) :
    c.invFun x ∈ unitChartCubeZero d ↔ x ∈ frontier Ω := by
  rw [← c.toFun_mem_frontier_iff (c.mapsTo_invFun hx), c.toFun_invFun hx]

/-- `U` is contained in the compact set `H(Q̄)`. -/
theorem U_subset_image_closure : c.U ⊆ c.toFun '' closure (unitChartCube d) :=
  c.image_unitChartCube ▸ image_mono subset_closure

theorem isCompact_image_closure : IsCompact (c.toFun '' closure (unitChartCube d)) :=
  isCompact_closure_unitChartCube.image_of_continuousOn c.continuousOn

theorem isBounded_U : Bornology.IsBounded c.U :=
  c.isCompact_image_closure.isBounded.subset c.U_subset_image_closure

/-- The closure of the range `U` of a chart is compact: `U ⊆ H(Q̄)`, a compact set. -/
theorem isCompact_closure_U : IsCompact (closure c.U) :=
  c.isCompact_image_closure.of_isClosed_subset isClosed_closure
    (c.isCompact_image_closure.isClosed.closure_subset_iff.2 c.U_subset_image_closure)

end ContDiffChart

/-- **An open set of class `C^n` by local charts**, [brezis2011functional] §9.2, Definition: `Ω` is
open and every boundary point lies in the range `U` of some chart of class `C^n`. Neither `Ω` nor
its boundary is asked to be bounded; "`Γ` bounded" is a separate hypothesis where a theorem needs
it. This is the chart counterpart of the graph condition `IsContDiffDomain`; the two are related
by `IsContDiffDomain.isContDiffChartDomain`. -/
def IsContDiffChartDomain (n : WithTop ℕ∞) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) : Prop :=
  IsOpen Ω ∧ ∀ x₀ ∈ frontier Ω, ∃ c : ContDiffChart n Ω, x₀ ∈ c.U

namespace IsContDiffChartDomain

theorem isOpen (h : IsContDiffChartDomain n Ω) : IsOpen Ω := h.1

theorem exists_chart (h : IsContDiffChartDomain n Ω) {x₀ : EuclideanSpace ℝ (Fin (d + 1))}
    (hx₀ : x₀ ∈ frontier Ω) : ∃ c : ContDiffChart n Ω, x₀ ∈ c.U :=
  h.2 x₀ hx₀

/-- A chart domain of class `C^n` is one of class `C^m` for `m ≤ n`. -/
theorem of_le {m : WithTop ℕ∞} (h : IsContDiffChartDomain n Ω) (hmn : m ≤ n) :
    IsContDiffChartDomain m Ω :=
  ⟨h.1, fun x₀ hx₀ ↦ let ⟨c, hc⟩ := h.2 x₀ hx₀; ⟨c.ofLE hmn, hc⟩⟩

/-- **A compact piece of the boundary is covered by finitely many charts.** This is the finite
atlas that the proof of [brezis2011functional] Theorem 9.7 starts from, in the form that also
serves an unbounded boundary met inside a ball (Corollary 9.8). -/
theorem exists_finite_atlas_of_isCompact (h : IsContDiffChartDomain n Ω)
    {K : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hK : IsCompact K) (hKΩ : K ⊆ frontier Ω) :
    ∃ (k : ℕ) (c : Fin k → ContDiffChart n Ω), K ⊆ ⋃ i, (c i).U := by
  have hcov : K ⊆ ⋃ c : ContDiffChart n Ω, c.U := fun x hx ↦
    let ⟨c, hc⟩ := h.2 x (hKΩ hx); mem_iUnion.2 ⟨c, hc⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c : ContDiffChart n Ω ↦ c.U)
    (fun c ↦ c.isOpen_U) hcov
  refine ⟨t.card, fun i ↦ (t.equivFin.symm i : ContDiffChart n Ω), fun x hx ↦ ?_⟩
  obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.1 (ht hx)
  exact mem_iUnion.2 ⟨t.equivFin ⟨c, hct⟩, by simpa using hxc⟩

/-- **A bounded boundary is covered by finitely many charts**: the first sentence of the proof of
[brezis2011functional] Theorem 9.7. -/
theorem exists_finite_atlas (h : IsContDiffChartDomain n Ω)
    (hΓ : Bornology.IsBounded (frontier Ω)) :
    ∃ (k : ℕ) (c : Fin k → ContDiffChart n Ω), frontier Ω ⊆ ⋃ i, (c i).U :=
  h.exists_finite_atlas_of_isCompact (Metric.isCompact_of_isClosed_isBounded isClosed_frontier hΓ)
    subset_rfl

end IsContDiffChartDomain


/-! ### From a local graph to a local chart

If, after the rigid motion `T`, the set `Ω` is the region above the graph of `g` near `x₀`, then
`Ψ x := T x − g((T x)') e_N` straightens the graph onto the hyperplane `{y_N = 0}` and sends `Ω`
to the upper half space, and the chart at `x₀` is `H y := Ψ⁻¹(Ψ x₀ + ε y)` for a small `ε`. -/

namespace EuclideanSpace

variable (T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
  (g : EuclideanSpace ℝ (Fin d) → ℝ)

/-- Straightening the graph of `g` seen through the rigid motion `T`: `x ↦ T x − g((T x)') e_N`,
which sends the region `{(T x)_N > g((T x)')}` above the graph onto the upper half space. -/
def graphStraighten (x : EuclideanSpace ℝ (Fin (d + 1))) : EuclideanSpace ℝ (Fin (d + 1)) :=
  T x - g (init (T x)) • single (Fin.last d) 1

/-- The inverse of `graphStraighten`: `y ↦ T⁻¹(y + g(y') e_N)`. -/
def graphUnstraighten (y : EuclideanSpace ℝ (Fin (d + 1))) : EuclideanSpace ℝ (Fin (d + 1)) :=
  T.symm (y + g (init y) • single (Fin.last d) 1)

@[simp]
theorem init_graphStraighten (x : EuclideanSpace ℝ (Fin (d + 1))) :
    init (graphStraighten T g x) = init (T x) := by
  simp [graphStraighten]

theorem graphStraighten_apply_last (x : EuclideanSpace ℝ (Fin (d + 1))) :
    graphStraighten T g x (Fin.last d) = T x (Fin.last d) - g (init (T x)) := by
  simp [graphStraighten]

@[simp]
theorem graphUnstraighten_graphStraighten (x : EuclideanSpace ℝ (Fin (d + 1))) :
    graphUnstraighten T g (graphStraighten T g x) = x := by
  simp [graphUnstraighten, graphStraighten]

@[simp]
theorem graphStraighten_graphUnstraighten (y : EuclideanSpace ℝ (Fin (d + 1))) :
    graphStraighten T g (graphUnstraighten T g y) = y := by
  simp [graphStraighten, graphUnstraighten]

theorem contDiff_affineIsometryEquiv {n : WithTop ℕ∞} : ContDiff ℝ n T :=
  T.toAffineIsometry.toContinuousAffineMap.contDiff

theorem contDiff_graphStraighten {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (graphStraighten T g) :=
  (contDiff_affineIsometryEquiv T).sub
    ((hg.comp (contDiff_init.comp (contDiff_affineIsometryEquiv T))).smul contDiff_const)

theorem contDiff_graphUnstraighten {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (graphUnstraighten T g) :=
  (contDiff_affineIsometryEquiv T.symm).comp
    (contDiff_id.add ((hg.comp contDiff_init).smul contDiff_const))

end EuclideanSpace

section Bridge

variable {x₀ : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ}
  {T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1))}
  {g : EuclideanSpace ℝ (Fin d) → ℝ}

/-- **A boundary point of a set that is locally a graph lies on the graph**: if, in the ball
`B(x₀, r)` and after the rigid motion `T`, the open set `Ω` is the region strictly above the graph
of the continuous `g`, and `x₀ ∈ ∂Ω`, then `(T x₀)_N = g((T x₀)')`. A point strictly above the
graph would be an interior point of `Ω`, and a point strictly below would have a neighbourhood
missing `Ω`. -/
theorem IsBoundaryGraphAt.last_eq_of_mem_frontier (hg : Continuous g) (hΩ : IsOpen Ω)
    (hx₀ : x₀ ∈ frontier Ω) (hr : 0 < r)
    (hgraph : Ω ∩ Metric.ball x₀ r =
      {x ∈ Metric.ball x₀ r | g (init (T x)) < T x (Fin.last d)}) :
    T x₀ (Fin.last d) = g (init (T x₀)) := by
  have hgraph' : ∀ x, x ∈ Ω ∩ Metric.ball x₀ r ↔
      x ∈ Metric.ball x₀ r ∧ g (init (T x)) < T x (Fin.last d) := fun x ↦ by
    rw [hgraph]; exact Iff.rfl
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- strictly below the graph: a neighbourhood of `x₀` misses `Ω`
    have hcont : Continuous fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦ T x (Fin.last d) :=
      continuous_apply_last.comp T.continuous
    have hWo : IsOpen {x : EuclideanSpace ℝ (Fin (d + 1)) |
        x ∈ Metric.ball x₀ r ∧ T x (Fin.last d) < g (init (T x))} :=
      Metric.isOpen_ball.inter (isOpen_lt hcont (hg.comp (continuous_init.comp T.continuous)))
    obtain ⟨x, ⟨hxb, hxlt⟩, hxΩ⟩ :=
      mem_closure_iff.1 hx₀.1 _ hWo ⟨Metric.mem_ball_self hr, hlt⟩
    have := ((hgraph' x).1 ⟨hxΩ, hxb⟩).2
    exact absurd this (not_lt.2 hxlt.le)
  · -- strictly above the graph: `x₀` is an interior point of `Ω`
    have : x₀ ∈ Ω := ((hgraph' x₀).2 ⟨Metric.mem_ball_self hr, hgt⟩).1
    exact hx₀.2 (by rwa [hΩ.interior_eq])

open EuclideanSpace in
/-- **The chart at a boundary point of a locally graphical domain**: if `Ω` is open and, near
`x₀ ∈ ∂Ω`, the region above the graph of a `C^n` function `g` in the coordinates `T x`, then
`x₀` lies in the range of a chart of class `C^n` of `Ω`. The chart is
`H y = Ψ⁻¹(Ψ x₀ + ε y)` for the straightening `Ψ` of the graph and a small `ε`. -/
theorem IsBoundaryGraphAt.exists_contDiffChart (hg : ContDiff ℝ n g) (hΩ : IsOpen Ω)
    (hx₀ : x₀ ∈ frontier Ω) (hr : 0 < r)
    (hgraph : Ω ∩ Metric.ball x₀ r =
      {x ∈ Metric.ball x₀ r | g (init (T x)) < T x (Fin.last d)}) :
    ∃ c : ContDiffChart n Ω, x₀ ∈ c.U := by
  set Ψ := graphStraighten T g with hΨ
  set Ψ' := graphUnstraighten T g with hΨ'
  have hΨΨ' : ∀ y, Ψ (Ψ' y) = y := graphStraighten_graphUnstraighten T g
  have hΨ'Ψ : ∀ x, Ψ' (Ψ x) = x := graphUnstraighten_graphStraighten T g
  have hΨd : ContDiff ℝ n Ψ := contDiff_graphStraighten T g hg
  have hΨ'd : ContDiff ℝ n Ψ' := contDiff_graphUnstraighten T g hg
  have hΨc : Continuous Ψ := hΨd.continuous
  have hΨ'c : Continuous Ψ' := hΨ'd.continuous
  set y₀ := Ψ x₀ with hy₀def
  have hy₀ : y₀ (Fin.last d) = 0 := by
    rw [hy₀def, hΨ, graphStraighten_apply_last,
      IsBoundaryGraphAt.last_eq_of_mem_frontier hg.continuous hΩ hx₀ hr hgraph, sub_self]
  -- the scale `ε` of the chart
  obtain ⟨δ, hδ, hδball⟩ : ∃ δ > 0, ∀ z, dist z y₀ < δ → Ψ' z ∈ Metric.ball x₀ r := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hΨ'c.continuousAt (x := y₀)) r hr
    exact ⟨δ, hδ, fun z hz ↦ by simpa [Metric.mem_ball, hy₀def, hΨ'Ψ] using h hz⟩
  set ε := δ / 4 with hε
  have hε0 : 0 < ε := by positivity
  set H : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) :=
    fun y ↦ Ψ' (y₀ + ε • y) with hH
  set Hinv : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) :=
    fun x ↦ ε⁻¹ • (Ψ x - y₀) with hHinv
  have hHinvH : ∀ y, Hinv (H y) = y := fun y ↦ by
    simp [hH, hHinv, hΨΨ', smul_smul, inv_mul_cancel₀ hε0.ne']
  have hHHinv : ∀ x, H (Hinv x) = x := fun x ↦ by
    simp [hH, hHinv, smul_smul, mul_inv_cancel₀ hε0.ne', hΨ'Ψ]
  have hHd : ContDiff ℝ n H := hΨ'd.comp (contDiff_const.add (contDiff_id.const_smul ε))
  have hHinvd : ContDiff ℝ n Hinv := (hΨd.sub contDiff_const).const_smul ε⁻¹
  let e : EuclideanSpace ℝ (Fin (d + 1)) ≃ₜ EuclideanSpace ℝ (Fin (d + 1)) :=
    { toFun := H
      invFun := Hinv
      left_inv := hHinvH
      right_inv := hHHinv
      continuous_toFun := hHd.continuous
      continuous_invFun := hHinvd.continuous }
  -- the chart sends the cylinder into the ball where `Ω` is a graph
  have hball : ∀ y ∈ unitChartCube d, H y ∈ Metric.ball x₀ r := fun y hy ↦ by
    refine hδball _ ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε0.le]
    have : ‖y‖ < 2 := by simpa using unitChartCube_subset_ball hy
    calc ε * ‖y‖ ≤ ε * 2 := by gcongr
      _ < δ := by rw [hε]; linarith
  have hmemΩ : ∀ y ∈ unitChartCube d, (H y ∈ Ω ↔ y ∈ unitChartCubePos d) := fun y hy ↦ by
    have h1 : H y ∈ Ω ↔ H y ∈ Ω ∩ Metric.ball x₀ r := (and_iff_left (hball y hy)).symm
    rw [h1, hgraph, mem_ofPred_eq, and_iff_right (hball y hy), mem_unitChartCubePos,
      and_iff_right hy]
    have hlast : T (H y) (Fin.last d) - g (init (T (H y))) = ε * y (Fin.last d) := by
      have := congrArg (fun z : EuclideanSpace ℝ (Fin (d + 1)) ↦ z (Fin.last d)) (hΨΨ' (y₀ + ε • y))
      simpa [hΨ, graphStraighten_apply_last, hy₀] using this
    rw [← sub_pos, hlast, mul_pos_iff_of_pos_left hε0]
  have hQpos : unitChartCube d ∩ H ⁻¹' Ω = unitChartCubePos d := by
    ext y
    constructor
    · rintro ⟨hy, hyΩ⟩
      exact (hmemΩ y hy).1 hyΩ
    · intro hy
      exact ⟨unitChartCubePos_subset hy, (hmemΩ y (unitChartCubePos_subset hy)).2 hy⟩
  have hQzero : unitChartCube d ∩ H ⁻¹' frontier Ω = unitChartCubeZero d := by
    have h1 : H ⁻¹' frontier Ω = frontier (H ⁻¹' Ω) := e.preimage_frontier Ω
    have h2 := frontier_inter_open_inter (s := H ⁻¹' Ω) isOpen_unitChartCube
    rw [h1, ← unitChartCube_inter_frontier_unitChartCubePos, ← hQpos,
      inter_comm (unitChartCube d) (H ⁻¹' Ω), inter_comm, ← h2, inter_comm]
  refine ⟨{ U := H '' unitChartCube d
            toFun := H
            invFun := Hinv
            isOpen_U := e.isOpenMap _ isOpen_unitChartCube
            contDiffOn := hHd.contDiffOn
            contDiffOn_invFun := hHinvd.contDiffOn
            bijOn := e.injective.injOn.bijOn_image
            invOn := ⟨fun y _ ↦ hHinvH y, fun x _ ↦ hHHinv x⟩
            image_pos := by rw [← hQpos, image_inter_preimage]
            image_zero := by rw [← hQzero, image_inter_preimage] }, ?_⟩
  exact ⟨0, zero_mem_unitChartCube, by simp [hH, hy₀def, hΨ'Ψ]⟩

end Bridge

/-- **Graph ⇒ chart**: a domain whose boundary is locally the graph of a `C^n` function, after a
rigid motion of the coordinates (`IsContDiffDomain`, the definition of Atkinson–Han), is an open
set of class `C^n` in the sense of [brezis2011functional] §9.2 (`IsContDiffChartDomain`). This is
the elementary direction of the equivalence of the two definitions, and the one through which
every result stated for chart domains reaches the graph domains of the finite element
literature. -/
theorem IsContDiffDomain.isContDiffChartDomain (h : IsContDiffDomain n Ω) :
    IsContDiffChartDomain n Ω := by
  refine ⟨h.isOpen, fun x₀ hx₀ ↦ ?_⟩
  obtain ⟨r, hr, T, g, hg, hgraph⟩ := h.isBoundaryOfClass x₀ hx₀
  exact IsBoundaryGraphAt.exists_contDiffChart hg h.isOpen hx₀ hr hgraph

/-- The half space is a chart domain of every class: the case "`Ω = ℝ^N_+`" of
[brezis2011functional] Theorem 9.7 read as an instance of the definition. -/
theorem isContDiffChartDomain_upperHalfSpace :
    IsContDiffChartDomain n (EuclideanSpace.upperHalfSpace d) :=
  IsContDiffDomain.isContDiffChartDomain
    ⟨EuclideanSpace.isOpen_upperHalfSpace, isBoundaryOfClass_upperHalfSpace contDiff_const⟩


/-! ### The partition of unity of Lemma 9.3 -/

section PartitionOfUnity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Lemma 9.3 (partition of unity)** of [brezis2011functional] §9.2: for a compact `Γ` in a
finite-dimensional space and open sets `U i`, `i` in a finite index type, covering `Γ`, there are
smooth `θ₀` and `θ i` with values in `[0, 1]`, `θ₀ + ∑ i, θ i = 1` everywhere, each `θ i` compactly
supported inside `U i`, and `θ₀` vanishing on a neighbourhood of `Γ`. Read off Mathlib's
`SmoothPartitionOfUnity.exists_isSubordinate` for the open cover of the whole space by `Γᶜ` and
the `U i ∩ B(0, R)`, `R` a radius of a ball containing `Γ` — the intersection with the ball is what
makes the supports compact. -/
theorem IsCompact.exists_contDiff_partitionOfUnity [FiniteDimensional ℝ E] {Γ : Set E}
    (hΓ : IsCompact Γ) {ι : Type*} [Fintype ι] {U : ι → Set E} (hU : ∀ i, IsOpen (U i))
    (hΓU : Γ ⊆ ⋃ i, U i) :
    ∃ (θ₀ : E → ℝ) (θ : ι → E → ℝ), ContDiff ℝ ∞ θ₀ ∧ (∀ i, ContDiff ℝ ∞ (θ i)) ∧
      (∀ x, θ₀ x ∈ Icc (0 : ℝ) 1) ∧ (∀ i x, θ i x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, θ₀ x + ∑ i, θ i x = 1) ∧ (∀ i, HasCompactSupport (θ i)) ∧
      (∀ i, tsupport (θ i) ⊆ U i) ∧ Disjoint (tsupport θ₀) Γ := by
  obtain ⟨R, hR⟩ := hΓ.isBounded.subset_ball 0
  let V : Option ι → Set E := fun j ↦ j.elim Γᶜ fun i ↦ U i ∩ Metric.ball 0 R
  have hVo : ∀ j, IsOpen (V j) := by
    rintro (_ | i)
    · exact hΓ.isClosed.isOpen_compl
    · exact (hU i).inter Metric.isOpen_ball
  have hVcov : (univ : Set E) ⊆ ⋃ j, V j := fun x _ ↦ by
    by_cases hx : x ∈ Γ
    · obtain ⟨i, hi⟩ := mem_iUnion.1 (hΓU hx)
      exact mem_iUnion.2 ⟨some i, hi, hR hx⟩
    · exact mem_iUnion.2 ⟨none, hx⟩
  obtain ⟨f, hf⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, E)) isClosed_univ V hVo hVcov
  refine ⟨f none, fun i ↦ f (some i), contMDiff_iff_contDiff.1 (f none).contMDiff,
    fun i ↦ contMDiff_iff_contDiff.1 (f (some i)).contMDiff,
    fun x ↦ ⟨f.nonneg none x, f.le_one none x⟩, fun i x ↦ ⟨f.nonneg _ x, f.le_one _ x⟩,
    fun x ↦ ?_, fun i ↦ ?_, fun i ↦ (hf (some i)).trans inter_subset_left,
    disjoint_compl_left.mono_left (hf none)⟩
  · have := f.sum_eq_one (mem_univ x)
    rwa [finsum_eq_sum_of_fintype, Fintype.sum_option] at this
  · exact Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _)
      (Metric.isBounded_ball.subset ((hf (some i)).trans inter_subset_right))

/-- The derivatives of a partition of unity `θ₀ + ∑ θ_i = 1` sum to zero. -/
theorem fderiv_add_sum_eq_zero_of_partition {ι : Type*} [Fintype ι] {θ₀ : E → ℝ}
    {θ : ι → E → ℝ} (hθ₀ : ContDiff ℝ ∞ θ₀) (hθ : ∀ i, ContDiff ℝ ∞ (θ i))
    (hsum : ∀ x, θ₀ x + ∑ i, θ i x = 1) (z v : E) :
    fderiv ℝ θ₀ z v + ∑ i, fderiv ℝ (θ i) z v = 0 := by
  have h1 : HasFDerivAt (fun x ↦ θ₀ x + ∑ i, θ i x)
      (fderiv ℝ θ₀ z + ∑ i, fderiv ℝ (θ i) z) z :=
    (hθ₀.differentiable (by simp) z).hasFDerivAt.add
      (HasFDerivAt.fun_sum fun i _ ↦ ((hθ i).differentiable (by simp) z).hasFDerivAt)
  have h2 : HasFDerivAt (fun x ↦ θ₀ x + ∑ i, θ i x) (0 : E →L[ℝ] ℝ) z := by
    have : (fun x ↦ θ₀ x + ∑ i, θ i x) = fun _ ↦ (1 : ℝ) := funext hsum
    rw [this]
    exact hasFDerivAt_const 1 z
  have := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) (h1.unique h2)
  simpa using this

end PartitionOfUnity

/-- A set disjoint from the frontier of an open set `Ω` meets `closure Ω` only inside `Ω`. This is
how "`θ₀|_Ω ∈ C_c^∞(Ω)`" is read for the `θ₀` of `IsCompact.exists_contDiff_partitionOfUnity` with
`Γ = ∂Ω`: `tsupport θ₀ ∩ closure Ω` is a closed subset of `Ω`, compact when `Ω` is bounded
(`IsClosed.isCompact_inter_closure_of_isBounded`). -/
theorem inter_closure_subset_of_disjoint_frontier {X : Type*} [TopologicalSpace X] {K Ω : Set X}
    (hΩ : IsOpen Ω) (h : Disjoint K (frontier Ω)) : K ∩ closure Ω ⊆ Ω := by
  rintro x ⟨hxK, hxc⟩
  by_contra hxΩ
  exact disjoint_left.1 h hxK ⟨hxc, fun hi ↦ hxΩ (hΩ.interior_eq ▸ hi)⟩

/-- In a proper space, a closed set meets the closure of a bounded set in a compact set. -/
theorem IsClosed.isCompact_inter_closure_of_isBounded {X : Type*} [PseudoMetricSpace X]
    [ProperSpace X] {K Ω : Set X} (hK : IsClosed K) (hΩ : Bornology.IsBounded Ω) :
    IsCompact (K ∩ closure Ω) :=
  Metric.isCompact_of_isClosed_isBounded (hK.inter isClosed_closure)
    (hΩ.closure.subset inter_subset_right)

/-! ### Bounded derivatives, and diffeomorphisms with bounded Jacobians -/

section Jacobian

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **A `C^1` function on a compact set has a bounded derivative on the interior of the set.** No
unique differentiability of the set is asked: the derivative is read off the local Taylor data of
`ContDiffWithinAt` at each point of the set, which at interior points is the ordinary derivative and
is continuous, hence bounded, near the point; compactness makes the bound uniform. -/
theorem ContDiffOn.exists_norm_fderiv_le_of_isCompact {f : E → F} {s : Set E}
    (hf : ContDiffOn 𝕜 1 f s) (hs : IsCompact s) :
    ∃ M, ∀ x ∈ interior s, ‖fderiv 𝕜 f x‖ ≤ M := by
  -- a local bound near each point of `s`
  have key : ∀ x ∈ s, ∃ W ∈ 𝓝 x, ∃ M : ℝ, ∀ y ∈ W ∩ interior s, ‖fderiv 𝕜 f y‖ ≤ M := by
    intro x hx
    have h1 : ContDiffWithinAt 𝕜 (0 + 1) f s x := by simpa using hf x hx
    obtain ⟨u, hu, -, f', hf', hf'c⟩ :=
      (contDiffWithinAt_succ_iff_hasFDerivWithinAt (n := 0) (by simp)).1 h1
    rw [insert_eq_of_mem hx] at hu
    have hxu : x ∈ u := mem_of_mem_nhdsWithin hx hu
    obtain ⟨v, hv, hcont⟩ := (contDiffWithinAt_zero hxu).1 hf'c
    have hxv : x ∈ v := mem_of_mem_nhdsWithin hxu hv
    have hev : ∀ᶠ y in 𝓝 x, y ∈ u ∩ v → ‖f' y‖ ≤ ‖f' x‖ + 1 := by
      rw [← eventually_nhdsWithin_iff]
      filter_upwards [(hcont x ⟨hxu, hxv⟩).eventually (Metric.ball_mem_nhds (f' x) one_pos)]
        with y hy
      have := mem_ball_iff_norm.1 hy
      linarith [norm_sub_norm_le (f' y) (f' x)]
    obtain ⟨A, hA, hAu⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hu
    obtain ⟨B, hB, hBv⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hv
    obtain ⟨C, hC, hCev⟩ := eventually_iff_exists_mem.1 hev
    obtain ⟨A', hA'A, hA'o, hxA'⟩ := mem_nhds_iff.1 hA
    refine ⟨A' ∩ B ∩ C, inter_mem (inter_mem (hA'o.mem_nhds hxA') hB) hC, ‖f' x‖ + 1, ?_⟩
    rintro y ⟨⟨⟨hyA', hyB⟩, hyC⟩, hyi⟩
    have hyu : y ∈ u := hAu ⟨hA'A hyA', interior_subset hyi⟩
    have hyv : y ∈ v := hBv ⟨hyB, hyu⟩
    have hu_nhds : u ∈ 𝓝 y := by
      refine mem_of_superset ((hA'o.inter isOpen_interior).mem_nhds ⟨hyA', hyi⟩) ?_
      rintro z ⟨hzA', hzi⟩
      exact hAu ⟨hA'A hzA', interior_subset hzi⟩
    rw [((hf' y hyu).hasFDerivAt hu_nhds).fderiv]
    exact hCev y hyC ⟨hyu, hyv⟩
  choose! W hW M hM using key
  obtain ⟨t, hts, htW⟩ := hs.elim_nhds_subcover W hW
  obtain ⟨M₀, hM₀⟩ := (t.image M).exists_le
  refine ⟨M₀, fun y hy ↦ ?_⟩
  obtain ⟨x, hxt, hyW⟩ := mem_iUnion₂.1 (htW (interior_subset hy))
  exact (hM x (hts x hxt) y ⟨hyW, hy⟩).trans (hM₀ _ (Finset.mem_image_of_mem M hxt))

end Jacobian

section Diffeo

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

/-- **A `C^1` diffeomorphism between open sets with bounded Jacobians**: the hypothesis bundle
of [brezis2011functional] Proposition 9.6 (with its footnote 6) — `H : s → t` is bijective with
inverse `Hinv`, `H ∈ C^1(s)`, `H⁻¹ ∈ C^1(t)`, and the derivatives are bounded by `M` on either
side, `Jac H ∈ L^∞(s)`, `Jac H⁻¹ ∈ L^∞(t)`. The sets are open, so that the derivatives are the
ordinary ones. A chart restricted to `Q₊` is an instance
(`ContDiffChart.isDiffeoOnWithBoundedJacobian_pos`). -/
structure IsDiffeoOnWithBoundedJacobian (H : E' → E) (Hinv : E → E') (s : Set E') (t : Set E)
    (M : ℝ) : Prop where
  isOpen_source : IsOpen s
  isOpen_target : IsOpen t
  bijOn : BijOn H s t
  invOn : InvOn Hinv H s t
  contDiffOn : ContDiffOn ℝ 1 H s
  contDiffOn_invFun : ContDiffOn ℝ 1 Hinv t
  norm_fderiv_le : ∀ y ∈ s, ‖fderiv ℝ H y‖ ≤ M
  norm_fderiv_invFun_le : ∀ x ∈ t, ‖fderiv ℝ Hinv x‖ ≤ M

namespace IsDiffeoOnWithBoundedJacobian

variable {H : E' → E} {Hinv : E → E'} {s : Set E'} {t : Set E} {M : ℝ}

/-- The inverse of a diffeomorphism with bounded Jacobians is one. -/
theorem symm (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) :
    IsDiffeoOnWithBoundedJacobian Hinv H t s M where
  isOpen_source := h.isOpen_target
  isOpen_target := h.isOpen_source
  bijOn := h.invOn.symm.bijOn (h.invOn.1.mapsTo h.bijOn.surjOn) h.bijOn.mapsTo
  invOn := h.invOn.symm
  contDiffOn := h.contDiffOn_invFun
  contDiffOn_invFun := h.contDiffOn
  norm_fderiv_le := h.norm_fderiv_invFun_le
  norm_fderiv_invFun_le := h.norm_fderiv_le

theorem mono_bound {M' : ℝ} (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) (hM : M ≤ M') :
    IsDiffeoOnWithBoundedJacobian H Hinv s t M' :=
  { h with
    norm_fderiv_le := fun y hy ↦ (h.norm_fderiv_le y hy).trans hM
    norm_fderiv_invFun_le := fun x hx ↦ (h.norm_fderiv_invFun_le x hx).trans hM }

/-- A diffeomorphism with bounded Jacobians restricts to every open subset `A` of its source, as
a diffeomorphism of `A` onto `H '' A`. -/
theorem restrict (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M)
    {A : Set E'} (hA : IsOpen A) (hAs : A ⊆ s) :
    IsDiffeoOnWithBoundedJacobian H Hinv A (H '' A) M where
  isOpen_source := hA
  isOpen_target := by
    have e : H '' A = t ∩ Hinv ⁻¹' A := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨h.bijOn.mapsTo (hAs hy), by rw [mem_preimage, h.invOn.1 (hAs hy)]; exact hy⟩
      · rintro ⟨hx, hx'⟩
        exact ⟨Hinv x, hx', h.invOn.2 hx⟩
    rw [e]
    exact h.contDiffOn_invFun.continuousOn.isOpen_inter_preimage h.isOpen_target hA
  bijOn := (h.bijOn.injOn.mono hAs).bijOn_image
  invOn := ⟨h.invOn.1.mono hAs, fun x hx ↦ h.invOn.2 (h.bijOn.mapsTo.image_subset (by
    exact (image_mono hAs) hx))⟩
  contDiffOn := h.contDiffOn.mono hAs
  contDiffOn_invFun := h.contDiffOn_invFun.mono (h.bijOn.mapsTo.image_subset.trans' (image_mono
    hAs))
  norm_fderiv_le := fun y hy ↦ h.norm_fderiv_le y (hAs hy)
  norm_fderiv_invFun_le := fun x hx ↦
    h.norm_fderiv_invFun_le x (h.bijOn.mapsTo.image_subset (image_mono hAs hx))

end IsDiffeoOnWithBoundedJacobian

end Diffeo

namespace ContDiffChart

variable (c : ContDiffChart n Ω)

/-- **The Jacobians of a chart are bounded**: the derivative of `H` on `Q` and that of `H⁻¹` on
`U` are bounded by a common constant, `H` and `H⁻¹` being `C^1` on the compact closures. -/
theorem exists_norm_fderiv_le (hn : 1 ≤ n) :
    ∃ M, (∀ y ∈ unitChartCube d, ‖fderiv ℝ c.toFun y‖ ≤ M) ∧
      ∀ x ∈ c.U, ‖fderiv ℝ c.invFun x‖ ≤ M := by
  obtain ⟨M₁, hM₁⟩ :=
    (c.contDiffOn.of_le hn).exists_norm_fderiv_le_of_isCompact isCompact_closure_unitChartCube
  obtain ⟨M₂, hM₂⟩ :=
    (c.contDiffOn_invFun.of_le hn).exists_norm_fderiv_le_of_isCompact c.isCompact_closure_U
  refine ⟨max M₁ M₂, fun y hy ↦ ?_, fun x hx ↦ ?_⟩
  · exact (hM₁ y (isOpen_unitChartCube.subset_interior_iff.2 subset_closure hy)).trans
      (le_max_left _ _)
  · exact (hM₂ x (c.isOpen_U.subset_interior_iff.2 subset_closure hx)).trans (le_max_right _ _)

/-- **A chart is a `C^1` diffeomorphism of `Q` onto `U` with bounded Jacobians.** -/
theorem isDiffeoOnWithBoundedJacobian (hn : 1 ≤ n) :
    ∃ M, IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (unitChartCube d) c.U M := by
  obtain ⟨M, hM₁, hM₂⟩ := c.exists_norm_fderiv_le hn
  exact ⟨M, isOpen_unitChartCube, c.isOpen_U, c.bijOn, c.invOn,
    (c.contDiffOn.of_le hn).mono subset_closure, (c.contDiffOn_invFun.of_le hn).mono subset_closure,
    hM₁, hM₂⟩

/-- **A chart restricted to the half cylinder is a `C^1` diffeomorphism of `Q₊` onto `U ∩ Ω` with
bounded Jacobians**, the form in which [brezis2011functional] Proposition 9.6 is applied in the
proof of Theorem 9.7 (step (b), the transfer `v_i(y) = u(H_i(y))`). -/
theorem isDiffeoOnWithBoundedJacobian_pos (hn : 1 ≤ n) (hΩ : IsOpen Ω) :
    ∃ M, IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (unitChartCubePos d) (c.U ∩ Ω) M := by
  obtain ⟨M, hM₁, hM₂⟩ := c.exists_norm_fderiv_le hn
  refine ⟨M, isOpen_unitChartCubePos, c.isOpen_U.inter hΩ, ?_,
    ⟨c.invOn.1.mono unitChartCubePos_subset, c.invOn.2.mono inter_subset_left⟩,
    (c.contDiffOn.of_le hn).mono (unitChartCubePos_subset.trans subset_closure),
    (c.contDiffOn_invFun.of_le hn).mono (inter_subset_left.trans subset_closure),
    fun y hy ↦ hM₁ y (unitChartCubePos_subset hy), fun x hx ↦ hM₂ x hx.1⟩
  rw [← c.image_pos]
  exact (c.injOn.mono unitChartCubePos_subset).bijOn_image

end ContDiffChart

end
