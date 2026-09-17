/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Interval/Basic.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Normed.Lp.SmoothApprox
import Numlib.Analysis.Sobolev.Interval.Higher

/-!
# The space `W_0^{1,p}(I)`

The closure `W_0^{1,p}(I)` of the test functions in `W^{1,p}(I)`, [brezis2011functional] §8.3,
for every exponent `1 ≤ p ≤ ∞` (the boundary characterization for `p < ∞`) and every open
interval `I`. The space `SobolevIntervalLpZero m p I` itself is defined in
`Numlib/Analysis/Sobolev/Interval/Basic.lean` as the multi-index `SobolevMultiIndexZero`.

## Main statements

* `SobolevIntervalLp.evalCLM'`: evaluation of the continuous representative at a point of `Ī`
  as a bounded linear functional, and `SobolevIntervalLpZero.rep_frontier_eq_zero` (Theorem 8.12,
  the easy direction): an element of `W_0^{1,p}(I)` vanishes on `∂I`.
* `SobolevIntervalLpZero.norm_deriv_zero_le`, `norm_le_mul_norm_deriv`,
  `eLpNorm_le_mul_eLpNorm_deriv` (**Proposition 8.13, Poincaré's inequality**): for
  `u ∈ W_0^{1,p}(a, b)`, `‖u‖_p ≤ (b - a)/p^{1/p} ‖u'‖_p` — the constant is `(b - a)/√2` at
  `p = 2` and `b - a` at `p = ∞` — so the seminorm `‖u'‖_p` is a norm on `W_0^{1,p}(a, b)`
  equivalent to the `W^{1,p}` norm; from the elementary form
  `SobolevIntervalLp.eLpNorm_integral_le` of `Numlib/Analysis/Sobolev/Interval/Higher.lean`.
* `SobolevIntervalLpZero.mem_of_rep_frontier_eq_zero_of_bounded` (Theorem 8.12, converse,
  bounded interval) and `mem_sobolevIntervalLpZero_iff` (**Theorem 8.12**):
  `u ∈ W_0^{1,p}(I) ↔ u = 0 on ∂I`, `1 ≤ p < ∞`, on every open interval;
  `sobolevIntervalLpZero_top` (Remark 13): `W_0^{1,p}(ℝ) = W^{1,p}(ℝ)`;
  `SobolevIntervalLpZero.mem_of_hasCompactSupport` (Remark 14 (ii));
  `SobolevIntervalLp.exists_not_mem_closure_testFunctions` (Remark 9).
* `SobolevIntervalLp.cutoff` and `tendsto_cutoff`: the cut-off sequence `ζ_n u → u` in
  `W^{1,p}(I)` of the proof of Theorem 8.7, used to reduce the unbounded case of Theorem 8.12 to
  the bounded one.
* `SobolevIntervalLp.abs_rep_sub_average_le`, `SobolevIntervalLpZero.abs_rep_le_half_eLpNorm_deriv`,
  `SobolevIntervalLp.eLpNorm_sub_average_le` (Problem 47 A.1, A.4, A.6): the Poincaré–Wirtinger
  inequalities `‖u - ū‖_∞ ≤ ‖u'‖_1` and `‖u‖_∞ ≤ ½ ‖u'‖_1` on `W_0^{1,1}`.

## Design

* `u = 0` on `∂I` is `∀ x ∈ frontier (I : Set ℝ), rep u x = 0`; the frontier of an open interval
  is its set of finite endpoints (empty for `ℝ`, so Remark 13 is the instance `I = ℝ`).
* The converse of Theorem 8.12 is not proved by the book's truncation `G(nu)/n`. On a bounded
  interval the derivative `u'` has zero mean and is approximated in `L^p` by a test function of
  zero mean, whose primitive is a test function converging to `u` by Poincaré's inequality (the
  proof of `SobolevIntervalZero.mem_of_rep_eq_zero` of `Numlib/Analysis/Sobolev/Interval.lean`
  at `p = 2`). On an unbounded interval the cut-offs `ζ_n u` vanish off the bounded interval
  `I ∩ (-2n, 2n)`, on which they lie in `W_0^{1,p}` by the bounded case
  (`SobolevIntervalLpZero.mem_of_forall_eq_zero_off_Ioo`, the restriction argument), and
  `ζ_n u → u` in `W^{1,p}(I)`; Remark 14 (ii) then follows from Theorem 8.12.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Interval Topology

noncomputable section

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

/-! ### Evaluation at a point of the closure -/

variable (p I) in
/-- **Evaluation of the continuous representative** at a point `x ∈ Ī` as a bounded linear
functional on `W^{1,p}(I)`, of norm at most `embeddingConst p I` (Theorem 8.8 (5)). -/
def evalCLM' (hI : (I : Set ℝ).OrdConnected) {x : ℝ} (hx : x ∈ closure (I : Set ℝ)) :
    StrongDual ℝ (SobolevIntervalLp 1 p I) :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ rep u x
      map_add' := fun u v ↦ rep_add hI u v hx
      map_smul' := fun r u ↦ rep_smul hI r u hx } (embeddingConst p I) fun u ↦ by
    rw [Real.norm_eq_abs]
    exact abs_rep_le hI u hx

/-- Evaluation is the value of the continuous representative. -/
@[simp]
theorem evalCLM'_apply (hI : (I : Set ℝ).OrdConnected) {x : ℝ} (hx : x ∈ closure (I : Set ℝ))
    (u : SobolevIntervalLp 1 p I) : evalCLM' p I hI hx u = rep u x := rfl

/-- A point of the frontier of an open set is not in the set. -/
theorem _root_.TopologicalSpace.Opens.notMem_of_mem_frontier {x : ℝ}
    (hx : x ∈ frontier (I : Set ℝ)) : x ∉ (I : Set ℝ) := by
  rw [I.isOpen.frontier_eq] at hx
  exact hx.2

/-- A point of the frontier of an open set lies in its closure. -/
theorem _root_.TopologicalSpace.Opens.mem_closure_of_mem_frontier {x : ℝ}
    (hx : x ∈ frontier (I : Set ℝ)) : x ∈ closure (I : Set ℝ) :=
  frontier_subset_closure hx

end SobolevIntervalLp

namespace SobolevIntervalLpZero

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

open SobolevIntervalLp

/-- An element of `W^{1,p}(I)` whose function is a test function lies in `W_0^{1,p}(I)`. -/
theorem mem_of_fn_ae_eq (φ : 𝓓(I, ℝ)) {u : SobolevIntervalLp 1 p I}
    (hu : fn u =ᵐ[volume.restrict I] φ) : u ∈ SobolevIntervalLpZero 1 p I :=
  SobolevMultiIndexZero.testFunctions_le ⟨φ, hu⟩

/-- Every test function on `I` is the function of an element of `W_0^{1,p}(I)`. -/
theorem exists_mem_fn_ae_eq (φ : 𝓓(I, ℝ)) :
    ∃ u ∈ SobolevIntervalLpZero 1 p I, fn u =ᵐ[volume.restrict I] φ :=
  let ⟨u, hu, hφ⟩ := TestFunction.exists_mem_sobolevMultiIndex_testFunctions
    (b := Module.Basis.singleton Unit ℝ) (k := 1) (p := p) φ
  ⟨u, SobolevMultiIndexZero.testFunctions_le hu, hφ⟩

/-- **Theorem 8.12 of [brezis2011functional], the easy direction**: an element of `W_0^{1,p}(I)`
vanishes on the boundary of `I`: evaluation at a point of `∂I` is a continuous linear functional
on `W^{1,p}(I)` vanishing on the test functions, hence on their closure. -/
theorem rep_frontier_eq_zero (hI : (I : Set ℝ).OrdConnected) {u : SobolevIntervalLp 1 p I}
    (hu : u ∈ SobolevIntervalLpZero 1 p I) {x : ℝ} (hx : x ∈ frontier (I : Set ℝ)) :
    rep u x = 0 := by
  have hxc : x ∈ closure (I : Set ℝ) := I.mem_closure_of_mem_frontier hx
  have hker : SobolevMultiIndex.testFunctions ℝ (Module.Basis.singleton Unit ℝ) 1 p I volume
      ≤ LinearMap.ker (evalCLM' p I hI hxc : SobolevIntervalLp 1 p I →ₗ[ℝ] ℝ) := by
    rintro v ⟨φ, hφ⟩
    change rep v x = 0
    rw [rep_eq_of_continuousOn hI v φ.continuous.continuousOn hφ hxc]
    exact φ.eq_zero_of_notMem (I.notMem_of_mem_frontier hx)
  exact Submodule.topologicalClosure_minimal _ hker (evalCLM' p I hI hxc).isClosed_ker hu

end SobolevIntervalLpZero

/-! ### Poincaré's inequality on `W_0^{1,p}(a, b)` -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {a b : ℝ}

/-- An element of `W^{1,p}(a, b)` whose representative vanishes at `a` is the primitive of its
derivative: `ũ(x) = ∫_a^x u'` for `x ∈ [a, b]`. -/
theorem rep_eq_integral_of_rep_left_eq_zero (hab : a < b)
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) (ha : rep u a = 0) {x : ℝ} (hx : x ∈ Icc a b) :
    rep u x = ∫ t in a..x, deriv u 1 t := by
  have h := rep_sub_rep (ordConnected_coe_Ioo a b) u (x := a) (y := x)
    (by rw [closure_coe_Ioo hab]; exact left_mem_Icc.2 hab.le)
    (by rw [closure_coe_Ioo hab]; exact hx)
  rwa [ha, sub_zero] at h

/-- **Poincaré's inequality** for an element of `W^{1,p}(a, b)` vanishing at `a`:
`‖u‖_{L^p} ≤ (b - a)/p^{1/p} ‖u'‖_{L^p}`, in `ℝ≥0∞`. -/
theorem eLpNorm_le_mul_eLpNorm_deriv_of_rep_left_eq_zero (hab : a < b)
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) (ha : rep u a = 0) :
    eLpNorm (fn u) p (volume.restrict (Ioo a b))
      ≤ ENNReal.ofReal ((b - a) / p.toReal ^ p.toReal⁻¹)
        * eLpNorm (deriv u 1) p (volume.restrict (Ioo a b)) := by
  have hfn : fn u =ᵐ[volume.restrict (Ioo a b)] fun x ↦ ∫ t in a..x, deriv u 1 t :=
    (fn_ae_eq_rep (ordConnected_coe_Ioo a b) u).trans ((ae_restrict_iff' measurableSet_Ioo).2
      (Eventually.of_forall fun x hx ↦
        rep_eq_integral_of_rep_left_eq_zero hab u ha (Ioo_subset_Icc_self hx)))
  rw [eLpNorm_congr_ae hfn]
  exact eLpNorm_integral_le hab.le (integrableOn_deriv_Ioo u 1)

/-- **Poincaré's inequality** for an element of `W^{1,p}(a, b)` vanishing at `a`, in the norms
of `L^p(a, b)`: `‖u‖_p ≤ (b - a)/p^{1/p} ‖u'‖_p`. -/
theorem norm_deriv_zero_le_of_rep_left_eq_zero (hab : a < b)
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) (ha : rep u a = 0) :
    ‖deriv u 0‖ ≤ (b - a) / p.toReal ^ p.toReal⁻¹ * ‖deriv u 1‖ := by
  rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_ofReal (poincareConst_nonneg hab.le),
    ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _)) ?_
  exact eLpNorm_le_mul_eLpNorm_deriv_of_rep_left_eq_zero hab u ha

/-- **Poincaré's inequality** for an element of `W^{1,p}(a, b)` vanishing at `a`, in the norm of
`W^{1,p}(a, b)`: `‖u‖_{W^{1,p}} ≤ ((b - a)/p^{1/p} + 1) ‖u'‖_p`. -/
theorem norm_le_mul_norm_deriv_of_rep_left_eq_zero (hab : a < b)
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) (ha : rep u a = 0) :
    ‖u‖ ≤ ((b - a) / p.toReal ^ p.toReal⁻¹ + 1) * ‖deriv u 1‖ := by
  refine (norm_le_sum_norm_deriv u).trans ?_
  rw [Fin.sum_univ_two, add_mul, one_mul]
  exact add_le_add (norm_deriv_zero_le_of_rep_left_eq_zero hab u ha) le_rfl

end SobolevIntervalLp

namespace SobolevIntervalLpZero

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {a b : ℝ}

open SobolevIntervalLp

/-- The representative of an element of `W_0^{1,p}(a, b)` vanishes at `a`. -/
theorem rep_left_eq_zero (hab : a < b) {u : SobolevIntervalLp 1 p (Opens.Ioo a b)}
    (hu : u ∈ SobolevIntervalLpZero 1 p (Opens.Ioo a b)) : rep u a = 0 :=
  rep_frontier_eq_zero (ordConnected_coe_Ioo a b) hu
    (by rw [Opens.coe_Ioo, frontier_Ioo hab]; exact mem_insert a {b})

/-- The representative of an element of `W_0^{1,p}(a, b)` vanishes at `b`. -/
theorem rep_right_eq_zero (hab : a < b) {u : SobolevIntervalLp 1 p (Opens.Ioo a b)}
    (hu : u ∈ SobolevIntervalLpZero 1 p (Opens.Ioo a b)) : rep u b = 0 :=
  rep_frontier_eq_zero (ordConnected_coe_Ioo a b) hu
    (by rw [Opens.coe_Ioo, frontier_Ioo hab]; exact mem_insert_of_mem a rfl)

/-- An element of `W_0^{1,p}(a, b)` is the primitive of its derivative: `ũ(x) = ∫_a^x u'`. -/
theorem rep_eq_integral (hab : a < b) {u : SobolevIntervalLp 1 p (Opens.Ioo a b)}
    (hu : u ∈ SobolevIntervalLpZero 1 p (Opens.Ioo a b)) {x : ℝ} (hx : x ∈ Icc a b) :
    rep u x = ∫ t in a..x, deriv u 1 t :=
  rep_eq_integral_of_rep_left_eq_zero hab u (rep_left_eq_zero hab hu) hx

/-- **Proposition 8.13 of [brezis2011functional] (Poincaré's inequality)**, in `ℝ≥0∞`: for
`u ∈ W_0^{1,p}(a, b)`, `1 ≤ p ≤ ∞`, `‖u‖_{L^p} ≤ (b - a)/p^{1/p} ‖u'‖_{L^p}` (`p^{1/p} = 1` at
`p = ∞`); at `p = 2` the constant is `(b - a)/√2`. -/
theorem eLpNorm_le_mul_eLpNorm_deriv (hab : a < b) {u : SobolevIntervalLp 1 p (Opens.Ioo a b)}
    (hu : u ∈ SobolevIntervalLpZero 1 p (Opens.Ioo a b)) :
    eLpNorm (fn u) p (volume.restrict (Ioo a b))
      ≤ ENNReal.ofReal ((b - a) / p.toReal ^ p.toReal⁻¹)
        * eLpNorm (deriv u 1) p (volume.restrict (Ioo a b)) :=
  eLpNorm_le_mul_eLpNorm_deriv_of_rep_left_eq_zero hab u (rep_left_eq_zero hab hu)

/-- **Proposition 8.13 of [brezis2011functional] (Poincaré's inequality)**, in the norms of
`L^p(a, b)`: for `u ∈ W_0^{1,p}(a, b)`, `‖u‖_p ≤ (b - a)/p^{1/p} ‖u'‖_p`. -/
theorem norm_deriv_zero_le (hab : a < b) {u : SobolevIntervalLp 1 p (Opens.Ioo a b)}
    (hu : u ∈ SobolevIntervalLpZero 1 p (Opens.Ioo a b)) :
    ‖deriv u 0‖ ≤ (b - a) / p.toReal ^ p.toReal⁻¹ * ‖deriv u 1‖ :=
  norm_deriv_zero_le_of_rep_left_eq_zero hab u (rep_left_eq_zero hab hu)

/-- **Proposition 8.13 of [brezis2011functional], the book's (13)**: on `W_0^{1,p}(a, b)` the
`W^{1,p}` norm is controlled by `‖u'‖_p`: `‖u‖_{W^{1,p}} ≤ ((b - a)/p^{1/p} + 1) ‖u'‖_p`. Together
with `‖u'‖_p ≤ ‖u‖` (`SobolevIntervalLp.norm_deriv_le`), `‖u'‖_p` is a norm on `W_0^{1,p}(a, b)`
equivalent to the `W^{1,p}` norm. -/
theorem norm_le_mul_norm_deriv (hab : a < b) {u : SobolevIntervalLp 1 p (Opens.Ioo a b)}
    (hu : u ∈ SobolevIntervalLpZero 1 p (Opens.Ioo a b)) :
    ‖u‖ ≤ ((b - a) / p.toReal ^ p.toReal⁻¹ + 1) * ‖deriv u 1‖ :=
  norm_le_mul_norm_deriv_of_rep_left_eq_zero hab u (rep_left_eq_zero hab hu)

/-- On `W_0^{1,p}(a, b)`, `‖u'‖_p = 0` only for `u = 0`. -/
theorem norm_deriv_one_eq_zero_iff (hab : a < b) {u : SobolevIntervalLp 1 p (Opens.Ioo a b)}
    (hu : u ∈ SobolevIntervalLpZero 1 p (Opens.Ioo a b)) : ‖deriv u 1‖ = 0 ↔ u = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, deriv_zero_elem, norm_zero]⟩
  have := norm_le_mul_norm_deriv hab hu
  rw [h, mul_zero] at this
  exact norm_le_zero_iff.1 this

end SobolevIntervalLpZero

/-! ### Remark 9: `W_0^{1,p}(a, b) ≠ W^{1,p}(a, b)` -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {a b : ℝ}

/-- **Remark 9 of [brezis2011functional], Chapter 8**: on a bounded interval `(a, b)`, the
constant function `1` lies in `W^{1,p}(a, b)` but not in the closure `W_0^{1,p}(a, b)` of the
test functions, since its representative is `1` at `a` (Theorem 8.12). So the test functions are
not dense in `W^{1,p}(a, b)`, in contrast to `L^p(a, b)`
(`MeasureTheory.Lp.dense_contDiff_tsupport_subset`). -/
theorem exists_not_mem_closure_testFunctions (hab : a < b) :
    ∃ u : SobolevIntervalLp 1 p (Opens.Ioo a b),
      fn u =ᵐ[volume.restrict (Ioo a b)] (fun _ ↦ (1 : ℝ)) ∧
        u ∉ SobolevIntervalLpZero 1 p (Opens.Ioo a b) := by
  obtain ⟨u, hu⟩ := (memSobolevIntervalLp_of_contDiffOn_Icc (p := p) hab
    (contDiffOn_const (c := (1 : ℝ)))).1.exists_sobolevIntervalLp
  refine ⟨u, hu, fun h ↦ ?_⟩
  have h1 := rep_eq_of_continuousOn (ordConnected_coe_Ioo a b) u continuousOn_const hu
    (x := a) (by rw [closure_coe_Ioo hab]; exact left_mem_Icc.2 hab.le)
  rw [SobolevIntervalLpZero.rep_left_eq_zero hab h] at h1
  exact zero_ne_one h1

/-- **Remark 9 of [brezis2011functional], Chapter 8**: `W_0^{1,p}(a, b)` is a proper subspace of
`W^{1,p}(a, b)`. -/
theorem sobolevIntervalLpZero_Ioo_ne_top (hab : a < b) :
    SobolevIntervalLpZero 1 p (Opens.Ioo a b) ≠ ⊤ := fun h ↦
  let ⟨_, _, hu⟩ := exists_not_mem_closure_testFunctions (p := p) hab
  hu (h ▸ Submodule.mem_top)

end SobolevIntervalLp

/-! ### Poincaré–Wirtinger: Problem 47 A.1, A.4, A.6 -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {a b : ℝ}

/-- The continuous representative of an element of `W^{1,p}(a, b)` is integrable on `(a, b)`. -/
theorem integrableOn_rep_Ioo (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    IntegrableOn (rep u) (Ioo a b) := by
  have hcl : Icc a b ⊆ closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) := by rw [closure_coe_Ioo hab]
  exact (((continuousOn_rep (ordConnected_coe_Ioo a b) u).mono hcl).integrableOn_Icc).mono_set
    Ioo_subset_Icc_self

/-- **Poincaré–Wirtinger, Problem 47 A.1 of [brezis2011functional]** (Comments on Chapter 8,
1 (i)), for every `1 ≤ p ≤ ∞`: for `u ∈ W^{1,p}(a, b)` and `ū` the mean of `u` on `(a, b)`,
`|ũ(x) - ū| ≤ (b - a)^{1 - 1/p} ‖u'‖_p` for every `x ∈ [a, b]` — `‖u - ū‖_∞ ≤ ‖u'‖_1` at `p = 1`.
Indeed `ũ(x) - ū` is the mean over `y` of `ũ(x) - ũ(y) = ∫_y^x u'`, which is bounded by Hölder;
the book's intermediate-value argument is not needed. -/
theorem abs_rep_sub_average_le (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x : ℝ}
    (hx : x ∈ Icc a b) :
    |rep u x - ⨍ y in Ioo a b, fn u y| ≤ (b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖ := by
  have hI := ordConnected_coe_Ioo a b
  have hcl : Icc a b ⊆ closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) := by rw [closure_coe_Ioo hab]
  have hvol : volume (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]; exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
  have hvol' : volume (Ioo a b) ≠ ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hfn : fn u =ᵐ[volume.restrict (Ioo a b)] rep u := fn_ae_eq_rep hI u
  have hbd : ∀ y ∈ Ioo a b, ‖rep u x - rep u y‖ ≤ (b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖ := by
    intro y hy
    rw [Real.norm_eq_abs, mul_comm]
    refine (abs_rep_sub_rep_le hI u (hcl hx) (hcl (Ioo_subset_Icc_self hy))).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) ?_
      (one_sub_toReal_inv_nonneg Fact.out)) (norm_nonneg _)
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  rw [average_congr hfn, ← setAverage_const hvol hvol' (rep u x),
    ← setAverage_sub (integrableOn_const hvol') (integrableOn_rep_Ioo hab u), setAverage_eq,
    smul_eq_mul, abs_mul, abs_inv, abs_of_nonneg measureReal_nonneg, ← Real.norm_eq_abs]
  refine (mul_le_mul_of_nonneg_left (norm_setIntegral_le_of_norm_le_const hvol'.lt_top hbd)
    (inv_nonneg.2 measureReal_nonneg)).trans (le_of_eq ?_)
  rw [Real.volume_real_Ioo_of_le hab.le, mul_comm _ (b - a), ← mul_assoc,
    inv_mul_cancel₀ (sub_pos.2 hab).ne', one_mul]

/-- **Problem 47 A.6 of [brezis2011functional], the Poincaré–Wirtinger inequality in `L^q`**:
for `u ∈ W^{1,p}(a, b)`, `1 ≤ p ≤ ∞`, and every `q`,
`‖u - ū‖_{L^q(a, b)} ≤ (b - a)^{1/q} (b - a)^{1 - 1/p} ‖u'‖_p`, from A.1 and
`‖·‖_q ≤ |I|^{1/q} ‖·‖_∞`. -/
theorem eLpNorm_sub_average_le (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b))
    (q : ℝ≥0∞) :
    eLpNorm (fun x ↦ fn u x - ⨍ y in Ioo a b, fn u y) q (volume.restrict (Ioo a b))
      ≤ ENNReal.ofReal (b - a) ^ q.toReal⁻¹
        * ENNReal.ofReal ((b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖) := by
  have hI := ordConnected_coe_Ioo a b
  have hcl : Icc a b ⊆ closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) := by rw [closure_coe_Ioo hab]
  have hfn : fn u =ᵐ[volume.restrict (Ioo a b)] rep u := fn_ae_eq_rep hI u
  have e : (fun x ↦ fn u x - ⨍ y in Ioo a b, fn u y)
      =ᵐ[volume.restrict (Ioo a b)] fun x ↦ rep u x - ⨍ y in Ioo a b, fn u y :=
    hfn.mono fun x hx ↦ by simp only [hx]
  rw [eLpNorm_congr_ae e]
  have h := eLpNorm_le_of_ae_bound (μ := volume.restrict (Ioo a b)) (p := q)
    (f := fun x ↦ rep u x - ⨍ y in Ioo a b, fn u y)
    (C := (b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖)
    ((((continuousOn_rep hI u).mono hcl).sub continuousOn_const).mono
      Ioo_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioo)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ by
      rw [Real.norm_eq_abs]
      exact abs_rep_sub_average_le hab u (Ioo_subset_Icc_self hx)))
  rwa [Measure.restrict_apply_univ, Real.volume_Ioo] at h

end SobolevIntervalLp

namespace SobolevIntervalLpZero

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {a b : ℝ}

open SobolevIntervalLp

/-- **Problem 47 A.4 of [brezis2011functional]**, in `ℝ≥0∞` and for every `1 ≤ p ≤ ∞`: for
`u ∈ W_0^{1,p}(a, b)` and `x ∈ [a, b]`, `2 |ũ(x)| ≤ ∫_a^b |u'| ≤ (b - a)^{1 - 1/p} ‖u'‖_p`, since
`|ũ(x)| ≤ ∫_a^x |u'|` and `|ũ(x)| ≤ ∫_x^b |u'|` (`ũ` vanishes at both ends). -/
theorem two_mul_enorm_rep_le (hab : a < b) {u : SobolevIntervalLp 1 p (Opens.Ioo a b)}
    (hu : u ∈ SobolevIntervalLpZero 1 p (Opens.Ioo a b)) {x : ℝ} (hx : x ∈ Icc a b) :
    2 * ‖rep u x‖ₑ ≤ ENNReal.ofReal (b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖ₑ := by
  have hI := ordConnected_coe_Ioo a b
  have hcl : Icc a b ⊆ closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) := by rw [closure_coe_Ioo hab]
  have h1 : ‖rep u x‖ₑ ≤ ∫⁻ t in Ioc a x, ‖deriv u 1 t‖ₑ := by
    rw [rep_eq_integral hab hu hx, intervalIntegral.integral_of_le hx.1]
    exact enorm_integral_le_lintegral_enorm _
  have h2 : ‖rep u x‖ₑ ≤ ∫⁻ t in Ioc x b, ‖deriv u 1 t‖ₑ := by
    have h := rep_sub_rep hI u (hcl hx) (hcl (right_mem_Icc.2 hab.le))
    rw [rep_right_eq_zero hab hu, zero_sub, intervalIntegral.integral_of_le hx.2] at h
    rw [← enorm_neg, h]
    exact enorm_integral_le_lintegral_enorm _
  calc 2 * ‖rep u x‖ₑ = ‖rep u x‖ₑ + ‖rep u x‖ₑ := two_mul _
    _ ≤ (∫⁻ t in Ioc a x, ‖deriv u 1 t‖ₑ) + ∫⁻ t in Ioc x b, ‖deriv u 1 t‖ₑ := add_le_add h1 h2
    _ = ∫⁻ t in Ioc a b, ‖deriv u 1 t‖ₑ := by
        rw [← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
          Ioc_union_Ioc_eq_Ioc hx.1 hx.2]
    _ ≤ volume (Ioc a b) ^ (1 - p.toReal⁻¹)
        * eLpNorm (deriv u 1) p (volume.restrict (Ioc a b)) := by
        have := setLIntegral_enorm_le_rpow_mul_eLpNorm (p := p) (μ := volume.restrict (Ioc a b))
          (deriv u 1) MeasurableSet.univ
        rwa [Measure.restrict_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter] at this
    _ ≤ ENNReal.ofReal (b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖ₑ := by
        rw [Real.volume_Ioc, Lp.enorm_def]
        exact mul_le_mul' le_rfl
          (eLpNorm_restrict_le_of_subset_closure hI (Ioc_subset_Icc_self.trans hcl) _ _)

/-- **Problem 47 A.4 of [brezis2011functional]** (Comments on Chapter 8, 1 (i)), for every
`1 ≤ p ≤ ∞`: for `u ∈ W_0^{1,p}(a, b)` and `x ∈ [a, b]`,
`|ũ(x)| ≤ ½ (b - a)^{1 - 1/p} ‖u'‖_p` — `‖u‖_∞ ≤ ½ ‖u'‖_1` at `p = 1`. -/
theorem abs_rep_le_half_eLpNorm_deriv (hab : a < b) {u : SobolevIntervalLp 1 p (Opens.Ioo a b)}
    (hu : u ∈ SobolevIntervalLpZero 1 p (Opens.Ioo a b)) {x : ℝ} (hx : x ∈ Icc a b) :
    |rep u x| ≤ 2⁻¹ * ((b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖) := by
  have h := ENNReal.toReal_mono (ofReal_rpow_mul_enorm_ne_top (sub_pos.2 hab) _ _)
    (two_mul_enorm_rep_le hab hu hx)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, toReal_enorm, Real.norm_eq_abs,
    toReal_ofReal_rpow_mul_enorm (sub_pos.2 hab).le] at h
  rw [← le_div_iff₀' two_pos] at h
  rwa [div_eq_inv_mul] at h

/-- **Problem 47 A.6 of [brezis2011functional], the Poincaré inequality in `L^q`**: for
`u ∈ W_0^{1,p}(a, b)`, `1 ≤ p ≤ ∞`, and every `q`,
`‖u‖_{L^q(a, b)} ≤ ½ (b - a)^{1/q} (b - a)^{1 - 1/p} ‖u'‖_p`, from A.4 and
`‖·‖_q ≤ |I|^{1/q} ‖·‖_∞`. -/
theorem eLpNorm_le_half_mul (hab : a < b) {u : SobolevIntervalLp 1 p (Opens.Ioo a b)}
    (hu : u ∈ SobolevIntervalLpZero 1 p (Opens.Ioo a b)) (q : ℝ≥0∞) :
    eLpNorm (fn u) q (volume.restrict (Ioo a b))
      ≤ ENNReal.ofReal (b - a) ^ q.toReal⁻¹
        * ENNReal.ofReal (2⁻¹ * ((b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖)) := by
  have hI := ordConnected_coe_Ioo a b
  have hcl : Icc a b ⊆ closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) := by rw [closure_coe_Ioo hab]
  have hfn : fn u =ᵐ[volume.restrict (Ioo a b)] rep u := fn_ae_eq_rep hI u
  rw [eLpNorm_congr_ae hfn]
  have h := eLpNorm_le_of_ae_bound (μ := volume.restrict (Ioo a b)) (p := q) (f := rep u)
    (C := 2⁻¹ * ((b - a) ^ (1 - p.toReal⁻¹) * ‖deriv u 1‖))
    (((continuousOn_rep hI u).mono hcl).mono Ioo_subset_Icc_self
      |>.aestronglyMeasurable measurableSet_Ioo)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ by
      rw [Real.norm_eq_abs]
      exact abs_rep_le_half_eLpNorm_deriv hab hu (Ioo_subset_Icc_self hx)))
  rwa [Measure.restrict_apply_univ, Real.volume_Ioo] at h

end SobolevIntervalLpZero

/-! ### Test functions as elements of `W^{1,p}(I)` -/

namespace TestFunction

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

/-- A test function on `I` has its classical derivative as weak derivative on `I`. -/
theorem hasWeakDerivOn (φ : 𝓓(I, ℝ)) : HasWeakDerivOn φ (deriv φ) I :=
  hasWeakDerivOn_of_contDiffOn (φ.contDiff.of_le (by simp)).contDiffOn

variable (p) in
/-- The element of `W^{1,p}(I)` carried by a test function on `I`: the pair of the function and
its derivative, in `L^p(I)`. -/
def toSobolevIntervalLp (φ : 𝓓(I, ℝ)) : SobolevIntervalLp 1 p I :=
  SobolevIntervalLp.mk ![(φ.memLp' p).toLp φ, (φ.memLp_deriv p).toLp (deriv φ)] fun j ↦ by
    fin_cases j
    · exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
        ((Lp.memLp _).locallyIntegrableOn (Ω := I) Fact.out)
    · exact φ.hasWeakDerivOn.congr_ae (φ.memLp' p).coeFn_toLp.symm
        (φ.memLp_deriv p).coeFn_toLp.symm

/-- The function of the element of `W^{1,p}(I)` carried by a test function. -/
theorem fn_toSobolevIntervalLp_ae_eq (φ : 𝓓(I, ℝ)) :
    SobolevIntervalLp.fn (toSobolevIntervalLp p φ) =ᵐ[volume.restrict I] φ :=
  (φ.memLp' p).coeFn_toLp

/-- The derivative of the element of `W^{1,p}(I)` carried by a test function. -/
theorem coeFn_deriv_toSobolevIntervalLp_one (φ : 𝓓(I, ℝ)) :
    ⇑(SobolevIntervalLp.deriv (toSobolevIntervalLp p φ) 1) =ᵐ[volume.restrict I] deriv φ :=
  (φ.memLp_deriv p).coeFn_toLp

/-- The element of `W^{1,p}(I)` carried by a test function lies in the image of the test
functions. -/
theorem toSobolevIntervalLp_mem_testFunctions (φ : 𝓓(I, ℝ)) :
    toSobolevIntervalLp p φ
      ∈ SobolevMultiIndex.testFunctions ℝ (Module.Basis.singleton Unit ℝ) 1 p I volume :=
  ⟨φ, fn_toSobolevIntervalLp_ae_eq φ⟩

/-- The element of `W^{1,p}(I)` carried by a test function lies in `W_0^{1,p}(I)`. -/
theorem toSobolevIntervalLp_mem (φ : 𝓓(I, ℝ)) :
    toSobolevIntervalLp p φ ∈ SobolevIntervalLpZero 1 p I :=
  SobolevMultiIndexZero.testFunctions_le (toSobolevIntervalLp_mem_testFunctions φ)

end TestFunction

/-! ### Theorem 8.12, converse, on a bounded interval -/

section Holder

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {a b : ℝ}

/-- **Hölder's inequality** for the integral over `(a, b)`, in `ℝ≥0∞` and without any hypothesis
on `w`: `|∫_a^b w| ≤ (b - a)^{1 - 1/p} ‖w‖_{L^p(a, b)}`. -/
theorem MeasureTheory.enorm_setIntegral_Ioo_le_rpow_mul_eLpNorm (w : ℝ → ℝ) :
    ‖∫ x in Ioo a b, w x‖ₑ
      ≤ ENNReal.ofReal (b - a) ^ (1 - p.toReal⁻¹) * eLpNorm w p (volume.restrict (Ioo a b)) := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have := setLIntegral_enorm_le_rpow_mul_eLpNorm (p := p) (μ := volume.restrict (Ioo a b)) w
    MeasurableSet.univ
  rwa [Measure.restrict_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo] at this

end Holder

namespace SobolevIntervalLpZero

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {a b : ℝ}

open SobolevIntervalLp

/-- **Theorem 8.12 of [brezis2011functional], converse, on a bounded interval**: for `a < b`,
`1 ≤ p < ∞` and `u ∈ W^{1,p}(a, b)` whose continuous representative vanishes at `a` and at `b`,
`u ∈ W_0^{1,p}(a, b)`.

The derivative `u'` has zero mean on `(a, b)`, since `ũ(b) - ũ(a) = ∫_a^b u'`. Approximate `u'` in
`L^p(a, b)` by a test function `ψ` (`MeasureTheory.MemLp.exists_contDiff_tsupport_subset`),
correct its mean by a multiple of a fixed test function of integral one (Hölder controls the
correction), and take the primitive `φ = ∫_a^x ψ'` of the corrected function, which is again a
test function (`TestFunction.primitiveIic`). Then `ũ - φ = ∫_a^x (u' - ψ')` and Poincaré's
inequality (`SobolevIntervalLp.eLpNorm_integral_le`) bounds `‖u - φ‖_{W^{1,p}}` by a multiple of
`‖u' - ψ'‖_p`. No cut-off or mollification of `u` itself is needed (the book truncates `u`
by `G(nu)/n` instead). -/
theorem mem_of_rep_frontier_eq_zero_of_bounded (hab : a < b) (hp : p ≠ ⊤)
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) (ha : rep u a = 0) (hb : rep u b = 0) :
    u ∈ SobolevIntervalLpZero 1 p (Opens.Ioo a b) := by
  have hI := ordConnected_coe_Ioo a b
  have hcl : Icc a b ⊆ closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) := by rw [closure_coe_Ioo hab]
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  -- `u'` has zero mean on `(a, b)`
  have hwint : ∫ x in Ioo a b, deriv u 1 x = 0 := by
    have := rep_sub_rep hI u (hcl (left_mem_Icc.2 hab.le)) (hcl (right_mem_Icc.2 hab.le))
    rw [ha, hb, sub_zero, intervalIntegral.integral_of_le hab.le,
      integral_Ioc_eq_integral_Ioo] at this
    exact this.symm
  obtain ⟨ψ₀, hψ₀⟩ := (Opens.Ioo a b).exists_testFunction_integral_eq_one (nonempty_Ioo.2 hab)
  -- the constants
  obtain ⟨E, hE⟩ : ∃ E, E = (b - a) ^ (1 - p.toReal⁻¹) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := hE ▸ Real.rpow_nonneg (sub_pos.2 hab).le _
  obtain ⟨N, hN⟩ : ∃ N, N = (eLpNorm ψ₀ p (volume.restrict (Ioo a b))).toReal := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := hN ▸ ENNReal.toReal_nonneg
  obtain ⟨CP, hCP⟩ : ∃ CP, CP = (b - a) / p.toReal ^ p.toReal⁻¹ := ⟨_, rfl⟩
  have hCP0 : 0 ≤ CP := hCP ▸ poincareConst_nonneg hab.le
  obtain ⟨M, hM⟩ : ∃ M, M = (CP + 1) * (1 + E * N) := ⟨_, rfl⟩
  have hM0 : 0 < M := hM ▸ by positivity
  rw [← SetLike.mem_coe, SobolevIntervalLpZero, SobolevMultiIndexZero,
    Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨η, hη⟩ : ∃ η, η = ε / (2 * M) := ⟨_, rfl⟩
  have hη0 : 0 < η := hη ▸ by positivity
  -- approximate `u'` in `L^p(a, b)` by a test function
  obtain ⟨g, hgc, hg, hgs, hψ⟩ := (memLp_deriv u 1).exists_contDiff_tsupport_subset
    (Opens.Ioo a b).isOpen hp1 hp hη0
  obtain ⟨ψ, hψc⟩ : ∃ ψ : 𝓓(Opens.Ioo a b, ℝ), (ψ : ℝ → ℝ) = g := ⟨⟨g, hg, hgc, hgs⟩, rfl⟩
  rw [← hψc] at hψ
  -- correct the mean of `ψ`
  obtain ⟨m, hm⟩ : ∃ m, m = ∫ x, ψ x := ⟨_, rfl⟩
  obtain ⟨ψ', hψ'c, hmean⟩ : ∃ ψ' : 𝓓(Opens.Ioo a b, ℝ),
      ((ψ' : ℝ → ℝ) = fun x ↦ ψ x - m * ψ₀ x) ∧ ∫ x, ψ' x = 0 := by
    refine ⟨ψ - m • ψ₀, ?_, ?_⟩
    · funext x; simp [smul_eq_mul]
    · simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_sub ψ.integrable_volume (ψ₀.integrable_volume.const_mul m), integral_const_mul,
        hψ₀, mul_one, hm, sub_self]
  -- the primitive of `ψ'` is a test function
  obtain ⟨φ, hφc, hφ'⟩ : ∃ φ : 𝓓(Opens.Ioo a b, ℝ),
      (∀ x ∈ Icc a b, (φ : ℝ → ℝ) x = ∫ t in a..x, ψ' t) ∧ deriv (φ : ℝ → ℝ) = ψ' := by
    refine ⟨TestFunction.primitiveIic hI ψ' hmean, fun x hx ↦ ?_,
      TestFunction.deriv_primitiveIic hI ψ' hmean⟩
    rw [TestFunction.primitiveIic_coe, ← intervalIntegral.integral_Iic_sub_Iic
      ψ'.integrable_volume.integrableOn ψ'.integrable_volume.integrableOn,
      setIntegral_eq_zero_of_forall_eq_zero fun t (ht : t ∈ Iic a) ↦ ψ'.eq_zero_of_notMem
        fun h ↦ ((show t ∈ Ioo a b from h).1.trans_le ht).false, sub_zero]
  refine ⟨TestFunction.toSobolevIntervalLp p φ, φ.toSobolevIntervalLp_mem_testFunctions, ?_⟩
  have hv0 : fn (TestFunction.toSobolevIntervalLp p φ) =ᵐ[volume.restrict (Ioo a b)] φ :=
    φ.fn_toSobolevIntervalLp_ae_eq
  have hv1 : ⇑(deriv (TestFunction.toSobolevIntervalLp p φ) 1) =ᵐ[volume.restrict (Ioo a b)] ψ' :=
    by rw [← hφ']; exact φ.coeFn_deriv_toSobolevIntervalLp_one
  -- the mean correction is small, by Hölder
  have hm' : ‖m‖ₑ ≤ ENNReal.ofReal (E * η) := by
    have e1 : m = -∫ x in Ioo a b, (deriv u 1 x - ψ x) := by
      rw [integral_sub (integrableOn_deriv_Ioo u 1) ψ.integrable_volume.integrableOn, hwint,
        zero_sub, neg_neg, hm]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
        ψ.eq_zero_of_notMem hx).symm
    rw [e1, enorm_neg]
    refine (enorm_setIntegral_Ioo_le_rpow_mul_eLpNorm (p := p) _).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (sub_pos.2 hab).le (one_sub_toReal_inv_nonneg hp1), ← hE,
      ENNReal.ofReal_mul hE0]
    exact mul_le_mul' le_rfl hψ
  -- the `L^p` distance of the derivatives
  have hA : eLpNorm (fun t ↦ deriv u 1 t - ψ' t) p (volume.restrict (Ioo a b))
      ≤ ENNReal.ofReal (η * (1 + E * N)) := by
    have e : (fun t ↦ deriv u 1 t - ψ' t)
        = (fun t ↦ deriv u 1 t - ψ t) + m • (ψ₀ : ℝ → ℝ) := by
      funext t
      simp only [hψ'c, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    refine (eLpNorm_add_le hp1).trans ?_
    rw [eLpNorm_const_smul, mul_add, mul_one, ENNReal.ofReal_add hη0.le (by positivity)]
    refine add_le_add hψ ?_
    calc ‖m‖ₑ * eLpNorm ψ₀ p (volume.restrict (Ioo a b))
        ≤ ENNReal.ofReal (E * η) * ENNReal.ofReal N := by
          gcongr
          rw [hN]
          exact (ENNReal.ofReal_toReal (ψ₀.memLp' p).eLpNorm_ne_top).symm.le
      _ = ENNReal.ofReal (η * (E * N)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hAne : eLpNorm (fun t ↦ deriv u 1 t - ψ' t) p (volume.restrict (Ioo a b)) ≠ ⊤ :=
    (hA.trans_lt ENNReal.ofReal_lt_top).ne
  have hAr : (eLpNorm (fun t ↦ deriv u 1 t - ψ' t) p (volume.restrict (Ioo a b))).toReal
      ≤ η * (1 + E * N) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hA
  -- the two components of `u - v`
  have h1 : ‖deriv (u - TestFunction.toSobolevIntervalLp p φ) 1‖
      = (eLpNorm (fun t ↦ deriv u 1 t - ψ' t) p (volume.restrict (Ioo a b))).toReal := by
    rw [Lp.norm_def, SobolevIntervalLp.deriv_sub]
    congr 1
    refine eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans ?_)
    filter_upwards [hv1] with t ht
    rw [Pi.sub_apply, ht]
  have hderiv0 : ⇑(deriv (u - TestFunction.toSobolevIntervalLp p φ) 0)
      =ᵐ[volume.restrict (Ioo a b)] fun x ↦ ∫ t in a..x, (deriv u 1 t - ψ' t) := by
    rw [SobolevIntervalLp.deriv_sub]
    filter_upwards [Lp.coeFn_sub (deriv u 0) (deriv (TestFunction.toSobolevIntervalLp p φ) 0),
      fn_ae_eq_rep hI u, hv0, ae_restrict_mem measurableSet_Ioo] with x hx1 hx2 hx3 hx4
    rw [hx1, Pi.sub_apply, deriv_zero, hx2, deriv_zero, hx3,
      rep_eq_integral_of_rep_left_eq_zero hab u ha (Ioo_subset_Icc_self hx4),
      hφc x (Ioo_subset_Icc_self hx4), ← intervalIntegral.integral_sub
        (intervalIntegrable_deriv hI u 1 (hcl (left_mem_Icc.2 hab.le))
          (hcl (Ioo_subset_Icc_self hx4))) (ψ'.continuous.intervalIntegrable _ _)]
  have h0 : ‖deriv (u - TestFunction.toSobolevIntervalLp p φ) 0‖
      ≤ CP * (eLpNorm (fun t ↦ deriv u 1 t - ψ' t) p (volume.restrict (Ioo a b))).toReal := by
    rw [Lp.norm_def, ← ENNReal.toReal_ofReal hCP0, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAne) ?_
    refine (eLpNorm_congr_ae hderiv0).trans_le ?_
    rw [hCP]
    exact eLpNorm_integral_le hab.le
      ((integrableOn_deriv_Ioo u 1).sub ψ'.integrable_volume.integrableOn)
  -- assembling
  rw [dist_eq_norm]
  calc ‖u - TestFunction.toSobolevIntervalLp p φ‖
      ≤ ‖deriv (u - TestFunction.toSobolevIntervalLp p φ) 0‖
        + ‖deriv (u - TestFunction.toSobolevIntervalLp p φ) 1‖ := by
        have := norm_le_sum_norm_deriv (u - TestFunction.toSobolevIntervalLp p φ)
        rwa [Fin.sum_univ_two] at this
    _ ≤ CP * (eLpNorm (fun t ↦ deriv u 1 t - ψ' t) p (volume.restrict (Ioo a b))).toReal
        + (eLpNorm (fun t ↦ deriv u 1 t - ψ' t) p (volume.restrict (Ioo a b))).toReal :=
        add_le_add h0 h1.le
    _ = (CP + 1) * (eLpNorm (fun t ↦ deriv u 1 t - ψ' t) p (volume.restrict (Ioo a b))).toReal :=
        by ring
    _ ≤ (CP + 1) * (η * (1 + E * N)) := by gcongr
    _ = M * η := by rw [hM]; ring
    _ = ε / 2 := by
        rw [hη, ← mul_div_assoc, mul_comm M ε, mul_div_mul_right _ _ hM0.ne']
    _ < ε := half_lt_self hε

end SobolevIntervalLpZero

/-! ### `C^1` functions as elements of `W^{1,p}(I)` -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

/-- The element of `W^{1,p}(I)` carried by a `C^1` function on `I` lying, with its derivative, in
`L^p(I)`. -/
def ofContDiffOn {g : ℝ → ℝ} (hg : ContDiffOn ℝ 1 g I) (hgp : MemLp g p (volume.restrict I))
    (hgp' : MemLp (_root_.deriv g) p (volume.restrict I)) : SobolevIntervalLp 1 p I :=
  mk ![hgp.toLp g, hgp'.toLp (_root_.deriv g)] fun j ↦ by
    fin_cases j
    · exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
        ((Lp.memLp _).locallyIntegrableOn (Ω := I) Fact.out)
    · exact (hasWeakDerivOn_of_contDiffOn hg).congr_ae hgp.coeFn_toLp.symm hgp'.coeFn_toLp.symm

/-- The function of `SobolevIntervalLp.ofContDiffOn`. -/
theorem fn_ofContDiffOn_ae_eq {g : ℝ → ℝ} (hg : ContDiffOn ℝ 1 g I)
    (hgp : MemLp g p (volume.restrict I)) (hgp' : MemLp (_root_.deriv g) p (volume.restrict I)) :
    fn (ofContDiffOn hg hgp hgp') =ᵐ[volume.restrict I] g :=
  hgp.coeFn_toLp

/-- The weak derivative of `SobolevIntervalLp.ofContDiffOn` is the classical derivative. -/
theorem coeFn_deriv_ofContDiffOn_one {g : ℝ → ℝ} (hg : ContDiffOn ℝ 1 g I)
    (hgp : MemLp g p (volume.restrict I)) (hgp' : MemLp (_root_.deriv g) p (volume.restrict I)) :
    ⇑(deriv (ofContDiffOn hg hgp hgp') 1) =ᵐ[volume.restrict I] _root_.deriv g :=
  hgp'.coeFn_toLp

/-- The continuous representative of `SobolevIntervalLp.ofContDiffOn` is the function itself,
on the closure of `I`, when that function is continuous there. -/
theorem rep_ofContDiffOn (hI : (I : Set ℝ).OrdConnected) {g : ℝ → ℝ} (hg : ContDiffOn ℝ 1 g I)
    (hgp : MemLp g p (volume.restrict I)) (hgp' : MemLp (_root_.deriv g) p (volume.restrict I))
    (hgc : ContinuousOn g (closure (I : Set ℝ))) :
    EqOn (rep (ofContDiffOn hg hgp hgp')) g (closure (I : Set ℝ)) :=
  rep_eq_of_continuousOn hI _ hgc (fn_ofContDiffOn_ae_eq hg hgp hgp')

end SobolevIntervalLp

/-! ### The cut-off sequence of Theorem 8.7 -/

namespace SobolevIntervalLp

/-- The model cut-off: a smooth bump equal to `1` on `[-1, 1]` and to `0` off `(-2, 2)`. -/
def cutoffBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cut-off `ζ_n(x) = ζ(x / (n + 1))`: a smooth function with `0 ≤ ζ_n ≤ 1`, equal to `1` on
`[-(n + 1), n + 1]` and to `0` off `(-2(n + 1), 2(n + 1))`. -/
def cutoffFn (n : ℕ) (x : ℝ) : ℝ := cutoffBump (x / ((n : ℝ) + 1))

/-- `ζ_n = 1` on `[-(n + 1), n + 1]`. -/
theorem cutoffFn_of_abs_le {n : ℕ} {x : ℝ} (hx : |x| ≤ (n : ℝ) + 1) : cutoffFn n x = 1 := by
  refine cutoffBump.one_of_mem_closedBall ?_
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  exact div_le_one_of_le₀ hx (by positivity)

/-- `ζ_n = 0` off `(-2(n + 1), 2(n + 1))`. -/
theorem cutoffFn_of_le_abs {n : ℕ} {x : ℝ} (hx : 2 * ((n : ℝ) + 1) ≤ |x|) : cutoffFn n x = 0 := by
  refine cutoffBump.zero_of_le_dist ?_
  rw [dist_zero_right, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  change (2 : ℝ) ≤ |x| / ((n : ℝ) + 1)
  rw [le_div_iff₀ (by positivity)]
  exact hx

/-- `0 ≤ ζ_n`. -/
theorem cutoffFn_nonneg (n : ℕ) (x : ℝ) : 0 ≤ cutoffFn n x := cutoffBump.nonneg

/-- `ζ_n ≤ 1`. -/
theorem cutoffFn_le_one (n : ℕ) (x : ℝ) : cutoffFn n x ≤ 1 := cutoffBump.le_one

/-- `ζ_n` is smooth. -/
theorem contDiff_cutoffFn (n : ℕ) : ContDiff ℝ ∞ (cutoffFn n) :=
  cutoffBump.contDiff.comp (contDiff_id.div_const _)

/-- `ζ_n` has compact support. -/
theorem hasCompactSupport_cutoffFn (n : ℕ) : HasCompactSupport (cutoffFn n) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := -(2 * ((n : ℝ) + 1))) (b := 2 * ((n : ℝ) + 1))) fun x hx ↦ by
    rw [Function.mem_support] at hx
    by_contra h
    refine hx (cutoffFn_of_le_abs ?_)
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

/-- The derivatives of the cut-offs are bounded by `C / (n + 1)`, `C = sup |ζ'|`. -/
theorem exists_abs_deriv_cutoffFn_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ), |_root_.deriv (cutoffFn n) x| ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C, hC⟩ := cutoffBump.hasCompactSupport.deriv.exists_bound_of_continuous
    ((cutoffBump.contDiff (n := ⊤)).continuous_deriv (by simp))
  refine ⟨C, (norm_nonneg _).trans (hC 0), fun n x ↦ ?_⟩
  have h1 : HasDerivAt (fun y : ℝ ↦ y / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) x :=
    (hasDerivAt_id x).div_const _
  have h2 : HasDerivAt cutoffBump (_root_.deriv cutoffBump (x / ((n : ℝ) + 1)))
      (x / ((n : ℝ) + 1)) :=
    ((cutoffBump.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have hd : HasDerivAt (cutoffFn n)
      (_root_.deriv cutoffBump (x / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)))
      x := h2.comp x h1
  rw [hd.deriv, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)),
    div_eq_mul_one_div C]
  gcongr
  exact (Real.norm_eq_abs _) ▸ hC _

variable {p : ℝ≥0∞} {I : Opens ℝ}

/-- `ζ_n ∈ L^p(I)` for every `I`. -/
theorem memLp_cutoffFn (n : ℕ) : MemLp (cutoffFn n) p (volume.restrict I) :=
  (contDiff_cutoffFn n).continuous.memLp_of_hasCompactSupport (hasCompactSupport_cutoffFn n)

/-- `ζ_n' ∈ L^p(I)` for every `I`. -/
theorem memLp_deriv_cutoffFn (n : ℕ) : MemLp (_root_.deriv (cutoffFn n)) p (volume.restrict I) :=
  ((contDiff_cutoffFn n).continuous_deriv (by simp)).memLp_of_hasCompactSupport
    (hasCompactSupport_cutoffFn n).deriv

variable [Fact (1 ≤ p)]

variable (p I) in
/-- The cut-off `ζ_n` as an element of `W^{1,p}(I)`. -/
def cutoffElem (n : ℕ) : SobolevIntervalLp 1 p I :=
  ofContDiffOn ((contDiff_cutoffFn n).of_le (by simp)).contDiffOn (memLp_cutoffFn n)
    (memLp_deriv_cutoffFn n)

/-- The continuous representative of the cut-off element is `ζ_n`. -/
theorem rep_cutoffElem (hI : (I : Set ℝ).OrdConnected) (n : ℕ) :
    EqOn (rep (cutoffElem p I n)) (cutoffFn n) (closure (I : Set ℝ)) :=
  rep_ofContDiffOn hI _ _ _ (contDiff_cutoffFn n).continuous.continuousOn

/-- **The cut-off sequence of the proof of Theorem 8.7 (b) of [brezis2011functional]**: the
element `ζ_n u` of `W^{1,p}(I)`, with function `ζ_n ũ` and weak derivative `ζ_n' ũ + ζ_n u'`. -/
def cutoff (hI : (I : Set ℝ).OrdConnected) (n : ℕ) (u : SobolevIntervalLp 1 p I) :
    SobolevIntervalLp 1 p I :=
  mul hI (cutoffElem p I n) u

/-- The continuous representative of `ζ_n u` is `ζ_n ũ` on the closure of `I`. -/
theorem rep_cutoff (hI : (I : Set ℝ).OrdConnected) (n : ℕ) (u : SobolevIntervalLp 1 p I) :
    EqOn (rep (cutoff hI n u)) (fun x ↦ cutoffFn n x * rep u x) (closure (I : Set ℝ)) :=
  fun x hx ↦ by
    rw [cutoff, rep_mul hI _ _ hx]
    beta_reduce
    rw [rep_cutoffElem hI n hx]

/-- The function of `ζ_n u` is `ζ_n ũ`. -/
theorem fn_cutoff (hI : (I : Set ℝ).OrdConnected) (n : ℕ) (u : SobolevIntervalLp 1 p I) :
    fn (cutoff hI n u) =ᵐ[volume.restrict I] fun x ↦ cutoffFn n x * rep u x :=
  (fn_mul hI _ u).trans (by
    filter_upwards [ae_restrict_mem I.isOpen.measurableSet] with x hx
    rw [rep_cutoffElem hI n (subset_closure hx)])

/-- The weak derivative of `ζ_n u` is `ζ_n' ũ + ζ_n u'`. -/
theorem coeFn_deriv_cutoff_one (hI : (I : Set ℝ).OrdConnected) (n : ℕ)
    (u : SobolevIntervalLp 1 p I) :
    ⇑(deriv (cutoff hI n u) 1) =ᵐ[volume.restrict I]
      fun x ↦ _root_.deriv (cutoffFn n) x * rep u x + cutoffFn n x * deriv u 1 x :=
  (coeFn_deriv_mul hI _ u).trans (by
    filter_upwards [ae_restrict_mem I.isOpen.measurableSet,
      coeFn_deriv_ofContDiffOn_one ((contDiff_cutoffFn n).of_le (by simp)).contDiffOn
        (memLp_cutoffFn (p := p) n) (memLp_deriv_cutoffFn n)] with x hx hx'
    rw [rep_cutoffElem hI n (subset_closure hx)]
    exact congrArg (· + _) (congrArg (· * _) hx'))

end SobolevIntervalLp

section Tail

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The `L^p` norm of `f ∈ L^p(μ)`, `p < ∞`, off `[-r, r]` tends to `0` as `r → ∞`. -/
theorem MeasureTheory.tendsto_eLpNorm_restrict_compl_Icc_atTop {μ : Measure ℝ} {f : ℝ → ℝ}
    (hp : p ≠ ⊤) (hf : MemLp f p μ) :
    Tendsto (fun r ↦ eLpNorm f p (μ.restrict (Icc (-r) r)ᶜ)) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hint : Integrable (fun x ↦ ‖f x‖ ^ p.toReal) μ := hf.integrable_norm_rpow hp0 hp
  have h1 : Tendsto (fun r ↦ ∫ t in (Icc (-r) r)ᶜ, ‖f t‖ ^ p.toReal ∂μ) atTop
      (𝓝 (∫ t in ⋂ r : ℝ, (Icc (-r) r)ᶜ, ‖f t‖ ^ p.toReal ∂μ)) :=
    tendsto_setIntegral_of_antitone (fun _ ↦ measurableSet_Icc.compl)
      (fun _ _ hxy ↦ compl_subset_compl.2 (Icc_subset_Icc (neg_le_neg hxy) hxy))
      ⟨0, hint.integrableOn⟩
  have hempty : ⋂ r : ℝ, (Icc (-r) r)ᶜ = ∅ :=
    eq_empty_iff_forall_notMem.2 fun y hy ↦
      (mem_iInter.1 hy |y|) ⟨neg_abs_le y, le_abs_self y⟩
  rw [hempty, Measure.restrict_empty, integral_zero_measure] at h1
  have h2 : ∀ r, eLpNorm f p (μ.restrict (Icc (-r) r)ᶜ)
      = ENNReal.ofReal ((∫ t in (Icc (-r) r)ᶜ, ‖f t‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹) := fun r ↦
    (hf.restrict _).eLpNorm_eq_integral_rpow_norm hp0 hp
  simp_rw [h2]
  have h3 : Tendsto (fun r ↦ (∫ t in (Icc (-r) r)ᶜ, ‖f t‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹) atTop
      (𝓝 0) := by
    have := h1.rpow_const (p := p.toReal⁻¹) (Or.inr (inv_nonneg.2 hpr.le))
    rwa [Real.zero_rpow (inv_ne_zero hpr.ne')] at this
  simpa using ENNReal.tendsto_ofReal h3

end Tail

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

/-- **The cut-offs converge** ([brezis2011functional], proof of Theorem 8.7 (b)): for
`u ∈ W^{1,p}(I)`, `1 ≤ p < ∞`, `ζ_n u → u` in `W^{1,p}(I)`. Indeed `ζ_n u - u = (ζ_n - 1) ũ`
vanishes on `[-(n+1), n+1]` and is bounded by `|ũ|`, so its `L^p` norm is at most the norm of
`ũ` off `[-(n+1), n+1]`, which tends to `0`; likewise for `(ζ_n - 1) u'`, and
`‖ζ_n' ũ‖_p ≤ (C / (n + 1)) ‖ũ‖_p → 0`. -/
theorem tendsto_cutoff_smul (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ⊤)
    (u : SobolevIntervalLp 1 p I) : Tendsto (fun n ↦ cutoff hI n u) atTop (𝓝 u) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_deriv_cutoffFn_le
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hR : eLpNorm (rep u) p (volume.restrict I) ≠ ⊤ := (memLp_rep hI u).eLpNorm_ne_top
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  -- the three vanishing terms
  have hT0 : Tendsto (fun n : ℕ ↦ eLpNorm (rep u) p
      ((volume.restrict I).restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))ᶜ)) atTop (𝓝 0) :=
    (tendsto_eLpNorm_restrict_compl_Icc_atTop hp (memLp_rep hI u)).comp hnat
  have hT1 : Tendsto (fun n : ℕ ↦ eLpNorm (deriv u 1) p
      ((volume.restrict I).restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))ᶜ)) atTop (𝓝 0) :=
    (tendsto_eLpNorm_restrict_compl_Icc_atTop hp (Lp.memLp (deriv u 1))).comp hnat
  have hC' : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (C / ((n : ℝ) + 1))
      * eLpNorm (rep u) p (volume.restrict I)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop hnat (a := C))
    rw [ENNReal.ofReal_zero] at h
    simpa using ENNReal.Tendsto.mul_const h (Or.inr hR)
  have hS : Tendsto (fun n : ℕ ↦ (eLpNorm (rep u) p
      ((volume.restrict I).restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))ᶜ)
      + (ENNReal.ofReal (C / ((n : ℝ) + 1)) * eLpNorm (rep u) p (volume.restrict I)
        + eLpNorm (deriv u 1) p
          ((volume.restrict I).restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))ᶜ))).toReal)
      atTop (𝓝 0) := by
    have h1 := hT0.add (hC'.add hT1)
    rw [add_zero, add_zero] at h1
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    rw [ENNReal.toReal_zero] at h
    exact h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hS
  have hfin0 : eLpNorm (rep u) p
      ((volume.restrict I).restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))ᶜ) ≠ ⊤ :=
    ((memLp_rep hI u).restrict _).eLpNorm_ne_top
  have hfin1 : eLpNorm (deriv u 1) p
      ((volume.restrict I).restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))ᶜ) ≠ ⊤ :=
    ((Lp.memLp _).restrict _).eLpNorm_ne_top
  have hfin : ENNReal.ofReal (C / ((n : ℝ) + 1)) * eLpNorm (rep u) p (volume.restrict I)
      + eLpNorm (deriv u 1) p
        ((volume.restrict I).restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))ᶜ) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hR, hfin1⟩
  -- the pointwise bound `|(ζ_n - 1) g| ≤ |1_{[-(n+1), n+1]ᶜ} g|`
  have hpt : ∀ g : ℝ → ℝ, ∀ x, ‖(cutoffFn n x - 1) * g x‖
      ≤ ‖(Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))ᶜ.indicator g x‖ := fun g x ↦ by
    by_cases hx : x ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
    · rw [cutoffFn_of_abs_le (abs_le.2 hx), sub_self, zero_mul, norm_zero]
      exact norm_nonneg _
    · rw [indicator_of_mem (mem_compl hx), Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (abs_le.2 ⟨by linarith [cutoffFn_nonneg n x], by linarith [cutoffFn_le_one n x]⟩)
  -- the function component
  have hD0 : eLpNorm ⇑(deriv (cutoff hI n u - u) 0) p (volume.restrict I)
      ≤ eLpNorm (rep u) p
        ((volume.restrict I).restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))ᶜ) := by
    have e : ⇑(deriv (cutoff hI n u - u) 0) =ᵐ[volume.restrict I]
        fun x ↦ (cutoffFn n x - 1) * rep u x := by
      rw [deriv_sub]
      filter_upwards [Lp.coeFn_sub (deriv (cutoff hI n u) 0) (deriv u 0), fn_cutoff hI n u,
        fn_ae_eq_rep hI u] with x hx1 hx2 hx3
      rw [hx1, Pi.sub_apply, deriv_zero, hx2, deriv_zero, hx3]
      ring
    rw [eLpNorm_congr_ae e, ← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc.compl]
    exact eLpNorm_mono_ae (((contDiff_cutoffFn n).continuous.sub continuous_const)
      |>.aestronglyMeasurable.mul (memLp_rep hI u).aestronglyMeasurable)
      (Eventually.of_forall (hpt _))
  -- the derivative component
  have hD1 : eLpNorm ⇑(deriv (cutoff hI n u - u) 1) p (volume.restrict I)
      ≤ ENNReal.ofReal (C / ((n : ℝ) + 1)) * eLpNorm (rep u) p (volume.restrict I)
        + eLpNorm (deriv u 1) p
          ((volume.restrict I).restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))ᶜ) := by
    have e : ⇑(deriv (cutoff hI n u - u) 1) =ᵐ[volume.restrict I]
        (fun x ↦ _root_.deriv (cutoffFn n) x * rep u x)
          + fun x ↦ (cutoffFn n x - 1) * deriv u 1 x := by
      rw [deriv_sub]
      filter_upwards [Lp.coeFn_sub (deriv (cutoff hI n u) 1) (deriv u 1),
        coeFn_deriv_cutoff_one hI n u] with x hx1 hx2
      rw [hx1, Pi.sub_apply, hx2, Pi.add_apply]
      ring
    rw [eLpNorm_congr_ae e]
    refine (eLpNorm_add_le hp1).trans (add_le_add ?_ ?_)
    · calc eLpNorm (fun x ↦ _root_.deriv (cutoffFn n) x * rep u x) p (volume.restrict I)
          ≤ eLpNorm ((C / ((n : ℝ) + 1)) • rep u) p (volume.restrict I) := by
            refine eLpNorm_mono_ae (((contDiff_cutoffFn n).continuous_deriv (by simp))
              |>.aestronglyMeasurable.mul (memLp_rep hI u).aestronglyMeasurable)
              (Eventually.of_forall fun x ↦ ?_)
            rw [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ C / ((n : ℝ) + 1))]
            exact mul_le_mul_of_nonneg_right (hC n x) (abs_nonneg _)
        _ = ENNReal.ofReal (C / ((n : ℝ) + 1)) * eLpNorm (rep u) p (volume.restrict I) := by
            rw [eLpNorm_const_smul, Real.enorm_of_nonneg (by positivity)]
    · rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc.compl]
      exact eLpNorm_mono_ae (((contDiff_cutoffFn n).continuous.sub continuous_const)
        |>.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)) (Eventually.of_forall (hpt _))
  calc ‖cutoff hI n u - u‖
      ≤ ‖deriv (cutoff hI n u - u) 0‖ + ‖deriv (cutoff hI n u - u) 1‖ := by
        have := norm_le_sum_norm_deriv (cutoff hI n u - u)
        rwa [Fin.sum_univ_two] at this
    _ ≤ (eLpNorm (rep u) p
          ((volume.restrict I).restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))ᶜ)).toReal
        + (ENNReal.ofReal (C / ((n : ℝ) + 1)) * eLpNorm (rep u) p (volume.restrict I)
          + eLpNorm (deriv u 1) p
            ((volume.restrict I).restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))ᶜ)).toReal := by
        rw [Lp.norm_def, Lp.norm_def]
        exact add_le_add (ENNReal.toReal_mono hfin0 hD0) (ENNReal.toReal_mono hfin hD1)
    _ = _ := (ENNReal.toReal_add hfin0 hfin).symm

end SobolevIntervalLp

/-! ### Restriction to a subinterval, and uniqueness -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I J : Opens ℝ} [Fact (1 ≤ p)]

/-- The zero function has weak derivative zero. -/
theorem hasWeakDerivOn_zero (I : Opens ℝ) : HasWeakDerivOn (0 : ℝ → ℝ) 0 I := by
  have := hasWeakDerivOn_of_contDiffOn (I := I) (contDiffOn_const (c := (0 : ℝ)))
  rw [deriv_const'] at this
  exact this

omit [Fact (1 ≤ p)] in
/-- Two elements of `W^{1,p}(I)` with the same function are equal: the weak derivative is
unique. -/
theorem eq_of_fn_ae_eq {u v : SobolevIntervalLp 1 p I} (h : fn u =ᵐ[volume.restrict I] fn v) :
    u = v := by
  have h1 : ⇑(deriv u 1) =ᵐ[volume.restrict I] deriv v 1 := by
    have hw : HasWeakDerivOn (fn v) (deriv u 1) I :=
      (hasWeakDerivOn_fn u).congr_ae h EventuallyEq.rfl
    rw [Filter.EventuallyEq, ae_restrict_iff' I.isOpen.measurableSet]
    exact hw.ae_eq (hasWeakDerivOn_fn v)
  refine ext fun j ↦ ?_
  fin_cases j
  · exact Lp.ext h
  · exact Lp.ext h1

omit [Fact (1 ≤ p)] in
/-- An element of `W^{1,p}(I)` whose representative vanishes on the closure of `I` is zero. -/
theorem eq_zero_of_rep_eq_zero (hI : (I : Set ℝ).OrdConnected) {u : SobolevIntervalLp 1 p I}
    (h : ∀ x ∈ closure (I : Set ℝ), rep u x = 0) : u = 0 :=
  eq_of_fn_ae_eq ((fn_ae_eq_rep hI u).trans (by
    have h0 : fn (0 : SobolevIntervalLp 1 p I) =ᵐ[volume.restrict I] 0 := SobolevMultiIndex.fn_zero
    filter_upwards [ae_restrict_mem I.isOpen.measurableSet, h0] with x hx hx0
    rw [h x (subset_closure hx), hx0]
    rfl))

/-- The restriction of an `L^p(I)` function to an open set `J ⊆ I`. -/
def restrictLp (hJI : (J : Set ℝ) ⊆ I) (f : Lp ℝ p (volume.restrict (I : Set ℝ))) :
    Lp ℝ p (volume.restrict (J : Set ℝ)) :=
  ((Lp.memLp f).mono_measure (Measure.restrict_mono hJI le_rfl)).toLp f

omit [Fact (1 ≤ p)] in
/-- The restriction is the function, almost everywhere on `J`. -/
theorem coeFn_restrictLp (hJI : (J : Set ℝ) ⊆ I) (f : Lp ℝ p (volume.restrict (I : Set ℝ))) :
    ⇑(restrictLp hJI f) =ᵐ[volume.restrict J] f :=
  MemLp.coeFn_toLp _

/-- **Restriction** of `u ∈ W^{1,p}(I)` to an open set `J ⊆ I`: its function and weak derivative
restricted to `J`. -/
def restrict (hJI : (J : Set ℝ) ⊆ I) (u : SobolevIntervalLp 1 p I) : SobolevIntervalLp 1 p J :=
  mk ![restrictLp hJI (deriv u 0), restrictLp hJI (deriv u 1)] fun j ↦ by
    fin_cases j
    · exact HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
        ((Lp.memLp _).locallyIntegrableOn (Ω := J) Fact.out)
    · exact ((hasWeakDerivOn_fn u).mono hJI).congr_ae (coeFn_restrictLp hJI _).symm
        (coeFn_restrictLp hJI _).symm

/-- The function of the restriction. -/
theorem fn_restrict_ae_eq (hJI : (J : Set ℝ) ⊆ I) (u : SobolevIntervalLp 1 p I) :
    fn (restrict hJI u) =ᵐ[volume.restrict J] fn u :=
  coeFn_restrictLp hJI _

/-- The weak derivative of the restriction. -/
theorem coeFn_deriv_restrict_one (hJI : (J : Set ℝ) ⊆ I) (u : SobolevIntervalLp 1 p I) :
    ⇑(deriv (restrict hJI u) 1) =ᵐ[volume.restrict J] deriv u 1 :=
  coeFn_restrictLp hJI _

/-- The continuous representative of the restriction is the restriction of the continuous
representative. -/
theorem rep_restrict (hI : (I : Set ℝ).OrdConnected) (hJ : (J : Set ℝ).OrdConnected)
    (hJI : (J : Set ℝ) ⊆ I) (u : SobolevIntervalLp 1 p I) :
    EqOn (rep (restrict hJI u)) (rep u) (closure (J : Set ℝ)) :=
  rep_eq_of_continuousOn hJ _ ((continuousOn_rep hI u).mono (closure_mono hJI))
    ((fn_restrict_ae_eq hJI u).trans ((fn_ae_eq_rep hI u).filter_mono
      (ae_mono (Measure.restrict_mono hJI le_rfl))))

omit [Fact (1 ≤ p)] in
/-- The `L^p` norm over `t` of a function vanishing a.e. on `t \ s` is its `L^p` norm over
`s`. -/
theorem _root_.MeasureTheory.eLpNorm_restrict_eq_of_ae_eq_zero_off {μ : Measure ℝ} {f : ℝ → ℝ}
    {s t : Set ℝ} (hs : MeasurableSet s) (hst : s ⊆ t)
    (h : ∀ᵐ x ∂(μ.restrict t), x ∉ s → f x = 0) :
    eLpNorm f p (μ.restrict t) = eLpNorm f p (μ.restrict s) := by
  have e : f =ᵐ[μ.restrict t] s.indicator f := by
    filter_upwards [h] with x hx
    by_cases hxs : x ∈ s
    · rw [indicator_of_mem hxs]
    · rw [indicator_of_notMem hxs, hx hxs]
  rw [eLpNorm_congr_ae e, eLpNorm_indicator_eq_eLpNorm_restrict hs, Measure.restrict_restrict hs,
    inter_eq_left.2 hst]

end SobolevIntervalLp

/-! ### Theorem 8.12 on any interval -/

namespace SobolevIntervalLpZero

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

open SobolevIntervalLp

/-- **The restriction argument of Theorem 8.12**: an element `u ∈ W^{1,p}(I)`, `1 ≤ p < ∞`, whose
representative vanishes on `∂I` and off a bounded interval `(c, d)` lies in `W_0^{1,p}(I)`.
The set `J = I ∩ (c, d)` is a bounded interval `(a, b)` (or empty, and then `u = 0`); the
restriction of `u` to `J` vanishes at `a` and `b`, hence lies in `W_0^{1,p}(J)` by the bounded
case, so it is approximated by test functions on `J`, which are test functions on `I`; and the
`W^{1,p}(I)` distance from `u` to such a test function is at most twice the `W^{1,p}(J)` distance,
since `u` and `u'` vanish a.e. off `J`. -/
theorem mem_of_rep_eq_zero_off_Ioo (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ⊤)
    (u : SobolevIntervalLp 1 p I) {c d : ℝ} (hfr : ∀ x ∈ frontier (I : Set ℝ), rep u x = 0)
    (hoff : ∀ x ∈ closure (I : Set ℝ), x ∉ Ioo c d → rep u x = 0) :
    u ∈ SobolevIntervalLpZero 1 p I := by
  -- `ũ` vanishes on `closure I` off `K = I ∩ (c, d)`
  have hK : ∀ x ∈ closure (I : Set ℝ), x ∉ (I : Set ℝ) ∩ Ioo c d → rep u x = 0 :=
    fun x hx hxK ↦ by
    by_cases hxI : x ∈ (I : Set ℝ)
    · exact hoff x hx fun h ↦ hxK ⟨hxI, h⟩
    · exact hfr x (by rw [I.isOpen.frontier_eq]; exact ⟨hx, hxI⟩)
  have hKI : ((I ⊓ Opens.Ioo c d : Opens ℝ) : Set ℝ) = (I : Set ℝ) ∩ Ioo c d := rfl
  have hKord : ((I ⊓ Opens.Ioo c d : Opens ℝ) : Set ℝ).OrdConnected := by
    rw [hKI]; exact hI.inter ordConnected_Ioo
  rcases Opens.eq_intervals_of_ordConnected hKord with h | h | ⟨a, h⟩ | ⟨b, h⟩ | ⟨a, b, hab, h⟩
  · -- `K = ∅`: `u = 0`
    rw [hKI] at h
    rw [eq_zero_of_rep_eq_zero hI fun x hx ↦ hK x hx (by rw [h]; exact notMem_empty x)]
    exact zero_mem _
  · exfalso
    rw [hKI] at h
    have : max c d + 1 ∈ (I : Set ℝ) ∩ Ioo c d := by rw [h]; exact mem_univ _
    linarith [this.2.2, le_max_right c d]
  · exfalso
    rw [hKI] at h
    have : max a d + 1 ∈ (I : Set ℝ) ∩ Ioo c d := by
      rw [h]; exact show a < max a d + 1 by linarith [le_max_left a d]
    linarith [this.2.2, le_max_right a d]
  · exfalso
    rw [hKI] at h
    have : min b c - 1 ∈ (I : Set ℝ) ∩ Ioo c d := by
      rw [h]; exact show min b c - 1 < b by linarith [min_le_left b c]
    linarith [this.2.1, min_le_right b c]
  -- `K = (a, b)`, `a < b`
  rw [hKI] at h
  have hJI : ((Opens.Ioo a b : Opens ℝ) : Set ℝ) ⊆ I := by
    rw [Opens.coe_Ioo, ← h]; exact inter_subset_left
  have hJ := ordConnected_coe_Ioo a b
  have hcl : Icc a b ⊆ closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) := by rw [closure_coe_Ioo hab]
  have hclI : closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) ⊆ closure (I : Set ℝ) :=
    closure_mono hJI
  have hoff' : ∀ x ∈ closure (I : Set ℝ), x ∉ ((Opens.Ioo a b : Opens ℝ) : Set ℝ) → rep u x = 0 :=
    fun x hx hx' ↦ hK x hx (by rw [h]; exact hx')
  -- the restriction to `(a, b)` lies in `W_0^{1,p}(a, b)`
  have hrep := rep_restrict hI hJ hJI u
  have hv : restrict hJI u ∈ SobolevIntervalLpZero 1 p (Opens.Ioo a b) :=
    mem_of_rep_frontier_eq_zero_of_bounded hab hp _
      (by
        rw [hrep (hcl (left_mem_Icc.2 hab.le))]
        exact hoff' a (hclI (hcl (left_mem_Icc.2 hab.le))) fun h ↦ lt_irrefl a h.1)
      (by
        rw [hrep (hcl (right_mem_Icc.2 hab.le))]
        exact hoff' b (hclI (hcl (right_mem_Icc.2 hab.le))) fun h ↦ lt_irrefl b h.2)
  -- `u` and `u'` vanish a.e. off `(a, b)`
  have hfn0 : ∀ᵐ x ∂(volume.restrict I), x ∉ ((Opens.Ioo a b : Opens ℝ) : Set ℝ) → fn u x = 0 := by
    filter_upwards [fn_ae_eq_rep hI u, ae_restrict_mem I.isOpen.measurableSet] with x hx1 hx2 hx3
    rw [hx1]; exact hoff' x (subset_closure hx2) hx3
  have hderiv0 : ∀ᵐ x ∂(volume.restrict I), x ∉ ((Opens.Ioo a b : Opens ℝ) : Set ℝ) →
      deriv u 1 x = 0 := by
    -- on the open set `U = I \ [a, b]` the function vanishes a.e., hence so does its derivative
    obtain ⟨U, hU⟩ : ∃ U : Opens ℝ, U = ⟨(I : Set ℝ) \ Icc a b, I.isOpen.sdiff isClosed_Icc⟩ :=
      ⟨_, rfl⟩
    have hUc : (U : Set ℝ) = (I : Set ℝ) \ Icc a b := by rw [hU]; rfl
    have hUI : (U : Set ℝ) ⊆ I := by rw [hUc]; exact sdiff_subset
    have hU0 : fn u =ᵐ[volume.restrict U] 0 := by
      filter_upwards [(fn_ae_eq_rep hI u).filter_mono (ae_mono (Measure.restrict_mono hUI le_rfl)),
        ae_restrict_mem U.isOpen.measurableSet] with x hx1 hx2
      rw [hUc] at hx2
      rw [hx1]
      exact hoff' x (subset_closure hx2.1) fun h ↦ hx2.2 (Ioo_subset_Icc_self h)
    have hae := (((hasWeakDerivOn_fn u).mono hUI).congr_ae hU0 EventuallyEq.rfl).ae_eq
      (hasWeakDerivOn_zero U)
    have hab' : ∀ᵐ x ∂volume, x ∉ ({a, b} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.1 (((finite_singleton b).insert a).measure_zero volume)
    rw [ae_restrict_iff' I.isOpen.measurableSet]
    filter_upwards [hae, hab'] with x hx1 hx2 hxI hx3
    refine hx1 (by
      rw [hUc]
      refine ⟨hxI, fun hxab ↦ hx3 ⟨lt_of_le_of_ne hxab.1 fun e ↦ hx2 ?_,
        lt_of_le_of_ne hxab.2 fun e ↦ hx2 ?_⟩⟩
      · rw [← e]; exact mem_insert a _
      · rw [e]; exact mem_insert_of_mem a rfl)
  -- approximation: test functions on `(a, b)` are test functions on `I`
  rw [← SetLike.mem_coe, SobolevIntervalLpZero, SobolevMultiIndexZero,
    Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  rw [← SetLike.mem_coe, SobolevIntervalLpZero, SobolevMultiIndexZero,
    Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hv
  intro ε hε
  obtain ⟨w, ⟨φ, hφ⟩, hw⟩ := hv (ε / 2) (half_pos hε)
  have hwφ : w = TestFunction.toSobolevIntervalLp p φ :=
    eq_of_fn_ae_eq (hφ.trans φ.fn_toSobolevIntervalLp_ae_eq.symm)
  obtain ⟨φ', hφ'⟩ : ∃ φ' : 𝓓(I, ℝ), (φ' : ℝ → ℝ) = φ :=
    ⟨⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hJI⟩, rfl⟩
  refine ⟨TestFunction.toSobolevIntervalLp p φ', φ'.toSobolevIntervalLp_mem_testFunctions, ?_⟩
  -- the components of `u - φ'` on `I` agree with those of `v - w` on `(a, b)`
  have key : ∀ j : Fin 2, ‖deriv (u - TestFunction.toSobolevIntervalLp p φ') j‖
      ≤ ‖restrict hJI u - w‖ := by
    intro j
    refine le_trans ?_ (norm_deriv_le _ j)
    rw [Lp.norm_def, Lp.norm_def]
    refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (le_of_eq ?_)
    rw [hwφ]
    fin_cases j
    · have e1 : ⇑(deriv (u - TestFunction.toSobolevIntervalLp p φ') 0) =ᵐ[volume.restrict I]
          fun x ↦ fn u x - φ x := by
        rw [SobolevIntervalLp.deriv_sub]
        filter_upwards [Lp.coeFn_sub (deriv u 0) (deriv (TestFunction.toSobolevIntervalLp p φ') 0),
          φ'.fn_toSobolevIntervalLp_ae_eq (p := p)] with x hx1 hx2
        rw [hx1, Pi.sub_apply, SobolevIntervalLp.deriv_zero, SobolevIntervalLp.deriv_zero, hx2, hφ']
      have e2 : ⇑(deriv (restrict hJI u - TestFunction.toSobolevIntervalLp p φ) 0)
          =ᵐ[volume.restrict ((Opens.Ioo a b : Opens ℝ) : Set ℝ)] fun x ↦ fn u x - φ x := by
        rw [SobolevIntervalLp.deriv_sub]
        filter_upwards [Lp.coeFn_sub (deriv (restrict hJI u) 0)
          (deriv (TestFunction.toSobolevIntervalLp p φ) 0), fn_restrict_ae_eq hJI u,
          φ.fn_toSobolevIntervalLp_ae_eq (p := p)] with x hx1 hx2 hx3
        rw [hx1, Pi.sub_apply, SobolevIntervalLp.deriv_zero, SobolevIntervalLp.deriv_zero, hx2, hx3]
      have hz : ∀ᵐ x ∂(volume.restrict I), x ∉ ((Opens.Ioo a b : Opens ℝ) : Set ℝ) →
          fn u x - φ x = 0 := by
        filter_upwards [hfn0] with x hx hx'
        rw [hx hx', φ.eq_zero_of_notMem hx', sub_zero]
      exact (eLpNorm_congr_ae e1).trans ((eLpNorm_restrict_eq_of_ae_eq_zero_off
        (Opens.Ioo a b).isOpen.measurableSet hJI hz).trans (eLpNorm_congr_ae e2).symm)
    · have e1 : ⇑(deriv (u - TestFunction.toSobolevIntervalLp p φ') 1) =ᵐ[volume.restrict I]
          fun x ↦ deriv u 1 x - _root_.deriv φ x := by
        rw [SobolevIntervalLp.deriv_sub]
        filter_upwards [Lp.coeFn_sub (deriv u 1) (deriv (TestFunction.toSobolevIntervalLp p φ') 1),
          φ'.coeFn_deriv_toSobolevIntervalLp_one (p := p)] with x hx1 hx2
        rw [hx1, Pi.sub_apply, hx2, hφ']
      have e2 : ⇑(deriv (restrict hJI u - TestFunction.toSobolevIntervalLp p φ) 1)
          =ᵐ[volume.restrict ((Opens.Ioo a b : Opens ℝ) : Set ℝ)]
            fun x ↦ deriv u 1 x - _root_.deriv φ x := by
        rw [SobolevIntervalLp.deriv_sub]
        filter_upwards [Lp.coeFn_sub (deriv (restrict hJI u) 1)
          (deriv (TestFunction.toSobolevIntervalLp p φ) 1), coeFn_deriv_restrict_one hJI u,
          φ.coeFn_deriv_toSobolevIntervalLp_one (p := p)] with x hx1 hx2 hx3
        rw [hx1, Pi.sub_apply, hx2, hx3]
      have hz : ∀ᵐ x ∂(volume.restrict I), x ∉ ((Opens.Ioo a b : Opens ℝ) : Set ℝ) →
          deriv u 1 x - _root_.deriv φ x = 0 := by
        filter_upwards [hderiv0] with x hx hx'
        rw [hx hx', Function.notMem_support.1 fun h ↦ hx' (φ.tsupport_subset
          (support_deriv_subset h)), sub_zero]
      exact (eLpNorm_congr_ae e1).trans ((eLpNorm_restrict_eq_of_ae_eq_zero_off
        (Opens.Ioo a b).isOpen.measurableSet hJI hz).trans (eLpNorm_congr_ae e2).symm)
  rw [dist_eq_norm] at hw ⊢
  calc ‖u - TestFunction.toSobolevIntervalLp p φ'‖
      ≤ ‖deriv (u - TestFunction.toSobolevIntervalLp p φ') 0‖
        + ‖deriv (u - TestFunction.toSobolevIntervalLp p φ') 1‖ := by
        have := norm_le_sum_norm_deriv (u - TestFunction.toSobolevIntervalLp p φ')
        rwa [Fin.sum_univ_two] at this
    _ ≤ ‖restrict hJI u - w‖ + ‖restrict hJI u - w‖ := add_le_add (key 0) (key 1)
    _ < ε / 2 + ε / 2 := add_lt_add hw hw
    _ = ε := add_halves ε

/-- **Theorem 8.12 of [brezis2011functional]**: for `1 ≤ p < ∞` and an open interval `I`, bounded
or not, `u ∈ W^{1,p}(I)` lies in `W_0^{1,p}(I)` if and only if its continuous representative
vanishes on the boundary of `I`. The converse direction reduces to the bounded case through the
cut-offs `ζ_n u` (`SobolevIntervalLp.tendsto_cutoff_smul`), which vanish off `(-2(n+1), 2(n+1))`
and at the finite endpoints of `I`, hence lie in `W_0^{1,p}(I)` (`mem_of_rep_eq_zero_off_Ioo`),
and converge to `u`. -/
theorem _root_.mem_sobolevIntervalLpZero_iff (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ⊤)
    (u : SobolevIntervalLp 1 p I) :
    u ∈ SobolevIntervalLpZero 1 p I ↔ ∀ x ∈ frontier (I : Set ℝ), rep u x = 0 := by
  refine ⟨fun hu x hx ↦ rep_frontier_eq_zero hI hu hx, fun h ↦ ?_⟩
  refine SobolevMultiIndexZero.isClosed.mem_of_tendsto
    (tendsto_cutoff_smul hI hp u) (Eventually.of_forall fun n ↦ ?_)
  refine mem_of_rep_eq_zero_off_Ioo hI hp _ (c := -(2 * ((n : ℝ) + 1))) (d := 2 * ((n : ℝ) + 1))
    (fun x hx ↦ ?_) fun x hx hx' ↦ ?_
  · rw [rep_cutoff hI n u (frontier_subset_closure hx)]
    beta_reduce
    rw [h x hx, mul_zero]
  · rw [rep_cutoff hI n u hx]
    beta_reduce
    rw [cutoffFn_of_le_abs ?_, zero_mul]
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hx'
    rcases hx' with hx' | hx'
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; exact hx'

/-- **Remark 13 of [brezis2011functional], Chapter 8**: `W_0^{1,p}(ℝ) = W^{1,p}(ℝ)` for
`1 ≤ p < ∞`, the instance `I = ℝ` of Theorem 8.12 (`ℝ` has no boundary). -/
theorem _root_.sobolevIntervalLpZero_top (hp : p ≠ ⊤) : SobolevIntervalLpZero 1 p ⊤ = ⊤ :=
  eq_top_iff.2 fun u _ ↦ (mem_sobolevIntervalLpZero_iff Opens.ordConnected_top hp u).2 fun x hx ↦ by
    rw [Opens.coe_top, frontier_univ] at hx
    exact absurd hx (notMem_empty x)

/-- **Remark 14 (ii) of [brezis2011functional], Chapter 8**: if the continuous representative of
`u ∈ W^{1,p}(I)`, `1 ≤ p < ∞`, vanishes off a subset `K ⊆ I` (for instance a compact one), then
`u ∈ W_0^{1,p}(I)`: `ũ` vanishes at the boundary points of `I`, which are not in `K`. -/
theorem mem_of_rep_eq_zero_off (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ⊤)
    (u : SobolevIntervalLp 1 p I) {K : Set ℝ} (hKI : K ⊆ I)
    (hK : ∀ x ∈ closure (I : Set ℝ), x ∉ K → rep u x = 0) : u ∈ SobolevIntervalLpZero 1 p I :=
  (mem_sobolevIntervalLpZero_iff hI hp u).2 fun x hx ↦
    hK x (frontier_subset_closure hx) fun hxK ↦ I.notMem_of_mem_frontier hx (hKI hxK)

/-- **Remark 14 (ii) of [brezis2011functional], Chapter 8**, for the support: if the support of
the continuous representative of `u ∈ W^{1,p}(I)`, `1 ≤ p < ∞`, lies in `I`, then
`u ∈ W_0^{1,p}(I)`. -/
theorem mem_of_tsupport_rep_subset (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ⊤)
    (u : SobolevIntervalLp 1 p I) (h : tsupport (rep u) ⊆ I) :
    u ∈ SobolevIntervalLpZero 1 p I :=
  mem_of_rep_eq_zero_off hI hp u h fun _ _ hx ↦ image_eq_zero_of_notMem_tsupport hx

/-- **Remark 14 (ii) of [brezis2011functional], Chapter 8**, as stated there: if the continuous
representative of `u ∈ W^{1,p}(I)`, `1 ≤ p < ∞`, vanishes off a compact subset of `I`, then
`u ∈ W_0^{1,p}(I)`. -/
theorem mem_of_hasCompactSupport (hI : (I : Set ℝ).OrdConnected) (hp : p ≠ ⊤)
    (u : SobolevIntervalLp 1 p I)
    (h : ∃ K : Set ℝ, IsCompact K ∧ K ⊆ I ∧ ∀ x ∈ closure (I : Set ℝ), x ∉ K → rep u x = 0) :
    u ∈ SobolevIntervalLpZero 1 p I :=
  let ⟨_, _, hKI, hK⟩ := h
  mem_of_rep_eq_zero_off hI hp u hKI hK

end SobolevIntervalLpZero

/-! ### Remark 16 (i): the zero extension -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The `L^p(ℝ)` distance from a function vanishing off `I` to the zero extension of `g` is the
`L^p(I)` distance to `g`. -/
theorem eLpNorm_sub_indicator (f g : ℝ → ℝ) (hf : ∀ x, x ∉ (I : Set ℝ) → f x = 0) :
    eLpNorm (f - (I : Set ℝ).indicator g) p volume = eLpNorm (f - g) p (volume.restrict I) := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict I.isOpen.measurableSet]
  congr 1
  funext x
  by_cases hx : x ∈ (I : Set ℝ)
  · simp [indicator_of_mem hx]
  · simp [indicator_of_notMem hx, hf x hx]

/-- The components of a convergent sequence converge, in `ℝ≥0∞`. -/
theorem tendsto_enorm_deriv_sub {w : ℕ → SobolevIntervalLp 1 p I} {u : SobolevIntervalLp 1 p I}
    (hlim : Tendsto w atTop (𝓝 u)) (j : Fin 2) :
    Tendsto (fun n ↦ ‖deriv (w n - u) j‖ₑ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n ↦ ‖deriv (w n - u) j‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ norm_deriv_le _ j)
      (tendsto_iff_norm_sub_tendsto_zero.1 hlim)
  have h2 := ENNReal.tendsto_ofReal h1
  rw [ENNReal.ofReal_zero] at h2
  simpa only [ofReal_norm] using h2

omit [Fact (1 ≤ p)] in
/-- The zero extension of the function of `u ∈ W^{1,p}(I)` lies in `L^p(ℝ)`. -/
theorem memLp_indicator_deriv (u : SobolevIntervalLp 1 p I) (j : Fin 2) :
    MemLp ((I : Set ℝ).indicator (deriv u j)) p volume :=
  memLp_iff.2 (by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict I.isOpen.measurableSet]
    exact Lp.eLpNorm_lt_top _)

end SobolevIntervalLp

namespace SobolevIntervalLpZero

variable {p : ℝ≥0∞} {I : Opens ℝ} [Fact (1 ≤ p)]

open SobolevIntervalLp

/-- **Remark 16 (i) of [brezis2011functional], Chapter 8, forward direction**: the zero extension
`ū` of `u ∈ W_0^{1,p}(I)`, `1 ≤ p ≤ ∞`, has the zero extension of `u'` as weak derivative on
`ℝ`. Test functions `φ_n` on `I` converge to `u` in `W^{1,p}(I)`; as test functions on `ℝ` they
converge to `ū` in `W^{1,p}(ℝ)`, and the weak derivative is closed under `L^p` limits
(`hasWeakDerivOn_of_tendsto_eLpNorm`). -/
theorem hasWeakDerivOn_indicator {u : SobolevIntervalLp 1 p I}
    (hu : u ∈ SobolevIntervalLpZero 1 p I) :
    HasWeakDerivOn ((I : Set ℝ).indicator (fn u)) ((I : Set ℝ).indicator (deriv u 1)) ⊤ := by
  -- a sequence of test functions converging to `u`
  have hu' : u ∈ closure (SobolevMultiIndex.testFunctions ℝ (Module.Basis.singleton Unit ℝ) 1 p I
      volume : Set (SobolevIntervalLp 1 p I)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hu
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.1 hu'
  choose φ hφ using hw
  have hwφ : ∀ n, w n = TestFunction.toSobolevIntervalLp p (φ n) := fun n ↦
    eq_of_fn_ae_eq ((hφ n).trans (φ n).fn_toSobolevIntervalLp_ae_eq.symm)
  have h0 := tendsto_enorm_deriv_sub hlim 0
  have h1 := tendsto_enorm_deriv_sub hlim 1
  refine hasWeakDerivOn_of_tendsto_eLpNorm (I := ⊤) (p := p) (u := fun n ↦ ⇑(φ n))
    (w := fun n ↦ _root_.deriv (φ n)) (fun n ↦ ?_) ?_ ?_ ?_ ?_
  · exact hasWeakDerivOn_of_contDiffOn ((φ n).contDiff.of_le (by simp)).contDiffOn
  · exact memLp_restrict_top_iff.2 (memLp_indicator_deriv u 0)
  · exact memLp_restrict_top_iff.2 (memLp_indicator_deriv u 1)
  · refine h0.congr fun n ↦ ?_
    rw [Opens.coe_top, Measure.restrict_univ, eLpNorm_sub_indicator _ _
      (fun x hx ↦ (φ n).eq_zero_of_notMem hx), Lp.enorm_def, SobolevIntervalLp.deriv_sub]
    refine (eLpNorm_congr_ae ?_).symm
    filter_upwards [Lp.coeFn_sub (deriv (w n) 0) (deriv u 0), hφ n] with x hx1 hx2
    rw [hx1, Pi.sub_apply, Pi.sub_apply]
    exact congrArg₂ (· - ·) hx2.symm rfl
  · refine h1.congr fun n ↦ ?_
    rw [Opens.coe_top, Measure.restrict_univ, eLpNorm_sub_indicator _ _
      (fun x hx ↦ Function.notMem_support.1 fun h ↦ hx ((φ n).tsupport_subset
        (support_deriv_subset h))), Lp.enorm_def, SobolevIntervalLp.deriv_sub]
    refine (eLpNorm_congr_ae ?_).symm
    filter_upwards [Lp.coeFn_sub (deriv (w n) 1) (deriv u 1),
      (φ n).coeFn_deriv_toSobolevIntervalLp_one (p := p)] with x hx1 hx2
    rw [← hwφ n] at hx2
    rw [hx1, Pi.sub_apply, Pi.sub_apply, hx2]

/-- **Remark 16 (i) of [brezis2011functional], Chapter 8**: for `1 ≤ p < ∞` and an open interval
`I`, `u ∈ W^{1,p}(I)` lies in `W_0^{1,p}(I)` if and only if its zero extension `ū` lies in
`W^{1,p}(ℝ)`. Conversely, the continuous representative of `ū ∈ W^{1,p}(ℝ)` vanishes a.e. on
one side of each boundary point of `I`, hence at that point by continuity, and Theorem 8.12
applies. -/
theorem _root_.mem_sobolevIntervalLpZero_iff_indicator_mem (hI : (I : Set ℝ).OrdConnected)
    (hp : p ≠ ⊤) (u : SobolevIntervalLp 1 p I) :
    u ∈ SobolevIntervalLpZero 1 p I
      ↔ MemSobolevIntervalLp ((I : Set ℝ).indicator (fn u)) 1 p ⊤ := by
  constructor
  · intro hu
    exact memSobolevIntervalLp_one_iff.2 ⟨memLp_restrict_top_iff.2 (memLp_indicator_deriv u 0), _,
      hasWeakDerivOn_indicator hu, memLp_restrict_top_iff.2 (memLp_indicator_deriv u 1)⟩
  · intro h
    obtain ⟨v, hv⟩ := h.exists_sobolevIntervalLp
    rw [eventuallyEq_restrict_top_iff] at hv
    rw [mem_sobolevIntervalLpZero_iff hI hp]
    intro x hx
    have hcont : ContinuousOn (rep v) univ := by
      have := continuousOn_rep Opens.ordConnected_top v
      rwa [Opens.coe_top, closure_univ] at this
    have hrv : rep v =ᵐ[volume] (I : Set ℝ).indicator (fn u) := by
      have := (fn_ae_eq_rep Opens.ordConnected_top v).symm.trans
        (eventuallyEq_restrict_top_iff.2 hv)
      exact eventuallyEq_restrict_top_iff.1 this
    -- the representatives of `u` and `v` agree on the closure of `I`
    have hvu : fn u =ᵐ[volume.restrict I] rep v := by
      filter_upwards [hrv.filter_mono (ae_mono Measure.restrict_le_self),
        ae_restrict_mem I.isOpen.measurableSet] with y hy1 hy2
      rw [hy1, indicator_of_mem hy2]
    rw [rep_eq_of_continuousOn hI u (hcont.mono (subset_univ _)) hvu (frontier_subset_closure hx)]
    -- `I` lies on one side of `x`
    have hxI : x ∉ (I : Set ℝ) := I.notMem_of_mem_frontier hx
    have hside : (∀ y < x, y ∉ (I : Set ℝ)) ∨ (∀ y > x, y ∉ (I : Set ℝ)) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨⟨y₁, hy₁, hy₁I⟩, ⟨y₂, hy₂, hy₂I⟩⟩ := hcon
      exact hxI (hI.out hy₁I hy₂I ⟨hy₁.le, hy₂.le⟩)
    -- `ṽ` vanishes a.e. on that side, hence on it, hence at `x`
    have key : ∀ S : Set ℝ, IsOpen S → x ∈ closure S → (∀ y ∈ S, y ∉ (I : Set ℝ)) →
        rep v x = 0 := by
      intro S hS hxS hSI
      have h0 : rep v =ᵐ[volume.restrict S] 0 := by
        filter_upwards [hrv.filter_mono (ae_mono Measure.restrict_le_self),
          ae_restrict_mem hS.measurableSet] with y hy1 hy2
        rw [hy1, indicator_of_notMem (hSI y hy2)]
        rfl
      have hEq : EqOn (rep v) 0 S :=
        Measure.eqOn_open_of_ae_eq h0 hS (hcont.mono (subset_univ _)) continuousOn_const
      exact hEq.of_subset_closure (hcont.mono (subset_univ _)) continuousOn_const subset_closure
        subset_rfl hxS
    rcases hside with h | h
    · exact key (Iio x) isOpen_Iio (by rw [closure_Iio]; exact self_mem_Iic) fun y hy ↦ h y hy
    · exact key (Ioi x) isOpen_Ioi (by rw [closure_Ioi]; exact self_mem_Ici) fun y hy ↦ h y hy

end SobolevIntervalLpZero

end
