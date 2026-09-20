import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Numlib.Analysis.Sobolev.Interval
import Numlib.MeasureTheory.Function.LpSpace.Duality
import Numlib.MeasureTheory.Integral.IntervalIntegral

/-!
# Atkinson–Han §2.5: linear functionals

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §2.5: the book's dual space `V'` of bounded linear
functionals is Mathlib's `StrongDual 𝕜 V`.

The book's inner product `(u, v)` is linear in its *first* argument while Mathlib's `⟪u, v⟫` is
linear in its second, so the book's `ℓ(v) = (v, u)` is written `ℓ v = inner 𝕜 u v` below.

## Main results

* `IsSublinear`, `isSublinear_iff` — Definition 2.5.4 and its bridge to Mathlib's hypotheses.
* `theorem_2_5_2`, `theorem_2_5_5` — the Hahn–Banach theorem and its generalized (sublinear) form.
* `corollary_2_5_6`, `corollary_2_5_7` — norming functionals and the dual description (2.5.4) of
  the norm.
* `theorem_2_5_8` — the Riesz representation theorem, (2.5.5) and (2.5.6).
* `example_2_5_9_l2`, `example_2_5_9` — Example 2.5.9: the identification of `(L²(Ω))'` with
  `L²(Ω)`, and the representer of point evaluation on `H¹(a, b)`, which solves (2.5.8).
* `example_2_5_1`, `example_2_5_1_top` — Example 2.5.1: `(Lᵖ(Ω))' = L^{p'}(Ω)` for `1 ≤ p < ∞`
  through the pairing (2.5.1), and the dual of `L^∞(Ω)` strictly larger than `L¹(Ω)`.
* `cosetLinfty`, `contCosets`, `evalCoset`, `example_2_5_3` — Example 2.5.3: the point evaluation
  `ℓ_c([v]) = v(c)` on the cosets of continuous functions in `L^∞(0, 1)`, its Hahn–Banach
  extension of norm one, and the fact that no such extension is given by an `L¹` function.

`H¹(a, b)` is the backbone's `SobolevInterval 1 a b`
(`Numlib/Analysis/Sobolev/Interval.lean`), a Hilbert space whose inner product is
`(u, v)_{H¹} = ∫_a^b (u' v' + u v)` (`SobolevInterval.inner_eq_intervalIntegral`), and
point evaluation at `c ∈ [a, b]` is bounded on it because `H¹(a, b)` embeds in `C[a, b]`
(`SobolevInterval.toContinuousMap`), which is the hint of Exercise 2.5.5.

## Examples 2.5.1 and 2.5.3

The `Lᵖ`–`L^{p'}` duality is the backbone's Riesz representation theorem
`MeasureTheory.Lp.dualEquiv` (`Numlib/MeasureTheory/Function/LpSpace/Duality.lean`), stated on
any σ-finite measure, so Example 2.5.1 is proved for an arbitrary `Ω ⊆ ℝ^d` rather than the
book's bounded open set; its `p = ∞` clause is the backbone's
`MeasureTheory.Lp.not_surjective_toDual_top`. Example 2.5.3 builds the book's `V₀`, `ℓ_c` and
`ℓ̂_c` explicitly; that `ℓ̂_c` is not an `L¹` function is proved for every extension of `ℓ_c`,
by the argument of `MeasureTheory.Lp.exists_strongDual_top_apply_eq`
(`toDual_ne_of_forall_contDiff_apply_eq`). The book's further properties of `ℓ̂_c` (locality and
the bounds `m ≤ ℓ̂_c([v]) ≤ M`) are stated without proof and are not restated.
-/

open Filter Topology

namespace AtkinsonHan.Chapter02

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-! ### Theorem 2.5.2: the Hahn–Banach theorem -/

/-- **Hahn–Banach theorem** (Theorem 2.5.2). A bounded linear functional on a subspace `V₀` of a
normed space extends to a bounded linear functional on the whole space with the same norm. -/
theorem theorem_2_5_2 (V₀ : Submodule 𝕜 V) (ℓ : StrongDual 𝕜 V₀) :
    ∃ ℓhat : StrongDual 𝕜 V, (∀ v : V₀, ℓhat v = ℓ v) ∧ ‖ℓhat‖ = ‖ℓ‖ :=
  exists_extension_norm_eq V₀ ℓ

/-! ### Definition 2.5.4 and Theorem 2.5.5: the generalized Hahn–Banach theorem -/

/-- **Sublinear functional** (Definition 2.5.4): `p` is subadditive and positively homogeneous.
The book states positive homogeneity for all `α ≥ 0`; `isSublinear_iff` shows this is the same as
Mathlib's `α > 0` form. -/
def IsSublinear {E : Type*} [AddCommGroup E] [Module ℝ E] (p : E → ℝ) : Prop :=
  (∀ u v, p (u + v) ≤ p u + p v) ∧ ∀ (α : ℝ) (v : E), 0 ≤ α → p (α • v) = α * p v

/-- Bridge from Definition 2.5.4 to the hypotheses `N_add` and `N_hom` of Mathlib's
`exists_extension_of_le_sublinear`: positive homogeneity for `α > 0` already implies it for
`α = 0`, because `p 0 = p (2 • 0) = 2 p 0`. -/
theorem isSublinear_iff {E : Type*} [AddCommGroup E] [Module ℝ E] (p : E → ℝ) :
    IsSublinear p ↔
      (∀ u v, p (u + v) ≤ p u + p v) ∧ ∀ c : ℝ, 0 < c → ∀ v : E, p (c • v) = c * p v := by
  refine ⟨fun h => ⟨h.1, fun c hc v => h.2 c v hc.le⟩, fun h => ⟨h.1, fun α v hα => ?_⟩⟩
  rcases hα.lt_or_eq with hα' | hα'
  · exact h.2 α hα' v
  · have hzero : p 0 = 0 := by
      have := h.2 2 (by norm_num) (0 : E)
      rw [smul_zero] at this
      linarith
    rw [← hα', zero_smul, hzero, zero_mul]

/-- **Generalized Hahn–Banach theorem** (Theorem 2.5.5). On a real vector space, a linear
functional on a subspace dominated by a sublinear functional `p` extends to the whole space,
still dominated by `p`. -/
theorem theorem_2_5_5 {E : Type*} [AddCommGroup E] [Module ℝ E] (V₀ : Submodule ℝ E) (p : E → ℝ)
    (hp : IsSublinear p) (ℓ : V₀ →ₗ[ℝ] ℝ) (hℓ : ∀ v : V₀, ℓ v ≤ p v) :
    ∃ ℓhat : E →ₗ[ℝ] ℝ, (∀ v : V₀, ℓhat v = ℓ v) ∧ ∀ v, ℓhat v ≤ p v := by
  obtain ⟨hadd, hhom⟩ := (isSublinear_iff p).1 hp
  exact exists_extension_of_le_sublinear ⟨V₀, ℓ⟩ p (fun c hc x => hhom c hc x) hadd hℓ

/-! ### Corollaries 2.5.6 and 2.5.7 -/

/-- **Norming functional** (Corollary 2.5.6). For every nonzero `v` there is a functional of norm
one attaining `‖v‖` at `v`. -/
theorem corollary_2_5_6 (v : V) (hv : v ≠ 0) : ∃ ℓ : StrongDual 𝕜 V, ‖ℓ‖ = 1 ∧ ℓ v = ‖v‖ :=
  exists_dual_vector 𝕜 v (norm_ne_zero_iff.mpr hv)

/-- **(2.5.4)** (Corollary 2.5.7): the norm of `v` is the supremum of `|ℓ(v)|` over the unit
sphere of the dual space. -/
theorem corollary_2_5_7 (v : V) :
    ‖v‖ = sSup {r : ℝ | ∃ ℓ : StrongDual 𝕜 V, ‖ℓ‖ = 1 ∧ r = ‖ℓ v‖} := by
  have hbdd : ∀ r ∈ {r : ℝ | ∃ ℓ : StrongDual 𝕜 V, ‖ℓ‖ = 1 ∧ r = ‖ℓ v‖}, r ≤ ‖v‖ := by
    rintro r ⟨ℓ, hℓ, rfl⟩
    simpa [hℓ] using ℓ.le_opNorm v
  refine le_antisymm ?_ (Real.sSup_le hbdd (norm_nonneg v))
  rcases eq_or_ne v 0 with rfl | hv
  · rw [norm_zero]
    exact Real.sSup_nonneg (by rintro r ⟨ℓ, -, rfl⟩; exact norm_nonneg _)
  · obtain ⟨ℓ, hℓ, hval⟩ := corollary_2_5_6 (𝕜 := 𝕜) v hv
    refine le_csSup ⟨‖v‖, fun r hr => hbdd r hr⟩ ⟨ℓ, hℓ, ?_⟩
    rw [hval, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg v)]

/-! ### Theorem 2.5.8: the Riesz representation theorem -/

/-- **Riesz representation theorem** (Theorem 2.5.8). Every bounded linear functional `ℓ` on a
Hilbert space is `ℓ(v) = (v, u)` for a unique `u` (2.5.5), and `‖ℓ‖ = ‖u‖` (2.5.6). In Mathlib's
convention the book's `(v, u)` is `inner 𝕜 u v`, and the representer `u` is
`(InnerProductSpace.toDual 𝕜 H).symm ℓ`. -/
theorem theorem_2_5_8 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (ℓ : StrongDual 𝕜 H) :
    (∃! u : H, ∀ v, ℓ v = inner 𝕜 u v) ∧ ‖ℓ‖ = ‖(InnerProductSpace.toDual 𝕜 H).symm ℓ‖ := by
  constructor
  · refine ⟨(InnerProductSpace.toDual 𝕜 H).symm ℓ, fun v => ?_, ?_⟩
    · exact (InnerProductSpace.toDual_symm_apply).symm
    · change ∀ u : H, (∀ v, ℓ v = inner 𝕜 u v) → u = (InnerProductSpace.toDual 𝕜 H).symm ℓ
      intro u hu
      have : InnerProductSpace.toDual 𝕜 H u = ℓ := by
        ext v
        exact (hu v).symm
      rw [← this, LinearIsometryEquiv.symm_apply_apply]
  · exact ((InnerProductSpace.toDual 𝕜 H).symm.norm_map ℓ).symm

/-! ### Example 2.5.9: the Riesz representer of point evaluation on `H¹(a, b)` -/

section Example259

open MeasureTheory Set

variable {a b : ℝ}

/-- **Example 2.5.9**, the `L²` half: for `Ω ⊆ ℝ^d` the Riesz representation theorem puts the
bounded linear functionals on `L²(Ω)` in one-to-one correspondence with `L²(Ω)` itself through
(2.5.5), so `(L²(Ω))' = L²(Ω)`. It is `theorem_2_5_8` read on `L²(Ω)`. -/
theorem example_2_5_9_l2 {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : StrongDual ℝ (Lp ℝ 2 (volume.restrict Ω))) :
    ∃! u : Lp ℝ 2 (volume.restrict Ω), ∀ v, ℓ v = inner ℝ u v :=
  (theorem_2_5_8 ℓ).1

/-- **Example 2.5.9**, the `H¹(a, b)` half: for `c ∈ [a, b]` the functional `ℓ(v) = v(c)` of
(2.5.7) has a unique Riesz representer `u ∈ H¹(a, b)`, characterized by (2.5.8),

`∫_a^b (u'(x) v'(x) + u(x) v(x)) dx = v(c)` for every `v ∈ H¹(a, b)`.

Here `v(c)` is the value at `c` of the continuous representative of `v`, the embedding
`H¹(a, b) ↪ C[a, b]`. The book calls `u` the generalized solution of `-u'' + u = δ(x - c)` with
`u'(a) = u'(b) = 0`; that boundary value problem is not formalized. -/
theorem example_2_5_9 (hab : a < b) (c : Icc a b) :
    ∃! u : SobolevInterval 1 a b, ∀ v : SobolevInterval 1 a b,
      (∫ x in a..b, (SobolevInterval.deriv u 1 x * SobolevInterval.deriv v 1 x
          + SobolevInterval.fn u x * SobolevInterval.fn v x)) =
        SobolevInterval.toContinuousMap hab v c := by
  obtain ⟨u, hu, huniq⟩ := (theorem_2_5_8 (SobolevInterval.evalCLM hab c)).1
  refine ⟨u, fun v => ?_, fun u' hu' => huniq u' fun v => ?_⟩
  · rw [← SobolevInterval.inner_eq_intervalIntegral hab.le u v]
    exact (hu v).symm
  · rw [SobolevInterval.inner_eq_intervalIntegral hab.le u' v]
    exact (hu' v).symm

end Example259

section Example251

open MeasureTheory Set
open scoped ENNReal

/-! ### Example 2.5.1: `(Lᵖ(Ω))' = L^{p'}(Ω)` -/

/-- **Example 2.5.1**, the identification `(Lᵖ(Ω))' = L^{p'}(Ω)` for `1 ≤ p < ∞` and the conjugate
exponent `1/p + 1/p' = 1` (`p' = ∞` when `p = 1`): every `ℓ ∈ (Lᵖ(Ω))'` is `ℓ(v) = ∫_Ω u v`
(2.5.1) for a unique `u ∈ L^{p'}(Ω)`; conversely every `u ∈ L^{p'}(Ω)` defines through (2.5.1) a
bounded linear functional, of norm `‖u‖_{p'}`; and the identification is a linear isometric
isomorphism `L^{p'}(Ω) ≃ (Lᵖ(Ω))'`.

The book takes `Ω ⊆ ℝ^d` bounded and open; the backbone's Riesz representation theorem
`MeasureTheory.Lp.dualEquiv` (`Numlib/MeasureTheory/Function/LpSpace/Duality.lean`) needs only a
σ-finite measure, so `Ω` is any set here. The scalars are `ℝ` or `ℂ`, and the pairing is
bilinear, `∫ u v` with no conjugate, as in (2.5.1). -/
theorem example_2_5_1 {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (p p' : ℝ≥0∞) [Fact (1 ≤ p)]
    [Fact (1 ≤ p')] [p.HolderConjugate p'] (hp : p ≠ ∞) :
    (∀ ℓ : StrongDual 𝕜 (Lp 𝕜 p (volume.restrict Ω)),
      ∃! u : Lp 𝕜 p' (volume.restrict Ω), ∀ v, ℓ v = ∫ x in Ω, u x * v x) ∧
    (∀ u : Lp 𝕜 p' (volume.restrict Ω), ∃ ℓ : StrongDual 𝕜 (Lp 𝕜 p (volume.restrict Ω)),
      ‖ℓ‖ = ‖u‖ ∧ ∀ v, ℓ v = ∫ x in Ω, u x * v x) ∧
    ∃ e : Lp 𝕜 p' (volume.restrict Ω) ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 p (volume.restrict Ω)),
      ∀ u v, e u v = ∫ x in Ω, u x * v x := by
  set e := Lp.dualEquiv 𝕜 p p' (volume.restrict Ω) hp with he
  refine ⟨fun ℓ ↦ ⟨e.symm ℓ, fun v ↦ ?_, fun u hu ↦ ?_⟩, fun u ↦ ⟨e u, e.norm_map u,
    fun v ↦ Lp.dualEquiv_apply hp u v⟩, e, fun u v ↦ Lp.dualEquiv_apply hp u v⟩
  · rw [← Lp.dualEquiv_apply hp (e.symm ℓ) v, he, LinearIsometryEquiv.apply_symm_apply]
  · refine e.injective ?_
    rw [he, LinearIsometryEquiv.apply_symm_apply]
    ext v
    rw [Lp.dualEquiv_apply hp u v, hu v]

/-- **Example 2.5.1**, the case `p = ∞`: the dual of `L^∞(Ω)` is strictly larger than `L¹(Ω)`. For
a nonempty open `Ω ⊆ ℝ^d` (`d ≥ 1`) there is a functional `ℓ ∈ (L^∞(Ω))'` that is not of the form
(2.5.1) for any `u ∈ L¹(Ω)`: the backbone's `MeasureTheory.Lp.not_surjective_toDual_top`, a
Hahn–Banach extension of a point evaluation (Example 2.5.3). Real scalars. -/
theorem example_2_5_1_top {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) (hΩ : IsOpen Ω)
    (hne : Ω.Nonempty) :
    ∃ ℓ : StrongDual ℝ (Lp ℝ ∞ (volume.restrict Ω)), ∀ u : Lp ℝ 1 (volume.restrict Ω),
      ∃ v, ℓ v ≠ ∫ x in Ω, u x * v x := by
  have h := Lp.not_surjective_toDual_top (volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))) hΩ hne
  rw [Function.Surjective, not_forall] at h
  obtain ⟨ℓ, hℓ⟩ := h
  refine ⟨ℓ, fun u ↦ ?_⟩
  by_contra hcon
  push Not at hcon
  exact hℓ ⟨u, ContinuousLinearMap.ext fun v ↦ by rw [Lp.toDual_apply, hcon v]⟩

end Example251

/-! ### Example 2.5.3: point evaluation on `L^∞(0, 1)` -/

section Example253

open MeasureTheory Set
open scoped ENNReal

/-- The coset `[v] ∈ L^∞(0, 1)` of a continuous function `v ∈ C[0, 1]`, Example 2.5.3: the class
of the extension of `v` by its endpoint values. -/
noncomputable def cosetLinfty : C(Icc (0 : ℝ) 1, ℝ) →ₗ[ℝ] Lp ℝ ∞ (volume.restrict (Ioo (0 : ℝ) 1))
    where
  toFun v := (ContinuousMap.IccExtend zero_le_one v).continuous.continuousOn.memLp_top_restrict_Ioo
    |>.toLp _
  map_add' v w := by
    rw [← MemLp.toLp_add]
    exact (MemLp.toLp_eq_toLp_iff _ _).2 (Eventually.of_forall fun x ↦ by
      simp [ContinuousMap.coe_IccExtend, IccExtend, Pi.add_apply])
  map_smul' c v := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact (MemLp.toLp_eq_toLp_iff _ _).2 (Eventually.of_forall fun x ↦ by
      simp [ContinuousMap.coe_IccExtend, IccExtend, Pi.smul_apply])

/-- The coset of `v` is the extension of `v` almost everywhere on `(0, 1)`. -/
theorem coeFn_cosetLinfty (v : C(Icc (0 : ℝ) 1, ℝ)) :
    cosetLinfty v =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] IccExtend zero_le_one v :=
  MemLp.coeFn_toLp
    (ContinuousMap.IccExtend zero_le_one v).continuous.continuousOn.memLp_top_restrict_Ioo

/-- **The values of a continuous function are bounded by the `L^∞(0, 1)` norm of its coset**,
the inequality `|v(x)| ≤ ‖[v]‖_∞` for `x ∈ [0, 1]` of Example 2.5.3: the essential supremum over
`(0, 1)` bounds `|v|` on a dense subset of `[0, 1]`, hence everywhere by continuity. -/
theorem norm_apply_le_norm_cosetLinfty (v : C(Icc (0 : ℝ) 1, ℝ)) (x : Icc (0 : ℝ) 1) :
    ‖v x‖ ≤ ‖cosetLinfty v‖ := by
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ‖IccExtend zero_le_one v t‖ ≤ ‖cosetLinfty v‖ := by
    filter_upwards [coeFn_cosetLinfty v, Lp.ae_norm_le_norm_top (cosetLinfty v)] with t ht ht'
    rw [← ht]
    exact ht'
  have hIoo : ∀ t ∈ Ioo (0 : ℝ) 1, ‖IccExtend zero_le_one v t‖ ≤ ‖cosetLinfty v‖ :=
    forall_of_ae_restrict_of_isOpen isOpen_Ioo (by
      simp only [not_le]
      exact isOpen_lt continuous_const
        (ContinuousMap.IccExtend zero_le_one v).continuous.norm) hae
  have hcl : closure (Ioo (0 : ℝ) 1) ⊆ {t | ‖IccExtend zero_le_one v t‖ ≤ ‖cosetLinfty v‖} :=
    (isClosed_le (ContinuousMap.IccExtend zero_le_one v).continuous.norm
      continuous_const).closure_subset_iff.2 hIoo
  rw [closure_Ioo zero_ne_one] at hcl
  have := hcl x.2
  rwa [mem_ofPred_eq, IccExtend_val] at this

/-- **The `L^∞(0, 1)` norm of the coset of `v ∈ C[0, 1]` is the supremum norm of `v`**: the
"equivalence" of the norm (2.5.2) restricted to `V₀` with the norm of `C[0, 1]` of Example 2.5.3
is an equality. -/
theorem norm_cosetLinfty (v : C(Icc (0 : ℝ) 1, ℝ)) : ‖cosetLinfty v‖ = ‖v‖ := by
  refine le_antisymm ?_ ((ContinuousMap.norm_le _ (norm_nonneg _)).2
    (norm_apply_le_norm_cosetLinfty v))
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  refine ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) (eLpNormEssSup_le_of_ae_bound ?_)
  filter_upwards [coeFn_cosetLinfty v, ae_restrict_mem measurableSet_Ioo] with t ht htI
  rw [ht, IccExtend_of_mem _ _ (Ioo_subset_Icc_self htI)]
  exact v.norm_coe_le_norm _

/-- The coset map is injective: `V₀` is a copy of `C[0, 1]` inside `L^∞(0, 1)`. -/
theorem cosetLinfty_injective : Function.Injective cosetLinfty :=
  (injective_iff_map_eq_zero _).2 fun v hv ↦ by
    have h := norm_cosetLinfty v
    rw [hv, norm_zero] at h
    exact norm_eq_zero.1 h.symm

/-- **`V₀`**, the subspace of `L^∞(0, 1)` of the cosets of continuous functions on `[0, 1]`,
Example 2.5.3. -/
noncomputable abbrev contCosets : Submodule ℝ (Lp ℝ ∞ (volume.restrict (Ioo (0 : ℝ) 1))) :=
  LinearMap.range cosetLinfty

/-- **The point evaluation `ℓ_c([v]) = v(c)`** (2.5.3) on `V₀`, well defined because the coset map
is injective, and bounded with `‖ℓ_c‖ ≤ 1` because `|v(c)| ≤ ‖[v]‖_∞`. -/
noncomputable def evalCoset (c : Icc (0 : ℝ) 1) : StrongDual ℝ contCosets :=
  LinearMap.mkContinuous
    ((ContinuousMap.evalCLM ℝ c : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ).toLinearMap ∘ₗ
      (LinearEquiv.ofInjective cosetLinfty cosetLinfty_injective).symm.toLinearMap) 1
    fun g ↦ by
      obtain ⟨v, rfl⟩ := (LinearEquiv.ofInjective cosetLinfty cosetLinfty_injective).surjective g
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, one_mul]
      exact norm_apply_le_norm_cosetLinfty v c

/-- The coset of a continuous function lies in `V₀`. -/
theorem cosetLinfty_mem_contCosets (v : C(Icc (0 : ℝ) 1, ℝ)) : cosetLinfty v ∈ contCosets :=
  LinearMap.mem_range_self _ v

/-- `ℓ_c` evaluates the coset of `v` to `v(c)`. -/
@[simp]
theorem evalCoset_apply (c : Icc (0 : ℝ) 1) (v : C(Icc (0 : ℝ) 1, ℝ)) :
    evalCoset c ⟨cosetLinfty v, cosetLinfty_mem_contCosets v⟩ = v c := by
  change (ContinuousMap.evalCLM ℝ c)
    ((LinearEquiv.ofInjective cosetLinfty cosetLinfty_injective).symm
      ⟨cosetLinfty v, cosetLinfty_mem_contCosets v⟩) = v c
  have : (LinearEquiv.ofInjective cosetLinfty cosetLinfty_injective).symm
      ⟨cosetLinfty v, cosetLinfty_mem_contCosets v⟩ = v := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [this]
  rfl

/-- `‖ℓ_c‖ = 1`: the bound `|v(c)| ≤ ‖[v]‖_∞` gives `‖ℓ_c‖ ≤ 1`, and the constant function `1`
gives equality. -/
theorem norm_evalCoset (c : Icc (0 : ℝ) 1) : ‖evalCoset c‖ = 1 := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) ?_
  have h1 := (evalCoset c).le_opNorm ⟨cosetLinfty 1, cosetLinfty_mem_contCosets 1⟩
  rw [evalCoset_apply, ContinuousMap.one_apply] at h1
  change ‖(1 : ℝ)‖ ≤ ‖evalCoset c‖ * ‖cosetLinfty 1‖ at h1
  simp only [norm_cosetLinfty, norm_one, mul_one] at h1
  exact h1

/-- A functional on `L^∞(0, 1)` extending `ℓ_c` is the point evaluation at `c` on the continuous
functions of the line. -/
theorem apply_toLp_eq_of_forall_cosetLinfty (c : Icc (0 : ℝ) 1)
    (ℓ : StrongDual ℝ (Lp ℝ ∞ (volume.restrict (Ioo (0 : ℝ) 1))))
    (hℓ : ∀ v : C(Icc (0 : ℝ) 1, ℝ), ℓ (cosetLinfty v) = v c) (f : ℝ → ℝ)
    (hf : MemLp f ∞ (volume.restrict (Ioo (0 : ℝ) 1))) (hfc : Continuous f) :
    ℓ (hf.toLp f) = f c := by
  set v : C(Icc (0 : ℝ) 1, ℝ) := ⟨fun t ↦ f t, hfc.comp continuous_subtype_val⟩ with hv
  have : hf.toLp f = cosetLinfty v := by
    refine (MemLp.toLp_eq_toLp_iff hf (ContinuousMap.IccExtend zero_le_one
      v).continuous.continuousOn.memLp_top_restrict_Ioo).2 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [ContinuousMap.coe_IccExtend, IccExtend_of_mem _ _ (Ioo_subset_Icc_self ht)]
    rfl
  rw [this, hℓ]
  rfl

/-- **Example 2.5.3**: on the subspace `V₀ ⊆ L^∞(0, 1)` of the cosets of continuous functions
(`contCosets`), the point evaluation `ℓ_c([v]) = v(c)` (2.5.3) at `c ∈ [0, 1]` is well defined
and bounded with `‖ℓ_c‖ = 1` (`evalCoset`); the Hahn–Banach theorem (`theorem_2_5_2`) extends it
to `ℓ̂_c ∈ (L^∞(0, 1))'` with `‖ℓ̂_c‖ = 1` — a point evaluation on merely measurable functions;
and no such extension is of the form (2.5.1) for a `u ∈ L¹(0, 1)`: the dual of `L^∞(0, 1)` is
strictly larger than `L¹(0, 1)` (Example 2.5.1), the point of the example.

The book's further properties of `ℓ̂_c` (the bounds `m ≤ ℓ̂_c([v]) ≤ M` from a neighbourhood of
`c`, the value `v(c)` at a point of continuity of `v`) are stated without proof and are not
restated. -/
theorem example_2_5_3 (c : Icc (0 : ℝ) 1) :
    ‖evalCoset c‖ = 1 ∧
    (∃ ℓhat : StrongDual ℝ (Lp ℝ ∞ (volume.restrict (Ioo (0 : ℝ) 1))),
      (∀ v : C(Icc (0 : ℝ) 1, ℝ), ℓhat (cosetLinfty v) = v c) ∧ ‖ℓhat‖ = 1) ∧
    ∀ ℓhat : StrongDual ℝ (Lp ℝ ∞ (volume.restrict (Ioo (0 : ℝ) 1))),
      (∀ v : C(Icc (0 : ℝ) 1, ℝ), ℓhat (cosetLinfty v) = v c) →
      ∀ u : Lp ℝ 1 (volume.restrict (Ioo (0 : ℝ) 1)),
        ∃ w, ℓhat w ≠ ∫ x in Ioo (0 : ℝ) 1, u x * w x := by
  refine ⟨norm_evalCoset c, ?_, fun ℓhat hℓ u ↦ ?_⟩
  · obtain ⟨ℓhat, hext, hnorm⟩ := theorem_2_5_2 contCosets (evalCoset c)
    refine ⟨ℓhat, fun v ↦ ?_, hnorm.trans (norm_evalCoset c)⟩
    rw [← evalCoset_apply c v]
    exact hext ⟨cosetLinfty v, cosetLinfty_mem_contCosets v⟩
  · have h := Lp.toDual_ne_of_forall_contDiff_apply_eq (x₀ := (c : ℝ)) ℓhat
      (fun f hf hfc _ ↦ apply_toLp_eq_of_forall_cosetLinfty c ℓhat hℓ f hf hfc.continuous) u
    by_contra hcon
    push Not at hcon
    exact h (ContinuousLinearMap.ext fun w ↦ by rw [Lp.toDual_apply, hcon w])

end Example253

end AtkinsonHan.Chapter02
