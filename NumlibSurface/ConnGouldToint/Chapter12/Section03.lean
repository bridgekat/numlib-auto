import NumlibSurface.ConnGouldToint.Chapter12.Section02
import NumlibSurface.ConnGouldToint.Chapter06.Section04
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.MetricSpace.Thickening

/-! # Geometry of active constraints at limit points -/

open Filter Topology
open scoped RealInnerProductSpace Matrix

namespace ConnGouldToint.Chapter12

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The indices of zero-valued inequality constraints at the point. -/
def activeConstraintSet (c : ι → E → ℝ) (x : E) : Set ι := {i | c i x = 0}

/-- Positive multipliers on the active constraints, with stationarity in the
book's convention (c_i ≥ 0). The supplied normal fields are the inward
constraint gradients. -/
def HasStrictActiveMultipliers [Fintype ι] (c : ι → E → ℝ) (n : ι → E → E)
    (g : E → E) (x : E) : Prop :=
  ∃ μ : ι → ℝ, g x = ∑ i, μ i • n i x ∧
    (∀ i ∈ activeConstraintSet c x, 0 < μ i) ∧
    ∀ i ∉ activeConstraintSet c x, μ i = 0

/-- A supported normal representation near a strictly complementary point
identifies the active set even when the represented vector is perturbed. -/
theorem eventually_activeConstraintSet_eq_of_normal_representation [Fintype ι]
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E} {x : E}
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i))
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ n i x))
    (hmul : HasStrictActiveMultipliers c n g x) :
    ∀ᶠ y : E × E in 𝓝 (x, g x),
      (∃ μ : ι → ℝ, y.2 = ∑ i, μ i • n i y.1 ∧
        ∀ i ∉ activeConstraintSet c y.1, μ i = 0) →
      activeConstraintSet c y.1 = activeConstraintSet c x := by
  classical
  let w₀ : E × E := (x, g x)
  let J := activeConstraintSet c x
  have hsub : ∀ᶠ y in 𝓝 x, activeConstraintSet c y ⊆ J := by
    have h (i : ι) : ∀ᶠ y in 𝓝 x, i ∈ activeConstraintSet c y → i ∈ J := by
      by_cases hi : i ∈ J
      · exact Eventually.of_forall fun _ _ ↦ hi
      · have hne : c i x ≠ 0 := hi
        have ho := (show IsOpen {y : ℝ | y ≠ 0} from isOpen_ne).mem_nhds hne
        have he : ∀ᶠ y in 𝓝 x, c i y ≠ 0 := (hc i).continuousAt ho
        exact he.mono fun y hy hy' ↦ (hy hy').elim
    exact (eventually_all.mpr h).mono fun y hy i ↦ hy i
  let G (y : E × E) : Matrix J J ℝ := Matrix.gram ℝ (fun i : J ↦ n i y.1)
  let rhs (y : E × E) (i : J) := ⟪n i y.1, y.2⟫
  let a (y : E × E) := (G y)⁻¹ *ᵥ rhs y
  have hG : Continuous G := continuous_matrix fun i j ↦
    ((hn i).comp continuous_fst).inner ((hn j).comp continuous_fst)
  have hdet : (G w₀).det ≠ 0 := (Matrix.det_gram_ne_zero_iff_linearIndependent).mpr hind
  have hdnear : ∀ᶠ y in 𝓝 w₀, (G y).det ≠ 0 :=
    hG.matrix_det.continuousAt ((show IsOpen {y : ℝ | y ≠ 0} from isOpen_ne).mem_nhds hdet)
  have hGi : ContinuousAt (fun y ↦ (G y)⁻¹) w₀ := by
    apply (continuousAt_matrix_inv (G w₀) ?_).comp hG.continuousAt
    change ContinuousAt (fun y : ℝ ↦ Ring.inverse y) (G w₀).det
    simp_rw [Ring.inverse_eq_inv]
    exact continuousAt_inv₀ hdet
  have ha (i : J) : ContinuousAt (fun y ↦ a y i) w₀ := by
    change ContinuousAt (fun y ↦ ∑ j : J, (G y)⁻¹ i j * rhs y j) w₀
    apply tendsto_finsetSum _ fun j _ ↦ ?_
    have hrhs : ContinuousAt (fun y : E × E ↦ ⟪n j y.1, y.2⟫) w₀ :=
      (((hn j).comp continuous_fst).inner continuous_snd).continuousAt
    exact ((continuous_apply j).continuousAt.comp
      ((continuous_apply i).continuousAt.comp hGi)).mul hrhs
  have hcoef (y : E × E) (hJ : activeConstraintSet c y.1 ⊆ J) (hdet' : (G y).det ≠ 0)
      (μ : ι → ℝ) (hstat : y.2 = ∑ i, μ i • n i y.1)
      (hzero : ∀ i ∉ activeConstraintSet c y.1, μ i = 0) :
      a y = fun i : J ↦ μ i := by
    let μJ : J → ℝ := fun i ↦ μ i
    have hsum : (∑ i : J, μ i • n i y.1) = ∑ i, μ i • n i y.1 := by
      have hzero' : (∑ i : {i // i ∉ J}, μ i • n i y.1) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hzero i (fun hai ↦ i.2 (hJ hai)), zero_smul]
      simpa only [hzero', add_zero] using
        Fintype.sum_subtype_add_sum_subtype (· ∈ J) (fun i ↦ μ i • n i y.1)
    have hnormal : G y *ᵥ μJ = rhs y := by
      funext i
      change (∑ j : J, ⟪n i y.1, n j y.1⟫ * μ j) = ⟪n i y.1, y.2⟫
      rw [hstat, ← hsum, inner_sum]
      simp only [real_inner_smul_right, mul_comm]
    change (G y)⁻¹ *ᵥ rhs y = μJ
    rw [← hnormal, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet'),
      Matrix.one_mulVec]
  obtain ⟨μ, hμ, hμpos, hμzero⟩ := hmul
  have hax := hcoef w₀ (fun _ hi ↦ hi) hdet μ hμ hμzero
  have hposnear : ∀ᶠ y in 𝓝 w₀, ∀ i : J, 0 < a y i := by
    apply eventually_all.mpr
    intro i
    have hi : 0 < a w₀ i := by rw [hax]; exact hμpos i i.2
    exact (ha i).eventually (lt_mem_nhds hi)
  have hfst : Tendsto (Prod.fst : E × E → E) (𝓝 w₀) (𝓝 x) :=
    continuous_fst.continuousAt
  have hsub' : ∀ᶠ y : E × E in 𝓝 w₀, activeConstraintSet c y.1 ⊆ J :=
    hfst.eventually hsub
  filter_upwards [hsub', hdnear, hposnear] with y hyJ hyd hypos
  intro hy
  refine Set.Subset.antisymm hyJ ?_
  intro i hi
  obtain ⟨ν, hν, hνzero⟩ := hy
  have haν := hcoef y hyJ hyd ν hν hνzero
  have hi' := hypos ⟨i, hi⟩
  rw [haν] at hi'
  exact not_not.mp fun hn ↦ hi'.ne' (hνzero i hn)

/-- Active-set identification along convergent primal and represented normal
sequences, provided the coefficients are eventually supported on the active constraints. -/
theorem eventually_activeConstraintSet_eq_of_tendsto [Fintype ι] {α : Type*}
    {l : Filter α} {u v : α → E} {c : ι → E → ℝ} {n : ι → E → E}
    {g : E → E} {x : E}
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i))
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ n i x))
    (hmul : HasStrictActiveMultipliers c n g x)
    (hu : Tendsto u l (𝓝 x)) (hv : Tendsto v l (𝓝 (g x)))
    (hrep : ∀ᶠ k in l, ∃ μ : ι → ℝ, v k = ∑ i, μ i • n i (u k) ∧
      ∀ i ∉ activeConstraintSet c (u k), μ i = 0) :
    ∀ᶠ k in l, activeConstraintSet c (u k) = activeConstraintSet c x := by
  filter_upwards [(hu.prodMk_nhds hv).eventually
    (eventually_activeConstraintSet_eq_of_normal_representation hc hn hind hmul), hrep]
    with k hnear hrep
  exact hnear hrep

/-- The active set is locally constant relative to a set of strictly
complementary stationary points with independent active normals. -/
theorem eventually_activeConstraintSet_eq [Fintype ι] {S : Set E}
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E} {x : E}
    (hx : x ∈ S) (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i))
    (hg : Continuous g)
    (hind : LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ n i x))
    (hmul : ∀ y ∈ S, HasStrictActiveMultipliers c n g y) :
    ∀ᶠ y in 𝓝 x, y ∈ S → activeConstraintSet c y = activeConstraintSet c x := by
  have hpair : Tendsto (fun y ↦ (y, g y)) (𝓝 x) (𝓝 (x, g x)) :=
    continuousAt_id.prodMk hg.continuousAt
  filter_upwards [hpair.eventually
    (eventually_activeConstraintSet_eq_of_normal_representation hc hn hind (hmul x hx))]
    with y hy hyS
  obtain ⟨μ, hstat, _, hzero⟩ := hmul y hyS
  exact hy ⟨μ, hstat, hzero⟩

private theorem activeConstraintSet_continuousOn [Fintype ι]
    [TopologicalSpace (Set ι)] [DiscreteTopology (Set ι)] {S : Set E}
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i)) (hg : Continuous g)
    (hind : ∀ x ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ n i x))
    (hmul : ∀ x ∈ S, HasStrictActiveMultipliers c n g x) :
    ContinuousOn (activeConstraintSet c) S := by
  intro x hx
  apply (continuousWithinAt_const (b := activeConstraintSet c x)).congr_of_eventuallyEq
  · filter_upwards [(eventually_activeConstraintSet_eq hx hc hn hg (hind x hx) hmul).filter_mono
      nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyS
    exact hy hyS
  · rfl

/-- Lemma 12.3.1. Local constancy suffices on any connected set of limit
points. No path-connectedness assumption is needed. -/
theorem lemma_12_3_1 [Fintype ι] {S : Set E}
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    (hS : IsConnected S) (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i))
    (hg : Continuous g)
    (hind : ∀ x ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ n i x))
    (hmul : ∀ x ∈ S, HasStrictActiveMultipliers c n g x) :
    ∃ A : Set ι, ∀ x ∈ S, activeConstraintSet c x = A := by
  let : TopologicalSpace (Set ι) := ⊥
  let : DiscreteTopology (Set ι) := ⟨rfl⟩
  have hcont := activeConstraintSet_continuousOn hc hn hg hind hmul
  obtain ⟨x, hx⟩ := hS.nonempty
  exact ⟨activeConstraintSet c x, fun y hy ↦ hS.isPreconnected.constant hcont hy hx⟩

/-- Supported normal certificates identify the common active set uniformly
along a compact sequence and nearby trial points. -/
theorem eventually_activeConstraintSet_eq_of_compact_normal_certificates [Fintype ι]
    {K S : Set E} {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    {x u v : ℕ → E} {A : Set ι}
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K)
    (hlim : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i)) (hg : Continuous g)
    (hind : ∀ z ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ n i z))
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c n g z)
    (hAS : ∀ z ∈ S, activeConstraintSet c z = A)
    (hu : Tendsto (fun k ↦ u k - x k) atTop (𝓝 0))
    (hv : Tendsto (fun k ↦ v k - g (x k)) atTop (𝓝 0))
    (hrep : ∀ᶠ k in atTop, ∃ μ : ι → ℝ, v k = ∑ i, μ i • n i (u k) ∧
      ∀ i ∉ activeConstraintSet c (u k), μ i = 0) :
    ∀ᶠ k in atTop, activeConstraintSet c (u k) = A := by
  by_contra! hbad
  obtain ⟨j, hj, hjbad⟩ := extraction_of_frequently_atTop hbad
  obtain ⟨z, _, i, hi, hzi⟩ := hK.isSeqCompact (fun k ↦ hx (j k))
  let w := j ∘ i
  have hw : StrictMono w := hj.comp hi
  have hxw : Tendsto (x ∘ w) atTop (𝓝 z) := hzi
  have hz := hlim z w hw hxw
  have huw : Tendsto (u ∘ w) atTop (𝓝 z) := by
    change Tendsto (fun k ↦ u (w k)) atTop (𝓝 z)
    simpa only [Function.comp_apply, sub_add_cancel, zero_add] using
      (hu.comp hw.tendsto_atTop).add hxw
  have hgw : Tendsto (g ∘ x ∘ w) atTop (𝓝 (g z)) := hg.continuousAt.tendsto.comp hxw
  have hvw : Tendsto (v ∘ w) atTop (𝓝 (g z)) := by
    change Tendsto (fun k ↦ v (w k)) atTop (𝓝 (g z))
    simpa only [Function.comp_apply, sub_add_cancel, zero_add] using
      (hv.comp hw.tendsto_atTop).add hgw
  have hgood := eventually_activeConstraintSet_eq_of_tendsto hc hn (hind z hz) (hstat z hz)
    huw hvw (hw.tendsto_atTop.eventually hrep)
  obtain ⟨k, hk⟩ := hgood.exists
  exact hjbad (i k) (hk.trans (hAS z hz))

/-- A certificate-based version of Theorem 12.3.8. On a connected limit set,
asymptotically accurate supported normal certificates at the iterates and at
the Cauchy points identify the same active set at both sequences. -/
theorem theorem_12_3_8_of_normal_certificates [Fintype ι]
    {K S : Set E} {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    {x u v w : ℕ → E}
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K) (hS : IsConnected S)
    (hlim : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i)) (hg : Continuous g)
    (hind : ∀ z ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ n i z))
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c n g z)
    (hu : Tendsto (fun k ↦ u k - x k) atTop (𝓝 0))
    (hv : Tendsto (fun k ↦ v k - g (x k)) atTop (𝓝 0))
    (hw : Tendsto (fun k ↦ w k - g (x k)) atTop (𝓝 0))
    (hvrep : ∀ᶠ k in atTop, ∃ μ : ι → ℝ, v k = ∑ i, μ i • n i (x k) ∧
      ∀ i ∉ activeConstraintSet c (x k), μ i = 0)
    (hwrep : ∀ᶠ k in atTop, ∃ μ : ι → ℝ, w k = ∑ i, μ i • n i (u k) ∧
      ∀ i ∉ activeConstraintSet c (u k), μ i = 0) :
    ∃ A : Set ι, (∀ z ∈ S, activeConstraintSet c z = A) ∧
      ∀ᶠ k in atTop, activeConstraintSet c (x k) = A ∧ activeConstraintSet c (u k) = A := by
  obtain ⟨A, hA⟩ := lemma_12_3_1 hS hc hn hg hind hstat
  have hzero : Tendsto (fun k ↦ x k - x k) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : E)) atTop (𝓝 0))
  exact ⟨A, hA,
    (eventually_activeConstraintSet_eq_of_compact_normal_certificates
      hK hx hlim hc hn hg hind hstat hA hzero hv hvrep).and
    (eventually_activeConstraintSet_eq_of_compact_normal_certificates
      hK hx hlim hc hn hg hind hstat hA hu hw hwrep)⟩

/-- Lemma 12.3.7 under the compact-run normal certificate condition.
Infinitely many successful iterations then give an identified subsequence. -/
theorem lemma_12_3_7_of_normal_certificates [Fintype ι]
    {K S : Set E} {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    {x v : ℕ → E} {A : Set ι} {success : ℕ → Prop}
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K)
    (hlim : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i)) (hg : Continuous g)
    (hind : ∀ z ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ n i z))
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c n g z)
    (hA : ∀ z ∈ S, activeConstraintSet c z = A)
    (hv : Tendsto (fun k ↦ v k - g (x k)) atTop (𝓝 0))
    (hrep : ∀ᶠ k in atTop, ∃ μ : ι → ℝ, v k = ∑ i, μ i • n i (x k) ∧
      ∀ i ∉ activeConstraintSet c (x k), μ i = 0)
    (hsuccess : ∃ᶠ k in atTop, success k) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ ∀ i, success (j i) ∧ activeConstraintSet c (x (j i)) = A := by
  have hzero : Tendsto (fun k ↦ x k - x k) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : E)) atTop (𝓝 0))
  have hid := eventually_activeConstraintSet_eq_of_compact_normal_certificates
    hK hx hlim hc hn hg hind hstat hA hzero hv hrep
  exact extraction_of_frequently_atTop (hsuccess.and_eventually hid)

/-- Lemma 12.3.2. On a compact limit set, points with different active
sets are uniformly separated. This pairwise statement also separates a point
from any nonempty component with a different active set. -/
theorem lemma_12_3_2 [Fintype ι] {S : Set E}
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    (hS : IsCompact S) (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i))
    (hg : Continuous g)
    (hind : ∀ x ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c x ↦ n i x))
    (hmul : ∀ x ∈ S, HasStrictActiveMultipliers c n g x) :
    ∃ ψ ∈ Set.Ioo (0 : ℝ) 1, ∀ x ∈ S, ∀ y ∈ S,
      activeConstraintSet c x ≠ activeConstraintSet c y → ψ ≤ dist x y := by
  let : TopologicalSpace (Set ι) := ⊥
  let : DiscreteTopology (Set ι) := ⟨rfl⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let a (x : S) := activeConstraintSet c x
  have ha : Continuous a :=
    continuousOn_iff_continuous_domRestrict.mp (activeConstraintSet_continuousOn hc hn hg hind hmul)
  let T : Set (S × S) := {p | a p.1 ≠ a p.2}
  have hT : IsCompact T := by
    have hd : DiscreteTopology ((Set ι) × (Set ι)) := inferInstance
    exact ((isClosed_discrete {q : Set ι × Set ι | q.1 ≠ q.2}).preimage
      ((ha.comp continuous_fst).prodMk (ha.comp continuous_snd))).isCompact
  let D (p : S × S) := dist (p.1 : E) (p.2 : E)
  have hD : Continuous D :=
    (continuous_subtype_val.comp continuous_fst).dist (continuous_subtype_val.comp continuous_snd)
  by_cases hne : T.Nonempty
  · obtain ⟨p, hp, hmin⟩ := hT.exists_isMinOn hne hD.continuousOn
    have hp₀ : 0 < D p := by
      change a p.1 ≠ a p.2 at hp
      apply dist_pos.mpr
      intro he
      exact hp (congrArg a (Subtype.ext he))
    refine ⟨min (1 / 2) (D p), ⟨lt_min (by norm_num) hp₀,
      (min_le_left _ _).trans_lt (by norm_num)⟩, ?_⟩
    intro x hx y hy hxy
    exact (min_le_right _ _).trans ((isMinOn_iff.mp hmin) (⟨x, hx⟩, ⟨y, hy⟩) hxy)
  · refine ⟨1 / 2, by norm_num [Set.mem_Ioo], ?_⟩
    intro x hx y hy hxy
    exact (hne ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩).elim

/-- Theorem 12.3.3. In a compact run, the iterates eventually lie in a
fixed-radius neighborhood of a component of the limit set. Throughout
that neighborhood no constraint inactive on the component becomes active. -/
theorem theorem_12_3_3 [Fintype ι] {S Ω : Set E} {x : ℕ → E}
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    (hS : IsCompact S) (hΩ : IsCompact Ω) (hx : ∀ k, x k ∈ Ω)
    (hlimit : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hc : ∀ i, Continuous (c i)) (hn : ∀ i, Continuous (n i)) (hg : Continuous g)
    (hind : ∀ z ∈ S, LinearIndependent ℝ (fun i : activeConstraintSet c z ↦ n i z))
    (hmul : ∀ z ∈ S, HasStrictActiveMultipliers c n g z) :
    ∃ ψ ∈ Set.Ioo (0 : ℝ) 1, ∃ δ ∈ Set.Ioo (0 : ℝ) (ψ / 4),
      (∀ u ∈ S, ∀ v ∈ S, activeConstraintSet c u ≠ activeConstraintSet c v → ψ ≤ dist u v) ∧
      ∀ᶠ k in atTop, ∃ z ∈ S, IsCompact (connectedComponentIn S z) ∧
        x k ∈ Metric.cthickening δ (connectedComponentIn S z) ∧
        ∀ y ∈ Metric.cthickening δ (connectedComponentIn S z),
          activeConstraintSet c y ⊆ activeConstraintSet c z := by
  classical
  obtain ⟨ψ, hψ, hsep⟩ := lemma_12_3_2 hS hc hn hg hind hmul
  let : TopologicalSpace (Set ι) := ⊥
  let : DiscreteTopology (Set ι) := ⟨rfl⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have ha : Continuous (fun z : S ↦ activeConstraintSet c z) :=
    continuousOn_iff_continuous_domRestrict.mp
      (activeConstraintSet_continuousOn hc hn hg hind hmul)
  let T (i : ι) : Set E := {z ∈ S | c i z ≠ 0}
  have hT (i : ι) : IsCompact (T i) := by
    let A : Set (Set ι) := {a | i ∉ a}
    have hcompact := ((isClosed_discrete A).preimage ha).isCompact.image continuous_subtype_val
    convert hcompact using 1
    ext z
    constructor
    · rintro ⟨hz, hi⟩
      exact ⟨⟨z, hz⟩, hi, rfl⟩
    · rintro ⟨⟨z, hz⟩, hi, rfl⟩
      exact ⟨hz, hi⟩
  have hε (i : ι) : ∃ ε > 0, Metric.cthickening ε (T i) ⊆ {z | c i z ≠ 0} :=
    (hT i).exists_cthickening_subset_open
      ((show IsOpen {z : ℝ | z ≠ 0} from isOpen_ne).preimage (hc i)) (fun z hz ↦ hz.2)
  choose ε hεpos hεsub using hε
  have hcommon : ∃ r > 0, ∀ i, r ≤ ε i := by
    by_cases hι : Nonempty ι
    · let : Nonempty ι := hι
      obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ ε Finset.univ_nonempty
      exact ⟨ε i, hεpos i, fun j ↦ hi j (Finset.mem_univ _)⟩
    · exact ⟨1, zero_lt_one, fun i ↦ (hι ⟨i⟩).elim⟩
  obtain ⟨r, hr, hrε⟩ := hcommon
  let δ := min r (ψ / 8)
  have hδ : 0 < δ := lt_min hr (div_pos hψ.1 (by norm_num))
  have hδψ : δ < ψ / 4 := (min_le_right _ _).trans_lt (by linarith [hψ.1])
  refine ⟨ψ, hψ, δ, ⟨hδ, hδψ⟩, hsep, ?_⟩
  have hnear : ∀ᶠ k in atTop, x k ∈ Metric.thickening δ S := by
    by_contra! hbad
    let K := Ω ∩ (Metric.thickening δ S)ᶜ
    have hK : IsCompact K := hΩ.inter_right Metric.isOpen_thickening.isClosed_compl
    have hfreq : ∃ᶠ k in atTop, x k ∈ K := hbad.mono fun k hk ↦ ⟨hx k, hk⟩
    obtain ⟨z, hz, j, hj, ht⟩ := hK.tendsto_subseq' hfreq
    exact hz.2 (Metric.mem_thickening_iff.mpr
      ⟨z, hlimit z j hj ht, by simpa using hδ⟩)
  filter_upwards [hnear] with k hk
  obtain ⟨z, hz, hdist⟩ := Metric.mem_thickening_iff.mp hk
  let K := connectedComponentIn S z
  have hK : IsCompact K := by
    rw [show K = _ from connectedComponentIn_eq_image hz]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hzK : z ∈ K := mem_connectedComponentIn hz
  have hKS : K ⊆ S := connectedComponentIn_subset S z
  have hKconn : IsConnected K := isConnected_connectedComponentIn_iff.mpr hz
  obtain ⟨A, hA⟩ := lemma_12_3_1 hKconn hc hn hg
    (fun w hw ↦ hind w (hKS hw)) (fun w hw ↦ hmul w (hKS hw))
  refine ⟨z, hz, hK, Metric.mem_cthickening_of_dist_le _ _ _ _ hzK hdist.le, ?_⟩
  intro y hy i hi
  by_contra hnot
  have hKT : K ⊆ T i := by
    intro w hw
    refine ⟨hKS hw, ?_⟩
    change i ∉ activeConstraintSet c w
    rwa [hA w hw, ← hA z hzK]
  have hye : y ∈ Metric.cthickening (ε i) (T i) :=
    Metric.cthickening_mono ((min_le_left _ _).trans (hrε i)) (T i)
      (Metric.cthickening_subset_of_subset δ hKT hy)
  exact hεsub i hye hi

open Optimization in
/-- The relaxed comparison (12.3.15)–(12.3.16). The endpoint feasible
after dropping a constraint can be compared with criticality on the
relaxed set. Moving the base point also shifts the displacement. -/
theorem relaxedCriticality_lower_bound_of_nearby [CompleteSpace E]
    {R : Set E} {f : E → ℝ} {x z d : E}
    (hd : z + d ∈ R) (hdnorm : ‖d‖ ≤ 1 / 2) (hxz : ‖z - x‖ ≤ 1 / 2) :
    ⟪-gradient f z, d⟫ - ‖gradient f x - gradient f z‖ * ‖d‖ -
        ‖gradient f x‖ * ‖z - x‖ ≤ criticality R f x 1 := by
  let w := d + (z - x)
  have hw : x + w = z + d := by dsimp [w]; abel
  have hn : ‖w‖ ≤ 1 := (norm_add_le _ _).trans (by linarith)
  have hχ := inner_le_linearDecrease (v := -gradient f x) (hw ▸ hd) hn
  have h₁ := neg_abs_le (⟪gradient f z - gradient f x, d⟫)
  have h₁' := abs_real_inner_le_norm (gradient f z - gradient f x) d
  rw [norm_sub_rev] at h₁'
  have h₂ := neg_abs_le (⟪-gradient f x, z - x⟫)
  have h₂' := abs_real_inner_le_norm (-gradient f x) (z - x)
  rw [norm_neg] at h₂'
  change ⟪-gradient f x, w⟫ ≤ criticality R f x 1 at hχ
  rw [show w = d + (z - x) from rfl, inner_add_right] at hχ
  simp only [inner_sub_left] at h₁ h₁'
  simp only [inner_neg_left] at h₂ h₂' hχ ⊢
  linarith only [h₁, h₁', h₂, h₂', hχ]

open Optimization in
/-- The relaxed criticality bound supported by the comparison in Theorem
12.3.4. The transported trial must be feasible in the set used to compute
criticality, and the linear decrease pays for the translation of the base. -/
theorem theorem_12_3_4_relaxed [CompleteSpace E] {R : Set E} {f : E → ℝ} {x z d : E}
    {ε : ℝ} (hε : ε ≤ 1) (hd : z + d ∈ R) (hdnorm : ‖d‖ ≤ 1 / 2)
    (hxz : ‖z - x‖ ≤ 1 / 2)
    (hgap : 2 * ε ≤ ⟪-gradient f z, d⟫)
    (hgrad : ‖gradient f x - gradient f z‖ ≤ ε)
    (htranslate : ‖gradient f x‖ * ‖z - x‖ ≤ ε / 2) :
    ε ≤ cappedCriticality R f x := by
  have hterm : ‖gradient f x - gradient f z‖ * ‖d‖ ≤ ε / 2 :=
    (mul_le_mul_of_nonneg_left hdnorm (norm_nonneg _)).trans (by linarith)
  have hb := relaxedCriticality_lower_bound_of_nearby (f := f) hd hdnorm hxz
  have hχ : ε ≤ criticality R f x 1 := by linarith
  exact le_min hε hχ

open Optimization in
/-- Missing an active constraint at a generalized Cauchy trial does not
itself bound the full feasible criticality away from zero. On the
nonnegative half-line the radius-boundary Cauchy trial is strictly
positive while both the base point and criticality can tend to zero.
This example concerns the local comparison, without a radius-update run. -/
theorem missing_active_local_criticality_counterexample
    (P : GeneralizedCauchyParams) {x : ℝ} (hx : 0 < x) (hx₁ : x ≤ 1) :
    IsApproxGeneralizedCauchyPoint P (Set.Ici (0 : ℝ)) id id x (x / 2) (x / 2) ∧
      activeConstraintSet (fun _ : Unit ↦ id) 0 ≠
        activeConstraintSet (fun _ : Unit ↦ id) (x / 2) ∧
      cappedCriticality (Set.Ici (0 : ℝ)) id x = x := by
  let C := Set.Ici (0 : ℝ)
  have hg : gradient (id : ℝ → ℝ) x = 1 := by rw [gradient_eq_deriv', deriv_id]
  have hhalf : 0 < x / 2 := half_pos hx
  have hdiff : ‖x / 2 - x‖ = x / 2 := by
    rw [Real.norm_eq_abs, abs_of_neg (by linarith : x / 2 - x < 0)]
    ring
  have hpath : projectedGradientPath C id x (x / 2) = x / 2 := by
    unfold projectedGradientPath
    change bestApprox C (x + (x / 2) • (-gradient (id : ℝ → ℝ) x)) = x / 2
    rw [hg, smul_eq_mul, show x + x / 2 * (-1) = x / 2 by ring]
    exact (bestApprox_eq_iff ⟨0, by simp⟩ isClosed_Ici (convex_Ici _)).mpr
      ⟨hhalf.le, by simp⟩
  refine ⟨⟨x / 2, hhalf, hpath.symm, hdiff.le, ?_, Or.inl ?_⟩, ?_, ?_⟩
  · simp only [id_eq, hg, Real.inner_apply, one_mul]
    have h := mul_nonneg (sub_nonneg.mpr (P.slope_order.trans P.lower_lt_one).le) hhalf.le
    nlinarith only [h]
  · rw [hdiff]
    exact mul_le_of_le_one_left hhalf.le P.fraction_lt_one.le
  · intro he
    have h0 : () ∈ activeConstraintSet (fun _ : Unit ↦ id) (0 : ℝ) := rfl
    have hn := he ▸ h0
    exact hhalf.ne' hn
  · have hχ : criticality C id x 1 = x := by
      unfold criticality
      rw [hg]
      apply le_antisymm
      · apply linearDecrease_le (show x ∈ C from hx.le) zero_le_one
        intro d hd _
        change 0 ≤ x + d at hd
        simp only [Real.inner_apply]
        linarith only [hd]
      · have hnorm : ‖-x‖ ≤ (1 : ℝ) := by
          simpa only [norm_neg, Real.norm_eq_abs, abs_of_pos hx] using hx₁
        have h := inner_le_linearDecrease (v := (-1 : ℝ))
          (show x + -x ∈ C by simp [C]) hnorm
        simpa only [Real.inner_apply, neg_mul_neg, one_mul, neg_mul, mul_neg, mul_one,
          neg_neg] using h
    rw [cappedCriticality, hχ, min_eq_right hx₁]

open ConnGouldToint.Chapter06 in
/-- Lemma 12.3.5. The small-radius acceptance estimate with the capped
criticality measure and the model decrease condition AA.1b. -/
theorem lemma_12_3_5 [CompleteSpace E] {P : BTRParams} {C : Set E}
    {f m : E → ℝ} {x s : E} {β Δ Δ' κ B : ℝ}
    (hβ : 0 < β) (hβB : β ≤ B) (hΔ : 0 < Δ)
    (hπ : 0 < cappedCriticality C f x) (hκ : 0 < κ) (hκ' : κ < 1)
    (hval : f x = m x)
    (hdec : κ * cappedCriticality C f x * min (cappedCriticality C f x / β) Δ ≤
      m x - m (x + s))
    (herr : |f (x + s) - m (x + s)| ≤ B * Δ ^ 2)
    (hsmall : Δ ≤ κ * cappedCriticality C f x * (1 - P.η₂) / B)
    (hupdate : BTRRadiusUpdate P (btrRatio f m x s) Δ Δ') :
    P.η₂ ≤ btrRatio f m x s ∧ Δ ≤ Δ' := by
  have hsuccess := btrRatio_ge_eta₂_of_small_radius_of_decrease
    hβ hβB hΔ hπ hκ hκ' hval hdec herr hsmall
  exact ⟨hsuccess, hupdate.very_successful hsuccess⟩

open Optimization ConvexAnalysis in
/-- Lemma 12.3.6. For an already reindexed subsequence, the projected gradients
tend to zero when the nearby feasible points have the component's active set.
The outward normals generate supporting directions at those feasible points. -/
private theorem projectedGradient_tendsto_zero_of_eventually_active [Fintype ι] [CompleteSpace E]
    {C K S : Set E}
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    {x u : ℕ → E} {A : Set ι}
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K)
    (hlim : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hclose : Tendsto (fun k ↦ u k - x k) atTop (𝓝 0))
    (hu : ∀ k, u k ∈ C) (hAu : ∀ᶠ k in atTop, activeConstraintSet c (u k) = A)
    (hAS : ∀ z ∈ S, activeConstraintSet c z = A)
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c n g z)
    (hg : Continuous g) (hn : ∀ i, Continuous (n i))
    (hnormal : ∀ y ∈ C, ∀ i ∈ activeConstraintSet c y, -n i y ∈ normalDirections C y) :
    Tendsto (fun k ↦ bestApprox (tangentDirections C (u k)) (-g (x k))) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_contra! hbad
  obtain ⟨j, hj, hjbad⟩ := extraction_of_frequently_atTop hbad
  obtain ⟨z, _, i, hi, hzi⟩ := hK.isSeqCompact (fun k ↦ hx (j k))
  let q := j ∘ i
  have hq : StrictMono q := hj.comp hi
  have hxq : Tendsto (x ∘ q) atTop (𝓝 z) := hzi
  have hz := hlim z q hq hxq
  obtain ⟨μ, hμ, hpos, hzero⟩ := hstat z hz
  have huq : Tendsto (u ∘ q) atTop (𝓝 z) := by
    change Tendsto (fun k ↦ u (q k)) atTop (𝓝 z)
    simpa only [Function.comp_apply, sub_add_cancel, zero_add] using
      (hclose.comp hq.tendsto_atTop).add hxq
  let w (y : E) := ∑ a, μ a • (-n a y)
  have hw : Continuous w := continuous_finsetSum _ fun a _ ↦
    continuous_const.smul (hn a).neg
  have hwz : w z = -g z := by
    simp only [w, smul_neg, Finset.sum_neg_distrib, ← hμ]
  have hwmem (k : ℕ) (hk : activeConstraintSet c (u (q k)) = A) :
      w (u (q k)) ∈ normalDirections C (u (q k)) := by
    apply mem_normalDirections.mpr
    intro y hy
    change ⟪∑ a, μ a • (-n a (u (q k))), y - u (q k)⟫ ≤ 0
    rw [sum_inner]
    apply Finset.sum_nonpos
    intro a _
    rw [real_inner_smul_left]
    by_cases ha : a ∈ activeConstraintSet c z
    · have hau : a ∈ activeConstraintSet c (u (q k)) := by
        rwa [hk, ← hAS z hz]
      exact mul_nonpos_of_nonneg_of_nonpos (hpos a ha).le
        (mem_normalDirections.mp (hnormal _ (hu _) a hau) y hy)
    · rw [hzero a ha, zero_mul]
  have hbound (k : ℕ) (hk : activeConstraintSet c (u (q k)) = A) :
      ‖bestApprox (tangentDirections C (u (q k))) (-g (x (q k)))‖ ≤
        ‖-g (x (q k)) - w (u (q k))‖ := by
    let T := tangentDirections C (u (q k))
    have hTzero : (0 : E) ∈ T := by simp [T, tangentDirections, mem_polarCone]
    have hTclosed : IsClosed T := isClosed_polarCone
    have hTconvex : Convex ℝ T := convex_polarCone _ _
    have hproj : bestApprox T (w (u (q k))) = 0 := by
      apply (bestApprox_eq_iff ⟨0, hTzero⟩ hTclosed hTconvex).2
      refine ⟨hTzero, fun y hy ↦ ?_⟩
      simpa only [sub_zero, innerₗ_apply_apply] using (mem_polarCone.mp hy) _ (hwmem k hk)
    simpa only [hproj, sub_zero] using
      norm_bestApprox_sub_bestApprox_le ⟨0, hTzero⟩ hTclosed hTconvex
        (-g (x (q k))) (w (u (q k)))
  have hgq : Tendsto (fun k ↦ g (x (q k))) atTop (𝓝 (g z)) :=
    hg.continuousAt.tendsto.comp hxq
  have hwq : Tendsto (fun k ↦ w (u (q k))) atTop (𝓝 (w z)) :=
    hw.continuousAt.tendsto.comp huq
  have ht : Tendsto (fun k ↦ ‖-g (x (q k)) - w (u (q k))‖) atTop (𝓝 0) := by
    simpa only [hwz, sub_self, norm_zero] using (hgq.neg.sub hwq).norm
  have he := ht.eventually (gt_mem_nhds hε)
  obtain ⟨k, hk, hak⟩ := (he.and (hq.tendsto_atTop.eventually hAu)).exists
  exact (not_lt_of_ge (hjbad (i k))) (by
    rw [dist_zero_right]
    exact (hbound k hak).trans_lt hk)

open Optimization ConvexAnalysis in
/-- Lemma 12.3.6. For an already reindexed subsequence, the projected gradients
tend to zero when the nearby feasible points have the component's active set.
The outward normals generate supporting directions at those feasible points. -/
theorem lemma_12_3_6 [Fintype ι] [CompleteSpace E] {C K S : Set E}
    {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    {x u : ℕ → E} {A : Set ι}
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K)
    (hlim : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hclose : Tendsto (fun k ↦ u k - x k) atTop (𝓝 0))
    (hu : ∀ k, u k ∈ C) (hAu : ∀ k, activeConstraintSet c (u k) = A)
    (hAS : ∀ z ∈ S, activeConstraintSet c z = A)
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c n g z)
    (hg : Continuous g) (hn : ∀ i, Continuous (n i))
    (hnormal : ∀ y ∈ C, ∀ i ∈ activeConstraintSet c y, -n i y ∈ normalDirections C y) :
    Tendsto (fun k ↦ bestApprox (tangentDirections C (u k)) (-g (x k))) atTop (𝓝 0) :=
  projectedGradient_tendsto_zero_of_eventually_active hK hx hlim hclose hu
    (Eventually.of_forall hAu) hAS hstat hg hn hnormal

open Optimization ConvexAnalysis in
/-- Corollary 12.3.9 on a component with an eventually identified active set. -/
theorem corollary_12_3_9_of_eventually_active [Fintype ι] [CompleteSpace E]
    {C K S : Set E} {c : ι → E → ℝ} {n : ι → E → E} {g : E → E}
    {x : ℕ → E} {A : Set ι}
    (hK : IsCompact K) (hx : ∀ k, x k ∈ K)
    (hlim : ∀ z (j : ℕ → ℕ), StrictMono j → Tendsto (x ∘ j) atTop (𝓝 z) → z ∈ S)
    (hfeas : ∀ k, x k ∈ C) (hA : ∀ᶠ k in atTop, activeConstraintSet c (x k) = A)
    (hAS : ∀ z ∈ S, activeConstraintSet c z = A)
    (hstat : ∀ z ∈ S, HasStrictActiveMultipliers c n g z)
    (hg : Continuous g) (hn : ∀ i, Continuous (n i))
    (hnormal : ∀ y ∈ C, ∀ i ∈ activeConstraintSet c y, -n i y ∈ normalDirections C y) :
    Tendsto (fun k ↦ bestApprox (tangentDirections C (x k)) (-g (x k))) atTop (𝓝 0) := by
  apply projectedGradient_tendsto_zero_of_eventually_active hK hx hlim _ hfeas
    hA hAS hstat hg hn hnormal
  simpa only [sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : E)) atTop (𝓝 0))

end ConnGouldToint.Chapter12
