import Numlib.Optimization.EpigraphPenalty
import NumlibSurface.ConnGouldToint.Chapter11.Section02
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Order.Filter.Extr
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-! # Composite nonsmooth equations -/

open Filter Topology

namespace ConnGouldToint.Chapter16

/-- The exact merit function (16.2.23) for the composite objective `h ∘ c`. -/
def epigraphMerit {X Y : Type*} (c : X → Y) (h : Y → ℝ)
    (x : X) (σ t : ℝ) : ℝ :=
  Numlib.Optimization.epigraphPenalty (h (c x)) σ t

/-- Lemma 16.2.3. The minimum merit value over the epigraph variable is `h (c x)`,
and the set of minimizers is the singleton with that same value. -/
theorem lemma_16_2_3 {X Y : Type*} (c : X → Y) (h : Y → ℝ)
    (x : X) {σ : ℝ} (hσ : 1 < σ) :
    IsLeast (Set.range (epigraphMerit c h x σ)) (h (c x)) ∧
      {t | IsMinOn (epigraphMerit c h x σ) Set.univ t} = {h (c x)} := by
  have htight : epigraphMerit c h x σ (h (c x)) = h (c x) :=
    (Numlib.Optimization.epigraphPenalty_eq_iff hσ).2 rfl
  have hbound (t : ℝ) : h (c x) ≤ epigraphMerit c h x σ t :=
    Numlib.Optimization.le_epigraphPenalty hσ.le
  refine ⟨⟨⟨h (c x), htight⟩, ?_⟩, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hbound t
  · ext t
    change IsMinOn (epigraphMerit c h x σ) Set.univ t ↔ t = h (c x)
    constructor
    · intro hmin
      have hle := isMinOn_univ_iff.mp hmin (h (c x))
      rw [htight] at hle
      exact (Numlib.Optimization.epigraphPenalty_eq_iff hσ).1 (le_antisymm hle (hbound t))
    · rintro rfl
      apply isMinOn_univ_iff.mpr
      intro y
      rw [htight]
      exact hbound y

section EpigraphConditions

variable {E Y ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype ι]

/-- The affine contribution (16.2.2) to the polyhedral maximum. -/
def affineResidualBranch (p : Y →L[ℝ] ℝ) (b : ℝ) (y : Y) : ℝ := p y + b

/-- The polyhedral maximum (16.2.1) of the affine contributions. -/
noncomputable def polyhedralAffineMaximum [Nonempty ι]
    (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ) (y : Y) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ↦ affineResidualBranch (p i) (b i) y)

/-- The polyhedral residual objective (16.2.3). -/
noncomputable def polyhedralResidualValue [Nonempty ι] (c : E → Y)
    (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ) (x : E) : ℝ :=
  polyhedralAffineMaximum p b (c x)

/-- The composite trust-region model (16.2.4). -/
noncomputable def polyhedralResidualModel [Nonempty ι] (c : E → Y)
    (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ) (x s : E) : ℝ :=
  H s s / 2 + polyhedralAffineMaximum p b (c x + fderiv ℝ c x s)

/-- The trust-region model problem (16.2.5). -/
def IsPolyhedralModelSolution [Nonempty ι] (c : E → Y)
    (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ)
    (x : E) (Δ : ℝ) (s : E) : Prop :=
  s ∈ Metric.closedBall 0 Δ ∧ IsMinOn (polyhedralResidualModel c p b H x) (Metric.closedBall 0 Δ) s

/-- The constraints of the epigraph problem (16.2.9). -/
def polyhedralEpigraphFeasible (c : E → Y) (p : ι → Y →L[ℝ] ℝ)
    (b : ι → ℝ) : Set (E × ℝ) :=
  {w | ∀ i, affineResidualBranch (p i) (b i) (c w.1) ≤ w.2}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The epigraph is the set of feasible pairs whose height is at least the
polyhedral residual value. -/
theorem mem_polyhedralEpigraphFeasible [Nonempty ι] {c : E → Y}
    {p : ι → Y →L[ℝ] ℝ} {b : ι → ℝ} {w : E × ℝ} :
    w ∈ polyhedralEpigraphFeasible c p b ↔ polyhedralResidualValue c p b w.1 ≤ w.2 := by
  change (∀ i, affineResidualBranch (p i) (b i) (c w.1) ≤ w.2) ↔
    Finset.univ.sup' Finset.univ_nonempty
      (fun i ↦ affineResidualBranch (p i) (b i) (c w.1)) ≤ w.2
  simp only [Finset.sup'_le_iff, Finset.mem_univ, true_implies]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The epigraph problem (16.2.9) and the composite problem (16.2.10) have
the same minimizing points once the epigraph height is eliminated. -/
theorem isMinOn_polyhedralEpigraph_iff [Nonempty ι] {c : E → Y}
    {p : ι → Y →L[ℝ] ℝ} {b : ι → ℝ} {x : E} {t : ℝ} :
    ((x, t) ∈ polyhedralEpigraphFeasible c p b ∧
      IsMinOn Prod.snd (polyhedralEpigraphFeasible c p b) (x, t)) ↔
    t = polyhedralResidualValue c p b x ∧
      IsMinOn (polyhedralResidualValue c p b) Set.univ x := by
  have hfeas (y : E) :
      (y, polyhedralResidualValue c p b y) ∈ polyhedralEpigraphFeasible c p b :=
    mem_polyhedralEpigraphFeasible.2 le_rfl
  constructor
  · rintro ⟨hf, hm⟩
    have ht : t = polyhedralResidualValue c p b x := le_antisymm ((isMinOn_iff.1 hm) _ (hfeas x))
      (mem_polyhedralEpigraphFeasible.1 hf)
    refine ⟨ht, isMinOn_univ_iff.2 fun y ↦ ?_⟩
    simpa only [ht] using ((isMinOn_iff.1 hm) _ (hfeas y) : t ≤ polyhedralResidualValue c p b y)
  · rintro ⟨rfl, hm⟩
    exact ⟨hfeas x, isMinOn_iff.2 fun w hw ↦
      ((isMinOn_univ_iff.1 hm) w.1).trans (mem_polyhedralEpigraphFeasible.1 hw)⟩

/-- Equations (16.2.11)–(16.2.14) in a finite branch representation.
Here `a i` is the value of the `i`th branch, `A i` its derivative,
and `t` the epigraph height. -/
structure EpigraphMultiplier (a : ι → ℝ) (A : ι → E →L[ℝ] ℝ)
    (t : ℝ) (θ : ι → ℝ) : Prop where
  feasible : ∀ i, a i ≤ t
  nonneg : ∀ i, 0 ≤ θ i
  complementary : ∀ i, θ i * (t - a i) = 0
  sum_eq_one : ∑ i, θ i = 1
  stationary : ∑ i, θ i • A i = 0

/-- The epigraph critical cone in the proof of Theorem 16.2.2. -/
def epigraphCriticalCone (a : ι → ℝ) (A : ι → E →L[ℝ] ℝ)
    (t : ℝ) (θ : ι → ℝ) : Set (E × ℝ) :=
  {v | (∀ i, a i = t → A i v.1 ≤ v.2) ∧
    ∀ i, a i = t → 0 < θ i → A i v.1 = v.2}

private theorem EpigraphMultiplier.eq_height_of_pos {a : ι → ℝ} {A : ι → E →L[ℝ] ℝ}
    {t : ℝ} {θ : ι → ℝ} (h : EpigraphMultiplier a A t θ) {i : ι} (hi : 0 < θ i) :
    a i = t := by
  have hz := (mul_eq_zero.1 (h.complementary i)).resolve_left hi.ne'
  exact (sub_eq_zero.1 hz).symm

private theorem EpigraphMultiplier.sum_apply_eq_zero {a : ι → ℝ} {A : ι → E →L[ℝ] ℝ}
    {t : ℝ} {θ : ι → ℝ} (h : EpigraphMultiplier a A t θ) (d : E) :
    ∑ i, θ i * A i d = 0 := by
  have hs := congrArg (fun f : E →L[ℝ] ℝ ↦ f d) h.stationary
  simpa only [sum_apply, smul_apply, smul_eq_mul, zero_apply] using hs

/-- The epigraph cone projects onto the directions with nonpositive active
branch derivatives. Its height component vanishes at a stationary point. -/
theorem mem_epigraphCriticalCone_iff {a : ι → ℝ} {A : ι → E →L[ℝ] ℝ}
    {t : ℝ} {θ : ι → ℝ} (h : EpigraphMultiplier a A t θ) {d : E} {u : ℝ} :
    (d, u) ∈ epigraphCriticalCone a A t θ ↔ u = 0 ∧ ∀ i, a i = t → A i d ≤ 0 := by
  have hstat := h.sum_apply_eq_zero d
  constructor
  · rintro ⟨hactive, hpos⟩
    have heq : ∑ i, θ i * A i d = ∑ i, θ i * u := by
      apply Finset.sum_congr rfl
      intro i _
      rcases eq_or_lt_of_le (h.nonneg i) with hi | hi
      · simp [← hi]
      · rw [hpos i (h.eq_height_of_pos hi) hi]
    rw [← Finset.sum_mul, h.sum_eq_one, one_mul, hstat] at heq
    exact ⟨heq.symm, fun i hi ↦ heq ▸ hactive i hi⟩
  · rintro ⟨rfl, hactive⟩
    have hnonpos (i : ι) (_ : i ∈ Finset.univ) : θ i * A i d ≤ 0 := by
      rcases eq_or_lt_of_le (h.nonneg i) with hi | hi
      · simp [← hi]
      · exact mul_nonpos_of_nonneg_of_nonpos hi.le (hactive i (h.eq_height_of_pos hi))
    refine ⟨hactive, fun i _ hi ↦ ?_⟩
    exact (mul_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonpos hnonpos).1 hstat i
      (Finset.mem_univ i))).resolve_left hi.ne'

/-- Theorem 16.2.2, in active-branch coordinates. The epigraph Lagrangian
and the composite condition have the same weighted branch Hessian.
A stationary convex combination of the active branches has directional
derivative zero, so the maximum over those branches is zero exactly when
all active derivatives are nonpositive. -/
theorem epigraphSecondOrder_iff_activeBranch {a : ι → ℝ} {A : ι → E →L[ℝ] ℝ}
    {t : ℝ} {θ : ι → ℝ} (h : EpigraphMultiplier a A t θ)
    (H : ι → E →L[ℝ] E →L[ℝ] ℝ) :
    (∀ v ∈ epigraphCriticalCone a A t θ, v ≠ 0 →
      0 < ∑ i, θ i * H i v.1 v.1) ↔
    (∀ d : E, ‖d‖ = 1 → (∀ i, a i = t → A i d ≤ 0) →
      0 < ∑ i, θ i * H i d d) := by
  constructor
  · intro hpos d hd hactive
    apply hpos (d, 0) ((mem_epigraphCriticalCone_iff h).2 ⟨rfl, hactive⟩)
    intro hz
    have hdz : d = 0 := congrArg Prod.fst hz
    simp [hdz] at hd
  · intro hpos v hv hn
    obtain ⟨d, u⟩ := v
    obtain ⟨rfl, hactive⟩ := (mem_epigraphCriticalCone_iff h).1 hv
    have hd : d ≠ 0 := by
      intro hz
      exact hn (by simp [hz])
    let r := ‖d‖⁻¹
    have hr : 0 < r := inv_pos.2 (norm_pos_iff.2 hd)
    have hunit : ‖r • d‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hd)
    have hact i (hi : a i = t) : A i (r • d) ≤ 0 := by
      simpa only [map_smul, smul_eq_mul] using
        mul_nonpos_of_nonneg_of_nonpos hr.le (hactive i hi)
    have hscale (i : ι) : θ i * H i (r • d) (r • d) = r ^ 2 * (θ i * H i d d) := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    have hp := hpos (r • d) hunit hact
    simp only [hscale, ← Finset.mul_sum] at hp
    exact pos_of_mul_pos_right hp (sq_nonneg r)

/-- The active-branch convex combination used in (16.2.16)–(16.2.18),
which represents an element of the subdifferential of the affine maximum. -/
def IsActiveBranchCombination (a : ι → ℝ) (p : ι → Y →L[ℝ] ℝ)
    (t : ℝ) (y : Y →L[ℝ] ℝ) : Prop :=
  ∃ θ : ι → ℝ, (∀ i, 0 ≤ θ i) ∧ ∑ i, θ i = 1 ∧
    (∀ i, a i ≠ t → θ i = 0) ∧ y = ∑ i, θ i • p i

private theorem activeBranchCombination_self {a : ι → ℝ} {p : ι → Y →L[ℝ] ℝ}
    {t : ℝ} {i : ι} (hi : a i = t) : IsActiveBranchCombination a p t (p i) := by
  classical
  refine ⟨fun j ↦ if j = i then 1 else 0, ?_, by simp, ?_, ?_⟩
  · intro j
    by_cases hji : j = i <;> simp [hji]
  · intro j hj
    have hji : j ≠ i := fun e ↦ hj (e ▸ hi)
    simp [hji]
  · simp [ite_smul]

/-- The multiplier representation (16.2.16)–(16.2.18) is equivalent to
membership in the convex hull of the active slopes. -/
theorem isActiveBranchCombination_iff_mem_convexHull {a : ι → ℝ}
    {p : ι → Y →L[ℝ] ℝ} {t : ℝ} {y : Y →L[ℝ] ℝ} :
    IsActiveBranchCombination a p t y ↔
      y ∈ convexHull ℝ {q | ∃ i, a i = t ∧ p i = q} := by
  classical
  let S : Set (Y →L[ℝ] ℝ) := {q | ∃ i, a i = t ∧ p i = q}
  constructor
  · rintro ⟨θ, hn, hs, hzero, rfl⟩
    have hfilter (w : ι → ℝ) (hz : ∀ i, a i ≠ t → w i = 0) :
        ∑ i ∈ Finset.univ.filter (fun i ↦ a i = t), w i = ∑ i, w i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : a i = t <;> simp [hi, hz]
    have hf : ∑ i ∈ Finset.univ.filter (fun i ↦ a i = t), θ i • p i =
        ∑ i, θ i • p i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : a i = t <;> simp [hi, hzero]
    rw [← hf]
    exact (convex_convexHull ℝ S).sum_mem (fun i _ ↦ hn i)
      ((hfilter θ hzero).trans hs) (fun i hi ↦
        subset_convexHull ℝ S ⟨i, (Finset.mem_filter.1 hi).2, rfl⟩)
  · have hsub : S ⊆ {q | IsActiveBranchCombination a p t q} := by
      rintro _ ⟨i, hi, rfl⟩
      exact activeBranchCombination_self hi
    apply convexHull_min hsub _ (a := y)
    intro u hu v hv α β hα hβ hsum
    rcases hu with ⟨θ, hn, hs, hz, rfl⟩
    rcases hv with ⟨η, en, es, ez, rfl⟩
    refine ⟨fun i ↦ α * θ i + β * η i, fun i ↦ add_nonneg (mul_nonneg hα (hn i)) (mul_nonneg hβ (en i)), ?_, ?_, ?_⟩
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hs, es, mul_one, hsum]
    · intro i hi
      simp [hz i hi, ez i hi]
    · simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

private theorem activeBranchCombination_le_iff {a : ι → ℝ} {p : ι → Y →L[ℝ] ℝ}
    {t : ℝ} {v : Y} :
    (∀ y : Y →L[ℝ] ℝ, IsActiveBranchCombination a p t y → y v ≤ 0) ↔
      ∀ i, a i = t → p i v ≤ 0 := by
  classical
  constructor
  · intro h i hi
    exact h (p i) (activeBranchCombination_self hi)
  · rintro h y ⟨θ, hn, _, hs, rfl⟩
    simp only [sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_nonpos
    intro i _
    by_cases hi : a i = t
    · exact mul_nonpos_of_nonneg_of_nonpos (hn i) (h i hi)
    · rw [hs i hi, zero_mul]

private theorem EpigraphMultiplier.height_eq_sup [Nonempty ι] {a : ι → ℝ}
    {A : ι → E →L[ℝ] ℝ} {t : ℝ} {θ : ι → ℝ} (h : EpigraphMultiplier a A t θ) :
    t = Finset.univ.sup' Finset.univ_nonempty a := by
  apply le_antisymm _ (Finset.sup'_le _ _ fun i _ ↦ h.feasible i)
  obtain ⟨i, hi, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h.sum_eq_one.trans_ne one_ne_zero)
  rw [← h.eq_height_of_pos (lt_of_le_of_ne (h.nonneg i) hn.symm)]
  exact Finset.le_sup' _ hi

/-- Derivative of an affine branch composed with the residual map. -/
theorem fderiv_affineResidualBranch {c : E → Y} {x : E}
    (hc : DifferentiableAt ℝ c x) (p : Y →L[ℝ] ℝ) (b : ℝ) :
    fderiv ℝ (fun z ↦ p (c z) + b) x = p.comp (fderiv ℝ c x) :=
  ((p.hasFDerivAt.comp x hc.hasFDerivAt).add_const b).fderiv

/-- The second variation of an affine branch is the residual's second
variation evaluated against its slope. -/
theorem fderiv_fderiv_affineResidualBranch {c : E → Y} {x : E}
    (hc : ContDiffAt ℝ 2 c x) (p : Y →L[ℝ] ℝ) (b : ℝ) (d e : E) :
    fderiv ℝ (fderiv ℝ (fun z ↦ p (c z) + b)) x d e =
      p (fderiv ℝ (fderiv ℝ c) x d e) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ c) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun z ↦ p (c z) + b) =ᶠ[𝓝 x]
      fun z ↦ p.comp (fderiv ℝ c z) :=
    (hc.eventually (by norm_num)).mono fun _ hy ↦
      fderiv_affineResidualBranch (hy.differentiableAt (by norm_num)) p b
  rw [heq.fderiv_eq]
  change fderiv ℝ (((ContinuousLinearMap.compL ℝ E Y ℝ) p) ∘ fderiv ℝ c) x d e = _
  rw [(((ContinuousLinearMap.compL ℝ E Y ℝ) p).hasFDerivAt.comp x hd.hasFDerivAt).fderiv]
  rfl

/-- The Lagrangian of the epigraph problem with nonnegative inequality
multipliers for the constraints `pᵢ(c(x)) + bᵢ - t ≤ 0`. -/
def polyhedralEpigraphLagrangian (c : E → Y) (p : ι → Y →L[ℝ] ℝ)
    (b θ : ι → ℝ) (w : E × ℝ) : ℝ :=
  w.2 + ∑ i, θ i * (affineResidualBranch (p i) (b i) (c w.1) - w.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem polyhedralEpigraphLagrangian_eq_of_sum_eq_one
    (c : E → Y) (p : ι → Y →L[ℝ] ℝ) (b θ : ι → ℝ) (hθ : ∑ i, θ i = 1) :
    polyhedralEpigraphLagrangian c p b θ =
      fun w ↦ (∑ i, θ i • p i) (c w.1) + ∑ i, θ i * b i := by
  funext w
  simp only [polyhedralEpigraphLagrangian, affineResidualBranch, sum_apply, smul_apply,
    smul_eq_mul, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, hθ, one_mul]
  ring

/-- The epigraph Lagrangian's second variation (16.2.15). The residual
Hessian is evaluated against the convex combination of the slopes,
independently of the number of affine branches. -/
theorem fderiv_fderiv_polyhedralEpigraphLagrangian
    {c : E → Y} {x : E} (hc : ContDiffAt ℝ 2 c x) (p : ι → Y →L[ℝ] ℝ)
    (b θ : ι → ℝ) (hθ : ∑ i, θ i = 1) (t : ℝ) (v w : E × ℝ) :
    fderiv ℝ (fderiv ℝ (polyhedralEpigraphLagrangian c p b θ)) (x, t) v w =
      ∑ i, θ i * p i (fderiv ℝ (fderiv ℝ c) x v.1 w.1) := by
  rw [polyhedralEpigraphLagrangian_eq_of_sum_eq_one c p b θ hθ]
  let F : E × ℝ →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ
  have hc' : ContDiffAt ℝ 2 (fun z : E × ℝ ↦ c z.1) (x, t) :=
    hc.comp (x, t) F.contDiff.contDiffAt
  rw [fderiv_fderiv_affineResidualBranch hc']
  suffices h : fderiv ℝ (fderiv ℝ (fun z : E × ℝ ↦ c z.1)) (x, t) v w =
      fderiv ℝ (fderiv ℝ c) x v.1 w.1 by
    simp only [h, sum_apply, smul_apply, smul_eq_mul]
  let L := (ContinuousLinearMap.compL ℝ (E × ℝ) E Y).flip F
  have hd : DifferentiableAt ℝ (fderiv ℝ c) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun z : E × ℝ ↦ c z.1) =ᶠ[𝓝 (x, t)]
      fun z ↦ L (fderiv ℝ c z.1) := by
    have he := (F.continuous.tendsto (x, t)).eventually (hc.eventually (by norm_num))
    filter_upwards [he] with z hz
    exact (hz.differentiableAt (by norm_num)).hasFDerivAt.comp z F.hasFDerivAt |>.fderiv
  rw [heq.fderiv_eq]
  exact congrArg (fun f : (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] Y ↦ f v w)
    (L.hasFDerivAt.comp (x, t) (hd.hasFDerivAt.comp (x, t) F.hasFDerivAt)).fderiv

/-- Theorem 16.2.2 for an affine maximum composed with a residual map.
The left side uses the epigraph height and its KKT multipliers. The right
side uses a subgradient represented by active affine slopes and restricts
the residual Hessian to unit directions with zero support value. Stationarity
supplies a subgradient attaining zero on every direction in this test. -/
theorem theorem_16_2_2 [Nonempty ι] (c : E → Y) (p : ι → Y →L[ℝ] ℝ)
    (b : ι → ℝ) (x : E) :
    let a i := p i (c x) + b i
    let A i := (p i).comp (fderiv ℝ c x)
    let H := fderiv ℝ (fderiv ℝ c) x
    let height := polyhedralResidualValue c p b x
    (∃ t θ, EpigraphMultiplier a A t θ ∧
      ∀ v ∈ epigraphCriticalCone a A t θ, v ≠ 0 →
        0 < ∑ i, θ i * p i (H v.1 v.1)) ↔
    (∃ y : Y →L[ℝ] ℝ, IsActiveBranchCombination a p height y ∧
      y.comp (fderiv ℝ c x) = 0 ∧ ∀ d : E, ‖d‖ = 1 →
        (∀ z : Y →L[ℝ] ℝ, IsActiveBranchCombination a p height z →
          z (fderiv ℝ c x d) ≤ 0) → 0 < y (H d d)) := by
  dsimp only
  let a (i : ι) := p i (c x) + b i
  let A (i : ι) := (p i).comp (fderiv ℝ c x)
  let H := fderiv ℝ (fderiv ℝ c) x
  let height := polyhedralResidualValue c p b x
  let Q (i : ι) := (ContinuousLinearMap.compL ℝ E Y ℝ (p i)).comp H
  have hsum (θ : ι → ℝ) :
      (∑ i, θ i • p i).comp (fderiv ℝ c x) = ∑ i, θ i • A i := by
    ext d
    simp only [A, ContinuousLinearMap.comp_apply, sum_apply, smul_apply]
  have hquad (θ : ι → ℝ) (d : E) :
      (∑ i, θ i • p i) (H d d) = ∑ i, θ i * Q i d d := by
    simp only [Q, sum_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply]
  constructor
  · rintro ⟨t, θ, hθ, hpos⟩
    have ht : t = height := hθ.height_eq_sup
    subst t
    refine ⟨∑ i, θ i • p i, ⟨θ, hθ.nonneg, hθ.sum_eq_one, ?_, rfl⟩, ?_, ?_⟩
    · intro i hi
      exact (mul_eq_zero.1 (hθ.complementary i)).resolve_right (sub_ne_zero.2 hi.symm)
    · rw [hsum]
      exact hθ.stationary
    · intro d hd hz
      rw [hquad]
      exact (epigraphSecondOrder_iff_activeBranch hθ Q).1 hpos d hd
        (activeBranchCombination_le_iff (p := p) (v := fderiv ℝ c x d) |>.1 hz)
  · rintro ⟨_, ⟨θ, hn, hs, hzero, rfl⟩, hstat, hpos⟩
    have hθ : EpigraphMultiplier a A height θ := by
      refine ⟨fun i ↦ Finset.le_sup' a (Finset.mem_univ i), hn, ?_, hs, ?_⟩
      · intro i
        by_cases hi : a i = height
        · rw [hi, sub_self, mul_zero]
        · rw [hzero i hi, zero_mul]
      · rw [← hsum]
        exact hstat
    refine ⟨height, θ, hθ, (epigraphSecondOrder_iff_activeBranch hθ Q).2 ?_⟩
    intro d hd hactive
    rw [← hquad]
    exact hpos d hd (activeBranchCombination_le_iff (p := p) (v := fderiv ℝ c x d) |>.2 hactive)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The maximum of affine branches is globally Lipschitz, with a constant
bounded by the sum of the operator norms of the slopes. -/
theorem lipschitzWith_polyhedralAffineMaximum [Nonempty ι]
    (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ) :
    LipschitzWith (∑ i, ‖p i‖₊) (polyhedralAffineMaximum p b) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  let K : ℝ := ((∑ i, ‖p i‖₊ : NNReal) : ℝ)
  have hK (i : ι) : ‖p i‖ ≤ K := by
    exact_mod_cast (Finset.single_le_sum (f := fun j ↦ ‖p j‖₊)
      (fun _ _ ↦ zero_le) (Finset.mem_univ i))
  have h (u v : Y) : polyhedralAffineMaximum p b u ≤
      polyhedralAffineMaximum p b v + K * dist u v := by
    apply Finset.sup'_le
    intro i hi
    have hv : affineResidualBranch (p i) (b i) v ≤ polyhedralAffineMaximum p b v :=
      Finset.le_sup' (fun j ↦ affineResidualBranch (p j) (b j) v) hi
    have hdiff : p i u - p i v ≤ K * dist u v := by
      rw [← map_sub, dist_eq_norm]
      have hnorm := (p i).le_opNorm (u - v)
      rw [Real.norm_eq_abs] at hnorm
      exact ((le_abs_self _).trans hnorm).trans
        (mul_le_mul_of_nonneg_right (hK i) (norm_nonneg _))
    dsimp [affineResidualBranch] at hv ⊢
    linarith only [hv, hdiff]
  have hzy := h z y
  rw [dist_comm z y] at hzy
  rw [Real.dist_eq]
  change _ ≤ K * dist y z
  exact abs_le.2 ⟨by linarith only [hzy], by linarith only [h y z]⟩

private theorem exists_uniform_firstOrder_of_contDiff {c : E → Y}
    (hc : ContDiff ℝ 1 c) (x : E) {a : ℝ} (ha : 0 < a) :
    ∃ r > 0, ∀ y ∈ Metric.ball x r, ∀ s : E, ‖s‖ ≤ r →
      ‖c (y + s) - c y - fderiv ℝ c y s‖ ≤ a * ‖s‖ := by
  obtain ⟨r, hr, hclose⟩ := Metric.continuousAt_iff.1
    (show ContinuousAt (fderiv ℝ c) x from (hc.continuous_fderiv one_ne_zero).continuousAt) (a / 2) (half_pos ha)
  refine ⟨r / 3, by positivity, ?_⟩
  intro y hy s hs
  have hy' : y ∈ Metric.ball x r := Metric.ball_subset_ball (by linarith) hy
  have hys : y + s ∈ Metric.ball x r := by
    have hdy := Metric.mem_ball.1 hy
    rw [Metric.mem_ball]
    have ht := dist_triangle (y + s) y x
    rw [dist_eq_norm (y + s) y, add_sub_cancel_left] at ht
    linarith
  let g : E → Y := fun z ↦ c z - fderiv ℝ c y z
  have hdiff (z : E) : DifferentiableAt ℝ g z :=
    (hc.differentiable one_ne_zero z).sub (ContinuousLinearMap.differentiableAt _)
  have hbound (z : E) (hz : z ∈ Metric.ball x r) : ‖fderiv ℝ g z‖ ≤ a := by
    rw [show g = fun z ↦ c z - fderiv ℝ c y z from rfl,
      fderiv_fun_sub (hc.differentiable one_ne_zero z) (ContinuousLinearMap.differentiableAt _),
      ContinuousLinearMap.fderiv]
    rw [← dist_eq_norm]
    have ht := dist_triangle (fderiv ℝ c z) (fderiv ℝ c x) (fderiv ℝ c y)
    rw [dist_comm (fderiv ℝ c x)] at ht
    linarith only [ht, hclose hz, hclose hy']
  have he := (convex_ball x r).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hdiff z) hbound hy' hys
  have hcalc : g (y + s) - g y = c (y + s) - c y - fderiv ℝ c y s := by
    dsimp [g]
    rw [map_add]
    abel
  rwa [hcalc, add_sub_cancel_left] at he

end EpigraphConditions

section PolyhedralConvergence

variable {E Y ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype ι]

open Chapter11 in
/-- A bounded family of quadratic terms gives uniform normalized model
agreement for (16.2.4), using the affine maximum's Lipschitz bound. -/
theorem polyhedralResidualModel_uniformAgreement
    [Nonempty ι] {I : Type*} {c : E → Y}
    (hc : ContDiff ℝ 1 c) (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ)
    (B : I → E →L[ℝ] E →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hB : ∀ i, ‖B i‖ ≤ M) (x : E) :
    UniformNormalizedModelAgreementAt (polyhedralResidualValue c p b)
      (fun y i s ↦ polyhedralResidualModel c p b (B i) y s) x := by
  intro a ha
  let K : ℝ := ((∑ i, ‖p i‖₊ : NNReal) : ℝ)
  have hK : 0 ≤ K := by positivity
  have hK₁ : 0 < K + 1 := by positivity
  have hM₁ : 0 < M + 1 := by positivity
  obtain ⟨r, hr, hrem⟩ := exists_uniform_firstOrder_of_contDiff hc x
    (div_pos (half_pos ha) hK₁)
  let t := min r (a / (M + 1))
  have ht : 0 < t := lt_min hr (div_pos ha hM₁)
  refine ⟨t, t, ht, ht, ?_⟩
  intro y hy i s hs
  by_cases hzero : s = 0
  · simp [normalizedModelError, hzero, ha.le]
  have hn := norm_pos_iff.2 hzero
  have hres : ‖c (y + s) - (c y + fderiv ℝ c y s)‖ ≤ (a / 2 / (K + 1)) * ‖s‖ := by
    rw [← sub_sub]
    exact hrem y (Metric.ball_subset_ball (min_le_left _ _) hy) s (hs.trans (min_le_left _ _))
  have hlip := (lipschitzWith_polyhedralAffineMaximum p b).dist_le_mul
    (c (y + s)) (c y + fderiv ℝ c y s)
  rw [Real.dist_eq, dist_eq_norm] at hlip
  have hpoly : |polyhedralResidualValue c p b (y + s) -
        polyhedralAffineMaximum p b (c y + fderiv ℝ c y s)| ≤ a / 2 * ‖s‖ := by
    apply hlip.trans
    calc
      K * ‖c (y + s) - (c y + fderiv ℝ c y s)‖ ≤ K * ((a / 2 / (K + 1)) * ‖s‖) :=
        mul_le_mul_of_nonneg_left hres hK
      _ = (K / (K + 1)) * (a / 2 * ‖s‖) := by ring
      _ ≤ a / 2 * ‖s‖ := mul_le_of_le_one_left (by positivity)
        ((div_le_one hK₁).2 (by linarith))
  have hcurv : |B i s s| ≤ M * ‖s‖ ^ 2 := by
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ‖B i s‖ * ‖s‖ := (B i s).le_opNorm s
      _ ≤ (‖B i‖ * ‖s‖) * ‖s‖ :=
        mul_le_mul_of_nonneg_right ((B i).le_opNorm s) (norm_nonneg _)
      _ = ‖B i‖ * ‖s‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hB i) (sq_nonneg _)
  have hsn := (le_div_iff₀ hM₁).1 (hs.trans (min_le_right _ _))
  have hmul : M * ‖s‖ ≤ a := by nlinarith only [hsn, norm_nonneg s]
  have hquad : |B i s s / 2| ≤ a / 2 * ‖s‖ := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact hcurv.trans (by nlinarith only [mul_le_mul_of_nonneg_right hmul (norm_nonneg s)])
  rw [normalizedModelError, abs_div, abs_of_nonneg hn.le]
  apply (div_le_iff₀ hn).2
  rw [polyhedralResidualModel, add_comm (B i s s / 2), ← sub_sub]
  exact (abs_sub _ _).trans (by linarith only [hpoly, hquad])

open Chapter11 in
/-- Theorem 16.2.1 for Algorithm 11.1.1. Every subsequential limit of a
monotone nonsmooth trust-region run for the polyhedral residual objective
is Clarke stationary. -/
theorem theorem_16_2_1_monotone
    [CompleteSpace E] [Nonempty ι] {I : Type*} {c : E → Y}
    (hc : ContDiff ℝ 1 c) (p : ι → Y →L[ℝ] ℝ) (b : ι → ℝ)
    (B : I → E →L[ℝ] E →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M) (hB : ∀ i, ‖B i‖ ≤ M)
    {Q : NonsmoothTRParams}
    (R : NonsmoothTRRun Q (polyhedralResidualValue c p b)
      (fun y i s ↦ polyhedralResidualModel c p b (B i) y s))
    (hAA : ∀ y, R.HasLocalSufficientDecrease y)
    {x : E} {j : ℕ → ℕ} (hj : StrictMono j) (hx : Tendsto (R.x ∘ j) atTop (𝓝 x)) :
    (0 : E) ∈ Optimization.clarkeSubgradient (polyhedralResidualValue c p b) x := by
  have hloc := (lipschitzWith_polyhedralAffineMaximum p b).locallyLipschitz.comp hc.locallyLipschitz
  obtain ⟨L, U, hU, hL⟩ := hloc x
  have hmatch : modelValueMatches (polyhedralResidualValue c p b)
      (fun y i s ↦ polyhedralResidualModel c p b (B i) y s) := by
    intro y i
    simp [polyhedralResidualModel, polyhedralResidualValue]
  exact theorem_11_2_5 R hU hL hmatch (polyhedralResidualModel_uniformAgreement hc p b B hM hB x)
    hAA hj hx

end PolyhedralConvergence

end ConnGouldToint.Chapter16
