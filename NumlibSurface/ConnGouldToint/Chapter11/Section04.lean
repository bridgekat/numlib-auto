import NumlibSurface.ConnGouldToint.Chapter11.Section02
import NumlibSurface.ConnGouldToint.Chapter08.Section01
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Topology

/-! # Generalized gradients of residual penalties -/

open Filter Topology Set Optimization ConvexAnalysis
open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter11

private theorem clarke_mem_iff_supports {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {f : E → ℝ} {x y : E} {K : NNReal}
    (hconv : ConvexOn ℝ univ f) (hLip : LipschitzWith K f) :
    y ∈ clarkeSubgradient f x ↔ ∀ z, f x + ⟪y, z - x⟫ ≤ f z := by
  constructor
  · intro hy z
    have h := mem_subdifferential.mp
      (clarkeSubgradient_subset_subdifferential hconv hLip.continuous univ_mem
        hLip.lipschitzOnWith hy) z
    rw [innerₗ_apply_apply, real_inner_comm] at h
    exact_mod_cast h
  · intro hy d
    apply le_clarkeDerivative_of_eventually_base_quotient_ge univ_mem hLip.lipschitzOnWith
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    apply (le_div_iff₀ ht).mpr
    have h := hy (x + t • d)
    rw [add_sub_cancel_left, real_inner_smul_right] at h
    linarith only [h]

variable {ι : Type*} [Fintype ι]

/-- Clip the inequality coordinates from below at zero and retain the
equality coordinates in (11.4.2). -/
noncomputable def clipResidualPlus (I : Set ι) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  open Classical in WithLp.toLp 2 (fun i ↦ if i ∈ I then max (x i) 0 else x i)

/-- The norm comparison by coordinate magnitudes used in Section 11.4. -/
def MonotoneResidualSeminorm (p : Seminorm ℝ (EuclideanSpace ℝ ι)) : Prop :=
  ∀ x y, (∀ i, |x i| ≤ |y i|) → p x ≤ p y

/-- Positive-part residual penalty (11.4.2). -/
noncomputable def residualPlus (p : Seminorm ℝ (EuclideanSpace ℝ ι)) (I : Set ι)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  p (clipResidualPlus I x)

/-- Negative-part residual penalty (11.4.3), using the reflection
identity (11.4.11) for a coordinatewise monotone norm. -/
noncomputable def residualMinus (p : Seminorm ℝ (EuclideanSpace ℝ ι)) (I : Set ι)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  residualPlus p I (-x)

/-- The dual unit ball in its pointwise form. For a norm this is
equivalent to the dual norm bound in (11.4.5). -/
def residualDualBall (p : Seminorm ℝ (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι) :=
  {y | ∀ d : EuclideanSpace ℝ ι, |⟪y, d⟫| ≤ p d}

omit [Fintype ι] in
private theorem residualPlus_zero (p : Seminorm ℝ (EuclideanSpace ℝ ι)) (I : Set ι) :
    residualPlus p I 0 = 0 := by
  classical
  have h : clipResidualPlus I (0 : EuclideanSpace ℝ ι) = 0 := by
    ext i
    simp [clipResidualPlus]
  simp [residualPlus, h]

omit [Fintype ι] in
private theorem residualPlus_smul (p : Seminorm ℝ (EuclideanSpace ℝ ι)) (I : Set ι)
    {t : ℝ} (ht : 0 ≤ t) (x : EuclideanSpace ℝ ι) :
    residualPlus p I (t • x) = t * residualPlus p I x := by
  classical
  have h : clipResidualPlus I (t • x) = t • clipResidualPlus I x := by
    ext i
    by_cases hi : i ∈ I
    · simp only [clipResidualPlus, PiLp.toLp_apply, PiLp.smul_apply, ite_eq_left hi, smul_eq_mul]
      rw [mul_max_of_nonneg _ _ ht, mul_zero]
    · simp [clipResidualPlus, hi]
  rw [residualPlus, h, map_smul_eq_mul, Real.norm_of_nonneg ht]
  rfl

omit [Fintype ι] in
private theorem residualPlus_le (p : Seminorm ℝ (EuclideanSpace ℝ ι))
    (hp : MonotoneResidualSeminorm p) (I : Set ι) (x : EuclideanSpace ℝ ι) :
    residualPlus p I x ≤ p x := by
  classical
  apply hp
  intro i
  by_cases hi : i ∈ I
  · simp only [clipResidualPlus, PiLp.toLp_apply, ite_eq_left hi]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ max (x i) 0 from le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  · simp [clipResidualPlus, hi]

omit [Fintype ι] in
private theorem residualPlus_add_le (p : Seminorm ℝ (EuclideanSpace ℝ ι))
    (hp : MonotoneResidualSeminorm p) (I : Set ι) (x y : EuclideanSpace ℝ ι) :
    residualPlus p I (x + y) ≤ residualPlus p I x + residualPlus p I y := by
  classical
  refine (hp _ _ (fun i ↦ ?_)).trans (map_add_le_add p _ _)
  by_cases hi : i ∈ I
  · simp only [clipResidualPlus, PiLp.toLp_apply, PiLp.add_apply, ite_eq_left hi]
    rw [abs_of_nonneg (le_max_right _ _),
      abs_of_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _))]
    exact max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
      (add_nonneg (le_max_right _ _) (le_max_right _ _))
  · simp [clipResidualPlus, hi, PiLp.add_apply]

omit [Fintype ι] in
private theorem residualPlus_convex (p : Seminorm ℝ (EuclideanSpace ℝ ι))
    (hp : MonotoneResidualSeminorm p) (I : Set ι) : ConvexOn ℝ univ (residualPlus p I) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  simpa only [residualPlus_smul p I ha, residualPlus_smul p I hb, smul_eq_mul] using
    residualPlus_add_le p hp I (a • x) (b • y)

private theorem residualPlus_lipschitz (p : Seminorm ℝ (EuclideanSpace ℝ ι))
    (hp : MonotoneResidualSeminorm p) (I : Set ι) {K : NNReal}
    (hK : ∀ d, p d ≤ K * ‖d‖) : LipschitzWith K (residualPlus p I) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm, abs_sub_le_iff]
  have h (u v : EuclideanSpace ℝ ι) : residualPlus p I u - residualPlus p I v ≤ p (u - v) := by
    have h := residualPlus_add_le p hp I (u - v) v
    rw [sub_add_cancel] at h
    linarith only [h, residualPlus_le p hp I (u - v)]
  exact ⟨(h x y).trans (hK _), (h y x).trans (by simpa only [norm_sub_rev] using hK (y - x))⟩

private theorem inner_clip_ge {I : Set ι} {y : EuclideanSpace ℝ ι}
    (hy : ∀ i ∈ I, 0 ≤ y i) (d : EuclideanSpace ℝ ι) :
    ⟪y, d⟫ ≤ ⟪y, clipResidualPlus I d⟫ := by
  classical
  simp only [PiLp.inner_apply, Real.inner_apply]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ I
  · simp only [clipResidualPlus, PiLp.toLp_apply, ite_eq_left hi]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hy i hi)
  · simp [clipResidualPlus, hi]

private theorem exists_monotoneResidualSeminorm_bound
    (p : Seminorm ℝ (EuclideanSpace ℝ ι)) (hp : MonotoneResidualSeminorm p) :
    ∃ K : NNReal, ∀ d, p d ≤ K * ‖d‖ := by
  let u : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ ↦ (1 : ℝ))
  refine ⟨(p u).toNNReal, fun d ↦ ?_⟩
  have h : p d ≤ p (‖d‖ • u) := by
    apply hp
    intro i
    have hi := PiLp.norm_apply_le d i
    simpa [u, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg d)] using hi
  rw [map_smul_eq_mul, Real.norm_of_nonneg (norm_nonneg d)] at h
  rw [Real.coe_toNNReal _ (apply_nonneg p u), mul_comm]
  exact h

/-- Theorem 11.4.1. The generalized gradient is the part of the dual
unit ball that is nonnegative on inequality coordinates and supports
the clipped penalty at the given residual. The final two conditions
give vanishing on negative coordinates and an attained dual bound. -/
theorem theorem_11_4_1 (p : Seminorm ℝ (EuclideanSpace ℝ ι))
    (hp : MonotoneResidualSeminorm p) (I : Set ι) (x y : EuclideanSpace ℝ ι) :
    y ∈ clarkeSubgradient (residualPlus p I) x ↔
      (⟪y, x⟫ = residualPlus p I x ∧ (∀ i ∈ I, 0 ≤ y i) ∧ y ∈ residualDualBall p) ∧
      (∀ i ∈ I, x i < 0 → y i = 0) ∧
      ⟪y, clipResidualPlus I x⟫ = p (clipResidualPlus I x) := by
  classical
  obtain ⟨K, hK⟩ := exists_monotoneResidualSeminorm_bound p hp
  rw [clarke_mem_iff_supports (residualPlus_convex p hp I) (residualPlus_lipschitz p hp I hK)]
  constructor
  · intro h
    have hlin (d : EuclideanSpace ℝ ι) : ⟪y, d⟫ ≤ residualPlus p I d := by
      have hh := h (x + d)
      rw [add_sub_cancel_left] at hh
      linarith only [hh, residualPlus_add_le p hp I x d]
    have hxe : ⟪y, x⟫ = residualPlus p I x := by
      have hh := h 0
      rw [residualPlus_zero, zero_sub, inner_neg_right] at hh
      exact le_antisymm (hlin x) (by linarith)
    have hsign (i : ι) (hi : i ∈ I) : 0 ≤ y i := by
      let v := EuclideanSpace.single i (-1 : ℝ)
      have he : clipResidualPlus I v = 0 := by
        ext j
        by_cases hj : j = i
        · subst j
          simp [clipResidualPlus, v, hi]
        · simp [clipResidualPlus, v, hj]
      have hv := hlin v
      rw [show residualPlus p I v = 0 by simp [residualPlus, he],
        show ⟪y, v⟫ = -y i by simp [v, EuclideanSpace.inner_single_right]] at hv
      linarith only [hv]
    have hdual : y ∈ residualDualBall p := by
      intro d
      have hd := (hlin d).trans (residualPlus_le p hp I d)
      have hd' := (hlin (-d)).trans (residualPlus_le p hp I (-d))
      rw [inner_neg_right, map_neg_eq_map] at hd'
      exact abs_le.mpr ⟨by linarith only [hd'], hd⟩
    have hclip : ⟪y, clipResidualPlus I x⟫ = p (clipResidualPlus I x) := by
      exact le_antisymm ((le_abs_self _).trans (hdual _))
        (by change residualPlus p I x ≤ _; rw [← hxe]; exact inner_clip_ge hsign x)
    refine ⟨⟨hxe, hsign, hdual⟩, ?_, hclip⟩
    intro i hi hxi
    have hsum : (∑ j, y j * ((clipResidualPlus I x) j - x j)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      have h := hclip.trans hxe.symm
      simp only [PiLp.inner_apply, Real.inner_apply] at h
      rw [← h, sub_self]
    have hnn (j : ι) : 0 ≤ y j * ((clipResidualPlus I x) j - x j) := by
      by_cases hj : j ∈ I
      · simp only [clipResidualPlus, PiLp.toLp_apply, ite_eq_left hj]
        exact mul_nonneg (hsign j hj) (sub_nonneg.mpr (le_max_left _ _))
      · simp [clipResidualPlus, hj]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hnn j)).mp hsum i
      (Finset.mem_univ _)
    simp only [clipResidualPlus, PiLp.toLp_apply, ite_eq_left hi, max_eq_right hxi.le,
      zero_sub] at hz
    exact (mul_eq_zero.mp hz).resolve_right (neg_ne_zero.mpr hxi.ne)
  · rintro ⟨⟨hxe, hsign, hdual⟩, _, _⟩ z
    have h := (inner_clip_ge hsign z).trans ((le_abs_self _).trans
      (hdual (clipResidualPlus I z)))
    rw [inner_sub_right, ← hxe, add_sub_cancel]
    exact h

/-- Corollary 11.4.2. Reflection changes the sign of the inequality
coordinates in the dual characterization. -/
theorem corollary_11_4_2 (p : Seminorm ℝ (EuclideanSpace ℝ ι))
    (hp : MonotoneResidualSeminorm p) (I : Set ι) (x y : EuclideanSpace ℝ ι) :
    y ∈ clarkeSubgradient (residualMinus p I) x ↔
      (⟪y, x⟫ = residualMinus p I x ∧ (∀ i ∈ I, y i ≤ 0) ∧ y ∈ residualDualBall p) ∧
      (∀ i ∈ I, 0 < x i → y i = 0) ∧
      ⟪-y, clipResidualPlus I (-x)⟫ = p (clipResidualPlus I (-x)) := by
  obtain ⟨K, hK⟩ := exists_monotoneResidualSeminorm_bound p hp
  have hconv : ConvexOn ℝ univ (residualMinus p I) := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ s t hs ht hst
    simpa only [residualMinus, neg_add, smul_neg] using
      (residualPlus_convex p hp I).2 (mem_univ (-a)) (mem_univ (-b)) hs ht hst
  have hLip : LipschitzWith K (residualMinus p I) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have h := (residualPlus_lipschitz p hp I hK).dist_le_mul (-a) (-b)
    simpa only [dist_neg_neg, residualMinus] using h
  have he : y ∈ clarkeSubgradient (residualMinus p I) x ↔
      -y ∈ clarkeSubgradient (residualPlus p I) (-x) := by
    rw [clarke_mem_iff_supports hconv hLip,
      clarke_mem_iff_supports (residualPlus_convex p hp I) (residualPlus_lipschitz p hp I hK)]
    constructor
    · intro h z
      have hh := h (-z)
      rw [show -z - x = -(z - -x) by abel, inner_neg_right] at hh
      simpa only [residualMinus, neg_neg, inner_neg_left] using hh
    · intro h z
      have hh := h (-z)
      rw [show -z - -x = -(z - x) by abel, inner_neg_neg] at hh
      exact hh
  rw [he, theorem_11_4_1 p hp]
  have hd : -y ∈ residualDualBall p ↔ y ∈ residualDualBall p := by
    simp only [residualDualBall, mem_ofPred_eq, inner_neg_left, abs_neg]
  simp only [inner_neg_neg, residualMinus, PiLp.neg_apply, neg_nonneg, hd, neg_lt_zero,
    neg_eq_zero]


private theorem dualNorm_eq_one_of_support (p : Seminorm ℝ (EuclideanSpace ℝ ι))
    {y d : EuclideanSpace ℝ ι} (hy : y ∈ residualDualBall p)
    (hd : 0 < p d) (h : ⟪y, d⟫ = p d) : Chapter08.dualNorm p y = 1 := by
  have hle (v : EuclideanSpace ℝ ι) : |⟪y, v⟫| / p v ≤ 1 := by
    by_cases hv : p v = 0
    · simp [hv]
    · exact (div_le_one (lt_of_le_of_ne (apply_nonneg p v) (Ne.symm hv))).mpr (hy v)
  apply le_antisymm (ciSup_le hle)
  have hbd : BddAbove (range (fun v : EuclideanSpace ℝ ι ↦ |⟪y, v⟫| / p v)) :=
    ⟨1, fun _ ⟨v, hv⟩ ↦ hv ▸ hle v⟩
  have he : |⟪y, d⟫| / p d = 1 := by rw [h, abs_of_pos hd, div_self hd.ne']
  exact he ▸ le_ciSup hbd d

/-- At a positive clipped residual, every positive-part subgradient has
dual norm exactly one. -/
theorem residualPlus_dualNorm_eq_one (p : Seminorm ℝ (EuclideanSpace ℝ ι))
    (hp : MonotoneResidualSeminorm p) {I : Set ι} {x y : EuclideanSpace ℝ ι}
    (hy : y ∈ clarkeSubgradient (residualPlus p I) x) (hx : 0 < residualPlus p I x) :
    Chapter08.dualNorm p y = 1 := by
  obtain ⟨⟨_, _, hdual⟩, _, hclip⟩ := (theorem_11_4_1 p hp I x y).mp hy
  exact dualNorm_eq_one_of_support p hdual hx hclip

/-- At a positive clipped residual, every negative-part subgradient has
dual norm exactly one. -/
theorem residualMinus_dualNorm_eq_one (p : Seminorm ℝ (EuclideanSpace ℝ ι))
    (hp : MonotoneResidualSeminorm p) {I : Set ι} {x y : EuclideanSpace ℝ ι}
    (hy : y ∈ clarkeSubgradient (residualMinus p I) x) (hx : 0 < residualMinus p I x) :
    Chapter08.dualNorm p y = 1 := by
  obtain ⟨⟨_, _, hdual⟩, _, hclip⟩ := (corollary_11_4_2 p hp I x y).mp hy
  have hn : -y ∈ residualDualBall p := by
    intro d
    rw [inner_neg_left, abs_neg]
    exact hdual d
  have h := dualNorm_eq_one_of_support p hn hx hclip
  simpa only [Chapter08.dualNorm, inner_neg_left, abs_neg] using h

section Polyhedral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nonempty ι]

/-- The finite maximum of affine functions (11.4.4). -/
noncomputable def polyhedralResidual (p : ι → E) (b : ι → ℝ) (x : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ⟪p i, x⟫ + b i)

/-- Indices that attain the affine maximum at a given point. -/
def polyhedralActiveSet (p : ι → E) (b : ι → ℝ) (x : E) : Set ι :=
  {i | ⟪p i, x⟫ + b i = polyhedralResidual p b x}

private theorem affine_le_polyhedral (p : ι → E) (b : ι → ℝ) (x : E) (i : ι) :
    ⟪p i, x⟫ + b i ≤ polyhedralResidual p b x :=
  Finset.le_sup' (fun i ↦ ⟪p i, x⟫ + b i) (Finset.mem_univ i)

private theorem polyhedral_convex (p : ι → E) (b : ι → ℝ) :
    ConvexOn ℝ univ (polyhedralResidual p b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a c ha hc hac
  apply Finset.sup'_le
  intro i _
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  simp only [smul_eq_mul]
  have hx := mul_le_mul_of_nonneg_left (affine_le_polyhedral p b x i) ha
  have hy := mul_le_mul_of_nonneg_left (affine_le_polyhedral p b y i) hc
  nlinarith only [hx, hy, congrArg (fun z : ℝ ↦ z * b i) hac]

private theorem polyhedral_lipschitz (p : ι → E) (b : ι → ℝ) :
    LipschitzWith (∑ i, ‖p i‖₊) (polyhedralResidual p b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm, abs_sub_le_iff]
  have h (u v : E) :
      polyhedralResidual p b u - polyhedralResidual p b v ≤
        (↑(∑ i, ‖p i‖₊) : ℝ) * ‖u - v‖ := by
    apply sub_le_iff_le_add.mpr
    apply Finset.sup'_le
    intro i hi
    have hsum : ‖p i‖ ≤ (↑(∑ j, ‖p j‖₊) : ℝ) := by
      have hh : ‖p i‖₊ ≤ ∑ j, ‖p j‖₊ :=
        Finset.single_le_sum (fun j _ ↦ show (0 : NNReal) ≤ ‖p j‖₊ from zero_le) hi
      exact_mod_cast hh
    have hdiff := (real_inner_le_norm (p i) (u - v)).trans
      (mul_le_mul_of_nonneg_right hsum (norm_nonneg _))
    rw [inner_sub_right] at hdiff
    linarith only [hdiff, affine_le_polyhedral p b v i]
  exact ⟨h x y, by simpa only [norm_sub_rev] using h y x⟩

/-- Theorem 11.4.3. The generalized gradient of a finite maximum of
affine functions is the convex hull of the gradients of its active terms. -/
theorem theorem_11_4_3 [CompleteSpace E] (p : ι → E) (b : ι → ℝ) (x : E) :
    clarkeSubgradient (polyhedralResidual p b) x =
      convexHull ℝ (p '' polyhedralActiveSet p b x) := by
  classical
  let h := polyhedralResidual p b
  let A := p '' polyhedralActiveSet p b x
  let C := convexHull ℝ A
  have hC : Convex ℝ C := convex_convexHull ℝ A
  have hCcl : IsClosed C :=
    (((Set.toFinite (polyhedralActiveSet p b x)).image p).isCompact_convexHull ℝ).isClosed
  have hCne : C.Nonempty := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i ↦ ⟪p i, x⟫ + b i)
    exact ⟨p i, subset_convexHull ℝ A ⟨i, hi.symm, rfl⟩⟩
  ext y
  rw [clarke_mem_iff_supports (polyhedral_convex p b) (polyhedral_lipschitz p b)]
  change (∀ z, h x + ⟪y, z - x⟫ ≤ h z) ↔ y ∈ C
  constructor
  · intro hs
    by_contra hy
    let w := bestApprox C y
    let d := y - w
    have hw : w ∈ C := bestApprox_mem hCne hCcl hC _
    have hd : d ≠ 0 := fun hzero ↦ hy ((sub_eq_zero.mp hzero).symm ▸ hw)
    have hnormal := (bestApprox_eq_iff hCne hCcl hC).mp (show bestApprox C y = w from rfl)
    have hgap (i : ι) (hi : i ∈ polyhedralActiveSet p b x) : ⟪p i, d⟫ < ⟪y, d⟫ := by
      have hp : p i ∈ C := subset_convexHull ℝ A ⟨i, hi, rfl⟩
      have h := hnormal.2 (p i) hp
      change ⟪d, p i - w⟫ ≤ 0 at h
      rw [inner_sub_right] at h
      have hyw : ⟪y, d⟫ - ⟪w, d⟫ = ‖d‖ ^ 2 := by
        rw [← inner_sub_left]
        exact real_inner_self_eq_norm_sq d
      linarith only [h, hyw, sq_pos_of_pos (norm_pos_iff.mpr hd), real_inner_comm d (p i),
        real_inner_comm d w]
    have hsmall (i : ι) :
        ∀ᶠ t : ℝ in 𝓝[>] 0, ⟪p i, x + t • d⟫ + b i < h x + t * ⟪y, d⟫ := by
      by_cases hi : i ∈ polyhedralActiveSet p b x
      · have he : ⟪p i, x⟫ + b i = h x := hi
        filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
        rw [inner_add_right, real_inner_smul_right]
        linarith only [he, mul_lt_mul_of_pos_left (hgap i hi) ht]
      · have hlt : ⟪p i, x⟫ + b i < h x :=
          lt_of_le_of_ne (affine_le_polyhedral p b x i) hi
        have hc : Continuous (fun t : ℝ ↦
          (⟪p i, x⟫ + b i - h x) + t * (⟪p i, d⟫ - ⟪y, d⟫)) := by fun_prop
        have he : ∀ᶠ t : ℝ in 𝓝[>] 0,
            (⟪p i, x⟫ + b i - h x) + t * (⟪p i, d⟫ - ⟪y, d⟫) < 0 :=
          (hc.continuousAt.tendsto.eventually_lt_const
          (show (⟪p i, x⟫ + b i - h x) + 0 * (⟪p i, d⟫ - ⟪y, d⟫) < 0 by
            linarith only [hlt])).filter_mono nhdsWithin_le_nhds
        filter_upwards [he] with t ht
        rw [inner_add_right, real_inner_smul_right]
        linarith only [ht]
    obtain ⟨t, ht⟩ := (Filter.eventually_all.mpr hsmall).exists
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i ↦ ⟪p i, x + t • d⟫ + b i)
    have hh := hs (x + t • d)
    rw [add_sub_cancel_left, real_inner_smul_right] at hh
    change h (x + t • d) = _ at hi
    exact (ht i).not_ge (hh.trans_eq hi)
  · intro hy z
    have hA : A ⊆ {v : E | ⟪v, z - x⟫ ≤ h z - h x} := by
      rintro _ ⟨i, hi, rfl⟩
      have he : ⟪p i, x⟫ + b i = h x := hi
      have hh := affine_le_polyhedral p b z i
      change ⟪p i, z - x⟫ ≤ h z - h x
      rw [inner_sub_right]
      linarith only [he, hh]
    have hhalf : Convex ℝ {v : E | ⟪v, z - x⟫ ≤ h z - h x} := by
      intro u hu v hv a c ha hc hac
      change ⟪u, z - x⟫ ≤ h z - h x at hu
      change ⟪v, z - x⟫ ≤ h z - h x at hv
      change ⟪a • u + c • v, z - x⟫ ≤ h z - h x
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      nlinarith only [mul_le_mul_of_nonneg_left hu ha, mul_le_mul_of_nonneg_left hv hc,
        congrArg (fun t : ℝ ↦ t * (h z - h x)) hac]
    have hh := convexHull_min hA hhalf hy
    exact le_sub_iff_add_le'.mp hh

end Polyhedral

end ConnGouldToint.Chapter11
