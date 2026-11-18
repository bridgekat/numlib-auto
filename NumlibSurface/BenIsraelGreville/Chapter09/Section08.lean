/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter09.Section03
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Frames in Hilbert spaces

Section 9.8 of [benIsrael2003generalized] characterizes frames by
surjectivity of synthesis. Coefficient series use unconditional convergence.
-/

noncomputable section

namespace BenIsraelGreville.Chapter09

open Filter Topology
open scoped InnerProductSpace ENNReal

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "ℓ²" => lp (fun _ : ℕ => 𝕜) 2

/-- **Equation (103)** of [benIsrael2003generalized], Chapter 9.
A sequence is a basis when each vector has a unique expansion in the
given order. -/
def IsSequenceBasis (f : ℕ → H) : Prop :=
  ∀ x : H, ∃! c : ℕ → 𝕜,
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, c i • f i) atTop (𝓝 x)

/-- An unconditional basis has an unconditionally convergent expansion
for each vector. -/
def IsUnconditionalSequenceBasis (f : ℕ → H) : Prop :=
  IsSequenceBasis (𝕜 := 𝕜) f ∧ ∀ x : H, ∃ c : ℕ → 𝕜, HasSum (fun n => c n • f n) x

/-- The coefficient at an index, with the inner product linear in the vector being analyzed. -/
def frameCoefficient (f : ℕ → H) (x : H) (n : ℕ) : 𝕜 := inner 𝕜 (f n) x

/-- The coefficient energy in **Equation (104)** of [benIsrael2003generalized]. -/
def frameCoefficientEnergy (f : ℕ → H) (x : H) : ℝ :=
  ∑' n, ‖frameCoefficient (𝕜 := 𝕜) f x n‖ ^ 2

/-- **Definition 6(b)** of [benIsrael2003generalized], Chapter 9.
A Bessel sequence has square-summable coefficients and a uniform upper bound. -/
structure IsBesselSequence (f : ℕ → H) : Prop where
  /-- Every vector has square-summable coefficients. -/
  summable (x : H) : Summable (fun n => ‖frameCoefficient (𝕜 := 𝕜) f x n‖ ^ 2)
  /-- A single upper bound controls every coefficient energy. -/
  exists_bound : ∃ B : ℝ, 0 < B ∧ ∀ x, frameCoefficientEnergy (𝕜 := 𝕜) f x ≤ B * ‖x‖ ^ 2

/-- **Definition 6(a)**, Equation (104) of [benIsrael2003generalized], Chapter 9.
A frame also has a positive uniform lower bound. -/
def IsFrame (f : ℕ → H) : Prop :=
  IsBesselSequence (𝕜 := 𝕜) f ∧
    ∃ A : ℝ, 0 < A ∧ ∀ x, A * ‖x‖ ^ 2 ≤ frameCoefficientEnergy (𝕜 := 𝕜) f x

private theorem norm_sq_lp_eq_energy (c : ℓ²) : ‖c‖ ^ 2 = ∑' n, ‖c n‖ ^ 2 := by
  have h₂ : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  simpa only [h₂, Real.rpow_two] using lp.norm_rpow_eq_tsum (by norm_num) c

private def frameAnalysisLinear (f : ℕ → H) (h : IsBesselSequence (𝕜 := 𝕜) f) : H →ₗ[𝕜] ℓ² where
  toFun x := ⟨frameCoefficient f x, memℓp_gen (by
    have h₂ : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
    simpa only [h₂, Real.rpow_two] using h.summable x)⟩
  map_add' x y := by
    apply lp.ext
    funext n
    exact inner_add_right _ _ _
  map_smul' c x := by
    apply lp.ext
    funext n
    exact inner_smul_right _ _ _

/-- **Equation (106)** of [benIsrael2003generalized], Chapter 9.
Frame analysis sends a vector to its sequence of coefficients. -/
def frameAnalysis (f : ℕ → H) (h : IsBesselSequence (𝕜 := 𝕜) f) : H →L[𝕜] ℓ² := by
  apply (frameAnalysisLinear f h).mkContinuousOfExistsBound
  obtain ⟨B, hB, hbound⟩ := h.exists_bound
  refine ⟨Real.sqrt B, fun x => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_sq_lp_eq_energy, mul_pow, Real.sq_sqrt hB.le]
  exact hbound x

/-- Each coordinate of analysis is the inner product with the frame vector. -/
theorem frameAnalysis_apply (f : ℕ → H) (h : IsBesselSequence (𝕜 := 𝕜) f) (x : H) (n : ℕ) :
    frameAnalysis f h x n = frameCoefficient f x n := rfl

/-- The squared norm of analysis is the sum of squared coefficients. -/
theorem norm_sq_frameAnalysis (f : ℕ → H) (h : IsBesselSequence (𝕜 := 𝕜) f) (x : H) :
    ‖frameAnalysis f h x‖ ^ 2 = frameCoefficientEnergy (𝕜 := 𝕜) f x :=
  norm_sq_lp_eq_energy _

variable [CompleteSpace H]

/-- **Equation (105)** of [benIsrael2003generalized], Chapter 9.
Synthesis is the bounded adjoint of analysis. -/
def frameSynthesis (f : ℕ → H) (h : IsBesselSequence (𝕜 := 𝕜) f) : ℓ² →L[𝕜] H :=
  (frameAnalysis f h).adjoint

/-- **Equation (106)** of [benIsrael2003generalized], Chapter 9.
The adjoint of synthesis is analysis. -/
theorem frameSynthesis_adjoint (f : ℕ → H) (h : IsBesselSequence (𝕜 := 𝕜) f) :
    (frameSynthesis f h).adjoint = frameAnalysis f h :=
  ContinuousLinearMap.adjoint_adjoint _

private theorem frameSynthesis_single (f : ℕ → H) (h : IsBesselSequence (𝕜 := 𝕜) f)
    (n : ℕ) (c : 𝕜) : frameSynthesis f h (lp.single 2 n c) = c • f n := by
  apply ext_inner_left 𝕜
  intro x
  rw [frameSynthesis, ContinuousLinearMap.adjoint_inner_right, lp.inner_single_right]
  change inner 𝕜 (frameCoefficient f x n) c = inner 𝕜 x (c • f n)
  rw [frameCoefficient, inner_smul_right, ← inner_conj_symm (x := x) (y := f n)]
  simp [RCLike.inner_apply]

/-- **Equation (105)** of [benIsrael2003generalized], Chapter 9.
The synthesis series converges unconditionally to the value of synthesis. -/
theorem hasSum_frameSynthesis (f : ℕ → H) (h : IsBesselSequence (𝕜 := 𝕜) f) (c : ℓ²) :
    HasSum (fun n => c n • f n) (frameSynthesis f h c) := by
  have hs := (lp.hasSum_single (by norm_num) c).mapL (frameSynthesis f h)
  simpa only [Function.comp_apply, frameSynthesis_single] using hs

omit [CompleteSpace H] in
private theorem boundedSynthesis_of_summable (f : ℕ → H)
    (hs : ∀ c : ℓ², Summable (fun n => c n • f n)) :
    ∃ T : ℓ² →L[𝕜] H, ∀ c : ℓ², HasSum (fun n => c n • f n) (T c) := by
  let P (n : ℕ) : ℓ² →L[𝕜] H :=
    ∑ i ∈ Finset.range n, (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 2 i).smulRight (f i)
  have hP (n : ℕ) (c : ℓ²) : P n c = ∑ i ∈ Finset.range n, c i • f i := by
    simp [P, ContinuousLinearMap.smulRight_apply]
    rfl
  have hlim (c : ℓ²) : Tendsto (fun n => P n c) atTop (𝓝 (∑' i, c i • f i)) := by
    simpa only [hP] using (hs c).hasSum.tendsto_sum_nat
  obtain ⟨C, hC⟩ := banach_steinhaus (g := P) fun c => by
    obtain ⟨B, hB⟩ := (hlim c).norm.bddAbove_range
    exact ⟨B, fun i => hB ⟨i, rfl⟩⟩
  let L : ℓ² →ₗ[𝕜] H :=
    { toFun := fun c => ∑' i, c i • f i
      map_add' := fun c d => by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (hs c).tsum_add (hs d)
      map_smul' := fun a c => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
        exact ((hs c).hasSum.const_smul a).tsum_eq }
  have hL (c : ℓ²) : ‖L c‖ ≤ C * ‖c‖ :=
    le_of_tendsto (hlim c).norm (Eventually.of_forall fun n =>
      ((P n).le_opNorm c).trans (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg c)))
  exact ⟨L.mkContinuous C hL, fun c => (hs c).hasSum⟩

private theorem analysis_of_boundedSynthesis (f : ℕ → H) (T : ℓ² →L[𝕜] H)
    (hT : ∀ c : ℓ², HasSum (fun n => c n • f n) (T c)) (x : H) (n : ℕ) :
    T.adjoint x n = frameCoefficient f x n := by
  have hs : HasSum (fun i => (lp.single 2 n (1 : 𝕜) : ℓ²) i • f i) (f n) := by
    convert hasSum_ite_eq n (f n) using 1
    funext i
    by_cases hi : i = n
    · simp [hi]
    · simp [hi, lp.single_apply]
  have hsingle : T (lp.single 2 n (1 : 𝕜)) = f n := (hT _).unique hs
  calc
    _ = inner 𝕜 (lp.single 2 n (1 : 𝕜)) (T.adjoint x) := by
      rw [lp.inner_single_left, RCLike.inner_apply]
      simp
    _ = _ := by rw [ContinuousLinearMap.adjoint_inner_right, hsingle]; rfl

/-- **Equations (105)–(106)** of [benIsrael2003generalized], Chapter 9.
A sequence is Bessel exactly when synthesis is defined by a convergent
series for every square-summable input. -/
theorem bessel_iff_synthesis (f : ℕ → H) :
    IsBesselSequence (𝕜 := 𝕜) f ↔ ∀ c : ℓ², Summable (fun n => c n • f n) := by
  refine ⟨fun h c => (hasSum_frameSynthesis f h c).summable, fun h => ?_⟩
  obtain ⟨T, hT⟩ := boundedSynthesis_of_summable f h
  have hc (x : H) (n : ℕ) := analysis_of_boundedSynthesis f T hT x n
  constructor
  · intro x
    simp_rw [← hc]
    have h₂ : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
    simpa only [h₂, Real.rpow_two] using (lp.memℓp (T.adjoint x)).summable (by norm_num)
  · refine ⟨‖T.adjoint‖ ^ 2 + 1, by positivity, fun x => ?_⟩
    unfold frameCoefficientEnergy
    simp_rw [← hc]
    rw [← norm_sq_lp_eq_energy]
    calc
      _ ≤ (‖T.adjoint‖ * ‖x‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (T.adjoint.le_opNorm x)
      _ ≤ (‖T.adjoint‖ ^ 2 + 1) * ‖x‖ ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg _)

/-- **Equation (107)** of [benIsrael2003generalized], Chapter 9.
The frame operator analyzes a vector and synthesizes its coefficients. -/
def frameOperator (f : ℕ → H) (h : IsBesselSequence (𝕜 := 𝕜) f) : H →L[𝕜] H :=
  (frameSynthesis f h).comp (frameAnalysis f h)

/-- The frame operator is given by unconditional synthesis of the coefficients. -/
theorem hasSum_frameOperator (f : ℕ → H) (h : IsBesselSequence (𝕜 := 𝕜) f) (x : H) :
    HasSum (fun n => frameCoefficient (𝕜 := 𝕜) f x n • f n) (frameOperator f h x) :=
  hasSum_frameSynthesis f h (frameAnalysis f h x)

/-- The quadratic form of the frame operator is the coefficient energy. -/
theorem frameOperator_re_inner (f : ℕ → H) (h : IsBesselSequence (𝕜 := 𝕜) f) (x : H) :
    RCLike.re (inner 𝕜 (frameOperator f h x) x) = frameCoefficientEnergy (𝕜 := 𝕜) f x := by
  change RCLike.re (inner 𝕜 ((frameAnalysis f h).adjoint (frameAnalysis f h x)) x) = _
  rw [ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq, norm_sq_frameAnalysis]

/-- The frame operator is self-adjoint for every Bessel sequence. -/
theorem frameOperator_adjoint (f : ℕ → H) (h : IsBesselSequence (𝕜 := 𝕜) f) :
    (frameOperator f h).adjoint = frameOperator f h := by
  simp only [frameOperator, ContinuousLinearMap.adjoint_comp,
    frameSynthesis, ContinuousLinearMap.adjoint_adjoint]

/-- The frame operator of a frame is a bounded linear isomorphism. -/
theorem exists_frameOperator_equiv (f : ℕ → H) (h : IsFrame (𝕜 := 𝕜) f) :
    ∃ E : H ≃L[𝕜] H, E.toContinuousLinearMap = frameOperator f h.1 := by
  let S := frameOperator f h.1
  obtain ⟨a, ha, haS⟩ := h.2
  have hnorm (x : H) : a * ‖x‖ ≤ ‖S x‖ := by
    by_cases hx : x = 0
    · simp [hx]
    apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hx)).mp
    calc
      (a * ‖x‖) * ‖x‖ = a * ‖x‖ ^ 2 := by ring
      _ ≤ RCLike.re (inner 𝕜 (S x) x) := by rw [frameOperator_re_inner]; exact haS x
      _ ≤ ‖S x‖ * ‖x‖ := re_inner_le_norm _ _
  obtain ⟨C, hC⟩ := (antilipschitzWith_iff_exists_mul_le_norm (f := S)).mpr ⟨a, ha, hnorm⟩
  have hk : S.ker = ⊥ := LinearMap.ker_eq_bot.mpr hC.injective
  have hR : IsClosed (S.range : Set H) := hC.isClosed_range S.uniformContinuous
  let : CompleteSpace S.range := hR.completeSpace_coe
  have ht : S.range = ⊤ := by
    apply S.range.orthogonal_eq_bot_iff.mp
    rw [S.orthogonal_range, frameOperator_adjoint, hk]
  exact ⟨ContinuousLinearEquiv.ofBijective S hk ht, ContinuousLinearEquiv.coe_ofBijective S hk ht⟩

private theorem frameInverse_inner (f : ℕ → H) (h : IsBesselSequence (𝕜 := 𝕜) f)
    (S : H ≃L[𝕜] H) (hS : S.toContinuousLinearMap = frameOperator f h) (x y : H) :
    inner 𝕜 (S.symm x) y = inner 𝕜 x (S.symm y) := by
  have hs : (S.toContinuousLinearMap).adjoint = S.toContinuousLinearMap := by
    rw [hS, frameOperator_adjoint]
  have he := S.toContinuousLinearMap.adjoint_inner_right (S.symm x) (S.symm y)
  rw [hs] at he
  change inner 𝕜 (S.symm x) (S (S.symm y)) = inner 𝕜 (S (S.symm x)) (S.symm y) at he
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using he

/-- **Equation (108)** of [benIsrael2003generalized], Chapter 9.
The inverse of the frame operator gives dual-frame coefficients and an
unconditionally convergent reconstruction. -/
theorem frame_reconstruction (f : ℕ → H) (h : IsFrame (𝕜 := 𝕜) f) :
    ∃ S : H ≃L[𝕜] H, S.toContinuousLinearMap = frameOperator f h.1 ∧
      ∀ x : H, HasSum (fun n => inner 𝕜 (S.symm (f n)) x • f n) x := by
  obtain ⟨S, hS⟩ := exists_frameOperator_equiv f h
  refine ⟨S, hS, fun x => ?_⟩
  have hsum := hasSum_frameOperator f h.1 (S.symm x)
  rw [← hS] at hsum
  change HasSum _ (S (S.symm x)) at hsum
  rw [S.apply_symm_apply] at hsum
  simpa only [frameCoefficient, ← frameInverse_inner f h.1 S hS] using hsum

/-- **Theorem 12** of [benIsrael2003generalized], Chapter 9.
A sequence is a frame exactly when its synthesis series converges for all
square-summable inputs and its values span the whole Hilbert space. -/
theorem theorem_12 (f : ℕ → H) :
    IsFrame (𝕜 := 𝕜) f ↔
      (∀ c : ℓ², Summable (fun n => c n • f n)) ∧
        Function.Surjective (fun c : ℓ² => ∑' n, c n • f n) := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := exists_frameOperator_equiv f h
    refine ⟨(bessel_iff_synthesis f).mp h.1, fun x => ?_⟩
    refine ⟨frameAnalysis f h.1 (S.symm x), ?_⟩
    change (∑' n, frameAnalysis f h.1 (S.symm x) n • f n) = x
    rw [(hasSum_frameSynthesis f h.1 _).tsum_eq]
    change frameOperator f h.1 (S.symm x) = x
    rw [← hS]
    exact S.apply_symm_apply x
  · rintro ⟨hs, hsur⟩
    have h := (bessel_iff_synthesis f).mpr hs
    let T := frameSynthesis f h
    have hT : Function.Surjective T := by
      intro x
      obtain ⟨c, hc⟩ := hsur x
      exact ⟨c, ((hasSum_frameSynthesis f h c).tsum_eq).symm.trans hc⟩
    obtain ⟨C, hC, hpre⟩ := T.exists_preimage_norm_le hT
    refine ⟨h, C⁻¹ ^ 2, by positivity, fun x => ?_⟩
    by_cases hx : x = 0
    · subst x
      simp [frameCoefficientEnergy, frameCoefficient]
    obtain ⟨c, hc, hnc⟩ := hpre x
    have hinner : inner 𝕜 x x = inner 𝕜 c (frameAnalysis f h x) := by
      calc
        _ = inner 𝕜 (T c) x := by rw [hc]
        _ = inner 𝕜 c (T.adjoint x) := (T.adjoint_inner_right c x).symm
        _ = _ := by rw [frameSynthesis_adjoint]
    have hnorm : ‖x‖ ≤ C * ‖frameAnalysis f h x‖ := by
      apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hx)).mp
      calc
        ‖x‖ * ‖x‖ = RCLike.re (inner 𝕜 x x) := by rw [inner_self_eq_norm_sq, pow_two]
        _ = RCLike.re (inner 𝕜 c (frameAnalysis f h x)) := congrArg RCLike.re hinner
        _ ≤ ‖c‖ * ‖frameAnalysis f h x‖ := re_inner_le_norm _ _
        _ ≤ (C * ‖x‖) * ‖frameAnalysis f h x‖ := mul_le_mul_of_nonneg_right hnc (norm_nonneg _)
        _ = (C * ‖frameAnalysis f h x‖) * ‖x‖ := by rw [mul_right_comm]
    rw [← norm_sq_frameAnalysis f h, ← mul_pow]
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr
    simpa only [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] using
      mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hC.le)

/-- Synthesis for a frame is surjective. -/
theorem frameSynthesis_surjective (f : ℕ → H) (h : IsFrame (𝕜 := 𝕜) f) :
    Function.Surjective (frameSynthesis f h.1) := by
  intro x
  obtain ⟨c, hc⟩ := ((theorem_12 f).mp h).2 x
  exact ⟨c, (hasSum_frameSynthesis f h.1 c).tsum_eq.symm.trans hc⟩

/-- Unconditional expansions with square-summable coefficients are
unique for a frame exactly when synthesis is injective. -/
theorem frame_coefficients_unique_iff (f : ℕ → H) (h : IsFrame (𝕜 := 𝕜) f) :
    (∀ x : H, ∃! c : ℓ², HasSum (fun n => c n • f n) x) ↔
      Function.Injective (frameSynthesis f h.1) := by
  constructor
  · intro hU c d he
    exact (hU (frameSynthesis f h.1 c)).unique (hasSum_frameSynthesis f h.1 c)
      (he.symm ▸ hasSum_frameSynthesis f h.1 d)
  · intro hI x
    obtain ⟨c, hc⟩ := frameSynthesis_surjective f h x
    refine ⟨c, hc ▸ hasSum_frameSynthesis f h.1 c, fun d hd => hI ?_⟩
    exact ((hasSum_frameSynthesis f h.1 d).unique hd).trans hc.symm

private theorem frameSynthesis_closedRange (f : ℕ → H) (h : IsFrame (𝕜 := 𝕜) f) :
    IsClosed ((frameSynthesis f h.1).range : Set H) := by
  have hr : (frameSynthesis f h.1).range = ⊤ :=
    LinearMap.range_eq_top.mpr (frameSynthesis_surjective f h)
  rw [hr, Submodule.top_coe]
  exact isClosed_univ

/-- The bounded Moore–Penrose inverse of synthesis for a frame. -/
def frameSynthesisInverse (f : ℕ → H) (h : IsFrame (𝕜 := 𝕜) f) : H →L[𝕜] ℓ² :=
  boundedMoorePenroseInverse (frameSynthesis f h.1) (frameSynthesis_closedRange f h)

private theorem frameSynthesis_comp_inverse (f : ℕ → H) (h : IsFrame (𝕜 := 𝕜) f) :
    (frameSynthesis f h.1).comp (frameSynthesisInverse f h) = ContinuousLinearMap.id 𝕜 H := by
  have hp := (boundedMoorePenroseInverse_projections _ (frameSynthesis_closedRange f h)).1
  rw [frameSynthesisInverse, hp]
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  obtain ⟨c, rfl⟩ := frameSynthesis_surjective f h x
  exact Submodule.le_topologicalClosure _ ⟨c, rfl⟩

/-- **Equation (109)** of [benIsrael2003generalized], Chapter 9.
The Moore–Penrose coefficients reconstruct the vector unconditionally. -/
theorem frame_reconstruction_pinv (f : ℕ → H) (h : IsFrame (𝕜 := 𝕜) f) (x : H) :
    HasSum (fun n => frameSynthesisInverse f h x n • f n) x := by
  have hs := hasSum_frameSynthesis f h.1 (frameSynthesisInverse f h x)
  change HasSum _ (((frameSynthesis f h.1).comp (frameSynthesisInverse f h)) x) at hs
  rw [frameSynthesis_comp_inverse] at hs
  exact hs

/-- **Equation (110)** of [benIsrael2003generalized], Chapter 9.
The norm of the inverse frame operator is the squared norm of the
Moore–Penrose inverse of synthesis. -/
theorem frameOperator_inverse_norm (f : ℕ → H) (h : IsFrame (𝕜 := 𝕜) f)
    (S : H ≃L[𝕜] H) (hS : S.toContinuousLinearMap = frameOperator f h.1) :
    ‖S.symm.toContinuousLinearMap‖ = ‖frameSynthesisInverse f h‖ ^ 2 := by
  let T := frameSynthesis f h.1
  let B := frameSynthesisInverse f h
  have hTB (x : H) : T (B x) = x := DFunLike.congr_fun (frameSynthesis_comp_inverse f h) x
  have hBT : T.adjoint.comp B.adjoint = B.comp T := by
    rw [← ContinuousLinearMap.adjoint_comp]
    exact (boundedMoorePenroseInverse_penrose T (frameSynthesis_closedRange f h)).2.2.2
  have he : B.adjoint.comp B = S.symm.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    apply S.injective
    change S (B.adjoint (B x)) = S (S.symm x)
    rw [S.apply_symm_apply]
    change S.toContinuousLinearMap (B.adjoint (B x)) = x
    rw [hS]
    change T ((frameAnalysis f h.1) (B.adjoint (B x))) = x
    rw [← frameSynthesis_adjoint]
    change T ((T.adjoint.comp B.adjoint) (B x)) = x
    rw [hBT, ContinuousLinearMap.comp_apply, hTB, hTB]
  rw [← he, ContinuousLinearMap.norm_adjoint_comp_self, ← sq]

/-- **Equation (110)** of [benIsrael2003generalized], Chapter 9.
On a nontrivial Hilbert space the reciprocal squared synthesis-inverse
norm is positive and is the largest lower frame bound. -/
theorem frame_optimal_lower_bound [Nontrivial H] (f : ℕ → H) (h : IsFrame (𝕜 := 𝕜) f) :
    let a₀ := (‖frameSynthesisInverse f h‖ ^ 2)⁻¹
    0 < a₀ ∧ ∀ a : ℝ,
      (∀ x : H, a * ‖x‖ ^ 2 ≤ frameCoefficientEnergy (𝕜 := 𝕜) f x) ↔ a ≤ a₀ := by
  intro a₀
  let T := frameSynthesis f h.1
  let B := frameSynthesisInverse f h
  have hTB : T.comp B = ContinuousLinearMap.id 𝕜 H := frameSynthesis_comp_inverse f h
  have hBp : 0 < ‖B‖ := norm_pos_iff.mpr fun hB => by
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    apply hx
    have he := DFunLike.congr_fun hTB x
    simpa only [hB, ContinuousLinearMap.comp_zero, zero_apply,
      ContinuousLinearMap.id_apply] using he.symm
  have hpos : 0 < a₀ := inv_pos.mpr (pow_pos hBp _)
  have hnormB : ‖B.adjoint‖ = ‖B‖ := LinearIsometryEquiv.norm_map _ _
  have hBTa : B.adjoint.comp T.adjoint = ContinuousLinearMap.id 𝕜 H := by
    rw [← ContinuousLinearMap.adjoint_comp, hTB, ContinuousLinearMap.adjoint_id]
  have hTBstar : T.adjoint.comp B.adjoint = T.kerᗮ.starProjection := by
    have hBT : B.comp T = T.kerᗮ.starProjection :=
      (boundedMoorePenroseInverse_projections T (frameSynthesis_closedRange f h)).2
    rw [← ContinuousLinearMap.adjoint_comp, hBT]
    exact (isSelfAdjoint_starProjection _).star_eq
  have he (x : H) : ‖T.adjoint x‖ ^ 2 = frameCoefficientEnergy (𝕜 := 𝕜) f x := by
    rw [show T = frameSynthesis f h.1 from rfl, frameSynthesis_adjoint, norm_sq_frameAnalysis]
  have hLower (x : H) : a₀ * ‖x‖ ^ 2 ≤ frameCoefficientEnergy (𝕜 := 𝕜) f x := by
    have hbound : ‖x‖ ≤ ‖B‖ * ‖T.adjoint x‖ := by
      have hc := B.adjoint.le_opNorm (T.adjoint x)
      change ‖(B.adjoint.comp T.adjoint) x‖ ≤ _ at hc
      rwa [hBTa, ContinuousLinearMap.id_apply, hnormB] at hc
    have hh := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hBp.le)
    have hscaled : ‖B‖⁻¹ * ‖x‖ ≤ ‖T.adjoint x‖ := by
      simpa only [← mul_assoc, inv_mul_cancel₀ hBp.ne', one_mul] using hh
    rw [← he, show a₀ = (‖B‖ ^ 2)⁻¹ from rfl, ← inv_pow, ← mul_pow]
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hscaled
  refine ⟨hpos, fun a => ⟨fun ha => ?_, fun hle x => ?_⟩⟩
  · by_cases ha₀ : 0 < a
    · have hBcalc : ‖B.adjoint‖ ≤ (Real.sqrt a)⁻¹ := by
        refine B.adjoint.opNorm_le_bound (by positivity) fun c => ?_
        have hproj : ‖T.adjoint (B.adjoint c)‖ ≤ ‖c‖ := by
          change ‖(T.adjoint.comp B.adjoint) c‖ ≤ _
          rw [hTBstar]
          exact T.kerᗮ.norm_starProjection_apply_le c
        have hsq : a * ‖B.adjoint c‖ ^ 2 ≤ ‖c‖ ^ 2 := by
          have hb := ha (B.adjoint c)
          rw [← he] at hb
          exact hb.trans ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hproj)
        apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
        rw [mul_pow, inv_pow, Real.sq_sqrt ha₀.le]
        calc
          _ = a⁻¹ * (a * ‖B.adjoint c‖ ^ 2) := by rw [← mul_assoc, inv_mul_cancel₀ ha₀.ne', one_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr ha₀.le)
      rw [hnormB] at hBcalc
      have hsq := (sq_le_sq₀ (norm_nonneg B) (by positivity)).mpr hBcalc
      rw [inv_pow, Real.sq_sqrt ha₀.le] at hsq
      apply (inv_le_inv₀ hpos ha₀).mp
      change ((‖B‖ ^ 2)⁻¹)⁻¹ ≤ a⁻¹
      rwa [inv_inv]
    · exact (le_of_not_gt ha₀).trans hpos.le
  · exact (mul_le_mul_of_nonneg_right hle (sq_nonneg _)).trans (hLower x)

end BenIsraelGreville.Chapter09
