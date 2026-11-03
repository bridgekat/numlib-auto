import Numlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecificLimits.Basic
import NumlibSurface.ConnGouldToint.Chapter06.Section03
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.MonotoneConvergence
import Numlib.Optimization.ModelBased.RatioTest

/-! # Relaxed linearization SQP

The normal scaling interval (15.4.12) is used for nonzero trial normal
steps. At a zero trial step we take unit scaling. The left-hand side in
Lemma 15.4.2 is evaluated at the stated Cauchy step.
-/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter15

open Chapter06

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The exact-penalty merit function used in relaxed linearization SQP. -/
noncomputable def sqpMerit (f : E → ℝ) (c : E → F) (σ : ℝ) (x : E) : ℝ :=
  f x + σ * ‖c x‖

/-- The normal model measures the residual of the linearized constraint. -/
noncomputable def sqpNormalModel (c : F) (A : E →L[ℝ] F) (n : E) : ℝ :=
  ‖c + A n‖

/-- The overall relaxed SQP model (15.4.4). -/
noncomputable def sqpOverallModel (f₀ : ℝ) (g : E) (H : E →L[ℝ] E)
    (c : F) (A : E →L[ℝ] F) (σ : ℝ) (s : E) : ℝ :=
  quadraticModel f₀ g H.toLinearMap s + σ * sqpNormalModel c A s

/-- The tangential model (15.4.5) after taking the normal step. -/
noncomputable def sqpTangentialModel (g : E) (H : E →L[ℝ] E) (n t : E) : ℝ :=
  quadraticModel 0 (g + H n) H.toLinearMap t

/-- The overall decrease splits into the tangential decrease, the
penalized normal feasibility decrease, and the normal objective decrease. -/
theorem sqpOverallModel_decrease (f₀ σ : ℝ) (g : E) (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric) (c : F) (A : E →L[ℝ] F) (n t : E) (ht : A t = 0) :
    sqpOverallModel f₀ g H c A σ 0 - sqpOverallModel f₀ g H c A σ (n + t) =
      (sqpTangentialModel g H n 0 - sqpTangentialModel g H n t) +
      σ * (sqpNormalModel c A 0 - sqpNormalModel c A n) +
      (quadraticModel f₀ g H.toLinearMap 0 - quadraticModel f₀ g H.toLinearMap n) := by
  have hs : ⟪n, H t⟫ = ⟪H n, t⟫ := (hH n t).symm
  simp [sqpOverallModel, sqpNormalModel, sqpTangentialModel, quadraticModel,
    inner_add_left, inner_add_right, ht, hs, real_inner_comm t (H n)]
  ring

/-- The penalty threshold (15.4.8) for a strictly positive normal decrease. -/
noncomputable def sqpPenaltyThreshold (ν dN dT dq : ℝ) : ℝ :=
  -(dq + dT) / ((1 - ν) * dN)

/-- Equation (15.4.7) holds exactly above the threshold (15.4.8). -/
theorem sqpPenaltyThreshold_le_iff {ν dN dT dq σ : ℝ} (hν : ν < 1) (hN : 0 < dN) :
    sqpPenaltyThreshold ν dN dT dq ≤ σ ↔ ν * σ * dN ≤ dT + σ * dN + dq := by
  unfold sqpPenaltyThreshold
  rw [div_le_iff₀ (mul_pos (sub_pos.mpr hν) hN)]
  constructor <;> intro h <;> linarith only [show σ * ((1 - ν) * dN) =
    σ * dN - ν * σ * dN by ring, h]

/-- AA.1h, with unit scaling at a zero trial normal step. -/
def IsSQPNormalScaling (nC : E) (θ ξ Δ α : ℝ) : Prop :=
  open Classical in
  if nC = 0 then α = 1 else
    α ∈ Set.Icc (min 1 (θ * ξ * Δ / ‖nC‖)) (min 1 (ξ * Δ / ‖nC‖))

/-- The exact reduction identity (15.4.16). -/
theorem sqpNormalModel_decrease_scaled {c : F} {A : E →L[ℝ] F} {nC : E} {α : ℝ}
    (hlin : A nC + c = 0) (hα : α ≤ 1) :
    sqpNormalModel c A 0 - sqpNormalModel c A (α • nC) = α * ‖c‖ := by
  have hn : A nC = -c := eq_neg_of_add_eq_zero_left hlin
  simp only [sqpNormalModel, map_zero, add_zero, map_smul, hn]
  rw [show c + α • (-c) = (1 - α) • c by rw [smul_neg, sub_smul, one_smul, sub_eq_add_neg],
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hα)]
  ring

/-- Lemma 15.4.1, including the case in which the trial step vanishes. -/
theorem lemma_15_4_1 {c : F} {A : E →L[ℝ] F} {nC : E} {θ ξ Δ α κ : ℝ}
    (hθ : 0 ≤ θ) (hξ : 0 ≤ ξ) (hΔ : 0 ≤ Δ) (hκ : 0 < κ)
    (hlin : A nC + c = 0) (hbound : ‖nC‖ ≤ κ * ‖c‖)
    (hscale : IsSQPNormalScaling nC θ ξ Δ α) :
    let dN := sqpNormalModel c A 0 - sqpNormalModel c A (α • nC)
    min ‖c‖ (θ * ξ / κ * Δ) ≤ dN ∧ dN ≤ ‖c‖ := by
  by_cases hn : nC = 0
  · have hc : c = 0 := by simpa [hn] using hlin
    simp [hc, hn, sqpNormalModel]
  have hn' : 0 < ‖nC‖ := norm_pos_iff.mpr hn
  simp only [IsSQPNormalScaling, ite_eq_right hn, Set.mem_Icc] at hscale
  have hα : α ≤ 1 := hscale.2.trans (min_le_left _ _)
  dsimp only
  rw [sqpNormalModel_decrease_scaled hlin hα]
  refine ⟨?_, mul_le_of_le_one_left (norm_nonneg c) hα⟩
  have hcompare : θ * ξ / κ * Δ ≤ (θ * ξ * Δ / ‖nC‖) * ‖c‖ := by
    have hh := mul_le_mul_of_nonneg_left hbound (show 0 ≤ θ * ξ * Δ by positivity)
    field_simp
    nlinarith only [hh]
  have h := mul_le_mul_of_nonneg_right hscale.1 (norm_nonneg c)
  rw [min_mul_of_nonneg _ _ (norm_nonneg c), one_mul] at h
  exact (min_le_min le_rfl hcompare).trans h

/-- Lemma 15.4.2 applies the Cauchy decrease estimate in null-space coordinates.
The map N is injective because its columns form a basis of the null space. -/
theorem lemma_15_4_2 {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (N : Z →L[ℝ] E) (hN : Function.Injective N) (g : Z) (H : Z →L[ℝ] Z)
    {R : ℝ} (hR : 0 ≤ R) {zC : Z}
    (hC : IsCauchyPoint (quadraticModel 0 g H.toLinearMap)
      ((normSeminorm ℝ E).comp N.toLinearMap) g R zC) :
    (1 / 2) * ‖g‖ * min (R / ‖N‖) (‖g‖ / quadraticCurvatureBound H) ≤
      0 - quadraticModel 0 g H.toLinearMap zC := by
  let p := (normSeminorm ℝ E).comp N.toLinearMap
  have hp (v : Z) (hv : p v = 0) : v = 0 := by
    change ‖N v‖ = 0 at hv
    exact hN ((norm_eq_zero.mp hv).trans N.map_zero.symm)
  have h := theorem_6_3_1 0 g H p hp hR hC
  by_cases hg : g = 0
  · simpa [hg] using h
  have hpg : 0 < ‖N g‖ := norm_pos_iff.mpr (fun hz => hg (hN (hz.trans N.map_zero.symm)))
  have hN' : 0 < ‖N‖ := by
    have hNnorm := N.le_opNorm g
    by_contra! hzero
    linarith [mul_nonpos_of_nonpos_of_nonneg hzero (norm_nonneg g)]
  have hratio : R / ‖N‖ ≤ cauchyNormRatio p g * R := by
    unfold cauchyNormRatio
    change R / ‖N‖ ≤ ‖g‖ / ‖N g‖ * R
    have hmul := mul_le_mul_of_nonneg_right (N.le_opNorm g) hR
    field_simp
    nlinarith only [hmul]
  rw [min_comm (R / ‖N‖)]
  exact (mul_le_mul_of_nonneg_left (min_le_min le_rfl hratio) (by positivity)).trans h

/-- Lemma 15.4.3. The Taylor assumptions are imposed on the full trial
segment, including trial points that the algorithm may reject. -/
theorem lemma_15_4_3 [CompleteSpace E] {f : E → ℝ} {c : E → F} {x s : E}
    (H : E →L[ℝ] E) {σ Δ ξ Lf Lc B : ℝ}
    (hσ : 0 ≤ σ) (hs : ‖s‖ ≤ ξ * Δ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ f (x + t • s))
    (hc : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ c (x + t • s))
    (hLf : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ f (x + t • s) - fderiv ℝ f x‖ ≤ Lf * (t * ‖s‖))
    (hLc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ c (x + t • s) - fderiv ℝ c x‖ ≤ Lc * (t * ‖s‖))
    (hLc₀ : 0 ≤ Lc) (hH : ‖H‖ ≤ B) :
    let κ := max ((Lf + B) / 2) (Lc / 2)
    let err := |sqpMerit f c σ (x + s) -
      sqpOverallModel (f x) (gradient f x) H (c x) (fderiv ℝ c x) σ s|
    err ≤ κ * (1 + σ) * ‖s‖ ^ 2 ∧ err ≤ ξ ^ 2 * κ * (1 + σ) * Δ ^ 2 := by
  let κ := max ((Lf + B) / 2) (Lc / 2)
  have hκ : 0 ≤ κ := (by linarith : 0 ≤ Lc / 2).trans (le_max_right _ _)
  have hF := norm_sub_firstOrder_le_of_lipschitz_on_segment hf hLf
  have hC := norm_sub_firstOrder_le_of_lipschitz_on_segment hc hLc
  have hh : |⟪s, H s⟫| ≤ B * ‖s‖ ^ 2 := calc
    _ ≤ ‖s‖ * ‖H s‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖s‖ * (‖H‖ * ‖s‖) := mul_le_mul_of_nonneg_left (H.le_opNorm _) (norm_nonneg _)
    _ = ‖H‖ * ‖s‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hH (sq_nonneg _)
  have hobj : |f (x + s) - quadraticModel (f x) (gradient f x) H.toLinearMap s| ≤
      ((Lf + B) / 2) * ‖s‖ ^ 2 := by
    rw [Real.norm_eq_abs] at hF
    simp only [quadraticModel, ContinuousLinearMap.coe_coe, inner_gradient_left]
    rw [← sub_sub]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    nlinarith only [hF, hh]
  have hcon : |‖c (x + s)‖ - sqpNormalModel (c x) (fderiv ℝ c x) s| ≤
      Lc / 2 * ‖s‖ ^ 2 := by
    unfold sqpNormalModel
    exact (abs_norm_sub_norm_le _ _).trans (by convert hC using 1; ring)
  have herr : |sqpMerit f c σ (x + s) -
      sqpOverallModel (f x) (gradient f x) H (c x) (fderiv ℝ c x) σ s| ≤
      κ * (1 + σ) * ‖s‖ ^ 2 := by
    unfold sqpMerit sqpOverallModel
    rw [show f (x + s) + σ * ‖c (x + s)‖ -
        (quadraticModel (f x) (gradient f x) H.toLinearMap s +
          σ * sqpNormalModel (c x) (fderiv ℝ c x) s) =
        (f (x + s) - quadraticModel (f x) (gradient f x) H.toLinearMap s) +
          σ * (‖c (x + s)‖ - sqpNormalModel (c x) (fderiv ℝ c x) s) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hσ]
    have h₁ := hobj.trans (mul_le_mul_of_nonneg_right (le_max_left ((Lf + B) / 2) (Lc / 2)) (sq_nonneg ‖s‖))
    have h₂ := hcon.trans (mul_le_mul_of_nonneg_right (le_max_right ((Lf + B) / 2) (Lc / 2)) (sq_nonneg ‖s‖))
    nlinarith only [h₁, mul_le_mul_of_nonneg_left h₂ hσ]
  refine ⟨herr, herr.trans ?_⟩
  calc
    _ ≤ κ * (1 + σ) * (ξ * Δ) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hs 2) (by positivity)
    _ = _ := by ring

omit [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
/-- Lemma 15.4.4. At a fixed iterate, the feasible case uses a nonzero
reduced gradient and a bounded penalty. The infeasible case uses the
penalty-weighted normal decrease, so the penalty need not be bounded above. -/
theorem lemma_15_4_4 (f : E → ℝ) (c : E → F) (x : E)
    (s : ℝ → E) (m : ℝ → E → ℝ) (σ : ℝ → ℝ)
    {η C σmin : ℝ} (hη : η < 1) (hC : 0 ≤ C) (hmin : 0 < σmin)
    (hσ : ∀ r > 0, σmin ≤ σ r)
    (hcenter : ∀ r > 0, m r 0 = sqpMerit f c (σ r) x)
    (herr : ∀ r > 0, |sqpMerit f c (σ r) (x + s r) - m r (s r)| ≤
      C * (1 + σ r) * r ^ 2)
    (hcase :
      (c x = 0 ∧ ∃ G R β ξ κ S : ℝ,
        0 < G ∧ 0 < R ∧ 0 < β ∧ 0 < ξ ∧ 0 < κ ∧ 0 ≤ S ∧
        ∀ r > 0, σ r ≤ S ∧ κ * G * min (ξ * r / R) (G / β) ≤ m r 0 - m r (s r)) ∨
      (c x ≠ 0 ∧ ∃ ν b : ℝ, 0 < ν ∧ 0 < b ∧
        ∀ r > 0, ν * σ r * min ‖c x‖ (b * r) ≤ m r 0 - m r (s r))) :
    ∃ r₀ > 0, ∀ r ∈ Set.Ioc (0 : ℝ) r₀,
      η ≤ Optimization.reductionRatio (sqpMerit f c (σ r)) x (s r) (m r 0 - m r (s r)) := by
  suffices ∃ a > 0, ∃ b > 0, ∀ r ∈ Set.Ioc (0 : ℝ) b,
      a * (1 + σ r) * r ≤ m r 0 - m r (s r) by
    obtain ⟨a, ha, b, hb, hlin⟩ := this
    let r₀ := min b ((1 - η) * a / (C + 1))
    refine ⟨r₀, lt_min hb (by positivity), ?_⟩
    intro r hr
    have hrb : r ∈ Set.Ioc (0 : ℝ) b := ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
    have hd := hlin r hrb
    have hp : 0 < m r 0 - m r (s r) :=
      (mul_pos (mul_pos ha (by linarith [hσ r hr.1])) hr.1).trans_le hd
    have hsmall := (le_div_iff₀ (by positivity : 0 < C + 1)).mp
      (hr.2.trans (min_le_right _ _))
    have hcr : C * r ≤ (1 - η) * a := by
      linarith only [hsmall, hr.1]
    have hσ' : 0 ≤ 1 + σ r := by linarith [hσ r hr.1]
    have he : |sqpMerit f c (σ r) (x + s r) -
        (sqpMerit f c (σ r) x - (m r 0 - m r (s r)))| ≤
        (1 - η) * (m r 0 - m r (s r)) := by
      rw [← hcenter r hr.1, sub_sub_cancel]
      refine (herr r hr.1).trans ?_
      have hscale := mul_le_mul_of_nonneg_right hcr (mul_nonneg hσ' hr.1.le)
      have hpred := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hη.le)
      nlinarith only [hscale, hpred]
    have h := Optimization.le_reductionRatio_of_abs_sub_le hp he
    linarith only [h]
  rcases hcase with ⟨_, G, R, β, ξ, κ, S, hG, hR, hβ, hξ, hκ, hS, hdec⟩ |
    ⟨hc, ν, b, hν, hb, hdec⟩
  · let a := κ * G * ξ / (R * (1 + S))
    let b := (G / β) * R / ξ
    have ha : 0 < a := by dsimp [a]; positivity
    have hb : 0 < b := by dsimp [b]; positivity
    refine ⟨a, ha, b, hb, fun r hr => ?_⟩
    obtain ⟨hS', hdrop⟩ := hdec r hr.1
    have hm : ξ * r / R ≤ G / β := by
      apply (div_le_iff₀ hR).mpr
      have hh := (le_div_iff₀ hξ).mp (show r ≤ (G / β) * R / ξ from hr.2)
      rwa [mul_comm ξ r]
    rw [min_eq_left hm] at hdrop
    calc
      _ ≤ a * (1 + S) * r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) ha.le) hr.1.le
      _ = κ * G * (ξ * r / R) := by
        dsimp [a]
        field_simp
      _ ≤ _ := hdrop
  · let a := ν * b * (σmin / (1 + σmin))
    refine ⟨a, by dsimp [a]; positivity, ‖c x‖ / b,
      div_pos (norm_pos_iff.mpr hc) hb, fun r hr => ?_⟩
    have hm : b * r ≤ ‖c x‖ := by
      rw [mul_comm]
      exact (le_div_iff₀ hb).mp hr.2
    have hσr := hσ r hr.1
    have hfrac : σmin / (1 + σmin) * (1 + σ r) ≤ σ r := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 1 + σmin)).mpr
      linarith only [hσr]
    have hdrop := hdec r hr.1
    rw [min_eq_right hm] at hdrop
    calc
      _ = (ν * b * r) * (σmin / (1 + σmin) * (1 + σ r)) := by dsimp [a]; ring
      _ ≤ (ν * b * r) * σ r :=
        mul_le_mul_of_nonneg_left hfrac (by positivity [hr.1])
      _ = ν * σ r * (b * r) := by ring
      _ ≤ _ := hdrop

/-- The normalized merit of Section 15.4.1.4. -/
noncomputable def sqpNormalizedMerit (f : E → ℝ) (c : E → F) (fmin σ : ℝ) (x : E) : ℝ :=
  (sqpMerit f c σ x - fmin) / σ

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
/-- Lemma 15.4.5 on the subsequence of successful iterates. Rejected
iterations leave the iterate unchanged, so the reduction condition
compares consecutive points of this subsequence at the old penalty. -/
theorem lemma_15_4_5 (f : E → ℝ) (c : E → F) (x : ℕ → E) (σ d : ℕ → ℝ)
    {fmin η : ℝ} (hf : ∀ i, fmin ≤ f (x i)) (hσ : ∀ i, 0 < σ i) (hmono : Monotone σ)
    (hη : 0 ≤ η) (hd : ∀ i, 0 ≤ d i)
    (haccept : ∀ i, η * d i ≤ sqpMerit f c (σ i) (x i) - sqpMerit f c (σ i) (x (i + 1))) :
    (∀ i, 0 ≤ sqpNormalizedMerit f c fmin (σ i) (x i)) ∧
    ∀ i j : ℕ, 0 < j →
      sqpNormalizedMerit f c fmin (σ (i + j)) (x (i + j)) ≤
        sqpNormalizedMerit f c fmin (σ i) (x i) - η * (d i / σ i) := by
  let v (i : ℕ) := sqpNormalizedMerit f c fmin (σ i) (x i)
  have hexpand (s : ℝ) (hs : s ≠ 0) (z : E) :
      sqpNormalizedMerit f c fmin s z = (f z - fmin) / s + ‖c z‖ := by
    unfold sqpNormalizedMerit sqpMerit
    field_simp
    ring
  have hstep (i : ℕ) : v (i + 1) ≤ v i - η * (d i / σ i) := by
    calc
      _ ≤ sqpNormalizedMerit f c fmin (σ i) (x (i + 1)) := by
        simp only [v, hexpand _ (hσ _).ne']
        exact add_le_add (div_le_div_of_nonneg_left (sub_nonneg.mpr (hf _))
          (hσ i) (hmono (Nat.le_succ i))) le_rfl
      _ ≤ _ := by
        dsimp [v, sqpNormalizedMerit]
        rw [← mul_div_assoc, ← sub_div]
        apply (div_le_div_iff_of_pos_right (hσ i)).mpr
        linarith only [haccept i]
  have hanti : Antitone v := antitone_nat_of_succ_le
    (fun i => (hstep i).trans (sub_le_self _ (mul_nonneg hη (div_nonneg (hd i) (hσ i).le))))
  refine ⟨fun i => ?_, fun i j hj => ?_⟩
  · rw [hexpand _ (hσ i).ne']
    exact add_nonneg (div_nonneg (sub_nonneg.mpr (hf i)) (hσ i).le) (norm_nonneg _)
  · exact (hanti (Nat.add_le_add_left hj i)).trans (hstep i)

private def HasRelaxedProgress (u v Δ : ℕ → ℝ) (S : Set ℕ) : Prop :=
  ∀ ε > 0, ∃ (a b e r : ℝ) (K : ℕ), 0 < a ∧ 0 < b ∧ 0 < e ∧ 0 < r ∧
    ∀ k ≥ K, ε ≤ u k →
      (Δ k ≤ r → k ∈ S ∧ Δ k ≤ Δ (k + 1)) ∧
      (k ∈ S → a * min e (b * Δ k) ≤ v k - v (k + 1))

private theorem relaxed_progress_frequently_small {u v Δ : ℕ → ℝ} {S : Set ℕ}
    {γ γ₂ : ℝ} (hγ : 0 < γ) (hγ₂ : 0 ≤ γ₂) (hγ₂' : γ₂ < 1)
    (hv : ∀ k, 0 ≤ v k) (hΔ : ∀ k, 0 < Δ k)
    (hmono : Antitone v) (hnext : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hrej : ∀ k ∉ S, Δ (k + 1) ≤ γ₂ * Δ k)
    (hcontrol : HasRelaxedProgress u v Δ S) (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ k ≥ N₀, u k < ε := by
  have hbdd : BddBelow (Set.range v) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hv k⟩
  have hlim := tendsto_atTop_ciInf hmono hbdd
  have hdiff : Filter.Tendsto (fun k => v k - v (k + 1)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, sub_self] using
      hlim.sub (hlim.comp (Filter.tendsto_add_atTop_nat 1))
  by_contra! hfail
  obtain ⟨a, b, e, r, K, ha, hb, he, hr, hcontrol⟩ := hcontrol ε hε
  let N := max K N₀
  let d := min (Δ N) (γ * r)
  have hd : 0 < d := lt_min (hΔ N) (mul_pos hγ hr)
  have hfloor (k : ℕ) (hk : N ≤ k) : d ≤ Δ k := by
    induction k, hk using Nat.le_induction with
    | base => exact min_le_left _ _
    | succ k hk ih =>
      by_cases h : Δ k ≤ r
      · exact ih.trans ((hcontrol k ((le_max_left _ _).trans hk)
          (hfail k ((le_max_right _ _).trans hk))).1 h).2
      · exact (min_le_right _ _).trans
          ((mul_le_mul_of_nonneg_left (lt_of_not_ge h).le hγ.le).trans (hnext k))
  have hpos : 0 < a * min e (b * d) := mul_pos ha (lt_min he (mul_pos hb hd))
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp (hdiff.eventually (gt_mem_nhds hpos))
  let M := max J N
  have hstop (k : ℕ) (hk : M ≤ k) : k ∉ S := by
    intro h
    have hkN := (le_max_right _ _).trans hk
    have hlow : a * min e (b * d) ≤ a * min e (b * Δ k) := mul_le_mul_of_nonneg_left
      (min_le_min le_rfl (mul_le_mul_of_nonneg_left (hfloor k hkN) hb.le)) ha.le
    exact (not_le_of_gt (hJ k ((le_max_left _ _).trans hk))) (hlow.trans ((hcontrol k ((le_max_left _ _).trans hkN)
      (hfail k ((le_max_right _ _).trans hkN))).2 h))
  have hpow (j : ℕ) : Δ (M + j) ≤ γ₂ ^ j * Δ M := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hmj : M ≤ M + j := Nat.le_add_right _ _
      change Δ (M + j + 1) ≤ γ₂ ^ (j + 1) * Δ M
      rw [pow_succ', mul_assoc]
      exact (hrej (M + j) (hstop _ hmj)).trans
        (mul_le_mul_of_nonneg_left ih hγ₂)
  have hzero : Filter.Tendsto (fun j => γ₂ ^ j * Δ M) Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hγ₂ hγ₂').mul_const (Δ M)
  obtain ⟨j, hj⟩ := (hzero.eventually (gt_mem_nhds hd)).exists
  have hm : N ≤ M + j := (le_max_right J N).trans (Nat.le_add_right _ _)
  exact (not_le_of_gt hj) ((hfloor _ hm).trans (hpow j))

private theorem tendsto_zero_of_relaxed_steps {u v Δ : ℕ → ℝ} {S : Set ℕ}
    {L γ γ₂ : ℝ} (hL : 0 ≤ L)
    (hγ : 0 < γ) (hγ₂ : 0 ≤ γ₂) (hγ₂' : γ₂ < 1)
    (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k) (hΔ : ∀ k, 0 < Δ k)
    (hmono : Antitone v) (hnext : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hrej : ∀ k ∉ S, Δ (k + 1) ≤ γ₂ * Δ k ∧ u (k + 1) = u k)
    (hmove : ∀ k ∈ S, u k - u (k + 1) ≤ L * Δ k)
    (hcontrol : HasRelaxedProgress u v Δ S) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  have hbdd : BddBelow (Set.range v) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hv k⟩
  have hlim := tendsto_atTop_ciInf hmono hbdd
  have hdiff : Filter.Tendsto (fun k => v k - v (k + 1)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, sub_self] using
      hlim.sub (hlim.comp (Filter.tendsto_add_atTop_nat 1))
  have htail : Filter.Tendsto (fun k => v k - ⨅ j, v j) Filter.atTop (nhds 0) := by
    simpa using hlim.sub_const (⨅ j, v j)
  have hfreq := relaxed_progress_frequently_small hγ hγ₂ hγ₂' hv hΔ hmono hnext
    (fun k hk => (hrej k hk).1) hcontrol
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let e := ε / 2
  have he : 0 < e := half_pos hε
  obtain ⟨a, b, e₀, r, K, ha, hb, he₀, hr, hc⟩ := hcontrol e he
  let C := L / (a * b)
  have hC : 0 ≤ C := div_nonneg hL (mul_nonneg ha.le hb.le)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hdiff.eventually (gt_mem_nhds (mul_pos ha he₀)))
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp
    (htail.eventually (gt_mem_nhds (div_pos he (by positivity : 0 < C + 1))))
  have hlocal (k : ℕ) (hk : max N K ≤ k) (hhigh : e ≤ u k) :
      u k - u (k + 1) ≤ C * (v k - v (k + 1)) := by
    by_cases hs : k ∈ S
    · have hdrop := (hc k ((le_max_right _ _).trans hk) hhigh).2 hs
      have hΔe : b * Δ k < e₀ := by
        by_contra! hh
        have hh' := mul_le_mul_of_nonneg_left (le_min le_rfl hh) ha.le
        exact (not_le_of_gt (hN k ((le_max_left _ _).trans hk))) (hh'.trans hdrop)
      rw [min_eq_right hΔe.le] at hdrop
      refine (hmove k hs).trans ?_
      have h := mul_le_mul_of_nonneg_left hdrop hC
      have hid : C * (a * (b * Δ k)) = L * Δ k := by
        dsimp [C]
        field_simp
      rwa [hid] at h
    · rw [(hrej k hs).2, sub_self]
      exact mul_nonneg hC (sub_nonneg.mpr (hmono (Nat.le_succ k)))
  refine ⟨max (max N K) J, fun k hk => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hu k)]
  by_contra! hhigh
  let j := Nat.find (hfreq e he k)
  have hj : k ≤ j ∧ u j < e := Nat.find_spec (hfreq e he k)
  have htel (i : ℕ) (hi : k ≤ i) : i ≤ j → u k - u i ≤ C * (v k - v i) := by
    induction i, hi using Nat.le_induction with
    | base => simp
    | succ i hi ih =>
      intro hij
      have hlt : i < j := Nat.lt_of_succ_le hij
      have hhi : e ≤ u i := le_of_not_gt fun h => Nat.find_min (hfreq e he k) hlt ⟨hi, h⟩
      linarith only [ih hlt.le, hlocal i (((le_max_left _ _).trans hk).trans hi) hhi]
  have hlow : e < u k - u j := by dsimp [e] at hj ⊢; linarith [hj.2]
  have hupper : C * (v k - v j) < e := calc
    _ ≤ (C + 1) * (v k - v j) :=
      mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr (hmono hj.1))
    _ ≤ (C + 1) * (v k - ⨅ i, v i) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left (ciInf_le hbdd j) _) (by positivity)
    _ < _ := by
      rw [mul_comm]
      exact (lt_div_iff₀ (by positivity : 0 < C + 1)).mp (hJ k ((le_max_right _ _).trans hk))
  exact (not_lt_of_ge (htel j hj.1 le_rfl)) (hupper.trans hlow)

omit [InnerProductSpace ℝ E] [NormedSpace ℝ F] in
/-- Theorem 15.4.6 for the relaxed-linearization run. The model lower bound
combines (15.4.7) and Lemma 15.4.1. The uniform quadratic error bound is
the second inequality of Lemma 15.4.3. The variation bound on constraints
is required only on steps actually taken. -/
theorem theorem_15_4_6 (f : E → ℝ) (c : E → F) (x s : ℕ → E) (σ d Δ : ℕ → ℝ)
    (S : Set ℕ) {fmin σmin η η₂ ν b C L γ γ₂ : ℝ}
    (hη : 0 < η) (hη₂ : η ≤ η₂) (hη₂' : η₂ < 1) (hν : 0 < ν) (hb : 0 < b) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hσmin : 0 < σmin) (hγ : 0 < γ) (hγ₂ : 0 ≤ γ₂) (hγ₂' : γ₂ < 1)
    (hf : ∀ k, fmin ≤ f (x k)) (hσ : ∀ k, σmin ≤ σ k) (hσmono : Monotone σ)
    (hΔ : ∀ k, 0 < Δ k)
    (hratio : ∀ k, k ∈ S ↔ η ≤ Optimization.reductionRatio
      (sqpMerit f c (σ k)) (x k) (s k) (d k))
    (hpred : ∀ k, ν * σ k * min ‖c (x k)‖ (b * Δ k) ≤ d k)
    (herr : ∀ k, |sqpMerit f c (σ k) (x k + s k) -
      (sqpMerit f c (σ k) (x k) - d k)| ≤ C * (1 + σ k) * (Δ k) ^ 2)
    (hnext : ∀ k, γ * Δ k ≤ Δ (k + 1))
    (hacc : ∀ k ∈ S, x (k + 1) = x k + s k)
    (hvery : ∀ k, η₂ ≤ Optimization.reductionRatio
      (sqpMerit f c (σ k)) (x k) (s k) (d k) → Δ k ≤ Δ (k + 1))
    (hrej : ∀ k ∉ S, x (k + 1) = x k ∧ Δ (k + 1) ≤ γ₂ * Δ k)
    (hmove : ∀ k ∈ S, ‖c (x k + s k) - c (x k)‖ ≤ L * Δ k) :
    Filter.Tendsto (fun k => c (x k)) Filter.atTop (nhds 0) := by
  let u (k : ℕ) := ‖c (x k)‖
  let v (k : ℕ) := sqpNormalizedMerit f c fmin (σ k) (x k)
  let p := ν * (σmin / (1 + σmin))
  have hp : 0 < p := by dsimp [p]; positivity
  have hσpos (k : ℕ) := hσmin.trans_le (hσ k)
  have hfrac (k : ℕ) : p * (1 + σ k) ≤ ν * σ k := by
    have hh : σmin / (1 + σmin) * (1 + σ k) ≤ σ k := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 1 + σmin)).mpr
      linarith only [hσ k]
    rw [show p * (1 + σ k) = ν * (σmin / (1 + σmin) * (1 + σ k)) by dsimp [p]; ring]
    exact mul_le_mul_of_nonneg_left hh hν.le
  have hdecrease (k : ℕ) : p * (1 + σ k) * min (u k) (b * Δ k) ≤ d k :=
    (mul_le_mul_of_nonneg_right (hfrac k)
      (le_min (norm_nonneg _) (mul_nonneg hb.le (hΔ k).le))).trans (hpred k)
  have hexpand (r : ℝ) (hr : r ≠ 0) (z : E) :
      sqpNormalizedMerit f c fmin r z = (f z - fmin) / r + ‖c z‖ := by
    unfold sqpNormalizedMerit sqpMerit
    field_simp
    ring
  have hcompare (k : ℕ) : v (k + 1) ≤ sqpNormalizedMerit f c fmin (σ k) (x (k + 1)) := by
    simp only [v, hexpand _ (hσpos _).ne']
    exact add_le_add
      (div_le_div_of_nonneg_left (sub_nonneg.mpr (hf _)) (hσpos _) (hσmono (Nat.le_succ _)))
      le_rfl
  have hdrop (k : ℕ) (hk : k ∈ S) : η * p * min (u k) (b * Δ k) ≤ v k - v (k + 1) := by
    have hge : 0 ≤ d k := (mul_nonneg (mul_nonneg hp.le (by positivity [hσpos k]))
      (le_min (norm_nonneg _) (mul_nonneg hb.le (hΔ k).le))).trans (hdecrease k)
    have hpos : 0 < d k := by
      by_contra! hz
      have hzero := le_antisymm hz hge
      have hbad := (hratio k).mp hk
      simp [Optimization.reductionRatio, hzero, not_le_of_gt hη] at hbad
    have hactual := (le_div_iff₀ hpos).mp ((hratio k).mp hk)
    change η * d k ≤ sqpMerit f c (σ k) (x k) -
      sqpMerit f c (σ k) (x k + s k) at hactual
    rw [← hacc k hk] at hactual
    have hnorm : sqpNormalizedMerit f c fmin (σ k) (x (k + 1)) ≤ v k - η * (d k / σ k) := by
      dsimp [v, sqpNormalizedMerit]
      rw [← mul_div_assoc, ← sub_div]
      exact (div_le_div_iff_of_pos_right (hσpos k)).mpr (by linarith)
    have hd : p * min (u k) (b * Δ k) ≤ d k / σ k := by
      apply (le_div_iff₀ (hσpos k)).mpr
      have hh := mul_le_mul_of_nonneg_right
        (show σ k ≤ 1 + σ k by linarith)
        (mul_nonneg hp.le (le_min (norm_nonneg (c (x k))) (mul_nonneg hb.le (hΔ k).le)))
      nlinarith only [hh, hdecrease k]
    have h := mul_le_mul_of_nonneg_left hd hη.le
    linarith only [h, (hcompare k).trans hnorm]
  have hmono : Antitone v := antitone_nat_of_succ_le fun k => by
    by_cases hk : k ∈ S
    · have h := hdrop k hk
      have hn : 0 ≤ η * p * min (u k) (b * Δ k) := by
        exact mul_nonneg (mul_nonneg hη.le hp.le)
          (le_min (norm_nonneg _) (mul_nonneg hb.le (hΔ k).le))
      linarith
    · have h := hcompare k
      rwa [(hrej k hk).1] at h
  have hsmall (ε : ℝ) (hε : 0 < ε) :
      ∃ r > 0, ∀ k, ε ≤ u k → Δ k ≤ r → k ∈ S ∧ Δ k ≤ Δ (k + 1) := by
    let r := min (ε / b) ((1 - η₂) * p * b / (C + 1))
    refine ⟨r, lt_min (div_pos hε hb) (by positivity), fun k hu hk => ?_⟩
    have hm : b * Δ k ≤ u k := by
      have hh := (le_div_iff₀ hb).mp (hk.trans (min_le_left _ _))
      exact (by simpa only [mul_comm] using hh : b * Δ k ≤ ε).trans hu
    have hd := hdecrease k
    rw [min_eq_right hm] at hd
    have hs : 0 < 1 + σ k := by positivity [hσpos k]
    have hpos := (mul_pos (mul_pos hp hs) (mul_pos hb (hΔ k))).trans_le hd
    have hCΔ : C * Δ k ≤ (1 - η₂) * p * b := by
      have hh := (le_div_iff₀ (by positivity : 0 < C + 1)).mp (hk.trans (min_le_right _ _))
      linarith only [hh, hΔ k]
    have hbound := mul_le_mul_of_nonneg_right hCΔ (mul_nonneg hs.le (hΔ k).le)
    have hbound' := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hη₂'.le)
    have hv : η₂ ≤ Optimization.reductionRatio
        (sqpMerit f c (σ k)) (x k) (s k) (d k) := by
      have h := Optimization.le_reductionRatio_of_abs_sub_le hpos
        ((herr k).trans (by nlinarith only [hbound, hbound']))
      linarith only [h]
    exact ⟨(hratio k).mpr (hη₂.trans hv), hvery k hv⟩
  have hcontrol : HasRelaxedProgress u v Δ S := by
    intro ε hε
    obtain ⟨r, hr, hs⟩ := hsmall ε hε
    refine ⟨η * p, b, ε, r, 0, mul_pos hη hp, hb, hε, hr, fun k _ hk => ⟨hs k hk, ?_⟩⟩
    intro hS
    exact (mul_le_mul_of_nonneg_left (min_le_min_right _ hk) (mul_nonneg hη.le hp.le)).trans
      (hdrop k hS)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_zero_of_relaxed_steps hL hγ hγ₂ hγ₂'
    (fun k => norm_nonneg _) ?_ hΔ hmono hnext
    (fun k hk => ⟨(hrej k hk).2, by simp only [(hrej k hk).1]⟩) ?_ hcontrol
  · intro k
    rw [show v k = sqpNormalizedMerit f c fmin (σ k) (x k) from rfl,
      hexpand _ (hσpos k).ne']
    exact add_nonneg (div_nonneg (sub_nonneg.mpr (hf k)) (hσpos k).le) (norm_nonneg _)
  · intro k hk
    change ‖c (x k)‖ - ‖c (x (k + 1))‖ ≤ _
    rw [hacc k hk]
    calc
      _ ≤ ‖c (x k) - c (x k + s k)‖ := norm_sub_norm_le _ _
      _ = ‖c (x k + s k) - c (x k)‖ := norm_sub_rev _ _
      _ ≤ _ := hmove k hk

/-- Lemma 15.4.7. The exact reduction identity gives the stronger coefficient
1 / κ directly, regardless of which radius bound is active. -/
theorem lemma_15_4_7 {c : F} {A : E →L[ℝ] F} {nC : E} {α κ : ℝ}
    (hκ : 0 < κ) (hlin : A nC + c = 0) (hbound : ‖nC‖ ≤ κ * ‖c‖)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    let dN := sqpNormalModel c A 0 - sqpNormalModel c A (α • nC)
    (1 / κ) * ‖α • nC‖ ≤ dN ∧ dN ≤ ‖c‖ := by
  dsimp only
  rw [sqpNormalModel_decrease_scaled hlin hα.2,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hα.1]
  refine ⟨?_, mul_le_of_le_one_left (norm_nonneg _) hα.2⟩
  rw [one_div, ← div_eq_inv_mul]
  exact (div_le_iff₀ hκ).mpr (by
    calc
      α * ‖nC‖ ≤ α * (κ * ‖c‖) := mul_le_mul_of_nonneg_left hbound hα.1
      _ = α * ‖c‖ * κ := by ring)

/-- The penalty update in Step 2 of Algorithm 15.4.1, using the
required penalty as the threshold for an increase. -/
noncomputable def sqpPenaltyUpdate (τ₁ τ₂ required previous : ℝ) : ℝ :=
  if required ≤ previous then previous else max required (max (τ₁ * previous) (previous + τ₂))

/-- An eventually bounded threshold forces the penalty update to stabilize
after finitely many increases. -/
theorem sqpPenaltyUpdate_eventually_constant {τ₁ τ₂ : ℝ} (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 < τ₂)
    {required σ : ℕ → ℝ} (hσ₀ : 0 < σ 0)
    (hupdate : ∀ k, σ (k + 1) = sqpPenaltyUpdate τ₁ τ₂ (required k) (σ k))
    {B : ℝ} {K : ℕ} (hrequired : ∀ k ≥ K, required k ≤ B) :
    ∃ j, K ≤ j ∧ 0 < σ j ∧ ∀ k ≥ j, σ k = σ j := by
  have hgap (k : ℕ) : σ (k + 1) = σ k ∨ τ₂ ≤ σ (k + 1) - σ k := by
    rw [hupdate, sqpPenaltyUpdate]
    split_ifs with h
    · exact Or.inl rfl
    · apply Or.inr
      have h := le_max_right (τ₁ * σ k) (σ k + τ₂)
      exact le_sub_iff_add_le.mpr (by linarith [h.trans (le_max_right (required k) _)])
  have hmono : Monotone σ := monotone_nat_of_le_succ fun k => by
    rcases hgap k with h | h
    · exact h.ge
    · linarith
  have hpos (k : ℕ) : 0 < σ k := hσ₀.trans_le (hmono (Nat.zero_le k))
  let M := max (σ K) (max B (max (τ₁ * B) (B + τ₂)))
  have hM : ∀ k ≥ K, σ k ≤ M := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_max_left _ _
    | succ k hk ih =>
      rw [hupdate, sqpPenaltyUpdate]
      split_ifs with h
      · exact ih
      · have hsmall : σ k ≤ B := (lt_of_not_ge h).le.trans (hrequired k hk)
        have h₁ := hrequired k hk
        have h₂ := mul_le_mul_of_nonneg_left hsmall hτ₁
        have h₃ := add_le_add hsmall (le_refl τ₂)
        exact (max_le_max h₁ (max_le_max h₂ h₃)).trans (le_max_right _ _)
  have hbd : BddAbove (Set.range σ) := ⟨M, by
    rintro _ ⟨k, rfl⟩
    by_cases hk : K ≤ k
    · exact hM k hk
    · exact (hmono (le_of_not_ge hk)).trans (hM K le_rfl)⟩
  have hlim := tendsto_atTop_ciSup hmono hbd
  have hdiff : Filter.Tendsto (fun k => σ (k + 1) - σ k) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, sub_self] using
      (hlim.comp (Filter.tendsto_add_atTop_nat 1)).sub hlim
  obtain ⟨j, hj⟩ := Filter.eventually_atTop.mp (hdiff.eventually (gt_mem_nhds hτ₂))
  let l := max K j
  refine ⟨l, le_max_left _ _, hpos l, ?_⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have heq : σ (k + 1) = σ k :=
      (hgap k).resolve_right (not_le_of_gt (hj k ((le_max_right K j).trans hk)))
    exact heq.trans ih

/-- Theorem 15.4.8. The normal objective term is bounded by a constant
times the normal feasibility reduction, and the penalty eventually stops
increasing. The index of the penalty used at iteration k is k+1, leaving
index zero for the initial penalty. -/
theorem theorem_15_4_8 (g n : ℕ → E) (H : ℕ → E →L[ℝ] E)
    (dN dT σ auxiliary : ℕ → ℝ) {G B U b S ν τ₁ τ₂ : ℝ} {K : ℕ}
    (hG : 0 ≤ G) (hB : 0 ≤ B) (hU : 0 ≤ U) (hb : 0 < b)
    (hν : ν < 1) (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 < τ₂) (hσ₀ : 0 < σ 0)
    (hg : ∀ k, ‖g k‖ ≤ G) (hH : ∀ k, ‖H k‖ ≤ B)
    (hN : ∀ k ≥ K, b * ‖n k‖ ≤ dN k ∧ dN k ≤ U)
    (hT : ∀ k, 0 ≤ dT k) (haux : ∀ k, auxiliary k ≤ S)
    (hupdate : ∀ k,
      let dq := -⟪g k, n k⟫ - (1 / 2) * ⟪n k, H k (n k)⟫
      let required := if dN k = 0 then auxiliary k
        else max (auxiliary k) (sqpPenaltyThreshold ν (dN k) (dT k) dq)
      σ (k + 1) = sqpPenaltyUpdate τ₁ τ₂ required (σ k)) :
    ∃ σmax > 0, ∃ C ≥ 0, ∃ j, ∀ k ≥ j,
      σ (k + 1) = σmax ∧
      dT k + (σ (k + 1) - C) * dN k ≤
        dT k + σ (k + 1) * dN k +
          (-⟪g k, n k⟫ - (1 / 2) * ⟪n k, H k (n k)⟫) := by
  let dq (k : ℕ) := -⟪g k, n k⟫ - (1 / 2) * ⟪n k, H k (n k)⟫
  let required (k : ℕ) := if dN k = 0 then auxiliary k
    else max (auxiliary k) (sqpPenaltyThreshold ν (dN k) (dT k) (dq k))
  let C := (G + (1 / 2) * B * (U / b)) / b
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdq (k : ℕ) (hk : K ≤ k) : -(C * dN k) ≤ dq k := by
    have hnc := (hN k hk).1
    have hn : ‖n k‖ ≤ U / b := (le_div_iff₀ hb).mpr (by linarith [(hN k hk).2])
    have h₁ : ⟪g k, n k⟫ ≤ G * ‖n k‖ :=
      (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hg k) (norm_nonneg _)))
    have h₂ : ⟪n k, H k (n k)⟫ ≤ B * (U / b) * ‖n k‖ := calc
      _ ≤ |⟪n k, H k (n k)⟫| := le_abs_self _
      _ ≤ ‖n k‖ * ‖H k (n k)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖n k‖ * (‖H k‖ * ‖n k‖) :=
        mul_le_mul_of_nonneg_left ((H k).le_opNorm _) (norm_nonneg _)
      _ ≤ ‖n k‖ * (B * (U / b)) := by
        gcongr
        exact hH k
      _ = _ := by ring
    have hthird : (G + (1 / 2) * B * (U / b)) * ‖n k‖ ≤ C * dN k := by
      have h := mul_le_mul_of_nonneg_left hnc hC
      have hCb : C * b = G + (1 / 2) * B * (U / b) := div_mul_cancel₀ _ hb.ne'
      rwa [← mul_assoc, hCb] at h
    dsimp [dq]
    linarith only [h₁, h₂, hthird]
  have hrequired (k : ℕ) (hk : K ≤ k) : required k ≤ max S (C / (1 - ν)) := by
    dsimp [required]
    split_ifs with hz
    · exact (haux k).trans (le_max_left _ _)
    · have hdN : 0 < dN k := lt_of_le_of_ne
        ((mul_nonneg hb.le (norm_nonneg _)).trans (hN k hk).1) (Ne.symm hz)
      apply max_le (le_trans (haux k) (le_max_left _ _))
      apply le_trans _ (le_max_right _ _)
      unfold sqpPenaltyThreshold
      rw [div_le_iff₀ (mul_pos (sub_pos.mpr hν) hdN)]
      have hcancel : C / (1 - ν) * ((1 - ν) * dN k) = C * dN k := by
        rw [← mul_assoc, div_mul_cancel₀ _ (sub_pos.mpr hν).ne']
      rw [hcancel]
      linarith only [hdq k hk, hT k]
  obtain ⟨j, hKj, hpos, hstable⟩ :=
    sqpPenaltyUpdate_eventually_constant hτ₁ hτ₂ hσ₀ hupdate hrequired
  refine ⟨σ j, hpos, C, hC, j, fun k hk => ⟨hstable _ (hk.trans (Nat.le_succ k)), ?_⟩⟩
  change _ ≤ dT k + σ (k + 1) * dN k + dq k
  linarith only [hdq k (hKj.trans hk)]

/-- Lemma 15.4.9 with a positive coefficient for every nonnegative normal
objective-loss bound. The denominator is positive even if the stabilized
penalty meets or exceeds the normal objective-loss bound. -/
theorem lemma_15_4_9 {ν σ B : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hB : 0 ≤ B)
    {dN dT dm : ℝ} (hN : 0 ≤ dN)
    (h₁ : dT + (σ - B) * dN ≤ dm) (h₂ : ν * σ * dN ≤ dm) :
    0 < ν * σ / (ν * σ + B) ∧ (ν * σ / (ν * σ + B)) * dT ≤ dm := by
  have hp : 0 < ν * σ := mul_pos hν hσ
  have hden : 0 < ν * σ + B := add_pos_of_pos_of_nonneg hp hB
  refine ⟨div_pos hp hden, ?_⟩
  have hT : dT ≤ dm + B * dN := by nlinarith only [h₁, mul_nonneg hσ.le hN]
  have hh := mul_le_mul_of_nonneg_left hT hp.le
  have hh' := mul_le_mul_of_nonneg_left h₂ hB
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hh, hh']

/-- The coefficient in the printed proof of Lemma 15.4.9 can be negative. -/
theorem printed_tangential_coefficient_nonpos :
    (1 / 2 : ℝ) * min 1 ((1 / 2) * 2 / (1 - 2)) < 0 := by
  norm_num

/-- The scalar data of a stabilized relaxed-SQP tail. Here u is the
unshifted reduced gradient norm, w includes the normal-step correction,
and v is the merit function at the fixed penalty shifted by a lower bound. -/
structure SQPTangentialRun (P : BTRParams) (u w v Δ d actual : ℕ → ℝ) (S : Set ℕ) where
  u_nonneg : ∀ k, 0 ≤ u k
  merit_nonneg : ∀ k, 0 ≤ v k
  radius_pos : ∀ k, 0 < Δ k
  merit_antitone : Antitone v
  radius_lower : ∀ k, P.γ₁ * Δ k ≤ Δ (k + 1)
  radius_rejected : ∀ k ∉ S, Δ (k + 1) ≤ P.γ₂ * Δ k
  merit_successful : ∀ k ∈ S, P.η₁ * d k ≤ v k - v (k + 1)
  very_successful : ∀ k, P.η₂ ≤ actual k / d k → k ∈ S ∧ Δ k ≤ Δ (k + 1)

/-- With bounded reduced-coordinate maps and Hessians, the vanishing
normal step gives a vanishing perturbation of the reduced gradient. -/
theorem sqpReducedGradient_perturbation {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (g n : ℕ → E) (H : ℕ → E →L[ℝ] E) (NT : ℕ → E →L[ℝ] Z)
    {B D : ℝ} (hD : 0 ≤ D)
    (hH : ∀ k, ‖H k‖ ≤ B) (hNT : ∀ k, ‖NT k‖ ≤ D)
    (hn : Filter.Tendsto n Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ‖NT k (g k + H k (n k))‖ - ‖NT k (g k)‖)
      Filter.atTop (nhds 0) := by
  have hn' : Filter.Tendsto (fun k => ‖n k‖) Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hn
  refine squeeze_zero_norm' (a := fun k => D * (B * ‖n k‖)) ?_ ?_
  · apply Filter.Eventually.of_forall
    intro k
    calc
      _ ≤ ‖NT k (g k + H k (n k)) - NT k (g k)‖ := abs_norm_sub_norm_le _ _
      _ = ‖NT k (H k (n k))‖ := by rw [map_add, add_sub_cancel_left]
      _ ≤ ‖NT k‖ * ‖H k (n k)‖ := (NT k).le_opNorm _
      _ ≤ D * (B * ‖n k‖) := by
        exact mul_le_mul (hNT k) (((H k).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hH k) (norm_nonneg _))) (norm_nonneg _) hD
  · simpa only [mul_zero] using (hn'.const_mul B).const_mul D

private theorem tangentialProgress {P : BTRParams} {u w v Δ d actual : ℕ → ℝ} {S : Set ℕ}
    (run : SQPTangentialRun P u w v Δ d actual S)
    {κ b β C : ℝ} (hκ : 0 < κ) (hb : 0 < b) (hβ : 0 < β) (hC : 0 ≤ C)
    (hpert : Filter.Tendsto (fun k => w k - u k) Filter.atTop (nhds 0))
    (hpred : ∀ᶠ k in Filter.atTop, κ * w k * min (b * Δ k) (w k / β) ≤ d k)
    (herr : ∀ᶠ k in Filter.atTop, |actual k - d k| ≤ C * (Δ k) ^ 2) :
    HasRelaxedProgress u v Δ S := by
  intro ε hε
  let e := ε / 2
  have he : 0 < e := half_pos hε
  let r := min (e / (β * b)) ((1 - P.η₂) * κ * e * b / (C + 1))
  have hr : 0 < r := lt_min (div_pos he (mul_pos hβ hb)) (by positivity [P.eta₂_lt_one])
  have hsmall := hpert.eventually (lt_mem_nhds (neg_neg_of_pos he))
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp ((hsmall.and hpred).and herr)
  refine ⟨P.η₁ * κ * e, b, e / β, r, K, by positivity [P.eta₁_pos], hb,
    div_pos he hβ, hr, ?_⟩
  intro k hk hu
  have h := hK k hk
  have hw : e ≤ w k := by
    have ht : -e < w k - u k := h.1.1
    dsimp [e] at ht ⊢
    linarith
  have hbound : κ * e * min (b * Δ k) (e / β) ≤ d k := by
    refine (mul_le_mul (mul_le_mul_of_nonneg_left hw hκ.le) ?_ ?_ ?_).trans h.1.2
    · exact min_le_min_left _ (div_le_div_of_nonneg_right hw hβ.le)
    · exact le_min (mul_nonneg hb.le (run.radius_pos k).le) (div_nonneg he.le hβ.le)
    · exact mul_nonneg hκ.le (he.le.trans hw)
  constructor
  · intro hΔ
    have hD : b * Δ k ≤ e / β := by
      have hh := (le_div_iff₀ (mul_pos hβ hb)).mp (hΔ.trans (min_le_left _ _))
      apply (le_div_iff₀ hβ).mpr
      nlinarith only [hh]
    rw [min_eq_left hD] at hbound
    have hpos : 0 < d k :=
      (mul_pos (mul_pos hκ he) (mul_pos hb (run.radius_pos k))).trans_le hbound
    have hCΔ : C * Δ k ≤ (1 - P.η₂) * κ * e * b := by
      have hh := (le_div_iff₀ (by positivity : 0 < C + 1)).mp (hΔ.trans (min_le_right _ _))
      linarith only [hh, run.radius_pos k]
    have h₁ := mul_le_mul_of_nonneg_right hCΔ (run.radius_pos k).le
    have h₂ := mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr P.eta₂_lt_one.le)
    have he' : |actual k - d k| ≤ (1 - P.η₂) * d k := h.2.trans (by nlinarith only [h₁, h₂])
    apply run.very_successful k
    apply (le_div_iff₀ hpos).mpr
    linarith only [(abs_le.mp he').1]
  · intro hkS
    have hh := mul_le_mul_of_nonneg_left hbound P.eta₁_pos.le
    rw [min_comm (e / β), mul_assoc P.η₁ κ]
    simpa only [mul_assoc] using hh.trans (run.merit_successful k hkS)

/-- Theorem 15.4.10. A bounded penalty, a vanishing normal perturbation and
the uniform trial-segment error bound give zero limit inferior of the
unshifted reduced gradient norm. -/
theorem theorem_15_4_10 {P : BTRParams} {u w v Δ d actual : ℕ → ℝ} {S : Set ℕ}
    (run : SQPTangentialRun P u w v Δ d actual S)
    {κ b β C : ℝ} (hκ : 0 < κ) (hb : 0 < b) (hβ : 0 < β) (hC : 0 ≤ C)
    (hpert : Filter.Tendsto (fun k => w k - u k) Filter.atTop (nhds 0))
    (hpred : ∀ᶠ k in Filter.atTop, κ * w k * min (b * Δ k) (w k / β) ≤ d k)
    (herr : ∀ᶠ k in Filter.atTop, |actual k - d k| ≤ C * (Δ k) ^ 2) :
    Filter.liminf u Filter.atTop = 0 := by
  have hcontrol := tangentialProgress run hκ hb hβ hC hpert hpred herr
  have hfreq (ε : ℝ) (hε : 0 < ε) : ∃ᶠ k in Filter.atTop, u k < ε :=
    Filter.frequently_atTop.mpr (relaxed_progress_frequently_small P.gamma₁_pos
      (P.gamma₁_pos.le.trans P.gamma₁_le_gamma₂) P.gamma₂_lt_one run.merit_nonneg
      run.radius_pos run.merit_antitone run.radius_lower run.radius_rejected hcontrol ε hε)
  have hbdd : (Filter.atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) u :=
    ⟨0, show ∀ᶠ k in Filter.atTop, 0 ≤ u k from Filter.Eventually.of_forall run.u_nonneg⟩
  have hc : (Filter.atTop : Filter ℕ).IsCoboundedUnder (· ≥ ·) u := by
    refine ⟨1, fun b h => ?_⟩
    obtain ⟨k, hk, hbk⟩ := ((hfreq 1 zero_lt_one).and_eventually h).exists
    exact hbk.trans hk.le
  refine le_antisymm ?_ (Filter.le_liminf_of_le hc (Filter.Eventually.of_forall run.u_nonneg))
  by_contra! hp
  have hlim := Filter.liminf_le_of_frequently_le
    ((hfreq _ (half_pos hp)).mono fun _ h => h.le) hbdd
  linarith

/-- Theorem 15.4.11 with uniform variation control for the unshifted reduced
gradient on accepted steps. This control is supplied, for example, by a
Lipschitz reduced-gradient map and the composite step radius bound. -/
theorem theorem_15_4_11 {P : BTRParams} {u w v Δ d actual : ℕ → ℝ} {S : Set ℕ}
    (run : SQPTangentialRun P u w v Δ d actual S)
    {κ b β C L : ℝ} (hκ : 0 < κ) (hb : 0 < b) (hβ : 0 < β) (hC : 0 ≤ C)
    (hpert : Filter.Tendsto (fun k => w k - u k) Filter.atTop (nhds 0))
    (hpred : ∀ᶠ k in Filter.atTop, κ * w k * min (b * Δ k) (w k / β) ≤ d k)
    (herr : ∀ᶠ k in Filter.atTop, |actual k - d k| ≤ C * (Δ k) ^ 2)
    (hL : 0 ≤ L) (hmove : ∀ k ∈ S, u k - u (k + 1) ≤ L * Δ k)
    (hstay : ∀ k ∉ S, u (k + 1) = u k) :
    Filter.Tendsto u Filter.atTop (nhds 0) :=
  tendsto_zero_of_relaxed_steps hL P.gamma₁_pos
    (P.gamma₁_pos.le.trans P.gamma₁_le_gamma₂) P.gamma₂_lt_one
    run.u_nonneg run.merit_nonneg run.radius_pos run.merit_antitone run.radius_lower
    (fun k hk => ⟨run.radius_rejected k hk, hstay k hk⟩) hmove
    (tangentialProgress run hκ hb hβ hC hpert hpred herr)

end ConnGouldToint.Chapter15
