import Numlib.Optimization.FischerBurmeister
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Complementarity problems -/

open scoped BigOperators

namespace ConnGouldToint.Chapter16

/-- The generalized complementarity conditions (16.3.1) on the two vectors. -/
def IsComplementary {ι : Type*} [Fintype ι] (a b : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ (∀ i, 0 ≤ b i) ∧ ∑ i, a i * b i = 0

/-- The scalar complementarity residual (16.3.2). -/
noncomputable abbrev fischerBurmeister := Numlib.Optimization.fischerBurmeister

/-- The residual `Φ` in the system (16.3.3), evaluated on the two vectors. -/
noncomputable def complementarityResidual {ι : Type*} (a b : ι → ℝ) (i : ι) : ℝ :=
  fischerBurmeister (a i) (b i)

/-- The residual system (16.3.3) is equivalent to the complementarity conditions (16.3.1). -/
theorem complementarityResidual_eq_zero_iff {ι : Type*} [Fintype ι] {a b : ι → ℝ} :
    complementarityResidual a b = 0 ↔ IsComplementary a b := by
  constructor
  · intro h
    have hc (i : ι) : 0 ≤ a i ∧ 0 ≤ b i ∧ a i * b i = 0 :=
      Numlib.Optimization.fischerBurmeister_eq_zero_iff.mp (congrFun h i)
    exact ⟨fun i ↦ (hc i).1, fun i ↦ (hc i).2.1,
      Finset.sum_eq_zero fun i _ ↦ (hc i).2.2⟩
  · rintro ⟨ha, hb, hsum⟩
    have hprod := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ ↦ mul_nonneg (ha i) (hb i))).mp hsum
    funext i
    exact Numlib.Optimization.fischerBurmeister_eq_zero_iff.mpr
      ⟨ha i, hb i, hprod i (Finset.mem_univ i)⟩

/-- The least-squares complementarity merit (16.3.7) on the two vectors. -/
noncomputable def complementarityMerit {ι : Type*} [Fintype ι] (a b : ι → ℝ) : ℝ :=
  (∑ i, complementarityResidual a b i ^ 2) / 2

/-- A diagonal coefficient in (16.3.5)–(16.3.6). At the origin we choose the
centre of the permitted disk. -/
noncomputable def complementarityCoefficient (a b : ℝ) : ℝ :=
  a / √(a ^ 2 + b ^ 2) - 1

private theorem radicand_pos {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) :
    0 < a ^ 2 + b ^ 2 := by
  rcases h with h | h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg b)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg a) (sq_pos_of_ne_zero h)

/-- The chosen pair of diagonal coefficients lies in the disk (16.3.5). -/
theorem complementarityCoefficient_disk (a b : ℝ) :
    (complementarityCoefficient a b + 1) ^ 2 +
      (complementarityCoefficient b a + 1) ^ 2 ≤ 1 := by
  by_cases h : a ≠ 0 ∨ b ≠ 0
  · have hq := radicand_pos h
    unfold complementarityCoefficient
    rw [add_comm (b ^ 2), sub_add_cancel, sub_add_cancel, div_pow, div_pow, ← add_div,
      Real.sq_sqrt hq.le, div_self hq.ne']
  · push Not at h
    norm_num [complementarityCoefficient, h.1, h.2]

private theorem abs_fischerBurmeister_le (a b : ℝ) :
    |fischerBurmeister a b| ≤ 2 * (|a| + |b|) := by
  have hs : √(a ^ 2 + b ^ 2) ≤ |a| + |b| := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by positivity, by nlinarith [sq_abs a, sq_abs b, mul_nonneg (abs_nonneg a) (abs_nonneg b)]⟩
  calc
    _ ≤ |√(a ^ 2 + b ^ 2) - a| + |b| := abs_sub _ _
    _ ≤ (√(a ^ 2 + b ^ 2) + |a|) + |b| := by
      have ht := abs_sub (√(a ^ 2 + b ^ 2)) a
      rw [abs_of_nonneg (Real.sqrt_nonneg _)] at ht
      linarith
    _ ≤ _ := by linarith

open Filter Asymptotics
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem hasFDerivAt_fischerBurmeister_of_ne_zero {a b : E → ℝ} {x : E}
    {A B : E →L[ℝ] ℝ} (ha : HasFDerivAt a A x) (hb : HasFDerivAt b B x)
    (h : a x ≠ 0 ∨ b x ≠ 0) :
    HasFDerivAt (fun y ↦ fischerBurmeister (a y) (b y))
      (complementarityCoefficient (a x) (b x) • A +
        complementarityCoefficient (b x) (a x) • B) x := by
  have hq := radicand_pos h
  have hs := (((ha.pow 2).add (hb.pow 2)).sqrt hq.ne').sub ha |>.sub hb
  convert hs using 1
  · rfl
  · ext v
    simp [complementarityCoefficient, add_comm (b x ^ 2)]
    ring

/-- The residual linearization (16.3.4) maps a direction to its component
changes. With the usual Jacobian convention, diagonal weights act on the
output of each Jacobian. -/
noncomputable def complementarityLinearization {ι : Type*} (a b : E → ι → ℝ) (x : E) :
    E →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i ↦
    complementarityCoefficient (a x i) (b x i) • fderiv ℝ (a · i) x +
      complementarityCoefficient (b x i) (a x i) • fderiv ℝ (b · i) x

/-- The linearization (16.3.4) is the derivative of the residual wherever
each pair of component values is nonzero. -/
theorem hasFDerivAt_complementarityResidual {ι : Type*} [Fintype ι]
    {a b : E → ι → ℝ} {x : E}
    (ha : ∀ i, DifferentiableAt ℝ (a · i) x) (hb : ∀ i, DifferentiableAt ℝ (b · i) x)
    (h : ∀ i, a x i ≠ 0 ∨ b x i ≠ 0) :
    HasFDerivAt (fun y ↦ complementarityResidual (a y) (b y))
      (complementarityLinearization a b x) x :=
  hasFDerivAt_pi.2 fun i ↦
    hasFDerivAt_fischerBurmeister_of_ne_zero (ha i).hasFDerivAt (hb i).hasFDerivAt (h i)

private theorem hasFDerivAt_half_fischerBurmeister_sq {a b : E → ℝ} {x : E}
    {A B : E →L[ℝ] ℝ} (ha : HasFDerivAt a A x) (hb : HasFDerivAt b B x) :
    HasFDerivAt (fun y ↦ fischerBurmeister (a y) (b y) ^ 2 / 2)
      (fischerBurmeister (a x) (b x) •
        (complementarityCoefficient (a x) (b x) • A +
          complementarityCoefficient (b x) (a x) • B)) x := by
  by_cases h : a x ≠ 0 ∨ b x ≠ 0
  · have hs := hasFDerivAt_fischerBurmeister_of_ne_zero ha hb h
    have hd := (hs.pow 2).const_mul ((2 : ℝ)⁻¹)
    convert hd using 1
    · funext y
      ring
    · ext v
      simp
      ring
  · push Not at h
    have hzero : fischerBurmeister (a x) (b x) = 0 := by
      simp [Numlib.Optimization.fischerBurmeister, h.1, h.2]
    rw [hzero, zero_smul, hasFDerivAt_iff_isLittleO]
    have hA : a =O[𝓝 x] (· - x) := by simpa [h.1] using ha.isBigO_sub
    have hB : b =O[𝓝 x] (· - x) := by simpa [h.2] using hb.isBigO_sub
    let r (y : E) := fischerBurmeister (a y) (b y)
    have hr : r =O[𝓝 x] (· - x) := by
      apply IsBigO.trans _ (hA.norm_left.add hB.norm_left)
      apply IsBigO.of_bound 2
      filter_upwards with y
      change ‖r y‖ ≤ 2 * ‖‖a y‖ + ‖b y‖‖
      rw [Real.norm_eq_abs (r y), Real.norm_of_nonneg (by positivity), Real.norm_eq_abs (a y),
        Real.norm_eq_abs (b y)]
      exact abs_fischerBurmeister_le (a y) (b y)
    have hrcont : ContinuousAt r x := by
      change ContinuousAt (fun y ↦ √(a y ^ 2 + b y ^ 2) - a y - b y) x
      have hca := ha.continuousAt
      have hcb := hb.continuousAt
      fun_prop
    have hrsmall : r =o[𝓝 x] (fun _ ↦ (1 : ℝ)) := by
      apply (isLittleO_one_iff ℝ).2
      simpa [r, hzero] using hrcont.tendsto
    have hsq : (fun y ↦ r y ^ 2) =o[𝓝 x] (· - x) := by
      apply IsLittleO.of_norm_right
      simpa only [pow_two, mul_one] using hr.norm_right.mul_isLittleO hrsmall
    simpa [r, hzero, div_eq_mul_inv, mul_comm] using hsq.const_mul_left ((2 : ℝ)⁻¹)

/-- The derivative in (16.3.8) is the weighted sum of the component derivatives.
Writing it as a functional uses the standard convention that a Jacobian maps
input directions to output directions. -/
theorem hasFDerivAt_complementarityMerit {ι : Type*} [Fintype ι]
    {a b : E → ι → ℝ} {x : E}
    (ha : ∀ i, DifferentiableAt ℝ (a · i) x) (hb : ∀ i, DifferentiableAt ℝ (b · i) x) :
    HasFDerivAt (fun y ↦ complementarityMerit (a y) (b y))
      (∑ i, complementarityResidual (a x) (b x) i •
        (complementarityCoefficient (a x i) (b x i) • fderiv ℝ (a · i) x +
          complementarityCoefficient (b x i) (a x i) • fderiv ℝ (b · i) x)) x := by
  simpa only [complementarityMerit, complementarityResidual, Finset.sum_div] using
    HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
      hasFDerivAt_half_fischerBurmeister_sq (ha i).hasFDerivAt (hb i).hasFDerivAt)

/-- The Gauss–Newton model (16.3.9) in step coordinates. -/
noncomputable def complementarityModel {ι : Type*} [Fintype ι]
    (a b : E → ι → ℝ) (x s : E) : ℝ :=
  (∑ i, (complementarityResidual (a x) (b x) i +
    complementarityLinearization a b x s i) ^ 2) / 2

/-- Expanding (16.3.9) gives the merit value, its first-order term, and the
squared Euclidean norm of the linearized change divided by two. -/
theorem complementarityModel_expansion {ι : Type*} [Fintype ι]
    {a b : E → ι → ℝ} {x : E}
    (ha : ∀ i, DifferentiableAt ℝ (a · i) x) (hb : ∀ i, DifferentiableAt ℝ (b · i) x)
    (s : E) :
    complementarityModel a b x s = complementarityMerit (a x) (b x) +
      fderiv ℝ (fun y ↦ complementarityMerit (a y) (b y)) x s +
      (∑ i, complementarityLinearization a b x s i ^ 2) / 2 := by
  rw [(hasFDerivAt_complementarityMerit ha hb).fderiv]
  simp only [complementarityModel, complementarityMerit, Finset.sum_div,
    sum_apply, smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [complementarityLinearization, ContinuousLinearMap.pi_apply]
  ring

/-- Componentwise complementarity, the index condition defining `J_C`. -/
def IsComplementaryComponent (a b : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ a * b = 0

/-- The sign conditions on either of the two vectors in the regularity test.
The three cases are `J_C`, `J_+` and `J_-`, respectively. -/
def HasRegularitySigns {ι : Type*} (a b v : ι → ℝ) : Prop :=
  ∀ i, (IsComplementaryComponent (a i) (b i) → v i = 0) ∧
    (0 < a i → 0 < b i → 0 < v i) ∧
    (¬ IsComplementaryComponent (a i) (b i) → ¬ (0 < a i ∧ 0 < b i) → v i < 0)

/-- Regularity for the generalized complementarity problem at `x`.
With Jacobians mapping input directions to output directions, this condition
uses their transposes, expressed as sums of the component derivative functionals. -/
def ComplementarityRegular {ι : Type*} [Fintype ι] (a b : E → ι → ℝ) (x : E) : Prop :=
  ∀ u v : ι → ℝ, u ≠ 0 → v ≠ 0 →
    HasRegularitySigns (a x) (b x) u → HasRegularitySigns (a x) (b x) v →
    (∑ i, (u i • fderiv ℝ (a · i) x + v i • fderiv ℝ (b · i) x)) ≠ 0

private theorem coefficient_neg_of_other_ne_zero {a b : ℝ} (hb : b ≠ 0) :
    complementarityCoefficient a b < 0 := by
  have hs := Real.sqrt_pos.2 (radicand_pos (Or.inr hb : a ≠ 0 ∨ b ≠ 0))
  have hlt : a < √(a ^ 2 + b ^ 2) := by
    by_cases ha : 0 ≤ a
    · exact (Real.lt_sqrt ha).2 (lt_add_of_pos_right _ (sq_pos_of_ne_zero hb))
    · linarith
  unfold complementarityCoefficient
  linarith [(div_lt_one hs).2 hlt]

private theorem coefficient_neg_of_neg {a b : ℝ} (ha : a < 0) :
    complementarityCoefficient a b < 0 := by
  unfold complementarityCoefficient
  have hs := Real.sqrt_pos.2 (radicand_pos (Or.inl ha.ne : a ≠ 0 ∨ b ≠ 0))
  linarith [div_neg_of_neg_of_pos ha hs]

private theorem weighted_coefficient_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < complementarityCoefficient a b * fischerBurmeister a b := by
  apply mul_pos_of_neg_of_neg (coefficient_neg_of_other_ne_zero hb.ne')
  have hs : √(a ^ 2 + b ^ 2) < a + b :=
    (Real.sqrt_lt (by positivity) (by positivity)).2 (by nlinarith [mul_pos ha hb])
  change √(a ^ 2 + b ^ 2) - a - b < 0
  linarith

private theorem weighted_coefficient_neg {a b : ℝ} (h : a < 0 ∨ b < 0) :
    complementarityCoefficient a b * fischerBurmeister a b < 0 := by
  apply mul_neg_of_neg_of_pos
  · exact h.elim coefficient_neg_of_neg (fun hb ↦ coefficient_neg_of_other_ne_zero hb.ne)
  · have hs₁ : a ≤ √(a ^ 2 + b ^ 2) := by
      by_cases ha : 0 ≤ a
      · exact (Real.le_sqrt ha (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg b))
      · exact (le_of_not_ge ha).trans (Real.sqrt_nonneg _)
    have hs₂ : b ≤ √(a ^ 2 + b ^ 2) := by
      by_cases hb : 0 ≤ b
      · exact (Real.le_sqrt hb (by positivity)).2 (le_add_of_nonneg_left (sq_nonneg a))
      · exact (le_of_not_ge hb).trans (Real.sqrt_nonneg _)
    change 0 < √(a ^ 2 + b ^ 2) - a - b
    rcases h with ha | hb <;> linarith

private theorem weighted_coefficients_signs {ι : Type*} (a b : ι → ℝ) :
    HasRegularitySigns a b
      (fun i ↦ complementarityCoefficient (a i) (b i) * complementarityResidual a b i) ∧
    HasRegularitySigns a b
      (fun i ↦ complementarityCoefficient (b i) (a i) * complementarityResidual a b i) := by
  have hneg {a b : ℝ} (hc : ¬ IsComplementaryComponent a b)
      (hp : ¬ (0 < a ∧ 0 < b)) : a < 0 ∨ b < 0 := by
    by_contra! h
    have ha : a = 0 ∨ b = 0 := by
      rcases eq_or_lt_of_le h.1 with ha | ha
      · exact Or.inl ha.symm
      · exact Or.inr (le_antisymm (le_of_not_gt (fun hb ↦ hp ⟨ha, hb⟩)) h.2)
    exact hc ⟨h.1, h.2, mul_eq_zero.2 ha⟩
  have hsymm (a b : ℝ) : fischerBurmeister a b = fischerBurmeister b a := by
    change √(a ^ 2 + b ^ 2) - a - b = √(b ^ 2 + a ^ 2) - b - a
    rw [add_comm (b ^ 2)]
    ring
  constructor
  · intro i
    exact ⟨fun hc ↦ mul_eq_zero.2
      (Or.inr (Numlib.Optimization.fischerBurmeister_eq_zero_iff.2 hc)),
      weighted_coefficient_pos, fun hc hp ↦ weighted_coefficient_neg (hneg hc hp)⟩
  · intro i
    refine ⟨fun hc ↦ mul_eq_zero.2
      (Or.inr (Numlib.Optimization.fischerBurmeister_eq_zero_iff.2 hc)), ?_, ?_⟩
    · intro ha hb
      simp only [complementarityResidual]
      rw [hsymm (a i) (b i)]
      exact weighted_coefficient_pos hb ha
    · intro hc hp
      simp only [complementarityResidual]
      rw [hsymm (a i) (b i)]
      exact weighted_coefficient_neg (Or.symm (hneg hc hp))

/-- Theorem 16.3.1. Complementarity is equivalent to regularity and first-order
criticality of the merit function. The functional formula uses the transpose
of the ordinary component Jacobians. -/
theorem theorem_16_3_1 {ι : Type*} [Fintype ι] {a b : E → ι → ℝ} {x : E}
    (ha : ∀ i, DifferentiableAt ℝ (a · i) x) (hb : ∀ i, DifferentiableAt ℝ (b · i) x) :
    IsComplementary (a x) (b x) ↔ ComplementarityRegular a b x ∧
      fderiv ℝ (fun y ↦ complementarityMerit (a y) (b y)) x = 0 := by
  have hd := (hasFDerivAt_complementarityMerit ha hb).fderiv
  constructor
  · intro hc
    have hz := complementarityResidual_eq_zero_iff.2 hc
    refine ⟨?_, by rw [hd, hz]; simp⟩
    intro u v hu _ hsu _
    exfalso
    apply hu
    funext i
    exact (hsu i).1 (Numlib.Optimization.fischerBurmeister_eq_zero_iff.1 (congrFun hz i))
  · rintro ⟨hregular, hcritical⟩
    by_contra hc
    let u (i : ι) := complementarityCoefficient (a x i) (b x i) *
      complementarityResidual (a x) (b x) i
    let v (i : ι) := complementarityCoefficient (b x i) (a x i) *
      complementarityResidual (a x) (b x) i
    have hs := weighted_coefficients_signs (a x) (b x)
    have hi : ∃ i, ¬ IsComplementaryComponent (a x i) (b x i) := by
      by_contra! h
      exact hc (complementarityResidual_eq_zero_iff.1
        (funext fun i ↦ Numlib.Optimization.fischerBurmeister_eq_zero_iff.2 (h i)))
    obtain ⟨i, hi⟩ := hi
    have hne {w : ι → ℝ} (hw : HasRegularitySigns (a x) (b x) w) : w ≠ 0 := by
      intro h
      have hwi : w i = 0 := congrFun h i
      by_cases hp : 0 < a x i ∧ 0 < b x i
      · exact (ne_of_gt ((hw i).2.1 hp.1 hp.2)) hwi
      · exact (ne_of_lt ((hw i).2.2 hi hp)) hwi
    apply hregular u v (hne hs.1) (hne hs.2) hs.1 hs.2
    rw [hd] at hcritical
    simpa only [u, v, smul_add, smul_smul, mul_comm] using hcritical

end ConnGouldToint.Chapter16
