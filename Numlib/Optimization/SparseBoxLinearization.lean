import Numlib.Optimization.SparseConstraints
import Mathlib.Basic.Sign.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Linear minimization with a box and a sparsity budget

Coordinates outside the retained support must be dropped. Retaining a coordinate instead
replaces that baseline by its scalar box minimum. The resulting support problem is a finite
maximization of explicit gains; its actual maximizer gives a global minimizer of the original
linear problem. Zero gains and ties require no uniqueness assumption.
-/

noncomputable section
open scoped BigOperators
open Set
namespace Optimization.SparseConstraints
variable {ι : Type*} [Fintype ι]

/-- The feasible displacements in the coordinate box with a sparsity budget. -/
def feasibleBoxSteps (x : ι → ℝ) (δ : ℝ) (k : ℕ) : Set (ι → ℝ) :=
  {d | (∀ i, |d i| ≤ δ) ∧ x + d ∈ sparseSet k}

/-- Feasibility records both actual coordinate bounds and the translated sparsity constraint. -/
@[simp] theorem mem_feasibleBoxSteps {x d : ι → ℝ} {δ : ℝ} {k : ℕ} :
    d ∈ feasibleBoxSteps x δ k ↔ (∀ i, |d i| ≤ δ) ∧ x + d ∈ sparseSet k := Iff.rfl

/-- The original sparse point supplies a feasible zero step at every nonnegative radius. -/
theorem zero_mem_feasibleBoxSteps {x : ι → ℝ} {δ : ℝ} {k : ℕ}
    (hδ : 0 ≤ δ) (hx : x ∈ sparseSet k) : 0 ∈ feasibleBoxSteps x δ k := by
  exact ⟨by simpa using fun _ : ι => hδ, by simpa using hx⟩

/-- A solution of the finite binary support problem, with ties allowed. -/
structure IsOptimalOptionalSupport (x g : ι → ℝ) (δ : ℝ) (k : ℕ)
    (J : Finset ι) : Prop where
  /-- The selected coordinates respect the optional cardinality budget. -/
  mem : J ∈ optionalSupports x δ k
  /-- No feasible optional support has a greater total coordinate gain. -/
  maximal : ∀ K ∈ optionalSupports x δ k,
    ∑ i ∈ K, optionalWeight x g δ i ≤ ∑ i ∈ J, optionalWeight x g δ i

/-- The finite support problem always attains its maximum. -/
theorem exists_optimalOptionalSupport (x g : ι → ℝ) (δ : ℝ) (k : ℕ) :
    ∃ J, IsOptimalOptionalSupport x g δ k J := by
  obtain ⟨J, hJ, hmax⟩ := (optionalSupports x δ k).exists_max_image
    (fun J => ∑ i ∈ J, optionalWeight x g δ i) (optionalSupports_nonempty x δ k)
  exact ⟨J, hJ, hmax⟩

/-- An actual maximizer of the finite binary support problem. -/
noncomputable def optimalOptionalSupport (x g : ι → ℝ) (δ : ℝ) (k : ℕ) : Finset ι :=
  (exists_optimalOptionalSupport x g δ k).choose

/-- The selected support satisfies the budget and the finite maximization property. -/
theorem optimalOptionalSupport_spec (x g : ι → ℝ) (δ : ℝ) (k : ℕ) :
    IsOptimalOptionalSupport x g δ k (optimalOptionalSupport x g δ k) :=
  (exists_optimalOptionalSupport x g δ k).choose_spec

variable [DecidableEq ι]

/-- Retain mandatory and selected optional coordinates at their scalar box minima;
drop every other coordinate. -/
def boxLinearStep (x g : ι → ℝ) (δ : ℝ) (J : Finset ι) : ι → ℝ :=
  fun i => if i ∈ mandatoryIndices x δ ∪ J then -δ * (SignType.sign (g i) : ℝ) else -x i

/-- The selected support gives the explicit coordinate formula for the step. -/
theorem boxLinearStep_apply (x g : ι → ℝ) (δ : ℝ) (J : Finset ι) (i : ι) :
    boxLinearStep x g δ J i =
      if i ∈ mandatoryIndices x δ ∪ J then -δ * (SignType.sign (g i) : ℝ) else -x i := rfl

/-- A nonretained coordinate is exactly cancelled by the displacement. -/
theorem boxLinearStep_of_not_mem {x g : ι → ℝ} {δ : ℝ} {J : Finset ι} {i : ι}
    (hi : i ∉ mandatoryIndices x δ ∪ J) : boxLinearStep x g δ J i = -x i :=
  ite_eq_right hi

/-- Every coordinate of the constructed displacement obeys the box bound. -/
theorem abs_boxLinearStep_le {x g : ι → ℝ} {δ : ℝ} {J : Finset ι}
    (hδ : 0 ≤ δ) (i : ι) : |boxLinearStep x g δ J i| ≤ δ := by
  rw [boxLinearStep_apply]
  split_ifs with hi
  · cases SignType.sign (g i) <;> simp [abs_of_nonneg hδ, hδ]
  · rw [abs_neg]
    exact le_of_not_gt (fun h => hi (Finset.mem_union_left J (mem_mandatoryIndices.mpr h)))

/-- The translated step has no support outside the retained coordinates. -/
theorem supportIndices_add_boxLinearStep_subset (x g : ι → ℝ) (δ : ℝ) (J : Finset ι) :
    supportIndices (x + boxLinearStep x g δ J) ⊆ mandatoryIndices x δ ∪ J := by
  intro i hi
  by_contra hn
  have h := mem_supportIndices.mp hi
  exact h (by simp [boxLinearStep_of_not_mem hn])

/-- A feasible mandatory cardinality and optional budget make the explicit step feasible. -/
theorem boxLinearStep_mem_feasibleBoxSteps_of_card_le {x g : ι → ℝ} {δ : ℝ} {k : ℕ} {J : Finset ι}
    (hδ : 0 ≤ δ) (hm : (mandatoryIndices x δ).card ≤ k)
    (hJ : J ∈ optionalSupports x δ k) :
    boxLinearStep x g δ J ∈ feasibleBoxSteps x δ k := by
  refine ⟨abs_boxLinearStep_le hδ, ?_⟩
  obtain ⟨hd, hc⟩ := mem_optionalSupports.mp hJ
  apply (Finset.card_le_card (supportIndices_add_boxLinearStep_subset x g δ J)).trans
  rw [Finset.card_union_of_disjoint hd.symm]
  omega

/-- Sparsity of the original point supplies the mandatory cardinality bound. -/
theorem boxLinearStep_mem_feasibleBoxSteps {x g : ι → ℝ} {δ : ℝ} {k : ℕ} {J : Finset ι}
    (hδ : 0 ≤ δ) (hx : x ∈ sparseSet k) (hJ : J ∈ optionalSupports x δ k) :
    boxLinearStep x g δ J ∈ feasibleBoxSteps x δ k :=
  boxLinearStep_mem_feasibleBoxSteps_of_card_le hδ
    ((Finset.card_le_card (mandatoryIndices_subset_support hδ)).trans hx) hJ

/-- The exact linear value of a retained support, relative to dropping all coordinates. -/
theorem sum_mul_boxLinearStep {x g : ι → ℝ} {δ : ℝ} {J : Finset ι}
    (hJ : Disjoint J (mandatoryIndices x δ)) :
    ∑ i, g i * boxLinearStep x g δ J i =
      -(∑ i, x i * g i) - (∑ i ∈ mandatoryIndices x δ, optionalWeight x g δ i) -
        ∑ i ∈ J, optionalWeight x g δ i := by
  have hp (i : ι) : g i * boxLinearStep x g δ J i =
      -(x i * g i) - if i ∈ mandatoryIndices x δ ∪ J then optionalWeight x g δ i else 0 := by
    rw [boxLinearStep_apply]
    split_ifs with hi
    · rw [show g i * (-δ * (SignType.sign (g i) : ℝ)) =
        -δ * (g i * (SignType.sign (g i) : ℝ)) by ring, self_mul_sign]
      dsimp [optionalWeight]
      ring
    · ring
  calc
    ∑ i, g i * boxLinearStep x g δ J i =
        ∑ i, (-(x i * g i) -
          if i ∈ mandatoryIndices x δ ∪ J then optionalWeight x g δ i else 0) :=
      Finset.sum_congr rfl (fun i _ => hp i)
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_ite_mem_eq,
        Finset.sum_union hJ.symm]
      ring

omit [DecidableEq ι] in
/-- A box-feasible displacement pays at least the baseline minus its actual support gains. -/
theorem sum_mul_ge_support_gain {x g d : ι → ℝ} {δ : ℝ} (hd : ∀ i, |d i| ≤ δ) :
    -(∑ i, x i * g i) - (∑ i ∈ supportIndices (x + d), optionalWeight x g δ i) ≤
      ∑ i, g i * d i := by
  classical
  have hp (i : ι) :
      -(x i * g i) - (if i ∈ supportIndices (x + d) then optionalWeight x g δ i else 0) ≤
        g i * d i := by
    by_cases hi : i ∈ supportIndices (x + d)
    · rw [ite_eq_left hi]
      have ha : |g i * d i| ≤ δ * |g i| := by
        rw [abs_mul, mul_comm δ]
        exact mul_le_mul_of_nonneg_left (hd i) (abs_nonneg _)
      have he : -(x i * g i) - optionalWeight x g δ i = -(δ * |g i|) := by
        dsimp [optionalWeight]
        ring
      rw [he]
      exact (abs_le.mp ha).1
    · rw [ite_eq_right hi, sub_zero]
      have hz : x i + d i = 0 := by simpa only [mem_supportIndices, not_not, Pi.add_apply] using hi
      have he : d i = -x i := by linarith
      rw [he]
      exact le_of_eq (by ring)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  simpa only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_ite_mem_eq] using hs

/-- The actual optional support of any feasible competitor obeys the binary selection budget. -/
theorem support_sdiff_mem_optionalSupports {x d : ι → ℝ} {δ : ℝ} {k : ℕ}
    (hd : d ∈ feasibleBoxSteps x δ k) :
    supportIndices (x + d) \ mandatoryIndices x δ ∈ optionalSupports x δ k := by
  apply mem_optionalSupports.mpr
  refine ⟨Finset.disjoint_left.mpr (fun i hi him => (Finset.mem_sdiff.mp hi).2 him), ?_⟩
  rw [Finset.card_sdiff_of_subset (mandatoryIndices_subset_support_add hd.1)]
  exact Nat.sub_le_sub_right hd.2 _

/-- A maximum-gain optional support gives a global linear minimum among all feasible steps. -/
theorem boxLinearStep_isMinOn {x g : ι → ℝ} {δ : ℝ} {k : ℕ} {J : Finset ι}
    (hJ : IsOptimalOptionalSupport x g δ k J) :
    IsMinOn (fun d : ι → ℝ => ∑ i, g i * d i) (feasibleBoxSteps x δ k)
      (boxLinearStep x g δ J) := by
  intro d hd
  have hm := mandatoryIndices_subset_support_add (x := x) hd.1
  have hs := Finset.sum_sdiff (f := optionalWeight x g δ) hm
  have hmax := hJ.maximal _ (support_sdiff_mem_optionalSupports hd)
  have hlo := sum_mul_ge_support_gain (x := x) (g := g) hd.1
  change (∑ i, g i * boxLinearStep x g δ J i) ≤ ∑ i, g i * d i
  rw [sum_mul_boxLinearStep (mem_optionalSupports.mp hJ.mem).1]
  linarith

/-- The selected finite maximizer yields an actual feasible global minimizer. -/
theorem exists_sparseBoxLinear_minimizer {x g : ι → ℝ} {δ : ℝ} {k : ℕ}
    (hδ : 0 ≤ δ) (hx : x ∈ sparseSet k) :
    ∃ J, IsOptimalOptionalSupport x g δ k J ∧
      boxLinearStep x g δ J ∈ feasibleBoxSteps x δ k ∧
      IsMinOn (fun d : ι → ℝ => ∑ i, g i * d i) (feasibleBoxSteps x δ k)
        (boxLinearStep x g δ J) := by
  let J := optimalOptionalSupport x g δ k
  have hJ := optimalOptionalSupport_spec x g δ k
  exact ⟨J, hJ, boxLinearStep_mem_feasibleBoxSteps hδ hx hJ.mem, boxLinearStep_isMinOn hJ⟩

/-- The zero-one vector of an actual optional support. -/
def supportIndicator (J : Finset ι) (i : ι) : ℝ := if i ∈ J then 1 else 0

omit [Fintype ι] in
/-- Support indicators take precisely the allowed binary values. -/
theorem supportIndicator_binary (J : Finset ι) (i : ι) :
    supportIndicator J i = 0 ∨ supportIndicator J i = 1 := by
  simp only [supportIndicator]
  split_ifs <;> simp

/-- The sum of a support indicator is the support cardinality. -/
@[simp] theorem sum_supportIndicator (J : Finset ι) :
    ∑ i, supportIndicator J i = (J.card : ℝ) := by
  simp [supportIndicator]

/-- Multiplication by the indicator recovers exactly the finite selected sum. -/
@[simp] theorem sum_supportIndicator_mul (J : Finset ι) (w : ι → ℝ) :
    ∑ i, supportIndicator J i * w i = ∑ i ∈ J, w i := by
  simp [supportIndicator, ite_mul]

/-- Feasibility for the binary optional selection problem, including zeros on mandatory indices. -/
def IsBinaryOptionalSelection (x : ι → ℝ) (δ : ℝ) (k : ℕ) (τ : ι → ℝ) : Prop :=
  (∀ i, τ i = 0 ∨ τ i = 1) ∧ (∀ i ∈ mandatoryIndices x δ, τ i = 0) ∧
    ∑ i, τ i ≤ (k - (mandatoryIndices x δ).card : ℕ)

omit [DecidableEq ι] in
/-- The binary feasibility interface exposes the binary, mandatory-zero and budget conditions. -/
@[simp] theorem isBinaryOptionalSelection_iff {x τ : ι → ℝ} {δ : ℝ} {k : ℕ} :
    IsBinaryOptionalSelection x δ k τ ↔
      (∀ i, τ i = 0 ∨ τ i = 1) ∧ (∀ i ∈ mandatoryIndices x δ, τ i = 0) ∧
        ∑ i, τ i ≤ (k - (mandatoryIndices x δ).card : ℕ) := Iff.rfl

/-- Every feasible optional support gives a feasible binary selection. -/
theorem supportIndicator_isBinaryOptionalSelection {x : ι → ℝ} {δ : ℝ} {k : ℕ}
    {J : Finset ι} (hJ : J ∈ optionalSupports x δ k) :
    IsBinaryOptionalSelection x δ k (supportIndicator J) := by
  obtain ⟨hd, hc⟩ := mem_optionalSupports.mp hJ
  refine ⟨supportIndicator_binary J, ?_, ?_⟩
  · intro i hi
    simp only [supportIndicator, ite_eq_right_iff, one_ne_zero, imp_false]
    exact fun h => Finset.disjoint_left.mp hd h hi
  · rw [sum_supportIndicator]
    exact_mod_cast hc

/-- Every feasible binary vector is the indicator of a feasible optional support. -/
theorem exists_optionalSupport_indicator {x τ : ι → ℝ} {δ : ℝ} {k : ℕ}
    (hτ : IsBinaryOptionalSelection x δ k τ) :
    ∃ J ∈ optionalSupports x δ k, τ = supportIndicator J := by
  let J := Finset.univ.filter (fun i => τ i = 1)
  have he : τ = supportIndicator J := by
    funext i
    rcases hτ.1 i with h | h <;> simp [supportIndicator, J, h]
  refine ⟨J, mem_optionalSupports.mpr ⟨?_, ?_⟩, he⟩
  · apply Finset.disjoint_left.mpr
    intro i hi him
    have h1 : τ i = 1 := (Finset.mem_filter.mp hi).2
    have h0 := hτ.2.1 i him
    linarith
  · have hc := hτ.2.2
    rw [he, sum_supportIndicator] at hc
    exact_mod_cast hc

/-- The finite maximum is exactly the binary maximum with the remaining cardinality budget. -/
theorem IsOptimalOptionalSupport.binary_maximal {x g : ι → ℝ} {δ : ℝ} {k : ℕ}
    {J : Finset ι} (hJ : IsOptimalOptionalSupport x g δ k J)
    {τ : ι → ℝ} (hτ : IsBinaryOptionalSelection x δ k τ) :
    ∑ i, τ i * optionalWeight x g δ i ≤
      ∑ i, supportIndicator J i * optionalWeight x g δ i := by
  obtain ⟨K, hK, rfl⟩ := exists_optionalSupport_indicator hτ
  simpa only [sum_supportIndicator_mul] using hJ.maximal K hK

end Optimization.SparseConstraints
