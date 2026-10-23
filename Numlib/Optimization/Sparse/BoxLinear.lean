import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Basic.Real.Sign
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Sparse linear optimization in a box

Coordinates larger than the box radius cannot be zeroed. They consume mandatory support
slots. Among the remaining coordinates, the improvement over zeroing is a finite gain,
and selecting the largest admissible total gain is exactly a cardinality knapsack problem.
The candidate step is proved box-feasible, sparse, and globally optimal for the actual
linear objective. All definitions depend only on the input vectors and radius.
-/

open Finset

namespace SparseBox
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite support of a vector. -/
noncomputable def support (x : ι → ℝ) : Finset ι := univ.filter (fun i => x i ≠ 0)

omit [DecidableEq ι] in
@[simp] theorem mem_support {x : ι → ℝ} {i : ι} : i ∈ support x ↔ x i ≠ 0 := by
  simp [support]

/-- Coordinates that no displacement in the radius box can zero. -/
noncomputable def forced (x : ι → ℝ) (δ : ℝ) : Finset ι := univ.filter (fun i => δ < |x i|)

omit [DecidableEq ι] in
@[simp] theorem mem_forced {x : ι → ℝ} {δ : ℝ} {i : ι} :
    i ∈ forced x δ ↔ δ < |x i| := by simp [forced]

/-- Genuine box and support-cardinality feasibility for a displacement. -/
def Admissible (x : ι → ℝ) (k : ℕ) (δ : ℝ) (d : ι → ℝ) : Prop :=
  (∀ i, |d i| ≤ δ) ∧ (support (fun i => x i + d i)).card ≤ k

omit [DecidableEq ι] in
/-- The coordinate box is exactly the infinity-norm ball, including empty index types. -/
theorem box_iff_norm_le {d : ι → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ i, |d i| ≤ δ) ↔ ‖d‖ ≤ δ := by
  simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg hδ (x := d)).symm

omit [DecidableEq ι] in
/-- Actual sparse box feasibility in the infinity-norm formulation. -/
theorem admissible_iff_norm {x d : ι → ℝ} {k : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) :
    Admissible x k δ d ↔ ‖d‖ ≤ δ ∧ (support (fun i => x i + d i)).card ≤ k := by
  exact and_congr (box_iff_norm_le hδ) Iff.rfl

/-- The actual linear objective of the box problem. -/
noncomputable def objective (g d : ι → ℝ) : ℝ := ∑ i, g i * d i

/-- The improvement obtained by retaining a coordinate instead of zeroing it. -/
noncomputable def gain (x g : ι → ℝ) (δ : ℝ) (i : ι) : ℝ := δ * |g i| - x i * g i

/-- The total gain of a support selection. -/
noncomputable def selectionGain (x g : ι → ℝ) (δ : ℝ) (R : Finset ι) : ℝ :=
  ∑ i ∈ R, gain x g δ i

/-- A finite binary selection, represented by the indices with binary value one. -/
def Selection (x : ι → ℝ) (k : ℕ) (δ : ℝ) (R : Finset ι) : Prop :=
  R ⊆ (forced x δ)ᶜ ∧ R.card ≤ k - (forced x δ).card

/-- A selection solves the actual finite cardinality knapsack maximization. -/
def IsOptimalSelection (x g : ι → ℝ) (k : ℕ) (δ : ℝ) (R : Finset ι) : Prop :=
  Selection x k δ R ∧ ∀ Q, Selection x k δ Q → selectionGain x g δ Q ≤ selectionGain x g δ R

/-- The explicit step: retained and mandatory coordinates take their best box endpoint;
all other coordinates are zeroed in the next iterate. -/
noncomputable def step (x g : ι → ℝ) (δ : ℝ) (R : Finset ι) (i : ι) : ℝ :=
  if i ∈ forced x δ ∨ i ∈ R then -δ * Real.sign (g i) else -x i

/-- A signed box endpoint has the exact minimal scalar objective value. -/
theorem sign_endpoint_value (g δ : ℝ) : g * (-δ * Real.sign g) = -δ * |g| := by
  rcases lt_trichotomy g 0 with hg | rfl | hg
  · rw [Real.sign_of_neg hg, abs_of_neg hg]; ring
  · simp
  · rw [Real.sign_of_pos hg, abs_of_pos hg]; ring

/-- Signed endpoints lie in the box even when the coefficient vanishes. -/
theorem sign_endpoint_abs_le (g : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    |-δ * Real.sign g| ≤ δ := by
  rcases Real.sign_apply_eq g with hg | hg | hg <;> rw [hg] <;> simp [abs_of_nonneg hδ]
  exact hδ

/-- Every box coordinate has objective value at least that of its signed endpoint. -/
theorem endpoint_le_mul (g d : ℝ) {δ : ℝ} (hd : |d| ≤ δ) : -δ * |g| ≤ g * d := by
  have hm := mul_le_mul_of_nonneg_left hd (abs_nonneg g)
  have hl := neg_abs_le (g * d)
  rw [abs_mul] at hl
  nlinarith

omit [DecidableEq ι] in
/-- Mandatory coordinates lie in the original support. -/
theorem forced_subset_support (x : ι → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    forced x δ ⊆ support x := by
  intro i hi
  rw [mem_forced] at hi
  rw [mem_support]
  intro hz
  simp only [hz, abs_zero] at hi
  linarith

omit [DecidableEq ι] in
/-- Every feasible displacement retains every mandatory coordinate. -/
theorem forced_subset_new_support (x : ι → ℝ) {δ : ℝ} {d : ι → ℝ}
    (hd : ∀ i, |d i| ≤ δ) : forced x δ ⊆ support (fun i => x i + d i) := by
  intro i hi
  rw [mem_forced] at hi
  rw [mem_support]
  intro hz
  have he : x i = -d i := by linarith
  rw [he, abs_neg] at hi
  exact (not_lt_of_ge (hd i)) hi

omit [DecidableEq ι] in
/-- Mandatory support consumes no more than the feasible sparsity budget. -/
theorem forced_card_le {x : ι → ℝ} {δ : ℝ} {k : ℕ} (hδ : 0 ≤ δ)
    (hx : (support x).card ≤ k) : (forced x δ).card ≤ k :=
  (Finset.card_le_card (forced_subset_support x hδ)).trans hx

/-- Every finite cardinality knapsack admits a maximizing selection. -/
theorem exists_optimalSelection (x g : ι → ℝ) (k : ℕ) (δ : ℝ) :
    ∃ R, IsOptimalSelection x g k δ R := by
  classical
  let S := univ.powerset.filter (Selection x k δ)
  have hS : ∅ ∈ S := by simp [S, Selection]
  obtain ⟨R, hR, hmax⟩ := S.exists_max_image (selectionGain x g δ) ⟨∅, hS⟩
  refine ⟨R, (mem_filter.mp hR).2, ?_⟩
  intro Q hQ
  exact hmax Q (by simp [S, hQ])

/-- A feasible selection gives a box-feasible step with the required support budget. -/
theorem step_admissible {x g : ι → ℝ} {δ : ℝ} {k : ℕ} {R : Finset ι}
    (hδ : 0 ≤ δ) (hx : (support x).card ≤ k) (hR : Selection x k δ R) :
    Admissible x k δ (step x g δ R) := by
  constructor
  · intro i
    by_cases hi : i ∈ forced x δ ∨ i ∈ R
    · simpa only [step, ite_eq_left hi] using sign_endpoint_abs_le (g i) hδ
    · have hnot : i ∉ forced x δ := fun h => hi (Or.inl h)
      simpa only [step, ite_eq_right hi, abs_neg] using le_of_not_gt (by simpa using hnot)
  · have hsupport : support (fun i => x i + step x g δ R i) ⊆ forced x δ ∪ R := by
      intro i hi
      by_contra hnot
      have hh : ¬(i ∈ forced x δ ∨ i ∈ R) := by simpa only [mem_union] using hnot
      have hz : x i + step x g δ R i = 0 := by simp only [step, ite_eq_right hh, add_neg_cancel]
      exact (mem_support.mp hi) hz
    have hcard := (card_le_card hsupport).trans (card_union_le (forced x δ) R)
    have hFk := forced_card_le hδ hx
    have hRcard := hR.2
    omega

/-- The optional support of any feasible displacement is an admissible binary selection. -/
theorem selection_of_admissible {x : ι → ℝ} {k : ℕ} {δ : ℝ} {d : ι → ℝ}
    (hd : Admissible x k δ d) :
    Selection x k δ (support (fun i => x i + d i) \ forced x δ) := by
  constructor
  · intro i hi
    exact mem_compl.mpr (mem_sdiff.mp hi).2
  · rw [card_sdiff_of_subset (forced_subset_new_support x hd.1)]
    exact Nat.sub_le_sub_right hd.2 _

/-- Objective value obtained by using the best box endpoint on mandatory coordinates
and zeroing all optional coordinates. -/
noncomputable def baseline (x g : ι → ℝ) (δ : ℝ) : ℝ :=
  ∑ i, if i ∈ forced x δ then -δ * |g i| else -x i * g i

/-- The candidate's exact objective is baseline minus the chosen knapsack gain. -/
theorem objective_step {x g : ι → ℝ} {δ : ℝ} {k : ℕ} {R : Finset ι}
    (hR : Selection x k δ R) :
    objective g (step x g δ R) = baseline x g δ - selectionGain x g δ R := by
  have hpoint (i : ι) : g i * step x g δ R i =
      (if i ∈ forced x δ then -δ * |g i| else -x i * g i) -
        (if i ∈ R then gain x g δ i else 0) := by
    by_cases hi : i ∈ forced x δ
    · have hiR : i ∉ R := fun h => (mem_compl.mp (hR.1 h)) hi
      simp only [step, hi, true_or, ite_true, hiR, ite_false, sub_zero]
      exact sign_endpoint_value _ _
    · by_cases hiR : i ∈ R
      · simp only [step, hi, hiR, false_or, ite_true, ite_false, gain]
        rw [sign_endpoint_value]
        ring
      · simp only [step, hi, hiR, or_self, ite_false, sub_zero]
        ring
  have heq := sum_congr (s₁ := (univ : Finset ι)) rfl (fun i _ => hpoint i)
  simpa only [objective, baseline, selectionGain, sum_sub_distrib, sum_ite_mem, univ_inter] using heq

/-- Any feasible step has objective at least baseline minus the gain of its optional
support. The comparison uses actual coordinates, with no optimality assumption. -/
theorem baseline_sub_gain_le_objective {x g : ι → ℝ} {δ : ℝ} {k : ℕ} {d : ι → ℝ}
    (hd : Admissible x k δ d) :
    baseline x g δ - selectionGain x g δ (support (fun i => x i + d i) \ forced x δ) ≤
      objective g d := by
  let T := support (fun i => x i + d i) \ forced x δ
  have hpoint (i : ι) :
      (if i ∈ forced x δ then -δ * |g i| else -x i * g i) -
        (if i ∈ T then gain x g δ i else 0) ≤ g i * d i := by
    by_cases hi : i ∈ forced x δ
    · have hiT : i ∉ T := by simp [T, hi]
      simp only [hi, ite_true, hiT, ite_false, sub_zero]
      exact endpoint_le_mul (g i) (d i) (hd.1 i)
    · by_cases hiT : i ∈ T
      · simp only [hi, ite_false, hiT, ite_true, gain]
        have he : -x i * g i - (δ * |g i| - x i * g i) = -δ * |g i| := by ring
        rw [he]
        exact endpoint_le_mul (g i) (d i) (hd.1 i)
      · have hz : x i + d i = 0 := by
          by_contra hz
          exact hiT (mem_sdiff.mpr ⟨mem_support.mpr hz, hi⟩)
        simp only [hi, ite_false, hiT, sub_zero]
        have hdi : d i = -x i := by linarith
        rw [hdi]
        ring_nf
        exact le_rfl
  have hh := sum_le_sum (s := (univ : Finset ι)) (fun i _ => hpoint i)
  simpa only [objective, baseline, selectionGain, sum_sub_distrib, sum_ite_mem, univ_inter, T] using hh

/-- Every true knapsack maximizer produces a globally optimal sparse box step. -/
theorem step_isMinOn {x g : ι → ℝ} {δ : ℝ} {k : ℕ} {R : Finset ι}
    (hδ : 0 ≤ δ) (hx : (support x).card ≤ k) (hR : IsOptimalSelection x g k δ R) :
    Admissible x k δ (step x g δ R) ∧
      IsMinOn (objective g) {d | Admissible x k δ d} (step x g δ R) := by
  refine ⟨step_admissible hδ hx hR.1, ?_⟩
  intro d hd
  change objective g (step x g δ R) ≤ objective g d
  rw [objective_step hR.1]
  have hg := hR.2 _ (selection_of_admissible hd)
  exact (sub_le_sub_left hg _).trans (baseline_sub_gain_le_objective hd)

/-- The binary variable recording whether an optional coordinate is retained. -/
noncomputable def binary (R : Finset ι) (i : ι) : ℝ := if i ∈ R then 1 else 0

omit [Fintype ι] in
/-- Each selection variable takes one of the two binary values. -/
theorem binary_values (R : Finset ι) (i : ι) : binary R i = 0 ∨ binary R i = 1 := by
  by_cases hi : i ∈ R <;> simp [binary, hi]

/-- The explicit optimizer in coordinate form of the three sums in (14.2.20). -/
theorem step_eq_coordinate (x g : ι → ℝ) (δ : ℝ) (R : Finset ι) (i : ι) :
    step x g δ R i = if i ∈ forced x δ then -δ * Real.sign (g i)
      else -x i - binary R i * (δ * Real.sign (g i) - x i) := by
  by_cases hi : i ∈ forced x δ <;> by_cases hiR : i ∈ R <;>
    simp only [step, binary, hi, hiR, true_or, false_or, or_false, ite_true, ite_false] <;> ring

/-- The binary variables' cardinality sum equals the selected support size. -/
theorem sum_binary {x : ι → ℝ} {δ : ℝ} {k : ℕ} {R : Finset ι}
    (hR : Selection x k δ R) : ∑ i ∈ (forced x δ)ᶜ, binary R i = (R.card : ℝ) := by
  simp only [binary, sum_ite_mem, inter_eq_right.mpr hR.1, sum_const, nsmul_eq_mul,
    mul_one]

/-- The finite-set gain is the binary knapsack objective in (14.2.21). -/
theorem selectionGain_eq_binary_sum {x g : ι → ℝ} {δ : ℝ} {k : ℕ} {R : Finset ι}
    (hR : Selection x k δ R) : selectionGain x g δ R =
      ∑ i ∈ (forced x δ)ᶜ, binary R i * (δ * |g i| - x i * g i) := by
  simp only [binary, ite_mul, one_mul, zero_mul, sum_ite_mem, inter_eq_right.mpr hR.1,
    selectionGain, gain]

omit [Fintype ι] in
/-- A finite sum of coordinate vectors evaluates to the corresponding indicator. -/
theorem sum_single_apply (S : Finset ι) (a : ι → ℝ) (i : ι) :
    (∑ j ∈ S, Pi.single j (a j)) i = if i ∈ S then a i else 0 := by
  simp [Finset.sum_apply, Pi.single_apply]

/-- The optimizer equals the three coordinate-vector sums in (14.2.20). -/
theorem step_eq_sub_sums (x g : ι → ℝ) (δ : ℝ) (R : Finset ι) :
    step x g δ R =
      (∑ i ∈ forced x δ, Pi.single i (-δ * Real.sign (g i))) -
      (∑ i ∈ support x \ forced x δ, Pi.single i (x i)) -
      (∑ i ∈ (forced x δ)ᶜ, Pi.single i (binary R i * (δ * Real.sign (g i) - x i))) := by
  ext i
  simp only [Pi.sub_apply, sum_single_apply, step_eq_coordinate]
  by_cases hi : i ∈ forced x δ
  · simp only [hi, ite_true, mem_sdiff, not_true_eq_false, and_false, ite_false,
      mem_compl, sub_zero]
  · by_cases hx : x i = 0
    · simp only [hi, ite_false, mem_sdiff, not_false_eq_true, and_true,
        mem_support, hx, ne_eq, not_true_eq_false, mem_compl, ite_true]
      ring
    · simp only [hi, ite_false, mem_sdiff, not_false_eq_true, and_true,
        mem_support, hx, ne_eq, mem_compl, ite_true]
      ring

end SparseBox
