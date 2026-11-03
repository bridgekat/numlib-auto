import NumlibSurface.ConnGouldToint.Chapter06.Section04
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Structured trust regions

Element objectives and models are invariant along their corresponding null subspaces.
Their trust regions constrain only the projected components of the trial step.
-/

open scoped BigOperators
open Set

namespace ConnGouldToint.Chapter10

open Chapter06

section Geometry

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Translation along the invariant subspace leaves the element unchanged. -/
def InvariantAlong {F : Type*} (N : Submodule ℝ E) (f : E → F) : Prop :=
  ∀ x w, w ∈ N → f (x + w) = f x

/-- The partial separability representation (10.2.2). Each element is invariant
along a nontrivial subspace. Its range subspace is the orthogonal complement. -/
structure PartiallySeparable [Fintype ι] (f : E → ℝ)
    (elements : ι → E → ℝ) (N : ι → Submodule ℝ E) : Prop where
  sum_elements : ∀ x, f x = ∑ i, elements i x
  nontrivial : ∀ i, N i ≠ ⊥
  invariant : ∀ i, InvariantAlong (N i) (elements i)

/-- The objective in the fully separable case (10.2.1). -/
def separableObjective [Fintype ι] {X : ι → Type*} (elements : ∀ i, X i → ℝ)
    (x : ∀ i, X i) : ℝ :=
  ∑ i, elements i (x i)

/-- The cylinder (10.2.3) for the element whose invariant subspace is `N`. -/
def elementTrustRegion (p : Seminorm ℝ E) (N : Submodule ℝ E)
    [Nᗮ.HasOrthogonalProjection] (x : E) (Δ : ℝ) : Set E :=
  {y | p (Nᗮ.starProjection (y - x)) ≤ Δ}

/-- The overall trust region is the intersection of the element cylinders. -/
def structuredTrustRegion [CompleteSpace E] (p : Seminorm ℝ E) (N : ι → Submodule ℝ E)
    (x : E) (Δ : ι → ℝ) : Set E :=
  ⋂ i, elementTrustRegion p (N i) x (Δ i)

/-- The minimum element radius (10.2.4). -/
noncomputable def minimumRadius [Fintype ι] [Nonempty ι] (Δ : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty Δ

private theorem structuredTrustRegion_convex [CompleteSpace E]
    (p : Seminorm ℝ E) (N : ι → Submodule ℝ E) (x : E) (Δ : ι → ℝ) :
    Convex ℝ (structuredTrustRegion p N x Δ) := by
  apply convex_iInter
  intro i
  exact ((p.comp (N i)ᗮ.starProjection.toLinearMap).convex_closedBall x (Δ i))

end Geometry

/-- The structured radius parameters and their compatibility condition (10.2.5). -/
structure StructuredTRParams extends BTRParams where
  η₃ : ℝ
  μ₁ : ℝ
  μ₂ : ℝ
  eta₂_lt_eta₃ : η₂ < η₃
  eta₃_lt_one : η₃ < 1
  mu₁_pos : 0 < μ₁
  mu₁_lt_mu₂ : μ₁ < μ₂
  mu₂_lt_one : μ₂ < 1
  compatible : μ₁ + μ₂ ≤ η₂ - η₁

/-- The ratio test (10.2.6) is equivalent to the signed-free test (10.2.7)
when the predicted decrease is strictly positive. At zero the ratio test
has no such interpretation. -/
theorem elementRatio_iff_fit {a d η : ℝ} (hd : 0 < d) :
    η ≤ a / d ↔ d - (1 - η) * |d| ≤ a := by
  rw [le_div_iff₀ hd, abs_of_pos hd]
  have h : d - (1 - η) * d = η * d := by ring
  rw [h]

/-- At zero predicted decrease, the two tests in (10.2.6) and (10.2.7) can disagree. -/
theorem elementRatio_zero_counterexample :
    ¬ ((1 / 2 : ℝ) ≤ 0 / 0 ↔ (0 : ℝ) - (1 - 1 / 2) * |0| ≤ 0) := by norm_num

section Radii

variable {ι : Type*} [Fintype ι]

/-- The negligible set (10.2.8), using the total predicted change. -/
noncomputable def negligibleElements (μ : ℝ) (d : ι → ℝ) : Finset ι :=
  open Classical in
  Finset.univ.filter fun i ↦ |d i| ≤ μ / Fintype.card ι * ∑ j, d j

/-- The complement of the negligible set, within the finite element family. -/
noncomputable def meaningfulElements (μ : ℝ) (d : ι → ℝ) : Finset ι :=
  open Classical in
  Finset.univ \ negligibleElements μ d

/-- The fit test (10.2.9) or (10.2.12), according to the choice of `η`. -/
def elementFit (η : ℝ) (d a : ι → ℝ) (i : ι) : Prop :=
  d i - (1 - η) / Fintype.card ι * ∑ j, d j ≤ a i

/-- The total acceptance test (10.2.10). -/
def structuredSuccessful (η₁ : ℝ) (d a : ι → ℝ) : Prop :=
  η₁ * (∑ i, d i) ≤ ∑ i, a i

/-- With positive total predicted decrease, (10.2.10) is the ratio test in
Step 3 of Algorithm 10.2.2. -/
theorem structuredSuccessful_iff_ratio (η₁ : ℝ) {d a : ι → ℝ} (hd : 0 < ∑ i, d i) :
    structuredSuccessful η₁ d a ↔ η₁ ≤ (∑ i, a i) / ∑ i, d i :=
  (le_div_iff₀ hd).symm

/-- The fit test (10.2.13) used for a negligible element. -/
def negligibleFit (μ₂ : ℝ) (d a : ι → ℝ) (i : ι) : Prop :=
  |a i| ≤ μ₂ / Fintype.card ι * ∑ j, d j

/-- The seven radius update cases of Algorithm 10.2.1. -/
structure StructuredRadiusUpdate (P : StructuredTRParams) (d a Δ Δ' : ι → ℝ) : Prop where
  meaningful_expand : ∀ i ∈ meaningfulElements P.μ₁ d,
    elementFit P.η₃ d a i → structuredSuccessful P.η₁ d a → Δ i ≤ Δ' i
  meaningful_hold : ∀ i ∈ meaningfulElements P.μ₁ d,
    elementFit P.η₃ d a i → ¬ structuredSuccessful P.η₁ d a → Δ' i = Δ i
  meaningful_moderate : ∀ i ∈ meaningfulElements P.μ₁ d,
    ¬ elementFit P.η₃ d a i → elementFit P.η₂ d a i →
      P.γ₂ * Δ i ≤ Δ' i ∧ Δ' i ≤ Δ i
  meaningful_contract : ∀ i ∈ meaningfulElements P.μ₁ d,
    ¬ elementFit P.η₂ d a i → P.γ₁ * Δ i ≤ Δ' i ∧ Δ' i ≤ P.γ₂ * Δ i
  negligible_expand : ∀ i ∈ negligibleElements P.μ₁ d,
    negligibleFit P.μ₂ d a i → structuredSuccessful P.η₁ d a → Δ i ≤ Δ' i
  negligible_hold : ∀ i ∈ negligibleElements P.μ₁ d,
    negligibleFit P.μ₂ d a i → ¬ structuredSuccessful P.η₁ d a → Δ' i = Δ i
  negligible_contract : ∀ i ∈ negligibleElements P.μ₁ d,
    ¬ negligibleFit P.μ₂ d a i → P.γ₁ * Δ i ≤ Δ' i ∧ Δ' i ≤ P.γ₂ * Δ i

private theorem mem_negligibleElements {μ : ℝ} {d : ι → ℝ} {i : ι} :
    i ∈ negligibleElements μ d ↔ |d i| ≤ μ / Fintype.card ι * ∑ j, d j := by
  classical
  simp [negligibleElements]

private theorem mem_meaningfulElements {μ : ℝ} {d : ι → ℝ} {i : ι} :
    i ∈ meaningfulElements μ d ↔ i ∉ negligibleElements μ d := by
  classical
  simp [meaningfulElements]

/-- Lemma 10.2.1(ii). Every element radius retains at least the fraction `γ₁`. -/
theorem lemma_10_2_1_ii {P : StructuredTRParams} {d a Δ Δ' : ι → ℝ}
    (hu : StructuredRadiusUpdate P d a Δ Δ') (hΔ : ∀ i, 0 ≤ Δ i) (i : ι) :
    P.γ₁ * Δ i ≤ Δ' i := by
  have h₁₂ : P.γ₁ * Δ i ≤ P.γ₂ * Δ i :=
    mul_le_mul_of_nonneg_right P.gamma₁_le_gamma₂ (hΔ i)
  have h₁ : P.γ₁ * Δ i ≤ Δ i :=
    h₁₂.trans (mul_le_of_le_one_left (hΔ i) P.gamma₂_lt_one.le)
  by_cases hn : i ∈ negligibleElements P.μ₁ d
  · by_cases hfit : negligibleFit P.μ₂ d a i
    · by_cases hs : structuredSuccessful P.η₁ d a
      · exact h₁.trans (hu.negligible_expand i hn hfit hs)
      · rwa [hu.negligible_hold i hn hfit hs]
    · exact (hu.negligible_contract i hn hfit).1
  · have hm := mem_meaningfulElements.mpr hn
    by_cases hfit : elementFit P.η₃ d a i
    · by_cases hs : structuredSuccessful P.η₁ d a
      · exact h₁.trans (hu.meaningful_expand i hm hfit hs)
      · rwa [hu.meaningful_hold i hm hfit hs]
    · by_cases hmoderate : elementFit P.η₂ d a i
      · exact h₁₂.trans (hu.meaningful_moderate i hm hfit hmoderate).1
      · exact (hu.meaningful_contract i hm hmoderate).1

private theorem sum_meaningful_add_sum_negligible (μ : ℝ) (d a : ι → ℝ) :
    (∑ i ∈ meaningfulElements μ d, a i) + (∑ i ∈ negligibleElements μ d, a i) = ∑ i, a i := by
  classical
  exact Finset.sum_sdiff (Finset.subset_univ _)

private theorem card_meaningful_add_card_negligible (μ : ℝ) (d : ι → ℝ) :
    (meaningfulElements μ d).card + (negligibleElements μ d).card = Fintype.card ι := by
  classical
  simpa only [meaningfulElements, Finset.card_univ] using Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (negligibleElements μ d))

variable [Nonempty ι]

private theorem negligible_card_bound {μ : ℝ} {d : ι → ℝ} (hμ : μ < 1)
    (hd : 0 < ∑ i, d i) :
    (meaningfulElements μ d).Nonempty ∧
      ((negligibleElements μ d).card : ℝ) ≤ (Fintype.card ι : ℝ) - 1 := by
  classical
  have hp : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hM : (meaningfulElements μ d).Nonempty := by
    by_contra hn
    have hsmall (i : ι) : |d i| ≤ μ / Fintype.card ι * ∑ j, d j :=
      mem_negligibleElements.mp (by
        by_contra hi
        exact hn ⟨i, mem_meaningfulElements.mpr hi⟩)
    have hle : (∑ i, d i) ≤ μ * ∑ i, d i := calc
      _ ≤ ∑ _i : ι, μ / Fintype.card ι * ∑ j, d j :=
        Finset.sum_le_sum fun i _ ↦ (le_abs_self _).trans (hsmall i)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
    exact ((mul_lt_mul_of_pos_right hμ hd).not_ge (by simpa using hle))
  have hcard := card_meaningful_add_card_negligible μ d
  have hMpos : 1 ≤ (meaningfulElements μ d).card := Finset.card_pos.mpr hM
  refine ⟨hM, ?_⟩
  have hle : (negligibleElements μ d).card + 1 ≤ Fintype.card ι := by omega
  have hle' : ((negligibleElements μ d).card : ℝ) + 1 ≤ Fintype.card ι := by exact_mod_cast hle
  linarith

omit [Nonempty ι] in
private theorem sum_abs_le_card_bound {d a : ι → ℝ} {μ c : ℝ}
    (hcard : ((negligibleElements μ d).card : ℝ) ≤ (Fintype.card ι : ℝ) - 1)
    (hc : 0 ≤ c) (ha : ∀ i ∈ negligibleElements μ d, |a i| ≤ c) :
    (∑ i ∈ negligibleElements μ d, |a i|) ≤ ((Fintype.card ι : ℝ) - 1) * c := calc
  _ ≤ ∑ _i ∈ negligibleElements μ d, c := Finset.sum_le_sum ha
  _ ≤ _ := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard hc

/-- Lemma 10.2.1(i). A positive total predicted change forces a meaningful
element, and the sum of the meaningful changes lies in (10.2.14). -/
theorem lemma_10_2_1_i {μ : ℝ} {d : ι → ℝ} (hμ₀ : 0 ≤ μ) (hμ₁ : μ < 1)
    (hd : 0 < ∑ i, d i) :
    (meaningfulElements μ d).Nonempty ∧
      (1 - ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * μ) * (∑ i, d i) ≤
        (∑ i ∈ meaningfulElements μ d, d i) ∧
      (∑ i ∈ meaningfulElements μ d, d i) ≤
        (1 + ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * μ) * (∑ i, d i) := by
  obtain ⟨hm, hcard⟩ := negligible_card_bound hμ₁ hd
  have hsum := sum_meaningful_add_sum_negligible μ d d
  have habs := sum_abs_le_card_bound (a := d) hcard
    (show 0 ≤ μ / Fintype.card ι * ∑ i, d i by positivity)
    (fun _ hi ↦ mem_negligibleElements.mp hi)
  have hnegligible := (Finset.abs_sum_le_sum_abs _ _).trans habs
  have hscale :
      ((Fintype.card ι : ℝ) - 1) * (μ / Fintype.card ι * ∑ i, d i) =
      (((Fintype.card ι : ℝ) - 1) / Fintype.card ι * μ) * ∑ i, d i := by ring
  rw [hscale] at hnegligible
  refine ⟨hm, ?_, ?_⟩ <;> nlinarith [(abs_le.mp hnegligible).1, (abs_le.mp hnegligible).2]

/-- Lemma 10.2.2. The element fit tests imply global acceptance. The conclusion
includes both intermediate estimates (10.2.16)–(10.2.17). -/
theorem lemma_10_2_2 (P : StructuredTRParams) {d a : ι → ℝ}
    (hd : 0 < ∑ i, d i)
    (hm : ∀ i ∈ meaningfulElements P.μ₁ d, elementFit P.η₂ d a i)
    (hn : ∀ i ∈ negligibleElements P.μ₁ d, negligibleFit P.μ₂ d a i) :
    (P.η₂ - ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * P.μ₁) * (∑ i, d i) ≤
        (∑ i ∈ meaningfulElements P.μ₁ d, a i) ∧
      (∑ i ∈ negligibleElements P.μ₁ d, |a i|) ≤
        ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * P.μ₂ * (∑ i, d i) ∧
      structuredSuccessful P.η₁ d a := by
  classical
  have hμ₁ := P.mu₁_lt_mu₂.trans P.mu₂_lt_one
  have hμ₂ := P.mu₁_pos.trans P.mu₁_lt_mu₂
  have hp : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have ⟨_, hcard⟩ := negligible_card_bound hμ₁ hd
  have ⟨_, hlower, _⟩ := lemma_10_2_1_i P.mu₁_pos.le hμ₁ hd
  let c := (1 - P.η₂) / Fintype.card ι * ∑ i, d i
  have hc : 0 ≤ c := mul_nonneg (div_nonneg (sub_nonneg.mpr P.eta₂_lt_one.le) hp.le) hd.le
  have hcardM : ((meaningfulElements P.μ₁ d).card : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Finset.card_le_univ (meaningfulElements P.μ₁ d)
  have hfit :
      (∑ i ∈ meaningfulElements P.μ₁ d, d i) - (1 - P.η₂) * (∑ i, d i) ≤
        ∑ i ∈ meaningfulElements P.μ₁ d, a i := by
    have hsum : (∑ i ∈ meaningfulElements P.μ₁ d, (d i - c)) ≤
        ∑ i ∈ meaningfulElements P.μ₁ d, a i :=
      Finset.sum_le_sum hm
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
    have hscale : (Fintype.card ι : ℝ) * c = (1 - P.η₂) * (∑ i, d i) := by
      dsimp [c]
      field_simp
    rw [← hscale]
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_right hcardM hc) _).trans hsum
  have hM : (P.η₂ - ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * P.μ₁) * (∑ i, d i) ≤
      ∑ i ∈ meaningfulElements P.μ₁ d, a i := by
    nlinarith only [hlower, hfit]
  have hN : (∑ i ∈ negligibleElements P.μ₁ d, |a i|) ≤
      ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * P.μ₂ * (∑ i, d i) :=
    (sum_abs_le_card_bound hcard (show 0 ≤ P.μ₂ / Fintype.card ι * ∑ i, d i by positivity)
      hn).trans_eq (by ring)
  refine ⟨hM, hN, ?_⟩
  have hsplit := sum_meaningful_add_sum_negligible P.μ₁ d a
  have habs := Finset.abs_sum_le_sum_abs a (negligibleElements P.μ₁ d)
  have hneg := (abs_le.mp (habs.trans hN)).1
  let α := ((Fintype.card ι : ℝ) - 1) / Fintype.card ι
  have hα : α ≤ 1 := (div_le_iff₀ hp).mpr (by linarith)
  have hsuccess : P.η₁ ≤ P.η₂ - α * P.μ₁ - α * P.μ₂ := by
    linarith [P.compatible, mul_le_of_le_one_left P.mu₁_pos.le hα,
      mul_le_of_le_one_left hμ₂.le hα]
  have hscaled := mul_le_mul_of_nonneg_right hsuccess hd.le
  change P.η₁ * (∑ i, d i) ≤ ∑ i, a i
  dsimp only [α] at hscaled
  nlinarith only [hsplit, hM, hneg, hscaled]

end Radii

section Run

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype ι] [Nonempty ι]

/-- The structured sufficient-decrease condition AA.1s. For a nonzero step,
`p s` is the ratio of `‖s‖` to the step norm conversion factor. -/
def structuredSufficientDecrease (model : E → ℝ) (x s : E) (p : Seminorm ℝ E)
    (Δ : ι → ℝ) (β κ : ℝ) : Prop :=
  κ * ‖gradient model x‖ * min (‖gradient model x‖ / β) (max (minimumRadius Δ) (p s)) ≤
    model x - model (x + s)

open Classical in
/-- An infinite structured trust-region run following Algorithm 10.2.2.
The element objectives and models share the specified invariant subspaces. -/
structure StructuredTRRun (P : StructuredTRParams) (elements : ι → E → ℝ)
    (N : ι → Submodule ℝ E) (β : ℕ → ℝ) (κ : ℝ) where
  x : ℕ → E
  s : ℕ → E
  p : ℕ → Seminorm ℝ E
  model : ℕ → ι → E → ℝ
  Δ : ℕ → ι → ℝ
  norm_separates : ∀ k v, p k v = 0 → v = 0
  invariant_nontrivial : ∀ i, N i ≠ ⊥
  objective_invariant : ∀ i, InvariantAlong (N i) (elements i)
  model_invariant : ∀ k i, InvariantAlong (N i) (model k i)
  initial_pos : ∀ i, 0 < Δ 0 i
  β_pos : ∀ k, 0 < β k
  κ_pos : 0 < κ
  feasible : ∀ k, x k + s k ∈ structuredTrustRegion (p k) N (x k) (Δ k)
  sufficient : ∀ k, structuredSufficientDecrease (fun z ↦ ∑ i, model k i z)
    (x k) (s k) (p k) (Δ k) (β k) κ
  predicted_pos : ∀ k, 0 < ∑ i, (model k i (x k) - model k i (x k + s k))
  radius_update : ∀ k,
    StructuredRadiusUpdate P (fun i ↦ model k i (x k) - model k i (x k + s k))
      (fun i ↦ elements i (x k) - elements i (x k + s k)) (Δ k) (Δ (k + 1))
  iterate_update : ∀ k, x (k + 1) =
    if structuredSuccessful P.η₁ (fun i ↦ model k i (x k) - model k i (x k + s k))
        (fun i ↦ elements i (x k) - elements i (x k + s k))
    then x k + s k else x k

/-- All radii in a structured run remain positive by Lemma 10.2.1(ii). -/
theorem StructuredTRRun.delta_pos {P : StructuredTRParams} {elements : ι → E → ℝ}
    {N : ι → Submodule ℝ E} {β : ℕ → ℝ} {κ : ℝ}
    (run : StructuredTRRun P elements N β κ) (k : ℕ) (i : ι) : 0 < run.Δ k i := by
  induction k generalizing i with
  | zero => exact run.initial_pos i
  | succ k ih =>
    exact (mul_pos P.gamma₁_pos (ih i)).trans_le
      (lemma_10_2_1_ii (run.radius_update k) (fun j ↦ (ih j).le) i)

end Run

section Accuracy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem InvariantAlong.fderiv_invariant {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {N : Submodule ℝ E} {f : E → F} (hf : InvariantAlong N f) :
    InvariantAlong N (fderiv ℝ f) := by
  intro x w hw
  rw [← fderiv_comp_add_right]
  rw [show (fun y ↦ f (y + w)) = f from funext fun y ↦ hf y w hw]

private theorem InvariantAlong.differentiableAt_add_iff {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {N : Submodule ℝ E} {f : E → F} (hf : InvariantAlong N f)
    {x w : E} (hw : w ∈ N) :
    DifferentiableAt ℝ f (x + w) ↔ DifferentiableAt ℝ f x := by
  rw [← differentiableAt_comp_add_right]
  rw [show (fun y ↦ f (y + w)) = f from funext fun y ↦ hf y w hw]

private theorem element_taylor_bound {N : Submodule ℝ E} [N.HasOrthogonalProjection]
    {f : E → ℝ} {x s : E} {C : ℝ} (hf : InvariantAlong N f)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ f (x + t • s))
    (hdd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fderiv ℝ f) (x + t • s))
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ (fderiv ℝ f) (x + t • s)‖ ≤ C) :
    |f (x + s) - (f x + fderiv ℝ f x (Nᗮ.starProjection s))| ≤
      (1 / 2 : ℝ) * C * ‖Nᗮ.starProjection s‖ ^ 2 := by
  let q := Nᗮ.starProjection s
  let n := N.starProjection s
  have hn : n ∈ N := N.starProjection_apply_mem s
  have hq : n + q = s := N.starProjection_add_starProjection_orthogonal s
  have hshift (t : ℝ) : (x + t • q) + t • n = x + t • s := by
    rw [add_assoc, ← smul_add, add_comm q n, hq]
  have hsegment (z : E) (hz : z ∈ segment ℝ x (x + q)) :
      ∃ t ∈ Icc (0 : ℝ) 1, x + t • q = z := by
    rw [segment_eq_image', add_sub_cancel_left] at hz
    exact hz
  have hbound := norm_sub_firstOrder_le_of_hessian_bound
    (convex_segment (𝕜 := ℝ) x (x + q)) (left_mem_segment ℝ x (x + q))
    (right_mem_segment ℝ x (x + q))
    (f := f) (s := q)
    (fun z hz ↦ by
      obtain ⟨t, ht, rfl⟩ := hsegment z hz
      apply (hf.differentiableAt_add_iff (N.smul_mem t hn)).mp
      rw [hshift]
      exact hd t ht)
    (fun z hz ↦ by
      obtain ⟨t, ht, rfl⟩ := hsegment z hz
      apply (hf.fderiv_invariant.differentiableAt_add_iff (N.smul_mem t hn)).mp
      rw [hshift]
      exact hdd t ht)
    (fun z hz ↦ by
      obtain ⟨t, ht, rfl⟩ := hsegment z hz
      rw [← hf.fderiv_invariant.fderiv_invariant (x + t • q) (t • n) (N.smul_mem t hn), hshift]
      exact hC t ht)
  have hval : f (x + s) = f (x + q) := by
    have h := hshift 1
    simp only [one_smul] at h
    rw [← h]
    exact hf (x + q) n hn
  rw [Real.norm_eq_abs] at hbound
  rwa [hval]

private theorem InvariantAlong.value_at_projection {F : Type*}
    {N : Submodule ℝ E} [N.HasOrthogonalProjection] {f : E → F}
    (hf : InvariantAlong N f) (z : E) : f z = f (Nᗮ.starProjection z) := by
  have hz : Nᗮ.starProjection z + N.starProjection z = z := by
    rw [add_comm]
    exact N.starProjection_add_starProjection_orthogonal z
  conv_lhs => rw [← hz]
  exact hf (Nᗮ.starProjection z) (N.starProjection z) (N.starProjection_apply_mem z)

variable {ι : Type*} [Fintype ι] [Nonempty ι] [CompleteSpace E]
  {P : StructuredTRParams} {elements : ι → E → ℝ} {N : ι → Submodule ℝ E}
  {β : ℕ → ℝ} {κ : ℝ} [∀ i, (N i).HasOrthogonalProjection]

private theorem StructuredTRRun.segment_mem (run : StructuredTRRun P elements N β κ)
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    run.x k + t • run.s k ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) := by
  have hx : run.x k ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) := by
    rw [structuredTrustRegion, mem_iInter]
    intro i
    simpa [elementTrustRegion] using (run.delta_pos k i).le
  simpa only [add_sub_cancel_left] using
    (structuredTrustRegion_convex (run.p k) N (run.x k) (run.Δ k)).add_smul_sub_mem
      hx (run.feasible k) ht

private theorem StructuredTRRun.projected_step_le (run : StructuredTRRun P elements N β κ)
    {K : ℝ} (hK : 0 ≤ K) (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v) (k : ℕ) (i : ι) :
    ‖(N i)ᗮ.starProjection (run.s k)‖ ≤ K * run.Δ k i := by
  have h := run.feasible k
  rw [structuredTrustRegion, mem_iInter] at h
  have hi : run.p k ((N i)ᗮ.starProjection (run.s k)) ≤ run.Δ k i := by
    simpa [elementTrustRegion] using h i
  exact (hnorm k _).trans (mul_le_mul_of_nonneg_left hi hK)

/-- Theorem 10.2.3. The error for each element is quadratic in its own radius.
The model Hessian bound is required on the full structured trust region.
Translation invariance permits the projected step estimate without requiring
the projected trial point to belong to that region. -/
theorem theorem_10_2_3 (run : StructuredTRRun P elements N β κ)
    {K κf κm : ℝ} (hK : 1 ≤ K) (hκf : 1 ≤ κf) (hκm : 1 ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hf : ∀ i, ContDiff ℝ 2 (elements i))
    (hF : ∀ i z, z ∈ (N i)ᗮ → ‖fderiv ℝ (fderiv ℝ (elements i)) z‖ ≤ κf)
    (hm : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      DifferentiableAt ℝ (run.model k i) z)
    (hDm : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      DifferentiableAt ℝ (fderiv ℝ (run.model k i)) z)
    (hM : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ‖fderiv ℝ (fderiv ℝ (run.model k i)) z‖ ≤ κm - 1)
    (hval : ∀ k i, run.model k i (run.x k) = elements i (run.x k))
    (hgrad : ∀ k i, fderiv ℝ (run.model k i) (run.x k) = fderiv ℝ (elements i) (run.x k))
    (k : ℕ) (i : ι) :
    1 ≤ uniformHessianConstant K κf κm ∧
      |elements i (run.x k + run.s k) - run.model k i (run.x k + run.s k)| ≤
        uniformHessianConstant K κf κm * (run.Δ k i) ^ 2 := by
  refine ⟨?_, ?_⟩
  · have hK₂ : 1 ≤ K ^ 2 := by nlinarith
    exact one_le_mul_of_one_le_of_one_le hK₂ (hκm.trans (le_max_right _ _))
  let q := (N i)ᗮ.starProjection (run.s k)
  let C := max κf κm
  have hC : 0 ≤ C := (zero_le_one.trans hκf).trans (le_max_left _ _)
  have hq := run.projected_step_le (zero_le_one.trans hK) hnorm k i
  have hfun := element_taylor_bound (run.objective_invariant i) (C := C)
    (x := run.x k) (s := run.s k)
    (fun t _ ↦ (hf i).differentiable (by norm_num) _)
    (fun t _ ↦ ((hf i).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) _)
    (fun t _ ↦ by
      rw [(run.objective_invariant i).fderiv_invariant.fderiv_invariant.value_at_projection]
      exact (hF i _ ((N i)ᗮ.starProjection_apply_mem _)).trans (le_max_left _ _))
  have hmod := element_taylor_bound (run.model_invariant k i) (C := C)
    (fun t ht ↦ hm k i _ (run.segment_mem k ht))
    (fun t ht ↦ hDm k i _ (run.segment_mem k ht))
    (fun t ht ↦ (hM k i _ (run.segment_mem k ht)).trans
      ((by linarith : κm - 1 ≤ κm).trans (le_max_right _ _)))
  rw [hval k i, hgrad k i] at hmod
  have herr :
      |elements i (run.x k + run.s k) - run.model k i (run.x k + run.s k)| ≤ C * ‖q‖ ^ 2 := by
    have h₁ := abs_le.mp hfun
    have h₂ := abs_le.mp hmod
    change _ ≤ (1 / 2 : ℝ) * C * ‖q‖ ^ 2 at hfun hmod
    apply abs_le.mpr
    constructor <;> linarith only [h₁.1, h₁.2, h₂.1, h₂.2]
  calc
    _ ≤ C * ‖q‖ ^ 2 := herr
    _ ≤ C * (K * run.Δ k i) ^ 2 := by gcongr
    _ = _ := by unfold uniformHessianConstant C; ring

/-- Lemma 10.2.4. The small element radius condition bounds the element model
change linearly in that radius. The estimate uses the bounded objective
element gradients of AF.5s and the model Hessian bound of AM.4s. -/
theorem lemma_10_2_4 (run : StructuredTRRun P elements N β κ)
    {K κfg κm : ℝ} (hK : 1 ≤ K) (hκfg : 0 < κfg) (hκm : 1 ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hF : ∀ i z, z ∈ (N i)ᗮ → ‖gradient (elements i) z‖ ≤ κfg)
    (hm : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      DifferentiableAt ℝ (run.model k i) z)
    (hDm : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      DifferentiableAt ℝ (fderiv ℝ (run.model k i)) z)
    (hM : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ‖fderiv ℝ (fderiv ℝ (run.model k i)) z‖ ≤ κm - 1)
    (hgrad : ∀ k i, fderiv ℝ (run.model k i) (run.x k) = fderiv ℝ (elements i) (run.x k))
    (k : ℕ) (i : ι) (hsmall : K * run.Δ k i ≤ 1) :
    K * minimumRadius (run.Δ k) ≤ 1 ∧
    |run.model k i (run.x k) - run.model k i (run.x k + run.s k)| ≤
      K * (κfg + κm / 2) * run.Δ k i := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hκm₀ : 0 ≤ κm := zero_le_one.trans hκm
  refine ⟨?_, ?_⟩
  · have hmin : minimumRadius (run.Δ k) ≤ run.Δ k i := Finset.inf'_le _ (Finset.mem_univ i)
    exact (mul_le_mul_of_nonneg_left hmin hK₀).trans hsmall
  let q := (N i)ᗮ.starProjection (run.s k)
  have hq : ‖q‖ ≤ K * run.Δ k i := run.projected_step_le hK₀ hnorm k i
  have hq₁ : ‖q‖ ≤ 1 := hq.trans hsmall
  have hmodel := element_taylor_bound (run.model_invariant k i) (C := κm)
    (fun t ht ↦ hm k i _ (run.segment_mem k ht))
    (fun t ht ↦ hDm k i _ (run.segment_mem k ht))
    (fun t ht ↦ (hM k i _ (run.segment_mem k ht)).trans (by linarith))
  have hD : ‖fderiv ℝ (run.model k i) (run.x k)‖ ≤ κfg := by
    rw [hgrad k i, (run.objective_invariant i).fderiv_invariant.value_at_projection]
    have h := hF i _ ((N i)ᗮ.starProjection_apply_mem (run.x k))
    simpa only [gradient, LinearIsometryEquiv.norm_map] using h
  have hlin : |fderiv ℝ (run.model k i) (run.x k) q| ≤ κfg * ‖q‖ := by
    rw [← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  let r := run.model k i (run.x k + run.s k) -
    (run.model k i (run.x k) + fderiv ℝ (run.model k i) (run.x k) q)
  have hr : |r| ≤ (1 / 2 : ℝ) * κm * ‖q‖ ^ 2 := hmodel
  have hsum : |run.model k i (run.x k) - run.model k i (run.x k + run.s k)| ≤
      |r| + |fderiv ℝ (run.model k i) (run.x k) q| := by
    rw [abs_sub_comm]
    have heq : run.model k i (run.x k + run.s k) - run.model k i (run.x k) =
        r + fderiv ℝ (run.model k i) (run.x k) q := by dsimp [r]; ring
    rw [heq]
    exact abs_add_le _ _
  have hsq : ‖q‖ ^ 2 ≤ ‖q‖ := by nlinarith [mul_nonneg (norm_nonneg q) (sub_nonneg.mpr hq₁)]
  calc
    _ ≤ |r| + |fderiv ℝ (run.model k i) (run.x k) q| := hsum
    _ ≤ (1 / 2 : ℝ) * κm * ‖q‖ ^ 2 + κfg * ‖q‖ := add_le_add hr hlin
    _ ≤ (κfg + κm / 2) * ‖q‖ := by nlinarith [mul_le_mul_of_nonneg_left hsq hκm₀]
    _ ≤ (κfg + κm / 2) * (K * run.Δ k i) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by ring

end Accuracy

end ConnGouldToint.Chapter10
