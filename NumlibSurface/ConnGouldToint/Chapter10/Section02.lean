import NumlibSurface.ConnGouldToint.Chapter06.Section04
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Structured trust regions

Element objectives and models are invariant along their corresponding null subspaces.
Their trust regions constrain only the projected components of the trial step.
-/

open scoped BigOperators Topology
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

section Convergence

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype ι] [Nonempty ι] {P : StructuredTRParams} {elements : ι → E → ℝ}
  {N : ι → Submodule ℝ E} {β : ℕ → ℝ} {κ : ℝ}

/-- The predicted change of each element in the structured run. -/
noncomputable def StructuredTRRun.predictedDrop (run : StructuredTRRun P elements N β κ)
    (k : ℕ) (i : ι) : ℝ :=
  run.model k i (run.x k) - run.model k i (run.x k + run.s k)

/-- The achieved change of each element in the structured run. -/
noncomputable def StructuredTRRun.actualDrop (run : StructuredTRRun P elements N β κ)
    (k : ℕ) (i : ι) : ℝ :=
  elements i (run.x k) - elements i (run.x k + run.s k)

/-- The gradient of the total model at the current iterate. -/
noncomputable def StructuredTRRun.modelGradient (run : StructuredTRRun P elements N β κ)
    (k : ℕ) : E :=
  gradient (fun x ↦ ∑ i, run.model k i x) (run.x k)

/-- The gradient of the total objective at the current iterate. -/
noncomputable def StructuredTRRun.objectiveGradient (run : StructuredTRRun P elements N β κ)
    (k : ℕ) : E :=
  gradient (fun x ↦ ∑ i, elements i x) (run.x k)

/-- The successful iterations of the structured run. -/
def StructuredTRRun.successful (run : StructuredTRRun P elements N β κ) : Set ℕ :=
  {k | structuredSuccessful P.η₁ (run.predictedDrop k) (run.actualDrop k)}

private theorem minimumRadius_le (Δ : ι → ℝ) (i : ι) : minimumRadius Δ ≤ Δ i :=
  Finset.inf'_le _ (Finset.mem_univ i)

private theorem le_minimumRadius {Δ : ι → ℝ} {b : ℝ} (h : ∀ i, b ≤ Δ i) :
    b ≤ minimumRadius Δ :=
  Finset.le_inf' _ _ fun i _ ↦ h i

private theorem exists_eq_minimumRadius (Δ : ι → ℝ) : ∃ i, Δ i = minimumRadius Δ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty Δ
  exact ⟨i, hi.symm⟩

private theorem minimumRadius_pos (Δ : ι → ℝ) (h : ∀ i, 0 < Δ i) :
    0 < minimumRadius Δ := by
  obtain ⟨i, hi⟩ := exists_eq_minimumRadius Δ
  simpa only [← hi] using h i

omit [Nonempty ι] in
private theorem StructuredRadiusUpdate.noncontract_of_scaled_error
    {d a Δ Δ' : ι → ℝ} (hu : StructuredRadiusUpdate P d a Δ Δ') (i : ι)
    (hgood : |a i - d i| ≤ (1 - P.η₃) / Fintype.card ι * ∑ j, d j)
    (hsmall : |a i - d i| ≤ (P.μ₂ - P.μ₁) / Fintype.card ι * ∑ j, d j) :
    Δ i ≤ Δ' i := by
  by_cases hn : i ∈ negligibleElements P.μ₁ d
  · have hN : negligibleFit P.μ₂ d a i := by
      have hd := mem_negligibleElements.mp hn
      have hsum : |a i| ≤ |a i - d i| + |d i| := by
        simpa only [sub_add_cancel] using abs_add_le (a i - d i) (d i)
      unfold negligibleFit
      calc
        _ ≤ |a i - d i| + |d i| := hsum
        _ ≤ (P.μ₂ - P.μ₁) / Fintype.card ι * (∑ j, d j) +
            P.μ₁ / Fintype.card ι * ∑ j, d j := add_le_add hsmall hd
        _ = _ := by rw [← add_mul, ← add_div, sub_add_cancel]
    by_cases hs : structuredSuccessful P.η₁ d a
    · exact hu.negligible_expand i hn hN hs
    · rw [hu.negligible_hold i hn hN hs]
  · have hm := mem_meaningfulElements.mpr hn
    have hM : elementFit P.η₃ d a i := by
      unfold elementFit
      linarith only [(abs_le.mp hgood).1]
    by_cases hs : structuredSuccessful P.η₁ d a
    · exact hu.meaningful_expand i hm hM hs
    · rw [hu.meaningful_hold i hm hM hs]

private theorem StructuredTRRun.predicted_total_ge (run : StructuredTRRun P elements N β κ)
    {B ε : ℝ} {k : ℕ} (hβ : β k ≤ B) (hε : 0 < ε)
    (hg : ε ≤ ‖run.modelGradient k‖) :
    κ * ε * min (ε / B) (minimumRadius (run.Δ k)) ≤ ∑ i, run.predictedDrop k i := by
  have hB : 0 < B := (run.β_pos k).trans_le hβ
  have hmin : 0 < minimumRadius (run.Δ k) := minimumRadius_pos _ (run.delta_pos k)
  have hs := run.sufficient k
  unfold structuredSufficientDecrease at hs
  change κ * ‖run.modelGradient k‖ *
      min (‖run.modelGradient k‖ / β k) (max (minimumRadius (run.Δ k)) (run.p k (run.s k))) ≤
      (∑ i, run.model k i (run.x k)) - (∑ i, run.model k i (run.x k + run.s k)) at hs
  rw [← Finset.sum_sub_distrib] at hs
  refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left hg run.κ_pos.le) ?_
    (le_min (div_nonneg hε.le hB.le) hmin.le) (mul_nonneg run.κ_pos.le (norm_nonneg _))) hs
  exact min_le_min (div_le_div₀ (norm_nonneg _) hg (run.β_pos k) hβ) (le_max_left _ _)

/-- A radius floor for a tail with gradient norm at least `ε`. The two error
terms come from the meaningful and negligible element tests. This replaces
the sufficient threshold printed in (10.2.24). -/
noncomputable def structuredRadiusFloor (P : StructuredTRParams) (p : ℕ)
    (κ ε B C initial : ℝ) : ℝ :=
  let e := P.γ₁ * (κ * ε)
  min initial (P.γ₁ * min (ε / B)
    (min (((1 - P.η₃) / p) * e / C) (((P.μ₂ - P.μ₁) / p) * e / C)))

/-- The quantitative radius floor remains valid for every tail on which the
gradient norm has a positive lower bound. -/
theorem structuredRadiusFloor_pos_and_le (run : StructuredTRRun P elements N β κ)
    {B C ε : ℝ} (hβ : ∀ k, β k ≤ B) (hC : 0 < C) (hε : 0 < ε) (n : ℕ)
    (hg : ∀ k ≥ n, ε ≤ ‖run.modelGradient k‖)
    (herr : ∀ k i, |run.actualDrop k i - run.predictedDrop k i| ≤ C * (run.Δ k i) ^ 2) :
    0 < structuredRadiusFloor P (Fintype.card ι) κ ε B C (minimumRadius (run.Δ n)) ∧
      ∀ k ≥ n, structuredRadiusFloor P (Fintype.card ι) κ ε B C (minimumRadius (run.Δ n)) ≤
        minimumRadius (run.Δ k) := by
  have hB : 0 < B := (run.β_pos 0).trans_le (hβ 0)
  have hp : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  let e := P.γ₁ * (κ * ε)
  have he : 0 < e := mul_pos P.gamma₁_pos (mul_pos run.κ_pos hε)
  let a := (1 - P.η₃) / (Fintype.card ι : ℝ)
  let b := (P.μ₂ - P.μ₁) / (Fintype.card ι : ℝ)
  have ha : 0 < a := div_pos (sub_pos.mpr P.eta₃_lt_one) hp
  have hb : 0 < b := div_pos (sub_pos.mpr P.mu₁_lt_mu₂) hp
  let θ := min (ε / B) (min (a * e / C) (b * e / C))
  have hθ : 0 < θ := lt_min (div_pos hε hB)
    (lt_min (div_pos (mul_pos ha he) hC) (div_pos (mul_pos hb he) hC))
  let δ := min (minimumRadius (run.Δ n)) (P.γ₁ * θ)
  have hδ : 0 < δ := lt_min (minimumRadius_pos _ (run.delta_pos n))
    (mul_pos P.gamma₁_pos hθ)
  change 0 < δ ∧ ∀ k ≥ n, δ ≤ minimumRadius (run.Δ k)
  refine ⟨hδ, fun k hk ↦ ?_⟩
  induction k, hk using Nat.le_induction with
  | base => exact min_le_left _ _
  | succ k hk ih =>
    apply le_minimumRadius
    intro i
    by_contra! hnext
    have hr := lemma_10_2_1_ii (run.radius_update k) (fun j ↦ (run.delta_pos k j).le) i
    have hiθ : run.Δ k i ≤ θ := by
      have h := hr.trans (hnext.le.trans (min_le_right _ _))
      exact le_of_mul_le_mul_left h P.gamma₁_pos
    have hminθ := (minimumRadius_le (run.Δ k) i).trans hiθ
    have hm := run.predicted_total_ge (hβ k) hε (hg k hk)
    rw [min_eq_right (hminθ.trans (min_le_left _ _))] at hm
    have hnextmin : run.Δ (k + 1) i ≤ minimumRadius (run.Δ k) := hnext.le.trans ih
    have hpred : e * run.Δ k i ≤ ∑ j, run.predictedDrop k j := by
      calc
        e * run.Δ k i = (κ * ε) * (P.γ₁ * run.Δ k i) := by dsimp [e]; ring
        _ ≤ (κ * ε) * minimumRadius (run.Δ k) :=
          mul_le_mul_of_nonneg_left (hr.trans hnextmin) (mul_nonneg run.κ_pos.le hε.le)
        _ ≤ _ := hm
    have hscale {c : ℝ} (hc : 0 ≤ c) (hic : run.Δ k i ≤ c * e / C) :
        |run.actualDrop k i - run.predictedDrop k i| ≤ c * ∑ j, run.predictedDrop k j := by
      have hmul : C * run.Δ k i ≤ c * e := by
        simpa only [mul_comm C] using (le_div_iff₀ hC).mp hic
      calc
        _ ≤ C * (run.Δ k i) ^ 2 := herr k i
        _ = (C * run.Δ k i) * run.Δ k i := by ring
        _ ≤ (c * e) * run.Δ k i :=
          mul_le_mul_of_nonneg_right hmul (run.delta_pos k i).le
        _ = c * (e * run.Δ k i) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpred hc
    have haup : run.Δ k i ≤ a * e / C :=
      (hiθ.trans (min_le_right _ _)).trans (min_le_left _ _)
    have hbup : run.Δ k i ≤ b * e / C :=
      (hiθ.trans (min_le_right _ _)).trans (min_le_right _ _)
    have hu : StructuredRadiusUpdate P (run.predictedDrop k) (run.actualDrop k)
        (run.Δ k) (run.Δ (k + 1)) := run.radius_update k
    have hkeep := hu.noncontract_of_scaled_error i (hscale ha.le haup) (hscale hb.le hbup)
    exact hnext.not_ge ((ih.trans (minimumRadius_le (run.Δ k) i)).trans hkeep)

/-- Theorem 10.2.5 in terms of the quantitative model accuracy and aggregate
curvature bounds. A uniformly positive model gradient prevents any element
radius from approaching zero. The proof compares absolute model error
directly with the two fit tolerances and uses no bound on element gradients. -/
theorem theorem_10_2_5_of_error_bound (run : StructuredTRRun P elements N β κ)
    {B C ε : ℝ} (hβ : ∀ k, β k ≤ B) (hC : 0 < C) (hε : 0 < ε)
    (hg : ∀ k, ε ≤ ‖run.modelGradient k‖)
    (herr : ∀ k i, |run.actualDrop k i - run.predictedDrop k i| ≤ C * (run.Δ k i) ^ 2) :
    ∃ δ > 0, ∀ k, δ ≤ minimumRadius (run.Δ k) := by
  obtain ⟨hδ, hr⟩ := structuredRadiusFloor_pos_and_le run hβ hC hε 0 (fun k _ ↦ hg k) herr
  exact ⟨_, hδ, fun k ↦ hr k (Nat.zero_le k)⟩

omit [Nonempty ι] in
private theorem StructuredRadiusUpdate.le_of_unsuccessful
    {d a Δ Δ' : ι → ℝ} (hu : StructuredRadiusUpdate P d a Δ Δ') (i : ι)
    (hΔ : 0 ≤ Δ i) (hs : ¬ structuredSuccessful P.η₁ d a) :
    Δ' i ≤ Δ i := by
  have hγ : P.γ₂ * Δ i ≤ Δ i := mul_le_of_le_one_left hΔ P.gamma₂_lt_one.le
  by_cases hn : i ∈ negligibleElements P.μ₁ d
  · by_cases hfit : negligibleFit P.μ₂ d a i
    · rw [hu.negligible_hold i hn hfit hs]
    · exact (hu.negligible_contract i hn hfit).2.trans hγ
  · have hm := mem_meaningfulElements.mpr hn
    by_cases hfit : elementFit P.η₃ d a i
    · rw [hu.meaningful_hold i hm hfit hs]
    · by_cases hfit₂ : elementFit P.η₂ d a i
      · exact (hu.meaningful_moderate i hm hfit hfit₂).2
      · exact (hu.meaningful_contract i hm hfit₂).2.trans hγ

private theorem StructuredRadiusUpdate.exists_contraction_of_unsuccessful
    {d a Δ Δ' : ι → ℝ} (hu : StructuredRadiusUpdate P d a Δ Δ')
    (hd : 0 < ∑ i, d i) (hs : ¬ structuredSuccessful P.η₁ d a) :
    ∃ i, Δ' i ≤ P.γ₂ * Δ i := by
  by_contra! hn
  apply hs
  exact (lemma_10_2_2 P hd
    (fun i hi ↦ by
      by_contra h
      exact (hn i).not_ge (hu.meaningful_contract i hi h).2)
    (fun i hi ↦ by
      by_contra h
      exact (hn i).not_ge (hu.negligible_contract i hi h).2)).2.2

/-- Theorem 10.2.6 in terms of the quadratic error and aggregate curvature
bounds. After the last accepted step the iterate is constant. On every
unsuccessful iteration at least one element radius contracts and none grows.
A nonzero gradient would force a uniform radius floor, contradicting the
resulting uniform decrease in the sum of the radii. -/
theorem theorem_10_2_6_of_error_bound (run : StructuredTRRun P elements N β κ)
    {B C : ℝ} (hβ : ∀ k, β k ≤ B) (hC : 0 < C)
    (herr : ∀ k i, |run.actualDrop k i - run.predictedDrop k i| ≤ C * (run.Δ k i) ^ 2)
    (hgrad : ∀ k, run.modelGradient k = run.objectiveGradient k)
    (hfinite : run.successful.Finite) :
    ∃ x, (∀ᶠ k in Filter.atTop, run.x k = x) ∧ gradient (fun z ↦ ∑ i, elements i z) x = 0 := by
  obtain ⟨J, hJ⟩ := hfinite.bddAbove
  let n := J + 1
  have hfail (k : ℕ) (hk : n ≤ k) : k ∉ run.successful := by
    intro h
    have hle := hJ h
    change J + 1 ≤ k at hk
    omega
  have hx (k : ℕ) (hk : n ≤ k) : run.x k = run.x n := by
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      have hs : ¬ structuredSuccessful P.η₁
          (fun i ↦ run.model k i (run.x k) - run.model k i (run.x k + run.s k))
          (fun i ↦ elements i (run.x k) - elements i (run.x k + run.s k)) := hfail k hk
      rw [run.iterate_update, ite_eq_right hs, ih]
  refine ⟨run.x n, Filter.eventually_atTop.mpr ⟨n, hx⟩, ?_⟩
  change run.objectiveGradient n = 0
  by_contra hn
  let ε := ‖run.objectiveGradient n‖
  have hε : 0 < ε := norm_pos_iff.mpr hn
  have hg (k : ℕ) (hk : n ≤ k) : ε ≤ ‖run.modelGradient k‖ := by
    rw [hgrad k]
    unfold StructuredTRRun.objectiveGradient
    rw [hx k hk]
    exact le_rfl
  let δ := structuredRadiusFloor P (Fintype.card ι) κ ε B C (minimumRadius (run.Δ n))
  obtain ⟨hδ, hfloor⟩ := structuredRadiusFloor_pos_and_le run hβ hC hε n hg herr
  let c := (1 - P.γ₂) * δ
  have hc : 0 < c := mul_pos (sub_pos.mpr P.gamma₂_lt_one) hδ
  let total (k : ℕ) := ∑ i, run.Δ k i
  have htotal (k : ℕ) : 0 ≤ total k := Finset.sum_nonneg (fun i _ ↦ (run.delta_pos k i).le)
  have hdrop (k : ℕ) (hk : n ≤ k) : c ≤ total k - total (k + 1) := by
    have hu : StructuredRadiusUpdate P (run.predictedDrop k) (run.actualDrop k)
        (run.Δ k) (run.Δ (k + 1)) := run.radius_update k
    have hfailed : ¬ structuredSuccessful P.η₁ (run.predictedDrop k) (run.actualDrop k) :=
      hfail k hk
    obtain ⟨i, hi⟩ := hu.exists_contraction_of_unsuccessful (run.predicted_pos k) hfailed
    have hδi := (hfloor k hk).trans (minimumRadius_le (run.Δ k) i)
    have hstep : c ≤ run.Δ k i - run.Δ (k + 1) i := calc
      _ ≤ (1 - P.γ₂) * run.Δ k i :=
        mul_le_mul_of_nonneg_left hδi (sub_nonneg.mpr P.gamma₂_lt_one.le)
      _ = run.Δ k i - P.γ₂ * run.Δ k i := by ring
      _ ≤ _ := sub_le_sub_left hi _
    have hsum : run.Δ k i - run.Δ (k + 1) i ≤ ∑ j, (run.Δ k j - run.Δ (k + 1) j) :=
      Finset.single_le_sum
        (fun j _ ↦ sub_nonneg.mpr (hu.le_of_unsuccessful j (run.delta_pos k j).le hfailed))
        (Finset.mem_univ i)
    rw [Finset.sum_sub_distrib] at hsum
    exact hstep.trans hsum
  have hdec (j : ℕ) : total (n + j) + (j : ℝ) * c ≤ total n := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h := hdrop (n + j) (Nat.le_add_right _ _)
      push_cast
      rw [← Nat.add_assoc]
      linarith only [h, ih]
  obtain ⟨j, hj⟩ := exists_nat_gt (total n / c)
  exact (not_lt_of_ge (by linarith [hdec j, htotal (n + j)] : (j : ℝ) * c ≤ total n))
    ((div_lt_iff₀ hc).mp hj)

variable [∀ i, (N i).HasOrthogonalProjection]

/-- The curvature quantity (6.3.1) for the aggregate model on the structured
trust region, using the supremum of the Hessian norms. -/
noncomputable def StructuredTRRun.aggregateCurvature (run : StructuredTRRun P elements N β κ)
    (k : ℕ) : ℝ :=
  1 + sSup ((fun z ↦ ‖fderiv ℝ (fderiv ℝ (fun x ↦ ∑ i, run.model k i x)) z‖) ''
    structuredTrustRegion (run.p k) N (run.x k) (run.Δ k))

/-- An elementwise Hessian bound gives a uniform bound on the aggregate
curvature. The factor counting elements allows their Hessians to overlap. -/
theorem StructuredTRRun.aggregateCurvature_le (run : StructuredTRRun P elements N β κ)
    {κm : ℝ}
    (hmodel : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ContDiffAt ℝ 2 (run.model k i) z)
    (hM : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ‖fderiv ℝ (fderiv ℝ (run.model k i)) z‖ ≤ κm - 1)
    (k : ℕ) : run.aggregateCurvature k ≤ 1 + Fintype.card ι * (κm - 1) := by
  have hx : run.x k ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) := by
    simpa only [zero_smul, add_zero] using run.segment_mem k (show (0 : ℝ) ∈ Icc 0 1 by simp)
  unfold StructuredTRRun.aggregateCurvature
  apply add_le_add le_rfl
  apply csSup_le (Set.Nonempty.image _ ⟨run.x k, hx⟩)
  rintro _ ⟨z, hz, rfl⟩
  dsimp only
  have hloc : ∀ᶠ y in 𝓝 z, ∀ i, DifferentiableAt ℝ (run.model k i) y :=
    Filter.eventually_all.mpr fun i ↦ ((hmodel k i z hz).eventually (by norm_num)).mono
      (fun _ h ↦ h.differentiableAt (by norm_num))
  have hsum :
      fderiv ℝ (fun x ↦ ∑ i, run.model k i x) =ᶠ[𝓝 z]
        (fun y ↦ ∑ i, fderiv ℝ (run.model k i) y) :=
    hloc.mono fun _ hy ↦ fderiv_fun_sum (fun i _ ↦ hy i)
  have hsecond :
      fderiv ℝ (fun y ↦ ∑ i, fderiv ℝ (run.model k i) y) z =
        ∑ i, fderiv ℝ (fderiv ℝ (run.model k i)) z :=
    fderiv_fun_sum (fun i _ ↦
      ((hmodel k i z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  rw [hsum.fderiv_eq (𝕜 := ℝ), hsecond]
  let H : ι → E →L[ℝ] E →L[ℝ] ℝ := fun i ↦ fderiv ℝ (fderiv ℝ (run.model k i)) z
  have hnorm : ‖∑ i, H i‖ ≤ ∑ i, ‖H i‖ := norm_sum_le Finset.univ H
  have hsumBound : (∑ i, ‖H i‖) ≤ ∑ _i : ι, (κm - 1) :=
    Finset.sum_le_sum (fun i _ ↦ hM k i z hz)
  have hconst : (∑ _i : ι, (κm - 1)) = Fintype.card ι * (κm - 1) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change ‖∑ i, H i‖ ≤ Fintype.card ι * (κm - 1)
  exact hnorm.trans (hsumBound.trans_eq hconst)

private theorem StructuredTRRun.gradients_agree (run : StructuredTRRun P elements N β κ)
    (hf : ∀ i, ContDiff ℝ 2 (elements i))
    (hmodel : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ContDiffAt ℝ 2 (run.model k i) z)
    (hgrad : ∀ k i, fderiv ℝ (run.model k i) (run.x k) = fderiv ℝ (elements i) (run.x k))
    (k : ℕ) : run.modelGradient k = run.objectiveGradient k := by
  have hx : run.x k ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) := by
    simpa only [zero_smul, add_zero] using run.segment_mem k (show (0 : ℝ) ∈ Icc 0 1 by simp)
  unfold StructuredTRRun.modelGradient StructuredTRRun.objectiveGradient gradient
  rw [fderiv_fun_sum (fun i _ ↦ (hmodel k i _ hx).differentiableAt (by norm_num)),
    fderiv_fun_sum (fun i _ ↦ (hf i).differentiable (by norm_num) _)]
  simp only [hgrad]

private theorem StructuredTRRun.drop_error (run : StructuredTRRun P elements N β κ)
    {K κf κm : ℝ} (hK : 1 ≤ K) (hκf : 1 ≤ κf) (hκm : 1 ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hf : ∀ i, ContDiff ℝ 2 (elements i))
    (hF : ∀ i z, z ∈ (N i)ᗮ → ‖fderiv ℝ (fderiv ℝ (elements i)) z‖ ≤ κf)
    (hmodel : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ContDiffAt ℝ 2 (run.model k i) z)
    (hM : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ‖fderiv ℝ (fderiv ℝ (run.model k i)) z‖ ≤ κm - 1)
    (hval : ∀ k i, run.model k i (run.x k) = elements i (run.x k))
    (hgrad : ∀ k i, fderiv ℝ (run.model k i) (run.x k) = fderiv ℝ (elements i) (run.x k))
    (k : ℕ) (i : ι) :
    |run.actualDrop k i - run.predictedDrop k i| ≤ uniformHessianConstant K κf κm * (run.Δ k i) ^ 2 := by
  have heq : run.actualDrop k i - run.predictedDrop k i =
      -(elements i (run.x k + run.s k) - run.model k i (run.x k + run.s k)) := by
    unfold StructuredTRRun.actualDrop StructuredTRRun.predictedDrop
    rw [hval k i]
    ring
  rw [heq, abs_neg]
  exact (theorem_10_2_3 run hK hκf hκm hnorm hf hF
    (fun j l z hz ↦ (hmodel j l z hz).differentiableAt (by norm_num))
    (fun j l z hz ↦ ((hmodel j l z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)) hM hval hgrad k i).2

private theorem uniformHessianConstant_pos {K κf κm : ℝ} (hK : 1 ≤ K) (hκf : 1 ≤ κf) :
    0 < uniformHessianConstant K κf κm :=
  mul_pos (pow_pos (zero_lt_one.trans_le hK) 2) ((zero_lt_one.trans_le hκf).trans_le (le_max_left _ _))

/-- Theorem 10.2.5. With the usual aggregate curvature choice and quadratic
element accuracy from the smoothness assumptions, a uniform positive gradient
floor forces a uniform positive floor on the minimum radius. -/
theorem theorem_10_2_5 (run : StructuredTRRun P elements N β κ)
    {K κf κm ε : ℝ} (hK : 1 ≤ K) (hκf : 1 ≤ κf) (hκm : 1 ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hf : ∀ i, ContDiff ℝ 2 (elements i))
    (hF : ∀ i z, z ∈ (N i)ᗮ → ‖fderiv ℝ (fderiv ℝ (elements i)) z‖ ≤ κf)
    (hmodel : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ContDiffAt ℝ 2 (run.model k i) z)
    (hM : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ‖fderiv ℝ (fderiv ℝ (run.model k i)) z‖ ≤ κm - 1)
    (hval : ∀ k i, run.model k i (run.x k) = elements i (run.x k))
    (hgrad : ∀ k i, fderiv ℝ (run.model k i) (run.x k) = fderiv ℝ (elements i) (run.x k))
    (hβ : ∀ k, β k = run.aggregateCurvature k)
    (hε : 0 < ε) (hg : ∀ k, ε ≤ ‖run.modelGradient k‖) :
    ∃ δ > 0, ∀ k, δ ≤ minimumRadius (run.Δ k) :=
  theorem_10_2_5_of_error_bound run
    (fun k ↦ (hβ k).le.trans (run.aggregateCurvature_le hmodel hM k))
    (uniformHessianConstant_pos hK hκf) hε hg
    (run.drop_error hK hκf hκm hnorm hf hF hmodel hM hval hgrad)

/-- Theorem 10.2.6. A structured run with only finitely many successful
iterations is eventually constant at a first-order critical point. The
quantitative proof uses the lower norm comparison of AN.1 and does not
require the separate element gradient bound AF.5s. -/
theorem theorem_10_2_6 (run : StructuredTRRun P elements N β κ)
    {K κf κm : ℝ} (hK : 1 ≤ K) (hκf : 1 ≤ κf) (hκm : 1 ≤ κm)
    (hnorm : ∀ k v, ‖v‖ ≤ K * run.p k v)
    (hf : ∀ i, ContDiff ℝ 2 (elements i))
    (hF : ∀ i z, z ∈ (N i)ᗮ → ‖fderiv ℝ (fderiv ℝ (elements i)) z‖ ≤ κf)
    (hmodel : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ContDiffAt ℝ 2 (run.model k i) z)
    (hM : ∀ k i z, z ∈ structuredTrustRegion (run.p k) N (run.x k) (run.Δ k) →
      ‖fderiv ℝ (fderiv ℝ (run.model k i)) z‖ ≤ κm - 1)
    (hval : ∀ k i, run.model k i (run.x k) = elements i (run.x k))
    (hgrad : ∀ k i, fderiv ℝ (run.model k i) (run.x k) = fderiv ℝ (elements i) (run.x k))
    (hβ : ∀ k, β k = run.aggregateCurvature k) (hfinite : run.successful.Finite) :
    ∃ x, (∀ᶠ k in Filter.atTop, run.x k = x) ∧ gradient (fun z ↦ ∑ i, elements i z) x = 0 :=
  theorem_10_2_6_of_error_bound run
    (fun k ↦ (hβ k).le.trans (run.aggregateCurvature_le hmodel hM k))
    (uniformHessianConstant_pos hK hκf)
    (run.drop_error hK hκf hκm hnorm hf hF hmodel hM hval hgrad)
    (run.gradients_agree hf hmodel hgrad) hfinite

end Convergence

end ConnGouldToint.Chapter10
