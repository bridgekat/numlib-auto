import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Basic.Real.Pointwise
import Numlib.Optimization.Descent
import Numlib.Optimization.Optimality.Approximate

/-!
# Criticality measures over admissible displacements

The constrained criticality measures of [cartis2022evaluation], (6.1.5), (6.1.7), (6.1.9),
(6.2.3)–(6.2.5) and (7.1.2) all have the shape
`ω = -min_{d ∈ T ∩ 𝓑} A[d]^j = sup_{d ∈ T ∩ 𝓑} (-A[d]^j)`, with `A` a `j`-linear form (a
derivative tensor of the objective or of a model), `𝓑` the closed unit ball and `T` a set of
admissible displacements: the feasible steps `𝒞(x) = {d | x + d ∈ C}` (6.1.2) or a restricted
subset `{d ∈ T | |B[d]^i| ≤ a}` ((6.1.8), (6.1.10), (6.2.1), (6.2.2)).

## Main definitions

* `Optimization.feasibleSteps C x`: the feasible displacements `𝒞(x)` of (1.1.7), (6.1.2).
* `Optimization.formCriticality A T`: the measure `sup_{d ∈ T, ‖d‖ ≤ 1} (-A[d]^j)`.
* `Optimization.restrictedSteps B a T`: the restricted set `{d ∈ T | |B[d]^i| ≤ a}`.

## Main results

* `formCriticality_nonneg`, `formCriticality_le_iff`: nonnegativity and the form in which
  termination tests are used;
* `formCriticality_mono`, `formCriticality_le_add_of_abs_sub_le`,
  `abs_formCriticality_sub_le_norm`, `formCriticality_smul`: the structural facts used in the
  analysis of Chapters 6 and 7;
* `inter_closedBall_restrictedSteps_subset`: transfer of restricted sets (proof of Theorem 6.2.3);
* `formCriticality_one_univ`: without constraints the first-order measure is `‖∇f(x)‖`;
* `formCriticality_eq_zero_iff`: the first-order measure on a convex set vanishes exactly at
  first-order critical points (1.1.6);
* `exists_formCriticality_eq`: in finite dimension the supremum is attained.

## Implementation notes

The measures (6.1.5) and (6.1.9) are `-min …`, nonnegative (compare (6.2.3) and (7.1.2)). The
measure is the `decrementMeasure` (an `sSup`) of the decrease `d ↦ -A[d]^j` with radius `1`,
finite since the image is bounded by `‖A‖`; it is a `max` in finite
dimension when `T` is closed.
-/

open Set Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Optimization

/-! ### Feasible displacements -/

section FeasibleSteps

/-- The feasible displacements `𝒞(x) = {d | x + d ∈ C}` of [cartis2022evaluation], (1.1.7),
(6.1.2). The model's set `𝓜⁰_k(s)` of (6.2.1) is `feasibleSteps C (x_k + s)`. -/
def feasibleSteps (C : Set E) (x : E) : Set E := {d | x + d ∈ C}

variable {C : Set E} {x d : E}

omit [NormedSpace ℝ E] in
@[simp]
theorem mem_feasibleSteps : d ∈ feasibleSteps C x ↔ x + d ∈ C := Iff.rfl

omit [NormedSpace ℝ E] in
theorem feasibleSteps_eq_preimage (C : Set E) (x : E) :
    feasibleSteps C x = (fun d => x + d) ⁻¹' C := rfl

omit [NormedSpace ℝ E] in
@[simp]
theorem zero_mem_feasibleSteps : 0 ∈ feasibleSteps C x ↔ x ∈ C := by
  simp

theorem convex_feasibleSteps (hC : Convex ℝ C) (x : E) : Convex ℝ (feasibleSteps C x) :=
  hC.translate_preimage_right x

omit [NormedSpace ℝ E] in
theorem isClosed_feasibleSteps (hC : IsClosed C) (x : E) : IsClosed (feasibleSteps C x) :=
  hC.preimage (continuous_const.add continuous_id)

/-- Feasible displacements of a convex set may be shortened. -/
theorem smul_mem_feasibleSteps (hC : Convex ℝ C) (hx : x ∈ C) (hd : d ∈ feasibleSteps C x)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t • d ∈ feasibleSteps C x := by
  exact (convex_feasibleSteps hC x).smul_mem_of_zero_mem (zero_mem_feasibleSteps.2 hx) hd
    ⟨ht0, ht1⟩

end FeasibleSteps

/-! ### The criticality measure of a multilinear form -/

section FormCriticality

variable {j : ℕ}

/-- The criticality measure of a `j`-linear form `A` over the admissible displacements `T`
([cartis2022evaluation], (6.1.5), (6.1.7), (6.1.9), (6.2.3)–(6.2.5), (7.1.2)):
`formCriticality A T = sup_{d ∈ T, ‖d‖ ≤ 1} (-A[d]^j)`, the book's `-min_{d ∈ T ∩ 𝓑} A[d]^j`: the
`decrementMeasure` of radius `1` of the decrease `d ↦ -A[d]^j`. -/
noncomputable def formCriticality (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ)
    (T : Set E) : ℝ :=
  decrementMeasure (fun d => -A fun _ => d) 1 T

variable (A B : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ) {T T' : Set E}

/-- On the unit ball, `|A[d]^j| ≤ ‖A‖`. -/
theorem abs_apply_le_norm_of_mem_closedBall {d : E} (hd : d ∈ closedBall (0 : E) 1) :
    |A fun _ => d| ≤ ‖A‖ := by
  have hd' : ‖d‖ ≤ 1 := by simpa using hd
  calc |A fun _ => d| = ‖A fun _ => d‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖A‖ * ∏ _i : Fin j, ‖d‖ := A.le_opNorm _
    _ ≤ ‖A‖ * 1 := by
        gcongr
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) hd'
    _ = ‖A‖ := mul_one _

theorem bddAbove_formCriticality (T : Set E) :
    BddAbove ((fun d => -A fun _ => d) '' (closedBall 0 1 ∩ T)) := by
  refine ⟨‖A‖, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  exact (neg_le_abs _).trans (abs_apply_le_norm_of_mem_closedBall A hd.1)

/-- Every admissible displacement in the unit ball gives a lower bound. -/
theorem le_formCriticality {d : E} (hd : d ∈ closedBall 0 1 ∩ T) :
    (-A fun _ => d) ≤ formCriticality A T :=
  le_decrementMeasure (bddAbove_formCriticality A T) hd

theorem formCriticality_le {ε : ℝ} (hT : (closedBall 0 1 ∩ T).Nonempty)
    (h : ∀ d ∈ closedBall 0 1 ∩ T, (-A fun _ => d) ≤ ε) : formCriticality A T ≤ ε :=
  decrementMeasure_le hT h

omit [NormedSpace ℝ E] in
theorem zero_mem_closedBall_inter (hT : 0 ∈ T) : (0 : E) ∈ closedBall 0 1 ∩ T :=
  ⟨mem_closedBall_self zero_le_one, hT⟩

/-- The measure is nonnegative when `d = 0` is admissible ([cartis2022evaluation], (6.1.5)). -/
theorem formCriticality_nonneg (hj : 1 ≤ j) (hT : 0 ∈ T) : 0 ≤ formCriticality A T := by
  have h := le_formCriticality A (zero_mem_closedBall_inter hT)
  have : (A fun _ => (0 : E)) = 0 := A.map_coord_zero ⟨0, hj⟩ rfl
  simpa [this] using h

/-- The form of the termination tests (6.2.8), (6.2.9), (7.1.4): `ω ≤ ε` iff `A[d]^j ≥ -ε` for all
admissible `d` in the unit ball. -/
theorem formCriticality_le_iff (hT : 0 ∈ T) {ε : ℝ} :
    formCriticality A T ≤ ε ↔ ∀ d ∈ closedBall 0 1 ∩ T, -ε ≤ A fun _ => d := by
  constructor
  · intro h d hd
    linarith [le_formCriticality A hd]
  · intro h
    exact formCriticality_le A ⟨0, zero_mem_closedBall_inter hT⟩ fun d hd => by
      linarith [h d hd]

/-- Monotonicity in the admissible set (only its unit-ball part matters). -/
theorem formCriticality_mono (hT : (closedBall 0 1 ∩ T).Nonempty)
    (hTT' : closedBall 0 1 ∩ T ⊆ T') : formCriticality A T ≤ formCriticality A T' :=
  formCriticality_le A hT fun _ hd => le_formCriticality A ⟨hd.1, hTT' hd⟩

/-- Perturbation of the form: if `|A[d]^j - B[d]^j| ≤ e` on the admissible unit-ball
displacements, the measures differ by at most `e` (step "(6.2.23) ⇒ …" of the proof of
Lemma 6.2.1 in [cartis2022evaluation]). -/
theorem abs_formCriticality_sub_le (hT : (closedBall 0 1 ∩ T).Nonempty) {e : ℝ}
    (h : ∀ d ∈ closedBall 0 1 ∩ T, |(A fun _ => d) - B fun _ => d| ≤ e) :
    |formCriticality A T - formCriticality B T| ≤ e :=
  abs_decrementMeasure_sub_le hT (bddAbove_formCriticality A T) (bddAbove_formCriticality B T)
    fun d hd => by rw [neg_sub_neg, abs_sub_comm]; exact h d hd

/-- One-sided form of `abs_formCriticality_sub_le`. -/
theorem formCriticality_le_add_of_abs_sub_le (hT : (closedBall 0 1 ∩ T).Nonempty) {e : ℝ}
    (h : ∀ d ∈ closedBall 0 1 ∩ T, |(A fun _ => d) - B fun _ => d| ≤ e) :
    formCriticality A T ≤ formCriticality B T + e := by
  linarith [(abs_le.1 (abs_formCriticality_sub_le A B hT h)).2]

/-- The measure is `1`-Lipschitz in the form for the operator norm. -/
theorem abs_formCriticality_sub_le_norm (hT : (closedBall 0 1 ∩ T).Nonempty) :
    |formCriticality A T - formCriticality B T| ≤ ‖A - B‖ :=
  abs_formCriticality_sub_le A B hT fun d hd => by
    simpa using abs_apply_le_norm_of_mem_closedBall (A - B) hd.1

/-- Positive homogeneity in the form (used in Lemma 7.2.1 of [cartis2022evaluation]). -/
theorem formCriticality_smul {c : ℝ} (hc : 0 ≤ c) (T : Set E) :
    formCriticality (c • A) T = c * formCriticality A T := by
  rw [formCriticality, formCriticality, decrementMeasure_def, decrementMeasure_def, ← smul_eq_mul,
    ← Real.sSup_smul_of_nonneg hc,
    ← Set.image_smul, Set.image_image]
  congr 1
  refine Set.image_congr fun _ _ => ?_
  simp

/-- Without constraints, the first-order measure is the norm of the linear form: with
`A = ∇f(x)` this is `‖∇f(x)‖` (remark after (6.1.10) of [cartis2022evaluation]). -/
theorem formCriticality_one_univ (A : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) :
    formCriticality A univ = ‖A‖ := by
  set ℓ : E →L[ℝ] ℝ := continuousMultilinearCurryFin1 ℝ E ℝ A
  have hℓ : ∀ s, ℓ s = A fun _ => s := fun s => by
    simp only [ℓ, continuousMultilinearCurryFin1_apply]
    congr 1
  rw [formCriticality, decrementMeasure_def, inter_univ]
  have : (fun d => -A fun _ => d) = fun s => -ℓ s := funext fun s => by rw [hℓ]
  rw [this, sSup_neg_apply_closedBall ℓ zero_le_one, one_mul]
  exact (continuousMultilinearCurryFin1 ℝ E ℝ).norm_map A

/-- The unconstrained first-order measure of `f` at `x` is `‖∇f(x)‖`. -/
theorem formCriticality_iteratedFDeriv_one_univ (f : E → ℝ) (x : E) :
    formCriticality (iteratedFDeriv ℝ 1 f x) univ = ‖fderiv ℝ f x‖ := by
  rw [formCriticality_one_univ, norm_iteratedFDeriv_one]

/-- The unconstrained first-order measure is the book's `‖∇f(x)‖ ≤ ε` test (2.1.2). -/
theorem formCriticality_iteratedFDeriv_one_univ_le_iff (f : E → ℝ) (x : E) {ε : ℝ} :
    formCriticality (iteratedFDeriv ℝ 1 f x) univ ≤ ε ↔ IsApproxFirstOrder f x ε := by
  rw [formCriticality_iteratedFDeriv_one_univ, isApproxFirstOrder_iff]

/-- Bridge to the Taylor-decrement measure: the first-order measure over `T` is the first-order
Taylor measure of radius `1` over `T` ([cartis2022evaluation], (12.1.12), (14.2.2)). -/
theorem formCriticality_eq_taylorMeasure_one (D : FormalMultilinearSeries ℝ E ℝ) (T : Set E) :
    formCriticality (D 1) T = taylorMeasure D 1 1 T := by
  rw [formCriticality, taylorMeasure]
  congr 1
  funext d
  rw [FormalMultilinearSeries.taylorDecrement_one_apply]

/-- The first-order measure on a convex set vanishes exactly at the points satisfying the
first-order condition `∇f(x)[y - x] ≥ 0` for all `y ∈ C` ([cartis2022evaluation], (1.1.6)).
This holds for any linear form `A` in place of `∇f(x)`. -/
theorem formCriticality_eq_zero_iff {C : Set E} (hC : Convex ℝ C) {x : E} (hx : x ∈ C)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) :
    formCriticality A (feasibleSteps C x) = 0 ↔ ∀ y ∈ C, 0 ≤ A fun _ => y - x := by
  have h0 : (0 : E) ∈ feasibleSteps C x := zero_mem_feasibleSteps.2 hx
  have hlin : ∀ (c : ℝ) (v : E), (A fun _ => c • v) = c * A fun _ => v := fun c v => by
    rw [A.apply_smul_diag, pow_one, smul_eq_mul]
  rw [le_antisymm_iff, and_iff_left (formCriticality_nonneg A le_rfl h0),
    formCriticality_le_iff A h0]
  simp only [neg_zero]
  constructor
  · intro h y hy
    have hd : y - x ∈ feasibleSteps C x := by simpa using hy
    rcases le_or_gt ‖y - x‖ 1 with hle | hgt
    · exact h _ ⟨by simpa using hle, hd⟩
    · have hpos : 0 < ‖y - x‖ := by linarith
      have hmem : ‖y - x‖⁻¹ • (y - x) ∈ closedBall (0 : E) 1 ∩ feasibleSteps C x :=
        ⟨by simp [norm_smul, hpos.ne'],
          smul_mem_feasibleSteps hC hx hd (inv_nonneg.2 hpos.le) (inv_le_one_of_one_le₀ hgt.le)⟩
      have := h _ hmem
      rw [hlin] at this
      exact nonneg_of_mul_nonneg_right (by linarith) (inv_pos.2 hpos)
  · intro h d hd
    simpa using h (x + d) hd.2

/-- The first-order measure of `f` on a convex set `C ∋ x` vanishes exactly when
`∇f(x)[y - x] ≥ 0` for all `y ∈ C`, the first-order condition (1.1.6) of [cartis2022evaluation]
(no differentiability is needed). -/
theorem formCriticality_fderiv_eq_zero_iff {f : E → ℝ} {C : Set E} (hC : Convex ℝ C) {x : E}
    (hx : x ∈ C) :
    formCriticality (iteratedFDeriv ℝ 1 f x) (feasibleSteps C x) = 0 ↔
      ∀ y ∈ C, 0 ≤ fderiv ℝ f x (y - x) := by
  simp only [formCriticality_eq_zero_iff hC hx, iteratedFDeriv_one_apply]

/-- A local minimizer on a convex set, at which `f` is differentiable, has zero first-order
measure. -/
theorem formCriticality_eq_zero_of_isLocalMinOn {f : E → ℝ} {C : Set E} (hC : Convex ℝ C)
    {x : E} (hx : x ∈ C) (hmin : IsLocalMinOn f C x) (hf : DifferentiableAt ℝ f x) :
    formCriticality (iteratedFDeriv ℝ 1 f x) (feasibleSteps C x) = 0 := by
  rw [formCriticality_fderiv_eq_zero_iff hC hx]
  intro y hy
  exact Descent.fderiv_apply_sub_nonneg_of_isLocalMinOn (f' := fderiv ℝ f) hC hx hmin
    hf.hasFDerivAt y hy

/-- In finite dimension, for closed `T` meeting the unit ball, the supremum is attained
(justifying the book's `min`). -/
theorem exists_formCriticality_eq [FiniteDimensional ℝ E] (hT : IsClosed T)
    (hne : (closedBall 0 1 ∩ T).Nonempty) :
    ∃ d ∈ closedBall 0 1 ∩ T, (-A fun _ => d) = formCriticality A T := by
  have hK : IsCompact (closedBall (0 : E) 1 ∩ T) := (isCompact_closedBall 0 1).inter_right hT
  have hc : Continuous fun d : E => -A fun _ => d :=
    (A.cont.comp (continuous_pi fun _ => continuous_id)).neg
  obtain ⟨d, hd, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
  rw [formCriticality, decrementMeasure_def]
  refine ⟨d, hd, (IsGreatest.csSup_eq (s := (fun d => -A fun _ => d) '' (closedBall 0 1 ∩ T))
    (a := -A fun _ => d) ⟨⟨d, hd, rfl⟩, ?_⟩).symm⟩
  rintro _ ⟨e, he, rfl⟩
  exact hmax he

end FormCriticality

/-! ### Restricted admissible sets -/

section RestrictedSteps

variable {i j : ℕ}

/-- The restricted set `{d ∈ T | |B[d]^i| ≤ a}` of [cartis2022evaluation]:
`𝒞¹(x, α) = restrictedSteps (∇f(x)) (τ₁ α) 𝒞(x)` (6.1.8),
`𝒞²(x, α₁, α₂) = restrictedSteps (∇²f(x)) (τ₂ α₂) 𝒞¹(x, α₁)` (6.1.10), and their model
counterparts (6.2.1), (6.2.2). -/
def restrictedSteps (B : ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ) (a : ℝ) (T : Set E) :
    Set E :=
  {d ∈ T | |B fun _ => d| ≤ a}

variable {B : ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ} {a b : ℝ} {T T' : Set E}

@[simp]
theorem mem_restrictedSteps {d : E} :
    d ∈ restrictedSteps B a T ↔ d ∈ T ∧ |B fun _ => d| ≤ a := Iff.rfl

theorem restrictedSteps_subset : restrictedSteps B a T ⊆ T := fun _ hd => hd.1

theorem zero_mem_restrictedSteps (hi : 1 ≤ i) (ha : 0 ≤ a) :
    0 ∈ restrictedSteps B a T ↔ 0 ∈ T := by
  have : (B fun _ => (0 : E)) = 0 := B.map_coord_zero ⟨0, hi⟩ rfl
  simp [this, ha]

theorem restrictedSteps_mono (hab : a ≤ b) (hT : T ⊆ T') :
    restrictedSteps B a T ⊆ restrictedSteps B b T' :=
  fun _ hd => ⟨hT hd.1, hd.2.trans hab⟩

/-- Transfer of restricted sets: if `|A[d]^i - B[d]^i| ≤ e` on `T ∩ 𝓑` and `e + a ≤ b`, then
`𝓑 ∩ {d ∈ T | |A[d]^i| ≤ a} ⊆ {d ∈ T | |B[d]^i| ≤ b}`. This is the inclusion
`𝒞¹(x_{k+1}, ε₁) ∩ 𝓑 ⊆ 𝓜¹_k(s_k)` of the proof of Theorem 6.2.3 of [cartis2022evaluation],
where the estimate (6.2.23) holds on the unit ball `𝓑` only. -/
theorem inter_closedBall_restrictedSteps_subset
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ) {e : ℝ}
    (h : ∀ d ∈ closedBall 0 1 ∩ T, |(A fun _ => d) - B fun _ => d| ≤ e) (hab : e + a ≤ b) :
    closedBall 0 1 ∩ restrictedSteps A a T ⊆ restrictedSteps B b T := by
  rintro d ⟨hd, hdT, hA⟩
  refine ⟨hdT, ?_⟩
  have := h d ⟨hd, hdT⟩
  calc |B fun _ => d| ≤ |(A fun _ => d) - B fun _ => d| + |A fun _ => d| := by
        have := abs_sub_abs_le_abs_sub (B fun _ => d) (A fun _ => d)
        rw [abs_sub_comm] at this
        linarith
    _ ≤ e + a := add_le_add this hA
    _ ≤ b := hab

end RestrictedSteps

end Optimization
