import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Numlib.Analysis.Calculus.MeanValue
import Numlib.Optimization.EvaluationComplexity
import Numlib.Optimization.LineSearch

/-!
# Quantitative gradient descent and dyadic Armijo backtracking

The sharp Lipschitz-derivative remainder gives a quadratic upper model and a sufficient Armijo
step. Backtracking selects the first accepted dyadic trial, so its lower bound retains the
initial step: `min initial ((1 - α) / L)`. In particular the bound remains valid when the initial
trial is already very small. The calculus uses real inner product spaces; a gradient is specified
by its usual continuous linear derivative `innerSL ℝ (g x)` without requiring completeness.

The motivating source is Cartis–Gould–Toint, *Evaluation Complexity of Algorithms for Nonconvex
Optimization* (2022), §2.2. The initial-step correction is necessary for the unrestricted
initialization in Algorithm 2.2.1 of the supplied transcription.
-/

open Filter Topology

noncomputable section

namespace Optimization.SmoothDescent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sharp quadratic upper model along the negative gradient. -/
theorem gradient_step_upper_bound {f : E → ℝ} {g : E → E} {L : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    f (x - t • g x) ≤ f x - t * ‖g x‖ ^ 2 + L / 2 * t ^ 2 * ‖g x‖ ^ 2 := by
  have h := Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le
    (convex_univ : Convex ℝ (Set.univ : Set E))
    (fun y _ => hf y) (x := x) (y := x - t • g x) (Set.mem_univ _) (Set.mem_univ _)
    (fun y _ => by simpa only [← map_sub, innerSL_apply_norm] using hL y x)
  have hsub : x - t • g x - x = -(t • g x) := by abel
  simp only [hsub, map_neg, map_smul, innerSL_apply_apply, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, smul_eq_mul] at h
  have hh := (abs_le.mp h).2
  nlinarith

/-- Every nonnegative step below the Lipschitz threshold satisfies the Armijo test. -/
theorem armijo_of_step_le {f : E → ℝ} {g : E → E} {L α t : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (x : E) (ht : 0 ≤ t) (htmax : t ≤ 2 * (1 - α) / L) :
    LineSearch.Armijo f (fun y => innerSL ℝ (g y)) α x (-g x) t := by
  have h := gradient_step_upper_bound hf hL x ht
  rw [LineSearch.Armijo, map_neg, innerSL_apply_apply, real_inner_self_eq_norm_sq,
    smul_neg, ← sub_eq_add_neg]
  have hLt : L * t ≤ 2 * (1 - α) := by
    have := (le_div_iff₀ hLpos).mp htmax
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hLt (mul_nonneg ht (sq_nonneg ‖g x‖))
  nlinarith

/-- The `i`th trial of a dyadic backtracking search. -/
def backtrackingStep (initial : ℝ) (i : ℕ) : ℝ := initial * (1 / 2 : ℝ) ^ i

/-- The accepted trial is the first one that passes the Armijo test. -/
def IsBacktrackingIndex (f : E → ℝ) (g : E → E) (α initial : ℝ) (x : E) (i : ℕ) : Prop :=
  LineSearch.Armijo f (fun y => innerSL ℝ (g y)) α x (-g x) (backtrackingStep initial i) ∧
    ∀ j < i, ¬ LineSearch.Armijo f (fun y => innerSL ℝ (g y)) α x (-g x)
      (backtrackingStep initial j)

/-- The initial backtracking trial uses the initial step. -/
@[simp] theorem backtrackingStep_zero (initial : ℝ) : backtrackingStep initial 0 = initial := by
  simp [backtrackingStep]

/-- Each additional trial halves the preceding step. -/
@[simp] theorem backtrackingStep_succ (initial : ℝ) (i : ℕ) :
    backtrackingStep initial (i + 1) = backtrackingStep initial i / 2 := by
  simp [backtrackingStep, pow_succ, mul_assoc, div_eq_mul_inv]

/-- Positive initialization makes every trial positive. -/
theorem backtrackingStep_pos {initial : ℝ} (h : 0 < initial) (i : ℕ) :
    0 < backtrackingStep initial i := by
  exact mul_pos h (pow_pos (by norm_num) _)

/-- There is a trial below any positive step threshold. -/
theorem exists_backtrackingStep_le (initial : ℝ) {threshold : ℝ} (hthreshold : 0 < threshold) :
    ∃ i, backtrackingStep initial i ≤ threshold := by
  have hlim : Tendsto (backtrackingStep initial) atTop (𝓝 0) := by
    change Tendsto (fun i : ℕ => initial * (1 / 2 : ℝ) ^ i) atTop (𝓝 0)
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul initial
  obtain ⟨i, hi⟩ := (hlim.eventually (gt_mem_nhds hthreshold)).exists
  exact ⟨i, hi.le⟩

/-- Dyadic backtracking terminates under the Lipschitz-gradient hypothesis. -/
theorem exists_backtrackingIndex {f : E → ℝ} {g : E → E} {L α initial : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (hα : α < 1) (hini : 0 < initial) (x : E) :
    ∃ i, IsBacktrackingIndex f g α initial x i := by
  classical
  have hbound : 0 < 2 * (1 - α) / L := div_pos (by linarith) hLpos
  obtain ⟨i, hi⟩ := exists_backtrackingStep_le initial hbound
  have hex : ∃ i, LineSearch.Armijo f (fun y => innerSL ℝ (g y)) α x (-g x)
      (backtrackingStep initial i) :=
    ⟨i, armijo_of_step_le hf hL hLpos x (backtrackingStep_pos hini i).le hi⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩

/-- The first accepted step is uniformly positive, including when the initial step is already
below the sufficient-step threshold. -/
theorem backtrackingStep_lower_bound {f : E → ℝ} {g : E → E} {L α initial : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (hini : 0 < initial) {x : E} {i : ℕ} (hi : IsBacktrackingIndex f g α initial x i) :
    min initial ((1 - α) / L) ≤ backtrackingStep initial i := by
  cases i with
  | zero => simp
  | succ i =>
    have hrejected := hi.2 i (Nat.lt_succ_self i)
    have hlarge : 2 * (1 - α) / L < backtrackingStep initial i := by
      by_contra! h
      exact hrejected (armijo_of_step_le hf hL hLpos x (backtrackingStep_pos hini i).le h)
    rw [backtrackingStep_succ]
    have hlarge' : 2 * ((1 - α) / L) < backtrackingStep initial i := by
      convert hlarge using 1
      ring
    have : (1 - α) / L ≤ backtrackingStep initial i / 2 := by linarith
    exact (min_le_right _ _).trans this

/-- Read the accepted Armijo test without unfolding the backtracking specification. -/
theorem IsBacktrackingIndex.armijo {f : E → ℝ} {g : E → E} {α initial : ℝ} {x : E} {i : ℕ}
    (hi : IsBacktrackingIndex f g α initial x i) :
    f (x - backtrackingStep initial i • g x) ≤
      f x - α * backtrackingStep initial i * ‖g x‖ ^ 2 := by
  have h := hi.1
  simpa only [LineSearch.Armijo, smul_neg, ← sub_eq_add_neg, map_neg,
    innerSL_apply_apply, real_inner_self_eq_norm_sq, mul_neg, ← sub_eq_add_neg] using h

/-- A run of negative-gradient Armijo backtracking up to its first successful gradient test.
The indices specify the actual inner search; the sequence may be extended arbitrarily after
termination. -/
structure IsBacktrackingSequence (f : E → ℝ) (g : E → E) (α initial ε : ℝ)
    (x : ℕ → E) (index : ℕ → ℕ) : Prop where
  /-- Before termination, the accepted trial is the first one that passes Armijo. -/
  first : ∀ k, (∀ j ≤ k, ε < ‖g (x j)‖) →
    IsBacktrackingIndex f g α initial (x k) (index k)
  /-- Before termination, the algorithm takes its accepted negative-gradient step. -/
  step : ∀ k, (∀ j ≤ k, ε < ‖g (x j)‖) →
    x (k + 1) = x k - backtrackingStep initial (index k) • g (x k)

/-- Armijo backtracking reaches an approximate stationary point within the descent budget.
This statement makes no assumption about decrease after the first successful test. -/
theorem exists_stationary_of_armijo {f : E → ℝ} {g : E → E} {L α initial ε low : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (hαpos : 0 < α) (hα : α < 1) (hini : 0 < initial) (hε : 0 < ε)
    {x : ℕ → E} {index : ℕ → ℕ}
    (hseq : IsBacktrackingSequence f g α initial ε x index) (hlow : ∀ k, low ≤ f (x k)) :
    ∃ k ≤ ⌊(f (x 0) - low) / (α * min initial ((1 - α) / L) * ε ^ 2)⌋₊,
      ‖g (x k)‖ ≤ ε ∧ ∀ j < k, ε < ‖g (x j)‖ := by
  have hsmin : 0 < min initial ((1 - α) / L) :=
    lt_min hini (div_pos (by linarith) hLpos)
  have hδ : 0 < α * min initial ((1 - α) / L) * ε ^ 2 := by positivity
  obtain ⟨k, hk, hstop, hfirst⟩ := EvaluationComplexity.exists_first_of_decrease
    (u := fun k => f (x k)) (P := fun k => ‖g (x k)‖ ≤ ε) hδ hlow (by
      intro k hfail
      have hp : ∀ j ≤ k, ε < ‖g (x j)‖ := fun j hj => lt_of_not_ge (hfail j hj)
      have hindex := hseq.first k hp
      have hs := backtrackingStep_lower_bound hf hL hLpos hini hindex
      have hdec := hindex.armijo
      rw [← hseq.step k hp] at hdec
      have hsq : ε ^ 2 ≤ ‖g (x k)‖ ^ 2 := by nlinarith [hp k le_rfl]
      have hm := mul_le_mul_of_nonneg_left
        (mul_le_mul hs hsq (sq_nonneg ε) (backtrackingStep_pos hini _).le) hαpos.le
      nlinarith)
  exact ⟨k, hk, hstop, fun j hj => lt_of_not_ge (hfirst j hj)⟩

/-- Any trial below the sufficient-step threshold bounds the first accepted index. -/
theorem backtrackingIndex_le_of_step_le {f : E → ℝ} {g : E → E} {L α initial : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (hini : 0 < initial) {x : E} {i B : ℕ} (hi : IsBacktrackingIndex f g α initial x i)
    (hB : backtrackingStep initial B ≤ 2 * (1 - α) / L) : i ≤ B := by
  by_contra! h
  exact hi.2 B h (armijo_of_step_le hf hL hLpos x (backtrackingStep_pos hini B).le hB)

/-- Exact objective-oracle count through iterate `k`: the initial value, and every rejected
or accepted trial value. Accepted values are reused at the next iteration. -/
def functionEvaluations (index : ℕ → ℕ) (k : ℕ) : ℕ :=
  1 + ∑ j ∈ Finset.range k, (index j + 1)

/-- A uniform bound on backtracking indices gives a linear bound on objective evaluations. -/
theorem functionEvaluations_le {index : ℕ → ℕ} {k B : ℕ}
    (hB : ∀ j < k, index j ≤ B) : functionEvaluations index k ≤ 1 + k * (B + 1) := by
  apply Nat.add_le_add_left
  calc
    ∑ j ∈ Finset.range k, (index j + 1) ≤ ∑ _j ∈ Finset.range k, (B + 1) :=
      Finset.sum_le_sum fun j hj => Nat.add_le_add_right (hB j (Finset.mem_range.mp hj)) 1
    _ = k * (B + 1) := by simp

/-- A first stationary iterate, with separate bounds for objective and gradient evaluations.
`B` bounds the inner search uniformly and does not depend on the stationarity tolerance. -/
theorem exists_stationary_with_cost {f : E → ℝ} {g : E → E} {L α initial ε low : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (hαpos : 0 < α) (hα : α < 1) (hini : 0 < initial) (hε : 0 < ε)
    {x : ℕ → E} {index : ℕ → ℕ}
    (hseq : IsBacktrackingSequence f g α initial ε x index) (hlow : ∀ k, low ≤ f (x k))
    (B : ℕ) (hB : backtrackingStep initial B ≤ 2 * (1 - α) / L) :
    let budget := (f (x 0) - low) / (α * min initial ((1 - α) / L) * ε ^ 2)
    ∃ K, ‖g (x K)‖ ≤ ε ∧ (∀ j < K, ε < ‖g (x j)‖) ∧ (K : ℝ) ≤ budget ∧
      (functionEvaluations index K : ℝ) ≤ 1 + (B + 1 : ℕ) * budget ∧
      ((K + 1 : ℕ) : ℝ) ≤ budget + 1 := by
  dsimp only
  obtain ⟨K, hK, hstop, hfirst⟩ := exists_stationary_of_armijo hf hL hLpos
    hαpos hα hini hε hseq hlow
  have hbudget : 0 ≤ (f (x 0) - low) / (α * min initial ((1 - α) / L) * ε ^ 2) :=
    div_nonneg (sub_nonneg.mpr (hlow 0)) (by positivity)
  have hKreal : (K : ℝ) ≤ (f (x 0) - low) / (α * min initial ((1 - α) / L) * ε ^ 2) :=
    (Nat.cast_le.mpr hK).trans (Nat.floor_le hbudget)
  have hindices : ∀ j < K, index j ≤ B := by
    intro j hj
    exact backtrackingIndex_le_of_step_le hf hL hLpos hini
      (hseq.first j (fun m hm => hfirst m (lt_of_le_of_lt hm hj))) hB
  have hcost := functionEvaluations_le hindices
  have hcostreal : (functionEvaluations index K : ℝ) ≤ 1 + (K : ℝ) * (B + 1 : ℕ) := by
    exact_mod_cast hcost
  refine ⟨K, hstop, hfirst, hKreal, ?_, ?_⟩
  · have hm := mul_le_mul_of_nonneg_left hKreal (Nat.cast_nonneg (B + 1) : (0 : ℝ) ≤ _)
    nlinarith
  · push_cast
    linarith

open Classical in
/-- The first accepted backtracking index, constructed from the proved existence of an
accepted trial. Its value implements the inner search without a fuel parameter. -/
def backtrackingIndex {f : E → ℝ} {g : E → E} {L α initial : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (hα : α < 1) (hini : 0 < initial) (x : E) : ℕ :=
  Nat.find (exists_backtrackingIndex hf hL hLpos hα hini x)

/-- The constructed inner search returns the first accepted trial. -/
theorem backtrackingIndex_spec {f : E → ℝ} {g : E → E} {L α initial : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (hα : α < 1) (hini : 0 < initial) (x : E) :
    IsBacktrackingIndex f g α initial x (backtrackingIndex hf hL hLpos hα hini x) := by
  classical
  exact Nat.find_spec (exists_backtrackingIndex hf hL hLpos hα hini x)

open Classical in
/-- Negative-gradient descent with the first accepted dyadic Armijo trial. Once the gradient
test succeeds the iterate is held fixed, so the sequence also represents a terminated run. -/
def backtrackingIterates {f : E → ℝ} {g : E → E} {L α initial : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (hα : α < 1) (hini : 0 < initial) (ε : ℝ) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 =>
    let x := backtrackingIterates hf hL hLpos hα hini ε x₀ k
    if ‖g x‖ ≤ ε then x
    else x - backtrackingStep initial (backtrackingIndex hf hL hLpos hα hini x) • g x

/-- The constructed descent sequence starts at its prescribed initial point. -/
@[simp] theorem backtrackingIterates_zero {f : E → ℝ} {g : E → E} {L α initial : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (hα : α < 1) (hini : 0 < initial) (ε : ℝ) (x₀ : E) :
    backtrackingIterates hf hL hLpos hα hini ε x₀ 0 = x₀ := rfl

/-- The constructed descent sequence implements the backtracking run specification. -/
theorem backtrackingIterates_spec {f : E → ℝ} {g : E → E} {L α initial : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (hα : α < 1) (hini : 0 < initial) (ε : ℝ) (x₀ : E) :
    IsBacktrackingSequence f g α initial ε (backtrackingIterates hf hL hLpos hα hini ε x₀)
      (fun k => backtrackingIndex hf hL hLpos hα hini
        (backtrackingIterates hf hL hLpos hα hini ε x₀ k)) := by
  classical
  constructor
  · exact fun k _ => backtrackingIndex_spec hf hL hLpos hα hini _
  · intro k hk
    rw [backtrackingIterates]
    rw [ite_eq_right (not_le.mpr (hk k le_rfl))]

/-- The nonnegative ceiling of a base-two logarithm reaches a positive trial threshold.
The natural ceiling equals zero when the initial trial is already sufficiently small. -/
theorem backtrackingStep_logb_ceiling_le {initial threshold : ℝ}
    (hini : 0 < initial) (ht : 0 < threshold) :
    backtrackingStep initial ⌈Real.logb 2 (initial / threshold)⌉₊ ≤ threshold := by
  let B := ⌈Real.logb 2 (initial / threshold)⌉₊
  have hlog : Real.logb 2 (initial / threshold) ≤ (B : ℝ) := Nat.le_ceil _
  have hpow : initial / threshold ≤ (2 : ℝ) ^ B := by
    have hh := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (div_pos hini ht)).mp hlog
    simpa only [Real.rpow_natCast] using hh
  have hmul := (div_le_iff₀ ht).mp hpow
  change initial * (1 / 2 : ℝ) ^ B ≤ threshold
  rw [one_div_pow, mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ B)]
  linarith

/-- The first accepted Armijo trial has the corrected logarithmic bound, with the natural
ceiling retaining the already-small-initial-step branch. -/
theorem backtrackingIndex_le_logb_ceiling {f : E → ℝ} {g : E → E} {L α initial : ℝ}
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hL : ∀ y z, ‖g y - g z‖ ≤ L * ‖y - z‖) (hLpos : 0 < L)
    (hα : α < 1) (hini : 0 < initial) {x : E} {i : ℕ}
    (hi : IsBacktrackingIndex f g α initial x i) :
    i ≤ ⌈Real.logb 2 (initial * L / (2 * (1 - α)))⌉₊ := by
  have ht : 0 < 2 * (1 - α) / L := by positivity
  have hB := backtrackingStep_logb_ceiling_le hini ht
  rw [div_div_eq_mul_div] at hB
  exact backtrackingIndex_le_of_step_le hf hL hLpos hini hi hB

end Optimization.SmoothDescent
