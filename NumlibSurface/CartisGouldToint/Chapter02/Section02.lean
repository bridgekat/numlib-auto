import Numlib.Optimization.ExactLineSearch
import Numlib.Optimization.ExactLineSearchSharpness
import Numlib.Optimization.FirstOrderSharpness
import Numlib.Optimization.SmoothDescent
import NumlibSurface.CartisGouldToint.Chapter02.Section01

/-!
# Steepest descent with backtracking and exact line search

Algorithm 2.2.1 and Lemma 2.2.1, specialized to Euclidean space. The corrected form of Theorem
2.2.2 counts one initial objective evaluation, all rejected and accepted trial values, and the
final gradient test. The initial step enters the decrease constant through
`min initial ((1 - α) / L)`. Any natural trial bound `B` below the sufficient-step threshold gives
the uniform per-iteration oracle bound `B + 1`, independently of the accuracy tolerance.

The supplied transcription's equations (2.2.6)–(2.2.9) omit these initial-step and oracle-count
corrections. The original theorem remains marked `wrong` in the plan; the declaration below is
explicitly named as its correction. A uniform family of globally smooth hard objectives
proves sharpness for the actual backtracking iterates. The corrected logarithmic halving
bound is uniform over all iterates. Exact global ray minimization has the iteration bound
of Theorem 2.2.4, conditional on an actual lawful sequence of ray minimizers. A diagonal
quadratic family proves Theorem 2.2.5 with uniform smoothness and initial-gap constants.
-/

noncomputable section

namespace CartisGouldToint.Chapter02.Section02

open Section01
open Optimization.SmoothDescent

variable {n : ℕ}

/-- Algorithm 2.2.1 (SDBA): reset to the initial step, halve until the first accepted Armijo
trial, take the negative-gradient step, and stop when the gradient-norm test succeeds.
The returned sequence holds the terminal iterate fixed. -/
def algorithm_2_2_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) {L α initial : ℝ}
    (hf : assumption_f_gL f L) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hini : 0 < initial)
    (ε : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n) :=
  backtrackingIterates hf.hasFDerivAt hf.lipschitz hf.constant_pos hα.2 hini ε x₀

/-- The number of halvings at each nonterminal iteration of Algorithm 2.2.1. -/
def backtrackingIndices (f : EuclideanSpace ℝ (Fin n) → ℝ) {L α initial : ℝ}
    (hf : assumption_f_gL f L) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hini : 0 < initial)
    (ε : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) : ℕ :=
  backtrackingIndex hf.hasFDerivAt hf.lipschitz hf.constant_pos hα.2 hini
    (algorithm_2_2_1 f hf hα hini ε x₀ k)

/-- The concrete SDBA construction satisfies the backtracking-run interface. -/
theorem algorithm_2_2_1_spec (f : EuclideanSpace ℝ (Fin n) → ℝ) {L α initial : ℝ}
    (hf : assumption_f_gL f L) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hini : 0 < initial)
    (ε : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) :
    IsBacktrackingSequence f (gradient f) α initial ε (algorithm_2_2_1 f hf hα hini ε x₀)
      (backtrackingIndices f hf hα hini ε x₀) :=
  backtrackingIterates_spec hf.hasFDerivAt hf.lipschitz hf.constant_pos hα.2 hini ε x₀

/-- Lemma 2.2.1: every step in the stated closed interval satisfies sufficient decrease. -/
theorem lemma_2_2_1 {f : EuclideanSpace ℝ (Fin n) → ℝ} {L α t : ℝ}
    (hf : assumption_f_gL f L) (_hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (x : EuclideanSpace ℝ (Fin n)) (ht : t ∈ Set.Icc (0 : ℝ) (2 * (1 - α) / L)) :
    f (x - t • gradient f x) ≤ f x - α * t * ‖gradient f x‖ ^ 2 := by
  have h := armijo_of_step_le hf.hasFDerivAt hf.lipschitz hf.constant_pos x ht.1 ht.2
  simpa only [LineSearch.Armijo, smul_neg, ← sub_eq_add_neg, map_neg,
    innerSL_apply_apply, real_inner_self_eq_norm_sq, mul_neg, ← sub_eq_add_neg] using h

/-- Corrected Theorem 2.2.2: SDBA reaches the first `ε`-approximate first-order minimizer in
at most `gap / (c * ε²)` steps, where `c = α * min initial ((1 - α) / L)`.
If trial `B` is below the sufficient-step threshold, objective calls are at most
`1 + (B + 1) * gap / (c * ε²)` and gradient calls at most `gap / (c * ε²) + 1`.
The exact objective count is the initial value plus `index + 1` trials per outer step. -/
theorem theorem_2_2_2_corrected {f : EuclideanSpace ℝ (Fin n) → ℝ} {L α initial ε low : ℝ}
    (hf : assumption_f_gL f L) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hini : 0 < initial)
    (hε : 0 < ε) (hlow : ∀ x, low ≤ f x) (x₀ : EuclideanSpace ℝ (Fin n))
    (B : ℕ) (hB : backtrackingStep initial B ≤ 2 * (1 - α) / L) :
    let x := algorithm_2_2_1 f hf hα hini ε x₀
    let index := backtrackingIndices f hf hα hini ε x₀
    let budget := (f x₀ - low) / (α * min initial ((1 - α) / L) * ε ^ 2)
    ∃ K, approximateFirstOrderMinimizer f ε (x K) ∧ (∀ j < K, ε < ‖gradient f (x j)‖) ∧
      (K : ℝ) ≤ budget ∧
      (functionEvaluations index K : ℝ) ≤ 1 + (B + 1 : ℕ) * budget ∧
      ((K + 1 : ℕ) : ℝ) ≤ budget + 1 := by
  simpa only [approximateFirstOrderMinimizer, algorithm_2_2_1, backtrackingIterates_zero] using
    exists_stationary_with_cost hf.hasFDerivAt hf.lipschitz hf.constant_pos
      hα.1 hα.2 hini hε (algorithm_2_2_1_spec f hf hα hini ε x₀)
      (fun k => hlow (algorithm_2_2_1 f hf hα hini ε x₀ k)) B hB

/-- Theorem 2.2.3: fixed global smoothness and gap constants admit, at every tolerance,
a one-dimensional objective on which the actual SDBA algorithm takes at least `ε⁻²` steps.
The initial step is one; every first trial is accepted. Oracle counts include initialization. -/
theorem theorem_2_2_3 {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ L B : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (hf : assumption_f_gL f L)
        (x₀ : EuclideanSpace ℝ (Fin 1)) (N : ℕ),
        assumption_f_Bb f ∧ (∀ u, -B ≤ f u) ∧ f x₀ - (-B) ≤ B ∧
        ε⁻¹ ^ 2 ≤ (N : ℝ) ∧
        (∀ k < N, ε < ‖gradient f (algorithm_2_2_1 f hf hα zero_lt_one ε x₀ k)‖) ∧
        approximateFirstOrderMinimizer f ε
          (algorithm_2_2_1 f hf hα zero_lt_one ε x₀ N) ∧
        ε⁻¹ ^ 2 ≤ (functionEvaluations
          (backtrackingIndices f hf hα zero_lt_one ε x₀) N : ℝ) ∧
        ε⁻¹ ^ 2 ≤ ((N + 1 : ℕ) : ℝ) := by
  classical
  obtain ⟨L, B, hL, _, hc⟩ := Optimization.LowerBound.exists_firstOrder_chain
  refine ⟨L, B, ?_⟩
  intro ε he he1
  obtain ⟨f, N, x, hf, hLip, hlow, hzero, hN, hpre, hlast, hstep, hdrop⟩ := hc ε he he1
  have hfg : assumption_f_gL f L := ⟨hf, hL, hLip⟩
  have hseq := Optimization.LowerBound.unitSteps_isBacktrackingSequence hstep hdrop hα.2.le
    (ε := ε)
  have hindex (k : ℕ) (hk : k < N) :
      backtrackingIndex hfg.hasFDerivAt hfg.lipschitz hfg.constant_pos
        hα.2 zero_lt_one (x k) = 0 := by
    apply (Nat.find_eq_zero _).mpr
    exact hseq.first k (fun j hj => by rw [hpre j (by omega)]; linarith)
  have hx : ∀ k ≤ N, algorithm_2_2_1 f hfg hα zero_lt_one ε (x 0) k = x k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hkn : k < N := by omega
      have hi := ih (by omega)
      change backtrackingIterates _ _ _ _ _ _ _ (k + 1) = _
      rw [backtrackingIterates]
      change backtrackingIterates _ _ _ _ _ _ _ k = x k at hi
      rw [hi, ite_eq_right (by rw [hpre k hkn]; linarith), hindex k hkn,
        backtrackingStep_zero, one_smul, ← hstep k]
  refine ⟨f, hfg, x 0, N, assumption_f_Bb_iff.mpr ⟨-B, hlow⟩, hlow,
    by rw [hzero]; simp, hN, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hx k hk.le, hpre k hk]
    linarith
  · rw [approximateFirstOrderMinimizer, hx N le_rfl, hlast, norm_zero]
    exact he.le
  · apply hN.trans
    exact_mod_cast (by
      unfold functionEvaluations
      have hsum : N ≤ ∑ j ∈ Finset.range N,
          (backtrackingIndices f hfg hα zero_lt_one ε (x 0) j + 1) := by
        simpa using Finset.sum_le_sum (s := Finset.range N)
          (fun j _ => Nat.le_add_left 1
            (backtrackingIndices f hfg hα zero_lt_one ε (x 0) j))
      omega : N ≤ functionEvaluations (backtrackingIndices f hfg hα zero_lt_one ε (x 0)) N)
  · exact hN.trans (by push_cast; linarith)

/-- Exact steepest-descent line searches (2.2.26), executed before the first successful
termination test. Each step is a global minimum on the nonnegative ray; the source's choice
of the first tied minimum is optional. A lawful run explicitly supplies its ray minimizers. -/
def exactLineSearchRun (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ) : Prop :=
  IsExactSequence f (gradient f) ε x t

/-- Theorem 2.2.4: any lawful exact-line-search run reaches its first small gradient in
at most `2 L gap / ε²` iterations. The constant is chosen before the tolerance and run;
internal exact-search oracle evaluations are not bounded by this theorem. -/
theorem theorem_2_2_4 {f : EuclideanSpace ℝ (Fin n) → ℝ} {L low : ℝ}
    (hf : assumption_f_gL f L) (hlow : ∀ y, low ≤ f y) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ ε : ℝ, 0 < ε →
      ∀ (x : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ),
        exactLineSearchRun f ε x t → ∃ K : ℕ,
          approximateFirstOrderMinimizer f ε (x K) ∧
          (∀ j < K, ε < ‖gradient f (x j)‖) ∧
          (K : ℝ) ≤ kappa * ((f (x 0) - low) / ε ^ 2) := by
  refine ⟨2 * L, mul_pos (by norm_num) hf.constant_pos, ?_⟩
  intro ε he x t hr
  exact exists_stationary_of_exactLineSearch hf.hasFDerivAt hf.lipschitz hf.constant_pos
    he hr (fun k => hlow (x k))

/-- The corrected logarithmic halving bound (2.2.6), uniform in the iterate and tolerance.
The natural ceiling is zero when the initial trial is already below the sufficient-step
threshold, and oracle counting still includes its accepted trial. -/
theorem backtracking_uniform_log_bound {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {L α initial : ℝ} (hf : assumption_f_gL f L) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hini : 0 < initial) (ε : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    backtrackingIndices f hf hα hini ε x₀ k ≤
      ⌈Real.logb 2 (initial * L / (2 * (1 - α)))⌉₊ :=
  backtrackingIndex_le_logb_ceiling hf.hasFDerivAt hf.lipschitz hf.constant_pos hα.2 hini
    (backtrackingIndex_spec hf.hasFDerivAt hf.lipschitz hf.constant_pos hα.2 hini _)

/-- Theorem 2.2.5: with uniform global smoothness and initial-gap constants, exact steepest
descent can take more than `⌈ε⁻²⌉` iterations before its first successful gradient test.
The two-dimensional example starts at the origin, and every step is an actual global
nonnegative-ray minimizer. Each outer iteration requires an objective and gradient evaluation. -/
theorem theorem_2_2_5 :
    ∃ L B : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (f : EuclideanSpace ℝ (Fin 2) → ℝ) (_hf : assumption_f_gL f L)
        (x : ℕ → EuclideanSpace ℝ (Fin 2)) (t : ℕ → ℝ) (K : ℕ),
        assumption_f_Bb f ∧ (∀ u, 0 ≤ f u) ∧ f (x 0) ≤ B ∧ x 0 = 0 ∧
        exactLineSearchRun f ε x t ∧
        (∀ k, LineSearch.IsExact f (x k) (-gradient f (x k)) (t k)) ∧
        (∀ k, x (k + 1) = x k - t k • gradient f (x k)) ∧
        approximateFirstOrderMinimizer f ε (x K) ∧
        (∀ j < K, ε < ‖gradient f (x j)‖) ∧ ⌈ε⁻¹ ^ 2⌉₊ < K ∧
        ε⁻¹ ^ 2 ≤ (K : ℝ) ∧ ε⁻¹ ^ 2 ≤ ((K + 1 : ℕ) : ℝ) := by
  obtain ⟨L, B, hL, _, h⟩ :=
    Optimization.ExactLineSearchSharpness.exists_slow_exactLineSearch
  refine ⟨L, B, ?_⟩
  intro ε he he1
  obtain ⟨f, x, t, K, hf, hLip, hlow, hgap, hx, hsearch, hstep, hK, hfirst, hlong⟩ :=
    h ε he he1
  have hcount : ε⁻¹ ^ 2 ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hlong.le)
  refine ⟨f, ⟨hf, hL, hLip⟩, x, t, K, assumption_f_Bb_iff.mpr ⟨0, hlow⟩,
    hlow, hgap, hx, ⟨fun k _ => hsearch k, fun k _ => hstep k⟩, hsearch, hstep,
    hK, hfirst, hlong, hcount, ?_⟩
  exact hcount.trans (by push_cast; linarith)

end CartisGouldToint.Chapter02.Section02
