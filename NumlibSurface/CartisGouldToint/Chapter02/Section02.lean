import Numlib.Optimization.Complexity.Basic
import Numlib.Optimization.Complexity.SlowExample
import Numlib.Optimization.Complexity.ZigZagExample
import Numlib.Optimization.LineSearch.Backtracking
import NumlibSurface.CartisGouldToint.Chapter02.Section01

/-!
# Cartis–Gould–Toint §2.2: Linesearch algorithms

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §2.2: steepest descent with a
backtracking-Armijo linesearch (SDBA) and with an exact linesearch (SDEX), on
`ℝⁿ = EuclideanSpace ℝ (Fin n)`.

Algorithms are formalized as *run predicates* on the sequence of iterates: a run is any sequence
obeying the rules of the algorithm at every iteration before the termination test
`‖∇f(x_k)‖ ≤ ε` of Step 1 first holds (`Optimization.UntilHit`); the termination index is the
first `k` at which the test holds (`Optimization.IsFirstHit`).

## Main definitions

* `algorithm_2_2_1 f α tini ε x i` — Algorithm 2.2.1 (SDBA), with iterates `x` and backtracking
  indices `i` (the accepted step being `t_k = 2^{-i_k} t_ini`); `exists_algorithm_2_2_1` (a run
  exists under f.gL) and `algorithm_2_2_1.eq_of_eq` (SDBA is deterministic).
* `sdbaFunEvalCount i k = 1 + ∑_{j<k} (i_j + 1)` — the number of objective evaluations of SDBA
  before iteration `k` (the initial one, then `i_j + 1` trial points at iteration `j`).
* `kappaSDBA L α tini = 1 / (α min(t_ini, (1-α)/L))` — the constant of Theorem 2.2.2;
  it is the book's `κ_SDBA = L/(α(1-α))` when `t_ini ≥ (1-α)/L` (`kappaSDBA_of_le`).
* `IsSDEXRun f ε x t` — the SDEX algorithm: steepest descent with the exact linesearch (2.2.26)
  (`LineSearch.IsExactLineMin`: `t_k` is the first global minimizer of `t ↦ f(x_k - t∇f(x_k))`
  on `t ≥ 0`); `IsSDEXRun.exists` (a run exists when the initial sublevel set is bounded).

## Main results

* `lemma_2_2_1` — Lemma 2.2.1: the Armijo condition holds for `t ∈ [0, 2(1-α)/L]`;
  `lemma_2_2_1_index` gives the consequences (2.2.6)–(2.2.7) for the backtracking index.
* `theorem_2_2_2` — Theorem 2.2.2, with a corrected objective-evaluation bound (see below).
* `theorem_2_2_3` — Theorem 2.2.3: SDBA may need `ε⁻²` iterations (and `ε⁻² + 1` evaluations).
* `theorem_2_2_4` — Theorem 2.2.4: SDEX needs at most `2L(f(x₀) - f_low)/ε²` iterations.
* `theorem_2_2_5` — Theorem 2.2.5: SDEX may need `ε⁻²` iterations (the two-dimensional zig-zag
  example `Optimization.zigZagFunction` of Appendix B).

## Fixes with respect to the book

* (2.2.7) `t_k ≥ t_low/2` holds only when `t_ini ≥ t_low/2`; in general
  `t_k ≥ min(t_ini, t_low/2)`. Accordingly the constant of Theorem 2.2.2 is
  `kappaSDBA = 1/(α min(t_ini, (1-α)/L))`, equal to the book's `κ_SDBA` when `t_ini ≥ (1-α)/L`.
* (2.2.8) as printed, `⌈log₂(L t_ini/(2(1-α)))⌉ κ_SDBA (f(x₀) - f_low)/ε²`, is false: it vanishes
  for `t_ini ≤ 2(1-α)/L` although the algorithm evaluates `f` at least once, and it omits the
  first trial point of every iteration. The corrected bound is
  `1 + (⌈log₂(L t_ini/(2(1-α)))⌉ + 1) κ (f(x₀) - f_low)/ε²`.
* Theorem 2.2.3: the hypothesis `t_ini ≥ α` of the proof is not needed, and `ε⁻²` is assumed to
  be an integer (as the proof does, (2.2.14)); likewise in Theorem 2.2.5.

The variants of §§2.2.3.1–2.2.3.3 and 2.2.3.5 (flexible Armijo, Goldstein–Armijo, Nesterov's view,
nonmonotone methods) contain no numbered results and are not formalized.
-/

open Set Finset Optimization LineSearch
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter02

variable {n : ℕ}

/-! ### Lemma 2.2.1 -/

section Lemma221

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {L α tini : ℝ}

/-- **Lemma 2.2.1** of [cartis2022evaluation] ((2.2.3)–(2.2.4)). Under f.gL, the Armijo condition
`f(x - t∇f(x)) ≤ f(x) - α t ‖∇f(x)‖²` holds for every `t ∈ [0, t_low]`,
`t_low = 2(1-α)/L_{f,1}`. -/
theorem lemma_2_2_1 (hf : AssumptionGL f L) (x : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 2 * (1 - α) / L) :
    f (x - t • gradient f x) ≤ f x - α * t * ‖gradient f x‖ ^ 2 :=
  armijo_neg_gradient_of_le hf.differentiable hf.lipschitz hf.pos x ht0 ht

/-- **Consequences (2.2.6)–(2.2.7) of Lemma 2.2.1** ([cartis2022evaluation]). Under f.gL, with
`0 < α < 1` and `t_ini > 0`, the backtracking index (the least `i` such that `2^{-i} t_ini`
satisfies (2.2.1)) is at most `⌈log₂(L t_ini/(2(1-α)))⌉`, and the accepted step satisfies
`t ≥ min(t_ini, t_low/2)` (the book's (2.2.7), `t ≥ t_low/2`, needs `t_ini ≥ t_low/2`). -/
theorem lemma_2_2_1_index (hf : AssumptionGL f L) (hα : α < 1) (htini : 0 < tini)
    (x : EuclideanSpace ℝ (Fin n)) :
    backtrackingIndex f α tini x ≤ ⌈Real.logb 2 (L * tini / (2 * (1 - α)))⌉₊ ∧
      min tini ((1 - α) / L) ≤ tini * 2⁻¹ ^ backtrackingIndex f α tini x :=
  backtrackingIndex_le hf.differentiable hf.lipschitz hf.pos hα htini x

/-- Under f.gL some trial step of the backtracking linesearch satisfies (2.2.1). -/
theorem exists_backtrackingTest (hf : AssumptionGL f L) (hα : α < 1) (htini : 0 < tini)
    (x : EuclideanSpace ℝ (Fin n)) : ∃ i, BacktrackingTest f α tini x i := by
  have hpos : 0 < 2 * (1 - α) / L / tini := by
    have := hf.pos; have : 0 < 1 - α := sub_pos.2 hα; positivity
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (2⁻¹ : ℝ) < 1)
  refine ⟨i, backtrackingTest_of_le hf.differentiable hf.lipschitz hf.pos htini x ?_⟩
  rw [lt_div_iff₀ htini] at hi
  linarith

end Lemma221

/-! ### Algorithm 2.2.1 (SDBA) -/

/-- **Algorithm 2.2.1** (SDBA) of [cartis2022evaluation], as a run predicate: `x` is the sequence
of iterates (`x 0` the given starting point) and `i k` the number of halvings of the linesearch at
iteration `k`. The constants satisfy (2.2.2), `t_ini > 0` and `0 < α < 1`, and `ε > 0`. At every
iteration `k` before the termination test `‖∇f(x_k)‖ ≤ ε` first holds, `i_k` is the smallest index
for which the trial step `t_k = 2^{-i_k} t_ini` satisfies the Armijo condition (2.2.1)
(`LineSearch.BacktrackingTest`), and `x_{k+1} = x_k - t_k ∇f(x_k)` (Step 4). -/
structure algorithm_2_2_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (α tini ε : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (i : ℕ → ℕ) : Prop where
  /-- `t_ini > 0` (2.2.2). -/
  tini_pos : 0 < tini
  /-- `α > 0` (2.2.2). -/
  α_pos : 0 < α
  /-- `α < 1` (2.2.2). -/
  α_lt_one : α < 1
  /-- The accuracy level is positive. -/
  ε_pos : 0 < ε
  /-- Step 3: the accepted trial step satisfies (2.2.1). -/
  armijo : UntilHit (fun k => ‖gradient f (x k)‖ ≤ ε) fun k =>
    BacktrackingTest f α tini (x k) (i k)
  /-- Step 3: the earlier trial steps of the iteration violate (2.2.1). -/
  minimal : UntilHit (fun k => ‖gradient f (x k)‖ ≤ ε) fun k =>
    ∀ j < i k, ¬ BacktrackingTest f α tini (x k) j
  /-- Step 4: the new iterate. -/
  step : UntilHit (fun k => ‖gradient f (x k)‖ ≤ ε) fun k =>
    x (k + 1) = x k - (tini * 2⁻¹ ^ i k) • gradient f (x k)

namespace algorithm_2_2_1

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {α tini ε L : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)}
  {i : ℕ → ℕ}

/-- Before termination, `i_k` is the backtracking index `LineSearch.backtrackingIndex`. -/
theorem index_eq (h : algorithm_2_2_1 f α tini ε x i) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) : i k = backtrackingIndex f α tini (x k) := by
  have ht := h.armijo k hk
  refine le_antisymm ?_ (backtrackingIndex_le_of_test ht)
  by_contra hlt
  exact h.minimal k hk _ (not_le.1 hlt) (backtrackingIndex_spec ⟨_, ht⟩)

/-- **SDBA is deterministic**: two runs from the same starting point coincide up to (and
including) the termination index of the first one. -/
theorem eq_of_eq {x' : ℕ → EuclideanSpace ℝ (Fin n)} {i' : ℕ → ℕ}
    (h : algorithm_2_2_1 f α tini ε x i) (h' : algorithm_2_2_1 f α tini ε x' i')
    (h0 : x' 0 = x 0) {K : ℕ} (hK : ∀ j < K, ¬ ‖gradient f (x j)‖ ≤ ε) :
    ∀ k ≤ K, (∀ j ≤ k, x' j = x j) ∧ ∀ j < k, i' j = i j := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun j hj => by rw [Nat.le_zero.1 hj, h0], fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨hx, -⟩ := ih (Nat.le_of_succ_le hk)
    have hstop : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε := fun j hj => hK j (by omega)
    have hstop' : ∀ j ≤ k, ¬ ‖gradient f (x' j)‖ ≤ ε := fun j hj => by
      rw [hx j hj]; exact hstop j hj
    have hi : ∀ j ≤ k, i' j = i j := fun j hj => by
      have hj1 : ∀ l ≤ j, ¬ ‖gradient f (x l)‖ ≤ ε := fun l hl => hstop l (hl.trans hj)
      have hj2 : ∀ l ≤ j, ¬ ‖gradient f (x' l)‖ ≤ ε := fun l hl => hstop' l (hl.trans hj)
      rw [h'.index_eq hj2, h.index_eq hj1, hx j hj]
    refine ⟨fun j hj => ?_, fun j hj => hi j (Nat.lt_succ_iff.1 hj)⟩
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · exact hx j (Nat.lt_succ_iff.1 hj)
    · rw [h.step k hstop, h'.step k hstop', hx k le_rfl, hi k le_rfl]

/-- **Decrease of SDBA** ((2.2.10)): under f.gL, at every iteration `k` before termination,
`f(x_k) - f(x_{k+1}) ≥ α min(t_ini, (1-α)/L) ‖∇f(x_k)‖²`. -/
theorem sub_ge (h : algorithm_2_2_1 f α tini ε x i) (hf : AssumptionGL f L) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) :
    α * min tini ((1 - α) / L) * ‖gradient f (x k)‖ ^ 2 ≤ f (x k) - f (x (k + 1)) := by
  have ht : f (x k - (tini * 2⁻¹ ^ i k) • gradient f (x k)) ≤
      f (x k) - α * (tini * 2⁻¹ ^ i k) * ‖gradient f (x k)‖ ^ 2 := h.armijo k hk
  rw [← h.step k hk] at ht
  have hlow := (lemma_2_2_1_index hf h.α_lt_one h.tini_pos (x k)).2
  rw [← h.index_eq hk] at hlow
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlow h.α_pos.le)
    (sq_nonneg ‖gradient f (x k)‖)
  linarith

end algorithm_2_2_1

/-- **Existence of SDBA runs** ([cartis2022evaluation], Algorithm 2.2.1 is well defined by
Lemma 2.2.1): under f.gL, for constants satisfying (2.2.2) and `ε > 0`, there is a run from every
starting point `x₀`. -/
theorem exists_algorithm_2_2_1 {f : EuclideanSpace ℝ (Fin n) → ℝ} {L α tini ε : ℝ}
    (hf : AssumptionGL f L) (htini : 0 < tini) (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x i, x 0 = x₀ ∧ algorithm_2_2_1 f α tini ε x i := by
  let next : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun y =>
    y - (tini * 2⁻¹ ^ backtrackingIndex f α tini y) • gradient f y
  let x : ℕ → EuclideanSpace ℝ (Fin n) := fun k => Nat.rec x₀ (fun _ y => next y) k
  refine ⟨x, fun k => backtrackingIndex f α tini (x k), rfl,
    ⟨htini, hα0, hα1, hε, fun k _ => ?_, fun k _ j hj => not_backtrackingTest_of_lt hj,
      fun k _ => rfl⟩⟩
  exact backtrackingIndex_spec (exists_backtrackingTest hf hα1 htini (x k))

/-! ### Theorem 2.2.2 -/

/-- The number of objective-function evaluations of SDBA before iteration `k`: the initial one
(Step 0) and `i_j + 1` at each iteration `j < k` (Step 2 and each backtrack of Step 3). -/
def sdbaFunEvalCount (i : ℕ → ℕ) (k : ℕ) : ℕ :=
  1 + ∑ j ∈ range k, (i j + 1)

theorem sdbaFunEvalCount_def (i : ℕ → ℕ) (k : ℕ) :
    sdbaFunEvalCount i k = 1 + ∑ j ∈ range k, (i j + 1) := rfl

/-- If no backtracking takes place before iteration `k`, SDBA has evaluated `f` exactly `k + 1`
times. -/
theorem sdbaFunEvalCount_of_forall_eq_zero {i : ℕ → ℕ} {k : ℕ} (hi : ∀ j < k, i j = 0) :
    sdbaFunEvalCount i k = k + 1 := by
  rw [sdbaFunEvalCount_def, sum_congr rfl fun j hj => by rw [hi j (mem_range.1 hj)]]
  simp [add_comm]

/-- The complexity constant of SDBA, `κ = 1/(α min(t_ini, (1-α)/L))` (the reciprocal of the
guaranteed decrease per unit of `‖∇f‖²`, (2.2.10) with the corrected step bound). -/
noncomputable def kappaSDBA (L α tini : ℝ) : ℝ :=
  1 / (α * min tini ((1 - α) / L))

/-- When `t_ini ≥ (1-α)/L`, `kappaSDBA` is the book's `κ_SDBA = L/(α(1-α))` (2.2.13). -/
theorem kappaSDBA_of_le {L α tini : ℝ} (hL : 0 < L) (hα : α < 1) (h : (1 - α) / L ≤ tini) :
    kappaSDBA L α tini = L / (α * (1 - α)) := by
  have : 0 < 1 - α := sub_pos.2 hα
  rw [kappaSDBA, min_eq_right h]
  field_simp

theorem kappaSDBA_pos {L α tini : ℝ} (hL : 0 < L) (hα0 : 0 < α) (hα : α < 1) (htini : 0 < tini) :
    0 < kappaSDBA L α tini := by
  have : 0 < 1 - α := sub_pos.2 hα
  unfold kappaSDBA
  have : 0 < min tini ((1 - α) / L) := lt_min htini (by positivity)
  positivity

/-- **Theorem 2.2.2** of [cartis2022evaluation], **corrected**. Assume f.Bb and f.gL and let
`x, i` be a run of SDBA (Algorithm 2.2.1). With `κ = kappaSDBA L α t_ini` (the book's
`κ_SDBA = L/(α(1-α))` when `t_ini ≥ (1-α)/L`, `kappaSDBA_of_le`) and
`i_max = ⌈log₂(L t_ini/(2(1-α)))⌉` (2.2.6), the algorithm terminates at an iteration
`k_ε ≤ κ (f(x₀) - f_low)/ε²` (2.2.13), after at most
`1 + (i_max + 1) κ (f(x₀) - f_low)/ε²` objective evaluations and
`k_ε + 1 ≤ κ (f(x₀) - f_low)/ε² + 1` gradient evaluations (2.2.9).
The printed objective bound (2.2.8), `i_max κ_SDBA (f(x₀) - f_low)/ε²`, is false: it ignores the
initial evaluation and the first trial point of each iteration (it vanishes when
`t_ini ≤ 2(1-α)/L`). -/
theorem theorem_2_2_2 {f : EuclideanSpace ℝ (Fin n) → ℝ} {flow L α tini ε : ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {i : ℕ → ℕ} (hb : AssumptionBb f flow)
    (hf : AssumptionGL f L) (h : algorithm_2_2_1 f α tini ε x i) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε ∧
      (kε : ℝ) ≤ kappaSDBA L α tini * (f (x 0) - flow) / ε ^ 2 ∧
      (sdbaFunEvalCount i kε : ℝ) ≤
        1 + (⌈Real.logb 2 (L * tini / (2 * (1 - α)))⌉₊ + 1) *
          (kappaSDBA L α tini * (f (x 0) - flow) / ε ^ 2) ∧
      ((kε + 1 : ℕ) : ℝ) ≤ kappaSDBA L α tini * (f (x 0) - flow) / ε ^ 2 + 1 := by
  set tmin := min tini ((1 - α) / L)
  have h1α : 0 < 1 - α := sub_pos.2 h.α_lt_one
  have htmin : 0 < tmin := lt_min h.tini_pos (div_pos h1α hf.pos)
  have hε2 : 0 < ε ^ 2 := pow_pos h.ε_pos 2
  have hc : 0 < α * tmin * ε ^ 2 := by have := h.α_pos; positivity
  obtain ⟨kε, hk, hkle⟩ := exists_isFirstHit_of_sub_ge (φ := fun k => f (x k))
    (test := fun k => ‖gradient f (x k)‖ ≤ ε) hc (fun k hk => by
      have h1 := h.sub_ge hf hk
      have hg : ε ≤ ‖gradient f (x k)‖ := (not_le.1 (hk k le_rfl)).le
      have h2 : ε ^ 2 ≤ ‖gradient f (x k)‖ ^ 2 := pow_le_pow_left₀ h.ε_pos.le hg 2
      have := mul_le_mul_of_nonneg_left h2 (mul_pos h.α_pos htmin).le
      linarith) (fun k => hb (x k))
  have hkε : (kε : ℝ) ≤ kappaSDBA L α tini * (f (x 0) - flow) / ε ^ 2 := by
    rw [kappaSDBA, div_mul_eq_mul_div, one_mul, div_div, le_div_iff₀ (by positivity)]
    simpa [mul_assoc] using hkle
  refine ⟨kε, hk, hkε, ?_, by push_cast; linarith⟩
  -- objective evaluations
  set imax := ⌈Real.logb 2 (L * tini / (2 * (1 - α)))⌉₊
  have hsum : (sdbaFunEvalCount i kε : ℝ) ≤ 1 + (imax + 1) * kε := by
    rw [sdbaFunEvalCount_def]
    push_cast
    have : ∑ j ∈ range kε, ((i j : ℝ) + 1) ≤ ∑ _j ∈ range kε, ((imax : ℝ) + 1) := by
      refine sum_le_sum fun j hj => ?_
      have hj : ∀ l ≤ j, ¬ ‖gradient f (x l)‖ ≤ ε :=
        fun l hl => hk.not_test_of_lt (hl.trans_lt (mem_range.1 hj))
      rw [h.index_eq hj]
      have := (lemma_2_2_1_index hf h.α_lt_one h.tini_pos (x j)).1
      have : (backtrackingIndex f α tini (x j) : ℝ) ≤ imax := by exact_mod_cast this
      linarith
    rw [sum_const, card_range, nsmul_eq_mul] at this
    linarith
  have := mul_le_mul_of_nonneg_left hkε (by positivity : (0 : ℝ) ≤ imax + 1)
  linarith

/-! ### Theorem 2.2.3 -/

/-- The unit vector `e₀` of `ℝ¹` along which the one-dimensional examples are laid out. -/
noncomputable abbrev e₀ : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1

theorem norm_e₀ : ‖e₀‖ = 1 := by simp [e₀]

theorem inner_e₀_smul (c : ℝ) : ⟪e₀, c • e₀⟫ = c := by
  rw [inner_smul_right, real_inner_self_eq_norm_sq, norm_e₀]; ring

/-- A one-dimensional function `G` with `|G| ≤ B` and `L`-Lipschitz `C¹` derivative, lifted to
`ℝ¹` along `e₀`, satisfies f.Bb with `f_low = -B` and f.gL with constant `max L 1`; its gradient
is `G'(⟪e₀, x⟫) e₀`. -/
theorem ridge_assumptions {G : ℝ → ℝ} {L B : ℝ} (hG : ContDiff ℝ 1 G)
    (hGL : ∀ s t, |deriv G s - deriv G t| ≤ L * |s - t|) (hGB : ∀ t, |G t| ≤ B) :
    AssumptionBb (ridge G e₀) (-B) ∧ AssumptionGL (ridge G e₀) (max L 1) ∧
      ∀ y, gradient (ridge G e₀) y = deriv G ⟪e₀, y⟫ • e₀ := by
  have hgrad : ∀ y, gradient (ridge G e₀) y = deriv G ⟪e₀, y⟫ • e₀ :=
    gradient_ridge (hG.differentiable one_ne_zero)
  refine ⟨fun y => by rw [ridge_apply]; linarith [neg_abs_le (G ⟪e₀, y⟫), hGB ⟪e₀, y⟫],
    ⟨contDiff_ridge hG, le_max_right _ _, fun y z => ?_⟩, hgrad⟩
  rw [hgrad, hgrad, ← sub_smul, norm_smul, norm_e₀, mul_one, Real.norm_eq_abs]
  have h1 := hGL ⟪e₀, y⟫ ⟪e₀, z⟫
  have h2 : |⟪e₀, y⟫ - ⟪e₀, z⟫| ≤ ‖y - z‖ := by
    rw [← inner_sub_right]
    exact (abs_real_inner_le_norm _ _).trans (by rw [norm_e₀, one_mul])
  have hL0 : 0 ≤ L := by
    by_contra hneg
    have := (abs_nonneg _).trans (hGL 1 0)
    simp at this
    linarith
  calc |deriv G ⟪e₀, y⟫ - deriv G ⟪e₀, z⟫| ≤ L * |⟪e₀, y⟫ - ⟪e₀, z⟫| := h1
    _ ≤ L * ‖y - z‖ := mul_le_mul_of_nonneg_left h2 hL0
    _ ≤ max L 1 * ‖y - z‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- The data of Theorem 2.2.3 ((2.2.15)–(2.2.19)) with constant step factor `θ`:
`ω_k = ε (k_ε - k)/k_ε`, `x_k = ∑_{j<k} θ (ε + ω_j)` and `f_k = 4θ - ∑_{j<k} θ (ε + ω_j)²`. -/
noncomputable def slowOmega (ε : ℝ) (kε k : ℕ) : ℝ := ε * ((kε : ℝ) - k) / kε

/-- The abscissae of the one-dimensional slow example with constant step factor `θ`. -/
noncomputable def slowX (θ ε : ℝ) (kε k : ℕ) : ℝ := ∑ j ∈ range k, θ * (ε + slowOmega ε kε j)

/-- The function values of the one-dimensional slow example with constant step factor `θ`. -/
noncomputable def slowF (θ ε : ℝ) (kε k : ℕ) : ℝ :=
  4 * θ - ∑ j ∈ range k, θ * (ε + slowOmega ε kε j) ^ 2

theorem slowOmega_self {ε : ℝ} {kε : ℕ} : slowOmega ε kε kε = 0 := by simp [slowOmega]

theorem slowOmega_pos {ε : ℝ} (hε : 0 < ε) {kε k : ℕ} (hk : k < kε) : 0 < slowOmega ε kε k := by
  have : (k : ℝ) < kε := by exact_mod_cast hk
  have : (0 : ℝ) < kε := by have := Nat.zero_le k; exact_mod_cast (Nat.zero_le k).trans_lt hk
  unfold slowOmega
  apply div_pos (mul_pos hε (by linarith)) this

/-- **The slow example for first-order methods** ([cartis2022evaluation], proof of Theorem
2.2.3): for every step factor `θ > 0` there are `L ≥ 1` and `f_low` such that for every
`ε ∈ (0, 1]` with `k_ε ε² = 1` there is `f : ℝ¹ → ℝ` satisfying f.Bb and f.gL whose gradient at
`x_k = slowX θ ε k_ε k • e₀` is `-(ε + ω_k) e₀` and whose value there is `slowF θ ε k_ε k`, for
`k ≤ k_ε`. -/
theorem exists_slow_example {θ : ℝ} (hθ : 0 < θ) :
    ∃ L flow : ℝ, 1 ≤ L ∧ ∀ (ε : ℝ) (kε : ℕ), 0 < ε → ε ≤ 1 → (kε : ℝ) * ε ^ 2 = 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, AssumptionBb f flow ∧ AssumptionGL f L ∧
        ∀ k ≤ kε, f (slowX θ ε kε k • e₀) = slowF θ ε kε k ∧
          gradient f (slowX θ ε kε k • e₀) = -(ε + slowOmega ε kε k) • e₀ := by
  obtain ⟨L, B, -, -, H⟩ := exists_slowFirstOrder_interpolant hθ le_rfl
  refine ⟨max L 1, -B, le_max_right _ _, fun ε kε hε hε1 hkε => ?_⟩
  obtain ⟨G, hG, hGL, hGB, -, hGk⟩ := H ε kε (fun _ => θ) (slowX θ ε kε) (slowF θ ε kε) hε hε1
    hkε (fun _ _ => ⟨le_rfl, le_rfl⟩) (fun k _ => by simp [slowX, slowOmega, sum_range_succ])
    (by simp [slowF]) (fun k _ => by simp [slowF, slowOmega, sum_range_succ]; ring)
  obtain ⟨hb, hgl, hgrad⟩ := ridge_assumptions hG hGL hGB
  refine ⟨ridge G e₀, hb, hgl, fun k hk => ?_⟩
  rw [hgrad, ridge_apply, inner_e₀_smul, (hGk k hk).1, (hGk k hk).2]
  exact ⟨rfl, by simp [slowOmega]⟩

theorem slowX_succ (θ ε : ℝ) (kε k : ℕ) :
    slowX θ ε kε (k + 1) = slowX θ ε kε k + θ * (ε + slowOmega ε kε k) := by
  simp [slowX, sum_range_succ]

theorem slowF_succ (θ ε : ℝ) (kε k : ℕ) :
    slowF θ ε kε (k + 1) = slowF θ ε kε k - θ * (ε + slowOmega ε kε k) ^ 2 := by
  simp [slowF, sum_range_succ]; ring

/-- The gradient norms of the slow example: `‖∇f(x_k)‖ = ε + ω_k`, which exceeds `ε` for
`k < k_ε` and equals `ε` at `k_ε`, so the termination test first holds at `k_ε`. -/
theorem isFirstHit_slow {f : EuclideanSpace ℝ (Fin 1) → ℝ} {θ ε : ℝ} {kε : ℕ} (hε : 0 < ε)
    {x : ℕ → EuclideanSpace ℝ (Fin 1)} (hx : ∀ k ≤ kε, x k = slowX θ ε kε k • e₀)
    (hg : ∀ k ≤ kε, gradient f (slowX θ ε kε k • e₀) = -(ε + slowOmega ε kε k) • e₀) :
    IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε := by
  have hnorm : ∀ k ≤ kε, ‖gradient f (x k)‖ = ε + slowOmega ε kε k := fun k hk => by
    rw [hx k hk, hg k hk, norm_smul, norm_e₀, mul_one, norm_neg, Real.norm_eq_abs, abs_of_nonneg]
    have : (k : ℝ) ≤ kε := by exact_mod_cast hk
    have : 0 ≤ slowOmega ε kε k := by
      unfold slowOmega; positivity
    linarith
  refine ⟨by simp only; rw [hnorm kε le_rfl, slowOmega_self, add_zero], fun j hj => ?_⟩
  simp only
  rw [hnorm j hj.le, not_le]
  linarith [slowOmega_pos hε hj]

/-- **Theorem 2.2.3** of [cartis2022evaluation] (sharpness of SDBA). For every `t_ini > 0` there
are `L ≥ 1` and `f_low` (depending only on `t_ini`) such that for all `α ∈ (0,1)` and every
`ε ∈ (0,1]` with `k_ε = ε⁻²` an integer, there is `f : ℝ¹ → ℝ` satisfying f.Bb and f.gL for which
SDBA from `x₀ = 0` runs (a run exists) and every run never backtracks before iteration `k_ε`,
terminates exactly at `k_ε`, and so uses `k_ε + 1` evaluations of `f` and of `∇f`. (The book's
hypothesis `t_ini ≥ α` is not needed.) -/
theorem theorem_2_2_3 {tini : ℝ} (htini : 0 < tini) :
    ∃ L flow : ℝ, 1 ≤ L ∧ ∀ α : ℝ, 0 < α → α < 1 → ∀ (ε : ℝ) (kε : ℕ), 0 < ε → ε ≤ 1 →
      (kε : ℝ) * ε ^ 2 = 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, AssumptionBb f flow ∧ AssumptionGL f L ∧
        (∃ x i, x 0 = 0 ∧ algorithm_2_2_1 f α tini ε x i) ∧
        ∀ x i, x 0 = 0 → algorithm_2_2_1 f α tini ε x i →
          (∀ k < kε, i k = 0) ∧ IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε ∧
            sdbaFunEvalCount i kε = kε + 1 := by
  obtain ⟨L, flow, hL, H⟩ := exists_slow_example htini
  refine ⟨L, flow, hL, fun α hα0 hα1 ε kε hε hε1 hkε => ?_⟩
  obtain ⟨f, hb, hgl, hfk⟩ := H ε kε hε hε1 hkε
  set x : ℕ → EuclideanSpace ℝ (Fin 1) := fun k => slowX tini ε kε k • e₀
  have hhit : IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε :=
    isFirstHit_slow hε (fun _ _ => rfl) fun k hk => (hfk k hk).2
  -- the constructed run never backtracks
  have hbefore : ∀ k, (∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε) → k < kε := fun k hk =>
    not_le.1 fun hle => hk kε hle hhit.test
  have hstep : ∀ k < kε, x (k + 1) = x k - (tini * 2⁻¹ ^ 0) • gradient f (x k) := fun k hk => by
    simp only [x, pow_zero, mul_one]
    rw [(hfk k hk.le).2, slowX_succ]
    module
  have hrun : algorithm_2_2_1 f α tini ε x fun _ => 0 := by
    refine ⟨htini, hα0, hα1, hε, fun k hk => ?_, fun k _ j hj => absurd hj (Nat.not_lt_zero _),
      fun k hk => hstep k (hbefore k hk)⟩
    have hk := hbefore k hk
    change f (x k - (tini * 2⁻¹ ^ 0) • gradient f (x k)) ≤
      f (x k) - α * (tini * 2⁻¹ ^ 0) * ‖gradient f (x k)‖ ^ 2
    rw [← hstep k hk]
    simp only [x]
    rw [(hfk (k + 1) hk).1, (hfk k hk.le).1, (hfk k hk.le).2, slowF_succ, norm_smul, norm_neg,
      norm_e₀, mul_one, Real.norm_eq_abs, sq_abs, pow_zero, mul_one]
    have : 0 ≤ tini * (ε + slowOmega ε kε k) ^ 2 := by positivity
    nlinarith
  refine ⟨f, hb, hgl, ⟨x, _, by simp [x, slowX], hrun⟩, fun x' i' hx0 h' => ?_⟩
  obtain ⟨hx, hi⟩ := hrun.eq_of_eq h' (by rw [hx0]; simp [x, slowX]) hhit.2 kε le_rfl
  refine ⟨hi, ?_, sdbaFunEvalCount_of_forall_eq_zero hi⟩
  exact ⟨by simp only; rw [hx kε le_rfl]; exact hhit.test,
    fun j hj => by simp only; rw [hx j hj.le]; exact hhit.not_test_of_lt hj⟩

/-! ### The exact linesearch (SDEX) and Theorem 2.2.4 -/

section SDEX

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- The SDEX algorithm of [cartis2022evaluation] (§2.2.3.4, steepest descent with the exact
linesearch (2.2.26)), as a run predicate: `ε > 0` and, at every iteration `k` before the
termination test `‖∇f(x_k)‖ ≤ ε` first holds, `t_k` is the first global minimizer of
`t ↦ f(x_k - t∇f(x_k))` on `t ≥ 0` (`LineSearch.IsExactLineMin`) and
`x_{k+1} = x_k - t_k ∇f(x_k)`. -/
structure IsSDEXRun (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (t : ℕ → ℝ) : Prop where
  /-- The accuracy level is positive. -/
  ε_pos : 0 < ε
  /-- The exact linesearch (2.2.26). -/
  exact : UntilHit (fun k => ‖gradient f (x k)‖ ≤ ε) fun k => IsExactLineMin f (x k) (t k)
  /-- The new iterate. -/
  step : UntilHit (fun k => ‖gradient f (x k)‖ ≤ ε) fun k =>
    x (k + 1) = x k - t k • gradient f (x k)

/-- **Existence of SDEX runs**: if `f` is continuous and its sublevel set at `x₀` is bounded, an
SDEX run from `x₀` exists. -/
theorem IsSDEXRun.exists (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hbdd : Bornology.IsBounded {y | f y ≤ f x₀}) :
    ∃ x t, x 0 = x₀ ∧ IsSDEXRun f ε x t := by
  classical
  let T : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    if h : Bornology.IsBounded {z | f z ≤ f y} then (exists_isExactLineMin hf h).choose else 0
  have hT : ∀ y, Bornology.IsBounded {z | f z ≤ f y} → IsExactLineMin f y (T y) := fun y h => by
    simp only [T, h, dite_true]
    exact (exists_isExactLineMin hf h).choose_spec
  let x : ℕ → EuclideanSpace ℝ (Fin n) := fun k =>
    Nat.rec x₀ (fun _ y => y - T y • gradient f y) k
  have hle : ∀ k, f (x k) ≤ f x₀ := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      have hb : Bornology.IsBounded {z | f z ≤ f (x k)} :=
        hbdd.subset fun z hz => (show f z ≤ f (x k) from hz).trans ih
      have := (hT (x k) hb).1.2 0 le_rfl
      simp only [zero_smul, sub_zero] at this
      exact this.trans ih
  refine ⟨x, fun k => T (x k), rfl, hε, fun k _ => hT _ ?_, fun k _ => rfl⟩
  exact hbdd.subset fun z hz => (show f z ≤ f (x k) from hz).trans (hle k)

/-- **Theorem 2.2.4** of [cartis2022evaluation]. Under f.Bb and f.gL, every SDEX run terminates at
an iteration `k_ε ≤ κ_SDEX (f(x₀) - f_low)/ε²` with `κ_SDEX = 2 L_{f,1}` (2.2.27) (a bound on
iterations, not on evaluations). -/
theorem theorem_2_2_4 {flow L ε : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)} {t : ℕ → ℝ}
    (hb : AssumptionBb f flow) (hf : AssumptionGL f L) (h : IsSDEXRun f ε x t) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε ∧
      (kε : ℝ) ≤ 2 * L * (f (x 0) - flow) / ε ^ 2 := by
  have hε2 : 0 < ε ^ 2 := pow_pos h.ε_pos 2
  have hL := hf.pos
  obtain ⟨kε, hk, hkle⟩ := exists_isFirstHit_of_sub_ge (φ := fun k => f (x k))
    (test := fun k => ‖gradient f (x k)‖ ≤ ε) (c := ε ^ 2 / (2 * L)) (by positivity)
    (fun k hk => by
      have hg : ε < ‖gradient f (x k)‖ := not_le.1 (hk k le_rfl)
      have hne : gradient f (x k) ≠ 0 := norm_pos_iff.1 (h.ε_pos.trans hg)
      have hdec := (decrease_ge_of_exactLineMin hf.differentiable hf.lipschitz hL hne
        (Or.inl (h.exact k hk).isGlobalLineMin)).2
      rw [← h.step k hk] at hdec
      have : ε ^ 2 ≤ ‖gradient f (x k)‖ ^ 2 := pow_le_pow_left₀ h.ε_pos.le hg.le 2
      have : ε ^ 2 / (2 * L) ≤ ‖gradient f (x k)‖ ^ 2 / (2 * L) :=
        div_le_div_of_nonneg_right this (by positivity)
      linarith) (fun k => hb (x k))
  refine ⟨kε, hk, ?_⟩
  rw [le_div_iff₀ hε2]
  have : (kε : ℝ) * (ε ^ 2 / (2 * L)) * (2 * L) ≤ (f (x 0) - flow) * (2 * L) :=
    mul_le_mul_of_nonneg_right hkle (by positivity)
  field_simp at this
  linarith

/-- **Theorem 2.2.5** of [cartis2022evaluation] (sharpness of SDEX). There are `L ≥ 1` and `f_low`
such that for every `ε > 0` with `k_ε = ε⁻²` an integer there is `f : ℝ² → ℝ` satisfying f.Bb and
f.gL for which SDEX (with the exact linesearch (2.2.26)) from `x₀ = 0` runs, and every such run
(SDEX is deterministic, the first global line minimizer being unique) takes the steps `t_k = √2`
and terminates exactly at iteration `k_ε`. The function is the zig-zag example
`Optimization.zigZagFunction ε k_ε` of Appendix B (Lemmas B.2.2–B.2.6). -/
theorem theorem_2_2_5 :
    ∃ L flow : ℝ, 1 ≤ L ∧ ∀ (ε : ℝ) (kε : ℕ), 0 < ε → (kε : ℝ) * ε ^ 2 = 1 →
      ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ, AssumptionBb f flow ∧ AssumptionGL f L ∧
        (∃ x t, x 0 = 0 ∧ IsSDEXRun f ε x t) ∧
        ∀ x t, x 0 = 0 → IsSDEXRun f ε x t →
          (∀ k < kε, t k = √2) ∧ IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε) kε := by
  obtain ⟨M, L, -, hL, H⟩ := zigZag_bounds
  refine ⟨L, -M, hL, fun ε kε hε hkε => ?_⟩
  have hadm : ZigZag.IsAdmissible ε kε := ⟨hε, hkε⟩
  obtain ⟨hC, hlow, hlip⟩ := H ε kε hadm
  set f := zigZagFunction ε kε
  set z : ℕ → EuclideanSpace ℝ (Fin 2) := zigZagIterate ε kε
  have hz0 : z 0 = 0 := by
    ext i; fin_cases i <;> simp [z, zigZagIterate, ZigZag.height]
  have hnorm : ∀ k ≤ kε, ‖gradient f (z k)‖ = ε + ZigZag.omega ε kε k :=
    fun k hk => (zigZag_gradient hadm hk).2.1
  have hhit : IsFirstHit (fun k => ‖gradient f (z k)‖ ≤ ε) kε := by
    refine ⟨by simp only; rw [hnorm kε le_rfl, ZigZag.omega_self, add_zero], fun j hj => ?_⟩
    simp only
    rw [hnorm j hj.le, not_le]
    linarith [hadm.omega_pos hj]
  have hbefore : ∀ k, (∀ j ≤ k, ¬ ‖gradient f (z j)‖ ≤ ε) → k < kε := fun k hk =>
    not_le.1 fun hle => hk kε hle hhit.test
  have hrun : IsSDEXRun f ε z fun _ => √2 :=
    ⟨hε, fun k hk => zigZag_isExactLineMin hadm (hbefore k hk),
      fun k hk => (zigZag_gradient hadm (hbefore k hk).le).2.2⟩
  refine ⟨f, hlow, ⟨hC, hL, hlip⟩, ⟨z, _, hz0, hrun⟩, fun x t hx0 h => ?_⟩
  -- every run follows the zig-zag iterates
  have heq : ∀ k ≤ kε, (∀ j ≤ k, x j = z j) ∧ ∀ j < k, t j = √2 := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun j hj => by rw [Nat.le_zero.1 hj, hx0, hz0],
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨hx, ht⟩ := ih (Nat.le_of_succ_le hk)
      have hstop : ∀ j ≤ k, ¬ ‖gradient f (x j)‖ ≤ ε := fun j hj => by
        rw [hx j hj]; exact hhit.not_test_of_lt (by omega)
      have htk : t k = √2 := by
        have h1 : IsExactLineMin f (x k) (t k) := h.exact k hstop
        rw [hx k le_rfl] at h1
        exact h1.unique (zigZag_isExactLineMin hadm (by omega))
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · rcases Nat.lt_or_eq_of_le hj with hj | rfl
        · exact hx j (Nat.lt_succ_iff.1 hj)
        · rw [h.step k hstop, hx k le_rfl, htk]
          exact ((zigZag_gradient hadm (k := k) (by omega)).2.2).symm
      · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hj) with hj | rfl
        · exact ht j hj
        · exact htk
  obtain ⟨hx, ht⟩ := heq kε le_rfl
  exact ⟨ht, ⟨by simp only; rw [hx kε le_rfl]; exact hhit.test,
    fun j hj => by simp only; rw [hx j hj.le]; exact hhit.not_test_of_lt hj⟩⟩

end SDEX

end CartisGouldToint.Chapter02
