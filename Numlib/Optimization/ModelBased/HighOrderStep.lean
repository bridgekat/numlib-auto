import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Logic.Relation
import Numlib.Analysis.SpecialFunctions.FactorialSum

/-!
# The step computation of high-order adaptive-regularization methods

The adaptive-regularization methods ARqp ([cartis2022evaluation], Algorithm 12.2.2) and ARqpC
(Algorithm 14.1.1) compute, at every iteration, a step `s_k` approximately minimizing the model
`m_k` together with radii `δ_{s_k} ∈ (0, 1]^q` for which `s_k` is approximately `q`-th order
critical for the model. The *detailed Step 2* that does so (Algorithms 12.2.3 and 14.1.2) is
stated here once, for abstract data:

* `m : E → ℝ` (the model), `T : Set E` (the feasible steps), `Sd s : Set E` (the feasible
  displacements at a trial step `s`), `ΔT j s d` (the order-`j` Taylor decrement of the model at
  `s`), the order `q`, constants `ς, θ`, tolerances `ε j`, and `J : Set ℕ`, the orders at which the
  radius may be halved (`j ≥ 3` in Algorithm 12.2.3; `j ≥ 2`, or all `j` if the nonsmooth part is
  nonconvex, in Algorithm 14.1.2).

The order-`j` measure at `s` with radius `δ` is `sSup (ΔT j s '' (closedBall 0 δ ∩ Sd s))`.

The global minimal value `m* = sInf (m '' T)` of Step 2.2 is meaningful when `m` is bounded below
on `T` (as the regularized models are); otherwise Lean's `sInf` of an unbounded set is `0`, and
the results below still hold but say nothing about global minimization. The long-step test of
Step 2.3 is `‖s‖ ≥ 1` as in Algorithms 12.2.3 and 14.1.2, whereas the Step-2 condition (12.2.28)
of the outer algorithm is printed with `‖s_k‖ > 1`; the two differ only on the sphere `‖s‖ = 1`,
where the short-step conditions are not checked.

The procedure chooses an approximate global minimizer `s_μ` (Step 2.2) and approximate maximizers
`d_{μ,j}` (Step 2.4.1); it is modelled as a nondeterministic transition system
(`Optimization.DetailedStepTrans` on `Optimization.DetailedStepState`), and its outputs
(`Optimization.IsDetailedStepOutput`) are the returned states reachable from an initial state.

* `Optimization.IsDetailedStepOutput.spec`: every output satisfies the Step-2 conditions
  (12.2.27)–(12.2.29) / (14.1.12)–(14.1.13);
* `Optimization.exists_isDetailedStepOutput`: from a global minimizer of the model there is an
  output whose radii are bounded below (Lemmas 12.2.9 and 14.1.3);
* `Optimization.IsDetailedStepOutput.radius_ge`: every output has radii at least `δbar j / 2`
  when the model-decrease property of Lemmas 12.2.8/14.1.2 holds at all short trial steps.

The second part is the step-length algebra shared by Lemmas 12.2.12, 13.1.17 and 14.1.8: if the
measure inequality `a ε δ^j / j! ≤ A ∑_{ℓ=1}^j δ^ℓ/ℓ! t^{p-ℓ+1} + B t^{p+1}` holds for the step
length `t = ‖s_k‖`, then `t` is bounded below (`Optimization.pow_ge_of_measure_ineq`,
`Optimization.norm_step_ge_of_measure_ineq`).
-/

open Finset Metric
open scoped Nat

namespace Optimization

/-! ### The detailed Step 2 -/

/-- The states of the detailed Step 2 ([cartis2022evaluation], Algorithms 12.2.3, 14.1.2). -/
inductive DetailedStepState (E : Type*)
  /-- About to execute Step 2.2 with parameter `μ` and radii `δ`. -/
  | findStep (μ : ℝ) (δ : ℕ → ℝ)
  /-- In Step 2.4 at order `j`, with parameter `μ`, trial step `s` and radii `δ`. -/
  | check (μ : ℝ) (s : E) (δ : ℕ → ℝ) (j : ℕ)
  /-- The pair `(s_k, δ_{s_k}) = (s, δ)` has been returned (Steps 2.3, 2.5). -/
  | done (s : E) (δ : ℕ → ℝ)

open DetailedStepState

variable {E : Type*} [NormedAddCommGroup E]

/-- One transition of the detailed Step 2 ([cartis2022evaluation], Algorithm 12.2.3 for `J` the
orders `j ≥ 3`, Algorithm 14.1.2 for `j ≥ 2` or all orders), with `m* = sInf (m '' T)` the global
minimal value of the model and `φ j s δ = sSup (ΔT j s '' (closedBall 0 δ ∩ Sd s))` the order-`j`
measure at `s`:
* Steps 2.2–2.3: a step `s ∈ T` with `μ (m 0 - m*) ≤ m 0 - m s` is returned if `‖s‖ ≥ 1`, and
  checked from order `1` otherwise;
* Steps 2.4.1–2.4.2: a displacement `d` of norm at most `δ_j` with `ς φ j s δ_j ≤ ΔT j s d` and
  `ΔT j s d ≤ ς θ ε_j δ_j^j / j!` passes order `j` (to order `j + 1`, or returning `(s, δ)` after
  order `q`);
* Step 2.4.3: if the decrement is too large, `j ∈ J` and the model decrease
  `m s - m (s + d)` is smaller than `ς θ ε_j δ_j^j / (2 j!)`, the radius `δ_j` is halved;
* Step 2.4.4: otherwise `μ` is replaced by `(1 + μ) / 2` and a new step is computed. -/
inductive DetailedStepTrans (m : E → ℝ) (T : Set E) (Sd : E → Set E) (ΔT : ℕ → E → E → ℝ)
    (q : ℕ) (ς θ : ℝ) (ε : ℕ → ℝ) (J : Set ℕ) :
    DetailedStepState E → DetailedStepState E → Prop
  /-- Step 2.3: return a long step. -/
  | ret {μ : ℝ} {δ : ℕ → ℝ} {s : E} (hs : s ∈ T) (hdec : μ * (m 0 - sInf (m '' T)) ≤ m 0 - m s)
      (hlong : 1 ≤ ‖s‖) :
      DetailedStepTrans m T Sd ΔT q ς θ ε J (findStep μ δ) (done s δ)
  /-- Step 2.3: check a short step, starting from order `1`. -/
  | start {μ : ℝ} {δ : ℕ → ℝ} {s : E} (hs : s ∈ T)
      (hdec : μ * (m 0 - sInf (m '' T)) ≤ m 0 - m s) (hshort : ‖s‖ < 1) :
      DetailedStepTrans m T Sd ΔT q ς θ ε J (findStep μ δ) (check μ s δ 1)
  /-- Step 2.4.2: order `j < q` passes, consider the next order. -/
  | next {μ : ℝ} {s : E} {δ : ℕ → ℝ} {j : ℕ} {d : E} (hd : d ∈ closedBall 0 (δ j) ∩ Sd s)
      (happrox : ς * sSup (ΔT j s '' (closedBall 0 (δ j) ∩ Sd s)) ≤ ΔT j s d)
      (hsmall : ΔT j s d ≤ ς * θ * ε j * δ j ^ j / j !) (hj : j < q) :
      DetailedStepTrans m T Sd ΔT q ς θ ε J (check μ s δ j) (check μ s δ (j + 1))
  /-- Steps 2.4.2 and 2.5: the last order passes, return `(s, δ)`. -/
  | finish {μ : ℝ} {s : E} {δ : ℕ → ℝ} {j : ℕ} {d : E} (hd : d ∈ closedBall 0 (δ j) ∩ Sd s)
      (happrox : ς * sSup (ΔT j s '' (closedBall 0 (δ j) ∩ Sd s)) ≤ ΔT j s d)
      (hsmall : ΔT j s d ≤ ς * θ * ε j * δ j ^ j / j !) (hj : q ≤ j) :
      DetailedStepTrans m T Sd ΔT q ς θ ε J (check μ s δ j) (done s δ)
  /-- Step 2.4.3: halve the radius of order `j`. -/
  | halve {μ : ℝ} {s : E} {δ : ℕ → ℝ} {j : ℕ} {d : E} (hd : d ∈ closedBall 0 (δ j) ∩ Sd s)
      (happrox : ς * sSup (ΔT j s '' (closedBall 0 (δ j) ∩ Sd s)) ≤ ΔT j s d)
      (hlarge : ς * θ * ε j * δ j ^ j / j ! < ΔT j s d) (hJ : j ∈ J)
      (hmodel : m s - m (s + d) < ς * θ * ε j * δ j ^ j / (2 * j !)) :
      DetailedStepTrans m T Sd ΔT q ς θ ε J (check μ s δ j)
        (check μ s (Function.update δ j (δ j / 2)) j)
  /-- Step 2.4.4: increase `μ` and compute a new step. -/
  | restart {μ : ℝ} {s : E} {δ : ℕ → ℝ} {j : ℕ} {d : E} (hd : d ∈ closedBall 0 (δ j) ∩ Sd s)
      (happrox : ς * sSup (ΔT j s '' (closedBall 0 (δ j) ∩ Sd s)) ≤ ΔT j s d)
      (hlarge : ς * θ * ε j * δ j ^ j / j ! < ΔT j s d)
      (hJ : j ∉ J ∨ ς * θ * ε j * δ j ^ j / (2 * j !) ≤ m s - m (s + d)) :
      DetailedStepTrans m T Sd ΔT q ς θ ε J (check μ s δ j) (findStep ((1 + μ) / 2) δ)

/-- `(s, δs)` is an output of the detailed Step 2: it is returned by some execution of the
procedure started (Step 2.1) with some `μ₀ ∈ (0, 1]` and all radii equal to `1`. -/
def IsDetailedStepOutput (m : E → ℝ) (T : Set E) (Sd : E → Set E) (ΔT : ℕ → E → E → ℝ)
    (q : ℕ) (ς θ : ℝ) (ε : ℕ → ℝ) (J : Set ℕ) (s : E) (δs : ℕ → ℝ) : Prop :=
  ∃ μ₀ ∈ Set.Ioc (0 : ℝ) 1,
    Relation.ReflTransGen (DetailedStepTrans m T Sd ΔT q ς θ ε J) (findStep μ₀ fun _ => 1)
      (done s δs)

section DetailedStep

variable {m : E → ℝ} {T : Set E} {Sd : E → Set E} {ΔT : ℕ → E → E → ℝ} {q : ℕ} {ς θ : ℝ}
  {ε : ℕ → ℝ} {J : Set ℕ}

/-- The radii stay in `(0, 1]`, and equal to `1` at the orders that are never halved. -/
private def RadiiOK (J : Set ℕ) (δ : ℕ → ℝ) : Prop :=
  ∀ i, 0 < δ i ∧ δ i ≤ 1 ∧ (i ∉ J → δ i = 1)

/-- The order-`i` conditions (12.2.29) at the step `s` with radius `δ i`. -/
private def OrderOK (Sd : E → Set E) (ΔT : ℕ → E → E → ℝ) (ς θ : ℝ) (ε : ℕ → ℝ) (s : E)
    (δ : ℕ → ℝ) (i : ℕ) : Prop :=
  ∃ d ∈ closedBall 0 (δ i) ∩ Sd s,
    ς * sSup (ΔT i s '' (closedBall 0 (δ i) ∩ Sd s)) ≤ ΔT i s d ∧
      ΔT i s d ≤ ς * θ * ε i * δ i ^ i / i !

/-- The invariant of the detailed Step 2. -/
private def StepInv (m : E → ℝ) (T : Set E) (Sd : E → Set E) (ΔT : ℕ → E → E → ℝ) (q : ℕ)
    (ς θ : ℝ) (ε : ℕ → ℝ) (J : Set ℕ) : DetailedStepState E → Prop
  | findStep μ δ => μ ∈ Set.Ioc (0 : ℝ) 1 ∧ RadiiOK J δ
  | check μ s δ j => μ ∈ Set.Ioc (0 : ℝ) 1 ∧ RadiiOK J δ ∧ s ∈ T ∧
      μ * (m 0 - sInf (m '' T)) ≤ m 0 - m s ∧ ‖s‖ < 1 ∧
      ∀ i, 1 ≤ i → i < j → OrderOK Sd ΔT ς θ ε s δ i
  | done s δ => RadiiOK J δ ∧ s ∈ T ∧
      (∃ μ ∈ Set.Ioc (0 : ℝ) 1, μ * (m 0 - sInf (m '' T)) ≤ m 0 - m s) ∧
      (1 ≤ ‖s‖ ∨ ∀ i ∈ Icc 1 q, OrderOK Sd ΔT ς θ ε s δ i)

private theorem stepInv_trans {a b : DetailedStepState E}
    (h : DetailedStepTrans m T Sd ΔT q ς θ ε J a b) (ha : StepInv m T Sd ΔT q ς θ ε J a) :
    StepInv m T Sd ΔT q ς θ ε J b := by
  cases h with
  | ret hs hdec hlong => exact ⟨ha.2, hs, ⟨_, ha.1, hdec⟩, Or.inl hlong⟩
  | start hs hdec hshort =>
    exact ⟨ha.1, ha.2, hs, hdec, hshort, fun i hi hi1 => absurd hi (by omega)⟩
  | next hd happrox hsmall hj =>
    obtain ⟨hμ, hR, hs, hdec, hshort, hord⟩ := ha
    refine ⟨hμ, hR, hs, hdec, hshort, fun i hi hij => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | rfl
    · exact hord i hi hlt
    · exact ⟨_, hd, happrox, hsmall⟩
  | @finish μ s δ j d hd happrox hsmall hj =>
    obtain ⟨hμ, hR, hs, hdec, hshort, hord⟩ := ha
    refine ⟨hR, hs, ⟨μ, hμ, hdec⟩, Or.inr fun i hi => ?_⟩
    obtain ⟨hi1, hiq⟩ := mem_Icc.1 hi
    rcases (hiq.trans hj).lt_or_eq with hlt | rfl
    · exact hord i hi1 hlt
    · exact ⟨_, hd, happrox, hsmall⟩
  | @halve μ s δ j d hd happrox hlarge hJ hmodel =>
    obtain ⟨hμ, hR, hs, hdec, hshort, hord⟩ := ha
    refine ⟨hμ, fun i => ?_, hs, hdec, hshort, fun i hi hij => ?_⟩
    · rcases eq_or_ne i j with rfl | hij
      · obtain ⟨h0, h1, -⟩ := hR i
        simp only [Function.update_self]
        exact ⟨by linarith, by linarith, fun h => absurd hJ h⟩
      · simp only [Function.update_of_ne hij]
        exact hR i
    · have hne : i ≠ j := hij.ne
      simpa only [OrderOK, Function.update_of_ne hne] using hord i hi hij
  | restart hd happrox hlarge hJ =>
    obtain ⟨hμ, hR, -⟩ := ha
    obtain ⟨h0, h1⟩ := hμ
    exact ⟨⟨by linarith, by linarith⟩, hR⟩

/-- **The outputs of the detailed Step 2 satisfy the Step-2 conditions** ([cartis2022evaluation],
(12.2.27)–(12.2.29), (14.1.12)–(14.1.13)). If `(s, δs)` is an output, then `s ∈ T`;
`μ (m 0 - m*) ≤ m 0 - m s` for some `μ ∈ (0, 1]`, with `m* = sInf (m '' T)`; the radii lie in
`(0, 1]` and equal `1` at every order outside `J`; and either `‖s‖ ≥ 1`, or for every
`j ∈ [1, q]` some displacement `d` of norm at most `δs j` (feasible at `s`) satisfies
`ς φ j s (δs j) ≤ ΔT j s d ≤ ς θ ε_j δs_j^j / j!`.

(When the step is long, the radii are those current at Step 2.3, which may differ from `1`; the
outer algorithm is free to replace them, as in (12.2.28).) -/
theorem IsDetailedStepOutput.spec {s : E} {δs : ℕ → ℝ}
    (h : IsDetailedStepOutput m T Sd ΔT q ς θ ε J s δs) :
    s ∈ T ∧ (∃ μ ∈ Set.Ioc (0 : ℝ) 1, μ * (m 0 - sInf (m '' T)) ≤ m 0 - m s) ∧
      (∀ j, 0 < δs j ∧ δs j ≤ 1) ∧ (∀ j ∉ J, δs j = 1) ∧
      (1 ≤ ‖s‖ ∨ ∀ j ∈ Icc 1 q, ∃ d ∈ closedBall 0 (δs j) ∩ Sd s,
        ς * sSup (ΔT j s '' (closedBall 0 (δs j) ∩ Sd s)) ≤ ΔT j s d ∧
          ΔT j s d ≤ ς * θ * ε j * δs j ^ j / j !) := by
  obtain ⟨μ₀, hμ₀, hrun⟩ := h
  have hinv : StepInv m T Sd ΔT q ς θ ε J (done s δs) := by
    refine Relation.ReflTransGen.rec (motive := fun b _ => StepInv m T Sd ΔT q ς θ ε J b)
      ?_ (fun _ hbc ih => stepInv_trans hbc ih) hrun
    exact ⟨hμ₀, fun _ => ⟨one_pos, le_rfl, fun _ => rfl⟩⟩
  obtain ⟨hR, hs, hμ, hord⟩ := hinv
  exact ⟨hs, hμ, fun j => ⟨(hR j).1, (hR j).2.1⟩, fun j hj => (hR j).2.2 hj, hord⟩

/-- An output never increases the model when `0 ∈ T` and the model is bounded below on `T`. -/
theorem IsDetailedStepOutput.le_of_bddBelow {s : E} {δs : ℕ → ℝ}
    (h : IsDetailedStepOutput m T Sd ΔT q ς θ ε J s δs) (h0 : (0 : E) ∈ T)
    (hb : BddBelow (m '' T)) : m s ≤ m 0 := by
  obtain ⟨-, ⟨μ, hμ, hdec⟩, -⟩ := h.spec
  have : sInf (m '' T) ≤ m 0 := csInf_le hb ⟨0, h0, rfl⟩
  nlinarith [hμ.1]

/-- If an output does not decrease the model (the termination test of Step 2 of ARqp), then `0`
is a global minimizer of the model on `T` (given boundedness below). -/
theorem IsDetailedStepOutput.isMinOn_of_eq {s : E} {δs : ℕ → ℝ}
    (h : IsDetailedStepOutput m T Sd ΔT q ς θ ε J s δs)
    (hb : BddBelow (m '' T)) (heq : m s = m 0) : IsMinOn m T 0 := by
  obtain ⟨-, ⟨μ, hμ, hdec⟩, -⟩ := h.spec
  rw [heq, sub_self] at hdec
  have hle : m 0 ≤ sInf (m '' T) := by
    by_contra hlt
    push Not at hlt
    nlinarith [hμ.1]
  intro t ht
  exact hle.trans (csInf_le hb ⟨t, ht, rfl⟩)

/-- The invariant behind `IsDetailedStepOutput.radius_ge`: positive radii, bounded below by
`δbar j / 2` at the halved orders `j ∈ J ∩ [1, q]`, and short feasible trial steps and orders in
`[1, q]` while checking. -/
private def RadiusLB (T : Set E) (q : ℕ) (J : Set ℕ) (δbar : ℕ → ℝ) :
    DetailedStepState E → Prop
  | findStep _ δ => ∀ j, 0 < δ j ∧ (j ∈ J → j ∈ Icc 1 q → δbar j / 2 ≤ δ j)
  | check _ s δ i => (∀ j, 0 < δ j ∧ (j ∈ J → j ∈ Icc 1 q → δbar j / 2 ≤ δ j)) ∧ s ∈ T ∧
      ‖s‖ < 1 ∧ i ∈ Icc 1 q
  | done _ δ => ∀ j, 0 < δ j ∧ (j ∈ J → j ∈ Icc 1 q → δbar j / 2 ≤ δ j)

/-- **Lower bound on the radii of every output** of the detailed Step 2 (the argument of
[cartis2022evaluation], Lemmas 12.2.9 and 14.1.3, for all executions): let `1 ≤ q`, let
`δbar j ≤ 1` at the halved orders `j ∈ J ∩ [1, q]`, and suppose that at every short feasible trial
step `s` a decrement `ΔT j s d ≥ ς θ ε_j δ^j/j!` with `0 < δ ≤ δbar j` forces the model decrease
`m s - m (s + d) ≥ ς θ ε_j δ^j/(2 j!)` (Lemmas 12.2.8, 14.1.2). Then the radius `δ_j` is never
halved below `δbar j / 2`: every output has `δs j ≥ δbar j / 2` for `j ∈ J ∩ [1, q]`. -/
theorem IsDetailedStepOutput.radius_ge {s : E} {δs : ℕ → ℝ} {δbar : ℕ → ℝ}
    (h : IsDetailedStepOutput m T Sd ΔT q ς θ ε J s δs) (hq : 1 ≤ q)
    (hδbar : ∀ j ∈ J, j ∈ Icc 1 q → δbar j ≤ 1)
    (hgood : ∀ s ∈ T, ‖s‖ < 1 → ∀ j ∈ J, j ∈ Icc 1 q → ∀ δ ∈ Set.Ioc (0 : ℝ) (δbar j),
      ∀ d ∈ closedBall 0 δ ∩ Sd s, ς * θ * ε j * δ ^ j / j ! ≤ ΔT j s d →
        ς * θ * ε j * δ ^ j / (2 * j !) ≤ m s - m (s + d)) :
    ∀ j ∈ J, j ∈ Icc 1 q → δbar j / 2 ≤ δs j := by
  obtain ⟨μ₀, -, hrun⟩ := h
  have hinv : RadiusLB T q J δbar (done s δs) := by
    refine Relation.ReflTransGen.rec (motive := fun b _ => RadiusLB T q J δbar b)
      ?_ (fun _ hbc ih => ?_) hrun
    · exact fun j => ⟨one_pos, fun hj hjq => by linarith [hδbar j hj hjq]⟩
    cases hbc with
    | ret hs hdec hlong => exact ih
    | start hs hdec hshort => exact ⟨ih, hs, hshort, mem_Icc.2 ⟨le_rfl, hq⟩⟩
    | next hd happrox hsmall hj =>
      obtain ⟨hR, hs', hshort, hjq⟩ := ih
      exact ⟨hR, hs', hshort, mem_Icc.2 ⟨by have := (mem_Icc.1 hjq).1; omega, hj⟩⟩
    | finish hd happrox hsmall hj => exact ih.1
    | @halve μ s' δ j d hd happrox hlarge hJ hmodel =>
      obtain ⟨hR, hs', hshort, hjq⟩ := ih
      refine ⟨fun i => ?_, hs', hshort, hjq⟩
      rcases eq_or_ne i j with rfl | hij
      · simp only [Function.update_self]
        have hpos := (hR i).1
        have hgt : δbar i < δ i := by
          by_contra hle
          push Not at hle
          have := hgood s' hs' hshort i hJ hjq (δ i) ⟨hpos, hle⟩ d hd hlarge.le
          linarith
        exact ⟨by linarith, fun _ _ => by linarith⟩
      · simp only [Function.update_of_ne hij]
        exact hR i
    | restart hd happrox hlarge hJ => exact ih.1
  exact fun j hj hjq => (hinv j).2 hj hjq

/-- The supremum of `f` over `S` is attained at a maximizer `d ∈ S`. -/
private theorem sSup_image_eq_of_max {α : Type*} {f : α → ℝ} {S : Set α} {d : α} (hd : d ∈ S)
    (hmax : ∀ d' ∈ S, f d' ≤ f d) : sSup (f '' S) = f d :=
  IsGreatest.csSup_eq ⟨⟨d, hd, rfl⟩, by rintro _ ⟨d', hd', rfl⟩; exact hmax d' hd'⟩

/-- The hypotheses of `Optimization.exists_isDetailedStepOutput` at one order `j`, at a global
minimizer `sstar` of the model. -/
private structure OrderHyp (m : E → ℝ) (T : Set E) (Sd : E → Set E) (ΔT : ℕ → E → E → ℝ)
    (ς θ : ℝ) (ε : ℕ → ℝ) (J : Set ℕ) (sstar : E) (δbar : ℕ → ℝ) (j : ℕ) : Prop where
  min : ∀ t ∈ T, m sstar ≤ m t
  feas : ∀ d ∈ Sd sstar, sstar + d ∈ T
  att : ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ d ∈ closedBall 0 δ ∩ Sd sstar,
    ∀ d' ∈ closedBall 0 δ ∩ Sd sstar, ΔT j sstar d' ≤ ΔT j sstar d
  zero_mem : (0 : E) ∈ Sd sstar
  zero_dec : ΔT j sstar 0 = 0
  pos : 0 < ς * θ * ε j
  ς_le : ς ≤ 1
  notJ : j ∉ J → ∀ d ∈ closedBall 0 1 ∩ Sd sstar, ΔT j sstar d ≤ 0
  δbar_pos : j ∈ J → 0 < δbar j
  good : j ∈ J → ∀ δ ∈ Set.Ioc (0 : ℝ) (δbar j), ∀ d ∈ closedBall 0 δ ∩ Sd sstar,
    ς * θ * ε j * δ ^ j / j ! ≤ ΔT j sstar d →
      ς * θ * ε j * δ ^ j / (2 * j !) ≤ m sstar - m (sstar + d)

/-- One visit of order `j` at the global minimizer `sstar`: either order `j` passes with the
current radii, or `j ∈ J`, `δ j > δbar j` and the radius `δ j` is halved (Step 2.4.3). -/
private theorem pass_or_halve {sstar : E} {δbar : ℕ → ℝ} {j : ℕ}
    (H : OrderHyp m T Sd ΔT ς θ ε J sstar δbar j) {δ : ℕ → ℝ} (hR : RadiiOK J δ) :
    OrderOK Sd ΔT ς θ ε sstar δ j ∨
      (j ∈ J ∧ δbar j < δ j ∧ RadiiOK J (Function.update δ j (δ j / 2)) ∧
        DetailedStepTrans m T Sd ΔT q ς θ ε J (check 1 sstar δ j)
          (check 1 sstar (Function.update δ j (δ j / 2)) j)) := by
  have hfact : (0 : ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
  have hpos := H.pos
  have hδj := pow_pos (hR j).1 j
  obtain ⟨d, hd, hmax⟩ := H.att (δ j) ⟨(hR j).1, (hR j).2.1⟩
  have hφ := sSup_image_eq_of_max hd hmax
  have hnn : 0 ≤ ΔT j sstar d := by
    have := hmax 0 ⟨mem_closedBall_self (hR j).1.le, H.zero_mem⟩
    rwa [H.zero_dec] at this
  have happrox : ς * sSup (ΔT j sstar '' (closedBall 0 (δ j) ∩ Sd sstar)) ≤ ΔT j sstar d := by
    rw [hφ]; exact mul_le_of_le_one_left hnn H.ς_le
  have hbound : 0 < ς * θ * ε j * δ j ^ j / (j ! : ℝ) := by positivity
  by_cases hsmall : ΔT j sstar d ≤ ς * θ * ε j * δ j ^ j / (j ! : ℝ)
  · exact Or.inl ⟨d, hd, happrox, hsmall⟩
  right
  push Not at hsmall
  have hjJ : j ∈ J := by
    by_contra hjJ
    have h1 : δ j = 1 := (hR j).2.2 hjJ
    have := H.notJ hjJ d (by rw [← h1]; exact hd)
    linarith
  have hmodel : m sstar - m (sstar + d) ≤ 0 := by
    linarith [H.min _ (H.feas d hd.2)]
  have hhalf : 0 < ς * θ * ε j * δ j ^ j / (2 * j ! : ℝ) := by positivity
  refine ⟨hjJ, ?_, ?_, DetailedStepTrans.halve hd happrox hsmall hjJ (hmodel.trans_lt hhalf)⟩
  · by_contra hle
    push Not at hle
    have := H.good hjJ (δ j) ⟨(hR j).1, hle⟩ d hd hsmall.le
    linarith
  · intro i
    rcases eq_or_ne i j with rfl | hij
    · obtain ⟨h0, h1, -⟩ := hR i
      simp only [Function.update_self]
      exact ⟨by linarith, by linarith, fun h => absurd hjJ h⟩
    · simp only [Function.update_of_ne hij]
      exact hR i

/-- Halving the radius of order `j` until the order-`j` test passes (proof of Lemma 12.2.9).
Starting from radii satisfying the invariant (with `δbar j / 2 ≤ δ j ≤ 2^n δbar j` if `j ∈ J`),
the procedure at the global minimizer `sstar` reaches radii `δ'` that differ from `δ` only at `j`,
with `δ' j ≥ δbar j / 2` if `j ∈ J`, at which order `j` passes. -/
private theorem exists_pass_of_halving {sstar : E} {δbar : ℕ → ℝ} {j : ℕ}
    (H : OrderHyp m T Sd ΔT ς θ ε J sstar δbar j) (n : ℕ) :
    ∀ δ : ℕ → ℝ, RadiiOK J δ → (j ∈ J → δbar j / 2 ≤ δ j ∧ δ j ≤ 2 ^ n * δbar j) →
      ∃ δ' : ℕ → ℝ, RadiiOK J δ' ∧ (j ∈ J → δbar j / 2 ≤ δ' j) ∧ (∀ i ≠ j, δ' i = δ i) ∧
        Relation.ReflTransGen (DetailedStepTrans m T Sd ΔT q ς θ ε J) (check 1 sstar δ j)
          (check 1 sstar δ' j) ∧ OrderOK Sd ΔT ς θ ε sstar δ' j := by
  induction n with
  | zero =>
    intro δ hR hJδ
    rcases pass_or_halve (q := q) H hR with hpass | ⟨hjJ, hbig, -, -⟩
    · exact ⟨δ, hR, fun hj => (hJδ hj).1, fun _ _ => rfl, Relation.ReflTransGen.refl, hpass⟩
    · have := (hJδ hjJ).2
      rw [pow_zero, one_mul] at this
      exact absurd this (not_le.2 hbig)
  | succ n ih =>
    intro δ hR hJδ
    rcases pass_or_halve (q := q) H hR with hpass | ⟨hjJ, hbig, hR', htrans⟩
    · exact ⟨δ, hR, fun hj => (hJδ hj).1, fun _ _ => rfl, Relation.ReflTransGen.refl, hpass⟩
    obtain ⟨δ', hR'', hlow, hother, hrun, hord⟩ := ih _ hR' fun _ => by
      simp only [Function.update_self]
      have := (hJδ hjJ).2
      rw [pow_succ] at this
      constructor <;> linarith
    refine ⟨δ', hR'', hlow, fun i hi => ?_, Relation.ReflTransGen.head htrans hrun, hord⟩
    rw [hother i hi, Function.update_of_ne hi]

/-- Order `j ∈ [1, q]` eventually passes at the global minimizer, keeping the radius bounds. -/
private theorem exists_pass {sstar : E} {δbar : ℕ → ℝ} {j : ℕ} (hjI : j ∈ Icc 1 q)
    (H : OrderHyp m T Sd ΔT ς θ ε J sstar δbar j) {δ : ℕ → ℝ} (hR : RadiiOK J δ)
    (hlow : ∀ i ∈ J, i ∈ Icc 1 q → δbar i / 2 ≤ δ i) :
    ∃ δ' : ℕ → ℝ, RadiiOK J δ' ∧ (∀ i ∈ J, i ∈ Icc 1 q → δbar i / 2 ≤ δ' i) ∧
      Relation.ReflTransGen (DetailedStepTrans m T Sd ΔT q ς θ ε J) (check 1 sstar δ j)
        (check 1 sstar δ' j) ∧ OrderOK Sd ΔT ς θ ε sstar δ' j := by
  have hn : ∃ n : ℕ, j ∈ J → δbar j / 2 ≤ δ j ∧ δ j ≤ 2 ^ n * δbar j := by
    by_cases hjJ : j ∈ J
    · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / δbar j) one_lt_two
      have hpos := H.δbar_pos hjJ
      refine ⟨n, fun _ => ⟨hlow j hjJ hjI, (hR j).2.1.trans ?_⟩⟩
      rw [div_lt_iff₀ hpos] at hn
      exact hn.le
    · exact ⟨0, fun h => absurd h hjJ⟩
  obtain ⟨n, hn⟩ := hn
  obtain ⟨δ', hR', hlow', hother, hrun, hord⟩ := exists_pass_of_halving (q := q) H n δ hR hn
  refine ⟨δ', hR', fun i hiJ hiI => ?_, hrun, hord⟩
  rcases eq_or_ne i j with rfl | hij
  · exact hlow' hiJ
  · rw [hother i hij]; exact hlow i hiJ hiI

/-- The orders `j, …, q` pass one after the other (proof of Lemma 12.2.9). -/
private theorem exists_done_of_check {sstar : E} {δbar : ℕ → ℝ}
    (H : ∀ j ∈ Icc 1 q, OrderHyp m T Sd ΔT ς θ ε J sstar δbar j) (k : ℕ) :
    ∀ j, q - j = k → 1 ≤ j → j ≤ q → ∀ δ : ℕ → ℝ, RadiiOK J δ →
      (∀ i ∈ J, i ∈ Icc 1 q → δbar i / 2 ≤ δ i) →
      ∃ δs : ℕ → ℝ, RadiiOK J δs ∧ (∀ i ∈ J, i ∈ Icc 1 q → δbar i / 2 ≤ δs i) ∧
        Relation.ReflTransGen (DetailedStepTrans m T Sd ΔT q ς θ ε J) (check 1 sstar δ j)
          (done sstar δs) := by
  induction k with
  | zero =>
    intro j hk hj1 hjq δ hR hlow
    have hjI : j ∈ Icc 1 q := mem_Icc.2 ⟨hj1, hjq⟩
    obtain ⟨δ', hR', hlow', hrun, d, hd, happrox, hsmall⟩ := exists_pass hjI (H j hjI) hR hlow
    exact ⟨δ', hR', hlow', hrun.tail (DetailedStepTrans.finish hd happrox hsmall (by omega))⟩
  | succ k ih =>
    intro j hk hj1 hjq δ hR hlow
    have hjI : j ∈ Icc 1 q := mem_Icc.2 ⟨hj1, hjq⟩
    obtain ⟨δ', hR', hlow', hrun, d, hd, happrox, hsmall⟩ := exists_pass hjI (H j hjI) hR hlow
    obtain ⟨δs, hRs, hlows, hruns⟩ :=
      ih (j + 1) (by omega) (by omega) (by omega) δ' hR' hlow'
    exact ⟨δs, hRs, hlows,
      (hrun.tail (DetailedStepTrans.next hd happrox hsmall (by omega))).trans hruns⟩

/-- **Existence of an output with bounded radii** ([cartis2022evaluation], Lemmas 12.2.9,
14.1.3). Let `sstar ∈ T` be a global minimizer of the model on `T` with `sstar + d ∈ T` for every
feasible displacement `d ∈ Sd sstar ∋ 0`, and let `1 ≤ q`, `0 < ς ≤ 1`, `0 < θ`. Suppose that for
every order `j ∈ [1, q]`: `ε j > 0`; `ΔT j sstar 0 = 0`; for every `δ ∈ (0, 1]` the decrement
`ΔT j sstar` attains its maximum on `closedBall 0 δ ∩ Sd sstar`; if `j ∉ J`, the decrement is
nonpositive on `closedBall 0 1 ∩ Sd sstar` (the model is `j`-th order critical at `sstar` for the
radius `1`); and if `j ∈ J`, there is `δbar j ∈ (0, 1]` such that, for `δ ∈ (0, δbar j]` and every
feasible `d` of norm at most `δ`, `ς θ ε_j δ^j / j! ≤ ΔT j sstar d` implies the model decrease
`m sstar - m (sstar + d) ≥ ς θ ε_j δ^j / (2 j!)` (Lemma 12.2.8, resp. 14.1.2, with
`α = ς θ ε_j`). Then the procedure started with `μ = 1` returns `(sstar, δs)` with `δs j = 1` for
`j ∉ J` and `δs j ≥ δbar j / 2` for `j ∈ J ∩ [1, q]`.

(The book shows moreover that every execution of the procedure terminates; that statement is not
formalized here.) -/
theorem exists_isDetailedStepOutput {sstar : E} {δbar : ℕ → ℝ} (hq : 1 ≤ q) (hs : sstar ∈ T)
    (hmin : ∀ t ∈ T, m sstar ≤ m t) (hfeas : ∀ d ∈ Sd sstar, sstar + d ∈ T)
    (h0 : (0 : E) ∈ Sd sstar) (hς : 0 < ς) (hς1 : ς ≤ 1) (hθ : 0 < θ)
    (hε : ∀ j ∈ Icc 1 q, 0 < ε j) (hdec0 : ∀ j ∈ Icc 1 q, ΔT j sstar 0 = 0)
    (hatt : ∀ j ∈ Icc 1 q, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ d ∈ closedBall 0 δ ∩ Sd sstar,
      ∀ d' ∈ closedBall 0 δ ∩ Sd sstar, ΔT j sstar d' ≤ ΔT j sstar d)
    (hnotJ : ∀ j ∈ Icc 1 q, j ∉ J → ∀ d ∈ closedBall 0 1 ∩ Sd sstar, ΔT j sstar d ≤ 0)
    (hδbar : ∀ j ∈ Icc 1 q, j ∈ J → δbar j ∈ Set.Ioc (0 : ℝ) 1)
    (hgood : ∀ j ∈ Icc 1 q, j ∈ J → ∀ δ ∈ Set.Ioc (0 : ℝ) (δbar j),
      ∀ d ∈ closedBall 0 δ ∩ Sd sstar, ς * θ * ε j * δ ^ j / j ! ≤ ΔT j sstar d →
        ς * θ * ε j * δ ^ j / (2 * j !) ≤ m sstar - m (sstar + d)) :
    ∃ δs : ℕ → ℝ, IsDetailedStepOutput m T Sd ΔT q ς θ ε J sstar δs ∧
      (∀ j ∉ J, δs j = 1) ∧ ∀ j ∈ Icc 1 q, j ∈ J → δbar j / 2 ≤ δs j := by
  have H : ∀ j ∈ Icc 1 q, OrderHyp m T Sd ΔT ς θ ε J sstar δbar j := fun j hj =>
    { min := hmin, feas := hfeas, att := hatt j hj, zero_mem := h0, zero_dec := hdec0 j hj
      pos := by have := hε j hj; positivity
      ς_le := hς1, notJ := hnotJ j hj, δbar_pos := fun hJ => (hδbar j hj hJ).1
      good := hgood j hj }
  have hR1 : RadiiOK J (fun _ : ℕ => (1 : ℝ)) := fun _ => ⟨one_pos, le_rfl, fun _ => rfl⟩
  have hinf : sInf (m '' T) = m sstar :=
    IsLeast.csInf_eq ⟨⟨sstar, hs, rfl⟩, by rintro _ ⟨t, ht, rfl⟩; exact hmin t ht⟩
  have hdec : (1 : ℝ) * (m 0 - sInf (m '' T)) ≤ m 0 - m sstar := by rw [hinf, one_mul]
  have hfin : ∀ δs : ℕ → ℝ, RadiiOK J δs → (∀ j ∉ J, δs j = 1) := fun δs hR j hj => (hR j).2.2 hj
  rcases le_or_gt 1 ‖sstar‖ with hlong | hshort
  · refine ⟨fun _ => 1, ⟨1, ⟨one_pos, le_rfl⟩, Relation.ReflTransGen.single
      (DetailedStepTrans.ret hs hdec hlong)⟩, fun _ _ => rfl, fun j hj hjJ => ?_⟩
    have := (hδbar j hj hjJ).2
    linarith
  · obtain ⟨δs, hRs, hlows, hrun⟩ := exists_done_of_check H (q - 1) 1 rfl le_rfl hq
      (fun _ => 1) hR1 fun i hiJ hiI => by linarith [(hδbar i hiI hiJ).2]
    exact ⟨δs, ⟨1, ⟨one_pos, le_rfl⟩, Relation.ReflTransGen.head
      (DetailedStepTrans.start hs hdec hshort) hrun⟩, hfin δs hRs, fun j hj hjJ => hlows j hjJ hj⟩

end DetailedStep

/-! ### Termination and progress of the detailed Step 2 -/

section Termination

variable {m : E → ℝ} {T : Set E} {Sd : E → Set E} {ΔT : ℕ → E → E → ℝ} {q : ℕ} {ς θ : ℝ}
  {ε : ℕ → ℝ} {J : Set ℕ}

/-- The radii of a state of the detailed Step 2. -/
def DetailedStepState.radii : DetailedStepState E → ℕ → ℝ
  | findStep _ δ => δ
  | check _ _ δ _ => δ
  | done _ δ => δ

omit [NormedAddCommGroup E] in
@[simp] theorem DetailedStepState.radii_findStep (μ : ℝ) (δ : ℕ → ℝ) :
    (findStep μ δ : DetailedStepState E).radii = δ := rfl

omit [NormedAddCommGroup E] in
@[simp] theorem DetailedStepState.radii_check (μ : ℝ) (s : E) (δ : ℕ → ℝ) (j : ℕ) :
    (check μ s δ j).radii = δ := rfl

omit [NormedAddCommGroup E] in
@[simp] theorem DetailedStepState.radii_done (s : E) (δ : ℕ → ℝ) :
    (done s δ : DetailedStepState E).radii = δ := rfl

/-- **Progress of the detailed Step 2** ([cartis2022evaluation], Algorithms 12.2.3, 14.1.2:
every step of the procedure can be executed). Assume that Step 2.2 can always be performed (for
every `μ ∈ (0, 1]` some `s ∈ T` has `μ (m(0) - m*) ≤ m(0) - m(s)`) and Step 2.4.1 can always be
performed (for every feasible `s`, order `j` and radius `r ∈ (0, 1]` some feasible `d` of norm at
most `r` achieves the fraction `ς` of the supremum of the decrements). Then every state reachable
from `μ₀ ∈ (0, 1]` and unit radii that is not final has a successor: the tests of Steps 2.3–2.4
cover all cases. -/
theorem DetailedStepState.exists_trans
    (hfind : ∀ μ ∈ Set.Ioc (0 : ℝ) 1, ∃ s ∈ T, μ * (m 0 - sInf (m '' T)) ≤ m 0 - m s)
    (hdisp : ∀ s ∈ T, ∀ (j : ℕ) (r : ℝ), 0 < r → r ≤ 1 → ∃ d ∈ closedBall 0 r ∩ Sd s,
      ς * sSup (ΔT j s '' (closedBall 0 r ∩ Sd s)) ≤ ΔT j s d) {μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ Set.Ioc (0 : ℝ) 1) {b : DetailedStepState E}
    (h : Relation.ReflTransGen (DetailedStepTrans m T Sd ΔT q ς θ ε J)
      (findStep μ₀ fun _ => 1) b) (hb : ∀ s δ, b ≠ done s δ) :
    ∃ b', DetailedStepTrans m T Sd ΔT q ς θ ε J b b' := by
  have hinv : StepInv m T Sd ΔT q ς θ ε J b := by
    refine Relation.ReflTransGen.rec (motive := fun b _ => StepInv m T Sd ΔT q ς θ ε J b)
      ?_ (fun _ hbc ih => stepInv_trans hbc ih) h
    exact ⟨hμ₀, fun _ => ⟨one_pos, le_rfl, fun _ => rfl⟩⟩
  rcases b with ⟨μ, δ⟩ | ⟨μ, s, δ, j⟩ | ⟨s, δ⟩
  · obtain ⟨s, hs, hdec⟩ := hfind μ hinv.1
    by_cases hlong : 1 ≤ ‖s‖
    · exact ⟨_, DetailedStepTrans.ret hs hdec hlong⟩
    · exact ⟨_, DetailedStepTrans.start hs hdec (not_le.1 hlong)⟩
  · obtain ⟨-, hR, hsT, -⟩ := hinv
    obtain ⟨d, hd, happrox⟩ := hdisp s hsT j (δ j) (hR j).1 (hR j).2.1
    by_cases hsmall : ΔT j s d ≤ ς * θ * ε j * δ j ^ j / (j ! : ℝ)
    · rcases lt_or_ge j q with hjq | hjq
      · exact ⟨_, DetailedStepTrans.next hd happrox hsmall hjq⟩
      · exact ⟨_, DetailedStepTrans.finish hd happrox hsmall hjq⟩
    · push Not at hsmall
      by_cases hJ : j ∈ J ∧ m s - m (s + d) < ς * θ * ε j * δ j ^ j / (2 * j !)
      · exact ⟨_, DetailedStepTrans.halve hd happrox hsmall hJ.1 hJ.2⟩
      · refine ⟨_, DetailedStepTrans.restart hd happrox hsmall ?_⟩
        by_cases hjJ : j ∈ J
        · exact Or.inr (not_lt.1 fun h' => hJ ⟨hjJ, h'⟩)
        · exact Or.inl hjJ
  · exact absurd rfl (hb s δ)

/-- Radii between the lower bounds `lb` and `1`, equal to `1` outside `J`. -/
private def RadLB (J : Set ℕ) (lb δ : ℕ → ℝ) : Prop :=
  ∀ j, lb j ≤ δ j ∧ δ j ≤ 1 ∧ (j ∉ J → δ j = 1)

/-- The invariant of an execution with radius lower bounds `lb`. -/
private def TermInv (m : E → ℝ) (T : Set E) (q : ℕ) (J : Set ℕ) (lb : ℕ → ℝ) :
    DetailedStepState E → Prop
  | findStep μ δ => μ ∈ Set.Ioc (0 : ℝ) 1 ∧ RadLB J lb δ
  | check μ s δ j => μ ∈ Set.Ioc (0 : ℝ) 1 ∧ RadLB J lb δ ∧ s ∈ T ∧
      μ * (m 0 - sInf (m '' T)) ≤ m 0 - m s ∧ ‖s‖ < 1 ∧ 1 ≤ j ∧ j ≤ q
  | done _ δ => RadLB J lb δ

/-- The halving hypothesis of the termination theorem: a halving (Step 2.4.3) at an order
`j ∈ J ∩ [1, q]`, from radii within their bounds at a short feasible trial step, only happens
when `δ_j ≥ 2 lb_j` (so the halved radius stays above `lb_j`). -/
def DetailedHalvingBound (m : E → ℝ) (T : Set E) (Sd : E → Set E) (ΔT : ℕ → E → E → ℝ)
    (q : ℕ) (ς θ : ℝ) (ε : ℕ → ℝ) (J : Set ℕ) (lb : ℕ → ℝ) : Prop :=
  ∀ (s : E) (δ : ℕ → ℝ) (j : ℕ) (d : E), s ∈ T → ‖s‖ < 1 → 1 ≤ j → j ≤ q → j ∈ J →
    lb j ≤ δ j → δ j ≤ 1 → d ∈ closedBall 0 (δ j) ∩ Sd s →
    ς * θ * ε j * δ j ^ j / j ! < ΔT j s d →
    m s - m (s + d) < ς * θ * ε j * δ j ^ j / (2 * j !) → 2 * lb j ≤ δ j

/-- The restart-gap hypothesis of the termination theorem: there is `η > 0` such that a restart
(Step 2.4.4) at a short feasible trial step `s`, with radii within their bounds, only happens when
`m(s) - m* ≥ η`, with `m* = sInf (m '' T)`. -/
def DetailedRestartGap (m : E → ℝ) (T : Set E) (Sd : E → Set E) (ΔT : ℕ → E → E → ℝ)
    (q : ℕ) (ς θ : ℝ) (ε : ℕ → ℝ) (J : Set ℕ) (lb : ℕ → ℝ) : Prop :=
  ∃ η > 0, ∀ (s : E) (δ : ℕ → ℝ) (j : ℕ) (d : E), s ∈ T → ‖s‖ < 1 → 1 ≤ j → j ≤ q →
    (∀ i, lb i ≤ δ i ∧ δ i ≤ 1 ∧ (i ∉ J → δ i = 1)) → d ∈ closedBall 0 (δ j) ∩ Sd s →
    ς * θ * ε j * δ j ^ j / j ! < ΔT j s d →
    (j ∉ J ∨ ς * θ * ε j * δ j ^ j / (2 * j !) ≤ m s - m (s + d)) →
    η ≤ m s - sInf (m '' T)

private theorem termInv_trans {lb : ℕ → ℝ} (hq : 1 ≤ q)
    (hhalve : DetailedHalvingBound m T Sd ΔT q ς θ ε J lb) {a b : DetailedStepState E}
    (h : DetailedStepTrans m T Sd ΔT q ς θ ε J a b) (ha : TermInv m T q J lb a) :
    TermInv m T q J lb b := by
  cases h with
  | ret hs hdec hlong => exact ha.2
  | start hs hdec hshort => exact ⟨ha.1, ha.2, hs, hdec, hshort, le_rfl, hq⟩
  | next hd happrox hsmall hj =>
    obtain ⟨hμ, hR, hsT, hdec, hs, hj1, -⟩ := ha
    exact ⟨hμ, hR, hsT, hdec, hs, by omega, hj⟩
  | finish hd happrox hsmall hj => exact ha.2.1
  | @halve μ s δ j d hd happrox hlarge hJ hmodel =>
    obtain ⟨hμ, hR, hsT, hdec, hs, hj1, hjq⟩ := ha
    refine ⟨hμ, fun i => ?_, hsT, hdec, hs, hj1, hjq⟩
    rcases eq_or_ne i j with rfl | hij
    · simp only [Function.update_self]
      obtain ⟨hlb, hle1, -⟩ := hR i
      have := hhalve s δ i d hsT hs hj1 hjq hJ hlb hle1 hd hlarge hmodel
      exact ⟨by linarith, by linarith, fun h => absurd hJ h⟩
    · simp only [Function.update_of_ne hij]
      exact hR i
  | restart hd happrox hlarge hJ =>
    obtain ⟨⟨h0, h1⟩, hR, -⟩ := ha
    exact ⟨⟨by linarith, by linarith⟩, hR⟩

private theorem termInv_init {lb : ℕ → ℝ} (hlb : ∀ j, lb j ≤ 1) {μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ Set.Ioc (0 : ℝ) 1) : TermInv m T q J lb (findStep μ₀ fun _ => 1) :=
  ⟨hμ₀, fun j => ⟨hlb j, le_rfl, fun _ => rfl⟩⟩

private theorem termInv_of_reflTransGen {lb : ℕ → ℝ} (hq : 1 ≤ q) (hlb : ∀ j, lb j ≤ 1)
    (hhalve : DetailedHalvingBound m T Sd ΔT q ς θ ε J lb) {μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ Set.Ioc (0 : ℝ) 1) {b : DetailedStepState E}
    (h : Relation.ReflTransGen (DetailedStepTrans m T Sd ΔT q ς θ ε J)
      (findStep μ₀ fun _ => 1) b) : TermInv m T q J lb b :=
  Relation.ReflTransGen.rec (motive := fun b _ => TermInv m T q J lb b)
    (termInv_init hlb hμ₀) (fun _ hbc ih => termInv_trans hq hhalve hbc ih) h

/-- **Radius lower bounds along executions** (proof of [cartis2022evaluation], Lemma 12.2.9):
under the halving bound, every state reachable from `μ₀ ∈ (0, 1]` and unit radii has radii
`lb_j ≤ δ_j ≤ 1` (for lower bounds `lb_j ≤ 1`). -/
theorem DetailedStepState.lb_le_radii {lb : ℕ → ℝ} (hq : 1 ≤ q) (hlb : ∀ j, lb j ≤ 1)
    (hhalve : DetailedHalvingBound m T Sd ΔT q ς θ ε J lb) {μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ Set.Ioc (0 : ℝ) 1) {b : DetailedStepState E}
    (h : Relation.ReflTransGen (DetailedStepTrans m T Sd ΔT q ς θ ε J)
      (findStep μ₀ fun _ => 1) b) : ∀ j, lb j ≤ b.radii j ∧ b.radii j ≤ 1 := by
  have hinv := termInv_of_reflTransGen hq hlb hhalve hμ₀ h
  intro j
  rcases b with ⟨μ, δ⟩ | ⟨μ, s, δ, i⟩ | ⟨s, δ⟩
  · exact ⟨(hinv.2 j).1, (hinv.2 j).2.1⟩
  · exact ⟨(hinv.2.1 j).1, (hinv.2.1 j).2.1⟩
  · exact ⟨(hinv j).1, (hinv j).2.1⟩

/-- The potential `C (1 - μ) + ∑_{i ≤ q} δ_i + ℓ (q + 1 - j)` of a state. -/
private noncomputable def termPotential (q : ℕ) (C ℓ : ℝ) : DetailedStepState E → ℝ
  | findStep μ δ => C * (1 - μ) + ∑ i ∈ Icc 1 q, δ i + ℓ * ((q : ℝ) + 1)
  | check μ _ δ j => C * (1 - μ) + ∑ i ∈ Icc 1 q, δ i + ℓ * ((q : ℝ) + 1 - j)
  | done _ _ => 0

/-- The potential decreases by `ℓ` at every transition to a state that is not final. -/
private theorem termPotential_le {lb : ℕ → ℝ} {C ℓ : ℝ} (hℓ0 : 0 ≤ ℓ)
    (hℓ : ∀ j ∈ Icc 1 q, ℓ ≤ lb j / 2)
    (hrestart : ∀ (μ : ℝ) (s : E) (δ : ℕ → ℝ) (j : ℕ) (d : E),
      TermInv m T q J lb (check μ s δ j) → d ∈ closedBall 0 (δ j) ∩ Sd s →
      ς * θ * ε j * δ j ^ j / j ! < ΔT j s d →
      (j ∉ J ∨ ς * θ * ε j * δ j ^ j / (2 * j !) ≤ m s - m (s + d)) →
      ℓ * ((q : ℝ) + 1) ≤ C * (1 - μ) / 2)
    {a b : DetailedStepState E} (h : DetailedStepTrans m T Sd ΔT q ς θ ε J a b)
    (ha : TermInv m T q J lb a) (hb : ∀ s δ, b ≠ done s δ) :
    termPotential q C ℓ b ≤ termPotential q C ℓ a - ℓ := by
  cases h with
  | ret hs hdec hlong => exact absurd rfl (hb _ _)
  | start hs hdec hshort =>
    simp only [termPotential, Nat.cast_one]
    linarith
  | next hd happrox hsmall hj =>
    simp only [termPotential, Nat.cast_add, Nat.cast_one]
    linarith
  | finish hd happrox hsmall hj => exact absurd rfl (hb _ _)
  | @halve μ s δ j d hd happrox hlarge hJ hmodel =>
    obtain ⟨-, hR, -, -, -, hj1, hjq⟩ := ha
    have hj : j ∈ Icc 1 q := mem_Icc.2 ⟨hj1, hjq⟩
    have hsum := sum_update_of_mem hj δ (δ j / 2)
    have hsplit := sum_eq_add_sum_sdiff_singleton (s := Icc 1 q) j δ fun h' => absurd hj h'
    have := hℓ j hj
    have := (hR j).1
    simp only [termPotential]
    linarith
  | @restart μ s δ j d hd happrox hlarge hJ =>
    have hr := hrestart μ s δ j d ha hd hlarge hJ
    obtain ⟨-, -, -, -, -, -, hjq⟩ := ha
    have : (j : ℝ) ≤ q := by exact_mod_cast hjq
    have : ℓ * j ≤ ℓ * q := mul_le_mul_of_nonneg_left this hℓ0
    simp only [termPotential]
    nlinarith

/-- **Termination of the detailed Step 2** ([cartis2022evaluation], Lemma 12.2.9 for
Algorithm 12.2.3, and Algorithm 14.1.2), abstract form. Let `1 ≤ q`, `0 ∈ T`, the model be bounded
below on `T`, `lb_j ∈ (0, 1]`, and assume the halving bound (halvings stop at `2 lb_j`) and the
restart gap (a restart needs `m(s) - m* ≥ η > 0`). Then there is no infinite execution started
(Step 2.1) with `μ₀ ∈ (0, 1]` and unit radii. (A potential
`C (1 - μ) + ∑ δ_i + ℓ (q + 1 - j)` decreases by `ℓ` at every transition.) -/
theorem detailedStep_terminates {lb : ℕ → ℝ} (hq : 1 ≤ q) (h0 : (0 : E) ∈ T)
    (hb : BddBelow (m '' T)) (hlb : ∀ j, 0 < lb j ∧ lb j ≤ 1)
    (hhalve : DetailedHalvingBound m T Sd ΔT q ς θ ε J lb)
    (hgap : DetailedRestartGap m T Sd ΔT q ς θ ε J lb) {μ₀ : ℝ}
    (hμ₀ : μ₀ ∈ Set.Ioc (0 : ℝ) 1) :
    ¬ ∃ c : ℕ → DetailedStepState E, c 0 = findStep μ₀ (fun _ => 1) ∧
      ∀ n, DetailedStepTrans m T Sd ΔT q ς θ ε J (c n) (c (n + 1)) := by
  classical
  rintro ⟨c, hc0, hc⟩
  have hinv : ∀ n, TermInv m T q J lb (c n) := fun n => by
    induction n with
    | zero => rw [hc0]; exact termInv_init (fun j => (hlb j).2) hμ₀
    | succ n ih => exact termInv_trans hq hhalve (hc n) ih
  have hnd : ∀ n s δ, c (n + 1) ≠ done s δ := fun n s δ h => by
    have := hc (n + 1)
    rw [h] at this
    cases this
  obtain ⟨η, hη, hgap⟩ := hgap
  set Δm := m 0 - sInf (m '' T) with hΔm
  have hΔm0 : 0 ≤ Δm := sub_nonneg.2 (csInf_le hb ⟨0, h0, rfl⟩)
  have hne : (Icc 1 q).Nonempty := ⟨1, mem_Icc.2 ⟨le_rfl, hq⟩⟩
  set ℓ := (Icc 1 q).inf' hne fun j => lb j / 2 with hℓdef
  have hℓ0 : 0 < ℓ := (lt_inf'_iff _).2 fun j _ => half_pos (hlb j).1
  have hℓ : ∀ j ∈ Icc 1 q, ℓ ≤ lb j / 2 := fun j hj => inf'_le _ hj
  set C := 2 * (ℓ * ((q : ℝ) + 1)) * Δm / η with hCdef
  have hC : 0 ≤ C := by positivity
  -- the potential decreases by `ℓ` at every transition
  have hrestart : ∀ (μ : ℝ) (s : E) (δ : ℕ → ℝ) (j : ℕ) (d : E),
      TermInv m T q J lb (check μ s δ j) → d ∈ closedBall 0 (δ j) ∩ Sd s →
      ς * θ * ε j * δ j ^ j / j ! < ΔT j s d →
      (j ∉ J ∨ ς * θ * ε j * δ j ^ j / (2 * j !) ≤ m s - m (s + d)) →
      ℓ * ((q : ℝ) + 1) ≤ C * (1 - μ) / 2 := by
    intro μ s δ j d hinv' hd hlarge hJ
    obtain ⟨-, hR, hsT, h2, hs, hj1, hjq⟩ := hinv'
    have h1 := hgap s δ j d hsT hs hj1 hjq hR hd hlarge hJ
    have h3 : η ≤ (1 - μ) * Δm := by
      have e : (1 - μ) * Δm = Δm - μ * Δm := by ring
      rw [e, hΔm]
      linarith
    have h4 : 1 ≤ (1 - μ) * Δm / η := (one_le_div hη).2 h3
    have e : C * (1 - μ) / 2 = ℓ * ((q : ℝ) + 1) * ((1 - μ) * Δm / η) := by
      rw [hCdef]; field_simp
    rw [e]
    have : 0 ≤ ℓ * ((q : ℝ) + 1) := by positivity
    nlinarith
  have hdec : ∀ n, termPotential q C ℓ (c (n + 1)) ≤ termPotential q C ℓ (c n) - ℓ := fun n =>
    termPotential_le hℓ0.le hℓ hrestart (hc n) (hinv n) (hnd n)
  have hbound : ∀ n : ℕ, termPotential q C ℓ (c n) ≤ termPotential q C ℓ (c 0) - n * ℓ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have := hdec n; push_cast; linarith
  have hnonneg : ∀ n, 0 ≤ termPotential q C ℓ (c n) := by
    intro n
    have ha := hinv n
    have hS : ∀ δ : ℕ → ℝ, RadLB J lb δ → 0 ≤ ∑ i ∈ Icc 1 q, δ i := fun δ hR =>
      sum_nonneg fun i _ => (hlb i).1.le.trans (hR i).1
    generalize c n = a at ha
    rcases a with ⟨μ, δ⟩ | ⟨μ, s, δ, j⟩ | ⟨s, δ⟩
    · obtain ⟨⟨-, h1⟩, hR⟩ := ha
      have := hS δ hR
      have : 0 ≤ C * (1 - μ) := mul_nonneg hC (by linarith)
      simp only [termPotential]
      positivity
    · obtain ⟨⟨-, h1⟩, hR, -, -, -, -, hjq⟩ := ha
      have := hS δ hR
      have : 0 ≤ C * (1 - μ) := mul_nonneg hC (by linarith)
      have : (j : ℝ) ≤ q := by exact_mod_cast hjq
      have : 0 ≤ ℓ * ((q : ℝ) + 1 - j) := mul_nonneg hℓ0.le (by linarith)
      simp only [termPotential]
      linarith
    · exact le_rfl
  obtain ⟨n, hn⟩ := exists_nat_gt (termPotential q C ℓ (c 0) / ℓ)
  have h1 := hbound n
  have h2 := hnonneg n
  rw [div_lt_iff₀ hℓ0] at hn
  linarith

end Termination

/-! ### Step-length algebra -/

section StepLength

variable {A B a ε δ t : ℝ} {j p : ℕ}

/-- `∑_{ℓ=1}^j δ^ℓ/ℓ! t^{p-ℓ+1} = t^{p+1} χ_j(δ/t)` for `t > 0` and `j ≤ p`. -/
private theorem sum_mul_pow_eq (ht : 0 < t) (hjp : j ≤ p) :
    ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) * t ^ (p - ℓ + 1) =
      t ^ (p + 1) * ∑ ℓ ∈ Icc 1 j, (δ / t) ^ ℓ / (ℓ ! : ℝ) := by
  rw [mul_sum]
  refine sum_congr rfl fun ℓ hℓ => ?_
  have hℓp : ℓ ≤ p := (mem_Icc.1 hℓ).2.trans hjp
  have hpow : t ^ (p + 1) = t ^ (p - ℓ + 1) * t ^ ℓ := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, div_pow]
  field_simp

/-- For `0 < t ≤ δ` and `j ≤ p`: `∑_{ℓ=1}^j δ^ℓ/ℓ! t^{p-ℓ+1} ≤ 2 δ^j t^{p-j+1}` (by (A.35)). -/
theorem sum_mul_pow_le_of_le (ht : 0 < t) (htδ : t ≤ δ) (hjp : j ≤ p) :
    ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) * t ^ (p - ℓ + 1) ≤ 2 * δ ^ j * t ^ (p - j + 1) := by
  rw [sum_mul_pow_eq ht hjp]
  have h1 : 1 ≤ δ / t := (one_le_div ht).2 htδ
  have := sum_pow_div_factorial_le_two_mul_pow h1 j
  have hpow : t ^ (p + 1) = t ^ (p - j + 1) * t ^ j := by
    rw [← pow_add]; congr 1; omega
  calc t ^ (p + 1) * ∑ ℓ ∈ Icc 1 j, (δ / t) ^ ℓ / (ℓ ! : ℝ) ≤ t ^ (p + 1) * (2 * (δ / t) ^ j) :=
        mul_le_mul_of_nonneg_left this (pow_nonneg ht.le _)
    _ = 2 * δ ^ j * t ^ (p - j + 1) := by
        rw [hpow, div_pow]; field_simp

/-- For `0 ≤ δ ≤ t`, `0 < t` and `j ≤ p`: `∑_{ℓ=1}^j δ^ℓ/ℓ! t^{p-ℓ+1} ≤ 2 δ t^p` (by (A.34)). -/
theorem sum_mul_pow_le_of_ge (ht : 0 < t) (hδ : 0 ≤ δ) (hδt : δ ≤ t) (hjp : j ≤ p) :
    ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) * t ^ (p - ℓ + 1) ≤ 2 * δ * t ^ p := by
  rw [sum_mul_pow_eq ht hjp]
  have h1 : δ / t ≤ 1 := (div_le_one ht).2 hδt
  have := sum_pow_div_factorial_le_two_mul (div_nonneg hδ ht.le) h1 j
  calc t ^ (p + 1) * ∑ ℓ ∈ Icc 1 j, (δ / t) ^ ℓ / (ℓ ! : ℝ) ≤ t ^ (p + 1) * (2 * (δ / t)) :=
        mul_le_mul_of_nonneg_left this (pow_nonneg ht.le _)
    _ = 2 * δ * t ^ p := by
        rw [pow_succ]; field_simp

/-- The measure inequality `a ε δ^j / j! ≤ A ∑_{ℓ=1}^j δ^ℓ/ℓ! t^{p-ℓ+1} + B t^{p+1}` of
Lemmas 12.2.11, 13.1.16, 14.1.7 ([cartis2022evaluation], (12.2.52), (13.1.79), (14.1.30)),
with `t = ‖s_k‖`. -/
def MeasureIneq (A B a ε δ t : ℝ) (j p : ℕ) : Prop :=
  a * ε * δ ^ j / j ! ≤ A * ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) * t ^ (p - ℓ + 1) + B * t ^ (p + 1)

theorem measureIneq_iff : MeasureIneq A B a ε δ t j p ↔
    a * ε * δ ^ j / j ! ≤
      A * ∑ ℓ ∈ Icc 1 j, δ ^ ℓ / (ℓ ! : ℝ) * t ^ (p - ℓ + 1) + B * t ^ (p + 1) :=
  Iff.rfl

/-- The measure inequality when the step is shorter than the radius (`t ≤ δ`):
`a ε / j! ≤ (2A + B) t^{p-j+1}` (proofs of Lemmas 12.2.12, 14.1.8, case `‖s_k‖ ≤ δ`). -/
theorem MeasureIneq.div_le_of_le (h : MeasureIneq A B a ε δ t j p) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht : 0 < t) (htδ : t ≤ δ) (hjp : j ≤ p) :
    a * ε / j ! ≤ (2 * A + B) * t ^ (p - j + 1) := by
  have hδ : 0 < δ := ht.trans_le htδ
  have hsum := sum_mul_pow_le_of_le (j := j) ht htδ hjp
  have hBt : B * t ^ (p + 1) ≤ B * (δ ^ j * t ^ (p - j + 1)) := by
    refine mul_le_mul_of_nonneg_left ?_ hB
    have : t ^ (p + 1) = t ^ j * t ^ (p - j + 1) := by rw [← pow_add]; congr 1; omega
    rw [this]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.le htδ j) (pow_nonneg ht.le _)
  have hδj : 0 < δ ^ j := pow_pos hδ j
  have key : a * ε * δ ^ j / j ! ≤ δ ^ j * ((2 * A + B) * t ^ (p - j + 1)) := by
    calc a * ε * δ ^ j / j ! ≤ A * (2 * δ ^ j * t ^ (p - j + 1)) + B * (δ ^ j * t ^ (p - j + 1)) :=
          h.trans (add_le_add (mul_le_mul_of_nonneg_left hsum hA) hBt)
      _ = δ ^ j * ((2 * A + B) * t ^ (p - j + 1)) := by ring
  rw [mul_div_right_comm, mul_comm (a * ε / j !)] at key
  exact le_of_mul_le_mul_left key hδj

/-- The measure inequality when the step is longer than the radius (`δ ≤ t`):
`a ε δ^j / j! ≤ 2 A δ t^p + B t^{p+1}` (proofs of Lemmas 12.2.12, 14.1.8, case `δ < ‖s_k‖`). -/
theorem MeasureIneq.le_of_ge (h : MeasureIneq A B a ε δ t j p) (hA : 0 ≤ A) (ht : 0 < t)
    (hδ : 0 ≤ δ) (hδt : δ ≤ t) (hjp : j ≤ p) :
    a * ε * δ ^ j / j ! ≤ 2 * A * δ * t ^ p + B * t ^ (p + 1) := by
  have := mul_le_mul_of_nonneg_left (sum_mul_pow_le_of_ge (j := j) ht hδ hδt hjp) hA
  unfold MeasureIneq at h
  linarith

/-- **Step-length bound for ARqp and ARqpIDA** ([cartis2022evaluation], Lemmas 12.2.12, 13.1.17,
corrected). Let `1 ≤ j ≤ p`, `A, a, ε > 0`, `t ∈ (0, 1]`, `δ > 0`, and suppose the measure
inequality `a ε δ^j / j! ≤ A ∑_{ℓ=1}^j δ^ℓ/ℓ! t^{p-ℓ+1}` holds. If `κ > 0` and `κ ε ≤ δ`
(e.g. `δ = 1`, `κ = 1`, `ε ≤ 1`), then with `τ = a / (A j!)` and `κ̂ = min κ (τ/2)`:
`(τ/2) κ̂^{j-1} ε^j ≤ t^p`.

(The book states `(τ/2) κ^{j-1} ε^j ≤ t^p`; its proof in the case `t ≤ δ` uses `κ ≤ τ/2`, which is
not assumed, hence `κ̂`.) -/
theorem pow_ge_of_measure_ineq {κ : ℝ} (h : MeasureIneq A 0 a ε δ t j p) (hA : 0 < A)
    (ha : 0 < a) (hε : 0 < ε) (ht : 0 < t) (ht1 : t ≤ 1) (hδ : 0 < δ)
    (hj : 1 ≤ j) (hjp : j ≤ p) (hκ : 0 < κ) (hκε : κ * ε ≤ δ) :
    a / (A * j !) / 2 * min κ (a / (A * j !) / 2) ^ (j - 1) * ε ^ j ≤ t ^ p := by
  set τ := a / (A * j !)
  have hfact : (0 : ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
  have hτ : 0 < τ := div_pos ha (mul_pos hA hfact)
  set κh := min κ (τ / 2)
  have hκh : 0 < κh := lt_min hκ (half_pos hτ)
  have hκhτ : κh ≤ τ / 2 := min_le_right _ _
  have hκhκ : κh ≤ κ := min_le_left _ _
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  rcases le_or_gt t δ with htδ | hδt
  · -- `τ ε / 2 ≤ t^{p-j+1}`
    have h1 := h.div_le_of_le hA.le le_rfl ht htδ hjp
    have hx : τ * ε / 2 ≤ t ^ (p - (i + 1) + 1) := by
      rw [add_zero] at h1
      have : τ * ε / 2 = a * ε / (i + 1) ! / (2 * A) := by
        simp only [τ]; field_simp
      rw [this, div_le_iff₀ (by positivity)]
      linarith
    have hx0 : 0 ≤ τ * ε / 2 := by positivity
    -- `t^p ≥ t^{j (p-j+1)} ≥ (τ ε / 2)^j`
    have hexp : p ≤ (i + 1) * (p - (i + 1) + 1) := by
      obtain ⟨r, rfl⟩ : ∃ r, p = i + 1 + r := ⟨p - (i + 1), by omega⟩
      rw [show i + 1 + r - (i + 1) + 1 = r + 1 by omega]
      nlinarith
    have h2 : (τ * ε / 2) ^ (i + 1) ≤ t ^ p := by
      calc (τ * ε / 2) ^ (i + 1) ≤ (t ^ (p - (i + 1) + 1)) ^ (i + 1) :=
            pow_le_pow_left₀ hx0 hx _
        _ = t ^ ((i + 1) * (p - (i + 1) + 1)) := by rw [← pow_mul, mul_comm]
        _ ≤ t ^ p := pow_le_pow_of_le_one ht.le ht1 hexp
    calc τ / 2 * κh ^ i * ε ^ (i + 1) ≤ τ / 2 * (τ / 2) ^ i * ε ^ (i + 1) := by
          gcongr
      _ = (τ * ε / 2) ^ (i + 1) := by ring
      _ ≤ t ^ p := h2
  · -- `τ ε δ^{j-1} / 2 ≤ t^p`
    have h1 := h.le_of_ge hA.le ht hδ.le hδt.le hjp
    rw [zero_mul, add_zero] at h1
    have hδj : δ ^ (i + 1) = δ * δ ^ i := pow_succ' δ i
    have h2 : τ / 2 * ε * δ ^ i ≤ t ^ p := by
      rw [hδj] at h1
      have : τ / 2 * ε * δ ^ i * (2 * A * δ) = a * ε * (δ * δ ^ i) / (i + 1) ! := by
        simp only [τ]; field_simp
      have hpos : 0 < 2 * A * δ := by positivity
      rw [← mul_le_mul_iff_left₀ hpos, this]
      linarith
    have h3 : (κh * ε) ^ i ≤ δ ^ i :=
      pow_le_pow_left₀ (by positivity) ((mul_le_mul_of_nonneg_right hκhκ hε.le).trans hκε) _
    calc τ / 2 * κh ^ i * ε ^ (i + 1) = τ / 2 * ε * (κh * ε) ^ i := by ring
      _ ≤ τ / 2 * ε * δ ^ i := by gcongr
      _ ≤ t ^ p := h2

/-- `x ≤ t^n` with `x, t ≥ 0`, `n ≠ 0` gives `x^{1/n} ≤ t`. -/
theorem rpow_one_div_le_of_le_pow {x t : ℝ} {n : ℕ} (hn : n ≠ 0) (hx : 0 ≤ x)
    (ht : 0 ≤ t) (h : x ≤ t ^ n) : x ^ (1 / (n : ℝ)) ≤ t := by
  calc x ^ (1 / (n : ℝ)) ≤ (t ^ n) ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow hx h (by positivity)
    _ = t := by rw [one_div, Real.pow_rpow_inv_natCast ht hn]

/-- `(t^n)^{m/n} = t^m` for `t ≥ 0`, `n ≠ 0`. -/
theorem pow_rpow_div_natCast {t : ℝ} (ht : 0 ≤ t) {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    (t ^ n) ^ ((m : ℝ) / (n : ℝ)) = t ^ m := by
  rw [← Real.rpow_natCast t n, ← Real.rpow_mul ht, mul_div_cancel₀ _ (by positivity),
    Real.rpow_natCast]

/-- **Step-length bound for ARqpC** ([cartis2022evaluation], Lemma 14.1.8, corrected). Let
`j ≤ p`, `A > 0`, `0 ≤ B ≤ A`, `0 < a ≤ j! A`, `ε ∈ (0, 1]`, `t > 0`, `δ > 0`, and suppose the
measure inequality `a ε δ^j / j! ≤ A ∑_{ℓ=1}^j δ^ℓ/ℓ! t^{p-ℓ+1} + B t^{p+1}` holds. Let
`α = a / (j! A) ∈ (0, 1]`.
* If `t ≤ δ`, then `(α ε / 3)^{1/(p-j+1)} ≤ t`.
* If `κ ∈ (0, 1]` and `κ ε ≤ δ`, then `(α κ^j / 3)^{1/(p-j+1)} ε^{(j+1)/(p+1)} ≤ t`.

(The second case of (14.1.31) as printed omits the factor `ε^{(j+1)/(p+1)}`.) -/
theorem norm_step_ge_of_measure_ineq (h : MeasureIneq A B a ε δ t j p) (hA : 0 < A)
    (hB : 0 ≤ B) (hBA : B ≤ A) (ha : 0 < a) (haA : a ≤ j ! * A) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ht : 0 < t) (hδ : 0 < δ) (hjp : j ≤ p) :
    (t ≤ δ → (a / (j ! * A) * ε / 3) ^ (1 / (p - j + 1 : ℝ)) ≤ t) ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ 1 → κ * ε ≤ δ →
        (a / (j ! * A) * κ ^ j / 3) ^ (1 / (p - j + 1 : ℝ)) *
          ε ^ ((j + 1 : ℝ) / (p + 1)) ≤ t := by
  have hfact : (0 : ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
  set α := a / (j ! * A) with hα_def
  have hα : 0 < α := div_pos ha (mul_pos hfact hA)
  have hα1 : α ≤ 1 := (div_le_one (mul_pos hfact hA)).2 haA
  have hn : (p - j + 1 : ℝ) = ((p - j + 1 : ℕ) : ℝ) := by push_cast [Nat.cast_sub hjp]; ring
  have hn0 : p - j + 1 ≠ 0 := by omega
  -- the case `t ≤ δ`: `α ε / 3 ≤ t^{p-j+1}`
  have hcase1 : t ≤ δ → α * ε / 3 ≤ t ^ (p - j + 1) := by
    intro htδ
    have h1 := h.div_le_of_le hA.le hB ht htδ hjp
    have h2 : (2 * A + B) * t ^ (p - j + 1) ≤ 3 * A * t ^ (p - j + 1) := by
      gcongr; linarith
    have : α * ε / 3 = a * ε / j ! / (3 * A) := by
      rw [hα_def]; field_simp
    rw [this, div_le_iff₀ (by positivity)]
    linarith
  refine ⟨fun htδ => ?_, fun κ hκ hκ1 hκε => ?_⟩
  · rw [hn]
    exact rpow_one_div_le_of_le_pow hn0 (by positivity) ht.le (hcase1 htδ)
  set b := α * κ ^ j / 3 with hb_def
  have hb : 0 < b := by positivity
  have hκj : κ ^ j ≤ 1 := pow_le_one₀ hκ.le hκ1
  have hb1 : b ≤ α / 3 := by
    rw [hb_def]; gcongr; exact mul_le_of_le_one_right hα.le hκj
  have hp1 : (0 : ℝ) < p + 1 := by positivity
  have hnpos : (0 : ℝ) < p - j + 1 := by rw [hn]; exact_mod_cast Nat.pos_of_ne_zero hn0
  rcases le_or_gt t δ with htδ | hδt
  · -- `X ≤ (α ε / 3)^{1/(p-j+1)} ≤ t`
    have hc : 1 / (p - j + 1 : ℝ) ≤ (j + 1 : ℝ) / (p + 1) := by
      rw [div_le_div_iff₀ hnpos hp1]
      have : (j : ℝ) ≤ p := by exact_mod_cast hjp
      nlinarith
    calc b ^ (1 / (p - j + 1 : ℝ)) * ε ^ ((j + 1 : ℝ) / (p + 1))
        ≤ (α / 3) ^ (1 / (p - j + 1 : ℝ)) * ε ^ (1 / (p - j + 1 : ℝ)) := by
          exact mul_le_mul (Real.rpow_le_rpow hb.le hb1 (by positivity))
            (Real.rpow_le_rpow_of_exponent_ge hε hε1 hc) (by positivity) (by positivity)
      _ = (α * ε / 3) ^ (1 / (p - j + 1 : ℝ)) := by
          rw [← Real.mul_rpow (by positivity) hε.le]; ring_nf
      _ ≤ t := by
          rw [hn]
          exact rpow_one_div_le_of_le_pow hn0 (by positivity) ht.le (hcase1 htδ)
  · -- `b ε^{j+1} ≤ t^{p+1}`
    have h1 := h.le_of_ge hA.le ht hδ.le hδt.le hjp
    have h2 : 2 * A * δ * t ^ p + B * t ^ (p + 1) ≤ 3 * A * t ^ (p + 1) := by
      have : 2 * A * δ * t ^ p ≤ 2 * A * t ^ (p + 1) := by
        have := mul_le_mul_of_nonneg_left hδt.le (by positivity : (0 : ℝ) ≤ 2 * A * t ^ p)
        rw [pow_succ]; linarith
      have : B * t ^ (p + 1) ≤ A * t ^ (p + 1) := by gcongr
      linarith
    have h3 : (κ * ε) ^ j ≤ δ ^ j := pow_le_pow_left₀ (by positivity) hκε j
    have hkey : b * ε ^ (j + 1) ≤ t ^ (p + 1) := by
      have : b * ε ^ (j + 1) * (3 * A) = a * ε * (κ * ε) ^ j / j ! := by
        rw [hb_def, hα_def]; field_simp; ring
      rw [← mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < 3 * A), this]
      calc a * ε * (κ * ε) ^ j / j ! ≤ a * ε * δ ^ j / j ! := by gcongr
        _ ≤ 3 * A * t ^ (p + 1) := h1.trans h2
        _ = t ^ (p + 1) * (3 * A) := by ring
    have hexp : 1 / (p + 1 : ℝ) ≤ 1 / (p - j + 1 : ℝ) := by
      apply one_div_le_one_div_of_le hnpos
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    calc b ^ (1 / (p - j + 1 : ℝ)) * ε ^ ((j + 1 : ℝ) / (p + 1))
        ≤ b ^ (1 / (p + 1 : ℝ)) * ε ^ ((j + 1 : ℝ) / (p + 1)) := by
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_ge hb (hb1.trans (by linarith)) hexp) (by positivity)
      _ = (b * ε ^ (j + 1)) ^ (1 / ((p + 1 : ℕ) : ℝ)) := by
          rw [Real.mul_rpow hb.le (by positivity), ← Real.rpow_natCast ε (j + 1),
            ← Real.rpow_mul hε.le]
          push_cast
          ring_nf
      _ ≤ t := rpow_one_div_le_of_le_pow (Nat.succ_ne_zero p) (by positivity) ht.le hkey

end StepLength

end Optimization
