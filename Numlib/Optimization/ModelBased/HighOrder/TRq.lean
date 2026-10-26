import Numlib.Optimization.ModelBased.TRRun
import Numlib.Optimization.ModelBased.HighOrder.MeasureTest
import Numlib.Optimization.Complexity.Existence
import Numlib.Analysis.SpecialFunctions.FactorialSum
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder

/-!
# The high-order trust-region method TRq

The trust-region method TRq of [cartis2022evaluation] (Algorithm 12.2.1) seeks
`(ε, δ)`-approximate `q`-th order minimizers ((12.1.25)). At iteration `k` it sets the optimality
radius `δ_k = min(Δ_k, ϑ)`, computes for `j = 1, …, q` approximate optimality displacements
`d_{k,j}` ((12.2.1)) and stops when `ΔT_j(x_k, d_{k,j}) ≤ ς ε_j δ_k^j / j!` for every `j`. Otherwise
`j_k` is the least failing order, `d_k = d_{k,j_k}`, and any step `s_k ∈ B_{Δ_k}` with
`ΔT_{j_k}(x_k, s_k) ≥ ΔT_{j_k}(x_k, d_k)` ((12.2.3)) is tried with the trust-region acceptance
rule ((12.2.4)–(12.2.5)), the radius being capped by `Δ_max`.

The method is stated as a relational run predicate on top of the generic trust-region run
`Optimization.IsTRRun`, generic in
* the derivative data `D k : FormalMultilinearSeries ℝ E ℝ` used at iteration `k` (exact TRq:
  `D k = ftaylorSeries ℝ f (x k)`; inexact data in the variants of Chapter 13), and
* the feasible displacement sets `S k : Set E` (`univ` for TRq; `{d | x k + d ∈ X}` for the
  simply constrained variant TRq-SC of §14.2).

Step-1 witnesses `d k j` are required for all orders `j ∈ [1, q]` (also beyond the first failing
order, where they exist and are unused).

## Main definitions

* `Optimization.TRqParams`: the constants of Algorithm 12.2.1;
* `Optimization.trqTest`: the Step-1 termination test;
* `Optimization.IsTRqStep`: Steps 1.2 and 2 of one iteration;
* `Optimization.IsTRqRun`: a run of TRq;
* `Optimization.trqGap`: the scaled approximate criticality gap `φ̂` of (12.2.8);
* `Optimization.trqKappa`: the constant `κ_Δ` of (12.2.14).

## Main results

* `Optimization.exists_isTRqRun`: runs exist (finite dimension, closed feasible sets);
* `Optimization.IsTRqRun.trqGap_ge`: Lemma 12.2.1;
* `Optimization.IsTRqRun.le_reductionRatio`: Lemma 12.2.2;
* `Optimization.IsTRqRun.radius_ge`: Lemma 12.2.3;
* `Optimization.IsTRqRun.taylorDecrement_ge`: Lemma 12.2.4.

The one-iteration lemmas assume an abstract *model-fidelity* bound
`|f(x_k + s_k) - (f(x_k) - ΔT_{j_k}(s_k))| ≤ L ‖s_k‖^{j_k+1} / (j_k+1)!` before termination; for
exact data and `∇^{j_k} f` Lipschitz with constant `L` this is (A.19)
(`abs_sub_taylorPolynomial_le_of_lipschitz`).
-/

open Set Metric Finset
open scoped Nat

namespace Optimization

/-- The constants of the TRq method ([cartis2022evaluation], Algorithm 12.2.1, Step 0): the
trust-region constants, the maximal radius `Δ_max ≥ Δ₀` and the fraction `ς ∈ (0, 1]` of the
measure that the Step-1 displacements must achieve. (The threshold `ϑ` depends on the tolerances
and is an argument of the run predicate.) -/
structure TRqParams extends TRParams where
  /-- The maximal trust-region radius. -/
  Δmax : ℝ
  /-- The fraction of the criticality measure achieved by the Step-1 displacements. -/
  ς : ℝ
  /-- `Δ₀ ≤ Δ_max`. -/
  Δ₀_le_Δmax : Δ₀ ≤ Δmax
  /-- `ς > 0`. -/
  ς_pos : 0 < ς
  /-- `ς ≤ 1`. -/
  ς_le_one : ς ≤ 1

/-! ### Prefix minima -/

section PrefixMin

variable {α : Type*} [LinearOrder α] {u : ℕ → α}

/-- The minimum `min_{i ∈ [0, k]} u_i` of the first `k + 1` terms of a sequence. -/
def prefixMin (u : ℕ → α) (k : ℕ) : α :=
  (range (k + 1)).inf' nonempty_range_add_one u

theorem le_prefixMin_iff {k : ℕ} {c : α} : c ≤ prefixMin u k ↔ ∀ i ≤ k, c ≤ u i := by
  simp [prefixMin]

theorem prefixMin_le {i k : ℕ} (hi : i ≤ k) : prefixMin u k ≤ u i :=
  le_prefixMin_iff.1 le_rfl i hi

theorem prefixMin_mono {k k' : ℕ} (h : k ≤ k') : prefixMin u k' ≤ prefixMin u k :=
  le_prefixMin_iff.2 fun _ hi => prefixMin_le (hi.trans h)

theorem prefixMin_antitone : Antitone (prefixMin u) := fun _ _ h => prefixMin_mono h

@[simp]
theorem prefixMin_zero : prefixMin u 0 = u 0 :=
  le_antisymm (prefixMin_le le_rfl) (le_prefixMin_iff.2 fun i hi => by rw [Nat.le_zero.1 hi])

@[simp]
theorem prefixMin_succ (k : ℕ) : prefixMin u (k + 1) = min (prefixMin u k) (u (k + 1)) := by
  refine le_antisymm (le_min (prefixMin_mono (Nat.le_succ k)) (prefixMin_le le_rfl))
    (le_prefixMin_iff.2 fun i hi => ?_)
  rcases Nat.lt_or_eq_of_le hi with hi | rfl
  · exact (min_le_left _ _).trans (prefixMin_le (Nat.lt_succ_iff.1 hi))
  · exact min_le_right _ _

end PrefixMin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The run predicate -/

/-- The Step-1 termination test of TRq ([cartis2022evaluation], Algorithm 12.2.1, Step 1) at
iteration `k`: with `δ_k = min(Δ_k, ϑ)`, `ΔT_j(D_k, d_{k,j}) ≤ ς ε_j δ_k^j / j!` for all
`j ∈ [1, q]`. -/
def trqTest (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (P : TRqParams) (q : ℕ) (ε : ℕ → ℝ)
    (ϑ : ℝ) (Δ : ℕ → ℝ) (d : ℕ → ℕ → E) (k : ℕ) : Prop :=
  MeasureTestPasses (fun j => (D k).taylorDecrement j) q P.ς ε (fun _ => min (Δ k) ϑ) (d k)

theorem trqTest_iff {D : ℕ → FormalMultilinearSeries ℝ E ℝ} {P : TRqParams} {q : ℕ}
    {ε : ℕ → ℝ} {ϑ : ℝ} {Δ : ℕ → ℝ} {d : ℕ → ℕ → E} {k : ℕ} :
    trqTest D P q ε ϑ Δ d k ↔
      MeasureTestPasses (fun j => (D k).taylorDecrement j) q P.ς ε (fun _ => min (Δ k) ϑ) (d k) :=
  Iff.rfl

/-- The ratio (12.2.4) of TRq: the reduction ratio with the predicted decrease
`ΔT_{j_k}(D_k, s_k)`. -/
noncomputable def trqRatio (f : E → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (x s : ℕ → E)
    (jk : ℕ → ℕ) (k : ℕ) : ℝ :=
  reductionRatio f (x k) (s k) ((D k).taylorDecrement (jk k) (s k))

theorem trqRatio_eq {f : E → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ} {x s : ℕ → E}
    {jk : ℕ → ℕ} {k : ℕ} :
    trqRatio f D x s jk k = reductionRatio f (x k) (s k) ((D k).taylorDecrement (jk k) (s k)) :=
  rfl

/-- Steps 1.2 and 2 of one TRq iteration ([cartis2022evaluation], (12.2.2)–(12.2.3)), for data
`D`, feasible displacements `S`, optimality radius `δ`, trust-region radius `Δ`, Step-1
displacements `d`: the order `j ∈ [1, q]` is the least order failing the test, and the step `s`
is feasible, in the trust region, and decreases the order-`j` Taylor model at least as much as
`d j`. -/
structure IsTRqStep (D : FormalMultilinearSeries ℝ E ℝ) (S : Set E) (ς : ℝ) (q : ℕ)
    (ε : ℕ → ℝ) (δ Δ : ℝ) (d : ℕ → E) (j : ℕ) (s : E) : Prop where
  /-- The order lies in `[1, q]`. -/
  order_mem : j ∈ Finset.Icc 1 q
  /-- The test fails at order `j` ((12.2.2)). -/
  lt_taylorDecrement : ς * ε j * δ ^ j / j ! < D.taylorDecrement j (d j)
  /-- The test passes at the lower orders. -/
  taylorDecrement_le_of_lt :
    ∀ i ∈ Finset.Icc 1 q, i < j → D.taylorDecrement i (d i) ≤ ς * ε i * δ ^ i / i !
  /-- The step lies in the trust region and is feasible. -/
  mem : s ∈ closedBall 0 Δ ∩ S
  /-- The step decreases the model at least as much as the Step-1 displacement ((12.2.3)). -/
  taylorDecrement_le : D.taylorDecrement j (d j) ≤ D.taylorDecrement j s

/-- A run of the TRq method ([cartis2022evaluation], Algorithm 12.2.1) with derivative data
`D k` and feasible displacement sets `S k` at iteration `k`, constants `P`, order `q`, tolerances
`ε`, threshold `ϑ`, iterates `x`, steps `s`, radii `Δ`, orders `jk` and Step-1 displacements `d`.
Writing `δ_k = min(Δ_k, ϑ)`:
* Steps 2–4 form a trust-region run (`Optimization.IsTRRun`) with termination test
  `Optimization.trqTest`, step condition `Optimization.IsTRqStep` and ratio
  `Optimization.trqRatio`;
* the displacements `d k j` are approximate optimality displacements ((12.2.1)) at every
  iteration up to and including termination;
* the radii stay below `Δ_max` ((12.2.5)).

Exact TRq: `D k = ftaylorSeries ℝ f (x k)`, `S k = univ`; TRq-SC: `S k = {d | x k + d ∈ X}`. -/
structure IsTRqRun (f : E → ℝ) (D : ℕ → FormalMultilinearSeries ℝ E ℝ) (S : ℕ → Set E)
    (P : TRqParams) (q : ℕ) (ε : ℕ → ℝ) (ϑ : ℝ) (x s : ℕ → E) (Δ : ℕ → ℝ) (jk : ℕ → ℕ)
    (d : ℕ → ℕ → E) : Prop extends
    IsTRRun P.toTRParams (trqTest D P q ε ϑ Δ d)
      (fun k => IsTRqStep (D k) (S k) P.ς q ε (min (Δ k) ϑ) (Δ k) (d k) (jk k) (s k))
      (trqRatio f D x s jk) x s Δ where
  /-- Step 1.1: approximate optimality displacements at every iteration up to termination. -/
  witness : ∀ k, (∀ i < k, ¬ trqTest D P q ε ϑ Δ d i) → ∀ j ∈ Finset.Icc 1 q,
    IsApproxMeasureStep ((D k).taylorDecrement j) (min (Δ k) ϑ) (S k) P.ς (d k j)
  /-- The cap `Δ_{k+1} ≤ Δ_max` of (12.2.5). -/
  cap : UntilHit (trqTest D P q ε ϑ Δ d) fun k => Δ (k + 1) ≤ P.Δmax

/-! ### Existence of runs -/

/-- The state of a TRq run at iteration `k`: iterate, radius and Step-1 displacements at `k`,
and the step and order chosen at iteration `k - 1`. -/
private structure TRqState (E : Type*) where
  x : E
  Δ : ℝ
  d : ℕ → E
  s : E
  j : ℕ

/-- **Existence of TRq runs** ([cartis2022evaluation], Algorithm 12.2.1, well-posedness). In
finite dimension, for data `J y` and feasible displacement sets `C' y` depending on the current
iterate `y`, with every `C' y` closed and containing `0`, and `ϑ ≥ 0`, every starting point `x₀`
starts a TRq run. (Construction: exact maximizers as Step-1 displacements, `s_k = d_k`, and the
canonical radius update, which never increases the radius.) -/
theorem exists_isTRqRun [FiniteDimensional ℝ E] (f : E → ℝ)
    (J : E → FormalMultilinearSeries ℝ E ℝ) (C' : E → Set E) (hC : ∀ y, IsClosed (C' y))
    (hC0 : ∀ y, (0 : E) ∈ C' y) (P : TRqParams) (q : ℕ) (ε : ℕ → ℝ) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (x₀ : E) :
    ∃ (x s : ℕ → E) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → E), x 0 = x₀ ∧
      IsTRqRun f (fun k => J (x k)) (fun k => C' (x k)) P q ε ϑ x s Δ jk d := by
  classical
  -- witnesses at any admissible point
  have hwit : ∀ (y : E) (Δ : ℝ), 0 < Δ → ∃ d : ℕ → E, ∀ j,
      IsApproxMeasureStep ((J y).taylorDecrement j) (min Δ ϑ) (C' y) P.ς (d j) := by
    intro y Δ hΔ
    choose d hd using fun j => exists_isApproxMeasureStep_taylorDecrement (J y) j (hC y)
      (hC0 y) (le_min hΔ.le hϑ) P.ς_le_one
    exact ⟨d, hd⟩
  let wit : E → ℝ → (ℕ → E) → Prop := fun y Δ d => ∀ j,
    IsApproxMeasureStep ((J y).taylorDecrement j) (min Δ ϑ) (C' y) P.ς (d j)
  let inv : ℕ → TRqState E → Prop := fun _ a => 0 < a.Δ ∧ a.Δ ≤ P.Δmax ∧ wit a.x a.Δ a.d
  let stop : ℕ → TRqState E → Prop := fun _ a =>
    MeasureTestPasses (fun j => (J a.x).taylorDecrement j) q P.ς ε (fun _ => min a.Δ ϑ) a.d
  let step : ℕ → TRqState E → TRqState E → Prop := fun k a b => inv (k + 1) b ∧
    IsTRqStep (J a.x) (C' a.x) P.ς q ε (min a.Δ ϑ) a.Δ a.d b.j b.s ∧
    TRAcceptance P.toTRParams
      (reductionRatio f a.x b.s ((J a.x).taylorDecrement b.j b.s)) a.x b.s b.x a.Δ b.Δ
  obtain ⟨d₀, hd₀⟩ := hwit x₀ P.Δ₀ P.Δ₀_pos
  obtain ⟨r, hr0, hr⟩ := exists_run_of_forall_exists_of_invariant (α := TRqState E)
    (init := fun a => a.x = x₀ ∧ a.Δ = P.Δ₀ ∧ wit a.x a.Δ a.d) (inv := inv) (stop := stop)
    (step := step) ⟨⟨x₀, P.Δ₀, d₀, 0, 0⟩, rfl, rfl, hd₀⟩
    (fun a ⟨_, hΔ, hw⟩ => ⟨hΔ ▸ P.Δ₀_pos, hΔ ▸ P.Δ₀_le_Δmax, hw⟩)
    (by
      intro k a ⟨hΔ, hΔmax, hw⟩ hstop
      obtain ⟨j, hj, hlt, hle⟩ := exists_lt_of_not_measureTestPasses hstop
      set ρ := reductionRatio f a.x (a.d j) ((J a.x).taylorDecrement j (a.d j))
      obtain ⟨Δ', hacc, hΔ'le, hΔ'pos⟩ :=
        exists_trAcceptance P.toTRParams ρ a.x (a.d j) hΔ.le
      set x' := if P.η₁ ≤ ρ then a.x + a.d j else a.x
      obtain ⟨d', hd'⟩ := hwit x' Δ' (hΔ'pos hΔ)
      have hinv : inv (k + 1) ⟨x', Δ', d', a.d j, j⟩ := ⟨hΔ'pos hΔ, hΔ'le.trans hΔmax, hd'⟩
      refine ⟨⟨x', Δ', d', a.d j, j⟩, hinv, hinv, ?_, hacc⟩
      have hdm := (hw j).1
      refine ⟨hj, hlt, hle, ⟨?_, hdm.2⟩, le_rfl⟩
      exact closedBall_subset_closedBall (min_le_left _ _) hdm.1)
  -- the run: `x, Δ, d` from `r k`; `s, jk` from `r (k + 1)`
  refine ⟨fun k => (r k).x, fun k => (r (k + 1)).s, fun k => (r k).Δ, fun k => (r (k + 1)).j,
    fun k => (r k).d, hr0.1, ⟨⟨hr0.2.1, fun k hk => (hr k hk).2.2.1,
    fun k hk => (hr k hk).2.2.2⟩, ?_, fun k hk => (hr k hk).2.1.2.1⟩⟩
  intro k hk j _
  rcases k with _ | k
  · exact hr0.2.2 j
  · exact (hr k fun i hi => hk i (Nat.lt_succ_of_le hi)).2.1.2.2 j

/-! ### One-iteration lemmas -/

/-- The scaled approximate criticality gap ([cartis2022evaluation], (12.2.8)):
`φ̂ = j! ΔT_j(D, d) / δ^j`, for order `j`, optimality radius `δ` and displacement `d`. -/
noncomputable def trqGap (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) (δ : ℝ) (d : E) : ℝ :=
  j ! * D.taylorDecrement j d / δ ^ j

theorem trqGap_def (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) (δ : ℝ) (d : E) :
    trqGap D j δ d = j ! * D.taylorDecrement j d / δ ^ j :=
  rfl

/-- For `δ > 0`, `ΔT_j(D, d) = φ̂ δ^j / j!`. -/
theorem trqGap_mul_pow_div (D : FormalMultilinearSeries ℝ E ℝ) (j : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (d : E) : trqGap D j δ d * δ ^ j / j ! = D.taylorDecrement j d := by
  have := pow_pos hδ j
  have : (0 : ℝ) < j ! := by exact_mod_cast j.factorial_pos
  rw [trqGap_def]
  field_simp

/-- The constant `κ_Δ` of [cartis2022evaluation], (12.2.14):
`γ₁ (1 - η₂) / L · min(ϑ, Δ₀ δ₀^q / (2 q! M))` with `δ₀ = min(Δ₀, ϑ)`, where `L` is the
model-fidelity constant and `M` bounds the norms of the derivative data at `x₀` of orders
`1, …, q` (in the book, `M = max_{i ∈ [1, q]} ‖∇^i f(x₀)‖`). -/
noncomputable def trqKappa (P : TRqParams) (L ϑ M : ℝ) (q : ℕ) : ℝ :=
  P.γ₁ * (1 - P.η₂) / L * min ϑ (P.Δ₀ * min P.Δ₀ ϑ ^ q / (2 * q ! * M))


theorem trqKappa_pos {P : TRqParams} {L ϑ M : ℝ} {q : ℕ} (hL : 0 < L) (hϑ : 0 < ϑ)
    (hM : 0 < M) : 0 < trqKappa P L ϑ M q := by
  have := P.Δ₀_pos
  have : (0 : ℝ) < q ! := by exact_mod_cast q.factorial_pos
  unfold trqKappa
  have := P.γ₁_pos
  have := P.one_sub_η₂_pos
  positivity

/-- `κ_Δ ≤ γ₁ (1 - η₂) ϑ / L`. -/
theorem trqKappa_le {P : TRqParams} {L ϑ M : ℝ} {q : ℕ} (hL : 0 < L) :
    trqKappa P L ϑ M q ≤ P.γ₁ * (1 - P.η₂) / L * ϑ := by
  have := P.γ₁_pos
  have := P.one_sub_η₂_pos
  exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)

/-- `κ_Δ ≤ γ₁` when `L ≥ 1` and `ϑ ≤ 1`. -/
theorem trqKappa_le_γ₁ {P : TRqParams} {L ϑ M : ℝ} {q : ℕ} (hL : 1 ≤ L) (hϑ1 : ϑ ≤ 1) :
    trqKappa P L ϑ M q ≤ P.γ₁ := by
  refine (trqKappa_le (by linarith)).trans ?_
  have := P.γ₁_pos
  have := P.η₂_pos
  have h1 : (1 - P.η₂) / L ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  calc P.γ₁ * (1 - P.η₂) / L * ϑ = P.γ₁ * ((1 - P.η₂) / L * ϑ) := by ring
    _ ≤ P.γ₁ * 1 := by
        gcongr
        rcases le_total 0 ϑ with h | h
        · calc (1 - P.η₂) / L * ϑ ≤ 1 * 1 := by
                gcongr
            _ = 1 := one_mul 1
        · have : (1 - P.η₂) / L * ϑ ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (div_nonneg P.one_sub_η₂_pos.le (by linarith)) h
          linarith
    _ = P.γ₁ := mul_one _

/-- `κ_Δ < 1` when `L ≥ 1` and `ϑ ≤ 1`. -/
theorem trqKappa_lt_one {P : TRqParams} {L ϑ M : ℝ} {q : ℕ} (hL : 1 ≤ L) (hϑ1 : ϑ ≤ 1) :
    trqKappa P L ϑ M q < 1 :=
  (trqKappa_le_γ₁ hL hϑ1).trans_lt P.γ₁_lt_one

namespace IsTRqRun

variable {f : E → ℝ} {D : ℕ → FormalMultilinearSeries ℝ E ℝ} {S : ℕ → Set E} {P : TRqParams}
  {q : ℕ} {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → E} {Δ : ℕ → ℝ} {jk : ℕ → ℕ} {d : ℕ → ℕ → E}
  (h : IsTRqRun f D S P q ε ϑ x s Δ jk d)
include h

/-- The step conditions at an iteration before termination. -/
theorem isTRqStep {k : ℕ} (hk : ∀ i ≤ k, ¬ trqTest D P q ε ϑ Δ d i) :
    IsTRqStep (D k) (S k) P.ς q ε (min (Δ k) ϑ) (Δ k) (d k) (jk k) (s k) :=
  h.step k hk

/-- The radii are positive up to (and including) termination. -/
theorem delta_pos' {k : ℕ} (hk : ∀ i < k, ¬ trqTest D P q ε ϑ Δ d i) : 0 < Δ k :=
  h.delta_pos hk k le_rfl

/-- The optimality radius `δ_k = min(Δ_k, ϑ)` is positive up to termination when `ϑ > 0`. -/
theorem radius_pos (hϑ : 0 < ϑ) {k : ℕ} (hk : ∀ i < k, ¬ trqTest D P q ε ϑ Δ d i) :
    0 < min (Δ k) ϑ :=
  lt_min (h.delta_pos' hk) hϑ

/-- The radii stay below `Δ_max` up to (and including) termination. -/
theorem delta_le_max {k : ℕ} (hk : ∀ i < k, ¬ trqTest D P q ε ϑ Δ d i) : Δ k ≤ P.Δmax := by
  rcases k with _ | k
  · rw [h.delta_zero]; exact P.Δ₀_le_Δmax
  · exact h.cap k fun i hi => hk i (Nat.lt_succ_of_le hi)

/-- Up to termination, `φ̂_k δ_k^{j_k} / j_k! = ΔT_{j_k}(D_k, d_{k,j_k})` (definition (12.2.8)). -/
theorem trqGap_mul_pow_div_eq (hϑ : 0 < ϑ) {k : ℕ} (hk : ∀ i < k, ¬ trqTest D P q ε ϑ Δ d i) :
    trqGap (D k) (jk k) (min (Δ k) ϑ) (d k (jk k)) * min (Δ k) ϑ ^ jk k / (jk k) ! =
      (D k).taylorDecrement (jk k) (d k (jk k)) :=
  trqGap_mul_pow_div _ _ (h.radius_pos hϑ hk) _

/-- `ς ε_{j_k} < φ̂_k` before termination. -/
theorem lt_trqGap (hϑ : 0 < ϑ) {k : ℕ} (hk : ∀ i ≤ k, ¬ trqTest D P q ε ϑ Δ d i) :
    P.ς * ε (jk k) < trqGap (D k) (jk k) (min (Δ k) ϑ) (d k (jk k)) := by
  have hδ := h.radius_pos hϑ fun i hi => hk i hi.le
  have hlt := (h.isTRqStep hk).lt_taylorDecrement
  rw [← h.trqGap_mul_pow_div_eq hϑ fun i hi => hk i hi.le] at hlt
  have : (0 : ℝ) < (jk k) ! := by exact_mod_cast (jk k).factorial_pos
  have := pow_pos hδ (jk k)
  rw [div_lt_div_iff_of_pos_right (by positivity)] at hlt
  exact lt_of_mul_lt_mul_right hlt this.le

/-- (12.2.10): before termination, `φ̂_k δ_k^{j_k} / j_k! ≤ ΔT_{j_k}(D_k, s_k)`. -/
theorem trqGap_mul_pow_div_le (hϑ : 0 < ϑ) {k : ℕ} (hk : ∀ i ≤ k, ¬ trqTest D P q ε ϑ Δ d i) :
    trqGap (D k) (jk k) (min (Δ k) ϑ) (d k (jk k)) * min (Δ k) ϑ ^ jk k / (jk k) ! ≤
      (D k).taylorDecrement (jk k) (s k) := by
  rw [h.trqGap_mul_pow_div_eq hϑ fun i hi => hk i hi.le]
  exact (h.isTRqStep hk).taylorDecrement_le

/-- **Lemma 12.2.1** ([cartis2022evaluation], (12.2.9)–(12.2.10)). If `ϑ > 0` and `εmin ≤ ε_j` for
all `j ∈ [1, q]`, then at every iteration `k` before termination `ς εmin ≤ min_{i ≤ k} φ̂_i`
(12.2.9) and `φ̂_k δ_k^{j_k} / j_k! ≤ ΔT_{j_k}(D_k, s_k)` (12.2.10). -/
theorem trqGap_ge (hϑ : 0 < ϑ) {εmin : ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, εmin ≤ ε j) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ trqTest D P q ε ϑ Δ d i) :
    P.ς * εmin ≤ prefixMin (fun i => trqGap (D i) (jk i) (min (Δ i) ϑ) (d i (jk i))) k ∧
      trqGap (D k) (jk k) (min (Δ k) ϑ) (d k (jk k)) * min (Δ k) ϑ ^ jk k / (jk k) ! ≤
        (D k).taylorDecrement (jk k) (s k) := by
  refine ⟨le_prefixMin_iff.2 fun i hi => ?_, h.trqGap_mul_pow_div_le hϑ hk⟩
  have hi' : ∀ i' ≤ i, ¬ trqTest D P q ε ϑ Δ d i' := fun i' h' => hk i' (h'.trans hi)
  refine le_trans ?_ (h.lt_trqGap hϑ hi').le
  exact mul_le_mul_of_nonneg_left (hε _ (h.isTRqStep hi').order_mem) P.ς_pos.le

/-- The scaled gaps are positive before termination when the tolerances are nonnegative. -/
theorem trqGap_pos (hϑ : 0 < ϑ) (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ trqTest D P q ε ϑ Δ d i) :
    0 < trqGap (D k) (jk k) (min (Δ k) ϑ) (d k (jk k)) :=
  lt_of_le_of_lt (mul_nonneg P.ς_pos.le (hε _ (h.isTRqStep hk).order_mem)) (h.lt_trqGap hϑ hk)

/-- **Lemma 12.2.2** ([cartis2022evaluation]): condition for a very successful iteration. Let `k`
be an iteration before termination with model fidelity
`|f(x_k + s_k) - (f(x_k) - ΔT_{j_k}(s_k))| ≤ L ‖s_k‖^{j_k+1} / (j_k+1)!` (`L > 0`) and
`Δ_k ≤ min(ϑ, (1 - η₂) φ̂_k / L)` ((12.2.11)). Then `δ_k = Δ_k`, `ρ_k ≥ η₂` and
`Δ_k ≤ Δ_{k+1}`. -/
theorem le_reductionRatio {L : ℝ} (hL : 0 < L) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ trqTest D P q ε ϑ Δ d i)
    (hfid : |f (x k + s k) - (f (x k) - (D k).taylorDecrement (jk k) (s k))| ≤
      L / (jk k + 1)! * ‖s k‖ ^ (jk k + 1))
    (hΔ : Δ k ≤ min ϑ ((1 - P.η₂) * trqGap (D k) (jk k) (min (Δ k) ϑ) (d k (jk k)) / L)) :
    min (Δ k) ϑ = Δ k ∧ P.η₂ ≤ trqRatio f D x s jk k ∧ Δ k ≤ Δ (k + 1) := by
  have hΔpos := h.delta_pos' fun i hi => hk i hi.le
  have hδ : min (Δ k) ϑ = Δ k := min_eq_left (hΔ.trans (min_le_left _ _))
  have hϑ : 0 < ϑ := hΔpos.trans_le (hΔ.trans (min_le_left _ _))
  set g := trqGap (D k) (jk k) (min (Δ k) ϑ) (d k (jk k))
  set j := jk k
  have hstep := h.isTRqStep hk
  have hs : ‖s k‖ ≤ Δ k := mem_closedBall_zero_iff.1 hstep.mem.1
  have hg : L * Δ k ≤ (1 - P.η₂) * g := by
    have := hΔ.trans (min_le_right _ _)
    rwa [le_div_iff₀ hL, mul_comm] at this
  have hpred : g * Δ k ^ j / j ! ≤ (D k).taylorDecrement j (s k) := by
    have := h.trqGap_mul_pow_div_le hϑ hk
    calc g * Δ k ^ j / j ! = g * min (Δ k) ϑ ^ j / j ! := by rw [hδ]
      _ ≤ _ := this
  have hfac : (0 : ℝ) < j ! := by exact_mod_cast j.factorial_pos
  have hfac1 : (j ! : ℝ) ≤ (j + 1) ! := by exact_mod_cast Nat.factorial_le (Nat.le_succ j)
  have hgpos : 0 < g := by
    have := mul_pos hL hΔpos
    have := P.one_sub_η₂_pos
    nlinarith
  have hpredpos : 0 < (D k).taylorDecrement j (s k) :=
    lt_of_lt_of_le (by positivity) hpred
  have hρ : P.η₂ ≤ trqRatio f D x s jk k := by
    have key : |f (x k + s k) - (f (x k) - (D k).taylorDecrement j (s k))| ≤
        (1 - P.η₂) * (D k).taylorDecrement j (s k) := by
      refine hfid.trans ?_
      calc L / (j + 1) ! * ‖s k‖ ^ (j + 1) ≤ L / j ! * Δ k ^ (j + 1) := by
            gcongr
        _ = L * Δ k * Δ k ^ j / j ! := by ring
        _ ≤ (1 - P.η₂) * g * Δ k ^ j / j ! := by gcongr
        _ = (1 - P.η₂) * (g * Δ k ^ j / j !) := by ring
        _ ≤ (1 - P.η₂) * (D k).taylorDecrement j (s k) :=
            mul_le_mul_of_nonneg_left hpred P.one_sub_η₂_pos.le
    have := le_reductionRatio_of_abs_sub_le hpredpos key
    rw [trqRatio_eq]
    linarith
  exact ⟨hδ, hρ, (h.update hk).le_of_very_successful hρ⟩

/-- Positivity of the bound `M` on the initial data when the run does not stop at once: if
`‖D 0 i‖ ≤ M` for `i ∈ [1, q]`, `ε_j ≥ 0` and `ϑ ≥ 0`, and the test fails at `k = 0`, then
`M > 0`. -/
theorem pos_of_not_trqTest_zero (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) (hϑ : 0 ≤ ϑ) {M : ℝ}
    (hM : ∀ i ∈ Finset.Icc 1 q, ‖D 0 i‖ ≤ M) (h0 : ¬ trqTest D P q ε ϑ Δ d 0) : 0 < M := by
  have hstep := h.isTRqStep (k := 0) fun i hi => by rwa [Nat.le_zero.1 hi]
  set j := jk 0
  have hjq := Finset.mem_Icc.1 hstep.order_mem
  have hδ : 0 ≤ min (Δ 0) ϑ := le_min (h.delta_pos' (k := 0) (by simp)).le hϑ
  have hlow : 0 < (D 0).taylorDecrement j (d 0 j) := by
    refine lt_of_le_of_lt ?_ hstep.lt_taylorDecrement
    have := hε j hstep.order_mem
    have := P.ς_pos
    positivity
  by_contra hM0
  push Not at hM0
  have hb := (D 0).abs_taylorDecrement_le j (d 0 j)
  have : ∑ i ∈ Finset.Icc 1 j, ‖D 0 i‖ * ‖d 0 j‖ ^ i / i ! ≤ 0 := by
    refine Finset.sum_nonpos fun i hi => ?_
    have hi' := Finset.mem_Icc.1 hi
    have : ‖D 0 i‖ ≤ 0 := (hM i (Finset.mem_Icc.2 ⟨hi'.1, hi'.2.trans hjq.2⟩)).trans hM0
    have : ‖D 0 i‖ = 0 := le_antisymm this (norm_nonneg _)
    simp [this]
  have := abs_le.1 (hb.trans this)
  linarith

/-- Bound on the initial scaled gap ([cartis2022evaluation], proof of Lemma 12.2.3): if
`‖D 0 i‖ ≤ M` for `i ∈ [1, q]`, `0 < ϑ ≤ 1` and the test fails at `k = 0`, then
`φ̂_0 ≤ 2 q! M / δ₀^q`. -/
theorem trqGap_zero_le (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {M : ℝ}
    (hM : ∀ i ∈ Finset.Icc 1 q, ‖D 0 i‖ ≤ M) (h0 : ¬ trqTest D P q ε ϑ Δ d 0) :
    trqGap (D 0) (jk 0) (min (Δ 0) ϑ) (d 0 (jk 0)) ≤ 2 * q ! * M / min (Δ 0) ϑ ^ q := by
  have hk0 : ∀ i ≤ 0, ¬ trqTest D P q ε ϑ Δ d i := fun i hi => by rwa [Nat.le_zero.1 hi]
  have hstep := h.isTRqStep hk0
  set j := jk 0
  set δ := min (Δ 0) ϑ
  have hjq := Finset.mem_Icc.1 hstep.order_mem
  have hδ : 0 < δ := h.radius_pos hϑ (k := 0) (by simp)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans hϑ1
  have hd : ‖d 0 j‖ ≤ δ := (h.witness 0 (by simp) j hstep.order_mem).norm_le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM j hstep.order_mem)
  -- `ΔT_j(d) ≤ 2 M δ`
  have hT : (D 0).taylorDecrement j (d 0 j) ≤ 2 * M * δ := by
    refine (le_abs_self _).trans (((D 0).abs_taylorDecrement_le_of_norm_le j hd).trans ?_)
    calc ∑ i ∈ Finset.Icc 1 j, ‖D 0 i‖ * δ ^ i / i !
        ≤ ∑ i ∈ Finset.Icc 1 j, M * (δ ^ i / i !) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_Icc.1 hi
          rw [mul_div_assoc]
          gcongr
          exact hM i (Finset.mem_Icc.2 ⟨hi'.1, hi'.2.trans hjq.2⟩)
      _ = M * ∑ i ∈ Finset.Icc 1 j, δ ^ i / i ! := (Finset.mul_sum _ _ _).symm
      _ ≤ M * (2 * δ) := by gcongr; exact sum_pow_div_factorial_le_two_mul hδ.le hδ1 j
      _ = 2 * M * δ := by ring
  have hfac : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hjq.2
  have hfacpos : (0 : ℝ) < j ! := by exact_mod_cast j.factorial_pos
  have hpow : δ ^ (q + 1) ≤ δ ^ j := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have hδj := pow_pos hδ j
  have hδq := pow_pos hδ q
  rw [trqGap_def, div_le_div_iff₀ hδj hδq]
  have hfq : (0 : ℝ) ≤ q ! := by positivity
  have hA : (j ! : ℝ) * (D 0).taylorDecrement j (d 0 j) ≤ q ! * (2 * M * δ) := by
    rcases le_or_gt ((D 0).taylorDecrement j (d 0 j)) 0 with hT0 | hT0
    · have : (j ! : ℝ) * (D 0).taylorDecrement j (d 0 j) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hfacpos.le hT0
      have : 0 ≤ (q ! : ℝ) * (2 * M * δ) := by positivity
      linarith
    · exact mul_le_mul hfac hT hT0.le hfq
  calc (j ! : ℝ) * (D 0).taylorDecrement j (d 0 j) * δ ^ q ≤ q ! * (2 * M * δ) * δ ^ q := by
        gcongr
    _ = 2 * q ! * M * δ ^ (q + 1) := by ring
    _ ≤ 2 * q ! * M * δ ^ j := by gcongr

/-- The initial scaled gap and `κ_Δ` ([cartis2022evaluation], proof of Lemma 12.2.3): under the
hypotheses of `IsTRqRun.trqGap_zero_le` and `L ≥ 1`, `κ_Δ φ̂_0 ≤ Δ₀`. -/
theorem trqKappa_mul_trqGap_zero_le {L M : ℝ} (hL : 1 ≤ L) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) (hM : ∀ i ∈ Finset.Icc 1 q, ‖D 0 i‖ ≤ M)
    (h0 : ¬ trqTest D P q ε ϑ Δ d 0) :
    trqKappa P L ϑ M q * trqGap (D 0) (jk 0) (min (Δ 0) ϑ) (d 0 (jk 0)) ≤ P.Δ₀ := by
  have hk0 : ∀ i ≤ 0, ¬ trqTest D P q ε ϑ Δ d i := fun i hi => by rwa [Nat.le_zero.1 hi]
  have hMpos := h.pos_of_not_trqTest_zero hε hϑ.le hM h0
  have hgpos := h.trqGap_pos hϑ hε hk0
  have hg := h.trqGap_zero_le hϑ hϑ1 hM h0
  rw [h.delta_zero] at hg hgpos ⊢
  set g := trqGap (D 0) (jk 0) (min P.Δ₀ ϑ) (d 0 (jk 0))
  have hδ : 0 < min P.Δ₀ ϑ := lt_min P.Δ₀_pos hϑ
  have hδq := pow_pos hδ q
  have hfac : (0 : ℝ) < q ! := by exact_mod_cast q.factorial_pos
  have hc : 0 ≤ P.γ₁ * (1 - P.η₂) / L := by
    have := P.γ₁_pos; have := P.one_sub_η₂_pos; positivity
  have hc1 : P.γ₁ * (1 - P.η₂) / L ≤ 1 := by
    rw [div_le_one (by linarith)]
    have := P.γ₁_pos; have := P.γ₁_lt_one; have := P.η₂_pos; have := P.one_sub_η₂_pos
    nlinarith
  have hB : 0 < 2 * q ! * M := by positivity
  calc trqKappa P L ϑ M q * g
      ≤ P.γ₁ * (1 - P.η₂) / L * (P.Δ₀ * min P.Δ₀ ϑ ^ q / (2 * q ! * M)) *
          (2 * q ! * M / min P.Δ₀ ϑ ^ q) := by
        unfold trqKappa
        have := P.Δ₀_pos
        gcongr
        exact min_le_right (a := ϑ) _
    _ = P.γ₁ * (1 - P.η₂) / L * P.Δ₀ := by field_simp
    _ ≤ 1 * P.Δ₀ := mul_le_mul_of_nonneg_right hc1 P.Δ₀_pos.le
    _ = P.Δ₀ := one_mul _

/-- **Lemma 12.2.3** ([cartis2022evaluation], (12.2.13)): lower bound on the trust-region radius.
Assume `L ≥ 1`, `0 < ϑ ≤ 1`, `ε_j ≥ 0`, `‖D 0 i‖ ≤ M` for `i ∈ [1, q]`, and the model fidelity
`|f(x_k + s_k) - (f(x_k) - ΔT_{j_k}(s_k))| ≤ L ‖s_k‖^{j_k+1} / (j_k+1)!` at every iteration before
termination. Then for every `k` before termination (so the test fails at `0`) both `Δ_k` and
`Δ_{k+1}` are at least `min(γ₁ ϑ, κ_Δ min_{i ≤ k} φ̂_i)`, with `κ_Δ = trqKappa P L ϑ M q`
((12.2.14)). (The bound on `Δ_{k+1}` gives the bound at the termination index with the minimum
over the earlier iterations.) -/
theorem radius_ge {L M : ℝ} (hL : 1 ≤ L) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) (hM : ∀ i ∈ Finset.Icc 1 q, ‖D 0 i‖ ≤ M)
    (hfid : ∀ k, (∀ i ≤ k, ¬ trqTest D P q ε ϑ Δ d i) →
      |f (x k + s k) - (f (x k) - (D k).taylorDecrement (jk k) (s k))| ≤
        L / (jk k + 1)! * ‖s k‖ ^ (jk k + 1))
    {k : ℕ} (hk : ∀ i ≤ k, ¬ trqTest D P q ε ϑ Δ d i) :
    min (P.γ₁ * ϑ) (trqKappa P L ϑ M q *
        prefixMin (fun i => trqGap (D i) (jk i) (min (Δ i) ϑ) (d i (jk i))) k) ≤ Δ k ∧
      min (P.γ₁ * ϑ) (trqKappa P L ϑ M q *
        prefixMin (fun i => trqGap (D i) (jk i) (min (Δ i) ϑ) (d i (jk i))) k) ≤ Δ (k + 1) := by
  have h0 : ¬ trqTest D P q ε ϑ Δ d 0 := hk 0 (Nat.zero_le k)
  set g : ℕ → ℝ := fun i => trqGap (D i) (jk i) (min (Δ i) ϑ) (d i (jk i)) with hgdef
  set κ := trqKappa P L ϑ M q
  have hL0 : 0 < L := by linarith
  have hc : 0 ≤ (1 - P.η₂) / L := div_nonneg P.one_sub_η₂_pos.le hL0.le
  have hMpos := h.pos_of_not_trqTest_zero hε hϑ.le hM h0
  have hκ : 0 < κ := trqKappa_pos hL0 hϑ hMpos
  set θ : ℕ → ℝ := fun i => min ϑ ((1 - P.η₂) / L * prefixMin g i)
  have hθ : ∀ i, θ (i + 1) ≤ θ i := fun i =>
    min_le_min le_rfl (mul_le_mul_of_nonneg_left (prefixMin_mono (Nat.le_succ i)) hc)
  have hforce : ∀ i < k + 1, Δ i < θ i → P.η₂ ≤ trqRatio f D x s jk i := by
    intro i hi hΔi
    have hi' : ∀ i' ≤ i, ¬ trqTest D P q ε ϑ Δ d i' := fun i' h' => hk i' (h'.trans (by omega))
    refine (h.le_reductionRatio hL0 hi' (hfid i hi') ?_).2.1
    refine le_min (hΔi.le.trans (min_le_left _ _)) (hΔi.le.trans ((min_le_right _ _).trans ?_))
    calc (1 - P.η₂) / L * prefixMin g i ≤ (1 - P.η₂) / L * g i :=
          mul_le_mul_of_nonneg_left (prefixMin_le le_rfl) hc
      _ = (1 - P.η₂) * g i / L := by ring
  have hpm : 0 ≤ prefixMin g k :=
    le_prefixMin_iff.2 fun i hi => (h.trqGap_pos hϑ hε fun i' h' => hk i' (h'.trans hi)).le
  have hbound : min (P.γ₁ * ϑ) (κ * prefixMin g k) ≤ min P.Δ₀ (P.γ₁ * θ k) := by
    refine le_min ((min_le_right _ _).trans ?_) ?_
    · calc κ * prefixMin g k ≤ κ * g 0 :=
            mul_le_mul_of_nonneg_left (prefixMin_le (Nat.zero_le k)) hκ.le
        _ ≤ P.Δ₀ := h.trqKappa_mul_trqGap_zero_le hL hϑ hϑ1 hε hM h0
    · rw [mul_min_of_nonneg _ _ P.γ₁_pos.le]
      refine min_le_min le_rfl ?_
      have hκle : κ ≤ P.γ₁ * ((1 - P.η₂) / L) := by
        refine (trqKappa_le hL0).trans ?_
        rw [← mul_div_assoc]
        exact mul_le_of_le_one_right (div_nonneg (mul_nonneg P.γ₁_pos.le
          P.one_sub_η₂_pos.le) hL0.le) hϑ1
      calc κ * prefixMin g k ≤ P.γ₁ * ((1 - P.η₂) / L) * prefixMin g k := by gcongr
        _ = P.γ₁ * ((1 - P.η₂) / L * prefixMin g k) := by ring
  have hK : ∀ i < k + 1, ¬ trqTest D P q ε ϑ Δ d i := fun i hi => hk i (Nat.lt_succ_iff.1 hi)
  refine ⟨hbound.trans ?_, hbound.trans ?_⟩
  · exact h.toIsTRRun.delta_ge hK (fun i _ => hθ i) hforce k (Nat.le_succ k)
  · exact h.toIsTRRun.delta_succ_ge hK (fun i _ => hθ i) hforce k (Nat.lt_succ_self k)

/-- The minimal radius in the proof of [cartis2022evaluation], Theorem 12.2.5: under the
hypotheses of `IsTRqRun.radius_ge` with `0 < εmin ≤ ϑ` and `εmin ≤ ε_j` for `j ∈ [1, q]`,
`ς κ_Δ εmin ≤ Δ_k` for every `k` up to and including the first termination index. -/
theorem mul_le_delta {L M εmin : ℝ} (hL : 1 ≤ L) (hϑ1 : ϑ ≤ 1) (hεmin : 0 < εmin)
    (hεϑ : εmin ≤ ϑ) (hε : ∀ j ∈ Finset.Icc 1 q, εmin ≤ ε j)
    (hM : ∀ i ∈ Finset.Icc 1 q, ‖D 0 i‖ ≤ M) (h0 : ¬ trqTest D P q ε ϑ Δ d 0)
    (hfid : ∀ k, (∀ i ≤ k, ¬ trqTest D P q ε ϑ Δ d i) →
      |f (x k + s k) - (f (x k) - (D k).taylorDecrement (jk k) (s k))| ≤
        L / (jk k + 1)! * ‖s k‖ ^ (jk k + 1))
    {k : ℕ} (hk : ∀ i < k, ¬ trqTest D P q ε ϑ Δ d i) :
    P.ς * trqKappa P L ϑ M q * εmin ≤ Δ k := by
  have hϑ : 0 < ϑ := hεmin.trans_le hεϑ
  have hε0 : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j := fun j hj => hεmin.le.trans (hε j hj)
  have hMpos := h.pos_of_not_trqTest_zero hε0 hϑ.le hM h0
  have hκ : 0 < trqKappa P L ϑ M q := trqKappa_pos (by linarith) hϑ hMpos
  have hk0 : ∀ i ≤ 0, ¬ trqTest D P q ε ϑ Δ d i := fun i hi => by rwa [Nat.le_zero.1 hi]
  rcases k with _ | k
  · have h1 := h.trqKappa_mul_trqGap_zero_le hL hϑ hϑ1 hε0 hM h0
    have h2 := (h.trqGap_ge hϑ hε hk0).1.trans (prefixMin_le le_rfl)
    rw [h.delta_zero]
    calc P.ς * trqKappa P L ϑ M q * εmin = trqKappa P L ϑ M q * (P.ς * εmin) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hκ.le
      _ ≤ P.Δ₀ := h1
  · have hk' : ∀ i ≤ k, ¬ trqTest D P q ε ϑ Δ d i := fun i hi => hk i (Nat.lt_succ_of_le hi)
    refine le_trans ?_ (h.radius_ge (M := M) hL hϑ hϑ1 hε0 hM hfid hk').2
    refine le_min ?_ ?_
    · have := trqKappa_le_γ₁ (P := P) (M := M) (q := q) hL hϑ1
      calc P.ς * trqKappa P L ϑ M q * εmin ≤ 1 * P.γ₁ * ϑ :=
            mul_le_mul (mul_le_mul P.ς_le_one this hκ.le zero_le_one) hεϑ hεmin.le
              (by have := P.γ₁_pos; positivity)
        _ = P.γ₁ * ϑ := by ring
    · have := (h.trqGap_ge hϑ hε hk').1
      calc P.ς * trqKappa P L ϑ M q * εmin = trqKappa P L ϑ M q * (P.ς * εmin) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hκ.le

/-- **Lemma 12.2.4** ([cartis2022evaluation], (12.2.18)–(12.2.19)): model and function decreases.
Under the hypotheses of `IsTRqRun.radius_ge` with `0 < εmin ≤ ϑ` and `εmin ≤ ε_j` for
`j ∈ [1, q]`, at every iteration `k` before termination
`(ς κ_Δ)^{q+1} εmin^{q+1} / q! ≤ ΔT_{j_k}(D_k, s_k)`, and if `k` is successful,
`η₁ (ς κ_Δ)^{q+1} εmin^{q+1} / q! ≤ f(x_k) - f(x_{k+1})`. -/
theorem taylorDecrement_ge {L M εmin : ℝ} (hL : 1 ≤ L) (hϑ1 : ϑ ≤ 1) (hεmin : 0 < εmin)
    (hεϑ : εmin ≤ ϑ) (hε : ∀ j ∈ Finset.Icc 1 q, εmin ≤ ε j)
    (hM : ∀ i ∈ Finset.Icc 1 q, ‖D 0 i‖ ≤ M)
    (hfid : ∀ k, (∀ i ≤ k, ¬ trqTest D P q ε ϑ Δ d i) →
      |f (x k + s k) - (f (x k) - (D k).taylorDecrement (jk k) (s k))| ≤
        L / (jk k + 1)! * ‖s k‖ ^ (jk k + 1))
    {k : ℕ} (hk : ∀ i ≤ k, ¬ trqTest D P q ε ϑ Δ d i) :
    (P.ς * trqKappa P L ϑ M q) ^ (q + 1) / q ! * εmin ^ (q + 1) ≤
        (D k).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ trqRatio f D x s jk k →
        P.η₁ * ((P.ς * trqKappa P L ϑ M q) ^ (q + 1) / q ! * εmin ^ (q + 1)) ≤
          f (x k) - f (x (k + 1))) := by
  have h0 : ¬ trqTest D P q ε ϑ Δ d 0 := hk 0 (Nat.zero_le k)
  have hϑ : 0 < ϑ := hεmin.trans_le hεϑ
  have hε0 : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j := fun j hj => hεmin.le.trans (hε j hj)
  have hMpos := h.pos_of_not_trqTest_zero hε0 hϑ.le hM h0
  set κ := trqKappa P L ϑ M q
  have hκ : 0 < κ := trqKappa_pos (by linarith) hϑ hMpos
  have hκ1 : κ < 1 := trqKappa_lt_one hL hϑ1
  set m := P.ς * κ * εmin with hm
  have hm0 : 0 < m := by have := P.ς_pos; positivity
  have hςκ : P.ς * κ ≤ 1 := by
    calc P.ς * κ ≤ 1 * 1 := mul_le_mul P.ς_le_one hκ1.le hκ.le zero_le_one
      _ = 1 := one_mul 1
  have hmε : m ≤ εmin := by
    calc m = P.ς * κ * εmin := rfl
      _ ≤ 1 * εmin := by gcongr
      _ = εmin := one_mul _
  have hm1 : m ≤ 1 := hmε.trans (hεϑ.trans hϑ1)
  have hδ : m ≤ min (Δ k) ϑ :=
    le_min (h.mul_le_delta hL hϑ1 hεmin hεϑ hε hM h0 hfid fun i hi => hk i hi.le)
      (hmε.trans hεϑ)
  have hg : m ≤ trqGap (D k) (jk k) (min (Δ k) ϑ) (d k (jk k)) := by
    refine le_trans ?_ ((h.trqGap_ge hϑ hε hk).1.trans (prefixMin_le le_rfl))
    calc m = κ * (P.ς * εmin) := by rw [hm]; ring
      _ ≤ 1 * (P.ς * εmin) := by gcongr; have := P.ς_pos; positivity
      _ = P.ς * εmin := one_mul _
  have hjq := Finset.mem_Icc.1 (h.isTRqStep hk).order_mem
  have hfac : (0 : ℝ) < (jk k) ! := by exact_mod_cast (jk k).factorial_pos
  have hfacq : ((jk k) ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hjq.2
  have hdec : m ^ (q + 1) / q ! ≤ (D k).taylorDecrement (jk k) (s k) := by
    refine le_trans ?_ (h.trqGap_mul_pow_div_le hϑ hk)
    calc m ^ (q + 1) / q ! = m * m ^ q / q ! := by ring
      _ ≤ m * m ^ jk k / q ! := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hm0.le hm1 hjq.2) hm0.le)
          (Nat.cast_nonneg _)
      _ ≤ m * m ^ jk k / (jk k) ! := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul hg (pow_le_pow_left₀ hm0.le hδ _)
          (by positivity) (hm0.le.trans hg)) hfac.le
  have heq : (P.ς * κ) ^ (q + 1) / q ! * εmin ^ (q + 1) = m ^ (q + 1) / q ! := by
    rw [hm, mul_pow]; ring
  rw [heq]
  refine ⟨hdec, fun hs => ?_⟩
  have hpos : 0 < (D k).taylorDecrement (jk k) (s k) :=
    lt_of_lt_of_le (by positivity) hdec
  have := (h.toIsTRRun.sub_ge_of_succ (pred := fun k => (D k).taylorDecrement (jk k) (s k))
    hk trqRatio_eq hpos hs).2
  exact (mul_le_mul_of_nonneg_left hdec P.η₁_pos.le).trans this

end IsTRqRun

/-- **Model fidelity for exact data** ((A.19), used in Lemma 12.2.2): for a TRq run with the exact
Taylor data `D k = ftaylorSeries ℝ f (x k)` of a `C^q` function whose derivatives of orders
`1, …, q` are `L`-Lipschitz (f.D1qL with `L_f ≤ L`), the hypothesis `hfid` of
`IsTRqRun.radius_ge` and `IsTRqRun.taylorDecrement_ge` holds. -/
theorem IsTRqRun.abs_sub_le_of_lipschitz {f : E → ℝ} {S : ℕ → Set E} {P : TRqParams} {q : ℕ}
    {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → E} {Δ : ℕ → ℝ} {jk : ℕ → ℕ} {d : ℕ → ℕ → E} {L : ℝ}
    (h : IsTRqRun f (fun k => ftaylorSeries ℝ f (x k)) S P q ε ϑ x s Δ jk d)
    (hf : ContDiff ℝ q f) (hL : ∀ j ∈ Finset.Icc 1 q, IteratedFDerivLipschitzOn f j L univ) :
    ∀ k, (∀ i ≤ k, ¬ trqTest (fun k => ftaylorSeries ℝ f (x k)) P q ε ϑ Δ d i) →
      |f (x k + s k) - (f (x k) - (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k))| ≤
        L / (jk k + 1)! * ‖s k‖ ^ (jk k + 1) := by
  intro k hk
  have hj := (h.isTRqStep hk).order_mem
  rw [ftaylorSeries_taylorDecrement_eq, sub_sub_cancel]
  exact abs_sub_taylorPolynomial_le_of_lipschitz convex_univ
    (fun y _ => (hf.of_le (by exact_mod_cast (Finset.mem_Icc.1 hj).2)).contDiffAt) (hL _ hj)
    (mem_univ _) (mem_univ _)

end Optimization
