import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Complexity

/-!
# Phase-2 sequences with one-step inner calls

The simplest data of Phase 2 of a high-order target-following method
(`Constrained.HighOrderTargetSeq`): outer iterates `x`, targets `t`, all optimality radii `1`, and
every inner call makes exactly one successful iteration, from `x_k` to `x_{k+1}`. Such data are a
run (`Constrained.isHighOrderTargetRun_oneStep`) as soon as each step satisfies the conditions of
Steps 1–2, and the merit-decrease contracts of the inner method hold for them whenever every call
ends at a point exempt from the decrease (`HighOrderTargetSeq.isEndCritContract_oneStep`,
`HighOrderTargetSeq.isInnerTestContract_oneStep`).

## Main definitions

* `Constrained.HighOrderTargetSeq.oneStep x t`: the data with one-step inner calls.

## Main results

* `Constrained.HighOrderTargetSeq.funEvals_oneStep`, `derivEvals_oneStep`: `k + 1` evaluations
  up to outer iteration `k`;
* `Constrained.isHighOrderTargetRun_oneStep`: the run conditions for one-step calls.
-/

open Finset
open scoped Nat

namespace Constrained

variable {E F : Type*}

namespace HighOrderTargetSeq

/-- The Phase-2 data with iterates `x`, targets `t` and radii `1`, in which the `k`-th inner call
makes one successful iteration, from `x_k` to `x_{k+1}`. -/
def oneStep (x : ℕ → E) (t : ℕ → ℝ) : HighOrderTargetSeq E :=
  ⟨x, t, fun _ _ => 1, fun k i => if i = 0 then x k else x (k + 1), fun _ => 1, fun _ _ => True⟩

variable (x : ℕ → E) (t : ℕ → ℝ)

@[simp] theorem oneStep_x : (oneStep x t).x = x := rfl

@[simp] theorem oneStep_t : (oneStep x t).t = t := rfl

@[simp] theorem oneStep_δ (k j : ℕ) : (oneStep x t).δ k j = 1 := rfl

@[simp] theorem oneStep_e (k : ℕ) : (oneStep x t).e k = 1 := rfl

@[simp] theorem oneStep_succ (k i : ℕ) : (oneStep x t).succ k i := trivial

@[simp] theorem oneStep_xi_zero (k : ℕ) : (oneStep x t).xi k 0 = x k := rfl

@[simp] theorem oneStep_xi_one (k : ℕ) : (oneStep x t).xi k 1 = x (k + 1) := rfl

/-- `k + 1` evaluations of `(f, c)` up to outer iteration `k`: one at `x₁` and one per call. -/
theorem funEvals_oneStep (k : ℕ) : (oneStep x t).funEvals k = k + 1 := by
  simp [funEvals_eq_sum, add_comm]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- Every inner call makes one successful iteration. -/
@[simp] theorem succCount_oneStep (k : ℕ) : (oneStep x t).succCount k = 1 := by
  classical
  rw [succCount_eq_card_filter, Finset.card_eq_one]
  exact ⟨0, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨by simp, trivial⟩,
    fun i hi => by simpa using (Finset.mem_filter.1 hi).1⟩⟩

/-- `k + 1` evaluations of the derivatives up to outer iteration `k`. -/
theorem derivEvals_oneStep (k : ℕ) : (oneStep x t).derivEvals k = k + 1 := by
  simp [derivEvals_eq_sum, add_comm]

variable {f : E → ℝ} {c : E → F} {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x t}

/-- **The end-criticality contract for one-step calls**: if every call ends at a point passing
the criticality test (14.3.34) for the old target, the only successful iteration of each call is
exempt from the decrease of `IsEndCritContract`, which then holds for every `κ_decr`, `π` and
`κ_uns + κ_unc ≥ 1`. -/
theorem isEndCritContract_oneStep {κdecr κuns κunc : ℝ} {π : ℕ → ℝ} (hκ : 1 ≤ κuns + κunc)
    (hcrit : ∀ k, 1 ≤ k → (oneStep x t).Before f c X q θ ε k →
      targetCrit f c X q ε (t k) (x (k + 1)) (fun _ => 1)) :
    (oneStep x t).IsEndCritContract f c X q θ β ε κdecr κuns κunc π :=
  ⟨fun _ _ _ => by simp; linarith, fun _ _ _ _ _ hs => absurd trivial hs,
    fun k hk1 hk i hi _ hcont _ => by
      obtain rfl : i = 0 := by simpa using hi
      rcases hcont with h | h
      · simp at h
      · exact absurd (hcrit k hk1 hk) h⟩

/-- **The inner-test contract for one-step calls**: if every call ends at a point passing the
inner method's own test (14.3.19), the only successful iteration of each call is exempt from the
decrease of `IsInnerTestContract`, which then holds for every `κ_decr`, `π`, `κ_uns + κ_unc ≥ 1`
and radii `ρ ≤ 1`. -/
theorem isInnerTestContract_oneStep {κdecr κuns κunc : ℝ} {π ρ : ℕ → ℝ}
    (hκ : 1 ≤ κuns + κunc) (hρ : ∀ j ∈ Finset.Icc 1 q, ρ j ≤ 1)
    (htest : ∀ k, 1 ≤ k → (oneStep x t).Before f c X q θ ε k →
      (oneStep x t).InnerTest f c X q β ε k) :
    (oneStep x t).IsInnerTestContract f c X q θ β ε κdecr κuns κunc π ρ :=
  ⟨⟨fun _ _ _ => by simp; linarith, fun _ _ _ _ _ hs => absurd trivial hs,
    fun k hk1 hk i hi _ hcont _ => by
      obtain rfl : i = 0 := by simpa using hi
      rcases hcont with h | h
      · simp at h
      · exact absurd (htest k hk1 hk) h⟩,
    fun _ _ _ _ _ j hj => hρ j hj⟩

end HighOrderTargetSeq

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] {f : E → ℝ} {c : E → F}
  {X : Set E} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ}

/-- **Runs with one-step inner calls**: `HighOrderTargetSeq.oneStep x t` is a run of Phase 2 from
`x₁ = x 1` as soon as the constants are admissible, Step 0 holds, and at every outer iteration
`k ≥ 1` reached the new iterate is feasible and satisfies (14.3.32) with radii `1`, the step does
not increase `μ(·, t_k)`, `‖r(x_k, t_k)‖ ≥ θε₀`, and the target updates (14.3.33), (14.3.35)
hold. -/
theorem isHighOrderTargetRun_oneStep {x : ℕ → E} {t : ℕ → ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hβ : 0 < β) (hβθ : β ≤ θ) (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j)
    (hε1 : ∀ j ∈ Finset.range (q + 1), ε j ≤ 1) (hx1 : x 1 ∈ X) (hc1 : ‖c (x 1)‖ ≤ θ * ε 0)
    (ht1 : t 1 = f (x 1) - √(ε 0 ^ 2 - ‖c (x 1)‖ ^ 2))
    (hmem : ∀ k, 1 ≤ k → (HighOrderTargetSeq.oneStep x t).Before f c X q θ ε k →
      x (k + 1) ∈ X)
    (hout : ∀ k, 1 ≤ k → (HighOrderTargetSeq.oneStep x t).Before f c X q θ ε k →
      targetResidual f c (t k) (x (k + 1)) < θ * ε 0 ∨ f (x (k + 1)) < t k ∨
        targetCrit f c X q ε (t k) (x (k + 1)) (fun _ => 1))
    (hmono : ∀ k, 1 ≤ k → (HighOrderTargetSeq.oneStep x t).Before f c X q θ ε k →
      targetMerit f c (t k) (x (k + 1)) ≤ targetMerit f c (t k) (x k))
    (hres : ∀ k, 1 ≤ k → (HighOrderTargetSeq.oneStep x t).Before f c X q θ ε k →
      θ * ε 0 ≤ targetResidual f c (t k) (x k))
    (ha : ∀ k, 1 ≤ k → (HighOrderTargetSeq.oneStep x t).Before f c X q θ ε k →
      (HighOrderTargetSeq.oneStep x t).IsKa f c θ ε k →
      t (k + 1) = f (x (k + 1)) - √(ε 0 ^ 2 - ‖c (x (k + 1))‖ ^ 2))
    (hb : ∀ k, 1 ≤ k → (HighOrderTargetSeq.oneStep x t).Before f c X q θ ε k →
      (HighOrderTargetSeq.oneStep x t).IsKb f c θ ε k → t (k + 1) = 2 * f (x (k + 1)) - t k) :
    IsHighOrderTargetRun f c X q θ β ε (x 1) (HighOrderTargetSeq.oneStep x t) :=
  ⟨hθ, hθ1, hβ, hβθ, hε, hε1, hx1, hc1, rfl, ht1, hmem, fun _ _ _ _ _ => ⟨one_pos, le_rfl⟩, hout,
    fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun k hk1 hk i hi => by obtain rfl : i = 0 := by simpa using hi
                            exact hmono k hk1 hk,
    fun k hk1 hk i hi => by obtain rfl : i = 0 := by simpa using hi
                            exact hres k hk1 hk, ha, hb⟩

end Constrained
