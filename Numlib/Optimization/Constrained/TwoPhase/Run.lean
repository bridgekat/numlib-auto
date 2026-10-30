import Numlib.Optimization.Constrained.TwoPhase.Basic

/-!
# The outer loop of Phase 2 of two-phase target-following methods

Phase 2 of the two-phase methods TPp-GC (Algorithm 7.2.1) and TPqp-GC (Algorithm 14.3.2) of
[cartis2022evaluation] for `min f(x)` subject to `x ∈ 𝒳`, `c(x) = 0` starts at an approximately
feasible point `x₁` with `‖c(x₁)‖ ≤ θε₀` and target `t₁ = f(x₁) - √(ε₀² - ‖c(x₁)‖²)`. At outer
iteration `k ≥ 1`:

* Step 1: an inner method is called on the merit function `μ(·, t_k) = ½ ‖r(·, t_k)‖²`,
  `r(x, t) = (c(x), f(x) - t)`, from `x_k`; its iterates `x_{k,i}`, `i ≤ e_k`, do not increase
  `‖r(·, t_k)‖`, and the call ends at `x_{k+1} = x_{k,e_k}` when the residual is small, when
  `f(x_{k+1}) < t_k`, or when an approximate-criticality test holds;
* Step 2: in case (a) (small residual) the target is reset by (7.2.11), in case (b)
  (`f(x_{k+1}) < t_k`) it is reflected by (7.2.13), and Phase 2 terminates in case (c) (neither) or
  when the criticality test holds at `(x_{k+1}, t_{k+1})`.

This file formalizes this outer loop independently of the inner method and of the criticality
measure. The data (`Constrained.TargetFollowingSeq`) are the sequences together with the tests
evaluated along them; the run predicate is `Constrained.IsTargetFollowingRun`.

## Main definitions

* `Constrained.TargetFollowingSeq E`: outer iterates, targets, inner iterates, call lengths, and
  the tests `Ka`, `Kb`, `crit` of Step 2;
* `Constrained.TargetFollowingSeq.Stop`, `Before`, `IsEnd`, `targetOut`: termination and output;
* `Constrained.IsTargetFollowingRun f c θ ε₀ X x₁ S`: `S` is a run of Phase 2 from `x₁ ∈ X`.

## Main results

* `Constrained.IsTargetFollowingRun.isTargetSequence`: the outer bookkeeping is a target sequence
  (so Lemmas 7.2.3 and 7.2.4 hold);
* `Constrained.IsTargetFollowingRun.output_spec`: the output `(x_ε, t_ε)` satisfies
  `θε₀ ≤ ‖r(x_ε, t_ε)‖ ≤ ε₀`, `t_ε ≤ f(x_ε)` and the criticality test ((7.2.17), (7.2.20),
  (14.3.48)–(14.3.52));
* `Constrained.IsTargetFollowingRun.residual_le_of_forall_kb`: the residual does not increase along
  a run of case-(b) iterations ((B.14.19));
* `Constrained.TargetFollowingSeq.exists_isEnd_of_forall_le`: a uniform bound on the outer
  iterations reached gives termination.

## Implementation notes

The tests are abstract predicates, constrained by the fields of `Constrained.IsTargetFollowingRun`:
case (a) needs `‖r(x_{k+1}, t_k)‖ ≤ θε₀`, its failure needs `‖r(x_{k+1}, t_k)‖ ≥ θε₀`, and case (b)
is the failure of case (a) together with `f(x_{k+1}) < t_k`. This covers Step 2(a) both with
`≤ θε₀` and with `< θε₀`. The criticality test `crit k τ` is evaluated at the output `x_{k+1}`
of the `k`-th call: for `τ = t_k` it is the third stopping test of the inner call, for
`τ = t_{k+1}` the termination test of Step 2; it may depend on further data of the call (such as
the radii of the order-`q` measures of TPqp-GC).
-/

open Finset

namespace Constrained

variable {E F : Type*} [NormedAddCommGroup F]

/-- The sequences and tests of Phase 2 of a two-phase target-following method
([cartis2022evaluation], Algorithms 7.2.1 and 14.3.2), indexed by the outer iteration `k ≥ 1`
(the values at `k = 0` are unused). -/
structure TargetFollowingSeq (E : Type*) where
  /-- The outer iterates `x_k`. -/
  x : ℕ → E
  /-- The targets `t_k`. -/
  t : ℕ → ℝ
  /-- The iterates `x_{k,i}` of the `k`-th call of the inner method. -/
  xi : ℕ → ℕ → E
  /-- The number `e_k` of iterations of the `k`-th call. -/
  e : ℕ → ℕ
  /-- Outer iteration `k` performs Step 2(a) (case (a)). -/
  Ka : ℕ → Prop
  /-- Outer iteration `k` performs Step 2(b) (case (b)). -/
  Kb : ℕ → Prop
  /-- The approximate-criticality test at the output `x_{k+1}` of the `k`-th call, for a
  target `τ`. -/
  crit : ℕ → ℝ → Prop

namespace TargetFollowingSeq

variable (S : TargetFollowingSeq E)

/-- Phase 2 terminates at outer iteration `k`: in case (c), or in cases (a)/(b) when the
criticality test holds at `(x_{k+1}, t_{k+1})`. -/
def Stop (k : ℕ) : Prop :=
  (¬ S.Ka k ∧ ¬ S.Kb k) ∨ ((S.Ka k ∨ S.Kb k) ∧ S.crit k (S.t (k + 1)))

/-- No outer iteration `j ∈ [1, k)` has terminated Phase 2. -/
def Before (k : ℕ) : Prop := ∀ j, 1 ≤ j → j < k → ¬ S.Stop j

/-- Phase 2 terminates at outer iteration `kε ≥ 1`. -/
def IsEnd (kε : ℕ) : Prop := 1 ≤ kε ∧ S.Stop kε ∧ S.Before kε

open Classical in
/-- The output target `t_ε` of Phase 2 terminating at outer iteration `k`: `t_{k+1}` in cases
(a)/(b) and `t_k` in case (c) (the output point is `x_ε = x_{k+1}`). -/
noncomputable def targetOut (k : ℕ) : ℝ := if S.Ka k ∨ S.Kb k then S.t (k + 1) else S.t k

variable {S}

theorem stop_iff {k : ℕ} :
    S.Stop k ↔ (¬ S.Ka k ∧ ¬ S.Kb k) ∨ ((S.Ka k ∨ S.Kb k) ∧ S.crit k (S.t (k + 1))) :=
  Iff.rfl

theorem before_iff {k : ℕ} : S.Before k ↔ ∀ j, 1 ≤ j → j < k → ¬ S.Stop j := Iff.rfl

theorem isEnd_iff {kε : ℕ} : S.IsEnd kε ↔ 1 ≤ kε ∧ S.Stop kε ∧ S.Before kε := Iff.rfl

theorem before_zero : S.Before 0 := fun _ _ hj => absurd hj (Nat.not_lt_zero _)

theorem before_one : S.Before 1 := fun _ h1 hj => absurd hj (by omega)

theorem Before.mono {k K : ℕ} (h : S.Before K) (hk : k ≤ K) : S.Before k :=
  fun j h1 hj => h j h1 (hj.trans_le hk)

theorem Before.not_stop {k K : ℕ} (h : S.Before K) (hk1 : 1 ≤ k) (hk : k < K) : ¬ S.Stop k :=
  h k hk1 hk

theorem Before.succ {k : ℕ} (h : S.Before k) (hs : 1 ≤ k → ¬ S.Stop k) : S.Before (k + 1) := by
  intro j h1 hj
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · exact h j h1 hj
  · exact hs h1

/-- Before termination, an outer iteration is in case (a) or in case (b). -/
theorem ka_or_kb_of_not_stop {k : ℕ} (h : ¬ S.Stop k) : S.Ka k ∨ S.Kb k := by
  by_contra h'
  exact h (Or.inl (not_or.1 h'))

/-- Before termination, an outer iteration that is not in case (a) is in case (b). -/
theorem Before.kb_of_not_ka {k K : ℕ} (hK : S.Before K) (hk1 : 1 ≤ k) (hkK : k < K)
    (ha : ¬ S.Ka k) : S.Kb k :=
  (ka_or_kb_of_not_stop (hK.not_stop hk1 hkK)).resolve_left ha

theorem targetOut_of_ka_or_kb {k : ℕ} (h : S.Ka k ∨ S.Kb k) : S.targetOut k = S.t (k + 1) := by
  classical
  simp only [targetOut, h, ite_true]

theorem targetOut_of_not {k : ℕ} (ha : ¬ S.Ka k) (hb : ¬ S.Kb k) : S.targetOut k = S.t k := by
  classical
  simp only [targetOut, not_or.2 ⟨ha, hb⟩, ite_false]

/-- **Termination from a bound on the outer iterations**: if every outer iteration `K ≥ 1`
reached satisfies `K ≤ B`, then Phase 2 terminates at some `k_ε ≤ B`. -/
theorem exists_isEnd_of_forall_le {B : ℝ} (hB : ∀ K, 1 ≤ K → S.Before K → (K : ℝ) ≤ B) :
    ∃ kε, S.IsEnd kε ∧ (kε : ℝ) ≤ B := by
  by_contra hno
  have hall : ∀ K, S.Before K := by
    intro K
    induction K with
    | zero => exact before_zero
    | succ K ih => exact ih.succ fun hK1 hstop => hno ⟨K, ⟨hK1, hstop, ih⟩, hB K hK1 ih⟩
  have h1 := hB (⌈B⌉₊ + 1) (by omega) (hall _)
  push_cast at h1
  linarith [Nat.le_ceil B]

end TargetFollowingSeq

/-- **A run of Phase 2 of a two-phase target-following method** ([cartis2022evaluation],
Algorithms 7.2.1 and 14.3.2), started at `x₁ ∈ X`, with constants `θ ∈ (0, 1)` and
`ε₀ ∈ (0, 1]`, as a predicate on the data `S`. Writing `r_k(y) = ‖r(y, t_k)‖`
(`Constrained.targetResidual f c (S.t k) y`):
* the tests: case (a) implies `r_k(x_{k+1}) ≤ θε₀`, its failure implies `r_k(x_{k+1}) ≥ θε₀`, and
  case (b) holds iff case (a) fails and `f(x_{k+1}) < t_k`;
* Step 0: `‖c(x₁)‖ ≤ θε₀` and `t₁ = f(x₁) - √(ε₀² - ‖c(x₁)‖²)`;
* Step 1, for every outer iteration `k ≥ 1` reached: the call starts at `x_k` and ends at
  `x_{k+1} ∈ X`, does not increase `r_k`, keeps `r_k ≥ θε₀` before its last iterate (it is stopped
  as soon as the residual is small), and ends in case (a), with `f(x_{k+1}) < t_k`, or with the
  criticality test `crit k t_k`;
* Step 2: the target updates (7.2.11) in case (a) and (7.2.13) in case (b). -/
structure IsTargetFollowingRun (f : E → ℝ) (c : E → F) (θ ε₀ : ℝ) (X : Set E) (x₁ : E)
    (S : TargetFollowingSeq E) : Prop where
  θ_pos : 0 < θ
  θ_lt_one : θ < 1
  ε₀_pos : 0 < ε₀
  ε₀_le_one : ε₀ ≤ 1
  /-- Case (a) is entered only with a small residual. -/
  residual_le_of_ka : ∀ k, S.Ka k → targetResidual f c (S.t k) (S.x (k + 1)) ≤ θ * ε₀
  /-- Case (a) fails only with a residual at least `θε₀`. -/
  le_residual_of_not_ka : ∀ k, ¬ S.Ka k → θ * ε₀ ≤ targetResidual f c (S.t k) (S.x (k + 1))
  /-- Case (b): case (a) fails and `f(x_{k+1}) < t_k`. -/
  kb_iff : ∀ k, S.Kb k ↔ ¬ S.Ka k ∧ f (S.x (k + 1)) < S.t k
  /-- `x₁ ∈ X`. -/
  mem_one : x₁ ∈ X
  /-- Phase 1 ended with `‖c(x₁)‖ ≤ θε₀`. -/
  norm_one_le : ‖c x₁‖ ≤ θ * ε₀
  x_one : S.x 1 = x₁
  /-- Step 0. -/
  t_one : S.t 1 = f x₁ - √(ε₀ ^ 2 - ‖c x₁‖ ^ 2)
  /-- Step 1: the new iterate lies in `X`. -/
  mem_succ : ∀ k, 1 ≤ k → S.Before k → S.x (k + 1) ∈ X
  /-- Step 1: the call ends on one of its stopping tests. -/
  output : ∀ k, 1 ≤ k → S.Before k → S.Ka k ∨ f (S.x (k + 1)) < S.t k ∨ S.crit k (S.t k)
  /-- Step 1: the call starts at `x_k`. -/
  inner_zero : ∀ k, 1 ≤ k → S.Before k → S.xi k 0 = S.x k
  /-- Step 1: the call ends at `x_{k+1}`. -/
  inner_end : ∀ k, 1 ≤ k → S.Before k → S.xi k (S.e k) = S.x (k + 1)
  /-- Step 1: the call does not increase the residual. -/
  inner_mono : ∀ k, 1 ≤ k → S.Before k → ∀ i < S.e k,
    targetResidual f c (S.t k) (S.xi k (i + 1)) ≤ targetResidual f c (S.t k) (S.xi k i)
  /-- Step 1: the call is stopped as soon as the residual is below `θε₀`. -/
  inner_residual_ge : ∀ k, 1 ≤ k → S.Before k → ∀ i < S.e k,
    θ * ε₀ ≤ targetResidual f c (S.t k) (S.xi k i)
  /-- Step 2(a): (7.2.11). -/
  t_succ_a : ∀ k, 1 ≤ k → S.Before k → S.Ka k →
    S.t (k + 1) = f (S.x (k + 1)) - √(ε₀ ^ 2 - ‖c (S.x (k + 1))‖ ^ 2)
  /-- Step 2(b): (7.2.13). -/
  t_succ_b : ∀ k, 1 ≤ k → S.Before k → S.Kb k → S.t (k + 1) = 2 * f (S.x (k + 1)) - S.t k

namespace IsTargetFollowingRun

variable {f : E → ℝ} {c : E → F} {θ ε₀ : ℝ} {X : Set E} {x₁ : E} {S : TargetFollowingSeq E}
  (h : IsTargetFollowingRun f c θ ε₀ X x₁ S)
include h

theorem not_ka_of_kb {k : ℕ} (hb : S.Kb k) : ¬ S.Ka k := ((h.kb_iff k).1 hb).1

theorem lt_target_of_kb {k : ℕ} (hb : S.Kb k) : f (S.x (k + 1)) < S.t k := ((h.kb_iff k).1 hb).2

theorem le_residual_succ_of_kb {k : ℕ} (hb : S.Kb k) :
    θ * ε₀ ≤ targetResidual f c (S.t k) (S.x (k + 1)) :=
  h.le_residual_of_not_ka k (h.not_ka_of_kb hb)

/-- The residual `‖r(·, t_k)‖` is nonincreasing along the `k`-th call. -/
theorem inner_residual_antitone {k : ℕ} (hk1 : 1 ≤ k) (hk : S.Before k) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ S.e k) :
    targetResidual f c (S.t k) (S.xi k j) ≤ targetResidual f c (S.t k) (S.xi k i) := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (h.inner_mono k hk1 hk j (by omega)).trans (ih (by omega))

/-- The merit `μ(·, t_k)` is nonincreasing along the `k`-th call. -/
theorem inner_merit_antitone {k : ℕ} (hk1 : 1 ≤ k) (hk : S.Before k) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ S.e k) :
    targetMerit f c (S.t k) (S.xi k j) ≤ targetMerit f c (S.t k) (S.xi k i) :=
  targetMerit_le_targetMerit_iff.2 (h.inner_residual_antitone hk1 hk hij hj)

/-- `‖r(x_{k+1}, t_k)‖ ≤ ‖r(x_k, t_k)‖`. -/
theorem residual_succ_le {k : ℕ} (hk1 : 1 ≤ k) (hk : S.Before k) :
    targetResidual f c (S.t k) (S.x (k + 1)) ≤ targetResidual f c (S.t k) (S.x k) := by
  have := h.inner_residual_antitone hk1 hk (Nat.zero_le _) le_rfl
  rwa [h.inner_end k hk1 hk, h.inner_zero k hk1 hk] at this

/-- The residual at the start of a call that makes at least one iteration is at least `θε₀`. -/
theorem le_residual_of_pos {k : ℕ} (hk1 : 1 ≤ k) (hk : S.Before k) (he : 0 < S.e k) :
    θ * ε₀ ≤ targetResidual f c (S.t k) (S.x k) := by
  have := h.inner_residual_ge k hk1 hk 0 he
  rwa [h.inner_zero k hk1 hk] at this

/-- The outer iterates stay in `X`. -/
theorem x_mem : ∀ k, 1 ≤ k → S.Before k → S.x k ∈ X := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base => intro _; rw [h.x_one]; exact h.mem_one
  | succ k hk1 _ => intro hk; exact h.mem_succ k hk1 (hk.mono k.le_succ)

/-- **The outer bookkeeping of Phase 2** is a target sequence up to every outer iteration `K`
reached; hence Lemmas 7.2.3 and 7.2.4 of [cartis2022evaluation] hold. -/
theorem isTargetSequence {K : ℕ} (hK : S.Before K) :
    IsTargetSequence f c θ ε₀ S.x S.t S.Ka K where
  norm_one_le := h.x_one ▸ h.norm_one_le
  target_one := by rw [h.t_one, h.x_one]
  residual_succ_le k hk1 hkK := h.residual_succ_le hk1 (hK.mono hkK.le)
  residual_le_of_Ka k _ _ ha := h.residual_le_of_ka k ha
  target_succ_of_Ka k hk1 hkK ha := h.t_succ_a k hk1 (hK.mono hkK.le) ha
  le_residual_of_not_Ka k _ _ ha := h.le_residual_of_not_ka k ha
  lt_target_of_not_Ka k hk1 hkK ha := h.lt_target_of_kb (hK.kb_of_not_ka hk1 hkK ha)
  target_succ_of_not_Ka k hk1 hkK ha :=
    h.t_succ_b k hk1 (hK.mono hkK.le) (hK.kb_of_not_ka hk1 hkK ha)

/-- `‖r(x_k, t_k)‖ ≤ ε₀` at every outer iteration reached ((7.2.27)–(7.2.28)). -/
theorem residual_le {k : ℕ} (hk1 : 1 ≤ k) (hk : S.Before k) :
    targetResidual f c (S.t k) (S.x k) ≤ ε₀ :=
  (h.isTargetSequence hk).residual_le h.θ_lt_one.le h.ε₀_pos.le hk1 le_rfl

/-- `t_k ≤ f(x_k)` at every outer iteration reached ((7.2.26)). -/
theorem target_le {k : ℕ} (hk1 : 1 ≤ k) (hk : S.Before k) : S.t k ≤ f (S.x k) := by
  have := (h.isTargetSequence hk).sub_target_nonneg hk1 le_rfl
  linarith

/-- The targets decrease strictly before termination (Lemma 7.2.3). -/
theorem target_succ_lt {k : ℕ} (hk1 : 1 ≤ k) (hk : S.Before (k + 1)) : S.t (k + 1) < S.t k :=
  (h.isTargetSequence hk).target_succ_lt h.θ_pos.le h.θ_lt_one h.ε₀_pos hk1 k.lt_succ_self

/-- In case (b) the target update preserves the residual: `‖r(x_{k+1}, t_{k+1})‖ =
‖r(x_{k+1}, t_k)‖` ((7.2.28)). -/
theorem residual_succ_of_kb {k : ℕ} (hk1 : 1 ≤ k) (hk : S.Before k) (hb : S.Kb k) :
    targetResidual f c (S.t (k + 1)) (S.x (k + 1)) = targetResidual f c (S.t k) (S.x (k + 1)) := by
  rw [h.t_succ_b k hk1 hk hb, targetResidual_two_mul_sub]

/-- In case (a) the target update resets the residual to `ε₀` ((7.2.27)). -/
theorem residual_succ_of_ka {k : ℕ} (hk1 : 1 ≤ k) (hk : S.Before k) (ha : S.Ka k) :
    targetResidual f c (S.t (k + 1)) (S.x (k + 1)) = ε₀ := by
  rw [h.t_succ_a k hk1 hk ha]
  refine targetResidual_sub_sqrt h.ε₀_pos.le ?_
  exact norm_le_targetResidual.trans ((h.residual_le_of_ka k ha).trans
    (mul_le_of_le_one_left h.ε₀_pos.le h.θ_lt_one.le))

open Classical in
/-- The residual of the output of Phase 2 terminating at `k_ε`: `ε₀` in case (a), and
`‖r(x_{k_ε+1}, t_{k_ε})‖` otherwise. -/
theorem residual_targetOut {kε : ℕ} (hk1 : 1 ≤ kε) (hk : S.Before kε) :
    targetResidual f c (S.targetOut kε) (S.x (kε + 1)) =
      if S.Ka kε then ε₀ else targetResidual f c (S.t kε) (S.x (kε + 1)) := by
  split_ifs with ha
  · rw [TargetFollowingSeq.targetOut_of_ka_or_kb (Or.inl ha), h.residual_succ_of_ka hk1 hk ha]
  · by_cases hb : S.Kb kε
    · rw [TargetFollowingSeq.targetOut_of_ka_or_kb (Or.inr hb), h.residual_succ_of_kb hk1 hk hb]
    · rw [TargetFollowingSeq.targetOut_of_not ha hb]

/-- **The output of Phase 2** ([cartis2022evaluation], (7.2.17), (7.2.20), (14.3.48), (14.3.49),
(14.3.52)): if Phase 2 terminates at outer iteration `k_ε`, the output `x_ε = x_{k_ε+1}`,
`t_ε = targetOut k_ε` satisfies `x_ε ∈ X`, `θε₀ ≤ ‖r(x_ε, t_ε)‖ ≤ ε₀`, `t_ε ≤ f(x_ε)` and the
criticality test at `(x_ε, t_ε)`. -/
theorem output_spec {kε : ℕ} (hend : S.IsEnd kε) :
    S.x (kε + 1) ∈ X ∧
      θ * ε₀ ≤ targetResidual f c (S.targetOut kε) (S.x (kε + 1)) ∧
      targetResidual f c (S.targetOut kε) (S.x (kε + 1)) ≤ ε₀ ∧
      S.targetOut kε ≤ f (S.x (kε + 1)) ∧ S.crit kε (S.targetOut kε) := by
  obtain ⟨hk1, hstop, hbef⟩ := hend
  have hε₀ := h.ε₀_pos
  have hθε : θ * ε₀ ≤ ε₀ := mul_le_of_le_one_left hε₀.le h.θ_lt_one.le
  have hr_succ := (h.residual_succ_le hk1 hbef).trans (h.residual_le hk1 hbef)
  have hr := h.residual_targetOut hk1 hbef
  refine ⟨h.mem_succ kε hk1 hbef, ?_, ?_, ?_⟩
  · rw [hr]; split_ifs with ha
    · exact hθε
    · exact h.le_residual_of_not_ka kε ha
  · rw [hr]; split_ifs
    · exact le_rfl
    · exact hr_succ
  rcases hstop with ⟨hna, hnb⟩ | ⟨hab, hcrit⟩
  · -- case (c)
    rw [TargetFollowingSeq.targetOut_of_not hna hnb]
    have hft : S.t kε ≤ f (S.x (kε + 1)) :=
      not_lt.1 fun hlt => hnb ((h.kb_iff kε).2 ⟨hna, hlt⟩)
    refine ⟨hft, ?_⟩
    rcases h.output kε hk1 hbef with h1 | h2 | h3
    · exact absurd h1 hna
    · exact absurd h2 (not_lt.2 hft)
    · exact h3
  · rw [TargetFollowingSeq.targetOut_of_ka_or_kb hab]
    refine ⟨?_, hcrit⟩
    rcases hab with ha | hb
    · rw [h.t_succ_a kε hk1 hbef ha]
      linarith [Real.sqrt_nonneg (ε₀ ^ 2 - ‖c (S.x (kε + 1))‖ ^ 2)]
    · rw [h.t_succ_b kε hk1 hbef hb]
      linarith [h.lt_target_of_kb hb]

/-- **The residual does not increase along a run of case-(b) iterations**: if every outer
iteration of `[k, k')` is in case (b), then `‖r(x_{k'}, t_{k'})‖ ≤ ‖r(x_k, t_k)‖` (the calls do
not increase `‖r(·, t_j)‖`, and (7.2.13) preserves it; [cartis2022evaluation], (B.14.19)). -/
theorem residual_le_of_forall_kb {k k' : ℕ} (hk1 : 1 ≤ k) (hkk' : k ≤ k') (hK : S.Before k')
    (hb : ∀ j, k ≤ j → j < k' → S.Kb j) :
    targetResidual f c (S.t k') (S.x k') ≤ targetResidual f c (S.t k) (S.x k) := by
  induction k', hkk' using Nat.le_induction with
  | base => exact le_rfl
  | succ j hkj ih =>
    have hjB : S.Before j := hK.mono j.le_succ
    rw [h.residual_succ_of_kb (hk1.trans hkj) hjB (hb j hkj j.lt_succ_self)]
    exact (h.residual_succ_le (hk1.trans hkj) hjB).trans
      (ih hjB fun i hi hij => hb i hi (hij.trans j.lt_succ_self))

end IsTargetFollowingRun

end Constrained
