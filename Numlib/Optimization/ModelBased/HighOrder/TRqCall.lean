import Numlib.Analysis.SpecialFunctions.Log
import Numlib.Optimization.ModelBased.HighOrder.TRqComplexity

/-!
# TRq runs as inner solvers

A run of the trust-region method TRq ([cartis2022evaluation], Algorithm 12.2.1) with the exact
Taylor data of `f` on a closed feasible set `X` (TRq-SC of §14.2) is the inner solver INNER of
trust-region type of the two-phase method TPqp-GC (§14.3). Each call starts afresh from the radius
`Δ₀` at a point given by the outer method, and is cut either at its own termination or earlier by
a test of the outer method. This file collects what an outer analysis needs about one call, with
constants that depend on `f` only through Lipschitz constants `L` of its derivatives and a bound
`M` on its derivatives of orders `1, …, q` at the start of the call, so that they are uniform over
all calls.

## Main definitions

* `Optimization.trqCallKappaDelta`, `trqCallKappaRad`, `trqCallKappaDecr`, `trqKappaUns`,
  `trqCallKappaS`, `trqCallKappaA`, `trqCallKappaC`: the constants of Lemmas 12.2.3, 12.2.4,
  2.3.1 and Theorem 12.2.5 with the derivative bound `M` in place of the derivatives at the start;
* `Optimization.IsTRqCallOut`: a call cut at any iteration up to its termination, with its
  iterates, successful iterations and returned radii `min(Δ_e, ϑ)`;
* `Optimization.IsTRqOutputCost`: a terminating call with its evaluation counts.

## Main results

* `Optimization.trqCallKappaDelta_le_trqKappaDelta` and the comparisons
  `kappaSTRq_le_trqCallKappaS`, `kappaATRq_le_trqCallKappaA`, `kappaCTRq_le_trqCallKappaC`;
* `Optimization.IsTRqRun.trqCallKappaRad_mul_le`: the radii stay above `κ_ρ ε_min` up to
  termination (Lemma 12.2.3 with (12.2.9));
* `Optimization.IsTRqCallOut.eq_of_not_succ`, `IsTRqCallOut.le_count`, `IsTRqCallOut.decrease`,
  `IsTRqCallOut.radius_ge`: unsuccessful iterations do not move; the number of iterations of a call
  is at most `κ_uns (|𝒮| + 1) + |log(κ_ρ ε_min/Δ₀)|/|log γ₂|` (Lemma 2.3.1); every successful
  iteration decreases `f` by at least `κ_decr ε_min^{q+1}` (Lemma 12.2.4); the returned radii are
  at least `κ_ρ ε_min`;
* `Optimization.IsTRqOutputCost.cost_le`: the evaluation counts of a terminating call
  (Theorem 12.2.5);
* `Optimization.exists_isTRqRun_feasible`: runs with a closed feasible set exist;
* `Optimization.exists_isTRqCallOut_of_stop`: calls stopped at the first iterate satisfying an
  external test, or at termination, exist.

## Design notes

The constants of Theorem 12.2.5 (`trqKappaDelta`, `kappaSTRq`, …) depend on the starting point
through `max_i ‖∇^i f(x₀)‖`. Their call counterparts take a bound `M` instead and are compared
with them through the antitonicity of `trqKappa` in `M` (`trqKappa_anti`). Because every call
restarts from the radius `Δ₀`, the count of a call carries the term `|log(κ_ρ ε_min/Δ₀)|`, which
an outer method multiplies by its number of calls.
-/

open Set
open scoped Nat

namespace Optimization

/-- The exact Taylor data `k ↦ ftaylorSeries ℝ f (x k)` along the iterates. -/
local notation "𝒥" f:max x:max => fun k : ℕ => ftaylorSeries ℝ f (x k)

/-- The feasible displacements `k ↦ {e | x k + e ∈ X}`. -/
local notation "𝒳" X:max x:max => fun k : ℕ => Set.ofPred fun e => x k + e ∈ X

/-- `|𝒮_e| ≤ |{i < e | succ i}| + 1`: the success set up to `e` (which includes `e`) has at most
one more element than the set of successful iterations before `e`. -/
theorem card_successSet_le_card_filter_add_one (succ : ℕ → Prop) [DecidablePred succ] (e : ℕ) :
    ((successSet succ e).card : ℝ) ≤ ((Finset.range e).filter succ).card + 1 := by
  rw [successSet_eq_filter, Finset.range_add_one, Finset.filter_insert]
  split_ifs
  · exact_mod_cast Finset.card_insert_le _ _
  · exact le_add_of_nonneg_right zero_le_one

/-! ### The constants of a call -/

section Constants

variable (P : TRqParams) (L : ℕ → ℝ) (ϑ M : ℝ) (q : ℕ)

/-- The lower bound `κ_Δ(M) = γ₁ (1 - η₂)/L_f · min(ϑ, Δ₀ δ₀^q/(2 q! M))` of the constant `κ_Δ`
of (12.2.14) of [cartis2022evaluation] (`trqKappaDelta`), for a bound `M` on the derivatives of
orders `1, …, q` at the starting point and `L_f = max(1, max_j L_j)`. -/
noncomputable def trqCallKappaDelta : ℝ :=
  trqKappa P (finMax 1 L q) ϑ M q

/-- The radius constant `κ_ρ = min(γ₁ ϑ, ς κ_Δ(M), Δ₀)`: the trust-region radii up to
termination, and the optimality radii `min(Δ_k, ϑ)`, are at least `κ_ρ ε_min`
(Lemma 12.2.3 of [cartis2022evaluation] with (12.2.9)). -/
noncomputable def trqCallKappaRad : ℝ :=
  min (min (P.γ₁ * ϑ) (trqCallKappaDelta P L ϑ M q * P.ς)) P.Δ₀

/-- The decrease constant `κ_decr = η₁ (ς κ_Δ(M))^{q+1}/q!` of Lemma 12.2.4 of
[cartis2022evaluation]: a successful iteration decreases the objective by at least
`κ_decr ε_min^{q+1}`. -/
noncomputable def trqCallKappaDecr : ℝ :=
  P.η₁ * ((P.ς * trqCallKappaDelta P L ϑ M q) ^ (q + 1) / q !)

/-- The constant `κ_uns = 1 + log γ₃/|log γ₂|` of Lemma 2.3.1 of [cartis2022evaluation]. -/
noncomputable def trqKappaUns : ℝ :=
  1 + Real.log P.γ₃ / |Real.log P.γ₂|

/-- The constant `κ^S = q!/(η₁ (ς κ_Δ(M))^{q+1})` of Theorem 12.2.5 of [cartis2022evaluation]
with `κ_Δ(M)` in place of `κ_Δ`. -/
noncomputable def trqCallKappaS : ℝ :=
  q ! / (P.η₁ * (P.ς * trqCallKappaDelta P L ϑ M q) ^ (q + 1))

/-- The constant `κ^A = κ^S κ_uns` of Theorem 12.2.5 of [cartis2022evaluation] with `κ_Δ(M)` in
place of `κ_Δ`. -/
noncomputable def trqCallKappaA : ℝ :=
  trqCallKappaS P L ϑ M q * trqKappaUns P

/-- An upper bound `(|log ς| + |log κ_Δ(M)| + |log Δ₀|)/|log γ₂| + 1` for the constant
`κ^C = |log(ς κ_Δ/Δ₀)|/|log γ₂| + 1` of Theorem 12.2.5 of [cartis2022evaluation]. -/
noncomputable def trqCallKappaC : ℝ :=
  (|Real.log P.ς| + |Real.log (trqCallKappaDelta P L ϑ M q)| + |Real.log P.Δ₀|) /
    |Real.log P.γ₂| + 1

variable {P L ϑ M q}

theorem trqCallKappaDelta_pos (hϑ : 0 < ϑ) (hM : 0 < M) : 0 < trqCallKappaDelta P L ϑ M q :=
  trqKappa_pos (zero_lt_one.trans_le one_le_finMax) hϑ hM

theorem trqCallKappaDelta_lt_one (hϑ1 : ϑ ≤ 1) : trqCallKappaDelta P L ϑ M q < 1 :=
  trqKappa_lt_one one_le_finMax hϑ1

theorem trqCallKappaRad_pos (hϑ : 0 < ϑ) (hM : 0 < M) : 0 < trqCallKappaRad P L ϑ M q :=
  lt_min (lt_min (mul_pos P.γ₁_pos hϑ) (mul_pos (trqCallKappaDelta_pos hϑ hM) P.ς_pos)) P.Δ₀_pos

theorem trqCallKappaRad_le_γ₁ : trqCallKappaRad P L ϑ M q ≤ P.γ₁ * ϑ :=
  (min_le_left _ _).trans (min_le_left _ _)

theorem trqCallKappaDecr_pos (hϑ : 0 < ϑ) (hM : 0 < M) : 0 < trqCallKappaDecr P L ϑ M q := by
  have := trqCallKappaDelta_pos (P := P) (L := L) (q := q) hϑ hM
  have := P.ς_pos
  have := P.η₁_pos
  unfold trqCallKappaDecr
  positivity

theorem one_le_trqKappaUns : 1 ≤ trqKappaUns P := by
  unfold trqKappaUns
  have : 0 ≤ Real.log P.γ₃ / |Real.log P.γ₂| :=
    div_nonneg (Real.log_nonneg P.one_le_γ₃) (abs_nonneg _)
  linarith

theorem trqCallKappaS_nonneg (hϑ : 0 < ϑ) (hM : 0 < M) : 0 ≤ trqCallKappaS P L ϑ M q := by
  have := trqCallKappaDelta_pos (P := P) (L := L) (q := q) hϑ hM
  have := P.ς_pos
  have := P.η₁_pos
  unfold trqCallKappaS
  positivity

theorem trqCallKappaA_nonneg (hϑ : 0 < ϑ) (hM : 0 < M) : 0 ≤ trqCallKappaA P L ϑ M q :=
  mul_nonneg (trqCallKappaS_nonneg hϑ hM) (zero_le_one.trans one_le_trqKappaUns)

theorem one_le_trqCallKappaC : 1 ≤ trqCallKappaC P L ϑ M q := by
  unfold trqCallKappaC
  have : 0 ≤ (|Real.log P.ς| + |Real.log (trqCallKappaDelta P L ϑ M q)| + |Real.log P.Δ₀|) /
    |Real.log P.γ₂| := by positivity
  linarith

/-- `κ_Δ(M) = trqKappa P L' ϑ M q` is antitone in the derivative bound `M`. -/
theorem trqKappa_anti {L' ϑ M M' : ℝ} (hL : 0 < L') (hϑ : 0 ≤ ϑ) (hM : 0 < M) (hMM : M ≤ M') :
    trqKappa P L' ϑ M' q ≤ trqKappa P L' ϑ M q := by
  unfold trqKappa
  have := P.γ₁_pos
  have := P.one_sub_η₂_pos
  have := P.Δ₀_pos
  have hf : (0 : ℝ) < q ! := by positivity
  have hmin : 0 ≤ min P.Δ₀ ϑ := le_min P.Δ₀_pos.le hϑ
  refine mul_le_mul_of_nonneg_left (min_le_min le_rfl ?_) (by positivity)
  exact div_le_div_of_nonneg_left (mul_nonneg P.Δ₀_pos.le (pow_nonneg hmin q)) (by positivity)
    (by gcongr)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {y : E}

/-- **The constant `κ_Δ` of (12.2.14) is at least `κ_Δ(M)`** at a point `y` where it is positive
(which holds when a run from `y` does not stop at once) and the derivatives of orders `1, …, q`
are bounded by `M`. -/
theorem trqCallKappaDelta_le_trqKappaDelta (hpos : 0 < trqKappaDelta f P q L ϑ y)
    (hM : finMax 0 (fun i => ‖iteratedFDeriv ℝ i f y‖) q ≤ M) (hϑ : 0 ≤ ϑ) :
    trqCallKappaDelta P L ϑ M q ≤ trqKappaDelta f P q L ϑ y := by
  unfold trqKappaDelta at hpos ⊢
  unfold trqCallKappaDelta
  set M₀ := finMax 0 (fun i => ‖iteratedFDeriv ℝ i f y‖) q with hM₀
  have hL : 0 < finMax 1 L q := zero_lt_one.trans_le one_le_finMax
  have hM₀0 : 0 < M₀ := by
    rcases (le_finMax_left : (0 : ℝ) ≤ M₀).lt_or_eq with h | h
    · exact h
    · exfalso
      have h' : M₀ = 0 := by rw [hM₀]; exact h.symm
      rw [h'] at hpos
      unfold trqKappa at hpos
      have h0 : min ϑ (P.Δ₀ * min P.Δ₀ ϑ ^ q / (2 * q ! * 0)) ≤ 0 := by
        rw [mul_zero, div_zero]; exact min_le_right _ _
      have := P.γ₁_pos
      have := P.one_sub_η₂_pos
      exact absurd hpos (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) h0))
  exact trqKappa_anti hL hϑ hM₀0 hM

/-- `κ^S_{TRq} ≤ κ^S(M)` under the hypotheses of `trqCallKappaDelta_le_trqKappaDelta`. -/
theorem kappaSTRq_le_trqCallKappaS (hpos : 0 < trqKappaDelta f P q L ϑ y)
    (hM : finMax 0 (fun i => ‖iteratedFDeriv ℝ i f y‖) q ≤ M) (hϑ : 0 < ϑ) (hM0 : 0 < M) :
    kappaSTRq f P q L ϑ y ≤ trqCallKappaS P L ϑ M q := by
  have hκ := trqCallKappaDelta_le_trqKappaDelta hpos hM hϑ.le
  have hp1 : 0 < P.ς * trqCallKappaDelta P L ϑ M q :=
    mul_pos P.ς_pos (trqCallKappaDelta_pos hϑ hM0)
  have hpow : (P.ς * trqCallKappaDelta P L ϑ M q) ^ (q + 1) ≤
      (P.ς * trqKappaDelta f P q L ϑ y) ^ (q + 1) :=
    pow_le_pow_left₀ hp1.le (mul_le_mul_of_nonneg_left hκ P.ς_pos.le) _
  unfold kappaSTRq trqCallKappaS
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos P.η₁_pos (pow_pos hp1 _))
    (mul_le_mul_of_nonneg_left hpow P.η₁_pos.le)

/-- `κ^A_{TRq} ≤ κ^A(M)` under the hypotheses of `trqCallKappaDelta_le_trqKappaDelta`. -/
theorem kappaATRq_le_trqCallKappaA (hpos : 0 < trqKappaDelta f P q L ϑ y)
    (hM : finMax 0 (fun i => ‖iteratedFDeriv ℝ i f y‖) q ≤ M) (hϑ : 0 < ϑ) (hM0 : 0 < M) :
    kappaATRq f P q L ϑ y ≤ trqCallKappaA P L ϑ M q :=
  mul_le_mul_of_nonneg_right (kappaSTRq_le_trqCallKappaS hpos hM hϑ hM0)
    (zero_le_one.trans one_le_trqKappaUns)

/-- `κ^C_{TRq} ≤ κ^C(M)` under the hypotheses of `trqCallKappaDelta_le_trqKappaDelta`, `ϑ ≤ 1`. -/
theorem kappaCTRq_le_trqCallKappaC (hpos : 0 < trqKappaDelta f P q L ϑ y)
    (hM : finMax 0 (fun i => ‖iteratedFDeriv ℝ i f y‖) q ≤ M) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1)
    (hM0 : 0 < M) : kappaCTRq f P q L ϑ y ≤ trqCallKappaC P L ϑ M q := by
  have hκ := trqCallKappaDelta_le_trqKappaDelta hpos hM hϑ.le
  have hκ' := trqCallKappaDelta_pos (P := P) (L := L) (q := q) hϑ hM0
  have hκ1 : trqKappaDelta f P q L ϑ y < 1 := trqKappa_lt_one one_le_finMax hϑ1
  have hg : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
  unfold kappaCTRq trqCallKappaC
  have hlogκ : |Real.log (trqKappaDelta f P q L ϑ y)| ≤
      |Real.log (trqCallKappaDelta P L ϑ M q)| := by
    rw [abs_of_nonpos (Real.log_nonpos hpos.le hκ1.le),
      abs_of_nonpos (Real.log_nonpos hκ'.le (hκ.trans hκ1.le))]
    exact neg_le_neg (Real.log_le_log hκ' hκ)
  have : |Real.log (P.ς * trqKappaDelta f P q L ϑ y / P.Δ₀)| ≤
      |Real.log P.ς| + |Real.log (trqCallKappaDelta P L ϑ M q)| + |Real.log P.Δ₀| := by
    rw [Real.log_div (mul_pos P.ς_pos hpos).ne' P.Δ₀_pos.ne', Real.log_mul P.ς_pos.ne' hpos.ne']
    calc _ ≤ |Real.log P.ς + Real.log (trqKappaDelta f P q L ϑ y)| + |Real.log P.Δ₀| :=
          abs_sub _ _
      _ ≤ |Real.log P.ς| + |Real.log (trqKappaDelta f P q L ϑ y)| + |Real.log P.Δ₀| :=
          add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by linarith
  linarith [div_le_div_of_nonneg_right this hg.le]

end Constants

/-! ### Runs with a feasible set -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {X : Set E} {P : TRqParams} {q : ℕ} {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → E}
  {Δ : ℕ → ℝ} {jk : ℕ → ℕ} {d : ℕ → ℕ → E} {L : ℕ → ℝ} {M : ℝ}

/-- **Runs of TRq with a feasible set exist** ([cartis2022evaluation], Algorithm 12.2.1 with
feasible displacements `{d | y + d ∈ X}`, as used in §14.2): in finite dimension, for a closed `X`,
`ϑ ≥ 0` and every `x₀ ∈ X` (from `exists_isTRqRun`; the iterates stay in `X` up to
termination). -/
theorem exists_isTRqRun_feasible [FiniteDimensional ℝ E] (hX : IsClosed X) (f : E → ℝ)
    (P : TRqParams) (q : ℕ) (ε : ℕ → ℝ) (hϑ : 0 ≤ ϑ) {x₀ : E} (hx₀ : x₀ ∈ X) :
    ∃ (x s : ℕ → E) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → E), x 0 = x₀ ∧
      IsTRqRun f (𝒥 f x) (𝒳 X x) P q ε ϑ x s Δ jk d := by
  classical
  obtain ⟨C', hC'⟩ : ∃ C' : E → Set E,
      ∀ y, C' y = if y ∈ X then {e | y + e ∈ X} else univ := ⟨_, fun _ => rfl⟩
  have hC : ∀ y, IsClosed (C' y) := fun y => by
    rw [hC']
    by_cases hy : y ∈ X
    · simp only [hy, ↓reduceIte]
      exact hX.preimage (continuous_const.add continuous_id)
    · simp only [hy, ↓reduceIte]
      exact isClosed_univ
  have hC0 : ∀ y, (0 : E) ∈ C' y := fun y => by
    rw [hC']
    by_cases hy : y ∈ X <;> simp [hy]
  obtain ⟨x, s, Δ, jk, d, hx0, hr⟩ := exists_isTRqRun f
    (fun y => ftaylorSeries ℝ f y) C' hC hC0 P q ε hϑ x₀
  have hmem : ∀ k, (∀ i < k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) → x k ∈ X := by
    intro k
    induction k with
    | zero => intro _; rw [hx0]; exact hx₀
    | succ k ih =>
      intro hk
      have hk' : ∀ i ≤ k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i :=
        fun i hi => hk i (Nat.lt_succ_of_le hi)
      have hxk := ih fun i hi => hk' i hi.le
      have hacc := hr.accept k hk'
      by_cases hs : P.η₁ ≤ trqRatio f (𝒥 f x) x s jk k
      · rw [hacc.eq_add hs]
        have := (hr.step k hk').mem.2
        rw [hC'] at this
        simp only [hxk, ↓reduceIte] at this
        exact this
      · rw [hacc.eq_self (not_le.1 hs)]
        exact hxk
  have hS : ∀ k, (∀ i < k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) → C' (x k) = {e | x k + e ∈ X} :=
    fun k hk => by
    rw [hC']
    simp only [hmem k hk, ↓reduceIte]
  refine ⟨x, s, Δ, jk, d, hx0, ⟨⟨hr.delta_zero, fun k hk => ?_, hr.accept⟩,
    fun k hk j hj => ?_, hr.cap⟩⟩
  · have h1 := hr.step k hk
    have h2 := hS k fun i hi => hk i hi.le
    exact h2 ▸ h1
  · have h1 := hr.witness k hk j hj
    have h2 := hS k hk
    exact h2 ▸ h1

/-- With exact data, `f` does not increase along a TRq run before termination (for any data `D`
and feasible sets `S`, `ε ≥ 0`, `ϑ ≥ 0`): a step has a positive predicted decrease. -/
theorem IsTRqRun.apply_succ_le {D : ℕ → FormalMultilinearSeries ℝ E ℝ} {S : ℕ → Set E}
    (h : IsTRqRun f D S P q ε ϑ x s Δ jk d) (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) (hϑ : 0 ≤ ϑ)
    {k : ℕ} (hk : ∀ i ≤ k, ¬ trqTest D P q ε ϑ Δ d i) : f (x (k + 1)) ≤ f (x k) := by
  have hst := h.isTRqStep hk
  have hδ : 0 ≤ min (Δ k) ϑ := le_min (h.delta_pos' fun i hi => hk i hi.le).le hϑ
  have hpos : 0 < (D k).taylorDecrement (jk k) (s k) := by
    refine lt_of_le_of_lt ?_ (hst.lt_taylorDecrement.trans_le hst.taylorDecrement_le)
    exact div_nonneg (mul_nonneg (mul_nonneg P.ς_pos.le (hε _ hst.order_mem))
      (pow_nonneg hδ _)) (Nat.cast_nonneg _)
  exact (h.accept k hk).le trqRatio_eq hpos

/-- **The radius bound of a call** (Lemma 12.2.3 of [cartis2022evaluation] with (12.2.9) and
`κ_Δ ≥ κ_Δ(M)`): up to and including termination, `Δ_e ≥ κ_ρ ε_min`, for a run with exact data on
`X ⊆ C` under `LipschitzDerivsAnchored f C A 1 q L` with `A ⊇ {y ∈ X | f(y) ≤ f(x₀)}`, the
derivatives at `x₀` bounded by `M`, `ε_j > 0` and `0 < ϑ ≤ 1`. -/
theorem IsTRqRun.trqCallKappaRad_mul_le {C A : Set E}
    (hr : IsTRqRun f (𝒥 f x) (𝒳 X x) P q ε ϑ x s Δ jk d)
    (hf : LipschitzDerivsAnchored f C A 1 q L) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) (hx0 : x 0 ∈ X)
    (hM : finMax 0 (fun i => ‖iteratedFDeriv ℝ i f (x 0)‖) q ≤ M)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {e : ℕ}
    (hnot : ∀ i < e, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) :
    trqCallKappaRad P L ϑ M q * finMin 1 ε q ≤ Δ e := by
  have hεm1 : finMin 1 ε q ≤ 1 := finMin_le_left
  have hεm0 : 0 < finMin 1 ε q := finMin_pos one_pos hε
  rcases e with _ | k
  · rw [hr.toIsTRRun.delta_zero]
    calc trqCallKappaRad P L ϑ M q * finMin 1 ε q ≤ P.Δ₀ * 1 :=
          mul_le_mul (min_le_right _ _) hεm1 hεm0.le P.Δ₀_pos.le
      _ = P.Δ₀ := mul_one _
  · have hk : ∀ i ≤ k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i := fun i hi => hnot i (by omega)
    obtain ⟨⟨hκ0, -⟩, -, hΔ⟩ := hr.radius_ge_of_anchored hf hXC hA hx0 hϑ0 hϑ1
      (fun j hj => (hε j hj).le) hk
    have hgap : P.ς * finMin 1 ε q ≤
        prefixMin (fun i => trqGap (ftaylorSeries ℝ f (x i)) (jk i) (min (Δ i) ϑ) (d i (jk i)))
          k :=
      (hr.trqGap_ge hϑ0 (fun _ hj => finMin_le hj) hk).1
    have hκ := trqCallKappaDelta_le_trqKappaDelta hκ0 hM hϑ0.le
    refine le_trans (le_min ?_ ?_) hΔ
    · calc trqCallKappaRad P L ϑ M q * finMin 1 ε q ≤ (P.γ₁ * ϑ) * 1 :=
            mul_le_mul trqCallKappaRad_le_γ₁ hεm1 hεm0.le (mul_pos P.γ₁_pos hϑ0).le
        _ = P.γ₁ * ϑ := mul_one _
    · calc trqCallKappaRad P L ϑ M q * finMin 1 ε q ≤
            (trqCallKappaDelta P L ϑ M q * P.ς) * finMin 1 ε q :=
            mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) hεm0.le
        _ = trqCallKappaDelta P L ϑ M q * (P.ς * finMin 1 ε q) := by ring
        _ ≤ _ := mul_le_mul hκ hgap (mul_pos P.ς_pos hεm0).le hκ0.le

/-! ### Calls cut before termination -/

/-- **A call of TRq with a feasible set** ([cartis2022evaluation], Algorithm 12.2.1 used as INNER,
e.g. in Algorithm 14.3.2): the points `xi 0, …, xi e` are the first `e + 1` iterates of a run of
TRq with exact data on `f` with feasible displacements `{d | x_i + d ∈ X}`, tolerances `ε` and
threshold `ϑ`, whose first termination index `k_ε` is at least `e` (the call may be cut before
termination); `succ i` holds for `i < e` exactly when iteration `i` of the run is successful, and
the returned radii are the optimality radii `δ_j = min(Δ_e, ϑ)`, `j ∈ [1, q]`, at the last iterate
(at termination these certify `(ε, δ)`-approximate optimality, `IsTRqRun.complexity`). -/
def IsTRqCallOut (f : E → ℝ) (X : Set E) (P : TRqParams) (q : ℕ) (ε : ℕ → ℝ) (ϑ : ℝ)
    (xi : ℕ → E) (e : ℕ) (succ : ℕ → Prop) (δo : ℕ → ℝ) : Prop :=
  ∃ (x s : ℕ → E) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → E) (kε : ℕ),
    IsTRqRun f (𝒥 f x) (𝒳 X x) P q ε ϑ x s Δ jk d ∧
    IsFirstHit (trqTest (𝒥 f x) P q ε ϑ Δ d) kε ∧
    e ≤ kε ∧ (∀ i ≤ e, xi i = x i) ∧
    (∀ i < e, (succ i ↔ P.η₁ ≤ trqRatio f (𝒥 f x) x s jk i)) ∧
    ∀ j ∈ Finset.Icc 1 q, δo j = min (Δ e) ϑ

namespace IsTRqCallOut

variable {xi : ℕ → E} {e : ℕ} {succ : ℕ → Prop} {δo : ℕ → ℝ}

/-- Unsuccessful iterations of a call do not move. -/
theorem eq_of_not_succ (h : IsTRqCallOut f X P q ε ϑ xi e succ δo) :
    ∀ i < e, ¬ succ i → xi (i + 1) = xi i := by
  obtain ⟨x, s, Δ, jk, d, kε, hr, hhit, he, hxi, hsucc, -⟩ := h
  intro i hi hs
  rw [hxi i hi.le, hxi (i + 1) hi]
  exact hr.toIsTRRun.eq_of_not_succ (fun l hl => hhit.2 l (by omega))
    (not_le.1 ((hsucc i hi).not.1 hs))

variable {C A : Set E}

/-- **The radius bound of a call**: `Δ_e ≥ κ_ρ ε_min` at the last iterate
(`IsTRqRun.trqCallKappaRad_mul_le`), for an objective satisfying `LipschitzDerivsAnchored` on the
sublevel set of the start with derivatives bounded there by `M > 0`, `ε ∈ (0, 1]^q` and
`ε_min ≤ ϑ ≤ 1`; hence the returned radii `min(Δ_e, ϑ)` are at least `κ_ρ ε_min`. -/
theorem radius_ge (h : IsTRqCallOut f X P q ε ϑ xi e succ δo)
    (hf : LipschitzDerivsAnchored f C A 1 q L) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y ≤ f (xi 0) → y ∈ A) (hx0 : xi 0 ∈ X)
    (hM : finMax 0 (fun i => ‖iteratedFDeriv ℝ i f (xi 0)‖) q ≤ M)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1) :
    ∀ j ∈ Finset.Icc 1 q, trqCallKappaRad P L ϑ M q * finMin 1 ε q ≤ δo j := by
  obtain ⟨x, s, Δ, jk, d, kε, hr, hhit, he, hxi, -, hδo⟩ := h
  have h0 := hxi 0 (Nat.zero_le _)
  rw [h0] at hA hx0 hM
  have hεm0 : 0 < finMin 1 ε q := finMin_pos one_pos fun j hj => (hε j hj).1
  have hϑ0 : 0 < ϑ := hεm0.trans_le hϑ
  have hrad := hr.trqCallKappaRad_mul_le hf hXC hA hx0 hM (fun j hj => (hε j hj).1) hϑ0 hϑ1
    fun i hi => hhit.2 i (lt_of_lt_of_le hi he)
  intro j hj
  rw [hδo j hj]
  refine le_min hrad ?_
  calc trqCallKappaRad P L ϑ M q * finMin 1 ε q ≤ (P.γ₁ * ϑ) * 1 :=
        mul_le_mul trqCallKappaRad_le_γ₁ finMin_le_left hεm0.le (mul_pos P.γ₁_pos hϑ0).le
    _ ≤ ϑ := by nlinarith [P.γ₁_le_one]

open Classical in
/-- **The number of iterations of a call** ([cartis2022evaluation], Lemma 2.3.1 with the radius
bound of Lemma 12.2.3): `e ≤ κ_uns (|𝒮| + 1) + |log(κ_ρ ε_min/Δ₀)|/|log γ₂|`, `𝒮` the
successful iterations of the call, under the hypotheses of `IsTRqCallOut.radius_ge`. -/
theorem le_count (h : IsTRqCallOut f X P q ε ϑ xi e succ δo)
    (hf : LipschitzDerivsAnchored f C A 1 q L) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y ≤ f (xi 0) → y ∈ A) (hx0 : xi 0 ∈ X)
    (hM : finMax 0 (fun i => ‖iteratedFDeriv ℝ i f (xi 0)‖) q ≤ M) (hM0 : 0 < M)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1) :
    (e : ℝ) ≤ trqKappaUns P * ((Finset.range e).filter succ).card + trqKappaUns P +
      |Real.log (trqCallKappaRad P L ϑ M q * finMin 1 ε q / P.Δ₀)| / |Real.log P.γ₂| := by
  obtain ⟨x, s, Δ, jk, d, kε, hr, hhit, he, hxi, hsucc, -⟩ := h
  have h0 := hxi 0 (Nat.zero_le _)
  rw [h0] at hA hx0 hM
  have hεm0 : 0 < finMin 1 ε q := finMin_pos one_pos fun j hj => (hε j hj).1
  have hϑ0 : 0 < ϑ := hεm0.trans_le hϑ
  have hnot : ∀ i < e, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i :=
    fun i hi => hhit.2 i (lt_of_lt_of_le hi he)
  have hrad := hr.trqCallKappaRad_mul_le hf hXC hA hx0 hM (fun j hj => (hε j hj).1) hϑ0 hϑ1 hnot
  have h3 := hr.toIsTRRun.le_succ_count hnot (mul_pos (trqCallKappaRad_pos hϑ0 hM0) hεm0) hrad
  have hS' : (Finset.range e).filter succ =
      (Finset.range e).filter (fun j => P.η₁ ≤ trqRatio f (𝒥 f x) x s jk j) :=
    Finset.filter_congr fun i hi => hsucc i (Finset.mem_range.1 hi)
  have hcard := card_successSet_le_card_filter_add_one
    (fun j => P.η₁ ≤ trqRatio f (𝒥 f x) x s jk j) e
  rw [hS']
  have hu := one_le_trqKappaUns (P := P)
  have := mul_le_mul_of_nonneg_right hcard (zero_le_one.trans hu)
  unfold trqKappaUns at hu this ⊢
  linarith

/-- **The decrease of a call** ([cartis2022evaluation], Lemma 12.2.4 with `κ_Δ ≥ κ_Δ(M)`, the
TRq-SC row of Lemma 14.2.2): every successful iteration decreases `f` by at least
`κ_decr ε_min^{q+1}`, under the hypotheses of `IsTRqCallOut.le_count`. -/
theorem decrease (h : IsTRqCallOut f X P q ε ϑ xi e succ δo)
    (hf : LipschitzDerivsAnchored f C A 1 q L) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y ≤ f (xi 0) → y ∈ A) (hx0 : xi 0 ∈ X)
    (hM : finMax 0 (fun i => ‖iteratedFDeriv ℝ i f (xi 0)‖) q ≤ M) (hM0 : 0 < M)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1) :
    ∀ i < e, succ i →
      trqCallKappaDecr P L ϑ M q * finMin 1 ε q ^ (q + 1) ≤ f (xi i) - f (xi (i + 1)) := by
  obtain ⟨x, s, Δ, jk, d, kε, hr, hhit, he, hxi, hsucc, -⟩ := h
  have h0 := hxi 0 (Nat.zero_le _)
  rw [h0] at hA hx0 hM
  have hεm0 : 0 < finMin 1 ε q := finMin_pos one_pos fun j hj => (hε j hj).1
  have hϑ0 : 0 < ϑ := hεm0.trans_le hϑ
  have hnot : ∀ i < e, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i :=
    fun i hi => hhit.2 i (lt_of_lt_of_le hi he)
  intro i hi hs
  have hdec := (hr.taylorDecrement_ge_of_anchored hf hXC hA hx0 hε hϑ hϑ1
    fun l hl => hnot l (by omega)).2 ((hsucc i hi).1 hs)
  obtain ⟨⟨hκ0, -⟩, -⟩ := hr.radius_ge_of_anchored hf hXC hA hx0 hϑ0 hϑ1
    (fun j hj => (hε j hj).1.le) (k := 0) (fun l hl => hnot l (by omega))
  have hκ := trqCallKappaDelta_le_trqKappaDelta hκ0 hM hϑ0.le
  rw [hxi i hi.le, hxi (i + 1) hi]
  refine le_trans ?_ hdec
  have hκ' := trqCallKappaDelta_pos (P := P) (L := L) (q := q) hϑ0 hM0
  have hpow : (P.ς * trqCallKappaDelta P L ϑ M q) ^ (q + 1) ≤
      (P.ς * trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) :=
    pow_le_pow_left₀ (mul_pos P.ς_pos hκ').le (mul_le_mul_of_nonneg_left hκ P.ς_pos.le) _
  unfold trqCallKappaDecr
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hpow (by positivity)) (by positivity)) P.η₁_pos.le

end IsTRqCallOut

open Classical in
/-- **Calls stopped by an external test exist**: in finite dimension, for a closed `X`, `f ≥ f_low`
on `X`, `LipschitzDerivsAnchored f C A 1 q L` with `X ⊆ C` and `A ⊇ {y ∈ X | f(y) ≤ f(x₀)}`,
`ε ∈ (0, 1]^q`, `ε_min ≤ ϑ ≤ 1` and any test `stop` on points, there is a call from `x₀`
(`IsTRqCallOut`) cut at the first iterate satisfying `stop` or at the termination of the run
(which terminates, `IsTRqRun.complexity`), whichever comes first. Its iterates do not increase
`f` and stay in `X`, the returned radii are a common `δ ∈ (0, 1]`, and at the last iterate either
`stop` holds or the run has terminated with an `(ε, δ)`-approximate `q`-th order minimizer on
`X`. -/
theorem exists_isTRqCallOut_of_stop [FiniteDimensional ℝ E] {C A : Set E} {flow : ℝ}
    (hX : IsClosed X) (hb : ∀ y ∈ X, flow ≤ f y) (hf : LipschitzDerivsAnchored f C A 1 q L)
    (hXC : X ⊆ C) {x₀ : E} (hx₀ : x₀ ∈ X) (hA : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (P : TRqParams) (stop : E → Prop) :
    ∃ (xi : ℕ → E) (e : ℕ) (succ : ℕ → Prop) (δ : ℝ),
      IsTRqCallOut f X P q ε ϑ xi e succ (fun _ => δ) ∧ xi 0 = x₀ ∧ xi e ∈ X ∧ δ ∈ Ioc 0 1 ∧
      (∀ i < e, f (xi (i + 1)) ≤ f (xi i)) ∧ f (xi e) ≤ f x₀ ∧ (∀ i < e, ¬ stop (xi i)) ∧
      (stop (xi e) ∨
        IsEpsDeltaApprox (ftaylorSeries ℝ f (xi e)) {d | xi e + d ∈ X} q ε (fun _ => δ)) := by
  have hϑ0 : 0 < ϑ := (finMin_pos one_pos fun j hj => (hε j hj).1).trans_le hϑ
  have hε0 : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j := fun j hj => (hε j hj).1.le
  obtain ⟨x, s, Δ, jk, d, hx0, hr⟩ := exists_isTRqRun_feasible hX f P q ε hϑ0.le hx₀
  have hA' : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A := by rw [hx0]; exact hA
  have hx0' : x 0 ∈ X := hx0 ▸ hx₀
  obtain ⟨kε, hhit, -, -, hcert, -, -⟩ :=
    IsTRqRun.complexity (flow := flow) hb hf hXC hA' hx0' hε hϑ hϑ1 hr
  have hex : ∃ i, i = kε ∨ stop (x i) := ⟨kε, Or.inl rfl⟩
  have he_le : Nat.find hex ≤ kε := Nat.find_min' hex (Or.inl rfl)
  have hnot : ∀ i < Nat.find hex, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i :=
    fun i hi => hhit.2 i (by omega)
  have hsub := hr.mem_sublevel hx0' hε0 hϑ0.le (Nat.find hex) hnot
  refine ⟨x, Nat.find hex, fun i => P.η₁ ≤ trqRatio f (𝒥 f x) x s jk i,
    min (Δ (Nat.find hex)) ϑ, ⟨x, s, Δ, jk, d, kε, hr, hhit, he_le, fun _ _ => rfl,
    fun _ _ => Iff.rfl, fun _ _ => rfl⟩, hx0, hsub.1,
    ⟨lt_min (hr.delta_pos' hnot) hϑ0, (min_le_right _ _).trans hϑ1⟩,
    fun i hi => hr.apply_succ_le hε0 hϑ0.le fun l hl => hnot l (by omega), hx0 ▸ hsub.2,
    fun i hi => (not_or.1 (Nat.find_min hex hi)).2, ?_⟩
  by_cases hst : stop (x (Nat.find hex))
  · exact Or.inl hst
  · right
    have hek : Nat.find hex = kε := (Nat.find_spec hex).resolve_right hst
    rw [hek]
    exact hcert

/-! ### Terminating calls and their cost -/

/-- `(y, δ)` is the output of a terminating call of TRq with a feasible set from `x^S` that uses
`nF` evaluations of `f` and `nD` evaluations of its derivatives: a run with exact data on `X` from
`x^S` terminating first at `k_ε` with `x_{k_ε} = y`, returned radii `δ_j = min(Δ_{k_ε}, ϑ)`,
`nF = k_ε + 1` (`funEvalCount`) and `nD` the number of successful iterations plus one
(`derivEvalCount`). -/
def IsTRqOutputCost (f : E → ℝ) (X : Set E) (P : TRqParams) (q : ℕ) (ε : ℕ → ℝ) (ϑ : ℝ)
    (xS y : E) (δ : ℕ → ℝ) (nF nD : ℕ) : Prop :=
  ∃ (x s : ℕ → E) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → E) (kε : ℕ),
    IsTRqRun f (𝒥 f x) (𝒳 X x) P q ε ϑ x s Δ jk d ∧
    IsFirstHit (trqTest (𝒥 f x) P q ε ϑ Δ d) kε ∧
    x 0 = xS ∧ x kε = y ∧ (∀ j ∈ Finset.Icc 1 q, δ j = min (Δ kε) ϑ) ∧
    nF = funEvalCount kε ∧
    nD = derivEvalCount (fun k => P.η₁ ≤ trqRatio f (𝒥 f x) x s jk k) kε

/-- **The cost of a terminating call** ([cartis2022evaluation], Theorem 12.2.5 with a feasible set,
the TRq-SC row of Theorem 14.2.4, with `κ_Δ ≥ κ_Δ(M)`): for `f ≥ f_low` on `X`,
`LipschitzDerivsAnchored f C A 1 q L` with `X ⊆ C` and `A ⊇ {z ∈ X | f(z) ≤ f(x^S)}`, the
derivatives at `x^S` bounded by `M > 0`, `ε ∈ (0, 1]^q` and `ε_min ≤ ϑ ≤ 1`, the call uses at most
`κ^A (f(x^S) - f_low)/ε_min^{q+1} + κ^B |log ε_min| + κ^C` evaluations of `f` and
`κ^S (f(x^S) - f_low)/ε_min^{q+1} + 1` derivative evaluations, with the constants of the call. -/
theorem IsTRqOutputCost.cost_le {C A : Set E} {flow : ℝ} {xS y : E} {δ : ℕ → ℝ} {nF nD : ℕ}
    (h : IsTRqOutputCost f X P q ε ϑ xS y δ nF nD) (hb : ∀ z ∈ X, flow ≤ f z)
    (hf : LipschitzDerivsAnchored f C A 1 q L) (hXC : X ⊆ C)
    (hA : ∀ z ∈ X, f z ≤ f xS → z ∈ A) (hxS : xS ∈ X)
    (hM : finMax 0 (fun i => ‖iteratedFDeriv ℝ i f xS‖) q ≤ M) (hM0 : 0 < M)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1) :
    (nF : ℝ) ≤ trqCallKappaA P L ϑ M q * (f xS - flow) / finMin 1 ε q ^ (q + 1) +
        kappaBTRq P * |Real.log (finMin 1 ε q)| + trqCallKappaC P L ϑ M q ∧
      (nD : ℝ) ≤ trqCallKappaS P L ϑ M q * (f xS - flow) / finMin 1 ε q ^ (q + 1) + 1 := by
  obtain ⟨x, s, Δ, jk, d, kε, hr, hhit, hx0, -, -, hnF, hnD⟩ := h
  subst hx0 hnF hnD
  obtain ⟨kε', hhit', -, -, -, hF', hD'⟩ :=
    IsTRqRun.complexity (flow := flow) hb hf hXC hA hxS hε hϑ hϑ1 hr
  rw [hhit'.unique hhit] at hF' hD'
  have hεm0 : 0 < finMin 1 ε q := finMin_pos one_pos fun j hj => (hε j hj).1
  have hϑ0 : 0 < ϑ := hεm0.trans_le hϑ
  have hF0 : 0 ≤ f (x 0) - flow := sub_nonneg.2 (hb _ hxS)
  have hB0 : 0 ≤ kappaBTRq P := by unfold kappaBTRq; positivity
  have hA0 := trqCallKappaA_nonneg (P := P) (L := L) (q := q) hϑ0 hM0
  have hS0 := trqCallKappaS_nonneg (P := P) (L := L) (q := q) hϑ0 hM0
  have hC1 := one_le_trqCallKappaC (P := P) (L := L) (ϑ := ϑ) (M := M) (q := q)
  have hpow : 0 < finMin 1 ε q ^ (q + 1) := pow_pos hεm0 _
  have hAt : 0 ≤ trqCallKappaA P L ϑ M q * (f (x 0) - flow) / finMin 1 ε q ^ (q + 1) := by
    positivity
  have hSt : 0 ≤ trqCallKappaS P L ϑ M q * (f (x 0) - flow) / finMin 1 ε q ^ (q + 1) := by
    positivity
  have hlog0 : 0 ≤ kappaBTRq P * |Real.log (finMin 1 ε q)| := by positivity
  rcases Nat.eq_zero_or_pos kε with h0 | hpos
  · subst h0
    have e1 : (funEvalCount 0 : ℝ) = 1 := by simp [funEvalCount]
    have e2 : (derivEvalCount (fun k => P.η₁ ≤ trqRatio f (𝒥 f x) x s jk k) 0 : ℝ) = 1 := by
      simp [derivEvalCount]
    rw [e1, e2]
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨⟨hκ0, -⟩, -⟩ := hr.radius_ge_of_anchored hf hXC hA hxS hϑ0 hϑ1
      (fun j hj => (hε j hj).1.le) (k := 0) (fun i hi => hhit.2 i (by omega))
    have hSle := kappaSTRq_le_trqCallKappaS hκ0 hM hϑ0 hM0
    have hAle := kappaATRq_le_trqCallKappaA hκ0 hM hϑ0 hM0
    have hCle := kappaCTRq_le_trqCallKappaC hκ0 hM hϑ0 hϑ1 hM0
    have h1 : kappaATRq f P q L ϑ (x 0) * (f (x 0) - flow) / finMin 1 ε q ^ (q + 1) ≤
        trqCallKappaA P L ϑ M q * (f (x 0) - flow) / finMin 1 ε q ^ (q + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAle hF0) hpow.le
    have h2 : kappaSTRq f P q L ϑ (x 0) * (f (x 0) - flow) / finMin 1 ε q ^ (q + 1) ≤
        trqCallKappaS P L ϑ M q * (f (x 0) - flow) / finMin 1 ε q ^ (q + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hSle hF0) hpow.le
    exact ⟨by linarith, by linarith⟩

end Optimization
