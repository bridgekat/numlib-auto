import Numlib.Analysis.Calculus.AnchoredLipschitzDerivs
import Numlib.Optimization.Complexity.Telescoping
import Numlib.Optimization.ModelBased.HighOrder.Orders
import Numlib.Optimization.ModelBased.HighOrder.TRq

/-!
# Evaluation complexity of TRq with exact derivatives

The complexity analysis of the trust-region method TRq ([cartis2022evaluation], §12.2.1,
Algorithm 12.2.1) run with the exact Taylor data `D k = ftaylorSeries ℝ f (x k)` on a feasible set
`X` (displacements `{e | x k + e ∈ X}`; the unconstrained method is `X = univ`, TRq-SC of §14.2 is a
closed `X`), under the anchored smoothness assumption `LipschitzDerivsAnchored f C A 1 q L`: `X ⊆ C`
with `C` open and convex, and the derivatives of orders `1, …, q` are Lipschitz anchored at the
points of a set `A` containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}`.

The iterates stay in that sublevel set (`IsTRqRun.mem_sublevel`): an accepted step has a positive
Taylor decrease, hence does not increase `f`. The models are built at the iterates, which are
anchors, so Taylor's theorem anchored at the iterate gives the model fidelity
(`IsTRqRun.abs_sub_le_of_lipschitzDerivsAnchored`) that the generic one-iteration lemmas of
`Numlib.Optimization.ModelBased.HighOrder.TRq` assume. Lipschitz derivatives on all of `C` (in
particular on the whole space) are the case `A = C`.

## Main definitions

* `Optimization.trqKappaDelta`: the radius constant `κ_Δ` of (12.2.14) with `L_f = finMax 1 L q`;
* `Optimization.kappaSTRq`, `kappaATRq`, `kappaBTRq`, `kappaCTRq`: the constants of the
  evaluation bounds of Theorem 12.2.5.

## Main results

* `Optimization.IsTRqRun.mem_of_feasible`, `Optimization.IsTRqRun.mem_sublevel`;
* `Optimization.IsTRqRun.abs_sub_le_of_lipschitzDerivsAnchored`: model fidelity ((A.19));
* `Optimization.IsTRqRun.radius_ge_of_anchored`: Lemma 12.2.3;
* `Optimization.IsTRqRun.taylorDecrement_ge_of_anchored`: Lemma 12.2.4;
* `Optimization.IsTRqRun.complexity`: Theorem 12.2.5 — the run terminates at an
  `(ε, δ)`-approximate `q`-th order minimizer on `X` within
  `O(κ (f(x₀) - f_low) ε_min^{-(q+1)} + |log ε_min|)` evaluations of `f` and
  `O(κ (f(x₀) - f_low) ε_min^{-(q+1)})` evaluations of the derivatives.
-/

open Set
open scoped Nat

namespace Optimization

/-- The exact Taylor data `k ↦ ftaylorSeries ℝ f (x k)` along the iterates. -/
local notation "𝒥" f:max x:max => fun k : ℕ => ftaylorSeries ℝ f (x k)

/-- The feasible displacements `k ↦ {e | x k + e ∈ X}`. -/
local notation "𝒳" X:max x:max => fun k : ℕ => Set.ofPred fun e => x k + e ∈ X

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {P : TRqParams} {q : ℕ} {ε : ℕ → ℝ} {ϑ : ℝ} {x s : ℕ → E}
  {Δ : ℕ → ℝ} {jk : ℕ → ℕ} {d : ℕ → ℕ → E} {L : ℕ → ℝ}

/-- The constant `κ_Δ` of (12.2.14): `γ₁ (1 - η₂)/L_f · min(ϑ, Δ₀ δ₀^q/(2 q! max_i ‖∇^i f(x₀)‖))`
with `δ₀ = min(Δ₀, ϑ)`. -/
noncomputable def trqKappaDelta (f : E → ℝ) (P : TRqParams) (q : ℕ) (L : ℕ → ℝ) (ϑ : ℝ)
    (x₀ : E) : ℝ :=
  trqKappa P (finMax 1 L q) ϑ (finMax 0 (fun i => ‖iteratedFDeriv ℝ i f x₀‖) q) q

theorem trqKappaDelta_nonneg (hϑ : 0 ≤ ϑ) (x₀ : E) : 0 ≤ trqKappaDelta f P q L ϑ x₀ := by
  have hM : 0 ≤ finMax 0 (fun i => ‖iteratedFDeriv ℝ i f x₀‖) q := le_finMax_left
  have hL : 0 < finMax 1 L q := zero_lt_one.trans_le le_finMax_left
  have := P.γ₁_pos
  have := P.one_sub_η₂_pos
  have := P.Δ₀_pos
  unfold trqKappaDelta trqKappa
  have : (0 : ℝ) < q ! := by positivity
  positivity

/-- The derivatives of orders `1, …, q` at `x₀` are bounded by `max_i ‖∇^i f(x₀)‖`
(`finMax 0`), the constant of (12.2.14). -/
theorem norm_ftaylorSeries_le_finMax (x₀ : E) : ∀ i ∈ Finset.Icc 1 q,
    ‖ftaylorSeries ℝ f x₀ i‖ ≤ finMax 0 (fun i => ‖iteratedFDeriv ℝ i f x₀‖) q :=
  fun _ hi => le_finMax (u := fun i => ‖iteratedFDeriv ℝ i f x₀‖) hi

/-- The constant `κ^S_{TRq} = q!/(η₁ (ς κ_Δ)^{q+1})` of Theorem 12.2.5. -/
noncomputable def kappaSTRq (f : E → ℝ) (P : TRqParams) (q : ℕ) (L : ℕ → ℝ) (ϑ : ℝ)
    (x₀ : E) : ℝ :=
  q ! / (P.η₁ * (P.ς * trqKappaDelta f P q L ϑ x₀) ^ (q + 1))

/-- The constant `κ^A_{TRq} = κ^S_{TRq} (1 + log γ₃/|log γ₂|)` of Theorem 12.2.5. -/
noncomputable def kappaATRq (f : E → ℝ) (P : TRqParams) (q : ℕ) (L : ℕ → ℝ) (ϑ : ℝ)
    (x₀ : E) : ℝ :=
  kappaSTRq f P q L ϑ x₀ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|)

/-- The constant `κ^B_{TRq} = 1/|log γ₂|` of Theorem 12.2.5. -/
noncomputable def kappaBTRq (P : TRqParams) : ℝ :=
  1 / |Real.log P.γ₂|

theorem kappaBTRq_nonneg (P : TRqParams) : 0 ≤ kappaBTRq P := by
  unfold kappaBTRq; positivity

/-- The constant `κ^C_{TRq} = |log(ς κ_Δ/Δ₀)|/|log γ₂| + 1` of Theorem 12.2.5. -/
noncomputable def kappaCTRq (f : E → ℝ) (P : TRqParams) (q : ℕ) (L : ℕ → ℝ) (ϑ : ℝ)
    (x₀ : E) : ℝ :=
  |Real.log (P.ς * trqKappaDelta f P q L ϑ x₀ / P.Δ₀)| / |Real.log P.γ₂| + 1

/-- The iterates of a feasible TRq run stay in `X` up to termination. -/
theorem IsTRqRun.mem_of_feasible {X : Set E} (h : IsTRqRun f (𝒥 f x) (𝒳 X x) P q ε ϑ x s Δ jk d)
    (hx0 : x 0 ∈ X) : ∀ k, (∀ i < k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) → x k ∈ X := by
  intro k
  induction k with
  | zero => exact fun _ => hx0
  | succ k ih =>
    intro hk
    have hk' : ∀ i ≤ k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i := fun i hi => hk i (Nat.lt_succ_of_le hi)
    have hacc := h.accept k hk'
    by_cases hs : P.η₁ ≤ trqRatio f (𝒥 f x) x s jk k
    · rw [hacc.eq_add hs]
      exact (h.isTRqStep hk').mem.2
    · rw [hacc.eq_self (not_le.1 hs)]
      exact ih fun i hi => hk' i hi.le

/-- The iterates of a feasible TRq run with `ε ≥ 0` and `ϑ ≥ 0` stay in the sublevel set
`{y ∈ X | f(y) ≤ f(x₀)}` up to termination: a step has a positive Taylor decrease, so an accepted
step does not increase `f`. -/
theorem IsTRqRun.mem_sublevel {X : Set E} (h : IsTRqRun f (𝒥 f x) (𝒳 X x) P q ε ϑ x s Δ jk d)
    (hx0 : x 0 ∈ X) (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) (hϑ : 0 ≤ ϑ) :
    ∀ k, (∀ i < k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) → x k ∈ X ∧ f (x k) ≤ f (x 0) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨hx0, le_rfl⟩
  | succ k ih =>
    intro hk
    have hk' : ∀ i ≤ k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i := fun i hi => hk i (Nat.lt_succ_of_le hi)
    have hst := h.isTRqStep hk'
    have hδ : 0 ≤ min (Δ k) ϑ := le_min (h.delta_pos' fun i hi => hk' i hi.le).le hϑ
    have hpos : 0 < (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k) := by
      refine lt_of_le_of_lt ?_ (hst.lt_taylorDecrement.trans_le hst.taylorDecrement_le)
      exact div_nonneg (mul_nonneg (mul_nonneg P.ς_pos.le (hε _ hst.order_mem))
        (pow_nonneg hδ _)) (Nat.cast_nonneg _)
    exact ⟨h.mem_of_feasible hx0 (k + 1) hk,
      ((h.accept k hk').le trqRatio_eq hpos).trans (ih fun i hi => hk' i hi.le).2⟩

/-- **Model fidelity** ((A.19) anchored at the iterate): for a TRq run with exact data on `X`,
under the anchored assumption on `A ⊇ {y ∈ X | f(y) ≤ f(x₀)}`, before termination
`|f(x_k + s_k) - T_{f,j_k}(x_k, s_k)| ≤ L_f ‖s_k‖^{j_k+1}/(j_k+1)!` with `L_f = finMax 1 L q`
(the iterate lies in `A`, the trial point in `X ⊆ C`). -/
theorem IsTRqRun.abs_sub_le_of_lipschitzDerivsAnchored {X C A : Set E}
    (h : IsTRqRun f (𝒥 f x) (𝒳 X x) P q ε ϑ x s Δ jk d) (hf : LipschitzDerivsAnchored f C A 1 q L)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) (hϑ : 0 ≤ ϑ) :
    ∀ k, (∀ i ≤ k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) →
      |f (x k + s k) - (f (x k) - (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k))| ≤
        finMax 1 L q / (jk k + 1)! * ‖s k‖ ^ (jk k + 1) := by
  intro k hk
  have hst := h.isTRqStep hk
  have hj := hst.order_mem
  obtain ⟨hxk, hfk⟩ := h.mem_sublevel hx0 hε hϑ k fun i hi => hk i hi.le
  rw [ftaylorSeries_taylorDecrement_eq, sub_sub_cancel, ← Real.norm_eq_abs]
  exact norm_sub_taylorPolynomial_le_of_lipschitzAnchored hf.convex
    (fun y hy => (hf.contDiffAt y hy).of_le (by exact_mod_cast (Finset.mem_Icc.1 hj).2))
    (((hf.lipschitzAnchored _ hj).mono_const (le_finMax hj)).lipschitzAt
      (hA _ hxk hfk)) (hXC hxk) (hXC hst.mem.2)

/-- **The trust-region radius stays bounded below** ([cartis2022evaluation], Lemma 12.2.3).
Let `X ⊆ C`, `C` open and convex, `x₀ = x 0 ∈ X`, and let the derivatives of orders `1, …, q` be
`L_j`-Lipschitz anchored at the points of a set `A` containing `{y ∈ X | f(y) ≤ f(x₀)}`. For
`0 < ϑ ≤ 1` and `ε_j ≥ 0`, at every iteration `k` before termination of a TRq run with exact data
on `X`, `Δ_k` and `Δ_{k+1}` are at least `min(γ₁ ϑ, κ_Δ min_{i ≤ k} φ̂_i)` (12.2.13), with
`κ_Δ = trqKappaDelta ∈ (0, 1)` ((12.2.14)). -/
theorem IsTRqRun.radius_ge_of_anchored {X C A : Set E}
    (h : IsTRqRun f (𝒥 f x) (𝒳 X x) P q ε ϑ x s Δ jk d) (hf : LipschitzDerivsAnchored f C A 1 q L)
    (hXC : X ⊆ C) (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) (hx0 : x 0 ∈ X) (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) {k : ℕ} (hk : ∀ i ≤ k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) :
    (0 < trqKappaDelta f P q L ϑ (x 0) ∧ trqKappaDelta f P q L ϑ (x 0) < 1) ∧
      min (P.γ₁ * ϑ) (trqKappaDelta f P q L ϑ (x 0) * prefixMin
        (fun i => trqGap (ftaylorSeries ℝ f (x i)) (jk i) (min (Δ i) ϑ) (d i (jk i))) k) ≤
        Δ k ∧
      min (P.γ₁ * ϑ) (trqKappaDelta f P q L ϑ (x 0) * prefixMin
        (fun i => trqGap (ftaylorSeries ℝ f (x i)) (jk i) (min (Δ i) ϑ) (d i (jk i))) k) ≤
        Δ (k + 1) := by
  have hL : 1 ≤ finMax 1 L q := one_le_finMax
  have hM := IsTRqRun.pos_of_not_trqTest_zero h hε hϑ.le
    (norm_ftaylorSeries_le_finMax (x 0)) (hk 0 (Nat.zero_le k))
  refine ⟨⟨trqKappa_pos (by linarith) hϑ hM, trqKappa_lt_one hL hϑ1⟩, ?_⟩
  exact IsTRqRun.radius_ge h hL hϑ hϑ1 hε
    (norm_ftaylorSeries_le_finMax (x 0))
    (h.abs_sub_le_of_lipschitzDerivsAnchored hf hXC hA hx0 hε hϑ.le) hk

/-- **Sufficient decrease** ([cartis2022evaluation], Lemmas 12.2.4 and 14.2.2).
Let `X ⊆ C`, `C` open and convex, `x₀ = x 0 ∈ X`, and let the derivatives of orders `1, …, q` be
`L_j`-Lipschitz anchored at the points of a set `A` containing `{y ∈ X | f(y) ≤ f(x₀)}`. For
`ε ∈ (0, 1]^q` and `ϑ ∈ [ε_min, 1]`, at every iteration `k` before termination of a TRq run with
exact data on `X`, `ΔT_{f,j_k}(x_k, s_k) ≥ (ς κ_Δ)^{q+1} ε_min^{q+1}/q!` (12.2.18), and a
successful iteration decreases `f` by `η₁` times this bound (12.2.19). -/
theorem IsTRqRun.taylorDecrement_ge_of_anchored {X C A : Set E}
    (h : IsTRqRun f (𝒥 f x) (𝒳 X x) P q ε ϑ x s Δ jk d)
    (hf : LipschitzDerivsAnchored f C A 1 q L) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) :
    (P.ς * trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! * finMin 1 ε q ^ (q + 1) ≤
        (ftaylorSeries ℝ f (x k)).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ trqRatio f (𝒥 f x) x s jk k →
        P.η₁ * ((P.ς * trqKappaDelta f P q L ϑ (x 0)) ^ (q + 1) / q ! *
          finMin 1 ε q ^ (q + 1)) ≤ f (x k) - f (x (k + 1))) :=
  IsTRqRun.taylorDecrement_ge h one_le_finMax hϑ1
    (finMin_pos one_pos fun j hj => (hε j hj).1) hϑ (fun _ hj => finMin_le hj)
      (norm_ftaylorSeries_le_finMax (x 0))
    (h.abs_sub_le_of_lipschitzDerivsAnchored hf hXC hA hx0 (fun j hj => (hε j hj).1.le)
      ((finMin_pos one_pos fun j hj => (hε j hj).1).le.trans hϑ)) hk

/-- **Evaluation complexity of TRq** ([cartis2022evaluation], Theorem 12.2.5; Theorem 14.2.4 for
TRq-SC). Let `X ⊆ C`, `C` open and convex, `x₀ = x 0 ∈ X`, and let the derivatives of orders
`1, …, q` be `L_j`-Lipschitz anchored at the points of a set `A` containing
`{y ∈ X | f(y) ≤ f(x₀)}`. Let `f ≥ f_low` on `X`, `ε ∈ (0, 1]^q` and `ϑ ∈ [ε_min, 1]`. Every TRq run
with exact data on `X` terminates at some `k_ε` with `x_{k_ε} ∈ X` and the certificate
`φ^{δ_ε}_{f,j}(x_{k_ε}) ≤ ε_j δ_ε^j/j!` over `{d | x_{k_ε} + d ∈ X}`, `δ_ε = min(Δ_{k_ε}, ϑ)`,
after at most `κ^A (f(x₀) - f_low)/ε_min^{q+1} + κ^B |log ε_min| + κ^C` evaluations of `f` and
`κ^S (f(x₀) - f_low)/ε_min^{q+1} + 1` evaluations of the derivatives. -/
theorem IsTRqRun.complexity {X C A : Set E} {flow : ℝ} (hb : ∀ y ∈ X, flow ≤ f y)
    (hf : LipschitzDerivsAnchored f C A 1 q L) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (h : IsTRqRun f (𝒥 f x) (𝒳 X x) P q ε ϑ x s Δ jk d) :
    ∃ kε, IsFirstHit (trqTest (𝒥 f x) P q ε ϑ Δ d) kε ∧ x kε ∈ X ∧
      min (Δ kε) ϑ ∈ Ioc 0 1 ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) {e | x kε + e ∈ X} q ε
        (fun _ => min (Δ kε) ϑ) ∧
      (funEvalCount kε : ℝ) ≤
        kappaATRq f P q L ϑ (x 0) * (f (x 0) - flow) / finMin 1 ε q ^ (q + 1) +
          kappaBTRq P * |Real.log (finMin 1 ε q)| + kappaCTRq f P q L ϑ (x 0) ∧
      (derivEvalCount (fun k => P.η₁ ≤ trqRatio f (𝒥 f x) x s jk k) kε : ℝ) ≤
        kappaSTRq f P q L ϑ (x 0) * (f (x 0) - flow) / finMin 1 ε q ^ (q + 1) + 1 := by
  set εm := finMin 1 ε q with hεm_def
  have hεm : 0 < εm := finMin_pos one_pos fun j hj => (hε j hj).1
  have hϑ0 : 0 < ϑ := hεm.trans_le hϑ
  have hfid := h.abs_sub_le_of_lipschitzDerivsAnchored hf hXC hA hx0 (fun j hj => (hε j hj).1.le)
    hϑ0.le
  set κ := trqKappaDelta f P q L ϑ (x 0) with hκ_def
  have hκ0 : 0 ≤ κ := trqKappaDelta_nonneg hϑ0.le _
  have hlog2 : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
  have hlog3 : 0 ≤ Real.log P.γ₃ := Real.log_nonneg P.one_le_γ₃
  set X := (f (x 0) - flow) / εm ^ (q + 1) with hX_def
  have hX : 0 ≤ X := div_nonneg (sub_nonneg.2 (hb _ hx0)) (by positivity)
  have hκS : 0 ≤ kappaSTRq f P q L ϑ (x 0) := by
    unfold kappaSTRq; have := P.η₁_pos; have := P.ς_pos; positivity
  set A := 1 + Real.log P.γ₃ / |Real.log P.γ₂| with hA_def
  have hA : 0 ≤ A := by positivity
  have hεle : ∀ j ∈ Finset.Icc 1 q, εm ≤ ε j := fun _ hj => finMin_le hj
  -- the counting statement
  have hmain : ∃ kε, IsFirstHit (trqTest (𝒥 f x) P q ε ϑ Δ d) kε ∧
      (funEvalCount kε : ℝ) ≤ A * (kappaSTRq f P q L ϑ (x 0) * X) +
        (|Real.log (P.ς * κ / P.Δ₀)| + |Real.log εm|) / |Real.log P.γ₂| + 1 ∧
      (derivEvalCount (fun k => P.η₁ ≤ trqRatio f (𝒥 f x) x s jk k) kε : ℝ) ≤
        kappaSTRq f P q L ϑ (x 0) * X + 1 := by
    by_cases h0 : trqTest (𝒥 f x) P q ε ϑ Δ d 0
    · refine ⟨0, ⟨h0, fun j hj => absurd hj (Nat.not_lt_zero _)⟩, ?_, ?_⟩
      · rw [funEvalCount_eq]; push_cast
        have : 0 ≤ A * (kappaSTRq f P q L ϑ (x 0) * X) := by positivity
        have : 0 ≤ (|Real.log (P.ς * κ / P.Δ₀)| + |Real.log εm|) / |Real.log P.γ₂| := by
          positivity
        linarith
      · rw [derivEvalCount_zero]; push_cast
        have : 0 ≤ kappaSTRq f P q L ϑ (x 0) * X := by positivity
        linarith
    have hM := IsTRqRun.pos_of_not_trqTest_zero h (fun j hj => (hε j hj).1.le) hϑ0.le
      (norm_ftaylorSeries_le_finMax (x 0)) h0
    have hκ : 0 < κ := trqKappa_pos (zero_lt_one.trans_le one_le_finMax) hϑ0 hM
    set c := P.η₁ * ((P.ς * κ) ^ (q + 1) / q ! * εm ^ (q + 1)) with hc_def
    have hc : 0 < c := by have := P.η₁_pos; have := P.ς_pos; positivity
    have hdec := fun k (hk : ∀ i ≤ k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) =>
      IsTRqRun.taylorDecrement_ge h one_le_finMax hϑ1 hεm hϑ hεle
        (norm_ftaylorSeries_le_finMax (x 0))
        hfid hk
    have hsucc : ∀ k, (∀ i ≤ k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) →
        ((successSet (fun k => P.η₁ ≤ trqRatio f (𝒥 f x) x s jk k) k).card : ℝ) ≤
          kappaSTRq f P q L ϑ (x 0) * X := by
      intro k hk
      have hcard := card_mul_le_of_decrease («φ» := fun j => f (x j)) (c := c) (k := k)
        (T := successSet (fun k => P.η₁ ≤ trqRatio f (𝒥 f x) x s jk k) k) successSet_subset_range
        (fun j hj => by
          have hj' : ∀ i ≤ j, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i := fun i hi => hk i (hi.trans hj)
          have hpos : 0 < (ftaylorSeries ℝ f (x j)).taylorDecrement (jk j) (s j) :=
            lt_of_lt_of_le (by have := P.ς_pos; positivity) (hdec j hj').1
          exact (h.accept j hj').le trqRatio_eq hpos)
        (fun j hj => by
          rw [mem_successSet] at hj
          exact (hdec j fun i hi => hk i (hi.trans hj.1)).2 hj.2)
        (hb _ (h.mem_of_feasible hx0 (k + 1) fun i hi => hk i (Nat.lt_succ_iff.1 hi)))
      have e : kappaSTRq f P q L ϑ (x 0) * X = (f (x 0) - flow) / c := by
        rw [hc_def, hX_def, kappaSTRq, ← hκ_def]
        have := P.η₁_pos; have := P.ς_pos
        field_simp
      rw [e, le_div_iff₀ hc]
      linarith
    have hcount : ∀ k, (∀ i ≤ k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) →
        (k + 1 : ℝ) ≤ A * (successSet (fun k => P.η₁ ≤ trqRatio f (𝒥 f x) x s jk k) k).card +
          (|Real.log (P.ς * κ / P.Δ₀)| + |Real.log εm|) / |Real.log P.γ₂| := by
      intro k hk
      have hΔ := IsTRqRun.mul_le_delta h one_le_finMax hϑ1 hεm hϑ hεle
        (norm_ftaylorSeries_le_finMax (x 0)) h0 hfid (k := k + 1)
        fun i hi => hk i (Nat.lt_succ_iff.1 hi)
      have hpos : 0 < P.ς * κ * εm := by have := P.ς_pos; positivity
      have hcnt := h.toIsTRRun.succ_count hk hpos hΔ
      have hlog : |Real.log (P.ς * κ * εm / P.Δ₀)| ≤
          |Real.log (P.ς * κ / P.Δ₀)| + |Real.log εm| := by
        have : P.ς * κ * εm / P.Δ₀ = P.ς * κ / P.Δ₀ * εm := by ring
        have hpos' : 0 < P.ς * κ / P.Δ₀ := by have := P.ς_pos; have := P.Δ₀_pos; positivity
        rw [this, Real.log_mul hpos'.ne' hεm.ne']
        exact abs_add_le _ _
      have := div_le_div_of_nonneg_right hlog hlog2.le
      have hAc : (successSet (fun k => P.η₁ ≤ trqRatio f (𝒥 f x) x s jk k) k).card *
          (1 + Real.log P.γ₃ / |Real.log P.γ₂|) =
          A * (successSet (fun k => P.η₁ ≤ trqRatio f (𝒥 f x) x s jk k) k).card := by
        rw [hA_def]; ring
      linarith
    exact exists_isFirstHit_evalCount_le_of_counting hA (by positivity) (by positivity) hcount
      hsucc
  obtain ⟨kε, hk, hF, hD⟩ := hmain
  have hkε : ∀ i < kε, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i := fun i hi => hk.2 i hi
  have hδ : min (Δ kε) ϑ ∈ Ioc 0 1 :=
    ⟨lt_min (h.delta_pos' hkε) hϑ0, (min_le_right _ _).trans hϑ1⟩
  refine ⟨kε, hk, h.mem_of_feasible hx0 kε hkε, hδ,
    MeasureTestPasses.isEpsDeltaApprox P.ς_pos (h.witness kε hkε) hk.1, hF.trans_eq ?_,
    hD.trans_eq ?_⟩
  · rw [kappaATRq, kappaBTRq, kappaCTRq, ← hκ_def, hX_def, hA_def]
    field_simp
    ring
  · rw [hX_def, mul_div_assoc]

/-- **The number of unsuccessful iterations** ([cartis2022evaluation], Lemma 14.2.3 for TRq,
Lemma 2.3.1 with the radius bound of Lemma 12.2.3): every iteration `k` reached (up to and including
termination) satisfies `k ≤ κ_uns |𝒮_k| + κ_unc` with `κ_uns = 1 + log γ₃/|log γ₂|` and
`κ_unc = |log(min(γ₁ ϑ, κ_Δ ς ε_min)/Δ₀)|/|log γ₂|`. -/
theorem IsTRqRun.le_succ_count_of_anchored {X C A : Set E}
    (h : IsTRqRun f (𝒥 f x) (𝒳 X x) P q ε ϑ x s Δ jk d)
    (hf : LipschitzDerivsAnchored f C A 1 q L) (hXC : X ⊆ C)
    (hA : ∀ y ∈ X, f y ≤ f (x 0) → y ∈ A) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    {k : ℕ} (hk : ∀ i < k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i) :
    (k : ℝ) ≤
      (successSet (fun j => P.η₁ ≤ trqRatio f (𝒥 f x) x s jk j) k).card *
          (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
        |Real.log (min (P.γ₁ * ϑ) (trqKappaDelta f P q L ϑ (x 0) *
          (P.ς * finMin 1 ε q)) / P.Δ₀)| / |Real.log P.γ₂| := by
  rcases k with _ | k
  · rw [Nat.cast_zero]
    have : 0 ≤ 1 + Real.log P.γ₃ / |Real.log P.γ₂| :=
      add_nonneg zero_le_one (div_nonneg (Real.log_nonneg P.one_le_γ₃) (abs_nonneg _))
    positivity
  have hk' : ∀ i ≤ k, ¬ trqTest (𝒥 f x) P q ε ϑ Δ d i := fun i hi =>
    hk i (Nat.lt_succ_of_le hi)
  have hεm : 0 < finMin 1 ε q := finMin_pos one_pos fun j hj => (hε j hj).1
  have hϑ0 : 0 < ϑ := hεm.trans_le hϑ
  obtain ⟨⟨hκ0, -⟩, -, hΔ⟩ := h.radius_ge_of_anchored hf hXC hA hx0 hϑ0 hϑ1
    (fun j hj => (hε j hj).1.le) hk'
  have hgap : P.ς * finMin 1 ε q ≤
      prefixMin ((fun i => trqGap (ftaylorSeries ℝ f (x i)) (jk i) (min (Δ i) ϑ) (d i (jk i)))) k :=
    (IsTRqRun.trqGap_ge h hϑ0 (fun _ hj => finMin_le hj) hk').1
  have hmin : 0 < min (P.γ₁ * ϑ) (trqKappaDelta f P q L ϑ (x 0) *
      (P.ς * finMin 1 ε q)) :=
    lt_min (mul_pos P.γ₁_pos hϑ0) (mul_pos hκ0 (mul_pos P.ς_pos hεm))
  exact h.toIsTRRun.le_succ_count hk hmin
    ((min_le_min le_rfl (mul_le_mul_of_nonneg_left hgap hκ0.le)).trans hΔ)

end Optimization
