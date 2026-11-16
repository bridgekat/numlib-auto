/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.SpecialFunctions.Log
import Numlib.Optimization.ModelBased.HighOrder.TRqComplexity

/-!
# TRq runs as inner solvers

A run of the trust-region method TRq ([cartis2022evaluation], Algorithm 12.2.1) with the exact
Taylor data of $f$ on a closed feasible set $X$ (TRq-SC of §14.2) serves as the inner solver INNER
of trust-region type of the two-phase method TPqp-GC (§14.3). Each call starts afresh from the
radius $\Delta_0$ at a point given by the outer method, and is cut either at its own termination or
earlier by a test of the outer method. This file collects what an outer analysis needs about one
call. The constants depend on $f$ only through the Lipschitz constants $L_j$ of its derivatives and
a bound $M$ on its derivatives of orders $1, \dots, q$ at the start of the call, so they are uniform
over all calls.

The main facts about a call are: unsuccessful iterations do not move; the radii stay above
$\kappa_\rho\varepsilon_{\min}$; every successful iteration decreases $f$ by at least
$\kappa_{\mathrm{decr}}\varepsilon_{\min}^{q+1}$; and the number of iterations is at most
$\kappa_{\mathrm{uns}}(|\mathcal{S}| + 1) +
|\log(\kappa_\rho\varepsilon_{\min}/\Delta_0)|/|\log\gamma_2|$, where $\mathcal{S}$ is the set of
successful iterations. Here $\varepsilon_{\min} = \min_j \varepsilon_j$.

## Main definitions

* `Optimization.trqCallKappaDelta`, `Optimization.trqCallKappaRad`, `Optimization.trqCallKappaDecr`,
  `Optimization.trqKappaUns`, `Optimization.trqCallKappaS`, `Optimization.trqCallKappaA`,
  `Optimization.trqCallKappaC`: the constants of Lemmas 12.2.3, 12.2.4 and 2.3.1 and of Theorem
  12.2.5, with the derivative bound $M$ in place of the derivatives at the start.
* `Optimization.IsTRqCallOut`: a call cut at any iteration up to its termination, with its iterates,
  its successful iterations and its returned radii $\min(\Delta_e, \vartheta)$.
* `Optimization.IsTRqOutputCost`: a terminating call with its evaluation counts.

## Main results

* `Optimization.trqCallKappaDelta_le_trqKappaDelta`, with the comparisons
  `Optimization.kappaSTRq_le_trqCallKappaS`, `Optimization.kappaATRq_le_trqCallKappaA` and
  `Optimization.kappaCTRq_le_trqCallKappaC`: the constants of a call bound the constants of Theorem
  12.2.5.
* `Optimization.IsTRqRun.trqCallKappaRad_mul_le`: the radii stay above
  $\kappa_\rho\varepsilon_{\min}$ up to termination (Lemma 12.2.3 with (12.2.9)).
* `Optimization.IsTRqCallOut.eq_of_not_succ`: unsuccessful iterations do not move.
* `Optimization.IsTRqCallOut.le_count`: the number of iterations of a call is at most
  $\kappa_{\mathrm{uns}}(|\mathcal{S}| + 1) +
|\log(\kappa_\rho\varepsilon_{\min}/\Delta_0)|/|\log\gamma_2|$ (Lemma 2.3.1).
* `Optimization.IsTRqCallOut.decrease`: every successful iteration decreases $f$ by at least
  $\kappa_{\mathrm{decr}}\varepsilon_{\min}^{q+1}$ (Lemma 12.2.4).
* `Optimization.IsTRqCallOut.radius_ge`: the returned radii are at least
  $\kappa_\rho\varepsilon_{\min}$.
* `Optimization.IsTRqOutputCost.cost_le`: the evaluation counts of a terminating call (Theorem
  12.2.5).
* `Optimization.exists_isTRqRun_feasible`: runs with a closed feasible set exist.
* `Optimization.exists_isTRqCallOut_of_stop`: calls stopped at the first iterate that satisfies an
  external test, or at termination, exist.

## Notation

* `𝒥 f x` (local): the exact Taylor data `fun k => ftaylorSeries ℝ f (x k)` of $f$ along the
  iterates.
* `𝒳 X x` (local): the feasible displacements $\{e : x_k + e \in X\}$ at the iterates, as a function
  of $k$.

## Implementation notes

* The constants of Theorem 12.2.5 (`Optimization.trqKappaDelta`, `Optimization.kappaSTRq`, …) depend
  on the starting point through $\max_i\|\nabla^i f(x_0)\|$. Their call counterparts take a bound
  $M$ instead. They are compared through the antitonicity of `Optimization.trqKappa` in $M$
  (`Optimization.trqKappa_anti`).
* Because every call restarts from the radius $\Delta_0$, the iteration count of a call carries the
  term $|\log(\kappa_\rho\varepsilon_{\min}/\Delta_0)|$, which an outer method multiplies by its
  number of calls.
* $\varepsilon_{\min}$ is `Optimization.finMin 1 ε q`
  $= \min(1, \min_{1 \le j \le q}\varepsilon_j)$, and $L_f = \max(1, \max_j L_j)$ is
  `Optimization.finMax 1 L q`. The derivative bound at a point $y$ is the hypothesis
  `Optimization.finMax 0 (fun i => ‖iteratedFDeriv ℝ i f y‖) q ≤ M`, that is, $\max(0, \max_{1 \le i
  \le q}\|\nabla^i f(y)\|) \le M$.
* The anchored assumption is `LipschitzDerivsAnchored f C A 1 q L`: $C$ is open and convex,
  $A \subseteq C$, $f$ is of class $C^q$ near every point of $C$, and $\|\nabla^j f(a) - \nabla^j
  f(y)\| \le L_j\|a - y\|$ for $a \in A$, $y \in C$ and $j = 1, \dots, q$.
-/

open Set
open scoped Nat

namespace Optimization

/-- The exact Taylor data of $f$ along the iterates: the jet `ftaylorSeries ℝ f (x k)` of $f$ at
$x_k$, for each $k$. -/
local notation "𝒥" f:max x:max => fun k : ℕ => ftaylorSeries ℝ f (x k)

/-- The feasible displacements at the iterates: the set $\{e : x_k + e \in X\}$, for each $k$. -/
local notation "𝒳" X:max x:max => fun k : ℕ => Set.ofPred fun e => x k + e ∈ X

/-- Let $\mathrm{succ}$ be a predicate on iterations and $e \in \mathbb{N}$. The success set
$\mathcal{S}_e = \{i \le e : \mathrm{succ}(i)\}$, which can include $e$ itself, has at most one
more element than the set of successful iterations before $e$:
$$|\mathcal{S}_e| \le |\{i < e : \mathrm{succ}(i)\}| + 1.$$
-/
theorem card_successSet_le_card_filter_add_one (succ : ℕ → Prop) [DecidablePred succ] (e : ℕ) :
    ((successSet succ e).card : ℝ) ≤ ((Finset.range e).filter succ).card + 1 := by
  rw [successSet_eq_filter, Finset.range_add_one, Finset.filter_insert]
  split_ifs
  · exact_mod_cast Finset.card_insert_le _ _
  · exact le_add_of_nonneg_right zero_le_one

/-! ### The constants of a call -/

section Constants

variable (P : TRqParams) (L : ℕ → ℝ) (ϑ M : ℝ) (q : ℕ)

/-- The constant
$$\kappa_\Delta(M) = \frac{\gamma_1(1 - \eta_2)}{L_f}\min\left(\vartheta,
  \frac{\Delta_0\delta_0^q}{2\,q!\,M}\right), \qquad \delta_0 = \min(\Delta_0, \vartheta),\
  L_f = \max(1, \max_{1 \le j \le q} L_j).$$
It is the constant $\kappa_\Delta$ of (12.2.14) of [cartis2022evaluation]
(`Optimization.trqKappaDelta`) with a bound $M$ on the derivatives of orders $1, \dots, q$ at
the starting point in place of their maximum norm. For such a bound it is a lower bound of
$\kappa_\Delta$ (`Optimization.trqCallKappaDelta_le_trqKappaDelta`). -/
noncomputable def trqCallKappaDelta : ℝ :=
  trqKappa P (finMax 1 L q) ϑ M q

/-- The radius constant $\kappa_\rho = \min(\gamma_1\vartheta, \varsigma\kappa_\Delta(M),
\Delta_0)$. The trust-region radii up to termination, and the optimality radii
$\min(\Delta_k, \vartheta)$, are at least $\kappa_\rho\varepsilon_{\min}$ (Lemma 12.2.3 of
[cartis2022evaluation] with (12.2.9); see `Optimization.IsTRqRun.trqCallKappaRad_mul_le`). -/
noncomputable def trqCallKappaRad : ℝ :=
  min (min (P.γ₁ * ϑ) (trqCallKappaDelta P L ϑ M q * P.ς)) P.Δ₀

/-- The decrease constant $\kappa_{\mathrm{decr}} = \eta_1(\varsigma\kappa_\Delta(M))^{q+1}/q!$ of
Lemma 12.2.4 of [cartis2022evaluation]. A successful iteration decreases the objective by at
least $\kappa_{\mathrm{decr}}\varepsilon_{\min}^{q+1}$ (`Optimization.IsTRqCallOut.decrease`). -/
noncomputable def trqCallKappaDecr : ℝ :=
  P.η₁ * ((P.ς * trqCallKappaDelta P L ϑ M q) ^ (q + 1) / q !)

/-- The constant $\kappa_{\mathrm{uns}} = 1 + \log\gamma_3/|\log\gamma_2|$ of Lemma 2.3.1 of
[cartis2022evaluation]. -/
noncomputable def trqKappaUns : ℝ :=
  1 + Real.log P.γ₃ / |Real.log P.γ₂|

/-- The constant $\kappa^S(M) = q!/(\eta_1(\varsigma\kappa_\Delta(M))^{q+1})$, which is $\kappa^S$
of Theorem 12.2.5 of [cartis2022evaluation] with $\kappa_\Delta(M)$ in place of $\kappa_\Delta$. -/
noncomputable def trqCallKappaS : ℝ :=
  q ! / (P.η₁ * (P.ς * trqCallKappaDelta P L ϑ M q) ^ (q + 1))

/-- The constant $\kappa^A(M) = \kappa^S(M)\,\kappa_{\mathrm{uns}}$, which is $\kappa^A$ of Theorem
12.2.5 of [cartis2022evaluation] with $\kappa_\Delta(M)$ in place of $\kappa_\Delta$. -/
noncomputable def trqCallKappaA : ℝ :=
  trqCallKappaS P L ϑ M q * trqKappaUns P

/-- The constant $\kappa^C(M) = (|\log\varsigma| + |\log\kappa_\Delta(M)| +
|\log\Delta_0|)/|\log\gamma_2| + 1$. It is an upper bound for the constant $\kappa^C =
|\log(\varsigma\kappa_\Delta/\Delta_0)|/|\log\gamma_2| + 1$ of Theorem 12.2.5 of
[cartis2022evaluation] (`Optimization.kappaCTRq_le_trqCallKappaC`). -/
noncomputable def trqCallKappaC : ℝ :=
  (|Real.log P.ς| + |Real.log (trqCallKappaDelta P L ϑ M q)| + |Real.log P.Δ₀|) /
    |Real.log P.γ₂| + 1

variable {P L ϑ M q}

/-- For $\vartheta > 0$ and $M > 0$, $\kappa_\Delta(M) > 0$. -/
theorem trqCallKappaDelta_pos (hϑ : 0 < ϑ) (hM : 0 < M) : 0 < trqCallKappaDelta P L ϑ M q :=
  trqKappa_pos (zero_lt_one.trans_le one_le_finMax) hϑ hM

/-- For $\vartheta \le 1$, $\kappa_\Delta(M) < 1$. -/
theorem trqCallKappaDelta_lt_one (hϑ1 : ϑ ≤ 1) : trqCallKappaDelta P L ϑ M q < 1 :=
  trqKappa_lt_one one_le_finMax hϑ1

/-- For $\vartheta > 0$ and $M > 0$, $\kappa_\rho > 0$. -/
theorem trqCallKappaRad_pos (hϑ : 0 < ϑ) (hM : 0 < M) : 0 < trqCallKappaRad P L ϑ M q :=
  lt_min (lt_min (mul_pos P.γ₁_pos hϑ) (mul_pos (trqCallKappaDelta_pos hϑ hM) P.ς_pos)) P.Δ₀_pos

/-- $\kappa_\rho \le \gamma_1\vartheta$. -/
theorem trqCallKappaRad_le_γ₁ : trqCallKappaRad P L ϑ M q ≤ P.γ₁ * ϑ :=
  (min_le_left _ _).trans (min_le_left _ _)

/-- For $\vartheta > 0$ and $M > 0$, $\kappa_{\mathrm{decr}} > 0$. -/
theorem trqCallKappaDecr_pos (hϑ : 0 < ϑ) (hM : 0 < M) : 0 < trqCallKappaDecr P L ϑ M q := by
  have := trqCallKappaDelta_pos (P := P) (L := L) (q := q) hϑ hM
  have := P.ς_pos
  have := P.η₁_pos
  unfold trqCallKappaDecr
  positivity

/-- $\kappa_{\mathrm{uns}} \ge 1$. -/
theorem one_le_trqKappaUns : 1 ≤ trqKappaUns P := by
  unfold trqKappaUns
  have : 0 ≤ Real.log P.γ₃ / |Real.log P.γ₂| :=
    div_nonneg (Real.log_nonneg P.one_le_γ₃) (abs_nonneg _)
  linarith

/-- For $\vartheta > 0$ and $M > 0$, $\kappa^S(M) \ge 0$. -/
theorem trqCallKappaS_nonneg (hϑ : 0 < ϑ) (hM : 0 < M) : 0 ≤ trqCallKappaS P L ϑ M q := by
  have := trqCallKappaDelta_pos (P := P) (L := L) (q := q) hϑ hM
  have := P.ς_pos
  have := P.η₁_pos
  unfold trqCallKappaS
  positivity

/-- For $\vartheta > 0$ and $M > 0$, $\kappa^A(M) \ge 0$. -/
theorem trqCallKappaA_nonneg (hϑ : 0 < ϑ) (hM : 0 < M) : 0 ≤ trqCallKappaA P L ϑ M q :=
  mul_nonneg (trqCallKappaS_nonneg hϑ hM) (zero_le_one.trans one_le_trqKappaUns)

/-- $\kappa^C(M) \ge 1$. -/
theorem one_le_trqCallKappaC : 1 ≤ trqCallKappaC P L ϑ M q := by
  unfold trqCallKappaC
  have : 0 ≤ (|Real.log P.ς| + |Real.log (trqCallKappaDelta P L ϑ M q)| + |Real.log P.Δ₀|) /
    |Real.log P.γ₂| := by positivity
  linarith

/-- The constant $\kappa_\Delta(M)$ is antitone in the derivative bound $M$. Let $L' > 0$,
$\vartheta \ge 0$ and $0 < M \le M'$. Then
$$\frac{\gamma_1(1 - \eta_2)}{L'}\min\left(\vartheta,
  \frac{\Delta_0\delta_0^q}{2\,q!\,M'}\right) \le \frac{\gamma_1(1 -
  \eta_2)}{L'}\min\left(\vartheta, \frac{\Delta_0\delta_0^q}{2\,q!\,M}\right),$$
with $\delta_0 = \min(\Delta_0, \vartheta)$; both sides are `Optimization.trqKappa`. -/
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

/-- **The constant $\kappa_\Delta$ of (12.2.14) is at least $\kappa_\Delta(M)$.** Let $y \in E$ with
$\kappa_\Delta > 0$ at $y$, let $\max(0, \max_{1 \le i \le q}\|\nabla^i f(y)\|) \le M$, and let
$\vartheta \ge 0$. Then $\kappa_\Delta(M)$ is at most the constant $\kappa_\Delta$ of (12.2.14)
of [cartis2022evaluation] at $y$.

The constant $\kappa_\Delta$ at $y$ is `Optimization.trqKappaDelta f P q L ϑ y`. It is positive
when a run from $y$ does not stop at once. -/
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

/-- Under the hypotheses of `Optimization.trqCallKappaDelta_le_trqKappaDelta`, with $\vartheta > 0$
and $M > 0$, the constant $\kappa^S_{\mathrm{TRq}}$ at $y$ is at most $\kappa^S(M)$. -/
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

/-- Under the hypotheses of `Optimization.trqCallKappaDelta_le_trqKappaDelta`, with $\vartheta > 0$
and $M > 0$, the constant $\kappa^A_{\mathrm{TRq}}$ at $y$ is at most $\kappa^A(M)$. -/
theorem kappaATRq_le_trqCallKappaA (hpos : 0 < trqKappaDelta f P q L ϑ y)
    (hM : finMax 0 (fun i => ‖iteratedFDeriv ℝ i f y‖) q ≤ M) (hϑ : 0 < ϑ) (hM0 : 0 < M) :
    kappaATRq f P q L ϑ y ≤ trqCallKappaA P L ϑ M q :=
  mul_le_mul_of_nonneg_right (kappaSTRq_le_trqCallKappaS hpos hM hϑ hM0)
    (zero_le_one.trans one_le_trqKappaUns)

/-- Under the hypotheses of `Optimization.trqCallKappaDelta_le_trqKappaDelta`, with
$0 < \vartheta \le 1$ and $M > 0$, the constant $\kappa^C_{\mathrm{TRq}}$ at $y$ is at most
$\kappa^C(M)$. -/
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

/-- **Runs of TRq with a feasible set exist.** Let $E$ be finite-dimensional, $X \subseteq E$
closed, $\vartheta \ge 0$ and $x_0 \in X$. Then for every $f$, every choice of the constants
$P$, every order $q$ and all tolerances $\varepsilon$, there is a run of TRq with exact data on
$X$ that starts at $x_0$. This is the well-posedness of Algorithm 12.2.1 of
[cartis2022evaluation] with the feasible displacements $\{d : x_k + d \in X\}$, as used in
§14.2.

The run is `Optimization.IsTRqRun f (𝒥 f x) (𝒳 X x) P q ε ϑ x s Δ jk d`. The proof specializes
`Optimization.exists_isTRqRun`. The iterates stay in $X$ up to termination
(`Optimization.IsTRqRun.mem_of_feasible`). -/
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

/-- Let a run of TRq have any data $D_k$ and any feasible sets $S_k$, with the objective $f$, and
let $\varepsilon_j \ge 0$ for $j \in [1, q]$ and $\vartheta \ge 0$. If the termination test
fails at all $i \le k$, then $f(x_{k+1}) \le f(x_k)$.

A step has a positive predicted decrease, so an accepted step does not increase $f$. -/
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

/-- **The radius bound of a call.** Let a run of TRq with exact data on $X$ start at $x_0 \in X$.
Let $f$ satisfy the anchored assumption `LipschitzDerivsAnchored f C A 1 q L` with
$X \subseteq C$ and $\{y \in X : f(y) \le f(x_0)\} \subseteq A$, let $\max(0, \max_{1 \le i \le
q}\|\nabla^i f(x_0)\|) \le M$, $\varepsilon_j > 0$ for $j \in [1, q]$, and
$0 < \vartheta \le 1$. If the termination test fails at all $i < e$, then
$$\Delta_e \ge \kappa_\rho\varepsilon_{\min}.$$
So the bound holds up to and including termination. This is Lemma 12.2.3 of
[cartis2022evaluation] with (12.2.9) and $\kappa_\Delta \ge \kappa_\Delta(M)$. -/
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

/-- A **call of TRq with a feasible set**, cut at iteration $e$, with iterates
$\xi_0, \dots, \xi_e$, a predicate $\mathrm{succ}$ on iterations and returned radii
$\delta^{\mathrm{o}}$. There is a run of TRq with exact data on $f$, feasible displacements
$\{d : x_i + d \in X\}$, tolerances $\varepsilon$ and threshold $\vartheta$, such that:
* the run terminates, and its first termination index $k_\varepsilon$ satisfies
  $e \le k_\varepsilon$;
* $\xi_i = x_i$ for $i \le e$;
* for $i < e$, $\mathrm{succ}(i)$ holds exactly when iteration $i$ of the run is successful,
  $\rho_i \ge \eta_1$;
* the returned radii are the optimality radii $\delta^{\mathrm{o}}_j = \min(\Delta_e,
  \vartheta)$ at the last iterate, for $j \in [1, q]$.

This is Algorithm 12.2.1 of [cartis2022evaluation] used as INNER, for example in Algorithm
14.3.2. The call may be cut before termination. At termination the returned radii certify
$(\varepsilon, \delta)$-approximate optimality (`Optimization.IsTRqRun.complexity`). -/
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

/-- In a call cut at iteration $e$, an iteration $i < e$ that is not successful does not move:
$\xi_{i+1} = \xi_i$. -/
theorem eq_of_not_succ (h : IsTRqCallOut f X P q ε ϑ xi e succ δo) :
    ∀ i < e, ¬ succ i → xi (i + 1) = xi i := by
  obtain ⟨x, s, Δ, jk, d, kε, hr, hhit, he, hxi, hsucc, -⟩ := h
  intro i hi hs
  rw [hxi i hi.le, hxi (i + 1) hi]
  exact hr.toIsTRRun.eq_of_not_succ (fun l hl => hhit.2 l (by omega))
    (not_le.1 ((hsucc i hi).not.1 hs))

variable {C A : Set E}

/-- **The radius bound of a call.** Let a call with iterates $\xi_i$ be cut at iteration $e$, with
$\xi_0 \in X$. Let $f$ satisfy the anchored assumption `LipschitzDerivsAnchored f C A 1 q L`
with $X \subseteq C$ and $\{y \in X : f(y) \le f(\xi_0)\} \subseteq A$, let $\max(0, \max_{1 \le
i \le q}\|\nabla^i f(\xi_0)\|) \le M$, $\varepsilon_j \in (0, 1]$ for $j \in [1, q]$, and
$\varepsilon_{\min} \le \vartheta \le 1$. Then the returned radii satisfy
$$\delta^{\mathrm{o}}_j \ge \kappa_\rho\varepsilon_{\min} \quad \text{for } j \in [1, q].$$

The proof uses $\Delta_e \ge \kappa_\rho\varepsilon_{\min}$
(`Optimization.IsTRqRun.trqCallKappaRad_mul_le`) and $\kappa_\rho\varepsilon_{\min} \le
\gamma_1\vartheta \le \vartheta$. -/
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
/-- **The number of iterations of a call.** Under the hypotheses of
`Optimization.IsTRqCallOut.radius_ge`, and with $M > 0$,
$$e \le \kappa_{\mathrm{uns}}|\mathcal{S}| + \kappa_{\mathrm{uns}} +
  \frac{|\log(\kappa_\rho\varepsilon_{\min}/\Delta_0)|}{|\log\gamma_2|},$$
where $\mathcal{S} = \{i < e : \mathrm{succ}(i)\}$ is the set of successful iterations of the
call. This is Lemma 2.3.1 of [cartis2022evaluation] with the radius bound of Lemma 12.2.3. -/
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

/-- **The decrease of a call.** Under the hypotheses of `Optimization.IsTRqCallOut.radius_ge`, and
with $M > 0$, every successful iteration $i < e$ decreases $f$ by at least
$$f(\xi_i) - f(\xi_{i+1}) \ge \kappa_{\mathrm{decr}}\varepsilon_{\min}^{q+1}.$$
This is Lemma 12.2.4 of [cartis2022evaluation] with $\kappa_\Delta \ge \kappa_\Delta(M)$, the
TRq-SC row of Lemma 14.2.2. -/
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
/-- **Calls stopped by an external test exist.** Let $E$ be finite-dimensional, $X \subseteq E$
closed, $f \ge f_{\mathrm{low}}$ on $X$, and $x_0 \in X$. Let $f$ satisfy the anchored
assumption `LipschitzDerivsAnchored f C A 1 q L` with $X \subseteq C$ and
$\{y \in X : f(y) \le f(x_0)\} \subseteq A$. Let $\varepsilon_j \in (0, 1]$ for $j \in [1, q]$,
$\varepsilon_{\min} \le \vartheta \le 1$, let $P$ be the constants of TRq and let
$\mathrm{stop}$ be a test on points. Then there is a call from $x_0$, cut at some iteration $e$,
with iterates $\xi_i$, a predicate $\mathrm{succ}$ and a common returned radius
$\delta \in (0, 1]$, such that:
* $\xi_e \in X$, $f(\xi_{i+1}) \le f(\xi_i)$ for $i < e$, and $f(\xi_e) \le f(x_0)$;
* $\mathrm{stop}(\xi_i)$ fails for $i < e$;
* either $\mathrm{stop}(\xi_e)$ holds, or $\xi_e$ is an $(\varepsilon, \delta)$-approximate
  minimizer of order $q$ on $X$: $\phi^{\delta}_{f,j}(\xi_e) \le \varepsilon_j\delta^j/j!$ for
  $1 \le j \le q$, over the feasible displacements $\{d : \xi_e + d \in X\}$.

The call is cut at the first iterate that satisfies $\mathrm{stop}$, or at the termination of
the run, whichever comes first; the run terminates by `Optimization.IsTRqRun.complexity`. The
certificate is `Optimization.IsEpsDeltaApprox`. -/
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

/-- The pair $(y, \delta)$ is the **output of a terminating call** of TRq with a feasible set from
$x^S$ that uses $n_F$ evaluations of $f$ and $n_D$ evaluations of its derivatives. That is,
there is a run of TRq with exact data on $X$ from $x_0 = x^S$ that terminates first at
$k_\varepsilon$, with $x_{k_\varepsilon} = y$, returned radii $\delta_j =
\min(\Delta_{k_\varepsilon}, \vartheta)$ for $j \in [1, q]$, $n_F = k_\varepsilon + 1$, and
$n_D$ equal to the number of successful iterations before $k_\varepsilon$ plus one.

The counts are `Optimization.funEvalCount` and `Optimization.derivEvalCount`. -/
def IsTRqOutputCost (f : E → ℝ) (X : Set E) (P : TRqParams) (q : ℕ) (ε : ℕ → ℝ) (ϑ : ℝ)
    (xS y : E) (δ : ℕ → ℝ) (nF nD : ℕ) : Prop :=
  ∃ (x s : ℕ → E) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → E) (kε : ℕ),
    IsTRqRun f (𝒥 f x) (𝒳 X x) P q ε ϑ x s Δ jk d ∧
    IsFirstHit (trqTest (𝒥 f x) P q ε ϑ Δ d) kε ∧
    x 0 = xS ∧ x kε = y ∧ (∀ j ∈ Finset.Icc 1 q, δ j = min (Δ kε) ϑ) ∧
    nF = funEvalCount kε ∧
    nD = derivEvalCount (fun k => P.η₁ ≤ trqRatio f (𝒥 f x) x s jk k) kε

/-- **The cost of a terminating call.** Let $(y, \delta)$ be the output of a terminating call from
$x^S \in X$ with $n_F$ evaluations of $f$ and $n_D$ evaluations of the derivatives. Let
$f \ge f_{\mathrm{low}}$ on $X$, let $f$ satisfy the anchored assumption
`LipschitzDerivsAnchored f C A 1 q L` with $X \subseteq C$ and
$\{z \in X : f(z) \le f(x^S)\} \subseteq A$, let $\max(0, \max_{1 \le i \le q}\|\nabla^i
f(x^S)\|) \le M$ with $M > 0$, $\varepsilon_j \in (0, 1]$ for $j \in [1, q]$, and
$\varepsilon_{\min} \le \vartheta \le 1$. Then
$$n_F \le \kappa^A(M)\frac{f(x^S) - f_{\mathrm{low}}}{\varepsilon_{\min}^{q+1}} +
\kappa^B_{\mathrm{TRq}}|\log\varepsilon_{\min}| + \kappa^C(M), \qquad n_D \le
\kappa^S(M)\frac{f(x^S) - f_{\mathrm{low}}}{\varepsilon_{\min}^{q+1}} + 1.$$
This is Theorem 12.2.5 of [cartis2022evaluation] with a feasible set, the TRq-SC row of Theorem
14.2.4, with $\kappa_\Delta \ge \kappa_\Delta(M)$. -/
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
