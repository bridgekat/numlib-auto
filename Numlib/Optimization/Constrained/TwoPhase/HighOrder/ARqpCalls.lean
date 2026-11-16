/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.Constrained.TwoPhase.HighOrder.Complexity
import Numlib.Optimization.ModelBased.HighOrder.ARqpCCall

/-!
# Runs of Phase 2 with adaptive-regularization inner calls

This file realizes the inner method of Phase 2 of a high-order target-following method (Algorithm
14.3.2 of [cartis2022evaluation]) by the adaptive-regularization method ARqp, run as ARqpC with
$c = 0$ and $h = 0$. Every inner call $\mathrm{INNER}(\mu(\cdot, t_k), X, q, x_k, \beta \|r(x_k,
t_k)\| \varepsilon)$ is a prefix of such a run on the merit function $\mu(\cdot, t_k)$, cut at any
iteration, together with its output radii (`Optimization.IsARqpCallOut`). For every run of Phase 2
of this kind, the calls satisfy the contract keyed on the inner test
(`Constrained.HighOrderTargetSeq.IsInnerTestContract`) with constants independent of the targets.
Calls with the required properties exist from every admissible point, so such runs exist by
`Constrained.HighOrderTargetSeq.exists_run_of_oracle`. The same holds on the whole space for the
ARqp runs with unit radii (`Optimization.IsARqpUnitCallOut`).

Below, $\mathcal{L}(t) = \{y \in X \mid \|r(y, t)\| \le 1\}$ is the sublevel set
`Constrained.targetSublevel`, and $\theta_P$ and $\varsigma_P$ are the parameters
`Optimization.ARqpParams.θ` and `Optimization.ARqpParams.ς` of ARqp.

## Main definitions

* `Constrained.HighOrderTargetSeq.IsARqpCalls`: the inner calls are ARqp calls with their output
  radii.
* `Constrained.HighOrderTargetSeq.IsARqpUnitCalls`: the inner calls are ARqp calls with unit radii.

## Main results

* `Constrained.IsHighOrderTargetRun.isInnerTestContract_of_isARqpCalls` (exponents $\pi_l = l + 1$),
  `Constrained.IsHighOrderTargetRun.isInnerTestContract_of_isARqpCalls_arqpPiOf` (exponents given by
  `Optimization.arqpPiOf`),
  `Constrained.IsHighOrderTargetRun.isInnerTestContract_of_isARqpUnitCalls`: the contracts.
* `Constrained.exists_arqpCall`, `Constrained.exists_arqpUnitCall`: one inner call from every
  admissible point.
-/

open Set
open scoped Nat

namespace Constrained

variable {E F G : Type*} [NormedAddCommGroup F]

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace HighOrderTargetSeq

variable (G) in
/-- **The inner calls of Phase 2 are ARqp calls.** For every outer iteration $k \ge 1$ that is
reached, the iterates, the successful iterations and the output radii $\delta_{k+1}$ of the
$k$-th call are those of an ARqp run on $\mu(\cdot, t_k)$ with the tolerances
$\beta \|r(x_k, t_k)\| \varepsilon_j$, cut at any iteration (`Optimization.IsARqpCallOut`).

The ARqp run is an ARqpC run with the constraint $c = 0 : E \to G$ and $h = 0$. -/
def IsARqpCalls (D : HighOrderTargetSeq E) (f : E → ℝ) (c : E → F) (X : Set E) (p q : ℕ)
    (P : Optimization.ARqpParams) (θ β : ℝ) (ε : ℕ → ℝ) : Prop :=
  ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
    Optimization.IsARqpCallOut G (targetMerit f c (D.t k)) X p q P
      (fun j => β * targetResidual f c (D.t k) (D.x k) * ε j) (D.xi k) (D.e k) (D.succ k)
      (D.δ (k + 1))

/-- **The inner calls of Phase 2 on the whole space are ARqp calls with unit radii.** For every
outer iteration $k \ge 1$ that is reached, the $k$-th call is an
`Optimization.IsARqpUnitCallOut` on $\mu(\cdot, t_k)$ with the tolerances
$\beta \|r(x_k, t_k)\| \varepsilon_j$, cut at any iteration. -/
def IsARqpUnitCalls (D : HighOrderTargetSeq E) (f : E → ℝ) (c : E → F) (p q : ℕ)
    (P : Optimization.ARqpParams) (θ β : ℝ) (ε : ℕ → ℝ) : Prop :=
  ∀ k, 1 ≤ k → D.Before f c univ q θ ε k →
    Optimization.IsARqpUnitCallOut (targetMerit f c (D.t k)) p q P
      (fun j => β * targetResidual f c (D.t k) (D.x k) * ε j) (D.xi k) (D.e k) (D.succ k)
      (D.δ (k + 1))

end HighOrderTargetSeq

namespace IsHighOrderTargetRun

variable {f : E → ℝ} {c : E → F} {X : Set E} {p q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : E}
  {D : HighOrderTargetSeq E}

/-- In a run of Phase 2, let $k \ge 1$ be an outer iteration that is reached. Then every $y \in X$
with $\mu(y, t_k) \le \mu(x_{k,0}, t_k)$ lies in the sublevel set $\mathcal{L}(t_k)$
(`Constrained.targetSublevel`), that is, $\|r(y, t_k)\| \le 1$.

The reason is $\|r(x_k, t_k)\| \le \varepsilon_0 \le 1$. -/
theorem call_sublevel (h : IsHighOrderTargetRun f c X q θ β ε x₁ D) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) :
    ∀ y ∈ X, targetMerit f c (D.t k) y ≤ targetMerit f c (D.t k) (D.xi k 0) →
      y ∈ targetSublevel f c X (D.t k) := by
  intro y hy hyk
  rw [h.inner_zero k hk1 hk] at hyk
  exact ⟨hy, (targetMerit_le_targetMerit_iff.1 hyk).trans
    (((h.isTargetSequence hk).residual_le h.θ_lt_one.le h.ε₀_pos.le hk1 le_rfl).trans
      (h.ε_le_one 0 (by simp)))⟩

/-- In a run of Phase 2, let $k \ge 1$ be an outer iteration in $\mathcal{K}_b$ that is reached, let
$\kappa \ge 0$, and let $j \in \{1, \dots, q\}$. Then $\kappa \beta \theta \varepsilon_0
\varepsilon_j \le \kappa \beta \|r(x_k, t_k)\| \varepsilon_j$. -/
theorem mul_tol_le_of_isKb (h : IsHighOrderTargetRun f c X q θ β ε x₁ D) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : D.Before f c X q θ ε k) (hb : D.IsKb f c θ ε k) {κ : ℝ} (hκ : 0 ≤ κ) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 q) :
    κ * β * θ * ε 0 * ε j ≤ κ * (β * targetResidual f c (D.t k) (D.x k) * ε j) := by
  have hrk : θ * ε 0 ≤ targetResidual f c (D.t k) (D.x k) :=
    hb.1.trans (h.residual_succ_le hk1 hk)
  have := h.β_pos
  have := h.ε_pos' hj
  calc κ * β * θ * ε 0 * ε j = κ * (β * (θ * ε 0) * ε j) := by ring
    _ ≤ _ := by gcongr

variable {P : Optimization.ARqpParams} {X₀ : Set E} {L : ℕ → ℝ}

/-- **Runs with ARqp calls satisfy the contract keyed on the inner test**, with the exponents
$\pi_l = l + 1$. Let $D$ be a run of Phase 2 whose inner calls are ARqp calls
(`Constrained.HighOrderTargetSeq.IsARqpCalls`). Let $X_0 \supseteq X$, and suppose that for
every target $t$:

* $\mu(\cdot, t)$ satisfies the anchored Lipschitz condition of order $p$
  (`LipschitzDerivsAnchored`) on the open convex set $X_0$, anchored in $\mathcal{L}(t)$, with
  constants $L$ and $L_p \ge 1$;
* $\|\nabla^i \mu(y, t)\| \le \max(1, \max_{1 \le j \le p} L_j)$ for $i = 2, \dots, p$ and every
  $y \in \mathcal{L}(t)$.

Suppose also that the ARqp parameters satisfy $\theta_P < \varsigma_P$. Then the calls satisfy
`Constrained.HighOrderTargetSeq.IsInnerTestContract` with target-independent constants: the
decrease constant $\kappa_{\mathrm{decr}}$ given by `Optimization.arqpCallKappaDecr`, the count
constants $\kappa_{\mathrm{uns}}$ given by `Optimization.arqpKappaUns` and
$\kappa_{\mathrm{unc}}$ given by `Optimization.arqpCallKappaUnc`, and the radii $\rho_j =
\kappa_\rho \beta\theta\varepsilon_0\varepsilon_j$ with $\kappa_\rho$ given by
`Optimization.arqpCallKappaRad`.

This follows Lemmas 14.2.2 and 14.2.3 of [cartis2022evaluation]. The proof applies
`Optimization.IsARqpCallOut.contract` to every call, so the calls may be cut by any test. -/
theorem isInnerTestContract_of_isARqpCalls (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hcalls : D.IsARqpCalls G f c X p q P θ β ε)
    (hf : ∀ t, LipschitzDerivsAnchored (targetMerit f c t) X₀ (targetSublevel f c X t) p p L)
    (hL : 1 ≤ L p)
    (hjet : ∀ t, ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ targetSublevel f c X t,
      ‖iteratedFDeriv ℝ i (targetMerit f c t) y‖ ≤ Optimization.finMax 1 L p)
    (hXX₀ : X ⊆ X₀) (hθς : P.θ < P.ς) :
    D.IsInnerTestContract f c X q θ β ε (Optimization.arqpCallKappaDecr P L p q)
      (Optimization.arqpKappaUns P) (Optimization.arqpCallKappaUnc P L p) (fun l => (l : ℝ) + 1)
      (fun j => Optimization.arqpCallKappaRad P L p * β * θ * ε 0 * ε j) := by
  have hC := fun k (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) =>
    (hcalls k hk1 hk).contract (hf (D.t k)) hL (hjet (D.t k)) hXX₀ (h.call_sublevel hk1 hk) hθς
  refine ⟨⟨fun k hk1 hk => (hC k hk1 hk).2.1, fun k hk1 hk => (hC k hk1 hk).1,
    fun k hk1 hk i hi hs hcont _ => ?_⟩, fun k hk1 hk hb _ j hj => ?_⟩
  · have hcont' : i + 1 < D.e k ∨ ¬ Optimization.IsEpsDeltaApprox
        (ftaylorSeries ℝ (targetMerit f c (D.t k)) (D.xi k (D.e k)))
        {d | D.xi k (D.e k) + d ∈ X} q
        (fun j => β * targetResidual f c (D.t k) (D.x k) * ε j) (D.δ (k + 1)) := by
      rw [h.inner_end k hk1 hk]
      exact hcont
    obtain ⟨l, hl, hdec⟩ := (hC k hk1 hk).2.2.1 i hi hs hcont'
    refine ⟨l, hl, ?_⟩
    have e : ((l : ℝ) + 1) = ((l + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e, Real.rpow_natCast]
    exact hdec
  · exact (h.mul_tol_le_of_isKb hk1 hk hb
      (Optimization.arqpCallKappaRad_pos (P := P) (L := L) (p := p)).le hj).trans
      ((hC k hk1 hk).2.2.2.2 j hj)

/-- **Runs with ARqp calls satisfy the contract keyed on the inner test, with the exponents of a
radii mode.** Under the assumptions of
`Constrained.IsHighOrderTargetRun.isInnerTestContract_of_isARqpCalls`, let $u$ be a radii mode
such that $u$ implies $q = 1$ and the convexity of $X$. Then the calls satisfy
`Constrained.HighOrderTargetSeq.IsInnerTestContract` with the same constants
$\kappa_{\mathrm{uns}}$ and $\kappa_{\mathrm{unc}}$ and the same radii, the decrease constant
$\kappa_{\mathrm{decr}} = \eta_1 \kappa_{\Delta m}$ (`Optimization.arqpKappaDmOf`), and the
exponents (`Optimization.arqpPiOf`) $\pi_l = (p + 1)/(p - l + 1)$ if $u$ holds and
$\pi_l = l(p + 1)/p$ otherwise.

This follows Lemmas 14.2.2 and 14.2.3 of [cartis2022evaluation], row ARqp-SC. -/
theorem isInnerTestContract_of_isARqpCalls_arqpPiOf (h : IsHighOrderTargetRun f c X q θ β ε x₁ D)
    (hcalls : D.IsARqpCalls G f c X p q P θ β ε)
    (hf : ∀ t, LipschitzDerivsAnchored (targetMerit f c t) X₀ (targetSublevel f c X t) p p L)
    (hL : 1 ≤ L p)
    (hjet : ∀ t, ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ targetSublevel f c X t,
      ‖iteratedFDeriv ℝ i (targetMerit f c t) y‖ ≤ Optimization.finMax 1 L p)
    (hXX₀ : X ⊆ X₀) (hθς : P.θ < P.ς) {u : Prop} [Decidable u] (hu : u → q = 1 ∧ Convex ℝ X) :
    D.IsInnerTestContract f c X q θ β ε (P.η₁ * Optimization.arqpKappaDmOf u P L p q)
      (Optimization.arqpKappaUns P) (Optimization.arqpCallKappaUnc P L p)
      (Optimization.arqpPiOf u p)
      (fun j => Optimization.arqpCallKappaRad P L p * β * θ * ε 0 * ε j) := by
  have hC := fun k (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) =>
    (hcalls k hk1 hk).contract (hf (D.t k)) hL (hjet (D.t k)) hXX₀ (h.call_sublevel hk1 hk) hθς
  refine ⟨⟨fun k hk1 hk => (hC k hk1 hk).2.1, fun k hk1 hk => (hC k hk1 hk).1,
    fun k hk1 hk i hi hs hcont _ => ?_⟩, fun k hk1 hk hb _ j hj => ?_⟩
  · have hcont' : i + 1 < D.e k ∨ ¬ Optimization.IsEpsDeltaApprox
        (ftaylorSeries ℝ (targetMerit f c (D.t k)) (D.xi k (D.e k)))
        {d | D.xi k (D.e k) + d ∈ X} q
        (fun j => β * targetResidual f c (D.t k) (D.x k) * ε j) (D.δ (k + 1)) := by
      rw [h.inner_end k hk1 hk]
      exact hcont
    exact (hC k hk1 hk).2.2.2.1 u hu i hi hs hcont'
  · exact (h.mul_tol_le_of_isKb hk1 hk hb
      (Optimization.arqpCallKappaRad_pos (P := P) (L := L) (p := p)).le hj).trans
      ((hC k hk1 hk).2.2.2.2 j hj)

/-- **Runs on the whole space with unit-radius ARqp calls satisfy the contract keyed on the inner
test.** Let $D$ be a run of Phase 2 with $X = E$ whose inner calls are ARqp calls with unit
radii (`Constrained.HighOrderTargetSeq.IsARqpUnitCalls`). Suppose that for every target $t$ the
merit function $\mu(\cdot, t)$ satisfies the anchored Lipschitz condition of order $p$ on $E$,
anchored in $\mathcal{L}(t)$, with constants $L$ and $L_p \ge 1$. Suppose also that the ARqp
parameters satisfy $\theta_P < \varsigma_P$, and that $1 \le q \le p$. Then the calls satisfy
`Constrained.HighOrderTargetSeq.IsInnerTestContract` with the exponents
$\pi_l = (p + 1)/(p - l + 1)$ (`Optimization.arqpPiOf` in the mode of unit radii), the
target-independent constants $\kappa_{\mathrm{decr}} = \eta_1 \kappa_{\Delta m}$
(`Optimization.arqpKappaDmOf` in the mode of unit radii), $\kappa_{\mathrm{uns}}$ given by
`Optimization.arqpKappaUns` and $\kappa_{\mathrm{unc}}$ given by
`Optimization.arqpCallKappaUnc`, and the radii $\rho_j = 1$.

This follows Lemmas 12.2.13 and 14.2.3 of [cartis2022evaluation] with unit radii. -/
theorem isInnerTestContract_of_isARqpUnitCalls (h : IsHighOrderTargetRun f c univ q θ β ε x₁ D)
    (hcalls : D.IsARqpUnitCalls f c p q P θ β ε)
    (hf : ∀ t, LipschitzDerivsAnchored (targetMerit f c t) univ (targetSublevel f c univ t) p p L)
    (hL : 1 ≤ L p) (hθς : P.θ < P.ς) (hq : 1 ≤ q) (hqp : q ≤ p) :
    D.IsInnerTestContract f c univ q θ β ε (P.η₁ * Optimization.arqpKappaDmOf True P L p q)
      (Optimization.arqpKappaUns P) (Optimization.arqpCallKappaUnc P L p)
      (Optimization.arqpPiOf True p) (fun _ => 1) := by
  have hC := fun k (hk1 : 1 ≤ k) (hk : D.Before f c univ q θ ε k) =>
    (hcalls k hk1 hk).contract (hf (D.t k)) hL
      (fun y hy => h.call_sublevel hk1 hk y (mem_univ y) hy) hθς hq hqp
  refine ⟨⟨fun k hk1 hk => (hC k hk1 hk).2.1, fun k hk1 hk => (hC k hk1 hk).1,
    fun k hk1 hk i hi hs hcont _ => ?_⟩, fun k hk1 hk _ _ j hj => ((hcalls k hk1 hk).2 j hj).ge⟩
  have hcont' : i + 1 < D.e k ∨ ¬ Optimization.IsEpsDeltaApprox
      (ftaylorSeries ℝ (targetMerit f c (D.t k)) (D.xi k (D.e k)))
      {d | D.xi k (D.e k) + d ∈ (univ : Set E)} q
      (fun j => β * targetResidual f c (D.t k) (D.x k) * ε j) (D.δ (k + 1)) := by
    rw [h.inner_end k hk1 hk]
    exact hcont
  have hrk : θ * ε 0 ≤ targetResidual f c (D.t k) (D.x k) := by
    have := h.inner_residual_ge k hk1 hk 0 (by omega)
    rwa [h.inner_zero k hk1 hk] at this
  have hε' : ∀ j ∈ Finset.Icc 1 q,
      β * targetResidual f c (D.t k) (D.x k) * ε j ∈ Ioc 0 1 := fun j hj => by
    have hrk1 : targetResidual f c (D.t k) (D.x k) ≤ 1 :=
      ((h.isTargetSequence hk).residual_le h.θ_lt_one.le h.ε₀_pos.le hk1 le_rfl).trans
        (h.ε_le_one 0 (by simp))
    have hεj := h.ε_pos' hj
    have hεj1 := h.ε_le_one j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
    have hβ1 : β ≤ 1 := h.β_le_θ.trans h.θ_lt_one.le
    have hr0 : 0 < targetResidual f c (D.t k) (D.x k) :=
      lt_of_lt_of_le (mul_pos h.θ_pos h.ε₀_pos) hrk
    refine ⟨by have := h.β_pos; positivity, ?_⟩
    calc β * targetResidual f c (D.t k) (D.x k) * ε j ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  exact (hC k hk1 hk).2.2 hε' i hi hs hcont'

end IsHighOrderTargetRun

/-! ### Existence of calls -/

section Existence

variable [FiniteDimensional ℝ E] {f : E → ℝ} {c : E → F} {X : Set E} {p q : ℕ} {ε : ℕ → ℝ}
  {θ β : ℝ} {t : ℝ} {L : ℕ → ℝ} {X₀ : Set E}

variable (G) in
open Classical in
/-- **One ARqp inner call with its output radii exists.** Let $E$ be finite-dimensional, let $X$ be
closed with $X \subseteq X_0$, and fix a target $t$. Suppose that $\mu(\cdot, t)$ satisfies the
anchored Lipschitz condition of order $p$ on $X_0$, anchored in $\mathcal{L}(t)$, with constants
$L$ and $L_p \ge 1$, and that $\|\nabla^i \mu(y, t)\| \le \max(1, \max_{1 \le j \le p} L_j)$ for
$i = 2, \dots, p$ and every $y \in \mathcal{L}(t)$. Let the ARqp parameters satisfy
$\sigma_{\min} > 0$ and $\theta_P < \varsigma_P$, let $1 \le q \le p$, $\theta > 0$,
$0 < \beta \le \theta$ and $\varepsilon_j \in (0, 1]$ for $j = 0, \dots, q$. Then for every
$x \in X$ with $\theta\varepsilon_0 \le \|r(x, t)\| \le \varepsilon_0$ there is a call $o$ with
$e$ iterations such that:

* $o_0 = x$, $o_e \in X$, and the radii satisfy $\delta_j \in (0, 1]$ for $j = 1, \dots, q$;
* $\|r(o_e, t)\| < \theta\varepsilon_0$, or the criticality test (14.3.34) holds at $(o_e, t)$
  with the radii $\delta$; these are the first and the third test of (14.3.32);
* $\mu(\cdot, t)$ does not increase along the call, and $\|r(o_i, t)\| \ge \theta\varepsilon_0$
  for every $i < e$;
* $\|r(o_e, t)\| \le \|r(x, t)\|$;
* the call is an `Optimization.IsARqpCallOut` on $\mu(\cdot, t)$ with the tolerances
  $\beta \|r(x, t)\| \varepsilon_j$.

The call is an ARqp run on $\mu(\cdot, t)$, stopped at its termination or as soon as
$\|r(\cdot, t)\| < \theta\varepsilon_0$. -/
theorem exists_arqpCall
    (hf : LipschitzDerivsAnchored (targetMerit f c t) X₀ (targetSublevel f c X t) p p L)
    (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ targetSublevel f c X t,
      ‖iteratedFDeriv ℝ i (targetMerit f c t) y‖ ≤ Optimization.finMax 1 L p)
    (hXX₀ : X ⊆ X₀) (P : Optimization.ARqpParams) (hσ : 0 < P.σmin) (hθς : P.θ < P.ς)
    (hq : 1 ≤ q) (hqp : q ≤ p) (hX : IsClosed X) (hθ0 : 0 < θ) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {x : E} (hx : x ∈ X)
    (hlo : θ * ε 0 ≤ targetResidual f c t x) (hhi : targetResidual f c t x ≤ ε 0) :
    ∃ o : InnerCall E, o.xi 0 = x ∧ o.xi o.e ∈ X ∧
      (∀ j ∈ Finset.Icc 1 q, 0 < o.δ j ∧ o.δ j ≤ 1) ∧
      (targetResidual f c t (o.xi o.e) < θ * ε 0 ∨ targetCrit f c X q ε t (o.xi o.e) o.δ) ∧
      (∀ i < o.e, targetMerit f c t (o.xi (i + 1)) ≤ targetMerit f c t (o.xi i)) ∧
      (∀ i < o.e, θ * ε 0 ≤ targetResidual f c t (o.xi i)) ∧
      targetResidual f c t (o.xi o.e) ≤ targetResidual f c t x ∧
      Optimization.IsARqpCallOut G (targetMerit f c t) X p q P
        (fun j => β * targetResidual f c t x * ε j) o.xi o.e o.succ o.δ := by
  set F := targetMerit f c t with hFdef
  set ρ := targetResidual f c t x with hρ
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have hε₀ := hε 0 (by simp)
  have hρ0 : 0 < ρ := lt_of_lt_of_le (mul_pos hθ0 hε₀.1) hlo
  have hε' : ∀ j ∈ Finset.Icc 1 q, β * ρ * ε j ∈ Ioc 0 1 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hεI j hj
    refine ⟨by positivity, ?_⟩
    have : β * ρ ≤ 1 := by nlinarith
    nlinarith
  have hS : ∀ y ∈ X, F y ≤ F x → y ∈ targetSublevel f c X t := fun y hy hyx =>
    ⟨hy, (targetMerit_le_targetMerit_iff.1 hyx).trans (hhi.trans hε₀.2)⟩
  obtain ⟨xi, e, succ, δo, hcall, hx0, hmem, hδo, hmono, hle, hstop, hend⟩ :=
    Optimization.exists_isARqpCallOut_of_stop G hX hx (flow := 0)
      (fun y _ => targetMerit_nonneg) hf hL hjet hXX₀ hS P hσ hθς hq hqp hε'
      (fun y => targetResidual f c t y < θ * ε 0)
  have hcrit : ∀ δo : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δo j) →
      Optimization.IsEpsDeltaApprox (ftaylorSeries ℝ F (xi e)) {d | xi e + d ∈ X} q
        (fun j => β * ρ * ε j) δo →
      θ * ε 0 ≤ targetResidual f c t (xi e) → targetCrit f c X q ε t (xi e) δo := by
    intro δo hδo happ hge j hj
    refine (happ j hj).trans ?_
    have hδ := hδo j hj
    have hεj := (hεI j hj).1
    have : β * ρ ≤ targetResidual f c t (xi e) := by nlinarith
    have : β * ρ * ε j ≤ ε j * targetResidual f c t (xi e) := by nlinarith
    change β * ρ * ε j * δo j ^ j / (j ! : ℝ) ≤
      ε j * targetResidual f c t (xi e) * δo j ^ j / (j ! : ℝ)
    gcongr
  refine ⟨⟨xi, e, succ, δo⟩, hx0, hmem, hδo, ?_, hmono, fun i hi => not_lt.1 (hstop i hi),
    targetMerit_le_targetMerit_iff.1 (hle e le_rfl), hcall⟩
  by_cases hlt : targetResidual f c t (xi e) < θ * ε 0
  · exact Or.inl hlt
  · exact Or.inr (hcrit δo (fun j hj => (hδo j hj).1) (hend.resolve_left hlt) (not_lt.1 hlt))

open Classical in
/-- **One unit-radius ARqp inner call exists on the whole space.** Let $E$ be finite-dimensional and
fix a target $t$. Let $\mathcal{L}(t)$ here be the sublevel set in $E$. Suppose that
$\mu(\cdot, t)$ satisfies the anchored Lipschitz condition of order $p$ on $E$, anchored in
$\mathcal{L}(t)$, with constants $L$ and $L_p \ge 1$, and that $\|\nabla^i \mu(y, t)\| \le
\max(1, \max_{1 \le j \le p} L_j)$ for $i = 2, \dots, p$ and every $y \in \mathcal{L}(t)$. Let
the ARqp parameters satisfy $\sigma_{\min} > 0$ and $\theta_P < \varsigma_P$, let
$1 \le q \le \min(2, p)$, $\theta > 0$, $0 < \beta \le \theta$ and $\varepsilon_j \in (0, 1]$
for $j = 0, \dots, q$. Then for every $x$ with $\theta\varepsilon_0 \le \|r(x, t)\| \le
\varepsilon_0$ there is a call $o$ with $e$ iterations such that:

* $o_0 = x$, and the radii satisfy $\delta_j \in (0, 1]$ for $j = 1, \dots, q$;
* $\|r(o_e, t)\| < \theta\varepsilon_0$, or the criticality test (14.3.34) on the whole space
  holds at $(o_e, t)$ with the radii $\delta$;
* $\mu(\cdot, t)$ does not increase along the call, and $\|r(o_i, t)\| \ge \theta\varepsilon_0$
  for every $i < e$;
* $\|r(o_e, t)\| \le \|r(x, t)\|$;
* the call is an `Optimization.IsARqpUnitCallOut` on $\mu(\cdot, t)$ with the tolerances
  $\beta \|r(x, t)\| \varepsilon_j$, and its radii are $1$.

The call is the ARqp run of `Optimization.exists_isARqpUnitCallOut_of_stop` on $\mu(\cdot, t)$,
stopped at its termination or as soon as $\|r(\cdot, t)\| < \theta\varepsilon_0$. -/
theorem exists_arqpUnitCall
    (hf : LipschitzDerivsAnchored (targetMerit f c t) univ (targetSublevel f c univ t) p p L)
    (hL : 1 ≤ L p)
    (hjet : ∀ i ∈ Finset.Icc 2 p, ∀ y ∈ targetSublevel f c univ t,
      ‖iteratedFDeriv ℝ i (targetMerit f c t) y‖ ≤ Optimization.finMax 1 L p)
    (P : Optimization.ARqpParams) (hσ : 0 < P.σmin) (hθς : P.θ < P.ς)
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hqp : q ≤ p) (hθ0 : 0 < θ) (hβ0 : 0 < β) (hβθ : β ≤ θ)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {x : E}
    (hlo : θ * ε 0 ≤ targetResidual f c t x) (hhi : targetResidual f c t x ≤ ε 0) :
    ∃ o : InnerCall E, o.xi 0 = x ∧ o.xi o.e ∈ (univ : Set E) ∧
      (∀ j ∈ Finset.Icc 1 q, 0 < o.δ j ∧ o.δ j ≤ 1) ∧
      (targetResidual f c t (o.xi o.e) < θ * ε 0 ∨ targetCrit f c univ q ε t (o.xi o.e) o.δ) ∧
      (∀ i < o.e, targetMerit f c t (o.xi (i + 1)) ≤ targetMerit f c t (o.xi i)) ∧
      (∀ i < o.e, θ * ε 0 ≤ targetResidual f c t (o.xi i)) ∧
      targetResidual f c t (o.xi o.e) ≤ targetResidual f c t x ∧
      Optimization.IsARqpUnitCallOut (targetMerit f c t) p q P
        (fun j => β * targetResidual f c t x * ε j) o.xi o.e o.succ o.δ := by
  set ρ := targetResidual f c t x with hρ
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have hε₀ := hε 0 (by simp)
  have hρ0 : 0 < ρ := lt_of_lt_of_le (mul_pos hθ0 hε₀.1) hlo
  have hε' : ∀ j ∈ Finset.Icc 1 q, β * ρ * ε j ∈ Ioc 0 1 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hεI j hj
    refine ⟨by positivity, ?_⟩
    have : β * ρ ≤ 1 := by nlinarith
    nlinarith
  have hS : ∀ y, targetMerit f c t y ≤ targetMerit f c t x → y ∈ targetSublevel f c univ t :=
    fun y hyx => ⟨mem_univ y, (targetMerit_le_targetMerit_iff.1 hyx).trans (hhi.trans hε₀.2)⟩
  obtain ⟨xi, e, succ, hcall, hx0, hmono, hle, hstop, hend⟩ :=
    Optimization.exists_isARqpUnitCallOut_of_stop (flow := 0)
      (fun _ => targetMerit_nonneg) hf hL hjet P hσ hθς hq hq2 hqp x hS hε'
      (fun y => targetResidual f c t y < θ * ε 0)
  refine ⟨⟨xi, e, succ, fun _ => 1⟩, hx0, mem_univ _, fun _ _ => ⟨one_pos, le_rfl⟩, ?_, hmono,
    fun i hi => not_lt.1 (hstop i hi), targetMerit_le_targetMerit_iff.1 (hle e le_rfl), hcall⟩
  by_cases hlt : targetResidual f c t (xi e) < θ * ε 0
  · exact Or.inl hlt
  · refine Or.inr fun j hj => ((hend.resolve_left hlt) j hj).trans ?_
    have hεj := (hεI j hj).1
    have hge := not_lt.1 hlt
    have : β * ρ ≤ targetResidual f c t (xi e) := by nlinarith
    have : β * ρ * ε j ≤ ε j * targetResidual f c t (xi e) := by nlinarith
    change β * ρ * ε j * 1 ^ j / (j ! : ℝ) ≤
      ε j * targetResidual f c t (xi e) * 1 ^ j / (j ! : ℝ)
    gcongr

end Existence

end Constrained
