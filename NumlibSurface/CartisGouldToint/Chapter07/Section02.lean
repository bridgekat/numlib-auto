import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Numlib.Optimization.Constrained.TwoPhase
import NumlibSurface.CartisGouldToint.Chapter06.Section03
import NumlibSurface.CartisGouldToint.Chapter07.Section01

/-!
# Cartis–Gould–Toint §7.2: Finding first-order approximate minimizers

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §7.2: the two-phase
target-following algorithm TPp-GC (Algorithm 7.2.1) for `minimize f(x)` subject to `x ∈ 𝒞`,
`c(x) = 0` (7.1.1), its termination guarantees (Lemma 7.2.1) and the evaluation complexity of
its optimality phase (Lemmas 7.2.3–7.2.6, Theorem 7.2.7). The residual `‖r(x, t)‖` and the merit
function `μ₂(x, t) = ½ ‖r(x, t)‖²` are `Constrained.targetResidual f c t x` and
`Constrained.targetMerit f c t x`; the outer bookkeeping of the targets is the backbone
`Constrained.IsTargetSequence`.

## Main definitions

* `AssumptionCD1pLC c C p`, `AssumptionFD1pLC f C p` — c.D1pL.C and f.D1pL.C;
* `nearFeasible C c β` — the region of near feasibility `ℱ_β = {x ∈ 𝒞 | ‖c(x)‖ ≤ β}` (7.2.7);
* `AssumptionBFb f c C β flow fup` — f.B.Fb: `flow ≤ f(x) ≤ fup` on `ℱ_β`;
* `AssumptionMu2DpLC f c C p` — μ₂.DpL.C;
* `TPpGCParams`, `TPpGCTol` — the constants and tolerances (7.2.8) of Algorithm 7.2.1;
* `innerStop`, `targetCrit` — the tests (7.2.10) and (7.2.12);
* `Phase2Seq`, `IsTPpGCPhase2` — the sequences of Phase 2 and the run predicate; `Phase2Seq.IsKa`,
  `Phase2Seq.IsKb` — the sets `𝒦_a`, `𝒦_b` (7.2.25); `Phase2Seq.Stop`, `Phase2Seq.IsEnd` —
  termination; `Phase2Seq.funEvals`, `Phase2Seq.derivEvals` — the evaluation counts;
  `Phase2Seq.IsGood`, `Phase2Seq.IsBad` — good inner iterations and bad outer iterations;
* `algorithm_7_2_1` — a whole run of TPp-GC (Phase 1, an ARpLE-CC run on `c`, then Phase 2).

## Main results

* `exists_innerRun`, `exists_phase2` — the inner runs exist and terminate; Phase 2 exists;
* `lemma_7_2_1_phase2` (with `IsTPpGCPhase2.output_spec`) — Lemma 7.2.1 for Phase 2;
* `lemma_7_2_3`, `lemma_7_2_4`, `lemma_7_2_5` — Lemmas 7.2.3–7.2.5 (with
  `IsTPpGCPhase2.inner_sigma_le`);
* `lemma_7_2_6`, `theorem_7_2_7_phase2` — the corrected Lemma 7.2.6 and Theorem 7.2.7 for Phase 2,
  with `lemma_7_2_6_of_mu2`, `theorem_7_2_7_phase2_of_mu2` under the book's μ₂.DpL.C and f.B.Fb;
* `algorithm_7_2_1_exists`, `lemma_7_2_1`, `lemma_7_2_2`, `theorem_7_2_7` — existence of runs,
  Lemma 7.2.1, Lemma 7.2.2 (Phase 1) and Theorem 7.2.7 for the whole algorithm.

## Deviations from the book

* f.B.Fb is stated "if `ℱ_β ≠ ∅`"; for the universally quantified form used here that proviso is
  vacuous. The constants `flow`, `fup` are explicit arguments.
* In f.D1pL.C the book writes `∇^j_x f_i`; the objective is scalar and `∇^j_x f` is meant.
* The derivative tensors in c.D1pL.C and f.D1pL.C are the Fréchet derivatives
  `iteratedFDeriv ℝ j`, with Mathlib's operator norm; the Lipschitz and boundedness constants are
  existentially quantified, as in the book.
* Step 1 of Phase 2 applies ARp1-CC (Algorithm 6.2.2), not ARp-CC: the proof of Lemma 7.2.6 uses
  Lemma 6.2.4, i.e. the step rule (6.2.29); ARp-CC's (6.2.10) with a fixed tolerance does not fit
  the relative test of (7.2.10).
* Step 2(a) is entered when `‖r(x_{k+1}, t_k)‖ ≤ θε₀` (printed `< θε₀`): with `<`, an inner run
  stopped by `‖r‖ = θε₀` exactly, with `f ≥ t` and a large criticality measure, falls into
  Step 2(c) and terminates without the guarantee (7.2.17), contradicting Lemma 7.2.1. With `≤`,
  the strict `‖c(x_ε)‖ > θε₀` in (7.2.15) also follows (the printed proof only gives `≥`).
* Counting (Lemma 7.2.6, Theorem 7.2.7): the printed block argument bounds only successful inner
  iterations whose new iterate fails the third test of (7.2.10) ("good" iterations). It omits the
  restart of `σ` at `σ₀` in every inner run (Lemma 2.4.1 is applied per run here), the `i = 0`
  elements of `𝓘^s_k` (so (7.2.39) fails as printed when its right-hand side is `< 1`), and the
  outer iterations of `𝒦_b` whose inner run contains no good iteration ("bad" iterations; their
  last successful iteration lands on a point that passes the third test): no decrease is
  guaranteed for these and the book gives no bound on their number. Theorem 7.2.7 is therefore
  stated with the number of bad iterations as a parameter; with it bounded independently of `ε`,
  the counts are of the order
  `O(max(ε₀^{-1}, ε₀^{-1/p} ε₁^{-(p+1)/p}))` of (7.2.50). The derivative count acquires the
  `ε₀^{-1}` term: it is part of the proven bound, since every iteration of `𝒦_a` needs a
  successful inner iteration; whether the book's (7.2.53), which lacks it, holds is not
  established. The good iterations are counted by one telescoping over all outer iterations,
  which gives the sharper constant `κ₁⁻¹ θ^{-(p+1)/p}` instead of (7.2.47)'s `θ^{-(p+2)/p}`.
* Lemma 7.2.2: the printed derivative-evaluation bound (7.2.24) lacks the `+ 2` of
  Theorem 6.3.1, which is restored.
* Lemma 7.2.5's uniform Lipschitz constant uses that `μ₂` is affine in `t` up to a constant; the
  book's hypothesis φℓ.DpL.C is not needed.
-/

open Set Optimization
open scoped Nat

namespace CartisGouldToint.Chapter07

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-- Smoothness of a scalar function `g` in the sense of c.D1pL.C / f.D1pL.C of
[cartis2022evaluation], §7.2.2.1: `g` is `p` times continuously differentiable on an open set
`𝒟 ⊇ 𝒞`, and for each `j ∈ [1 : p]` its derivative tensor `∇^j g` is Lipschitz continuous and
bounded on `𝒞`. -/
def IsD1pLOn (g : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) : Prop :=
  (∃ D, IsOpen D ∧ C ⊆ D ∧ ContDiffOn ℝ p g D) ∧
    ∀ j ∈ Finset.Icc 1 p, (∃ L, IteratedFDerivLipschitzOn g j L C) ∧
      ∃ B, ∀ x ∈ C, ‖iteratedFDeriv ℝ j g x‖ ≤ B

/-- **Assumption c.D1pL.C** of [cartis2022evaluation], §7.2.2.1: the constraint functions
`cᵢ`, `i ∈ [1 : m]`, are `p` times continuously differentiable in an open set containing `𝒞`,
and their derivative tensors `∇^j cᵢ`, `j ∈ [1 : p]`, are Lipschitz continuous and bounded
in `𝒞`. -/
def AssumptionCD1pLC (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (p : ℕ) : Prop :=
  ∀ i, IsD1pLOn (fun x => c x i) C p

/-- **Assumption f.D1pL.C** of [cartis2022evaluation], §7.2.2.1: the objective `f` is `p` times
continuously differentiable in an open set containing `𝒞`, and its derivative tensors `∇^j f`,
`j ∈ [1 : p]`, are Lipschitz continuous and bounded in `𝒞`. -/
def AssumptionFD1pLC (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) : Prop :=
  IsD1pLOn f C p

/-- The region of near feasibility `ℱ_β = {x ∈ 𝒞 | ‖c(x)‖ ≤ β}` of [cartis2022evaluation],
(7.2.7). -/
def nearFeasible (C : Set ℝⁿ) (c : ℝⁿ → ℝᵐ) (β : ℝ) : Set ℝⁿ := {x ∈ C | ‖c x‖ ≤ β}

/-- **Assumption f.B.Fb** of [cartis2022evaluation], §7.2.2.1: `f` is bounded below by `flow`
and above by `fup` on the region of near feasibility `ℱ_β`. -/
def AssumptionBFb (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (β flow fup : ℝ) : Prop :=
  ∀ x ∈ nearFeasible C c β, flow ≤ f x ∧ f x ≤ fup

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {x : ℝⁿ} {p : ℕ} {β β' flow fup : ℝ}

theorem isD1pLOn_iff {g : ℝⁿ → ℝ} :
    IsD1pLOn g C p ↔ (∃ D, IsOpen D ∧ C ⊆ D ∧ ContDiffOn ℝ p g D) ∧
      ∀ j ∈ Finset.Icc 1 p, (∃ L, IteratedFDerivLipschitzOn g j L C) ∧
        ∃ B, ∀ x ∈ C, ‖iteratedFDeriv ℝ j g x‖ ≤ B :=
  Iff.rfl

theorem assumptionCD1pLC_iff : AssumptionCD1pLC c C p ↔ ∀ i, IsD1pLOn (fun x => c x i) C p :=
  Iff.rfl

theorem assumptionFD1pLC_iff : AssumptionFD1pLC f C p ↔ IsD1pLOn f C p := Iff.rfl

theorem mem_nearFeasible : x ∈ nearFeasible C c β ↔ x ∈ C ∧ ‖c x‖ ≤ β := Iff.rfl

theorem nearFeasible_subset : nearFeasible C c β ⊆ C := fun _ hx => hx.1

theorem nearFeasible_mono (h : β ≤ β') : nearFeasible C c β ⊆ nearFeasible C c β' :=
  fun _ hx => ⟨hx.1, hx.2.trans h⟩

/-- The feasible set lies in every region of near feasibility with `β ≥ 0`. -/
theorem feasibleSet_subset_nearFeasible (hβ : 0 ≤ β) : feasibleSet C c ⊆ nearFeasible C c β :=
  fun _ hx => ⟨hx.1, by simpa [hx.2] using hβ⟩

theorem assumptionBFb_iff :
    AssumptionBFb f c C β flow fup ↔ ∀ x ∈ C, ‖c x‖ ≤ β → flow ≤ f x ∧ f x ≤ fup :=
  ⟨fun h x hx hc => h x ⟨hx, hc⟩, fun h x hx => h x hx.1 hx.2⟩

/-- f.B.Fb with parameter `β` holds for every smaller parameter. -/
theorem AssumptionBFb.mono (h : AssumptionBFb f c C β flow fup) (hβ : β' ≤ β) :
    AssumptionBFb f c C β' flow fup :=
  fun x hx => h x (nearFeasible_mono hβ hx)

/-! ### The assumption μ₂.DpL.C and the data of Algorithm 7.2.1 -/

/-- **Assumption μ₂.DpL.C** of [cartis2022evaluation], §7.2.2.1 (footnote 53: Φℓ.DpL.C for
`Φ_ℓ = μ₂(·, t)`): for every target `t`, the merit function `μ₂(·, t) = ½ ‖r(·, t)‖²` satisfies
f.DpL.C on `𝒞` with some Lipschitz constant (which may depend on `t`; Lemma 7.2.5 makes it uniform
over the relevant targets). -/
def AssumptionMu2DpLC (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (p : ℕ) : Prop :=
  ∀ t : ℝ, ∃ L, Chapter06.AssumptionDpLC (Constrained.targetMerit f c t) C p L

/-- The constants of Algorithm 7.2.1 (TPp-GC) of [cartis2022evaluation]: those of the
adaptive-regularization algorithms of Chapter 6 (`Chapter06.ARpCCParams`, used by both phases;
only `θ₁` among their `θ`'s enters ARp1-CC and ARpLE-CC), the infeasibility bound `β > 0` defining
`ℱ_β`, and the constant `θ ∈ (0, 1)`. -/
structure TPpGCParams extends toARpCCParams : Chapter06.ARpCCParams where
  /-- The factor `θ` of the tests `‖c(x)‖ ≤ θε₀` and `‖r(x, t)‖ ≤ θε₀`. -/
  θ : ℝ
  /-- The infeasibility bound `β` of `ℱ_β`. -/
  β : ℝ
  θ_pos : 0 < θ
  θ_lt_one : θ < 1
  β_pos : 0 < β

/-- The tolerances (7.2.8) of Algorithm 7.2.1 of [cartis2022evaluation]:
`0 < ε₀ ≤ min(1, β)` and `0 < ε₁ ≤ 1`. -/
structure TPpGCTol (P : TPpGCParams) (ε₀ ε₁ : ℝ) : Prop where
  ε₀_pos : 0 < ε₀
  ε₀_le_one : ε₀ ≤ 1
  ε₀_le_β : ε₀ ≤ P.β
  ε₁_pos : 0 < ε₁
  ε₁_le_one : ε₁ ≤ 1

/-- The termination test (7.2.10) of the inner iteration of Phase 2 of Algorithm 7.2.1 of
[cartis2022evaluation], for the target `t`: `‖r(x, t)‖ ≤ θε₀`, or `f(x) < t`, or
`ω_{μ₂,𝒞,1}(x, t) ≤ ε₁ ‖r(x, t)‖`. -/
def innerStop (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (θ ε₀ ε₁ t : ℝ) (x : ℝⁿ) : Prop :=
  Constrained.targetResidual f c t x ≤ θ * ε₀ ∨ f x < t ∨
    Chapter06.omega1 (Constrained.targetMerit f c t) C x ≤
      ε₁ * Constrained.targetResidual f c t x

/-- The test (7.2.12) of [cartis2022evaluation] (also the third test of (7.2.10)):
`ω_{μ₂,𝒞,1}(x, t) ≤ ε₁ ‖r(x, t)‖`. -/
def targetCrit (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (ε₁ t : ℝ) (x : ℝⁿ) : Prop :=
  Chapter06.omega1 (Constrained.targetMerit f c t) C x ≤ ε₁ * Constrained.targetResidual f c t x

theorem innerStop_iff {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {θ ε₀ ε₁ t : ℝ} {x : ℝⁿ} :
    innerStop f c C θ ε₀ ε₁ t x ↔ Constrained.targetResidual f c t x ≤ θ * ε₀ ∨ f x < t ∨
      targetCrit f c C ε₁ t x := Iff.rfl

/-- The sequences generated by Phase 2 of Algorithm 7.2.1 of [cartis2022evaluation], indexed by
the outer iteration `k ≥ 1` (the values at `k = 0` are unused): the outer iterates `X k = x_k`, the
targets `t k = t_k`, and the `k`-th inner ARp1-CC run on `μ₂(·, t_k)` with iterates `xi k i =
x_{k,i}`, steps `si k i`, regularization parameters `σi k i` and length `e k = e_k`. -/
structure Phase2Seq (n : ℕ) where
  /-- The outer iterates. -/
  X : ℕ → EuclideanSpace ℝ (Fin n)
  /-- The targets. -/
  t : ℕ → ℝ
  /-- The inner iterates. -/
  xi : ℕ → ℕ → EuclideanSpace ℝ (Fin n)
  /-- The inner steps. -/
  si : ℕ → ℕ → EuclideanSpace ℝ (Fin n)
  /-- The inner regularization parameters. -/
  σi : ℕ → ℕ → ℝ
  /-- The lengths of the inner runs. -/
  e : ℕ → ℕ

namespace Phase2Seq

variable (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (p : ℕ) (P : TPpGCParams) (ε₀ ε₁ : ℝ)
  (D : Phase2Seq n)

/-- Outer iteration `k` is in `𝒦_a` ((7.2.25) of [cartis2022evaluation]): Step 2(a) occurs,
`‖r(x_{k+1}, t_k)‖ ≤ θε₀` (the book prints `<`; see the module documentation). -/
def IsKa (k : ℕ) : Prop := Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ≤ P.θ * ε₀

/-- Outer iteration `k` is in `𝒦_b` ((7.2.25) of [cartis2022evaluation]): Step 2(b) occurs,
`‖r(x_{k+1}, t_k)‖ > θε₀` and `f(x_{k+1}) < t_k`. -/
def IsKb (k : ℕ) : Prop :=
  P.θ * ε₀ < Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ∧ f (D.X (k + 1)) < D.t k

/-- Phase 2 terminates at outer iteration `k` (Step 2 of Algorithm 7.2.1): in case (c), or in
cases (a)/(b) when (7.2.12) holds at `(x_{k+1}, t_{k+1})`. -/
def Stop (k : ℕ) : Prop :=
  (¬ D.IsKa f c P ε₀ k ∧ ¬ D.IsKb f c P ε₀ k) ∨
    ((D.IsKa f c P ε₀ k ∨ D.IsKb f c P ε₀ k) ∧ targetCrit f c C ε₁ (D.t (k + 1)) (D.X (k + 1)))

/-- No outer iteration `j ∈ [1, k)` has terminated Phase 2. -/
def Before (k : ℕ) : Prop := ∀ j, 1 ≤ j → j < k → ¬ D.Stop f c C P ε₀ ε₁ j

/-- Phase 2 terminates at outer iteration `kε ≥ 1`. -/
def IsEnd (kε : ℕ) : Prop := 1 ≤ kε ∧ D.Stop f c C P ε₀ ε₁ kε ∧ D.Before f c C P ε₀ ε₁ kε

open Classical in
/-- The output target `t_ε` of Phase 2 terminating at outer iteration `k`: `t_{k+1}` in cases
(a)/(b) and `t_k` in case (c) (the output point is `x_ε = x_{k+1}`). -/
noncomputable def targetOut (k : ℕ) : ℝ :=
  if D.IsKa f c P ε₀ k ∨ D.IsKb f c P ε₀ k then D.t (k + 1) else D.t k

/-- Inner iteration `i` of the `k`-th inner run is successful. -/
def InnerSucc (k i : ℕ) : Prop :=
  P.η₁ ≤ taylorRatio (Constrained.targetMerit f c (D.t k)) p (D.xi k) (D.si k) i

open Classical in
/-- The number of evaluations of `(f, c)` in Phase 2 up to outer iteration `k`:
`1 + ∑_{j ∈ [1, k]} e_j` (one at `x₁` and one per inner iteration). -/
noncomputable def funEvals (k : ℕ) : ℕ := 1 + ∑ j ∈ Finset.Icc 1 k, D.e j

open Classical in
/-- The number of evaluations of the derivatives of `(f, c)` in Phase 2 up to outer iteration
`k`: one at `x₁` and one per successful inner iteration. -/
noncomputable def derivEvals (k : ℕ) : ℕ :=
  1 + ∑ j ∈ Finset.Icc 1 k, ((Finset.range (D.e j)).filter (D.InnerSucc f c p P j)).card

/-- A *good* inner iteration `(k, i)`: it is successful, and its new iterate fails the third test
of (7.2.10) with residual `> θε₀`. The decrease of these iterations is controlled by Lemma 6.2.4
(the iterations counted by the proof of Lemma 7.2.6 of [cartis2022evaluation]). -/
def IsGood (k i : ℕ) : Prop :=
  i < D.e k ∧ D.InnerSucc f c p P k i ∧ ¬ targetCrit f c C ε₁ (D.t k) (D.xi k (i + 1)) ∧
    P.θ * ε₀ < Constrained.targetResidual f c (D.t k) (D.xi k (i + 1))

end Phase2Seq

/-- **Phase 2 of Algorithm 7.2.1** (TPp-GC) of [cartis2022evaluation] started at the output `x₁`
of Phase 1 (with `x₁ ∈ 𝒞` and `‖c(x₁)‖ ≤ θε₀`), as a predicate on the sequences `D`: Step 0
(`t₁ = f(x₁) - √(ε₀² - ‖c(x₁)‖²)`), and for every outer iteration `k ≥ 1` reached: Step 1, an
ARp1-CC run (Algorithm 6.2.2, steps `Optimization.IsFirstOrderCCStep`) on `μ₂(·, t_k)` from `x_k`
with the termination test (7.2.10), stopped at its first hit `e_k`, `x_{k+1} = x_{k, e_k}`; Step 2,
the target updates (7.2.11) in case (a) and (7.2.13) in case (b). Termination is
`Phase2Seq.Stop`. (Corrections: ARp1-CC rather than ARp-CC, and Step 2(a) with `≤`; see the module
documentation.) -/
structure IsTPpGCPhase2 (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (p : ℕ) (P : TPpGCParams)
    (ε₀ ε₁ : ℝ) (x₁ : ℝⁿ) (D : Phase2Seq n) : Prop where
  /-- The tolerances (7.2.8). -/
  tol : TPpGCTol P ε₀ ε₁
  /-- `x₁ ∈ 𝒞`. -/
  mem_one : x₁ ∈ C
  /-- Phase 1 ended with `‖c(x₁)‖ ≤ θε₀`. -/
  norm_one_le : ‖c x₁‖ ≤ P.θ * ε₀
  X_one : D.X 1 = x₁
  /-- Step 0. -/
  t_one : D.t 1 = f x₁ - √(ε₀ ^ 2 - ‖c x₁‖ ^ 2)
  /-- Step 1: the inner run starts at `x_k`. -/
  inner_zero : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ k → D.xi k 0 = D.X k
  /-- Step 1: the inner ARp1-CC run on `μ₂(·, t_k)` with the test (7.2.10). -/
  inner_run : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ k →
    IsARRun P.toARParams (fun i => innerStop f c C P.θ ε₀ ε₁ (D.t k) (D.xi k i))
      (fun i => IsFirstOrderCCStep (Constrained.targetMerit f c (D.t k)) C p P.θ₁ (D.xi k i)
        (D.σi k i) (D.si k i)) (fun _ => False)
      (taylorRatio (Constrained.targetMerit f c (D.t k)) p (D.xi k) (D.si k)) (D.xi k) (D.si k)
      (D.σi k)
  /-- Step 1: the inner run stops at its first hit `e_k` of (7.2.10). -/
  inner_hit : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ k →
    IsFirstHit (fun i => innerStop f c C P.θ ε₀ ε₁ (D.t k) (D.xi k i)) (D.e k)
  /-- Step 1: `x_{k+1} = x_{k, e_k}`. -/
  X_succ : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ k → D.X (k + 1) = D.xi k (D.e k)
  /-- Step 2(a): (7.2.11). -/
  t_succ_a : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ k → D.IsKa f c P ε₀ k →
    D.t (k + 1) = f (D.X (k + 1)) - √(ε₀ ^ 2 - ‖c (D.X (k + 1))‖ ^ 2)
  /-- Step 2(b): (7.2.13). -/
  t_succ_b : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ k → D.IsKb f c P ε₀ k →
    D.t (k + 1) = 2 * f (D.X (k + 1)) - D.t k

namespace Phase2Seq

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {D : Phase2Seq n}

theorem before_one : D.Before f c C P ε₀ ε₁ 1 := fun _ h1 hj => absurd hj (by omega)

theorem Before.mono {k K : ℕ} (h : D.Before f c C P ε₀ ε₁ K) (hk : k ≤ K) :
    D.Before f c C P ε₀ ε₁ k := fun j h1 hj => h j h1 (hj.trans_le hk)

theorem Before.not_stop {k K : ℕ} (h : D.Before f c C P ε₀ ε₁ K) (hk1 : 1 ≤ k) (hk : k < K) :
    ¬ D.Stop f c C P ε₀ ε₁ k := h k hk1 hk

theorem Before.succ {k : ℕ} (h : D.Before f c C P ε₀ ε₁ k)
    (hs : 1 ≤ k → ¬ D.Stop f c C P ε₀ ε₁ k) : D.Before f c C P ε₀ ε₁ (k + 1) := by
  intro j h1 hj
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · exact h j h1 hj
  · exact hs h1

theorem IsKb.not_isKa {k : ℕ} (h : D.IsKb f c P ε₀ k) : ¬ D.IsKa f c P ε₀ k :=
  fun ha => absurd ha (not_le.2 h.1)

/-- Before termination, an outer iteration is in `𝒦_a` or in `𝒦_b`. -/
theorem isKa_or_isKb_of_not_stop {k : ℕ} (h : ¬ D.Stop f c C P ε₀ ε₁ k) :
    D.IsKa f c P ε₀ k ∨ D.IsKb f c P ε₀ k := by
  by_contra h'
  exact h (Or.inl (not_or.1 h'))

end Phase2Seq

namespace IsTPpGCPhase2

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₁ : ℝⁿ} {D : Phase2Seq n}

section Inner

variable (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D) {k : ℕ} (hk1 : 1 ≤ k)
  (hk : D.Before f c C P ε₀ ε₁ k)
include h hk1 hk

/-- Before its end, the inner run has not stopped. -/
theorem inner_not_stop {i : ℕ} (hi : i < D.e k) :
    ¬ innerStop f c C P.θ ε₀ ε₁ (D.t k) (D.xi k i) :=
  (h.inner_hit k hk1 hk).2 i hi

/-- The inner steps satisfy the ARp1-CC conditions before the end of the inner run. -/
theorem inner_step {i : ℕ} (hi : i < D.e k) :
    IsFirstOrderCCStep (Constrained.targetMerit f c (D.t k)) C p P.θ₁ (D.xi k i) (D.σi k i)
      (D.si k i) :=
  (h.inner_run k hk1 hk).step_of_forall_le
    (IsARRun.forall_le_not_stop_iff.2 fun _ hj => h.inner_not_stop hk1 hk (hj.trans_lt hi))

/-- The inner regularization parameters are positive up to the end of the inner run. -/
theorem inner_sigma_pos {i : ℕ} (hi : i ≤ D.e k) : 0 < D.σi k i :=
  (h.inner_run k hk1 hk).sigma_pos (K := D.e k)
    (IsARRun.forall_lt_not_stop_iff.2 fun _ hj => h.inner_not_stop hk1 hk hj) i hi

/-- The inner iterates stay in `𝒞` if `x_k ∈ 𝒞`. -/
theorem inner_mem (hX : D.X k ∈ C) {i : ℕ} (hi : i ≤ D.e k) : D.xi k i ∈ C := by
  refine (h.inner_run k hk1 hk).mem (C := C) (by rw [h.inner_zero k hk1 hk]; exact hX)
    (fun j hj _ _ => ?_) i (IsARRun.forall_lt_not_stop_iff.2 fun _ hj =>
      h.inner_not_stop hk1 hk (hj.trans_le hi))
  exact ((h.inner_run k hk1 hk).step_of_forall_le hj).mem

/-- The merit function `μ₂(·, t_k)` is nonincreasing along the inner run. -/
theorem inner_merit_antitone {i j : ℕ} (hij : i ≤ j) (hj : j ≤ D.e k) :
    Constrained.targetMerit f c (D.t k) (D.xi k j) ≤
      Constrained.targetMerit f c (D.t k) (D.xi k i) := by
  have hK := IsARRun.forall_lt_not_stop_iff.2 fun _ hj => h.inner_not_stop hk1 hk hj
  refine (h.inner_run k hk1 hk).objective_antitone
    (w := Constrained.targetMerit f c (D.t k))
    (pred := fun i => FormalMultilinearSeries.taylorDecrement
      (ftaylorSeries ℝ (Constrained.targetMerit f c (D.t k)) (D.xi k i)) p (D.si k i)) hK
    (fun _ _ => rfl) (fun i hi => ?_) i j hij hj
  have hd := lt_taylorDecrement_of_regularizedModel_lt (h.inner_step hk1 hk hi).decrease
  have := h.inner_sigma_pos hk1 hk hi.le
  exact lt_of_le_of_lt (by positivity) hd

/-- The residual `‖r(·, t_k)‖` is nonincreasing along the inner run. -/
theorem inner_resid_antitone {i j : ℕ} (hij : i ≤ j) (hj : j ≤ D.e k) :
    Constrained.targetResidual f c (D.t k) (D.xi k j) ≤
      Constrained.targetResidual f c (D.t k) (D.xi k i) :=
  Constrained.targetMerit_le_targetMerit_iff.1 (h.inner_merit_antitone hk1 hk hij hj)

/-- `‖r(x_{k+1}, t_k)‖ ≤ ‖r(x_k, t_k)‖`. -/
theorem resid_succ_le :
    Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ≤
      Constrained.targetResidual f c (D.t k) (D.X k) := by
  have := h.inner_resid_antitone hk1 hk (Nat.zero_le _) le_rfl
  rwa [← h.X_succ k hk1 hk, h.inner_zero k hk1 hk] at this

/-- The inner run ends on the test (7.2.10). -/
theorem innerStop_succ : innerStop f c C P.θ ε₀ ε₁ (D.t k) (D.X (k + 1)) := by
  rw [h.X_succ k hk1 hk]
  exact (h.inner_hit k hk1 hk).1

end Inner

variable (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
include h

/-- The outer iterates stay in `𝒞`. -/
theorem X_mem : ∀ k, 1 ≤ k → D.Before f c C P ε₀ ε₁ k → D.X k ∈ C := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base => intro _; rw [h.X_one]; exact h.mem_one
  | succ k hk1 ih =>
    intro hk
    have hk' := hk.mono k.le_succ
    rw [h.X_succ k hk1 hk']
    exact h.inner_mem hk1 hk' (ih hk') le_rfl

/-- **The outer bookkeeping of Phase 2** is a target sequence (`Constrained.IsTargetSequence`)
up to every outer iteration `K` reached, with `𝒦_a` given by `Phase2Seq.IsKa`. -/
theorem isTargetSequence {K : ℕ} (hK : D.Before f c C P ε₀ ε₁ K) :
    Constrained.IsTargetSequence f c P.θ ε₀ D.X D.t (D.IsKa f c P ε₀) K where
  norm_one_le := h.X_one ▸ h.norm_one_le
  target_one := by rw [h.t_one, h.X_one]
  residual_succ_le k hk1 hkK := h.resid_succ_le hk1 (hK.mono hkK.le)
  residual_le_of_Ka _ _ _ ha := ha
  target_succ_of_Ka k hk1 hkK ha := h.t_succ_a k hk1 (hK.mono hkK.le) ha
  le_residual_of_not_Ka _ _ _ ha := (not_le.1 ha).le
  lt_target_of_not_Ka k hk1 hkK ha :=
    ((Phase2Seq.isKa_or_isKb_of_not_stop (hK.not_stop hk1 hkK)).resolve_left ha).2
  target_succ_of_not_Ka k hk1 hkK ha := h.t_succ_b k hk1 (hK.mono hkK.le)
    ((Phase2Seq.isKa_or_isKb_of_not_stop (hK.not_stop hk1 hkK)).resolve_left ha)

end IsTPpGCPhase2

/-! ### Lemmas 7.2.3–7.2.5 -/

section Lemmas

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₁ : ℝⁿ} {D : Phase2Seq n}

/-- f.B.Fb with `ε₀ ≤ β` in the form used by `Constrained.IsTargetSequence`. -/
private theorem bfb_of_le {β flow fup : ℝ} (hB : AssumptionBFb f c C β flow fup) (hε : ε₀ ≤ β) :
    ∀ z ∈ C, ‖c z‖ ≤ ε₀ → flow ≤ f z ∧ f z ≤ fup :=
  fun z hz hcz => hB z ⟨hz, hcz.trans hε⟩

/-- **Lemma 7.2.3** of [cartis2022evaluation]. For a Phase-2 run of TPp-GC and every outer
iteration `K` reached: the targets decrease strictly on `[1, K]`; for `k ∈ [1, K]`,
`0 ≤ f(x_k) - t_k ≤ ε₀` and `‖c(x_k)‖ ≤ ε₀` ((7.2.26), (7.2.29)); for `k ∈ [1, K)`,
`‖r(x_{k+1}, t_{k+1})‖ = ε₀` and `t_k - t_{k+1} ≥ (1 - θ)ε₀` if `k ∈ 𝒦_a` ((7.2.27), (7.2.30)),
and `‖r(x_{k+1}, t_{k+1})‖ = ‖r(x_{k+1}, t_k)‖ ≤ ε₀` if `k ∈ 𝒦_b` ((7.2.28)); under f.B.Fb,
`t_k ∈ [f_low - 1, f_up]` for `k ∈ [1, K]` ((7.2.31)). -/
theorem lemma_7_2_3 (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D) {K : ℕ}
    (hK : D.Before f c C P ε₀ ε₁ K) :
    (∀ k, 1 ≤ k → k < K → D.t (k + 1) < D.t k) ∧
    (∀ k, 1 ≤ k → k ≤ K →
      0 ≤ f (D.X k) - D.t k ∧ f (D.X k) - D.t k ≤ ε₀ ∧ ‖c (D.X k)‖ ≤ ε₀) ∧
    (∀ k, 1 ≤ k → k < K → D.IsKa f c P ε₀ k →
      Constrained.targetResidual f c (D.t (k + 1)) (D.X (k + 1)) = ε₀ ∧
        (1 - P.θ) * ε₀ ≤ D.t k - D.t (k + 1)) ∧
    (∀ k, 1 ≤ k → k < K → D.IsKb f c P ε₀ k →
      Constrained.targetResidual f c (D.t (k + 1)) (D.X (k + 1)) =
          Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ∧
        Constrained.targetResidual f c (D.t (k + 1)) (D.X (k + 1)) ≤ ε₀) ∧
    (∀ flow fup, AssumptionBFb f c C P.β flow fup →
      ∀ k, 1 ≤ k → k ≤ K → D.t k ∈ Icc (flow - 1) fup) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := (h.isTargetSequence hK).props P.θ_pos.le P.θ_lt_one h.tol.ε₀_pos
  refine ⟨h1, h2, h3, fun k hk1 hkK hb => h4 k hk1 hkK hb.not_isKa, fun flow fup hB =>
    h5 h.tol.ε₀_le_one C flow fup (fun k hk1 hkK => h.X_mem k hk1 (hK.mono hkK))
      (bfb_of_le hB h.tol.ε₀_le_β)⟩

/-- **Lemma 7.2.4** of [cartis2022evaluation]: under f.B.Fb, for a Phase-2 run of TPp-GC and every
outer iteration `K ≥ 1` reached, the number of iterations `k ∈ [1, K)` in `𝒦_a` is at most
`(f_up - f_low + 1)/((1 - θ)ε₀)`. -/
theorem lemma_7_2_4 (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D) {flow fup : ℝ}
    (hB : AssumptionBFb f c C P.β flow fup) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : D.Before f c C P ε₀ ε₁ K) [DecidablePred (D.IsKa f c P ε₀)] :
    (((Finset.Ico 1 K).filter (D.IsKa f c P ε₀)).card : ℝ) ≤
      (fup - flow + 1) / ((1 - P.θ) * ε₀) :=
  (h.isTargetSequence hK).card_Ka_le P.θ_pos.le P.θ_lt_one h.tol.ε₀_pos h.tol.ε₀_le_one hK1
    (fun k hk1 hkK => h.X_mem k hk1 (hK.mono hkK)) (bfb_of_le hB h.tol.ε₀_le_β)

/-- **Lemma 7.2.5** of [cartis2022evaluation], first part: under μ₂.DpL.C (`p ≥ 1`), for any
interval `[a, b]` of targets there is `L_μ ≥ 0` such that `μ₂(·, t)` satisfies f.DpL.C on `𝒞`
with constant `L_μ` for every `t ∈ [a, b]` (applied with `[a, b] = [f_low - 1, f_up]`, which
contains all targets by Lemma 7.2.3). The constant is `max(L_a, L_b)`: `μ₂` is affine in `t` up to
an additive constant (the book's "continuous dependence on `t`" would not suffice). The hypothesis
φℓ.DpL.C listed by the book is not needed. -/
theorem lemma_7_2_5 (hμ : AssumptionMu2DpLC f c C p) (hp : 1 ≤ p) (a b : ℝ) :
    ∃ Lμ, 0 ≤ Lμ ∧ ∀ t ∈ Icc a b,
      Chapter06.AssumptionDpLC (Constrained.targetMerit f c t) C p Lμ := by
  obtain ⟨L₁, h₁⟩ := hμ a
  obtain ⟨L₂, h₂⟩ := hμ b
  refine ⟨max L₁ L₂, le_max_of_le_left h₁.nonneg, fun t ht => ⟨le_max_of_le_left h₁.nonneg, ?_,
    Constrained.iteratedFDerivHolderOn_targetMerit_of_mem_Icc (by omega) ht h₁.contDiffAt
      h₂.contDiffAt h₁.lipschitz h₂.lipschitz⟩⟩
  rcases ht.1.eq_or_lt with rfl | hat
  · exact h₁.contDiffOn
  obtain ⟨D₁, hD₁, hCD₁, hf₁⟩ := h₁.contDiffOn
  obtain ⟨D₂, hD₂, hCD₂, hf₂⟩ := h₂.contDiffOn
  refine ⟨D₁ ∩ D₂, hD₁.inter hD₂, subset_inter hCD₁ hCD₂, ?_⟩
  rw [Constrained.targetMerit_eq_lineMap (hat.trans_le ht.2)]
  exact (((hf₁.mono inter_subset_left).const_smul _).add
    ((hf₂.mono inter_subset_right).const_smul _)).add contDiffOn_const

end Lemmas

/-! ### Lemma 7.2.1 -/

section Termination

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₁ : ℝⁿ} {D : Phase2Seq n}

/-- (7.2.17) and (7.2.20) of [cartis2022evaluation]: when Phase 2 terminates at outer iteration
`k_ε`, the output `(x_ε, t_ε) = (x_{k_ε+1}, t_ε)` satisfies `x_ε ∈ 𝒞`,
`θε₀ < ‖r(x_ε, t_ε)‖ ≤ ε₀`, `f(x_ε) ≥ t_ε` and `ω_{μ₂,𝒞,1}(x_ε, t_ε) ≤ ε₁ ‖r(x_ε, t_ε)‖`. (The
strict lower bound uses the corrected Step 2(a).) -/
theorem IsTPpGCPhase2.output_spec (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D) {kε : ℕ}
    (hend : D.IsEnd f c C P ε₀ ε₁ kε) :
    D.X (kε + 1) ∈ C ∧
      P.θ * ε₀ < Constrained.targetResidual f c (D.targetOut f c P ε₀ kε) (D.X (kε + 1)) ∧
      Constrained.targetResidual f c (D.targetOut f c P ε₀ kε) (D.X (kε + 1)) ≤ ε₀ ∧
      D.targetOut f c P ε₀ kε ≤ f (D.X (kε + 1)) ∧
      targetCrit f c C ε₁ (D.targetOut f c P ε₀ kε) (D.X (kε + 1)) := by
  obtain ⟨hk1, hstop, hbef⟩ := hend
  set k := kε
  have hε₀ := h.tol.ε₀_pos
  have hθ1 := P.θ_lt_one
  have hθ0 := P.θ_pos
  have hX : D.X (k + 1) ∈ C := by
    rw [h.X_succ k hk1 hbef]
    exact h.inner_mem hk1 hbef (h.X_mem k hk1 hbef) le_rfl
  have hres : Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ≤ ε₀ :=
    (h.resid_succ_le hk1 hbef).trans
      ((h.isTargetSequence hbef).residual_le hθ1.le hε₀.le hk1 le_rfl)
  have hin := h.innerStop_succ hk1 hbef
  refine ⟨hX, ?_⟩
  unfold Phase2Seq.targetOut
  rcases hstop with ⟨hna, hnb⟩ | ⟨hab, hcrit⟩
  · -- case (c)
    rw [ite_eq_right (not_or.2 ⟨hna, hnb⟩)]
    have hlt : P.θ * ε₀ < Constrained.targetResidual f c (D.t k) (D.X (k + 1)) := not_le.1 hna
    have hle : D.t k ≤ f (D.X (k + 1)) := le_of_not_gt fun h' => hnb ⟨hlt, h'⟩
    refine ⟨hlt, hres, hle, ?_⟩
    rcases hin with h' | h' | h'
    · exact absurd h' hna
    · exact absurd h' (not_lt.2 hle)
    · exact h'
  · rw [ite_eq_left hab]
    rcases hab with ha | hb
    · -- case (a)
      have hc : ‖c (D.X (k + 1))‖ ≤ ε₀ :=
        Constrained.norm_le_targetResidual.trans (ha.trans (by nlinarith))
      have ht := h.t_succ_a k hk1 hbef ha
      have hr : Constrained.targetResidual f c (D.t (k + 1)) (D.X (k + 1)) = ε₀ := by
        rw [ht]; exact Constrained.targetResidual_sub_sqrt hε₀.le hc
      refine ⟨by rw [hr]; nlinarith, hr.le, ?_, hcrit⟩
      rw [ht]
      linarith [Real.sqrt_nonneg (ε₀ ^ 2 - ‖c (D.X (k + 1))‖ ^ 2)]
    · -- case (b)
      have ht := h.t_succ_b k hk1 hbef hb
      have hr : Constrained.targetResidual f c (D.t (k + 1)) (D.X (k + 1)) =
          Constrained.targetResidual f c (D.t k) (D.X (k + 1)) := by
        rw [ht, Constrained.targetResidual_two_mul_sub]
      refine ⟨hr ▸ hb.1, hr ▸ hres, ?_, hcrit⟩
      rw [ht]
      linarith [hb.2]

/-- **Lemma 7.2.1** of [cartis2022evaluation], Phase 2 (for the corrected algorithm; `f` and `c`
differentiable at the points of `𝒞`): if Phase 2 terminates at outer iteration `k_ε` with output
`x_ε = x_{k_ε+1}`, `t_ε = targetOut`, then (7.2.17) and (7.2.20) hold (`output_spec`), and either
`f(x_ε) = t_ε`, `ω_{Φ₂,𝒞,1}(x_ε) ≤ ε₁ ‖c(x_ε)‖` and `‖c(x_ε)‖ > θε₀` (7.2.15), with
`Φ₂ = ½ ‖c‖²`; or `f(x_ε) > t_ε` and `x_ε` is an `(ε₀, ε₁)`-approximate first-order minimizer
within `ℱ(𝒞, c)` with the multiplier `y_ε = -c(x_ε)/(f(x_ε) - t_ε)` (7.2.16), (7.2.22). (The
printed proof gives only `‖c(x_ε)‖ ≥ θε₀` in (7.2.15); the strict inequality follows from the
corrected Step 2(a).) -/
theorem lemma_7_2_1_phase2 (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
    (hf : ∀ x ∈ C, DifferentiableAt ℝ f x) (hc : ∀ x ∈ C, DifferentiableAt ℝ c x) {kε : ℕ}
    (hend : D.IsEnd f c C P ε₀ ε₁ kε) :
    (f (D.X (kε + 1)) = D.targetOut f c P ε₀ kε ∧
        Chapter06.omega1 (fun z => ‖c z‖ ^ 2 / 2) C (D.X (kε + 1)) ≤ ε₁ * ‖c (D.X (kε + 1))‖ ∧
        P.θ * ε₀ < ‖c (D.X (kε + 1))‖) ∨
      (D.targetOut f c P ε₀ kε < f (D.X (kε + 1)) ∧
        IsApproxFirstOrderGC f c C ε₀ ε₁ (D.X (kε + 1))
          (Constrained.targetMultiplier f c (D.targetOut f c P ε₀ kε) (D.X (kε + 1)))) := by
  obtain ⟨hX, hlow, hup, hle, hcrit⟩ := h.output_spec hend
  set x := D.X (kε + 1)
  set τ := D.targetOut f c P ε₀ kε
  rcases hle.eq_or_lt with heq | hlt
  · -- `f(x_ε) = t_ε`
    have hr : Constrained.targetResidual f c τ x = ‖c x‖ := by
      rw [heq]; exact Constrained.targetResidual_self
    refine Or.inl ⟨heq.symm, ?_, hr ▸ hlow⟩
    have hD : iteratedFDeriv ℝ 1 (Constrained.targetMerit f c τ) x =
        iteratedFDeriv ℝ 1 (fun z => ‖c z‖ ^ 2 / 2) x := by
      ext m
      rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply,
        Constrained.fderiv_targetMerit_of_eq (hf x hX) (hc x hX) heq.symm]
    have := hcrit
    rw [targetCrit, Chapter06.omega1, hD, hr] at this
    exact this
  · -- `f(x_ε) > t_ε`
    refine Or.inr ⟨hlt, hX, Constrained.norm_le_targetResidual.trans hup, ?_⟩
    have hτ : 0 < f x - τ := sub_pos.2 hlt
    have heq := Constrained.formCriticality_targetMerit_eq_mul (hf x hX) (hc x hX) hlt
      (feasibleSteps C x)
    have hcr := hcrit
    rw [targetCrit, Chapter06.omega1, heq] at hcr
    rw [omegaL_def, Chapter06.omega1, ← Constrained.targetResidual_div_eq_sqrt hlt,
      mul_div_assoc', le_div_iff₀ hτ]
    simp only [lagrangianVec_def]
    linarith
end Termination

/-! ### Counting the inner iterations of Phase 2 (Lemma 7.2.6) -/

namespace Phase2Seq

variable (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (p : ℕ) (P : TPpGCParams) (ε₀ ε₁ : ℝ)
  (D : Phase2Seq n)

open Classical in
/-- The number of good iterations (`Phase2Seq.IsGood`) of the `k`-th inner run. -/
noncomputable def goodCount (k : ℕ) : ℕ :=
  ((Finset.range (D.e k)).filter (D.IsGood f c C p P ε₀ ε₁ k)).card

open Classical in
/-- The number of successful iterations of the `k`-th inner run. -/
noncomputable def succCount (k : ℕ) : ℕ :=
  ((Finset.range (D.e k)).filter (D.InnerSucc f c p P k)).card

open Classical in
/-- The number of outer iterations in `𝒦_a` among `[1, K)`. -/
noncomputable def kaCount (K : ℕ) : ℕ := ((Finset.Ico 1 K).filter (D.IsKa f c P ε₀)).card

/-- A *bad* outer iteration: `k ∈ 𝒦_b` and its inner run contains no good iteration. For Phase-2
runs, the new iterate then passes the third test of (7.2.10) for the old target,
`ω_{μ₂,𝒞,1}(x_{k+1}, t_k) ≤ ε₁ ‖r(x_{k+1}, t_k)‖` (`IsTPpGCPhase2.isBad_targetCrit`); the book
gives no bound on the number of such iterations. -/
def IsBad (k : ℕ) : Prop := D.IsKb f c P ε₀ k ∧ D.goodCount f c C p P ε₀ ε₁ k = 0

open Classical in
/-- The number of bad outer iterations (`Phase2Seq.IsBad`) among `[1, K)`. -/
noncomputable def badCount (K : ℕ) : ℕ :=
  ((Finset.Ico 1 K).filter (D.IsBad f c C p P ε₀ ε₁)).card

end Phase2Seq

/-- The constant `κ^S_ARpGC = κ₁⁻¹ θ^{-(p+1)/p}` (the book's (7.2.47) has the weaker
`θ^{-(p+2)/p}`), with `κ₁ = η₁ σ_min/(p+1)! (p!/(L_μ + σ_μ,max + θ₁ p!))^{(p+1)/p}` of Lemma 6.2.4
for the merit functions `μ₂(·, t)` with uniform constant `L_μ` (Lemma 7.2.5). -/
noncomputable def kappaSGC (P : TPpGCParams) (Lμ : ℝ) (p : ℕ) : ℝ :=
  (Chapter06.kappa1CC P.toARpCCParams Lμ p)⁻¹ * P.θ ^ (-(((p : ℝ) + 1) / p))

/-- The bound `G = κ^S_ARpGC (1 - θ) ε₀^{(p-1)/p} ε₁^{-(p+1)/p}` of (7.2.39) of
[cartis2022evaluation] on the number of good inner iterations between two consecutive iterations
of `𝒦_a`. -/
noncomputable def goodBound (P : TPpGCParams) (Lμ : ℝ) (p : ℕ) (ε₀ ε₁ : ℝ) : ℝ :=
  kappaSGC P Lμ p * (1 - P.θ) * ε₀ ^ (((p : ℝ) - 1) / p) * ε₁ ^ (-(((p : ℝ) + 1) / p))

/-- The decrease `δ = κ₁ θ^{(p+1)/p} ε₀^{1/p} ε₁^{(p+1)/p}` of the residual on good iterations. -/
private noncomputable def goodDecr (P : TPpGCParams) (Lμ : ℝ) (p : ℕ) (ε₀ ε₁ : ℝ) : ℝ :=
  Chapter06.kappa1CC P.toARpCCParams Lμ p * P.θ ^ (((p : ℝ) + 1) / p) *
    (ε₀ ^ (((p : ℝ) + 1) / p - 1) * ε₁ ^ (((p : ℝ) + 1) / p))

private theorem goodDecr_pos {P : TPpGCParams} {Lμ ε₀ ε₁ : ℝ} (hL : 0 ≤ Lμ) (p : ℕ)
    (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) : 0 < goodDecr P Lμ p ε₀ ε₁ := by
  have := Chapter06.kappa1CC_pos (P := P.toARpCCParams) (p := p) hL; have := P.θ_pos
  unfold goodDecr; positivity

/-- `G = (1 - θ) ε₀ / δ`. -/
private theorem goodBound_eq {P : TPpGCParams} {Lμ ε₀ ε₁ : ℝ} (hL : 0 ≤ Lμ) {p : ℕ}
    (hp : 1 ≤ p) (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) :
    goodBound P Lμ p ε₀ ε₁ = (1 - P.θ) * ε₀ / goodDecr P Lμ p ε₀ ε₁ := by
  have hκ := Chapter06.kappa1CC_pos (P := P.toARpCCParams) (p := p) hL
  have hθ := P.θ_pos
  have h1 : ε₀ ^ (((p : ℝ) - 1) / p) = ε₀ ^ (1 : ℝ) / ε₀ ^ (((p : ℝ) + 1) / p - 1) := by
    rw [← Real.rpow_sub hε₀]
    congr 1
    have : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    field_simp; ring
  rw [goodBound, goodDecr, kappaSGC, Real.rpow_neg hθ.le, Real.rpow_neg hε₁.le, h1,
    Real.rpow_one]
  have : 0 < ε₀ ^ (((p : ℝ) + 1) / p - 1) := by positivity
  have : 0 < ε₁ ^ (((p : ℝ) + 1) / p) := by positivity
  have : 0 < P.θ ^ (((p : ℝ) + 1) / p) := by positivity
  field_simp

namespace IsTPpGCPhase2

section Counting

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₁ : ℝⁿ} {D : Phase2Seq n} (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
  {flow fup Lμ : ℝ} (hB : AssumptionBFb f c C P.β flow fup)
  (hL : ∀ t ∈ Icc (flow - 1) fup,
    Chapter06.AssumptionDpLC (Constrained.targetMerit f c t) C p Lμ)

include h hB in
/-- The targets of the outer iterations reached lie in `[f_low - 1, f_up]` ((7.2.31)). -/
theorem t_mem {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c C P ε₀ ε₁ k) :
    D.t k ∈ Icc (flow - 1) fup :=
  (lemma_7_2_3 h hk).2.2.2.2 flow fup hB k hk1 le_rfl

include h hB hL in
/-- **Lemma 7.2.5** of [cartis2022evaluation], second part: the regularization parameters of the
inner runs of Phase 2 stay in `[σ_min, σ_μ,max]`, `σ_μ,max = max(σ₀, γ₃ L_μ/(1 - η₂))`. -/
theorem inner_sigma_le (hC : Chapter06.AssumptionCNe C) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : D.Before f c C P ε₀ ε₁ k) {i : ℕ} (hi : i ≤ D.e k) :
    P.σmin ≤ D.σi k i ∧ D.σi k i ≤ P.toARpCCParams.sigmaMax Lμ :=
  (Chapter06.arpcc_sigma_le (P := P.toARpCCParams) (h.inner_run k hk1 hk) hC
    (hL _ (h.t_mem hB hk1 hk)) (by rw [h.inner_zero k hk1 hk]; exact h.X_mem k hk1 hk)
    (fun _ hs => ⟨hs.mem, hs.decrease⟩) i
    (fun _ hj => h.inner_not_stop hk1 hk (hj.trans_le hi))).2

include h hB hL in
/-- The residual decrease on a good inner iteration ((7.2.43) and the display after (7.2.46)):
`‖r(x_{k,i}, t_k)‖ - ‖r(x_{k,i+1}, t_k)‖ ≥ δ = κ₁ θ^{(p+1)/p} ε₀^{1/p} ε₁^{(p+1)/p}`. -/
private theorem good_decrease (hC : Chapter06.AssumptionCNe C) (hp : 1 ≤ p) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : D.Before f c C P ε₀ ε₁ k) {i : ℕ}
    (hg : D.IsGood f c C p P ε₀ ε₁ k i) :
    goodDecr P Lμ p ε₀ ε₁ ≤ Constrained.targetResidual f c (D.t k) (D.xi k i) -
      Constrained.targetResidual f c (D.t k) (D.xi k (i + 1)) := by
  obtain ⟨hi, hs, hncrit, hlow⟩ := hg
  have hdpl := hL _ (h.t_mem hB hk1 hk)
  have hX := h.X_mem k hk1 hk
  have hxi := h.inner_mem hk1 hk hX hi.le
  have hσ := h.inner_sigma_le hB hL hC hk1 hk hi.le
  have hsucc : D.xi k (i + 1) = D.xi k i + D.si k i :=
    (h.inner_run k hk1 hk).eq_add_of_succ
      (IsARRun.forall_le_not_stop_iff.2 fun _ hj => h.inner_not_stop hk1 hk (hj.trans_lt hi)) hs
  have hdec := (h.inner_step hk1 hk hi).sub_ge hC.convex hdpl.contDiffAt hdpl.lipschitz
    hdpl.nonneg hxi hp P.θ₁_pos.le P.σmin_nonneg hσ.1 hσ.2 P.η₁_pos hs
  rw [← hsucc] at hdec
  have hε₀ := h.tol.ε₀_pos
  have hε₁ := h.tol.ε₁_pos
  set ρ := Constrained.targetResidual f c (D.t k) (D.xi k i)
  set ρ' := Constrained.targetResidual f c (D.t k) (D.xi k (i + 1))
  have hρ' : 0 ≤ ρ' := Constrained.targetResidual_nonneg
  have hω : ε₁ * ρ' < Chapter06.omega1 (Constrained.targetMerit f c (D.t k)) C (D.xi k (i + 1)) :=
    lt_of_not_ge hncrit
  have hπ : 0 ≤ ((p : ℝ) + 1) / p := by positivity
  have hκ := Chapter06.kappa1CC_pos (P := P.toARpCCParams) (p := p) hdpl.nonneg
  have key : Chapter06.kappa1CC P.toARpCCParams Lμ p * (ρ' * ε₁) ^ (((p : ℝ) + 1) / p) ≤
      ρ ^ 2 / 2 - ρ' ^ 2 / 2 := by
    rw [← Constrained.targetMerit_eq, ← Constrained.targetMerit_eq]
    refine le_trans ?_ hdec
    rw [Chapter06.kappa1CC]
    gcongr
    rw [mul_comm]
    exact hω.le
  have hρle : ρ ≤ ε₀ :=
    (h.inner_resid_antitone hk1 hk (Nat.zero_le i) hi.le).trans (by
      rw [h.inner_zero k hk1 hk]
      exact (h.isTargetSequence hk).residual_le P.θ_lt_one.le hε₀.le hk1 le_rfl)
  exact Constrained.sub_ge_of_residual_decrease P.θ_pos P.θ_lt_one.le hε₀ hκ hπ le_rfl hε₁
    hlow.le (h.inner_resid_antitone hk1 hk i.le_succ hi) hρle key

include h hB hL in
/-- The good iterations of one inner run (the telescoping of (7.2.43) within one run):
`|good_k| δ ≤ max(‖r(x_k, t_k)‖, θε₀) - max(‖r(x_{k+1}, t_k)‖, θε₀)`. -/
private theorem goodCount_mul_le (hC : Chapter06.AssumptionCNe C) (hp : 1 ≤ p) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : D.Before f c C P ε₀ ε₁ k) :
    (D.goodCount f c C p P ε₀ ε₁ k : ℝ) * goodDecr P Lμ p ε₀ ε₁ ≤
      max (Constrained.targetResidual f c (D.t k) (D.X k)) (P.θ * ε₀) -
        max (Constrained.targetResidual f c (D.t k) (D.X (k + 1))) (P.θ * ε₀) := by
  classical
  have := card_mul_le_sub_of_decrease
    («φ» := fun j => max (Constrained.targetResidual f c (D.t k) (D.xi k j)) (P.θ * ε₀))
    (N := D.e k) (T := (Finset.range (D.e k)).filter (D.IsGood f c C p P ε₀ ε₁ k))
    (c := goodDecr P Lμ p ε₀ ε₁) (Finset.filter_subset _ _)
    (fun j hj => max_le_max (h.inner_resid_antitone hk1 hk j.le_succ hj) le_rfl)
    (fun j hj => by
      have hg := (Finset.mem_filter.1 hj).2
      have hd := h.good_decrease hB hL hC hp hk1 hk hg
      have h1 := hg.2.2.2
      have h2 := h.inner_resid_antitone hk1 hk j.le_succ hg.1
      rw [max_eq_left h1.le, max_eq_left (h1.le.trans h2)]
      exact hd)
  rw [h.inner_zero k hk1 hk, ← h.X_succ k hk1 hk] at this
  convert this using 2
  unfold Phase2Seq.goodCount
  congr

end Counting

end IsTPpGCPhase2

namespace IsTPpGCPhase2

section Counting2

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₁ : ℝⁿ} {D : Phase2Seq n} (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
  {flow fup Lμ : ℝ} (hB : AssumptionBFb f c C P.β flow fup)
  (hL : ∀ t ∈ Icc (flow - 1) fup,
    Chapter06.AssumptionDpLC (Constrained.targetMerit f c t) C p Lμ)

include h hB hL in
/-- **The good inner iterations of Phase 2** (the corrected (7.2.39) of [cartis2022evaluation],
summed over the blocks): for every outer iteration `K ≥ 1` reached, the number of good inner
iterations of the outer iterations `[1, K]` is at most `G (|𝒦_a ∩ [1, K)| + 1)`,
`G = goodBound`. -/
theorem sum_goodCount_le (hC : Chapter06.AssumptionCNe C) (hp : 1 ≤ p) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : D.Before f c C P ε₀ ε₁ K) :
    (∑ k ∈ Finset.Icc 1 K, D.goodCount f c C p P ε₀ ε₁ k : ℝ) ≤
      goodBound P Lμ p ε₀ ε₁ * (D.kaCount f c P ε₀ K + 1) := by
  have hε₀ := h.tol.ε₀_pos
  have hL0 : 0 ≤ Lμ := (hL _ (h.t_mem hB le_rfl Phase2Seq.before_one)).nonneg
  have hδ := goodDecr_pos (P := P) hL0 p hε₀ h.tol.ε₁_pos
  classical
  have hsum := (h.isTargetSequence hK).sum_max_sub_le P.θ_pos.le P.θ_lt_one.le hε₀.le hK1
  have h1 : ∑ k ∈ Finset.Icc 1 K, (D.goodCount f c C p P ε₀ ε₁ k : ℝ) * goodDecr P Lμ p ε₀ ε₁ ≤
      ∑ k ∈ Finset.Icc 1 K,
        (max (Constrained.targetResidual f c (D.t k) (D.X k)) (P.θ * ε₀) -
          max (Constrained.targetResidual f c (D.t k) (D.X (k + 1))) (P.θ * ε₀)) :=
    Finset.sum_le_sum fun k hk => by
      rw [Finset.mem_Icc] at hk
      exact h.goodCount_mul_le hB hL hC hp hk.1 (hK.mono hk.2)
  rw [← Finset.sum_mul] at h1
  have hka : (D.kaCount f c P ε₀ K : ℝ) = ((Finset.Ico 1 K).filter (D.IsKa f c P ε₀)).card := by
    unfold Phase2Seq.kaCount; congr
  rw [goodBound_eq hL0 hp hε₀ h.tol.ε₁_pos, div_mul_eq_mul_div, le_div_iff₀ hδ, hka]
  linarith

include h in
/-- Every successful inner iteration except possibly the last one of its run is good: the
number of successful iterations of the `k`-th inner run is at most `|good_k| + 1`. -/
theorem succCount_le {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c C P ε₀ ε₁ k) :
    D.succCount f c p P k ≤ D.goodCount f c C p P ε₀ ε₁ k + 1 := by
  classical
  unfold Phase2Seq.succCount Phase2Seq.goodCount
  refine (Finset.card_le_card (t := insert (D.e k - 1)
    ((Finset.range (D.e k)).filter (D.IsGood f c C p P ε₀ ε₁ k))) ?_).trans
    (Finset.card_insert_le _ _)
  intro i hi
  rw [Finset.mem_filter, Finset.mem_range] at hi
  rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  by_cases hi1 : i + 1 < D.e k
  · right
    have hns := h.inner_not_stop hk1 hk hi1
    simp only [innerStop, not_or, not_le] at hns
    exact ⟨hi.1, hi.1, hi.2, not_le.2 hns.2.2, hns.1⟩
  · left; omega

include h in
/-- An outer iteration of `𝒦_b` whose new iterate fails the third test of (7.2.10) for the old
target contains a good inner iteration: its inner run moved (`f(x_{k+1}) < t_k ≤ f(x_k)`), and its
last successful iteration is good. -/
theorem one_le_goodCount_of_not_targetCrit {k : ℕ} (hk1 : 1 ≤ k)
    (hk : D.Before f c C P ε₀ ε₁ k) (hb : D.IsKb f c P ε₀ k)
    (hnc : ¬ targetCrit f c C ε₁ (D.t k) (D.X (k + 1))) :
    1 ≤ D.goodCount f c C p P ε₀ ε₁ k := by
  classical
  have hle : D.t k ≤ f (D.X k) := by
    have := (h.isTargetSequence hk).sub_target_nonneg hk1 le_rfl
    linarith
  have hne : D.xi k (D.e k) ≠ D.xi k 0 := by
    rw [← h.X_succ k hk1 hk, h.inner_zero k hk1 hk]
    intro heq
    have := hb.2
    rw [heq] at this
    linarith
  obtain ⟨s, hs, hsucc, hxs⟩ := (h.inner_run k hk1 hk).exists_last_succ (D.e k)
    (fun j hj => h.inner_not_stop hk1 hk hj) hne
  rw [← h.X_succ k hk1 hk] at hxs
  have hg : D.IsGood f c C p P ε₀ ε₁ k s :=
    ⟨hs, hsucc, by rw [hxs]; exact hnc, by rw [hxs]; exact hb.1⟩
  unfold Phase2Seq.goodCount
  exact Finset.card_pos.2 ⟨s, Finset.mem_filter.2 ⟨Finset.mem_range.2 hs, hg⟩⟩

include h in
/-- The new iterate of a bad outer iteration passes the third test of (7.2.10) for the old
target. -/
theorem isBad_targetCrit {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c C P ε₀ ε₁ k)
    (hbad : D.IsBad f c C p P ε₀ ε₁ k) : targetCrit f c C ε₁ (D.t k) (D.X (k + 1)) := by
  by_contra hnc
  have := h.one_le_goodCount_of_not_targetCrit hk1 hk hbad.1 hnc
  rw [hbad.2] at this
  exact absurd this (by norm_num)

omit h in
/-- The outer iterations: each `k ∈ [1, K)` is in `𝒦_a`, or bad, or contains a good inner
iteration, so `K ≤ |𝒦_a ∩ [1, K)| + |good iterations of [1, K]| + |bad ∩ [1, K)| + 1`. -/
theorem le_counts {K : ℕ} (hK : D.Before f c C P ε₀ ε₁ K) :
    K ≤ D.kaCount f c P ε₀ K + ∑ k ∈ Finset.Icc 1 K, D.goodCount f c C p P ε₀ ε₁ k +
      D.badCount f c C p P ε₀ ε₁ K + 1 := by
  classical
  have := Constrained.le_card_add_sum_of_cover (D.IsKa f c P ε₀) (D.IsBad f c C p P ε₀ ε₁)
    (D.goodCount f c C p P ε₀ ε₁) (K := K) fun k hk => by
      have hk' := Finset.mem_Ico.1 hk
      rcases Phase2Seq.isKa_or_isKb_of_not_stop (hK.not_stop hk'.1 hk'.2) with ha | hb
      · exact Or.inl ha
      · by_cases hbad : D.IsBad f c C p P ε₀ ε₁ k
        · exact Or.inr (Or.inl hbad)
        · exact Or.inr (Or.inr (Nat.one_le_iff_ne_zero.2 fun h0 => hbad ⟨hb, h0⟩))
  unfold Phase2Seq.kaCount Phase2Seq.badCount
  convert this

include h hB hL in
/-- Lemma 2.4.1 for one inner run (the regularization parameter restarts at `σ₀` in every run):
`e_k ≤ (1 + |log γ₁|/log γ₂) |successful iterations of run k| + log(σ_μ,max/σ₀)/log γ₂`. -/
theorem e_le (hC : Chapter06.AssumptionCNe C) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : D.Before f c C P ε₀ ε₁ k) :
    (D.e k : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * D.succCount f c p P k +
      Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂ := by
  classical
  have hlog := P.toARParams.log_γ₂_pos
  have hC₁ : 0 ≤ Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂ :=
    div_nonneg (Real.log_nonneg ((one_le_div P.σ₀_pos).2 (σ₀_le_arSigmaMax _ _))) hlog.le
  rcases hN : D.e k with _ | N
  · simp only [CharP.cast_eq_zero]
    have : 0 ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (D.succCount f c p P k : ℝ) := by
      positivity
    linarith
  · have hle : ∀ j ≤ N, ¬ IsARRun.Stop
        (fun i => innerStop f c C P.θ ε₀ ε₁ (D.t k) (D.xi k i)) (fun _ => False) j :=
      IsARRun.forall_le_not_stop_iff.2 fun j hj => h.inner_not_stop hk1 hk (by omega)
    have := (h.inner_run k hk1 hk).succ_count hle
      (h.inner_sigma_le hB hL hC hk1 hk (by omega)).2
    have hS : successSet (fun j => P.η₁ ≤
        taylorRatio (Constrained.targetMerit f c (D.t k)) p (D.xi k) (D.si k) j) N =
        (Finset.range (D.e k)).filter (D.InnerSucc f c p P k) := by
      rw [successSet_eq_filter, hN]; rfl
    rw [hS] at this
    unfold Phase2Seq.succCount
    push_cast
    linarith

end Counting2

end IsTPpGCPhase2

/-! ### Lemma 7.2.6 and the complexity of Phase 2 -/

section Complexity

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₁ : ℝⁿ} {D : Phase2Seq n} {flow fup Lμ : ℝ}

/-- **Lemma 7.2.6** of [cartis2022evaluation], **corrected**. Under C.CNe, f.B.Fb and a uniform
constant `L_μ` for f.DpL.C of `μ₂(·, t)`, `t ∈ [f_low - 1, f_up]` (Lemma 7.2.5), for every outer
iteration `K ≥ 1` reached by Phase 2:
(i) for each `k ∈ [1, K]`, the `k`-th inner run has at most `|good_k| + 1` successful iterations
and `e_k ≤ (1 + |log γ₁|/log γ₂) |successful_k| + log(σ_μ,max/σ₀)/log γ₂` (Lemma 2.4.1 per run,
the regularization parameter restarting at `σ₀`);
(ii) the number of good inner iterations of `[1, K]` is at most `G (|𝒦_a ∩ [1, K)| + 1)` with
`G = κ^S_ARpGC (1 - θ) ε₀^{(p-1)/p} ε₁^{-(p+1)/p}` (`goodBound`; the telescoping of (7.2.43)
across the blocks of outer iterations between consecutive elements of `𝒦_a`);
(iii) `K ≤ |𝒦_a ∩ [1, K)| + |good iterations of [1, K]| + |bad ∩ [1, K)| + 1`.
The book bounds `|𝓘_k^s|` by `G` per block: this fails as printed (it counts the `i = 0` elements
and the last iterations of runs that end on the third test of (7.2.10), which have no guaranteed
decrease), and the number of bad outer iterations of `𝒦_b` is not bounded by the printed
argument. -/
theorem lemma_7_2_6 (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D) (hC : Chapter06.AssumptionCNe C)
    (hp : 1 ≤ p) (hB : AssumptionBFb f c C P.β flow fup)
    (hL : ∀ t ∈ Icc (flow - 1) fup,
      Chapter06.AssumptionDpLC (Constrained.targetMerit f c t) C p Lμ)
    {K : ℕ} (hK1 : 1 ≤ K) (hK : D.Before f c C P ε₀ ε₁ K) :
    (∀ k, 1 ≤ k → k ≤ K →
      D.succCount f c p P k ≤ D.goodCount f c C p P ε₀ ε₁ k + 1 ∧
      (D.e k : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * D.succCount f c p P k +
        Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂) ∧
    (∑ k ∈ Finset.Icc 1 K, D.goodCount f c C p P ε₀ ε₁ k : ℝ) ≤
      goodBound P Lμ p ε₀ ε₁ * (D.kaCount f c P ε₀ K + 1) ∧
    K ≤ D.kaCount f c P ε₀ K + ∑ k ∈ Finset.Icc 1 K, D.goodCount f c C p P ε₀ ε₁ k +
      D.badCount f c C p P ε₀ ε₁ K + 1 :=
  ⟨fun _ hk1 hkK => ⟨h.succCount_le hk1 (hK.mono hkK), h.e_le hB hL hC hk1 (hK.mono hkK)⟩,
    h.sum_goodCount_le hB hL hC hp hK1 hK, IsTPpGCPhase2.le_counts (p := p) hK⟩

private theorem goodBound_nonneg {P : TPpGCParams} {Lμ ε₀ ε₁ : ℝ} (hL : 0 ≤ Lμ) {p : ℕ}
    (hp : 1 ≤ p) (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) : 0 ≤ goodBound P Lμ p ε₀ ε₁ := by
  rw [goodBound_eq hL hp hε₀ hε₁]
  have := goodDecr_pos (P := P) hL p hε₀ hε₁
  have := P.θ_lt_one
  have : 0 ≤ 1 - P.θ := by linarith
  positivity

/-- **Theorem 7.2.7** of [cartis2022evaluation], Phase 2, **corrected**. Under C.CNe, f.B.Fb and
a uniform constant `L_μ` (Lemma 7.2.5), let `N_a = (f_up - f_low + 1)/((1 - θ)ε₀)` (Lemma 7.2.4),
`G = goodBound` (Lemma 7.2.6), `A₁ = 1 + |log γ₁|/log γ₂`, `C₁ = log(σ_μ,max/σ₀)/log γ₂`. For
every Phase-2 run of TPp-GC:
(i) every outer iteration `K ≥ 1` reached satisfies `K ≤ (N_a + 1)(G + 1) + n_bad(K)`, where
`n_bad(K)` is the number of bad iterations (`Phase2Seq.IsBad`) in `[1, K)`;
(ii) if the number of bad iterations is bounded by `M`, Phase 2 terminates, at an outer iteration
`k_ε ≤ (N_a + 1)(G + 1) + M` (its output then satisfies Lemma 7.2.1, `lemma_7_2_1_phase2`);
(iii) if Phase 2 terminates at `k_ε`, it uses at most `1 + G (N_a + 1) + k_ε` evaluations of the
derivatives and at most `1 + A₁ (G (N_a + 1) + k_ε) + C₁ k_ε` evaluations of `(f, c)`.
With `M` independent of `ε` both counts are `O(max(ε₀^{-1}, ε₀^{-1/p} ε₁^{-(p+1)/p}))`, the order
of (7.2.50); the book's unconditional termination claim rests on the gap of Lemma 7.2.6. -/
theorem theorem_7_2_7_phase2 (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
    (hC : Chapter06.AssumptionCNe C) (hp : 1 ≤ p) (hB : AssumptionBFb f c C P.β flow fup)
    (hL : ∀ t ∈ Icc (flow - 1) fup,
      Chapter06.AssumptionDpLC (Constrained.targetMerit f c t) C p Lμ) :
    (∀ K, 1 ≤ K → D.Before f c C P ε₀ ε₁ K →
      (K : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) * (goodBound P Lμ p ε₀ ε₁ + 1) +
        D.badCount f c C p P ε₀ ε₁ K) ∧
    (∀ M : ℝ, (∀ K, D.Before f c C P ε₀ ε₁ K → (D.badCount f c C p P ε₀ ε₁ K : ℝ) ≤ M) →
      ∃ kε, D.IsEnd f c C P ε₀ ε₁ kε ∧
        (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) * (goodBound P Lμ p ε₀ ε₁ + 1) +
          M) ∧
    (∀ kε, D.IsEnd f c C P ε₀ ε₁ kε →
      (D.derivEvals f c p P kε : ℝ) ≤
        1 + goodBound P Lμ p ε₀ ε₁ * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε ∧
      (D.funEvals kε : ℝ) ≤
        1 + (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          (goodBound P Lμ p ε₀ ε₁ * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε) +
          Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂ * kε) := by
  classical
  set Na := (fup - flow + 1) / ((1 - P.θ) * ε₀)
  set G := goodBound P Lμ p ε₀ ε₁
  have hε₀ := h.tol.ε₀_pos
  have hL0 : 0 ≤ Lμ := (hL _ (h.t_mem hB le_rfl Phase2Seq.before_one)).nonneg
  have hG : 0 ≤ G := goodBound_nonneg hL0 hp hε₀ h.tol.ε₁_pos
  -- the bound on the number of outer iterations
  have hgood : ∀ K, 1 ≤ K → D.Before f c C P ε₀ ε₁ K →
      (∑ k ∈ Finset.Icc 1 K, D.goodCount f c C p P ε₀ ε₁ k : ℝ) ≤ G * (Na + 1) := by
    intro K hK1 hK
    have h1 := h.sum_goodCount_le hB hL hC hp hK1 hK
    have h2 : (D.kaCount f c P ε₀ K : ℝ) ≤ Na := by
      have := lemma_7_2_4 h hB hK1 hK
      unfold Phase2Seq.kaCount
      convert this
    exact h1.trans (by gcongr)
  have hi : ∀ K, 1 ≤ K → D.Before f c C P ε₀ ε₁ K →
      (K : ℝ) ≤ (Na + 1) * (G + 1) + D.badCount f c C p P ε₀ ε₁ K := by
    intro K hK1 hK
    have h1 : (K : ℝ) ≤ D.kaCount f c P ε₀ K +
        (∑ k ∈ Finset.Icc 1 K, D.goodCount f c C p P ε₀ ε₁ k : ℝ) +
        D.badCount f c C p P ε₀ ε₁ K + 1 := by exact_mod_cast IsTPpGCPhase2.le_counts (p := p) hK
    have h2 : (D.kaCount f c P ε₀ K : ℝ) ≤ Na := by
      have := lemma_7_2_4 h hB hK1 hK
      unfold Phase2Seq.kaCount
      convert this
    have h3 := hgood K hK1 hK
    nlinarith
  refine ⟨hi, fun M hM => ?_, fun kε hend => ?_⟩
  · -- termination when the number of bad iterations is bounded
    by_contra hno
    have hall : ∀ K, D.Before f c C P ε₀ ε₁ K := by
      intro K
      induction K with
      | zero => exact fun _ _ hj => absurd hj (Nat.not_lt_zero _)
      | succ K ih =>
        refine ih.succ fun hK1 hstop => ?_
        have hb := hi K hK1 ih
        exact hno ⟨K, ⟨hK1, hstop, ih⟩, hb.trans (by linarith [hM K ih])⟩
    set K := ⌈(Na + 1) * (G + 1) + M⌉₊ + 1
    have h1 := hi K (by omega) (hall K)
    have h2 := hM K (hall K)
    have h3 : (Na + 1) * (G + 1) + M < K := by
      have := Nat.le_ceil ((Na + 1) * (G + 1) + M)
      push_cast [K]
      linarith
    linarith
  · -- evaluation counts
    obtain ⟨hk1, -, hbef⟩ := hend
    have hgood' := hgood kε hk1 hbef
    have hsucc : (∑ k ∈ Finset.Icc 1 kε, D.succCount f c p P k : ℝ) ≤
        ∑ k ∈ Finset.Icc 1 kε, (D.goodCount f c C p P ε₀ ε₁ k : ℝ) + kε := by
      have : ∑ k ∈ Finset.Icc 1 kε, D.succCount f c p P k ≤
          ∑ k ∈ Finset.Icc 1 kε, (D.goodCount f c C p P ε₀ ε₁ k + 1) :=
        Finset.sum_le_sum fun k hk => by
          rw [Finset.mem_Icc] at hk
          exact h.succCount_le hk.1 (hbef.mono hk.2)
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one,
        Nat.add_sub_cancel] at this
      exact_mod_cast this
    have hD : (D.derivEvals f c p P kε : ℝ) =
        1 + ∑ k ∈ Finset.Icc 1 kε, (D.succCount f c p P k : ℝ) := by
      unfold Phase2Seq.derivEvals Phase2Seq.succCount
      push_cast
      rfl
    have hA : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ := by
      have := P.toARParams.log_γ₂_pos; positivity
    have hF : (D.funEvals kε : ℝ) ≤ 1 + ∑ k ∈ Finset.Icc 1 kε,
        ((1 + |Real.log P.γ₁| / Real.log P.γ₂) * D.succCount f c p P k +
          Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂) := by
      unfold Phase2Seq.funEvals
      push_cast
      gcongr with k hk
      rw [Finset.mem_Icc] at hk
      exact h.e_le hB hL hC hk.1 (hbef.mono hk.2)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul] at hF
    refine ⟨by rw [hD]; linarith, hF.trans ?_⟩
    have : (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
        ∑ k ∈ Finset.Icc 1 kε, (D.succCount f c p P k : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (G * (Na + 1) + kε) :=
      mul_le_mul_of_nonneg_left (hsucc.trans (by linarith)) hA
    linarith

end Complexity

/-! ### Existence of Phase 2 -/

section Existence

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}

/-- The inner runs of Phase 2 exist and terminate ([cartis2022evaluation], Step 1 of Phase 2 of
Algorithm 7.2.1): under C.CNe and μ₂.DpL.C (`p ≥ 1`), from every `y ∈ 𝒞` and for every target
`τ` there is an ARp1-CC run on `μ₂(·, τ)` with the termination test (7.2.10), and it reaches the
test, at a point of `𝒞`. (A failing test gives `ω_{μ₂,𝒞,1} > ε₁ θ ε₀ > 0`, so a model minimizer
over `𝒞(x)` is an admissible step, and each successful iteration decreases `μ₂(·, τ) ≥ 0` by at
least `κ₁ (ε₁ θ ε₀)^{(p+1)/p}`, as in Theorem 6.2.5.) -/
theorem exists_innerRun (hC : Chapter06.AssumptionCNe C) (hμ : AssumptionMu2DpLC f c C p)
    (hp : 1 ≤ p) (htol : TPpGCTol P ε₀ ε₁) (τ : ℝ) {y : ℝⁿ} (hy : y ∈ C) :
    ∃ (xs ss : ℕ → ℝⁿ) (σs : ℕ → ℝ) (e : ℕ), xs 0 = y ∧
      IsARRun P.toARParams (fun i => innerStop f c C P.θ ε₀ ε₁ τ (xs i))
        (fun i => IsFirstOrderCCStep (Constrained.targetMerit f c τ) C p P.θ₁ (xs i) (σs i)
          (ss i)) (fun _ => False)
        (taylorRatio (Constrained.targetMerit f c τ) p xs ss) xs ss σs ∧
      IsFirstHit (fun i => innerStop f c C P.θ ε₀ ε₁ τ (xs i)) e ∧ xs e ∈ C := by
  obtain ⟨L, hdpl⟩ := hμ τ
  set μ := Constrained.targetMerit f c τ
  have hε₀ := htol.ε₀_pos
  have hε₁ := htol.ε₁_pos
  have hθ := P.θ_pos
  -- a failing test gives a large first-order measure
  have hbig : ∀ z, ¬ innerStop f c C P.θ ε₀ ε₁ τ z →
      ε₁ * (P.θ * ε₀) < Chapter06.omega1 μ C z := by
    intro z hz
    simp only [innerStop, not_or, not_le] at hz
    exact lt_of_le_of_lt (by gcongr; exact hz.1.le) hz.2.2
  obtain ⟨xs, ss, σs, hx0, hrun, hinv⟩ := exists_isARRun P.toARParams (Inv := (· ∈ C))
    (test := innerStop f c C P.θ ε₀ ε₁ τ) (stepOK := IsFirstOrderCCStep μ C p P.θ₁)
    (fun z _ t => reductionRatio μ z t ((ftaylorSeries ℝ μ z).taylorDecrement p t))
    (fun z σ hz _ hσ ht => by
      obtain ⟨s, -, hs, -⟩ := exists_isFirstOrderCCStep (θ := P.θ₁) hC.isClosed hC.convex hz
        (hdpl.contDiffAt z hz) hp hσ P.θ₁_pos.le
        ((by positivity : (0 : ℝ) < ε₁ * (P.θ * ε₀)).trans (hbig z ht))
      exact ⟨s, hs, hs.mem⟩) hy
  -- termination, as in Theorem 6.2.5
  have hσ : ∀ k, (∀ j < k, ¬ IsARRun.Stop (fun i => innerStop f c C P.θ ε₀ ε₁ τ (xs i))
      (fun _ => False) j) → xs k ∈ C ∧ P.σmin ≤ σs k ∧ σs k ≤ P.toARpCCParams.sigmaMax L :=
    fun k hk => Chapter06.arpcc_sigma_le (P := P.toARpCCParams) hrun hC hdpl (hx0 ▸ hy)
      (fun _ hs => ⟨hs.mem, hs.decrease⟩) k (IsARRun.forall_lt_not_stop_iff.1 hk)
  have hκ := Chapter06.kappa1CC_pos (P := P.toARpCCParams) (p := p) hdpl.nonneg
  have he : 0 < ((p : ℝ) + 1) / p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    positivity
  obtain ⟨e, he, -, -⟩ := hrun.exists_isFirstHit_of_decrease (σmax := P.toARpCCParams.sigmaMax L)
    (V := fun i => μ (xs i)) (Vlow := 0)
    (δ := Chapter06.kappa1CC P.toARpCCParams L p * (ε₁ * (P.θ * ε₀)) ^ (((p : ℝ) + 1) / p))
    (fun k hk => (hσ k hk).2.2) (by positivity)
    (fun k hk => (hrun.accept k hk).le (w := μ) rfl (by
      have := P.σmin_nonneg.trans (hσ k fun j hj => hk j hj.le).2.1
      exact lt_of_le_of_lt (by positivity) (lt_taylorDecrement_of_regularizedModel_lt
        (hrun.step_of_forall_le hk).decrease)))
    (fun k _ => Constrained.targetMerit_nonneg)
    (fun k hk hs => by
      have hk' : ∀ j ≤ k, ¬ IsARRun.Stop (fun i => innerStop f c C P.θ ε₀ ε₁ τ (xs i))
          (fun _ => False) j := fun j hj => hk j (hj.trans k.le_succ)
      obtain ⟨hxk, hmin, hmax⟩ := hσ k fun j hj => hk' j hj.le
      have hstep : IsFirstOrderCCStep μ C p P.θ₁ (xs k) (σs k) (ss k) :=
        hrun.step_of_forall_le hk'
      have hdec := hstep.sub_ge hC.convex hdpl.contDiffAt hdpl.lipschitz hdpl.nonneg hxk hp
        P.θ₁_pos.le P.σmin_nonneg hmin hmax P.η₁_pos hs
      rw [← hrun.eq_add_of_succ hk' hs] at hdec
      have hω := hbig _ (fun h' => hk (k + 1) le_rfl (Or.inl h'))
      refine le_trans ?_ hdec
      rw [Chapter06.kappa1CC]
      gcongr
      exact hω.le)
  have he' : IsFirstHit (fun i => innerStop f c C P.θ ε₀ ε₁ τ (xs i)) e :=
    ⟨he.1.resolve_right id, fun j hj h' => he.2 j hj (Or.inl h')⟩
  exact ⟨xs, ss, σs, e, hx0, hrun, he', hinv e he'.2⟩

/-- **Existence of Phase 2** of Algorithm 7.2.1 of [cartis2022evaluation]: under C.CNe and
μ₂.DpL.C (`p ≥ 1`), with the tolerances (7.2.8), from every `x₁ ∈ 𝒞` with `‖c(x₁)‖ ≤ θε₀`
there are sequences forming a Phase-2 run (the outer sequence is built recursively from the inner
runs of `exists_innerRun`). -/
theorem exists_phase2 (hC : Chapter06.AssumptionCNe C) (hμ : AssumptionMu2DpLC f c C p)
    (hp : 1 ≤ p) (htol : TPpGCTol P ε₀ ε₁) {x₁ : ℝⁿ} (hx₁ : x₁ ∈ C)
    (hc₁ : ‖c x₁‖ ≤ P.θ * ε₀) : ∃ D : Phase2Seq n, IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D := by
  classical
  have hin : ∀ (y : ℝⁿ) (τ : ℝ), y ∈ C → ∃ r : (ℕ → ℝⁿ) × (ℕ → ℝⁿ) × (ℕ → ℝ) × ℕ,
      r.1 0 = y ∧
      IsARRun P.toARParams (fun i => innerStop f c C P.θ ε₀ ε₁ τ (r.1 i))
        (fun i => IsFirstOrderCCStep (Constrained.targetMerit f c τ) C p P.θ₁ (r.1 i)
          (r.2.2.1 i) (r.2.1 i)) (fun _ => False)
        (taylorRatio (Constrained.targetMerit f c τ) p r.1 r.2.1) r.1 r.2.1 r.2.2.1 ∧
      IsFirstHit (fun i => innerStop f c C P.θ ε₀ ε₁ τ (r.1 i)) r.2.2.2 ∧ r.1 r.2.2.2 ∈ C := by
    intro y τ hy
    obtain ⟨xs, ss, σs, e, h0, hr, he, hm⟩ := exists_innerRun hC hμ hp htol τ hy
    exact ⟨(xs, ss, σs, e), h0, hr, he, hm⟩
  choose! R hR using hin
  -- one outer iteration: the inner run, then the target update
  let next : ℝⁿ × ℝ → ℝⁿ × ℝ := fun st =>
    ((R st.1 st.2).1 (R st.1 st.2).2.2.2,
      if Constrained.targetResidual f c st.2 ((R st.1 st.2).1 (R st.1 st.2).2.2.2) ≤ P.θ * ε₀
      then f ((R st.1 st.2).1 (R st.1 st.2).2.2.2) -
        √(ε₀ ^ 2 - ‖c ((R st.1 st.2).1 (R st.1 st.2).2.2.2)‖ ^ 2)
      else 2 * f ((R st.1 st.2).1 (R st.1 st.2).2.2.2) - st.2)
  let S : ℕ → ℝⁿ × ℝ := fun j => Nat.rec (x₁, f x₁ - √(ε₀ ^ 2 - ‖c x₁‖ ^ 2))
    (fun _ st => next st) j
  have hS : ∀ j, S (j + 1) = next (S j) := fun _ => rfl
  have hmem : ∀ j, (S j).1 ∈ C := by
    intro j
    induction j with
    | zero => exact hx₁
    | succ j ih => rw [hS]; exact (hR _ _ ih).2.2.2
  let D : Phase2Seq n :=
    { X := fun k => (S (k - 1)).1
      t := fun k => (S (k - 1)).2
      xi := fun k => (R (S (k - 1)).1 (S (k - 1)).2).1
      si := fun k => (R (S (k - 1)).1 (S (k - 1)).2).2.1
      σi := fun k => (R (S (k - 1)).1 (S (k - 1)).2).2.2.1
      e := fun k => (R (S (k - 1)).1 (S (k - 1)).2).2.2.2 }
  have hX : ∀ k, 1 ≤ k → D.X (k + 1) = D.xi k (D.e k) := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rfl
  have ht : ∀ k, 1 ≤ k → D.t (k + 1) =
      if Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ≤ P.θ * ε₀
      then f (D.X (k + 1)) - √(ε₀ ^ 2 - ‖c (D.X (k + 1))‖ ^ 2)
      else 2 * f (D.X (k + 1)) - D.t k := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rfl
  refine ⟨D, htol, hx₁, hc₁, rfl, rfl, fun k _ _ => (hR _ _ (hmem _)).1,
    fun k _ _ => (hR _ _ (hmem _)).2.1, fun k _ _ => (hR _ _ (hmem _)).2.2.1,
    fun k hk _ => hX k hk, fun k hk _ ha => ?_, fun k hk _ hb => ?_⟩
  · rw [ht k hk, ite_eq_left (show Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ≤
      P.θ * ε₀ from ha)]
  · rw [ht k hk, ite_eq_right (show ¬ Constrained.targetResidual f c (D.t k) (D.X (k + 1)) ≤
      P.θ * ε₀ from hb.not_isKa)]

end Existence

/-! ### The whole algorithm -/

section Whole

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p ℓ : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₀ : ℝⁿ} {y s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {k₁ : ℕ} {D : Phase2Seq n}

/-- **Algorithm 7.2.1** (TPp-GC) of [cartis2022evaluation], a whole run. Phase 1 is an ARpLE-CC
run (Algorithm 6.3.1) on the constraint residual `c` from `x₀ ∈ 𝒞` with tolerances `(θε₀, ε₁)`,
stopped at the first index `k₁` at which (7.2.9) holds; `x₁ = y_{k₁}`. If `‖c(x₁)‖ > θε₀` the
algorithm terminates with `x_ε = x₁`; otherwise Phase 2 (`IsTPpGCPhase2`) is run from `x₁`. The
evaluation counts of Phase 1 are `funEvalCount k₁` and `derivEvalCount` of its successful
iterations, those of Phase 2 `Phase2Seq.funEvals` and `Phase2Seq.derivEvals`. -/
structure algorithm_7_2_1 (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (C : Set ℝⁿ) (p ℓ : ℕ) (P : TPpGCParams)
    (ε₀ ε₁ : ℝ) (x₀ : ℝⁿ) (y s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (k₁ : ℕ) (D : Phase2Seq n) : Prop where
  /-- The tolerances (7.2.8). -/
  tol : TPpGCTol P ε₀ ε₁
  /-- Phase 1 starts at `x₀`. -/
  start : y 0 = x₀
  /-- Phase 1: ARpLE-CC on `c` with the test (7.2.9). -/
  phase1 : Chapter06.algorithm_6_3_1 c ℓ C p P.toARpCCParams (P.θ * ε₀) ε₁ y s σ
  /-- Phase 1 stops at `k₁`, the first index at which (7.2.9) holds, i.e. at which the
  ARpLE-CC test `Chapter06.stopLE c ℓ C (θε₀) ε₁` holds; `x₁ = y_{k₁}`. -/
  phase1_hit : IsFirstHit (fun k => Chapter06.stopLE c ℓ C (P.θ * ε₀) ε₁ (y k)) k₁
  /-- Phase 2 is run from `x₁ = y_{k₁}` when `‖c(x₁)‖ ≤ θε₀`. -/
  phase2 : ‖c (y k₁)‖ ≤ P.θ * ε₀ → IsTPpGCPhase2 f c C p P ε₀ ε₁ (y k₁) D

/-- The output `x₁` of Phase 1 lies in `𝒞`. -/
theorem algorithm_7_2_1.mem_phase1 (h : algorithm_7_2_1 f c C p ℓ P ε₀ ε₁ x₀ y s σ k₁ D) :
    y k₁ ∈ C :=
  h.phase1.mem h.phase1_hit.2

/-- **Existence of TPp-GC runs** ([cartis2022evaluation], Algorithm 7.2.1): under C.CNe, Φℓ.DpL.C
for `c` (with `p ≥ 1`, `ℓ ≥ 2` and `ι₁(p, ℓ, i) ≥ 0` for some `i`), μ₂.DpL.C and the tolerances
(7.2.8), from every `x₀ ∈ 𝒞` there is a run: Phase 1 exists (`Chapter06.algorithm_6_3_1.exists_run`)
and terminates (`Chapter06.theorem_6_3_1`), and Phase 2 exists (`exists_phase2`). -/
theorem algorithm_7_2_1_exists (hC : Chapter06.AssumptionCNe C) (hx₀ : x₀ ∈ C) (hp : 1 ≤ p)
    (hℓ : 2 ≤ ℓ) {i : ℕ} (hι : 0 ≤ ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p) {LΦ : ℝ}
    (hΦ : Chapter06.AssumptionPhiDpLC c ℓ C p LΦ) (hμ : AssumptionMu2DpLC f c C p)
    (htol : TPpGCTol P ε₀ ε₁) :
    ∃ (y s : ℕ → ℝⁿ) (σ : ℕ → ℝ) (k₁ : ℕ) (D : Phase2Seq n),
      algorithm_7_2_1 f c C p ℓ P ε₀ ε₁ x₀ y s σ k₁ D := by
  obtain ⟨y, s, σ, hy0, hrun⟩ := Chapter06.algorithm_6_3_1.exists_run (r := c) (ℓ := ℓ)
    (ε₀ := P.θ * ε₀) P.toARpCCParams hC hΦ.contDiffAt hp htol.ε₁_pos.le hx₀
  obtain ⟨k₁, hk₁, -, -⟩ := Chapter06.theorem_6_3_1 hp hℓ hι (β := 1 / 2) (by norm_num)
    (by norm_num) hC hΦ hrun (mul_pos P.θ_pos htol.ε₀_pos) htol.ε₁_pos
  have hmem : y k₁ ∈ C := hrun.mem hk₁.2
  by_cases hc : ‖c (y k₁)‖ ≤ P.θ * ε₀
  · obtain ⟨D, hD⟩ := exists_phase2 hC hμ hp htol hmem hc
    exact ⟨y, s, σ, k₁, D, htol, hy0, hrun, hk₁, fun _ => hD⟩
  · exact ⟨y, s, σ, k₁, ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
      fun _ => 0⟩, htol, hy0, hrun, hk₁, fun h' => absurd h' hc⟩

/-- **Lemma 7.2.1** of [cartis2022evaluation] for the whole algorithm (`f`, `c` differentiable
at the points of `𝒞`): if TPp-GC stops in Phase 1 (`‖c(x₁)‖ > θε₀`), then `x_ε = x₁ ∈ 𝒞`
satisfies (7.2.14), `ω_{Φ_ℓ,𝒞,1}(x_ε) ≤ ε₁ ‖c(x_ε)‖^{ℓ-1}` and `‖c(x_ε)‖ > θε₀`; if it enters
Phase 2 and Phase 2 stops at outer iteration `k_ε`, then `x_ε = x_{k_ε+1}` satisfies (7.2.15) or
(7.2.16) (`lemma_7_2_1_phase2`, with `Φ₂ = ½ ‖c‖²`). -/
theorem lemma_7_2_1 (h : algorithm_7_2_1 f c C p ℓ P ε₀ ε₁ x₀ y s σ k₁ D)
    (hf : ∀ x ∈ C, DifferentiableAt ℝ f x) (hc : ∀ x ∈ C, DifferentiableAt ℝ c x) :
    (P.θ * ε₀ < ‖c (y k₁)‖ → y k₁ ∈ C ∧
      Chapter06.omega1 (Chapter06.PhiEll c ℓ) C (y k₁) ≤ ε₁ * ‖c (y k₁)‖ ^ (ℓ - 1)) ∧
    (‖c (y k₁)‖ ≤ P.θ * ε₀ → ∀ kε, D.IsEnd f c C P ε₀ ε₁ kε →
      (f (D.X (kε + 1)) = D.targetOut f c P ε₀ kε ∧
          Chapter06.omega1 (fun z => ‖c z‖ ^ 2 / 2) C (D.X (kε + 1)) ≤
            ε₁ * ‖c (D.X (kε + 1))‖ ∧
          P.θ * ε₀ < ‖c (D.X (kε + 1))‖) ∨
        (D.targetOut f c P ε₀ kε < f (D.X (kε + 1)) ∧
          IsApproxFirstOrderGC f c C ε₀ ε₁ (D.X (kε + 1))
            (Constrained.targetMultiplier f c (D.targetOut f c P ε₀ kε) (D.X (kε + 1))))) := by
  refine ⟨fun hgt => ⟨h.mem_phase1, ?_⟩, fun hle kε hend =>
    lemma_7_2_1_phase2 (h.phase2 hle) hf hc hend⟩
  rcases h.phase1_hit.1 with h' | h'
  · exact absurd h' (not_le.2 hgt)
  · exact h'

/-- **Lemma 7.2.2** of [cartis2022evaluation] (Phase 1): under C.CNe and Φℓ.DpL.C for `c`, with
`p ≥ 1`, `ℓ ≥ 2`, `ι₁(p, ℓ, i) ≥ 0` and the analysis constant `β ∈ (0, 1)` of Theorem 6.3.1,
Phase 1 stops at `x₁ = y_{k₁}` with `‖c(x₁)‖ ≤ θε₀` or `ω_{Φ_ℓ,𝒞,1}(x₁) ≤ ε₁ ‖c(x₁)‖^{ℓ-1}`
(7.2.9) after at most
`κ^A max[‖c(x₀)‖^{1/2^i}, ‖c(x₀)‖^{1-(ℓ-1)/p}] / min[(θε₀)^{1/2^i}, ε₁^{(p+1)/p}] + κ^C`
evaluations of `c` (7.2.23) and `κ^S (same ratio) + 2` evaluations of its derivatives (7.2.24;
the printed bound lacks the `+ 2` of Theorem 6.3.1), with the constants of Theorem 6.3.1. -/
theorem lemma_7_2_2 (h : algorithm_7_2_1 f c C p ℓ P ε₀ ε₁ x₀ y s σ k₁ D)
    (hC : Chapter06.AssumptionCNe C) (hp : 1 ≤ p) (hℓ : 2 ≤ ℓ) {i : ℕ}
    (hι : 0 ≤ ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {LΦ : ℝ} (hΦ : Chapter06.AssumptionPhiDpLC c ℓ C p LΦ) :
    (‖c (y k₁)‖ ≤ P.θ * ε₀ ∨
      Chapter06.omega1 (Chapter06.PhiEll c ℓ) C (y k₁) ≤ ε₁ * ‖c (y k₁)‖ ^ (ℓ - 1)) ∧
    (funEvalCount k₁ : ℝ) ≤
        max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) *
              Chapter06.kappaSARp1CC P.toARpCCParams LΦ p) *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          max (‖c (x₀)‖ ^ (1 / 2 ^ i : ℝ)) (‖c (x₀)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)) /
          min ((P.θ * ε₀) ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) +
        ((|Real.log P.γ₁| + Real.log (P.toARpCCParams.sigmaMax LΦ / P.σ₀)) / Real.log P.γ₂ + 2) ∧
    (derivEvalCount (fun k => P.η₁ ≤ taylorRatio (Chapter06.PhiEll c ℓ) p y s k) k₁ : ℝ) ≤
        max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) *
              Chapter06.kappaSARp1CC P.toARpCCParams LΦ p) *
          max (‖c (x₀)‖ ^ (1 / 2 ^ i : ℝ)) (‖c (x₀)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)) /
          min ((P.θ * ε₀) ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) + 2 := by
  obtain ⟨kε, hkε, hF, hD⟩ := Chapter06.theorem_6_3_1 hp hℓ hι hβ0 hβ1 hC hΦ h.phase1
    (mul_pos P.θ_pos h.tol.ε₀_pos) h.tol.ε₁_pos
  rw [hkε.unique h.phase1_hit, h.start] at *
  exact ⟨h.phase1_hit.1, hF, hD⟩

end Whole

/-! ### Theorem 7.2.7 under the book's hypotheses -/

section BookHypotheses

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {C : Set ℝⁿ} {p : ℕ} {P : TPpGCParams} {ε₀ ε₁ : ℝ}
  {x₁ : ℝⁿ} {D : Phase2Seq n} {flow fup : ℝ}

/-- **Lemma 7.2.6** of [cartis2022evaluation] under the book's hypotheses μ₂.DpL.C and f.B.Fb
(`p ≥ 1`): the uniform Lipschitz constant `L_μ` of `lemma_7_2_6` exists by Lemma 7.2.5 on
`[f_low - 1, f_up]`. -/
theorem lemma_7_2_6_of_mu2 (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
    (hC : Chapter06.AssumptionCNe C) (hp : 1 ≤ p) (hB : AssumptionBFb f c C P.β flow fup)
    (hμ : AssumptionMu2DpLC f c C p) :
    ∃ Lμ, 0 ≤ Lμ ∧ ∀ K, 1 ≤ K → D.Before f c C P ε₀ ε₁ K →
      (∀ k, 1 ≤ k → k ≤ K →
        D.succCount f c p P k ≤ D.goodCount f c C p P ε₀ ε₁ k + 1 ∧
        (D.e k : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * D.succCount f c p P k +
          Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂) ∧
      (∑ k ∈ Finset.Icc 1 K, D.goodCount f c C p P ε₀ ε₁ k : ℝ) ≤
        goodBound P Lμ p ε₀ ε₁ * (D.kaCount f c P ε₀ K + 1) ∧
      K ≤ D.kaCount f c P ε₀ K + ∑ k ∈ Finset.Icc 1 K, D.goodCount f c C p P ε₀ ε₁ k +
        D.badCount f c C p P ε₀ ε₁ K + 1 := by
  obtain ⟨Lμ, hL0, hL⟩ := lemma_7_2_5 hμ hp (flow - 1) fup
  exact ⟨Lμ, hL0, fun _ hK1 hK => lemma_7_2_6 h hC hp hB hL hK1 hK⟩

/-- **Theorem 7.2.7** of [cartis2022evaluation], Phase 2, under the book's hypotheses μ₂.DpL.C
and f.B.Fb (`p ≥ 1`): the conclusions of `theorem_7_2_7_phase2` hold with the uniform Lipschitz
constant `L_μ` given by Lemma 7.2.5 on `[f_low - 1, f_up]`. -/
theorem theorem_7_2_7_phase2_of_mu2 (h : IsTPpGCPhase2 f c C p P ε₀ ε₁ x₁ D)
    (hC : Chapter06.AssumptionCNe C) (hp : 1 ≤ p) (hB : AssumptionBFb f c C P.β flow fup)
    (hμ : AssumptionMu2DpLC f c C p) :
    ∃ Lμ, 0 ≤ Lμ ∧
      (∀ K, 1 ≤ K → D.Before f c C P ε₀ ε₁ K →
        (K : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) * (goodBound P Lμ p ε₀ ε₁ + 1) +
          D.badCount f c C p P ε₀ ε₁ K) ∧
      (∀ M : ℝ, (∀ K, D.Before f c C P ε₀ ε₁ K → (D.badCount f c C p P ε₀ ε₁ K : ℝ) ≤ M) →
        ∃ kε, D.IsEnd f c C P ε₀ ε₁ kε ∧
          (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) * (goodBound P Lμ p ε₀ ε₁ + 1) +
            M) ∧
      (∀ kε, D.IsEnd f c C P ε₀ ε₁ kε →
        (D.derivEvals f c p P kε : ℝ) ≤
          1 + goodBound P Lμ p ε₀ ε₁ * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε ∧
        (D.funEvals kε : ℝ) ≤
          1 + (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
            (goodBound P Lμ p ε₀ ε₁ * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε) +
            Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂ * kε) := by
  obtain ⟨Lμ, hL0, hL⟩ := lemma_7_2_5 hμ hp (flow - 1) fup
  exact ⟨Lμ, hL0, theorem_7_2_7_phase2 h hC hp hB hL⟩


/-- **Theorem 7.2.7** of [cartis2022evaluation], whole algorithm, **corrected**. Under C.CNe,
Φℓ.DpL.C for `c` (`p ≥ 1`, `ℓ ≥ 2`, `ι₁(p, ℓ, i) ≥ 0`, analysis constant `β ∈ (0, 1)`),
μ₂.DpL.C and f.B.Fb: Phase 1 terminates within the bounds (7.2.23)–(7.2.24) of Lemma 7.2.2, with
(7.2.14) if it stops the algorithm (`lemma_7_2_1`); if Phase 2 is entered, it satisfies the
conclusions of `theorem_7_2_7_phase2` for the constant `L_μ` of Lemma 7.2.5 (its output satisfies
Lemma 7.2.1 when it terminates). The total counts are the sums of the two phases. When the number
of bad iterations of `𝒦_b` is bounded independently of `ε`, the totals are
`O(max[ε₀^{-1/2^i}, ε₀^{-1}, ε₀^{-1/p} ε₁^{-(p+1)/p}])`; the book's unconditional (7.2.50)–(7.2.51)
rest on the gap of Lemma 7.2.6. -/
theorem theorem_7_2_7 {ℓ : ℕ} {x₀ : ℝⁿ} {y s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {k₁ : ℕ}
    (h : algorithm_7_2_1 f c C p ℓ P ε₀ ε₁ x₀ y s σ k₁ D) (hC : Chapter06.AssumptionCNe C)
    (hp : 1 ≤ p) (hℓ : 2 ≤ ℓ) {i : ℕ} (hι : 0 ≤ ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) / p)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {LΦ : ℝ} (hΦ : Chapter06.AssumptionPhiDpLC c ℓ C p LΦ)
    (hμ : AssumptionMu2DpLC f c C p) {flow fup : ℝ} (hB : AssumptionBFb f c C P.β flow fup) :
    ((funEvalCount k₁ : ℝ) ≤
        max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) *
              Chapter06.kappaSARp1CC P.toARpCCParams LΦ p) *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          max (‖c (x₀)‖ ^ (1 / 2 ^ i : ℝ)) (‖c (x₀)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)) /
          min ((P.θ * ε₀) ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) +
        ((|Real.log P.γ₁| + Real.log (P.toARpCCParams.sigmaMax LΦ / P.σ₀)) / Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio (Chapter06.PhiEll c ℓ) p y s k) k₁ : ℝ) ≤
        max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (2 ^ i / β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) *
              Chapter06.kappaSARp1CC P.toARpCCParams LΦ p) *
          max (‖c (x₀)‖ ^ (1 / 2 ^ i : ℝ)) (‖c (x₀)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)) /
          min ((P.θ * ε₀) ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)) + 2) ∧
    (‖c (y k₁)‖ ≤ P.θ * ε₀ → ∃ Lμ, 0 ≤ Lμ ∧
      (∀ K, 1 ≤ K → D.Before f c C P ε₀ ε₁ K →
        (K : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) * (goodBound P Lμ p ε₀ ε₁ + 1) +
          D.badCount f c C p P ε₀ ε₁ K) ∧
      (∀ M : ℝ, (∀ K, D.Before f c C P ε₀ ε₁ K → (D.badCount f c C p P ε₀ ε₁ K : ℝ) ≤ M) →
        ∃ kε, D.IsEnd f c C P ε₀ ε₁ kε ∧
          (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) * (goodBound P Lμ p ε₀ ε₁ + 1) +
            M) ∧
      (∀ kε, D.IsEnd f c C P ε₀ ε₁ kε →
        (D.derivEvals f c p P kε : ℝ) ≤
          1 + goodBound P Lμ p ε₀ ε₁ * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε ∧
        (D.funEvals kε : ℝ) ≤
          1 + (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
            (goodBound P Lμ p ε₀ ε₁ * ((fup - flow + 1) / ((1 - P.θ) * ε₀) + 1) + kε) +
            Real.log (P.toARpCCParams.sigmaMax Lμ / P.σ₀) / Real.log P.γ₂ * kε)) := by
  obtain ⟨-, hF, hD⟩ := lemma_7_2_2 h hC hp hℓ hι hβ0 hβ1 hΦ
  exact ⟨⟨hF, hD⟩, fun hle => theorem_7_2_7_phase2_of_mu2 (h.phase2 hle) hC hp hB hμ⟩

end BookHypotheses

end CartisGouldToint.Chapter07
