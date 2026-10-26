import Numlib.Analysis.Calculus.AnchoredLipschitz
import Numlib.Optimization.Complexity.ScaledRestart
import Numlib.Optimization.Constrained.TwoPhase
import Numlib.Optimization.Optimality.CurveConditions
import NumlibSurface.CartisGouldToint.Chapter07.Section02
import NumlibSurface.CartisGouldToint.Chapter14.Section02

/-!
# Cartis–Gould–Toint §14.3: High-order criticality for nonconvex constraints

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §14.3: the problem
`min_{x ∈ X} f(x)` subject to `c(x) = 0` (14.3.1) with a closed set `X ⊆ ℝⁿ` of simple
constraints and `c : ℝⁿ → ℝᵐ`, curve-based necessary conditions (§14.3.1), the
least-Euclidean-norm algorithm LENq-SC and the two-phase algorithm TPqp-GC (§14.3.2).

The Lagrangian is `ℒ(x, y) = f(x) - ⟪y, c(x)⟫` ((1.1.1)), `Constrained.lagrangianFn f c y`;
its measures are `Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c y) x) j δ V`
for sets `V` of
feasible displacements. The residual of Phase 2 is `r(x, t) = (c(x), f(x) - t)`, with norm
`Constrained.targetResidual f c t x` and merit `μ(x, t) = ½ ‖r(x, t)‖² =
Constrained.targetMerit f c t x` (14.3.30); `ν = ½ ‖c‖²` and `Φ₂ = ½ ‖r‖²` are `phi2 c`,
`phi2 r`.

## Main definitions

* `AssumptionXCQ` — X.CQ; `Constrained.lagrangianFn` — the Lagrangian;
* `phi2`, `lenStop`, `algorithm_14_3_1` — LENq-SC (Algorithm 14.3.1);
* `innerEvalBound` — the INNER cost contract (14.3.20)–(14.3.21);
* `AssumptionD1pLBX`, `AssumptionCD1pLBX` — f.D1pLB.X and c.D1pLB.X;
* `TPqpSeq`, `IsTPqpGCPhase2`, `algorithm_14_3_2` — TPqp-GC (Algorithm 14.3.2), with the
  tests `TPqpSeq.IsKa`, `IsKb`, `Stop` and `meritCrit` ((14.3.32), (14.3.34));
* `IsInnerPhaseRun` — the INNER contract of Phase 2 (Lemmas 14.2.2–14.2.3 for `μ(·, t)`);
* `TPqpSeq.goodCount`, `IsBad`, `badCount`, `funEvals`, `derivEvals`, `goodBound`.

## Main results

* `theorem_14_3_1` (corrected), `example_14_3_1` (corrected), `theorem_14_3_2`;
* `theorem_14_3_3` (with an integer ceiling), `theorem_14_3_4` (with `∑_j` for `max_j`);
* `lemma_14_3_5` (corrected), `lemma_14_3_6_i`, `lemma_14_3_6_ii`, `lemma_14_3_7`,
  `lemma_14_3_8` and `theorem_14_3_9` (corrected, with the number of bad outer iterations as a
  parameter).

## Deviations from the book

* **Theorem 14.3.1 is false as printed.** The book's descriptor set `𝒟^j_X` only asks the arc to
  stay in `X` and satisfy the expansion conditions (14.3.3) of `c`; then `X = ℝ²`,
  `c(x) = x₁² + x₂²`, `f(x) = -x₁` and the (only feasible, hence minimizing) point `x⋆ = 0`
  violate (14.3.4) for `s₁ = e₁`. The arcs must be feasible for `X ∩ {c = 0}`, and (14.3.3) then
  holds automatically. X.CQ only rules out vacuity and is not needed.
* Theorem 14.3.2: "neighbourhood of diameter `δ_j`" is read as the closed ball of radius `δ_j`,
  and `L_{c,j}` as the Lipschitz constant of the vector-valued `∇^j c` (componentwise constants
  would cost a factor `√m`); `X` closed and nonempty and `x_ε ∈ X` are not needed.
* Algorithm 14.3.1: the constant `β ∈ (0, min(1, 1/‖r(x₀)‖))` is written
  `0 < β < 1`, `β ‖r(x₀)‖ < 1` (so that `r(x₀) = 0` is allowed); the tolerances `ε_j ∈ (0, 1)` are
  relaxed to `(0, 1]`, as Algorithm 14.3.2 calls LENq-SC with `ε_j ∈ (0, 1]`.
* Theorem 14.3.3: the iteration bound `max(0, log(ε₀/‖r(x₀)‖)/log β)` must be rounded up.
* Theorem 14.3.4: the proof bounds `∑_k max_j a_{k,j}` by `max_j ∑_k a_{k,j}`, which is invalid;
  the bound holds with `∑_j` in place of `max_j` (the same order for fixed `q`). The smoothness
  assumption Φ₂.D1qLaB.X only serves to justify the cost contract (14.3.20)–(14.3.21), which is
  the hypothesis actually used; the statement is given for one cost sequence (function or
  derivative evaluations alike).
* Algorithm 14.3.2: the INNER calls of Phase 2 are described by their iterates; the run requires
  that `μ(·, t_k)` does not increase along a call and that a call is stopped as soon as the first
  test of (14.3.32) holds (`‖r‖ < θε₀`). The latter is a convenience (checking (14.3.32) after
  each inner iteration): it makes every successful iteration but the last of a call a good one;
  without it, the successful iterations below `θε₀` could be bounded separately using `μ ≥ 0`.
  Step 2(a) keeps the printed
  strict test `‖r(x_{k+1}, t_k)‖ < θε₀`.
* Lemma 14.3.5: (14.3.43), (14.3.46) are false as printed (the extra terms are not bounded by
  `φ_{ℒ,1} ‖∇f‖ δ`; e.g. `c ≡ 0`, `X = [-1, 1]`, `f(x) = x/4 - 25x²/8`, `ε₀ = 1/100` gives
  `φ^1_{ℒ,T,2} = 27/8` against `17/32`); they are replaced by `(‖∇f‖δ)²/(2τ)` and
  `(‖∇f‖δ + ‖∇²f‖δ²)‖∇f‖δ/(2τ)`. When Phase 2 ends with `f(x_ε) = t_ε`, only `‖c(x_ε)‖ ≥ θε₀`
  follows and only the first-order part of (14.3.41) (the measures of `ν` and `μ` differ at
  order `j ≥ 2`).
* Lemmas 14.3.7–14.3.8 and Theorem 14.3.9: `∑_j` replaces `max_j` as in Theorem 14.3.4; the good
  inner iterations (successful and not followed by the end of their INNER call) are counted per
  block by `G = κ^S (1 - θ) M`; the `i = 0` entries and the last iterations of the calls are
  counted separately, `κ_unc` is paid per call, and the number of *bad* calls of `𝒦_b` (calls
  whose only move is their last iteration) is not bounded by the book and appears as a parameter;
  the book's `f_up - f_low - 1` is `f_up - f_low + 1`. The derivative count acquires an
  `ε₀^{-1}` term.

## Not formalized

The explicit counterexample to (14.3.43) (only described above), the existence of LENq-SC and
TPqp-GC runs, and the asymptotic `O(·)` restatements.
-/

open Set Metric
open scoped Nat RealInnerProductSpace
open Constrained (lagrangianFn)

namespace CartisGouldToint.Chapter14

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-! ### §14.3.1 Necessary conditions -/

/-- **Assumption X.CQ** of [cartis2022evaluation], §14.3.1, at `x⋆ ∈ X` for orders `j ≤ q`, as
printed: for each `j ∈ [1 : q]` some nonzero tuple `(s_1, …, s_j)` belongs to the descriptor set
`𝒟^j_X` (an arc `x⋆ + ∑ α^i s_i + o(α^j)` stays in `X`) and satisfies (14.3.3) for `c`. It is not
needed for the (corrected) Theorem 14.3.1. -/
def AssumptionXCQ (X : Set ℝⁿ) (c : ℝⁿ → ℝᵐ) (xs : ℝⁿ) (q : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 q, ∃ s : ℕ → ℝⁿ, (∃ i ∈ Finset.Icc 1 j, s i ≠ 0) ∧
    Optimization.IsFeasibleArc X xs j s ∧
    ∀ i ∈ Finset.Icc 1 j, Optimization.curveCoeff (ftaylorSeries ℝ c xs) s i = 0

/-- **Theorem 14.3.1** of [cartis2022evaluation] (curve-based necessary conditions for a
constrained minimum), **corrected**. Let `f` and `c` be `C^q` on an open set containing `X`, and
let `x⋆` be a local minimizer of (14.3.1): a feasible point (`x⋆ ∈ X`, `c(x⋆) = 0`) minimizing `f`
locally on `X ∩ {c = 0}`. Then `c(x⋆) = 0` and, for every multiplier `y⋆`, every `j ∈ [1 : q]` and
every tuple `s` admitting an arc `x⋆ + ∑_{i ≤ j} α^i s_i + o(α^j)` that stays in `X ∩ {c = 0}`:
the expansion conditions (14.3.3) hold, and if the Lagrangian coefficients of orders `1, …, j-1`
vanish (14.3.5), the coefficient of order `j` is nonnegative (14.3.4). The coefficients are
`Optimization.curveCoeff`, the book's `∑_k 1/k! ∑_{P(j,k)} ∇^k[s_{ℓ₁}, …, s_{ℓ_k}]`.
(As printed, with arcs that are only `X`-feasible, the theorem is false; see the module
documentation.) -/
theorem theorem_14_3_1 {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {xs : ℝⁿ}
    (hsmooth : ∃ U, IsOpen U ∧ X ⊆ U ∧ ContDiffOn ℝ q f U ∧ ContDiffOn ℝ q c U)
    (hfeas : xs ∈ X ∩ {x | c x = 0}) (hmin : IsLocalMinOn f (X ∩ {x | c x = 0}) xs) :
    c xs = 0 ∧ ∀ (ys : ℝᵐ), ∀ j ∈ Finset.Icc 1 q, ∀ s : ℕ → ℝⁿ,
      Optimization.IsFeasibleArc (X ∩ {x | c x = 0}) xs j s →
        (∀ i ∈ Finset.Icc 1 j, Optimization.curveCoeff (ftaylorSeries ℝ c xs) s i = 0) ∧
        ((∀ i ∈ Finset.Ico 1 j,
            Optimization.curveCoeff (ftaylorSeries ℝ (lagrangianFn f c ys) xs) s i = 0) →
          0 ≤ Optimization.curveCoeff (ftaylorSeries ℝ (lagrangianFn f c ys) xs) s j) := by
  obtain ⟨U, hU, hXU, hfU, hcU⟩ := hsmooth
  have hxU : xs ∈ U := hXU hfeas.1
  have hf : ContDiffAt ℝ q f xs := hfU.contDiffAt (hU.mem_nhds hxU)
  have hc : ContDiffAt ℝ q c xs := hcU.contDiffAt (hU.mem_nhds hxU)
  refine ⟨hfeas.2, fun ys j hj s harc => ⟨?_, fun hzero => ?_⟩⟩
  · have hjq : (j : WithTop ℕ∞) ≤ q := by exact_mod_cast (Finset.mem_Icc.1 hj).2
    exact Optimization.curveCoeff_eq_zero_of_isFeasibleArc (hc.of_le hjq) harc
  · exact Optimization.curveCoeff_lagrangian_nonneg_of_isLocalMinOn hf hc hfeas.2 hmin ys hj harc
      hzero

/-! ### Theorem 14.3.2 -/

/-- **Theorem 14.3.2** of [cartis2022evaluation] (local sufficiency of the Lagrangian for
approximate minimizers). Let `f` and `c` be `C^j` near `x_ε` with `∇^j f`, `∇^j c` Lipschitz with
constants `L_f, L_c ≥ 0` on the closed ball of radius `δ` around `x_ε`, `V` a set of feasible
displacements, `‖c(x_ε)‖ ≤ ε₀` (14.3.8), and
`φ^δ_{ℒ,V,j}(x_ε, y_ε) ≤ ε ‖(1, y_ε)‖ δ^j/j! + η` (14.3.9), `‖(1, y)‖ = √(1 + ‖y‖²)`. Then for
every `d ∈ V` with `‖d‖ ≤ δ`, `‖c(x_ε + d)‖ ≤ ε₀` and `√2 max(L_f, L_c) ‖d‖ ≤ (j+1) ε` (14.3.11):
(14.3.10) `f(x_ε + d) ≥ f(x_ε) - 2ε₀‖y_ε‖ - 2ε‖(1, y_ε)‖ δ^j/j! - η`; and (14.3.12) the term
`2ε₀‖y_ε‖` can be dropped if `c(x_ε + d) = c(x_ε)`, or if `c(x_ε + d) = 0` and
`⟪y_ε, c(x_ε)⟫ ≤ 0`. -/
theorem theorem_14_3_2 {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {xε : ℝⁿ} {yε : ℝᵐ} {V : Set ℝⁿ} {j : ℕ}
    {δ ε η ε₀ Lf Lc : ℝ} (hf : ∀ z ∈ closedBall xε δ, ContDiffAt ℝ j f z)
    (hc : ∀ z ∈ closedBall xε δ, ContDiffAt ℝ j c z)
    (hLf : IteratedFDerivLipschitzOn f j Lf (closedBall xε δ))
    (hLc : IteratedFDerivLipschitzOn c j Lc (closedBall xε δ)) (hLf0 : 0 ≤ Lf) (hLc0 : 0 ≤ Lc)
    (hcx : ‖c xε‖ ≤ ε₀)
    (hφ : Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c yε) xε) j δ V ≤
      ε * √(1 + ‖yε‖ ^ 2) * δ ^ j / j ! + η)
    {d : ℝⁿ} (hdV : d ∈ V) (hd : ‖d‖ ≤ δ)
    (hLd : √2 * max Lf Lc * ‖d‖ ≤ (j + 1) * ε) :
    (‖c (xε + d)‖ ≤ ε₀ →
      f xε - 2 * ε₀ * ‖yε‖ - 2 * ε * √(1 + ‖yε‖ ^ 2) * δ ^ j / (j ! : ℝ) - η ≤ f (xε + d)) ∧
    (c (xε + d) = c xε ∨ (c (xε + d) = 0 ∧ ⟪yε, c xε⟫ ≤ 0) →
      f xε - 2 * ε * √(1 + ‖yε‖ ^ 2) * δ ^ j / (j ! : ℝ) - η ≤ f (xε + d)) := by
  refine ⟨fun hcd => Optimization.le_of_lagrangian_taylorMeasure_le hf hc hLf hLc hLf0 hLc0 hcx
    hφ hdV hd hcd hLd, ?_⟩
  rintro (heq | ⟨h0, hy⟩)
  · exact Optimization.le_of_lagrangian_taylorMeasure_le_of_eq hf hc hLf hLc hLf0 hLc0 hφ hdV hd
      heq hLd
  · exact Optimization.le_of_lagrangian_taylorMeasure_le_of_eq_zero hf hc hLf hLc hLf0 hLc0 hφ hdV
      hd h0 hy hLd

/-! ### §14.3.2.1 The LENq-SC algorithm -/

/-- The least-squares function `Φ₂(x) = ½ ‖r(x)‖²` of [cartis2022evaluation], (14.3.16) (for
`r = c` this is `ν`). -/
noncomputable def phi2 (r : ℝⁿ → ℝᵐ) : ℝⁿ → ℝ := fun x => ‖r x‖ ^ 2 / 2

theorem phi2_apply (r : ℝⁿ → ℝᵐ) (x : ℝⁿ) : phi2 r x = ‖r x‖ ^ 2 / 2 := rfl

/-- The termination test (14.3.23) of LENq-SC ([cartis2022evaluation], Algorithm 14.3.1) at
iteration `k`: `‖r(x_k)‖ ≤ ε₀`, or (for `k ≥ 1`, when radii `δ_k` have been computed)
`φ^{δ_{k,j}}_{Φ₂,X(x_k),j}(x_k) ≤ ε_j ‖r(x_k)‖ δ_{k,j}^j/j!` for all `j ∈ [1 : q]`. The primal
tolerance is `ε 0`. -/
def lenStop (r : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (δ : ℕ → ℕ → ℝ)
    (k : ℕ) : Prop :=
  ‖r (x k)‖ ≤ ε 0 ∨ (1 ≤ k ∧ ∀ j ∈ Finset.Icc 1 q,
    Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 r) (x k)) j (δ k j) {d | x k + d ∈ X} ≤
      ε j * ‖r (x k)‖ * δ k j ^ j / j !)

/-- **Algorithm 14.3.1 (LENq-SC)** of [cartis2022evaluation] as a run predicate on the iterates
`x` and radii `δ` (indexed by the outer iteration `k`; `δ 0` is unused). Given `x₀ ∈ X`,
tolerances `ε_j ∈ (0, 1]` (`j ∈ [0 : q]`) and `β` with `0 < β < 1`, `β ‖r(x₀)‖ < 1`: the run
stops at the first `k` with `lenStop` ((14.3.23); at `k = 0` only `‖r(x₀)‖ ≤ ε₀`), and at every
iteration `k ≥ 1` reached, `x_k ∈ X` and `δ_k ∈ (0, 1]^q` are the output of
`INNER(Φ₂, X, q, x_{k-1}, β ‖r(x_{k-1})‖ ε)`, i.e. satisfy (14.3.22). -/
structure algorithm_14_3_1 (r : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (ε : ℕ → ℝ) (β : ℝ)
    (x : ℕ → ℝⁿ) (δ : ℕ → ℕ → ℝ) : Prop where
  mem_zero : x 0 ∈ X
  /-- The tolerances are positive. -/
  ε_pos : ∀ j ∈ Finset.range (q + 1), 0 < ε j
  /-- The tolerances are at most `1`. -/
  ε_le_one : ∀ j ∈ Finset.range (q + 1), ε j ≤ 1
  /-- `β > 0`. -/
  β_pos : 0 < β
  β_lt_one : β < 1
  β_mul_lt_one : β * ‖r (x 0)‖ < 1
  /-- The INNER output lies in `X`. -/
  mem : ∀ k, 1 ≤ k → (∀ i < k, ¬ lenStop r X q ε x δ i) → x k ∈ X
  /-- The INNER output radii lie in `(0, 1]`. -/
  radius_mem : ∀ k, 1 ≤ k → (∀ i < k, ¬ lenStop r X q ε x δ i) →
    ∀ j ∈ Finset.Icc 1 q, 0 < δ k j ∧ δ k j ≤ 1
  /-- The INNER output condition (14.3.22). -/
  inner : ∀ k, 1 ≤ k → (∀ i < k, ¬ lenStop r X q ε x δ i) → ∀ j ∈ Finset.Icc 1 q,
    Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 r) (x k)) j (δ k j) {d | x k + d ∈ X} ≤
      β * ‖r (x (k - 1))‖ * ε j * δ k j ^ j / j !

namespace algorithm_14_3_1

variable {r : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {ε : ℕ → ℝ} {β : ℝ} {x : ℕ → ℝⁿ}
  {δ : ℕ → ℕ → ℝ}

/-- **The residual contracts** ([cartis2022evaluation], proof of Theorem 14.3.3): at every
iteration `k ≥ 1` at which LENq-SC has not terminated (up to and including `k`),
`‖r(x_k)‖ < β ‖r(x_{k-1})‖`. -/
theorem norm_lt (h : algorithm_14_3_1 r X q ε β x δ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ i ≤ k, ¬ lenStop r X q ε x δ i) : ‖r (x k)‖ < β * ‖r (x (k - 1))‖ := by
  have hks := hk k le_rfl
  simp only [lenStop, not_or, not_and, not_forall, not_le] at hks
  obtain ⟨j, hj, hlt⟩ := hks.2 hk1
  have hbef : ∀ i < k, ¬ lenStop r X q ε x δ i := fun i hi => hk i hi.le
  have hin := h.inner k hk1 hbef j hj
  have hδ := (h.radius_mem k hk1 hbef j hj).1
  have hεj : 0 < ε j := h.ε_pos j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have ha : 0 < ε j * δ k j ^ j / j ! := by positivity
  have : ‖r (x k)‖ * (ε j * δ k j ^ j / j !) < β * ‖r (x (k - 1))‖ * (ε j * δ k j ^ j / j !) := by
    calc ‖r (x k)‖ * (ε j * δ k j ^ j / j !) = ε j * ‖r (x k)‖ * δ k j ^ j / j ! := by ring
      _ < _ := hlt.trans_le hin
      _ = _ := by ring
  exact lt_of_mul_lt_mul_right this ha.le

/-- Iterating the contraction: before termination, `‖r(x_j)‖ ≤ β^{j-i} ‖r(x_i)‖` for `i ≤ j`. -/
theorem norm_le_pow_mul (h : algorithm_14_3_1 r X q ε β x δ) {i j : ℕ} (hij : i ≤ j)
    (hj : ∀ l ≤ j, ¬ lenStop r X q ε x δ l) : ‖r (x j)‖ ≤ β ^ (j - i) * ‖r (x i)‖ := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have ih := ih fun l hl => hj l (hl.trans j.le_succ)
    have hlt : ‖r (x (j + 1))‖ < β * ‖r (x j)‖ := h.norm_lt (Nat.succ_pos j) hj
    rw [Nat.succ_sub hij, pow_succ]
    have := h.β_pos
    calc ‖r (x (j + 1))‖ ≤ β * ‖r (x j)‖ := hlt.le
      _ ≤ β * (β ^ (j - i) * ‖r (x i)‖) := by gcongr
      _ = _ := by ring

end algorithm_14_3_1

/-- **Theorem 14.3.3** of [cartis2022evaluation] (convergence of LENq-SC), **with the integer
ceiling**. Every LENq-SC run terminates, at an iteration
`k_max ≤ ⌈log(ε₀/‖r(x₀)‖)/log β⌉₊` (the book's `max(0, log(ε₀/‖r(x₀)‖)/log β)` must be rounded
up), at a point satisfying (14.3.18): `‖r(x_{k_max})‖ ≤ ε₀`, or
`φ^{δ_j}_{Φ₂,X(x_{k_max}),j}(x_{k_max}) ≤ ε_j ‖r(x_{k_max})‖ δ_j^j/j!` for all `j ∈ [1 : q]`, for
some `δ ∈ (0, 1]^q`. Moreover `‖r(x_k)‖ < β ‖r(x_{k-1})‖` at every iteration `k ≥ 1` before
termination. -/
theorem theorem_14_3_3 {r : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {ε : ℕ → ℝ} {β : ℝ}
    {x : ℕ → ℝⁿ} {δ : ℕ → ℕ → ℝ} (h : algorithm_14_3_1 r X q ε β x δ) :
    (∃ kmax, Optimization.IsFirstHit (lenStop r X q ε x δ) kmax ∧
      kmax ≤ ⌈Real.log (ε 0 / ‖r (x 0)‖) / Real.log β⌉₊ ∧
      (‖r (x kmax)‖ ≤ ε 0 ∨ ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δ' j ∧ δ' j ≤ 1) ∧
        ∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 r) (x kmax)) j
          (δ' j) {d | x kmax + d ∈ X} ≤ ε j * ‖r (x kmax)‖ * δ' j ^ j / j !)) ∧
    ∀ k, 1 ≤ k → (∀ i ≤ k, ¬ lenStop r X q ε x δ i) → ‖r (x k)‖ < β * ‖r (x (k - 1))‖ := by
  have hε₀ : 0 < ε 0 := h.ε_pos 0 (by simp)
  obtain ⟨kmax, hhit, hle⟩ := Optimization.le_ceil_log_of_contract (r := fun k => ‖r (x k)‖)
    h.β_pos h.β_lt_one hε₀ (fun k hk => not_le.1 fun h' => hk (Or.inl h'))
    (fun k hk1 hk => h.norm_lt hk1 hk)
  refine ⟨⟨kmax, hhit, hle, ?_⟩, fun k hk1 hk => h.norm_lt hk1 hk⟩
  rcases hhit.1 with h0 | ⟨hk1, hcrit⟩
  · exact Or.inl h0
  · exact Or.inr ⟨δ kmax, h.radius_mem kmax hk1 hhit.2, hcrit⟩

/-- **The INNER cost contract** of [cartis2022evaluation], (14.3.20)–(14.3.21):
`κ (f(x^S) - f_low) max_{j ∈ [1 : q]} ε_j^{-π_j}`, with `gap = f(x^S) - f_low` and the exponents
`π_j > 1` of the chosen INNER method (from (14.2.12)). The maximum is a supremum over the finite
index set (`0` if `q = 0`). -/
noncomputable def innerEvalBound (κ : ℝ) (π : ℕ → ℝ) (q : ℕ) (gap : ℝ) (ε : ℕ → ℝ) : ℝ :=
  κ * gap * ⨆ j : Finset.Icc 1 q, ε j ^ (-π j)

/-- The maximum in the cost contract is at most the sum. -/
theorem innerEvalBound_le_sum {κ gap : ℝ} (hκ : 0 ≤ κ) (hgap : 0 ≤ gap) (π : ℕ → ℝ) (q : ℕ)
    {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) :
    innerEvalBound κ π q gap ε ≤ κ * gap * ∑ j ∈ Finset.Icc 1 q, ε j ^ (-π j) := by
  unfold innerEvalBound
  gcongr
  refine Real.iSup_le (fun j => ?_) (Finset.sum_nonneg fun i hi =>
    (Real.rpow_pos_of_pos (hε i hi) _).le)
  exact Finset.single_le_sum (f := fun i => ε i ^ (-π i))
    (fun i hi => (Real.rpow_pos_of_pos (hε i hi) _).le) j.2

/-- **Theorem 14.3.4** of [cartis2022evaluation] (evaluation complexity of LENq-SC),
**corrected**. Let a LENq-SC run terminate at `k_max`, let `π_j > 1`, and let the cost `n_k` of
the `k`-th INNER call (evaluations of `Φ₂`, or of its derivatives) satisfy the contract
(14.3.20) (resp. (14.3.21)) with constant `κ ≥ 0` and `f_low = 0`:
`n_k ≤ κ Φ₂(x_{k-1}) max_j (β ‖r(x_{k-1})‖ ε_j)^{-π_j}`. Then the total cost is
`∑_{k=1}^{k_max} n_k ≤ ½ κ ‖r(x₀)‖ ∑_{j=1}^q β^{1-2π_j}/(β^{1-π_j} - 1) ε₀^{1-π_j} ε_j^{-π_j}`
((14.3.27)–(14.3.28) with `∑_j` in place of `max_j`: the printed proof exchanges a sum over `k` and
a maximum over `j`). -/
theorem theorem_14_3_4 {r : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {ε : ℕ → ℝ} {β : ℝ}
    {x : ℕ → ℝⁿ} {δ : ℕ → ℕ → ℝ} (h : algorithm_14_3_1 r X q ε β x δ) {kmax : ℕ}
    (hend : Optimization.IsFirstHit (lenStop r X q ε x δ) kmax) {π : ℕ → ℝ}
    (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j) {κ : ℝ} (hκ : 0 ≤ κ) {cost : ℕ → ℝ}
    (hcost : ∀ k ∈ Finset.Icc 1 kmax,
      cost k ≤ innerEvalBound κ π q (phi2 r (x (k - 1))) (fun j => β * ‖r (x (k - 1))‖ * ε j)) :
    ∑ k ∈ Finset.Icc 1 kmax, cost k ≤
      1 / 2 * κ * ‖r (x 0)‖ * ∑ j ∈ Finset.Icc 1 q,
        β ^ (1 - 2 * π j) / (β ^ (1 - π j) - 1) * ε 0 ^ (1 - π j) * ε j ^ (-π j) := by
  set R : ℕ → ℝ := fun k => ‖r (x k)‖ with hR
  have hβ := h.β_pos
  have hβ1 := h.β_lt_one
  have hε₀ : 0 < ε 0 := h.ε_pos 0 (by simp)
  have hεj : ∀ j ∈ Finset.Icc 1 q, 0 < ε j := fun j hj =>
    h.ε_pos j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  -- the residuals before termination
  have hnot : ∀ l < kmax, ¬ lenStop r X q ε x δ l := hend.2
  have hRgt : ∀ l < kmax, ε 0 < R l := fun l hl =>
    not_le.1 fun h' => hnot l hl (Or.inl h')
  have hRle0 : ∀ k ∈ Finset.Icc 1 kmax, R (k - 1) ≤ R 0 := fun k hk => by
    have hk := Finset.mem_Icc.1 hk
    have := h.norm_le_pow_mul (Nat.zero_le (k - 1))
      (fun l hl => hnot l (by omega))
    have hp : β ^ (k - 1 - 0) ≤ 1 := pow_le_one₀ hβ.le hβ1.le
    calc R (k - 1) ≤ β ^ (k - 1 - 0) * R 0 := this
      _ ≤ 1 * R 0 := by gcongr
      _ = R 0 := one_mul _
  have hRlow : ∀ k ∈ Finset.Icc 1 kmax, β ^ ((k : ℤ) - kmax) * ε 0 ≤ R (k - 1) := by
    intro k hk
    have hk := Finset.mem_Icc.1 hk
    have hpow := h.norm_le_pow_mul (i := k - 1) (j := kmax - 1) (by omega)
      (fun l hl => hnot l (by omega))
    have hlast := hRgt (kmax - 1) (by omega)
    have hz : β ^ ((k : ℤ) - kmax) = (β ^ (kmax - 1 - (k - 1)))⁻¹ := by
      rw [← zpow_natCast, ← zpow_neg]
      congr 1
      rw [show kmax - 1 - (k - 1) = kmax - k by omega, Nat.cast_sub hk.2]
      ring
    rw [hz, inv_mul_le_iff₀ (pow_pos hβ _)]
    exact (hlast.le.trans hpow)
  -- the per-call bound
  have hcall : ∀ k ∈ Finset.Icc 1 kmax, cost k ≤ 1 / 2 * κ * R 0 *
      ∑ j ∈ Finset.Icc 1 q, β ^ (-π j) * ε j ^ (-π j) * R (k - 1) ^ (1 - π j) := by
    intro k hk
    have hRk : 0 < R (k - 1) := hε₀.trans (hRgt (k - 1) (by have := Finset.mem_Icc.1 hk; omega))
    refine (hcost k hk).trans ((innerEvalBound_le_sum hκ (by unfold phi2; positivity) π q
      (fun j hj => by have := hεj j hj; positivity)).trans ?_)
    rw [phi2_apply, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hε := hεj j hj
    rw [Real.mul_rpow (by positivity) hε.le, Real.mul_rpow hβ.le hRk.le]
    have hsq : R (k - 1) ^ 2 * R (k - 1) ^ (-π j) ≤ R 0 * R (k - 1) ^ (1 - π j) := by
      have : R (k - 1) ^ 2 * R (k - 1) ^ (-π j) = R (k - 1) * R (k - 1) ^ (1 - π j) := by
        rw [Real.rpow_sub hRk, Real.rpow_one, Real.rpow_neg hRk.le]
        field_simp
      rw [this]
      gcongr
      exact hRle0 k hk
    have h1 : 0 ≤ κ * β ^ (-π j) * ε j ^ (-π j) / 2 := by positivity
    calc κ * (‖r (x (k - 1))‖ ^ 2 / 2) * (β ^ (-π j) * R (k - 1) ^ (-π j) * ε j ^ (-π j))
        = κ * β ^ (-π j) * ε j ^ (-π j) / 2 * (R (k - 1) ^ 2 * R (k - 1) ^ (-π j)) := by
          rw [hR]; ring
      _ ≤ κ * β ^ (-π j) * ε j ^ (-π j) / 2 * (R 0 * R (k - 1) ^ (1 - π j)) := by gcongr
      _ = 1 / 2 * κ * R 0 * (β ^ (-π j) * ε j ^ (-π j) * R (k - 1) ^ (1 - π j)) := by ring
  refine (Finset.sum_le_sum hcall).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hR0 : 0 ≤ R 0 := norm_nonneg _
  gcongr with j hj
  rw [← Finset.mul_sum]
  have hgeom := Optimization.sum_rpow_le_of_geometric_lower (r := R) hβ hβ1 hε₀ (hπ j hj) hRlow
  have hε := hεj j hj
  have hb : 0 ≤ β ^ (-π j) * ε j ^ (-π j) := by positivity
  calc β ^ (-π j) * ε j ^ (-π j) * ∑ k ∈ Finset.Icc 1 kmax, R (k - 1) ^ (1 - π j)
      ≤ β ^ (-π j) * ε j ^ (-π j) * (ε 0 ^ (1 - π j) * β ^ (1 - π j) / (β ^ (1 - π j) - 1)) :=
        mul_le_mul_of_nonneg_left hgeom hb
    _ = β ^ (1 - 2 * π j) / (β ^ (1 - π j) - 1) * ε 0 ^ (1 - π j) * ε j ^ (-π j) := by
        have : β ^ (1 - 2 * π j) = β ^ (-π j) * β ^ (1 - π j) := by
          rw [← Real.rpow_add hβ]; ring_nf
        rw [this]; ring

/-! ### Smoothness assumptions and Lemma 14.3.6 -/

/-- **Assumption f.D1pLB.X** of [cartis2022evaluation], §14.3.2.2 (and f.D1qLB.X with `q` in
place of `p`): `g` is `p` times continuously differentiable on an open convex set `X₀ ⊇ X`, and
for `j ∈ [1 : p]` its derivative tensors `∇^j g` are Lipschitz continuous (constants `L j`) and
bounded (constants `B j`) on `X₀`. -/
structure AssumptionD1pLBX (g : ℝⁿ → ℝ) (X X₀ : Set ℝⁿ) (p : ℕ) (L B : ℕ → ℝ) : Prop where
  isOpen : IsOpen X₀
  convex : Convex ℝ X₀
  subset : X ⊆ X₀
  contDiffOn : ContDiffOn ℝ p g X₀
  lipschitz : ∀ j ∈ Finset.Icc 1 p, IteratedFDerivLipschitzOn g j (L j) X₀
  norm_le : ∀ j ∈ Finset.Icc 1 p, ∀ x ∈ X₀, ‖iteratedFDeriv ℝ j g x‖ ≤ B j

/-- **Assumption c.D1pLB.X** of [cartis2022evaluation], §14.3.2.2: the components `c_i` are `p`
times continuously differentiable on an open convex set `X₀ ⊇ X`, with Lipschitz and bounded
derivative tensors of orders `1, …, p` on `X₀` (with constants common to all components, which is
no loss of generality for finitely many components). -/
structure AssumptionCD1pLBX (c : ℝⁿ → ℝᵐ) (X X₀ : Set ℝⁿ) (p : ℕ) (L B : ℕ → ℝ) : Prop where
  isOpen : IsOpen X₀
  convex : Convex ℝ X₀
  subset : X ⊆ X₀
  component : ∀ i, AssumptionD1pLBX (fun x => c x i) X X₀ p L B

theorem AssumptionCD1pLBX.contDiffOn {c : ℝⁿ → ℝᵐ} {X X₀ : Set ℝⁿ} {p : ℕ} {L B : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ p L B) : ContDiffOn ℝ p c X₀ :=
  contDiffOn_piLp' 2 fun i => (hc.component i).contDiffOn

/-- The sublevel set `𝓛_ν(x₀) = {x ∈ X | ‖c(x)‖ ≤ ‖c(x₀)‖}` of Lemma 14.3.6(i) of
[cartis2022evaluation]. -/
def nuSublevel (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (x₀ : ℝⁿ) : Set ℝⁿ := {x ∈ X | ‖c x‖ ≤ ‖c x₀‖}

/-- The set `𝓛_μ(t) = {x ∈ X | ‖r(x, t)‖ ≤ 1}` of Lemma 14.3.6(ii) of [cartis2022evaluation]. -/
def muSublevel (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (t : ℝ) : Set ℝⁿ :=
  {x ∈ X | Constrained.targetResidual f c t x ≤ 1}

/-- f.D1pLB.X gives the hypotheses of the product rule (`AnchoredJetBounds`) for `g - a` on an
anchor set `A ⊆ X₀` on which `|g - a| ≤ U`. -/
theorem AssumptionD1pLBX.anchoredJetBounds_sub {g : ℝⁿ → ℝ} {X X₀ : Set ℝⁿ} {p : ℕ}
    {L B : ℕ → ℝ} (hg : AssumptionD1pLBX g X X₀ p L B) {A : Set ℝⁿ} (hA : A ⊆ X₀) (a : ℝ)
    {U : ℝ} (hU : ∀ x ∈ A, |g x - a| ≤ U) :
    AnchoredJetBounds (fun y => g y - a) p L B U A X₀ where
  contDiffOn := hg.contDiffOn.sub contDiffOn_const
  lipschitzAnchored i hi x hx y hy := by
    have hip := (Finset.mem_Icc.1 hi).2
    have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.1 hi).1; omega
    have hcd : ∀ z ∈ X₀, ContDiffAt ℝ i g z := fun z hz =>
      (hg.contDiffOn.contDiffAt (hg.isOpen.mem_nhds hz)).of_le (by exact_mod_cast hip)
    rw [AnchoredJetBounds.iteratedFDeriv_sub_const (hcd x (hA hx)) a hi0,
      AnchoredJetBounds.iteratedFDeriv_sub_const (hcd y hy) a hi0]
    exact ((hg.lipschitz i hi).anchored hA) x hx y hy
  norm_le i hi y hy := by
    have hip := (Finset.mem_Icc.1 hi).2
    have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.1 hi).1; omega
    rw [AnchoredJetBounds.iteratedFDeriv_sub_const
      ((hg.contDiffOn.contDiffAt (hg.isOpen.mem_nhds hy)).of_le (by exact_mod_cast hip)) a hi0]
    exact hg.norm_le i hi y hy
  abs_le := hU

/-- **Lemma 14.3.6(i)** of [cartis2022evaluation] (smoothness of `ν`). Under c.D1pLB.X there are
constants `L^A_j, L^B_j, B^A_j, B^B_j ≥ 1`, depending only on `m` and the constants of
c.D1pLB.X, such that for every `x₀`, `ν = ½ ‖c‖²` is `C^p` on `X₀` and for `j ∈ [1 : p]`,
`‖∇^j ν(x) - ∇^j ν(y)‖ ≤ (L^A_j + L^B_j ‖c(x₀)‖) ‖x - y‖` (14.3.60) and
`‖∇^j ν(x)‖ ≤ B^A_j + B^B_j ‖c(x₀)‖` (14.3.61) for all `x ∈ 𝓛_ν(x₀)` and `y ∈ X₀`. -/
theorem lemma_14_3_6_i {c : ℝⁿ → ℝᵐ} {X X₀ : Set ℝⁿ} {p : ℕ} {L B : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ p L B) :
    ∃ LA LB BA BB : ℕ → ℝ, (∀ j, 1 ≤ LA j ∧ 1 ≤ LB j ∧ 1 ≤ BA j ∧ 1 ≤ BB j) ∧
      ∀ x₀ : ℝⁿ, ContDiffOn ℝ p (phi2 c) X₀ ∧ ∀ j ∈ Finset.Icc 1 p,
        IteratedFDerivLipschitzAnchored (phi2 c) j (LA j + LB j * ‖c x₀‖) (nuSublevel c X x₀)
          X₀ ∧
        ∀ x ∈ nuSublevel c X x₀, ‖iteratedFDeriv ℝ j (phi2 c) x‖ ≤ BA j + BB j * ‖c x₀‖ := by
  refine ⟨fun j => max 1 (m * (anchoredMulLipConst L L B B j / 2)),
    fun j => max 1 (m * L j), fun j => max 1 (m * (anchoredMulBoundConst B B j / 2)),
    fun j => max 1 (m * B j), fun j => ⟨le_max_left _ _, le_max_left _ _, le_max_left _ _,
      le_max_left _ _⟩, fun x₀ => ?_⟩
  have hA : nuSublevel c X x₀ ⊆ X₀ := fun x hx => hc.subset hx.1
  have hU : 0 ≤ ‖c x₀‖ := norm_nonneg _
  have hjb : ∀ i, AnchoredJetBounds (fun y => c y i) p L B ‖c x₀‖ (nuSublevel c X x₀) X₀ :=
    fun i => by
      simpa using (hc.component i).anchoredJetBounds_sub hA 0 (U := ‖c x₀‖) fun x hx => by
        rw [sub_zero, ← Real.norm_eq_abs]
        exact (PiLp.norm_apply_le (c x) i).trans hx.2
  refine ⟨(hc.contDiffOn.norm_sq ℝ).div_const 2, fun j hj => ⟨?_, fun x hx => ?_⟩⟩
  · refine (AnchoredJetBounds.lipschitzAnchored_half_norm_sq hjb hc.isOpen hc.convex hA hj
      |>.mono_const ?_)
    have h1 := le_max_right 1 (m * (anchoredMulLipConst L L B B j / 2))
    have h2 := mul_le_mul_of_nonneg_right (le_max_right 1 ((m : ℝ) * L j)) hU
    nlinarith
  · refine (AnchoredJetBounds.norm_iteratedFDeriv_half_norm_sq_le hjb hc.isOpen hA hj hx).trans ?_
    have h1 := le_max_right 1 (m * (anchoredMulBoundConst B B j / 2))
    have h2 := mul_le_mul_of_nonneg_right (le_max_right 1 ((m : ℝ) * B j)) hU
    nlinarith

/-- `μ(·, t) = ½ ‖c‖² + ½ (f - t)²`. -/
theorem targetMerit_eq_add (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (t : ℝ) :
    Constrained.targetMerit f c t = (fun y => ‖c y‖ ^ 2 / 2) + fun y => (f y - t) ^ 2 / 2 := by
  funext y
  simp only [Constrained.targetMerit_def, Pi.add_apply]
  ring

/-- **Lemma 14.3.6(ii)** of [cartis2022evaluation] (smoothness of `μ`). Under c.D1pLB.X and
f.D1pLB.X (on the same `X₀`) there are constants `L_{μ,j}, B_{μ,j} ≥ 1`, independent of `t`,
such that for every target `t`, `μ(·, t)` is `C^p` on `X₀` and for `j ∈ [1 : p]`,
`‖∇^j μ(x, t) - ∇^j μ(y, t)‖ ≤ L_{μ,j} ‖x - y‖` (14.3.62) and `‖∇^j μ(x, t)‖ ≤ B_{μ,j}` (14.3.63;
the book writes `∇^j ν` there) for all `x ∈ 𝓛_μ(t) = {x ∈ X | ‖r(x, t)‖ ≤ 1}` and `y ∈ X₀`. -/
theorem lemma_14_3_6_ii {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X X₀ : Set ℝⁿ} {p : ℕ}
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ p Lc Bc)
    (hf : AssumptionD1pLBX f X X₀ p Lf Bf) :
    ∃ Lμ Bμ : ℕ → ℝ, (∀ j, 1 ≤ Lμ j ∧ 1 ≤ Bμ j) ∧
      ∀ t : ℝ, ContDiffOn ℝ p (Constrained.targetMerit f c t) X₀ ∧ ∀ j ∈ Finset.Icc 1 p,
        IteratedFDerivLipschitzAnchored (Constrained.targetMerit f c t) j (Lμ j)
          (muSublevel f c X t) X₀ ∧
        ∀ x ∈ muSublevel f c X t, ‖iteratedFDeriv ℝ j (Constrained.targetMerit f c t) x‖ ≤
          Bμ j := by
  refine ⟨fun j => max 1 (m * (anchoredMulLipConst Lc Lc Bc Bc j / 2 + Lc j) +
      (anchoredMulLipConst Lf Lf Bf Bf j / 2 + Lf j)),
    fun j => max 1 (m * (anchoredMulBoundConst Bc Bc j / 2 + Bc j) +
      (anchoredMulBoundConst Bf Bf j / 2 + Bf j)),
    fun j => ⟨le_max_left _ _, le_max_left _ _⟩, fun t => ?_⟩
  have hA : muSublevel f c X t ⊆ X₀ := fun x hx => hc.subset hx.1
  have hjc : ∀ i, AnchoredJetBounds (fun y => c y i) p Lc Bc 1 (muSublevel f c X t) X₀ :=
    fun i => by
      simpa using (hc.component i).anchoredJetBounds_sub hA 0 (U := 1) fun x hx => by
        rw [sub_zero, ← Real.norm_eq_abs]
        exact (PiLp.norm_apply_le (c x) i).trans
          (Constrained.norm_le_targetResidual.trans hx.2)
  have hjf : AnchoredJetBounds (fun y => f y - t) p Lf Bf 1 (muSublevel f c X t) X₀ :=
    hf.anchoredJetBounds_sub hA t fun x hx =>
      Constrained.abs_sub_le_targetResidual.trans hx.2
  have hcc : ContDiffOn ℝ p (fun y => ‖c y‖ ^ 2 / 2) X₀ :=
    (hc.contDiffOn.norm_sq ℝ).div_const 2
  have hff : ContDiffOn ℝ p (fun y => (f y - t) ^ 2 / 2) X₀ :=
    ((hf.contDiffOn.sub contDiffOn_const).pow 2).div_const 2
  rw [targetMerit_eq_add]
  refine ⟨hcc.add hff, fun j hj => ⟨?_, fun x hx => ?_⟩⟩
  · have hjp : (j : WithTop ℕ∞) ≤ p := by exact_mod_cast (Finset.mem_Icc.1 hj).2
    have h := (AnchoredJetBounds.lipschitzAnchored_half_norm_sq hjc hc.isOpen hc.convex hA
      hj).add (AnchoredJetBounds.lipschitzAnchored_half_sq hjf hc.isOpen hc.convex hA hj)
      (fun y hy => (hcc.contDiffAt (hc.isOpen.mem_nhds hy)).of_le hjp)
      (fun y hy => (hff.contDiffAt (hc.isOpen.mem_nhds hy)).of_le hjp) hA
    refine h.mono_const ?_
    simp only [mul_one]
    exact le_max_right _ _
  · have hjp : (j : WithTop ℕ∞) ≤ p := by exact_mod_cast (Finset.mem_Icc.1 hj).2
    rw [iteratedFDeriv_add_apply ((hcc.contDiffAt (hc.isOpen.mem_nhds (hA hx))).of_le hjp)
      ((hff.contDiffAt (hc.isOpen.mem_nhds (hA hx))).of_le hjp)]
    refine (norm_add_le _ _).trans ?_
    have h1 := AnchoredJetBounds.norm_iteratedFDeriv_half_norm_sq_le hjc hc.isOpen hA hj hx
    have h2 := AnchoredJetBounds.norm_iteratedFDeriv_half_sq_le hjf hc.isOpen hA hj hx
    simp only [mul_one] at h1 h2
    exact (add_le_add h1 h2).trans (le_max_right _ _)


/-! ### §14.3.2.2 The TPqp-GC algorithm -/

/-- The tolerances of Phase 1 of TPqp-GC ([cartis2022evaluation], Algorithm 14.3.2): LENq-SC on
`ν` with primal tolerance `θ ε₀` and dual tolerances `ε_j`, `j ∈ [1 : q]`. -/
noncomputable def phase1Tol (θ : ℝ) (ε : ℕ → ℝ) : ℕ → ℝ := fun j => if j = 0 then θ * ε 0 else ε j

@[simp] theorem phase1Tol_zero (θ : ℝ) (ε : ℕ → ℝ) : phase1Tol θ ε 0 = θ * ε 0 := rfl

theorem phase1Tol_of_ne (θ : ℝ) (ε : ℕ → ℝ) {j : ℕ} (hj : j ≠ 0) : phase1Tol θ ε j = ε j := by
  simp [phase1Tol, hj]

/-- The approximate-criticality test (14.3.34) of TPqp-GC (also the third test of (14.3.32)) at
the point `y` for the target `t` with radii `δ`:
`φ^{δ_j}_{μ,X(y),j}(y, t) ≤ ε_j ‖r(y, t)‖ δ_j^j/j!` for `j ∈ [1 : q]`. -/
def meritCrit (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (ε : ℕ → ℝ) (t : ℝ) (y : ℝⁿ)
    (δ : ℕ → ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 q,
    Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit f c t) y) j (δ j)
      {d | y + d ∈ X} ≤ ε j * Constrained.targetResidual f c t y * δ j ^ j / j !

/-- The sequences generated by Phase 2 of TPqp-GC ([cartis2022evaluation], Algorithm 14.3.2),
indexed by the outer iteration `k ≥ 1` (values at `k = 0` are unused): outer iterates `x k`,
targets `t k`, optimality radii `δ k`, and for the `k`-th call of INNER on `μ(·, t_k)` its
iterates `xi k i`, its number of iterations `e k` and its successful iterations `succ k i`. -/
structure TPqpSeq (n : ℕ) where
  /-- The outer iterates. -/
  x : ℕ → EuclideanSpace ℝ (Fin n)
  /-- The targets. -/
  t : ℕ → ℝ
  /-- The optimality radii. -/
  δ : ℕ → ℕ → ℝ
  /-- The inner iterates. -/
  xi : ℕ → ℕ → EuclideanSpace ℝ (Fin n)
  /-- The numbers of inner iterations. -/
  e : ℕ → ℕ
  /-- The successful inner iterations. -/
  succ : ℕ → ℕ → Prop

namespace TPqpSeq

variable (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (θ : ℝ) (ε : ℕ → ℝ)
  (D : TPqpSeq n)

/-- Outer iteration `k` is in `𝒦_a` ((14.3.36) of [cartis2022evaluation]): Step 2(a) occurs,
`‖r(x_{k+1}, t_k)‖ < θε₀`. -/
def IsKa (k : ℕ) : Prop := Constrained.targetResidual f c (D.t k) (D.x (k + 1)) < θ * ε 0

/-- Outer iteration `k` is in `𝒦_b` ([cartis2022evaluation], after (14.3.36)): Step 2(b)
occurs, `‖r(x_{k+1}, t_k)‖ ≥ θε₀` and `f(x_{k+1}) < t_k`. -/
def IsKb (k : ℕ) : Prop :=
  θ * ε 0 ≤ Constrained.targetResidual f c (D.t k) (D.x (k + 1)) ∧ f (D.x (k + 1)) < D.t k

/-- Phase 2 terminates at outer iteration `k` (Step 2 of Algorithm 14.3.2): in case (c), or in
cases (a)/(b) when (14.3.34) holds at `(x_{k+1}, t_{k+1})` with the radii `δ_{k+1}`. -/
def Stop (k : ℕ) : Prop :=
  (¬ D.IsKa f c θ ε k ∧ ¬ D.IsKb f c θ ε k) ∨
    ((D.IsKa f c θ ε k ∨ D.IsKb f c θ ε k) ∧
      meritCrit f c X q ε (D.t (k + 1)) (D.x (k + 1)) (D.δ (k + 1)))

/-- No outer iteration `j ∈ [1, k)` has terminated Phase 2. -/
def Before (k : ℕ) : Prop := ∀ j, 1 ≤ j → j < k → ¬ D.Stop f c X q θ ε j

/-- Phase 2 terminates at outer iteration `kε ≥ 1`. -/
def IsEnd (kε : ℕ) : Prop := 1 ≤ kε ∧ D.Stop f c X q θ ε kε ∧ D.Before f c X q θ ε kε

open Classical in
/-- The output target `t_ε` of Phase 2 terminating at outer iteration `k`: `t_{k+1}` in cases
(a)/(b) and `t_k` in case (c) (the output point is `x_ε = x_{k+1}`). -/
noncomputable def targetOut (k : ℕ) : ℝ :=
  if D.IsKa f c θ ε k ∨ D.IsKb f c θ ε k then D.t (k + 1) else D.t k

end TPqpSeq

/-- **Phase 2 of Algorithm 14.3.2** (TPqp-GC) of [cartis2022evaluation], started at the output
`x₁ ∈ X` of Phase 1 with `‖c(x₁)‖ ≤ θε₀`, as a predicate on the sequences `D`. Constants:
`θ ∈ (0, 1)`, `β ∈ (0, θ]`, tolerances `ε_j ∈ (0, 1]`, `j ∈ [0 : q]` (`ε₀ = ε 0`). Step 0:
`t₁ = f(x₁) - √(ε₀² - ‖c(x₁)‖²)`. For every outer iteration `k ≥ 1` reached:
Step 1, `x_{k+1} ∈ X` and radii `δ_{k+1} ∈ (0, 1]^q` satisfy (14.3.32), computed by a call of
INNER on `μ(·, t_k)` from `x_k`, whose iterates `x_{k,i}` (`i ≤ e_k`, `x_{k,0} = x_k`,
`x_{k,e_k} = x_{k+1}`) do not increase `μ(·, t_k)` and keep `‖r(·, t_k)‖ ≥ θε₀` before the last
one (the call is stopped as soon as the first test of (14.3.32) holds); Step 2, the target
updates (14.3.33) in case (a) and (14.3.35) in case (b). Termination is `TPqpSeq.Stop`. -/
structure IsTPqpGCPhase2 (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (θ β : ℝ)
    (ε : ℕ → ℝ) (x₁ : ℝⁿ) (D : TPqpSeq n) : Prop where
  /-- `θ > 0`. -/
  θ_pos : 0 < θ
  /-- `θ < 1`. -/
  θ_lt_one : θ < 1
  β_pos : 0 < β
  /-- `β ≤ θ`. -/
  β_le_θ : β ≤ θ
  ε_pos : ∀ j ∈ Finset.range (q + 1), 0 < ε j
  ε_le_one : ∀ j ∈ Finset.range (q + 1), ε j ≤ 1
  /-- `x₁ ∈ X`. -/
  mem_one : x₁ ∈ X
  /-- Phase 1 ended with `‖c(x₁)‖ ≤ θε₀`. -/
  norm_one_le : ‖c x₁‖ ≤ θ * ε 0
  /-- Phase 2 starts at `x₁`. -/
  x_one : D.x 1 = x₁
  /-- Step 0. -/
  t_one : D.t 1 = f x₁ - √(ε 0 ^ 2 - ‖c x₁‖ ^ 2)
  /-- Step 1: the new iterate is feasible. -/
  mem_succ : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.x (k + 1) ∈ X
  /-- Step 1: the radii lie in `(0, 1]`. -/
  radius_mem : ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
    ∀ j ∈ Finset.Icc 1 q, 0 < D.δ (k + 1) j ∧ D.δ (k + 1) j ≤ 1
  /-- Step 1: the output condition (14.3.32). -/
  output : ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
    Constrained.targetResidual f c (D.t k) (D.x (k + 1)) < θ * ε 0 ∨ f (D.x (k + 1)) < D.t k ∨
      meritCrit f c X q ε (D.t k) (D.x (k + 1)) (D.δ (k + 1))
  /-- Step 1: the INNER call starts at `x_k`. -/
  inner_zero : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.xi k 0 = D.x k
  /-- Step 1: the INNER call ends at `x_{k+1}`. -/
  inner_end : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.xi k (D.e k) = D.x (k + 1)
  /-- Step 1: INNER does not increase `μ(·, t_k)`. -/
  inner_mono : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → ∀ i < D.e k,
    Constrained.targetMerit f c (D.t k) (D.xi k (i + 1)) ≤
      Constrained.targetMerit f c (D.t k) (D.xi k i)
  /-- Step 1: the call is stopped as soon as `‖r(·, t_k)‖ < θε₀`. -/
  inner_residual_ge : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → ∀ i < D.e k,
    θ * ε 0 ≤ Constrained.targetResidual f c (D.t k) (D.xi k i)
  /-- Step 2(a): (14.3.33). -/
  t_succ_a : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.IsKa f c θ ε k →
    D.t (k + 1) = f (D.x (k + 1)) - √(ε 0 ^ 2 - ‖c (D.x (k + 1))‖ ^ 2)
  /-- Step 2(b): (14.3.35). -/
  t_succ_b : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.IsKb f c θ ε k →
    D.t (k + 1) = 2 * f (D.x (k + 1)) - D.t k

/-- **Algorithm 14.3.2 (TPqp-GC)** of [cartis2022evaluation] as a run predicate. Phase 1 is a
LENq-SC run (`algorithm_14_3_1`) on `r = c` from `x₀ ∈ X` with constant `β₁` and tolerances
`(θε₀, ε_1, …, ε_q)` (`phase1Tol`), terminating at its first hit `k₁`; its output is
`x₁ = xP k₁` with radii `δP k₁` ((14.3.31)). If `‖c(x₁)‖ > θε₀` the algorithm terminates;
otherwise Phase 2 (`IsTPqpGCPhase2`) runs from `x₁`. (The LENq-SC test stops at
`‖c(x₁)‖ ≤ θε₀`, while (14.3.31) is printed with `<`; the two differ only when
`‖c(x₁)‖ = θε₀`, in which case Phase 2 is entered, consistently with the exit test
`‖c(x₁)‖ > θε₀`.) -/
structure algorithm_14_3_2 (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (θ β₁ β : ℝ)
    (ε : ℕ → ℝ) (x₀ : ℝⁿ) (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) : Prop where
  /-- Phase 1 starts at `x₀`. -/
  start : xP 0 = x₀
  /-- Phase 1: LENq-SC on `ν = ½ ‖c‖²`. -/
  phase1 : algorithm_14_3_1 c X q (phase1Tol θ ε) β₁ xP δP
  /-- Phase 1 ends at its first termination index `k₁` (which exists by Theorem 14.3.3 and is
  determined by the Phase-1 sequences). -/
  phase1_end : Optimization.IsFirstHit (lenStop c X q (phase1Tol θ ε) xP δP) k₁
  /-- Phase 2, entered when `‖c(x₁)‖ ≤ θε₀`. -/
  phase2 : ‖c (xP k₁)‖ ≤ θ * ε 0 → IsTPqpGCPhase2 f c X q θ β ε (xP k₁) D

namespace IsTPqpGCPhase2

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : ℝⁿ}
  {D : TPqpSeq n}

theorem ε₀_pos (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) : 0 < ε 0 := h.ε_pos 0 (by simp)

theorem ε_pos' (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) {j : ℕ} (hj : j ∈ Finset.Icc 1 q) :
    0 < ε j :=
  h.ε_pos j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))

theorem before_one : D.Before f c X q θ ε 1 := fun _ h1 hj => absurd hj (by omega)

theorem before_mono {k K : ℕ} (h : D.Before f c X q θ ε K) (hk : k ≤ K) :
    D.Before f c X q θ ε k := fun j h1 hj => h j h1 (hj.trans_le hk)

/-- Before termination, an outer iteration is in `𝒦_a` or in `𝒦_b`. -/
theorem isKa_or_isKb_of_not_stop {k : ℕ} (hs : ¬ D.Stop f c X q θ ε k) :
    D.IsKa f c θ ε k ∨ D.IsKb f c θ ε k := by
  by_contra h'
  exact hs (Or.inl (not_or.1 h'))

/-- `μ(·, t_k)` is nonincreasing along the `k`-th INNER call. -/
theorem inner_merit_antitone (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : D.Before f c X q θ ε k) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ D.e k) :
    Constrained.targetMerit f c (D.t k) (D.xi k j) ≤
      Constrained.targetMerit f c (D.t k) (D.xi k i) := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (h.inner_mono k hk1 hk j (by omega)).trans (ih (by omega))

/-- `‖r(·, t_k)‖` is nonincreasing along the `k`-th INNER call. -/
theorem inner_resid_antitone (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : D.Before f c X q θ ε k) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ D.e k) :
    Constrained.targetResidual f c (D.t k) (D.xi k j) ≤
      Constrained.targetResidual f c (D.t k) (D.xi k i) :=
  Constrained.targetMerit_le_targetMerit_iff.1 (h.inner_merit_antitone hk1 hk hij hj)

/-- `‖r(x_{k+1}, t_k)‖ ≤ ‖r(x_k, t_k)‖`. -/
theorem resid_succ_le (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : D.Before f c X q θ ε k) :
    Constrained.targetResidual f c (D.t k) (D.x (k + 1)) ≤
      Constrained.targetResidual f c (D.t k) (D.x k) := by
  have := h.inner_resid_antitone hk1 hk (Nat.zero_le _) le_rfl
  rwa [h.inner_end k hk1 hk, h.inner_zero k hk1 hk] at this

/-- The outer iterates stay in `X`. -/
theorem x_mem (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) :
    ∀ k, 1 ≤ k → D.Before f c X q θ ε k → D.x k ∈ X := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base => intro _; rw [h.x_one]; exact h.mem_one
  | succ k hk1 _ => intro hk; exact h.mem_succ k hk1 (before_mono hk k.le_succ)

/-- **The outer bookkeeping of Phase 2** is a target sequence (`Constrained.IsTargetSequence`, with
the printed strict test `‖r(x_{k+1}, t_k)‖ < θε₀` of Step 2(a)) up to every outer iteration `K`
reached; hence Lemmas 7.2.3 and 7.2.4 hold for TPqp-GC ([cartis2022evaluation], §14.3.2.2). -/
theorem isTargetSequence (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) {K : ℕ}
    (hK : D.Before f c X q θ ε K) :
    Constrained.IsTargetSequence f c θ (ε 0) D.x D.t (D.IsKa f c θ ε) K where
  norm_one_le := h.x_one ▸ h.norm_one_le
  target_one := by rw [h.t_one, h.x_one]
  residual_succ_le k hk1 hkK := h.resid_succ_le hk1 (before_mono hK hkK.le)
  residual_le_of_Ka _ _ _ ha := ha.le
  target_succ_of_Ka k hk1 hkK ha := h.t_succ_a k hk1 (before_mono hK hkK.le) ha
  le_residual_of_not_Ka _ _ _ ha := not_lt.1 ha
  lt_target_of_not_Ka k hk1 hkK ha :=
    ((isKa_or_isKb_of_not_stop (hK k hk1 hkK)).resolve_left ha).2
  target_succ_of_not_Ka k hk1 hkK ha := h.t_succ_b k hk1 (before_mono hK hkK.le)
    ((isKa_or_isKb_of_not_stop (hK k hk1 hkK)).resolve_left ha)

/-- **The output of Phase 2** ([cartis2022evaluation], (14.3.48), (14.3.49), (14.3.52)): if
Phase 2 terminates at outer iteration `k_ε`, the output `x_ε = x_{k_ε+1}`,
`t_ε = targetOut k_ε` with radii `δ_ε = δ_{k_ε+1}` satisfies `θε₀ ≤ ‖r(x_ε, t_ε)‖ ≤ ε₀`,
`f(x_ε) ≥ t_ε` and (14.3.34) at `(x_ε, t_ε)`. -/
theorem output_spec (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) {kε : ℕ}
    (hend : D.IsEnd f c X q θ ε kε) :
    θ * ε 0 ≤ Constrained.targetResidual f c (D.targetOut f c θ ε kε) (D.x (kε + 1)) ∧
      Constrained.targetResidual f c (D.targetOut f c θ ε kε) (D.x (kε + 1)) ≤ ε 0 ∧
      D.targetOut f c θ ε kε ≤ f (D.x (kε + 1)) ∧
      meritCrit f c X q ε (D.targetOut f c θ ε kε) (D.x (kε + 1)) (D.δ (kε + 1)) := by
  classical
  obtain ⟨hk1, hstop, hbef⟩ := hend
  have hε₀ := h.ε₀_pos
  have hθ1 := h.θ_lt_one
  have hθε : θ * ε 0 ≤ ε 0 := mul_le_of_le_one_left hε₀.le hθ1.le
  have hr_k := (h.isTargetSequence hbef).residual_le hθ1.le hε₀.le hk1 le_rfl
  have hr_succ := (h.resid_succ_le hk1 hbef).trans hr_k
  rcases hstop with ⟨hna, hnb⟩ | ⟨hab, hcrit⟩
  · -- case (c)
    have hout : D.targetOut f c θ ε kε = D.t kε := by
      simp only [TPqpSeq.targetOut, not_or.2 ⟨hna, hnb⟩, ite_false]
    have hge : θ * ε 0 ≤ Constrained.targetResidual f c (D.t kε) (D.x (kε + 1)) := not_lt.1 hna
    have hft : D.t kε ≤ f (D.x (kε + 1)) := not_lt.1 fun hlt => hnb ⟨hge, hlt⟩
    rw [hout]
    refine ⟨hge, hr_succ, hft, ?_⟩
    rcases h.output kε hk1 hbef with h1 | h2 | h3
    · exact absurd h1 hna
    · exact absurd h2 (not_lt.2 hft)
    · exact h3
  · have hout : D.targetOut f c θ ε kε = D.t (kε + 1) := by
      simp only [TPqpSeq.targetOut, hab, ite_true]
    rw [hout]
    refine ⟨?_, ?_, ?_, hcrit⟩ <;> by_cases ha : D.IsKa f c θ ε kε
    · rw [h.t_succ_a kε hk1 hbef ha, Constrained.targetResidual_sub_sqrt hε₀.le
        (Constrained.norm_le_targetResidual.trans (ha.le.trans hθε))]
      exact hθε
    · have hb := hab.resolve_left ha
      rw [h.t_succ_b kε hk1 hbef hb, Constrained.targetResidual_two_mul_sub]
      exact hb.1
    · rw [h.t_succ_a kε hk1 hbef ha, Constrained.targetResidual_sub_sqrt hε₀.le
        (Constrained.norm_le_targetResidual.trans (ha.le.trans hθε))]
    · have hb := hab.resolve_left ha
      rw [h.t_succ_b kε hk1 hbef hb, Constrained.targetResidual_two_mul_sub]
      exact hr_succ
    · rw [h.t_succ_a kε hk1 hbef ha]
      linarith [Real.sqrt_nonneg (ε 0 ^ 2 - ‖c (D.x (kε + 1))‖ ^ 2)]
    · have hb := hab.resolve_left ha
      rw [h.t_succ_b kε hk1 hbef hb]
      linarith [hb.2]

end IsTPqpGCPhase2


/-! ### Lemma 14.3.5: consequences of termination -/

section Termination

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X X₀ : Set ℝⁿ} {q p : ℕ} {θ β₁ β : ℝ} {ε : ℕ → ℝ}
  {x₀ : ℝⁿ} {xP : ℕ → ℝⁿ} {δP : ℕ → ℕ → ℝ} {k₁ : ℕ} {D : TPqpSeq n}

/-- Termination of Phase 1 with `‖c(x₁)‖ > θε₀` gives (14.3.41) at `x₁` with the radii of the
last LENq-SC iteration. -/
theorem algorithm_14_3_2.phase1_exit (h : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D)
    (hc : θ * ε 0 < ‖c (xP k₁)‖) :
    1 ≤ k₁ ∧ (∀ j ∈ Finset.Icc 1 q, 0 < δP k₁ j ∧ δP k₁ j ≤ 1) ∧
      ∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (xP k₁)) j
        (δP k₁ j) {d | xP k₁ + d ∈ X} ≤ ε j * ‖c (xP k₁)‖ * δP k₁ j ^ j / j ! := by
  rcases h.phase1_end.1 with h0 | ⟨hk1, hcrit⟩
  · exact absurd h0 (not_le.2 (by simpa using hc))
  · refine ⟨hk1, h.phase1.radius_mem k₁ hk1 h.phase1_end.2, fun j hj => ?_⟩
    have := hcrit j hj
    rwa [phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega)] at this

/-- The first-order Taylor decrements of `μ(·, t)` and `ν` agree at a point where `f(x) = t`. -/
theorem taylorMeasure_one_targetMerit_of_eq {x : ℝⁿ} {t : ℝ} (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (ht : f x = t) (δ : ℝ) (S : Set ℝⁿ) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit f c t) x) 1 δ S =
      Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) x) 1 δ S := by
  unfold Optimization.taylorMeasure
  congr 1
  funext d
  rw [FormalMultilinearSeries.taylorDecrement_one_apply,
    FormalMultilinearSeries.taylorDecrement_one_apply]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply]
  rw [Constrained.fderiv_targetMerit_of_eq hf hc ht]
  rfl

/-- `ν = ½ ‖c‖²` is the merit function of the zero objective with target `0`. -/
theorem phi2_eq_targetMerit (c : ℝⁿ → ℝᵐ) :
    phi2 c = Constrained.targetMerit (fun _ => (0 : ℝ)) c 0 := by
  funext z
  simp [phi2]

/-- At a point where `f(x) = t`: `ΔT_{μ,2}(d) = ΔT_{ν,2}(d) - ½ (∇f(x)[d])²`. -/
theorem taylorDecrement_two_targetMerit_of_eq {x : ℝⁿ} {t : ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hc : ContDiffAt ℝ 2 c x) (ht : f x = t) (d : ℝⁿ) :
    (ftaylorSeries ℝ (Constrained.targetMerit f c t) x).taylorDecrement 2 d =
      (ftaylorSeries ℝ (phi2 c) x).taylorDecrement 2 d - (fderiv ℝ f x d) ^ 2 / 2 := by
  have hf1 : DifferentiableAt ℝ f x := hf.differentiableAt two_ne_zero
  have hc1 : DifferentiableAt ℝ c x := hc.differentiableAt two_ne_zero
  rw [FormalMultilinearSeries.taylorDecrement_two, FormalMultilinearSeries.taylorDecrement_two]
  simp only [ftaylorSeries, iteratedFDeriv_one_apply]
  rw [Constrained.fderiv_targetMerit_of_eq hf1 hc1 ht,
    Constrained.iteratedFDeriv_two_targetMerit_apply hf hc, phi2_eq_targetMerit,
    Constrained.iteratedFDeriv_two_targetMerit_apply contDiffAt_const hc, ← ht]
  have e : (fun y => ‖c y‖ ^ 2 / 2) = Constrained.targetMerit (fun _ => (0 : ℝ)) c 0 := by
    rw [← phi2_eq_targetMerit]; rfl
  rw [← e]
  simp
  ring

/-- At a point where `f(x) = t`: `ΔT_{μ,3}(d) = ΔT_{ν,3}(d) - ½ (∇f(x)[d])² -
½ ∇f(x)[d] ∇²f(x)[d]²`. -/
theorem taylorDecrement_three_targetMerit_of_eq {x : ℝⁿ} {t : ℝ} (hf : ContDiffAt ℝ 3 f x)
    (hc : ContDiffAt ℝ 3 c x) (ht : f x = t) (d : ℝⁿ) :
    (ftaylorSeries ℝ (Constrained.targetMerit f c t) x).taylorDecrement 3 d =
      (ftaylorSeries ℝ (phi2 c) x).taylorDecrement 3 d - (fderiv ℝ f x d) ^ 2 / 2 -
        fderiv ℝ f x d * iteratedFDeriv ℝ 2 f x (fun _ => d) / 2 := by
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hc2 : ContDiffAt ℝ 2 c x := hc.of_le (by norm_num)
  have h2 := taylorDecrement_two_targetMerit_of_eq hf2 hc2 ht d
  rw [FormalMultilinearSeries.taylorDecrement_three, FormalMultilinearSeries.taylorDecrement_three]
  rw [FormalMultilinearSeries.taylorDecrement_two, FormalMultilinearSeries.taylorDecrement_two]
    at h2
  have h3 : iteratedFDeriv ℝ 3 (Constrained.targetMerit f c t) x (fun _ => d) =
      iteratedFDeriv ℝ 3 (phi2 c) x (fun _ => d) +
        3 * iteratedFDeriv ℝ 2 f x (fun _ => d) * fderiv ℝ f x d := by
    rw [Constrained.iteratedFDeriv_three_targetMerit_apply hf hc, phi2_eq_targetMerit,
      Constrained.iteratedFDeriv_three_targetMerit_apply contDiffAt_const hc, ← ht]
    simp
  simp only [ftaylorSeries] at h2 ⊢
  rw [h3]
  linarith

private theorem abs_fderiv_le {x d : ℝⁿ} {δ : ℝ} (hd : d ∈ closedBall (0 : ℝⁿ) δ) :
    |fderiv ℝ f x d| ≤ ‖fderiv ℝ f x‖ * δ := by
  rw [← Real.norm_eq_abs]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
    (mem_closedBall_zero_iff.1 hd) (norm_nonneg _))

private theorem abs_iteratedFDeriv_two_le {x d : ℝⁿ} {δ : ℝ} (hd : d ∈ closedBall (0 : ℝⁿ) δ) :
    |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ ‖iteratedFDeriv ℝ 2 f x‖ * δ ^ 2 := by
  rw [← Real.norm_eq_abs]
  refine ((iteratedFDeriv ℝ 2 f x).le_opNorm _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
    (mem_closedBall_zero_iff.1 hd) 2) (norm_nonneg _)

/-- Second-order measures of `ν` from those of `μ` at a point where `f(x) = t`: on
`S ∩ ker ∇f(x)` they agree, and on `S` they differ by at most `(‖∇f(x)‖ δ)²/2`. -/
theorem taylorMeasure_phi2_two_le_of_eq {x : ℝⁿ} {t δ B : ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hc : ContDiffAt ℝ 2 c x) (ht : f x = t) (hδ : 0 ≤ δ) {S : Set ℝⁿ} (hS : (0 : ℝⁿ) ∈ S)
    (hμ : Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit f c t) x) 2 δ S ≤
      B) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) x) 2 δ
        (S ∩ {d | fderiv ℝ f x d = 0}) ≤ B ∧
      Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) x) 2 δ S ≤
        B + (‖fderiv ℝ f x‖ * δ) ^ 2 / 2 := by
  constructor
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS, by simp⟩
      fun d hd => ?_
    have h := taylorDecrement_two_targetMerit_of_eq hf hc ht d
    have hd0 : fderiv ℝ f x d = 0 := hd.2.2
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (Constrained.targetMerit f c t) x) 2 (S := S) ⟨hd.1, hd.2.1⟩
    rw [hd0] at h
    linarith
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS⟩ fun d hd => ?_
    have h := taylorDecrement_two_targetMerit_of_eq hf hc ht d
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (Constrained.targetMerit f c t) x) 2 (S := S) hd
    have hg : (fderiv ℝ f x d) ^ 2 ≤ (‖fderiv ℝ f x‖ * δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_fderiv_le hd.1) 2
    linarith

/-- Third-order measures of `ν` from those of `μ` at a point where `f(x) = t`: on
`S ∩ ker ∇f(x)` they agree, and on `S` they differ by at most
`(‖∇f(x)‖ δ)²/2 + ‖∇f(x)‖ δ ‖∇²f(x)‖ δ²/2`. -/
theorem taylorMeasure_phi2_three_le_of_eq {x : ℝⁿ} {t δ B : ℝ} (hf : ContDiffAt ℝ 3 f x)
    (hc : ContDiffAt ℝ 3 c x) (ht : f x = t) (hδ : 0 ≤ δ) {S : Set ℝⁿ} (hS : (0 : ℝⁿ) ∈ S)
    (hμ : Optimization.taylorMeasure (ftaylorSeries ℝ (Constrained.targetMerit f c t) x) 3 δ S ≤
      B) :
    Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) x) 3 δ
        (S ∩ {d | fderiv ℝ f x d = 0}) ≤ B ∧
      Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) x) 3 δ S ≤
        B + (‖fderiv ℝ f x‖ * δ) ^ 2 / 2 +
          ‖fderiv ℝ f x‖ * δ * (‖iteratedFDeriv ℝ 2 f x‖ * δ ^ 2) / 2 := by
  constructor
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS, by simp⟩
      fun d hd => ?_
    have h := taylorDecrement_three_targetMerit_of_eq hf hc ht d
    have hd0 : fderiv ℝ f x d = 0 := hd.2.2
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (Constrained.targetMerit f c t) x) 3 (S := S) ⟨hd.1, hd.2.1⟩
    rw [hd0] at h
    linarith
  · rw [Optimization.taylorMeasure]
    refine Optimization.decrementMeasure_le ⟨0, mem_closedBall_self hδ, hS⟩ fun d hd => ?_
    have h := taylorDecrement_three_targetMerit_of_eq hf hc ht d
    have hμd := Optimization.taylorDecrement_le_taylorMeasure
      (ftaylorSeries ℝ (Constrained.targetMerit f c t) x) 3 (S := S) hd
    have h1 := abs_fderiv_le (f := f) (x := x) hd.1
    have h2 := abs_iteratedFDeriv_two_le (f := f) (x := x) hd.1
    have hg : (fderiv ℝ f x d) ^ 2 ≤ (‖fderiv ℝ f x‖ * δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hgh : fderiv ℝ f x d * iteratedFDeriv ℝ 2 f x (fun _ => d) ≤
        ‖fderiv ℝ f x‖ * δ * (‖iteratedFDeriv ℝ 2 f x‖ * δ ^ 2) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    linarith

/-- `τ⁻¹ ε ‖r‖ δ^j/j! = ε ‖(1, y)‖ δ^j/j!` for `τ = f(x) - t > 0` and `y = -c(x)/τ`. -/
private theorem inv_mul_le_of_le {x : ℝⁿ} {t a ε δ : ℝ} {j : ℕ} (ht : t < f x)
    (hφ : a ≤ ε * Constrained.targetResidual f c t x * δ ^ j / j !) :
    (f x - t)⁻¹ * a ≤
      ε * √(1 + ‖Constrained.targetMultiplier f c t x‖ ^ 2) * δ ^ j / j ! := by
  have hτ : 0 < f x - t := sub_pos.2 ht
  have hdiv := Constrained.targetResidual_div_eq_sqrt (f := f) (c := c) ht
  rw [add_comm (1 : ℝ)]
  calc (f x - t)⁻¹ * a ≤ (f x - t)⁻¹ * (ε * Constrained.targetResidual f c t x * δ ^ j / j !) :=
        mul_le_mul_of_nonneg_left hφ (inv_nonneg.2 hτ.le)
    _ = ε * (Constrained.targetResidual f c t x / (f x - t)) * δ ^ j / j ! := by
        field_simp
    _ = _ := by rw [hdiv]

/-- **Lemma 14.3.5** of [cartis2022evaluation] (consequences of the termination of TPqp-GC),
**corrected**. Assume c.D1pLB.X and f.D1pLB.X on `X₀` with `q ≤ p`. For a TPqp-GC run:

* (Phase-1 exit, (14.3.41)) if `‖c(x₁)‖ > θε₀`, then
  `φ^{δ_j}_{ν,X(x₁),j}(x₁) ≤ ε_j ‖c(x₁)‖ δ_j^j/j!` for `j ∈ [1 : q]`, with the radii
  `δ ∈ (0, 1]^q` of Phase 1;
* (Phase-2 exit) if Phase 2 terminates at `k_ε` with output `x_ε = x_{k_ε+1}`,
  `t_ε = targetOut k_ε` and radii `δ = δ_{k_ε+1}`, then `t_ε ≤ f(x_ε)` (14.3.48) and:
  - if `f(x_ε) = t_ε`: `θε₀ ≤ ‖c(x_ε)‖ ≤ ε₀` and `φ^{δ_1}_{ν,X(x_ε),1}(x_ε) ≤ ε_1 ‖c(x_ε)‖ δ_1`
    (the first-order part of (14.3.41), with `≥ θε₀` instead of the printed `> θε₀`);
  - if `f(x_ε) > t_ε`, with `τ = f(x_ε) - t_ε` and `y_ε = -c(x_ε)/τ` (14.3.53):
    `‖c(x_ε)‖ ≤ ε₀`, `⟪y_ε, c(x_ε)⟫ ≤ 0`,
    (14.3.42) `φ^{δ_1}_{ℒ,X(x_ε),1}(x_ε, y_ε) ≤ ε_1 ‖(1, y_ε)‖ δ_1`; if `q ≥ 2`,
    (14.3.44) `φ^{δ_2}_{ℒ,M(x_ε),2} ≤ ½ ε_2 ‖(1, y_ε)‖ δ_2²` and the corrected (14.3.43)
    `φ^{δ_2}_{ℒ,T(x_ε),2} ≤ ½ ε_2 ‖(1, y_ε)‖ δ_2² + (‖∇f(x_ε)‖ δ_2)²/(2τ)`; if `q ≥ 3`,
    (14.3.47) `φ^{δ_3}_{ℒ,M(x_ε),3} ≤ ⅙ ε_3 ‖(1, y_ε)‖ δ_3³` and the corrected (14.3.46)
    `φ^{δ_3}_{ℒ,T(x_ε),3} ≤ ⅙ ε_3 ‖(1, y_ε)‖ δ_3³ +
      (‖∇f(x_ε)‖ δ_3 + ‖∇²f(x_ε)‖ δ_3²) ‖∇f(x_ε)‖ δ_3/(2τ)`.

Here `T(x) = X(x) ∩ ker ∇c(x)`, `M(x) = T(x) ∩ ker ∇f(x)` (14.3.45) and
`‖(1, y)‖ = √(1 + ‖y‖²)`. Corrections: the printed (14.3.43), (14.3.46) bound the extra terms by
`φ_{ℒ,1} ‖∇f‖ δ`, which is invalid (on `T(x_ε)`, `∇ℒ[d] = ∇f[d]`, not `∇f[d]/τ`; a
counterexample is described in the module documentation); when `f(x_ε) = t_ε`, Phase 2 only
gives `‖c(x_ε)‖ ≥ θε₀`, and the measures of `ν` and `μ` agree only at first order: for
`j = 2, 3` they agree on `X(x_ε) ∩ ker ∇f(x_ε)`, and on `X(x_ε)` they differ by the terms
`(‖∇f‖δ)²/2` and `‖∇f‖δ ‖∇²f‖δ²/2` (`taylorMeasure_phi2_two_le_of_eq`,
`taylorMeasure_phi2_three_le_of_eq`); so the higher-order part of (14.3.41) holds only in these
corrected forms. Only the smoothness parts of c.D1pLB.X and f.D1pLB.X (`C^q` near `x_ε`) are
used. -/
theorem lemma_14_3_5 (h : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D) {Lc Bc Lf Bf : ℕ → ℝ}
    (hcB : AssumptionCD1pLBX c X X₀ p Lc Bc) (hfB : AssumptionD1pLBX f X X₀ p Lf Bf)
    (hqp : q ≤ p) :
    (θ * ε 0 < ‖c (xP k₁)‖ →
      (∀ j ∈ Finset.Icc 1 q, 0 < δP k₁ j ∧ δP k₁ j ≤ 1) ∧
      ∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (xP k₁)) j
        (δP k₁ j) {d | xP k₁ + d ∈ X} ≤ ε j * ‖c (xP k₁)‖ * δP k₁ j ^ j / j !) ∧
    (‖c (xP k₁)‖ ≤ θ * ε 0 → ∀ kε, D.IsEnd f c X q θ ε kε →
      D.targetOut f c θ ε kε ≤ f (D.x (kε + 1)) ∧
      (f (D.x (kε + 1)) = D.targetOut f c θ ε kε →
        θ * ε 0 ≤ ‖c (D.x (kε + 1))‖ ∧ ‖c (D.x (kε + 1))‖ ≤ ε 0 ∧
        (1 ≤ q → Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (D.x (kε + 1))) 1
          (D.δ (kε + 1) 1) {d | D.x (kε + 1) + d ∈ X} ≤
            ε 1 * ‖c (D.x (kε + 1))‖ * D.δ (kε + 1) 1) ∧
        (2 ≤ q →
          Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (D.x (kε + 1))) 2
              (D.δ (kε + 1) 2)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ f (D.x (kε + 1)) d = 0}) ≤
            ε 2 * ‖c (D.x (kε + 1))‖ * D.δ (kε + 1) 2 ^ 2 / 2 ∧
          Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (D.x (kε + 1))) 2
              (D.δ (kε + 1) 2) {d | D.x (kε + 1) + d ∈ X} ≤
            ε 2 * ‖c (D.x (kε + 1))‖ * D.δ (kε + 1) 2 ^ 2 / 2 +
              (‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 2) ^ 2 / 2) ∧
        (3 ≤ q →
          Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (D.x (kε + 1))) 3
              (D.δ (kε + 1) 3)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ f (D.x (kε + 1)) d = 0}) ≤
            ε 3 * ‖c (D.x (kε + 1))‖ * D.δ (kε + 1) 3 ^ 3 / 6 ∧
          Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (D.x (kε + 1))) 3
              (D.δ (kε + 1) 3) {d | D.x (kε + 1) + d ∈ X} ≤
            ε 3 * ‖c (D.x (kε + 1))‖ * D.δ (kε + 1) 3 ^ 3 / 6 +
              (‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 3) ^ 2 / 2 +
              ‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 3 *
                (‖iteratedFDeriv ℝ 2 f (D.x (kε + 1))‖ * D.δ (kε + 1) 3 ^ 2) / 2)) ∧
      (D.targetOut f c θ ε kε < f (D.x (kε + 1)) →
        ‖c (D.x (kε + 1))‖ ≤ ε 0 ∧
        ⟪Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1)),
          c (D.x (kε + 1))⟫ ≤ 0 ∧
        (1 ≤ q → Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c
            (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
            (D.x (kε + 1))) 1 (D.δ (kε + 1) 1) {d | D.x (kε + 1) + d ∈ X} ≤
          ε 1 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
            (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 1) ∧
        (2 ≤ q →
          Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 2 (D.δ (kε + 1) 2)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ c (D.x (kε + 1)) d = 0} ∩
                {d | fderiv ℝ f (D.x (kε + 1)) d = 0}) ≤
            ε 2 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
              (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 2 ^ 2 / 2 ∧
          Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 2 (D.δ (kε + 1) 2)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ c (D.x (kε + 1)) d = 0}) ≤
            ε 2 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
              (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 2 ^ 2 / 2 +
              (‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 2) ^ 2 /
                (2 * (f (D.x (kε + 1)) - D.targetOut f c θ ε kε))) ∧
        (3 ≤ q →
          Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 3 (D.δ (kε + 1) 3)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ c (D.x (kε + 1)) d = 0} ∩
                {d | fderiv ℝ f (D.x (kε + 1)) d = 0}) ≤
            ε 3 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
              (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 3 ^ 3 / 6 ∧
          Optimization.taylorMeasure (ftaylorSeries ℝ (lagrangianFn f c
              (Constrained.targetMultiplier f c (D.targetOut f c θ ε kε) (D.x (kε + 1))))
              (D.x (kε + 1))) 3 (D.δ (kε + 1) 3)
              ({d | D.x (kε + 1) + d ∈ X} ∩ {d | fderiv ℝ c (D.x (kε + 1)) d = 0}) ≤
            ε 3 * √(1 + ‖Constrained.targetMultiplier f c (D.targetOut f c θ ε kε)
              (D.x (kε + 1))‖ ^ 2) * D.δ (kε + 1) 3 ^ 3 / 6 +
              (‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 3 +
                ‖iteratedFDeriv ℝ 2 f (D.x (kε + 1))‖ * D.δ (kε + 1) 3 ^ 2) *
                (‖fderiv ℝ f (D.x (kε + 1))‖ * D.δ (kε + 1) 3) /
                (2 * (f (D.x (kε + 1)) - D.targetOut f c θ ε kε))))) := by
  refine ⟨fun hc => (h.phase1_exit hc).2, fun hc1 kε hend => ?_⟩
  have h2 := h.phase2 hc1
  set xε := D.x (kε + 1) with hxε
  set tε := D.targetOut f c θ ε kε with htε
  set δε := D.δ (kε + 1) with hδε
  obtain ⟨hθr, hr, hft, hcrit⟩ := h2.output_spec hend
  obtain ⟨hk1, -, hbef⟩ := hend
  have hxX : xε ∈ X := h2.mem_succ kε hk1 hbef
  have hrad := h2.radius_mem kε hk1 hbef
  have hS : (0 : ℝⁿ) ∈ {d | xε + d ∈ X} := by simpa using hxX
  have hfC : ∀ {i : ℕ}, i ≤ q → ContDiffAt ℝ i f xε := fun hi =>
    (hfB.contDiffOn.contDiffAt (hfB.isOpen.mem_nhds (hfB.subset hxX))).of_le
      (by exact_mod_cast hi.trans hqp)
  have hcC : ∀ {i : ℕ}, i ≤ q → ContDiffAt ℝ i c xε := fun hi =>
    (hcB.contDiffOn.contDiffAt (hcB.isOpen.mem_nhds (hcB.subset hxX))).of_le
      (by exact_mod_cast hi.trans hqp)
  refine ⟨hft, fun heq => ?_, fun hlt => ?_⟩
  · -- `f(x_ε) = t_ε`
    have hrc : Constrained.targetResidual f c tε xε = ‖c xε‖ := by
      rw [← heq]; exact Constrained.targetResidual_self
    rw [hrc] at hθr hr
    refine ⟨hθr, hr, fun hq => ?_, fun hq => ?_, fun hq => ?_⟩
    · have hj : (1 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
      have := hcrit 1 hj
      rw [taylorMeasure_one_targetMerit_of_eq ((hfC hq).differentiableAt one_ne_zero)
        ((hcC hq).differentiableAt one_ne_zero) heq, hrc] at this
      simpa using this
    · have hj : (2 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by norm_num, hq⟩
      have := hcrit 2 hj
      rw [hrc] at this
      norm_num [Nat.factorial] at this
      exact taylorMeasure_phi2_two_le_of_eq (hfC hq) (hcC hq) heq (hrad 2 hj).1.le hS this
    · have hj : (3 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by norm_num, hq⟩
      have := hcrit 3 hj
      rw [hrc] at this
      norm_num [Nat.factorial] at this
      exact taylorMeasure_phi2_three_le_of_eq (hfC hq) (hcC hq) heq (hrad 3 hj).1.le hS this
  · -- `f(x_ε) > t_ε`
    have hτ : 0 < f xε - tε := sub_pos.2 hlt
    refine ⟨Constrained.norm_le_targetResidual.trans hr,
      Constrained.inner_targetMultiplier_nonpos hlt.le, fun hq => ?_, fun hq => ?_,
      fun hq => ?_⟩
    · have hj : (1 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
      have hφ := hcrit 1 hj
      rw [Constrained.taylorMeasure_lagrangian_one_eq ((hfC hq).differentiableAt one_ne_zero)
        ((hcC hq).differentiableAt one_ne_zero) hlt]
      simpa using inv_mul_le_of_le hlt hφ
    · have hj : (2 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by norm_num, hq⟩
      have hφ := hcrit 2 hj
      have hδ := (hrad 2 hj).1
      have hG : ∀ d ∈ closedBall (0 : ℝⁿ) (δε 2) ∩
          ({d | xε + d ∈ X} ∩ {d | fderiv ℝ c xε d = 0}),
          |fderiv ℝ f xε d| ≤ ‖fderiv ℝ f xε‖ * δε 2 := fun d hd => by
        rw [← Real.norm_eq_abs]
        exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
          (mem_closedBall_zero_iff.1 hd.1) (norm_nonneg _))
      refine ⟨(Constrained.taylorMeasure_lagrangian_two_le_of_ker (hfC hq) (hcC hq) hlt hδ.le
        hS).trans ?_, (Constrained.taylorMeasure_lagrangian_two_le (hfC hq) (hcC hq) hlt hδ.le
        hS hG).trans ?_⟩
      · simpa using inv_mul_le_of_le hlt hφ
      · rw [mul_add]
        have := inv_mul_le_of_le hlt hφ
        have e : (f xε - tε)⁻¹ * ((‖fderiv ℝ f xε‖ * δε 2) ^ 2 / 2) =
            (‖fderiv ℝ f xε‖ * δε 2) ^ 2 / (2 * (f xε - tε)) := by
          field_simp
        simp only [Nat.factorial_two, Nat.cast_ofNat] at this
        linarith
    · have hj : (3 : ℕ) ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨by norm_num, hq⟩
      have hφ := hcrit 3 hj
      have hδ := (hrad 3 hj).1
      have hG : ∀ d ∈ closedBall (0 : ℝⁿ) (δε 3) ∩
          ({d | xε + d ∈ X} ∩ {d | fderiv ℝ c xε d = 0}),
          |fderiv ℝ f xε d| ≤ ‖fderiv ℝ f xε‖ * δε 3 := fun d hd => by
        rw [← Real.norm_eq_abs]
        exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
          (mem_closedBall_zero_iff.1 hd.1) (norm_nonneg _))
      have hH : ∀ d ∈ closedBall (0 : ℝⁿ) (δε 3) ∩
          ({d | xε + d ∈ X} ∩ {d | fderiv ℝ c xε d = 0}),
          |iteratedFDeriv ℝ 2 f xε (fun _ => d)| ≤
            ‖iteratedFDeriv ℝ 2 f xε‖ * δε 3 ^ 2 := fun d hd => by
        rw [← Real.norm_eq_abs]
        refine ((iteratedFDeriv ℝ 2 f xε).le_opNorm _).trans ?_
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
          (mem_closedBall_zero_iff.1 hd.1) 2) (norm_nonneg _)
      refine ⟨(Constrained.taylorMeasure_lagrangian_three_le_of_ker (hfC hq) (hcC hq) hlt hδ.le
        hS).trans ?_, (Constrained.taylorMeasure_lagrangian_three_le (hfC hq) (hcC hq) hlt hδ.le
        hS hG hH).trans ?_⟩
      · have := inv_mul_le_of_le hlt hφ
        simpa [Nat.factorial] using this
      · rw [mul_add]
        have := inv_mul_le_of_le hlt hφ
        have e : (f xε - tε)⁻¹ * ((‖fderiv ℝ f xε‖ * δε 3 +
              ‖iteratedFDeriv ℝ 2 f xε‖ * δε 3 ^ 2) * (‖fderiv ℝ f xε‖ * δε 3) / 2) =
            (‖fderiv ℝ f xε‖ * δε 3 + ‖iteratedFDeriv ℝ 2 f xε‖ * δε 3 ^ 2) *
              (‖fderiv ℝ f xε‖ * δε 3) / (2 * (f xε - tε)) := by
          field_simp
        have h6 : ((3 : ℕ)! : ℝ) = 6 := by norm_num [Nat.factorial]
        rw [h6] at this
        linarith

/-- **Lemma 14.3.7** of [cartis2022evaluation] (evaluation complexity of Phase 1 of TPqp-GC, with
the correction of Theorem 14.3.4). Phase 1 terminates at `x₁` with `‖c(x₁)‖ ≤ θε₀` or
`φ^{δ_j}_{ν,X(x₁),j}(x₁) ≤ ε_j ‖c(x₁)‖ δ_j^j/j!` for `j ∈ [1 : q]` and some `δ ∈ (0, 1]^q`
(14.3.64). If the cost of the `k`-th INNER call of Phase 1 (evaluations of `c`, or of its
derivatives) satisfies the contract (14.3.20) (resp. (14.3.21)) for `ν` with constant `κ ≥ 0`
(by Lemma 14.3.6(i) such constants exist depending on the constants of c.D1pLB.X and on
`‖c(x₀)‖`) and exponents `π_j > 1`, then the total cost of Phase 1 is at most
`½ κ ‖c(x₀)‖ ∑_{j=1}^q β₁^{1-2π_j}/(β₁^{1-π_j} - 1) θ^{1-π_j} ε₀^{1-π_j} ε_j^{-π_j}`
((14.3.65)–(14.3.66) with `∑_j` in place of `max_j`). -/
theorem lemma_14_3_7 (h : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D) (hθ : 0 < θ)
    {π : ℕ → ℝ} (hπ : ∀ j ∈ Finset.Icc 1 q, 1 < π j) {κ : ℝ} (hκ : 0 ≤ κ) {cost : ℕ → ℝ}
    (hcost : ∀ k ∈ Finset.Icc 1 k₁, cost k ≤ innerEvalBound κ π q (phi2 c (xP (k - 1)))
      (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j)) :
    (‖c (xP k₁)‖ ≤ θ * ε 0 ∨ ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 < δ' j ∧ δ' j ≤ 1) ∧
      ∀ j ∈ Finset.Icc 1 q, Optimization.taylorMeasure (ftaylorSeries ℝ (phi2 c) (xP k₁)) j
        (δ' j) {d | xP k₁ + d ∈ X} ≤ ε j * ‖c (xP k₁)‖ * δ' j ^ j / j !) ∧
    ∑ k ∈ Finset.Icc 1 k₁, cost k ≤
      1 / 2 * κ * ‖c (x₀)‖ * ∑ j ∈ Finset.Icc 1 q,
        β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) * θ ^ (1 - π j) * ε 0 ^ (1 - π j) *
          ε j ^ (-π j) := by
  have hε₀ : 0 < ε 0 := by
    have := h.phase1.ε_pos 0 (by simp)
    rw [phase1Tol_zero] at this
    exact pos_of_mul_pos_right this hθ.le
  refine ⟨?_, ?_⟩
  · rcases h.phase1_end.1 with h0 | ⟨hk1, hcrit⟩
    · exact Or.inl (by simpa using h0)
    · refine Or.inr ⟨δP k₁, h.phase1.radius_mem k₁ hk1 h.phase1_end.2, fun j hj => ?_⟩
      have := hcrit j hj
      rwa [phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega)] at this
  · have hmain := theorem_14_3_4 h.phase1 h.phase1_end hπ hκ hcost
    rw [h.start] at hmain
    refine hmain.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [phase1Tol_zero, phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega),
      Real.mul_rpow hθ.le hε₀.le]
    ring

end Termination


/-! ### Lemma 14.3.8 and Theorem 14.3.9: evaluation complexity of TPqp-GC -/

namespace TPqpSeq

variable (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (θ : ℝ) (ε : ℕ → ℝ)
  (D : TPqpSeq n)

open Classical in
/-- The number of successful iterations of the `k`-th INNER call. -/
noncomputable def succCount (k : ℕ) : ℕ := ((Finset.range (D.e k)).filter (D.succ k)).card

/-- A *good* inner iteration `(k, i)` ([cartis2022evaluation], proof of Lemma 14.3.8, as for
Lemma 7.2.6): it is successful, its decrease is guaranteed (INNER does not stop at the new iterate,
`i + 1 < e_k`, or the call ends at a point failing the third test of (14.3.32)), and its new
iterate has residual `‖r(·, t_k)‖ ≥ θε₀`. -/
def IsGood (k i : ℕ) : Prop :=
  i < D.e k ∧ D.succ k i ∧
    (i + 1 < D.e k ∨ ¬ meritCrit f c X q ε (D.t k) (D.x (k + 1)) (D.δ (k + 1))) ∧
    θ * ε 0 ≤ Constrained.targetResidual f c (D.t k) (D.xi k (i + 1))

open Classical in
/-- The number of good iterations of the `k`-th INNER call. -/
noncomputable def goodCount (k : ℕ) : ℕ :=
  ((Finset.range (D.e k)).filter (D.IsGood f c X q θ ε k)).card

open Classical in
/-- The number of outer iterations of `𝒦_a` among `[1, K)`. -/
noncomputable def kaCount (K : ℕ) : ℕ := ((Finset.Ico 1 K).filter (D.IsKa f c θ ε)).card

/-- A *bad* outer iteration: `k ∈ 𝒦_b` and the new iterate passes the third test of (14.3.32) for
the old target, `meritCrit` at `(x_{k+1}, t_k)` (as for Lemma 7.2.6). Its INNER call need not
contain a good iteration, and the book gives no bound on the number of such iterations. -/
def IsBad (k : ℕ) : Prop :=
  D.IsKb f c θ ε k ∧ meritCrit f c X q ε (D.t k) (D.x (k + 1)) (D.δ (k + 1))

open Classical in
/-- The number of bad outer iterations among `[1, K)`. -/
noncomputable def badCount (K : ℕ) : ℕ :=
  ((Finset.Ico 1 K).filter (D.IsBad f c X q θ ε)).card

/-- The number of evaluations of `(f, c)` in Phase 2 up to outer iteration `k`:
`1 + ∑_{j ∈ [1, k]} e_j` (one at `x₁` and one per inner iteration). -/
noncomputable def funEvals (k : ℕ) : ℕ := 1 + ∑ j ∈ Finset.Icc 1 k, D.e j

/-- The number of evaluations of the derivatives of `(f, c)` in Phase 2 up to outer iteration
`k`: one at `x₁` and one per successful inner iteration. -/
noncomputable def derivEvals (k : ℕ) : ℕ := 1 + ∑ j ∈ Finset.Icc 1 k, D.succCount j

end TPqpSeq

/-- **The INNER contract of Phase 2** of TPqp-GC ([cartis2022evaluation], Lemmas 14.2.2–14.2.3
applied to `μ(·, t_k)`, with constants independent of `t_k` by Lemma 14.3.6(ii)): for every
outer iteration `k ≥ 1` reached,
(count) `e_k ≤ κ_uns |𝒮_k| + κ_unc` (14.2.13), `𝒮_k` the successful inner iterations;
(stay) unsuccessful inner iterations do not move;
(decrease) every successful inner iteration `i` that is not followed by the termination of INNER
(`i + 1 < e_k`), or that ends a call at a point failing the third test of (14.3.32), decreases
`μ(·, t_k)` by at least `κ_decr min_l (β ‖r(x_k, t_k)‖ ε_l)^{π_l}` ((14.2.11) for INNER called
with tolerances `β ‖r(x_k, t_k)‖ ε_l`; "so long as the third termination test in (14.3.32) has
not been satisfied", (B.14.21)). -/
structure IsInnerPhaseRun (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ) (θ β : ℝ)
    (ε : ℕ → ℝ) (D : TPqpSeq n) (κdecr κuns κunc : ℝ) (π : ℕ → ℝ) : Prop where
  count : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → (D.e k : ℝ) ≤ κuns * D.succCount k + κunc
  stay : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → ∀ i < D.e k, ¬ D.succ k i →
    D.xi k (i + 1) = D.xi k i
  decrease : ∀ k, 1 ≤ k → D.Before f c X q θ ε k → ∀ i < D.e k, D.succ k i →
    (i + 1 < D.e k ∨ ¬ meritCrit f c X q ε (D.t k) (D.x (k + 1)) (D.δ (k + 1))) →
    ∃ l ∈ Finset.Icc 1 q,
      κdecr * (β * Constrained.targetResidual f c (D.t k) (D.x k) * ε l) ^ π l ≤
        Constrained.targetMerit f c (D.t k) (D.xi k i) -
          Constrained.targetMerit f c (D.t k) (D.xi k (i + 1))

/-- The bound `G = κ^S (1 - θ) M` of (14.3.71) of [cartis2022evaluation] with
`κ^S = κ_decr⁻¹ (βθ)^{-π_max}` and `M ≥ max_l ε₀^{2-π_l} ε_l^{-π_l}`. -/
noncomputable def goodBound (κdecr β θ πmax M : ℝ) : ℝ :=
  κdecr⁻¹ * (β * θ) ^ (-πmax) * (1 - θ) * M

namespace IsTPqpGCPhase2

section Counting

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : ℝⁿ}
  {D : TPqpSeq n} {κdecr κuns κunc πmax M : ℝ} {π : ℕ → ℝ}

/-- The residual decrease `κ_decr (βθ)^{π_max} ε₀ / M` guaranteed by a good inner iteration. -/
private noncomputable def goodDecr (κdecr β θ πmax M ε₀ : ℝ) : ℝ :=
  κdecr * (β * θ) ^ πmax * ε₀ / M

/-- A good inner iteration decreases the residual `‖r(·, t_k)‖` by at least `goodDecr`. -/
private theorem resid_drop (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D)
    (hin : IsInnerPhaseRun f c X q θ β ε D κdecr κuns κunc π) (hκ : 0 < κdecr)
    (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) (hM0 : 0 < M)
    (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) {i : ℕ}
    (hi : D.IsGood f c X q θ ε k i) :
    goodDecr κdecr β θ πmax M (ε 0) ≤
      Constrained.targetResidual f c (D.t k) (D.xi k i) -
        Constrained.targetResidual f c (D.t k) (D.xi k (i + 1)) := by
  obtain ⟨hie, hsucc, hcont, hρj_ge⟩ := hi
  obtain ⟨l, hl, hdec⟩ := hin.decrease k hk1 hk i hie hsucc hcont
  have hε₀ := h.ε₀_pos
  have hεl := h.ε_pos' hl
  have hθ := h.θ_pos
  have hβ := h.β_pos
  have hβθ1 : β * θ ≤ 1 := by
    have := h.β_le_θ; have := h.θ_lt_one; nlinarith
  obtain ⟨hπ0, hπmax⟩ := hπ l hl
  set r := Constrained.targetResidual f c (D.t k) (D.x k)
  set ρi := Constrained.targetResidual f c (D.t k) (D.xi k i)
  set ρj := Constrained.targetResidual f c (D.t k) (D.xi k (i + 1))
  -- `θε₀ ≤ r ≤ ε₀`
  have hr_ge : θ * ε 0 ≤ r := by
    have := h.inner_residual_ge k hk1 hk 0 (by omega)
    rwa [h.inner_zero k hk1 hk] at this
  have hr_le : r ≤ ε 0 :=
    (h.isTargetSequence hk).residual_le h.θ_lt_one.le hε₀.le hk1 le_rfl
  have hρi : ρi ≤ r := by
    have := h.inner_resid_antitone hk1 hk (Nat.zero_le i) (by omega)
    rwa [h.inner_zero k hk1 hk] at this
  have hρji : ρj ≤ ρi := h.inner_resid_antitone hk1 hk (Nat.le_succ i) hie
  -- the merit decrease is at least `Dmin = κ (βθ)^{π_max} ε₀² / M`
  have hbase : (β * θ * (ε 0 * ε l)) ^ π l ≤ (β * r * ε l) ^ π l := by
    refine Real.rpow_le_rpow (by positivity) ?_ hπ0
    have : β * (θ * ε 0) * ε l ≤ β * r * ε l := by gcongr
    linarith
  have hpow : (β * θ) ^ πmax ≤ (β * θ) ^ π l :=
    Real.rpow_le_rpow_of_exponent_ge (by positivity) hβθ1 hπmax
  have hεε : ε 0 ^ 2 / M ≤ (ε 0 * ε l) ^ π l := by
    rw [div_le_iff₀ hM0]
    have hMl := hM l hl
    have e : (ε 0 * ε l) ^ π l * (ε 0 ^ (2 - π l) * ε l ^ (-π l)) = ε 0 ^ 2 := by
      rw [Real.mul_rpow hε₀.le hεl.le, Real.rpow_sub hε₀, Real.rpow_neg hεl.le]
      have : (0 : ℝ) < ε 0 ^ π l := Real.rpow_pos_of_pos hε₀ _
      have : (0 : ℝ) < ε l ^ π l := Real.rpow_pos_of_pos hεl _
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    calc ε 0 ^ 2 = (ε 0 * ε l) ^ π l * (ε 0 ^ (2 - π l) * ε l ^ (-π l)) := e.symm
      _ ≤ (ε 0 * ε l) ^ π l * M := by
          gcongr
  have hDmin : κdecr * (β * θ) ^ πmax * (ε 0 ^ 2 / M) ≤
      Constrained.targetMerit f c (D.t k) (D.xi k i) -
        Constrained.targetMerit f c (D.t k) (D.xi k (i + 1)) := by
    refine le_trans ?_ hdec
    rw [Real.mul_rpow (by positivity) (by positivity)] at hbase
    calc κdecr * (β * θ) ^ πmax * (ε 0 ^ 2 / M)
        ≤ κdecr * ((β * θ) ^ π l * (ε 0 * ε l) ^ π l) := by
          rw [mul_assoc]
          gcongr
      _ ≤ κdecr * (β * r * ε l) ^ π l := by gcongr
  -- from merits to residuals: `ρi² - ρj² ≥ 2 Dmin` and `ρi + ρj ≤ 2ε₀`
  rw [Constrained.targetMerit_eq, Constrained.targetMerit_eq] at hDmin
  have hsum_le : ρi + ρj ≤ 2 * ε 0 := by linarith
  have hgd : goodDecr κdecr β θ πmax M (ε 0) =
      κdecr * (β * θ) ^ πmax * (ε 0 ^ 2 / M) / ε 0 := by
    unfold goodDecr
    field_simp
  rw [hgd, div_le_iff₀ hε₀]
  have hd0 : 0 ≤ ρi - ρj := sub_nonneg.2 hρji
  nlinarith [mul_le_mul_of_nonneg_left hsum_le hd0]

end Counting

end IsTPqpGCPhase2


namespace IsTPqpGCPhase2

section Counting2

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : ℝⁿ}
  {D : TPqpSeq n} {κdecr κuns κunc πmax M : ℝ} {π : ℕ → ℝ}

/-- The good iterations of one INNER call telescope:
`|good_k| δ ≤ max(‖r(x_k, t_k)‖, θε₀) - max(‖r(x_{k+1}, t_k)‖, θε₀)`. -/
private theorem goodCount_mul_le (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D)
    (hin : IsInnerPhaseRun f c X q θ β ε D κdecr κuns κunc π) (hκ : 0 < κdecr)
    (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) (hM0 : 0 < M)
    (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) :
    (D.goodCount f c X q θ ε k : ℝ) * goodDecr κdecr β θ πmax M (ε 0) ≤
      max (Constrained.targetResidual f c (D.t k) (D.x k)) (θ * ε 0) -
        max (Constrained.targetResidual f c (D.t k) (D.x (k + 1))) (θ * ε 0) := by
  classical
  have := Optimization.card_mul_le_sub_of_decrease
    («φ» := fun j => max (Constrained.targetResidual f c (D.t k) (D.xi k j)) (θ * ε 0))
    (N := D.e k) (T := (Finset.range (D.e k)).filter (D.IsGood f c X q θ ε k))
    (c := goodDecr κdecr β θ πmax M (ε 0)) (Finset.filter_subset _ _)
    (fun j hj => max_le_max (h.inner_resid_antitone hk1 hk j.le_succ hj) le_rfl)
    (fun j hj => by
      have hg := (Finset.mem_filter.1 hj).2
      have hd := resid_drop h hin hκ hπ hM0 hM hk1 hk hg
      have h1 := hg.2.2.2
      have h2 := h.inner_resid_antitone hk1 hk j.le_succ hg.1
      rw [max_eq_left h1, max_eq_left (h1.trans h2)]
      exact hd)
  rw [h.inner_zero k hk1 hk, h.inner_end k hk1 hk] at this
  convert this using 2
  unfold TPqpSeq.goodCount
  congr

/-- The good inner iterations of the outer iterations `[1, K]` number at most
`G (|𝒦_a ∩ [1, K)| + 1)`, `G = goodBound` (the corrected (14.3.71), summed over the blocks of
outer iterations between consecutive case-(a) iterations). -/
theorem sum_goodCount_le (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D)
    (hin : IsInnerPhaseRun f c X q θ β ε D κdecr κuns κunc π) (hκ : 0 < κdecr)
    (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) (hM0 : 0 < M)
    (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : D.Before f c X q θ ε K) :
    (∑ k ∈ Finset.Icc 1 K, D.goodCount f c X q θ ε k : ℝ) ≤
      goodBound κdecr β θ πmax M * (D.kaCount f c θ ε K + 1) := by
  classical
  have hε₀ := h.ε₀_pos
  have hθ := h.θ_pos
  have hβ := h.β_pos
  have hδ : 0 < goodDecr κdecr β θ πmax M (ε 0) := by unfold goodDecr; positivity
  have hsum := (h.isTargetSequence hK).sum_max_sub_le hθ.le h.θ_lt_one.le hε₀.le hK1
  have h1 : ∑ k ∈ Finset.Icc 1 K,
      (D.goodCount f c X q θ ε k : ℝ) * goodDecr κdecr β θ πmax M (ε 0) ≤
      ∑ k ∈ Finset.Icc 1 K,
        (max (Constrained.targetResidual f c (D.t k) (D.x k)) (θ * ε 0) -
          max (Constrained.targetResidual f c (D.t k) (D.x (k + 1))) (θ * ε 0)) :=
    Finset.sum_le_sum fun k hk => by
      rw [Finset.mem_Icc] at hk
      exact goodCount_mul_le h hin hκ hπ hM0 hM hk.1 (before_mono hK hk.2)
  rw [← Finset.sum_mul] at h1
  have hG : goodBound κdecr β θ πmax M = (1 - θ) * ε 0 / goodDecr κdecr β θ πmax M (ε 0) := by
    unfold goodBound goodDecr
    rw [Real.rpow_neg (by positivity)]
    have : 0 < (β * θ) ^ πmax := by positivity
    field_simp
  have hka : (D.kaCount f c θ ε K : ℝ) = ((Finset.Ico 1 K).filter (D.IsKa f c θ ε)).card := by
    unfold TPqpSeq.kaCount; congr
  rw [hG, div_mul_eq_mul_div, le_div_iff₀ hδ, hka]
  linarith

/-- Every successful inner iteration except possibly the last one of its call is good:
`|𝒮_k| ≤ |good_k| + 1`. -/
theorem succCount_le (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : D.Before f c X q θ ε k) : D.succCount k ≤ D.goodCount f c X q θ ε k + 1 := by
  classical
  unfold TPqpSeq.succCount TPqpSeq.goodCount
  refine (Finset.card_le_card (t := insert (D.e k - 1)
    ((Finset.range (D.e k)).filter (D.IsGood f c X q θ ε k))) ?_).trans
    (Finset.card_insert_le _ _)
  intro i hi
  rw [Finset.mem_filter, Finset.mem_range] at hi
  rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  by_cases hi1 : i + 1 < D.e k
  · exact Or.inr ⟨hi.1, hi.1, hi.2, Or.inl hi1, h.inner_residual_ge k hk1 hk (i + 1) hi1⟩
  · left; omega

/-- In a sequence whose unsuccessful steps do not move, a final point different from the first
was reached by a successful step: some successful `i < N` has `y_{i+1} = y_N`. -/
private theorem exists_last_succ {y : ℕ → ℝⁿ} {succ : ℕ → Prop} :
    ∀ N, (∀ i < N, ¬ succ i → y (i + 1) = y i) → y N ≠ y 0 →
      ∃ i < N, succ i ∧ y (i + 1) = y N := by
  intro N
  induction N with
  | zero => exact fun _ h0 => absurd rfl h0
  | succ N ih =>
    intro hstay hne
    by_cases hs : succ N
    · exact ⟨N, N.lt_succ_self, hs, rfl⟩
    · have heq := hstay N N.lt_succ_self hs
      obtain ⟨i, hi, hsi, hyi⟩ := ih (fun j hj => hstay j (hj.trans N.lt_succ_self))
        (heq ▸ hne)
      exact ⟨i, hi.trans N.lt_succ_self, hsi, hyi.trans heq.symm⟩

/-- An outer iteration of `𝒦_b` that is not bad contains a good inner iteration: its call moved
(`f(x_{k+1}) < t_k ≤ f(x_k)`), and its last successful iteration is good. -/
theorem one_le_goodCount (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D)
    (hin : IsInnerPhaseRun f c X q θ β ε D κdecr κuns κunc π) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : D.Before f c X q θ ε k) (hb : D.IsKb f c θ ε k) (hnb : ¬ D.IsBad f c X q θ ε k) :
    1 ≤ D.goodCount f c X q θ ε k := by
  classical
  have hle : D.t k ≤ f (D.x k) := by
    have := (h.isTargetSequence hk).sub_target_nonneg hk1 le_rfl
    linarith
  have hne : D.xi k (D.e k) ≠ D.xi k 0 := by
    rw [h.inner_end k hk1 hk, h.inner_zero k hk1 hk]
    intro heq
    have := hb.2
    rw [heq] at this
    linarith
  obtain ⟨i, hi, hsucc, hxi⟩ := exists_last_succ (succ := D.succ k) (D.e k)
    (hin.stay k hk1 hk) hne
  rw [h.inner_end k hk1 hk] at hxi
  have hg : D.IsGood f c X q θ ε k i :=
    ⟨hi, hsucc, Or.inr fun hc => hnb ⟨hb, hc⟩, by rw [hxi]; exact hb.1⟩
  unfold TPqpSeq.goodCount
  exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hg⟩⟩

/-- The outer iterations: each `k ∈ [1, K)` is in `𝒦_a`, or bad, or contains a good inner
iteration, so `K ≤ |𝒦_a ∩ [1, K)| + |good iterations of [1, K]| + |bad ∩ [1, K)| + 1`. -/
theorem le_counts (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D)
    (hin : IsInnerPhaseRun f c X q θ β ε D κdecr κuns κunc π) {K : ℕ}
    (hK : D.Before f c X q θ ε K) :
    K ≤ D.kaCount f c θ ε K + ∑ k ∈ Finset.Icc 1 K, D.goodCount f c X q θ ε k +
      D.badCount f c X q θ ε K + 1 := by
  classical
  have := Constrained.le_card_add_sum_of_cover (D.IsKa f c θ ε) (D.IsBad f c X q θ ε)
    (D.goodCount f c X q θ ε) (K := K) fun k hk => by
      have hk' := Finset.mem_Ico.1 hk
      rcases isKa_or_isKb_of_not_stop (hK k hk'.1 hk'.2) with ha | hb
      · exact Or.inl ha
      · by_cases hbad : D.IsBad f c X q θ ε k
        · exact Or.inr (Or.inl hbad)
        · exact Or.inr (Or.inr (h.one_le_goodCount hin hk'.1 (before_mono hK hk'.2.le) hb hbad))
  unfold TPqpSeq.kaCount TPqpSeq.badCount
  convert this

end Counting2

end IsTPqpGCPhase2

section Complexity

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {θ β : ℝ} {ε : ℕ → ℝ} {x₁ : ℝⁿ}
  {D : TPqpSeq n} {κdecr κuns κunc πmax M : ℝ} {π : ℕ → ℝ}

/-- **Lemma 14.3.8** of [cartis2022evaluation] (bounds on the inner iterations of Phase 2),
**corrected**. Let the INNER calls of Phase 2 satisfy the contract `IsInnerPhaseRun` with
`κ_decr > 0`, exponents `0 ≤ π_l ≤ π_max`, and let `M > 0` bound
`ε₀^{2-π_l} ε_l^{-π_l}` for `l ∈ [1 : q]` (the book's `max_l`). For every outer iteration
`K ≥ 1` reached:
(i) the `k`-th call has at most `|good_k| + 1` successful iterations and
`e_k ≤ κ_uns |𝒮_k| + κ_unc` (`κ_unc` is paid per call, each INNER call being a fresh run);
(ii) the number of good inner iterations of `[1, K]` is at most
`G (|𝒦_a ∩ [1, K)| + 1)` with `G = κ^S (1 - θ) M`, `κ^S = κ_decr⁻¹ (βθ)^{-π_max}` (14.3.71)
(the book's per-block bound, summed over the at most `|𝒦_a ∩ [1, K)| + 1` blocks of outer
iterations between consecutive elements of `𝒦_a`);
(iii) `K ≤ |𝒦_a ∩ [1, K)| + |good iterations of [1, K]| + |bad ∩ [1, K)| + 1`.
The printed lemma bounds `|𝓘_k^s|` by `G` per block: this also counts the `i = 0` elements and
the last iterations of the INNER calls, which have no guaranteed decrease, and the number of bad
calls of `𝒦_b` (`TPqpSeq.IsBad`) is not bounded by the printed argument (as in Lemma 7.2.6). The
smoothness and boundedness assumptions of the book only serve to justify the contract
(Lemmas 14.2.2–14.2.3 and 14.3.6). -/
theorem lemma_14_3_8 (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D)
    (hin : IsInnerPhaseRun f c X q θ β ε D κdecr κuns κunc π) (hκ : 0 < κdecr)
    (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) (hM0 : 0 < M)
    (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : D.Before f c X q θ ε K) :
    (∀ k, 1 ≤ k → k ≤ K → D.succCount k ≤ D.goodCount f c X q θ ε k + 1 ∧
      (D.e k : ℝ) ≤ κuns * D.succCount k + κunc) ∧
    (∑ k ∈ Finset.Icc 1 K, D.goodCount f c X q θ ε k : ℝ) ≤
      goodBound κdecr β θ πmax M * (D.kaCount f c θ ε K + 1) ∧
    K ≤ D.kaCount f c θ ε K + ∑ k ∈ Finset.Icc 1 K, D.goodCount f c X q θ ε k +
      D.badCount f c X q θ ε K + 1 :=
  ⟨fun k hk1 hkK => ⟨h.succCount_le hk1 (IsTPqpGCPhase2.before_mono hK hkK),
    hin.count k hk1 (IsTPqpGCPhase2.before_mono hK hkK)⟩,
    h.sum_goodCount_le hin hκ hπ hM0 hM hK1 hK, h.le_counts hin hK⟩

/-- `|𝒦_a ∩ [1, K)| ≤ N_a = (f_up - f_low + 1)/((1 - θ)ε₀)` (Lemma 7.2.4 for TPqp-GC) under
f.B.Fb on `ℱ_{β_F} = {x ∈ X | ‖c(x)‖ ≤ β_F}` with `ε₀ ≤ β_F`. -/
theorem IsTPqpGCPhase2.kaCount_le (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) {βF flow fup : ℝ}
    (hB : Chapter07.AssumptionBFb f c X βF flow fup) (hεβ : ε 0 ≤ βF) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : D.Before f c X q θ ε K) :
    (D.kaCount f c θ ε K : ℝ) ≤ (fup - flow + 1) / ((1 - θ) * ε 0) := by
  classical
  have := (h.isTargetSequence hK).card_Ka_le h.θ_pos.le h.θ_lt_one h.ε₀_pos
    (h.ε_le_one 0 (by simp)) hK1 (X := X) (fun k hk1 hkK => h.x_mem k hk1 (before_mono hK hkK))
    (fun z hz hcz => hB z ⟨hz, hcz.trans hεβ⟩)
  unfold TPqpSeq.kaCount
  convert this

/-- **Theorem 14.3.9** of [cartis2022evaluation] (complexity of TPqp-GC), **corrected**. Let
the INNER calls of both phases satisfy their contracts: in Phase 1 the costs `nF₁ k`, `nD₁ k` of
the `k`-th call satisfy (14.3.20)–(14.3.21) for `ν` (constants `κF₁, κD₁ ≥ 0`, exponents
`π_j > 1`); in Phase 2 the calls satisfy `IsInnerPhaseRun` (`κ_decr > 0`, `π_j ≤ π_max`, `M` as in
Lemma 14.3.8). Assume f.B.Fb on `ℱ_{β_F}` with `ε₀ ≤ β_F`, and write
`N_a = (f_up - f_low + 1)/((1 - θ)ε₀)` (the book's `f_up - f_low - 1` is a sign slip) and
`G = κ^S (1 - θ) M` (Lemma 14.3.8). Then:
(Phase 1) the costs of Phase 1 are bounded by Lemma 14.3.7 (`#F₁`, `#D₁`);
(Phase 2) if Phase 2 is entered, (i) every outer iteration `K ≥ 1` reached satisfies
`K ≤ (N_a + 1)(G + 1) + n_bad(K)`, `n_bad(K)` the number of bad outer iterations in `[1, K)`;
(ii) if `n_bad` is bounded by `B`, Phase 2 terminates at some `k_ε ≤ (N_a + 1)(G + 1) + B`;
(iii) if Phase 2 terminates at `k_ε`, it uses at most `1 + G (N_a + 1) + k_ε` derivative
evaluations and at most `1 + κ_uns (G (N_a + 1) + k_ε) + κ_unc k_ε` evaluations of `(f, c)`.
With `n_bad` bounded independently of `ε`, the totals are
`O(max(ε₀^{-1}, max_j ε₀^{1-π_j} ε_j^{-π_j}))` for both function and derivative evaluations (the
book's derivative bound omits the `ε₀^{-1}` coming from at least one successful iteration per
outer iteration, and its `#F₂` omits the `1/(1 - θ)` of the `κ^C ε₀^{-1}` term); the book's
unconditional claim rests on the gap of Lemma 14.3.8. -/
theorem theorem_14_3_9 {β₁ : ℝ} {x₀ : ℝⁿ} {xP : ℕ → ℝⁿ} {δP : ℕ → ℕ → ℝ} {k₁ : ℕ}
    (h : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D) (hθ : 0 < θ)
    (hπ1 : ∀ j ∈ Finset.Icc 1 q, 1 < π j) {κF₁ κD₁ : ℝ} (hκF₁ : 0 ≤ κF₁) (hκD₁ : 0 ≤ κD₁)
    {nF₁ nD₁ : ℕ → ℝ}
    (hnF₁ : ∀ k ∈ Finset.Icc 1 k₁, nF₁ k ≤ innerEvalBound κF₁ π q (phi2 c (xP (k - 1)))
      (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j))
    (hnD₁ : ∀ k ∈ Finset.Icc 1 k₁, nD₁ k ≤ innerEvalBound κD₁ π q (phi2 c (xP (k - 1)))
      (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j))
    (hin : IsInnerPhaseRun f c X q θ β ε D κdecr κuns κunc π) (hκ : 0 < κdecr)
    (hκuns : 0 ≤ κuns) (hπ : ∀ l ∈ Finset.Icc 1 q, 0 ≤ π l ∧ π l ≤ πmax) (hM0 : 0 < M)
    (hM : ∀ l ∈ Finset.Icc 1 q, ε 0 ^ (2 - π l) * ε l ^ (-π l) ≤ M) {βF flow fup : ℝ}
    (hB : Chapter07.AssumptionBFb f c X βF flow fup) (hεβ : ε 0 ≤ βF) :
    (∑ k ∈ Finset.Icc 1 k₁, nF₁ k ≤ 1 / 2 * κF₁ * ‖c x₀‖ * ∑ j ∈ Finset.Icc 1 q,
        β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) * θ ^ (1 - π j) * ε 0 ^ (1 - π j) *
          ε j ^ (-π j)) ∧
    (∑ k ∈ Finset.Icc 1 k₁, nD₁ k ≤ 1 / 2 * κD₁ * ‖c x₀‖ * ∑ j ∈ Finset.Icc 1 q,
        β₁ ^ (1 - 2 * π j) / (β₁ ^ (1 - π j) - 1) * θ ^ (1 - π j) * ε 0 ^ (1 - π j) *
          ε j ^ (-π j)) ∧
    (‖c (xP k₁)‖ ≤ θ * ε 0 →
      (∀ K, 1 ≤ K → D.Before f c X q θ ε K →
        (K : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
          (goodBound κdecr β θ πmax M + 1) + D.badCount f c X q θ ε K) ∧
      (∀ Bb : ℝ, (∀ K, D.Before f c X q θ ε K → (D.badCount f c X q θ ε K : ℝ) ≤ Bb) →
        ∃ kε, D.IsEnd f c X q θ ε kε ∧
          (kε : ℝ) ≤ ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) *
            (goodBound κdecr β θ πmax M + 1) + Bb) ∧
      (∀ kε, D.IsEnd f c X q θ ε kε →
        (D.derivEvals kε : ℝ) ≤
          1 + goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) + kε ∧
        (D.funEvals kε : ℝ) ≤
          1 + κuns * (goodBound κdecr β θ πmax M * ((fup - flow + 1) / ((1 - θ) * ε 0) + 1) +
            kε) + κunc * kε)) := by
  classical
  refine ⟨(lemma_14_3_7 h hθ hπ1 hκF₁ hnF₁).2, (lemma_14_3_7 h hθ hπ1 hκD₁ hnD₁).2,
    fun hc1 => ?_⟩
  have h2 := h.phase2 hc1
  set Na := (fup - flow + 1) / ((1 - θ) * ε 0)
  set G := goodBound κdecr β θ πmax M
  have hε₀ := h2.ε₀_pos
  have hG : 0 ≤ G := by
    unfold G goodBound
    have := h2.θ_lt_one; have := h2.β_pos
    have : 0 ≤ 1 - θ := by linarith
    positivity
  have hgood : ∀ K, 1 ≤ K → D.Before f c X q θ ε K →
      (∑ k ∈ Finset.Icc 1 K, D.goodCount f c X q θ ε k : ℝ) ≤ G * (Na + 1) := by
    intro K hK1 hK
    have h1 := h2.sum_goodCount_le hin hκ hπ hM0 hM hK1 hK
    have h3 := h2.kaCount_le hB hεβ hK1 hK
    exact h1.trans (by gcongr)
  have hi : ∀ K, 1 ≤ K → D.Before f c X q θ ε K →
      (K : ℝ) ≤ (Na + 1) * (G + 1) + D.badCount f c X q θ ε K := by
    intro K hK1 hK
    have h1 : (K : ℝ) ≤ D.kaCount f c θ ε K +
        (∑ k ∈ Finset.Icc 1 K, D.goodCount f c X q θ ε k : ℝ) +
        D.badCount f c X q θ ε K + 1 := by exact_mod_cast h2.le_counts hin hK
    have h3 := h2.kaCount_le hB hεβ hK1 hK
    have h4 := hgood K hK1 hK
    nlinarith
  refine ⟨hi, fun Bb hBb => ?_, fun kε hend => ?_⟩
  · by_contra hno
    have hall : ∀ K, D.Before f c X q θ ε K := by
      intro K
      induction K with
      | zero => exact fun _ _ hj => absurd hj (Nat.not_lt_zero _)
      | succ K ih =>
        intro j hj1 hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact ih j hj1 hj
        · intro hstop
          exact hno ⟨j, ⟨hj1, hstop, ih⟩, (hi j hj1 ih).trans (by linarith [hBb j ih])⟩
    set K := ⌈(Na + 1) * (G + 1) + Bb⌉₊ + 1
    have h1 := hi K (by omega) (hall K)
    have h2' := hBb K (hall K)
    have h3 : (Na + 1) * (G + 1) + Bb < K := by
      have := Nat.le_ceil ((Na + 1) * (G + 1) + Bb)
      push_cast [K]
      linarith
    linarith
  · obtain ⟨hk1, -, hbef⟩ := hend
    have hgood' := hgood kε hk1 hbef
    have hsucc : (∑ k ∈ Finset.Icc 1 kε, D.succCount k : ℝ) ≤
        ∑ k ∈ Finset.Icc 1 kε, (D.goodCount f c X q θ ε k : ℝ) + kε := by
      have : ∑ k ∈ Finset.Icc 1 kε, D.succCount k ≤
          ∑ k ∈ Finset.Icc 1 kε, (D.goodCount f c X q θ ε k + 1) :=
        Finset.sum_le_sum fun k hk => h2.succCount_le (Finset.mem_Icc.1 hk).1
          (IsTPqpGCPhase2.before_mono hbef (Finset.mem_Icc.1 hk).2)
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one,
        Nat.add_sub_cancel] at this
      exact_mod_cast this
    have hD : (D.derivEvals kε : ℝ) = 1 + ∑ k ∈ Finset.Icc 1 kε, (D.succCount k : ℝ) := by
      unfold TPqpSeq.derivEvals
      push_cast
      rfl
    have hF : (D.funEvals kε : ℝ) ≤ 1 + ∑ k ∈ Finset.Icc 1 kε,
        (κuns * D.succCount k + κunc) := by
      unfold TPqpSeq.funEvals
      push_cast
      gcongr with k hk
      rw [Finset.mem_Icc] at hk
      exact hin.count k hk.1 (IsTPqpGCPhase2.before_mono hbef hk.2)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul] at hF
    refine ⟨by rw [hD]; linarith, hF.trans ?_⟩
    have : κuns * ∑ k ∈ Finset.Icc 1 kε, (D.succCount k : ℝ) ≤ κuns * (G * (Na + 1) + kε) :=
      mul_le_mul_of_nonneg_left (hsucc.trans (by linarith)) hκuns
    linarith

end Complexity


/-! ### Example 14.3.1 -/

section Example1431

/-- The objective `f(x) = x₁ + x₂² + x₂³ - x₃` of Example 14.3.1 (coordinates `x 0, x 1, x 2`). -/
noncomputable def example1431F : EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun x => x 0 + x 1 ^ 2 + x 1 ^ 3 - x 2
/-- The constraints `c(x) = (-x₁ - x₂² + x₁x₂ + x₃, x₁ + x₂² + x₁x₂ + x₃)` of Example 14.3.1. -/
noncomputable def example1431C : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2) := fun x =>
  !₂[-x 0 - x 1 ^ 2 + x 0 * x 1 + x 2, x 0 + x 1 ^ 2 + x 0 * x 1 + x 2]
/-- The tuple `s₁ = e₂`, `s₂ = -e₁`, `s₃ = e₃` of Example 14.3.1. -/
noncomputable def example1431Arc : ℕ → EuclideanSpace ℝ (Fin 3) := fun ℓ =>
  if ℓ = 1 then !₂[0, 1, 0] else if ℓ = 2 then !₂[-1, 0, 0] else if ℓ = 3 then !₂[0, 0, 1]
  else 0

/-- The polynomial arc of Example 14.3.1 is `α ↦ (-α², α, α³)`. -/
theorem example1431_arc_eq (α : ℝ) :
    (0 : EuclideanSpace ℝ (Fin 3)) + ∑ ℓ ∈ Finset.Icc 1 3, α ^ ℓ • example1431Arc ℓ =
      !₂[-α ^ 2, α, α ^ 3] := by
  rw [show (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} by decide]
  ext i; fin_cases i <;> simp [example1431Arc]

/-- The feasible set of Example 14.3.1 is the curve `{(-t², t, t³)}`. -/
theorem example1431C_eq_zero_iff (x : EuclideanSpace ℝ (Fin 3)) :
    example1431C x = 0 ↔ ∃ t : ℝ, x = !₂[-t ^ 2, t, t ^ 3] := by
  constructor
  · intro h
    have h0 : -x 0 - x 1 ^ 2 + x 0 * x 1 + x 2 = 0 := by
      simpa [example1431C] using congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
    have h1 : x 0 + x 1 ^ 2 + x 0 * x 1 + x 2 = 0 := by
      simpa [example1431C] using congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
    refine ⟨x 1, ?_⟩
    have e0 : x 0 = -x 1 ^ 2 := by linarith
    have e2 : x 2 = x 1 ^ 3 := by rw [e0] at h1; nlinarith
    ext i; fin_cases i <;> simp [e0, e2]
  · rintro ⟨t, rfl⟩
    ext i; fin_cases i <;> simp [example1431C] <;> ring


/-- With `y₀ = (-1, 0)`, the Lagrangian `f - ⟪y₀, c⟫` of Example 14.3.1 is `x₂³ + x₁x₂`. -/
theorem example1431_lagrangian_eq :
    lagrangianFn example1431F example1431C (!₂[-1, 0]) = fun x => x 1 ^ 3 + x 0 * x 1 := by
  funext x
  simp [lagrangianFn, example1431F, example1431C,
    EuclideanSpace.inner_eq_star_dotProduct,
    Fin.sum_univ_two, dotProduct]
  ring

/-- Polarization for a symmetric bilinear form on `Fin 2`-tuples. -/
private theorem bilin_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (hA : ∀ u v : E, A ![u, v] = A ![v, u]) (u v : E) :
    A ![u, v] = (A (fun _ => u + v) - A (fun _ => u) - A (fun _ => v)) / 2 := by
  have hl : ∀ a b c : E, A ![a + b, c] = A ![a, c] + A ![b, c] := fun a b c => by
    have := A.map_update_add ![a, c] 0 a b
    have e : ∀ y : E, Function.update ![a, c] 0 y = ![y, c] := fun y => by
      funext i; fin_cases i <;> rfl
    rwa [e, e, e] at this
  have hr : ∀ a b c : E, A ![c, a + b] = A ![c, a] + A ![c, b] := fun a b c => by
    have := A.map_update_add ![c, a] 1 a b
    have e : ∀ y : E, Function.update ![c, a] 1 y = ![c, y] := fun y => by
      funext i; fin_cases i <;> rfl
    rwa [e, e, e] at this
  have hd : ∀ w : E, A (fun _ => w) = A ![w, w] := fun w => by
    congr 1; funext i; fin_cases i <;> rfl
  rw [hd, hd, hd, hl, hr, hr, hA v u]
  ring

/-- The mixed second and the third derivative of the Lagrangian in Example 14.3.1:
`∇²ℒ(0, y₀)[s₁, s₂] = -1` and `(1/6) ∇³ℒ(0, y₀)[s₁]³ = 1`, so (14.3.6) holds with both terms
nonzero. -/
theorem example1431_derivs :
    iteratedFDeriv ℝ 2 (lagrangianFn example1431F example1431C (!₂[-1, 0])) 0
        ![example1431Arc 1, example1431Arc 2] = -1 ∧
      (1 / 6 : ℝ) * iteratedFDeriv ℝ 3
        (lagrangianFn example1431F example1431C (!₂[-1, 0])) 0
        (fun _ => example1431Arc 1) = 1 := by
  rw [example1431_lagrangian_eq]
  set g : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => x 1 ^ 3 + x 0 * x 1
  have hcoord : ∀ i : Fin 3, ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin 3) => x i) :=
    fun i => contDiff_piLp_apply (p := 2)
  have hg : ContDiff ℝ ⊤ g := ((hcoord 1).pow 3).add ((hcoord 0).mul (hcoord 1))
  have hdiag : ∀ (d : EuclideanSpace ℝ (Fin 3)), ∀ i ∈ Finset.Icc 1 3,
      iteratedFDeriv ℝ i g 0 (fun _ => d) =
        (Nat.factorial i : ℝ) * (if i = 1 then 0 else if i = 2 then d 0 * d 1 else d 1 ^ 3) := by
    intro d
    refine Optimization.iteratedFDeriv_apply_diag_eq_of_poly (N := 3)
      (hg.contDiffAt.of_le le_top) (Filter.Eventually.of_forall fun t => ?_)
    rw [show (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} by decide]
    simp [g]; ring
  constructor
  · have hsymm := (hg.contDiffAt (x := 0)).isSymm_ftaylorSeries (p := 2) le_top
    have hA : ∀ u v : EuclideanSpace ℝ (Fin 3),
        iteratedFDeriv ℝ 2 g 0 ![u, v] = iteratedFDeriv ℝ 2 g 0 ![v, u] := fun u v => by
      have := hsymm 2 le_rfl (Equiv.swap 0 1) ![u, v]
      change iteratedFDeriv ℝ 2 g 0 _ = iteratedFDeriv ℝ 2 g 0 _ at this
      rw [← this]
      congr 1; funext i; fin_cases i <;> rfl
    rw [bilin_polar _ hA, hdiag _ 2 (by decide), hdiag _ 2 (by decide), hdiag _ 2 (by decide)]
    simp [example1431Arc]
  · rw [hdiag _ 3 (by decide)]
    simp [example1431Arc, Nat.factorial]

/-- **Example 14.3.1** of [cartis2022evaluation] (`n = 3`, `m = 2`, `X = ℝ³`), with the
corrections noted below. (i) The arc `x(α) = α s₁ + α² s₂ + α³ s₃ = (-α², α, α³)`
(`s₁ = e₂`, `s₂ = -e₁`, `s₃ = e₃`) is feasible; (ii) the feasible set is exactly
`{(-t², t, t³) | t ∈ ℝ}` and `f` vanishes on it, so the origin is a (non-strict, global)
minimizer — not the "high-order saddle point" claimed by the book; (iii) with `y₀ = (-1, 0)`
(the book's `(1, 0)` corresponds to the opposite sign convention `ℒ = f + ⟨y, c⟩`) the Lagrangian
coefficients of orders `1, 2, 3` along the arc vanish, so (14.3.5) holds for `i = 1, 2` and
(14.3.4) holds with equality for `j = 3`; in the book's notation this is (14.3.6),
`∇²ℒ[s₁, s₂] + (1/6) ∇³ℒ[s₁]³ = -1 + 1 = 0` with both terms nonzero
(`example1431_derivs`). -/
theorem example_14_3_1 :
    Optimization.IsFeasibleArc (univ ∩ {x | example1431C x = 0}) 0 3 example1431Arc ∧
    (∀ x : EuclideanSpace ℝ (Fin 3), example1431C x = 0 ↔ ∃ t : ℝ, x = !₂[-t ^ 2, t, t ^ 3]) ∧
    (∀ x : EuclideanSpace ℝ (Fin 3), example1431C x = 0 → example1431F x = 0) ∧ example1431F 0 = 0 ∧
    IsMinOn example1431F {x | example1431C x = 0} 0 ∧
    ∀ i ∈ Finset.Icc 1 3, Optimization.curveCoeff
      (ftaylorSeries ℝ (lagrangianFn example1431F example1431C (!₂[-1, 0])) 0) example1431Arc i
        = 0 := by
  have hF : ∀ x : EuclideanSpace ℝ (Fin 3), example1431C x = 0 → example1431F x = 0 :=
      fun x hx => by
    obtain ⟨t, rfl⟩ := (example1431C_eq_zero_iff x).1 hx
    simp [example1431F]
  refine ⟨⟨fun α => !₂[-α ^ 2, α, α ^ 3], ?_, Filter.Eventually.of_forall fun α =>
    ⟨mem_univ _, (example1431C_eq_zero_iff _).2 ⟨α, rfl⟩⟩⟩, example1431C_eq_zero_iff, hF,
    by simp [example1431F], fun x hx => ?_, ?_⟩
  · simp only [example1431_arc_eq, sub_self]
    exact Asymptotics.isLittleO_zero _ _
  · simp only [mem_ofPred_eq] at hx ⊢
    rw [hF x hx]; simp [example1431F]
  · rw [example1431_lagrangian_eq]
    have hcoord : ∀ i : Fin 3, ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin 3) => x i) :=
      fun i => contDiff_piLp_apply (p := 2)
    have hcd : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => x 1 ^ 3 + x 0 * x 1) 0 :=
      (((hcoord 1).pow 3).add ((hcoord 0).mul (hcoord 1))).contDiffAt.of_le le_top
    refine Optimization.curveCoeff_eq_of_isLittleO (a := fun _ => 0) hcd ?_
    simp only [example1431_arc_eq]
    simp
    ring_nf
    exact Asymptotics.isLittleO_zero _ _

end Example1431

end CartisGouldToint.Chapter14
