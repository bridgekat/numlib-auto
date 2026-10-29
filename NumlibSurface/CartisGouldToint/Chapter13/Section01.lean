import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.ARqpIDAExistence
import Numlib.Optimization.ModelBased.HighOrder.DynamicAccuracy.TRqIDA
import NumlibSurface.CartisGouldToint.Chapter02.Section01

/-!
# Cartis–Gould–Toint §13.1: Inexact algorithms using implicit dynamic accuracy

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §13.1: the trust-region method
TRqIDA (Algorithm 13.1.1) and the adaptive-regularization method ARqpIDA (Algorithm 13.1.2), which
use exact function values and inexact derivatives `∇̄^i f(x_k)` satisfying (13.1.2),
`‖∇̄^i f(x_k) - ∇^i f(x_k)‖ ≤ κ_{∇,i} h_{k,i}`, for constants `κ_{∇,i} ≥ 0` unknown to the
algorithm and requested accuracies `h_{k,i}` controlled by it.

Points live in `ℝⁿ = EuclideanSpace ℝ (Fin n)`. Tolerances `ε`, radii and accuracies are
sequences indexed by the orders (`ε j` for `j ∈ [1, q]`), with `ε_min = epsMin q ε`. Inexact
derivatives at iteration `k` form a jet `D k : FormalMultilinearSeries ℝ ℝⁿ ℝ`; their decrements
are `(D k).taylorDecrement j` (`\overline{ΔT}_{f,j}(x_k, ·)`), their measures
`Optimization.taylorMeasure (D k) j δ S` (`\overline{φ}^δ_{f,j}(x_k)`, (13.1.5)), and the oracle
error model (13.1.2) is `Optimization.JetApprox (ftaylorSeries ℝ f (x k)) (D k) r (κg · h k)`.

## Modelling

The algorithms and their analysis are those of the library
(`Numlib/Optimization/ModelBased/HighOrder/DynamicAccuracy/`), stated there on a real inner
product space, on a feasible set `X` and under the anchored smoothness hypothesis
`LipschitzDerivsAnchored`; this file instantiates them with `X = univ` under f.D0qL.

* One iteration (Steps 1, 2, 4 and 5) of TRqIDA is the predicate `Optimization.TRqDAStep`, and of
  ARqpIDA `Optimization.ARqpDAStep`, given the value `ρ k` of the ratio; they are reused by the
  explicit-dynamic-accuracy methods of §13.3, so Lemmas 13.1.1, 13.1.2, 13.1.9, 13.1.11 and 13.1.13
  are stated for the step predicates (on any feasible set `X`). The runs `algorithm_13_1_1`,
  `algorithm_13_1_2` are `Optimization.IsTRqIDARun`, `Optimization.IsARqpIDARun` with `X = univ`:
  they add the exact-value ratio (13.1.16), (13.1.58) and the oracle bounds.
* f.D0qL (`AssumptionD0qL`) is the smoothness hypothesis `LipschitzDerivsAnchored f univ univ 0 q L`
  with normalized constants `L_j ≥ 1` (`assumptionD0qL_iff_lipschitzDerivsAnchored`);
  `AssumptionD0qLOn` is its form on an open convex set, used for the feasible sets of §14.2.
* An iteration is accuracy-improving (`𝒜`) when the Prop `acc k` holds, and a trial iteration
  (`𝒯 = 𝒮 ∪ 𝒰`) otherwise. After an unsuccessful iteration the jet is reused (`D (k+1) = D k`).
  Function evaluations up to iteration `k` are counted by `derivEvalCount (¬ acc ·) k` (the
  initial value and one per trial iteration), derivative estimates by
  `derivEvalCount (𝒮 ∪ 𝒜) k`.
* Step 1 records displacements `dd k j` for all orders `j ∈ [1, q]` (the book computes them up to
  the first failing order only; admissible displacements always exist). The ARqpIDA halving loop
  of Step 1 is recorded by its effect on the radii (`δ₁ k j ≤ δ k j`) together with witnesses of
  the last halving and of the failure of (13.1.53) at the inherited radius.
* IDA methods have no termination rule: the complexity theorems bound the evaluations performed
  before the first iterate that is (truly) approximately optimal. For TRqIDA the radius is
  `δ_k = min(Δ_k, ϑ)` (`trTest`); for ARqpIDA the test is approximate optimality for *some* radii
  in `(0, 1]^q` (`arTest`).
* Constants that the book defines through a chain of earlier constants are parameters with the
  properties used (e.g. `κ_Δ` of (13.1.31) only needs `0 < κ_Δ ≤ min(1, γ₁(1-η₂)/(L_f +
  4(q+1)!κ_s κ_{∇,max}))`, `Optimization.IsTRKappaDelta`; the book's value is `trKappaDelta`).

## Main definitions

* `AssumptionD0qL`, `AssumptionD0pL` (f.D0qL, f.D0pL); `AssumptionD0qLOn`, `AssumptionD0pLOn`
  (on an open convex set);
* `algorithm_13_1_1` (TRqIDA), `trTest`, `phiHat`;
* `algorithm_13_1_2` (ARqpIDA), `arTest`.

## Main results

* TRqIDA: `lemma_13_1_1` – `lemma_13_1_7`, `theorem_13_1_8`; runs exist
  (`exists_algorithm_13_1_1`, for every oracle satisfying (13.1.2)).
* ARqpIDA: `lemma_13_1_9` – `lemma_13_1_18`, `theorem_13_1_19_i`, `theorem_13_1_19_ii` (through
  `arqpIDA_complexity`); runs with the radii control exist (`exists_algorithm_13_1_2`, through
  `Optimization.exists_arqpDA_steps`).

## Deviations from the book

* **Algorithm 13.1.1, Step 0** prints `0 < γ₁ < 1 < γ₂ < γ₃`; the trust-region update (13.1.17)
  and the proof of Lemma 13.1.1 require `0 < γ₁ ≤ γ₂ < 1 ≤ γ₃` (`TRqIDAParams` extends
  `Optimization.TRParams`).
* **Lemmas 13.1.1 and 13.1.9** assume the radius (parameter) bound at `Δ_k` (`σ_k`); the proofs
  need it at `Δ_{k+1}` (`σ_{k+1}`), and the printed statements are false for `k = 0`.
* **Lemma 13.1.4**: the radius bound is proved for every lower bound `c` of `{φ̂_i : i ∈ 𝒯_k}`
  (`trqDA_delta_ge`), which contains the printed cases `𝒯_k ≠ ∅` and `𝒯_k = ∅` (`lemma_13_1_4`).
  The constant `κ_Δ` of (13.1.31) is only used through
  `0 < κ_Δ ≤ min(1, γ₁(1-η₂)/(L_f + 4(q+1)! κ_s κ_{∇,max}))` (`IsTRKappaDelta`); the printed value
  (`trKappaDelta`) has these properties when its denominator is positive.
* **Algorithm 13.1.2, Step 0** omits `ς ∈ (0, 1]` from its list of constants, which Step 1 uses
  (`ARqpIDAParams` includes it).
* **Lemma 13.1.6** uses the bound `L̄_f` on the inexact derivatives, which the book defines only
  in (13.1.63).
* **Lemma 13.1.11**: the finiteness of the halving loop (the existence half of the printed
  statement) is `Optimization.exists_arqpDA_halving`; the radius bounds hold for every run.
* **Lemma 13.1.12** is proved for any bound `σ̄ ≥ σ_i` (`i ≤ k`), the book's `σ_{k,max}` being one;
  the well-definedness of Step 2 (its first part) is part of the existence of runs.
* **Lemma 13.1.15** writes `δ_k` for the radii `δ^{(1)}_k` at the end of Step 1.
* **Algorithm 13.1.1, Step 4**: after an unsuccessful iteration with `Δ_{k+1} ≥ ϑ` the book goes
  back to Step 2 with `d_{k+1} = d_k`; the run predicate performs Step 1 at every iteration. Every
  book run is a run of the predicate (the same displacements are admissible, since `δ_{k+1} = δ_k`
  and the derivative estimates are unchanged), so the analysis covers the book's algorithm.
* **Theorem 13.1.8** (and 13.1.19): the derivative-evaluation bounds count the initial estimate
  and the last accuracy-improving iteration (`κ^F + 2`, resp. `+ 3`); the conclusion `φ^δ_{f,q}`
  of 13.1.8 reads `φ^δ_{f,j}`.
* **Algorithm 13.1.2, Step 2** tests (13.1.46) for `i ∈ [1, q]` only; (13.1.46), Step 5 and the
  proofs of Lemmas 13.1.14 and 13.1.16 concern `i ∈ [1, p]`, which `ARqpDAStep` uses. The test is
  also skipped for long steps `‖s_k‖ ≥ 1`, where Lemma 13.1.14 still uses (13.1.47); its constant
  `σ_max` is corrected with `max(κ_s, κ_h)` in place of `κ_s`.
* **Radii control** (13.1.69)–(13.1.70): the results assume the weaker `RadiiControl`
  (`δ_{s_k} = 1` if `q ≤ 2`; the lower bounds `ς θ ε_j/(24 max(L̄, σ_k))` at every order if
  `q > 2`), which the book's condition implies (`Optimization.RadiiControl.of_unit_le_two`); for
  `q > 2` the proofs do not use `δ = 1` at the orders `j ≤ 2`. The library's analysis takes the
  mode as a parameter (`Optimization.ARqpDARadiiControl u`: unit radii if `u`, the lower bounds at
  every order if `¬ u`, with exponents `arPiOf u`), so that the lower-bound mode also covers
  `q ≤ 2` when unit radii are not available (§14.2); `RadiiControl` is the mode `u = (q ≤ 2)`.
* **Lemma 13.1.17** (`q > 2`): the printed constant `κ_{δ,min}^{j-1}` is replaced by
  `κ̂^{j-1}` with `κ̂ = min(κ_{δ,min}, (1-θ)/(2 q! (L_{f,p} + σ_max + 3κ_{∇,max}κ_s)))`; the
  book's derivation ("the first case implies the second") needs `κ_{δ,min}` below that bound.
  Lemma 13.1.18 and Theorem 13.1.19 use `κ̂` accordingly.
* **Lemma 13.1.18** states (13.1.82) for every trial iteration before approximate optimality; its
  proof (through Lemma 13.1.17) covers successful iterations `k` with `x_{k+1}` not approximately
  optimal, which is the case used.
* **Theorem 13.1.19**: the index `k_ε` is the first iterate that is approximately optimal for some
  radii in `(0, 1]^q` (the radii certified by the algorithm are those at the end of Step 1, which
  may be smaller than one; the book's proof conflates `δ^{(0)}_k` and `δ^{(1)}_k`). For `q ≤ 2`
  this gives the printed conclusion with radius one (`isEpsDeltaApprox_one_of_le_two`); for
  `q > 2` the conclusion is with some radii, as printed. The constant `κ^C` of (13.1.89) misses
  the factor `1 + |log γ₁|/log γ₂` on the `+1` coming from `|𝒮_k| ≤ |𝒮_{k-1}| + 1`. For
  `κ_h = 0` (allowed by (13.1.51)) there are no accuracy-improving iterations before termination
  and `κ^F` is read with `log 0 = 0`.
-/

open Set Metric Finset Optimization
open scoped Nat

namespace CartisGouldToint.Chapter13

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ### Minima and maxima over the orders

The extrema `epsMin`, `ordMax`, `lipMax` over the orders are those of the library
(`Optimization.epsMin`, `Optimization.ordMax`, `Optimization.lipMax`). -/

/-! ### Assumptions f.D0qL and f.D0pL -/

/-- **Assumption f.D0qL** of [cartis2022evaluation], §13.1.3.2: `f` is `q` times continuously
differentiable and, for every `j ∈ [0, q]` (including `j = 0`, the function itself), the `j`-th
derivative is Lipschitz continuous with a constant `L_{f,j} ≥ 1`. -/
def AssumptionD0qL (f : ℝⁿ → ℝ) (q : ℕ) (L : ℕ → ℝ) : Prop :=
  ContDiff ℝ q f ∧ ∀ j ≤ q, 1 ≤ L j ∧ IteratedFDerivLipschitzOn f j (L j) univ

/-- **Assumption f.D0pL** of [cartis2022evaluation], §13.1.4.1: f.D0qL with order `p`. -/
abbrev AssumptionD0pL (f : ℝⁿ → ℝ) (p : ℕ) (L : ℕ → ℝ) : Prop :=
  AssumptionD0qL f p L

section Assumption

variable {f : ℝⁿ → ℝ} {q : ℕ} {L : ℕ → ℝ}

theorem assumptionD0qL_iff : AssumptionD0qL f q L ↔
    ContDiff ℝ q f ∧ ∀ j ≤ q, 1 ≤ L j ∧ IteratedFDerivLipschitzOn f j (L j) univ := Iff.rfl

theorem AssumptionD0qL.one_le (hf : AssumptionD0qL f q L) {j : ℕ} (hj : j ≤ q) : 1 ≤ L j :=
  (hf.2 j hj).1

theorem AssumptionD0qL.lipschitz (hf : AssumptionD0qL f q L) {j : ℕ} (hj : j ≤ q) :
    IteratedFDerivLipschitzOn f j (L j) univ :=
  (hf.2 j hj).2

theorem AssumptionD0qL.one_le_lipMax (hf : AssumptionD0qL f q L) : 1 ≤ lipMax L q :=
  (hf.one_le (Nat.zero_le q)).trans (le_lipMax (Nat.zero_le q))

theorem AssumptionD0qL.contDiffAt (hf : AssumptionD0qL f q L) {j : ℕ} (hj : j ≤ q) (y : ℝⁿ) :
    ContDiffAt ℝ j f y :=
  (hf.1.of_le (by exact_mod_cast hj)).contDiffAt

/-- f.D0qL gives normalized constants `L_j ≥ 1` for `j ≤ q`. -/
theorem AssumptionD0qL.normalized (hf : AssumptionD0qL f q L) : ∀ j ≤ q, 1 ≤ L j :=
  fun _ hj => hf.one_le hj

/-- f.D0qL is the smoothness hypothesis `LipschitzDerivsAnchored` of the library on the whole
space, with the orders `0, …, q` (anchored at every point). -/
theorem AssumptionD0qL.lipschitzDerivsAnchored (hf : AssumptionD0qL f q L) :
    LipschitzDerivsAnchored f univ univ 0 q L :=
  .of_contDiff hf.1 (fun _ hj => hf.lipschitz (Finset.mem_Icc.1 hj).2) univ

/-- f.D0qL is `LipschitzDerivsAnchored f univ univ 0 q L` with normalized constants. -/
theorem assumptionD0qL_iff_lipschitzDerivsAnchored :
    AssumptionD0qL f q L ↔ LipschitzDerivsAnchored f univ univ 0 q L ∧ ∀ j ≤ q, 1 ≤ L j :=
  ⟨fun hf => ⟨hf.lipschitzDerivsAnchored, hf.normalized⟩, fun ⟨hf, hL⟩ =>
    ⟨contDiff_iff_contDiffAt.2 fun y => hf.contDiffAt y (mem_univ y),
      fun j hj => ⟨hL j hj, hf.lipschitzOn_of_le hj⟩⟩⟩

/-- **(A.19) under f.D0qL**: `|f(x + s) - T_{f,j}(x, s)| ≤ L_{f,j}/(j+1)! ‖s‖^{j+1}`, in the form
`|f(x + s) - (f(x) - ΔT_{f,j}(x, s))|`. -/
theorem AssumptionD0qL.abs_sub_le (hf : AssumptionD0qL f q L) {j : ℕ} (hj : j ≤ q) (x s : ℝⁿ) :
    |f (x + s) - (f x - (ftaylorSeries ℝ f x).taylorDecrement j s)| ≤
      L j / ((j + 1)! : ℝ) * ‖s‖ ^ (j + 1) :=
  hf.lipschitzDerivsAnchored.abs_sub_taylorDecrement_le_of_le hj (mem_univ x) (mem_univ _)

/-- **(13.1.24)**: under f.D0qL, `‖∇^i f(x)‖ ≤ L_{f,i-1} ≤ L_f` for `i ∈ [1, q]`. -/
theorem AssumptionD0qL.norm_iteratedFDeriv_le (hf : AssumptionD0qL f q L) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 q) (x : ℝⁿ) : ‖iteratedFDeriv ℝ i f x‖ ≤ lipMax L q :=
  hf.lipschitzDerivsAnchored.norm_iteratedFDeriv_le_lipMax hf.normalized hi (mem_univ x)

/-- **(13.1.24), (13.1.63)**: inexact derivatives within `κ_{∇,i} h_i` of the exact ones, with
`0 ≤ κ_{∇,i}`, `0 ≤ h_i ≤ κ_h`, satisfy `‖∇̄^i f(x)‖ ≤ L_f + κ_{∇,max} κ_h` for `i ∈ [1, q]`. -/
theorem AssumptionD0qL.norm_le_of_jetApprox (hf : AssumptionD0qL f q L)
    {D : FormalMultilinearSeries ℝ ℝⁿ ℝ} {κg hh : ℕ → ℝ} {κh : ℝ} {x : ℝⁿ}
    (hD : JetApprox (ftaylorSeries ℝ f x) D q (fun i => κg i * hh i))
    (hκ : ∀ i ∈ Finset.Icc 1 q, 0 ≤ κg i) (hh0 : ∀ i ∈ Finset.Icc 1 q, 0 ≤ hh i)
    (hhκ : ∀ i ∈ Finset.Icc 1 q, hh i ≤ κh) {i : ℕ} (hi : i ∈ Finset.Icc 1 q) :
    ‖D i‖ ≤ lipMax L q + ordMax q κg * κh :=
  hf.lipschitzDerivsAnchored.norm_le_of_jetApprox hf.normalized (mem_univ x) hD hκ hh0 hhκ hi

end Assumption

/-- **f.D0qL on an open convex set** `C` (the form of f.D0qL used with a feasible set `X ⊆ C`,
[cartis2022evaluation] §14.2, for the TRqIDA-SC, TRqEDA-SC, ARqpIDA-SC and ARqpEDA-SC
algorithms): `C` is open and convex, `f` is `C^q` near every point of `C` and, for every
`j ∈ [0, q]`, the `j`-th derivative is `L_{f,j}`-Lipschitz on `C` with `L_{f,j} ≥ 1`; that is,
`LipschitzDerivsAnchored f C C 0 q L` with normalized constants. With `C = univ` this is
`AssumptionD0qL` (`assumptionD0qLOn_univ_iff`). -/
structure AssumptionD0qLOn (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (q : ℕ) (L : ℕ → ℝ) : Prop
    extends LipschitzDerivsAnchored f C C 0 q L where
  /-- The constants are at least `1`. -/
  one_le : ∀ j ≤ q, 1 ≤ L j

/-- **f.D0pL on an open convex set** `C`: `AssumptionD0qLOn` with order `p`. -/
abbrev AssumptionD0pLOn (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (L : ℕ → ℝ) : Prop :=
  AssumptionD0qLOn f C p L

/-- f.D0qL is f.D0qL on `univ`. -/
theorem AssumptionD0qL.on_univ {f : ℝⁿ → ℝ} {q : ℕ} {L : ℕ → ℝ} (hf : AssumptionD0qL f q L) :
    AssumptionD0qLOn f univ q L :=
  ⟨hf.lipschitzDerivsAnchored, hf.normalized⟩

theorem assumptionD0qLOn_univ_iff {f : ℝⁿ → ℝ} {q : ℕ} {L : ℕ → ℝ} :
    AssumptionD0qLOn f univ q L ↔ AssumptionD0qL f q L :=
  ⟨fun h => assumptionD0qL_iff_lipschitzDerivsAnchored.2 ⟨h.toLipschitzDerivsAnchored, h.one_le⟩,
    AssumptionD0qL.on_univ⟩


/-! ### TRqIDA -/

section TRqIDA

variable {X : Set ℝⁿ} {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {ρ : ℕ → ℝ} {L : ℕ → ℝ}
  {k : ℕ}

/-- The scaled criticality `φ̂_{f,k} = j_k! \overline{ΔT}_{f,j_k}(x_k, d_k) / δ_k^{j_k}` of
(13.1.25), for data `D`, order `j`, radius `δ` and displacement `d`. -/
noncomputable abbrev phiHat (D : FormalMultilinearSeries ℝ ℝⁿ ℝ) (j : ℕ) (δ : ℝ) (d : ℝⁿ) : ℝ :=
  trqGap D j δ d

/-- The test of approximate optimality of TRqIDA at iteration `k` (not observable by the method,
[cartis2022evaluation], (12.1.25)): `x_k` is an `(ε, δ_k)`-approximate `q`-th order minimizer
with the radius `δ_k = min(Δ_k, ϑ)` at all orders. -/
def trTest (f : ℝⁿ → ℝ) (P : TRqIDAParams) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (k : ℕ) :
    Prop :=
  IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε (fun _ => trqDARadius P Δ k)

theorem trqIDATest_univ {f : ℝⁿ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x : ℕ → ℝⁿ}
    {Δ : ℕ → ℝ} : trqIDATest f univ P ε x Δ = trTest f P ε x Δ := by
  funext k; simp only [trqIDATest, trTest, Set.setOf_add_mem_univ]

/-- **Algorithm 13.1.1** (TRqIDA) of [cartis2022evaluation] as a run predicate, for the objective
`f`, the (unknown) oracle constants `κ_{∇,i}` (`κg i ≥ 0`), constants `P`, tolerances
`ε ∈ (0, 1]^q` with `ε_min ≤ ϑ`, starting point `x₀`, and sequences of iterates `x`, radii `Δ`,
requested accuracies `h`, inexact jets `D` satisfying (13.1.2), Step-1 displacements `dd`,
orders `j_k`, steps `s` and accuracy-improving flags `acc`; every iteration satisfies
`TRqDAStep` with the exact-value ratio (13.1.16) `ρ_k = (f(x_k) - f(x_k + s_k)) /
\overline{ΔT}_{f,j_k}(x_k, s_k)` (`Optimization.trqRatio`). The method has no termination rule;
see `trTest`. This is `IsTRqIDARun` with the feasible set `X = univ`. -/
abbrev algorithm_13_1_1 (f : ℝⁿ → ℝ) (κg : ℕ → ℝ) (P : TRqIDAParams) (ε : ℕ → ℝ)
    (x₀ : ℝⁿ) (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
    (acc : ℕ → Prop) : Prop :=
  IsTRqIDARun f univ κg P ε x₀ x Δ h D dd jk s acc

/-- **Lemma 13.1.1** ([cartis2022evaluation], index-corrected): for sequences satisfying the
TRqIDA step predicate at every iteration `i ≤ k` with `Δ_0 = Δ₀`, if `0 < Δ_min ≤ Δ_{k+1}`, then
`|𝒯_k| ≤ |𝒮_k| (1 + log γ₃/|log γ₂|) + |log (Δ_min/Δ₀)|/|log γ₂|` (13.1.22), where
`𝒯_k = {i ≤ k | ¬ acc i}` and `𝒮_k = {i ≤ k | ¬ acc i, ρ_i ≥ η₁}`. The book assumes
`Δ_min ≤ Δ_k` and `Δ_min ≤ Δ₀`; its proof needs the radius after iteration `k`, and the upper
bound `Δ_min ≤ Δ₀` is not needed. -/
theorem lemma_13_1_1 (hstep : ∀ i ≤ k, TRqDAStep X P ε x Δ h D dd jk s acc ρ i)
    (hΔ0 : Δ 0 = P.Δ₀) {Δmin : ℝ} (hmin : 0 < Δmin) (hΔmin : Δmin ≤ Δ (k + 1)) :
    ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k).card *
          (1 + Real.log P.γ₃ / |Real.log P.γ₂|) +
        |Real.log (Δmin / P.Δ₀)| / |Real.log P.γ₂| :=
  trqDA_card_trial_le hstep hΔ0 hmin hΔmin

/-- **Lemma 13.1.2** ([cartis2022evaluation]): at a trial iteration `k ∈ 𝒯` of TRqIDA (or
TRqEDA) with `Δ_k > 0`, the scaled criticality `φ̂_{f,k}` of (13.1.25) satisfies
`φ̂_{f,k} ≥ ½ ς ε_min` (hence (13.1.26), `min_{i ∈ 𝒯_k} φ̂_{f,i} ≥ ½ ς ε_min`) and (13.1.27),
`\overline{ΔT}_{f,j_k}(x_k, s_k) ≥ φ̂_{f,k} δ_k^{j_k} / j_k!`. -/
theorem lemma_13_1_2 (hs : TRqDAStep X P ε x Δ h D dd jk s acc ρ k) (hk : ¬ acc k)
    (hΔ : 0 < Δ k) :
    P.ς * epsMin P.q ε / 2 ≤ phiHat (D k) (jk k) (trqDARadius P Δ k) (dd k (jk k)) ∧
      phiHat (D k) (jk k) (trqDARadius P Δ k) (dd k (jk k)) * trqDARadius P Δ k ^ jk k / (jk k)! ≤
        (D k).taylorDecrement (jk k) (s k) :=
  TRqDAStep.trqGap_ge hs hk hΔ

/-- **Lemma 13.1.3** ([cartis2022evaluation]): under f.D0qL, at a trial iteration `k ∈ 𝒯` of
TRqIDA with (13.1.28) `Δ_k ≤ min(ϑ, (1 - η₂)/(L_f + 4 (q+1)! κ_s κ_{∇,max}) pĥ_{f,k})`, the
iteration is very successful (`ρ_k ≥ η₂`) and `Δ_{k+1} ≥ Δ_k`. -/
theorem lemma_13_1_3 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) (hk : ¬ acc k)
    (hΔ : Δ k ≤ min P.ϑ ((1 - P.η₂) /
      (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg) * trPhiHat P Δ D dd jk k)) :
    P.η₂ ≤ trqRatio f D x s jk k ∧ Δ k ≤ Δ (k + 1) :=
  IsTRqIDARun.ratio_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hk hΔ

/-- The constant `κ_Δ` of (13.1.31) ([cartis2022evaluation]):
`min(1, γ₁(1 - η₂)/(L_f + 4(q+1)! κ_s κ_{∇,max})) ·
min(ϑ, Δ₀ min_j δ₀^j / (2q (max_i ‖∇^i f(x₀)‖ + κ_{∇,max} κ_h)))` with `δ₀ = min(Δ₀, ϑ)`. Only
`0 < κ_Δ ≤ min(1, γ₁(1 - η₂)/(L_f + 4(q+1)! κ_s κ_{∇,max}))` is used by the analysis
(`trKappaDelta_spec`), and the results are stated for every such `κ_Δ`. -/
noncomputable def trKappaDelta (f : ℝⁿ → ℝ) (P : TRqIDAParams) (L κg : ℕ → ℝ) (x₀ : ℝⁿ) : ℝ :=
  min 1 (P.γ₁ * (1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg)) *
    min P.ϑ (P.Δ₀ * epsMin P.q (fun j => min P.Δ₀ P.ϑ ^ j) /
      (2 * P.q * (ordMax P.q (fun i => ‖iteratedFDeriv ℝ i f x₀‖) + ordMax P.q κg * P.κh)))

/-- The constant `κ_Δ` of (13.1.31) has the properties used in Lemma 13.1.4, provided the
denominator `max_i ‖∇^i f(x₀)‖ + κ_{∇,max} κ_h` is positive (otherwise the printed formula has a
division by zero). -/
theorem trKappaDelta_spec {f : ℝⁿ → ℝ} {P : TRqIDAParams} {L κg : ℕ → ℝ} {x₀ : ℝⁿ}
    (hf : AssumptionD0qL f P.q L) (hκg : ∀ i ∈ Finset.Icc 1 P.q, 0 ≤ κg i)
    (hM : 0 < ordMax P.q (fun i => ‖iteratedFDeriv ℝ i f x₀‖) + ordMax P.q κg * P.κh) :
    0 < trKappaDelta f P L κg x₀ ∧ trKappaDelta f P L κg x₀ ≤ 1 ∧
      trKappaDelta f P L κg x₀ ≤
        P.γ₁ * ((1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg)) := by
  have hLf := hf.one_le_lipMax
  have hκm := ordMax_nonneg hκg
  have hC : 0 < lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg := by
    have := P.κs_pos; positivity
  have hδ₀ : 0 < min P.Δ₀ P.ϑ := lt_min P.Δ₀_pos P.ϑ_pos
  have hmin : 0 < epsMin P.q (fun j => min P.Δ₀ P.ϑ ^ j) :=
    Optimization.epsMin_pos P.one_le_q fun j _ => pow_pos hδ₀ j
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.one_le_q
  have hA0 : 0 < min 1 (P.γ₁ * (1 - P.η₂) /
      (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg)) :=
    lt_min one_pos (div_pos (mul_pos P.γ₁_pos P.one_sub_η₂_pos) hC)
  have hB0 : 0 < min P.ϑ (P.Δ₀ * epsMin P.q (fun j => min P.Δ₀ P.ϑ ^ j) /
      (2 * P.q * (ordMax P.q (fun i => ‖iteratedFDeriv ℝ i f x₀‖) + ordMax P.q κg * P.κh))) :=
    lt_min P.ϑ_pos (by have := P.Δ₀_pos; positivity)
  have hB1 : min P.ϑ (P.Δ₀ * epsMin P.q (fun j => min P.Δ₀ P.ϑ ^ j) /
      (2 * P.q * (ordMax P.q (fun i => ‖iteratedFDeriv ℝ i f x₀‖) + ordMax P.q κg * P.κh))) ≤ 1 :=
    (min_le_left _ _).trans P.ϑ_le_one
  refine ⟨mul_pos hA0 hB0, ?_, ?_⟩
  · exact (mul_le_of_le_one_left hB0.le (min_le_left _ _)).trans hB1
  · rw [← mul_div_assoc]
    exact (mul_le_of_le_one_right hA0.le hB1).trans (min_le_right _ _)

/-- **Lemma 13.1.4** ([cartis2022evaluation]): under f.D0qL, along a TRqIDA run, for every
`κ_Δ ∈ (0, 1]` with `κ_Δ ≤ γ₁ (1 - η₂)/(L_f + 4(q+1)! κ_s κ_{∇,max})` (e.g. the value (13.1.31),
`trKappaDelta`) and every `k`: (13.1.30) `Δ_k ≥ min(γ₁ ϑ, κ_Δ min_{i ∈ 𝒯_k} φ̂_{f,i})` if
`𝒯_k ≠ ∅` and `Δ_k ≥ γ₁ ϑ` otherwise, and (13.1.32) `δ_k ≥ ς κ_δ ε_min` with `κ_δ = κ_Δ/2`
(13.1.33). -/
theorem lemma_13_1_4 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ} (hκΔ0 : 0 < κΔ)
    (hκΔ1 : κΔ ≤ 1)
    (hκΔ : κΔ ≤ P.γ₁ * ((1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg)))
    (k : ℕ) :
    (∀ hne : (successSet (fun i => ¬ acc i) k).Nonempty, min (P.γ₁ * P.ϑ)
        (κΔ * (successSet (fun i => ¬ acc i) k).inf' hne (trPhiHat P Δ D dd jk)) ≤ Δ k) ∧
      (successSet (fun i => ¬ acc i) k = ∅ → P.γ₁ * P.ϑ ≤ Δ k) ∧
      P.ς * (κΔ / 2) * epsMin P.q ε ≤ trqDARadius P Δ k :=
  IsTRqIDARun.delta_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hκΔ0 hκΔ1 hκΔ k

/-- **Lemma 13.1.5** ([cartis2022evaluation]): under f.D0qL, for an admissible `κ_Δ` and
`κ_δ = κ_Δ/2`, every trial iteration `k ∈ 𝒯` of a TRqIDA run satisfies (13.1.34)
`\overline{ΔT}_{f,j_k}(x_k, s_k) ≥ (ς κ_δ)^{q+1}/q! ε_min^{q+1}`, and if moreover `k ∈ 𝒮` then
(13.1.35) `f(x_k) - f(x_{k+1}) ≥ η₁ (ς κ_δ)^{q+1}/(2 q!) ε_min^{q+1}`. (No optimality hypothesis
is needed.) -/
theorem lemma_13_1_5 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) (hk : ¬ acc k) :
    (P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1) ≤
        (D k).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ trqRatio f D x s jk k →
        P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
          f (x k) - f (x (k + 1))) :=
  IsTRqIDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hκΔ hk

/-- **Lemma 13.1.6** ([cartis2022evaluation]): under f.D0qL, with `L̄_f = L_f + κ_{∇,max} κ_h`
((13.1.24)) and an admissible `κ_Δ`, `κ_δ = κ_Δ/2`: if Step 1 of TRqIDA branches to Step 2 at
iteration `k` and (13.1.36) `h_{k,i} ≤ κ_s (ς^{q+1} κ_δ^q/(4 q! L̄_f))^q ε_min^{q(q+1)}` for all
`i ∈ [1, q]`, then Step 2 does not branch to Step 5 (`k ∈ 𝒯`). (The book uses `L̄_f`, defined only
in (13.1.63), for the bound (13.1.24).) -/
theorem lemma_13_1_6 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ)
    (hb : ∃ j ∈ Finset.Icc 1 P.q, trqDAFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤ P.κs * (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q /
      (4 * P.q ! * (lipMax L P.q + ordMax P.q κg * P.κh))) ^ P.q *
        epsMin P.q ε ^ (P.q * (P.q + 1))) :
    ¬ acc k :=
  IsTRqIDARun.not_acc_of_le hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hκΔ hb hh

/-- **Lemma 13.1.7** ([cartis2022evaluation]): under f.D0qL and for an admissible `κ_Δ`,
`κ_δ = κ_Δ/2`: if Step 1 of TRqIDA branches to Step 5 at iteration `k` ((13.1.14) fails at every
order) and (13.1.37) `κ_{∇,max} h_{k,i} ≤ ς^{q+1} κ_δ^q/(4 q!) ε_min^{q+1}` for `i ∈ [1, q]`
(written without division, so that `κ_{∇,max} = 0` is allowed), then
`φ^{δ_k}_{f,j}(x_k) ≤ ε_j δ_k^j/j!` for all `j ∈ [1, q]`. -/
theorem lemma_13_1_7 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, ¬ trqDAFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, ordMax P.q κg * h k i ≤
      P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    trTest f P ε x Δ k := by
  have := IsTRqIDARun.trqIDATest_of_pass hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hκΔ hpass hh
  rwa [trqIDATest_univ] at this

/-- **Theorem 13.1.8** ([cartis2022evaluation]): complexity of TRqIDA. Let f.D0qL and f.Bb
(`f ≥ f_low`) hold, `ε ∈ (0, 1]^q`, and `κ_Δ` be admissible (e.g. (13.1.31)), `κ_δ = κ_Δ/2`. For
every TRqIDA run there is a first iteration `k_ε` at which `x_ε = x_{k_ε}` is an
`(ε, δ_ε)`-approximate `q`-th order minimizer with `δ_ε = min(Δ_{k_ε}, ϑ) ∈ (0, 1]`, and before
it at most (13.1.38)
`κ^A (f(x₀) - f_low)/ε_min^{q+1} + κ^B |log ε_min| + κ^C` function evaluations and (13.1.39)
`κ^A (f(x₀) - f_low)/ε_min^{q+1} + κ^E |log ε_min| + κ^F + 2` derivative estimates are made, with
`κ^S = 2 q!/(η₁ (ς κ_δ)^{q+1})`, `κ^A = κ^S (1 + log γ₃/|log γ₂|)`, `κ^B = 1/|log γ₂|`,
`κ^C = |log(ς κ_δ/Δ₀)|/|log γ₂| + 1`, `κ^E = q(q+1)/|log γ_h|`,
`κ^F = |log(κ_acc/κ_h)|/|log γ_h|` (`κ_acc = trKappaAcc`). The derivative count includes the
initial estimate and the last accuracy-improving iteration (the book's `κ^F` is `κ^F + 2`). -/
theorem theorem_13_1_8 (hf : AssumptionD0qL f P.q L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) :
    ∃ kε, IsFirstHit (trTest f P ε x Δ) kε ∧ 0 < trqDARadius P Δ kε ∧ trqDARadius P Δ kε ≤ 1 ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          1 / |Real.log P.γ₂| * |Real.log (epsMin P.q ε)| +
          (|Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i)) kε : ℝ) ≤
        trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow) /
            epsMin P.q ε ^ (P.q + 1) +
          P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
            P.κh)| / |Real.log P.γh| + 2 := by
  have := IsTRqIDARun.complexity hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) (fun y _ => hb y) hrun hκΔ
  rwa [trqIDATest_univ] at this

end TRqIDA

/-- **Runs of Algorithm 13.1.1 exist** ([cartis2022evaluation]): for every objective `f`,
constants `P`, tolerances `ε ∈ (0, 1]^q` with `ε_min ≤ ϑ`, oracle constants `κ_{∇,i} ≥ 0`,
starting point `x₀`, and every deterministic oracle `O` satisfying (13.1.2) at every point for
all positive accuracies (e.g. the exact jet, `exists_algorithm_13_1_1_exact`, or a finite
derivative-approximation scheme, `exists_algorithm_13_1_1_of_scheme`), there is a TRqIDA run whose
derivative estimates are `D_k = O(x_k, h_k)`. -/
theorem exists_algorithm_13_1_1 {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ}
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hϑ : epsMin P.q ε ≤ P.ϑ)
    (hκg : ∀ i ∈ Finset.Icc 1 P.q, 0 ≤ κg i) (x₀ : ℝⁿ)
    (O : ℝⁿ → (ℕ → ℝ) → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (hO : ∀ y h', (∀ i ∈ Finset.Icc 1 P.q, 0 < h' i) →
      JetApprox (ftaylorSeries ℝ f y) (O y h') P.q (fun i => κg i * h' i)) :
    ∃ (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
      (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop),
      algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc ∧ ∀ k, D k = O (x k) (h k) := by
  obtain ⟨x, Δ, h, dd, jk, s, acc, hx, hΔ, hh, hstep⟩ := exists_trqDA_run f P ε O x₀
  exact ⟨x, Δ, h, _, dd, jk, s, acc, ⟨hε, hϑ, hκg, hx, mem_univ _, hΔ, hh,
    fun k => hO _ _ fun i hi =>
      ((trqDA_invariants (k := k) (fun i _ => hstep i) hΔ hh).2 i hi).1, hstep⟩, fun _ => rfl⟩

/-- The exact jet is an oracle for (13.1.2): **TRqIDA runs with exact derivatives exist**
(instance of `exists_algorithm_13_1_1`). -/
theorem exists_algorithm_13_1_1_exact {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : TRqIDAParams}
    {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hϑ : epsMin P.q ε ≤ P.ϑ)
    (hκg : ∀ i ∈ Finset.Icc 1 P.q, 0 ≤ κg i) (x₀ : ℝⁿ) :
    ∃ (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
      (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop),
      algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc ∧
        ∀ k, D k = ftaylorSeries ℝ f (x k) :=
  exists_algorithm_13_1_1 hε hϑ hκg x₀ (fun y _ => ftaylorSeries ℝ f y) fun _ _ hh =>
    (jetApprox_self _ _).mono_err fun i hi => mul_nonneg (hκg i hi) (hh i hi).le


/-! ### ARqpIDA -/

section ARqpIDA

variable {X : Set ℝⁿ} {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ}
  {acc : ℕ → Prop} {ρ : ℕ → ℝ} {L : ℕ → ℝ} {k : ℕ}

/-- **Lemma 13.1.9** ([cartis2022evaluation], index-corrected): for sequences satisfying the
ARqpIDA step predicate at every iteration `i ≤ k` with `σ_0 = σ₀`, if `σ_{k+1} ≤ σ_max`, then
`|𝒯_k| ≤ |𝒮_k| (1 + |log γ₁|/log γ₂) + log(σ_max/σ₀)/log γ₂` (13.1.62). The book assumes
`σ_k ≤ σ_max`; its proof needs the parameter after iteration `k`. -/
theorem lemma_13_1_9 (hstep : ∀ i ≤ k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hσ0 : σ 0 = P.σ₀) (hδ0 : δ 0 = P.δ₀) (hh0 : h 0 = P.h₀) {σmax : ℝ}
    (hσmax : σ (k + 1) ≤ σmax) :
    ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤
      (successSet (fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) k).card *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) +
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ :=
  arqpDA_card_trial_le hstep hσ0 hδ0 hh0 hσmax

/-- **Lemma 13.1.11** ([cartis2022evaluation]): if Step 1 of ARqpIDA (or ARqpEDA) is performed at
iteration `k` with `‖∇̄^i f(x_k)‖ ≤ L̄` for `i ∈ [1, p]` (`L̄ > 0`; (13.1.63) for ARqpIDA),
`σ_k ≥ 0` and `δ^{(0)}_k ∈ (0, 1]^q`, then (13.1.66)
`δ^{(0)}_{k,j} ≥ δ^{(1)}_{k,j} ≥ min(ς ε_j/(16 max(L̄, σ_k)), δ^{(0)}_{k,j})` for `j ∈ [1, q]`.
(The finiteness of the halving loop, the existence half of the printed statement, is a property
of the algorithm: the same estimate shows that the loop stops once the radius is below
`ς ε_j/(8 max(L̄, σ_k))`.) -/
theorem lemma_13_1_11 (hs : ARqpStep1 X P ε x σ δ δ₁ D dd k) {Lb : ℝ}
    (hLb : 0 < Lb) (hD : ∀ i ∈ Finset.Icc 1 P.p, ‖D k i‖ ≤ Lb) (hσ : 0 ≤ σ k)
    (hδ1 : ∀ j ∈ Finset.Icc 1 P.q, δ k j ≤ 1) {j : ℕ} (hj : j ∈ Finset.Icc 1 P.q) :
    δ₁ k j ≤ δ k j ∧ min (P.ς * ε j / (16 * max Lb (σ k))) (δ k j) ≤ δ₁ k j :=
  ARqpStep1.radius_bounds hs hLb hD hσ hδ1 hj

/-- **Lemma 13.1.13** ([cartis2022evaluation]): at a trial iteration `k ∈ 𝒯` of ARqpIDA (or
ARqpEDA) with `ε_{j_k} > 0` and `σ_k ≥ 0`,
`\overline{ΔT}_{f,p}(x_k, s_k) ≥ σ_k/(p+1)! ‖s_k‖^{p+1}` (13.1.76) and
`\overline{ΔT}_{f,p}(x_k, s_k) > 0`, so that the ratio (13.1.58) is well defined. -/
theorem lemma_13_1_13 (hs : ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ k) (hk : ¬ acc k)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, 0 < ε j) (hσ : 0 ≤ σ k) :
    σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) ≤ (D k).taylorDecrement P.p (s k) ∧
      0 < (D k).taylorDecrement P.p (s k) :=
  ARqpDAStep.taylorDecrement_ge hs hk hε hσ

/-- **Lemma 13.1.10** ([cartis2022evaluation]): let f.D0pL hold, `D` be inexact derivatives at `x`
satisfying (13.1.2) with `0 ≤ κ_{∇,i}` and `0 ≤ h_i ≤ κ_h`, and `L̄_f = L_f + κ_{∇,max} κ_h`
(13.1.63). For `σ ≥ 0`, `δ ∈ (0, min(1, α/(4 max(L̄_f, σ)))]` (13.1.64) and `d ∈ B_δ` with
`\overline{ΔT}_{f,j}(x, d) ≥ α δ^j/j!` for some `j ∈ [1, p]`, the model decrease satisfies
`Δm̄(d) ≥ ½ α δ^j/j!` (13.1.65). (The book's `α > 0` is not needed.) -/
theorem lemma_13_1_10 {f : ℝⁿ → ℝ} {p : ℕ} {L κg hh : ℕ → ℝ} {κh : ℝ} {x : ℝⁿ}
    {D : FormalMultilinearSeries ℝ ℝⁿ ℝ} (hf : AssumptionD0pL f p L)
    (hD : JetApprox (ftaylorSeries ℝ f x) D p (fun i => κg i * hh i))
    (hκg : ∀ i ∈ Finset.Icc 1 p, 0 ≤ κg i) (hh0 : ∀ i ∈ Finset.Icc 1 p, 0 ≤ hh i)
    (hhκ : ∀ i ∈ Finset.Icc 1 p, hh i ≤ κh) {σ α δ : ℝ} (hσ : 0 ≤ σ)
    (hδ : δ ∈ Set.Ioc 0 (min 1 (α / (4 * max (lipMax L p + ordMax p κg * κh) σ))))
    {j : ℕ} (hj : j ∈ Finset.Icc 1 p) {d : ℝⁿ} (hd : ‖d‖ ≤ δ)
    (hdec : α * δ ^ j / j ! ≤ D.taylorDecrement j d) :
    α / 2 * δ ^ j / j ! ≤ regularizedModel D p σ 0 - regularizedModel D p σ d := by
  set Lb := lipMax L p + ordMax p κg * κh
  have hLb : 0 < Lb := by
    have := hf.one_le_lipMax
    have := ordMax_nonneg hκg
    have h1p : 1 ∈ Finset.Icc 1 p :=
      Finset.mem_Icc.2 ⟨le_rfl, (Finset.mem_Icc.1 hj).1.trans (Finset.mem_Icc.1 hj).2⟩
    have : 0 ≤ κh := (hh0 1 h1p).trans (hhκ 1 h1p)
    positivity
  have hM : 0 < max Lb σ := lt_max_of_lt_left hLb
  obtain ⟨hδ0, hδ1⟩ := hδ
  refine regularizedModel_decrease_ge_of_taylorDecrement_ge (Finset.mem_Icc.1 hj).2 hσ
    (L := Lb) (fun ℓ hℓ => hf.norm_le_of_jetApprox hD hκg hh0 hhκ
      (Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hℓ).1; omega, (Finset.mem_Icc.1 hℓ).2⟩))
    hδ0.le (hδ1.trans (min_le_left _ _)) ?_ hd hdec
  have := hδ1.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at this
  linarith

/-- The test of approximate optimality used for ARqpIDA (not observable by the method,
[cartis2022evaluation], Theorem 13.1.19): `x_k` is an `(ε, δ)`-approximate `q`-th order minimizer
((12.1.25)) for *some* radii `δ ∈ (0, 1]^q`. -/
def arTest (f : ℝⁿ → ℝ) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (k : ℕ) : Prop :=
  ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 P.q, δ' j ∈ Set.Ioc 0 1) ∧
    IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε δ'

theorem arqpIDATest_univ {f : ℝⁿ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x : ℕ → ℝⁿ} :
    arqpIDATest f univ P ε x = arTest f P ε x := by
  funext k; simp only [arqpIDATest, arTest, Set.setOf_add_mem_univ]

/-- **Algorithm 13.1.2** (ARqpIDA) of [cartis2022evaluation] as a run predicate, for the
objective `f`, the (unknown) oracle constants `κ_{∇,i} ≥ 0`, constants `P`, tolerances
`ε ∈ (0, 1]^q` with `ε ≤ δ₀`, starting point `x₀`, and sequences of iterates `x`, regularization
parameters `σ`, radii `δ, δ₁, δs` (`δ^{(0)}_k, δ^{(1)}_k, δ_{s_k}`), requested accuracies `h`,
inexact jets `D` satisfying (13.1.2) up to order `p`, Step-1 displacements `dd`, orders `j_k`,
steps `s` and accuracy-improving flags `acc`; every iteration satisfies `ARqpDAStep` with the
exact-value ratio (13.1.58). The method has no termination rule; see `arTest`. This is
`IsARqpIDARun` with the feasible set `X = univ`. -/
abbrev algorithm_13_1_2 (f : ℝⁿ → ℝ) (κg : ℕ → ℝ) (P : ARqpIDAParams) (ε : ℕ → ℝ)
    (x₀ : ℝⁿ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
    (acc : ℕ → Prop) : Prop :=
  IsARqpIDARun f univ κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc

/-- **Lemma 13.1.12** ([cartis2022evaluation]): the outcomes of Step 2 at iteration `k` of an
ARqpIDA run. Assume f.D0pL, write `L̄_f = L_f + κ_{∇,max} κ_h`, assume the radii control
(13.1.69)–(13.1.70) at the earlier iterations `i < k` (only these enter the radius bound at `k`),
and let `σ̄` be any bound with `σ_i ≤ σ̄` for `i ≤ k` (the book takes `σ̄ = σ_{k,max}`). Then:
* if Step 2 is performed at `k`, then (13.1.74)
  `Δm̄_k(s_k) ≥ ¼ ς ε_{j_k} (δ^{(1)}_{k,j_k})^{j_k}/j_k! > 0`, hence `s_k ≠ 0`;
* (13.1.71) `δ^{(0)}_{k,j} ≥ δ^{(1)}_{k,j} ≥ κ^{(1)}_δ(σ̄) ε_j` for `j ∈ [1, q]`;
* if Step 2 is performed at `k` and (13.1.73)
  `h_{k,i} ≤ κ_s (ς κ^{(1)}_δ(σ̄)^q/(12 q! max(L̄_f, σ̄)))^p ε_min^{p(q+1)}` for `i ∈ [1, p]`, then
  `k ∈ 𝒯`, i.e. iteration `k` is not accuracy-improving (`¬ acc k`).
(The well-definedness of Step 2, the first part of the printed lemma, concerns the existence of
runs.) -/
theorem lemma_13_1_12 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i < k, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    {σbar : ℝ} (hσ : ∀ i ≤ k, σ i ≤ σbar) :
    ((∃ j ∈ Finset.Icc 1 P.q, ¬ arqpDAPass P ε D δ₁ dd k j) →
        0 < P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ∧
        P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ≤ arModelDec P D σ k (s k) ∧
        s k ≠ 0) ∧
      (∀ j ∈ Finset.Icc 1 P.q,
        arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh) σbar * ε j ≤ δ₁ k j ∧
          δ₁ k j ≤ δ k j) ∧
      ((∃ j ∈ Finset.Icc 1 P.q, ¬ arqpDAPass P ε D δ₁ dd k j) →
        (∀ i ∈ Finset.Icc 1 P.p, h k i ≤
          P.κs * (P.ς * arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh) σbar ^ P.q /
            (12 * P.q ! * max (lipMax L P.p + ordMax P.p κg * P.κh) σbar)) ^ P.p *
            epsMin P.q ε ^ (P.p * (P.q + 1))) → ¬ acc k) :=
  IsARqpIDARun.not_acc_of_le hf.lipschitzDerivsAnchored hf.normalized
    (fun _ _ _ => Set.mem_univ _) hrun hrc hσ

/-- **Lemma 13.1.14** ([cartis2022evaluation], corrected constant): under f.D0pL, every
ARqpIDA run satisfies `σ_k ≤ σ_max` (13.1.77) for all `k`, with `σ_max = arqpIDASigmaMax`. The book
uses `κ_s` instead of `κ_s' = max(κ_s, κ_h)`: its proof applies (13.1.47) also to long steps
`‖s_k‖ ≥ 1`, where the accuracy test (13.1.46) is not performed and only `h_{k,i} ≤ κ_h` is
known. -/
theorem lemma_13_1_14 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) (k : ℕ) :
    σ k ≤ arqpIDASigmaMax P (L P.p) (ordMax P.p κg) :=
  IsARqpIDARun.sigma_le hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun k

/-- **Lemma 13.1.15** ([cartis2022evaluation]): under f.D0pL and the radii control at every
iteration before `k`, if Step 1 of ARqpIDA branches to Step 5 at iteration `k` ((13.1.53) at
every order) and (13.1.78) `κ_{∇,max} h_{k,i} ≤ ς κ^{(1)}_δ(σ_max)^q/(4 q!) ε_min^{q+1}` for
`i ∈ [1, p]`, then
`x_k` is an `(ε, δ^{(1)}_k)`-approximate `q`-th order minimizer with `δ^{(1)}_k ∈ (0, 1]^q` (in
particular `arTest k`). (The book writes `δ_k` for the radii `δ^{(1)}_k` at the end of Step 1.) -/
theorem lemma_13_1_15 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i < k, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, arqpDAPass P ε D δ₁ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, ordMax P.p κg * h k i ≤
      P.ς * arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) ^ P.q / (4 * P.q !) *
        epsMin P.q ε ^ (P.q + 1)) :
    (∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε (δ₁ k) ∧ arTest f P ε x k := by
  have := IsARqpIDARun.arqpIDATest_of_pass hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hrc hpass hh
  rwa [Set.setOf_add_mem_univ, arqpIDATest_univ] at this

/-- **Lemma 13.1.16** ([cartis2022evaluation]): under f.D0pL, let iteration `k` of ARqpIDA be
successful with `‖s_k‖ < 1`, and let `x_{k+1}` not be approximately optimal for the radii
`δ_{k+1} = δ^{(0)}_{k+1}` (`= δ_{s_k}`). Then for some `j ∈ [1, q]` (13.1.79)
`(1 - θ) ε_j δ_{k+1,j}^j/j! ≤ (L_{f,p} + σ_max + 3 κ_{∇,max} κ_s) ∑_{ℓ=1}^j δ_{k+1,j}^ℓ/ℓ!
‖s_k‖^{p-ℓ+1}`, with `σ_max` of Lemma 13.1.14. -/
theorem lemma_13_1_16 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hs1 : ‖s k‖ < 1)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) univ P.q ε (δ (k + 1))) :
    ∃ j ∈ Finset.Icc 1 P.q, (1 - P.θ) * ε j * δ (k + 1) j ^ j / j ! ≤
      (L P.p + arqpIDASigmaMax P (L P.p) (ordMax P.p κg) + 3 * ordMax P.p κg * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) :=
  IsARqpIDARun.measure_ineq hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hk hρ hs1 (by rwa [Set.setOf_add_mem_univ])

/-- **Lemma 13.1.17** ([cartis2022evaluation], corrected constant): under f.D0pL and the radii
control at iteration `k`, if iteration `k` of ARqpIDA is successful and `x_{k+1}` is not
approximately optimal for the radii `δ_{k+1}`, then for some `j ∈ [1, q]` (13.1.80):
* if `q ≤ 2`, `‖s_k‖ ≥ ((1 - θ)/(2 j! A))^{1/(p-j+1)} ε_j^{1/(p-j+1)}`;
* if `q > 2`, `‖s_k‖ ≥ ((1 - θ) κ̂^{j-1}/(2 j! A))^{1/p} ε_j^{j/p}`,
where `A = L_{f,p} + σ_max + 3 κ_{∇,max} κ_s` and `κ̂ = min(κ_{δ,min}, (1-θ)/(2 q! A))` with
`κ_{δ,min} = ς θ/(24 max(L̄_f, σ_max))` (13.1.81). The book has `κ_{δ,min}` in place of `κ̂`; its
argument (that of Lemma 12.2.12) needs `κ_{δ,min} ≤ (1 - θ)/(2 j! A)`. -/
theorem lemma_13_1_17 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) univ P.q ε (δ (k + 1))) :
    (P.q ≤ 2 → ∃ j ∈ Finset.Icc 1 P.q,
      ((1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg))) ^ (1 / ((P.p - j + 1 : ℕ) : ℝ)) *
        ε j ^ (1 / ((P.p - j + 1 : ℕ) : ℝ)) ≤ ‖s k‖) ∧
    (2 < P.q → ∃ j ∈ Finset.Icc 1 P.q,
      ((1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
          (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) /
          (2 * j ! * arConstA P L (ordMax P.p κg))) ^ (1 / (P.p : ℝ)) *
        ε j ^ ((j : ℝ) / P.p) ≤ ‖s k‖) := by
  have h := IsARqpIDARun.norm_step_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hrc hk hρ
    (by rwa [Set.setOf_add_mem_univ])
  exact ⟨h.1, fun hq => h.2 (not_le.2 hq)⟩

/-- **Lemma 13.1.18** ([cartis2022evaluation], corrected scope and constant): under f.D0pL and
the radii control at every iteration, if iteration `k` of ARqpIDA is successful and `x_{k+1}` is
not approximately optimal (for any radii in `(0, 1]^q`), then (13.1.82)
`\overline{ΔT}_{f,p}(x_k, s_k) ≥ κ_{Δm} min_{j ∈ [1,q]} ε_j^{π_j}` and (13.1.83)
`f(x_k) - f(x_{k+1}) ≥ ½ η₁ κ_{Δm} min_j ε_j^{π_j}`, with `π_j = arPi q p j` and
`κ_{Δm} = σ_min/(p+1)! · arStepConst q p (1 - θ) A κ_{δ,min}`: for `q ≤ 2`,
`κ_{Δm} = σ_min/(p+1)! ((1-θ)/(2 q! A))^{(p+1)/(p-q+1)}`, for `q > 2`,
`κ_{Δm} = σ_min/(p+1)! ((1-θ) κ̂^{q-1}/(2 q! A))^{q(p+1)/p}` (`κ̂` as in Lemma 13.1.17). The book
states (13.1.82) for every trial iteration before approximate optimality; its proof covers the
successful iterations followed by a non-optimal iterate. -/
theorem lemma_13_1_18 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hnot : ¬ arTest f P ε x (k + 1)) :
    P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) *
        epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ (D k).taylorDecrement P.p (s k) ∧
      P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
          (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ f (x k) - f (x (k + 1)) :=
  IsARqpIDARun.decrease_ge hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) hrun hrc hk hρ (by rwa [arqpIDATest_univ])

/-- **The complexity argument of Theorem 13.1.19** ([cartis2022evaluation]), for any decrease
constant: under f.D0pL, f.Bb and the radii control at every iteration, if every
successful iteration `k` of an ARqpIDA run followed by an iterate `x_{k+1}` that is not
approximately optimal decreases `f` by at least `c > 0`, then there is a first approximately
optimal iterate `x_{k_ε}`, before which at most
`(1 + |log γ₁|/log γ₂) (f(x₀) - f_low)/c + log(σ_max/σ₀)/log γ₂ + 2 + |log γ₁|/log γ₂`
function evaluations and at most
`(f(x₀) - f_low)/c + p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 3`
derivative estimates are made. -/
theorem arqpIDA_complexity (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    {c : ℝ} (hc : 0 < c)
    (hdec : ∀ k, ¬ acc k → P.η₁ ≤ arqpIDARatio f P D x s k → ¬ arTest f P ε x (k + 1) →
      c ≤ f (x k) - f (x (k + 1))) :
    ∃ kε, IsFirstHit (arTest f P ε x) kε ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) / c) +
          (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) / c + P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  have := IsARqpIDARun.complexity hf.lipschitzDerivsAnchored hf.normalized (subset_univ _)
    (fun _ _ _ => Set.mem_univ _) (fun y _ => hb y) hrun hrc hc
    fun k hk hρ hnot => hdec k hk hρ (by rwa [arqpIDATest_univ] at hnot)
  rwa [arqpIDATest_univ] at this

/-- **Theorem 13.1.19 (1)** ([cartis2022evaluation], `q ∈ {1, 2}`, corrected): under f.D0pL,
f.Bb and the radii control (13.1.69)–(13.1.70) at every iteration, every ARqpIDA run
reaches an iterate `x_{k_ε}` that is an `(ε, δ_ε)`-approximate `q`-th order minimizer for some
radii `δ_ε ∈ (0, 1]^q` (first such index), hence `φ^1_{f,j}(x_ε) ≤ ε_j/j!` for `j ∈ [1, q]`
(`isEpsDeltaApprox_one_of_le_two`), after at most (13.1.84)
`κ^A (f(x₀) - f_low)/min_j ε_j^{(p+1)/(p-j+1)} + κ^C` function evaluations and (13.1.85)
`κ^S (f(x₀) - f_low)/min_j ε_j^{(p+1)/(p-j+1)} + κ^E |log ε_min| + κ^F + 3` derivative
estimates, where `κ_{Δm} = σ_min/(p+1)! ((1-θ)/(2 q! A))^{(p+1)/(p-q+1)}`
(`A = L_{f,p} + σ_max + 3 κ_{∇,max} κ_s`), `κ^S = 2/(η₁ κ_{Δm})`,
`κ^A = κ^S (1 + |log γ₁|/log γ₂)`, `κ^C = log(σ_max/σ₀)/log γ₂ + 2 + |log γ₁|/log γ₂`,
`κ^E = p(q+1)/|log γ_h|` and `κ^F = |log(κ_acc/κ_h)|/|log γ_h|`.
Corrections: the first-hit index is that of approximate optimality for some radii in `(0, 1]^q`
(the radii certified by the algorithm), from which radius one follows for `q ≤ 2`; `κ^C` carries
the factor `1 + |log γ₁|/log γ₂` on the `+1` of
`|𝒮_k| ≤ |𝒮_{k-1}| + 1`; the derivative count includes the initial estimate, the `+1` on `|𝒮|`
and the last accuracy-improving iteration (`+3`). -/
theorem theorem_13_1_19_i (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    (hq2 : P.q ≤ 2) :
    ∃ kε, IsFirstHit (arTest f P ε x) kε ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x kε)) univ P.q ε (fun _ => 1) ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((1 - P.θ) / (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^
              (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ)))) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f x₀ - flow) /
          epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) +
        (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
          |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((1 - P.θ) / (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^
              (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ)))) * (f x₀ - flow) /
          epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) +
        P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  set κΔm := P.σmin / ((P.p + 1)! : ℝ) *
    ((1 - P.θ) / (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^
      (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ)) with hκΔm
  set m := epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) with hm
  have hm' : epsMin P.q (fun j => ε j ^ arPi P.q P.p j) = m := by
    simp only [arPi, arPiOf, hq2, ↓reduceIte]; exact hm.symm
  have hκ' : P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
      (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) = κΔm := by
    simp only [arStepConst, arStepConstOf, hq2, ↓reduceIte]; exact hκΔm.symm
  have hA := one_le_arConstA (hf.one_le le_rfl) hrun.kappaMax_nonneg (P := P) (L := L)
  have hκpos : 0 < κΔm := by
    have := P.σmin_pos; have := P.θ_lt_one
    have : 0 < (1 - P.θ) / (2 * P.q ! * arConstA P L (ordMax P.p κg)) := by
      apply div_pos (by linarith) (by positivity)
    positivity
  have hmpos : 0 < m := Optimization.epsMin_pos P.one_le_q fun j hj =>
    Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * κΔm / 2 * m := by have := P.η₁_pos; positivity
  obtain ⟨kε, hk, h1, h2⟩ := arqpIDA_complexity hf hb hrun hrc hc fun k hk hρ hnot => by
    have := (lemma_13_1_18 hf hrun (hrc k) hk hρ hnot).2
    rwa [hm', hκ'] at this
  have hdiv : (f x₀ - flow) / (P.η₁ * κΔm / 2 * m) = 2 / (P.η₁ * κΔm) * (f x₀ - flow) / m := by
    have := P.η₁_pos; field_simp
  obtain ⟨δ', hδ', hap⟩ := hk.test
  exact ⟨kε, hk, isEpsDeltaApprox_one_of_le_two hq2 hδ' hap,
    h1.trans (le_of_eq (by rw [hdiv]; ring)),
    h2.trans (le_of_eq (by rw [hdiv]))⟩

/-- **Theorem 13.1.19 (2)** ([cartis2022evaluation], `q > 2`, corrected): as
`theorem_13_1_19_i`, with the exponents `π_j = j(p+1)/p` ((13.1.86)–(13.1.87), the exponents of
Lemma 13.1.18) and
`κ_{Δm} = σ_min/(p+1)! ((1-θ) κ̂^{q-1}/(2 q! A))^{q(p+1)/p}`, `κ̂` as in Lemma 13.1.17 (the
book's `κ^{s,2}` prints the exponent `(p+1)/(p-j+1)` and `κ_{δ,min}^{j-1}`). -/
theorem theorem_13_1_19_ii (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    (hq2 : 2 < P.q) :
    ∃ kε, IsFirstHit (arTest f P ε x) kε ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
              (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
                (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (P.q - 1) /
              (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^
              ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p))) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f x₀ - flow) /
          epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) +
        (Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
          |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
              (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
                (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (P.q - 1) /
              (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^
              ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p))) * (f x₀ - flow) /
          epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) +
        P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  have hq2' : ¬ P.q ≤ 2 := not_le.2 hq2
  set κΔm := P.σmin / ((P.p + 1)! : ℝ) *
    ((1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
      (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (P.q - 1) /
      (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^ ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p)
    with hκΔm
  set m := epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) with hm
  have hm' : epsMin P.q (fun j => ε j ^ arPi P.q P.p j) = m := by
    simp only [arPi, arPiOf, hq2', ↓reduceIte]; exact hm.symm
  have hκ' : P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
      (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) = κΔm := by
    simp only [arStepConst, arStepConstOf, hq2', ↓reduceIte]; exact hκΔm.symm
  have hLb := hrun.one_le_Lbar hf.normalized
  have hA := one_le_arConstA (hf.one_le le_rfl) hrun.kappaMax_nonneg (P := P) (L := L)
  have hκpos : 0 < κΔm := by
    have := P.σmin_pos; have := P.θ_lt_one
    have h0 : 0 < arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) :=
      lt_min (arKappaDelta1_pos (by linarith)) (div_pos (by linarith) (by positivity))
    have : 0 < (1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) ^ (P.q - 1) /
        (2 * P.q ! * arConstA P L (ordMax P.p κg)) :=
      div_pos (mul_pos (by linarith) (pow_pos h0 _)) (by positivity)
    positivity
  have hmpos : 0 < m := Optimization.epsMin_pos P.one_le_q fun j hj =>
    Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hc : 0 < P.η₁ * κΔm / 2 * m := by have := P.η₁_pos; positivity
  obtain ⟨kε, hk, h1, h2⟩ := arqpIDA_complexity hf hb hrun hrc hc fun k hk hρ hnot => by
    have := (lemma_13_1_18 hf hrun (hrc k) hk hρ hnot).2
    rwa [hm', hκ'] at this
  have hdiv : (f x₀ - flow) / (P.η₁ * κΔm / 2 * m) = 2 / (P.η₁ * κΔm) * (f x₀ - flow) / m := by
    have := P.η₁_pos; field_simp
  exact ⟨kε, hk, h1.trans (le_of_eq (by rw [hdiv]; ring)),
    h2.trans (le_of_eq (by rw [hdiv]))⟩

end ARqpIDA

section ARExistence

variable {P : ARqpIDAParams} {ε : ℕ → ℝ} (O : ℝⁿ → (ℕ → ℝ) → FormalMultilinearSeries ℝ ℝⁿ ℝ)

/-- **Runs of Algorithm 13.1.2 exist** ([cartis2022evaluation], existence part of
Lemmas 13.1.11 and 13.1.12): under f.D0pL, for constants `P`, tolerances `ε ∈ (0, 1]^q` with
`ε ≤ δ₀`, oracle constants `κ_{∇,i} ≥ 0`, a starting point `x₀` and every deterministic
oracle `O` satisfying (13.1.2) at every point for all accuracies `h ∈ (0, κ_h]^p`, and positive
initial accuracies `h_{0,i} > 0`, there is an ARqpIDA run with
`D_k = O(x_k, h_k)` which satisfies the radii control (13.1.69)–(13.1.70) at every iteration (Step 2
uses a global minimizer of the model, Lemma 12.2.9). -/
theorem exists_algorithm_13_1_2 {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {L : ℕ → ℝ}
    (hf : AssumptionD0pL f P.p L) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hεδ : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j) (hκg : ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ κg i)
    (hh₀ : ∀ i ∈ Finset.Icc 1 P.p, 0 < P.h₀ i) (x₀ : ℝⁿ)
    (hO : ∀ y h', (∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh) →
      JetApprox (ftaylorSeries ℝ f y) (O y h') P.p (fun i => κg i * h' i)) :
    ∃ (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop), algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc ∧
        (∀ k, D k = O (x k) (h k)) ∧
        ∀ k, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k := by
  obtain ⟨x, σ, δ, δ₁, δs, h, dd, jk, s, acc, hx0, hσ0, hδ0, hh0, hhm, hstep, hrc⟩ :=
    exists_arqpDA_steps O hf.lipschitzDerivsAnchored hf.normalized hε hκg x₀ P.σmin_le_σ₀
        (fun j hj => P.δ₀_mem j hj)
      (fun i hi => ⟨hh₀ i hi, P.h₀_le i hi⟩) hO
  exact ⟨x, σ, δ, δ₁, δs, h, fun i => O (x i) (h i), dd, jk, s, acc,
    ⟨hε, hεδ, hκg, hx0, mem_univ _, hσ0, hδ0, hh0, fun k => hO _ _ (hhm k), hstep⟩,
    fun _ => rfl, hrc⟩

/-- The exact jet is an oracle for (13.1.2): **ARqpIDA runs with exact derivatives and the radii
control exist** (instance of `exists_algorithm_13_1_2`). -/
theorem exists_algorithm_13_1_2_exact {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {L : ℕ → ℝ}
    (hf : AssumptionD0pL f P.p L) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hεδ : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j) (hκg : ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ κg i)
    (hh₀ : ∀ i ∈ Finset.Icc 1 P.p, 0 < P.h₀ i) (x₀ : ℝⁿ) :
    ∃ (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop), algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc ∧
        (∀ k, D k = ftaylorSeries ℝ f (x k)) ∧
        ∀ k, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k :=
  exists_algorithm_13_1_2 (fun y _ => ftaylorSeries ℝ f y) hf hε hεδ hκg hh₀ x₀ fun _ _ hh =>
    (jetApprox_self _ _).mono_err fun i hi => mul_nonneg (hκg i hi) (hh i hi).1.le

end ARExistence

end CartisGouldToint.Chapter13
