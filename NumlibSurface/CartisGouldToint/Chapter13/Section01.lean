import Numlib.Analysis.Calculus.AnchoredLipschitz
import Numlib.Optimization.ModelBased.InexactTaylor
import Numlib.Optimization.ModelBased.InexactRatio
import Numlib.Optimization.ModelBased.HighOrder.ARqp
import Numlib.Optimization.ModelBased.HighOrder.TRq
import Numlib.Optimization.ModelBased.HighOrderStep
import Numlib.Optimization.Complexity.DynamicAccuracy
import Numlib.Optimization.Complexity.Telescoping
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

* One iteration (Steps 1, 2, 4 and 5) of TRqIDA is the predicate `TRqDAStep`, and of ARqpIDA the
  predicate `ARqpDAStep`, given the value `ρ k` of the ratio. The runs `algorithm_13_1_1`,
  `algorithm_13_1_2` add the exact-value ratio (13.1.16), (13.1.58) and the oracle bounds. The
  explicit-dynamic-accuracy runs of §13.3 reuse the step predicates, so the lemmas not involving
  the formula of `ρ` are stated for the step predicates.
* The step predicates and the runs take a feasible set `X` (displacements `{e | x_k + e ∈ X}`,
  feasible trial points and starting point): `algorithm_13_1_1_feasible` and
  `algorithm_13_1_2_feasible` are TRqIDA-SC and ARqpIDA-SC of §14.2, and the algorithms of this
  chapter, `algorithm_13_1_1` and `algorithm_13_1_2`, are the case `X = univ`. The results are
  proved for the feasible runs under f.D0qL (f.D0pL) on an open convex `C ⊇ X`
  (`AssumptionD0qLOn`), with approximate optimality on `X` (`trTest_feasible`,
  `arTest_feasible`), in the `_feasible` declarations; the statements for Algorithms
  13.1.1–13.1.2 are their `X = univ` instances.
* The `_feasible` results are in turn instances of `_anchored` ones, under f.D0qL anchored on a set
  `A` (`AssumptionD0qLAnchored`, the form f.D0qLaB.X of §14.2) that contains the sublevel set
  `{y ∈ X | f(y) ≤ f(x₀)}` (hypothesis `hAX`). The objective does not increase along the runs
  (`algorithm_13_1_1_feasible.f_le`, `algorithm_13_1_2_feasible.f_le`: the ratio uses exact
  values and the predicted decrease of a trial iteration is positive), so the iterates are anchors
  (`mem_anchor`); derivatives are only evaluated at iterates, and trial points are related to them
  by Taylor's theorem anchored at the iterate.
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
  properties used (e.g. `κ_Δ` of (13.1.31) only needs `0 < κ_Δ ≤ min(1, γ₁(1-η₂)/(L_f + 4(q+1)!κ_s
  κ_{∇,max}))`; the book's value is `trKappaDelta`).

## Main definitions

* `AssumptionD0qL`, `AssumptionD0pL` (f.D0qL, f.D0pL), `epsMin`, `ordMax`, `lipMax`;
  `AssumptionD0qLOn`, `AssumptionD0pLOn` (on an open convex set, for feasible sets);
  `AssumptionD0qLAnchored`, `AssumptionD0pLAnchored` (anchored on a set, f.D0qLaB.X);
* `TRqIDAParams`, `TRqDAStep`, `algorithm_13_1_1` (TRqIDA), `trTest`, `phiHat`;
  `algorithm_13_1_1_feasible`, `trTest_feasible` (TRqIDA-SC);
* `ARqpIDAParams`, `ARqpStep1`, `ARqpStep2`, `ARqpDAStep`, `RadiiControlOf`, `RadiiControl`,
  `algorithm_13_1_2` (ARqpIDA), `arTest`; `algorithm_13_1_2_feasible`, `arTest_feasible`
  (ARqpIDA-SC); `arPiOf`, `arPi`, `arStepConstOf`, `arStepConst` (exponents and constants).

## Main results

* TRqIDA: `lemma_13_1_1` – `lemma_13_1_7`, `theorem_13_1_8`; runs exist
  (`exists_algorithm_13_1_1`, for every oracle satisfying (13.1.2)).
* ARqpIDA: `lemma_13_1_9` – `lemma_13_1_18`, `theorem_13_1_19_i`, `theorem_13_1_19_ii` (through
  `arqpIDA_complexity`); runs with the radii control exist (`exists_algorithm_13_1_2`, with the
  halving loop `exists_halving` and Step 2 from a global model minimizer); one iteration only
  involves the data at `k` and `k + 1` (`ARqpDAStep.congr`, for splicing runs), and iterations
  exist from any admissible state (`exists_arqpDA_steps`); unit radii give the radii control in
  either mode (`RadiiControlOf.of_unit`). For `q ≤ 2` without constraints the unit-radius step
  argument applies in either mode (`lemma_13_1_16_unit`, `arqpIDA_step_bound_unit`,
  `lemma_13_1_18_unit`), since `δ ↦ φ^δ_j/δ^j` is non-increasing for `j ≤ 2`.
* With a feasible set (§14.2): `lemma_13_1_3_feasible` – `lemma_13_1_7_feasible`,
  `theorem_13_1_8_feasible`, `lemma_13_1_12_feasible`, `lemma_13_1_14_feasible` –
  `lemma_13_1_18_feasible`, `arqpIDA_complexity_feasible` (Lemmas 13.1.1–13.1.2, 13.1.9, 13.1.11
  and 13.1.13 are stated for the step predicates, which carry `X`); the counts of
  accuracy-improving iterations `trqIDA_card_acc_le_feasible`, `arqpIDA_card_acc_le_feasible`.
* Under the anchored assumption: `lemma_13_1_3_anchored`, …, `arqpIDA_complexity_anchored` (one
  per `_feasible` result above); monotonicity of `f` along the runs
  (`algorithm_13_1_1_feasible.f_le`, `algorithm_13_1_2_feasible.f_le`).

## Deviations from the book

* **Algorithm 13.1.1, Step 0** prints `0 < γ₁ < 1 < γ₂ < γ₃`; the trust-region update (13.1.17)
  and the proof of Lemma 13.1.1 require `0 < γ₁ ≤ γ₂ < 1 ≤ γ₃` (`TRqIDAParams` extends
  `Optimization.TRParams`).
* **Lemmas 13.1.1 and 13.1.9** assume the radius (parameter) bound at `Δ_k` (`σ_k`); the proofs
  need it at `Δ_{k+1}` (`σ_{k+1}`), and the printed statements are false for `k = 0`.
* **Lemma 13.1.4**: the radius bound is proved for every lower bound `c` of `{φ̂_i : i ∈ 𝒯_k}`
  (`trq_delta_ge`), which contains the printed cases `𝒯_k ≠ ∅` and `𝒯_k = ∅` (`lemma_13_1_4`).
  The constant `κ_Δ` of (13.1.31) is only used through
  `0 < κ_Δ ≤ min(1, γ₁(1-η₂)/(L_f + 4(q+1)! κ_s κ_{∇,max}))` (`IsTRKappaDelta`); the printed value
  (`trKappaDelta`) has these properties when its denominator is positive.
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
  `q > 2`), which the book's condition implies (`RadiiControl.of_book`); for `q > 2` the proofs
  do not use `δ = 1` at the orders `j ≤ 2`. The `_feasible` analysis takes the mode as a
  parameter (`RadiiControlOf u`: unit radii if `u`, the lower bounds at every order if `¬ u`,
  with exponents `arPiOf u`), so that the lower-bound mode also covers `q ≤ 2` when unit radii
  are not available (§14.2); `RadiiControl` is the mode `u = (q ≤ 2)`.
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

/-! ### Minima and maxima over the orders -/

section Orders

variable {q : ℕ} {ε : ℕ → ℝ} {j : ℕ}

/-- The smallest tolerance `ε_min = min_{j ∈ [1, q]} ε_j` (`0` if `q = 0`). -/
noncomputable def epsMin (q : ℕ) (ε : ℕ → ℝ) : ℝ :=
  if h : (Finset.Icc 1 q).Nonempty then (Finset.Icc 1 q).inf' h ε else 0

/-- The largest value `max_{i ∈ [1, r]} κ_i` (`0` if `r = 0`), used for `κ_{∇,max}` and
`h_{k,max}`. -/
noncomputable def ordMax (r : ℕ) (κ : ℕ → ℝ) : ℝ :=
  if h : (Finset.Icc 1 r).Nonempty then (Finset.Icc 1 r).sup' h κ else 0

theorem epsMin_eq (hne : (Finset.Icc 1 q).Nonempty) : epsMin q ε = (Finset.Icc 1 q).inf' hne ε :=
  dite_eq_left_of_eq_true (eq_true hne)

theorem ordMax_eq (hne : (Finset.Icc 1 q).Nonempty) : ordMax q ε = (Finset.Icc 1 q).sup' hne ε :=
  dite_eq_left_of_eq_true (eq_true hne)

theorem epsMin_le (hj : j ∈ Finset.Icc 1 q) : epsMin q ε ≤ ε j := by
  rw [epsMin_eq ⟨j, hj⟩]
  exact Finset.inf'_le _ hj

theorem le_ordMax (hj : j ∈ Finset.Icc 1 q) : ε j ≤ ordMax q ε := by
  rw [ordMax_eq ⟨j, hj⟩]
  exact Finset.le_sup' _ hj

theorem exists_epsMin_eq (hq : 1 ≤ q) : ∃ j ∈ Finset.Icc 1 q, epsMin q ε = ε j := by
  have hne : (Finset.Icc 1 q).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hq⟩⟩
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' hne ε
  exact ⟨j, hj, by rw [epsMin_eq hne, he]⟩

theorem exists_ordMax_eq (hq : 1 ≤ q) : ∃ j ∈ Finset.Icc 1 q, ordMax q ε = ε j := by
  have hne : (Finset.Icc 1 q).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hq⟩⟩
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup' hne ε
  exact ⟨j, hj, by rw [ordMax_eq hne, he]⟩

theorem le_epsMin_iff (hq : 1 ≤ q) {c : ℝ} : c ≤ epsMin q ε ↔ ∀ j ∈ Finset.Icc 1 q, c ≤ ε j := by
  refine ⟨fun h j hj => h.trans (epsMin_le hj), fun h => ?_⟩
  obtain ⟨j, hj, he⟩ := exists_epsMin_eq (ε := ε) hq
  exact he ▸ h j hj

theorem ordMax_le_iff (hq : 1 ≤ q) {c : ℝ} : ordMax q ε ≤ c ↔ ∀ j ∈ Finset.Icc 1 q, ε j ≤ c := by
  refine ⟨fun h j hj => (le_ordMax hj).trans h, fun h => ?_⟩
  obtain ⟨j, hj, he⟩ := exists_ordMax_eq (ε := ε) hq
  exact he ▸ h j hj

theorem epsMin_pos (hq : 1 ≤ q) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) : 0 < epsMin q ε := by
  obtain ⟨j, hj, he⟩ := exists_epsMin_eq (ε := ε) hq
  exact he ▸ hε j hj

theorem epsMin_le_one (hq : 1 ≤ q) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ≤ 1) : epsMin q ε ≤ 1 :=
  (epsMin_le (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)).trans (hε 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩))

theorem ordMax_nonneg (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) : 0 ≤ ordMax q ε := by
  by_cases hq : 1 ≤ q
  · obtain ⟨j, hj, he⟩ := exists_ordMax_eq (ε := ε) hq
    exact he ▸ hε j hj
  · have hne : ¬ (Finset.Icc 1 q).Nonempty := by
      rintro ⟨j, hj⟩
      exact hq ((Finset.mem_Icc.1 hj).1.trans (Finset.mem_Icc.1 hj).2)
    rw [ordMax, dite_eq_right_of_eq_false (eq_false hne)]

/-- Scaling all values by `c ≥ 0` scales the maximum. -/
theorem ordMax_mul (hq : 1 ≤ q) {c : ℝ} (hc : 0 ≤ c) (κ : ℕ → ℝ) :
    ordMax q (fun i => c * κ i) = c * ordMax q κ := by
  have hne : (Finset.Icc 1 q).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hq⟩⟩
  refine le_antisymm ((ordMax_le_iff hq).2 fun i hi =>
    mul_le_mul_of_nonneg_left (le_ordMax hi) hc) ?_
  obtain ⟨j, hj, he⟩ := exists_ordMax_eq (ε := κ) hq
  rw [he]
  exact le_ordMax (ε := fun i => c * κ i) hj

/-- The values agree on `[1, q]`: same maximum. -/
theorem ordMax_congr {κ κ' : ℕ → ℝ} (h : ∀ i ∈ Finset.Icc 1 q, κ i = κ' i) :
    ordMax q κ = ordMax q κ' := by
  unfold ordMax
  split_ifs with hne
  · exact Finset.sup'_congr hne rfl h
  · rfl

/-- The largest Lipschitz constant `L_f = max_{j ∈ [0, q]} L_{f,j}` (13.1.23). -/
noncomputable def lipMax (L : ℕ → ℝ) (q : ℕ) : ℝ :=
  (Finset.range (q + 1)).sup' nonempty_range_add_one L

theorem le_lipMax {L : ℕ → ℝ} {i : ℕ} (hi : i ≤ q) : L i ≤ lipMax L q :=
  Finset.le_sup' L (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

end Orders

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

/-- **(A.19) under f.D0qL**: `|f(x + s) - T_{f,j}(x, s)| ≤ L_{f,j}/(j+1)! ‖s‖^{j+1}`, in the form
`|f(x + s) - (f(x) - ΔT_{f,j}(x, s))|`. -/
theorem AssumptionD0qL.abs_sub_le (hf : AssumptionD0qL f q L) {j : ℕ} (hj : j ≤ q) (x s : ℝⁿ) :
    |f (x + s) - (f x - (ftaylorSeries ℝ f x).taylorDecrement j s)| ≤
      L j / ((j + 1)! : ℝ) * ‖s‖ ^ (j + 1) := by
  rw [ftaylorSeries_taylorDecrement_eq, sub_sub_cancel]
  exact abs_sub_taylorPolynomial_le_of_lipschitz convex_univ
    (fun y _ => hf.contDiffAt hj y) (hf.lipschitz hj) (mem_univ x) (mem_univ (x + s))

/-- **(13.1.24)**: under f.D0qL, `‖∇^i f(x)‖ ≤ L_{f,i-1} ≤ L_f` for `i ∈ [1, q]`. -/
theorem AssumptionD0qL.norm_iteratedFDeriv_le (hf : AssumptionD0qL f q L) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 q) (x : ℝⁿ) : ‖iteratedFDeriv ℝ i f x‖ ≤ lipMax L q := by
  obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.1 hi
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hm : m ≤ q := by omega
  exact (norm_iteratedFDeriv_succ_le_of_lipschitzOn isOpen_univ
    (zero_le_one.trans (hf.one_le hm)) (hf.lipschitz hm) (mem_univ x)).trans (le_lipMax hm)

/-- **(13.1.24), (13.1.63)**: inexact derivatives within `κ_{∇,i} h_i` of the exact ones, with
`0 ≤ κ_{∇,i}`, `0 ≤ h_i ≤ κ_h`, satisfy `‖∇̄^i f(x)‖ ≤ L_f + κ_{∇,max} κ_h` for `i ∈ [1, q]`. -/
theorem AssumptionD0qL.norm_le_of_jetApprox (hf : AssumptionD0qL f q L)
    {D : FormalMultilinearSeries ℝ ℝⁿ ℝ} {κg hh : ℕ → ℝ} {κh : ℝ} {x : ℝⁿ}
    (hD : JetApprox (ftaylorSeries ℝ f x) D q (fun i => κg i * hh i))
    (hκ : ∀ i ∈ Finset.Icc 1 q, 0 ≤ κg i) (hh0 : ∀ i ∈ Finset.Icc 1 q, 0 ≤ hh i)
    (hhκ : ∀ i ∈ Finset.Icc 1 q, hh i ≤ κh) {i : ℕ} (hi : i ∈ Finset.Icc 1 q) :
    ‖D i‖ ≤ lipMax L q + ordMax q κg * κh :=
  norm_le_add_mul_of_jetApprox hD hi (hf.norm_iteratedFDeriv_le hi x) (hκ i hi) (le_ordMax hi)
    (hh0 i hi) (hhκ i hi)

end Assumption

/-- **f.D0qL on an open convex set** `C` (the form of f.D0qL used with a feasible set `X ⊆ C`,
[cartis2022evaluation] §14.2, for the TRqIDA-SC, TRqEDA-SC, ARqpIDA-SC and ARqpEDA-SC
algorithms): `C` is open and convex, `f` is `C^q` near every point of `C` and, for every
`j ∈ [0, q]`, the `j`-th derivative is `L_{f,j}`-Lipschitz on `C` with `L_{f,j} ≥ 1`. With
`C = univ` this is `AssumptionD0qL` (`AssumptionD0qL.on_univ`, `assumptionD0qLOn_univ_iff`). -/
structure AssumptionD0qLOn (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (q : ℕ) (L : ℕ → ℝ) : Prop where
  /-- `C` is open. -/
  isOpen : IsOpen C
  /-- `C` is convex. -/
  convex : Convex ℝ C
  /-- `f` is `C^q` near every point of `C`. -/
  contDiffAt_q : ∀ y ∈ C, ContDiffAt ℝ q f y
  /-- The constants are at least `1`. -/
  one_le : ∀ {j : ℕ}, j ≤ q → 1 ≤ L j
  /-- The `j`-th derivative is `L_{f,j}`-Lipschitz on `C`. -/
  lipschitz : ∀ {j : ℕ}, j ≤ q → IteratedFDerivLipschitzOn f j (L j) C

/-- **f.D0pL on an open convex set** `C`: `AssumptionD0qLOn` with order `p`. -/
abbrev AssumptionD0pLOn (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (L : ℕ → ℝ) : Prop :=
  AssumptionD0qLOn f C p L

section AssumptionOn

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {q : ℕ} {L : ℕ → ℝ}

/-- f.D0qL is f.D0qL on `univ`. -/
theorem AssumptionD0qL.on_univ (hf : AssumptionD0qL f q L) : AssumptionD0qLOn f univ q L :=
  ⟨isOpen_univ, convex_univ, fun _ _ => hf.1.contDiffAt, hf.one_le, hf.lipschitz⟩

theorem assumptionD0qLOn_univ_iff : AssumptionD0qLOn f univ q L ↔ AssumptionD0qL f q L :=
  ⟨fun h => ⟨contDiff_iff_contDiffAt.2 fun y => h.contDiffAt_q y (mem_univ y),
    fun _ hj => ⟨h.one_le hj, h.lipschitz hj⟩⟩, AssumptionD0qL.on_univ⟩

/-- The assumption of order `q` implies the assumption of every lower order. -/
theorem AssumptionD0qLOn.mono (hf : AssumptionD0qLOn f C q L) {r : ℕ} (hr : r ≤ q) :
    AssumptionD0qLOn f C r L :=
  ⟨hf.isOpen, hf.convex, fun y hy => (hf.contDiffAt_q y hy).of_le (by exact_mod_cast hr),
    fun hj => hf.one_le (hj.trans hr), fun hj => hf.lipschitz (hj.trans hr)⟩

theorem AssumptionD0qLOn.one_le_lipMax (hf : AssumptionD0qLOn f C q L) : 1 ≤ lipMax L q :=
  (hf.one_le (Nat.zero_le q)).trans (le_lipMax (Nat.zero_le q))

theorem AssumptionD0qLOn.contDiffAt (hf : AssumptionD0qLOn f C q L) {j : ℕ} (hj : j ≤ q)
    {y : ℝⁿ} (hy : y ∈ C) : ContDiffAt ℝ j f y :=
  (hf.contDiffAt_q y hy).of_le (by exact_mod_cast hj)

/-- **(A.19) under f.D0qL on `C`**: for `x, x + s ∈ C`,
`|f(x + s) - T_{f,j}(x, s)| ≤ L_{f,j}/(j+1)! ‖s‖^{j+1}`. -/
theorem AssumptionD0qLOn.abs_sub_le (hf : AssumptionD0qLOn f C q L) {j : ℕ} (hj : j ≤ q)
    {x s : ℝⁿ} (hx : x ∈ C) (hxs : x + s ∈ C) :
    |f (x + s) - (f x - (ftaylorSeries ℝ f x).taylorDecrement j s)| ≤
      L j / ((j + 1)! : ℝ) * ‖s‖ ^ (j + 1) := by
  rw [ftaylorSeries_taylorDecrement_eq, sub_sub_cancel]
  exact abs_sub_taylorPolynomial_le_of_lipschitz hf.convex
    (fun y hy => hf.contDiffAt hj hy) (hf.lipschitz hj) hx hxs

/-- **(13.1.24) on `C`**: `‖∇^i f(x)‖ ≤ L_{f,i-1} ≤ L_f` for `i ∈ [1, q]` and `x ∈ C`. -/
theorem AssumptionD0qLOn.norm_iteratedFDeriv_le (hf : AssumptionD0qLOn f C q L) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 q) {x : ℝⁿ} (hx : x ∈ C) : ‖iteratedFDeriv ℝ i f x‖ ≤ lipMax L q := by
  obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.1 hi
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hm : m ≤ q := by omega
  exact (norm_iteratedFDeriv_succ_le_of_lipschitzOn hf.isOpen
    (zero_le_one.trans (hf.one_le hm)) (hf.lipschitz hm) hx).trans (le_lipMax hm)

/-- **(13.1.24), (13.1.63) on `C`**: inexact derivatives at `x ∈ C` within `κ_{∇,i} h_i` of the
exact ones, with `0 ≤ κ_{∇,i}`, `0 ≤ h_i ≤ κ_h`, satisfy `‖∇̄^i f(x)‖ ≤ L_f + κ_{∇,max} κ_h`. -/
theorem AssumptionD0qLOn.norm_le_of_jetApprox (hf : AssumptionD0qLOn f C q L)
    {D : FormalMultilinearSeries ℝ ℝⁿ ℝ} {κg hh : ℕ → ℝ} {κh : ℝ} {x : ℝⁿ} (hx : x ∈ C)
    (hD : JetApprox (ftaylorSeries ℝ f x) D q (fun i => κg i * hh i))
    (hκ : ∀ i ∈ Finset.Icc 1 q, 0 ≤ κg i) (hh0 : ∀ i ∈ Finset.Icc 1 q, 0 ≤ hh i)
    (hhκ : ∀ i ∈ Finset.Icc 1 q, hh i ≤ κh) {i : ℕ} (hi : i ∈ Finset.Icc 1 q) :
    ‖D i‖ ≤ lipMax L q + ordMax q κg * κh :=
  norm_le_add_mul_of_jetApprox hD hi (hf.norm_iteratedFDeriv_le hi hx) (hκ i hi) (le_ordMax hi)
    (hh0 i hi) (hhκ i hi)

end AssumptionOn

/-- **f.D0qL anchored on a set** (the form of f.D0qLaB.X / f.D0pLaB.X of [cartis2022evaluation]
§14.2.1, (14.2.9) with `j ∈ [0, q]`): `C` is open and convex, `A ⊆ C`, `f` is `C^q` near every
point of `C` and, for every `j ∈ [0, q]`, `‖∇^j f(x) - ∇^j f(y)‖ ≤ L_{f,j} ‖x - y‖` for `x ∈ A` and
`y ∈ C`, with `L_{f,j} ≥ 1`. In the applications, `A` is (a superset of) the sublevel set
`{y ∈ X | f(y) ≤ f(x₀)}` of a feasible set `X` and a starting point `x₀`, which contains the
iterates of the dynamic-accuracy methods: the derivative estimates are made at iterates, and the
trial points are related to them by Taylor's theorem anchored at the iterate. f.D0qL on `C` gives
it for every `A ⊆ C` (`AssumptionD0qLOn.anchored`). -/
structure AssumptionD0qLAnchored (f : ℝⁿ → ℝ) (C A : Set ℝⁿ) (q : ℕ) (L : ℕ → ℝ) : Prop where
  /-- `C` is open. -/
  isOpen : IsOpen C
  /-- `C` is convex. -/
  convex : Convex ℝ C
  /-- The anchors lie in `C`. -/
  subset : A ⊆ C
  /-- `f` is `C^q` near every point of `C`. -/
  contDiffAt_q : ∀ y ∈ C, ContDiffAt ℝ q f y
  /-- The constants are at least `1`. -/
  one_le : ∀ {j : ℕ}, j ≤ q → 1 ≤ L j
  /-- The `j`-th derivative is `L_{f,j}`-Lipschitz anchored in `A` with respect to `C`
  ((14.2.9)). -/
  lipschitzAnchored : ∀ {j : ℕ}, j ≤ q → IteratedFDerivLipschitzAnchored f j (L j) A C

/-- **f.D0pL anchored on a set**: `AssumptionD0qLAnchored` with order `p`. -/
abbrev AssumptionD0pLAnchored (f : ℝⁿ → ℝ) (C A : Set ℝⁿ) (p : ℕ) (L : ℕ → ℝ) : Prop :=
  AssumptionD0qLAnchored f C A p L

/-- f.D0qL on `C` is f.D0qL anchored on every `A ⊆ C`. -/
theorem AssumptionD0qLOn.anchored {f : ℝⁿ → ℝ} {C A : Set ℝⁿ} {q : ℕ} {L : ℕ → ℝ}
    (hf : AssumptionD0qLOn f C q L) (hA : A ⊆ C) : AssumptionD0qLAnchored f C A q L :=
  ⟨hf.isOpen, hf.convex, hA, hf.contDiffAt_q, hf.one_le,
    fun hj => (hf.lipschitz hj).anchored hA⟩

namespace AssumptionD0qLAnchored

variable {f : ℝⁿ → ℝ} {C A A' : Set ℝⁿ} {q : ℕ} {L : ℕ → ℝ}

/-- Shrinking the anchor set. -/
theorem mono_left (hf : AssumptionD0qLAnchored f C A q L) (hA : A' ⊆ A) :
    AssumptionD0qLAnchored f C A' q L :=
  ⟨hf.isOpen, hf.convex, hA.trans hf.subset, hf.contDiffAt_q, hf.one_le,
    fun hj => (hf.lipschitzAnchored hj).mono_left hA⟩

/-- The assumption of order `q` implies the assumption of every lower order. -/
theorem mono (hf : AssumptionD0qLAnchored f C A q L) {r : ℕ} (hr : r ≤ q) :
    AssumptionD0qLAnchored f C A r L :=
  ⟨hf.isOpen, hf.convex, hf.subset,
    fun y hy => (hf.contDiffAt_q y hy).of_le (by exact_mod_cast hr),
    fun hj => hf.one_le (hj.trans hr), fun hj => hf.lipschitzAnchored (hj.trans hr)⟩

theorem one_le_lipMax (hf : AssumptionD0qLAnchored f C A q L) : 1 ≤ lipMax L q :=
  (hf.one_le (Nat.zero_le q)).trans (le_lipMax (Nat.zero_le q))

theorem contDiffAt (hf : AssumptionD0qLAnchored f C A q L) {j : ℕ} (hj : j ≤ q) {y : ℝⁿ}
    (hy : y ∈ C) : ContDiffAt ℝ j f y :=
  (hf.contDiffAt_q y hy).of_le (by exact_mod_cast hj)

/-- The anchored condition at an anchor `x ∈ A`:
`‖∇^j f(y) - ∇^j f(x)‖ ≤ L_{f,j} ‖y - x‖` for `y ∈ C`. -/
theorem lipschitzAt (hf : AssumptionD0qLAnchored f C A q L) {j : ℕ} (hj : j ≤ q) {x : ℝⁿ}
    (hx : x ∈ A) :
    ∀ y ∈ C, ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x‖ ≤ L j * ‖y - x‖ :=
  (hf.lipschitzAnchored hj).lipschitzAt hx

/-- **(A.19) anchored at `x ∈ A`**: for `x + s ∈ C`,
`|f(x + s) - T_{f,j}(x, s)| ≤ L_{f,j}/(j+1)! ‖s‖^{j+1}`. -/
theorem abs_sub_le (hf : AssumptionD0qLAnchored f C A q L) {j : ℕ} (hj : j ≤ q) {x s : ℝⁿ}
    (hx : x ∈ A) (hxs : x + s ∈ C) :
    |f (x + s) - (f x - (ftaylorSeries ℝ f x).taylorDecrement j s)| ≤
      L j / ((j + 1)! : ℝ) * ‖s‖ ^ (j + 1) := by
  rw [ftaylorSeries_taylorDecrement_eq, sub_sub_cancel, ← Real.norm_eq_abs]
  exact norm_sub_taylorPolynomial_le_of_lipschitzAnchored hf.convex
    (fun y hy => hf.contDiffAt hj hy) (hf.lipschitzAt hj hx) (hf.subset hx) hxs

/-- **(13.1.24) at the anchors**: `‖∇^i f(x)‖ ≤ L_{f,i-1} ≤ L_f` for `i ∈ [1, q]` and `x ∈ A`
(the anchored condition of order `i - 1` at the interior point `x` bounds the derivative there). -/
theorem norm_iteratedFDeriv_le (hf : AssumptionD0qLAnchored f C A q L) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 q) {x : ℝⁿ} (hx : x ∈ A) : ‖iteratedFDeriv ℝ i f x‖ ≤ lipMax L q := by
  obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.1 hi
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hm : m ≤ q := by omega
  rw [← norm_fderiv_iteratedFDeriv]
  refine (norm_fderiv_le_of_lip' ℝ (zero_le_one.trans (hf.one_le hm)) ?_).trans (le_lipMax hm)
  filter_upwards [hf.isOpen.mem_nhds (hf.subset hx)] with y hy
  exact hf.lipschitzAt hm hx y hy

/-- **(13.1.24), (13.1.63) at the anchors**: inexact derivatives at `x ∈ A` within `κ_{∇,i} h_i`
of the exact ones, with `0 ≤ κ_{∇,i}`, `0 ≤ h_i ≤ κ_h`, satisfy
`‖∇̄^i f(x)‖ ≤ L_f + κ_{∇,max} κ_h`. -/
theorem norm_le_of_jetApprox (hf : AssumptionD0qLAnchored f C A q L)
    {D : FormalMultilinearSeries ℝ ℝⁿ ℝ} {κg hh : ℕ → ℝ} {κh : ℝ} {x : ℝⁿ} (hx : x ∈ A)
    (hD : JetApprox (ftaylorSeries ℝ f x) D q (fun i => κg i * hh i))
    (hκ : ∀ i ∈ Finset.Icc 1 q, 0 ≤ κg i) (hh0 : ∀ i ∈ Finset.Icc 1 q, 0 ≤ hh i)
    (hhκ : ∀ i ∈ Finset.Icc 1 q, hh i ≤ κh) {i : ℕ} (hi : i ∈ Finset.Icc 1 q) :
    ‖D i‖ ≤ lipMax L q + ordMax q κg * κh :=
  norm_le_add_mul_of_jetApprox hD hi (hf.norm_iteratedFDeriv_le hi hx) (hκ i hi) (le_ordMax hi)
    (hh0 i hi) (hhκ i hi)

end AssumptionD0qLAnchored

/-! ### Elementary bounds -/

section Elementary

/-- The decrement is small for short steps: if `‖D_i‖ ≤ Lb` for `i ∈ [1, j]`, `0 ≤ Lb` and
`‖s‖ ≤ 1`, then `ΔT_j(s) ≤ 2 Lb ‖s‖` (sum bound (A.34)). -/
theorem taylorDecrement_le_two_mul {D : FormalMultilinearSeries ℝ ℝⁿ ℝ} {j : ℕ} {Lb : ℝ}
    (hLb : 0 ≤ Lb) (hD : ∀ i ∈ Finset.Icc 1 j, ‖D i‖ ≤ Lb) {s : ℝⁿ} (hs : ‖s‖ ≤ 1) :
    D.taylorDecrement j s ≤ 2 * Lb * ‖s‖ := by
  refine (le_abs_self _).trans ((D.abs_taylorDecrement_le j s).trans ?_)
  calc ∑ i ∈ Finset.Icc 1 j, ‖D i‖ * ‖s‖ ^ i / i !
      ≤ ∑ i ∈ Finset.Icc 1 j, Lb * (‖s‖ ^ i / i !) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [mul_div_assoc]
        gcongr
        exact hD i hi
    _ = Lb * ∑ i ∈ Finset.Icc 1 j, ‖s‖ ^ i / i ! := by rw [Finset.mul_sum]
    _ ≤ Lb * (2 * ‖s‖) := by gcongr; exact sum_pow_div_factorial_le_two_mul (norm_nonneg s) hs j
    _ = 2 * Lb * ‖s‖ := by ring

/-- `a b ≤ 1` for `a, b ∈ [0, 1]`. -/
theorem mul_le_one_of_le_one {a b : ℝ} (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    a * b ≤ 1 :=
  (mul_le_mul ha1 hb1 hb0 zero_le_one).trans_eq (one_mul 1)

/-- `Optimization.card_accuracyImproving_le_of_pow` allowing `κ_h = 0`: if moreover
`h_max(j) ≤ κ_h` for `j ≤ k`, then for `κ_h = 0` no iteration is accuracy-improving (the threshold
`κ_acc ε^N` is positive), and the bound holds with `log(κ_acc/0) = 0`. -/
theorem card_accuracyImproving_le_of_pow_of_nonneg {acc : ℕ → Prop} {hmax : ℕ → ℝ}
    {γh κh κacc ε : ℝ} {N : ℕ} (hγh : 0 < γh) (hγh1 : γh < 1) (hκh : 0 ≤ κh) (hκacc : 0 < κacc)
    (hε : 0 < ε) (hh0 : hmax 0 ≤ κh) {k : ℕ} (hle : ∀ j ≤ k, hmax j ≤ κh)
    (hacc : ∀ j ≤ k, acc j → hmax (j + 1) = γh * hmax j)
    (hnacc : ∀ j ≤ k, ¬ acc j → hmax (j + 1) = hmax j)
    (hc : ∀ j ≤ k, acc j → κacc * ε ^ N < hmax j) :
    ((successSet acc k).card : ℝ) ≤
      (N * |Real.log ε| + |Real.log (κacc / κh)|) / |Real.log γh| + 1 := by
  rcases hκh.lt_or_eq with hκh | hκh
  · exact card_accuracyImproving_le_of_pow hγh hγh1 hκh hκacc hε hh0 hacc hnacc hc
  · have h0 : successSet acc k = ∅ := by
      ext j
      simp only [mem_successSet, Finset.notMem_empty, iff_false, not_and]
      intro hj ha
      have := hc j hj ha
      have := hle j hj
      have : 0 < κacc * ε ^ N := by positivity
      linarith
    rw [h0, Finset.card_empty, Nat.cast_zero]
    positivity


/-- A sequence that does not increase on `[0, k]` stays below its first term:
`u_{i+1} ≤ u_i` for `i < k` gives `u_k ≤ u_0`. -/
theorem le_zero_of_succ_le {u : ℕ → ℝ} {k : ℕ} (h : ∀ i < k, u (i + 1) ≤ u i) : u k ≤ u 0 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (h k k.lt_succ_self).trans (ih fun i hi => h i (hi.trans k.lt_succ_self))

end Elementary

/-! ### TRqIDA: constants and one iteration -/

/-- The constants of Algorithm 13.1.1 (TRqIDA, [cartis2022evaluation], Step 0): the trust-region
constants (`0 < η₁ ≤ η₂ < 1`, `0 < γ₁ ≤ γ₂ < 1 ≤ γ₃`, `Δ₀ > 0`), the criticality order `q ≥ 1`,
`ϑ ∈ (0, 1]` with `ϑ ≤ Δ₀ ≤ Δ_max`, `ς ∈ (0, 1]`, `γ_h ∈ (0, 1)`, `κ_s > 0`, and initial
accuracies `0 < h_{0,i} ≤ κ_h` (`i ∈ [1, q]`). The tolerance-dependent requirement
`ϑ ≥ ε_min` is part of the run predicate. The printed Step 0 reads `0 < γ₁ < 1 < γ₂ < γ₃`; the
update (13.1.17) and Lemma 13.1.1 require `γ₂ < 1`. -/
structure TRqIDAParams extends TRParams where
  /-- The criticality order. -/
  q : ℕ
  /-- The threshold on the optimality radius. -/
  ϑ : ℝ
  /-- The maximal trust-region radius. -/
  Δmax : ℝ
  /-- The accuracy reduction factor. -/
  γh : ℝ
  /-- The constant of the accuracy test (13.1.9). -/
  κs : ℝ
  /-- The bound on the initial accuracies. -/
  κh : ℝ
  /-- The fraction of the measure achieved by the Step-1 displacements. -/
  ς : ℝ
  /-- The initial requested accuracies. -/
  h₀ : ℕ → ℝ
  one_le_q : 1 ≤ q
  ϑ_pos : 0 < ϑ
  ϑ_le_one : ϑ ≤ 1
  ϑ_le_Δ₀ : ϑ ≤ Δ₀
  Δ₀_le_Δmax : Δ₀ ≤ Δmax
  ς_pos : 0 < ς
  ς_le_one : ς ≤ 1
  γh_pos : 0 < γh
  γh_lt_one : γh < 1
  κs_pos : 0 < κs
  h₀_pos : ∀ i ∈ Finset.Icc 1 q, 0 < h₀ i
  h₀_le : ∀ i ∈ Finset.Icc 1 q, h₀ i ≤ κh

namespace TRqIDAParams

variable (P : TRqIDAParams)

theorem κh_pos : 0 < P.κh :=
  (P.h₀_pos 1 (Finset.mem_Icc.2 ⟨le_rfl, P.one_le_q⟩)).trans_le
    (P.h₀_le 1 (Finset.mem_Icc.2 ⟨le_rfl, P.one_le_q⟩))

theorem one_mem_Icc : 1 ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨le_rfl, P.one_le_q⟩

end TRqIDAParams

section TRStep

variable {X : Set ℝⁿ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x : ℕ → ℝⁿ} {Δ : ℕ → ℝ}
  {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ}
  {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {ρ : ℕ → ℝ} {k : ℕ}

/-- The optimality radius `δ_k = min(Δ_k, ϑ)` of TRqIDA (Step 1). -/
noncomputable abbrev trRadius (P : TRqIDAParams) (Δ : ℕ → ℝ) (k : ℕ) : ℝ := min (Δ k) P.ϑ

/-- The Step-1.2 test (13.1.14) at order `j` fails to certify optimality:
`\overline{ΔT}_{f,j}(x_k, d_{k,j}) > ½ ς ε_j δ_k^j / j!`. -/
def trFail (P : TRqIDAParams) (ε : ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (Δ : ℕ → ℝ) (dd : ℕ → ℕ → ℝⁿ) (k j : ℕ) : Prop :=
  P.ς * ε j * trRadius P Δ k ^ j / j ! / 2 < (D k).taylorDecrement j (dd k j)

/-- The scaled criticality `φ̂_{f,k} = j_k! \overline{ΔT}_{f,j_k}(x_k, d_k) / δ_k^{j_k}` of
(13.1.25), for data `D`, order `j`, radius `δ` and displacement `d`. -/
noncomputable def phiHat (D : FormalMultilinearSeries ℝ ℝⁿ ℝ) (j : ℕ) (δ : ℝ) (d : ℝⁿ) : ℝ :=
  j ! * D.taylorDecrement j d / δ ^ j

/-- Step 2 of TRqIDA ((13.1.15) and the accuracy test (13.1.9)), entered at the least order `j_k`
at which (13.1.14) holds: `s_k ∈ B_{Δ_k}` (feasible) does at least as well as `d_k = d_{k,j_k}`
on the order-`j_k` inexact decrement, and the iteration is accuracy-improving iff (13.1.9)
fails for some `i ∈ [1, q]`. -/
structure TRqStep2 (X : Set ℝⁿ) (P : TRqIDAParams) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ)
    (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ)
    (s : ℕ → ℝⁿ) (acc : ℕ → Prop) (k : ℕ) : Prop where
  /-- `j_k ∈ [1, q]`. -/
  jk_mem : jk k ∈ Finset.Icc 1 P.q
  /-- (13.1.14) holds at `j_k`. -/
  fail : trFail P ε D Δ dd k (jk k)
  /-- `j_k` is the least such order. -/
  pass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < jk k → ¬ trFail P ε D Δ dd k j
  /-- The trial point is feasible. -/
  mem : x k + s k ∈ X
  /-- `s_k ∈ B_{Δ_k}`. -/
  norm_le : ‖s k‖ ≤ Δ k
  /-- (13.1.15). -/
  dec_le : (D k).taylorDecrement (jk k) (dd k (jk k)) ≤ (D k).taylorDecrement (jk k) (s k)
  /-- Branching to Step 5 iff the accuracy test (13.1.9) fails. -/
  acc_iff : acc k ↔ ∃ i ∈ Finset.Icc 1 P.q, P.κs * ‖s k‖ ^ (P.q - i + 1) < h k i

/-- **One iteration of TRqIDA / TRqEDA** ([cartis2022evaluation], Algorithm 13.1.1, Steps 1, 2,
4, 5) on the feasible set `X`, given the ratio `ρ k` of Step 3: Step-1 displacements `d_{k,j}` with
(13.1.13) for every order; if (13.1.14) fails at every order the iteration is accuracy-improving,
otherwise Step 2 (`TRqStep2`); a trial iteration (`¬ acc k`) accepts or rejects the step and updates
the radius by (13.1.17) (capped by `Δ_max`), keeps the accuracies, and keeps the derivative
estimates when the step is rejected; an accuracy-improving iteration keeps `x_k` and `Δ_k` and
multiplies the accuracies by `γ_h` (13.1.18). -/
structure TRqDAStep (X : Set ℝⁿ) (P : TRqIDAParams) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ)
    (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ)
    (s : ℕ → ℝⁿ) (acc : ℕ → Prop) (ρ : ℕ → ℝ) (k : ℕ) : Prop where
  /-- (13.1.13): `ς`-approximate optimality displacements at every order. -/
  witness : ∀ j ∈ Finset.Icc 1 P.q, IsApproxMeasureStep ((D k).taylorDecrement j)
    (trRadius P Δ k) {e | x k + e ∈ X} P.ς (dd k j)
  /-- Step 1 → Step 5 when (13.1.14) fails at every order. -/
  acc_of_pass : (∀ j ∈ Finset.Icc 1 P.q, ¬ trFail P ε D Δ dd k j) → acc k
  /-- Step 2 when (13.1.14) holds at some order. -/
  step2 : (∃ j ∈ Finset.Icc 1 P.q, trFail P ε D Δ dd k j) →
    TRqStep2 X P ε x Δ h D dd jk s acc k
  /-- Steps 3–4 on a trial iteration. -/
  accept : ¬ acc k → TRAcceptance P.toTRParams (ρ k) (x k) (s k) (x (k + 1)) (Δ k) (Δ (k + 1))
  /-- The radius cap of (13.1.17). -/
  le_Δmax : ¬ acc k → Δ (k + 1) ≤ P.Δmax
  /-- The accuracies are kept on trial iterations. -/
  h_trial : ¬ acc k → h (k + 1) = h k
  /-- No new derivative estimates at an unchanged iterate. -/
  D_unsucc : ¬ acc k → ρ k < P.η₁ → D (k + 1) = D k
  /-- Step 5 keeps the iterate. -/
  x_acc : acc k → x (k + 1) = x k
  /-- Step 5 keeps the radius. -/
  Δ_acc : acc k → Δ (k + 1) = Δ k
  /-- Step 5 (13.1.18). -/
  h_acc : acc k → ∀ i, h (k + 1) i = P.γh * h k i

namespace TRqDAStep

variable (hs : TRqDAStep X P ε x Δ h D dd jk s acc ρ k)
include hs

/-- A trial iteration went through Step 2. -/
theorem step2_of_not_acc (hk : ¬ acc k) : TRqStep2 X P ε x Δ h D dd jk s acc k := by
  refine hs.step2 ?_
  by_contra hc
  push Not at hc
  exact hk (hs.acc_of_pass hc)

/-- The radius update of a trial iteration. -/
theorem update (hk : ¬ acc k) :
    TRUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ (ρ k) (Δ k) (Δ (k + 1)) :=
  (hs.accept hk).update

/-- The radius either is kept or follows the update. -/
theorem delta_succ_eq_or_update : Δ (k + 1) = Δ k ∨
    TRUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ (ρ k) (Δ k) (Δ (k + 1)) := by
  by_cases hk : acc k
  · exact Or.inl (hs.Δ_acc hk)
  · exact Or.inr (hs.update hk)

/-- The iterate is kept unless the iteration is successful. -/
theorem x_succ_eq (hk : ¬ (¬ acc k ∧ P.η₁ ≤ ρ k)) : x (k + 1) = x k := by
  by_cases ha : acc k
  · exact hs.x_acc ha
  · exact (hs.accept ha).eq_self (not_le.1 fun h' => hk ⟨ha, h'⟩)

/-- A successful iteration moves to the trial point. -/
theorem x_succ_eq_add (hk : ¬ acc k) (hρ : P.η₁ ≤ ρ k) : x (k + 1) = x k + s k :=
  (hs.accept hk).eq_add hρ

/-- The iterates stay feasible: `x_k ∈ X` implies `x_{k+1} ∈ X`. -/
theorem mem_succ (hx : x k ∈ X) : x (k + 1) ∈ X := by
  by_cases hc : ¬ acc k ∧ P.η₁ ≤ ρ k
  · rw [hs.x_succ_eq_add hc.1 hc.2]; exact (hs.step2_of_not_acc hc.1).mem
  · rw [hs.x_succ_eq hc]; exact hx

/-- One iteration only involves the data at iterations `k` and `k + 1`: the step predicate at `k`
transfers to sequences whose iterates, radii, accuracies and estimates at `k'` and `k' + 1`, and
whose displacements, order, step, flag and ratio at `k'`, are those of iterations `k` and `k + 1`
(used to splice runs). -/
theorem congr {x' : ℕ → ℝⁿ} {Δ' : ℕ → ℝ} {h' : ℕ → ℕ → ℝ}
    {D' : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd' : ℕ → ℕ → ℝⁿ} {jk' : ℕ → ℕ} {s' : ℕ → ℝⁿ}
    {acc' : ℕ → Prop} {ρ' : ℕ → ℝ} {k' : ℕ} (hx : x' k' = x k) (hx1 : x' (k' + 1) = x (k + 1))
    (hΔ : Δ' k' = Δ k) (hΔ1 : Δ' (k' + 1) = Δ (k + 1)) (hh : h' k' = h k)
    (hh1 : h' (k' + 1) = h (k + 1)) (hD : D' k' = D k) (hD1 : D' (k' + 1) = D (k + 1))
    (hdd : dd' k' = dd k) (hjk : jk' k' = jk k) (hs' : s' k' = s k) (hacc : acc' k' ↔ acc k)
    (hρ : ρ' k' = ρ k) :
    TRqDAStep X P ε x' Δ' h' D' dd' jk' s' acc' ρ' k' := by
  obtain ⟨hw, hap, hst, hac, hle, hht, hdu, hxa, hΔa, hha⟩ := hs
  have hF : ∀ j, trFail P ε D' Δ' dd' k' j ↔ trFail P ε D Δ dd k j := fun j => by
    simp only [trFail, trRadius, hD, hΔ, hdd]
  refine ⟨fun j hj => ?_, fun hp => hacc.2 (hap fun j hj hf => hp j hj ((hF j).2 hf)),
    fun ⟨j, hj, hf⟩ => ?_, fun ha => ?_, fun ha => ?_, fun ha => ?_, fun ha hr => ?_,
    fun ha => ?_, fun ha => ?_, fun ha => ?_⟩
  · simpa only [trRadius, hD, hΔ, hx, hdd] using hw j hj
  · obtain ⟨hjm, hfl, hpl, hmem, hnl, hdl, hai⟩ := hst ⟨j, hj, (hF j).1 hf⟩
    refine ⟨hjk ▸ hjm, (hF _).2 (hjk ▸ hfl), fun i hi hlt hfi => hpl i hi (hjk ▸ hlt)
      ((hF i).1 hfi), by rw [hx, hs']; exact hmem, by rw [hs', hΔ]; exact hnl,
      by rw [hD, hjk, hdd, hs']; exact hdl, by rw [hacc, hs', hh]; exact hai⟩
  · rw [hρ, hx, hs', hx1, hΔ, hΔ1]; exact hac (fun h => ha (hacc.2 h))
  · rw [hΔ1]; exact hle (fun h => ha (hacc.2 h))
  · rw [hh1, hh]; exact hht (fun h => ha (hacc.2 h))
  · rw [hD1, hD]; exact hdu (fun h => ha (hacc.2 h)) (hρ ▸ hr)
  · rw [hx1, hx]; exact hxa (hacc.1 ha)
  · rw [hΔ1, hΔ]; exact hΔa (hacc.1 ha)
  · rw [hh1, hh]; exact hha (hacc.1 ha)

end TRqDAStep

/-- The iterates of TRqIDA/TRqEDA sequences starting in `X` stay in `X`. -/
theorem trq_mem (hstep : ∀ i < k, TRqDAStep X P ε x Δ h D dd jk s acc ρ i) (hx0 : x 0 ∈ X) :
    x k ∈ X := by
  induction k with
  | zero => exact hx0
  | succ k ih => exact (hstep k k.lt_succ_self).mem_succ (ih fun i hi => hstep i (by omega))

/-- The radii of TRqIDA/TRqEDA sequences stay positive. -/
theorem trq_delta_pos (hstep : ∀ i < k, TRqDAStep X P ε x Δ h D dd jk s acc ρ i)
    (hΔ0 : Δ 0 = P.Δ₀) : 0 < Δ k := by
  induction k with
  | zero => rw [hΔ0]; exact P.Δ₀_pos
  | succ k ih =>
    have hΔ := ih fun i hi => hstep i (hi.trans k.lt_succ_self)
    have hk := hstep k k.lt_succ_self
    by_cases ha : acc k
    · rw [hk.Δ_acc ha]; exact hΔ
    · exact (hk.accept ha).pos hΔ

/-- **Invariants of TRqIDA/TRqEDA sequences**: if the step predicate holds at every iteration
`i < k`, `Δ_0 = Δ₀` and `h_0 = h₀`, then `0 < Δ_k ≤ Δ_max` and `0 < h_{k,i} ≤ κ_h` for
`i ∈ [1, q]`. -/
theorem trq_invariants (hstep : ∀ i < k, TRqDAStep X P ε x Δ h D dd jk s acc ρ i)
    (hΔ0 : Δ 0 = P.Δ₀) (hh0 : h 0 = P.h₀) :
    (0 < Δ k ∧ Δ k ≤ P.Δmax) ∧ ∀ i ∈ Finset.Icc 1 P.q, 0 < h k i ∧ h k i ≤ P.κh := by
  induction k with
  | zero =>
    rw [hΔ0, hh0]
    exact ⟨⟨P.Δ₀_pos, P.Δ₀_le_Δmax⟩, fun i hi => ⟨P.h₀_pos i hi, P.h₀_le i hi⟩⟩
  | succ k ih =>
    obtain ⟨⟨hΔ, hΔm⟩, hh⟩ := ih fun i hi => hstep i (hi.trans k.lt_succ_self)
    have hk := hstep k k.lt_succ_self
    by_cases ha : acc k
    · refine ⟨⟨by rw [hk.Δ_acc ha]; exact hΔ, by rw [hk.Δ_acc ha]; exact hΔm⟩, fun i hi => ?_⟩
      rw [hk.h_acc ha i]
      obtain ⟨h1, h2⟩ := hh i hi
      exact ⟨mul_pos P.γh_pos h1, (mul_le_of_le_one_left h1.le P.γh_lt_one.le).trans h2⟩
    · exact ⟨⟨(hk.accept ha).pos hΔ, hk.le_Δmax ha⟩, by rw [hk.h_trial ha]; exact hh⟩

/-- The optimality radius lies in `(0, 1]`. -/
theorem trRadius_mem (hΔ : 0 < Δ k) : 0 < trRadius P Δ k ∧ trRadius P Δ k ≤ 1 :=
  ⟨lt_min hΔ P.ϑ_pos, (min_le_right _ _).trans P.ϑ_le_one⟩

/-! ### Lemma 13.1.1 -/

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
        |Real.log (Δmin / P.Δ₀)| / |Real.log P.γ₂| := by
  have h := card_successSet_or_le_of_upper_ratio (Δ := Δ) (k := k)
    (succ := fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) (fail := fun i => ¬ acc i ∧ ρ i < P.η₁)
    P.γ₂_pos P.γ₂_lt_one P.one_le_γ₃
    (fun i _ hi hf => not_le.2 hf.2 hi.2)
    (fun i hi hs => (((hstep i hi).update hs.1).le_mul_of_le hs.2 P.γ₂_lt_one P.one_le_γ₃))
    (fun i hi hf => ((hstep i hi).update hf.1).le_mul_of_lt hf.2)
    (fun i hi hs hf => by
      have ha : acc i := by
        by_contra ha
        rcases le_or_gt P.η₁ (ρ i) with hρ | hρ
        · exact hs ⟨ha, hρ⟩
        · exact hf ⟨ha, hρ⟩
      rw [(hstep i hi).Δ_acc ha])
    hmin hΔmin
  rw [hΔ0] at h
  have hset : successSet (fun i => (¬ acc i ∧ P.η₁ ≤ ρ i) ∨ (¬ acc i ∧ ρ i < P.η₁)) k =
      successSet (fun i => ¬ acc i) k := by
    ext i
    simp only [mem_successSet]
    constructor
    · rintro ⟨hi, (h1 | h1)⟩ <;> exact ⟨hi, h1.1⟩
    · rintro ⟨hi, h1⟩
      exact ⟨hi, (le_or_gt P.η₁ (ρ i)).imp (fun h2 => ⟨h1, h2⟩) fun h2 => ⟨h1, h2⟩⟩
  rwa [hset] at h

/-! ### Lemma 13.1.2 -/

/-- **Lemma 13.1.2** ([cartis2022evaluation]): at a trial iteration `k ∈ 𝒯` of TRqIDA (or
TRqEDA) with `Δ_k > 0`, the scaled criticality `φ̂_{f,k}` of (13.1.25) satisfies
`φ̂_{f,k} ≥ ½ ς ε_min` (hence (13.1.26), `min_{i ∈ 𝒯_k} φ̂_{f,i} ≥ ½ ς ε_min`) and (13.1.27),
`\overline{ΔT}_{f,j_k}(x_k, s_k) ≥ φ̂_{f,k} δ_k^{j_k} / j_k!`. -/
theorem lemma_13_1_2 (hs : TRqDAStep X P ε x Δ h D dd jk s acc ρ k) (hk : ¬ acc k)
    (hΔ : 0 < Δ k) :
    P.ς * epsMin P.q ε / 2 ≤ phiHat (D k) (jk k) (trRadius P Δ k) (dd k (jk k)) ∧
      phiHat (D k) (jk k) (trRadius P Δ k) (dd k (jk k)) * trRadius P Δ k ^ jk k / (jk k)! ≤
        (D k).taylorDecrement (jk k) (s k) := by
  have h2 := hs.step2_of_not_acc hk
  have hδ := (trRadius_mem (P := P) hΔ).1
  set δ := trRadius P Δ k
  set j := jk k
  have hf : (0 : ℝ) < (j ! : ℝ) := by positivity
  have hδj : 0 < δ ^ j := pow_pos hδ j
  have heq : phiHat (D k) j δ (dd k j) * δ ^ j / j ! = (D k).taylorDecrement j (dd k j) := by
    rw [phiHat]; field_simp
  refine ⟨?_, heq ▸ h2.dec_le⟩
  have hfail := h2.fail
  unfold trFail at hfail
  rw [phiHat, le_div_iff₀ hδj]
  have hεj := epsMin_le (ε := ε) h2.jk_mem
  have : P.ς * epsMin P.q ε / 2 * δ ^ j ≤ P.ς * ε j * δ ^ j / 2 := by
    have := P.ς_pos.le
    have : P.ς * epsMin P.q ε ≤ P.ς * ε j := mul_le_mul_of_nonneg_left hεj this
    nlinarith
  calc P.ς * epsMin P.q ε / 2 * δ ^ j ≤ P.ς * ε j * δ ^ j / 2 := this
    _ = j ! * (P.ς * ε j * δ ^ j / j ! / 2) := by field_simp
    _ ≤ j ! * (D k).taylorDecrement j (dd k j) := by gcongr

/-- The predicted decrease `\overline{ΔT}_{f,j_k}(x_k, s_k)` of a trial iteration of TRqIDA (or
TRqEDA) with `Δ_k > 0` and `ε_min > 0` is positive (Lemma 13.1.2). -/
theorem TRqDAStep.taylorDecrement_pos (hs : TRqDAStep X P ε x Δ h D dd jk s acc ρ k)
    (hk : ¬ acc k) (hΔ : 0 < Δ k) (hε : 0 < epsMin P.q ε) :
    0 < (D k).taylorDecrement (jk k) (s k) := by
  obtain ⟨hφ, hdec⟩ := lemma_13_1_2 hs hk hΔ
  have hδ := (trRadius_mem (P := P) hΔ).1
  have h0 : 0 < P.ς * epsMin P.q ε / 2 := by have := P.ς_pos; positivity
  exact lt_of_lt_of_le (div_pos (mul_pos (h0.trans_le hφ) (pow_pos hδ _)) (by positivity)) hdec

/-- The scaled criticality `φ̂_{f,i}` (13.1.25) of iteration `i`. -/
noncomputable abbrev trPhiHat (P : TRqIDAParams) (Δ : ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (i : ℕ) : ℝ :=
  phiHat (D i) (jk i) (trRadius P Δ i) (dd i (jk i))

/-- **The radius bound behind Lemma 13.1.4** ([cartis2022evaluation], Appendix B), for sequences
satisfying the TRqIDA step predicate at every iteration `i < k` with `Δ_0 = Δ₀`. Suppose that a
trial iteration `i` with `Δ_i ≤ min(ϑ, a φ̂_{f,i})` is very successful (Lemmas 13.1.3, 13.3.1),
and let `0 ≤ κ_Δ ≤ γ₁ a`. Then for every lower bound `c` of the `φ̂_{f,i}`, `i ∈ 𝒯_{k-1}`,
`Δ_k ≥ min(γ₁ ϑ, κ_Δ c)`. -/
theorem trq_delta_ge (hstep : ∀ i < k, TRqDAStep X P ε x Δ h D dd jk s acc ρ i)
    (hΔ0 : Δ 0 = P.Δ₀) {a κΔ c : ℝ} (ha : 0 ≤ a) (hκΔ0 : 0 ≤ κΔ) (hκΔ : κΔ ≤ P.γ₁ * a)
    (hsucc : ∀ i < k, ¬ acc i → Δ i ≤ min P.ϑ (a * trPhiHat P Δ D dd jk i) → P.η₂ ≤ ρ i)
    (hc : ∀ i < k, ¬ acc i → c ≤ trPhiHat P Δ D dd jk i) :
    min (P.γ₁ * P.ϑ) (κΔ * c) ≤ Δ k := by
  induction k with
  | zero =>
    rw [hΔ0]
    exact (min_le_left _ _).trans ((mul_le_of_le_one_left P.ϑ_pos.le P.γ₁_le_one).trans
      P.ϑ_le_Δ₀)
  | succ k ih =>
    have hlt : ∀ i < k, i < k + 1 := fun i hi => hi.trans k.lt_succ_self
    have IH := ih (fun i hi => hstep i (hlt i hi)) (fun i hi => hsucc i (hlt i hi))
      (fun i hi => hc i (hlt i hi))
    have hk := hstep k k.lt_succ_self
    have hΔpos := trq_delta_pos (fun i hi => hstep i (hlt i hi)) hΔ0
    by_cases hacc : acc k
    · rw [hk.Δ_acc hacc]; exact IH
    have hu := hk.update hacc
    by_cases hsmall : Δ k ≤ min P.ϑ (a * trPhiHat P Δ D dd jk k)
    · exact IH.trans (hu.le_of_very_successful (hsucc k k.lt_succ_self hacc hsmall))
    have hγ : P.γ₁ * Δ k ≤ Δ (k + 1) := hu.mul_le P.γ₁_le_γ₂ P.γ₁_le_one hΔpos.le
    rcases le_or_gt c 0 with hc0 | hc0
    · exact (min_le_right _ _).trans ((mul_nonpos_of_nonneg_of_nonpos hκΔ0 hc0).trans
        (hu.pos P.γ₁_pos P.γ₁_le_γ₂ P.γ₁_le_one hΔpos).le)
    rw [not_le, min_lt_iff] at hsmall
    refine le_trans ?_ hγ
    rcases hsmall with hϑ | hφ
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hϑ.le P.γ₁_pos.le)
    · have h1 : a * c ≤ a * trPhiHat P Δ D dd jk k :=
        mul_le_mul_of_nonneg_left (hc k k.lt_succ_self hacc) ha
      calc min (P.γ₁ * P.ϑ) (κΔ * c) ≤ κΔ * c := min_le_right _ _
        _ ≤ P.γ₁ * a * c := mul_le_mul_of_nonneg_right hκΔ hc0.le
        _ = P.γ₁ * (a * c) := by ring
        _ ≤ P.γ₁ * Δ k := mul_le_mul_of_nonneg_left (h1.trans hφ.le) P.γ₁_pos.le

/-- **The decrement bound behind Lemma 13.1.5** ([cartis2022evaluation], Appendix B), for one
trial iteration of the TRqIDA step predicate: if `0 < ε_min ≤ 1`, `0 ≤ κ_δ ≤ ½` and
`δ_k ≥ ς κ_δ ε_min` ((13.1.32)), then
`\overline{ΔT}_{f,j_k}(x_k, s_k) ≥ (ς κ_δ)^{q+1}/q! ε_min^{q+1}` ((13.1.34)). -/
theorem TRqDAStep.taylorDecrement_ge (hs : TRqDAStep X P ε x Δ h D dd jk s acc ρ k)
    (hk : ¬ acc k) (hΔ : 0 < Δ k) {κδ : ℝ} (hκδ0 : 0 ≤ κδ) (hκδ : κδ ≤ 1 / 2)
    (hεmin : 0 < epsMin P.q ε) (hεmin1 : epsMin P.q ε ≤ 1)
    (hδ : P.ς * κδ * epsMin P.q ε ≤ trRadius P Δ k) :
    (P.ς * κδ) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1) ≤
      (D k).taylorDecrement (jk k) (s k) := by
  obtain ⟨hφ, hdec⟩ := lemma_13_1_2 hs hk hΔ
  have h2 := hs.step2_of_not_acc hk
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 h2.jk_mem
  set m := P.ς * κδ * epsMin P.q ε with hm
  set ph := trPhiHat P Δ D dd jk k
  set δ := trRadius P Δ k
  set j := jk k
  have hm0 : 0 ≤ m := by have := P.ς_pos.le; positivity
  have hm1 : m ≤ 1 := by
    have : P.ς * κδ ≤ 1 := by
      have := P.ς_le_one; have := P.ς_pos.le; nlinarith
    calc m = P.ς * κδ * epsMin P.q ε := rfl
      _ ≤ 1 * 1 := mul_le_mul this hεmin1 hεmin.le zero_le_one
      _ = 1 := one_mul 1
  have hmφ : m ≤ ph := by
    refine le_trans ?_ hφ
    have := P.ς_pos.le
    have : P.ς * epsMin P.q ε * κδ ≤ P.ς * epsMin P.q ε * (1 / 2) :=
      mul_le_mul_of_nonneg_left hκδ (by positivity)
    rw [hm]; linarith
  have hδj : m ^ P.q ≤ δ ^ j :=
    (pow_le_pow_of_le_one hm0 hm1 hjq).trans (pow_le_pow_left₀ hm0 hδ j)
  have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
  have hjpos : (0 : ℝ) < j ! := by positivity
  calc (P.ς * κδ) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1) = m * m ^ P.q / P.q ! := by
        rw [hm, mul_pow, pow_succ']; ring
    _ ≤ ph * δ ^ j / P.q ! :=
        div_le_div_of_nonneg_right (mul_le_mul hmφ hδj (by positivity) (hm0.trans hmφ))
          (by positivity)
    _ ≤ ph * δ ^ j / j ! :=
        div_le_div_of_nonneg_left (mul_nonneg (hm0.trans hmφ) (pow_nonneg (hm0.trans hδ) _))
          hjpos hfact
    _ ≤ (D k).taylorDecrement j (s k) := hdec

/-- **The accuracy bound behind Lemma 13.1.6** ([cartis2022evaluation]), for one iteration of the
TRqIDA step predicate that goes through Step 2: if `‖∇̄^i f(x_k)‖ ≤ L̄` for `i ∈ [1, q]` with
`L̄ ≥ 1`, `ε ∈ (0, 1]^q`, `0 ≤ κ_δ ≤ 1`, `δ_k ≥ ς κ_δ ε_min` and (13.1.36)
`h_{k,i} ≤ κ_s (ς^{q+1} κ_δ^q/(4 q! L̄))^q ε_min^{q(q+1)}` for `i ∈ [1, q]`, then the accuracy test
(13.1.9) holds, i.e. the iteration is not accuracy-improving. -/
theorem TRqStep2.not_acc_of_le (h2 : TRqStep2 X P ε x Δ h D dd jk s acc k) (hΔ : 0 < Δ k)
    {Lb κδ : ℝ} (hLb : 1 ≤ Lb) (hD : ∀ i ∈ Finset.Icc 1 P.q, ‖D k i‖ ≤ Lb)
    (hκδ0 : 0 ≤ κδ) (hκδ : κδ ≤ 1) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hδ : P.ς * κδ * epsMin P.q ε ≤ trRadius P Δ k)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤
      P.κs * (P.ς ^ (P.q + 1) * κδ ^ P.q / (4 * P.q ! * Lb)) ^ P.q *
        epsMin P.q ε ^ (P.q * (P.q + 1))) :
    ¬ acc k := by
  have hq := P.one_le_q
  have hεmin : 0 < epsMin P.q ε := epsMin_pos hq fun j hj => (hε j hj).1
  have hεmin1 : epsMin P.q ε ≤ 1 := epsMin_le_one hq fun j hj => (hε j hj).2
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 h2.jk_mem
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  set j := jk k
  set em := epsMin P.q ε
  set c := P.ς ^ (P.q + 1) * κδ ^ P.q / (4 * P.q ! * Lb) * em ^ (P.q + 1) with hc
  have hfq : (0 : ℝ) < P.q ! := by positivity
  have hLb0 : 0 < Lb := zero_lt_one.trans_le hLb
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by
    have h1 : P.ς ^ (P.q + 1) ≤ 1 := pow_le_one₀ hς.le hς1
    have h2 : κδ ^ P.q ≤ 1 := pow_le_one₀ hκδ0 hκδ
    have h3 : em ^ (P.q + 1) ≤ 1 := pow_le_one₀ hεmin.le hεmin1
    have h4 : (1 : ℝ) ≤ 4 * P.q ! * Lb := by
      have : (1 : ℝ) ≤ P.q ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
      nlinarith
    rw [hc, div_mul_eq_mul_div, div_le_one (by positivity)]
    calc P.ς ^ (P.q + 1) * κδ ^ P.q * em ^ (P.q + 1) ≤ 1 * 1 * 1 := by gcongr
      _ ≤ 4 * P.q ! * Lb := by linarith
  -- the step is not too short
  have hsc : c ≤ ‖s k‖ ∨ 1 ≤ ‖s k‖ := by
    rcases le_or_gt 1 ‖s k‖ with h1 | h1
    · exact Or.inr h1
    left
    have hfail := h2.fail
    unfold trFail at hfail
    have hup := taylorDecrement_le_two_mul (D := D k) (j := j) hLb0.le
      (fun i hi => hD i (Finset.Icc_subset_Icc le_rfl hjq hi)) h1.le
    have hlow := hfail.trans_le (h2.dec_le.trans hup)
    have hδ0 := (trRadius_mem (P := P) hΔ).1
    set δ := trRadius P Δ k
    have hm0 : 0 ≤ P.ς * κδ * em := by positivity
    have hm1 : P.ς * κδ * em ≤ 1 := by
      calc P.ς * κδ * em ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by ring
    have hδj : (P.ς * κδ * em) ^ P.q ≤ δ ^ j :=
      (pow_le_pow_of_le_one hm0 hm1 hjq).trans (pow_le_pow_left₀ hm0 hδ j)
    have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
    have hjpos : (0 : ℝ) < j ! := by positivity
    have hεj : em ≤ ε j := epsMin_le h2.jk_mem
    have key : P.ς * em * (P.ς * κδ * em) ^ P.q / (4 * P.q ! * Lb) ≤
        P.ς * ε j * δ ^ j / j ! / 2 / (2 * Lb) := by
      have hnum : P.ς * em * (P.ς * κδ * em) ^ P.q ≤ P.ς * ε j * δ ^ j :=
        mul_le_mul (mul_le_mul_of_nonneg_left hεj hς.le) hδj (by positivity)
          (mul_nonneg hς.le (hεmin.le.trans hεj))
      have hN : 0 ≤ P.ς * ε j * δ ^ j :=
        mul_nonneg (mul_nonneg hς.le (hεmin.le.trans hεj)) (pow_nonneg hδ0.le _)
      calc P.ς * em * (P.ς * κδ * em) ^ P.q / (4 * P.q ! * Lb)
          ≤ P.ς * ε j * δ ^ j / (4 * P.q ! * Lb) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ P.ς * ε j * δ ^ j / (4 * j ! * Lb) :=
            div_le_div_of_nonneg_left hN (by positivity) (by gcongr)
        _ = P.ς * ε j * δ ^ j / j ! / 2 / (2 * Lb) := by field_simp; ring
    have : c = P.ς * em * (P.ς * κδ * em) ^ P.q / (4 * P.q ! * Lb) := by
      rw [hc]; ring
    rw [this]
    refine key.trans ?_
    rw [div_le_iff₀ (by positivity)]
    linarith
  rw [h2.acc_iff]
  push Not
  intro i hi
  obtain ⟨hi1, hiq⟩ := Finset.mem_Icc.1 hi
  have hcq : c ^ P.q ≤ ‖s k‖ ^ (P.q - i + 1) := by
    rcases hsc with hsc | hsc
    · exact (pow_le_pow_of_le_one hc0 hc1 (by omega)).trans (pow_le_pow_left₀ hc0 hsc _)
    · exact (pow_le_one₀ hc0 hc1).trans (one_le_pow₀ hsc)
  calc h k i ≤ P.κs * (P.ς ^ (P.q + 1) * κδ ^ P.q / (4 * P.q ! * Lb)) ^ P.q *
        em ^ (P.q * (P.q + 1)) := hh i hi
    _ = P.κs * c ^ P.q := by rw [hc, mul_pow, ← pow_mul, mul_comm (P.q + 1) P.q, mul_assoc]
    _ ≤ P.κs * ‖s k‖ ^ (P.q - i + 1) := mul_le_mul_of_nonneg_left hcq P.κs_pos.le

end TRStep

/-! ### TRqIDA runs -/

/-- `{e | y + e ∈ univ} = univ`. -/
theorem setOf_add_mem_univ (y : ℝⁿ) : {e : ℝⁿ | y + e ∈ (univ : Set ℝⁿ)} = univ := by
  ext; simp

/-- The test of approximate optimality of TRqIDA at iteration `k` (not observable by the method,
[cartis2022evaluation], (12.1.25)): `x_k` is an `(ε, δ_k)`-approximate `q`-th order minimizer
with the radius `δ_k = min(Δ_k, ϑ)` at all orders. -/
def trTest (f : ℝⁿ → ℝ) (P : TRqIDAParams) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (k : ℕ) :
    Prop :=
  IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε (fun _ => trRadius P Δ k)

/-- The test of approximate optimality of TRqIDA-SC at iteration `k` ([cartis2022evaluation],
§14.2, (14.2.2)): `x_k` is an `(ε, δ_k)`-approximate `q`-th order minimizer of `f` on the
feasible set `X` (measures over the feasible displacements `{e | x_k + e ∈ X}`) with the radius
`δ_k = min(Δ_k, ϑ)`. With `X = univ` this is `trTest` (`trTest_feasible_univ`). -/
def trTest_feasible (f : ℝⁿ → ℝ) (X : Set ℝⁿ) (P : TRqIDAParams) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ)
    (Δ : ℕ → ℝ) (k : ℕ) : Prop :=
  IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε (fun _ => trRadius P Δ k)

theorem trTest_feasible_univ {f : ℝⁿ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x : ℕ → ℝⁿ}
    {Δ : ℕ → ℝ} : trTest_feasible f univ P ε x Δ = trTest f P ε x Δ := by
  funext k; simp only [trTest_feasible, trTest, setOf_add_mem_univ]

/-- **Algorithm 13.1.1 with a feasible set** (TRqIDA-SC, [cartis2022evaluation] §14.2) as a run
predicate, for the objective `f`, the closed feasible set `X` (closedness is not used by the
analysis), the (unknown) oracle constants `κ_{∇,i}` (`κg i ≥ 0`), constants `P`, tolerances
`ε ∈ (0, 1]^q` with `ε_min ≤ ϑ`, a feasible starting point `x₀ ∈ X`, and sequences of iterates `x`,
radii `Δ`, requested accuracies `h`, inexact jets `D` satisfying (13.1.2), Step-1 displacements
`dd`, orders `j_k`, steps `s` and accuracy-improving flags `acc`; every iteration satisfies
`TRqDAStep` on `X` (feasible Step-1 displacements and trial points) with the exact-value ratio
(13.1.16) `ρ_k = (f(x_k) - f(x_k + s_k)) / \overline{ΔT}_{f,j_k}(x_k, s_k)`
(`Optimization.trqRatio`). With `X = univ` this is `algorithm_13_1_1`. -/
structure algorithm_13_1_1_feasible (f : ℝⁿ → ℝ) (X : Set ℝⁿ) (κg : ℕ → ℝ) (P : TRqIDAParams)
    (ε : ℕ → ℝ) (x₀ : ℝⁿ) (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
    (acc : ℕ → Prop) : Prop where
  /-- `ε ∈ (0, 1]^q`. -/
  eps_mem : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1
  /-- `ϑ ≥ ε_min`. -/
  epsMin_le_ϑ : epsMin P.q ε ≤ P.ϑ
  /-- `κ_{∇,i} ≥ 0`. -/
  κg_nonneg : ∀ i ∈ Finset.Icc 1 P.q, 0 ≤ κg i
  /-- The starting point. -/
  x_zero : x 0 = x₀
  /-- The starting point is feasible. -/
  x₀_mem : x₀ ∈ X
  /-- The initial radius. -/
  Δ_zero : Δ 0 = P.Δ₀
  /-- The initial accuracies. -/
  h_zero : h 0 = P.h₀
  /-- The error model (13.1.2). -/
  oracle : ∀ k, JetApprox (ftaylorSeries ℝ f (x k)) (D k) P.q (fun i => κg i * h k i)
  /-- Steps 1–5. -/
  step : ∀ k, TRqDAStep X P ε x Δ h D dd jk s acc (trqRatio f D x s jk) k

/-- **Algorithm 13.1.1** (TRqIDA) of [cartis2022evaluation] as a run predicate, for the objective
`f`, the (unknown) oracle constants `κ_{∇,i}` (`κg i ≥ 0`), constants `P`, tolerances
`ε ∈ (0, 1]^q` with `ε_min ≤ ϑ`, starting point `x₀`, and sequences of iterates `x`, radii `Δ`,
requested accuracies `h`, inexact jets `D` satisfying (13.1.2), Step-1 displacements `dd`,
orders `j_k`, steps `s` and accuracy-improving flags `acc`; every iteration satisfies
`TRqDAStep` with the exact-value ratio (13.1.16) `ρ_k = (f(x_k) - f(x_k + s_k)) /
\overline{ΔT}_{f,j_k}(x_k, s_k)` (`Optimization.trqRatio`). The method has no termination rule;
see `trTest`. This is `algorithm_13_1_1_feasible` with the feasible set `X = univ`. -/
abbrev algorithm_13_1_1 (f : ℝⁿ → ℝ) (κg : ℕ → ℝ) (P : TRqIDAParams) (ε : ℕ → ℝ)
    (x₀ : ℝⁿ) (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
    (acc : ℕ → Prop) : Prop :=
  algorithm_13_1_1_feasible f univ κg P ε x₀ x Δ h D dd jk s acc

namespace algorithm_13_1_1_feasible

variable {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {κg : ℕ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop}
  (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc)
include hrun

theorem delta_pos (k : ℕ) : 0 < Δ k :=
  trq_delta_pos (fun i _ => hrun.step i) hrun.Δ_zero

theorem h_mem (k : ℕ) {i : ℕ} (hi : i ∈ Finset.Icc 1 P.q) : 0 < h k i ∧ h k i ≤ P.κh :=
  (trq_invariants (k := k) (fun i _ => hrun.step i) hrun.Δ_zero hrun.h_zero).2 i hi

theorem epsMin_pos : 0 < epsMin P.q ε :=
  Chapter13.epsMin_pos P.one_le_q fun j hj => (hrun.eps_mem j hj).1

theorem epsMin_le_one : epsMin P.q ε ≤ 1 :=
  Chapter13.epsMin_le_one P.one_le_q fun j hj => (hrun.eps_mem j hj).2

theorem kappaMax_nonneg : 0 ≤ ordMax P.q κg := ordMax_nonneg hrun.κg_nonneg

/-- The iterates are feasible. -/
theorem mem (k : ℕ) : x k ∈ X :=
  trq_mem (fun i _ => hrun.step i) (hrun.x_zero ▸ hrun.x₀_mem)

/-- The objective does not increase along a TRqIDA-SC run: `f(x_k) ≤ f(x₀)` (the ratio uses
exact function values and the predicted decrease of a trial iteration is positive). -/
theorem f_le (k : ℕ) : f (x k) ≤ f x₀ := by
  rw [← hrun.x_zero]
  refine le_zero_of_succ_le (u := fun i => f (x i)) fun i _ => ?_
  by_cases ha : acc i
  · simp only [(hrun.step i).x_acc ha, le_rfl]
  · exact ((hrun.step i).accept ha).le (f := f) trqRatio_eq
      ((hrun.step i).taylorDecrement_pos ha (hrun.delta_pos i) hrun.epsMin_pos)

/-- The iterates lie in every set `A` containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}`. -/
theorem mem_anchor {A : Set ℝⁿ} (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) (k : ℕ) : x k ∈ A :=
  hAX _ (hrun.mem k) (hrun.f_le k)

/-- (13.1.24): `‖∇̄^i f(x_k)‖ ≤ L̄_f = L_f + κ_{∇,max} κ_h` under f.D0qL anchored on a set `A`
containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}`. -/
theorem norm_D_le_anchored {C A : Set ℝⁿ} {L : ℕ → ℝ} (hf : AssumptionD0qLAnchored f C A P.q L)
    (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) (k : ℕ) {i : ℕ} (hi : i ∈ Finset.Icc 1 P.q) :
    ‖D k i‖ ≤ lipMax L P.q + ordMax P.q κg * P.κh :=
  hf.norm_le_of_jetApprox (hrun.mem_anchor hAX k) (hrun.oracle k) hrun.κg_nonneg
    (fun _ hi => (hrun.h_mem k hi).1.le) (fun _ hi => (hrun.h_mem k hi).2) hi

/-- (13.1.24): `‖∇̄^i f(x_k)‖ ≤ L̄_f = L_f + κ_{∇,max} κ_h` under f.D0qL on `C ⊇ X`. -/
theorem norm_D_le {C : Set ℝⁿ} {L : ℕ → ℝ} (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (k : ℕ) {i : ℕ} (hi : i ∈ Finset.Icc 1 P.q) :
    ‖D k i‖ ≤ lipMax L P.q + ordMax P.q κg * P.κh :=
  hrun.norm_D_le_anchored (hf.anchored hXC) (fun _ hy _ => hy) k hi

end algorithm_13_1_1_feasible

section TRqIDA

variable {X C A : Set ℝⁿ} {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {Δ : ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {L : ℕ → ℝ} {k : ℕ}

/-! ### Lemma 13.1.3 -/

/-- **Lemma 13.1.3 under the anchored assumption** ([cartis2022evaluation] §14.2): the conclusion of
`lemma_13_1_3` for a TRqIDA-SC run (`algorithm_13_1_1_feasible`) under f.D0qL anchored on a set `A`
containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}` (`AssumptionD0qLAnchored`). -/
theorem lemma_13_1_3_anchored (hf : AssumptionD0qLAnchored f C A P.q L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc) (hk : ¬ acc k)
    (hΔ : Δ k ≤ min P.ϑ ((1 - P.η₂) /
      (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg) * trPhiHat P Δ D dd jk k)) :
    P.η₂ ≤ trqRatio f D x s jk k ∧ Δ k ≤ Δ (k + 1) := by
  have hs := hrun.step k
  have h2 := hs.step2_of_not_acc hk
  have hΔpos := hrun.delta_pos k
  obtain ⟨hφ, hdec⟩ := lemma_13_1_2 hs hk hΔpos
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 h2.jk_mem
  have hδeq : trRadius P Δ k = Δ k := min_eq_left (hΔ.trans (min_le_left _ _))
  set j := jk k
  set δ := trRadius P Δ k
  set ph := trPhiHat P Δ D dd jk k
  set Lf := lipMax L P.q
  set κm := ordMax P.q κg
  set C := Lf + 4 * (P.q + 1)! * P.κs * κm
  have hLf : 1 ≤ Lf := hf.one_le_lipMax
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  have hκs := P.κs_pos
  have hC : 0 < C := by positivity
  have hδ0 : 0 < δ := (trRadius_mem (P := P) hΔpos).1
  have hδ1 : δ ≤ 1 := (trRadius_mem (P := P) hΔpos).2
  have hφ0 : 0 < ph := lt_of_lt_of_le (by have := P.ς_pos; have := hrun.epsMin_pos; positivity) hφ
  have hfj : (0 : ℝ) < j ! := by positivity
  set ΔTb := (D k).taylorDecrement j (s k)
  have hΔTb : ph * δ ^ j / j ! ≤ ΔTb := hdec
  have hΔTb0 : 0 < ΔTb := lt_of_lt_of_le (by positivity) hΔTb
  have hsδ : ‖s k‖ ≤ δ := hδeq ▸ h2.norm_le
  -- the step accuracy (13.1.9) holds on a trial iteration
  have hacc : ∀ i ∈ Finset.Icc 1 P.q, κg i * h k i ≤ κm * P.κs * ‖s k‖ ^ (P.q - i + 1) := by
    intro i hi
    have hhi : h k i ≤ P.κs * ‖s k‖ ^ (P.q - i + 1) := by
      by_contra hc
      exact hk (h2.acc_iff.2 ⟨i, hi, not_le.1 hc⟩)
    rw [mul_assoc]
    exact mul_le_mul (le_ordMax hi) hhi (hrun.h_mem k hi).1.le hκm
  have hE := abs_taylorDecrement_sub_le_of_stepAccuracy hκm hκs.le (hrun.oracle k) hacc hjq
  have hR := hf.abs_sub_le hjq (hrun.mem_anchor hAX k) (hXC h2.mem)
  have hLj : L j ≤ Lf := le_lipMax hjq
  -- bounds by `δ^{j+1}`
  have hs0 := norm_nonneg (s k)
  have hpow1 : ‖s k‖ ^ (j + 1) ≤ δ ^ (j + 1) := pow_le_pow_left₀ hs0 hsδ _
  have hpow2 : ‖s k‖ ^ (P.q + 1) ≤ δ ^ (j + 1) :=
    (pow_le_pow_of_le_one hs0 (hsδ.trans hδ1) (by omega)).trans hpow1
  have hfact1 : ((j + 1)! : ℝ) ≥ j ! := by exact_mod_cast Nat.factorial_le (Nat.le_succ j)
  have hfact2 : (2 : ℝ) * j ! ≤ 4 * (P.q + 1)! := by
    have : (j ! : ℝ) ≤ (P.q + 1)! := by exact_mod_cast Nat.factorial_le (by omega)
    linarith
  have hδC : δ * C ≤ (1 - P.η₂) * ph := by
    have := hΔ.trans (min_le_right _ _)
    rw [← hδeq] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ hC] at this
    linarith
  have herr : |f (x k) - f (x k)| + |f (x k + s k) - (f (x k) -
      (ftaylorSeries ℝ f (x k)).taylorDecrement j (s k))| +
      |(ftaylorSeries ℝ f (x k)).taylorDecrement j (s k) - ΔTb| +
      |f (x k + s k) - f (x k + s k)| ≤ (1 - P.η₂) * ΔTb := by
    rw [sub_self, sub_self, abs_zero, zero_add, add_zero]
    have hRb : L j / ((j + 1)! : ℝ) * ‖s k‖ ^ (j + 1) ≤ Lf / j ! * δ ^ (j + 1) := by
      gcongr
    have hEb : 2 * P.κs * κm * ‖s k‖ ^ (P.q + 1) ≤
        4 * (P.q + 1)! * P.κs * κm / j ! * δ ^ (j + 1) := by
      have : 2 * P.κs * κm ≤ 4 * (P.q + 1)! * P.κs * κm / j ! := by
        rw [le_div_iff₀ hfj]
        have := mul_le_mul_of_nonneg_right hfact2 (mul_nonneg hκs.le hκm)
        linarith
      exact mul_le_mul this hpow2 (by positivity) (by positivity)
    calc |f (x k + s k) - (f (x k) - (ftaylorSeries ℝ f (x k)).taylorDecrement j (s k))| +
          |(ftaylorSeries ℝ f (x k)).taylorDecrement j (s k) - ΔTb|
        ≤ L j / ((j + 1)! : ℝ) * ‖s k‖ ^ (j + 1) + 2 * P.κs * κm * ‖s k‖ ^ (P.q + 1) :=
          add_le_add hR (by rw [abs_sub_comm]; exact hE)
      _ ≤ Lf / j ! * δ ^ (j + 1) + 4 * (P.q + 1)! * P.κs * κm / j ! * δ ^ (j + 1) :=
          add_le_add hRb hEb
      _ = δ ^ j / j ! * (δ * C) := by rw [pow_succ]; ring
      _ ≤ δ ^ j / j ! * ((1 - P.η₂) * ph) := by gcongr
      _ = (1 - P.η₂) * (ph * δ ^ j / j !) := by ring
      _ ≤ (1 - P.η₂) * ΔTb := mul_le_mul_of_nonneg_left hΔTb P.one_sub_η₂_pos.le
  have hρ : P.η₂ ≤ trqRatio f D x s jk k := by
    rw [trqRatio_eq, reductionRatio_def]
    exact le_div_of_inexact_error_le hΔTb0 herr
  exact ⟨hρ, (hs.update hk).le_of_very_successful hρ⟩

/-- **Lemma 13.1.3 with a feasible set** ([cartis2022evaluation] §14.2): the conclusion of
`lemma_13_1_3` for a TRqIDA-SC run (`algorithm_13_1_1_feasible`) under f.D0qL on an open
convex `C ⊇ X`. -/
theorem lemma_13_1_3_feasible (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc) (hk : ¬ acc k)
    (hΔ : Δ k ≤ min P.ϑ ((1 - P.η₂) /
      (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg) * trPhiHat P Δ D dd jk k)) :
    P.η₂ ≤ trqRatio f D x s jk k ∧ Δ k ≤ Δ (k + 1) :=
  lemma_13_1_3_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hrun hk hΔ

/-- **Lemma 13.1.3** ([cartis2022evaluation]): under f.D0qL, at a trial iteration `k ∈ 𝒯` of
TRqIDA with (13.1.28) `Δ_k ≤ min(ϑ, (1 - η₂)/(L_f + 4 (q+1)! κ_s κ_{∇,max}) pĥ_{f,k})`, the
iteration is very successful (`ρ_k ≥ η₂`) and `Δ_{k+1} ≥ Δ_k`. -/
theorem lemma_13_1_3 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) (hk : ¬ acc k)
    (hΔ : Δ k ≤ min P.ϑ ((1 - P.η₂) /
      (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg) * trPhiHat P Δ D dd jk k)) :
    P.η₂ ≤ trqRatio f D x s jk k ∧ Δ k ≤ Δ (k + 1) :=
  lemma_13_1_3_feasible hf.on_univ (subset_univ _) hrun hk hΔ

/-! ### Lemma 13.1.4 -/

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
    Chapter13.epsMin_pos P.one_le_q fun j _ => pow_pos hδ₀ j
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
  · exact mul_le_one_of_le_one (min_le_left _ _) hB0.le hB1
  · rw [← mul_div_assoc]
    exact (mul_le_of_le_one_right hA0.le hB1).trans (min_le_right _ _)

/-- **Lemma 13.1.4 under the anchored assumption** ([cartis2022evaluation] §14.2): the radius bounds
of `lemma_13_1_4` for a TRqIDA-SC run under f.D0qL anchored on a set `A` containing the sublevel set
`{y ∈ X | f(y) ≤ f(x₀)}` (`AssumptionD0qLAnchored`). -/
theorem lemma_13_1_4_anchored (hf : AssumptionD0qLAnchored f C A P.q L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ} (hκΔ0 : 0 < κΔ)
    (hκΔ1 : κΔ ≤ 1)
    (hκΔ : κΔ ≤ P.γ₁ * ((1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg)))
    (k : ℕ) :
    (∀ hne : (successSet (fun i => ¬ acc i) k).Nonempty, min (P.γ₁ * P.ϑ)
        (κΔ * (successSet (fun i => ¬ acc i) k).inf' hne (trPhiHat P Δ D dd jk)) ≤ Δ k) ∧
      (successSet (fun i => ¬ acc i) k = ∅ → P.γ₁ * P.ϑ ≤ Δ k) ∧
      P.ς * (κΔ / 2) * epsMin P.q ε ≤ trRadius P Δ k := by
  set a := (1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg) with ha_def
  have hLf := hf.one_le_lipMax
  have hκm := hrun.kappaMax_nonneg
  have hC : 1 ≤ lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg := by
    have := P.κs_pos; nlinarith [show (0 : ℝ) ≤ 4 * (P.q + 1)! * P.κs * ordMax P.q κg by
      positivity]
  have ha0 : 0 ≤ a := div_nonneg P.one_sub_η₂_pos.le (zero_le_one.trans hC)
  have ha1 : a ≤ 1 := by
    rw [ha_def, div_le_one (zero_lt_one.trans_le hC)]
    linarith [P.η₂_pos]
  have hsucc : ∀ i < k, ¬ acc i → Δ i ≤ min P.ϑ (a * trPhiHat P Δ D dd jk i) →
      P.η₂ ≤ trqRatio f D x s jk i :=
    fun i _ hi hΔ => (lemma_13_1_3_anchored hf hXC hAX hrun hi hΔ).1
  have core := fun c (hc : ∀ i < k, ¬ acc i → c ≤ trPhiHat P Δ D dd jk i) =>
    trq_delta_ge (fun i _ => hrun.step i) hrun.Δ_zero ha0 hκΔ0.le hκΔ hsucc hc
  refine ⟨fun hne => core _ fun i hi hai => Finset.inf'_le _
      (mem_successSet.2 ⟨hi.le, hai⟩), fun hempty => ?_, ?_⟩
  · have := core (P.γ₁ * P.ϑ / κΔ) fun i hi hai => by
      have : i ∈ successSet (fun i => ¬ acc i) k := mem_successSet.2 ⟨hi.le, hai⟩
      rw [hempty] at this
      exact absurd this (Finset.notMem_empty i)
    rwa [mul_div_cancel₀ _ hκΔ0.ne', min_self] at this
  · have hεmin := hrun.epsMin_pos
    have hc := core (P.ς * epsMin P.q ε / 2) fun i _ hai =>
      (lemma_13_1_2 (hrun.step i) hai (hrun.delta_pos i)).1
    have hκγ : κΔ ≤ P.γ₁ := hκΔ.trans (mul_le_of_le_one_right P.γ₁_pos.le ha1)
    have hς := P.ς_pos
    have hς1 := P.ς_le_one
    have h1 : P.ς * (κΔ / 2) * epsMin P.q ε ≤ epsMin P.q ε := by
      have : P.ς * (κΔ / 2) ≤ 1 := by nlinarith
      nlinarith
    refine le_min (le_trans ?_ hc) (h1.trans hrun.epsMin_le_ϑ)
    refine le_min ?_ (le_of_eq (by ring))
    calc P.ς * (κΔ / 2) * epsMin P.q ε ≤ P.γ₁ * epsMin P.q ε := by
          have : P.ς * (κΔ / 2) ≤ P.γ₁ := by nlinarith
          exact mul_le_mul_of_nonneg_right this hεmin.le
      _ ≤ P.γ₁ * P.ϑ := mul_le_mul_of_nonneg_left hrun.epsMin_le_ϑ P.γ₁_pos.le

/-- **Lemma 13.1.4 with a feasible set** ([cartis2022evaluation] §14.2): the radius bounds of
`lemma_13_1_4` for a TRqIDA-SC run under f.D0qL on an open convex `C ⊇ X`. -/
theorem lemma_13_1_4_feasible (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ} (hκΔ0 : 0 < κΔ)
    (hκΔ1 : κΔ ≤ 1)
    (hκΔ : κΔ ≤ P.γ₁ * ((1 - P.η₂) / (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg)))
    (k : ℕ) :
    (∀ hne : (successSet (fun i => ¬ acc i) k).Nonempty, min (P.γ₁ * P.ϑ)
        (κΔ * (successSet (fun i => ¬ acc i) k).inf' hne (trPhiHat P Δ D dd jk)) ≤ Δ k) ∧
      (successSet (fun i => ¬ acc i) k = ∅ → P.γ₁ * P.ϑ ≤ Δ k) ∧
      P.ς * (κΔ / 2) * epsMin P.q ε ≤ trRadius P Δ k :=
  lemma_13_1_4_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hrun hκΔ0 hκΔ1 hκΔ k

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
      P.ς * (κΔ / 2) * epsMin P.q ε ≤ trRadius P Δ k :=
  lemma_13_1_4_feasible hf.on_univ (subset_univ _) hrun hκΔ0 hκΔ1 hκΔ k

/-- The admissible values of `κ_Δ` in Lemmas 13.1.4–13.1.7 and Theorem 13.1.8:
`0 < κ_Δ ≤ 1` and `κ_Δ ≤ γ₁ (1 - η₂)/(L_f + 4(q+1)! κ_s κ_{∇,max})`. -/
def IsTRKappaDelta (P : TRqIDAParams) (Lf κm κΔ : ℝ) : Prop :=
  0 < κΔ ∧ κΔ ≤ 1 ∧ κΔ ≤ P.γ₁ * ((1 - P.η₂) / (Lf + 4 * (P.q + 1)! * P.κs * κm))

/-! ### Lemma 13.1.5 -/

/-- **Lemma 13.1.5 under the anchored assumption** ([cartis2022evaluation] §14.2): for a TRqIDA-SC
run under f.D0qL anchored on a set `A` containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}`
(`AssumptionD0qLAnchored`) and an admissible `κ_Δ`, every trial iteration satisfies (13.1.34) and
every successful one (13.1.35), as in `lemma_13_1_5`. -/
theorem lemma_13_1_5_anchored (hf : AssumptionD0qLAnchored f C A P.q L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) (hk : ¬ acc k) :
    (P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1) ≤
        (D k).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ trqRatio f D x s jk k →
        P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
          f (x k) - f (x (k + 1))) := by
  obtain ⟨hκΔ0, hκΔ1, hκΔ⟩ := hκΔ
  have h1 := (hrun.step k).taylorDecrement_ge hk (hrun.delta_pos k) (by positivity)
    (by linarith) hrun.epsMin_pos hrun.epsMin_le_one
    (lemma_13_1_4_anchored hf hXC hAX hrun hκΔ0 hκΔ1 hκΔ k).2.2
  refine ⟨h1, fun hρ => ?_⟩
  have hpos : 0 < (D k).taylorDecrement (jk k) (s k) :=
    lt_of_lt_of_le (by have := P.ς_pos; have := hrun.epsMin_pos; positivity) h1
  have h2 := ((hrun.step k).accept hk).sub_ge (f := f) trqRatio_eq hpos hρ
  have hη := P.η₁_pos
  have : 0 ≤ (P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1) := by
    have := P.ς_pos; have := hrun.epsMin_pos; positivity
  calc P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1)
      = P.η₁ * ((P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1)) / 2 := by
        field_simp
    _ ≤ P.η₁ * ((P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1)) := by
        have := mul_nonneg hη.le this; linarith
    _ ≤ P.η₁ * (D k).taylorDecrement (jk k) (s k) := mul_le_mul_of_nonneg_left h1 hη.le
    _ ≤ f (x k) - f (x (k + 1)) := h2

/-- **Lemma 13.1.5 with a feasible set** ([cartis2022evaluation] §14.2): for a TRqIDA-SC run under
f.D0qL on an open convex `C ⊇ X` and an admissible `κ_Δ`, every trial iteration satisfies (13.1.34)
and every successful one (13.1.35), as in `lemma_13_1_5`. -/
theorem lemma_13_1_5_feasible (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) (hk : ¬ acc k) :
    (P.ς * (κΔ / 2)) ^ (P.q + 1) / P.q ! * epsMin P.q ε ^ (P.q + 1) ≤
        (D k).taylorDecrement (jk k) (s k) ∧
      (P.η₁ ≤ trqRatio f D x s jk k →
        P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * epsMin P.q ε ^ (P.q + 1) ≤
          f (x k) - f (x (k + 1))) :=
  lemma_13_1_5_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hrun hκΔ hk

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
  lemma_13_1_5_feasible hf.on_univ (subset_univ _) hrun hκΔ hk

/-! ### Lemmas 13.1.6 and 13.1.7 -/

/-- **Lemma 13.1.6 under the anchored assumption** ([cartis2022evaluation] §14.2): the conclusion of
`lemma_13_1_6` for a TRqIDA-SC run under f.D0qL anchored on a set `A` containing the sublevel set
`{y ∈ X | f(y) ≤ f(x₀)}` (`AssumptionD0qLAnchored`). -/
theorem lemma_13_1_6_anchored (hf : AssumptionD0qLAnchored f C A P.q L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ)
    (hb : ∃ j ∈ Finset.Icc 1 P.q, trFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤ P.κs * (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q /
      (4 * P.q ! * (lipMax L P.q + ordMax P.q κg * P.κh))) ^ P.q *
        epsMin P.q ε ^ (P.q * (P.q + 1))) :
    ¬ acc k := by
  obtain ⟨hκΔ0, hκΔ1, hκΔ'⟩ := hκΔ
  have hLb : 1 ≤ lipMax L P.q + ordMax P.q κg * P.κh := by
    have := hf.one_le_lipMax; have := hrun.kappaMax_nonneg; have := P.κh_pos; nlinarith
  exact ((hrun.step k).step2 hb).not_acc_of_le (hrun.delta_pos k) hLb
    (fun i hi => hrun.norm_D_le_anchored hf hAX k hi) (by positivity) (by linarith) hrun.eps_mem
    (lemma_13_1_4_anchored hf hXC hAX hrun hκΔ0 hκΔ1 hκΔ' k).2.2 hh

/-- **Lemma 13.1.6 with a feasible set** ([cartis2022evaluation] §14.2): the conclusion of
`lemma_13_1_6` for a TRqIDA-SC run under f.D0qL on an open convex `C ⊇ X`. -/
theorem lemma_13_1_6_feasible (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ)
    (hb : ∃ j ∈ Finset.Icc 1 P.q, trFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤ P.κs * (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q /
      (4 * P.q ! * (lipMax L P.q + ordMax P.q κg * P.κh))) ^ P.q *
        epsMin P.q ε ^ (P.q * (P.q + 1))) :
    ¬ acc k :=
  lemma_13_1_6_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hrun hκΔ hb hh

/-- **Lemma 13.1.6** ([cartis2022evaluation]): under f.D0qL, with `L̄_f = L_f + κ_{∇,max} κ_h`
((13.1.24)) and an admissible `κ_Δ`, `κ_δ = κ_Δ/2`: if Step 1 of TRqIDA branches to Step 2 at
iteration `k` and (13.1.36) `h_{k,i} ≤ κ_s (ς^{q+1} κ_δ^q/(4 q! L̄_f))^q ε_min^{q(q+1)}` for all
`i ∈ [1, q]`, then Step 2 does not branch to Step 5 (`k ∈ 𝒯`). (The book uses `L̄_f`, defined only
in (13.1.63), for the bound (13.1.24).) -/
theorem lemma_13_1_6 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ)
    (hb : ∃ j ∈ Finset.Icc 1 P.q, trFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, h k i ≤ P.κs * (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q /
      (4 * P.q ! * (lipMax L P.q + ordMax P.q κg * P.κh))) ^ P.q *
        epsMin P.q ε ^ (P.q * (P.q + 1))) :
    ¬ acc k :=
  lemma_13_1_6_feasible hf.on_univ (subset_univ _) hrun hκΔ hb hh

/-- **Lemma 13.1.7 under the anchored assumption** ([cartis2022evaluation] §14.2): for a TRqIDA-SC
run under f.D0qL anchored on a set `A` containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}`
(`AssumptionD0qLAnchored`), if Step 1 branches to Step 5 at iteration `k` and (13.1.37) holds, then
`x_k` is an `(ε, δ_k)`-approximate minimizer on `X` (`trTest_feasible`). -/
theorem lemma_13_1_7_anchored (hf : AssumptionD0qLAnchored f C A P.q L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, ¬ trFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, ordMax P.q κg * h k i ≤
      P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    trTest_feasible f X P ε x Δ k := by
  obtain ⟨hκΔ0, hκΔ1, hκΔ'⟩ := hκΔ
  have hδm := (lemma_13_1_4_anchored hf hXC hAX hrun hκΔ0 hκΔ1 hκΔ' k).2.2
  have hδ := trRadius_mem (P := P) (hrun.delta_pos k)
  have hεmin := hrun.epsMin_pos
  have hεmin1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  intro j hj
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  set δ := trRadius P Δ k
  set em := epsMin P.q ε
  set m := P.ς * (κΔ / 2) * em
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ 1 := by
    have : P.ς * (κΔ / 2) ≤ 1 := by nlinarith
    calc m ≤ 1 * 1 := mul_le_mul this hεmin1 hεmin.le zero_le_one
      _ = 1 := one_mul 1
  have hw := ((hrun.step k).witness j hj).2
  refine taylorMeasure_le_of_inexact_certificate_uniform (hrun.oracle k) hj
    (by simpa using hrun.mem k) hδ.1.le
    hδ.2 hς hw (not_lt.1 (hpass j hj))
    (e := P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * em ^ (P.q + 1))
    (fun i hi => ?_) ?_
  · have hiq : i ∈ Finset.Icc 1 P.q := Finset.Icc_subset_Icc le_rfl hjq hi
    exact (mul_le_mul_of_nonneg_right (le_ordMax hiq) (hrun.h_mem k hiq).1.le).trans (hh i hiq)
  · have hδj : m ^ P.q ≤ δ ^ j :=
      (pow_le_pow_of_le_one hm0 hm1 hjq).trans (pow_le_pow_left₀ hm0 hδm j)
    have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
    have hεj : P.ς * em ≤ ε j := (mul_le_of_le_one_left hεmin.le hς1).trans (epsMin_le hj)
    calc P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * em ^ (P.q + 1) =
          P.ς * em * m ^ P.q / (4 * P.q !) := by simp only [m]; ring
      _ ≤ ε j * δ ^ j / (4 * P.q !) :=
          div_le_div_of_nonneg_right (mul_le_mul hεj hδj (pow_nonneg hm0 _)
            (hrun.eps_mem j hj).1.le) (by positivity)
      _ ≤ ε j * δ ^ j / (4 * j !) := by
          gcongr
          exact mul_nonneg ((by positivity : (0 : ℝ) ≤ P.ς * em).trans hεj)
            (pow_nonneg hδ.1.le _)

/-- **Lemma 13.1.7 with a feasible set** ([cartis2022evaluation] §14.2): for a TRqIDA-SC run under
f.D0qL on an open convex `C ⊇ X`, if Step 1 branches to Step 5 at iteration `k` and (13.1.37) holds,
then `x_k` is an `(ε, δ_k)`-approximate minimizer on `X` (`trTest_feasible`). -/
theorem lemma_13_1_7_feasible (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, ¬ trFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, ordMax P.q κg * h k i ≤
      P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    trTest_feasible f X P ε x Δ k :=
  lemma_13_1_7_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hrun hκΔ hpass hh

/-- **Lemma 13.1.7** ([cartis2022evaluation]): under f.D0qL and for an admissible `κ_Δ`,
`κ_δ = κ_Δ/2`: if Step 1 of TRqIDA branches to Step 5 at iteration `k` ((13.1.14) fails at every
order) and (13.1.37) `κ_{∇,max} h_{k,i} ≤ ς^{q+1} κ_δ^q/(4 q!) ε_min^{q+1}` for `i ∈ [1, q]`
(written without division, so that `κ_{∇,max} = 0` is allowed), then
`φ^{δ_k}_{f,j}(x_k) ≤ ε_j δ_k^j/j!` for all `j ∈ [1, q]`. -/
theorem lemma_13_1_7 (hf : AssumptionD0qL f P.q L)
    (hrun : algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, ¬ trFail P ε D Δ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.q, ordMax P.q κg * h k i ≤
      P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * epsMin P.q ε ^ (P.q + 1)) :
    trTest f P ε x Δ k := by
  have := lemma_13_1_7_feasible hf.on_univ (subset_univ _) hrun hκΔ hpass hh
  rwa [trTest_feasible_univ] at this

/-! ### Theorem 13.1.8 -/

/-- The constant `κ^S_{TRqIDA} = 2 q!/(η₁ (ς κ_δ)^{q+1})` (13.1.40), with `κ_δ = κ_Δ/2`. -/
noncomputable def trKappaS (P : TRqIDAParams) (κΔ : ℝ) : ℝ :=
  2 * P.q ! / (P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1))

/-- The constant `κ_acc` of the proof of Theorem 13.1.8 ([cartis2022evaluation]):
`min(ς^{q+1} κ_δ^q/(4 q! κ_{∇,max}), κ_s (ς^{q+1} κ_δ^q/(4 q! L̄_f))^q)`, the first term being
omitted when `κ_{∇,max} = 0` (exact derivatives). -/
noncomputable def trKappaAcc (P : TRqIDAParams) (κΔ Lb κm : ℝ) : ℝ :=
  if κm = 0 then P.κs * (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q ! * Lb)) ^ P.q
  else min (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q ! * κm))
    (P.κs * (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q ! * Lb)) ^ P.q)

theorem trKappaAcc_pos {P : TRqIDAParams} {κΔ Lb κm : ℝ} (hκΔ : 0 < κΔ) (hLb : 0 < Lb)
    (hκm : 0 ≤ κm) : 0 < trKappaAcc P κΔ Lb κm := by
  have := P.ς_pos; have := P.κs_pos
  unfold trKappaAcc
  split_ifs with h0
  · positivity
  · exact lt_min (by have := lt_of_le_of_ne hκm (Ne.symm h0); positivity) (by positivity)

theorem trKappaAcc_le {P : TRqIDAParams} {κΔ Lb κm : ℝ} :
    trKappaAcc P κΔ Lb κm ≤
      P.κs * (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q ! * Lb)) ^ P.q := by
  unfold trKappaAcc
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

theorem mul_trKappaAcc_le {P : TRqIDAParams} {κΔ Lb κm : ℝ} (hκΔ : 0 < κΔ) (hκm : 0 ≤ κm) :
    κm * trKappaAcc P κΔ Lb κm ≤ P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) := by
  have := P.ς_pos
  unfold trKappaAcc
  split_ifs with h0
  · rw [h0, zero_mul]; positivity
  · have hκm' : 0 < κm := lt_of_le_of_ne hκm (Ne.symm h0)
    calc κm * min (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q ! * κm)) _
        ≤ κm * (P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q ! * κm)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hκm
      _ = P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) := by field_simp

/-- **The accuracy-improving iterations of TRqIDA-SC** (proof of Theorem 13.1.8,
[cartis2022evaluation]): under f.D0qL anchored on a set `A` containing the sublevel set
`{y ∈ X | f(y) ≤ f(x₀)}` (`AssumptionD0qLAnchored`) and for an admissible `κ_Δ`, if no iterate
`x_j`, `j ≤ k`, is approximately optimal on `X`, then
`|𝒜_k| ≤ q(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. -/
theorem trqIDA_card_acc_le_anchored (hf : AssumptionD0qLAnchored f C A P.q L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ trTest_feasible f X P ε x Δ j) :
    ((successSet acc k).card : ℝ) ≤
      P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
        |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
          P.κh)| / |Real.log P.γh| + 1 := by
  have hκΔ'' := hκΔ
  have hκΔ0 := hκΔ.1
  have hq := P.one_le_q
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  set Lf := lipMax L P.q
  set κm := ordMax P.q κg
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  set Lb := Lf + κm * P.κh
  have hLb : 0 < Lb := by have := hf.one_le_lipMax; have := P.κh_pos; nlinarith
  set κacc := trKappaAcc P κΔ Lb κm
  have hκacc : 0 < κacc := trKappaAcc_pos hκΔ0 hLb hκm
  have hlogh : 0 < |Real.log P.γh| := abs_pos.2 (Real.log_neg P.γh_pos P.γh_lt_one).ne
  set NA := P.q * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hpowq : em ^ (P.q * (P.q + 1)) ≤ em ^ (P.q + 1) :=
    pow_le_pow_of_le_one hεmin.le hεmin1 (by nlinarith)
  have h := card_accuracyImproving_le_of_pow (acc := acc) (hmax := fun j => ordMax P.q (h j))
    (N := P.q * (P.q + 1)) (k := k) P.γh_pos P.γh_lt_one P.κh_pos hκacc hεmin
    ((ordMax_le_iff hq).2 fun i hi => by rw [hrun.h_zero]; exact P.h₀_le i hi)
    (fun j _ ha => by
      rw [show h (j + 1) = fun i => P.γh * h j i from funext ((hrun.step j).h_acc ha),
        ordMax_mul hq P.γh_pos.le])
    (fun j _ ha => by rw [(hrun.step j).h_trial ha])
    (fun j hj ha => by
      by_contra hcon
      push Not at hcon
      have hhi : ∀ i ∈ Finset.Icc 1 P.q, h j i ≤ κacc * em ^ (P.q * (P.q + 1)) :=
        fun i hi => (le_ordMax hi).trans hcon
      by_cases hfail : ∃ i ∈ Finset.Icc 1 P.q, trFail P ε D Δ dd j i
      · refine lemma_13_1_6_anchored hf hXC hAX hrun hκΔ'' hfail
          (fun i hi => (hhi i hi).trans ?_) ha
        exact mul_le_mul_of_nonneg_right trKappaAcc_le (by positivity)
      · push Not at hfail
        refine hk j hj (lemma_13_1_7_anchored hf hXC hAX hrun hκΔ'' hfail fun i hi => ?_)
        calc κm * h j i ≤ κm * (κacc * em ^ (P.q * (P.q + 1))) :=
              mul_le_mul_of_nonneg_left (hhi i hi) hκm
          _ = κm * κacc * em ^ (P.q * (P.q + 1)) := by ring
          _ ≤ P.ς ^ (P.q + 1) * (κΔ / 2) ^ P.q / (4 * P.q !) * em ^ (P.q + 1) :=
              mul_le_mul (mul_trKappaAcc_le hκΔ0 hκm) hpowq (by positivity) (by positivity))
  calc ((successSet acc k).card : ℝ)
      ≤ (((P.q * (P.q + 1) : ℕ) : ℝ) * |Real.log em| + |Real.log (κacc / P.κh)|) /
          |Real.log P.γh| + 1 := h
    _ = NA := by rw [hNA_def]; push_cast; ring

/-- **The accuracy-improving iterations of TRqIDA-SC** (proof of Theorem 13.1.8,
[cartis2022evaluation]): under f.D0qL on an open convex `C ⊇ X` and for an admissible `κ_Δ`, if
no iterate `x_j`, `j ≤ k`, is approximately optimal on `X`, then
`|𝒜_k| ≤ q(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1`. -/
theorem trqIDA_card_acc_le_feasible (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ trTest_feasible f X P ε x Δ j) :
    ((successSet acc k).card : ℝ) ≤
      P.q * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
        |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
          P.κh)| / |Real.log P.γh| + 1 :=
  trqIDA_card_acc_le_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hrun hκΔ hk

/-- **Theorem 13.1.8 under the anchored assumption** ([cartis2022evaluation] §14.2): complexity of
TRqIDA-SC (the TRqIDA-SC row of Theorem 14.2.4). Under f.D0qL anchored on a set `A` containing the
sublevel set `{y ∈ X | f(y) ≤ f(x₀)}` (`AssumptionD0qLAnchored`) and f.bB.X (`f ≥ f_low` on `X`),
every TRqIDA-SC run has a first iterate `x_{k_ε}` that is an `(ε, δ_ε)`-approximate minimizer on `X`
(`trTest_feasible`), before which at most the numbers of evaluations of `theorem_13_1_8` are made.
-/
theorem theorem_13_1_8_anchored (hf : AssumptionD0qLAnchored f C A P.q L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) :
    ∃ kε, IsFirstHit (trTest_feasible f X P ε x Δ) kε ∧ 0 < trRadius P Δ kε ∧ trRadius P Δ kε ≤ 1 ∧
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
  have hκΔ'' := hκΔ
  obtain ⟨hκΔ0, hκΔ1, hκΔ'⟩ := hκΔ
  have hq := P.one_le_q
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  have hη := P.η₁_pos
  set Lf := lipMax L P.q
  set κm := ordMax P.q κg
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  set Lb := Lf + κm * P.κh
  have hLb : 0 < Lb := by have := hf.one_le_lipMax; have := P.κh_pos; nlinarith
  have hf0 : 0 ≤ f x₀ - flow := sub_nonneg.2 (hb x₀ hrun.x₀_mem)
  -- successful iterations
  set c := P.η₁ * (P.ς * (κΔ / 2)) ^ (P.q + 1) / (2 * P.q !) * em ^ (P.q + 1) with hc_def
  have hc : 0 < c := by positivity
  set NS := trKappaS P κΔ * (f x₀ - flow) / em ^ (P.q + 1) with hNS_def
  have hNS : NS = (f x₀ - flow) / c := by
    rw [hNS_def, hc_def, trKappaS, eq_div_iff (by positivity)]
    field_simp
  have hNS0 : 0 ≤ NS := by rw [hNS]; positivity
  have hSk : ∀ k, ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i) k).card : ℝ)
      ≤ NS := by
    intro k
    rw [hNS, ← hrun.x_zero]
    exact card_successSet_le_div_of_decrease («φ» := fun i => f (x i)) hc
      (fun j _ hj => by rw [(hrun.step j).x_succ_eq hj])
      (fun j _ hj => (lemma_13_1_5_anchored hf hXC hAX hrun hκΔ'' hj.1).2 hj.2) (hb _ (hrun.mem _))
  -- trial iterations
  have hlog2 : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
  set A' := 1 + Real.log P.γ₃ / |Real.log P.γ₂| with hA'
  have hA'1 : 1 ≤ A' := by
    have := Real.log_nonneg P.one_le_γ₃; rw [hA']; have := div_nonneg this hlog2.le; linarith
  set NT := trKappaS P κΔ * A' * (f x₀ - flow) / em ^ (P.q + 1) +
    1 / |Real.log P.γ₂| * |Real.log em| + |Real.log (P.ς * (κΔ / 2) / P.Δ₀)| /
      |Real.log P.γ₂| with hNT_def
  have hNT0 : 0 ≤ NT := by
    have : 0 ≤ trKappaS P κΔ := by unfold trKappaS; positivity
    positivity
  have hTk : ∀ k, ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤ NT := by
    intro k
    have hΔmin : P.ς * (κΔ / 2) * em ≤ Δ (k + 1) :=
      (lemma_13_1_4_anchored hf hXC hAX hrun hκΔ0 hκΔ1 hκΔ' (k + 1)).2.2.trans (min_le_left _ _)
    have h1 := lemma_13_1_1 (fun i _ => hrun.step i) hrun.Δ_zero (by positivity) hΔmin
    have hlog : |Real.log (P.ς * (κΔ / 2) * em / P.Δ₀)| ≤
        |Real.log em| + |Real.log (P.ς * (κΔ / 2) / P.Δ₀)| := by
      have hpos : 0 < P.ς * (κΔ / 2) / P.Δ₀ := by have := P.Δ₀_pos; positivity
      rw [show P.ς * (κΔ / 2) * em / P.Δ₀ = em * (P.ς * (κΔ / 2) / P.Δ₀) by ring,
        Real.log_mul hεmin.ne' hpos.ne']
      exact abs_add_le _ _
    have h2 := mul_le_mul_of_nonneg_right (hSk k) (zero_le_one.trans hA'1)
    calc ((successSet (fun i => ¬ acc i) k).card : ℝ)
        ≤ _ := h1
      _ ≤ NS * A' + (|Real.log em| + |Real.log (P.ς * (κΔ / 2) / P.Δ₀)|) /
            |Real.log P.γ₂| := add_le_add h2 (div_le_div_of_nonneg_right hlog hlog2.le)
      _ = NT := by rw [hNT_def, hNS_def]; ring
  -- accuracy-improving iterations
  set κacc := trKappaAcc P κΔ Lb κm
  set NA := P.q * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hAk : ∀ k, (∀ j ≤ k, ¬ trTest_feasible f X P ε x Δ j) →
      ((successSet acc k).card : ℝ) ≤ NA :=
    fun k hk => trqIDA_card_acc_le_anchored hf hXC hAX hrun hκΔ'' hk
  -- conclusion
  obtain ⟨kε, hkε, -, hT, hA⟩ :=
    exists_firstHit_le_of_dynamicAccuracy hNT0 hNA0 (fun k _ => hTk k) hAk
  have hS := derivEvalCount_le_of_isFirstHit hNS0 hkε (fun k _ => hSk k)
  have hor : (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i)) kε :
      ℝ) + 1 ≤ derivEvalCount acc kε +
        derivEvalCount (fun i => ¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i) kε := by
    exact_mod_cast derivEvalCount_or_add_one_le _ _ kε
  have hNSA : NS ≤ trKappaS P κΔ * A' * (f x₀ - flow) / em ^ (P.q + 1) := by
    have : trKappaS P κΔ * A' * (f x₀ - flow) / em ^ (P.q + 1) = A' * NS := by
      rw [hNS_def]; ring
    rw [this]
    exact le_mul_of_one_le_left hNS0 hA'1
  refine ⟨kε, hkε, (trRadius_mem (hrun.delta_pos kε)).1, (trRadius_mem (hrun.delta_pos kε)).2,
    ?_, ?_⟩
  · calc (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤ NT + 1 := hT
      _ = _ := by rw [hNT_def]; ring
  · calc _ ≤ (NA + 1) + (NS + 1) - 1 := by linarith
      _ ≤ trKappaS P κΔ * A' * (f x₀ - flow) / em ^ (P.q + 1) + NA + 1 := by linarith
      _ = _ := by rw [hNA_def]; ring

/-- **Theorem 13.1.8 with a feasible set** ([cartis2022evaluation] §14.2): complexity of TRqIDA-SC
(the TRqIDA-SC row of Theorem 14.2.4). Under f.D0qL on an open convex `C ⊇ X` and f.bB.X
(`f ≥ f_low` on `X`), every TRqIDA-SC run has a first iterate `x_{k_ε}` that is an
`(ε, δ_ε)`-approximate minimizer on `X` (`trTest_feasible`), before which at most the numbers of
evaluations of `theorem_13_1_8` are made. -/
theorem theorem_13_1_8_feasible (hf : AssumptionD0qLOn f C P.q L) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : algorithm_13_1_1_feasible f X κg P ε x₀ x Δ h D dd jk s acc) {κΔ : ℝ}
    (hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ) :
    ∃ kε, IsFirstHit (trTest_feasible f X P ε x Δ) kε ∧ 0 < trRadius P Δ kε ∧ trRadius P Δ kε ≤ 1 ∧
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
            P.κh)| / |Real.log P.γh| + 2 :=
  theorem_13_1_8_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hb hrun hκΔ

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
    ∃ kε, IsFirstHit (trTest f P ε x Δ) kε ∧ 0 < trRadius P Δ kε ∧ trRadius P Δ kε ≤ 1 ∧
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
  have := theorem_13_1_8_feasible hf.on_univ (subset_univ _) (fun y _ => hb y) hrun hκΔ
  rwa [trTest_feasible_univ] at this

end TRqIDA

/-! ### Existence of TRqIDA runs -/

section TRExistence

/-- The data of one TRqIDA iteration: iterate, radius, accuracies, Step-1 displacements, order,
step and accuracy-improving flag. -/
private structure TRState (n : ℕ) where
  x : EuclideanSpace ℝ (Fin n)
  Δ : ℝ
  h : ℕ → ℝ
  dd : ℕ → EuclideanSpace ℝ (Fin n)
  jk : ℕ
  s : EuclideanSpace ℝ (Fin n)
  acc : Prop

variable (f : ℝⁿ → ℝ) (P : TRqIDAParams) (ε : ℕ → ℝ)
  (O : ℝⁿ → (ℕ → ℝ) → FormalMultilinearSeries ℝ ℝⁿ ℝ)

/-- The Step-1.2 test of a state. -/
private def trFailS (a : TRState n) (j : ℕ) : Prop :=
  P.ς * ε j * min a.Δ P.ϑ ^ j / j ! / 2 < (O a.x a.h).taylorDecrement j (a.dd j)

/-- Steps 1–2 of a state, and the radius invariant. -/
private def TRLocal (a : TRState n) : Prop :=
  (0 < a.Δ ∧ a.Δ ≤ P.Δmax) ∧
  (∀ j ∈ Finset.Icc 1 P.q, IsApproxMeasureStep ((O a.x a.h).taylorDecrement j) (min a.Δ P.ϑ)
    univ P.ς (a.dd j)) ∧
  ((∀ j ∈ Finset.Icc 1 P.q, ¬ trFailS P ε O a j) → a.acc) ∧
  ((∃ j ∈ Finset.Icc 1 P.q, trFailS P ε O a j) →
    a.jk ∈ Finset.Icc 1 P.q ∧ trFailS P ε O a a.jk ∧
    (∀ j ∈ Finset.Icc 1 P.q, j < a.jk → ¬ trFailS P ε O a j) ∧ ‖a.s‖ ≤ a.Δ ∧
    (O a.x a.h).taylorDecrement a.jk (a.dd a.jk) ≤ (O a.x a.h).taylorDecrement a.jk a.s ∧
    (a.acc ↔ ∃ i ∈ Finset.Icc 1 P.q, P.κs * ‖a.s‖ ^ (P.q - i + 1) < a.h i))

/-- Steps 1–2 can be performed at every iterate with a positive radius. -/
private theorem exists_trLocal (x : ℝⁿ) {Δ : ℝ} (hΔ : 0 < Δ) (hΔm : Δ ≤ P.Δmax) (h : ℕ → ℝ) :
    ∃ dd jk s, ∃ acc : Prop, TRLocal P ε O ⟨x, Δ, h, dd, jk, s, acc⟩ := by
  classical
  have hδ : 0 ≤ min Δ P.ϑ := le_min hΔ.le P.ϑ_pos.le
  choose dd hdd using fun j => exists_isApproxMeasureStep_taylorDecrement (O x h) j
    isClosed_univ (mem_univ 0) hδ P.ς_le_one
  by_cases hex : ∃ j, j ∈ Finset.Icc 1 P.q ∧
      P.ς * ε j * min Δ P.ϑ ^ j / j ! / 2 < (O x h).taylorDecrement j (dd j)
  · set jk := Nat.find hex
    obtain ⟨hjk, hfjk⟩ := Nat.find_spec hex
    refine ⟨dd, jk, dd jk, ∃ i ∈ Finset.Icc 1 P.q, P.κs * ‖dd jk‖ ^ (P.q - i + 1) < h i,
      ⟨hΔ, hΔm⟩, fun j _ => hdd j, fun hpass => absurd hfjk (hpass jk hjk), fun _ =>
      ⟨hjk, hfjk, fun j hj hlt hf => Nat.find_min hex hlt ⟨hj, hf⟩,
        (hdd jk).norm_le.trans (min_le_left _ _), le_rfl, Iff.rfl⟩⟩
  · push Not at hex
    exact ⟨dd, 1, 0, True, ⟨hΔ, hΔm⟩, fun j _ => hdd j, fun _ => trivial,
      fun ⟨j, hj, hf⟩ => absurd (hex j hj) (not_le.2 hf)⟩

/-- The transition of a TRqIDA run from a state satisfying Steps 1–2. -/
private theorem exists_trNext (a : TRState n) (ha : TRLocal P ε O a) :
    ∃ b : TRState n, TRLocal P ε O b ∧ ∀ (r : ℕ → TRState n) (k : ℕ), r k = a → r (k + 1) = b →
      TRqDAStep univ P ε (fun i => (r i).x) (fun i => (r i).Δ) (fun i => (r i).h)
        (fun i => O (r i).x (r i).h) (fun i => (r i).dd) (fun i => (r i).jk) (fun i => (r i).s)
        (fun i => (r i).acc)
        (trqRatio f (fun i => O (r i).x (r i).h) (fun i => (r i).x) (fun i => (r i).s)
          (fun i => (r i).jk)) k := by
  classical
  obtain ⟨⟨hΔ, hΔm⟩, hw, hpass, hst⟩ := ha
  set ρ := reductionRatio f a.x a.s ((O a.x a.h).taylorDecrement a.jk a.s) with hρ
  set x' := if a.acc then a.x else if P.η₁ ≤ ρ then a.x + a.s else a.x
  set Δ' := if a.acc then a.Δ else if P.η₁ ≤ ρ then a.Δ else P.γ₂ * a.Δ
  set h' : ℕ → ℝ := if a.acc then fun i => P.γh * a.h i else a.h
  have hΔ' : 0 < Δ' ∧ Δ' ≤ P.Δmax := by
    simp only [Δ']
    split_ifs
    · exact ⟨hΔ, hΔm⟩
    · exact ⟨hΔ, hΔm⟩
    · exact ⟨mul_pos P.γ₂_pos hΔ, (mul_le_of_le_one_left hΔ.le P.γ₂_lt_one.le).trans hΔm⟩
  obtain ⟨dd', jk', s', acc', hloc⟩ := exists_trLocal P ε O x' hΔ'.1 hΔ'.2 h'
  refine ⟨⟨x', Δ', h', dd', jk', s', acc'⟩, hloc, fun r k hra hrb => ?_⟩
  have hfail : ∀ j, trFail P ε (fun i => O (r i).x (r i).h) (fun i => (r i).Δ)
      (fun i => (r i).dd) k j ↔ trFailS P ε O a j := by
    intro j; simp only [trFail, trRadius, trFailS, hra]
  have hratio : trqRatio f (fun i => O (r i).x (r i).h) (fun i => (r i).x) (fun i => (r i).s)
      (fun i => (r i).jk) k = ρ := by simp only [trqRatio, hra, hρ]
  refine ⟨fun j hj => ?_, fun hp => ?_, fun he => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_,
    fun hk hlt => ?_, fun hk => ?_, fun hk => ?_, fun hk i => ?_⟩
  · simp only [trRadius, hra, setOf_add_mem_univ]; exact hw j hj
  · simp only [hra]; exact hpass fun j hj => (hfail j).not.1 (hp j hj)
  · obtain ⟨j, hj, hf⟩ := he
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst ⟨j, hj, (hfail j).1 hf⟩
    refine ⟨by simp only [hra]; exact h1, by simp only [hra] at hfail ⊢; exact (hfail _).2 h2,
      fun j hj hlt => ?_, by simp, by simp only [hra]; exact h4, by simp only [hra]; exact h5,
      by simp only [hra]; exact h6⟩
    simp only [hra] at hlt
    exact (hfail j).not.2 (h3 j hj hlt)
  · simp only [hra] at hk
    rw [hratio]
    simp only [hra, hrb, x', Δ', hk, ite_false]
    refine ⟨rfl, ?_⟩
    have hu := TRUpdate.mk (η₁ := P.η₁) (η₂ := P.η₂) (γ₁ := P.γ₁) (γ₂ := P.γ₂) (γ₃ := P.γ₃)
      (ρ := ρ) (Δ := a.Δ) (Δ' := if P.η₁ ≤ ρ then a.Δ else P.γ₂ * a.Δ)
      (fun h2 => by
        rw [ite_eq_left (P.η₁_le_η₂.trans h2)]
        exact ⟨le_rfl, le_mul_of_one_le_left hΔ.le P.one_le_γ₃⟩)
      (fun h1 _ => by
        rw [ite_eq_left h1]
        exact ⟨mul_le_of_le_one_left hΔ.le P.γ₂_lt_one.le, le_rfl⟩)
      (fun h1 => by
        rw [ite_eq_right (not_le.2 h1)]
        exact ⟨mul_le_mul_of_nonneg_right P.γ₁_le_γ₂ hΔ.le, le_rfl⟩)
    exact hu
  · simp only [hrb]; exact hΔ'.2
  · simp only [hra] at hk; simp only [hra, hrb, h', hk, ite_false]
  · simp only [hra] at hk; rw [hratio] at hlt
    simp only [hra, hrb, x', h', hk, ite_false, ite_eq_right (not_le.2 hlt)]
  · simp only [hra] at hk; simp only [hra, hrb, x', hk, ite_true]
  · simp only [hra] at hk; simp only [hra, hrb, Δ', hk, ite_true]
  · simp only [hra] at hk; simp only [hra, hrb, h', hk, ite_true]

/-- **Existence of TRqIDA iterations** ([cartis2022evaluation], Algorithm 13.1.1): for every
objective `f`, constants `P`, tolerances `ε`, starting point `x₀` and deterministic derivative
oracle `O` (inexact jet `O y h` at `y` for accuracies `h`), there are sequences following the
iteration of TRqIDA at every step, with the exact-value ratio (13.1.16) and the derivatives
`D_k = O(x_k, h_k)`. -/
theorem exists_trqDA_run (x₀ : ℝⁿ) :
    ∃ (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ)
      (s : ℕ → ℝⁿ) (acc : ℕ → Prop), x 0 = x₀ ∧ Δ 0 = P.Δ₀ ∧ h 0 = P.h₀ ∧
      ∀ k, TRqDAStep univ P ε x Δ h (fun i => O (x i) (h i)) dd jk s acc
        (trqRatio f (fun i => O (x i) (h i)) x s jk) k := by
  obtain ⟨dd₀, jk₀, s₀, acc₀, h₀⟩ :=
    exists_trLocal P ε O x₀ P.Δ₀_pos P.Δ₀_le_Δmax P.h₀
  obtain ⟨r, hr0, hr⟩ := exists_run_of_forall_exists_of_invariant (α := TRState n)
    (init := fun a => a = ⟨x₀, P.Δ₀, P.h₀, dd₀, jk₀, s₀, acc₀⟩)
    (inv := fun _ a => TRLocal P ε O a) (stop := fun _ _ => False)
    (step := fun k a b => ∀ (r : ℕ → TRState n), r k = a → r (k + 1) = b →
      TRqDAStep univ P ε (fun i => (r i).x) (fun i => (r i).Δ) (fun i => (r i).h)
        (fun i => O (r i).x (r i).h) (fun i => (r i).dd) (fun i => (r i).jk) (fun i => (r i).s)
        (fun i => (r i).acc)
        (trqRatio f (fun i => O (r i).x (r i).h) (fun i => (r i).x) (fun i => (r i).s)
          (fun i => (r i).jk)) k)
    ⟨_, rfl⟩ (fun a ha => ha ▸ h₀) (fun k a ha _ => by
      obtain ⟨b, hb, hs⟩ := exists_trNext f P ε O a ha
      exact ⟨b, hb, fun r => hs r k⟩)
  refine ⟨fun i => (r i).x, fun i => (r i).Δ, fun i => (r i).h, fun i => (r i).dd,
    fun i => (r i).jk, fun i => (r i).s, fun i => (r i).acc, by simp only [hr0],
    by simp only [hr0], by simp only [hr0], fun k => (hr k fun _ _ h => h).2 r rfl rfl⟩

end TRExistence

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
      ((trq_invariants (k := k) (fun i _ => hstep i) hΔ hh).2 i hi).1, hstep⟩, fun _ => rfl⟩

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

/-! ### ARqpIDA: constants and one iteration -/

/-- The constants of Algorithm 13.1.2 (ARqpIDA, [cartis2022evaluation], Step 0, (13.1.51)): the
ARqp constants (`σ₀ > 0`, `0 < η₁ ≤ η₂ < 1`, `0 < γ₁ < 1 < γ₂ ≤ γ₃`, `θ ∈ (0, 1)`,
`ς ∈ (0, 1]`, the last one missing from the printed Step-0 list) with `σ_min ∈ (0, σ₀]`, orders
`1 ≤ q ≤ p`, `κ_s > 0`, `κ_h ≥ 0`, `γ_h ∈ (0, 1)`, initial radii `δ₀ ∈ (0, 1]^q` and initial
accuracies `0 ≤ h_{0,i} ≤ κ_h` (`i ∈ [1, p]`). The requirement `ε_j ≤ δ_{0,j}` is part of the run
predicate. -/
structure ARqpIDAParams extends ARqpParams where
  /-- The criticality order. -/
  q : ℕ
  /-- The degree of the model. -/
  p : ℕ
  /-- The accuracy reduction factor. -/
  γh : ℝ
  /-- The constant of the accuracy test (13.1.46). -/
  κs : ℝ
  /-- The bound on the initial accuracies. -/
  κh : ℝ
  /-- The initial optimality radii. -/
  δ₀ : ℕ → ℝ
  /-- The initial requested accuracies. -/
  h₀ : ℕ → ℝ
  one_le_q : 1 ≤ q
  q_le_p : q ≤ p
  σmin_pos : 0 < σmin
  γh_pos : 0 < γh
  γh_lt_one : γh < 1
  κs_pos : 0 < κs
  κh_nonneg : 0 ≤ κh
  δ₀_mem : ∀ j ∈ Finset.Icc 1 q, δ₀ j ∈ Set.Ioc 0 1
  h₀_nonneg : ∀ i ∈ Finset.Icc 1 p, 0 ≤ h₀ i
  h₀_le : ∀ i ∈ Finset.Icc 1 p, h₀ i ≤ κh

namespace ARqpIDAParams

variable (P : ARqpIDAParams)

theorem one_le_p : 1 ≤ P.p := P.one_le_q.trans P.q_le_p

theorem one_mem_Icc : 1 ∈ Finset.Icc 1 P.q := Finset.mem_Icc.2 ⟨le_rfl, P.one_le_q⟩

theorem Icc_q_subset : Finset.Icc 1 P.q ⊆ Finset.Icc 1 P.p :=
  Finset.Icc_subset_Icc le_rfl P.q_le_p

end ARqpIDAParams

section ARStep

variable {X : Set ℝⁿ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x : ℕ → ℝⁿ} {σ : ℕ → ℝ}
  {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ} {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ}
  {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {ρ : ℕ → ℝ} {k : ℕ}

/-- The decrease `Δm̄_k(v) = m̄_k(0) - m̄_k(v)` of the regularized inexact model
`m̄_k(v) = \overline{T}_{f,p}(x_k, v) + σ_k/(p+1)! ‖v‖^{p+1}` (13.1.45). -/
noncomputable abbrev arModelDec (P : ARqpIDAParams) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (σ : ℕ → ℝ) (k : ℕ) (v : ℝⁿ) : ℝ :=
  regularizedModel (D k) P.p (σ k) 0 - regularizedModel (D k) P.p (σ k) v

/-- `Δm̄_k(v) = \overline{ΔT}_{f,p}(x_k, v) - σ_k/(p+1)! ‖v‖^{p+1}`. -/
theorem arModelDec_eq (k : ℕ) (v : ℝⁿ) :
    arModelDec P D σ k v =
      (D k).taylorDecrement P.p v - σ k / ((P.p + 1)! : ℝ) * ‖v‖ ^ (P.p + 1) := by
  rw [arModelDec, regularizedModel_zero_right, regularizedModel_def,
    FormalMultilinearSeries.taylorDecrement]
  ring

/-- The Step-1.2 test (13.1.53) passes at order `j` with the radius `δ^{(1)}_{k,j}`:
`\overline{ΔT}_{f,j}(x_k, d_{k,j}) ≤ ½ ς ε_j (δ^{(1)}_{k,j})^j/j!`. -/
def arPass (P : ARqpIDAParams) (ε : ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (δ₁ : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → ℝⁿ) (k j : ℕ) : Prop :=
  (D k).taylorDecrement j (dd k j) ≤ P.ς * ε j * δ₁ k j ^ j / j ! / 2

/-- Step 2 of ARqpIDA, entered at the least order `j_k` at which (13.1.53) fails (and (13.1.54)
holds): the step `s_k` (feasible) decreases the model at least as much as `d_k` (13.1.55), and
either `‖s_k‖ ≥ 1` with `δ_{s_k} = δ^{(1)}_k` (13.1.56) or the radii `δ_{s_k} ∈ (0, 1]^q` and
displacements `d^m_{s_k,ℓ}` satisfy (13.1.57); the iteration is accuracy-improving iff
`‖s_k‖ < 1` and the accuracy test (13.1.46) fails for some `i ∈ [1, p]`. -/
structure ARqpStep2 (X : Set ℝⁿ) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ)
    (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop) (k : ℕ) : Prop where
  /-- `j_k ∈ [1, q]`. -/
  jk_mem : jk k ∈ Finset.Icc 1 P.q
  /-- (13.1.53) fails at `j_k`. -/
  not_pass : ¬ arPass P ε D δ₁ dd k (jk k)
  /-- (13.1.53) holds below `j_k`. -/
  pass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < jk k → arPass P ε D δ₁ dd k j
  /-- The radii above `j_k` are not examined in Step 1. -/
  radius_gt : ∀ j ∈ Finset.Icc 1 P.q, jk k < j → δ₁ k j = δ k j
  /-- (13.1.54) at `j_k`. -/
  model_dec : P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ≤ arModelDec P D σ k (dd k (jk k))
  /-- The trial point is feasible. -/
  mem : x k + s k ∈ X
  /-- (13.1.55). -/
  dec_le : arModelDec P D σ k (dd k (jk k)) ≤ arModelDec P D σ k (s k)
  /-- (13.1.56) or (13.1.57). -/
  radii : (1 ≤ ‖s k‖ ∧ δs k = δ₁ k) ∨ ∀ ℓ ∈ Finset.Icc 1 P.q, δs k ℓ ∈ Set.Ioc 0 1 ∧
    ∃ dm, IsApproxMeasureStep
        ((ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ)
        (δs k ℓ) {e | x k + s k + e ∈ X} P.ς dm ∧
      (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ dm ≤
        P.ς * P.θ * ε ℓ * δs k ℓ ^ ℓ / ℓ !
  /-- Branching to Step 5 iff `‖s_k‖ < 1` and (13.1.46) fails for some `i ∈ [1, p]`. -/
  acc_iff : acc k ↔ ‖s k‖ < 1 ∧ ∃ i ∈ Finset.Icc 1 P.p, P.κs * ‖s k‖ ^ (P.p - i + 1) < h k i

/-- **Step 1 of ARqpIDA / ARqpEDA** ([cartis2022evaluation], Algorithm 13.1.2, Steps 1.1–1.4) at
iteration `k` on the feasible set `X`, with radii `δ k = δ^{(0)}_k` at the start of Step 1
(13.1.60) and `δ₁ k = δ^{(1)}_k` at its end (13.1.61). The halving loop (`δ_{k,j}` is halved while
(13.1.53) and (13.1.54) both fail) is recorded by its effect:
`0 < δ^{(1)}_{k,j} = δ^{(0)}_{k,j}/2^m ≤ δ^{(0)}_{k,j}`, and after at least one halving,
`2 δ^{(1)}_{k,j} ≤ δ^{(0)}_{k,j}` with a witness of the last halving (both tests failed at
radius `2 δ^{(1)}_{k,j}`) and of the
first one ((13.1.53) failed at radius `δ^{(0)}_{k,j}`). The final displacements satisfy
(13.1.52). -/
structure ARqpStep1 (X : Set ℝⁿ) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ)
    (δ δ₁ : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (k : ℕ) :
    Prop where
  /-- `δ^{(1)}_{k,j} > 0`. -/
  radius_pos : ∀ j ∈ Finset.Icc 1 P.q, 0 < δ₁ k j
  /-- `δ^{(1)}_{k,j} ≤ δ^{(0)}_{k,j}`. -/
  radius_le : ∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ≤ δ k j
  /-- The halving loop of Steps 1.1–1.4. -/
  halving : ∀ j ∈ Finset.Icc 1 P.q, δ₁ k j < δ k j → 2 * δ₁ k j ≤ δ k j ∧
    (∃ d', ‖d'‖ ≤ 2 * δ₁ k j ∧ x k + d' ∈ X ∧
      P.ς * ε j * (2 * δ₁ k j) ^ j / j ! / 2 < (D k).taylorDecrement j d' ∧
      arModelDec P D σ k d' < P.ς * ε j * (2 * δ₁ k j) ^ j / j ! / 4) ∧
    ∃ d₀, ‖d₀‖ ≤ δ k j ∧ x k + d₀ ∈ X ∧
      P.ς * ε j * δ k j ^ j / j ! / 2 < (D k).taylorDecrement j d₀
  /-- The radii at the end of Step 1 are obtained by halving:
  `δ^{(1)}_{k,j} = δ^{(0)}_{k,j}/2^m`. -/
  dyadic : ∀ j ∈ Finset.Icc 1 P.q, ∃ m : ℕ, δ₁ k j = δ k j / 2 ^ m
  /-- (13.1.52). -/
  witness : ∀ j ∈ Finset.Icc 1 P.q, IsApproxMeasureStep ((D k).taylorDecrement j) (δ₁ k j)
    {e | x k + e ∈ X} P.ς (dd k j)

/-- **One iteration of ARqpIDA / ARqpEDA** ([cartis2022evaluation], Algorithm 13.1.2, Steps 1, 2,
4, 5) on the feasible set `X`, given the ratio `ρ k`: Step 1 (`ARqpStep1`, radii `δ k`, `δ₁ k`);
if (13.1.53) holds at every order the iteration is accuracy-improving, otherwise Step 2
(`ARqpStep2`, radii `δs k = δ_{s_k}`) is performed. A trial iteration accepts or rejects the step,
updates `σ` by (13.1.59), inherits the radii `δ_{s_k}` after a successful short step and
`δ^{(1)}_k` otherwise, keeps the accuracies, and keeps the derivative estimates when the step is
rejected; an accuracy-improving iteration keeps `x_k`, `σ_k` and `δ^{(0)}_k` and multiplies the
accuracies by `γ_h`. -/
structure ARqpDAStep (X : Set ℝⁿ) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ)
    (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
    (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop) (ρ : ℕ → ℝ) (k : ℕ) :
    Prop extends ARqpStep1 X P ε x σ δ δ₁ D dd k where
  /-- Step 1 → Step 5 when (13.1.53) holds at every order. -/
  acc_of_pass : (∀ j ∈ Finset.Icc 1 P.q, arPass P ε D δ₁ dd k j) → acc k
  /-- Step 2 otherwise. -/
  step2 : (∃ j ∈ Finset.Icc 1 P.q, ¬ arPass P ε D δ₁ dd k j) →
    ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k
  /-- Steps 3–4 on a trial iteration. -/
  accept : ¬ acc k → ARAcceptance P.toARParams (ρ k) (x k) (s k) (x (k + 1)) (σ k) (σ (k + 1))
  /-- The radii inherited by the next iteration (Step 3). -/
  radii_trial : ¬ acc k →
    δ (k + 1) = if P.η₁ ≤ ρ k ∧ ‖s k‖ < 1 then δs k else δ₁ k
  /-- The accuracies are kept on trial iterations. -/
  h_trial : ¬ acc k → h (k + 1) = h k
  /-- No new derivative estimates at an unchanged iterate. -/
  D_unsucc : ¬ acc k → ρ k < P.η₁ → D (k + 1) = D k
  /-- Step 5 keeps the iterate. -/
  x_acc : acc k → x (k + 1) = x k
  /-- Step 5 keeps the radii `δ^{(0)}_k`. -/
  δ_acc : acc k → δ (k + 1) = δ k
  /-- Step 5 keeps the regularization parameter. -/
  σ_acc : acc k → σ (k + 1) = σ k
  /-- Step 5 multiplies the accuracies by `γ_h`. -/
  h_acc : acc k → ∀ i, h (k + 1) i = P.γh * h k i

/-- The radii control of ARqpIDA / ARqpEDA in one of two modes, selected by the proposition `u`
([cartis2022evaluation], (13.1.69)–(13.1.70) and §14.2): after a trial iteration with a short
step `‖s_k‖ < 1`, if `u` holds then `δ_{s_k,j} = 1` for all `j ∈ [1, q]` (unit radii), and if `u`
fails then `δ_{s_k,j} ≥ ς θ ε_j/(24 max(L̄, σ_k))` for all `j ∈ [1, q]` (the (12.2.51)-type lower
bound at every order). Unit radii are what Algorithm 12.2.3 delivers for `q ≤ 2` without
constraints (or for `q = 1` on a convex feasible set); the lower bound is available in every
case, in particular for `q > 2` or with a general feasible set. The complexity orders depend on
the mode (`arPiOf u`). -/
def RadiiControlOf (u : Prop) (P : ARqpIDAParams) (ε : ℕ → ℝ) (Lb : ℝ) (σ : ℕ → ℝ)
    (δs : ℕ → ℕ → ℝ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop) (k : ℕ) : Prop :=
  ¬ acc k → ‖s k‖ < 1 → (u → ∀ j ∈ Finset.Icc 1 P.q, δs k j = 1) ∧
    (¬ u → ∀ j ∈ Finset.Icc 1 P.q, P.ς * P.θ * ε j / (24 * max Lb (σ k)) ≤ δs k j)

/-- The radii control assumed in Theorem 13.1.19 ([cartis2022evaluation], (13.1.69)–(13.1.70)),
in the form used by the analysis: `RadiiControlOf` with unit radii exactly when `q ≤ 2`, i.e.
after a trial iteration with a short step, `δ_{s_k,j} = 1` for all `j ∈ [1, q]` if `q ≤ 2`, and
`δ_{s_k,j} ≥ ς θ ε_j/(24 max(L̄, σ_k))` for all `j ∈ [1, q]` if `q > 2`. The book's
(13.1.69)–(13.1.70) (`δ_{s_k,j} = 1` for `j ≤ min(2, q)` and the lower bound for `j ∈ [3, q]`,
achievable by Algorithm 12.2.3 as Lemma 13.1.12 shows) imply it (`RadiiControl.of_book`). -/
def RadiiControl (P : ARqpIDAParams) (ε : ℕ → ℝ) (Lb : ℝ) (σ : ℕ → ℝ) (δs : ℕ → ℕ → ℝ)
    (s : ℕ → ℝⁿ) (acc : ℕ → Prop) (k : ℕ) : Prop :=
  RadiiControlOf (P.q ≤ 2) P ε Lb σ δs s acc k

/-- `RadiiControl` in the printed form, with the case `2 < q` for the lower bounds. -/
theorem radiiControl_iff {P : ARqpIDAParams} {ε : ℕ → ℝ} {Lb : ℝ} {σ : ℕ → ℝ}
    {δs : ℕ → ℕ → ℝ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {k : ℕ} :
    RadiiControl P ε Lb σ δs s acc k ↔
      (¬ acc k → ‖s k‖ < 1 → (P.q ≤ 2 → ∀ j ∈ Finset.Icc 1 P.q, δs k j = 1) ∧
        (2 < P.q → ∀ j ∈ Finset.Icc 1 P.q, P.ς * P.θ * ε j / (24 * max Lb (σ k)) ≤ δs k j)) := by
  simp only [RadiiControl, RadiiControlOf, not_le]

/-- Unit radii give the radii control in either mode: if `δ_{s_k,j} = 1` for all `j ∈ [1, q]`
after a trial iteration with a short step, `ε_j ≤ 1` and `L̄ ≥ 1`, then `RadiiControlOf u` holds
for every `u` (the lower bound `ς θ ε_j/(24 max(L̄, σ_k)) ≤ 1` is automatic). -/
theorem RadiiControlOf.of_unit {P : ARqpIDAParams} {ε : ℕ → ℝ} {Lb : ℝ} {σ : ℕ → ℝ}
    {δs : ℕ → ℕ → ℝ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {k : ℕ} {u : Prop} (hLb : 1 ≤ Lb)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ 1)
    (h1 : ¬ acc k → ‖s k‖ < 1 → ∀ j ∈ Finset.Icc 1 P.q, δs k j = 1) :
    RadiiControlOf u P ε Lb σ δs s acc k := by
  intro hk hs1
  refine ⟨fun _ => h1 hk hs1, fun _ j hj => ?_⟩
  rw [h1 hk hs1 j hj]
  have hM : 1 ≤ max Lb (σ k) := hLb.trans (le_max_left _ _)
  have := P.ς_pos; have := P.ς_le_one; have := P.θ_pos; have := P.θ_lt_one
  rw [div_le_one (by positivity)]
  have h0 : P.ς * P.θ ≤ 1 := mul_le_one_of_le_one P.ς_le_one P.θ_pos.le P.θ_lt_one.le
  rcases le_or_gt (ε j) 0 with hε0 | hε0
  · have : P.ς * P.θ * ε j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hε0
    linarith
  · have : P.ς * P.θ * ε j ≤ 1 := by nlinarith [hε j hj]
    linarith

/-- The book's radii control (13.1.69)–(13.1.70) (`δ_{s_k,j} = 1` for `j ≤ min(2, q)`,
`δ_{s_k,j} ≥ ς θ ε_j/(24 max(L̄, σ_k))` for `j ∈ [3, q]`) implies `RadiiControl` when
`ε ∈ (0, 1]^q` and `L̄ ≥ 1`. -/
theorem RadiiControl.of_book {P : ARqpIDAParams} {ε : ℕ → ℝ} {Lb : ℝ} {σ : ℕ → ℝ}
    {δs : ℕ → ℕ → ℝ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {k : ℕ}
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hLb : 1 ≤ Lb)
    (h : ¬ acc k → ‖s k‖ < 1 → (∀ j ∈ Finset.Icc 1 (min 2 P.q), δs k j = 1) ∧
      ∀ j ∈ Finset.Icc 3 P.q, P.ς * P.θ * ε j / (24 * max Lb (σ k)) ≤ δs k j) :
    RadiiControl P ε Lb σ δs s acc k := by
  intro hk hs1
  obtain ⟨h1, h2⟩ := h hk hs1
  refine ⟨fun hq j hj => h1 j ?_, fun _ j hj => ?_⟩
  · obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
    exact Finset.mem_Icc.2 ⟨hj1, le_min (hjq.trans hq) hjq⟩
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  rcases le_or_gt j 2 with hj2 | hj2
  · rw [h1 j (Finset.mem_Icc.2 ⟨hj1, le_min hj2 hjq⟩)]
    have hM : 1 ≤ max Lb (σ k) := hLb.trans (le_max_left _ _)
    have := P.ς_pos; have := P.ς_le_one; have := P.θ_pos; have := P.θ_lt_one
    have hεj := hε j hj
    rw [div_le_one (by positivity)]
    have : P.ς * P.θ * ε j ≤ 1 :=
      mul_le_one_of_le_one (mul_le_one_of_le_one P.ς_le_one P.θ_pos.le P.θ_lt_one.le)
        hεj.1.le hεj.2
    linarith
  · exact h2 j (Finset.mem_Icc.2 ⟨hj2, hjq⟩)

namespace ARqpDAStep

variable (hs : ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ k)
include hs

/-- A trial iteration went through Step 2. -/
theorem step2_of_not_acc (hk : ¬ acc k) : ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k := by
  refine hs.step2 ?_
  by_contra hc
  push Not at hc
  exact hk (hs.acc_of_pass hc)

/-- The parameter update of a trial iteration. -/
theorem update (hk : ¬ acc k) :
    ARUpdate P.η₁ P.η₂ P.γ₁ P.γ₂ P.γ₃ P.σmin (ρ k) (σ k) (σ (k + 1)) :=
  (hs.accept hk).2

/-- The iterate is kept unless the iteration is successful. -/
theorem x_succ_eq (hk : ¬ (¬ acc k ∧ P.η₁ ≤ ρ k)) : x (k + 1) = x k := by
  by_cases ha : acc k
  · exact hs.x_acc ha
  · exact (hs.accept ha).eq_self (not_le.1 fun h' => hk ⟨ha, h'⟩)

/-- A successful iteration moves to the trial point. -/
theorem x_succ_eq_add (hk : ¬ acc k) (hρ : P.η₁ ≤ ρ k) : x (k + 1) = x k + s k :=
  (hs.accept hk).eq_add hρ

/-- The iterates stay feasible: `x_k ∈ X` implies `x_{k+1} ∈ X`. -/
theorem mem_succ (hx : x k ∈ X) : x (k + 1) ∈ X := by
  by_cases hc : ¬ acc k ∧ P.η₁ ≤ ρ k
  · rw [hs.x_succ_eq_add hc.1 hc.2]; exact (hs.step2_of_not_acc hc.1).mem
  · rw [hs.x_succ_eq hc]; exact hx

/-- One iteration only involves the data at iterations `k` and `k + 1`: the step predicate at `k`
transfers to sequences whose iterates, weights, radii `δ^{(0)}`, accuracies and estimates at `k'`
and `k' + 1`, and whose radii `δ^{(1)}`, `δ_s`, displacements, order, step, flag and ratio at
`k'`, are those of iterations `k` and `k + 1` (used to splice runs). -/
theorem congr {x' : ℕ → ℝⁿ} {σ' : ℕ → ℝ} {δ' δ₁' δs' : ℕ → ℕ → ℝ} {h' : ℕ → ℕ → ℝ}
    {D' : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd' : ℕ → ℕ → ℝⁿ} {jk' : ℕ → ℕ} {s' : ℕ → ℝⁿ}
    {acc' : ℕ → Prop} {ρ' : ℕ → ℝ} {k' : ℕ} (hx : x' k' = x k) (hx1 : x' (k' + 1) = x (k + 1))
    (hσ : σ' k' = σ k) (hσ1 : σ' (k' + 1) = σ (k + 1)) (hδ : δ' k' = δ k)
    (hδ1 : δ' (k' + 1) = δ (k + 1)) (hδ₁ : δ₁' k' = δ₁ k) (hδs : δs' k' = δs k)
    (hh : h' k' = h k) (hh1 : h' (k' + 1) = h (k + 1)) (hD : D' k' = D k)
    (hD1 : D' (k' + 1) = D (k + 1)) (hdd : dd' k' = dd k) (hjk : jk' k' = jk k)
    (hs' : s' k' = s k) (hacc : acc' k' ↔ acc k) (hρ : ρ' k' = ρ k) :
    ARqpDAStep X P ε x' σ' δ' δ₁' δs' h' D' dd' jk' s' acc' ρ' k' := by
  obtain ⟨⟨hpos, hle, hhalf, hdy, hw⟩, hap, hst, hac, hrt, hht, hdu, hxa, hδa, hσa, hha⟩ := hs
  have hP : ∀ j, arPass P ε D' δ₁' dd' k' j ↔ arPass P ε D δ₁ dd k j := fun j => by
    simp only [arPass, hD, hδ₁, hdd]
  have hM : ∀ v, arModelDec P D' σ' k' v = arModelDec P D σ k v := fun v => by
    simp only [arModelDec, hD, hσ]
  refine ⟨⟨fun j hj => ?_, fun j hj => ?_, fun j hj hlt => ?_, fun j hj => ?_, fun j hj => ?_⟩,
    fun hp => hacc.2 (hap fun j hj => (hP j).1 (hp j hj)), fun ⟨j, hj, hf⟩ => ?_,
    fun ha => ?_, fun ha => ?_, fun ha => ?_, fun ha hr => ?_, fun ha => ?_, fun ha => ?_,
    fun ha => ?_, fun ha => ?_⟩
  · rw [hδ₁]; exact hpos j hj
  · rw [hδ₁, hδ]; exact hle j hj
  · rw [hδ₁, hδ] at hlt ⊢
    simp only [hx, hM, hD]
    exact hhalf j hj hlt
  · rw [hδ₁, hδ]; exact hdy j hj
  · rw [hδ₁, hD, hx, hdd]; exact hw j hj
  · obtain ⟨hjm, hnp, hpl, hrg, hmd, hmem, hdl, hrad, hai⟩ :=
      hst ⟨j, hj, fun h' => hf ((hP j).2 h')⟩
    refine ⟨hjk ▸ hjm, fun h' => hnp ((hP _).1 (hjk ▸ h')), fun i hi hlt => (hP i).2
      (hpl i hi (hjk ▸ hlt)), fun i hi hlt => by rw [hδ₁, hδ]; exact hrg i hi (hjk ▸ hlt),
      by rw [hM, hjk, hdd, hδ₁]; exact hmd, by rw [hx, hs']; exact hmem,
      by rw [hM, hM, hjk, hdd, hs']; exact hdl, ?_, by rw [hacc, hs', hh]; exact hai⟩
    rw [hs', hδs, hD, hσ, hx, hδ₁]; exact hrad
  · rw [hρ, hx, hs', hx1, hσ, hσ1]; exact hac (fun h => ha (hacc.2 h))
  · rw [hδ1, hρ, hs', hδs, hδ₁]; exact hrt (fun h => ha (hacc.2 h))
  · rw [hh1, hh]; exact hht (fun h => ha (hacc.2 h))
  · rw [hD1, hD]; exact hdu (fun h => ha (hacc.2 h)) (hρ ▸ hr)
  · rw [hx1, hx]; exact hxa (hacc.1 ha)
  · rw [hδ1, hδ]; exact hδa (hacc.1 ha)
  · rw [hσ1, hσ]; exact hσa (hacc.1 ha)
  · rw [hh1, hh]; exact hha (hacc.1 ha)

end ARqpDAStep

/-- The iterates of ARqpIDA/ARqpEDA sequences starting in `X` stay in `X`. -/
theorem arqp_mem (hstep : ∀ i < k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hx0 : x 0 ∈ X) : x k ∈ X := by
  induction k with
  | zero => exact hx0
  | succ k ih => exact (hstep k k.lt_succ_self).mem_succ (ih fun i hi => hstep i (by omega))

/-- A trial step with `‖s_k‖ < 1` satisfies (13.1.57). -/
theorem ARqpStep2.radii_of_lt (h2 : ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k)
    (hs1 : ‖s k‖ < 1) :
    ∀ ℓ ∈ Finset.Icc 1 P.q, δs k ℓ ∈ Set.Ioc 0 1 ∧
      ∃ dm, IsApproxMeasureStep
          ((ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ)
          (δs k ℓ) {e | x k + s k + e ∈ X} P.ς dm ∧
        (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)).taylorDecrement ℓ dm ≤
          P.ς * P.θ * ε ℓ * δs k ℓ ^ ℓ / ℓ ! :=
  h2.radii.resolve_left fun h' => absurd h'.1 (not_le.2 hs1)

/-- On a trial iteration with `‖s_k‖ < 1`, the accuracy test (13.1.46) holds. -/
theorem ARqpStep2.h_le_of_not_acc (h2 : ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k)
    (hk : ¬ acc k) (hs1 : ‖s k‖ < 1) :
    ∀ i ∈ Finset.Icc 1 P.p, h k i ≤ P.κs * ‖s k‖ ^ (P.p - i + 1) := by
  intro i hi
  by_contra hc
  exact hk (h2.acc_iff.2 ⟨hs1, i, hi, not_le.1 hc⟩)

/-- **Invariants of ARqpIDA/ARqpEDA sequences**: if the step predicate holds at every iteration
`i < k`, `σ_0 = σ₀`, `δ_0 = δ₀` and `h_0 = h₀`, then `σ_k ≥ σ_min`, `δ_{k,j} ∈ (0, 1]` for
`j ∈ [1, q]` and `0 ≤ h_{k,i} ≤ κ_h` for `i ∈ [1, p]`. -/
theorem arqp_invariants (hstep : ∀ i < k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hσ0 : σ 0 = P.σ₀) (hδ0 : δ 0 = P.δ₀) (hh0 : h 0 = P.h₀) :
    P.σmin ≤ σ k ∧ (∀ j ∈ Finset.Icc 1 P.q, 0 < δ k j ∧ δ k j ≤ 1) ∧
      ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ h k i ∧ h k i ≤ P.κh := by
  induction k with
  | zero =>
    rw [hσ0, hδ0, hh0]
    exact ⟨P.σmin_le_σ₀, fun j hj => P.δ₀_mem j hj, fun i hi => ⟨P.h₀_nonneg i hi, P.h₀_le i hi⟩⟩
  | succ k ih =>
    obtain ⟨hσ, hδ, hh⟩ := ih fun i hi => hstep i (hi.trans k.lt_succ_self)
    have hk := hstep k k.lt_succ_self
    by_cases ha : acc k
    · refine ⟨by rw [hk.σ_acc ha]; exact hσ, by rw [hk.δ_acc ha]; exact hδ, fun i hi => ?_⟩
      rw [hk.h_acc ha i]
      obtain ⟨h1, h2⟩ := hh i hi
      exact ⟨mul_nonneg P.γh_pos.le h1, (mul_le_of_le_one_left h1 P.γh_lt_one.le).trans h2⟩
    refine ⟨(hk.update ha).sigmaMin_le P.σmin_nonneg P.one_le_γ₂ hσ, ?_,
      by rw [hk.h_trial ha]; exact hh⟩
    intro j hj
    rw [hk.radii_trial ha]
    split_ifs with hc
    · exact ((hk.step2_of_not_acc ha).radii_of_lt hc.2 j hj).1
    · exact ⟨hk.radius_pos j hj, (hk.radius_le j hj).trans (hδ j hj).2⟩

/-- The regularization parameters of ARqpIDA/ARqpEDA sequences are positive. -/
theorem arqp_sigma_pos (hstep : ∀ i < k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hσ0 : σ 0 = P.σ₀) (hδ0 : δ 0 = P.δ₀) (hh0 : h 0 = P.h₀) : 0 < σ k :=
  P.σmin_pos.trans_le (arqp_invariants hstep hσ0 hδ0 hh0).1

/-! ### Lemma 13.1.9 -/

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
        Real.log (σmax / P.σ₀) / Real.log P.γ₂ := by
  have hpos : ∀ i ≤ k, 0 < σ i := fun i hi =>
    arqp_sigma_pos (fun j hj => hstep j (by omega)) hσ0 hδ0 hh0
  have h := card_successSet_or_le_of_lower_ratio (σ := σ) (k := k)
    (succ := fun i => ¬ acc i ∧ P.η₁ ≤ ρ i) (fail := fun i => ¬ acc i ∧ ρ i < P.η₁)
    (hσ0 ▸ P.σ₀_pos) P.γ₁_pos P.γ₁_le_one P.one_lt_γ₂
    (fun i _ hi hf => not_le.2 hf.2 hi.2)
    (fun i hi hs => ((hstep i hi).update hs.1).mul_le_of_le hs.2 P.γ₁_le_one (hpos i hi).le)
    (fun i hi hf => ((hstep i hi).update hf.1).mul_le_of_lt hf.2)
    (fun i hi hs hf => by
      have ha : acc i := by
        by_contra ha
        rcases le_or_gt P.η₁ (ρ i) with hρ | hρ
        · exact hs ⟨ha, hρ⟩
        · exact hf ⟨ha, hρ⟩
      rw [(hstep i hi).σ_acc ha])
    hσmax
  rw [hσ0] at h
  have hset : successSet (fun i => (¬ acc i ∧ P.η₁ ≤ ρ i) ∨ (¬ acc i ∧ ρ i < P.η₁)) k =
      successSet (fun i => ¬ acc i) k := by
    ext i
    simp only [mem_successSet]
    constructor
    · rintro ⟨hi, (h1 | h1)⟩ <;> exact ⟨hi, h1.1⟩
    · rintro ⟨hi, h1⟩
      exact ⟨hi, (le_or_gt P.η₁ (ρ i)).imp (fun h2 => ⟨h1, h2⟩) fun h2 => ⟨h1, h2⟩⟩
  rwa [hset] at h

/-! ### Lemmas 13.1.10–13.1.13 -/

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
    δ₁ k j ≤ δ k j ∧ min (P.ς * ε j / (16 * max Lb (σ k))) (δ k j) ≤ δ₁ k j := by
  refine ⟨hs.radius_le j hj, ?_⟩
  rcases (hs.radius_le j hj).lt_or_eq with hlt | heq
  swap
  · rw [heq]; exact min_le_right _ _
  obtain ⟨h2δ, ⟨d', hd'n, -, hd'T, hd'm⟩, -⟩ := hs.halving j hj hlt
  refine (min_le_left _ _).trans ?_
  by_contra hcon
  push Not at hcon
  have hM : 0 < max Lb (σ k) := lt_max_of_lt_left hLb
  have hjp : j ≤ P.p := (Finset.mem_Icc.1 hj).2.trans P.q_le_p
  have hpos := hs.radius_pos j hj
  have hε : 0 < ε j := by
    by_contra hε
    push Not at hε
    have : P.ς * ε j / (16 * max Lb (σ k)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos P.ς_pos.le hε) (by positivity)
    linarith
  have key := regularizedModel_decrease_ge_of_taylorDecrement_ge (D := D k) (p := P.p)
    (σ := σ k) (L := Lb) hjp hσ
    (fun ℓ hℓ => hD ℓ (Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hℓ).1; omega,
      (Finset.mem_Icc.1 hℓ).2⟩))
    (α := P.ς * ε j / 2) (δ := 2 * δ₁ k j) (by positivity) (h2δ.trans (hδ1 j hj)) ?_ hd'n
    (by
      have : P.ς * ε j / 2 * (2 * δ₁ k j) ^ j / j ! = P.ς * ε j * (2 * δ₁ k j) ^ j / j ! / 2 := by
        ring
      linarith)
  · have : P.ς * ε j / 2 / 2 * (2 * δ₁ k j) ^ j / j ! =
        P.ς * ε j * (2 * δ₁ k j) ^ j / j ! / 4 := by ring
    rw [this] at key
    exact absurd key (not_le.2 hd'm)
  · rw [lt_div_iff₀ (by positivity)] at hcon
    nlinarith

/-- The constant `κ^{(1)}_δ(σ) = ς θ/(24 max(L̄, σ))` of (13.1.72). -/
noncomputable def arKappaDelta1 (P : ARqpIDAParams) (Lb σ : ℝ) : ℝ :=
  P.ς * P.θ / (24 * max Lb σ)

theorem arKappaDelta1_pos {P : ARqpIDAParams} {Lb σ : ℝ} (hLb : 0 < Lb) :
    0 < arKappaDelta1 P Lb σ := by
  have := P.ς_pos; have := P.θ_pos
  exact div_pos (by positivity) (by have : 0 < max Lb σ := lt_max_of_lt_left hLb; positivity)

theorem arKappaDelta1_le_one {P : ARqpIDAParams} {Lb σ : ℝ} (hLb : 1 ≤ Lb) :
    arKappaDelta1 P Lb σ ≤ 1 := by
  have := P.ς_pos; have := P.ς_le_one; have := P.θ_pos; have := P.θ_lt_one
  have hM : 1 ≤ max Lb σ := hLb.trans (le_max_left _ _)
  rw [arKappaDelta1, div_le_one (by positivity)]
  nlinarith

/-- Either mode of the radii control gives the lower bound `κ^{(1)}_δ(σ̄) ε_j ≤ δ_{s_k,j}` after
a trial iteration with a short step, when `ε ∈ (0, 1]^q`, `L̄ ≥ 1` and `σ_k ≤ σ̄`. -/
theorem RadiiControlOf.kappa_mul_le {u : Prop} {P : ARqpIDAParams} {ε : ℕ → ℝ} {Lb : ℝ}
    {σ : ℕ → ℝ} {δs : ℕ → ℕ → ℝ} {s : ℕ → ℝⁿ} {acc : ℕ → Prop} {k : ℕ}
    (hrc : RadiiControlOf u P ε Lb σ δs s acc k) (hk : ¬ acc k) (hs : ‖s k‖ < 1)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hLb : 1 ≤ Lb) {σbar : ℝ}
    (hσ : σ k ≤ σbar) {j : ℕ} (hj : j ∈ Finset.Icc 1 P.q) :
    arKappaDelta1 P Lb σbar * ε j ≤ δs k j := by
  obtain ⟨h1, h2⟩ := hrc hk hs
  have hεj := hε j hj
  have := P.ς_pos; have := P.ς_le_one; have := P.θ_pos; have := P.θ_lt_one
  have hM : 1 ≤ max Lb σbar := hLb.trans (le_max_left _ _)
  have hM' : 1 ≤ max Lb (σ k) := hLb.trans (le_max_left _ _)
  by_cases hu : u
  · rw [h1 hu j hj, arKappaDelta1, div_mul_eq_mul_div, div_le_one (by positivity)]
    have : P.ς * P.θ * ε j ≤ 1 :=
      mul_le_one_of_le_one (mul_le_one_of_le_one P.ς_le_one P.θ_pos.le P.θ_lt_one.le)
        hεj.1.le hεj.2
    nlinarith
  · refine le_trans ?_ (h2 hu j hj)
    rw [arKappaDelta1, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (by have := hεj.1; positivity) (by positivity)
      (by have := max_le_max (le_refl Lb) hσ; linarith)

/-- **The radius bound (13.1.71) of Lemma 13.1.12** ([cartis2022evaluation]), for sequences
satisfying the ARqpIDA step predicate at every iteration `i < k` and Step 1 at `k`, with
`ε ∈ (0, 1]^q`, `ε ≤ δ₀`, `‖∇̄^ℓ f(x_i)‖ ≤ L̄` (`L̄ ≥ 1`), `σ_i ≤ σ̄` for `i ≤ k` and the radii
control (`RadiiControlOf`, either mode) at every `i < k`:
`δ^{(0)}_{k,j} ≥ δ^{(1)}_{k,j} ≥ κ^{(1)}_δ(σ̄) ε_j` for `j ∈ [1, q]`. (The book takes
`σ̄ = σ_{k,max} = max_{i ≤ k} σ_i`.) -/
theorem arqp_radius_ge (hstep : ∀ i < k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ i)
    (hstep1 : ARqpStep1 X P ε x σ δ δ₁ D dd k) (hσ0 : σ 0 = P.σ₀) (hδ0 : δ 0 = P.δ₀)
    (hh0 : h 0 = P.h₀)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hεδ : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j)
    {Lb σbar : ℝ} (hLb : 1 ≤ Lb) (hD : ∀ i ≤ k, ∀ ℓ ∈ Finset.Icc 1 P.p, ‖D i ℓ‖ ≤ Lb)
    (hσ : ∀ i ≤ k, σ i ≤ σbar) {u : Prop}
    (hrc : ∀ i < k, RadiiControlOf u P ε Lb σ δs s acc i) :
    ∀ j ∈ Finset.Icc 1 P.q, arKappaDelta1 P Lb σbar * ε j ≤ δ₁ k j ∧ δ₁ k j ≤ δ k j := by
  have hLb0 : 0 < Lb := zero_lt_one.trans_le hLb
  set κ := arKappaDelta1 P Lb σbar with hκdef
  have hκ0 : 0 < κ := arKappaDelta1_pos hLb0
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  have hς := P.ς_pos
  have hθ := P.θ_pos
  have hθ1 := P.θ_lt_one.le
  have hσpos : ∀ i ≤ k, 0 < σ i := fun i hi =>
    arqp_sigma_pos (fun j hj => hstep j (by omega)) hσ0 hδ0 hh0
  have hMle : ∀ i ≤ k, max Lb (σ i) ≤ max Lb σbar := fun i hi => max_le_max le_rfl (hσ i hi)
  -- (a) the halving lower bound dominates `κ ε`
  have ha : ∀ i ≤ k, ∀ j ∈ Finset.Icc 1 P.q,
      κ * ε j ≤ P.ς * ε j / (16 * max Lb (σ i)) := by
    intro i hi j hj
    have hεj := (hε j hj).1
    have hM : 0 < max Lb (σ i) := lt_max_of_lt_left hLb0
    rw [le_div_iff₀ (by positivity), hκdef, arKappaDelta1, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_le_iff₀ (by have : 0 < max Lb σbar := lt_max_of_lt_left hLb0; positivity)]
    have := hMle i hi
    have h1 : P.ς * P.θ * ε j * (16 * max Lb (σ i)) ≤ P.ς * 1 * ε j * (16 * max Lb σbar) := by
      gcongr
    have : 0 ≤ P.ς * ε j * max Lb σbar := by
      have : 0 < max Lb σbar := lt_max_of_lt_left hLb0
      positivity
    linarith
  -- the radii at the start of Step 1
  have hδk : ∀ i ≤ k, ∀ j ∈ Finset.Icc 1 P.q, κ * ε j ≤ δ i j := by
    intro i
    induction i with
    | zero =>
      intro _ j hj
      rw [hδ0]
      exact (mul_le_of_le_one_left (hε j hj).1.le hκ1).trans (hεδ j hj)
    | succ i ih =>
      intro hi j hj
      have hik : i ≤ k := by omega
      have hsi := hstep i (by omega)
      have hδ1i : ∀ j ∈ Finset.Icc 1 P.q, δ i j ≤ 1 := fun j hj =>
        ((arqp_invariants (fun l hl => hstep l (by omega)) hσ0 hδ0 hh0).2.1 j hj).2
      have h11 := (lemma_13_1_11 hsi.toARqpStep1 hLb0 (hD i hik) (hσpos i hik).le hδ1i hj).2
      have hδ₁ : κ * ε j ≤ δ₁ i j := (le_min (ha i hik j hj) (ih hik j hj)).trans h11
      by_cases hacc : acc i
      · rw [hsi.δ_acc hacc]; exact ih hik j hj
      rw [hsi.radii_trial hacc]
      split_ifs with hc
      · exact (hrc i (by omega)).kappa_mul_le hacc hc.2 hε hLb (hσ i hik) hj
      · exact hδ₁
  intro j hj
  have hδ1k : ∀ j ∈ Finset.Icc 1 P.q, δ k j ≤ 1 := fun j hj =>
    ((arqp_invariants (fun l hl => hstep l (by omega)) hσ0 hδ0 hh0).2.1 j hj).2
  have h11 := lemma_13_1_11 hstep1 hLb0 (hD k le_rfl) (hσpos k le_rfl).le hδ1k hj
  exact ⟨(le_min (ha k le_rfl j hj) (hδk k le_rfl j hj)).trans h11.2, h11.1⟩

/-- **Lemma 13.1.13** ([cartis2022evaluation]): at a trial iteration `k ∈ 𝒯` of ARqpIDA (or
ARqpEDA) with `ε_{j_k} > 0` and `σ_k ≥ 0`,
`\overline{ΔT}_{f,p}(x_k, s_k) ≥ σ_k/(p+1)! ‖s_k‖^{p+1}` (13.1.76) and
`\overline{ΔT}_{f,p}(x_k, s_k) > 0`, so that the ratio (13.1.58) is well defined. -/
theorem lemma_13_1_13 (hs : ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc ρ k) (hk : ¬ acc k)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, 0 < ε j) (hσ : 0 ≤ σ k) :
    σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) ≤ (D k).taylorDecrement P.p (s k) ∧
      0 < (D k).taylorDecrement P.p (s k) := by
  have h2 := hs.step2_of_not_acc hk
  have hpos : 0 < P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 := by
    have := P.ς_pos; have := hε _ h2.jk_mem; have := hs.radius_pos _ h2.jk_mem; positivity
  have hm := hpos.trans_le (h2.model_dec.trans h2.dec_le)
  rw [arModelDec_eq] at hm
  have : 0 ≤ σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) := by positivity
  constructor <;> linarith

/-- **The accuracy bound (13.1.73) of Lemma 13.1.12** ([cartis2022evaluation]), for one
iteration of the ARqpIDA step predicate that goes through Step 2: if `‖∇̄^i f(x_k)‖ ≤ L̄` for
`i ∈ [1, p]` (`L̄ ≥ 1`), `σ_k ≥ 0`, any `σ̄`, `ε ∈ (0, 1]^q`, `0 ≤ κ ≤ 1` with
`δ^{(1)}_{k,j} ≥ κ ε_j`,
and `h_{k,i} ≤ κ_s (ς κ^q/(12 q! max(L̄, σ̄)))^p ε_min^{p(q+1)}` for `i ∈ [1, p]`, then the
iteration is not accuracy-improving. -/
theorem ARqpStep2.not_acc_of_le (h2 : ARqpStep2 X P ε x σ δ δ₁ δs h D dd jk s acc k)
    (hpos : ∀ j ∈ Finset.Icc 1 P.q, 0 < δ₁ k j) {Lb σbar κ : ℝ} (hLb : 1 ≤ Lb)
    (hD : ∀ i ∈ Finset.Icc 1 P.p, ‖D k i‖ ≤ Lb) (hσ : 0 ≤ σ k)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hδ₁ : ∀ j ∈ Finset.Icc 1 P.q, κ * ε j ≤ δ₁ k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, h k i ≤
      P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * max Lb σbar)) ^ P.p *
        epsMin P.q ε ^ (P.p * (P.q + 1))) :
    ¬ acc k := by
  have hq := P.one_le_q
  have hεmin : 0 < epsMin P.q ε := epsMin_pos hq fun j hj => (hε j hj).1
  have hεmin1 : epsMin P.q ε ≤ 1 := epsMin_le_one hq fun j hj => (hε j hj).2
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 h2.jk_mem
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  set j := jk k
  set em := epsMin P.q ε
  set M := max Lb σbar
  have hM : 1 ≤ M := hLb.trans (le_max_left _ _)
  set c := P.ς * κ ^ P.q / (12 * P.q ! * M) * em ^ (P.q + 1) with hc
  have hfq : (1 : ℝ) ≤ P.q ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_mul_eq_mul_div, div_le_one (by positivity)]
    calc P.ς * κ ^ P.q * em ^ (P.q + 1) ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul hς1 (pow_le_one₀ hκ0 hκ1) (by positivity) zero_le_one)
            (pow_le_one₀ hεmin.le hεmin1) (by positivity) (by norm_num)
      _ ≤ 12 * P.q ! * M := by nlinarith
  rw [h2.acc_iff]
  rintro ⟨hs1, i, hi, hlt⟩
  refine absurd hlt (not_lt.2 ?_)
  -- the step is not too short
  have hsc : c ≤ ‖s k‖ := by
    have hup := taylorDecrement_le_two_mul (D := D k) (j := P.p) (zero_le_one.trans hLb) hD hs1.le
    have hm := h2.model_dec.trans h2.dec_le
    rw [arModelDec_eq] at hm
    have hσs : 0 ≤ σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) := by positivity
    have hlow : P.ς * ε j * δ₁ k j ^ j / j ! / 4 ≤ 2 * Lb * ‖s k‖ := by linarith
    have hm0 : 0 ≤ κ * em := by positivity
    have hm1 : κ * em ≤ 1 := mul_le_one_of_le_one hκ1 hεmin.le hεmin1
    have hδj : (κ * em) ^ P.q ≤ δ₁ k j ^ j :=
      (pow_le_pow_of_le_one hm0 hm1 hjq).trans (pow_le_pow_left₀ hm0
        ((mul_le_mul_of_nonneg_left (epsMin_le h2.jk_mem) hκ0).trans (hδ₁ j h2.jk_mem)) j)
    have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
    have hεj : em ≤ ε j := epsMin_le h2.jk_mem
    have hLbM : 2 * Lb ≤ 3 * M := by have := le_max_left Lb σbar; linarith
    have hnum : P.ς * em * (κ * em) ^ P.q ≤ P.ς * ε j * δ₁ k j ^ j :=
      mul_le_mul (mul_le_mul_of_nonneg_left hεj hς.le) hδj (by positivity)
        (mul_nonneg hς.le (hεmin.le.trans hεj))
    have hN : 0 ≤ P.ς * ε j * δ₁ k j ^ j :=
      mul_nonneg (mul_nonneg hς.le (hεmin.le.trans hεj)) (pow_nonneg (hpos j h2.jk_mem).le _)
    calc c = P.ς * em * (κ * em) ^ P.q / (12 * P.q ! * M) := by rw [hc]; ring
      _ ≤ P.ς * ε j * δ₁ k j ^ j / (12 * P.q ! * M) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ P.ς * ε j * δ₁ k j ^ j / (12 * j ! * M) :=
          div_le_div_of_nonneg_left hN (by positivity) (by gcongr)
      _ = P.ς * ε j * δ₁ k j ^ j / j ! / 4 / (3 * M) := by field_simp; ring
      _ ≤ 2 * Lb * ‖s k‖ / (3 * M) := div_le_div_of_nonneg_right hlow (by positivity)
      _ ≤ 3 * M * ‖s k‖ / (3 * M) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hLbM (norm_nonneg _))
            (by positivity)
      _ = ‖s k‖ := by field_simp
  obtain ⟨hi1, hip⟩ := Finset.mem_Icc.1 hi
  have hcp : c ^ P.p ≤ ‖s k‖ ^ (P.p - i + 1) :=
    (pow_le_pow_of_le_one hc0 hc1 (by omega)).trans (pow_le_pow_left₀ hc0 hsc _)
  calc h k i ≤ P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * M)) ^ P.p * em ^ (P.p * (P.q + 1)) :=
        hh i hi
    _ = P.κs * c ^ P.p := by rw [hc, mul_pow, ← pow_mul, mul_assoc, mul_comm (P.q + 1) P.p]
    _ ≤ P.κs * ‖s k‖ ^ (P.p - i + 1) := mul_le_mul_of_nonneg_left hcp P.κs_pos.le

end ARStep

/-! ### Step-length algebra for ARqpIDA and ARqpEDA -/

section StepLength

/-- `(t^m)^{r/m} = t^r` for `t ≥ 0`, `m ≠ 0`. -/
theorem pow_rpow_div {t : ℝ} {m : ℕ} (hm : m ≠ 0) (ht : 0 ≤ t) (r : ℝ) :
    (t ^ m) ^ (r / (m : ℝ)) = t ^ r := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  congr 1
  field_simp

/-- The constant `κ̂ = min(κ, a/(2 q! A))` replacing `κ_{δ,min}` in the step-length bounds for
`q > 2` (Lemmas 13.1.17, 13.1.18). -/
noncomputable def arKappaHat (q : ℕ) (a A κ : ℝ) : ℝ := min κ (a / (2 * q ! * A))

/-- **The step-length bound of Lemma 13.1.17** ([cartis2022evaluation], via Lemma 12.2.12),
from the radius inequality (13.1.79), in the unit-radius mode (`u`, where `δ = 1`) or the
lower-bound mode (`¬ u`): let `a, A > 0`, `ε > 0`, `t ∈ (0, 1)`, `δ > 0`, `j ∈ [1, q]`, `q ≤ p`,
`κ > 0` with `κ ε ≤ δ`, and `δ = 1` if `u`. If
`a ε δ^j/j! ≤ A ∑_{ℓ=1}^j δ^ℓ/ℓ! t^{p-ℓ+1}`, then `a/(2 j! A) ε ≤ t^{p-j+1}` if `u`, and
`a/(2 j! A) κ̂^{j-1} ε^j ≤ t^p` with `κ̂ = min(κ, a/(2 q! A))` if `¬ u`. (The book's cases are
`u = (q ≤ 2)`.) -/
theorem arqp_pow_ge_of_radius_ineq {a A t ε δ κ : ℝ} {j p q : ℕ} {u : Prop} (ha : 0 < a)
    (hA : 0 < A) (hε : 0 < ε) (ht : 0 < t) (ht1 : t < 1) (hδ : 0 < δ) (hj : j ∈ Finset.Icc 1 q)
    (hqp : q ≤ p) (hκ : 0 < κ) (hκε : κ * ε ≤ δ) (hu : u → δ = 1)
    (hineq : a * ε * δ ^ j / j ! ≤ A * ∑ ℓ ∈ Finset.Icc 1 j, δ ^ ℓ / ℓ ! * t ^ (p - ℓ + 1)) :
    (u → a / (2 * j ! * A) * ε ≤ t ^ (p - j + 1)) ∧
      (¬ u → a / (2 * j ! * A) * arKappaHat q a A κ ^ (j - 1) * ε ^ j ≤ t ^ p) := by
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hjp : j ≤ p := hjq.trans hqp
  have hM : MeasureIneq A 0 a ε δ t j p := by
    rw [measureIneq_iff, zero_mul, add_zero]; exact hineq
  have hfj : (0 : ℝ) < j ! := by positivity
  refine ⟨fun hq => ?_, fun _ => ?_⟩
  · have h1 := hM.div_le_of_le hA.le le_rfl ht (by rw [hu hq]; exact ht1.le) hjp
    rw [add_zero] at h1
    calc a / (2 * j ! * A) * ε = a * ε / j ! / (2 * A) := by field_simp
      _ ≤ t ^ (p - j + 1) := by rw [div_le_iff₀ (by positivity)]; linarith
  · have h1 := pow_ge_of_measure_ineq hM hA ha hε ht ht1.le hδ hj1 hjp hκ hκε
    refine le_trans ?_ h1
    have hfq : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hjq
    have hk1 : arKappaHat q a A κ ≤ min κ (a / (A * j !) / 2) := by
      refine min_le_min le_rfl ?_
      rw [div_div, mul_comm (A * j !) 2, ← mul_assoc, mul_right_comm 2 A]
      exact div_le_div_of_nonneg_left ha.le (by positivity) (by gcongr)
    have hk0 : 0 ≤ arKappaHat q a A κ := le_min hκ.le (by positivity)
    have : a / (2 * j ! * A) = a / (A * j !) / 2 := by field_simp
    rw [this]
    gcongr

/-- The exponent `π_j` of Lemma 13.1.18 in the radii mode `u` (`RadiiControlOf`):
`(p+1)/(p-j+1)` with unit radii (`u`) and `j(p+1)/p` with the lower-bound radii (`¬ u`). -/
noncomputable def arPiOf (u : Prop) [Decidable u] (p j : ℕ) : ℝ :=
  if u then ((p : ℝ) + 1) / ((p - j + 1 : ℕ) : ℝ) else (j : ℝ) * ((p : ℝ) + 1) / p

/-- The exponent `π_j` of Lemma 13.1.18: `(p+1)/(p-j+1)` if `q ≤ 2`, `j(p+1)/p` if `q > 2`. -/
noncomputable def arPi (q p j : ℕ) : ℝ := arPiOf (q ≤ 2) p j

/-- The step-length constant of Lemma 13.1.18 in the radii mode `u`:
`(a/(2 q! A))^{(p+1)/(p-q+1)}` with unit radii (`u`), and `(a κ̂^{q-1}/(2 q! A))^{q(p+1)/p}` with
`κ̂ = arKappaHat q a A κ` with the lower-bound radii (`¬ u`). -/
noncomputable def arStepConstOf (u : Prop) [Decidable u] (q p : ℕ) (a A κ : ℝ) : ℝ :=
  if u then (a / (2 * q ! * A)) ^ (((p : ℝ) + 1) / ((p - q + 1 : ℕ) : ℝ))
  else (a * arKappaHat q a A κ ^ (q - 1) / (2 * q ! * A)) ^ ((q : ℝ) * ((p : ℝ) + 1) / p)

/-- The step-length constant of Lemma 13.1.18: `(a/(2 q! A))^{(p+1)/(p-q+1)}` if `q ≤ 2`, and
`(a κ̂^{q-1}/(2 q! A))^{q(p+1)/p}` with `κ̂ = arKappaHat q a A κ` if `q > 2`. -/
noncomputable def arStepConst (q p : ℕ) (a A κ : ℝ) : ℝ := arStepConstOf (q ≤ 2) q p a A κ

theorem arStepConstOf_nonneg {u : Prop} [Decidable u] {q p : ℕ} {a A κ : ℝ} (ha : 0 ≤ a)
    (hA : 0 ≤ A) (hκ : 0 ≤ κ) : 0 ≤ arStepConstOf u q p a A κ := by
  unfold arStepConstOf
  have : 0 ≤ arKappaHat q a A κ := le_min hκ (by positivity)
  split_ifs <;> positivity

theorem arStepConstOf_pos {u : Prop} [Decidable u] {q p : ℕ} {a A κ : ℝ} (ha : 0 < a)
    (hA : 0 < A) (hκ : 0 < κ) : 0 < arStepConstOf u q p a A κ := by
  unfold arStepConstOf
  have : 0 < arKappaHat q a A κ := lt_min hκ (by positivity)
  split_ifs <;> positivity

theorem arPiOf_nonneg {u : Prop} [Decidable u] {p j : ℕ} : 0 ≤ arPiOf u p j := by
  unfold arPiOf; split_ifs <;> positivity

theorem arStepConst_nonneg {q p : ℕ} {a A κ : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hκ : 0 ≤ κ) :
    0 ≤ arStepConst q p a A κ :=
  arStepConstOf_nonneg ha hA hκ

theorem arStepConst_pos {q p : ℕ} {a A κ : ℝ} (ha : 0 < a) (hA : 0 < A) (hκ : 0 < κ) :
    0 < arStepConst q p a A κ :=
  arStepConstOf_pos ha hA hκ

theorem arPi_nonneg {q p j : ℕ} : 0 ≤ arPi q p j := arPiOf_nonneg

/-- **From step lengths to decrements** ([cartis2022evaluation], proof of Lemma 13.1.18): with
`0 < a ≤ 1`, `A ≥ 1`, `0 < κ ≤ 1`, `ε ∈ (0, 1]`, `j ∈ [1, q]`, `q ≤ p`, `t > 0`, if either
`t ≥ 1` or the bounds of `arqp_pow_ge_of_radius_ineq` (in the radii mode `u`) hold, then
`arStepConstOf u q p a A κ · ε^{π_j} ≤ t^{p+1}` with `π_j = arPiOf u p j`. -/
theorem arqp_pow_succ_ge {a A t ε κ : ℝ} {j p q : ℕ} {u : Prop} [Decidable u] (ha : 0 < a)
    (ha1 : a ≤ 1) (hA : 1 ≤ A) (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 < t) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hj : j ∈ Finset.Icc 1 q) (hqp : q ≤ p)
    (hb : 1 ≤ t ∨ ((u → a / (2 * j ! * A) * ε ≤ t ^ (p - j + 1)) ∧
      (¬ u → a / (2 * j ! * A) * arKappaHat q a A κ ^ (j - 1) * ε ^ j ≤ t ^ p))) :
    arStepConstOf u q p a A κ * ε ^ arPiOf u p j ≤ t ^ (p + 1) := by
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hfj : (1 : ℝ) ≤ j ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have hfq : (j ! : ℝ) ≤ q ! := by exact_mod_cast Nat.factorial_le hjq
  set κh := arKappaHat q a A κ
  have hκh0 : 0 < κh := lt_min hκ (by positivity)
  have hκh1 : κh ≤ 1 := (min_le_left _ _).trans hκ1
  have hbq0 : 0 < a / (2 * q ! * A) := by positivity
  have hbqj : a / (2 * q ! * A) ≤ a / (2 * j ! * A) :=
    div_le_div_of_nonneg_left ha.le (by positivity) (by gcongr)
  have hbj1 : a / (2 * j ! * A) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hbq1 : a / (2 * q ! * A) ≤ 1 := hbqj.trans hbj1
  have hπ := arPiOf_nonneg (u := u) (p := p) (j := j)
  have hC0 := arStepConstOf_nonneg (u := u) (q := q) (p := p) ha.le hA0.le hκ.le
  have hepi : ε ^ arPiOf u p j ≤ 1 := Real.rpow_le_one hε.le hε1 hπ
  have hC1 : arStepConstOf u q p a A κ ≤ 1 := by
    unfold arStepConstOf
    split_ifs
    · exact Real.rpow_le_one hbq0.le hbq1 (by positivity)
    · refine Real.rpow_le_one (by positivity) ?_ (by positivity)
      rw [mul_div_right_comm]
      exact mul_le_one_of_le_one hbq1 (by positivity) (pow_le_one₀ hκh0.le hκh1)
  rcases hb with ht1 | ⟨hq2, hq3⟩
  · exact (mul_le_one_of_le_one hC1 (by positivity) hepi).trans (one_le_pow₀ ht1)
  by_cases hq : u
  · have hX := hq2 hq
    simp only [arStepConstOf, arPiOf, hq, ↓reduceIte]
    set m := p - j + 1 with hm
    have hm0 : m ≠ 0 := by omega
    set π := ((p : ℝ) + 1) / (m : ℝ)
    have hππ : π ≤ ((p : ℝ) + 1) / ((p - q + 1 : ℕ) : ℝ) := by
      refine div_le_div_of_nonneg_left (by positivity) (by
        have : 0 < p - q + 1 := by omega
        exact_mod_cast this) ?_
      exact_mod_cast (show p - q + 1 ≤ m by omega)
    have hπ0 : 0 ≤ π := by positivity
    calc (a / (2 * q ! * A)) ^ (((p : ℝ) + 1) / ((p - q + 1 : ℕ) : ℝ)) * ε ^ π
        ≤ (a / (2 * q ! * A)) ^ π * ε ^ π :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hbq0 hbq1 hππ)
            (by positivity)
      _ ≤ (a / (2 * j ! * A)) ^ π * ε ^ π := by
          gcongr
      _ = (a / (2 * j ! * A) * ε) ^ π := (Real.mul_rpow (by positivity) hε.le).symm
      _ ≤ (t ^ m) ^ π := Real.rpow_le_rpow (by positivity) hX hπ0
      _ = t ^ ((p : ℝ) + 1) := pow_rpow_div hm0 ht.le _
      _ = t ^ (p + 1) := by rw [← Real.rpow_natCast]; push_cast; ring_nf
  · have hX := hq3 hq
    simp only [arStepConstOf, arPiOf, hq, ↓reduceIte]
    have hp0 : p ≠ 0 := by omega
    have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp0
    set B := a / (2 * j ! * A) * κh ^ (j - 1)
    set Bq := a * κh ^ (q - 1) / (2 * q ! * A)
    have hBq0 : 0 < Bq := by positivity
    have hBqB : Bq ≤ B := by
      rw [show Bq = a / (2 * q ! * A) * κh ^ (q - 1) by ring]
      exact mul_le_mul hbqj (pow_le_pow_of_le_one hκh0.le hκh1 (by omega)) (by positivity)
        (by positivity)
    have hBq1 : Bq ≤ 1 := by
      rw [show Bq = a / (2 * q ! * A) * κh ^ (q - 1) by ring]
      exact mul_le_one_of_le_one hbq1 (by positivity) (pow_le_one₀ hκh0.le hκh1)
    have he : ((p : ℝ) + 1) / p ≤ (q : ℝ) * ((p : ℝ) + 1) / p := by
      rw [mul_div_assoc]
      exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast (by omega : 1 ≤ q))
    have hεpow : (ε ^ j) ^ (((p : ℝ) + 1) / p) = ε ^ ((j : ℝ) * ((p : ℝ) + 1) / p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, mul_div_assoc]
    calc Bq ^ ((q : ℝ) * ((p : ℝ) + 1) / p) * ε ^ ((j : ℝ) * ((p : ℝ) + 1) / p)
        ≤ Bq ^ (((p : ℝ) + 1) / p) * ε ^ ((j : ℝ) * ((p : ℝ) + 1) / p) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hBq0 hBq1 he)
            (by positivity)
      _ ≤ B ^ (((p : ℝ) + 1) / p) * (ε ^ j) ^ (((p : ℝ) + 1) / p) := by
          rw [hεpow]; gcongr
      _ = (B * ε ^ j) ^ (((p : ℝ) + 1) / p) :=
          (Real.mul_rpow (by positivity) (by positivity)).symm
      _ ≤ (t ^ p) ^ (((p : ℝ) + 1) / p) := Real.rpow_le_rpow (by positivity) hX (by positivity)
      _ = t ^ ((p : ℝ) + 1) := pow_rpow_div hp0 ht.le _
      _ = t ^ (p + 1) := by rw [← Real.rpow_natCast]; push_cast; ring_nf

end StepLength

/-! ### ARqpIDA runs -/

/-- The ratio (13.1.58) of ARqpIDA: `ρ_k = (f(x_k) - f(x_k + s_k)) / \overline{ΔT}_{f,p}(x_k, s_k)`
with exact function values. -/
noncomputable def arqpIDARatio (f : ℝⁿ → ℝ) (P : ARqpIDAParams)
    (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (x s : ℕ → ℝⁿ) (k : ℕ) : ℝ :=
  reductionRatio f (x k) (s k) ((D k).taylorDecrement P.p (s k))

/-- The test of approximate optimality used for ARqpIDA (not observable by the method,
[cartis2022evaluation], Theorem 13.1.19): `x_k` is an `(ε, δ)`-approximate `q`-th order minimizer
((12.1.25)) for *some* radii `δ ∈ (0, 1]^q`. -/
def arTest (f : ℝⁿ → ℝ) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (k : ℕ) : Prop :=
  ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 P.q, δ' j ∈ Set.Ioc 0 1) ∧
    IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε δ'

/-- The test of approximate optimality used for ARqpIDA-SC ([cartis2022evaluation], §14.2,
(14.2.2)): `x_k` is an `(ε, δ)`-approximate `q`-th order minimizer of `f` on the feasible set `X`
(measures over `{e | x_k + e ∈ X}`) for *some* radii `δ ∈ (0, 1]^q`. With `X = univ` this is
`arTest` (`arTest_feasible_univ`). -/
def arTest_feasible (f : ℝⁿ → ℝ) (X : Set ℝⁿ) (P : ARqpIDAParams) (ε : ℕ → ℝ) (x : ℕ → ℝⁿ)
    (k : ℕ) : Prop :=
  ∃ δ' : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 P.q, δ' j ∈ Set.Ioc 0 1) ∧
    IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε δ'

theorem arTest_feasible_univ {f : ℝⁿ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x : ℕ → ℝⁿ} :
    arTest_feasible f univ P ε x = arTest f P ε x := by
  funext k; simp only [arTest_feasible, arTest, setOf_add_mem_univ]

/-- **Algorithm 13.1.2 with a feasible set** (ARqpIDA-SC, [cartis2022evaluation] §14.2) as a run
predicate: as `algorithm_13_1_2`, for a feasible set `X` (closedness is not used by the analysis)
and a feasible starting point `x₀ ∈ X`, every iteration satisfying `ARqpDAStep` on `X` (feasible
Step-1 displacements, trial points and Step-2 displacements). With `X = univ` this is
`algorithm_13_1_2`. -/
structure algorithm_13_1_2_feasible (f : ℝⁿ → ℝ) (X : Set ℝⁿ) (κg : ℕ → ℝ) (P : ARqpIDAParams)
    (ε : ℕ → ℝ) (x₀ : ℝⁿ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
    (acc : ℕ → Prop) : Prop where
  /-- `ε ∈ (0, 1]^q`. -/
  eps_mem : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1
  /-- `ε_j ≤ δ_{0,j}` (13.1.51). -/
  eps_le : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j
  /-- `κ_{∇,i} ≥ 0`. -/
  κg_nonneg : ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ κg i
  /-- The starting point. -/
  x_zero : x 0 = x₀
  /-- The starting point is feasible. -/
  x₀_mem : x₀ ∈ X
  /-- The initial regularization parameter. -/
  σ_zero : σ 0 = P.σ₀
  /-- The initial radii. -/
  δ_zero : δ 0 = P.δ₀
  /-- The initial accuracies. -/
  h_zero : h 0 = P.h₀
  /-- The error model (13.1.2) for `i ∈ [1, p]`. -/
  oracle : ∀ k, JetApprox (ftaylorSeries ℝ f (x k)) (D k) P.p (fun i => κg i * h k i)
  /-- Steps 1–5. -/
  step : ∀ k, ARqpDAStep X P ε x σ δ δ₁ δs h D dd jk s acc (arqpIDARatio f P D x s) k

/-- **Algorithm 13.1.2** (ARqpIDA) of [cartis2022evaluation] as a run predicate, for the
objective `f`, the (unknown) oracle constants `κ_{∇,i} ≥ 0`, constants `P`, tolerances
`ε ∈ (0, 1]^q` with `ε ≤ δ₀`, starting point `x₀`, and sequences of iterates `x`, regularization
parameters `σ`, radii `δ, δ₁, δs` (`δ^{(0)}_k, δ^{(1)}_k, δ_{s_k}`), requested accuracies `h`,
inexact jets `D` satisfying (13.1.2) up to order `p`, Step-1 displacements `dd`, orders `j_k`,
steps `s` and accuracy-improving flags `acc`; every iteration satisfies `ARqpDAStep` with the
exact-value ratio (13.1.58). The method has no termination rule; see `arTest`. This is
`algorithm_13_1_2_feasible` with the feasible set `X = univ`. -/
abbrev algorithm_13_1_2 (f : ℝⁿ → ℝ) (κg : ℕ → ℝ) (P : ARqpIDAParams) (ε : ℕ → ℝ)
    (x₀ : ℝⁿ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
    (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
    (acc : ℕ → Prop) : Prop :=
  algorithm_13_1_2_feasible f univ κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc

namespace algorithm_13_1_2_feasible

variable {f : ℝⁿ → ℝ} {X : Set ℝⁿ} {κg : ℕ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ}
  {acc : ℕ → Prop}
  (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
include hrun

theorem invariants (k : ℕ) :
    P.σmin ≤ σ k ∧ (∀ j ∈ Finset.Icc 1 P.q, 0 < δ k j ∧ δ k j ≤ 1) ∧
      ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ h k i ∧ h k i ≤ P.κh :=
  arqp_invariants (fun i _ => hrun.step i) hrun.σ_zero hrun.δ_zero hrun.h_zero

theorem sigma_pos (k : ℕ) : 0 < σ k := P.σmin_pos.trans_le (hrun.invariants k).1

theorem epsMin_pos : 0 < epsMin P.q ε :=
  Chapter13.epsMin_pos P.one_le_q fun j hj => (hrun.eps_mem j hj).1

theorem epsMin_le_one : epsMin P.q ε ≤ 1 :=
  Chapter13.epsMin_le_one P.one_le_q fun j hj => (hrun.eps_mem j hj).2

theorem kappaMax_nonneg : 0 ≤ ordMax P.p κg := ordMax_nonneg hrun.κg_nonneg

/-- The iterates are feasible. -/
theorem mem (k : ℕ) : x k ∈ X :=
  arqp_mem (fun i _ => hrun.step i) (hrun.x_zero ▸ hrun.x₀_mem)

/-- The objective does not increase along an ARqpIDA-SC run: `f(x_k) ≤ f(x₀)` (the ratio uses
exact function values and the predicted decrease of a trial iteration is positive,
Lemma 13.1.13). -/
theorem f_le (k : ℕ) : f (x k) ≤ f x₀ := by
  rw [← hrun.x_zero]
  refine le_zero_of_succ_le (u := fun i => f (x i)) fun i _ => ?_
  by_cases ha : acc i
  · simp only [(hrun.step i).x_acc ha, le_rfl]
  · exact ((hrun.step i).accept ha).le (w := f) rfl (lemma_13_1_13 (hrun.step i) ha
      (fun j hj => (hrun.eps_mem j hj).1) (hrun.sigma_pos i).le).2

/-- The iterates lie in every set `A` containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}`. -/
theorem mem_anchor {A : Set ℝⁿ} (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) (k : ℕ) : x k ∈ A :=
  hAX _ (hrun.mem k) (hrun.f_le k)

/-- (13.1.63): `‖∇̄^i f(x_k)‖ ≤ L̄_f = L_f + κ_{∇,max} κ_h` for `i ∈ [1, p]`, under f.D0pL
anchored on a set `A` containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}`. -/
theorem norm_D_le_anchored {C A : Set ℝⁿ} {L : ℕ → ℝ} (hf : AssumptionD0pLAnchored f C A P.p L)
    (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) (k : ℕ) {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p) :
    ‖D k i‖ ≤ lipMax L P.p + ordMax P.p κg * P.κh :=
  hf.norm_le_of_jetApprox (hrun.mem_anchor hAX k) (hrun.oracle k) hrun.κg_nonneg
    (fun i hi => ((hrun.invariants k).2.2 i hi).1) (fun i hi => ((hrun.invariants k).2.2 i hi).2) hi

/-- (13.1.63): `‖∇̄^i f(x_k)‖ ≤ L̄_f = L_f + κ_{∇,max} κ_h` for `i ∈ [1, p]`, under f.D0pL on
`C ⊇ X`. -/
theorem norm_D_le {C : Set ℝⁿ} {L : ℕ → ℝ} (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (k : ℕ) {i : ℕ} (hi : i ∈ Finset.Icc 1 P.p) :
    ‖D k i‖ ≤ lipMax L P.p + ordMax P.p κg * P.κh :=
  hrun.norm_D_le_anchored (hf.anchored hXC) (fun _ hy _ => hy) k hi

theorem one_le_Lbar {C : Set ℝⁿ} {L : ℕ → ℝ} (hf : AssumptionD0pLOn f C P.p L) :
    1 ≤ lipMax L P.p + ordMax P.p κg * P.κh := by
  have := hf.one_le_lipMax; have := hrun.kappaMax_nonneg; have := P.κh_nonneg; nlinarith

theorem one_le_Lbar_anchored {C A : Set ℝⁿ} {L : ℕ → ℝ}
    (hf : AssumptionD0pLAnchored f C A P.p L) : 1 ≤ lipMax L P.p + ordMax P.p κg * P.κh := by
  have := hf.one_le_lipMax; have := hrun.kappaMax_nonneg; have := P.κh_nonneg; nlinarith

end algorithm_13_1_2_feasible

section ARqpIDA

variable {X C A : Set ℝⁿ} {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : ARqpIDAParams} {ε : ℕ → ℝ} {x₀ : ℝⁿ}
  {x : ℕ → ℝⁿ} {σ : ℕ → ℝ} {δ δ₁ δs : ℕ → ℕ → ℝ} {h : ℕ → ℕ → ℝ}
  {D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ} {dd : ℕ → ℕ → ℝⁿ} {jk : ℕ → ℕ} {s : ℕ → ℝⁿ}
  {acc : ℕ → Prop} {L : ℕ → ℝ} {k : ℕ}

/-- **Lemma 13.1.12 under the anchored assumption** ([cartis2022evaluation] §14.2): the conclusions
of `lemma_13_1_12` for an ARqpIDA-SC run (`algorithm_13_1_2_feasible`) under f.D0pL anchored on a
set `A` containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}` (`AssumptionD0pLAnchored`), for either
mode `u` of the radii control (`RadiiControlOf`). -/
theorem lemma_13_1_12_anchored (hf : AssumptionD0pLAnchored f C A P.p L)
    (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i < k, RadiiControlOf u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    {σbar : ℝ} (hσ : ∀ i ≤ k, σ i ≤ σbar) :
    ((∃ j ∈ Finset.Icc 1 P.q, ¬ arPass P ε D δ₁ dd k j) →
        0 < P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ∧
        P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ≤ arModelDec P D σ k (s k) ∧
        s k ≠ 0) ∧
      (∀ j ∈ Finset.Icc 1 P.q,
        arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh) σbar * ε j ≤ δ₁ k j ∧
          δ₁ k j ≤ δ k j) ∧
      ((∃ j ∈ Finset.Icc 1 P.q, ¬ arPass P ε D δ₁ dd k j) →
        (∀ i ∈ Finset.Icc 1 P.p, h k i ≤
          P.κs * (P.ς * arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh) σbar ^ P.q /
            (12 * P.q ! * max (lipMax L P.p + ordMax P.p κg * P.κh) σbar)) ^ P.p *
            epsMin P.q ε ^ (P.p * (P.q + 1))) → ¬ acc k) := by
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  have hLb := hrun.one_le_Lbar_anchored hf
  have hrad := arqp_radius_ge (fun i _ => hrun.step i) (hrun.step k).toARqpStep1 hrun.σ_zero
    hrun.δ_zero hrun.h_zero
    hrun.eps_mem hrun.eps_le hLb (fun i _ ℓ hℓ => hrun.norm_D_le_anchored hf hAX i hℓ) hσ hrc
  refine ⟨fun hb => ?_, hrad, fun hb hh => ?_⟩
  · have h2 := (hrun.step k).step2 hb
    have hpos : 0 < P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 := by
      have := P.ς_pos; have := (hrun.eps_mem _ h2.jk_mem).1
      have := (hrun.step k).radius_pos _ h2.jk_mem; positivity
    have hm := h2.model_dec.trans h2.dec_le
    refine ⟨hpos, hm, fun h0 => ?_⟩
    rw [h0, arModelDec, sub_self] at hm
    linarith
  · have h2 := (hrun.step k).step2 hb
    exact h2.not_acc_of_le ((hrun.step k).radius_pos) hLb
      (fun i hi => hrun.norm_D_le_anchored hf hAX k hi)
      (hrun.sigma_pos k).le (arKappaDelta1_pos (by linarith)).le
      (arKappaDelta1_le_one hLb) hrun.eps_mem (fun j hj => (hrad j hj).1) hh

/-- **Lemma 13.1.12 with a feasible set** ([cartis2022evaluation] §14.2): the conclusions of
`lemma_13_1_12` for an ARqpIDA-SC run (`algorithm_13_1_2_feasible`) under f.D0pL on an open convex
`C ⊇ X`, for either mode `u` of the radii control (`RadiiControlOf`). -/
theorem lemma_13_1_12_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i < k, RadiiControlOf u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    {σbar : ℝ} (hσ : ∀ i ≤ k, σ i ≤ σbar) :
    ((∃ j ∈ Finset.Icc 1 P.q, ¬ arPass P ε D δ₁ dd k j) →
        0 < P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ∧
        P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ≤ arModelDec P D σ k (s k) ∧
        s k ≠ 0) ∧
      (∀ j ∈ Finset.Icc 1 P.q,
        arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh) σbar * ε j ≤ δ₁ k j ∧
          δ₁ k j ≤ δ k j) ∧
      ((∃ j ∈ Finset.Icc 1 P.q, ¬ arPass P ε D δ₁ dd k j) →
        (∀ i ∈ Finset.Icc 1 P.p, h k i ≤
          P.κs * (P.ς * arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh) σbar ^ P.q /
            (12 * P.q ! * max (lipMax L P.p + ordMax P.p κg * P.κh) σbar)) ^ P.p *
            epsMin P.q ε ^ (P.p * (P.q + 1))) → ¬ acc k) :=
  lemma_13_1_12_anchored (hf.anchored hXC) (fun _ hy _ => hy) hrun hrc hσ

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
    ((∃ j ∈ Finset.Icc 1 P.q, ¬ arPass P ε D δ₁ dd k j) →
        0 < P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ∧
        P.ς * ε (jk k) * δ₁ k (jk k) ^ jk k / (jk k)! / 4 ≤ arModelDec P D σ k (s k) ∧
        s k ≠ 0) ∧
      (∀ j ∈ Finset.Icc 1 P.q,
        arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh) σbar * ε j ≤ δ₁ k j ∧
          δ₁ k j ≤ δ k j) ∧
      ((∃ j ∈ Finset.Icc 1 P.q, ¬ arPass P ε D δ₁ dd k j) →
        (∀ i ∈ Finset.Icc 1 P.p, h k i ≤
          P.κs * (P.ς * arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh) σbar ^ P.q /
            (12 * P.q ! * max (lipMax L P.p + ordMax P.p κg * P.κh) σbar)) ^ P.p *
            epsMin P.q ε ^ (P.p * (P.q + 1))) → ¬ acc k) :=
  lemma_13_1_12_feasible hf.on_univ (subset_univ _) hrun hrc hσ

/-! ### Lemma 13.1.14 -/

/-- The bound `σ_max = max(σ₀, γ₃ (2 L_{f,p} + 4 (p+1)! κ_s' κ_{∇,max})/(1 - η₂))` of (13.1.77),
with `κ_s' = max(κ_s, κ_h)` (corrected; the book has `κ_s`). -/
noncomputable def arSigmaMax (P : ARqpIDAParams) (Lp κm : ℝ) : ℝ :=
  max P.σ₀ (P.γ₃ * ((2 * Lp + 4 * (P.p + 1)! * max P.κs P.κh * κm) / (1 - P.η₂)))

/-- **Lemma 13.1.14 under the anchored assumption** ([cartis2022evaluation] §14.2): `σ_k ≤ σ_max`
for an ARqpIDA-SC run under f.D0pL anchored on a set `A` containing the sublevel set
`{y ∈ X | f(y) ≤ f(x₀)}` (`AssumptionD0pLAnchored`). -/
theorem lemma_13_1_14_anchored (hf : AssumptionD0pLAnchored f C A P.p L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) (k : ℕ) :
    σ k ≤ arSigmaMax P (L P.p) (ordMax P.p κg) := by
  set κm := ordMax P.p κg
  set κs' := max P.κs P.κh
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  have hκs' : 0 ≤ κs' := P.κs_pos.le.trans (le_max_left _ _)
  have hLp : 1 ≤ L P.p := hf.one_le le_rfl
  set σbar := (2 * L P.p + 4 * (P.p + 1)! * κs' * κm) / (1 - P.η₂)
  have key : ∀ k, ¬ acc k → σbar ≤ σ k → P.η₂ ≤ arqpIDARatio f P D x s k := by
    intro k hk hσk
    have hs := hrun.step k
    have h2 := hs.step2_of_not_acc hk
    obtain ⟨hlow, hpos⟩ := lemma_13_1_13 hs hk (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos k).le
    set t := ‖s k‖
    have hherr : ∀ i ∈ Finset.Icc 1 P.p, κg i * h k i ≤ κm * κs' * t ^ (P.p - i + 1) := by
      intro i hi
      have hhi : h k i ≤ κs' * t ^ (P.p - i + 1) := by
        rcases lt_or_ge t 1 with ht | ht
        · exact (h2.h_le_of_not_acc hk ht i hi).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        · exact (((hrun.invariants k).2.2 i hi).2.trans (le_max_right _ _)).trans
            (le_mul_of_one_le_right hκs' (one_le_pow₀ ht))
      rw [mul_assoc]
      exact mul_le_mul (le_ordMax hi) hhi ((hrun.invariants k).2.2 i hi).1 hκm
    have hE := abs_taylorDecrement_sub_le_of_stepAccuracy hκm hκs' (hrun.oracle k) hherr le_rfl
    have hR := hf.abs_sub_le le_rfl (hrun.mem_anchor hAX k) (hXC h2.mem)
    have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
    have hσbar : (2 * L P.p + 4 * (P.p + 1)! * κs' * κm) ≤ (1 - P.η₂) * σ k := by
      have := (div_le_iff₀' P.one_sub_η₂_pos).1 hσk
      linarith
    rw [arqpIDARatio, reductionRatio_def]
    refine le_div_of_inexact_error_le (fx := f (x k)) (fxs := f (x k + s k))
      (ΔT := (ftaylorSeries ℝ f (x k)).taylorDecrement P.p (s k)) hpos ?_
    rw [sub_self, sub_self, abs_zero, zero_add, add_zero]
    have htp : 0 ≤ t ^ (P.p + 1) := by positivity
    calc |f (x k + s k) - (f (x k) - (ftaylorSeries ℝ f (x k)).taylorDecrement P.p (s k))| +
          |(ftaylorSeries ℝ f (x k)).taylorDecrement P.p (s k) - (D k).taylorDecrement P.p (s k)|
        ≤ L P.p / ((P.p + 1)! : ℝ) * t ^ (P.p + 1) + 2 * κs' * κm * t ^ (P.p + 1) :=
          add_le_add hR (by rw [abs_sub_comm]; exact hE)
      _ = (L P.p + 2 * (P.p + 1)! * κs' * κm) / (P.p + 1)! * t ^ (P.p + 1) := by
          field_simp
      _ ≤ (1 - P.η₂) * σ k / (P.p + 1)! * t ^ (P.p + 1) := by
          gcongr
          have : 0 ≤ (P.p + 1)! * κs' * κm := by positivity
          linarith
      _ = (1 - P.η₂) * (σ k / ((P.p + 1)! : ℝ) * t ^ (P.p + 1)) := by ring
      _ ≤ (1 - P.η₂) * (D k).taylorDecrement P.p (s k) :=
          mul_le_mul_of_nonneg_left hlow P.one_sub_η₂_pos.le
  have h := sigma_le_max_of_arUpdate_of_neutral (σ := σ) (K := k) (σbar := σbar)
    (ρ := arqpIDARatio f P D x s) P.γ₁_pos P.γ₂_pos P.γ₂_le_γ₃ P.one_le_γ₃
    (hrun.σ_zero ▸ P.σ₀_pos) (fun i _ => by
      by_cases ha : acc i
      · exact Or.inl ((hrun.step i).σ_acc ha)
      · exact Or.inr ⟨(hrun.step i).update ha, key i ha⟩) k le_rfl
  rwa [hrun.σ_zero] at h

/-- **Lemma 13.1.14 with a feasible set** ([cartis2022evaluation] §14.2): `σ_k ≤ σ_max` for an
ARqpIDA-SC run under f.D0pL on an open convex `C ⊇ X`. -/
theorem lemma_13_1_14_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) (k : ℕ) :
    σ k ≤ arSigmaMax P (L P.p) (ordMax P.p κg) :=
  lemma_13_1_14_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hrun k

/-- **Lemma 13.1.14** ([cartis2022evaluation], corrected constant): under f.D0pL, every
ARqpIDA run satisfies `σ_k ≤ σ_max` (13.1.77) for all `k`, with `σ_max = arSigmaMax`. The book
uses `κ_s` instead of `κ_s' = max(κ_s, κ_h)`: its proof applies (13.1.47) also to long steps
`‖s_k‖ ≥ 1`, where the accuracy test (13.1.46) is not performed and only `h_{k,i} ≤ κ_h` is
known. -/
theorem lemma_13_1_14 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) (k : ℕ) :
    σ k ≤ arSigmaMax P (L P.p) (ordMax P.p κg) :=
  lemma_13_1_14_feasible hf.on_univ (subset_univ _) hrun k

/-! ### Lemmas 13.1.15 and 13.1.16 -/

/-- **Lemma 13.1.15 under the anchored assumption** ([cartis2022evaluation] §14.2): for an
ARqpIDA-SC run under f.D0pL anchored on a set `A` containing the sublevel set
`{y ∈ X | f(y) ≤ f(x₀)}` (`AssumptionD0pLAnchored`), the conclusion of `lemma_13_1_15` with the
measures over the feasible displacements `{e | x_k + e ∈ X}`, for either mode `u` of the radii
control (`RadiiControlOf`). -/
theorem lemma_13_1_15_anchored (hf : AssumptionD0pLAnchored f C A P.p L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i < k, RadiiControlOf u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, arPass P ε D δ₁ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, ordMax P.p κg * h k i ≤
      P.ς * arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arSigmaMax P (L P.p) (ordMax P.p κg)) ^ P.q / (4 * P.q !) *
        epsMin P.q ε ^ (P.q + 1)) :
    (∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε (δ₁ k) ∧
        arTest_feasible f X P ε x k := by
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  have hLb := hrun.one_le_Lbar_anchored hf
  set κ := arKappaDelta1 P Lb (arSigmaMax P (L P.p) (ordMax P.p κg))
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  have hrad := (lemma_13_1_12_anchored hf hAX hrun hrc (k := k)
    (fun i _ => lemma_13_1_14_anchored hf hXC hAX hrun i)).2.1
  have hmem : ∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1 := fun j hj =>
    ⟨(hrun.step k).radius_pos j hj, (hrad j hj).2.trans ((hrun.invariants k).2.1 j hj).2⟩
  have hεmin := hrun.epsMin_pos
  have hεmin1 := hrun.epsMin_le_one
  have hς := P.ς_pos
  have hς1 := P.ς_le_one
  have happrox : IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε (δ₁ k) := by
    intro j hj
    obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
    set em := epsMin P.q ε
    have hw := ((hrun.step k).witness j hj).2
    have hm0 : 0 ≤ κ * em := by positivity
    have hm1 : κ * em ≤ 1 := mul_le_one_of_le_one hκ1 hεmin.le hεmin1
    have hδj : (κ * em) ^ P.q ≤ δ₁ k j ^ j :=
      (pow_le_pow_of_le_one hm0 hm1 hjq).trans (pow_le_pow_left₀ hm0
        ((mul_le_mul_of_nonneg_left (epsMin_le hj) hκ0.le).trans (hrad j hj).1) j)
    have hfact : (j ! : ℝ) ≤ P.q ! := by exact_mod_cast Nat.factorial_le hjq
    have hεj : P.ς * em ≤ ε j := (mul_le_of_le_one_left hεmin.le hς1).trans (epsMin_le hj)
    refine taylorMeasure_le_of_inexact_certificate_uniform ((hrun.oracle k).mono P.q_le_p) hj
      (by simpa using hrun.mem k) (hmem j hj).1.le (hmem j hj).2 hς hw (hpass j hj)
      (e := P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1)) (fun i hi => ?_) ?_
    · have hip : i ∈ Finset.Icc 1 P.p :=
        Finset.Icc_subset_Icc le_rfl (hjq.trans P.q_le_p) hi
      exact (mul_le_mul_of_nonneg_right (le_ordMax hip) ((hrun.invariants k).2.2 i hip).1).trans
        (hh i hip)
    · calc P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1) =
            P.ς * em * (κ * em) ^ P.q / (4 * P.q !) := by ring
        _ ≤ ε j * δ₁ k j ^ j / (4 * P.q !) :=
            div_le_div_of_nonneg_right (mul_le_mul hεj hδj (pow_nonneg hm0 _)
              (hrun.eps_mem j hj).1.le) (by positivity)
        _ ≤ ε j * δ₁ k j ^ j / (4 * j !) := by
            gcongr
            exact mul_nonneg (hrun.eps_mem j hj).1.le (pow_nonneg (hmem j hj).1.le _)
  exact ⟨hmem, happrox, δ₁ k, hmem, happrox⟩

/-- **Lemma 13.1.15 with a feasible set** ([cartis2022evaluation] §14.2): for an ARqpIDA-SC run
under f.D0pL on an open convex `C ⊇ X`, the conclusion of `lemma_13_1_15` with the measures over the
feasible displacements `{e | x_k + e ∈ X}`, for either mode `u` of the radii control
(`RadiiControlOf`). -/
theorem lemma_13_1_15_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i < k, RadiiControlOf u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, arPass P ε D δ₁ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, ordMax P.p κg * h k i ≤
      P.ς * arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arSigmaMax P (L P.p) (ordMax P.p κg)) ^ P.q / (4 * P.q !) *
        epsMin P.q ε ^ (P.q + 1)) :
    (∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) {e | x k + e ∈ X} P.q ε (δ₁ k) ∧
        arTest_feasible f X P ε x k :=
  lemma_13_1_15_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hrun hrc hpass hh

/-- **Lemma 13.1.15** ([cartis2022evaluation]): under f.D0pL and the radii control at every
iteration before `k`, if Step 1 of ARqpIDA branches to Step 5 at iteration `k` ((13.1.53) at
every order) and (13.1.78) `κ_{∇,max} h_{k,i} ≤ ς κ^{(1)}_δ(σ_max)^q/(4 q!) ε_min^{q+1}` for
`i ∈ [1, p]`, then
`x_k` is an `(ε, δ^{(1)}_k)`-approximate `q`-th order minimizer with `δ^{(1)}_k ∈ (0, 1]^q` (in
particular `arTest k`). (The book writes `δ_k` for the radii `δ^{(1)}_k` at the end of Step 1.) -/
theorem lemma_13_1_15 (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : ∀ i < k, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    (hpass : ∀ j ∈ Finset.Icc 1 P.q, arPass P ε D δ₁ dd k j)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, ordMax P.p κg * h k i ≤
      P.ς * arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arSigmaMax P (L P.p) (ordMax P.p κg)) ^ P.q / (4 * P.q !) *
        epsMin P.q ε ^ (P.q + 1)) :
    (∀ j ∈ Finset.Icc 1 P.q, δ₁ k j ∈ Set.Ioc 0 1) ∧
      IsEpsDeltaApprox (ftaylorSeries ℝ f (x k)) univ P.q ε (δ₁ k) ∧ arTest f P ε x k := by
  have := lemma_13_1_15_feasible hf.on_univ (subset_univ _) hrun hrc hpass hh
  rwa [setOf_add_mem_univ, arTest_feasible_univ] at this

/-- **Lemma 13.1.16 under the anchored assumption** ([cartis2022evaluation] §14.2): for an
ARqpIDA-SC run under f.D0pL anchored on a set `A` containing the sublevel set
`{y ∈ X | f(y) ≤ f(x₀)}` (`AssumptionD0pLAnchored`), if iteration `k` is successful with `‖s_k‖ < 1`
and `x_{k+1}` is not approximately optimal on `X` for the radii `δ_{k+1}`, then (13.1.79) holds for
some `j ∈ [1, q]`. -/
theorem lemma_13_1_16_anchored (hf : AssumptionD0pLAnchored f C A P.p L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hs1 : ‖s k‖ < 1)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1))) :
    ∃ j ∈ Finset.Icc 1 P.q, (1 - P.θ) * ε j * δ (k + 1) j ^ j / j ! ≤
      (L P.p + arSigmaMax P (L P.p) (ordMax P.p κg) + 3 * ordMax P.p κg * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) := by
  have hs := hrun.step k
  have h2 := hs.step2_of_not_acc hk
  have hx : x (k + 1) = x k + s k := hs.x_succ_eq_add hk hρ
  have hδ : δ (k + 1) = δs k := by rw [hs.radii_trial hk, ite_eq_left ⟨hρ, hs1⟩]
  unfold IsEpsDeltaApprox at hnot
  push Not at hnot
  obtain ⟨j, hj, hlt⟩ := hnot
  refine ⟨j, hj, ?_⟩
  obtain ⟨hδmem, dm, hdm, hdmle⟩ := h2.radii_of_lt hs1 j hj
  rw [hx] at hlt
  rw [hδ] at hlt ⊢
  have hjp : j ≤ P.p := (Finset.mem_Icc.1 hj).2.trans P.q_le_p
  have h₂ : taylorMeasure (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) j (δs k j)
      {e | x k + s k + e ∈ X} ≤ P.θ * ε j * δs k j ^ j / j ! := by
    have hw := hdm.2
    have := hw.trans hdmle
    have hς := P.ς_pos
    rw [show P.ς * P.θ * ε j * δs k j ^ j / j ! = P.ς * (P.θ * ε j * δs k j ^ j / j !) by ring]
      at this
    exact le_of_mul_le_mul_left this hς
  have hxA := hrun.mem_anchor hAX k
  have := radius_inequality_of_measure_gt_anchored hf.convex
    (fun y hy => hf.contDiffAt le_rfl hy) (hf.lipschitzAt le_rfl hxA)
    (zero_le_one.trans (hf.one_le le_rfl)) (hf.subset hxA)
    (hXC h2.mem) (hrun.oracle k) hrun.kappaMax_nonneg P.κs_pos.le
    (fun i hi => by
      rw [mul_assoc]
      exact mul_le_mul (le_ordMax hi) (h2.h_le_of_not_acc hk hs1 i hi)
        ((hrun.invariants k).2.2 i hi).1 hrun.kappaMax_nonneg)
    (hrun.sigma_pos k).le (lemma_13_1_14_anchored hf hXC hAX hrun k) hjp (by simpa using h2.mem)
    hδmem.1.le
    (a := 1) (e₀ := 0) (by rw [one_mul, sub_zero]; exact hlt) h₂
  rw [add_zero] at this
  exact this.le

/-- **Lemma 13.1.16 with a feasible set** ([cartis2022evaluation] §14.2): for an ARqpIDA-SC run
under f.D0pL on an open convex `C ⊇ X`, if iteration `k` is successful with `‖s_k‖ < 1` and
`x_{k+1}` is not approximately optimal on `X` for the radii `δ_{k+1}`, then (13.1.79) holds for some
`j ∈ [1, q]`. -/
theorem lemma_13_1_16_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hs1 : ‖s k‖ < 1)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1))) :
    ∃ j ∈ Finset.Icc 1 P.q, (1 - P.θ) * ε j * δ (k + 1) j ^ j / j ! ≤
      (L P.p + arSigmaMax P (L P.p) (ordMax P.p κg) + 3 * ordMax P.p κg * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) :=
  lemma_13_1_16_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hrun hk hρ hs1 hnot

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
      (L P.p + arSigmaMax P (L P.p) (ordMax P.p κg) + 3 * ordMax P.p κg * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, δ (k + 1) j ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) :=
  lemma_13_1_16_feasible hf.on_univ (subset_univ _) hrun hk hρ hs1 (by rwa [setOf_add_mem_univ])

/-! ### Lemmas 13.1.17 and 13.1.18 -/

/-- The constant `L_{f,p} + σ_max + 3 κ_{∇,max} κ_s` of Lemmas 13.1.16–13.1.18. -/
noncomputable def arConstA (P : ARqpIDAParams) (L : ℕ → ℝ) (κm : ℝ) : ℝ :=
  L P.p + arSigmaMax P (L P.p) κm + 3 * κm * P.κs

theorem one_le_arConstA {P : ARqpIDAParams} {L : ℕ → ℝ} {κm : ℝ} (hL : 1 ≤ L P.p)
    (hκm : 0 ≤ κm) : 1 ≤ arConstA P L κm := by
  have h1 : 0 ≤ arSigmaMax P (L P.p) κm := P.σ₀_pos.le.trans (le_max_left _ _)
  have h2 : 0 ≤ 3 * κm * P.κs := by have := P.κs_pos; positivity
  unfold arConstA; linarith

/-- `κ^{(1)}_δ(σ') ε ≤ ς θ ε/(24 max(L̄, σ))` for `σ ≤ σ'`. -/
theorem arKappaDelta1_mul_le {P : ARqpIDAParams} {Lb σ σ' e : ℝ} (hLb : 0 < Lb) (hσ : σ ≤ σ')
    (he : 0 ≤ e) : arKappaDelta1 P Lb σ' * e ≤ P.ς * P.θ * e / (24 * max Lb σ) := by
  have := P.ς_pos; have := P.θ_pos
  have hM : 0 < max Lb σ := lt_max_of_lt_left hLb
  have hM' : max Lb σ ≤ max Lb σ' := max_le_max le_rfl hσ
  rw [arKappaDelta1, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- `arqpIDA_step_bound` for an ARqpIDA-SC run under f.D0pL anchored on a set `A` containing the
sublevel set `{y ∈ X | f(y) ≤ f(x₀)}` (`AssumptionD0pLAnchored`), for either mode `u` of the radii
control (`RadiiControlOf`): the case `q ≤ 2` of `arqpIDA_step_bound` becomes the unit-radius mode
`u`, the case `q > 2` the lower-bound mode `¬ u`. -/
theorem arqpIDA_step_bound_anchored (hf : AssumptionD0pLAnchored f C A P.p L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : RadiiControlOf u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1))) :
    ∃ j ∈ Finset.Icc 1 P.q, 1 ≤ ‖s k‖ ∨
      ((u → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) * ε j ≤
          ‖s k‖ ^ (P.p - j + 1)) ∧
        (¬ u → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) *
          arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
            (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) * ε j ^ j ≤ ‖s k‖ ^ P.p)) := by
  rcases le_or_gt 1 ‖s k‖ with hs1 | hs1
  · exact ⟨1, P.one_mem_Icc, Or.inl hs1⟩
  obtain ⟨j, hj, hineq⟩ := lemma_13_1_16_anchored hf hXC hAX hrun hk hρ hs1 hnot
  refine ⟨j, hj, Or.inr ?_⟩
  have hs := hrun.step k
  have h2 := hs.step2_of_not_acc hk
  have hδ : δ (k + 1) = δs k := by rw [hs.radii_trial hk, ite_eq_left ⟨hρ, hs1⟩]
  rw [hδ] at hineq
  have hLb := hrun.one_le_Lbar_anchored hf
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  set κ := arKappaDelta1 P Lb (arSigmaMax P (L P.p) (ordMax P.p κg))
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hεj := hrun.eps_mem j hj
  have hδpos := (h2.radii_of_lt hs1 j hj).1.1
  have hκε : κ * ε j ≤ δs k j :=
    hrc.kappa_mul_le hk hs1 hrun.eps_mem hLb (lemma_13_1_14_anchored hf hXC hAX hrun k) hj
  have hq2 : u → δs k j = 1 := fun hu => (hrc hk hs1).1 hu j hj
  have ht : 0 < ‖s k‖ := by
    have hpos := (lemma_13_1_13 hs hk (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos k).le).2
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hA : 0 < arConstA P L (ordMax P.p κg) := by
    have := hf.one_le le_rfl
    have : 0 ≤ arSigmaMax P (L P.p) (ordMax P.p κg) := (P.σ₀_pos.le).trans (le_max_left _ _)
    have := hrun.kappaMax_nonneg; have := P.κs_pos
    unfold arConstA; positivity
  exact arqp_pow_ge_of_radius_ineq (sub_pos.2 P.θ_lt_one) hA hεj.1 ht hs1 hδpos hj P.q_le_p
    hκ0 hκε hq2 hineq

/-- `arqpIDA_step_bound` for an ARqpIDA-SC run under f.D0pL on an open convex `C ⊇ X`, for
either mode `u` of the radii control (`RadiiControlOf`): the case `q ≤ 2` of `arqpIDA_step_bound`
becomes the unit-radius mode `u`, the case `q > 2` the lower-bound mode `¬ u`. -/
theorem arqpIDA_step_bound_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : RadiiControlOf u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1))) :
    ∃ j ∈ Finset.Icc 1 P.q, 1 ≤ ‖s k‖ ∨
      ((u → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) * ε j ≤
          ‖s k‖ ^ (P.p - j + 1)) ∧
        (¬ u → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) *
          arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
            (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) * ε j ^ j ≤ ‖s k‖ ^ P.p)) :=
  arqpIDA_step_bound_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hrun hrc hk hρ hnot

/-- The step-length bounds behind Lemmas 13.1.17 and 13.1.18 for ARqpIDA: at a successful
iteration `k` with the radii control at `k` and `x_{k+1}` not approximately optimal for the radii
`δ_{k+1}`, either `‖s_k‖ ≥ 1` or the conclusions of `arqp_pow_ge_of_radius_ineq` hold for some
order `j` with `a = 1 - θ`, `A = L_{f,p} + σ_max + 3 κ_{∇,max} κ_s` and `κ = κ_{δ,min}`. -/
theorem arqpIDA_step_bound (hf : AssumptionD0pL f P.p L)
    (hrun : algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hrc : RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) univ P.q ε (δ (k + 1))) :
    ∃ j ∈ Finset.Icc 1 P.q, 1 ≤ ‖s k‖ ∨
      ((P.q ≤ 2 → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) * ε j ≤
          ‖s k‖ ^ (P.p - j + 1)) ∧
        (2 < P.q → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) *
          arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
            (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) * ε j ^ j ≤ ‖s k‖ ^ P.p)) := by
  obtain ⟨j, hj, h⟩ := arqpIDA_step_bound_feasible hf.on_univ (subset_univ _) hrun hrc hk hρ
    (by rwa [setOf_add_mem_univ])
  exact ⟨j, hj, h.imp_right fun h => ⟨h.1, fun hq => h.2 (not_le.2 hq)⟩⟩

/-- **Lemma 13.1.17 under the anchored assumption** ([cartis2022evaluation] §14.2): the step-length
bounds (13.1.80) of `lemma_13_1_17` for an ARqpIDA-SC run under f.D0pL anchored on a set `A`
containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}` (`AssumptionD0pLAnchored`), when `x_{k+1}` is
not approximately optimal on `X` for the radii `δ_{k+1}`, for either mode `u` of the radii control
(`RadiiControlOf`; the cases `q ≤ 2` and `q > 2` become `u` and `¬ u`). -/
theorem lemma_13_1_17_anchored (hf : AssumptionD0pLAnchored f C A P.p L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : RadiiControlOf u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1))) :
    (u → ∃ j ∈ Finset.Icc 1 P.q,
      ((1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg))) ^ (1 / ((P.p - j + 1 : ℕ) : ℝ)) *
        ε j ^ (1 / ((P.p - j + 1 : ℕ) : ℝ)) ≤ ‖s k‖) ∧
    (¬ u → ∃ j ∈ Finset.Icc 1 P.q,
      ((1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
          (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arSigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) /
          (2 * j ! * arConstA P L (ordMax P.p κg))) ^ (1 / (P.p : ℝ)) *
        ε j ^ ((j : ℝ) / P.p) ≤ ‖s k‖) := by
  obtain ⟨j, hj, hb⟩ := arqpIDA_step_bound_anchored hf hXC hAX hrun hrc hk hρ hnot
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  set A := arConstA P L (ordMax P.p κg)
  have hLb := hrun.one_le_Lbar_anchored hf
  set κh := arKappaHat P.q (1 - P.θ) A (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
    (arSigmaMax P (L P.p) (ordMax P.p κg)))
  have hA : 1 ≤ A := one_le_arConstA (hf.one_le le_rfl) hrun.kappaMax_nonneg
  have hθ := P.θ_pos
  have hθ1 := P.θ_lt_one
  have hεj := hrun.eps_mem j hj
  have hfj : (1 : ℝ) ≤ j ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have hden : 0 < 2 * (j ! : ℝ) * A := by nlinarith
  have hb0 : 0 ≤ (1 - P.θ) / (2 * j ! * A) := div_nonneg (by linarith) hden.le
  have hb1 : (1 - P.θ) / (2 * j ! * A) ≤ 1 := by
    rw [div_le_one hden]; nlinarith
  have hκh0 : 0 ≤ κh := le_min (arKappaDelta1_pos (by linarith)).le
    (div_nonneg (by linarith) (by nlinarith))
  have hκh1 : κh ≤ 1 := (min_le_left _ _).trans (arKappaDelta1_le_one hLb)
  have hB0 : 0 ≤ (1 - P.θ) * κh ^ (j - 1) / (2 * j ! * A) := by
    exact div_nonneg (mul_nonneg (by linarith) (pow_nonneg hκh0 _)) hden.le
  have hB1 : (1 - P.θ) * κh ^ (j - 1) / (2 * j ! * A) ≤ 1 := by
    rw [mul_div_right_comm]
    exact mul_le_one_of_le_one hb1 (pow_nonneg hκh0 _) (pow_le_one₀ hκh0 hκh1)
  rcases hb with hs1 | ⟨hq2, hq3⟩
  · refine ⟨fun _ => ⟨j, hj, ?_⟩, fun _ => ⟨j, hj, ?_⟩⟩
    · exact (mul_le_one_of_le_one
        (Real.rpow_le_one hb0 hb1 (by positivity))
        (Real.rpow_nonneg hεj.1.le _) (Real.rpow_le_one hεj.1.le hεj.2 (by positivity))).trans hs1
    · exact (mul_le_one_of_le_one
        (Real.rpow_le_one hB0 hB1 (by positivity))
        (Real.rpow_nonneg hεj.1.le _) (Real.rpow_le_one hεj.1.le hεj.2 (by positivity))).trans hs1
  refine ⟨fun hq => ⟨j, hj, ?_⟩, fun hq => ⟨j, hj, ?_⟩⟩
  · rw [← Real.mul_rpow hb0 hεj.1.le]
    exact Optimization.rpow_one_div_le_of_le_pow (by omega) (mul_nonneg hb0 hεj.1.le)
      (norm_nonneg _) (hq2 hq)
  · have hp0 : P.p ≠ 0 := by have := P.one_le_p; omega
    have he : ε j ^ ((j : ℝ) / P.p) = (ε j ^ j) ^ (1 / (P.p : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hεj.1.le, mul_one_div]
    rw [he, ← Real.mul_rpow hB0 (pow_nonneg hεj.1.le _)]
    refine Optimization.rpow_one_div_le_of_le_pow hp0 (mul_nonneg hB0 (pow_nonneg hεj.1.le _))
      (norm_nonneg _) ?_
    calc (1 - P.θ) * κh ^ (j - 1) / (2 * j ! * A) * ε j ^ j =
          (1 - P.θ) / (2 * j ! * A) * κh ^ (j - 1) * ε j ^ j := by ring
      _ ≤ ‖s k‖ ^ P.p := hq3 hq

/-- **Lemma 13.1.17 with a feasible set** ([cartis2022evaluation] §14.2): the step-length bounds
(13.1.80) of `lemma_13_1_17` for an ARqpIDA-SC run under f.D0pL on an open convex `C ⊇ X`, when
`x_{k+1}` is not approximately optimal on `X` for the radii `δ_{k+1}`, for either mode `u` of the
radii control (`RadiiControlOf`; the cases `q ≤ 2` and `q > 2` become `u` and `¬ u`). -/
theorem lemma_13_1_17_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : RadiiControlOf u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1))) :
    (u → ∃ j ∈ Finset.Icc 1 P.q,
      ((1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg))) ^ (1 / ((P.p - j + 1 : ℕ) : ℝ)) *
        ε j ^ (1 / ((P.p - j + 1 : ℕ) : ℝ)) ≤ ‖s k‖) ∧
    (¬ u → ∃ j ∈ Finset.Icc 1 P.q,
      ((1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
          (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arSigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) /
          (2 * j ! * arConstA P L (ordMax P.p κg))) ^ (1 / (P.p : ℝ)) *
        ε j ^ ((j : ℝ) / P.p) ≤ ‖s k‖) :=
  lemma_13_1_17_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hrun hrc hk hρ hnot

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
            (arSigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) /
          (2 * j ! * arConstA P L (ordMax P.p κg))) ^ (1 / (P.p : ℝ)) *
        ε j ^ ((j : ℝ) / P.p) ≤ ‖s k‖) := by
  have h := lemma_13_1_17_feasible hf.on_univ (subset_univ _) hrun hrc hk hρ
    (by rwa [setOf_add_mem_univ])
  exact ⟨h.1, fun hq => h.2 (not_le.2 hq)⟩

/-- **Lemma 13.1.18 under the anchored assumption** ([cartis2022evaluation] §14.2): for an
ARqpIDA-SC run under f.D0pL anchored on a set `A` containing the sublevel set
`{y ∈ X | f(y) ≤ f(x₀)}` (`AssumptionD0pLAnchored`) and the radii control at `k`, if iteration `k`
is successful and `x_{k+1}` is not approximately optimal on `X` (`arTest_feasible`), then (13.1.82)
and (13.1.83) hold, as in `lemma_13_1_18`, for either mode `u` of the radii control
(`RadiiControlOf`), with `π_j = arPiOf u p j` and
`κ_{Δm} = σ_min/(p+1)! · arStepConstOf u q p (1 - θ) A κ_{δ,min}`. -/
theorem lemma_13_1_18_anchored (hf : AssumptionD0pLAnchored f C A P.p L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    [Decidable u]
    (hrc : RadiiControlOf u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hnot : ¬ arTest_feasible f X P ε x (k + 1)) :
    P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arSigmaMax P (L P.p) (ordMax P.p κg))) *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ (D k).taylorDecrement P.p (s k) ∧
      P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
          (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arSigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) := by
  have hnot' : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) {e | x (k + 1) + e ∈ X} P.q ε
      (δ (k + 1)) :=
    fun hc => hnot ⟨δ (k + 1), fun j hj => (hrun.invariants (k + 1)).2.1 j hj, hc⟩
  obtain ⟨j, hj, hb⟩ := arqpIDA_step_bound_anchored hf hXC hAX hrun hrc hk hρ hnot'
  have hs := hrun.step k
  obtain ⟨hlow, hpos⟩ := lemma_13_1_13 hs hk (fun j hj => (hrun.eps_mem j hj).1)
    (hrun.sigma_pos k).le
  have hLb := hrun.one_le_Lbar_anchored hf
  set A := arConstA P L (ordMax P.p κg)
  have hA : 1 ≤ A := one_le_arConstA (hf.one_le le_rfl) hrun.kappaMax_nonneg
  have ht : 0 < ‖s k‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hεj := hrun.eps_mem j hj
  have hC := arqp_pow_succ_ge (sub_pos.2 P.θ_lt_one) (by linarith [P.θ_pos]) hA hεj.1 hεj.2 ht
    (arKappaDelta1_pos (by linarith)) (arKappaDelta1_le_one hLb) hj P.q_le_p hb
  set C := arStepConstOf u P.q P.p (1 - P.θ) A
    (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
      (arSigmaMax P (L P.p) (ordMax P.p κg)))
  have hC0 : 0 ≤ C := arStepConstOf_nonneg (by linarith [P.θ_lt_one]) (by linarith)
    (arKappaDelta1_pos (by linarith)).le
  have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
  have hmin : epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ ε j ^ arPiOf u P.p j := epsMin_le hj
  have hmin0 : 0 ≤ epsMin P.q (fun j => ε j ^ arPiOf u P.p j) :=
    (Chapter13.epsMin_pos P.one_le_q fun j hj =>
      Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _).le
  have hσ := (hrun.invariants k).1
  have h1 : P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤
      (D k).taylorDecrement P.p (s k) := by
    calc P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)
        ≤ P.σmin / ((P.p + 1)! : ℝ) * (C * ε j ^ arPiOf u P.p j) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmin hC0)
            (div_nonneg P.σmin_pos.le hfp.le)
      _ ≤ σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) :=
          mul_le_mul (div_le_div_of_nonneg_right hσ hfp.le) hC
            (mul_nonneg hC0 (Real.rpow_nonneg hεj.1.le _))
            (div_nonneg (P.σmin_pos.le.trans hσ) hfp.le)
      _ ≤ _ := hlow
  refine ⟨h1, ?_⟩
  have h2 := (hs.accept hk).sub_ge (w := f) rfl hpos hρ
  have hη := P.η₁_pos
  have h0 : 0 ≤ P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j) := by
    have := P.σmin_pos; positivity
  calc P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C) / 2 * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)
      = P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) /
          2 := by ring
    _ ≤ P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf u P.p j)) := by
        have := mul_nonneg hη.le h0; linarith
    _ ≤ P.η₁ * (D k).taylorDecrement P.p (s k) := mul_le_mul_of_nonneg_left h1 hη.le
    _ ≤ f (x k) - f (x (k + 1)) := h2

/-- **Lemma 13.1.18 with a feasible set** ([cartis2022evaluation] §14.2): for an ARqpIDA-SC run
under f.D0pL on an open convex `C ⊇ X` and the radii control at `k`, if iteration `k` is successful
and `x_{k+1}` is not approximately optimal on `X` (`arTest_feasible`), then (13.1.82) and (13.1.83)
hold, as in `lemma_13_1_18`, for either mode `u` of the radii control (`RadiiControlOf`), with
`π_j = arPiOf u p j` and `κ_{Δm} = σ_min/(p+1)! · arStepConstOf u q p (1 - θ) A κ_{δ,min}`. -/
theorem lemma_13_1_18_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    [Decidable u]
    (hrc : RadiiControlOf u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k) (hk : ¬ acc k)
    (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hnot : ¬ arTest_feasible f X P ε x (k + 1)) :
    P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arSigmaMax P (L P.p) (ordMax P.p κg))) *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ (D k).taylorDecrement P.p (s k) ∧
      P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf u P.q P.p (1 - P.θ)
          (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arSigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPiOf u P.p j) ≤ f (x k) - f (x (k + 1)) :=
  lemma_13_1_18_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hrun hrc hk hρ hnot

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
          (arSigmaMax P (L P.p) (ordMax P.p κg))) *
        epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ (D k).taylorDecrement P.p (s k) ∧
      P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
          (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arSigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ f (x k) - f (x (k + 1)) :=
  lemma_13_1_18_feasible hf.on_univ (subset_univ _) hrun hrc hk hρ (by rwa [arTest_feasible_univ])

/-! ### Theorem 13.1.19 -/

/-- The constant `κ_acc` of the proof of Theorem 13.1.19 ([cartis2022evaluation]):
`min(ς κ^q/(4 q! κ_{∇,max}), κ_s (ς κ^q/(12 q! max(L̄_f, σ_max)))^p)` with `κ = κ^{(1)}_δ(σ_max)`,
the first term being omitted when `κ_{∇,max} = 0`. -/
noncomputable def arKappaAcc (P : ARqpIDAParams) (κ Lb σmax κm : ℝ) : ℝ :=
  if κm = 0 then P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * max Lb σmax)) ^ P.p
  else min (P.ς * κ ^ P.q / (4 * P.q ! * κm))
    (P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * max Lb σmax)) ^ P.p)

theorem arKappaAcc_pos {P : ARqpIDAParams} {κ Lb σmax κm : ℝ} (hκ : 0 < κ) (hLb : 0 < Lb)
    (hκm : 0 ≤ κm) : 0 < arKappaAcc P κ Lb σmax κm := by
  have := P.ς_pos; have := P.κs_pos
  have hM : 0 < max Lb σmax := lt_max_of_lt_left hLb
  unfold arKappaAcc
  split_ifs with h0
  · positivity
  · exact lt_min (by have := lt_of_le_of_ne hκm (Ne.symm h0); positivity) (by positivity)

theorem arKappaAcc_le {P : ARqpIDAParams} {κ Lb σmax κm : ℝ} :
    arKappaAcc P κ Lb σmax κm ≤ P.κs * (P.ς * κ ^ P.q / (12 * P.q ! * max Lb σmax)) ^ P.p := by
  unfold arKappaAcc
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

theorem mul_arKappaAcc_le {P : ARqpIDAParams} {κ Lb σmax κm : ℝ} (hκ : 0 ≤ κ) (hκm : 0 ≤ κm) :
    κm * arKappaAcc P κ Lb σmax κm ≤ P.ς * κ ^ P.q / (4 * P.q !) := by
  have := P.ς_pos
  unfold arKappaAcc
  split_ifs with h0
  · rw [h0, zero_mul]; positivity
  · have hκm' : 0 < κm := lt_of_le_of_ne hκm (Ne.symm h0)
    calc κm * min (P.ς * κ ^ P.q / (4 * P.q ! * κm)) _
        ≤ κm * (P.ς * κ ^ P.q / (4 * P.q ! * κm)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hκm
      _ = P.ς * κ ^ P.q / (4 * P.q !) := by field_simp

/-- **The accuracy-improving iterations of ARqpIDA-SC** (proof of Theorem 13.1.19,
[cartis2022evaluation]): under f.D0pL anchored on a set `A` containing the sublevel set
`{y ∈ X | f(y) ≤ f(x₀)}` (`AssumptionD0pLAnchored`) and the radii control at every iteration, if no
iterate `x_j`, `j ≤ k`, is approximately optimal on `X`, then
`|𝒜_k| ≤ p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1` (either mode of the radii
control, `RadiiControlOf`). -/
theorem arqpIDA_card_acc_le_anchored (hf : AssumptionD0pLAnchored f C A P.p L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i, RadiiControlOf u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arTest_feasible f X P ε x j) :
    ((successSet acc k).card : ℝ) ≤
      P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
        |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arSigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
            (arSigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
          |Real.log P.γh| + 1 := by
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  set κm := ordMax P.p κg
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  have hLb := hrun.one_le_Lbar_anchored hf
  set σmax := arSigmaMax P (L P.p) κm
  have hσk : ∀ k, σ k ≤ σmax := fun k => lemma_13_1_14_anchored hf hXC hAX hrun k
  set κ := arKappaDelta1 P Lb σmax
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  set κacc := arKappaAcc P κ Lb σmax κm
  have hκacc : 0 < κacc := arKappaAcc_pos hκ0 (by linarith) hκm
  have hlogh : 0 < |Real.log P.γh| := abs_pos.2 (Real.log_neg P.γh_pos P.γh_lt_one).ne
  set NA := P.p * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hpowq : em ^ (P.p * (P.q + 1)) ≤ em ^ (P.q + 1) :=
    pow_le_pow_of_le_one hεmin.le hεmin1 (by nlinarith [P.one_le_p])
  have hp := P.one_le_p
  have h := card_accuracyImproving_le_of_pow_of_nonneg (acc := acc)
    (hmax := fun j => ordMax P.p (h j))
    (N := P.p * (P.q + 1)) (k := k) P.γh_pos P.γh_lt_one P.κh_nonneg hκacc hεmin
    ((ordMax_le_iff hp).2 fun i hi => by rw [hrun.h_zero]; exact P.h₀_le i hi)
    (fun j _ => (ordMax_le_iff hp).2 fun i hi => ((hrun.invariants j).2.2 i hi).2)
    (fun j _ ha => by
      rw [show h (j + 1) = fun i => P.γh * h j i from funext ((hrun.step j).h_acc ha),
        ordMax_mul hp P.γh_pos.le])
    (fun j _ ha => by rw [(hrun.step j).h_trial ha])
    (fun j hj ha => by
      by_contra hcon
      push Not at hcon
      have hhi : ∀ i ∈ Finset.Icc 1 P.p, h j i ≤ κacc * em ^ (P.p * (P.q + 1)) :=
        fun i hi => (le_ordMax hi).trans hcon
      by_cases hfail : ∃ i ∈ Finset.Icc 1 P.q, ¬ arPass P ε D δ₁ dd j i
      · refine (lemma_13_1_12_anchored hf hAX hrun (fun i _ => hrc i) (k := j)
          (fun i _ => hσk i)).2.2 hfail
          (fun i hi => (hhi i hi).trans ?_) ha
        exact mul_le_mul_of_nonneg_right arKappaAcc_le (by positivity)
      · push Not at hfail
        refine hk j hj
          (lemma_13_1_15_anchored hf hXC hAX hrun (fun i _ => hrc i) hfail fun i hi => ?_).2.2
        calc κm * h j i ≤ κm * (κacc * em ^ (P.p * (P.q + 1))) :=
              mul_le_mul_of_nonneg_left (hhi i hi) hκm
          _ = κm * κacc * em ^ (P.p * (P.q + 1)) := by ring
          _ ≤ P.ς * κ ^ P.q / (4 * P.q !) * em ^ (P.q + 1) :=
              mul_le_mul (mul_arKappaAcc_le hκ0.le hκm) hpowq (by positivity)
                (by have := P.ς_pos; positivity))
  calc ((successSet acc k).card : ℝ)
      ≤ (((P.p * (P.q + 1) : ℕ) : ℝ) * |Real.log em| + |Real.log (κacc / P.κh)|) /
          |Real.log P.γh| + 1 := h
    _ = NA := by rw [hNA_def]; push_cast; ring

/-- **The accuracy-improving iterations of ARqpIDA-SC** (proof of Theorem 13.1.19,
[cartis2022evaluation]): under f.D0pL on an open convex `C ⊇ X` and the radii control at every
iteration, if no iterate `x_j`, `j ≤ k`, is approximately optimal on `X`, then
`|𝒜_k| ≤ p(q+1)/|log γ_h| |log ε_min| + |log(κ_acc/κ_h)|/|log γ_h| + 1` (either mode of the
radii control, `RadiiControlOf`). -/
theorem arqpIDA_card_acc_le_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i, RadiiControlOf u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arTest_feasible f X P ε x j) :
    ((successSet acc k).card : ℝ) ≤
      P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
        |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arSigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
            (arSigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
          |Real.log P.γh| + 1 :=
  arqpIDA_card_acc_le_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hrun hrc hk

/-- **The complexity argument of Theorem 13.1.19 under the anchored assumption**
([cartis2022evaluation] §14.2): `arqpIDA_complexity` for an ARqpIDA-SC run under f.D0pL anchored on
a set `A` containing the sublevel set `{y ∈ X | f(y) ≤ f(x₀)}` (`AssumptionD0pLAnchored`) and
f.bB.X, with approximate optimality on `X` (`arTest_feasible`) and either mode of the radii control
(`RadiiControlOf`). -/
theorem arqpIDA_complexity_anchored (hf : AssumptionD0pLAnchored f C A P.p L)
    (hXC : X ⊆ C) (hAX : ∀ y ∈ X, f y ≤ f x₀ → y ∈ A) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i, RadiiControlOf u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    {c : ℝ} (hc : 0 < c)
    (hdec : ∀ k, ¬ acc k → P.η₁ ≤ arqpIDARatio f P D x s k → ¬ arTest_feasible f X P ε x (k + 1) →
      c ≤ f (x k) - f (x (k + 1))) :
    ∃ kε, IsFirstHit (arTest_feasible f X P ε x) kε ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) / c) +
          (Real.log (arSigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) / c + P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  have hq := P.one_le_q
  set em := epsMin P.q ε with hem
  have hεmin : 0 < em := hrun.epsMin_pos
  have hεmin1 : em ≤ 1 := hrun.epsMin_le_one
  set κm := ordMax P.p κg
  have hκm : 0 ≤ κm := hrun.kappaMax_nonneg
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  have hLb := hrun.one_le_Lbar_anchored hf
  set σmax := arSigmaMax P (L P.p) κm
  have hσk : ∀ k, σ k ≤ σmax := fun k => lemma_13_1_14_anchored hf hXC hAX hrun k
  have hσ₀ : P.σ₀ ≤ σmax := le_max_left _ _
  set κ := arKappaDelta1 P Lb σmax
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hf0 : 0 ≤ f x₀ - flow := sub_nonneg.2 (hb x₀ hrun.x₀_mem)
  set N := (f x₀ - flow) / c with hN_def
  have hN0 : 0 ≤ N := by positivity
  -- successful iterations before termination
  have hS : ∀ k, (∀ j ≤ k, ¬ arTest_feasible f X P ε x j) →
      ((successSet (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) k).card : ℝ) ≤ N + 1 := by
    refine card_successSet_le_add_one_of_forall hN0 fun k hk => ?_
    rw [hN_def, ← hrun.x_zero]
    exact card_successSet_le_div_of_decrease («φ» := fun i => f (x i)) hc
      (fun j _ hj => by rw [(hrun.step j).x_succ_eq hj])
      (fun j hj hs => hdec j hs.1 hs.2 (hk (j + 1) (by omega))) (hb _ (hrun.mem _))
  -- trial iterations
  have hlog2 : 0 < Real.log P.γ₂ := P.log_γ₂_pos
  set cT := 1 + |Real.log P.γ₁| / Real.log P.γ₂ with hcT
  have hcT0 : 0 ≤ cT := by positivity
  set NT := (N + 1) * cT + Real.log (σmax / P.σ₀) / Real.log P.γ₂ with hNT_def
  have hNT0 : 0 ≤ NT := by
    have : 0 ≤ Real.log (σmax / P.σ₀) :=
      Real.log_nonneg ((one_le_div P.σ₀_pos).2 hσ₀)
    positivity
  have hT : ∀ k, (∀ j ≤ k, ¬ arTest_feasible f X P ε x j) →
      ((successSet (fun i => ¬ acc i) k).card : ℝ) ≤ NT := by
    intro k hk
    have h1 := lemma_13_1_9 (fun i _ => hrun.step i) hrun.σ_zero hrun.δ_zero hrun.h_zero
      (hσk (k + 1))
    have h2 := mul_le_mul_of_nonneg_right (hS k hk) hcT0
    linarith
  -- accuracy-improving iterations
  set κacc := arKappaAcc P κ Lb σmax κm
  set NA := P.p * (P.q + 1) / |Real.log P.γh| * |Real.log em| +
    |Real.log (κacc / P.κh)| / |Real.log P.γh| + 1 with hNA_def
  have hNA0 : 0 ≤ NA := by positivity
  have hp := P.one_le_p
  have hA : ∀ k, (∀ j ≤ k, ¬ arTest_feasible f X P ε x j) → ((successSet acc k).card : ℝ) ≤ NA :=
    fun k hk => arqpIDA_card_acc_le_anchored hf hXC hAX hrun hrc hk
  -- conclusion
  obtain ⟨kε, hkε, -, hTk, hAk⟩ := exists_firstHit_le_of_dynamicAccuracy hNT0 hNA0 hT hA
  have hSk := derivEvalCount_le_of_isFirstHit (by linarith) hkε hS
  have hor : (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε :
      ℝ) + 1 ≤ derivEvalCount acc kε +
        derivEvalCount (fun i => ¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i) kε := by
    exact_mod_cast derivEvalCount_or_add_one_le _ _ kε
  refine ⟨kε, hkε, ?_, ?_⟩
  · calc (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤ NT + 1 := hTk
      _ = _ := by rw [hNT_def, hcT]; ring
  · calc _ ≤ (NA + 1) + (N + 1 + 1) - 1 := by linarith
      _ = _ := by rw [hNA_def]; ring

/-- **The complexity argument of Theorem 13.1.19 with a feasible set** ([cartis2022evaluation]
§14.2): `arqpIDA_complexity` for an ARqpIDA-SC run under f.D0pL on an open convex `C ⊇ X` and
f.bB.X, with approximate optimality on `X` (`arTest_feasible`) and either mode of the radii
control (`RadiiControlOf`). -/
theorem arqpIDA_complexity_feasible (hf : AssumptionD0pLOn f C P.p L) (hXC : X ⊆ C) {flow : ℝ}
    (hb : ∀ y ∈ X, flow ≤ f y)
    (hrun : algorithm_13_1_2_feasible f X κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc) {u : Prop}
    (hrc : ∀ i, RadiiControlOf u P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i)
    {c : ℝ} (hc : 0 < c)
    (hdec : ∀ k, ¬ acc k → P.η₁ ≤ arqpIDARatio f P D x s k → ¬ arTest_feasible f X P ε x (k + 1) →
      c ≤ f (x k) - f (x (k + 1))) :
    ∃ kε, IsFirstHit (arTest_feasible f X P ε x) kε ∧
      (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f x₀ - flow) / c) +
          (Real.log (arSigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) / c + P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 :=
  arqpIDA_complexity_anchored (hf.anchored hXC) hXC (fun _ hy _ => hy) hb hrun hrc hc hdec

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
          (Real.log (arSigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
            |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        (f x₀ - flow) / c + P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  have := arqpIDA_complexity_feasible hf.on_univ (subset_univ _) (fun y _ => hb y) hrun hrc hc
    fun k hk hρ hnot => hdec k hk hρ (by rwa [arTest_feasible_univ] at hnot)
  rwa [arTest_feasible_univ] at this

/-- **Radius one for orders `≤ 2`** (used for Theorem 13.1.19 (1)): if `q ≤ 2` and `x` is an
`(ε, δ)`-approximate `q`-th order minimizer for some radii `δ ∈ (0, 1]^q` (unconstrained), then
`φ^1_{f,j}(x) ≤ ε_j/j!` for `j ∈ [1, q]` (`δ ↦ φ^δ_j/δ^j` is non-increasing for `j ≤ 2`,
`Optimization.pow_div_mul_taylorMeasure_le`). -/
theorem isEpsDeltaApprox_one_of_le_two {D : FormalMultilinearSeries ℝ ℝⁿ ℝ} {q : ℕ}
    (hq : q ≤ 2) {ε δ : ℕ → ℝ} (hδ : ∀ j ∈ Finset.Icc 1 q, δ j ∈ Set.Ioc 0 1)
    (h : IsEpsDeltaApprox D univ q ε δ) : IsEpsDeltaApprox D univ q ε (fun _ => 1) := by
  intro j hj
  have hj2 : j ≤ 2 := (Finset.mem_Icc.1 hj).2.trans hq
  have h1 := pow_div_mul_taylorMeasure_le D hj2 (hδ j hj).1 (hδ j hj).2
  have h2 := h j hj
  have hpos : 0 < δ j ^ j := pow_pos (hδ j hj).1 j
  have hf : (0 : ℝ) < j ! := by positivity
  rw [div_one] at h1
  simp only [one_pow, mul_one]
  have : δ j ^ j * taylorMeasure D j 1 univ ≤ δ j ^ j * (ε j / j !) := by
    calc δ j ^ j * taylorMeasure D j 1 univ ≤ ε j * δ j ^ j / j ! := h1.trans h2
      _ = δ j ^ j * (ε j / j !) := by ring
  exact le_of_mul_le_mul_left this hpos

/-- **Lemma 13.1.16 at unit radii** (`q ≤ 2`, no constraints): for an ARqpIDA run on `ℝⁿ`
(`algorithm_13_1_2_feasible` with `X = univ`) under f.D0pL, a successful iteration `k` with
`‖s_k‖ < 1` such that `x_{k+1}` is not approximately optimal with unit radii satisfies (13.1.79)
with `δ = 1`, whatever the radii `δ_{s_k}` of Step 2: since `δ ↦ φ^δ_ℓ/δ^ℓ` is non-increasing for
`ℓ ≤ 2` (`Optimization.pow_div_mul_taylorMeasure_le`), the bound (13.1.57) on the model at the
radii `δ_{s_k}` gives the same bound at radius `1`. -/
theorem lemma_13_1_16_unit (hf : AssumptionD0pLOn f univ P.p L) (hq2 : P.q ≤ 2)
    (hrun : algorithm_13_1_2_feasible f univ κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hk : ¬ acc k) (hρ : P.η₁ ≤ arqpIDARatio f P D x s k) (hs1 : ‖s k‖ < 1)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) univ P.q ε (fun _ => 1)) :
    ∃ j ∈ Finset.Icc 1 P.q, (1 - P.θ) * ε j * 1 ^ j / j ! ≤
      (L P.p + arSigmaMax P (L P.p) (ordMax P.p κg) + 3 * ordMax P.p κg * P.κs) *
        ∑ ℓ ∈ Finset.Icc 1 j, 1 ^ ℓ / ℓ ! * ‖s k‖ ^ (P.p - ℓ + 1) := by
  have hs := hrun.step k
  have h2 := hs.step2_of_not_acc hk
  have hx : x (k + 1) = x k + s k := hs.x_succ_eq_add hk hρ
  unfold IsEpsDeltaApprox at hnot
  push Not at hnot
  obtain ⟨j, hj, hlt⟩ := hnot
  refine ⟨j, hj, ?_⟩
  obtain ⟨hδmem, dm, hdm, hdmle⟩ := h2.radii_of_lt hs1 j hj
  rw [hx] at hlt
  have hjp : j ≤ P.p := (Finset.mem_Icc.1 hj).2.trans P.q_le_p
  have hj2 : j ≤ 2 := (Finset.mem_Icc.1 hj).2.trans hq2
  have hfj : (0 : ℝ) < j ! := by positivity
  have h₂δ : taylorMeasure (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) j (δs k j)
      univ ≤ P.θ * ε j * δs k j ^ j / j ! := by
    have hw := hdm.2
    have := hw.trans hdmle
    have hς := P.ς_pos
    rw [show P.ς * P.θ * ε j * δs k j ^ j / j ! = P.ς * (P.θ * ε j * δs k j ^ j / j !) by ring,
      setOf_add_mem_univ] at this
    exact le_of_mul_le_mul_left this hς
  have h₂ : taylorMeasure (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) j 1
      univ ≤ P.θ * ε j * 1 ^ j / j ! := by
    have hmono := pow_div_mul_taylorMeasure_le
      (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) hj2 hδmem.1 hδmem.2
    rw [div_one] at hmono
    have hpos : 0 < δs k j ^ j := pow_pos hδmem.1 j
    rw [one_pow, mul_one]
    have : δs k j ^ j * taylorMeasure
        (ftaylorSeries ℝ (regularizedModel (D k) P.p (σ k)) (s k)) j 1 univ ≤
        δs k j ^ j * (P.θ * ε j / j !) := by
      calc _ ≤ P.θ * ε j * δs k j ^ j / j ! := hmono.trans h₂δ
        _ = δs k j ^ j * (P.θ * ε j / j !) := by ring
    exact le_of_mul_le_mul_left this hpos
  have := radius_inequality_of_measure_gt hf.convex (fun y hy => hf.contDiffAt le_rfl hy)
    (hf.lipschitz le_rfl) (zero_le_one.trans (hf.one_le le_rfl)) (mem_univ _) (mem_univ _)
    (hrun.oracle k) hrun.kappaMax_nonneg P.κs_pos.le
    (fun i hi => by
      rw [mul_assoc]
      exact mul_le_mul (le_ordMax hi) (h2.h_le_of_not_acc hk hs1 i hi)
        ((hrun.invariants k).2.2 i hi).1 hrun.kappaMax_nonneg)
    (hrun.sigma_pos k).le (lemma_13_1_14_feasible hf subset_rfl hrun k) hjp (mem_univ 0)
    zero_le_one (a := 1) (e₀ := 0) (by rw [one_mul, sub_zero]; exact hlt) h₂
  rw [add_zero] at this
  exact this.le

/-- **The step bound at unit radii** (`q ≤ 2`, no constraints): for an ARqpIDA run on `ℝⁿ` under
f.D0pL and any radii, a successful iteration `k` such that `x_{k+1}` is not approximately optimal
with unit radii has a long step or `(1-θ)/(2 j! A) ε_j ≤ ‖s_k‖^{p-j+1}` for some `j ∈ [1, q]`
(the conclusion of `arqpIDA_step_bound_feasible` in the unit-radii mode). -/
theorem arqpIDA_step_bound_unit (hf : AssumptionD0pLOn f univ P.p L) (hq2 : P.q ≤ 2)
    (hrun : algorithm_13_1_2_feasible f univ κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hk : ¬ acc k) (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) univ P.q ε (fun _ => 1)) :
    ∃ j ∈ Finset.Icc 1 P.q, 1 ≤ ‖s k‖ ∨
      ((True → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) * ε j ≤
          ‖s k‖ ^ (P.p - j + 1)) ∧
        (¬ True → (1 - P.θ) / (2 * j ! * arConstA P L (ordMax P.p κg)) *
          arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
            (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg))) ^ (j - 1) * ε j ^ j ≤ ‖s k‖ ^ P.p)) := by
  rcases le_or_gt 1 ‖s k‖ with hs1 | hs1
  · exact ⟨1, P.one_mem_Icc, Or.inl hs1⟩
  obtain ⟨j, hj, hineq⟩ := lemma_13_1_16_unit hf hq2 hrun hk hρ hs1 hnot
  refine ⟨j, hj, Or.inr ?_⟩
  have hs := hrun.step k
  have hLb := hrun.one_le_Lbar hf
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  set κ := arKappaDelta1 P Lb (arSigmaMax P (L P.p) (ordMax P.p κg))
  have hκ0 : 0 < κ := arKappaDelta1_pos (by linarith)
  have hκ1 : κ ≤ 1 := arKappaDelta1_le_one hLb
  have hεj := hrun.eps_mem j hj
  have hκε : κ * ε j ≤ 1 := mul_le_one_of_le_one hκ1 hεj.1.le hεj.2
  have ht : 0 < ‖s k‖ := by
    have hpos := (lemma_13_1_13 hs hk (fun j hj => (hrun.eps_mem j hj).1)
      (hrun.sigma_pos k).le).2
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hA : 0 < arConstA P L (ordMax P.p κg) := by
    have := hf.one_le le_rfl
    have : 0 ≤ arSigmaMax P (L P.p) (ordMax P.p κg) := (P.σ₀_pos.le).trans (le_max_left _ _)
    have := hrun.kappaMax_nonneg; have := P.κs_pos
    unfold arConstA; positivity
  exact arqp_pow_ge_of_radius_ineq (u := True) (sub_pos.2 P.θ_lt_one) hA hεj.1 ht hs1 one_pos
    hj P.q_le_p hκ0 hκε (fun _ => rfl) hineq

/-- **Lemma 13.1.18 at unit radii** (`q ≤ 2`, no constraints): for an ARqpIDA run on `ℝⁿ` under
f.D0pL and any radii, every successful iteration `k` such that `x_{k+1}` is not approximately
optimal (`arTest_feasible`, some radii in `(0, 1]^q`) decreases `f` by at least
`½ η₁ κ_{Δm} min_j ε_j^{(p+1)/(p-j+1)}`, the decrease of the unit-radii mode
(`lemma_13_1_18_feasible` with `u = True`), whatever the radii control of the run. -/
theorem lemma_13_1_18_unit (hf : AssumptionD0pLOn f univ P.p L) (hq2 : P.q ≤ 2)
    (hrun : algorithm_13_1_2_feasible f univ κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc)
    (hk : ¬ acc k) (hρ : P.η₁ ≤ arqpIDARatio f P D x s k)
    (hnot : ¬ arTest_feasible f univ P ε x (k + 1)) :
    P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * arStepConstOf True P.q P.p (1 - P.θ)
          (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
            (arSigmaMax P (L P.p) (ordMax P.p κg)))) / 2 *
        epsMin P.q (fun j => ε j ^ arPiOf True P.p j) ≤ f (x k) - f (x (k + 1)) := by
  have hnot' : ¬ IsEpsDeltaApprox (ftaylorSeries ℝ f (x (k + 1))) univ P.q ε (fun _ => 1) :=
    fun hc => hnot ⟨fun _ => 1, fun _ _ => ⟨one_pos, le_rfl⟩, by rwa [setOf_add_mem_univ]⟩
  obtain ⟨j, hj, hb⟩ := arqpIDA_step_bound_unit hf hq2 hrun hk hρ hnot'
  have hs := hrun.step k
  obtain ⟨hlow, hpos⟩ := lemma_13_1_13 hs hk (fun j hj => (hrun.eps_mem j hj).1)
    (hrun.sigma_pos k).le
  have hLb := hrun.one_le_Lbar hf
  set A := arConstA P L (ordMax P.p κg)
  have hA : 1 ≤ A := one_le_arConstA (hf.one_le le_rfl) hrun.kappaMax_nonneg
  have ht : 0 < ‖s k‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    rw [h0, FormalMultilinearSeries.taylorDecrement_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hεj := hrun.eps_mem j hj
  have hC := arqp_pow_succ_ge (u := True) (sub_pos.2 P.θ_lt_one) (by linarith [P.θ_pos]) hA
    hεj.1 hεj.2 ht (arKappaDelta1_pos (by linarith)) (arKappaDelta1_le_one hLb) hj P.q_le_p hb
  set C := arStepConstOf True P.q P.p (1 - P.θ) A
    (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
      (arSigmaMax P (L P.p) (ordMax P.p κg)))
  have hC0 : 0 ≤ C := arStepConstOf_nonneg (by linarith [P.θ_lt_one]) (by linarith)
    (arKappaDelta1_pos (by linarith)).le
  have hfp : (0 : ℝ) < (P.p + 1)! := by positivity
  have hmin : epsMin P.q (fun j => ε j ^ arPiOf True P.p j) ≤ ε j ^ arPiOf True P.p j :=
    epsMin_le hj
  have hσ := (hrun.invariants k).1
  have h1 : P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf True P.p j) ≤
      (D k).taylorDecrement P.p (s k) := by
    calc P.σmin / ((P.p + 1)! : ℝ) * C * epsMin P.q (fun j => ε j ^ arPiOf True P.p j)
        ≤ P.σmin / ((P.p + 1)! : ℝ) * (C * ε j ^ arPiOf True P.p j) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmin hC0)
            (div_nonneg P.σmin_pos.le hfp.le)
      _ ≤ σ k / ((P.p + 1)! : ℝ) * ‖s k‖ ^ (P.p + 1) :=
          mul_le_mul (div_le_div_of_nonneg_right hσ hfp.le) hC
            (mul_nonneg hC0 (Real.rpow_nonneg hεj.1.le _))
            (div_nonneg (P.σmin_pos.le.trans hσ) hfp.le)
      _ ≤ _ := hlow
  have h2 := (hs.accept hk).sub_ge (w := f) rfl hpos hρ
  have hη := P.η₁_pos
  have h0 : 0 ≤ P.σmin / ((P.p + 1)! : ℝ) * C *
      epsMin P.q (fun j => ε j ^ arPiOf True P.p j) := by
    have hm0 : 0 ≤ epsMin P.q (fun j => ε j ^ arPiOf True P.p j) :=
      (Chapter13.epsMin_pos P.one_le_q fun j hj =>
        Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _).le
    have := P.σmin_pos; positivity
  calc P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C) / 2 *
        epsMin P.q (fun j => ε j ^ arPiOf True P.p j)
      = P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C *
          epsMin P.q (fun j => ε j ^ arPiOf True P.p j)) / 2 := by ring
    _ ≤ P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) * C *
          epsMin P.q (fun j => ε j ^ arPiOf True P.p j)) := by
        have := mul_nonneg hη.le h0; linarith
    _ ≤ P.η₁ * (D k).taylorDecrement P.p (s k) := mul_le_mul_of_nonneg_left h1 hη.le
    _ ≤ f (x k) - f (x (k + 1)) := h2

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
        (Real.log (arSigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
          |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((1 - P.θ) / (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^
              (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ)))) * (f x₀ - flow) /
          epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) +
        P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  set κΔm := P.σmin / ((P.p + 1)! : ℝ) *
    ((1 - P.θ) / (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^
      (((P.p : ℝ) + 1) / ((P.p - P.q + 1 : ℕ) : ℝ)) with hκΔm
  set m := epsMin P.q (fun j => ε j ^ (((P.p : ℝ) + 1) / ((P.p - j + 1 : ℕ) : ℝ))) with hm
  have hm' : epsMin P.q (fun j => ε j ^ arPi P.q P.p j) = m := by
    simp only [arPi, arPiOf, hq2, ↓reduceIte]; exact hm.symm
  have hκ' : P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
      (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arSigmaMax P (L P.p) (ordMax P.p κg))) = κΔm := by
    simp only [arStepConst, arStepConstOf, hq2, ↓reduceIte]; exact hκΔm.symm
  have hA := one_le_arConstA (hf.one_le le_rfl) hrun.kappaMax_nonneg (P := P) (L := L)
  have hκpos : 0 < κΔm := by
    have := P.σmin_pos; have := P.θ_lt_one
    have : 0 < (1 - P.θ) / (2 * P.q ! * arConstA P L (ordMax P.p κg)) := by
      apply div_pos (by linarith) (by positivity)
    positivity
  have hmpos : 0 < m := Chapter13.epsMin_pos P.one_le_q fun j hj =>
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
`theorem_13_1_19_i`, with the exponents `π_j = j(p+1)/p` ((13.1.86)–(13.1.87); the printed
(13.1.86) is OCR-damaged and is restored from Lemma 13.1.18) and
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
                (arSigmaMax P (L P.p) (ordMax P.p κg))) ^ (P.q - 1) /
              (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^
              ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p))) *
            (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (f x₀ - flow) /
          epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) +
        (Real.log (arSigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
          |Real.log P.γ₁| / Real.log P.γ₂) ∧
      (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε : ℝ) ≤
        2 / (P.η₁ * (P.σmin / ((P.p + 1)! : ℝ) *
            ((1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
              (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
                (arSigmaMax P (L P.p) (ordMax P.p κg))) ^ (P.q - 1) /
              (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^
              ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p))) * (f x₀ - flow) /
          epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) +
        P.p * (P.q + 1) / |Real.log P.γh| * |Real.log (epsMin P.q ε)| +
          |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
              (arSigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| /
            |Real.log P.γh| + 3 := by
  have hq2' : ¬ P.q ≤ 2 := not_le.2 hq2
  set κΔm := P.σmin / ((P.p + 1)! : ℝ) *
    ((1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
      (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arSigmaMax P (L P.p) (ordMax P.p κg))) ^ (P.q - 1) /
      (2 * P.q ! * arConstA P L (ordMax P.p κg))) ^ ((P.q : ℝ) * ((P.p : ℝ) + 1) / P.p)
    with hκΔm
  set m := epsMin P.q (fun j => ε j ^ ((j : ℝ) * ((P.p : ℝ) + 1) / P.p)) with hm
  have hm' : epsMin P.q (fun j => ε j ^ arPi P.q P.p j) = m := by
    simp only [arPi, arPiOf, hq2', ↓reduceIte]; exact hm.symm
  have hκ' : P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
      (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
        (arSigmaMax P (L P.p) (ordMax P.p κg))) = κΔm := by
    simp only [arStepConst, arStepConstOf, hq2', ↓reduceIte]; exact hκΔm.symm
  have hLb := hrun.one_le_Lbar hf.on_univ
  have hA := one_le_arConstA (hf.one_le le_rfl) hrun.kappaMax_nonneg (P := P) (L := L)
  have hκpos : 0 < κΔm := by
    have := P.σmin_pos; have := P.θ_lt_one
    have h0 : 0 < arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arSigmaMax P (L P.p) (ordMax P.p κg))) :=
      lt_min (arKappaDelta1_pos (by linarith)) (div_pos (by linarith) (by positivity))
    have : 0 < (1 - P.θ) * arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arSigmaMax P (L P.p) (ordMax P.p κg))) ^ (P.q - 1) /
        (2 * P.q ! * arConstA P L (ordMax P.p κg)) :=
      div_pos (mul_pos (by linarith) (pow_pos h0 _)) (by positivity)
    positivity
  have hmpos : 0 < m := Chapter13.epsMin_pos P.one_le_q fun j hj =>
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

/-! ### Existence of ARqpIDA runs -/

section ARExistence

open Classical in
/-- **The halving loop of Step 1 of ARqpIDA terminates** ([cartis2022evaluation], Lemma 13.1.11,
existence half): for inexact derivatives with `‖D_ℓ‖ ≤ L̄` (`ℓ ∈ [1, p]`), `σ ≥ 0`, `ε_j > 0`
and a radius `δ ∈ (0, 1]`, halving `δ` while (13.1.53) and (13.1.54) both fail stops at a radius
`δ₁ ∈ (0, δ]` with a displacement `d` satisfying (13.1.52) and (13.1.53) or (13.1.54), and if
`δ₁ < δ` with the witnesses of the last and of the first halving. -/
theorem exists_halving {D : FormalMultilinearSeries ℝ ℝⁿ ℝ} {p : ℕ} {σ Lb : ℝ} (hσ : 0 ≤ σ)
    (hLb : 0 < Lb) (hD : ∀ ℓ ∈ Finset.Icc 1 p, ‖D ℓ‖ ≤ Lb) {j : ℕ} (hjp : j ≤ p)
    {ς e δ : ℝ} (hς : 0 < ς) (hς1 : ς ≤ 1) (he : 0 < e) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ δ₁ d, 0 < δ₁ ∧ δ₁ ≤ δ ∧ IsApproxMeasureStep (D.taylorDecrement j) δ₁ univ ς d ∧
      (D.taylorDecrement j d ≤ ς * e * δ₁ ^ j / j ! / 2 ∨
        ς * e * δ₁ ^ j / j ! / 4 ≤ regularizedModel D p σ 0 - regularizedModel D p σ d) ∧
      (δ₁ < δ → 2 * δ₁ ≤ δ ∧
        (∃ d', ‖d'‖ ≤ 2 * δ₁ ∧ ς * e * (2 * δ₁) ^ j / j ! / 2 < D.taylorDecrement j d' ∧
          regularizedModel D p σ 0 - regularizedModel D p σ d' < ς * e * (2 * δ₁) ^ j / j ! / 4) ∧
        ∃ d₀, ‖d₀‖ ≤ δ ∧ ς * e * δ ^ j / j ! / 2 < D.taylorDecrement j d₀) ∧
      ∃ m : ℕ, δ₁ = δ / 2 ^ m := by
  set r : ℕ → ℝ := fun m => δ / 2 ^ m with hr
  have hr0 : ∀ m, 0 < r m := fun m => by positivity
  have hrle : ∀ m, r m ≤ δ := fun m => div_le_self hδ.le (one_le_pow₀ one_le_two)
  have hrsucc : ∀ m, 2 * r (m + 1) = r m := fun m => by simp only [hr, pow_succ]; field_simp
  choose d hd using fun m => exists_isApproxMeasureStep_taylorDecrement D j isClosed_univ
    (mem_univ 0) (hr0 m).le hς1
  set M := max Lb σ
  have hM : 0 < M := lt_max_of_lt_left hLb
  have hex : ∃ m, D.taylorDecrement j (d m) ≤ ς * e * r m ^ j / j ! / 2 ∨
      ς * e * r m ^ j / j ! / 4 ≤ regularizedModel D p σ 0 - regularizedModel D p σ (d m) := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (δ / (ς * e / (8 * M))) one_lt_two
    refine ⟨m, ?_⟩
    by_cases hpass : D.taylorDecrement j (d m) ≤ ς * e * r m ^ j / j ! / 2
    · exact Or.inl hpass
    right
    have hrm : r m ≤ ς * e / (8 * M) := by
      rw [div_lt_iff₀ (by positivity)] at hm
      simp only [hr]
      rw [div_le_iff₀ (by positivity)]
      linarith
    have key := regularizedModel_decrease_ge_of_taylorDecrement_ge (D := D) (p := p) (σ := σ)
      (L := Lb) hjp hσ
      (fun ℓ hℓ => hD ℓ (Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hℓ).1; omega,
        (Finset.mem_Icc.1 hℓ).2⟩))
      (α := ς * e / 2) (hr0 m).le ((hrle m).trans hδ1) (by
        rw [le_div_iff₀ (by positivity)] at hrm; nlinarith) (hd m).norm_le
      (by
        have : ς * e / 2 * r m ^ j / j ! = ς * e * r m ^ j / j ! / 2 := by ring
        rw [this]; exact (not_le.1 hpass).le)
    have : ς * e / 2 / 2 * r m ^ j / j ! = ς * e * r m ^ j / j ! / 4 := by ring
    rwa [this] at key
  set m := Nat.find hex
  refine ⟨r m, d m, hr0 m, hrle m, hd m, Nat.find_spec hex, fun hlt => ?_, m, rfl⟩
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := by
    refine ⟨m - 1, ?_⟩
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; rw [h0] at hlt; simp [hr] at hlt
    · omega
  have hmin : ∀ i < m, ¬ (D.taylorDecrement j (d i) ≤ ς * e * r i ^ j / j ! / 2 ∨
      ς * e * r i ^ j / j ! / 4 ≤ regularizedModel D p σ 0 - regularizedModel D p σ (d i)) :=
    fun i hi => Nat.find_min hex hi
  have h2 : 2 * r m = r m' := by rw [hm']; exact hrsucc m'
  rw [h2]
  have hm'lt : m' < m := by omega
  push Not at hmin
  obtain ⟨hp', ht'⟩ := hmin m' hm'lt
  obtain ⟨hp0, -⟩ := hmin 0 (by omega)
  exact ⟨hrle m', ⟨d m', (hd m').norm_le, hp', ht'⟩, d 0, (hd 0).norm_le.trans (by simp [hr]),
    by simpa [hr] using hp0⟩

/-- The data of one ARqpIDA iteration. -/
private structure ARState (n : ℕ) where
  x : EuclideanSpace ℝ (Fin n)
  σ : ℝ
  δ : ℕ → ℝ
  δ₁ : ℕ → ℝ
  δs : ℕ → ℝ
  h : ℕ → ℝ
  dd : ℕ → EuclideanSpace ℝ (Fin n)
  jk : ℕ
  s : EuclideanSpace ℝ (Fin n)
  acc : Prop

variable (P : ARqpIDAParams) (ε : ℕ → ℝ) (O : ℝⁿ → (ℕ → ℝ) → FormalMultilinearSeries ℝ ℝⁿ ℝ)
  (Lb : ℝ)

/-- The Step-1.2 test (13.1.53) of a state. -/
private def arPassS (a : ARState n) (j : ℕ) : Prop :=
  (O a.x a.h).taylorDecrement j (a.dd j) ≤ P.ς * ε j * a.δ₁ j ^ j / j ! / 2

/-- Step 2 of a state. -/
private structure ARStep2S (a : ARState n) : Prop where
  /-- See `ARqpStep2`. -/
  jk_mem : a.jk ∈ Finset.Icc 1 P.q
  /-- See `ARqpStep2`. -/
  not_pass : ¬ arPassS P ε O a a.jk
  /-- See `ARqpStep2`. -/
  pass_lt : ∀ j ∈ Finset.Icc 1 P.q, j < a.jk → arPassS P ε O a j
  /-- See `ARqpStep2`. -/
  radius_gt : ∀ j ∈ Finset.Icc 1 P.q, a.jk < j → a.δ₁ j = a.δ j
  /-- See `ARqpStep2`. -/
  model_dec : P.ς * ε a.jk * a.δ₁ a.jk ^ a.jk / a.jk ! / 4 ≤
    regularizedModel (O a.x a.h) P.p a.σ 0 - regularizedModel (O a.x a.h) P.p a.σ (a.dd a.jk)
  /-- See `ARqpStep2`. -/
  dec_le : regularizedModel (O a.x a.h) P.p a.σ 0 - regularizedModel (O a.x a.h) P.p a.σ
      (a.dd a.jk) ≤
    regularizedModel (O a.x a.h) P.p a.σ 0 - regularizedModel (O a.x a.h) P.p a.σ a.s
  /-- See `ARqpStep2`. -/
  radii : (1 ≤ ‖a.s‖ ∧ a.δs = a.δ₁) ∨ ∀ ℓ ∈ Finset.Icc 1 P.q, a.δs ℓ ∈ Set.Ioc 0 1 ∧
    ∃ dm, IsApproxMeasureStep
        ((ftaylorSeries ℝ (regularizedModel (O a.x a.h) P.p a.σ) a.s).taylorDecrement ℓ)
        (a.δs ℓ) {e | a.x + a.s + e ∈ (univ : Set ℝⁿ)} P.ς dm ∧
      (ftaylorSeries ℝ (regularizedModel (O a.x a.h) P.p a.σ) a.s).taylorDecrement ℓ dm ≤
        P.ς * P.θ * ε ℓ * a.δs ℓ ^ ℓ / ℓ !
  /-- See `ARqpStep2`. -/
  acc_iff : a.acc ↔ ‖a.s‖ < 1 ∧ ∃ i ∈ Finset.Icc 1 P.p, P.κs * ‖a.s‖ ^ (P.p - i + 1) < a.h i

/-- Steps 1–2 of a state, the invariants and the radii control. -/
private structure ARLocal (a : ARState n) : Prop where
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  σ_ge : P.σmin ≤ a.σ
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  δ_mem : ∀ j ∈ Finset.Icc 1 P.q, 0 < a.δ j ∧ a.δ j ≤ 1
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  h_mem : ∀ i ∈ Finset.Icc 1 P.p, 0 < a.h i ∧ a.h i ≤ P.κh
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  radius_pos : ∀ j ∈ Finset.Icc 1 P.q, 0 < a.δ₁ j
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  radius_le : ∀ j ∈ Finset.Icc 1 P.q, a.δ₁ j ≤ a.δ j
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  halving : ∀ j ∈ Finset.Icc 1 P.q, a.δ₁ j < a.δ j → 2 * a.δ₁ j ≤ a.δ j ∧
    (∃ d', ‖d'‖ ≤ 2 * a.δ₁ j ∧ a.x + d' ∈ (univ : Set ℝⁿ) ∧
      P.ς * ε j * (2 * a.δ₁ j) ^ j / j ! / 2 < (O a.x a.h).taylorDecrement j d' ∧
      regularizedModel (O a.x a.h) P.p a.σ 0 - regularizedModel (O a.x a.h) P.p a.σ d' <
        P.ς * ε j * (2 * a.δ₁ j) ^ j / j ! / 4) ∧
    ∃ d₀, ‖d₀‖ ≤ a.δ j ∧ a.x + d₀ ∈ (univ : Set ℝⁿ) ∧
      P.ς * ε j * a.δ j ^ j / j ! / 2 < (O a.x a.h).taylorDecrement j d₀
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  dyadic : ∀ j ∈ Finset.Icc 1 P.q, ∃ m : ℕ, a.δ₁ j = a.δ j / 2 ^ m
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  witness : ∀ j ∈ Finset.Icc 1 P.q, IsApproxMeasureStep ((O a.x a.h).taylorDecrement j)
    (a.δ₁ j) {e | a.x + e ∈ (univ : Set ℝⁿ)} P.ς (a.dd j)
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  acc_of_pass : (∀ j ∈ Finset.Icc 1 P.q, arPassS P ε O a j) → a.acc
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  step2 : (∃ j ∈ Finset.Icc 1 P.q, ¬ arPassS P ε O a j) → ARStep2S P ε O a
  /-- See `ARqpDAStep` and `RadiiControl`. -/
  rc : ¬ a.acc → ‖a.s‖ < 1 → (∀ j ∈ Finset.Icc 1 (min 2 P.q), a.δs j = 1) ∧
    ∀ j ∈ Finset.Icc 3 P.q, P.ς * P.θ * ε j / (24 * max Lb a.σ) ≤ a.δs j

/-- Steps 1–2 of ARqpIDA can be performed at every state satisfying the invariants, with the
radii control (13.1.69)–(13.1.70). -/
private theorem exists_arLocal (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hLb1 : 1 ≤ Lb)
    (hO : ∀ y h', (∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh) →
      ∀ ℓ ∈ Finset.Icc 1 P.p, ‖O y h' ℓ‖ ≤ Lb)
    (x : ℝⁿ) {σ : ℝ} (hσ : P.σmin ≤ σ) {δ h : ℕ → ℝ}
    (hδ : ∀ j ∈ Finset.Icc 1 P.q, 0 < δ j ∧ δ j ≤ 1)
    (hh : ∀ i ∈ Finset.Icc 1 P.p, 0 < h i ∧ h i ≤ P.κh) :
    ∃ δ₁ δs dd jk s, ∃ acc : Prop, ARLocal P ε O Lb ⟨x, σ, δ, δ₁, δs, h, dd, jk, s, acc⟩ := by
  classical
  have hLb : 0 < Lb := zero_lt_one.trans_le hLb1
  set D := O x h
  have hD := hO x h hh
  have hσ0 : 0 < σ := P.σmin_pos.trans_le hσ
  have H : ∀ j ∈ Finset.Icc 1 P.q, ∃ δ₁ d, 0 < δ₁ ∧ δ₁ ≤ δ j ∧
      IsApproxMeasureStep (D.taylorDecrement j) δ₁ univ P.ς d ∧
      (D.taylorDecrement j d ≤ P.ς * ε j * δ₁ ^ j / j ! / 2 ∨
        P.ς * ε j * δ₁ ^ j / j ! / 4 ≤ regularizedModel D P.p σ 0 - regularizedModel D P.p σ d) ∧
      (δ₁ < δ j → 2 * δ₁ ≤ δ j ∧
        (∃ d', ‖d'‖ ≤ 2 * δ₁ ∧ P.ς * ε j * (2 * δ₁) ^ j / j ! / 2 < D.taylorDecrement j d' ∧
          regularizedModel D P.p σ 0 - regularizedModel D P.p σ d' <
            P.ς * ε j * (2 * δ₁) ^ j / j ! / 4) ∧
        ∃ d₀, ‖d₀‖ ≤ δ j ∧ P.ς * ε j * δ j ^ j / j ! / 2 < D.taylorDecrement j d₀) ∧
      ∃ m : ℕ, δ₁ = δ j / 2 ^ m :=
    fun j hj => exists_halving hσ0.le hLb hD ((Finset.mem_Icc.1 hj).2.trans P.q_le_p) P.ς_pos
      P.ς_le_one (hε j hj).1 (hδ j hj).1 (hδ j hj).2
  choose! δ₁h ddh hH using H
  have H0 : ∀ j ∈ Finset.Icc 1 P.q, ∃ d, IsApproxMeasureStep (D.taylorDecrement j) (δ j) univ
      P.ς d := fun j hj => exists_isApproxMeasureStep_taylorDecrement D j isClosed_univ
        (mem_univ 0) (hδ j hj).1.le P.ς_le_one
  choose! d0 hd0 using H0
  by_cases hex : ∃ j, j ∈ Finset.Icc 1 P.q ∧
      ¬ D.taylorDecrement j (ddh j) ≤ P.ς * ε j * δ₁h j ^ j / j ! / 2
  · set jk := Nat.find hex
    obtain ⟨hjk, hfjk⟩ := Nat.find_spec hex
    have hjkmin : ∀ j ∈ Finset.Icc 1 P.q, j < jk →
        D.taylorDecrement j (ddh j) ≤ P.ς * ε j * δ₁h j ^ j / j ! / 2 := fun j hj hlt => by
      by_contra hc; exact Nat.find_min hex hlt ⟨hj, hc⟩
    set δ₁ : ℕ → ℝ := fun j => if jk < j then δ j else δ₁h j
    set dd : ℕ → ℝⁿ := fun j => if jk < j then d0 j else ddh j
    have hp : 1 ≤ P.p := P.one_le_p
    obtain ⟨s, δs0, dm, hmin, hδs0, hδs2, hδs3, hbr⟩ := exists_highOrderStep (D := D)
      (p := P.p) (q := P.q) (σ := σ) (L := Lb) hp P.q_le_p hσ0 hLb.le
      (fun i hi => hD i (Finset.Icc_subset_Icc (by norm_num) le_rfl hi)) P.θ_pos P.ς_pos
      P.ς_le_one fun j hj => (hε j hj).1
    set δs : ℕ → ℝ := if 1 ≤ ‖s‖ then δ₁ else δs0
    refine ⟨δ₁, δs, dd, jk, s, ‖s‖ < 1 ∧ ∃ i ∈ Finset.Icc 1 P.p, P.κs * ‖s‖ ^ (P.p - i + 1) < h i,
      ⟨hσ, hδ, hh, fun j hj => ?_, fun j hj => ?_, fun j hj hlt => ?_, fun j hj => ?_,
        fun j hj => ?_, fun hpass => ?_, fun _ => ?_, fun _ hs1 => ?_⟩⟩
    · dsimp only; simp only [δ₁]; split_ifs
      · exact (hδ j hj).1
      · exact (hH j hj).1
    · dsimp only; simp only [δ₁]; split_ifs
      · exact le_rfl
      · exact (hH j hj).2.1
    · dsimp only at hlt ⊢
      simp only [δ₁] at hlt ⊢
      split_ifs at hlt ⊢ with hj'
      · exact absurd hlt (lt_irrefl _)
      · obtain ⟨h1, ⟨d', hd'n, hd'T, hd'm⟩, d₀, hd₀n, hd₀⟩ := (hH j hj).2.2.2.2.1 hlt
        exact ⟨h1, ⟨d', hd'n, mem_univ _, hd'T, hd'm⟩, d₀, hd₀n, mem_univ _, hd₀⟩
    · dsimp only; simp only [δ₁]; split_ifs
      · exact ⟨0, by rw [pow_zero, div_one]⟩
      · exact (hH j hj).2.2.2.2.2
    · dsimp only
      rw [setOf_add_mem_univ]
      simp only [δ₁, dd]; split_ifs
      · exact hd0 j hj
      · exact (hH j hj).2.2.1
    · exfalso
      have := hpass jk hjk
      simp only [arPassS, δ₁, dd, lt_irrefl, ite_false] at this
      exact hfjk this
    · have hpass_jk : ¬ arPassS P ε O ⟨x, σ, δ, δ₁, δs, h, dd, jk, s,
          ‖s‖ < 1 ∧ ∃ i ∈ Finset.Icc 1 P.p, P.κs * ‖s‖ ^ (P.p - i + 1) < h i⟩ jk := by
        simp only [arPassS, δ₁, dd, lt_irrefl, ite_false]; exact hfjk
      have hdec : P.ς * ε jk * δ₁h jk ^ jk / jk ! / 4 ≤
          regularizedModel D P.p σ 0 - regularizedModel D P.p σ (ddh jk) :=
        (hH jk hjk).2.2.2.1.resolve_left hfjk
      have hminv := isMinOn_iff.1 hmin (ddh jk) (mem_univ _)
      refine ⟨hjk, hpass_jk, fun j hj hlt => ?_, fun j hj hlt => ?_, ?_, ?_, ?_, Iff.rfl⟩
      · dsimp only at hlt
        have hlt' : ¬ jk < j := by omega
        simp only [arPassS, δ₁, dd, hlt', ite_false]; exact hjkmin j hj hlt
      · dsimp only at hlt ⊢; simp only [δ₁, hlt, ite_true]
      · dsimp only; simp only [δ₁, dd, lt_irrefl, ite_false]; exact hdec
      · dsimp only; simp only [dd, lt_irrefl, ite_false]
        linarith
      · dsimp only
        by_cases hs1 : 1 ≤ ‖s‖
        · left; exact ⟨hs1, by simp only [δs, hs1, ite_true]⟩
        · right
          intro ℓ hℓ
          have hδsℓ : δs ℓ = δs0 ℓ := by simp only [δs, hs1, ite_false]
          rw [hδsℓ]
          obtain ⟨happ, hle⟩ := (hbr.resolve_left hs1) ℓ hℓ
          refine ⟨⟨(hδs0 ℓ hℓ).1, (hδs0 ℓ hℓ).2⟩, dm ℓ, ?_, hle⟩
          have : {e | x + s + e ∈ (univ : Set ℝⁿ)} = univ := by ext; simp
          rw [this]; exact happ
    · dsimp only at hs1 ⊢
      have hs1' : ¬ 1 ≤ ‖s‖ := not_le.2 hs1
      have hδsℓ : ∀ ℓ, δs ℓ = δs0 ℓ := fun ℓ => by simp only [δs, hs1', ite_false]
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
        rw [hδsℓ]
        exact hδs2 j (Finset.mem_Icc.2 ⟨hj1, hj2.trans (min_le_right _ _)⟩)
          (hj2.trans (min_le_left _ _))
      · rw [hδsℓ, hδs3 j hj]
        have hεj := hε j (Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hj).1; omega,
          (Finset.mem_Icc.1 hj).2⟩)
        have hM : 1 ≤ max Lb σ := hLb1.trans (le_max_left _ _)
        have hς := P.ς_pos; have hς1 := P.ς_le_one; have hθ := P.θ_pos; have hθ1 := P.θ_lt_one
        have h1 : P.ς * P.θ * ε j / (24 * max Lb σ) ≤ 1 := by
          rw [div_le_one (by positivity)]
          have : P.ς * P.θ * ε j ≤ 1 * 1 * 1 :=
            mul_le_mul (mul_le_mul hς1 hθ1.le hθ.le zero_le_one) hεj.2 hεj.1.le (by norm_num)
          linarith
        refine le_min h1 ?_
        refine div_le_div_of_nonneg_left (by have := hεj.1; positivity) (by positivity) ?_
        have := le_max_left Lb σ; have := le_max_right Lb σ
        linarith
  · push Not at hex
    refine ⟨δ₁h, fun _ => 1, ddh, 1, 0, True, ⟨hσ, hδ, hh, fun j hj => (hH j hj).1,
      fun j hj => (hH j hj).2.1, fun j hj hlt => ?_, fun j hj => (hH j hj).2.2.2.2.2,
      fun j hj => ?_, fun _ => trivial,
      fun ⟨j, hj, hf⟩ => absurd (hex j hj) hf, fun h' => absurd trivial h'⟩⟩
    · dsimp only at hlt ⊢
      obtain ⟨h1, ⟨d', hd'n, hd'T, hd'm⟩, d₀, hd₀n, hd₀⟩ := (hH j hj).2.2.2.2.1 hlt
      exact ⟨h1, ⟨d', hd'n, mem_univ _, hd'T, hd'm⟩, d₀, hd₀n, mem_univ _, hd₀⟩
    · dsimp only; rw [setOf_add_mem_univ]; exact (hH j hj).2.2.1

/-- The transition of an ARqpIDA run from a state satisfying Steps 1–2. -/
private theorem exists_arNext (f : ℝⁿ → ℝ) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hLb1 : 1 ≤ Lb)
    (hO : ∀ y h', (∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh) →
      ∀ ℓ ∈ Finset.Icc 1 P.p, ‖O y h' ℓ‖ ≤ Lb)
    (a : ARState n) (ha : ARLocal P ε O Lb a) :
    ∃ b : ARState n, ARLocal P ε O Lb b ∧ ∀ (r : ℕ → ARState n) (k : ℕ), r k = a →
      r (k + 1) = b →
      ARqpDAStep univ P ε (fun i => (r i).x) (fun i => (r i).σ) (fun i => (r i).δ)
        (fun i => (r i).δ₁) (fun i => (r i).δs) (fun i => (r i).h) (fun i => O (r i).x (r i).h)
        (fun i => (r i).dd) (fun i => (r i).jk) (fun i => (r i).s) (fun i => (r i).acc)
        (arqpIDARatio f P (fun i => O (r i).x (r i).h) (fun i => (r i).x) (fun i => (r i).s)) k ∧
      RadiiControl P ε Lb (fun i => (r i).σ) (fun i => (r i).δs) (fun i => (r i).s)
        (fun i => (r i).acc) k := by
  classical
  set ρ := reductionRatio f a.x a.s ((O a.x a.h).taylorDecrement P.p a.s) with hρ
  set x' := if a.acc then a.x else if P.η₁ ≤ ρ then a.x + a.s else a.x
  set σ' := if a.acc then a.σ else if P.η₁ ≤ ρ then a.σ else P.γ₂ * a.σ
  set δ' := if a.acc then a.δ else if P.η₁ ≤ ρ ∧ ‖a.s‖ < 1 then a.δs else a.δ₁
  set h' : ℕ → ℝ := if a.acc then fun i => P.γh * a.h i else a.h
  have hσpos : 0 < a.σ := P.σmin_pos.trans_le ha.σ_ge
  have hstep2 : ¬ a.acc → ARStep2S P ε O a := fun hk => ha.step2 (by
    by_contra hc; push Not at hc; exact hk (ha.acc_of_pass hc))
  have hσ' : P.σmin ≤ σ' := by
    simp only [σ']; split_ifs
    · exact ha.σ_ge
    · exact ha.σ_ge
    · exact ha.σ_ge.trans (le_mul_of_one_le_left hσpos.le P.one_le_γ₂)
  have hδ' : ∀ j ∈ Finset.Icc 1 P.q, 0 < δ' j ∧ δ' j ≤ 1 := by
    intro j hj
    simp only [δ']; split_ifs with h1 h2
    · exact ha.δ_mem j hj
    · exact ((hstep2 h1).radii.resolve_left (fun h' => absurd h'.1 (not_le.2 h2.2)) j hj).1
    · exact ⟨ha.radius_pos j hj, (ha.radius_le j hj).trans (ha.δ_mem j hj).2⟩
  have hh' : ∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh := by
    intro i hi
    simp only [h']; split_ifs
    · obtain ⟨h1, h2⟩ := ha.h_mem i hi
      exact ⟨mul_pos P.γh_pos h1, (mul_le_of_le_one_left h1.le P.γh_lt_one.le).trans h2⟩
    · exact ha.h_mem i hi
  obtain ⟨δ₁', δs', dd', jk', s', acc', hloc⟩ :=
    exists_arLocal P ε O Lb hε hLb1 hO x' hσ' hδ' hh'
  refine ⟨⟨x', σ', δ', δ₁', δs', h', dd', jk', s', acc'⟩, hloc, fun r k hra hrb => ?_⟩
  have hpass : ∀ j, arPass P ε (fun i => O (r i).x (r i).h) (fun i => (r i).δ₁)
      (fun i => (r i).dd) k j ↔ arPassS P ε O a j := by
    intro j; simp only [arPass, arPassS, hra]
  have hratio : arqpIDARatio f P (fun i => O (r i).x (r i).h) (fun i => (r i).x)
      (fun i => (r i).s) k = ρ := by simp only [arqpIDARatio, hra, hρ]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [hra]; exact ha.radius_pos
  · simp only [hra]; exact ha.radius_le
  · simp only [arModelDec, hra]; exact ha.halving
  · simp only [hra]; exact ha.dyadic
  · simp only [hra]; exact ha.witness
  · intro hp; simp only [hra]; exact ha.acc_of_pass fun j hj => (hpass j).1 (hp j hj)
  · rintro ⟨j, hj, hf⟩
    have h2 := ha.step2 ⟨j, hj, (hpass j).not.1 hf⟩
    refine ⟨?_, ?_, fun j hj hlt => ?_, fun j hj hlt => ?_, ?_, by simp, ?_, ?_, ?_⟩
    · simp only [hra]; exact h2.jk_mem
    · simp only [hra] at hpass ⊢; exact (hpass _).not.2 h2.not_pass
    · simp only [hra] at hlt; exact (hpass j).2 (h2.pass_lt j hj hlt)
    · simp only [hra] at hlt ⊢; exact h2.radius_gt j hj hlt
    · simp only [arModelDec, hra]; exact h2.model_dec
    · simp only [arModelDec, hra]; exact h2.dec_le
    · simp only [hra]; exact h2.radii
    · simp only [hra]; exact h2.acc_iff
  · intro hk
    simp only [hra] at hk
    rw [hratio]
    simp only [hra, hrb, x', σ', hk, ite_false]
    refine ⟨rfl, ⟨fun h2 => ?_, fun h1 _ => ?_, fun h1 => ?_⟩⟩
    · rw [ite_eq_left (P.η₁_le_η₂.trans h2)]
      exact ⟨max_le ha.σ_ge (mul_le_of_le_one_left hσpos.le P.γ₁_le_one), le_rfl⟩
    · rw [ite_eq_left h1]
      exact ⟨le_rfl, le_mul_of_one_le_left hσpos.le P.one_le_γ₂⟩
    · rw [ite_eq_right (not_le.2 h1)]
      exact ⟨le_rfl, mul_le_mul_of_nonneg_right P.γ₂_le_γ₃ hσpos.le⟩
  · intro hk
    simp only [hra] at hk
    rw [hratio]
    simp only [hra, hrb, δ', hk, ite_false]
  · intro hk; simp only [hra] at hk; simp only [hra, hrb, h', hk, ite_false]
  · intro hk hlt; simp only [hra] at hk; rw [hratio] at hlt
    simp only [hra, hrb, x', h', hk, ite_false, ite_eq_right (not_le.2 hlt)]
  · intro hk; simp only [hra] at hk; simp only [hra, hrb, x', hk, ite_true]
  · intro hk; simp only [hra] at hk; simp only [hra, hrb, δ', hk, ite_true]
  · intro hk; simp only [hra] at hk; simp only [hra, hrb, σ', hk, ite_true]
  · intro hk i; simp only [hra] at hk; simp only [hra, hrb, h', hk, ite_true]
  · exact RadiiControl.of_book hε hLb1 fun hk hs1 => by
      simp only [hra] at hk hs1 ⊢; exact ha.rc hk hs1

variable {P ε}

/-- **ARqpIDA iterations exist from any admissible state** ([cartis2022evaluation], existence
part of Lemmas 13.1.11 and 13.1.12): under f.D0pL, for tolerances `ε ∈ (0, 1]^q`, oracle
constants `κ_{∇,i} ≥ 0`, every deterministic oracle `O` satisfying (13.1.2) for all accuracies
`h ∈ (0, κ_h]^p`, and a starting state (`x₀`, a weight `σ' ≥ σ_min`, radii `δ' ∈ (0, 1]^q`,
accuracies `h' ∈ (0, κ_h]^p`), there are sequences starting at that state all of whose iterations
are ARqpIDA steps (`ARqpDAStep` on `X = univ`, with `D_k = O(x_k, h_k)`) satisfying the radii
control (13.1.69)–(13.1.70). With the initial state of `P` this gives `exists_algorithm_13_1_2`;
other states are used to continue runs. -/
theorem exists_arqpDA_steps {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {L : ℕ → ℝ}
    (hf : AssumptionD0pL f P.p L) (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1)
    (hκg : ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ κg i) (x₀ : ℝⁿ) {σ' : ℝ} (hσ' : P.σmin ≤ σ')
    {δ' h' : ℕ → ℝ} (hδ' : ∀ j ∈ Finset.Icc 1 P.q, 0 < δ' j ∧ δ' j ≤ 1)
    (hh' : ∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh)
    (hO : ∀ y h', (∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh) →
      JetApprox (ftaylorSeries ℝ f y) (O y h') P.p (fun i => κg i * h' i)) :
    ∃ (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ) (dd : ℕ → ℕ → ℝⁿ)
      (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop),
      x 0 = x₀ ∧ σ 0 = σ' ∧ δ 0 = δ' ∧ h 0 = h' ∧
        (∀ k, ∀ i ∈ Finset.Icc 1 P.p, 0 < h k i ∧ h k i ≤ P.κh) ∧
        (∀ k, ARqpDAStep univ P ε x σ δ δ₁ δs h (fun i => O (x i) (h i)) dd jk s acc
          (arqpIDARatio f P (fun i => O (x i) (h i)) x s) k) ∧
        ∀ k, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k := by
  set Lb := lipMax L P.p + ordMax P.p κg * P.κh
  have hLb1 : 1 ≤ Lb := by
    have := hf.one_le_lipMax; have := ordMax_nonneg hκg; have := P.κh_nonneg; nlinarith
  have hO' : ∀ y h', (∀ i ∈ Finset.Icc 1 P.p, 0 < h' i ∧ h' i ≤ P.κh) →
      ∀ ℓ ∈ Finset.Icc 1 P.p, ‖O y h' ℓ‖ ≤ Lb := fun y h' hh ℓ hℓ =>
    hf.norm_le_of_jetApprox (hO y h' hh) hκg (fun i hi => (hh i hi).1.le)
      (fun i hi => (hh i hi).2) hℓ
  obtain ⟨δ₁₀, δs₀, dd₀, jk₀, s₀, acc₀, h₀⟩ := exists_arLocal P ε O Lb hε hLb1 hO' x₀
    hσ' hδ' hh'
  obtain ⟨r, hr0, hr⟩ := exists_run_of_forall_exists_of_invariant (α := ARState n)
    (init := fun a => a = ⟨x₀, σ', δ', δ₁₀, δs₀, h', dd₀, jk₀, s₀, acc₀⟩)
    (inv := fun _ a => ARLocal P ε O Lb a) (stop := fun _ _ => False)
    (step := fun k a b => ∀ (r : ℕ → ARState n), r k = a → r (k + 1) = b →
      ARqpDAStep univ P ε (fun i => (r i).x) (fun i => (r i).σ) (fun i => (r i).δ)
        (fun i => (r i).δ₁) (fun i => (r i).δs) (fun i => (r i).h) (fun i => O (r i).x (r i).h)
        (fun i => (r i).dd) (fun i => (r i).jk) (fun i => (r i).s) (fun i => (r i).acc)
        (arqpIDARatio f P (fun i => O (r i).x (r i).h) (fun i => (r i).x) (fun i => (r i).s)) k ∧
      RadiiControl P ε Lb (fun i => (r i).σ) (fun i => (r i).δs) (fun i => (r i).s)
        (fun i => (r i).acc) k)
    ⟨_, rfl⟩ (fun a ha => ha ▸ h₀) (fun k a ha _ => by
      obtain ⟨b, hb, hs⟩ := exists_arNext P ε O Lb f hε hLb1 hO' a ha
      exact ⟨b, hb, fun r => hs r k⟩)
  exact ⟨fun i => (r i).x, fun i => (r i).σ, fun i => (r i).δ, fun i => (r i).δ₁,
    fun i => (r i).δs, fun i => (r i).h, fun i => (r i).dd, fun i => (r i).jk, fun i => (r i).s,
    fun i => (r i).acc, by simp only [hr0], by simp only [hr0], by simp only [hr0],
    by simp only [hr0], fun k => (hr k fun _ _ h => h).1.h_mem,
    fun k => ((hr k fun _ _ h => h).2 r rfl rfl).1, fun k => ((hr k fun _ _ h => h).2 r rfl rfl).2⟩

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
    exists_arqpDA_steps O hf hε hκg x₀ P.σmin_le_σ₀ (fun j hj => P.δ₀_mem j hj)
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
