import Numlib.Analysis.SpecialFunctions.Pow.Real
import Numlib.Optimization.Complexity.SlowExample.ARp
import Numlib.Optimization.ModelBased.ARpRun
import NumlibSurface.CartisGouldToint.Chapter03.Section03

/-!
# Cartis–Gould–Toint §4.1: The ARp algorithm and its complexity

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §4.1: the adaptive-regularization
algorithm ARp with `p`-th order Taylor models on `ℝⁿ = EuclideanSpace ℝ (Fin n)`.

The model (4.1.2) is `m_k(s) = T_{f,p}(x_k, s) + σ_k/(p+1)! ‖s‖^{p+1}`, the backbone's
`Optimization.regularizedModel (ftaylorSeries ℝ f x_k) p σ_k`; the ratio (4.1.15) is
`Optimization.taylorRatio f p x s`. ARp is the backbone run predicate `Optimization.IsARpRun` (an
instance of the generic adaptive-regularization run `Optimization.IsARRun`) with the Step-1 test
(4.1.5)–(4.1.9); the order of criticality sought is `q = 1, 2, 3` according to the number of
finite tolerances (`arpOrder`).

## Main definitions

* `ARpParams` — the constants of Step 0.
* `AssumptionDpL` — assumption f.DpL (4.1.17).
* `smallCurvatureSet`, `IsApproxThirdOrderMinimizer` — (4.1.3)–(4.1.4).
* `arpStopTest`, `arpCurvSet`, `algorithm_4_1_1` — Algorithm 4.1.1 (the sets `𝓜_k` of Step 0 and
  (4.1.14) are functions of the run).
* `sigmaMaxARp`, `kappaARp₁`, `kappaARp₂`, `kappaARp₃`, `kappaSARp`, `kappaCARp` — the constants
  (4.1.19), (4.1.32), (4.1.34), (4.1.36), (4.1.45), (4.1.46).

## Main results

* `exists_algorithm_4_1_1` — runs exist for `ε₃ = +∞`; `not_exists_algorithm_4_1_1_third_order` —
  they need not exist for `ε₃ < +∞`.
* Lemmas 4.1.1–4.1.4 (`lemma_4_1_1`, …, `lemma_4_1_4_iii`).
* `theorem_4_1_5_i`, `theorem_4_1_5_ii`, `theorem_4_1_5_iii` — Theorem 4.1.5, one statement per
  order of criticality.
* `theorem_4_1_6_i`, `theorem_4_1_6_ii`, `theorem_4_1_6_iii` — Theorem 4.1.6 (sharpness).

## Deviations from the book

* **Step 1, third-order branch** (4.1.8)–(4.1.9): the book also requires `𝓜_k ≠ ∅`. With that
  requirement a run can get stuck at a point satisfying (4.1.5) and (4.1.7) with `𝓜_k = ∅`, and the
  proof of Theorem 4.1.5 uses the vacuous reading (`∀ d ∈ 𝓜_k`), which is the one formalized.
  Likewise (4.1.13) is required for all `d ∈ 𝓜_{k+1}` (vacuous when the set is empty).
* **Well-posedness**: with `ε₃ < ∞` an admissible step need not exist when the test fails
  (`not_exists_algorithm_4_1_1_third_order`); Theorem 4.1.5 (iii) is a statement about runs.
* **Theorem 4.1.5** is stated for `(ε₁, ε₂, ε₃) ∈ (0, 1]³` with one constant `κ^S` mixing the
  three orders; it is split by order of criticality, each part with the constants of the active
  orders only (and without `ε ≤ 1`, which is not needed).
* **Theorem 4.1.6** (the book defers the proof to §12.2.2.4) is proved on the one-dimensional data
  of Theorem 12.2.15 (`Optimization.exists_slowTaylorOrder_interpolant`): the iterations are exact
  global model minimizations with `σ_k = σ₀` and `ρ_k = 1`. The run terminates at iteration
  `⌈ε^{-(p+1)/(p-q+1)}⌉` (`+1` evaluations). Part (iii) assumes `σ₀ ≤ (p-2)! min(θ₂, θ₃)`: for
  other constants the global model minimizer need not satisfy (4.1.13), and the claim is unproved.
  In the proof of the book (`λ_min = f_k^{(2)} = ε + ω_k`) the sign is wrong: `λ_min = -(ε + ω_k)`.
  The restriction is sufficient, not necessary; it interacts with the vacuous reading of `𝓜_k`:
  for other constants the sets `𝓜_{k+1}` of the third-order example may be empty, and the run then
  stops early (vacuous reading) or never (literal reading). In part (iii) the termination index
  is also the first iterate satisfying the true criterion (4.1.3)–(4.1.4). The run mechanism on
  spike data is the backbone's `Optimization.arp_ridge_run`
  (`Numlib.Optimization.Complexity.SlowExample.ARp`).
* §4.1.3 ("A TRp algorithm?") contains no numbered statement and defines no algorithm.
-/

open Set Finset Optimization
open Optimization hiding ARParams ARpParams
open scoped Nat RealInnerProductSpace

namespace CartisGouldToint.Chapter04

variable {n : ℕ}

/-! ### The algorithm -/

/-- The constants of Algorithm 4.1.1 ([cartis2022evaluation], Step 0): those of
`Optimization.ARpParams` (`σ₀ > 0`, `0 < η₁ ≤ η₂ < 1`, `0 < γ₁ < 1 < γ₂ ≤ γ₃`,
`θ₁, θ₂, θ₃ ∈ (0, 1]`), with `σ_min ∈ (0, σ₀]` and `γ₂ < γ₃`. -/
structure ARpParams extends Optimization.ARpParams where
  /-- `σ_min > 0`. -/
  σmin_pos : 0 < σmin
  /-- `γ₂ < γ₃`. -/
  γ₂_lt_γ₃ : γ₂ < γ₃

/-- The adaptive-regularization constants of ARp as those of AR1 (2.4.2). -/
def ARpParams.toAR1Params (P : ARpParams) : Chapter02.ARParams where
  toARParams := P.toARParams
  σmin_pos := P.σmin_pos
  γ₂_lt_γ₃ := P.γ₂_lt_γ₃

/-- **Assumption f.DpL** of [cartis2022evaluation] (4.1.17): `f` is `p` times continuously
differentiable on `ℝⁿ` and its `p`-th derivative tensor is Lipschitz continuous (in the tensor
norm, which is Mathlib's operator norm) with a constant `L_{f,p} ≥ 1`. -/
structure AssumptionDpL (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (L : ℝ) : Prop where
  /-- `f` is `p` times continuously differentiable. -/
  contDiff : ContDiff ℝ p f
  /-- The Lipschitz constant satisfies `L_{f,p} ≥ 1`. -/
  one_le : 1 ≤ L
  /-- `∇^p f` is `L`-Lipschitz (4.1.17). -/
  lipschitz : ∀ x y, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖

namespace AssumptionDpL

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {L : ℝ}

theorem nonneg (h : AssumptionDpL f p L) : 0 ≤ L :=
  zero_le_one.trans h.one_le

/-- **Bridge to the backbone**: under f.DpL, `IteratedFDerivLipschitzOn f p L univ`. -/
theorem iteratedFDerivLipschitzOn (h : AssumptionDpL f p L) :
    IteratedFDerivLipschitzOn f p L univ :=
  iteratedFDerivLipschitzOn_iff.2 fun x _ y _ => h.lipschitz x y

/-- f.DpL with a larger constant. -/
theorem mono (h : AssumptionDpL f p L) {L' : ℝ} (hL : L ≤ L') : AssumptionDpL f p L' :=
  ⟨h.contDiff, h.one_le.trans hL, fun x y =>
    (h.lipschitz x y).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))⟩

end AssumptionDpL

/-- f.DpL from a `C^p` function whose `p`-th derivative is `L`-Lipschitz, `L ≥ 1`. -/
theorem assumptionDpL_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {L : ℝ} :
    AssumptionDpL f p L ↔ ContDiff ℝ p f ∧ 1 ≤ L ∧ IteratedFDerivLipschitzOn f p L univ :=
  ⟨fun h => ⟨h.contDiff, h.one_le, h.iteratedFDerivLipschitzOn⟩, fun ⟨h1, h2, h3⟩ =>
    ⟨h1, h2, fun x y => iteratedFDerivLipschitzOn_iff.1 h3 x (mem_univ _) y (mem_univ _)⟩⟩

/-- For `p = 2`, f.DpL is f.HL. -/
theorem assumptionDpL_two_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ} :
    AssumptionDpL f 2 L ↔ Chapter03.AssumptionHL f L :=
  ⟨fun h => ⟨h.contDiff, h.one_le, h.lipschitz⟩, fun h => ⟨h.contDiff, h.one_le, h.lipschitz⟩⟩

/-- For `p = 1`, f.DpL is f.gL. -/
theorem assumptionDpL_one_iff {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ} :
    AssumptionDpL f 1 L ↔ Chapter02.AssumptionGL f L := by
  have hg : ∀ x y, ‖gradient f x - gradient f y‖ = ‖iteratedFDeriv ℝ 1 f x -
      iteratedFDeriv ℝ 1 f y‖ := fun x y => by
    rw [norm_iteratedFDeriv_one_sub, gradient_eq_toDualReal_symm, ← map_sub,
      LinearIsometryEquiv.norm_map]
  constructor
  · intro h
    exact ⟨h.contDiff, h.one_le, fun x y => (hg x y).trans_le (h.lipschitz x y)⟩
  · intro h
    exact ⟨h.contDiff, h.one_le, fun x y => (hg x y).symm.trans_le (h.lipschitz x y)⟩

/-- The set `𝒵_ε` of (4.1.4): the unit directions of curvature at most `ε₂` in absolute value,
`{d | ‖d‖ = 1 ∧ |∇²f(x)[d]²| ≤ ε₂}` (also the set `𝓜₀` of Step 0). -/
def smallCurvatureSet (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (ε₂ : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  smallCurvatureDirections (iteratedFDeriv ℝ 2 f x) ε₂

theorem mem_smallCurvatureSet {f : EuclideanSpace ℝ (Fin n) → ℝ} {x d : EuclideanSpace ℝ (Fin n)}
    {ε₂ : ℝ} :
    d ∈ smallCurvatureSet f x ε₂ ↔ ‖d‖ = 1 ∧ |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ ε₂ :=
  Iff.rfl

/-- An **`ε`-approximate third-order minimizer** ([cartis2022evaluation], (4.1.3)–(4.1.4)): an
`(ε₁, ε₂)`-approximate second-order minimizer (3.2.6) at which `|∇³f(x)[d]³| ≤ ε₃` for every
`d ∈ 𝒵_ε` (vacuous when `𝒵_ε = ∅`, in which case `λ_min[∇²f(x)] > ε₂`). -/
def IsApproxThirdOrderMinimizer (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (ε₁ ε₂ ε₃ : ℝ) : Prop :=
  Chapter03.IsApproxSecondOrderMinimizer f x ε₁ ε₂ ∧
    ∀ d ∈ smallCurvatureSet f x ε₂, |iteratedFDeriv ℝ 3 f x (fun _ => d)| ≤ ε₃

/-- The certificate of ARp's third-order test ([cartis2022evaluation], Theorem 4.1.5): an
`(ε₁, ε₂)`-approximate second-order minimizer at which `|∇³f(x)[d]³| ≤ ε₃` for the directions
`d` of a set `M` only (the directions of small model curvature `𝓜_ε ⊆ 𝒵_ε`). -/
def IsApproxThirdOrderMinimizerOn (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (ε₁ ε₂ ε₃ : ℝ) (M : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Chapter03.IsApproxSecondOrderMinimizer f x ε₁ ε₂ ∧
    ∀ d ∈ M, |iteratedFDeriv ℝ 3 f x (fun _ => d)| ≤ ε₃

/-- An approximate third-order minimizer is one relative to `𝒵_ε`. -/
theorem isApproxThirdOrderMinimizer_iff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {ε₁ ε₂ ε₃ : ℝ} :
    IsApproxThirdOrderMinimizer f x ε₁ ε₂ ε₃ ↔
      IsApproxThirdOrderMinimizerOn f x ε₁ ε₂ ε₃ (smallCurvatureSet f x ε₂) :=
  Iff.rfl

/-- **Step 1 of Algorithm 4.1.1** ([cartis2022evaluation], (4.1.5)–(4.1.9)), with
`ε₂, ε₃ : Option ℝ` (`none` standing for `+∞`) and the current set `M = 𝓜_k` of directions of
small model curvature:
`‖∇f(x)‖ ≤ ε₁` and, if `ε₂ < ∞`, either `λ_min[∇²f(x)] > ε₂` (4.1.6), or `λ_min[∇²f(x)] ≥ -ε₂`
(4.1.7) and, if `ε₃ < ∞`, `|∇³f(x)[d]³| ≤ ε₃` (4.1.8) and `|∇²f(x)[d]²| ≤ ε₂` (4.1.9) for all
`d ∈ M` (vacuous when `M = ∅`). -/
def arpStopTest (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε₁ : ℝ) (ε₂ ε₃ : Option ℝ)
    (M : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖gradient f x‖ ≤ ε₁ ∧ ∀ e₂ ∈ ε₂, e₂ < Chapter01.hessianMinEig f x ∨
    (-e₂ ≤ Chapter01.hessianMinEig f x ∧ ∀ e₃ ∈ ε₃, ∀ d ∈ M,
      |iteratedFDeriv ℝ 3 f x (fun _ => d)| ≤ e₃ ∧ |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ e₂)

section StopTest

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {ε₁ : ℝ} {M : Set (EuclideanSpace ℝ (Fin n))}
  {x : EuclideanSpace ℝ (Fin n)}

@[simp]
theorem arpStopTest_none {ε₃ : Option ℝ} :
    arpStopTest f ε₁ none ε₃ M x ↔ ‖gradient f x‖ ≤ ε₁ := by
  simp [arpStopTest]

/-- With `ε₃ = +∞` the test is the second-order test (3.2.9) of Chapter 3 (for `ε₂ ≥ 0`). -/
theorem arpStopTest_none_right {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 ≤ e) :
    arpStopTest f ε₁ ε₂ none M x ↔ Chapter03.stopTest f ε₁ ε₂ x := by
  rcases ε₂ with _ | e₂
  · simp
  · have he := hε₂ e₂ rfl
    simp only [arpStopTest, Option.mem_def, Option.some.injEq, forall_eq', reduceCtorEq,
      IsEmpty.forall_iff, implies_true, and_true, Chapter03.stopTest]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h1, by linarith⟩
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Or.inr h2⟩

/-- The test with finite tolerances fails iff `‖∇f(x)‖ > ε₁`, or `λ_min[∇²f(x)] ≤ ε₂` and either
`λ_min[∇²f(x)] < -ε₂` or some `d ∈ M` violates (4.1.8) or (4.1.9). -/
theorem not_arpStopTest_some_some {e₂ e₃ : ℝ} :
    ¬ arpStopTest f ε₁ (some e₂) (some e₃) M x ↔
      ε₁ < ‖gradient f x‖ ∨ (Chapter01.hessianMinEig f x ≤ e₂ ∧
        (Chapter01.hessianMinEig f x < -e₂ ∨ ∃ d ∈ M,
          e₃ < |iteratedFDeriv ℝ 3 f x (fun _ => d)| ∨
            e₂ < |iteratedFDeriv ℝ 2 f x (fun _ => d)|)) := by
  have hs : arpStopTest f ε₁ (some e₂) (some e₃) M x ↔ ‖gradient f x‖ ≤ ε₁ ∧
      (e₂ < Chapter01.hessianMinEig f x ∨ (-e₂ ≤ Chapter01.hessianMinEig f x ∧ ∀ d ∈ M,
        |iteratedFDeriv ℝ 3 f x (fun _ => d)| ≤ e₃ ∧
          |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ e₂)) := by
    unfold arpStopTest
    refine and_congr Iff.rfl ⟨fun h => ?_, fun h e he => ?_⟩
    · rcases h e₂ rfl with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2 e₃ rfl⟩
    · cases he
      rcases h with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, fun e he => by cases he; exact h2⟩
  rw [hs]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    refine h ⟨h1, ?_⟩
    rcases le_or_gt (Chapter01.hessianMinEig f x) e₂ with hl | hl
    · obtain ⟨h4, h5⟩ := h2 hl
      exact Or.inr ⟨h4, fun d hd => h5 d hd⟩
    · exact Or.inl hl
  · rintro (h | ⟨hl, h | ⟨d, hd, h⟩⟩) ⟨h1, h2⟩
    · linarith
    · rcases h2 with h2 | ⟨h2, -⟩ <;> linarith
    · rcases h2 with h2 | ⟨-, h2⟩
      · linarith
      · obtain ⟨h3, h4⟩ := h2 d hd
        rcases h with h | h <;> linarith

/-- **The certificate of the third-order test** ([cartis2022evaluation], Theorem 4.1.5 and the
discussion after Algorithm 4.1.1): if the test holds with finite tolerances `ε₂ ≥ 0`, `ε₃` and a
set `M` of unit vectors, then `x` is an `(ε₁, ε₂)`-approximate second-order minimizer, and either
`λ_min[∇²f(x)] > ε₂` (an approximate strict local minimizer, `𝒵_ε = ∅`), or `M ⊆ 𝒵_ε` and
`|∇³f(x)[d]³| ≤ ε₃` for all `d ∈ M`. -/
theorem arpStopTest_some_some_certificate {e₂ e₃ : ℝ} (he₂ : 0 ≤ e₂)
    (hM : ∀ d ∈ M, ‖d‖ = 1) (h : arpStopTest f ε₁ (some e₂) (some e₃) M x) :
    Chapter03.IsApproxSecondOrderMinimizer f x ε₁ e₂ ∧
      (e₂ < Chapter01.hessianMinEig f x ∨
        (M ⊆ smallCurvatureSet f x e₂ ∧ IsApproxThirdOrderMinimizerOn f x ε₁ e₂ e₃ M)) := by
  obtain ⟨h1, h2⟩ := h
  rcases h2 e₂ rfl with h2 | ⟨h2, h3⟩
  · exact ⟨⟨h1, by linarith⟩, Or.inl h2⟩
  · exact ⟨⟨h1, h2⟩, Or.inr ⟨fun d hd => ⟨hM d hd, (h3 e₃ rfl d hd).2⟩, ⟨h1, h2⟩,
      fun d hd => (h3 e₃ rfl d hd).1⟩⟩

end StopTest

/-- The order of criticality sought by ARp: `1` if `ε₂ = +∞`, `2` if `ε₂ < ∞ = ε₃` and `3` if
both are finite. -/
def arpOrder : Option ℝ → Option ℝ → ℕ
  | none, _ => 1
  | some _, none => 2
  | some _, some _ => 3

@[simp] theorem arpOrder_none (ε₃ : Option ℝ) : arpOrder none ε₃ = 1 := rfl
@[simp] theorem arpOrder_some_none (e₂ : ℝ) : arpOrder (some e₂) none = 2 := rfl
@[simp] theorem arpOrder_some_some (e₂ e₃ : ℝ) : arpOrder (some e₂) (some e₃) = 3 := rfl

/-- The sets `𝓜_k` of directions of small model curvature of an ARp run: `𝓜₀ = 𝒵(x₀, ε₂)` (Step 0)
and `𝓜_{k+1} = {d | ‖d‖ = 1 ∧ |∇²m_k(s_k)[d]²| ≤ θ₂ ‖s_k‖^{p-1}}` (4.1.14), with the model
`m_k = regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)` of (4.1.2). (`𝓜₀ = ∅` if `ε₂ = +∞`; the
sets are only used when `ε₃ < ∞`.) -/
def arpCurvSet (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpParams) (ε₂ : Option ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) : ℕ → Set (EuclideanSpace ℝ (Fin n))
  | 0 => ε₂.elim ∅ (smallCurvatureSet f (x 0))
  | k + 1 => smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
      (P.θ₂ * ‖s k‖ ^ (p - 1))

theorem arpCurvSet_succ (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpParams)
    (ε₂ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) (k : ℕ) :
    arpCurvSet f p P ε₂ x s σ (k + 1) = smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k))
      (P.θ₂ * ‖s k‖ ^ (p - 1)) := rfl

/-- The elements of the sets `𝓜_k` are unit vectors. -/
theorem norm_eq_one_of_mem_arpCurvSet {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpParams}
    {ε₂ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ} {k : ℕ}
    {d : EuclideanSpace ℝ (Fin n)} (hd : d ∈ arpCurvSet f p P ε₂ x s σ k) : ‖d‖ = 1 := by
  cases k with
  | zero =>
    rcases ε₂ with _ | e₂
    · exact absurd hd (by simp [arpCurvSet])
    · exact hd.1
  | succ k => exact hd.1

/-- The termination test of iteration `k` of an ARp run: `arpStopTest` at `x_k` with `𝓜_k`. -/
abbrev arpTest (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpParams) (ε₁ : ℝ)
    (ε₂ ε₃ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) (k : ℕ) : Prop :=
  arpStopTest f ε₁ ε₂ ε₃ (arpCurvSet f p P ε₂ x s σ k) (x k)

/-- **Algorithm 4.1.1** (ARp) of [cartis2022evaluation], as a run predicate on iterates `x`,
steps `s` and regularization parameters `σ`, for `p ≥ 1` and tolerances `ε₁ > 0`,
`ε₂, ε₃ ∈ (0, ∞]` (`ε₃ = ∞` if `ε₂ = ∞`, and `p` at least the order `q` of criticality sought): the
backbone ARp run `Optimization.IsARpRun` of order `q = arpOrder ε₂ ε₃` with the termination test
`arpTest` (4.1.5)–(4.1.9). Spelled out, with `m_k` the model (4.1.2): `σ₀` is given, and at every
iteration `k` before termination the step satisfies (4.1.10) `m_k(s_k) < m_k(0)`, (4.1.11)
`‖∇m_k(s_k)‖ ≤ θ₁ ‖s_k‖^p`, if `ε₂ < ∞` (4.1.12) `λ_min[∇²m_k(s_k)] ≥ -θ₂ ‖s_k‖^{p-1}` and, if
`ε₃ < ∞`, (4.1.13) `|∇³m_k(s_k)[d]³| ≤ θ₃ ‖s_k‖^{p-2}` for all `d ∈ 𝓜_{k+1}`; the trial point is
accepted iff `ρ_k ≥ η₁` with `ρ_k` of (4.1.15), and `σ_{k+1}` follows (4.1.16). Iteration `k` is
successful iff `η₁ ≤ taylorRatio f p x s k`. -/
structure algorithm_4_1_1 (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ) (P : ARpParams) (ε₁ : ℝ)
    (ε₂ ε₃ : Option ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ) : Prop where
  /-- The order of the models is at least `1`. -/
  one_le_p : 1 ≤ p
  /-- The order of the models is at least the order of criticality sought. -/
  order_le : arpOrder ε₂ ε₃ ≤ p
  /-- The first-order tolerance is positive. -/
  ε₁_pos : 0 < ε₁
  /-- The second-order tolerance is positive. -/
  ε₂_pos : ∀ e ∈ ε₂, 0 < e
  /-- The third-order tolerance is positive. -/
  ε₃_pos : ∀ e ∈ ε₃, 0 < e
  /-- A finite third-order tolerance requires a finite second-order tolerance. -/
  ε₃_eq_none : ε₂ = none → ε₃ = none
  /-- Steps 1–4. -/
  run : IsARpRun f p P.toARpParams (arpOrder ε₂ ε₃) (arpTest f p P ε₁ ε₂ ε₃ x s σ) x s σ

section Order

theorem two_le_arpOrder {ε₂ ε₃ : Option ℝ} (h : ε₂ ≠ none) : 2 ≤ arpOrder ε₂ ε₃ := by
  rcases ε₂ with _ | e₂
  · exact absurd rfl h
  · rcases ε₃ with _ | e₃ <;> simp

theorem three_le_arpOrder {ε₂ ε₃ : Option ℝ} (h₂ : ε₂ ≠ none) (h₃ : ε₃ ≠ none) :
    3 ≤ arpOrder ε₂ ε₃ := by
  rcases ε₂ with _ | e₂
  · exact absurd rfl h₂
  · rcases ε₃ with _ | e₃
    · exact absurd rfl h₃
    · simp

theorem arpOrder_le_three (ε₂ ε₃ : Option ℝ) : arpOrder ε₂ ε₃ ≤ 3 := by
  rcases ε₂ with _ | e₂ <;> rcases ε₃ with _ | e₃ <;> simp

theorem arpOrder_none_right_le_two (ε₂ : Option ℝ) : arpOrder ε₂ none ≤ 2 := by
  rcases ε₂ with _ | e₂ <;> simp

end Order

namespace algorithm_4_1_1

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpParams} {ε₁ : ℝ}
  {ε₂ ε₃ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- Step 2 holds at every iteration before termination. -/
theorem step (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j) :
    IsARpStep f p P.toARpParams (arpOrder ε₂ ε₃) (x k) (σ k) (s k) :=
  h.run.step_spec hk

theorem sigma_pos (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) {k : ℕ}
    (hk : ∀ j < k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j) : 0 < σ k :=
  h.run.sigma_pos hk

/-- A finite second-order tolerance requires `p ≥ 2`. -/
theorem two_le_p (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) (h₂ : ε₂ ≠ none) : 2 ≤ p :=
  (two_le_arpOrder h₂).trans h.order_le

/-- A finite third-order tolerance requires `p ≥ 3` (and a finite `ε₂`). -/
theorem three_le_order (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) (h₃ : ε₃ ≠ none) :
    3 ≤ arpOrder ε₂ ε₃ :=
  three_le_arpOrder (fun h₂ => h₃ (h.ε₃_eq_none h₂)) h₃

theorem three_le_p (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) (h₃ : ε₃ ≠ none) : 3 ≤ p :=
  (h.three_le_order h₃).trans h.order_le

/-- **(4.1.18) along a run**: at every iteration before termination,
`T_{f,p}(x_k, 0) - T_{f,p}(x_k, s_k) > σ_k/(p+1)! ‖s_k‖^{p+1}`. -/
theorem lt_taylorDecrement (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j) :
    σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) <
      (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) :=
  lt_taylorDecrement_of_regularizedModel_lt (h.step hk).decrease

/-- The predicted decrease is positive before termination. -/
theorem taylorDecrement_pos (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j) :
    0 < (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) := by
  have := h.sigma_pos fun j hj => hk j hj.le
  exact lt_of_le_of_lt (by positivity) (h.lt_taylorDecrement hk)

end algorithm_4_1_1

/-! ### Existence of runs -/

section Existence

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ}

/-- **Existence of ARp runs for `ε₃ = +∞`** ([cartis2022evaluation], Algorithm 4.1.1 is well
defined in its first- and second-order modes): for a `C^p` function, all constants, tolerances
`ε₁ > 0`, `ε₂ ∈ (0, ∞]` with `p ≥ 2` if `ε₂ < ∞`, and every starting point there is an ARp run
(a global minimizer of the model (4.1.2) satisfies Step 2 whenever the termination test fails). -/
theorem exists_algorithm_4_1_1 (hf : ContDiff ℝ p f) (P : ARpParams) (hp : 1 ≤ p) {ε₁ : ℝ}
    (hε₁ : 0 < ε₁) {ε₂ : Option ℝ} (hε₂ : ∀ e ∈ ε₂, 0 < e) (hord : arpOrder ε₂ none ≤ p)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x s σ, x 0 = x₀ ∧ algorithm_4_1_1 f p P ε₁ ε₂ none x s σ := by
  have hq := arpOrder_none_right_le_two ε₂
  have hcrit : ∀ y, ¬ Chapter03.stopTest f ε₁ ε₂ y → fderiv ℝ f y ≠ 0 ∨
      (2 ≤ arpOrder ε₂ none ∧ minCurvature (iteratedFDeriv ℝ 2 f y) < 0) := by
    intro y hy
    by_cases hg : fderiv ℝ f y = 0
    · right
      have hg' : ‖gradient f y‖ = 0 := by rw [norm_gradient_eq, hg, norm_zero]
      rcases ε₂ with _ | e₂
      · exact absurd (by rw [Chapter03.stopTest_none, hg']; exact hε₁.le) hy
      · refine ⟨by simp, ?_⟩
        rw [Chapter03.not_stopTest_some, hg'] at hy
        have := hε₂ e₂ rfl
        rcases hy with hy | hy
        · linarith
        · change Chapter01.hessianMinEig f y < 0
          linarith
    · exact Or.inl hg
  obtain ⟨x, s, σ, hx0, hrun⟩ := exists_isARpRun (q := arpOrder ε₂ none) P.toARpParams hf hp hq
    (fun h2 => h2.trans hord) (test := Chapter03.stopTest f ε₁ ε₂) hcrit x₀
  refine ⟨x, s, σ, hx0, ⟨hp, hord, hε₁, hε₂, fun _ h => absurd h (by simp), fun _ => rfl, ?_⟩⟩
  have htest : arpTest f p P ε₁ ε₂ none x s σ = fun k => Chapter03.stopTest f ε₁ ε₂ (x k) :=
    funext fun k => propext (arpStopTest_none_right fun e he => (hε₂ e he).le)
  rw [htest]
  exact hrun

end Existence

/-! ### Lemmas 4.1.1–4.1.4 -/

/-- **Lemma 4.1.1** of [cartis2022evaluation] ((4.1.18)). If the model (4.1.2) at `x` satisfies
`m(s) ≤ m(0)`, then `T_{f,p}(x, 0) - T_{f,p}(x, s) ≥ σ/(p+1)! ‖s‖^{p+1}`. (Along an ARp run this
holds, strictly, at every iteration before termination: `algorithm_4_1_1.lt_taylorDecrement`.) -/
theorem lemma_4_1_1 {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {x s : EuclideanSpace ℝ (Fin n)}
    {σ : ℝ} (h : regularizedModel (ftaylorSeries ℝ f x) p σ s ≤
      regularizedModel (ftaylorSeries ℝ f x) p σ 0) :
    σ / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) ≤ (ftaylorSeries ℝ f x).taylorDecrement p s :=
  taylorDecrement_ge_of_regularizedModel_le h

/-- The bound `σ_max = max(σ₀, γ₃ L_{f,p}/(1 - η₂))` of (4.1.19) (`Optimization.arSigmaMax`). -/
noncomputable abbrev sigmaMaxARp (P : ARpParams) (L : ℝ) : ℝ := arSigmaMax P.toARParams L

/-- The constant `κ₁ = η₁ σ_min/(p+1)! (p!/(L_{f,p} + σ_max + θ₁ p!))^{(p+1)/p}` of (4.1.32). -/
noncomputable def kappaARp₁ (P : ARpParams) (p : ℕ) (L : ℝ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    ((p ! : ℝ) / (L + sigmaMaxARp P L + P.θ₁ * p !)) ^ (((p : ℝ) + 1) / p)

/-- The constant `κ₂` of (4.1.34),
`η₁ σ_min/(p+1)! ((p-1)!/(L_{f,p} + σ_max + θ₂ (p-1)!))^{(p+1)/(p-1)}`. -/
noncomputable def kappaARp₂ (P : ARpParams) (p : ℕ) (L : ℝ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    (((p - 1)! : ℝ) / (L + sigmaMaxARp P L + P.θ₂ * (p - 1)!)) ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))

/-- The constant `κ₃` of (4.1.36),
`η₁ σ_min/(p+1)! ((p-2)!/(L_{f,p} + σ_max + θ₃ (p-2)!))^{(p+1)/(p-2)}`. -/
noncomputable def kappaARp₃ (P : ARpParams) (p : ℕ) (L : ℝ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    (((p - 2)! : ℝ) / (L + sigmaMaxARp P L + P.θ₃ * (p - 2)!)) ^ (((p : ℝ) + 1) / ((p : ℝ) - 2))

/-- The constant `κ_{s2} = (p-1)!/(L_{f,p} + σ_max + θ₂ (p-1)!)` of (4.1.23). -/
noncomputable def kappaS2ARp (P : ARpParams) (p : ℕ) (L : ℝ) : ℝ :=
  ((p - 1)! : ℝ) / (L + sigmaMaxARp P L + P.θ₂ * (p - 1)!)

section Lemmas

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpParams} {ε₁ L flow : ℝ}
  {ε₂ ε₃ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- **Lemma 4.1.2** of [cartis2022evaluation] ((4.1.19)). Under f.DpL, every ARp run satisfies
`σ_k ≤ σ_max = max(σ₀, γ₃ L_{f,p}/(1 - η₂))` for every iteration `k` up to (and including)
termination. -/
theorem lemma_4_1_2 (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    {k : ℕ} (hk : ∀ j < k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j) : σ k ≤ sigmaMaxARp P L :=
  (h.run.sigma_le hf.contDiff hf.iteratedFDerivLipschitzOn hk).2

/-- **Lemma 4.1.3, (4.1.20)** of [cartis2022evaluation]. Under f.DpL, on every successful
iteration `k` of an ARp run (before termination),
`‖s_k‖^p ≥ p!/(L_{f,p} + σ_max + θ₁ p!) ‖∇f(x_{k+1})‖`. -/
theorem lemma_4_1_3_i (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    (p ! : ℝ) / (L + sigmaMaxARp P L + P.θ₁ * p !) * ‖gradient f (x (k + 1))‖ ≤ ‖s k‖ ^ p := by
  rw [norm_gradient_eq]
  exact (h.run.step_lower_bounds hf.contDiff hf.iteratedFDerivLipschitzOn hf.nonneg h.one_le_p
    h.order_le hk hs).2.1

/-- **Lemma 4.1.3, (4.1.21)** of [cartis2022evaluation]. Under f.DpL, if `ε₂ < ∞`, on every
successful iteration `k` of an ARp run (before termination),
`‖s_k‖^{p-1} ≥ (p-1)!/(L_{f,p} + σ_max + θ₂ (p-1)!) max(0, -λ_min[∇²f(x_{k+1})])`. -/
theorem lemma_4_1_3_ii (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    (h₂ : ε₂ ≠ none) {k : ℕ} (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    ((p - 1)! : ℝ) / (L + sigmaMaxARp P L + P.θ₂ * (p - 1)!) *
      max 0 (-Chapter01.hessianMinEig f (x (k + 1))) ≤ ‖s k‖ ^ (p - 1) :=
  (h.run.step_lower_bounds hf.contDiff hf.iteratedFDerivLipschitzOn hf.nonneg h.one_le_p
    h.order_le hk hs).2.2.1 (two_le_arpOrder h₂)

/-- **Lemma 4.1.3, (4.1.22)** of [cartis2022evaluation]. Under f.DpL, if `ε₃ < ∞`, on every
successful iteration `k` of an ARp run (before termination), for every `d ∈ 𝓜_{k+1}` (4.1.14),
`‖s_k‖^{p-2} ≥ (p-2)!/(L_{f,p} + σ_max + θ₃ (p-2)!) |∇³f(x_{k+1})[d]³|`. -/
theorem lemma_4_1_3_iii (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    (h₃ : ε₃ ≠ none) {k : ℕ} (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    ∀ d ∈ arpCurvSet f p P ε₂ x s σ (k + 1),
      ((p - 2)! : ℝ) / (L + sigmaMaxARp P L + P.θ₃ * (p - 2)!) *
        |iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ => d)| ≤ ‖s k‖ ^ (p - 2) :=
  (h.run.step_lower_bounds hf.contDiff hf.iteratedFDerivLipschitzOn hf.nonneg h.one_le_p
    h.order_le hk hs).2.2.2.1 (h.three_le_order h₃)

/-- **Lemma 4.1.3, (4.1.23)** of [cartis2022evaluation]. Under f.DpL, if `ε₂ < ∞`, on every
successful iteration `k` of an ARp run (before termination), for every `d ∈ 𝓜_{k+1}` (4.1.14),
`|∇²f(x_{k+1})[d]²| ≤ ‖s_k‖^{p-1}/κ_{s2}` with `κ_{s2} = (p-1)!/(L_{f,p} + σ_max + θ₂ (p-1)!)`. -/
theorem lemma_4_1_3_iv (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    (h₂ : ε₂ ≠ none) {k : ℕ} (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    ∀ d ∈ arpCurvSet f p P ε₂ x s σ (k + 1),
      |iteratedFDeriv ℝ 2 f (x (k + 1)) (fun _ => d)| ≤ 1 / kappaS2ARp P p L * ‖s k‖ ^ (p - 1) := by
  intro d hd
  rw [kappaS2ARp, one_div_div]
  exact (h.run.step_lower_bounds hf.contDiff hf.iteratedFDerivLipschitzOn hf.nonneg h.one_le_p
    h.order_le hk hs).2.2.2.2 (two_le_arpOrder h₂) d hd

/-- **Lemma 4.1.4, (4.1.31) and (4.1.37)** of [cartis2022evaluation]. Under f.DpL, on every
successful iteration `k` of an ARp run (before termination),
`f(x_k) - f(x_{k+1}) ≥ η₁ σ_min/(p+1)! ‖s_k‖^{p+1}` and
`f(x_k) - f(x_{k+1}) ≥ κ₁ ‖∇f(x_{k+1})‖^{(p+1)/p}`. -/
theorem lemma_4_1_4_i (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    P.η₁ * P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤ f (x k) - f (x (k + 1)) ∧
      kappaARp₁ P p L * ‖gradient f (x (k + 1))‖ ^ (((p : ℝ) + 1) / p) ≤
        f (x k) - f (x (k + 1)) := by
  obtain ⟨h1, h2, -⟩ := h.run.decrease_ge hf.contDiff hf.iteratedFDerivLipschitzOn hf.nonneg
    h.one_le_p h.order_le hk hs
  rw [norm_gradient_eq]
  exact ⟨h1, h2⟩

/-- **Lemma 4.1.4, (4.1.33)** of [cartis2022evaluation]. Under f.DpL, if `ε₂ < ∞`, on every
successful iteration `k` of an ARp run (before termination),
`f(x_k) - f(x_{k+1}) ≥ κ₂ max(0, -λ_min[∇²f(x_{k+1})])^{(p+1)/(p-1)}`. -/
theorem lemma_4_1_4_ii (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    (h₂ : ε₂ ≠ none) {k : ℕ} (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    kappaARp₂ P p L * (max 0 (-Chapter01.hessianMinEig f (x (k + 1)))) ^
      (((p : ℝ) + 1) / ((p : ℝ) - 1)) ≤ f (x k) - f (x (k + 1)) :=
  (h.run.decrease_ge hf.contDiff hf.iteratedFDerivLipschitzOn hf.nonneg h.one_le_p h.order_le hk
    hs).2.2.1 (two_le_arpOrder h₂)

/-- **Lemma 4.1.4, (4.1.35)** of [cartis2022evaluation]. Under f.DpL, if `ε₃ < ∞`, on every
successful iteration `k` of an ARp run (before termination), for every `d ∈ 𝓜_{k+1}`,
`f(x_k) - f(x_{k+1}) ≥ κ₃ |∇³f(x_{k+1})[d]³|^{(p+1)/(p-2)}`. -/
theorem lemma_4_1_4_iii (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ)
    (h₃ : ε₃ ≠ none) {k : ℕ} (hk : ∀ j ≤ k, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j)
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    ∀ d ∈ arpCurvSet f p P ε₂ x s σ (k + 1),
      kappaARp₃ P p L * |iteratedFDeriv ℝ 3 f (x (k + 1)) (fun _ => d)| ^
        (((p : ℝ) + 1) / ((p : ℝ) - 2)) ≤ f (x k) - f (x (k + 1)) :=
  (h.run.decrease_ge hf.contDiff hf.iteratedFDerivLipschitzOn hf.nonneg h.one_le_p h.order_le hk
    hs).2.2.2 (h.three_le_order h₃)

end Lemmas

/-! ### Theorem 4.1.5 -/

/-- The constant `κ^S_ARp` of (4.1.45) for the order of criticality `q` (only the terms of the
active orders `j ≤ q` enter the maximum):
`(p+1)!/(η₁ σ_min) max_{j ≤ q} ((L_{f,p} + σ_max + θ_j (p-j)!)/(p-j)!)^{(p+1)/(p-j+1)}`. -/
noncomputable def kappaSARp (P : ARpParams) (p : ℕ) (L : ℝ) (q : ℕ) : ℝ :=
  ((p + 1)! : ℝ) / (P.η₁ * P.σmin) *
    max (((L + sigmaMaxARp P L + P.θ₁ * p !) / (p ! : ℝ)) ^ (((p : ℝ) + 1) / p))
      (max (if 2 ≤ q then ((L + sigmaMaxARp P L + P.θ₂ * (p - 1)!) / ((p - 1)! : ℝ)) ^
          (((p : ℝ) + 1) / ((p : ℝ) - 1)) else 0)
        (if 3 ≤ q then ((L + sigmaMaxARp P L + P.θ₃ * (p - 2)!) / ((p - 2)! : ℝ)) ^
          (((p : ℝ) + 1) / ((p : ℝ) - 2)) else 0))

/-- The constant `κ^C_ARp = (|log γ₁| + log(σ_max/σ₀))/log γ₂ + 2` of (4.1.46). -/
noncomputable def kappaCARp (P : ARpParams) (L : ℝ) : ℝ :=
  (|Real.log P.γ₁| + Real.log (sigmaMaxARp P L / P.σ₀)) / Real.log P.γ₂ + 2

section Constants

variable {P : ARpParams} {p : ℕ} {L : ℝ}

private theorem constant_pos (hL : 0 ≤ L) (θ : ℝ) (hθ : 0 < θ) (m : ℕ) :
    0 < L + sigmaMaxARp P L + θ * m ! := by
  have := arSigmaMax_pos P.toARParams L
  positivity

private theorem one_le_mul_of_le {u v a b M e : ℝ} (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hb : 0 < b) (hM : (b / a) ^ e ≤ M) : 1 ≤ u / v * M * (v / u * (a / b) ^ e) := by
  have h1 : u / v * M * (v / u * (a / b) ^ e) = M * (a / b) ^ e := by
    field_simp
  have h2 : (b / a) ^ e * (a / b) ^ e = 1 := by
    have : b / a * (a / b) = 1 := by field_simp
    rw [← Real.mul_rpow (by positivity) (by positivity), this, Real.one_rpow]
  rw [h1, ← h2]
  exact mul_le_mul_of_nonneg_right hM (by positivity)

theorem kappaSARp_pos (hL : 0 ≤ L) (q : ℕ) : 0 < kappaSARp P p L q := by
  have := P.η₁_pos; have := P.σmin_pos
  have h1 : 0 < ((L + sigmaMaxARp P L + P.θ₁ * p !) / (p ! : ℝ)) ^ (((p : ℝ) + 1) / p) := by
    have := constant_pos (P := P) hL _ P.θ₁_pos p
    positivity
  unfold kappaSARp
  exact mul_pos (by positivity) (h1.trans_le (le_max_left _ _))

theorem one_le_kappaSARp_mul_kappaARp₁ (hL : 0 ≤ L) (q : ℕ) :
    1 ≤ kappaSARp P p L q * kappaARp₁ P p L := by
  have := P.η₁_pos; have := P.σmin_pos
  exact one_le_mul_of_le (by positivity) (by positivity) (by positivity)
    (constant_pos hL _ P.θ₁_pos p) (le_max_left _ _)

theorem one_le_kappaSARp_mul_kappaARp₂ (hL : 0 ≤ L) {q : ℕ} (hq : 2 ≤ q) :
    1 ≤ kappaSARp P p L q * kappaARp₂ P p L := by
  have := P.η₁_pos; have := P.σmin_pos
  refine one_le_mul_of_le (by positivity) (by positivity) (by positivity)
    (constant_pos hL _ P.θ₂_pos (p - 1)) ?_
  refine le_trans (le_of_eq ?_) ((le_max_left _ _).trans (le_max_right _ _))
  simp [hq]

theorem one_le_kappaSARp_mul_kappaARp₃ (hL : 0 ≤ L) {q : ℕ} (hq : 3 ≤ q) :
    1 ≤ kappaSARp P p L q * kappaARp₃ P p L := by
  have := P.η₁_pos; have := P.σmin_pos
  refine one_le_mul_of_le (by positivity) (by positivity) (by positivity)
    (constant_pos hL _ P.θ₃_pos (p - 2)) ?_
  refine le_trans (le_of_eq ?_) ((le_max_right _ _).trans (le_max_right _ _))
  simp [hq]

/-- `κ₂ = η₁ σ_min/(p+1)! κ_{s2}^{(p+1)/(p-1)}` (the remark after (4.1.44)). -/
theorem kappaARp₂_eq : kappaARp₂ P p L = P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    kappaS2ARp P p L ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) := rfl

/-- `κ^C ≥ 2` (since `σ_max ≥ σ₀`). -/
theorem two_le_kappaCARp (L : ℝ) : 2 ≤ kappaCARp P L := by
  have h1 : 1 ≤ sigmaMaxARp P L / P.σ₀ := by
    rw [le_div_iff₀ P.σ₀_pos, one_mul]; exact σ₀_le_arSigmaMax _ _
  have := Real.log_nonneg h1
  have := P.toARParams.log_γ₂_pos
  unfold kappaCARp
  have : 0 ≤ (|Real.log P.γ₁| + Real.log (sigmaMaxARp P L / P.σ₀)) / Real.log P.γ₂ := by
    positivity
  linarith

end Constants

private theorem div_le_mul_of_one_le {t E κS κ : ℝ} (hκS : 0 < κS) (h1 : 1 ≤ κS * κ)
    (ht : t ≤ E) (hE : 0 ≤ E) : t / κS ≤ κ * E := by
  rw [div_le_iff₀ hκS]
  nlinarith

section Complexity

variable {f : EuclideanSpace ℝ (Fin n) → ℝ} {p : ℕ} {P : ARpParams} {ε₁ L flow : ℝ}
  {ε₂ ε₃ : Option ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)} {σ : ℕ → ℝ}

/-- The common end of the proof of Theorem 4.1.5: if every successful iteration `k` such that
`k + 1` is not the termination index decreases `f` by at least `δ > 0`, the run terminates with
`k_ε + 1 ≤ (1 + |log γ₁|/log γ₂) (f(x₀) - f_low)/δ + κ^C` and at most `(f(x₀) - f_low)/δ + 2`
derivative evaluations. -/
theorem algorithm_4_1_1.exists_isFirstHit_of_decrease (hb : Chapter02.AssumptionBb f flow)
    (hf : AssumptionDpL f p L) (h : algorithm_4_1_1 f p P ε₁ ε₂ ε₃ x s σ) {δ : ℝ} (hδ : 0 < δ)
    (hdec : ∀ k, (∀ j ≤ k + 1, ¬ arpTest f p P ε₁ ε₂ ε₃ x s σ j) →
      P.η₁ ≤ taylorRatio f p x s k → δ ≤ f (x k) - f (x (k + 1))) :
    ∃ kε, IsFirstHit (arpTest f p P ε₁ ε₂ ε₃ x s σ) kε ∧
      (funEvalCount kε : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * ((f (x 0) - flow) / δ) +
        kappaCARp P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f p x s k) kε : ℝ) ≤
        (f (x 0) - flow) / δ + 2 := by
  obtain ⟨kε, hk, hF, hD⟩ := h.run.toIsARRun.exists_isFirstHit_of_decrease
    (σmax := sigmaMaxARp P L) (V := fun k => f (x k)) (Vlow := flow)
    (fun k hk => lemma_4_1_2 hf h (IsARRun.forall_lt_not_stop_iff.1 hk)) hδ
    (fun k hk => (h.run.toIsARRun.accept k hk).le (w := f) rfl
      (h.taylorDecrement_pos (IsARRun.forall_le_not_stop_iff.1 hk)))
    (fun k _ => hb (x k))
    (fun k hk hs => hdec k (IsARRun.forall_le_not_stop_iff.1 hk) hs)
  exact ⟨kε, IsARRun.isFirstHit_stop_iff.1 hk, hF, hD⟩

/-- **Theorem 4.1.5** of [cartis2022evaluation], first-order mode (`ε₂ = ε₃ = +∞`, any `p ≥ 1`).
Under f.Bb and f.DpL, every ARp run with `ε₁ > 0` terminates at an iteration `k_ε` (the first with
`‖∇f(x_k)‖ ≤ ε₁`) after at most `κ^A (f(x₀) - f_low)/ε₁^{(p+1)/p} + κ^C` evaluations of `f` and at
most `κ^S (f(x₀) - f_low)/ε₁^{(p+1)/p} + 2` evaluations of the derivatives of orders `1` to `p`
(4.1.38), with `κ^S = kappaSARp P p L 1 = (p+1)!/(η₁ σ_min) ((L + σ_max + θ₁ p!)/p!)^{(p+1)/p}`,
`κ^A = κ^S (1 + |log γ₁|/log γ₂)` and `κ^C = kappaCARp` (4.1.46). -/
theorem theorem_4_1_5_i (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionDpL f p L)
    (h : algorithm_4_1_1 f p P ε₁ none none x s σ) :
    ∃ kε, IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) kε ∧
      (funEvalCount kε : ℝ) ≤ kappaSARp P p L 1 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
        (f (x 0) - flow) / ε₁ ^ (((p : ℝ) + 1) / p) + kappaCARp P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f p x s k) kε : ℝ) ≤
        kappaSARp P p L 1 * (f (x 0) - flow) / ε₁ ^ (((p : ℝ) + 1) / p) + 2 := by
  have hκ := kappaSARp_pos (P := P) (p := p) hf.nonneg 1
  have hε := h.ε₁_pos
  set e := ((p : ℝ) + 1) / p
  have hE : 0 < ε₁ ^ e := Real.rpow_pos_of_pos hε _
  set δ := ε₁ ^ e / kappaSARp P p L 1
  have hδ : 0 < δ := by positivity
  have hNδ : (f (x 0) - flow) / δ = kappaSARp P p L 1 * (f (x 0) - flow) / ε₁ ^ e := by
    simp only [δ]; field_simp
  obtain ⟨kε, hk, hF, hD⟩ := h.exists_isFirstHit_of_decrease hb hf hδ fun k hk hs => by
    have hg : ε₁ < ‖gradient f (x (k + 1))‖ := by
      have := hk (k + 1) le_rfl
      simpa using this
    have h1 := (lemma_4_1_4_i hf h (fun j hj => hk j (hj.trans k.le_succ)) hs).2
    have hκ₁ : 0 ≤ kappaARp₁ P p L := by
      have := P.η₁_pos; have := P.σmin_pos
      have := constant_pos (P := P) hf.nonneg _ P.θ₁_pos p
      unfold kappaARp₁; positivity
    refine le_trans ?_ h1
    refine (div_le_mul_of_one_le hκ (one_le_kappaSARp_mul_kappaARp₁ hf.nonneg 1) le_rfl
      hE.le).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε.le hg.le (by positivity)) hκ₁
  rw [hNδ] at hF hD
  have htest : arpTest f p P ε₁ none none x s σ = fun k => ‖gradient f (x k)‖ ≤ ε₁ :=
    funext fun k => propext arpStopTest_none
  refine ⟨kε, htest ▸ hk, ?_, hD⟩
  calc (funEvalCount kε : ℝ) ≤ _ := hF
    _ = _ := by ring

private theorem kappaARp₁_nonneg (hL : 0 ≤ L) : 0 ≤ kappaARp₁ P p L := by
  have := P.η₁_pos; have := P.σmin_pos
  have := constant_pos (P := P) hL _ P.θ₁_pos p
  unfold kappaARp₁; positivity

private theorem kappaARp₂_nonneg (hL : 0 ≤ L) : 0 ≤ kappaARp₂ P p L := by
  have := P.η₁_pos; have := P.σmin_pos
  have := constant_pos (P := P) hL _ P.θ₂_pos (p - 1)
  unfold kappaARp₂; positivity

private theorem kappaARp₃_nonneg (hL : 0 ≤ L) : 0 ≤ kappaARp₃ P p L := by
  have := P.η₁_pos; have := P.σmin_pos
  have := constant_pos (P := P) hL _ P.θ₃_pos (p - 2)
  unfold kappaARp₃; positivity

/-- One case of the decrease estimate (4.1.44): if `t ≤ ε^e`, `ε ≤ v`, `κ^S κ ≥ 1` and the
decrease is at least `κ v^e`, then it is at least `t/κ^S`. -/
private theorem div_le_of_decrease {t ε v e κS κ D : ℝ} (hκS : 0 < κS) (h1 : 1 ≤ κS * κ)
    (hκ : 0 ≤ κ) (ht : t ≤ ε ^ e) (hε : 0 ≤ ε) (hv : ε ≤ v) (he : 0 ≤ e) (hD : κ * v ^ e ≤ D) :
    t / κS ≤ D :=
  (div_le_mul_of_one_le hκS h1 ht (by positivity)).trans
    ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε hv he) hκ).trans hD)

/-- **Theorem 4.1.5** of [cartis2022evaluation], second-order mode (`ε₂ < ∞ = ε₃`, `p ≥ 2`). Under
f.Bb and f.DpL, every ARp run with `ε₁ > 0` and `ε₂ > 0` terminates at an iteration `k_ε` (the
first `(ε₁, ε₂)`-approximate second-order minimizer, (4.1.5) and (4.1.7)) after at most
`κ^A (f(x₀) - f_low)/min(ε₁^{(p+1)/p}, ε₂^{(p+1)/(p-1)}) + κ^C` evaluations of `f` and at most
`κ^S (f(x₀) - f_low)/min(ε₁^{(p+1)/p}, ε₂^{(p+1)/(p-1)}) + 2` evaluations of the derivatives
(4.1.38), with `κ^S = kappaSARp P p L 2` (the first two terms of (4.1.45)),
`κ^A = κ^S (1 + |log γ₁|/log γ₂)` and `κ^C = kappaCARp` (4.1.46). -/
theorem theorem_4_1_5_ii (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionDpL f p L)
    {e₂ : ℝ} (h : algorithm_4_1_1 f p P ε₁ (some e₂) none x s σ) :
    ∃ kε, IsFirstHit (fun k => Chapter03.IsApproxSecondOrderMinimizer f (x k) ε₁ e₂) kε ∧
      (funEvalCount kε : ℝ) ≤ kappaSARp P p L 2 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
        (f (x 0) - flow) / min (ε₁ ^ (((p : ℝ) + 1) / p)) (e₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))) +
          kappaCARp P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f p x s k) kε : ℝ) ≤
        kappaSARp P p L 2 * (f (x 0) - flow) /
          min (ε₁ ^ (((p : ℝ) + 1) / p)) (e₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))) + 2 := by
  have hκ := kappaSARp_pos (P := P) (p := p) hf.nonneg 2
  have hε := h.ε₁_pos
  have he₂ := h.ε₂_pos e₂ rfl
  have hp2 := h.two_le_p (by simp)
  set a := ((p : ℝ) + 1) / p
  set b := ((p : ℝ) + 1) / ((p : ℝ) - 1)
  have hb0 : 0 ≤ b := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    exact div_nonneg (by linarith) (by linarith)
  set T := min (ε₁ ^ a) (e₂ ^ b)
  have hT : 0 < T := lt_min (Real.rpow_pos_of_pos hε _) (Real.rpow_pos_of_pos he₂ _)
  set δ := T / kappaSARp P p L 2
  have hδ : 0 < δ := by positivity
  have hNδ : (f (x 0) - flow) / δ = kappaSARp P p L 2 * (f (x 0) - flow) / T := by
    simp only [δ]; field_simp
  have htest : arpTest f p P ε₁ (some e₂) none x s σ =
      fun k => Chapter03.IsApproxSecondOrderMinimizer f (x k) ε₁ e₂ := by
    funext k
    rw [arpTest, arpStopTest_none_right (by simpa using he₂.le), Chapter03.stopTest_some]
  obtain ⟨kε, hk, hF, hD⟩ := h.exists_isFirstHit_of_decrease hb hf hδ fun k hk hs => by
    have hk' : ∀ j ≤ k, ¬ arpTest f p P ε₁ (some e₂) none x s σ j :=
      fun j hj => hk j (hj.trans k.le_succ)
    have hfail := hk (k + 1) le_rfl
    rw [htest] at hfail
    have hfail' : ε₁ < ‖gradient f (x (k + 1))‖ ∨
        Chapter01.hessianMinEig f (x (k + 1)) < -e₂ := by
      rw [← Chapter03.not_stopTest_some, Chapter03.stopTest_some]; exact hfail
    rcases hfail' with hg | hl
    · exact div_le_of_decrease hκ (one_le_kappaSARp_mul_kappaARp₁ hf.nonneg 2)
        (kappaARp₁_nonneg hf.nonneg) (min_le_left _ _) hε.le hg.le (by positivity)
        (lemma_4_1_4_i hf h hk' hs).2
    · exact div_le_of_decrease hκ (one_le_kappaSARp_mul_kappaARp₂ hf.nonneg le_rfl)
        (kappaARp₂_nonneg hf.nonneg) (min_le_right _ _) he₂.le
        ((by linarith : e₂ ≤ -Chapter01.hessianMinEig f (x (k + 1))).trans (le_max_right _ _))
        hb0 (lemma_4_1_4_ii hf h (by simp) hk' hs)
  rw [hNδ] at hF hD
  refine ⟨kε, htest ▸ hk, ?_, hD⟩
  calc (funEvalCount kε : ℝ) ≤ _ := hF
    _ = _ := by ring

/-- **Theorem 4.1.5** of [cartis2022evaluation], third-order mode (`ε₂, ε₃ < ∞`, `p ≥ 3`). Under
f.Bb and f.DpL, every ARp run with `ε₁, ε₂, ε₃ > 0` terminates at an iteration `k_ε` after at
most `κ^A (f(x₀) - f_low)/min(ε₁^{(p+1)/p}, ε₂^{(p+1)/(p-1)}, ε₃^{(p+1)/(p-2)}) + κ^C`
evaluations of `f` and at most `κ^S (f(x₀) - f_low)/min(…) + 2` evaluations of the derivatives
(4.1.38), with `κ^S = kappaSARp P p L 3` (4.1.45), `κ^A = κ^S (1 + |log γ₁|/log γ₂)` and
`κ^C = kappaCARp` (4.1.46). At `x_ε = x_{k_ε}`, with `𝓜_ε = 𝓜_{k_ε}`: `‖∇f(x_ε)‖ ≤ ε₁`,
`λ_min[∇²f(x_ε)] ≥ -ε₂`, and either `λ_min[∇²f(x_ε)] > ε₂` (an approximate strict local
minimizer, `𝒵_ε = ∅`) or `𝓜_ε ⊆ 𝒵_ε` and `|∇³f(x_ε)[d]³| ≤ ε₃` for all `d ∈ 𝓜_ε`. (This is the
book's conclusion; it is weaker than (4.1.3), cf. §6.2.1. By
`not_exists_algorithm_4_1_1_third_order` runs need not exist in this mode.) -/
theorem theorem_4_1_5_iii (hb : Chapter02.AssumptionBb f flow) (hf : AssumptionDpL f p L)
    {e₂ e₃ : ℝ} (h : algorithm_4_1_1 f p P ε₁ (some e₂) (some e₃) x s σ) :
    ∃ kε, IsFirstHit (arpTest f p P ε₁ (some e₂) (some e₃) x s σ) kε ∧
      (funEvalCount kε : ℝ) ≤ kappaSARp P p L 3 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
        (f (x 0) - flow) / min (ε₁ ^ (((p : ℝ) + 1) / p))
          (min (e₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))) (e₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)))) +
          kappaCARp P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f p x s k) kε : ℝ) ≤
        kappaSARp P p L 3 * (f (x 0) - flow) / min (ε₁ ^ (((p : ℝ) + 1) / p))
          (min (e₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))) (e₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)))) +
          2 ∧
      Chapter03.IsApproxSecondOrderMinimizer f (x kε) ε₁ e₂ ∧
      (e₂ < Chapter01.hessianMinEig f (x kε) ∨
        (arpCurvSet f p P (some e₂) x s σ kε ⊆ smallCurvatureSet f (x kε) e₂ ∧
          ∀ d ∈ arpCurvSet f p P (some e₂) x s σ kε,
            |iteratedFDeriv ℝ 3 f (x kε) (fun _ => d)| ≤ e₃)) := by
  have hκ := kappaSARp_pos (P := P) (p := p) hf.nonneg 3
  have hε := h.ε₁_pos
  have he₂ := h.ε₂_pos e₂ rfl
  have he₃ := h.ε₃_pos e₃ rfl
  have hp3 := h.three_le_p (by simp)
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  set a := ((p : ℝ) + 1) / p
  set b := ((p : ℝ) + 1) / ((p : ℝ) - 1)
  set c := ((p : ℝ) + 1) / ((p : ℝ) - 2)
  have hb0 : 0 ≤ b := div_nonneg (by linarith) (by linarith)
  have hc0 : 0 ≤ c := div_nonneg (by linarith) (by linarith)
  set T := min (ε₁ ^ a) (min (e₂ ^ b) (e₃ ^ c))
  have hT : 0 < T := lt_min (Real.rpow_pos_of_pos hε _)
    (lt_min (Real.rpow_pos_of_pos he₂ _) (Real.rpow_pos_of_pos he₃ _))
  set δ := T / kappaSARp P p L 3
  have hδ : 0 < δ := by positivity
  have hNδ : (f (x 0) - flow) / δ = kappaSARp P p L 3 * (f (x 0) - flow) / T := by
    simp only [δ]; field_simp
  have hs2 : 0 < kappaS2ARp P p L := by
    have := constant_pos (P := P) hf.nonneg _ P.θ₂_pos (p - 1)
    unfold kappaS2ARp; positivity
  obtain ⟨kε, hk, hF, hD⟩ := h.exists_isFirstHit_of_decrease hb hf hδ fun k hk hs => by
    have hk' : ∀ j ≤ k, ¬ arpTest f p P ε₁ (some e₂) (some e₃) x s σ j :=
      fun j hj => hk j (hj.trans k.le_succ)
    have hfail := not_arpStopTest_some_some.1 (hk (k + 1) le_rfl)
    rcases hfail with hg | ⟨-, hl | ⟨d, hd, h3 | h2⟩⟩
    · exact div_le_of_decrease hκ (one_le_kappaSARp_mul_kappaARp₁ hf.nonneg 3)
        (kappaARp₁_nonneg hf.nonneg) (min_le_left _ _) hε.le hg.le (by positivity)
        (lemma_4_1_4_i hf h hk' hs).2
    · exact div_le_of_decrease hκ (one_le_kappaSARp_mul_kappaARp₂ hf.nonneg (by norm_num))
        (kappaARp₂_nonneg hf.nonneg) ((min_le_right _ _).trans (min_le_left _ _)) he₂.le
        ((by linarith : e₂ ≤ -Chapter01.hessianMinEig f (x (k + 1))).trans (le_max_right _ _))
        hb0 (lemma_4_1_4_ii hf h (by simp) hk' hs)
    · exact div_le_of_decrease hκ (one_le_kappaSARp_mul_kappaARp₃ hf.nonneg le_rfl)
        (kappaARp₃_nonneg hf.nonneg) ((min_le_right _ _).trans (min_le_right _ _)) he₃.le
        h3.le hc0 (lemma_4_1_4_iii hf h (by simp) hk' hs d hd)
    · -- (4.1.43): a direction of `𝓜_{k+1}` with large curvature forces a long step
      have hiv := lemma_4_1_3_iv hf h (by simp) hk' hs d hd
      have hstep : kappaS2ARp P p L * e₂ ≤ ‖s k‖ ^ (p - 1) := by
        have := h2.le.trans hiv
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hs2] at this
        linarith
      have h37 := (lemma_4_1_4_i hf h hk' hs).1
      have hcm : b = ((p + 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
        simp only [b]; rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hpow : (kappaS2ARp P p L * e₂) ^ b ≤ ‖s k‖ ^ (p + 1) := by
        rw [hcm]
        exact Real.rpow_div_le_pow_of_le_pow (by positivity) (norm_nonneg _) (by omega) hstep
      have hD : kappaARp₂ P p L * e₂ ^ b ≤ f (x k) - f (x (k + 1)) := by
        rw [kappaARp₂_eq, mul_assoc, ← Real.mul_rpow hs2.le he₂.le]
        have := P.η₁_pos; have := P.σmin_pos
        exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans h37
      exact (div_le_mul_of_one_le hκ (one_le_kappaSARp_mul_kappaARp₂ hf.nonneg (by norm_num))
        ((min_le_right _ _).trans (min_le_left _ _)) (by positivity)).trans hD
  rw [hNδ] at hF hD
  have hcert := arpStopTest_some_some_certificate he₂.le
    (fun d hd => norm_eq_one_of_mem_arpCurvSet hd) hk.test
  refine ⟨kε, hk, ?_, hD, hcert.1, ?_⟩
  · calc (funEvalCount kε : ℝ) ≤ _ := hF
      _ = _ := by ring
  · rcases hcert.2 with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, h2.2⟩

end Complexity


section WellPosedness

open Chapter02 (e₀ norm_e₀ inner_e₀_smul)

/-! ### Third-order runs need not exist -/

section Counterexample

variable (a b : ℝ)

/-- The quartic `G(t) = a t²/2 + b t³/3 + t⁴` of the counterexample to the well-posedness of the
third-order mode of ARp. -/
noncomputable def arpQuartic (t : ℝ) : ℝ := a * t ^ 2 / 2 + b * t ^ 3 / 3 + t ^ 4

private theorem hasDerivAt_arpQuartic (t : ℝ) :
    HasDerivAt (arpQuartic a b) (a * t + b * t ^ 2 + 4 * t ^ 3) t := by
  have h1 := ((hasDerivAt_pow 2 t).const_mul a).div_const 2
  have h2 := ((hasDerivAt_pow 3 t).const_mul b).div_const 3
  have h3 := hasDerivAt_pow 4 t
  convert (h1.add h2).add h3 using 1
  · funext s; simp only [arpQuartic, Pi.add_apply]
  · norm_num; ring

private theorem deriv_arpQuartic :
    deriv (arpQuartic a b) = fun t => a * t + b * t ^ 2 + 4 * t ^ 3 :=
  funext fun t => (hasDerivAt_arpQuartic a b t).deriv

private theorem deriv2_arpQuartic :
    deriv (fun t : ℝ => a * t + b * t ^ 2 + 4 * t ^ 3) = fun t => a + 2 * b * t + 12 * t ^ 2 := by
  funext t
  have h1 := (hasDerivAt_id t).const_mul a
  have h2 := (hasDerivAt_pow 2 t).const_mul b
  have h3 := (hasDerivAt_pow 3 t).const_mul 4
  have h : HasDerivAt (fun t : ℝ => a * t + b * t ^ 2 + 4 * t ^ 3)
      (a + 2 * b * t + 12 * t ^ 2) t := by
    convert (h1.add h2).add h3 using 1
    · funext s; simp only [Pi.add_apply, id]
    · norm_num; ring
  exact h.deriv

private theorem deriv3_arpQuartic :
    deriv (fun t : ℝ => a + 2 * b * t + 12 * t ^ 2) = fun t => 2 * b + 24 * t := by
  funext t
  have h1 := ((hasDerivAt_id t).const_mul (2 * b)).const_add a
  have h3 := (hasDerivAt_pow 2 t).const_mul 12
  have h : HasDerivAt (fun t : ℝ => a + 2 * b * t + 12 * t ^ 2) (2 * b + 24 * t) t := by
    convert h1.add h3 using 1
    · funext s; simp only [Pi.add_apply, id]
    · norm_num; ring
  exact h.deriv

theorem iteratedDeriv_one_arpQuartic :
    iteratedDeriv 1 (arpQuartic a b) = fun t => a * t + b * t ^ 2 + 4 * t ^ 3 := by
  rw [iteratedDeriv_one, deriv_arpQuartic]

theorem iteratedDeriv_two_arpQuartic :
    iteratedDeriv 2 (arpQuartic a b) = fun t => a + 2 * b * t + 12 * t ^ 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one_arpQuartic, deriv2_arpQuartic]

theorem iteratedDeriv_three_arpQuartic :
    iteratedDeriv 3 (arpQuartic a b) = fun t => 2 * b + 24 * t := by
  rw [iteratedDeriv_succ, iteratedDeriv_two_arpQuartic, deriv3_arpQuartic]

theorem contDiff_arpQuartic : ContDiff ℝ ⊤ (arpQuartic a b) := by
  unfold arpQuartic
  fun_prop

end Counterexample

/-- **The third-order mode of ARp is not always well posed** ([cartis2022evaluation],
Algorithm 4.1.1 with `ε₃ < ∞`). Let `p = 3`, `ε₁, ε₂, ε₃ > 0` and constants with
`4 ε₃² ≤ 3 ε₂ σ₀`, and let `f(x) = ε₂ x²/2 + ε₃ x³/3 + x⁴` on `ℝ¹`, which satisfies f.Bb
(`f ≥ -ε₃⁴`) and f.DpL (`L_{f,3} = 24`). Then no ARp run starts from `x₀ = 0`: the termination
test fails at `0` (`∇f(0) = 0`, `λ_min[∇²f(0)] = ε₂`, `𝓜₀ = {±1}` and `|∇³f(0)[1]³| = 2 ε₃ > ε₃`),
but the model `m₀(s) - m₀(0) = s² (ε₂/2 + ε₃ s/3 + σ₀ s²/24)` is nonnegative, so no step satisfies
(4.1.10). -/
theorem not_exists_algorithm_4_1_1_third_order (P : ARpParams) {ε₁ e₂ e₃ : ℝ} (he₂ : 0 < e₂)
    (he₃ : 0 < e₃) (hσ : 4 * e₃ ^ 2 ≤ 3 * e₂ * P.σ₀) :
    Chapter02.AssumptionBb (ridge (arpQuartic e₂ e₃) e₀) (-e₃ ^ 4) ∧
      AssumptionDpL (ridge (arpQuartic e₂ e₃) e₀) 3 24 ∧
      ¬ ∃ x s σ, x 0 = 0 ∧
        algorithm_4_1_1 (ridge (arpQuartic e₂ e₃) e₀) 3 P ε₁ (some e₂) (some e₃) x s σ := by
  have hG : ContDiff ℝ ⊤ (arpQuartic e₂ e₃) := contDiff_arpQuartic e₂ e₃
  have hG3 : ContDiff ℝ 3 (arpQuartic e₂ e₃) := hG.of_le le_top
  refine ⟨fun y => ?_, ?_, ?_⟩
  · simp only [ridge_apply, arpQuartic]
    set t := ⟪e₀, y⟫
    nlinarith [sq_nonneg (t ^ 2 + e₃ * t / 6), sq_nonneg (e₃ ^ 2 - 0), sq_nonneg t,
      sq_nonneg (e₃ * t), sq_nonneg (t + e₃), mul_pos he₂ he₂, sq_nonneg (e₂ * t),
      sq_nonneg (t ^ 2 - e₃ ^ 2), sq_nonneg (e₃ * t + 2 * e₃ ^ 2)]
  · refine assumptionDpL_iff.2 ⟨contDiff_ridge hG3, by norm_num, ?_⟩
    refine iteratedFDerivLipschitzOn_ridge hG3 le_rfl norm_e₀.le (by norm_num) fun s t => ?_
    rw [iteratedDeriv_three_arpQuartic]
    simp only
    rw [show 2 * e₃ + 24 * s - (2 * e₃ + 24 * t) = 24 * (s - t) by ring, abs_mul]
    norm_num
  · rintro ⟨x, s, σ, hx0, h⟩
    have hd2 : ∀ d : EuclideanSpace ℝ (Fin 1),
        iteratedFDeriv ℝ 2 (ridge (arpQuartic e₂ e₃) e₀) (x 0) (fun _ => d) =
          e₂ * ⟪e₀, d⟫ ^ 2 := fun d => by
      rw [iteratedFDeriv_ridge_apply_diag hG (by exact_mod_cast le_top), hx0, inner_zero_right,
        iteratedDeriv_two_arpQuartic]
      ring
    have hd3 : ∀ d : EuclideanSpace ℝ (Fin 1),
        iteratedFDeriv ℝ 3 (ridge (arpQuartic e₂ e₃) e₀) (x 0) (fun _ => d) =
          2 * e₃ * ⟪e₀, d⟫ ^ 3 := fun d => by
      rw [iteratedFDeriv_ridge_apply_diag hG (by exact_mod_cast le_top), hx0, inner_zero_right,
        iteratedDeriv_three_arpQuartic]
      ring
    have he₀ : ⟪e₀, e₀⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_e₀]; norm_num
    -- the test fails at `x₀ = 0`
    have htest : ¬ arpTest (ridge (arpQuartic e₂ e₃) e₀) 3 P ε₁ (some e₂) (some e₃) x s σ 0 := by
      rw [arpTest, not_arpStopTest_some_some]
      have hlam : Chapter01.hessianMinEig (ridge (arpQuartic e₂ e₃) e₀) (x 0) = e₂ := by
        rw [Chapter03.hessianMinEig_ridge (hG.of_le le_top), hx0, inner_zero_right,
          iteratedDeriv_two_arpQuartic]
        ring
      refine Or.inr ⟨hlam.le, Or.inr ⟨e₀, ⟨norm_e₀, ?_⟩, Or.inl ?_⟩⟩
      · rw [hd2, he₀]; simp [abs_of_pos he₂]
      · rw [hd3, he₀, one_pow, mul_one, abs_of_pos (by linarith)]
        linarith
    have hstep := (h.step (k := 0) fun j hj => by
      rw [Nat.le_zero.1 hj]; exact htest).decrease
    rw [h.run.toIsARRun.sigma_zero] at hstep
    -- the model does not decrease
    set t := ⟪e₀, s 0⟫
    have hT : taylorPolynomial (ridge (arpQuartic e₂ e₃) e₀) 3 (x 0) (s 0) =
        arpQuartic e₂ e₃ 0 + e₂ * t ^ 2 / 2 + e₃ * t ^ 3 / 3 := by
      rw [Optimization.taylorPolynomial_ridge hG3, hx0, inner_zero_right]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero,
        iteratedDeriv_one_arpQuartic, iteratedDeriv_two_arpQuartic, iteratedDeriv_three_arpQuartic]
      norm_num [Nat.factorial]
      ring
    have hm : regularizedModel (ftaylorSeries ℝ (ridge (arpQuartic e₂ e₃) e₀) (x 0)) 3 P.σ₀ (s 0) -
        regularizedModel (ftaylorSeries ℝ (ridge (arpQuartic e₂ e₃) e₀) (x 0)) 3 P.σ₀ 0 =
          t ^ 2 * (e₂ / 2 + e₃ * t / 3 + P.σ₀ * t ^ 2 / 24) := by
      rw [regularizedModel_ftaylorSeries_zero_right, regularizedModel_def,
        ← taylorPolynomial_eq_taylorSum, hT, Chapter03.norm_eq_abs_inner_e₀, hx0]
      simp only [ridge_apply, inner_zero_right]
      rw [show 3 + 1 = 2 * 2 by rfl, pow_mul, sq_abs]
      norm_num [Nat.factorial]
      ring
    have hσ₀ := P.σ₀_pos
    have hq : 0 ≤ e₂ / 2 + e₃ * t / 3 + P.σ₀ * t ^ 2 / 24 := by
      nlinarith [sq_nonneg (P.σ₀ * t + 4 * e₃)]
    have := mul_nonneg (sq_nonneg t) hq
    linarith


end WellPosedness

/-! ### Theorem 4.1.6 -/

section Sharpness

open Chapter02 (e₀ norm_e₀ inner_e₀_smul)
open Chapter03 (norm_eq_abs_inner_e₀ inner_e₀_sq)

theorem abs_inner_e₀_eq_one {d : EuclideanSpace ℝ (Fin 1)} (hd : ‖d‖ = 1) : |⟪e₀, d⟫| = 1 := by
  rw [← norm_eq_abs_inner_e₀, hd]

/-! ### The one-dimensional data -/

/-- The termination index `⌈ε^{-(p+1)/(p-q+1)}⌉` of the one-dimensional ARp examples. -/
noncomputable def arpSlowK (p q : ℕ) (ε : ℝ) : ℕ :=
  ⌈ε ^ (-((p + 1 : ℝ) / ((p - q + 1 : ℕ) : ℝ)))⌉₊

theorem arpSlowK_pos {p q : ℕ} {ε : ℝ} (hε : 0 < ε) : 0 < arpSlowK p q ε :=
  Nat.ceil_pos.2 (Real.rpow_pos_of_pos hε _)

theorem arpSlowK_one {p : ℕ} (hp : 1 ≤ p) (ε : ℝ) :
    arpSlowK p 1 ε = ⌈ε ^ (-(((p : ℝ) + 1) / p))⌉₊ := by
  rw [arpSlowK, Nat.sub_add_cancel hp]

theorem arpSlowK_two {p : ℕ} (hp : 2 ≤ p) (ε : ℝ) :
    arpSlowK p 2 ε = ⌈ε ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 1)))⌉₊ := by
  rw [arpSlowK, show p - 2 + 1 = p - 1 by omega, Nat.cast_sub (by omega), Nat.cast_one]

theorem arpSlowK_three {p : ℕ} (hp : 3 ≤ p) (ε : ℝ) :
    arpSlowK p 3 ε = ⌈ε ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 2)))⌉₊ := by
  rw [arpSlowK, show p - 3 + 1 = p - 2 by omega, Nat.cast_sub (by omega)]
  norm_num

/-- **The one-dimensional ARp examples** (the data of Theorem 12.2.15 of [cartis2022evaluation]
with the scale `c = p!/((q-1)! σ₀)`, `Optimization.exists_slowTaylorOrder_interpolant`). For
`1 ≤ q ≤ p` there are constants `L ≥ 1`, `B ≥ 0` (depending on `p, q, σ₀` only) such that for every
`ε ∈ (0, 1]` there are a `C^p` function `G` (whose ridge `f` on `ℝ¹` satisfies f.Bb with
`f_low = -B` and f.DpL with constant `L`) and points `x_0 = 0, …, x_{k_ε}` with spike jets
`G^{(q)}(x_k) = -α_k`, spaced by the global minimizers of the one-dimensional ARp models with
`σ = σ₀`, and with `G(x_{k+1}) = T_{f,p}(x_k, s_k)`. -/
theorem exists_arp_slow_data (P : ARpParams) {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    ∃ L B : ℝ, 1 ≤ L ∧ 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (G : ℝ → ℝ) (xr : ℕ → ℝ), ContDiff ℝ p G ∧
        Chapter02.AssumptionBb (ridge G e₀) (-B) ∧ AssumptionDpL (ridge G e₀) p L ∧ xr 0 = 0 ∧
        (∀ k ≤ arpSlowK p q ε,
          IsSpikeJetOf p G q (xr k) (Chapter03.ar2SlowAlpha ε (arpSlowK p q ε) k)) ∧
        (∀ k < arpSlowK p q ε, xr (k + 1) = xr k +
          monomialMinimizer p q P.σ₀ (Chapter03.ar2SlowAlpha ε (arpSlowK p q ε) k)) ∧
        ∀ k < arpSlowK p q ε, G (xr (k + 1)) = G (xr k) -
          Chapter03.ar2SlowAlpha ε (arpSlowK p q ε) k * (xr (k + 1) - xr k) ^ q / q ! := by
  have hσ₀ := P.σ₀_pos
  set c : ℝ := (p ! : ℝ) / (P.σ₀ * (q - 1)!)
  have hc : 0 < c := by positivity
  have hcα : ∀ α : ℝ, c * α = α / (P.σ₀ * (q - 1)! / p !) := fun α => by
    simp only [c]; field_simp
  obtain ⟨L, B, hL, hB, H⟩ := exists_slowTaylorOrder_interpolant hq hqp hc
  refine ⟨max L 1, B, le_max_right _ _, hB, fun ε hε hε1 => ?_⟩
  set K := arpSlowK p q ε
  set xr : ℕ → ℝ := fun k => ∑ j ∈ range k,
    (c * (ε + ε * ((K : ℝ) - j) / K)) ^ (1 / ((p - q + 1 : ℕ) : ℝ))
  obtain ⟨G, hG, hGL, hGB, hGk, hGv⟩ := H ε K xr hε hε1 rfl
    (fun k _ => by simp only [xr, sum_range_succ])
  have hb : Chapter02.AssumptionBb (ridge G e₀) (-B) := fun y => by
    have := hGB 0 (by omega) ⟪e₀, y⟫
    rw [iteratedDeriv_zero] at this
    rw [ridge_apply]; linarith [neg_abs_le (G ⟪e₀, y⟫)]
  have hDpL : AssumptionDpL (ridge G e₀) p (max L 1) := assumptionDpL_iff.2
    ⟨contDiff_ridge hG, le_max_right _ _, iteratedFDerivLipschitzOn_ridge hG le_rfl norm_e₀.le
      (by positivity) fun s t => (hGL s t).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))⟩
  refine ⟨G, xr, hG, hb, hDpL, by simp [xr], fun k hk => hGk k hk, fun k _ => ?_,
    fun k hk => hGv k hk⟩
  simp only [xr, sum_range_succ, Chapter03.ar2SlowAlpha, monomialMinimizer, hcα]

/-! ### Ridge functions at the iterates -/

section RidgeAt

variable {p : ℕ} {G : ℝ → ℝ}

theorem norm_gradient_ridge_e₀ (hG : ContDiff ℝ 1 G) (a : ℝ) :
    ‖gradient (ridge G e₀) (a • e₀)‖ = |iteratedDeriv 1 G a| := by
  rw [gradient_ridge (hG.differentiable one_ne_zero), inner_e₀_smul, norm_smul, norm_e₀, mul_one,
    Real.norm_eq_abs, iteratedDeriv_one]

theorem hessianMinEig_ridge_e₀ (hG : ContDiff ℝ 2 G) (a : ℝ) :
    Chapter01.hessianMinEig (ridge G e₀) (a • e₀) = iteratedDeriv 2 G a := by
  rw [Chapter03.hessianMinEig_ridge hG, inner_e₀_smul]

theorem iteratedFDeriv_ridge_e₀ (hG : ContDiff ℝ p G) {j : ℕ} (hj : j ≤ p) (a : ℝ)
    (d : EuclideanSpace ℝ (Fin 1)) :
    iteratedFDeriv ℝ j (ridge G e₀) (a • e₀) (fun _ => d) = iteratedDeriv j G a * ⟪e₀, d⟫ ^ j := by
  rw [iteratedFDeriv_ridge_apply_diag hG (by exact_mod_cast hj), inner_e₀_smul]

theorem abs_iteratedFDeriv_ridge_e₀ (hG : ContDiff ℝ p G) {j : ℕ} (hj : j ≤ p) (a : ℝ)
    {d : EuclideanSpace ℝ (Fin 1)} (hd : ‖d‖ = 1) :
    |iteratedFDeriv ℝ j (ridge G e₀) (a • e₀) (fun _ => d)| = |iteratedDeriv j G a| := by
  rw [iteratedFDeriv_ridge_e₀ hG hj, abs_mul, abs_pow, abs_inner_e₀_eq_one hd, one_pow, mul_one]

end RidgeAt

/-! ### Theorem 4.1.6 -/

/-- **Theorem 4.1.6** of [cartis2022evaluation], first order (sharpness of Theorem 4.1.5 (i); the
book defers the proof to §12.2.2.4). For every `p ≥ 1` and all ARp constants there are `f_low` and
`L_{f,p} ≥ 1` such that for every `ε₁ ∈ (0, 1]` there are `f : ℝ¹ → ℝ` satisfying f.Bb and f.DpL
and an ARp run with `ε₂ = ε₃ = +∞` from `x₀ = 0`, with `σ_k = σ₀`, steps that are global
minimizers of the models and `ρ_k = 1` (every iteration very successful), which terminates
exactly at iteration `⌈ε₁^{-(p+1)/p}⌉` (after `⌈ε₁^{-(p+1)/p}⌉ + 1` evaluations of `f` and of its
derivatives). -/
theorem theorem_4_1_6_i (P : ARpParams) {p : ℕ} (hp : 1 ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧ AssumptionDpL f p L ∧
        ∃ x s σ, x 0 = 0 ∧ algorithm_4_1_1 f p P ε₁ none none x s σ ∧ (∀ k, σ k = P.σ₀) ∧
          (∀ k < ⌈ε₁ ^ (-(((p : ℝ) + 1) / p))⌉₊,
            IsMinOn (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) univ (s k) ∧
              taylorRatio f p x s k = 1) ∧
          IsFirstHit (fun k => ‖gradient f (x k)‖ ≤ ε₁) ⌈ε₁ ^ (-(((p : ℝ) + 1) / p))⌉₊ := by
  obtain ⟨L, B, hL, -, H⟩ := exists_arp_slow_data P le_rfl hp
  refine ⟨-B, L, hL, fun ε hε hε1 => ?_⟩
  obtain ⟨G, xr, hG, hb, hDpL, hx0, hd, hx, hv⟩ := H ε hε hε1
  have hK := arpSlowK_pos (p := p) (q := 1) hε
  set K := arpSlowK p 1 ε
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast hp)
  have htest : ∀ k ≤ K, (arpTest (ridge G e₀) p P ε none none (fun k => xr k • e₀)
      (fun k => (xr (k + 1) - xr k) • e₀) (fun _ => P.σ₀) k ↔ K ≤ k) := fun k hk => by
    rw [arpTest, arpStopTest_none, norm_gradient_ridge_e₀ hG1, (hd k hk).1, abs_neg,
      abs_of_pos (Chapter03.ar2SlowAlpha_pos hε hK hk)]
    exact Chapter03.ar2SlowAlpha_le_iff hε hK hk
  obtain ⟨hrun, hhit, hmin⟩ := arp_ridge_run P.toARpParams norm_e₀ norm_eq_abs_inner_e₀ (r := 1)
    le_rfl hp (by omega) (by omega) hG
    (fun k hk => Chapter03.ar2SlowAlpha_pos hε hK hk.le) (fun k hk => hd k hk.le) hx hv htest
  have htest' : arpTest (ridge G e₀) p P ε none none (fun k => xr k • e₀)
      (fun k => (xr (k + 1) - xr k) • e₀) (fun _ => P.σ₀) =
      fun k => ‖gradient (ridge G e₀) (xr k • e₀)‖ ≤ ε :=
    funext fun k => propext arpStopTest_none
  refine ⟨ridge G e₀, hb, hDpL, _, _, _, by rw [hx0, zero_smul],
    ⟨hp, by simpa using hp, hε, by simp, by simp, fun _ => rfl, hrun⟩, fun _ => rfl, ?_, ?_⟩
  · rw [← arpSlowK_one hp]; exact hmin
  · rw [← arpSlowK_one hp, ← htest']; exact hhit

/-- ARp runs on one-dimensional spike data, assembled as runs of Algorithm 4.1.1: under the
well-posedness conditions of the tolerances, if the termination test of the explicit sequences
holds at `k ≤ K` exactly when `k = K`, there is an ARp run from `0` with `σ_k = σ₀` terminating
exactly at `K`. -/
theorem exists_algorithm_4_1_1_ridge (P : ARpParams) {p q : ℕ} {ε₁ : ℝ} {ε₂ ε₃ : Option ℝ}
    (hp : 1 ≤ p) (hord : arpOrder ε₂ ε₃ ≤ p) (hε₁ : 0 < ε₁) (hε₂ : ∀ e ∈ ε₂, 0 < e)
    (hε₃ : ∀ e ∈ ε₃, 0 < e) (h32 : ε₂ = none → ε₃ = none) (hq : 1 ≤ q) (hqp : q ≤ p)
    (hthird : 3 ≤ arpOrder ε₂ ε₃ → q ≤ 3 ∧ 3 ≤ p ∧ P.σ₀ ≤ (p - 2)! * P.θ₃) {G : ℝ → ℝ}
    (hG : ContDiff ℝ p G) {xr α : ℕ → ℝ} {K : ℕ} (hα : ∀ k < K, 0 < α k)
    (hd : ∀ k < K, IsSpikeJetOf p G q (xr k) (α k))
    (hx : ∀ k < K, xr (k + 1) = xr k + monomialMinimizer p q P.σ₀ (α k))
    (hval : ∀ k < K, G (xr (k + 1)) = G (xr k) - α k * (xr (k + 1) - xr k) ^ q / q !)
    (hx0 : xr 0 = 0)
    (htest : ∀ k ≤ K, (arpTest (ridge G e₀) p P ε₁ ε₂ ε₃ (fun k => xr k • e₀)
      (fun k => (xr (k + 1) - xr k) • e₀) (fun _ => P.σ₀) k ↔ K ≤ k)) :
    ∃ x s σ, x 0 = 0 ∧ algorithm_4_1_1 (ridge G e₀) p P ε₁ ε₂ ε₃ x s σ ∧ (∀ k, σ k = P.σ₀) ∧
      IsFirstHit (arpTest (ridge G e₀) p P ε₁ ε₂ ε₃ x s σ) K ∧ ∀ k, x k = xr k • e₀ := by
  obtain ⟨hrun, hhit, -⟩ := arp_ridge_run P.toARpParams norm_e₀ norm_eq_abs_inner_e₀ hq hqp
    (fun h2 => h2.trans hord) hthird hG hα hd hx hval htest
  exact ⟨_, _, _, by simp only [hx0, zero_smul], ⟨hp, hord, hε₁, hε₂, hε₃, h32, hrun⟩,
    fun _ => rfl, hhit, fun _ => rfl⟩

/-- A predicate that holds at `k ≤ K` exactly when `k = K` first holds at `K`. -/
theorem isFirstHit_of_forall_le_iff {test : ℕ → Prop} {K : ℕ} (h : ∀ k ≤ K, (test k ↔ K ≤ k)) :
    IsFirstHit test K :=
  ⟨(h K le_rfl).2 le_rfl, fun j hj ht => absurd ((h j hj.le).1 ht) (not_le.2 hj)⟩

/-- **Theorem 4.1.6** of [cartis2022evaluation], second order (sharpness of Theorem 4.1.5 (ii)).
For every `p ≥ 2` and all ARp constants there are `f_low` and `L_{f,p} ≥ 1` such that for all
`ε₁, ε₂ ∈ (0, 1]` there are `f : ℝ¹ → ℝ` satisfying f.Bb and f.DpL and an ARp run with
`ε₃ = +∞` from `x₀ = 0` with `σ_k = σ₀` whose first approximate second-order minimizer (the
termination index) is `x_k` with `k = max(⌈ε₁^{-(p+1)/p}⌉, ⌈ε₂^{-(p+1)/(p-1)}⌉)`. (If the first
term dominates, the example of Theorem 4.1.6 (i) with zero curvature is used; otherwise a
negative-curvature example with zero gradients, `λ_min[∇²f(x_k)] = -(ε₂ + ω_k)`.) -/
theorem theorem_4_1_6_ii (P : ARpParams) {p : ℕ} (hp : 2 ≤ p) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε₁ e₂ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → 0 < e₂ → e₂ ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧ AssumptionDpL f p L ∧
        ∃ x s σ, x 0 = 0 ∧ algorithm_4_1_1 f p P ε₁ (some e₂) none x s σ ∧
          (∀ k, σ k = P.σ₀) ∧
          IsFirstHit (fun k => Chapter03.IsApproxSecondOrderMinimizer f (x k) ε₁ e₂)
            (max ⌈ε₁ ^ (-(((p : ℝ) + 1) / p))⌉₊ ⌈e₂ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 1)))⌉₊) := by
  obtain ⟨L₁, B₁, hL₁, -, H₁⟩ := exists_arp_slow_data P le_rfl (by omega : 1 ≤ p)
  obtain ⟨L₂, B₂, -, -, H₂⟩ := exists_arp_slow_data P (q := 2) (by norm_num) hp
  refine ⟨-max B₁ B₂, max L₁ L₂, hL₁.trans (le_max_left _ _),
    fun ε₁ e₂ hε₁ hε₁1 he₂ he₂1 => ?_⟩
  have hord : arpOrder (some e₂) none ≤ p := by simpa using hp
  have hG2 : ∀ {G : ℝ → ℝ}, ContDiff ℝ p G → ContDiff ℝ 2 G := fun hG =>
    hG.of_le (by exact_mod_cast hp)
  have hsecond : ∀ (f : EuclideanSpace ℝ (Fin 1) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin 1))
      (σ : ℕ → ℝ), arpTest f p P ε₁ (some e₂) none x s σ =
        fun k => Chapter03.IsApproxSecondOrderMinimizer f (x k) ε₁ e₂ := fun f x s σ => by
    funext k
    rw [arpTest, arpStopTest_none_right (by simpa using he₂.le), Chapter03.stopTest_some]
  rcases le_total ⌈e₂ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 1)))⌉₊ ⌈ε₁ ^ (-(((p : ℝ) + 1) / p))⌉₊
    with hle | hle
  · -- the first-order example
    rw [max_eq_left hle, ← arpSlowK_one (by omega)]
    obtain ⟨G, xr, hG, hb, hDpL, hx0, hd, hx, hv⟩ := H₁ ε₁ hε₁ hε₁1
    have hK := arpSlowK_pos (p := p) (q := 1) hε₁
    obtain ⟨x, s, σ, hx0', halg, hσ, hhit, -⟩ :=
      exists_algorithm_4_1_1_ridge P (by omega) hord hε₁
      (by simpa using he₂) (by simp) (by simp) le_rfl (by omega) (by simp) hG
      (fun k hk => Chapter03.ar2SlowAlpha_pos hε₁ hK hk.le) (fun k hk => hd k hk.le) hx hv hx0
      fun k hk => by
        rw [hsecond]
        dsimp only
        rw [Chapter03.IsApproxSecondOrderMinimizer, norm_gradient_ridge_e₀
          (hG.of_le (by exact_mod_cast (by omega : 1 ≤ p))), hessianMinEig_ridge_e₀ (hG2 hG),
          (hd k hk).1, (hd k hk).2 2 (by norm_num) hp (by norm_num), abs_neg,
          abs_of_pos (Chapter03.ar2SlowAlpha_pos hε₁ hK hk),
          ← Chapter03.ar2SlowAlpha_le_iff hε₁ hK hk]
        exact ⟨fun h => h.1, fun h => ⟨h, by linarith⟩⟩
    refine ⟨ridge G e₀, fun y => (hb y).trans' (by linarith [le_max_left B₁ B₂]),
      hDpL.mono (le_max_left _ _), x, s, σ, hx0', halg, hσ, ?_⟩
    rw [← hsecond (ridge G e₀) x s σ]; exact hhit
  · -- the negative-curvature example
    rw [max_eq_right hle, ← arpSlowK_two hp]
    obtain ⟨G, xr, hG, hb, hDpL, hx0, hd, hx, hv⟩ := H₂ e₂ he₂ he₂1
    have hK := arpSlowK_pos (p := p) (q := 2) he₂
    obtain ⟨x, s, σ, hx0', halg, hσ, hhit, -⟩ :=
      exists_algorithm_4_1_1_ridge P (by omega) hord hε₁
      (by simpa using he₂) (by simp) (by simp) (by norm_num) hp (by simp) hG
      (fun k hk => Chapter03.ar2SlowAlpha_pos he₂ hK hk.le) (fun k hk => hd k hk.le) hx hv hx0
      fun k hk => by
        rw [hsecond]
        dsimp only
        rw [Chapter03.IsApproxSecondOrderMinimizer, norm_gradient_ridge_e₀
          (hG.of_le (by exact_mod_cast (by omega : 1 ≤ p))), hessianMinEig_ridge_e₀ (hG2 hG),
          (hd k hk).1, (hd k hk).2 1 le_rfl (by omega) (by norm_num), abs_zero, neg_le_neg_iff,
          ← Chapter03.ar2SlowAlpha_le_iff he₂ hK hk]
        exact ⟨fun h => h.2, fun h => ⟨hε₁.le, h⟩⟩
    refine ⟨ridge G e₀, fun y => (hb y).trans' (by linarith [le_max_right B₁ B₂]),
      hDpL.mono (le_max_right _ _), x, s, σ, hx0', halg, hσ, ?_⟩
    rw [← hsecond (ridge G e₀) x s σ]; exact hhit

/-- The third-order test holds when `‖∇f(x)‖ ≤ ε₁`, `λ_min[∇²f(x)] ≥ -ε₂` and every `d ∈ M`
satisfies (4.1.8) and (4.1.9). -/
theorem arpStopTest_some_some_of {f : EuclideanSpace ℝ (Fin n) → ℝ} {ε₁ e₂ e₃ : ℝ}
    {M : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (hg : ‖gradient f x‖ ≤ ε₁) (hl : -e₂ ≤ Chapter01.hessianMinEig f x)
    (hM : ∀ d ∈ M, |iteratedFDeriv ℝ 3 f x (fun _ => d)| ≤ e₃ ∧
      |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ e₂) :
    arpStopTest f ε₁ (some e₂) (some e₃) M x :=
  ⟨hg, fun e he => by
    cases he
    exact Or.inr ⟨hl, fun e' he' d hd => by cases he'; exact hM d hd⟩⟩

/-- **Theorem 4.1.6** of [cartis2022evaluation], third order (sharpness of Theorem 4.1.5 (iii)),
**under the restriction `σ₀ ≤ (p-2)! min(θ₂, θ₃)` on the constants**. For every `p ≥ 3` and all
ARp constants with `σ₀ ≤ (p-2)! min(θ₂, θ₃)` there are `f_low` and `L_{f,p} ≥ 1` such that for all
`ε₁, ε₂, ε₃ ∈ (0, 1]` there are `f : ℝ¹ → ℝ` satisfying f.Bb and f.DpL and an ARp run from
`x₀ = 0` with `σ_k = σ₀` which terminates exactly at iteration
`K = max(⌈ε₁^{-(p+1)/p}⌉, ⌈ε₂^{-(p+1)/(p-1)}⌉, ⌈ε₃^{-(p+1)/(p-2)}⌉)`; moreover `x_K` is also the
first iterate that is an `ε`-approximate third-order minimizer in the sense of (4.1.3)–(4.1.4)
(`IsApproxThirdOrderMinimizer`), so the sharpness holds for the true criterion as well as for the
algorithm's test. The restriction is a sufficient condition: it makes the global model minimizers
satisfy (4.1.13) (`σ₀ ≤ (p-2)! θ₃`) and keeps `±e₀` in the sets `𝓜_{k+1}` of the third-order
example (`σ₀ ≤ (p-2)! θ₂`), so that its test fails before the last iteration. (The exact
conditions on these examples are weaker and depend on the example, e.g.
`σ₀ ((p-2)/p!) ≤ θ₂` and `σ₀ (1/(p-2)! - 2/p!) ≤ θ₃` for the third-order one.) For other
constants the claim of the book is unproved: if `±e₀ ∉ 𝓜_{k+1}`, then `𝓜_{k+1} = ∅` and, with the
vacuous reading of Step 1, the test holds as soon as `‖∇f‖ ≤ ε₁` and `λ_min ≥ -ε₂`, while with the
book's requirement `𝓜_k ≠ ∅` the run cannot terminate at all. -/
theorem theorem_4_1_6_iii (P : ARpParams) {p : ℕ} (hp : 3 ≤ p)
    (hσ : P.σ₀ ≤ (p - 2)! * min P.θ₂ P.θ₃) :
    ∃ flow L : ℝ, 1 ≤ L ∧ ∀ ε₁ e₂ e₃ : ℝ, 0 < ε₁ → ε₁ ≤ 1 → 0 < e₂ → e₂ ≤ 1 → 0 < e₃ → e₃ ≤ 1 →
      ∃ f : EuclideanSpace ℝ (Fin 1) → ℝ, Chapter02.AssumptionBb f flow ∧ AssumptionDpL f p L ∧
        ∃ x s σ, x 0 = 0 ∧ algorithm_4_1_1 f p P ε₁ (some e₂) (some e₃) x s σ ∧
          (∀ k, σ k = P.σ₀) ∧
          IsFirstHit (arpTest f p P ε₁ (some e₂) (some e₃) x s σ)
            (max (max ⌈ε₁ ^ (-(((p : ℝ) + 1) / p))⌉₊
              ⌈e₂ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 1)))⌉₊)
              ⌈e₃ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 2)))⌉₊) ∧
          IsFirstHit (fun k => IsApproxThirdOrderMinimizer f (x k) ε₁ e₂ e₃)
            (max (max ⌈ε₁ ^ (-(((p : ℝ) + 1) / p))⌉₊
              ⌈e₂ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 1)))⌉₊)
              ⌈e₃ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 2)))⌉₊) := by
  obtain ⟨L₁, B₁, hL₁, -, H₁⟩ := exists_arp_slow_data P le_rfl (by omega : 1 ≤ p)
  obtain ⟨L₂, B₂, -, -, H₂⟩ := exists_arp_slow_data P (p := p) (q := 2) (by norm_num) (by omega)
  obtain ⟨L₃, B₃, -, -, H₃⟩ := exists_arp_slow_data P (q := 3) (by norm_num) hp
  refine ⟨-max B₁ (max B₂ B₃), max L₁ (max L₂ L₃), hL₁.trans (le_max_left _ _),
    fun ε₁ e₂ e₃ hε₁ hε₁1 he₂ he₂1 he₃ he₃1 => ?_⟩
  have hord : arpOrder (some e₂) (some e₃) ≤ p := by simpa using hp
  have hσ₀ := P.σ₀_pos
  have hthird : 3 ≤ arpOrder (some e₂) (some e₃) → ∀ q, q ≤ 3 →
      q ≤ 3 ∧ 3 ≤ p ∧ P.σ₀ ≤ (p - 2)! * P.θ₃ := fun _ q hq =>
    ⟨hq, hp, hσ.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity))⟩
  have hG' : ∀ {G : ℝ → ℝ}, ContDiff ℝ p G → ContDiff ℝ 1 G ∧ ContDiff ℝ 2 G := fun hG =>
    ⟨hG.of_le (by exact_mod_cast (by omega : 1 ≤ p)), hG.of_le (by exact_mod_cast (by omega))⟩
  have hunit : ∀ {x s : ℕ → EuclideanSpace ℝ (Fin 1)} {σ : ℕ → ℝ} {k : ℕ} {d}
      {f : EuclideanSpace ℝ (Fin 1) → ℝ}, d ∈ arpCurvSet f p P (some e₂) x s σ k → ‖d‖ = 1 :=
    fun hd => norm_eq_one_of_mem_arpCurvSet hd
  set A := ⌈ε₁ ^ (-(((p : ℝ) + 1) / p))⌉₊
  set B := ⌈e₂ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 1)))⌉₊
  set C := ⌈e₃ ^ (-(((p : ℝ) + 1) / ((p : ℝ) - 2)))⌉₊
  rcases (by omega : (B ≤ A ∧ C ≤ A) ∨ (A ≤ B ∧ C ≤ B) ∨ (A ≤ C ∧ B ≤ C)) with hm | hm | hm
  · -- the first-order example
    rw [show max (max A B) C = A by omega,
      show A = arpSlowK p 1 ε₁ from (arpSlowK_one (by omega) _).symm]
    obtain ⟨G, xr, hG, hb, hDpL, hx0, hd, hx, hv⟩ := H₁ ε₁ hε₁ hε₁1
    have hK := arpSlowK_pos (p := p) (q := 1) hε₁
    obtain ⟨x, s, σ, hx0', halg, hσ', hhit, hxk⟩ :=
      exists_algorithm_4_1_1_ridge P (by omega) hord hε₁
      (by simpa using he₂) (by simpa using he₃) (by simp) le_rfl (by omega)
      (fun h => hthird h 1 (by norm_num)) hG
      (fun k hk => Chapter03.ar2SlowAlpha_pos hε₁ hK hk.le) (fun k hk => hd k hk.le) hx hv hx0
      fun k hk => by
        have hα := Chapter03.ar2SlowAlpha_pos hε₁ hK hk
        have hg : ‖gradient (ridge G e₀) (xr k • e₀)‖ =
            Chapter03.ar2SlowAlpha ε₁ (arpSlowK p 1 ε₁) k := by
          rw [norm_gradient_ridge_e₀ (hG' hG).1, (hd k hk).1, abs_neg, abs_of_pos hα]
        rcases hk.lt_or_eq with hlt | rfl
        · refine iff_of_false (not_arpStopTest_some_some.2 (Or.inl ?_)) (not_le.2 hlt)
          rw [hg]
          exact not_le.1 fun h => (not_le.2 hlt) ((Chapter03.ar2SlowAlpha_le_iff hε₁ hK hk).1 h)
        · refine iff_of_true (arpStopTest_some_some_of ?_ ?_ fun d hd' => ?_) le_rfl
          · rw [hg]; exact (Chapter03.ar2SlowAlpha_le_iff hε₁ hK hk).2 le_rfl
          · rw [hessianMinEig_ridge_e₀ (hG' hG).2, (hd _ hk).2 2 (by norm_num) (by omega)
              (by norm_num)]
            linarith
          · rw [abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ (hunit hd'),
              abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ (hunit hd'),
              (hd _ hk).2 3 (by norm_num) hp (by norm_num),
              (hd _ hk).2 2 (by norm_num) (by omega) (by norm_num), abs_zero]
            exact ⟨he₃.le, he₂.le⟩
    have hcrit : IsFirstHit (fun k => IsApproxThirdOrderMinimizer (ridge G e₀) (x k) ε₁ e₂ e₃)
        (arpSlowK p 1 ε₁) := by
      simp only [hxk]
      refine isFirstHit_of_forall_le_iff fun k hk => ?_
      have hα := Chapter03.ar2SlowAlpha_pos hε₁ hK hk
      rw [IsApproxThirdOrderMinimizer, Chapter03.IsApproxSecondOrderMinimizer,
        norm_gradient_ridge_e₀ (hG' hG).1, (hd k hk).1, abs_neg, abs_of_pos hα,
        hessianMinEig_ridge_e₀ (hG' hG).2, (hd k hk).2 2 (by norm_num) (by omega) (by norm_num),
        ← Chapter03.ar2SlowAlpha_le_iff hε₁ hK hk]
      refine ⟨fun h => h.1.1, fun h => ⟨⟨h, by linarith⟩, fun d hd' => ?_⟩⟩
      rw [abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ hd'.1,
        (hd k hk).2 3 (by norm_num) hp (by norm_num), abs_zero]
      exact he₃.le
    exact ⟨ridge G e₀, fun y => (hb y).trans' (by linarith [le_max_left B₁ (max B₂ B₃)]),
      hDpL.mono (le_max_left _ _), x, s, σ, hx0', halg, hσ', hhit, hcrit⟩
  · -- the negative-curvature example
    rw [show max (max A B) C = B by omega,
      show B = arpSlowK p 2 e₂ from (arpSlowK_two (by omega) _).symm]
    obtain ⟨G, xr, hG, hb, hDpL, hx0, hd, hx, hv⟩ := H₂ e₂ he₂ he₂1
    have hK := arpSlowK_pos (p := p) (q := 2) he₂
    obtain ⟨x, s, σ, hx0', halg, hσ', hhit, hxk⟩ :=
      exists_algorithm_4_1_1_ridge P (by omega) hord hε₁
      (by simpa using he₂) (by simpa using he₃) (by simp) (by norm_num) (by omega)
      (fun h => hthird h 2 (by norm_num)) hG
      (fun k hk => Chapter03.ar2SlowAlpha_pos he₂ hK hk.le) (fun k hk => hd k hk.le) hx hv hx0
      fun k hk => by
        have hα := Chapter03.ar2SlowAlpha_pos he₂ hK hk
        have hl : Chapter01.hessianMinEig (ridge G e₀) (xr k • e₀) =
            -Chapter03.ar2SlowAlpha e₂ (arpSlowK p 2 e₂) k := by
          rw [hessianMinEig_ridge_e₀ (hG' hG).2, (hd k hk).1]
        rcases hk.lt_or_eq with hlt | rfl
        · refine iff_of_false (not_arpStopTest_some_some.2 (Or.inr ⟨by linarith, Or.inl ?_⟩))
            (not_le.2 hlt)
          rw [hl, neg_lt_neg_iff]
          exact not_le.1 fun h => (not_le.2 hlt) ((Chapter03.ar2SlowAlpha_le_iff he₂ hK hk).1 h)
        · have hαle := (Chapter03.ar2SlowAlpha_le_iff he₂ hK hk).2 le_rfl
          refine iff_of_true (arpStopTest_some_some_of ?_ ?_ fun d hd' => ?_) le_rfl
          · rw [norm_gradient_ridge_e₀ (hG' hG).1, (hd _ hk).2 1 le_rfl (by omega) (by norm_num),
              abs_zero]
            exact hε₁.le
          · rw [hl, neg_le_neg_iff]; exact hαle
          · rw [abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ (hunit hd'),
              abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ (hunit hd'),
              (hd _ hk).2 3 (by norm_num) hp (by norm_num), (hd _ hk).1, abs_zero, abs_neg,
              abs_of_pos hα]
            exact ⟨he₃.le, hαle⟩
    have hcrit : IsFirstHit (fun k => IsApproxThirdOrderMinimizer (ridge G e₀) (x k) ε₁ e₂ e₃)
        (arpSlowK p 2 e₂) := by
      simp only [hxk]
      refine isFirstHit_of_forall_le_iff fun k hk => ?_
      have hα := Chapter03.ar2SlowAlpha_pos he₂ hK hk
      rw [IsApproxThirdOrderMinimizer, Chapter03.IsApproxSecondOrderMinimizer,
        norm_gradient_ridge_e₀ (hG' hG).1, (hd k hk).2 1 le_rfl (by omega) (by norm_num),
        abs_zero, hessianMinEig_ridge_e₀ (hG' hG).2, (hd k hk).1, neg_le_neg_iff,
        ← Chapter03.ar2SlowAlpha_le_iff he₂ hK hk]
      refine ⟨fun h => h.1.2, fun h => ⟨⟨hε₁.le, h⟩, fun d hd' => ?_⟩⟩
      rw [abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ hd'.1,
        (hd k hk).2 3 (by norm_num) hp (by norm_num), abs_zero]
      exact he₃.le
    exact ⟨ridge G e₀, fun y => (hb y).trans' (by
        linarith [le_max_left B₂ B₃, le_max_right B₁ (max B₂ B₃)]),
      hDpL.mono ((le_max_left _ _).trans (le_max_right _ _)), x, s, σ, hx0', halg, hσ', hhit,
      hcrit⟩
  · -- the third-order example
    rw [show max (max A B) C = C by omega,
      show C = arpSlowK p 3 e₃ from (arpSlowK_three hp _).symm]
    obtain ⟨G, xr, hG, hb, hDpL, hx0, hd, hx, hv⟩ := H₃ e₃ he₃ he₃1
    have hK := arpSlowK_pos (p := p) (q := 3) he₃
    set K := arpSlowK p 3 e₃
    set α := Chapter03.ar2SlowAlpha e₃ K
    -- `e₀` is a direction of small model curvature at every iteration before `K`
    have hmem : ∀ k < K, e₀ ∈ arpCurvSet (ridge G e₀) p P (some e₂) (fun k => xr k • e₀)
        (fun k => (xr (k + 1) - xr k) • e₀) (fun _ => P.σ₀) k := by
      intro k hk
      cases k with
      | zero =>
        change e₀ ∈ smallCurvatureSet (ridge G e₀) (xr 0 • e₀) e₂
        rw [mem_smallCurvatureSet, abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ norm_e₀,
          (hd 0 hk.le).2 2 (by norm_num) (by omega) (by norm_num), abs_zero]
        exact ⟨norm_e₀, he₂.le⟩
      | succ j =>
        rw [arpCurvSet_succ, mem_smallCurvatureDirections]
        have hj : j < K := by omega
        have hdj : IsSpikeJetOf p G 3 ⟪e₀, xr j • e₀⟫ (α j) := by
          rw [inner_e₀_smul]; exact hd j hj.le
        have hαj : 0 < α j := Chapter03.ar2SlowAlpha_pos he₃ hK hj.le
        have ht : ⟪e₀, (xr (j + 1) - xr j) • e₀⟫ = monomialMinimizer p 3 P.σ₀ (α j) := by
          rw [inner_e₀_smul, hx j hj]; ring
        have htpos := monomialMinimizer_pos (p := p) (q := 3) hσ₀ hαj
        have hn : ‖(xr (j + 1) - xr j) • e₀‖ = monomialMinimizer p 3 P.σ₀ (α j) := by
          rw [norm_eq_abs_inner_e₀, ht, abs_of_pos htpos]
        refine ⟨norm_e₀, ?_⟩
        rw [iteratedFDeriv_regularizedModel_ridge_spike norm_eq_abs_inner_e₀ hG (by norm_num) hp hdj
          _ (by norm_num)
          (by omega), ht, hn, real_inner_self_eq_norm_sq, norm_e₀]
        obtain ⟨h0, h1⟩ := iteratedDeriv_two_negMonomialRegModel_mem hp hσ₀ hαj
        rw [one_pow, one_pow, mul_one, abs_of_nonneg h0]
        refine h1.trans ?_
        have hf1 : (0 : ℝ) < (p - 1)! := by positivity
        have hf : ((p - 2)! : ℝ) ≤ (p - 1)! := by
          exact_mod_cast Nat.factorial_le (by omega)
        have hσ2 : P.σ₀ ≤ (p - 1)! * P.θ₂ :=
          hσ.trans ((mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans
            (mul_le_mul_of_nonneg_right hf P.θ₂_pos.le))
        rw [div_le_iff₀ hf1]
        have : 0 ≤ monomialMinimizer p 3 P.σ₀ (α j) ^ (p - 1) := by positivity
        nlinarith
    obtain ⟨x, s, σ, hx0', halg, hσ', hhit, hxk⟩ :=
      exists_algorithm_4_1_1_ridge P (by omega) hord hε₁
      (by simpa using he₂) (by simpa using he₃) (by simp) (by norm_num) hp
      (fun h => hthird h 3 le_rfl) hG
      (fun k hk => Chapter03.ar2SlowAlpha_pos he₃ hK hk.le) (fun k hk => hd k hk.le) hx hv hx0
      fun k hk => by
        have hαk := Chapter03.ar2SlowAlpha_pos he₃ hK hk
        have hg : ‖gradient (ridge G e₀) (xr k • e₀)‖ = 0 := by
          rw [norm_gradient_ridge_e₀ (hG' hG).1, (hd k hk).2 1 le_rfl (by omega) (by norm_num),
            abs_zero]
        have hl : Chapter01.hessianMinEig (ridge G e₀) (xr k • e₀) = 0 := by
          rw [hessianMinEig_ridge_e₀ (hG' hG).2, (hd k hk).2 2 (by norm_num) (by omega)
            (by norm_num)]
        rcases hk.lt_or_eq with hlt | rfl
        · refine iff_of_false (not_arpStopTest_some_some.2 (Or.inr ⟨by rw [hl]; exact he₂.le,
            Or.inr ⟨e₀, hmem k hlt, Or.inl ?_⟩⟩)) (not_le.2 hlt)
          rw [abs_iteratedFDeriv_ridge_e₀ hG hp _ norm_e₀, (hd k hk).1, abs_neg, abs_of_pos hαk]
          exact not_le.1 fun h => (not_le.2 hlt) ((Chapter03.ar2SlowAlpha_le_iff he₃ hK hk).1 h)
        · refine iff_of_true (arpStopTest_some_some_of (by rw [hg]; exact hε₁.le)
            (by rw [hl]; linarith) fun d hd' => ?_) le_rfl
          rw [abs_iteratedFDeriv_ridge_e₀ hG hp _ (hunit hd'),
            abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ (hunit hd'), (hd _ hk).1,
            (hd _ hk).2 2 (by norm_num) (by omega) (by norm_num), abs_zero, abs_neg,
            abs_of_pos hαk]
          exact ⟨(Chapter03.ar2SlowAlpha_le_iff he₃ hK hk).2 le_rfl, he₂.le⟩
    have hcrit : IsFirstHit (fun k => IsApproxThirdOrderMinimizer (ridge G e₀) (x k) ε₁ e₂ e₃)
        K := by
      simp only [hxk]
      refine isFirstHit_of_forall_le_iff fun k hk => ?_
      have hαk := Chapter03.ar2SlowAlpha_pos he₃ hK hk
      have h3 : ∀ d : EuclideanSpace ℝ (Fin 1), ‖d‖ = 1 →
          |iteratedFDeriv ℝ 3 (ridge G e₀) (xr k • e₀) (fun _ => d)| = α k := fun d hd' => by
        rw [abs_iteratedFDeriv_ridge_e₀ hG hp _ hd', (hd k hk).1, abs_neg, abs_of_pos hαk]
      rw [IsApproxThirdOrderMinimizer, Chapter03.IsApproxSecondOrderMinimizer,
        norm_gradient_ridge_e₀ (hG' hG).1, (hd k hk).2 1 le_rfl (by omega) (by norm_num),
        abs_zero, hessianMinEig_ridge_e₀ (hG' hG).2,
        (hd k hk).2 2 (by norm_num) (by omega) (by norm_num),
        ← Chapter03.ar2SlowAlpha_le_iff he₃ hK hk]
      refine ⟨fun h => ?_, fun h => ⟨⟨hε₁.le, by linarith⟩, fun d hd' => (h3 d hd'.1).le.trans h⟩⟩
      have he₀ : e₀ ∈ smallCurvatureSet (ridge G e₀) (xr k • e₀) e₂ := by
        rw [mem_smallCurvatureSet, abs_iteratedFDeriv_ridge_e₀ hG (by omega) _ norm_e₀,
          (hd k hk).2 2 (by norm_num) (by omega) (by norm_num), abs_zero]
        exact ⟨norm_e₀, he₂.le⟩
      exact (h3 e₀ norm_e₀).symm.le.trans (h.2 e₀ he₀)
    exact ⟨ridge G e₀, fun y => (hb y).trans' (by
        linarith [le_max_right B₂ B₃, le_max_right B₁ (max B₂ B₃)]),
      hDpL.mono ((le_max_right _ _).trans (le_max_right _ _)), x, s, σ, hx0', halg, hσ', hhit,
      hcrit⟩


end Sharpness

end CartisGouldToint.Chapter04
