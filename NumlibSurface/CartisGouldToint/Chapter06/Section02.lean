import Numlib.Optimization.ModelBased.ConvexConstrained
import NumlibSurface.CartisGouldToint.Chapter02.Section04
import NumlibSurface.CartisGouldToint.Chapter06.Section01

/-!
# Cartis–Gould–Toint §6.2: The ARp-CC algorithm and its complexity

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §6.2: adaptive regularization with
`p`-th order models over a closed convex set `𝒞 ⊆ ℝⁿ` (ARp-CC, Algorithm 6.2.1), its evaluation
complexity for approximate first- to third-order minimizers (Lemmas 6.2.1–6.2.2, Theorem 6.2.3),
and the first-order variant ARp1-CC (Algorithm 6.2.2, Lemma 6.2.4, Theorem 6.2.5).

The model of iteration `k` is `m_k(s) = T_{f,p}(x_k, s) + σ_k/(p+1)! ‖s‖^{p+1}` (4.1.2),
`Optimization.regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)`. Runs are instances of the
generic adaptive-regularization run `Optimization.IsARRun` (Steps 3–4: acceptance of the trial
point and the update (2.4.4) of the regularization parameter), with the ratio
`Optimization.taylorRatio f p x s` of Step 3. The model counterparts (6.2.1)–(6.2.5) of the
feasible sets and criticality measures of §6.1 are `Optimization.restrictedSteps` and
`Optimization.formCriticality` of the derivative tensors of the model.

## Main definitions

* `AssumptionBbC f C flow`, `AssumptionDpLC f C p L` — f.bB.C and f.DpL.C.
* `ARpCCParams` — the constants (6.2.7); `ARpCCParams.sigmaMax P L` — `σ_max` of (4.1.19).
* `modelSteps₀`, `modelSteps₁`, `modelSteps₂` — `𝓜⁰_k(s)`, `𝓜¹_k(s)`, `𝓜²_k(s)` (6.2.1)–(6.2.2).
* `modelOmega1`, `modelOmega2`, `modelOmega3` — `ω_{m_k,𝓜,j}(s)` (6.2.3)–(6.2.5).
* `IsARpCCStep` — the Step-2 conditions (6.2.10)–(6.2.12).
* `algorithm_6_2_1` — Algorithm 6.2.1 (ARp-CC) as a run predicate.
* `omegaNext2`, `omegaNext3` — the mixed measures `ω_{k+1,2}` (6.2.14), `ω_{k+1,3}` (6.2.16).
* `kappaCC` — the constants `κ_j^cc` of Lemma 6.2.2; `tolMin`, `kappaSARpCC` — the quantities
  `min_j ε_j^{(p+1)/(p-j+1)}` and `κ^S_ARpCC` of Theorem 6.2.3.
* `algorithm_6_2_2` — Algorithm 6.2.2 (ARp1-CC) as a run predicate.

## Main results

* `exists_algorithm_6_2_1_of_forall_exists_step`, `exists_algorithm_6_2_1_one` — existence of
  ARp-CC runs when Step 2 is always feasible, in particular for `q = 1`;
  `algorithm_6_2_1_not_exists_step` — Step 2 may be infeasible for `q ≥ 2`.
* `arpcc_sigma_le`, `arpcc_sub_ge` — "Lemmas 4.1.1 and 4.1.2 continue to hold".
* `lemma_6_2_1_i` … `lemma_6_2_1_iv` — Lemma 6.2.1.
* `lemma_6_2_2` — Lemma 6.2.2 (corrected constants).
* `arpcc_decrease_of_not_test`, `theorem_6_2_3` — Theorem 6.2.3.
* `exists_algorithm_6_2_2`, `lemma_6_2_4`, `theorem_6_2_5` — §6.2.3.

## Deviations from the book

* The book indexes the order of the sought minimizer by which tolerances are infinite
  (`ε₂ = ε₃ = ∞` for first order, `ε₃ = ∞` for second order). Here the order is an explicit
  `q ∈ {1, 2, 3}` and all tolerances are finite positive reals; the tests and step conditions of
  order `> q` are switched off.
* (6.2.18)–(6.2.19) of Lemma 6.2.1 are stated for `‖d‖ ≤ 1` only: the proof's (6.2.23) holds on
  the unit ball `𝓑` (the error term scales like `‖d‖^j`). Accordingly, the inclusions
  `𝒞¹(x_{k+1}, ε₁) ⊆ 𝓜¹_k(s_k)` and `𝒞²(…) ⊆ 𝓜²_k(s_k)` in the proof of Theorem 6.2.3 are used
  on `𝓑`, which is all that the measures see.
* Lemma 6.2.2: the prefactor of `κ_j^cc` is `η₁ σ_min/(p+1)!`, not `η₁ σ_min/p!` as printed (the
  successful decrease is `η₁ σ_min ‖s‖^{p+1}/(p+1)!`, Lemma 4.1.1); Theorem 6.2.3's `κ^S` already
  uses `(p+1)!`.
* Third order needs `p ≥ 3` (and second order `p ≥ 2`); all results assume `q ≤ p`.
* Step 2 of ARp-CC can be infeasible for `q ≥ 2`, even at a strict global minimizer of `f` on `𝒞`
  (`algorithm_6_2_1_not_exists_step`): the second-order measure ranges over directions with
  `|∇f(x)[d]| ≤ τ₁ε₁`, including ascent directions, while Step 2 demands a model decrease. The
  book's remark that the model measures "will all be small in the neighbourhood of any …
  global minimizer of `m_k`" does not give a step with `m_k(s) < m_k(0)`. Theorem 6.2.3 holds for
  every run; runs exist for `q = 1`, and for `q ≥ 2` whenever Step 2 is always feasible.
* f.DpL.C asks for `f` to be `C^p` on an open set `𝒟 ⊇ 𝒞`; only `C^p` at the points of `𝒞` is
  used by the analysis.
-/

open Set Metric Optimization
open scoped Nat

namespace CartisGouldToint.Chapter06

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ### Assumptions and constants -/

/-- **Assumption f.bB.C** of [cartis2022evaluation], §6.2.2: `f` is bounded below on `𝒞` by
`flow`. -/
def AssumptionBbC (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (flow : ℝ) : Prop :=
  ∀ x ∈ C, flow ≤ f x

theorem assumptionBbC_iff {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {flow : ℝ} :
    AssumptionBbC f C flow ↔ ∀ x ∈ C, flow ≤ f x := Iff.rfl

/-- **Assumption f.DpL.C** of [cartis2022evaluation], §6.2.2: `f` is `p` times continuously
differentiable on an open set `𝒟 ⊇ 𝒞`, and its `p`-th derivative tensor is Lipschitz continuous
on `𝒞` with constant `L ≥ 0` (tensor norm = operator norm, (A.7)). -/
structure AssumptionDpLC (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (L : ℝ) : Prop where
  /-- `L_{f,p} ≥ 0`. -/
  nonneg : 0 ≤ L
  /-- `f` is `C^p` on an open set containing `𝒞`. -/
  contDiffOn : ∃ D, IsOpen D ∧ C ⊆ D ∧ ContDiffOn ℝ p f D
  /-- `∇^p f` is `L`-Lipschitz on `𝒞`. -/
  lipschitz : IteratedFDerivLipschitzOn f p L C

/-- Under f.DpL.C, `f` is `C^p` at every point of `𝒞`. -/
theorem AssumptionDpLC.contDiffAt {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p : ℕ} {L : ℝ}
    (h : AssumptionDpLC f C p L) : ∀ y ∈ C, ContDiffAt ℝ p f y := by
  obtain ⟨D, hD, hCD, hf⟩ := h.contDiffOn
  exact fun y hy => hf.contDiffAt (hD.mem_nhds (hCD hy))

/-- The constants (6.2.7) of ARp-CC ([cartis2022evaluation], Algorithm 6.2.1): those of
adaptive regularization (`σ₀ > 0`, `σ_min ∈ (0, σ₀]`, `0 < η₁ ≤ η₂ < 1`,
`0 < γ₁ < 1 < γ₂ < γ₃`), together with `θ₁, θ₂, θ₃ ∈ (0,1)`, `τ₁, τ₂ ∈ (0,1)`,
`(1 + τ₁)/2 ≤ θ₁` and `(1 + τ₂)/2 ≤ θ₂`. -/
structure ARpCCParams extends toChapter02ARParams : Chapter02.ARParams where
  /-- The first-order model tolerance factor. -/
  θ₁ : ℝ
  /-- The second-order model tolerance factor. -/
  θ₂ : ℝ
  /-- The third-order model tolerance factor. -/
  θ₃ : ℝ
  /-- The first-order restriction factor of (6.1.8). -/
  τ₁ : ℝ
  /-- The second-order restriction factor of (6.1.10). -/
  τ₂ : ℝ
  θ₁_pos : 0 < θ₁
  θ₁_lt_one : θ₁ < 1
  θ₂_pos : 0 < θ₂
  θ₂_lt_one : θ₂ < 1
  θ₃_pos : 0 < θ₃
  θ₃_lt_one : θ₃ < 1
  τ₁_pos : 0 < τ₁
  τ₁_lt_one : τ₁ < 1
  τ₂_pos : 0 < τ₂
  τ₂_lt_one : τ₂ < 1
  /-- `(1 + τ₁)/2 ≤ θ₁`. -/
  τ₁_le_θ₁ : (1 + τ₁) / 2 ≤ θ₁
  /-- `(1 + τ₂)/2 ≤ θ₂`. -/
  τ₂_le_θ₂ : (1 + τ₂) / 2 ≤ θ₂

namespace ARpCCParams

variable (P : ARpCCParams)

/-- The bound `σ_max = max(σ₀, γ₃ L/(1 - η₂))` of (4.1.19) on the regularization parameter. -/
noncomputable def sigmaMax (L : ℝ) : ℝ := arSigmaMax P.toARParams L

theorem sigmaMax_pos (L : ℝ) : 0 < P.sigmaMax L := arSigmaMax_pos _ L

/-- `1 - θ₁ + τ₁ ≤ θ₁` (from (6.2.7)). -/
theorem one_sub_θ₁_add_τ₁_le : 1 - P.θ₁ + P.τ₁ ≤ P.θ₁ := by linarith [P.τ₁_le_θ₁]

/-- `1 - θ₂ + τ₂ ≤ θ₂` (from (6.2.7)). -/
theorem one_sub_θ₂_add_τ₂_le : 1 - P.θ₂ + P.τ₂ ≤ P.θ₂ := by linarith [P.τ₂_le_θ₂]

end ARpCCParams

/-! ### Model measures and the algorithm -/

/-- `𝓜⁰_k(s) = 𝒞(x_k + s)` (6.2.1) of [cartis2022evaluation]. -/
def modelSteps₀ (C : Set ℝⁿ) (x s : ℝⁿ) : Set ℝⁿ := feasibleSteps C (x + s)

/-- `𝓜¹_k(s) = {d ∈ 𝓜⁰_k(s) | |∇_s m_k(s)[d]| ≤ θ₁ε₁}` (6.2.1) of [cartis2022evaluation], for
the model `m_k = regularizedModel (ftaylorSeries ℝ f x) p σ`. -/
def modelSteps₁ (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (θ₁ ε₁ : ℝ) (x : ℝⁿ) (σ : ℝ) (s : ℝⁿ) :
    Set ℝⁿ :=
  restrictedSteps (iteratedFDeriv ℝ 1 (regularizedModel (ftaylorSeries ℝ f x) p σ) s) (θ₁ * ε₁)
    (modelSteps₀ C x s)

/-- `𝓜²_k(s) = {d ∈ 𝓜¹_k(s) | |∇²_s m_k(s)[d]²| ≤ θ₂ε₂}` (6.2.2) of [cartis2022evaluation]. -/
def modelSteps₂ (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (θ₁ θ₂ ε₁ ε₂ : ℝ) (x : ℝⁿ) (σ : ℝ)
    (s : ℝⁿ) : Set ℝⁿ :=
  restrictedSteps (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) s) (θ₂ * ε₂)
    (modelSteps₁ f C p θ₁ ε₁ x σ s)

/-- The first-order model measure `ω_{m_k,𝓜,1}(s) = -min_{d ∈ 𝓜⁰_k(s) ∩ 𝓑} ∇_s m_k(s)[d]`
(6.2.3) of [cartis2022evaluation]. -/
noncomputable def modelOmega1 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (x : ℝⁿ) (σ : ℝ) (s : ℝⁿ) :
    ℝ :=
  formCriticality (iteratedFDeriv ℝ 1 (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
    (modelSteps₀ C x s)

/-- The second-order model measure `ω_{m_k,𝓜,2}(s) = -min_{d ∈ 𝓜¹_k(s) ∩ 𝓑} ∇²_s m_k(s)[d]²`
(6.2.4) of [cartis2022evaluation]. -/
noncomputable def modelOmega2 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (θ₁ ε₁ : ℝ) (x : ℝⁿ) (σ : ℝ)
    (s : ℝⁿ) : ℝ :=
  formCriticality (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
    (modelSteps₁ f C p θ₁ ε₁ x σ s)

/-- The third-order model measure `ω_{m_k,𝓜,3}(s) = -min_{d ∈ 𝓜²_k(s) ∩ 𝓑} ∇³_s m_k(s)[d]³`
(6.2.5) of [cartis2022evaluation]. -/
noncomputable def modelOmega3 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (θ₁ θ₂ ε₁ ε₂ : ℝ) (x : ℝⁿ)
    (σ : ℝ) (s : ℝⁿ) : ℝ :=
  formCriticality (iteratedFDeriv ℝ 3 (regularizedModel (ftaylorSeries ℝ f x) p σ) s)
    (modelSteps₂ f C p θ₁ θ₂ ε₁ ε₂ x σ s)

/-- **Step 2 of ARp-CC** ([cartis2022evaluation], Algorithm 6.2.1) at `x` with weight `σ`, for
the `q`-th order version (`q ∈ {1, 2, 3}`): the trial point is feasible, the model decreases,
and the model measures of order `≤ q` are small, (6.2.10)–(6.2.12). -/
structure IsARpCCStep (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (P : ARpCCParams) (q : ℕ)
    (ε₁ ε₂ ε₃ : ℝ) (x : ℝⁿ) (σ : ℝ) (s : ℝⁿ) : Prop where
  /-- `s ∈ 𝒞(x)`. -/
  mem : x + s ∈ C
  /-- `m(s) < m(0)`. -/
  decrease : regularizedModel (ftaylorSeries ℝ f x) p σ s <
    regularizedModel (ftaylorSeries ℝ f x) p σ 0
  /-- (6.2.10). -/
  omega1_le : modelOmega1 f C p x σ s ≤ P.θ₁ * ε₁
  /-- (6.2.11), for `q ≥ 2`. -/
  omega2_le : 2 ≤ q → modelOmega2 f C p P.θ₁ ε₁ x σ s ≤ P.θ₂ * ε₂
  /-- (6.2.12), for `q = 3`. -/
  omega3_le : 3 ≤ q → modelOmega3 f C p P.θ₁ P.θ₂ ε₁ ε₂ x σ s ≤ P.θ₃ * ε₃

/-- **Algorithm 6.2.1** (ARp-CC) of [cartis2022evaluation], seeking a `q`-th order approximate
minimizer (`q ∈ {1, 2, 3}`), as a run predicate on iterates `x`, trial steps `s` and
regularization parameters `σ`: tolerances `ε₁, ε₂, ε₃ > 0`, `x₀ ∈ 𝒞`, and the generic
adaptive-regularization run with the Step-1 test "`x_k` is a `q`-th order approximate minimizer
within `𝒞`" (`IsApproxMinimizerCC`), the Step-2 conditions `IsARpCCStep`, and the ratio of
Step 3 (`taylorRatio f p`). -/
structure algorithm_6_2_1 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (P : ARpCCParams) (q : ℕ)
    (ε₁ ε₂ ε₃ : ℝ) (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) : Prop where
  ε₁_pos : 0 < ε₁
  ε₂_pos : 0 < ε₂
  ε₃_pos : 0 < ε₃
  one_le_q : 1 ≤ q
  q_le_three : q ≤ 3
  /-- `x₀ ∈ 𝒞`. -/
  mem_zero : x 0 ∈ C
  /-- Steps 1–4. -/
  run : IsARRun P.toARParams (fun k => IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x k))
    (fun k => IsARpCCStep f C p P q ε₁ ε₂ ε₃ (x k) (σ k) (s k)) (fun _ => False)
    (taylorRatio f p x s) x s σ

/-- **Algorithm 6.2.2** (ARp1-CC) of [cartis2022evaluation]: ARp-CC for a first-order
approximate minimizer (`ε₂ = ε₃ = ∞`), with the step condition (6.2.10) replaced by (6.2.29),
`ω_{m_k,𝓜,1}(s_k) ≤ θ₁ ‖s_k‖^p` (`Optimization.IsFirstOrderCCStep`). -/
structure algorithm_6_2_2 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (P : ARpCCParams) (ε₁ : ℝ)
    (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) : Prop where
  ε₁_pos : 0 < ε₁
  /-- `x₀ ∈ 𝒞`. -/
  mem_zero : x 0 ∈ C
  /-- Steps 1–4. -/
  run : IsARRun P.toARParams (fun k => omega1 f C (x k) ≤ ε₁)
    (fun k => IsFirstOrderCCStep f C p P.θ₁ (x k) (σ k) (s k)) (fun _ => False)
    (taylorRatio f p x s) x s σ

/-- The mixed measure `ω_{k+1,2} = -min_{d ∈ 𝓜¹_k(s_k) ∩ 𝓑} ∇²f(x_k + s_k)[d]²` (6.2.14) of
[cartis2022evaluation] (objective tensor, model admissible set). -/
noncomputable def omegaNext2 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (θ₁ ε₁ : ℝ) (x : ℝⁿ) (σ : ℝ)
    (s : ℝⁿ) : ℝ :=
  formCriticality (iteratedFDeriv ℝ 2 f (x + s)) (modelSteps₁ f C p θ₁ ε₁ x σ s)

/-- The mixed measure `ω_{k+1,3} = -min_{d ∈ 𝓜²_k(s_k) ∩ 𝓑} ∇³f(x_k + s_k)[d]³` (6.2.16) of
[cartis2022evaluation]. -/
noncomputable def omegaNext3 (f : ℝⁿ → ℝ) (C : Set ℝⁿ) (p : ℕ) (θ₁ θ₂ ε₁ ε₂ : ℝ) (x : ℝⁿ)
    (σ : ℝ) (s : ℝⁿ) : ℝ :=
  formCriticality (iteratedFDeriv ℝ 3 f (x + s)) (modelSteps₂ f C p θ₁ θ₂ ε₁ ε₂ x σ s)

section Membership

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p : ℕ} {θ₁ θ₂ ε₁ ε₂ σ : ℝ} {x s d : ℝⁿ}

theorem mem_modelSteps₀ : d ∈ modelSteps₀ C x s ↔ x + s + d ∈ C := Iff.rfl

theorem mem_modelSteps₁ :
    d ∈ modelSteps₁ f C p θ₁ ε₁ x σ s ↔ d ∈ modelSteps₀ C x s ∧
      |iteratedFDeriv ℝ 1 (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
        θ₁ * ε₁ := Iff.rfl

theorem mem_modelSteps₂ :
    d ∈ modelSteps₂ f C p θ₁ θ₂ ε₁ ε₂ x σ s ↔ d ∈ modelSteps₁ f C p θ₁ ε₁ x σ s ∧
      |iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
        θ₂ * ε₂ := Iff.rfl

theorem zero_mem_modelSteps₀ (h : x + s ∈ C) : 0 ∈ modelSteps₀ C x s := by
  simpa [mem_modelSteps₀] using h

theorem zero_mem_modelSteps₁ (h : x + s ∈ C) (hε : 0 ≤ θ₁ * ε₁) :
    0 ∈ modelSteps₁ f C p θ₁ ε₁ x σ s :=
  (zero_mem_restrictedSteps le_rfl hε).2 (zero_mem_modelSteps₀ h)

theorem zero_mem_modelSteps₂ (h : x + s ∈ C) (hε₁ : 0 ≤ θ₁ * ε₁) (hε₂ : 0 ≤ θ₂ * ε₂) :
    0 ∈ modelSteps₂ f C p θ₁ θ₂ ε₁ ε₂ x σ s :=
  (zero_mem_restrictedSteps one_le_two hε₂).2 (zero_mem_modelSteps₁ h hε₁)

/-- `𝓜⁰_k(s_k) = 𝒞(x_{k+1})`, so `ω_{m,𝓜,1}` and `ω_{f,𝒞,1}(x + s)` range over the same set. -/
theorem modelSteps₀_eq : modelSteps₀ C x s = feasibleSteps C (x + s) := rfl

end Membership

/-! ### Lemmas 4.1.1 and 4.1.2 for convexly constrained runs -/

section Generic

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p : ℕ} {L : ℝ} {P : ARpCCParams}
  {test step : ℕ → Prop} {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}

/-- **"Lemma 4.1.2 continues to hold"** ([cartis2022evaluation], §6.2.2) for ARp-CC, ARp1-CC
(and every adaptive-regularization run over `𝒞` whose steps keep the trial point feasible and
decrease the model): under C.CNe and f.DpL.C, up to (and including) the first termination
index, `x_k ∈ 𝒞` and `σ_min ≤ σ_k ≤ σ_max = max(σ₀, γ₃ L/(1 - η₂))`. -/
theorem arpcc_sigma_le
    (h : IsARRun P.toARParams test step (fun _ => False) (taylorRatio f p x s) x s σ)
    (hC : AssumptionCNe C) (hf : AssumptionDpLC f C p L) (hx0 : x 0 ∈ C)
    (hstep : ∀ k, step k → x k + s k ∈ C ∧
      regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) (s k) <
        regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) 0)
    (k : ℕ) (hk : ∀ j < k, ¬ test j) :
    x k ∈ C ∧ P.σmin ≤ σ k ∧ σ k ≤ P.sigmaMax L :=
  h.sigma_le hC.convex hf.contDiffAt hf.lipschitz hx0 (fun k _ hs => hstep k hs) k
    (IsARRun.forall_lt_not_stop_iff.2 hk)

/-- **"Lemma 4.1.1 continues to hold"** ([cartis2022evaluation], §6.2.2) together with the
decrease (4.1.37) on successful iterations: before termination,
`T_{f,p}(x_k, 0) - T_{f,p}(x_k, s_k) > σ_k/(p+1)! ‖s_k‖^{p+1}`, and if iteration `k` is
successful then `x_{k+1} = x_k + s_k` and `f(x_k) - f(x_{k+1}) ≥ η₁ σ_min/(p+1)! ‖s_k‖^{p+1}`. -/
theorem arpcc_sub_ge
    (h : IsARRun P.toARParams test step (fun _ => False) (taylorRatio f p x s) x s σ)
    (hstep : ∀ k, step k →
      regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) (s k) <
        regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k) 0)
    {k : ℕ} (hk : ∀ j ≤ k, ¬ test j) :
    σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) <
        (ftaylorSeries ℝ f (x k)).taylorDecrement p (s k) ∧
      (P.η₁ ≤ taylorRatio f p x s k → x (k + 1) = x k + s k ∧
        P.η₁ * P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤ f (x k) - f (x (k + 1))) := by
  have hk' := IsARRun.forall_le_not_stop_iff.2 hk
  have hm := hstep k (h.step_of_forall_le hk')
  refine ⟨lt_taylorDecrement_of_regularizedModel_lt hm, fun hs => ?_⟩
  obtain ⟨heq, hge⟩ := h.sub_ge_of_succ_taylor hk' hm hs
  refine ⟨heq, le_trans ?_ hge⟩
  have hσ := h.sigmaMin_le (K := k) (fun j hj => hk' j hj.le) k le_rfl
  have := P.η₁_pos
  rw [mul_div_assoc, mul_assoc]
  gcongr

end Generic

/-! ### One-iteration estimates -/

section Estimates

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p : ℕ} {L : ℝ}

/-- The core of (6.2.13), (6.2.15), (6.2.17): if the model measure of order `j ≤ p` over `T ∋ 0`
is at most `θ ε` while the objective's exceeds `ε`, then
`‖s‖^{p-j+1} > (p-j+1)! (1 - θ)/(L + σ_max) ε`. -/
private theorem pow_gt_of_lt_formCriticality (hf : AssumptionDpLC f C p L) (hC : Convex ℝ C)
    {x s : ℝⁿ} {σ σmax θ ε : ℝ} (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ)
    (hσmax : σ ≤ σmax) (hpos : 0 < L + σmax) {j : ℕ} (hj : j ≤ p) {T : Set ℝⁿ} (hT : 0 ∈ T)
    (hm : formCriticality (iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s) T ≤
      θ * ε)
    (hlt : ε < formCriticality (iteratedFDeriv ℝ j f (x + s)) T) :
    ((p - j + 1)! : ℝ) * (1 - θ) / (L + σmax) * ε < ‖s‖ ^ (p - j + 1) := by
  have h1 := formCriticality_le_regularizedModel hC hf.contDiffAt hf.lipschitz hf.nonneg hx hxs
    hσ hj hT
  set N := ((p - j + 1)! : ℝ)
  set t := ‖s‖ ^ (p - j + 1)
  have hN : 0 < N := by positivity
  have ht : 0 ≤ t := by positivity
  have h2 : (L + σ) / N * t ≤ (L + σmax) / N * t := by gcongr
  have key : (1 - θ) * ε < (L + σmax) / N * t := by linarith
  rw [div_mul_eq_mul_div, lt_div_iff₀ hN] at key
  rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
  linarith

/-- (6.2.23) on the unit ball, as a bound on the model tensor: for `j ≤ p` and `‖d‖ ≤ 1`,
`|∇^j m(s)[d]^j| ≤ (L + σ_max)/(p-j+1)! ‖s‖^{p-j+1} + |∇^j f(x+s)[d]^j|`. -/
private theorem abs_model_le (hf : AssumptionDpLC f C p L) (hC : Convex ℝ C) {x s : ℝⁿ}
    {σ σmax : ℝ} (hx : x ∈ C) (hxs : x + s ∈ C) (hσ : 0 ≤ σ) (hσmax : σ ≤ σmax) {j : ℕ}
    (hj : j ≤ p) {d : ℝⁿ} (hd : ‖d‖ ≤ 1) :
    |iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d)| ≤
      (L + σmax) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) +
        |iteratedFDeriv ℝ j f (x + s) (fun _ => d)| := by
  have h1 := abs_iteratedFDeriv_sub_regularizedModel_le_of_mem_closedBall hC hf.contDiffAt
    hf.lipschitz hf.nonneg hx hxs hσ hj (d := d) (by simpa using hd)
  have h2 : (L + σ) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) ≤
      (L + σmax) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by gcongr
  have h3 := abs_sub_abs_le_abs_sub
    (iteratedFDeriv ℝ j (regularizedModel (ftaylorSeries ℝ f x) p σ) s (fun _ => d))
    (iteratedFDeriv ℝ j f (x + s) (fun _ => d))
  rw [abs_sub_comm] at h3
  linarith

/-- `(t^m)^{(p+1)/m} = t^{p+1}` for `t ≥ 0`, `m ≠ 0`. -/
private theorem pow_rpow_div {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (hm : m ≠ 0) (p : ℕ) :
    (t ^ m) ^ (((p : ℝ) + 1) / m) = t ^ (p + 1) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [← Real.rpow_natCast t m, ← Real.rpow_mul ht, mul_div_cancel₀ _ hm', ← Real.rpow_natCast]
  push_cast; ring_nf

end Estimates

/-! ### Lemmas 6.2.1 and 6.2.2 -/

/-- The constant `κ_j^cc = η₁ σ_min/(p+1)! ((p-j+1)! (1 - θ)/(L + σ_max))^{(p+1)/(p-j+1)}` of
Lemma 6.2.2 of [cartis2022evaluation] (with the corrected prefactor `1/(p+1)!`), for `θ = θ_j`. -/
noncomputable def kappaCC (P : ARpCCParams) (L : ℝ) (p j : ℕ) (θ : ℝ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    (((p - j + 1)! : ℝ) * (1 - θ) / (L + P.sigmaMax L)) ^ (((p : ℝ) + 1) / ((p : ℝ) - j + 1))

namespace algorithm_6_2_1

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p q : ℕ} {L : ℝ} {P : ARpCCParams} {ε₁ ε₂ ε₃ : ℝ}
  {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}

/-- The Step-2 conditions of an ARp-CC run hold before termination. -/
theorem step (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j)) :
    IsARpCCStep f C p P q ε₁ ε₂ ε₃ (x k) (σ k) (s k) :=
  h.run.step_of_forall_le (IsARRun.forall_le_not_stop_iff.2 hk)

/-- "Lemma 4.1.2 continues to hold" for ARp-CC runs (`arpcc_sigma_le`). -/
theorem sigma_le (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) (k : ℕ)
    (hk : ∀ j < k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j)) :
    x k ∈ C ∧ P.σmin ≤ σ k ∧ σ k ≤ P.sigmaMax L :=
  arpcc_sigma_le h.run hC hf h.mem_zero (fun _ hs => ⟨hs.mem, hs.decrease⟩) k hk

/-- The facts used on a successful iteration before termination. -/
private theorem succ_facts (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    x k ∈ C ∧ x (k + 1) = x k + s k ∧ x k + s k ∈ C ∧ 0 ≤ σ k ∧ σ k ≤ P.sigmaMax L ∧
      P.η₁ * P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) ≤ f (x k) - f (x (k + 1)) := by
  obtain ⟨hx, hmin, hmax⟩ := h.sigma_le hC hf k fun j hj => hk j hj.le
  obtain ⟨-, hsucc⟩ := arpcc_sub_ge h.run (fun _ hs => hs.decrease) hk
  obtain ⟨heq, hdec⟩ := hsucc hs
  exact ⟨hx, heq, (h.step hk).mem, P.σmin_nonneg.trans hmin, hmax, hdec⟩

/-- **Lemma 6.2.1**, (6.2.13), of [cartis2022evaluation]: under C.CNe and f.DpL.C, on a
successful iteration `k` of ARp-CC (before termination, `p ≥ 1`), if
`ω_{f,𝒞,1}(x_{k+1}) > ε₁` then `‖s_k‖^p > p! (1 - θ₁)/(L + σ_max) ε₁`. -/
theorem _root_.CartisGouldToint.Chapter06.lemma_6_2_1_i
    (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) (hp : 1 ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k) (hω : ε₁ < omega1 f C (x (k + 1))) :
    (p ! : ℝ) * (1 - P.θ₁) / (L + P.sigmaMax L) * ε₁ < ‖s k‖ ^ p := by
  obtain ⟨hx, heq, hxs, hσ, hσmax, -⟩ := h.succ_facts hC hf hk hs
  have hpos : 0 < L + P.sigmaMax L := by linarith [hf.nonneg, P.sigmaMax_pos L]
  have := pow_gt_of_lt_formCriticality hf hC.convex hx hxs hσ hσmax hpos hp
    (zero_mem_modelSteps₀ hxs) (h.step hk).omega1_le (by rwa [heq] at hω)
  rwa [Nat.sub_add_cancel hp] at this

/-- **Lemma 6.2.1**, (6.2.15), of [cartis2022evaluation]: in the setting of `lemma_6_2_1_i`, for
`2 ≤ q ≤ p`, if `ω_{k+1,2} > ε₂` then `‖s_k‖^{p-1} > (p-1)! (1 - θ₂)/(L + σ_max) ε₂`. -/
theorem _root_.CartisGouldToint.Chapter06.lemma_6_2_1_ii
    (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) (hq : 2 ≤ q) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k)
    (hω : ε₂ < omegaNext2 f C p P.θ₁ ε₁ (x k) (σ k) (s k)) :
    ((p - 1)! : ℝ) * (1 - P.θ₂) / (L + P.sigmaMax L) * ε₂ < ‖s k‖ ^ (p - 1) := by
  obtain ⟨hx, -, hxs, hσ, hσmax, -⟩ := h.succ_facts hC hf hk hs
  have hpos : 0 < L + P.sigmaMax L := by linarith [hf.nonneg, P.sigmaMax_pos L]
  have := pow_gt_of_lt_formCriticality hf hC.convex hx hxs hσ hσmax hpos (j := 2) (by omega)
    (zero_mem_modelSteps₁ hxs (mul_nonneg P.θ₁_pos.le h.ε₁_pos.le)) ((h.step hk).omega2_le hq) hω
  have e : p - 2 + 1 = p - 1 := by omega
  rwa [e] at this

/-- **Lemma 6.2.1**, (6.2.17), of [cartis2022evaluation]: in the setting of `lemma_6_2_1_i`, for
`q = 3 ≤ p`, if `ω_{k+1,3} > ε₃` then `‖s_k‖^{p-2} > (p-2)! (1 - θ₃)/(L + σ_max) ε₃`. -/
theorem _root_.CartisGouldToint.Chapter06.lemma_6_2_1_iii
    (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) (hq : 3 ≤ q) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k)
    (hω : ε₃ < omegaNext3 f C p P.θ₁ P.θ₂ ε₁ ε₂ (x k) (σ k) (s k)) :
    ((p - 2)! : ℝ) * (1 - P.θ₃) / (L + P.sigmaMax L) * ε₃ < ‖s k‖ ^ (p - 2) := by
  obtain ⟨hx, -, hxs, hσ, hσmax, -⟩ := h.succ_facts hC hf hk hs
  have hpos : 0 < L + P.sigmaMax L := by linarith [hf.nonneg, P.sigmaMax_pos L]
  have := pow_gt_of_lt_formCriticality hf hC.convex hx hxs hσ hσmax hpos (j := 3) (by omega)
    (zero_mem_modelSteps₂ hxs (mul_nonneg P.θ₁_pos.le h.ε₁_pos.le)
      (mul_nonneg P.θ₂_pos.le h.ε₂_pos.le)) ((h.step hk).omega3_le hq) hω
  have e : p - 3 + 1 = p - 2 := by omega
  rwa [e] at this

/-- **Lemma 6.2.1**, (6.2.18)–(6.2.19), of [cartis2022evaluation], **on the unit ball**: on a
successful iteration `k` before termination, for `d ∈ 𝒞¹(x_{k+1}, ε₁)` with `‖d‖ ≤ 1`,
`|∇_s m_k(s_k)[d]| ≤ (L + σ_max)/p! ‖s_k‖^p + τ₁ε₁` (`p ≥ 1`), and for
`d ∈ 𝒞²(x_{k+1}, ε₁, ε₂)` with `‖d‖ ≤ 1`,
`|∇²_s m_k(s_k)[d]²| ≤ (L + σ_max)/(p-1)! ‖s_k‖^{p-1} + τ₂ε₂` (`p ≥ 2`). (The book states both
for all `d` in the restricted sets; its proof, through (6.2.23), covers only `‖d‖ ≤ 1`.) -/
theorem _root_.CartisGouldToint.Chapter06.lemma_6_2_1_iv
    (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    (1 ≤ p → ∀ d ∈ restrictedSteps₁ f C P.τ₁ ε₁ (x (k + 1)), ‖d‖ ≤ 1 →
      |iteratedFDeriv ℝ 1 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k)
          (fun _ => d)| ≤ (L + P.sigmaMax L) / (p ! : ℝ) * ‖s k‖ ^ p + P.τ₁ * ε₁) ∧
    (2 ≤ p → ∀ d ∈ restrictedSteps₂ f C P.τ₁ P.τ₂ ε₁ ε₂ (x (k + 1)), ‖d‖ ≤ 1 →
      |iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) (s k)
          (fun _ => d)| ≤
        (L + P.sigmaMax L) / ((p - 1)! : ℝ) * ‖s k‖ ^ (p - 1) + P.τ₂ * ε₂) := by
  obtain ⟨hx, heq, hxs, hσ, hσmax, -⟩ := h.succ_facts hC hf hk hs
  refine ⟨fun hp d hd hd1 => ?_, fun hp d hd hd1 => ?_⟩
  · have h1 := abs_model_le hf hC.convex hx hxs hσ hσmax hp hd1
    rw [Nat.sub_add_cancel hp] at h1
    rw [heq] at hd
    have := hd.2
    linarith
  · have h1 := abs_model_le hf hC.convex hx hxs hσ hσmax (j := 2) hp hd1
    have e : p - 2 + 1 = p - 1 := by omega
    rw [e] at h1
    rw [heq] at hd
    have := hd.2
    linarith

/-- On a successful iteration, `‖s_k‖^m > b ε` (`1 ≤ m ≤ p + 1`, `b, ε ≥ 0`) forces the decrease
`f(x_k) - f(x_{k+1}) > η₁ σ_min/(p+1)! b^{(p+1)/m} ε^{(p+1)/m}` (proof of Lemma 4.1.4). -/
private theorem decrease_gt (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ)
    (hC : AssumptionCNe C) (hf : AssumptionDpLC f C p L) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k) {m : ℕ} (hm : m ≠ 0) {b ε : ℝ} (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (hlt : b * ε < ‖s k‖ ^ m) :
    P.η₁ * P.σmin / ((p + 1)! : ℝ) * (b ^ (((p : ℝ) + 1) / m) * ε ^ (((p : ℝ) + 1) / m)) <
      f (x k) - f (x (k + 1)) := by
  obtain ⟨-, -, -, -, -, hdec⟩ := h.succ_facts hC hf hk hs
  have hc : 0 < P.η₁ * P.σmin / ((p + 1)! : ℝ) := by
    have := P.η₁_pos; have := P.σmin_pos; positivity
  have he : 0 < ((p : ℝ) + 1) / m := by
    have : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    positivity
  have h1 : (b * ε) ^ (((p : ℝ) + 1) / m) < ‖s k‖ ^ (p + 1) := by
    rw [← pow_rpow_div (norm_nonneg _) hm]
    exact Real.rpow_lt_rpow (mul_nonneg hb hε) hlt he
  rw [← Real.mul_rpow hb hε]
  calc _ < P.η₁ * P.σmin / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1) := mul_lt_mul_of_pos_left h1 hc
    _ ≤ _ := hdec

/-- Lemma 6.2.2 for one order `j ∈ [1 : p]`: a long step `‖s_k‖^{p-j+1} > (p-j+1)! (1-θ)/(L +
σ_max) ε` forces the decrease `f(x_k) - f(x_{k+1}) > κ_j^cc ε^{(p+1)/(p-j+1)}`. -/
private theorem decrease_gt_kappaCC (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ)
    (hC : AssumptionCNe C) (hf : AssumptionDpLC f C p L) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k) {j : ℕ} (hj : j ≤ p) {θ ε : ℝ} (hθ : θ < 1)
    (hε : 0 ≤ ε)
    (hlt : ((p - j + 1)! : ℝ) * (1 - θ) / (L + P.sigmaMax L) * ε < ‖s k‖ ^ (p - j + 1)) :
    kappaCC P L p j θ * ε ^ (((p : ℝ) + 1) / ((p : ℝ) - j + 1)) < f (x k) - f (x (k + 1)) := by
  have hpos : 0 < L + P.sigmaMax L := by linarith [hf.nonneg, P.sigmaMax_pos L]
  have hb : 0 ≤ ((p - j + 1)! : ℝ) * (1 - θ) / (L + P.sigmaMax L) := by
    have : 0 ≤ 1 - θ := by linarith
    positivity
  have := h.decrease_gt hC hf hk hs (by omega) hb hε hlt
  have hcast : (((p - j + 1 : ℕ)) : ℝ) = (p : ℝ) - j + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hj, Nat.cast_one]
  rw [hcast] at this
  rw [kappaCC, mul_assoc]
  exact this

/-- **Lemma 6.2.2** of [cartis2022evaluation], **with corrected constants**: under C.CNe and
f.DpL.C, on a successful iteration `k` of ARp-CC before termination, with
`κ_j^cc = η₁ σ_min/(p+1)! ((p-j+1)! (1-θ_j)/(L + σ_max))^{(p+1)/(p-j+1)}`:
if `ω_{f,𝒞,1}(x_{k+1}) > ε₁` then `f(x_k) - f(x_{k+1}) > κ_1^cc ε₁^{(p+1)/p}` (`p ≥ 1`);
if `2 ≤ q ≤ p` and `ω_{k+1,2} > ε₂` then `f(x_k) - f(x_{k+1}) > κ_2^cc ε₂^{(p+1)/(p-1)}`;
if `3 ≤ q ≤ p` and `ω_{k+1,3} > ε₃` then `f(x_k) - f(x_{k+1}) > κ_3^cc ε₃^{(p+1)/(p-2)}`.
(The book's prefactor `η₁ σ_min/p!` overstates the decrease by the factor `p + 1`.) -/
theorem _root_.CartisGouldToint.Chapter06.lemma_6_2_2
    (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k) :
    (ε₁ < omega1 f C (x (k + 1)) →
      kappaCC P L p 1 P.θ₁ * ε₁ ^ (((p : ℝ) + 1) / p) < f (x k) - f (x (k + 1))) ∧
    (2 ≤ q → ε₂ < omegaNext2 f C p P.θ₁ ε₁ (x k) (σ k) (s k) →
      kappaCC P L p 2 P.θ₂ * ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) <
        f (x k) - f (x (k + 1))) ∧
    (3 ≤ q → ε₃ < omegaNext3 f C p P.θ₁ P.θ₂ ε₁ ε₂ (x k) (σ k) (s k) →
      kappaCC P L p 3 P.θ₃ * ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)) <
        f (x k) - f (x (k + 1))) := by
  have hp : 1 ≤ p := h.one_le_q.trans hqp
  refine ⟨fun hω => ?_, fun hq hω => ?_, fun hq hω => ?_⟩
  · have h1 := lemma_6_2_1_i h hC hf hp hk hs hω
    have := h.decrease_gt_kappaCC hC hf hk hs hp P.θ₁_lt_one h.ε₁_pos.le
      (by rwa [Nat.sub_add_cancel hp])
    simpa using this
  · have h1 := lemma_6_2_1_ii h hC hf hq hqp hk hs hω
    have e : p - 2 + 1 = p - 1 := by omega
    have := h.decrease_gt_kappaCC hC hf hk hs (j := 2) (by omega) P.θ₂_lt_one h.ε₂_pos.le
      (by rwa [e])
    convert this using 3
    push_cast; ring
  · have h1 := lemma_6_2_1_iii h hC hf hq hqp hk hs hω
    have e : p - 3 + 1 = p - 2 := by omega
    have := h.decrease_gt_kappaCC hC hf hk hs (j := 3) (by omega) P.θ₃_lt_one h.ε₃_pos.le
      (by rwa [e])
    convert this using 3
    push_cast; ring

end algorithm_6_2_1

/-! ### Theorem 6.2.3 -/

/-- The `j`-th term `((L + σ_max)/((p-j+1)! (1 - θ)))^{(p+1)/(p-j+1)}` of the maximum in the
constant `κ^S_ARpCC` of Theorem 6.2.3 of [cartis2022evaluation] (for `θ = θ_j`). -/
noncomputable def ccFactor (P : ARpCCParams) (L : ℝ) (p j : ℕ) (θ : ℝ) : ℝ :=
  ((L + P.sigmaMax L) / (((p - j + 1)! : ℝ) * (1 - θ))) ^ (((p : ℝ) + 1) / ((p : ℝ) - j + 1))

/-- The maximum of `ccFactor` over the orders `j ∈ [1 : q]` (`q ∈ {1, 2, 3}`). -/
noncomputable def ccMax (P : ARpCCParams) (L : ℝ) (p q : ℕ) : ℝ :=
  if q ≤ 1 then ccFactor P L p 1 P.θ₁
  else if q = 2 then max (ccFactor P L p 1 P.θ₁) (ccFactor P L p 2 P.θ₂)
  else max (max (ccFactor P L p 1 P.θ₁) (ccFactor P L p 2 P.θ₂)) (ccFactor P L p 3 P.θ₃)

/-- The constant `κ^S_ARpCC = (p+1)!/(η₁ σ_min) max_{j ∈ [1:q]} ((L + σ_max)/((p-j+1)! (1 -
θ_j)))^{(p+1)/(p-j+1)}` of Theorem 6.2.3 of [cartis2022evaluation] (`= 1/min_j κ_j^cc`). -/
noncomputable def kappaSARpCC (P : ARpCCParams) (L : ℝ) (p q : ℕ) : ℝ :=
  ((p + 1)! : ℝ) / (P.η₁ * P.σmin) * ccMax P L p q

/-- The constant `κ^A_ARpCC = κ^S_ARpCC (1 + |log γ₁|/log γ₂)` of Theorem 6.2.3 of
[cartis2022evaluation]. -/
noncomputable def kappaAARpCC (P : ARpCCParams) (L : ℝ) (p q : ℕ) : ℝ :=
  kappaSARpCC P L p q * (1 + |Real.log P.γ₁| / Real.log P.γ₂)

/-- The constant `κ^C_ARpCC = (|log γ₁| + log(σ_max/σ₀))/log γ₂ + 2` of Theorem 6.2.3 of
[cartis2022evaluation] (also `κ^C_ARp` of Theorem 6.2.5, (4.1.46)). -/
noncomputable def kappaCARpCC (P : ARpCCParams) (L : ℝ) : ℝ :=
  (|Real.log P.γ₁| + Real.log (P.sigmaMax L / P.σ₀)) / Real.log P.γ₂ + 2

/-- The accuracy term `min_{j ∈ [1:q]} ε_j^{(p+1)/(p-j+1)}` of Theorem 6.2.3 of
[cartis2022evaluation]: `min[ε₁^{(p+1)/p}, ε₂^{(p+1)/(p-1)}, ε₃^{(p+1)/(p-2)}]` for `q = 3`,
its first two entries for `q = 2`, and `ε₁^{(p+1)/p}` for `q = 1`. -/
noncomputable def tolMin (p q : ℕ) (ε₁ ε₂ ε₃ : ℝ) : ℝ :=
  if q ≤ 1 then ε₁ ^ (((p : ℝ) + 1) / p)
  else if q = 2 then min (ε₁ ^ (((p : ℝ) + 1) / p)) (ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)))
  else min (min (ε₁ ^ (((p : ℝ) + 1) / p)) (ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))))
    (ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)))

section Constants

variable {P : ARpCCParams} {L : ℝ} {p q : ℕ} {ε₁ ε₂ ε₃ : ℝ}

theorem ccFactor_pos (hL : 0 ≤ L) {j : ℕ} {θ : ℝ} (hθ : θ < 1) : 0 < ccFactor P L p j θ := by
  have := P.sigmaMax_pos L
  have : 0 < 1 - θ := by linarith
  unfold ccFactor
  positivity

theorem ccMax_pos (hL : 0 ≤ L) : 0 < ccMax P L p q := by
  have h1 := ccFactor_pos (P := P) (p := p) (j := 1) hL P.θ₁_lt_one
  unfold ccMax
  split_ifs
  · exact h1
  · exact lt_max_of_lt_left h1
  · exact lt_max_of_lt_left (lt_max_of_lt_left h1)

theorem kappaSARpCC_pos (hL : 0 ≤ L) : 0 < kappaSARpCC P L p q := by
  have := P.η₁_pos; have := P.σmin_pos; have := ccMax_pos (P := P) (p := p) (q := q) hL
  unfold kappaSARpCC
  positivity

theorem tolMin_pos (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) : 0 < tolMin p q ε₁ ε₂ ε₃ := by
  unfold tolMin
  split_ifs <;> positivity

/-- `κ_j^cc = η₁ σ_min/(p+1)! / ccFactor_j`. -/
theorem kappaCC_eq (hL : 0 ≤ L) {j : ℕ} {θ : ℝ} (hθ : θ < 1) :
    kappaCC P L p j θ = P.η₁ * P.σmin / ((p + 1)! : ℝ) / ccFactor P L p j θ := by
  have := P.sigmaMax_pos L
  have : 0 < 1 - θ := by linarith
  rw [kappaCC, ccFactor, div_eq_mul_inv _ (_ ^ _), ← Real.inv_rpow (by positivity), inv_div]

/-- The bookkeeping of the proof of Theorem 6.2.3: if `ccFactor_j ≤ ccMax` and
`tolMin ≤ ε^e` then `tolMin/κ^S ≤ κ_j^cc ε^e`. -/
private theorem div_kappaS_le (hL : 0 ≤ L) {j : ℕ} {θ ε e : ℝ} (hθ : θ < 1) (hε : 0 ≤ ε)
    (hF : ccFactor P L p j θ ≤ ccMax P L p q) (ht : tolMin p q ε₁ ε₂ ε₃ ≤ ε ^ e) :
    tolMin p q ε₁ ε₂ ε₃ / kappaSARpCC P L p q ≤ kappaCC P L p j θ * ε ^ e := by
  have hFpos := ccFactor_pos (P := P) (p := p) (j := j) hL hθ
  have hc : 0 ≤ P.η₁ * P.σmin / ((p + 1)! : ℝ) := by
    have := P.η₁_pos; have := P.σmin_pos; positivity
  have hM := hFpos.trans_le hF
  have he : 0 ≤ ε ^ e := Real.rpow_nonneg hε e
  rw [kappaCC_eq hL hθ, kappaSARpCC]
  have h1 : tolMin p q ε₁ ε₂ ε₃ / (((p + 1)! : ℝ) / (P.η₁ * P.σmin) * ccMax P L p q) =
      tolMin p q ε₁ ε₂ ε₃ * (P.η₁ * P.σmin / ((p + 1)! : ℝ) / ccMax P L p q) := by
    have := P.η₁_pos; have := P.σmin_pos
    field_simp
  rw [h1, mul_comm _ (ε ^ e)]
  calc tolMin p q ε₁ ε₂ ε₃ * (P.η₁ * P.σmin / ((p + 1)! : ℝ) / ccMax P L p q)
      ≤ ε ^ e * (P.η₁ * P.σmin / ((p + 1)! : ℝ) / ccMax P L p q) :=
        mul_le_mul_of_nonneg_right ht (by positivity)
    _ ≤ ε ^ e * (P.η₁ * P.σmin / ((p + 1)! : ℝ) / ccFactor P L p j θ) := by gcongr

private theorem ccFactor_one_le : ccFactor P L p 1 P.θ₁ ≤ ccMax P L p q := by
  unfold ccMax; split_ifs
  · exact le_rfl
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_left _ _)

private theorem ccFactor_two_le (hq : 2 ≤ q) : ccFactor P L p 2 P.θ₂ ≤ ccMax P L p q := by
  unfold ccMax; split_ifs
  · omega
  · exact le_max_right _ _
  · exact (le_max_right _ _).trans (le_max_left _ _)

private theorem ccFactor_three_le (hq : 3 ≤ q) : ccFactor P L p 3 P.θ₃ ≤ ccMax P L p q := by
  unfold ccMax; split_ifs
  · omega
  · omega
  · exact le_max_right _ _

private theorem tolMin_le_one : tolMin p q ε₁ ε₂ ε₃ ≤ ε₁ ^ (((p : ℝ) + 1) / p) := by
  unfold tolMin; split_ifs
  · exact le_rfl
  · exact min_le_left _ _
  · exact (min_le_left _ _).trans (min_le_left _ _)

private theorem tolMin_le_two (hq : 2 ≤ q) :
    tolMin p q ε₁ ε₂ ε₃ ≤ ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) := by
  unfold tolMin; split_ifs
  · omega
  · exact min_le_right _ _
  · exact (min_le_left _ _).trans (min_le_right _ _)

private theorem tolMin_le_three (hq : 3 ≤ q) :
    tolMin p q ε₁ ε₂ ε₃ ≤ ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)) := by
  unfold tolMin; split_ifs
  · omega
  · omega
  · exact min_le_right _ _

end Constants

namespace algorithm_6_2_1

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p q : ℕ} {L flow : ℝ} {P : ARpCCParams} {ε₁ ε₂ ε₃ : ℝ}
  {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}

/-- `‖s‖^m ≤ N (1 - θ)/(L + σ_max) ε` and `σ ≤ σ_max` give `(L + σ)/N ‖s‖^m ≤ (1 - θ) ε`. -/
private theorem err_le {σ σmax N t θ ε : ℝ} (hσ : σ ≤ σmax) (hpos : 0 < L + σmax) (hN : 0 < N)
    (ht0 : 0 ≤ t) (ht : t ≤ N * (1 - θ) / (L + σmax) * ε) :
    (L + σ) / N * t ≤ (1 - θ) * ε := by
  calc (L + σ) / N * t ≤ (L + σmax) / N * t := by gcongr
    _ ≤ (L + σmax) / N * (N * (1 - θ) / (L + σmax) * ε) := by gcongr
    _ = (1 - θ) * ε := by field_simp

/-- **The decrease of the proof of Theorem 6.2.3** ([cartis2022evaluation], its version of
(4.1.44)): under C.CNe and f.DpL.C with `q ≤ p`, on a successful iteration `k` of ARp-CC before
termination such that `x_{k+1}` fails the termination test,
`f(x_k) - f(x_{k+1}) ≥ min_j κ_j^cc · min_j ε_j^{(p+1)/(p-j+1)} = tolMin/κ^S_ARpCC`. If the step
is long ((6.2.27) or, for `q ≥ 2`, (6.2.28) fails) this follows from Lemma 4.1.1; otherwise
`𝒞¹(x_{k+1}, ε₁) ∩ 𝓑 ⊆ 𝓜¹_k(s_k)` and `𝒞²(x_{k+1}, ε₁, ε₂) ∩ 𝓑 ⊆ 𝓜²_k(s_k)` (Lemma 6.2.1 and
(6.2.7)), so `ω_{f,𝒞,2}(x_{k+1}, ε₁) ≤ ω_{k+1,2}`, `ω_{f,𝒞,3}(x_{k+1}, ε₁, ε₂) ≤ ω_{k+1,3}`, and
Lemma 6.2.2 applies to the failing measure. -/
theorem _root_.CartisGouldToint.Chapter06.arpcc_decrease_of_not_test
    (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ)
    (hC : AssumptionCNe C) (hf : AssumptionDpLC f C p L) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x j))
    (hs : P.η₁ ≤ taylorRatio f p x s k)
    (hk1 : ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x (k + 1))) :
    tolMin p q ε₁ ε₂ ε₃ / kappaSARpCC P L p q ≤ f (x k) - f (x (k + 1)) := by
  have hp : 1 ≤ p := h.one_le_q.trans hqp
  have hL := hf.nonneg
  obtain ⟨hx, heq, hxs, hσ, hσmax, -⟩ := h.succ_facts hC hf hk hs
  have hpos : 0 < L + P.sigmaMax L := by linarith [P.sigmaMax_pos L]
  have hε₁ := h.ε₁_pos
  have hε₂ := h.ε₂_pos
  have hε₃ := h.ε₃_pos
  have hl := lemma_6_2_2 h hC hf hqp hk hs
  -- the three ways to conclude
  have fin1 : kappaCC P L p 1 P.θ₁ * ε₁ ^ (((p : ℝ) + 1) / p) < f (x k) - f (x (k + 1)) →
      tolMin p q ε₁ ε₂ ε₃ / kappaSARpCC P L p q ≤ f (x k) - f (x (k + 1)) := fun h' =>
    (div_kappaS_le hL P.θ₁_lt_one hε₁.le ccFactor_one_le tolMin_le_one).trans h'.le
  have fin2 : 2 ≤ q → kappaCC P L p 2 P.θ₂ * ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) <
      f (x k) - f (x (k + 1)) →
      tolMin p q ε₁ ε₂ ε₃ / kappaSARpCC P L p q ≤ f (x k) - f (x (k + 1)) := fun hq h' =>
    (div_kappaS_le hL P.θ₂_lt_one hε₂.le (ccFactor_two_le hq) (tolMin_le_two hq)).trans h'.le
  have fin3 : 3 ≤ q → kappaCC P L p 3 P.θ₃ * ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)) <
      f (x k) - f (x (k + 1)) →
      tolMin p q ε₁ ε₂ ε₃ / kappaSARpCC P L p q ≤ f (x k) - f (x (k + 1)) := fun hq h' =>
    (div_kappaS_le hL P.θ₃_lt_one hε₃.le (ccFactor_three_le hq) (tolMin_le_three hq)).trans h'.le
  have hx1 : x (k + 1) ∈ C := heq ▸ hxs
  rw [isApproxMinimizerCC_iff] at hk1
  -- first-order measure
  by_cases h1 : omega1 f C (x (k + 1)) ≤ ε₁
  swap
  · exact fin1 (hl.1 (lt_of_not_ge h1))
  -- long step with respect to (6.2.27)
  by_cases hl1 : ‖s k‖ ^ p ≤ (p ! : ℝ) * (1 - P.θ₁) / (L + P.sigmaMax L) * ε₁
  swap
  · have := h.decrease_gt_kappaCC hC hf hk hs hp P.θ₁_lt_one hε₁.le
      (by rw [Nat.sub_add_cancel hp]; exact lt_of_not_ge hl1)
    exact fin1 (by simpa using this)
  have hτ₁ : 0 ≤ P.τ₁ * ε₁ := mul_nonneg P.τ₁_pos.le hε₁.le
  have incl1 : closedBall 0 1 ∩ restrictedSteps₁ f C P.τ₁ ε₁ (x k + s k) ⊆
      modelSteps₁ f C p P.θ₁ ε₁ (x k) (σ k) (s k) := by
    refine inter_closedBall_restrictedSteps_subset_regularizedModel hC.convex hf.contDiffAt
      hf.lipschitz hL hx hxs hσ hp ?_
    rw [Nat.sub_add_cancel hp]
    have := err_le hσmax hpos (by positivity) (by positivity) hl1
    nlinarith [P.one_sub_θ₁_add_τ₁_le]
  have hne1 : (closedBall (0 : ℝⁿ) 1 ∩ restrictedSteps₁ f C P.τ₁ ε₁ (x k + s k)).Nonempty :=
    ⟨0, zero_mem_closedBall_inter (zero_mem_restrictedSteps₁ hxs hτ₁)⟩
  -- second-order measure
  by_cases h2 : 2 ≤ q → omega2 f C P.τ₁ (x (k + 1)) ε₁ ≤ ε₂
  swap
  · simp only [Classical.not_imp, not_le] at h2
    obtain ⟨hq, h2⟩ := h2
    refine fin2 hq (hl.2.1 hq (h2.trans_le ?_))
    rw [heq]
    exact formCriticality_mono _ hne1 incl1
  have hq3 : 3 ≤ q ∧ ε₃ < omega3 f C P.τ₁ P.τ₂ (x (k + 1)) ε₁ ε₂ := by
    by_contra hcon
    exact hk1 ⟨hx1, h1, h2, fun hq => le_of_not_gt fun h' => hcon ⟨hq, h'⟩⟩
  obtain ⟨hq, h3⟩ := hq3
  -- long step with respect to (6.2.28)
  by_cases hl2 : ‖s k‖ ^ (p - 1) ≤ ((p - 1)! : ℝ) * (1 - P.θ₂) / (L + P.sigmaMax L) * ε₂
  swap
  · have e : p - 2 + 1 = p - 1 := by omega
    have := h.decrease_gt_kappaCC hC hf hk hs (j := 2) (by omega) P.θ₂_lt_one hε₂.le
      (by rw [e]; exact lt_of_not_ge hl2)
    refine fin2 (by omega) (lt_of_eq_of_lt ?_ this)
    congr 2; push_cast; ring
  have hτ₂ : 0 ≤ P.τ₂ * ε₂ := mul_nonneg P.τ₂_pos.le hε₂.le
  have incl2 : closedBall 0 1 ∩ restrictedSteps₂ f C P.τ₁ P.τ₂ ε₁ ε₂ (x k + s k) ⊆
      modelSteps₂ f C p P.θ₁ P.θ₂ ε₁ ε₂ (x k) (σ k) (s k) := by
    rintro d ⟨hdB, hd⟩
    have hd1 : d ∈ modelSteps₁ f C p P.θ₁ ε₁ (x k) (σ k) (s k) := incl1 ⟨hdB, hd.1⟩
    refine inter_closedBall_restrictedSteps_subset_regularizedModel (j := 2)
      (T := modelSteps₁ f C p P.θ₁ ε₁ (x k) (σ k) (s k)) hC.convex hf.contDiffAt
      hf.lipschitz hL hx hxs hσ (by omega) ?_ ⟨hdB, hd1, hd.2⟩
    have e : p - 2 + 1 = p - 1 := by omega
    rw [e]
    have := err_le hσmax hpos (by positivity) (by positivity) hl2
    nlinarith [P.one_sub_θ₂_add_τ₂_le]
  have hne2 : (closedBall (0 : ℝⁿ) 1 ∩
      restrictedSteps₂ f C P.τ₁ P.τ₂ ε₁ ε₂ (x k + s k)).Nonempty :=
    ⟨0, zero_mem_closedBall_inter (zero_mem_restrictedSteps₂ hxs hτ₁ hτ₂)⟩
  refine fin3 hq (hl.2.2 hq (h3.trans_le ?_))
  rw [heq]
  exact formCriticality_mono _ hne2 incl2

end algorithm_6_2_1

namespace algorithm_6_2_1

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p q : ℕ} {L flow : ℝ} {P : ARpCCParams} {ε₁ ε₂ ε₃ : ℝ}
  {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ}

/-- **Theorem 6.2.3** of [cartis2022evaluation]. Under C.CNe, f.DpL.C and f.bB.C, with
`1 ≤ q ≤ p`, every ARp-CC run terminates: there is a first iteration `k_ε` at which `x_{k_ε}` is a
`q`-th order approximate minimizer within `𝒞`, and, with
`m_ε = min_{j ∈ [1:q]} ε_j^{(p+1)/(p-j+1)}` (`tolMin`), the number of evaluations of `f` is at
most `κ^A_ARpCC (f(x₀) - f_low)/m_ε + κ^C_ARpCC` and that of derivatives at most
`κ^S_ARpCC (f(x₀) - f_low)/m_ε + 2` (the book's constants; `σ_max` of (4.1.19)). Hence
`O(max_j ε_j^{-(p+1)/(p-j+1)})` evaluations. (The book states the case `q = 3`, with `q = 1, 2`
covered by infinite tolerances; the restriction `ε_j ≤ 1` is not needed.) -/
theorem _root_.CartisGouldToint.Chapter06.theorem_6_2_3
    (hC : AssumptionCNe C) (hf : AssumptionDpLC f C p L)
    (hb : AssumptionBbC f C flow) (hqp : q ≤ p) (h : algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ) :
    ∃ kε, IsFirstHit (fun k => IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤
        kappaAARpCC P L p q * (f (x 0) - flow) / tolMin p q ε₁ ε₂ ε₃ + kappaCARpCC P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f p x s k) kε : ℝ) ≤
        kappaSARpCC P L p q * (f (x 0) - flow) / tolMin p q ε₁ ε₂ ε₃ + 2 := by
  have hS := kappaSARpCC_pos (P := P) (p := p) (q := q) hf.nonneg
  have ht := tolMin_pos (p := p) (q := q) h.ε₁_pos h.ε₂_pos h.ε₃_pos
  obtain ⟨kε, hk, hF, hD⟩ := h.run.exists_isFirstHit_of_decrease (σmax := P.sigmaMax L)
    (V := fun k => f (x k)) (Vlow := flow) (δ := tolMin p q ε₁ ε₂ ε₃ / kappaSARpCC P L p q)
    (fun k hk => (h.sigma_le hC hf k (IsARRun.forall_lt_not_stop_iff.1 hk)).2.2) (div_pos ht hS)
    (fun k hk => (h.run.accept k hk).le (w := f) rfl
      (lt_of_le_of_lt (by
          have := P.σmin_nonneg.trans
            (h.sigma_le hC hf k fun j hj => IsARRun.forall_le_not_stop_iff.1 hk j hj.le).2.1
          positivity)
        (arpcc_sub_ge h.run (fun _ hs => hs.decrease) (IsARRun.forall_le_not_stop_iff.1 hk)).1))
    (fun k hk => hb _ (h.sigma_le hC hf k (IsARRun.forall_lt_not_stop_iff.1 hk)).1)
    (fun k hk hs => by
      have hk' := IsARRun.forall_le_not_stop_iff.1 hk
      exact arpcc_decrease_of_not_test h hC hf hqp (fun j hj => hk' j (hj.trans k.le_succ)) hs
        (hk' (k + 1) le_rfl))
  have hN : (f (x 0) - flow) / (tolMin p q ε₁ ε₂ ε₃ / kappaSARpCC P L p q) =
      kappaSARpCC P L p q * (f (x 0) - flow) / tolMin p q ε₁ ε₂ ε₃ := by
    field_simp
  rw [hN] at hF hD
  refine ⟨kε, ⟨hk.1.resolve_right id, fun j hj h' => hk.2 j hj (Or.inl h')⟩, ?_, hD⟩
  refine hF.trans_eq ?_
  rw [kappaAARpCC, kappaCARpCC, kappaSARpCC]
  ring

end algorithm_6_2_1

/-! ### Existence of ARp-CC runs -/

section Existence

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p q : ℕ} {P : ARpCCParams} {ε₁ ε₂ ε₃ : ℝ}

/-- **Existence of ARp-CC runs** ([cartis2022evaluation], Algorithm 6.2.1) when Step 2 is always
feasible: if at every feasible `y` that fails the termination test and for every
`σ ≥ σ_min` some step `s` satisfies the Step-2 conditions, then a run starts from every
`x₀ ∈ 𝒞`. (The proviso can fail for `q ≥ 2`: `algorithm_6_2_1_not_exists_step`.) -/
theorem exists_algorithm_6_2_1_of_forall_exists_step (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃)
    (hq : 1 ≤ q) (hq3 : q ≤ 3)
    (hstep : ∀ y ∈ C, ∀ σ, P.σmin ≤ σ → ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ y →
      ∃ s, IsARpCCStep f C p P q ε₁ ε₂ ε₃ y σ s)
    {x₀ : ℝⁿ} (hx₀ : x₀ ∈ C) :
    ∃ x s σ, x 0 = x₀ ∧ algorithm_6_2_1 f C p P q ε₁ ε₂ ε₃ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.toARParams (Inv := (· ∈ C))
    (test := IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃)
    (stepOK := IsARpCCStep f C p P q ε₁ ε₂ ε₃)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement p t))
    (fun y σ hy hσ _ ht => by
      obtain ⟨s, hs⟩ := hstep y hy σ hσ ht
      exact ⟨s, hs, hs.mem⟩) hx₀
  exact ⟨x, s, σ, hx0, h₁, h₂, h₃, hq, hq3, hx0 ▸ hx₀, hrun⟩

/-- **Existence of first-order ARp-CC runs** ([cartis2022evaluation], Algorithm 6.2.1 with
`ε₂ = ε₃ = ∞`): under C.CNe, with `f` `C^p` at the points of `𝒞` (`p ≥ 1`), a run of the
first-order version starts from every `x₀ ∈ 𝒞` (a global minimizer of the model over `𝒞(x_k)`
satisfies (6.2.10) with model measure `0`, `Optimization.exists_isFirstOrderCCStep`). -/
theorem exists_algorithm_6_2_1_one (hC : AssumptionCNe C) (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hp : 1 ≤ p) (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) (h₃ : 0 < ε₃) {x₀ : ℝⁿ} (hx₀ : x₀ ∈ C) :
    ∃ x s σ, x 0 = x₀ ∧ algorithm_6_2_1 f C p P 1 ε₁ ε₂ ε₃ x s σ := by
  refine exists_algorithm_6_2_1_of_forall_exists_step h₁ h₂ h₃ le_rfl (by norm_num)
    (fun y hy σ hσ ht => ?_) hx₀
  have hω : ε₁ < omega1 f C y := by
    by_contra h'
    exact ht ⟨hy, le_of_not_gt h', fun h => absurd h (by norm_num),
      fun h => absurd h (by norm_num)⟩
  obtain ⟨s, -, hs, hzero⟩ := exists_isFirstOrderCCStep (θ := P.θ₁) hC.isClosed hC.convex hy
    (hf y hy) hp (P.σmin_pos.trans_le hσ) P.θ₁_pos.le (h₁.trans hω)
  refine ⟨s, hs.mem, hs.decrease, ?_, fun h => absurd h (by norm_num),
    fun h => absurd h (by norm_num)⟩
  rw [modelOmega1, modelSteps₀_eq, hzero]
  exact mul_nonneg P.θ₁_pos.le h₁.le

end Existence

/-! ### ARp1-CC: Lemma 6.2.4 and Theorem 6.2.5 -/

/-- The constant `κ₁ = η₁ σ_min/(p+1)! (p!/(L + σ_max + θ₁ p!))^{(p+1)/p}` of (4.1.32), used by
Lemma 6.2.4 of [cartis2022evaluation]. -/
noncomputable def kappa1CC (P : ARpCCParams) (L : ℝ) (p : ℕ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    ((p ! : ℝ) / (L + P.sigmaMax L + P.θ₁ * p !)) ^ (((p : ℝ) + 1) / p)

/-- The constant `κ^S_ARp1CC = (p+1)!/(η₁ σ_min) ((L + σ_max + θ₁ p!)/p!)^{(p+1)/p}` of
Theorem 6.2.5 of [cartis2022evaluation] (`= 1/κ₁`). -/
noncomputable def kappaSARp1CC (P : ARpCCParams) (L : ℝ) (p : ℕ) : ℝ :=
  ((p + 1)! : ℝ) / (P.η₁ * P.σmin) *
    ((L + P.sigmaMax L + P.θ₁ * p !) / (p ! : ℝ)) ^ (((p : ℝ) + 1) / p)

/-- The constant `κ^A_ARp1CC = κ^S_ARp1CC (1 + |log γ₁|/log γ₂)` of Theorem 6.2.5 of
[cartis2022evaluation]. -/
noncomputable def kappaAARp1CC (P : ARpCCParams) (L : ℝ) (p : ℕ) : ℝ :=
  kappaSARp1CC P L p * (1 + |Real.log P.γ₁| / Real.log P.γ₂)

theorem kappa1CC_mul_kappaSARp1CC {P : ARpCCParams} {L : ℝ} (hL : 0 ≤ L) (p : ℕ) :
    kappa1CC P L p * kappaSARp1CC P L p = 1 := by
  have := P.η₁_pos; have := P.σmin_pos; have := P.sigmaMax_pos L; have := P.θ₁_pos
  have hK : 0 < L + P.sigmaMax L + P.θ₁ * p ! := by positivity
  rw [kappa1CC, kappaSARp1CC, ← inv_div (L + P.sigmaMax L + P.θ₁ * p !),
    Real.inv_rpow (by positivity)]
  have : 0 < ((L + P.sigmaMax L + P.θ₁ * p !) / (p ! : ℝ)) ^ (((p : ℝ) + 1) / p) := by
    positivity
  field_simp

section ARp1CC

variable {f : ℝⁿ → ℝ} {C : Set ℝⁿ} {p : ℕ} {P : ARpCCParams} {ε₁ : ℝ}

/-- **Existence of ARp1-CC runs** ([cartis2022evaluation], Algorithm 6.2.2): under C.CNe, with
`f` `C^p` at the points of `𝒞` (`p ≥ 1`), a run starts from every `x₀ ∈ 𝒞` (a global minimizer
of the model over `𝒞(x_k)` satisfies (6.2.29), `Optimization.exists_isFirstOrderCCStep`). -/
theorem exists_algorithm_6_2_2 (hC : AssumptionCNe C) (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hp : 1 ≤ p) (h₁ : 0 < ε₁) {x₀ : ℝⁿ} (hx₀ : x₀ ∈ C) :
    ∃ x s σ, x 0 = x₀ ∧ algorithm_6_2_2 f C p P ε₁ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun, -⟩ := exists_isARRun P.toARParams (Inv := (· ∈ C))
    (test := fun y => omega1 f C y ≤ ε₁) (stepOK := IsFirstOrderCCStep f C p P.θ₁)
    (fun y _ t => reductionRatio f y t ((ftaylorSeries ℝ f y).taylorDecrement p t))
    (fun y σ hy _ hσ ht => by
      obtain ⟨s, -, hs, -⟩ := exists_isFirstOrderCCStep (θ := P.θ₁) hC.isClosed hC.convex hy
        (hf y hy) hp hσ P.θ₁_pos.le (h₁.trans (lt_of_not_ge ht))
      exact ⟨s, hs, hs.mem⟩) hx₀
  exact ⟨x, s, σ, hx0, h₁, hx0 ▸ hx₀, hrun⟩

namespace algorithm_6_2_2

variable {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {L flow : ℝ}

/-- "Lemma 4.1.2 continues to hold" for ARp1-CC runs (`arpcc_sigma_le`). -/
theorem sigma_le (h : algorithm_6_2_2 f C p P ε₁ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) (k : ℕ) (hk : ∀ j < k, ¬ omega1 f C (x j) ≤ ε₁) :
    x k ∈ C ∧ P.σmin ≤ σ k ∧ σ k ≤ P.sigmaMax L :=
  arpcc_sigma_le h.run hC hf h.mem_zero (fun _ hs => ⟨hs.mem, hs.decrease⟩) k hk

/-- **Lemma 6.2.4** of [cartis2022evaluation]: under C.CNe and f.DpL.C (`p ≥ 1`), on a
successful iteration `k` of ARp1-CC before termination,
`f(x_k) - f(x_{k+1}) ≥ κ₁ ω_{f,𝒞,1}(x_{k+1})^{(p+1)/p}` with `κ₁` of (4.1.32). -/
theorem _root_.CartisGouldToint.Chapter06.lemma_6_2_4
    (h : algorithm_6_2_2 f C p P ε₁ x s σ) (hC : AssumptionCNe C)
    (hf : AssumptionDpLC f C p L) (hp : 1 ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ omega1 f C (x j) ≤ ε₁) (hs : P.η₁ ≤ taylorRatio f p x s k) :
    kappa1CC P L p * omega1 f C (x (k + 1)) ^ (((p : ℝ) + 1) / p) ≤ f (x k) - f (x (k + 1)) := by
  have hk' := IsARRun.forall_le_not_stop_iff.2 hk
  obtain ⟨hx, hmin, hmax⟩ := h.sigma_le hC hf k fun j hj => hk j hj.le
  have hstep : IsFirstOrderCCStep f C p P.θ₁ (x k) (σ k) (s k) := h.run.step_of_forall_le hk'
  rw [h.run.eq_add_of_succ hk' hs]
  exact hstep.sub_ge hC.convex hf.contDiffAt hf.lipschitz hf.nonneg hx hp P.θ₁_pos.le
    P.σmin_nonneg hmin hmax P.η₁_pos hs

/-- **Theorem 6.2.5** of [cartis2022evaluation]. Under C.CNe, f.DpL.C and f.bB.C (`p ≥ 1`),
every ARp1-CC run terminates at a first iteration `k_ε` with `ω_{f,𝒞,1}(x_{k_ε}) ≤ ε₁`, after at
most `κ^A_ARp1CC (f(x₀) - f_low)/ε₁^{(p+1)/p} + κ^C_ARp` evaluations of `f` and at most
`κ^S_ARp1CC (f(x₀) - f_low)/ε₁^{(p+1)/p} + 2` evaluations of derivatives. (The restriction
`ε₁ ≤ 1` is not needed.) -/
theorem _root_.CartisGouldToint.Chapter06.theorem_6_2_5
    (hC : AssumptionCNe C) (hf : AssumptionDpLC f C p L)
    (hb : AssumptionBbC f C flow) (hp : 1 ≤ p) (h : algorithm_6_2_2 f C p P ε₁ x s σ) :
    ∃ kε, IsFirstHit (fun k => omega1 f C (x k) ≤ ε₁) kε ∧
      (funEvalCount kε : ℝ) ≤
        kappaAARp1CC P L p * (f (x 0) - flow) / ε₁ ^ (((p : ℝ) + 1) / p) + kappaCARpCC P L ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio f p x s k) kε : ℝ) ≤
        kappaSARp1CC P L p * (f (x 0) - flow) / ε₁ ^ (((p : ℝ) + 1) / p) + 2 := by
  have hL := hf.nonneg
  have hε := h.ε₁_pos
  have hκ := kappa1CC_mul_kappaSARp1CC (P := P) hL p
  have hκ1 : 0 < kappa1CC P L p := by
    have := P.η₁_pos; have := P.σmin_pos; have := P.sigmaMax_pos L; have := P.θ₁_pos
    unfold kappa1CC; positivity
  have he : 0 < ((p : ℝ) + 1) / p := by
    have : (0 : ℝ) < p := by exact_mod_cast hp
    positivity
  obtain ⟨kε, hk, hF, hD⟩ := h.run.exists_isFirstHit_of_decrease (σmax := P.sigmaMax L)
    (V := fun k => f (x k)) (Vlow := flow) (δ := kappa1CC P L p * ε₁ ^ (((p : ℝ) + 1) / p))
    (fun k hk => (h.sigma_le hC hf k (IsARRun.forall_lt_not_stop_iff.1 hk)).2.2) (by positivity)
    (fun k hk => (h.run.accept k hk).le (w := f) rfl
      (lt_of_le_of_lt (by
          have := P.σmin_nonneg.trans
            (h.sigma_le hC hf k fun j hj => IsARRun.forall_le_not_stop_iff.1 hk j hj.le).2.1
          positivity)
        (arpcc_sub_ge h.run (fun _ hs => hs.decrease) (IsARRun.forall_le_not_stop_iff.1 hk)).1))
    (fun k hk => hb _ (h.sigma_le hC hf k (IsARRun.forall_lt_not_stop_iff.1 hk)).1)
    (fun k hk hs => by
      have hk' := IsARRun.forall_le_not_stop_iff.1 hk
      refine le_trans ?_ (lemma_6_2_4 h hC hf hp (fun j hj => hk' j (hj.trans k.le_succ)) hs)
      gcongr
      exact (lt_of_not_ge (hk' (k + 1) le_rfl)).le)
  have hN : (f (x 0) - flow) / (kappa1CC P L p * ε₁ ^ (((p : ℝ) + 1) / p)) =
      kappaSARp1CC P L p * (f (x 0) - flow) / ε₁ ^ (((p : ℝ) + 1) / p) := by
    have : kappaSARp1CC P L p = (kappa1CC P L p)⁻¹ := (eq_inv_of_mul_eq_one_right hκ)
    rw [this]
    have : 0 < ε₁ ^ (((p : ℝ) + 1) / p) := by positivity
    field_simp
  rw [hN] at hF hD
  refine ⟨kε, ⟨hk.1.resolve_right id, fun j hj h' => hk.2 j hj (Or.inl h')⟩, ?_, hD⟩
  refine hF.trans_eq ?_
  rw [kappaAARp1CC, kappaCARpCC]
  ring

end algorithm_6_2_2

end ARp1CC

/-! ### Step 2 of ARp-CC may be infeasible -/

section Counterexample

/-- Derivative of a cubic without constant term. -/
private theorem deriv_cubic (a b c : ℝ) :
    deriv (fun t : ℝ => a * t + b * t ^ 2 + c * t ^ 3) =
      fun t => a + 2 * b * t + 3 * c * t ^ 2 := by
  funext t
  have := (((hasDerivAt_id' t).const_mul a).add ((hasDerivAt_pow 2 t).const_mul b)).add
    ((hasDerivAt_pow 3 t).const_mul c)
  refine this.deriv.trans ?_; push_cast; ring

/-- The first three derivatives of a cubic without constant term. -/
private theorem iteratedDeriv_cubic (a b c t : ℝ) :
    iteratedDeriv 1 (fun t : ℝ => a * t + b * t ^ 2 + c * t ^ 3) t =
        a + 2 * b * t + 3 * c * t ^ 2 ∧
      iteratedDeriv 2 (fun t : ℝ => a * t + b * t ^ 2 + c * t ^ 3) t = 2 * b + 6 * c * t ∧
      iteratedDeriv 3 (fun t : ℝ => a * t + b * t ^ 2 + c * t ^ 3) t = 6 * c := by
  have h1 := deriv_cubic a b c
  have h2 : deriv (fun t : ℝ => a + 2 * b * t + 3 * c * t ^ 2) = fun t => 2 * b + 6 * c * t := by
    have := deriv_cubic (2 * b) (3 * c) 0
    funext t
    have e : (fun t : ℝ => a + 2 * b * t + 3 * c * t ^ 2) =
        fun t => (2 * b * t + 3 * c * t ^ 2 + 0 * t ^ 3) + a := by funext t; ring
    rw [e, deriv_add_const, this]; ring
  have h3 : deriv (fun t : ℝ => 2 * b + 6 * c * t) = fun _ => 6 * c := by
    funext t
    have := ((hasDerivAt_id t).const_mul (6 * c)).const_add (2 * b)
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [iteratedDeriv_one, h1]
  · rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2]
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, h1, h2, h3]

/-- Derivative tensors of a function of the coordinate of `ℝ¹`. -/
private theorem iteratedFDeriv_comp_coord {h : ℝ → ℝ} (hh : ContDiff ℝ ⊤ h) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin 1)) (m : Fin k → EuclideanSpace ℝ (Fin 1)) :
    iteratedFDeriv ℝ k (fun y : EuclideanSpace ℝ (Fin 1) => h (y 0)) x m =
      (∏ i, m i 0) * iteratedDeriv k h (x 0) := by
  have e : (fun y : EuclideanSpace ℝ (Fin 1) => h (y 0)) =
      h ∘ (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) := by
    funext y; simp
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hh _ (by exact_mod_cast le_top)]
  simp [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]

/-- **Step 2 of ARp-CC can be infeasible for `q ≥ 2`** (a gap in [cartis2022evaluation],
§6.2.1: the book asserts that the model measures (6.2.3)–(6.2.5) "will all be small in the
neighbourhood of any … global minimizer of `m_k`", but Step 2 also demands
`m_k(s_k) < m_k(0)`). For all ARp-CC constants and `ε₁, ε₂ > 0`, `q ≥ 2`, take `n = 1`,
`𝒞 = {x | x₁ ≥ 0}`, `p = 3`, `g = τ₁ε₁`, `K = 2ε₂`, `c = K²/(8g)` and
`f(x) = g x₁ - K/2 x₁² + c x₁³`. Then C.CNe, f.DpL.C (`L = 0`) and f.bB.C (`f_low = 0`) hold and
`x = 0` is a strict global minimizer of `f` on `𝒞`; yet `x = 0` fails the second-order test
(`ω_{f,𝒞,2}(0, ε₁) ≥ K > ε₂`, attained in the ascent direction `d = 1`), and no step satisfies
the Step-2 conditions at `x = 0` for any `σ ≥ 0`, because
`m(s) - m(0) = s(g - K s/2 + c s²) + σ s⁴/24 ≥ 0` for `s ≥ 0`. Hence no ARp-CC run starts from
`x₀ = 0`. -/
theorem algorithm_6_2_1_not_exists_step (P : ARpCCParams) {ε₁ ε₂ ε₃ : ℝ} (h₁ : 0 < ε₁)
    (h₂ : 0 < ε₂) {q : ℕ} (hq : 2 ≤ q) :
    ∃ (C : Set (EuclideanSpace ℝ (Fin 1))) (f : EuclideanSpace ℝ (Fin 1) → ℝ),
      AssumptionCNe C ∧ AssumptionDpLC f C 3 0 ∧ AssumptionBbC f C 0 ∧ (0 : _) ∈ C ∧
      (∀ y ∈ C, y ≠ 0 → f 0 < f y) ∧
      ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ 0 ∧
      (∀ σ, 0 ≤ σ → ∀ s, ¬ IsARpCCStep f C 3 P q ε₁ ε₂ ε₃ 0 σ s) ∧
      ¬ ∃ x s σ, x 0 = 0 ∧ algorithm_6_2_1 f C 3 P q ε₁ ε₂ ε₃ x s σ := by
  set g := P.τ₁ * ε₁ with hg_def
  set K := 2 * ε₂ with hK_def
  set c := K ^ 2 / (8 * g) with hc_def
  have hg : 0 < g := mul_pos P.τ₁_pos h₁
  have hK : 0 < K := by positivity
  have hc : 0 < c := by positivity
  set h : ℝ → ℝ := fun t => g * t + (-K / 2) * t ^ 2 + c * t ^ 3 with hh_def
  have hh : ContDiff ℝ ⊤ h := by rw [hh_def]; fun_prop
  have hD : ∀ t, iteratedDeriv 1 h t = g + 2 * (-K / 2) * t + 3 * c * t ^ 2 ∧
      iteratedDeriv 2 h t = 2 * (-K / 2) + 6 * c * t ∧ iteratedDeriv 3 h t = 6 * c :=
    iteratedDeriv_cubic g (-K / 2) c
  set f : EuclideanSpace ℝ (Fin 1) → ℝ := fun y => h (y 0) with hf_def
  set C : Set (EuclideanSpace ℝ (Fin 1)) := {y | 0 ≤ y 0} with hC_def
  have hquad : ∀ t, g / 2 ≤ g + (-K / 2) * t + c * t ^ 2 := by
    intro t
    have : c * (8 * g) = K ^ 2 := by rw [hc_def]; field_simp
    nlinarith [sq_nonneg (K * t - 2 * g)]
  have hfval : ∀ y, f y = y 0 * (g + (-K / 2) * y 0 + c * y 0 ^ 2) := by
    intro y; simp only [hf_def, hh_def]; ring
  have hf0 : f 0 = 0 := by simp [hfval]
  have hfnn : ∀ y ∈ C, 0 ≤ f y := fun y hy => by
    rw [hfval]; exact mul_nonneg hy (by linarith [hquad (y 0)])
  have hdiag : ∀ k x d, iteratedFDeriv ℝ k f x (fun _ => d) = d 0 ^ k * iteratedDeriv k h (x 0) :=
    fun k x d => by rw [iteratedFDeriv_comp_coord hh]; simp
  -- the assumptions
  have hCNe : AssumptionCNe C := by
    refine ⟨isClosed_le continuous_const (by fun_prop), ?_, ⟨0, by simp [hC_def]⟩⟩
    intro x hx y hy a b ha hb _
    simp only [hC_def, mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at *
    positivity
  have hfC : ContDiff ℝ ⊤ f := by
    have := hh.comp (EuclideanSpace.proj (0 : Fin 1) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).contDiff
    convert this using 1
    funext y; simp [hf_def]
  have hDpL : AssumptionDpLC f C 3 0 := by
    refine ⟨le_rfl, ⟨univ, isOpen_univ, subset_univ _,
      (hfC.of_le (by exact_mod_cast le_top)).contDiffOn⟩, ?_⟩
    intro x _ y _
    have : iteratedFDeriv ℝ 3 f x = iteratedFDeriv ℝ 3 f y := by
      ext m
      rw [iteratedFDeriv_comp_coord hh, iteratedFDeriv_comp_coord hh, (hD (x 0)).2.2,
        (hD (y 0)).2.2]
    simp [this]
  -- the strict minimizer
  have hstrict : ∀ y ∈ C, y ≠ 0 → f 0 < f y := by
    intro y hy hy0
    have hpos : 0 < y 0 := by
      refine lt_of_le_of_ne hy fun h0 => hy0 ?_
      ext i; fin_cases i; simp [← h0]
    rw [hf0, hfval]
    exact mul_pos hpos (by linarith [hquad (y 0)])
  -- the second-order test fails at `0`
  have hnot : ¬ IsApproxMinimizerCC f C P.τ₁ P.τ₂ q ε₁ ε₂ ε₃ 0 := by
    rintro ⟨-, -, h2, -⟩
    set e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
    have he : e 0 = 1 := by simp [e]
    have hmem : e ∈ Metric.closedBall 0 1 ∩ restrictedSteps₁ f C P.τ₁ ε₁ 0 := by
      refine ⟨by simp [e], ?_, ?_⟩
      · simp [mem_feasibleSteps, hC_def, he]
      · have : |g| ≤ P.τ₁ * ε₁ := by rw [abs_of_pos hg]
        rw [hdiag, he, (hD _).1]; simpa using this
    have := le_formCriticality (iteratedFDeriv ℝ 2 f 0) hmem
    rw [hdiag, he, (hD _).2.1] at this
    have h2' := h2 hq
    rw [omega2] at h2'
    norm_num at this
    linarith
  -- no admissible step at `0`
  have hnostep : ∀ σ, 0 ≤ σ → ∀ s, ¬ IsARpCCStep f C 3 P q ε₁ ε₂ ε₃ 0 σ s := by
    intro σ hσ s hs
    have hdec := hs.decrease
    have hsC : s ∈ C := by simpa using hs.mem
    rw [regularizedModel_ftaylorSeries_zero_right, hf0, regularizedModel_def,
      FormalMultilinearSeries.taylorSum_def] at hdec
    have hT : ∑ i ∈ Finset.range (3 + 1), ((i ! : ℝ))⁻¹ • ftaylorSeries ℝ f 0 i (fun _ => s) =
        f s := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, ftaylorSeries,
        hdiag, smul_eq_mul]
      rw [(hD _).1, (hD _).2.1, (hD _).2.2, iteratedDeriv_zero, hfval]
      simp only [hh_def, Nat.factorial, PiLp.zero_apply]
      push_cast
      ring
    rw [hT] at hdec
    have := hfnn s hsC
    have : 0 ≤ σ / ((3 + 1)! : ℝ) * ‖s‖ ^ (3 + 1) := by positivity
    linarith
  refine ⟨C, f, hCNe, hDpL, fun y hy => hf0 ▸ (hfnn y hy), by simp [hC_def], hstrict, hnot,
    hnostep, ?_⟩
  rintro ⟨x, s, σ, hx0, hrun⟩
  have hst := hrun.run.step 0 (fun j hj => absurd hj (Nat.not_lt_zero _))
    (by rw [hx0]; exact hnot)
  rw [hx0] at hst
  exact hnostep (σ 0) (hrun.run.sigma_zero ▸ P.σ₀_pos.le) (s 0) hst

end Counterexample

end CartisGouldToint.Chapter06
