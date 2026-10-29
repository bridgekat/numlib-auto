import Numlib.Analysis.SpecialFunctions.Pow.Real
import Numlib.Optimization.ResidualPower
import NumlibSurface.CartisGouldToint.Chapter01.Section01

/-!
# Cartis–Gould–Toint §5.1: Nonlinear least squares and least Euclidean norms

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §5.1. For a residual
`r : ℝⁿ → ℝᵐ` (`ℝⁿ = EuclideanSpace ℝ (Fin n)`) the problem `minimize ‖r(x)‖` is attacked through
`Φ_ℓ(x) = ‖r(x)‖^ℓ/ℓ` (5.1.3), the backbone `Optimization.residualPow`. The ARpLE algorithm
(Algorithm 5.1.1) is the ARp method `Optimization.IsARpRun` applied to `Φ_ℓ` with the
residual-scaled termination tests (5.1.9)–(5.1.14), and its complexity (Theorem 5.1.7) follows by
telescoping the potential `‖r(x_k)‖^{1/2^i}`.

## Main definitions

* `Phi r ℓ` — `Φ_ℓ` (5.1.3); `psiOne`, `psiTwo`, `psiTwoDir`, `psiThree` — the scaled measures
  `ψ_{ℓ,1}`, `ψ_{ℓ,2}`, `ψ_{ℓ,2}(·, d)`, `ψ_{ℓ,3}(·, d)` of (5.1.6)–(5.1.7); `zSet` — `𝒵_ε`.
* `AssumptionPhiDpL` — assumption Φ_ℓ.DpL.
* `ARpLEStop`, `mdir`, `algorithm_5_1_1` — the Step-1 test, the sets `𝓜_k` (4.1.14) and the
  ARpLE run predicate.
* `iota j p ℓ i` — the exponents `ι₁, ι₂, ι₃` of (5.1.21), (5.1.23), (5.1.25).
* `kappa₁`, `kappa₂`, `kappa₃`, `kappaS₂` — the constants (4.1.32), (4.1.34), (4.1.36), (4.1.23)
  with `L = L_{Φ_ℓ,p}`.

## Main results

* `lemma_5_1_1` — smoothness of `Φ_ℓ`.
* `algorithm_5_1_1.exists_run` — ARpLE runs exist for `q ≤ 2`.
* `lemma_5_1_2`, `lemma_5_1_3`, `lemma_5_1_4` — bounds on the residual decrease.
* `lemma_5_1_5`, `lemma_5_1_6` — odd factorizations and good exponents.
* `theorem_5_1_7_of_iota_nonneg`, `theorem_5_1_7` — complexity of ARpLE.
* `psiOne_eq_of_jacobian`, `psiOne_ge_of_jacobian` — (5.1.63)–(5.1.64).

## Deviations from the book

* **The third-order test.** Algorithm 5.1.1 requires `𝓜_k ≠ ∅` in the third-order branch of the
  test. With that requirement the proof of Theorem 5.1.7 breaks down when `𝓜_{k+1} = ∅`: none of
  (5.1.48)–(5.1.49) or (5.1.51)–(5.1.52) then needs to hold, and there is no guaranteed decrease.
  `ARpLEStop` reads the condition "for all `d ∈ 𝓜_k`" vacuously instead; the guarantee at
  termination ("for all `d ∈ 𝓜_ε`") is unchanged.
* **Existence of runs.** For `q = 3` an admissible step need not exist when the test fails (see
  `Optimization.ARpRun`), so runs are only shown to exist for `q ≤ 2`; the complexity theorems
  hold for every run.
* **Lemma 5.1.1** is proved for `ℓ > 2p` as stated (the backbone gives `ℓ ≥ 2p`).
* **Lemma 5.1.5** needs `p ≠ 0` (the book writes `p ∈ ℕ`).
* **Theorem 5.1.7.** The multiplier in (5.1.44) is `κ^A` (printed `κ^C`); in (5.1.51) the three
  conditions are alternatives ("or", printed "and"), and the set `𝓜_{j+1}` there is that of
  (4.1.14) (printed "(4.1.9)"). The run may also stop by the strict-local-minimizer test
  (5.1.11), which is one of the termination branches of `ARpLEStop`. The theorem is proved in a
general form (`theorem_5_1_7_of_iota_nonneg`, any order
  `q ≤ 3` and any `ℓ`, `i` with `ι_j ≥ 0` for `j ≤ q`), which also covers the first- and
  second-order variants mentioned after the book's proof. The book's hypothesis
  `(ε₀, …, ε₃) ∈ (0, 1]⁴` is only used as `ε_j > 0`.
-/

open Set Optimization
open scoped Nat

namespace CartisGouldToint.Chapter05

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)
set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-! ### The objective `Φ_ℓ` and the scaled criticality measures -/

/-- The objective `Φ_ℓ(x) = ‖r(x)‖^ℓ / ℓ` of [cartis2022evaluation], (5.1.3); `Φ_1 = ‖r‖` is
(5.1.1) and `Φ_2` the least-squares objective (5.1.2). -/
noncomputable abbrev Phi (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) : ℝⁿ → ℝ :=
  residualPow r ℓ

theorem Phi_apply (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (x : ℝⁿ) : Phi r ℓ x = ‖r x‖ ^ ℓ / ℓ :=
  rfl

/-- For a natural exponent, `Φ_ℓ(x) = ‖r(x)‖^ℓ / ℓ` with the natural power. -/
theorem Phi_natCast (r : ℝⁿ → ℝᵐ) (ℓ : ℕ) (x : ℝⁿ) : Phi r ℓ x = ‖r x‖ ^ ℓ / ℓ :=
  residualPow_natCast r ℓ x

/-- **Lemma 5.1.1** ([cartis2022evaluation]): if `r` is `C^p`, so is `Φ_ℓ` when `ℓ` is an even
natural number or a real `ℓ > 2p`. -/
theorem lemma_5_1_1 {r : ℝⁿ → ℝᵐ} {p : ℕ} {ℓ : ℝ} (hr : ContDiff ℝ p r)
    (hℓ : (∃ k : ℕ, ℓ = 2 * k) ∨ 2 * (p : ℝ) < ℓ) : ContDiff ℝ p (Phi r ℓ) :=
  contDiff_residualPow hr (hℓ.imp_right le_of_lt)

/-- The scaled first-order measure `ψ_{ℓ,1}(x) = ‖∇Φ_ℓ(x)‖ / ‖r(x)‖^{ℓ-1}`
([cartis2022evaluation], §5.1.1). (Where `r(x) = 0` and `ℓ ≠ 1`, the denominator is `0` and
Lean's division gives `0`; for `ℓ = 1` it is `0^0 = 1`. The case `r(x) = 0` is excluded by the
test (5.1.9).) -/
noncomputable def psiOne (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (x : ℝⁿ) : ℝ :=
  ‖gradient (Phi r ℓ) x‖ / ‖r x‖ ^ (ℓ - 1)

/-- The scaled second-order measure `ψ_{ℓ,2}(x) = λ_min[∇²Φ_ℓ(x)] / ‖r(x)‖^{ℓ-1}`
([cartis2022evaluation], §5.1.1). -/
noncomputable def psiTwo (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (x : ℝⁿ) : ℝ :=
  Chapter01.hessianMinEig (Phi r ℓ) x / ‖r x‖ ^ (ℓ - 1)

/-- The scaled curvature along `d`, `ψ_{ℓ,2}(x, d) = |∇²Φ_ℓ(x)[d]²| / ‖r(x)‖^{ℓ-1}`
([cartis2022evaluation], (5.1.7)). -/
noncomputable def psiTwoDir (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (x d : ℝⁿ) : ℝ :=
  |iteratedFDeriv ℝ 2 (Phi r ℓ) x (fun _ => d)| / ‖r x‖ ^ (ℓ - 1)

/-- The scaled third-order measure along `d`,
`ψ_{ℓ,3}(x, d) = |∇³Φ_ℓ(x)[d]³| / ‖r(x)‖^{ℓ-1}` ([cartis2022evaluation], (5.1.6)). -/
noncomputable def psiThree (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (x d : ℝⁿ) : ℝ :=
  |iteratedFDeriv ℝ 3 (Phi r ℓ) x (fun _ => d)| / ‖r x‖ ^ (ℓ - 1)

/-- The set `𝒵_ε = {d | ‖d‖ = 1, ψ_{ℓ,2}(x, d) ≤ ε₂}` of directions of small scaled curvature
([cartis2022evaluation], (5.1.7)). -/
def zSet (r : ℝⁿ → ℝᵐ) (ℓ ε₂ : ℝ) (x : ℝⁿ) : Set ℝⁿ :=
  {d | ‖d‖ = 1 ∧ psiTwoDir r ℓ x d ≤ ε₂}

section Measures

variable {r : ℝⁿ → ℝᵐ} {ℓ : ℝ} {x : ℝⁿ}

theorem mem_zSet {ε₂ : ℝ} {d : ℝⁿ} : d ∈ zSet r ℓ ε₂ x ↔ ‖d‖ = 1 ∧ psiTwoDir r ℓ x d ≤ ε₂ :=
  Iff.rfl

private theorem scale_pos (hx : r x ≠ 0) : 0 < ‖r x‖ ^ (ℓ - 1) :=
  Real.rpow_pos_of_pos (norm_pos_iff.2 hx) _

theorem psiOne_eq : psiOne r ℓ x = ‖fderiv ℝ (Phi r ℓ) x‖ / ‖r x‖ ^ (ℓ - 1) := by
  rw [psiOne, norm_gradient_eq]

theorem psiTwo_eq :
    psiTwo r ℓ x = minCurvature (iteratedFDeriv ℝ 2 (Phi r ℓ) x) / ‖r x‖ ^ (ℓ - 1) :=
  rfl

theorem psiOne_nonneg : 0 ≤ psiOne r ℓ x :=
  div_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem psiTwoDir_nonneg {d : ℝⁿ} : 0 ≤ psiTwoDir r ℓ x d :=
  div_nonneg (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem psiThree_nonneg {d : ℝⁿ} : 0 ≤ psiThree r ℓ x d :=
  div_nonneg (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)

/-- Off the zeros of `r`, `ψ_{ℓ,1}(x) ≤ ε` iff `‖∇Φ_ℓ(x)‖ ≤ ε ‖r(x)‖^{ℓ-1}`. -/
theorem psiOne_le_iff (hx : r x ≠ 0) {ε : ℝ} :
    psiOne r ℓ x ≤ ε ↔ ‖fderiv ℝ (Phi r ℓ) x‖ ≤ ε * ‖r x‖ ^ (ℓ - 1) := by
  rw [psiOne_eq, div_le_iff₀ (scale_pos hx)]

/-- Off the zeros of `r`, `ψ_{ℓ,2}(x) < -ε` iff `ε ‖r(x)‖^{ℓ-1} < -λ_min[∇²Φ_ℓ(x)]`. -/
theorem psiTwo_lt_neg_iff (hx : r x ≠ 0) {ε : ℝ} :
    psiTwo r ℓ x < -ε ↔
      ε * ‖r x‖ ^ (ℓ - 1) < -minCurvature (iteratedFDeriv ℝ 2 (Phi r ℓ) x) := by
  rw [psiTwo_eq, div_lt_iff₀ (scale_pos hx)]
  constructor <;> intro h <;> linarith

theorem psiTwoDir_le_iff (hx : r x ≠ 0) {ε : ℝ} {d : ℝⁿ} :
    psiTwoDir r ℓ x d ≤ ε ↔ |iteratedFDeriv ℝ 2 (Phi r ℓ) x (fun _ => d)| ≤ ε * ‖r x‖ ^ (ℓ - 1) :=
  div_le_iff₀ (scale_pos hx)

theorem psiThree_le_iff (hx : r x ≠ 0) {ε : ℝ} {d : ℝⁿ} :
    psiThree r ℓ x d ≤ ε ↔ |iteratedFDeriv ℝ 3 (Phi r ℓ) x (fun _ => d)| ≤ ε * ‖r x‖ ^ (ℓ - 1) :=
  div_le_iff₀ (scale_pos hx)

/-- Off the zeros of `r`, `𝒵_ε` is the set of unit directions of curvature at most
`ε₂ ‖r(x)‖^{ℓ-1}` in absolute value. -/
theorem zSet_eq (hx : r x ≠ 0) (ε₂ : ℝ) :
    zSet r ℓ ε₂ x = smallCurvatureDirections (iteratedFDeriv ℝ 2 (Phi r ℓ) x)
      (ε₂ * ‖r x‖ ^ (ℓ - 1)) := by
  ext d
  rw [mem_zSet, mem_smallCurvatureDirections, psiTwoDir_le_iff hx]

/-- `(ω / b^e)^ν b^{eν} ≤ ω^ν` for `b, e, ω ≥ 0`, `ν > 0` (with equality if `b > 0`): undoing
the scaling of a measure. -/
private theorem div_rpow_mul_le {ω b e ν : ℝ} (hω : 0 ≤ ω) (hb : 0 ≤ b) (hν : 0 < ν) :
    (ω / b ^ e) ^ ν * b ^ (e * ν) ≤ ω ^ ν := by
  rcases hb.lt_or_eq with hb | hb
  · rw [Real.rpow_mul hb.le, ← Real.mul_rpow (div_nonneg hω (Real.rpow_nonneg hb.le _))
      (Real.rpow_nonneg hb.le _), div_mul_cancel₀ _ (Real.rpow_pos_of_pos hb _).ne']
  · subst hb
    rcases eq_or_ne e 0 with he | he
    · simp [he]
    · rw [Real.zero_rpow he, div_zero, Real.zero_rpow hν.ne', zero_mul]
      exact Real.rpow_nonneg hω _

end Measures

/-! ### The algorithm -/

/-- **Assumption Φ_ℓ.DpL** ([cartis2022evaluation], §5.1.2): `Φ_ℓ` is `p` times continuously
differentiable on `ℝⁿ` and its `p`-th derivative is Lipschitz with constant `L ≥ 0` (tensor norm
= operator norm). -/
structure AssumptionPhiDpL (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (p : ℕ) (L : ℝ) : Prop where
  /-- `Φ_ℓ ∈ C^p`. -/
  contDiff : ContDiff ℝ p (Phi r ℓ)
  /-- `L ≥ 0`. -/
  nonneg : 0 ≤ L
  /-- `∇^p Φ_ℓ` is `L`-Lipschitz. -/
  lipschitz : IteratedFDerivLipschitzOn (Phi r ℓ) p L univ

/-- Φ_ℓ.DpL is the backbone predicate `IteratedFDerivLipschitzOn` for `Φ_ℓ` on `ℝⁿ`, together with
`Φ_ℓ ∈ C^p` and `L ≥ 0`. -/
theorem assumptionPhiDpL_iff {r : ℝⁿ → ℝᵐ} {ℓ : ℝ} {p : ℕ} {L : ℝ} :
    AssumptionPhiDpL r ℓ p L ↔
      ContDiff ℝ p (Phi r ℓ) ∧ 0 ≤ L ∧ IteratedFDerivLipschitzOn (Phi r ℓ) p L univ :=
  ⟨fun h => ⟨h.contDiff, h.nonneg, h.lipschitz⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

/-- The Step-1 termination test of ARpLE ([cartis2022evaluation], Algorithm 5.1.1, (5.1.9)–(5.1.14))
at the point `x` with the direction set `M = 𝓜_k`, for the order `q ∈ {1, 2, 3}` (the book's
`ε₂ = ε₃ = ∞` is `q = 1`, `ε₃ = ∞ > ε₂` is `q = 2`); the tolerances of index `> q` are unused.
The branches are: `‖r(x)‖ ≤ ε₀` (5.1.9); `q = 1` and (5.1.10); `q ≥ 2`, (5.1.10) and the
strict-local-minimizer test (5.1.11); `q = 2`, (5.1.10) and (5.1.12); `q = 3`, (5.1.10), (5.1.12)
and (5.1.13)–(5.1.14) for all `d ∈ M`. The book also requires `𝓜_k ≠ ∅` in the last branch;
that requirement is dropped (see the module documentation). -/
def ARpLEStop (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (q : ℕ) (ε₀ ε₁ ε₂ ε₃ : ℝ) (M : Set ℝⁿ) (x : ℝⁿ) : Prop :=
  ‖r x‖ ≤ ε₀ ∨
    (q = 1 ∧ psiOne r ℓ x ≤ ε₁) ∨
    (2 ≤ q ∧ psiOne r ℓ x ≤ ε₁ ∧ ε₂ < psiTwo r ℓ x) ∨
    (q = 2 ∧ psiOne r ℓ x ≤ ε₁ ∧ -ε₂ ≤ psiTwo r ℓ x) ∨
    (q = 3 ∧ psiOne r ℓ x ≤ ε₁ ∧ -ε₂ ≤ psiTwo r ℓ x ∧
      ∀ d ∈ M, psiThree r ℓ x d ≤ ε₃ ∧ psiTwoDir r ℓ x d ≤ ε₂)

/-- The direction sets `𝓜_k` of ARpLE ([cartis2022evaluation], Algorithm 4.1.1 Step 0 and
(4.1.14), applied to `f = Φ_ℓ`): `𝓜_0` contains the unit directions of curvature at most `ε₂` of
`∇²Φ_ℓ(x_0)`, and `𝓜_{k+1}` those of curvature at most `θ₂ ‖s_k‖^{p-1}` of the model Hessian
`∇²m_k(s_k)`. -/
noncomputable def mdir (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (p : ℕ) (P : ARpParams) (ε₂ : ℝ) (x s : ℕ → ℝⁿ)
    (σ : ℕ → ℝ) : ℕ → Set ℝⁿ
  | 0 => smallCurvatureDirections (iteratedFDeriv ℝ 2 (Phi r ℓ) (x 0)) ε₂
  | k + 1 => smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ (Phi r ℓ) (x k)) p (σ k)) (s k))
      (P.θ₂ * ‖s k‖ ^ (p - 1))

theorem mdir_succ (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (p : ℕ) (P : ARpParams) (ε₂ : ℝ) (x s : ℕ → ℝⁿ)
    (σ : ℕ → ℝ) (k : ℕ) :
    mdir r ℓ p P ε₂ x s σ (k + 1) = smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ (Phi r ℓ) (x k)) p (σ k)) (s k))
      (P.θ₂ * ‖s k‖ ^ (p - 1)) :=
  rfl

/-- The directions in `𝓜_k` are unit vectors. -/
theorem norm_eq_one_of_mem_mdir {r : ℝⁿ → ℝᵐ} {ℓ : ℝ} {p : ℕ} {P : ARpParams} {ε₂ : ℝ}
    {x s : ℕ → ℝⁿ} {σ : ℕ → ℝ} {k : ℕ} {d : ℝⁿ} (hd : d ∈ mdir r ℓ p P ε₂ x s σ k) : ‖d‖ = 1 := by
  cases k with
  | zero => exact hd.1
  | succ k => exact hd.1

/-- **Algorithm 5.1.1** (ARpLE, [cartis2022evaluation]) as a run predicate: the ARp method
(Algorithm 4.1.1, `Optimization.IsARpRun`) applied to `f = Φ_ℓ` with the model (5.1.8), the
order `q`, the constants `P` (`σ₀, σ_min, η₁, η₂, γ₁, γ₂, γ₃, θ₁, θ₂, θ₃`) and the Step-1 test
`ARpLEStop` with `𝓜_k = mdir …`. Iteration `k` is successful iff
`P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k`. -/
def algorithm_5_1_1 (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (p : ℕ) (P : ARpParams) (q : ℕ)
    (ε₀ ε₁ ε₂ ε₃ : ℝ) (x s : ℕ → ℝⁿ) (σ : ℕ → ℝ) : Prop :=
  IsARpRun (Phi r ℓ) p P q
    (fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k)) x s σ

namespace algorithm_5_1_1

variable {r : ℝⁿ → ℝᵐ} {ℓ : ℝ} {p q : ℕ} {P : ARpParams} {ε₀ ε₁ ε₂ ε₃ : ℝ} {x s : ℕ → ℝⁿ}
  {σ : ℕ → ℝ}

/-- An ARpLE run is an ARp run. -/
theorem isARpRun (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ) :
    IsARpRun (Phi r ℓ) p P q
      (fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k)) x s σ :=
  h

/-- The residual norm does not increase along an ARpLE run before termination (`ℓ > 0`). -/
theorem norm_succ_le (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ) (hℓ : 0 < ℓ) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ j) (x j)) :
    ‖r (x (k + 1))‖ ≤ ‖r (x k)‖ := by
  have hk' : ∀ j ≤ k, ¬ IsARRun.Stop
      (fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k)) (fun _ => False) j :=
    fun j hj h' => h'.elim (hk j hj) id
  by_cases hs : P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k
  · obtain ⟨-, hdec⟩ := h.isARpRun.toIsARRun.sub_ge_of_succ_taylor hk'
      (h.isARpRun.step_spec hk).decrease hs
    have hσ : 0 ≤ σ k := (h.isARpRun.sigma_pos (k := k) fun j hj => hk j hj.le).le
    have : 0 ≤ P.η₁ * (σ k / ((p + 1)! : ℝ) * ‖s k‖ ^ (p + 1)) := by
      have := P.η₁_pos; positivity
    have hle : Phi r ℓ (x (k + 1)) ≤ Phi r ℓ (x k) := by linarith
    rw [Phi_apply, Phi_apply, div_le_div_iff_of_pos_right hℓ] at hle
    exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hℓ).1 hle
  · rw [h.isARpRun.eq_of_not_succ hk hs]

/-- The residual norms stay below `‖r(x_0)‖` up to termination (`ℓ > 0`). -/
theorem norm_le_norm_zero (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ) (hℓ : 0 < ℓ) :
    ∀ k, (∀ j < k, ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ j) (x j)) →
      ‖r (x k)‖ ≤ ‖r (x 0)‖ := by
  intro k
  induction k with
  | zero => exact fun _ => le_rfl
  | succ k ih =>
    intro hk
    exact (h.norm_succ_le hℓ fun j hj => hk j (Nat.lt_succ_of_le hj)).trans
      (ih fun j hj => hk j (hj.trans k.lt_succ_self))

end algorithm_5_1_1

/-! ### Bounds on the residual decrease -/

/-- The constant `κ₁` of (4.1.32) ([cartis2022evaluation]), with `σ_max` of (4.1.19). -/
noncomputable def kappa₁ (P : ARpParams) (L : ℝ) (p : ℕ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    ((p ! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₁ * p !)) ^ (((p : ℝ) + 1) / p)

/-- The constant `κ_{s2} = (p-1)!/(L + σ_max + θ₂ (p-1)!)` of (4.1.23) ([cartis2022evaluation]). -/
noncomputable def kappaS₂ (P : ARpParams) (L : ℝ) (p : ℕ) : ℝ :=
  ((p - 1)! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₂ * (p - 1)!)

/-- The constant `κ₂ = η₁ σ_min/(p+1)! κ_{s2}^{(p+1)/(p-1)}` of (4.1.34)
([cartis2022evaluation]). -/
noncomputable def kappa₂ (P : ARpParams) (L : ℝ) (p : ℕ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) * kappaS₂ P L p ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))

/-- The constant `κ₃` of (4.1.36) ([cartis2022evaluation]). -/
noncomputable def kappa₃ (P : ARpParams) (L : ℝ) (p : ℕ) : ℝ :=
  P.η₁ * P.σmin / ((p + 1)! : ℝ) *
    (((p - 2)! : ℝ) / (L + arSigmaMax P.toARParams L + P.θ₃ * (p - 2)!)) ^
      (((p : ℝ) + 1) / ((p : ℝ) - 2))

section Constants

variable {P : ARpParams} {L : ℝ} {p : ℕ}

private theorem sum_pos (hL : 0 ≤ L) {θ : ℝ} (hθ : 0 < θ) (j : ℕ) :
    0 < L + arSigmaMax P.toARParams L + θ * (j ! : ℝ) := by
  have := arSigmaMax_pos P.toARParams L
  positivity

private theorem coef_nonneg : 0 ≤ P.η₁ * P.σmin / ((p + 1)! : ℝ) := by
  have := P.η₁_pos; have := P.σmin_nonneg; positivity

theorem kappa₁_nonneg (hL : 0 ≤ L) : 0 ≤ kappa₁ P L p := by
  have := sum_pos (P := P) hL P.θ₁_pos p
  have := coef_nonneg (P := P) (p := p)
  unfold kappa₁; positivity

theorem kappaS₂_pos (hL : 0 ≤ L) : 0 < kappaS₂ P L p := by
  have := sum_pos (P := P) hL P.θ₂_pos (p - 1)
  unfold kappaS₂; positivity

theorem kappa₂_nonneg (hL : 0 ≤ L) : 0 ≤ kappa₂ P L p := by
  have := (kappaS₂_pos (P := P) (p := p) hL).le
  have := coef_nonneg (P := P) (p := p)
  unfold kappa₂; positivity

theorem kappa₃_nonneg (hL : 0 ≤ L) : 0 ≤ kappa₃ P L p := by
  have := sum_pos (P := P) hL P.θ₃_pos (p - 2)
  have := coef_nonneg (P := P) (p := p)
  unfold kappa₃; positivity

theorem kappa₁_pos (hL : 0 ≤ L) (hσ : 0 < P.σmin) : 0 < kappa₁ P L p := by
  have := sum_pos (P := P) hL P.θ₁_pos p
  have := P.η₁_pos
  unfold kappa₁; positivity

theorem kappa₂_pos (hL : 0 ≤ L) (hσ : 0 < P.σmin) : 0 < kappa₂ P L p := by
  have := kappaS₂_pos (P := P) (p := p) hL
  have := P.η₁_pos
  unfold kappa₂; positivity

theorem kappa₃_pos (hL : 0 ≤ L) (hσ : 0 < P.σmin) : 0 < kappa₃ P L p := by
  have := sum_pos (P := P) hL P.θ₃_pos (p - 2)
  have := P.η₁_pos
  unfold kappa₃; positivity

end Constants

section Decrease

variable {r : ℝⁿ → ℝᵐ} {p q : ℕ} {P : ARpParams} {ε₀ ε₁ ε₂ ε₃ L : ℝ} {x s : ℕ → ℝⁿ}
  {σ : ℕ → ℝ}

/-- `(ω / t) t ≤ ω` for `ω, t ≥ 0`. -/
private theorem div_mul_le_self {ω t : ℝ} (hω : 0 ≤ ω) (ht : 0 ≤ t) : ω / t * t ≤ ω := by
  rcases ht.lt_or_eq with ht | ht
  · rw [div_mul_cancel₀ _ ht.ne']
  · rw [← ht, mul_zero]; exact hω

/-- The decreases of Lemma 4.1.4 for `f = Φ_ℓ`, multiplied by `ℓ`, in terms of the unscaled
measures at `x_{k+1}` (and the step-length decrease (4.1.37) with (4.1.23)). -/
private theorem decrease_unscaled {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ) (hΦ : AssumptionPhiDpL r ℓ p L)
    (hp : 1 ≤ p) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ j) (x j))
    (hs : P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k) :
    ℓ * kappa₁ P L p * ‖fderiv ℝ (Phi r ℓ) (x (k + 1))‖ ^ (((p : ℝ) + 1) / p) ≤
        ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ ∧
    (2 ≤ q → ℓ * kappa₂ P L p *
        (max 0 (-minCurvature (iteratedFDeriv ℝ 2 (Phi r ℓ) (x (k + 1))))) ^
          (((p : ℝ) + 1) / ((p : ℝ) - 1)) ≤ ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ) ∧
    (3 ≤ q → ∀ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1), ℓ * kappa₃ P L p *
        |iteratedFDeriv ℝ 3 (Phi r ℓ) (x (k + 1)) (fun _ => d)| ^
          (((p : ℝ) + 1) / ((p : ℝ) - 2)) ≤ ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ) ∧
    (2 ≤ q → ∀ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1),
      |iteratedFDeriv ℝ 2 (Phi r ℓ) (x (k + 1)) (fun _ => d)| ≤ ‖s k‖ ^ (p - 1) / kappaS₂ P L p) ∧
    (2 ≤ q → ∀ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1), ℓ * kappa₂ P L p *
        |iteratedFDeriv ℝ 2 (Phi r ℓ) (x (k + 1)) (fun _ => d)| ^
          (((p : ℝ) + 1) / ((p : ℝ) - 1)) ≤ ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ) := by
  obtain ⟨d0, d1, d2, d3⟩ := h.isARpRun.decrease_ge hΦ.contDiff hΦ.lipschitz hΦ.nonneg hp hqp hk hs
  obtain ⟨-, -, -, -, b5⟩ :=
    h.isARpRun.step_lower_bounds hΦ.contDiff hΦ.lipschitz hΦ.nonneg hp hqp hk hs
  have hsub : Phi r ℓ (x k) - Phi r ℓ (x (k + 1)) =
      (‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ) / ℓ := by
    rw [Phi_apply, Phi_apply]; ring
  have hmul : ∀ {c : ℝ}, c ≤ Phi r ℓ (x k) - Phi r ℓ (x (k + 1)) →
      ℓ * c ≤ ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ := fun hc => by
    rw [hsub, le_div_iff₀ hℓ] at hc; linarith
  have hK2 := kappaS₂_pos (P := P) (p := p) hΦ.nonneg
  -- (4.1.23) in the form `|∇²Φ(x_{k+1})[d]²| ≤ ‖s_k‖^{p-1}/κ_{s2}`
  have h18 : 2 ≤ q → ∀ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1),
      |iteratedFDeriv ℝ 2 (Phi r ℓ) (x (k + 1)) (fun _ => d)| ≤
        ‖s k‖ ^ (p - 1) / kappaS₂ P L p := fun hq d hd => by
    have hfac : (0 : ℝ) < (p - 1)! := by positivity
    have hK := sum_pos (P := P) hΦ.nonneg P.θ₂_pos (p - 1)
    refine (b5 hq d hd).trans_eq ?_
    rw [kappaS₂]
    field_simp
  refine ⟨by rw [mul_assoc]; exact hmul d1, fun hq => by rw [mul_assoc]; exact hmul (d2 hq),
    fun hq d hd => by rw [mul_assoc]; exact hmul (d3 hq d hd), h18, fun hq d hd => ?_⟩
  -- (5.1.57): the decrease from `‖s_k‖^{p-1} ≥ κ_{s2} |∇²Φ[d]²|`
  have hp2 : 2 ≤ p := hq.trans hqp
  have hstep : kappaS₂ P L p * |iteratedFDeriv ℝ 2 (Phi r ℓ) (x (k + 1)) (fun _ => d)| ≤
      ‖s k‖ ^ (p - 1) := by
    have := h18 hq d hd
    rw [le_div_iff₀ hK2] at this; linarith
  have hn : ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) := by push_cast; ring
  have hm : ((p : ℝ) - 1) = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hpow := Real.rpow_div_le_pow_of_le_pow (n := p + 1) (by positivity) (norm_nonneg _)
    (by omega) hstep
  rw [← hn, ← hm, Real.mul_rpow hK2.le (abs_nonneg _)] at hpow
  have hc := coef_nonneg (P := P) (p := p)
  rw [mul_assoc]
  refine hmul (le_trans ?_ d0)
  rw [kappa₂, mul_assoc]
  exact mul_le_mul_of_nonneg_left hpow hc

private theorem max_zero_neg_div {a t : ℝ} (ht : 0 ≤ t) : max 0 (-(a / t)) = max 0 (-a) / t := by
  rw [← max_div_div_right ht, zero_div, neg_div]

/-- **Lemma 5.1.2** ([cartis2022evaluation]): under Φ_ℓ.DpL (`ℓ > 0`), on a successful iteration
`k` of ARpLE before termination (`1 ≤ p`, `q ≤ p`), with `κ₁, κ₂, κ₃` of (4.1.32), (4.1.34),
(4.1.36) for `L = L_{Φ_ℓ,p}`:
(5.1.15) `‖r(x_k)‖^ℓ - ‖r(x_{k+1})‖^ℓ ≥`
`κ₁ ℓ ψ_{ℓ,1}(x_{k+1})^{(p+1)/p} ‖r(x_{k+1})‖^{(ℓ-1)(p+1)/p}`;
(5.1.16) if `q ≥ 2`, the same with `κ₂`, `max(0, -ψ_{ℓ,2}(x_{k+1}))` and the exponent
`(p+1)/(p-1)`;
(5.1.17) if `q = 3`, the same with `κ₃`, `ψ_{ℓ,3}(x_{k+1}, d)` and the exponent `(p+1)/(p-2)`, for
every `d ∈ 𝓜_{k+1}`;
(5.1.18) for every `d ∈ 𝓜_{k+1}` (`q ≥ 2`),
`ψ_{ℓ,2}(x_{k+1}, d) ‖r(x_{k+1})‖^{ℓ-1} ≤ ‖s_k‖^{p-1} / κ_{s2}`. -/
theorem lemma_5_1_2 {ℓ : ℝ} (hℓ : 0 < ℓ) (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ)
    (hΦ : AssumptionPhiDpL r ℓ p L) (hp : 1 ≤ p) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ j) (x j))
    (hs : P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k) :
    kappa₁ P L p * ℓ * psiOne r ℓ (x (k + 1)) ^ (((p : ℝ) + 1) / p) *
        ‖r (x (k + 1))‖ ^ ((ℓ - 1) * (((p : ℝ) + 1) / p)) ≤
      ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ ∧
    (2 ≤ q → kappa₂ P L p * ℓ *
        max 0 (-psiTwo r ℓ (x (k + 1))) ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) *
        ‖r (x (k + 1))‖ ^ ((ℓ - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1))) ≤
      ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ) ∧
    (3 ≤ q → ∀ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1), kappa₃ P L p * ℓ *
        psiThree r ℓ (x (k + 1)) d ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)) *
        ‖r (x (k + 1))‖ ^ ((ℓ - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 2))) ≤
      ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ) ∧
    (2 ≤ q → ∀ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1),
      psiTwoDir r ℓ (x (k + 1)) d * ‖r (x (k + 1))‖ ^ (ℓ - 1) ≤
        ‖s k‖ ^ (p - 1) / kappaS₂ P L p) := by
  obtain ⟨d1, d2, d3, d4, -⟩ := decrease_unscaled hℓ h hΦ hp hqp hk hs
  have hb := norm_nonneg (r (x (k + 1)))
  have hL := hΦ.nonneg
  have hν : ∀ j : ℕ, j < p → (0 : ℝ) < ((p : ℝ) + 1) / ((p : ℝ) - j) := fun j hj => by
    have : (j : ℝ) < p := by exact_mod_cast hj
    exact div_pos (by positivity) (by linarith)
  -- undo the scaling
  have key : ∀ κ ω ν : ℝ, 0 ≤ κ → 0 ≤ ω → 0 < ν →
      ℓ * κ * ω ^ ν ≤ ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ →
      κ * ℓ * (ω / ‖r (x (k + 1))‖ ^ (ℓ - 1)) ^ ν * ‖r (x (k + 1))‖ ^ ((ℓ - 1) * ν) ≤
        ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ := fun κ ω ν hκ hω hν' hdec => by
    refine le_trans ?_ hdec
    rw [mul_comm κ ℓ, mul_assoc (ℓ * κ)]
    exact mul_le_mul_of_nonneg_left (div_rpow_mul_le hω hb hν') (by positivity)
  refine ⟨?_, fun hq => ?_, fun hq d hd => ?_, fun hq d hd => ?_⟩
  · rw [psiOne_eq]
    have := hν 0 (by omega)
    simp only [Nat.cast_zero, sub_zero] at this
    exact key _ _ _ (kappa₁_nonneg hL) (norm_nonneg _) this d1
  · rw [psiTwo_eq, max_zero_neg_div (Real.rpow_nonneg hb _)]
    have := hν 1 (by omega)
    simp only [Nat.cast_one] at this
    exact key _ _ _ (kappa₂_nonneg hL) (le_max_left _ _) this (d2 hq)
  · have := hν 2 (by omega)
    simp only [Nat.cast_ofNat] at this
    exact key _ _ _ (kappa₃_nonneg hL) (abs_nonneg _) this (d3 hq d hd)
  · exact (div_mul_le_self (abs_nonneg _) (Real.rpow_nonneg hb _)).trans (d4 hq d hd)

end Decrease

/-- **Lemma 5.1.3** ([cartis2022evaluation], cascading differences): for `a ≥ b ≥ 0` and integers
`i ≥ 0`, `ℓ ≥ 1`, `a^{1/2^i} - b^{1/2^i} ≥ (a^ℓ - b^ℓ) / (2^i ℓ a^{(2^i-1)/2^i + ℓ - 1})` (both
sides vanish when `a = 0`, by Lean's convention `x / 0 = 0`). -/
theorem lemma_5_1_3 {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (i : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (a ^ ℓ - b ^ ℓ) / (2 ^ i * ℓ * a ^ (((2 : ℝ) ^ i - 1) / 2 ^ i + ℓ - 1)) ≤
      a ^ (1 / 2 ^ i : ℝ) - b ^ (1 / 2 ^ i : ℝ) :=
  rpow_inv_two_pow_sub_ge hb hba i hℓ

/-! ### Exponents -/

/-- The exponents `ι_j(p, ℓ, i) = (2^i - 1)/2^i - j (ℓ - 1)/(p - j + 1)` of
[cartis2022evaluation], (5.1.21) (`j = 1`), (5.1.23) (`j = 2`) and (5.1.25) (`j = 3`). -/
noncomputable def iota (j p : ℕ) (ℓ : ℝ) (i : ℕ) : ℝ :=
  ((2 : ℝ) ^ i - 1) / 2 ^ i - j * (ℓ - 1) / ((p : ℝ) - j + 1)

theorem iota_def (j p : ℕ) (ℓ : ℝ) (i : ℕ) :
    iota j p ℓ i = ((2 : ℝ) ^ i - 1) / 2 ^ i - j * (ℓ - 1) / ((p : ℝ) - j + 1) :=
  rfl

/-- `ι₁ = (2^i - 1)/2^i - (ℓ - 1)((p+1)/p - 1)`. -/
theorem iota_one_eq {p : ℕ} (hp : 1 ≤ p) (ℓ : ℝ) (i : ℕ) :
    iota 1 p ℓ i = ((2 : ℝ) ^ i - 1) / 2 ^ i - (ℓ - 1) * (((p : ℝ) + 1) / p - 1) := by
  have : (p : ℝ) ≠ 0 := by positivity
  rw [iota]; push_cast; rw [sub_add_cancel]; field_simp; ring

/-- `ι₂ = (2^i - 1)/2^i - (ℓ - 1)((p+1)/(p-1) - 1)`. -/
theorem iota_two_eq {p : ℕ} (hp : 2 ≤ p) (ℓ : ℝ) (i : ℕ) :
    iota 2 p ℓ i = ((2 : ℝ) ^ i - 1) / 2 ^ i - (ℓ - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1) - 1) := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) - 2 + 1 = (p : ℝ) - 1 := by ring
  rw [iota]; push_cast; rw [h2]; field_simp; ring

/-- `ι₃ = (2^i - 1)/2^i - (ℓ - 1)((p+1)/(p-2) - 1)`. -/
theorem iota_three_eq {p : ℕ} (hp : 3 ≤ p) (ℓ : ℝ) (i : ℕ) :
    iota 3 p ℓ i = ((2 : ℝ) ^ i - 1) / 2 ^ i - (ℓ - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 2) - 1) := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have : (p : ℝ) - 2 ≠ 0 := by linarith
  have h2 : (p : ℝ) - 3 + 1 = (p : ℝ) - 2 := by ring
  rw [iota]; push_cast; rw [h2]; field_simp; ring

/-- **(5.1.34)** ([cartis2022evaluation]): `ι₁ = ι₂ + (ℓ-1)(p+1)/(p(p-1))` (`p ≥ 2`). -/
theorem iota_one_eq_iota_two_add {p : ℕ} (hp : 2 ≤ p) (ℓ : ℝ) (i : ℕ) :
    iota 1 p ℓ i = iota 2 p ℓ i + (ℓ - 1) * (p + 1) / (p * (p - 1)) := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  have : (p : ℝ) ≠ 0 := by linarith
  rw [iota_one_eq (by omega), iota_two_eq hp]; field_simp; ring

/-- **(5.1.36)** ([cartis2022evaluation]): `ι₁ = ι₃ + 2(ℓ-1)(p+1)/(p(p-2))` (`p ≥ 3`). -/
theorem iota_one_eq_iota_three_add {p : ℕ} (hp : 3 ≤ p) (ℓ : ℝ) (i : ℕ) :
    iota 1 p ℓ i = iota 3 p ℓ i + 2 * (ℓ - 1) * (p + 1) / (p * (p - 2)) := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have : (p : ℝ) - 2 ≠ 0 := by linarith
  have : (p : ℝ) ≠ 0 := by linarith
  rw [iota_one_eq (by omega), iota_three_eq hp]; field_simp; ring

/-- **(5.1.37)** ([cartis2022evaluation]): `ι₂ = ι₃ + (ℓ-1)(p+1)/((p-1)(p-2))` (`p ≥ 3`). -/
theorem iota_two_eq_iota_three_add {p : ℕ} (hp : 3 ≤ p) (ℓ : ℝ) (i : ℕ) :
    iota 2 p ℓ i = iota 3 p ℓ i + (ℓ - 1) * (p + 1) / ((p - 1) * (p - 2)) := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have : (p : ℝ) - 2 ≠ 0 := by linarith
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [iota_two_eq (by omega), iota_three_eq hp]; field_simp; ring

/-! ### Lemma 5.1.4 -/

/-- The real-number core of (5.1.20), (5.1.22), (5.1.24) ([cartis2022evaluation], proof of
Lemma 5.1.4): let `ℓ ≥ 1`, `ν > 0`, `ι = (2^i - 1)/2^i - (ℓ - 1)(ν - 1)`, `β > 0`, `κ, ψ ≥ 0`,
`0 ≤ b ≤ a` with `b > β a`, and `a^ℓ - b^ℓ ≥ κ ℓ ψ^ν b^{(ℓ-1)ν}` (the form of Lemma 5.1.2). Then
`a^{1/2^i} - b^{1/2^i} ≥ κ β^{(ℓ-1)ν}/2^i ψ^ν / a^ι`. -/
theorem rpow_inv_two_pow_sub_ge_of_decrease {ℓ i : ℕ} (hℓ : 1 ≤ ℓ) {ν ι β κ ψ a b : ℝ}
    (hν : 0 < ν) (hι : ι = ((2 : ℝ) ^ i - 1) / 2 ^ i - ((ℓ : ℝ) - 1) * (ν - 1)) (hβ : 0 < β)
    (hκ : 0 ≤ κ) (hψ : 0 ≤ ψ) (hb : 0 ≤ b) (hba : b ≤ a) (hβab : β * a < b)
    (hdec : κ * ℓ * ψ ^ ν * b ^ (((ℓ : ℝ) - 1) * ν) ≤ a ^ (ℓ : ℝ) - b ^ (ℓ : ℝ)) :
    κ * β ^ (((ℓ : ℝ) - 1) * ν) / 2 ^ i * ψ ^ ν / a ^ ι ≤
      a ^ (1 / 2 ^ i : ℝ) - b ^ (1 / 2 ^ i : ℝ) := by
  have ha : 0 < a := by
    rcases (hb.trans hba).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hβab; linarith
  set e := ((ℓ : ℝ) - 1) * ν with he_def
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have he : 0 ≤ e := mul_nonneg (by linarith) hν.le
  have hcasc := rpow_inv_two_pow_sub_ge hb hba i hℓ
  have hsplit : ((2 : ℝ) ^ i - 1) / 2 ^ i + ℓ - 1 = e + ι := by rw [hι, he_def]; ring
  rw [hsplit, Real.rpow_add ha] at hcasc
  rw [Real.rpow_natCast, Real.rpow_natCast] at hdec
  have hbe : (β * a) ^ e ≤ b ^ e := Real.rpow_le_rpow (by positivity) hβab.le he
  rw [Real.mul_rpow hβ.le ha.le] at hbe
  have hAe : 0 < a ^ e := Real.rpow_pos_of_pos ha _
  have hAι : 0 < a ^ ι := Real.rpow_pos_of_pos ha _
  have hℓpos : (0 : ℝ) < ℓ := by linarith
  have hψν : 0 ≤ ψ ^ ν := Real.rpow_nonneg hψ _
  calc κ * β ^ e / 2 ^ i * ψ ^ ν / a ^ ι
      = κ * ℓ * ψ ^ ν * (β ^ e * a ^ e) / (2 ^ i * ℓ * (a ^ e * a ^ ι)) := by
        field_simp
    _ ≤ κ * ℓ * ψ ^ ν * b ^ e / (2 ^ i * ℓ * (a ^ e * a ^ ι)) := by gcongr
    _ ≤ (a ^ ℓ - b ^ ℓ) / (2 ^ i * ℓ * (a ^ e * a ^ ι)) := by gcongr
    _ ≤ _ := hcasc

/-- The real-number core of (5.1.27) ([cartis2022evaluation], Lemma 5.1.4): if `0 ≤ b ≤ a` and
`b ≤ β a` with `β ∈ [0, 1]`, then
`a^{1/2^i} - b^{1/2^i} ≥ (1 - β^{1/2^i}) a^{1/2^i} ≥ (1 - β^{1/2^i}) b^{1/2^i}`. -/
theorem rpow_inv_two_pow_sub_ge_of_le_mul {i : ℕ} {β a b : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hb : 0 ≤ b) (hba : b ≤ a) (h : b ≤ β * a) :
    (1 - β ^ (1 / 2 ^ i : ℝ)) * a ^ (1 / 2 ^ i : ℝ) ≤
        a ^ (1 / 2 ^ i : ℝ) - b ^ (1 / 2 ^ i : ℝ) ∧
      (1 - β ^ (1 / 2 ^ i : ℝ)) * b ^ (1 / 2 ^ i : ℝ) ≤
        (1 - β ^ (1 / 2 ^ i : ℝ)) * a ^ (1 / 2 ^ i : ℝ) := by
  set α : ℝ := 1 / 2 ^ i
  have hα : 0 < α := by positivity
  have ha : 0 ≤ a := hb.trans hba
  have hbα : b ^ α ≤ β ^ α * a ^ α := by
    rw [← Real.mul_rpow hβ ha]; exact Real.rpow_le_rpow hb h hα.le
  have hβα : β ^ α ≤ 1 := Real.rpow_le_one hβ hβ1 hα.le
  refine ⟨?_, mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb hba hα.le) (by linarith)⟩
  have : (1 - β ^ α) * a ^ α = a ^ α - β ^ α * a ^ α := by ring
  linarith

section Decrease

variable {r : ℝⁿ → ℝᵐ} {p q : ℕ} {P : ARpParams} {ε₀ ε₁ ε₂ ε₃ L : ℝ} {x s : ℕ → ℝⁿ}
  {σ : ℕ → ℝ}

/-- The decrease (5.1.57) of [cartis2022evaluation] in the scaled form of Lemma 5.1.2: for
`d ∈ 𝓜_{k+1}` (`q ≥ 2`),
`‖r(x_k)‖^ℓ - ‖r(x_{k+1})‖^ℓ ≥`
`κ₂ ℓ ψ_{ℓ,2}(x_{k+1}, d)^{(p+1)/(p-1)} ‖r(x_{k+1})‖^{(ℓ-1)(p+1)/(p-1)}`
(from (4.1.37) and (5.1.18)). -/
theorem decrease_psiTwoDir {ℓ : ℝ} (hℓ : 0 < ℓ) (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ)
    (hΦ : AssumptionPhiDpL r ℓ p L) (hp : 1 ≤ p) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ j) (x j))
    (hs : P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k) (hq : 2 ≤ q) {d : ℝⁿ}
    (hd : d ∈ mdir r ℓ p P ε₂ x s σ (k + 1)) :
    kappa₂ P L p * ℓ * psiTwoDir r ℓ (x (k + 1)) d ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) *
        ‖r (x (k + 1))‖ ^ ((ℓ - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1))) ≤
      ‖r (x k)‖ ^ ℓ - ‖r (x (k + 1))‖ ^ ℓ := by
  obtain ⟨-, -, -, -, d5⟩ := decrease_unscaled hℓ h hΦ hp hqp hk hs
  have hb := norm_nonneg (r (x (k + 1)))
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hq.trans hqp
  have hν : (0 : ℝ) < ((p : ℝ) + 1) / ((p : ℝ) - 1) := div_pos (by positivity) (by linarith)
  refine le_trans ?_ (d5 hq d hd)
  rw [mul_comm (kappa₂ P L p) ℓ, mul_assoc (ℓ * kappa₂ P L p)]
  exact mul_le_mul_of_nonneg_left (div_rpow_mul_le (abs_nonneg _) hb hν)
    (mul_nonneg hℓ.le (kappa₂_nonneg hΦ.nonneg))

/-- **Lemma 5.1.4** ([cartis2022evaluation]): under Φ_ℓ.DpL (`ℓ ≥ 1` an integer), on a
successful iteration `k` of ARpLE before termination (`1 ≤ p`, `q ≤ p`), for `β ∈ (0, 1)` and
every integer `i ≥ 0`, writing `a = ‖r(x_k)‖`, `b = ‖r(x_{k+1})‖`:
if `b > β a` (5.1.19), then (5.1.20)
`a^{1/2^i} - b^{1/2^i} ≥ κ_{r1} ψ_{ℓ,1}(x_{k+1})^{(p+1)/p} / a^{ι₁}`, (5.1.22) (`q ≥ 2`)
`a^{1/2^i} - b^{1/2^i} ≥ κ_{r2} max(0, -ψ_{ℓ,2}(x_{k+1}))^{(p+1)/(p-1)} / a^{ι₂}` and (5.1.24)
(`q = 3`) `a^{1/2^i} - b^{1/2^i} ≥ κ_{r3} ψ_{ℓ,3}(x_{k+1}, d)^{(p+1)/(p-2)} / a^{ι₃}` for every
`d ∈ 𝓜_{k+1}`, with `κ_{rj} = κ_j β^{(ℓ-1)(p+1)/(p-j+1)} / 2^i` ((5.1.21), (5.1.23), (5.1.25));
if `b ≤ β a` (5.1.26), then (5.1.27)
`a^{1/2^i} - b^{1/2^i} ≥ κ_{r0} a^{1/2^i} ≥ κ_{r0} b^{1/2^i}` with `κ_{r0} = 1 - β^{1/2^i}`
(5.1.28). -/
theorem lemma_5_1_4 {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ)
    (hΦ : AssumptionPhiDpL r ℓ p L) (hp : 1 ≤ p) (hqp : q ≤ p) {k : ℕ}
    (hk : ∀ j ≤ k, ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ j) (x j))
    (hs : P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (i : ℕ) :
    (β * ‖r (x k)‖ < ‖r (x (k + 1))‖ →
      kappa₁ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i *
          psiOne r ℓ (x (k + 1)) ^ (((p : ℝ) + 1) / p) / ‖r (x k)‖ ^ iota 1 p ℓ i ≤
        ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ) - ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ) ∧
      (2 ≤ q → kappa₂ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1))) / 2 ^ i *
          max 0 (-psiTwo r ℓ (x (k + 1))) ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) /
            ‖r (x k)‖ ^ iota 2 p ℓ i ≤
        ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ) - ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ)) ∧
      (3 ≤ q → ∀ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1),
        kappa₃ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 2))) / 2 ^ i *
          psiThree r ℓ (x (k + 1)) d ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)) /
            ‖r (x k)‖ ^ iota 3 p ℓ i ≤
        ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ) - ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ))) ∧
    (‖r (x (k + 1))‖ ≤ β * ‖r (x k)‖ →
      (1 - β ^ (1 / 2 ^ i : ℝ)) * ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ) ≤
          ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ) - ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ) ∧
        (1 - β ^ (1 / 2 ^ i : ℝ)) * ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ) ≤
          (1 - β ^ (1 / 2 ^ i : ℝ)) * ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ)) := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  obtain ⟨l1, l2, l3, -⟩ := lemma_5_1_2 hℓpos h hΦ hp hqp hk hs
  have hba := h.norm_succ_le hℓpos hk
  have hb := norm_nonneg (r (x (k + 1)))
  have hL := hΦ.nonneg
  refine ⟨fun hβab => ⟨?_, fun hq => ?_, fun hq d hd => ?_⟩,
    fun hβab => rpow_inv_two_pow_sub_ge_of_le_mul hβ0.le hβ1.le hb hba hβab⟩
  · exact rpow_inv_two_pow_sub_ge_of_decrease hℓ (by positivity) (iota_one_eq hp _ i) hβ0
      (kappa₁_nonneg hL) psiOne_nonneg hb hba hβab l1
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hq.trans hqp
    exact rpow_inv_two_pow_sub_ge_of_decrease hℓ (div_pos (by positivity) (by linarith))
      (iota_two_eq (hq.trans hqp) _ i) hβ0 (kappa₂_nonneg hL) (le_max_left _ _) hb hba hβab
      (l2 hq)
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hq.trans hqp
    exact rpow_inv_two_pow_sub_ge_of_decrease hℓ (div_pos (by positivity) (by linarith))
      (iota_three_eq (hq.trans hqp) _ i) hβ0 (kappa₃_nonneg hL) psiThree_nonneg hb hba hβab
      (l3 hq d hd)

/-! ### Theorem 5.1.7 -/

/-- `κ ε^ν / max(1, R^ι) ≤ κ ψ^ν / a^ι` for `0 ≤ ε ≤ ψ`, `ν, ι ≥ 0`, `0 < a ≤ R`. -/
private theorem div_max_le_div {κ ε ψ ν ι a R : ℝ} (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hεψ : ε ≤ ψ)
    (hν : 0 ≤ ν) (hι : 0 ≤ ι) (ha : 0 < a) (haR : a ≤ R) :
    κ * ε ^ ν / max 1 (R ^ ι) ≤ κ * ψ ^ ν / a ^ ι := by
  have h1 : a ^ ι ≤ max 1 (R ^ ι) := (Real.rpow_le_rpow ha.le haR hι).trans (le_max_right _ _)
  have h2 : ε ^ ν ≤ ψ ^ ν := Real.rpow_le_rpow hε hεψ hν
  have : 0 ≤ κ * ε ^ ν := mul_nonneg hκ (Real.rpow_nonneg hε _)
  exact div_le_div₀ (mul_nonneg hκ (Real.rpow_nonneg (hε.trans hεψ) _))
    (mul_le_mul_of_nonneg_left h2 hκ) (Real.rpow_pos_of_pos ha _) h1

/-- **Theorem 5.1.7, general form** ([cartis2022evaluation], Theorem 5.1.7 and the remark after
its proof): let `q ∈ {1, 2, 3}`, `q ≤ p`, `ℓ ≥ 1` and `i ≥ 0` integers with
`ι_j(p, ℓ, i) ≥ 0` for `j ∈ [1 : q]`, `β ∈ (0, 1)`, Φ_ℓ.DpL, `ε₀ > 0` and `ε₁, ε₂, ε₃ ≥ 0`. Let
`δ > 0` be a lower bound for the decreases (5.1.58)–(5.1.59) of the potential
`‖r(x_k)‖^{1/2^i}`: `δ ≤ κ_{r0} ε₀^{1/2^i}` and
`δ ≤ κ_{rj} ε_j^{(p+1)/(p-j+1)} / max(1, ‖r(x_0)‖^{ι_j})`
for `j ∈ [1 : q]`, with `κ_{rj}` of Lemma 5.1.4. Then every ARpLE run terminates at some `k_ε`
(the first index at which the test `ARpLEStop` holds) after at most
`A ‖r(x_0)‖^{1/2^i}/δ + κ^C` evaluations of `r` and `‖r(x_0)‖^{1/2^i}/δ + 2` evaluations of its
derivatives, with `A = 1 + |log γ₁|/log γ₂` (so that `κ^A = κ^S A` in the book's notation) and
`κ^C = (|log γ₁| + log(σ_max/σ₀))/log γ₂ + 2`, `σ_max = max(σ₀, γ₃ L/(1 - η₂))` ((5.1.60),
(5.1.61)). The book's choice `δ = min_j κ_{rj} · min_j ε_j^{…} / max(1, ‖r(x_0)‖^{ι₁}, …)` gives
Theorem 5.1.7 (`theorem_5_1_7`); `q = 1, 2` are the first- and second-order variants. (A positive
`δ` as above exists only if `σ_min > 0`: the `κ_{rj}` vanish when `σ_min = 0`.) -/
theorem theorem_5_1_7_of_iota_nonneg {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3)
    (hp : 1 ≤ p) (hqp : q ≤ p) (h : algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ)
    (hΦ : AssumptionPhiDpL r ℓ p L) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (i : ℕ)
    (hι : ∀ j, 1 ≤ j → j ≤ q → 0 ≤ iota j p ℓ i) (hε₀ : 0 < ε₀) (hε₁ : 0 ≤ ε₁)
    (hε₂ : 2 ≤ q → 0 ≤ ε₂) (hε₃ : 3 ≤ q → 0 ≤ ε₃) {δ : ℝ} (hδ : 0 < δ)
    (hδ₀ : δ ≤ (1 - β ^ (1 / 2 ^ i : ℝ)) * ε₀ ^ (1 / 2 ^ i : ℝ))
    (hδ₁ : δ ≤ kappa₁ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i *
      ε₁ ^ (((p : ℝ) + 1) / p) / max 1 (‖r (x 0)‖ ^ iota 1 p ℓ i))
    (hδ₂ : 2 ≤ q → δ ≤ kappa₂ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1))) /
      2 ^ i * ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1)) / max 1 (‖r (x 0)‖ ^ iota 2 p ℓ i))
    (hδ₃ : 3 ≤ q → δ ≤ kappa₃ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 2))) /
      2 ^ i * ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)) / max 1 (‖r (x 0)‖ ^ iota 3 p ℓ i)) :
    ∃ kε, IsFirstHit (fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          (‖r (x 0)‖ ^ (1 / 2 ^ i : ℝ) / δ) +
        ((|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams L / P.σ₀)) / Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k) kε : ℝ) ≤
        ‖r (x 0)‖ ^ (1 / 2 ^ i : ℝ) / δ + 2 := by
  set test := fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k) with htest
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hL := hΦ.nonneg
  have hα : (0 : ℝ) < 1 / 2 ^ i := by positivity
  have hdec : ∀ k, (∀ j ≤ k + 1, ¬ IsARRun.Stop test (fun _ => False) j) →
      P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k →
      δ ≤ ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ) - ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ) := by
    intro k hk hs
    have hk' : ∀ j ≤ k + 1, ¬ test j := fun j hj h' => hk j hj (Or.inl h')
    have hkk : ∀ j ≤ k, ¬ test j := fun j hj => hk' j (hj.trans k.le_succ)
    have hba := h.norm_succ_le hℓpos hkk
    have haR := h.norm_le_norm_zero hℓpos k fun j hj => hkk j hj.le
    -- the test fails at `x_{k+1}`
    have hnot := hk' (k + 1) le_rfl
    have hb0 : ε₀ < ‖r (x (k + 1))‖ := lt_of_not_ge fun hle => hnot (Or.inl hle)
    have hbpos : 0 < ‖r (x (k + 1))‖ := hε₀.trans hb0
    obtain ⟨L4a, L4b⟩ := lemma_5_1_4 hℓ h hΦ hp hqp hkk hs hβ0 hβ1 i
    rcases le_or_gt ‖r (x (k + 1))‖ (β * ‖r (x k)‖) with hβab | hβab
    · obtain ⟨c1, c2⟩ := L4b hβab
      have hκ0 : 0 ≤ 1 - β ^ (1 / 2 ^ i : ℝ) := by
        have := Real.rpow_le_one hβ0.le hβ1.le hα.le; linarith
      have : ε₀ ^ (1 / 2 ^ i : ℝ) ≤ ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ) :=
        Real.rpow_le_rpow hε₀.le hb0.le hα.le
      calc δ ≤ (1 - β ^ (1 / 2 ^ i : ℝ)) * ε₀ ^ (1 / 2 ^ i : ℝ) := hδ₀
        _ ≤ (1 - β ^ (1 / 2 ^ i : ℝ)) * ‖r (x (k + 1))‖ ^ (1 / 2 ^ i : ℝ) := by gcongr
        _ ≤ _ := c2.trans c1
    obtain ⟨A1, A2, A3⟩ := L4a hβab
    have ha : 0 < ‖r (x k)‖ := hbpos.trans_le hba
    -- which part of the test fails at `x_{k+1}`
    have hcase : ε₁ < psiOne r ℓ (x (k + 1)) ∨ (2 ≤ q ∧ psiTwo r ℓ (x (k + 1)) < -ε₂) ∨
        (3 ≤ q ∧ ∃ d ∈ mdir r ℓ p P ε₂ x s σ (k + 1),
          ε₃ < psiThree r ℓ (x (k + 1)) d ∨ ε₂ < psiTwoDir r ℓ (x (k + 1)) d) := by
      by_contra hc
      simp only [not_or, not_and, not_lt, not_exists] at hc
      obtain ⟨c1, c2, c3⟩ := hc
      apply hnot
      simp only [htest, ARpLEStop]
      interval_cases q
      · exact Or.inr (Or.inl ⟨rfl, c1⟩)
      · rcases le_or_gt (psiTwo r ℓ (x (k + 1))) ε₂ with h2 | h2
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, c1, c2 le_rfl⟩)))
        · exact Or.inr (Or.inr (Or.inl ⟨le_rfl, c1, h2⟩))
      · rcases le_or_gt (psiTwo r ℓ (x (k + 1))) ε₂ with h2 | h2
        · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, c1, c2 (by norm_num), fun d hd => ?_⟩)))
          exact c3 (le_refl 3) d hd
        · exact Or.inr (Or.inr (Or.inl ⟨by norm_num, c1, h2⟩))
    have hνpos : ∀ j : ℕ, j < p → (0 : ℝ) < ((p : ℝ) + 1) / ((p : ℝ) - j) := fun j hj => by
      have : (j : ℝ) < p := by exact_mod_cast hj
      exact div_pos (by positivity) (by linarith)
    rcases hcase with h1 | ⟨hq, h2⟩ | ⟨hq, d, hd, h3 | h3⟩
    · have := hνpos 0 (by omega)
      simp only [Nat.cast_zero, sub_zero] at this
      refine hδ₁.trans ((div_max_le_div ?_ hε₁ h1.le this.le (hι 1 le_rfl hq1) ha haR).trans A1)
      have := kappa₁_nonneg (P := P) (p := p) hL; positivity
    · have := hνpos 1 (by omega)
      simp only [Nat.cast_one] at this
      refine (hδ₂ hq).trans ((div_max_le_div ?_ (hε₂ hq) (le_max_of_le_right (by linarith))
        this.le (hι 2 (by norm_num) hq) ha haR).trans (A2 hq))
      have := kappa₂_nonneg (P := P) (p := p) hL; positivity
    · have := hνpos 2 (by omega)
      simp only [Nat.cast_ofNat] at this
      refine (hδ₃ hq).trans ((div_max_le_div ?_ (hε₃ hq) h3.le this.le (hι 3 (by norm_num) hq) ha
        haR).trans (A3 hq d hd))
      have := kappa₃_nonneg (P := P) (p := p) hL; positivity
    · have hq2 : 2 ≤ q := by omega
      have := hνpos 1 (by omega)
      simp only [Nat.cast_one] at this
      have hdec := decrease_psiTwoDir hℓpos h hΦ hp hqp hkk hs hq2 hd
      have A4 := rpow_inv_two_pow_sub_ge_of_decrease hℓ this (iota_two_eq (hq2.trans hqp) _ i)
        hβ0 (kappa₂_nonneg hL) psiTwoDir_nonneg hbpos.le hba hβab hdec
      refine (hδ₂ hq2).trans ((div_max_le_div ?_ (hε₂ hq2) h3.le this.le (hι 2 (by norm_num) hq2)
        ha haR).trans A4)
      have := kappa₂_nonneg (P := P) (p := p) hL; positivity
  obtain ⟨kε, hfirst, hF, hD⟩ := h.isARpRun.toIsARRun.exists_isFirstHit_of_decrease
    (σmax := arSigmaMax P.toARParams L)
    (fun k hk => (h.isARpRun.sigma_le hΦ.contDiff hΦ.lipschitz (k := k)
      fun j hj h' => hk j hj (Or.inl h')).2)
    (V := fun k => ‖r (x k)‖ ^ (1 / 2 ^ i : ℝ)) (Vlow := 0) hδ
    (fun k hk => Real.rpow_le_rpow (norm_nonneg _)
      (h.norm_succ_le hℓpos fun j hj h' => hk j hj (Or.inl h')) hα.le)
    (fun k _ => by positivity) hdec
  refine ⟨kε, IsARRun.isFirstHit_stop_iff.1 hfirst, ?_, ?_⟩
  · simpa using hF
  · simpa using hD

end Decrease

/-! ### The choice of `ℓ` and `i` -/

/-- Odd factorizations are unique: `o 2^i = o' 2^j` with `o, o'` odd forces `o = o'`, `i = j`. -/
theorem eq_of_odd_mul_two_pow_eq {o o' i j : ℕ} (ho : Odd o) (ho' : Odd o')
    (h : o * 2 ^ i = o' * 2 ^ j) : o = o' ∧ i = j := by
  wlog hij : i ≤ j generalizing o o' i j with H
  · obtain ⟨h1, h2⟩ := H ho' ho h.symm (le_of_not_ge hij)
    exact ⟨h1.symm, h2.symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have h'' : o * 2 ^ i = (o' * 2 ^ d) * 2 ^ i := by rw [h, pow_add]; ring
  have h' : o = o' * 2 ^ d := Nat.eq_of_mul_eq_mul_right (by positivity) h''
  cases d with
  | zero => simpa using h'
  | succ d =>
    exfalso
    have : Even o := h' ▸ Nat.even_mul.2 (Or.inr (Nat.even_pow.2 ⟨even_two, by omega⟩))
    exact (Nat.not_even_iff_odd.2 ho) this

/-- **Lemma 5.1.5** ([cartis2022evaluation], odd factorization): every natural number `p ≠ 0` is
uniquely `p = o 2^i` with `o` odd. (The book writes `p ∈ ℕ`; `p = 0` must be excluded.) -/
theorem lemma_5_1_5 {p : ℕ} (hp : p ≠ 0) : ∃! oi : ℕ × ℕ, Odd oi.1 ∧ p = oi.1 * 2 ^ oi.2 := by
  obtain ⟨i, o, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hp
  refine ⟨(o, i), ⟨ho, mul_comm _ _⟩, ?_⟩
  rintro ⟨o', i'⟩ ⟨ho', h⟩
  simp only at ho' h
  obtain ⟨h1, h2⟩ := eq_of_odd_mul_two_pow_eq ho' ho (by rw [← h, mul_comm])
  rw [h1, h2]

theorem iota_one_eq' {p : ℕ} (ℓ : ℝ) (i : ℕ) :
    iota 1 p ℓ i = ((2 : ℝ) ^ i - 1) / 2 ^ i - (ℓ - 1) / p := by
  rw [iota]; push_cast; rw [sub_add_cancel, one_mul]

theorem iota_two_eq' {p : ℕ} (ℓ : ℝ) (i : ℕ) :
    iota 2 p ℓ i = ((2 : ℝ) ^ i - 1) / 2 ^ i - 2 * (ℓ - 1) / ((p : ℝ) - 1) := by
  rw [iota]; push_cast; rw [show (p : ℝ) - 2 + 1 = p - 1 by ring]

theorem iota_three_eq' {p : ℕ} (ℓ : ℝ) (i : ℕ) :
    iota 3 p ℓ i = ((2 : ℝ) ^ i - 1) / 2 ^ i - 3 * (ℓ - 1) / ((p : ℝ) - 2) := by
  rw [iota]; push_cast; rw [show (p : ℝ) - 3 + 1 = p - 2 by ring]

/-- `(2^i - 1)/2^i - a/b > 0` iff `a 2^i < (2^i - 1) b` (for `b > 0`). -/
private theorem iota_pos_iff {i : ℕ} {a b : ℝ} (hb : 0 < b) :
    0 < ((2 : ℝ) ^ i - 1) / 2 ^ i - a / b ↔ a * 2 ^ i < (2 ^ i - 1) * b := by
  rw [sub_pos, div_lt_div_iff₀ hb (by positivity)]

/-- `∑_{k < j} 4^k` times `3` is `4^j - 1`. -/
private theorem three_mul_sum_four_pow (j : ℕ) : 3 * ∑ k ∈ Finset.range j, 4 ^ k + 1 = 4 ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- **Lemma 5.1.6** ([cartis2022evaluation], good exponents), `p ≥ 1`, with `ι_j = iota j p ℓ i`:
* (5.1.38) if `ℓ = p` and `p < 2^i` (`i > log₂ p`), then `ι₁ > 0`;
* (5.1.39) if `p` is even, `p = o 2^i` with `o` odd and `ℓ = 1 + o (2^i - 1)`, then `ι₁ = 0` and
  `ℓ > 1`;
* (5.1.40) if `p` is even, `ℓ = p/2` and `p - 1 < 2^i`, then `ι₁ > 0` and `ι₂ > 0`;
* (5.1.41) if `4 ∣ p - 1`, `p - 1 = o₂ 2^{i+1}` with `o₂` odd and `ℓ = 1 + o₂ (2^i - 1)`, then
  `ι₂ = 0`, `ι₁ > 0` and `ℓ > 1`;
* (5.1.42) if `ℓ = p/3` (`3 ∣ p`) and `p - 2 < 2^i`, then `ι₁, ι₂, ι₃ > 0`;
* (5.1.43) if `p - 2 = o₃ 2^i` with `o₃` odd, `i ≥ 2` even and `ℓ = 1 + o₃ ∑_{k<i/2} 4^k`, then
  `ι₃ = 0`, `ι₁, ι₂ > 0`, `ℓ > 1` and `ℓ` is even. -/
theorem lemma_5_1_6 {p : ℕ} (hp : 1 ≤ p) :
    (∀ ℓ i : ℕ, ℓ = p → p < 2 ^ i → 0 < iota 1 p ℓ i) ∧
    (∀ ℓ o i : ℕ, Even p → Odd o → p = o * 2 ^ i → ℓ = 1 + o * (2 ^ i - 1) →
      iota 1 p ℓ i = 0 ∧ 1 < ℓ) ∧
    (∀ ℓ i : ℕ, Even p → 2 * ℓ = p → p - 1 < 2 ^ i → 0 < iota 1 p ℓ i ∧ 0 < iota 2 p ℓ i) ∧
    (∀ ℓ o₂ i : ℕ, 4 ∣ p - 1 → Odd o₂ → p - 1 = o₂ * 2 ^ (i + 1) → ℓ = 1 + o₂ * (2 ^ i - 1) →
      iota 2 p ℓ i = 0 ∧ 0 < iota 1 p ℓ i ∧ 1 < ℓ) ∧
    (∀ ℓ i : ℕ, 3 * ℓ = p → p - 2 < 2 ^ i →
      0 < iota 1 p ℓ i ∧ 0 < iota 2 p ℓ i ∧ 0 < iota 3 p ℓ i) ∧
    (∀ ℓ o₃ i : ℕ, Odd o₃ → p - 2 = o₃ * 2 ^ i → 2 ≤ i → Even i →
      ℓ = 1 + o₃ * ∑ k ∈ Finset.range (i / 2), 4 ^ k →
      iota 3 p ℓ i = 0 ∧ 0 < iota 1 p ℓ i ∧ 0 < iota 2 p ℓ i ∧ 1 < ℓ ∧ Even ℓ) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h2i : ∀ i : ℕ, (0 : ℝ) < 2 ^ i := fun i => by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (5.1.38)
    intro ℓ i hℓp hi
    rw [hℓp]
    have hi' : (p : ℝ) < 2 ^ i := by exact_mod_cast hi
    rw [iota_one_eq', iota_pos_iff (by linarith)]
    nlinarith
  · -- (5.1.39)
    rintro ℓ o i hpe ho rfl rfl
    have hi : i ≠ 0 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 (by simpa using ho)) hpe
    have h2 : 2 ≤ 2 ^ i := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hi)
    have ho1 : 1 ≤ o := ho.pos
    have hm := Nat.mul_le_mul ho1 (show 1 ≤ 2 ^ i - 1 by omega)
    refine ⟨?_, by omega⟩
    rw [iota_one_eq']
    have ho0 : (o : ℝ) ≠ 0 := by positivity
    push_cast [Nat.cast_sub (Nat.one_le_two_pow)]
    field_simp
    ring
  · -- (5.1.40)
    rintro ℓ i hpe rfl hi
    have hℓ : 1 ≤ ℓ := by omega
    have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have hi' : (2 * (ℓ : ℝ)) - 1 < 2 ^ i := by
      have : ((2 * ℓ - 1 : ℕ) : ℝ) < 2 ^ i := by exact_mod_cast hi
      push_cast [Nat.cast_sub (show 1 ≤ 2 * ℓ by omega)] at this
      exact this
    have h2 : 0 < iota 2 (2 * ℓ) ℓ i := by
      rw [iota_two_eq', iota_pos_iff (by push_cast; linarith)]
      push_cast
      nlinarith
    refine ⟨?_, h2⟩
    rcases (Nat.lt_or_ge 1 (2 * ℓ)) with hp2 | hp2
    · rw [iota_one_eq_iota_two_add (by omega)]
      have : 0 ≤ ((ℓ : ℝ) - 1) * ((2 * ℓ : ℕ) + 1) / ((2 * ℓ : ℕ) * ((2 * ℓ : ℕ) - 1)) := by
        push_cast
        apply div_nonneg (mul_nonneg (by linarith) (by positivity))
        nlinarith
      linarith
    · omega
  · -- (5.1.41)
    rintro ℓ o₂ i h4 ho hp1 rfl
    have hi : i ≠ 0 := by
      rintro rfl
      rw [hp1] at h4
      obtain ⟨c, hc⟩ := h4
      have : Even o₂ := ⟨c, by omega⟩
      exact (Nat.not_even_iff_odd.2 ho) this
    have h2 : 2 ≤ 2 ^ i := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hi)
    have ho1 : 1 ≤ o₂ := ho.pos
    have hm := Nat.mul_le_mul ho1 (show 1 ≤ 2 ^ i - 1 by omega)
    have hℓ1 : 1 < 1 + o₂ * (2 ^ i - 1) := by omega
    have hpR' : (p : ℝ) - 1 = o₂ * 2 ^ (i + 1) := by
      have : ((p - 1 : ℕ) : ℝ) = ((o₂ * 2 ^ (i + 1) : ℕ) : ℝ) := by rw [hp1]
      push_cast [Nat.cast_sub hp] at this
      exact this
    have hι2 : iota 2 p ((1 + o₂ * (2 ^ i - 1) : ℕ) : ℝ) i = 0 := by
      rw [iota_two_eq', hpR']
      have ho0 : (o₂ : ℝ) ≠ 0 := by positivity
      push_cast [Nat.cast_sub (Nat.one_le_two_pow)]
      field_simp
      ring
    refine ⟨hι2, ?_, hℓ1⟩
    have hp5 : 2 ≤ p := by
      have : 4 ≤ o₂ * 2 ^ (i + 1) := by
        calc 4 = 1 * 2 ^ 2 := rfl
          _ ≤ o₂ * 2 ^ (i + 1) := Nat.mul_le_mul ho1 (Nat.pow_le_pow_right (by norm_num)
            (by omega))
      omega
    rw [iota_one_eq_iota_two_add hp5, hι2, zero_add]
    have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp5
    have hℓR : (1 : ℝ) < ((1 + o₂ * (2 ^ i - 1) : ℕ) : ℝ) := by exact_mod_cast hℓ1
    apply div_pos (mul_pos (by linarith) (by positivity))
    nlinarith
  · -- (5.1.42)
    rintro ℓ i rfl hi
    have hℓ : 1 ≤ ℓ := by omega
    have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have hi' : (3 * (ℓ : ℝ)) - 2 < 2 ^ i := by
      have : ((3 * ℓ - 2 : ℕ) : ℝ) < 2 ^ i := by exact_mod_cast hi
      push_cast [Nat.cast_sub (show 2 ≤ 3 * ℓ by omega)] at this
      exact this
    have h3 : 0 < iota 3 (3 * ℓ) ℓ i := by
      rw [iota_three_eq', iota_pos_iff (by push_cast; linarith)]
      push_cast
      nlinarith
    have hpp : 3 ≤ 3 * ℓ := by omega
    have hpR3 : (3 : ℝ) ≤ ((3 * ℓ : ℕ) : ℝ) := by exact_mod_cast hpp
    refine ⟨?_, ?_, h3⟩
    · rw [iota_one_eq_iota_three_add hpp]
      have : 0 ≤ 2 * ((ℓ : ℝ) - 1) * ((3 * ℓ : ℕ) + 1) / ((3 * ℓ : ℕ) * ((3 * ℓ : ℕ) - 2)) := by
        apply div_nonneg (mul_nonneg (by linarith) (by positivity))
        nlinarith
      linarith
    · rw [iota_two_eq_iota_three_add hpp]
      have : 0 ≤ ((ℓ : ℝ) - 1) * ((3 * ℓ : ℕ) + 1) / (((3 * ℓ : ℕ) - 1) * ((3 * ℓ : ℕ) - 2)) := by
        apply div_nonneg (mul_nonneg (by linarith) (by positivity))
        nlinarith
      linarith
  · -- (5.1.43)
    rintro ℓ o₃ i ho hp2 hi he rfl
    obtain ⟨j, rfl⟩ := he
    have hj : (j + j) / 2 = j := by omega
    rw [hj]
    have hj1 : 1 ≤ j := by omega
    set S := ∑ k ∈ Finset.range j, 4 ^ k with hS
    have h3S := three_mul_sum_four_pow j
    rw [← hS] at h3S
    have h4 : (4 : ℕ) ^ j = 2 ^ (j + j) := by rw [← two_mul, pow_mul]; norm_num
    have hS1 : 1 ≤ S := by
      have : 4 ≤ 4 ^ j := by
        calc 4 = 4 ^ 1 := rfl
          _ ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
      omega
    have ho1 : 1 ≤ o₃ := ho.pos
    have hℓ1 : 1 < 1 + o₃ * S := by nlinarith
    have hSodd : Odd S := by
      have : Odd (3 * S) := by
        have he4 : Even (4 ^ j) := Nat.even_pow.2 ⟨by decide, by omega⟩
        obtain ⟨c, hc⟩ := he4
        exact ⟨c - 1, by omega⟩
      exact (Nat.odd_mul.1 this).2
    have hpR' : (p : ℝ) - 2 = o₃ * 2 ^ (j + j) := by
      have hp6 : 2 ≤ p := by
        have : 1 ≤ o₃ * 2 ^ (j + j) := Nat.one_le_iff_ne_zero.2 (by positivity)
        omega
      have : ((p - 2 : ℕ) : ℝ) = ((o₃ * 2 ^ (j + j) : ℕ) : ℝ) := by rw [hp2]
      push_cast [Nat.cast_sub hp6] at this
      exact this
    have h3SR : (3 : ℝ) * S = 2 ^ (j + j) - 1 := by
      have : ((3 * S + 1 : ℕ) : ℝ) = ((2 ^ (j + j) : ℕ) : ℝ) := by rw [h3S, h4]
      push_cast at this
      linarith
    have hι3 : iota 3 p ((1 + o₃ * S : ℕ) : ℝ) (j + j) = 0 := by
      rw [iota_three_eq', hpR']
      have ho0 : (o₃ : ℝ) ≠ 0 := by positivity
      push_cast
      rw [show (1 : ℝ) + o₃ * S - 1 = o₃ * S by ring, show 3 * (o₃ * (S : ℝ)) = o₃ * (3 * S) by
        ring, h3SR]
      field_simp
      ring
    have hp3 : 3 ≤ p := by
      have : 4 ≤ o₃ * 2 ^ (j + j) := by
        calc 4 = 1 * 2 ^ 2 := rfl
          _ ≤ o₃ * 2 ^ (j + j) := Nat.mul_le_mul ho1 (Nat.pow_le_pow_right (by norm_num)
            (by omega))
      omega
    have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hℓR : (1 : ℝ) < ((1 + o₃ * S : ℕ) : ℝ) := by exact_mod_cast hℓ1
    refine ⟨hι3, ?_, ?_, hℓ1, ?_⟩
    · rw [iota_one_eq_iota_three_add hp3, hι3, zero_add]
      apply div_pos (mul_pos (by linarith) (by positivity))
      nlinarith
    · rw [iota_two_eq_iota_three_add hp3, hι3, zero_add]
      apply div_pos (mul_pos (by linarith) (by positivity))
      nlinarith
    · obtain ⟨c, hc⟩ := Nat.odd_mul.2 ⟨ho, hSodd⟩
      exact ⟨c + 1, by omega⟩

section Theorem517

variable {r : ℝⁿ → ℝᵐ} {p : ℕ} {P : ARpParams} {ε₀ ε₁ ε₂ ε₃ L : ℝ} {x s : ℕ → ℝⁿ}
  {σ : ℕ → ℝ}

/-- `e / (K M) ≤ k E / m` from `0 ≤ e ≤ E`, `1/k ≤ K` (`k > 0`) and `0 < m ≤ M`. -/
private theorem div_mul_le_mul_div {e E K k M m : ℝ} (he : 0 ≤ e) (heE : e ≤ E) (hk : 0 < k)
    (hK : 1 / k ≤ K) (hm : 0 < m) (hmM : m ≤ M) : e / (K * M) ≤ k * E / m := by
  have hK0 : 0 < K := (one_div_pos.2 hk).trans_le hK
  have hM0 : 0 < M := hm.trans_le hmM
  have h1 : 1 / K ≤ k := by rw [div_le_iff₀ hK0]; rw [div_le_iff₀ hk] at hK; linarith
  calc e / (K * M) = e * (1 / K) * (1 / M) := by field_simp
    _ ≤ E * k * (1 / m) :=
        mul_le_mul (mul_le_mul heE h1 (by positivity) (he.trans heE))
          (one_div_le_one_div_of_le hm hmM) (by positivity) (by have := he.trans heE; positivity)
    _ = k * E / m := by ring

/-- **Theorem 5.1.7** ([cartis2022evaluation]): suppose that `i ≥ 0` and the integer `ℓ > 1`
satisfy (5.1.42) or (5.1.43) for `p`, that Φ_ℓ.DpL holds, `σ_min > 0` and `β ∈ (0, 1)`. Then for
all `ε₀, ε₁, ε₂, ε₃ > 0`, every run of ARpLE (`q = 3`) terminates at some `k_ε` (the first index
at which `ARpLEStop` holds: `‖r(x_ε)‖ ≤ ε₀`, or `ψ_{ℓ,1}(x_ε) ≤ ε₁` together with
`ψ_{ℓ,2}(x_ε) > ε₂`, or with `ψ_{ℓ,2}(x_ε) ≥ -ε₂` and `ψ_{ℓ,3}(x_ε, d) ≤ ε₃`,
`ψ_{ℓ,2}(x_ε, d) ≤ ε₂` for all `d ∈ 𝓜_ε`, so that `𝓜_ε ⊆ 𝒵_ε`) after at most
`κ^A max[‖r_0‖^{1/2^i}, ‖r_0‖^{1-(ℓ-1)/p}, ‖r_0‖^{1-2(ℓ-1)/(p-1)}, ‖r_0‖^{1-3(ℓ-1)/(p-2)}] /
min[ε₀^{1/2^i}, ε₁^{(p+1)/p}, ε₂^{(p+1)/(p-1)}, ε₃^{(p+1)/(p-2)}] + κ^C` evaluations of `r`
(5.1.44) and `κ^S (same ratio) + 2` evaluations of its derivatives (5.1.45), where
`κ^S = max(1/κ_{r0}, 1/κ_{r1}, 1/κ_{r2}, 1/κ_{r3})` with the constants of Lemma 5.1.4,
`κ^A = κ^S (1 + |log γ₁|/log γ₂)` and `κ^C = (|log γ₁| + log(σ_max/σ₀))/log γ₂ + 2`
((5.1.60)–(5.1.61)). -/
theorem theorem_5_1_7 {ℓ i : ℕ} (hℓ : 1 < ℓ)
    (hpi : (3 * ℓ = p ∧ p - 2 < 2 ^ i) ∨
      (∃ o₃ : ℕ, Odd o₃ ∧ p - 2 = o₃ * 2 ^ i ∧ 2 ≤ i ∧ Even i ∧
        ℓ = 1 + o₃ * ∑ k ∈ Finset.range (i / 2), 4 ^ k))
    (h : algorithm_5_1_1 r ℓ p P 3 ε₀ ε₁ ε₂ ε₃ x s σ) (hΦ : AssumptionPhiDpL r ℓ p L)
    (hσ : 0 < P.σmin) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hε₃ : 0 < ε₃) :
    ∃ kε, IsFirstHit (fun k => ARpLEStop r ℓ 3 ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k)) kε ∧
      (funEvalCount kε : ℝ) ≤
        max (max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (1 / (kappa₁ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i)))
          (max (1 / (kappa₂ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1))) / 2 ^ i))
            (1 / (kappa₃ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 2))) / 2 ^ i))) *
          (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
          max (max (‖r (x 0)‖ ^ (1 / 2 ^ i : ℝ)) (‖r (x 0)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)))
            (max (‖r (x 0)‖ ^ (1 - 2 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 1)))
              (‖r (x 0)‖ ^ (1 - 3 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 2)))) /
          min (min (ε₀ ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)))
            (min (ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))) (ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)))) +
        ((|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams L / P.σ₀)) / Real.log P.γ₂ + 2) ∧
      (derivEvalCount (fun k => P.η₁ ≤ taylorRatio (Phi r ℓ) p x s k) kε : ℝ) ≤
        max (max (1 / (1 - β ^ (1 / 2 ^ i : ℝ)))
            (1 / (kappa₁ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i)))
          (max (1 / (kappa₂ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1))) / 2 ^ i))
            (1 / (kappa₃ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 2))) / 2 ^ i))) *
          max (max (‖r (x 0)‖ ^ (1 / 2 ^ i : ℝ)) (‖r (x 0)‖ ^ (1 - ((ℓ : ℝ) - 1) / p)))
            (max (‖r (x 0)‖ ^ (1 - 2 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 1)))
              (‖r (x 0)‖ ^ (1 - 3 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 2)))) /
          min (min (ε₀ ^ (1 / 2 ^ i : ℝ)) (ε₁ ^ (((p : ℝ) + 1) / p)))
            (min (ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))) (ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2)))) +
        2 := by
  -- `p ≥ 3` and the exponents are nonnegative (Lemma 5.1.6)
  have hp3 : 3 ≤ p := by
    rcases hpi with ⟨h3, -⟩ | ⟨o₃, ho, hp2, hi, -, -⟩
    · omega
    · have : 4 ≤ o₃ * 2 ^ i := by
        calc 4 = 1 * 2 ^ 2 := rfl
          _ ≤ o₃ * 2 ^ i := Nat.mul_le_mul ho.pos (Nat.pow_le_pow_right (by norm_num) hi)
      omega
  have hp1 : 1 ≤ p := by omega
  obtain ⟨-, -, -, -, h42, h43⟩ := lemma_5_1_6 hp1
  have hι : ∀ j, 1 ≤ j → j ≤ 3 → 0 ≤ iota j p ℓ i := by
    have hpos : 0 ≤ iota 1 p ℓ i ∧ 0 ≤ iota 2 p ℓ i ∧ 0 ≤ iota 3 p ℓ i := by
      rcases hpi with ⟨h3, h2⟩ | ⟨o₃, ho, hp2, hi, he, hℓe⟩
      · obtain ⟨h1, h2, h3⟩ := h42 ℓ i h3 h2
        exact ⟨h1.le, h2.le, h3.le⟩
      · obtain ⟨h1, h2, h3, -⟩ := h43 ℓ o₃ i ho hp2 hi he hℓe
        exact ⟨h2.le, h3.le, h1.ge⟩
    intro j hj1 hj3
    interval_cases j
    · exact hpos.1
    · exact hpos.2.1
    · exact hpos.2.2
  have hL := hΦ.nonneg
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.le
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  set α : ℝ := 1 / 2 ^ i with hαdef
  have hα : 0 < α := by positivity
  set R := ‖r (x 0)‖ with hRdef
  have hR0 : 0 ≤ R := norm_nonneg _
  set κr0 := 1 - β ^ α with hκr0def
  set κr1 := kappa₁ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / p)) / 2 ^ i
  set κr2 := kappa₂ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1))) / 2 ^ i
  set κr3 := kappa₃ P L p * β ^ (((ℓ : ℝ) - 1) * (((p : ℝ) + 1) / ((p : ℝ) - 2))) / 2 ^ i
  have hκr0 : 0 < κr0 := by have := Real.rpow_lt_one hβ0.le hβ1 hα; linarith
  have hκr1 : 0 < κr1 := by have := kappa₁_pos (P := P) (p := p) hL hσ; positivity
  have hκr2 : 0 < κr2 := by have := kappa₂_pos (P := P) (p := p) hL hσ; positivity
  have hκr3 : 0 < κr3 := by have := kappa₃_pos (P := P) (p := p) hL hσ; positivity
  set κS := max (max (1 / κr0) (1 / κr1)) (max (1 / κr2) (1 / κr3)) with hκS
  set εmin := min (min (ε₀ ^ α) (ε₁ ^ (((p : ℝ) + 1) / p)))
    (min (ε₂ ^ (((p : ℝ) + 1) / ((p : ℝ) - 1))) (ε₃ ^ (((p : ℝ) + 1) / ((p : ℝ) - 2))))
    with hεmin_def
  have hεmin : 0 < εmin := by positivity
  set M1 := max (max 1 (R ^ iota 1 p ℓ i)) (max (R ^ iota 2 p ℓ i) (R ^ iota 3 p ℓ i)) with hM1
  have hM1one : 1 ≤ M1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hS0 : 1 / κr0 ≤ κS := le_trans (le_max_left _ _) (le_max_left _ _)
  have hS1 : 1 / κr1 ≤ κS := le_trans (le_max_right _ _) (le_max_left _ _)
  have hS2 : 1 / κr2 ≤ κS := le_trans (le_max_left _ _) (le_max_right _ _)
  have hS3 : 1 / κr3 ≤ κS := le_trans (le_max_right _ _) (le_max_right _ _)
  have hκSpos : 0 < κS := (one_div_pos.2 hκr0).trans_le hS0
  set δ := εmin / (κS * M1) with hδdef
  have hδ : 0 < δ := div_pos hεmin (mul_pos hκSpos (by linarith))
  obtain ⟨kε, hfirst, hF, hD⟩ := theorem_5_1_7_of_iota_nonneg (by omega) (by norm_num) le_rfl
    hp1 hp3 h hΦ hβ0 hβ1 i hι hε₀ hε₁.le (fun _ => hε₂.le) (fun _ => hε₃.le) hδ
    ((div_mul_le_mul_div hεmin.le (le_trans (min_le_left _ _) (min_le_left _ _)) hκr0 hS0
      one_pos hM1one).trans_eq (div_one _))
    (div_mul_le_mul_div hεmin.le (le_trans (min_le_left _ _) (min_le_right _ _)) hκr1 hS1
      (by positivity) (le_max_left _ _))
    (fun _ => div_mul_le_mul_div hεmin.le (le_trans (min_le_right _ _) (min_le_left _ _)) hκr2
      hS2 (by positivity) (max_le (hM1one) (le_trans (le_max_left _ _) (le_max_right _ _))))
    (fun _ => div_mul_le_mul_div hεmin.le (le_trans (min_le_right _ _) (min_le_right _ _)) hκr3
      hS3 (by positivity) (max_le (hM1one) (le_trans (le_max_right _ _) (le_max_right _ _))))
  -- `‖r_0‖^{1/2^i} max(1, ‖r_0‖^{ι_j}) ≤ max_j ‖r_0‖^{1/2^i + ι_j}`
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2' : (p : ℝ) - 2 ≠ 0 := by linarith
  have e1 : α + iota 1 p ℓ i = 1 - ((ℓ : ℝ) - 1) / p := by
    rw [iota_one_eq', hαdef]; field_simp; ring
  have e2 : α + iota 2 p ℓ i = 1 - 2 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 1) := by
    rw [iota_two_eq', hαdef]; field_simp; ring
  have e3 : α + iota 3 p ℓ i = 1 - 3 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 2) := by
    rw [iota_three_eq', hαdef]; field_simp; ring
  have hRM : R ^ α * M1 ≤ max (max (R ^ α) (R ^ (1 - ((ℓ : ℝ) - 1) / p)))
      (max (R ^ (1 - 2 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 1)))
        (R ^ (1 - 3 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 2)))) := by
    have hRα : 0 ≤ R ^ α := Real.rpow_nonneg hR0 _
    rw [hM1, mul_max_of_nonneg _ _ hRα, mul_max_of_nonneg _ _ hRα, mul_max_of_nonneg _ _ hRα,
      mul_one, ← e1, ← e2, ← e3]
    exact max_le_max (max_le_max le_rfl (Real.le_rpow_add hR0 _ _))
      (max_le_max (Real.le_rpow_add hR0 _ _) (Real.le_rpow_add hR0 _ _))
  set Rmax := max (max (R ^ α) (R ^ (1 - ((ℓ : ℝ) - 1) / p)))
    (max (R ^ (1 - 2 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 1)))
      (R ^ (1 - 3 * ((ℓ : ℝ) - 1) / ((p : ℝ) - 2)))) with hRmax
  have hratio : R ^ α / δ ≤ κS * Rmax / εmin := by
    rw [hδdef, div_div_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hεmin.le
    calc R ^ α * (κS * M1) = κS * (R ^ α * M1) := by ring
      _ ≤ κS * Rmax := mul_le_mul_of_nonneg_left hRM hκSpos.le
  have hκA : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ := by
    have := P.log_γ₂_pos; positivity
  refine ⟨kε, hfirst, hF.trans ?_, hD.trans (by linarith)⟩
  have := mul_le_mul_of_nonneg_left hratio hκA
  calc (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (R ^ α / δ) +
        ((|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams L / P.σ₀)) / Real.log P.γ₂ + 2)
      ≤ (1 + |Real.log P.γ₁| / Real.log P.γ₂) * (κS * Rmax / εmin) +
        ((|Real.log P.γ₁| + Real.log (arSigmaMax P.toARParams L / P.σ₀)) / Real.log P.γ₂ + 2) :=
        by linarith
    _ = _ := by ring

end Theorem517

/-! ### Termination guarantees and existence of runs -/

section Existence

variable {r : ℝⁿ → ℝᵐ} {ℓ : ℝ} {q : ℕ} {ε₀ ε₁ ε₂ ε₃ : ℝ}

/-- At termination by the third-order branch of the test, the model directions of small
curvature are directions of small scaled curvature for `Φ_ℓ`: `𝓜_ε ⊆ 𝒵_ε`
([cartis2022evaluation], remark after Algorithm 5.1.1 and Theorem 5.1.7). -/
theorem subset_zSet_of_forall {M : Set ℝⁿ} {x : ℝⁿ} (hM : ∀ d ∈ M, ‖d‖ = 1)
    (h : ∀ d ∈ M, psiThree r ℓ x d ≤ ε₃ ∧ psiTwoDir r ℓ x d ≤ ε₂) : M ⊆ zSet r ℓ ε₂ x :=
  fun d hd => ⟨hM d hd, (h d hd).2⟩

/-- For `q ≤ 2` the test does not depend on the direction set. -/
theorem arpLEStop_congr_of_le_two (hq : q ≤ 2) (M M' : Set ℝⁿ) (x : ℝⁿ) :
    ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ M x ↔ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ M' x := by
  have h3 : q ≠ 3 := by omega
  simp only [ARpLEStop, h3, false_and, or_false]

/-- **Existence of ARpLE runs for `q ∈ {1, 2}`** ([cartis2022evaluation], Algorithm 5.1.1): if
`Φ_ℓ` is `C^p` (`p ≥ q`, `p ≥ 1`) and `ε₀, ε₁, ε₂ ≥ 0`, there is a run from every `x₀`. (When
the test fails, `r(x_k) ≠ 0` and either `ψ_{ℓ,1}(x_k) > ε₁ ≥ 0` or (`q = 2`)
`ψ_{ℓ,2}(x_k) < -ε₂ ≤ 0`, so `x_k` is not a second-order critical point of `Φ_ℓ` and a global
minimizer of the model is an admissible step.) -/
theorem algorithm_5_1_1.exists_run (P : ARpParams) {p : ℕ} (hΦ : ContDiff ℝ p (Phi r ℓ))
    (hp : 1 ≤ p) (hq1 : 1 ≤ q) (hq : q ≤ 2) (hqp : q ≤ p) (hε₀ : 0 ≤ ε₀) (hε₁ : 0 ≤ ε₁)
    (hε₂ : 0 ≤ ε₂) (x₀ : ℝⁿ) :
    ∃ x s : ℕ → ℝⁿ, ∃ σ : ℕ → ℝ, x 0 = x₀ ∧ algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ := by
  have htest : ∀ y, ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ ∅ y →
      fderiv ℝ (Phi r ℓ) y ≠ 0 ∨
        (2 ≤ q ∧ minCurvature (iteratedFDeriv ℝ 2 (Phi r ℓ) y) < 0) := by
    intro y hy
    simp only [ARpLEStop, not_or, not_and, not_le, not_lt] at hy
    obtain ⟨h0, h1, h2, h3, -⟩ := hy
    have hy0 : r y ≠ 0 := norm_pos_iff.1 (hε₀.trans_lt h0)
    have hpos : 0 < ‖r y‖ ^ (ℓ - 1) := Real.rpow_pos_of_pos (hε₀.trans_lt h0) _
    rcases le_or_gt (psiOne r ℓ y) ε₁ with hψ | hψ
    · right
      interval_cases q
      · exact absurd hψ (not_le.2 (h1 rfl))
      · refine ⟨le_rfl, ?_⟩
        have hlt := h3 rfl hψ
        rw [psiTwo_eq, div_lt_iff₀ hpos] at hlt
        nlinarith
    · left
      intro h0'
      rw [psiOne_eq, h0', norm_zero, zero_div] at hψ
      linarith
  obtain ⟨x, s, σ, hx0, hrun⟩ := exists_isARpRun (f := Phi r ℓ) (q := q) P hΦ hp hq
    (fun h2 => h2.trans hqp) htest x₀
  refine ⟨x, s, σ, hx0, ?_⟩
  have heq : (fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k)) =
      fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ ∅ (x k) :=
    funext fun k => propext (arpLEStop_congr_of_le_two hq _ _ _)
  rw [algorithm_5_1_1, heq]
  exact hrun

/-- The direction set `𝓜_k` read from the previous iteration (as `Optimization.prevIterate`
provides it): `𝓜_0` from `∇²Φ_ℓ(x_0)` and `ε₂`, `𝓜_{k+1}` from the model of iteration `k`. -/
private noncomputable def mdirOfPrev (r : ℝⁿ → ℝᵐ) (ℓ : ℝ) (p : ℕ) (P : ARpParams) (ε₂ : ℝ) :
    Option (ℝⁿ × ℝ × ℝⁿ) → ℝⁿ → Set ℝⁿ
  | none, y => smallCurvatureDirections (iteratedFDeriv ℝ 2 (Phi r ℓ) y) ε₂
  | some (x', σ', s'), _ => smallCurvatureDirections
      (iteratedFDeriv ℝ 2 (regularizedModel (ftaylorSeries ℝ (Phi r ℓ) x') p σ') s')
      (P.θ₂ * ‖s'‖ ^ (p - 1))

/-- **Existence of ARpLE runs for any `q`, under an explicit hypothesis** ([cartis2022evaluation],
Algorithm 5.1.1): if an admissible ARp step (4.1.10)–(4.1.13) exists at every point `y` and
weight `σ ≥ σ_min`, `σ > 0`, at which the test fails for some direction set `M`, there is a run
from every `x₀`. For `q = 3` the hypothesis can fail (see `Optimization.ARpRun`); for `q ≤ 2` it
holds and `algorithm_5_1_1.exists_run` applies. -/
theorem algorithm_5_1_1.exists_run_of_step (P : ARpParams) {p : ℕ}
    (hstep : ∀ (M : Set ℝⁿ) (y : ℝⁿ) (σ : ℝ), P.σmin ≤ σ → 0 < σ →
      ¬ ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ M y → ∃ s, IsARpStep (Phi r ℓ) p P q y σ s)
    (x₀ : ℝⁿ) :
    ∃ x s : ℕ → ℝⁿ, ∃ σ : ℕ → ℝ, x 0 = x₀ ∧ algorithm_5_1_1 r ℓ p P q ε₀ ε₁ ε₂ ε₃ x s σ := by
  obtain ⟨x, s, σ, hx0, hrun⟩ := exists_isARpRun_prev (f := Phi r ℓ) (p := p) (q := q) P
    (test := fun prev y _ => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdirOfPrev r ℓ p P ε₂ prev y) y)
    (fun prev y σ hσ hσ0 ht => hstep _ y σ hσ hσ0 ht) x₀
  refine ⟨x, s, σ, hx0, ?_⟩
  have heq : (fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃ (mdir r ℓ p P ε₂ x s σ k) (x k)) =
      fun k => ARpLEStop r ℓ q ε₀ ε₁ ε₂ ε₃
        (mdirOfPrev r ℓ p P ε₂ (prevIterate x s σ k) (x k)) (x k) := by
    funext k
    cases k <;> rfl
  rw [algorithm_5_1_1, heq]
  exact hrun

end Existence

/-! ### Full rank -/

/-- **(5.1.63)** ([cartis2022evaluation]): off the zeros of a residual `r` differentiable at `x`,
for every `ℓ > 1`, `ψ_{ℓ,1}(x) = ‖J(x)^T r(x)‖ / ‖r(x)‖` (independent of `ℓ`), with
`J(x)^T` the adjoint of the Jacobian. -/
theorem psiOne_eq_of_jacobian {r : ℝⁿ → ℝᵐ} {ℓ : ℝ} (hℓ : 1 < ℓ) {x : ℝⁿ}
    (hr : DifferentiableAt ℝ r x) (hx : r x ≠ 0) :
    psiOne r ℓ x = ‖(ContinuousLinearMap.adjoint (fderiv ℝ r x)) (r x)‖ / ‖r x‖ := by
  rw [psiOne_eq]
  exact norm_fderiv_residualPow_div hr hℓ hx

/-- **(5.1.62)–(5.1.64)** ([cartis2022evaluation]): if the Jacobian's adjoint satisfies
`‖J(x)^T v‖ ≥ s₀ ‖v‖` for all `v` (its smallest singular value is at least `s₀`), then
`ψ_{ℓ,1}(x) ≥ s₀` off the zeros of `r` (`ℓ > 1`). -/
theorem psiOne_ge_of_jacobian {r : ℝⁿ → ℝᵐ} {ℓ : ℝ} (hℓ : 1 < ℓ) {x : ℝⁿ}
    (hr : DifferentiableAt ℝ r x) (hx : r x ≠ 0) {s₀ : ℝ}
    (hs : ∀ v, s₀ * ‖v‖ ≤ ‖(ContinuousLinearMap.adjoint (fderiv ℝ r x)) v‖) :
    s₀ ≤ psiOne r ℓ x := by
  rw [psiOne_eq_of_jacobian hℓ hr hx, le_div_iff₀ (norm_pos_iff.2 hx)]
  exact hs _

end CartisGouldToint.Chapter05
