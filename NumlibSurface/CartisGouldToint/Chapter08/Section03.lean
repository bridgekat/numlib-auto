import Numlib.Optimization.Complexity.Basic
import Numlib.Optimization.Complexity.Existence
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Cartis–Gould–Toint §8.3: Subproblem solution

Surface file for [cartis2022evaluation] §8.3: the partition of the multiplier line into the sets
`𝓝`, `𝓛`, `𝓖` for the regularization subproblem (8.1.3) and the trust-region subproblem (8.1.2),
the iterations of Algorithms 8.3.1 and 8.3.2 from a point of `𝓛`, and the description of all
global minimizers, hard case included (Corollaries 8.3.1 and 8.3.2).

## Main definitions

* `setN`, `setL_reg`, `setG_reg`, `setF_reg` — the sets `𝓝 = (-∞, λₛ]`, `𝓛`, `𝓖`, `𝓕 = 𝓛 ∪ 𝓖` of
  §8.3.1, by their descriptions through `‖s(λ)‖_M`; `setL_tr`, `setG_tr` — those of §8.3.2.
* `taylorCorrectionFn`, `regNewtonCorrectionFn`, `trNewtonCorrectionFn` — the corrections
  `δₖᵀ(λc)` (rightmost real root of (8.2.15)), `δᴺ(λc, β)` of (8.2.25) and `δᴺ` of (8.2.24).
* `algorithm_8_3_1`, `algorithm_8_3_2` — runs of Algorithms 8.3.1 and 8.3.2.
* `minNormSolution hH hM g λ` — the minimum-`M`-norm solution `-(H + λ M)⁺ g` of (8.3.2).
* `exitTest` — the exit test of Algorithms 8.3.1 and 8.3.2.

## Main results

* `setF_reg_eq_Ioi`, `setL_tr_union_setG_tr` — `𝓝`, `𝓛`, `𝓖` partition `ℝ`.
* `setL_reg_eq_Ioc`, `setL_tr_eq_Ioc` — `𝓛 = (λₛ, λ*]` and `𝓖 = (λ*, ∞)`.
* `algorithm_8_3_1_terminates`, `algorithm_8_3_2_terminates` — from `λ₀ ∈ 𝓛` (easy case
  `λ* > λₛ`) the iterates stay in `𝓛`, increase to `λ*` (Q-linearly and Q-superlinearly when a
  Newton correction is among the candidates), every run stays in `𝓛` and increases, and the exit
  test is met: a run exists.
* `minNormSolution_spec`, `tendsto_stepOf_minNormSolution` — the minimum-`M`-norm solution and
  the limit `s(λ) → sₛ` as `λ ↓ -λ₁`.
* `corollary_8_3_1`, `corollary_8_3_2` — global minimizers and the optimal values (8.3.3),
  (8.3.5).

## Corrections to the source

* §8.3.1 describes `𝓝` also as `{λ | H + λ M is not positive definite}`; that set is
  `(-∞, -λ₁]`, which differs from `(-∞, λₛ]` when `λ₁ > 0`. Likewise the set-builder forms
  `𝓛 = {λ | H + λ M ≻ 0, ‖s(λ)‖_M ≥ …}`, `𝓖 = {λ | H + λ M ≻ 0, ‖s(λ)‖_M < …}` contain points
  `λ ∈ (-λ₁, 0]` outside `(λₛ, ∞)` when `λ₁ > 0` (e.g. `H = M = I`, `λ = -1/2`). The interval forms
  are used: `𝓛`, `𝓖` are defined inside `(λₛ, ∞)` and `𝓝`, `𝓛`, `𝓖` partition `ℝ`
  (`setF_reg_eq_Ioi`, `setL_tr_union_setG_tr`).
* §8.3.1 writes the transformed regularization target as `τ(λ; β) = (λ/σ)^{β/(r-2)}`; it is
  `(λ/σ)^{2β/(r-2)}` (consistent with (8.2.25)), as used by `regSecularFn`. The prose ranges
  `β ∈ (0, r - 2]` and `β ∈ [-1, 0)` should read `(0, (r-2)/2]` and `[-1/2, 0)`.
* Algorithm 8.3.1 allows any `β ∈ [-1/2, (r-2)/2]`, but (8.2.25) is undefined at `β = 0`; `β ≠ 0`
  is assumed.
* Corollaries 8.3.1/8.3.2: a single fixed eigenvector `v₁` does not parametrize all minimizers
  when `λ₁` is multiple; the formal statements give `s* = sₛ + α v` for some nonzero generalized
  eigenvector `v` for `λ₁` (equivalently `s* - sₛ ∈ ker (H + λ* M)`), for `n ≥ 1`. The minimum-norm
  solution is taken in the `M`-norm, which is the limit of `s(λ)` as `λ ↓ λₛ`.
* Corollary 8.3.2: when `λ* = 0` (`λ₁ = 0`, interior solutions) the vector `sₛ + α v₁` need not lie
  on the boundary (`n = 1`, `H = 0`, `g = 0`, `M = 1`, `Δ = 1`, `s* = 0`); the boundary condition
  `‖sₛ + α v₁‖_M = Δ` is stated for `λ* > 0` only.
-/

open Matrix Set Filter Topology
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter08

open Subproblem

variable {n : ℕ} {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-! ### The sets `𝓝`, `𝓛`, `𝓖` -/

/-- The set `𝓝 = (-∞, λₛ]` of [cartis2022evaluation] §8.3. -/
def setN (hH : H.IsHermitian) (hM : M.PosDef) : Set ℝ := Iic (lambdaS hH hM)

/-- The set `𝓛` of [cartis2022evaluation] §8.3.1 for the regularization subproblem (8.1.3):
`λ > λₛ` with `‖s(λ)‖_M ≥ (λ/σ)^{1/(r-2)}`; it is `(λₛ, λ*]` (`setL_reg_eq_Ioc`). -/
def setL_reg (hH : H.IsHermitian) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n)) (σ r : ℝ) :
    Set ℝ :=
  {lam | lambdaS hH hM < lam ∧ (lam / σ) ^ (1 / (r - 2)) ≤ mNorm M (stepOf g H M lam)}

/-- The set `𝓖` of [cartis2022evaluation] §8.3.1 for the regularization subproblem (8.1.3):
`λ > λₛ` with `‖s(λ)‖_M < (λ/σ)^{1/(r-2)}`; it is `(λ*, ∞)` (`setL_reg_eq_Ioc`). -/
def setG_reg (hH : H.IsHermitian) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n)) (σ r : ℝ) :
    Set ℝ :=
  {lam | lambdaS hH hM < lam ∧ mNorm M (stepOf g H M lam) < (lam / σ) ^ (1 / (r - 2))}

/-- The set `𝓕 = 𝓛 ∪ 𝓖` of [cartis2022evaluation] §8.3.1. -/
def setF_reg (hH : H.IsHermitian) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n)) (σ r : ℝ) :
    Set ℝ :=
  setL_reg hH hM g σ r ∪ setG_reg hH hM g σ r

/-- The set `𝓛` of [cartis2022evaluation] §8.3.2 for the trust-region subproblem (8.1.2):
`λ > λₛ` with `‖s(λ)‖_M ≥ Δ`. -/
def setL_tr (hH : H.IsHermitian) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n)) (Δ : ℝ) :
    Set ℝ :=
  {lam | lambdaS hH hM < lam ∧ Δ ≤ mNorm M (stepOf g H M lam)}

/-- The set `𝓖` of [cartis2022evaluation] §8.3.2 for the trust-region subproblem (8.1.2):
`λ > λₛ` with `‖s(λ)‖_M < Δ`. -/
def setG_tr (hH : H.IsHermitian) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n)) (Δ : ℝ) :
    Set ℝ :=
  {lam | lambdaS hH hM < lam ∧ mNorm M (stepOf g H M lam) < Δ}

/-- The regularization target `τ(λ) = (λ/σ)^{2/(r-2)}` of (8.2.9). -/
noncomputable def regTarget (σ r : ℝ) (lam : ℝ) : ℝ := (lam / σ) ^ (2 / (r - 2))

theorem regTarget_eq_sq {σ lam : ℝ} (r : ℝ) (hσ : 0 < σ) (hlam : 0 ≤ lam) :
    regTarget σ r lam = ((lam / σ) ^ (1 / (r - 2))) ^ 2 := by
  rw [regTarget, ← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hlam hσ.le)]
  congr 1
  push_cast
  ring

variable (hH : H.IsHermitian) (hM : M.PosDef)
include hH

theorem mem_setL_reg_iff {σ r lam : ℝ} (hσ : 0 < σ) :
    lam ∈ setL_reg hH hM g σ r ↔ lambdaS hH hM < lam ∧ regTarget σ r lam ≤ secularFn g H M lam := by
  refine and_congr_right fun hlam => ?_
  have hl : 0 ≤ lam := (lambdaS_nonneg hH hM).trans hlam.le
  rw [regTarget_eq_sq r hσ hl, ← mNorm_stepOf_sq hM]
  exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg (div_nonneg hl hσ.le) _) (mNorm_nonneg _ _)
    two_ne_zero).symm

theorem mem_setG_reg_iff {σ r lam : ℝ} (hσ : 0 < σ) :
    lam ∈ setG_reg hH hM g σ r ↔ lambdaS hH hM < lam ∧ secularFn g H M lam < regTarget σ r lam := by
  refine and_congr_right fun hlam => ?_
  have hl : 0 ≤ lam := (lambdaS_nonneg hH hM).trans hlam.le
  rw [regTarget_eq_sq r hσ hl, ← mNorm_stepOf_sq hM]
  exact (pow_lt_pow_iff_left₀ (mNorm_nonneg _ _) (Real.rpow_nonneg (div_nonneg hl hσ.le) _)
    two_ne_zero).symm

theorem mem_setL_tr_iff {Δ lam : ℝ} (hΔ : 0 < Δ) :
    lam ∈ setL_tr hH hM g Δ ↔ lambdaS hH hM < lam ∧ Δ ^ 2 ≤ secularFn g H M lam := by
  refine and_congr_right fun _ => ?_
  rw [← mNorm_stepOf_sq hM]
  exact (pow_le_pow_iff_left₀ hΔ.le (mNorm_nonneg _ _) two_ne_zero).symm

theorem mem_setG_tr_iff {Δ lam : ℝ} (hΔ : 0 < Δ) :
    lam ∈ setG_tr hH hM g Δ ↔ lambdaS hH hM < lam ∧ secularFn g H M lam < Δ ^ 2 := by
  refine and_congr_right fun _ => ?_
  rw [← mNorm_stepOf_sq hM]
  exact (pow_lt_pow_iff_left₀ (mNorm_nonneg _ _) hΔ.le two_ne_zero).symm

/-- **The partition, regularization** ([cartis2022evaluation] §8.3.1): `𝓛 ∩ 𝓖 = ∅` and
`𝓕 = 𝓛 ∪ 𝓖 = (λₛ, ∞)`, so `𝓝`, `𝓛`, `𝓖` partition `ℝ`. -/
theorem setF_reg_eq_Ioi (σ r : ℝ) :
    Disjoint (setL_reg hH hM g σ r) (setG_reg hH hM g σ r) ∧
      setF_reg hH hM g σ r = Ioi (lambdaS hH hM) ∧
      Disjoint (setN hH hM) (setF_reg hH hM g σ r) ∧ setN hH hM ∪ setF_reg hH hM g σ r = univ := by
  have hF : setF_reg hH hM g σ r = Ioi (lambdaS hH hM) := by
    ext lam
    simp only [setF_reg, setL_reg, setG_reg, mem_union, mem_ofPred_eq, mem_Ioi]
    exact ⟨fun h => h.elim And.left And.left, fun h => (le_or_gt _ _).imp (⟨h, ·⟩) (⟨h, ·⟩)⟩
  refine ⟨Set.disjoint_left.2 fun lam h1 h2 => not_le.2 h2.2 h1.2, hF, ?_, ?_⟩
  · rw [hF]; exact Set.disjoint_left.2 fun lam (h1 : lam ≤ _) (h2 : _ < lam) => not_le.2 h2 h1
  · rw [hF, setN, Iic_union_Ioi]

/-- **The partition, trust region** ([cartis2022evaluation] §8.3.2): `𝓛 ∩ 𝓖 = ∅` and
`𝓛 ∪ 𝓖 = (λₛ, ∞)`. -/
theorem setL_tr_union_setG_tr (Δ : ℝ) :
    Disjoint (setL_tr hH hM g Δ) (setG_tr hH hM g Δ) ∧
      setL_tr hH hM g Δ ∪ setG_tr hH hM g Δ = Ioi (lambdaS hH hM) := by
  refine ⟨Set.disjoint_left.2 fun lam h1 h2 => not_le.2 h2.2 h1.2, ?_⟩
  ext lam
  simp only [setL_tr, setG_tr, mem_union, mem_ofPred_eq, mem_Ioi]
  exact ⟨fun h => h.elim And.left And.left, fun h => (le_or_gt _ _).imp (⟨h, ·⟩) (⟨h, ·⟩)⟩

/-- **`𝓛` and `𝓖` as intervals, regularization** ([cartis2022evaluation] §8.3.1). Let `s*` be a
global minimizer of (8.1.3) with multiplier `λ* = σ ‖s*‖_M^{r-2}`. Then `λₛ ≤ λ*`,
`𝓛 = (λₛ, λ*]`, `𝓖 = (λ*, ∞)` and `𝓕 = (λₛ, ∞)`; in particular `𝓛 ≠ ∅` iff `λ* > λₛ` (the easy
case). -/
theorem setL_reg_eq_Ioc {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r) {s : EuclideanSpace ℝ (Fin n)}
    (hs : IsRegularizationSolution g H M σ r s) :
    lambdaS hH hM ≤ σ * mNorm M s ^ (r - 2) ∧
      setL_reg hH hM g σ r = Ioc (lambdaS hH hM) (σ * mNorm M s ^ (r - 2)) ∧
      setG_reg hH hM g σ r = Ioi (σ * mNorm M s ^ (r - 2)) ∧
      setF_reg hH hM g σ r = Ioi (lambdaS hH hM) ∧
      ((setL_reg hH hM g σ r).Nonempty ↔ lambdaS hH hM < σ * mNorm M s ^ (r - 2)) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hmin := (isRegularizationSolution_iff_scaled hM).1 hs
  have hle : lambdaS hH hM ≤ σ * mNorm M s ^ (r - 2) := by
    rw [lambdaS_eq, mNorm_eq_norm_toScaled hM]
    exact (shiftThreshold_le_of_isMinOn_regModel (hH := hT) hσ hr hmin).1
  have hiff : ∀ lam, lambdaS hH hM < lam →
      (regTarget σ r lam ≤ secularFn g H M lam ↔ lam ≤ σ * mNorm M s ^ (r - 2)) := by
    intro lam hlam
    rw [lambdaS_eq] at hlam
    rw [secularFn_eq_secular hM, mNorm_eq_norm_toScaled hM]
    exact le_secular_iff_of_regularization hσ hr hmin hlam
  have hL : setL_reg hH hM g σ r = Ioc (lambdaS hH hM) (σ * mNorm M s ^ (r - 2)) := by
    ext lam
    rw [mem_setL_reg_iff hH hM hσ, mem_Ioc]
    exact and_congr_right (hiff lam)
  have hG : setG_reg hH hM g σ r = Ioi (σ * mNorm M s ^ (r - 2)) := by
    ext lam
    rw [mem_setG_reg_iff hH hM hσ, mem_Ioi]
    constructor
    · rintro ⟨hlam, h⟩
      exact not_le.1 fun h' => (not_le.2 h) ((hiff lam hlam).2 h')
    · intro h
      have hlam := hle.trans_lt h
      exact ⟨hlam, not_le.1 fun h' => (not_le.2 h) ((hiff lam hlam).1 h')⟩
  refine ⟨hle, hL, hG, ?_, ?_⟩
  · rw [setF_reg, hL, hG, Ioc_union_Ioi_eq_Ioi hle]
  · rw [hL, nonempty_Ioc]

/-- **`𝓛` and `𝓖` as intervals, trust region** ([cartis2022evaluation] §8.3.2). Let `Δ > 0`, `s*`
a global minimizer of (8.1.2) with multiplier `λ*` (`IsTrustRegionKKT`). Then `λₛ ≤ λ*`,
`𝓛 = (λₛ, λ*]`, `𝓖 = (λ*, ∞)`; in particular `𝓛 ≠ ∅` iff `λ* > λₛ`. -/
theorem setL_tr_eq_Ioc {Δ : ℝ} (hΔ : 0 < Δ) {s : EuclideanSpace ℝ (Fin n)}
    (hs : IsTrustRegionSolution g H M Δ s) {lamStar : ℝ}
    (hkkt : IsTrustRegionKKT g H M Δ s lamStar) :
    lambdaS hH hM ≤ lamStar ∧ setL_tr hH hM g Δ = Ioc (lambdaS hH hM) lamStar ∧
      setG_tr hH hM g Δ = Ioi lamStar ∧
      ((setL_tr hH hM g Δ).Nonempty ↔ lambdaS hH hM < lamStar) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hn := ((isTrustRegionSolution_iff_scaled hM).1 hs).1
  have hμ := (isTrustRegionKKT_iff_scaled hM hΔ).1 hkkt
  have hle : lambdaS hH hM ≤ lamStar := by
    rw [lambdaS_eq]; exact (shiftThreshold_le_of_isTrustRegionMultiplier (hH := hT) hμ).1
  have hiff : ∀ lam, lambdaS hH hM < lam → (Δ ^ 2 ≤ secularFn g H M lam ↔ lam ≤ lamStar) := by
    intro lam hlam
    rw [lambdaS_eq] at hlam
    rw [secularFn_eq_secular hM]
    exact le_secular_iff_of_trustRegion hΔ hμ hn hlam
  have hL : setL_tr hH hM g Δ = Ioc (lambdaS hH hM) lamStar := by
    ext lam
    rw [mem_setL_tr_iff hH hM hΔ, mem_Ioc]
    exact and_congr_right (hiff lam)
  refine ⟨hle, hL, ?_, by rw [hL, nonempty_Ioc]⟩
  ext lam
  rw [mem_setG_tr_iff hH hM hΔ, mem_Ioi]
  constructor
  · rintro ⟨hlam, h⟩
    exact not_le.1 fun h' => (not_le.2 h) ((hiff lam hlam).2 h')
  · intro h
    have hlam := hle.trans_lt h
    exact ⟨hlam, not_le.1 fun h' => (not_le.2 h) ((hiff lam hlam).1 h')⟩

omit hH

/-! ### The corrections -/

/-- The **Taylor correction** `δₖᵀ(λc)` of [cartis2022evaluation] §8.2.1: the rightmost real root
of `t_k(δ) = τ(λc + δ)` (8.2.15), defined as the supremum of the root set. -/
noncomputable def taylorCorrectionFn (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (τ : ℝ → ℝ) (k : ℕ) (lamc : ℝ) : ℝ :=
  sSup {δ | secularTaylorPoly g H M k lamc δ = τ (lamc + δ)}

/-- The transformed regularization secular function `θ(λ; β) = π(λ; β) - (λ/σ)^{2β/(r-2)}` of
[cartis2022evaluation] §8.2.2. -/
noncomputable def regSecularFn (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (σ r β lam : ℝ) : ℝ :=
  secularFn g H M lam ^ β - (lam / σ) ^ (2 * β / (r - 2))

/-- The **regularization Newton correction** `δᴺ(λc, β) = -θ(λc; β)/θ⁽¹⁾(λc; β)` of
[cartis2022evaluation] (8.2.25). -/
noncomputable def regNewtonCorrectionFn (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (σ r β lamc : ℝ) : ℝ :=
  -regSecularFn g H M σ r β lamc / deriv (regSecularFn g H M σ r β) lamc

/-- The **trust-region Newton correction**
`δᴺ = 2 π(λc)/π⁽¹⁾(λc) (1 - ‖s(λc)‖_M/Δ)` of [cartis2022evaluation] (8.2.24). -/
noncomputable def trNewtonCorrectionFn (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (Δ lamc : ℝ) : ℝ :=
  2 * secularFn g H M lamc / deriv (secularFn g H M) lamc * (1 - mNorm M (stepOf g H M lamc) / Δ)

theorem taylorCorrectionFn_eq (τ : ℝ → ℝ) (k : ℕ) (lamc : ℝ) :
    taylorCorrectionFn g H M τ k lamc =
      taylorCorrection (scaledGrad hM g) (scaledOp H hM) τ k lamc := by
  simp only [taylorCorrectionFn, taylorCorrection, secularTaylorPoly_eq hM]

theorem regSecularFn_eq (σ r β : ℝ) :
    regSecularFn g H M σ r β = regSecular (scaledGrad hM g) (scaledOp H hM) σ r β := by
  funext lam
  rw [regSecularFn, regSecular, secularFn_eq_secular hM]

theorem regNewtonCorrectionFn_eq (σ r β lamc : ℝ) :
    regNewtonCorrectionFn g H M σ r β lamc =
      regNewtonCorrection (scaledGrad hM g) (scaledOp H hM) σ r β lamc := by
  rw [regNewtonCorrectionFn, regNewtonCorrection, regSecularFn_eq hM]

theorem trNewtonCorrectionFn_eq (Δ lamc : ℝ) :
    trNewtonCorrectionFn g H M Δ lamc =
      trNewtonCorrection (scaledGrad hM g) (scaledOp H hM) Δ lamc := by
  rw [trNewtonCorrectionFn, trNewtonCorrection, secularFn_eq_secular hM,
    mNorm_eq_norm_toScaled hM, toScaled_stepOf hM]

/-! ### Runs of the secular iterations -/

/-- The **exit test** of Algorithms 8.3.1 and 8.3.2 of [cartis2022evaluation] at iteration `k`:
`k ≥ 1` and `|λ k - λ (k - 1)| ≤ ε`. A run stops at the first such `k`
(`Optimization.IsFirstHit`). -/
def exitTest (ε : ℝ) (lam : ℕ → ℝ) (k : ℕ) : Prop := 1 ≤ k ∧ |lam k - lam (k - 1)| ≤ ε

/-- A convergent real sequence meets the exit test. -/
theorem exists_exitTest {x : ℕ → ℝ} {L ε : ℝ} (hx : Tendsto x atTop (𝓝 L)) (hε : 0 < ε) :
    ∃ k, exitTest ε x k := by
  have hd : Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0) := by
    simpa using (hx.comp (tendsto_add_atTop_nat 1)).sub hx
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hd ε hε
  have := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at this
  exact ⟨N + 1, by omega, by simpa using this.le⟩

/-- A greatest-candidate sequence exists when the candidate sets are nonempty
(`Optimization.exists_run_of_forall_exists`). -/
theorem exists_isGreatest_seq (C : ℝ → Finset ℝ) (hC : ∀ t, (C t).Nonempty) (x₀ : ℝ) :
    ∃ x : ℕ → ℝ, x 0 = x₀ ∧ ∀ k, IsGreatest (C (x k) : Set ℝ) (x (k + 1)) := by
  obtain ⟨x, hx0, hx⟩ := Optimization.exists_run_of_forall_exists (init := fun a => a = x₀)
    (stop := fun _ _ => False) (step := fun _ a b => IsGreatest (C a : Set ℝ) b) ⟨x₀, rfl⟩
    fun _ a _ => ⟨_, Finset.isGreatest_max' _ (hC a)⟩
  exact ⟨x, hx0, fun k => hx k not_false⟩

/-- A sequence with `x k ≤ x (k + 1) ≤ L` for `k < K` from `x 0 ∈ (a, L]` stays in `(a, L]` up
to `K`. -/
theorem mem_Ioc_of_le {x : ℕ → ℝ} {a L : ℝ} {K : ℕ} (h0 : x 0 ∈ Ioc a L)
    (hstep : ∀ k < K, x k ∈ Ioc a L → x k ≤ x (k + 1) ∧ x (k + 1) ≤ L) :
    ∀ k ≤ K, x k ∈ Ioc a L := by
  intro k hk
  induction k with
  | zero => exact h0
  | succ k ih =>
    have hmem := ih (by omega)
    obtain ⟨h1, h2⟩ := hstep k (by omega) hmem
    exact ⟨hmem.1.trans_le h1, h2⟩

/-- A sequence squeezed by `x k ≤ x (k + 1) ≤ L` from `x 0 ∈ (a, L]` stays in `(a, L]` and is
monotone. -/
theorem mem_Ioc_and_monotone {x : ℕ → ℝ} {a L : ℝ} (h0 : x 0 ∈ Ioc a L)
    (hstep : ∀ k, x k ∈ Ioc a L → x k ≤ x (k + 1) ∧ x (k + 1) ≤ L) :
    (∀ k, x k ∈ Ioc a L) ∧ Monotone x := by
  have hmem : ∀ k, x k ∈ Ioc a L := fun k =>
    mem_Ioc_of_le (K := k) h0 (fun j _ => hstep j) k le_rfl
  exact ⟨hmem, monotone_nat_of_le_succ fun k => (hstep k (hmem k)).1⟩

/-! ### Algorithm 8.3.1 -/

/-- The candidates of one iteration of Algorithm 8.3.1 of [cartis2022evaluation] from `λc`:
`λc + δᵀ_{2i-1}(λc)` for `i = 1, …, i_max` (Taylor corrections of odd order for the target
`(λ/σ)^{2/(r-2)}`) and `λc + δᴺ(λc, βⱼ)` (8.2.25) for `j = 1, …, j_max`. -/
noncomputable def candidates831 (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (σ r : ℝ) (iMax jMax : ℕ) (β : Fin jMax → ℝ) (lamc : ℝ) : Finset ℝ :=
  (Finset.Icc 1 iMax).image
      (fun i => lamc + taylorCorrectionFn g H M (regTarget σ r) (2 * i - 1) lamc) ∪
    Finset.univ.image fun j => lamc + regNewtonCorrectionFn g H M σ r (β j) lamc

/-- A **run of Algorithm 8.3.1** of [cartis2022evaluation] (given `λc ∈ 𝓛`, estimate the
multiplier `λ*` of (8.1.3)): parameters `i_max ≥ 1`, `j_max ≥ 0`, `ε > 0` and
`βⱼ ∈ [-1/2, (r-2)/2]`, `βⱼ ≠ 0`; iterates `λ 0 ∈ 𝓛` and `λ (k + 1) = λ₊` the largest
candidate (`candidates831`) from `λ k`, until the first `K` meeting the exit test
`|λ K - λ (K - 1)| ≤ ε`, `K ≥ 1` (`exitTest`; the output is `λ K`). -/
structure algorithm_8_3_1 (hH : H.IsHermitian) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (σ r : ℝ) (iMax jMax : ℕ) (β : Fin jMax → ℝ) (ε : ℝ) (lam : ℕ → ℝ) (K : ℕ) : Prop where
  /-- At least one Taylor correction is used. -/
  one_le_iMax : 1 ≤ iMax
  /-- The exit tolerance is positive. -/
  eps_pos : 0 < ε
  /-- The exponents are admissible. -/
  beta_mem : ∀ j, β j ∈ Icc (-1 / 2) ((r - 2) / 2) ∧ β j ≠ 0
  /-- The initial estimate lies in `𝓛`. -/
  start : lam 0 ∈ setL_reg hH hM g σ r
  /-- Each new estimate is the largest candidate. -/
  step : ∀ k < K, IsGreatest (candidates831 g H M σ r iMax jMax β (lam k) : Set ℝ) (lam (k + 1))
  /-- The run stops at the first iteration meeting the exit test. -/
  exit : Optimization.IsFirstHit (exitTest ε lam) K

/-- **Algorithm 8.3.1 of [cartis2022evaluation] converges and terminates.** Let `σ > 0`, `r > 2`,
`s*` a global minimizer of (8.1.3) with multiplier `λ* = σ ‖s*‖_M^{r-2}`, and admissible
parameters. If `λ₀ ∈ 𝓛` (so `λ* > λₛ`, the easy case, `setL_reg_eq_Ioc`), then:
* every sequence of largest candidates from `λ₀` stays in `𝓛`, increases and converges to `λ*`;
  when `j_max ≥ 1` the convergence is globally Q-linear (factor `γ < 1`) and Q-superlinear;
* every run of Algorithm 8.3.1 stays in `𝓛` and increases up to its exit, so its output is
  `≤ λ*`;
* a run of Algorithm 8.3.1 from `λ₀` exists (the exit test is met after finitely many steps). -/
theorem algorithm_8_3_1_terminates (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} (hσ : 0 < σ)
    (hr : 2 < r) {s : EuclideanSpace ℝ (Fin n)} (hs : IsRegularizationSolution g H M σ r s)
    {iMax jMax : ℕ} (hi : 1 ≤ iMax) {β : Fin jMax → ℝ}
    (hβ : ∀ j, β j ∈ Icc (-1 / 2) ((r - 2) / 2) ∧ β j ≠ 0) {ε : ℝ} (hε : 0 < ε) {lam₀ : ℝ}
    (h₀ : lam₀ ∈ setL_reg hH hM g σ r) :
    (∀ x : ℕ → ℝ, x 0 = lam₀ →
      (∀ k, IsGreatest (candidates831 g H M σ r iMax jMax β (x k) : Set ℝ) (x (k + 1))) →
      (∀ k, x k ∈ setL_reg hH hM g σ r) ∧ Monotone x ∧
      Tendsto x atTop (𝓝 (σ * mNorm M s ^ (r - 2))) ∧
      (0 < jMax → ∃ γ ∈ Ico (0 : ℝ) 1,
        (∀ k, σ * mNorm M s ^ (r - 2) - x (k + 1) ≤ γ * (σ * mNorm M s ^ (r - 2) - x k)) ∧
        ConvergesSuperlinearly x (σ * mNorm M s ^ (r - 2)))) ∧
    (∀ (lam : ℕ → ℝ) (K : ℕ), algorithm_8_3_1 hH hM g σ r iMax jMax β ε lam K →
      (∀ k ≤ K, lam k ∈ setL_reg hH hM g σ r) ∧ (∀ k < K, lam k ≤ lam (k + 1)) ∧
        lam K ≤ σ * mNorm M s ^ (r - 2)) ∧
    ∃ lam K, algorithm_8_3_1 hH hM g σ r iMax jMax β ε lam K ∧ lam 0 = lam₀ := by
  set lamStar := σ * mNorm M s ^ (r - 2) with hlamStar
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hmin := (isRegularizationSolution_iff_scaled hM).1 hs
  have hL := (setL_reg_eq_Ioc hH hM hσ hr hs).2.1
  have heasy : lambdaS hH hM < lamStar := by
    have := h₀; rw [hL] at this; exact this.1.trans_le this.2
  have hstar : shiftThreshold hT < lamStar := by rwa [← lambdaS_eq]
  have hroot : secular (scaledGrad hM g) (scaledOp H hM) lamStar = regTarget σ r lamStar := by
    rw [hlamStar, mNorm_eq_norm_toScaled hM]
    exact secular_eq_of_regularization hσ hr hmin (by rwa [← mNorm_eq_norm_toScaled hM])
  have hpos : 0 < lamStar := (lambdaS_nonneg hH hM).trans_lt heasy
  have hg : scaledGrad hM g ≠ 0 := by
    intro h
    rw [h, secular_zero_left] at hroot
    exact (Real.rpow_pos_of_pos (div_pos hpos hσ) _).ne' hroot.symm
  have hadm := (tau_admissible_8_2_9 hH hM).2 σ r hσ hr
  rw [lambdaS_eq] at hadm
  have htgt : IsSecularTarget hT (scaledGrad hM g) (regTarget σ r) (shiftThreshold hT) lamStar :=
    ⟨hg, neg_leftmost_le_shiftThreshold, hadm.continuousOn.mono Ioi_subset_Ici_self,
      hadm.monotoneOn.mono Ioi_subset_Ici_self, hstar, hroot⟩
  have hβ' : ∀ j, β j ∈ Ico (-1 / 2) 0 ∪ Ioc 0 ((r - 2) / 2) := fun j => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := hβ j
    rcases h3.lt_or_gt with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h, h2⟩
  have hLs : setL_reg hH hM g σ r = Ioc (shiftThreshold hT) lamStar := by rw [hL, lambdaS_eq]
  -- every candidate from `λc ∈ 𝓛` lies in `[λc, λ*]`
  have hcand : ∀ lamc ∈ Ioc (shiftThreshold hT) lamStar,
      ∀ c ∈ candidates831 g H M σ r iMax jMax β lamc, lamc ≤ c ∧ c ≤ lamStar := by
    intro lamc hc c hcm
    simp only [candidates831, Finset.mem_union, Finset.mem_image, Finset.mem_Icc,
      Finset.mem_univ, true_and] at hcm
    rcases hcm with ⟨i, ⟨hi1, -⟩, rfl⟩ | ⟨j, rfl⟩
    · rw [taylorCorrectionFn_eq hM]
      have hk : Odd (2 * i - 1) := ⟨i - 1, by omega⟩
      exact (htgt.taylorCorrection_mem hk hc).2.2
    · rw [regNewtonCorrectionFn_eq hM]
      obtain ⟨h1, h2⟩ := regNewtonCorrection_mem hσ hr (hβ' j) hstar hroot hc.1
      exact ⟨h2 hc.2, h1⟩
  have hseq : ∀ x : ℕ → ℝ, x 0 = lam₀ →
      (∀ k, IsGreatest (candidates831 g H M σ r iMax jMax β (x k) : Set ℝ) (x (k + 1))) →
      (∀ k, x k ∈ Ioc (shiftThreshold hT) lamStar) ∧ Monotone x := by
    intro x hx0 hx
    refine mem_Ioc_and_monotone (by rw [hx0, ← hLs]; exact h₀) fun k hk => ?_
    exact hcand _ hk _ (hx k).1
  have hconv : ∀ x : ℕ → ℝ, x 0 = lam₀ →
      (∀ k, IsGreatest (candidates831 g H M σ r iMax jMax β (x k) : Set ℝ) (x (k + 1))) →
      Tendsto x atTop (𝓝 lamStar) := by
    intro x hx0 hx
    obtain ⟨hmem, -⟩ := hseq x hx0 hx
    have hstep : ∀ j, x j + taylorCorrection (scaledGrad hM g) (scaledOp H hM) (regTarget σ r) 1
        (x j) ≤ x (j + 1) ∧ x (j + 1) ≤ lamStar := fun j => ⟨by
      rw [← taylorCorrectionFn_eq hM]
      exact (hx j).2 (Finset.mem_union_left _ (Finset.mem_image.2 ⟨1, by simp [hi], rfl⟩)),
      (hmem (j + 1)).2⟩
    exact (htgt.tendsto_of_taylorCorrection_le (k := 1) odd_one (hmem 0) hstep).2
  refine ⟨fun x hx0 hx => ?_, fun lam K hrun => ?_, ?_⟩
  · obtain ⟨hmem, hmono⟩ := hseq x hx0 hx
    refine ⟨fun k => hLs ▸ hmem k, hmono, hconv x hx0 hx, fun hj => ?_⟩
    have hstep : ∀ j, x j + regNewtonCorrection (scaledGrad hM g) (scaledOp H hM) σ r (β ⟨0, hj⟩)
        (x j) ≤ x (j + 1) ∧ x (j + 1) ≤ lamStar := fun j => ⟨by
      rw [← regNewtonCorrectionFn_eq hM]
      exact (hx j).2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨0, hj⟩, by simp, rfl⟩)),
      (hmem (j + 1)).2⟩
    obtain ⟨-, -, hγ, hlin, hsup⟩ :=
      tendsto_of_regNewtonCorrection_le hσ hr (hβ' ⟨0, hj⟩) hstar hroot (hmem 0) hstep
    exact ⟨_, hγ, hlin, hsup⟩
  · have hmem := mem_Ioc_of_le (K := K) (by rw [← hLs]; exact hrun.start)
      fun k hk hm => hcand _ hm _ (hrun.step k hk).1
    exact ⟨fun k hk => hLs ▸ hmem k hk, fun k hk => (hcand _ (hmem k hk.le) _ (hrun.step k hk).1).1,
      (hmem K le_rfl).2⟩
  · have hne : ∀ t, (candidates831 g H M σ r iMax jMax β t).Nonempty := fun t =>
      ⟨_, Finset.mem_union_left _ (Finset.mem_image.2 ⟨1, by simp [hi], rfl⟩)⟩
    obtain ⟨x, hx0, hx⟩ := exists_isGreatest_seq _ hne lam₀
    obtain ⟨K, hK⟩ := Optimization.exists_isFirstHit (exists_exitTest (hconv x hx0 hx) hε)
    exact ⟨x, K, ⟨hi, hε, hβ, hx0 ▸ h₀, fun k _ => hx k, hK⟩, hx0⟩

/-! ### Algorithm 8.3.2 -/

/-- The candidates of one iteration of Algorithm 8.3.2 of [cartis2022evaluation] from `λc`:
`λc + δᵀ_{2i-1}(λc)` for `i = 1, …, i_max` (Taylor corrections for the target `Δ²`) and the Newton
candidate `λc + δᴺ` with `δᴺ` of (8.2.24). -/
noncomputable def candidates832 (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (Δ : ℝ) (iMax : ℕ) (lamc : ℝ) : Finset ℝ :=
  insert (lamc + trNewtonCorrectionFn g H M Δ lamc)
    ((Finset.Icc 1 iMax).image fun i => lamc + taylorCorrectionFn g H M (fun _ => Δ ^ 2)
      (2 * i - 1) lamc)

/-- A **run of Algorithm 8.3.2** of [cartis2022evaluation] (given `λc ∈ 𝓛`, estimate the
multiplier `λ*` of (8.1.2)): as Algorithm 8.3.1 with the trust-region set `𝓛`, the target `Δ²`,
`j_max = 1` and the Newton candidate (8.2.24) (`candidates832`). -/
structure algorithm_8_3_2 (hH : H.IsHermitian) (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (Δ : ℝ) (iMax : ℕ) (ε : ℝ) (lam : ℕ → ℝ) (K : ℕ) : Prop where
  /-- At least one Taylor correction is used. -/
  one_le_iMax : 1 ≤ iMax
  /-- The exit tolerance is positive. -/
  eps_pos : 0 < ε
  /-- The initial estimate lies in `𝓛`. -/
  start : lam 0 ∈ setL_tr hH hM g Δ
  /-- Each new estimate is the largest candidate. -/
  step : ∀ k < K, IsGreatest (candidates832 g H M Δ iMax (lam k) : Set ℝ) (lam (k + 1))
  /-- The run stops at the first iteration meeting the exit test. -/
  exit : Optimization.IsFirstHit (exitTest ε lam) K

/-- **Algorithm 8.3.2 of [cartis2022evaluation] converges and terminates.** Let `Δ > 0`, `s*` a
global minimizer of (8.1.2) with multiplier `λ*`. If `λ₀ ∈ 𝓛` (so `λ* > λₛ`, the easy case), every
sequence of largest candidates from `λ₀` stays in `𝓛`, increases and converges to `λ*` globally
Q-linearly and Q-superlinearly; every run stays in `𝓛` and increases up to its exit; and a run of
Algorithm 8.3.2 from `λ₀` exists. -/
theorem algorithm_8_3_2_terminates (hH : H.IsHermitian) (hM : M.PosDef) {Δ : ℝ} (hΔ : 0 < Δ)
    {s : EuclideanSpace ℝ (Fin n)} (hs : IsTrustRegionSolution g H M Δ s) {lamStar : ℝ}
    (hkkt : IsTrustRegionKKT g H M Δ s lamStar) {iMax : ℕ} (hi : 1 ≤ iMax) {ε : ℝ} (hε : 0 < ε)
    {lam₀ : ℝ} (h₀ : lam₀ ∈ setL_tr hH hM g Δ) :
    (∀ x : ℕ → ℝ, x 0 = lam₀ →
      (∀ k, IsGreatest (candidates832 g H M Δ iMax (x k) : Set ℝ) (x (k + 1))) →
      (∀ k, x k ∈ setL_tr hH hM g Δ) ∧ Monotone x ∧ Tendsto x atTop (𝓝 lamStar) ∧
      (∃ γ ∈ Ico (0 : ℝ) 1, ∀ k, lamStar - x (k + 1) ≤ γ * (lamStar - x k)) ∧
      ConvergesSuperlinearly x lamStar) ∧
    (∀ (lam : ℕ → ℝ) (K : ℕ), algorithm_8_3_2 hH hM g Δ iMax ε lam K →
      (∀ k ≤ K, lam k ∈ setL_tr hH hM g Δ) ∧ (∀ k < K, lam k ≤ lam (k + 1)) ∧
        lam K ≤ lamStar) ∧
    ∃ lam K, algorithm_8_3_2 hH hM g Δ iMax ε lam K ∧ lam 0 = lam₀ := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hμ := (isTrustRegionKKT_iff_scaled hM hΔ).1 hkkt
  have hL := (setL_tr_eq_Ioc hH hM hΔ hs hkkt).2.1
  have heasy : lambdaS hH hM < lamStar := by
    have := h₀; rw [hL] at this; exact this.1.trans_le this.2
  have hstar : shiftThreshold hT < lamStar := by rwa [← lambdaS_eq]
  have hstar' := neg_leftmost_le_shiftThreshold.trans_lt hstar
  have hroot : secular (scaledGrad hM g) (scaledOp H hM) lamStar = Δ ^ 2 :=
    secular_eq_of_trustRegion hμ hstar
  have hg : scaledGrad hM g ≠ 0 := by
    intro h
    rw [h, secular_zero_left] at hroot
    exact (pow_pos hΔ 2).ne' hroot.symm
  have htgt : IsSecularTarget hT (scaledGrad hM g) (fun _ => Δ ^ 2) (shiftThreshold hT) lamStar :=
    ⟨hg, neg_leftmost_le_shiftThreshold, continuousOn_const, monotoneOn_const, hstar, hroot⟩
  have hLs : setL_tr hH hM g Δ = Ioc (shiftThreshold hT) lamStar := by rw [hL, lambdaS_eq]
  have hcand : ∀ lamc ∈ Ioc (shiftThreshold hT) lamStar,
      ∀ c ∈ candidates832 g H M Δ iMax lamc, lamc ≤ c ∧ c ≤ lamStar := by
    intro lamc hc c hcm
    simp only [candidates832, Finset.mem_insert, Finset.mem_image, Finset.mem_Icc] at hcm
    rcases hcm with rfl | ⟨i, ⟨hi1, -⟩, rfl⟩
    · rw [trNewtonCorrectionFn_eq hM]
      obtain ⟨h1, h2⟩ := trNewtonCorrection_mem hΔ hstar' hroot
        (neg_leftmost_le_shiftThreshold.trans_lt hc.1)
      exact ⟨h2 hc.2, h1⟩
    · rw [taylorCorrectionFn_eq hM]
      have hk : Odd (2 * i - 1) := ⟨i - 1, by omega⟩
      exact (htgt.taylorCorrection_mem hk hc).2.2
  have hseq : ∀ x : ℕ → ℝ, x 0 = lam₀ →
      (∀ k, IsGreatest (candidates832 g H M Δ iMax (x k) : Set ℝ) (x (k + 1))) →
      (∀ k, x k ∈ Ioc (shiftThreshold hT) lamStar) ∧ Monotone x := by
    intro x hx0 hx
    refine mem_Ioc_and_monotone (by rw [hx0, ← hLs]; exact h₀) fun k hk => ?_
    exact hcand _ hk _ (hx k).1
  have hnewton : ∀ x : ℕ → ℝ, x 0 = lam₀ →
      (∀ k, IsGreatest (candidates832 g H M Δ iMax (x k) : Set ℝ) (x (k + 1))) →
      Monotone x ∧ Tendsto x atTop (𝓝 lamStar) ∧
      (∃ γ ∈ Ico (0 : ℝ) 1, ∀ k, lamStar - x (k + 1) ≤ γ * (lamStar - x k)) ∧
      ConvergesSuperlinearly x lamStar := by
    intro x hx0 hx
    obtain ⟨hmem, -⟩ := hseq x hx0 hx
    have hstep : ∀ j, x j + trNewtonCorrection (scaledGrad hM g) (scaledOp H hM) Δ (x j) ≤
        x (j + 1) ∧ x (j + 1) ≤ lamStar := fun j => ⟨by
      rw [← trNewtonCorrectionFn_eq hM]
      exact (hx j).2 (Finset.mem_insert_self _ _), (hmem (j + 1)).2⟩
    obtain ⟨h1, h2, hγ, hlin, hsup⟩ := tendsto_of_trNewtonCorrection_le hΔ hstar' hroot
      ⟨neg_leftmost_le_shiftThreshold.trans_lt (hmem 0).1, (hmem 0).2⟩ hstep
    exact ⟨h1, h2, ⟨_, hγ, hlin⟩, hsup⟩
  refine ⟨fun x hx0 hx => ?_, fun lam K hrun => ?_, ?_⟩
  · obtain ⟨hmem, -⟩ := hseq x hx0 hx
    exact ⟨fun k => hLs ▸ hmem k, hnewton x hx0 hx⟩
  · have hmem := mem_Ioc_of_le (K := K) (by rw [← hLs]; exact hrun.start)
      fun k hk hm => hcand _ hm _ (hrun.step k hk).1
    exact ⟨fun k hk => hLs ▸ hmem k hk, fun k hk => (hcand _ (hmem k hk.le) _ (hrun.step k hk).1).1,
      (hmem K le_rfl).2⟩
  · have hne : ∀ t, (candidates832 g H M Δ iMax t).Nonempty := fun _ =>
      Finset.insert_nonempty _ _
    obtain ⟨x, hx0, hx⟩ := exists_isGreatest_seq _ hne lam₀
    obtain ⟨K, hK⟩ := Optimization.exists_isFirstHit (exists_exitTest (hnewton x hx0 hx).2.1 hε)
    exact ⟨x, K, ⟨hi, hε, hx0 ▸ h₀, fun k _ => hx k, hK⟩, hx0⟩

/-! ### Global minimizers -/

/-- The **minimum-`M`-norm solution** `sₛ = -(H + λ M)⁺ g` of [cartis2022evaluation] (8.3.2): when
`g ⊥ ker (H + λ M)`, the solution of `(H + λ M) x = -g` that is `M`-orthogonal to
`ker (H + λ M)`, equivalently of least `M`-norm (`minNormSolution_spec`); it is the limit of
`s(λ')` as `λ' ↓ λ = -λ₁` (`Subproblem.tendsto_step_threshold`). -/
noncomputable def minNormSolution (hH : H.IsHermitian) (hM : M.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (lam : ℝ) : EuclideanSpace ℝ (Fin n) :=
  (toScaled hM).symm (particular (isSymmetric_scaledOp hH) (scaledGrad hM g) lam)

theorem toScaled_minNormSolution (hH : H.IsHermitian) (hM : M.PosDef) (lam : ℝ) :
    toScaled hM (minNormSolution hH hM g lam) =
      particular (isSymmetric_scaledOp hH) (scaledGrad hM g) lam :=
  (toScaled hM).apply_symm_apply _

/-- **Characterization of the minimum-`M`-norm solution** (8.3.2): if `g ⊥ ker (H + λ M)` then `sₛ`
solves `(H + λ M) sₛ = -g`, is `M`-orthogonal to `ker (H + λ M)`, and has the least `M`-norm among
the solutions; it is the only `M`-orthogonal solution. -/
theorem minNormSolution_spec (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ}
    (hg : g ∈ (LinearMap.ker (toEuclideanLin (H + lam • M)))ᗮ) :
    toEuclideanLin (H + lam • M) (minNormSolution hH hM g lam) = -g ∧
      (∀ v ∈ LinearMap.ker (toEuclideanLin (H + lam • M)),
        ⟪toEuclideanLin M (minNormSolution hH hM g lam), v⟫ = 0) ∧
      (∀ y, toEuclideanLin (H + lam • M) y = -g →
        mNorm M (minNormSolution hH hM g lam) ≤ mNorm M y) ∧
      ∀ x, (toEuclideanLin (H + lam • M) x = -g ∧
        ∀ v ∈ LinearMap.ker (toEuclideanLin (H + lam • M)), ⟪toEuclideanLin M x, v⟫ = 0) →
        x = minNormSolution hH hM g lam := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hiff := toScaled_eq_particular_iff (hM := hM) hH hg
  have hg' := (scaledGrad_mem_orthogonal_iff (H := H) (hM := hM) lam g).2 hg
  obtain ⟨-, -, hmin, -⟩ := (particular_spec (hH := hT) (g := scaledGrad hM g) lam).2.1 hg'
  obtain ⟨h1, h2⟩ := (hiff _).1 (toScaled_minNormSolution hH hM lam)
  refine ⟨h1, h2, fun y hy => ?_, fun x hx => ?_⟩
  · rw [mNorm_eq_norm_toScaled hM, mNorm_eq_norm_toScaled hM, toScaled_minNormSolution]
    exact hmin _ ((add_smul_scaledOp_toScaled_eq_neg_iff lam g y).2 hy)
  · exact (toScaled hM).injective ((hiff x).2 hx |>.trans (toScaled_minNormSolution hH hM lam).symm)

/-- **The limit of the step at the threshold** ([cartis2022evaluation] §8.3.1): if
`g ⊥ ker (H - λ₁ M)` then `s(λ) → sₛ = minNormSolution hH hM g (-λ₁)` as `λ ↓ -λ₁`. -/
theorem tendsto_stepOf_minNormSolution (hH : H.IsHermitian) (hM : M.PosDef)
    (hg : g ∈ (LinearMap.ker (toEuclideanLin (H + (-leftmostPencil hH hM) • M)))ᗮ) :
    Tendsto (stepOf g H M) (𝓝[>] (-leftmostPencil hH hM))
      (𝓝 (minNormSolution hH hM g (-leftmostPencil hH hM))) := by
  rw [leftmostPencil_eq] at hg ⊢
  have hg' := (scaledGrad_mem_orthogonal_iff (H := H) (hM := hM) _ g).2 hg
  have h := ((tendsto_step_threshold (hH := isSymmetric_scaledOp (hM := hM) hH)
    (g := scaledGrad hM g)).1 hg').1
  have hc : Continuous (toScaled hM).symm :=
    (toScaled hM).symm.toContinuousLinearEquiv.continuous
  have := (hc.tendsto _).comp h
  refine this.congr fun lam => ?_
  simp only [Function.comp_apply, ← toScaled_stepOf hM, LinearEquiv.symm_apply_apply]

/-- In the hard case `λ* = -λ₁`, a vector of `ker (M⁻¹ H - λ₁)` is, transported back, `α v` for a
**nonzero** generalized eigenvector `v` of `(H, M)` for `λ₁` (`n ≥ 1`). -/
theorem exists_eigen_smul_of_mem_ker [NeZero n] (hH : H.IsHermitian) (hM : M.PosDef) {μ : ℝ}
    (hμ : μ = -leftmost (isSymmetric_scaledOp (hM := hM) hH)) {w : ScaledSpace hM}
    (hw : w ∈ LinearMap.ker ((scaledOp H hM + μ • 1 : ScaledSpace hM →L[ℝ] ScaledSpace hM) :
      ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)) :
    ∃ v : EuclideanSpace ℝ (Fin n), v ≠ 0 ∧ ∃ α : ℝ,
      toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v ∧
        (toScaled hM).symm w = α • v := by
  rcases eq_or_ne w 0 with rfl | hw0
  · have hT := isSymmetric_scaledOp (hM := hM) hH
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hT)
    obtain ⟨u, hu, heig⟩ := exists_eigen_of_eigenvalues (hM := hM) hH i
    exact ⟨u, hu, 0, by rw [leftmostPencil_eq, ← hi]; exact heig, by simp⟩
  · refine ⟨(toScaled hM).symm w, by simpa using hw0, 1, ?_, (one_smul _ _).symm⟩
    rw [eigen_of_mem_ker hw, hμ, neg_neg, leftmostPencil_eq]

/-- **Corollary 8.3.1 of [cartis2022evaluation] (Global minimizers of the regularization
subproblem).** Let `n ≥ 1`, `r > 2`, `σ > 0`, `s*` a global minimizer of (8.1.3),
`λ* = σ ‖s*‖_M^{r-2}`, `sₛ = minNormSolution hH hM g λ*` (8.3.2) and `λ₁` the leftmost pencil
eigenvalue. Then `λ* ≥ -λ₁`, and (8.3.1): if `λ* > -λ₁` then `s* = sₛ`, the unique global
minimizer; if `λ* = -λ₁` then `s* = sₛ + α v` for a (nonzero) generalized eigenvector `v` of
`(H, M)` for `λ₁` and a root `α` of `‖sₛ + α v‖_M = (λ*/σ)^{1/(r-2)}`. In all cases the optimal
value is (8.3.3): `m^R(s*) = ½ (⟪g, sₛ⟫ - (r-2)/r λ* (λ*/σ)^{2/(r-2)})`. -/
theorem corollary_8_3_1 [NeZero n] (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} (hσ : 0 < σ)
    (hr : 2 < r) {s : EuclideanSpace ℝ (Fin n)} (hs : IsRegularizationSolution g H M σ r s) :
    -leftmostPencil hH hM ≤ σ * mNorm M s ^ (r - 2) ∧
    (-leftmostPencil hH hM < σ * mNorm M s ^ (r - 2) →
      s = minNormSolution hH hM g (σ * mNorm M s ^ (r - 2)) ∧
        ∀ u, IsRegularizationSolution g H M σ r u → u = s) ∧
    (σ * mNorm M s ^ (r - 2) = -leftmostPencil hH hM →
      ∃ v : EuclideanSpace ℝ (Fin n), v ≠ 0 ∧ ∃ α : ℝ,
        toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v ∧
        s = minNormSolution hH hM g (σ * mNorm M s ^ (r - 2)) + α • v ∧
        mNorm M (minNormSolution hH hM g (σ * mNorm M s ^ (r - 2)) + α • v) =
          (σ * mNorm M s ^ (r - 2) / σ) ^ (1 / (r - 2))) ∧
    regModel g H M σ r s = 1 / 2 * (⟪g, minNormSolution hH hM g (σ * mNorm M s ^ (r - 2))⟫ -
      (r - 2) / r * (σ * mNorm M s ^ (r - 2)) * (σ * mNorm M s ^ (r - 2) / σ) ^ (2 / (r - 2))) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hmin := (isRegularizationSolution_iff_scaled hM).1 hs
  obtain ⟨hle, hker, -, hstep⟩ := shiftThreshold_le_of_isMinOn_regModel (hH := hT) hσ hr hmin
  have hn := mNorm_eq_norm_toScaled hM s
  rw [hn]
  refine ⟨?_, fun hlt => ⟨?_, fun u hu => ?_⟩, fun heq => ?_, ?_⟩
  · rw [leftmostPencil_eq]; exact neg_leftmost_le_shiftThreshold.trans hle
  · rw [leftmostPencil_eq] at hlt
    exact (toScaled hM).injective ((hstep hlt).1.trans (toScaled_minNormSolution hH hM _).symm)
  · rw [leftmostPencil_eq] at hlt
    have hc := ((isSymmetricCoercive_add_smul_iff (hH := hT) _).2 hlt).isCoercive
    exact (toScaled hM).injective (eq_of_isMinOn_regModel_of_posDef hT hσ hr hmin hc
      ((isRegularizationSolution_iff_scaled hM).1 hu))
  · rw [leftmostPencil_eq] at heq
    set w := toScaled hM s - particular hT (scaledGrad hM g) (σ * ‖toScaled hM s‖ ^ (r - 2))
    obtain ⟨v, hv0, α, heig, hwv⟩ := exists_eigen_smul_of_mem_ker hH hM heq hker
    have hsum : minNormSolution hH hM g (σ * ‖toScaled hM s‖ ^ (r - 2)) + α • v = s := by
      apply (toScaled hM).injective
      rw [map_add, toScaled_minNormSolution, ← hwv, LinearEquiv.apply_symm_apply, add_sub_cancel]
    refine ⟨v, hv0, α, heig, hsum.symm, ?_⟩
    have hσ0 : σ * ‖toScaled hM s‖ ^ (r - 2) / σ = ‖toScaled hM s‖ ^ (r - 2) := by field_simp
    rw [hsum, hn, hσ0, one_div, Real.rpow_rpow_inv (norm_nonneg _) (sub_pos.2 hr).ne']
  · rw [regModel_eq_regModel hM, optimalValue_eq_of_regularization (hH := hT) hσ hr hmin,
      ← toScaled_minNormSolution hH hM, inner_scaledGrad_toScaled]

/-- **Corollary 8.3.2 of [cartis2022evaluation] (Global minimizers of the trust-region
subproblem)**, corrected. Let `n ≥ 1`, `Δ > 0`, `s*` a global minimizer of (8.1.2) with multiplier
`λ*` (`IsTrustRegionKKT`: `λ* ≥ 0`, `λ* (‖s*‖_M² - Δ²) = 0`), `sₛ = minNormSolution hH hM g λ*`.
Then `λ* ≥ -λ₁`; if `λ* > -λ₁` then `s* = sₛ`, the unique global minimizer; if `λ* = -λ₁` then
`s* = sₛ + α v` for a (nonzero) generalized eigenvector `v` for `λ₁` with `‖sₛ + α v‖_M ≤ Δ`, and
`‖sₛ + α v‖_M = Δ` when `λ* > 0` (the book's boundary condition fails for `λ* = 0`). The optimal
value is (8.3.5): `m(s*) = ½ (⟪g, sₛ⟫ - λ* Δ²)`. -/
theorem corollary_8_3_2 [NeZero n] (hH : H.IsHermitian) (hM : M.PosDef) {Δ : ℝ} (hΔ : 0 < Δ)
    {s : EuclideanSpace ℝ (Fin n)} (hs : IsTrustRegionSolution g H M Δ s) {lamStar : ℝ}
    (hkkt : IsTrustRegionKKT g H M Δ s lamStar) :
    -leftmostPencil hH hM ≤ lamStar ∧
    (-leftmostPencil hH hM < lamStar →
      s = minNormSolution hH hM g lamStar ∧ ∀ u, IsTrustRegionSolution g H M Δ u → u = s) ∧
    (lamStar = -leftmostPencil hH hM →
      ∃ v : EuclideanSpace ℝ (Fin n), v ≠ 0 ∧ ∃ α : ℝ,
        toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v ∧
        s = minNormSolution hH hM g lamStar + α • v ∧
        mNorm M (minNormSolution hH hM g lamStar + α • v) ≤ Δ ∧
        (0 < lamStar → mNorm M (minNormSolution hH hM g lamStar + α • v) = Δ)) ∧
    model g H s = 1 / 2 * (⟪g, minNormSolution hH hM g lamStar⟫ - lamStar * Δ ^ 2) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  obtain ⟨hn, hmin⟩ := (isTrustRegionSolution_iff_scaled hM).1 hs
  have hμ := (isTrustRegionKKT_iff_scaled hM hΔ).1 hkkt
  obtain ⟨hle, hker, -, hstep⟩ := shiftThreshold_le_of_isTrustRegionMultiplier (hH := hT) hμ
  refine ⟨?_, fun hlt => ⟨?_, fun u hu => ?_⟩, fun heq => ?_, ?_⟩
  · rw [leftmostPencil_eq]; exact neg_leftmost_le_shiftThreshold.trans hle
  · rw [leftmostPencil_eq] at hlt
    exact (toScaled hM).injective ((hstep hlt).1.trans (toScaled_minNormSolution hH hM _).symm)
  · rw [leftmostPencil_eq] at hlt
    have hc := ((isSymmetricCoercive_add_smul_iff (hH := hT) _).2 hlt).isCoercive
    obtain ⟨hun, humin⟩ := (isTrustRegionSolution_iff_scaled hM).1 hu
    exact (toScaled hM).injective (eq_of_isMinOn_closedBall_of_posDef hT hμ hn hc hun humin)
  · rw [leftmostPencil_eq] at heq
    set w := toScaled hM s - particular hT (scaledGrad hM g) lamStar
    obtain ⟨v, hv0, α, heig, hwv⟩ := exists_eigen_smul_of_mem_ker hH hM heq hker
    have hsum : minNormSolution hH hM g lamStar + α • v = s := by
      apply (toScaled hM).injective
      rw [map_add, toScaled_minNormSolution, ← hwv, LinearEquiv.apply_symm_apply, add_sub_cancel]
    refine ⟨v, hv0, α, heig, hsum.symm, ?_, fun hpos => ?_⟩
    · rw [hsum, mNorm_eq_norm_toScaled hM]; exact hn
    · rw [hsum, mNorm_eq_norm_toScaled hM]; exact hμ.norm_eq_of_pos hpos
  · rw [model_eq_quadModel hM, optimalValue_eq_of_trustRegion (hH := hT) hμ,
      ← toScaled_minNormSolution hH hM, inner_scaledGrad_toScaled]

end CartisGouldToint.Chapter08
