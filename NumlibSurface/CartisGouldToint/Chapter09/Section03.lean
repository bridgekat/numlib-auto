import Numlib.Optimization.Subproblem.InverseIteration
import NumlibSurface.CartisGouldToint.Chapter08.Section03

/-!
# Cartis–Gould–Toint §9.3: The regularization subproblem

Surface file for [cartis2022evaluation] §9.3: initial bounds on the multiplier `λ*` of (8.1.3)
(§9.3.1, (9.3.3)–(9.3.5), generalized Gershgorin bounds (9.3.6)–(9.3.7)), the potential-hard-case
iteration (Algorithm 9.3.1, Theorem 9.3.1), monotonicity of `𝓛` in `σ` (§9.3.5) and the
constructive early-termination test (Theorem 9.3.2, (9.3.16)).

## Main definitions

* `rightmostPencil hH hM` — the largest pencil eigenvalue `λₙ`.
* `invIterVec H M λ z i` — `i` normalized inverse iterations `w ← (H + λ M)⁻¹ M w / ‖·‖_M`.
* `algorithm_9_3_1` — runs of Algorithm 9.3.1.
* `stoppingRules_9_3_14` — the early-termination requirements (9.3.14).
* `Matrix.offDiagSum` (backbone) — the off-diagonal row sums `o_kᴬ` of (9.3.6).
* `etaL`, `etaU` — the factors of (9.3.16).

## Main results

* `lambdaStar_bounds_9_3_3` — (9.3.3)–(9.3.5).
* `pencil_gershgorin_9_3_7` — (9.3.6)–(9.3.7) and the Rayleigh bound `λ₁ ≤ hᵢᵢ/mᵢᵢ`.
* `algorithm_9_3_1.isInverseIterationRun`, `theorem_9_3_1` — fast convergence in the hard case.
* `setL_reg_mono` — §9.3.5.
* `theorem_9_3_2`, `cubic_termination_9_3_16` — §9.3.6.

The safeguarded update (9.3.10)–(9.3.12) and the overall procedure of §9.3.7 combine these
heuristically and are not separately formalized; their admissible choices are covered by
`CartisGouldToint.Chapter09.algorithm_9_2_1`.

## Corrections to the source

* Theorem 9.3.1 omits the hypothesis `z₀ ∈ 𝒵₁` (footnote 64 notes that it is missing from the
  source paper; it is also missing from the printed theorem), and `𝒵₁` must be read in the
  `M`-inner product, `⟪z, M v⟫ ≠ 0` for a generalized eigenvector `v` for `λ₁` (the printed
  Euclidean `⟪z, vᵢ⟫ ≠ 0` is the right condition only for `M = I`; it is the hypothesis `z₀ ∈ 𝒵₁`
  of `theorem_9_3_1`, equivalent to `z₀` having a nonzero `M`-orthogonal component in the leftmost
  eigenspace). The parameter sequences `nₖ`, `ωₖ`, `γₖ` are fixed before the closeness `ε`, which
  depends on them (with `nₖ` eventually constant, as in the book; no single `ε` serves all runs
  when `n_U = ∞`, see `Subproblem.IsInverseIterationRun.convergence`); the Q-order `γ̄` is stated
  as two-sided bounds
  `c eₖ^γ̄ ≤ eₖ₊₁ ≤ C eₖ^γ̄`. Algorithm 9.3.1 assumes `λ₀ᴳ ∈ 𝓖`; only `H + λ₀ᴳ M ≻ 0` is used.
* Theorem 9.3.2: with the Euclidean `λ_min` in (9.3.14c) the theorem is false for `M ≠ I`, since
  (9.3.15c) only yields `∇²m^R(s) ⪰ -θ₂ ‖s‖_M M`; (9.3.14) is stated with the `M`-scalings of the
  primal and dual norms and of `λ_min` (`λ_min[∇²m^R(s), M]`), as the book's phrase "with the
  appropriate `M`-scalings" suggests.
* (9.3.6): the book's middle term `|∑_{i≠k} (h_ki - λ m_ki)|` drops the factors `uᵢ/u_k`
  (`|uᵢ/u_k| ≤ 1`) and is not a valid bound as printed; only the outer inequality
  `|h_kk - λ m_kk| ≤ o_kᴴ + |λ| o_kᴹ` is stated (`exists_abs_sub_le_of_eigen`, via
  `Matrix.exists_abs_sub_le_of_mulVec_eq`), which is what (9.3.7) uses.
* §9.3.1, `M = I`: the comparisons `‖H‖₂ ≤ min(‖H‖_∞, ‖H‖_F)` are standard facts quoted by the
  book and are not formalized (nor is `|λᵢ| ≤ ‖H‖_F`); the bounds `|λᵢ| ≤ ‖H‖₂` and
  `|λᵢ| ≤ ‖H‖_∞` are.
* §9.3.5: `𝓝 = (-∞, λₛ]` and `λₛ` depend only on `H` and `M`, not on `σ`, which is why `𝓝₊ = 𝓝`.
-/

open Matrix Set Filter Topology
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter09

open Subproblem CartisGouldToint.Chapter08

variable {n : ℕ} {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-! ### The extreme pencil eigenvalues -/

/-- The **rightmost eigenvalue** `λₙ` of the pencil `(H, M)` (the largest of
`Matrix.pencilEigenvalues hH hM`; `0` when `n = 0`). -/
noncomputable def rightmostPencil (hH : H.IsHermitian) (hM : M.PosDef) : ℝ :=
  ⨆ i, pencilEigenvalues hH hM i

/-- The rightmost pencil eigenvalue is the rightmost eigenvalue of the scaled operator. -/
theorem rightmostPencil_eq (hH : H.IsHermitian) (hM : M.PosDef) :
    rightmostPencil hH hM = rightmost (isSymmetric_scaledOp (hM := hM) hH) :=
  (rightmost_scaledOp hH).symm

/-! ### Initial bounds on `λ*` (§9.3.1) -/

/-- **Bounds on the multiplier, regularization** ([cartis2022evaluation] (9.3.1)–(9.3.5)). Let
`σ > 0`, `r > 2`, `s*` a global minimizer of (8.1.3), `λ* = σ ‖s*‖_M^{r-2}`, `λ₁ ≤ λₙ` the extreme
pencil eigenvalues, `p = 1/(r-2)` and `c = σ^p ‖g‖_{M⁻¹}`. Then `λ* ≥ λₛ` and
`(λ* + λ₁) λ*^p ≤ c ≤ (λ* + λₙ) λ*^p` (9.3.3); the same holds with outer bounds `λ₁ᴸ ≤ λ₁`,
`λₙᵁ ≥ λₙ` (9.3.4); and if `λᵁ` is the rightmost root on `λ ≥ 0` of `(λ + λ₁ᴸ) λ^p = c` and `λᴸ ≥ 0`
is a root of `(λ + λₙᵁ) λ^p = c` (9.3.5; the book takes the rightmost one) then
`λᴸ ≤ λ* ≤ λᵁ` (9.2.1). -/
theorem lambdaStar_bounds_9_3_3 (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} (hσ : 0 < σ)
    (hr : 2 < r) {s : EuclideanSpace ℝ (Fin n)} (hs : IsRegularizationSolution g H M σ r s) :
    lambdaS hH hM ≤ σ * mNorm M s ^ (r - 2) ∧
    (σ * mNorm M s ^ (r - 2) + leftmostPencil hH hM) * (σ * mNorm M s ^ (r - 2)) ^ (1 / (r - 2)) ≤
      σ ^ (1 / (r - 2)) * mNorm M⁻¹ g ∧
    σ ^ (1 / (r - 2)) * mNorm M⁻¹ g ≤
      (σ * mNorm M s ^ (r - 2) + rightmostPencil hH hM) *
        (σ * mNorm M s ^ (r - 2)) ^ (1 / (r - 2)) ∧
    ∀ l₁ lₙ : ℝ, l₁ ≤ leftmostPencil hH hM → rightmostPencil hH hM ≤ lₙ →
      (σ * mNorm M s ^ (r - 2) + l₁) * (σ * mNorm M s ^ (r - 2)) ^ (1 / (r - 2)) ≤
        σ ^ (1 / (r - 2)) * mNorm M⁻¹ g ∧
      σ ^ (1 / (r - 2)) * mNorm M⁻¹ g ≤
        (σ * mNorm M s ^ (r - 2) + lₙ) * (σ * mNorm M s ^ (r - 2)) ^ (1 / (r - 2)) ∧
      ∀ lamL lamU : ℝ,
        IsGreatest {lam | 0 ≤ lam ∧ (lam + l₁) * lam ^ (1 / (r - 2)) =
          σ ^ (1 / (r - 2)) * mNorm M⁻¹ g} lamU →
        0 ≤ lamL → (lamL + lₙ) * lamL ^ (1 / (r - 2)) = σ ^ (1 / (r - 2)) * mNorm M⁻¹ g →
        lamL ≤ σ * mNorm M s ^ (r - 2) ∧ σ * mNorm M s ^ (r - 2) ≤ lamU := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hmin := (isRegularizationSolution_iff_scaled hM).1 hs
  have hle := (CartisGouldToint.Chapter08.setL_reg_eq_Ioc hH hM hσ hr hs).1
  obtain ⟨hsh, -⟩ := (isMinOn_regModel_iff hT hσ hr).1 hmin
  rw [mNorm_inv_eq_norm_scaledGrad hM, leftmostPencil_eq, rightmostPencil_eq,
    mNorm_eq_norm_toScaled hM]
  rw [mNorm_eq_norm_toScaled hM] at hle
  set μ := σ * ‖toScaled hM s‖ ^ (r - 2) with hμdef
  set p := 1 / (r - 2) with hpdef
  have hp : 0 < p := by rw [hpdef]; exact one_div_pos.2 (sub_pos.2 hr)
  have hμ0 : 0 ≤ μ := (lambdaS_nonneg hH hM).trans hle
  have hμl : -leftmost hT ≤ μ := by
    rw [lambdaS_eq] at hle; exact neg_leftmost_le_shiftThreshold.trans hle
  have hns : ‖toScaled hM s‖ = (μ / σ) ^ p := by
    rw [hμdef, mul_div_cancel_left₀ _ hσ.ne', hpdef, one_div,
      Real.rpow_rpow_inv (norm_nonneg _) (sub_pos.2 hr).ne']
  have hσp : 0 < σ ^ p := Real.rpow_pos_of_pos hσ p
  have hmul : σ ^ p * (μ / σ) ^ p = μ ^ p := by
    rw [Real.div_rpow hμ0 hσ.le]; field_simp
  obtain ⟨hb1, hb2⟩ := norm_add_smul_apply_bounds (hH := hT) hμl (toScaled hM s)
  rw [hsh, norm_neg, hns] at hb1 hb2
  have hlow : (μ + leftmost hT) * μ ^ p ≤ σ ^ p * ‖scaledGrad hM g‖ := by
    rw [← hmul, mul_left_comm]; exact mul_le_mul_of_nonneg_left hb1 hσp.le
  have hup : σ ^ p * ‖scaledGrad hM g‖ ≤ (μ + rightmost hT) * μ ^ p := by
    rw [← hmul, mul_left_comm]; exact mul_le_mul_of_nonneg_left hb2 hσp.le
  have hμp : 0 ≤ μ ^ p := Real.rpow_nonneg hμ0 p
  refine ⟨hle, hlow, hup, fun l₁ lₙ hl₁ hlₙ => ?_⟩
  set c := σ ^ p * ‖scaledGrad hM g‖ with hc
  have hc0 : 0 ≤ c := mul_nonneg hσp.le (norm_nonneg _)
  have hlow' : (μ + l₁) * μ ^ p ≤ c :=
    (mul_le_mul_of_nonneg_right (by linarith) hμp).trans hlow
  have hup' : c ≤ (μ + lₙ) * μ ^ p :=
    hup.trans (mul_le_mul_of_nonneg_right (by linarith) hμp)
  refine ⟨hlow', hup', fun lamL lamU hU hL0 hL => ⟨?_, ?_⟩⟩
  · by_contra hlt
    push Not at hlt
    have hμn : 0 ≤ μ + lₙ := by linarith [leftmost_le_rightmost (hH := hT)]
    have h1 : (μ + lₙ) * μ ^ p ≤ (μ + lₙ) * lamL ^ p :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hμ0 hlt.le hp.le) hμn
    have h2 : (μ + lₙ) * lamL ^ p < (lamL + lₙ) * lamL ^ p :=
      mul_lt_mul_of_pos_right (by linarith) (Real.rpow_pos_of_pos (hμ0.trans_lt hlt) p)
    linarith
  · by_contra hlt
    push Not at hlt
    set T := max (max μ 1) (c - l₁)
    have hμT : μ ≤ T := (le_max_left _ _).trans (le_max_left _ _)
    have h1T : 1 ≤ T := (le_max_right _ _).trans (le_max_left _ _)
    have hcT : c - l₁ ≤ T := le_max_right _ _
    have hfT : c ≤ (T + l₁) * T ^ p :=
      (by linarith : c ≤ T + l₁).trans (le_mul_of_one_le_right (by linarith)
        (Real.one_le_rpow h1T hp.le))
    have hcont : ContinuousOn (fun t : ℝ => (t + l₁) * t ^ p) (Icc μ T) :=
      ((continuous_id.add continuous_const).mul (Real.continuous_rpow_const hp.le)).continuousOn
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hμT hcont ⟨hlow', hfT⟩
    have := hU.2 ⟨hμ0.trans ht.1, hft⟩
    linarith [ht.1]

/-! ### Generalized Gershgorin bounds (9.3.6)–(9.3.7) -/

/-- **Gershgorin for the pencil** ((9.3.6)–(9.3.7)): every generalized eigenvalue `μ` of `(H, M)`
satisfies `|h_kk - μ m_kk| ≤ o_kᴴ + |μ| o_kᴹ` for some `k`. -/
theorem exists_abs_sub_le_of_eigen {μ : ℝ} {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0)
    (h : toEuclideanLin H u = μ • toEuclideanLin M u) :
    ∃ k, |H k k - μ * M k k| ≤ offDiagSum H k + |μ| * offDiagSum M k := by
  refine exists_abs_sub_le_of_mulVec_eq (u := WithLp.ofLp u)
    (fun h0 => hu (by simpa using congrArg (WithLp.toLp 2) h0)) ?_
  have := congrArg WithLp.ofLp h
  simpa only [toEuclideanLin_apply, WithLp.ofLp_smul] using this

/-- **Generalized Gershgorin bounds** ([cartis2022evaluation] (9.3.6)–(9.3.7) and §9.3.1), for
`n ≥ 1`. Every generalized eigenvalue `μ` of `(H, M)` satisfies `|h_kk - μ m_kk| ≤ o_kᴴ + |μ| o_kᴹ`
for some `k`; if `M` is strictly diagonally dominant (`o_kᴹ < m_kk`) each such region is the
interval of `mem_gershgorin_interval` and
`λ₁ ≥ min_k min((h_kk - o_kᴴ)/(m_kk - o_kᴹ), (h_kk - o_kᴴ)/(m_kk + o_kᴹ))`,
`λₙ ≤ max_k max((h_kk + o_kᴴ)/(m_kk - o_kᴹ), (h_kk + o_kᴴ)/(m_kk + o_kᴹ))`. Moreover
`λ₁ ≤ min_i h_ii/m_ii`, and for `M = I` every eigenvalue satisfies `|μ| ≤ ‖H‖₂` and
`|μ| ≤ ‖H‖_∞ = max_k ∑_j |h_kj|`. -/
theorem pencil_gershgorin_9_3_7 [NeZero n] (hH : H.IsHermitian) (hM : M.PosDef) :
    (∀ (μ : ℝ) (u : EuclideanSpace ℝ (Fin n)), u ≠ 0 →
      toEuclideanLin H u = μ • toEuclideanLin M u →
      ∃ k, |H k k - μ * M k k| ≤ offDiagSum H k + |μ| * offDiagSum M k) ∧
    ((∀ k, offDiagSum M k < M k k) →
      (⨅ k, min ((H k k - offDiagSum H k) / (M k k - offDiagSum M k))
          ((H k k - offDiagSum H k) / (M k k + offDiagSum M k))) ≤ leftmostPencil hH hM ∧
        rightmostPencil hH hM ≤ ⨆ k, max ((H k k + offDiagSum H k) / (M k k - offDiagSum M k))
          ((H k k + offDiagSum H k) / (M k k + offDiagSum M k))) ∧
    (∀ i, leftmostPencil hH hM ≤ H i i / M i i) ∧
    (M = 1 → ∀ (μ : ℝ) (u : EuclideanSpace ℝ (Fin n)), u ≠ 0 → toEuclideanLin H u = μ • u →
      |μ| ≤ ‖LinearMap.toContinuousLinearMap (toEuclideanLin H)‖ ∧
        |μ| ≤ ⨆ k, ∑ j, |H k j|) := by
  set hT := isSymmetric_scaledOp (hM := hM) hH
  have hfin : Nonempty (Fin (Module.finrank ℝ (ScaledSpace hM))) :=
    ⟨⟨0, Module.finrank_pos⟩⟩
  refine ⟨fun μ u hu h => exists_abs_sub_le_of_eigen hu h, fun hdd => ⟨?_, ?_⟩, fun i => ?_,
    fun h1 μ u hu h => ⟨?_, ?_⟩⟩
  · obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hT)
    obtain ⟨u, hu, heig⟩ := exists_eigen_of_eigenvalues (hM := hM) hH i
    obtain ⟨k, hk⟩ := exists_abs_sub_le_of_eigen hu heig
    refine (ciInf_le (Set.finite_range _).bddBelow k).trans ?_
    rw [leftmostPencil_eq, ← hi]
    exact (mem_gershgorin_interval (offDiagSum_nonneg M k) (hdd k) hk).1
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => hT.eigenvalues rfl i)
    obtain ⟨u, hu, heig⟩ := exists_eigen_of_eigenvalues (hM := hM) hH i
    obtain ⟨k, hk⟩ := exists_abs_sub_le_of_eigen hu heig
    refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove k)
    rw [rightmostPencil_eq, rightmost, ← hi]
    exact (mem_gershgorin_interval (offDiagSum_nonneg M k) (hdd k) hk).2
  · have hv := leftmost_mul_norm_sq_le (hH := hT) (toScaled hM (EuclideanSpace.single i 1))
    rw [norm_toScaled_sq, real_inner_comm, ← real_inner_comm (toScaled hM _),
      inner_scaledOp_toScaled] at hv
    simp only [toEuclideanLin_apply, PiLp.ofLp_single, mulVec_single,
      EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left, one_mul, map_one] at hv
    rw [leftmostPencil_eq, le_div_iff₀ hM.diag_pos]
    simpa [mul_comm] using hv
  · have hle := (LinearMap.toContinuousLinearMap (toEuclideanLin H)).le_opNorm u
    rw [LinearMap.coe_toContinuousLinearMap', h, norm_smul, Real.norm_eq_abs] at hle
    exact le_of_mul_le_mul_right hle (norm_pos_iff.2 hu)
  · subst h1
    obtain ⟨k, hk⟩ := exists_abs_sub_le_of_eigen (H := H) (M := 1) hu
      (by rw [toEuclideanLin_one_apply]; exact h)
    have h0 : offDiagSum (1 : Matrix (Fin n) (Fin n) ℝ) k = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [one_apply_ne' (Finset.ne_of_mem_erase hi)]
    rw [h0, mul_zero, add_zero, one_apply_eq, mul_one] at hk
    have hsum : ∑ j, |H k j| = |H k k| + offDiagSum H k :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
    refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove k)
    rw [hsum]
    have := abs_sub_abs_le_abs_sub μ (H k k)
    rw [abs_sub_comm] at this
    linarith

/-! ### Algorithm 9.3.1 and Theorem 9.3.1 -/

/-- `n` normalized inverse iterations of [cartis2022evaluation] Algorithm 9.3.1 with shift `λ`:
`w₀ = z` and `wᵢ = vᵢ / ‖vᵢ‖_M` with `vᵢ = (H + λ M)⁻¹ M wᵢ₋₁`. -/
noncomputable def invIterVec (H M : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => z
  | i + 1 =>
    (mNorm M (toEuclideanLin (H + lam • M)⁻¹ (toEuclideanLin M (invIterVec H M lam z i))))⁻¹ •
      toEuclideanLin (H + lam • M)⁻¹ (toEuclideanLin M (invIterVec H M lam z i))

/-- A **run of Algorithm 9.3.1** of [cartis2022evaluation] (potential hard case): constants
`0 < ω_L ≤ ω_U`, `0 < γ_U ≤ 1`, `1 < γ_L ≤ 2 - γ_U`, `1 ≤ n_U ≤ ∞`; shifts `λᴳₖ` with
`H + λᴳ₀ M` positive definite (the book's `λᴳ₀ ∈ 𝓖`), unit vectors `zₖ` (`‖z₀‖_M = 1`), and at each
step `1 ≤ nₖ ≤ n_U` inverse iterations from `zₖ` with shift `λᴳₖ` give `zₖ₊₁`, with Rayleigh
quotient `ρ = ⟪zₖ₊₁, H zₖ₊₁⟫`, and `λᴳₖ₊₁ = -ρ + ωₖ (λᴳₖ + ρ)^{γₖ}` for some `ωₖ ∈ [ω_L, ω_U]`,
`γₖ ∈ [γ_L, 2nₖ - γ_U]`. -/
structure algorithm_9_3_1 (hH : H.IsHermitian) (hM : M.PosDef) (ωL ωU γL γU : ℝ) (nU : ℕ∞)
    (lamG : ℕ → ℝ) (z : ℕ → EuclideanSpace ℝ (Fin n)) (nk : ℕ → ℕ) (ω γ : ℕ → ℝ) : Prop where
  /-- The constants of the algorithm. -/
  constants : 0 < ωL ∧ ωL ≤ ωU ∧ 0 < γU ∧ γU ≤ 1 ∧ 1 < γL ∧ γL ≤ 2 - γU ∧ 1 ≤ nU
  /-- The initial vector is a unit vector in the `M`-norm. -/
  norm_zero : mNorm M (z 0) = 1
  /-- The initial shift makes `H + λᴳ₀ M` positive definite. -/
  start : (H + lamG 0 • M).PosDef
  /-- The numbers of inverse iterations. -/
  count : ∀ k, 1 ≤ nk k ∧ (nk k : ℕ∞) ≤ nU
  /-- The weights. -/
  weight_mem : ∀ k, ω k ∈ Icc ωL ωU
  /-- The exponents. -/
  exponent_mem : ∀ k, γ k ∈ Icc γL (2 * nk k - γU)
  /-- The inverse iterations. -/
  vector_succ : ∀ k, z (k + 1) = invIterVec H M (lamG k) (z k) (nk k)
  /-- The shift update. -/
  shift_succ : ∀ k, lamG (k + 1) = -⟪z (k + 1), toEuclideanLin H (z (k + 1))⟫ +
    ω k * (lamG k + ⟪z (k + 1), toEuclideanLin H (z (k + 1))⟫) ^ γ k

/-- The inner iterations of Algorithm 9.3.1 are, transported, the normalized powers of the
inverse of the shifted scaled operator. -/
theorem toScaled_invIterVec (hM : M.PosDef) (lam : ℝ) (z : EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    toScaled hM (invIterVec H M lam z (i + 1)) =
      ‖(Ring.inverse (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM)) ^ (i + 1))
          (toScaled hM z)‖⁻¹ •
        (Ring.inverse (scaledOp H hM + lam • (1 : ScaledSpace hM →L[ℝ] ScaledSpace hM)) ^ (i + 1))
          (toScaled hM z) := by
  refine normalize_iterate _ (w := fun j => toScaled hM (invIterVec H M lam z j)) rfl
    (fun j => ?_) i
  simp only [invIterVec, map_smul, mNorm_eq_norm_toScaled hM, toScaled_inv_mul_apply,
    NormedSpace.normalize]

/-- **Algorithm 9.3.1 in the scaled setting**: a run of Algorithm 9.3.1 is, transported to the
`M`-inner product space, a run of `Subproblem.IsInverseIterationRun` for `M⁻¹ H`. -/
theorem algorithm_9_3_1.isInverseIterationRun (hH : H.IsHermitian) (hM : M.PosDef)
    {ωL ωU γL γU : ℝ} {nU : ℕ∞} {lamG : ℕ → ℝ} {z : ℕ → EuclideanSpace ℝ (Fin n)}
    {nk : ℕ → ℕ} {ω γ : ℕ → ℝ} (h : algorithm_9_3_1 hH hM ωL ωU γL γU nU lamG z nk ω γ) :
    IsInverseIterationRun (isSymmetric_scaledOp (hM := hM) hH) ωL ωU γL γU nU lamG
      (fun k => toScaled hM (z k)) nk ω γ := by
  have hrq : ∀ x : EuclideanSpace ℝ (Fin n),
      ⟪toScaled hM x, scaledOp H hM (toScaled hM x)⟫ = ⟪x, toEuclideanLin H x⟫ := fun x => by
    rw [real_inner_comm, inner_scaledOp_toScaled, real_inner_comm]
  refine ⟨by rw [← mNorm_eq_norm_toScaled hM]; exact h.norm_zero, ?_, fun k => (h.count k).1,
    fun k => (h.count k).2, h.weight_mem, h.exponent_mem, fun k => ?_, fun k => ?_⟩
  · rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · have := h.norm_zero
      rw [Subsingleton.elim (z 0) 0, mNorm, inner_zero_left, Real.sqrt_zero] at this
      exact absurd this zero_ne_one
    · have : NeZero n :=
        ⟨fun h0 => by subst h0; exact (not_isEmpty_of_nonempty (Fin 0)) inferInstance⟩
      exact neg_leftmost_lt_of_posDef hH hM h.start
  · obtain ⟨m, hm⟩ : ∃ m, nk k = m + 1 := ⟨nk k - 1, by have := (h.count k).1; omega⟩
    simp only [h.vector_succ k, hm, toScaled_invIterVec hM]
  · simp only [h.shift_succ k, hrq]

/-- The start condition `z₀ ∈ 𝒵₁` in the `M`-inner product, `⟪z₀, M v⟫ ≠ 0` for a generalized
eigenvector `v` for `λ₁`, says that `z₀` has a nonzero component in the leftmost eigenspace of the
scaled operator. -/
theorem starProjection_ne_zero_of_mem_Z₁ (hH : H.IsHermitian) (hM : M.PosDef)
    {z₀ : EuclideanSpace ℝ (Fin n)}
    (hz₀ : ∃ v : EuclideanSpace ℝ (Fin n),
      toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v ∧
        ⟪z₀, toEuclideanLin M v⟫ ≠ 0) :
    (leftmostSpace (isSymmetric_scaledOp (hM := hM) hH)).starProjection (toScaled hM z₀) ≠ 0 := by
  obtain ⟨v, hv, hne⟩ := hz₀
  intro h0
  rw [Submodule.starProjection_apply_eq_zero_iff] at h0
  have hmem : toScaled hM v ∈ leftmostSpace (isSymmetric_scaledOp (hM := hM) hH) := by
    rw [mem_leftmostSpace_iff, ← leftmostPencil_eq hH hM]
    exact scaledOp_toScaled_of_eigen hv
  apply hne
  have := Submodule.inner_right_of_mem_orthogonal hmem h0
  rwa [inner_toScaled, real_inner_comm] at this

/-- **Theorem 9.3.1 of [cartis2022evaluation] (Fast convergence in the hard case)**, with the
missing hypothesis `z₀ ∈ 𝒵₁` read in the `M`-inner product. Let `λ₁` be the leftmost pencil
eigenvalue, `0 < ω_L`, `0 < γ_U`, `1 < γ_L`, and fix parameter sequences `nₖ`, `ωₖ`, `γₖ` with
`nₖ = n̄` and `γₖ = γ̄` for all large `k`. Then there is `ε > 0` such that every run of
Algorithm 9.3.1 with these sequences, `z 0 = z₀` and `λᴳ₀ < -λ₁ + ε` satisfies `λᴳₖ > -λ₁`,
decreases monotonically and converges to `-λ₁` with Q-order `γ̄`:
`c (λᴳₖ + λ₁)^γ̄ ≤ λᴳₖ₊₁ + λ₁ ≤ C (λᴳₖ + λ₁)^γ̄` for all large `k`, some `0 < c ≤ C`. The radius
`ε` depends on `z₀` and on the fixed sequences (through a bound on `nₖ`), but not on `n_U` or on
the run. The hypothesis `z₀ ∈ 𝒵₁` is `∃ v, H v = λ₁ M v ∧ ⟪z₀, M v⟫ ≠ 0`. -/
theorem theorem_9_3_1 (hH : H.IsHermitian) (hM : M.PosDef) {ωL ωU γL γU : ℝ} (hωL : 0 < ωL)
    (hγU : 0 < γU) (hγL : 1 < γL) {z₀ : EuclideanSpace ℝ (Fin n)}
    (hz₀ : ∃ v : EuclideanSpace ℝ (Fin n),
      toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v ∧
        ⟪z₀, toEuclideanLin M v⟫ ≠ 0)
    {nk : ℕ → ℕ} {ω γ : ℕ → ℝ} {nbar : ℕ} (hn : ∀ᶠ k in atTop, nk k = nbar) {γbar : ℝ}
    (hγ : ∀ᶠ k in atTop, γ k = γbar) :
    ∃ ε > 0, ∀ (nU : ℕ∞) (lamG : ℕ → ℝ) (z : ℕ → EuclideanSpace ℝ (Fin n)),
      algorithm_9_3_1 hH hM ωL ωU γL γU nU lamG z nk ω γ → z 0 = z₀ →
      lamG 0 < -leftmostPencil hH hM + ε →
      (∀ k, -leftmostPencil hH hM < lamG k) ∧ Antitone lamG ∧
      Tendsto lamG atTop (𝓝 (-leftmostPencil hH hM)) ∧
      (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ k in atTop,
        c * (lamG k + leftmostPencil hH hM) ^ γbar ≤ lamG (k + 1) + leftmostPencil hH hM ∧
          lamG (k + 1) + leftmostPencil hH hM ≤ C * (lamG k + leftmostPencil hH hM) ^ γbar) ∧
      ConvergesWithOrder lamG (-leftmostPencil hH hM) γbar := by
  obtain ⟨ε, hε, hrun⟩ := IsInverseIterationRun.convergence_of_eventually_const
    (ω := ω) (γ := γ) hωL hγU hγL (starProjection_ne_zero_of_mem_Z₁ hH hM hz₀) hn
  refine ⟨ε, hε, fun nU lamG z h hz0 hlt => ?_⟩
  rw [leftmostPencil_eq] at hlt ⊢
  obtain ⟨h1, h2, h3, -, -, h6⟩ := hrun nU lamG _ (h.isInverseIterationRun hH hM)
    (by simp only [hz0]) hlt
  exact ⟨h1, h2, h3, (h6 γbar hγ).1, (h6 γbar hγ).2⟩

/-! ### Sequences of problems (§9.3.5) -/

/-- **Monotonicity of `𝓛` in `σ`** ([cartis2022evaluation] §9.3.5): for fixed `H`, `g`, `M`, `r`
and `σ ≤ σ₊`, `𝓛 ⊆ 𝓛₊` (`𝓝 = (-∞, λₛ]` does not depend on `σ`, since `λₛ = max(0, -λ₁)` depends
only on `H` and `M`); and every sampled `λ₊ > λₛ` with
`π(λ₊) ≥ (λ₊/σ₊)^{2/(r-2)}` lies in `𝓛₊`. -/
theorem setL_reg_mono (hH : H.IsHermitian) (hM : M.PosDef) {σ σp r : ℝ} (hσ : 0 < σ)
    (hσp : σ ≤ σp) (hr : 2 < r) :
    setL_reg hH hM g σ r ⊆ setL_reg hH hM g σp r ∧
      ∀ lam, lambdaS hH hM < lam → (lam / σp) ^ (2 / (r - 2)) ≤ secularFn g H M lam →
        lam ∈ setL_reg hH hM g σp r := by
  refine ⟨fun lam ⟨hlam, h⟩ => ⟨hlam, le_trans ?_ h⟩, fun lam hlam h =>
    (mem_setL_reg_iff hH hM (hσ.trans_le hσp)).2 ⟨hlam, h⟩⟩
  have hl : 0 ≤ lam := (lambdaS_nonneg hH hM).trans hlam.le
  exact Real.rpow_le_rpow (div_nonneg hl (hσ.trans_le hσp).le)
    (div_le_div_of_nonneg_left hl hσ hσp) (one_div_nonneg.2 (sub_pos.2 hr).le)

/-! ### Early termination (§9.3.6) -/

/-- The **early-termination requirements** (9.3.14) of [cartis2022evaluation] for a step `s` of the
regularization subproblem (8.1.3), with the `M`-scalings of the norms, `λ = σ ‖s‖_M^{r-2}` and the
Hessian `∇²m^R(s) = H + λ M + (r-2) λ (M s)(M s)ᵀ/‖s‖_M²` of (8.2.34):
(a) `m^R(s) ≤ m^R(0) = 0`;
(b) `‖g + H s + λ M s‖_{M⁻¹} ≤ ½ θ₁ ‖s‖_M²`;
(c) `λ_min[∇²m^R(s), M] ≥ -θ₂ ‖s‖_M`, i.e. `⟪w, ∇²m^R(s) w⟫ ≥ -θ₂ ‖s‖_M ⟪w, M w⟫` for all `w`. -/
structure stoppingRules_9_3_14 (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (σ r θ₁ θ₂ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : Prop where
  /-- (9.3.14a): the model does not increase. -/
  decrease : regModel g H M σ r s ≤ 0
  /-- (9.3.14b): the gradient is small in the dual norm. -/
  gradient : mNorm M⁻¹ (g + toEuclideanLin H s + (σ * mNorm M s ^ (r - 2)) • toEuclideanLin M s) ≤
    1 / 2 * θ₁ * mNorm M s ^ 2
  /-- (9.3.14c): the Hessian is almost positive semidefinite, in the `M`-scaling. -/
  curvature : ∀ w, -(θ₂ * mNorm M s) * ⟪w, toEuclideanLin M w⟫ ≤
    ⟪w, toEuclideanLin H w⟫ + σ * mNorm M s ^ (r - 2) * ⟪w, toEuclideanLin M w⟫ +
      (r - 2) * σ * mNorm M s ^ (r - 4) * ⟪toEuclideanLin M s, w⟫ ^ 2

/-- The rules (9.3.14) are the operator rules `Subproblem.RegStoppingRules` in the `M`-inner
product space. -/
theorem stoppingRules_9_3_14_iff_scaled (hM : M.PosDef) {σ r θ₁ θ₂ : ℝ} (hr : r ≠ 0)
    (s : EuclideanSpace ℝ (Fin n)) :
    stoppingRules_9_3_14 g H M σ r θ₁ θ₂ s ↔
      RegStoppingRules (scaledGrad hM g) (scaledOp H hM) σ r θ₁ θ₂ (toScaled hM s) := by
  have hMs := isSymmetric_toEuclideanLin_iff.2 hM.isHermitian
  rw [regStoppingRules_scaled_iff hr, ← mNorm_eq_norm_toScaled hM]
  have ha : regModel g H M σ r s = ⟪g, s⟫ + 1 / 2 * ⟪s, toEuclideanLin H s⟫ +
      σ / r * mNorm M s ^ r := by
    simp only [Chapter08.regModel, Chapter08.model]; ring
  have hc : ∀ w, ⟪toEuclideanLin M w, w⟫ = ⟪w, toEuclideanLin M w⟫ := fun w => hMs w w
  simp only [hc, ← sq]
  rw [← ha]
  exact ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- **Theorem 9.3.2 of [cartis2022evaluation] (Constructive early termination test)**, with the
`M`-scaled curvature condition. Let `σ > 0`, `r > 2`, `λc ∈ 𝓕` and `π = π(λc)` satisfy
(9.3.15a) `π ≤ (r/2)^{2/(r-2)} (λc/σ)^{2/(r-2)}`, (9.3.15b) `|π^{(r-2)/2} - λc/σ| ≤ θ₁/(2σ) π^{1/2}`
and (9.3.15c) `π^{(r-2)/2} - λc/σ ≥ -(θ₂/σ) π^{1/2}`. Then `s = s(λc)` satisfies the stopping rules
(9.3.14). -/
theorem theorem_9_3_2 (hH : H.IsHermitian) (hM : M.PosDef) {σ r θ₁ θ₂ lamc : ℝ} (hσ : 0 < σ)
    (hr : 2 < r) (hc : lamc ∈ setF_reg hH hM g σ r)
    (ha : secularFn g H M lamc ≤ (r / 2) ^ (2 / (r - 2)) * (lamc / σ) ^ (2 / (r - 2)))
    (hb : |secularFn g H M lamc ^ ((r - 2) / 2) - lamc / σ| ≤
      θ₁ / (2 * σ) * secularFn g H M lamc ^ (1 / 2 : ℝ))
    (hcc : secularFn g H M lamc ^ ((r - 2) / 2) - lamc / σ ≥
      -(θ₂ / σ) * secularFn g H M lamc ^ (1 / 2 : ℝ)) :
    stoppingRules_9_3_14 g H M σ r θ₁ θ₂ (stepOf g H M lamc) := by
  have hlam : lambdaS hH hM < lamc := by rcases hc with h | h <;> exact h.1
  rw [lambdaS_eq] at hlam
  rw [secularFn_eq_secular hM] at ha hb hcc
  rw [stoppingRules_9_3_14_iff_scaled hM (by linarith), toScaled_stepOf hM]
  exact regStoppingRules_step (hH := isSymmetric_scaledOp hH) hσ hr hlam ha hb hcc

/-- The lower factor `ηᴸ(σ, θ₁, θ₂) = max(1/(1 + θ₁/(2σ)), 1/(1 + θ₂/σ))` of (9.3.16). -/
noncomputable def etaL (σ θ₁ θ₂ : ℝ) : ℝ := max (1 / (1 + θ₁ / (2 * σ))) (1 / (1 + θ₂ / σ))

/-- The upper factor `ηᵁ(σ, θ₁) = min(3/2, 1/(1 - θ₁/(2σ)))` of (9.3.16), the second term absent
when `1 - θ₁/(2σ) ≤ 0`. -/
noncomputable def etaU (σ θ₁ : ℝ) : ℝ :=
  if 0 < 1 - θ₁ / (2 * σ) then min (3 / 2) (1 / (1 - θ₁ / (2 * σ))) else 3 / 2

/-- The real-variable content of (9.3.16): for `p, x ≥ 0`, `a, b ≥ 0`, the conditions
`p² ≤ (3/2)² x²`, `|p - x| ≤ a p`, `p - x ≥ -b p` hold iff
`max(1/(1+a), 1/(1+b)) x ≤ p ≤ ηᵁ x`. -/
theorem cubic_conditions_iff {p x a b : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x) (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    (p ^ 2 ≤ (3 / 2) ^ 2 * x ^ 2 ∧ |p - x| ≤ a * p ∧ p - x ≥ -b * p) ↔
      max (1 / (1 + a)) (1 / (1 + b)) * x ≤ p ∧
        p ≤ (if 0 < 1 - a then min (3 / 2) (1 / (1 - a)) else 3 / 2) * x := by
  have h1a : 0 < 1 + a := by linarith
  have h1b : 0 < 1 + b := by linarith
  have hsq : p ^ 2 ≤ (3 / 2) ^ 2 * x ^ 2 ↔ p ≤ 3 / 2 * x := by
    rw [← mul_pow]; exact pow_le_pow_iff_left₀ hp (by positivity) two_ne_zero
  have hA : max (1 / (1 + a)) (1 / (1 + b)) * x ≤ p ↔ x ≤ (1 + a) * p ∧ x ≤ (1 + b) * p := by
    rw [max_mul_of_nonneg _ _ hx, max_le_iff, one_div_mul_eq_div, one_div_mul_eq_div,
      div_le_iff₀ h1a, div_le_iff₀ h1b, mul_comm p, mul_comm p]
  rw [hsq, abs_le, hA]
  split_ifs with h
  · have hB : p ≤ min (3 / 2) (1 / (1 - a)) * x ↔ p ≤ 3 / 2 * x ∧ (1 - a) * p ≤ x := by
      rw [min_mul_of_nonneg _ _ hx, le_min_iff, one_div_mul_eq_div, le_div_iff₀ h, mul_comm p]
    rw [hB]
    constructor
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
      exact ⟨⟨by linarith, by linarith⟩, h1, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h3, ⟨by linarith, by linarith⟩, by linarith⟩
  · push Not at h
    constructor
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
      exact ⟨⟨by linarith, by linarith⟩, h1⟩
    · rintro ⟨⟨h2, h3⟩, h1⟩
      have : (1 - a) * p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hp
      exact ⟨h1, ⟨by linarith, by linarith⟩, by linarith⟩

/-- **The cubic case of the termination test** ([cartis2022evaluation] (9.3.16)): for `r = 3`,
`σ > 0`, `θ₁, θ₂ ≥ 0` and `λc ∈ 𝓕`, the conditions (9.3.15) are equivalent to
`ηᴸ(σ, θ₁, θ₂) λc/σ ≤ ‖s(λc)‖_M ≤ ηᵁ(σ, θ₁) λc/σ`. -/
theorem cubic_termination_9_3_16 (hH : H.IsHermitian) (hM : M.PosDef) {σ r θ₁ θ₂ lamc : ℝ}
    (hσ : 0 < σ) (hr : r = 3) (hθ₁ : 0 ≤ θ₁) (hθ₂ : 0 ≤ θ₂) (hc : lamc ∈ setF_reg hH hM g σ r) :
    (secularFn g H M lamc ≤ (r / 2) ^ (2 / (r - 2)) * (lamc / σ) ^ (2 / (r - 2)) ∧
      |secularFn g H M lamc ^ ((r - 2) / 2) - lamc / σ| ≤
        θ₁ / (2 * σ) * secularFn g H M lamc ^ (1 / 2 : ℝ) ∧
      secularFn g H M lamc ^ ((r - 2) / 2) - lamc / σ ≥
        -(θ₂ / σ) * secularFn g H M lamc ^ (1 / 2 : ℝ)) ↔
    etaL σ θ₁ θ₂ * (lamc / σ) ≤ mNorm M (stepOf g H M lamc) ∧
      mNorm M (stepOf g H M lamc) ≤ etaU σ θ₁ * (lamc / σ) := by
  subst hr
  have hlam : lambdaS hH hM < lamc := by rcases hc with h | h <;> exact h.1
  have hx : 0 ≤ lamc / σ := div_nonneg ((lambdaS_nonneg hH hM).trans hlam.le) hσ.le
  have hπ : secularFn g H M lamc = mNorm M (stepOf g H M lamc) ^ 2 := (mNorm_stepOf_sq hM _).symm
  have hhalf : secularFn g H M lamc ^ (1 / 2 : ℝ) = mNorm M (stepOf g H M lamc) := by
    rw [← Real.sqrt_eq_rpow, hπ, Real.sqrt_sq (mNorm_nonneg _ _)]
  have e1 : ((3 : ℝ) - 2) / 2 = 1 / 2 := by norm_num
  have e2 : (2 : ℝ) / (3 - 2) = (2 : ℕ) := by norm_num
  rw [e1, hhalf, e2, Real.rpow_natCast, Real.rpow_natCast, hπ, etaL, etaU]
  exact cubic_conditions_iff (mNorm_nonneg _ _) hx (by positivity) (by positivity)

end CartisGouldToint.Chapter09
