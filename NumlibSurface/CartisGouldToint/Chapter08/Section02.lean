import Numlib.Optimization.Subproblem.Multiplier
import Numlib.Optimization.Subproblem.SecularIteration
import NumlibSurface.CartisGouldToint.Chapter08.Section01

/-!
# Cartis–Gould–Toint §8.2: A digression on all things secular

Surface file for [cartis2022evaluation] §8.2: the secular function of the subproblems (8.1.2) and
(8.1.3), for a symmetric `H` and a symmetric positive definite `M` on `ℝⁿ`.

## Main definitions

* `stepOf g H M λ` — the step `s(λ) = (H + λ M)⁻¹ (-g)` of (8.2.2).
* `secularFn g H M λ` — the secular function `π(λ) = ⟪s(λ), M s(λ)⟫` (8.2.4); the transformed
  secular function `π(λ; β)` of (8.2.17) is `secularFn g H M λ ^ β`.
* `leftmostPencil hH hM` — the leftmost eigenvalue `λ₁` of the pencil `(H, M)`, and
  `lambdaS hH hM = max 0 (-λ₁)`, the book's `λₛ`.
* `secularTaylorPoly g H M λc k δ` — the Taylor polynomial `t_k(δ)` (8.2.12).
* `secularDerivVec g H M λ k`, `alphaCoeff k` — the vectors `s⁽ᵏ⁾(λ)` of (8.2.29) and the
  coefficients `αₖ` of (8.2.30).

## Main results

* `secularFn_eq_sum`, `exists_pencil_eigenbasis` — the spectral form (8.2.6)–(8.2.7).
* `lambdaS_lt_iff` — `λ > λₛ` iff `λ > 0` and `H + λ M ≻ 0`.
* `lemma_8_2_1`, `IsAdmissibleTarget.lemma_8_2_1` — the root of the secular equation;
  `tau_admissible_8_2_9` — the targets (8.2.9) are admissible.
* `theorem_8_2_2`, `theorem_8_2_2_strict` — Taylor bounds (8.2.13)–(8.2.14).
* `lemma_8_2_3`, `lemma_8_2_3_strict` — signs of the derivatives of `π(λ; β)`.
* `corollary_8_2_4` — monotonicity and convexity of `π(λ; β)`; `corollary_8_2_4_tendsto_lambdaS` —
  its right limit at `λₛ`.
* `theorem_8_2_5`, `theorem_8_2_5_strict` — first-order Taylor bounds (8.2.20)–(8.2.21).
* `theorem_8_2_6` — derivatives of the secular function (8.2.27)–(8.2.30).
* `theorem_8_2_7`, `theorem_8_2_8` — global optimality of the two subproblems.

All proofs transport the backbone `Numlib.Optimization.Subproblem` through the `M`-inner product
space `Subproblem.ScaledSpace hM`: the secular function is the operator secular function of
`M⁻¹ g` and `M⁻¹ H` for every `λ` (`secularFn_eq_secular`).

## Corrections to the source

* Lemma 8.2.1: `π(λₛ) > τ(λₛ)` is read as `π(λ) ≥ c > τ(λₛ)` for `λ` near `λₛ` from the right
  (`λₛ` may be a pole), and `τ` is assumed right-continuous at `λₛ` (the book assumes continuity
  only on `(λₛ, ∞)` but uses `τ(λₛ)`).
* Lemma 8.2.3, Theorem 8.2.5: the strict inequalities need `g ≠ 0`, and for `β = -1/2` they fail
  exactly when `g = M v` for a generalized eigenvector `v` of `(H, M)` (then `π(λ; -1/2)` is
  affine: `n = 1`, `H = 0`, `M = 1`, `g = 1` gives `π(λ; -1/2) = λ`); Theorem 8.2.5 also needs
  `δ ≠ 0` for strictness. Corollary 8.2.4 needs `g ≠ 0` (for `g = 0` the function is constant).
* Corollary 8.2.4: the starting value "`π(λₛ; β)`" is read as the right limit at `λₛ`
  (`corollary_8_2_4_tendsto_lambdaS`), which may be `+∞` for `β > 0` when `λₛ = -λ₁` is a pole.
* Theorem 8.2.2: the book states it for `k > 0`; it holds for every `k`.
* The convexity of `-λ^γ` (`γ ∈ (0, 1]`) and the concavity of `λ^γ` (`γ < 0`) used for the
  transformed secular equations are stated on `λ ≥ λₛ`, which may contain `0` when `λ₁ ≥ 0`; they
  hold on `λ > 0`.
-/

open Matrix Set Filter Topology
open Finset (range)
open scoped Nat RealInnerProductSpace

namespace CartisGouldToint.Chapter08

open Subproblem

variable {n : ℕ}

/-! ### The step and the secular function -/

/-- The **step** `s(λ) = (H + λ M)⁻¹ (-g)` solving (8.2.2) of [cartis2022evaluation] when
`H + λ M` is nonsingular (it is `0` otherwise, by the convention `A⁻¹ = 0` for singular `A`). -/
noncomputable def stepOf (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) : EuclideanSpace ℝ (Fin n) :=
  toEuclideanLin (H + lam • M)⁻¹ (-g)

theorem stepOf_def (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) :
    stepOf g H M lam = toEuclideanLin (H + lam • M)⁻¹ (-g) :=
  rfl

/-- The **secular function** `π(λ) = ⟪s(λ), M s(λ)⟫ = ‖s(λ)‖_M²` of [cartis2022evaluation]
(8.2.4). The transformed secular function `π(λ; β)` of (8.2.17) is `secularFn g H M λ ^ β`. -/
noncomputable def secularFn (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) : ℝ :=
  ⟪stepOf g H M lam, toEuclideanLin M (stepOf g H M lam)⟫

theorem secularFn_def (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) :
    secularFn g H M lam = ⟪stepOf g H M lam, toEuclideanLin M (stepOf g H M lam)⟫ :=
  rfl

/-- The **leftmost eigenvalue** `λ₁` of the pencil `(H, M)` ([cartis2022evaluation] (8.2.5)):
the least of `Matrix.pencilEigenvalues hH hM` (and `0` when `n = 0`). -/
noncomputable def leftmostPencil {H M : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian)
    (hM : M.PosDef) : ℝ :=
  ⨅ i, pencilEigenvalues hH hM i

/-- The threshold `λₛ = max(0, -λ₁)` of Lemma 8.2.1 of [cartis2022evaluation]. -/
noncomputable def lambdaS {H M : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian)
    (hM : M.PosDef) : ℝ :=
  max 0 (-leftmostPencil hH hM)

theorem lambdaS_def {H M : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) (hM : M.PosDef) :
    lambdaS hH hM = max 0 (-leftmostPencil hH hM) :=
  rfl

variable {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- The leftmost pencil eigenvalue is the leftmost eigenvalue of the scaled operator `M⁻¹ H`. -/
theorem leftmostPencil_eq (hH : H.IsHermitian) (hM : M.PosDef) :
    leftmostPencil hH hM = leftmost (isSymmetric_scaledOp (hM := hM) hH) :=
  (leftmost_scaledOp hH).symm

/-- `λₛ` is the shift threshold of the scaled operator `M⁻¹ H`. -/
theorem lambdaS_eq (hH : H.IsHermitian) (hM : M.PosDef) :
    lambdaS hH hM = shiftThreshold (isSymmetric_scaledOp (hM := hM) hH) := by
  rw [lambdaS, shiftThreshold, leftmostPencil_eq]

theorem lambdaS_nonneg (hH : H.IsHermitian) (hM : M.PosDef) : 0 ≤ lambdaS hH hM :=
  le_max_left _ _

theorem neg_leftmostPencil_le_lambdaS (hH : H.IsHermitian) (hM : M.PosDef) :
    -leftmostPencil hH hM ≤ lambdaS hH hM :=
  le_max_right _ _

/-- Above `λₛ` the shift `λ` lies above `-λ₁` of the scaled operator. -/
theorem neg_leftmost_lt_of_lambdaS_lt (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ}
    (h : lambdaS hH hM < lam) : -leftmost (isSymmetric_scaledOp (hM := hM) hH) < lam := by
  rw [lambdaS_eq] at h
  exact (neg_leftmost_le_shiftThreshold).trans_lt h

/-- `λ > λₛ` iff `λ > 0` and `H + λ M` is positive definite (`n ≥ 1`). -/
theorem lambdaS_lt_iff [NeZero n] (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ} :
    lambdaS hH hM < lam ↔ 0 < lam ∧ (H + lam • M).PosDef := by
  rw [lambdaS, max_lt_iff, (posDef_add_smul_iff_scaled hH lam).2, leftmostPencil_eq]

/-- **The step in the scaled setting**, for every `λ`: `M⁻¹`-transported, `s(λ)` is the operator
step `step (M⁻¹ g) (M⁻¹ H) λ` (both vanish when `H + λ M` is singular). -/
theorem toScaled_stepOf (hM : M.PosDef) (g : EuclideanSpace ℝ (Fin n)) (lam : ℝ) :
    toScaled hM (stepOf g H M lam) = step (scaledGrad hM g) (scaledOp H hM) lam :=
  toScaled_step g lam

/-- **The secular function in the scaled setting**: `π = secular (M⁻¹ g) (M⁻¹ H)` as functions
of `λ`. -/
theorem secularFn_eq_secular (hM : M.PosDef) :
    secularFn g H M = secular (scaledGrad hM g) (scaledOp H hM) := by
  funext lam
  rw [secular_scaled g lam, secularFn, stepOf, real_inner_comm]

/-- `π(λ) = ‖s(λ)‖_M²`. -/
theorem mNorm_stepOf_sq (hM : M.PosDef) (lam : ℝ) :
    mNorm M (stepOf g H M lam) ^ 2 = secularFn g H M lam :=
  mNorm_sq hM _

theorem secularFn_nonneg (hM : M.PosDef) (lam : ℝ) : 0 ≤ secularFn g H M lam := by
  rw [← mNorm_stepOf_sq hM]; positivity

/-- The step solves (8.2.2) above `λₛ`. -/
theorem add_smul_stepOf (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ}
    (hlam : -leftmost (isSymmetric_scaledOp (hM := hM) hH) < lam) :
    toEuclideanLin (H + lam • M) (stepOf g H M lam) = -g := by
  have := (step_spec (hH := isSymmetric_scaledOp (hM := hM) hH) (g := scaledGrad hM g) hlam).1
  rw [← toScaled_stepOf hM] at this
  exact (add_smul_scaledOp_toScaled_eq_neg_iff lam g _).1 this

/-- On an empty index type every vector vanishes and so does the secular function. -/
theorem secularFn_of_isEmpty [IsEmpty (Fin n)] : secularFn g H M = fun _ => 0 := by
  funext lam
  rw [secularFn, Subsingleton.elim (stepOf g H M lam) 0, inner_zero_left]

/-- Positive definiteness of `H + λ M` is `λ > -λ₁` for the scaled operator (`n ≥ 1`). -/
theorem neg_leftmost_lt_of_posDef [NeZero n] (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ}
    (h : (H + lam • M).PosDef) : -leftmost (isSymmetric_scaledOp (hM := hM) hH) < lam :=
  ((posDef_add_smul_iff_scaled hH lam).2).1 h

/-! ### The spectral form (8.2.6)–(8.2.7) -/

/-- **The spectral form of the secular function** ([cartis2022evaluation] (8.2.6)–(8.2.7)). Let
`V` have `M`-orthonormal generalized eigenvectors of `(H, M)` as columns, `H V = M V Λ` and
`Vᵀ M V = I` (8.2.5), and let `γ = Vᵀ g`. If `λ ≠ -λᵢ` for all `i` then
`s_V(λ) = Vᵀ M s(λ) = -(Λ + λ I)⁻¹ γ` and `π(λ) = ∑ᵢ (γᵢ / (λ + λᵢ))²`. -/
theorem secularFn_eq_sum (hM : M.PosDef) {V : Matrix (Fin n) (Fin n) ℝ} {μ : Fin n → ℝ}
    (hV : H * V = M * V * diagonal μ) (hVM : Vᵀ * M * V = 1) {lam : ℝ}
    (hlam : ∀ i, lam + μ i ≠ 0) :
    (∀ i, toEuclideanLin (Vᵀ * M) (stepOf g H M lam) i =
        -(toEuclideanLin Vᵀ g i) / (lam + μ i)) ∧
      secularFn g H M lam = ∑ i, (toEuclideanLin Vᵀ g i / (lam + μ i)) ^ 2 := by
  set Dinv : Matrix (Fin n) (Fin n) ℝ := diagonal fun i => (lam + μ i)⁻¹
  have hMt : Mᵀ = M := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hM.isHermitian.eq
  have hV1 : V * (Vᵀ * M) = 1 := mul_eq_one_comm.1 hVM
  have hMVV : M * V * Vᵀ = 1 := by
    have := congrArg transpose hV1
    rwa [transpose_mul, transpose_mul, transpose_transpose, hMt, transpose_one] at this
  have hd : (diagonal μ + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) * Dinv = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Dinv, add_comm (μ i), hlam i]
    · simp [Dinv, h]
  have hX : (H + lam • M) * (V * Dinv * Vᵀ) = 1 := by
    calc (H + lam • M) * (V * Dinv * Vᵀ)
        = (H * V + lam • (M * V)) * Dinv * Vᵀ := by
          simp only [add_mul, smul_mul_assoc, mul_assoc]
      _ = M * V * ((diagonal μ + lam • 1) * Dinv) * Vᵀ := by
          rw [hV]; simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
            one_mul, mul_assoc]
      _ = 1 := by rw [hd, mul_one, hMVV]
  have hinv : (H + lam • M)⁻¹ = V * Dinv * Vᵀ := inv_eq_right_inv hX
  -- the coordinates `y = Vᵀ M s(λ)`
  set y := toEuclideanLin (Vᵀ * M) (stepOf g H M lam) with hy
  have hy' : y = toEuclideanLin Dinv (toEuclideanLin Vᵀ (-g)) := by
    rw [hy, stepOf, hinv, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply,
      show Vᵀ * M * (V * Dinv * Vᵀ) = Vᵀ * M * V * Dinv * Vᵀ by simp only [mul_assoc],
      hVM, one_mul]
  have hyi : ∀ i, y i = -(toEuclideanLin Vᵀ g i) / (lam + μ i) := fun i => by
    rw [hy', map_neg, map_neg]
    simp [Dinv, toEuclideanLin_apply, -mulVec_mulVec, mulVec_diagonal, div_eq_inv_mul]
  refine ⟨hyi, ?_⟩
  have hs : stepOf g H M lam = toEuclideanLin V y := by
    rw [hy, ← toEuclideanLin_mul_apply, hV1, toEuclideanLin_one_apply]
  have hsec : secularFn g H M lam = ⟪y, y⟫ := by
    rw [secularFn, hs, ← toEuclideanLin_transpose_inner_right, ← toEuclideanLin_mul_apply,
      ← toEuclideanLin_mul_apply, hVM, toEuclideanLin_one_apply]
  rw [hsec, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hyi, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, neg_div, neg_sq]

/-- **Existence of the generalized eigenvectors (8.2.5)**: there are `V` and `Λ = diagonal μ` with
`H V = M V Λ` and `Vᵀ M V = I`, so `secularFn_eq_sum` applies. -/
theorem exists_pencil_eigenbasis (hH : H.IsHermitian) (hM : M.PosDef) :
    ∃ (V : Matrix (Fin n) (Fin n) ℝ) (μ : Fin n → ℝ),
      H * V = M * V * diagonal μ ∧ Vᵀ * M * V = 1 := by
  obtain ⟨V, d, -, h1, h2, -⟩ := Matrix.exists_simultaneous_diagonalization hH hM
  have hs : star V = Vᵀ := by rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [hs] at h1 h2
  have hMt : Mᵀ = M := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hM.isHermitian.eq
  have hV1 : V * (Vᵀ * M) = 1 := mul_eq_one_comm.1 h1
  have hMVV : M * V * Vᵀ = 1 := by
    have := congrArg transpose hV1
    rwa [transpose_mul, transpose_mul, transpose_transpose, hMt, transpose_one] at this
  refine ⟨V, d, ?_, h1⟩
  calc H * V = M * V * Vᵀ * H * V := by rw [hMVV, one_mul]
    _ = M * V * (Vᵀ * H * V) := by simp only [mul_assoc]
    _ = M * V * diagonal d := by rw [h2]; rfl

/-- `Ioi λₛ` lies above `-λ₁` of the scaled operator. -/
theorem Ioi_lambdaS_subset (hH : H.IsHermitian) (hM : M.PosDef) :
    Ioi (lambdaS hH hM) ⊆ Ioi (-leftmost (isSymmetric_scaledOp (hM := hM) hH)) :=
  fun _ h => neg_leftmost_lt_of_lambdaS_lt hH hM h

/-! ### The root of the secular equation -/

/-- **Lemma 8.2.1 of [cartis2022evaluation] (Root of the secular equation).** Let `τ` be
nonnegative, monotonically nondecreasing and continuous on `(λₛ, ∞)`, not identically zero there,
right-continuous at `λₛ` (so the book's `τ(λₛ) ≥ 0` follows), and suppose `π(λₛ) > τ(λₛ)`, read
as `π(λ) ≥ c` near `λₛ` from the right for some `c > τ(λₛ)` (`λₛ` may be a pole of `π`). Then the
secular equation `π(λ) = τ(λ)` (8.2.8) has a unique root `λ* > λₛ`. -/
theorem lemma_8_2_1 (hH : H.IsHermitian) (hM : M.PosDef) {τ : ℝ → ℝ}
    (hτ0 : ∀ lam ∈ Ioi (lambdaS hH hM), 0 ≤ τ lam) (hτm : MonotoneOn τ (Ioi (lambdaS hH hM)))
    (hτc : ContinuousOn τ (Ioi (lambdaS hH hM)))
    (hτne : ∃ lam ∈ Ioi (lambdaS hH hM), τ lam ≠ 0)
    (hτs : ContinuousWithinAt τ (Ici (lambdaS hH hM)) (lambdaS hH hM))
    (hπ : ∃ c > τ (lambdaS hH hM), ∀ᶠ lam in 𝓝[>] (lambdaS hH hM), c ≤ secularFn g H M lam) :
    ∃! lamStar, lambdaS hH hM < lamStar ∧ secularFn g H M lamStar = τ lamStar := by
  obtain ⟨c, hc, hev⟩ := hπ
  have hτlt : ∀ᶠ lam in 𝓝[>] (lambdaS hH hM), τ lam < c :=
    (hτs.mono Ioi_subset_Ici_self).eventually (gt_mem_nhds hc)
  have hleft := (hτlt.and hev).mono fun lam h => h.1.trans_le h.2
  rw [secularFn_eq_secular hM] at hleft ⊢
  rw [lambdaS_eq] at hτ0 hτm hτc hτne hleft ⊢
  obtain ⟨lamStar, hgt, heq, -, -, huniq⟩ := existsUnique_secular_root hτc hτm hτ0 hτne hleft
  exact ⟨lamStar, ⟨hgt, heq⟩, fun lam h => huniq lam h.1 h.2⟩

/-- The hypotheses of Lemma 8.2.1 on a target `τ` with threshold `a` (the book's `λₛ`), in the form
used by `IsAdmissibleTarget.lemma_8_2_1`: `τ` is nonnegative, monotonically nondecreasing and
continuous on the closed half-line `[a, ∞)` (so in particular right-continuous at `a`, as the
lemma needs), and not identically zero on the open half-line `(a, ∞)`. -/
structure IsAdmissibleTarget (a : ℝ) (τ : ℝ → ℝ) : Prop where
  /-- The target is nonnegative. -/
  nonneg : ∀ lam ∈ Ici a, 0 ≤ τ lam
  /-- The target is monotonically nondecreasing. -/
  monotoneOn : MonotoneOn τ (Ici a)
  /-- The target is continuous (in particular right-continuous at `a`). -/
  continuousOn : ContinuousOn τ (Ici a)
  /-- The target is not identically zero. -/
  exists_ne_zero : ∃ lam ∈ Ioi a, τ lam ≠ 0

/-- **The two targets (8.2.9)** of [cartis2022evaluation], `τ(λ) = Δ²` (trust region, `Δ > 0`) and
`τ(λ) = (λ/σ)^{2/(r-2)}` (regularization, `σ > 0`, `r > 2`), satisfy the hypotheses of
Lemma 8.2.1 on `(λₛ, ∞)`. -/
theorem tau_admissible_8_2_9 (hH : H.IsHermitian) (hM : M.PosDef) :
    (∀ Δ : ℝ, 0 < Δ → IsAdmissibleTarget (lambdaS hH hM) fun _ => Δ ^ 2) ∧
      ∀ σ r : ℝ, 0 < σ → 2 < r →
        IsAdmissibleTarget (lambdaS hH hM) fun lam => (lam / σ) ^ (2 / (r - 2)) := by
  refine ⟨fun Δ hΔ => ⟨fun _ _ => sq_nonneg Δ, monotoneOn_const, continuousOn_const,
    ⟨lambdaS hH hM + 1, by simp, by positivity⟩⟩, fun σ r hσ hr => ?_⟩
  have hp : 0 ≤ 2 / (r - 2) := div_nonneg zero_le_two (sub_pos.2 hr).le
  have hs := lambdaS_nonneg hH hM
  refine ⟨fun lam hlam => Real.rpow_nonneg (div_nonneg (hs.trans hlam) hσ.le) _,
    (monotoneOn_regTarget hσ hr).mono fun x hx => hs.trans hx,
    ((continuous_id.div_const σ).rpow_const fun _ => Or.inr hp).continuousOn,
    ⟨lambdaS hH hM + 1, by simp, (Real.rpow_pos_of_pos (by positivity) _).ne'⟩⟩

/-- **Lemma 8.2.1 for an admissible target**: if `τ` satisfies `IsAdmissibleTarget λₛ τ` (for
instance one of the targets (8.2.9), `tau_admissible_8_2_9`) and `π(λₛ) > τ(λₛ)` (in the sense of
`lemma_8_2_1`), the secular equation `π(λ) = τ(λ)` has a unique root `λ* > λₛ`. -/
theorem IsAdmissibleTarget.lemma_8_2_1 (hH : H.IsHermitian) (hM : M.PosDef) {τ : ℝ → ℝ}
    (hτ : IsAdmissibleTarget (lambdaS hH hM) τ)
    (hπ : ∃ c > τ (lambdaS hH hM), ∀ᶠ lam in 𝓝[>] (lambdaS hH hM), c ≤ secularFn g H M lam) :
    ∃! lamStar, lambdaS hH hM < lamStar ∧ secularFn g H M lamStar = τ lamStar :=
  CartisGouldToint.Chapter08.lemma_8_2_1 hH hM (fun lam h => hτ.nonneg lam (mem_Ici_of_Ioi h))
    (hτ.monotoneOn.mono Ioi_subset_Ici_self) (hτ.continuousOn.mono Ioi_subset_Ici_self)
    hτ.exists_ne_zero (hτ.continuousOn _ (mem_Ici.2 le_rfl)) hπ

/-! ### Taylor estimates -/

/-- The `k`-th order **Taylor polynomial of the secular function** at `λc`,
`t_k(δ) = ∑_{j=0}^k π⁽ʲ⁾(λc)/j! δʲ` ([cartis2022evaluation] (8.2.12)). -/
noncomputable def secularTaylorPoly (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (lamc δ : ℝ) : ℝ :=
  ∑ j ∈ range (k + 1), iteratedDeriv j (secularFn g H M) lamc / j ! * δ ^ j

/-- The Taylor polynomial is that of the operator secular function. -/
theorem secularTaylorPoly_eq (hM : M.PosDef) (k : ℕ) (lamc δ : ℝ) :
    secularTaylorPoly g H M k lamc δ =
      secularTaylor (scaledGrad hM g) (scaledOp H hM) k lamc δ := by
  rw [secularTaylorPoly, secularTaylor, secularFn_eq_secular hM]

/-- **Theorem 8.2.2 of [cartis2022evaluation] (Lower and upper Taylor estimates of `π`).** Let
`λc > λₛ`. For every `k` (the book states `k > 0`; `k = 0` holds as well) and `δ > 0`,
`π(λc + δ) ≤ t_k(δ)` for even `k` and `π(λc + δ) ≥ t_k(δ)` for odd `k` (8.2.13); for `λₛ - λc < δ <
0`, `π(λc + δ) ≥ t_{k+1}(δ) ≥ t_k(δ)` (8.2.14). The strict versions for `g ≠ 0` are
`theorem_8_2_2_strict`. -/
theorem theorem_8_2_2 (hH : H.IsHermitian) (hM : M.PosDef) {lamc : ℝ}
    (hc : lambdaS hH hM < lamc) (k : ℕ) :
    (∀ δ, 0 < δ → (Even k → secularFn g H M (lamc + δ) ≤ secularTaylorPoly g H M k lamc δ) ∧
      (Odd k → secularTaylorPoly g H M k lamc δ ≤ secularFn g H M (lamc + δ))) ∧
    (∀ δ, lambdaS hH hM - lamc < δ → δ < 0 →
      secularTaylorPoly g H M k lamc δ ≤ secularTaylorPoly g H M (k + 1) lamc δ ∧
        secularTaylorPoly g H M (k + 1) lamc δ ≤ secularFn g H M (lamc + δ)) := by
  have h := secular_taylor_bounds (g := scaledGrad hM g) (neg_leftmost_lt_of_lambdaS_lt hH hM hc) k
  simp only [secularTaylorPoly, secularFn_eq_secular hM]
  exact ⟨h.1, fun δ hδ1 hδ2 => h.2 δ hδ2 (neg_leftmost_lt_of_lambdaS_lt hH hM (by linarith))⟩

/-- **Theorem 8.2.2 of [cartis2022evaluation], strict form**: the inequalities (8.2.13) and
(8.2.14) are strict when `g ≠ 0`. -/
theorem theorem_8_2_2_strict (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) {lamc : ℝ}
    (hc : lambdaS hH hM < lamc) (k : ℕ) :
    (∀ δ, 0 < δ → (Even k → secularFn g H M (lamc + δ) < secularTaylorPoly g H M k lamc δ) ∧
      (Odd k → secularTaylorPoly g H M k lamc δ < secularFn g H M (lamc + δ))) ∧
    (∀ δ, lambdaS hH hM - lamc < δ → δ < 0 →
      secularTaylorPoly g H M k lamc δ < secularTaylorPoly g H M (k + 1) lamc δ ∧
        secularTaylorPoly g H M (k + 1) lamc δ < secularFn g H M (lamc + δ)) := by
  have h := secular_taylor_bounds_strict (scaledGrad_ne_zero (hM := hM) hg)
    (neg_leftmost_lt_of_lambdaS_lt hH hM hc) k
  simp only [secularTaylorPoly, secularFn_eq_secular hM]
  exact ⟨h.1, fun δ hδ1 hδ2 => h.2 δ hδ2 (neg_leftmost_lt_of_lambdaS_lt hH hM (by linarith))⟩

/-! ### The transformed secular function -/

/-- **Lemma 8.2.3 of [cartis2022evaluation] (Derivatives of `π(λ; β)`).** For `λ > λₛ`:
(i) `π⁽¹⁾(λ; β) ≤ 0` for `β > 0` and `≥ 0` for `β < 0`; (ii) `π⁽²⁾(λ; β) ≥ 0` for `β > 0` and
`≤ 0` for `β ∈ [-1/2, 0)`. The strict versions are `lemma_8_2_3_strict`. -/
theorem lemma_8_2_3 (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ}
    (hlam : lambdaS hH hM < lam) (β : ℝ) :
    (0 < β → deriv (fun t => secularFn g H M t ^ β) lam ≤ 0) ∧
    (β < 0 → 0 ≤ deriv (fun t => secularFn g H M t ^ β) lam) ∧
    (0 < β → 0 ≤ iteratedDeriv 2 (fun t => secularFn g H M t ^ β) lam) ∧
    (β ∈ Ico (-1 / 2) 0 → iteratedDeriv 2 (fun t => secularFn g H M t ^ β) lam ≤ 0) := by
  rw [secularFn_eq_secular hM]
  rcases eq_or_ne g 0 with rfl | hg
  · have h1 : deriv (fun t => secular 0 (scaledOp H hM) t ^ β) lam = 0 := by
      rw [← iteratedDeriv_one]; exact secular_rpow_zero_left _ β lam 0
    have h2 : iteratedDeriv 2 (fun t => secular 0 (scaledOp H hM) t ^ β) lam = 0 :=
      secular_rpow_zero_left _ β lam 1
    rw [scaledGrad_zero, h1, h2]
    exact ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ => le_rfl, fun _ => le_rfl⟩
  · obtain ⟨h1, h2, h3, h4, -, -⟩ := secular_rpow_deriv_sign (scaledGrad_ne_zero (hM := hM) hg)
      (neg_leftmost_lt_of_lambdaS_lt hH hM hlam) β
    exact ⟨fun h => (h1 h).le, fun h => (h2 h).le, fun h => (h3 h).le, h4⟩

/-- **Lemma 8.2.3 of [cartis2022evaluation], strict form**, corrected. For `g ≠ 0` and `λ > λₛ`
the inequalities in (i) and the `β > 0` part of (ii) are strict; for `β ∈ [-1/2, 0)` the second
derivative is negative unless `β = -1/2` and `g = M v` for a generalized eigenvector `v` of
`(H, M)`, in which case it vanishes (the book claims strictness whenever `g ≠ 0`). -/
theorem lemma_8_2_3_strict (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) {lam : ℝ}
    (hlam : lambdaS hH hM < lam) (β : ℝ) :
    (0 < β → deriv (fun t => secularFn g H M t ^ β) lam < 0) ∧
    (β < 0 → 0 < deriv (fun t => secularFn g H M t ^ β) lam) ∧
    (0 < β → 0 < iteratedDeriv 2 (fun t => secularFn g H M t ^ β) lam) ∧
    (β ∈ Ico (-1 / 2) 0 → (β ≠ -1 / 2 ∨ ¬ ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ),
        toEuclideanLin M v = g ∧ toEuclideanLin H v = c • toEuclideanLin M v) →
      iteratedDeriv 2 (fun t => secularFn g H M t ^ β) lam < 0) ∧
    (β = -1 / 2 → (∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ),
        toEuclideanLin M v = g ∧ toEuclideanLin H v = c • toEuclideanLin M v) →
      iteratedDeriv 2 (fun t => secularFn g H M t ^ β) lam = 0) := by
  rw [secularFn_eq_secular hM, ← exists_scaledOp_scaledGrad_eq_iff (hM := hM)]
  obtain ⟨h1, h2, h3, -, h5, h6⟩ := secular_rpow_deriv_sign (scaledGrad_ne_zero (hM := hM) hg)
    (neg_leftmost_lt_of_lambdaS_lt hH hM hlam) β
  exact ⟨h1, h2, h3, h5, h6⟩

/-- **Corollary 8.2.4 of [cartis2022evaluation] (Monotonicity of the transformed secular
function)**, for `g ≠ 0`. On `(λₛ, ∞)`, `π(λ; β)` is strictly decreasing, strictly convex and
tends to `0` at `+∞` when `β > 0`, and strictly increasing, concave and tends to `+∞` when
`β ∈ [-1/2, 0)`. (For `g = 0` it is constant.) The book's "from `π(λₛ; β)`" refers to the right
limit at `λₛ`, which may be infinite (a pole) and need not be `π(λₛ)^β` (the value of `π` at a
pole is a junk value); it is `corollary_8_2_4_tendsto_lambdaS`. -/
theorem corollary_8_2_4 (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) (β : ℝ) :
    (0 < β → StrictAntiOn (fun t => secularFn g H M t ^ β) (Ioi (lambdaS hH hM)) ∧
      StrictConvexOn ℝ (Ioi (lambdaS hH hM)) (fun t => secularFn g H M t ^ β) ∧
      Tendsto (fun t => secularFn g H M t ^ β) atTop (𝓝 0)) ∧
    (β ∈ Ico (-1 / 2) 0 → StrictMonoOn (fun t => secularFn g H M t ^ β) (Ioi (lambdaS hH hM)) ∧
      ConcaveOn ℝ (Ioi (lambdaS hH hM)) (fun t => secularFn g H M t ^ β) ∧
      Tendsto (fun t => secularFn g H M t ^ β) atTop atTop) := by
  rw [secularFn_eq_secular hM]
  obtain ⟨-, -, -, -, -, hpos, hneg⟩ := secular_shape (scaledGrad_ne_zero (hM := hM) hg) β
    (hH := isSymmetric_scaledOp (hM := hM) hH)
  have hsub := Ioi_lambdaS_subset hH hM
  refine ⟨fun hβ => ?_, fun hβ => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hpos hβ
    exact ⟨h1.mono hsub, h2.subset hsub (convex_Ioi _), h3⟩
  · obtain ⟨h1, h2, h3⟩ := hneg hβ
    exact ⟨h1.mono hsub, h2.subset hsub (convex_Ioi _), h3⟩

/-- **Corollary 8.2.4 of [cartis2022evaluation], the starting values** (for `g ≠ 0`): the value
"`π(λₛ; β)`" from which `π(λ; β)` decreases (`β > 0`) or increases (`β < 0`) on `(λₛ, ∞)` is its
right limit at `λₛ`, identified as follows.
* If `λₛ > -λ₁` (that is, `λ₁ > 0` and `λₛ = 0`), `π` is continuous at `λₛ` and the limit is
  `π(λₛ)^β`.
* Either `π(λ)` has a finite positive right limit `L` at `λₛ` and then `π(λ; β) → L^β` for every
  `β` (always the case when `λₛ > -λ₁`; when `λₛ = -λ₁` this happens exactly when
  `g ⊥ ker(H + λₛ M)`, i.e. `(H + λₛ M) s = -g` is consistent, and `L` is then the squared
  `M`-norm of its minimum-`M`-norm solution; see `Subproblem.tendsto_secular_rpow_threshold`),
* or `λₛ = -λ₁` is a pole: `π(λ) → +∞`, so `π(λ; β) → +∞` for `β > 0` and `π(λ; β) → 0` for
  `β < 0`.
When `λₛ = -λ₁` the value `π(λₛ)` itself is a junk value (`H + λₛ M` is singular), so only the
limit is meaningful there. -/
theorem corollary_8_2_4_tendsto_lambdaS (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) :
    (∀ β : ℝ, -leftmostPencil hH hM < lambdaS hH hM →
      Tendsto (fun t => secularFn g H M t ^ β) (𝓝[>] (lambdaS hH hM))
        (𝓝 (secularFn g H M (lambdaS hH hM) ^ β))) ∧
    ((∃ L, 0 < L ∧ Tendsto (secularFn g H M) (𝓝[>] (lambdaS hH hM)) (𝓝 L) ∧
        ∀ β : ℝ, Tendsto (fun t => secularFn g H M t ^ β) (𝓝[>] (lambdaS hH hM)) (𝓝 (L ^ β))) ∨
      (lambdaS hH hM = -leftmostPencil hH hM ∧
        Tendsto (secularFn g H M) (𝓝[>] (lambdaS hH hM)) atTop ∧
        ∀ β : ℝ, (0 < β → Tendsto (fun t => secularFn g H M t ^ β) (𝓝[>] (lambdaS hH hM)) atTop) ∧
          (β < 0 → Tendsto (fun t => secularFn g H M t ^ β) (𝓝[>] (lambdaS hH hM)) (𝓝 0)))) := by
  rw [secularFn_eq_secular hM, lambdaS_eq, leftmostPencil_eq]
  set hT := isSymmetric_scaledOp (hM := hM) hH
  have hg' := scaledGrad_ne_zero (hM := hM) hg
  have hcont : -leftmost hT < shiftThreshold hT → ∀ β : ℝ,
      Tendsto (fun t => secular (scaledGrad hM g) (scaledOp H hM) t ^ β)
        (𝓝[>] (shiftThreshold hT))
        (𝓝 (secular (scaledGrad hM g) (scaledOp H hM) (shiftThreshold hT) ^ β)) := fun h β =>
    (((Real.continuousAt_rpow_const _ β (Or.inl (secular_pos (hH := hT) hg' h).ne')).comp
      (hasDerivAt_secular (hH := hT) h).continuousAt).tendsto).mono_left nhdsWithin_le_nhds
  refine ⟨fun β h => hcont h β, ?_⟩
  rcases (neg_leftmost_le_shiftThreshold (hH := hT)).lt_or_eq with hlt | heq
  · exact Or.inl ⟨_, secular_pos (hH := hT) hg' hlt,
      ((hasDerivAt_secular (hH := hT) hlt).continuousAt.tendsto).mono_left nhdsWithin_le_nhds,
      hcont hlt⟩
  rw [← heq]
  by_cases hK : scaledGrad hM g ∈ (LinearMap.ker ((scaledOp H hM + (-leftmost hT) • 1 :
      ScaledSpace hM →L[ℝ] ScaledSpace hM) : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM))ᗮ
  · have hp : particular hT (scaledGrad hM g) (-leftmost hT) ≠ 0 := fun h0 => hg' (by
      have := ((particular_spec (hH := hT) (g := scaledGrad hM g) _).2.1 hK).1
      rw [h0, map_zero, eq_comm, neg_eq_zero] at this
      exact this)
    exact Or.inl ⟨_, pow_pos (norm_pos_iff.2 hp) 2,
      ((tendsto_step_threshold (hH := hT) (g := scaledGrad hM g)).1 hK).2,
      fun β => (tendsto_secular_rpow_threshold (hH := hT) β).1 hK (Or.inl hp)⟩
  · exact Or.inr ⟨rfl, (tendsto_step_threshold (hH := hT) (g := scaledGrad hM g)).2 hK,
      fun β => (tendsto_secular_rpow_threshold (hH := hT) β).2 hK⟩

/-- **Theorem 8.2.5 of [cartis2022evaluation] (Lower and upper first-order Taylor estimates of
`π(λ; β)`).** Let `λc > λₛ`, `δ > λₛ - λc` and `t₁(δ; β) = π(λc; β) + π⁽¹⁾(λc; β) δ`. Then
`π(λc + δ; β) ≥ t₁(δ; β)` for `β > 0` (8.2.20) and `π(λc + δ; β) ≤ t₁(δ; β)` for `β ∈ [-1/2, 0)`
(8.2.21). The strict versions are `theorem_8_2_5_strict`. -/
theorem theorem_8_2_5 (hH : H.IsHermitian) (hM : M.PosDef) {lamc δ : ℝ}
    (hc : lambdaS hH hM < lamc) (hδ : lambdaS hH hM - lamc < δ) (β : ℝ) :
    (0 < β → secularFn g H M lamc ^ β + deriv (fun t => secularFn g H M t ^ β) lamc * δ ≤
      secularFn g H M (lamc + δ) ^ β) ∧
    (β ∈ Ico (-1 / 2) 0 → secularFn g H M (lamc + δ) ^ β ≤
      secularFn g H M lamc ^ β + deriv (fun t => secularFn g H M t ^ β) lamc * δ) := by
  rw [secularFn_eq_secular hM]
  rcases eq_or_ne g 0 with rfl | hg
  · simp [secular_zero_left]
  · obtain ⟨h1, -, h3, -, -⟩ := secular_rpow_tangent (scaledGrad_ne_zero (hM := hM) hg)
      (neg_leftmost_lt_of_lambdaS_lt hH hM hc)
      (neg_leftmost_lt_of_lambdaS_lt hH hM (by linarith)) β
    exact ⟨h1, h3⟩

/-- **Theorem 8.2.5 of [cartis2022evaluation], strict form**, corrected. For `g ≠ 0` and `δ ≠ 0`,
(8.2.20) is strict, and (8.2.21) is strict unless `β = -1/2` and `g = M v` for a generalized
eigenvector `v` of `(H, M)`, in which case it is an equality (the book claims strictness whenever
`g ≠ 0`). -/
theorem theorem_8_2_5_strict (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) {lamc δ : ℝ}
    (hc : lambdaS hH hM < lamc) (hδ : lambdaS hH hM - lamc < δ) (β : ℝ) :
    (0 < β → δ ≠ 0 → secularFn g H M lamc ^ β +
      deriv (fun t => secularFn g H M t ^ β) lamc * δ < secularFn g H M (lamc + δ) ^ β) ∧
    (β ∈ Ico (-1 / 2) 0 → δ ≠ 0 → (β ≠ -1 / 2 ∨ ¬ ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ),
        toEuclideanLin M v = g ∧ toEuclideanLin H v = c • toEuclideanLin M v) →
      secularFn g H M (lamc + δ) ^ β <
        secularFn g H M lamc ^ β + deriv (fun t => secularFn g H M t ^ β) lamc * δ) ∧
    (β = -1 / 2 → (∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ),
        toEuclideanLin M v = g ∧ toEuclideanLin H v = c • toEuclideanLin M v) →
      secularFn g H M (lamc + δ) ^ β =
        secularFn g H M lamc ^ β + deriv (fun t => secularFn g H M t ^ β) lamc * δ) := by
  rw [secularFn_eq_secular hM, ← exists_scaledOp_scaledGrad_eq_iff (hM := hM)]
  obtain ⟨-, h2, -, h4, h5⟩ := secular_rpow_tangent (scaledGrad_ne_zero (hM := hM) hg)
    (neg_leftmost_lt_of_lambdaS_lt hH hM hc) (neg_leftmost_lt_of_lambdaS_lt hH hM (by linarith)) β
  exact ⟨h2, h4, h5⟩

/-! ### Derivatives of the secular function -/

/-- The **derivative vectors** `s⁽ᵏ⁾(λ)` of [cartis2022evaluation] Theorem 8.2.6:
`s⁽⁰⁾ = s(λ)` and `(H + λ M) s⁽ᵏ⁺¹⁾ = -(k + 1) M s⁽ᵏ⁾` (8.2.29), solved with `(H + λ M)⁻¹`. They are
the derivatives of `s(λ)` (`toScaled_secularDerivVec`). -/
noncomputable def secularDerivVec (g : EuclideanSpace ℝ (Fin n))
    (H M : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => stepOf g H M lam
  | k + 1 => toEuclideanLin (H + lam • M)⁻¹
      (-((k + 1 : ℝ) • toEuclideanLin M (secularDerivVec g H M lam k)))

theorem secularDerivVec_zero (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) : secularDerivVec g H M lam 0 = stepOf g H M lam :=
  rfl

theorem secularDerivVec_succ (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) (k : ℕ) :
    secularDerivVec g H M lam (k + 1) = toEuclideanLin (H + lam • M)⁻¹
      (-((k + 1 : ℝ) • toEuclideanLin M (secularDerivVec g H M lam k))) :=
  rfl

/-- The coefficients `α₀ = 1`, `αₖ₊₁ = 2 (2k + 3)/(k + 1) αₖ` of [cartis2022evaluation]
(8.2.30). -/
noncomputable def alphaCoeff : ℕ → ℝ
  | 0 => 1
  | k + 1 => 2 * (2 * k + 3) / (k + 1) * alphaCoeff k

/-- The coefficients (8.2.30) are `αₖ = (2k + 1)!/(k!)²`. -/
theorem alphaCoeff_eq_secularCoeff (k : ℕ) : alphaCoeff k = secularCoeff k := by
  induction k with
  | zero => simp [alphaCoeff, secularCoeff_zero]
  | succ k ih => rw [alphaCoeff, secularCoeff_succ, ih]

/-- The vectors (8.2.29) are, `M⁻¹`-transported, the derivatives `stepDeriv` of the operator
step, for `λ > -λ₁`. -/
theorem toScaled_secularDerivVec (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ}
    (hlam : -leftmost (isSymmetric_scaledOp (hM := hM) hH) < lam) (k : ℕ) :
    toScaled hM (secularDerivVec g H M lam k) =
      stepDeriv (scaledGrad hM g) (scaledOp H hM) k lam := by
  have hu : IsUnit (H + lam • M) :=
    isUnit_of_isUnit_add_smul_scaledOp (hM := hM)
      (isUnit_add_smul (hH := isSymmetric_scaledOp hH) hlam)
  induction k with
  | zero => rw [stepDeriv_zero, ← toScaled_stepOf hM]; rfl
  | succ k ih =>
    refine stepDeriv_succ_unique (hH := isSymmetric_scaledOp hH) hlam k ?_
    rw [secularDerivVec, add_smul_scaledOp_toScaled, toEuclideanLin_mul_nonsing_inv_apply hu,
      map_neg, map_smul, toEuclideanLin_nonsing_inv_mul_apply hM.isUnit, map_neg, map_smul, ih]

/-- **Theorem 8.2.6 of [cartis2022evaluation] (Derivatives of the secular function).** If
`H + λ M` is positive definite then for `k = 0, 1, …`,
`π⁽²ᵏ⁺¹⁾(λ) = 2 αₖ ⟪s⁽ᵏ⁾(λ), M s⁽ᵏ⁺¹⁾(λ)⟫` (8.2.27) and
`π⁽²ᵏ⁺²⁾(λ) = αₖ₊₁ ⟪s⁽ᵏ⁺¹⁾(λ), M s⁽ᵏ⁺¹⁾(λ)⟫` (8.2.28), with `s⁽ᵏ⁾` of (8.2.29) and `αₖ` of
(8.2.30). -/
theorem theorem_8_2_6 (hH : H.IsHermitian) (hM : M.PosDef) {lam : ℝ}
    (hpd : (H + lam • M).PosDef) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (secularFn g H M) lam = 2 * alphaCoeff k *
        ⟪secularDerivVec g H M lam k, toEuclideanLin M (secularDerivVec g H M lam (k + 1))⟫ ∧
      iteratedDeriv (2 * k + 2) (secularFn g H M) lam = alphaCoeff (k + 1) *
        ⟪secularDerivVec g H M lam (k + 1),
          toEuclideanLin M (secularDerivVec g H M lam (k + 1))⟫ := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp only [secularFn_of_isEmpty, Subsingleton.elim _ (0 : EuclideanSpace ℝ (Fin n)),
      inner_zero_left, mul_zero]
    exact ⟨by rw [iteratedDeriv_succ']; simp, by rw [iteratedDeriv_succ']; simp⟩
  · have : NeZero n := ⟨fun h => by subst h; exact (not_isEmpty_of_nonempty (Fin 0)) inferInstance⟩
    have hlam := neg_leftmost_lt_of_posDef hH hM hpd
    have hMs := isSymmetric_toEuclideanLin_iff.2 hM.isHermitian
    obtain ⟨h1, h2⟩ := iteratedDeriv_secular (g := scaledGrad hM g) hlam k
    rw [secularFn_eq_secular hM, h1, h2, ← toScaled_secularDerivVec hH hM hlam,
      ← toScaled_secularDerivVec hH hM hlam, ← real_inner_self_eq_norm_sq, inner_toScaled,
      inner_toScaled, alphaCoeff_eq_secularCoeff, alphaCoeff_eq_secularCoeff,
      ← hMs, ← hMs]
    exact ⟨rfl, rfl⟩

/-! ### Global optimality of the subproblems -/

/-- The trust-region multiplier conditions transport to the scaled setting. -/
theorem isTrustRegionMultiplier_scaled_iff (hM : M.PosDef) {Δ μ : ℝ}
    {s : EuclideanSpace ℝ (Fin n)} :
    IsTrustRegionMultiplier (scaledGrad hM g) (scaledOp H hM) Δ (toScaled hM s) μ ↔
      0 ≤ μ ∧ toEuclideanLin (H + μ • M) s = -g ∧ (H + μ • M).PosSemidef ∧
        μ * (mNorm M s - Δ) = 0 := by
  rw [mNorm_eq_norm_toScaled hM, ← add_smul_scaledOp_toScaled_eq_neg_iff (hM := hM),
    posSemidef_add_smul_iff_isPositive (hM := hM)]
  exact ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- Complementarity in squared form: for `Δ > 0`, `μ (‖s‖_M - Δ) = 0 ↔ μ (‖s‖_M² - Δ²) = 0`. -/
theorem mul_mNorm_sub_eq_zero_iff (M : Matrix (Fin n) (Fin n) ℝ) {Δ μ : ℝ} (hΔ : 0 < Δ)
    (s : EuclideanSpace ℝ (Fin n)) :
    μ * (mNorm M s - Δ) = 0 ↔ μ * (mNorm M s ^ 2 - Δ ^ 2) = 0 := by
  have h0 := mNorm_nonneg M s
  have hfac : mNorm M s ^ 2 - Δ ^ 2 = (mNorm M s - Δ) * (mNorm M s + Δ) := by ring
  rw [hfac, ← mul_assoc, mul_eq_zero (a := μ * _), or_iff_left (by positivity)]

/-- The **multiplier conditions** of Theorem 8.2.7 of [cartis2022evaluation] for a step `s` of the
trust-region subproblem (8.1.2) and a multiplier `λ`: `λ ≥ 0`, `(H + λ M) s = -g` (8.2.31),
`H + λ M` positive semidefinite and `λ (‖s‖_M² - Δ²) = 0` (8.2.32). -/
structure IsTrustRegionKKT (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (Δ : ℝ) (s : EuclideanSpace ℝ (Fin n)) (lam : ℝ) : Prop where
  /-- The multiplier is nonnegative. -/
  nonneg : 0 ≤ lam
  /-- The step solves the shifted system (8.2.31). -/
  shifted : toEuclideanLin (H + lam • M) s = -g
  /-- The shifted matrix is positive semidefinite. -/
  posSemidef : (H + lam • M).PosSemidef
  /-- Complementarity (8.2.32). -/
  complementarity : lam * (mNorm M s ^ 2 - Δ ^ 2) = 0

/-- The multiplier conditions are those of the operator subproblem in the `M`-inner product
space. -/
theorem isTrustRegionKKT_iff_scaled (hM : M.PosDef) {Δ μ : ℝ} (hΔ : 0 < Δ)
    {s : EuclideanSpace ℝ (Fin n)} :
    IsTrustRegionKKT g H M Δ s μ ↔
      IsTrustRegionMultiplier (scaledGrad hM g) (scaledOp H hM) Δ (toScaled hM s) μ := by
  rw [isTrustRegionMultiplier_scaled_iff hM, mul_mNorm_sub_eq_zero_iff M hΔ s]
  exact ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- **Theorem 8.2.7 of [cartis2022evaluation] (Trust-region subproblem global optimality).** Let
`Δ > 0`. Any global minimizer `s*` of (8.1.2) satisfies `(H + λ* M) s* = -g` (8.2.31) for some
`λ* ≥ 0` with `H + λ* M` positive semidefinite and `λ* (‖s*‖_M² - Δ²) = 0` (8.2.32)
(`IsTrustRegionKKT`); if `H + λ* M` is positive definite then `s*` is the unique global
minimizer. -/
theorem theorem_8_2_7 (hH : H.IsHermitian) (hM : M.PosDef) {Δ : ℝ} (hΔ : 0 < Δ)
    {s : EuclideanSpace ℝ (Fin n)} (hs : IsTrustRegionSolution g H M Δ s) :
    ∃ lamStar, IsTrustRegionKKT g H M Δ s lamStar ∧
      ((H + lamStar • M).PosDef → ∀ u, IsTrustRegionSolution g H M Δ u → u = s) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  obtain ⟨hn, hmin⟩ := (isTrustRegionSolution_iff_scaled hM).1 hs
  obtain ⟨μ, hμ⟩ := (isMinOn_closedBall_iff hT hΔ hn).1 hmin
  refine ⟨μ, (isTrustRegionKKT_iff_scaled hM hΔ).2 hμ, fun hpd u hu => ?_⟩
  obtain ⟨hun, humin⟩ := (isTrustRegionSolution_iff_scaled hM).1 hu
  have hc := ((posDef_add_smul_iff_isSymmetricCoercive (hM := hM) μ).1 hpd).isCoercive
  exact (toScaled hM).injective (eq_of_isMinOn_closedBall_of_posDef hT hμ hn hc hun humin)

/-- **Theorem 8.2.8 of [cartis2022evaluation] (Regularization subproblem global optimality).**
Let `σ > 0` and `r > 2`. Any global minimizer `s*` of (8.1.3) satisfies `(H + λ* M) s* = -g`
(8.2.31) with `λ* = σ ‖s*‖_M^{r-2}` (8.2.33) and `H + λ* M` positive semidefinite; if `H + λ* M` is
positive definite then `s*` is the unique global minimizer. -/
theorem theorem_8_2_8 (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    {s : EuclideanSpace ℝ (Fin n)} (hs : IsRegularizationSolution g H M σ r s) :
    toEuclideanLin (H + (σ * mNorm M s ^ (r - 2)) • M) s = -g ∧
      (H + (σ * mNorm M s ^ (r - 2)) • M).PosSemidef ∧
      ((H + (σ * mNorm M s ^ (r - 2)) • M).PosDef →
        ∀ u, IsRegularizationSolution g H M σ r u → u = s) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hmin := (isRegularizationSolution_iff_scaled hM).1 hs
  obtain ⟨h1, h2⟩ := (isMinOn_regModel_iff hT hσ hr).1 hmin
  rw [mNorm_eq_norm_toScaled hM]
  refine ⟨(add_smul_scaledOp_toScaled_eq_neg_iff _ g s).1 h1,
    (posSemidef_add_smul_iff_isPositive _).2 h2, fun hpd u hu => ?_⟩
  have hc := ((posDef_add_smul_iff_isSymmetricCoercive (hM := hM) _).1 hpd).isCoercive
  exact (toScaled hM).injective (eq_of_isMinOn_regModel_of_posDef hT hσ hr hmin hc
    ((isRegularizationSolution_iff_scaled hM).1 hu))

/-! ### Sufficiency of the optimality conditions -/

section Sufficiency

/-- **Sufficiency of the multiplier conditions** for (8.1.2): a feasible step `s` with a multiplier
`λ` (`IsTrustRegionKKT`) is a global minimizer of the trust-region subproblem. -/
theorem isTrustRegionSolution_of_kkt (hH : H.IsHermitian) (hM : M.PosDef) {Δ lam : ℝ}
    (hΔ : 0 < Δ) {s : EuclideanSpace ℝ (Fin n)} (h : IsTrustRegionKKT g H M Δ s lam)
    (hs : mNorm M s ≤ Δ) : IsTrustRegionSolution g H M Δ s := by
  rw [isTrustRegionSolution_iff_scaled hM]
  rw [mNorm_eq_norm_toScaled hM] at hs
  exact ⟨hs, ((isTrustRegionKKT_iff_scaled hM hΔ).1 h).isMinOn (isSymmetric_scaledOp hH)⟩

/-- **Sufficiency of the optimality conditions** for (8.1.3): if `(H + λ M) s = -g` with
`λ = σ ‖s‖_M^{r-2}` and `H + λ M ⪰ 0`, then `s` is a global minimizer of the regularization
subproblem. -/
theorem isRegularizationSolution_of_shifted (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ}
    (hσ : 0 < σ) (hr : 2 < r) {s : EuclideanSpace ℝ (Fin n)}
    (h1 : toEuclideanLin (H + (σ * mNorm M s ^ (r - 2)) • M) s = -g)
    (h2 : (H + (σ * mNorm M s ^ (r - 2)) • M).PosSemidef) :
    IsRegularizationSolution g H M σ r s := by
  rw [isRegularizationSolution_iff_scaled hM, isMinOn_regModel_iff (isSymmetric_scaledOp hH) hσ hr]
  rw [mNorm_eq_norm_toScaled hM] at h1 h2
  exact ⟨(add_smul_scaledOp_toScaled_eq_neg_iff _ g s).2 h1,
    (posSemidef_add_smul_iff_isPositive _).1 h2⟩

/-- A step with a multiplier `λ` for which `H + λ M` is positive definite is the unique global
minimizer of the trust-region subproblem (8.1.2). -/
theorem eq_of_isTrustRegionKKT_of_posDef (hH : H.IsHermitian) (hM : M.PosDef) {Δ lam : ℝ}
    (hΔ : 0 < Δ) {s : EuclideanSpace ℝ (Fin n)} (h : IsTrustRegionKKT g H M Δ s lam)
    (hs : mNorm M s ≤ Δ) (hpd : (H + lam • M).PosDef) {u : EuclideanSpace ℝ (Fin n)}
    (hu : IsTrustRegionSolution g H M Δ u) : u = s := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  obtain ⟨hun, humin⟩ := (isTrustRegionSolution_iff_scaled hM).1 hu
  have hc := ((posDef_add_smul_iff_isSymmetricCoercive (hM := hM) lam).1 hpd).isCoercive
  rw [mNorm_eq_norm_toScaled hM] at hs
  exact (toScaled hM).injective (eq_of_isMinOn_closedBall_of_posDef hT
    ((isTrustRegionKKT_iff_scaled hM hΔ).1 h) hs hc hun humin)

end Sufficiency

end CartisGouldToint.Chapter08
