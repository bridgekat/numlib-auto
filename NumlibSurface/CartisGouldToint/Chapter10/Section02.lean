import NumlibSurface.CartisGouldToint.Chapter09.Section03
import NumlibSurface.CartisGouldToint.Chapter10.Section01

/-!
# Cartis–Gould–Toint §10.2: Computational details for regularization methods

Surface file for [cartis2022evaluation] §10.2: the Krylov subspace solutions `sₖ = Qₖ s̄ₖ` of the
regularization subproblem, where `s̄ₖ` globally minimizes the reduced problem (10.1.6)
`γ₁ ⟪e₁, s̄⟫ + ½ ⟪s̄, Tₖ s̄⟫ + (σ/r) ‖s̄‖^r` on `ℝᵏ`.

## Main definitions

* `algorithm_10_2_1`, `algorithm_10_2_2` — the factorization of the shifted Lanczos tridiagonal
  `Tₖ + λ Iₖ` and the solve with its factors.
* `conditionNumber_10_2_8` — the condition number `κₖ = (θₖ,ₖ + λₖ)/(θ₁,ₖ + λₖ)` (10.2.8);
  `kappaStar` — `κ* = max_{1 ≤ k ≤ grade} κₖ` (10.2.10).

## Main results

* `subspace_optimality_10_2_2` — (10.2.2)–(10.2.3): `(Tₖ + λₖ Iₖ) s̄ₖ = -γ₁ e₁` with `Tₖ + λₖ Iₖ`
  positive definite (no hard case in the subspace).
* `algorithm_10_2_1_spec`, `algorithm_10_2_2_spec` — correctness of the two algorithms.
* `lemma_10_2_1` — the multipliers and norms increase with `k`.
* `start_10_2_3` — the one-dimensional start (10.2.7).
* `theorem_10_2_2` — the gradient bound (10.2.9).
* `corollary_10_2_3` — the iteration bound.

## Implementation notes

`‖M⁻¹H‖` in Theorem 10.2.2 and Corollary 10.2.3 is the operator norm of `M⁻¹H` induced by the
scaled norm `‖·‖_M` (the norm of `Subproblem.scaledOp H hM` on the `M`-inner product space), which
equals `‖M^{-1/2} H M^{-1/2}‖₂`; with this reading the identity (B.10.4) holds. It is bounded by
the Euclidean operator norm of `M⁻¹H` (`Subproblem.norm_scaledOp_le`).

## Corrections to the source

* Lemma 10.2.1 refers to "a global minimizer of (8.1.4)"; (8.1.4) is the model, the problem is
  (8.1.3).
* Corollary 10.2.3: the printed bound `⌈log A / log((√κ* + 1)/(√κ* - 1))⌉ + 1` is unsatisfiable when
  `log A < 0` (e.g. for large `θ₁`) and undefined for `κ* = 1`. The ceiling is read as `⌈·⌉₊`, and
  for `κ* = 1` the test holds at some `k ≤ min(2, grade)`. The hypothesis `g ≠ 0` is needed.
-/

open Matrix Set
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter10

open Subproblem CartisGouldToint.Chapter08 CartisGouldToint.Chapter09

variable {n : ℕ} {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}

/-! ### The scaled form of the Krylov subproblems -/

section Scaled

/-- A positive `k ≤ grade(M⁻¹H, M⁻¹g)` forces `g ≠ 0`. -/
theorem ne_zero_of_le_gradeHM (hM : M.PosDef) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ gradeHM H M g) :
    scaledGrad hM g ≠ 0 := fun hb => by
  rw [gradeHM_eq hM, hb, Krylov.grade_zero] at hk
  omega

/-- The Lanczos tridiagonal is symmetric. -/
theorem lanczosTridiag_isHermitian (hM : M.PosDef) (k : ℕ) :
    (lanczosTridiag hM H g k).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.2 (Lanczos.tridiag_isSymm _ _ _)

/-- `Qₖ s̄` lies in `𝒦ₖ`, in the `M`-inner product space. -/
theorem toScaled_lanczosBasis_mem (hM : M.PosDef) {k : ℕ} (y : EuclideanSpace ℝ (Fin k)) :
    toScaled hM (toEuclideanLin (lanczosBasis hM H g k) y) ∈
      Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) k :=
  (toScaled_mem_krylov_iff hM).2 (range_lanczosBasis hM ▸ LinearMap.mem_range_self _ y)

/-- A solution `s̄ₖ` of the reduced problem (10.1.6) gives, `M⁻¹`-transported, a minimizer of the
operator regularized model over the Krylov subspace `𝒦ₖ`. -/
theorem isMinOn_krylov_of_reduced (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} {k : ℕ}
    (hk : k ≤ gradeHM H M g) {sbar : EuclideanSpace ℝ (Fin k)}
    (hs : IsRegularizationSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 σ r sbar) :
    IsMinOn (Subproblem.regModel (scaledGrad hM g) (scaledOp H hM) σ r)
      (Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
        (scaledGrad hM g) k : Set (ScaledSpace hM))
      (toScaled hM (toEuclideanLin (lanczosBasis hM H g k) sbar)) :=
  ((isRegSubspaceSolution_iff_scaled hM).1
    ((isRegSubspaceSolution_krylov_iff hM hH hk σ r sbar).2 hs)).2

/-- The gradient of the regularized model in the `M`-inner product space. -/
theorem mNorm_inv_gradient (hM : M.PosDef) (s : EuclideanSpace ℝ (Fin n)) (lam : ℝ) :
    mNorm M⁻¹ (g + toEuclideanLin H s + lam • toEuclideanLin M s) =
      ‖scaledGrad hM g + scaledOp H hM (toScaled hM s) + lam • toScaled hM s‖ := by
  rw [mNorm_inv_eq_norm_scaledGrad hM, scaledGrad_gradient, _root_.add_apply,
    _root_.smul_apply, one_apply_eq_self, add_assoc]

end Scaled

/-! ### Optimality of the subspace solution (§10.2.1) -/

/-- **Optimality of the Krylov subspace solution** ([cartis2022evaluation] (10.2.2)–(10.2.3),
§10.2.1). Let `H` be symmetric, `M` positive definite, `σ > 0`, `r > 2`,
`1 ≤ k ≤ grade(M⁻¹H, M⁻¹g)`, and let `s̄ₖ` globally minimize the reduced problem (10.1.6). Then
with `λₖ = σ ‖s̄ₖ‖^{r-2} = σ ‖Qₖ s̄ₖ‖_M^{r-2}`:
`(Tₖ + λₖ Iₖ) s̄ₖ = -γ₁ e₁` ((10.2.2), `γ₁ = ‖g‖_{M⁻¹}`), and `Tₖ + λₖ Iₖ` is positive definite (the
hard case cannot occur for the unreduced `Tₖ`); in particular `s̄ₖ` is the unique global
minimizer. -/
theorem subspace_optimality_10_2_2 (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} (hσ : 0 < σ)
    (hr : 2 < r) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ gradeHM H M g)
    {sbar : EuclideanSpace ℝ (Fin k)}
    (hs : IsRegularizationSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 σ r sbar) :
    toEuclideanLin (lanczosTridiag hM H g k + (σ * ‖sbar‖ ^ (r - 2)) • (1 : Matrix _ _ ℝ)) sbar =
        -EuclideanSpace.single ⟨0, hk1⟩ (mNorm M⁻¹ g) ∧
      σ * ‖sbar‖ ^ (r - 2) = σ * mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbar) ^ (r - 2) ∧
      (lanczosTridiag hM H g k + (σ * ‖sbar‖ ^ (r - 2)) • (1 : Matrix _ _ ℝ)).PosDef ∧
      ∀ u, IsRegularizationSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 σ r u →
        u = sbar := by
  obtain ⟨h1, -, h3⟩ := theorem_8_2_8 (lanczosTridiag_isHermitian hM k) PosDef.one hσ hr hs
  rw [mNorm_one, lanczosGrad_eq hM hk1] at h1
  rw [mNorm_one] at h3
  have hpd : (lanczosTridiag hM H g k + (σ * ‖sbar‖ ^ (r - 2)) • (1 : Matrix _ _ ℝ)).PosDef := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hT := isSymmetric_scaledOp (hM := hM) hH
    have hb := ne_zero_of_le_gradeHM hM hk1 hk
    have hmin := isMinOn_krylov_of_reduced hH hM hk hs
    have hlt := (neg_leftmost_lt_of_isMinOn_regModel_krylov hT hb hσ hr hk1
      (toScaled_lanczosBasis_mem hM sbar) hmin).1
    rw [← mNorm_eq_norm_toScaled hM, mNorm_lanczosBasis hM hk] at hlt
    exact posDef_tridiag_add hT hb (by rw [← gradeHM_eq hM]; exact hk) hlt
  exact ⟨h1, by rw [mNorm_lanczosBasis hM hk], hpd, h3 hpd⟩

/-! ### Factorizing and solving shifted Lanczos systems (Algorithms 10.2.1–10.2.2) -/

section Algorithms

variable (ρ γ : ℕ → ℝ) (lam : ℝ)

/-- The reciprocal pivots `rᵢ(λ)` computed by Algorithm 10.2.1 (`0`-based: `ρ i`, `γ i` are the
book's `ρᵢ₊₁`, `γᵢ₊₁`): `r₀ = 1/(ρ₀ + λ)`, `rᵢ₊₁ = 1/(ρᵢ₊₁ + λ - γᵢ₊₁ lᵢ₊₁)` with
`lᵢ₊₁ = γᵢ₊₁ rᵢ`. -/
noncomputable def recipPivot : ℕ → ℝ
  | 0 => 1 / (ρ 0 + lam)
  | i + 1 => 1 / (ρ (i + 1) + lam - γ (i + 1) * (γ (i + 1) * recipPivot i))

/-- The tests of Algorithm 10.2.1: `ρ₀ + λ > 0`, and `ρᵢ₊₁ + λ > γᵢ₊₁ lᵢ₊₁` for the later rows. -/
def pivotTest : ℕ → Prop
  | 0 => 0 < ρ 0 + lam
  | i + 1 => γ (i + 1) * (γ (i + 1) * recipPivot ρ γ lam i) < ρ (i + 1) + lam

/-- Extension by zero of a vector on `Fin k` to `ℕ`. -/
def extendFin {k : ℕ} (v : Fin k → ℝ) (j : ℕ) : ℝ := if h : j < k then v ⟨j, h⟩ else 0

omit ρ γ lam in
@[simp]
theorem extendFin_val {k : ℕ} (v : Fin k → ℝ) (i : Fin k) : extendFin v i = v i := by
  simp [extendFin]

/-- **Algorithm 10.2.1 of [cartis2022evaluation]** (factorize the shifted Lanczos tridiagonal
`Tₖ + λ Iₖ`, `Tₖ = symTridiag ρ γ k` with diagonal `ρ₀, …, ρₖ₋₁` and off-diagonal
`γ₁, …, γₖ₋₁`): it exits with "not positive definite" (`none`) as soon as a test
`pivotTest` fails, and otherwise returns the multipliers `lᵢ = γᵢ rᵢ₋₁` (`l₀` unused, set to `0`)
and the reciprocal pivots `rᵢ`. -/
noncomputable def algorithm_10_2_1 (k : ℕ) : Option ((Fin k → ℝ) × (Fin k → ℝ)) :=
  open Classical in
  if ∀ i < k, pivotTest ρ γ lam i then
    some (fun i => if (i : ℕ) = 0 then 0 else γ i * recipPivot ρ γ lam (i - 1),
      fun i => recipPivot ρ γ lam i)
  else none

/-- The reciprocal pivots are the reciprocals of the `LDLᵀ` pivots. -/
theorem recipPivot_eq (i : ℕ) : recipPivot ρ γ lam i = (ldlPivot ρ γ lam i)⁻¹ := by
  induction i with
  | zero => rw [recipPivot, ldlPivot_zero, one_div]
  | succ i ih =>
    rw [recipPivot, ih, ldlPivot_succ, one_div]
    congr 1
    ring

/-- The tests of Algorithm 10.2.1 are the positivity of the pivots. -/
theorem pivotTest_iff (i : ℕ) : pivotTest ρ γ lam i ↔ 0 < ldlPivot ρ γ lam i := by
  cases i with
  | zero => rfl
  | succ i =>
    rw [pivotTest, recipPivot_eq, ldlPivot_succ]
    have : γ (i + 1) * (γ (i + 1) * (ldlPivot ρ γ lam i)⁻¹) =
        γ (i + 1) ^ 2 / ldlPivot ρ γ lam i := by ring
    rw [this, sub_pos]

/-- **Correctness of Algorithm 10.2.1** ([cartis2022evaluation] (10.2.5)–(10.2.6), §10.2.1–10.2.2).
(i) The algorithm exits with "not positive definite" iff `Tₖ + λ Iₖ` is not positive definite.
(ii) If it returns `(l, r)`, then `Tₖ + λ Iₖ = Lₖ Dₖ Lₖᵀ` with `Lₖ` unit lower bidiagonal with
subdiagonal entries `lᵢ` and `Dₖ = diag(1/rᵢ)` with positive entries.
(iii) If `Tₖ + λ Iₖ` is positive definite, then `Tₖ₊₁ + λ Iₖ₊₁` is positive definite iff
`ρₖ + λ > γₖ² rₖ₋₁(λ)` (book indexing `ρₖ₊₁ + λ > γₖ₊₁² rₖ(λ)`). -/
theorem algorithm_10_2_1_spec (k : ℕ) :
    (algorithm_10_2_1 ρ γ lam k = none ↔
      ¬ (symTridiag ρ γ k + lam • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef) ∧
    (∀ l r, algorithm_10_2_1 ρ γ lam k = some (l, r) →
      symTridiag ρ γ k + lam • (1 : Matrix (Fin k) (Fin k) ℝ) =
          lowerBidiagonalOf (extendFin l) k * diagonal (fun i => (r i)⁻¹) *
            (lowerBidiagonalOf (extendFin l) k)ᵀ ∧
        ∀ i, 0 < (r i)⁻¹) ∧
    ((symTridiag ρ γ (k + 1) + lam • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)).PosDef →
      ((symTridiag ρ γ (k + 2) + lam • (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ)).PosDef ↔
        γ (k + 1) ^ 2 * recipPivot ρ γ lam k < ρ (k + 1) + lam)) := by
  have hpd : (symTridiag ρ γ k + lam • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef ↔
      ∀ i < k, pivotTest ρ γ lam i := by
    rw [posDef_symTridiag_add_iff]
    exact forall₂_congr fun i _ => (pivotTest_iff ρ γ lam i).symm
  refine ⟨?_, fun l r hlr => ?_, fun h => ?_⟩
  · rw [hpd, algorithm_10_2_1]
    split_ifs with h
    · exact iff_of_false (by simp) (not_not.2 h)
    · exact iff_of_true rfl h
  · rw [algorithm_10_2_1] at hlr
    split_ifs at hlr with ht
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hlr)
    have hd : ∀ i < k, 0 < ldlPivot ρ γ lam i := fun i hi => (pivotTest_iff ρ γ lam i).1 (ht i hi)
    have hL : lowerBidiagonalOf (extendFin fun i : Fin k =>
        if (i : ℕ) = 0 then 0 else γ i * recipPivot ρ γ lam (i - 1)) k = ldlLower ρ γ lam k := by
      rw [ldlLower_eq]
      ext i j
      simp only [lowerBidiagonalOf, of_apply, extendFin_val]
      by_cases h1 : i = j
      · simp [h1]
      by_cases h2 : (j : ℕ) + 1 = i
      · have h3 : (i : ℕ) ≠ 0 := by omega
        obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) = m + 1 := ⟨i - 1, by omega⟩
        simp only [h1, h2, h3, ite_false, ite_true]
        rw [hm, ldlMult_succ, Nat.add_sub_cancel, recipPivot_eq, div_eq_mul_inv]
      · simp [h1, h2]
    refine ⟨?_, fun i => by
      change 0 < (recipPivot ρ γ lam i)⁻¹
      rw [recipPivot_eq, inv_inv]; exact hd i i.2⟩
    have hD : (fun i : Fin k => ((fun i : Fin k => recipPivot ρ γ lam i) i)⁻¹) =
        fun i : Fin k => ldlPivot ρ γ lam i := funext fun i => by
      change (recipPivot ρ γ lam i)⁻¹ = _
      rw [recipPivot_eq, inv_inv]
    rw [hL, hD, symTridiag_add_smul_one_eq_ldl ρ γ lam fun i hi => (hd i (by omega)).ne']
  · rw [posDef_symTridiag_succ_add_iff ρ γ lam h, recipPivot_eq, div_eq_mul_inv]

/-- The forward substitution `x₀ = b₀`, `xᵢ₊₁ = bᵢ₊₁ - lᵢ₊₁ xᵢ` of Algorithm 10.2.2. -/
noncomputable def solveForward {k : ℕ} (l b : Fin k → ℝ) : ℕ → ℝ
  | 0 => extendFin b 0
  | i + 1 => extendFin b (i + 1) - extendFin l (i + 1) * solveForward l b i

/-- The backward substitution `xₖ₋₁` unchanged, `xᵢ ← xᵢ - lᵢ₊₁ xᵢ₊₁` of Algorithm 10.2.2. -/
noncomputable def solveBackward (k : ℕ) (l' z : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i + 1 < k then z i - l' (i + 1) * solveBackward k l' z (i + 1) else z i
termination_by k - i

theorem solveBackward_eq (k : ℕ) (l' z : ℕ → ℝ) (i : ℕ) :
    solveBackward k l' z i =
      if i + 1 < k then z i - l' (i + 1) * solveBackward k l' z (i + 1) else z i := by
  rw [solveBackward]

/-- **Algorithm 10.2.2 of [cartis2022evaluation]** (solve `(Tₖ + λ Iₖ) x = b` with the factors
`l`, `r` of Algorithm 10.2.1): forward substitution `xᵢ = bᵢ - lᵢ xᵢ₋₁`, scaling `xᵢ ← rᵢ xᵢ`,
backward substitution `xᵢ₋₁ ← xᵢ₋₁ - lᵢ xᵢ`. -/
noncomputable def algorithm_10_2_2 {k : ℕ} (l r b : Fin k → ℝ) : Fin k → ℝ :=
  fun i => solveBackward k (extendFin l) (fun j => extendFin r j * solveForward l b j) i

/-- **Correctness of Algorithm 10.2.2** ((10.2.4)): if Algorithm 10.2.1 returns the factors
`(l, r)` of `Tₖ + λ Iₖ`, then Algorithm 10.2.2 solves `(Tₖ + λ Iₖ) x = b`. -/
theorem algorithm_10_2_2_spec {k : ℕ} {l r : Fin k → ℝ}
    (h : algorithm_10_2_1 ρ γ lam k = some (l, r)) (b : Fin k → ℝ) :
    (symTridiag ρ γ k + lam • (1 : Matrix (Fin k) (Fin k) ℝ)) *ᵥ algorithm_10_2_2 l r b = b := by
  rw [algorithm_10_2_1] at h
  split_ifs at h with ht
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hd : ∀ i < k, 0 < ldlPivot ρ γ lam i := fun i hi => (pivotTest_iff ρ γ lam i).1 (ht i hi)
  set l : Fin k → ℝ := fun i => if (i : ℕ) = 0 then 0 else γ i * recipPivot ρ γ lam (i - 1)
  have hl : ∀ i, 1 ≤ i → i < k → extendFin l i = ldlMult ρ γ lam i := fun i hi1 hik => by
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    simp only [extendFin, hik, dite_true, l, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      ite_false, Nat.add_sub_cancel]
    rw [ldlMult_succ, recipPivot_eq, div_eq_mul_inv]
  have hf : ∀ j < k, solveForward l b j =
      ldlForward ρ γ lam (fun j => if h : j < k then b ⟨j, h⟩ else 0) j := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [solveForward, ldlForward, ih (by omega), hl _ (by omega) hj]
      rfl
  have hb : ∀ m i, i + m + 1 = k →
      solveBackward k (extendFin l) (fun j => extendFin (fun i : Fin k => recipPivot ρ γ lam i) j *
          solveForward l b j) i =
        ldlBackward ρ γ lam k (fun j => ldlForward ρ γ lam
          (fun j => if h : j < k then b ⟨j, h⟩ else 0) j / ldlPivot ρ γ lam j) i := by
    have hz : ∀ j < k, extendFin (fun i : Fin k => recipPivot ρ γ lam i) j * solveForward l b j =
        ldlForward ρ γ lam (fun j => if h : j < k then b ⟨j, h⟩ else 0) j / ldlPivot ρ γ lam j :=
      fun j hj => by
        simp only [extendFin, hj, dite_true]
        rw [hf j hj, recipPivot_eq, div_eq_mul_inv, mul_comm]
    intro m
    induction m with
    | zero =>
      intro i hi
      rw [solveBackward_eq, ldlBackward_eq, ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hz i (by omega)
    | succ m ih =>
      intro i hi
      rw [solveBackward_eq, ldlBackward_eq, ite_eq_left (by omega), ite_eq_left (by omega),
        ih (i + 1) (by omega), hz i (by omega), hl _ (by omega) (by omega)]
  have heq : algorithm_10_2_2 l (fun i => recipPivot ρ γ lam i) b = tridiagSolve ρ γ lam k b := by
    funext i
    exact hb (k - 1 - i) i (by omega)
  rw [heq]
  exact mulVec_tridiagSolve ρ γ lam (fun i hi => (hd i hi).ne') b

end Algorithms

/-! ### Monotonicity (Lemma 10.2.1) and the start (§10.2.3) -/

/-- **Lemma 10.2.1 of [cartis2022evaluation] (Nested subspace solutions increase in norm).** Let
`H` be symmetric, `M` positive definite, `σ > 0`, `r > 2`, `1 ≤ k ≤ ℓ ≤ grade(M⁻¹H, M⁻¹g)`; let
`sₖ = Qₖ s̄ₖ`, `sℓ = Qℓ s̄ℓ` with `s̄ₖ`, `s̄ℓ` global minimizers of (10.1.6), with multipliers
`λₖ = σ ‖sₖ‖_M^{r-2}`, `λℓ = σ ‖sℓ‖_M^{r-2}` (10.2.3), and let `s*` be a global minimizer of
(8.1.3) (printed "(8.1.4)") with `λ* = σ ‖s*‖_M^{r-2}`. Then `λₖ ≤ λℓ ≤ λ*` and
`‖sₖ‖_M ≤ ‖sℓ‖_M ≤ ‖s*‖_M`. -/
theorem lemma_10_2_1 (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    {k ℓ : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) (hℓ : ℓ ≤ gradeHM H M g)
    {sbark : EuclideanSpace ℝ (Fin k)} {sbarl : EuclideanSpace ℝ (Fin ℓ)}
    (hsk : IsRegularizationSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 σ r sbark)
    (hsl : IsRegularizationSolution (lanczosGrad hM H g ℓ) (lanczosTridiag hM H g ℓ) 1 σ r sbarl)
    {sstar : EuclideanSpace ℝ (Fin n)} (hstar : IsRegularizationSolution g H M σ r sstar) :
    (σ * mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbark) ^ (r - 2) ≤
        σ * mNorm M (toEuclideanLin (lanczosBasis hM H g ℓ) sbarl) ^ (r - 2) ∧
      σ * mNorm M (toEuclideanLin (lanczosBasis hM H g ℓ) sbarl) ^ (r - 2) ≤
        σ * mNorm M sstar ^ (r - 2)) ∧
    mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbark) ≤
        mNorm M (toEuclideanLin (lanczosBasis hM H g ℓ) sbarl) ∧
      mNorm M (toEuclideanLin (lanczosBasis hM H g ℓ) sbarl) ≤ mNorm M sstar := by
  simp only [mNorm_eq_norm_toScaled hM]
  exact krylov_multiplier_mono_regularization (isSymmetric_scaledOp hH) hσ hr hk hkℓ
    (toScaled_lanczosBasis_mem hM sbark) (isMinOn_krylov_of_reduced hH hM (hkℓ.trans hℓ) hsk)
    (toScaled_lanczosBasis_mem hM sbarl) (isMinOn_krylov_of_reduced hH hM hℓ hsl)
    ((isRegularizationSolution_iff_scaled hM).1 hstar)

/-- **Starting the Lanczos process** ([cartis2022evaluation] §10.2.3, (10.2.7)). For `k = 1` the
problem (10.1.6) is `min_{s ∈ ℝ} γ₁ s + ½ ρ₁ s² + (1/r) σ |s|^r`. Let `γ₁ ≠ 0`, `σ > 0`, `r > 2`
and let `s̄₁` be a global minimizer, with multiplier `λ₁ = σ |s̄₁|^{r-2}`. Then
`γ₁ + (ρ₁ + λ₁) s̄₁ = 0` (10.2.7), `ρ₁ + λ₁ > 0` and `λ₁ > 0`, and `λ₁` is the unique root on
`λ > max(0, -ρ₁)` of the rearranged secular equation `λ (ρ₁ + λ)^{r-2} = σ |γ₁|^{r-2}`; for
`r = 3` it is the larger root `(-ρ₁ + √(ρ₁² + 4σ|γ₁|))/2` of a quadratic. -/
theorem start_10_2_3 {γ₁ ρ₁ σ r : ℝ} (hγ : γ₁ ≠ 0) (hσ : 0 < σ) (hr : 2 < r) {s : ℝ}
    (hs : ∀ u : ℝ, γ₁ * s + 1 / 2 * ρ₁ * s ^ 2 + 1 / r * σ * |s| ^ r ≤
      γ₁ * u + 1 / 2 * ρ₁ * u ^ 2 + 1 / r * σ * |u| ^ r) :
    γ₁ + (ρ₁ + σ * |s| ^ (r - 2)) * s = 0 ∧ 0 < ρ₁ + σ * |s| ^ (r - 2) ∧
      0 < σ * |s| ^ (r - 2) ∧
      σ * |s| ^ (r - 2) * (ρ₁ + σ * |s| ^ (r - 2)) ^ (r - 2) = σ * |γ₁| ^ (r - 2) ∧
      (∀ μ, max 0 (-ρ₁) < μ → μ * (ρ₁ + μ) ^ (r - 2) = σ * |γ₁| ^ (r - 2) →
        μ = σ * |s| ^ (r - 2)) ∧
      (r = 3 → σ * |s| ^ (r - 2) = (-ρ₁ + √(ρ₁ ^ 2 + 4 * σ * |γ₁|)) / 2) := by
  set T : ℝ →L[ℝ] ℝ := ρ₁ • (1 : ℝ →L[ℝ] ℝ)
  have hT : (T : ℝ →ₗ[ℝ] ℝ).IsSymmetric := fun x y => by
    simp only [T, ContinuousLinearMap.coe_coe, _root_.smul_apply, one_apply_eq_self,
      real_inner_smul_left, real_inner_smul_right]
  have hmin : IsMinOn (Subproblem.regModel γ₁ T σ r) univ s := isMinOn_univ_iff.2 fun u => by
    have := hs u
    simp only [Subproblem.regModel_def, quadModel_def, T, _root_.smul_apply, one_apply_eq_self,
      Real.norm_eq_abs, RCLike.inner_apply, conj_trivial, smul_eq_mul]
    calc _ = γ₁ * s + 1 / 2 * ρ₁ * s ^ 2 + 1 / r * σ * |s| ^ r := by ring
      _ ≤ _ := this
      _ = _ := by ring
  obtain ⟨h1, h2⟩ := (isMinOn_regModel_iff hT hσ hr).1 hmin
  simp only [T, _root_.add_apply, _root_.smul_apply, one_apply_eq_self, smul_eq_mul,
    Real.norm_eq_abs] at h1
  set lam := σ * |s| ^ (r - 2) with hlam
  have hshift : γ₁ + (ρ₁ + lam) * s = 0 := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; apply hγ; linarith
  have hlam0 : 0 < lam := mul_pos hσ (Real.rpow_pos_of_pos (abs_pos.2 hs0) _)
  have hpos : 0 ≤ ρ₁ + lam := by
    have := h2.inner_nonneg_left 1
    simp only [ContinuousLinearMap.coe_coe, T, _root_.add_apply, _root_.smul_apply,
      one_apply_eq_self, smul_eq_mul, RCLike.inner_apply, conj_trivial, Real.norm_eq_abs] at this
    linarith [hlam]
  have hpos' : 0 < ρ₁ + lam := by
    refine lt_of_le_of_ne hpos fun h => hγ ?_
    rw [← h, zero_mul, add_zero] at hshift; exact hshift
  have habs : |γ₁| = (ρ₁ + lam) * |s| := by
    rw [show γ₁ = -((ρ₁ + lam) * s) by linarith, abs_neg, abs_mul, abs_of_pos hpos']
  have hroot : lam * (ρ₁ + lam) ^ (r - 2) = σ * |γ₁| ^ (r - 2) := by
    rw [habs, Real.mul_rpow hpos'.le (abs_nonneg _), hlam]; ring
  have hmono : ∀ a b, max 0 (-ρ₁) < a → a < b →
      a * (ρ₁ + a) ^ (r - 2) < b * (ρ₁ + b) ^ (r - 2) := by
    intro a b ha hab
    have ha0 : 0 < a := lt_of_le_of_lt (le_max_left _ _) ha
    have hρa : 0 < ρ₁ + a := by have := lt_of_le_of_lt (le_max_right _ _) ha; linarith
    have h3 : (ρ₁ + a) ^ (r - 2) ≤ (ρ₁ + b) ^ (r - 2) :=
      Real.rpow_le_rpow hρa.le (by linarith) (by linarith)
    have h4 : 0 < (ρ₁ + a) ^ (r - 2) := Real.rpow_pos_of_pos hρa _
    calc a * (ρ₁ + a) ^ (r - 2) < b * (ρ₁ + a) ^ (r - 2) := mul_lt_mul_of_pos_right hab h4
      _ ≤ b * (ρ₁ + b) ^ (r - 2) := mul_le_mul_of_nonneg_left h3 (by linarith)
  have hlamD : max 0 (-ρ₁) < lam := max_lt hlam0 (by linarith)
  refine ⟨hshift, hpos', hlam0, hroot, fun μ hμ hμr => ?_, fun hr3 => ?_⟩
  · rcases lt_trichotomy μ lam with h | h | h
    · exact absurd (hμr.trans hroot.symm) (hmono μ lam hμ h).ne
    · exact h
    · exact absurd (hroot.trans hμr.symm) (hmono lam μ hlamD h).ne
  · rw [hr3, show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one, Real.rpow_one] at hroot
    have hsq : ρ₁ ^ 2 + 4 * σ * |γ₁| = (2 * lam + ρ₁) ^ 2 := by nlinarith
    rw [hsq, Real.sqrt_sq (by linarith)]
    ring

/-! ### The gradient bound (Theorem 10.2.2) and the iteration bound (Corollary 10.2.3) -/

/-- The **condition number** `κₖ = κ(Tₖ + λ Iₖ) = (θₖ,ₖ + λ)/(θ₁,ₖ + λ)` of
[cartis2022evaluation] (10.2.8), `θ₁,ₖ ≤ θₖ,ₖ` the extreme Ritz values (eigenvalues of `Tₖ`,
`Lanczos.ritzValues`); the book evaluates it at the multiplier `λ = λₖ`. -/
noncomputable def conditionNumber_10_2_8 (hM : M.PosDef) (H : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (lam : ℝ) : ℝ :=
  ((⨆ i, Lanczos.ritzValues (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
      (scaledGrad hM g) k i) + lam) /
    ((⨅ i, Lanczos.ritzValues (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
      (scaledGrad hM g) k i) + lam)

/-- The **largest condition number** `κ* = max_{1 ≤ k ≤ grade} κₖ(λₖ)` of [cartis2022evaluation]
(10.2.10), for multipliers `λₖ = lam k`. -/
noncomputable def kappaStar (hM : M.PosDef) (H : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (lam : ℕ → ℝ) : ℝ :=
  ⨆ k : Finset.Icc 1 (gradeHM H M g), conditionNumber_10_2_8 hM H g k (lam k)

/-- Below the grade, `κₖ` is the condition number of the shifted compression of `M⁻¹H` to
`𝒦ₖ`. -/
theorem conditionNumber_eq_krylovCond (hH : H.IsHermitian) (hM : M.PosDef) {k : ℕ}
    (hk : k ≤ gradeHM H M g) (lam : ℝ) :
    conditionNumber_10_2_8 hM H g k lam =
      krylovCond (isSymmetric_scaledOp hH) (scaledGrad hM g) k lam := by
  rw [krylovCond_eq_ritzValues _ (by rw [← gradeHM_eq hM]; exact hk), conditionNumber_10_2_8]

/-- `κₖ ≤ κ*`. -/
theorem le_kappaStar (hM : M.PosDef) (lam : ℕ → ℝ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ gradeHM H M g) :
    conditionNumber_10_2_8 hM H g k (lam k) ≤ kappaStar hM H g lam :=
  le_ciSup (f := fun k : Finset.Icc 1 (gradeHM H M g) => conditionNumber_10_2_8 hM H g k (lam k))
    (Finite.bddAbove_range _) ⟨k, Finset.mem_Icc.2 ⟨hk1, hk⟩⟩

/-- **Theorem 10.2.2 of [cartis2022evaluation] (Bound on the gradient at the subspace
minimizer).** Let `H` be symmetric, `M` positive definite, `σ > 0`, `r > 2`,
`1 ≤ k ≤ grade(M⁻¹H, M⁻¹g)`, let `s̄ₖ` globally minimize (10.1.6), `sₖ = Qₖ s̄ₖ`,
`λₖ = σ ‖sₖ‖_M^{r-2}` (10.2.3) and `κₖ` the condition number (10.2.8). Then the gradient (8.2.34)
`∇ₛ m^R(sₖ) = g + H sₖ + λₖ M sₖ` satisfies (10.2.9):
`‖∇ₛ m^R(sₖ)‖_{M⁻¹} ≤ 2 ‖M⁻¹H‖ κₖ (λₖ/σ)^{1/(r-2)} ((√κₖ - 1)/(√κₖ + 1))^{k-1}`,
`‖M⁻¹H‖` the operator norm induced by `‖·‖_M`. -/
theorem theorem_10_2_2 (hH : H.IsHermitian) (hM : M.PosDef) {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ gradeHM H M g) {sbar : EuclideanSpace ℝ (Fin k)}
    (hs : IsRegularizationSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 σ r sbar) :
    mNorm M⁻¹ (g + toEuclideanLin H (toEuclideanLin (lanczosBasis hM H g k) sbar) +
        (σ * mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbar) ^ (r - 2)) •
          toEuclideanLin M (toEuclideanLin (lanczosBasis hM H g k) sbar)) ≤
      2 * ‖scaledOp H hM‖ *
        conditionNumber_10_2_8 hM H g k
          (σ * mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbar) ^ (r - 2)) *
        (σ * mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbar) ^ (r - 2) / σ) ^ (1 / (r - 2)) *
        ((√(conditionNumber_10_2_8 hM H g k
            (σ * mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbar) ^ (r - 2))) - 1) /
          (√(conditionNumber_10_2_8 hM H g k
            (σ * mNorm M (toEuclideanLin (lanczosBasis hM H g k) sbar) ^ (r - 2))) + 1)) ^
          (k - 1) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hb := ne_zero_of_le_gradeHM hM hk1 hk
  have hmem := toScaled_lanczosBasis_mem (H := H) (g := g) hM sbar
  have hmin := isMinOn_krylov_of_reduced hH hM hk hs
  have hbound := krylov_gradient_bound_regularization hT hb hσ hr hk1 hmem hmin
  rw [mNorm_inv_gradient hM, mNorm_eq_norm_toScaled hM, conditionNumber_eq_krylovCond hH hM hk]
  exact hbound

/-- **Corollary 10.2.3 of [cartis2022evaluation] (Iteration bound for the subspace
approximation)**, corrected. Let `H` be symmetric, `M` positive definite, `g ≠ 0`, `σ > 0`,
`r > 2`, `θ₁ > 0`; for `1 ≤ k ≤ grade(M⁻¹H, M⁻¹g)` let `s̄ₖ` globally minimize (10.1.6),
`sₖ = Qₖ s̄ₖ`, `λₖ = σ ‖sₖ‖_M^{r-2}`, and let `s*` globally minimize (8.1.3),
`λ* = σ ‖s*‖_M^{r-2}`. Let `κ*` be (10.2.10), `λ_max[H, M]` the largest pencil eigenvalue and
`A = (4 ‖M⁻¹H‖_M κ*/θ₁) (λ*/σ)^{1/(r-2)} ((λ_max[H, M] + λ*)/‖g‖_{M⁻¹})²`. Then the stopping rule
(9.3.14b) `‖g + H sₖ + λₖ M sₖ‖_{M⁻¹} ≤ ½ θ₁ ‖sₖ‖_M²` holds for some
`1 ≤ k ≤ min(⌈log A / log((√κ* + 1)/(√κ* - 1))⌉₊ + 1, grade)` when `κ* > 1`, and for some
`1 ≤ k ≤ min(2, grade)` when `κ* = 1`. -/
theorem corollary_10_2_3 (hH : H.IsHermitian) (hM : M.PosDef) (hg : g ≠ 0) {σ r θ : ℝ}
    (hσ : 0 < σ) (hr : 2 < r) (hθ : 0 < θ) {sbar : (k : ℕ) → EuclideanSpace ℝ (Fin k)}
    (hs : ∀ k, 1 ≤ k → k ≤ gradeHM H M g →
      IsRegularizationSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 σ r (sbar k))
    {s : ℕ → EuclideanSpace ℝ (Fin n)}
    (hsk : ∀ k, s k = toEuclideanLin (lanczosBasis hM H g k) (sbar k))
    {sstar : EuclideanSpace ℝ (Fin n)} (hstar : IsRegularizationSolution g H M σ r sstar) :
    (1 < kappaStar hM H g (fun k => σ * mNorm M (s k) ^ (r - 2)) →
      ∃ k, 1 ≤ k ∧
        k ≤ min (⌈Real.log (4 * ‖scaledOp H hM‖ *
            kappaStar hM H g (fun k => σ * mNorm M (s k) ^ (r - 2)) / θ *
            (σ * mNorm M sstar ^ (r - 2) / σ) ^ (1 / (r - 2)) *
            ((rightmostPencil hH hM + σ * mNorm M sstar ^ (r - 2)) / mNorm M⁻¹ g) ^ 2) /
          Real.log ((√(kappaStar hM H g (fun k => σ * mNorm M (s k) ^ (r - 2))) + 1) /
            (√(kappaStar hM H g (fun k => σ * mNorm M (s k) ^ (r - 2))) - 1))⌉₊ + 1)
          (gradeHM H M g) ∧
        mNorm M⁻¹ (g + toEuclideanLin H (s k) +
            (σ * mNorm M (s k) ^ (r - 2)) • toEuclideanLin M (s k)) ≤
          1 / 2 * θ * mNorm M (s k) ^ 2) ∧
    (kappaStar hM H g (fun k => σ * mNorm M (s k) ^ (r - 2)) = 1 →
      ∃ k, 1 ≤ k ∧ k ≤ min 2 (gradeHM H M g) ∧
        mNorm M⁻¹ (g + toEuclideanLin H (s k) +
            (σ * mNorm M (s k) ^ (r - 2)) • toEuclideanLin M (s k)) ≤
          1 / 2 * θ * mNorm M (s k) ^ 2) := by
  have hT := isSymmetric_scaledOp (hM := hM) hH
  have hb := scaledGrad_ne_zero (hM := hM) hg
  set κs := kappaStar hM H g (fun k => σ * mNorm M (s k) ^ (r - 2))
  set G := gradeHM H M g with hGdef
  have hGeq : G = Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
      (scaledGrad hM g) := gradeHM_eq hM
  have hG : 1 ≤ G := by rw [hGeq]; exact Krylov.grade_pos_of_ne_zero _ _ hb
  have hS : ∀ k, toScaled hM (s k) ∈
      Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) k :=
    fun k => hsk k ▸ toScaled_lanczosBasis_mem hM (sbar k)
  have hmin : ∀ k, 1 ≤ k → k ≤ Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] _)
      (scaledGrad hM g) → IsMinOn (Subproblem.regModel (scaledGrad hM g) (scaledOp H hM) σ r)
        (Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] _) (scaledGrad hM g) k :
          Set (ScaledSpace hM)) (toScaled hM (s k)) := fun k hk1 hk => by
    rw [← hGeq] at hk
    rw [hsk k]
    exact isMinOn_krylov_of_reduced hH hM hk (hs k hk1 hk)
  have hκs : ∀ k, 1 ≤ k → k ≤ Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] _)
      (scaledGrad hM g) → krylovCond hT (scaledGrad hM g) k (σ * ‖toScaled hM (s k)‖ ^ (r - 2)) ≤
        κs := fun k hk1 hk => by
    rw [← hGeq] at hk
    rw [← mNorm_eq_norm_toScaled hM, ← conditionNumber_eq_krylovCond hH hM hk]
    exact le_kappaStar hM (fun k => σ * mNorm M (s k) ^ (r - 2)) hk1 hk
  have hκ1 : 1 ≤ κs := by
    refine le_trans ?_ (hκs 1 le_rfl (hGeq ▸ hG))
    exact one_le_krylovCond hT (neg_leftmost_lt_of_isMinOn_regModel_krylov hT hb hσ hr le_rfl
      (hS 1) (hmin 1 le_rfl (hGeq ▸ hG))).1
  obtain ⟨hP, hPG, -, -⟩ := krylov_iteration_bound_regularization hT hb hσ hr hθ hS hmin
    ((isRegularizationSolution_iff_scaled hM).1 hstar) hκs
  rw [← hGeq] at hP hPG
  simp only [← mNorm_eq_norm_toScaled hM, ← rightmostPencil_eq hH hM,
    ← mNorm_inv_eq_norm_scaledGrad hM] at hP hPG
  have htest : ∀ k, ‖scaledGrad hM g + scaledOp H hM (toScaled hM (s k)) +
      (σ * mNorm M (s k) ^ (r - 2)) • toScaled hM (s k)‖ =
      mNorm M⁻¹ (g + toEuclideanLin H (s k) +
        (σ * mNorm M (s k) ^ (r - 2)) • toEuclideanLin M (s k)) := fun k =>
    (mNorm_inv_gradient hM _ _).symm
  simp only [htest] at hP hPG
  set A := 4 * ‖scaledOp H hM‖ * κs / θ *
    (σ * mNorm M sstar ^ (r - 2) / σ) ^ (1 / (r - 2)) *
    ((rightmostPencil hH hM + σ * mNorm M sstar ^ (r - 2)) / mNorm M⁻¹ g) ^ 2
  have hP' : ∀ k, 1 ≤ k → k ≤ G → A * convFactor κs ^ (k - 1) ≤ 1 →
      mNorm M⁻¹ (g + toEuclideanLin H (s k) +
        (σ * mNorm M (s k) ^ (r - 2)) • toEuclideanLin M (s k)) ≤
          1 / 2 * θ * mNorm M (s k) ^ 2 := fun k hk1 hk hA => by
    refine hP k hk1 hk (le_trans ?_ hA)
    have hq := convFactor_nonneg hκ1
    have : 0 ≤ κs := by linarith
    have : 0 ≤ (σ * mNorm M sstar ^ (r - 2) / σ) ^ (1 / (r - 2)) :=
      Real.rpow_nonneg (div_nonneg (mul_nonneg hσ.le
        (Real.rpow_nonneg (mNorm_nonneg _ _) _)) hσ.le) _
    simp only [A]
    gcongr
  obtain ⟨h1, h2⟩ := exists_le_min_of_geometric hG hP' hPG
  refine ⟨fun hκ => ?_, fun hκ => h2 (by rw [hκ, convFactor_one])⟩
  have := h1 (convFactor_pos hκ) (convFactor_lt_one κs)
  rwa [convFactor, one_div_div] at this

end CartisGouldToint.Chapter10
