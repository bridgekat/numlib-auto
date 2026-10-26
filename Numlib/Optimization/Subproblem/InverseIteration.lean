import Mathlib.Analysis.Normed.Module.Normalize
import Numlib.Nonlinear.Order
import Numlib.Optimization.Subproblem.Secular

/-!
# Inverse iteration with Rayleigh-quotient shifts from the definite side

Let `H` be a symmetric operator on a finite-dimensional real inner product space `E`, with
leftmost eigenvalue `λ₁` and leftmost eigenspace `E₁ = ker (H - λ₁)`. Algorithm 9.3.1 of
Cartis–Gould–Toint, *Evaluation complexity of algorithms for nonconvex optimization* (after
Gould–Robinson–Thorne), produces shifts `ℓₖ > -λ₁`, i.e. with `H + ℓₖ` positive definite, that
converge to `-λ₁` with any prescribed Q-order. From a unit vector `zₖ` it performs `nₖ` steps of
shifted inverse iteration `z ↦ (H + ℓₖ)⁻¹ z`, normalizes the result to `zₖ₊₁`, computes the
Rayleigh quotient `ρₖ₊₁ = ⟪zₖ₊₁, H zₖ₊₁⟫ ≥ λ₁` and sets
`ℓₖ₊₁ = -ρₖ₊₁ + ωₖ (ℓₖ + ρₖ₊₁) ^ γₖ`.

As in `Numlib.Optimization.Subproblem.Secular`, the scaling matrix `M` of the book is not a
parameter: `E` carries the energy inner product, in which the pencil `(H, M)` becomes the single
symmetric operator `M⁻¹ H`.

## Main definitions

* `leftmostSpace hH`: the leftmost eigenspace `E₁`; `leftmostWeight hH z` and `restWeight hH z`
  are the squared norms of the components of `z` in `E₁` and in `E₁ᗮ`.
* `IsInverseIterationRun`: a run of Algorithm 9.3.1.

## Main results

* `starProjection_leftmostSpace`, `norm_starProjection_leftmostSpace_sq`,
  `norm_sub_starProjection_leftmostSpace_sq`: the orthogonal projection onto `E₁` in the
  eigenvector basis.
* `rayleigh_sub_leftmost_le`: `0 ≤ ρ(z) - λ₁ ≤ (λₙ - λ₁) ‖(1 - P₁) z‖²` for unit `z`.
* `restWeight_div_leftmostWeight_inverse_pow_le`: `n` shifted inverse steps multiply the squared
  tangent `‖(1 - P₁) z‖² / ‖P₁ z‖²` by at most `((ℓ + λ₁) / (ℓ + λ₁ + μ)) ^ (2 n)`, where `μ` is
  a lower bound of the spectral gap.
* `IsInverseIterationRun.convergence`, `IsInverseIterationRun.convergence_of_eventually_const`:
  Theorem 9.3.1.

## Corrections to the source

* The start condition `z₀ ∈ 𝒵₁` of the book is `⟨z₀, vᵢ⟩ ≠ 0` for some leftmost eigenvector
  `vᵢ`; for `M ≠ I` this is the wrong inner product. The condition used here is
  `P₁ z₀ ≠ 0` for the orthogonal projection `P₁` onto `E₁` in the inner product of `E` (the
  `M`-inner product), i.e. `⟨z₀, M vᵢ⟩ ≠ 0` for some `M`-orthonormal leftmost eigenvector.
* The closeness `ε` must depend on a bound for `nₖ`. The book allows `n_U = ∞`, and then no
  single `ε` serves all runs: for `H = diag (0, μ)` with `μ < 1` and `z₀ = (1, 1)/√2`, the choices
  `γ₀ = 2 n₀ - γ_U` and `n₀` large give `ℓ₁ < -λ₁` from any given `ℓ₀ ∈ (-λ₁, 1 - μ - λ₁)`,
  because the Rayleigh-quotient error `≈ μ (e/(e+μ))^(2 n₀)` beats `ω e ^ γ₀`. The book's
  statement holds when the sequences `nₖ, ωₖ, γₖ` are fixed before `ε`, with `nₖ` eventually
  constant (`IsInverseIterationRun.convergence_of_eventually_const`, `n_U = ∞` allowed);
  `IsInverseIterationRun.convergence` gives an `ε` uniform over all runs when `n_U < ∞`.
* Only `γₖ = γ̄` for large `k` is needed for the Q-order `γ̄`; `nₖ` may keep varying. The two-sided
  error bounds hold at every iteration.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : E →L[ℝ] E}

/-! ### The leftmost eigenspace in the eigenvector basis -/

section Spectral

variable (hH : (H : E →ₗ[ℝ] E).IsSymmetric)

/-- The leftmost eigenspace `E₁ = ker (H - λ₁)` of the symmetric operator `H`. -/
noncomputable def leftmostSpace : Submodule ℝ E :=
  Module.End.eigenspace (H : E →ₗ[ℝ] E) (leftmost hH)

/-- The squared norm `‖P₁ z‖²` of the component of `z` in the leftmost eigenspace, in the
eigenvector basis (`norm_starProjection_leftmostSpace_sq`). -/
noncomputable def leftmostWeight (z : E) : ℝ :=
  ∑ i, if hH.eigenvalues rfl i = leftmost hH then ⟪hH.eigenvectorBasis rfl i, z⟫ ^ 2 else 0

/-- The squared norm `‖(1 - P₁) z‖²` of the component of `z` orthogonal to the leftmost
eigenspace, in the eigenvector basis (`norm_sub_starProjection_leftmostSpace_sq`). -/
noncomputable def restWeight (z : E) : ℝ :=
  ∑ i, if hH.eigenvalues rfl i = leftmost hH then 0 else ⟪hH.eigenvectorBasis rfl i, z⟫ ^ 2

variable {hH}

/-- The coordinates of `H v` in the eigenvector basis: `⟪bᵢ, H v⟫ = λᵢ ⟪bᵢ, v⟫`. -/
theorem inner_eigenvectorBasis_apply (v : E) (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, H v⟫ = hH.eigenvalues rfl i * ⟪hH.eigenvectorBasis rfl i, v⟫ := by
  simpa using inner_eigenvectorBasis_add_smul (hH := hH) 0 v i

theorem mem_leftmostSpace_iff {v : E} : v ∈ leftmostSpace hH ↔ H v = leftmost hH • v := by
  rw [leftmostSpace, Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe]

/-- The squared norm in the coordinates of the eigenvector basis. -/
theorem norm_sq_eq_sum_eigenvectorBasis (v : E) :
    ‖v‖ ^ 2 = ∑ i, ⟪hH.eigenvectorBasis rfl i, v⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum_eigenvectorBasis (hH := hH)]
  simp [sq]

/-- A vector of the leftmost eigenspace has no component along eigenvectors of other
eigenvalues. -/
theorem inner_eigenvectorBasis_eq_zero_of_mem {v : E} (hv : v ∈ leftmostSpace hH)
    {i : Fin (Module.finrank ℝ E)} (hi : hH.eigenvalues rfl i ≠ leftmost hH) :
    ⟪hH.eigenvectorBasis rfl i, v⟫ = 0 := by
  have h := inner_eigenvectorBasis_apply (hH := hH) v i
  rw [mem_leftmostSpace_iff.1 hv, real_inner_smul_right] at h
  have h' : (hH.eigenvalues rfl i - leftmost hH) * ⟪hH.eigenvectorBasis rfl i, v⟫ = 0 := by
    rw [sub_mul]; linarith
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hi)

/-- The orthogonal projection onto the leftmost eigenspace keeps the leftmost coordinates. -/
theorem starProjection_leftmostSpace (z : E) :
    (leftmostSpace hH).starProjection z = ∑ i, (if hH.eigenvalues rfl i = leftmost hH then
      ⟪hH.eigenvectorBasis rfl i, z⟫ else 0) • hH.eigenvectorBasis rfl i := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [mem_leftmostSpace_iff]
    refine eq_of_inner_eigenvectorBasis (hH := hH) fun j => ?_
    rw [inner_eigenvectorBasis_apply, inner_eigenvectorBasis_sum, real_inner_smul_right,
      inner_eigenvectorBasis_sum]
    split_ifs with h <;> simp [h]
  · intro w hw
    rw [inner_eq_sum_eigenvectorBasis (hH := hH)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_sub_right, inner_eigenvectorBasis_sum]
    split_ifs with h
    · simp
    · rw [inner_eigenvectorBasis_eq_zero_of_mem hw h, mul_zero]

theorem inner_eigenvectorBasis_starProjection (z : E) (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, (leftmostSpace hH).starProjection z⟫ =
      if hH.eigenvalues rfl i = leftmost hH then ⟪hH.eigenvectorBasis rfl i, z⟫ else 0 := by
  rw [starProjection_leftmostSpace, inner_eigenvectorBasis_sum]

theorem norm_starProjection_leftmostSpace_sq (z : E) :
    ‖(leftmostSpace hH).starProjection z‖ ^ 2 = leftmostWeight hH z := by
  rw [norm_sq_eq_sum_eigenvectorBasis (hH := hH), leftmostWeight]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_eigenvectorBasis_starProjection]
  split_ifs <;> simp

theorem norm_sub_starProjection_leftmostSpace_sq (z : E) :
    ‖z - (leftmostSpace hH).starProjection z‖ ^ 2 = restWeight hH z := by
  rw [norm_sq_eq_sum_eigenvectorBasis (hH := hH), restWeight]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sub_right, inner_eigenvectorBasis_starProjection]
  split_ifs <;> simp

theorem leftmostWeight_nonneg (z : E) : 0 ≤ leftmostWeight hH z :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

theorem restWeight_nonneg (z : E) : 0 ≤ restWeight hH z :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

theorem leftmostWeight_add_restWeight (z : E) :
    leftmostWeight hH z + restWeight hH z = ‖z‖ ^ 2 := by
  rw [norm_sq_eq_sum_eigenvectorBasis (hH := hH), leftmostWeight, restWeight,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem leftmostWeight_smul (c : ℝ) (z : E) :
    leftmostWeight hH (c • z) = c ^ 2 * leftmostWeight hH z := by
  rw [leftmostWeight, leftmostWeight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right]
  split_ifs <;> ring

theorem restWeight_smul (c : ℝ) (z : E) :
    restWeight hH (c • z) = c ^ 2 * restWeight hH z := by
  rw [restWeight, restWeight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_right]
  split_ifs <;> ring

theorem starProjection_leftmostSpace_ne_zero_iff {z : E} :
    (leftmostSpace hH).starProjection z ≠ 0 ↔ 0 < leftmostWeight hH z := by
  rw [← norm_starProjection_leftmostSpace_sq, ← norm_ne_zero_iff]
  exact ⟨fun h => pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)) 2,
    fun h h0 => by simp [h0] at h⟩

/-- The Rayleigh quotient in the eigenvector basis:
`⟪z, H z⟫ - λ₁ ‖z‖² = ∑ᵢ (λᵢ - λ₁) ⟪bᵢ, z⟫²`. -/
theorem inner_apply_sub_leftmost_mul (z : E) :
    ⟪z, H z⟫ - leftmost hH * ‖z‖ ^ 2 =
      ∑ i, (hH.eigenvalues rfl i - leftmost hH) * ⟪hH.eigenvectorBasis rfl i, z⟫ ^ 2 := by
  rw [inner_eq_sum_eigenvectorBasis (hH := hH) z (H z), norm_sq_eq_sum_eigenvectorBasis (hH := hH),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_eigenvectorBasis_apply]
  ring

/-- The Rayleigh-quotient error of a unit vector is at most `(λₙ - λ₁)` times its squared
component off the leftmost eigenspace (coordinate form of `rayleigh_sub_leftmost_le`). -/
theorem rayleigh_sub_leftmost_le_restWeight {z : E} (hz : ‖z‖ = 1) :
    0 ≤ ⟪z, H z⟫ - leftmost hH ∧
      ⟪z, H z⟫ - leftmost hH ≤ (rightmost hH - leftmost hH) * restWeight hH z := by
  have h := inner_apply_sub_leftmost_mul (hH := hH) z
  rw [hz, one_pow, mul_one] at h
  rw [h, restWeight, Finset.mul_sum]
  constructor
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (sub_nonneg.2 (leftmost_le_eigenvalues i)) (sq_nonneg _)
  · refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with hi
    · simp [hi]
    · exact mul_le_mul_of_nonneg_right
        (by linarith [eigenvalues_le_rightmost (hH := hH) i]) (sq_nonneg _)

/-- **The Rayleigh quotient is second-order accurate** (standard; used in Theorem 9.3.1). For a
unit vector `z`, with `P₁` the orthogonal projection onto the leftmost eigenspace:
`0 ≤ ⟪z, H z⟫ - λ₁ ≤ (λₙ - λ₁) ‖(1 - P₁) z‖²`, and if `P₁ z ≠ 0` then the off-eigenspace
component is at most the tangent: `‖(1 - P₁) z‖ ≤ t = ‖(1 - P₁) z‖ / ‖P₁ z‖`. -/
theorem rayleigh_sub_leftmost_le {z : E} (hz : ‖z‖ = 1) :
    0 ≤ ⟪z, H z⟫ - leftmost hH ∧
      ⟪z, H z⟫ - leftmost hH ≤
        (rightmost hH - leftmost hH) * ‖z - (leftmostSpace hH).starProjection z‖ ^ 2 ∧
      ((leftmostSpace hH).starProjection z ≠ 0 →
        ‖z - (leftmostSpace hH).starProjection z‖ ≤
          ‖z - (leftmostSpace hH).starProjection z‖ /
            ‖(leftmostSpace hH).starProjection z‖) := by
  refine ⟨(rayleigh_sub_leftmost_le_restWeight hz).1, ?_, fun hP => ?_⟩
  · rw [norm_sub_starProjection_leftmostSpace_sq]
    exact (rayleigh_sub_leftmost_le_restWeight hz).2
  · have h1 : ‖(leftmostSpace hH).starProjection z‖ ≤ 1 := by
      have := leftmostWeight_add_restWeight (hH := hH) z
      rw [hz, ← norm_starProjection_leftmostSpace_sq] at this
      nlinarith [restWeight_nonneg (hH := hH) z,
        norm_nonneg ((leftmostSpace hH).starProjection z)]
    exact le_div_self (norm_nonneg _) (norm_pos_iff.2 hP) h1

/-- There is a positive lower bound `μ ≤ 1` on the gap `λᵢ - λ₁` between the leftmost eigenvalue
and every other eigenvalue. -/
theorem exists_spectralGap :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧
      ∀ i, hH.eigenvalues rfl i ≠ leftmost hH → leftmost hH + μ ≤ hH.eigenvalues rfl i := by
  let f : Fin (Module.finrank ℝ E) → ℝ := fun i =>
    if hH.eigenvalues rfl i = leftmost hH then 1 else hH.eigenvalues rfl i - leftmost hH
  have hf : ∀ i, 0 < f i := fun i => by
    simp only [f]
    split_ifs with h
    · exact one_pos
    · exact sub_pos.2 (lt_of_le_of_ne (leftmost_le_eigenvalues i) (Ne.symm h))
  have key : ∀ μ, μ ≤ 1 → (∀ i, μ ≤ f i) →
      ∀ i, hH.eigenvalues rfl i ≠ leftmost hH → leftmost hH + μ ≤ hH.eigenvalues rfl i :=
    fun μ _ hμ i hi => by
      have := hμ i
      simp only [f, hi, ite_false] at this
      linarith
  rcases isEmpty_or_nonempty (Fin (Module.finrank ℝ E)) with hE | hE
  · exact ⟨1, one_pos, le_rfl, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨min 1 (f i₀), lt_min one_pos (hf i₀), min_le_left _ _,
      key _ (min_le_left _ _) fun i => (min_le_right _ _).trans (hi₀ i)⟩

/-- **Shifted inverse iteration reduces the tangent.** Let `ℓ > -λ₁` and let `μ > 0` bound the
gap between `λ₁` and the other eigenvalues. For `v = (H + ℓ)⁻ⁿ z`:
`‖P₁ v‖² = ‖P₁ z‖² / (ℓ + λ₁) ^ (2 n)` and the squared tangent `‖(1 - P₁) v‖² / ‖P₁ v‖²` is at
most `((ℓ + λ₁)ⁿ / (ℓ + λ₁ + μ)ⁿ)²` times that of `z`. -/
theorem restWeight_div_leftmostWeight_inverse_pow_le {μ ℓ : ℝ} (hμ : 0 < μ)
    (hgap : ∀ i, hH.eigenvalues rfl i ≠ leftmost hH → leftmost hH + μ ≤ hH.eigenvalues rfl i)
    (hℓ : -leftmost hH < ℓ) (n : ℕ) (z : E) :
    leftmostWeight hH ((Ring.inverse (H + ℓ • 1) ^ n) z) =
        leftmostWeight hH z / ((ℓ + leftmost hH) ^ n) ^ 2 ∧
      restWeight hH ((Ring.inverse (H + ℓ • 1) ^ n) z) ≤
        restWeight hH z / ((ℓ + leftmost hH + μ) ^ n) ^ 2 := by
  have he : 0 < ℓ + leftmost hH := by linarith
  constructor
  · rw [leftmostWeight, leftmostWeight, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_eigenvectorBasis_inverse_pow hℓ]
    split_ifs with hi
    · rw [hi, div_pow]
    · simp
  · rw [restWeight, restWeight, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [inner_eigenvectorBasis_inverse_pow hℓ]
    split_ifs with hi
    · simp
    · rw [div_pow]
      have := hgap i hi
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) n) 2)

/-- One block of Algorithm 9.3.1 in the eigenvector basis: normalizing `v = (H + ℓ)⁻ⁿ z` gives a
unit vector with nonzero leftmost component whose squared tangent is at most
`((ℓ + λ₁)ⁿ / (ℓ + λ₁ + μ)ⁿ)²` times that of `z`. -/
theorem inverseIteration_block {μ ℓ : ℝ} (hμ : 0 < μ)
    (hgap : ∀ i, hH.eigenvalues rfl i ≠ leftmost hH → leftmost hH + μ ≤ hH.eigenvalues rfl i)
    (hℓ : -leftmost hH < ℓ) (n : ℕ) {z v : E} (hz : 0 < leftmostWeight hH z)
    (hv : v = (Ring.inverse (H + ℓ • 1) ^ n) z) :
    ‖‖v‖⁻¹ • v‖ = 1 ∧ 0 < leftmostWeight hH (‖v‖⁻¹ • v) ∧
      restWeight hH (‖v‖⁻¹ • v) / leftmostWeight hH (‖v‖⁻¹ • v) ≤
        ((ℓ + leftmost hH) ^ n / (ℓ + leftmost hH + μ) ^ n) ^ 2 *
          (restWeight hH z / leftmostWeight hH z) := by
  obtain ⟨hL, hR⟩ := restWeight_div_leftmostWeight_inverse_pow_le hμ hgap hℓ n z
  rw [← hv] at hL hR
  have he : 0 < ℓ + leftmost hH := by linarith
  have hLv : 0 < leftmostWeight hH v := by rw [hL]; positivity
  have hv0 : v ≠ 0 := by rintro rfl; simp [leftmostWeight] at hLv
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hc : (‖v‖⁻¹) ^ 2 ≠ 0 := by positivity
  refine ⟨by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne'], ?_, ?_⟩
  · rw [leftmostWeight_smul]; positivity
  · rw [leftmostWeight_smul, restWeight_smul, mul_div_mul_left _ _ hc, hL, div_pow]
    have hA : ((ℓ + leftmost hH) ^ n) ^ 2 ≠ 0 := by positivity
    have hD : ((ℓ + leftmost hH + μ) ^ n) ^ 2 ≠ 0 := by positivity
    have hL0 := hz.ne'
    calc restWeight hH v / (leftmostWeight hH z / ((ℓ + leftmost hH) ^ n) ^ 2)
        ≤ restWeight hH z / ((ℓ + leftmost hH + μ) ^ n) ^ 2 /
            (leftmostWeight hH z / ((ℓ + leftmost hH) ^ n) ^ 2) :=
          div_le_div_of_nonneg_right hR (by positivity)
      _ = _ := by field_simp

end Spectral

/-! ### Algorithm 9.3.1 -/

variable (hH : (H : E →ₗ[ℝ] E).IsSymmetric)

/-- A run of **Algorithm 9.3.1** (potential hard case) with constants `ωL, ωU, γL, γU, nU`:
shifts `ℓ k` (the book's `λᴳₖ`, starting with `ℓ 0 > -λ₁`), unit vectors `z k`, numbers of inverse
iterations `1 ≤ n k ≤ nU`, and parameters `ω k ∈ [ωL, ωU]`, `γ k ∈ [γL, 2 n k - γU]`;
`z (k+1)` is the normalization of `(H + ℓ k)⁻ⁿ⁽ᵏ⁾ z k` (normalizing after each inverse step, as
the book does, gives the same vector) and `ℓ (k+1) = -ρ + ω k (ℓ k + ρ) ^ γ k` with the Rayleigh
quotient `ρ = ⟪z (k+1), H z (k+1)⟫`. The book's constants satisfy `0 < ωL ≤ ωU`, `0 < γU ≤ 1`,
`1 < γL ≤ 2 - γU` and `1 ≤ nU ≤ ∞`; they are hypotheses of the theorems, not of the run. -/
structure IsInverseIterationRun (ωL ωU γL γU : ℝ) (nU : ℕ∞) (ℓ : ℕ → ℝ) (z : ℕ → E)
    (n : ℕ → ℕ) (ω γ : ℕ → ℝ) : Prop where
  norm_zero : ‖z 0‖ = 1
  shift_zero : -leftmost hH < ℓ 0
  one_le_count : ∀ k, 1 ≤ n k
  count_le : ∀ k, (n k : ℕ∞) ≤ nU
  weight_mem : ∀ k, ω k ∈ Icc ωL ωU
  exponent_mem : ∀ k, γ k ∈ Icc γL (2 * n k - γU)
  vector_succ : ∀ k, z (k + 1) = ‖(Ring.inverse (H + ℓ k • 1) ^ n k) (z k)‖⁻¹ •
    (Ring.inverse (H + ℓ k • 1) ^ n k) (z k)
  shift_succ : ∀ k, ℓ (k + 1) = -⟪z (k + 1), H (z (k + 1))⟫ +
    ω k * (ℓ k + ⟪z (k + 1), H (z (k + 1))⟫) ^ γ k

variable {hH}

/-- The error recursion of the shift update: with `e = ℓ + λ₁` and the Rayleigh-quotient error
`d = ρ - λ₁ ≥ 0`, the new error is `e' = ω (e + d) ^ γ - d`. If `e ≤ ε` and `d ≤ K e ^ (2 n)` for
an `ε` small in terms of `K` and the constants, then `ωL/2 · e ^ γ ≤ e' ≤ ωU 2 ^ γ e ^ γ` and
`e' ≤ e / 2`. -/
theorem shiftUpdate_bounds {ωL ωU γL γU K ε e d ω γ : ℝ} {n N : ℕ} (hγU : 0 < γU)
    (hγL : 1 < γL) (hK : 0 ≤ K) (hε1 : ε ≤ 1) (hKε : K * ε ≤ 1)
    (hKεγ : K * ε ^ γU ≤ ωL / 2) (hωε : ωU * 2 ^ (2 * N : ℝ) * ε ^ (γL - 1) ≤ 1 / 2)
    (he : 0 < e) (heε : e ≤ ε) (hd0 : 0 ≤ d) (hd : d ≤ K * e ^ (2 * n)) (hn : 1 ≤ n)
    (hnN : n ≤ N) (hω : ω ∈ Icc ωL ωU) (hγ : γ ∈ Icc γL (2 * n - γU)) :
    ωL / 2 * e ^ γ ≤ ω * (e + d) ^ γ - d ∧ ω * (e + d) ^ γ - d ≤ ωU * 2 ^ γ * e ^ γ ∧
      ω * (e + d) ^ γ - d ≤ e / 2 := by
  have he1 : e ≤ 1 := heε.trans hε1
  have hγ0 : 0 ≤ γ := by linarith [hγ.1]
  have hωL : 0 ≤ ωL := by
    have : 0 ≤ K * ε ^ γU := mul_nonneg hK (Real.rpow_nonneg (he.le.trans heε) _)
    linarith
  have hω0 : 0 ≤ ω := hωL.trans hω.1
  have heγ : 0 ≤ e ^ γ := Real.rpow_nonneg he.le _
  -- `d ≤ K ε ^ γU e ^ γ ≤ ωL/2 · e ^ γ`
  have hpow : e ^ (2 * n) = e ^ ((2 * n : ℝ) - γ) * e ^ γ := by
    rw [← Real.rpow_add he, sub_add_cancel, ← Real.rpow_natCast]
    norm_num
  have h1 : e ^ ((2 * n : ℝ) - γ) ≤ ε ^ γU :=
    (Real.rpow_le_rpow_of_exponent_ge he he1 (by linarith [hγ.2])).trans
      (Real.rpow_le_rpow he.le heε hγU.le)
  have hdγ : d ≤ ωL / 2 * e ^ γ :=
    calc d ≤ K * e ^ (2 * n) := hd
      _ = K * e ^ ((2 * n : ℝ) - γ) * e ^ γ := by rw [hpow, mul_assoc]
      _ ≤ K * ε ^ γU * e ^ γ := by gcongr
      _ ≤ ωL / 2 * e ^ γ := by gcongr
  have hlow : ωL * e ^ γ ≤ ω * (e + d) ^ γ :=
    mul_le_mul hω.1 (Real.rpow_le_rpow he.le (by linarith) hγ0) heγ hω0
  -- `d ≤ e`
  have hde : d ≤ e := by
    have h2 : e ^ (2 * n) ≤ e ^ 2 := pow_le_pow_of_le_one he.le he1 (by omega)
    calc d ≤ K * e ^ (2 * n) := hd
      _ ≤ K * e ^ 2 := by gcongr
      _ = K * e * e := by ring
      _ ≤ K * ε * e := by gcongr
      _ ≤ 1 * e := by gcongr
      _ = e := one_mul e
  have hup : ω * (e + d) ^ γ ≤ ωU * 2 ^ γ * e ^ γ := by
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) he.le]
    exact mul_le_mul hω.2 (Real.rpow_le_rpow (by linarith) (by linarith) hγ0)
      (Real.rpow_nonneg (by linarith) _) (hω0.trans hω.2)
  refine ⟨by linarith, by linarith, ?_⟩
  -- `ωU 2 ^ γ e ^ γ ≤ e / 2`
  have h2γ : (2 : ℝ) ^ γ ≤ 2 ^ (2 * N : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have : (n : ℝ) ≤ N := by exact_mod_cast hnN
      linarith [hγ.2])
  have heγ1 : e ^ (γ - 1) ≤ ε ^ (γL - 1) :=
    (Real.rpow_le_rpow_of_exponent_ge he he1 (by linarith [hγ.1])).trans
      (Real.rpow_le_rpow he.le heε (by linarith))
  have hsplit : e ^ γ = e ^ (γ - 1) * e := by
    rw [Real.rpow_sub_one he.ne', div_mul_cancel₀ _ he.ne']
  have hωU : 0 ≤ ωU := hω0.trans hω.2
  have : ωU * 2 ^ γ * e ^ γ ≤ 1 / 2 * e :=
    calc ωU * 2 ^ γ * e ^ γ = ωU * 2 ^ γ * e ^ (γ - 1) * e := by rw [hsplit]; ring
      _ ≤ ωU * 2 ^ (2 * N : ℝ) * ε ^ (γL - 1) * e := by gcongr
      _ ≤ 1 / 2 * e := by gcongr
  linarith

/-- The smallness conditions of `shiftUpdate_bounds` hold for all small `ε > 0`. -/
theorem exists_shiftUpdate_radius {K ωL ωU γL γU : ℝ} (hωL : 0 < ωL) (hγU : 0 < γU)
    (hγL : 1 < γL) (N : ℕ) :
    ∃ ε > 0, ε ≤ 1 ∧ K * ε ≤ 1 ∧ K * ε ^ γU ≤ ωL / 2 ∧
      ωU * 2 ^ (2 * N : ℝ) * ε ^ (γL - 1) ≤ 1 / 2 := by
  have hc : ∀ {p : ℝ}, 0 < p → ∀ c : ℝ, Tendsto (fun ε : ℝ => c * ε ^ p) (𝓝 0) (𝓝 0) :=
    fun hp c => by
      have := ((Real.continuousAt_rpow_const 0 _ (Or.inr hp.le)).tendsto).const_mul c
      simpa [Real.zero_rpow hp.ne'] using this
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 := eventually_lt_nhds one_pos
  have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), K * ε < 1 := by
    have : Tendsto (fun ε : ℝ => K * ε) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_const_mul K).tendsto 0
    exact (tendsto_order.1 this).2 _ one_pos
  have h3 := (tendsto_order.1 (hc hγU K)).2 _ (half_pos hωL)
  have h4 := (tendsto_order.1 (hc (sub_pos.2 hγL) (ωU * 2 ^ (2 * N : ℝ)))).2 _
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨ε, hε, ⟨h1, h2⟩, h3, h4⟩ :=
    ((eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)).and
      (nhdsWithin_le_nhds ((h1.and h2).and (h3.and h4)))).exists
  exact ⟨ε, hε, h1.le, h2.le, h3.le, h4.le⟩

/-- The tangent factor of one block: `((e)ⁿ / (e + μ)ⁿ)² ≤ e ^ (2 n) / μ ^ (2 N)` for
`0 < μ ≤ 1`, `n ≤ N`, and it is at most `1`. -/
theorem tangentFactor_le {e μ : ℝ} {n N : ℕ} (he : 0 < e) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hnN : n ≤ N) :
    (e ^ n / (e + μ) ^ n) ^ 2 ≤ e ^ (2 * n) / μ ^ (2 * N) ∧ (e ^ n / (e + μ) ^ n) ^ 2 ≤ 1 := by
  have hq : e ^ n / (e + μ) ^ n ≤ 1 :=
    (div_le_one (by positivity)).2 (pow_le_pow_left₀ he.le (by linarith) n)
  refine ⟨?_, pow_le_one₀ (by positivity) hq⟩
  calc (e ^ n / (e + μ) ^ n) ^ 2 ≤ (e ^ n / μ ^ n) ^ 2 := by
        gcongr
        linarith
    _ = e ^ (2 * n) / μ ^ (2 * n) := by rw [div_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
    _ ≤ e ^ (2 * n) / μ ^ (2 * N) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_of_le_one hμ.le hμ1 (by omega))

/-- **Theorem 9.3.1 (fast convergence in the hard case).** Let `z₀` have a nonzero component in
the leftmost eigenspace `E₁`, and let the constants satisfy `0 < ωL`, `0 < γU`, `1 < γL` and
`nU < ∞`. There is `ε > 0` such that every run of Algorithm 9.3.1 with `z 0 = z₀` and
`ℓ 0 < -λ₁ + ε` satisfies, with the errors `eₖ = ℓ k + λ₁`:
* `ℓ k > -λ₁` for all `k` (every `H + ℓ k` is positive definite), `ℓ` is antitone and `ℓ k → -λ₁`;
* `z k` approaches `E₁`: `‖(1 - P₁) z k‖ → 0`;
* `ωL/2 · eₖ ^ γₖ ≤ eₖ₊₁ ≤ ωU 2 ^ γₖ eₖ ^ γₖ` for every `k`;
* hence, if `γ k = γ̄` for all large `k`, the shifts converge with Q-order exactly `γ̄`: there are
  `0 < c ≤ C` with `c eₖ ^ γ̄ ≤ eₖ₊₁ ≤ C eₖ ^ γ̄` for all large `k`, and
  `ConvergesWithOrder ℓ (-λ₁) γ̄`.

The start condition is read in the inner product of `E` (the `M`-inner product of the book), and
`ε` depends on the bound `nU` for `n k`; see the module docstring and
`IsInverseIterationRun.convergence_of_eventually_const`. -/
theorem IsInverseIterationRun.convergence {ωL ωU γL γU : ℝ} {nU : ℕ∞} (hωL : 0 < ωL)
    (hγU : 0 < γU) (hγL : 1 < γL) (hnU : nU ≠ ⊤) {z₀ : E}
    (hz₀ : (leftmostSpace hH).starProjection z₀ ≠ 0) :
    ∃ ε > 0, ∀ (ℓ : ℕ → ℝ) (z : ℕ → E) (n : ℕ → ℕ) (ω γ : ℕ → ℝ),
      IsInverseIterationRun hH ωL ωU γL γU nU ℓ z n ω γ → z 0 = z₀ →
      ℓ 0 < -leftmost hH + ε →
      (∀ k, -leftmost hH < ℓ k) ∧ Antitone ℓ ∧ Tendsto ℓ atTop (𝓝 (-leftmost hH)) ∧
      Tendsto (fun k => ‖z k - (leftmostSpace hH).starProjection (z k)‖) atTop (𝓝 0) ∧
      (∀ k, ωL / 2 * (ℓ k + leftmost hH) ^ γ k ≤ ℓ (k + 1) + leftmost hH ∧
        ℓ (k + 1) + leftmost hH ≤ ωU * 2 ^ γ k * (ℓ k + leftmost hH) ^ γ k) ∧
      ∀ γbar : ℝ, (∀ᶠ k in atTop, γ k = γbar) →
        (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ k in atTop,
          c * (ℓ k + leftmost hH) ^ γbar ≤ ℓ (k + 1) + leftmost hH ∧
            ℓ (k + 1) + leftmost hH ≤ C * (ℓ k + leftmost hH) ^ γbar) ∧
        ConvergesWithOrder ℓ (-leftmost hH) γbar := by
  obtain ⟨N, rfl⟩ := ENat.ne_top_iff_exists.1 hnU
  obtain ⟨μ, hμ, hμ1, hgap⟩ := exists_spectralGap (hH := hH)
  rw [starProjection_leftmostSpace_ne_zero_iff] at hz₀
  set T₀ := restWeight hH z₀ / leftmostWeight hH z₀ with hT₀
  have hT₀0 : 0 ≤ T₀ := div_nonneg (restWeight_nonneg _) hz₀.le
  set Λ := max 0 (rightmost hH - leftmost hH) with hΛ
  set K := Λ * T₀ / μ ^ (2 * N) with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨ε, hε, hε1, hKε, hKεγ, hωε⟩ :=
    exists_shiftUpdate_radius (K := K) (ωU := ωU) hωL hγU hγL N
  refine ⟨ε, hε, fun ℓ z n ω γ hr hz0 hℓ0 => ?_⟩
  -- the error and the invariant
  set e : ℕ → ℝ := fun k => ℓ k + leftmost hH with he_def
  have hnN : ∀ k, n k ≤ N := fun k => by exact_mod_cast hr.count_le k
  let Inv : ℕ → Prop := fun k => ‖z k‖ = 1 ∧ 0 < leftmostWeight hH (z k) ∧
    restWeight hH (z k) / leftmostWeight hH (z k) ≤ T₀ ∧ 0 < e k ∧ e k ≤ ε * (1 / 2) ^ k
  have hstep : ∀ k, Inv k → Inv (k + 1) ∧
      (ωL / 2 * e k ^ γ k ≤ e (k + 1) ∧ e (k + 1) ≤ ωU * 2 ^ γ k * e k ^ γ k) ∧
      e (k + 1) ≤ e k ∧ restWeight hH (z (k + 1)) ≤ T₀ / μ ^ (2 * N) * e k ^ 2 := by
    rintro k ⟨-, hL, hT, he, hek⟩
    have hℓk : -leftmost hH < ℓ k := by simp only [he_def] at he; linarith
    obtain ⟨hz1, hL1, hT1⟩ := inverseIteration_block hμ hgap hℓk (n k) hL rfl
    rw [← hr.vector_succ] at hz1 hL1 hT1
    obtain ⟨hf, hf1⟩ := tangentFactor_le (n := n k) he hμ hμ1 (hnN k)
    have hT1' : restWeight hH (z (k + 1)) / leftmostWeight hH (z (k + 1)) ≤
        e k ^ (2 * n k) / μ ^ (2 * N) * T₀ :=
      hT1.trans (mul_le_mul hf hT (div_nonneg (restWeight_nonneg _) hL.le) (by positivity))
    have hRle : restWeight hH (z (k + 1)) ≤
        restWeight hH (z (k + 1)) / leftmostWeight hH (z (k + 1)) := by
      have := leftmostWeight_add_restWeight (hH := hH) (z (k + 1))
      rw [hz1] at this
      have h0 := restWeight_nonneg (hH := hH) (z (k + 1))
      exact le_div_self h0 hL1 (by linarith)
    -- the Rayleigh-quotient error
    set d := ⟪z (k + 1), H (z (k + 1))⟫ - leftmost hH with hd_def
    obtain ⟨hd0, hd1⟩ := rayleigh_sub_leftmost_le_restWeight (hH := hH) hz1
    have hdK : d ≤ K * e k ^ (2 * n k) :=
      calc d ≤ (rightmost hH - leftmost hH) * restWeight hH (z (k + 1)) := hd1
        _ ≤ Λ * (e k ^ (2 * n k) / μ ^ (2 * N) * T₀) :=
          mul_le_mul (le_max_right _ _) (hRle.trans hT1') (restWeight_nonneg _)
            (le_max_left _ _)
        _ = K * e k ^ (2 * n k) := by rw [hK]; ring
    have hrec : e (k + 1) = ω k * (e k + d) ^ γ k - d := by
      simp only [he_def, hd_def]
      rw [hr.shift_succ]
      ring_nf
    obtain ⟨hlo, hhi, hhalf⟩ := shiftUpdate_bounds hγU hγL hK0 hε1 hKε hKεγ hωε he
      (hek.trans (mul_le_of_le_one_right hε.le (pow_le_one₀ (by norm_num) (by norm_num))))
      hd0 hdK (hr.one_le_count k) (hnN k) (hr.weight_mem k) (hr.exponent_mem k)
    rw [← hrec] at hlo hhi hhalf
    have hpos : 0 < e (k + 1) :=
      lt_of_lt_of_le (mul_pos (half_pos hωL) (Real.rpow_pos_of_pos he _)) hlo
    have hTle : restWeight hH (z (k + 1)) / leftmostWeight hH (z (k + 1)) ≤ T₀ :=
      hT1.trans (by
        calc _ ≤ 1 * T₀ := mul_le_mul hf1 hT (div_nonneg (restWeight_nonneg _) hL.le) one_pos.le
          _ = T₀ := one_mul _)
    have he1 : e k ≤ 1 :=
      hek.trans ((mul_le_of_le_one_right hε.le (pow_le_one₀ (by norm_num) (by norm_num))).trans
        hε1)
    refine ⟨⟨hz1, hL1, hTle, hpos, ?_⟩, ⟨hlo, hhi⟩, by linarith, ?_⟩
    · rw [pow_succ]; linarith
    · calc restWeight hH (z (k + 1)) ≤ e k ^ (2 * n k) / μ ^ (2 * N) * T₀ := hRle.trans hT1'
        _ ≤ e k ^ 2 / μ ^ (2 * N) * T₀ :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
            (pow_le_pow_of_le_one he.le he1 (by linarith [hr.one_le_count k])) (by positivity))
            hT₀0
        _ = T₀ / μ ^ (2 * N) * e k ^ 2 := by ring
  have hinv : ∀ k, Inv k := by
    intro k
    induction k with
    | zero =>
      refine ⟨hr.norm_zero, hz0 ▸ hz₀, by rw [hz0], ?_, ?_⟩
      · simp only [he_def]; linarith [hr.shift_zero]
      · simp only [he_def, pow_zero, mul_one]; linarith
    | succ k ih => exact (hstep k ih).1
  have hpos : ∀ k, 0 < e k := fun k => (hinv k).2.2.2.1
  have hbd := fun k => (hstep k (hinv k)).2.1
  have he0 : Tendsto e atTop (𝓝 0) :=
    squeeze_zero (fun k => (hpos k).le) (fun k => (hinv k).2.2.2.2) (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul ε)
  have hℓlim : Tendsto ℓ atTop (𝓝 (-leftmost hH)) := by
    simpa [he_def] using he0.sub_const (leftmost hH)
  refine ⟨fun k => by have := hpos k; simp only [he_def] at this; linarith,
    antitone_nat_of_succ_le fun k => ?_, hℓlim, ?_, hbd, fun γbar hγ => ?_⟩
  · have := (hstep k (hinv k)).2.2.1
    simp only [he_def] at this
    linarith
  · have hR : Tendsto (fun k => restWeight hH (z (k + 1))) atTop (𝓝 0) :=
      squeeze_zero (fun k => restWeight_nonneg _) (fun k => (hstep k (hinv k)).2.2.2) (by
        simpa using (he0.pow 2).const_mul (T₀ / μ ^ (2 * N)))
    have hsq : Tendsto (fun k => ‖z k - (leftmostSpace hH).starProjection (z k)‖ ^ 2) atTop
        (𝓝 0) := by
      rw [← tendsto_add_atTop_iff_nat 1]
      simpa only [norm_sub_starProjection_leftmostSpace_sq] using hR
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at this
    exact this
  · obtain ⟨k₀, hk₀⟩ := hγ.exists
    have hγbar : 1 < γbar := hk₀ ▸ lt_of_lt_of_le hγL (hr.exponent_mem k₀).1
    have hωLU : ωL ≤ ωU := (hr.weight_mem 0).1.trans (hr.weight_mem 0).2
    have h2 : (1 : ℝ) ≤ 2 ^ γbar := Real.one_le_rpow (by norm_num) (by linarith)
    have hC : 0 < ωU * 2 ^ γbar := mul_pos (by linarith) (by linarith)
    have hev : ∀ᶠ k in atTop, ωL / 2 * e k ^ γbar ≤ e (k + 1) ∧
        e (k + 1) ≤ ωU * 2 ^ γbar * e k ^ γbar :=
      hγ.mono fun k hk => by rw [← hk]; exact hbd k
    refine ⟨⟨ωL / 2, ωU * 2 ^ γbar, half_pos hωL, ?_, hev⟩, hℓlim, ωU * 2 ^ γbar, hC,
      hev.mono fun k hk => ?_⟩
    · calc ωL / 2 ≤ ωU * 1 := by linarith
        _ ≤ ωU * 2 ^ γbar := mul_le_mul_of_nonneg_left h2 (by linarith)
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_neg_eq_add, sub_neg_eq_add,
        abs_of_pos (hpos (k + 1)), abs_of_pos (hpos k)]
      exact hk.2


/-- **Theorem 9.3.1 as stated in the book** (with `n_U = ∞` allowed). Fix the sequences `n k`,
`ω k`, `γ k`, with `n k` eventually constant. Then there is `ε > 0` such that every run of
Algorithm 9.3.1 with these sequences, `z 0 = z₀` and `ℓ 0 < -λ₁ + ε` satisfies the conclusions
of `IsInverseIterationRun.convergence` (in particular Q-order `γ̄` when `γ k = γ̄` eventually).
The `ε` depends on the sequences only through a bound for `n k`. -/
theorem IsInverseIterationRun.convergence_of_eventually_const {ωL ωU γL γU : ℝ} (hωL : 0 < ωL)
    (hγU : 0 < γU) (hγL : 1 < γL) {z₀ : E} (hz₀ : (leftmostSpace hH).starProjection z₀ ≠ 0)
    {n : ℕ → ℕ} {ω γ : ℕ → ℝ} {nbar : ℕ} (hn : ∀ᶠ k in atTop, n k = nbar) :
    ∃ ε > 0, ∀ (nU : ℕ∞) (ℓ : ℕ → ℝ) (z : ℕ → E),
      IsInverseIterationRun hH ωL ωU γL γU nU ℓ z n ω γ → z 0 = z₀ →
      ℓ 0 < -leftmost hH + ε →
      (∀ k, -leftmost hH < ℓ k) ∧ Antitone ℓ ∧ Tendsto ℓ atTop (𝓝 (-leftmost hH)) ∧
      Tendsto (fun k => ‖z k - (leftmostSpace hH).starProjection (z k)‖) atTop (𝓝 0) ∧
      (∀ k, ωL / 2 * (ℓ k + leftmost hH) ^ γ k ≤ ℓ (k + 1) + leftmost hH ∧
        ℓ (k + 1) + leftmost hH ≤ ωU * 2 ^ γ k * (ℓ k + leftmost hH) ^ γ k) ∧
      ∀ γbar : ℝ, (∀ᶠ k in atTop, γ k = γbar) →
        (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ k in atTop,
          c * (ℓ k + leftmost hH) ^ γbar ≤ ℓ (k + 1) + leftmost hH ∧
            ℓ (k + 1) + leftmost hH ≤ C * (ℓ k + leftmost hH) ^ γbar) ∧
        ConvergesWithOrder ℓ (-leftmost hH) γbar  := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hn
  have hN : ∀ k, n k ≤ max nbar ((Finset.range K).sup n) := fun k => by
    by_cases hk : k < K
    · exact le_max_of_le_right (Finset.le_sup (Finset.mem_range.2 hk))
    · rw [hK k (not_lt.1 hk)]
      exact le_max_left _ _
  obtain ⟨ε, hε, hconv⟩ := IsInverseIterationRun.convergence (hH := hH) (ωU := ωU)
    (nU := (max nbar ((Finset.range K).sup n) : ℕ)) hωL hγU hγL (ENat.natCast_ne_top _) hz₀
  exact ⟨ε, hε, fun _ ℓ z hr hz0 hℓ0 =>
    hconv ℓ z n ω γ { hr with count_le := fun k => by exact_mod_cast hN k } hz0 hℓ0⟩

/-- **Normalizing after every step of a linear iteration is normalizing at the end**: if
`wᵢ₊₁ = normalize (R wᵢ)` and `w₀ = z` then `wᵢ₊₁ = normalize (Rⁱ⁺¹ z)` (the inner loop of
Algorithm 9.3.1 of [cartis2022evaluation]). -/
theorem normalize_iterate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (R : F →L[ℝ] F)
    {w : ℕ → F} {z : F} (h0 : w 0 = z) (hs : ∀ i, w (i + 1) = NormedSpace.normalize (R (w i)))
    (i : ℕ) : w (i + 1) = NormedSpace.normalize ((R ^ (i + 1)) z) := by
  induction i with
  | zero => rw [hs, h0, zero_add, pow_one]
  | succ i ih =>
    have hRR : (R * R ^ (i + 1)) z = R ((R ^ (i + 1)) z) := rfl
    have hRn : R (NormedSpace.normalize ((R ^ (i + 1)) z)) =
        ‖(R ^ (i + 1)) z‖⁻¹ • R ((R ^ (i + 1)) z) := by
      rw [NormedSpace.normalize, map_smul]
    rw [hs, ih, pow_succ' R (i + 1), hRR, hRn]
    rcases eq_or_ne ((R ^ (i + 1)) z) 0 with hv | hv
    · simp [hv]
    · exact NormedSpace.normalize_smul_of_pos (inv_pos.2 (norm_pos_iff.2 hv)) _

end Subproblem

