import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.Banach
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Optimization.Subproblem.SecularSum

/-!
# The resolvent step and the secular function

Let `H : E →L[ℝ] E` be a symmetric operator on a finite-dimensional real inner product space,
`g : E`, and `λ` a real shift. This file studies the step `s(λ) = -(H + λ)⁻¹ g` solving
`(H + λ) s = -g` (Cartis–Gould–Toint, *Evaluation complexity of algorithms for nonconvex
optimization*, (8.2.2)) and the secular function `π(λ) = ‖s(λ)‖²` ((8.2.4)), on the interval
`λ > -λ₁` to the right of the leftmost eigenvalue `λ₁` of `H`, where `H + λ` is positive definite.

A scaling norm `‖·‖_M` of the book is not a parameter: it is the norm of the inner product space
`E` (an energy space, in which the pencil `(H, M)` becomes the single symmetric operator `M⁻¹ H`).

## Main definitions

* `leftmost hH`, `rightmost hH`: the least and greatest eigenvalues `λ₁`, `λₙ` of `H` (`0` on the
  zero space), and
  `shiftThreshold hH = max 0 (-λ₁)`, the book's `λₛ`.
* `step g H λ = -(Ring.inverse (H + λ • 1)) g` and `secular g H λ = ‖step g H λ‖ ^ 2`.
* `particular hH g λ`: the minimum-norm solution of `(H + λ) x = -g` when one exists (the book's
  `sₛ` at `λ = -λ₁`), spectrally `-(H + λ)⁺ g`. "Minimum norm" refers to the norm of `E`: in the
  scaled setting of the book, where `E` carries the energy inner product `⟪x, y⟫_M`, it is the
  `M`-minimum-norm solution — the limit of `s(λ)` as `λ ↓ -λ₁` — and *not* the Euclidean
  Moore–Penrose solution (the two differ by a kernel vector).
* `stepDeriv g H k λ = (-1) ^ (k + 1) k! (H + λ)⁻⁽ᵏ⁺¹⁾ g`, the `k`-th derivative of `step`, and
  `secularCoeff k = (2 k + 1)! / (k!)²`, the book's `αₖ`.

## Main results

* `isPositive_add_smul_iff`, `isSymmetricCoercive_add_smul_iff`: `H + λ` is positive
  semidefinite iff `λ ≥ -λ₁` and positive definite iff `λ > -λ₁`;
  `isPositive_add_smul_of_le` and `shiftThreshold_le_of_isPositive` need no nontriviality.
* `le_leftmost_iff`, `le_leftmost_iff_forall`, `le_leftmost_iff_isCoerciveWith`: `λ₁` is the
  greatest lower bound of the eigenvalues and the best constant in `c ‖v‖² ≤ ⟪v, H v⟫`;
  `inner_le_rightmost_mul_norm_sq`, `rightmost_le_of_forall` are the same for `λₙ`, and
  `norm_add_smul_apply_le` bounds `‖(H + λ) v‖ ≤ (λ + λₙ) ‖v‖` for `λ ≥ -λ₁`.
* `step_spec`, `step_eq_sum`, `secular_eq_secularSum`: on `λ > -λ₁`, `step` is the unique
  solution of `(H + λ) s = -g`, with the spectral expansions (8.2.6)–(8.2.7) in an orthonormal
  eigenbasis `bᵢ`: `s(λ) = -∑ ⟪bᵢ, g⟫ / (λ + λᵢ) bᵢ` and `π(λ) = ∑ ⟪bᵢ, g⟫² / (λ + λᵢ)²`. All
  real-variable properties of `π` then come from `Numlib.Optimization.Subproblem.SecularSum`.
* `secular_shape`: shape of `π` and of `π ^ β` on `λ > -λ₁` (Corollary 8.2.4).
* `hasDerivAt_secular`, `secular_pos`, `deriv_secular_neg`, `hasDerivAt_secular_rpow`,
  `contDiffOn_secular_rpow`: calculus facts about `π` and `π ^ β` on `λ > -λ₁` for `g ≠ 0`.
* `particular_spec`, `tendsto_step_threshold`: the minimum-norm solution, and the behaviour of
  `s(λ)` and `π(λ)` as `λ ↓ -λ₁` (finite limit `sₛ` iff `g ⊥ ker (H - λ₁)`, otherwise `π → ∞`).
  `tendsto_secular_rpow_threshold` is the corresponding statement for `π ^ β`.
* `iteratedDeriv_step`, `stepDeriv_succ_unique`, `iteratedDeriv_secular`: the derivatives of `s`
  and `π`, computed by the solves `(H + λ) s⁽ᵏ⁺¹⁾ = -(k + 1) s⁽ᵏ⁾` (Theorem 8.2.6).
* `secular_taylor_bounds`, `secular_rpow_deriv_sign`, `secular_rpow_strictConcaveOn`,
  `secular_rpow_tangent`: Theorem 8.2.2, Lemma 8.2.3 and Theorem 8.2.5 for `π`
  (`secular_rpow_zero_left` is the degenerate case `g = 0`, where `π ≡ 0`).

## Implementation notes

Everything is computed in the orthonormal eigenvector basis `bᵢ = hH.eigenvectorBasis rfl i` with
eigenvalues `λᵢ = hH.eigenvalues rfl i`: two vectors are equal when their coordinates are
(`eq_of_inner_eigenvectorBasis`), and `⟪bᵢ, (H + λ) v⟫ = (λ + λᵢ) ⟪bᵢ, v⟫`. Mathlib sorts the
eigenvalues decreasingly; `leftmost` is defined as their infimum, which is `0` on the zero space
(hence the `[Nontrivial E]` hypotheses of the characterizations).

## Strictness and domain

The strict inequalities of Lemma 8.2.3 and Theorem 8.2.5 fail for `β = -1/2` when `g` is an
eigenvector of `H` (then `π(λ) ^ (-1/2)` is affine); Theorem 8.2.5 also needs `δ ≠ 0` for
strictness. The results are stated on the interval `λ > -λ₁`, which contains `λ > λₛ`.
-/

open Set Filter Topology
open Finset (range)
open scoped Nat RealInnerProductSpace

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : E →L[ℝ] E}

/-! ### The leftmost eigenvalue -/

section Leftmost

variable (hH : (H : E →ₗ[ℝ] E).IsSymmetric)

/-- The leftmost (least) eigenvalue `λ₁` of the symmetric operator `H`; `0` if `E` is the zero
space. -/
noncomputable def leftmost : ℝ := ⨅ i, hH.eigenvalues rfl i

/-- The book's `λₛ = max 0 (-λ₁)` (Lemma 8.2.1): the left end of the interval of shifts `λ ≥ 0`
on which `H + λ` is positive definite. -/
noncomputable def shiftThreshold : ℝ := max 0 (-leftmost hH)

/-- The rightmost (greatest) eigenvalue `λₙ` of the symmetric operator `H`; `0` if `E` is the
zero space. -/
noncomputable def rightmost : ℝ := ⨆ i, hH.eigenvalues rfl i

theorem rightmost_def : rightmost hH = ⨆ i, hH.eigenvalues rfl i := rfl

variable {hH}

theorem eigenvalues_le_rightmost (i : Fin (Module.finrank ℝ E)) :
    hH.eigenvalues rfl i ≤ rightmost hH :=
  le_ciSup (Set.finite_range _).bddAbove i

theorem leftmost_le_eigenvalues (i : Fin (Module.finrank ℝ E)) :
    leftmost hH ≤ hH.eigenvalues rfl i :=
  ciInf_le (Set.finite_range _).bddBelow i

theorem leftmost_le_rightmost : leftmost hH ≤ rightmost hH := by
  rcases isEmpty_or_nonempty (Fin (Module.finrank ℝ E)) with h | ⟨⟨i⟩⟩
  · simp [leftmost, rightmost]
  · exact (leftmost_le_eigenvalues i).trans (eigenvalues_le_rightmost i)

theorem exists_eigenvalues_eq_leftmost [Nontrivial E] :
    ∃ i, hH.eigenvalues rfl i = leftmost hH := by
  have : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  exact exists_eq_ciInf_of_finite

theorem shiftThreshold_nonneg : 0 ≤ shiftThreshold hH := le_max_left _ _

theorem neg_leftmost_le_shiftThreshold : -leftmost hH ≤ shiftThreshold hH := le_max_right _ _

theorem Ioi_shiftThreshold_subset : Ioi (shiftThreshold hH) ⊆ Ioi (-leftmost hH) :=
  Ioi_subset_Ioi neg_leftmost_le_shiftThreshold

/-- The action of `H` on its eigenvector basis, with real scalars. -/
theorem apply_eigenvectorBasis' (i : Fin (Module.finrank ℝ E)) :
    H (hH.eigenvectorBasis rfl i) = hH.eigenvalues rfl i • hH.eigenvectorBasis rfl i := by
  have h := hH.apply_eigenvectorBasis rfl i
  simp only [ContinuousLinearMap.coe_coe, RCLike.ofReal_real_eq_id, id] at h
  exact h

/-- Coordinates of `(H + λ) v` in the eigenvector basis: `⟪bᵢ, (H + λ) v⟫ = (λ + λᵢ) ⟪bᵢ, v⟫`. -/
theorem inner_eigenvectorBasis_add_smul (lam : ℝ) (v : E) (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, (H + lam • 1) v⟫ =
      (lam + hH.eigenvalues rfl i) * ⟪hH.eigenvectorBasis rfl i, v⟫ := by
  have hsymm : ⟪hH.eigenvectorBasis rfl i, H v⟫ = ⟪H (hH.eigenvectorBasis rfl i), v⟫ :=
    (hH _ _).symm
  simp only [add_apply, smul_apply,
    one_apply_eq_self, inner_add_right, inner_smul_right]
  rw [show ⟪hH.eigenvectorBasis rfl i, H v⟫ = _ from hsymm, apply_eigenvectorBasis',
    real_inner_smul_left]
  ring

/-- The inner product in the coordinates of the eigenvector basis. -/
theorem inner_eq_sum_eigenvectorBasis (x y : E) :
    ⟪x, y⟫ = ∑ i, ⟪hH.eigenvectorBasis rfl i, x⟫ * ⟪hH.eigenvectorBasis rfl i, y⟫ := by
  rw [← (hH.eigenvectorBasis rfl).sum_inner_mul_inner x y]
  exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm x]

/-- Two vectors with the same coordinates in the eigenvector basis are equal. -/
theorem eq_of_inner_eigenvectorBasis {x y : E}
    (h : ∀ i, ⟪hH.eigenvectorBasis rfl i, x⟫ = ⟪hH.eigenvectorBasis rfl i, y⟫) : x = y := by
  rw [← (hH.eigenvectorBasis rfl).sum_repr' x, ← (hH.eigenvectorBasis rfl).sum_repr' y]
  simp_rw [h]

/-- The coordinates of a combination of the eigenvectors. -/
theorem inner_eigenvectorBasis_sum (c : Fin (Module.finrank ℝ E) → ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, ∑ j, c j • hH.eigenvectorBasis rfl j⟫ = c i :=
  (hH.eigenvectorBasis rfl).orthonormal.inner_right_fintype c i

/-- The Rayleigh lower bound `λ₁ ‖v‖² ≤ ⟪v, H v⟫`, written for the shift `H + λ`:
`(λ + λ₁) ‖v‖² ≤ ⟪(H + λ) v, v⟫`. -/
theorem add_leftmost_mul_norm_sq_le (lam : ℝ) (v : E) :
    (lam + leftmost hH) * ‖v‖ ^ 2 ≤ ⟪(H + lam • 1) v, v⟫ := by
  rw [← real_inner_self_eq_norm_sq, real_inner_comm, inner_eq_sum_eigenvectorBasis (hH := hH),
    inner_eq_sum_eigenvectorBasis (hH := hH), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [inner_eigenvectorBasis_add_smul]
  have := leftmost_le_eigenvalues (hH := hH) i
  nlinarith [mul_self_nonneg ⟪hH.eigenvectorBasis rfl i, v⟫]

theorem leftmost_mul_norm_sq_le (v : E) : leftmost hH * ‖v‖ ^ 2 ≤ ⟪v, H v⟫ := by
  simpa [real_inner_comm, inner_add_left, real_inner_self_eq_norm_sq] using
    add_leftmost_mul_norm_sq_le (hH := hH) 0 v

/-- `leftmost` is characterized as the greatest lower bound of the eigenvalues. -/
theorem le_leftmost_iff [Nontrivial E] {c : ℝ} :
    c ≤ leftmost hH ↔ ∀ i, c ≤ hH.eigenvalues rfl i := by
  have : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  exact le_ciInf_iff (Set.finite_range _).bddBelow

/-- `leftmost` is the best constant in the Rayleigh bound `c ‖v‖² ≤ ⟪v, H v⟫` (Courant–Fischer
for the least eigenvalue). -/
theorem le_leftmost_iff_forall [Nontrivial E] {c : ℝ} :
    c ≤ leftmost hH ↔ ∀ v, c * ‖v‖ ^ 2 ≤ ⟪v, H v⟫ := by
  constructor
  · intro hc v
    exact le_trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) (leftmost_mul_norm_sq_le v)
  · intro h
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hH)
    have h' := h (hH.eigenvectorBasis rfl i)
    rw [apply_eigenvectorBasis', real_inner_smul_right, real_inner_self_eq_norm_sq,
      (hH.eigenvectorBasis rfl).norm_eq_one, hi] at h'
    simpa using h'

/-- The same characterization in the language of `LinearMap.IsCoerciveWith`: `H` is coercive
with constant `c` iff `c ≤ λ₁`. -/
theorem le_leftmost_iff_isCoerciveWith [Nontrivial E] {c : ℝ} :
    c ≤ leftmost hH ↔ (H : E →ₗ[ℝ] E).IsCoerciveWith c := by
  rw [le_leftmost_iff_forall]
  refine forall_congr' fun v => ?_
  simp [real_inner_comm]

/-- The leftmost eigenvalue is an eigenvalue (on a nonzero space). -/
theorem hasEigenvalue_leftmost [Nontrivial E] :
    Module.End.HasEigenvalue (H : E →ₗ[ℝ] E) (leftmost hH) := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hH)
  simpa [hi] using hH.hasEigenvalue_eigenvalues rfl i

/-- `H + λ` is positive semidefinite iff `λ ≥ -λ₁` (on a nonzero space). -/
theorem isPositive_add_smul_iff [Nontrivial E] (lam : ℝ) :
    ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive ↔ -leftmost hH ≤ lam := by
  rw [ContinuousLinearMap.isPositive_add_smul_one_iff hH]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hH)
    have h' := h (hH.eigenvectorBasis rfl i)
    rw [inner_eigenvectorBasis_add_smul, real_inner_self_eq_norm_sq,
      (hH.eigenvectorBasis rfl).norm_eq_one, hi] at h'
    linarith
  · intro hlam v
    rw [real_inner_comm]
    exact le_trans (mul_nonneg (by linarith) (sq_nonneg _))
      (add_leftmost_mul_norm_sq_le (hH := hH) lam v)

/-- On the zero space the leftmost eigenvalue is `0` (an empty infimum). -/
theorem leftmost_eq_zero_of_subsingleton [Subsingleton E] : leftmost hH = 0 := by
  have : IsEmpty (Fin (Module.finrank ℝ E)) := by
    rw [Module.finrank_zero_of_subsingleton]; infer_instance
  exact Real.iInf_of_isEmpty _

/-- `H + λ` is positive semidefinite for `λ ≥ -λ₁` (no nontriviality needed). -/
theorem isPositive_add_smul_of_le {lam : ℝ} (hlam : -leftmost hH ≤ lam) :
    ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [ContinuousLinearMap.isPositive_add_smul_one_iff hH]
    intro v; simp [Subsingleton.elim v 0]
  · exact (isPositive_add_smul_iff (hH := hH) lam).2 hlam

/-- A nonnegative shift making `H + μ` positive semidefinite is at least `λₛ`. -/
theorem shiftThreshold_le_of_isPositive {μ : ℝ} (hμ : 0 ≤ μ)
    (hpos : ((H + μ • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E).IsPositive) : shiftThreshold hH ≤ μ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [shiftThreshold, leftmost_eq_zero_of_subsingleton]; simpa using hμ
  · exact max_le hμ ((isPositive_add_smul_iff (hH := hH) μ).1 hpos)

/-- `H + λ` is positive definite (symmetric and coercive) iff `λ > -λ₁` (on a nonzero space). -/
theorem isSymmetricCoercive_add_smul_iff [Nontrivial E] (lam : ℝ) :
    ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetricCoercive ↔ -leftmost hH < lam := by
  constructor
  · intro hc
    obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hH)
    have h := hc.isCoercive.inner_self_pos ((hH.eigenvectorBasis rfl).orthonormal.ne_zero i)
    simp only [RCLike.re_to_real, ContinuousLinearMap.coe_coe] at h
    rw [real_inner_comm, inner_eigenvectorBasis_add_smul, real_inner_self_eq_norm_sq,
      (hH.eigenvectorBasis rfl).norm_eq_one, hi] at h
    linarith
  · intro hlam
    refine ⟨ContinuousLinearMap.isSymmetric_add_smul_one hH lam, ?_⟩
    refine (LinearMap.isCoercive_iff_forall_pos _).2 fun x hx => ?_
    simp only [RCLike.re_to_real, ContinuousLinearMap.coe_coe]
    exact lt_of_lt_of_le (mul_pos (by linarith) (by positivity))
      (add_leftmost_mul_norm_sq_le (hH := hH) lam x)

/-- At the threshold `λ = -λ₁`, `H + λ` is singular (on a nonzero space). -/
theorem ker_add_neg_leftmost_ne_bot [Nontrivial E] :
    LinearMap.ker ((H + (-leftmost hH) • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E) ≠ ⊥ := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_leftmost (hH := hH)
  rw [Submodule.ne_bot_iff]
  refine ⟨hH.eigenvectorBasis rfl i, ?_, (hH.eigenvectorBasis rfl).orthonormal.ne_zero i⟩
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, add_apply, apply_eigenvectorBasis', hi]
  simp

/-- For `λ > -λ₁`, `H + λ` is invertible. -/
theorem isUnit_add_smul {lam : ℝ} (hlam : -leftmost hH < lam) : IsUnit (H + lam • 1) := by
  have := FiniteDimensional.complete ℝ E
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot']
  intro v hv
  refine eq_of_inner_eigenvectorBasis (hH := hH) fun i => ?_
  have h := inner_eigenvectorBasis_add_smul (hH := hH) lam v i
  rw [ContinuousLinearMap.coe_coe] at hv
  rw [hv, inner_zero_right] at h
  have hpos : 0 < lam + hH.eigenvalues rfl i := by
    have := leftmost_le_eigenvalues (hH := hH) i; linarith
  rw [inner_zero_right]
  exact (mul_eq_zero.1 h.symm).resolve_left hpos.ne'

/-- The Rayleigh upper bound `⟪(H + λ) v, v⟫ ≤ (λ + λₙ) ‖v‖²`, `λₙ` the rightmost eigenvalue. -/
theorem inner_add_smul_le_add_rightmost (lam : ℝ) (v : E) :
    ⟪(H + lam • 1) v, v⟫ ≤ (lam + rightmost hH) * ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, real_inner_comm, inner_eq_sum_eigenvectorBasis (hH := hH),
    inner_eq_sum_eigenvectorBasis (hH := hH), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [inner_eigenvectorBasis_add_smul]
  have := eigenvalues_le_rightmost (hH := hH) i
  nlinarith [mul_self_nonneg ⟪hH.eigenvectorBasis rfl i, v⟫]

/-- The Rayleigh upper bound `⟪v, H v⟫ ≤ λₙ ‖v‖²`. -/
theorem inner_le_rightmost_mul_norm_sq (v : E) : ⟪v, H v⟫ ≤ rightmost hH * ‖v‖ ^ 2 := by
  simpa [real_inner_comm, inner_add_left, real_inner_self_eq_norm_sq] using
    inner_add_smul_le_add_rightmost (hH := hH) 0 v

/-- The rightmost eigenvalue is an eigenvalue (on a nonzero space). -/
theorem exists_eigenvalues_eq_rightmost [Nontrivial E] :
    ∃ i, hH.eigenvalues rfl i = rightmost hH := by
  have : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
  exact exists_eq_ciSup_of_finite

/-- `λₙ` is the least constant in the Rayleigh bound `⟪v, H v⟫ ≤ c ‖v‖²` (on a nonzero space). -/
theorem rightmost_le_of_forall [Nontrivial E] {c : ℝ} (h : ∀ v, ⟪v, H v⟫ ≤ c * ‖v‖ ^ 2) :
    rightmost hH ≤ c := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_rightmost (hH := hH)
  have h' := h (hH.eigenvectorBasis rfl i)
  rw [apply_eigenvectorBasis', real_inner_smul_right, real_inner_self_eq_norm_sq,
    (hH.eigenvectorBasis rfl).norm_eq_one, hi] at h'
  simpa using h'

/-- **Norm bound for a positive semidefinite shift**: for `λ ≥ -λ₁`,
`‖(H + λ) v‖ ≤ (λ + λₙ) ‖v‖`. -/
theorem norm_add_smul_apply_le {lam : ℝ} (hlam : -leftmost hH ≤ lam) (v : E) :
    ‖(H + lam • 1) v‖ ≤ (lam + rightmost hH) * ‖v‖ := by
  have hsq : ‖(H + lam • 1) v‖ ^ 2 ≤ ((lam + rightmost hH) * ‖v‖) ^ 2 := by
    rw [mul_pow, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      inner_eq_sum_eigenvectorBasis (hH := hH), inner_eq_sum_eigenvectorBasis (hH := hH) v v,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [inner_eigenvectorBasis_add_smul]
    have h1 := leftmost_le_eigenvalues (hH := hH) i
    have h2 := eigenvalues_le_rightmost (hH := hH) i
    have h3 : 0 ≤ lam + hH.eigenvalues rfl i := by linarith
    have h4 : (lam + hH.eigenvalues rfl i) ^ 2 ≤ (lam + rightmost hH) ^ 2 :=
      pow_le_pow_left₀ h3 (by linarith) 2
    nlinarith [mul_self_nonneg ⟪hH.eigenvectorBasis rfl i, v⟫]
  have h0 : 0 ≤ lam + rightmost hH := by linarith [leftmost_le_rightmost (hH := hH)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **Rayleigh-quotient bounds for a shifted operator** (the generalized Rayleigh-quotient
inequality as used in [cartis2022evaluation] (9.3.1)): for `μ ≥ -λ₁`,
`(μ + λ₁) ‖s‖ ≤ ‖(H + μ) s‖ ≤ (μ + λₙ) ‖s‖`, with `λ₁ = leftmost`, `λₙ = rightmost`. -/
theorem norm_add_smul_apply_bounds {μ : ℝ} (hμ : -leftmost hH ≤ μ) (s : E) :
    (μ + leftmost hH) * ‖s‖ ≤ ‖(H + μ • 1) s‖ ∧ ‖(H + μ • 1) s‖ ≤ (μ + rightmost hH) * ‖s‖ := by
  have hsq' : ∀ x : E, ‖x‖ ^ 2 = ∑ i, ⟪hH.eigenvectorBasis rfl i, x⟫ ^ 2 := fun x => by
    rw [← real_inner_self_eq_norm_sq, inner_eq_sum_eigenvectorBasis (hH := hH)]
    exact Finset.sum_congr rfl fun i _ => (sq _).symm
  have hsq : ‖(H + μ • 1) s‖ ^ 2 =
      ∑ i, (μ + hH.eigenvalues rfl i) ^ 2 * ⟪hH.eigenvectorBasis rfl i, s⟫ ^ 2 := by
    rw [hsq']
    exact Finset.sum_congr rfl fun i _ => by rw [inner_eigenvectorBasis_add_smul, mul_pow]
  have hs := hsq' s
  have h1 : 0 ≤ μ + leftmost hH := by linarith
  have hl : ∀ i, μ + leftmost hH ≤ μ + hH.eigenvalues rfl i := fun i => by
    linarith [leftmost_le_eigenvalues (hH := hH) i]
  have hr : ∀ i, μ + hH.eigenvalues rfl i ≤ μ + rightmost hH := fun i => by
    linarith [eigenvalues_le_rightmost (hH := hH) i]
  have hr0 : 0 ≤ μ + rightmost hH := by linarith [leftmost_le_rightmost (hH := hH)]
  constructor
  · refine (pow_le_pow_iff_left₀ (mul_nonneg h1 (norm_nonneg _)) (norm_nonneg _)
      two_ne_zero).1 ?_
    rw [hsq, mul_pow, hs, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h1 (hl i) 2) (sq_nonneg _)
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hr0 (norm_nonneg _))
      two_ne_zero).1 ?_
    rw [hsq, mul_pow, hs, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (h1.trans (hl i)) (hr i) 2) (sq_nonneg _)

end Leftmost

/-! ### The step and the secular function -/

/-- The step `s(λ) = -(H + λ)⁻¹ g` (book (8.2.2)), defined with `Ring.inverse` so that it is total;
it solves `(H + λ) s = -g` whenever `H + λ` is invertible (`step_spec`). -/
noncomputable def step (g : E) (H : E →L[ℝ] E) (lam : ℝ) : E := -(Ring.inverse (H + lam • 1)) g

/-- The secular function `π(λ) = ‖s(λ)‖²` (book (8.2.4)). The transformed secular function
`π(λ; β)` of (8.2.17) is `secular g H λ ^ β` (`Real.rpow`). -/
noncomputable def secular (g : E) (H : E →L[ℝ] E) (lam : ℝ) : ℝ := ‖step g H lam‖ ^ 2

variable {g : E} (hH : (H : E →ₗ[ℝ] E).IsSymmetric)

/-- The spectral weights `⟪bᵢ, g⟫²` of `g` in the eigenvector basis of `H`; in the book's
notation (8.2.7), `γᵢ²`. -/
noncomputable def secularWeight (g : E) (i : Fin (Module.finrank ℝ E)) : ℝ :=
  ⟪hH.eigenvectorBasis rfl i, g⟫ ^ 2

variable {hH}

theorem secularWeight_nonneg : 0 ≤ secularWeight hH g := fun _ => sq_nonneg _

/-- The spectral weights sum to `‖g‖²`. -/
theorem sum_secularWeight : ∑ i, secularWeight hH g i = ‖g‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum_eigenvectorBasis (hH := hH)]
  simp [secularWeight, sq]

/-- Some spectral weight is nonzero iff `g ≠ 0`. -/
theorem secularWeight_ne_zero_iff : secularWeight hH g ≠ 0 ↔ g ≠ 0 := by
  constructor
  · rintro hw rfl
    exact hw (funext fun i => by simp [secularWeight])
  · intro hg hw
    have := sum_secularWeight (hH := hH) (g := g)
    rw [hw] at this
    simp only [Pi.zero_apply, Finset.sum_const_zero] at this
    exact hg (by simpa using this.symm)

/-- `g` is an eigenvector-or-zero of `H` (lies in a single eigenspace) iff its nonzero spectral
weights sit at a single eigenvalue. -/
theorem singlePole_secularWeight_iff (hg : g ≠ 0) :
    SinglePole (hH.eigenvalues rfl) (secularWeight hH g) ↔ ∃ c : ℝ, H g = c • g := by
  have hcoord : ∀ i, ⟪hH.eigenvectorBasis rfl i, H g⟫ =
      hH.eigenvalues rfl i * ⟪hH.eigenvectorBasis rfl i, g⟫ := fun i => by
    have := inner_eigenvectorBasis_add_smul (hH := hH) 0 g i
    simpa using this
  have hw : ∀ i, secularWeight hH g i ≠ 0 ↔ ⟪hH.eigenvectorBasis rfl i, g⟫ ≠ 0 := fun i => by
    simp [secularWeight]
  constructor
  · intro hs
    obtain ⟨i₀, hi₀⟩ : ∃ i, ⟪hH.eigenvectorBasis rfl i, g⟫ ≠ 0 := by
      by_contra h
      push Not at h
      exact hg (eq_of_inner_eigenvectorBasis (hH := hH) fun i => by simp [h i])
    refine ⟨hH.eigenvalues rfl i₀, eq_of_inner_eigenvectorBasis (hH := hH) fun i => ?_⟩
    rw [hcoord, real_inner_smul_right]
    by_cases hi : ⟪hH.eigenvectorBasis rfl i, g⟫ = 0
    · simp [hi]
    · rw [hs i i₀ ((hw i).2 hi) ((hw i₀).2 hi₀)]
  · rintro ⟨c, hc⟩ i j hi hj
    have key : ∀ k, ⟪hH.eigenvectorBasis rfl k, g⟫ ≠ 0 → hH.eigenvalues rfl k = c := by
      intro k hk
      have := hcoord k
      rw [hc, real_inner_smul_right] at this
      exact (mul_right_cancel₀ hk this).symm
    rw [key i ((hw i).1 hi), key j ((hw j).1 hj)]

/-- The shifts `λ > -λ₁` lie to the right of every pole `-λᵢ`. -/
theorem mem_secularDomain_of_lt {lam : ℝ} (hlam : -leftmost hH < lam) :
    lam ∈ secularDomain (hH.eigenvalues rfl) := fun i => by
  have := leftmost_le_eigenvalues (hH := hH) i
  linarith

theorem Ioi_subset_secularDomain :
    Ioi (-leftmost hH) ⊆ secularDomain (hH.eigenvalues rfl) := fun _ h =>
  mem_secularDomain_of_lt h

/-- For `λ > -λ₁`, `Ring.inverse (H + λ)` is a right inverse of `H + λ`. -/
theorem add_smul_inverse_apply {lam : ℝ} (hlam : -leftmost hH < lam) (x : E) :
    (H + lam • 1) (Ring.inverse (H + lam • 1) x) = x :=
  congrArg (fun T : E →L[ℝ] E => T x) (Ring.mul_inverse_cancel _ (isUnit_add_smul hlam))

/-- For `λ > -λ₁`, `H + λ` is injective. -/
theorem injective_add_smul {lam : ℝ} (hlam : -leftmost hH < lam) :
    Function.Injective ⇑(H + lam • 1 : E →L[ℝ] E) :=
  Function.LeftInverse.injective fun x =>
    congrArg (fun T : E →L[ℝ] E => T x) (Ring.inverse_mul_cancel _ (isUnit_add_smul hlam))

/-- **The step solves the shifted system** (book (8.2.2)): for `λ > -λ₁`,
`(H + λ) (step g H λ) = -g`, and `step g H λ` is the only solution. -/
theorem step_spec {lam : ℝ} (hlam : -leftmost hH < lam) :
    (H + lam • 1) (step g H lam) = -g ∧
      ∀ s, (H + lam • 1) s = -g → s = step g H lam := by
  have heq : (H + lam • 1) (step g H lam) = -g := by
    rw [step, map_neg, add_smul_inverse_apply hlam]
  refine ⟨heq, fun s hs => ?_⟩
  have hinj := injective_add_smul (hH := hH) hlam
  exact hinj (hs.trans heq.symm)

/-- The coordinates of a vector `y` with `(H + λ) y = v`: `⟪bᵢ, y⟫ = ⟪bᵢ, v⟫ / (λ + λᵢ)`. -/
theorem inner_eigenvectorBasis_eq_div {lam : ℝ} (hlam : -leftmost hH < lam) {y v : E}
    (hy : (H + lam • 1) y = v) (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, y⟫ =
      ⟪hH.eigenvectorBasis rfl i, v⟫ / (lam + hH.eigenvalues rfl i) := by
  have hpos : 0 < lam + hH.eigenvalues rfl i := by
    have := leftmost_le_eigenvalues (hH := hH) i; linarith
  rw [← hy, inner_eigenvectorBasis_add_smul, mul_div_cancel_left₀ _ hpos.ne']

theorem inner_eigenvectorBasis_step {lam : ℝ} (hlam : -leftmost hH < lam)
    (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, step g H lam⟫ =
      -⟪hH.eigenvectorBasis rfl i, g⟫ / (lam + hH.eigenvalues rfl i) := by
  rw [inner_eigenvectorBasis_eq_div hlam (step_spec hlam).1, inner_neg_right]

/-- **Spectral expansion of the step** (book (8.2.6)): for `λ > -λ₁`,
`step g H λ = -∑ i, (⟪bᵢ, g⟫ / (λ + λᵢ)) • bᵢ` in the eigenvector basis `bᵢ` of `H` with
eigenvalues `λᵢ`. The corresponding expansion of `π` is `secular_eq_secularSum`. -/
theorem step_eq_sum {lam : ℝ} (hlam : -leftmost hH < lam) :
    step g H lam = -∑ i, (⟪hH.eigenvectorBasis rfl i, g⟫ / (lam + hH.eigenvalues rfl i)) •
      hH.eigenvectorBasis rfl i := by
  refine eq_of_inner_eigenvectorBasis (hH := hH) fun i => ?_
  rw [inner_eigenvectorBasis_step hlam, inner_neg_right, inner_eigenvectorBasis_sum, neg_div]

/-- **Spectral expansion of the secular function** (book (8.2.7)): for `λ > -λ₁`,
`π(λ) = ∑ i, ⟪bᵢ, g⟫² / (λ + λᵢ)²`. -/
theorem secular_eq_secularSum {lam : ℝ} (hlam : -leftmost hH < lam) :
    secular g H lam = secularSum (hH.eigenvalues rfl) (secularWeight hH g) lam := by
  rw [secular, ← real_inner_self_eq_norm_sq, inner_eq_sum_eigenvectorBasis (hH := hH)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_eigenvectorBasis_step hlam, secularWeight, neg_div, neg_mul_neg, ← sq, div_pow]

theorem eqOn_secular_secularSum :
    EqOn (secular g H) (secularSum (hH.eigenvalues rfl) (secularWeight hH g))
      (Ioi (-leftmost hH)) := fun _ h => secular_eq_secularSum h

theorem secular_eventuallyEq {lam : ℝ} (hlam : -leftmost hH < lam) :
    secular g H =ᶠ[𝓝 lam] secularSum (hH.eigenvalues rfl) (secularWeight hH g) :=
  Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hlam) fun _ h => secular_eq_secularSum h

theorem secular_eventuallyEq_atTop :
    secular g H =ᶠ[atTop] secularSum (hH.eigenvalues rfl) (secularWeight hH g) :=
  Filter.eventually_of_mem (Ioi_mem_atTop _) fun _ h => secular_eq_secularSum h

/-- **Shape of the secular function** (book §8.2.1 and Corollary 8.2.4, on the interval
`λ > -λ₁ ⊇ (λₛ, ∞)`). For `g ≠ 0`: `π` is positive, continuous, strictly decreasing and strictly
convex on `λ > -λ₁` with limit `0` at `+∞`; `π ^ β` is strictly decreasing and strictly convex
with limit `0` for `β > 0`, and strictly increasing and concave with limit `+∞` for
`β ∈ [-1/2, 0)`. -/
theorem secular_shape (hg : g ≠ 0) (β : ℝ) :
    (∀ lam ∈ Ioi (-leftmost hH), 0 < secular g H lam) ∧
    ContinuousOn (secular g H) (Ioi (-leftmost hH)) ∧
    StrictAntiOn (secular g H) (Ioi (-leftmost hH)) ∧
    StrictConvexOn ℝ (Ioi (-leftmost hH)) (secular g H) ∧
    Tendsto (secular g H) atTop (𝓝 0) ∧
    (0 < β → StrictAntiOn (fun lam => secular g H lam ^ β) (Ioi (-leftmost hH)) ∧
      StrictConvexOn ℝ (Ioi (-leftmost hH)) (fun lam => secular g H lam ^ β) ∧
      Tendsto (fun lam => secular g H lam ^ β) atTop (𝓝 0)) ∧
    (β ∈ Ico (-1 / 2) 0 →
      StrictMonoOn (fun lam => secular g H lam ^ β) (Ioi (-leftmost hH)) ∧
      ConcaveOn ℝ (Ioi (-leftmost hH)) (fun lam => secular g H lam ^ β) ∧
      Tendsto (fun lam => secular g H lam ^ β) atTop atTop) := by
  have hw := secularWeight_nonneg (hH := hH) (g := g)
  have hw0 := (secularWeight_ne_zero_iff (hH := hH)).2 hg
  have hsub := Ioi_subset_secularDomain (hH := hH)
  have heq := eqOn_secular_secularSum (hH := hH) (g := g)
  have heqβ : EqOn (fun lam => secularSum (hH.eigenvalues rfl) (secularWeight hH g) lam ^ β)
      (fun lam => secular g H lam ^ β) (Ioi (-leftmost hH)) := fun x hx => by
    simp only [heq hx]
  have hevβ : (fun lam => secularSum (hH.eigenvalues rfl) (secularWeight hH g) lam ^ β) =ᶠ[atTop]
      (fun lam => secular g H lam ^ β) :=
    (secular_eventuallyEq_atTop (hH := hH) (g := g)).mono fun x hx => by simp only [hx]
  have hconv : Convex ℝ (Ioi (-leftmost hH)) := convex_Ioi _
  obtain ⟨hpos, hneg⟩ := secularSum_rpow_shape hw hw0 β
  refine ⟨fun lam h => heq h ▸ secularSum_pos hw hw0 (hsub h),
    (continuousOn_secularSum.mono hsub).congr fun x hx => heq hx,
    ((secularSum_strictAntiOn hw hw0).mono hsub).congr heq.symm,
    ((secularSum_strictConvexOn hw hw0).subset hsub hconv).congr heq.symm,
    tendsto_secularSum_atTop.congr' (secular_eventuallyEq_atTop (hH := hH) (g := g)).symm,
    fun hβ => ?_, fun hβ => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hpos hβ
    exact ⟨(h1.mono hsub).congr heqβ, (h2.subset hsub hconv).congr heqβ, h3.congr' hevβ⟩
  · obtain ⟨h1, h2, h3⟩ := hneg hβ
    exact ⟨(h1.mono hsub).congr heqβ, (h2.subset hsub hconv).congr heqβ, h3.congr' hevβ⟩

/-! ### The minimum-norm solution and the threshold -/

theorem mem_ker_add_smul_iff {lam : ℝ} {v : E} :
    v ∈ LinearMap.ker ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E) ↔
      ∀ i, (lam + hH.eigenvalues rfl i) * ⟪hH.eigenvectorBasis rfl i, v⟫ = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro h i
    rw [← inner_eigenvectorBasis_add_smul, h, inner_zero_right]
  · intro h
    refine eq_of_inner_eigenvectorBasis (hH := hH) fun i => ?_
    rw [inner_eigenvectorBasis_add_smul, h, inner_zero_right]

/-- An eigenvector `bᵢ` with `λ + λᵢ = 0` lies in the kernel of `H + λ`. -/
theorem eigenvectorBasis_mem_ker {lam : ℝ} {i : Fin (Module.finrank ℝ E)}
    (hi : lam + hH.eigenvalues rfl i = 0) :
    hH.eigenvectorBasis rfl i ∈ LinearMap.ker ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, add_apply, apply_eigenvectorBasis',
    smul_apply, one_apply_eq_self, ← add_smul, add_comm, hi, zero_smul]

variable (hH) in
/-- The minimum-norm solution of `(H + λ) x = -g` (when one exists, `particular_spec`):
`-∑ i, (⟪bᵢ, g⟫ / (λ + λᵢ)) • bᵢ`, the terms with `λ + λᵢ = 0` being `0` (division by zero). It is
`-(H + λ)⁺ g` for the pseudoinverse `(H + λ)⁺`, and at `λ = -λ₁` it is the book's `sₛ`
(Section 8.3), the limit of `s(λ)` as `λ ↓ -λ₁` when that limit exists
(`tendsto_step_threshold`). -/
noncomputable def particular (g : E) (lam : ℝ) : E :=
  -∑ i, (⟪hH.eigenvectorBasis rfl i, g⟫ / (lam + hH.eigenvalues rfl i)) • hH.eigenvectorBasis rfl i

theorem inner_eigenvectorBasis_particular (lam : ℝ) (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, particular hH g lam⟫ =
      -⟪hH.eigenvectorBasis rfl i, g⟫ / (lam + hH.eigenvalues rfl i) := by
  rw [particular, inner_neg_right, inner_eigenvectorBasis_sum, neg_div]

/-- **The minimum-norm solution** of `(H + λ) x = -g`. Write `K = ker (H + λ)`.
(i) `particular hH g λ ∈ Kᗮ`;
(ii) if `g ∈ Kᗮ` (that is, the system is consistent), then `particular hH g λ` solves it, the
solutions are exactly `particular hH g λ + v` with `v ∈ K`, `particular hH g λ` has the least norm
among them, and `⟪g, v⟫ = 0` for `v ∈ K`;
(iii) for `λ > -λ₁` it is the step `s(λ)`. -/
theorem particular_spec (lam : ℝ) :
    particular hH g lam ∈ (LinearMap.ker ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ ∧
    (g ∈ (LinearMap.ker ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ →
      (H + lam • 1) (particular hH g lam) = -g ∧
      (∀ x, (H + lam • 1) x = -g ↔
        x - particular hH g lam ∈ LinearMap.ker ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E)) ∧
      (∀ x, (H + lam • 1) x = -g → ‖particular hH g lam‖ ≤ ‖x‖) ∧
      (∀ v ∈ LinearMap.ker ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E), ⟪g, v⟫ = 0)) ∧
    (-leftmost hH < lam → particular hH g lam = step g H lam) := by
  set K := LinearMap.ker ((H + lam • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E)
  have hperp : particular hH g lam ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    rw [inner_eq_sum_eigenvectorBasis (hH := hH)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_eigenvectorBasis_particular]
    by_cases hi : lam + hH.eigenvalues rfl i = 0
    · simp [hi]
    · rw [(mul_eq_zero.1 ((mem_ker_add_smul_iff (hH := hH)).1 hu i)).resolve_left hi, mul_zero]
  refine ⟨hperp, fun hg => ?_, fun hlam => ?_⟩
  · have hγ : ∀ i, lam + hH.eigenvalues rfl i = 0 → ⟪hH.eigenvectorBasis rfl i, g⟫ = 0 :=
      fun i hi => Submodule.inner_right_of_mem_orthogonal (eigenvectorBasis_mem_ker hi) hg
    have hsol : (H + lam • 1) (particular hH g lam) = -g := by
      refine eq_of_inner_eigenvectorBasis (hH := hH) fun i => ?_
      rw [inner_eigenvectorBasis_add_smul, inner_eigenvectorBasis_particular, inner_neg_right]
      by_cases hi : lam + hH.eigenvalues rfl i = 0
      · rw [hi, hγ i hi]; simp
      · field_simp
    have hiff : ∀ x, (H + lam • 1) x = -g ↔ x - particular hH g lam ∈ K := fun x => by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hsol, sub_eq_zero]
    refine ⟨hsol, hiff, fun x hx => ?_, fun v hv => Submodule.inner_left_of_mem_orthogonal hv hg⟩
    have h0 : ⟪particular hH g lam, x - particular hH g lam⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal ((hiff x).1 hx) hperp
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_real h0
    rw [add_sub_cancel] at hpy
    by_contra hlt
    push Not at hlt
    have := mul_self_lt_mul_self (norm_nonneg x) hlt
    nlinarith [mul_self_nonneg ‖x - particular hH g lam‖]
  · rw [step_eq_sum hlam, particular]

/-- **Behaviour at the threshold** `λ ↓ -λ₁`. Let `K = ker (H - λ₁)` (written `H + (-λ₁) • 1`).
(i) If `g ∈ Kᗮ`, the step `s(λ)` converges to the minimum-norm solution
`sₛ = particular hH g (-λ₁)` and `π(λ) → ‖sₛ‖²` as `λ → -λ₁` from the right: `π` extends
continuously to `[-λ₁, ∞)`, which is how the book's `π(λₛ)` is read.
(ii) Otherwise `π(λ) → +∞`. -/
theorem tendsto_step_threshold :
    (g ∈ (LinearMap.ker ((H + (-leftmost hH) • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ →
      Tendsto (step g H) (𝓝[>] (-leftmost hH)) (𝓝 (particular hH g (-leftmost hH))) ∧
      Tendsto (secular g H) (𝓝[>] (-leftmost hH)) (𝓝 (‖particular hH g (-leftmost hH)‖ ^ 2))) ∧
    (g ∉ (LinearMap.ker ((H + (-leftmost hH) • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ →
      Tendsto (secular g H) (𝓝[>] (-leftmost hH)) atTop) := by
  set L := leftmost hH
  have hev : step g H =ᶠ[𝓝[>] (-L)] particular hH g :=
    eventually_nhdsWithin_of_forall fun lam h => ((particular_spec (g := g) lam).2.2 h).symm
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · have hγ : ∀ i, -L + hH.eigenvalues rfl i = 0 → ⟪hH.eigenvectorBasis rfl i, g⟫ = 0 :=
      fun i hi => Submodule.inner_right_of_mem_orthogonal (eigenvectorBasis_mem_ker hi) hg
    have hcont : ContinuousAt (particular hH g) (-L) := by
      have : Tendsto (fun lam => ∑ i, (⟪hH.eigenvectorBasis rfl i, g⟫ /
          (lam + hH.eigenvalues rfl i)) • hH.eigenvectorBasis rfl i) (𝓝 (-L))
          (𝓝 (∑ i, (⟪hH.eigenvectorBasis rfl i, g⟫ /
          (-L + hH.eigenvalues rfl i)) • hH.eigenvectorBasis rfl i)) := by
        refine tendsto_finsetSum _ fun i _ => ?_
        by_cases hi : -L + hH.eigenvalues rfl i = 0
        · simp only [hγ i hi, zero_div, zero_smul]
          exact tendsto_const_nhds
        · exact ((continuousAt_const.div (continuousAt_id.add continuousAt_const) hi).smul
            continuousAt_const).tendsto
      exact this.neg
    have h1 : Tendsto (step g H) (𝓝[>] (-L)) (𝓝 (particular hH g (-L))) :=
      (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
    exact ⟨h1, (h1.norm.pow 2)⟩
  · -- some eigenvector at `λ₁` carries weight
    obtain ⟨i, hi, hγi⟩ : ∃ i, -L + hH.eigenvalues rfl i = 0 ∧
        ⟪hH.eigenvectorBasis rfl i, g⟫ ≠ 0 := by
      by_contra h
      push Not at h
      refine hg ((Submodule.mem_orthogonal _ _).2 fun v hv => ?_)
      rw [inner_eq_sum_eigenvectorBasis (hH := hH)]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : -L + hH.eigenvalues rfl j = 0
      · rw [h j hj, mul_zero]
      · rw [(mul_eq_zero.1 ((mem_ker_add_smul_iff (hH := hH)).1 hv j)).resolve_left hj,
          zero_mul]
    have hshift : Tendsto (fun lam => lam + L) (𝓝[>] (-L)) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun lam h => ?_⟩
      · exact ((continuous_id.add continuous_const).tendsto' (-L) 0 (neg_add_cancel _)).mono_left
          nhdsWithin_le_nhds
      · simp only [mem_Ioi] at h ⊢; linarith
    have hlim : Tendsto (fun lam => secularWeight hH g i * ((lam + L)⁻¹) ^ 2)
        (𝓝[>] (-L)) atTop :=
      (((tendsto_pow_atTop two_ne_zero).comp (tendsto_inv_nhdsGT_zero.comp hshift))).const_mul_atTop
        (by simp only [secularWeight]; positivity)
    refine tendsto_atTop_mono' _ (eventually_nhdsWithin_of_forall fun lam h => ?_) hlim
    rw [secular_eq_secularSum h, secularSum_apply]
    have hL : lam + hH.eigenvalues rfl i = lam + L := by linarith
    calc secularWeight hH g i * ((lam + L)⁻¹) ^ 2
        = secularWeight hH g i / (lam + hH.eigenvalues rfl i) ^ 2 := by
          rw [hL, div_eq_mul_inv, inv_pow]
      _ ≤ _ := Finset.single_le_sum (f := fun j => secularWeight hH g j /
          (lam + hH.eigenvalues rfl j) ^ 2)
          (fun j _ => div_nonneg (secularWeight_nonneg j) (sq_nonneg _)) (Finset.mem_univ i)

/-! ### Derivatives -/

/-- The `k`-th derivative of the step, `s⁽ᵏ⁾(λ) = (-1) ^ (k + 1) k! (H + λ)⁻⁽ᵏ⁺¹⁾ g`
(`iteratedDeriv_step`); `stepDeriv g H 0 = step g H`. -/
noncomputable def stepDeriv (g : E) (H : E →L[ℝ] E) (k : ℕ) (lam : ℝ) : E :=
  (((-1 : ℝ) ^ (k + 1) * k !) • (Ring.inverse (H + lam • 1) ^ (k + 1))) g

omit [FiniteDimensional ℝ E] in
theorem stepDeriv_zero (lam : ℝ) : stepDeriv g H 0 lam = step g H lam := by
  simp [stepDeriv, step]

/-- The coordinates of `(H + λ)⁻ᵐ v`: `⟪bᵢ, (H + λ)⁻ᵐ v⟫ = ⟪bᵢ, v⟫ / (λ + λᵢ) ^ m`. -/
theorem inner_eigenvectorBasis_inverse_pow {lam : ℝ} (hlam : -leftmost hH < lam) (m : ℕ)
    (v : E) (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, (Ring.inverse (H + lam • 1) ^ m) v⟫ =
      ⟪hH.eigenvectorBasis rfl i, v⟫ / (lam + hH.eigenvalues rfl i) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    change ⟪_, Ring.inverse (H + lam • 1) ((Ring.inverse (H + lam • 1) ^ m) v)⟫ = _
    rw [inner_eigenvectorBasis_eq_div hlam
      (add_smul_inverse_apply hlam _) i, ih, div_div, pow_succ]

theorem inner_eigenvectorBasis_stepDeriv {lam : ℝ} (hlam : -leftmost hH < lam) (k : ℕ)
    (i : Fin (Module.finrank ℝ E)) :
    ⟪hH.eigenvectorBasis rfl i, stepDeriv g H k lam⟫ =
      (-1) ^ (k + 1) * k ! * ⟪hH.eigenvectorBasis rfl i, g⟫ /
        (lam + hH.eigenvalues rfl i) ^ (k + 1) := by
  rw [stepDeriv, smul_apply, real_inner_smul_right,
    inner_eigenvectorBasis_inverse_pow hlam, mul_div_assoc]

/-- The spectral expansion of `s⁽ᵏ⁾(λ)`. -/
theorem stepDeriv_eq_sum {lam : ℝ} (hlam : -leftmost hH < lam) (k : ℕ) :
    stepDeriv g H k lam = ∑ i, ((-1) ^ (k + 1) * k ! * ⟪hH.eigenvectorBasis rfl i, g⟫ /
      (lam + hH.eigenvalues rfl i) ^ (k + 1)) • hH.eigenvectorBasis rfl i :=
  eq_of_inner_eigenvectorBasis (hH := hH) fun i => by
    rw [inner_eigenvectorBasis_stepDeriv hlam, inner_eigenvectorBasis_sum]

theorem hasDerivAt_stepDeriv {lam : ℝ} (hlam : -leftmost hH < lam) (k : ℕ) :
    HasDerivAt (stepDeriv g H k) (stepDeriv g H (k + 1) lam) lam := by
  have hev : stepDeriv g H k =ᶠ[𝓝 lam] fun t => ∑ i, ((-1) ^ (k + 1) * k ! *
      ⟪hH.eigenvectorBasis rfl i, g⟫ / (t + hH.eigenvalues rfl i) ^ (k + 1)) •
        hH.eigenvectorBasis rfl i :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hlam) fun t ht => stepDeriv_eq_sum ht k
  have hD := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hasDerivAt_div_add_pow ((-1) ^ (k + 1) * k ! * ⟪hH.eigenvectorBasis rfl i, g⟫)
      (hH.eigenvalues rfl i) (k + 1) (mem_secularDomain_of_lt hlam i).ne').smul_const
      (hH.eigenvectorBasis rfl i)
  refine (hD.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [stepDeriv_eq_sum hlam (k + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- **Derivatives of the step** (book (8.2.29)). For `λ > -λ₁` and every `k`,
`iteratedDeriv k (step g H) λ = stepDeriv g H k λ`, and the derivatives are computed recursively
by the solves `(H + λ) s⁽ᵏ⁺¹⁾ = -(k + 1) s⁽ᵏ⁾`. -/
theorem iteratedDeriv_step {lam : ℝ} (hlam : -leftmost hH < lam) (k : ℕ) :
    iteratedDeriv k (step g H) lam = stepDeriv g H k lam ∧
      (H + lam • 1) (stepDeriv g H (k + 1) lam) = -((k + 1 : ℝ) • stepDeriv g H k lam) := by
  constructor
  · induction k generalizing lam with
    | zero => rw [iteratedDeriv_zero, stepDeriv_zero]
    | succ k ih =>
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k (step g H) =ᶠ[𝓝 lam] stepDeriv g H k :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hlam) fun t ht => ih ht
      rw [hev.deriv_eq, (hasDerivAt_stepDeriv hlam k).deriv]
  · refine eq_of_inner_eigenvectorBasis (hH := hH) fun i => ?_
    have ha : lam + hH.eigenvalues rfl i ≠ 0 := (mem_secularDomain_of_lt hlam i).ne'
    rw [inner_eigenvectorBasis_add_smul, inner_eigenvectorBasis_stepDeriv hlam, inner_neg_right,
      real_inner_smul_right, inner_eigenvectorBasis_stepDeriv hlam, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The coefficients `αₖ = (2 k + 1)! / (k!)²` of Theorem 8.2.6. -/
noncomputable def secularCoeff (k : ℕ) : ℝ := ((2 * k + 1)! : ℝ) / (k ! : ℝ) ^ 2

@[simp]
theorem secularCoeff_zero : secularCoeff 0 = 1 := by simp [secularCoeff]

/-- The recursion `αₖ₊₁ = 2 (2 k + 3) / (k + 1) αₖ` (book (8.2.30)). -/
theorem secularCoeff_succ (k : ℕ) :
    secularCoeff (k + 1) = 2 * (2 * k + 3) / (k + 1) * secularCoeff k := by
  rw [secularCoeff, secularCoeff, show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring,
    Nat.factorial_succ (2 * k + 1 + 1), Nat.factorial_succ (2 * k + 1), Nat.factorial_succ k]
  push_cast
  field_simp
  ring

/-- The derivatives of the secular function in closed form (book (B.8.8)): for `λ > -λ₁`,
`π⁽ʲ⁾(λ) = (-1) ^ j (j + 1)! ∑ i, ⟪bᵢ, g⟫² / (λ + λᵢ) ^ (j + 2)`. -/
theorem iteratedDeriv_secular_eq {lam : ℝ} (hlam : -leftmost hH < lam) (j : ℕ) :
    iteratedDeriv j (secular g H) lam = (-1) ^ j * (j + 1)! *
      secularMoment (hH.eigenvalues rfl) (secularWeight hH g) (j + 2) lam := by
  rw [(secular_eventuallyEq hlam).iteratedDeriv_eq j,
    iteratedDeriv_secularSum j fun i => (mem_secularDomain_of_lt hlam i).ne']

/-- **Derivatives of the secular function** (Cartis–Gould–Toint, Theorem 8.2.6). For `λ > -λ₁`
and every `k`, with `s⁽ʲ⁾ = stepDeriv g H j λ` (computed by the solves of `iteratedDeriv_step`)
and `αₖ = secularCoeff k`:
`π⁽²ᵏ⁺¹⁾(λ) = 2 αₖ ⟪s⁽ᵏ⁾, s⁽ᵏ⁺¹⁾⟫` and `π⁽²ᵏ⁺²⁾(λ) = αₖ₊₁ ‖s⁽ᵏ⁺¹⁾‖²`. -/
theorem iteratedDeriv_secular {lam : ℝ} (hlam : -leftmost hH < lam) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (secular g H) lam =
        2 * secularCoeff k * ⟪stepDeriv g H k lam, stepDeriv g H (k + 1) lam⟫ ∧
      iteratedDeriv (2 * k + 2) (secular g H) lam =
        secularCoeff (k + 1) * ‖stepDeriv g H (k + 1) lam‖ ^ 2 := by
  have hk : (k ! : ℝ) ≠ 0 := by positivity
  constructor
  · rw [iteratedDeriv_secular_eq hlam, inner_eq_sum_eigenvectorBasis (hH := hH),
      secularMoment_apply, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have ha : lam + hH.eigenvalues rfl i ≠ 0 := (mem_secularDomain_of_lt hlam i).ne'
    rw [inner_eigenvectorBasis_stepDeriv hlam, inner_eigenvectorBasis_stepDeriv hlam,
      secularCoeff, secularWeight, show 2 * k + 1 + 1 = (2 * k + 1) + 1 by ring,
      Nat.factorial_succ (2 * k + 1), Nat.factorial_succ k]
    push_cast
    field_simp
    ring
  · rw [iteratedDeriv_secular_eq hlam, ← real_inner_self_eq_norm_sq,
      inner_eq_sum_eigenvectorBasis (hH := hH), secularMoment_apply, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have ha : lam + hH.eigenvalues rfl i ≠ 0 := (mem_secularDomain_of_lt hlam i).ne'
    rw [inner_eigenvectorBasis_stepDeriv hlam, secularCoeff, secularWeight,
      show 2 * (k + 1) + 1 = 2 * k + 2 + 1 by ring]
    have hk1 : ((k + 1)! : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-! ### Taylor estimates -/

/-- The Taylor polynomials of `π` and of its spectral form agree at `λ > -λ₁`. -/
theorem sum_taylor_secular_eq {lam : ℝ} (hlam : -leftmost hH < lam) (m : ℕ) (δ : ℝ) :
    ∑ j ∈ range m, iteratedDeriv j (secular g H) lam / j ! * δ ^ j =
      ∑ j ∈ range m, iteratedDeriv j
        (secularSum (hH.eigenvalues rfl) (secularWeight hH g)) lam / j ! * δ ^ j :=
  Finset.sum_congr rfl fun j _ => by rw [(secular_eventuallyEq hlam).iteratedDeriv_eq j]

/-- **Lower and upper Taylor estimates of `π`** (Cartis–Gould–Toint, Theorem 8.2.2, on the
interval `λ > -λ₁ ⊇ (λₛ, ∞)`). Let `λc > -λ₁` and `tₖ(δ) = ∑ j ≤ k, π⁽ʲ⁾(λc) / j! δʲ`. For
`δ > 0`, `π(λc + δ) ≤ tₖ(δ)` for even `k` and `π(λc + δ) ≥ tₖ(δ)` for odd `k`; for
`-λ₁ - λc < δ < 0`, `tₖ(δ) ≤ tₖ₊₁(δ) ≤ π(λc + δ)`. The strict forms (for `g ≠ 0`) are
`secular_taylor_bounds_strict`. -/
theorem secular_taylor_bounds {lamc : ℝ} (hlam : -leftmost hH < lamc) (k : ℕ) :
    (∀ δ, 0 < δ → (Even k → secular g H (lamc + δ) ≤
        ∑ j ∈ range (k + 1), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j) ∧
      (Odd k → ∑ j ∈ range (k + 1), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j ≤
        secular g H (lamc + δ))) ∧
    (∀ δ, δ < 0 → -leftmost hH < lamc + δ →
      ∑ j ∈ range (k + 1), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j ≤
        ∑ j ∈ range (k + 2), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j ∧
      ∑ j ∈ range (k + 2), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j ≤
        secular g H (lamc + δ)) := by
  obtain ⟨hpos, hneg⟩ := secularSum_taylor_bounds secularWeight_nonneg
    (mem_secularDomain_of_lt hlam) k
  simp only [sum_taylor_secular_eq hlam]
  refine ⟨fun δ hδ => ?_, fun δ hδ hlamδ => ?_⟩
  · rw [secular_eq_secularSum (by linarith : -leftmost hH < lamc + δ)]
    exact hpos δ hδ
  · rw [secular_eq_secularSum hlamδ]
    exact hneg δ hδ (mem_secularDomain_of_lt hlamδ)

/-- The strict form of `secular_taylor_bounds` for `g ≠ 0` (Theorem 8.2.2, strict part). -/
theorem secular_taylor_bounds_strict (hg : g ≠ 0) {lamc : ℝ} (hlam : -leftmost hH < lamc)
    (k : ℕ) :
    (∀ δ, 0 < δ → (Even k → secular g H (lamc + δ) <
        ∑ j ∈ range (k + 1), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j) ∧
      (Odd k → ∑ j ∈ range (k + 1), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j <
        secular g H (lamc + δ))) ∧
    (∀ δ, δ < 0 → -leftmost hH < lamc + δ →
      ∑ j ∈ range (k + 1), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j <
        ∑ j ∈ range (k + 2), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j ∧
      ∑ j ∈ range (k + 2), iteratedDeriv j (secular g H) lamc / j ! * δ ^ j <
        secular g H (lamc + δ)) := by
  obtain ⟨hpos, hneg⟩ := secularSum_taylor_bounds_strict secularWeight_nonneg
    ((secularWeight_ne_zero_iff (hH := hH)).2 hg) (mem_secularDomain_of_lt hlam) k
  simp only [sum_taylor_secular_eq hlam]
  refine ⟨fun δ hδ => ?_, fun δ hδ hlamδ => ?_⟩
  · rw [secular_eq_secularSum (by linarith : -leftmost hH < lamc + δ)]
    exact hpos δ hδ
  · rw [secular_eq_secularSum hlamδ]
    exact hneg δ hδ (mem_secularDomain_of_lt hlamδ)

/-! ### The transformed secular function -/

theorem secular_rpow_eventuallyEq {lam : ℝ} (hlam : -leftmost hH < lam) (β : ℝ) :
    (fun t => secular g H t ^ β) =ᶠ[𝓝 lam]
      fun t => secularSum (hH.eigenvalues rfl) (secularWeight hH g) t ^ β :=
  (secular_eventuallyEq (g := g) hlam).mono fun t ht => by simp only [ht]

/-- **Derivatives of the transformed secular function** (Cartis–Gould–Toint, Lemma 8.2.3, on
`λ > -λ₁`). Let `g ≠ 0` and `q = fun λ => π(λ) ^ β`. Then `q' < 0` for `β > 0` and `q' > 0` for
`β < 0`; `q'' > 0` for `β > 0`; `q'' ≤ 0` for `β ∈ [-1/2, 0)`, strictly unless `β = -1/2` and `g`
is an eigenvector of `H`, in which case `q'' = 0`. -/
theorem secular_rpow_deriv_sign (hg : g ≠ 0) {lam : ℝ} (hlam : -leftmost hH < lam) (β : ℝ) :
    (0 < β → deriv (fun t => secular g H t ^ β) lam < 0) ∧
    (β < 0 → 0 < deriv (fun t => secular g H t ^ β) lam) ∧
    (0 < β → 0 < iteratedDeriv 2 (fun t => secular g H t ^ β) lam) ∧
    (β ∈ Ico (-1 / 2) 0 → iteratedDeriv 2 (fun t => secular g H t ^ β) lam ≤ 0) ∧
    (β ∈ Ico (-1 / 2) 0 → (β ≠ -1 / 2 ∨ ¬ ∃ c : ℝ, H g = c • g) →
      iteratedDeriv 2 (fun t => secular g H t ^ β) lam < 0) ∧
    (β = -1 / 2 → (∃ c : ℝ, H g = c • g) →
      iteratedDeriv 2 (fun t => secular g H t ^ β) lam = 0) := by
  have hev := secular_rpow_eventuallyEq (g := g) hlam β
  rw [hev.deriv_eq, hev.iteratedDeriv_eq, ← singlePole_secularWeight_iff hg]
  exact secularSum_rpow_deriv_sign secularWeight_nonneg
    ((secularWeight_ne_zero_iff (hH := hH)).2 hg) β (mem_secularDomain_of_lt hlam)

/-- **First-order Taylor estimates of the transformed secular function** (Cartis–Gould–Toint,
Theorem 8.2.5, on `λ > -λ₁`). Let `g ≠ 0`, `λc > -λ₁`, `λc + δ > -λ₁`, `q = fun λ => π(λ) ^ β`
and `t₁(δ) = q(λc) + q'(λc) δ`. For `β > 0`, `q(λc + δ) ≥ t₁(δ)`; for `β ∈ [-1/2, 0)`,
`q(λc + δ) ≤ t₁(δ)`. Both are strict for `δ ≠ 0`, except when `β = -1/2` and `g` is an
eigenvector of `H`: then `q` is affine and `q(λc + δ) = t₁(δ)`. The sign statements of
Lemma 8.2.3 are `secular_rpow_deriv_sign`. -/
theorem secular_rpow_tangent (hg : g ≠ 0) {lamc δ : ℝ} (hlam : -leftmost hH < lamc)
    (hlamδ : -leftmost hH < lamc + δ) (β : ℝ) :
    (0 < β → secular g H lamc ^ β + deriv (fun t => secular g H t ^ β) lamc * δ ≤
      secular g H (lamc + δ) ^ β) ∧
    (0 < β → δ ≠ 0 → secular g H lamc ^ β + deriv (fun t => secular g H t ^ β) lamc * δ <
      secular g H (lamc + δ) ^ β) ∧
    (β ∈ Ico (-1 / 2) 0 → secular g H (lamc + δ) ^ β ≤
      secular g H lamc ^ β + deriv (fun t => secular g H t ^ β) lamc * δ) ∧
    (β ∈ Ico (-1 / 2) 0 → δ ≠ 0 → (β ≠ -1 / 2 ∨ ¬ ∃ c : ℝ, H g = c • g) →
      secular g H (lamc + δ) ^ β <
        secular g H lamc ^ β + deriv (fun t => secular g H t ^ β) lamc * δ) ∧
    (β = -1 / 2 → (∃ c : ℝ, H g = c • g) → secular g H (lamc + δ) ^ β =
      secular g H lamc ^ β + deriv (fun t => secular g H t ^ β) lamc * δ) := by
  rw [(secular_rpow_eventuallyEq (g := g) hlam β).deriv_eq, secular_eq_secularSum hlam,
    secular_eq_secularSum hlamδ, ← singlePole_secularWeight_iff hg]
  exact secularSum_rpow_tangent secularWeight_nonneg
    ((secularWeight_ne_zero_iff (hH := hH)).2 hg) β (mem_secularDomain_of_lt hlam)
    (mem_secularDomain_of_lt hlamδ)

/-- The defining solves of the derivatives determine them: for `λ > -λ₁`, the only solution of
`(H + λ) s = -(k + 1) s⁽ᵏ⁾(λ)` is `s⁽ᵏ⁺¹⁾(λ)` (book (8.2.29)). -/
theorem stepDeriv_succ_unique {lam : ℝ} (hlam : -leftmost hH < lam) (k : ℕ) {s : E}
    (hs : (H + lam • 1) s = -((k + 1 : ℝ) • stepDeriv g H k lam)) :
    s = stepDeriv g H (k + 1) lam :=
  injective_add_smul hlam (hs.trans (iteratedDeriv_step hlam k).2.symm)

omit [FiniteDimensional ℝ E] in
/-- For `g = 0` the step and the secular function vanish identically. -/
theorem secular_zero_left (H : E →L[ℝ] E) : secular 0 H = 0 := by
  ext lam
  simp [secular, step]

omit [FiniteDimensional ℝ E] in
/-- The degenerate case `g = 0` of Lemma 8.2.3: the transformed secular function is constant, so
its derivatives vanish and the non-strict sign statements hold trivially. -/
theorem secular_rpow_zero_left (H : E →L[ℝ] E) (β lam : ℝ) (n : ℕ) :
    iteratedDeriv (n + 1) (fun t => secular 0 H t ^ β) lam = 0 := by
  simp only [secular_zero_left, Pi.zero_apply]
  rw [iteratedDeriv_succ']
  simp

/-- The transformed secular function is strictly concave on `λ > -λ₁` for `β ∈ [-1/2, 0)` and
`g ≠ 0`, except when `β = -1/2` and `g` is an eigenvector of `H` (then it is affine). -/
theorem secular_rpow_strictConcaveOn (hg : g ≠ 0) {β : ℝ} (hβ : β ∈ Ico (-1 / 2) 0)
    (hne : β ≠ -1 / 2 ∨ ¬ ∃ c : ℝ, H g = c • g) :
    StrictConcaveOn ℝ (Ioi (-leftmost hH)) (fun t => secular g H t ^ β) := by
  rw [← singlePole_secularWeight_iff hg] at hne
  refine ((secularSum_rpow_strictConcaveOn secularWeight_nonneg
    ((secularWeight_ne_zero_iff (hH := hH)).2 hg) β hβ hne).subset Ioi_subset_secularDomain
    (convex_Ioi _)).congr fun t ht => ?_
  simp only [secular_eq_secularSum ht]

/-- The transformed secular function at the threshold `λ ↓ -λ₁`, with `K = ker (H - λ₁)` and
`sₛ = particular hH g (-λ₁)`: if `g ∈ Kᗮ`, then `π(λ) ^ β → (‖sₛ‖²) ^ β` (when `sₛ ≠ 0` or
`β ≥ 0`); otherwise `π(λ) ^ β → +∞` for `β > 0` and `→ 0` for `β < 0`. -/
theorem tendsto_secular_rpow_threshold (β : ℝ) :
    (g ∈ (LinearMap.ker ((H + (-leftmost hH) • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ →
      (particular hH g (-leftmost hH) ≠ 0 ∨ 0 ≤ β) →
      Tendsto (fun t => secular g H t ^ β) (𝓝[>] (-leftmost hH))
        (𝓝 ((‖particular hH g (-leftmost hH)‖ ^ 2) ^ β))) ∧
    (g ∉ (LinearMap.ker ((H + (-leftmost hH) • 1 : E →L[ℝ] E) : E →ₗ[ℝ] E))ᗮ →
      (0 < β → Tendsto (fun t => secular g H t ^ β) (𝓝[>] (-leftmost hH)) atTop) ∧
      (β < 0 → Tendsto (fun t => secular g H t ^ β) (𝓝[>] (-leftmost hH)) (𝓝 0))) := by
  refine ⟨fun hg h => ?_, fun hg => ⟨fun hβ => ?_, fun hβ => ?_⟩⟩
  · have h' : ‖particular hH g (-leftmost hH)‖ ^ 2 ≠ 0 ∨ 0 ≤ β :=
      h.imp_left fun hp => pow_ne_zero 2 (norm_ne_zero_iff.2 hp)
    exact (Real.continuousAt_rpow_const _ β h').tendsto.comp
      ((tendsto_step_threshold (hH := hH)).1 hg).2
  · exact (tendsto_rpow_atTop hβ).comp ((tendsto_step_threshold (hH := hH)).2 hg)
  · have := (tendsto_rpow_neg_atTop (neg_pos.2 hβ)).comp
      ((tendsto_step_threshold (hH := hH)).2 hg)
    simpa only [neg_neg, Function.comp_def] using this

/-! ### Calculus facts about the secular function -/

section SecularCalculus

variable {g : E} {hH : (H : E →ₗ[ℝ] E).IsSymmetric}

/-- `π` is differentiable on `λ > -λ₁`. -/
theorem hasDerivAt_secular {lam : ℝ} (hlam : -leftmost hH < lam) :
    HasDerivAt (secular g H) (deriv (secular g H) lam) lam :=
  ((hasDerivAt_secularSum (μ := hH.eigenvalues rfl) (w := secularWeight hH g)
    fun i => (mem_secularDomain_of_lt hlam i).ne').congr_of_eventuallyEq
      (secular_eventuallyEq hlam)).differentiableAt.hasDerivAt

/-- For `g ≠ 0`, `π(λ) > 0` on `λ > -λ₁`. -/
theorem secular_pos (hg : g ≠ 0) {lam : ℝ} (hlam : -leftmost hH < lam) : 0 < secular g H lam :=
  (secular_shape (hH := hH) hg 0).1 lam hlam

/-- For `g ≠ 0`, `π'(λ) < 0` on `λ > -λ₁` (book (8.2.4) and Theorem 8.2.6). -/
theorem deriv_secular_neg (hg : g ≠ 0) {lam : ℝ} (hlam : -leftmost hH < lam) :
    deriv (secular g H) lam < 0 := by
  rw [(secular_eventuallyEq hlam).deriv_eq,
    deriv_secularSum fun i => (mem_secularDomain_of_lt hlam i).ne']
  have := secularMoment_pos secularWeight_nonneg ((secularWeight_ne_zero_iff (hH := hH)).2 hg)
    (mem_secularDomain_of_lt hlam) 3
  linarith

/-- The derivative of the transformed secular function: `(π ^ β)' = β π ^ (β - 1) π'`
(book (8.2.18)). -/
theorem hasDerivAt_secular_rpow (hg : g ≠ 0) {lam : ℝ} (hlam : -leftmost hH < lam) (β : ℝ) :
    HasDerivAt (fun t => secular g H t ^ β)
      (β * secular g H lam ^ (β - 1) * deriv (secular g H) lam) lam := by
  convert (hasDerivAt_secular hlam).rpow_const (p := β) (Or.inl (secular_pos hg hlam).ne') using 1
  ring

/-- `π ^ β` is smooth on `λ > -λ₁` for `g ≠ 0`. -/
theorem contDiffOn_secular_rpow (hg : g ≠ 0) (β : ℝ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun t => secular g H t ^ β) (Ioi (-leftmost hH)) :=
  ((contDiffOn_secularSum_rpow secularWeight_nonneg
    ((secularWeight_ne_zero_iff (hH := hH)).2 hg) β).mono Ioi_subset_secularDomain).congr
    fun x hx => by simp only [secular_eq_secularSum hx]

/-- The spectral moments decrease in `λ` on `λ > -λ₁`. -/
theorem secularMoment_le_of_le {x₀ x : ℝ} (hx₀ : -leftmost hH < x₀) (hx : x₀ ≤ x) (m : ℕ) :
    secularMoment (hH.eigenvalues rfl) (secularWeight hH g) m x ≤
      secularMoment (hH.eigenvalues rfl) (secularWeight hH g) m x₀ := by
  have h0 := mem_secularDomain_of_lt hx₀
  refine Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_left (secularWeight_nonneg i)
    (pow_pos (h0 i) m) (pow_le_pow_left₀ (h0 i).le (by linarith) m)

end SecularCalculus

omit [FiniteDimensional ℝ E] in
/-- `g ≠ 0` as soon as the secular function has a positive value. -/
theorem ne_zero_of_secular_pos {lam : ℝ} (h : 0 < secular g H lam) : g ≠ 0 := by
  rintro rfl
  simp [secular_zero_left] at h

end Subproblem
