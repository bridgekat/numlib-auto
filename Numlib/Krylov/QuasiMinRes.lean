import Mathlib.Algebra.Order.Chebyshev
import Numlib.Krylov.Hessenberg

/-!
# Quasi-minimal residual methods

What a Krylov method can still prove when the basis in which it expands the residual is **not**
orthonormal.

* `Krylov.HessenbergRelation₂ A z v h`: the relation `A z_j = ∑_{i ≤ j+1} h_ij v_i` for two
  *unrelated* families, the iterate basis `z` on the left and the residual basis `v` on the
  right. `Krylov.HessenbergRelation` is the diagonal case `z = v`
  (`Krylov.HessenbergRelation₂.of_hessenbergRelation`); flexible GMRES
  (Saad, *Iterative Methods*[^saad-iterative] (9.22), where `z_j = M_j⁻¹ v_j` for a
  step-dependent preconditioner) and TFQMR (Saad (7.70)) are genuinely two-family, and the
  residual formulas `residual_eq`, `residual_eq_of_mulVec_eq` hold verbatim at this generality.
* `Krylov.quasiResidual h β m y = ‖β e₁ - H̄_m y‖₂`, and the specification
  `Krylov.IsQuasiMinResIterate z h β x₀ m x`, "`x = x₀ + Z_m y` with `y` minimizing the
  quasi-residual": QMR (Freund–Nachtigal[^freund-nachtigal]; Saad Algorithm 7.4),
  TFQMR (Algorithm 7.8), QGMRES and DQGMRES
  (Algorithms 6.12–6.13) and FGMRES (Algorithm 9.6) all satisfy it, each for its own `z`, `v`
  and `h`. It is `Krylov.IsMinResIterate` when the residual basis is the Arnoldi one
  (`Krylov.isQuasiMinResIterate_iff_isMinResIterate`); in general it minimizes something else,
  and three theorems say by how much:
  * `Krylov.IsQuasiMinResIterate.norm_residual_le`: `‖b - A x‖ ≤ C ‖γ_m‖` whenever
    `‖∑ w_i v_i‖ ≤ C ‖w‖₂` (Saad Proposition 7.3, (6.51), (7.83); `C = √(m+1)` for unit vectors
    by `Krylov.norm_sum_smul_le_sqrt_mul`);
  * `Krylov.IsQuasiMinResIterate.norm_residual_le_mul`: `‖r^Q_m‖ ≤ (C/c) ‖b - A x'‖` for every
    `x'` of the same affine space, when also `c ‖w‖₂ ≤ ‖∑ w_i v_i‖` — Saad Theorem 7.4 and
    Theorem 6.11, with `C/c` the conditioning of the residual basis;
  * `Krylov.IsQuasiMinResIterate.isMinOn_norm_residual`: with an orthonormal residual basis and an
    arbitrary `z`, the iterate genuinely minimizes `‖b - A x‖` over `x₀ + span {z_0, …, z_{m-1}}`
    (Saad Proposition 9.2, the optimality of FGMRES).
* The harmonic relations between successive quasi-residual norms, in their pure Givens form as
  statements about `Krylov.gamma` and `Krylov.givensC` alone: `Krylov.inv_sq_norm_gamma`,
  `Krylov.inv_sq_norm_gamma_eq_sum` and `Krylov.exists_norm_gamma_div_givensC_le` are Saad (7.23),
  (7.24) and Proposition 7.5, as `Krylov.inv_sq_norm_residual_minRes` and
  `Krylov.exists_norm_residual_galerkin_le` are (6.65) and Proposition 6.15 for true residuals.
* `Krylov.IsQuasiMinResIterate.eq_combination`: successive quasi-minimal-residual iterates are the
  smoothing combinations `x^Q_{m+1} = |s_m|² x^Q_m + |c_m|² x^F_{m+1}` of the previous
  quasi-minimal-residual iterate and the Galerkin iterate at the current step (Saad (7.29)–(7.30),
  (6.58); Zhou–Walker[^zhou-walker]).

Indices are `0`-based, as in the rest of the Krylov layer: `ρ^Q_k = ‖γ_k‖` is the quasi-residual
norm after `k` steps and `ρ^F_k = ρ^Q_k / |c_{k-1}|` the Galerkin one.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^freund-nachtigal]: Roland W. Freund and Noël M. Nachtigal, *QMR: a quasi-minimal residual method
  for non-Hermitian linear systems*, Numerische Mathematik 60 (1991), 315–339.
[^zhou-walker]: Lu Zhou and Homer F. Walker, *Residual smoothing techniques for iterative
  methods*, SIAM Journal on Scientific Computing 15 (1994), 297–312.
-/

open Krylov Finset

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

/-! ### The two-family Hessenberg relation -/

/-- A pair of sequences `z`, `v` satisfying the two-family Hessenberg relation
`A z_j = ∑_{i ≤ j+1} h i j v_i` with `h` upper Hessenberg: the iterate basis `z` on the left, the
residual basis `v` on the right (Saad, *Iterative Methods*, (9.22) for FGMRES and (7.70) for
TFQMR). `Krylov.HessenbergRelation` is the diagonal case `z = v`, embedded by
`Krylov.HessenbergRelation₂.of_hessenbergRelation`. -/
structure HessenbergRelation₂ (A : E →ₗ[𝕜] E) (z v : ℕ → E) (h : ℕ → ℕ → 𝕜) : Prop where
  /-- The expansion of `A z_j` in the residual basis up to `v_{j+1}`. -/
  apply_eq : ∀ j, A (z j) = ∑ i ∈ range (j + 2), h i j • v i
  /-- The coefficients are upper Hessenberg. -/
  eq_zero_of_lt : ∀ i j, j + 1 < i → h i j = 0

namespace HessenbergRelation₂

/-- A one-family Hessenberg relation is the two-family relation with `z = v`. -/
theorem of_hessenbergRelation {A : E →ₗ[𝕜] E} {v : ℕ → E} {h : ℕ → ℕ → 𝕜}
    (hv : HessenbergRelation A v h) : HessenbergRelation₂ A v v h :=
  ⟨hv.apply_eq, hv.eq_zero_of_lt⟩

variable {A : E →ₗ[𝕜] E} {z v : ℕ → E} {h : ℕ → ℕ → 𝕜} (hv : HessenbergRelation₂ A z v h)
include hv

/-- The matrix `H̄_m` cut out of the coefficients of a two-family relation is upper Hessenberg. -/
theorem hessenbergOf_isUpperHessenbergRect (m : ℕ) : (hessenbergOf h m).IsUpperHessenbergRect :=
  fun i j hij => hv.eq_zero_of_lt i j hij

/-- The Hessenberg expansion of `A z_j` may be taken over any range containing `j + 2`. -/
private theorem apply_eq_range (j N : ℕ) (hj : j + 2 ≤ N) :
    A (z j) = ∑ i ∈ range N, h i j • v i := by
  rw [hv.apply_eq j]
  refine Finset.sum_subset (by simpa using hj) fun i hi hi' => ?_
  rw [Finset.mem_range] at hi'
  rw [hv.eq_zero_of_lt i j (by omega), zero_smul]

/-- `A Z_m = V_{m+1} H̄_m` (Saad, *Iterative Methods*, (9.22)) in coordinates. -/
theorem apply_sum (m : ℕ) (y : Fin m → 𝕜) :
    A (∑ j, y j • z j) = ∑ i : Fin (m + 1), (hessenbergOf h m).mulVec y i • v i := by
  rw [map_sum]
  have hleft : ∀ j : Fin m, A (y j • z j) = ∑ i : Fin (m + 1), (y j * h i j) • v i := by
    intro j
    rw [map_smul, hv.apply_eq_range (j : ℕ) (m + 1) (by omega), Finset.smul_sum,
      ← Fin.sum_univ_eq_sum_range (fun i => y j • h i (j : ℕ) • v i) (m + 1)]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  rw [Finset.sum_congr rfl fun j _ => hleft j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hessenbergOf, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]

/-- Saad, *Iterative Methods*, (9.25): with `r₀ = β v₀`, the residual of `x₀ + Z_m y` is
`V_{m+1} (β e₁ - H̄_m y)`. The two-family form of `Krylov.HessenbergRelation.residual_eq`; it is
Saad (7.16) for QMR, (7.75) for TFQMR and (9.25) for FGMRES. -/
theorem residual_eq {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0) (m : ℕ) (y : Fin m → 𝕜) :
    b - A (x₀ + ∑ j, y j • z j) =
      ∑ i : Fin (m + 1), (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i • v i := by
  have hfirst : ∑ i : Fin (m + 1), firstVec β (m + 1) i • v i = β • v 0 := by
    rw [Finset.sum_eq_single (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))]
    · rfl
    · intro i _ hi
      have : (i : ℕ) ≠ 0 := fun hc => hi (Fin.ext hc)
      simp [firstVec, this]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  have hAx : A (x₀ + ∑ j, y j • z j) = A x₀ + ∑ i : Fin (m + 1),
      (hessenbergOf h m).mulVec y i • v i := by
    rw [map_add, hv.apply_sum m y]
  have hsplit : ∑ i : Fin (m + 1), (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i • v i
      = β • v 0 - ∑ i : Fin (m + 1), (hessenbergOf h m).mulVec y i • v i := by
    rw [← hfirst, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, sub_smul]
  rw [hsplit, hAx, ← hr]
  abel

/-- Saad, *Iterative Methods*, (7.76) and (9.23): if `H_m y = β e₁` then the residual of
`x₀ + Z_m y` is `-(h_{m,m-1} y_{m-1}) v_m`. The two-family form of
`Krylov.HessenbergRelation.residual_eq_of_mulVec_eq`. -/
theorem residual_eq_of_mulVec_eq {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0) {m : ℕ}
    (hm : 0 < m) (y : Fin m → 𝕜) (hy : (hessenbergSqOf h m).mulVec y = firstVec β m) :
    b - A (x₀ + ∑ j, y j • z j) = -(h m (m - 1) * y ⟨m - 1, by omega⟩) • v m := by
  rw [hv.residual_eq hr m y]
  have hzero : ∀ i : Fin (m + 1), (i : ℕ) < m →
      (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i = 0 := by
    intro i hi
    have h1 : (hessenbergOf h m).mulVec y i = (hessenbergSqOf h m).mulVec y ⟨i, hi⟩ := by
      simp [Matrix.mulVec, dotProduct, hessenbergOf, hessenbergSqOf]
    have h2 : firstVec β (m + 1) i = firstVec β m ⟨i, hi⟩ := by simp [firstVec]
    simp only [Pi.sub_apply, h1, h2, hy, sub_self]
  have hlast : (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) ⟨m, Nat.lt_succ_self m⟩ =
      -(h m (m - 1) * y ⟨m - 1, by omega⟩) := by
    have hfv : firstVec β (m + 1) (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = 0 := by
      simp [firstVec, hm.ne']
    have hmv : (hessenbergOf h m).mulVec y (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) =
        h m (m - 1) * y ⟨m - 1, by omega⟩ := by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single (⟨m - 1, by omega⟩ : Fin m)]
      · rfl
      · intro j _ hj
        have : (j : ℕ) + 1 < m := by
          have := j.isLt
          have : (j : ℕ) ≠ m - 1 := fun hc => hj (Fin.ext hc)
          omega
        rw [hessenbergOf, Matrix.of_apply, hv.eq_zero_of_lt m j (by omega), zero_mul]
      · intro hc; exact absurd (Finset.mem_univ _) hc
    simp only [Pi.sub_apply, hfv, hmv, zero_sub]
  rw [Finset.sum_eq_single (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))]
  · rw [hlast]
  · intro i _ hi
    have : (i : ℕ) < m := by
      have := i.isLt
      have : (i : ℕ) ≠ m := fun hc => hi (Fin.ext hc)
      omega
    rw [hzero i this, zero_smul]
  · intro hc; exact absurd (Finset.mem_univ _) hc

end HessenbergRelation₂

/-! ### The quasi-residual -/

/-- The quasi-residual `‖β e₁ - H̄_m y‖₂` (Saad, *Iterative Methods*, §7.3.2): the Euclidean norm
of the coefficient vector, in the residual basis, of the residual of `x₀ + Z_m y`. It is the true
residual norm exactly when that basis is orthonormal. -/
noncomputable def quasiResidual (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) (y : Fin m → 𝕜) : ℝ :=
  ‖(WithLp.toLp 2 (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) :
    EuclideanSpace 𝕜 (Fin (m + 1)))‖

/-- `Krylov.quasiResidual` unfolded, for rewriting. -/
theorem quasiResidual_def (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) (y : Fin m → 𝕜) :
    quasiResidual h β m y =
      ‖(WithLp.toLp 2 (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) :
        EuclideanSpace 𝕜 (Fin (m + 1)))‖ := rfl

/-- The quasi-residual is a norm, hence nonnegative. -/
theorem quasiResidual_nonneg (h : ℕ → ℕ → 𝕜) (β : 𝕜) (m : ℕ) (y : Fin m → 𝕜) :
    0 ≤ quasiResidual h β m y := norm_nonneg _

namespace HessenbergRelation₂

/-- Saad, *Iterative Methods*, Proposition 7.3 and (6.51): if the residual basis satisfies
`‖∑ w_i v_i‖ ≤ C ‖w‖₂` then the true residual of `x₀ + Z_m y` is at most `C` times its
quasi-residual — for *every* `y`, with no Givens hypothesis. The quasi-minimal-residual iterate
specializes it at the minimizer, where the quasi-residual is `‖γ_m‖`
(`Krylov.IsQuasiMinResIterate.norm_residual_le`). -/
theorem norm_residual_le {A : E →ₗ[𝕜] E} {z v : ℕ → E} {h : ℕ → ℕ → 𝕜}
    (hv : HessenbergRelation₂ A z v h) {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0) {m : ℕ}
    {C : ℝ} (hC : ∀ w : Fin (m + 1) → 𝕜,
      ‖∑ i, w i • v i‖ ≤ C * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖)
    (y : Fin m → 𝕜) :
    ‖b - A (x₀ + ∑ j, y j • z j)‖ ≤ C * quasiResidual h β m y := by
  rw [hv.residual_eq hr m y, quasiResidual_def]
  exact hC _

end HessenbergRelation₂

section QuasiResidual

variable (h : ℕ → ℕ → 𝕜)

/-- The minimizers of the quasi-residual are exactly the solutions of the rotated triangular
system `R_m y = g_m` (Saad, *Iterative Methods*, (6.41)–(6.43)). -/
theorem quasiResidual_isMinOn_iff (hh : ∀ i j, j + 1 < i → h i j = 0) {m : ℕ}
    (hρ : ∀ k < m, givensRho h k ≠ 0) (β : 𝕜) (y : Fin m → 𝕜) :
    IsMinOn (quasiResidual h β m) Set.univ y ↔
      (hessenbergSqOf (rotated h m) m).mulVec y = fun i : Fin m => gvec h β (i : ℕ) := by
  have hsplit : ∀ w : Fin m → 𝕜, quasiResidual h β m w ^ 2 =
      ‖(WithLp.toLp 2 ((fun i : Fin m => gvec h β (i : ℕ)) -
          (hessenbergSqOf (rotated h m) m).mulVec w) : EuclideanSpace 𝕜 (Fin m))‖ ^ 2 +
        ‖gamma h β m‖ ^ 2 := fun w => norm_sq_firstVec_sub_mulVec_eq h hh hρ β w
  constructor
  · intro hmin
    obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
      (isUnit_hessenbergSqOf_rotated_self h hh hρ) (fun i : Fin m => gvec h β (i : ℕ))
    have hw2 : quasiResidual h β m w ^ 2 = ‖gamma h β m‖ ^ 2 := by
      rw [hsplit w, hw, sub_self]
      simp
    have hle : quasiResidual h β m y ≤ quasiResidual h β m w :=
      isMinOn_iff.mp hmin w (Set.mem_univ w)
    have hD : ‖(WithLp.toLp 2 ((fun i : Fin m => gvec h β (i : ℕ)) -
        (hessenbergSqOf (rotated h m) m).mulVec y) : EuclideanSpace 𝕜 (Fin m))‖ = 0 := by
      have h1 := hsplit y
      have h2 := quasiResidual_nonneg h β m y
      have h3 := quasiResidual_nonneg h β m w
      have h4 : (0 : ℝ) ≤ ‖(WithLp.toLp 2 ((fun i : Fin m => gvec h β (i : ℕ)) -
          (hessenbergSqOf (rotated h m) m).mulVec y) : EuclideanSpace 𝕜 (Fin m))‖ := norm_nonneg _
      nlinarith
    rw [norm_eq_zero, WithLp.toLp_eq_zero] at hD
    exact (sub_eq_zero.mp hD).symm
  · intro hy
    have hy2 : quasiResidual h β m y ^ 2 = ‖gamma h β m‖ ^ 2 := by
      rw [hsplit y, hy, sub_self]
      simp
    refine isMinOn_iff.mpr fun w _ => ?_
    have h1 := hsplit w
    have h2 := quasiResidual_nonneg h β m y
    have h3 := quasiResidual_nonneg h β m w
    have h4 : (0 : ℝ) ≤ ‖(WithLp.toLp 2 ((fun i : Fin m => gvec h β (i : ℕ)) -
        (hessenbergSqOf (rotated h m) m).mulVec w) : EuclideanSpace 𝕜 (Fin m))‖ ^ 2 := sq_nonneg _
    nlinarith

/-- Saad, *Iterative Methods*, (7.18) and (6.42): the minimum value of the quasi-residual is
`‖γ_m‖`, which by `Krylov.norm_gamma_eq_prod` is `|s_0 ⋯ s_{m-1}| ‖β‖`. No basis is involved. -/
theorem quasiResidual_eq_norm_gamma (hh : ∀ i j, j + 1 < i → h i j = 0) {m : ℕ}
    (hρ : ∀ k < m, givensRho h k ≠ 0) (β : 𝕜) {y : Fin m → 𝕜}
    (hy : IsMinOn (quasiResidual h β m) Set.univ y) :
    quasiResidual h β m y = ‖gamma h β m‖ := by
  have hsol := (quasiResidual_isMinOn_iff h hh hρ β y).mp hy
  have h1 : quasiResidual h β m y ^ 2 = ‖gamma h β m‖ ^ 2 := by
    rw [quasiResidual_def, norm_sq_firstVec_sub_mulVec_eq h hh hρ β y, hsol, sub_self]
    simp
  have h2 := quasiResidual_nonneg h β m y
  have h3 := norm_nonneg (gamma h β m)
  nlinarith

end QuasiResidual

/-! ### The quasi-minimal-residual specification -/

/-- The quasi-minimal-residual specification: `x = x₀ + Z_m y` with `y` minimizing the
quasi-residual `‖β e₁ - H̄_m y‖₂`. QMR (Saad, *Iterative Methods*, Algorithm 7.4), TFQMR
(Algorithm 7.8), QGMRES and DQGMRES (Algorithms 6.12–6.13) and FGMRES (Algorithm 9.6) all satisfy
it, each for its own `z`, `v` and `h`. -/
def IsQuasiMinResIterate (z : ℕ → E) (h : ℕ → ℕ → 𝕜) (β : 𝕜) (x₀ : E) (m : ℕ) (x : E) : Prop :=
  ∃ y : Fin m → 𝕜, IsMinOn (quasiResidual h β m) Set.univ y ∧ x = x₀ + ∑ j, y j • z j

/-- The norm of a combination of an orthonormal family is the Euclidean norm of its
coefficients. -/
private theorem norm_sum_smul_eq_of_orthonormal {ι : Type*} [Fintype ι] {v : ι → E}
    (hv : Orthonormal 𝕜 v) (c : ι → 𝕜) :
    ‖∑ i, c i • v i‖ = ‖(WithLp.toLp 2 c : EuclideanSpace 𝕜 ι)‖ := by
  have hK : ((‖∑ i, c i • v i‖ : ℝ) : 𝕜) ^ 2 = ((∑ i, ‖c i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← inner_self_eq_norm_sq_to_K, sum_inner]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, hv.inner_right_fintype c i, RCLike.conj_mul]
  have hsq : ‖∑ i, c i • v i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by exact_mod_cast hK
  have hrhs : ‖(WithLp.toLp 2 c : EuclideanSpace 𝕜 ι)‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  rw [← Real.sqrt_sq (norm_nonneg (∑ i, c i • v i)),
    ← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 c : EuclideanSpace 𝕜 ι)), hsq, hrhs]

/-- Cauchy–Schwarz: a combination of vectors of norm at most `1` obeys `‖∑ w_i v_i‖ ≤ √n ‖w‖₂`
(Saad, *Iterative Methods*, (6.51) and (7.83): `‖V_{m+1}‖₂ ≤ √(m+1)` for unit basis vectors).
This is the constant `C` of `Krylov.IsQuasiMinResIterate.norm_residual_le` in the normalization
the book uses. -/
theorem norm_sum_smul_le_sqrt_mul {n : ℕ} {v : ℕ → E} (hv : ∀ i, ‖v i‖ ≤ 1) (w : Fin n → 𝕜) :
    ‖∑ i, w i • v i‖ ≤ Real.sqrt n * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin n))‖ := by
  have h1 : ‖∑ i, w i • v i‖ ≤ ∑ i, ‖w i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hv _)
  have h2 : (∑ i, ‖w i‖) ^ 2 ≤ (n : ℝ) * ∑ i, ‖w i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => ‖w i‖)
  have h3 : ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin n))‖ ^ 2 = ∑ i, ‖w i‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  have h4 : (0 : ℝ) ≤ ∑ i, ‖w i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have h5 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have h6 : (0 : ℝ) ≤ Real.sqrt n * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin n))‖ := by
    positivity
  have h8 : (∑ i, ‖w i‖) ^ 2 ≤
      (Real.sqrt n * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin n))‖) ^ 2 := by
    rw [mul_pow, h5, h3]
    exact h2
  refine h1.trans ?_
  have h9 := Real.sqrt_le_sqrt h8
  rwa [Real.sqrt_sq h4, Real.sqrt_sq h6] at h9

namespace IsQuasiMinResIterate

variable {A : E →ₗ[𝕜] E} {z v : ℕ → E} {h : ℕ → ℕ → 𝕜} {b x₀ x : E} {β : 𝕜} {m : ℕ}

/-- Saad, *Iterative Methods*, Proposition 7.3, (6.51) and (7.83): if the residual basis satisfies
`‖∑ w_i v_i‖ ≤ C ‖w‖₂` then the residual of a quasi-minimal-residual iterate is at most `C ‖γ_m‖`,
the quasi-residual norm times the conditioning of that basis. -/
theorem norm_residual_le (hv : HessenbergRelation₂ A z v h) (hr : b - A x₀ = β • v 0)
    (hρ : ∀ k < m, givensRho h k ≠ 0) {C : ℝ}
    (hC : ∀ w : Fin (m + 1) → 𝕜,
      ‖∑ i, w i • v i‖ ≤ C * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖)
    (hx : IsQuasiMinResIterate z h β x₀ m x) : ‖b - A x‖ ≤ C * ‖gamma h β m‖ := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine (hv.norm_residual_le hr hC y).trans_eq ?_
  rw [quasiResidual_eq_norm_gamma h hv.eq_zero_of_lt hρ β hy]

/-- Saad, *Iterative Methods*, Theorem 7.4 (and Theorem 6.11): if the residual basis satisfies
`c ‖w‖₂ ≤ ‖∑ w_i v_i‖ ≤ C ‖w‖₂` with `0 < c` then the quasi-minimal-residual iterate is within
the conditioning `C / c` of *every* point of the same affine space; taking that point to be the
minimal-residual iterate, `‖r^Q_m‖ ≤ κ₂(V_{m+1}) ‖r^G_m‖`. Neither a factorization of the
residual basis nor its full rank is needed. -/
theorem norm_residual_le_mul (hv : HessenbergRelation₂ A z v h) (hr : b - A x₀ = β • v 0)
    {c C : ℝ} (hc0 : 0 < c)
    (hc : ∀ w : Fin (m + 1) → 𝕜,
      c * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖ ≤ ‖∑ i, w i • v i‖)
    (hC : ∀ w : Fin (m + 1) → 𝕜,
      ‖∑ i, w i • v i‖ ≤ C * ‖(WithLp.toLp 2 w : EuclideanSpace 𝕜 (Fin (m + 1)))‖)
    (hx : IsQuasiMinResIterate z h β x₀ m x) (w : Fin m → 𝕜) :
    ‖b - A x‖ ≤ C / c * ‖b - A (x₀ + ∑ j, w j • z j)‖ := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hone : ‖(WithLp.toLp 2 (Pi.single (0 : Fin (m + 1)) (1 : 𝕜)) :
      EuclideanSpace 𝕜 (Fin (m + 1)))‖ = 1 := by
    have hsq : ‖(WithLp.toLp 2 (Pi.single (0 : Fin (m + 1)) (1 : 𝕜)) :
        EuclideanSpace 𝕜 (Fin (m + 1)))‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Pi.single_apply]
      rw [Finset.sum_eq_single (0 : Fin (m + 1))]
      · simp
      · intro j _ hj
        simp [hj]
      · intro hc; exact absurd (Finset.mem_univ _) hc
    nlinarith [norm_nonneg (WithLp.toLp 2 (Pi.single (0 : Fin (m + 1)) (1 : 𝕜)) :
      EuclideanSpace 𝕜 (Fin (m + 1)))]
  have hcC : c ≤ C := by
    have h1 := hc (Pi.single (0 : Fin (m + 1)) (1 : 𝕜))
    have h2 := hC (Pi.single (0 : Fin (m + 1)) (1 : 𝕜))
    rw [hone, mul_one] at h1 h2
    linarith
  have hC0 : 0 ≤ C := hc0.le.trans hcC
  rw [hv.residual_eq hr m y, hv.residual_eq hr m w]
  have hmin := isMinOn_iff.mp hy w (Set.mem_univ w)
  rw [quasiResidual_def, quasiResidual_def] at hmin
  refine ((hC _).trans (mul_le_mul_of_nonneg_left hmin hC0)).trans ?_
  have h9 : C * ‖(WithLp.toLp 2 (firstVec β (m + 1) - (hessenbergOf h m).mulVec w) :
      EuclideanSpace 𝕜 (Fin (m + 1)))‖ =
      C / c * (c * ‖(WithLp.toLp 2 (firstVec β (m + 1) - (hessenbergOf h m).mulVec w) :
        EuclideanSpace 𝕜 (Fin (m + 1)))‖) := by
    field_simp
  rw [h9]
  exact mul_le_mul_of_nonneg_left (hc _) (div_nonneg hC0 hc0.le)

/-- Saad, *Iterative Methods*, Proposition 9.2 (the optimality of FGMRES): with an orthonormal
residual basis `v` — the iterate basis `z` staying arbitrary — the quasi-residual *is* the
residual norm, so a quasi-minimal-residual iterate minimizes `‖b - A x‖` over
`x₀ + span {z_0, …, z_{m-1}}`. -/
theorem isMinOn_norm_residual (hv : HessenbergRelation₂ A z v h) (hr : b - A x₀ = β • v 0)
    (hon : Orthonormal 𝕜 fun i : Fin (m + 1) => v (i : ℕ))
    (hx : IsQuasiMinResIterate z h β x₀ m x) :
    IsMinRes A b x₀ (Submodule.span 𝕜 (Set.range fun j : Fin m => z (j : ℕ))) x := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hnorm : ∀ u : Fin m → 𝕜,
      ‖b - A (x₀ + ∑ j, u j • z j)‖ = quasiResidual h β m u := fun u => by
    rw [hv.residual_eq hr m u, norm_sum_smul_eq_of_orthonormal hon, quasiResidual_def]
  refine ⟨?_, fun w hw => ?_⟩
  · have hmem : ∑ j, y j • z (j : ℕ) ∈
        Submodule.span 𝕜 (Set.range fun j : Fin m => z (j : ℕ)) :=
      Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
    simpa using hmem
  · obtain ⟨c, hcw⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hw
    have hwe : w = x₀ + ∑ j, c j • z j := by
      rw [hcw]
      abel
    rw [hwe, hnorm, hnorm]
    exact isMinOn_iff.mp hy c (Set.mem_univ c)

end IsQuasiMinResIterate

/-- The Arnoldi vectors span `𝒦_m` as a `Fin m`-indexed family. -/
private theorem span_range_arnoldi_vec (A : E →ₗ[𝕜] E) (r : E) (m : ℕ) :
    Submodule.span 𝕜 (Set.range fun j : Fin m => Arnoldi.vec A r (j : ℕ)) = subspace A r m := by
  rw [← Arnoldi.span_vec A r m]
  congr 1
  ext w
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨(j : ℕ), j.isLt, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩

/-- For the Arnoldi basis — `z = v` orthonormal, `h = Arnoldi.coeff`, `m ≤ grade` — the
quasi-minimal-residual specification *is* the minimal-residual specification. This is the book's
"QGMRES coincides with GMRES when the orthogonalization is complete"
(Saad, *Iterative Methods*, §6.5.6), and it is what makes `Krylov.IsQuasiMinResIterate` a
generalization of `Krylov.IsMinResIterate` rather than a new object. -/
theorem isQuasiMinResIterate_iff_isMinResIterate {A : E →ₗ[𝕜] E} {b x₀ : E}
    [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {m : ℕ} (hm : m ≤ grade A (b - A x₀))
    (x : E) :
    IsQuasiMinResIterate (Arnoldi.vec A (b - A x₀)) (Arnoldi.coeff A (b - A x₀))
        (‖b - A x₀‖ : 𝕜) x₀ m x ↔ IsMinResIterate A b x₀ m x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (isMinResIterate_iff_isMinOn hm y).mpr hy
  · intro hx
    have hmem : x - x₀ ∈ Submodule.span 𝕜 (Set.range fun j : Fin m =>
        Arnoldi.vec A (b - A x₀) (j : ℕ)) := by
      rw [span_range_arnoldi_vec]
      exact hx.mem
    obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hmem
    have hxe : x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) (j : ℕ) := by
      rw [hy]
      abel
    rw [hxe] at hx
    exact ⟨y, (isMinResIterate_iff_isMinOn hm y).mp hx, hxe⟩

/-! ### The harmonic relations between quasi-residual norms -/

section Harmonic

variable (h : ℕ → ℕ → 𝕜)

/-- A nonzero subdiagonal coefficient makes rotation `k` nondegenerate: `ρ_k ≠ 0`. This is how the
hypothesis `∀ k < m, givensRho h k ≠ 0` of `Krylov.quasiResidual_eq_norm_gamma` and of the residual
bounds is met in practice — for the Arnoldi coefficients it is
`Krylov.givensRho_arnoldi_ne_zero`. Its natural home is `Numlib/Krylov/Hessenberg`, beside
`Krylov.givensRho_ne_zero_of_rotated_ne_zero`. -/
theorem givensRho_ne_zero_of_subdiag_ne_zero {k : ℕ} (hk : h (k + 1) k ≠ 0) :
    givensRho h k ≠ 0 := by
  intro h0
  have hsum : ‖rotated h k k k‖ ^ 2 + ‖rotated h k (k + 1) k‖ ^ 2 = 0 := by
    rw [← givensRho_sq, h0]
    ring
  obtain ⟨-, h2⟩ := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp hsum
  have hd : rotated h k (k + 1) k = 0 :=
    norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
  rw [rotated_eq_of_le h k (k + 1) k le_rfl] at hd
  exact hk hd

/-- The harmonic identity behind `Krylov.inv_sq_norm_gamma`, over the reals. -/
private theorem inv_sq_harmonic {S G C : ℝ} (hS : S ≠ 0) (hG : G ≠ 0)
    (hCS : C ^ 2 + S ^ 2 = 1) : 1 / (S * G) ^ 2 = 1 / G ^ 2 + C ^ 2 / (S * G) ^ 2 := by
  have h1 : S ^ 2 / (S * G) ^ 2 = 1 / G ^ 2 := by
    rw [mul_pow]
    field_simp
  rw [← h1, ← add_div, show S ^ 2 + C ^ 2 = 1 by linarith]

/-- Saad, *Iterative Methods*, (7.23) and (6.65), in pure Givens form: with `ρ^Q_k = ‖γ_k‖` the
quasi-residual norm and `ρ^F_{k+1} = ρ^Q_{k+1} / |c_k|` the Galerkin one,
`1/(ρ^Q_{m+1})² = 1/(ρ^Q_m)² + 1/(ρ^F_{m+1})²`. It is `|c_m|² + |s_m|² = 1` together with
`Krylov.gamma_succ`. -/
theorem inv_sq_norm_gamma (β : 𝕜) {m : ℕ} (h0 : gamma h β (m + 1) ≠ 0) :
    1 / ‖gamma h β (m + 1)‖ ^ 2 =
      1 / ‖gamma h β m‖ ^ 2 + 1 / (‖gamma h β (m + 1)‖ / ‖givensC h m‖) ^ 2 := by
  have hsucc := gamma_succ h β m
  have hs : givensS h m ≠ 0 := fun hc => by rw [hsucc, hc] at h0; simp at h0
  have hγ : gamma h β m ≠ 0 := fun hc => by rw [hsucc, hc] at h0; simp at h0
  have hρ : givensRho h m ≠ 0 := fun hc => hs (by rw [givensS, hc]; simp)
  have hcs := norm_givensC_sq_add_norm_givensS_sq h m hρ
  have hs0 : ‖givensS h m‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  have hγ0 : ‖gamma h β m‖ ≠ 0 := norm_ne_zero_iff.mpr hγ
  have hns : ‖gamma h β (m + 1)‖ = ‖givensS h m‖ * ‖gamma h β m‖ := by
    rw [hsucc, norm_mul, norm_neg]
  have hkey : 1 / ((‖givensS h m‖ * ‖gamma h β m‖) / ‖givensC h m‖) ^ 2 =
      ‖givensC h m‖ ^ 2 / (‖givensS h m‖ * ‖gamma h β m‖) ^ 2 := by
    rw [div_pow, one_div_div]
  rw [hns, hkey]
  exact inv_sq_harmonic hs0 hγ0 hcs

/-- Saad, *Iterative Methods*, (7.24) and Corollary 6.14: the quasi-residual norm is the harmonic
average `1/(ρ^Q_m)² = ∑_{i ≤ m} 1/(ρ^F_i)²` of the Galerkin ones, where `ρ^F_0 = ‖β‖` and
`ρ^F_{k+1} = ‖γ_{k+1}‖ / |c_k|`. -/
theorem inv_sq_norm_gamma_eq_sum (β : 𝕜) {ρF : ℕ → ℝ} (hρF0 : ρF 0 = ‖β‖)
    (hρF : ∀ k, ρF (k + 1) = ‖gamma h β (k + 1)‖ / ‖givensC h k‖) {m : ℕ}
    (h0 : gamma h β m ≠ 0) :
    1 / ‖gamma h β m‖ ^ 2 = ∑ i ∈ Finset.range (m + 1), 1 / ρF i ^ 2 := by
  induction m with
  | zero => simp [hρF0, gamma]
  | succ n ih =>
      have hn : gamma h β n ≠ 0 := fun hc => by rw [gamma_succ h β n, hc] at h0; simp at h0
      rw [Finset.sum_range_succ, ← ih hn, hρF n, inv_sq_norm_gamma h β h0]

/-- The Galerkin norms `ρ^F` of `Krylov.inv_sq_norm_gamma_eq_sum` are nonnegative. -/
private theorem rhoF_nonneg (β : 𝕜) {ρF : ℕ → ℝ} (hρF0 : ρF 0 = ‖β‖)
    (hρF : ∀ k, ρF (k + 1) = ‖gamma h β (k + 1)‖ / ‖givensC h k‖) (i : ℕ) : 0 ≤ ρF i := by
  cases i with
  | zero => rw [hρF0]; exact norm_nonneg _
  | succ n => rw [hρF n]; positivity

/-- Saad, *Iterative Methods*, Proposition 7.5, first half: `ρ^Q_m ≤ ρ^F_i` for every `i ≤ m` at
which the Galerkin iterate exists (`ρ^F_i ≠ 0`, that is `c_{i-1} ≠ 0`). -/
theorem norm_gamma_le (β : 𝕜) {ρF : ℕ → ℝ} (hρF0 : ρF 0 = ‖β‖)
    (hρF : ∀ k, ρF (k + 1) = ‖gamma h β (k + 1)‖ / ‖givensC h k‖) {m i : ℕ} (hi : i ≤ m)
    (h0 : gamma h β m ≠ 0) (hρi : ρF i ≠ 0) : ‖gamma h β m‖ ≤ ρF i := by
  have hsum := inv_sq_norm_gamma_eq_sum h β hρF0 hρF h0
  have hpos : 0 < ‖gamma h β m‖ := norm_pos_iff.mpr h0
  have hipos : 0 < ρF i := lt_of_le_of_ne (rhoF_nonneg h β hρF0 hρF i) (Ne.symm hρi)
  have hle : 1 / ρF i ^ 2 ≤ ∑ j ∈ Finset.range (m + 1), 1 / ρF j ^ 2 :=
    Finset.single_le_sum (f := fun j => 1 / ρF j ^ 2) (fun j _ => by positivity)
      (Finset.mem_range.mpr (by omega))
  rw [← hsum] at hle
  have h1 : ‖gamma h β m‖ ^ 2 ≤ ρF i ^ 2 := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ρF i ^ 2)
      (by positivity : (0 : ℝ) < ‖gamma h β m‖ ^ 2)] at hle
    linarith
  nlinarith

/-- Saad, *Iterative Methods*, Proposition 7.5 (the analogue of Proposition 6.15):
`min_{i ≤ m} ρ^F_i ≤ √(m+1) ρ^Q_m`, from `Krylov.inv_sq_norm_gamma_eq_sum` by bounding a sum of
`m + 1` terms below by `m + 1` times its smallest. -/
theorem exists_norm_gamma_div_givensC_le (β : 𝕜) {ρF : ℕ → ℝ} (hρF0 : ρF 0 = ‖β‖)
    (hρF : ∀ k, ρF (k + 1) = ‖gamma h β (k + 1)‖ / ‖givensC h k‖) (m : ℕ) :
    ∃ i ≤ m, ρF i ≤ Real.sqrt (m + 1) * ‖gamma h β m‖ := by
  rcases eq_or_ne (gamma h β m) 0 with h0 | h0
  · refine ⟨m, le_rfl, ?_⟩
    have hρm : ρF m = 0 := by
      cases m with
      | zero => rw [hρF0, show β = 0 from h0, norm_zero]
      | succ n => rw [hρF n, h0, norm_zero, zero_div]
    rw [hρm, h0, norm_zero, mul_zero]
  have hpos : 0 < ‖gamma h β m‖ := norm_pos_iff.mpr h0
  have hsum := inv_sq_norm_gamma_eq_sum h β hρF0 hρF h0
  by_contra hcon
  push Not at hcon
  have hlt : ∀ i ∈ Finset.range (m + 1),
      1 / ρF i ^ 2 < 1 / (((m : ℝ) + 1) * ‖gamma h β m‖ ^ 2) := by
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 := hcon i hi'
    have hsq : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hs0 : 0 ≤ Real.sqrt ((m : ℝ) + 1) * ‖gamma h β m‖ := by positivity
    have h2 : ((m : ℝ) + 1) * ‖gamma h β m‖ ^ 2 < ρF i ^ 2 := by
      nlinarith [mul_self_lt_mul_self hs0 h1, hsq]
    exact one_div_lt_one_div_of_lt (by positivity) h2
  have hkey : ∑ i ∈ Finset.range (m + 1), 1 / ρF i ^ 2
      < ∑ _i ∈ Finset.range (m + 1), 1 / (((m : ℝ) + 1) * ‖gamma h β m‖ ^ 2) :=
    Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ hlt
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hkey
  rw [← hsum] at hkey
  have heq : ((m : ℝ) + 1) * (1 / (((m : ℝ) + 1) * ‖gamma h β m‖ ^ 2)) =
      1 / ‖gamma h β m‖ ^ 2 := by
    have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  push_cast at hkey
  rw [heq] at hkey
  exact lt_irrefl _ hkey

end Harmonic

/-! ### Quasi-minimal residual smoothing -/

section Smoothing

variable (h : ℕ → ℕ → 𝕜)

/-- Rows `0, …, m` of the product of the first `m` rotations ignore the last coordinate. -/
private theorem givensQAux_mulVec_of_last {m : ℕ} (d : Fin (m + 2) → 𝕜)
    (hd : ∀ l : Fin (m + 2), (l : ℕ) ≠ m + 1 → d l = 0) (i : Fin (m + 1)) :
    (givensQAux h m (m + 1)).mulVec d i.castSucc = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) = m + 1
  · have hi := i.isLt
    have hne : i.castSucc ≠ l := by
      intro hc
      have h1 : (i : ℕ) = (l : ℕ) := by rw [← hc]; rfl
      omega
    rw [givensQAux_apply_of_lt h m (m + 1) i.castSucc l (by omega), ite_eq_right hne, zero_mul]
  · rw [hd l hl, mul_zero]

/-- The Galerkin system in rotated coordinates: if `H_{m+1} y = β e₁` then `R̃_{m+1} y` is the
truncated rotated right-hand side `(g_0, …, g_{m-1}, γ_m)`. -/
private theorem rotated_mulVec_of_mulVec_eq (hh : ∀ i j, j + 1 < i → h i j = 0) (β : 𝕜) {m : ℕ}
    {w : Fin (m + 1) → 𝕜} (hw : (hessenbergSqOf h (m + 1)).mulVec w = firstVec β (m + 1))
    (i : Fin (m + 1)) :
    (hessenbergSqOf (rotated h m) (m + 1)).mulVec w i = gvecTrunc h β m (i : ℕ) := by
  have hd' : ∀ l : Fin (m + 2), (l : ℕ) ≠ m + 1 →
      (firstVec β (m + 2) - (hessenbergOf h (m + 1)).mulVec w) l = 0 := fun l hl => by
    rw [firstVec_sub_mulVec_apply_of_mulVec_eq h hh β hw, ite_eq_right hl]
  have hsub : (hessenbergOf h (m + 1)).mulVec w =
      firstVec β (m + 2) - (firstVec β (m + 2) - (hessenbergOf h (m + 1)).mulVec w) :=
    (sub_sub_cancel _ _).symm
  rw [hessenbergSqOf_rotated_mulVec h w i, hsub, Matrix.mulVec_sub, Pi.sub_apply,
    givensQAux_mulVec_firstVec h β (m + 1) m (by omega), givensQAux_mulVec_of_last h _ hd' i,
    sub_zero]
  rfl

/-- The coordinate form of Saad, *Iterative Methods*, (7.29): the quasi-minimal-residual
coordinates at step `m + 1` are `|s_m|²` times the padded coordinates at step `m` plus `|c_m|²`
times the Galerkin coordinates. -/
private theorem coeff_eq_combination (hh : ∀ i j, j + 1 < i → h i j = 0) {m : ℕ}
    (hρ : ∀ k < m + 1, givensRho h k ≠ 0) (β : 𝕜) {y u w : Fin (m + 1) → 𝕜} {y' : Fin m → 𝕜}
    (hy : (hessenbergSqOf (rotated h (m + 1)) (m + 1)).mulVec y =
      fun i : Fin (m + 1) => gvec h β (i : ℕ))
    (hy' : (hessenbergSqOf (rotated h m) m).mulVec y' = fun i : Fin m => gvec h β (i : ℕ))
    (hw : (hessenbergSqOf h (m + 1)).mulVec w = firstVec β (m + 1))
    (huc : ∀ j : Fin m, u j.castSucc = y' j) (hul : u (Fin.last m) = 0) :
    y = ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) • u + ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) • w := by
  have hρm : givensRho h m ≠ 0 := hρ m (by omega)
  have hρm' : ((givensRho h m : ℝ) : 𝕜) ≠ 0 := by
    simpa using hρm
  have hcs := norm_givensC_sq_add_norm_givensS_sq h m hρm
  have had : ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) + ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [← RCLike.ofReal_add, show ‖givensS h m‖ ^ 2 + ‖givensC h m‖ ^ 2 = 1 by linarith,
      RCLike.ofReal_one]
  -- the padded step-`m` coordinates
  have hRu : ∀ i : Fin (m + 1), (hessenbergSqOf (rotated h (m + 1)) (m + 1)).mulVec u i =
      if (i : ℕ) < m then gvec h β (i : ℕ) else 0 := by
    intro i
    simp only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply]
    rw [Fin.sum_univ_castSucc, hul, mul_zero, add_zero]
    by_cases hi : (i : ℕ) < m
    · rw [ite_eq_left hi, ← congrFun hy' ⟨(i : ℕ), hi⟩]
      simp only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply]
      exact Finset.sum_congr rfl fun j _ => by
        rw [Fin.val_castSucc, huc j, rotated_succ_eq_of_lt h hh m (j : ℕ) j.isLt (i : ℕ)]
    · rw [ite_eq_right hi]
      refine Finset.sum_eq_zero fun j _ => ?_
      have him : (i : ℕ) = m := by have := i.isLt; omega
      rw [Fin.val_castSucc, him,
        rotated_eq_zero_of_lt h hh (m + 1) m (j : ℕ) (by omega) j.isLt, zero_mul]
  -- the Galerkin coordinates
  have hRw : ∀ i : Fin (m + 1), (hessenbergSqOf (rotated h (m + 1)) (m + 1)).mulVec w i =
      if (i : ℕ) < m then gvec h β (i : ℕ)
      else ((givensRho h m : ℝ) : 𝕜) * w (Fin.last m) := by
    intro i
    by_cases hi : (i : ℕ) < m
    · rw [ite_eq_left hi, ← gvecTrunc_of_lt h β hi, ← rotated_mulVec_of_mulVec_eq h hh β hw i]
      simp only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply]
      exact Finset.sum_congr rfl fun j _ => by
        rw [rotated_succ_apply, ite_eq_right (by omega), ite_eq_right (by omega)]
    · have him : (i : ℕ) = m := by have := i.isLt; omega
      rw [ite_eq_right hi]
      simp only [Matrix.mulVec, dotProduct, hessenbergSqOf, Matrix.of_apply]
      rw [Fin.sum_univ_castSucc]
      have hzero : ∀ j : Fin m, rotated h (m + 1) (i : ℕ) (j.castSucc : ℕ) * w j.castSucc = 0 :=
        fun j => by
          rw [Fin.val_castSucc, him,
            rotated_eq_zero_of_lt h hh (m + 1) m (j : ℕ) (by omega) j.isLt, zero_mul]
      rw [Finset.sum_congr rfl fun j _ => hzero j, Finset.sum_const_zero, zero_add, him,
        Fin.val_last, rotated_succ_self]
  -- the last rotated equation
  have hlast : ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) * (((givensRho h m : ℝ) : 𝕜) * w (Fin.last m)) =
      gvec h β m := by
    have hgam : rotated h m m m * w (Fin.last m) = gamma h β m :=
      rotated_self_mul_eq_gamma h hh β hw
    have hc : givensC h m * ((givensRho h m : ℝ) : 𝕜) = rotated h m m m := by
      rw [givensC, div_mul_cancel₀ _ hρm']
    have hconj : ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) =
        starRingEnd 𝕜 (givensC h m) * givensC h m := by
      rw [RCLike.conj_mul]
      push_cast
      ring
    rw [gvec, ← hgam, ← hc, hconj]
    ring
  refine Matrix.mulVec_injective_iff_isUnit.mpr
    (isUnit_hessenbergSqOf_rotated_self h hh hρ) ?_
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hy]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hRu i, hRw i]
  by_cases hi : (i : ℕ) < m
  · rw [ite_eq_left hi, ite_eq_left hi, ← add_mul, had, one_mul]
  · have him : (i : ℕ) = m := by have := i.isLt; omega
    rw [ite_eq_right hi, ite_eq_right hi, mul_zero, zero_add, hlast, him]

variable {h}

namespace IsQuasiMinResIterate

variable {A : E →ₗ[𝕜] E} {z v : ℕ → E} {b x₀ x x' xF : E} {β : 𝕜} {m : ℕ}

/-- Saad, *Iterative Methods*, (7.29) and (6.58): successive quasi-minimal-residual iterates are
the smoothing combinations `x^Q_{m+1} = |s_m|² x^Q_m + |c_m|² x^F_{m+1}` of the previous
quasi-minimal-residual iterate and the Galerkin iterate at the current step — the identity that
lets QMR be implemented as quasi-minimal residual smoothing of BCG. -/
theorem eq_combination (hh : ∀ i j, j + 1 < i → h i j = 0)
    (hρ : ∀ k < m + 1, givensRho h k ≠ 0) {w : Fin (m + 1) → 𝕜}
    (hx : IsQuasiMinResIterate z h β x₀ (m + 1) x) (hx' : IsQuasiMinResIterate z h β x₀ m x')
    (hw : (hessenbergSqOf h (m + 1)).mulVec w = firstVec β (m + 1))
    (hxF : xF = x₀ + ∑ j, w j • z j) :
    x = ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) • x' + ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) • xF := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hx'
  have hρ' : ∀ k < m, givensRho h k ≠ 0 := fun k hk => hρ k (by omega)
  have hcs := norm_givensC_sq_add_norm_givensS_sq h m (hρ m (by omega))
  have had : ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) + ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [← RCLike.ofReal_add, show ‖givensS h m‖ ^ 2 + ‖givensC h m‖ ^ 2 = 1 by linarith,
      RCLike.ofReal_one]
  obtain ⟨u, huc, hul⟩ : ∃ u : Fin (m + 1) → 𝕜,
      (∀ j : Fin m, u j.castSucc = y' j) ∧ u (Fin.last m) = 0 :=
    ⟨Fin.snoc y' 0, fun j => by simp, by simp⟩
  have hcomb := coeff_eq_combination h hh hρ β
    ((quasiResidual_isMinOn_iff h hh hρ β y).mp hy)
    ((quasiResidual_isMinOn_iff h hh hρ' β y').mp hy') hw huc hul
  have hsum : ∑ j, u j • z (j : ℕ) = ∑ j, y' j • z (j : ℕ) := by
    rw [Fin.sum_univ_castSucc, hul, zero_smul, add_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [huc j, Fin.val_castSucc]
  have hx0 : ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) • x₀ + ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) • x₀ = x₀ := by
    rw [← add_smul, had, one_smul]
  rw [hxF, hcomb]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul, Finset.sum_add_distrib,
    ← Finset.smul_sum, hsum, smul_add]
  conv_lhs => rw [← hx0]
  module

/-- The residual form of `Krylov.IsQuasiMinResIterate.eq_combination`
(Saad, *Iterative Methods*, (7.30) and (6.58)): `r^Q_{m+1} = |s_m|² r^Q_m + |c_m|² r^F_{m+1}`. -/
theorem residual_eq_combination (hh : ∀ i j, j + 1 < i → h i j = 0)
    (hρ : ∀ k < m + 1, givensRho h k ≠ 0) {w : Fin (m + 1) → 𝕜}
    (hx : IsQuasiMinResIterate z h β x₀ (m + 1) x) (hx' : IsQuasiMinResIterate z h β x₀ m x')
    (hw : (hessenbergSqOf h (m + 1)).mulVec w = firstVec β (m + 1))
    (hxF : xF = x₀ + ∑ j, w j • z j) :
    b - A x = ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) • (b - A x') +
      ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) • (b - A xF) := by
  have hcs := norm_givensC_sq_add_norm_givensS_sq h m (hρ m (by omega))
  have had : ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) + ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [← RCLike.ofReal_add, show ‖givensS h m‖ ^ 2 + ‖givensC h m‖ ^ 2 = 1 by linarith,
      RCLike.ofReal_one]
  have hb : ((‖givensS h m‖ ^ 2 : ℝ) : 𝕜) • b + ((‖givensC h m‖ ^ 2 : ℝ) : 𝕜) • b = b := by
    rw [← add_smul, had, one_smul]
  rw [eq_combination hh hρ hx hx' hw hxF, map_add, map_smul, map_smul, smul_sub, smul_sub]
  conv_lhs => rw [← hb]
  module

end IsQuasiMinResIterate

end Smoothing

end Krylov
