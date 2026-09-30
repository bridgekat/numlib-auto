import Numlib.Analysis.InnerProductSpace.SingularValues
import Numlib.Krylov.Decomposition
import Numlib.LinearAlgebra.Matrix.Bidiagonal

/-!
# Golub–Kahan bidiagonalization

For `A : E →ₗ[𝕜] F` between two inner product spaces and an operator `Astar : F →ₗ[𝕜] E` that is its
adjoint (`hadj : ∀ u x, ⟪Astar u, x⟫ = ⟪u, A x⟫`, a hypothesis as in
`Numlib/Krylov/NormalEquations`, so that neither completeness nor finite dimension is needed), the
Golub–Kahan process builds orthonormal `v_j ∈ E`, `u_j ∈ F` and nonnegative reals `α_j`, `β_j` with

`A v_j = α_j u_j + β_{j-1} u_{j-1}`,   `Astar u_j = α_j v_j + β_j v_{j+1}`

([golub2013matrix] §10.4.1, (10.4.2)–(10.4.3)).

## Design

**Specification first.** The vectors are *defined* as Arnoldi vectors of the two Gram operators,
`GolubKahan.rightVec A Astar v j := Arnoldi.vec (Astar ∘ₗ A) v j` and
`GolubKahan.leftVec A Astar v j := Arnoldi.vec (A ∘ₗ Astar) (A v) j`, so that (10.4.11)–(10.4.12)
are `Arnoldi.span_vec`, and `α_j := re ⟪u_j, A v_j⟫`, `β_j := re ⟪v_{j+1}, Astar u_j⟫`. The coupled
recurrences are theorems. The one idea behind them is that `A` *intertwines* the two Gram operators,
`A ∘ (Astar A) = (A Astar) ∘ A`, and so does `Astar` in the other direction; an intertwining map
carries Krylov subspaces to Krylov subspaces (`Krylov.map_subspace_of_semiconj`) and carries an
Arnoldi vector to a vector whose component along the Arnoldi vector of the same step is a
nonnegative real (`Arnoldi.inner_vec_apply_vec_of_semiconj`). Breakdown is uniform: past the grade
the vectors are `0` and every identity holds with both sides `0`.

Indices are `0`-based: `rightVec … 0 = v/‖v‖` is the book's `v_1`, `alpha … j` is `α_{j+1}`,
`beta … j` is `β_{j+1}`.

**Upper and lower are dual, not two processes.** The Paige–Saunders lower bidiagonalization of `A`
from `u ∈ F` ([golub2013matrix] Algorithm 10.4.2) *is* the Golub–Kahan process of the adjoint pair
`(Astar, A)` from `u`, and its lower bidiagonal matrix is `GolubKahan.bidiagLower`, which is already
the matrix of `Astar` in the upper process ((10.4.10)). The LSQR residual formula
`GolubKahan.residual_eq` is therefore an instance of `Krylov.HessenbergRelation₂.residual_eq`
through `GolubKahan.hessenbergRelation₂`.

**The link to Lanczos.** `B_kᵀ B_k = T_k(Aᴴ A)` (`GolubKahan.bidiag_conjTranspose_mul_bidiag`), and
the Lanczos process of the Hermitian dilation `LinearMap.hermitianDilation A Astar` from `(v, 0)`
interleaves the two families, with zero diagonal and off-diagonal `α₀, β₀, α₁, …`
(`GolubKahan.lanczos_jordanWielandt`, [golub2013matrix] §10.4.3).

**Matrix form.** For `A : Matrix m n 𝕜`, `GolubKahan.rightMatrix`/`leftMatrix` are the matrices
`V_k`, `U_k` of Lanczos vectors of `Aᴴ A` and `A Aᴴ`; (10.4.9) is `GolubKahan.mul_rightMatrix`,
(10.4.10) is `GolubKahan.conjTranspose_mul_leftMatrix`.

## Main results

* `GolubKahan.apply_rightVec_zero`, `GolubKahan.apply_rightVec`, `GolubKahan.adjoint_apply_leftVec`:
  the coupled recurrences (10.4.2)–(10.4.3).
* `GolubKahan.alpha_nonneg`, `GolubKahan.beta_nonneg` and the reality of the defining inner
  products.
* `GolubKahan.lanczos_alpha_zero`, `GolubKahan.lanczos_alpha_succ`, `GolubKahan.lanczos_beta_eq`,
  `GolubKahan.bidiag_conjTranspose_mul_bidiag`: the Lanczos coefficients of `Aᴴ A`.
* `GolubKahan.residual_eq`: the LSQR residual `b − A (x₀ + V_k y) = U_{k+1} (β e₁ − B̄_k y)`.
* `GolubKahan.lanczos_jordanWielandt`: the tridiagonal–bidiagonal connection.

## References

* [golub2013matrix] §10.4, §11.4.2.
-/

open Krylov Finset

open scoped Matrix

open LinearMap (hermitianDilation)

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The Golub–Kahan vectors and coefficients -/

namespace GolubKahan

section Operator

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (v : E)

/-- The right Golub–Kahan vectors `v_j`: the Arnoldi (Lanczos) vectors of `Astar ∘ A` from `v`; the
book's `v_{j+1}` ([golub2013matrix] Algorithm 10.4.1). -/
noncomputable def rightVec (j : ℕ) : E :=
  Arnoldi.vec (Astar ∘ₗ A) v j

/-- The left Golub–Kahan vectors `u_j`: the Arnoldi (Lanczos) vectors of `A ∘ Astar` from `A v`; the
book's `u_{j+1}`. -/
noncomputable def leftVec (j : ℕ) : F :=
  Arnoldi.vec (A ∘ₗ Astar) (A v) j

/-- The diagonal coefficient `α_j = re ⟪u_j, A v_j⟫`, the book's `α_{j+1}`. -/
noncomputable def alpha (j : ℕ) : ℝ :=
  RCLike.re (inner 𝕜 (leftVec A Astar v j) (A (rightVec A Astar v j)))

/-- The superdiagonal coefficient `β_j = re ⟪v_{j+1}, Astar u_j⟫`, the book's `β_{j+1}`. -/
noncomputable def beta (j : ℕ) : ℝ :=
  RCLike.re (inner 𝕜 (rightVec A Astar v (j + 1)) (Astar (leftVec A Astar v j)))

/-- The right vectors span the Krylov subspaces of `Aᴴ A` ([golub2013matrix] (10.4.11)). -/
theorem span_rightVec (k : ℕ) :
    Submodule.span 𝕜 (rightVec A Astar v '' Set.Iio k) = subspace (Astar ∘ₗ A) v k :=
  Arnoldi.span_vec _ _ k

/-- The left vectors span the Krylov subspaces of `A Aᴴ` from `A v` ([golub2013matrix]
(10.4.12)). -/
theorem span_leftVec (k : ℕ) :
    Submodule.span 𝕜 (leftVec A Astar v '' Set.Iio k) = subspace (A ∘ₗ Astar) (A v) k :=
  Arnoldi.span_vec _ _ k

private theorem semiconj_right : Function.Semiconj A (Astar ∘ₗ A) (A ∘ₗ Astar) := fun _ => rfl

private theorem semiconj_left : Function.Semiconj Astar (A ∘ₗ Astar) (Astar ∘ₗ A) := fun _ => rfl

private theorem eq_sum_leftVec {x : F} {m : ℕ} (hx : x ∈ subspace (A ∘ₗ Astar) (A v) m) :
    x = ∑ i ∈ range m, inner 𝕜 (leftVec A Astar v i) x • leftVec A Astar v i :=
  Arnoldi.eq_sum_inner_smul_vec _ _ hx

private theorem eq_sum_rightVec {x : E} {m : ℕ} (hx : x ∈ subspace (Astar ∘ₗ A) v m) :
    x = ∑ i ∈ range m, inner 𝕜 (rightVec A Astar v i) x • rightVec A Astar v i :=
  Arnoldi.eq_sum_inner_smul_vec _ _ hx

/-- `A v_j ∈ 𝒦_{j+1}(A Aᴴ, A v)`. -/
theorem apply_rightVec_mem (j : ℕ) :
    A (rightVec A Astar v j) ∈ subspace (A ∘ₗ Astar) (A v) (j + 1) :=
  Arnoldi.apply_vec_mem_subspace_of_semiconj (semiconj_right A Astar) (s := 0)
    (by rw [pow_zero, Module.End.one_apply]) j

/-- `Astar u_j ∈ 𝒦_{j+2}(Aᴴ A, v)`. -/
theorem adjoint_apply_leftVec_mem (j : ℕ) :
    Astar (leftVec A Astar v j) ∈ subspace (Astar ∘ₗ A) v (j + 2) :=
  Arnoldi.apply_vec_mem_subspace_of_semiconj (semiconj_left A Astar) (s := 1)
    (by rw [pow_one]; rfl) j

private theorem alpha_spec (j : ℕ) :
    0 ≤ alpha A Astar v j ∧
      inner 𝕜 (leftVec A Astar v j) (A (rightVec A Astar v j)) = (alpha A Astar v j : 𝕜) ∧
      (alpha A Astar v j = 0 → leftVec A Astar v j = 0) := by
  obtain ⟨r, hr, heq, h0⟩ := Arnoldi.inner_vec_apply_vec_of_semiconj (semiconj_right A Astar)
    (b := v) (c := A v) (s := 0) (by rw [pow_zero, Module.End.one_apply]) j
  have ha : alpha A Astar v j = r := by
    rw [alpha]
    exact (congrArg RCLike.re heq).trans (RCLike.ofReal_re r)
  rw [ha]
  exact ⟨hr, heq, h0⟩

private theorem beta_spec (j : ℕ) :
    0 ≤ beta A Astar v j ∧
      inner 𝕜 (rightVec A Astar v (j + 1)) (Astar (leftVec A Astar v j)) =
        (beta A Astar v j : 𝕜) ∧
      (beta A Astar v j = 0 → rightVec A Astar v (j + 1) = 0) := by
  obtain ⟨r, hr, heq, h0⟩ := Arnoldi.inner_vec_apply_vec_of_semiconj (semiconj_left A Astar)
    (b := A v) (c := v) (s := 1) (by rw [pow_one]; rfl) j
  have hb : beta A Astar v j = r := by
    rw [beta]
    exact (congrArg RCLike.re heq).trans (RCLike.ofReal_re r)
  rw [hb]
  exact ⟨hr, heq, h0⟩

/-- `α_j ≥ 0` ([golub2013matrix] Algorithm 10.4.1: `α_j` is a norm). -/
theorem alpha_nonneg (j : ℕ) : 0 ≤ alpha A Astar v j :=
  (alpha_spec A Astar v j).1

/-- `β_j ≥ 0` ([golub2013matrix] Algorithm 10.4.1: `β_j` is a norm). -/
theorem beta_nonneg (j : ℕ) : 0 ≤ beta A Astar v j :=
  (beta_spec A Astar v j).1

/-- The inner product defining `α_j` is real: `⟪u_j, A v_j⟫ = α_j`. -/
theorem inner_leftVec_apply_rightVec (j : ℕ) :
    inner 𝕜 (leftVec A Astar v j) (A (rightVec A Astar v j)) = (alpha A Astar v j : 𝕜) :=
  (alpha_spec A Astar v j).2.1

/-- The inner product defining `β_j` is real: `⟪v_{j+1}, Astar u_j⟫ = β_j`. -/
theorem inner_rightVec_adjoint_apply_leftVec (j : ℕ) :
    inner 𝕜 (rightVec A Astar v (j + 1)) (Astar (leftVec A Astar v j)) = (beta A Astar v j : 𝕜) :=
  (beta_spec A Astar v j).2.1

/-- A vanishing `α_j` means that the left process has broken down: `u_j = 0`. -/
theorem leftVec_eq_zero_of_alpha_eq_zero {j : ℕ} (h : alpha A Astar v j = 0) :
    leftVec A Astar v j = 0 :=
  (alpha_spec A Astar v j).2.2 h

/-- A vanishing `β_j` means that the right process has broken down: `v_{j+1} = 0`. -/
theorem rightVec_eq_zero_of_beta_eq_zero {j : ℕ} (h : beta A Astar v j = 0) :
    rightVec A Astar v (j + 1) = 0 :=
  (beta_spec A Astar v j).2.2 h

private theorem inner_leftVec_apply_rightVec_of_lt {i j : ℕ} (h : j < i) :
    inner 𝕜 (leftVec A Astar v i) (A (rightVec A Astar v j)) = 0 :=
  Submodule.inner_left_of_mem_orthogonal
    (subspace_mono (A ∘ₗ Astar) (A v) (by omega : j + 1 ≤ i) (apply_rightVec_mem A Astar v j))
    (Arnoldi.vec_mem_orthogonal _ _ i)

private theorem inner_rightVec_adjoint_apply_leftVec_of_lt {i j : ℕ} (h : j + 1 < i) :
    inner 𝕜 (rightVec A Astar v i) (Astar (leftVec A Astar v j)) = 0 :=
  Submodule.inner_left_of_mem_orthogonal
    (subspace_mono (Astar ∘ₗ A) v (by omega : j + 2 ≤ i) (adjoint_apply_leftVec_mem A Astar v j))
    (Arnoldi.vec_mem_orthogonal _ _ i)

/-- The first step of (10.4.2): `A v_0 = α_0 u_0`. -/
theorem apply_rightVec_zero :
    A (rightVec A Astar v 0) = (alpha A Astar v 0 : 𝕜) • leftVec A Astar v 0 := by
  refine (eq_sum_leftVec A Astar v (apply_rightVec_mem A Astar v 0)).trans ?_
  rw [sum_range_one, inner_leftVec_apply_rightVec]

/-! ### The bidiagonal matrices -/

/-- The upper bidiagonal `k × k` matrix `B_k` of [golub2013matrix] (10.4.8): `α_j` on the diagonal,
`β_j` at `(j, j + 1)`. -/
noncomputable def bidiag (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then alpha A Astar v i else if (i : ℕ) + 1 = j then beta A Astar v i else 0

/-- The lower bidiagonal `(k + 1) × k` matrix: `α_j` at `(j, j)`, `β_j` at `(j + 1, j)`. It is the
matrix of `Astar` in (10.4.10), `Aᴴ U_k = V_{k+1} B̄_k`, and — for the adjoint pair `(Astar, A)` —
the Paige–Saunders matrix `B(1:k+1, 1:k)` of [golub2013matrix] (10.4.18)–(10.4.19). Its first `k`
rows are `(bidiag k)ᵀ` (`GolubKahan.bidiagLower_submatrix_castSucc`). -/
noncomputable def bidiagLower (k : ℕ) : Matrix (Fin (k + 1)) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then alpha A Astar v j else if (i : ℕ) = j + 1 then beta A Astar v j else 0

/-- Entrywise description of `B_k`. -/
theorem bidiag_apply {k : ℕ} (i j : Fin k) :
    bidiag A Astar v k i j =
      if (i : ℕ) = j then alpha A Astar v i else if (i : ℕ) + 1 = j then beta A Astar v i
      else 0 :=
  rfl

/-- Entrywise description of `B̄_k`. -/
theorem bidiagLower_apply {k : ℕ} (i : Fin (k + 1)) (j : Fin k) :
    bidiagLower A Astar v k i j =
      if (i : ℕ) = j then alpha A Astar v j else if (i : ℕ) = j + 1 then beta A Astar v j else 0 :=
  rfl

/-- `B_k` is upper bidiagonal. -/
theorem bidiag_isUpperBidiagonal (k : ℕ) : (bidiag A Astar v k).IsUpperBidiagonal := by
  intro i j h
  have h' : (j : ℕ) < i ∨ (i : ℕ) + 1 < j := by
    rcases h with h | ⟨l, hil, hlj⟩
    · exact Or.inl (Fin.lt_def.1 h)
    · exact Or.inr (by rw [Fin.lt_def] at hil hlj; omega)
  rw [bidiag_apply]
  split_ifs <;> first | rfl | omega

/-- `B̄_k` is lower bidiagonal in the rectangular sense. -/
theorem bidiagLower_isLowerBidiagonalRect (k : ℕ) :
    (bidiagLower A Astar v k).IsLowerBidiagonalRect := by
  intro i j h1 h2
  rw [bidiagLower_apply, ite_eq_right h1, ite_eq_right h2]

/-- The first `k` rows of `B̄_k` are `B_kᵀ`. -/
theorem bidiagLower_submatrix_castSucc (k : ℕ) :
    (bidiagLower A Astar v k).submatrix Fin.castSucc id = (bidiag A Astar v k)ᵀ := by
  ext i j
  simp only [Matrix.submatrix_apply, id, Matrix.transpose_apply, bidiagLower_apply, bidiag_apply,
    Fin.val_castSucc]
  split_ifs <;> first | rfl | omega

/-! ### The Lanczos vectors of the Jordan–Wielandt operator (preliminaries) -/

private theorem hermitianDilation_toLp (a : E) (b : F) :
    hermitianDilation A Astar (WithLp.toLp 2 (a, b)) = WithLp.toLp 2 (Astar b, A a) :=
  rfl

private theorem norm_toLp_fst (a : E) :
    ‖(WithLp.toLp 2 (a, (0 : F)) : WithLp 2 (E × F))‖ = ‖a‖ := by
  rw [WithLp.prod_norm_eq_of_L2]
  simp [Real.sqrt_sq (norm_nonneg a)]

private theorem norm_toLp_snd (a : F) :
    ‖(WithLp.toLp 2 ((0 : E), a) : WithLp 2 (E × F))‖ = ‖a‖ := by
  rw [WithLp.prod_norm_eq_of_L2]
  simp [Real.sqrt_sq (norm_nonneg a)]

/-- `‖c x‖ = c` for a real `c ≥ 0` and a vector `x` that is a unit vector unless it is `0`, in which
case `c = 0`: the norm of an Arnoldi vector times its leading coefficient. -/
private theorem norm_ofReal_smul_eq {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {c : ℝ} (hc : 0 ≤ c) {x : G} (h0 : x = 0 → c = 0) (h1 : x ≠ 0 → ‖x‖ = 1) :
    ‖(c : 𝕜) • x‖ = c := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero, norm_zero, h0 rfl]
  · rw [norm_smul, h1 hx, mul_one, RCLike.norm_ofReal, abs_of_nonneg hc]

/-- Normalizing `c x` gives back `x` when `c ≥ 0` is real, `c = 0` forces `x = 0`, and `x` is a
unit vector unless it is `0`. -/
private theorem inv_norm_smul_smul {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {c : ℝ} (hc : 0 ≤ c) {x : G} (h0 : c = 0 → x = 0) (h1 : x ≠ 0 → ‖x‖ = 1) :
    (‖(c : 𝕜) • x‖ : 𝕜)⁻¹ • ((c : 𝕜) • x) = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hc0 : c ≠ 0 := fun h => hx (h0 h)
  rw [norm_smul, h1 hx, mul_one, RCLike.norm_ofReal, abs_of_nonneg hc, smul_smul,
    inv_mul_cancel₀ (RCLike.ofReal_ne_zero.2 hc0), one_smul]

/-- The interleaved family `(v_0, 0), (0, u_0), (v_1, 0), (0, u_1), …`. -/
private noncomputable def dilVec (l : ℕ) : WithLp 2 (E × F) :=
  if l % 2 = 0 then WithLp.toLp 2 (rightVec A Astar v (l / 2), 0)
  else WithLp.toLp 2 (0, leftVec A Astar v (l / 2))

private theorem dilVec_two_mul (j : ℕ) :
    dilVec A Astar v (2 * j) = WithLp.toLp 2 (rightVec A Astar v j, 0) := by
  simp [dilVec]

private theorem dilVec_two_mul_add_one (j : ℕ) :
    dilVec A Astar v (2 * j + 1) = WithLp.toLp 2 (0, leftVec A Astar v j) := by
  simp [dilVec, show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]

/-- The unnormalized next vector of the dilation's Lanczos process: `(0, α_j u_j)` after an even
step, `(β_j v_{j+1}, 0)` after an odd one. -/
private noncomputable def dilW (l : ℕ) : WithLp 2 (E × F) :=
  if l % 2 = 0 then WithLp.toLp 2 (0, (alpha A Astar v (l / 2) : 𝕜) • leftVec A Astar v (l / 2))
  else WithLp.toLp 2 ((beta A Astar v (l / 2) : 𝕜) • rightVec A Astar v (l / 2 + 1), 0)

private theorem dilW_two_mul (j : ℕ) :
    dilW A Astar v (2 * j) =
      WithLp.toLp 2 (0, (alpha A Astar v j : 𝕜) • leftVec A Astar v j) := by
  simp [dilW]

private theorem dilW_two_mul_add_one (j : ℕ) :
    dilW A Astar v (2 * j + 1) =
      WithLp.toLp 2 ((beta A Astar v j : 𝕜) • rightVec A Astar v (j + 1), 0) := by
  simp [dilW, show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]

/-- The candidate `w_i` is orthogonal to the interleaved vectors up to `i`. -/
private theorem inner_dilVec_dilW {l i : ℕ} (hl : l ≤ i) :
    inner 𝕜 (dilVec A Astar v l) (dilW A Astar v i) = 0 := by
  obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' l <;> obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
  · simp [dilVec_two_mul, dilW_two_mul]
  · have h0 : inner 𝕜 (rightVec A Astar v a) (rightVec A Astar v (j + 1)) = 0 :=
      Arnoldi.inner_vec_eq_zero _ _ (by omega)
    simp [dilVec_two_mul, dilW_two_mul_add_one, inner_smul_right, h0]
  · have h0 : inner 𝕜 (leftVec A Astar v a) (leftVec A Astar v j) = 0 :=
      Arnoldi.inner_vec_eq_zero _ _ (by omega)
    simp [dilVec_two_mul_add_one, dilW_two_mul, inner_smul_right, h0]
  · simp [dilVec_two_mul_add_one, dilW_two_mul_add_one]

private theorem vec_zero_hermitianDilation :
    Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) 0 = dilVec A Astar v 0 := by
  rw [show dilVec A Astar v 0 = WithLp.toLp 2 (rightVec A Astar v 0, 0) from
    dilVec_two_mul A Astar v 0]
  rcases eq_or_ne v 0 with rfl | hv
  · have h0 : ∀ {G : Type _} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] (T : G →ₗ[𝕜] G),
        Arnoldi.vec T 0 0 = 0 := fun T =>
      (Arnoldi.vec_eq_zero_iff_pow_apply_mem T 0 0).2 (by simp)
    have hz : (WithLp.toLp 2 ((0 : E), (0 : F)) : WithLp 2 (E × F)) = 0 := by
      rw [Prod.mk_zero_zero, WithLp.toLp_zero]
    rw [rightVec, h0 (Astar ∘ₗ A), hz]
    exact (Arnoldi.vec_eq_zero_iff_pow_apply_mem _ 0 0).2 (by simp)
  · have hz : (WithLp.toLp 2 (v, (0 : F)) : WithLp 2 (E × F)) ≠ 0 := fun h =>
      hv (by simpa using congrArg (fun z : WithLp 2 (E × F) => (WithLp.ofLp z).1) h)
    rw [Arnoldi.vec_zero _ _ hz, rightVec, Arnoldi.vec_zero _ _ hv, norm_toLp_fst,
      ← WithLp.toLp_smul, Prod.smul_mk, smul_zero]

/-- One step of the classical Arnoldi recurrence, when the image splits as a part orthogonal to the
current Krylov subspace plus a part inside it: the orthogonal part is `w_i`. -/
private theorem w_eq_of_apply_eq_add {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {T : G →ₗ[𝕜] G} {b x y : G} {i : ℕ}
    (h : T (Arnoldi.vec T b i) = x + y) (hx : x ∈ (subspace T b (i + 1))ᗮ)
    (hy : y ∈ subspace T b (i + 1)) :
    Arnoldi.w T b i = x := by
  rw [Arnoldi.w_eq_sub_starProjection, h, map_add,
    (Submodule.starProjection_apply_eq_zero_iff (K := subspace T b (i + 1))).2 hx,
    Submodule.starProjection_eq_self_iff.2 hy]
  abel

/-! ### The grades of the two families -/

/-- **Rank–nullity for the two Krylov spaces**: `A` maps `𝒦_∞(Aᴴ A, v)` onto `𝒦_∞(A Aᴴ, A v)`, so
`grade (A Aᴴ) (A v) + dim (𝒦_∞(Aᴴ A, v) ⊓ ker A) = grade (Aᴴ A) v`. -/
theorem grade_comp_adjoint_add_finrank [FiniteDimensional 𝕜 (fullSubspace (Astar ∘ₗ A) v)] :
    grade (A ∘ₗ Astar) (A v) +
        Module.finrank 𝕜 ↥(fullSubspace (Astar ∘ₗ A) v ⊓ LinearMap.ker A) =
      grade (Astar ∘ₗ A) v := by
  have hmap : (fullSubspace (Astar ∘ₗ A) v).map A = fullSubspace (A ∘ₗ Astar) (A v) :=
    map_fullSubspace_of_semiconj (semiconj_right A Astar) v
  have h := LinearMap.finrank_range_add_finrank_ker (A.domRestrict (fullSubspace (Astar ∘ₗ A) v))
  rw [LinearMap.range_domRestrict, hmap, LinearMap.ker_domRestrict] at h
  have hk : Module.finrank 𝕜 ↥((LinearMap.ker A).comap (fullSubspace (Astar ∘ₗ A) v).subtype) =
      Module.finrank 𝕜 ↥(fullSubspace (Astar ∘ₗ A) v ⊓ LinearMap.ker A) := by
    rw [← Submodule.map_comap_subtype]
    exact ((fullSubspace (Astar ∘ₗ A) v).equivSubtypeMap _).finrank_eq
  unfold grade
  rw [← hk]
  exact h

variable {A Astar} (hadj : ∀ u x, inner 𝕜 (Astar u) x = inner 𝕜 u (A x))
include hadj

/-- The adjoint relation read the other way: `⟪A x, u⟫ = ⟪x, Astar u⟫`, the hypothesis `hadj` of the
pair `(Astar, A)`. -/
theorem inner_apply_eq_inner_adjoint_apply (x : E) (u : F) :
    inner 𝕜 (A x) u = inner 𝕜 x (Astar u) := by
  rw [← inner_conj_symm, ← hadj, inner_conj_symm]

private theorem inner_leftVec_apply_rightVec_of_add_two_le {i j : ℕ} (h : i + 2 ≤ j) :
    inner 𝕜 (leftVec A Astar v i) (A (rightVec A Astar v j)) = 0 := by
  rw [← hadj]
  exact Submodule.inner_right_of_mem_orthogonal
    (subspace_mono (Astar ∘ₗ A) v h (adjoint_apply_leftVec_mem A Astar v i))
    (Arnoldi.vec_mem_orthogonal _ _ j)

private theorem inner_rightVec_adjoint_apply_leftVec_of_gt {i j : ℕ} (h : i < j) :
    inner 𝕜 (rightVec A Astar v i) (Astar (leftVec A Astar v j)) = 0 := by
  have h0 : inner 𝕜 (leftVec A Astar v j) (A (rightVec A Astar v i)) = 0 :=
    Submodule.inner_left_of_mem_orthogonal
      (subspace_mono (A ∘ₗ Astar) (A v) (by omega : i + 1 ≤ j) (apply_rightVec_mem A Astar v i))
      (Arnoldi.vec_mem_orthogonal _ _ j)
  rw [← inner_conj_symm, hadj, h0, map_zero]

/-- `⟪u_j, A v_{j+1}⟫ = β_j`. -/
theorem inner_leftVec_apply_rightVec_succ (j : ℕ) :
    inner 𝕜 (leftVec A Astar v j) (A (rightVec A Astar v (j + 1))) = (beta A Astar v j : 𝕜) := by
  rw [← hadj, ← inner_conj_symm, inner_rightVec_adjoint_apply_leftVec, RCLike.conj_ofReal]

/-- `⟪v_j, Astar u_j⟫ = α_j`. -/
theorem inner_rightVec_adjoint_apply_leftVec_self (j : ℕ) :
    inner 𝕜 (rightVec A Astar v j) (Astar (leftVec A Astar v j)) = (alpha A Astar v j : 𝕜) := by
  rw [← inner_conj_symm, hadj, inner_leftVec_apply_rightVec, RCLike.conj_ofReal]

/-- The recurrence (10.4.2) of [golub2013matrix] (`0`-based):
`A v_{j+1} = β_j u_j + α_{j+1} u_{j+1}`. -/
theorem apply_rightVec (j : ℕ) :
    A (rightVec A Astar v (j + 1)) =
      (beta A Astar v j : 𝕜) • leftVec A Astar v j +
        (alpha A Astar v (j + 1) : 𝕜) • leftVec A Astar v (j + 1) := by
  refine (eq_sum_leftVec A Astar v (apply_rightVec_mem A Astar v (j + 1))).trans ?_
  rw [sum_range_succ, sum_range_succ, sum_eq_zero fun i hi => by
      rw [inner_leftVec_apply_rightVec_of_add_two_le v hadj (by simp at hi; omega), zero_smul],
    zero_add, inner_leftVec_apply_rightVec_succ v hadj, inner_leftVec_apply_rightVec]

/-- The recurrence (10.4.3) of [golub2013matrix] (`0`-based):
`Astar u_j = α_j v_j + β_j v_{j+1}`. -/
theorem adjoint_apply_leftVec (j : ℕ) :
    Astar (leftVec A Astar v j) =
      (alpha A Astar v j : 𝕜) • rightVec A Astar v j +
        (beta A Astar v j : 𝕜) • rightVec A Astar v (j + 1) := by
  refine (eq_sum_rightVec A Astar v (adjoint_apply_leftVec_mem A Astar v j)).trans ?_
  rw [show j + 2 = j + 1 + 1 from rfl, sum_range_succ, sum_range_succ, sum_eq_zero fun i hi => by
      rw [inner_rightVec_adjoint_apply_leftVec_of_gt v hadj (by simp at hi; omega), zero_smul],
    zero_add, inner_rightVec_adjoint_apply_leftVec_self v hadj,
    inner_rightVec_adjoint_apply_leftVec]

/-! ### The link to the Lanczos process of `Aᴴ A` -/

/-- `⟪v_i, (Aᴴ A) v_j⟫ = ⟪A v_i, A v_j⟫`. -/
private theorem inner_rightVec_comp_apply (i j : ℕ) :
    inner 𝕜 (rightVec A Astar v i) ((Astar ∘ₗ A) (rightVec A Astar v j)) =
      inner 𝕜 (A (rightVec A Astar v i)) (A (rightVec A Astar v j)) := by
  rw [LinearMap.comp_apply, inner_apply_eq_inner_adjoint_apply hadj]

/-- The first diagonal Lanczos coefficient of `Aᴴ A`: `α₀(Aᴴ A) = α₀²` ([golub2013matrix] the remark
after (10.4.12)). -/
theorem lanczos_alpha_zero : Lanczos.alpha (Astar ∘ₗ A) v 0 = alpha A Astar v 0 ^ 2 := by
  have key : inner 𝕜 (A (rightVec A Astar v 0)) (A (rightVec A Astar v 0)) =
      ((alpha A Astar v 0 ^ 2 : ℝ) : 𝕜) := by
    nth_rewrite 2 [apply_rightVec_zero]
    rw [inner_smul_right, ← inner_conj_symm, inner_leftVec_apply_rightVec, RCLike.conj_ofReal]
    push_cast
    ring
  rw [Lanczos.alpha, Arnoldi.coeff]
  change RCLike.re (inner 𝕜 (rightVec A Astar v 0) ((Astar ∘ₗ A) (rightVec A Astar v 0))) = _
  rw [inner_rightVec_comp_apply v hadj, key, RCLike.ofReal_re]

/-- The later diagonal Lanczos coefficients of `Aᴴ A`: `α_{j+1}(Aᴴ A) = α_{j+1}² + β_j²`. -/
theorem lanczos_alpha_succ (j : ℕ) :
    Lanczos.alpha (Astar ∘ₗ A) v (j + 1) = alpha A Astar v (j + 1) ^ 2 + beta A Astar v j ^ 2 := by
  have key : inner 𝕜 (A (rightVec A Astar v (j + 1))) (A (rightVec A Astar v (j + 1))) =
      ((alpha A Astar v (j + 1) ^ 2 + beta A Astar v j ^ 2 : ℝ) : 𝕜) := by
    nth_rewrite 2 [apply_rightVec v hadj]
    rw [inner_add_right, inner_smul_right, inner_smul_right, ← inner_conj_symm,
      inner_leftVec_apply_rightVec_succ v hadj, ← inner_conj_symm (A _) (leftVec A Astar v (j + 1)),
      inner_leftVec_apply_rightVec, RCLike.conj_ofReal, RCLike.conj_ofReal]
    push_cast
    ring
  rw [Lanczos.alpha, Arnoldi.coeff]
  change RCLike.re (inner 𝕜 (rightVec A Astar v (j + 1))
    ((Astar ∘ₗ A) (rightVec A Astar v (j + 1)))) = _
  rw [inner_rightVec_comp_apply v hadj, key, RCLike.ofReal_re]

/-- The off-diagonal Lanczos coefficients of `Aᴴ A`: `β_j(Aᴴ A) = α_j β_j`. -/
theorem lanczos_beta_eq (j : ℕ) :
    Lanczos.beta (Astar ∘ₗ A) v j = alpha A Astar v j * beta A Astar v j := by
  have key : inner 𝕜 (A (rightVec A Astar v (j + 1))) (A (rightVec A Astar v j)) =
      ((alpha A Astar v j * beta A Astar v j : ℝ) : 𝕜) := by
    rw [apply_rightVec v hadj, inner_add_left, inner_smul_left, inner_smul_left,
      inner_leftVec_apply_rightVec, inner_leftVec_apply_rightVec_of_lt A Astar v j.lt_succ_self,
      RCLike.conj_ofReal]
    push_cast
    ring
  refine RCLike.ofReal_injective (K := 𝕜) ?_
  rw [Lanczos.coe_beta, Arnoldi.coeff]
  change inner 𝕜 (rightVec A Astar v (j + 1)) ((Astar ∘ₗ A) (rightVec A Astar v j)) = _
  rw [inner_rightVec_comp_apply v hadj, key]

/-- `B_kᴴ B_k = B_kᵀ B_k = T_k(Aᴴ A)` (`B_k` is real): the bidiagonal process is the Lanczos
process of `Aᴴ A` with the
tridiagonal matrix factored ([golub2013matrix] the remark after (10.4.12)). -/
theorem bidiag_conjTranspose_mul_bidiag (k : ℕ) :
    (bidiag A Astar v k)ᴴ * bidiag A Astar v k = Lanczos.tridiag (Astar ∘ₗ A) v k := by
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  rw [Matrix.mul_apply, Lanczos.tridiag_apply]
  simp only [Matrix.transpose_apply, bidiag_apply]
  rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
  · rw [ite_eq_right hij.ne]
    by_cases h1 : (i : ℕ) + 1 = j
    · rw [ite_eq_left h1, lanczos_beta_eq v hadj, Fintype.sum_eq_single i]
      · rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left h1]
      · intro l hl
        have hl' : (l : ℕ) ≠ i := fun h => hl (Fin.ext h)
        split_ifs <;> first | rfl | omega | ring
    · rw [ite_eq_right h1, ite_eq_right (by omega)]
      refine Fintype.sum_eq_zero _ fun l => ?_
      split_ifs <;> first | rfl | omega | ring
  · have hij' : i = j := Fin.ext hij
    subst hij'
    rw [ite_eq_left rfl]
    rcases Nat.eq_zero_or_eq_succ_pred (i : ℕ) with h0 | hs
    · rw [Fintype.sum_eq_single i, h0, lanczos_alpha_zero v hadj]
      · simp only [ite_eq_left]
        simp [sq]
      · intro l hl
        have hl' : (l : ℕ) ≠ i := fun h => hl (Fin.ext h)
        split_ifs <;> first | rfl | omega | ring
    · have hp : (i : ℕ) - 1 < k := by omega
      rw [Fintype.sum_eq_add i ⟨(i : ℕ) - 1, hp⟩ (fun h => by
          have := congrArg Fin.val h; simp at this; omega) (fun l hl => by
          have h1 : (l : ℕ) ≠ i := fun h => hl.1 (Fin.ext h)
          have h2 : (l : ℕ) ≠ (i : ℕ) - 1 := fun h => hl.2 (Fin.ext h)
          split_ifs <;> first | rfl | omega | ring)]
      have hL : Lanczos.alpha (Astar ∘ₗ A) v i =
          alpha A Astar v i ^ 2 + beta A Astar v ((i : ℕ) - 1) ^ 2 := by
        obtain ⟨i', hi'⟩ : ∃ i', (i : ℕ) = i' + 1 := ⟨(i : ℕ) - 1, by omega⟩
        rw [hi', lanczos_alpha_succ v hadj, Nat.add_sub_cancel]
      rw [hL]
      dsimp only
      split_ifs <;> first | omega | ring
  · rw [ite_eq_right hij.ne', ite_eq_right (by omega)]
    by_cases h1 : (j : ℕ) + 1 = i
    · rw [ite_eq_left h1, lanczos_beta_eq v hadj, Fintype.sum_eq_single j]
      · rw [ite_eq_right (by omega), ite_eq_left h1, ite_eq_left rfl]
        ring
      · intro l hl
        have hl' : (l : ℕ) ≠ j := fun h => hl (Fin.ext h)
        split_ifs <;> first | rfl | omega | ring
    · rw [ite_eq_right h1]
      refine Fintype.sum_eq_zero _ fun l => ?_
      split_ifs <;> first | rfl | omega | ring

/-! ### The bidiagonal relation of `Astar` as a Hessenberg relation, and the LSQR residual -/

/-- The recurrence (10.4.3) as a two-family Hessenberg relation `Krylov.HessenbergRelation₂` for
`Astar`, from the left vectors to the right vectors, with the lower bidiagonal coefficients of
`GolubKahan.bidiagLower`. -/
theorem hessenbergRelation₂ :
    HessenbergRelation₂ Astar (leftVec A Astar v) (rightVec A Astar v) fun i j =>
      ((if i = j then alpha A Astar v j else if i = j + 1 then beta A Astar v j else 0 : ℝ) :
        𝕜) := by
  refine ⟨fun j => ?_, fun i j h => ?_⟩
  · rw [adjoint_apply_leftVec v hadj, show j + 2 = j + 1 + 1 from rfl, sum_range_succ,
      sum_range_succ, sum_eq_zero, zero_add]
    · simp
    · intro i hi
      have : i < j := by simpa using hi
      rw [ite_eq_right (by omega), ite_eq_right (by omega), RCLike.ofReal_zero, zero_smul]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), RCLike.ofReal_zero]

/-- The kernel of `A` meets `𝒦_∞(Aᴴ A, v)` in at most a line: an element `x = c v + Aᴴ y` of it with
`⟪v, x⟫ = 0` has `‖x‖² = c̄ ⟪v, x⟫‾ + ⟪y, A x⟫‾ = 0`, so `x ↦ ⟪v, x⟫` is injective on it. -/
theorem finrank_fullSubspace_inf_ker_le_one :
    Module.finrank 𝕜 ↥(fullSubspace (Astar ∘ₗ A) v ⊓ LinearMap.ker A) ≤ 1 := by
  set S := fullSubspace (Astar ∘ₗ A) v ⊓ LinearMap.ker A
  have hle : fullSubspace (Astar ∘ₗ A) v ≤ (𝕜 ∙ v) ⊔ LinearMap.range Astar := by
    rw [fullSubspace, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    cases i with
    | zero => exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
    | succ i =>
      refine Submodule.mem_sup_right ⟨A (((Astar ∘ₗ A) ^ i) v), ?_⟩
      change Astar (A (((Astar ∘ₗ A) ^ i) v)) = ((Astar ∘ₗ A) ^ (i + 1)) v
      rw [pow_succ', Module.End.mul_apply]
      rfl
  let f : S →ₗ[𝕜] 𝕜 := (innerₛₗ 𝕜 v).comp S.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hxK, hxA⟩ hx
    rw [LinearMap.mem_ker] at hx
    have hxA' : A x = 0 := hxA
    change inner 𝕜 v x = 0 at hx
    suffices hx0 : x = 0 from Subtype.ext hx0
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hle hxK)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hz
    have e1 : inner 𝕜 x v = 0 := by rw [← inner_conj_symm, hx, map_zero]
    have e2 : inner 𝕜 x (Astar w) = 0 := by
      rw [← inner_conj_symm, hadj, hxA', inner_zero_right, map_zero]
    have hxx : inner 𝕜 x x = 0 := by
      nth_rewrite 2 [← hyz]
      rw [inner_add_right, inner_smul_right, e1, e2, mul_zero, add_zero]
    exact inner_self_eq_zero.1 hxx
  calc Module.finrank 𝕜 S ≤ Module.finrank 𝕜 𝕜 := LinearMap.finrank_le_finrank_of_injective hf
    _ = 1 := Module.finrank_self 𝕜

/-- The grades of the two Golub–Kahan families differ by at most one: `grade (A Aᴴ) (A v)` is
`grade (Aᴴ A) v` or one less, the second exactly when `ker A` meets `𝒦_∞(Aᴴ A, v)`. This is what
makes the breakdown statements "if `α_k = 0` … if `β_k = 0`" of [golub2013matrix] §10.4.1 line
up. -/
theorem grade_comp_adjoint [FiniteDimensional 𝕜 (fullSubspace (Astar ∘ₗ A) v)] :
    grade (A ∘ₗ Astar) (A v) = grade (Astar ∘ₗ A) v ∨
      grade (A ∘ₗ Astar) (A v) + 1 = grade (Astar ∘ₗ A) v := by
  have h1 := grade_comp_adjoint_add_finrank A Astar v
  have h2 := finrank_fullSubspace_inf_ker_le_one v hadj
  omega

omit hadj in
private theorem map_bidiagLower_eq_hessenbergOf (k : ℕ) :
    (bidiagLower A Astar v k).map (algebraMap ℝ 𝕜) =
      hessenbergOf (fun i j =>
        ((if i = j then alpha A Astar v j else if i = j + 1 then beta A Astar v j else 0 : ℝ) : 𝕜))
        k := by
  ext i j
  simp only [Matrix.map_apply, bidiagLower_apply, hessenbergOf, Matrix.of_apply,
    RCLike.algebraMap_eq_ofReal]

/-- **The LSQR residual** ([golub2013matrix] §11.4.2, from the lower bidiagonalization (10.4.19)).
The Paige–Saunders process of `A` from a unit vector `u ∈ F` is the Golub–Kahan process of the pair
`(Astar, A)`: its `u_j` are `rightVec Astar A u j ∈ F`, its `v_j` are `leftVec Astar A u j ∈ E`, and
its `(k + 1) × k` lower bidiagonal matrix is `bidiagLower Astar A u k`. If `b − A x₀ = β u`, the
residual of `x₀ + V_k y` is `U_{k+1} (β e₁ − B̄_k y)`. An instance of
`Krylov.HessenbergRelation₂.residual_eq`. -/
theorem residual_eq {u : F} (hu : ‖u‖ = 1) {b : F} {x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • u)
    (k : ℕ) (y : Fin k → 𝕜) :
    b - A (x₀ + ∑ j, y j • leftVec Astar A u j) =
      ∑ i : Fin (k + 1), (firstVec β (k + 1) -
        ((bidiagLower Astar A u k).map (algebraMap ℝ 𝕜)) *ᵥ y) i • rightVec Astar A u i := by
  have hrel := hessenbergRelation₂ (A := Astar) (Astar := A) u
    (inner_apply_eq_inner_adjoint_apply hadj)
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have h0 : rightVec Astar A u 0 = u := by
    rw [rightVec, Arnoldi.vec_zero _ _ hu0, hu]
    simp
  rw [map_bidiagLower_eq_hessenbergOf]
  exact hrel.residual_eq (by rw [h0]; exact hr) k y

/-! ### The Lanczos process of the Jordan–Wielandt operator -/

/-- The induction step: if the first `i + 1` Lanczos vectors of the dilation are the interleaved
ones, then `w_i` is `dilW i`. -/
private theorem w_hermitianDilation_of_forall {i : ℕ}
    (ih : ∀ l ≤ i, Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) l =
      dilVec A Astar v l) :
    Arnoldi.w (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) i = dilW A Astar v i := by
  have hx : dilW A Astar v i ∈
      (subspace (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) (i + 1))ᗮ := by
    rw [← Arnoldi.span_vec, Submodule.mem_orthogonal_span]
    rintro _ ⟨l, hl, rfl⟩
    rw [ih l (Nat.lt_succ_iff.1 hl)]
    exact inner_dilVec_dilW A Astar v (Nat.lt_succ_iff.1 hl)
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [dilW_two_mul] at hx ⊢
    cases j with
    | zero =>
      refine w_eq_of_apply_eq_add (y := 0) ?_ hx (Submodule.zero_mem _)
      rw [ih (2 * 0) le_rfl, dilVec_two_mul, hermitianDilation_toLp, map_zero,
        apply_rightVec_zero, add_zero]
    | succ j =>
      refine w_eq_of_apply_eq_add (y := (beta A Astar v j : 𝕜) •
          Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) (2 * j + 1)) ?_ hx
        (Submodule.smul_mem _ _ (Arnoldi.vec_mem_subspace_of_lt _ _ (by omega)))
      rw [ih (2 * (j + 1)) le_rfl, ih (2 * j + 1) (by omega), dilVec_two_mul,
        dilVec_two_mul_add_one, hermitianDilation_toLp, map_zero, apply_rightVec v hadj,
        ← WithLp.toLp_smul, ← WithLp.toLp_add, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero,
        add_comm]
  · rw [dilW_two_mul_add_one] at hx ⊢
    refine w_eq_of_apply_eq_add (y := (alpha A Astar v j : 𝕜) •
        Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) (2 * j)) ?_ hx
      (Submodule.smul_mem _ _ (Arnoldi.vec_mem_subspace_of_lt _ _ (by omega)))
    rw [ih (2 * j + 1) le_rfl, ih (2 * j) (by omega), dilVec_two_mul, dilVec_two_mul_add_one,
      hermitianDilation_toLp, map_zero, adjoint_apply_leftVec v hadj, ← WithLp.toLp_smul,
      ← WithLp.toLp_add, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, add_comm]

/-- The Lanczos vectors of the dilation are the interleaved Golub–Kahan vectors. -/
private theorem vec_hermitianDilation_eq_dilVec (i : ℕ) :
    Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) i = dilVec A Astar v i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    cases i with
    | zero => exact vec_zero_hermitianDilation A Astar v
    | succ i =>
      have ih' : ∀ l ≤ i, Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) l =
          dilVec A Astar v l := fun l hl => ih l (Nat.lt_succ_of_le hl)
      rw [Arnoldi.vec_succ_eq, w_hermitianDilation_of_forall v hadj ih']
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
      · rw [dilW_two_mul, dilVec_two_mul_add_one, ← WithLp.toLp_smul, Prod.smul_mk, smul_zero,
          norm_toLp_snd, inv_norm_smul_smul (alpha_nonneg A Astar v j)
            (leftVec_eq_zero_of_alpha_eq_zero A Astar v)
            (Arnoldi.norm_vec_eq_one_of_ne_zero _ _)]
      · rw [dilW_two_mul_add_one, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, dilVec_two_mul,
          ← WithLp.toLp_smul, Prod.smul_mk, smul_zero, norm_toLp_fst,
          inv_norm_smul_smul (beta_nonneg A Astar v j)
            (rightVec_eq_zero_of_beta_eq_zero A Astar v)
            (Arnoldi.norm_vec_eq_one_of_ne_zero _ _)]

/-- The even Lanczos vectors of the Jordan–Wielandt operator from `(v, 0)` are `(v_j, 0)`
([golub2013matrix] §10.4.3). -/
theorem vec_hermitianDilation_two_mul (j : ℕ) :
    Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) (2 * j) =
      WithLp.toLp 2 (rightVec A Astar v j, 0) := by
  rw [vec_hermitianDilation_eq_dilVec v hadj, dilVec_two_mul]

/-- The odd Lanczos vectors of the Jordan–Wielandt operator from `(v, 0)` are `(0, u_j)`
([golub2013matrix] §10.4.3). -/
theorem vec_hermitianDilation_two_mul_add_one (j : ℕ) :
    Arnoldi.vec (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) (2 * j + 1) =
      WithLp.toLp 2 (0, leftVec A Astar v j) := by
  rw [vec_hermitianDilation_eq_dilVec v hadj, dilVec_two_mul_add_one]

/-- The Lanczos process of the Jordan–Wielandt operator has zero diagonal. -/
theorem lanczos_alpha_hermitianDilation (i : ℕ) :
    Lanczos.alpha (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) i = 0 := by
  rw [Lanczos.alpha, Arnoldi.coeff, vec_hermitianDilation_eq_dilVec v hadj]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
  · simp [dilVec_two_mul]
  · simp [dilVec_two_mul_add_one]

/-- The off-diagonal of the Jordan–Wielandt Lanczos matrix at even positions: `β_{2j} = α_j`. -/
theorem lanczos_beta_hermitianDilation_two_mul (j : ℕ) :
    Lanczos.beta (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) (2 * j) =
      alpha A Astar v j := by
  rw [Lanczos.beta, w_hermitianDilation_of_forall v hadj
    (fun l _ => vec_hermitianDilation_eq_dilVec v hadj l), dilW_two_mul, norm_toLp_snd]
  refine norm_ofReal_smul_eq (alpha_nonneg A Astar v j) (fun h => ?_)
    (Arnoldi.norm_vec_eq_one_of_ne_zero _ _)
  rw [alpha, h, inner_zero_left, map_zero]

/-- The off-diagonal of the Jordan–Wielandt Lanczos matrix at odd positions: `β_{2j+1} = β_j`. -/
theorem lanczos_beta_hermitianDilation_two_mul_add_one (j : ℕ) :
    Lanczos.beta (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) (2 * j + 1) =
      beta A Astar v j := by
  rw [Lanczos.beta, w_hermitianDilation_of_forall v hadj
    (fun l _ => vec_hermitianDilation_eq_dilVec v hadj l), dilW_two_mul_add_one, norm_toLp_fst]
  refine norm_ofReal_smul_eq (beta_nonneg A Astar v j) (fun h => ?_)
    (Arnoldi.norm_vec_eq_one_of_ne_zero _ _)
  rw [beta, h, inner_zero_left, map_zero]

/-- **The tridiagonal–bidiagonal connection** ([golub2013matrix] §10.4.3, with (10.4.17)): the
Lanczos matrix of the Jordan–Wielandt operator `LinearMap.hermitianDilation A Astar` (on
`WithLp 2 (E × F)`, `(x, y) ↦ (Astar y, A x)`) from `(v, 0)` has zero diagonal and off-diagonal
`α₀, β₀, α₁, β₁, …`. (The book's `C = [0 A; Aᴴ 0]` acts on `F × E` from `(0, v)`; the dilation puts
the domain factor first.) -/
theorem lanczos_jordanWielandt (k : ℕ) :
    Lanczos.tridiag (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) k =
      Matrix.of fun i j : Fin k =>
        if (i : ℕ) + 1 = j then
          (if (i : ℕ) % 2 = 0 then alpha A Astar v (i / 2) else beta A Astar v (i / 2))
        else if (j : ℕ) + 1 = i then
          (if (j : ℕ) % 2 = 0 then alpha A Astar v (j / 2) else beta A Astar v (j / 2))
        else 0 := by
  have hb : ∀ l : ℕ, Lanczos.beta (hermitianDilation A Astar) (WithLp.toLp 2 (v, 0)) l =
      if l % 2 = 0 then alpha A Astar v (l / 2) else beta A Astar v (l / 2) := fun l => by
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' l
    · rw [lanczos_beta_hermitianDilation_two_mul v hadj]
      simp
    · rw [lanczos_beta_hermitianDilation_two_mul_add_one v hadj]
      simp [show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]
  ext i j
  rw [Lanczos.tridiag_apply, Matrix.of_apply, lanczos_alpha_hermitianDilation v hadj, hb, hb]
  split_ifs <;> first | rfl | omega

end Operator

/-! ### Matrix form -/

section Matrix

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (A : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n)

/-- The matrix `V_k = [v_1 | ⋯ | v_k]` of right Golub–Kahan vectors of `A : Matrix m n 𝕜` from `v`
([golub2013matrix] (10.4.9)). -/
noncomputable def rightMatrix (k : ℕ) : Matrix n (Fin k) 𝕜 :=
  Matrix.of fun i j => (rightVec (toEuclideanLin A) (toEuclideanLin Aᴴ) v j).ofLp i

/-- The matrix `U_k = [u_1 | ⋯ | u_k]` of left Golub–Kahan vectors of `A : Matrix m n 𝕜` from `v`
([golub2013matrix] (10.4.9)). -/
noncomputable def leftMatrix (k : ℕ) : Matrix m (Fin k) 𝕜 :=
  Matrix.of fun i j => (leftVec (toEuclideanLin A) (toEuclideanLin Aᴴ) v j).ofLp i

/-- `V_k` is the Lanczos basis matrix of `Aᴴ A` from `v`. -/
theorem rightMatrix_eq_basisMatrix (k : ℕ) :
    rightMatrix A v k = Arnoldi.basisMatrix (Aᴴ * A) v k := by
  ext i j
  simp only [rightMatrix, Arnoldi.basisMatrix, Matrix.of_apply, rightVec, toEuclideanLin_mul]

/-- `U_k` is the Lanczos basis matrix of `A Aᴴ` from `A v`. -/
theorem leftMatrix_eq_basisMatrix (k : ℕ) :
    leftMatrix A v k = Arnoldi.basisMatrix (A * Aᴴ) (toEuclideanLin A v) k := by
  ext i j
  simp only [leftMatrix, Arnoldi.basisMatrix, Matrix.of_apply, leftVec, toEuclideanLin_mul]

/-- Orthonormal columns: `V_kᴴ V_k = 1` below the grade of `Aᴴ A` at `v`. -/
theorem conjTranspose_rightMatrix_mul_self {k : ℕ}
    (hk : k ≤ grade (toEuclideanLin (Aᴴ * A)) v) :
    (rightMatrix A v k)ᴴ * rightMatrix A v k = 1 := by
  rw [rightMatrix_eq_basisMatrix]
  exact Arnoldi.conjTranspose_basisMatrix_mul_self _ _ hk

/-- Orthonormal columns: `U_kᴴ U_k = 1` below the grade of `A Aᴴ` at `A v`. -/
theorem conjTranspose_leftMatrix_mul_self {k : ℕ}
    (hk : k ≤ grade (toEuclideanLin (A * Aᴴ)) (toEuclideanLin A v)) :
    (leftMatrix A v k)ᴴ * leftMatrix A v k = 1 := by
  rw [leftMatrix_eq_basisMatrix]
  exact Arnoldi.conjTranspose_basisMatrix_mul_self _ _ hk

private theorem hadj_toEuclideanLin :
    ∀ u x, inner 𝕜 (toEuclideanLin Aᴴ u) x = inner 𝕜 u (toEuclideanLin A x) :=
  fun u x => toEuclideanLin_conjTranspose_inner_left A x u

/-- (10.4.9) of [golub2013matrix]: `A V_k = U_k B_k`, for every `k` (past breakdown the columns
vanish on both sides). -/
theorem mul_rightMatrix (k : ℕ) :
    A * rightMatrix A v k =
      leftMatrix A v k * (bidiag (toEuclideanLin A) (toEuclideanLin Aᴴ) v k).map
        (algebraMap ℝ 𝕜) := by
  ext x j
  have hl : (A * rightMatrix A v k) x j =
      (toEuclideanLin A (rightVec (toEuclideanLin A) (toEuclideanLin Aᴴ) v j)).ofLp x := by
    rw [ofLp_toEuclideanLin]
    rfl
  rw [hl, Matrix.mul_apply]
  simp only [leftMatrix, Matrix.map_apply, Matrix.of_apply, bidiag_apply,
    RCLike.algebraMap_eq_ofReal]
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero =>
    rw [apply_rightVec_zero, Fintype.sum_eq_single ⟨0, hj⟩]
    · simp [RCLike.real_smul_eq_coe_mul, mul_comm]
    · intro l hl
      have hl' : (l : ℕ) ≠ 0 := fun h => hl (Fin.ext h)
      rw [ite_eq_right (by simpa using hl'), ite_eq_right (by simp), RCLike.ofReal_zero, mul_zero]
  | succ j =>
    rw [apply_rightVec v (hadj_toEuclideanLin A), Fintype.sum_eq_add ⟨j, by omega⟩ ⟨j + 1, hj⟩
      (fun h => by simpa using congrArg Fin.val h) (fun l hl => by
        have h1 : (l : ℕ) ≠ j := fun h => hl.1 (Fin.ext h)
        have h2 : (l : ℕ) ≠ j + 1 := fun h => hl.2 (Fin.ext h)
        rw [ite_eq_right (by simpa using h2), ite_eq_right (by simpa using h1),
          RCLike.ofReal_zero, mul_zero])]
    simp [RCLike.real_smul_eq_coe_mul, mul_comm]

/-- (10.4.10) of [golub2013matrix]: `Aᴴ U_k = V_{k+1} B̄_k`, equivalently `V_k B_kᵀ + β_k v_{k+1}
e_kᵀ`. Applied to `Aᴴ` it is the Paige–Saunders relation (10.4.19). -/
theorem conjTranspose_mul_leftMatrix (k : ℕ) :
    Aᴴ * leftMatrix A v k =
      rightMatrix A v (k + 1) * (bidiagLower (toEuclideanLin A) (toEuclideanLin Aᴴ) v k).map
        (algebraMap ℝ 𝕜) := by
  ext x j
  have hl : (Aᴴ * leftMatrix A v k) x j =
      (toEuclideanLin Aᴴ (leftVec (toEuclideanLin A) (toEuclideanLin Aᴴ) v j)).ofLp x := by
    rw [ofLp_toEuclideanLin]
    rfl
  rw [hl, Matrix.mul_apply, adjoint_apply_leftVec v (hadj_toEuclideanLin A),
    Fintype.sum_eq_add j.castSucc j.succ Fin.castSucc_lt_succ.ne (fun l hl => by
      have h1 : (l : ℕ) ≠ j := fun h => hl.1 (Fin.ext h)
      have h2 : (l : ℕ) ≠ j + 1 := fun h => hl.2 (Fin.ext h)
      simp only [Matrix.map_apply, bidiagLower_apply, RCLike.algebraMap_eq_ofReal]
      rw [ite_eq_right h1, ite_eq_right h2, RCLike.ofReal_zero, mul_zero])]
  simp [rightMatrix, bidiagLower_apply, RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal,
    mul_comm]

end Matrix

end GolubKahan
