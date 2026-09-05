import Numlib.Surface.SaadSparse.Ch06.Basic

/-!
# Saad, §6.3: Arnoldi's method

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §6.3.

Algorithm 6.1 (Arnoldi with classical Gram–Schmidt) is `arnoldiCGS`; its coefficients `h_{ij}`
are `arnoldiCoeff` and its unnormalized vectors `w_j` are `arnoldiW`; the matrices `V_m`,
`H̄_m`, `H_m` of §6.3.1 are `V`, `Hbar`, `H`. Algorithm 6.2 (modified Gram–Schmidt) is
`arnoldiMGS`, with coefficients `arnoldiMGSCoeff`. Algorithm 6.3 (Householder Arnoldi) is
`hhZ`, `hhW`, `hhV`, `hhH` with the reflectors `householder`, `householderVec` of Saad
(1.23)–(1.26); `Qhh` is the `Q_j` of (6.10).

Indices are `0`-based: `arnoldiCGS A v₁ j` is the book's `v_{j+1}` and `arnoldiCoeff A v₁ i j`
is the book's `h_{i+1,j+1}`. Division by a vanishing norm is `0` in Lean, which reproduces the
book's "if `h_{j+1,j} = 0` then Stop": every later vector is `0`.

The bridge to the backbone is `arnoldiCGS_eq_vec_of_vec_zero`, which identifies Algorithm 6.1
with `Arnoldi.vec`, the Gram–Schmidt orthonormalization of the Krylov sequence. Its two
instances are `arnoldiCGS_eq_vec` (unit starting vector) and `arnoldiCGS_normalize` (the
residual start `v_1 = r_0/‖r_0‖` used by FOM and GMRES, where the backbone indexes everything
by `r_0` itself); `arnoldiCoeff_eq`, `Hbar_eq`, `H_eq`, the `*_normalize` family and
`hessenbergRelation` follow, and with them Propositions 6.4, 6.5, 6.6 and (6.6)–(6.9).

Definitions are polymorphic in `𝕜`; the numbered results are stated over `ℝ`, the book's
generality in §6.3, as one-line specializations of field-agnostic companions. Householder
Arnoldi is real throughout, as in the book.
-/

open scoped Matrix

namespace SaadSparse.Ch06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Coordinate helpers -/

private theorem sum_coord {ι : Type*} (s : Finset ι) (f : ι → 𝔼) (i : Fin n) :
    (∑ k ∈ s, f k) i = ∑ k ∈ s, f k i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

private theorem op_coord (B : Matrix (Fin n) (Fin n) 𝕜) (x : 𝔼) (i : Fin n) :
    op B x i = ∑ k, B i k * x k := rfl

private theorem range_fin_eq_image_Iio {α : Type*} (f : ℕ → α) (m : ℕ) :
    Set.range (fun i : Fin m => f (i : ℕ)) = f '' Set.Iio m := by
  ext x
  simp only [Set.mem_range, Set.mem_image, Set.mem_Iio, Fin.exists_iff]
  tauto

/-! ### Algorithm 6.1: Arnoldi with classical Gram–Schmidt -/

/-- **Algorithm 6.1** (Arnoldi, classical Gram–Schmidt), `0`-based: `v_0 = v₁` and
`v_{j+1} = w_j / ‖w_j‖` with `w_j = A v_j - ∑_{i ≤ j} h_{ij} v_i` and `h_{ij} = (A v_j, v_i)`.
The book's "if `h_{j+1,j} = 0` then Stop" is Lean's `x / 0 = 0`: all later vectors are `0`. -/
noncomputable def arnoldiCGS (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) : ℕ → 𝔼
  | 0 => v₁
  | j + 1 =>
    let v : Fin (j + 1) → 𝔼 := fun i => arnoldiCGS A v₁ (i : ℕ)
    let Av := op A (v (Fin.last j))
    let w := Av - ∑ i : Fin (j + 1), inner 𝕜 (v i) Av • v i
    ((‖w‖ : 𝕜)⁻¹) • w
  termination_by j => j
  decreasing_by exact i.isLt

/-- The Arnoldi coefficients `h_{ij} = (A v_j, v_i)` of Algorithm 6.1, line 3. -/
noncomputable def arnoldiCoeff (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (i j : ℕ) : 𝕜 :=
  inner 𝕜 (arnoldiCGS A v₁ i) (op A (arnoldiCGS A v₁ j))

/-- The unnormalized vector `w_j = A v_j - ∑_{i ≤ j} h_{ij} v_i` of Algorithm 6.1, line 4. -/
noncomputable def arnoldiW (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (j : ℕ) : 𝔼 :=
  op A (arnoldiCGS A v₁ j) -
    ∑ i ∈ Finset.range (j + 1), arnoldiCoeff A v₁ i j • arnoldiCGS A v₁ i

variable (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : EuclideanSpace 𝕜 (Fin n))

@[simp]
theorem arnoldiCGS_zero : arnoldiCGS A v₁ 0 = v₁ := by rw [arnoldiCGS]

/-- Algorithm 6.1, line 7: `v_{j+1} = w_j / h_{j+1,j}` with `h_{j+1,j} = ‖w_j‖`. -/
theorem arnoldiCGS_succ (j : ℕ) :
    arnoldiCGS A v₁ (j + 1) = ((‖arnoldiW A v₁ j‖ : 𝕜)⁻¹) • arnoldiW A v₁ j := by
  rw [arnoldiCGS, arnoldiW]
  simp only [arnoldiCoeff, Fin.val_last]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => inner 𝕜 (arnoldiCGS A v₁ i) (op A (arnoldiCGS A v₁ j)) • arnoldiCGS A v₁ i) (j + 1)]

/-! ### Identification with the backbone Arnoldi process -/

private theorem arnoldiW_eq_of_forall {r : EuclideanSpace 𝕜 (Fin n)} {j : ℕ}
    (ih : ∀ i ≤ j, arnoldiCGS A v₁ i = Arnoldi.vec (op A) r i) :
    arnoldiW A v₁ j = Arnoldi.w (op A) r j := by
  have hsum : ∑ i ∈ Finset.range (j + 1), arnoldiCoeff A v₁ i j • arnoldiCGS A v₁ i
      = ∑ i ∈ Finset.range (j + 1),
        Arnoldi.coeff (op A) r i j • Arnoldi.vec (op A) r i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [arnoldiCoeff, ih i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)), ih j le_rfl]
    rfl
  rw [arnoldiW, Arnoldi.w, hsum, ih j le_rfl]

/-- **The bridge to the backbone**: Algorithm 6.1 started at `v₁` computes the backbone Arnoldi
vectors of any `r` whose normalization is `v₁`. The two instances are `r = v₁` for a unit
starting vector (`arnoldiCGS_eq_vec`) and `r = r₀`, `v₁ = r₀/‖r₀‖` for the residual start that
FOM and GMRES use (`arnoldiCGS_normalize`). -/
theorem arnoldiCGS_eq_vec_of_vec_zero {r : EuclideanSpace 𝕜 (Fin n)}
    (h0 : Arnoldi.vec (op A) r 0 = v₁) (j : ℕ) : arnoldiCGS A v₁ j = Arnoldi.vec (op A) r j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [arnoldiCGS_zero, h0]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      rw [arnoldiCGS_succ, Arnoldi.vec_succ_eq,
        arnoldiW_eq_of_forall A v₁ fun i hi => ih i (Nat.lt_succ_of_le hi)]

/-- For a unit starting vector, Algorithm 6.1 computes the Gram–Schmidt orthonormalization
`Arnoldi.vec` of the Krylov sequence `v₁, A v₁, A² v₁, …`. -/
theorem arnoldiCGS_eq_vec (hv : ‖v₁‖ = 1) (j : ℕ) :
    arnoldiCGS A v₁ j = Arnoldi.vec (op A) v₁ j := by
  refine arnoldiCGS_eq_vec_of_vec_zero A v₁ ?_ j
  have hv0 : v₁ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    exact zero_ne_one hv
  rw [Arnoldi.vec_zero (op A) v₁ hv0, hv]
  simp

theorem arnoldiCoeff_eq (hv : ‖v₁‖ = 1) (i j : ℕ) :
    arnoldiCoeff A v₁ i j = Arnoldi.coeff (op A) v₁ i j := by
  rw [arnoldiCoeff, arnoldiCGS_eq_vec A v₁ hv, arnoldiCGS_eq_vec A v₁ hv]
  rfl

theorem arnoldiW_eq (hv : ‖v₁‖ = 1) (j : ℕ) : arnoldiW A v₁ j = Arnoldi.w (op A) v₁ j :=
  arnoldiW_eq_of_forall A v₁ fun i _ => arnoldiCGS_eq_vec A v₁ hv i

/-- The Arnoldi vectors are pairwise orthogonal (also past the breakdown, where they are `0`). -/
theorem inner_arnoldiCGS_eq_zero (hv : ‖v₁‖ = 1) {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (arnoldiCGS A v₁ i) (arnoldiCGS A v₁ j) = 0 := by
  rw [arnoldiCGS_eq_vec A v₁ hv, arnoldiCGS_eq_vec A v₁ hv]
  exact Arnoldi.inner_vec_eq_zero _ _ h

/-- Breakdown: the Arnoldi vectors vanish exactly from the grade of `v₁` on. -/
theorem arnoldiCGS_eq_zero_iff (hv : ‖v₁‖ = 1) (j : ℕ) :
    arnoldiCGS A v₁ j = 0 ↔ grade A v₁ ≤ j := by
  rw [arnoldiCGS_eq_vec A v₁ hv, Arnoldi.vec_eq_zero_iff, grade_eq]

theorem norm_arnoldiCGS (hv : ‖v₁‖ = 1) {j : ℕ} (h : j < grade A v₁) :
    ‖arnoldiCGS A v₁ j‖ = 1 := by
  rw [arnoldiCGS_eq_vec A v₁ hv]
  exact Arnoldi.norm_vec_eq_one_of_lt_grade _ _ (by rwa [← grade_eq])

/-- `h_{j+1,j} = ‖w_j‖`: Algorithm 6.1, line 5. -/
theorem arnoldiCoeff_succ_self (hv : ‖v₁‖ = 1) (j : ℕ) :
    arnoldiCoeff A v₁ (j + 1) j = (‖arnoldiW A v₁ j‖ : 𝕜) := by
  rw [arnoldiCoeff_eq A v₁ hv, arnoldiW_eq A v₁ hv, Arnoldi.coeff_succ_self]

/-- `w_j = h_{j+1,j} v_{j+1}`. -/
theorem arnoldiW_eq_smul (hv : ‖v₁‖ = 1) (j : ℕ) :
    arnoldiW A v₁ j = arnoldiCoeff A v₁ (j + 1) j • arnoldiCGS A v₁ (j + 1) := by
  rw [arnoldiCoeff_succ_self A v₁ hv, arnoldiCGS_succ, smul_smul]
  rcases eq_or_ne (arnoldiW A v₁ j) 0 with h | h
  · rw [h, smul_zero]
  · rw [mul_inv_cancel₀ (by simpa using norm_ne_zero_iff.2 h), one_smul]

/-- The Hessenberg structure: `h_{ij} = 0` for `i > j + 1`. -/
theorem arnoldiCoeff_eq_zero_of_lt (hv : ‖v₁‖ = 1) {i j : ℕ} (h : j + 1 < i) :
    arnoldiCoeff A v₁ i j = 0 := by
  rw [arnoldiCoeff_eq A v₁ hv]
  exact Arnoldi.coeff_eq_zero_of_lt (op A) v₁ h

/-- The Arnoldi vectors and coefficients satisfy the backbone Hessenberg relation
`A v_j = ∑_{i ≤ j+1} h_{ij} v_i`; this is the interface used by the FOM, GMRES and Givens
developments. -/
theorem hessenbergRelation (hv : ‖v₁‖ = 1) :
    Krylov.HessenbergRelation (op A) (arnoldiCGS A v₁) (arnoldiCoeff A v₁) := by
  have hvec : arnoldiCGS A v₁ = Arnoldi.vec (op A) v₁ := funext (arnoldiCGS_eq_vec A v₁ hv)
  have hc : arnoldiCoeff A v₁ = Arnoldi.coeff (op A) v₁ := by
    funext i j
    exact arnoldiCoeff_eq A v₁ hv i j
  rw [hvec, hc]
  exact Arnoldi.hessenbergRelation (op A) v₁

/-! ### Breakdown -/

/-- "Algorithm 6.1 does not stop before the `m`-th step": `h_{j+1,j} ≠ 0` at every step `j`
strictly before the last one. -/
def NoBreakdownBefore (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (m : ℕ) : Prop :=
  ∀ j, j + 1 < m → arnoldiCoeff A v₁ (j + 1) j ≠ 0

theorem arnoldiCoeff_succ_self_eq_zero_iff (hv : ‖v₁‖ = 1) (j : ℕ) :
    arnoldiCoeff A v₁ (j + 1) j = 0 ↔ grade A v₁ ≤ j + 1 := by
  rw [arnoldiCoeff_eq A v₁ hv, Arnoldi.coeff_succ_self_eq_zero_iff, grade_eq]

theorem grade_pos (hv : ‖v₁‖ = 1) : 0 < grade A v₁ := by
  rw [grade_eq]
  refine Nat.pos_of_ne_zero fun h => ?_
  rcases (Krylov.grade_eq_zero_iff (op A) v₁).1 h with h0 | h0
  · rw [h0, norm_zero] at hv
    exact zero_ne_one hv
  · exact h0 inferInstance

/-- Not stopping before step `m` is exactly `m ≤ μ`, the grade of the starting vector. -/
theorem noBreakdownBefore_iff (hv : ‖v₁‖ = 1) (m : ℕ) :
    NoBreakdownBefore A v₁ m ↔ m ≤ grade A v₁ := by
  constructor
  · intro h
    by_contra hc
    have hpos := grade_pos A v₁ hv
    obtain ⟨k, hk⟩ : ∃ k, grade A v₁ = k + 1 := ⟨grade A v₁ - 1, by omega⟩
    exact h k (by omega) ((arnoldiCoeff_succ_self_eq_zero_iff A v₁ hv k).2 (by omega))
  · intro h j hj hz
    exact absurd ((arnoldiCoeff_succ_self_eq_zero_iff A v₁ hv j).1 hz) (by omega)

/-! ### The matrices `V_m`, `H̄_m`, `H_m` of §6.3.1 -/

/-- The matrix whose `j`-th column is `u j`: the shape of the book's `V_m` for any `0`-based
sequence of vectors (Arnoldi, incomplete orthogonalization, Householder Arnoldi, …). -/
noncomputable def colMatrix (u : ℕ → 𝔼) (m : ℕ) : Matrix (Fin n) (Fin m) 𝕜 :=
  Matrix.of fun i j => u (j : ℕ) i

/-- `V_m = [v_1, …, v_m]`, the matrix whose columns are the Arnoldi vectors. -/
noncomputable def V (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (m : ℕ) : Matrix (Fin n) (Fin m) 𝕜 :=
  colMatrix (arnoldiCGS A v₁) m

/-- `H̄_m`, the `(m+1) × m` Hessenberg matrix of the Arnoldi coefficients. -/
noncomputable def Hbar (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin m) 𝕜 :=
  Matrix.of fun i j => arnoldiCoeff A v₁ i j

/-- `H_m`, the square `m × m` matrix obtained from `H̄_m` by deleting its last row. -/
noncomputable def H (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => arnoldiCoeff A v₁ i j

@[simp]
theorem V_apply {m : ℕ} (i : Fin n) (j : Fin m) : V A v₁ m i j = arnoldiCGS A v₁ (j : ℕ) i := rfl

@[simp]
theorem Hbar_apply {m : ℕ} (i : Fin (m + 1)) (j : Fin m) :
    Hbar A v₁ m i j = arnoldiCoeff A v₁ i j := rfl

@[simp]
theorem H_apply {m : ℕ} (i j : Fin m) : H A v₁ m i j = arnoldiCoeff A v₁ i j := rfl

theorem Hbar_eq_hessenbergOf (m : ℕ) :
    Hbar A v₁ m = Krylov.hessenbergOf (arnoldiCoeff A v₁) m := rfl

theorem H_eq_hessenbergSqOf (m : ℕ) :
    H A v₁ m = Krylov.hessenbergSqOf (arnoldiCoeff A v₁) m := rfl

theorem Hbar_eq (hv : ‖v₁‖ = 1) (m : ℕ) : Hbar A v₁ m = Arnoldi.hessenberg (op A) v₁ m := by
  ext i j
  rw [Hbar_apply, arnoldiCoeff_eq A v₁ hv]
  rfl

theorem H_eq (hv : ‖v₁‖ = 1) (m : ℕ) : H A v₁ m = Arnoldi.hessenbergSq (op A) v₁ m := by
  ext i j
  rw [H_apply, arnoldiCoeff_eq A v₁ hv]
  rfl

/-- `V_m y = ∑_j y_j u_j` for the matrix of any `0`-based family of vectors (Arnoldi,
incomplete orthogonalization, Householder Arnoldi, …). -/
theorem toEuclideanLin_colMatrix_apply (u : ℕ → 𝔼) {m : ℕ} (y : Fin m → 𝕜) :
    Matrix.toEuclideanLin (colMatrix u m) (WithLp.toLp 2 y) = ∑ j, y j • u (j : ℕ) := by
  rw [Matrix.toEuclideanLin_apply_eq_sum]
  exact Finset.sum_congr rfl fun j _ => rfl

/-- `V_m y = ∑_j y_j v_j`: the book's `V_m y` in the expansion form used by the backbone. -/
theorem toEuclideanLin_V_apply {m : ℕ} (y : Fin m → 𝕜) :
    Matrix.toEuclideanLin (V A v₁ m) (WithLp.toLp 2 y) = ∑ j, y j • arnoldiCGS A v₁ (j : ℕ) :=
  toEuclideanLin_colMatrix_apply _ y

/-! ### Starting from an unnormalized vector

FOM and GMRES run Algorithm 6.1 on `v_1 = r_0/‖r_0‖`, while the backbone indexes the Arnoldi
data by the residual `r_0` itself. These lemmas are the translation between the two. -/

theorem norm_norm_inv_smul {r : EuclideanSpace 𝕜 (Fin n)} (hr : r ≠ 0) :
    ‖(‖r‖⁻¹ : 𝕜) • r‖ = 1 := by
  rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hr)]

theorem arnoldiCGS_normalize {r : EuclideanSpace 𝕜 (Fin n)} (hr : r ≠ 0) (j : ℕ) :
    arnoldiCGS A ((‖r‖⁻¹ : 𝕜) • r) j = Arnoldi.vec (op A) r j :=
  arnoldiCGS_eq_vec_of_vec_zero A _ (Arnoldi.vec_zero (op A) r hr) j

theorem arnoldiCoeff_normalize {r : EuclideanSpace 𝕜 (Fin n)} (hr : r ≠ 0) (i j : ℕ) :
    arnoldiCoeff A ((‖r‖⁻¹ : 𝕜) • r) i j = Arnoldi.coeff (op A) r i j := by
  rw [arnoldiCoeff, arnoldiCGS_normalize A hr, arnoldiCGS_normalize A hr]
  rfl

theorem H_normalize {r : EuclideanSpace 𝕜 (Fin n)} (hr : r ≠ 0) (m : ℕ) :
    H A ((‖r‖⁻¹ : 𝕜) • r) m = Arnoldi.hessenbergSq (op A) r m := by
  ext i j
  rw [H_apply, arnoldiCoeff_normalize A hr]
  rfl

theorem Hbar_normalize {r : EuclideanSpace 𝕜 (Fin n)} (hr : r ≠ 0) (m : ℕ) :
    Hbar A ((‖r‖⁻¹ : 𝕜) • r) m = Arnoldi.hessenberg (op A) r m := by
  ext i j
  rw [Hbar_apply, arnoldiCoeff_normalize A hr]
  rfl

theorem grade_normalize {r : EuclideanSpace 𝕜 (Fin n)} (hr : r ≠ 0) :
    grade A ((‖r‖⁻¹ : 𝕜) • r) = grade A r :=
  grade_smul A r (inv_ne_zero (by simpa using norm_ne_zero_iff.2 hr))

/-! ### Proposition 6.4 -/

theorem orthonormal_arnoldiCGS (hv : ‖v₁‖ = 1) {m : ℕ} (hm : m ≤ grade A v₁) :
    Orthonormal 𝕜 (fun i : Fin m => arnoldiCGS A v₁ (i : ℕ)) := by
  have hg : m ≤ Krylov.grade (op A) v₁ := by rwa [← grade_eq]
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · dsimp only
    rw [arnoldiCGS_eq_vec A v₁ hv]
    exact Arnoldi.norm_vec_eq_one_of_lt_grade _ _ (lt_of_lt_of_le i.2 hg)
  · exact inner_arnoldiCGS_eq_zero A v₁ hv fun h => hij (Fin.val_injective h)

theorem span_arnoldiCGS (hv : ‖v₁‖ = 1) (m : ℕ) :
    Submodule.span 𝕜 (Set.range fun i : Fin m => arnoldiCGS A v₁ (i : ℕ)) = krylov A v₁ m := by
  have hfun : (fun i : Fin m => arnoldiCGS A v₁ (i : ℕ))
      = fun i : Fin m => Arnoldi.vec (op A) v₁ (i : ℕ) :=
    funext fun i => arnoldiCGS_eq_vec A v₁ hv i
  rw [krylov_eq, hfun, range_fin_eq_image_Iio, Arnoldi.span_vec]

/-! ### (6.6)–(6.9) and Proposition 6.5 -/

/-- (6.9): `A v_j = ∑_{i=1}^{j+1} h_{ij} v_i`. -/
theorem apply_arnoldiCGS (hv : ‖v₁‖ = 1) (j : ℕ) :
    op A (arnoldiCGS A v₁ j)
      = ∑ i ∈ Finset.range (j + 2), arnoldiCoeff A v₁ i j • arnoldiCGS A v₁ i :=
  (hessenbergRelation A v₁ hv).apply_eq j

private theorem eq_6_9_range (hv : ‖v₁‖ = 1) {j N : ℕ} (h : j + 2 ≤ N) :
    op A (arnoldiCGS A v₁ j)
      = ∑ i ∈ Finset.range N, arnoldiCoeff A v₁ i j • arnoldiCGS A v₁ i := by
  simp only [arnoldiCGS_eq_vec A v₁ hv, arnoldiCoeff_eq A v₁ hv]
  exact Arnoldi.apply_vec_of_le (op A) v₁ h

theorem mul_colMatrix_apply (B : Matrix (Fin n) (Fin n) 𝕜) (u : ℕ → 𝔼) {m : ℕ} (i : Fin n)
    (j : Fin m) : (B * colMatrix u m) i j = op B (u (j : ℕ)) i := by
  rw [Matrix.mul_apply, op_coord]
  rfl

private theorem mul_V_apply {m : ℕ} (i : Fin n) (j : Fin m) :
    (A * V A v₁ m) i j = op A (arnoldiCGS A v₁ (j : ℕ)) i :=
  mul_colMatrix_apply A _ i j

/-- The Hessenberg relation in matrix form, for any sequence satisfying it: this is (6.7) for
Arnoldi, for incomplete orthogonalization, and for Householder Arnoldi alike. -/
theorem mul_colMatrix_eq {u : ℕ → 𝔼} {h : ℕ → ℕ → 𝕜}
    (hr : Krylov.HessenbergRelation (op A) u h) (m : ℕ) :
    A * colMatrix u m = colMatrix u (m + 1) * Krylov.hessenbergOf h m := by
  have hrange : ∀ j : ℕ, j + 2 ≤ m + 1 →
      op A (u j) = ∑ i ∈ Finset.range (m + 1), h i j • u i := by
    intro j hN
    rw [hr.apply_eq j]
    refine Finset.sum_subset (by simpa using hN) fun i _ hi => ?_
    rw [Finset.mem_range, not_lt] at hi
    rw [hr.eq_zero_of_lt i j (by omega), zero_smul]
  ext i j
  rw [mul_colMatrix_apply, hrange (j : ℕ) (by omega), sum_coord, Matrix.mul_apply,
    ← Fin.sum_univ_eq_sum_range (fun l => (h l (j : ℕ) • u l) i) (m + 1)]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- (6.7): `A V_m = V_{m+1} H̄_m`. -/
theorem mul_V_eq (hv : ‖v₁‖ = 1) (m : ℕ) : A * V A v₁ m = V A v₁ (m + 1) * Hbar A v₁ m :=
  mul_colMatrix_eq A (hessenbergRelation A v₁ hv) m

/-- (6.6): `A V_m = V_m H_m + w_m e_mᵀ`, stated with `m + 1` Arnoldi steps so that `w_m` is the
last vector computed. -/
theorem mul_V_eq_add_vecMulVec (hv : ‖v₁‖ = 1) (m : ℕ) :
    A * V A v₁ (m + 1) = V A v₁ (m + 1) * H A v₁ (m + 1) +
      Matrix.vecMulVec (WithLp.ofLp (arnoldiW A v₁ m)) (Pi.single (Fin.last m) 1) := by
  have hlast : ∀ j : Fin (m + 1),
      arnoldiCoeff A v₁ (m + 1) (j : ℕ) • arnoldiCGS A v₁ (m + 1)
        = (Pi.single (M := fun _ : Fin (m + 1) => 𝕜) (Fin.last m) 1 j) • arnoldiW A v₁ m := by
    intro j
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 j.2) with hj | hj
    · have hjl : j = Fin.last m := Fin.ext (by simpa using hj)
      rw [hjl, Fin.val_last, Pi.single_eq_same, one_smul, arnoldiW_eq_smul A v₁ hv]
    · have hne : (j : ℕ) ≠ m := by omega
      rw [arnoldiCoeff_eq_zero_of_lt A v₁ hv (by omega), zero_smul]
      simp [Fin.ext_iff, hne]
  ext i j
  rw [mul_V_apply, eq_6_9_range A v₁ hv (N := m + 2) (by omega), Finset.sum_range_succ, hlast j,
    PiLp.add_apply, sum_coord, Matrix.add_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    ← Fin.sum_univ_eq_sum_range
      (fun l => (arnoldiCoeff A v₁ l (j : ℕ) • arnoldiCGS A v₁ l) i) (m + 1)]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun l _ => mul_comm _ _) ?_
  rw [PiLp.smul_apply, smul_eq_mul, mul_comm]

/-- (6.8): `V_mᴴ A V_m = H_m` — the book's `V_mᵀ A V_m = H_m` for real matrices. Neither a unit
starting vector nor a bound on the number of Arnoldi steps is needed here: both sides are the
same inner products by definition, and past the breakdown both vanish. -/
theorem conjTranspose_V_mul_mul_V (m : ℕ) : (V A v₁ m)ᴴ * A * V A v₁ m = H A v₁ m := by
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply, H_apply, arnoldiCoeff, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, V_apply, mul_V_apply, RCLike.inner_apply, mul_comm]
  rfl

/-! ### Proposition 6.6 and the lucky breakdown -/

/-- Arnoldi's method breaks down at step `j` exactly when the grade of `v₁` — the degree of its
minimal polynomial — is `j`. -/
theorem breakdown_iff_grade_eq (hv : ‖v₁‖ = 1) {j : ℕ} (hj : 0 < j) :
    (NoBreakdownBefore A v₁ j ∧ arnoldiCoeff A v₁ j (j - 1) = 0) ↔ grade A v₁ = j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel, noBreakdownBefore_iff A v₁ hv,
    arnoldiCoeff_succ_self_eq_zero_iff A v₁ hv]
  omega

/-- Once Arnoldi has broken down at step `j`, the Krylov subspace `𝒦_j` is invariant under `A`
(Proposition 6.6, second part). -/
theorem krylov_mem_invtSubmodule_of_breakdown {j : ℕ} (h : grade A v₁ ≤ j) :
    krylov A v₁ j ∈ Module.End.invtSubmodule (op A) := by
  rw [krylov_eq_of_grade_le A v₁ h]
  exact krylov_grade_mem_invtSubmodule A v₁

/-! ### Algorithm 6.2: Arnoldi with modified Gram–Schmidt -/

/-- The inner loop of **Algorithm 6.2**: `w` after the projections on `v_0, …, v_{k-1}` have
been subtracted one at a time. -/
noncomputable def mgsW (v : ℕ → 𝔼) (w₀ : 𝔼) : ℕ → 𝔼
  | 0 => w₀
  | k + 1 => mgsW v w₀ k - inner 𝕜 (v k) (mgsW v w₀ k) • v k

private theorem mgsW_congr {v v' : ℕ → 𝔼} (w₀ : 𝔼) {k : ℕ} (h : ∀ i < k, v i = v' i) :
    mgsW v w₀ k = mgsW v' w₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [mgsW, mgsW, ih fun i hi => h i (hi.trans k.lt_succ_self), h k k.lt_succ_self]

/-- The inner loop of modified Gram–Schmidt subtracts the same total as classical Gram–Schmidt,
as soon as the `v_i` are pairwise orthogonal. -/
private theorem mgsW_eq_sub_sum {v : ℕ → 𝔼} (ho : ∀ i j, i ≠ j → inner 𝕜 (v i) (v j) = 0)
    (w₀ : 𝔼) (k : ℕ) :
    mgsW v w₀ k = w₀ - ∑ i ∈ Finset.range k, inner 𝕜 (v i) w₀ • v i := by
  induction k with
  | zero => simp [mgsW]
  | succ k ih =>
    have hik : inner 𝕜 (v k) (mgsW v w₀ k) = inner 𝕜 (v k) w₀ := by
      rw [ih, inner_sub_right, inner_sum]
      refine sub_eq_self.2 (Finset.sum_eq_zero fun i hi => ?_)
      rw [inner_smul_right, ho k i (Ne.symm (Finset.mem_range.1 hi).ne), mul_zero]
    rw [mgsW, hik, ih, Finset.sum_range_succ]
    abel

private theorem inner_mgsW_self {v : ℕ → 𝔼} (ho : ∀ i j, i ≠ j → inner 𝕜 (v i) (v j) = 0)
    (w₀ : 𝔼) (k : ℕ) : inner 𝕜 (v k) (mgsW v w₀ k) = inner 𝕜 (v k) w₀ := by
  rw [mgsW_eq_sub_sum ho, inner_sub_right, inner_sum]
  refine sub_eq_self.2 (Finset.sum_eq_zero fun i hi => ?_)
  rw [inner_smul_right, ho k i (Ne.symm (Finset.mem_range.1 hi).ne), mul_zero]

/-- **Algorithm 6.2** (Arnoldi, modified Gram–Schmidt), `0`-based. The clamp `min i j` is
invisible: the inner loop reads only `v_0, …, v_j`, where the clamped family agrees with
`arnoldiMGS` itself (`mgsW_congr`). -/
noncomputable def arnoldiMGS (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) : ℕ → 𝔼
  | 0 => v₁
  | j + 1 =>
    let v : ℕ → 𝔼 := fun i => arnoldiMGS A v₁ (min i j)
    let w := mgsW v (op A (v j)) (j + 1)
    ((‖w‖ : 𝕜)⁻¹) • w
  termination_by j => j
  decreasing_by exact Nat.lt_succ_of_le (Nat.min_le_right _ _)

/-- `w_j` of Algorithm 6.2, the vector left by the whole inner loop. -/
noncomputable def arnoldiMGSW (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (j : ℕ) : 𝔼 :=
  mgsW (arnoldiMGS A v₁) (op A (arnoldiMGS A v₁ j)) (j + 1)

/-- The coefficients of Algorithm 6.2: `h_{ij}` is the inner product of `v_i` with the *current*
`w` for `i ≤ j`, `h_{j+1,j} = ‖w_j‖`, and `0` above the subdiagonal. -/
noncomputable def arnoldiMGSCoeff (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (i j : ℕ) : 𝕜 :=
  if i ≤ j then inner 𝕜 (arnoldiMGS A v₁ i) (mgsW (arnoldiMGS A v₁) (op A (arnoldiMGS A v₁ j)) i)
  else if i = j + 1 then (‖arnoldiMGSW A v₁ j‖ : 𝕜) else 0

@[simp]
theorem arnoldiMGS_zero : arnoldiMGS A v₁ 0 = v₁ := by rw [arnoldiMGS]

theorem arnoldiMGS_succ (j : ℕ) :
    arnoldiMGS A v₁ (j + 1) = ((‖arnoldiMGSW A v₁ j‖ : 𝕜)⁻¹) • arnoldiMGSW A v₁ j := by
  rw [arnoldiMGS, arnoldiMGSW]
  simp only [Nat.min_self]
  rw [mgsW_congr (v := fun i => arnoldiMGS A v₁ (min i j)) (v' := arnoldiMGS A v₁)
    (op A (arnoldiMGS A v₁ j)) fun i hi => by rw [Nat.min_eq_left (Nat.lt_succ_iff.1 hi)]]

/-- §6.3.2: in exact arithmetic Algorithm 6.2 computes the same vectors as Algorithm 6.1. -/
theorem arnoldiMGS_eq_arnoldiCGS (hv : ‖v₁‖ = 1) (j : ℕ) :
    arnoldiMGS A v₁ j = arnoldiCGS A v₁ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [arnoldiMGS_zero, arnoldiCGS_zero]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hle : ∀ i < k + 1, arnoldiMGS A v₁ i = arnoldiCGS A v₁ i := fun i hi => ih i hi
      have hw : arnoldiMGSW A v₁ k = arnoldiW A v₁ k := by
        rw [arnoldiMGSW, mgsW_congr _ hle, hle k k.lt_succ_self,
          mgsW_eq_sub_sum (fun a b hab => inner_arnoldiCGS_eq_zero A v₁ hv hab), arnoldiW]
        rfl
      rw [arnoldiMGS_succ, arnoldiCGS_succ, hw]

/-- §6.3.2: in exact arithmetic Algorithm 6.2 computes the same coefficients as Algorithm 6.1. -/
theorem arnoldiMGSCoeff_eq_arnoldiCoeff (hv : ‖v₁‖ = 1) (i j : ℕ) :
    arnoldiMGSCoeff A v₁ i j = arnoldiCoeff A v₁ i j := by
  have hvec : arnoldiMGS A v₁ = arnoldiCGS A v₁ := funext (arnoldiMGS_eq_arnoldiCGS A v₁ hv)
  have hw : arnoldiMGSW A v₁ j = arnoldiW A v₁ j := by
    rw [arnoldiMGSW, hvec, mgsW_eq_sub_sum (fun a b hab => inner_arnoldiCGS_eq_zero A v₁ hv hab),
      arnoldiW]
    rfl
  rw [arnoldiMGSCoeff, hvec, hw]
  split_ifs with h1 h2
  · rw [inner_mgsW_self (fun a b hab => inner_arnoldiCGS_eq_zero A v₁ hv hab), arnoldiCoeff]
  · rw [h2, arnoldiCoeff_succ_self A v₁ hv]
  · exact (arnoldiCoeff_eq_zero_of_lt A v₁ hv (by omega)).symm

end General

/-! ### Algorithm 6.3: Householder Arnoldi

The book presents Algorithm 6.3 for real matrices, using the real Householder reflectors of
§1.7 ((1.23)–(1.26)); this section follows that convention. Indices are again `0`-based, so
`hhV A v j` is the book's `v_{j+1}`, `hhZ A v j` is `z_{j+1}`, `hhW A v j` is `w_{j+1}`,
`hhH A v j` is `h_j` and `Qhh A v j` is `Q_{j+1} = P_{j+1} ⋯ P_1` of (6.10). -/

section Householder

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- The entry `z_k` of a vector at a natural index, `0` out of range. -/
noncomputable def coordAt (z : 𝔼) (k : ℕ) : ℝ := if h : k < n then z ⟨k, h⟩ else 0

/-- The standard basis vector `e_k`, `0` out of range. -/
noncomputable def stdVec (k : ℕ) : 𝔼 := WithLp.toLp 2 fun i => if (i : ℕ) = k then 1 else 0

/-- The tail `(0, …, 0, z_k, …, z_n)` of `z`; its norm is the book's `(∑_{i ≥ k} z_i²)^{1/2}`. -/
noncomputable def householderTail (z : 𝔼) (k : ℕ) : 𝔼 :=
  WithLp.toLp 2 fun i => if k ≤ (i : ℕ) then z i else 0

/-- Saad (1.25): `β = sign(z_k) (∑_{i ≥ k} z_i²)^{1/2}`, with the convention `sign 0 = 1`. -/
noncomputable def householderBeta (z : 𝔼) (k : ℕ) : ℝ :=
  (if 0 ≤ coordAt z k then 1 else -1) * ‖householderTail z k‖

/-- Saad (1.24): the unnormalized Householder direction `z'` at position `k`. -/
noncomputable def householderDir (z : 𝔼) (k : ℕ) : 𝔼 :=
  WithLp.toLp 2 fun i =>
    if (i : ℕ) < k then 0 else if (i : ℕ) = k then householderBeta z k + z i else z i

/-- Saad (1.26): the Householder unit vector `w = z'/‖z'‖` at position `k`; `0` when `z`
already has the required zero pattern. -/
noncomputable def householderVec (z : 𝔼) (k : ℕ) : 𝔼 :=
  (‖householderDir z k‖⁻¹ : ℝ) • householderDir z k

/-- Saad (1.23): the Householder reflector `P = I - 2 w wᵀ`; the identity when `w = 0`. -/
noncomputable def householder (w : 𝔼) : 𝔼 →ₗ[ℝ] 𝔼 :=
  LinearMap.id - (innerSL ℝ w).toLinearMap.smulRight ((2 : ℝ) • w)

@[simp]
theorem stdVec_coord (k : ℕ) (i : Fin n) : stdVec k i = if (i : ℕ) = k then 1 else 0 := rfl

@[simp]
theorem householderTail_coord (z : 𝔼) (k : ℕ) (i : Fin n) :
    householderTail z k i = if k ≤ (i : ℕ) then z i else 0 := rfl

@[simp]
theorem householderDir_coord (z : 𝔼) (k : ℕ) (i : Fin n) :
    householderDir z k i =
      if (i : ℕ) < k then 0 else if (i : ℕ) = k then householderBeta z k + z i else z i := rfl

private theorem inner_coord (x y : 𝔼) : (inner ℝ x y : ℝ) = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem householderDir_eq (z : 𝔼) (k : ℕ) :
    householderDir z k = householderTail z k + householderBeta z k • stdVec k := by
  ext i
  rcases lt_trichotomy (i : ℕ) k with h | h | h
  · have h1 : ¬ k ≤ (i : ℕ) := by omega
    have h2 : (i : ℕ) ≠ k := by omega
    simp [h, h1, h2]
  · simp [h, add_comm]
  · have h1 : ¬ (i : ℕ) < k := by omega
    have h2 : (i : ℕ) ≠ k := by omega
    have h3 : k ≤ (i : ℕ) := by omega
    simp [h1, h2, h3]

theorem inner_stdVec_left (x : 𝔼) (k : ℕ) : (inner ℝ (stdVec k) x : ℝ) = coordAt x k := by
  rw [inner_coord]
  by_cases h : k < n
  · rw [Finset.sum_eq_single (⟨k, h⟩ : Fin n)]
    · simp [coordAt, h]
    · intro b _ hb
      have hbk : (b : ℕ) ≠ k := fun hc => hb (Fin.ext hc)
      simp [hbk]
    · simp
  · refine (Finset.sum_eq_zero fun i _ => ?_).trans (by simp [coordAt, h])
    have hik : (i : ℕ) ≠ k := by omega
    simp [hik]

theorem norm_householderTail_sq (z : 𝔼) (k : ℕ) :
    ‖householderTail z k‖ ^ 2 = (inner ℝ (householderTail z k) z : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_coord, inner_coord]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : k ≤ (i : ℕ) <;> simp [h]

theorem inner_householderTail_stdVec (z : 𝔼) (k : ℕ) :
    (inner ℝ (householderTail z k) (stdVec k) : ℝ) = coordAt z k := by
  rw [real_inner_comm, inner_stdVec_left, coordAt, coordAt]
  by_cases h : k < n <;> simp [h]

theorem norm_stdVec_sq_of_lt {k : ℕ} (h : k < n) : ‖(stdVec k : 𝔼)‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, inner_stdVec_left, coordAt]
  simp [h]

theorem norm_stdVec_of_lt {k : ℕ} (h : k < n) : ‖(stdVec k : 𝔼)‖ = 1 := by
  have h1 := norm_stdVec_sq_of_lt (n := n) h
  nlinarith [norm_nonneg (stdVec (n := n) k)]

theorem householderBeta_sq (z : 𝔼) (k : ℕ) :
    householderBeta z k ^ 2 = ‖householderTail z k‖ ^ 2 := by
  rw [householderBeta, mul_pow]
  split_ifs <;> norm_num

/-- The identity behind Saad (1.26): `2 (z', z) = ‖z'‖²`. -/
theorem two_inner_householderDir (z : 𝔼) (k : ℕ) :
    2 * (inner ℝ (householderDir z k) z : ℝ) = ‖householderDir z k‖ ^ 2 := by
  by_cases hk : k < n
  · have hS : (inner ℝ (householderTail z k) (householderTail z k) : ℝ)
        = ‖householderTail z k‖ ^ 2 := real_inner_self_eq_norm_sq _
    have hT : (inner ℝ (householderTail z k) (stdVec k) : ℝ) = coordAt z k :=
      inner_householderTail_stdVec z k
    have hT' : (inner ℝ (stdVec k) (householderTail z k) : ℝ) = coordAt z k := by
      rw [real_inner_comm]; exact hT
    have hE : (inner ℝ (stdVec (n := n) k) (stdVec k) : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq]; exact norm_stdVec_sq_of_lt hk
    have hZ : (inner ℝ (stdVec k) z : ℝ) = coordAt z k := inner_stdVec_left z k
    have hb : householderBeta z k ^ 2 = ‖householderTail z k‖ ^ 2 := householderBeta_sq z k
    rw [← real_inner_self_eq_norm_sq, householderDir_eq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [hS, hT, hT', hE, hZ, ← norm_householderTail_sq]
    linear_combination -hb
  · have h0 : householderDir z k = 0 := by
      ext i
      have hi : (i : ℕ) < k := by omega
      simp [hi]
    rw [h0]
    simp

theorem householder_apply (w x : 𝔼) : householder w x = x - (2 * inner ℝ w x) • w := by
  simp [householder, smul_smul, mul_comm]

/-- A vector supported on the coordinates `≥ k` is orthogonal to one supported on `< k`. -/
theorem inner_eq_zero_of_supported {x y : 𝔼} {k : ℕ}
    (hx : ∀ i : Fin n, (i : ℕ) < k → x i = 0) (hy : ∀ i : Fin n, k ≤ (i : ℕ) → y i = 0) :
    (inner ℝ x y : ℝ) = 0 := by
  rw [inner_coord]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases lt_or_ge (i : ℕ) k with h | h
  · rw [hx i h, zero_mul]
  · rw [hy i h, mul_zero]

theorem householder_apply_of_inner_eq_zero {w x : 𝔼} (h : (inner ℝ w x : ℝ) = 0) :
    householder w x = x := by
  rw [householder_apply, h]
  simp

theorem norm_householderVec (z : 𝔼) (k : ℕ) :
    ‖householderVec z k‖ = 1 ∨ householderVec z k = 0 := by
  rcases eq_or_ne (householderDir z k) 0 with h | h
  · right
    rw [householderVec, h, smul_zero]
  · left
    rw [householderVec, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

theorem householder_householder {w : 𝔼} (hw : ‖w‖ = 1 ∨ w = 0) (x : 𝔼) :
    householder w (householder w x) = x := by
  rcases hw with hw | rfl
  · have hww : (inner ℝ w w : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq, hw]; norm_num
    rw [householder_apply, householder_apply, inner_sub_right, real_inner_smul_right, hww]
    module
  · simp [householder_apply]

theorem inner_householder (w x y : 𝔼) :
    (inner ℝ (householder w x) y : ℝ) = inner ℝ x (householder w y) := by
  rw [householder_apply, householder_apply, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm w x, real_inner_comm y w]
  ring

theorem norm_householder_apply {w : 𝔼} (hw : ‖w‖ = 1 ∨ w = 0) (x : 𝔼) :
    ‖householder w x‖ = ‖x‖ := by
  have h : (inner ℝ (householder w x) (householder w x) : ℝ) = inner ℝ x x := by
    rw [inner_householder, householder_householder hw]
  have h2 := congrArg Real.sqrt h
  rwa [real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm,
    Real.sqrt_mul_self (norm_nonneg _), Real.sqrt_mul_self (norm_nonneg _)] at h2

theorem householderVec_coord_of_lt {z : 𝔼} {k : ℕ} {i : Fin n} (h : (i : ℕ) < k) :
    householderVec z k i = 0 := by
  simp [householderVec, h]

/-- Saad (1.26): `P z` keeps the entries of `z` below `k`, puts `-β` at `k` and `0` above. -/
theorem householder_householderVec_apply (z : 𝔼) (k : ℕ) :
    householder (householderVec z k) z = z - householderDir z k := by
  rcases eq_or_ne (householderDir z k) 0 with h | h
  · rw [householderVec, h, smul_zero, householder_apply]
    simp
  · have hn : ‖householderDir z k‖ ≠ 0 := norm_ne_zero_iff.2 h
    have hkey := two_inner_householderDir z k
    have hone : 2 * (‖householderDir z k‖⁻¹ * (inner ℝ (householderDir z k) z : ℝ)) *
        ‖householderDir z k‖⁻¹ = 1 := by
      field_simp
      linarith [hkey]
    rw [householder_apply, householderVec, real_inner_smul_left, smul_smul, hone, one_smul]

theorem householder_householderVec_coord (z : 𝔼) (k : ℕ) (i : Fin n) :
    householder (householderVec z k) z i =
      if (i : ℕ) < k then z i else if (i : ℕ) = k then -householderBeta z k else 0 := by
  rw [householder_householderVec_apply, PiLp.sub_apply, householderDir_coord]
  rcases lt_trichotomy (i : ℕ) k with hi | hi | hi
  · simp [hi]
  · simp [hi]
  · have h1 : ¬ (i : ℕ) < k := by omega
    have h2 : (i : ℕ) ≠ k := by omega
    simp [h1, h2]

/-- A vector supported on the first `N` coordinates is the sum of its coordinates. -/
theorem eq_sum_coordAt_smul_stdVec {x : 𝔼} {N : ℕ} (h : ∀ i : Fin n, N ≤ (i : ℕ) → x i = 0) :
    x = ∑ i ∈ Finset.range N, coordAt x i • stdVec i := by
  ext i'
  rw [sum_coord]
  by_cases hlt : (i' : ℕ) < N
  · rw [Finset.sum_eq_single (i' : ℕ)]
    · simp [coordAt, i'.isLt]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hb
      exact absurd (Finset.mem_range.2 hlt) hb
  · rw [h i' (by omega)]
    refine (Finset.sum_eq_zero fun b hb => ?_).symm
    have hne : (i' : ℕ) ≠ b := by
      have := Finset.mem_range.1 hb
      omega
    simp [hne]

/-- `P_j ∘ ⋯ ∘ P_0` for a family of Householder vectors. -/
noncomputable def hhQAux (w : ℕ → 𝔼) : ℕ → (𝔼 →ₗ[ℝ] 𝔼)
  | 0 => householder (w 0)
  | j + 1 => householder (w (j + 1)) ∘ₗ hhQAux w j

/-- `P_0 ∘ ⋯ ∘ P_j`, the transpose of `hhQAux`. -/
noncomputable def hhQTAux (w : ℕ → 𝔼) : ℕ → (𝔼 →ₗ[ℝ] 𝔼)
  | 0 => householder (w 0)
  | j + 1 => hhQTAux w j ∘ₗ householder (w (j + 1))

private theorem hhQAux_congr {w w' : ℕ → 𝔼} {j : ℕ} (h : ∀ i ≤ j, w i = w' i) :
    hhQAux w j = hhQAux w' j := by
  induction j with
  | zero => rw [hhQAux, hhQAux, h 0 le_rfl]
  | succ j ih => rw [hhQAux, hhQAux, ih fun i hi => h i (hi.trans j.le_succ), h (j + 1) le_rfl]

private theorem hhQTAux_congr {w w' : ℕ → 𝔼} {j : ℕ} (h : ∀ i ≤ j, w i = w' i) :
    hhQTAux w j = hhQTAux w' j := by
  induction j with
  | zero => rw [hhQTAux, hhQTAux, h 0 le_rfl]
  | succ j ih => rw [hhQTAux, hhQTAux, ih fun i hi => h i (hi.trans j.le_succ), h (j + 1) le_rfl]

/-- **Algorithm 6.3** (Householder Arnoldi), `0`-based: the auxiliary vectors `z_j`, with
`z_0 = v` and `z_{j+1} = P_j ⋯ P_0 A v_j`. As in Algorithm 6.2 the clamp `min i j` is
invisible: only the reflectors `P_0, …, P_j` are used. -/
noncomputable def hhZ (A : Matrix (Fin n) (Fin n) ℝ) (v : 𝔼) : ℕ → 𝔼
  | 0 => v
  | j + 1 =>
    let w : ℕ → 𝔼 := fun i => householderVec (hhZ A v (min i j)) (min i j)
    hhQAux w j (op A (hhQTAux w j (stdVec j)))
  termination_by j => j
  decreasing_by exact Nat.lt_succ_of_le (Nat.min_le_right _ _)

variable (A : Matrix (Fin n) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n))

/-- The Householder unit vectors `w_j` of Algorithm 6.3, lines 3–5. -/
noncomputable def hhW (j : ℕ) : 𝔼 := householderVec (hhZ A v j) j

/-- (6.10): `Q_j = P_j ⋯ P_1`. -/
noncomputable def Qhh (j : ℕ) : 𝔼 →ₗ[ℝ] 𝔼 := hhQAux (hhW A v) j

/-- `Q_jᵀ = P_1 ⋯ P_j`, the inverse of `Qhh` (P-6.1(a),(b)). -/
noncomputable def QhhT (j : ℕ) : 𝔼 →ₗ[ℝ] 𝔼 := hhQTAux (hhW A v) j

/-- Algorithm 6.3, line 7: `v_j = P_1 P_2 ⋯ P_j e_j`. -/
noncomputable def hhV (j : ℕ) : 𝔼 := QhhT A v j (stdVec j)

/-- Algorithm 6.3, line 6: `h_{j-1} = P_j z_j`, the `j`-th column of the Householder
factorization (6.12). -/
noncomputable def hhH (j : ℕ) : 𝔼 := householder (hhW A v j) (hhZ A v j)

theorem Qhh_zero : Qhh A v 0 = householder (hhW A v 0) := rfl

theorem Qhh_succ (j : ℕ) : Qhh A v (j + 1) = householder (hhW A v (j + 1)) ∘ₗ Qhh A v j := rfl

theorem QhhT_zero : QhhT A v 0 = householder (hhW A v 0) := rfl

theorem QhhT_succ (j : ℕ) : QhhT A v (j + 1) = QhhT A v j ∘ₗ householder (hhW A v (j + 1)) := rfl

@[simp]
theorem hhZ_zero : hhZ A v 0 = v := by rw [hhZ]

theorem hhZ_succ (j : ℕ) : hhZ A v (j + 1) = Qhh A v j (op A (hhV A v j)) := by
  rw [hhZ]
  have hw : ∀ i ≤ j, householderVec (hhZ A v (min i j)) (min i j) = hhW A v i := by
    intro i hi
    rw [Nat.min_eq_left hi, hhW]
  rw [hhQAux_congr (w' := hhW A v) hw, hhQTAux_congr (w' := hhW A v) hw]
  rfl

theorem norm_hhW (j : ℕ) : ‖hhW A v j‖ = 1 ∨ hhW A v j = 0 := norm_householderVec _ _

theorem hhW_coord_of_lt {j : ℕ} {i : Fin n} (h : (i : ℕ) < j) : hhW A v j i = 0 :=
  householderVec_coord_of_lt h

/-- Each `P_j` fixes every vector supported in the coordinates below `j`. -/
theorem householder_hhW_apply_of_supported {j : ℕ} {x : 𝔼}
    (hx : ∀ i : Fin n, j ≤ (i : ℕ) → x i = 0) : householder (hhW A v j) x = x :=
  householder_apply_of_inner_eq_zero
    (inner_eq_zero_of_supported (fun _ hi => hhW_coord_of_lt A v hi) hx)

theorem householder_hhW_stdVec {i j : ℕ} (h : i < j) :
    householder (hhW A v j) (stdVec i) = stdVec i := by
  refine householder_hhW_apply_of_supported A v fun i' hi' => ?_
  have hne : (i' : ℕ) ≠ i := by omega
  simp [hne]

/-- P-6.1(a),(b): `Q_j` is orthogonal with inverse `Q_jᵀ = P_1 ⋯ P_j`. -/
theorem QhhT_Qhh (j : ℕ) (x : 𝔼) : QhhT A v j (Qhh A v j x) = x := by
  induction j with
  | zero => exact householder_householder (norm_hhW A v 0) x
  | succ j ih =>
    rw [QhhT_succ, Qhh_succ, LinearMap.comp_apply, LinearMap.comp_apply,
      householder_householder (norm_hhW A v (j + 1))]
    exact ih

theorem Qhh_QhhT (j : ℕ) (x : 𝔼) : Qhh A v j (QhhT A v j x) = x := by
  induction j generalizing x with
  | zero => exact householder_householder (norm_hhW A v 0) x
  | succ j ih =>
    rw [QhhT_succ, Qhh_succ, LinearMap.comp_apply, LinearMap.comp_apply, ih,
      householder_householder (norm_hhW A v (j + 1))]

theorem norm_Qhh_apply (j : ℕ) (x : 𝔼) : ‖Qhh A v j x‖ = ‖x‖ := by
  induction j with
  | zero => exact norm_householder_apply (norm_hhW A v 0) x
  | succ j ih =>
    rw [Qhh_succ, LinearMap.comp_apply, norm_householder_apply (norm_hhW A v (j + 1)), ih]

theorem norm_QhhT_apply (j : ℕ) (x : 𝔼) : ‖QhhT A v j x‖ = ‖x‖ := by
  induction j generalizing x with
  | zero => exact norm_householder_apply (norm_hhW A v 0) x
  | succ j ih =>
    rw [QhhT_succ, LinearMap.comp_apply, ih, norm_householder_apply (norm_hhW A v (j + 1))]

theorem inner_QhhT (j : ℕ) (x y : 𝔼) :
    (inner ℝ (QhhT A v j x) (QhhT A v j y) : ℝ) = inner ℝ x y := by
  induction j generalizing x y with
  | zero => rw [QhhT_zero, inner_householder, householder_householder (norm_hhW A v 0)]
  | succ j ih =>
    rw [QhhT_succ, LinearMap.comp_apply, LinearMap.comp_apply, ih, inner_householder,
      householder_householder (norm_hhW A v (j + 1))]

/-- (6.13), P-6.1(c): `Q_{j+1}ᵀ e_i = v_i` for `i ≤ j + 1`. -/
theorem eq_6_13 {i j : ℕ} (h : i ≤ j) : QhhT A v j (stdVec i) = hhV A v i := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := Nat.le_zero.1 h
    rfl
  | succ j ih =>
    rcases eq_or_lt_of_le h with rfl | h'
    · rfl
    · rw [QhhT_succ, LinearMap.comp_apply, householder_hhW_stdVec A v h']
      exact ih (Nat.lt_succ_iff.1 h')

/-- The `j`-th column `h_j` of (6.12) has zeros below the diagonal position `j`. -/
theorem hhH_coord_of_lt (j : ℕ) {i : Fin n} (h : j < (i : ℕ)) : hhH A v j i = 0 := by
  rw [hhH, hhW, householder_householderVec_coord]
  have h1 : ¬ (i : ℕ) < j := by omega
  have h2 : (i : ℕ) ≠ j := by omega
  simp [h1, h2]

theorem householder_hhW_hhH {i j : ℕ} (h : j < i) :
    householder (hhW A v i) (hhH A v j) = hhH A v j :=
  householder_hhW_apply_of_supported A v fun _ hi => hhH_coord_of_lt A v j (by omega)

/-- (6.11): `h_j = Q_{j+1} A v_j`. -/
theorem eq_6_11 (j : ℕ) : hhH A v (j + 1) = Qhh A v (j + 1) (op A (hhV A v j)) := by
  rw [hhH, hhZ_succ, Qhh_succ, LinearMap.comp_apply]

/-- (6.12): `Q_m [v, A v_1, …, A v_m] = [h_0, h_1, …, h_m]`, first column. -/
theorem eq_6_12_zero (m : ℕ) : Qhh A v m v = hhH A v 0 := by
  induction m with
  | zero => rw [Qhh_zero, hhH, hhZ_zero]
  | succ m ih => rw [Qhh_succ, LinearMap.comp_apply, ih, householder_hhW_hhH A v (by omega)]

/-- (6.12): `Q_m [v, A v_1, …, A v_m] = [h_0, h_1, …, h_m]`, the later columns. Together with
`hhH_coord_of_lt` this says that the factorization is upper triangular. -/
theorem eq_6_12 {j m : ℕ} (h : j + 1 ≤ m) :
    Qhh A v m (op A (hhV A v j)) = hhH A v (j + 1) := by
  induction m, h using Nat.le_induction with
  | base => exact (eq_6_11 A v j).symm
  | succ m hm ih =>
    rw [Qhh_succ, LinearMap.comp_apply, ih, householder_hhW_hhH A v (by omega)]

/-- The Hessenberg coefficients of the Householder basis: `H̄^{HH}_{ij} = (h_{j+1})_i`. -/
noncomputable def hhCoeff (i j : ℕ) : ℝ := coordAt (hhH A v (j + 1)) i

theorem hhCoeff_eq_zero_of_lt {i j : ℕ} (h : j + 1 < i) : hhCoeff A v i j = 0 := by
  rw [hhCoeff, coordAt]
  split_ifs with hi
  · exact hhH_coord_of_lt A v (j + 1) (by simpa using h)
  · rfl

/-- P-6.1(d): the Householder Arnoldi vectors satisfy the Hessenberg relation, hence
`A V_m = V_{m+1} H̄_m`. -/
theorem hh_hessenbergRelation :
    Krylov.HessenbergRelation (op A) (hhV A v) (hhCoeff A v) := by
  refine ⟨fun j => ?_, fun i j hij => hhCoeff_eq_zero_of_lt A v hij⟩
  have hzero : ∀ i : Fin n, j + 2 ≤ (i : ℕ) → hhH A v (j + 1) i = 0 :=
    fun i hi => hhH_coord_of_lt A v (j + 1) (by omega)
  have hAv : op A (hhV A v j) = QhhT A v (j + 1) (hhH A v (j + 1)) := by
    rw [eq_6_11, QhhT_Qhh]
  rw [hAv, eq_sum_coordAt_smul_stdVec hzero, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, eq_6_13 A v (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
  rfl

/-- `V^{HH}_m`, the matrix of the first `m` Householder Arnoldi vectors. -/
noncomputable def VHH (m : ℕ) : Matrix (Fin n) (Fin m) ℝ := colMatrix (hhV A v) m

/-- `H̄^{HH}_m`, the `(m+1) × m` Hessenberg matrix of the Householder Arnoldi coefficients. -/
noncomputable def HbarHH (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℝ :=
  Krylov.hessenbergOf (hhCoeff A v) m

/-- P-6.1(d): `A V_m = V_{m+1} H̄_m` for the Householder Arnoldi basis. -/
theorem hh_arnoldi_relation (m : ℕ) : A * VHH A v m = VHH A v (m + 1) * HbarHH A v m :=
  mul_colMatrix_eq A (hh_hessenbergRelation A v) m

/-- P-6.1(e): the Householder Arnoldi vectors are orthonormal. -/
theorem inner_hhV {i j : ℕ} (hi : i < n) :
    (inner ℝ (hhV A v i) (hhV A v j) : ℝ) = if i = j then 1 else 0 := by
  have h := inner_QhhT A v (max i j) (stdVec i) (stdVec j)
  rw [eq_6_13 A v (le_max_left i j), eq_6_13 A v (le_max_right i j)] at h
  rw [h, inner_stdVec_left]
  simp [coordAt, hi]

theorem norm_hhV {i : ℕ} (h : i < n) : ‖hhV A v i‖ = 1 := by
  rw [hhV, norm_QhhT_apply, norm_stdVec_of_lt h]

/-- P-6.1(e): `v_1, …, v_m` are orthonormal (`m ≤ n` Householder steps). -/
theorem hh_orthonormal {m : ℕ} (hm : m ≤ n) :
    Orthonormal ℝ (fun i : Fin m => hhV A v (i : ℕ)) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · dsimp only
    exact norm_hhV A v (lt_of_lt_of_le i.2 hm)
  · have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.val_injective h)
    dsimp only
    rw [inner_hhV A v (lt_of_lt_of_le i.2 hm)]
    simp [hne]

/-- The first column of the factorization (6.12) is `-β e_1` with `|β| = ‖v‖`: this is the
`β = ±‖r_0‖` of Householder GMRES (Algorithm 6.10). -/
theorem hhH_zero : hhH A v 0 = (-householderBeta v 0) • stdVec 0 := by
  ext i
  rw [hhH, hhZ_zero, hhW, hhZ_zero, householder_householderVec_coord, PiLp.smul_apply,
    stdVec_coord]
  simp

theorem abs_householderBeta_zero : |householderBeta v 0| = ‖v‖ := by
  have htail : householderTail v 0 = v := by
    ext i
    simp
  rw [householderBeta, htail, abs_mul, abs_of_nonneg (norm_nonneg _)]
  split_ifs <;> simp

/-- `v = -β v_1`: the first Householder Arnoldi vector is `± v / ‖v‖`. -/
theorem smul_hhV_zero : (-householderBeta v 0) • hhV A v 0 = v := by
  have h : householder (hhW A v 0) (hhH A v 0) = v := by
    rw [hhH, householder_householder (norm_hhW A v 0), hhZ_zero]
  rw [hhH_zero, map_smul] at h
  exact h

/-! #### The Householder flag and comparison with Gram–Schmidt Arnoldi -/

private theorem span_hhV_mono {i j : ℕ} (h : i ≤ j) :
    Submodule.span ℝ (hhV A v '' Set.Iio i) ≤ Submodule.span ℝ (hhV A v '' Set.Iio j) :=
  Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))

private theorem map_span_hhV_le (i : ℕ) :
    Submodule.map (op A) (Submodule.span ℝ (hhV A v '' Set.Iio (i + 1)))
      ≤ Submodule.span ℝ (hhV A v '' Set.Iio (i + 2)) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  have hl' : l < i + 1 := hl
  rw [SetLike.mem_coe, (hh_hessenbergRelation A v).apply_eq l]
  refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
  rw [Finset.mem_range] at hk
  exact Submodule.subset_span ⟨k, show k < i + 2 by omega, rfl⟩

private theorem pow_apply_mem_span_hhV (i : ℕ) :
    (op A ^ i) v ∈ Submodule.span ℝ (hhV A v '' Set.Iio (i + 1)) := by
  induction i with
  | zero =>
    have h0 : hhV A v 0 ∈ Submodule.span ℝ (hhV A v '' Set.Iio 1) :=
      Submodule.subset_span ⟨0, by simp, rfl⟩
    have h1 := Submodule.smul_mem _ (-householderBeta v 0) h0
    rw [smul_hhV_zero A v] at h1
    simpa using h1
  | succ i ih =>
    have hstep : (op A ^ (i + 1)) v = op A ((op A ^ i) v) := by
      rw [pow_succ']
      rfl
    rw [hstep]
    exact map_span_hhV_le A v i ⟨_, ih, rfl⟩

/-- The Krylov subspace is contained in the span of the Householder Arnoldi vectors; this half
of the flag identity needs no hypothesis. -/
theorem krylov_le_span_hhV (m : ℕ) :
    krylov A v m ≤ Submodule.span ℝ (hhV A v '' Set.Iio m) := by
  rw [krylov_eq, Krylov.subspace, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact span_hhV_mono A v (by omega) (pow_apply_mem_span_hhV A v (i : ℕ))

/-- (6.12) in span form: as long as `m` Householder steps fit (`m ≤ n`) and the grade of `v` is
at least `m`, the first `m` Householder Arnoldi vectors span `𝒦_m(A, v)`. -/
theorem span_hhV_eq {m : ℕ} (hmn : m ≤ n) (hmg : m ≤ grade A v) :
    Submodule.span ℝ (hhV A v '' Set.Iio m) = krylov A v m := by
  have hfin : Module.finrank ℝ (Submodule.span ℝ (hhV A v '' Set.Iio m)) = m := by
    rw [← range_fin_eq_image_Iio]
    simpa using finrank_span_eq_card (hh_orthonormal A v hmn).linearIndependent
  have hk : Module.finrank ℝ (krylov A v m) = m := by rw [finrank_krylov, min_eq_left hmg]
  exact (Submodule.eq_of_le_of_finrank_le (krylov_le_span_hhV A v m) (by rw [hfin, hk])).symm

/-- P-6.1(f): the Householder Arnoldi vectors agree with the Gram–Schmidt Arnoldi vectors of
Algorithm 6.1 up to a sign, as long as `m + 1` steps fit and the grade of `v` allows them. -/
theorem hh_eq_arnoldi_up_to_sign (hv : v ≠ 0) {m : ℕ} (hmn : m + 1 ≤ n)
    (hmg : m + 1 ≤ grade A v) :
    ∃ ε : ℕ → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ j ≤ m, hhV A v j = ε j • arnoldiCGS A (‖v‖⁻¹ • v) j := by
  classical
  have hnorm : ∀ i, arnoldiCGS A (‖v‖⁻¹ • v) i = Arnoldi.vec (op A) v i :=
    arnoldiCGS_normalize A hv
  refine ⟨fun j => if (inner ℝ (Arnoldi.vec (op A) v j) (hhV A v j) : ℝ) < 0 then -1 else 1,
    fun j => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact Or.inr rfl
    · exact Or.inl rfl
  intro j hj
  dsimp only
  have hmem : hhV A v j ∈ Krylov.subspace (op A) v (j + 1) := by
    rw [← krylov_eq, ← span_hhV_eq A v (by omega) (by omega)]
    exact Submodule.subset_span ⟨j, Nat.lt_succ_self j, rfl⟩
  have hperp : hhV A v j ∈ (Krylov.subspace (op A) v j)ᗮ := by
    rw [← krylov_eq, ← span_hhV_eq A v (by omega) (by omega), Submodule.mem_orthogonal_span]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < j := hk
    rw [inner_hhV A v (show k < n by omega)]
    simp [Nat.ne_of_lt hk']
  have hzero : ∀ i ∈ Finset.range (j + 1), i ≠ j →
      (inner ℝ (Arnoldi.vec (op A) v i) (hhV A v j) : ℝ) • Arnoldi.vec (op A) v i = 0 := by
    intro i hi hij
    have hlt : i < j := by
      rw [Finset.mem_range] at hi
      omega
    rw [(Submodule.mem_orthogonal _ _).1 hperp _ (Arnoldi.vec_mem_subspace_of_lt (op A) v hlt),
      zero_smul]
  have hsum : ∑ i ∈ Finset.range (j + 1),
      (inner ℝ (Arnoldi.vec (op A) v i) (hhV A v j) : ℝ) • Arnoldi.vec (op A) v i
      = (inner ℝ (Arnoldi.vec (op A) v j) (hhV A v j) : ℝ) • Arnoldi.vec (op A) v j :=
    Finset.sum_eq_single j hzero fun hb =>
      absurd (Finset.mem_range.2 (Nat.lt_succ_self j)) hb
  have hsingle : hhV A v j
      = (inner ℝ (Arnoldi.vec (op A) v j) (hhV A v j) : ℝ) • Arnoldi.vec (op A) v j :=
    (Arnoldi.eq_sum_inner_smul_vec (op A) v hmem).trans hsum
  have hnu : ‖Arnoldi.vec (op A) v j‖ = 1 :=
    Arnoldi.norm_vec_eq_one_of_lt_grade (op A) v (by rw [← grade_eq]; omega)
  have hnv : ‖hhV A v j‖ = 1 := norm_hhV A v (by omega)
  have habs : |(inner ℝ (Arnoldi.vec (op A) v j) (hhV A v j) : ℝ)| = 1 := by
    have hc := congrArg norm hsingle
    rwa [hnv, norm_smul, hnu, mul_one, Real.norm_eq_abs, eq_comm] at hc
  have hif : (if (inner ℝ (Arnoldi.vec (op A) v j) (hhV A v j) : ℝ) < 0 then (-1 : ℝ) else 1)
      = (inner ℝ (Arnoldi.vec (op A) v j) (hhV A v j) : ℝ) := by
    rcases (abs_eq (le_of_lt one_pos)).1 habs with h1 | h1 <;> rw [h1] <;> norm_num
  rw [hif, hnorm j]
  exact hsingle

end Householder

/-! ### The numbered results of §6.3, in the book's real setting -/

section BookResults

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : EuclideanSpace ℝ (Fin n))

/-- **Proposition 6.4**. If Algorithm 6.1 does not break down before step `m`, then the vectors
`v_1, …, v_m` form an orthonormal basis of `𝒦_m = span {v_1, A v_1, …, A^{m-1} v_1}`. -/
theorem prop_6_4 (hv : ‖v₁‖ = 1) {m : ℕ} (h : NoBreakdownBefore A v₁ m) :
    Orthonormal ℝ (fun i : Fin m => arnoldiCGS A v₁ (i : ℕ)) ∧
      Submodule.span ℝ (Set.range fun i : Fin m => arnoldiCGS A v₁ (i : ℕ)) = krylov A v₁ m :=
  ⟨orthonormal_arnoldiCGS A v₁ hv ((noBreakdownBefore_iff A v₁ hv m).1 h),
    span_arnoldiCGS A v₁ hv m⟩

/-- (6.9): `A v_j = ∑_{i=1}^{j+1} h_{ij} v_i`. -/
theorem eq_6_9 (hv : ‖v₁‖ = 1) (j : ℕ) :
    op A (arnoldiCGS A v₁ j)
      = ∑ i ∈ Finset.range (j + 2), arnoldiCoeff A v₁ i j • arnoldiCGS A v₁ i :=
  apply_arnoldiCGS A v₁ hv j

/-- (6.7), **Proposition 6.5**: `A V_m = V_{m+1} H̄_m`. -/
theorem eq_6_7 (hv : ‖v₁‖ = 1) (m : ℕ) : A * V A v₁ m = V A v₁ (m + 1) * Hbar A v₁ m :=
  mul_V_eq A v₁ hv m

/-- (6.6), **Proposition 6.5**: `A V_m = V_m H_m + w_m e_mᵀ`. -/
theorem eq_6_6 (hv : ‖v₁‖ = 1) (m : ℕ) :
    A * V A v₁ (m + 1) = V A v₁ (m + 1) * H A v₁ (m + 1) +
      Matrix.vecMulVec (WithLp.ofLp (arnoldiW A v₁ m)) (Pi.single (Fin.last m) 1) :=
  mul_V_eq_add_vecMulVec A v₁ hv m

/-- (6.8), **Proposition 6.5**: `V_mᵀ A V_m = H_m`. -/
theorem eq_6_8 (m : ℕ) : (V A v₁ m)ᵀ * A * V A v₁ m = H A v₁ m := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact conjTranspose_V_mul_mul_V A v₁ m

/-- **Proposition 6.6**. Arnoldi's method breaks down at step `j`, that is `h_{j+1,j} = 0` while
no earlier step broke down, if and only if the minimal polynomial of `v_1` has degree `j`. -/
theorem prop_6_6 (hv : ‖v₁‖ = 1) {j : ℕ} (hj : 0 < j) :
    (NoBreakdownBefore A v₁ j ∧ arnoldiCoeff A v₁ j (j - 1) = 0) ↔ grade A v₁ = j :=
  breakdown_iff_grade_eq A v₁ hv hj

/-- **Proposition 6.6**, second part: at a breakdown at step `j` the subspace `𝒦_j` is
invariant under `A`. -/
theorem prop_6_6' (hv : ‖v₁‖ = 1) {j : ℕ} (hj : 0 < j)
    (h : NoBreakdownBefore A v₁ j ∧ arnoldiCoeff A v₁ j (j - 1) = 0) :
    krylov A v₁ j ∈ Module.End.invtSubmodule (op A) :=
  krylov_mem_invtSubmodule_of_breakdown A v₁ ((prop_6_6 A v₁ hv hj).1 h).le

variable {A}

/-- The corollary of Proposition 6.6 stated in the text: a projection method onto `𝒦_j(A, r_0)`
is exact once Arnoldi has broken down at step `j`. This is Proposition 5.6 applied to the
invariant subspace `𝒦_j`. -/
theorem lucky_breakdown {j : ℕ} (hj : 0 < j) {b x₀ x : EuclideanSpace ℝ (Fin n)}
    {L : Submodule ℝ (EuclideanSpace ℝ (Fin n))} (hbreak : grade A (b - op A x₀) ≤ j)
    (hKL : ∀ z ∈ krylov A (b - op A x₀) j, z ∈ Lᗮ → z = 0)
    (hx : IsPetrovGalerkin (op A) b x₀ (krylov A (b - op A x₀) j) L x) :
    op A x = b :=
  hx.eq_of_invt (krylov_mem_invtSubmodule_of_breakdown A _ hbreak)
    (self_mem_krylov A _ hj) hKL

variable (A)

/-- §6.3.2: **Algorithm 6.2 is mathematically equivalent to Algorithm 6.1** — in exact
arithmetic the two produce the same vectors and the same coefficients. -/
theorem alg_6_2_eq_alg_6_1 (hv : ‖v₁‖ = 1) :
    arnoldiMGS A v₁ = arnoldiCGS A v₁ ∧ arnoldiMGSCoeff A v₁ = arnoldiCoeff A v₁ :=
  ⟨funext (arnoldiMGS_eq_arnoldiCGS A v₁ hv),
    funext fun i => funext fun j => arnoldiMGSCoeff_eq_arnoldiCoeff A v₁ hv i j⟩

end BookResults

end SaadSparse.Ch06
