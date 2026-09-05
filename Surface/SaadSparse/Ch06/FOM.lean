import SaadSparse.Ch06.Arnoldi

/-!
# Saad, §6.4: the Full Orthogonalization Method

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §6.4.

The Full Orthogonalization Method (6.16)–(6.17), Algorithm 6.4, is `fom`; `fomFixed` is the
same formula with a prescribed number of Arnoldi steps, and `fomRestarted` is FOM(m),
Algorithm 6.5. The heart of the section is `fomFixed_isGalerkinIterate`: the book's
`x_m = x_0 + V_m H_m^{-1}(β e_1)` *is* the backbone Galerkin iterate
`Krylov.IsGalerkinIterate` on `𝒦_m(A, r_0)`, and Proposition 6.7 with (6.18) is read off from
the backbone residual formula through that identification.

§6.4.2 is algorithm-only material: the incomplete orthogonalization procedure IOP
(Algorithm 6.6) is `iop`, IOM (Algorithm 6.7) is `iom`, and DIOM (Algorithm 6.8) is `diom`
with the Hessenberg LU factorization `dioU`, `dioL`, the auxiliary vectors `diomP` and the
scalars `diomZeta`. These satisfy no global variational specification; what the book proves
about them is proved here directly. The single structural fact they share with Arnoldi is the
Hessenberg relation `iop_hessenbergRelation`, which is exactly the backbone interface
`Krylov.HessenbergRelation` — the book's "(6.6) is still valid, since orthogonality was never
used".

Indices are `0`-based as in `Ch06/Arnoldi.lean`: `iop A v₁ k j` is the book's `v_{j+1}`, and
`iopCoeff A v₁ k i j` is `h_{i+1,j+1}`. Division by a vanishing norm is `0`, which reproduces
the book's "if `h_{j+1,j} = 0` then Stop", and the book's "set `m := j`" is `mEff` for FOM and
`iomSteps` for IOM.

Definitions are polymorphic in `𝕜`; the numbered results are stated over `ℝ`, the book's
generality in §6.4, as one-line specializations of field-agnostic companions.
-/

open scoped Matrix

namespace SaadSparse.Ch06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### The data of a linear system

The book's `r_0 = b - A x_0`, `β = ‖r_0‖₂` and `v_1 = r_0/β`. The backbone indexes the Arnoldi
process by `r_0` itself; the `*_v₁` lemmas below are the translation, and they are the reason
`Ch06/Arnoldi.lean` provides the normalization family `arnoldiCGS_normalize` and friends. -/

/-- The initial residual `r_0 = b - A x_0` (§6.4, Algorithm 6.4, line 1). -/
def r₀ (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : 𝔼 := b - op A x₀

/-- `β = ‖r_0‖₂` (Algorithm 6.4, line 1). -/
noncomputable def β (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : ℝ := ‖r₀ A b x₀‖

/-- `v_1 = r_0/β`, the starting vector of the Arnoldi process (Algorithm 6.4, line 1). -/
noncomputable def v₁ (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) : 𝔼 :=
  (β A b x₀ : 𝕜)⁻¹ • r₀ A b x₀

/-- The first coordinate vector `e_1 ∈ 𝕜^m`. -/
def e₁ (m : ℕ) : Fin m → 𝕜 := fun i => if (i : ℕ) = 0 then 1 else 0

/-- `β e_1` is the backbone's `Krylov.firstVec β`. -/
theorem smul_e₁_eq_firstVec (c : 𝕜) (m : ℕ) : c • e₁ m = Krylov.firstVec c m := by
  funext i
  by_cases h : (i : ℕ) = 0 <;> simp [e₁, Krylov.firstVec, h]

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

theorem r₀_def : r₀ A b x₀ = b - op A x₀ := rfl

theorem β_def : (β A b x₀ : 𝕜) = (‖b - op A x₀‖ : 𝕜) := rfl

theorem v₁_def : v₁ A b x₀ = (‖b - op A x₀‖ : 𝕜)⁻¹ • (b - op A x₀) := rfl

/-- `‖v_1‖ = 1` unless `x_0` already solves the system. -/
theorem norm_v₁ (hr : b - op A x₀ ≠ 0) : ‖v₁ A b x₀‖ = 1 := by
  rw [v₁_def]
  exact norm_norm_inv_smul hr

/-- Algorithm 6.4 runs Algorithm 6.1 on `v_1 = r_0/β`; the backbone runs it on `r_0`. -/
theorem arnoldiCGS_v₁ (hr : b - op A x₀ ≠ 0) :
    arnoldiCGS A (v₁ A b x₀) = Arnoldi.vec (op A) (b - op A x₀) := by
  rw [v₁_def]
  exact funext (arnoldiCGS_normalize A hr)

theorem arnoldiCoeff_v₁ (hr : b - op A x₀ ≠ 0) (i j : ℕ) :
    arnoldiCoeff A (v₁ A b x₀) i j = Arnoldi.coeff (op A) (b - op A x₀) i j := by
  rw [v₁_def]
  exact arnoldiCoeff_normalize A hr i j

theorem H_v₁ (hr : b - op A x₀ ≠ 0) (m : ℕ) :
    H A (v₁ A b x₀) m = Arnoldi.hessenbergSq (op A) (b - op A x₀) m := by
  rw [v₁_def]
  exact H_normalize A hr m

theorem Hbar_v₁ (hr : b - op A x₀ ≠ 0) (m : ℕ) :
    Hbar A (v₁ A b x₀) m = Arnoldi.hessenberg (op A) (b - op A x₀) m := by
  rw [v₁_def]
  exact Hbar_normalize A hr m

/-- The grade of `v_1` is the grade of `r_0`: the two starting vectors are proportional. -/
theorem grade_v₁ : grade A (v₁ A b x₀) = Krylov.grade (op A) (b - op A x₀) := by
  rcases eq_or_ne (b - op A x₀) 0 with h | h
  · rw [v₁_def, h, smul_zero, grade_eq]
  · rw [v₁_def, grade_smul A _ (inv_ne_zero (by simpa using norm_ne_zero_iff.2 h)), grade_eq]

/-! ### (6.16)–(6.17) and Algorithm 6.4 -/

/-- `y_m = H_m^{-1}(β e_1)` (6.17). `Matrix.inv` is `0` at a singular `H_m`, which is the
book's breakdown case. -/
noncomputable def fomY (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : Fin m → 𝕜 :=
  (H A (v₁ A b x₀) m)⁻¹ *ᵥ ((β A b x₀ : 𝕜) • e₁ m)

/-- (6.16)–(6.17) with exactly `m` steps of Algorithm 6.1: `x_m = x_0 + V_m y_m`. -/
noncomputable def fomFixed (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : 𝔼 :=
  x₀ + Matrix.toEuclideanLin (V A (v₁ A b x₀) m) (WithLp.toLp 2 (fomY A b x₀ m))

/-- The number of Arnoldi steps Algorithm 6.4 actually performs: the book's "if `h_{j+1,j} = 0`
then set `m := j`" stops the Arnoldi process at the grade of `v_1`. -/
noncomputable def mEff (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : ℕ :=
  min m (grade A (v₁ A b x₀))

/-- **Algorithm 6.4** (FOM). -/
noncomputable def fom (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : 𝔼 :=
  fomFixed A b x₀ (mEff A b x₀ m)

/-- FOM is *defined* at step `m` exactly when `H_m` is nonsingular (§6.4.1). -/
def FOMDefined (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : Prop :=
  IsUnit (H A (v₁ A b x₀) m)

theorem mEff_le (m : ℕ) : mEff A b x₀ m ≤ grade A (v₁ A b x₀) := min_le_right _ _

/-- Nothing happens at step `0`. -/
theorem fomFixed_zero : fomFixed A b x₀ 0 = x₀ := by
  rw [fomFixed, toEuclideanLin_V_apply]
  simp

/-- Below the grade of `v_1` the system is not yet solved. -/
private theorem residual_ne_zero_of_lt_grade {m : ℕ} (hm0 : 0 < m)
    (hm : m ≤ grade A (v₁ A b x₀)) : b - op A x₀ ≠ 0 := by
  intro hr
  rw [grade_v₁, hr, Krylov.grade_zero] at hm
  omega

/-- `x_m - x_0 = V_m y_m = ∑_j (y_m)_j v_j`, the form the backbone uses. -/
theorem fomFixed_eq_add_sum (hr : b - op A x₀ ≠ 0) (m : ℕ) :
    fomFixed A b x₀ m
      = x₀ + ∑ j, fomY A b x₀ m j • Arnoldi.vec (op A) (b - op A x₀) (j : ℕ) := by
  rw [fomFixed, toEuclideanLin_V_apply, arnoldiCGS_v₁ A b x₀ hr]

/-- `H_m y_m = β e_1` whenever `H_m` is nonsingular: `y_m` really solves (6.17). -/
theorem H_mulVec_fomY {m : ℕ} (hH : FOMDefined A b x₀ m) :
    H A (v₁ A b x₀) m *ᵥ fomY A b x₀ m = Krylov.firstVec (β A b x₀ : 𝕜) m := by
  rw [fomY, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hH), Matrix.one_mulVec,
    smul_e₁_eq_firstVec]

/-- **(6.16)–(6.17)**: the FOM iterate is the Galerkin iterate on `𝒦_m(A, r_0)`, the
orthogonal projection method (6.15) of §6.4.1. -/
theorem fomFixed_isGalerkinIterate {m : ℕ} (hH : FOMDefined A b x₀ m)
    (hm : m ≤ grade A (v₁ A b x₀)) :
    Krylov.IsGalerkinIterate (op A) b x₀ m (fomFixed A b x₀ m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · rw [fomFixed_zero]
    exact ⟨by simp, by
      rw [Krylov.subspace_zero, Submodule.bot_orthogonal_eq_top]; exact Submodule.mem_top⟩
  · have hr : b - op A x₀ ≠ 0 := residual_ne_zero_of_lt_grade A b x₀ hm0 hm
    have hgr : m ≤ Krylov.grade (op A) (b - op A x₀) := by rwa [← grade_v₁]
    have hy : Arnoldi.hessenbergSq (op A) (b - op A x₀) m *ᵥ fomY A b x₀ m
        = Krylov.firstVec (‖b - op A x₀‖ : 𝕜) m := by
      rw [← H_v₁ A b x₀ hr]
      exact H_mulVec_fomY A b x₀ hH
    have h := (Krylov.isGalerkinIterate_iff_mulVec_eq hgr (fomY A b x₀ m)).2 hy
    rwa [← fomFixed_eq_add_sum A b x₀ hr m] at h

/-- Algorithm 6.4 with its own stopping rule always produces a Galerkin iterate. -/
theorem fom_isGalerkinIterate {m : ℕ} (hH : FOMDefined A b x₀ (mEff A b x₀ m)) :
    Krylov.IsGalerkinIterate (op A) b x₀ (mEff A b x₀ m) (fom A b x₀ m) :=
  fomFixed_isGalerkinIterate A b x₀ hH (mEff_le A b x₀ m)

/-- Conversely, a Galerkin iterate on `𝒦_m(A, r_0)` is *the* FOM iterate. -/
theorem eq_fomFixed_of_isGalerkinIterate {m : ℕ} {x : 𝔼} (hH : FOMDefined A b x₀ m)
    (hm : m ≤ grade A (v₁ A b x₀)) (hx : Krylov.IsGalerkinIterate (op A) b x₀ m x) :
    x = fomFixed A b x₀ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have hmem := hx.mem
    rw [Krylov.subspace_zero, Submodule.mem_bot, sub_eq_zero] at hmem
    rw [hmem, fomFixed_zero]
  · have hr : b - op A x₀ ≠ 0 := residual_ne_zero_of_lt_grade A b x₀ hm0 hm
    have hgr : m ≤ Krylov.grade (op A) (b - op A x₀) := by rwa [← grade_v₁]
    obtain ⟨z, -, huniq⟩ := (Krylov.existsUnique_isGalerkinIterate_iff_isUnit hgr).2
      (by rw [← H_v₁ A b x₀ hr]; exact hH)
    rw [huniq x hx, huniq _ (fomFixed_isGalerkinIterate A b x₀ hH hm)]

/-- `V_mᴴ r_0 = β e_1` (§6.4.1): the book's `V_mᵀ r_0 = β e_1` for real matrices. -/
theorem conjTranspose_V_mulVec_r₀ (m : ℕ) :
    (V A (v₁ A b x₀) m)ᴴ *ᵥ WithLp.ofLp (r₀ A b x₀) = (β A b x₀ : 𝕜) • e₁ m := by
  funext i
  have hcoord : ((V A (v₁ A b x₀) m)ᴴ *ᵥ WithLp.ofLp (r₀ A b x₀)) i
      = inner 𝕜 (arnoldiCGS A (v₁ A b x₀) (i : ℕ)) (r₀ A b x₀) := by
    simp only [Matrix.mulVec, dotProduct, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Matrix.conjTranspose_apply, V_apply, RCLike.inner_apply, mul_comm]; rfl
  rw [hcoord, Pi.smul_apply, e₁, smul_eq_mul, β_def]
  rcases eq_or_ne (b - op A x₀) 0 with hr | hr
  · rw [show r₀ A b x₀ = 0 from hr, inner_zero_right, hr, norm_zero, RCLike.ofReal_zero,
      zero_mul]
  · have hne : ((‖b - op A x₀‖ : 𝕜)) ≠ 0 := by simpa using norm_ne_zero_iff.2 hr
    rw [arnoldiCGS_v₁ A b x₀ hr, show r₀ A b x₀ = b - op A x₀ from rfl]
    by_cases h0 : (i : ℕ) = 0
    · have hif : (if (i : ℕ) = 0 then (1 : 𝕜) else 0) = 1 := by simp [h0]
      rw [hif, mul_one, h0, Arnoldi.vec_zero _ _ hr, inner_smul_left,
        inner_self_eq_norm_sq_to_K, map_inv₀, RCLike.conj_ofReal, sq, ← mul_assoc,
        inv_mul_cancel₀ hne, one_mul]
    · have hif : (if (i : ℕ) = 0 then (1 : 𝕜) else 0) = 0 := by simp [h0]
      have h1 : inner 𝕜 (Arnoldi.vec (op A) (b - op A x₀) (i : ℕ))
          (Arnoldi.vec (op A) (b - op A x₀) 0) = 0 :=
        Arnoldi.inner_vec_eq_zero (op A) (b - op A x₀) h0
      rw [Arnoldi.vec_zero _ _ hr, inner_smul_right] at h1
      rw [hif, mul_zero, (mul_eq_zero.1 h1).resolve_left (inv_ne_zero hne)]

/-! ### Proposition 6.7 and (6.18) -/

/-- **Proposition 6.7** (field-agnostic form): the FOM residual is
`b - A x_m = -h_{m+1,m} (e_mᵀ y_m) v_{m+1}` (`0`-based indices). -/
theorem residual_fomFixed {m : ℕ} (hH : FOMDefined A b x₀ m) (hm : m ≤ grade A (v₁ A b x₀))
    (hm0 : 0 < m) :
    b - op A (fomFixed A b x₀ m)
      = -(arnoldiCoeff A (v₁ A b x₀) m (m - 1) * fomY A b x₀ m ⟨m - 1, by omega⟩) •
          arnoldiCGS A (v₁ A b x₀) m := by
  have hr : b - op A x₀ ≠ 0 := by
    intro hr
    rw [grade_v₁, hr, Krylov.grade_zero] at hm
    omega
  have hy : Arnoldi.hessenbergSq (op A) (b - op A x₀) m *ᵥ fomY A b x₀ m
      = Krylov.firstVec (‖b - op A x₀‖ : 𝕜) m := by
    rw [← H_v₁ A b x₀ hr]
    exact H_mulVec_fomY A b x₀ hH
  rw [fomFixed_eq_add_sum A b x₀ hr m, Krylov.residual_galerkin_eq hm0 _ hy,
    arnoldiCoeff_v₁ A b x₀ hr, arnoldiCGS_v₁ A b x₀ hr]

/-- **(6.18)** (field-agnostic form): `‖b - A x_m‖₂ = h_{m+1,m} |e_mᵀ y_m|`. Both sides vanish
at `m = μ`, where the Arnoldi process has already stopped. -/
theorem norm_residual_fomFixed {m : ℕ} (hH : FOMDefined A b x₀ m)
    (hm : m ≤ grade A (v₁ A b x₀)) (hm0 : 0 < m) :
    ‖b - op A (fomFixed A b x₀ m)‖
      = ‖arnoldiCoeff A (v₁ A b x₀) m (m - 1)‖ * ‖fomY A b x₀ m ⟨m - 1, by omega⟩‖ := by
  have hr : b - op A x₀ ≠ 0 := by
    intro hr
    rw [grade_v₁, hr, Krylov.grade_zero] at hm
    omega
  have hv : ‖v₁ A b x₀‖ = 1 := norm_v₁ A b x₀ hr
  rw [residual_fomFixed A b x₀ hH hm hm0, norm_smul, norm_neg, norm_mul]
  rcases eq_or_lt_of_le hm with hmg | hmg
  · have hz : arnoldiCoeff A (v₁ A b x₀) m (m - 1) = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      subst hk
      rw [Nat.add_sub_cancel]
      exact (arnoldiCoeff_succ_self_eq_zero_iff A _ hv k).2 (by omega)
    simp [hz]
  · rw [norm_arnoldiCGS A _ hv hmg, mul_one]


/-! ### Algorithm 6.6: the incomplete orthogonalization procedure

Algorithm 6.6 is Algorithm 6.2 with the inner loop restricted to the last `k` vectors,
`i = max{1, j-k+1}, …, j`. Everything below is proved without ever using orthogonality of the
`v_i`, which is exactly the book's reason ("the orthogonality was not used") for (6.6)–(6.7),
Proposition 6.7 and (6.18) surviving the truncation. -/

/-- The inner loop of **Algorithm 6.6**: `w` after the projections on those `v_i` with
`lo ≤ i < N` have been subtracted one at a time. -/
noncomputable def iopW (v : ℕ → 𝔼) (lo : ℕ) (w₀ : 𝔼) : ℕ → 𝔼
  | 0 => w₀
  | i + 1 =>
    let w := iopW v lo w₀ i
    if lo ≤ i then w - inner 𝕜 (v i) w • v i else w

/-- The coefficient `h_ij` produced by the inner loop of Algorithm 6.6 at row `i`; `0` outside
the band. -/
noncomputable def iopCoeffOf (v : ℕ → 𝔼) (lo : ℕ) (w₀ : 𝔼) (i : ℕ) : 𝕜 :=
  if lo ≤ i then inner 𝕜 (v i) (iopW v lo w₀ i) else 0

theorem iopW_succ (v : ℕ → 𝔼) (lo : ℕ) (w₀ : 𝔼) (i : ℕ) :
    iopW v lo w₀ (i + 1) = iopW v lo w₀ i - iopCoeffOf v lo w₀ i • v i := by
  rw [iopW, iopCoeffOf]
  split_ifs with h
  · rfl
  · rw [zero_smul, sub_zero]

/-- The truncated loop subtracts exactly the terms `h_ij v_i`, and nothing else. -/
theorem iopW_eq_sub_sum (v : ℕ → 𝔼) (lo : ℕ) (w₀ : 𝔼) (N : ℕ) :
    iopW v lo w₀ N = w₀ - ∑ i ∈ Finset.range N, iopCoeffOf v lo w₀ i • v i := by
  induction N with
  | zero => simp [iopW]
  | succ N ih => rw [iopW_succ, ih, Finset.sum_range_succ]; abel

private theorem iopW_congr {v v' : ℕ → 𝔼} (lo : ℕ) (w₀ : 𝔼) {N : ℕ} (h : ∀ i < N, v i = v' i) :
    iopW v lo w₀ N = iopW v' lo w₀ N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hN := ih fun i hi => h i (Nat.lt_succ_of_lt hi)
    rw [iopW_succ, iopW_succ, iopCoeffOf, iopCoeffOf, hN, h N N.lt_succ_self]

/-- The truncated loop is orthogonalizing as long as the vectors it sees are orthonormal (or
`0`): this is the only place where the `k`-band bookkeeping of §6.4.2 does any work. -/
private theorem inner_iopW_eq_zero {v : ℕ → 𝔼} {lo : ℕ} (w₀ : 𝔼) :
    ∀ N : ℕ, (∀ a b, lo ≤ a → lo ≤ b → a < N → b < N → a ≠ b → inner 𝕜 (v a) (v b) = 0) →
      (∀ a, lo ≤ a → a < N → inner 𝕜 (v a) (v a) = 1 ∨ v a = 0) →
      ∀ i, lo ≤ i → i < N → inner 𝕜 (v i) (iopW v lo w₀ N) = 0 := by
  intro N
  induction N with
  | zero => intro _ _ i _ hiN; omega
  | succ N ih =>
    intro hortho hnorm i hi hiN
    rw [iopW_succ, inner_sub_right, inner_smul_right]
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hiN) with heq | hlt
    · subst heq
      have hc : iopCoeffOf v lo w₀ i = inner 𝕜 (v i) (iopW v lo w₀ i) := by
        rw [iopCoeffOf, ite_eq_left_of_eq_true _ _ (eq_true hi)]
      rw [hc]
      rcases hnorm i hi i.lt_succ_self with h1 | h1
      · rw [h1, mul_one, sub_self]
      · simp [h1]
    · have ihN := ih (fun a b ha hb haN hbN hab =>
        hortho a b ha hb (Nat.lt_succ_of_lt haN) (Nat.lt_succ_of_lt hbN) hab)
        (fun a ha haN => hnorm a ha (Nat.lt_succ_of_lt haN)) i hi hlt
      rw [ihN, iopCoeffOf]
      split_ifs with hlo
      · rw [hortho i N hi hlo (Nat.lt_succ_of_lt hlt) N.lt_succ_self (Nat.ne_of_lt hlt),
          mul_zero, sub_zero]
      · rw [zero_mul, sub_zero]

variable (v : EuclideanSpace 𝕜 (Fin n)) (k : ℕ)

/-- **Algorithm 6.6** (IOP), `0`-based: Algorithm 6.2 with the inner loop restricted to the
band `i = max{0, j-k+1}, …, j`. The starting vector `v` is the book's `v_1`. -/
noncomputable def iop (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k : ℕ) : ℕ → 𝔼
  | 0 => v
  | j + 1 =>
    let u : ℕ → 𝔼 := fun i => iop A v k (min i j)
    let w := iopW u (j + 1 - k) (op A (u j)) (j + 1)
    ((‖w‖ : 𝕜)⁻¹) • w
  termination_by j => j
  decreasing_by exact Nat.lt_succ_of_le (Nat.min_le_right _ _)

/-- `w_j` of Algorithm 6.6, the vector left by the whole truncated inner loop. -/
noncomputable def iopVecW (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k j : ℕ) : 𝔼 :=
  iopW (iop A v k) (j + 1 - k) (op A (iop A v k j)) (j + 1)

/-- The coefficients `h_ij` of Algorithm 6.6: the band inner products for `i ≤ j`,
`h_{j+1,j} = ‖w_j‖`, and `0` above the subdiagonal. -/
noncomputable def iopCoeff (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k i j : ℕ) : 𝕜 :=
  if i ≤ j then iopCoeffOf (iop A v k) (j + 1 - k) (op A (iop A v k j)) i
  else if i = j + 1 then (‖iopVecW A v k j‖ : 𝕜) else 0

@[simp]
theorem iop_zero : iop A v k 0 = v := by rw [iop]

theorem iopCoeff_of_le {i j : ℕ} (h : i ≤ j) :
    iopCoeff A v k i j = iopCoeffOf (iop A v k) (j + 1 - k) (op A (iop A v k j)) i := by
  rw [iopCoeff, ite_eq_left_of_eq_true _ _ (eq_true h)]

/-- Algorithm 6.6, line 5: `h_{j+1,j} = ‖w_j‖`. -/
theorem iopCoeff_succ_self (j : ℕ) : iopCoeff A v k (j + 1) j = (‖iopVecW A v k j‖ : 𝕜) := by
  rw [iopCoeff]
  split_ifs with h1 h2
  · omega
  · rfl
  · exact absurd rfl h2

/-- The Hessenberg structure: `h_ij = 0` for `i > j + 1`. -/
theorem iopCoeff_eq_zero_of_lt {i j : ℕ} (h : j + 1 < i) : iopCoeff A v k i j = 0 := by
  rw [iopCoeff]
  split_ifs with h1 h2
  · omega
  · omega
  · rfl

/-- The band structure: `h_ij = 0` for `i < j - k + 1`, which is what makes `H_m` banded with
`k` diagonals. -/
theorem iopCoeff_eq_zero_of_add_le {i j : ℕ} (h : i + k ≤ j) : iopCoeff A v k i j = 0 := by
  rw [iopCoeff_of_le A v k (by omega), iopCoeffOf]
  split_ifs with h1
  · omega
  · rfl

/-- Algorithm 6.6, line 7: `v_{j+1} = w_j / h_{j+1,j}`. -/
theorem iop_succ (j : ℕ) :
    iop A v k (j + 1) = ((‖iopVecW A v k j‖ : 𝕜)⁻¹) • iopVecW A v k j := by
  rw [iop, iopVecW]
  simp only [Nat.min_self]
  rw [iopW_congr (v := fun i => iop A v k (min i j)) (v' := iop A v k) (j + 1 - k)
    (op A (iop A v k j)) fun i hi => by rw [Nat.min_eq_left (Nat.lt_succ_iff.1 hi)]]

/-- `w_j = h_{j+1,j} v_{j+1}`. -/
theorem iopVecW_eq_smul (j : ℕ) :
    iopVecW A v k j = iopCoeff A v k (j + 1) j • iop A v k (j + 1) := by
  rw [iopCoeff_succ_self, iop_succ, smul_smul]
  rcases eq_or_ne (iopVecW A v k j) 0 with h | h
  · rw [h, smul_zero]
  · rw [mul_inv_cancel₀ (by simpa using norm_ne_zero_iff.2 h), one_smul]

/-- Breakdown of Algorithm 6.6 at step `j`. -/
theorem iop_succ_eq_zero_iff (j : ℕ) :
    iop A v k (j + 1) = 0 ↔ iopCoeff A v k (j + 1) j = 0 := by
  rw [iopCoeff_succ_self, RCLike.ofReal_eq_zero, norm_eq_zero]
  constructor
  · intro h
    rw [iopVecW_eq_smul, h, smul_zero]
  · intro h
    rw [iop_succ, h, norm_zero, RCLike.ofReal_zero, inv_zero, zero_smul]

/-- Every vector Algorithm 6.6 produces is a unit vector, or `0` after the breakdown. -/
theorem norm_iop (hv : ‖v‖ = 1) (j : ℕ) : ‖iop A v k j‖ = 1 ∨ iop A v k j = 0 := by
  cases j with
  | zero => rw [iop_zero]; exact Or.inl hv
  | succ j =>
    rcases eq_or_ne (iopVecW A v k j) 0 with h | h
    · exact Or.inr (by rw [iop_succ, h, smul_zero])
    · refine Or.inl ?_
      rw [iop_succ, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

/-- **The bridge to the backbone**: the vectors and coefficients of Algorithm 6.6 satisfy the
Hessenberg relation `A v_j = ∑_{i ≤ j+1} h_{ij} v_i`, that is, (6.6)–(6.7) hold verbatim for
incomplete orthogonalization. No orthogonality is used, and none is available. -/
theorem iop_hessenbergRelation :
    Krylov.HessenbergRelation (op A) (iop A v k) (iopCoeff A v k) := by
  refine ⟨fun j => ?_, fun i j hij => iopCoeff_eq_zero_of_lt A v k hij⟩
  have hw : iopVecW A v k j
      = op A (iop A v k j) - ∑ i ∈ Finset.range (j + 1), iopCoeff A v k i j • iop A v k i := by
    rw [iopVecW, iopW_eq_sub_sum]
    refine congrArg _ (Finset.sum_congr rfl fun i hi => ?_)
    rw [iopCoeff_of_le A v k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
  rw [Finset.sum_range_succ, ← iopVecW_eq_smul, hw]
  abel

/-- §6.4.2: the local orthogonality of the incomplete orthogonalization process — each vector
is orthogonal to the `k` vectors preceding it, and to no others. -/
theorem inner_iop_eq_zero (hv : ‖v‖ = 1) :
    ∀ j i : ℕ, i < j → j ≤ i + k → inner 𝕜 (iop A v k i) (iop A v k j) = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i hij hk
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [iop_succ, inner_smul_right]
    have hkey : inner 𝕜 (iop A v k i) (iopVecW A v k j') = 0 := by
      rw [iopVecW]
      refine inner_iopW_eq_zero _ (j' + 1) (fun a b ha hb haN hbN hab => ?_)
        (fun a _ _ => ?_) i (by omega) (by omega)
      · rcases lt_or_gt_of_ne hab with h | h
        · exact ih b (by omega) a h (by omega)
        · rw [← inner_conj_symm, ih a (by omega) b h (by omega), map_zero]
      · rcases norm_iop A v k hv a with h | h
        · exact Or.inl (by rw [inner_self_eq_norm_sq_to_K, h]; norm_num)
        · exact Or.inr h
    rw [hkey, mul_zero]

/-! ### The matrices of the incomplete process, and Algorithm 6.7 (IOM) -/

/-- `V_m` for Algorithm 6.6. -/
noncomputable def VI (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k m : ℕ) :
    Matrix (Fin n) (Fin m) 𝕜 :=
  colMatrix (iop A v k) m

/-- `H̄_m` for Algorithm 6.6. -/
noncomputable def HbarI (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k m : ℕ) :
    Matrix (Fin (m + 1)) (Fin m) 𝕜 :=
  Krylov.hessenbergOf (iopCoeff A v k) m

/-- `H_m` for Algorithm 6.6. -/
noncomputable def HI (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k m : ℕ) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  Krylov.hessenbergSqOf (iopCoeff A v k) m

@[simp]
theorem HI_apply {m : ℕ} (i j : Fin m) : HI A v k m i j = iopCoeff A v k i j := rfl

/-- **(6.7) for incomplete orthogonalization**: `A V_m = V_{m+1} H̄_m` still holds. -/
theorem mul_VI_eq (m : ℕ) : A * VI A v k m = VI A v k (m + 1) * HbarI A v k m :=
  mul_colMatrix_eq A (iop_hessenbergRelation A v k) m

private theorem toEuclideanLin_colMatrix_apply (u : ℕ → 𝔼) {m : ℕ} (y : Fin m → 𝕜) :
    Matrix.toEuclideanLin (colMatrix u m) (WithLp.toLp 2 y) = ∑ j, y j • u (j : ℕ) := by
  rw [Matrix.toEuclideanLin_apply_eq_sum]
  exact Finset.sum_congr rfl fun j _ => rfl

/-- The number of steps Algorithm 6.7 actually performs: the book's "if `h_{j+1,j} = 0` then
set `m := j`" stops at the first breakdown of Algorithm 6.6. -/
noncomputable def iomSteps (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k m : ℕ) : ℕ :=
  sInf ({j | iopCoeff A v k (j + 1) j = 0} ∪ {m})

theorem iomSteps_le (m : ℕ) : iomSteps A v k m ≤ m :=
  Nat.sInf_le (Set.mem_union_right _ rfl)

/-- Without a breakdown Algorithm 6.7 performs the full `m` steps. -/
theorem iomSteps_eq {m : ℕ} (hnb : ∀ j < m, iopCoeff A v k (j + 1) j ≠ 0) :
    iomSteps A v k m = m := by
  refine le_antisymm (iomSteps_le A v k m) (le_csInf ⟨m, Set.mem_union_right _ rfl⟩ ?_)
  rintro c (hc | hc)
  · by_contra h
    exact hnb c (by omega) hc
  · exact le_of_eq (Set.mem_singleton_iff.1 hc).symm

/-- `y_m = H_m^{-1}(β e_1)` for the incomplete process. -/
noncomputable def iomY (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (k m : ℕ) : Fin m → 𝕜 :=
  (HI A (v₁ A b x₀) k m)⁻¹ *ᵥ ((β A b x₀ : 𝕜) • e₁ m)

/-- Algorithm 6.7 with exactly `m` steps of Algorithm 6.6: `x_m = x_0 + V_m y_m`. -/
noncomputable def iomFixed (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (k m : ℕ) : 𝔼 :=
  x₀ + Matrix.toEuclideanLin (VI A (v₁ A b x₀) k m) (WithLp.toLp 2 (iomY A b x₀ k m))

/-- **Algorithm 6.7** (IOM): Algorithm 6.4 with Algorithm 6.6 in place of the Arnoldi step. -/
noncomputable def iom (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (k m : ℕ) : 𝔼 :=
  iomFixed A b x₀ k (iomSteps A (v₁ A b x₀) k m)

theorem iom_eq_iomFixed {m : ℕ} (hnb : ∀ j < m, iopCoeff A (v₁ A b x₀) k (j + 1) j ≠ 0) :
    iom A b x₀ k m = iomFixed A b x₀ k m := by
  rw [iom, iomSteps_eq A (v₁ A b x₀) k hnb]

theorem iomFixed_eq_add_sum (m : ℕ) :
    iomFixed A b x₀ k m = x₀ + ∑ j, iomY A b x₀ k m j • iop A (v₁ A b x₀) k (j : ℕ) := by
  rw [iomFixed, VI, toEuclideanLin_colMatrix_apply]

/-- `β v_1 = r_0` also when `x_0` already solves the system, where both sides vanish. -/
theorem smul_iop_zero : (β A b x₀ : 𝕜) • iop A (v₁ A b x₀) k 0 = b - op A x₀ := by
  rw [iop_zero, v₁_def, smul_smul, β_def]
  rcases eq_or_ne (b - op A x₀) 0 with h | h
  · rw [h, smul_zero]
  · rw [mul_inv_cancel₀ (by simpa using norm_ne_zero_iff.2 h), one_smul]

theorem HI_mulVec_iomY {m : ℕ} (hH : IsUnit (HI A (v₁ A b x₀) k m)) :
    HI A (v₁ A b x₀) k m *ᵥ iomY A b x₀ k m = Krylov.firstVec (β A b x₀ : 𝕜) m := by
  rw [iomY, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hH), Matrix.one_mulVec,
    smul_e₁_eq_firstVec]

/-- **Proposition 6.7 for IOM** (§6.4.2, "the result of Proposition 6.7 is still valid"):
`b - A x_m = -h_{m+1,m} (e_mᵀ y_m) v_{m+1}`. -/
theorem residual_iomFixed {m : ℕ} (hH : IsUnit (HI A (v₁ A b x₀) k m)) (hm0 : 0 < m) :
    b - op A (iomFixed A b x₀ k m)
      = -(iopCoeff A (v₁ A b x₀) k m (m - 1) * iomY A b x₀ k m ⟨m - 1, by omega⟩) •
          iop A (v₁ A b x₀) k m := by
  rw [iomFixed_eq_add_sum]
  exact (iop_hessenbergRelation A (v₁ A b x₀) k).residual_eq_of_mulVec_eq
    (smul_iop_zero A b x₀ k).symm hm0 _ (HI_mulVec_iomY A b x₀ k hH)

/-- **(6.18) for IOM**: `‖b - A x_m‖₂ = h_{m+1,m} |e_mᵀ y_m|`. Both sides vanish at a
breakdown. -/
theorem norm_residual_iomFixed {m : ℕ} (hH : IsUnit (HI A (v₁ A b x₀) k m)) (hm0 : 0 < m)
    (hv : ‖v₁ A b x₀‖ = 1) :
    ‖b - op A (iomFixed A b x₀ k m)‖
      = ‖iopCoeff A (v₁ A b x₀) k m (m - 1)‖ * ‖iomY A b x₀ k m ⟨m - 1, by omega⟩‖ := by
  rw [residual_iomFixed A b x₀ k hH hm0, norm_smul, norm_neg, norm_mul]
  rcases norm_iop A (v₁ A b x₀) k hv m with h | h
  · rw [h, mul_one]
  · have hz : iopCoeff A (v₁ A b x₀) k m (m - 1) = 0 := by
      obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      subst hj
      rw [Nat.add_sub_cancel]
      exact (iop_succ_eq_zero_iff A (v₁ A b x₀) k j).1 h
    simp [hz]

/-- **Proposition 6.8**: IOM is a projection process onto `𝒦_m` orthogonally to
`L_m = span {z_1, …, z_m}` with `z_i = v_i - (v_i, v_{m+1}) v_{m+1}`. -/
theorem iomFixed_isPetrovGalerkin {m : ℕ} (hH : IsUnit (HI A (v₁ A b x₀) k m)) (hm0 : 0 < m)
    (hnorm : ‖iop A (v₁ A b x₀) k m‖ = 1)
    (hspan : Submodule.span 𝕜 (Set.range fun i : Fin m => iop A (v₁ A b x₀) k (i : ℕ))
      = krylov A (r₀ A b x₀) m) :
    IsPetrovGalerkin (op A) b x₀ (krylov A (r₀ A b x₀) m)
      (Submodule.span 𝕜 (Set.range fun i : Fin m =>
        iop A (v₁ A b x₀) k (i : ℕ)
          - inner 𝕜 (iop A (v₁ A b x₀) k m) (iop A (v₁ A b x₀) k (i : ℕ))
              • iop A (v₁ A b x₀) k m))
      (iomFixed A b x₀ k m) := by
  refine ⟨?_, ?_⟩
  · rw [iomFixed_eq_add_sum, add_sub_cancel_left, ← hspan]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.mem_orthogonal_span, residual_iomFixed A b x₀ k hH hm0]
    rintro _ ⟨i, rfl⟩
    have hself : inner 𝕜 (iop A (v₁ A b x₀) k m) (iop A (v₁ A b x₀) k m) = (1 : 𝕜) := by
      rw [inner_self_eq_norm_sq_to_K, hnorm]
      norm_num
    rw [inner_smul_right, inner_sub_left, inner_smul_left, hself, mul_one, inner_conj_symm,
      sub_self, mul_zero]


/-! ### The Hessenberg LU factorization of §6.4.2

`H_m = L_m U_m` computed without pivoting: `L_m` is unit lower bidiagonal and `U_m` is upper
triangular, banded with `k` diagonals when `H_m` is. -/

/-- The upper factor of the LU factorization of a Hessenberg coefficient function:
`u_{0j} = h_{0j}` and `u_{i+1,j} = h_{i+1,j} - l_i u_{ij}`. -/
noncomputable def dioU (h : ℕ → ℕ → 𝕜) : ℕ → ℕ → 𝕜
  | 0, j => h 0 j
  | i + 1, j => h (i + 1) j - h (i + 1) i / dioU h i i * dioU h i j

/-- The subdiagonal of the unit lower bidiagonal factor: `l_{i+1,i} = h_{i+1,i}/u_ii`. -/
noncomputable def dioL (h : ℕ → ℕ → 𝕜) (i : ℕ) : 𝕜 := h (i + 1) i / dioU h i i

theorem dioU_succ (h : ℕ → ℕ → 𝕜) (i j : ℕ) :
    dioU h (i + 1) j = h (i + 1) j - dioL h i * dioU h i j := rfl

/-- `U_m` inherits the bandwidth of `H_m`. -/
theorem dioU_eq_zero_of_add_le {h : ℕ → ℕ → 𝕜} {k : ℕ}
    (hband : ∀ a c, a + k ≤ c → h a c = 0) :
    ∀ i j : ℕ, i + k ≤ j → dioU h i j = 0 := by
  intro i
  induction i with
  | zero => intro j hj; exact hband 0 j hj
  | succ i ih => intro j hj; rw [dioU_succ, ih j (by omega), hband (i + 1) j hj, mul_zero, sub_zero]

/-- `U_m` is upper triangular as soon as the pivot on its diagonal does not vanish. -/
theorem dioU_eq_zero_of_lt {h : ℕ → ℕ → 𝕜} (hh : ∀ a c, c + 1 < a → h a c = 0) {j : ℕ}
    (hpiv : dioU h j j ≠ 0) : ∀ i, j < i → dioU h i j = 0 := by
  intro i
  induction i with
  | zero => intro hj; omega
  | succ i ih =>
    intro hji
    rw [dioU_succ]
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hji) with heq | hlt
    · subst heq
      rw [dioL, div_mul_cancel₀ _ hpiv, sub_self]
    · rw [ih hlt, mul_zero, sub_zero, hh (i + 1) j (by omega)]

/-- The unit lower bidiagonal factor `L_m`. -/
noncomputable def hessL (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 1 else if (i : ℕ) = (j : ℕ) + 1 then dioL h j
    else 0

/-- The banded upper triangular factor `U_m`. -/
noncomputable def hessU (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => if (i : ℕ) ≤ (j : ℕ) then dioU h i j else 0

/-- The Doolittle LU factorization of a Hessenberg matrix without pivoting (§6.4.2). -/
noncomputable def hessLU (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    Matrix (Fin m) (Fin m) 𝕜 × Matrix (Fin m) (Fin m) 𝕜 :=
  (hessL h m, hessU h m)

theorem hessL_apply (h : ℕ → ℕ → 𝕜) {m : ℕ} (i j : Fin m) :
    hessL h m i j =
      if (i : ℕ) = (j : ℕ) then 1 else if (i : ℕ) = (j : ℕ) + 1 then dioL h j else 0 := rfl

theorem hessU_apply (h : ℕ → ℕ → 𝕜) {m : ℕ} (i j : Fin m) :
    hessU h m i j = if (i : ℕ) ≤ (j : ℕ) then dioU h i j else 0 := rfl

theorem hessL_self (h : ℕ → ℕ → 𝕜) {m : ℕ} (i : Fin m) : hessL h m i i = 1 := by
  rw [hessL_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)]

theorem hessL_eq_zero (h : ℕ → ℕ → 𝕜) {m : ℕ} {i j : Fin m} (h1 : (i : ℕ) ≠ (j : ℕ))
    (h2 : (i : ℕ) ≠ (j : ℕ) + 1) : hessL h m i j = 0 := by
  rw [hessL_apply, ite_eq_right_of_eq_false _ _ (eq_false h1),
    ite_eq_right_of_eq_false _ _ (eq_false h2)]

theorem hessL_sub (h : ℕ → ℕ → 𝕜) {m : ℕ} {i j : Fin m} (hij : (i : ℕ) = (j : ℕ) + 1) :
    hessL h m i j = dioL h j := by
  rw [hessL_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega : (i : ℕ) ≠ (j : ℕ))),
    ite_eq_left_of_eq_true _ _ (eq_true hij)]

theorem hessU_of_le (h : ℕ → ℕ → 𝕜) {m : ℕ} {i j : Fin m} (hij : (i : ℕ) ≤ (j : ℕ)) :
    hessU h m i j = dioU h i j := by
  rw [hessU_apply, ite_eq_left_of_eq_true _ _ (eq_true hij)]

theorem hessU_eq_zero (h : ℕ → ℕ → 𝕜) {m : ℕ} {i j : Fin m} (hij : (j : ℕ) < (i : ℕ)) :
    hessU h m i j = 0 := by
  rw [hessU_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- `U_m` is banded with `k` diagonals when `H_m` is. -/
theorem hessU_eq_zero_of_add_le {h : ℕ → ℕ → 𝕜} {k : ℕ}
    (hband : ∀ a c, a + k ≤ c → h a c = 0) {m : ℕ} {i j : Fin m} (hij : (i : ℕ) + k ≤ (j : ℕ)) :
    hessU h m i j = 0 := by
  rw [hessU_of_le h (by omega), dioU_eq_zero_of_add_le hband (i : ℕ) (j : ℕ) hij]

private theorem sum_eq_pair {m : ℕ} (f : Fin m → 𝕜) (a c : Fin m) (hac : a ≠ c)
    (h0 : ∀ x : Fin m, x ≠ a → x ≠ c → f x = 0) : ∑ x, f x = f a + f c := by
  rw [← Finset.sum_subset (Finset.subset_univ ({a, c} : Finset (Fin m))), Finset.sum_pair hac]
  intro x _ hx
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  exact h0 x hx.1 hx.2

/-- **The LU factorization of §6.4.2**: `H_m = L_m U_m` with `L_m` unit lower bidiagonal and
`U_m` upper triangular, as long as no pivot vanishes. -/
theorem hessL_mul_hessU (h : ℕ → ℕ → 𝕜) (hh : ∀ a c, c + 1 < a → h a c = 0) {m : ℕ}
    (hpiv : ∀ l, l < m → dioU h l l ≠ 0) :
    hessL h m * hessU h m = Krylov.hessenbergSqOf h m := by
  ext i j
  rw [Matrix.mul_apply]
  change _ = h (i : ℕ) (j : ℕ)
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hi0
  · rw [Finset.sum_eq_single i (fun x _ hx => ?_) (fun hc => absurd (Finset.mem_univ i) hc)]
    · rw [hessL_self, one_mul, hessU_of_le h (by omega), hi0]
      rfl
    · rw [hessL_eq_zero h (fun hc => hx (Fin.ext hc.symm)) (by omega), zero_mul]
  · obtain ⟨i', hi'⟩ : ∃ i', (i : ℕ) = i' + 1 := ⟨(i : ℕ) - 1, by omega⟩
    have hi'm : i' < m := by have := i.isLt; omega
    have hne : (⟨i', hi'm⟩ : Fin m) ≠ i := fun hc => by
      have : i' = (i : ℕ) := congrArg Fin.val hc
      omega
    rw [sum_eq_pair _ (⟨i', hi'm⟩ : Fin m) i hne (fun x hxa hxc => ?_)]
    · rw [hessL_sub h (by simpa using hi'), hessL_self, one_mul]
      rcases lt_trichotomy (j : ℕ) i' with hj | hj | hj
      · rw [hessU_eq_zero h (by simpa using hj), hessU_eq_zero h (by omega), mul_zero, add_zero,
          hh (i : ℕ) (j : ℕ) (by omega)]
      · rw [hessU_of_le h (by simp [hj]), hessU_eq_zero h (by omega), add_zero, hj, dioL,
          div_mul_cancel₀ _ (hpiv i' hi'm), hi']
      · rw [hessU_of_le h (by simpa using le_of_lt hj), hessU_of_le h (by omega), hi',
          dioU_succ]
        ring
    · rw [hessL_eq_zero h (fun hc => hxc (Fin.ext hc.symm))
        (fun hc => hxa (Fin.ext (by simp only []; omega))), zero_mul]

theorem hessL_isLowerTriangular (h : ℕ → ℕ → 𝕜) (m : ℕ) : (hessL h m).IsLowerTriangular := by
  intro i j hij
  have hlt : i < j := hij
  rw [Fin.lt_def] at hlt
  exact hessL_eq_zero h (by omega) (by omega)

theorem hessU_isUpperTriangular (h : ℕ → ℕ → 𝕜) (m : ℕ) : (hessU h m).IsUpperTriangular := by
  intro i j hij
  have hlt : j < i := hij
  rw [Fin.lt_def] at hlt
  exact hessU_eq_zero h hlt

theorem det_hessL (h : ℕ → ℕ → 𝕜) (m : ℕ) : (hessL h m).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (hessL_isLowerTriangular h m)]
  simp [hessL_self]

theorem det_hessU (h : ℕ → ℕ → 𝕜) (m : ℕ) : (hessU h m).det = ∏ i : Fin m, dioU h i i := by
  rw [Matrix.det_of_isUpperTriangular (hessU_isUpperTriangular h m)]
  exact Finset.prod_congr rfl fun i _ => hessU_of_le h le_rfl

theorem isUnit_hessU (h : ℕ → ℕ → 𝕜) {m : ℕ} (hpiv : ∀ l, l < m → dioU h l l ≠ 0) :
    IsUnit (hessU h m) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_hessU]
  exact Finset.prod_ne_zero_iff.2 fun i _ => hpiv i i.isLt

/-- The `H_m` of an incomplete orthogonalization is nonsingular as soon as no pivot vanishes. -/
theorem isUnit_hessenbergSqOf (h : ℕ → ℕ → 𝕜) (hh : ∀ a c, c + 1 < a → h a c = 0) {m : ℕ}
    (hpiv : ∀ l, l < m → dioU h l l ≠ 0) : IsUnit (Krylov.hessenbergSqOf h m) := by
  rw [← hessL_mul_hessU h hh hpiv]
  refine IsUnit.mul ?_ (isUnit_hessU h hpiv)
  rw [Matrix.isUnit_iff_isUnit_det, det_hessL]
  exact isUnit_one

/-! ### Algorithm 6.8: DIOM -/

/-- `ζ_1 = β`, `ζ_{m} = -l_{m,m-1} ζ_{m-1}` (Algorithm 6.8, line 3). -/
noncomputable def diomZeta (h : ℕ → ℕ → 𝕜) (c : 𝕜) : ℕ → 𝕜
  | 0 => c
  | j + 1 => -dioL h j * diomZeta h c j

theorem diomZeta_succ (h : ℕ → ℕ → 𝕜) (c : 𝕜) (j : ℕ) :
    diomZeta h c (j + 1) = -dioL h j * diomZeta h c j := rfl

theorem diomZeta_ne_zero {h : ℕ → ℕ → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    ∀ j : ℕ, (∀ i, i < j → dioL h i ≠ 0) → diomZeta h c j ≠ 0 := by
  intro j
  induction j with
  | zero => intro _; exact hc
  | succ j ih =>
    intro hl
    rw [diomZeta_succ]
    exact mul_ne_zero (neg_ne_zero.2 (hl j j.lt_succ_self))
      (ih fun i hi => hl i (Nat.lt_succ_of_lt hi))

/-- `L_m z_m = β e_1`: the vector `z_m` of §6.4.2 is `(ζ_1, …, ζ_m)`. -/
theorem hessL_mulVec_diomZeta (h : ℕ → ℕ → 𝕜) (c : 𝕜) (m : ℕ) :
    hessL h m *ᵥ (fun j : Fin m => diomZeta h c (j : ℕ)) = Krylov.firstVec c m := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Krylov.firstVec]
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hi0
  · rw [Finset.sum_eq_single i (fun x _ hx => ?_) (fun hc => absurd (Finset.mem_univ i) hc)]
    · rw [hessL_self, one_mul, ite_eq_left_of_eq_true _ _ (eq_true hi0), hi0]
      rfl
    · rw [hessL_eq_zero h (fun hc => hx (Fin.ext hc.symm)) (by omega), zero_mul]
  · obtain ⟨i', hi'⟩ : ∃ i', (i : ℕ) = i' + 1 := ⟨(i : ℕ) - 1, by omega⟩
    have hi'm : i' < m := by have := i.isLt; omega
    have hne : (⟨i', hi'm⟩ : Fin m) ≠ i := fun hc => by
      have : i' = (i : ℕ) := congrArg Fin.val hc
      omega
    rw [sum_eq_pair _ (⟨i', hi'm⟩ : Fin m) i hne (fun x hxa hxc => ?_),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega : ¬ (i : ℕ) = 0))]
    · rw [hessL_sub h (by simpa using hi'), hessL_self, one_mul, hi', diomZeta_succ]
      ring
    · rw [hessL_eq_zero h (fun hc => hxc (Fin.ext hc.symm))
        (fun hc => hxa (Fin.ext (by simp only []; omega))), zero_mul]

/-- `p_m = u_mm^{-1}(v_m - ∑_{i=m-k+1}^{m-1} u_{im} p_i)` (Algorithm 6.8, line 4). -/
noncomputable def diomP (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k : ℕ) : ℕ → 𝔼
  | j =>
    (dioU (iopCoeff A v k) j j)⁻¹ •
      (iop A v k j - ∑ i : Fin j, if j + 1 - k ≤ (i : ℕ) then
        dioU (iopCoeff A v k) (i : ℕ) j • diomP A v k (i : ℕ) else 0)
  termination_by j => j
  decreasing_by exact i.isLt

theorem diomP_eq (j : ℕ) :
    diomP A v k j = (dioU (iopCoeff A v k) j j)⁻¹ •
      (iop A v k j - ∑ i ∈ Finset.Ico (j + 1 - k) j,
        dioU (iopCoeff A v k) i j • diomP A v k i) := by
  have hsum : (∑ i : Fin j, if j + 1 - k ≤ (i : ℕ) then
        dioU (iopCoeff A v k) (i : ℕ) j • diomP A v k (i : ℕ) else 0)
      = ∑ i ∈ Finset.Ico (j + 1 - k) j, dioU (iopCoeff A v k) i j • diomP A v k i := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if j + 1 - k ≤ i then
      dioU (iopCoeff A v k) i j • diomP A v k i else 0) j, ← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [diomP, hsum]

/-- `P_m U_m = V_m` columnwise: this is Algorithm 6.8, line 4, read backwards, and it is what
makes `P_m = V_m U_m^{-1}` of (6.20). -/
theorem sum_hessU_smul_diomP {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A v k) l l ≠ 0) (j : Fin m) :
    ∑ i : Fin m, hessU (iopCoeff A v k) m i j • diomP A v k (i : ℕ) = iop A v k (j : ℕ) := by
  have hband : ∀ a : ℕ, a + k ≤ (j : ℕ) → dioU (iopCoeff A v k) a (j : ℕ) = 0 := fun a ha =>
    dioU_eq_zero_of_add_le (fun _ _ hac => iopCoeff_eq_zero_of_add_le A v k hac) a (j : ℕ) ha
  have h1 : ∑ i : Fin m, hessU (iopCoeff A v k) m i j • diomP A v k (i : ℕ)
      = ∑ a ∈ Finset.range m,
        (if a ≤ (j : ℕ) then dioU (iopCoeff A v k) a (j : ℕ) else 0) • diomP A v k a := by
    rw [← Fin.sum_univ_eq_sum_range (fun a : ℕ =>
      (if a ≤ (j : ℕ) then dioU (iopCoeff A v k) a (j : ℕ) else 0) • diomP A v k a) m]
    exact Finset.sum_congr rfl fun i _ => by rw [hessU_apply]
  have hsub : Finset.range ((j : ℕ) + 1) ⊆ Finset.range m := fun x hx =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) j.isLt)
  have h2a : ∑ a ∈ Finset.range ((j : ℕ) + 1),
        (if a ≤ (j : ℕ) then dioU (iopCoeff A v k) a (j : ℕ) else 0) • diomP A v k a
      = ∑ a ∈ Finset.range m,
        (if a ≤ (j : ℕ) then dioU (iopCoeff A v k) a (j : ℕ) else 0) • diomP A v k a := by
    refine Finset.sum_subset hsub fun x _ hx => ?_
    rw [Finset.mem_range] at hx
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega : ¬ x ≤ (j : ℕ))), zero_smul]
  have h2b : ∑ a ∈ Finset.range ((j : ℕ) + 1),
        (if a ≤ (j : ℕ) then dioU (iopCoeff A v k) a (j : ℕ) else 0) • diomP A v k a
      = ∑ a ∈ Finset.range ((j : ℕ) + 1),
        dioU (iopCoeff A v k) a (j : ℕ) • diomP A v k a :=
    Finset.sum_congr rfl fun x hx => by
      rw [ite_eq_left_of_eq_true _ _ (eq_true (Nat.lt_succ_iff.1 (Finset.mem_range.1 hx)))]
  have h3 : ∑ a ∈ Finset.range (j : ℕ), dioU (iopCoeff A v k) a (j : ℕ) • diomP A v k a
      = ∑ a ∈ Finset.Ico ((j : ℕ) + 1 - k) (j : ℕ),
        dioU (iopCoeff A v k) a (j : ℕ) • diomP A v k a := by
    rw [Finset.range_eq_Ico]
    refine (Finset.sum_subset (Finset.Ico_subset_Ico_left (Nat.zero_le _)) fun x hx hx' => ?_).symm
    have hx1 : x < (j : ℕ) := (Finset.mem_Ico.1 hx).2
    have hx2 : ¬ ((j : ℕ) + 1 - k ≤ x ∧ x < (j : ℕ)) := fun hc => hx' (Finset.mem_Ico.2 hc)
    rw [hband x (by omega), zero_smul]
  have h4 : dioU (iopCoeff A v k) (j : ℕ) (j : ℕ) • diomP A v k (j : ℕ)
      = iop A v k (j : ℕ) - ∑ a ∈ Finset.Ico ((j : ℕ) + 1 - k) (j : ℕ),
        dioU (iopCoeff A v k) a (j : ℕ) • diomP A v k a := by
    rw [diomP_eq A v k (j : ℕ), smul_smul, mul_inv_cancel₀ (hpiv (j : ℕ) j.isLt), one_smul]
  rw [h1, ← h2a, h2b, Finset.sum_range_succ, h3, h4]
  abel

/-- Every `p_i` lies in the span of the first `i + 1` vectors of Algorithm 6.6, since `U_m` is
upper triangular. -/
theorem diomP_mem_span (i : ℕ) :
    diomP A v k i ∈ Submodule.span 𝕜 (iop A v k '' Set.Iio (i + 1)) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [diomP_eq]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.subset_span ⟨i, by simp, rfl⟩) (Submodule.sum_mem _ fun l hl => ?_))
    rw [Finset.mem_Ico] at hl
    exact Submodule.smul_mem _ _
      (Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega))) (ih l hl.2))

private theorem inner_diomP_iop_eq_zero {i j : ℕ}
    (h : ∀ l, l < i + 1 → inner 𝕜 (iop A v k l) (iop A v k j) = 0) :
    inner 𝕜 (diomP A v k i) (iop A v k j) = 0 := by
  have hmem : iop A v k j ∈ (Submodule.span 𝕜 (iop A v k '' Set.Iio (i + 1)))ᗮ := by
    rw [Submodule.mem_orthogonal_span]
    rintro _ ⟨l, hl, rfl⟩
    exact h l hl
  exact (Submodule.mem_orthogonal _ _).1 hmem _ (diomP_mem_span A v k i)

/-- **Algorithm 6.8** (DIOM): `x_m = x_{m-1} + ζ_m p_m` (6.21). -/
noncomputable def diom (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (k : ℕ) : ℕ → 𝔼
  | 0 => x₀
  | m + 1 => diom A b x₀ k m
      + diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) m • diomP A (v₁ A b x₀) k m

theorem diom_succ (m : ℕ) :
    diom A b x₀ k (m + 1) = diom A b x₀ k m
      + diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) m • diomP A (v₁ A b x₀) k m := rfl

theorem diom_eq_add_sum (m : ℕ) :
    diom A b x₀ k m = x₀ + ∑ j ∈ Finset.range m,
      diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) j • diomP A (v₁ A b x₀) k j := by
  induction m with
  | zero => simp [diom]
  | succ m ih => rw [diom_succ, ih, Finset.sum_range_succ, add_assoc]

/-- `y_m = U_m^{-1} z_m` — not computed by Algorithm 6.8, but the vector through which the
book's derivation of (6.20) passes. -/
noncomputable def diomY (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (k m : ℕ) : Fin m → 𝕜 :=
  (hessU (iopCoeff A (v₁ A b x₀) k) m)⁻¹ *ᵥ
    fun j : Fin m => diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) (j : ℕ)

theorem hessU_mulVec_diomY {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    hessU (iopCoeff A (v₁ A b x₀) k) m *ᵥ diomY A b x₀ k m
      = fun j : Fin m => diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) (j : ℕ) := by
  rw [diomY, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_hessU _ hpiv)), Matrix.one_mulVec]

theorem isUnit_HI_of_pivots {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A v k) l l ≠ 0) : IsUnit (HI A v k m) :=
  isUnit_hessenbergSqOf _ (fun _ _ hac => iopCoeff_eq_zero_of_lt A v k hac) hpiv

theorem HI_mulVec_diomY {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    HI A (v₁ A b x₀) k m *ᵥ diomY A b x₀ k m = Krylov.firstVec (β A b x₀ : 𝕜) m := by
  rw [HI, ← hessL_mul_hessU _ (fun _ _ hac => iopCoeff_eq_zero_of_lt A (v₁ A b x₀) k hac) hpiv,
    ← Matrix.mulVec_mulVec, hessU_mulVec_diomY A b x₀ k hpiv, hessL_mulVec_diomZeta]

theorem diomY_eq_iomY {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    diomY A b x₀ k m = iomY A b x₀ k m := by
  rw [iomY, smul_e₁_eq_firstVec, ← HI_mulVec_diomY A b x₀ k hpiv, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1
      (isUnit_HI_of_pivots A (v₁ A b x₀) k hpiv)), Matrix.one_mulVec]

/-- **(6.20)–(6.21)**: Algorithm 6.8 computes the IOM iterates — `x_m = x_0 + P_m z_m` is
`x_0 + V_m y_m`. -/
theorem diom_eq_iomFixed {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    diom A b x₀ k m = iomFixed A b x₀ k m := by
  rw [diom_eq_add_sum, iomFixed_eq_add_sum, ← diomY_eq_iomY A b x₀ k hpiv,
    ← Fin.sum_univ_eq_sum_range (fun j => diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) j •
      diomP A (v₁ A b x₀) k j) m]
  refine congrArg (x₀ + ·) ?_
  symm
  calc ∑ j : Fin m, diomY A b x₀ k m j • iop A (v₁ A b x₀) k (j : ℕ)
      = ∑ j : Fin m, ∑ i : Fin m,
          (diomY A b x₀ k m j * hessU (iopCoeff A (v₁ A b x₀) k) m i j) •
            diomP A (v₁ A b x₀) k (i : ℕ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← sum_hessU_smul_diomP A (v₁ A b x₀) k hpiv j, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
    _ = ∑ i : Fin m, (∑ j : Fin m,
          hessU (iopCoeff A (v₁ A b x₀) k) m i j * diomY A b x₀ k m j) •
            diomP A (v₁ A b x₀) k (i : ℕ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
    _ = ∑ i : Fin m, diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) (i : ℕ) •
          diomP A (v₁ A b x₀) k (i : ℕ) :=
        Finset.sum_congr rfl fun i _ =>
          congrArg (· • diomP A (v₁ A b x₀) k (i : ℕ))
            (congrFun (hessU_mulVec_diomY A b x₀ k hpiv) i)

/-- The last component of `y_m` is `ζ_m/u_mm`, by back substitution in `U_m y_m = z_m`. -/
theorem diomY_last {m : ℕ} (hm0 : 0 < m)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    diomY A b x₀ k m ⟨m - 1, by omega⟩
      = diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) (m - 1)
        / dioU (iopCoeff A (v₁ A b x₀) k) (m - 1) (m - 1) := by
  have hlast := congrFun (hessU_mulVec_diomY A b x₀ k hpiv) (⟨m - 1, by omega⟩ : Fin m)
  rw [Matrix.mulVec, dotProduct,
    Finset.sum_eq_single (⟨m - 1, by omega⟩ : Fin m) (fun x _ hx => ?_)
      (fun hc => absurd (Finset.mem_univ _) hc),
    hessU_of_le _ le_rfl] at hlast
  · exact (eq_div_iff (hpiv (m - 1) (by omega))).2 (by rw [mul_comm]; exact hlast)
  · rw [hessU_eq_zero _ (show (x : ℕ) < m - 1 by
      have := x.isLt
      have : (x : ℕ) ≠ m - 1 := fun hc => hx (Fin.ext hc)
      omega), zero_mul]

/-- **§6.4.2**: the DIOM residual norm is `h_{m+1,m} |ζ_m/u_mm|`. -/
theorem norm_residual_diom {m : ℕ} (hm0 : 0 < m) (hv : ‖v₁ A b x₀‖ = 1)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    ‖b - op A (diom A b x₀ k m)‖
      = ‖iopCoeff A (v₁ A b x₀) k m (m - 1)‖ *
        ‖diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) (m - 1)
          / dioU (iopCoeff A (v₁ A b x₀) k) (m - 1) (m - 1)‖ := by
  rw [diom_eq_iomFixed A b x₀ k hpiv,
    norm_residual_iomFixed A b x₀ k (isUnit_HI_of_pivots A (v₁ A b x₀) k hpiv) hm0 hv,
    ← diomY_eq_iomY A b x₀ k hpiv, diomY_last A b x₀ k hm0 hpiv]

/-! ### (6.22)–(6.24) (P-6.22) -/

/-- Every DIOM residual is a multiple of the next incomplete orthogonalization vector. -/
theorem residual_diom_eq_smul {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    ∃ c : 𝕜, b - op A (diom A b x₀ k m) = c • iop A (v₁ A b x₀) k m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exact ⟨(β A b x₀ : 𝕜), by rw [diom]; exact (smul_iop_zero A b x₀ k).symm⟩
  · refine ⟨-(iopCoeff A (v₁ A b x₀) k m (m - 1) * iomY A b x₀ k m ⟨m - 1, by omega⟩), ?_⟩
    rw [diom_eq_iomFixed A b x₀ k hpiv]
    exact residual_iomFixed A b x₀ k (isUnit_HI_of_pivots A (v₁ A b x₀) k hpiv) hm0

/-- **(6.22)**: `(r_j, r_i) = 0` for `|i - j| ≤ k`, `i ≠ j`. -/
theorem inner_residual_diom_eq_zero {m : ℕ} (hv : ‖v₁ A b x₀‖ = 1)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) {i j : ℕ} (hi : i ≤ m)
    (hj : j ≤ m) (hij : i ≠ j) (hk : |(i : ℤ) - (j : ℤ)| ≤ (k : ℤ)) :
    inner 𝕜 (b - op A (diom A b x₀ k i)) (b - op A (diom A b x₀ k j)) = 0 := by
  obtain ⟨hk1, hk2⟩ := abs_le.1 hk
  obtain ⟨ci, hci⟩ := residual_diom_eq_smul A b x₀ k (m := i) (fun l hl => hpiv l (by omega))
  obtain ⟨cj, hcj⟩ := residual_diom_eq_smul A b x₀ k (m := j) (fun l hl => hpiv l (by omega))
  rw [hci, hcj, inner_smul_left, inner_smul_right]
  have hvv : inner 𝕜 (iop A (v₁ A b x₀) k i) (iop A (v₁ A b x₀) k j) = (0 : 𝕜) := by
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact inner_iop_eq_zero A (v₁ A b x₀) k hv j i hlt (by omega)
    · rw [← inner_conj_symm, inner_iop_eq_zero A (v₁ A b x₀) k hv i j hlt (by omega), map_zero]
  rw [hvv, mul_zero, mul_zero]

/-- `ζ_m A p_m = r_{m-1} - r_m`, the residual form of (6.21). -/
theorem smul_apply_diomP (m : ℕ) :
    diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) m • op A (diomP A (v₁ A b x₀) k m)
      = (b - op A (diom A b x₀ k m)) - (b - op A (diom A b x₀ k (m + 1))) := by
  rw [diom_succ, map_add, map_smul]
  abel

/-- **(6.23)**: `(A p_j, v_i) = 0` for `j - k + 1 < i < j`. -/
theorem inner_iop_apply_diomP_eq_zero {m : ℕ} (hv : ‖v₁ A b x₀‖ = 1)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) {i j : ℕ} (hj : j + 1 ≤ m)
    (hζ : diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) j ≠ 0) (h₁ : j + 1 < i + k)
    (h₂ : i < j) :
    inner 𝕜 (iop A (v₁ A b x₀) k i) (op A (diomP A (v₁ A b x₀) k j)) = 0 := by
  obtain ⟨cj, hcj⟩ := residual_diom_eq_smul A b x₀ k (m := j) (fun l hl => hpiv l (by omega))
  obtain ⟨cj', hcj'⟩ := residual_diom_eq_smul A b x₀ k (m := j + 1) (fun l hl => hpiv l (by omega))
  have hkey : inner 𝕜 (iop A (v₁ A b x₀) k i)
      (diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) j • op A (diomP A (v₁ A b x₀) k j))
      = 0 := by
    rw [smul_apply_diomP, inner_sub_right, hcj, hcj', inner_smul_right, inner_smul_right,
      inner_iop_eq_zero A (v₁ A b x₀) k hv j i h₂ (by omega),
      inner_iop_eq_zero A (v₁ A b x₀) k hv (j + 1) i (by omega) (by omega), mul_zero, mul_zero,
      sub_zero]
  rw [inner_smul_right] at hkey
  exact (mul_eq_zero.1 hkey).resolve_left hζ

/-- **(6.24)**: for full orthogonalization (`k ≥ m`) the direction vectors are semi-conjugate,
`(A p_j, p_i) = 0` for `i < j`. -/
theorem inner_diomP_apply_diomP_eq_zero {m : ℕ} (hv : ‖v₁ A b x₀‖ = 1) (hk : m ≤ k)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) {i j : ℕ} (hj : j + 1 ≤ m)
    (hζ : diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) j ≠ 0) (hij : i < j) :
    inner 𝕜 (diomP A (v₁ A b x₀) k i) (op A (diomP A (v₁ A b x₀) k j)) = 0 := by
  obtain ⟨cj, hcj⟩ := residual_diom_eq_smul A b x₀ k (m := j) (fun l hl => hpiv l (by omega))
  obtain ⟨cj', hcj'⟩ := residual_diom_eq_smul A b x₀ k (m := j + 1) (fun l hl => hpiv l (by omega))
  have h1 : inner 𝕜 (diomP A (v₁ A b x₀) k i) (iop A (v₁ A b x₀) k j) = 0 :=
    inner_diomP_iop_eq_zero A (v₁ A b x₀) k fun l hl =>
      inner_iop_eq_zero A (v₁ A b x₀) k hv j l (by omega) (by omega)
  have h2 : inner 𝕜 (diomP A (v₁ A b x₀) k i) (iop A (v₁ A b x₀) k (j + 1)) = 0 :=
    inner_diomP_iop_eq_zero A (v₁ A b x₀) k fun l hl =>
      inner_iop_eq_zero A (v₁ A b x₀) k hv (j + 1) l (by omega) (by omega)
  have hkey : inner 𝕜 (diomP A (v₁ A b x₀) k i)
      (diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) j • op A (diomP A (v₁ A b x₀) k j))
      = 0 := by
    rw [smul_apply_diomP, inner_sub_right, hcj, hcj', inner_smul_right, inner_smul_right, h1, h2,
      mul_zero, mul_zero, sub_zero]
  rw [inner_smul_right] at hkey
  exact (mul_eq_zero.1 hkey).resolve_left hζ

/-! ### §6.4.2: IOP with a full band is Algorithm 6.2 -/

private theorem iopW_eq_mgsW (u : ℕ → 𝔼) (w₀ : 𝔼) (N : ℕ) : iopW u 0 w₀ N = mgsW u w₀ N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [iopW_succ, mgsW, ih, iopCoeffOf,
      ite_eq_left_of_eq_true _ _ (eq_true (Nat.zero_le N)), ih]

/-- §6.4.2: with `k` at least as large as the number of steps performed, Algorithm 6.6 is
Algorithm 6.2 — incomplete orthogonalization degenerates to full orthogonalization. -/
theorem iop_eq_arnoldiMGS_of_le : ∀ j, j ≤ k → iop A v k j = arnoldiMGS A v j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjk
    cases j with
    | zero => rw [iop_zero, arnoldiMGS_zero]
    | succ j =>
      have hprev : ∀ i < j + 1, iop A v k i = arnoldiMGS A v i := fun i hi =>
        ih i hi (by omega)
      have hw : iopVecW A v k j = arnoldiMGSW A v j := by
        rw [iopVecW, arnoldiMGSW, show j + 1 - k = 0 by omega, hprev j j.lt_succ_self,
          iopW_congr (v := iop A v k) (v' := arnoldiMGS A v) 0 (op A (arnoldiMGS A v j)) hprev,
          iopW_eq_mgsW]
      rw [iop_succ, arnoldiMGS_succ, hw]

end General

/-! ### Algorithm 6.5: FOM(m) -/

section Restarted

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b : EuclideanSpace 𝕜 (Fin n))

/-- One cycle of **Algorithm 6.5** (FOM(m)): `m` steps of Algorithm 6.4 from `x_0`. -/
noncomputable def fomCycle (m : ℕ) (x₀ : 𝔼) : 𝔼 := fom A b x₀ m

/-- **Algorithm 6.5** (FOM(m)): the restarted iterate after `k` cycles of `m` steps. -/
noncomputable def fomRestarted (m : ℕ) (x₀ : 𝔼) (k : ℕ) : 𝔼 := (fomCycle A b m)^[k] x₀

@[simp]
theorem fomRestarted_zero (m : ℕ) (x₀ : 𝔼) : fomRestarted A b m x₀ 0 = x₀ := rfl

theorem fomRestarted_succ (m : ℕ) (x₀ : 𝔼) (k : ℕ) :
    fomRestarted A b m x₀ (k + 1) = fomCycle A b m (fomRestarted A b m x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- FOM(m) satisfies the Galerkin specification *per cycle*: every restart is an orthogonal
projection method on the Krylov subspace of the current residual. This is all the book claims
about Algorithm 6.5 (Example 6.1 aside, which is numerical). -/
theorem fomRestarted_succ_isGalerkinIterate (m : ℕ) (x₀ : 𝔼) (k : ℕ)
    (hH : FOMDefined A b (fomRestarted A b m x₀ k)
      (mEff A b (fomRestarted A b m x₀ k) m)) :
    Krylov.IsGalerkinIterate (op A) b (fomRestarted A b m x₀ k)
      (mEff A b (fomRestarted A b m x₀ k) m) (fomRestarted A b m x₀ (k + 1)) := by
  rw [fomRestarted_succ]
  exact fom_isGalerkinIterate A b _ hH

end Restarted


/-! ### The numbered results of §6.4, in the book's real setting -/

section BookResults

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))
  (v : EuclideanSpace ℝ (Fin n)) (k : ℕ)

/-- **(6.16)–(6.17)**. The Full Orthogonalization Method — Arnoldi's method started at
`v_1 = r_0/β` followed by `y_m = H_m^{-1}(β e_1)`, `x_m = x_0 + V_m y_m` — is exactly the
orthogonal projection method (6.15) onto `𝒦_m(A, r_0)`. -/
theorem eq_6_16_17 {m : ℕ} (hH : FOMDefined A b x₀ m) (hm : m ≤ grade A (v₁ A b x₀)) :
    Krylov.IsGalerkinIterate (op A) b x₀ m (fomFixed A b x₀ m) :=
  fomFixed_isGalerkinIterate A b x₀ hH hm

/-- **(6.16)–(6.17)**, converse: the orthogonal projection method onto `𝒦_m(A, r_0)` has no
other solution than the FOM iterate. -/
theorem eq_6_16_17_unique {m : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hH : FOMDefined A b x₀ m)
    (hm : m ≤ grade A (v₁ A b x₀)) (hx : Krylov.IsGalerkinIterate (op A) b x₀ m x) :
    x = fomFixed A b x₀ m :=
  eq_fomFixed_of_isGalerkinIterate A b x₀ hH hm hx

/-- §6.4.1: FOM is defined at step `m` exactly when the projection method has a unique
solution. -/
theorem existsUnique_isGalerkinIterate_iff {m : ℕ} (hm : m ≤ grade A (v₁ A b x₀)) :
    (∃! x, Krylov.IsGalerkinIterate (op A) b x₀ m x) ↔ FOMDefined A b x₀ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · refine ⟨fun _ => (Matrix.isUnit_iff_isUnit_det _).2 (by simp), fun _ => ⟨x₀, ⟨by simp, ?_⟩,
      fun y hy => ?_⟩⟩
    · rw [Krylov.subspace_zero, Submodule.bot_orthogonal_eq_top]
      exact Submodule.mem_top
    · have hmem := hy.mem
      rw [Krylov.subspace_zero, Submodule.mem_bot, sub_eq_zero] at hmem
      exact hmem
  · have hr : b - op A x₀ ≠ 0 := residual_ne_zero_of_lt_grade A b x₀ hm0 hm
    rw [FOMDefined, H_v₁ A b x₀ hr]
    exact Krylov.existsUnique_isGalerkinIterate_iff_isUnit (by rwa [← grade_v₁])

/-- §6.4.1: `V_mᵀ r_0 = β e_1`. -/
theorem Vt_r₀ (m : ℕ) :
    (V A (v₁ A b x₀) m)ᵀ *ᵥ WithLp.ofLp (r₀ A b x₀) = (β A b x₀ : ℝ) • e₁ m := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact conjTranspose_V_mulVec_r₀ A b x₀ m

/-- **Proposition 6.7**. The residual vector of the FOM iterate is
`b - A x_m = -h_{m+1,m} (e_mᵀ y_m) v_{m+1}`. -/
theorem prop_6_7 {m : ℕ} (hH : FOMDefined A b x₀ m) (hm : m ≤ grade A (v₁ A b x₀))
    (hm0 : 0 < m) :
    b - op A (fomFixed A b x₀ m)
      = -(arnoldiCoeff A (v₁ A b x₀) m (m - 1) * fomY A b x₀ m ⟨m - 1, by omega⟩) •
          arnoldiCGS A (v₁ A b x₀) m :=
  residual_fomFixed A b x₀ hH hm hm0

/-- **(6.18)**: `‖b - A x_m‖₂ = h_{m+1,m} |e_mᵀ y_m|`. -/
theorem eq_6_18 {m : ℕ} (hH : FOMDefined A b x₀ m) (hm : m ≤ grade A (v₁ A b x₀)) (hm0 : 0 < m) :
    ‖b - op A (fomFixed A b x₀ m)‖
      = |arnoldiCoeff A (v₁ A b x₀) m (m - 1)| * |fomY A b x₀ m ⟨m - 1, by omega⟩| := by
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact norm_residual_fomFixed A b x₀ hH hm hm0

/-! #### §6.4.2: the incomplete orthogonalization methods -/

/-- §6.4.2: (6.6)–(6.7) hold verbatim for the incomplete orthogonalization procedure, since
their proof never used the orthogonality of the `v_i`. -/
theorem iop_eq_6_7 (m : ℕ) : A * VI A v k m = VI A v k (m + 1) * HbarI A v k m :=
  mul_VI_eq A v k m

/-- §6.4.2: **Proposition 6.7 for IOM**. -/
theorem prop_6_7_iom {m : ℕ} (hH : IsUnit (HI A (v₁ A b x₀) k m)) (hm0 : 0 < m) :
    b - op A (iomFixed A b x₀ k m)
      = -(iopCoeff A (v₁ A b x₀) k m (m - 1) * iomY A b x₀ k m ⟨m - 1, by omega⟩) •
          iop A (v₁ A b x₀) k m :=
  residual_iomFixed A b x₀ k hH hm0

/-- §6.4.2: **(6.18) for IOM**. -/
theorem eq_6_18_iom {m : ℕ} (hH : IsUnit (HI A (v₁ A b x₀) k m)) (hm0 : 0 < m)
    (hv : ‖v₁ A b x₀‖ = 1) :
    ‖b - op A (iomFixed A b x₀ k m)‖
      = |iopCoeff A (v₁ A b x₀) k m (m - 1)| * |iomY A b x₀ k m ⟨m - 1, by omega⟩| := by
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact norm_residual_iomFixed A b x₀ k hH hm0 hv

/-- §6.4.2: the DIOM residual norm is `h_{m+1,m} |ζ_m/u_mm|`. -/
theorem diom_residual {m : ℕ} (hm0 : 0 < m) (hv : ‖v₁ A b x₀‖ = 1)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    ‖b - op A (diom A b x₀ k m)‖
      = |iopCoeff A (v₁ A b x₀) k m (m - 1)| *
        |diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : ℝ) (m - 1)
          / dioU (iopCoeff A (v₁ A b x₀) k) (m - 1) (m - 1)| := by
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact norm_residual_diom A b x₀ k hm0 hv hpiv

/-- §6.4.2: the Hessenberg LU factorization `H_m = L_m U_m` without pivoting: `L_m` is unit
lower bidiagonal and `U_m` is upper triangular, banded with `k` diagonals. -/
theorem hessLU_spec (h : ℕ → ℕ → ℝ) (hh : ∀ a c, c + 1 < a → h a c = 0)
    (hband : ∀ a c, a + k ≤ c → h a c = 0) {m : ℕ} (hpiv : ∀ l, l < m → dioU h l l ≠ 0) :
    (hessLU h m).1 * (hessLU h m).2 = Krylov.hessenbergSqOf h m ∧
      (∀ i : Fin m, (hessLU h m).1 i i = 1) ∧
      (∀ i j : Fin m, (i : ℕ) ≠ (j : ℕ) → (i : ℕ) ≠ (j : ℕ) + 1 → (hessLU h m).1 i j = 0) ∧
      (hessLU h m).2.IsUpperTriangular ∧
      (∀ i j : Fin m, (i : ℕ) + k ≤ (j : ℕ) → (hessLU h m).2 i j = 0) :=
  ⟨hessL_mul_hessU h hh hpiv, fun i => hessL_self h i, fun _ _ h1 h2 => hessL_eq_zero h h1 h2,
    hessU_isUpperTriangular h m, fun _ _ hij => hessU_eq_zero_of_add_le hband hij⟩

/-- §6.4.2, **(6.20)–(6.21)**: Algorithm 6.8 (DIOM) is mathematically equivalent to
Algorithm 6.7 (IOM). -/
theorem alg_6_8_eq_alg_6_7 {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    diom A b x₀ k m = iomFixed A b x₀ k m :=
  diom_eq_iomFixed A b x₀ k hpiv

/-- **Proposition 6.8**. IOM and DIOM are mathematically equivalent to a projection process
onto `𝒦_m` orthogonally to `L_m = span {z_1, …, z_m}`, `z_i = v_i - (v_i, v_{m+1}) v_{m+1}`. -/
theorem prop_6_8 {m : ℕ} (hH : IsUnit (HI A (v₁ A b x₀) k m)) (hm0 : 0 < m)
    (hnorm : ‖iop A (v₁ A b x₀) k m‖ = 1)
    (hspan : Submodule.span ℝ (Set.range fun i : Fin m => iop A (v₁ A b x₀) k (i : ℕ))
      = krylov A (r₀ A b x₀) m) :
    IsPetrovGalerkin (op A) b x₀ (krylov A (r₀ A b x₀) m)
      (Submodule.span ℝ (Set.range fun i : Fin m =>
        iop A (v₁ A b x₀) k (i : ℕ)
          - inner ℝ (iop A (v₁ A b x₀) k m) (iop A (v₁ A b x₀) k (i : ℕ))
              • iop A (v₁ A b x₀) k m))
      (iomFixed A b x₀ k m) :=
  iomFixed_isPetrovGalerkin A b x₀ k hH hm0 hnorm hspan

/-- **(6.22)** (P-6.22): the DIOM residuals are orthogonal within a window of `k` steps. -/
theorem eq_6_22 {m : ℕ} (hv : ‖v₁ A b x₀‖ = 1)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) {i j : ℕ} (hi : i ≤ m)
    (hj : j ≤ m) (hij : i ≠ j) (hk : |(i : ℤ) - (j : ℤ)| ≤ (k : ℤ)) :
    inner ℝ (b - op A (diom A b x₀ k i)) (b - op A (diom A b x₀ k j)) = 0 :=
  inner_residual_diom_eq_zero A b x₀ k hv hpiv hi hj hij hk

/-- **(6.23)** (P-6.22): `(A p_j, v_i) = 0` for `j - k + 1 < i < j`. -/
theorem eq_6_23 {m : ℕ} (hv : ‖v₁ A b x₀‖ = 1)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) {i j : ℕ} (hj : j + 1 ≤ m)
    (hζ : diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : ℝ) j ≠ 0) (h₁ : j + 1 < i + k)
    (h₂ : i < j) :
    inner ℝ (iop A (v₁ A b x₀) k i) (op A (diomP A (v₁ A b x₀) k j)) = 0 :=
  inner_iop_apply_diomP_eq_zero A b x₀ k hv hpiv hj hζ h₁ h₂

/-- **(6.24)** (P-6.22): for full orthogonalization (`k ≥ m`) the `p_i` are semi-conjugate,
`(A p_j, p_i) = 0` for `i < j`. -/
theorem eq_6_24 {m : ℕ} (hv : ‖v₁ A b x₀‖ = 1) (hk : m ≤ k)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) {i j : ℕ} (hj : j + 1 ≤ m)
    (hζ : diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : ℝ) j ≠ 0) (hij : i < j) :
    inner ℝ (diomP A (v₁ A b x₀) k i) (op A (diomP A (v₁ A b x₀) k j)) = 0 :=
  inner_diomP_apply_diomP_eq_zero A b x₀ k hv hk hpiv hj hζ hij

/-- §6.4.2: with a full band Algorithm 6.6 is Algorithm 6.2 — incomplete orthogonalization
degenerates to Arnoldi's method. -/
theorem alg_6_6_eq_alg_6_2 {j : ℕ} (hjk : j ≤ k) : iop A v k j = arnoldiMGS A v j :=
  iop_eq_arnoldiMGS_of_le A v k j hjk

end BookResults

end SaadSparse.Ch06
