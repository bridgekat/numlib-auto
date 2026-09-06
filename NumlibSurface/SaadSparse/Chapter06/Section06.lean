import Numlib.Krylov.Arnoldi
import Numlib.Krylov.Lanczos
import Numlib.Krylov.OrthogonalPolynomials
import Numlib.Krylov.Subspace
import Numlib.LinearAlgebra.Matrix.Hessenberg
import NumlibSurface.SaadSparse.Chapter06.Section03

/-!
# Saad, §6.6: the symmetric Lanczos algorithm

Surface file for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003, §6.6.

**Algorithm 6.15** is `lanczosState`, a two-term state recursion whose fields are read off by
`lanczosV` (the vectors `v_j`), `lanczosAlpha` (`α_j`) and `lanczosBeta` (`β_j`, with
`lanczosBeta A v₁ 0 = 0` for the book's `β_1 = 0`). The tridiagonal matrix `T_m` of (6.84) is
`T`, and its `(m+1) × m` extension is `Tbar`.

The structural result of the section is **Theorem 6.19** (`theorem_6_19`) together with the
observation that Algorithm 6.15 *is* Arnoldi's method for a symmetric matrix: `lanczosV_eq`
identifies its vectors with those of Algorithm 6.1 (hence with Algorithm 6.2, the modified
Gram–Schmidt form the book actually derives it from), `lanczosAlpha_eq` and `lanczosBeta_eq`
identify its coefficients with `h_{jj}` and `h_{j+1,j}`, and `T_eq_H` gives `T_m = H_m` (6.84).
Everything else in §6.6 and §6.7 is then inherited from the Arnoldi theory of
`Chapter06/Section03.lean` rather than redeveloped.

§6.6.2 contributes the inner product (6.85), `polyInner`, the isomorphism `p ↦ p(A) v_1` from
`P_{m-1}` onto `𝒦_m` (`polyToKrylov`, `polyToKrylov_bijective`), its nondegeneracy
(`polyInner_nondegenerate`) and the Lanczos polynomials `lanczosPoly` with `v_i = q_{i-1}(A) v_1`
and their orthogonality. The two facts the book cites without proof are
`equation_6_85_charpoly_isMinOn` — the characteristic polynomial of `T_m` minimizes
`‖·‖_{v_1}` among the monic polynomials of degree `m` — and `equation_6_85_lanczos_charpoly`,
that the Lanczos process computes `p_{T_m}(A) v_1` up to the scalar `β_2 β_3 ⋯ β_{m+1}`; both are
read off the backbone's Ritz-value and orthogonal-polynomial material
(`Numlib/Eigen/RayleighRitz.lean`, `Numlib/Krylov/OrthogonalPolynomials.lean`).

Indices are `0`-based as in `Chapter06/Section03.lean`: `lanczosV A v₁ j` is the book's `v_{j+1}`,
`lanczosAlpha A v₁ j` is `α_{j+1}` and `lanczosBeta A v₁ j` is `β_{j+1}`. Definitions are
polymorphic in `𝕜`; the numbered results are stated over `ℝ` with `A` symmetric, the book's
generality in §6.6.
-/

open Polynomial

namespace SaadSparse.Ch06

/-- The running state of **Algorithm 6.15** after `j` steps. -/
structure LanczosState (n : ℕ) (𝕜 : Type*) [RCLike 𝕜] where
  /-- The previous Lanczos vector `v_{j-1}`; `0` at `j = 0`, the book's `v_0 = 0`. -/
  vPrev : EuclideanSpace 𝕜 (Fin n)
  /-- The current Lanczos vector `v_j`. -/
  v : EuclideanSpace 𝕜 (Fin n)
  /-- The coefficient `β_j = ‖w_{j-1}‖` used on line 3; `0` at `j = 0`, the book's `β_1 = 0`. -/
  beta : ℝ
  /-- The coefficient `α_{j-1}` produced on line 4 of the previous step; `0` at `j = 0`. -/
  alpha : 𝕜

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Algorithm 6.15 -/

/-- The coefficient `α_j = (w_j, v_j)` computed on line 4 of **Algorithm 6.15**, where `w_j` is
the vector `A v_j - β_j v_{j-1}` of line 3. -/
noncomputable def lanczosStepAlpha (A : Matrix (Fin n) (Fin n) 𝕜) (s : LanczosState n 𝕜) : 𝕜 :=
  inner 𝕜 s.v (op A s.v - (s.beta : 𝕜) • s.vPrev)

/-- The vector `w_j = A v_j - β_j v_{j-1} - α_j v_j` left by lines 3 and 5 of
**Algorithm 6.15**. -/
noncomputable def lanczosStepW (A : Matrix (Fin n) (Fin n) 𝕜) (s : LanczosState n 𝕜) :
    EuclideanSpace 𝕜 (Fin n) :=
  op A s.v - (s.beta : 𝕜) • s.vPrev - lanczosStepAlpha A s • s.v

/-- One pass through lines 3–7 of **Algorithm 6.15**: `w := A v_j - β_j v_{j-1}`,
`α_j := (w, v_j)`, `w := w - α_j v_j`, `β_{j+1} := ‖w‖₂`, `v_{j+1} := w/β_{j+1}`. The book's
"if `β_{j+1} = 0` then Stop" is Lean's `x / 0 = 0`: all later vectors are `0`. -/
noncomputable def lanczosStep (A : Matrix (Fin n) (Fin n) 𝕜) (s : LanczosState n 𝕜) :
    LanczosState n 𝕜 :=
  { vPrev := s.v, v := ((‖lanczosStepW A s‖ : 𝕜))⁻¹ • lanczosStepW A s,
    beta := ‖lanczosStepW A s‖, alpha := lanczosStepAlpha A s }

theorem lanczosStepAlpha_eq (A : Matrix (Fin n) (Fin n) 𝕜) (s : LanczosState n 𝕜) :
    lanczosStepAlpha A s = inner 𝕜 s.v (op A s.v - (s.beta : 𝕜) • s.vPrev) := rfl

theorem lanczosStepW_eq (A : Matrix (Fin n) (Fin n) 𝕜) (s : LanczosState n 𝕜) :
    lanczosStepW A s =
      op A s.v - (s.beta : 𝕜) • s.vPrev - lanczosStepAlpha A s • s.v := rfl

theorem lanczosStep_eq (A : Matrix (Fin n) (Fin n) 𝕜) (s : LanczosState n 𝕜) :
    lanczosStep A s =
      { vPrev := s.v, v := ((‖lanczosStepW A s‖ : 𝕜))⁻¹ • lanczosStepW A s,
        beta := ‖lanczosStepW A s‖, alpha := lanczosStepAlpha A s } := rfl

/-- **Algorithm 6.15** (symmetric Lanczos) run for `j` steps from the unit vector `v₁`. -/
noncomputable def lanczosState (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : 𝔼) (j : ℕ) :
    LanczosState n 𝕜 :=
  (lanczosStep A)^[j] { vPrev := 0, v := v₁, beta := 0, alpha := 0 }

variable (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ : EuclideanSpace 𝕜 (Fin n))

/-- The Lanczos vector `v_{j+1}` of Algorithm 6.15 (`0`-based: `lanczosV A v₁ 0 = v₁`). -/
noncomputable def lanczosV (j : ℕ) : 𝔼 := (lanczosState A v₁ j).v

/-- The diagonal coefficient `α_{j+1} = (w_j, v_j)` of Algorithm 6.15, line 4. -/
noncomputable def lanczosAlpha (j : ℕ) : ℝ := RCLike.re (lanczosState A v₁ (j + 1)).alpha

/-- The off-diagonal coefficient `β_{j+1} = ‖w_{j-1}‖₂` of Algorithm 6.15, line 6, with
`lanczosBeta A v₁ 0 = 0` for the book's `β_1 = 0` on line 1. -/
noncomputable def lanczosBeta (j : ℕ) : ℝ := (lanczosState A v₁ j).beta

@[simp] theorem lanczosV_zero : lanczosV A v₁ 0 = v₁ := rfl

@[simp] theorem lanczosBeta_zero : lanczosBeta A v₁ 0 = 0 := rfl

theorem lanczosState_succ (j : ℕ) :
    lanczosState A v₁ (j + 1) = lanczosStep A (lanczosState A v₁ j) :=
  Function.iterate_succ_apply' _ _ _

/-! ### Identification with Arnoldi's method (Theorem 6.19 and §6.6.1) -/

/-- The single step of the identification: whatever produces the backbone `w_j` from `v_j` and
the term `β_j v_{j-1}` sends a state describing step `j` to the state describing step `j+1`. -/
private theorem lanczosStep_of {s : LanczosState n 𝕜} {j : ℕ}
    (hvj : s.v = Arnoldi.vec (op A) v₁ j)
    (halpha : lanczosStepAlpha A s = Arnoldi.coeff (op A) v₁ j j)
    (hw : lanczosStepW A s = Arnoldi.w (op A) v₁ j) :
    lanczosStep A s =
      { vPrev := Arnoldi.vec (op A) v₁ j, v := Arnoldi.vec (op A) v₁ (j + 1),
        beta := Lanczos.beta (op A) v₁ j, alpha := Arnoldi.coeff (op A) v₁ j j } := by
  rw [lanczosStep_eq, hvj, halpha, hw, Arnoldi.vec_succ_eq]
  rfl

/-- The state of Algorithm 6.15 after `j + 1` steps, in terms of the backbone Arnoldi data. -/
private theorem lanczosState_succ_eq (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosState A v₁ (j + 1) =
      { vPrev := Arnoldi.vec (op A) v₁ j, v := Arnoldi.vec (op A) v₁ (j + 1),
        beta := Lanczos.beta (op A) v₁ j, alpha := Arnoldi.coeff (op A) v₁ j j } := by
  have hvec0 : Arnoldi.vec (op A) v₁ 0 = v₁ :=
    (arnoldiCGS_eq_vec A v₁ hv 0).symm.trans (arnoldiCGS_zero A v₁)
  induction j with
  | zero =>
    have halpha : lanczosStepAlpha A (lanczosState A v₁ 0) = Arnoldi.coeff (op A) v₁ 0 0 := by
      rw [lanczosStepAlpha_eq, Arnoldi.coeff]
      change (inner 𝕜 v₁ (op A v₁ - ((0 : ℝ) : 𝕜) • (0 : 𝔼)) : 𝕜) = _
      rw [hvec0]
      simp
    rw [lanczosState_succ]
    refine lanczosStep_of A v₁ hvec0.symm halpha ?_
    rw [lanczosStepW_eq, halpha, Arnoldi.w, Finset.sum_range_one, hvec0]
    change op A v₁ - ((0 : ℝ) : 𝕜) • (0 : 𝔼) - Arnoldi.coeff (op A) v₁ 0 0 • v₁ = _
    simp
  | succ j ih =>
    have halpha : lanczosStepAlpha A (lanczosState A v₁ (j + 1))
        = Arnoldi.coeff (op A) v₁ (j + 1) (j + 1) := by
      rw [lanczosStepAlpha_eq, ih]
      change (inner 𝕜 (Arnoldi.vec (op A) v₁ (j + 1)) (op A (Arnoldi.vec (op A) v₁ (j + 1)) -
        ((Lanczos.beta (op A) v₁ j : ℝ) : 𝕜) • Arnoldi.vec (op A) v₁ j) : 𝕜) = _
      rw [inner_sub_right, inner_smul_right,
        Arnoldi.inner_vec_eq_zero (op A) v₁ (Nat.succ_ne_self j), mul_zero, sub_zero]
      rfl
    rw [lanczosState_succ]
    refine lanczosStep_of A v₁ (by rw [ih]) halpha ?_
    rw [lanczosStepW_eq, halpha, ih]
    change op A (Arnoldi.vec (op A) v₁ (j + 1)) -
      ((Lanczos.beta (op A) v₁ j : ℝ) : 𝕜) • Arnoldi.vec (op A) v₁ j -
      Arnoldi.coeff (op A) v₁ (j + 1) (j + 1) • Arnoldi.vec (op A) v₁ (j + 1) = _
    rw [Lanczos.w_succ_eq v₁ hA j, ← Lanczos.coe_alpha v₁ hA (j + 1)]
    abel

/-- §6.6.1: the vectors of **Algorithm 6.15** are the Arnoldi vectors of `Chapter06/Section03.lean`.
This is the sentence "this leads to the following form of the modified Gram–Schmidt variant of
Arnoldi's method": for symmetric `A` the inner loop of Algorithm 6.2 subtracts only the two
terms `α_j v_j` and `β_j v_{j-1}`. -/
theorem lanczosV_eq_vec (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosV A v₁ j = Arnoldi.vec (op A) v₁ j := by
  cases j with
  | zero => exact ((arnoldiCGS_eq_vec A v₁ hv 0).symm.trans (arnoldiCGS_zero A v₁)).symm
  | succ j => rw [lanczosV, lanczosState_succ_eq A v₁ hA hv j]

/-- §6.6.1: Algorithm 6.15 computes the vectors of Algorithm 6.1. -/
theorem lanczosV_eq (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosV A v₁ j = arnoldiCGS A v₁ j := by
  rw [lanczosV_eq_vec A v₁ hA hv, arnoldiCGS_eq_vec A v₁ hv]

/-- §6.6.1: Algorithm 6.15 computes the vectors of Algorithm 6.2 (modified Gram–Schmidt). -/
theorem lanczosV_eq_arnoldiMGS (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosV A v₁ j = arnoldiMGS A v₁ j := by
  rw [lanczosV_eq A v₁ hA hv, arnoldiMGS_eq_arnoldiCGS A v₁ hv]

/-- `α_j = h_{jj}`. -/
theorem lanczosAlpha_eq_arnoldiCoeff (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    ((lanczosAlpha A v₁ j : ℝ) : 𝕜) = arnoldiCoeff A v₁ j j := by
  rw [lanczosAlpha, lanczosState_succ_eq A v₁ hA hv, arnoldiCoeff_eq A v₁ hv]
  exact (Arnoldi.coeff_diag_re_of_isSymmetric hA v₁ j).symm

/-- `α_j` is the backbone Lanczos coefficient `⟪v_j, A v_j⟫`. -/
theorem lanczosAlpha_eq (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosAlpha A v₁ j = Lanczos.alpha (op A) v₁ j := by
  rw [lanczosAlpha, lanczosState_succ_eq A v₁ hA hv]
  rfl

/-- `β_{j+1} = h_{j+1,j} = ‖w_j‖₂`, the backbone off-diagonal Lanczos coefficient. -/
theorem lanczosBeta_succ_eq (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosBeta A v₁ (j + 1) = Lanczos.beta (op A) v₁ j := by
  rw [lanczosBeta, lanczosState_succ_eq A v₁ hA hv]

/-- `β_{j+1} = h_{j+1,j}`. -/
theorem lanczosBeta_succ_eq_arnoldiCoeff (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    ((lanczosBeta A v₁ (j + 1) : ℝ) : 𝕜) = arnoldiCoeff A v₁ (j + 1) j := by
  rw [lanczosBeta_succ_eq A v₁ hA hv, arnoldiCoeff_eq A v₁ hv, Lanczos.coe_beta]

theorem lanczosBeta_nonneg (j : ℕ) : 0 ≤ lanczosBeta A v₁ j := by
  cases j with
  | zero => exact le_rfl
  | succ j =>
    rw [lanczosBeta, lanczosState_succ, lanczosStep_eq]
    exact norm_nonneg _

/-- Breakdown: `β_{j+1} = 0` exactly when the grade of `v₁` has been reached. -/
theorem lanczosBeta_succ_eq_zero_iff (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosBeta A v₁ (j + 1) = 0 ↔ grade A v₁ ≤ j + 1 := by
  rw [lanczosBeta_succ_eq A v₁ hA hv, Lanczos.beta_eq_zero_iff v₁ hA, grade_eq]

/-- `α_j = (A v_j, v_j)`: the coefficient of Algorithm 6.15, line 4, as a Rayleigh quotient. -/
theorem lanczosAlpha_eq_inner (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    ((lanczosAlpha A v₁ j : ℝ) : 𝕜) = inner 𝕜 (lanczosV A v₁ j) (op A (lanczosV A v₁ j)) := by
  rw [lanczosAlpha_eq_arnoldiCoeff A v₁ hA hv, arnoldiCoeff, lanczosV_eq A v₁ hA hv]

/-- `β_{j+1} = (A v_j, v_{j+1})`. -/
theorem lanczosBeta_succ_eq_inner (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    ((lanczosBeta A v₁ (j + 1) : ℝ) : 𝕜)
      = inner 𝕜 (lanczosV A v₁ (j + 1)) (op A (lanczosV A v₁ j)) := by
  rw [lanczosBeta_succ_eq_arnoldiCoeff A v₁ hA hv, arnoldiCoeff, lanczosV_eq A v₁ hA hv,
    lanczosV_eq A v₁ hA hv]

/-- The three-term recurrence of Algorithm 6.15 at the first step: `A v_1 = α_1 v_1 + β_2 v_2`
(lines 3–7 with `β_1 = 0` and `v_0 = 0`). -/
theorem apply_lanczosV_zero (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) :
    op A (lanczosV A v₁ 0) = (lanczosAlpha A v₁ 0 : 𝕜) • lanczosV A v₁ 0 +
      (lanczosBeta A v₁ 1 : 𝕜) • lanczosV A v₁ 1 := by
  rw [lanczosV_eq_vec A v₁ hA hv, lanczosV_eq_vec A v₁ hA hv, lanczosAlpha_eq A v₁ hA hv,
    lanczosBeta_succ_eq A v₁ hA hv]
  exact Lanczos.apply_vec_zero v₁ hA

/-- The three-term recurrence of Algorithm 6.15, lines 3–7:
`A v_{j+1} = β_{j+1} v_j + α_{j+1} v_{j+1} + β_{j+2} v_{j+2}`. -/
theorem apply_lanczosV (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    op A (lanczosV A v₁ (j + 1)) = (lanczosBeta A v₁ (j + 1) : 𝕜) • lanczosV A v₁ j +
      (lanczosAlpha A v₁ (j + 1) : 𝕜) • lanczosV A v₁ (j + 1) +
      (lanczosBeta A v₁ (j + 2) : 𝕜) • lanczosV A v₁ (j + 2) := by
  have hb2 : lanczosBeta A v₁ (j + 2) = Lanczos.beta (op A) v₁ (j + 1) :=
    lanczosBeta_succ_eq A v₁ hA hv (j + 1)
  rw [lanczosV_eq_vec A v₁ hA hv, lanczosV_eq_vec A v₁ hA hv, lanczosV_eq_vec A v₁ hA hv,
    lanczosAlpha_eq A v₁ hA hv, lanczosBeta_succ_eq A v₁ hA hv j, hb2]
  exact Lanczos.apply_vec v₁ hA j

/-- The Lanczos vectors are orthogonal. -/
theorem inner_lanczosV_eq_zero (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (lanczosV A v₁ i) (lanczosV A v₁ j) = 0 := by
  rw [lanczosV_eq A v₁ hA hv, lanczosV_eq A v₁ hA hv]
  exact inner_arnoldiCGS_eq_zero A v₁ hv h

/-- The Lanczos vectors lie in the Krylov subspaces: `v_{j+1} ∈ 𝒦_{j+1}`. -/
theorem lanczosV_mem_krylov (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosV A v₁ j ∈ krylov A v₁ (j + 1) := by
  rw [lanczosV_eq_vec A v₁ hA hv, krylov_eq]
  exact Arnoldi.vec_mem_subspace (op A) v₁ j

/-- The Lanczos vector `v_{j+1}` is orthogonal to `𝒦_j`. -/
theorem lanczosV_mem_orthogonal (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosV A v₁ j ∈ (krylov A v₁ j)ᗮ := by
  rw [lanczosV_eq_vec A v₁ hA hv, krylov_eq]
  exact Arnoldi.vec_mem_orthogonal (op A) v₁ j

/-! ### The tridiagonal matrices `T_m` (6.84) and `T̄_m` -/

/-- (6.84): `T_m = tridiag(β_i, α_i, β_{i+1})`, the symmetric tridiagonal Lanczos matrix. -/
noncomputable def T (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then lanczosAlpha A v₁ i
    else if (i : ℕ) + 1 = j then lanczosBeta A v₁ j
    else if (j : ℕ) + 1 = i then lanczosBeta A v₁ i
    else 0

/-- The `(m+1) × m` matrix `T̄_m` obtained from `T_{m+1}` by deleting its last column, the
Lanczos analogue of `H̄_m`. -/
noncomputable def Tbar (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then lanczosAlpha A v₁ i
    else if (i : ℕ) + 1 = j then lanczosBeta A v₁ j
    else if (j : ℕ) + 1 = i then lanczosBeta A v₁ i
    else 0

@[simp] theorem T_apply {m : ℕ} (i j : Fin m) :
    T A v₁ m i j =
      if (i : ℕ) = j then lanczosAlpha A v₁ i
      else if (i : ℕ) + 1 = j then lanczosBeta A v₁ j
      else if (j : ℕ) + 1 = i then lanczosBeta A v₁ i
      else 0 := rfl

@[simp] theorem Tbar_apply {m : ℕ} (i : Fin (m + 1)) (j : Fin m) :
    Tbar A v₁ m i j =
      if (i : ℕ) = j then lanczosAlpha A v₁ i
      else if (i : ℕ) + 1 = j then lanczosBeta A v₁ j
      else if (j : ℕ) + 1 = i then lanczosBeta A v₁ i
      else 0 := rfl

/-- `T_m` is the backbone tridiagonal Lanczos matrix. -/
theorem T_eq_tridiag (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (m : ℕ) :
    T A v₁ m = Lanczos.tridiag (op A) v₁ m := by
  ext i j
  rw [T_apply]
  simp only [Lanczos.tridiag, Matrix.of_apply]
  split_ifs with h₁ h₂ h₃
  · rw [lanczosAlpha_eq A v₁ hA hv]
  · rw [← h₂, lanczosBeta_succ_eq A v₁ hA hv]
  · rw [← h₃, lanczosBeta_succ_eq A v₁ hA hv]
  · rfl

/-- `T̄_m` is the backbone extended tridiagonal Lanczos matrix. -/
theorem Tbar_eq_tridiagExt (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (m : ℕ) :
    Tbar A v₁ m = Lanczos.tridiagExt (op A) v₁ m := by
  ext i j
  rw [Tbar_apply]
  simp only [Lanczos.tridiagExt, Matrix.of_apply]
  split_ifs with h₁ h₂ h₃
  · rw [lanczosAlpha_eq A v₁ hA hv]
  · rw [← h₂, lanczosBeta_succ_eq A v₁ hA hv]
  · rw [← h₃, lanczosBeta_succ_eq A v₁ hA hv]
  · rfl

/-- (6.84): `H_m = T_m`, entrywise over `𝕜`. -/
theorem map_T_eq_H (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (m : ℕ) :
    (T A v₁ m).map (algebraMap ℝ 𝕜) = H A v₁ m := by
  rw [T_eq_tridiag A v₁ hA hv, H_eq A v₁ hv, Lanczos.hessenbergSq_eq_map_tridiag v₁ hA m]

/-- `H̄_m = T̄_m`, entrywise over `𝕜`. -/
theorem map_Tbar_eq_Hbar (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (m : ℕ) :
    (Tbar A v₁ m).map (algebraMap ℝ 𝕜) = Hbar A v₁ m := by
  rw [Tbar_eq_tridiagExt A v₁ hA hv, Hbar_eq A v₁ hv,
    Lanczos.hessenberg_eq_map_tridiagExt v₁ hA m]

theorem T_isTridiagonal (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (m : ℕ) :
    (T A v₁ m).IsTridiagonal := by
  rw [T_eq_tridiag A v₁ hA hv]
  exact Lanczos.tridiag_isTridiagonal (op A) v₁ m

theorem T_isSymm (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (m : ℕ) : (T A v₁ m).IsSymm := by
  rw [T_eq_tridiag A v₁ hA hv]
  exact Lanczos.tridiag_isSymm (op A) v₁ m

/-! ### §6.6.2: the inner product (6.85) and the Lanczos polynomials -/

/-- (6.85): `⟨p, q⟩_{v₁} = (p(A) v₁, q(A) v₁)`. -/
noncomputable def polyInner (p q : 𝕜[X]) : 𝕜 :=
  inner 𝕜 (aeval (op A) q v₁) (aeval (op A) p v₁)

theorem polyInner_self_eq (p : 𝕜[X]) :
    polyInner A v₁ p p = ((‖aeval (op A) p v₁‖ ^ 2 : ℝ) : 𝕜) := by
  rw [polyInner, inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]

theorem polyInner_self_eq_zero_iff (p : 𝕜[X]) :
    polyInner A v₁ p p = 0 ↔ aeval (op A) p v₁ = 0 := by
  rw [polyInner, inner_self_eq_zero]

/-- §6.6.2, first property: the evaluation map `p ↦ p(A) v₁` from `P_{m-1}` to `𝒦_m`. -/
noncomputable def polyToKrylov (m : ℕ) : degreeLT 𝕜 m →ₗ[𝕜] krylov A v₁ m :=
  ((Krylov.polyEval (op A) v₁).domRestrict (degreeLT 𝕜 m)).codRestrict (krylov A v₁ m) fun p => by
    rw [krylov_eq_map_degreeLT]
    exact Submodule.mem_map_of_mem p.2

@[simp] theorem coe_polyToKrylov {m : ℕ} (p : degreeLT 𝕜 m) :
    (polyToKrylov A v₁ m p : 𝔼) = aeval (op A) (p : 𝕜[X]) v₁ := rfl

theorem polyToKrylov_surjective (m : ℕ) : Function.Surjective (polyToKrylov A v₁ m) := by
  rintro ⟨x, hx⟩
  obtain ⟨p, hp, hpx⟩ := (mem_krylov_iff_exists_aeval A v₁).1 hx
  exact ⟨⟨p, Polynomial.mem_degreeLT.2 hp⟩, Subtype.ext hpx⟩

/-- §6.6.2, first property: for `m` at most the grade of `v₁` the map `q ↦ q(A) v₁` is an
isomorphism from `P_{m-1}` onto `𝒦_m`. -/
theorem polyToKrylov_bijective {m : ℕ} (hm : m ≤ grade A v₁) :
    Function.Bijective (polyToKrylov A v₁ m) := by
  have : FiniteDimensional 𝕜 (degreeLT 𝕜 m) :=
    (Polynomial.degreeLTEquiv 𝕜 m).symm.finiteDimensional
  have hdim : Module.finrank 𝕜 (degreeLT 𝕜 m) = Module.finrank 𝕜 (krylov A v₁ m) := by
    rw [(Polynomial.degreeLTEquiv 𝕜 m).finrank_eq, Module.finrank_fin_fun 𝕜,
      finrank_krylov A v₁ m, min_eq_left hm]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2
    (polyToKrylov_surjective A v₁ m), polyToKrylov_surjective A v₁ m⟩

/-- §6.6.2: `p(A) v₁ = 0` forces `p = 0` for `p` of degree below the grade. -/
theorem eq_zero_of_aeval_eq_zero {m : ℕ} (hm : m ≤ grade A v₁) {p : 𝕜[X]} (hp : p.degree < m)
    (h : aeval (op A) p v₁ = 0) : p = 0 := by
  have hinj := (polyToKrylov_bijective A v₁ hm).1
  have h0 : polyToKrylov A v₁ m ⟨p, Polynomial.mem_degreeLT.2 hp⟩ = polyToKrylov A v₁ m 0 := by
    refine Subtype.ext ?_
    rw [coe_polyToKrylov, h]
    simp
  exact congrArg Subtype.val (hinj h0)

/-- §6.6.2, second property: (6.85) is a nondegenerate form on `P_{m-1}` for `m` at most the
grade of `v₁`. -/
theorem polyInner_nondegenerate {m : ℕ} (hm : m ≤ grade A v₁) {p : 𝕜[X]} (hp : p.degree < m)
    (h : ∀ q : 𝕜[X], q.degree < m → polyInner A v₁ p q = 0) : p = 0 :=
  eq_zero_of_aeval_eq_zero A v₁ hm hp
    ((polyInner_self_eq_zero_iff A v₁ p).1 (h p hp))

private theorem exists_aeval_eq_vec (i : ℕ) :
    ∃ p : 𝕜[X], p.degree < ((i + 1 : ℕ) : ℕ) ∧ aeval (op A) p v₁ = Arnoldi.vec (op A) v₁ i := by
  refine (mem_krylov_iff_exists_aeval A v₁).1 ?_
  rw [krylov_eq]
  exact Arnoldi.vec_mem_subspace (op A) v₁ i

/-- §6.6.2, third property: the polynomial `q_i` with `v_{i+1} = q_i(A) v₁`. -/
noncomputable def lanczosPoly (i : ℕ) : 𝕜[X] := (exists_aeval_eq_vec A v₁ i).choose

theorem degree_lanczosPoly_lt (i : ℕ) : (lanczosPoly A v₁ i).degree < ((i + 1 : ℕ) : ℕ) :=
  (exists_aeval_eq_vec A v₁ i).choose_spec.1

theorem aeval_lanczosPoly_eq_vec (i : ℕ) :
    aeval (op A) (lanczosPoly A v₁ i) v₁ = Arnoldi.vec (op A) v₁ i :=
  (exists_aeval_eq_vec A v₁ i).choose_spec.2

/-- §6.6.2, third property: `v_{i+1} = q_i(A) v₁`. -/
theorem aeval_lanczosPoly (hA : (op A).IsSymmetric) (hv : ‖v₁‖ = 1) (i : ℕ) :
    aeval (op A) (lanczosPoly A v₁ i) v₁ = lanczosV A v₁ i := by
  rw [aeval_lanczosPoly_eq_vec, lanczosV_eq_vec A v₁ hA hv]

/-- §6.6.2, third property: `q_i` has degree exactly `i` below the grade of `v₁`. -/
theorem degree_lanczosPoly {i : ℕ} (hi : i < grade A v₁) :
    (lanczosPoly A v₁ i).degree = (i : ℕ) := by
  refine le_antisymm (Order.le_of_lt_succ (degree_lanczosPoly_lt A v₁ i)) (not_lt.1 fun hlt => ?_)
  have hmem : Arnoldi.vec (op A) v₁ i ∈ Krylov.subspace (op A) v₁ i := by
    rw [← krylov_eq, ← aeval_lanczosPoly_eq_vec A v₁ i]
    exact aeval_mem_krylov A v₁ hlt
  have hperp := (Submodule.mem_orthogonal _ _).1 (Arnoldi.vec_mem_orthogonal (op A) v₁ i) _ hmem
  have hzero : Arnoldi.vec (op A) v₁ i = 0 := inner_self_eq_zero.1 hperp
  have hone : ‖Arnoldi.vec (op A) v₁ i‖ = 1 :=
    Arnoldi.norm_vec_eq_one_of_lt_grade (op A) v₁ (by rwa [← grade_eq])
  rw [hzero, norm_zero] at hone
  exact zero_ne_one hone

/-- §6.6.2, third property: the Lanczos polynomials are orthogonal for (6.85). -/
theorem polyInner_lanczosPoly {i j : ℕ} (h : i ≠ j) :
    polyInner A v₁ (lanczosPoly A v₁ i) (lanczosPoly A v₁ j) = 0 := by
  rw [polyInner, aeval_lanczosPoly_eq_vec, aeval_lanczosPoly_eq_vec]
  exact Arnoldi.inner_vec_eq_zero (op A) v₁ (Ne.symm h)

end General

/-! ### The numbered results of §6.6, in the book's real setting -/

section BookResults

variable {n : ℕ}

/-- Over `ℝ` a symmetric matrix induces a symmetric operator on `ℝⁿ`. -/
theorem isSymmetric_op_of_isSymm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    (op A).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hA)

variable (A : Matrix (Fin n) (Fin n) ℝ) (v₁ : EuclideanSpace ℝ (Fin n))

/-- **Theorem 6.19**. Assume that Arnoldi's method is applied to a real symmetric matrix `A`.
Then the coefficients `h_{ij}` generated by the algorithm are such that `h_{ij} = 0` for
`1 ≤ i < j - 1` (6.82) and `h_{j,j+1} = h_{j+1,j}` (6.83); in other words, the matrix `H_m`
obtained from the Arnoldi process is tridiagonal and symmetric. -/
theorem theorem_6_19 (hA : A.IsSymm) (hv : ‖v₁‖ = 1) (m : ℕ) :
    (∀ i j : ℕ, i + 1 < j → arnoldiCoeff A v₁ i j = 0) ∧
      (∀ j : ℕ, arnoldiCoeff A v₁ j (j + 1) = arnoldiCoeff A v₁ (j + 1) j) ∧
      (H A v₁ m).IsTridiagonal ∧ (H A v₁ m).IsSymm := by
  have hA' := isSymmetric_op_of_isSymm hA
  have hH : H A v₁ m = T A v₁ m := by
    rw [← map_T_eq_H A v₁ hA' hv]
    exact (Matrix.ext fun _ => congrFun rfl).symm
  refine ⟨fun i j hij => ?_, fun j => ?_, ?_, ?_⟩
  · rw [arnoldiCoeff_eq A v₁ hv]
    exact Arnoldi.coeff_eq_zero_of_isSymmetric hA' v₁ hij
  · rw [arnoldiCoeff_eq A v₁ hv, arnoldiCoeff_eq A v₁ hv,
      Arnoldi.coeff_conj_of_isSymmetric hA' v₁ j (j + 1)]
    rfl
  · rw [hH]; exact T_isTridiagonal A v₁ hA' hv m
  · rw [hH]; exact T_isSymm A v₁ hA' hv m

/-- (6.84): the Lanczos matrix `T_m` is the Arnoldi matrix `H_m`. -/
theorem T_eq_H (hA : A.IsSymm) (hv : ‖v₁‖ = 1) (m : ℕ) : T A v₁ m = H A v₁ m := by
  rw [← map_T_eq_H A v₁ (isSymmetric_op_of_isSymm hA) hv]
  exact Matrix.ext fun _ => congrFun rfl

/-- **§6.6.1**: Algorithm 6.15 is the modified Gram–Schmidt variant of Arnoldi's method for a
symmetric matrix — it produces the same vectors `v_j`, with `α_j = h_{jj}` and
`β_{j+1} = h_{j+1,j}`. -/
theorem algorithm_6_15_eq_alg_6_2 (hA : A.IsSymm) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosV A v₁ j = arnoldiMGS A v₁ j ∧ lanczosAlpha A v₁ j = arnoldiCoeff A v₁ j j ∧
      lanczosBeta A v₁ (j + 1) = arnoldiCoeff A v₁ (j + 1) j :=
  ⟨lanczosV_eq_arnoldiMGS A v₁ (isSymmetric_op_of_isSymm hA) hv j,
    lanczosAlpha_eq_arnoldiCoeff A v₁ (isSymmetric_op_of_isSymm hA) hv j,
    lanczosBeta_succ_eq_arnoldiCoeff A v₁ (isSymmetric_op_of_isSymm hA) hv j⟩

/-! #### The real forms used by §6.7

Over `ℝ` the coefficients of Algorithm 6.15 are scalars of the space itself, so the
`RCLike.ofReal` coercions of the general statements above disappear. -/

/-- Algorithm 6.15, lines 3–7, at the first step: `A v_1 = α_1 v_1 + β_2 v_2`. -/
theorem apply_lanczosV_zero_real (hA : A.IsSymm) (hv : ‖v₁‖ = 1) :
    op A (lanczosV A v₁ 0) =
      lanczosAlpha A v₁ 0 • lanczosV A v₁ 0 + lanczosBeta A v₁ 1 • lanczosV A v₁ 1 := by
  simpa using apply_lanczosV_zero A v₁ (isSymmetric_op_of_isSymm hA) hv

/-- Algorithm 6.15, lines 3–7: `A v_{j+1} = β_{j+1} v_j + α_{j+1} v_{j+1} + β_{j+2} v_{j+2}`. -/
theorem apply_lanczosV_real (hA : A.IsSymm) (hv : ‖v₁‖ = 1) (j : ℕ) :
    op A (lanczosV A v₁ (j + 1)) = lanczosBeta A v₁ (j + 1) • lanczosV A v₁ j +
      lanczosAlpha A v₁ (j + 1) • lanczosV A v₁ (j + 1) +
      lanczosBeta A v₁ (j + 2) • lanczosV A v₁ (j + 2) := by
  simpa using apply_lanczosV A v₁ (isSymmetric_op_of_isSymm hA) hv j

/-- `α_j = (A v_j, v_j)`. -/
theorem lanczosAlpha_eq_inner_real (hA : A.IsSymm) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosAlpha A v₁ j = inner ℝ (lanczosV A v₁ j) (op A (lanczosV A v₁ j)) := by
  simpa using lanczosAlpha_eq_inner A v₁ (isSymmetric_op_of_isSymm hA) hv j

/-- `β_{j+1} = (A v_j, v_{j+1})`. -/
theorem lanczosBeta_succ_eq_inner_real (hA : A.IsSymm) (hv : ‖v₁‖ = 1) (j : ℕ) :
    lanczosBeta A v₁ (j + 1) = inner ℝ (lanczosV A v₁ (j + 1)) (op A (lanczosV A v₁ j)) := by
  simpa using lanczosBeta_succ_eq_inner A v₁ (isSymmetric_op_of_isSymm hA) hv j

/-- §6.6.2 (a): for `m` at most the grade of `v_1` the mapping `q ↦ q(A) v_1` is an isomorphism
from `P_{m-1}` onto `𝒦_m`. -/
theorem equation_6_85_isomorphism {m : ℕ} (hm : m ≤ grade A v₁) :
    Function.Bijective (polyToKrylov A v₁ m) :=
  polyToKrylov_bijective A v₁ hm

/-- §6.6.2 (b): (6.85) defines a nondegenerate bilinear form on `P_{m-1}` for `m` at most the
grade of `v_1`. -/
theorem equation_6_85_nondegenerate {m : ℕ} (hm : m ≤ grade A v₁) {p : ℝ[X]} (hp : p.degree < m)
    (h : ∀ q : ℝ[X], q.degree < m → polyInner A v₁ p q = 0) : p = 0 :=
  polyInner_nondegenerate A v₁ hm hp h

/-- §6.6.2 (c): the Lanczos vectors are `v_{i+1} = q_i(A) v_1` with `deg q_i = i`, and the `q_i`
are orthogonal for the inner product (6.85). -/
theorem equation_6_85_orthogonal_polynomials (hA : A.IsSymm) (hv : ‖v₁‖ = 1) {i : ℕ}
    (hi : i < grade A v₁) :
    (lanczosPoly A v₁ i).degree = (i : ℕ) ∧
      aeval (op A) (lanczosPoly A v₁ i) v₁ = lanczosV A v₁ i ∧
      ∀ j, i ≠ j → polyInner A v₁ (lanczosPoly A v₁ i) (lanczosPoly A v₁ j) = 0 :=
  ⟨degree_lanczosPoly A v₁ hi,
    aeval_lanczosPoly A v₁ (isSymmetric_op_of_isSymm hA) hv i,
    fun _ h => polyInner_lanczosPoly A v₁ h⟩

/-- The characteristic polynomial of `T_m` is the one the backbone attaches to the compression of
`A` to `𝒦_m`: over `ℝ` the entrywise map `algebraMap ℝ ℝ` of `Lanczos.charpoly_tridiag_map` is the
identity. -/
private theorem charpoly_T_eq (hA : A.IsSymm) (hv : ‖v₁‖ = 1) {m : ℕ} (hm : m ≤ grade A v₁) :
    (T A v₁ m).charpoly =
      LinearMap.charpoly (compression (op A) (Krylov.subspace (op A) v₁ m)) := by
  have hA' := isSymmetric_op_of_isSymm hA
  have h := Lanczos.charpoly_tridiag_map hA' v₁ (m := m) (by rwa [← grade_eq])
  rw [Algebra.algebraMap_self, Polynomial.map_id] at h
  rw [T_eq_tridiag A v₁ hA' hv, h]

/-- §6.6.2 (d), the property the book states without proof: among the monic polynomials of degree
`m`, the characteristic polynomial of the tridiagonal matrix `T_m` minimizes
`‖p‖_{v_1} = ‖p(A) v_1‖`.

This is the backbone's `Arnoldi.charpoly_compression_isMinOn` — `T_m` is the matrix of the
compression of `A` to `𝒦_m` (6.84) — and the hypothesis `m ≤ μ` is what makes that compression
have the `m` orthonormal columns the book's `V_m` has. -/
theorem equation_6_85_charpoly_isMinOn (hA : A.IsSymm) (hv : ‖v₁‖ = 1) {m : ℕ}
    (hm : m ≤ grade A v₁) :
    IsMinOn (fun p : ℝ[X] => ‖aeval (op A) p v₁‖) {p : ℝ[X] | p.Monic ∧ p.natDegree = m}
      (T A v₁ m).charpoly := by
  rw [charpoly_T_eq A v₁ hA hv hm]
  exact Arnoldi.charpoly_compression_isMinOn (op A) v₁ (by rwa [← grade_eq])

/-- §6.6.2 (e), the second property the book states without proof: the Lanczos algorithm computes
`p_{T_m}(A) v_1` up to a scalar, namely `β_2 β_3 ⋯ β_{m+1} v_{m+1}`. In particular the algorithm
breaks down at step `m` exactly when `p_{T_m}(A) v_1 = 0`. -/
theorem equation_6_85_lanczos_charpoly (hA : A.IsSymm) (hv : ‖v₁‖ = 1) {m : ℕ}
    (hm : m ≤ grade A v₁) :
    aeval (op A) (T A v₁ m).charpoly v₁ =
      (∏ j ∈ Finset.range m, lanczosBeta A v₁ (j + 1)) • lanczosV A v₁ m := by
  have hA' := isSymmetric_op_of_isSymm hA
  have h := Lanczos.aeval_charpoly_tridiag hA' v₁ (m := m) (by rwa [← grade_eq])
  rw [Algebra.algebraMap_self, Polynomial.map_id, hv, one_mul] at h
  have hprod : ∀ j ∈ Finset.range m,
      lanczosBeta A v₁ (j + 1) = Lanczos.beta (op A) v₁ j :=
    fun j _ => lanczosBeta_succ_eq A v₁ hA' hv j
  rw [T_eq_tridiag A v₁ hA' hv, h, lanczosV_eq_vec A v₁ hA' hv, Finset.prod_congr rfl hprod]
  norm_num

end BookResults

end SaadSparse.Ch06
