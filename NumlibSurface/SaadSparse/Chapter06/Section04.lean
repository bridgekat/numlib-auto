/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Arnoldi
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Iterate
import Numlib.Krylov.Subspace
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.Projection.Basic
import NumlibSurface.SaadSparse.Chapter06.Common
import NumlibSurface.SaadSparse.Chapter06.Section03

/-!
# Saad, Section 6.4: The full orthogonalization method

This module formalizes Section 6.4 of [saad2003iterative]. The full orthogonalization method (FOM)
runs $m$ steps of Arnoldi's method on $v_1 = r_0 / \beta$, where $r_0 = b - Ax_0$ and
$\beta = \|r_0\|_2$, and then sets
$$y_m = H_m^{-1} (\beta e_1), \qquad x_m = x_0 + V_m y_m$$
as in (6.16)–(6.17). Section 6.4.1 shows that $x_m$ is the orthogonal projection method onto
$\mathcal{K}_m(A, r_0)$, and that its residual is $b - Ax_m = -h_{m+1,m} (e_m^T y_m) v_{m+1}$
(Proposition 6.7), with norm $h_{m+1,m} |e_m^T y_m|$ (6.18). The restarted method FOM($m$) is
Algorithm 6.5.

Section 6.4.2 treats the incomplete orthogonalization procedure (Algorithm 6.6), which
orthogonalizes each new vector against the previous $k$ vectors only, the method IOM built on it
(Algorithm 6.7), and its direct version DIOM (Algorithm 6.8), which updates $x_m$ through the LU
factorization $H_m = L_m U_m$. These methods satisfy no global variational property, and what the
book proves about them is proved here directly. The only structural fact that they share with
Arnoldi's method is the Hessenberg relation (6.6)–(6.7), which does not use orthogonality. The
proofs specialize the backbone modules `Numlib.Krylov.Arnoldi`, `Numlib.Krylov.Hessenberg` and
`Numlib.Krylov.Iterate`.

## Main definitions

* Equations (6.16)–(6.17), `SaadSparse.Chapter06.fomFixed`: the FOM iterate with exactly $m$ Arnoldi
  steps.
* Algorithm 6.4, `SaadSparse.Chapter06.fom`: FOM, with the stopping rule of the Arnoldi process.
* Section 6.4.1, `SaadSparse.Chapter06.FOMDefined`: FOM is defined at step $m$, that is, $H_m$ is
  nonsingular.
* Algorithm 6.5, `SaadSparse.Chapter06.fomCycle` and `SaadSparse.Chapter06.fomRestarted`: one cycle
  of FOM($m$), and the restarted iterate.
* Algorithm 6.6, `SaadSparse.Chapter06.iop` and `SaadSparse.Chapter06.iopCoeff`: the incomplete
  orthogonalization procedure and its coefficients.
* Section 6.4.2, `SaadSparse.Chapter06.VI`: the matrix $V_m$ of the incomplete orthogonalization
  vectors.
* Algorithm 6.7, `SaadSparse.Chapter06.iom`: IOM.
* Section 6.4.2, `SaadSparse.Chapter06.hessLU`: the LU factorization $H_m = L_m U_m$ without
  pivoting.
* Algorithm 6.8, `SaadSparse.Chapter06.diom`: DIOM.

## Main results

* Equations (6.16)–(6.17), `SaadSparse.Chapter06.equation_6_16_17` and
  `SaadSparse.Chapter06.equation_6_16_17_unique`: the FOM iterate is the unique orthogonal
  projection approximation onto $\mathcal{K}_m(A, r_0)$.
* Section 6.4.1, `SaadSparse.Chapter06.Vt_r₀`: $V_m^T r_0 = \beta e_1$.
* Proposition 6.7, `SaadSparse.Chapter06.proposition_6_7`:
  $b - Ax_m = -h_{m+1,m} (e_m^T y_m) v_{m+1}$.
* Equation (6.18), `SaadSparse.Chapter06.equation_6_18`: $\|b - Ax_m\|_2 = h_{m+1,m} |e_m^T y_m|$.
* Section 6.4.2, `SaadSparse.Chapter06.iop_eq_6_7`: (6.7) holds for the incomplete orthogonalization
  procedure.
* Section 6.4.2, `SaadSparse.Chapter06.proposition_6_7_iom` and
  `SaadSparse.Chapter06.equation_6_18_iom`: Proposition 6.7 and (6.18) hold for IOM.
* Section 6.4.2, `SaadSparse.Chapter06.diom_residual`: the DIOM residual norm is
  $h_{m+1,m} |\zeta_m / u_{mm}|$.
* Equations (6.20)–(6.21), `SaadSparse.Chapter06.algorithm_6_8_eq_alg_6_7`: DIOM computes the IOM
  iterates.
* Proposition 6.8, `SaadSparse.Chapter06.proposition_6_8`: IOM is a projection process onto
  $\mathcal{K}_m$ orthogonally to $\operatorname{span}\{z_1, \dots, z_m\}$.
* Equation (6.22), `SaadSparse.Chapter06.equation_6_22`: the DIOM residuals are orthogonal within a
  window of $k$ steps.
* Equation (6.23), `SaadSparse.Chapter06.equation_6_23`: $(A p_j, v_i) = 0$ for $j - k + 1 < i < j$.
* Equation (6.24), `SaadSparse.Chapter06.equation_6_24`: for full orthogonalization,
  $(A p_j, p_i) = 0$ for $i < j$.
* Section 6.4.2, `SaadSparse.Chapter06.algorithm_6_6_eq_alg_6_2`: with a full band, Algorithm 6.6 is
  Algorithm 6.2.

## Implementation notes

* The data $r_0$, $\beta$, $v_1$, $e_1$ and the bridge between $v_1$ and the backbone Arnoldi data
  of $r_0$ are in `NumlibSurface.SaadSparse.Chapter06.Common` and
  `NumlibSurface.SaadSparse.Chapter06.Section03`. They are shared with
  `NumlibSurface.SaadSparse.Chapter06.Section05`.
* Indices of vectors and coefficients are $0$-based, as in
  `NumlibSurface.SaadSparse.Chapter06.Section03`: `iop A v₁ k j` is the book's $v_{j+1}$. The
  iterates $x_m$ keep the book's index.
* The coefficient `iopCoeff A v₁ k i j` is the book's $h_{i+1,j+1}$.
* Division by a vanishing norm is $0$, which gives the book's "if $h_{j+1,j} = 0$ then Stop". The
  book's "set $m := j$" is `SaadSparse.Chapter06.mEff` for FOM and `SaadSparse.Chapter06.iomSteps`
  for IOM. Lean's matrix inverse is $0$ at a singular matrix, so $y_m = 0$ when $H_m$ is singular.
* The definitions are polymorphic in the scalar field `𝕜` with `[RCLike 𝕜]`. The numbered results
  are stated over $\mathbb{R}$, the generality of Section 6.4 of the book, as specializations of
  lemmas for any `𝕜`.

## Deviations from the source

* **Proposition 6.8** (reading). The statement adds two hypotheses that the source leaves implicit:
  $\|v_{m+1}\| = 1$, and $v_1, \dots, v_m$ span $\mathcal{K}_m$. See
  `SaadSparse.Chapter06.proposition_6_8`.
-/

open scoped Matrix

namespace SaadSparse.Chapter06

section General

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-! ### (6.16)–(6.17) and Algorithm 6.4 -/

/-- The vector $y_m = H_m^{-1} (\beta e_1)$ of (6.17) of [saad2003iterative]. Lean's matrix inverse
is $0$ at a singular $H_m$, the breakdown case of the book, and then $y_m = 0$. -/
noncomputable def fomY (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : Fin m → 𝕜 :=
  (H A (v₁ A b x₀) m)⁻¹ *ᵥ ((β A b x₀ : 𝕜) • e₁ m)

/-- **Equations (6.16)–(6.17)** of [saad2003iterative], with exactly $m$ steps of Algorithm 6.1. The
FOM iterate is
$$x_m = x_0 + V_m y_m, \qquad y_m = H_m^{-1} (\beta e_1),$$
where $V_m$ and $H_m$ are computed by Algorithm 6.1 from $v_1 = r_0 / \beta$.

If $H_m$ is singular, then $y_m = 0$ and $x_m = x_0$, by Lean's convention for the matrix
inverse. -/
noncomputable def fomFixed (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : 𝔼 :=
  x₀ + Matrix.toEuclideanLin (V A (v₁ A b x₀) m) (WithLp.toLp 2 (fomY A b x₀ m))

/-- **Algorithm 6.4** of [saad2003iterative] (FOM). The iterate $x_m = x_0 + V_m y_m$ of
(6.16)–(6.17), where the number of Arnoldi steps is $\min(m, \mu)$ with $\mu$ the grade of
$v_1$. This is the book's "if $h_{j+1,j} = 0$ then set $m := j$". -/
noncomputable def fom (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : 𝔼 :=
  fomFixed A b x₀ (mEff A b x₀ m)

/-- **Section 6.4.1** of [saad2003iterative]. FOM is **defined** at step $m$ if the matrix $H_m$ is
nonsingular. -/
def FOMDefined (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (m : ℕ) : Prop :=
  IsUnit (H A (v₁ A b x₀) m)

/-- With $m = 0$ steps, the FOM iterate is $x_0$. -/
theorem fomFixed_zero : fomFixed A b x₀ 0 = x₀ := by
  rw [fomFixed, toEuclideanLin_V_apply]
  simp

/-- The FOM iterate is $x_m = x_0 + \sum_{j} (y_m)_j v_j$, where the $v_j$ are the backbone Arnoldi
vectors `Arnoldi.vec` of $r_0$. This is the form that the backbone uses. -/
theorem fomFixed_eq_add_sum (m : ℕ) :
    fomFixed A b x₀ m
      = x₀ + ∑ j, fomY A b x₀ m j • Arnoldi.vec (op A) (b - op A x₀) (j : ℕ) := by
  rw [fomFixed, toEuclideanLin_V_apply, arnoldiCGS_v₁ A b x₀]

/-- If $H_m$ is nonsingular, then $y_m$ solves (6.17): $H_m y_m = \beta e_1$. -/
theorem H_mulVec_fomY {m : ℕ} (hH : FOMDefined A b x₀ m) :
    H A (v₁ A b x₀) m *ᵥ fomY A b x₀ m = Krylov.firstVec (β A b x₀ : 𝕜) m := by
  rw [fomY, Matrix.mulVec_nonsing_inv_mulVec hH, smul_e₁_eq_firstVec]

/-- **Equations (6.16)–(6.17)** of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$. Let $H_m$
be nonsingular and let $m$ be at most the grade of $v_1$. Then the FOM iterate $x_m$ is the
Galerkin iterate on $\mathcal{K}_m(A, r_0)$, the orthogonal projection method (6.15):
$x_m - x_0 \in \mathcal{K}_m(A, r_0)$ and $b - Ax_m \perp \mathcal{K}_m(A, r_0)$. -/
theorem fomFixed_isGalerkinIterate {m : ℕ} (hH : FOMDefined A b x₀ m)
    (hm : m ≤ grade A (v₁ A b x₀)) :
    Krylov.IsGalerkinIterate (op A) b x₀ m (fomFixed A b x₀ m) := by
  rcases Nat.eq_zero_or_pos m with rfl | -
  · rw [fomFixed_zero]
    exact ⟨by simp, by
      rw [Krylov.subspace_zero, Submodule.bot_orthogonal_eq_top]; exact Submodule.mem_top⟩
  · have hgr : m ≤ Krylov.grade (op A) (b - op A x₀) := by rwa [← grade_v₁]
    have hy : Arnoldi.hessenbergSq (op A) (b - op A x₀) m *ᵥ fomY A b x₀ m
        = Krylov.firstVec (‖b - op A x₀‖ : 𝕜) m := by
      rw [← H_v₁ A b x₀]
      exact H_mulVec_fomY A b x₀ hH
    have h := (Krylov.isGalerkinIterate_iff_mulVec_eq hgr (fomY A b x₀ m)).2 hy
    rwa [← fomFixed_eq_add_sum A b x₀ m] at h

/-- If $H_m$ is nonsingular for the number $m' = \min(m, \mu)$ of Arnoldi steps that Algorithm 6.4
performs, then the FOM iterate is the Galerkin iterate on $\mathcal{K}_{m'}(A, r_0)$. -/
theorem fom_isGalerkinIterate {m : ℕ} (hH : FOMDefined A b x₀ (mEff A b x₀ m)) :
    Krylov.IsGalerkinIterate (op A) b x₀ (mEff A b x₀ m) (fom A b x₀ m) :=
  fomFixed_isGalerkinIterate A b x₀ hH (mEff_le A b x₀ m)

/-- Let $H_m$ be nonsingular and let $m$ be at most the grade of $v_1$. If $x$ is a Galerkin iterate
on $\mathcal{K}_m(A, r_0)$, then $x$ is the FOM iterate $x_m$. -/
theorem eq_fomFixed_of_isGalerkinIterate {m : ℕ} {x : 𝔼} (hH : FOMDefined A b x₀ m)
    (hm : m ≤ grade A (v₁ A b x₀)) (hx : Krylov.IsGalerkinIterate (op A) b x₀ m x) :
    x = fomFixed A b x₀ m := by
  rcases Nat.eq_zero_or_pos m with rfl | -
  · have hmem := hx.mem
    rw [Krylov.subspace_zero, Submodule.mem_bot, sub_eq_zero] at hmem
    rw [hmem, fomFixed_zero]
  · have hgr : m ≤ Krylov.grade (op A) (b - op A x₀) := by rwa [← grade_v₁]
    obtain ⟨z, -, huniq⟩ := (Krylov.existsUnique_isGalerkinIterate_iff_isUnit hgr).2
      (by rw [← H_v₁ A b x₀]; exact hH)
    rw [huniq x hx, huniq _ (fomFixed_isGalerkinIterate A b x₀ hH hm)]

/-- **Section 6.4.1** of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$. For every $m$,
$V_m^H r_0 = \beta e_1$. This is the book's $V_m^T r_0 = \beta e_1$ for real matrices. -/
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
    rw [arnoldiCGS_v₁ A b x₀, r₀_def]
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

set_option linter.unusedVariables false in
/-- **Proposition 6.7** of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$. Let $m \ge 1$,
let $H_m$ be nonsingular, and let $m$ be at most the grade of $v_1$. Then the FOM residual is
$$b - Ax_m = -h_{m+1,m} (e_m^T y_m) v_{m+1}.$$

The no-breakdown hypothesis $m \le \mu$ is kept so that `SaadSparse.Chapter06.proposition_6_7`
reads as in the book. The identity needs only that $H_m$ is nonsingular, because after the grade
of $v_1$ both sides vanish. -/
theorem residual_fomFixed {m : ℕ} (hH : FOMDefined A b x₀ m) (hm : m ≤ grade A (v₁ A b x₀))
    (hm0 : 0 < m) :
    b - op A (fomFixed A b x₀ m)
      = -(arnoldiCoeff A (v₁ A b x₀) m (m - 1) * fomY A b x₀ m ⟨m - 1, by omega⟩) •
          arnoldiCGS A (v₁ A b x₀) m := by
  have hy : Arnoldi.hessenbergSq (op A) (b - op A x₀) m *ᵥ fomY A b x₀ m
      = Krylov.firstVec (‖b - op A x₀‖ : 𝕜) m := by
    rw [← H_v₁ A b x₀]
    exact H_mulVec_fomY A b x₀ hH
  rw [fomFixed_eq_add_sum A b x₀ m, Krylov.residual_galerkin_eq hm0 _ hy,
    arnoldiCoeff_v₁ A b x₀, arnoldiCGS_v₁ A b x₀]

/-- **Equation (6.18)** of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$. Let $m \ge 1$,
let $H_m$ be nonsingular, and let $m$ be at most the grade of $v_1$. Then
$$\|b - Ax_m\|_2 = |h_{m+1,m}| \, |e_m^T y_m|.$$

Both sides vanish at $m = \mu$, where the Arnoldi process has already stopped. -/
theorem norm_residual_fomFixed {m : ℕ} (hH : FOMDefined A b x₀ m)
    (hm : m ≤ grade A (v₁ A b x₀)) (hm0 : 0 < m) :
    ‖b - op A (fomFixed A b x₀ m)‖
      = ‖arnoldiCoeff A (v₁ A b x₀) m (m - 1)‖ * ‖fomY A b x₀ m ⟨m - 1, by omega⟩‖ := by
  have hr : r₀ A b x₀ ≠ 0 := by
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

/-!
### Algorithm 6.6: the incomplete orthogonalization procedure

Algorithm 6.6 is Algorithm 6.2 with the inner loop restricted to the last $k$ vectors,
$i = \max\{1, j - k + 1\}, \dots, j$. The results below never use the orthogonality of the $v_i$.
This is the book's reason ("the orthogonality was not used") why (6.6)–(6.7), Proposition 6.7 and
(6.18) remain true after the truncation.
-/

/-- The inner loop of **Algorithm 6.6** of [saad2003iterative]. For a $0$-based sequence
$u_0, u_1, \dots$, a lower index $l$ and a vector $w^{(0)}$, the vector $w^{(N)}$ is obtained by
subtracting one at a time the projections on the $u_i$ with $l \le i < N$. -/
noncomputable def iopW (v : ℕ → 𝔼) (lo : ℕ) (w₀ : 𝔼) : ℕ → 𝔼
  | 0 => w₀
  | i + 1 =>
    let w := iopW v lo w₀ i
    if lo ≤ i then w - inner 𝕜 (v i) w • v i else w

/-- The coefficient that the inner loop of Algorithm 6.6 produces at row $i$: $(w^{(i)}, u_i)$ if
$i \ge l$, and $0$ outside the band. -/
noncomputable def iopCoeffOf (v : ℕ → 𝔼) (lo : ℕ) (w₀ : 𝔼) (i : ℕ) : 𝕜 :=
  if lo ≤ i then inner 𝕜 (v i) (iopW v lo w₀ i) else 0

/-- One step of the inner loop of Algorithm 6.6: $w^{(i+1)} = w^{(i)} - c_i u_i$, where $c_i$ is the
coefficient of row $i$. -/
theorem iopW_succ (v : ℕ → 𝔼) (lo : ℕ) (w₀ : 𝔼) (i : ℕ) :
    iopW v lo w₀ (i + 1) = iopW v lo w₀ i - iopCoeffOf v lo w₀ i • v i := by
  rw [iopW, iopCoeffOf]
  split_ifs with h
  · rfl
  · rw [zero_smul, sub_zero]

/-- The truncated loop subtracts exactly the terms $c_i u_i$ and nothing else:
$w^{(N)} = w^{(0)} - \sum_{i < N} c_i u_i$, where $c_i$ is the coefficient of row $i$. -/
theorem iopW_eq_sub_sum (v : ℕ → 𝔼) (lo : ℕ) (w₀ : 𝔼) (N : ℕ) :
    iopW v lo w₀ N = w₀ - ∑ i ∈ Finset.range N, iopCoeffOf v lo w₀ i • v i := by
  induction N with
  | zero => simp [iopW]
  | succ N ih => rw [iopW_succ, ih, Finset.sum_range_succ]; abel

/-- The truncated loop reads only the first $N$ vectors: two sequences that agree before $N$ give
the same $w^{(N)}$. -/
theorem iopW_congr {v v' : ℕ → 𝔼} (lo : ℕ) (w₀ : 𝔼) {N : ℕ} (h : ∀ i < N, v i = v' i) :
    iopW v lo w₀ N = iopW v' lo w₀ N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hN := ih fun i hi => h i (Nat.lt_succ_of_lt hi)
    rw [iopW_succ, iopW_succ, iopCoeffOf, iopCoeffOf, hN, h N N.lt_succ_self]

/-- The truncated loop orthogonalizes against the vectors in the band, as long as these vectors are
pairwise orthogonal and each has norm $1$ or is $0$. -/
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

/-- **Algorithm 6.6** of [saad2003iterative] (incomplete orthogonalization procedure). Start from
$v_1 = v$. For $j = 1, 2, \dots$, set $w := Av_j$; for $i = \max\{1, j - k + 1\}, \dots, j$, set
$h_{ij} := (w, v_i)$ and $w := w - h_{ij} v_i$; then $v_{j+1} = w / \|w\|_2$.

As in Algorithm 6.2, the clamp `min i j` in the definition does not matter. The index is
$0$-based: `iop A v k j` is $v_{j+1}$. -/
noncomputable def iop (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k : ℕ) : ℕ → 𝔼
  | 0 => v
  | j + 1 =>
    let u : ℕ → 𝔼 := fun i => iop A v k (min i j)
    let w := iopW u (j + 1 - k) (op A (u j)) (j + 1)
    ((‖w‖ : 𝕜)⁻¹) • w
  termination_by j => j
  decreasing_by exact Nat.lt_succ_of_le (Nat.min_le_right _ _)

/-- The vector $w_j$ of Algorithm 6.6: what remains of $A v_j$ after the whole truncated inner loop.
-/
noncomputable def iopVecW (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k j : ℕ) : 𝔼 :=
  iopW (iop A v k) (j + 1 - k) (op A (iop A v k j)) (j + 1)

/-- **Algorithm 6.6** of [saad2003iterative], the coefficients. For $i \le j$, $h_{ij}$ is the inner
product of the band, which is $0$ for $i < j - k + 1$; $h_{j+1,j} = \|w_j\|_2$; and $h_{ij} = 0$
for $i > j + 1$.

The indices are $0$-based: `iopCoeff A v k i j` is $h_{i+1,j+1}$. -/
noncomputable def iopCoeff (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k i j : ℕ) : 𝕜 :=
  if i ≤ j then iopCoeffOf (iop A v k) (j + 1 - k) (op A (iop A v k j)) i
  else if i = j + 1 then (‖iopVecW A v k j‖ : 𝕜) else 0

/-- The first vector of Algorithm 6.6 is the starting vector $v_1$. -/
@[simp]
theorem iop_zero : iop A v k 0 = v := by rw [iop]

/-- For $i \le j$, the coefficient $h_{ij}$ of Algorithm 6.6 is the coefficient of row $i$ of the
truncated inner loop for $A v_j$. -/
theorem iopCoeff_of_le {i j : ℕ} (h : i ≤ j) :
    iopCoeff A v k i j = iopCoeffOf (iop A v k) (j + 1 - k) (op A (iop A v k j)) i := by
  rw [iopCoeff, ite_eq_left_of_eq_true _ _ (eq_true h)]

/-- **Algorithm 6.6** of [saad2003iterative], line 5. For every $j$, $h_{j+1,j} = \|w_j\|_2$. -/
theorem iopCoeff_succ_self (j : ℕ) : iopCoeff A v k (j + 1) j = (‖iopVecW A v k j‖ : 𝕜) := by
  rw [iopCoeff]
  split_ifs with h1 h2
  · omega
  · rfl
  · exact absurd rfl h2

/-- **Hessenberg structure.** The coefficients of Algorithm 6.6 satisfy $h_{ij} = 0$ for
$i > j + 1$. -/
theorem iopCoeff_eq_zero_of_lt {i j : ℕ} (h : j + 1 < i) : iopCoeff A v k i j = 0 := by
  rw [iopCoeff]
  split_ifs with h1 h2
  · omega
  · omega
  · rfl

/-- **Band structure.** The coefficients of Algorithm 6.6 satisfy $h_{ij} = 0$ for $i \le j - k$. So
$H_m$ has $k$ nonzero diagonals on and above the main diagonal. -/
theorem iopCoeff_eq_zero_of_add_le {i j : ℕ} (h : i + k ≤ j) : iopCoeff A v k i j = 0 := by
  rw [iopCoeff_of_le A v k (by omega), iopCoeffOf]
  split_ifs with h1
  · omega
  · rfl

/-- **Algorithm 6.6** of [saad2003iterative], line 7. Each next vector is
$v_{j+1} = w_j / h_{j+1,j}$, which is $0$ when $w_j = 0$. -/
theorem iop_succ (j : ℕ) :
    iop A v k (j + 1) = ((‖iopVecW A v k j‖ : 𝕜)⁻¹) • iopVecW A v k j := by
  rw [iop, iopVecW]
  simp only [Nat.min_self]
  rw [iopW_congr (v := fun i => iop A v k (min i j)) (v' := iop A v k) (j + 1 - k)
    (op A (iop A v k j)) fun i hi => by rw [Nat.min_eq_left (Nat.lt_succ_iff.1 hi)]]

/-- For every $j$, $w_j = h_{j+1,j} v_{j+1}$. -/
theorem iopVecW_eq_smul (j : ℕ) :
    iopVecW A v k j = iopCoeff A v k (j + 1) j • iop A v k (j + 1) := by
  rw [iopCoeff_succ_self, iop_succ, smul_smul]
  rcases eq_or_ne (iopVecW A v k j) 0 with h | h
  · rw [h, smul_zero]
  · rw [mul_inv_cancel₀ (by simpa using norm_ne_zero_iff.2 h), one_smul]

/-- **Breakdown.** The next vector $v_{j+1}$ of Algorithm 6.6 is $0$ if and only if $h_{j+1,j} = 0$.
-/
theorem iop_succ_eq_zero_iff (j : ℕ) :
    iop A v k (j + 1) = 0 ↔ iopCoeff A v k (j + 1) j = 0 := by
  rw [iopCoeff_succ_self, RCLike.ofReal_eq_zero, norm_eq_zero]
  constructor
  · intro h
    rw [iopVecW_eq_smul, h, smul_zero]
  · intro h
    rw [iop_succ, h, norm_zero, RCLike.ofReal_zero, inv_zero, zero_smul]

/-- If $\|v_1\| = 1$, then every vector of Algorithm 6.6 has norm $1$ or is $0$, the latter after a
breakdown. -/
theorem norm_iop (hv : ‖v‖ = 1) (j : ℕ) : ‖iop A v k j‖ = 1 ∨ iop A v k j = 0 := by
  cases j with
  | zero => rw [iop_zero]; exact Or.inl hv
  | succ j =>
    rcases eq_or_ne (iopVecW A v k j) 0 with h | h
    · exact Or.inr (by rw [iop_succ, h, smul_zero])
    · refine Or.inl ?_
      rw [iop_succ, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

/-- The **bridge to the backbone**. The vectors and coefficients of Algorithm 6.6 satisfy the
Hessenberg relation `Krylov.HessenbergRelation`: $A v_j = \sum_{i=1}^{j+1} h_{ij} v_i$ for every
$j$, and $h_{ij} = 0$ for $i > j + 1$. So (6.6)–(6.7) hold for incomplete orthogonalization.

No hypothesis is needed, and no orthogonality is used. -/
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

/-- **Section 6.4.2** of [saad2003iterative], local orthogonality. If $\|v_1\| = 1$, then each
vector of Algorithm 6.6 is orthogonal to the $k$ vectors before it: $(v_j, v_i) = 0$ for
$i < j \le i + k$. -/
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

/-- **Section 6.4.2** of [saad2003iterative]. The $n \times m$ matrix $V_m = [v_1, \dots, v_m]$
whose columns are the vectors of Algorithm 6.6. -/
noncomputable def VI (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k m : ℕ) :
    Matrix (Fin n) (Fin m) 𝕜 :=
  colMatrix (iop A v k) m

/-- The $(m+1) \times m$ Hessenberg matrix $\bar H_m$ of the coefficients of Algorithm 6.6. -/
noncomputable def HbarI (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k m : ℕ) :
    Matrix (Fin (m + 1)) (Fin m) 𝕜 :=
  Krylov.hessenbergOf (iopCoeff A v k) m

/-- The $m \times m$ Hessenberg matrix $H_m$ of the coefficients of Algorithm 6.6. -/
noncomputable def HI (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k m : ℕ) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  Krylov.hessenbergSqOf (iopCoeff A v k) m

/-- The $(i, j)$ entry of the matrix $H_m$ of Algorithm 6.6 is $h_{ij}$. -/
@[simp]
theorem HI_apply {m : ℕ} (i j : Fin m) : HI A v k m i j = iopCoeff A v k i j := rfl

/-- **Equation (6.7)** of [saad2003iterative] for incomplete orthogonalization, over $\mathbb{R}$ or
$\mathbb{C}$. For every $m$, $A V_m = V_{m+1} \bar H_m$. -/
theorem mul_VI_eq (m : ℕ) : A * VI A v k m = VI A v k (m + 1) * HbarI A v k m :=
  mul_colMatrix_eq A (iop_hessenbergRelation A v k) m

/-- The number of steps of Algorithm 6.6 that Algorithm 6.7 uses when it is asked for $m$ steps: the
least $j$ such that `iopCoeff A v k (j + 1) j` vanishes, or $m$ if no $j$ has this property.

In the book's indices, a breakdown $h_{j+1,j} = 0$ at step $j$, with no earlier breakdown, gives
$j - 1$ steps. The book's instruction "set $m := j$" asks for $j$ steps, and
`SaadSparse.Chapter06.mEff` for FOM gives $j$. The definition agrees with the book when there is
no breakdown (`SaadSparse.Chapter06.iomSteps_eq`). -/
noncomputable def iomSteps (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k m : ℕ) : ℕ :=
  sInf ({j | iopCoeff A v k (j + 1) j = 0} ∪ {m})

/-- The number of steps that Algorithm 6.7 uses is at most $m$. -/
theorem iomSteps_le (m : ℕ) : iomSteps A v k m ≤ m :=
  Nat.sInf_le (Set.mem_union_right _ rfl)

/-- If $h_{j+1,j} \neq 0$ for every step $j \le m$, then Algorithm 6.7 uses all $m$ steps.

In $0$-based indices the hypothesis is `iopCoeff A v k (j + 1) j ≠ 0` for $j < m$, which
includes the coefficient $h_{m+1,m}$ of the last step. -/
theorem iomSteps_eq {m : ℕ} (hnb : ∀ j < m, iopCoeff A v k (j + 1) j ≠ 0) :
    iomSteps A v k m = m := by
  refine le_antisymm (iomSteps_le A v k m) (le_csInf ⟨m, Set.mem_union_right _ rfl⟩ ?_)
  rintro c (hc | hc)
  · by_contra h
    exact hnb c (by omega) hc
  · exact le_of_eq (Set.mem_singleton_iff.1 hc).symm

/-- The vector $y_m = H_m^{-1} (\beta e_1)$ for the incomplete process, with $H_m$ the Hessenberg
matrix of Algorithm 6.6 started at $v_1 = r_0 / \beta$. It is $0$ when $H_m$ is singular. -/
noncomputable def iomY (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (k m : ℕ) : Fin m → 𝕜 :=
  (HI A (v₁ A b x₀) k m)⁻¹ *ᵥ ((β A b x₀ : 𝕜) • e₁ m)

/-- The iterate of Algorithm 6.7 with exactly $m$ steps of Algorithm 6.6: $x_m = x_0 + V_m y_m$,
with $V_m$ and $y_m$ from Algorithm 6.6 started at $v_1 = r_0 / \beta$. -/
noncomputable def iomFixed (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (k m : ℕ) : 𝔼 :=
  x₀ + Matrix.toEuclideanLin (VI A (v₁ A b x₀) k m) (WithLp.toLp 2 (iomY A b x₀ k m))

/-- **Algorithm 6.7** of [saad2003iterative] (IOM). Algorithm 6.4 with Algorithm 6.6 in place of the
Arnoldi process: $x_m = x_0 + V_m y_m$ with $y_m = H_m^{-1} (\beta e_1)$.

The number of steps is `SaadSparse.Chapter06.iomSteps`, which is $m$ when no breakdown occurs. -/
noncomputable def iom (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (k m : ℕ) : 𝔼 :=
  iomFixed A b x₀ k (iomSteps A (v₁ A b x₀) k m)

/-- If $h_{j+1,j} \neq 0$ for every step $j \le m$ of Algorithm 6.6 started at $v_1$, then the IOM
iterate is the iterate with exactly $m$ steps. -/
theorem iom_eq_iomFixed {m : ℕ} (hnb : ∀ j < m, iopCoeff A (v₁ A b x₀) k (j + 1) j ≠ 0) :
    iom A b x₀ k m = iomFixed A b x₀ k m := by
  rw [iom, iomSteps_eq A (v₁ A b x₀) k hnb]

/-- The IOM iterate with $m$ steps is $x_m = x_0 + \sum_{j=1}^{m} (y_m)_j v_j$, with the vectors
$v_j$ of Algorithm 6.6. -/
theorem iomFixed_eq_add_sum (m : ℕ) :
    iomFixed A b x₀ k m = x₀ + ∑ j, iomY A b x₀ k m j • iop A (v₁ A b x₀) k (j : ℕ) := by
  rw [iomFixed, VI, toEuclideanLin_colMatrix_apply]

/-- For every $b$ and $x_0$, $\beta v_1 = r_0$. This holds also when $x_0$ already solves the
system, where both sides vanish. -/
theorem smul_iop_zero : (β A b x₀ : 𝕜) • iop A (v₁ A b x₀) k 0 = b - op A x₀ := by
  rw [iop_zero, v₁_def, smul_smul, β_def]
  rcases eq_or_ne (b - op A x₀) 0 with h | h
  · rw [h, smul_zero]
  · rw [mul_inv_cancel₀ (by simpa using norm_ne_zero_iff.2 h), one_smul]

/-- If the matrix $H_m$ of Algorithm 6.6 is nonsingular, then $H_m y_m = \beta e_1$. -/
theorem HI_mulVec_iomY {m : ℕ} (hH : IsUnit (HI A (v₁ A b x₀) k m)) :
    HI A (v₁ A b x₀) k m *ᵥ iomY A b x₀ k m = Krylov.firstVec (β A b x₀ : 𝕜) m := by
  rw [iomY, Matrix.mulVec_nonsing_inv_mulVec hH, smul_e₁_eq_firstVec]

/-- **Section 6.4.2** of [saad2003iterative], Proposition 6.7 for IOM ("the result of Proposition
6.7 is still valid"), over $\mathbb{R}$ or $\mathbb{C}$. Let $m \ge 1$ and let the matrix $H_m$
of Algorithm 6.6 be nonsingular. Then the IOM residual is
$$b - Ax_m = -h_{m+1,m} (e_m^T y_m) v_{m+1}.$$
-/
theorem residual_iomFixed {m : ℕ} (hH : IsUnit (HI A (v₁ A b x₀) k m)) (hm0 : 0 < m) :
    b - op A (iomFixed A b x₀ k m)
      = -(iopCoeff A (v₁ A b x₀) k m (m - 1) * iomY A b x₀ k m ⟨m - 1, by omega⟩) •
          iop A (v₁ A b x₀) k m := by
  rw [iomFixed_eq_add_sum]
  exact (iop_hessenbergRelation A (v₁ A b x₀) k).residual_eq_of_mulVec_eq
    (smul_iop_zero A b x₀ k).symm hm0 _ (HI_mulVec_iomY A b x₀ k hH)

/-- **Section 6.4.2** of [saad2003iterative], (6.18) for IOM, over $\mathbb{R}$ or $\mathbb{C}$. Let
$m \ge 1$, let the matrix $H_m$ of Algorithm 6.6 be nonsingular, and let $\|v_1\| = 1$. Then
$$\|b - Ax_m\|_2 = |h_{m+1,m}| \, |e_m^T y_m|.$$

Both sides vanish at a breakdown. -/
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

/-- **Proposition 6.8** of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$. Let $m \ge 1$,
let the matrix $H_m$ of Algorithm 6.6 be nonsingular, let $\|v_{m+1}\| = 1$, and let
$v_1, \dots, v_m$ span $\mathcal{K}_m(A, r_0)$. Then the IOM iterate $x_m$ is a projection
approximation onto $\mathcal{K}_m(A, r_0)$ orthogonally to
$$L_m = \operatorname{span}\{z_1, \dots, z_m\}, \qquad z_i = v_i - (v_i, v_{m+1}) v_{m+1}.$$

**Reading.** The source leaves two hypotheses implicit. The hypothesis $\|v_{m+1}\| = 1$ is what
makes $v_{m+1}$ orthogonal to every $z_i$, the book's "by construction". The hypothesis on the
span makes the search space $\mathcal{K}_m$ and not only the span of the $v_i$. Both hold as
long as Algorithm 6.6 has not broken down, but neither follows from the nonsingularity of $H_m$
alone.

The approximation is `IsPetrovGalerkin`: $x_m - x_0 \in \mathcal{K}_m(A, r_0)$ and
$b - Ax_m \perp L_m$. -/
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

/-!
### The Hessenberg LU factorization of Section 6.4.2

The factorization $H_m = L_m U_m$ is computed without pivoting. The factor $L_m$ is unit lower
bidiagonal, and $U_m$ is upper triangular, with $k$ nonzero diagonals when $H_m$ has them.
-/

/-- The upper factor of the LU factorization of a Hessenberg coefficient function $h$, $0$-based:
$u_{0j} = h_{0j}$ and $u_{i+1,j} = h_{i+1,j} - l_i u_{ij}$, with $l_i = h_{i+1,i} / u_{ii}$. A
zero pivot $u_{ii}$ gives $l_i = 0$. -/
noncomputable def dioU (h : ℕ → ℕ → 𝕜) : ℕ → ℕ → 𝕜
  | 0, j => h 0 j
  | i + 1, j => h (i + 1) j - h (i + 1) i / dioU h i i * dioU h i j

/-- The subdiagonal entry $l_i = h_{i+1,i} / u_{ii}$ of the unit lower bidiagonal factor, $0$-based.
It is $0$ when $u_{ii} = 0$. -/
noncomputable def dioL (h : ℕ → ℕ → 𝕜) (i : ℕ) : 𝕜 := h (i + 1) i / dioU h i i

/-- The upper factor satisfies $u_{i+1,j} = h_{i+1,j} - l_i u_{ij}$. -/
theorem dioU_succ (h : ℕ → ℕ → 𝕜) (i j : ℕ) :
    dioU h (i + 1) j = h (i + 1) j - dioL h i * dioU h i j := rfl

/-- The upper factor inherits the band of $h$: if $h_{ac} = 0$ whenever $a + k \le c$, then
$u_{ij} = 0$ whenever $i + k \le j$. -/
theorem dioU_eq_zero_of_add_le {h : ℕ → ℕ → 𝕜} {k : ℕ}
    (hband : ∀ a c, a + k ≤ c → h a c = 0) :
    ∀ i j : ℕ, i + k ≤ j → dioU h i j = 0 := by
  intro i
  induction i with
  | zero => intro j hj; exact hband 0 j hj
  | succ i ih => intro j hj; rw [dioU_succ, ih j (by omega), hband (i + 1) j hj, mul_zero, sub_zero]

/-- Let $h$ be upper Hessenberg, $h_{ac} = 0$ for $a > c + 1$. If the pivot $u_{jj}$ is not $0$,
then $u_{ij} = 0$ for all $i > j$. -/
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

/-- The unit lower bidiagonal $m \times m$ matrix $L_m$, with $1$ on the diagonal and $l_j$ at the
position $(j + 1, j)$. -/
noncomputable def hessL (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 1 else if (i : ℕ) = (j : ℕ) + 1 then dioL h j
    else 0

/-- The upper triangular $m \times m$ matrix $U_m$, with the entries $u_{ij}$ for $i \le j$ and $0$
below the diagonal. -/
noncomputable def hessU (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => if (i : ℕ) ≤ (j : ℕ) then dioU h i j else 0

/-- **Section 6.4.2** of [saad2003iterative]. The LU factorization without pivoting (Doolittle) of
the Hessenberg matrix of a coefficient function $h$: the pair of matrices $(L_m, U_m)$.

The factorization is correct when $h$ is upper Hessenberg and no pivot $u_{ll}$ with $l < m$
vanishes (`SaadSparse.Chapter06.hessL_mul_hessU`). -/
noncomputable def hessLU (h : ℕ → ℕ → 𝕜) (m : ℕ) :
    Matrix (Fin m) (Fin m) 𝕜 × Matrix (Fin m) (Fin m) 𝕜 :=
  (hessL h m, hessU h m)

/-- The $(i, j)$ entry of $L_m$ is $1$ for $i = j$, $l_j$ for $i = j + 1$, and $0$ otherwise. -/
theorem hessL_apply (h : ℕ → ℕ → 𝕜) {m : ℕ} (i j : Fin m) :
    hessL h m i j =
      if (i : ℕ) = (j : ℕ) then 1 else if (i : ℕ) = (j : ℕ) + 1 then dioL h j else 0 := rfl

/-- The $(i, j)$ entry of $U_m$ is $u_{ij}$ for $i \le j$, and $0$ otherwise. -/
theorem hessU_apply (h : ℕ → ℕ → 𝕜) {m : ℕ} (i j : Fin m) :
    hessU h m i j = if (i : ℕ) ≤ (j : ℕ) then dioU h i j else 0 := rfl

/-- The diagonal entries of $L_m$ are $1$. -/
theorem hessL_self (h : ℕ → ℕ → 𝕜) {m : ℕ} (i : Fin m) : hessL h m i i = 1 := by
  rw [hessL_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)]

/-- The entries of $L_m$ off the diagonal and the subdiagonal are $0$. -/
theorem hessL_eq_zero (h : ℕ → ℕ → 𝕜) {m : ℕ} {i j : Fin m} (h1 : (i : ℕ) ≠ (j : ℕ))
    (h2 : (i : ℕ) ≠ (j : ℕ) + 1) : hessL h m i j = 0 := by
  rw [hessL_apply, ite_eq_right_of_eq_false _ _ (eq_false h1),
    ite_eq_right_of_eq_false _ _ (eq_false h2)]

/-- The subdiagonal entry $(j + 1, j)$ of $L_m$ is $l_j$. -/
theorem hessL_sub (h : ℕ → ℕ → 𝕜) {m : ℕ} {i j : Fin m} (hij : (i : ℕ) = (j : ℕ) + 1) :
    hessL h m i j = dioL h j := by
  rw [hessL_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega : (i : ℕ) ≠ (j : ℕ))),
    ite_eq_left_of_eq_true _ _ (eq_true hij)]

/-- For $i \le j$, the $(i, j)$ entry of $U_m$ is $u_{ij}$. -/
theorem hessU_of_le (h : ℕ → ℕ → 𝕜) {m : ℕ} {i j : Fin m} (hij : (i : ℕ) ≤ (j : ℕ)) :
    hessU h m i j = dioU h i j := by
  rw [hessU_apply, ite_eq_left_of_eq_true _ _ (eq_true hij)]

/-- For $i > j$, the $(i, j)$ entry of $U_m$ is $0$. -/
theorem hessU_eq_zero (h : ℕ → ℕ → 𝕜) {m : ℕ} {i j : Fin m} (hij : (j : ℕ) < (i : ℕ)) :
    hessU h m i j = 0 := by
  rw [hessU_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- If $h_{ac} = 0$ whenever $a + k \le c$, then the $(i, j)$ entry of $U_m$ is $0$ whenever
$i + k \le j$: $U_m$ has $k$ nonzero diagonals when $H_m$ has them. -/
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

/-- **Section 6.4.2** of [saad2003iterative], the LU factorization. Let $h$ be upper Hessenberg,
$h_{ac} = 0$ for $a > c + 1$, and let the pivots $u_{ll}$ with $l < m$ be nonzero. Then
$L_m U_m = H_m$, where $L_m$ is unit lower bidiagonal and $U_m$ is upper triangular. -/
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

/-- The matrix $L_m$ is lower triangular. -/
theorem hessL_isLowerTriangular (h : ℕ → ℕ → 𝕜) (m : ℕ) : (hessL h m).IsLowerTriangular := by
  intro i j hij
  have hlt : i < j := hij
  rw [Fin.lt_def] at hlt
  exact hessL_eq_zero h (by omega) (by omega)

/-- The matrix $U_m$ is upper triangular. -/
theorem hessU_isUpperTriangular (h : ℕ → ℕ → 𝕜) (m : ℕ) : (hessU h m).IsUpperTriangular := by
  intro i j hij
  have hlt : j < i := hij
  rw [Fin.lt_def] at hlt
  exact hessU_eq_zero h hlt

/-- The determinant of $L_m$ is $1$. -/
theorem det_hessL (h : ℕ → ℕ → 𝕜) (m : ℕ) : (hessL h m).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (hessL_isLowerTriangular h m)]
  simp [hessL_self]

/-- The determinant of $U_m$ is the product of the pivots: $\det U_m = \prod_{i < m} u_{ii}$. -/
theorem det_hessU (h : ℕ → ℕ → 𝕜) (m : ℕ) : (hessU h m).det = ∏ i : Fin m, dioU h i i := by
  rw [Matrix.det_of_isUpperTriangular (hessU_isUpperTriangular h m)]
  exact Finset.prod_congr rfl fun i _ => hessU_of_le h le_rfl

/-- If the pivots $u_{ll}$ with $l < m$ are nonzero, then $U_m$ is nonsingular. -/
theorem isUnit_hessU (h : ℕ → ℕ → 𝕜) {m : ℕ} (hpiv : ∀ l, l < m → dioU h l l ≠ 0) :
    IsUnit (hessU h m) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_hessU]
  exact Finset.prod_ne_zero_iff.2 fun i _ => hpiv i i.isLt

/-- Let $h$ be upper Hessenberg, and let the pivots $u_{ll}$ with $l < m$ be nonzero. Then the
$m \times m$ Hessenberg matrix of $h$ is nonsingular. -/
theorem isUnit_hessenbergSqOf (h : ℕ → ℕ → 𝕜) (hh : ∀ a c, c + 1 < a → h a c = 0) {m : ℕ}
    (hpiv : ∀ l, l < m → dioU h l l ≠ 0) : IsUnit (Krylov.hessenbergSqOf h m) := by
  rw [← hessL_mul_hessU h hh hpiv]
  refine IsUnit.mul ?_ (isUnit_hessU h hpiv)
  rw [Matrix.isUnit_iff_isUnit_det, det_hessL]
  exact isUnit_one

/-! ### Algorithm 6.8: DIOM -/

/-- **Algorithm 6.8** of [saad2003iterative], line 3. The scalars $\zeta_1 = \beta$ and
$\zeta_m = -l_{m,m-1} \zeta_{m-1}$, the entries of the solution $z_m$ of $L_m z_m = \beta e_1$.

The index is $0$-based: the starting value $c$ is `diomZeta h c 0`, and `diomZeta h c (j + 1)`
is $-l_j$ times `diomZeta h c j`. -/
noncomputable def diomZeta (h : ℕ → ℕ → 𝕜) (c : 𝕜) : ℕ → 𝕜
  | 0 => c
  | j + 1 => -dioL h j * diomZeta h c j

/-- The scalars of Algorithm 6.8 satisfy $\zeta_{j+1} = -l_j \zeta_j$. -/
theorem diomZeta_succ (h : ℕ → ℕ → 𝕜) (c : 𝕜) (j : ℕ) :
    diomZeta h c (j + 1) = -dioL h j * diomZeta h c j := rfl

/-- If $c \neq 0$ and $l_i \neq 0$ for all $i < j$, then $\zeta_j \neq 0$ ($0$-based). -/
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

/-- The vector $z_m = (\zeta_1, \dots, \zeta_m)$ solves $L_m z_m = c \, e_1$. No hypothesis is
needed. -/
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

/-- **Algorithm 6.8** of [saad2003iterative], line 4. The direction vectors
$$p_m = u_{mm}^{-1} \Big(v_m - \sum_{i = m-k+1}^{m-1} u_{im} p_i\Big),$$
with the vectors $v_i$ of Algorithm 6.6 and the upper factor $U_m$ of their Hessenberg matrix.

The index is $0$-based: `diomP A v k j` is $p_{j+1}$, and the lower limit of the sum is
truncated at the first vector. The vector is $0$ when the pivot $u_{mm}$ vanishes. -/
noncomputable def diomP (A : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (k : ℕ) : ℕ → 𝔼
  | j =>
    (dioU (iopCoeff A v k) j j)⁻¹ •
      (iop A v k j - ∑ i : Fin j, if j + 1 - k ≤ (i : ℕ) then
        dioU (iopCoeff A v k) (i : ℕ) j • diomP A v k (i : ℕ) else 0)
  termination_by j => j
  decreasing_by exact i.isLt

/-- The direction vectors of Algorithm 6.8 satisfy their defining recurrence, with the sum over the
$0$-based indices $i$ with $j + 1 - k \le i < j$. -/
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

/-- If the pivots $u_{ll}$ with $l < m$ are nonzero, then $\sum_{i=1}^{m} u_{ij} p_i = v_j$ for each
$j \le m$: the matrix form $P_m U_m = V_m$. This is line 4 of Algorithm 6.8 read backwards, and
it gives $P_m = V_m U_m^{-1}$ of (6.20). -/
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

/-- Every direction vector $p_i$ lies in the span of $v_1, \dots, v_i$, because $U_m$ is upper
triangular. -/
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

/-- **Algorithm 6.8** of [saad2003iterative] (DIOM). Start from $x_0$ and set
$$x_m = x_{m-1} + \zeta_m p_m,$$
as in (6.21), with the scalars $\zeta_m$ and the direction vectors $p_m$ of Algorithm 6.8 for
Algorithm 6.6 started at $v_1 = r_0 / \beta$.

The iterate keeps the book's index: `diom A b x₀ k m` is $x_m$. -/
noncomputable def diom (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (k : ℕ) : ℕ → 𝔼
  | 0 => x₀
  | m + 1 => diom A b x₀ k m
      + diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) m • diomP A (v₁ A b x₀) k m

/-- The DIOM iterates satisfy $x_{m+1} = x_m + \zeta_{m+1} p_{m+1}$. -/
theorem diom_succ (m : ℕ) :
    diom A b x₀ k (m + 1) = diom A b x₀ k m
      + diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) m • diomP A (v₁ A b x₀) k m := rfl

/-- The DIOM iterate is $x_m = x_0 + \sum_{j=1}^{m} \zeta_j p_j$. -/
theorem diom_eq_add_sum (m : ℕ) :
    diom A b x₀ k m = x₀ + ∑ j ∈ Finset.range m,
      diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) j • diomP A (v₁ A b x₀) k j := by
  induction m with
  | zero => simp [diom]
  | succ m ih => rw [diom_succ, ih, Finset.sum_range_succ, add_assoc]

/-- The vector $y_m = U_m^{-1} z_m$. Algorithm 6.8 does not compute it, but the derivation of (6.20)
in [saad2003iterative] passes through it. -/
noncomputable def diomY (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : 𝔼) (k m : ℕ) : Fin m → 𝕜 :=
  (hessU (iopCoeff A (v₁ A b x₀) k) m)⁻¹ *ᵥ
    fun j : Fin m => diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) (j : ℕ)

/-- If the pivots $u_{ll}$ with $l < m$ are nonzero, then $U_m y_m = z_m$. -/
theorem hessU_mulVec_diomY {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    hessU (iopCoeff A (v₁ A b x₀) k) m *ᵥ diomY A b x₀ k m
      = fun j : Fin m => diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) (j : ℕ) := by
  rw [diomY, Matrix.mulVec_nonsing_inv_mulVec (isUnit_hessU _ hpiv)]

/-- If the pivots $u_{ll}$ with $l < m$ are nonzero, then the matrix $H_m$ of Algorithm 6.6 is
nonsingular. -/
theorem isUnit_HI_of_pivots {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A v k) l l ≠ 0) : IsUnit (HI A v k m) :=
  isUnit_hessenbergSqOf _ (fun _ _ hac => iopCoeff_eq_zero_of_lt A v k hac) hpiv

/-- If the pivots $u_{ll}$ with $l < m$ are nonzero, then $y_m = U_m^{-1} z_m$ solves
$H_m y_m = \beta e_1$. -/
theorem HI_mulVec_diomY {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    HI A (v₁ A b x₀) k m *ᵥ diomY A b x₀ k m = Krylov.firstVec (β A b x₀ : 𝕜) m := by
  rw [HI, ← hessL_mul_hessU _ (fun _ _ hac => iopCoeff_eq_zero_of_lt A (v₁ A b x₀) k hac) hpiv,
    ← Matrix.mulVec_mulVec, hessU_mulVec_diomY A b x₀ k hpiv, hessL_mulVec_diomZeta]

/-- If the pivots $u_{ll}$ with $l < m$ are nonzero, then $U_m^{-1} z_m$ is the vector
$y_m = H_m^{-1} (\beta e_1)$ of IOM. -/
theorem diomY_eq_iomY {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    diomY A b x₀ k m = iomY A b x₀ k m := by
  rw [iomY, smul_e₁_eq_firstVec, ← HI_mulVec_diomY A b x₀ k hpiv,
    Matrix.nonsing_inv_mulVec_mulVec (isUnit_HI_of_pivots A (v₁ A b x₀) k hpiv)]

/-- **Equations (6.20)–(6.21)** of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$. If the
pivots $u_{ll}$ with $l < m$ are nonzero, then Algorithm 6.8 computes the IOM iterate:
$x_0 + P_m z_m = x_0 + V_m y_m$. -/
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

/-- If $m \ge 1$ and the pivots $u_{ll}$ with $l < m$ are nonzero, then the last entry of
$y_m = U_m^{-1} z_m$ is $\zeta_m / u_{mm}$, by back substitution. -/
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

/-- **Section 6.4.2** of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$. Let $m \ge 1$, let
$\|v_1\| = 1$, and let the pivots $u_{ll}$ with $l < m$ be nonzero. Then the DIOM residual norm
is
$$\|b - Ax_m\|_2 = |h_{m+1,m}| \, |\zeta_m / u_{mm}|.$$
-/
theorem norm_residual_diom {m : ℕ} (hm0 : 0 < m) (hv : ‖v₁ A b x₀‖ = 1)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    ‖b - op A (diom A b x₀ k m)‖
      = ‖iopCoeff A (v₁ A b x₀) k m (m - 1)‖ *
        ‖diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) (m - 1)
          / dioU (iopCoeff A (v₁ A b x₀) k) (m - 1) (m - 1)‖ := by
  rw [diom_eq_iomFixed A b x₀ k hpiv,
    norm_residual_iomFixed A b x₀ k (isUnit_HI_of_pivots A (v₁ A b x₀) k hpiv) hm0 hv,
    ← diomY_eq_iomY A b x₀ k hpiv, diomY_last A b x₀ k hm0 hpiv]

/-! ### Equations (6.22)–(6.24), Exercise P-6.22 -/

/-- If the pivots $u_{ll}$ with $l < m$ are nonzero, then the DIOM residual $b - Ax_m$ is a multiple
of the vector $v_{m+1}$ of Algorithm 6.6. -/
theorem residual_diom_eq_smul {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    ∃ c : 𝕜, b - op A (diom A b x₀ k m) = c • iop A (v₁ A b x₀) k m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exact ⟨(β A b x₀ : 𝕜), by rw [diom]; exact (smul_iop_zero A b x₀ k).symm⟩
  · refine ⟨-(iopCoeff A (v₁ A b x₀) k m (m - 1) * iomY A b x₀ k m ⟨m - 1, by omega⟩), ?_⟩
    rw [diom_eq_iomFixed A b x₀ k hpiv]
    exact residual_iomFixed A b x₀ k (isUnit_HI_of_pivots A (v₁ A b x₀) k hpiv) hm0

/-- **Equation (6.22)** of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$. Let $\|v_1\| = 1$
and let the pivots $u_{ll}$ with $l < m$ be nonzero. Then the DIOM residuals $r_i = b - Ax_i$
satisfy $(r_j, r_i) = 0$ for all $i, j \le m$ with $i \neq j$ and $|i - j| \le k$. -/
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

/-- For every $m$, $\zeta_{m+1} A p_{m+1} = r_m - r_{m+1}$, where $r_i = b - Ax_i$ are the DIOM
residuals. This is the residual form of (6.21). -/
theorem smul_apply_diomP (m : ℕ) :
    diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : 𝕜) m • op A (diomP A (v₁ A b x₀) k m)
      = (b - op A (diom A b x₀ k m)) - (b - op A (diom A b x₀ k (m + 1))) := by
  rw [diom_succ, map_add, map_smul]
  abel

/-- **Equation (6.23)** of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$. Let
$\|v_1\| = 1$, let the pivots $u_{ll}$ with $l < m$ be nonzero, let $j \le m$, and let
$\zeta_j \neq 0$. Then $(A p_j, v_i) = 0$ for $j - k + 1 < i < j$.

The indices of the Lean statement are $0$-based. The condition $j + 1 \le m$ there is $j \le m$
in the book's indices. -/
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

/-- **Equation (6.24)** of [saad2003iterative], over $\mathbb{R}$ or $\mathbb{C}$. Let
$\|v_1\| = 1$, let $k \ge m$, so that the orthogonalization is full, let the pivots $u_{ll}$
with $l < m$ be nonzero, let $j \le m$, and let $\zeta_j \neq 0$. Then the direction vectors are
semi-conjugate: $(A p_j, p_i) = 0$ for $i < j$.

The indices of the Lean statement are $0$-based. -/
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

/-! ### Section 6.4.2: incomplete orthogonalization with a full band is Algorithm 6.2 -/

private theorem iopW_eq_mgsW (u : ℕ → 𝔼) (w₀ : 𝔼) (N : ℕ) : iopW u 0 w₀ N = mgsW u w₀ N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [iopW_succ, mgsW_succ, ih, iopCoeffOf,
      ite_eq_left_of_eq_true _ _ (eq_true (Nat.zero_le N)), ih]

/-- **Section 6.4.2** of [saad2003iterative]. If $k$ is at least the number of steps performed, then
Algorithm 6.6 computes the same vectors as Algorithm 6.2: incomplete orthogonalization becomes
full orthogonalization.

In Lean, `iop A v k j` equals `arnoldiMGS A v j` for all $j \le k$, $0$-based. No hypothesis on
$v$ is needed. -/
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

/-- One cycle of **Algorithm 6.5** of [saad2003iterative] (FOM($m$)): the FOM iterate of Algorithm
6.4 with $m$ steps, started from $x_0$. -/
noncomputable def fomCycle (m : ℕ) (x₀ : 𝔼) : 𝔼 := fom A b x₀ m

/-- **Algorithm 6.5** of [saad2003iterative] (FOM($m$)). The restarted iterate after $k$ cycles of
$m$ steps, each cycle started from the iterate of the previous one. -/
noncomputable def fomRestarted (m : ℕ) (x₀ : 𝔼) (k : ℕ) : 𝔼 := (fomCycle A b m)^[k] x₀

/-- After $0$ cycles, the restarted iterate is $x_0$. -/
@[simp]
theorem fomRestarted_zero (m : ℕ) (x₀ : 𝔼) : fomRestarted A b m x₀ 0 = x₀ := rfl

/-- The restarted iterate after $k + 1$ cycles is one cycle applied to the iterate after $k$ cycles.
-/
theorem fomRestarted_succ (m : ℕ) (x₀ : 𝔼) (k : ℕ) :
    fomRestarted A b m x₀ (k + 1) = fomCycle A b m (fomRestarted A b m x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- FOM($m$) is a Galerkin method in each cycle. If the matrix $H$ of the cycle that starts from the
iterate after $k$ cycles is nonsingular, then the iterate after $k + 1$ cycles is the Galerkin
iterate on the Krylov subspace of the current residual, of dimension index $\min(m, \mu)$ with
$\mu$ the grade of the current $v_1$.

This is all that the book claims about Algorithm 6.5, apart from the numerical Example 6.1. -/
theorem fomRestarted_succ_isGalerkinIterate (m : ℕ) (x₀ : 𝔼) (k : ℕ)
    (hH : FOMDefined A b (fomRestarted A b m x₀ k)
      (mEff A b (fomRestarted A b m x₀ k) m)) :
    Krylov.IsGalerkinIterate (op A) b (fomRestarted A b m x₀ k)
      (mEff A b (fomRestarted A b m x₀ k) m) (fomRestarted A b m x₀ (k + 1)) := by
  rw [fomRestarted_succ]
  exact fom_isGalerkinIterate A b _ hH

end Restarted

/-! ### The numbered results of Section 6.4, over the real numbers -/

section BookResults

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n))
  (v : EuclideanSpace ℝ (Fin n)) (k : ℕ)

/-- **Equations (6.16)–(6.17)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and
$b, x_0 \in \mathbb{R}^n$. Let $H_m$ be nonsingular, and let $m$ be at most the grade of
$v_1 = r_0 / \beta$. Then the FOM iterate $x_m = x_0 + V_m y_m$ with
$y_m = H_m^{-1} (\beta e_1)$ is the orthogonal projection method (6.15) onto
$\mathcal{K}_m(A, r_0)$:
$$x_m - x_0 \in \mathcal{K}_m(A, r_0), \qquad b - Ax_m \perp \mathcal{K}_m(A, r_0).$$

The approximation is `Krylov.IsGalerkinIterate`. -/
theorem equation_6_16_17 {m : ℕ} (hH : FOMDefined A b x₀ m) (hm : m ≤ grade A (v₁ A b x₀)) :
    Krylov.IsGalerkinIterate (op A) b x₀ m (fomFixed A b x₀ m) :=
  fomFixed_isGalerkinIterate A b x₀ hH hm

/-- **Equations (6.16)–(6.17)** of [saad2003iterative], uniqueness. Let
$A \in \mathbb{R}^{n \times n}$ and $b, x_0 \in \mathbb{R}^n$. Let $H_m$ be nonsingular, and let
$m$ be at most the grade of $v_1$. If $x - x_0 \in \mathcal{K}_m(A, r_0)$ and
$b - Ax \perp \mathcal{K}_m(A, r_0)$, then $x$ is the FOM iterate $x_m$. -/
theorem equation_6_16_17_unique {m : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hH : FOMDefined A b x₀ m)
    (hm : m ≤ grade A (v₁ A b x₀)) (hx : Krylov.IsGalerkinIterate (op A) b x₀ m x) :
    x = fomFixed A b x₀ m :=
  eq_fomFixed_of_isGalerkinIterate A b x₀ hH hm hx

/-- **Section 6.4.1** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and
$b, x_0 \in \mathbb{R}^n$, and let $m$ be at most the grade of $v_1$. Then the orthogonal
projection method onto $\mathcal{K}_m(A, r_0)$ has a unique solution if and only if FOM is
defined at step $m$, that is, $H_m$ is nonsingular. -/
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
  · rw [FOMDefined, H_v₁ A b x₀]
    exact Krylov.existsUnique_isGalerkinIterate_iff_isUnit (by rwa [← grade_v₁])

/-- **Section 6.4.1** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and
$b, x_0 \in \mathbb{R}^n$. Then for every $m$,
$$V_m^T r_0 = \beta e_1.$$

No hypothesis is needed: when $r_0 = 0$, both sides vanish. -/
theorem Vt_r₀ (m : ℕ) :
    (V A (v₁ A b x₀) m)ᵀ *ᵥ WithLp.ofLp (r₀ A b x₀) = (β A b x₀ : ℝ) • e₁ m := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact conjTranspose_V_mulVec_r₀ A b x₀ m

/-- **Proposition 6.7** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and
$b, x_0 \in \mathbb{R}^n$. Let $m \ge 1$, let $H_m$ be nonsingular, and let $m$ be at most the
grade of $v_1$. Then the residual of the FOM iterate is
$$b - Ax_m = -h_{m+1,m} (e_m^T y_m) v_{m+1}.$$

The indices of the Lean statement are $0$-based: $h_{m+1,m}$ is
`arnoldiCoeff A (v₁ A b x₀) m (m - 1)`, $e_m^T y_m$ is the last entry of `fomY A b x₀ m`, and
$v_{m+1}$ is `arnoldiCGS A (v₁ A b x₀) m`. -/
theorem proposition_6_7 {m : ℕ} (hH : FOMDefined A b x₀ m) (hm : m ≤ grade A (v₁ A b x₀))
    (hm0 : 0 < m) :
    b - op A (fomFixed A b x₀ m)
      = -(arnoldiCoeff A (v₁ A b x₀) m (m - 1) * fomY A b x₀ m ⟨m - 1, by omega⟩) •
          arnoldiCGS A (v₁ A b x₀) m :=
  residual_fomFixed A b x₀ hH hm hm0

/-- **Equation (6.18)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and
$b, x_0 \in \mathbb{R}^n$. Let $m \ge 1$, let $H_m$ be nonsingular, and let $m$ be at most the
grade of $v_1$. Then
$$\|b - Ax_m\|_2 = |h_{m+1,m}| \, |e_m^T y_m|.$$

The book writes $h_{m+1,m}$ without the absolute value. For $\|v_1\| = 1$ the coefficient is the
norm $\|w_m\|_2 \ge 0$ (`SaadSparse.Chapter06.arnoldiCoeff_succ_self`). -/
theorem equation_6_18 {m : ℕ} (hH : FOMDefined A b x₀ m) (hm : m ≤ grade A (v₁ A b x₀))
    (hm0 : 0 < m) :
    ‖b - op A (fomFixed A b x₀ m)‖
      = |arnoldiCoeff A (v₁ A b x₀) m (m - 1)| * |fomY A b x₀ m ⟨m - 1, by omega⟩| := by
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact norm_residual_fomFixed A b x₀ hH hm hm0

/-! ### Section 6.4.2: the incomplete orthogonalization methods -/

/-- **Section 6.4.2** of [saad2003iterative], (6.7) for incomplete orthogonalization. Let
$A \in \mathbb{R}^{n \times n}$ and $v \in \mathbb{R}^n$. For every $k$ and $m$, the vectors and
coefficients of Algorithm 6.6 satisfy
$$A V_m = V_{m+1} \bar H_m.$$

The proof of (6.6)–(6.7) never uses the orthogonality of the $v_i$, so no hypothesis is needed. -/
theorem iop_eq_6_7 (m : ℕ) : A * VI A v k m = VI A v k (m + 1) * HbarI A v k m :=
  mul_VI_eq A v k m

/-- **Section 6.4.2** of [saad2003iterative], Proposition 6.7 for IOM. Let
$A \in \mathbb{R}^{n \times n}$ and $b, x_0 \in \mathbb{R}^n$. Let $m \ge 1$, and let the matrix
$H_m$ of Algorithm 6.6 started at $v_1 = r_0 / \beta$ be nonsingular. Then the residual of the
IOM iterate with $m$ steps is
$$b - Ax_m = -h_{m+1,m} (e_m^T y_m) v_{m+1}.$$
-/
theorem proposition_6_7_iom {m : ℕ} (hH : IsUnit (HI A (v₁ A b x₀) k m)) (hm0 : 0 < m) :
    b - op A (iomFixed A b x₀ k m)
      = -(iopCoeff A (v₁ A b x₀) k m (m - 1) * iomY A b x₀ k m ⟨m - 1, by omega⟩) •
          iop A (v₁ A b x₀) k m :=
  residual_iomFixed A b x₀ k hH hm0

/-- **Section 6.4.2** of [saad2003iterative], (6.18) for IOM. Let $A \in \mathbb{R}^{n \times n}$
and $b, x_0 \in \mathbb{R}^n$. Let $m \ge 1$, let the matrix $H_m$ of Algorithm 6.6 be
nonsingular, and let $\|v_1\| = 1$. Then the IOM iterate with $m$ steps satisfies
$$\|b - Ax_m\|_2 = |h_{m+1,m}| \, |e_m^T y_m|.$$
-/
theorem equation_6_18_iom {m : ℕ} (hH : IsUnit (HI A (v₁ A b x₀) k m)) (hm0 : 0 < m)
    (hv : ‖v₁ A b x₀‖ = 1) :
    ‖b - op A (iomFixed A b x₀ k m)‖
      = |iopCoeff A (v₁ A b x₀) k m (m - 1)| * |iomY A b x₀ k m ⟨m - 1, by omega⟩| := by
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact norm_residual_iomFixed A b x₀ k hH hm0 hv

/-- **Section 6.4.2** of [saad2003iterative], the DIOM residual norm. Let
$A \in \mathbb{R}^{n \times n}$ and $b, x_0 \in \mathbb{R}^n$. Let $m \ge 1$, let $\|v_1\| = 1$,
and let the pivots $u_{ll}$ with $l < m$ of the LU factorization of $H_m$ be nonzero. Then
$$\|b - Ax_m\|_2 = |h_{m+1,m}| \, |\zeta_m / u_{mm}|.$$

The indices of the Lean statement are $0$-based: $\zeta_m$ is `diomZeta _ _ (m - 1)` and
$u_{mm}$ is `dioU _ (m - 1) (m - 1)`. -/
theorem diom_residual {m : ℕ} (hm0 : 0 < m) (hv : ‖v₁ A b x₀‖ = 1)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    ‖b - op A (diom A b x₀ k m)‖
      = |iopCoeff A (v₁ A b x₀) k m (m - 1)| *
        |diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : ℝ) (m - 1)
          / dioU (iopCoeff A (v₁ A b x₀) k) (m - 1) (m - 1)| := by
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
  exact norm_residual_diom A b x₀ k hm0 hv hpiv

/-- **Section 6.4.2** of [saad2003iterative], the LU factorization. Let $h$ be an upper Hessenberg
coefficient function, $h_{ac} = 0$ for $a > c + 1$, with $k$ nonzero diagonals on and above the
diagonal, $h_{ac} = 0$ for $a + k \le c$. Let the pivots $u_{ll}$ with $l < m$ be nonzero. Then
$H_m = L_m U_m$, where $L_m$ is unit lower bidiagonal and $U_m$ is upper triangular with
$u_{ij} = 0$ for $i + k \le j$. -/
theorem hessLU_spec (h : ℕ → ℕ → ℝ) (hh : ∀ a c, c + 1 < a → h a c = 0)
    (hband : ∀ a c, a + k ≤ c → h a c = 0) {m : ℕ} (hpiv : ∀ l, l < m → dioU h l l ≠ 0) :
    (hessLU h m).1 * (hessLU h m).2 = Krylov.hessenbergSqOf h m ∧
      (∀ i : Fin m, (hessLU h m).1 i i = 1) ∧
      (∀ i j : Fin m, (i : ℕ) ≠ (j : ℕ) → (i : ℕ) ≠ (j : ℕ) + 1 → (hessLU h m).1 i j = 0) ∧
      (hessLU h m).2.IsUpperTriangular ∧
      (∀ i j : Fin m, (i : ℕ) + k ≤ (j : ℕ) → (hessLU h m).2 i j = 0) :=
  ⟨hessL_mul_hessU h hh hpiv, fun i => hessL_self h i, fun _ _ h1 h2 => hessL_eq_zero h h1 h2,
    hessU_isUpperTriangular h m, fun _ _ hij => hessU_eq_zero_of_add_le hband hij⟩

/-- **Equations (6.20)–(6.21)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and
$b, x_0 \in \mathbb{R}^n$, and let the pivots $u_{ll}$ with $l < m$ of the LU factorization of
$H_m$ be nonzero. Then Algorithm 6.8 (DIOM) is mathematically equivalent to Algorithm 6.7 (IOM):
the DIOM iterate $x_m$ is the IOM iterate with $m$ steps. -/
theorem algorithm_6_8_eq_alg_6_7 {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) :
    diom A b x₀ k m = iomFixed A b x₀ k m :=
  diom_eq_iomFixed A b x₀ k hpiv

/-- **Proposition 6.8** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and
$b, x_0 \in \mathbb{R}^n$. Let $m \ge 1$, let the matrix $H_m$ of Algorithm 6.6 started at
$v_1 = r_0 / \beta$ be nonsingular, let $\|v_{m+1}\| = 1$, and let $v_1, \dots, v_m$ span
$\mathcal{K}_m(A, r_0)$. Then the IOM iterate $x_m$ is a projection approximation onto
$\mathcal{K}_m(A, r_0)$ orthogonally to
$$L_m = \operatorname{span}\{z_1, \dots, z_m\}, \qquad z_i = v_i - (v_i, v_{m+1}) v_{m+1}.$$

**Reading.** The two hypotheses on $v_{m+1}$ and on the span are implicit in the source; see
`SaadSparse.Chapter06.iomFixed_isPetrovGalerkin`.

The book states the result for IOM and DIOM. The Lean statement is about the IOM iterate; DIOM
computes the same iterate when the pivots are nonzero
(`SaadSparse.Chapter06.algorithm_6_8_eq_alg_6_7`). -/
theorem proposition_6_8 {m : ℕ} (hH : IsUnit (HI A (v₁ A b x₀) k m)) (hm0 : 0 < m)
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

/-- **Equation (6.22)** of [saad2003iterative] (Exercise P-6.22). Let
$A \in \mathbb{R}^{n \times n}$ and $b, x_0 \in \mathbb{R}^n$. Let $\|v_1\| = 1$ and let the
pivots $u_{ll}$ with $l < m$ be nonzero. Then the DIOM residuals are orthogonal within a window
of $k$ steps: $(r_j, r_i) = 0$ for all $i, j \le m$ with $i \neq j$ and $|i - j| \le k$. -/
theorem equation_6_22 {m : ℕ} (hv : ‖v₁ A b x₀‖ = 1)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) {i j : ℕ} (hi : i ≤ m)
    (hj : j ≤ m) (hij : i ≠ j) (hk : |(i : ℤ) - (j : ℤ)| ≤ (k : ℤ)) :
    inner ℝ (b - op A (diom A b x₀ k i)) (b - op A (diom A b x₀ k j)) = 0 :=
  inner_residual_diom_eq_zero A b x₀ k hv hpiv hi hj hij hk

/-- **Equation (6.23)** of [saad2003iterative] (Exercise P-6.22). Let
$A \in \mathbb{R}^{n \times n}$ and $b, x_0 \in \mathbb{R}^n$. Let $\|v_1\| = 1$, let the pivots
$u_{ll}$ with $l < m$ be nonzero, let $j \le m$, and let $\zeta_j \neq 0$. Then
$$(A p_j, v_i) = 0 \quad \text{for } j - k + 1 < i < j.$$

The indices of the Lean statement are $0$-based. -/
theorem equation_6_23 {m : ℕ} (hv : ‖v₁ A b x₀‖ = 1)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) {i j : ℕ} (hj : j + 1 ≤ m)
    (hζ : diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : ℝ) j ≠ 0) (h₁ : j + 1 < i + k)
    (h₂ : i < j) :
    inner ℝ (iop A (v₁ A b x₀) k i) (op A (diomP A (v₁ A b x₀) k j)) = 0 :=
  inner_iop_apply_diomP_eq_zero A b x₀ k hv hpiv hj hζ h₁ h₂

/-- **Equation (6.24)** of [saad2003iterative] (Exercise P-6.22). Let
$A \in \mathbb{R}^{n \times n}$ and $b, x_0 \in \mathbb{R}^n$. Let $\|v_1\| = 1$, let $k \ge m$,
so that the orthogonalization is full, let the pivots $u_{ll}$ with $l < m$ be nonzero, let
$j \le m$, and let $\zeta_j \neq 0$. Then the direction vectors are semi-conjugate:
$$(A p_j, p_i) = 0 \quad \text{for } i < j.$$

The indices of the Lean statement are $0$-based. -/
theorem equation_6_24 {m : ℕ} (hv : ‖v₁ A b x₀‖ = 1) (hk : m ≤ k)
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) k) l l ≠ 0) {i j : ℕ} (hj : j + 1 ≤ m)
    (hζ : diomZeta (iopCoeff A (v₁ A b x₀) k) (β A b x₀ : ℝ) j ≠ 0) (hij : i < j) :
    inner ℝ (diomP A (v₁ A b x₀) k i) (op A (diomP A (v₁ A b x₀) k j)) = 0 :=
  inner_diomP_apply_diomP_eq_zero A b x₀ k hv hk hpiv hj hζ hij

/-- **Section 6.4.2** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ and
$v \in \mathbb{R}^n$. If $j \le k$ ($0$-based), then the vector `iop A v k j` of Algorithm 6.6
equals the vector `arnoldiMGS A v j` of Algorithm 6.2: with a full band, incomplete
orthogonalization is Arnoldi's method. -/
theorem algorithm_6_6_eq_alg_6_2 {j : ℕ} (hjk : j ≤ k) : iop A v k j = arnoldiMGS A v j :=
  iop_eq_arnoldiMGS_of_le A v k j hjk

end BookResults

end SaadSparse.Chapter06
