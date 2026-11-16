/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Projection.ObliqueProjection
import Numlib.Krylov.BiLanczos
import NumlibSurface.SaadSparse.Chapter06.Common
import NumlibSurface.SaadSparse.Chapter06.Section03

/-!
# Saad, Section 7.1: Lanczos biorthogonalization

This module formalizes Section 7.1 of [saad2003iterative], with the exercises P-7.2, P-7.3, P-7.5
and P-7.6. The Lanczos biorthogonalization procedure (Algorithm 7.1) starts from vectors $v_1$,
$w_1$ with $(v_1, w_1) = 1$ and builds two sequences by three-term recurrences,
$$\delta_{j+1} v_{j+1} = Av_j - \alpha_j v_j - \beta_j v_{j-1}, \qquad \bar\beta_{j+1} w_{j+1} = A^H
  w_j - \bar\alpha_j w_j - \bar\delta_j w_{j-1},$$
with $\alpha_j = (Av_j, w_j)$. As long as the procedure does not break down, the two sequences are
biorthogonal, $(v_j, w_i) = \delta_{ij}$, and span the Krylov subspaces $\mathcal{K}_m(A, v_1)$ and
$\mathcal{K}_m(A^H, w_1)$ (Proposition 7.1). In matrix form,
$AV_m = V_m T_m + \delta_{m+1} v_{m+1} e_m^T$ and $W_m^H A V_m = T_m$ with a tridiagonal $T_m$
((7.3)–(7.5)). Section 7.1.2 separates the lucky breakdown $\hat v_{m+1} = 0$, where the Krylov
subspace is invariant, from the serious breakdown, where $(\hat v_{m+1}, \hat w_{m+1}) = 0$ with
both vectors nonzero, and describes the process by polynomials $p_j$ that are formally orthogonal
for the indefinite form (7.7).

The algorithm computes the backbone two-sided Lanczos process `BiLanczos.vec` and
`BiLanczos.dualVec` of `Numlib.Krylov.BiLanczos` (`SaadSparse.Chapter07.bilanczosV_eq`,
`SaadSparse.Chapter07.bilanczosW_eq`), and Proposition 7.1 and the results after it are read off
from there.

## Main definitions

* Algorithm 7.1, `SaadSparse.Chapter07.bilanczos`, `SaadSparse.Chapter07.bilanczosV`,
  `SaadSparse.Chapter07.bilanczosW`, `SaadSparse.Chapter07.bilanczosBeta`,
  `SaadSparse.Chapter07.bilanczosDelta`, `SaadSparse.Chapter07.bilanczosAlpha`,
  `SaadSparse.Chapter07.bilanczosVhat`, `SaadSparse.Chapter07.bilanczosWhat`: the Lanczos
  biorthogonalization procedure and the quantities $v_j$, $w_j$, $\beta_j$, $\delta_j$, $\alpha_j$,
  $\hat v_{j+1}$, $\hat w_{j+1}$ that it computes.
* Algorithm 7.1, `SaadSparse.Chapter07.w₁`: the dual starting vector, rescaled so that
  $(v_1, w_1) = 1$.
* Section 7.1, `SaadSparse.Chapter07.NoBreakdown`, `SaadSparse.Chapter07.NoSeriousBreakdown`: the
  hypotheses that the procedure does not break down in its first $m$ steps, and that it never has a
  serious breakdown.
* Equations (7.2) and (7.15), `SaadSparse.Chapter07.bilanczosCoeff`, `SaadSparse.Chapter07.T`,
  `SaadSparse.Chapter07.Tbar`, `SaadSparse.Chapter07.V`, `SaadSparse.Chapter07.W`: the tridiagonal
  matrices $T_m$ and $\bar T_m$ and the basis matrices $V_m$ and $W_m$.
* Equation (7.7), `SaadSparse.Chapter07.polyForm`: the indefinite bilinear form
  $\langle p, q \rangle = (p(A) v_1, q(A^T) w_1)$ on polynomials.
* Section 7.1.2, `SaadSparse.Chapter07.bilanczosPoly`, `SaadSparse.Chapter07.momentMatrix`: the
  polynomials $p_j$ with $\hat v_{j+1} = p_j(A) v_1$, and the moment matrix $M_k$.
* Exercise P-7.3, `SaadSparse.Chapter07.bilanczosVUnit`, `SaadSparse.Chapter07.bilanczosWUnit`: the
  Lanczos vectors rescaled to unit 2-norm.

## Main results

* Algorithm 7.1, `SaadSparse.Chapter07.inner_w₁_v₁`: the normalization $(v_1, w_1) = 1$ of line 1.
* Section 7.1, `SaadSparse.Chapter07.bilanczosV_eq`, `SaadSparse.Chapter07.bilanczosW_eq`: the two
  sequences of Algorithm 7.1 are those of the backbone two-sided Lanczos process.
* Equation (7.1), `SaadSparse.Chapter07.equation_7_1`, `SaadSparse.Chapter07.equation_7_1_norm`: the
  scalars of lines 7–8 satisfy $\delta_{j+1} \beta_{j+1} = (\hat v_{j+1}, \hat w_{j+1})$, and the
  scaling by 2-norms also satisfies (7.1).
* Remark after (7.2), `SaadSparse.Chapter07.norm_bilanczosBeta_succ`: $|\beta_j| = |\delta_j|$.
* Proposition 7.1, `SaadSparse.Chapter07.proposition_7_1`, `SaadSparse.Chapter07.proposition_7_1'`,
  `SaadSparse.Chapter07.proposition_7_1_span`: the two sequences are biorthogonal and span
  $\mathcal{K}_m(A, v_1)$ and $\mathcal{K}_m(A^H, w_1)$.
* Exercise P-7.2, `SaadSparse.Chapter07.problem_7_2`: the columns of $V_m$ are linearly independent,
  and so are those of $W_m$.
* Equations (7.3), (7.4) and (7.15), `SaadSparse.Chapter07.equation_7_3`:
  $AV_m = V_m T_m + \delta_{m+1} v_{m+1} e_m^T$, $A^H W_m = W_m T_m^H + \bar\beta_{m+1} w_{m+1}
  e_m^T$, and $AV_m = V_{m+1} \bar T_m$.
* Section 7.1, `SaadSparse.Chapter07.bilanczos_hessenbergRelation`: without serious breakdown, the
  vectors $v_j$ satisfy the backbone Hessenberg relation with the tridiagonal coefficients.
* Equation (7.5), `SaadSparse.Chapter07.equation_7_5`: $W_m^H A V_m = T_m$.
* Exercise P-7.6, `SaadSparse.Chapter07.problem_7_6`, `SaadSparse.Chapter07.problem_7_6_inf_eq_bot`:
  $V_m W_m^H$ is the oblique projector onto $\mathcal{K}_m(A, v_1)$ orthogonally to
  $\mathcal{K}_m(A^H, w_1)$, which exists because $\mathcal{K}_m(A, v_1) \cap \mathcal{K}_m(A^H,
  w_1)^\perp = \{0\}$.
* Section 7.1.2, `SaadSparse.Chapter07.noSeriousBreakdown_of_bilanczosVhat_eq_zero`,
  `SaadSparse.Chapter07.krylov_mem_invtSubmodule_of_bilanczosVhat_eq_zero`,
  `SaadSparse.Chapter07.span_bilanczosV_succ`: a lucky breakdown is not a serious one, and at a
  lucky breakdown the Krylov subspace is $A$-invariant.
* Section 7.1.2, `SaadSparse.Chapter07.bilanczosVhat_eq_aeval`,
  `SaadSparse.Chapter07.bilanczosWhat_eq_smul`, `SaadSparse.Chapter07.bilanczosPoly_natDegree`:
  $\hat v_{j+1} = p_j(A) v_1$ with $\deg p_j = j$, and $\hat w_{j+1}$ is a multiple of
  $\bar p_j(A^H) w_1$.
* Section 7.1.2, `SaadSparse.Chapter07.polyForm_eq_moment`,
  `SaadSparse.Chapter07.momentMatrix_apply_eq_of_add_eq`: the form (7.7) is a moment functional, and
  $M_k$ is a Hankel matrix.
* Section 7.1.2, `SaadSparse.Chapter07.breakdown_iff_polyForm_eq_zero`,
  `SaadSparse.Chapter07.polyForm_bilanczosPoly_eq_zero`: a serious breakdown at step $j$ is
  $\langle p_j, p_j \rangle = 0$, and the $p_j$ are orthogonal for the form (7.7).
* Exercise P-7.5, `SaadSparse.Chapter07.problem_7_5`: $t^k p_j$ is orthogonal to $p_i$ whenever
  $\deg(t^k p_i) < \deg p_j$.
* Exercise P-7.3, `SaadSparse.Chapter07.problem_7_3`: the vectors rescaled to unit 2-norm stay
  biorthogonal up to diagonal factors, and the projected problem becomes a generalized eigenvalue
  problem.

## Conventions

* The book states Algorithm 7.1 over $\mathbb{R}$ with $A^T$. Here it is stated over $\mathbb{R}$ or
  $\mathbb{C}$ with $A^H$, with the conjugations that make the recurrences hold over $\mathbb{C}$;
  over $\mathbb{R}$ it is the book's algorithm.
* Indices are $0$-based, and the statements below use the indices of the book.
* The book's $v_{j+1}$ is `SaadSparse.Chapter07.bilanczosV A v₁ w₁ j`, and the same shift by one
  applies to $w$, $\alpha$, $\beta$ and $\delta$.
* In particular, the book's $\delta_1 = 0$ is `SaadSparse.Chapter07.bilanczosDelta A v₁ w₁ 0 = 0`.
* The book's $\hat v_{j+2}$ and $\hat w_{j+2}$, computed from $v_{j+1}$ and $w_{j+1}$, are
  `SaadSparse.Chapter07.bilanczosVhat A v₁ w₁ j` and `SaadSparse.Chapter07.bilanczosWhat A v₁ w₁ j`.
* The book's $p_{j+1}$ is `SaadSparse.Chapter07.bilanczosPoly A v₁ w₁ j`.
* `SaadSparse.Chapter07.NoBreakdown A v₁ w₁ m` says that $(v_1, w_1) = 1$ and that the first $m$
  steps pass the test of line 7, so that $v_1, \dots, v_{m+1}$ and $w_1, \dots, w_{m+1}$ are
  computed.

## Implementation notes

* After a breakdown, division by zero gives $0$ in Lean, so every later vector is $0$; this is the
  book's "Stop", and the definitions are total.
* `SaadSparse.Chapter07.NoSeriousBreakdown` is the weaker global hypothesis that the Hessenberg
  relation needs: a vanishing $(\hat v_{j+1}, \hat w_{j+1})$ must come with $\hat v_{j+1} = 0$. It
  does not follow from `SaadSparse.Chapter07.NoBreakdown A v₁ w₁ m` for any $m$, because in finite
  dimension the process always terminates. The relation (7.3) is false at a serious breakdown, where
  there is no $v_{m+1}$ along which to expand $Av_m$.
* The scalars of lines 7–8 are constrained only by their product $\delta_{j+1} \beta_{j+1} = (\hat
  v_{j+1}, \hat w_{j+1})$: any pair with this product normalizes the step to
  $(v_{j+1}, w_{j+1}) = 1$ (`SaadSparse.Chapter07.inner_smul_smul_eq_one`). The scaling by 2-norms,
  which the book names as an alternative, is the one that Section 7.3 uses from (7.18) on.
* The exactness of the iterate of Algorithm 7.2 at a lucky breakdown is in
  `NumlibSurface.SaadSparse.Chapter07.Section02`.

## Deviations from the source

* **Exercise P-7.5** (correction). The book says that $t^k p_j$ is orthogonal to
  $p_1, \dots, p_{j-k}$; the range is one polynomial too long, and the statement here stops at
  $p_{j-k-1}$. The worked example of Section 7.1.2 has the same off-by-one. See
  `SaadSparse.Chapter07.problem_7_5`.

## Not formalized

* **The LU factorization $M_k = L_k U_k$ of the moment matrix** (Section 7.1.2), on which the
  look-ahead implementation of Parlett, Taylor and Liu pivots. Neither Mathlib nor this library has
  a general theorem on the existence of an LU factorization.
* **The look-ahead Lanczos algorithms** (Section 7.1.2). They are described as implementation, with
  no claim attached.
* **Exercise P-7.5, second part.** Orthogonalizing $q$ against the polynomials of the first part is
  Gram–Schmidt for the form (7.7), and adds no content beyond the first part.
* **Exercise P-7.5, third part.** It asks for a general look-ahead procedure, which is an algorithm,
  not a theorem.
-/

open Matrix

open scoped Matrix SaadSparse

namespace SaadSparse.Chapter07

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### The dual starting vector -/

section Start

/-- **Algorithm 7.1** of [saad2003iterative], line 1, the dual starting vector. Let
$v_1 = r_0/\|r_0\|$ with $r_0 = b - Ax_0$, and let $w$ be a vector, in Algorithm 7.3 the dual
residual $r_0^* = b^* - A^H x_0^*$. Then
$$w_1 = \frac{w}{(w, v_1)},$$
so that $(v_1, w_1) = 1$. If $(w, v_1) = 0$, no such rescaling exists, and $w_1 = 0$ by division
by zero in Lean. -/
noncomputable def w₁ (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ w : EuclideanSpace 𝕜 (Fin n)) :
    EuclideanSpace 𝕜 (Fin n) :=
  (inner 𝕜 (Chapter06.v₁ A b x₀) w)⁻¹ • w

/-- **Algorithm 7.1** of [saad2003iterative], line 1. If $(w, v_1) \neq 0$, then the dual starting
vector satisfies $(v_1, w_1) = 1$.

In Mathlib's inner product, which is conjugate-linear in the first argument, $(v_1, w_1)$ is
`inner 𝕜 w₁ v₁`. -/
theorem inner_w₁_v₁ (A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ w : EuclideanSpace 𝕜 (Fin n))
    (hw : inner 𝕜 (Chapter06.v₁ A b x₀) w ≠ 0) :
    inner 𝕜 (w₁ A b x₀ w) (Chapter06.v₁ A b x₀) = 1 := by
  have hconj : starRingEnd 𝕜 (inner 𝕜 (Chapter06.v₁ A b x₀) w) = inner 𝕜 w (Chapter06.v₁ A b x₀) :=
    inner_conj_symm _ _
  rw [w₁, inner_smul_left, map_inv₀, hconj, inv_mul_cancel₀]
  rw [← hconj]
  exact fun h => hw (by simpa using congrArg (starRingEnd 𝕜) h)

end Start

/-! ### Algorithm 7.1 -/

section Algorithm

variable (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ w₁ : EuclideanSpace 𝕜 (Fin n))

/-- One pass through lines 4–10 of Algorithm 7.1. From the state $(v_j, w_j, v_{j-1}, w_{j-1},
\beta_j, \delta_j)$ it computes $\alpha_j = (Av_j, w_j)$, the vectors $\hat v_{j+1} = Av_j -
\alpha_j v_j - \beta_j v_{j-1}$ and $\hat w_{j+1} = A^H w_j - \bar\alpha_j w_j - \bar\delta_j
w_{j-1}$, the scalars $\delta_{j+1} = |(\hat v_{j+1}, \hat w_{j+1})|^{1/2}$ and $\beta_{j+1} =
(\hat v_{j+1}, \hat w_{j+1})/\delta_{j+1}$, and returns the state $(v_{j+1}, w_{j+1}, v_j, w_j,
\beta_{j+1}, \delta_{j+1})$ with $v_{j+1} = \hat v_{j+1}/\delta_{j+1}$ and
$w_{j+1} = \hat w_{j+1}/\bar\beta_{j+1}$.

The state is the backbone record `BiLanczos.State`. -/
noncomputable def bilanczosStep (s : BiLanczos.State 𝕜 (EuclideanSpace 𝕜 (Fin n))) :
    BiLanczos.State 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  let α : 𝕜 := inner 𝕜 s.w (op A s.v)
  let vh : EuclideanSpace 𝕜 (Fin n) := op A s.v - α • s.v - s.beta • s.vPrev
  let wh : EuclideanSpace 𝕜 (Fin n) :=
    op Aᴴ s.w - starRingEnd 𝕜 α • s.w - starRingEnd 𝕜 s.delta • s.wPrev
  let δ : 𝕜 := ((Real.sqrt ‖inner 𝕜 wh vh‖ : ℝ) : 𝕜)
  { v := δ⁻¹ • vh
    w := (starRingEnd 𝕜 (inner 𝕜 wh vh / δ))⁻¹ • wh
    vPrev := s.v
    wPrev := s.w
    beta := inner 𝕜 wh vh / δ
    delta := δ }

/-- **Algorithm 7.1** of [saad2003iterative] (Lanczos biorthogonalization). The state after $j$
steps of the procedure started from the pair $(v_1, w_1)$, with $v_0 = w_0 = 0$ and
$\beta_1 = \delta_1 = 0$.

The state holds $(v_{j+1}, w_{j+1}, v_j, w_j, \beta_{j+1}, \delta_{j+1})$. A breakdown makes all
later vectors $0$, by division by zero in Lean. -/
noncomputable def bilanczos (j : ℕ) : BiLanczos.State 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  (bilanczosStep A)^[j] { v := v₁, w := w₁, vPrev := 0, wPrev := 0, beta := 0, delta := 0 }

/-- **Algorithm 7.1** of [saad2003iterative], the primal Lanczos vectors:
`SaadSparse.Chapter07.bilanczosV A v₁ w₁ j` is $v_{j+1}$. -/
noncomputable def bilanczosV (j : ℕ) : EuclideanSpace 𝕜 (Fin n) := (bilanczos A v₁ w₁ j).v

/-- **Algorithm 7.1** of [saad2003iterative], the dual Lanczos vectors:
`SaadSparse.Chapter07.bilanczosW A v₁ w₁ j` is $w_{j+1}$. -/
noncomputable def bilanczosW (j : ℕ) : EuclideanSpace 𝕜 (Fin n) := (bilanczos A v₁ w₁ j).w

/-- The previous primal vector: `SaadSparse.Chapter07.bilanczosVPrev A v₁ w₁ j` is $v_j$, with
$v_0 = 0$ as in line 2 of Algorithm 7.1. -/
noncomputable def bilanczosVPrev (j : ℕ) : EuclideanSpace 𝕜 (Fin n) := (bilanczos A v₁ w₁ j).vPrev

/-- The previous dual vector: `SaadSparse.Chapter07.bilanczosWPrev A v₁ w₁ j` is $w_j$, with
$w_0 = 0$ as in line 2 of Algorithm 7.1. -/
noncomputable def bilanczosWPrev (j : ℕ) : EuclideanSpace 𝕜 (Fin n) := (bilanczos A v₁ w₁ j).wPrev

/-- **Algorithm 7.1** of [saad2003iterative], line 8, the superdiagonal coefficients:
`SaadSparse.Chapter07.bilanczosBeta A v₁ w₁ j` is $\beta_{j+1}$, with $\beta_1 = 0$. -/
noncomputable def bilanczosBeta (j : ℕ) : 𝕜 := (bilanczos A v₁ w₁ j).beta

/-- **Algorithm 7.1** of [saad2003iterative], line 7, the subdiagonal coefficients:
`SaadSparse.Chapter07.bilanczosDelta A v₁ w₁ j` is $\delta_{j+1}$, with $\delta_1 = 0$. -/
noncomputable def bilanczosDelta (j : ℕ) : 𝕜 := (bilanczos A v₁ w₁ j).delta

/-- **Algorithm 7.1** of [saad2003iterative], line 4, the diagonal coefficients
$\alpha_j = (Av_j, w_j)$: `SaadSparse.Chapter07.bilanczosAlpha A v₁ w₁ j` is $\alpha_{j+1}$. -/
noncomputable def bilanczosAlpha (j : ℕ) : 𝕜 :=
  inner 𝕜 (bilanczosW A v₁ w₁ j) (op A (bilanczosV A v₁ w₁ j))

/-- **Algorithm 7.1** of [saad2003iterative], line 5, the unnormalized primal vector
$$\hat v_{j+1} = Av_j - \alpha_j v_j - \beta_j v_{j-1}.$$

`SaadSparse.Chapter07.bilanczosVhat A v₁ w₁ j` is the vector computed from $v_{j+1}$, that is,
the book's $\hat v_{j+2}$. -/
noncomputable def bilanczosVhat (j : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  op A (bilanczosV A v₁ w₁ j) - bilanczosAlpha A v₁ w₁ j • bilanczosV A v₁ w₁ j -
    bilanczosBeta A v₁ w₁ j • bilanczosVPrev A v₁ w₁ j

/-- **Algorithm 7.1** of [saad2003iterative], line 6, the unnormalized dual vector
$$\hat w_{j+1} = A^H w_j - \bar\alpha_j w_j - \bar\delta_j w_{j-1}.$$

`SaadSparse.Chapter07.bilanczosWhat A v₁ w₁ j` is the vector computed from $w_{j+1}$, that is,
the book's $\hat w_{j+2}$. -/
noncomputable def bilanczosWhat (j : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  op Aᴴ (bilanczosW A v₁ w₁ j) - starRingEnd 𝕜 (bilanczosAlpha A v₁ w₁ j) • bilanczosW A v₁ w₁ j -
    starRingEnd 𝕜 (bilanczosDelta A v₁ w₁ j) • bilanczosWPrev A v₁ w₁ j

/-! ### The bridge to the backbone two-sided Lanczos process -/

private theorem bilanczosStep_eq (s : BiLanczos.State 𝕜 (EuclideanSpace 𝕜 (Fin n))) :
    bilanczosStep A s = BiLanczos.step (op A) (op Aᴴ) s := rfl

private theorem bilanczos_eq (j : ℕ) :
    bilanczos A v₁ w₁ j = BiLanczos.state (op A) (op Aᴴ) v₁ w₁ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [bilanczos, Function.iterate_succ_apply', ← bilanczos, ih, bilanczosStep_eq,
      ← BiLanczos.state_succ]

/-- For every $j$, the primal vector $v_{j+1}$ of Algorithm 7.1 is the backbone two-sided Lanczos
vector `BiLanczos.vec (SaadSparse.Chapter06.op A) (SaadSparse.Chapter06.op Aᴴ) v₁ w₁ j` of $A$
and its adjoint $A^H$.

This identification is how the results of this module are read off from
`Numlib.Krylov.BiLanczos`. -/
theorem bilanczosV_eq (j : ℕ) :
    bilanczosV A v₁ w₁ j = BiLanczos.vec (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosV, bilanczos_eq]; rfl

/-- For every $j$, the dual vector $w_{j+1}$ of Algorithm 7.1 is the backbone dual vector
`BiLanczos.dualVec`. -/
theorem bilanczosW_eq (j : ℕ) :
    bilanczosW A v₁ w₁ j = BiLanczos.dualVec (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosW, bilanczos_eq]; rfl

/-- The previous primal vector $v_j$ of Algorithm 7.1 is the backbone `BiLanczos.vecPrev`. -/
theorem bilanczosVPrev_eq (j : ℕ) :
    bilanczosVPrev A v₁ w₁ j = BiLanczos.vecPrev (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosVPrev, bilanczos_eq]; rfl

/-- The previous dual vector $w_j$ of Algorithm 7.1 is the backbone `BiLanczos.dualVecPrev`. -/
theorem bilanczosWPrev_eq (j : ℕ) :
    bilanczosWPrev A v₁ w₁ j = BiLanczos.dualVecPrev (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosWPrev, bilanczos_eq]; rfl

/-- The coefficients $\beta_j$ of Algorithm 7.1 are the backbone `BiLanczos.beta`. -/
theorem bilanczosBeta_eq (j : ℕ) :
    bilanczosBeta A v₁ w₁ j = BiLanczos.beta (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosBeta, bilanczos_eq]; rfl

/-- The coefficients $\delta_j$ of Algorithm 7.1 are the backbone `BiLanczos.delta`. -/
theorem bilanczosDelta_eq (j : ℕ) :
    bilanczosDelta A v₁ w₁ j = BiLanczos.delta (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosDelta, bilanczos_eq]; rfl

/-- The coefficients $\alpha_j$ of Algorithm 7.1 are the backbone `BiLanczos.alpha`. -/
theorem bilanczosAlpha_eq (j : ℕ) :
    bilanczosAlpha A v₁ w₁ j = BiLanczos.alpha (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosAlpha, bilanczosV_eq, bilanczosW_eq]; rfl

/-- The unnormalized primal vectors $\hat v_{j+1}$ of Algorithm 7.1, line 5, are the backbone
`BiLanczos.vhat`. -/
theorem bilanczosVhat_eq (j : ℕ) :
    bilanczosVhat A v₁ w₁ j = BiLanczos.vhat (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosVhat, bilanczosV_eq, bilanczosVPrev_eq, bilanczosAlpha_eq, bilanczosBeta_eq,
    BiLanczos.vhat_eq]

/-- The unnormalized dual vectors $\hat w_{j+1}$ of Algorithm 7.1, line 6, are the backbone
`BiLanczos.dualVhat`. -/
theorem bilanczosWhat_eq (j : ℕ) :
    bilanczosWhat A v₁ w₁ j = BiLanczos.dualVhat (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosWhat, bilanczosW_eq, bilanczosWPrev_eq, bilanczosAlpha_eq, bilanczosDelta_eq,
    BiLanczos.dualVhat_eq]

/-! ### Lines 1 and 6–9 of Algorithm 7.1 -/

/-- Algorithm 7.1, line 1: the primal sequence starts at $v_1$. -/
@[simp] theorem bilanczosV_zero : bilanczosV A v₁ w₁ 0 = v₁ := rfl

/-- Algorithm 7.1, line 1: the dual sequence starts at $w_1$. -/
@[simp] theorem bilanczosW_zero : bilanczosW A v₁ w₁ 0 = w₁ := rfl

/-- Algorithm 7.1, line 2: $v_0 = 0$. -/
@[simp] theorem bilanczosVPrev_zero : bilanczosVPrev A v₁ w₁ 0 = 0 := rfl

/-- Algorithm 7.1, line 2: $w_0 = 0$. -/
@[simp] theorem bilanczosWPrev_zero : bilanczosWPrev A v₁ w₁ 0 = 0 := rfl

/-- Algorithm 7.1, line 2: $\beta_1 = 0$. -/
@[simp] theorem bilanczosBeta_zero : bilanczosBeta A v₁ w₁ 0 = 0 := rfl

/-- Algorithm 7.1, line 2: $\delta_1 = 0$. -/
@[simp] theorem bilanczosDelta_zero : bilanczosDelta A v₁ w₁ 0 = 0 := rfl

/-- The previous primal vector after step $j + 1$ is $v_{j+1}$. -/
@[simp] theorem bilanczosVPrev_succ (j : ℕ) :
    bilanczosVPrev A v₁ w₁ (j + 1) = bilanczosV A v₁ w₁ j := by
  rw [bilanczosVPrev_eq, bilanczosV_eq, BiLanczos.vecPrev_succ]

/-- The previous dual vector after step $j + 1$ is $w_{j+1}$. -/
@[simp] theorem bilanczosWPrev_succ (j : ℕ) :
    bilanczosWPrev A v₁ w₁ (j + 1) = bilanczosW A v₁ w₁ j := by
  rw [bilanczosWPrev_eq, bilanczosW_eq, BiLanczos.dualVecPrev_succ]

/-- Algorithm 7.1, line 7: for every $j \ge 1$, $\delta_{j+1} = |(\hat v_{j+1}, \hat
w_{j+1})|^{1/2}$. -/
theorem bilanczosDelta_succ (j : ℕ) : bilanczosDelta A v₁ w₁ (j + 1) =
    ((Real.sqrt ‖inner 𝕜 (bilanczosWhat A v₁ w₁ j) (bilanczosVhat A v₁ w₁ j)‖ : ℝ) : 𝕜) := by
  rw [bilanczosDelta_eq, bilanczosWhat_eq, bilanczosVhat_eq, BiLanczos.delta_succ]
  rfl

/-- Algorithm 7.1, line 8: for every $j \ge 1$, $\beta_{j+1} = (\hat v_{j+1}, \hat
w_{j+1})/\delta_{j+1}$. -/
theorem bilanczosBeta_succ (j : ℕ) : bilanczosBeta A v₁ w₁ (j + 1) =
    inner 𝕜 (bilanczosWhat A v₁ w₁ j) (bilanczosVhat A v₁ w₁ j) /
      bilanczosDelta A v₁ w₁ (j + 1) := by
  rw [bilanczosBeta_eq, bilanczosWhat_eq, bilanczosVhat_eq, bilanczosDelta_eq,
    BiLanczos.beta_succ]
  rfl

/-- **Section 7.1** of [saad2003iterative], remark after (7.2). With the choice of lines 7–8 of
Algorithm 7.1, $|\beta_j| = |\delta_j|$ for every $j \ge 2$; the book says that "the
$\delta_j$'s are positive and $\beta_j = \pm\delta_j$".

The equality holds at every step, with no hypothesis on breakdown. -/
theorem norm_bilanczosBeta_succ (j : ℕ) :
    ‖bilanczosBeta A v₁ w₁ (j + 1)‖ = ‖bilanczosDelta A v₁ w₁ (j + 1)‖ := by
  rw [bilanczosBeta_eq, bilanczosDelta_eq, BiLanczos.norm_beta_succ]

/-- Algorithm 7.1, line 9: for every $j \ge 1$, $w_{j+1} = \hat w_{j+1}/\bar\beta_{j+1}$, and
$w_{j+1} = 0$ on breakdown. -/
theorem bilanczosW_succ (j : ℕ) : bilanczosW A v₁ w₁ (j + 1) =
    (starRingEnd 𝕜 (bilanczosBeta A v₁ w₁ (j + 1)))⁻¹ • bilanczosWhat A v₁ w₁ j := by
  rw [bilanczosW_eq, bilanczosWhat_eq, bilanczosBeta_eq, BiLanczos.dualVec_succ]

/-- Algorithm 7.1, line 10: for every $j \ge 1$, $v_{j+1} = \hat v_{j+1}/\delta_{j+1}$, and
$v_{j+1} = 0$ on breakdown. -/
theorem bilanczosV_succ (j : ℕ) : bilanczosV A v₁ w₁ (j + 1) =
    (bilanczosDelta A v₁ w₁ (j + 1))⁻¹ • bilanczosVhat A v₁ w₁ j := by
  rw [bilanczosV_eq, bilanczosVhat_eq, bilanczosDelta_eq, BiLanczos.vec_succ]

/-! ### (7.1): the scaling of lines 7–8 -/

/-- **Equation (7.1)** of [saad2003iterative]. For every $j \ge 1$, the two scalars of lines 7–8 of
Algorithm 7.1 satisfy
$$\delta_{j+1} \beta_{j+1} = (\hat v_{j+1}, \hat w_{j+1}).$$

Lines 9 and 10 divide $\hat w_{j+1}$ and $\hat v_{j+1}$ by these scalars, so this product is the
only constraint that the normalization $(v_{j+1}, w_{j+1}) = 1$ puts on the pair, and the choice
of lines 7–8 is one of many admissible ones (`SaadSparse.Chapter07.inner_smul_smul_eq_one`). No
hypothesis is needed: at a breakdown both sides are $0$. -/
theorem equation_7_1 (j : ℕ) :
    bilanczosDelta A v₁ w₁ (j + 1) * bilanczosBeta A v₁ w₁ (j + 1)
      = inner 𝕜 (bilanczosWhat A v₁ w₁ j) (bilanczosVhat A v₁ w₁ j) := by
  rw [bilanczosDelta_eq, bilanczosBeta_eq, bilanczosWhat_eq, bilanczosVhat_eq,
    BiLanczos.delta_mul_beta_succ]
  rfl

/-- Let $\hat v$, $\hat w$ be vectors with $(\hat v, \hat w) \neq 0$, and let $\delta$, $\beta$ be
scalars with $\delta\beta = (\hat v, \hat w)$. Then $(\hat v/\delta, \hat w/\bar\beta) = 1$. So
any such pair may be used in lines 7–8 of Algorithm 7.1, and lines 9–10 still give the
normalization $(v_{j+1}, w_{j+1}) = 1$. -/
theorem inner_smul_smul_eq_one {vh wh : EuclideanSpace 𝕜 (Fin n)} {δ β : 𝕜}
    (hne : inner 𝕜 wh vh ≠ 0) (h : δ * β = inner 𝕜 wh vh) :
    inner 𝕜 ((starRingEnd 𝕜 β)⁻¹ • wh) (δ⁻¹ • vh) = 1 :=
  BiLanczos.inner_smul_smul_eq_one_of_mul_eq hne h

/-- **Equation (7.1)** of [saad2003iterative], the scaling by 2-norms. Let $\hat v$, $\hat w$ be
vectors with $(\hat v, \hat w) \neq 0$, and let $\delta = \|\hat v\|_2$ and
$\beta = (\hat v, \hat w)/\|\hat v\|_2$. Then $\delta\beta = (\hat v, \hat w)$, the vector
$\hat v/\delta$ has unit 2-norm, and $(\hat v/\delta, \hat w/\bar\beta) = 1$.

This is the book's remark in Section 7.1.1 that "both vectors can also be scaled by their
2-norms". It justifies the hypothesis $\|v_j\|_2 = 1$ that Section 7.3 uses from (7.18) on. -/
theorem equation_7_1_norm {vh wh : EuclideanSpace 𝕜 (Fin n)} (hne : inner 𝕜 wh vh ≠ 0) :
    (‖vh‖ : 𝕜) * (inner 𝕜 wh vh / (‖vh‖ : 𝕜)) = inner 𝕜 wh vh ∧
      ‖((‖vh‖ : 𝕜))⁻¹ • vh‖ = 1 ∧
      inner 𝕜 ((starRingEnd 𝕜 (inner 𝕜 wh vh / (‖vh‖ : 𝕜)))⁻¹ • wh) (((‖vh‖ : 𝕜))⁻¹ • vh) = 1 := by
  have hv : vh ≠ 0 := fun hc => hne (by rw [hc, inner_zero_right])
  have hn : (‖vh‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hv)
  have hmul : (‖vh‖ : 𝕜) * (inner 𝕜 wh vh / (‖vh‖ : 𝕜)) = inner 𝕜 wh vh := by field_simp
  refine ⟨hmul, ?_, inner_smul_smul_eq_one hne hmul⟩
  rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg vh),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]

end Algorithm

/-! ### The no-breakdown hypotheses -/

section Breakdown

variable {A : Matrix (Fin n) (Fin n) 𝕜} {v₁ w₁ : EuclideanSpace 𝕜 (Fin n)}

/-- **Section 7.1** of [saad2003iterative], the no-breakdown hypothesis. Algorithm 7.1 **runs $m$
steps without breakdown** if the starting pair satisfies $(v_1, w_1) = 1$, as in line 1, and the
test of line 7 passes in each of the first $m$ steps: $(\hat v_{j+1}, \hat w_{j+1}) \neq 0$ for
$1 \le j \le m$.

This is the hypothesis that the book carries through Section 7.1. It is the surface form of
`BiLanczos.NoBreakdown`; the adjoint relation that the backbone takes as data holds here
automatically, because `SaadSparse.Chapter06.op Aᴴ` is the adjoint of
`SaadSparse.Chapter06.op A`. -/
structure NoBreakdown (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) :
    Prop where
  /-- Line 1 of Algorithm 7.1: $(v_1, w_1) = 1$. -/
  inner_start : inner 𝕜 w₁ v₁ = 1
  /-- The test of line 7 of Algorithm 7.1 passes in each of the first $m$ steps. -/
  inner_hat_ne_zero : ∀ j < m,
    inner 𝕜 (bilanczosWhat A v₁ w₁ j) (bilanczosVhat A v₁ w₁ j) ≠ 0

/-- **Section 7.1.2** of [saad2003iterative], the absence of serious breakdown. Algorithm 7.1 has
**no serious breakdown** if, at every step $j$, $(\hat v_{j+1}, \hat w_{j+1}) = 0$ implies
$\hat v_{j+1} = 0$: whenever line 7 stops the algorithm, the primal recurrence has already
terminated.

This holds generically and at a regular termination. Unlike `SaadSparse.Chapter07.NoBreakdown`,
it is a hypothesis about every step. This is what (7.3) needs: at a serious breakdown there is
no $v_{m+1}$ along which to expand $Av_m$, and the relation is false. -/
structure NoSeriousBreakdown (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) : Prop where
  /-- If $(\hat v_{j+1}, \hat w_{j+1}) = 0$, then $\hat v_{j+1} = 0$. -/
  vhat_eq_zero : ∀ j, inner 𝕜 (bilanczosWhat A v₁ w₁ j) (bilanczosVhat A v₁ w₁ j) = 0 →
    bilanczosVhat A v₁ w₁ j = 0

/-- $x \mapsto A^H x$ is the adjoint of $x \mapsto Ax$: $(Ax, y) = (x, A^H y)$ for all $x$, $y$. -/
theorem inner_op_conjTranspose (A : Matrix (Fin n) (Fin n) 𝕜)
    (x y : EuclideanSpace 𝕜 (Fin n)) : inner 𝕜 (op A x) y = inner 𝕜 x (op Aᴴ y) :=
  (Matrix.toEuclideanLin_conjTranspose_inner_right A x y).symm

private theorem zeta_eq (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ w₁ : EuclideanSpace 𝕜 (Fin n))
    (j : ℕ) : inner 𝕜 (bilanczosWhat A v₁ w₁ j) (bilanczosVhat A v₁ w₁ j)
      = BiLanczos.zeta (op A) (op Aᴴ) v₁ w₁ j := by
  rw [bilanczosWhat_eq, bilanczosVhat_eq, BiLanczos.zeta]

/-- If Algorithm 7.1 runs $m$ steps without breakdown and $k \le m$, it runs $k$ steps without
breakdown. -/
theorem NoBreakdown.mono {m k : ℕ} (h : NoBreakdown A v₁ w₁ m) (hk : k ≤ m) :
    NoBreakdown A v₁ w₁ k :=
  ⟨h.inner_start, fun j hj => h.inner_hat_ne_zero j (hj.trans_le hk)⟩

/-- The surface no-breakdown hypothesis implies the backbone hypothesis `BiLanczos.NoBreakdown`. -/
theorem NoBreakdown.toBiLanczos {m : ℕ} (h : NoBreakdown A v₁ w₁ m) :
    BiLanczos.NoBreakdown (op A) (op Aᴴ) v₁ w₁ m where
  adjoint := LinearMap.isAdjointPair_inner_iff'.2 (inner_op_conjTranspose A)
  inner_start := h.inner_start
  delta_ne_zero j hj := by
    rw [← bilanczosDelta_eq]
    intro hc
    refine h.inner_hat_ne_zero j hj ?_
    rw [zeta_eq, ← BiLanczos.delta_succ_eq_zero_iff, ← bilanczosDelta_eq]
    exact hc

/-- The backbone hypothesis `BiLanczos.NoSeriousBreakdown` implies the surface one. -/
theorem NoSeriousBreakdown.ofBiLanczos
    (h : BiLanczos.NoSeriousBreakdown (op A) (op Aᴴ) v₁ w₁) : NoSeriousBreakdown A v₁ w₁ where
  vhat_eq_zero j hj := by
    rw [bilanczosVhat_eq]
    exact h.vhat_eq_zero j
      ((BiLanczos.delta_succ_eq_zero_iff _ _ _ _ j).2 (zeta_eq A v₁ w₁ j ▸ hj))

/-- The surface no-serious-breakdown hypothesis implies the backbone hypothesis
`BiLanczos.NoSeriousBreakdown`. -/
theorem NoSeriousBreakdown.toBiLanczos (h : NoSeriousBreakdown A v₁ w₁) :
    BiLanczos.NoSeriousBreakdown (op A) (op Aᴴ) v₁ w₁ where
  vhat_eq_zero j hj := by
    rw [← bilanczosVhat_eq]
    refine h.vhat_eq_zero j ?_
    rw [zeta_eq, ← BiLanczos.delta_succ_eq_zero_iff, ← bilanczosDelta_eq, bilanczosDelta_eq]
    exact hj

/-- If Algorithm 7.1 runs $m$ steps without breakdown, then $\delta_{j+1} \neq 0$ for
$1 \le j \le m$. -/
theorem bilanczosDelta_ne_zero {m : ℕ} (h : NoBreakdown A v₁ w₁ m) {j : ℕ} (hj : j < m) :
    bilanczosDelta A v₁ w₁ (j + 1) ≠ 0 := by
  rw [bilanczosDelta_eq]
  exact h.toBiLanczos.delta_ne_zero j hj

end Breakdown

/-! ### Equations (7.2) and (7.15): the matrices $V_m$, $W_m$, $T_m$ and $\bar T_m$ -/

section Matrices

variable (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ w₁ : EuclideanSpace 𝕜 (Fin n))

/-- **Equation (7.2)** of [saad2003iterative], the entries of the tridiagonal matrix: $\alpha_j$ on
the diagonal, $\beta_{j+1}$ in position $(j, j+1)$, $\delta_{j+1}$ in position $(j+1, j)$, and
$0$ elsewhere.

The indices are $0$-based: `SaadSparse.Chapter07.bilanczosCoeff A v₁ w₁ i j` is the entry in row
$i + 1$ and column $j + 1$ of the book. -/
noncomputable def bilanczosCoeff (i j : ℕ) : 𝕜 :=
  if i = j then bilanczosAlpha A v₁ w₁ i
  else if i = j + 1 then bilanczosDelta A v₁ w₁ i
  else if j = i + 1 then bilanczosBeta A v₁ w₁ j
  else 0

/-- The tridiagonal coefficients are the backbone `BiLanczos.coeff`. -/
theorem bilanczosCoeff_eq (i j : ℕ) :
    bilanczosCoeff A v₁ w₁ i j = BiLanczos.coeff (op A) (op Aᴴ) v₁ w₁ i j := by
  rw [bilanczosCoeff, BiLanczos.coeff, bilanczosAlpha_eq, bilanczosDelta_eq, bilanczosBeta_eq]

/-- The diagonal entry in column $j$ is $\alpha_j$. -/
@[simp] theorem bilanczosCoeff_self (j : ℕ) :
    bilanczosCoeff A v₁ w₁ j j = bilanczosAlpha A v₁ w₁ j := by
  rw [bilanczosCoeff, ite_eq_left rfl]

/-- The subdiagonal entry in column $j$ is $\delta_{j+1}$. -/
@[simp] theorem bilanczosCoeff_succ_self (j : ℕ) :
    bilanczosCoeff A v₁ w₁ (j + 1) j = bilanczosDelta A v₁ w₁ (j + 1) := by
  rw [bilanczosCoeff, ite_eq_right (by omega), ite_eq_left rfl]

/-- The superdiagonal entry in row $j$ is $\beta_{j+1}$. -/
@[simp] theorem bilanczosCoeff_self_succ (j : ℕ) :
    bilanczosCoeff A v₁ w₁ j (j + 1) = bilanczosBeta A v₁ w₁ (j + 1) := by
  rw [bilanczosCoeff, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

/-- The tridiagonal coefficients vanish off the three diagonals. -/
theorem bilanczosCoeff_eq_zero {i j : ℕ} (h₁ : i ≠ j) (h₂ : i ≠ j + 1) (h₃ : j ≠ i + 1) :
    bilanczosCoeff A v₁ w₁ i j = 0 := by
  rw [bilanczosCoeff, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃]

/-- The tridiagonal coefficients vanish below the subdiagonal, so the array is upper Hessenberg. -/
theorem bilanczosCoeff_eq_zero_of_lt {i j : ℕ} (h : j + 1 < i) : bilanczosCoeff A v₁ w₁ i j = 0 :=
  bilanczosCoeff_eq_zero A v₁ w₁ (by omega) (by omega) (by omega)

/-- **Equation (7.2)** of [saad2003iterative]. The $m \times m$ tridiagonal matrix
$$T_m = \begin{bmatrix} \alpha_1 & \beta_2 & & \\ \delta_2 & \alpha_2 & \ddots & \\ & \ddots &
  \ddots & \beta_m \\ & & \delta_m & \alpha_m \end{bmatrix}$$
of the Lanczos biorthogonalization procedure. -/
noncomputable def T (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜 :=
  Matrix.of fun i j => bilanczosCoeff A v₁ w₁ i j

/-- **Equation (7.15)** of [saad2003iterative]. The $(m + 1) \times m$ matrix $\bar T_m$: the matrix
$T_m$ with the row $\delta_{m+1} e_m^T$ appended. -/
noncomputable def Tbar (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) 𝕜 :=
  Matrix.of fun i j => bilanczosCoeff A v₁ w₁ i j

/-- **Section 7.1** of [saad2003iterative]. The $n \times m$ matrix $V_m = [v_1, \dots, v_m]$ whose
columns are the primal Lanczos vectors. -/
noncomputable def V (m : ℕ) : Matrix (Fin n) (Fin m) 𝕜 := Chapter06.colMatrix (bilanczosV A v₁ w₁) m

/-- **Section 7.1** of [saad2003iterative]. The $n \times m$ matrix $W_m = [w_1, \dots, w_m]$ whose
columns are the dual Lanczos vectors. -/
noncomputable def W (m : ℕ) : Matrix (Fin n) (Fin m) 𝕜 := Chapter06.colMatrix (bilanczosW A v₁ w₁) m

/-- The entries of $T_m$ are the tridiagonal coefficients. -/
@[simp] theorem T_apply {m : ℕ} (i j : Fin m) : T A v₁ w₁ m i j = bilanczosCoeff A v₁ w₁ i j := rfl

/-- The entries of $\bar T_m$ are the tridiagonal coefficients. -/
@[simp] theorem Tbar_apply {m : ℕ} (i : Fin (m + 1)) (j : Fin m) :
    Tbar A v₁ w₁ m i j = bilanczosCoeff A v₁ w₁ i j := rfl

/-- The columns of $V_m$ are the primal Lanczos vectors. -/
@[simp] theorem V_apply {m : ℕ} (i : Fin n) (j : Fin m) :
    V A v₁ w₁ m i j = bilanczosV A v₁ w₁ (j : ℕ) i := rfl

/-- The columns of $W_m$ are the dual Lanczos vectors. -/
@[simp] theorem W_apply {m : ℕ} (i : Fin n) (j : Fin m) :
    W A v₁ w₁ m i j = bilanczosW A v₁ w₁ (j : ℕ) i := rfl

/-- $\bar T_m$ is the backbone Hessenberg matrix `Krylov.hessenbergOf` of the tridiagonal
coefficients. -/
theorem Tbar_eq_hessenbergOf (m : ℕ) :
    Tbar A v₁ w₁ m = Krylov.hessenbergOf (bilanczosCoeff A v₁ w₁) m := rfl

/-- $T_m$ is the backbone square Hessenberg matrix `Krylov.hessenbergSqOf` of the tridiagonal
coefficients. -/
theorem T_eq_hessenbergSqOf (m : ℕ) :
    T A v₁ w₁ m = Krylov.hessenbergSqOf (bilanczosCoeff A v₁ w₁) m := rfl

end Matrices

/-! ### Proposition 7.1 -/

section Proposition

variable {A : Matrix (Fin n) (Fin n) 𝕜} {v₁ w₁ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}

/-- **Proposition 7.1** of [saad2003iterative]. If Algorithm 7.1 runs $m$ steps without breakdown,
then the two families are biorthogonal:
$$(v_j, w_i) = \delta_{ij} \qquad \text{for } 1 \le i, j \le m + 1.$$

In Mathlib's notation $(v_j, w_i)$ is `inner 𝕜 (bilanczosW A v₁ w₁ i) (bilanczosV A v₁ w₁ j)`,
with $0$-based indices. -/
theorem proposition_7_1 (h : NoBreakdown A v₁ w₁ m) {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) :
    inner 𝕜 (bilanczosW A v₁ w₁ i) (bilanczosV A v₁ w₁ j) = if i = j then 1 else 0 := by
  rw [bilanczosW_eq, bilanczosV_eq]
  exact BiLanczos.inner_dualVec_vec h.toBiLanczos hi hj

/-- **Proposition 7.1** of [saad2003iterative], with the arguments exchanged. If Algorithm 7.1 runs
$m$ steps without breakdown, then $(w_j, v_i) = \delta_{ij}$ for $1 \le i, j \le m + 1$. -/
theorem proposition_7_1' (h : NoBreakdown A v₁ w₁ m) {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) :
    inner 𝕜 (bilanczosV A v₁ w₁ i) (bilanczosW A v₁ w₁ j) = if i = j then 1 else 0 := by
  rw [bilanczosW_eq, bilanczosV_eq]
  exact BiLanczos.inner_vec_dualVec h.toBiLanczos hi hj

private theorem range_fin_eq_image_Iio {α : Type*} (f : ℕ → α) (k : ℕ) :
    Set.range (fun i : Fin k => f (i : ℕ)) = f '' Set.Iio k := by
  ext z
  simp only [Set.mem_range, Set.mem_image, Set.mem_Iio]
  exact ⟨fun ⟨i, hi⟩ => ⟨(i : ℕ), i.2, hi⟩, fun ⟨i, hi, hz⟩ => ⟨⟨i, hi⟩, hz⟩⟩

/-- **Proposition 7.1** of [saad2003iterative], the spans. If Algorithm 7.1 runs $m$ steps without
breakdown, then $\{v_1, \dots, v_m\}$ spans $\mathcal{K}_m(A, v_1)$ and $\{w_1, \dots, w_m\}$
spans $\mathcal{K}_m(A^H, w_1)$.

With `SaadSparse.Chapter07.problem_7_2` these are bases. This is the full-rank hypothesis that
Theorem 7.4 therefore does not need to assume. -/
theorem proposition_7_1_span (h : NoBreakdown A v₁ w₁ m) :
    Submodule.span 𝕜 (Set.range fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
        = Chapter06.krylov A v₁ m ∧
      Submodule.span 𝕜 (Set.range fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ))
        = Chapter06.krylov Aᴴ w₁ m := by
  constructor
  · rw [range_fin_eq_image_Iio, Chapter06.krylov_eq,
      show (bilanczosV A v₁ w₁) = BiLanczos.vec (op A) (op Aᴴ) v₁ w₁ from
        funext (bilanczosV_eq A v₁ w₁)]
    exact BiLanczos.span_vec h.toBiLanczos
  · rw [range_fin_eq_image_Iio, Chapter06.krylov_eq,
      show (bilanczosW A v₁ w₁) = BiLanczos.dualVec (op A) (op Aᴴ) v₁ w₁ from
        funext (bilanczosW_eq A v₁ w₁)]
    exact BiLanczos.span_dualVec h.toBiLanczos

/-- A family biorthogonal to another is linearly independent: Mathlib's
`LinearIndependent.of_pairwise_dual_eq_zero_one` at the dual functionals `⟪w_i, ·⟫`. -/
private theorem linearIndependent_of_biorthogonal {k : ℕ}
    (v w : Fin k → EuclideanSpace 𝕜 (Fin n))
    (h0 : ∀ i j, i ≠ j → inner 𝕜 (w i) (v j) = (0 : 𝕜))
    (h1 : ∀ i, inner 𝕜 (w i) (v i) = (1 : 𝕜)) :
    LinearIndependent 𝕜 v :=
  LinearIndependent.of_pairwise_dual_eq_zero_one v (fun i => (innerSL 𝕜 (w i)).toLinearMap)
    (fun i j hij => by simpa using h0 i j hij) fun i => by simpa using h1 i

/-- **Exercise P-7.2** of [saad2003iterative]. If Algorithm 7.1 runs $m$ steps without breakdown,
then the vectors $v_1, \dots, v_m$, the columns of $V_m$, are linearly independent, and so are
the vectors $w_1, \dots, w_m$, the columns of $W_m$.

This follows from the biorthogonality of Proposition 7.1. -/
theorem problem_7_2 (h : NoBreakdown A v₁ w₁ m) :
    LinearIndependent 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ)) ∧
      LinearIndependent 𝕜 (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ)) :=
  ⟨linearIndependent_of_biorthogonal _ _
      (fun i j hij => by
        rw [proposition_7_1 h (le_of_lt i.2) (le_of_lt j.2),
          ite_eq_right (fun hc => hij (Fin.ext hc))])
      fun i => by rw [proposition_7_1 h (le_of_lt i.2) (le_of_lt i.2), ite_eq_left rfl],
    linearIndependent_of_biorthogonal _ _
      (fun i j hij => by
        rw [proposition_7_1' h (le_of_lt i.2) (le_of_lt j.2),
          ite_eq_right (fun hc => hij (Fin.ext hc))])
      fun i => by rw [proposition_7_1' h (le_of_lt i.2) (le_of_lt i.2), ite_eq_left rfl]⟩

end Proposition

/-! ### (7.3)–(7.5) and (7.15): the matrix relations -/

section Relations

/-- In column $j$, the terms of the tridiagonal coefficients above the diagonal reduce to the single
term $\beta_j v_{j-1}$. -/
private theorem sum_bilanczosCoeff_lt (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    ∑ i ∈ Finset.range j, bilanczosCoeff A v₁ w₁ i j • bilanczosV A v₁ w₁ i
      = bilanczosBeta A v₁ w₁ j • bilanczosVPrev A v₁ w₁ j := by
  cases j with
  | zero => simp
  | succ k =>
    have hz : ∑ i ∈ Finset.range k, bilanczosCoeff A v₁ w₁ i (k + 1) • bilanczosV A v₁ w₁ i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have hik : i < k := Finset.mem_range.1 hi
        rw [bilanczosCoeff_eq_zero A v₁ w₁ (by omega) (by omega) (by omega), zero_smul]
    rw [Finset.sum_range_succ, hz, zero_add, bilanczosCoeff_self_succ, bilanczosVPrev_succ]

/-- The dual form of the previous statement: the terms reduce to the single term
$\bar\delta_j w_{j-1}$. -/
private theorem sum_dualCoeff_lt (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    ∑ i ∈ Finset.range j, starRingEnd 𝕜 (bilanczosCoeff A v₁ w₁ j i) • bilanczosW A v₁ w₁ i
      = starRingEnd 𝕜 (bilanczosDelta A v₁ w₁ j) • bilanczosWPrev A v₁ w₁ j := by
  cases j with
  | zero => simp
  | succ k =>
    have hz : ∑ i ∈ Finset.range k,
        starRingEnd 𝕜 (bilanczosCoeff A v₁ w₁ (k + 1) i) • bilanczosW A v₁ w₁ i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have hik : i < k := Finset.mem_range.1 hi
        rw [bilanczosCoeff_eq_zero A v₁ w₁ (by omega) (by omega) (by omega), map_zero, zero_smul]
    rw [Finset.sum_range_succ, hz, zero_add, bilanczosCoeff_succ_self, bilanczosWPrev_succ]

variable {A : Matrix (Fin n) (Fin n) 𝕜} {v₁ w₁ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}

/-- Equation (7.3) column by column: if the first $m$ steps run without breakdown and $j \le m$,
then $Av_j = \sum_{i \le j+1} t_{ij} v_i$. -/
private theorem apply_bilanczosV_sum (h : NoBreakdown A v₁ w₁ m) {j : ℕ} (hj : j < m) :
    op A (bilanczosV A v₁ w₁ j)
      = ∑ i ∈ Finset.range (j + 2), bilanczosCoeff A v₁ w₁ i j • bilanczosV A v₁ w₁ i := by
  rw [show j + 2 = j + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    sum_bilanczosCoeff_lt, bilanczosCoeff_self, bilanczosCoeff_succ_self]
  simp only [bilanczosV_eq, bilanczosVPrev_eq, bilanczosAlpha_eq, bilanczosBeta_eq,
    bilanczosDelta_eq]
  exact BiLanczos.apply_vec _ _ _ _ (h.toBiLanczos.delta_ne_zero j hj)

/-- Equation (7.4) column by column: if the first $m$ steps run without breakdown and $j \le m$,
then $A^H w_j = \sum_{i \le j+1} \bar t_{ji} w_i$. -/
private theorem apply_bilanczosW_sum (h : NoBreakdown A v₁ w₁ m) {j : ℕ} (hj : j < m) :
    op Aᴴ (bilanczosW A v₁ w₁ j) = ∑ i ∈ Finset.range (j + 2),
      starRingEnd 𝕜 (bilanczosCoeff A v₁ w₁ j i) • bilanczosW A v₁ w₁ i := by
  rw [show j + 2 = j + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    sum_dualCoeff_lt, bilanczosCoeff_self, bilanczosCoeff_self_succ]
  simp only [bilanczosW_eq, bilanczosWPrev_eq, bilanczosAlpha_eq, bilanczosBeta_eq,
    bilanczosDelta_eq]
  exact BiLanczos.apply_dualVec _ _ _ _ (h.toBiLanczos.delta_ne_zero j hj)

/-- **Section 7.1** of [saad2003iterative], the Hessenberg relation. If Algorithm 7.1 has no serious
breakdown, then for every $j$
$$Av_j = \sum_{i \le j+1} t_{ij} v_i,$$
where $t_{ij}$ are the tridiagonal coefficients of (7.2), which vanish for $i > j + 1$.

This is the backbone `Krylov.HessenbergRelation`. So the residual formula of
`Numlib.Krylov.Hessenberg`, and the quasi-minimal-residual results built on it, apply to the
two-sided Lanczos basis, which is biorthogonal rather than orthonormal. This is the basis of
Sections 7.2 and 7.3. -/
theorem bilanczos_hessenbergRelation (h : NoSeriousBreakdown A v₁ w₁) :
    Krylov.HessenbergRelation (op A) (bilanczosV A v₁ w₁) (bilanczosCoeff A v₁ w₁) := by
  have hv : bilanczosV A v₁ w₁ = BiLanczos.vec (op A) (op Aᴴ) v₁ w₁ :=
    funext (bilanczosV_eq A v₁ w₁)
  have hc : bilanczosCoeff A v₁ w₁ = BiLanczos.coeff (op A) (op Aᴴ) v₁ w₁ :=
    funext fun i => funext fun j => bilanczosCoeff_eq A v₁ w₁ i j
  rw [hv, hc]
  exact BiLanczos.hessenbergRelation h.toBiLanczos

/-! ### Two matrix forms of a truncated Hessenberg recurrence -/

private theorem sum_coord {ι : Type*} (s : Finset ι) (f : ι → EuclideanSpace 𝕜 (Fin n))
    (i : Fin n) : (∑ k ∈ s, f k) i = ∑ k ∈ s, f k i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

/-- If $Bu_j = \sum_{i \le j+1} c_{ij} u_i$ for $j < k$, with $c$ upper Hessenberg, then
$BU_k = U_{k+1} \bar H_k$. -/
private theorem mul_colMatrix_eq_of_apply {B : Matrix (Fin n) (Fin n) 𝕜}
    {u : ℕ → EuclideanSpace 𝕜 (Fin n)} {c : ℕ → ℕ → 𝕜} {k : ℕ}
    (happ : ∀ j < k, op B (u j) = ∑ i ∈ Finset.range (j + 2), c i j • u i)
    (hz : ∀ i j, j + 1 < i → c i j = 0) :
    B * Chapter06.colMatrix u k = Chapter06.colMatrix u (k + 1) * Krylov.hessenbergOf c k := by
  ext i j
  have hj : (j : ℕ) < k := j.2
  have hrange : op B (u (j : ℕ)) = ∑ l ∈ Finset.range (k + 1), c l (j : ℕ) • u l := by
    rw [happ (j : ℕ) hj]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun l _ hl => ?_
    rw [Finset.mem_range, not_lt] at hl
    rw [hz l (j : ℕ) (by omega), zero_smul]
  rw [Chapter06.mul_colMatrix_apply, hrange, sum_coord, Matrix.mul_apply,
    ← Fin.sum_univ_eq_sum_range (fun l => (c l (j : ℕ) • u l) i) (k + 1)]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- If $Bu_j = \sum_{i \le j+1} c_{ij} u_i$ for $j \le k$, with $c$ upper Hessenberg, then
$BU_{k+1} = U_{k+1} H_{k+1} + c_{k+2,k+1} u_{k+2} e_{k+1}^T$. -/
private theorem mul_colMatrix_eq_add_vecMulVec {B : Matrix (Fin n) (Fin n) 𝕜}
    {u : ℕ → EuclideanSpace 𝕜 (Fin n)} {c : ℕ → ℕ → 𝕜} {k : ℕ}
    (happ : ∀ j < k + 1, op B (u j) = ∑ i ∈ Finset.range (j + 2), c i j • u i)
    (hz : ∀ i j, j + 1 < i → c i j = 0) :
    B * Chapter06.colMatrix u (k + 1) =
      Chapter06.colMatrix u (k + 1) * Krylov.hessenbergSqOf c (k + 1)
      + Matrix.vecMulVec (WithLp.ofLp (c (k + 1) k • u (k + 1)))
          (Pi.single (M := fun _ : Fin (k + 1) => 𝕜) (Fin.last k) 1) := by
  have hlast : ∀ j : Fin (k + 1), c (k + 1) (j : ℕ) • u (k + 1)
      = (Pi.single (M := fun _ : Fin (k + 1) => 𝕜) (Fin.last k) 1 j)
        • (c (k + 1) k • u (k + 1)) := by
    intro j
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 j.2) with hj | hj
    · have hjl : j = Fin.last k := Fin.ext (by simpa using hj)
      rw [hjl, Fin.val_last, Pi.single_eq_same, one_smul]
    · have hne : (j : ℕ) ≠ k := by omega
      rw [hz (k + 1) (j : ℕ) (by omega), zero_smul]
      simp [Fin.ext_iff, hne]
  ext i j
  have hj : (j : ℕ) < k + 1 := j.2
  have hrange : op B (u (j : ℕ)) = ∑ l ∈ Finset.range (k + 2), c l (j : ℕ) • u l := by
    rw [happ (j : ℕ) hj]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun l _ hl => ?_
    rw [Finset.mem_range, not_lt] at hl
    rw [hz l (j : ℕ) (by omega), zero_smul]
  rw [Chapter06.mul_colMatrix_apply, hrange, Finset.sum_range_succ, hlast j, PiLp.add_apply,
    sum_coord, Matrix.add_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    ← Fin.sum_univ_eq_sum_range (fun l => (c l (j : ℕ) • u l) i) (k + 1)]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun l _ => mul_comm _ _) ?_
  rw [PiLp.smul_apply, smul_eq_mul, mul_comm]

/-! ### Equations (7.3), (7.4) and (7.15) -/

private theorem dualCoeff_eq_zero_of_lt (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) {i j : ℕ} (hij : j + 1 < i) :
    starRingEnd 𝕜 (bilanczosCoeff A v₁ w₁ j i) = 0 := by
  rw [bilanczosCoeff_eq_zero A v₁ w₁ (by omega) (by omega) (by omega), map_zero]

private theorem hessenbergSqOf_dual (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) :
    Krylov.hessenbergSqOf (fun i j => starRingEnd 𝕜 (bilanczosCoeff A v₁ w₁ j i)) k
      = (T A v₁ w₁ k)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply, T_apply]
  rfl

/-- **Equations (7.3), (7.4) and (7.15)** of [saad2003iterative]. Let $k \ge 1$, and assume that
Algorithm 7.1 runs $k$ steps without breakdown. Then
$$AV_k = V_k T_k + \delta_{k+1} v_{k+1} e_k^T, \qquad A^H W_k = W_k T_k^H + \bar\beta_{k+1}
  w_{k+1} e_k^T,$$
and, with $m = k - 1$, $AV_m = V_{m+1} \bar T_m$.

The last identity is the extended form (7.15), on which Chapter 7 runs QMR. In the Lean
statement $k = m + 1$. -/
theorem equation_7_3 (h : NoBreakdown A v₁ w₁ (m + 1)) :
    A * V A v₁ w₁ (m + 1) = V A v₁ w₁ (m + 1) * T A v₁ w₁ (m + 1)
        + Matrix.vecMulVec
            (WithLp.ofLp (bilanczosDelta A v₁ w₁ (m + 1) • bilanczosV A v₁ w₁ (m + 1)))
            (Pi.single (M := fun _ : Fin (m + 1) => 𝕜) (Fin.last m) 1) ∧
      Aᴴ * W A v₁ w₁ (m + 1) = W A v₁ w₁ (m + 1) * (T A v₁ w₁ (m + 1))ᴴ
        + Matrix.vecMulVec
            (WithLp.ofLp (starRingEnd 𝕜 (bilanczosBeta A v₁ w₁ (m + 1))
              • bilanczosW A v₁ w₁ (m + 1)))
            (Pi.single (M := fun _ : Fin (m + 1) => 𝕜) (Fin.last m) 1) ∧
      A * V A v₁ w₁ m = V A v₁ w₁ (m + 1) * Tbar A v₁ w₁ m := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← bilanczosCoeff_succ_self A v₁ w₁ m]
    exact mul_colMatrix_eq_add_vecMulVec (fun j hj => apply_bilanczosV_sum h hj)
      (fun i j hij => bilanczosCoeff_eq_zero_of_lt A v₁ w₁ hij)
  · rw [← hessenbergSqOf_dual A v₁ w₁ (m + 1),
      ← bilanczosCoeff_self_succ A v₁ w₁ m]
    exact mul_colMatrix_eq_add_vecMulVec (fun j hj => apply_bilanczosW_sum h hj)
      (fun i j hij => dualCoeff_eq_zero_of_lt A v₁ w₁ hij)
  · exact mul_colMatrix_eq_of_apply (fun j hj => apply_bilanczosV_sum h (by omega))
      (fun i j hij => bilanczosCoeff_eq_zero_of_lt A v₁ w₁ hij)

private theorem mul_V_apply (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ w₁ : EuclideanSpace 𝕜 (Fin n))
    {k : ℕ} (i : Fin n) (j : Fin k) :
    (A * V A v₁ w₁ k) i j = op A (bilanczosV A v₁ w₁ (j : ℕ)) i :=
  Chapter06.mul_colMatrix_apply A _ i j

/-- **Equation (7.5)** of [saad2003iterative]. If Algorithm 7.1 runs $m$ steps without breakdown,
then
$$W_m^H A V_m = T_m \quad\text{and}\quad V_m^H A^H W_m = T_m^H.$$
So $T_m$ is the compression of $A$ to $\mathcal{K}_m(A, v_1)$ along $\mathcal{K}_m(A^H, w_1)$,
and $T_m^H$ compresses $A^H$ the other way. -/
theorem equation_7_5 (h : NoBreakdown A v₁ w₁ m) :
    (W A v₁ w₁ m)ᴴ * A * V A v₁ w₁ m = T A v₁ w₁ m ∧
      (V A v₁ w₁ m)ᴴ * Aᴴ * W A v₁ w₁ m = (T A v₁ w₁ m)ᴴ := by
  have hmain : (W A v₁ w₁ m)ᴴ * A * V A v₁ w₁ m = T A v₁ w₁ m := by
    cases m with
    | zero => ext i j; exact i.elim0
    | succ M =>
      have hcoeff : ∀ i j : Fin (M + 1),
          inner 𝕜 (bilanczosW A v₁ w₁ (i : ℕ)) (op A (bilanczosV A v₁ w₁ (j : ℕ)))
            = bilanczosCoeff A v₁ w₁ i j := by
        intro i j
        rw [bilanczosW_eq, bilanczosV_eq, bilanczosCoeff_eq]
        exact BiLanczos.inner_dualVec_apply_vec h.toBiLanczos (by omega) (by omega)
      ext i j
      rw [Matrix.mul_assoc, Matrix.mul_apply, T_apply, ← hcoeff i j, PiLp.inner_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_apply, W_apply, mul_V_apply, RCLike.inner_apply, mul_comm]
      rfl
  refine ⟨hmain, ?_⟩
  have hT := congrArg Matrix.conjTranspose hmain
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    ← Matrix.mul_assoc] at hT

end Relations

/-! ### Exercise P-7.6: the oblique projector $V_m W_m^H$ -/

section Projector

variable {A : Matrix (Fin n) (Fin n) 𝕜} {v₁ w₁ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}

/-- If Algorithm 7.1 runs $m$ steps without breakdown, then the cross Gram matrix $W_m^H V_m$ of the
two Lanczos bases is the identity. This is Proposition 7.1 as a matrix identity. -/
theorem crossGram_eq_one (h : NoBreakdown A v₁ w₁ m) :
    LinearMap.crossGram 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
        (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ)) = 1 := by
  ext i j
  rw [LinearMap.crossGram, Matrix.of_apply, proposition_7_1 h (le_of_lt i.2) (le_of_lt j.2)]
  simp [Matrix.one_apply, Fin.val_inj]

private theorem toEuclideanLin_conjTranspose_W_apply (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    Matrix.toEuclideanLin (W A v₁ w₁ k)ᴴ x
      = WithLp.toLp 2 (fun j : Fin k => inner 𝕜 (bilanczosW A v₁ w₁ (j : ℕ)) x) := by
  refine WithLp.ofLp_injective 2 (funext fun j => ?_)
  change ((W A v₁ w₁ k)ᴴ *ᵥ WithLp.ofLp x) j = inner 𝕜 (bilanczosW A v₁ w₁ (j : ℕ)) x
  rw [Matrix.mulVec_apply_eq_sum, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.conjTranspose_apply, W_apply, RCLike.inner_apply, mul_comm]
  rfl

/-- $V_m W_m^H x = \sum_j (x, w_j) v_j$: the coordinate form of the projector. -/
private theorem toEuclideanLin_V_mul_conjTranspose_W (A : Matrix (Fin n) (Fin n) 𝕜)
    (v₁ w₁ : EuclideanSpace 𝕜 (Fin n)) (k : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    Matrix.toEuclideanLin (V A v₁ w₁ k * (W A v₁ w₁ k)ᴴ) x
      = ∑ j : Fin k, inner 𝕜 (bilanczosW A v₁ w₁ (j : ℕ)) x • bilanczosV A v₁ w₁ (j : ℕ) := by
  rw [show Matrix.toEuclideanLin (V A v₁ w₁ k * (W A v₁ w₁ k)ᴴ)
      = Matrix.toEuclideanLin (V A v₁ w₁ k) ∘ₗ Matrix.toEuclideanLin (W A v₁ w₁ k)ᴴ from
    Matrix.toLpLin_mul 2 2 2 _ _]
  rw [LinearMap.comp_apply, toEuclideanLin_conjTranspose_W_apply]
  exact Chapter06.toEuclideanLin_colMatrix_apply _ _

/-- **Exercise P-7.6(a)** of [saad2003iterative]. If Algorithm 7.1 runs $m$ steps without breakdown,
then $V_m W_m^H$ is the oblique projector onto $\mathcal{K}_m(A, v_1)$ orthogonally to
$\mathcal{K}_m(A^H, w_1)$: it is the projector `LinearMap.obliqueProjectionOfBases` of the two
bases, it is idempotent, its range is $\mathcal{K}_m(A, v_1)$, and its kernel is
$\mathcal{K}_m(A^H, w_1)^\perp$.

The general formula $V(W^H V)^{-1} W^H$ reduces to $V_m W_m^H$ because $W_m^H V_m = I$ by
Proposition 7.1. -/
theorem problem_7_6 (h : NoBreakdown A v₁ w₁ m) :
    Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ)
        = LinearMap.obliqueProjectionOfBases 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
            (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ)) ∧
      IsIdempotentElem (Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ)) ∧
      LinearMap.range (Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ))
          = Chapter06.krylov A v₁ m ∧
      LinearMap.ker (Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ))
          = (Chapter06.krylov Aᴴ w₁ m)ᗮ := by
  have hG := crossGram_eq_one h
  have hU : IsUnit (LinearMap.crossGram 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
      (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ))) := hG ▸ isUnit_one
  have hobl : ∀ x : EuclideanSpace 𝕜 (Fin n),
      LinearMap.obliqueProjectionOfBases 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
          (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ)) x
        = ∑ j : Fin m, inner 𝕜 (bilanczosW A v₁ w₁ (j : ℕ)) x • bilanczosV A v₁ w₁ (j : ℕ) := by
    intro x
    have hdef : LinearMap.obliqueProjectionOfBases 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
          (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ)) x
        = ∑ j, (LinearMap.crossGram 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
            (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ)))⁻¹.mulVec
            (fun i => inner 𝕜 (bilanczosW A v₁ w₁ (i : ℕ)) x) j • bilanczosV A v₁ w₁ (j : ℕ) :=
      rfl
    rw [hdef, hG, _root_.inv_one, Matrix.one_mulVec]
  have hP : Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ)
      = LinearMap.obliqueProjectionOfBases 𝕜 (fun i : Fin m => bilanczosV A v₁ w₁ (i : ℕ))
          (fun i : Fin m => bilanczosW A v₁ w₁ (i : ℕ)) :=
    LinearMap.ext fun x => by rw [toEuclideanLin_V_mul_conjTranspose_W, hobl]
  obtain ⟨hspanV, hspanW⟩ := proposition_7_1_span h
  refine ⟨hP, ?_, ?_, ?_⟩
  · rw [hP]
    exact LinearMap.obliqueProjectionOfBases_isIdempotentElem _ _ hU
  · rw [hP, LinearMap.range_obliqueProjectionOfBases _ _ hU, ← hspanV]
  · rw [hP, LinearMap.ker_obliqueProjectionOfBases _ _ hU, ← hspanW]

/-- **Exercise P-7.6(b)** of [saad2003iterative]. A projector onto $K$ along $L^\perp$ exists
exactly when $K \cap L^\perp = \{0\}$. If Algorithm 7.1 runs $m$ steps without breakdown, the
two Lanczos subspaces satisfy this condition:
$$\mathcal{K}_m(A, v_1) \cap \mathcal{K}_m(A^H, w_1)^\perp = \{0\}.$$
-/
theorem problem_7_6_inf_eq_bot (h : NoBreakdown A v₁ w₁ m) :
    Chapter06.krylov A v₁ m ⊓ (Chapter06.krylov Aᴴ w₁ m)ᗮ = ⊥ := by
  obtain ⟨-, hidem, hran, hker⟩ := problem_7_6 h
  refine Submodule.eq_bot_iff _ |>.2 fun x hx => ?_
  obtain ⟨z, hz⟩ : x ∈ LinearMap.range (Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ)) := by
    rw [hran]; exact hx.1
  have hfix : Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ) x = x := by
    rw [← hz]
    exact DFunLike.congr_fun hidem z
  have hzero : Matrix.toEuclideanLin (V A v₁ w₁ m * (W A v₁ w₁ m)ᴴ) x = 0 := by
    rw [← LinearMap.mem_ker, hker]; exact hx.2
  rw [← hfix, hzero]

end Projector

/-! ### §7.1.2: the lucky breakdown -/

section LuckyBreakdown

variable {A : Matrix (Fin n) (Fin n) 𝕜} {v₁ w₁ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}

/-- **Section 7.1.2** of [saad2003iterative], a lucky breakdown is not a serious one. If Algorithm
7.1 runs $m$ steps without breakdown and the next unnormalized vector $\hat v_{m+2}$ is $0$,
then Algorithm 7.1 has no serious breakdown.

In the first $m$ steps the test of line 7 passes, and from then on every later $\hat v$ is $0$.
So everything that Sections 7.1–7.3 prove without serious breakdown, (7.3) included, holds after
a lucky breakdown; only the serious breakdown (7.6), where $\hat v_{j+1} \neq 0$ but
$(\hat v_{j+1}, \hat w_{j+1}) = 0$, is excluded. -/
theorem noSeriousBreakdown_of_bilanczosVhat_eq_zero (h : NoBreakdown A v₁ w₁ m)
    (hv : bilanczosVhat A v₁ w₁ m = 0) : NoSeriousBreakdown A v₁ w₁ :=
  NoSeriousBreakdown.ofBiLanczos
    (BiLanczos.NoSeriousBreakdown.of_vhat_eq_zero h.toBiLanczos
      (by rw [← bilanczosVhat_eq]; exact hv))

/-- **Section 7.1.2** of [saad2003iterative], a lucky breakdown gives an invariant subspace. If
Algorithm 7.1 runs $m$ steps without breakdown and the next unnormalized vector $\hat v_{m+2}$
is $0$, then $\mathcal{K}_{m+1}(A, v_1)$, the space spanned by $v_1, \dots, v_{m+1}$, is
invariant under $A$.

The last three-term relation has lost its term in $v_{m+2}$, so $Av_{m+1}$ lies in the span of
the earlier vectors. The iterate of Algorithm 7.2 is then exact; see
`SaadSparse.Chapter07.lanczosSolve_eq_of_bilanczosVhat_eq_zero`. -/
theorem krylov_mem_invtSubmodule_of_bilanczosVhat_eq_zero (h : NoBreakdown A v₁ w₁ m)
    (hv : bilanczosVhat A v₁ w₁ m = 0) :
    Chapter06.krylov A v₁ (m + 1) ∈ Module.End.invtSubmodule (op A) := by
  rw [Chapter06.krylov_eq]
  exact BiLanczos.subspace_succ_mem_invtSubmodule_of_vhat_eq_zero h.toBiLanczos
    (by rw [← bilanczosVhat_eq]; exact hv)

/-- **Section 7.1.2** of [saad2003iterative]. If Algorithm 7.1 runs $m$ steps without breakdown,
then the $m + 1$ vectors $v_1, \dots, v_{m+1}$ span $\mathcal{K}_{m+1}(A, v_1)$.

This is one Krylov subspace more than `SaadSparse.Chapter07.proposition_7_1_span` gives for $m$
steps, and it needs no hypothesis on step $m + 1$. It applies in particular at a lucky
breakdown, where the test of line 7 has just failed and Proposition 7.1 for $m + 1$ steps is not
available. -/
theorem span_bilanczosV_succ (h : NoBreakdown A v₁ w₁ m) :
    Submodule.span 𝕜 (Set.range fun i : Fin (m + 1) => bilanczosV A v₁ w₁ (i : ℕ))
      = Chapter06.krylov A v₁ (m + 1) := by
  rw [range_fin_eq_image_Iio, Chapter06.krylov_eq,
    show (bilanczosV A v₁ w₁) = BiLanczos.vec (op A) (op Aᴴ) v₁ w₁ from
      funext (bilanczosV_eq A v₁ w₁)]
  exact BiLanczos.span_vec_succ h.toBiLanczos

end LuckyBreakdown

/-! ### Section 7.1.2: equation (7.7), the formal orthogonal polynomials and the moment matrix -/

section OrthogonalPolynomials

open Polynomial

variable (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ w₁ : EuclideanSpace 𝕜 (Fin n))

/-- **Equation (7.7)** of [saad2003iterative]. The bilinear form on polynomials
$$\langle p, q \rangle = (p(A) v_1, q(A^T) w_1).$$

Over $\mathbb{C}$ the conjugation that the book's transpose hides is applied to the coefficients
of $q$: the form is $(p(A) v_1, \bar q(A^H) w_1)$, which keeps it bilinear. It is an indefinite
form, since $\langle p, p \rangle$ can vanish for a nonzero $p$, and this is exactly the serious
breakdown of Section 7.1.2 (`SaadSparse.Chapter07.breakdown_iff_polyForm_eq_zero`). This is the
backbone `BiLanczos.polyForm`. -/
noncomputable abbrev polyForm : 𝕜[X] → 𝕜[X] → 𝕜 := BiLanczos.polyForm (op A) (op Aᴴ) v₁ w₁

/-- **Section 7.1.2** of [saad2003iterative]. The polynomial $p_j$ with $\hat v_{j+1} = p_j(A) v_1$.

`SaadSparse.Chapter07.bilanczosPoly A v₁ w₁ j` is the book's $p_{j+1}$, of degree $j + 1$
without breakdown (`SaadSparse.Chapter07.bilanczosPoly_natDegree`). This is the backbone
`BiLanczos.vhatPoly`. -/
noncomputable abbrev bilanczosPoly : ℕ → 𝕜[X] := BiLanczos.vhatPoly (op A) (op Aᴴ) v₁ w₁

/-- **Section 7.1.2** of [saad2003iterative]. The $k \times k$ moment matrix $M_k = \{\langle
x^{i-1}, x^{j-1} \rangle\}_{i,j=1,\dots,k}$ of the form (7.7). -/
noncomputable abbrev momentMatrix (k : ℕ) : Matrix (Fin k) (Fin k) 𝕜 :=
  BiLanczos.momentMatrix (op A) (op Aᴴ) v₁ w₁ k

/-- **Section 7.1.2** of [saad2003iterative], existence of $p_j$. For every $j$,
$\hat v_{j+1} = p_j(A) v_1$.

This needs no hypothesis on breakdown. The degree of $p_j$ is
`SaadSparse.Chapter07.bilanczosPoly_natDegree`. -/
theorem bilanczosVhat_eq_aeval (j : ℕ) :
    bilanczosVhat A v₁ w₁ j = aeval (op A) (bilanczosPoly A v₁ w₁ j) v₁ := by
  rw [bilanczosVhat_eq, BiLanczos.aeval_vhatPoly]

/-- **Section 7.1.2** of [saad2003iterative]: "the same polynomial intervenes in the equivalent
expression of $\hat w_{j+1}$". For every $j$ there is a scalar $\gamma_j$ with
$$\hat w_{j+1} = \gamma_j\, \bar p_j(A^H) w_1,$$
where $\bar p_j$ has the conjugate coefficients of $p_j$.

The scalar is `BiLanczos.dualPolyScalar`. Over $\mathbb{R}$ the conjugation has no effect, and
this is the statement of the book. -/
theorem bilanczosWhat_eq_smul (j : ℕ) :
    bilanczosWhat A v₁ w₁ j = BiLanczos.dualPolyScalar (op A) (op Aᴴ) v₁ w₁ j •
      aeval (op Aᴴ) ((bilanczosPoly A v₁ w₁ j).map (starRingEnd 𝕜)) w₁ := by
  rw [bilanczosWhat_eq, BiLanczos.dualVhat_eq_smul]

/-- **Section 7.1.2** of [saad2003iterative]. The form (7.7) is a moment functional: for all
polynomials $p$ and $q$,
$$\langle p, q \rangle = L(pq), \qquad L(r) = (r(A) v_1, w_1).$$

The symmetry of the form and the Hankel structure of the moment matrix both follow from this
identity. The functional $L$ is `BiLanczos.moment`. -/
theorem polyForm_eq_moment (p q : 𝕜[X]) :
    polyForm A v₁ w₁ p q = BiLanczos.moment (op A) v₁ w₁ (p * q) :=
  BiLanczos.polyForm_eq_moment (LinearMap.isAdjointPair_inner_iff'.2 (inner_op_conjTranspose A))
    p q

/-- **Section 7.1.2** of [saad2003iterative]: "$M_k$ is a Hankel matrix, i.e., its coefficients
$m_{ij}$ are constant along anti-diagonals". For indices with $i + j = i' + j'$, the entries of
the moment matrix satisfy $m_{ij} = m_{i'j'}$. -/
theorem momentMatrix_apply_eq_of_add_eq {k : ℕ} {i j i' j' : Fin k}
    (hij : (i : ℕ) + (j : ℕ) = (i' : ℕ) + (j' : ℕ)) :
    momentMatrix A v₁ w₁ k i j = momentMatrix A v₁ w₁ k i' j' :=
  BiLanczos.momentMatrix_apply_eq_of_add_eq
    (LinearMap.isAdjointPair_inner_iff'.2 (inner_op_conjTranspose A)) hij

variable {A v₁ w₁}

/-- **Section 7.1.2** of [saad2003iterative], the degree of $p_j$. If Algorithm 7.1 runs $m$ steps
without breakdown, then $p_j$ has degree exactly $j$ for $1 \le j \le m + 1$.

In the $0$-based Lean statement, `SaadSparse.Chapter07.bilanczosPoly A v₁ w₁ j` has degree
$j + 1$ for $j \le m$. -/
theorem bilanczosPoly_natDegree {m : ℕ} (h : NoBreakdown A v₁ w₁ m) {j : ℕ} (hj : j ≤ m) :
    (bilanczosPoly A v₁ w₁ j).natDegree = j + 1 :=
  BiLanczos.vhatPoly_natDegree h.toBiLanczos hj

/-- **Section 7.1.2** of [saad2003iterative]: "there is a serious breakdown at step $j$ if and only
if the indefinite norm of the polynomial $p_j$ vanishes". If Algorithm 7.1 runs $m$ steps
without breakdown, then for $1 \le j \le m + 1$
$$(\hat v_{j+1}, \hat w_{j+1}) = 0 \iff \langle p_j, p_j \rangle = 0.$$

The two numbers differ by the factor $\gamma_j$ of `SaadSparse.Chapter07.bilanczosWhat_eq_smul`,
which is nonzero as long as the process has run this far. -/
theorem breakdown_iff_polyForm_eq_zero {m : ℕ} (h : NoBreakdown A v₁ w₁ m) {j : ℕ} (hj : j ≤ m) :
    inner 𝕜 (bilanczosWhat A v₁ w₁ j) (bilanczosVhat A v₁ w₁ j) = 0 ↔
      polyForm A v₁ w₁ (bilanczosPoly A v₁ w₁ j) (bilanczosPoly A v₁ w₁ j) = 0 := by
  rw [zeta_eq, ← BiLanczos.delta_succ_eq_zero_iff]
  exact BiLanczos.delta_succ_eq_zero_iff_polyForm_eq_zero h.toBiLanczos hj

/-- **Section 7.1.2** of [saad2003iterative]: "the nonsymmetric Lanczos algorithm attempts to
compute a sequence of polynomials that are orthogonal with respect to the indefinite inner
product defined above". If Algorithm 7.1 runs $m$ steps without breakdown, then
$\langle p_i, p_j \rangle = 0$ for $1 \le i, j \le m$ with $i \neq j$.

In fact $p_j$ is orthogonal to every polynomial of lower degree
(`BiLanczos.polyForm_vhatPoly_eq_zero_of_natDegree_le`). -/
theorem polyForm_bilanczosPoly_eq_zero {m : ℕ} (h : NoBreakdown A v₁ w₁ m) {i j : ℕ} (hi : i < m)
    (hj : j < m) (hij : i ≠ j) :
    polyForm A v₁ w₁ (bilanczosPoly A v₁ w₁ i) (bilanczosPoly A v₁ w₁ j) = 0 :=
  BiLanczos.polyForm_vhatPoly_eq_zero h.toBiLanczos hi hj hij

/-- **Exercise P-7.5** of [saad2003iterative], first part. If Algorithm 7.1 runs $m$ steps without
breakdown, $1 \le j \le m$, and $\deg(t^k p_i) < \deg p_j$, that is, $i + k < j$, then
$$\langle t^k p_j, p_i \rangle = 0.$$

**Correction.** The book prints the range "$p_1, p_2, \dots, p_{j-k}$ assuming $k \le j$", which
is one polynomial too long. At the last index, $t^k p_{j-k}$ has degree exactly $\deg p_j$, and
the pairing is a nonzero multiple of $\langle p_j, p_j \rangle$, which vanishes only at a
serious breakdown. The worked example of Section 7.1.2 has the same off-by-one: it says that
$q_j = x p_{j-1}$ is orthogonal to $p_1, \dots, p_{j-2}$. The statement here has the corrected
range.

The proof uses $\langle t^k p_j, p_i \rangle = \langle p_j, t^k p_i \rangle$ and the
orthogonality of $p_j$ to every polynomial of lower degree. -/
theorem problem_7_5 {m : ℕ} (h : NoBreakdown A v₁ w₁ m) {j : ℕ} (hj : j < m) {i k : ℕ}
    (hik : i + k + 1 ≤ j) :
    polyForm A v₁ w₁ (X ^ k * bilanczosPoly A v₁ w₁ j) (bilanczosPoly A v₁ w₁ i) = 0 := by
  rw [polyForm_eq_moment,
    show X ^ k * bilanczosPoly A v₁ w₁ j * bilanczosPoly A v₁ w₁ i
      = bilanczosPoly A v₁ w₁ j * (X ^ k * bilanczosPoly A v₁ w₁ i) from by ring,
    ← polyForm_eq_moment]
  refine BiLanczos.polyForm_vhatPoly_eq_zero_of_natDegree_le h.toBiLanczos hj ?_
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.natDegree_X_pow]
  exact le_trans (Nat.add_le_add_left (BiLanczos.vhatPoly_natDegree_le _ _ _ _ i) k) (by omega)

end OrthogonalPolynomials

/-! ### Exercise P-7.3: the variant normalized in the 2-norm -/

section UnitNorm

variable (A : Matrix (Fin n) (Fin n) 𝕜) (v₁ w₁ : EuclideanSpace 𝕜 (Fin n))

/-- **Exercise P-7.3** of [saad2003iterative]. The primal vectors of Algorithm 7.1 rescaled to unit
2-norm, $v'_j = v_j/\|v_j\|_2$.

These are the vectors that the variant of P-7.3 computes. Only the scaling of lines 7–8 differs;
the choice $\delta_{j+1} = \|\hat v_{j+1}\|_2$ is admissible by (7.1)
(`SaadSparse.Chapter07.equation_7_1_norm`), and the vectors that a run with this scaling
produces are the rescalings of the vectors of Algorithm 7.1. A zero vector stays $0$. -/
noncomputable def bilanczosVUnit (j : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  ((‖bilanczosV A v₁ w₁ j‖ : ℝ) : 𝕜)⁻¹ • bilanczosV A v₁ w₁ j

/-- **Exercise P-7.3** of [saad2003iterative]. The dual vectors of Algorithm 7.1 rescaled to unit
2-norm, $w'_j = w_j/\|w_j\|_2$; see `SaadSparse.Chapter07.bilanczosVUnit`. -/
noncomputable def bilanczosWUnit (j : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  ((‖bilanczosW A v₁ w₁ j‖ : ℝ) : 𝕜)⁻¹ • bilanczosW A v₁ w₁ j

variable {A v₁ w₁}

private theorem bilanczosV_ne_zero {m : ℕ} (h : NoBreakdown A v₁ w₁ m) {i : ℕ} (hi : i ≤ m) :
    bilanczosV A v₁ w₁ i ≠ 0 := fun hc => by
  have h1 := proposition_7_1 h hi hi
  rw [hc, inner_zero_right, ite_eq_left rfl] at h1
  exact zero_ne_one h1

private theorem bilanczosW_ne_zero {m : ℕ} (h : NoBreakdown A v₁ w₁ m) {i : ℕ} (hi : i ≤ m) :
    bilanczosW A v₁ w₁ i ≠ 0 := fun hc => by
  have h1 := proposition_7_1 h hi hi
  rw [hc, inner_zero_left, ite_eq_left rfl] at h1
  exact zero_ne_one h1

private theorem inner_unit_smul (a b : ℝ) (x y : EuclideanSpace 𝕜 (Fin n)) :
    inner 𝕜 ((a : 𝕜)⁻¹ • x) ((b : 𝕜)⁻¹ • y) = ((a * b : ℝ) : 𝕜)⁻¹ * inner 𝕜 x y := by
  rw [inner_smul_left, inner_smul_right, map_inv₀, RCLike.conj_ofReal, RCLike.ofReal_mul, mul_inv]
  ring

private theorem inner_bilanczosW_apply_bilanczosV {m : ℕ} (h : NoBreakdown A v₁ w₁ m) {i j : ℕ}
    (hi : i ≤ m) (hj : j + 1 ≤ m) :
    inner 𝕜 (bilanczosW A v₁ w₁ i) (op A (bilanczosV A v₁ w₁ j)) = bilanczosCoeff A v₁ w₁ i j := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  rw [bilanczosW_eq, bilanczosV_eq, bilanczosCoeff_eq]
  exact BiLanczos.inner_dualVec_apply_vec h.toBiLanczos hi (by omega)

/-- **Exercise P-7.3** of [saad2003iterative]. Assume that Algorithm 7.1 runs $m$ steps without
breakdown, and let $v'_j$, $w'_j$ be the vectors rescaled to unit 2-norm. Then:

1. $\|v'_i\|_2 = \|w'_i\|_2 = 1$ for $1 \le i \le m + 1$;
2. $(v'_j, w'_i) = \delta_{ij} / (\|w_i\|_2 \|v_j\|_2)$ for $1 \le i, j \le m + 1$;
3. $(Av'_j, w'_i) = t_{ij} / (\|w_i\|_2 \|v_j\|_2)$ for $1 \le i \le m + 1$ and $1 \le j \le m$,
   where $t_{ij}$ are the tridiagonal coefficients of (7.2).

So the rescaled families stay biorthogonal, but the projected problem becomes a generalized one.
Where Algorithm 7.1 has $W_m^H V_m = I$ and $W_m^H A V_m = T_m$, the rescaled families have
$W_m^H V_m = D_m$ and $W_m^H A V_m = D_W T_m D_V$, with diagonal matrices $D_m$, $D_W$, $D_V$ of
reciprocal norms. The eigenvalue problem to solve is then $T'_m y = \lambda D_m y$ instead of
$T_m y = \lambda y$. -/
theorem problem_7_3 {m : ℕ} (h : NoBreakdown A v₁ w₁ m) :
    (∀ i ≤ m, ‖bilanczosVUnit A v₁ w₁ i‖ = 1 ∧ ‖bilanczosWUnit A v₁ w₁ i‖ = 1) ∧
      (∀ i ≤ m, ∀ j ≤ m, inner 𝕜 (bilanczosWUnit A v₁ w₁ i) (bilanczosVUnit A v₁ w₁ j)
        = if i = j then ((‖bilanczosW A v₁ w₁ i‖ * ‖bilanczosV A v₁ w₁ j‖ : ℝ) : 𝕜)⁻¹ else 0) ∧
      (∀ i ≤ m, ∀ j, j + 1 ≤ m →
        inner 𝕜 (bilanczosWUnit A v₁ w₁ i) (op A (bilanczosVUnit A v₁ w₁ j))
          = ((‖bilanczosW A v₁ w₁ i‖ * ‖bilanczosV A v₁ w₁ j‖ : ℝ) : 𝕜)⁻¹
            * bilanczosCoeff A v₁ w₁ i j) := by
  refine ⟨fun i hi => ⟨?_, ?_⟩, fun i hi j hj => ?_, fun i hi j hj => ?_⟩
  · rw [bilanczosVUnit, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (bilanczosV_ne_zero h hi))]
  · rw [bilanczosWUnit, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (bilanczosW_ne_zero h hi))]
  · rw [bilanczosWUnit, bilanczosVUnit, inner_unit_smul, proposition_7_1 h hi hj]
    by_cases hij : i = j
    · rw [ite_eq_left hij, ite_eq_left hij, mul_one]
    · rw [ite_eq_right hij, ite_eq_right hij, mul_zero]
  · rw [bilanczosWUnit, bilanczosVUnit, map_smul, inner_unit_smul,
      inner_bilanczosW_apply_bilanczosV h hi hj]

end UnitNorm

end SaadSparse.Chapter07
