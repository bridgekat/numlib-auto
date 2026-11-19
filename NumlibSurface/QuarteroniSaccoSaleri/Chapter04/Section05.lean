/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.BiLanczos
import NumlibSurface.QuarteroniSaccoSaleri.Chapter04.Section04

/-!
# Quarteroni, Sacco and Saleri, Section 4.5: The Lanczos Method for Unsymmetric Systems

This module formalizes Section 4.5 of [quarteroni2000numerical]. For $A \in \mathbb{R}^{n \times n}$
and two starting vectors $v_1, z_1 \in \mathbb{R}^n$ with $z_1^T v_1 = 1$, the bi-orthogonalization
algorithm builds two sequences $v_k$ and $z_k$ by three-term recurrences in $A$ and $A^T$. If the
algorithm does not break down for $m$ steps, the two families are biorthogonal,
$z_i^T v_j = \delta_{ij}$ (4.67), they span the Krylov subspaces $K_m(A; v_1)$ and $K_m(A^T; z_1)$,
and $Z_m^T A V_m = T_m$ for a tridiagonal matrix $T_m$. The Lanczos method for unsymmetric systems
sets $x^{(m)} = x^{(0)} + V_m y^{(m)}$ with $T_m y^{(m)} = \|r^{(0)}\|_2 e_1$, and its residual is a
multiple of $v_{m+1}$. The section closes with the biconjugate gradient method, which is an oblique
projection method, and the quasi-minimal residual method, whose residual is bounded by a
quasi-residual.

The proofs specialize the backbone modules `Numlib.Krylov.BiLanczos` (the two-sided Lanczos process,
the biconjugate gradient method and the quasi-minimal residual method) and
`Numlib.Krylov.Hessenberg` (the residual formulas of a Hessenberg relation).

## Main definitions

* Section 4.5, `QuarteroniSaccoSaleri.Chapter04.biLanczosStep`: one step of the bi-orthogonalization
  algorithm.
* Section 4.5, `QuarteroniSaccoSaleri.Chapter04.biLanczos`: the state of the algorithm after $k$
  steps from $v_1$, $z_1$.
* Section 4.5, `QuarteroniSaccoSaleri.Chapter04.blV`, `QuarteroniSaccoSaleri.Chapter04.blZ`,
  `QuarteroniSaccoSaleri.Chapter04.blAlpha`, `QuarteroniSaccoSaleri.Chapter04.blBeta`,
  `QuarteroniSaccoSaleri.Chapter04.blGamma`: the vectors $v_k$, $z_k$ and the coefficients
  $\alpha_k$, $\beta_k$, $\gamma_k$ of the algorithm.
* Section 4.5, `QuarteroniSaccoSaleri.Chapter04.T`: the tridiagonal matrix $T_m$ of the
  coefficients.
* Section 4.5, `QuarteroniSaccoSaleri.Chapter04.That`: the $(m+1) \times m$ matrix $\bar T_m$, which
  is $T_m$ with the extra row $(0, \dots, 0, \gamma_{m+1})$.
* Section 4.5, `QuarteroniSaccoSaleri.Chapter04.Vmat`, `QuarteroniSaccoSaleri.Chapter04.Zmat`: the
  matrices $V_m$ and $Z_m$ with columns $v_1, \dots, v_m$ and $z_1, \dots, z_m$.

## Main results

* Section 4.5, `QuarteroniSaccoSaleri.Chapter04.biLanczos_eq`: the algorithm of the book is the
  backbone's two-sided Lanczos process of $A$ with adjoint $A^T$.
* Section 4.5, `QuarteroniSaccoSaleri.Chapter04.noBreakdown_of`: $z_1^T v_1 = 1$ and
  $\gamma_2, \dots, \gamma_{m+1} \neq 0$ give the backbone's hypothesis that the process runs $m$
  steps without breakdown.
* Equation (4.67), `QuarteroniSaccoSaleri.Chapter04.equation_4_67`: without breakdown,
  $z_i^T v_j = \delta_{ij}$, and the two families span $K_m(A; v_1)$ and $K_m(A^T; z_1)$.
* Section 4.5, `QuarteroniSaccoSaleri.Chapter04.biLanczos_tridiag`: without breakdown,
  $Z_m^T A V_m = T_m$.
* Section 4.5, `QuarteroniSaccoSaleri.Chapter04.lanczosUnsym_norm_residual`: the residual of the
  Lanczos method for unsymmetric systems is $r^{(m)} = -(\gamma_{m+1} e_m^T y^{(m)}) v_{m+1}$.
* Section 4.5, item 1, `QuarteroniSaccoSaleri.Chapter04.bicg_isPetrovGalerkin`: the biconjugate
  gradient method is the oblique projection method of Remark 4.4 with $Y_k = K_k(A; r^{(0)})$ and
  $L_k = K_k(A^T; r^{*(0)})$.
* Section 4.5, item 2, `QuarteroniSaccoSaleri.Chapter04.qmr_norm_residual_le`: the residual of
  $x^{(0)} + V_m y$ is $V_{m+1}(\|r^{(0)}\|_2 e_1 - \bar T_m y)$, and its norm is at most a bound of
  $V_{m+1}$ times the norm of the quasi-residual.

## Conventions

* Vectors are elements of `EuclideanSpace ℝ (Fin n)`, on which $A$ acts through
  `Matrix.toEuclideanLin A`, as in Sections 4.3 and 4.4. The transpose $A^T$ acts as the adjoint of
  $A$ (`QuarteroniSaccoSaleri.Chapter04.inner_toEuclideanLin_transpose`).
* Indices start at $0$: `QuarteroniSaccoSaleri.Chapter04.blV A v₁ z₁ k` is $v_{k+1}$,
  `QuarteroniSaccoSaleri.Chapter04.blAlpha A v₁ z₁ k` is $\alpha_{k+1}$, and
  `QuarteroniSaccoSaleri.Chapter04.blBeta A v₁ z₁ k` and `QuarteroniSaccoSaleri.Chapter04.blGamma A
  v₁ z₁ k` are $\beta_{k+1}$ and $\gamma_{k+1}$, with $\beta_1 = \gamma_1 = 0$.
* "The process runs $m$ steps without breakdown" is the hypothesis
  `∀ j < m, blGamma A v₁ z₁ (j + 1) ≠ 0`, that is $\gamma_2, \dots, \gamma_{m+1} \neq 0$. Together
  with $z_1^T v_1 = 1$, it gives the backbone's `BiLanczos.NoBreakdown` for $A$ and $A^T$
  (`QuarteroniSaccoSaleri.Chapter04.noBreakdown_of`).

## Implementation notes

* The algorithm is written as the book writes it, as one step
  `QuarteroniSaccoSaleri.Chapter04.biLanczosStep` on the state $(v_k, z_k, v_{k-1}, z_{k-1},
  \beta_k, \gamma_k)$, iterated from $(v_1, z_1, 0, 0, 0, 0)$. The state is the backbone's record
  `BiLanczos.State`, whose fields `w` and `delta` are the book's $z$ and $\gamma$.
* The step is the backbone's `BiLanczos.step` with $B = A^T$
  (`QuarteroniSaccoSaleri.Chapter04.biLanczosStep_eq`).
* The book stops the algorithm when $\gamma_{k+1} = 0$. In Lean, division by zero gives zero, so all
  later vectors are $0$.

## Deviations from the source

* **Totalization.** Two-sided Lanczos uses a total recurrence and states the initial-pairing
  requirement in its theorems. See `QuarteroniSaccoSaleri.Chapter04.biLanczosStep`,
  `QuarteroniSaccoSaleri.Chapter04.biLanczos`, `QuarteroniSaccoSaleri.Chapter04.biLanczos_succ`,
  `QuarteroniSaccoSaleri.Chapter04.blV`, `QuarteroniSaccoSaleri.Chapter04.blZ`,
  `QuarteroniSaccoSaleri.Chapter04.blAlpha`, `QuarteroniSaccoSaleri.Chapter04.blBeta`,
  `QuarteroniSaccoSaleri.Chapter04.blGamma`.
* **Scope.** Biorthogonality is stated for an extra column beyond the two Krylov spans. See
  `QuarteroniSaccoSaleri.Chapter04.equation_4_67`.
* **Totalization.** The tridiagonal and basis matrices also describe the padded recurrence. See
  `QuarteroniSaccoSaleri.Chapter04.T`, `QuarteroniSaccoSaleri.Chapter04.That`,
  `QuarteroniSaccoSaleri.Chapter04.Vmat`, `QuarteroniSaccoSaleri.Chapter04.Zmat`.
* **Scope.** The tridiagonal compression requires the nonzero normalization for the extra column.
  See `QuarteroniSaccoSaleri.Chapter04.biLanczos_tridiag`.
* **Scope.** The nonsymmetric residual formula uses the common start of Program 25 and a successful
  prefix. See `QuarteroniSaccoSaleri.Chapter04.lanczosUnsym_norm_residual`.
* **Scope.** The BiCG result specifies Petrov–Galerkin optimality on the paired Krylov spaces. See
  `QuarteroniSaccoSaleri.Chapter04.bicg_isPetrovGalerkin`.
* **Scope.** The QMR statement gives the reduced residual bound for supplied coefficients. See
  `QuarteroniSaccoSaleri.Chapter04.qmr_norm_residual_le`.
* **Residual formula of the Lanczos method** (reading). The formula $\|r^{(m)}\|_2 = |\gamma_{m+1}
  e_m^T y_m| \|v_{m+1}\|_2$ is stated for a run of $m$ steps without breakdown, which the derivation
  of the book needs. See `QuarteroniSaccoSaleri.Chapter04.lanczosUnsym_norm_residual`.
* **Item 2, the quasi-minimal residual method** (reading). The bound on the residual is stated with
  an explicit constant $C$ that bounds the map $w \mapsto V_{m+1} w$. See
  `QuarteroniSaccoSaleri.Chapter04.qmr_norm_residual_le`.

## Not formalized

* **Example 4.10.** It is a numerical run.
* **Program 25.** It is code.
* **Item 3, the CGS and BiCGStab methods.** The book names them without an algorithm or a result.
-/

open Filter Finset Matrix Topology WithLp

namespace QuarteroniSaccoSaleri.Chapter04

variable {n : ℕ}

/-! ### The bi-orthogonalization algorithm -/

section Algorithm

variable (A : Matrix (Fin n) (Fin n) ℝ)

/-- **Section 4.5** of [quarteroni2000numerical], one step of the bi-orthogonalization algorithm.
Let $A \in \mathbb{R}^{n \times n}$. The step maps the state $(v_k, z_k, v_{k-1}, z_{k-1},
\beta_k, \gamma_k)$ to $(v_{k+1}, z_{k+1}, v_k, z_k, \beta_{k+1}, \gamma_{k+1})$, where
$$\alpha_k = z_k^T A v_k, \quad \tilde v_{k+1} = A v_k - \alpha_k v_k - \beta_k v_{k-1}, \quad
  \tilde z_{k+1} = A^T z_k - \alpha_k z_k - \gamma_k z_{k-1},$$
$$\gamma_{k+1} = \sqrt{|\tilde z_{k+1}^T \tilde v_{k+1}|}, \quad \beta_{k+1} = \frac{\tilde
  z_{k+1}^T \tilde v_{k+1}}{\gamma_{k+1}}, \quad v_{k+1} = \frac{\tilde v_{k+1}}{\gamma_{k+1}},
  \quad z_{k+1} = \frac{\tilde z_{k+1}}{\beta_{k+1}}.$$
If $\gamma_{k+1} = 0$, then $\beta_{k+1} = 0$ and $v_{k+1} = z_{k+1} = 0$.

The book stops the algorithm when $\gamma_{k+1} = 0$. In Lean, division by zero gives zero, so
all later vectors are $0$. The state is the backbone's record `BiLanczos.State`, in which the
book's $z$ and $\gamma$ are the fields `w` and `delta`. The step is `BiLanczos.step` with
$B = A^T$ (`QuarteroniSaccoSaleri.Chapter04.biLanczosStep_eq`).

**Reading.** The recurrence is defined for arbitrary starting vectors and step counts. The source
requires the initial pairing to be one and stops at a vanishing normalization factor. Lean pads the
recurrence with zero vectors at breakdown.
-/
noncomputable def biLanczosStep (s : BiLanczos.State ℝ (EuclideanSpace ℝ (Fin n))) :
    BiLanczos.State ℝ (EuclideanSpace ℝ (Fin n)) :=
  let α := inner ℝ s.w (toEuclideanLin A s.v)
  let vt := toEuclideanLin A s.v - α • s.v - s.beta • s.vPrev
  let zt := toEuclideanLin Aᵀ s.w - α • s.w - s.delta • s.wPrev
  let γ := Real.sqrt |inner ℝ zt vt|
  let β := inner ℝ zt vt / γ
  { v := γ⁻¹ • vt, w := β⁻¹ • zt, vPrev := s.v, wPrev := s.w, beta := β, delta := γ }

/-- **Section 4.5** of [quarteroni2000numerical], the bi-orthogonalization algorithm. Let
$A \in \mathbb{R}^{n \times n}$ and $v_1, z_1 \in \mathbb{R}^n$. This is the state of the
algorithm after $k$ steps of `QuarteroniSaccoSaleri.Chapter04.biLanczosStep`, started from
$(v_1, z_1, v_0, z_0, \beta_1, \gamma_1) = (v_1, z_1, 0, 0, 0, 0)$.

**Reading.** The recurrence is defined for arbitrary starting vectors and step counts. The source
requires the initial pairing to be one and stops at a vanishing normalization factor. Lean pads the
recurrence with zero vectors at breakdown.
-/
noncomputable def biLanczos (v₁ z₁ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    BiLanczos.State ℝ (EuclideanSpace ℝ (Fin n)) :=
  (biLanczosStep A)^[k] { v := v₁, w := z₁, vPrev := 0, wPrev := 0, beta := 0, delta := 0 }

variable (v₁ z₁ : EuclideanSpace ℝ (Fin n))

/-- **Section 4.5** of [quarteroni2000numerical], the vectors $v_k$. This is the vector $v_{k+1}$ of
the bi-orthogonalization algorithm started from $v_1$ and $z_1$.

The index starts at $0$: `QuarteroniSaccoSaleri.Chapter04.blV A v₁ z₁ 0` is $v_1$.

**Reading.** The recurrence is defined for arbitrary starting vectors and step counts. The source
requires the initial pairing to be one and stops at a vanishing normalization factor. Lean pads the
recurrence with zero vectors at breakdown.
-/
noncomputable def blV (k : ℕ) : EuclideanSpace ℝ (Fin n) := (biLanczos A v₁ z₁ k).v

/-- **Section 4.5** of [quarteroni2000numerical], the vectors $z_k$. This is the vector $z_{k+1}$ of
the bi-orthogonalization algorithm started from $v_1$ and $z_1$.

The index starts at $0$: `QuarteroniSaccoSaleri.Chapter04.blZ A v₁ z₁ 0` is $z_1$.

**Reading.** The recurrence is defined for arbitrary starting vectors and step counts. The source
requires the initial pairing to be one and stops at a vanishing normalization factor. Lean pads the
recurrence with zero vectors at breakdown.
-/
noncomputable def blZ (k : ℕ) : EuclideanSpace ℝ (Fin n) := (biLanczos A v₁ z₁ k).w

/-- **Section 4.5** of [quarteroni2000numerical], the coefficients $\alpha_k$. This is the
coefficient $\alpha_{k+1} = z_{k+1}^T A v_{k+1}$ of the bi-orthogonalization algorithm.

The index starts at $0$.

**Reading.** The recurrence is defined for arbitrary starting vectors and step counts. The source
requires the initial pairing to be one and stops at a vanishing normalization factor. Lean pads the
recurrence with zero vectors at breakdown.
-/
noncomputable def blAlpha (k : ℕ) : ℝ := inner ℝ (blZ A v₁ z₁ k) (toEuclideanLin A (blV A v₁ z₁ k))

/-- **Section 4.5** of [quarteroni2000numerical], the coefficients $\beta_k$. This is the
coefficient $\beta_{k+1}$ of the bi-orthogonalization algorithm, with $\beta_1 = 0$.

The index starts at $0$.

**Reading.** The recurrence is defined for arbitrary starting vectors and step counts. The source
requires the initial pairing to be one and stops at a vanishing normalization factor. Lean pads the
recurrence with zero vectors at breakdown.
-/
noncomputable def blBeta (k : ℕ) : ℝ := (biLanczos A v₁ z₁ k).beta

/-- **Section 4.5** of [quarteroni2000numerical], the coefficients $\gamma_k$. This is the
coefficient $\gamma_{k+1}$ of the bi-orthogonalization algorithm, with $\gamma_1 = 0$. The value
$\gamma_{k+2} = 0$ is a breakdown at step $k + 1$.

The index starts at $0$.

**Reading.** The recurrence is defined for arbitrary starting vectors and step counts. The source
requires the initial pairing to be one and stops at a vanishing normalization factor. Lean pads the
recurrence with zero vectors at breakdown.
-/
noncomputable def blGamma (k : ℕ) : ℝ := (biLanczos A v₁ z₁ k).delta

/-- The state of the bi-orthogonalization algorithm after $k + 1$ steps is
`QuarteroniSaccoSaleri.Chapter04.biLanczosStep` applied to the state after $k$ steps.

**Reading.** The recurrence is defined for arbitrary starting vectors and step counts. The source
requires the initial pairing to be one and stops at a vanishing normalization factor. Lean pads the
recurrence with zero vectors at breakdown.
-/
theorem biLanczos_succ (k : ℕ) :
    biLanczos A v₁ z₁ (k + 1) = biLanczosStep A (biLanczos A v₁ z₁ k) :=
  Function.iterate_succ_apply' _ _ _

/-- For every state $s$, the step `QuarteroniSaccoSaleri.Chapter04.biLanczosStep` of the book equals
the backbone's step `BiLanczos.step` for the operators $A$ and $B = A^T$.

Over $\mathbb{R}$ the conjugations of the backbone are trivial and its modulus is the absolute
value. -/
theorem biLanczosStep_eq (s : BiLanczos.State ℝ (EuclideanSpace ℝ (Fin n))) :
    biLanczosStep A s = BiLanczos.step (toEuclideanLin A) (toEuclideanLin Aᵀ) s := by
  simp only [biLanczosStep, BiLanczos.step, BiLanczos.stepAlpha, BiLanczos.stepVhat,
    BiLanczos.stepWhat, RCLike.conj_to_real, Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq]

/-- The bi-orthogonalization algorithm of Section 4.5 of [quarteroni2000numerical] is the backbone's
two-sided Lanczos process of $A$ with adjoint $A^T$. For every $k$, the state after $k$ steps is
`BiLanczos.state`, and $v_{k+1}$, $z_{k+1}$, $\alpha_{k+1}$, $\beta_{k+1}$, $\gamma_{k+1}$ are
`BiLanczos.vec`, `BiLanczos.dualVec`, `BiLanczos.alpha`, `BiLanczos.beta` and `BiLanczos.delta`,
all for the operators $A$ and $A^T$ and the starting vectors $v_1$, $z_1$.

The book's $z$ and $\gamma$ are the $w$ and $\delta$ of the backbone, which follows
[saad2003iterative]. -/
theorem biLanczos_eq (k : ℕ) :
    biLanczos A v₁ z₁ k = BiLanczos.state (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k ∧
      blV A v₁ z₁ k = BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k ∧
      blZ A v₁ z₁ k = BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k ∧
      blAlpha A v₁ z₁ k = BiLanczos.alpha (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k ∧
      blBeta A v₁ z₁ k = BiLanczos.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k ∧
      blGamma A v₁ z₁ k = BiLanczos.delta (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k := by
  have hstate : ∀ k, biLanczos A v₁ z₁ k =
      BiLanczos.state (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [biLanczos_succ, ih, BiLanczos.state_succ, biLanczosStep_eq]
  refine ⟨hstate k, ?_, ?_, ?_, ?_, ?_⟩
  · rw [blV, hstate]; rfl
  · rw [blZ, hstate]; rfl
  · rw [blAlpha, blZ, blV, hstate]; rfl
  · rw [blBeta, hstate]; rfl
  · rw [blGamma, hstate]; rfl

/-- For $A \in \mathbb{R}^{n \times n}$ and $x, y \in \mathbb{R}^n$, $(Ax)^T y = x^T (A^T y)$: the
matrix $A^T$ acts as the adjoint of $A$. -/
theorem inner_toEuclideanLin_transpose (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (toEuclideanLin A x) y = inner ℝ x (toEuclideanLin Aᵀ y) := by
  rw [← conjTranspose_eq_transpose_of_trivial, real_inner_comm (toEuclideanLin Aᴴ y) x,
    toEuclideanLin_conjTranspose_inner_left, real_inner_comm]

variable {A v₁ z₁}

/-- Let $A \in \mathbb{R}^{n \times n}$ and $v_1, z_1 \in \mathbb{R}^n$ with $z_1^T v_1 = 1$, and
let $m \in \mathbb{N}$. If $\gamma_2, \dots, \gamma_{m+1} \neq 0$, then the backbone's
hypothesis `BiLanczos.NoBreakdown` holds for the operators $A$ and $A^T$, the starting vectors
$v_1$, $z_1$, and $m$ steps.

This is the reading of "the process runs $m$ steps without breakdown" in Section 4.5 of
[quarteroni2000numerical]. -/
theorem noBreakdown_of (hz : inner ℝ z₁ v₁ = 1) {m : ℕ}
    (hγ : ∀ j < m, blGamma A v₁ z₁ (j + 1) ≠ 0) :
    BiLanczos.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ m where
  adjoint := LinearMap.isAdjointPair_inner_iff'.2 (inner_toEuclideanLin_transpose A)
  inner_start := hz
  delta_ne_zero j hj := by
    rw [← (biLanczos_eq A v₁ z₁ (j + 1)).2.2.2.2.2]
    exact hγ j hj

end Algorithm

/-! ### Equation (4.67) and the tridiagonal matrix -/

section Biorthogonal

variable (A : Matrix (Fin n) (Fin n) ℝ) (v₁ z₁ : EuclideanSpace ℝ (Fin n))

/-- The range of a `Fin m`-indexed family is the image of `Set.Iio m`. -/
private theorem range_fin_eq_image_Iio {α : Type*} (f : ℕ → α) (m : ℕ) :
    Set.range (fun i : Fin m => f (i : ℕ)) = f '' Set.Iio m := by
  ext x
  simp only [Set.mem_range, Set.mem_image, Set.mem_Iio, Fin.exists_iff]
  tauto

/-- **Equation (4.67)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ and
$v_1, z_1 \in \mathbb{R}^n$ with $z_1^T v_1 = 1$, let $m \in \mathbb{N}$, and suppose that the
bi-orthogonalization algorithm does not break down, $\gamma_2, \dots, \gamma_{m+1} \neq 0$. Then
$$z_i^T v_j = \delta_{ij}, \qquad i, j = 1, \dots, m + 1,$$
and
$$\operatorname{span}\{v_1, \dots, v_m\} = K_m(A; v_1), \qquad \operatorname{span}\{z_1, \dots,
  z_m\} = K_m(A^T; z_1).$$

By the biorthogonality, the two families are linearly independent, so they are bases of the two
Krylov subspaces. The proof specializes the backbone's `BiLanczos.inner_dualVec_vec`,
`BiLanczos.span_vec` and `BiLanczos.span_dualVec`.

**Reading.** The result states biorthogonality through zero-based index $m$, so it requires that the
normalization for the extra column be nonzero as well. The two span identities refer to the first
$m$ columns.
-/
theorem equation_4_67 (hz : inner ℝ z₁ v₁ = 1) {m : ℕ}
    (hγ : ∀ j < m, blGamma A v₁ z₁ (j + 1) ≠ 0) :
    (∀ i j, i ≤ m → j ≤ m → inner ℝ (blZ A v₁ z₁ i) (blV A v₁ z₁ j) = if i = j then 1 else 0) ∧
      Submodule.span ℝ (Set.range fun i : Fin m => blV A v₁ z₁ i) = krylovSubspace A v₁ m ∧
      Submodule.span ℝ (Set.range fun i : Fin m => blZ A v₁ z₁ i) = krylovSubspace Aᵀ z₁ m := by
  have h := noBreakdown_of hz hγ
  simp only [(biLanczos_eq A v₁ z₁ _).2.1, (biLanczos_eq A v₁ z₁ _).2.2.1]
  refine ⟨fun i j hi hj => BiLanczos.inner_dualVec_vec h hi hj, ?_, ?_⟩
  · rw [range_fin_eq_image_Iio, BiLanczos.span_vec h, krylovSubspace_eq]
  · rw [range_fin_eq_image_Iio, BiLanczos.span_dualVec h, krylovSubspace_eq]

/-- **Section 4.5** of [quarteroni2000numerical], the tridiagonal matrix $T_m$. It is the
$m \times m$ matrix with $(T_m)_{kk} = \alpha_k$, $(T_m)_{k+1,k} = \gamma_{k+1}$ and
$(T_m)_{k,k+1} = \beta_{k+1}$, and with all other entries $0$.

The entry $(i, j)$ of the Lean matrix has $0$-based indices: the diagonal entry $(i, i)$ is
`QuarteroniSaccoSaleri.Chapter04.blAlpha A v₁ z₁ i`, which is $\alpha_{i+1}$.

**Reading.** The selected matrices are built from any prefix of the total recurrence, including
beyond breakdown. The book introduces them once the relevant basis has been generated.
-/
noncomputable def T (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then blAlpha A v₁ z₁ i
    else if (i : ℕ) = j + 1 then blGamma A v₁ z₁ i
    else if (j : ℕ) = i + 1 then blBeta A v₁ z₁ j
    else 0

/-- **Section 4.5** of [quarteroni2000numerical], the matrix $\bar T_m$. It is the $(m+1) \times m$
matrix with the same entries as $T_m$ in its first $m$ rows and the last row
$(0, \dots, 0, \gamma_{m+1})$. It is the matrix of the relation $A V_m = V_{m+1} \bar T_m$.

The indices are $0$-based, as in `QuarteroniSaccoSaleri.Chapter04.T`.

**Reading.** The selected matrices are built from any prefix of the total recurrence, including
beyond breakdown. The book introduces them once the relevant basis has been generated.
-/
noncomputable def That (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then blAlpha A v₁ z₁ i
    else if (i : ℕ) = j + 1 then blGamma A v₁ z₁ i
    else if (j : ℕ) = i + 1 then blBeta A v₁ z₁ j
    else 0

/-- **Section 4.5** of [quarteroni2000numerical], the matrix $V_m \in \mathbb{R}^{n \times m}$ whose
columns are $v_1, \dots, v_m$.

**Reading.** The selected matrices are built from any prefix of the total recurrence, including
beyond breakdown. The book introduces them once the relevant basis has been generated.
-/
noncomputable def Vmat (m : ℕ) : Matrix (Fin n) (Fin m) ℝ := Matrix.of fun i j => blV A v₁ z₁ j i

/-- **Section 4.5** of [quarteroni2000numerical], the matrix $Z_m \in \mathbb{R}^{n \times m}$ whose
columns are $z_1, \dots, z_m$.

**Reading.** The selected matrices are built from any prefix of the total recurrence, including
beyond breakdown. The book introduces them once the relevant basis has been generated.
-/
noncomputable def Zmat (m : ℕ) : Matrix (Fin n) (Fin m) ℝ := Matrix.of fun i j => blZ A v₁ z₁ j i

/-- The entries of $T_m$ are the backbone's tridiagonal coefficient array `BiLanczos.coeff` for the
operators $A$ and $A^T$. -/
theorem T_apply_eq_coeff (m : ℕ) (i j : Fin m) :
    T A v₁ z₁ m i j = BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ i j := by
  simp only [T, Matrix.of_apply, BiLanczos.coeff, (biLanczos_eq A v₁ z₁ _).2.2.2.1,
    (biLanczos_eq A v₁ z₁ _).2.2.2.2.1, (biLanczos_eq A v₁ z₁ _).2.2.2.2.2]

/-- The entries of $\bar T_m$ are the backbone's tridiagonal coefficient array `BiLanczos.coeff` for
the operators $A$ and $A^T$. -/
theorem That_apply_eq_coeff (m : ℕ) (i : Fin (m + 1)) (j : Fin m) :
    That A v₁ z₁ m i j = BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ i j := by
  simp only [That, Matrix.of_apply, BiLanczos.coeff, (biLanczos_eq A v₁ z₁ _).2.2.2.1,
    (biLanczos_eq A v₁ z₁ _).2.2.2.2.1, (biLanczos_eq A v₁ z₁ _).2.2.2.2.2]

/-- The entry $(i, j)$ of $Z_m^T A V_m$ is $z_i^T A v_j$. -/
private theorem transpose_Zmat_mul_mul_Vmat_apply (m : ℕ) (i j : Fin m) :
    ((Zmat A v₁ z₁ m)ᵀ * A * Vmat A v₁ z₁ m) i j =
      inner ℝ (blZ A v₁ z₁ i) (toEuclideanLin A (blV A v₁ z₁ j)) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ofLp_toEuclideanLin,
    Matrix.mul_apply, Matrix.transpose_apply, Zmat, Vmat, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **Section 4.5** of [quarteroni2000numerical], the tridiagonal form. Let
$A \in \mathbb{R}^{n \times n}$ and $v_1, z_1 \in \mathbb{R}^n$ with $z_1^T v_1 = 1$, let
$m \in \mathbb{N}$, and suppose that $\gamma_2, \dots, \gamma_{m+1} \neq 0$. Then
$$Z_m^T A V_m = T_m.$$

The proof specializes the backbone's `BiLanczos.inner_dualVec_apply_vec`.

**Reading.** The equality assumes that the extra vector after the $m$ columns is available. Only
pairings within the first $m$ columns appear in the displayed compression.
-/
theorem biLanczos_tridiag (hz : inner ℝ z₁ v₁ = 1) {m : ℕ}
    (hγ : ∀ j < m, blGamma A v₁ z₁ (j + 1) ≠ 0) :
    (Zmat A v₁ z₁ m)ᵀ * A * Vmat A v₁ z₁ m = T A v₁ z₁ m := by
  have h := noBreakdown_of hz hγ
  ext i j
  rw [transpose_Zmat_mul_mul_Vmat_apply, T_apply_eq_coeff, (biLanczos_eq A v₁ z₁ _).2.1,
    (biLanczos_eq A v₁ z₁ _).2.2.1]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := i.isLt; omega⟩
  exact BiLanczos.inner_dualVec_apply_vec h (by omega) (by have := j.isLt; omega)

end Biorthogonal

/-! ### The Lanczos method for unsymmetric systems -/

section Method

variable {A : Matrix (Fin n) (Fin n) ℝ} {v₁ z₁ : EuclideanSpace ℝ (Fin n)}

/-- If $b - A x_0 = \beta v_1$ and the process runs $m$ steps without breakdown, then the residual
of $x_0 + \sum_j y_j v_j$ is $\sum_{i=1}^{m+1} c_i v_i$ with the coordinate vector
$c = \beta e_1 - \bar T_m y$. -/
private theorem residual_eq_sum {b x₀ : EuclideanSpace ℝ (Fin n)} {β : ℝ}
    (hr : b - toEuclideanLin A x₀ = β • v₁) {m : ℕ}
    (h : BiLanczos.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ m) (y : Fin m → ℝ) :
    b - toEuclideanLin A (x₀ + ∑ j, y j • blV A v₁ z₁ j) =
      ∑ i : Fin (m + 1), (β • e₁ (m + 1) - That A v₁ z₁ m *ᵥ y) i • blV A v₁ z₁ i := by
  have hv : ∀ k, blV A v₁ z₁ k = BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ k :=
    fun k => (biLanczos_eq A v₁ z₁ k).2.1
  have hrel := h.hessenbergRelation₂.residual_eq (β := β) (b := b) (x₀ := x₀)
    (by rw [hr]; rfl) m y
  have hz : ∑ j : Fin m, y j • (if (j : ℕ) < m then
      BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ j else 0) =
      ∑ j : Fin m, y j • BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ j :=
    Finset.sum_congr rfl fun j _ => by rw [ite_eq_left j.isLt]
  have hH : Krylov.hessenbergOf (fun i j => if j < m then
      BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ z₁ i j else 0) m =
      That A v₁ z₁ m := by
    ext i j
    rw [Krylov.hessenbergOf, Matrix.of_apply, ite_eq_left j.isLt, That_apply_eq_coeff]
  rw [hz, hH, ← smul_e₁_eq_firstVec] at hrel
  simp only [hv]
  exact hrel

/-- **Section 4.5** of [quarteroni2000numerical], the Lanczos method for unsymmetric systems. Let
$A \in \mathbb{R}^{n \times n}$ and $b, x^{(0)} \in \mathbb{R}^n$ with
$r^{(0)} = b - A x^{(0)} \neq 0$, and run the bi-orthogonalization algorithm from
$v_1 = z_1 = r^{(0)} / \|r^{(0)}\|_2$. Let $m \ge 1$, and suppose that
$\gamma_2, \dots, \gamma_{m+1} \neq 0$. Let $y^{(m)} \in \mathbb{R}^m$ solve
$T_m y^{(m)} = \|r^{(0)}\|_2 e_1$, and let $x^{(m)} = x^{(0)} + V_m y^{(m)}$. Then the residual
$r^{(m)} = b - A x^{(m)}$ satisfies
$$r^{(m)} = -(\gamma_{m+1} e_m^T y^{(m)}) v_{m+1}, \qquad
  \|r^{(m)}\|_2 = |\gamma_{m+1} e_m^T y^{(m)}| \, \|v_{m+1}\|_2.$$

**Reading.** The formula is stated for a run of $m$ steps without breakdown,
$\gamma_2, \dots, \gamma_{m+1} \neq 0$, which the derivation of the book needs.

The choice $z_1 = v_1$ is that of Program 25, and it gives $z_1^T v_1 = 1$. The formula keeps
$\|v_{m+1}\|_2$ because the bi-Lanczos basis is not normalized. The vector $V_m y$ is
`∑ j, y j • blV A v₁ v₁ j`, and $e_m^T y$ is `y ⟨m - 1, _⟩`. The relation
$A V_m = V_{m+1} \bar T_m$ is a Hessenberg relation with a basis that is not orthonormal. It is
the backbone's $m$-step relation `BiLanczos.NoBreakdown.hessenbergRelation₂`, which pads the
relation with zeros beyond column $m$, and the proof applies
`Krylov.HessenbergRelation₂.residual_eq_of_mulVec_eq` to it.

**Reading.** The theorem uses the implementation's common primal and dual start and assumes a
successful prefix including the extra vector. It is conditional on supplied coefficients solving the
projected equation. The factor $\|v_{m+1}\|_2$ is retained because the primal basis is biorthogonal
with its dual.
-/
theorem lanczosUnsym_norm_residual {b x₀ : EuclideanSpace ℝ (Fin n)}
    (hr : b - toEuclideanLin A x₀ ≠ 0) (hv₁ : v₁ = (‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ •
      (b - toEuclideanLin A x₀)) {m : ℕ} (hm : 0 < m)
    (hγ : ∀ j < m, blGamma A v₁ v₁ (j + 1) ≠ 0) (y : Fin m → ℝ)
    (hy : T A v₁ v₁ m *ᵥ y = ‖b - toEuclideanLin A x₀‖ • e₁ m) :
    b - toEuclideanLin A (x₀ + ∑ j, y j • blV A v₁ v₁ j) =
        -(blGamma A v₁ v₁ m * y ⟨m - 1, Nat.sub_lt hm one_pos⟩) • blV A v₁ v₁ m ∧
      ‖b - toEuclideanLin A (x₀ + ∑ j, y j • blV A v₁ v₁ j)‖ =
        |blGamma A v₁ v₁ m * y ⟨m - 1, Nat.sub_lt hm one_pos⟩| * ‖blV A v₁ v₁ m‖ := by
  have hnorm : ‖b - toEuclideanLin A x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  have hz : inner ℝ v₁ v₁ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv₁, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm,
      one_pow]
  have h := noBreakdown_of hz hγ
  have hv : ∀ k, blV A v₁ v₁ k = BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ v₁ k :=
    fun k => (biLanczos_eq A v₁ v₁ k).2.1
  have hr' : b - toEuclideanLin A x₀ = ‖b - toEuclideanLin A x₀‖ • v₁ := by
    rw [hv₁, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  have hT : Krylov.hessenbergSqOf (fun i j => if j < m then
      BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ v₁ i j else 0) m = T A v₁ v₁ m := by
    ext i j
    rw [Krylov.hessenbergSqOf, Matrix.of_apply, ite_eq_left j.isLt, T_apply_eq_coeff]
  have hy' : Krylov.hessenbergSqOf (fun i j => if j < m then
      BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ v₁ i j else 0) m *ᵥ y =
      Krylov.firstVec ‖b - toEuclideanLin A x₀‖ m := by
    rw [hT, hy, smul_e₁_eq_firstVec]
  have hres := h.hessenbergRelation₂.residual_eq_of_mulVec_eq (b := b) (x₀ := x₀)
    (show b - toEuclideanLin A x₀ = ‖b - toEuclideanLin A x₀‖ •
      BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ v₁ 0 from hr') hm y hy'
  have hsum : ∑ j : Fin m, y j • (if (j : ℕ) < m then
      BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ v₁ j else 0) =
      ∑ j : Fin m, y j • BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) v₁ v₁ j :=
    Finset.sum_congr rfl fun j _ => by rw [ite_eq_left j.isLt]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hδ := (biLanczos_eq A v₁ v₁ (m' + 1)).2.2.2.2.2
  simp only [Nat.add_sub_cancel, Nat.lt_succ_self, ite_true, BiLanczos.coeff_succ_self,
    hsum] at hres
  simp only [← hδ, ← hv] at hres
  simp only [Nat.add_sub_cancel]
  refine ⟨hres, ?_⟩
  rw [hres, norm_smul, norm_neg, Real.norm_eq_abs]

/-- **Section 4.5** of [quarteroni2000numerical], item 1 (the biconjugate gradient method). Let
$A \in \mathbb{R}^{n \times n}$, let $b, x^{(0)} \in \mathbb{R}^n$, let
$r^{*(0)} \in \mathbb{R}^n$ be the shadow residual, and let $k \in \mathbb{N}$. Suppose that the
biconjugate gradient iteration, with $A^T$ as the adjoint of $A$, runs $k$ steps without
breakdown: for $j < k$, neither $r_j^{*T} r_j$ nor $p_j^{*T} A p_j$ is zero. Then its iterate
$x^{(k)}$ is the oblique projection method of Remark 4.4 with $Y_k = K_k(A; r^{(0)})$ and
$L_k = K_k(A^T; r^{*(0)})$:
$$x^{(k)} - x^{(0)} \in K_k(A; r^{(0)}), \qquad b - A x^{(k)} \perp K_k(A^T; r^{*(0)}).$$

The book says that the method "can be derived by the unsymmetric Lanczos method in the same way
as the conjugate gradient method is obtained from the FOM method". The iterate is the backbone's
`BCG.iterate`, which is Algorithm 7.3 of [saad2003iterative], and the hypothesis is
`BCG.NoBreakdown`. The proof specializes `BCG.isPetrovGalerkin`, which is Proposition 7.2 of
[saad2003iterative].

**Reading.** The declaration gives the BiCG iterate's Petrov–Galerkin condition under no breakdown.
The book describes deriving BiCG from unsymmetric Lanczos; the theorem does not identify the
implementation states of the two algorithms.
-/
theorem bicg_isPetrovGalerkin {b x₀ rs₀ : EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (h : BCG.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) b x₀ rs₀ k) :
    remark_4_4 A b x₀ (krylovSubspace A (b - toEuclideanLin A x₀) k) (krylovSubspace Aᵀ rs₀ k)
      (BCG.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) b x₀ rs₀ k).x := by
  rw [(remark_4_4_iff A b x₀ _ _ _).1, krylovSubspace_eq, krylovSubspace_eq]
  exact BCG.isPetrovGalerkin h

/-- **Section 4.5** of [quarteroni2000numerical], item 2 (the quasi-minimal residual method). Let
$A \in \mathbb{R}^{n \times n}$ and $b, x^{(0)} \in \mathbb{R}^n$ with
$r^{(0)} = b - A x^{(0)} \neq 0$, and run the bi-orthogonalization algorithm from
$v_1 = z_1 = r^{(0)} / \|r^{(0)}\|_2$. Let $m \in \mathbb{N}$, and suppose that
$\gamma_2, \dots, \gamma_{m+1} \neq 0$. Let $C \in \mathbb{R}$ satisfy
$\|V_{m+1} w\|_2 \le C \|w\|_2$ for all $w \in \mathbb{R}^{m+1}$. Then for every
$y \in \mathbb{R}^m$,
$$b - A(x^{(0)} + V_m y) = V_{m+1} \left( \|r^{(0)}\|_2 e_1 - \bar T_m y \right), \qquad
  \|b - A(x^{(0)} + V_m y)\|_2 \le C \left\| \|r^{(0)}\|_2 e_1 - \bar T_m y \right\|_2.$$

**Reading.** The book describes the method as "analogous to the GMRES method, the only
difference being that the Arnoldi orthonormalization is replaced by the Lanczos
bi-orthogonalization". The bound on the residual is stated here with an explicit constant $C$
for the map $w \mapsto V_{m+1} w$. The smallest such constant is $\|V_{m+1}\|_2$.

The quasi-residual $\|r^{(0)}\|_2 e_1 - \bar T_m y$ is what the method minimizes over $y$, in
place of the residual that GMRES minimizes. The two differ because $V_{m+1}$ is not orthogonal.
The proof specializes the backbone's `QMR.norm_residual_le_norm_quasiResidual`, which is
Proposition 7.3 of [saad2003iterative].

**Reading.** The declaration gives a residual identity and an inequality for any supplied projected
coefficient vector, with an explicit operator bound on the basis. It does not choose the reduced
least-squares minimizer described by the GMRES analogy.
-/
theorem qmr_norm_residual_le {b x₀ : EuclideanSpace ℝ (Fin n)}
    (hr : b - toEuclideanLin A x₀ ≠ 0) (hv₁ : v₁ = (‖b - toEuclideanLin A x₀‖ : ℝ)⁻¹ •
      (b - toEuclideanLin A x₀)) {m : ℕ} (hγ : ∀ j < m, blGamma A v₁ v₁ (j + 1) ≠ 0) {C : ℝ}
    (hC : ∀ z : Fin (m + 1) → ℝ, ‖∑ i, z i • blV A v₁ v₁ i‖ ≤
      C * ‖(toLp 2 z : EuclideanSpace ℝ (Fin (m + 1)))‖) (y : Fin m → ℝ) :
    b - toEuclideanLin A (x₀ + ∑ j, y j • blV A v₁ v₁ j) =
        ∑ i : Fin (m + 1), (‖b - toEuclideanLin A x₀‖ • e₁ (m + 1) - That A v₁ v₁ m *ᵥ y) i •
          blV A v₁ v₁ i ∧
      ‖b - toEuclideanLin A (x₀ + ∑ j, y j • blV A v₁ v₁ j)‖ ≤
        C * ‖(toLp 2 (‖b - toEuclideanLin A x₀‖ • e₁ (m + 1) - That A v₁ v₁ m *ᵥ y) :
          EuclideanSpace ℝ (Fin (m + 1)))‖ := by
  have hnorm : ‖b - toEuclideanLin A x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  have hz : inner ℝ v₁ v₁ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv₁, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm,
      one_pow]
  have h := noBreakdown_of hz hγ
  have hr' : b - toEuclideanLin A x₀ = ‖b - toEuclideanLin A x₀‖ • v₁ := by
    rw [hv₁, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  have hres := residual_eq_sum hr' h y
  exact ⟨hres, by rw [hres]; exact hC _⟩

end Method

end QuarteroniSaccoSaleri.Chapter04
