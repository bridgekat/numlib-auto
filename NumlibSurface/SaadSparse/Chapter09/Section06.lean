/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.CGW
import NumlibSurface.SaadSparse.Chapter01.Section11
import NumlibSurface.SaadSparse.Chapter09.Section02

/-!
# Saad, Section 9.6: The Concus–Golub–Widlund algorithm

This module formalizes Section 9.6 of [saad2003iterative]. For a nearly symmetric matrix $A$, the
preconditioner is its Hermitian part $M = (A + A^H)/2$, and $A = M - N$ with the skew-Hermitian
matrix $N = M - A = (A^H - A)/2$. Then $M^{-1} A = I - M^{-1} N$, and $M^{-1} N$ is skew-adjoint for
the $M$-inner product $(x, y)_M = (Mx, y)$. So the adjoint of $M^{-1} A$ for that inner product is
$2I - M^{-1} A$.

Two consequences give the algorithm a short recurrence. The Arnoldi process for $M^{-1} A$ in the
$M$-inner product has a tridiagonal Hessenberg matrix, because $2v - M^{-1} A v$ lies in
$\operatorname{span}\{v, M^{-1} A v\}$. Its entries satisfy
$h_{ij} + \overline{h_{ji}} = 2 (v_j, v_i)_M$, so the diagonal is $1$ and the two off-diagonals are
$\eta_{j+1}$ and $-\overline{\eta_{j+1}}$; this is (9.29). The resulting algorithm is Algorithm 9.1
with the sign of $\beta_j$ reversed. Over $\mathbb{R}$, its iterate is the Galerkin iterate of
$M^{-1} A x = M^{-1} b$ in the $M$-inner product. This is its only optimality property: it minimizes
nothing, because $M^{-1} A$ is not self-adjoint for the $M$-inner product. The proofs specialize the
backbone recurrence `CGW.iterate` of `Numlib.Krylov.CGW` for an operator of the form identity plus a
skew-adjoint operator.

## Main definitions

* Section 9.6, `SaadSparse.Chapter09.cgwM`: the preconditioner $M = (A + A^H)/2$.
* Section 9.6, `SaadSparse.Chapter09.cgwN`: the skew-Hermitian part $N = M - A$.
* Section 9.6, `SaadSparse.Chapter09.cgw`: the Concus–Golub–Widlund algorithm.

## Main results

* Section 9.6, `SaadSparse.Chapter09.cgwM_sub_cgwN`: $A = M - N$.
* Section 9.6, `SaadSparse.Chapter09.cgwM_isHermitian`: $M$ is Hermitian.
* Section 9.6, `SaadSparse.Chapter09.cgwN_conjTranspose`: $N$ is skew-Hermitian.
* Section 9.6, `SaadSparse.Chapter09.isSkewAdjoint_energy`: $M^{-1} N$ is skew-adjoint for the
  $M$-inner product.
* Section 9.6, `SaadSparse.Chapter09.adjoint_energyEnd`: the adjoint of $M^{-1} A$ for the $M$-inner
  product is $2I - M^{-1} A$.
* Equation (9.29), `SaadSparse.Chapter09.equation_9_29`: the Hessenberg matrix of the $M$-orthogonal
  Arnoldi process is tridiagonal, with unit diagonal and opposite conjugate off-diagonals.
* Section 9.6, `SaadSparse.Chapter09.cgw_residual_eq`: the residual of the algorithm is the true
  residual.
* Section 9.6, `SaadSparse.Chapter09.cgw_alpha`: the step length is that of Algorithm 9.1, and
  $\beta_j$ is the negative of that of Algorithm 9.1.
* Section 9.6, `SaadSparse.Chapter09.isShiftedSkewAdjoint_energyEnd`: over $\mathbb{R}$, $M^{-1} A$
  is shifted skew-adjoint for the $M$-inner product.
* Section 9.6, `SaadSparse.Chapter09.cgw_eq_CGW_iterate`: over $\mathbb{R}$, the algorithm is the
  backbone recurrence `CGW.iterate`.
* Section 9.6, `SaadSparse.Chapter09.cgw_isGalerkinIterate`: over $\mathbb{R}$, the iterate is the
  Galerkin iterate over $x_0 + \mathcal{K}_j(M^{-1} A, M^{-1} r_0)$.

## Implementation notes

* The Galerkin property, and the two results that lead to it, are stated over $\mathbb{R}$. Over
  $\mathbb{C}$ the Galerkin property is false: the quadratic form of a skew-adjoint operator is
  purely imaginary rather than zero, so the step length $\alpha_j$ is complex, and the cancellation
  that makes the search directions $M^{-1} A$-conjugate fails already at $j = 1$. The rest of the
  module, including (9.29), holds over $\mathbb{R}$ and over $\mathbb{C}$. The module doc comment of
  `Numlib.Krylov.CGW` gives the details.
* The hypothesis that $M$ is positive definite is `Krylov.IsPreconditioner (op (cgwM A)) (op (cgwM
  A)⁻¹)`.
* The state of the algorithm is the triple $(x_j, r_j, p_j)$, and indices are $0$-based. The step
  reuses the step length and the coefficient of Algorithm 9.1 (`SaadSparse.Chapter09.pcgStepAlpha`
  and `SaadSparse.Chapter09.pcgStepBeta`).

## Deviations from the source

* **Generalization.** The energy identities make the preconditioner hypothesis explicit and identify
  the adjoint. See `SaadSparse.Chapter09.isSkewAdjoint_energy`,
  `SaadSparse.Chapter09.energyEnd_eq_one_sub`, `SaadSparse.Chapter09.adjoint_energyEnd`,
  `SaadSparse.Chapter09.isShiftedSkewAdjoint_energyEnd`.
* **Reading.** The tridiagonal identities use the preconditioned operator and the complex
  skew-Hermitian form of the display. See `SaadSparse.Chapter09.equation_9_29`.
* **Generalization.** The CGW coefficient and state recurrences are total and retain the negative
  beta. See `SaadSparse.Chapter09.cgwStep`, `SaadSparse.Chapter09.cgw`,
  `SaadSparse.Chapter09.cgw_succ`, `SaadSparse.Chapter09.cgwAlpha`, `SaadSparse.Chapter09.cgwBeta`,
  `SaadSparse.Chapter09.cgw_alpha`.
* **Scope.** The CGW equivalence and Galerkin result are proved for real input with a valid energy
  preconditioner. See `SaadSparse.Chapter09.cgw_eq_CGW_iterate`,
  `SaadSparse.Chapter09.cgw_isGalerkinIterate`.

## Not formalized

* The inner-outer variants of Golub and Overton, which the notes of Section 9.6 mention. The book
  states no result about them.
-/

open Matrix

open scoped ComplexOrder SaadSparse

namespace SaadSparse.Chapter09

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Section 9.6: the splitting $A = M - N$ -/

/-- **Section 9.6** of [saad2003iterative], the preconditioner. For $A \in \mathbb{K}^{n \times n}$,
the preconditioner of the Concus–Golub–Widlund algorithm is the **Hermitian part** of $A$,
$$M = \tfrac{1}{2}(A + A^H).$$

The definition is Mathlib's `Matrix.hermitianPart`. -/
noncomputable def cgwM (A : Matrix (Fin n) (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.hermitianPart A

/-- **Section 9.6** of [saad2003iterative], the skew-Hermitian part. For
$A \in \mathbb{K}^{n \times n}$, the matrix $N$ of the splitting $A = M - N$ is
$$N = M - A = \tfrac{1}{2}(A^H - A).$$
The second form is `SaadSparse.Chapter09.cgwN_eq`. -/
noncomputable def cgwN (A : Matrix (Fin n) (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  cgwM A - A

variable {A : Matrix (Fin n) (Fin n) 𝕜}

/-- **Section 9.6** of [saad2003iterative], the splitting. For every
$A \in \mathbb{K}^{n \times n}$, $A = M - N$ with $M = (A + A^H)/2$ and $N = M - A$. -/
theorem cgwM_sub_cgwN (A : Matrix (Fin n) (Fin n) 𝕜) : cgwM A - cgwN A = A := by
  rw [cgwN, sub_sub_cancel]

/-- **Section 9.6** of [saad2003iterative]. For every $A \in \mathbb{K}^{n \times n}$, the
preconditioner $M = (A + A^H)/2$ is Hermitian. -/
theorem cgwM_isHermitian (A : Matrix (Fin n) (Fin n) 𝕜) : (cgwM A).IsHermitian :=
  Matrix.hermitianPart_isHermitian A

/-- For every $A \in \mathbb{K}^{n \times n}$, $N = \frac{1}{2}(A^H - A)$. -/
theorem cgwN_eq (A : Matrix (Fin n) (Fin n) 𝕜) : cgwN A = (2⁻¹ : 𝕜) • (Aᴴ - A) := by
  have h : cgwM A = (2⁻¹ : 𝕜) • (A + Aᴴ) := rfl
  rw [cgwN, h]
  match_scalars <;> ring

/-- **Section 9.6** of [saad2003iterative]. For every $A \in \mathbb{K}^{n \times n}$, the matrix
$N = M - A$ is skew-Hermitian: $N^H = -N$. -/
theorem cgwN_conjTranspose (A : Matrix (Fin n) (Fin n) 𝕜) : (cgwN A)ᴴ = -cgwN A := by
  rw [cgwN_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, ← neg_sub Aᴴ A, smul_neg,
    show star (2⁻¹ : 𝕜) = 2⁻¹ by simp]

/-! ### Section 9.6: skew-adjointness in the $M$-inner product -/

section Energy

variable {M : Matrix (Fin n) (Fin n) 𝕜}

/-- **Section 9.6** of [saad2003iterative], skew-adjointness of $M^{-1} N$. Let
$N \in \mathbb{K}^{n \times n}$ be skew-Hermitian, $N^H = -N$, and let $M$ be a preconditioner.
Then $M^{-1} N$ is skew-adjoint for the $M$-inner product:
$$(M^{-1} N u, v)_M = -(u, M^{-1} N v)_M \quad \text{for all } u, v.$$

The vectors $u$ and $v$ are elements of the space with the $M$-inner product, `hM.EnergySpace`.

**Generalization.** The skew-adjoint fact is stated for an arbitrary skew-Hermitian matrix and
energy preconditioner. The specialized formulas explicitly assume a valid positive definite energy
inner product, and identify the adjoint as $2I-M^{-1}A$.
-/
theorem isSkewAdjoint_energy {N : Matrix (Fin n) (Fin n) 𝕜} (hN : Nᴴ = -N)
    (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) (u v : hM.EnergySpace) :
    inner 𝕜 (hM.energyEnd (op M⁻¹ ∘ₗ op N) u) v
      = -inner 𝕜 u (hM.energyEnd (op M⁻¹ ∘ₗ op N) v) := by
  obtain ⟨x, rfl⟩ := hM.toEnergy.surjective u
  obtain ⟨y, rfl⟩ := hM.toEnergy.surjective v
  rw [hM.inner_energyEnd_left (op N), hM.inner_energyEnd_right (op N),
    Chapter07.inner_op_conjTranspose N x y, hN]
  have hneg : (op (-N) : 𝔼 →ₗ[𝕜] 𝔼) = -op N := map_neg Matrix.toEuclideanLin N
  rw [hneg, LinearMap.neg_apply, inner_neg_right]

/-- Let the Hermitian part $M$ of $A$ be a preconditioner. Then $M^{-1} A u = u - M^{-1} N u$ for
every $u$, in the space with the $M$-inner product.

**Generalization.** The skew-adjoint fact is stated for an arbitrary skew-Hermitian matrix and
energy preconditioner. The specialized formulas explicitly assume a valid positive definite energy
inner product, and identify the adjoint as $2I-M^{-1}A$.
-/
theorem energyEnd_eq_one_sub (hM : Krylov.IsPreconditioner (op (cgwM A)) (op (cgwM A)⁻¹))
    (u : hM.EnergySpace) :
    hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) u
      = u - hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op (cgwN A)) u := by
  obtain ⟨x, rfl⟩ := hM.toEnergy.surjective u
  have hA : (op A : 𝔼 →ₗ[𝕜] 𝔼) x = op (cgwM A) x - op (cgwN A) x := by
    rw [← LinearMap.sub_apply, ← map_sub, cgwM_sub_cgwN]
  rw [Krylov.IsPreconditioner.energyEnd_apply, Krylov.IsPreconditioner.energyEnd_apply,
    ← map_sub]
  congr 1
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hA, map_sub, hM.inv_apply]

/-- **Section 9.6** of [saad2003iterative], the adjoint of $M^{-1} A$. Let
$A \in \mathbb{K}^{n \times n}$, and let its Hermitian part $M$ be a preconditioner (positive
definite). Then the adjoint of $M^{-1} A$ for the $M$-inner product is $2I - M^{-1} A$:
$$(M^{-1} A u, v)_M = (u, 2v - M^{-1} A v)_M \quad \text{for all } u, v.$$

The whole section rests on this fact: it makes the Hessenberg matrix of the $M$-orthogonal
Arnoldi process tridiagonal.

**Generalization.** The skew-adjoint fact is stated for an arbitrary skew-Hermitian matrix and
energy preconditioner. The specialized formulas explicitly assume a valid positive definite energy
inner product, and identify the adjoint as $2I-M^{-1}A$.
-/
theorem adjoint_energyEnd (hM : Krylov.IsPreconditioner (op (cgwM A)) (op (cgwM A)⁻¹))
    (u v : hM.EnergySpace) :
    inner 𝕜 (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) u) v
      = inner 𝕜 u ((2 : 𝕜) • v - hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) v) := by
  have hskew := isSkewAdjoint_energy (cgwN_conjTranspose A) hM
  have hone := energyEnd_eq_one_sub (A := A) hM
  rw [hone u, inner_sub_left, hskew u v]
  have hv : hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op (cgwN A)) v
      = v - hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) v := by
    rw [hone v]; abel
  rw [hv, inner_sub_right, inner_sub_right, two_smul, inner_add_right]
  ring

end Energy

/-! ### Equation (9.29): the tridiagonal Hessenberg matrix of the $M$-orthogonal Arnoldi process -/

/-- **Equation (9.29)** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$, and let its
Hermitian part $M$ be a preconditioner. Let $v_0, v_1, \ldots$ be the Arnoldi vectors of
$B = M^{-1} A$ in the $M$-inner product, started from a vector $b$, and let
$h_{ij} = (B v_j, v_i)_M$ be the Hessenberg coefficients. Then:
* $h_{ij} = 0$ whenever $j \ge i + 2$; with the Hessenberg structure, only the three central
  diagonals remain, so the Hessenberg matrix is tridiagonal;
* $h_{ij} + \overline{h_{ji}} = 2 (v_j, v_i)_M$ for all $i, j$, so the superdiagonal entry is
  $-\overline{\eta_{j+1}}$ when the subdiagonal entry is $\eta_{j+1}$;
* $\operatorname{Re} h_{ii} = 1$ for every $i$ less than the grade of $b$ with respect to $B$.

Over $\mathbb{R}$ the third clause is the statement $h_{ii} = 1$ of the book. The Arnoldi
vectors and coefficients are the backbone `Arnoldi.vec` and `Arnoldi.coeff`, with $0$-based
indices; the vectors are the normalized Gram–Schmidt vectors of the sequence $B^i b$.

**Reading.** The surrounding text discusses $M^{-1}A$; the sentence before the display names $A$.
Lean uses the preconditioned operator. The complex result fixes the real part of the diagonal to one
before the grade and relates opposite entries by negative conjugation on an orthogonal prefix; the
displayed real matrix uses diagonal ones and opposite signed entries.
-/
theorem equation_9_29 (hM : Krylov.IsPreconditioner (op (cgwM A)) (op (cgwM A)⁻¹))
    (b : hM.EnergySpace) :
    (∀ i j : ℕ, i + 2 ≤ j →
        Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i j = 0) ∧
      (∀ i j : ℕ,
        Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i j
            + starRingEnd 𝕜 (Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b j i)
          = 2 * inner 𝕜 (Arnoldi.vec (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i)
              (Arnoldi.vec (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b j)) ∧
      (∀ i : ℕ, i < Krylov.grade (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b →
        RCLike.re (Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i i) = 1) := by
  have hadj := adjoint_energyEnd (A := A) hM
  have hband : ∀ i j : ℕ, i + 2 ≤ j →
      Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i j = 0 := by
    intro i j hij
    refine Arnoldi.coeff_eq_zero_of_adjoint_mem _ b
      (B := (2 : 𝕜) • (LinearMap.id : hM.EnergySpace →ₗ[𝕜] hM.EnergySpace)
        - hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) (LinearMap.isAdjointPair_inner_iff'.2 fun x y => ?_)
        (s := 2) (fun v => ?_) hij
    · rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      exact hadj x y
    · have h0 : v ∈ Krylov.subspace (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) v 2 :=
        Krylov.self_mem_subspace _ v (by omega)
      have h1 : hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) v
          ∈ Krylov.subspace (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) v 2 := by
        have h := Krylov.pow_apply_mem_subspace
          (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) v (i := 1) (m := 2) (by omega)
        simpa using h
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ h0) h1
  have hsum : ∀ i j : ℕ,
      Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i j
          + starRingEnd 𝕜 (Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b j i)
        = 2 * inner 𝕜 (Arnoldi.vec (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i)
            (Arnoldi.vec (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b j) := by
    intro i j
    rw [Arnoldi.coeff, Arnoldi.coeff, inner_conj_symm, hadj, inner_sub_right,
      inner_smul_right]
    ring
  refine ⟨hband, hsum, fun i hi => ?_⟩
  have : FiniteDimensional 𝕜 hM.EnergySpace :=
    LinearEquiv.finiteDimensional (hM.toEnergy)
  have hnorm := Arnoldi.norm_vec_eq_one_of_lt_grade
    (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b hi
  have h := hsum i i
  rw [inner_self_eq_norm_sq_to_K, hnorm] at h
  have h2 : (2 : 𝕜) * (RCLike.re (Arnoldi.coeff
      (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i i) : 𝕜) = 2 * 1 := by
    rw [← RCLike.add_conj]
    simpa using h
  have h3 : ((RCLike.re (Arnoldi.coeff (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)) b i i) : ℝ) : 𝕜)
      = ((1 : ℝ) : 𝕜) := by
    have := mul_left_cancel₀ (a := (2 : 𝕜)) (by norm_num) h2
    simpa using this
  exact_mod_cast h3

/-! ### The algorithm -/

section Algorithm

variable (A M : Matrix (Fin n) (Fin n) 𝕜)

/-- One step of the Concus–Golub–Widlund recurrence: Algorithm 9.1 of [saad2003iterative] with the
sign of $\beta_j$ reversed. It maps the state $(x_j, r_j, p_j)$ to $(x_j + \alpha_j p_j, \;
r_{j+1}, \; z_{j+1} - \beta_j p_j)$, where $\alpha_j$, $r_{j+1}$, $z_{j+1} = M^{-1} r_{j+1}$ and
$\beta_j$ are as in Algorithm 9.1.

**Generalization.** The recurrences are total for all matrices and indices, including an undefined
quotient. The coefficient order follows the conjugate-linear-first convention and recovers the real
recurrence. The negative sign of beta follows the printed CGW formula.
-/
noncomputable def cgwStep (s : 𝔼 × 𝔼 × 𝔼) : 𝔼 × 𝔼 × 𝔼 :=
  (s.1 + pcgStepAlpha A M s • s.2.2, pcgStepR A M s,
    op M⁻¹ (pcgStepR A M s) - pcgStepBeta A M s • s.2.2)

variable (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- **Section 9.6** of [saad2003iterative], the Concus–Golub–Widlund algorithm. Let
$A \in \mathbb{K}^{n \times n}$ with Hermitian part $M = (A + A^H)/2$, and let
$b, x_0 \in \mathbb{K}^n$. Set $r_0 = b - A x_0$ and $p_0 = z_0 = M^{-1} r_0$. For
$j = 0, 1, \ldots$ compute
$$\alpha_j = \frac{(r_j, z_j)}{(A p_j, p_j)}, \quad x_{j+1} = x_j + \alpha_j p_j, \quad
  r_{j+1} = r_j - \alpha_j A p_j,$$
$$z_{j+1} = M^{-1} r_{j+1}, \quad \beta_j = -\frac{(r_{j+1}, z_{j+1})}{(r_j, z_j)}, \quad
  p_{j+1} = z_{j+1} + \beta_j p_j.$$
The value at $j$ is the triple $(x_j, r_j, p_j)$ after $j$ steps.

**Generalization.** The recurrences are total for all matrices and indices, including an undefined
quotient. The coefficient order follows the conjugate-linear-first convention and recovers the real
recurrence. The negative sign of beta follows the printed CGW formula.
-/
noncomputable def cgw (j : ℕ) : 𝔼 × 𝔼 × 𝔼 :=
  (cgwStep A (cgwM A))^[j] (x₀, b - op A x₀, op (cgwM A)⁻¹ (b - op A x₀))

/-- The iterate $x_j$ of the Concus–Golub–Widlund algorithm. -/
noncomputable def cgwX (j : ℕ) : 𝔼 := (cgw A b x₀ j).1

/-- The residual $r_j$ of the Concus–Golub–Widlund algorithm, as computed by the recurrence. -/
noncomputable def cgwR (j : ℕ) : 𝔼 := (cgw A b x₀ j).2.1

/-- The search direction $p_j$ of the Concus–Golub–Widlund algorithm. -/
noncomputable def cgwP (j : ℕ) : 𝔼 := (cgw A b x₀ j).2.2

/-- The preconditioned residual $z_j = M^{-1} r_j$ of the Concus–Golub–Widlund algorithm. -/
noncomputable def cgwZ (j : ℕ) : 𝔼 := op (cgwM A)⁻¹ (cgwR A b x₀ j)

/-- The step length $\alpha_j$ of the Concus–Golub–Widlund algorithm.

**Generalization.** The recurrences are total for all matrices and indices, including an undefined
quotient. The coefficient order follows the conjugate-linear-first convention and recovers the real
recurrence. The negative sign of beta follows the printed CGW formula.
-/
noncomputable def cgwAlpha (j : ℕ) : 𝕜 := pcgStepAlpha A (cgwM A) (cgw A b x₀ j)

/-- The direction coefficient $\beta_j$ of the Concus–Golub–Widlund algorithm, the negative of the
coefficient of Algorithm 9.1.

**Generalization.** The recurrences are total for all matrices and indices, including an undefined
quotient. The coefficient order follows the conjugate-linear-first convention and recovers the real
recurrence. The negative sign of beta follows the printed CGW formula.
-/
noncomputable def cgwBeta (j : ℕ) : 𝕜 := -pcgStepBeta A (cgwM A) (cgw A b x₀ j)

/-- The state of the Concus–Golub–Widlund algorithm after $j + 1$ steps is one step applied to the
state after $j$ steps.

**Generalization.** The recurrences are total for all matrices and indices, including an undefined
quotient. The coefficient order follows the conjugate-linear-first convention and recovers the real
recurrence. The negative sign of beta follows the printed CGW formula.
-/
theorem cgw_succ (j : ℕ) : cgw A b x₀ (j + 1) = cgwStep A (cgwM A) (cgw A b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

/-- The Concus–Golub–Widlund algorithm starts at $x_0$. -/
@[simp] theorem cgwX_zero : cgwX A b x₀ 0 = x₀ := rfl

/-- The initial residual of the Concus–Golub–Widlund algorithm is $r_0 = b - A x_0$. -/
@[simp] theorem cgwR_zero : cgwR A b x₀ 0 = b - op A x₀ := rfl

/-- The initial direction of the Concus–Golub–Widlund algorithm is $p_0 = z_0 = M^{-1} r_0$. -/
@[simp] theorem cgwP_zero : cgwP A b x₀ 0 = cgwZ A b x₀ 0 := rfl

/-- The iterate update of the Concus–Golub–Widlund algorithm: $x_{j+1} = x_j + \alpha_j p_j$. -/
theorem cgwX_succ (j : ℕ) :
    cgwX A b x₀ (j + 1) = cgwX A b x₀ j + cgwAlpha A b x₀ j • cgwP A b x₀ j := by
  rw [cgwX, cgw_succ]; rfl

/-- The residual update of the Concus–Golub–Widlund algorithm: $r_{j+1} = r_j - \alpha_j A p_j$. -/
theorem cgwR_succ (j : ℕ) :
    cgwR A b x₀ (j + 1) = cgwR A b x₀ j - cgwAlpha A b x₀ j • op A (cgwP A b x₀ j) := by
  rw [cgwR, cgw_succ]; rfl

private theorem cgwR_succ_eq (j : ℕ) :
    cgwR A b x₀ (j + 1) = pcgStepR A (cgwM A) (cgw A b x₀ j) := by
  rw [cgwR, cgw_succ]; rfl

/-- The direction update of the Concus–Golub–Widlund algorithm: $p_{j+1} = z_{j+1} + \beta_j p_j$,
with $\beta_j$ the negative of the coefficient of Algorithm 9.1. -/
theorem cgwP_succ (j : ℕ) :
    cgwP A b x₀ (j + 1) = cgwZ A b x₀ (j + 1) + cgwBeta A b x₀ j • cgwP A b x₀ j := by
  rw [cgwBeta, neg_smul, ← sub_eq_add_neg, cgwZ, cgwR_succ_eq, cgwP, cgw_succ]
  rfl

/-- **Section 9.6** of [saad2003iterative], the residual. For all $A$, $b$, $x_0$ and $j$, the
residual of the Concus–Golub–Widlund algorithm is the true residual: $r_j = b - A x_j$.

This is the first step towards the identification of the iterate with the Galerkin iterate. -/
theorem cgw_residual_eq (j : ℕ) : cgwR A b x₀ j = b - op A (cgwX A b x₀ j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [cgwR_succ, cgwX_succ, ih, map_add, map_smul]
      abel

/-- **Section 9.6** of [saad2003iterative], the coefficients of the Concus–Golub–Widlund algorithm.
For all $A$, $b$, $x_0$ and $j$,
$$\alpha_j = \frac{(r_j, z_j)}{(A p_j, p_j)}, \qquad \beta_j = -\frac{(r_{j+1}, z_{j+1})}{(r_j,
  z_j)}.$$
The step length is that of Algorithm 9.1, and the direction coefficient is its negative.

The sign comes from the skew-adjointness of $M^{-1} N$, through $(M^{-1} A z_{j+1}, p_j)_M =
-(z_{j+1}, M^{-1} A p_j)_M$ for the relevant vectors.

**Generalization.** The recurrences are total for all matrices and indices, including an undefined
quotient. The coefficient order follows the conjugate-linear-first convention and recovers the real
recurrence. The negative sign of beta follows the printed CGW formula.
-/
theorem cgw_alpha (j : ℕ) :
    cgwAlpha A b x₀ j
        = inner 𝕜 (cgwZ A b x₀ j) (cgwR A b x₀ j)
            / inner 𝕜 (cgwP A b x₀ j) (op A (cgwP A b x₀ j))
      ∧ cgwBeta A b x₀ j
        = -(inner 𝕜 (cgwZ A b x₀ (j + 1)) (cgwR A b x₀ (j + 1))
            / inner 𝕜 (cgwZ A b x₀ j) (cgwR A b x₀ j)) := by
  refine ⟨rfl, ?_⟩
  rw [cgwBeta, pcgStepBeta_def, cgwZ, cgwZ, cgwR_succ_eq]
  rfl

end Algorithm

/-! ### The Galerkin property of the Concus–Golub–Widlund iterate (real case) -/

section Galerkin

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-- **Section 9.6** of [saad2003iterative], the hypothesis of the backbone recurrence. Let
$A \in \mathbb{R}^{n \times n}$, and let its symmetric part $M$ be a preconditioner. Then
$B = M^{-1} A$ is shifted skew-adjoint for the $M$-inner product: $B + B^* = 2I$, where $B^*$ is
the adjoint for the $M$-inner product.

This is `SaadSparse.Chapter09.adjoint_energyEnd` over $\mathbb{R}$, in the form
`LinearMap.IsShiftedSkewAdjoint` that `CGW.iterate` needs.

**Generalization.** The skew-adjoint fact is stated for an arbitrary skew-Hermitian matrix and
energy preconditioner. The specialized formulas explicitly assume a valid positive definite energy
inner product, and identify the adjoint as $2I-M^{-1}A$.
-/
theorem isShiftedSkewAdjoint_energyEnd
    (hM : Krylov.IsPreconditioner (op (cgwM A)) (op (cgwM A)⁻¹)) :
    (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A)).IsShiftedSkewAdjoint := by
  intro u v
  have h := adjoint_energyEnd (A := A) hM u v
  rw [inner_sub_right, real_inner_smul_right] at h
  linarith

/-- **Section 9.6** of [saad2003iterative], the algorithm as a backbone recurrence. Let
$A \in \mathbb{R}^{n \times n}$, and let its symmetric part $M$ be a preconditioner. Let
$(\xi_j, \rho_j, \pi_j)$ be the iterate, the residual and the search direction of the backbone
recurrence `CGW.iterate` for $M^{-1} A$ on the space with the $M$-inner product, with right-hand
side $M^{-1} b$ and initial guess $x_0$. Then for all $j$,
$$x_j = \xi_j, \qquad z_j = \rho_j, \qquad p_j = \pi_j.$$

The iterate and the search direction carry over unchanged. The preconditioned residual
$z_j = M^{-1} r_j$ plays the part of the backbone residual. Each vector is moved to the
$M$-inner product space by `hM.toEnergy`.

**Reading.** The update formulas are available over complex scalars, but the equivalence with the
shifted-skew CGW iteration and the Galerkin theorem are over the reals with a valid energy
preconditioner.
-/
theorem cgw_eq_CGW_iterate (hM : Krylov.IsPreconditioner (op (cgwM A)) (op (cgwM A)⁻¹))
    (b x₀ : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    hM.toEnergy (cgwX A b x₀ j)
        = (CGW.iterate (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
            (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀) j).x ∧
      hM.toEnergy (cgwZ A b x₀ j)
        = (CGW.iterate (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
            (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀) j).r ∧
      hM.toEnergy (cgwP A b x₀ j)
        = (CGW.iterate (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
            (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀) j).p := by
  have hnum : ∀ k : ℕ,
      inner ℝ (hM.toEnergy (cgwZ A b x₀ k)) (hM.toEnergy (cgwZ A b x₀ k))
        = inner ℝ (op (cgwM A)⁻¹ (cgwR A b x₀ k)) (cgwR A b x₀ k) := by
    intro k
    rw [WithEnergy.inner_equiv, _root_.energyInner]
    simp only [cgwZ]
    rw [hM.apply_inv]
    exact real_inner_comm _ _
  have hBapply : ∀ y : EuclideanSpace ℝ (Fin n),
      hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) (hM.toEnergy y)
        = hM.toEnergy (op (cgwM A)⁻¹ (op A y)) := by
    intro y
    rw [Krylov.IsPreconditioner.energyEnd_apply, LinearMap.comp_apply]
  have hinit : hM.toEnergy (op (cgwM A)⁻¹ (b - op A x₀))
      = hM.toEnergy (op (cgwM A)⁻¹ b)
        - hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) (hM.toEnergy x₀) := by
    rw [hBapply, ← map_sub, ← map_sub]
  induction j with
  | zero => exact ⟨rfl, hinit, hinit⟩
  | succ j ih =>
    obtain ⟨hx, hr, hp⟩ := ih
    have halpha : cgwAlpha A b x₀ j
        = CGW.alpha (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
          (CGW.iterate (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
            (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀) j) := by
      rw [CGW.alpha, ← hr, ← hp, hnum j, hM.inner_energyEnd_right (op A)]
      rfl
    have hr' : hM.toEnergy (cgwZ A b x₀ (j + 1))
        = (CGW.iterate (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
            (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀) (j + 1)).r := by
      rw [CGW.iterate_succ_r, ← hr, ← hp, ← halpha, hBapply]
      simp only [cgwZ, cgwR_succ, map_sub, map_smul]
    have hbeta : cgwBeta A b x₀ j
        = CGW.beta (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
          (CGW.iterate (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
            (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀) j) := by
      rw [CGW.beta_iterate, ← hr', ← hr, hnum (j + 1), hnum j, cgwBeta, pcgStepBeta_def,
        ← cgwR_succ_eq]
      rfl
    refine ⟨?_, hr', ?_⟩
    · rw [CGW.iterate_succ_x, ← hx, ← hp, ← halpha, cgwX_succ, map_add, map_smul]
    · rw [CGW.iterate_succ_p, ← hr', ← hp, ← hbeta, cgwP_succ, map_add, map_smul]

/-- **Section 9.6** of [saad2003iterative], the Galerkin property. Let
$A \in \mathbb{R}^{n \times n}$, and let its symmetric part $M$ be a preconditioner. Then for
all $b, x_0$ and $j$, the iterate $x_j$ of the Concus–Golub–Widlund algorithm is the Galerkin
iterate of $Ax = b$ over $x_0 + \mathcal{K}_j(M^{-1} A, M^{-1} r_0)$, with $r_0 = b - A x_0$:
$$x_j - x_0 \in \mathcal{K}_j(M^{-1} A, M^{-1} r_0), \qquad b - A x_j \perp \mathcal{K}_j(M^{-1}
  A, M^{-1} r_0).$$
Equivalently, the preconditioned residual $M^{-1}(b - A x_j)$ is $M$-orthogonal to that space,
so the algorithm is a projection method for $M^{-1} A x = M^{-1} b$ in the $M$-inner product.

This is the only optimality property of the algorithm. It comes with no minimization, because
$M^{-1} A$ is not self-adjoint for the $M$-inner product. The statement holds over $\mathbb{R}$
only. Over $\mathbb{C}$ the recurrence is not a projection method: the step length $\alpha_j$ is
complex, and the cancellation that makes the directions $M^{-1} A$-conjugate fails already at
$j = 1$; see the module doc comment of `Numlib.Krylov.CGW`.

**Reading.** The update formulas are available over complex scalars, but the equivalence with the
shifted-skew CGW iteration and the Galerkin theorem are over the reals with a valid energy
preconditioner.
-/
theorem cgw_isGalerkinIterate (hM : Krylov.IsPreconditioner (op (cgwM A)) (op (cgwM A)⁻¹))
    (b x₀ : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    IsGalerkin (op A) b x₀
      (Chapter06.krylov ((cgwM A)⁻¹ * A) (op (cgwM A)⁻¹ (b - op A x₀)) j) (cgwX A b x₀ j) := by
  have hgal : IsGalerkin (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
      (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀)
      (Krylov.subspace (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
        (hM.toEnergy (op (cgwM A)⁻¹ b)
          - hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) (hM.toEnergy x₀)) j)
      (CGW.iterate (hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A))
        (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀) j).x :=
    CGW.isGalerkinIterate (hM.toEnergy (op (cgwM A)⁻¹ b)) (hM.toEnergy x₀)
      (isShiftedSkewAdjoint_energyEnd hM) j
  rw [show hM.toEnergy (op (cgwM A)⁻¹ b)
        - hM.energyEnd (op (cgwM A)⁻¹ ∘ₗ op A) (hM.toEnergy x₀)
      = hM.toEnergy (op (cgwM A)⁻¹ (b - op A x₀)) by
      rw [Krylov.IsPreconditioner.energyEnd_apply, LinearMap.comp_apply, ← map_sub, ← map_sub],
    hM.subspace_energyEnd, ← (cgw_eq_CGW_iterate hM b x₀ j).1] at hgal
  rw [Chapter06.krylov_eq, op_mul]
  exact (hM.isGalerkin_energyEnd_iff (op A) b x₀ _ _).1 hgal

end Galerkin


end SaadSparse.Chapter09
