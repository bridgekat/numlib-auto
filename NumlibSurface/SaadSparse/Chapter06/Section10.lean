/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Numlib.Eigen.Normal
import Numlib.Krylov.Arnoldi
import Numlib.Krylov.Subspace
import NumlibSurface.SaadSparse.Chapter06.Section09

/-!
# Saad, Section 6.10: Optimality and the Faber–Manteuffel condition

This module formalizes Section 6.10 of [saad2003iterative], which asks for which matrices $A$ the
Arnoldi process is a short recurrence. Proposition 6.22 shows that if
$A^T v \in \mathcal{K}_s(A, v)$ for every vector $v$, then the Arnoldi coefficients satisfy the band
condition (6.108), $h_{ij} = 0$ for $i + s \le j$. Then the incomplete orthogonalization process of
Algorithm 6.6 with window $s$ drops nothing, and IOM(s) and DIOM(s) compute the FOM approximation.
The section then introduces $\nu(A)$, the least degree of a polynomial $q$ with $A^H = q(A)$, and
the class $CG(s)$ of Faber and Manteuffel: the matrices for which the Arnoldi process is an $s$-term
recurrence for every starting vector. A matrix with $A^H = q(A)$ is normal, and conversely every
normal matrix has such a $q$. Lemma 6.23 (Faber and Manteuffel) states that
$A^H v \in \mathcal{K}_s(A, v)$ for every $v$ if and only if $A$ is normal and $\nu(A) \le s - 1$.
Theorem 6.24 characterizes $CG(s)$; only its sufficiency half is formalized here.

The band condition is the backbone theorem `Arnoldi.coeff_eq_zero_of_adjoint_mem` of
`Numlib.Krylov.Arnoldi`. The algorithms IOP, IOM and DIOM are those of
`NumlibSurface.SaadSparse.Chapter06.Section04`. The facts about normal matrices specialize
`Numlib.Eigen.Normal`.

## Main definitions

* Section 6.10, `SaadSparse.Chapter06.ν`: $\nu(A)$, the least degree of a polynomial $q$ with
  $q(A) = A^H$.
* Section 6.10, `SaadSparse.Chapter06.IsCGs`: the class $CG(s)$ of matrices whose Arnoldi
  coefficients vanish outside a band of width $s$, up to the grade of every unit starting vector.

## Main results

* Proposition 6.22, `SaadSparse.Chapter06.proposition_6_22`: if $A^T v \in \mathcal{K}_s(A, v)$ for
  every $v$, then (6.108) holds, IOP(s) is the full Arnoldi process, and IOM(s) and DIOM(s) compute
  the FOM iterate.
* Section 6.10, `SaadSparse.Chapter06.isStarNormal_of_exists_aeval`: if $A^H = q(A)$ for a
  polynomial $q$, then $A$ is normal.
* Section 6.10, `SaadSparse.Chapter06.exists_aeval_eq_conjTranspose`: a normal $A$ satisfies
  $A^H = q(A)$ for a polynomial $q$ of degree at most $n - 1$.
* Lemma 6.23, `SaadSparse.Chapter06.lemma_6_23`: for $s \ge 1$, $A^H v \in \mathcal{K}_s(A, v)$ for
  every $v$ if and only if $A$ is normal and $\nu(A) \le s - 1$.
* Theorem 6.24, `SaadSparse.Chapter06.isCGs_of_natDegree_minpoly_le_or_isStarNormal`: if the minimal
  polynomial of $A$ has degree at most $s$, or $A$ is normal with $\nu(A) \le s - 1$, then
  $A \in CG(s)$.
* Section 6.10, `SaadSparse.Chapter06.nu_le_one_iff`: a normal $A$ has $\nu(A) \le 1$ if and only if
  $A$ is a scalar matrix, or Hermitian, or of the form $e^{i\theta}(\rho I + B)$ with $\theta, \rho$
  real and $B$ skew-Hermitian.

## Proof outline

For Lemma 6.23, an eigenvector $v$ of $A$ has $\mathcal{K}_s(A, v) \subseteq
\operatorname{span}\{v\}$, so $v$ is also an eigenvector of $A^H$, and $A$ is normal by Lemma 1.15.
Then a sum $w$ of one eigenvector from each eigenspace gives a polynomial $q$ of degree at most
$s - 1$ with $q(\lambda) = \bar\lambda$ at every eigenvalue $\lambda$, and hence $q(A) = A^H$. The
converse of the normality remark builds $q$ by Lagrange interpolation of $z \mapsto \bar z$ at the
eigenvalues, and reduces it modulo the characteristic polynomial.

## Conventions

* Proposition 6.22 is stated over $\mathbb{R}$ with $A^T$, and the material on normality is stated
  over $\mathbb{C}$ with $A^H$, as in the book. The lemmas on the band condition hold over any
  `RCLike` field.
* The Arnoldi vectors and coefficients are indexed from $0$:
  `SaadSparse.Chapter06.arnoldiCoeff A v i j` is the book's $h_{i+1,j+1}$. The band condition
  $i + s \le j$ reads the same in both indexings.

## Implementation notes

* $\nu(A)$ is an infimum of a set of natural numbers. The set is empty when no polynomial in $A$
  equals $A^H$, that is, when $A$ is not normal, and then $\nu(A) = 0$. For this reason the results
  about $\nu(A)$ assume that $A$ is normal.
* The three cases of `SaadSparse.Chapter06.nu_le_one_iff` are those of the book, and they are not
  disjoint: the third contains the other two. The backbone theorem
  `Matrix.exists_natDegree_le_one_aeval_eq_conjTranspose_iff` gives the sharper equivalence with no
  normality hypothesis.

## Deviations from the source

* **Lemma 6.23** (generalization). The book assumes that $A$ is nonsingular. The proof here does not
  use this, and the hypothesis is omitted. See `SaadSparse.Chapter06.lemma_6_23`.
* **Lemma 6.23** (reading). The book leaves $s \ge 1$ implicit. The statement assumes $0 < s$, which
  is necessary because $s - 1$ is truncated subtraction of natural numbers. See
  `SaadSparse.Chapter06.lemma_6_23`.

## Not formalized

* **Theorem 6.24, necessity.** The direction that $A \in CG(s)$ forces one of the two conditions is
  the Faber–Manteuffel theorem proper. The book states it without proof, and the known proofs (Faber
  and Manteuffel, 1984; Liesen and Strakoš, 2008) are research papers, not textbook arguments.
-/

open Polynomial

open scoped ComplexOrder Matrix

namespace SaadSparse.Chapter06

section Band

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

variable (A : Matrix (Fin n) (Fin n) 𝕜) (v : EuclideanSpace 𝕜 (Fin n))

/-! ### Equation (6.108): the band structure of the Arnoldi coefficients -/

/-- **Equation (6.108)** of [saad2003iterative]. Let $A$ be an $n \times n$ matrix, let
$s \in \mathbb{N}$, and suppose that $A^H w \in \mathcal{K}_s(A, w)$ for every vector $w$. Let
$v$ be a unit vector. Then the Arnoldi coefficients of $A$ with starting vector $v$ satisfy
$h_{ij} = 0$ whenever $i + s \le j$.

Here $A^H$ is the adjoint `LinearMap.adjoint (SaadSparse.Chapter06.op A)`, and the coefficients
are `SaadSparse.Chapter06.arnoldiCoeff`. This is the backbone theorem
`Arnoldi.coeff_eq_zero_of_adjoint_mem`. Its case $s = 2$ is the tridiagonality of the symmetric
Lanczos process. -/
theorem arnoldiCoeff_eq_zero_of_adjoint_mem {s : ℕ}
    (hs : ∀ w : 𝔼, LinearMap.adjoint (op A) w ∈ krylov A w s) (hv : ‖v‖ = 1) {i j : ℕ}
    (h : i + s ≤ j) : arnoldiCoeff A v i j = 0 := by
  rw [arnoldiCoeff_eq A v hv]
  refine Arnoldi.coeff_eq_zero_of_adjoint_mem (op A) v
    (LinearMap.isAdjointPair_inner (op A)) (fun w => ?_) h
  rw [← krylov_eq]
  exact hs w

/-! ### The truncated inner loop of Algorithm 6.6 under a band condition -/

/-- The modified Gram–Schmidt loop subtracts, at step $i$, the projection of the current vector on
$u_i$ with its running coefficient; this form needs no orthogonality of the $u_i$, unlike
`SaadSparse.Chapter06.mgsW_eq_sub_sum`. -/
private theorem mgsW_eq_sub_sum' (u : ℕ → 𝔼) (w₀ : 𝔼) (k : ℕ) :
    mgsW u w₀ k = w₀ - ∑ i ∈ Finset.range k, inner 𝕜 (u i) (mgsW u w₀ i) • u i := by
  induction k with
  | zero => simp [mgsW]
  | succ k ih =>
    rw [mgsW_succ, Finset.sum_range_succ]
    nth_rewrite 1 [ih]
    abel

/-- The truncated loop of Algorithm 6.6 equals the full loop of Algorithm 6.2 when all the
coefficients that it skips vanish. -/
private theorem iopW_eq_mgsW_of_band {u : ℕ → 𝔼} {lo : ℕ} (w₀ : 𝔼)
    (h : ∀ i < lo, inner 𝕜 (u i) (mgsW u w₀ i) = 0) (N : ℕ) :
    iopW u lo w₀ N = mgsW u w₀ N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [iopW_succ, iopCoeffOf, ih, mgsW_succ]
    by_cases hlo : lo ≤ N
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hlo)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hlo), h N (by omega), zero_smul]

variable {A v}

private theorem inner_mgsW_arnoldiMGS_eq_zero {s : ℕ} (hv : ‖v‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A v i j = 0) (j : ℕ) :
    ∀ i < j + 1 - s,
      inner 𝕜 (arnoldiMGS A v i) (mgsW (arnoldiMGS A v) (op A (arnoldiMGS A v j)) i) = 0 := by
  have ho : ∀ a c : ℕ, a ≠ c → inner 𝕜 (arnoldiMGS A v a) (arnoldiMGS A v c) = 0 := by
    intro a c hac
    rw [arnoldiMGS_eq_arnoldiCGS A v hv, arnoldiMGS_eq_arnoldiCGS A v hv]
    exact inner_arnoldiCGS_eq_zero A v hv hac
  intro i hi
  rw [inner_mgsW_self ho, arnoldiMGS_eq_arnoldiCGS A v hv, arnoldiMGS_eq_arnoldiCGS A v hv]
  exact hband i j (by omega)

/-- Let $v$ be a unit vector, and suppose that the Arnoldi coefficients of $A$ with starting vector
$v$ satisfy the band condition (6.108), $h_{ij} = 0$ for $i + s \le j$. Then the incomplete
orthogonalization process of Algorithm 6.6 with window $s$ produces the same vectors as the
modified Gram–Schmidt Arnoldi process of Algorithm 6.2, because the terms that it drops are
zero. This is the algorithmic content of Proposition 6.22 of [saad2003iterative]. -/
theorem iop_eq_arnoldiMGS_of_band {s : ℕ} (hv : ‖v‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A v i j = 0) (j : ℕ) :
    iop A v s j = arnoldiMGS A v j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => rw [iop_zero, arnoldiMGS_zero]
    | succ j =>
      have hprev : ∀ i < j + 1, iop A v s i = arnoldiMGS A v i := fun i hi => ih i hi
      have hw : iopVecW A v s j = arnoldiMGSW A v j := by
        rw [iopVecW, arnoldiMGSW, hprev j j.lt_succ_self,
          iopW_congr (v := iop A v s) (v' := arnoldiMGS A v) (j + 1 - s)
            (op A (arnoldiMGS A v j)) hprev]
        exact iopW_eq_mgsW_of_band _ (inner_mgsW_arnoldiMGS_eq_zero hv hband j) (j + 1)
      rw [iop_succ, arnoldiMGS_succ, hw]

private theorem iop_eq_arnoldiMGS_fun {s : ℕ} (hv : ‖v‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A v i j = 0) :
    iop A v s = arnoldiMGS A v :=
  funext (iop_eq_arnoldiMGS_of_band hv hband)

/-- Let $v$ be a unit vector, and suppose that the Arnoldi coefficients of $A$ with starting vector
$v$ satisfy $h_{ij} = 0$ for $i + s \le j$. Then the coefficients
`SaadSparse.Chapter06.iopCoeff A v s i j` of Algorithm 6.6 with window $s$ equal the Arnoldi
coefficients $h_{ij}$ for all $i$ and $j$. -/
theorem iopCoeff_eq_arnoldiCoeff_of_band {s : ℕ} (hv : ‖v‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A v i j = 0) (i j : ℕ) :
    iopCoeff A v s i j = arnoldiCoeff A v i j := by
  have hfun := iop_eq_arnoldiMGS_fun hv hband
  have hiw : ∀ N, iopW (arnoldiMGS A v) (j + 1 - s) (op A (arnoldiMGS A v j)) N
      = mgsW (arnoldiMGS A v) (op A (arnoldiMGS A v j)) N := fun N =>
    iopW_eq_mgsW_of_band _ (inner_mgsW_arnoldiMGS_eq_zero hv hband j) N
  rw [← arnoldiMGSCoeff_eq_arnoldiCoeff A v hv, iopCoeff, arnoldiMGSCoeff, iopVecW, hfun,
    arnoldiMGSW, hiw]
  split_ifs with h1 h2
  · rw [iopCoeffOf, hiw]
    by_cases hlo : j + 1 - s ≤ i
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hlo)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hlo),
        inner_mgsW_arnoldiMGS_eq_zero hv hband j i (by omega)]
  · rfl
  · rfl

end Band

section BandFOM

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

variable {A : Matrix (Fin n) (Fin n) 𝕜} {b x₀ : EuclideanSpace 𝕜 (Fin n)} {s : ℕ}

/-- Suppose that $\|v_1\| = 1$ and that the Arnoldi coefficients of $A$ with starting vector
$v_1 = r_0 / \|r_0\|$ satisfy $h_{ij} = 0$ for $i + s \le j$. Then Algorithm 6.6 with window $s$
and Algorithm 6.1 build the same basis matrix $V_m$, for every $m$. -/
theorem VI_eq_V (hv : ‖v₁ A b x₀‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A (v₁ A b x₀) i j = 0) (m : ℕ) :
    VI A (v₁ A b x₀) s m = V A (v₁ A b x₀) m := by
  rw [VI, V, iop_eq_arnoldiMGS_fun hv hband,
    funext fun l => arnoldiMGS_eq_arnoldiCGS A (v₁ A b x₀) hv l]

/-- Suppose that $\|v_1\| = 1$ and that the Arnoldi coefficients of $A$ with starting vector
$v_1 = r_0 / \|r_0\|$ satisfy $h_{ij} = 0$ for $i + s \le j$. Then Algorithm 6.6 with window $s$
and Algorithm 6.1 build the same Hessenberg matrix $H_m$, for every $m$. -/
theorem HI_eq_H (hv : ‖v₁ A b x₀‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A (v₁ A b x₀) i j = 0) (m : ℕ) :
    HI A (v₁ A b x₀) s m = H A (v₁ A b x₀) m := by
  ext i j
  rw [HI_apply, H_apply, iopCoeff_eq_arnoldiCoeff_of_band hv hband]

/-- **IOM(s) is FOM** under the band condition. Suppose that $\|v_1\| = 1$ and that the Arnoldi
coefficients of $A$ with starting vector $v_1 = r_0 / \|r_0\|$ satisfy $h_{ij} = 0$ for
$i + s \le j$. Then, for every $m$, the iterate $x_m$ of IOM(s) (Algorithm 6.7) equals the
iterate $x_m$ of FOM (Algorithm 6.4), both with exactly $m$ steps: the two methods solve the
same system in the same basis. -/
theorem iomFixed_eq_fomFixed_of_band (hv : ‖v₁ A b x₀‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A (v₁ A b x₀) i j = 0) (m : ℕ) :
    iomFixed A b x₀ s m = fomFixed A b x₀ m := by
  rw [iomFixed, fomFixed, iomY, fomY, HI_eq_H hv hband, VI_eq_V hv hband]

/-- **DIOM(s) is mathematically equivalent to FOM** under the band condition. Suppose that
$\|v_1\| = 1$, that the Arnoldi coefficients of $A$ with starting vector $v_1 = r_0 / \|r_0\|$
satisfy $h_{ij} = 0$ for $i + s \le j$, and that the first $m$ pivots $u_{ll}$, $l < m$, of the
LU factorization of the Hessenberg matrix of Algorithm 6.6 are nonzero. Then the iterate $x_m$
of DIOM(s) (Algorithm 6.8) equals the iterate $x_m$ of FOM with exactly $m$ steps. This is the
conclusion of Proposition 6.22 of [saad2003iterative].

The pivots are `SaadSparse.Chapter06.dioU`. DIOM divides by them, so the algorithm is defined
only when they are nonzero. -/
theorem diom_eq_fomFixed_of_band (hv : ‖v₁ A b x₀‖ = 1)
    (hband : ∀ i j : ℕ, i + s ≤ j → arnoldiCoeff A (v₁ A b x₀) i j = 0) {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) s) l l ≠ 0) :
    diom A b x₀ s m = fomFixed A b x₀ m := by
  rw [diom_eq_iomFixed A b x₀ s hpiv, iomFixed_eq_fomFixed_of_band hv hband]

end BandFOM

/-! ### Proposition 6.22, in the real setting of the book -/

section BookResults

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)

/-- Over $\mathbb{R}$, the adjoint of $x \mapsto Ax$ is $x \mapsto A^T x$. -/
private theorem adjoint_op_eq :
    LinearMap.adjoint (op A) = op Aᵀ := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A,
    Matrix.conjTranspose_eq_transpose_of_trivial]

/-- **Proposition 6.22** of [saad2003iterative]. Let $A$ be a real $n \times n$ matrix and
$s \in \mathbb{N}$, and assume that $A^T v \in \mathcal{K}_s(A, v)$ for every vector
$v \in \mathbb{R}^n$. Then DIOM(s) is mathematically equivalent to FOM. In detail:

1. for every unit vector $v$, the Arnoldi coefficients with starting vector $v$ satisfy (6.108),
   $h_{ij} = 0$ for $i + s \le j$;
2. for every unit vector $v$, the incomplete orthogonalization process of Algorithm 6.6 with
   window $s$ produces the same vectors as the modified Gram–Schmidt Arnoldi process of
   Algorithm 6.2;
3. for $b, x_0 \in \mathbb{R}^n$ with $r_0 = b - Ax_0 \neq 0$, and $m \in \mathbb{N}$ such that
   the first $m$ pivots of the LU factorization of the Hessenberg matrix of Algorithm 6.6 are
   nonzero, the iterates $x_m$ of IOM(s) and of DIOM(s) both equal the iterate $x_m$ of FOM with
   exactly $m$ steps.

The hypothesis $r_0 \neq 0$ makes $v_1 = r_0 / \|r_0\|$ a unit vector. The pivots are
`SaadSparse.Chapter06.dioU`, by which DIOM divides; the book does not mention them. The proof
applies `SaadSparse.Chapter06.arnoldiCoeff_eq_zero_of_adjoint_mem`,
`SaadSparse.Chapter06.iomFixed_eq_fomFixed_of_band` and
`SaadSparse.Chapter06.diom_eq_fomFixed_of_band`. -/
theorem proposition_6_22 {s : ℕ} (hs : ∀ w : EuclideanSpace ℝ (Fin n), op Aᵀ w ∈ krylov A w s)
    (b x₀ : EuclideanSpace ℝ (Fin n)) (hr : r₀ A b x₀ ≠ 0) {m : ℕ}
    (hpiv : ∀ l, l < m → dioU (iopCoeff A (v₁ A b x₀) s) l l ≠ 0) :
    (∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → ∀ i j : ℕ, i + s ≤ j →
        arnoldiCoeff A v i j = 0) ∧
      (∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → iop A v s = arnoldiMGS A v) ∧
      iomFixed A b x₀ s m = fomFixed A b x₀ m ∧ diom A b x₀ s m = fomFixed A b x₀ m := by
  have hadj : ∀ w : EuclideanSpace ℝ (Fin n), LinearMap.adjoint (op A) w ∈ krylov A w s := by
    intro w
    rw [adjoint_op_eq A]
    exact hs w
  have h108 : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → ∀ i j : ℕ, i + s ≤ j →
      arnoldiCoeff A v i j = 0 :=
    fun v hv _ _ h => arnoldiCoeff_eq_zero_of_adjoint_mem A v hadj hv h
  have hv : ‖v₁ A b x₀‖ = 1 := norm_v₁ A b x₀ hr
  exact ⟨h108, fun v hvu => iop_eq_arnoldiMGS_fun hvu (h108 v hvu),
    iomFixed_eq_fomFixed_of_band hv (h108 _ hv) m,
    diom_eq_fomFixed_of_band hv (h108 _ hv) hpiv⟩

end BookResults

/-! ### Section 6.10: $\nu(A)$, the class $CG(s)$, and normality -/

section Normal

variable {n : ℕ}

local notation "ℂ𝔼" => EuclideanSpace ℂ (Fin n)

/-- **Section 6.10** of [saad2003iterative], definition of $\nu(A)$. For a complex $n \times n$
matrix $A$, $\nu(A)$ is the least degree of a polynomial $q$ with $q(A) = A^H$.

If no polynomial in $A$ equals $A^H$, the set of degrees is empty and $\nu(A) = 0$, because the
infimum of the empty set of natural numbers is $0$ in Lean. This happens exactly when $A$ is not
normal (`SaadSparse.Chapter06.isStarNormal_of_exists_aeval` and
`SaadSparse.Chapter06.exists_aeval_eq_conjTranspose`). -/
noncomputable def ν (A : Matrix (Fin n) (Fin n) ℂ) : ℕ :=
  sInf {d : ℕ | ∃ q : ℂ[X], q.natDegree = d ∧ aeval A q = Aᴴ}

/-- **Section 6.10** of [saad2003iterative], the class $CG(s)$ of Faber and Manteuffel. A complex
$n \times n$ matrix $A$ is **in $CG(s)$** if, for every unit starting vector $v_1$, the Arnoldi
coefficients satisfy $h_{ij} = 0$ for all $i + s \le j \le \mu - 1$, where $\mu$ is the grade of
$v_1$ with respect to $A$. Then the Arnoldi process is an $s$-term recurrence up to the grade of
$v_1$.

The indices are $0$-based, and the grade is `SaadSparse.Chapter06.grade`. -/
def IsCGs (A : Matrix (Fin n) (Fin n) ℂ) (s : ℕ) : Prop :=
  ∀ v₁ : ℂ𝔼, ‖v₁‖ = 1 → ∀ i j : ℕ, i + s ≤ j → j + 1 ≤ grade A v₁ → arnoldiCoeff A v₁ i j = 0

/-- Every polynomial in $A$ commutes with $A$. -/
private theorem commute_aeval_self (A : Matrix (Fin n) (Fin n) ℂ) (q : ℂ[X]) :
    Commute (aeval A q) A := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add]; exact hp.add_left hr
  | monomial k c =>
    rw [Polynomial.aeval_monomial]
    have h1 : Commute (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) c) A := Algebra.commutes c A
    exact Commute.mul_left h1 ((Commute.refl A).pow_left k)

/-- **Section 6.10** of [saad2003iterative], first remark on normality. Let $A$ be a complex
$n \times n$ matrix. If $A^H = q(A)$ for some polynomial $q$, then $A$ is normal.

The reason is that $A$ commutes with every polynomial in $A$, and so with $A^H$. -/
theorem isStarNormal_of_exists_aeval {A : Matrix (Fin n) (Fin n) ℂ}
    (h : ∃ q : ℂ[X], aeval A q = Aᴴ) : IsStarNormal A := by
  obtain ⟨q, hq⟩ := h
  refine ⟨?_⟩
  rw [Matrix.star_eq_conjTranspose, ← hq]
  exact commute_aeval_self A q

/-- **Section 6.10** of [saad2003iterative], converse of the remark on normality. Every normal
complex $n \times n$ matrix $A$ satisfies $A^H = q(A)$ for some polynomial $q$.

This is the backbone theorem `Matrix.IsStarNormal.exists_aeval_eq_conjTranspose`. It builds $q$
by Lagrange interpolation of $z \mapsto \bar z$ at the eigenvalues of $A$, so that
$q(\lambda_j) = \bar\lambda_j$, without the unitary diagonalization $A = Q \Lambda Q^H$. -/
theorem exists_aeval_eq_conjTranspose_of_isStarNormal {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsStarNormal A) : ∃ q : ℂ[X], aeval A q = Aᴴ :=
  Matrix.IsStarNormal.exists_aeval_eq_conjTranspose hA

/-- **Section 6.10** of [saad2003iterative], second remark on normality. Every normal complex
$n \times n$ matrix $A$ satisfies $A^H = q(A)$ for some polynomial $q$ of degree at most
$n - 1$.

The degree bound comes from reducing any polynomial with $q(A) = A^H$ modulo the characteristic
polynomial of $A$. That polynomial is monic of degree $n$ and annihilates $A$ by the
Cayley–Hamilton theorem, so the reduction does not change $q(A)$. For $n = 0$ the bound $n - 1$
is $0$, by truncated subtraction. -/
theorem exists_aeval_eq_conjTranspose {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) :
    ∃ q : ℂ[X], q.natDegree ≤ n - 1 ∧ aeval A q = Aᴴ := by
  obtain ⟨q, hq⟩ := exists_aeval_eq_conjTranspose_of_isStarNormal hA
  have hmonic := A.charpoly_monic
  have hlt : (q %ₘ A.charpoly).degree < A.charpoly.degree := degree_modByMonic_lt q hmonic
  have hcd : A.charpoly.degree = (n : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, A.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  refine ⟨q %ₘ A.charpoly, ?_, ?_⟩
  · rcases eq_or_ne (q %ₘ A.charpoly) 0 with h0 | h0
    · simp [h0]
    · rw [Polynomial.degree_eq_natDegree h0, hcd] at hlt
      have hn : (q %ₘ A.charpoly).natDegree < n := by exact_mod_cast hlt
      omega
  · rw [aeval_modByMonic_eq_self_of_root (by rw [Matrix.aeval_self_charpoly]), hq]

/-! ### Lemma 6.23 -/

/-- For a normal complex matrix $A$, the infimum that defines $\nu(A)$ is attained: some polynomial
$q$ of degree exactly $\nu(A)$ satisfies $q(A) = A^H$. -/
theorem exists_natDegree_eq_nu {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) :
    ∃ q : ℂ[X], q.natDegree = ν A ∧ aeval A q = Aᴴ := by
  have hne : {d : ℕ | ∃ q : ℂ[X], q.natDegree = d ∧ aeval A q = Aᴴ}.Nonempty := by
    obtain ⟨q, hq⟩ := exists_aeval_eq_conjTranspose_of_isStarNormal hA
    exact ⟨q.natDegree, q, rfl, hq⟩
  exact Nat.sInf_mem hne

/-- Every polynomial $q$ with $q(A) = A^H$ has degree at least $\nu(A)$. -/
theorem nu_le_natDegree {A : Matrix (Fin n) (Fin n) ℂ} {q : ℂ[X]} (hq : aeval A q = Aᴴ) :
    ν A ≤ q.natDegree :=
  Nat.sInf_le ⟨q, rfl, hq⟩

/-- **Lemma 6.23** of [saad2003iterative] (Faber and Manteuffel). Let $A$ be a complex $n \times n$
matrix and let $s \ge 1$. Then $A^H v \in \mathcal{K}_s(A, v)$ for every vector
$v \in \mathbb{C}^n$ if and only if $A$ is normal and $\nu(A) \le s - 1$.

**Generalization.** The book assumes that $A$ is nonsingular. The proof here does not use this,
so the hypothesis is omitted.

**Reading.** The book leaves $s \ge 1$ implicit. The statement assumes $0 < s$, and the
assumption is necessary: $s - 1$ is truncated subtraction of natural numbers, so for $s = 0$ the
right-hand side holds for $A = I$ (where $\nu(I) = 0$), while for $n \ge 1$ the left-hand side
fails because $\mathcal{K}_0(A, v) = \{0\}$.

The proof of the forward direction differs from that of the book. At an eigenvector $v$ of $A$,
the subspace $\mathcal{K}_s(A, v)$ lies in $\operatorname{span}\{v\}$, so $A^H v$ is a multiple
of $v$. Thus every eigenvector of $A$ is an eigenvector of $A^H$, and $A$ is normal by Lemma
1.15 of the book (`LinearMap.isStarNormal_of_adjoint_apply_eq_smul`). The book then takes a
vector whose grade is the degree of the minimal polynomial of $A$. Here, instead,
$w = \sum_i x_i$ with one nonzero $x_i$ from each eigenspace. The $x_i$ are pairwise orthogonal,
so the polynomial $q$ of degree at most $s - 1$ given by $A^H w \in \mathcal{K}_s(A, w)$
satisfies $q(\lambda_i) = \bar\lambda_i$ at every eigenvalue, hence $q(A) = A^H$ and
$\nu(A) \le s - 1$. This route needs neither a maximal vector nor the equality of the degree of
the minimal polynomial with the number of distinct eigenvalues. -/
theorem lemma_6_23 {A : Matrix (Fin n) (Fin n) ℂ} {s : ℕ} (hs : 0 < s) :
    (∀ v : ℂ𝔼, op Aᴴ v ∈ krylov A v s) ↔ IsStarNormal A ∧ ν A ≤ s - 1 := by
  have hadj : op Aᴴ = LinearMap.adjoint (op A) := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  constructor
  · intro h
    classical
    have hev : ∀ (μ : ℂ) (y : ℂ𝔼), op A y = μ • y →
        ∃ ν : ℂ, LinearMap.adjoint (op A) y = ν • y := by
      intro μ y hy
      obtain ⟨p, _, hpy⟩ := (mem_krylov_iff_exists_aeval A y).1 (h y)
      exact ⟨p.eval μ, by rw [← hadj, ← hpy]; exact Module.End.aeval_apply_of_mem_apply_eq_smul hy⟩
    have hT : IsStarNormal (op A) := LinearMap.isStarNormal_of_adjoint_apply_eq_smul hev
    refine ⟨Matrix.isStarNormal_toEuclideanLin_iff.1 hT, ?_⟩
    obtain ⟨S, hS⟩ : ∃ S : Finset ℂ, ∀ μ : ℂ, μ ∈ S ↔ Module.End.HasEigenvalue (op A) μ :=
      ⟨(Module.End.finite_hasEigenvalue (op A)).toFinset, fun _ => Set.Finite.mem_toFinset _⟩
    have hexists : ∀ μ : ℂ, ∃ y : ℂ𝔼, μ ∈ S →
        y ∈ Module.End.eigenspace (op A) μ ∧ y ≠ 0 := by
      intro μ
      by_cases hμ : μ ∈ S
      · obtain ⟨y, hy⟩ := Module.End.HasEigenvalue.exists_hasEigenvector ((hS μ).1 hμ)
        exact ⟨y, fun _ => ⟨hy.1, hy.2⟩⟩
      · exact ⟨0, fun hc => absurd hc hμ⟩
    choose x hx using hexists
    obtain ⟨w, hw⟩ : ∃ w : ℂ𝔼, w = ∑ μ ∈ S, x μ := ⟨_, rfl⟩
    obtain ⟨p, hpdeg, hpw⟩ := (mem_krylov_iff_exists_aeval A w).1 (h w)
    have hAdjw : LinearMap.adjoint (op A) w = ∑ μ ∈ S, starRingEnd ℂ μ • x μ := by
      rw [hw, map_sum]
      refine Finset.sum_congr rfl fun μ hμ => Module.End.mem_eigenspace_iff.1 ?_
      rw [LinearMap.IsStarNormal.eigenspace_adjoint hT μ]
      exact (hx μ hμ).1
    have hEvalw : aeval (op A) p w = ∑ μ ∈ S, p.eval μ • x μ := by
      rw [hw, map_sum]
      exact Finset.sum_congr rfl fun μ hμ => Module.End.aeval_apply_of_mem_apply_eq_smul
        (Module.End.mem_eigenspace_iff.1 (hx μ hμ).1)
    have hsum : ∑ μ ∈ S, (p.eval μ - starRingEnd ℂ μ) • x μ = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hEvalw, ← hAdjw, hpw, hadj, sub_self]
    have hcoef : ∀ ν ∈ S, p.eval ν = starRingEnd ℂ ν := by
      intro ν hν
      have hsingle : (∑ μ ∈ S, (inner ℂ (x ν) ((p.eval μ - starRingEnd ℂ μ) • x μ) : ℂ))
          = inner ℂ (x ν) ((p.eval ν - starRingEnd ℂ ν) • x ν) := by
        refine Finset.sum_eq_single_of_mem ν hν fun μ hμ hμν => ?_
        rw [inner_smul_right, LinearMap.IsStarNormal.inner_eq_zero_of_ne hT
          (Ne.symm hμν) (hx ν hν).1 (hx μ hμ).1, mul_zero]
      have hj : (0 : ℂ) = (p.eval ν - starRingEnd ℂ ν) * inner ℂ (x ν) (x ν) := by
        rw [← inner_smul_right, ← hsingle, ← inner_sum, hsum, inner_zero_right]
      have hxx : (inner ℂ (x ν) (x ν) : ℂ) ≠ 0 :=
        fun hc => (hx ν hν).2 (inner_self_eq_zero.1 hc)
      exact sub_eq_zero.1 ((mul_eq_zero.1 hj.symm).resolve_right hxx)
    have hqM : aeval A p = Aᴴ :=
      Matrix.aeval_eq_conjTranspose_iff.1
        (LinearMap.IsStarNormal.aeval_eq_adjoint_of_eval_eq hT
          fun μ hμ => hcoef μ ((hS μ).2 hμ))
    refine le_trans (nu_le_natDegree hqM) ?_
    rcases eq_or_ne p 0 with rfl | hp0
    · simp
    · have hlt : p.natDegree < s := (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hpdeg
      omega
  · rintro ⟨hn, hν⟩ v
    obtain ⟨q, hqd, hq⟩ := exists_natDegree_eq_nu hn
    have hdeg : q.degree < (s : ℕ) := by
      rcases eq_or_ne q 0 with rfl | hq0
      · simp
      · exact (Polynomial.natDegree_lt_iff_degree_lt hq0).1 (by omega)
    rw [← hq, op_aeval]
    exact aeval_mem_krylov A v hdeg

/-! ### Theorem 6.24, the direction that the material of the book proves -/

/-- **Theorem 6.24** of [saad2003iterative], sufficiency, first case. Let $A$ be a complex
$n \times n$ matrix whose minimal polynomial has degree at most $s$. Then $A \in CG(s)$.

The condition of $CG(s)$ is vacuous here: every starting vector has grade at most the degree of
the minimal polynomial, so no pair $i + s \le j \le \mu - 1$ exists. -/
theorem isCGs_of_natDegree_minpoly_le {A : Matrix (Fin n) (Fin n) ℂ} {s : ℕ}
    (h : (minpoly ℂ A).natDegree ≤ s) : IsCGs A s := by
  intro v₁ _ i j hij hjg
  exfalso
  have hgr : grade A v₁ ≤ (minpoly ℂ A).natDegree :=
    grade_le_natDegree A v₁ (minpoly.monic (Algebra.IsIntegral.isIntegral A))
      (by rw [minpoly.aeval]; simp)
  omega

/-- **Theorem 6.24** of [saad2003iterative], sufficiency, second case. Let $A$ be a normal complex
$n \times n$ matrix and $s \ge 1$ with $\nu(A) \le s - 1$. Then $A \in CG(s)$.

Lemma 6.23 gives $A^H v \in \mathcal{K}_s(A, v)$ for every $v$, and (6.108) then gives the band
condition for all $j$, without the restriction $j \le \mu - 1$ that $CG(s)$ allows. -/
theorem isCGs_of_isStarNormal {A : Matrix (Fin n) (Fin n) ℂ} {s : ℕ} (hs : 0 < s)
    (hA : IsStarNormal A) (hν : ν A ≤ s - 1) : IsCGs A s := by
  have hmem : ∀ w : EuclideanSpace ℂ (Fin n), LinearMap.adjoint (op A) w ∈ krylov A w s := by
    intro w
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A]
    exact (lemma_6_23 hs).2 ⟨hA, hν⟩ w
  exact fun v₁ hv _ _ hij _ => arnoldiCoeff_eq_zero_of_adjoint_mem A v₁ hmem hv hij

/-- **Theorem 6.24** of [saad2003iterative], sufficiency. Let $A$ be a complex $n \times n$ matrix
and $s \ge 1$. If the minimal polynomial of $A$ has degree at most $s$, or $A$ is normal and
$\nu(A) \le s - 1$, then $A \in CG(s)$.

The converse, that $A \in CG(s)$ implies one of the two conditions, is the Faber–Manteuffel
theorem proper. The book states it without proof, and it is not formalized. -/
theorem isCGs_of_natDegree_minpoly_le_or_isStarNormal {A : Matrix (Fin n) (Fin n) ℂ} {s : ℕ}
    (hs : 0 < s) (h : (minpoly ℂ A).natDegree ≤ s ∨ (IsStarNormal A ∧ ν A ≤ s - 1)) :
    IsCGs A s := by
  rcases h with h | ⟨hA, hν⟩
  · exact isCGs_of_natDegree_minpoly_le h
  · exact isCGs_of_isStarNormal hs hA hν

/-! ### Section 6.10, the closing remark: the case $\nu(A) \le 1$ -/

/-- **Section 6.10** of [saad2003iterative], closing remark. Let $A$ be a normal complex
$n \times n$ matrix. Then $\nu(A) \le 1$, the case of the Conjugate Gradient method, holds if
and only if one of the following holds:

1. $A = cI$ for some $c \in \mathbb{C}$;
2. $A$ is Hermitian;
3. $A = e^{i\theta}(\rho I + B)$ for some $\theta, \rho \in \mathbb{R}$ and a skew-Hermitian
   matrix $B$, that is, $B^H = -B$.

Normality is a hypothesis, not a consequence: for a non-normal $A$ the set of degrees that
defines $\nu(A)$ is empty, so $\nu(A) = 0 \le 1$ although none of the three cases need hold. The
three cases are those of the book, and they are not disjoint: the third contains the other two.
A scalar matrix $cI$ is $e^{i \arg c}(|c| I + 0)$, and a Hermitian $A$ is
$e^{i\pi/2}(0 \cdot I + (-iA))$ with $-iA$ skew-Hermitian. The backbone theorem
`Matrix.exists_natDegree_le_one_aeval_eq_conjTranspose_iff` is that sharper equivalence. -/
theorem nu_le_one_iff {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) :
    ν A ≤ 1 ↔
      (∃ c : ℂ, A = c • (1 : Matrix (Fin n) (Fin n) ℂ)) ∨ A.IsHermitian ∨
        ∃ (θ ρ : ℝ) (B : Matrix (Fin n) (Fin n) ℂ), Bᴴ = -B ∧
          A = Complex.exp (θ * Complex.I) •
            ((ρ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + B) := by
  constructor
  · intro h
    obtain ⟨q, hqd, hq⟩ := exists_natDegree_eq_nu hA
    exact Or.inr (Or.inr
      (Matrix.exists_natDegree_le_one_aeval_eq_conjTranspose_iff.1 ⟨q, by omega, hq⟩))
  · intro h
    obtain ⟨q, hq1, hq2⟩ : ∃ q : ℂ[X], q.natDegree ≤ 1 ∧ aeval A q = Aᴴ := by
      rcases h with ⟨c, rfl⟩ | hH | h3
      · refine ⟨C (star c), by simp, ?_⟩
        rw [aeval_C, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          Algebra.algebraMap_eq_smul_one]
      · exact ⟨X, by simp, by rw [aeval_X, hH]⟩
      · exact Matrix.exists_natDegree_le_one_aeval_eq_conjTranspose_iff.2 h3
    exact (nu_le_natDegree hq2).trans hq1

end Normal

end SaadSparse.Chapter06
