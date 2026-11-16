/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Bidiagonalization
import Numlib.Krylov.Lanczos
import Numlib.Krylov.Monotonicity
import Numlib.Krylov.QuasiMinRes
import Numlib.Krylov.TransposeFree
import NumlibSurface.GolubVanLoan.Chapter01.Section04
import NumlibSurface.GolubVanLoan.Chapter03.Section01
import NumlibSurface.GolubVanLoan.Chapter05.Section01
import NumlibSurface.GolubVanLoan.Chapter10.Section04
import NumlibSurface.GolubVanLoan.Chapter10.Section05

/-!
# Golub and Van Loan, Section 11.4: Other Krylov methods

This module formalizes §11.4 of [golub2013matrix]: Krylov methods other than the conjugate gradient
method, for a system $Ax = b$ with $A \in \mathbb{R}^{n \times n}$ or for the least-squares problem
$\min_x \|Ax - b\|_2$ with $A \in \mathbb{R}^{m \times n}$. Each method takes its iterate $x_k$ from
$x_0 + \mathcal{K}(A, r_0, k)$, $r_0 = b - Ax_0$, or from a related Krylov subspace, through a
Krylov process, a factorization of the small matrix that the process produces, and short recursions.
MINRES and SYMMLQ (§11.4.1) solve symmetric indefinite systems through the Lanczos relation
$AQ_k = Q_{k+1}H_k$. LSQR and LSMR (§11.4.2) solve least-squares problems through the lower
bidiagonalization $AV_k = U_{k+1}\tilde B_k$. GMRES (§11.4.3, Algorithm 11.4.2) minimizes the
residual through the Arnoldi relation $AQ_k = Q_{k+1}\tilde H_k$ and Givens rotations. §11.4.4
writes the minimal residual as a minimum over polynomials $\psi$ with $\psi(0) = 1$. §11.4.5 treats
the methods built on the unsymmetric Lanczos process: BiCG, CGS, BiCGstab (the three columns of
Figure 11.4.1) and QMR. The source has no Algorithm 11.4.1: §11.4.1 describes MINRES and SYMMLQ in
prose, and the first numbered algorithm of the section is Algorithm 11.4.2.

The proofs specialize the backbone. The minimal-residual iterate `Krylov.IsMinResidualIterate` of
`Numlib.Krylov.Iterate` specifies MINRES, GMRES and LSMR. The Arnoldi and Lanczos relations and the
Givens rotations of the Hessenberg matrix come from `Numlib.Krylov.Arnoldi`, `Numlib.Krylov.Lanczos`
and `Numlib.Krylov.Hessenberg`, and the bidiagonalization from `Numlib.Krylov.Bidiagonalization`.
The two-sided Lanczos process, BiCG and QMR come from `Numlib.Krylov.BiLanczos`, and CGS and
BiCGstab from `Numlib.Krylov.TransposeFree`, whose recurrences are those of Figure 11.4.1.

## Main definitions

* §11.4.2, `GolubVanLoan.Chapter11.IsLSMRIterate`: $x$ is the $k$-th LSMR iterate if it minimizes
  $\|A^T(b - Ax)\|_2$ over $x_0 + \mathcal{K}(A^TA, A^Tr_0, k)$.
* Algorithm 11.4.2, `GolubVanLoan.Chapter11.algorithm_11_4_2`: $m$-step GMRES as a program over a
  rounding hook.
* Algorithm 11.4.2, `GolubVanLoan.Chapter11.arnoldiStepOp` and `GolubVanLoan.Chapter11.gmresCore`:
  the Arnoldi pass with the product by $A$ given as a routine, and the GMRES loop with the final
  triangular solve; Algorithm 11.5.2 reuses both.
* Figure 11.4.1, `GolubVanLoan.Chapter11.bicg`, `GolubVanLoan.Chapter11.cgs` and
  `GolubVanLoan.Chapter11.bicgstab`: the three columns of the figure as programs that run a given
  number of passes.

## Main results

* Equation (11.4.1), `GolubVanLoan.Chapter11.equation_11_4_1`: if $R_ky_k = p_k$ after $k$ Givens
  rotations, then $x_0 + Q_ky_k$ minimizes $\|b - Ax\|_2$ over $x_0 + \mathcal{K}(A, r_0, k)$, with
  residual norm $|\rho_k|$.
* §11.4.1, `GolubVanLoan.Chapter11.energyFunctional_unbounded_of_indefinite`:
  $\phi(x) = \frac12x^TAx - x^Tb$ has no lower bound if $A$ has a negative eigenvalue.
* Equations (11.4.2)–(11.4.3), `GolubVanLoan.Chapter11.equation_11_4_2`: the Lanczos relation
  $AQ_k = Q_{k+1}H_k$ with $H_k$ tridiagonal.
* §11.4.1, `GolubVanLoan.Chapter11.minres_reduction`: $\|A(x_0 + Q_ky) - b\|_2 = \|H_ky -
  \beta_0e_1\|_2$.
* §11.4.1, `GolubVanLoan.Chapter11.minres_givens_update`: one new rotation per step, and $R_k$ has
  upper bandwidth $2$.
* Equation (11.4.5), `GolubVanLoan.Chapter11.equation_11_4_5`: for SYMMLQ, the residual is
  orthogonal to $q_1, \dots, q_{k-1}$.
* §11.4.1, `GolubVanLoan.Chapter11.symmlq_minNorm_solution`: the Givens lower triangularization of
  $H_{k-1}^T$ gives the minimum-norm solution of (11.4.5).
* Equation (11.4.6), `GolubVanLoan.Chapter11.equation_11_4_6`: the lower bidiagonalization
  $AV_k = U_{k+1}\tilde B_k$ with orthonormal $V_k$ and $U_{k+1}$.
* §11.4.2, `GolubVanLoan.Chapter11.lsqr_span_eq`: $\operatorname{span}\{v_1, \dots, v_k\} =
  \mathcal{K}(A^TA, A^Tr_0, k)$.
* Equation (11.4.7), `GolubVanLoan.Chapter11.equation_11_4_7`: the LSQR iterate comes from the
  bidiagonal least-squares problem $\min_y \|\tilde B_ky - \beta_0e_1\|_2$.
* §11.4.2, `GolubVanLoan.Chapter11.lsmr_norm_residual_antitone`: along LSMR, $\|A^Tr_k\|_2$
  decreases, and so does $\|r_k\|_2$ if $A$ has full column rank.
* Equation (11.4.8), `GolubVanLoan.Chapter11.equation_11_4_8`: the Arnoldi relation
  $AQ_k = Q_{k+1}\tilde H_k$ and $\operatorname{span}\{q_1, \dots, q_k\} = \mathcal{K}(A, r_0, k)$.
* §11.4.3, `GolubVanLoan.Chapter11.gmres_reduction`: $\|A(x_0 + Q_ky) - b\|_2 = \|\tilde H_ky -
  \beta_0e_1\|_2$, and the GMRES iterate comes from the minimizing $y$.
* Equation (11.4.9), `GolubVanLoan.Chapter11.equation_11_4_9`: the Givens rotations bring
  $\tilde H_k$ to $[R_k; 0]$ with $R_k$ upper triangular.
* Equation (11.4.10), `GolubVanLoan.Chapter11.equation_11_4_10`: the rotated right-hand side is
  $[p_k; \rho_k]$, and $R_ky_k = p_k$ gives the GMRES iterate with residual norm $|\rho_k|$.
* §11.4.3, `GolubVanLoan.Chapter11.gmres_givens_prefix`: $R_{k-1}$ and $p_{k-1}$ are the leading
  parts of $R_k$ and $p_k$.
* Algorithm 11.4.2, `GolubVanLoan.Chapter11.algorithm_11_4_2_spec`: in exact arithmetic, the
  algorithm returns the GMRES iterate after $\min(m, \text{grade})$ steps, and a solution of
  $Ax = b$ if it stops early; `GolubVanLoan.Chapter11.gmresCore_spec` is the same statement for the
  loop.
* §11.4.4, `GolubVanLoan.Chapter11.krylov_eq_aeval`: the vectors $Q_ky$ are the vectors $\phi(A)q_1$
  with $\deg \phi < k$.
* §11.4.4, `GolubVanLoan.Chapter11.minResidual_eq_iInf_poly`: the minimal residual is
  $\min \|\psi(A)r_0\|_2$ over the polynomials $\psi$ of degree at most $k$ with $\psi(0) = 1$.
* Equation (11.4.12), `GolubVanLoan.Chapter11.equation_11_4_12`: the relations of the two-sided
  Lanczos process, its biorthogonality $\tilde Q_k^TQ_k = I_k$, and $\tilde Q_k^TAQ_k = T_k$.
* Equation (11.4.13), `GolubVanLoan.Chapter11.equation_11_4_13`: the dual relation $A^T\tilde Q_k =
  \tilde Q_kT_k^T + \tilde r_ke_k^T$ and $Q_k^T\tilde r_k = 0$.
* §11.4.5, `GolubVanLoan.Chapter11.bicg_residual_orthogonal`: the BiCG iterate has residual
  orthogonal to the columns of $\tilde Q_k$.
* Figure 11.4.1, `GolubVanLoan.Chapter11.bicg_spec`: in exact arithmetic the BiCG column is the
  backbone's BiCG iteration, with biorthogonal residuals and $A$-biconjugate directions.
* §11.4.5, `GolubVanLoan.Chapter11.bicg_eq_cg`: for symmetric $A$ and $\tilde r_0 = r_0$, BiCG is
  CG.
* Equation (11.4.14), `GolubVanLoan.Chapter11.equation_11_4_14`: $r_k = \psi_k(A)r_0$,
  $p_k = \phi_k(A)r_0$, $\tilde r_k = \psi_k(A^T)\tilde r_0$ and
  $\tilde p_k = \phi_k(A^T)\tilde r_0$.
* §11.4.5, `GolubVanLoan.Chapter11.bicg_inner_eq_poly`:
  $\tilde r_k^Tr_k = \tilde r_0^T\psi_k(A)^2r_0$ and
  $\tilde p_k^TAp_k = \tilde r_0^TA\phi_k(A)^2r_0$.
* §11.4.5, `GolubVanLoan.Chapter11.cgs_residual_eq`: the CGS residuals are $r_k = \psi_k(A)^2r_0$.
* §11.4.5, `GolubVanLoan.Chapter11.bicgstab_residual_eq`: the BiCGstab residuals are $r_k = (1 -
  \omega_kA) \cdots (1 - \omega_1A)\psi_k(A)r_0$, and each $\omega_k$ minimizes a residual.
* §11.4.5, `GolubVanLoan.Chapter11.qmr_residual_eq`: $b - A(x_0 + Q_ky) = Q_{k+1}(\beta_0e_1 -
  \tilde T_ky)$, and the QMR iterate minimizes $\|\beta_0e_1 - \tilde T_ky\|_2$.
* §11.4.5, `GolubVanLoan.Chapter11.qmr_eq_gmres_of_orthonormal`: with the orthonormal Arnoldi basis,
  the quasi-minimal-residual iterate is the GMRES iterate.

## Conventions

* A real matrix `A : Matrix (Fin n) (Fin n) ℝ` acts on `EuclideanSpace ℝ (Fin n)` as
  `Matrix.toEuclideanLin A`, and $A^T$ acts as `Matrix.toEuclideanLin Aᵀ`, the adjoint. A vector of
  $\mathbb{R}^n$ is carried there by `WithLp.toLp 2`.
* Indices are 0-based. The source's Lanczos or Arnoldi vector $q_j$, $j \ge 1$, is
  `Arnoldi.vec T r₀ (j - 1)` for `T = Matrix.toEuclideanLin A`. The source's $\tilde H_k$ is
  `Arnoldi.hessenberg T r₀ k`, and for symmetric $A$ its $H_k$ is `Lanczos.tridiagExt T r₀ k`. The
  vector $\beta e_1 \in \mathbb{R}^k$ is `Krylov.firstVec β k`.
* Let $\beta_0 = \|r_0\|_2$. After $k$ Givens rotations, the source's $R_k$, $p_k$ and $\rho_k$ are
  the matrix `Krylov.hessenbergSqOf (Krylov.rotated h k) k`, the vector of the entries
  `Krylov.gvec h β₀ i` for $i < k$, and the number `Krylov.gamma h β₀ k`, where
  `h = Arnoldi.coeff T r₀`.
* A statement about $k$ steps of a process assumes that $k$ (or $k + 1$) is at most the grade
  `Krylov.grade T r₀`, the dimension of the largest Krylov subspace of $r_0$. Below the grade the
  Krylov vectors are orthonormal; the source leaves this assumption implicit.

## Implementation notes

* Algorithm 11.4.2 and the three columns of Figure 11.4.1 are programs over a rounding hook
  `rnd : ℝ → M ℝ`, as in the algorithm conventions of `NumlibSurface.GolubVanLoan`. They are built
  from the dot product (Algorithm 1.1.1), the saxpy (Algorithm 1.1.2), the gaxpy (Algorithm 1.1.3)
  and the rounded vector operations of chapter 1. Their exact semantics ($M$ = `Id`, `rnd = pure`)
  is the corresponding backbone iteration. The source analyses no rounding error in this section.
* Figure 11.4.1 gives only the initializations and the update formulae, with no stopping test. Each
  program therefore runs `fuel` passes of the update, with `fuel` its last argument.
* In Algorithm 11.4.2, the first normalization of the Arnoldi pass divides again by $h_{1,0} = 1$.
  In the rounding model this adds one rounding per entry of $q_1$ to the single division of the
  source. It is kept so that the Arnoldi loop of chapter 10 is reused unchanged.
* The rotations that `givens` (Algorithm 5.1.3) computes in Algorithm 11.4.2 can differ in sign from
  the rotations `Krylov.givensQ` of the backbone. The exact correctness of the algorithm uses only
  that they are orthogonal and triangularize $\tilde H_k$.

## Deviations from the source

* **Display for $\phi(\alpha x)$ in §11.4.1** (typo). The source prints $\phi(\alpha x) =
  \alpha^2\lambda_{\min} - \alpha x^Tb$; the value is $\frac12\alpha^2\lambda_{\min}\|x\|_2^2 -
  \alpha x^Tb$. See `GolubVanLoan.Chapter11.energyFunctional_unbounded_of_indefinite`.
* **Equation (11.4.1)** (generalization). The source states the Givens solve for symmetric $A$; it
  holds for every $A$. See `GolubVanLoan.Chapter11.equation_11_4_1`.
* **Equation (11.4.3)** (typo). The source prints the first row as $\alpha_1\ \beta_2$; it is
  $\alpha_1\ \beta_1$. See `GolubVanLoan.Chapter11.equation_11_4_2`.
* **Equation (11.4.5)** (typo). The derivation prints $r_k = r_0 - AQ_{k-1}y_k$; it is
  $r_0 - AQ_ky_k$. See `GolubVanLoan.Chapter11.equation_11_4_5`.
* **Equation (11.4.5)** (generalization). The source takes the minimum-norm solution $y_k$; the
  orthogonality holds for every solution. See `GolubVanLoan.Chapter11.equation_11_4_5`.
* **The LSQR subspace in §11.4.2** (generalization). The source starts from $u_1 = r_0/\beta_0$; any
  nonzero multiple of $r_0$ gives the same subspace. See `GolubVanLoan.Chapter11.lsqr_span_eq`.
* **Givens display for LSQR in §11.4.2** (typo). The source prints $\beta_1e_1$; it is $\beta_0e_1$.
  See `GolubVanLoan.Chapter11.equation_11_4_7`.
* **First line of §11.4.3** (reading). The source writes $\mathcal{K}(A, b, k)$; it is read as
  $\mathcal{K}(A, r_0, k)$. See `GolubVanLoan.Chapter11.gmres_reduction`.
* **Three-line display of §11.4.4** (typo). The source prints the middle term
  $\|b - A(x_0 + \phi(A))r_0\|_2$; it is $\|b - A(x_0 + \phi(A)r_0)\|_2$. See
  `GolubVanLoan.Chapter11.minResidual_eq_iInf_poly`.
* **BiCG and CG in §11.4.5** (generalization). The source assumes $A$ symmetric positive definite;
  symmetry is enough. See `GolubVanLoan.Chapter11.bicg_eq_cg`.
* **Equation (11.4.14)** (correction). The source prints $\phi_k(0) = 1$, which is false:
  $\phi_1(0) = 1 + \tau_0$. The statement asserts only $\psi_k(0) = 1$. See
  `GolubVanLoan.Chapter11.equation_11_4_14`.
* **Figure 11.4.1, CGS and BiCGstab** (typo). The figure prints the initial condition
  $\tilde r_0^T\tilde r_0 \neq 0$; it is $\tilde r_0^Tr_0 \neq 0$. See `GolubVanLoan.Chapter11.cgs`
  and `GolubVanLoan.Chapter11.bicgstab`.

## Not formalized

* **The operation counts of §11.4**, such as "$O(1)$ flops" and "$O(n)$ work", and Problem P11.4.1.
  Operation counts are out of scope for the library.
* **The short recurrences of MINRES, SYMMLQ and LSQR** that avoid storing all Lanczos vectors, which
  the source describes in prose.
* **The monotonicity of $\|r_k\|_2$ for LSMR without full column rank.** The general case needs the
  energy argument on $\operatorname{ran} A^T$, where $A^TA$ is positive definite.
* **The look-ahead remark.**
* **The remark that CGS typically outperforms BiCG.** It is an observation, not a statement.
* **The advice on when to use which method.**
* **The Notes and References of §11.4.**
-/

open Matrix Polynomial Filter Topology Krylov

namespace GolubVanLoan.Chapter11

variable {n : ℕ}

/-! ### Transport between $\mathbb{R}^n$ and `EuclideanSpace ℝ (Fin n)` -/

/-- The transpose $A^T$ of a real square matrix $A$ acts on `EuclideanSpace ℝ (Fin n)` as the
adjoint of $A$. -/
private theorem inner_toEuclideanLin_transpose (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (toEuclideanLin A x) y = inner ℝ x (toEuclideanLin Aᵀ y) :=
  (toEuclideanLin_transpose_inner_right A x y).symm

/-- The real inner product of two vectors carried to `EuclideanSpace ℝ (Fin n)` is their dot
product. -/
private theorem inner_toLp (u v : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v) = u ⬝ᵥ v :=
  EuclideanSpace.inner_toLp_toLp_real u v

/-- Complex conjugation on $\mathbb{R}$ is the identity. -/
private theorem starRingEnd_real : starRingEnd ℝ = RingHom.id ℝ :=
  RingHom.ext fun x => by simp

/-- Conjugating the coefficients of a real polynomial does nothing. -/
private theorem map_starRingEnd_real (p : ℝ[X]) : p.map (starRingEnd ℝ) = p := by
  rw [starRingEnd_real, Polynomial.map_id]

/-- A loop of $k$ passes of a step is the $k$-th iterate of $g$, if a transport map takes each exact
pass to one application of $g$. -/
private theorem foldlM_range_transport {σ τ : Type*} (step : σ → Id σ) (g : τ → τ) (π : σ → τ)
    (h : ∀ s, π (Id.run (step s)) = g (π s)) (k : ℕ) (s₀ : σ) :
    π (Id.run ((List.range k).foldlM (fun s _ => step s) s₀)) = g^[k] (π s₀) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldlM_append, Function.iterate_succ_apply', ← ih]
    simp only [List.foldlM_cons, List.foldlM_nil, Id.run_bind, bind_pure]
    exact h _

/-- The transpose $A^T$ of a real rectangular matrix $A$ acts as the adjoint of $A$ between the
Euclidean spaces. -/
private theorem inner_toEuclideanLin_transpose' {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (toEuclideanLin A x) y = inner ℝ x (toEuclideanLin Aᵀ y) :=
  (toEuclideanLin_transpose_inner_right A x y).symm

/-- A real matrix mapped by `algebraMap ℝ ℝ` is itself. -/
private theorem map_algebraMap_real {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℝ) :
    M.map (algebraMap ℝ ℝ) = M := by
  ext i j
  simp

/-- If $k$ is at most the grade, then the first $k$ Arnoldi vectors are orthonormal. -/
private theorem orthonormal_vec_fin (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (r : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk : k ≤ grade T r) :
    Orthonormal ℝ fun i : Fin k => Arnoldi.vec T r i :=
  (Arnoldi.orthonormal T r).comp (Fin.castLE hk) (Fin.castLE_injective hk)

/-- For an orthonormal family $q$, $\langle \sum_i c_iq_i, \sum_i d_iq_i \rangle = \sum_i c_id_i$.
-/
private theorem inner_sum_smul_of_orthonormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {k : ℕ} {q : Fin k → E} (hq : Orthonormal ℝ q) (c d : Fin k → ℝ) :
    inner ℝ (∑ i, c i • q i) (∑ i, d i • q i) = ∑ i, c i * d i := by
  rw [hq.inner_sum c d Finset.univ]
  simp

/-- For an orthonormal family, the norm of a combination is the Euclidean norm of its coefficient
vector. -/
private theorem norm_sum_smul_of_orthonormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {k : ℕ} {q : Fin k → E} (hq : Orthonormal ℝ q) (c : Fin k → ℝ) :
    ‖∑ i, c i • q i‖ = ‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin k))‖ := by
  have h1 : ‖∑ i, c i • q i‖ ^ 2 = ‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      inner_sum_smul_of_orthonormal hq, inner_toLp]
    rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

/-! ### §11.4.1: MINRES and SYMMLQ -/

/-- **Section 11.4.1** of [golub2013matrix], unboundedness of $\phi$ for an indefinite matrix. Let
$A \in \mathbb{R}^{n \times n}$ and $b \in \mathbb{R}^n$, and let
$\phi(x) = \frac12x^TAx - x^Tb$. Let $x \neq 0$ satisfy $Ax = \mu x$ with $\mu < 0$. Then
$\phi(\alpha x) \to -\infty$ as $\alpha \to \infty$, and $\phi$ is not bounded below.

**Typo.** The source says: "If $Ax = \lambda_{\min}x$, then $\phi(\alpha x) =
\alpha^2\lambda_{\min} - \alpha x^Tb$ approaches $-\infty$ as $\alpha$ gets big." The correct
value is $\phi(\alpha x) = \frac12\alpha^2\lambda_{\min}\|x\|_2^2 - \alpha x^Tb$. The missing
factor $\frac12\|x\|_2^2$ is positive and does not change the conclusion.

The eigenvalue $\mu$ need not be the smallest eigenvalue: any negative eigenvalue gives the
conclusion. The functional $\phi$ is `energyFunctional (Matrix.toEuclideanLin A) b`. -/
theorem energyFunctional_unbounded_of_indefinite (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    {μ : ℝ} {x : Fin n → ℝ} (hx : A *ᵥ x = μ • x) (hx0 : x ≠ 0) (hμ : μ < 0) :
    Tendsto (fun α : ℝ => energyFunctional (toEuclideanLin A) (WithLp.toLp 2 b)
        (α • (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)))) atTop atBot ∧
      ¬ BddBelow (Set.range (energyFunctional (toEuclideanLin A)
        (WithLp.toLp 2 b : EuclideanSpace ℝ (Fin n)))) := by
  set u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  have hu0 : u ≠ 0 := fun h => hx0 (by simpa [u] using congrArg WithLp.ofLp h)
  have hTu : toEuclideanLin A u = μ • u := by
    rw [toEuclideanLin_toLp, hx, WithLp.toLp_smul]
  set c : ℝ := μ * ‖u‖ ^ 2 / 2
  set d : ℝ := inner ℝ (WithLp.toLp 2 b : EuclideanSpace ℝ (Fin n)) u
  have hc : c < 0 := by
    have : 0 < ‖u‖ ^ 2 := by positivity
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hμ this) two_pos
  have hf : ∀ α : ℝ, energyFunctional (toEuclideanLin A) (WithLp.toLp 2 b) (α • u) =
      α * (c * α - d) := by
    intro α
    simp only [energyFunctional, map_smul, hTu, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, RCLike.re_to_real, conj_trivial, c, d]
    ring
  have hlin : Tendsto (fun α : ℝ => c * α - d) atTop atBot := by
    simpa [sub_eq_add_neg] using
      tendsto_atBot_add_const_right atTop (-d) (tendsto_id.const_mul_atTop_of_neg hc)
  have htend : Tendsto (fun α : ℝ => energyFunctional (toEuclideanLin A) (WithLp.toLp 2 b)
      (α • u)) atTop atBot := by
    simp only [hf]
    exact tendsto_id.atTop_mul_atBot₀ hlin
  refine ⟨htend, ?_⟩
  rintro ⟨B, hB⟩
  obtain ⟨α, hα⟩ := (tendsto_atBot.1 htend (B - 1)).exists
  have := hB ⟨α • u, rfl⟩
  linarith

/-- **Equations (11.4.2)–(11.4.3)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric and $r_0 \in \mathbb{R}^n$, and let $q_1, \dots, q_{k+1}$ be the vectors of $k$
Lanczos steps from $r_0$. Then $AQ_k = Q_{k+1}H_k$, where $H_k \in \mathbb{R}^{(k+1) \times k}$
is the tridiagonal matrix (11.4.3): the Lanczos matrix $T_k$ with the row $\beta_ke_k^T$
appended. The relation is stated for every combination of the columns: $$A(Q_ky) = Q_{k+1}(H_ky)
\qquad \text{for all } y \in \mathbb{R}^k.$$

**Typo.** The source prints the first row of (11.4.3) as $\alpha_1\ \beta_2$. It is
$\alpha_1\ \beta_1$.

The vector $q_{j+1}$ is `Arnoldi.vec (Matrix.toEuclideanLin A) r₀ j`, and $H_k$ is
`Lanczos.tridiagExt (Matrix.toEuclideanLin A) r₀ k`. The statement has no hypothesis on $k$. -/
theorem equation_11_4_2 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (r₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) (y : Fin k → ℝ) :
    toEuclideanLin A (∑ j, y j • Arnoldi.vec (toEuclideanLin A) r₀ j) =
      ∑ i : Fin (k + 1), (Lanczos.tridiagExt (toEuclideanLin A) r₀ k *ᵥ y) i •
        Arnoldi.vec (toEuclideanLin A) r₀ i := by
  rw [Arnoldi.apply_sum, Lanczos.hessenberg_eq_map_tridiagExt r₀ hA.isSymmetric_toEuclideanLin,
    map_algebraMap_real]

/-- **Section 11.4.1** of [golub2013matrix], the MINRES reduction. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, let $b, x_0 \in \mathbb{R}^n$, $r_0 = b - Ax_0$
and $\beta_0 = \|r_0\|_2$, and let $k$ be at most the grade of $r_0$ with respect to $A$. Let
$Q_k$ and $H_k$ be as in (11.4.2) for $k$ Lanczos steps from $r_0$. Then for every
$y \in \mathbb{R}^k$, $$\|A(x_0 + Q_ky) - b\|_2 = \|H_ky - \beta_0e_1\|_2.$$

The source writes the chain "$\|A(x_0 + Q_ky) - b\|_2 = \|Q_{k+1}H_ky - (b - Ax_0)\|_2 =
\|H_ky - \beta_0e_1\|_2$" for $x = x_0 + Q_ky$, where $\operatorname{ran} Q_k = \mathcal{K}(A,
r_0, k)$. The bound on $k$ makes $q_1, \dots, q_k$ orthonormal. -/
theorem minres_reduction {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k ≤ grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) (y : Fin k → ℝ) :
    ‖toEuclideanLin A (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A)
        (b - toEuclideanLin A x₀) j) - b‖ =
      ‖(WithLp.toLp 2 (Lanczos.tridiagExt (toEuclideanLin A) (b - toEuclideanLin A x₀) k *ᵥ y -
        firstVec ‖b - toEuclideanLin A x₀‖ (k + 1)) : EuclideanSpace ℝ (Fin (k + 1)))‖ := by
  rw [norm_sub_rev, norm_residual_eq_norm_firstVec_sub_mulVec hk y,
    Lanczos.hessenberg_eq_map_tridiagExt _ hA.isSymmetric_toEuclideanLin, map_algebraMap_real,
    ← norm_neg, ← WithLp.toLp_neg, neg_sub]
  rfl

/-- The Givens solve of $\min_y \|\beta_0e_1 - \tilde H_ky\|_2$, shared by MINRES (11.4.1) and GMRES
(11.4.10): if $k$ is less than the grade and $R_ky = p_k$, then $x_0 + Q_ky$ is the
minimal-residual iterate, and its residual norm is $|\rho_k|$. -/
private theorem isMinResidualIterate_of_rotated_mulVec (A : Matrix (Fin n) (Fin n) ℝ)
    (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k < grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) {y : Fin k → ℝ}
    (hy : hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A)
        (b - toEuclideanLin A x₀)) k) k *ᵥ y =
      fun i : Fin k => gvec (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
        ‖b - toEuclideanLin A x₀‖ (i : ℕ)) :
    IsMinResidualIterate (toEuclideanLin A) b x₀ k
        (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀) j) ∧
      ‖b - toEuclideanLin A (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A)
          (b - toEuclideanLin A x₀) j)‖ =
        |gamma (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
          ‖b - toEuclideanLin A x₀‖ k| := by
  set T := toEuclideanLin A
  set h := Arnoldi.coeff T (b - T x₀)
  have hh : Matrix.IsUpperHessenberg (n := ℕ) h := Arnoldi.isUpperHessenberg_coeff _ _
  have hρ : ∀ l < k, givensRho h l ≠ 0 := fun l hl => givensRho_arnoldi_ne_zero (by omega)
  have hsq := norm_sq_firstVec_sub_mulVec_eq h hh hρ (‖b - T x₀‖ : ℝ)
  have hzero : ‖(WithLp.toLp 2 ((fun i : Fin k => gvec h (‖b - T x₀‖ : ℝ) (i : ℕ)) -
      (hessenbergSqOf (rotated h k) k).mulVec y) : EuclideanSpace ℝ (Fin k))‖ = 0 := by
    rw [hy, sub_self]
    simp
  have hy2 := hsq y
  rw [hzero] at hy2
  refine ⟨(isMinResidualIterate_iff_isMinOn hk.le y).2 ?_, ?_⟩
  · rw [isMinOn_iff]
    intro z _
    have hz2 := hsq z
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [Arnoldi.hessenberg_eq, hy2, hz2]
    nlinarith [sq_nonneg ‖(WithLp.toLp 2 ((fun i : Fin k => gvec h (‖b - T x₀‖ : ℝ) (i : ℕ)) -
      (hessenbergSqOf (rotated h k) k).mulVec z) : EuclideanSpace ℝ (Fin k))‖]
  · rw [norm_residual_eq_norm_firstVec_sub_mulVec hk.le y, ← Real.norm_eq_abs]
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [Arnoldi.hessenberg_eq, hy2]
    ring

/-- **Equation (11.4.1)** of [golub2013matrix], solved by Givens QR (MINRES). Let
$A \in \mathbb{R}^{n \times n}$, let $b, x_0 \in \mathbb{R}^n$, $r_0 = b - Ax_0$ and
$\beta_0 = \|r_0\|_2$, and let $k$ be less than the grade of $r_0$ with respect to $A$. Let
$\tilde H_k$ be the Hessenberg matrix of $k$ Arnoldi steps from $r_0$, and let $R_k$, $p_k$ and
$\rho_k$ result from $k$ Givens rotations of $\tilde H_k$ and $\beta_0e_1$. If
$y_k \in \mathbb{R}^k$ solves $R_ky_k = p_k$, then $x_k = x_0 + Q_ky_k$ solves (11.4.1),
$$\min_{x \in x_0 + \mathcal{K}(A, r_0, k)} \|b - Ax\|_2,$$ and $\|b - Ax_k\|_2 = |\rho_k|$.

**Generalization.** The source states this for symmetric $A$ (MINRES), where $\tilde H_k$ is the
tridiagonal matrix $H_k$ of (11.4.3) (`GolubVanLoan.Chapter11.equation_11_4_2`). The statement
holds for every $A$. For unsymmetric $A$ it is the statement (11.4.10) of GMRES.

That $x_k$ solves (11.4.1) is `Krylov.IsMinResidualIterate`. The matrix $R_k$ is
`Krylov.hessenbergSqOf (Krylov.rotated h k) k`, the entries of $p_k$ are `Krylov.gvec h β₀ i`
for $i < k$, and $\rho_k$ is `Krylov.gamma h β₀ k`, where
`h = Arnoldi.coeff (Matrix.toEuclideanLin A) r₀`. -/
theorem equation_11_4_1 (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k < grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) {y : Fin k → ℝ}
    (hy : hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A)
        (b - toEuclideanLin A x₀)) k) k *ᵥ y =
      fun i : Fin k => gvec (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
        ‖b - toEuclideanLin A x₀‖ (i : ℕ)) :
    IsMinResidualIterate (toEuclideanLin A) b x₀ k
        (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀) j) ∧
      ‖b - toEuclideanLin A (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A)
          (b - toEuclideanLin A x₀) j)‖ =
        |gamma (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
          ‖b - toEuclideanLin A x₀‖ k| :=
  isMinResidualIterate_of_rotated_mulVec A b x₀ hk hy

/-- Rotation $k$ acts only on rows $k$ and $k + 1$, so the rows above them are final. -/
private theorem rotated_succ_of_lt (h : ℕ → ℕ → ℝ) {k i : ℕ} (hi : i < k) (j : ℕ) :
    rotated h (k + 1) i j = rotated h k i j := by
  rw [rotated_succ_apply, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- **Section 11.4.1** of [golub2013matrix], the MINRES update. Let $A \in \mathbb{R}^{n \times n}$
be symmetric, $r_0 \in \mathbb{R}^n$ and $\beta_0 \in \mathbb{R}$, and let $R_k$ and $p_k$
result from $k$ Lanczos steps from $r_0$ and $k$ Givens rotations, as in (11.4.1). Then the
leading $k \times k$ block of $R_{k+1}$ is $R_k$, the first $k$ entries of $p_{k+1}$ are $p_k$,
and $R_k$ has upper bandwidth $2$: $(R_k)_{ij} = 0$ for $j > i + 2$.

The source says that "the transition $\{H_{k-1}, R_{k-1}, p_{k-1}, \rho_{k-1}\} \to \{H_k, R_k,
p_k, \rho_k\}$ can be realized … after the $k$th Lanczos step", with one new rotation, and that
"the matrix $R_k$ has upper bandwidth 2". The statement is at $k + 1$ in place of $k$. The first
two parts hold for every $A$ (`GolubVanLoan.Chapter11.gmres_givens_prefix`); the bandwidth needs
the tridiagonal $H_k$ of a symmetric $A$. The flop counts are not formalized. -/
theorem minres_givens_update {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (r₀ : EuclideanSpace ℝ (Fin n)) (β₀ : ℝ) (k : ℕ) :
    (∀ i j : Fin k, hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) (k + 1))
        (k + 1) i.castSucc j.castSucc =
      hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) k) k i j) ∧
    (∀ i : Fin k, (fun l : Fin (k + 1) => gvec (Arnoldi.coeff (toEuclideanLin A) r₀) β₀ l)
        i.castSucc = (fun l : Fin k => gvec (Arnoldi.coeff (toEuclideanLin A) r₀) β₀ l) i) ∧
    ∀ i j : Fin k, (i : ℕ) + 2 < j →
      hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) k) k i j = 0 := by
  refine ⟨fun i _ => rotated_succ_of_lt _ i.isLt _, fun i => rfl, fun i j hij => ?_⟩
  exact rotated_eq_zero_of_add_two_lt _
    (fun i j hij => Arnoldi.coeff_eq_zero_of_isSymmetric hA.isSymmetric_toEuclideanLin r₀ hij)
    k i j hij

/-- The combination of the first $k$ Arnoldi vectors with the unit coordinate vector $e_i$ is the
Arnoldi vector of index $i$. -/
private theorem sum_single_smul_vec (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (r : EuclideanSpace ℝ (Fin n)) {k : ℕ} (i : Fin k) :
    ∑ j : Fin k, (Pi.single i (1 : ℝ) : Fin k → ℝ) j • Arnoldi.vec T r j = Arnoldi.vec T r i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- **Equation (11.4.5)** of [golub2013matrix] (SYMMLQ). Let $A \in \mathbb{R}^{n \times n}$ be
symmetric, let $b, x_0 \in \mathbb{R}^n$, $r_0 = b - Ax_0$ and $\beta_0 = \|r_0\|_2$, and let
$k + 1$ be at most the grade of $r_0$ with respect to $A$. Let
$H_k \in \mathbb{R}^{(k+1) \times k}$ be the tridiagonal matrix (11.4.3) of $k$ Lanczos steps
from $r_0$. If $y \in \mathbb{R}^{k+1}$ solves the underdetermined system $H_k^Ty = \beta_0e_1$,
then the residual of $x = x_0 + Q_{k+1}y$ is orthogonal to $q_1, \dots, q_k$: $$q_i^T(b - Ax) =
0, \qquad i = 1, \dots, k.$$

**Typo.** The derivation in the source writes $r_k = r_0 - AQ_{k-1}y_k$. It is
$r_k = r_0 - AQ_ky_k$.

**Generalization.** The source takes for $y_k$ the minimum-norm solution of the system. The
statement holds for every solution.

The source says: "Suppose $x_k = x_0 + Q_ky_k$ where $y_k$ is the … solution to the
$(k-1)$-by-$k$ underdetermined system $H_{k-1}^Ty_k = \beta_0e_1$. … Thus, the residual
$r_k = b - Ax_k$ is orthogonal to $q_1, \dots, q_{k-1}$." The statement is at $k + 1$ in place
of $k$. -/
theorem equation_11_4_5 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k + 1 ≤ grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) {y : Fin (k + 1) → ℝ}
    (hy : (Lanczos.tridiagExt (toEuclideanLin A) (b - toEuclideanLin A x₀) k)ᵀ *ᵥ y =
      firstVec ‖b - toEuclideanLin A x₀‖ k) (i : Fin k) :
    inner ℝ (Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀) i)
      (b - toEuclideanLin A (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A)
        (b - toEuclideanLin A x₀) j)) = 0 := by
  set T := toEuclideanLin A
  set r₀ := b - T x₀
  set q := Arnoldi.vec T r₀
  have hT := hA.isSymmetric_toEuclideanLin
  have hon := orthonormal_vec_fin T r₀ hk
  have hres : b - T (x₀ + ∑ j, y j • q j) = r₀ - T (∑ j, y j • q j) := by
    rw [map_add, sub_add_eq_sub_sub]
  -- `⟪q_i, r₀⟫ = β₀ δ_{i0}`
  have hr0 : r₀ = ∑ j : Fin (k + 1), firstVec ‖r₀‖ (k + 1) j • q j := by
    rw [Finset.sum_eq_single (0 : Fin (k + 1))]
    · simp only [firstVec, Fin.val_zero, ↓reduceIte]
      exact (Arnoldi.smul_vec_zero T r₀).symm
    · intro j _ hj
      have hj' : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
      simp [firstVec, hj']
    · simp
  have hqi : q i = ∑ j : Fin (k + 1), (Pi.single i.castSucc (1 : ℝ) : Fin (k + 1) → ℝ) j • q j :=
    (sum_single_smul_vec T r₀ i.castSucc).symm
  have h1 : inner ℝ (q i) r₀ = firstVec ‖r₀‖ k i := by
    rw [hqi]
    conv_lhs => rw [hr0]
    rw [inner_sum_smul_of_orthonormal hon, Finset.sum_eq_single i.castSucc]
    · simp [firstVec]
    · intro j _ hj; simp [hj]
    · simp
  -- `⟪q_i, A Q y⟫ = (H_kᵀ y)_i`
  have hTqi : T (q i) = ∑ l : Fin (k + 1),
      (Lanczos.tridiagExt T r₀ k *ᵥ (Pi.single i (1 : ℝ))) l • q l := by
    rw [← equation_11_4_2 hA r₀ k, sum_single_smul_vec]
  have h2 : inner ℝ (q i) (T (∑ j, y j • q j)) = ((Lanczos.tridiagExt T r₀ k)ᵀ *ᵥ y) i := by
    rw [← hT, hTqi, inner_sum_smul_of_orthonormal hon]
    simp only [mulVec, dotProduct, transpose_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Pi.single_apply]
  rw [hres, inner_sub_right, h1, h2, hy, sub_self]

/-- **Section 11.4.1** of [golub2013matrix], the minimum-norm solution of SYMMLQ. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, $r_0 \in \mathbb{R}^n$ and
$\beta_0 \in \mathbb{R}$, and let $m$ be less than the grade of $r_0$ with respect to $A$. Let
$\tilde H_m \in \mathbb{R}^{(m+1) \times m}$ be the matrix (11.4.3) of $m$ Lanczos steps from
$r_0$, let $Q_m$ be the orthogonal matrix that accumulates its $m$ Givens rotations, let
$\bar R_m$ be the matrix that the $m$ rotations produce from $\tilde H_m$, with square part
$R_m$, and let $L_m = R_m^T$. Then:

* $\tilde H_m^TQ_m^T = \bar R_m^T$, which is the source's $[L_m \mid 0]$;
* $L_m$ is lower triangular and nonsingular, and has lower bandwidth $2$: $(L_m)_{ij} = 0$ for
  $i > j + 2$;
* if $w \in \mathbb{R}^m$ solves $L_mw = \beta_0e_1$, then
  $y = Q_m^T\begin{bmatrix} w \\ 0 \end{bmatrix}$ solves $\tilde H_m^Ty = \beta_0e_1$, and
  $\|y\|_2 \le \|y'\|_2$ for every solution $y'$ of this system.

The source works at $m = k - 1$. It says that the underdetermined system (11.4.5) "has full row
rank and that $y_k$ can be determined via a Givens rotation lower triangularization …
$H_{k-1}^TG_1 \cdots G_{k-1} = [L_{k-1} \mid 0]$ where $L_{k-1}$ is lower triangular. (This is
just the transpose of the Givens QR factorization of $H_{k-1}$.) If
$w_{k-1} \in \mathbb{R}^{k-1}$ solves the necessarily nonsingular system
$L_{k-1}w_{k-1} = \beta_0e_1$, then $y_k = G_1 \cdots G_{k-1}[w_{k-1}; 0]$", and that $L_{k-1}$
has lower bandwidth equal to 2.

The product $G_1 \cdots G_m$ is $Q_m^T$. With `T = Matrix.toEuclideanLin A` and
`h = Arnoldi.coeff T r₀`, the accumulated rotation is `Krylov.givensQ h m`, the matrix of
(11.4.3) is `Arnoldi.hessenberg T r₀ m`, the rotated matrix $\bar R_m$ is
`Krylov.hessenbergOf (Krylov.rotated h m) m`, and the minimum-norm property comes from
`Krylov.conjTranspose_hessenbergOf_mulVec_givensQ_snoc`. -/
theorem symmlq_minNorm_solution {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (r₀ : EuclideanSpace ℝ (Fin n)) {m : ℕ} (hm : m < grade (toEuclideanLin A) r₀) (β₀ : ℝ) :
    (Arnoldi.hessenberg (toEuclideanLin A) r₀ m)ᵀ *
        (givensQ (Arnoldi.coeff (toEuclideanLin A) r₀) m)ᵀ =
      (hessenbergOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) m) m)ᵀ ∧
    (hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) m) m)ᵀ.IsLowerTriangular ∧
    IsUnit (hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) m) m)ᵀ ∧
    (∀ i j : Fin m, (j : ℕ) + 2 < i →
      (hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) m) m)ᵀ i j = 0) ∧
    ∀ w : Fin m → ℝ,
      (hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) m) m)ᵀ *ᵥ w = firstVec β₀ m →
      (Arnoldi.hessenberg (toEuclideanLin A) r₀ m)ᵀ *ᵥ
          ((givensQ (Arnoldi.coeff (toEuclideanLin A) r₀) m)ᵀ *ᵥ Fin.snoc w 0) =
        firstVec β₀ m ∧
      ∀ y' : Fin (m + 1) → ℝ, (Arnoldi.hessenberg (toEuclideanLin A) r₀ m)ᵀ *ᵥ y' = firstVec β₀ m →
        ‖(WithLp.toLp 2 ((givensQ (Arnoldi.coeff (toEuclideanLin A) r₀) m)ᵀ *ᵥ Fin.snoc w 0) :
            EuclideanSpace ℝ (Fin (m + 1)))‖ ≤
          ‖(WithLp.toLp 2 y' : EuclideanSpace ℝ (Fin (m + 1)))‖ := by
  have hh := Arnoldi.isUpperHessenberg_coeff (toEuclideanLin A) r₀
  have hρ : ∀ l < m, givensRho (Arnoldi.coeff (toEuclideanLin A) r₀) l ≠ 0 := fun l hl => by
    have := givensRho_arnoldi_ne_zero (A := toEuclideanLin A) (b := r₀) (x₀ := 0) (k := l)
      (by simpa using (show l + 1 < grade (toEuclideanLin A) r₀ by omega))
    simpa using this
  rw [Arnoldi.hessenberg_eq]
  refine ⟨?_, ?_, ?_, fun i j hij => ?_, fun w hw => ?_⟩
  · rw [← Matrix.transpose_mul, givensQ_mul_hessenbergOf]
  · exact (hessenbergSqOf_rotated_isUpperTriangular _ hh (Nat.le_succ m)).transpose
  · exact (isUnit_transpose _).2 (isUnit_hessenbergSqOf_rotated_self _ hh hρ)
  · rw [transpose_apply]
    exact rotated_eq_zero_of_add_two_lt _
      (fun i j hij => Arnoldi.coeff_eq_zero_of_isSymmetric hA.isSymmetric_toEuclideanLin r₀ hij)
      m j i hij
  · have h := conjTranspose_hessenbergOf_mulVec_givensQ_snoc _ hh hρ (c := firstVec β₀ m)
      (w := w) (by rwa [conjTranspose_eq_transpose_of_trivial])
    simpa only [conjTranspose_eq_transpose_of_trivial] using h

/-! ### §11.4.2: LSQR and LSMR -/

/-- The image of $\{j \in \mathbb{N} : j < k\}$ under $f$ is the range of $f$ on `Fin k`. -/
private theorem image_Iio_eq_range {α : Type*} (f : ℕ → α) (k : ℕ) :
    f '' Set.Iio k = Set.range fun j : Fin k => f j := by
  ext v
  simp only [Set.mem_image, Set.mem_Iio, Set.mem_range]
  exact ⟨fun ⟨j, hj, hv⟩ => ⟨⟨j, hj⟩, hv⟩, fun ⟨j, hj⟩ => ⟨j, j.isLt, hj⟩⟩

section LeastSquares

variable {m : ℕ}

/-- The lower bidiagonal matrix of the Paige–Saunders process is the coefficient matrix
`Krylov.hessenbergOf` of its Hessenberg relation. -/
private theorem bidiagLower_eq_hessenbergOf (A : Matrix (Fin m) (Fin n) ℝ)
    (u₁ : EuclideanSpace ℝ (Fin m)) (k : ℕ) :
    GolubKahan.bidiagLower (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ k =
      hessenbergOf (fun i j =>
        ((if i = j then GolubKahan.alpha (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ j
          else if i = j + 1 then GolubKahan.beta (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ j
          else 0 : ℝ) : ℝ)) k := by
  ext i j
  simp only [GolubKahan.bidiagLower_apply, hessenbergOf, Matrix.of_apply]

/-- **Equation (11.4.6)** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times n}$ and
$u_1 \in \mathbb{R}^m$, and run $k$ steps of the Paige–Saunders lower bidiagonalization of $A$
(Algorithm 10.4.2) from $u_1$. Let $V_k = [v_1 | \cdots | v_k]$ and
$U_{k+1} = [u_1 | \cdots | u_{k+1}]$ hold its vectors, and let
$\tilde B_k \in \mathbb{R}^{(k+1) \times k}$ be lower bidiagonal with
$\alpha_1, \dots, \alpha_k$ on the diagonal and $\beta_1, \dots, \beta_k$ below it. Then:

* $AV_k = U_{k+1}\tilde B_k$, in the form $A(V_ky) = U_{k+1}(\tilde B_ky)$ for every
  $y \in \mathbb{R}^k$;
* if $k$ is at most the grade of $A^Tu_1$ with respect to $A^TA$, then $v_1, \dots, v_k$ are
  orthonormal;
* if $k + 1$ is at most the grade of $u_1$ with respect to $AA^T$, then $u_1, \dots, u_{k+1}$
  are orthonormal.

The source applies Algorithm 10.4.2 with $u_1 = r_0/\beta_0$. The process normalizes its
starting vector, so the statement needs no hypothesis on $u_1$. The source's condition
$p_k \neq 0$ is the second grade condition.

The process is the Golub–Kahan process of the pair $(A^T, A)$ of
`Numlib.Krylov.Bidiagonalization`. The vectors $v_{j+1}$ and $u_{j+1}$ and the matrix $\tilde B_k$
are, with `T = Matrix.toEuclideanLin A` and `Tt = Matrix.toEuclideanLin Aᵀ`, the vectors
`GolubKahan.leftVec Tt T u₁ j` and `GolubKahan.rightVec Tt T u₁ j` and the matrix
`GolubKahan.bidiagLower Tt T u₁ k`. -/
theorem equation_11_4_6 (A : Matrix (Fin m) (Fin n) ℝ) (u₁ : EuclideanSpace ℝ (Fin m)) (k : ℕ) :
    (∀ y : Fin k → ℝ, toEuclideanLin A
        (∑ j, y j • GolubKahan.leftVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ j) =
      ∑ i : Fin (k + 1), (GolubKahan.bidiagLower (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ k *ᵥ
        y) i • GolubKahan.rightVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ i) ∧
    (k ≤ grade (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A) (toEuclideanLin Aᵀ u₁) →
      Orthonormal ℝ fun j : Fin k =>
        GolubKahan.leftVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ j) ∧
    (k + 1 ≤ grade (toEuclideanLin A ∘ₗ toEuclideanLin Aᵀ) u₁ →
      Orthonormal ℝ fun i : Fin (k + 1) =>
        GolubKahan.rightVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ i) := by
  refine ⟨fun y => ?_, fun hk => ?_, fun hk => ?_⟩
  · have hrel := GolubKahan.hessenbergRelation₂ (A := toEuclideanLin Aᵀ)
      (Astar := toEuclideanLin A) u₁
      (LinearMap.isAdjointPair_inner_iff.2 fun u x => inner_toEuclideanLin_transpose' A u x)
    rw [bidiagLower_eq_hessenbergOf]
    exact hrel.apply_sum k y
  · exact (Arnoldi.orthonormal _ _).comp (Fin.castLE hk) (Fin.castLE_injective hk)
  · exact (Arnoldi.orthonormal _ _).comp (Fin.castLE hk) (Fin.castLE_injective hk)

/-- **Section 11.4.2** of [golub2013matrix], the LSQR subspace. Let $A \in \mathbb{R}^{m \times n}$,
let $r_0, u_1 \in \mathbb{R}^m$ with $r_0 = \beta_0u_1$ for some $\beta_0 \neq 0$, and let
$v_1, v_2, \dots$ be the vectors $v_j$ of the lower bidiagonalization (11.4.6) from $u_1$. Then
for every $k$, $$\operatorname{span}\{v_1, \dots, v_k\} = \mathcal{K}(A^TA, A^Tr_0, k).$$

**Generalization.** The source starts from $u_1 = r_0/\beta_0$ with $\beta_0 = \|r_0\|_2$. The
statement allows any nonzero multiple.

The source says: "It can be shown that $\operatorname{span}\{v_1, \dots, v_k\} =
\mathcal{K}(A^TA, A^Tr_0, k)$." The proof combines (10.4.12) for $A^T$
(`GolubVanLoan.Chapter10.equation_10_4_12`) with the invariance of a Krylov subspace under
scaling of its starting vector. -/
theorem lsqr_span_eq (A : Matrix (Fin m) (Fin n) ℝ) {r₀ u₁ : EuclideanSpace ℝ (Fin m)} {β₀ : ℝ}
    (hβ : β₀ ≠ 0) (hr : r₀ = β₀ • u₁) (k : ℕ) :
    Submodule.span ℝ (GolubKahan.leftVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ '' Set.Iio k) =
      Krylov.subspace (toEuclideanLin (Aᵀ * A)) (toEuclideanLin Aᵀ r₀) k := by
  have h := GolubVanLoan.Chapter10.equation_10_4_12 Aᵀ u₁ k
  rw [transpose_transpose] at h
  rw [h, toEuclideanLin_mul, hr, map_smul]
  refine le_antisymm ?_ (subspace_smul _ _ _ _)
  calc Krylov.subspace (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A) (toEuclideanLin Aᵀ u₁) k
      = Krylov.subspace (toEuclideanLin Aᵀ ∘ₗ toEuclideanLin A)
          (β₀⁻¹ • β₀ • toEuclideanLin Aᵀ u₁) k := by rw [inv_smul_smul₀ hβ]
    _ ≤ _ := subspace_smul _ _ _ _

/-- **Equation (11.4.7)** of [golub2013matrix] (LSQR). Let $A \in \mathbb{R}^{m \times n}$,
$b \in \mathbb{R}^m$ and $x_0 \in \mathbb{R}^n$, let $r_0 = b - Ax_0 = \beta_0u_1$ with
$\|u_1\|_2 = 1$ and $\beta_0 \neq 0$, and run the lower bidiagonalization (11.4.6) from $u_1$.
Let $k + 1$ be at most the grade of $u_1$ with respect to $AA^T$. Then:

* for every $y \in \mathbb{R}^k$, $\|b - A(x_0 + V_ky)\|_2 = \|\beta_0e_1 - \tilde B_ky\|_2$;
* if $y$ minimizes $\|\beta_0e_1 - \tilde B_ky\|_2$ over $\mathbb{R}^k$, then $x_k = x_0 + V_ky$
  satisfies $x_k - x_0 \in \mathcal{K}(A^TA, A^Tr_0, k)$ and minimizes $\|b - Ax\|_2$ over
  $x \in x_0 + \mathcal{K}(A^TA, A^Tr_0, k)$.

**Typo.** The Givens display of §11.4.2 prints $\beta_1e_1$. It is $\beta_0e_1$.

The source says: "The $k$th approximate minimizer $x_k$ solves $\min_{x \in x_0 +
\mathcal{K}(A^TA, A^Tr_0, k)} \|Ax - b\|_2$. Thus, $x_k = x_0 + V_ky_k$ where $y_k$ is the
minimizer of $\|A(x_0 + V_ky) - b\|_2 = \|U_{k+1}\tilde B_ky - (b - Ax_0)\|_2 = \|\tilde B_ky -
\beta_0e_1\|_2$." The second part states the minimality as in `IsMinResidual`, written out. -/
theorem equation_11_4_7 (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin n)) {u₁ : EuclideanSpace ℝ (Fin m)} {β₀ : ℝ} (hu : ‖u₁‖ = 1)
    (hβ : β₀ ≠ 0) (hr : b - toEuclideanLin A x₀ = β₀ • u₁) {k : ℕ}
    (hk : k + 1 ≤ grade (toEuclideanLin A ∘ₗ toEuclideanLin Aᵀ) u₁) :
    (∀ y : Fin k → ℝ, ‖b - toEuclideanLin A
        (x₀ + ∑ j, y j • GolubKahan.leftVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ j)‖ =
      ‖(WithLp.toLp 2 (firstVec β₀ (k + 1) -
        GolubKahan.bidiagLower (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ k *ᵥ y) :
          EuclideanSpace ℝ (Fin (k + 1)))‖) ∧
    ∀ y : Fin k → ℝ, IsMinOn (fun z : Fin k → ℝ => ‖(WithLp.toLp 2 (firstVec β₀ (k + 1) -
        GolubKahan.bidiagLower (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ k *ᵥ z) :
          EuclideanSpace ℝ (Fin (k + 1)))‖) Set.univ y →
      (x₀ + ∑ j, y j • GolubKahan.leftVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ j) - x₀ ∈
          Krylov.subspace (toEuclideanLin (Aᵀ * A)) (toEuclideanLin Aᵀ (b - toEuclideanLin A x₀))
            k ∧
        ∀ x, x - x₀ ∈ Krylov.subspace (toEuclideanLin (Aᵀ * A))
            (toEuclideanLin Aᵀ (b - toEuclideanLin A x₀)) k →
          ‖b - toEuclideanLin A
              (x₀ + ∑ j, y j • GolubKahan.leftVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u₁ j)‖ ≤
            ‖b - toEuclideanLin A x‖ := by
  set T := toEuclideanLin A
  set V := GolubKahan.leftVec (toEuclideanLin Aᵀ) T u₁
  have hon := (equation_11_4_6 A u₁ k).2.2 hk
  have hred : ∀ y : Fin k → ℝ, ‖b - T (x₀ + ∑ j, y j • V j)‖ =
      ‖(WithLp.toLp 2 (firstVec β₀ (k + 1) -
        GolubKahan.bidiagLower (toEuclideanLin Aᵀ) T u₁ k *ᵥ y) :
          EuclideanSpace ℝ (Fin (k + 1)))‖ := by
    intro y
    have hres := GolubKahan.residual_eq (A := T) (Astar := toEuclideanLin Aᵀ)
      (LinearMap.isAdjointPair_inner_iff.2 fun u x => (real_inner_comm _ _).trans
        ((inner_toEuclideanLin_transpose' A x u).symm.trans (real_inner_comm _ _))) hu hr k y
    rw [hres, map_algebraMap_real, norm_sum_smul_of_orthonormal hon]
  refine ⟨hred, fun y hy => ⟨?_, fun x hx => ?_⟩⟩
  · rw [add_sub_cancel_left, ← lsqr_span_eq A hβ hr k]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, j.isLt, rfl⟩)
  · rw [← lsqr_span_eq A hβ hr k, image_Iio_eq_range] at hx
    have hx' : x - x₀ ∈ Submodule.span ℝ (Set.range fun j : Fin k => V j) := hx
    obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx'
    have hxe : x = x₀ + ∑ j, z j • V j := by rw [hz]; abel
    rw [hxe, hred, hred]
    exact hy (Set.mem_univ z)

/-- **Section 11.4.2** of [golub2013matrix], definition of LSMR. Let
$A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$ and $x_0 \in \mathbb{R}^n$, and let
$r_0 = b - Ax_0$. A vector $x \in \mathbb{R}^n$ is the **$k$-th LSMR iterate** from $x_0$ if it
minimizes $\|A^T(b - Ax)\|_2$ over $x_0 + \mathcal{K}(A^TA, A^Tr_0, k)$.

The source defines LSMR as "mathematically equivalent to MINRES applied to the normal equations
$A^TAx = A^Tb$". The definition is `Krylov.IsMinResidualIterate` for the operator $A^TA$ and the
right-hand side $A^Tb$. -/
def IsLSMRIterate (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ) (k : ℕ)
    (x : Fin n → ℝ) : Prop :=
  IsMinResidualIterate (toEuclideanLin (Aᵀ * A)) (WithLp.toLp 2 (Aᵀ *ᵥ b)) (WithLp.toLp 2 x₀) k
    (WithLp.toLp 2 x)

/-- **Section 11.4.2** of [golub2013matrix], monotone residuals of LSMR. Let
$A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$ and $x_0 \in \mathbb{R}^n$, let $x_k$ be
the $k$-th LSMR iterate from $x_0$ for every $k$, and let $r_k = b - Ax_k$. Then $\|A^Tr_k\|_2$
is nonincreasing in $k$. If $A$ has full column rank, then $\|r_k\|_2$ is also nonincreasing in
$k$.

The source says: "The 2-norms of the vectors $r_k = b - Ax_k$ and $A^Tr_k$ decrease
monotonically", with no rank assumption. The case of $\|r_k\|_2$ without full column rank is not
formalized: it needs the same energy argument on $\operatorname{ran} A^T$, where $A^TA$ is
positive definite.

The first part holds because the iterates minimize over nested spaces. The second part follows
Fong and Saunders: $\|r_k\|_2^2 = \|b - Ax_{LS}\|_2^2 + \|x_k - x_{LS}\|_{A^TA}^2$, and the
energy error of MINRES on a positive definite system is nonincreasing. Full column rank is
`Function.Injective A.mulVec`. -/
theorem lsmr_norm_residual_antitone (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x₀ : Fin n → ℝ) {x : ℕ → Fin n → ℝ} (hx : ∀ k, IsLSMRIterate A b x₀ k (x k)) :
    Antitone (fun k => ‖(WithLp.toLp 2 (Aᵀ *ᵥ (b - A *ᵥ x k)) : EuclideanSpace ℝ (Fin n))‖) ∧
      (Function.Injective A.mulVec →
        Antitone fun k => ‖(WithLp.toLp 2 (b - A *ᵥ x k) : EuclideanSpace ℝ (Fin m))‖) := by
  refine ⟨?_, fun hinj => ?_⟩
  · have h := IsMinResidualIterate.norm_residual_antitone hx
    simpa only [toEuclideanLin_toLp, ← WithLp.toLp_sub, mulVec_sub, mulVec_mulVec] using h
  have hG : (Aᵀ * A).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using PosDef.conjTranspose_mul_self A hinj
  set xs : Fin n → ℝ := (Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b)
  have hGxs : (Aᵀ * A) *ᵥ xs = Aᵀ *ᵥ b := by
    rw [mulVec_mulVec, mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit),
      one_mulVec]
  have hstar : toEuclideanLin (Aᵀ * A) (WithLp.toLp 2 xs) = WithLp.toLp 2 (Aᵀ *ᵥ b) := by
    rw [toEuclideanLin_toLp, hGxs]
  have he := IsMinResidualIterate.energyNorm_error_antitone
    (hG.isSymmetricCoercive_toEuclideanLin) hx hstar
  -- the energy norm of `G = AᵀA` is `‖A ·‖₂`
  have hen : ∀ w : Fin n → ℝ, energyNorm (toEuclideanLin (Aᵀ * A)) (WithLp.toLp 2 w) =
      ‖(WithLp.toLp 2 (A *ᵥ w) : EuclideanSpace ℝ (Fin m))‖ := by
    intro w
    rw [energyNorm, toEuclideanLin_toLp, RCLike.re_to_real, inner_toLp, ← mulVec_mulVec,
      mulVec_transpose, ← dotProduct_mulVec, ← inner_toLp, real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _)]
  -- Pythagoras: `‖r_k‖² = ‖b − A xs‖² + ‖A (xs − x_k)‖²`
  have hpyth : ∀ k, ‖(WithLp.toLp 2 (b - A *ᵥ x k) : EuclideanSpace ℝ (Fin m))‖ ^ 2 =
      ‖(WithLp.toLp 2 (b - A *ᵥ xs) : EuclideanSpace ℝ (Fin m))‖ ^ 2 +
        ‖(WithLp.toLp 2 (A *ᵥ (xs - x k)) : EuclideanSpace ℝ (Fin m))‖ ^ 2 := by
    intro k
    have horth : inner ℝ (WithLp.toLp 2 (b - A *ᵥ xs) : EuclideanSpace ℝ (Fin m))
        (WithLp.toLp 2 (A *ᵥ (xs - x k))) = 0 := by
      rw [inner_toLp, dotProduct_mulVec, ← mulVec_transpose, mulVec_sub, mulVec_mulVec, hGxs,
        sub_self, zero_dotProduct]
    have hsum : (WithLp.toLp 2 (b - A *ᵥ x k) : EuclideanSpace ℝ (Fin m)) =
        WithLp.toLp 2 (b - A *ᵥ xs) + WithLp.toLp 2 (A *ᵥ (xs - x k)) := by
      rw [← WithLp.toLp_add, mulVec_sub]; congr 1; abel
    rw [hsum, norm_add_sq_real, horth]
    ring
  intro k l hkl
  have hel := he hkl
  simp only [← WithLp.toLp_sub, hen] at hel
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [hpyth, hpyth]
  have := pow_le_pow_left₀ (norm_nonneg _) hel 2
  linarith

end LeastSquares

/-! ### §11.4.3: GMRES -/

/-- **Equation (11.4.8)** of [golub2013matrix] and the displays after it. Let
$A \in \mathbb{R}^{n \times n}$ and $r_0 \in \mathbb{R}^n$, and let $q_1, q_2, \dots$ and
$\tilde H_k \in \mathbb{R}^{(k+1) \times k}$ be the vectors and the Hessenberg matrix of $k$
Arnoldi steps from $q_1 = r_0/\|r_0\|_2$. Then:

* $AQ_k = Q_{k+1}\tilde H_k$, in the form $A(Q_ky) = Q_{k+1}(\tilde H_ky)$ for every
  $y \in \mathbb{R}^k$;
* $\tilde H_k$ is upper Hessenberg;
* $\operatorname{span}\{q_1, \dots, q_k\} = \mathcal{K}(A, r_0, k)$;
* if $k + 1$ is at most the grade of $r_0$ with respect to $A$, then $q_1, \dots, q_{k+1}$ are
  orthonormal.

The source says: "After $k$ steps of the Arnoldi iteration … it is easy to confirm using
(10.5.2) that $AQ_k = Q_{k+1}\tilde H_k$ where the columns of $Q_{k+1}$ are the orthonormal
Arnoldi vectors and the upper Hessenberg matrix $\tilde H_k$ … Moreover, if $q_1 = r_0/\beta_0$
… then $\operatorname{span}\{q_1, \dots, q_k\} = \mathcal{K}(A, r_0, k)$." The matrix
$\tilde H_k$ is `Arnoldi.hessenberg (Matrix.toEuclideanLin A) r₀ k`. -/
theorem equation_11_4_8 (A : Matrix (Fin n) (Fin n) ℝ) (r₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    (∀ y : Fin k → ℝ, toEuclideanLin A (∑ j, y j • Arnoldi.vec (toEuclideanLin A) r₀ j) =
      ∑ i : Fin (k + 1), (Arnoldi.hessenberg (toEuclideanLin A) r₀ k *ᵥ y) i •
        Arnoldi.vec (toEuclideanLin A) r₀ i) ∧
    (Arnoldi.hessenberg (toEuclideanLin A) r₀ k).IsUpperHessenbergRect ∧
    Submodule.span ℝ (Arnoldi.vec (toEuclideanLin A) r₀ '' Set.Iio k) =
      Krylov.subspace (toEuclideanLin A) r₀ k ∧
    (k + 1 ≤ grade (toEuclideanLin A) r₀ →
      Orthonormal ℝ fun i : Fin (k + 1) => Arnoldi.vec (toEuclideanLin A) r₀ i) :=
  ⟨fun y => Arnoldi.apply_sum _ r₀ k y,
    (Arnoldi.hessenbergRelation _ r₀).hessenbergOf_isUpperHessenbergRect k,
    Arnoldi.span_vec _ r₀ k, fun hk => orthonormal_vec_fin _ r₀ hk⟩

/-- **Section 11.4.3** of [golub2013matrix], the GMRES reduction. Let
$A \in \mathbb{R}^{n \times n}$, let $b, x_0 \in \mathbb{R}^n$, $r_0 = b - Ax_0$ and
$\beta_0 = \|r_0\|_2$, and let $k$ be at most the grade of $r_0$ with respect to $A$. Let $Q_k$
and $\tilde H_k$ be as in (11.4.8). Then for every $y \in \mathbb{R}^k$, $$\|A(x_0 + Q_ky) -
b\|_2 = \|\tilde H_ky - \beta_0e_1\|_2,$$ and $x_0 + Q_ky$ is the $k$-th GMRES iterate, the
minimizer of $\|b - Ax\|_2$ over $x_0 + \mathcal{K}(A, r_0, k)$, if and only if $y$ minimizes
$\|\tilde H_ky - \beta_0e_1\|_2$ over $\mathbb{R}^k$.

**Reading.** The first line of §11.4.3 writes the subspace $\mathcal{K}(A, b, k)$. It is read as
$\mathcal{K}(A, r_0, k)$; the two agree for $x_0 = 0$.

The source says: "As with MINRES, we must find a vector $y \in \mathbb{R}^k$ so that $\|A(x_0 +
Q_ky) - b\|_2 = \|Q_{k+1}\tilde H_ky - (b - Ax_0)\|_2 = \|\tilde H_ky - \beta_0e_1\|_2$ is
minimized. If $y_k$ is the solution to this $(k+1)$-by-$k$ least squares problem, then the
$k$-th GMRES iterate is given by $x_k = x_0 + Q_ky_k$." The GMRES iterate is
`Krylov.IsMinResidualIterate`. -/
theorem gmres_reduction (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k ≤ grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) (y : Fin k → ℝ) :
    ‖toEuclideanLin A (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A)
        (b - toEuclideanLin A x₀) j) - b‖ =
      ‖(WithLp.toLp 2 (Arnoldi.hessenberg (toEuclideanLin A) (b - toEuclideanLin A x₀) k *ᵥ y -
        firstVec ‖b - toEuclideanLin A x₀‖ (k + 1)) : EuclideanSpace ℝ (Fin (k + 1)))‖ ∧
    (IsMinResidualIterate (toEuclideanLin A) b x₀ k
        (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀) j) ↔
      IsMinOn (fun z : Fin k → ℝ => ‖(WithLp.toLp 2
        (Arnoldi.hessenberg (toEuclideanLin A) (b - toEuclideanLin A x₀) k *ᵥ z -
          firstVec ‖b - toEuclideanLin A x₀‖ (k + 1)) : EuclideanSpace ℝ (Fin (k + 1)))‖)
        Set.univ y) := by
  have hneg : ∀ z : Fin k → ℝ, ‖(WithLp.toLp 2
      (Arnoldi.hessenberg (toEuclideanLin A) (b - toEuclideanLin A x₀) k *ᵥ z -
        firstVec ‖b - toEuclideanLin A x₀‖ (k + 1)) : EuclideanSpace ℝ (Fin (k + 1)))‖ =
      ‖(WithLp.toLp 2 (firstVec ‖b - toEuclideanLin A x₀‖ (k + 1) -
        Arnoldi.hessenberg (toEuclideanLin A) (b - toEuclideanLin A x₀) k *ᵥ z) :
          EuclideanSpace ℝ (Fin (k + 1)))‖ := fun z => by
    rw [← norm_neg, ← WithLp.toLp_neg, neg_sub]
  refine ⟨?_, ?_⟩
  · rw [norm_sub_rev, norm_residual_eq_norm_firstVec_sub_mulVec hk y, hneg]
    rfl
  · simp only [hneg]
    exact isMinResidualIterate_iff_isMinOn hk y

/-- **Equation (11.4.9)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$,
$b, x_0 \in \mathbb{R}^n$ and $r_0 = b - Ax_0$, let $k$ be less than the grade of $r_0$ with
respect to $A$, and let $\tilde H_k$ be as in (11.4.8). Let $G_1, \dots, G_k$ be the Givens
rotations that annihilate the subdiagonal of $\tilde H_k$ in turn, and let
$W = G_k^T \cdots G_1^T$. Then $W$ is orthogonal, and $$W\tilde H_k = \begin{bmatrix} R_k \\ 0
\end{bmatrix}$$ with $R_k \in \mathbb{R}^{k \times k}$ upper triangular.

The source says: "If Givens rotations $G_1, \dots, G_k$ have been determined so that
$G_k^T \cdots G_1^T\tilde H_k = [R_k; 0]$, $R_k \in \mathbb{R}^{k \times k}$, is upper
triangular". The matrix $W$ is `Krylov.givensQ h k`, and $W\tilde H_k$ is
`Krylov.hessenbergOf (Krylov.rotated h k) k`, where
`h = Arnoldi.coeff (Matrix.toEuclideanLin A) r₀`. The statement says that the square part of
$W\tilde H_k$ is upper triangular and that its last row is zero. -/
theorem equation_11_4_9 (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k < grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) :
    givensQ (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀)) k ∈
      Matrix.orthogonalGroup (Fin (k + 1)) ℝ ∧
    givensQ (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀)) k *
        Arnoldi.hessenberg (toEuclideanLin A) (b - toEuclideanLin A x₀) k =
      hessenbergOf (rotated (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀)) k) k ∧
    (hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A)
      (b - toEuclideanLin A x₀)) k) k).IsUpperTriangular ∧
    ∀ j < k, rotated (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀)) k k j = 0 := by
  set h := Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀)
  have hh : Matrix.IsUpperHessenberg (n := ℕ) h := Arnoldi.isUpperHessenberg_coeff _ _
  exact ⟨givensQ_mem_unitaryGroup h k fun l hl => givensRho_arnoldi_ne_zero (by omega),
    givensQ_mul_hessenbergOf h k, hessenbergSqOf_rotated_isUpperTriangular h hh (by omega),
    fun j hj => rotated_last_row h hh k j hj⟩

/-- **Equation (11.4.10)** of [golub2013matrix] and the line after it. Let $A$, $b$, $x_0$, $r_0$,
$k$ and $W = G_k^T \cdots G_1^T$ be as in (11.4.9), and let $\beta_0 = \|r_0\|_2$. Then
$$W(\beta_0e_1) = \begin{bmatrix} p_k \\ \rho_k \end{bmatrix}$$ with $p_k \in \mathbb{R}^k$ and
$\rho_k \in \mathbb{R}$. If $y_k$ solves $R_ky_k = p_k$, then $x_k = x_0 + Q_ky_k$ is the $k$-th
GMRES iterate, and $\|Ax_k - b\|_2 = |\rho_k|$.

The source says: "If … $G_k^T \cdots G_1^T(\beta_0e_1) = [p_k; \rho_k]$ … then $R_ky_k = p_k$
and $|\rho_k| = \|Ax_k - b\|_2$." The entries of $p_k$ are `Krylov.gvec h β₀ i` for $i < k$, and
$\rho_k$ is `Krylov.gamma h β₀ k`, where `h = Arnoldi.coeff (Matrix.toEuclideanLin A) r₀`. -/
theorem equation_11_4_10 (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k < grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) {y : Fin k → ℝ}
    (hy : hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A)
        (b - toEuclideanLin A x₀)) k) k *ᵥ y =
      fun i : Fin k => gvec (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
        ‖b - toEuclideanLin A x₀‖ (i : ℕ)) :
    givensQ (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀)) k *ᵥ
        firstVec ‖b - toEuclideanLin A x₀‖ (k + 1) =
      (fun i : Fin (k + 1) => if (i : ℕ) < k then
        gvec (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
          ‖b - toEuclideanLin A x₀‖ i
        else gamma (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
          ‖b - toEuclideanLin A x₀‖ k) ∧
    IsMinResidualIterate (toEuclideanLin A) b x₀ k
        (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀) j) ∧
    ‖toEuclideanLin A (x₀ + ∑ j, y j • Arnoldi.vec (toEuclideanLin A)
        (b - toEuclideanLin A x₀) j) - b‖ =
      |gamma (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀))
        ‖b - toEuclideanLin A x₀‖ k| := by
  obtain ⟨h1, h2⟩ := isMinResidualIterate_of_rotated_mulVec A b x₀ hk hy
  exact ⟨givensQ_mulVec_firstVec _ _ k, h1, by rw [norm_sub_rev, h2]⟩

/-- **Section 11.4.3** of [golub2013matrix], one new rotation per step. Let
$A \in \mathbb{R}^{n \times n}$, $r_0 \in \mathbb{R}^n$ and $\beta_0 \in \mathbb{R}$, and let
$R_k$ and $p_k$ result from $k$ Arnoldi steps from $r_0$ and $k$ Givens rotations, as in
(11.4.10). Then the leading $k \times k$ block of $R_{k+1}$ is $R_k$, and the first $k$ entries
of $p_{k+1}$ are $p_k$.

The source says: "The transition $\{R_{k-1}, p_{k-1}, \rho_{k-1}\} \to \{R_k, p_k, \rho_k\}$ is
a particularly simple update that involves the generation of a single rotation $G_k$ and
exploitation of the identities $R_{k-1} = R_k(1{:}k-1, 1{:}k-1)$ and $p_k(1{:}k-1) = p_{k-1}$."
The statement is at $k + 1$ in place of $k$. -/
theorem gmres_givens_prefix (A : Matrix (Fin n) (Fin n) ℝ) (r₀ : EuclideanSpace ℝ (Fin n))
    (β₀ : ℝ) (k : ℕ) :
    (∀ i j : Fin k, hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) (k + 1))
        (k + 1) i.castSucc j.castSucc =
      hessenbergSqOf (rotated (Arnoldi.coeff (toEuclideanLin A) r₀) k) k i j) ∧
    ∀ i : Fin k, (fun l : Fin (k + 1) => gvec (Arnoldi.coeff (toEuclideanLin A) r₀) β₀ l)
        i.castSucc = (fun l : Fin k => gvec (Arnoldi.coeff (toEuclideanLin A) r₀) β₀ l) i :=
  ⟨fun i _ => rotated_succ_of_lt _ i.isLt _, fun _ => rfl⟩

/-! ### Algorithm 11.4.2 -/

/-- The state of Algorithm 11.4.2 ($m$-step GMRES). It consists of the state of the Arnoldi loop of
Algorithm 10.5.1 (the step count $k$, the vectors $q_j$, the Hessenberg entries $h_{ij}$, the
residual $r_k$, and the flag `done` that records $\beta_k = 0$), the rotated Hessenberg matrix
$[R_k; 0]$, the rotated right-hand side $[p_k; \rho_k]$, and the rotations $(c_j, s_j)$
determined so far. The columns $0, \dots, k - 1$ of the rotated matrix are filled, and the
others are zero. -/
structure GMRESState (n m : ℕ) where
  /-- The state of the Arnoldi loop of Algorithm 10.5.1. -/
  arnoldi : GolubVanLoan.Chapter10.ArnoldiState n
  /-- The rotated Hessenberg matrix $G_k^T \cdots G_1^T\tilde H_k$, padded with zero columns. -/
  R : Matrix (Fin (m + 1)) (Fin m) ℝ
  /-- The rotated right-hand side $G_k^T \cdots G_1^T(\beta_0e_1)$. -/
  g : Fin (m + 1) → ℝ
  /-- The rotations: $G_{j+1}$ acts in the plane $(j, j+1)$ with $(c, s)$ given by `cs j`. -/
  cs : Fin m → ℝ × ℝ

section GMRES

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {m : ℕ}

/-- One pass of the Arnoldi loop of Algorithm 10.5.1 in Algorithm 11.4.2, with the product $Aq_k$
replaced by a routine `op`. If the state is marked `done`, the pass returns it unchanged.
Otherwise it computes $q_{k+1} = r_k/h_{k+1,k}$, with $h_{1,0} = 1$ at the first pass, sets
$k \leftarrow k + 1$ and $r_k = \mathrm{op}(q_k)$, runs the modified Gram–Schmidt loop (11.4.11)
of $r_k$ against $q_1, \dots, q_k$, and sets $h_{k+1,k} = \|r_k\|_2$. It marks the state `done`
when $h_{k+1,k} = 0$.

With $\mathrm{op}(q) = Aq$ computed by the gaxpy of Algorithm 1.1.3, the pass is the pass
`GolubVanLoan.Chapter10.arnoldiStep` of Algorithm 10.5.1
(`GolubVanLoan.Chapter11.arnoldiStepOp_gaxpy`). With $\mathrm{op}(q) = M^{-1}(Aq)$ it is the
pass of the preconditioned GMRES of §11.5. The Gram–Schmidt loop is
`GolubVanLoan.Chapter10.mgsLoop`. -/
noncomputable def arnoldiStepOp (op : (Fin n → ℝ) → M (Fin n → ℝ))
    (s : GolubVanLoan.Chapter10.ArnoldiState n) : M (GolubVanLoan.Chapter10.ArnoldiState n) :=
  if s.done then pure s else do
    let hk : ℝ := if s.k = 0 then 1 else s.h s.k (s.k - 1)
    let qk ← GolubVanLoan.Chapter10.vecDiv rnd s.r hk
    let q := Function.update s.q s.k qk
    let v ← op qk
    let vh ← GolubVanLoan.Chapter10.mgsLoop rnd q (s.k + 1) v
    let b ← GolubVanLoan.Chapter10.vecNorm rnd vh.1
    pure
      { k := s.k + 1
        q := q
        h := fun i j => if j = s.k then (if i = s.k + 1 then b else vh.2 i) else s.h i j
        r := vh.1
        done := decide (b = 0) }

/-- With the gaxpy of Algorithm 1.1.3 as its routine, `GolubVanLoan.Chapter11.arnoldiStepOp` is the
pass `GolubVanLoan.Chapter10.arnoldiStep` of Algorithm 10.5.1, for every rounding hook. -/
theorem arnoldiStepOp_gaxpy (A : Matrix (Fin n) (Fin n) ℝ)
    (s : GolubVanLoan.Chapter10.ArnoldiState n) :
    arnoldiStepOp rnd (fun q => GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A q 0) s =
      GolubVanLoan.Chapter10.arnoldiStep rnd A s := rfl

/-- One pass $j$, $0 \le j < m$, of the `while` loop of Algorithm 11.4.2. If the Arnoldi state is
marked `done` ($\beta_k = 0$), the pass does nothing. Otherwise it runs the Arnoldi pass
`GolubVanLoan.Chapter11.arnoldiStepOp`, copies the new column $H(1{:}k+1, k)$ into the rotated
matrix, applies $G_1, \dots, G_{k-1}$ to it, determines $G_k$ from $(r_{kk}, h_{k+1,k})$ by
`givens` (Algorithm 5.1.3), and applies $G_k$ to the column and to the right-hand side
(`GolubVanLoan.Chapter05.givensApplyLeft`, `GolubVanLoan.Chapter05.givensRotateVec`). -/
noncomputable def gmresStep (op : (Fin n → ℝ) → M (Fin n → ℝ)) (s : GMRESState n m) (j : Fin m) :
    M (GMRESState n m) :=
  if s.arnoldi.done then pure s else do
    let L ← arnoldiStepOp rnd op s.arnoldi
    let R₀ := s.R.updateCol j fun i => if (i : ℕ) ≤ j + 1 then L.h i j else 0
    let R₁ ← ((List.finRange m).filter (· < j)).foldlM
      (fun (R : Matrix (Fin (m + 1)) (Fin m) ℝ) (i : Fin m) =>
        GolubVanLoan.Chapter05.givensApplyLeft rnd i.castSucc i.succ (s.cs i).1 (s.cs i).2 [j] R)
      R₀
    let c ← GolubVanLoan.Chapter05.algorithm_5_1_3 rnd (R₁ j.castSucc j) (R₁ j.succ j)
    let R₂ ← GolubVanLoan.Chapter05.givensApplyLeft rnd j.castSucc j.succ c.1 c.2 [j] R₁
    let g ← GolubVanLoan.Chapter05.givensRotateVec rnd j.castSucc j.succ c.1 c.2 s.g
    pure ⟨L, R₂, g, Function.update s.cs j c⟩

/-- The body of the $m$-step GMRES programs of Algorithm 11.4.2 and Algorithm 11.5.2, for an initial
vector $z_0$ and an operator routine `op`. It computes $\beta_0 = \|z_0\|_2$ and
$q_1 = z_0/\beta_0$, runs the $m$ passes `GolubVanLoan.Chapter11.gmresStep`, solves
$R_ky_k = p_k$ on the leading $k \times k$ block of the rotated matrix by back substitution
(Algorithm 3.1.2), and computes $\tilde x = x_0 + Q_ky_k$ by the gaxpy (Algorithm 1.1.3). It
returns the final state and $\tilde x$.

The initial vector $z_0$ is $r_0$ for Algorithm 11.4.2 and $M^{-1}r_0$ for Algorithm 11.5.2. In
the branch $k > m$, which serves only to type the leading block, the program returns $x_0$. -/
noncomputable def gmresCore (op : (Fin n → ℝ) → M (Fin n → ℝ)) (x₀ z₀ : Fin n → ℝ) (m : ℕ) :
    M (GMRESState n m × (Fin n → ℝ)) := do
  let β₀ ← GolubVanLoan.Chapter10.vecNorm rnd z₀
  let q₁ ← GolubVanLoan.Chapter10.vecDiv rnd z₀ β₀
  let s ← (List.finRange m).foldlM (gmresStep rnd op)
    ⟨⟨0, fun _ => 0, fun _ _ => 0, q₁, decide (β₀ = 0)⟩, 0, Krylov.firstVec β₀ (m + 1),
      fun _ => (1, 0)⟩
  if h : s.arnoldi.k ≤ m then do
    let y ← GolubVanLoan.Chapter03.algorithm_3_1_2 rnd
      (s.R.submatrix (Fin.castLE (Nat.le_succ_of_le h)) (Fin.castLE h))
      (fun i => s.g (Fin.castLE (Nat.le_succ_of_le h) i))
    let x ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd
      (of fun i (l : Fin s.arnoldi.k) => s.arnoldi.q l i) y x₀
    pure (s, x)
  else pure (s, x₀)

/-- **Algorithm 11.4.2** of [golub2013matrix] ($m$-step GMRES). Let $A \in \mathbb{R}^{n \times n}$
be nonsingular, $b \in \mathbb{R}^n$, $Ax_0 \approx b$, and let $m$ be a positive iteration
limit. The algorithm computes $\tilde x \in \mathbb{R}^n$ that either solves $Ax = b$ or
minimizes $\|Ax - b\|_2$ over the affine space $x_0 + \mathcal{K}(A, r_0, m)$, where
$r_0 = b - Ax_0$:
```
k = 0, r₀ = b − Ax₀, β₀ = ‖r₀‖₂
while (β_k > 0) and k < m
  q_{k+1} = r_k/β_k,  k = k + 1,  r_k = Aq_k
  for i = 1:k: h_ik = q_iᵀr_k, r_k = r_k − h_ik q_i end        (11.4.11)
  β_k = ‖r_k‖₂,  h_{k+1,k} = β_k
  apply G_1, …, G_{k−1} to H(1:k, k) and determine G_k, R_k, p_k, ρ_k
end
solve R_k y_k = p_k and set x̃ = x₀ + Q_k y_k
```
The program computes $r_0$ by the gaxpy (Algorithm 1.1.3) and then runs
`GolubVanLoan.Chapter11.gmresCore` with the routine $q \mapsto Aq$. Its loop is $m$ passes of
`GolubVanLoan.Chapter11.gmresStep`, so the test $k < m$ is the length of the list of passes. It
returns the final state and $\tilde x$.

The program has no hypothesis on $A$; nonsingularity is a hypothesis of
`GolubVanLoan.Chapter11.algorithm_11_4_2_spec`. The Arnoldi part of a pass is the pass of
Algorithm 10.5.1, started from $q_1 = r_0/\beta_0$. Its first normalization divides again by
$h_{1,0} = 1$, which in the rounding model adds one rounding per entry of $q_1$ to the single
division of the source; it is kept so that the loop of chapter 10 is reused unchanged. -/
noncomputable def algorithm_11_4_2 (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (m : ℕ) :
    M (GMRESState n m × (Fin n → ℝ)) := do
  let r₀ ← GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A (-x₀) b
  gmresCore rnd (fun q => GolubVanLoan.Chapter01.algorithm_1_1_3 rnd A q 0) x₀ r₀ m

end GMRES

/-! ### Algorithm 11.4.2: exact semantics -/

section GMRESSpec

variable {m : ℕ}

/-! ### Rotations in the planes $(i, i+1)$ and their accumulation -/

/-- The rotation $G_{i+1}$ of the GMRES programs, in the plane $(i, i+1)$ of $\mathbb{R}^{m+1}$. -/
private noncomputable def gmresRot (c : ℝ × ℝ) (i : Fin m) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  GolubVanLoan.Chapter05.givensRotation i.castSucc i.succ c.1 c.2

/-- The product $G_t^T \cdots G_1^T$ of the transposed rotations of the first $t$ planes. -/
private noncomputable def gmresW (cs : Fin m → ℝ × ℝ) : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
  | 0 => 1
  | t + 1 => if h : t < m then (gmresRot (cs ⟨t, h⟩) ⟨t, h⟩)ᵀ * gmresW cs t else gmresW cs t

/-- The Hessenberg column $H(1{:}j+2, j+1)$ that GMRES pass $j$ copies, padded with zeros. -/
private def gmresHcol (L : GolubVanLoan.Chapter10.ArnoldiState n) (j : Fin m) :
    Fin (m + 1) → ℝ :=
  fun a => if (a : ℕ) ≤ j + 1 then L.h a j else 0

private theorem castSucc_ne_succ (i : Fin m) : i.castSucc ≠ i.succ :=
  (Fin.castSucc_lt_succ (i := i)).ne

private theorem gmresRot_mulVec_apply (c : ℝ × ℝ) (i : Fin m) (v : Fin (m + 1) → ℝ)
    (a : Fin (m + 1)) :
    ((gmresRot c i)ᵀ *ᵥ v) a = if a = i.castSucc then c.1 * v i.castSucc - c.2 * v i.succ
      else if a = i.succ then c.2 * v i.castSucc + c.1 * v i.succ else v a :=
  GolubVanLoan.Chapter05.givensRotation_transpose_mulVec_apply (castSucc_ne_succ i) _ _ v a

/-- The transposed rotation $G(i, i+1, \theta)^T$ fixes a vector whose entries $i$ and $i + 1$
vanish. -/
private theorem gmresRot_mulVec_of_eq_zero (c : ℝ × ℝ) (i : Fin m) {v : Fin (m + 1) → ℝ}
    (h1 : v i.castSucc = 0) (h2 : v i.succ = 0) : (gmresRot c i)ᵀ *ᵥ v = v := by
  ext a
  rw [gmresRot_mulVec_apply, h1, h2]
  split_ifs with ha hb
  · rw [ha, h1]; ring
  · rw [hb, h2]; ring
  · rfl

private theorem gmresW_succ (cs : Fin m → ℝ × ℝ) {t : ℕ} (ht : t < m) :
    gmresW cs (t + 1) = (gmresRot (cs ⟨t, ht⟩) ⟨t, ht⟩)ᵀ * gmresW cs t := by
  simp only [gmresW, ht, ↓reduceDIte]

private theorem gmresW_succ_of_le (cs : Fin m → ℝ × ℝ) {t : ℕ} (ht : m ≤ t) :
    gmresW cs (t + 1) = gmresW cs t := by
  simp only [gmresW, show ¬ t < m by omega, ↓reduceDIte]

/-- The accumulated rotations depend only on the rotations below $t$. -/
private theorem gmresW_congr {cs cs' : Fin m → ℝ × ℝ} {t : ℕ}
    (h : ∀ i : Fin m, (i : ℕ) < t → cs i = cs' i) : gmresW cs t = gmresW cs' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t < m
    · rw [gmresW_succ cs ht, gmresW_succ cs' ht, ih fun i hi => h i (by omega),
        h ⟨t, ht⟩ (by simp)]
    · rw [gmresW_succ_of_le cs (by omega), gmresW_succ_of_le cs' (by omega)]
      exact ih fun i hi => h i (by omega)

/-- The accumulated rotations are orthogonal. -/
private theorem gmresW_mem {cs : Fin m → ℝ × ℝ} {t : ℕ}
    (h : ∀ i : Fin m, (i : ℕ) < t → (cs i).1 ^ 2 + (cs i).2 ^ 2 = 1) :
    gmresW cs t ∈ orthogonalGroup (Fin (m + 1)) ℝ := by
  induction t with
  | zero => exact one_mem _
  | succ t ih =>
    by_cases ht : t < m
    · rw [gmresW_succ cs ht]
      refine mul_mem ?_ (ih fun i hi => h i (by omega))
      have hG := Unitary.star_mem (GolubVanLoan.Chapter05.givensRotation_mem_orthogonalGroup
        (castSucc_ne_succ ⟨t, ht⟩) (h ⟨t, ht⟩ (by simp)))
      rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hG
    · rw [gmresW_succ_of_le cs (by omega)]
      exact ih fun i hi => h i (by omega)

/-- The accumulated rotations of the first $t$ planes do not change the entries beyond $t$. -/
private theorem gmresW_mulVec_apply_of_lt (cs : Fin m → ℝ × ℝ) (t : ℕ) (v : Fin (m + 1) → ℝ)
    {a : Fin (m + 1)} (ha : t < a) : (gmresW cs t *ᵥ v) a = v a := by
  induction t with
  | zero => simp [gmresW]
  | succ t ih =>
    by_cases ht : t < m
    · rw [gmresW_succ cs ht, ← mulVec_mulVec, gmresRot_mulVec_apply,
        ite_eq_right fun h => by subst h; simp at ha,
        ite_eq_right fun h => by subst h; simp at ha]
      exact ih (by omega)
    · rw [gmresW_succ_of_le cs (by omega)]
      exact ih (by omega)

/-- The accumulated rotations of the first $t$ planes fix a vector that vanishes on $0, \dots, t$.
-/
private theorem gmresW_mulVec_of_eq_zero (cs : Fin m → ℝ × ℝ) (t : ℕ) {v : Fin (m + 1) → ℝ}
    (hv : ∀ i : Fin (m + 1), (i : ℕ) ≤ t → v i = 0) : gmresW cs t *ᵥ v = v := by
  induction t with
  | zero => simp [gmresW]
  | succ t ih =>
    by_cases ht : t < m
    · rw [gmresW_succ cs ht, ← mulVec_mulVec, ih fun i hi => hv i (by omega)]
      exact gmresRot_mulVec_of_eq_zero _ _ (hv _ (by simp)) (hv _ (by simp))
    · rw [gmresW_succ_of_le cs (by omega)]
      exact ih fun i hi => hv i (by omega)

/-- The entries of the accumulated rotations beyond column $t$ are those of the identity. -/
private theorem gmresW_apply_of_lt (cs : Fin m → ℝ × ℝ) (t : ℕ) (a : Fin (m + 1))
    {c : Fin (m + 1)} (hc : t < c) : gmresW cs t a c = if a = c then 1 else 0 := by
  have h := congrFun (gmresW_mulVec_of_eq_zero cs t (v := Pi.single c 1)
    fun i hi => Pi.single_eq_of_ne (by rintro rfl; omega) _) a
  rw [mulVec_single_one, col_apply, Pi.single_apply] at h
  exact h

/-! ### The rotation loops of the program in exact arithmetic -/

/-- The planes below $t + 1$ are the planes below $t$, followed by the plane $t$. -/
private theorem finRange_filter_lt_succ {t : ℕ} (ht : t < m) :
    (List.finRange m).filter (fun i : Fin m => (i : ℕ) < t + 1) =
      (List.finRange m).filter (fun i : Fin m => (i : ℕ) < t) ++ [⟨t, ht⟩] := by
  have hp := (List.sortedLT_finRange m).pairwise
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) (hp.filter _) ?_ fun a => ?_
  · rw [List.pairwise_append]
    refine ⟨hp.filter _, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      List.mem_singleton] at ha hb
    subst hb
    exact Fin.lt_def.2 ha
  · simp only [List.mem_append, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq, List.mem_singleton]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (Fin.ext h)
    · rintro (h | rfl)
      · omega
      · simp

/-- Applying the rotations of the planes below $t$ in order is multiplication by the accumulated
rotations. -/
private theorem foldl_rot_eq (cs : Fin m → ℝ × ℝ) (v : Fin (m + 1) → ℝ) {t : ℕ} (ht : t ≤ m) :
    ((List.finRange m).filter (fun i : Fin m => (i : ℕ) < t)).foldl
      (fun v i => (gmresRot (cs i) i)ᵀ *ᵥ v) v = gmresW cs t *ᵥ v := by
  induction t with
  | zero => simp [gmresW]
  | succ t ih =>
    rw [finRange_filter_lt_succ (by omega), List.foldl_append, ih (by omega), List.foldl_cons,
      List.foldl_nil, gmresW_succ cs (by omega), mulVec_mulVec]

/-- The row rotation of chapter 5 on the single column $j$ multiplies that column by $G^T$. -/
private theorem givensApplyLeft_col {p q : Fin (m + 1)} (hpq : p ≠ q) (c s : ℝ) (j : Fin m)
    (R : Matrix (Fin (m + 1)) (Fin m) ℝ) :
    Id.run (GolubVanLoan.Chapter05.givensApplyLeft pure p q c s [j] R) =
      R.updateCol j ((GolubVanLoan.Chapter05.givensRotation p q c s)ᵀ *ᵥ fun a => R a j) := by
  rw [GolubVanLoan.Chapter05.givensApplyLeft_spec hpq c s (List.nodup_singleton j)]
  ext a b
  rw [of_apply, updateCol_apply]
  by_cases hb : b = j
  · subst hb
    simp only [List.mem_singleton, ↓reduceIte]
    rfl
  · simp only [List.mem_singleton, hb, ↓reduceIte]

/-- The rotation loop of a GMRES pass on column $j$ applies the listed rotations to that column in
order. -/
private theorem foldlM_rot_col (cs : Fin m → ℝ × ℝ) (j : Fin m) :
    ∀ (l : List (Fin m)) (R₀ : Matrix (Fin (m + 1)) (Fin m) ℝ),
      Id.run (l.foldlM (fun (R : Matrix (Fin (m + 1)) (Fin m) ℝ) (i : Fin m) =>
          GolubVanLoan.Chapter05.givensApplyLeft pure i.castSucc i.succ (cs i).1 (cs i).2 [j] R)
          R₀) =
        R₀.updateCol j (l.foldl (fun v i => (gmresRot (cs i) i)ᵀ *ᵥ v) fun a => R₀ a j)
  | [], R₀ => by
    ext a b
    rw [List.foldlM_nil, List.foldl_nil, updateCol_apply]
    split_ifs with h
    · subst h; rfl
    · rfl
  | i :: l, R₀ => by
    rw [List.foldlM_cons, Id.run_bind, givensApplyLeft_col (castSucc_ne_succ i),
      foldlM_rot_col cs j l, List.foldl_cons]
    ext a b
    simp only [updateCol_apply, ↓reduceIte]
    split_ifs <;> rfl

/-- In exact arithmetic, the vector rotation of chapter 5 is multiplication by $G^T$. -/
private theorem givensRotateVec_run {p q : Fin (m + 1)} (hpq : p ≠ q) (c s : ℝ)
    (x : Fin (m + 1) → ℝ) :
    Id.run (GolubVanLoan.Chapter05.givensRotateVec pure p q c s x) =
      (GolubVanLoan.Chapter05.givensRotation p q c s)ᵀ *ᵥ x := by
  ext r
  rw [GolubVanLoan.Chapter05.givensRotation_transpose_mulVec_apply hpq]
  change Function.update (Function.update x p (c * x p - s * x q)) q (s * x p + c * x q) r = _
  by_cases hrq : r = q
  · subst hrq
    rw [Function.update_self, ite_eq_right hpq.symm, ite_eq_left rfl]
  · rw [Function.update_of_ne hrq]
    by_cases hrp : r = p
    · subst hrp; rw [Function.update_self, ite_eq_left rfl]
    · rw [Function.update_of_ne hrp, ite_eq_right hrp, ite_eq_right hrq]


/-! ### The exact passes -/

/-- If the routine computes $q \mapsto Bq$ in exact arithmetic, the exact pass
`GolubVanLoan.Chapter11.arnoldiStepOp` is the pass of Algorithm 10.5.1 for $B$. -/
private theorem arnoldiStepOp_run {op : (Fin n → ℝ) → Id (Fin n → ℝ)}
    {B : Matrix (Fin n) (Fin n) ℝ} (hop : ∀ q, Id.run (op q) = B *ᵥ q)
    (s : GolubVanLoan.Chapter10.ArnoldiState n) :
    Id.run (arnoldiStepOp pure op s) = Id.run (GolubVanLoan.Chapter10.arnoldiStep pure B s) := by
  have hop' : op = fun q => GolubVanLoan.Chapter01.algorithm_1_1_3 pure B q 0 := by
    funext q
    have h2 := GolubVanLoan.Chapter01.algorithm_1_1_3_spec B q 0
    rw [zero_add] at h2
    exact (hop q).trans h2.symm
  rw [hop']
  rfl

/-- A genuine Arnoldi pass increases the step count by one, keeps the earlier Hessenberg columns,
and marks the state `done` only when the new subdiagonal entry vanishes. -/
private theorem arnoldiStepOp_fields (op : (Fin n → ℝ) → Id (Fin n → ℝ))
    (s : GolubVanLoan.Chapter10.ArnoldiState n) (hd : s.done = false) :
    (Id.run (arnoldiStepOp pure op s)).k = s.k + 1 ∧
      (∀ i j, j ≠ s.k → (Id.run (arnoldiStepOp pure op s)).h i j = s.h i j) ∧
      ((Id.run (arnoldiStepOp pure op s)).done = true →
        (Id.run (arnoldiStepOp pure op s)).h (s.k + 1) s.k = 0) := by
  unfold arnoldiStepOp
  simp only [hd, Bool.false_eq_true, ↓reduceIte]
  exact ⟨rfl, fun i j hj => ite_eq_right hj,
    fun h => (ite_eq_left rfl).trans ((ite_eq_left rfl).trans (of_decide_eq_true h))⟩

/-- The vector $G_j^T \cdots G_1^T h_{:,j}$ that a genuine pass $j$ rotates last. -/
private noncomputable def gmresV (op : (Fin n → ℝ) → Id (Fin n → ℝ)) (s : GMRESState n m)
    (j : Fin m) : Fin (m + 1) → ℝ :=
  gmresW s.cs j *ᵥ gmresHcol (Id.run (arnoldiStepOp pure op s.arnoldi)) j

/-- The rotation $(c, s) = \mathrm{givens}(v_j, v_{j+1})$ that a genuine pass $j$ determines. -/
private noncomputable def gmresC (op : (Fin n → ℝ) → Id (Fin n → ℝ)) (s : GMRESState n m)
    (j : Fin m) : ℝ × ℝ :=
  Id.run (GolubVanLoan.Chapter05.algorithm_5_1_3 pure (gmresV op s j j.castSucc)
    (gmresV op s j j.succ))

/-- The exact run of a genuine GMRES pass. -/
private theorem gmresStep_run (op : (Fin n → ℝ) → Id (Fin n → ℝ)) (s : GMRESState n m)
    (j : Fin m) (hd : s.arnoldi.done = false) :
    Id.run (gmresStep pure op s j) =
      ⟨Id.run (arnoldiStepOp pure op s.arnoldi),
        s.R.updateCol j ((gmresRot (gmresC op s j) j)ᵀ *ᵥ gmresV op s j),
        (gmresRot (gmresC op s j) j)ᵀ *ᵥ s.g, Function.update s.cs j (gmresC op s j)⟩ := by
  have hl : (List.finRange m).filter (· < j) =
      (List.finRange m).filter (fun i : Fin m => (i : ℕ) < j) :=
    List.filter_congr fun i _ => decide_eq_decide.2 Fin.lt_def
  unfold gmresStep
  simp only [hd, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure]
  rw [hl, foldlM_rot_col, foldl_rot_eq _ _ j.2.le, givensApplyLeft_col (castSucc_ne_succ j),
    givensRotateVec_run (castSucc_ne_succ j)]
  simp only [updateCol_self, gmresV, gmresC, gmresRot]
  congr 1
  ext a b
  simp only [updateCol_apply]
  split_ifs <;> rfl

/-- The Arnoldi part of an exact GMRES pass is the pass of Algorithm 10.5.1 for $B$. -/
private theorem gmresStep_arnoldi {op : (Fin n → ℝ) → Id (Fin n → ℝ)}
    {B : Matrix (Fin n) (Fin n) ℝ} (hop : ∀ q, Id.run (op q) = B *ᵥ q) (s : GMRESState n m)
    (j : Fin m) :
    (Id.run (gmresStep pure op s j)).arnoldi =
      Id.run (GolubVanLoan.Chapter10.arnoldiStep pure B s.arnoldi) := by
  cases hd : s.arnoldi.done
  · rw [gmresStep_run op s j hd]
    exact arnoldiStepOp_run hop _
  · simp only [gmresStep, GolubVanLoan.Chapter10.arnoldiStep, hd, ↓reduceIte, Id.run_pure]

/-- The Arnoldi parts of the exact GMRES passes iterate the pass of Algorithm 10.5.1. -/
private theorem foldl_gmresStep_arnoldi {op : (Fin n → ℝ) → Id (Fin n → ℝ)}
    {B : Matrix (Fin n) (Fin n) ℝ} (hop : ∀ q, Id.run (op q) = B *ᵥ q) :
    ∀ (l : List (Fin m)) (s : GMRESState n m),
      (l.foldl (fun s j => Id.run (gmresStep pure op s j)) s).arnoldi =
        (fun L => Id.run (GolubVanLoan.Chapter10.arnoldiStep pure B L))^[l.length] s.arnoldi
  | [], _ => rfl
  | j :: l, s => by
    rw [List.foldl_cons, foldl_gmresStep_arnoldi hop l, gmresStep_arnoldi hop,
      List.length_cons, Function.iterate_succ_apply]

/-- The exact run of Algorithm 10.5.1 iterates its pass. -/
private theorem algorithm_10_5_1_run_eq_iterate (B : Matrix (Fin n) (Fin n) ℝ) (q₁ : Fin n → ℝ)
    (t : ℕ) :
    Id.run (GolubVanLoan.Chapter10.algorithm_10_5_1 pure B q₁ t) =
      (fun L => Id.run (GolubVanLoan.Chapter10.arnoldiStep pure B L))^[t]
        { k := 0, q := fun _ => 0, h := fun _ _ => 0, r := q₁, done := false } := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ← ih]
    simp only [GolubVanLoan.Chapter10.algorithm_10_5_1, List.range_succ, List.foldlM_append,
      List.foldlM_cons, List.foldlM_nil, bind_pure, Id.run_bind]

/-- The exact initial state of `GolubVanLoan.Chapter11.gmresCore` from $z_0$. -/
private noncomputable def gmresInit (z₀ : Fin n → ℝ) (m : ℕ) : GMRESState n m :=
  ⟨⟨0, fun _ => 0, fun _ _ => 0, (‖(WithLp.toLp 2 z₀ : EuclideanSpace ℝ (Fin n))‖)⁻¹ • z₀,
      decide (‖(WithLp.toLp 2 z₀ : EuclideanSpace ℝ (Fin n))‖ = 0)⟩, 0,
    Krylov.firstVec ‖(WithLp.toLp 2 z₀ : EuclideanSpace ℝ (Fin n))‖ (m + 1), fun _ => (1, 0)⟩

/-- The exact triangular solve and update after the loop of `GolubVanLoan.Chapter11.gmresCore`. -/
private noncomputable def gmresFinish (x₀ : Fin n → ℝ) (s : GMRESState n m) :
    GMRESState n m × (Fin n → ℝ) :=
  if h : s.arnoldi.k ≤ m then
    (s, x₀ + (of fun i (l : Fin s.arnoldi.k) => s.arnoldi.q l i) *ᵥ
      Id.run (GolubVanLoan.Chapter03.algorithm_3_1_2 pure
        (s.R.submatrix (Fin.castLE (Nat.le_succ_of_le h)) (Fin.castLE h))
        (fun i => s.g (Fin.castLE (Nat.le_succ_of_le h) i))))
  else (s, x₀)

/-- The exact run of `GolubVanLoan.Chapter11.gmresCore`. -/
private theorem gmresCore_run (op : (Fin n → ℝ) → Id (Fin n → ℝ)) (x₀ z₀ : Fin n → ℝ) (m : ℕ) :
    Id.run (gmresCore pure op x₀ z₀ m) =
      gmresFinish x₀ (Id.run ((List.finRange m).foldlM (gmresStep pure op) (gmresInit z₀ m))) := by
  simp only [gmresCore, Id.run_bind, GolubVanLoan.Chapter10.vecNorm_spec,
    GolubVanLoan.Chapter10.vecDiv_spec]
  unfold gmresFinish gmresInit
  split_ifs
  · simp only [Id.run_bind, Id.run_pure, GolubVanLoan.Chapter01.algorithm_1_1_3_spec]
  · rfl

/-! ### The invariant of the rotations -/

/-- The invariant of the exact GMRES loop after $t$ passes, on the step count, the exit test, the
rotations, the rotated Hessenberg matrix and the rotated right-hand side. -/
private def GInv (β₀ : ℝ) (t : ℕ) (s : GMRESState n m) : Prop :=
  s.arnoldi.k ≤ t ∧ (s.arnoldi.done = false → s.arnoldi.k = t) ∧
    (s.arnoldi.done = true → (s.arnoldi.k = 0 ∧ β₀ = 0) ∨
      (0 < s.arnoldi.k ∧ s.arnoldi.h s.arnoldi.k (s.arnoldi.k - 1) = 0)) ∧
    (∀ i : Fin m, (i : ℕ) < s.arnoldi.k → (s.cs i).1 ^ 2 + (s.cs i).2 ^ 2 = 1) ∧
    (∀ b : Fin m, s.arnoldi.k ≤ b → ∀ a, s.R a b = 0) ∧
    (∀ b : Fin m, (b : ℕ) < s.arnoldi.k → ∀ a,
      s.R a b = (gmresW s.cs s.arnoldi.k *ᵥ gmresHcol s.arnoldi b) a) ∧
    (∀ b : Fin m, (b : ℕ) < s.arnoldi.k → ∀ a : Fin (m + 1), (b : ℕ) < a → s.R a b = 0) ∧
    s.g = gmresW s.cs s.arnoldi.k *ᵥ Krylov.firstVec β₀ (m + 1)

/-- One exact pass keeps the invariant. -/
private theorem gInv_step (op : (Fin n → ℝ) → Id (Fin n → ℝ)) {β₀ : ℝ} {t : ℕ} (ht : t < m)
    {s : GMRESState n m} (hs : GInv β₀ t s) :
    GInv β₀ (t + 1) (Id.run (gmresStep pure op s ⟨t, ht⟩)) := by
  unfold GInv at hs ⊢
  obtain ⟨hkt, hnd, hdn, hcs, hR0, hRW, hRlow, hg⟩ := hs
  cases hd : s.arnoldi.done
  · have hk : s.arnoldi.k = t := hnd hd
    obtain ⟨hLk, hLh, hLd⟩ := arnoldiStepOp_fields op s.arnoldi hd
    rw [gmresStep_run op s ⟨t, ht⟩ hd]
    set j : Fin m := ⟨t, ht⟩ with hj
    set L := Id.run (arnoldiStepOp pure op s.arnoldi) with hL
    set c := gmresC op s j with hc
    set v := gmresV op s j with hv
    obtain ⟨hc1, hc2, -⟩ := GolubVanLoan.Chapter05.algorithm_5_1_3_spec (v j.castSucc) (v j.succ)
    have hcv : c = Id.run (GolubVanLoan.Chapter05.algorithm_5_1_3 pure (v j.castSucc)
        (v j.succ)) := rfl
    rw [← hcv] at hc1 hc2
    have hW : gmresW (Function.update s.cs j c) (t + 1) = (gmresRot c j)ᵀ * gmresW s.cs t := by
      rw [gmresW_succ _ ht, Function.update_self]
      congr 1
      exact gmresW_congr fun i hi => Function.update_of_ne (fun h => by
        rw [h] at hi; simp [j] at hi) _ _
    have hLk' : L.k = t + 1 := by rw [hLk, hk]
    have hcol : ∀ b : Fin m, (b : ℕ) < t → gmresHcol L b = gmresHcol s.arnoldi b := by
      intro b hb
      funext a
      simp only [gmresHcol]
      rw [hLh _ _ (by omega)]
    have hvW : v = gmresW s.cs t *ᵥ gmresHcol L j := rfl
    dsimp only
    refine ⟨hLk'.le, fun _ => hLk', fun hd' => Or.inr ⟨by omega, ?_⟩,
      fun i hi => ?_, fun b hb a => ?_, fun b hb a => ?_, fun b hb a hab => ?_, ?_⟩
    · rw [hLk', Nat.add_sub_cancel, ← hk]
      exact hLd hd'
    · simp only [hLk'] at hi
      by_cases hij : i = j
      · rw [hij, Function.update_self]; exact hc1
      · rw [Function.update_of_ne hij]
        have hne : (i : ℕ) ≠ t := fun h => hij (Fin.ext h)
        exact hcs i (by omega)
    · simp only [hLk'] at hb
      have hbj : b ≠ j := fun h => by rw [h] at hb; simp [j] at hb
      rw [updateCol_apply, ite_eq_right hbj]
      exact hR0 b (by omega) a
    · simp only [hLk'] at hb ⊢
      rw [hW, ← mulVec_mulVec]
      by_cases hbj : b = j
      · subst hbj
        rw [updateCol_apply, ite_eq_left rfl, hvW]
      · have hne : (b : ℕ) ≠ t := fun h => hbj (Fin.ext h)
        have hbt : (b : ℕ) < t := by omega
        rw [updateCol_apply, ite_eq_right hbj, hcol b hbt, ← hk]
        have hcolb : gmresW s.cs s.arnoldi.k *ᵥ gmresHcol s.arnoldi b = fun a => s.R a b :=
          funext fun a => (hRW b (by omega) a).symm
        rw [hcolb, gmresRot_mulVec_of_eq_zero _ _ (hRlow b (by omega) _ (by simp [j]; omega))
          (hRlow b (by omega) _ (by simp [j]; omega))]
    · simp only [hLk'] at hb
      by_cases hbj : b = j
      · subst hbj
        rw [updateCol_apply, ite_eq_left rfl, gmresRot_mulVec_apply]
        have ha1 : a ≠ j.castSucc := fun h => by rw [h] at hab; simp [j] at hab
        rw [ite_eq_right ha1]
        by_cases ha2 : a = j.succ
        · rw [ite_eq_left ha2]
          linear_combination hc2
        · rw [ite_eq_right ha2, hvW, gmresW_mulVec_apply_of_lt _ _ _ (by simp [j] at hab; omega)]
          simp only [gmresHcol]
          split_ifs with hle
          · exfalso
            apply ha2
            ext
            simp [j] at hab hle ⊢
            omega
          · rfl
      · rw [updateCol_apply, ite_eq_right hbj]
        have hne : (b : ℕ) ≠ t := fun h => hbj (Fin.ext h)
        exact hRlow b (by omega) a hab
    · simp only [hLk']
      rw [hW, ← mulVec_mulVec, ← hk, ← hg]
  · have hs' : Id.run (gmresStep pure op s ⟨t, ht⟩) = s := by
      simp only [gmresStep, hd, ↓reduceIte, Id.run_pure]
    rw [hs']
    exact ⟨by omega, fun h => absurd (h.symm.trans hd) Bool.false_ne_true, hdn, hcs, hR0, hRW,
      hRlow, hg⟩

/-- The invariant holds after the first $t$ exact passes. -/
private theorem gInv_foldl (op : (Fin n → ℝ) → Id (Fin n → ℝ)) (z₀ : Fin n → ℝ) :
    ∀ t ≤ m, GInv ‖(WithLp.toLp 2 z₀ : EuclideanSpace ℝ (Fin n))‖ t
      (((List.finRange m).take t).foldl (fun s j => Id.run (gmresStep pure op s j))
        (gmresInit z₀ m)) := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [List.take_zero, List.foldl_nil]
    unfold GInv
    refine ⟨le_rfl, fun _ => rfl, fun h => Or.inl ⟨rfl, by simpa [gmresInit] using h⟩,
      fun i hi => absurd hi (Nat.not_lt_zero _), fun b _ a => rfl,
      fun b hb => absurd hb (Nat.not_lt_zero _), fun b hb => absurd hb (Nat.not_lt_zero _), ?_⟩
    simp [gmresInit, gmresW]
  | succ t ih =>
    intro ht
    rw [List.take_succ_eq_append_getElem (by simpa using ht), List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    have hget : (List.finRange m)[t]'(by simpa using ht) = ⟨t, ht⟩ := by simp
    rw [hget]
    exact gInv_step op ht (ih (by omega))


/-- A sum over `Fin p` whose terms vanish from index $k$ on is the sum over its first $k$ indices.
-/
private theorem sum_castLE_eq {k p : ℕ} (h : k ≤ p) (f : Fin p → ℝ)
    (hf : ∀ c : Fin p, k ≤ (c : ℕ) → f c = 0) :
    ∑ a : Fin k, f (Fin.castLE h a) = ∑ c, f c := by
  have e1 : ∑ c, f c = ∑ i ∈ Finset.range p, (if hi : i < p then f ⟨i, hi⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if hi : i < p then f ⟨i, hi⟩ else 0)]
    exact Finset.sum_congr rfl fun c _ => by rw [dite_eq_left c.2]
  have e2 : ∑ a : Fin k, f (Fin.castLE h a) =
      ∑ i ∈ Finset.range k, (if hi : i < p then f ⟨i, hi⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if hi : i < p then f ⟨i, hi⟩ else 0)]
    exact Finset.sum_congr rfl fun a _ => by rw [dite_eq_left (lt_of_lt_of_le a.2 h)]; rfl
  rw [e1, e2]
  refine Finset.sum_subset (Finset.range_mono h) fun i hi hk => ?_
  simp only [Finset.mem_range] at hi hk
  rw [dite_eq_left hi]
  exact hf ⟨i, hi⟩ (by simpa using hk)

/-- The rows of the accumulated rotations beyond $t$ are those of the identity. -/
private theorem gmresW_apply_of_lt_left (cs : Fin m → ℝ × ℝ) (t : ℕ) {a : Fin (m + 1)}
    (ha : t < a) (c : Fin (m + 1)) : gmresW cs t a c = if a = c then 1 else 0 := by
  have h := gmresW_mulVec_apply_of_lt cs t (Pi.single c 1) ha
  rw [mulVec_single_one, col_apply, Pi.single_apply] at h
  exact h

/-- The exact GMRES loop makes $\min(m, g)$ Arnoldi steps on $z_0$, where $g$ is the grade, and
computes the Arnoldi vectors and the Hessenberg entries of $z_0$. -/
private theorem gmres_arnoldi_spec {op : (Fin n → ℝ) → Id (Fin n → ℝ)}
    {B : Matrix (Fin n) (Fin n) ℝ} (hop : ∀ q, Id.run (op q) = B *ᵥ q) (z₀ : Fin n → ℝ)
    (m : ℕ) :
    ((List.finRange m).foldl (fun s j => Id.run (gmresStep pure op s j))
        (gmresInit z₀ m)).arnoldi.k = min m (grade (toEuclideanLin B) (WithLp.toLp 2 z₀)) ∧
      ∀ j < ((List.finRange m).foldl (fun s j => Id.run (gmresStep pure op s j))
          (gmresInit z₀ m)).arnoldi.k,
        WithLp.toLp 2 (((List.finRange m).foldl (fun s j => Id.run (gmresStep pure op s j))
            (gmresInit z₀ m)).arnoldi.q j) =
          Arnoldi.vec (toEuclideanLin B) (WithLp.toLp 2 z₀) j ∧
        ∀ i ≤ j + 1, ((List.finRange m).foldl (fun s j => Id.run (gmresStep pure op s j))
            (gmresInit z₀ m)).arnoldi.h i j =
          Arnoldi.coeff (toEuclideanLin B) (WithLp.toLp 2 z₀) i j := by
  rw [foldl_gmresStep_arnoldi hop, List.length_finRange]
  set β₀ := ‖(WithLp.toLp 2 z₀ : EuclideanSpace ℝ (Fin n))‖ with hβ₀
  by_cases h0 : β₀ = 0
  · have hfix : ∀ t, (fun L => Id.run (GolubVanLoan.Chapter10.arnoldiStep pure B L))^[t]
        (gmresInit z₀ m).arnoldi = (gmresInit z₀ m).arnoldi := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih =>
        rw [Function.iterate_succ_apply', ih]
        simp [GolubVanLoan.Chapter10.arnoldiStep, gmresInit, ← hβ₀, h0]
    rw [hfix]
    have hz : (WithLp.toLp 2 z₀ : EuclideanSpace ℝ (Fin n)) = 0 := norm_eq_zero.1 h0
    rw [hz, grade_zero]
    refine ⟨by simp [gmresInit], fun j hj => absurd hj (by simp [gmresInit])⟩
  · have hinit : (gmresInit z₀ m).arnoldi =
        { k := 0, q := fun _ => 0, h := fun _ _ => 0, r := β₀⁻¹ • z₀, done := false } := by
      simp [gmresInit, ← hβ₀, h0]
    rw [hinit, ← algorithm_10_5_1_run_eq_iterate]
    have hβpos : 0 < β₀ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hq : (WithLp.toLp 2 (β₀⁻¹ • z₀) : EuclideanSpace ℝ (Fin n)) =
        β₀⁻¹ • WithLp.toLp 2 z₀ := WithLp.toLp_smul _ _ _
    have hqn : ‖(WithLp.toLp 2 (β₀⁻¹ • z₀) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      rw [hq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hβpos.le), ← hβ₀,
        inv_mul_cancel₀ h0]
    obtain ⟨hk, hvec, -⟩ := GolubVanLoan.Chapter10.algorithm_10_5_1_spec B hqn m
    have hvs : Arnoldi.vec (toEuclideanLin B) (WithLp.toLp 2 (β₀⁻¹ • z₀)) =
        Arnoldi.vec (toEuclideanLin B) (WithLp.toLp 2 z₀) := by
      rw [hq]; simpa using Arnoldi.vec_smul_of_pos (toEuclideanLin B) _ (inv_pos.2 hβpos)
    have hgr : grade (toEuclideanLin B) (WithLp.toLp 2 (β₀⁻¹ • z₀)) =
        grade (toEuclideanLin B) (WithLp.toLp 2 z₀) := by
      rw [hq]; exact grade_smul _ _ (inv_ne_zero h0)
    refine ⟨by rw [hk, hgr], fun j hj => ?_⟩
    obtain ⟨h1, h2⟩ := hvec j hj
    refine ⟨by rw [h1, WithLp.toLp_ofLp, hvs], fun i hi => ?_⟩
    rw [h2 i hi, Arnoldi.coeff, Arnoldi.coeff, hvs]

/-- Exact correctness of the GMRES loop `GolubVanLoan.Chapter11.gmresCore`, on which Algorithms
11.4.2 and 11.5.2 rest. Let $B \in \mathbb{R}^{n \times n}$ be nonsingular, let the routine `op`
compute $q \mapsto Bq$ in exact arithmetic, let $c, x_0 \in \mathbb{R}^n$ and $z_0 = c - Bx_0$,
and let $m \in \mathbb{N}$. Run the loop in exact arithmetic from $x_0$ and $z_0$, and let $k$
be its final step count and $\tilde x$ its result. Then:

* $k = \min(m, g)$, where $g$ is the grade of $z_0$ with respect to $B$;
* for $j < k$, the computed vector $q_{j+1}$ is the Arnoldi vector `Arnoldi.vec` of $z_0$ with
  respect to $B$, and the computed entries $h_{ij}$ with $i \le j + 1$ are the Arnoldi
  coefficients `Arnoldi.coeff`;
* $\tilde x$ minimizes $\|c - Bx\|_2$ over $x_0 + \mathcal{K}(B, z_0, k)$;
* the entry $\rho_k$ of index $k$ of the rotated right-hand side satisfies
  $|\rho_k| = \|c - B\tilde x\|_2$;
* if the loop stopped on $\beta_k = 0$, then $B\tilde x = c$.

In exact arithmetic the modified Gram–Schmidt loop is Gram–Schmidt, so the Arnoldi data are
those of `GolubVanLoan.Chapter10.algorithm_10_5_1_spec`. The rotations bring $\tilde H_k$ to
$[R_k; 0]$ with $R_k$ upper triangular and nonsingular, so the back substitution solves
$R_ky_k = p_k$. The case $\beta_k = 0$ uses `Krylov.IsMinResidualIterate.apply_eq_of_grade_le`.
The rotations of `givens` need not be those of `Krylov.givensQ`, because their signs are fixed
differently; the proof uses `Krylov.isMinResidualIterate_of_unitary_mul_hessenberg`, which needs
only that they are orthogonal and triangularize $\tilde H_k$. -/
theorem gmresCore_spec {op : (Fin n → ℝ) → Id (Fin n → ℝ)} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : IsUnit B) (hop : ∀ q, Id.run (op q) = B *ᵥ q) (c x₀ z₀ : Fin n → ℝ)
    (hz : z₀ = c - B *ᵥ x₀) (m : ℕ) :
    (Id.run (gmresCore pure op x₀ z₀ m)).1.arnoldi.k =
        min m (grade (toEuclideanLin B) (WithLp.toLp 2 z₀)) ∧
      (∀ j < (Id.run (gmresCore pure op x₀ z₀ m)).1.arnoldi.k,
        WithLp.toLp 2 ((Id.run (gmresCore pure op x₀ z₀ m)).1.arnoldi.q j) =
            Arnoldi.vec (toEuclideanLin B) (WithLp.toLp 2 z₀) j ∧
          ∀ i ≤ j + 1, (Id.run (gmresCore pure op x₀ z₀ m)).1.arnoldi.h i j =
            Arnoldi.coeff (toEuclideanLin B) (WithLp.toLp 2 z₀) i j) ∧
      IsMinResidualIterate (toEuclideanLin B) (WithLp.toLp 2 c) (WithLp.toLp 2 x₀)
        (Id.run (gmresCore pure op x₀ z₀ m)).1.arnoldi.k
        (WithLp.toLp 2 (Id.run (gmresCore pure op x₀ z₀ m)).2) ∧
      (∀ i : Fin (m + 1), (i : ℕ) = (Id.run (gmresCore pure op x₀ z₀ m)).1.arnoldi.k →
        |(Id.run (gmresCore pure op x₀ z₀ m)).1.g i| =
          ‖WithLp.toLp 2 c -
            toEuclideanLin B (WithLp.toLp 2 (Id.run (gmresCore pure op x₀ z₀ m)).2)‖) ∧
      ((Id.run (gmresCore pure op x₀ z₀ m)).1.arnoldi.done = true →
        B *ᵥ (Id.run (gmresCore pure op x₀ z₀ m)).2 = c) := by
  rw [gmresCore_run, List.idRun_foldlM]
  set T := toEuclideanLin B with hT
  set z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 z₀ with hzdef
  set β₀ := ‖z‖ with hβ₀
  set s := (List.finRange m).foldl (fun s j => Id.run (gmresStep pure op s j))
    (gmresInit z₀ m) with hs
  obtain ⟨hk, hvec⟩ := gmres_arnoldi_spec hop z₀ m
  rw [← hs] at hk hvec
  have hGI := gInv_foldl op z₀ m le_rfl
  rw [List.take_of_length_le (by simp), ← hs] at hGI
  obtain ⟨hkt, -, hdn, hcs, -, hRW, hRlow, hg⟩ := hGI
  set k := s.arnoldi.k with hkdef
  have hkm : k ≤ m := hkt
  have hkg : k ≤ grade T z := by rw [hk]; exact min_le_right _ _
  -- the triangular solve and the update
  set Rk : Matrix (Fin k) (Fin k) ℝ :=
    s.R.submatrix (Fin.castLE (Nat.le_succ_of_le hkm)) (Fin.castLE hkm) with hRk
  set pk : Fin k → ℝ := fun i => s.g (Fin.castLE (Nat.le_succ_of_le hkm) i) with hpk
  set y := Id.run (GolubVanLoan.Chapter03.algorithm_3_1_2 pure Rk pk) with hy
  have hfin : gmresFinish x₀ s =
      (s, x₀ + (of fun i (l : Fin k) => s.arnoldi.q l i) *ᵥ y) := by
    unfold gmresFinish
    exact dite_eq_left hkm
  rw [hfin]
  dsimp only
  -- the Hessenberg columns
  set h := Arnoldi.coeff T z with hh
  have hcolh : ∀ b : Fin m, (b : ℕ) < k →
      gmresHcol s.arnoldi b = fun a : Fin (m + 1) => h (a : ℕ) (b : ℕ) := by
    intro b hb
    funext a
    simp only [gmresHcol]
    split_ifs with ha
    · exact (hvec b hb).2 a ha
    · exact (Arnoldi.coeff_eq_zero_of_lt T z (by omega)).symm
  -- the rotations, restricted to the first `k + 1` entries
  set W := gmresW s.cs k with hW
  have hWmem : W ∈ orthogonalGroup (Fin (m + 1)) ℝ := gmresW_mem hcs
  have hk1 : k + 1 ≤ m + 1 := Nat.succ_le_succ hkm
  set ι : Fin (k + 1) → Fin (m + 1) := Fin.castLE hk1 with hι
  set κ : Fin k → Fin m := Fin.castLE hkm with hκ
  set W' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := W.submatrix ι ι with hW'
  set Hk := Arnoldi.hessenberg T z k with hHk
  set R' : Matrix (Fin (k + 1)) (Fin k) ℝ := s.R.submatrix ι κ with hR'
  have hWrow : ∀ (a : Fin (k + 1)) (c : Fin (m + 1)), k + 1 ≤ (c : ℕ) → W (ι a) c = 0 := by
    intro a c hc
    rw [hW, gmresW_apply_of_lt _ _ _ (by omega)]
    split_ifs with h'
    · have := congrArg Fin.val h'
      simp [ι] at this
      omega
    · rfl
  have hWcol : ∀ (d : Fin (m + 1)) (a : Fin (k + 1)), k + 1 ≤ (d : ℕ) → W d (ι a) = 0 := by
    intro d a hd
    rw [hW, gmresW_apply_of_lt_left _ _ (by omega)]
    split_ifs with h'
    · have := congrArg Fin.val h'
      simp [ι] at this
      omega
    · rfl
  have hC1 : W' * Hk = R' := by
    ext a b
    rw [Matrix.mul_apply, hR', submatrix_apply, hRW (κ b) b.2 (ι a), hcolh (κ b) b.2, mulVec,
      dotProduct]
    rw [← sum_castLE_eq hk1 (fun c => W (ι a) c * h c (κ b))
      fun c hc => by rw [hWrow a c hc, zero_mul]]
    rfl
  have hWo : W'ᵀ * W' = 1 := by
    have hWW := (mem_orthogonalGroup_iff' _ _).1 hWmem
    ext a c
    rw [Matrix.mul_apply]
    have e := congrFun (congrFun hWW (ι a)) (ι c)
    rw [Matrix.mul_apply, ← sum_castLE_eq hk1 (fun d => Wᵀ (ι a) d * W d (ι c))
      fun d hd => by rw [transpose_apply, hWcol d a hd, zero_mul]] at e
    refine e.trans ?_
    rw [Matrix.one_apply, Matrix.one_apply]
    simp [ι, Fin.ext_iff]
  have hW'mem : W' ∈ orthogonalGroup (Fin (k + 1)) ℝ := (mem_orthogonalGroup_iff' _ _).2 hWo
  have hC3 : (fun a => s.g (ι a)) = W' *ᵥ Krylov.firstVec β₀ (k + 1) := by
    funext a
    rw [hg, mulVec, dotProduct, mulVec, dotProduct,
      ← sum_castLE_eq hk1 (fun c => W (ι a) c * Krylov.firstVec β₀ (m + 1) c)
        fun c hc => by rw [hWrow a c hc, zero_mul]]
    rfl
  have hC4 : ∀ b : Fin k, R' (Fin.last k) b = 0 := fun b =>
    hRlow (κ b) b.2 (ι (Fin.last k)) (by simp [κ, ι])
  -- `R_k` is upper triangular and nonsingular
  have hRkU : Rk.IsUpperTriangular := fun a b hab => hRlow (κ b) b.2 _ (by simpa [κ] using hab)
  have hTinj : Function.Injective T := by
    intro u v huv
    have h1 : B *ᵥ u.ofLp = B *ᵥ v.ofLp := by
      have := congrArg WithLp.ofLp huv
      simpa [hT] using this
    exact WithLp.ofLp_injective 2 ((mulVec_injective_iff_isUnit.2 hB) h1)
  have hker : ∀ w : Fin k → ℝ, Rk *ᵥ w = 0 → w = 0 := by
    intro w hw
    have hR'w : R' *ᵥ w = 0 := by
      funext a
      refine Fin.lastCases ?_ (fun a => ?_) a
      · simp only [mulVec, dotProduct, hC4, zero_mul, Finset.sum_const_zero, Pi.zero_apply]
      · have e : (R' *ᵥ w) a.castSucc = (Rk *ᵥ w) a := rfl
        rw [e, hw]
        rfl
    have hHw : Hk *ᵥ w = 0 := by
      have e : W'ᵀ *ᵥ (W' *ᵥ (Hk *ᵥ w)) = Hk *ᵥ w := by
        rw [mulVec_mulVec, hWo, one_mulVec]
      have e2 : W' *ᵥ (Hk *ᵥ w) = 0 := by rw [mulVec_mulVec, hC1, hR'w]
      rw [← e, e2, mulVec_zero]
    have hsum : ∑ j, w j • Arnoldi.vec T z j = 0 := by
      apply hTinj
      rw [map_zero, Arnoldi.apply_sum, ← hHk, hHw]
      simp
    funext i
    have h1 := congrArg (fun v => inner ℝ (Arnoldi.vec T z i) v) hsum
    simp only [inner_sum, real_inner_smul_right, inner_zero_right] at h1
    rw [Finset.sum_eq_single i (fun j _ hji => by
        rw [Arnoldi.inner_vec_eq_zero _ _ (fun h => hji (Fin.ext h.symm)), mul_zero])
      (by simp), real_inner_self_eq_norm_sq,
      Arnoldi.norm_vec_eq_one_of_lt_grade _ _ (i.2.trans_le hkg), one_pow, mul_one] at h1
    exact h1
  have hRkunit : IsUnit Rk := mulVec_injective_iff_isUnit.1 fun w w' h' =>
    sub_eq_zero.1 (hker _ (by rw [mulVec_sub, h', sub_self]))
  have hdiag : ∀ i, Rk i i ≠ 0 := by
    have hdet := (isUnit_iff_isUnit_det Rk).1 hRkunit
    rw [det_of_isUpperTriangular hRkU] at hdet
    exact fun i => (Finset.prod_ne_zero_iff.1 hdet.ne_zero) i (Finset.mem_univ i)
  have hyR : Rk *ᵥ y = pk := GolubVanLoan.Chapter03.algorithm_3_1_2_spec hRkU hdiag pk
  -- the computed iterate in `𝔼`
  have hxE : WithLp.toLp 2 (x₀ + (of fun i (l : Fin k) => s.arnoldi.q l i) *ᵥ y) =
      WithLp.toLp 2 x₀ + ∑ j, y j • Arnoldi.vec T z j := by
    rw [WithLp.toLp_add]
    congr 1
    have hq : ∀ j : Fin k, Arnoldi.vec T z j = WithLp.toLp 2 (s.arnoldi.q j) :=
      fun j => ((hvec j j.2).1).symm
    simp_rw [hq, ← WithLp.toLp_smul, ← WithLp.toLp_sum]
    congr 1
    ext i
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hzE : z = WithLp.toLp 2 c - T (WithLp.toLp 2 x₀) := by
    rw [hzdef, hz, hT, toEuclideanLin_toLp, WithLp.toLp_sub]
  -- GMRES through the computed rotations
  obtain ⟨hmin', hres'⟩ := isMinResidualIterate_of_unitary_mul_hessenberg (A := T)
    (b := WithLp.toLp 2 c) (x₀ := WithLp.toLp 2 x₀) (hzE ▸ hkg) (W := W') hW'mem
    (fun j => by rw [← hzE, ← hHk, hC1]; exact hC4 j) (y := y) (fun i => by
      rw [← hzE, ← hHk, hC1]
      simp only [RCLike.ofReal_real_eq_id, id_eq]
      rw [← hβ₀, ← hC3]
      exact congrFun hyR i)
  rw [← hzE] at hmin' hres'
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hres'
  have hmin : IsMinResidualIterate T (WithLp.toLp 2 c) (WithLp.toLp 2 x₀) k
      (WithLp.toLp 2 (x₀ + (of fun i (l : Fin k) => s.arnoldi.q l i) *ᵥ y)) := by
    rw [hxE]
    exact hmin'
  refine ⟨hk, hvec, hmin, fun i hi => ?_, fun hdone => ?_⟩
  · have hiι : i = ι (Fin.last k) := Fin.ext hi
    rw [hxE, hres', ← hβ₀, ← hC3, hiι]
    exact (Real.norm_eq_abs _).symm
  · have hgk : grade T z ≤ k := by
      rcases hdn hdone with ⟨-, hb0⟩ | ⟨hpos, hh0⟩
      · have hz0 : z = 0 := norm_eq_zero.1 hb0
        rw [hz0, grade_zero]
        exact Nat.zero_le _
      · have e := (hvec (k - 1) (by omega)).2 k (by omega)
        rw [hh0] at e
        have e' : Arnoldi.coeff T z (k - 1 + 1) (k - 1) = 0 := by
          rw [Nat.sub_add_cancel hpos]; exact e.symm
        have := (Arnoldi.coeff_succ_self_eq_zero_iff T z (k - 1)).1 e'
        omega
    have happ := hmin.apply_eq_of_grade_le (hzE ▸ hgk) hTinj.injOn
    rw [hT, toEuclideanLin_toLp] at happ
    exact WithLp.toLp_injective 2 happ

/-- **Algorithm 11.4.2** of [golub2013matrix], exact correctness. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $b, x_0 \in \mathbb{R}^n$ and
$r_0 = b - Ax_0$, and let $m \in \mathbb{N}$. Run Algorithm 11.4.2 in exact arithmetic, and let
$k$ be its final step count and $\tilde x$ its result. Then:

* $k = \min(m, g)$, where $g$ is the grade of $r_0$ with respect to $A$;
* for $j < k$, the computed $q_{j+1}$ and $h_{ij}$ with $i \le j + 1$ are the Arnoldi vectors
  and coefficients of $r_0$;
* $\tilde x$ minimizes $\|b - Ax\|_2$ over $x_0 + \mathcal{K}(A, r_0, k)$;
* the entry $\rho_k$ of index $k$ of the rotated right-hand side satisfies
  $|\rho_k| = \|A\tilde x - b\|_2$;
* if the loop stopped on $\beta_k = 0$, then $A\tilde x = b$.

This is the statement of the source that $\tilde x$ "either solves $Ax = b$ or minimizes
$\|Ax - b\|_2$ over the affine space $x_0 + \mathcal{K}(A, r_0, m)$": if the loop does not stop
early, then $k = m$.

The modified Gram–Schmidt loop (11.4.11) is Gram–Schmidt in exact arithmetic
(`GolubVanLoan.Chapter10.algorithm_10_5_1_spec`). The rotations are those of `givens` (Algorithm
5.1.3), whose signs can differ from those of `Krylov.givensQ`. The proof,
`GolubVanLoan.Chapter11.gmresCore_spec`, uses only that they are orthogonal and give the
triangular form. -/
theorem algorithm_11_4_2_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (b x₀ : Fin n → ℝ)
    (m : ℕ) :
    let out := Id.run (algorithm_11_4_2 pure A b x₀ m)
    let T := toEuclideanLin A
    let r₀ : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 b - T (WithLp.toLp 2 x₀)
    out.1.arnoldi.k = min m (grade T r₀) ∧
      (∀ j < out.1.arnoldi.k, WithLp.toLp 2 (out.1.arnoldi.q j) = Arnoldi.vec T r₀ j ∧
        ∀ i ≤ j + 1, out.1.arnoldi.h i j = Arnoldi.coeff T r₀ i j) ∧
      IsMinResidualIterate T (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) out.1.arnoldi.k
        (WithLp.toLp 2 out.2) ∧
      (∀ i : Fin (m + 1), (i : ℕ) = out.1.arnoldi.k →
        |out.1.g i| = ‖WithLp.toLp 2 b - T (WithLp.toLp 2 out.2)‖) ∧
      (out.1.arnoldi.done = true → A *ᵥ out.2 = b) := by
  have hrun : Id.run (algorithm_11_4_2 pure A b x₀ m) =
      Id.run (gmresCore pure (fun q => GolubVanLoan.Chapter01.algorithm_1_1_3 pure A q 0) x₀
        (b - A *ᵥ x₀) m) := by
    simp only [algorithm_11_4_2, Id.run_bind, GolubVanLoan.Chapter01.algorithm_1_1_3_spec,
      mulVec_neg, ← sub_eq_add_neg]
  have hr₀ : WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀) =
      (WithLp.toLp 2 (b - A *ᵥ x₀) : EuclideanSpace ℝ (Fin n)) := by
    rw [toEuclideanLin_toLp, WithLp.toLp_sub]
  dsimp only
  rw [hrun, hr₀]
  exact gmresCore_spec hA
    (fun q => (GolubVanLoan.Chapter01.algorithm_1_1_3_spec A q 0).trans (zero_add _))
    b x₀ (b - A *ᵥ x₀) rfl m

end GMRESSpec

/-! ### §11.4.4: the polynomial point of view -/

/-- **Section 11.4.4** of [golub2013matrix], Krylov vectors as polynomials. Let
$A \in \mathbb{R}^{n \times n}$ and $q_1 \in \mathbb{R}^n$, and let the columns of
$Q_k \in \mathbb{R}^{n \times k}$ span $\mathcal{K}(A, q_1, k)$. Then for every
$y \in \mathbb{R}^k$ there is a real polynomial $\phi$ of degree less than $k$ with
$Q_ky = \phi(A)q_1$. Conversely, for every real polynomial $\phi$ of degree less than $k$ there
is $y \in \mathbb{R}^k$ with $Q_ky = \phi(A)q_1$.

The source says: "Suppose the columns of $Q_k \in \mathbb{R}^{n \times k}$ span
$\mathcal{K}(A, q_1, k)$. It follows that if $y \in \mathbb{R}^k$, then $Q_ky = \phi(A)q_1$ for
some polynomial $\phi$ that has degree $k - 1$ or less." The converse is added. The degree is
`Polynomial.degree`, so the zero polynomial is allowed. -/
theorem krylov_eq_aeval (A : Matrix (Fin n) (Fin n) ℝ) (q₁ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (Q : Fin k → EuclideanSpace ℝ (Fin n))
    (hQ : Submodule.span ℝ (Set.range Q) = Krylov.subspace (toEuclideanLin A) q₁ k) :
    (∀ y : Fin k → ℝ, ∃ φ : ℝ[X], φ.degree < k ∧ ∑ j, y j • Q j = aeval (toEuclideanLin A) φ q₁) ∧
      ∀ φ : ℝ[X], φ.degree < k → ∃ y : Fin k → ℝ,
        ∑ j, y j • Q j = aeval (toEuclideanLin A) φ q₁ := by
  refine ⟨fun y => ?_, fun φ hφ => ?_⟩
  · have hmem : ∑ j, y j • Q j ∈ Krylov.subspace (toEuclideanLin A) q₁ k := by
      rw [← hQ]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨φ, hφ, h⟩ := (mem_subspace_iff_exists_aeval _ _).1 hmem
    exact ⟨φ, hφ, h.symm⟩
  · have hmem := aeval_apply_mem_subspace (toEuclideanLin A) q₁ hφ
    rw [← hQ] at hmem
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem

/-- **Section 11.4.4** of [golub2013matrix], the minimal residual as a minimum over polynomials. Let
$A \in \mathbb{R}^{n \times n}$, let $b, x_0 \in \mathbb{R}^n$ and $r_0 = b - Ax_0$, and let
$x_k$ minimize $\|b - Ax\|_2$ over $x_0 + \mathcal{K}(A, r_0, k)$. Then $$\|b - Ax_k\|_2 =
\inf_{\deg \phi < k} \|(I - A\phi(A))r_0\|_2 = \inf_{\deg \psi \le k,\ \psi(0) = 1}
\|\psi(A)r_0\|_2,$$ where $\phi$ and $\psi$ range over real polynomials.

**Typo.** The source prints the middle term as $\|b - A(x_0 + \phi(A))r_0\|_2$, with a misplaced
parenthesis. It is $\|b - A(x_0 + \phi(A)r_0)\|_2 = \|(I - A\phi(A))r_0\|_2$.

The source writes the minima over $\phi \in \mathbb{P}_{k-1}$ and over $\psi \in \mathbb{P}_k$
with $\psi(0) = 1$. The statement writes them as infima over sets of polynomials. For $k = 0$
the first infimum is over $\phi = 0$ and the second over $\psi = 1$. -/
theorem minResidual_eq_iInf_poly (A : Matrix (Fin n) (Fin n) ℝ) {b x₀ x : EuclideanSpace ℝ (Fin n)}
    {k : ℕ} (hx : IsMinResidualIterate (toEuclideanLin A) b x₀ k x) :
    ‖b - toEuclideanLin A x‖ = ⨅ φ : {φ : ℝ[X] // φ.degree < k},
        ‖(b - toEuclideanLin A x₀) -
          toEuclideanLin A (aeval (toEuclideanLin A) φ.1 (b - toEuclideanLin A x₀))‖ ∧
      ‖b - toEuclideanLin A x‖ = ⨅ ψ : {ψ : ℝ[X] // ψ.degree ≤ k ∧ ψ.eval 0 = 1},
        ‖aeval (toEuclideanLin A) ψ.1 (b - toEuclideanLin A x₀)‖ := by
  set T := toEuclideanLin A
  refine ⟨?_, hx.norm_residual_eq_iInf⟩
  have hne : Nonempty {φ : ℝ[X] // φ.degree < k} := ⟨⟨0, by
    rw [degree_zero]; exact WithBot.bot_lt_coe k⟩⟩
  have hbdd : BddBelow (Set.range fun φ : {φ : ℝ[X] // φ.degree < k} =>
      ‖(b - T x₀) - T (aeval T φ.1 (b - T x₀))‖) :=
    ⟨0, by rintro _ ⟨φ, rfl⟩; exact norm_nonneg _⟩
  have hres : ∀ v, b - T (x₀ + v) = (b - T x₀) - T v := fun v => by rw [map_add]; abel
  refine le_antisymm (le_ciInf fun φ => ?_) ?_
  · have h := hx.min (x₀ + aeval T φ.1 (b - T x₀))
      (by rw [add_sub_cancel_left]; exact aeval_apply_mem_subspace T _ φ.2)
    rwa [hres] at h
  · obtain ⟨φ, hφ, h⟩ := (mem_subspace_iff_exists_aeval T (b - T x₀)).1 hx.mem
    refine (ciInf_le hbdd ⟨φ, hφ⟩).trans_eq ?_
    rw [h, ← hres, add_sub_cancel]

/-! ### §11.4.5: the unsymmetric Lanczos family -/

/-- **Equations (11.4.12)–(11.4.13)** of [golub2013matrix], the two-sided Lanczos process. Let
$A \in \mathbb{R}^{n \times n}$, let $r_0, \tilde r_0, q_1, \tilde q_1 \in \mathbb{R}^n$ with
$r_0 = \beta_0q_1$ and $\tilde r_0 = \gamma_0\tilde q_1$ for some $\beta_0, \gamma_0 \neq 0$,
and suppose that the two-sided Lanczos process of $A$ and $A^T$ from $(q_1, \tilde q_1)$ has no
breakdown through step $k$; this includes $\tilde q_1^Tq_1 = 1$. Write $v_0, v_1, \dots$ and
$w_0, w_1, \dots$ for the vectors of the process, with $v_0 = q_1$ and $w_0 = \tilde q_1$, and
$T$ for its tridiagonal coefficient array, with $\alpha_j$ on the diagonal, $\delta_j$ below it
and $\beta_j$ above it. Then:

* for $j < k$, $Av_j = \beta_jv_{j-1} + \alpha_jv_j + \delta_{j+1}v_{j+1}$, with $v_{-1} = 0$;
  this is column $j$ of $AQ_k = Q_kT_k + r_ke_k^T$;
* $w_i^Tv_k = 0$ for $i < k$, that is, $\tilde Q_k^Tr_k = 0$;
* $w_i^Tv_j = \delta_{ij}$ for $i, j < k$, that is, $\tilde Q_k^TQ_k = I_k$;
* $w_i^TAv_j = T_{ij}$ for $i, j < k$, that is, $\tilde Q_k^TAQ_k = T_k$;
* $T_{ij} = 0$ for $|i - j| > 1$, so $T_k$ is tridiagonal;
* $\operatorname{span}\{v_0, \dots, v_{k-1}\} = \mathcal{K}(A, r_0, k)$ and
  $\operatorname{span}\{w_0, \dots, w_{k-1}\} = \mathcal{K}(A^T, \tilde r_0, k)$.

The source says: "Suppose we complete $k$ steps of (10.5.11) with $q_1 = r_0/\beta_0$ … and
$r_0^T\tilde r_0 \neq 0$. This means we have the partial factorizations
$AQ_k = Q_kT_k + r_ke_k^T$, $\tilde Q_k^Tr_k = 0$, $A^T\tilde Q_k = \tilde Q_kT_k^T + \tilde
r_ke_k^T$, $Q_k^T\tilde r_k = 0$ where $\operatorname{ran}(Q_k) = \mathcal{K}(A, r_0, k)$,
$\operatorname{ran}(\tilde Q_k) = \mathcal{K}(A^T, \tilde r_0, k)$. In addition,
$\tilde Q_k^TQ_k = I_k$ and $\tilde Q_k^TAQ_k = T_k$ is tridiagonal." The shadow vector
$\tilde q_1$ is scaled so that $\tilde q_1^Tq_1 = 1$, the normalization of the pair in the
source. The source's $r_k = \beta_kq_{k+1}$ is $\delta_kv_k$ in this indexing.

The process is `BiLanczos` for `Matrix.toEuclideanLin A` and its adjoint
`Matrix.toEuclideanLin Aᵀ`: $v_j$ is `BiLanczos.vec`, $w_j$ is `BiLanczos.dualVec`, $T$ is
`BiLanczos.coeff`, and "no breakdown through step $k$" is `BiLanczos.NoBreakdown`. The dual
relation (11.4.13) is `GolubVanLoan.Chapter11.equation_11_4_13`. -/
theorem equation_11_4_12 (A : Matrix (Fin n) (Fin n) ℝ) {r₀ rt₀ q₁ qt₁ : EuclideanSpace ℝ (Fin n)}
    {β₀ γ₀ : ℝ} (hβ : β₀ ≠ 0) (hγ : γ₀ ≠ 0) (hr : r₀ = β₀ • q₁) (hrt : rt₀ = γ₀ • qt₁) {k : ℕ}
    (h : BiLanczos.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ k) :
    (∀ j < k, toEuclideanLin A (BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j) =
      BiLanczos.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j •
          BiLanczos.vecPrev (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j +
        BiLanczos.alpha (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j •
          BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j +
        BiLanczos.delta (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ (j + 1) •
          BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ (j + 1)) ∧
    (∀ i < k, inner ℝ (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i)
      (BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ k) = 0) ∧
    (∀ i < k, ∀ j < k, inner ℝ (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i)
      (BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j) = if i = j then 1 else 0) ∧
    (∀ i < k, ∀ j < k, inner ℝ (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i)
      (toEuclideanLin A (BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j)) =
        BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i j) ∧
    (∀ i j, i ≠ j → i ≠ j + 1 → j ≠ i + 1 →
      BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i j = 0) ∧
    Submodule.span ℝ (BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ '' Set.Iio k) =
      Krylov.subspace (toEuclideanLin A) r₀ k ∧
    Submodule.span ℝ
        (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ '' Set.Iio k) =
      Krylov.subspace (toEuclideanLin Aᵀ) rt₀ k := by
  refine ⟨fun j hj => BiLanczos.apply_vec _ _ _ _ (h.delta_ne_zero j hj), fun i hi => ?_,
    fun i hi j hj => BiLanczos.inner_dualVec_vec h hi.le hj.le, fun i hi j hj => ?_,
    fun i j h1 h2 h3 => BiLanczos.coeff_eq_zero _ _ _ _ h1 h2 h3, ?_, ?_⟩
  · rw [BiLanczos.inner_dualVec_vec h hi.le le_rfl, ite_eq_right hi.ne]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact BiLanczos.inner_dualVec_apply_vec h (by omega) (by omega)
  · rw [BiLanczos.span_vec h, hr, subspace_smul_of_ne_zero _ _ hβ]
  · rw [BiLanczos.span_dualVec h, hrt, subspace_smul_of_ne_zero _ _ hγ]

/-- **Equation (11.4.13)** of [golub2013matrix], the dual relation of the two-sided Lanczos process.
Let $A \in \mathbb{R}^{n \times n}$, and suppose that the two-sided Lanczos process of $A$ and
$A^T$ from $(q_1, \tilde q_1)$ has no breakdown through step $k$, with the notation of
`GolubVanLoan.Chapter11.equation_11_4_12`. Then:

* for $j < k$, $A^Tw_j = \delta_jw_{j-1} + \alpha_jw_j + \beta_{j+1}w_{j+1}$, with $w_{-1} = 0$;
  this is column $j$ of $A^T\tilde Q_k = \tilde Q_kT_k^T + \tilde r_ke_k^T$;
* $v_i^Tw_k = 0$ for $i < k$, that is, $Q_k^T\tilde r_k = 0$, because the source's $\tilde r_k$
  is a multiple of $w_k$. -/
theorem equation_11_4_13 (A : Matrix (Fin n) (Fin n) ℝ) {q₁ qt₁ : EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (h : BiLanczos.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ k) :
    (∀ j < k, toEuclideanLin Aᵀ
        (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j) =
      BiLanczos.delta (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j •
          BiLanczos.dualVecPrev (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j +
        BiLanczos.alpha (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j •
          BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j +
        BiLanczos.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ (j + 1) •
          BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ (j + 1)) ∧
    ∀ i < k, inner ℝ (BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i)
      (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ k) = 0 := by
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have := BiLanczos.apply_dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁
      (h.delta_ne_zero j hj)
    simpa only [starRingEnd_real, RingHom.id_apply] using this
  · rw [BiLanczos.inner_vec_dualVec h hi.le le_rfl, ite_eq_right hi.ne]

/-- **Section 11.4.5** of [golub2013matrix], BiCG as a Petrov–Galerkin method. Let
$A \in \mathbb{R}^{n \times n}$, $b, x_0 \in \mathbb{R}^n$ and $r_0 = b - Ax_0$, and suppose
that the two-sided Lanczos process of $A$ and $A^T$ from $(q_1, \tilde q_1)$ has no breakdown
through step $k + 1$, with the notation of `GolubVanLoan.Chapter11.equation_11_4_12`. Let
$y \in \mathbb{R}^{k+1}$ solve $T_{k+1}y = \tilde Q_{k+1}^Tr_0$. Then:

* the residual of $x = x_0 + Q_{k+1}y$ is orthogonal to $w_0, \dots, w_k$, that is,
  $\tilde Q_{k+1}^T(b - Ax) = 0$;
* if $T_{k+1} = LU$ with $L$ and $U$ nonsingular, then
  $y = U^{-1}(L^{-1}(\tilde Q_{k+1}^Tr_0))$.

The source says: "In step $k$ of the biconjugate gradient (BiCG) method, an iterate
$x_k = x_0 + Q_ky_k$ is produced where $y_k \in \mathbb{R}^k$ solves the $k$-by-$k$ tridiagonal
system $T_ky_k = \tilde Q_k^Tr_0$. It follows that $\tilde Q_k^T(b - Ax_k) = 0$. … Assume that
$T_k$ has an LU factorization $T_k = L_kU_k$ … It follows that $x_k = x_0 +
(Q_kU_k^{-1})(L_k^{-1}(\tilde Q_k^Tr_0))$." The statement is at $k + 1$ in place of $k$, and it
does not need $q_1 = r_0/\beta_0$. The BiCG recurrence of Figure 11.4.1 computes this iterate
(`BCG.isPetrovGalerkin`, through `GolubVanLoan.Chapter11.bicg_spec`). The proof specializes
`BiLanczos.inner_dualVec_sub_apply_sum_eq_zero`. -/
theorem bicg_residual_orthogonal (A : Matrix (Fin n) (Fin n) ℝ)
    {b x₀ q₁ qt₁ : EuclideanSpace ℝ (Fin n)} {k : ℕ}
    (h : BiLanczos.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ (k + 1))
    {y : Fin (k + 1) → ℝ}
    (hy : hessenbergSqOf (BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁) (k + 1)
        *ᵥ y = fun i : Fin (k + 1) => inner ℝ
          (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ (i : ℕ))
          (b - toEuclideanLin A x₀)) :
    (∀ i : Fin (k + 1), inner ℝ
        (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i)
        (b - toEuclideanLin A (x₀ + ∑ j, y j •
          BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j)) = 0) ∧
    ∀ L U : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ, IsUnit L → IsUnit U →
      hessenbergSqOf (BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁) (k + 1) =
        L * U →
      y = U⁻¹ *ᵥ (L⁻¹ *ᵥ fun i : Fin (k + 1) => inner ℝ
        (BiLanczos.dualVec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ (i : ℕ))
        (b - toEuclideanLin A x₀)) := by
  set T := toEuclideanLin A
  set q := BiLanczos.vec T (toEuclideanLin Aᵀ) q₁ qt₁
  set qt := BiLanczos.dualVec T (toEuclideanLin Aᵀ) q₁ qt₁
  refine ⟨fun i => ?_, fun L U hL hU hLU => ?_⟩
  · rw [map_add, sub_add_eq_sub_sub]
    exact BiLanczos.inner_dualVec_sub_apply_sum_eq_zero h hy i
  · have hLd := (Matrix.isUnit_iff_isUnit_det L).mp hL
    have hUd := (Matrix.isUnit_iff_isUnit_det U).mp hU
    rw [← hy, mulVec_mulVec, mulVec_mulVec, hLU, Matrix.mul_assoc, ← Matrix.mul_assoc L⁻¹,
      nonsing_inv_mul L hLd, Matrix.one_mul, nonsing_inv_mul U hUd, one_mulVec]

/-! ### Figure 11.4.1 as programs -/

/-- The state of the BiCG column of Figure 11.4.1: the iterate $x_c$, the residual $r_c$, the shadow
residual $\tilde r_c$, and the two directions $p_c$ and $\tilde p_c$. -/
structure BiCGState (n : ℕ) where
  /-- The iterate $x_c$. -/
  x : Fin n → ℝ
  /-- The residual $r_c$. -/
  r : Fin n → ℝ
  /-- The shadow residual $\tilde r_c$. -/
  rt : Fin n → ℝ
  /-- The direction $p_c$. -/
  p : Fin n → ℝ
  /-- The shadow direction $\tilde p_c$. -/
  pt : Fin n → ℝ

/-- The state of the CGS column of Figure 11.4.1: the iterate $x_c$, the residual $r_c$, the
auxiliary vector $u_c$ and the direction $p_c$. -/
structure CGSState (n : ℕ) where
  /-- The iterate $x_c$. -/
  x : Fin n → ℝ
  /-- The residual $r_c$. -/
  r : Fin n → ℝ
  /-- The auxiliary vector $u_c$. -/
  u : Fin n → ℝ
  /-- The direction $p_c$. -/
  p : Fin n → ℝ

/-- The state of the BiCGstab column of Figure 11.4.1: the iterate $x_c$, the residual $r_c$ and the
direction $p_c$. -/
structure BiCGstabState (n : ℕ) where
  /-- The iterate $x_c$. -/
  x : Fin n → ℝ
  /-- The residual $r_c$. -/
  r : Fin n → ℝ
  /-- The direction $p_c$. -/
  p : Fin n → ℝ

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One pass of the BiCG update formulae of Figure 11.4.1:
```
μ = r̃_cᵀr_c / p̃_cᵀAp_c,   x₊ = x_c + μp_c,   r₊ = r_c − μAp_c,   r̃₊ = r̃_c − μAᵀp̃_c,
τ = r̃₊ᵀr₊ / r̃_cᵀr_c,      p₊ = r₊ + τp_c,    p̃₊ = r̃₊ + τp̃_c
```
The products with $A$ and $A^T$ are gaxpys onto $0$ (Algorithm 1.1.3), the inner products are
Algorithm 1.1.1, the updates are saxpys (Algorithm 1.1.2), and each quotient is rounded once. -/
noncomputable def bicgStep (A : Matrix (Fin n) (Fin n) ℝ) (s : BiCGState n) :
    M (BiCGState n) := do
  let Ap ← Chapter01.algorithm_1_1_3 rnd A s.p 0
  let Atpt ← Chapter01.algorithm_1_1_3 rnd Aᵀ s.pt 0
  let ρ ← Chapter01.algorithm_1_1_1 rnd s.rt s.r
  let σ ← Chapter01.algorithm_1_1_1 rnd s.pt Ap
  let μ ← rnd (ρ / σ)
  let x ← Chapter01.algorithm_1_1_2 rnd μ s.p s.x
  let r ← Chapter01.algorithm_1_1_2 rnd (-μ) Ap s.r
  let rt ← Chapter01.algorithm_1_1_2 rnd (-μ) Atpt s.rt
  let ρn ← Chapter01.algorithm_1_1_1 rnd rt r
  let τ ← rnd (ρn / ρ)
  let p ← Chapter01.algorithm_1_1_2 rnd τ s.p r
  let pt ← Chapter01.algorithm_1_1_2 rnd τ s.pt rt
  pure ⟨x, r, rt, p, pt⟩

/-- **Figure 11.4.1** of [golub2013matrix], the BiCG column. Let $A \in \mathbb{R}^{n \times n}$ and
$b, x_0, \tilde r_0 \in \mathbb{R}^n$. The program computes $r_0 = b - Ax_0$, sets $x_c = x_0$,
$p_c = r_c = r_0$ and $\tilde p_c = \tilde r_c = \tilde r_0$, and then runs `fuel` passes of
`GolubVanLoan.Chapter11.bicgStep`.

The figure gives the initializations "$r_0 = b - Ax_0$, $\tilde r_0^Tr_0 \neq 0$, $x_c = x_0$,
$p_c = r_c = r_0$, $\tilde p_c = \tilde r_c = \tilde r_0$" and the update formulae, but no
stopping test, so the number of passes `fuel` is the last argument. The condition
$\tilde r_0^Tr_0 \neq 0$ is not a test of the program; the theorems state the hypotheses that
they need. -/
noncomputable def bicg (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (fuel : ℕ) :
    M (BiCGState n) := do
  let Ax ← Chapter01.algorithm_1_1_3 rnd A x₀ 0
  let r₀ ← Chapter01.vecSub rnd b Ax
  (List.range fuel).foldlM (fun s _ => bicgStep rnd A s) ⟨x₀, r₀, rt₀, r₀, rt₀⟩

/-- One pass of the CGS update formulae of Figure 11.4.1:
```
μ = r̃₀ᵀr_c / r̃₀ᵀAp_c,   q_c = u_c − μAp_c,   x₊ = x_c + μ(u_c + q_c),
r₊ = r_c − μA(u_c + q_c),   τ = r̃₀ᵀr₊ / r̃₀ᵀr_c,   u₊ = r₊ + τq_c,   p₊ = u₊ + τ(q_c + τp_c)
```
The products with $A$ are gaxpys onto $0$ (Algorithm 1.1.3), the inner products are Algorithm
1.1.1, the updates are saxpys (Algorithm 1.1.2) and one rounded vector sum, and each quotient is
rounded once. -/
noncomputable def cgsStep (A : Matrix (Fin n) (Fin n) ℝ) (rt₀ : Fin n → ℝ) (s : CGSState n) :
    M (CGSState n) := do
  let Ap ← Chapter01.algorithm_1_1_3 rnd A s.p 0
  let ρ ← Chapter01.algorithm_1_1_1 rnd rt₀ s.r
  let σ ← Chapter01.algorithm_1_1_1 rnd rt₀ Ap
  let μ ← rnd (ρ / σ)
  let q ← Chapter01.algorithm_1_1_2 rnd (-μ) Ap s.u
  let uq ← Chapter01.vecAdd rnd s.u q
  let Auq ← Chapter01.algorithm_1_1_3 rnd A uq 0
  let x ← Chapter01.algorithm_1_1_2 rnd μ uq s.x
  let r ← Chapter01.algorithm_1_1_2 rnd (-μ) Auq s.r
  let ρn ← Chapter01.algorithm_1_1_1 rnd rt₀ r
  let τ ← rnd (ρn / ρ)
  let u ← Chapter01.algorithm_1_1_2 rnd τ q r
  let w ← Chapter01.algorithm_1_1_2 rnd τ s.p q
  let p ← Chapter01.algorithm_1_1_2 rnd τ w u
  pure ⟨x, r, u, p⟩

/-- **Figure 11.4.1** of [golub2013matrix], the CGS column. Let $A \in \mathbb{R}^{n \times n}$ and
$b, x_0, \tilde r_0 \in \mathbb{R}^n$. The program computes $r_0 = b - Ax_0$, sets $x_c = x_0$,
$p_c = r_c = r_0$ and $u_c = r_c$, and then runs `fuel` passes of
`GolubVanLoan.Chapter11.cgsStep`. Only products with $A$ occur.

**Typo.** The figure prints the initial condition $\tilde r_0^T\tilde r_0 \neq 0$. It is
$\tilde r_0^Tr_0 \neq 0$.

As for `GolubVanLoan.Chapter11.bicg`, the figure has no stopping test, and the program does not
test the initial condition. -/
noncomputable def cgs (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (fuel : ℕ) :
    M (CGSState n) := do
  let Ax ← Chapter01.algorithm_1_1_3 rnd A x₀ 0
  let r₀ ← Chapter01.vecSub rnd b Ax
  (List.range fuel).foldlM (fun s _ => cgsStep rnd A rt₀ s) ⟨x₀, r₀, r₀, r₀⟩

/-- One pass of the BiCGstab update formulae of Figure 11.4.1:
```
μ = r̃₀ᵀr_c / r̃₀ᵀAp_c,   s_c = r_c − μAp_c,   ω = s_cᵀAs_c / (As_c)ᵀ(As_c),
x₊ = x_c + μp_c + ωs_c,   r₊ = s_c − ωAs_c,   τ = (r̃₀ᵀr₊)μ / ((r̃₀ᵀr_c)ω),
p₊ = r₊ + τ(p_c − ωAp_c)
```
The inner product $s_c^TAs_c$ is accumulated as $(As_c)^Ts_c$, from the same products. The
operations are rounded as in `GolubVanLoan.Chapter11.bicgStep`, and $\tau$ is computed as
$\mathrm{fl}(\mathrm{fl}(\tilde r_0^Tr_+ \cdot \mu)/\mathrm{fl}(\tilde r_0^Tr_c \cdot \omega))$. -/
noncomputable def bicgstabStep (A : Matrix (Fin n) (Fin n) ℝ) (rt₀ : Fin n → ℝ)
    (st : BiCGstabState n) : M (BiCGstabState n) := do
  let Ap ← Chapter01.algorithm_1_1_3 rnd A st.p 0
  let ρ ← Chapter01.algorithm_1_1_1 rnd rt₀ st.r
  let σ ← Chapter01.algorithm_1_1_1 rnd rt₀ Ap
  let μ ← rnd (ρ / σ)
  let s ← Chapter01.algorithm_1_1_2 rnd (-μ) Ap st.r
  let As ← Chapter01.algorithm_1_1_3 rnd A s 0
  let η ← Chapter01.algorithm_1_1_1 rnd As s
  let θ ← Chapter01.algorithm_1_1_1 rnd As As
  let ω ← rnd (η / θ)
  let x₁ ← Chapter01.algorithm_1_1_2 rnd μ st.p st.x
  let x ← Chapter01.algorithm_1_1_2 rnd ω s x₁
  let r ← Chapter01.algorithm_1_1_2 rnd (-ω) As s
  let ρn ← Chapter01.algorithm_1_1_1 rnd rt₀ r
  let num ← rnd (ρn * μ)
  let den ← rnd (ρ * ω)
  let τ ← rnd (num / den)
  let w ← Chapter01.algorithm_1_1_2 rnd (-ω) Ap st.p
  let p ← Chapter01.algorithm_1_1_2 rnd τ w r
  pure ⟨x, r, p⟩

/-- **Figure 11.4.1** of [golub2013matrix], the BiCGstab column. Let $A \in \mathbb{R}^{n \times n}$
and $b, x_0, \tilde r_0 \in \mathbb{R}^n$. The program computes $r_0 = b - Ax_0$, sets
$x_c = x_0$ and $p_c = r_c = r_0$, and then runs `fuel` passes of
`GolubVanLoan.Chapter11.bicgstabStep`.

**Typo.** The figure prints the initial condition $\tilde r_0^T\tilde r_0 \neq 0$. It is
$\tilde r_0^Tr_0 \neq 0$.

As for `GolubVanLoan.Chapter11.bicg`, the figure has no stopping test, and the program does not
test the initial condition. -/
noncomputable def bicgstab (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (fuel : ℕ) :
    M (BiCGstabState n) := do
  let Ax ← Chapter01.algorithm_1_1_3 rnd A x₀ 0
  let r₀ ← Chapter01.vecSub rnd b Ax
  (List.range fuel).foldlM (fun s _ => bicgstabStep rnd A rt₀ s) ⟨x₀, r₀, r₀⟩

end Programs

/-! ### Exact semantics: the backbone iterations -/

/-- A BiCG state, read as a state `BCG.State` of the backbone on `EuclideanSpace ℝ (Fin n)`. -/
def BiCGState.toState (s : BiCGState n) : BCG.State (EuclideanSpace ℝ (Fin n)) :=
  ⟨WithLp.toLp 2 s.x, WithLp.toLp 2 s.r, WithLp.toLp 2 s.rt, WithLp.toLp 2 s.p, WithLp.toLp 2 s.pt⟩

/-- A CGS state, read as a state `CGS.State` of the backbone on `EuclideanSpace ℝ (Fin n)`. -/
def CGSState.toState (s : CGSState n) : CGS.State (EuclideanSpace ℝ (Fin n)) :=
  ⟨WithLp.toLp 2 s.x, WithLp.toLp 2 s.r, WithLp.toLp 2 s.u, WithLp.toLp 2 s.p⟩

/-- A BiCGstab state, read as a state `BiCGSTAB.State` of the backbone on
`EuclideanSpace ℝ (Fin n)`. -/
def BiCGstabState.toState (s : BiCGstabState n) :
    BiCGSTAB.State (EuclideanSpace ℝ (Fin n)) :=
  ⟨WithLp.toLp 2 s.x, WithLp.toLp 2 s.r, WithLp.toLp 2 s.p⟩

/-- The exact BiCG pass is the backbone step `BCG.step` for $A$ and its adjoint $A^T$. -/
private theorem bicgStep_exact (A : Matrix (Fin n) (Fin n) ℝ) (s : BiCGState n) :
    (Id.run (bicgStep pure A s)).toState =
      BCG.step (toEuclideanLin A) (toEuclideanLin Aᵀ) s.toState := by
  simp only [bicgStep, Id.run_bind, Id.run_pure, Chapter01.algorithm_1_1_1_spec,
    Chapter01.algorithm_1_1_2_spec, Chapter01.algorithm_1_1_3_spec, zero_add]
  simp only [BiCGState.toState, BCG.step, BCG.stepAlpha, starRingEnd_real, RingHom.id_apply,
    ← WithLp.toLp_add, ← WithLp.toLp_smul, ← WithLp.toLp_sub, toEuclideanLin_toLp, inner_toLp,
    neg_smul, ← sub_eq_add_neg]

/-- The exact CGS pass is the backbone `CGS.step`. -/
private theorem cgsStep_exact (A : Matrix (Fin n) (Fin n) ℝ) (rt₀ : Fin n → ℝ)
    (s : CGSState n) :
    (Id.run (cgsStep pure A rt₀ s)).toState =
      CGS.step (toEuclideanLin A) (WithLp.toLp 2 rt₀) s.toState := by
  simp only [cgsStep, Id.run_bind, Id.run_pure, Chapter01.algorithm_1_1_1_spec,
    Chapter01.algorithm_1_1_2_spec, Chapter01.algorithm_1_1_3_spec, Chapter01.vecAdd_spec,
    zero_add]
  simp only [CGSState.toState, CGS.step, ← WithLp.toLp_add, ← WithLp.toLp_smul,
    ← WithLp.toLp_sub, toEuclideanLin_toLp, inner_toLp, neg_smul, ← sub_eq_add_neg]

/-- The exact BiCGstab pass is the backbone `BiCGSTAB.step`. -/
private theorem bicgstabStep_exact (A : Matrix (Fin n) (Fin n) ℝ) (rt₀ : Fin n → ℝ)
    (s : BiCGstabState n) :
    (Id.run (bicgstabStep pure A rt₀ s)).toState =
      BiCGSTAB.step (toEuclideanLin A) (WithLp.toLp 2 rt₀) s.toState := by
  simp only [bicgstabStep, Id.run_bind, Id.run_pure, Chapter01.algorithm_1_1_1_spec,
    Chapter01.algorithm_1_1_2_spec, Chapter01.algorithm_1_1_3_spec, zero_add]
  simp only [BiCGstabState.toState, BiCGSTAB.step, ← WithLp.toLp_add, ← WithLp.toLp_smul,
    ← WithLp.toLp_sub, toEuclideanLin_toLp, inner_toLp, neg_smul, ← sub_eq_add_neg,
    div_mul_div_comm]

/-- The exact initialization computes $r_0 = b - Ax_0$. -/
private theorem residual_init_exact (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) :
    Id.run (Chapter01.vecSub pure b (Id.run (Chapter01.algorithm_1_1_3 pure A x₀ 0))) =
      b - A *ᵥ x₀ := by
  rw [Chapter01.algorithm_1_1_3_spec, zero_add, Chapter01.vecSub_spec]

/-- **Figure 11.4.1** of [golub2013matrix], BiCG in exact arithmetic. Let
$A \in \mathbb{R}^{n \times n}$ and $b, x_0, \tilde r_0 \in \mathbb{R}^n$, let $r_0 = b - Ax_0$,
and let $x_k, r_k, \tilde r_k, p_k, \tilde p_k$ be the state after $k$ exact passes of
`GolubVanLoan.Chapter11.bicg`. Then:

* for every $k$, the state is the state `BCG.iterate` of the biconjugate gradient iteration of
  the backbone, for $A$ and its adjoint $A^T$;
* if BiCG does not break down through step $m$, then for $i \neq j$ with $i, j \le m$ the
  residuals are biorthogonal, $\tilde r_j^Tr_i = 0$, and the directions are $A$-biconjugate,
  $\tilde p_j^TAp_i = 0$;
* under the same hypothesis, $x_m$ is the Petrov–Galerkin iterate:
  $x_m \in x_0 + \mathcal{K}(A, r_0, m)$, and $b - Ax_m$ is orthogonal to
  $\mathcal{K}(A^T, \tilde r_0, m)$.

The iteration `BCG.iterate` is the recurrence of Algorithm 7.3 of [saad2003iterative]. "No
breakdown through step $m$" is `BCG.NoBreakdown`: neither $\tilde r_k^Tr_k$ nor
$\tilde p_k^TAp_k$ vanishes for $k < m$. The Petrov–Galerkin iterate is `IsPetrovGalerkin`; it
is the iterate of `GolubVanLoan.Chapter11.bicg_residual_orthogonal`. -/
theorem bicg_spec (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) :
    (∀ k, (Id.run (bicg pure A b x₀ rt₀ k)).toState =
      BCG.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
        (WithLp.toLp 2 rt₀) k) ∧
    ∀ m, BCG.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
        (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) m →
      (∀ i j, i ≤ m → j ≤ m → i ≠ j →
        (Id.run (bicg pure A b x₀ rt₀ j)).rt ⬝ᵥ (Id.run (bicg pure A b x₀ rt₀ i)).r = 0 ∧
        (Id.run (bicg pure A b x₀ rt₀ j)).pt ⬝ᵥ (A *ᵥ (Id.run (bicg pure A b x₀ rt₀ i)).p) = 0) ∧
      IsPetrovGalerkin (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
        (Krylov.subspace (toEuclideanLin A) (WithLp.toLp 2 (b - A *ᵥ x₀)) m)
        (Krylov.subspace (toEuclideanLin Aᵀ) (WithLp.toLp 2 rt₀) m)
        (WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ m)).x) := by
  have hspec : ∀ k, (Id.run (bicg pure A b x₀ rt₀ k)).toState =
      BCG.iterate (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
        (WithLp.toLp 2 rt₀) k := by
    intro k
    have h := foldlM_range_transport (bicgStep pure A)
      (BCG.step (toEuclideanLin A) (toEuclideanLin Aᵀ)) BiCGState.toState (bicgStep_exact A) k
    simp only [bicg, Id.run_bind, residual_init_exact, h]
    simp only [BCG.iterate, BiCGState.toState, WithLp.toLp_sub, toEuclideanLin_toLp]
  refine ⟨hspec, fun m hm => ⟨fun i j hi hj hij => ⟨?_, ?_⟩, ?_⟩⟩
  · have h := BCG.inner_residual_dualResidual_eq_zero hm hi hj hij
    rw [BCG.dualResidual, BCG.residual, ← hspec, ← hspec] at h
    simpa only [BiCGState.toState, inner_toLp, dotProduct_comm] using h
  · have h := BCG.inner_dualDirection_apply_direction_eq_zero hm hi hj hij
    rw [BCG.dualDirection, BCG.direction, ← hspec, ← hspec] at h
    simpa only [BiCGState.toState, toEuclideanLin_toLp, inner_toLp, dotProduct_comm] using h
  · have h := BCG.isPetrovGalerkin hm
    rw [← hspec] at h
    simpa only [WithLp.toLp_sub, toEuclideanLin_toLp, BiCGState.toState] using h

/-- **Section 11.4.5** of [golub2013matrix], BiCG for a symmetric matrix. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and $b, x_0 \in \mathbb{R}^n$, and run
`GolubVanLoan.Chapter11.bicg` in exact arithmetic with $\tilde r_0 = r_0 = b - Ax_0$. Then after
every number $k$ of passes, $\tilde r_k = r_k$ and $\tilde p_k = p_k$, and $x_k$, $r_k$ and
$p_k$ are the iterate, the residual and the direction of the conjugate gradient iteration
`CG.iterate`, which Algorithm 11.3.3 computes.

**Generalization.** The source says: "BiCG collapses to CG if $A$ is symmetric positive definite
and $\tilde r_0 = r_0$." The identity of the recurrences needs only symmetry; positive
definiteness is what makes CG well defined. -/
theorem bicg_eq_cg {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) (b x₀ : Fin n → ℝ) (k : ℕ) :
    WithLp.toLp 2 (Id.run (bicg pure A b x₀ (b - A *ᵥ x₀) k)).x =
        (CG.iterate (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) k).x ∧
      WithLp.toLp 2 (Id.run (bicg pure A b x₀ (b - A *ᵥ x₀) k)).r =
        (CG.iterate (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) k).r ∧
      WithLp.toLp 2 (Id.run (bicg pure A b x₀ (b - A *ᵥ x₀) k)).p =
        (CG.iterate (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) k).p ∧
      (Id.run (bicg pure A b x₀ (b - A *ᵥ x₀) k)).rt =
        (Id.run (bicg pure A b x₀ (b - A *ᵥ x₀) k)).r ∧
      (Id.run (bicg pure A b x₀ (b - A *ᵥ x₀) k)).pt =
        (Id.run (bicg pure A b x₀ (b - A *ᵥ x₀) k)).p := by
  have h := (bicg_spec A b x₀ (b - A *ᵥ x₀)).1 k
  have hT : Aᵀ = A := hA
  have hr₀ : (WithLp.toLp 2 (b - A *ᵥ x₀) : EuclideanSpace ℝ (Fin n)) =
      WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀) := by
    rw [WithLp.toLp_sub, toEuclideanLin_toLp]
  rw [hT, hr₀, BCG.iterate_self_eq_cg] at h
  have hx := congrArg BCG.State.x h
  have hr := congrArg BCG.State.r h
  have hrs := congrArg BCG.State.rs h
  have hp := congrArg BCG.State.p h
  have hps := congrArg BCG.State.ps h
  simp only [BiCGState.toState] at hx hr hrs hp hps
  exact ⟨hx, hr, hp, WithLp.toLp_injective 2 (hrs.trans hr.symm),
    WithLp.toLp_injective 2 (hps.trans hp.symm)⟩

/-- **Equation (11.4.14)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and
$b, x_0, \tilde r_0 \in \mathbb{R}^n$, let $r_0 = b - Ax_0$, and let
$r_k, \tilde r_k, p_k, \tilde p_k$ be the vectors after $k$ exact passes of
`GolubVanLoan.Chapter11.bicg`. There are real polynomials $\psi_k$ and $\phi_k$ of degree at
most $k$, with $\psi_k(0) = 1$, such that $$r_k = \psi_k(A)r_0, \quad p_k = \phi_k(A)r_0, \quad
\tilde r_k = \psi_k(A^T)\tilde r_0, \quad \tilde p_k = \phi_k(A^T)\tilde r_0.$$

**Correction.** The source prints $\phi_k(0) = 1$, which is false: $\phi_1(0) = 1 + \tau_0$. The
statement asserts $\psi_k(0) = 1$ and makes no claim about $\phi_k(0)$.

The source says: "After $k$ steps of the procedure we have degree-$k$ polynomials $\psi_k$ and
$\phi_k$ so that $r_k = \psi_k(A)r_0$, $p_k = \phi_k(A)r_0$,
$\tilde r_k = \psi_k(A^T)\tilde r_0$, $\tilde p_k = \phi_k(A^T)\tilde r_0$." The polynomials are
`BCG.residualPoly` and `BCG.directionPoly`, defined by $\psi_0 = \phi_0 = 1$,
$\psi_{k+1} = \psi_k - \mu_kX\phi_k$ and $\phi_{k+1} = \psi_{k+1} + \tau_k\phi_k$, with the
scalars $\mu_k$ and $\tau_k$ of the BiCG run. The statement gives degree at most $k$ and has no
hypothesis on breakdown. -/
theorem equation_11_4_14 (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (k : ℕ) :
    WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).r =
        aeval (toEuclideanLin A) (BCG.residualPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
          (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k)
          (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)) ∧
      WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).p =
        aeval (toEuclideanLin A) (BCG.directionPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
          (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k)
          (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)) ∧
      WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).rt =
        aeval (toEuclideanLin Aᵀ) (BCG.residualPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
          (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k) (WithLp.toLp 2 rt₀) ∧
      WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).pt =
        aeval (toEuclideanLin Aᵀ) (BCG.directionPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
          (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k) (WithLp.toLp 2 rt₀) ∧
      (BCG.residualPoly (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
        (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k).eval 0 = 1 ∧
      (BCG.residualPoly (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
        (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k).natDegree ≤ k ∧
      (BCG.directionPoly (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
        (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k).natDegree ≤ k := by
  obtain ⟨h1, h2, h3, h4⟩ := BCG.residual_eq_aeval (toEuclideanLin A) (toEuclideanLin Aᵀ)
    (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k
  rw [map_starRingEnd_real] at h3 h4
  have hs := (bicg_spec A b x₀ rt₀).1 k
  refine ⟨?_, ?_, ?_, ?_, BCG.residualPoly_eval_zero _ _ _ _ _ k,
    BCG.residualPoly_natDegree_le _ _ _ _ _ k, BCG.directionPoly_natDegree_le _ _ _ _ _ k⟩
  · rw [← h1, BCG.residual, ← hs]; rfl
  · rw [← h2, BCG.direction, ← hs]; rfl
  · rw [← h3, BCG.dualResidual, ← hs]; rfl
  · rw [← h4, BCG.dualDirection, ← hs]; rfl

/-- **Section 11.4.5** of [golub2013matrix], the transpose-free scalars. Let
$A \in \mathbb{R}^{n \times n}$ and $b, x_0, \tilde r_0 \in \mathbb{R}^n$, let $r_0 = b - Ax_0$,
and let $\psi_k$, $\phi_k$ and the vectors after $k$ exact passes of
`GolubVanLoan.Chapter11.bicg` be as in (11.4.14). Then $$\tilde r_k^Tr_k = \tilde
r_0^T(\psi_k(A)^2r_0), \qquad \tilde p_k^TAp_k = \tilde r_0^T(A\phi_k(A)^2r_0).$$

The source says that this enables "us to characterize expressions like $\tilde r_k^Tr_k$ and
$\tilde p_k^TAp_k$ in a way that involves only $A$-times-vector". The proof moves the polynomial
in $A^T$ across the inner product (`BiLanczos.inner_aeval_map_eq`). -/
theorem bicg_inner_eq_poly (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (k : ℕ) :
    inner ℝ (WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).rt : EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).r) =
      inner ℝ (WithLp.toLp 2 rt₀ : EuclideanSpace ℝ (Fin n))
        (aeval (toEuclideanLin A) (BCG.residualPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
          (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k ^ 2)
          (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀))) ∧
    inner ℝ (WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).pt : EuclideanSpace ℝ (Fin n))
        (toEuclideanLin A (WithLp.toLp 2 (Id.run (bicg pure A b x₀ rt₀ k)).p)) =
      inner ℝ (WithLp.toLp 2 rt₀ : EuclideanSpace ℝ (Fin n))
        (toEuclideanLin A (aeval (toEuclideanLin A)
          (BCG.directionPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
            (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k ^ 2)
          (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)))) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := equation_11_4_14 A b x₀ rt₀ k
  have hB : LinearMap.IsAdjointPair (innerₛₗ ℝ).flip (innerₛₗ ℝ).flip (toEuclideanLin A)
      (toEuclideanLin Aᵀ) :=
    LinearMap.isAdjointPair_inner_iff'.2 (inner_toEuclideanLin_transpose A)
  set T := toEuclideanLin A
  set ψ := BCG.residualPoly T (toEuclideanLin Aᵀ) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
    (WithLp.toLp 2 rt₀) k
  set φ := BCG.directionPoly T (toEuclideanLin Aᵀ) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
    (WithLp.toLp 2 rt₀) k
  set r₀ := WithLp.toLp 2 b - T (WithLp.toLp 2 x₀)
  have hsq : ∀ (q : ℝ[X]) (v : EuclideanSpace ℝ (Fin n)), aeval T (q ^ 2) v =
      aeval T q (aeval T q v) := fun q v => by
    rw [sq, map_mul]; rfl
  refine ⟨?_, ?_⟩
  · have key := BiLanczos.inner_aeval_map_eq hB ψ (WithLp.toLp 2 rt₀) (aeval T ψ r₀)
    rw [map_starRingEnd_real] at key
    rw [h3, h1, key, hsq]
  · have key := BiLanczos.inner_aeval_map_eq hB φ (WithLp.toLp 2 rt₀) (T (aeval T φ r₀))
    rw [map_starRingEnd_real] at key
    rw [h4, h2, key, hsq, Module.End.aeval_apply_apply]

/-- **Section 11.4.5** of [golub2013matrix], CGS (Sonneveld). Let $A \in \mathbb{R}^{n \times n}$
and $b, x_0, \tilde r_0 \in \mathbb{R}^n$, let $r_0 = b - Ax_0$, and let $\psi_k$ and $\phi_k$
be the BiCG polynomials of (11.4.14) for these data. After $k$ exact passes of
`GolubVanLoan.Chapter11.cgs`, the state is the state `CGS.iterate` of the CGS iteration of the
backbone, and $$r_k = \psi_k(A)^2r_0, \qquad p_k = \phi_k(A)^2r_0.$$

The source says that CGS "produces iterates $x_k$ whose residuals $r_k$ satisfy
$r_k = \psi_k(A)^2r_0$", with products by $A$ only. The iteration `CGS.iterate` is Algorithm 7.6
of [saad2003iterative], line by line the same as the figure. The polynomial identities are
`CGS.residual_eq_aeval_sq`; they need no hypothesis on breakdown. -/
theorem cgs_residual_eq (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (k : ℕ) :
    (Id.run (cgs pure A b x₀ rt₀ k)).toState =
        CGS.iterate (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k ∧
      WithLp.toLp 2 (Id.run (cgs pure A b x₀ rt₀ k)).r =
        aeval (toEuclideanLin A) (BCG.residualPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
          (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k ^ 2)
          (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)) ∧
      WithLp.toLp 2 (Id.run (cgs pure A b x₀ rt₀ k)).p =
        aeval (toEuclideanLin A) (BCG.directionPoly (toEuclideanLin A) (toEuclideanLin Aᵀ)
          (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k ^ 2)
          (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀)) := by
  have hs : (Id.run (cgs pure A b x₀ rt₀ k)).toState =
      CGS.iterate (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
        (WithLp.toLp 2 rt₀) k := by
    have h := foldlM_range_transport (cgsStep pure A rt₀)
      (CGS.step (toEuclideanLin A) (WithLp.toLp 2 rt₀)) CGSState.toState (cgsStep_exact A rt₀) k
    simp only [cgs, Id.run_bind, residual_init_exact, h]
    simp only [CGS.iterate, CGSState.toState, WithLp.toLp_sub, toEuclideanLin_toLp]
  obtain ⟨h1, h2, -⟩ := CGS.residual_eq_aeval_sq
    (LinearMap.isAdjointPair_inner_iff'.2 (inner_toEuclideanLin_transpose A)) k
    (b := WithLp.toLp 2 b) (x₀ := WithLp.toLp 2 x₀) (rs₀ := WithLp.toLp 2 rt₀)
  exact ⟨hs, by rw [← h1, ← hs]; rfl, by rw [← h2, ← hs]; rfl⟩

/-- **Section 11.4.5** of [golub2013matrix], BiCGstab (van der Vorst). Let
$A \in \mathbb{R}^{n \times n}$ and $b, x_0, \tilde r_0 \in \mathbb{R}^n$, let $r_0 = b - Ax_0$,
and let $\psi_k$ be the BiCG residual polynomial of (11.4.14) for these data. Let
$s_j = r_j - \mu_jAp_j$ and $\omega_j = (As_j)^Ts_j/(As_j)^T(As_j)$ be the intermediate vectors
and the scalars of the BiCGstab iteration. After $k$ exact passes of
`GolubVanLoan.Chapter11.bicgstab`:

* the state is the state `BiCGSTAB.iterate` of the BiCGstab iteration of the backbone;
* if BiCG does not break down through step $k$ and $\omega_j \neq 0$ for $j < k$, then $$r_k =
  (1 - \omega_{k-1}A) \cdots (1 - \omega_0A)\psi_k(A)r_0;$$
* $\omega_k$ minimizes $\|s_k - \omega As_k\|_2$ over $\omega \in \mathbb{R}$.

The source says that BiCGstab "produces iterates $x_k$ whose residuals satisfy $r_k = (1 -
\omega_kA) \cdots (1 - \omega_1A)\psi_k(A)r_0$ where $\psi_k$ is the BiCG residual polynomial
defined in (11.4.14). The parameter $\omega_k$ is chosen in step $k$ to minimize $\|r_k\|_2$
given $\omega_1, \dots, \omega_{k-1}$ and the vector $\psi_k(A)r_0$." The indices of $\omega$
are 0-based here. The iteration `BiCGSTAB.iterate` is Algorithm 7.7 of [saad2003iterative]. The
residual identity is `BiCGSTAB.residual_eq`, and the product of the factors $1 - \omega_jA$ is
`BiCGSTAB.stabPoly`. The minimization is Problem P11.4.2 of the source, the one-dimensional
minimal-residual step `Projection.minResStep`. -/
theorem bicgstab_residual_eq (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ rt₀ : Fin n → ℝ) (k : ℕ) :
    (Id.run (bicgstab pure A b x₀ rt₀ k)).toState =
        BiCGSTAB.iterate (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
          (WithLp.toLp 2 rt₀) k ∧
      (BCG.NoBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
          (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k →
        (∀ i < k, BiCGSTAB.omega (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
          (WithLp.toLp 2 rt₀) i ≠ 0) →
        WithLp.toLp 2 (Id.run (bicgstab pure A b x₀ rt₀ k)).r =
          aeval (toEuclideanLin A) (BiCGSTAB.stabPoly (toEuclideanLin A) (WithLp.toLp 2 b)
            (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k *
              BCG.residualPoly (toEuclideanLin A) (toEuclideanLin Aᵀ) (WithLp.toLp 2 b)
                (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k)
            (WithLp.toLp 2 b - toEuclideanLin A (WithLp.toLp 2 x₀))) ∧
      ∀ ω : ℝ,
        ‖BiCGSTAB.s (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k -
            BiCGSTAB.omega (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
              (WithLp.toLp 2 rt₀) k •
              toEuclideanLin A (BiCGSTAB.s (toEuclideanLin A) (WithLp.toLp 2 b)
                (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k)‖ ≤
          ‖BiCGSTAB.s (toEuclideanLin A) (WithLp.toLp 2 b) (WithLp.toLp 2 x₀)
              (WithLp.toLp 2 rt₀) k -
            ω • toEuclideanLin A (BiCGSTAB.s (toEuclideanLin A) (WithLp.toLp 2 b)
              (WithLp.toLp 2 x₀) (WithLp.toLp 2 rt₀) k)‖ := by
  set T := toEuclideanLin A
  set b' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 b
  set x₀' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x₀
  set rt₀' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 rt₀
  have hs : (Id.run (bicgstab pure A b x₀ rt₀ k)).toState = BiCGSTAB.iterate T b' x₀' rt₀' k := by
    have h := foldlM_range_transport (bicgstabStep pure A rt₀) (BiCGSTAB.step T rt₀')
      BiCGstabState.toState (bicgstabStep_exact A rt₀) k
    simp only [bicgstab, Id.run_bind, residual_init_exact, h]
    simp only [BiCGSTAB.iterate, BiCGstabState.toState, WithLp.toLp_sub, toEuclideanLin_toLp,
      b', x₀', T]
  refine ⟨hs, fun hbd hω => ?_, fun ω => ?_⟩
  · have h := (BiCGSTAB.residual_eq (B := toEuclideanLin Aᵀ) hbd hω le_rfl).1
    rw [← h, ← hs]
    rfl
  · set z := (BiCGSTAB.iterate T b' x₀' rt₀' k).x +
      BiCGSTAB.alpha T b' x₀' rt₀' k • (BiCGSTAB.iterate T b' x₀' rt₀' k).p
    set s := BiCGSTAB.s T b' x₀' rt₀' k
    have hz : b' - T z = s := by
      simp only [z, s, BiCGSTAB.s, BiCGSTAB.r_eq_sub_apply_x, map_add, map_smul]
      abel
    have hmin := Projection.minResStep_isMinResidual (A := T) (b := b') z
    have h1 := hmin.min (z + ω • s) (by
      rw [add_sub_cancel_left, hz]
      exact Submodule.smul_mem _ ω (Submodule.mem_span_singleton_self s))
    rw [← BiCGSTAB.iterate_succ_x_eq_minResStep, ← BiCGSTAB.r_eq_sub_apply_x,
      BiCGSTAB.iterate_succ_r, map_add, map_smul,
      show b' - (T z + ω • T s) = (b' - T z) - ω • T s by abel, hz] at h1
    exact h1

/-- **Section 11.4.5** of [golub2013matrix], QMR. Let $A \in \mathbb{R}^{n \times n}$, let
$b, x_0, q_1, \tilde q_1 \in \mathbb{R}^n$ with $b - Ax_0 = \beta_0q_1$, and suppose that the
two-sided Lanczos process of $A$ and $A^T$ from $(q_1, \tilde q_1)$ has no serious breakdown.
With the notation of `GolubVanLoan.Chapter11.equation_11_4_12`, let $Q_k$ have the columns
$v_0, \dots, v_{k-1}$, and let $\tilde T_k \in \mathbb{R}^{(k+1) \times k}$ be the leading block
of the coefficient array $T$. Then:

* for every $y \in \mathbb{R}^k$, $b - A(x_0 + Q_ky) = Q_{k+1}(\beta_0e_1 - \tilde T_ky)$;
* $x$ is the $k$-th QMR iterate if and only if $x = x_0 + Q_ky$ for some $y$ that minimizes
  $\|\beta_0e_1 - \tilde T_ky\|_2$ over $\mathbb{R}^k$.

The source says: "As in BiCG, the $k$th iterate has the form $x_k = x_0 + Q_ky_k$ … This
equation can be rewritten as $AQ_k = Q_{k+1}\tilde T_k$ where
$\tilde T_k \in \mathbb{R}^{(k+1) \times k}$ is tridiagonal. It follows that if
$q_1 = r_0/\beta_0$ … then $b - A(x_0 + Q_ky) = Q_{k+1}(\beta_0e_1 - \tilde T_ky)$. In QMR, $y$
is chosen to minimize $\|\beta_0e_1 - \tilde T_ky\|_2$."

"No serious breakdown" is `BiLanczos.NoSeriousBreakdown`: whenever $\delta_{j+1} = 0$, the
primal recurrence has already terminated. The residual identity is
`Krylov.HessenbergRelation₂.residual_eq` for `BiLanczos.hessenbergRelation`. The QMR iterate is
`QMR.IsQuasiMinResidual`, which is the minimization of the source by definition. -/
theorem qmr_residual_eq (A : Matrix (Fin n) (Fin n) ℝ) {b x₀ q₁ qt₁ : EuclideanSpace ℝ (Fin n)}
    {β₀ : ℝ} (h : BiLanczos.NoSeriousBreakdown (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁)
    (hr : b - toEuclideanLin A x₀ = β₀ • q₁) (k : ℕ) :
    (∀ y : Fin k → ℝ, b - toEuclideanLin A
        (x₀ + ∑ j, y j • BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j) =
      ∑ i : Fin (k + 1), (firstVec β₀ (k + 1) -
        hessenbergOf (BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁) k *ᵥ y) i •
          BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ i) ∧
    ∀ x, QMR.IsQuasiMinResidual (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ β₀ x₀ k x ↔
      ∃ y : Fin k → ℝ,
        x = x₀ + ∑ j, y j • BiLanczos.vec (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁ j ∧
        IsMinOn (fun z : Fin k → ℝ => ‖(WithLp.toLp 2 (firstVec β₀ (k + 1) -
          hessenbergOf (BiLanczos.coeff (toEuclideanLin A) (toEuclideanLin Aᵀ) q₁ qt₁) k *ᵥ z) :
            EuclideanSpace ℝ (Fin (k + 1)))‖) Set.univ y :=
  ⟨fun y => (BiLanczos.hessenbergRelation h).residual_eq hr k y, fun _ => Iff.rfl⟩

/-- **Section 11.4.5** of [golub2013matrix], QMR and GMRES. Let $A \in \mathbb{R}^{n \times n}$, let
$b, x_0 \in \mathbb{R}^n$, $r_0 = b - Ax_0$ and $\beta_0 = \|r_0\|_2$, and let $k$ be at most
the grade of $r_0$ with respect to $A$. Take the Arnoldi basis $q_1, q_2, \dots$ and the
Hessenberg matrix $\tilde H_k$ of (11.4.8). Then $x$ is the quasi-minimal-residual iterate,
$x = x_0 + Q_ky$ with $y$ minimizing $\|\beta_0e_1 - \tilde H_ky\|_2$, if and only if $x$ is the
GMRES iterate, the minimizer of $\|b - Ax\|_2$ over $x_0 + \mathcal{K}(A, r_0, k)$.

The source says: "GMRES minimizes the same quantity because $Q_{k+1}$ has orthonormal columns in
Arnoldi." The quasi-minimal-residual iterate is `Krylov.IsQuasiMinResidualIterate` for the
Arnoldi vectors and coefficients. -/
theorem qmr_eq_gmres_of_orthonormal (A : Matrix (Fin n) (Fin n) ℝ)
    (b x₀ : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : k ≤ grade (toEuclideanLin A) (b - toEuclideanLin A x₀)) (x : EuclideanSpace ℝ (Fin n)) :
    IsQuasiMinResidualIterate (Arnoldi.vec (toEuclideanLin A) (b - toEuclideanLin A x₀))
        (Arnoldi.coeff (toEuclideanLin A) (b - toEuclideanLin A x₀)) ‖b - toEuclideanLin A x₀‖
        x₀ k x ↔
      IsMinResidualIterate (toEuclideanLin A) b x₀ k x :=
  isQuasiMinResidualIterate_iff_isMinResidualIterate hk x

end GolubVanLoan.Chapter11
