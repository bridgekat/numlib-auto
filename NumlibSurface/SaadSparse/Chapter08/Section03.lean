/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.NormalEquations
import NumlibSurface.SaadSparse.Chapter06.Section02
import NumlibSurface.SaadSparse.Chapter07.Section01
import NumlibSurface.SaadSparse.Chapter08.Section01

/-!
# Saad, Section 8.3: Conjugate gradient and the normal equations

This module formalizes Section 8.3 of [saad2003iterative]. Both algorithms of the section are the
conjugate gradient method applied to a system of normal equations, rearranged so that only products
with $A$ and $A^H$ occur and neither $A^H A$ nor $A A^H$ is formed. Algorithm 8.4 (CGNR) computes
the conjugate gradient iterates of $A^H A x = A^H b$. Algorithm 8.5 (CGNE, Craig's method) computes
the conjugate gradient iterates of $A A^H u = b$, read through $x = A^H u$. The identification with
the conjugate gradient method specializes `Numlib.Krylov.NormalEquations`.

Both methods take their iterates from the same affine subspace
$x_0 + \mathcal{K}_m(A^H A, A^H r_0)$, because $A^H \mathcal{K}_m(A A^H, r_0) = \mathcal{K}_m(A^H A,
A^H r_0)$. Over it, CGNR minimizes the residual norm $\|b - Ax\|_2$ and CGNE minimizes the error
norm $\|x_* - x\|_2$. The conjugate gradient bound transported to CGNR contains the condition number
$\kappa_2(A) = \sigma_{\max}/\sigma_{\min}$ of $A$, not its square root; this is the price of the
normal equations that the book points out at (8.8).

## Main definitions

* Algorithm 8.4, `SaadSparse.Chapter08.cgnr`: the CGNR iteration.
* Algorithm 8.5, `SaadSparse.Chapter08.cgne`: the CGNE iteration (Craig's method).

## Main results

* Algorithm 8.4, `SaadSparse.Chapter08.cgnr_eq`: the CGNR iterates are the conjugate gradient
  iterates of $A^H A x = A^H b$.
* Algorithm 8.5, `SaadSparse.Chapter08.cgne_eq`: the CGNE iterates are the conjugate gradient
  iterates of $A A^H u = b$, read through $x = A^H u$.
* Section 8.3.1, `SaadSparse.Chapter08.cgnr_isMinResidual`: for nonsingular $A$, the CGNR iterate
  $x_m$ minimizes $\|b - Ax\|_2$ over $x_0 + \mathcal{K}_m(A^H A, A^H r_0)$.
* Section 8.3.2, `SaadSparse.Chapter08.cgne_isMinError`: for nonsingular $A$, the CGNE iterate $x_m$
  minimizes $\|x_* - x\|_2$ over the same affine subspace.
* Section 8.3, `SaadSparse.Chapter08.subspace_adjoint_eq`: $A^H \mathcal{K}_m(A A^H, r_0) =
  \mathcal{K}_m(A^H A, A^H r_0)$.
* Section 8.3, `SaadSparse.Chapter08.cgnr_norm_residual_le`: the residual of CGNR decreases at least
  like $2((\kappa - 1)/(\kappa + 1))^m$ with $\kappa = \sigma_{\max}/\sigma_{\min}$.

## Conventions

* The scalar field $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$ (`[RCLike 𝕜]`). The matrix $A$ is
  square, $A \in \mathbb{K}^{n \times n}$, as the coefficient matrix of the system $Ax = b$ of the
  chapter; the rectangular least-squares setting is Section 8.1.
* The operator $x \mapsto Ax$ is `SaadSparse.Chapter06.op A`, and $\mathcal{K}_m(A, v)$ is
  `SaadSparse.Chapter06.krylov A v m`.
* Mathlib's `inner 𝕜 u v` is the inner product $(v, u)$ of the book.

## Implementation notes

* A state of either iteration is a triple $(x_i, r_i, p_i)$: the iterate, the residual $b - Ax_i$
  and the search direction (`Krylov.CGNR.State` and `Krylov.CGNE.State`). In CGNR the vectors
  $z_i = A^H r_i$ and $w_i = A p_i$ are recomputed in each step rather than stored.
* Division by zero is $0$ in Lean. A step length with a vanishing denominator is therefore $0$, and
  the iteration stays where it is.

## Deviations from the source

* **Generalization.** The two normal operators are Hermitian coercive for the corresponding
  injective maps. See `SaadSparse.Chapter08.isSymmetricCoercive_normal`,
  `SaadSparse.Chapter08.isSymmetricCoercive_normal'`.
* **Totalization.** The CGNR and CGNE step coefficients are totalized squared-norm quotients. See
  `SaadSparse.Chapter08.cgnrStepAlpha`, `SaadSparse.Chapter08.cgnrStepBeta`,
  `SaadSparse.Chapter08.cgneStepAlpha`, `SaadSparse.Chapter08.cgneStepBeta`.
* **Generalization.** The CGNR and CGNE states are defined at every index, use the adjoint, and omit
  an explicit convergence test. See `SaadSparse.Chapter08.cgnrStepR`,
  `SaadSparse.Chapter08.cgnrStep`, `SaadSparse.Chapter08.cgnr`, `SaadSparse.Chapter08.cgnr_succ`,
  `SaadSparse.Chapter08.cgnr_zero_p`, `SaadSparse.Chapter08.cgneStepR`,
  `SaadSparse.Chapter08.cgneStep`, `SaadSparse.Chapter08.cgne`, `SaadSparse.Chapter08.cgne_succ`,
  `SaadSparse.Chapter08.cgne_zero_p`.
* **Generalization.** The normal-equation CG identities include singular inputs and use a compatible
  start for CGNE. See `SaadSparse.Chapter08.cgnr_eq`, `SaadSparse.Chapter08.cgne_eq`.
* **Generalization.** The two normal-equation optimality properties and shared Krylov space extend
  to complex scalars. See `SaadSparse.Chapter08.cgnr_isMinResidual`,
  `SaadSparse.Chapter08.cgne_isMinError`, `SaadSparse.Chapter08.subspace_adjoint_eq`.
* **Derivation.** An explicit CGNR residual bound is derived from the normal-equation identity and
  the earlier CG bound. See `SaadSparse.Chapter08.cgnr_norm_residual_le`.

## Not formalized

* **Example 8.1** (Table 8.1). It reports the iteration and operation counts of a floating-point run
  of CGNR on test problems of Section 3.7, and carries no mathematical claim.
-/

open Matrix

open scoped Matrix SaadSparse

namespace SaadSparse.Chapter08

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Preliminaries -/

/-- For $A \in \mathbb{K}^{n \times n}$ and $u, v \in \mathbb{K}^n$, $(v, A^H u) = (Av, u)$: the
conjugate transpose $A^H$ acts as the adjoint of $A$. This is the form of the hypothesis that
the backbone normal-equations layer takes. -/
theorem inner_op_conjTranspose (A : Matrix (Fin n) (Fin n) 𝕜) (u v : 𝔼) :
    inner 𝕜 (op Aᴴ u) v = inner 𝕜 u (op A v) :=
  inner_conjTranspose A u v

/-- The operators $A$ and $A^H$ form an adjoint pair for the inner product, in the form of
`LinearMap.IsAdjointPair`. -/
private theorem isAdjointPair_op (A : Matrix (Fin n) (Fin n) 𝕜) :
    LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip (op A) (op Aᴴ) :=
  LinearMap.isAdjointPair_inner_iff.2 (inner_op_conjTranspose A)

/-- The operator of a matrix product $BC$ is the composite of the operators of $B$ and $C$. -/
private theorem op_mul (B C : Matrix (Fin n) (Fin n) 𝕜) : op (B * C) = op B ∘ₗ op C :=
  Matrix.toEuclideanLin_mul B C

/-- For $B, C \in \mathbb{K}^{n \times n}$, the Krylov subspace $\mathcal{K}_m(BC, v)$ is the
backbone Krylov subspace `Krylov.subspace` of the composite operator $x \mapsto B(Cx)$. -/
theorem krylov_conjTranspose_mul (B C : Matrix (Fin n) (Fin n) 𝕜) (v : 𝔼) (m : ℕ) :
    Chapter06.krylov (B * C) v m = Krylov.subspace (op B ∘ₗ op C) v m := by
  rw [Chapter06.krylov_eq, op_mul]

/-- If $A \in \mathbb{K}^{n \times n}$ is nonsingular, then $A^H A$ is symmetric and coercive
(`LinearMap.IsSymmetricCoercive`), that is, symmetric positive definite. This is the hypothesis
under which CGNR is well defined.

**Generalization.** The real SPD statements extend to Hermitian coercivity over complex scalars with
the adjoint in place of the transpose.
-/
theorem isSymmetricCoercive_normal {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : Function.Injective (op A)) : (op Aᴴ ∘ₗ op A).IsSymmetricCoercive :=
  Krylov.adjoint_comp_isSymmetricCoercive_of_injective (isAdjointPair_op A) hA

/-- If $A^H$ is nonsingular, then $A A^H$ is symmetric and coercive
(`LinearMap.IsSymmetricCoercive`), that is, symmetric positive definite. This is the hypothesis
under which CGNE is well defined.

**Generalization.** The real SPD statements extend to Hermitian coercivity over complex scalars with
the adjoint in place of the transpose.
-/
theorem isSymmetricCoercive_normal' {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : Function.Injective (op Aᴴ)) : (op A ∘ₗ op Aᴴ).IsSymmetricCoercive :=
  Krylov.adjoint_comp_isSymmetricCoercive_of_injective
    (LinearMap.isAdjointPair_inner_iff.2 (Chapter07.inner_op_conjTranspose A)) hA

/-! ### Algorithm 8.4: CGNR -/

section CGNR

variable (A : Matrix (Fin n) (Fin n) 𝕜)

/-- The step length of line 4 of Algorithm 8.4 of [saad2003iterative], computed from a state
$(x_i, r_i, p_i)$: $\alpha_i = \|z_i\|_2^2 / \|w_i\|_2^2$ with $z_i = A^H r_i$ and
$w_i = A p_i$. It is $0$ when $w_i = 0$.

**Reading.** The coefficients are quotients of squared Euclidean norms, including over complex
scalars, with zero result for a zero denominator.
-/
noncomputable def cgnrStepAlpha (s : Krylov.CGNR.State 𝔼 𝔼) : 𝕜 :=
  (‖op Aᴴ s.r‖ : 𝕜) ^ 2 / (‖op A s.p‖ : 𝕜) ^ 2

/-- The new residual of line 6 of Algorithm 8.4 of [saad2003iterative]:
$r_{i+1} = r_i - \alpha_i w_i$ with $w_i = A p_i$.

**Generalization.** The state recurrence is defined for complex scalars with the adjoint replacing
the transpose. It extends through zero denominators and has no convergence test. The CGNR state
stores $(x,r,p)$ and computes the auxiliary $z$ and $w$ from these fields.
-/
noncomputable def cgnrStepR (s : Krylov.CGNR.State 𝔼 𝔼) : 𝔼 :=
  s.r - cgnrStepAlpha A s • op A s.p

/-- The coefficient of line 8 of Algorithm 8.4 of [saad2003iterative]:
$\beta_i = \|z_{i+1}\|_2^2 / \|z_i\|_2^2$ with $z_j = A^H r_j$. It is $0$ when $z_i = 0$.

**Reading.** The coefficients are quotients of squared Euclidean norms, including over complex
scalars, with zero result for a zero denominator.
-/
noncomputable def cgnrStepBeta (s : Krylov.CGNR.State 𝔼 𝔼) : 𝕜 :=
  (‖op Aᴴ (cgnrStepR A s)‖ : 𝕜) ^ 2 / (‖op Aᴴ s.r‖ : 𝕜) ^ 2

/-- One pass through lines 3–9 of Algorithm 8.4 of [saad2003iterative], on the state
$(x_i, r_i, p_i)$: $x_{i+1} = x_i + \alpha_i p_i$, $r_{i+1} = r_i - \alpha_i A p_i$ and
$p_{i+1} = A^H r_{i+1} + \beta_i p_i$. The normal-equations residual $z_i = A^H r_i$ and the
product $w_i = A p_i$ are recomputed rather than stored.

**Generalization.** The state recurrence is defined for complex scalars with the adjoint replacing
the transpose. It extends through zero denominators and has no convergence test. The CGNR state
stores $(x,r,p)$ and computes the auxiliary $z$ and $w$ from these fields.
-/
noncomputable def cgnrStep (s : Krylov.CGNR.State 𝔼 𝔼) : Krylov.CGNR.State 𝔼 𝔼 :=
  { x := s.x + cgnrStepAlpha A s • s.p
    r := cgnrStepR A s
    p := op Aᴴ (cgnrStepR A s) + cgnrStepBeta A s • s.p }

/-- **Algorithm 8.4** of [saad2003iterative] (CGNR). Let $A \in \mathbb{K}^{n \times n}$ and
$b, x_0 \in \mathbb{K}^n$. The state after $i$ steps is obtained from $r_0 = b - Ax_0$ and
$p_0 = z_0 = A^H r_0$ by $i$ passes of the recurrence
$$w_j = A p_j, \quad \alpha_j = \frac{\|z_j\|_2^2}{\|w_j\|_2^2}, \quad x_{j+1} = x_j + \alpha_j
  p_j, \quad r_{j+1} = r_j - \alpha_j w_j,$$
$$z_{j+1} = A^H r_{j+1}, \quad \beta_j = \frac{\|z_{j+1}\|_2^2}{\|z_j\|_2^2}, \quad p_{j+1} =
  z_{j+1} + \beta_j p_j.$$

The state is the triple $(x_i, r_i, p_i)$ of type `Krylov.CGNR.State`, and a pass is
`SaadSparse.Chapter08.cgnrStep`. A quotient with a vanishing denominator is $0$.

**Generalization.** The state recurrence is defined for complex scalars with the adjoint replacing
the transpose. It extends through zero denominators and has no convergence test. The CGNR state
stores $(x,r,p)$ and computes the auxiliary $z$ and $w$ from these fields.
-/
noncomputable def cgnr (b x₀ : 𝔼) (i : ℕ) : Krylov.CGNR.State 𝔼 𝔼 :=
  (cgnrStep A)^[i] { x := x₀, r := b - op A x₀, p := op Aᴴ (b - op A x₀) }

variable (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- The state of Algorithm 8.4 after $i + 1$ steps is one pass of the algorithm applied to the state
after $i$ steps.

**Generalization.** The state recurrence is defined for complex scalars with the adjoint replacing
the transpose. It extends through zero denominators and has no convergence test. The CGNR state
stores $(x,r,p)$ and computes the auxiliary $z$ and $w$ from these fields.
-/
theorem cgnr_succ (i : ℕ) : cgnr A b x₀ (i + 1) = cgnrStep A (cgnr A b x₀ i) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterate of Algorithm 8.4 after $0$ steps is $x_0$. -/
@[simp] theorem cgnr_zero_x : (cgnr A b x₀ 0).x = x₀ := rfl

/-- The residual of Algorithm 8.4 after $0$ steps is $r_0 = b - Ax_0$. -/
@[simp] theorem cgnr_zero_r : (cgnr A b x₀ 0).r = b - op A x₀ := rfl

/-- The search direction of Algorithm 8.4 after $0$ steps is $p_0 = z_0 = A^H r_0$.

**Generalization.** The state recurrence is defined for complex scalars with the adjoint replacing
the transpose. It extends through zero denominators and has no convergence test. The CGNR state
stores $(x,r,p)$ and computes the auxiliary $z$ and $w$ from these fields.
-/
@[simp] theorem cgnr_zero_p : (cgnr A b x₀ 0).p = op Aᴴ (b - op A x₀) := rfl

/-! ### The bridge to the backbone CGNR recurrence -/

variable {A}

private theorem cgnrStepAlpha_eq (s : Krylov.CGNR.State 𝔼 𝔼) :
    cgnrStepAlpha A s = Krylov.CGNR.alpha (op A) (op Aᴴ) s := by
  rw [cgnrStepAlpha, Krylov.CGNR.alpha, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]

private theorem cgnrStepR_eq (s : Krylov.CGNR.State 𝔼 𝔼) :
    cgnrStepR A s = (Krylov.CGNR.step (op A) (op Aᴴ) s).r := by
  rw [cgnrStepR, cgnrStepAlpha_eq, Krylov.CGNR.step_r]

private theorem cgnrStepBeta_eq (s : Krylov.CGNR.State 𝔼 𝔼) :
    cgnrStepBeta A s = Krylov.CGNR.beta (op A) (op Aᴴ) s := by
  rw [cgnrStepBeta, Krylov.CGNR.beta, cgnrStepR_eq, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]

private theorem cgnrStep_eq (s : Krylov.CGNR.State 𝔼 𝔼) :
    cgnrStep A s = Krylov.CGNR.step (op A) (op Aᴴ) s := by
  have h : cgnrStep A s =
      { x := s.x + cgnrStepAlpha A s • s.p
        r := cgnrStepR A s
        p := op Aᴴ (cgnrStepR A s) + cgnrStepBeta A s • s.p } := rfl
  rw [h, cgnrStepAlpha_eq, cgnrStepR_eq, cgnrStepBeta_eq]
  rfl

/-- For all $i$, the state of Algorithm 8.4 after $i$ steps is the state `Krylov.CGNR.iterate` of
the backbone CGNR recurrence for the operator pair $(A, A^H)$. -/
theorem cgnr_eq_iterate (i : ℕ) :
    cgnr A b x₀ i = Krylov.CGNR.iterate (op A) (op Aᴴ) b x₀ i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [cgnr_succ, ih, cgnrStep_eq, Krylov.CGNR.iterate_succ]

/-- **Algorithm 8.4** of [saad2003iterative], identification with the conjugate gradient method. Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0 \in \mathbb{K}^n$. For every $i$, the iterate $x_i$
of CGNR is the $i$-th iterate of the conjugate gradient method applied to the normal equations
$A^H A x = A^H b$ from $x_0$.

So CGNR computes the conjugate gradient iterates of the normal equations without forming
$A^H A$. Everything the backbone proves of `CG.iterate`, such as the orthogonality relations,
finite termination and the Chebyshev bounds, therefore holds for CGNR. The proof goes through
`SaadSparse.Chapter08.cgnr_eq_iterate` and the backbone module `Numlib.Krylov.NormalEquations`.

**Generalization.** The correspondence with CG is stated at every index for the totalized
recurrences, without a nonsingularity requirement. CGNE uses the explicit compatible start
$x_0=A^Hu_0$.
-/
theorem cgnr_eq (i : ℕ) :
    (cgnr A b x₀ i).x = (CG.iterate (op Aᴴ ∘ₗ op A) (op Aᴴ b) x₀ i).x := by
  rw [cgnr_eq_iterate]
  exact Krylov.CGNR.iterate_x_eq (op A) (op Aᴴ) b x₀ (isAdjointPair_op A) i

/-- For all $i$, the residual $r_i$ of Algorithm 8.4 is the true residual $b - Ax_i$ of the iterate
$x_i$. -/
theorem cgnr_residual_eq (i : ℕ) : (cgnr A b x₀ i).r = b - op A (cgnr A b x₀ i).x := by
  rw [cgnr_eq_iterate]
  exact Krylov.CGNR.residual_eq (op A) (op Aᴴ) b x₀ (isAdjointPair_op A) i

end CGNR

/-! ### Algorithm 8.5: CGNE (Craig's method) -/

section CGNE

variable (A : Matrix (Fin n) (Fin n) 𝕜)

/-- The step length of line 3 of Algorithm 8.5 of [saad2003iterative], computed from a state
$(x_i, r_i, p_i)$: $\alpha_i = (r_i, r_i)/(p_i, p_i)$. It is $0$ when $p_i = 0$.

**Reading.** The coefficients are quotients of squared Euclidean norms, including over complex
scalars, with zero result for a zero denominator.
-/
noncomputable def cgneStepAlpha (s : Krylov.CGNE.State 𝔼 𝔼) : 𝕜 :=
  (‖s.r‖ : 𝕜) ^ 2 / (‖s.p‖ : 𝕜) ^ 2

/-- The new residual of line 5 of Algorithm 8.5 of [saad2003iterative]:
$r_{i+1} = r_i - \alpha_i A p_i$.

**Generalization.** The state recurrence is defined for complex scalars with the adjoint replacing
the transpose. It extends through zero denominators and has no convergence test. The CGNR state
stores $(x,r,p)$ and computes the auxiliary $z$ and $w$ from these fields.
-/
noncomputable def cgneStepR (s : Krylov.CGNE.State 𝔼 𝔼) : 𝔼 :=
  s.r - cgneStepAlpha s • op A s.p

/-- The coefficient of line 6 of Algorithm 8.5 of [saad2003iterative]:
$\beta_i = (r_{i+1}, r_{i+1})/(r_i, r_i)$. It is $0$ when $r_i = 0$.

**Reading.** The coefficients are quotients of squared Euclidean norms, including over complex
scalars, with zero result for a zero denominator.
-/
noncomputable def cgneStepBeta (s : Krylov.CGNE.State 𝔼 𝔼) : 𝕜 :=
  (‖cgneStepR A s‖ : 𝕜) ^ 2 / (‖s.r‖ : 𝕜) ^ 2

/-- One pass through lines 3–7 of Algorithm 8.5 of [saad2003iterative], on the state
$(x_i, r_i, p_i)$: $x_{i+1} = x_i + \alpha_i p_i$, $r_{i+1} = r_i - \alpha_i A p_i$ and
$p_{i+1} = A^H r_{i+1} + \beta_i p_i$.

**Generalization.** The state recurrence is defined for complex scalars with the adjoint replacing
the transpose. It extends through zero denominators and has no convergence test. The CGNR state
stores $(x,r,p)$ and computes the auxiliary $z$ and $w$ from these fields.
-/
noncomputable def cgneStep (s : Krylov.CGNE.State 𝔼 𝔼) : Krylov.CGNE.State 𝔼 𝔼 :=
  { x := s.x + cgneStepAlpha s • s.p
    r := cgneStepR A s
    p := op Aᴴ (cgneStepR A s) + cgneStepBeta A s • s.p }

/-- **Algorithm 8.5** of [saad2003iterative] (CGNE, Craig's method). Let
$A \in \mathbb{K}^{n \times n}$ and $b, x_0 \in \mathbb{K}^n$. The state after $i$ steps is
obtained from $r_0 = b - Ax_0$ and $p_0 = A^H r_0$ by $i$ passes of the recurrence
$$\alpha_j = \frac{(r_j, r_j)}{(p_j, p_j)}, \quad x_{j+1} = x_j + \alpha_j p_j, \quad r_{j+1} =
  r_j - \alpha_j A p_j,$$
$$\beta_j = \frac{(r_{j+1}, r_{j+1})}{(r_j, r_j)}, \quad p_{j+1} = A^H r_{j+1} + \beta_j p_j.$$

The state is the triple $(x_i, r_i, p_i)$ of type `Krylov.CGNE.State`, and a pass is
`SaadSparse.Chapter08.cgneStep`. A quotient with a vanishing denominator is $0$.

**Generalization.** The state recurrence is defined for complex scalars with the adjoint replacing
the transpose. It extends through zero denominators and has no convergence test. The CGNR state
stores $(x,r,p)$ and computes the auxiliary $z$ and $w$ from these fields.
-/
noncomputable def cgne (b x₀ : 𝔼) (i : ℕ) : Krylov.CGNE.State 𝔼 𝔼 :=
  (cgneStep A)^[i] { x := x₀, r := b - op A x₀, p := op Aᴴ (b - op A x₀) }

variable (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- The state of Algorithm 8.5 after $i + 1$ steps is one pass of the algorithm applied to the state
after $i$ steps.

**Generalization.** The state recurrence is defined for complex scalars with the adjoint replacing
the transpose. It extends through zero denominators and has no convergence test. The CGNR state
stores $(x,r,p)$ and computes the auxiliary $z$ and $w$ from these fields.
-/
theorem cgne_succ (i : ℕ) : cgne A b x₀ (i + 1) = cgneStep A (cgne A b x₀ i) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterate of Algorithm 8.5 after $0$ steps is $x_0$. -/
@[simp] theorem cgne_zero_x : (cgne A b x₀ 0).x = x₀ := rfl

/-- The residual of Algorithm 8.5 after $0$ steps is $r_0 = b - Ax_0$. -/
@[simp] theorem cgne_zero_r : (cgne A b x₀ 0).r = b - op A x₀ := rfl

/-- The search direction of Algorithm 8.5 after $0$ steps is $p_0 = A^H r_0$.

**Generalization.** The state recurrence is defined for complex scalars with the adjoint replacing
the transpose. It extends through zero denominators and has no convergence test. The CGNR state
stores $(x,r,p)$ and computes the auxiliary $z$ and $w$ from these fields.
-/
@[simp] theorem cgne_zero_p : (cgne A b x₀ 0).p = op Aᴴ (b - op A x₀) := rfl

/-! ### The bridge to the backbone CGNE recurrence -/

variable {A}

private theorem cgneStepAlpha_eq (s : Krylov.CGNE.State 𝔼 𝔼) :
    cgneStepAlpha s = (Krylov.CGNE.alpha s : 𝕜) := by
  rw [cgneStepAlpha, Krylov.CGNE.alpha, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]

private theorem cgneStepR_eq (s : Krylov.CGNE.State 𝔼 𝔼) :
    cgneStepR A s = (Krylov.CGNE.step (op A) (op Aᴴ) s).r := by
  rw [cgneStepR, cgneStepAlpha_eq, Krylov.CGNE.step_r]

private theorem cgneStepBeta_eq (s : Krylov.CGNE.State 𝔼 𝔼) :
    cgneStepBeta A s = Krylov.CGNE.beta (op A) (op Aᴴ) s := by
  rw [cgneStepBeta, Krylov.CGNE.beta, cgneStepR_eq, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K]

private theorem cgneStep_eq (s : Krylov.CGNE.State 𝔼 𝔼) :
    cgneStep A s = Krylov.CGNE.step (op A) (op Aᴴ) s := by
  have h : cgneStep A s =
      { x := s.x + cgneStepAlpha s • s.p
        r := cgneStepR A s
        p := op Aᴴ (cgneStepR A s) + cgneStepBeta A s • s.p } := rfl
  rw [h, cgneStepAlpha_eq, cgneStepR_eq, cgneStepBeta_eq]
  rfl

/-- For all $i$, the state of Algorithm 8.5 after $i$ steps is the state `Krylov.CGNE.iterate` of
the backbone CGNE recurrence for the operator pair $(A, A^H)$. -/
theorem cgne_eq_iterate (i : ℕ) :
    cgne A b x₀ i = Krylov.CGNE.iterate (op A) (op Aᴴ) b x₀ i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [cgne_succ, ih, cgneStep_eq, Krylov.CGNE.iterate_succ]

/-- **Algorithm 8.5** of [saad2003iterative], identification with the conjugate gradient method. Let
$A \in \mathbb{K}^{n \times n}$, let $b, x_0, u_0 \in \mathbb{K}^n$ with $A^H u_0 = x_0$, and
let $(u_i, \rho_i, q_i)$ be the iterate, residual and search direction of the conjugate gradient
method applied to $A A^H u = b$ from $u_0$. Then for every $i$ the state $(x_i, r_i, p_i)$ of
CGNE satisfies
$$x_i = x_0 + A^H (u_i - u_0), \qquad r_i = \rho_i, \qquad p_i = A^H q_i.$$

So Craig's method is the conjugate gradient method for $A A^H u = b$ read in the variable
$x = A^H u$, and no vector of the $u$-iteration is formed. The conjugate gradient iteration is
`CG.iterate` for the operator $A A^H$.

**Generalization.** The correspondence with CG is stated at every index for the totalized
recurrences, without a nonsingularity requirement. CGNE uses the explicit compatible start
$x_0=A^Hu_0$.
-/
theorem cgne_eq {u₀ : EuclideanSpace 𝕜 (Fin n)} (hu₀ : op Aᴴ u₀ = x₀) (i : ℕ) :
    (cgne A b x₀ i).x = x₀ + op Aᴴ ((CG.iterate (op A ∘ₗ op Aᴴ) b u₀ i).x - u₀) ∧
      (cgne A b x₀ i).r = (CG.iterate (op A ∘ₗ op Aᴴ) b u₀ i).r ∧
      (cgne A b x₀ i).p = op Aᴴ (CG.iterate (op A ∘ₗ op Aᴴ) b u₀ i).p := by
  obtain ⟨hx, hr, hp⟩ :=
    Krylov.CGNE.iterate_eq (op A) (op Aᴴ) b x₀ (isAdjointPair_op A) hu₀ i
  rw [cgne_eq_iterate]
  refine ⟨?_, hr, hp⟩
  rw [hx, map_sub, hu₀]
  abel

end CGNE

/-! ### The two optimality properties -/

section Optimality

variable {A : Matrix (Fin n) (Fin n) 𝕜} (b x₀ : EuclideanSpace 𝕜 (Fin n))

/-- **Section 8.3.1** of [saad2003iterative], optimality of CGNR. Let
$A \in \mathbb{K}^{n \times n}$ be nonsingular and $b, x_0 \in \mathbb{K}^n$, and let
$r_0 = b - Ax_0$. For every $m$, the CGNR iterate $x_m$ lies in
$x_0 + \mathcal{K}_m(A^H A, A^H r_0)$ and
$$\|b - Ax_m\|_2 \le \|b - Ay\|_2 \quad \text{for all } y \in x_0 + \mathcal{K}_m(A^H A, A^H
  r_0).$$

This is the minimization that GMRES performs, over a different subspace. The conclusion is
`IsMinResidual`.

**Generalization.** The affine Krylov comparison and optimality statements extend to complex
scalars, replacing transpose with adjoint and using Hermitian inner products.
-/
theorem cgnr_isMinResidual (hA : Function.Injective (op A)) (m : ℕ) :
    IsMinResidual (op A) b x₀ (Chapter06.krylov (Aᴴ * A) (op Aᴴ (b - op A x₀)) m)
      (cgnr A b x₀ m).x := by
  have hgal := CG.isGalerkinIterate (op Aᴴ b) x₀ (isSymmetricCoercive_normal hA) m
  rw [cgnr_eq, krylov_conjTranspose_mul]
  exact (Krylov.isGalerkinIterate_adjoint_comp_iff_isMinResidual (isAdjointPair_op A) b x₀ m
    _).1 hgal

/-- **Section 8.3.2** of [saad2003iterative], optimality of CGNE. Let
$A \in \mathbb{K}^{n \times n}$ with $A^H$ nonsingular, let $b, x_0 \in \mathbb{K}^n$ and
$r_0 = b - Ax_0$, let $u_0$ satisfy $A^H u_0 = x_0$, and let $x_*$ satisfy $Ax_* = b$. For every
$m$, the CGNE iterate $x_m$ lies in $x_0 + \mathcal{K}_m(A^H A, A^H r_0)$ and
$$\|x_* - x_m\|_2 \le \|x_* - y\|_2 \quad \text{for all } y \in x_0 + \mathcal{K}_m(A^H A, A^H
  r_0).$$

This is the affine subspace over which CGNR minimizes the residual
(`SaadSparse.Chapter08.subspace_adjoint_eq`). The conclusion is `IsMinError`.

**Generalization.** The affine Krylov comparison and optimality statements extend to complex
scalars, replacing transpose with adjoint and using Hermitian inner products.
-/
theorem cgne_isMinError (hA : Function.Injective (op Aᴴ))
    {u₀ xstar : EuclideanSpace 𝕜 (Fin n)} (hu₀ : op Aᴴ u₀ = x₀) (hstar : op A xstar = b)
    (m : ℕ) :
    IsMinError xstar x₀ (Chapter06.krylov (Aᴴ * A) (op Aᴴ (b - op A x₀)) m) (cgne A b x₀ m).x := by
  have hgal := CG.isGalerkinIterate b u₀ (isSymmetricCoercive_normal' hA) m
  rw [(cgne_eq b x₀ hu₀ m).1, krylov_conjTranspose_mul]
  exact Krylov.isMinError_of_isGalerkinIterate_comp_adjoint (isAdjointPair_op A) b x₀
    hu₀.symm hstar hgal

/-- **Section 8.3** of [saad2003iterative], the closing observation of the section. For
$A \in \mathbb{K}^{n \times n}$, $r_0 \in \mathbb{K}^n$ and every $m$,
$$A^H \mathcal{K}_m(A A^H, r_0) = \mathcal{K}_m(A^H A, A^H r_0).$$
So CGNR and CGNE take their iterates from the same affine subspace and differ only in what they
minimize over it.

**Generalization.** The affine Krylov comparison and optimality statements extend to complex
scalars, replacing transpose with adjoint and using Hermitian inner products.
-/
theorem subspace_adjoint_eq (A : Matrix (Fin n) (Fin n) 𝕜) (r₀ : EuclideanSpace 𝕜 (Fin n))
    (m : ℕ) :
    (Chapter06.krylov (A * Aᴴ) r₀ m).map (op Aᴴ) = Chapter06.krylov (Aᴴ * A) (op Aᴴ r₀) m := by
  rw [krylov_conjTranspose_mul, krylov_conjTranspose_mul]
  exact Krylov.map_subspace_comp (op A) (op Aᴴ) r₀ m

/-- **Section 8.3** of [saad2003iterative], the quantitative form of the warning at (8.8). Let
$A \in \mathbb{K}^{n \times n}$ be nonsingular, let $0 < \sigma_{\min} \le \sigma_{\max}$
satisfy $\sigma_{\min} \|x\|_2 \le \|Ax\|_2 \le \sigma_{\max} \|x\|_2$ for all $x$, and let
$b, x_0, x_* \in \mathbb{K}^n$ with $Ax_* = b$. Then for every $m$ the CGNR iterate $x_m$
satisfies
$$\|b - Ax_m\|_2 \le 2 \left( \frac{\kappa - 1}{\kappa + 1} \right)^m \|b - Ax_0\|_2, \qquad
  \kappa = \frac{\sigma_{\max}}{\sigma_{\min}}.$$

This is the conjugate gradient bound for the matrix $A^H A$, whose condition number is
$\kappa^2$; its square root $\kappa = \kappa_2(A)$ therefore governs the rate. That is why the
chapter prefers methods that do not pass through the normal equations.

**Reading.** The chapter explains the squared condition number and identifies the minimized
residual. This theorem combines those observations with the earlier CG bound and permits any
positive lower and upper norm bounds for $A$.
-/
theorem cgnr_norm_residual_le {smin smax : ℝ} (hs : 0 < smin) (hss : smin ≤ smax)
    (hmin : ∀ x : EuclideanSpace 𝕜 (Fin n), smin * ‖x‖ ≤ ‖op A x‖)
    (hmax : ∀ x : EuclideanSpace 𝕜 (Fin n), ‖op A x‖ ≤ smax * ‖x‖)
    {xstar : EuclideanSpace 𝕜 (Fin n)} (hstar : op A xstar = b)
    (hA : Function.Injective (op A)) (m : ℕ) :
    ‖b - op A (cgnr A b x₀ m).x‖
      ≤ 2 * ((smax / smin - 1) / (smax / smin + 1)) ^ m * ‖b - op A x₀‖ := by
  have hB : (op Aᴴ ∘ₗ op A).IsSymmetricBoundedBy (smin ^ 2) (smax ^ 2) :=
    Krylov.adjoint_comp_isSymmetricBoundedBy (isAdjointPair_op A)
      (fun x => by
        nlinarith [hmin x, norm_nonneg (op A x), mul_nonneg hs.le (norm_nonneg x)])
      (fun x => by nlinarith [hmax x, norm_nonneg (op A x), norm_nonneg x])
  have hx := cgnr_isMinResidual b x₀ hA m
  rw [krylov_conjTranspose_mul] at hx
  exact Krylov.IsMinResidual.norm_residual_le_of_adjoint_comp (isAdjointPair_op A) hs hss hB
    hstar hx

end Optimality

end SaadSparse.Chapter08
