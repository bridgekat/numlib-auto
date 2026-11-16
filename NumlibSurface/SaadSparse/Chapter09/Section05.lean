/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.NormalEquations
import Numlib.Krylov.Preconditioned
import NumlibSurface.SaadSparse.Chapter08.Section03
import NumlibSurface.SaadSparse.Chapter09.Section02

/-!
# Saad, Section 9.5: Preconditioned CG for the normal equations

This module formalizes Section 9.5 of [saad2003iterative], with Problems P-9.4 and P-9.5. Both
algorithms of the section are Algorithm 9.1 run on a normal-equations system and rearranged so that
only products with $A$ and $A^H$ and solves with $M$ occur; neither $A^H A$ nor $A A^H$ is formed.
Algorithm 9.7 (left-preconditioned CGNR) is Algorithm 9.1 for $A^H A x = A^H b$, and Algorithm 9.8
(left-preconditioned CGNE) is Algorithm 9.1 for $A A^H u = b$, read through $x = A^H u$. They are
CGNR and CGNE of Section 8.3 (Algorithms 8.4 and 8.5) with $M^{-1}$ inserted, with the same two
rearrangements: the residual carried is the true residual $r_j = b - A x_j$, and the direction
vectors of Algorithm 9.8 carry an extra factor $A^H$.

Algorithm 9.7 minimizes $\|b - Ax\|_2$ over $x_0 + \mathcal{K}_m(M^{-1} A^H A, M^{-1} A^H r_0)$, and
Algorithm 9.8 minimizes $\|x_* - x\|_2$ over $x_0 + \mathcal{K}_m(A^H M^{-1} A, A^H M^{-1} r_0)$.
Unlike in the unpreconditioned case, the two spaces differ; at $M = I$ both are the space
$x_0 + \mathcal{K}_m(A^H A, A^H r_0)$ of Section 8.3. Problem P-9.4 asks for the right- and
split-preconditioned versions of the two algorithms; they are the methods of Section 9.2 applied to
the normal-equations matrices, and each gives the iterates of Algorithm 9.7 or 9.8 after a change of
variables. Problem P-9.5 treats the centred systems $A^H M^{-1} A x = A^H M^{-1} b$ and
$A M^{-1} A^H u = b$ with $x = M^{-1} A^H u$, whose coefficient matrices are symmetric. The proofs
use `NumlibSurface.SaadSparse.Chapter09.Section02` and `Numlib.Krylov.NormalEquations`.

## Main definitions

* Algorithm 9.7, `SaadSparse.Chapter09.pcgnr`: left-preconditioned CGNR.
* Algorithm 9.8, `SaadSparse.Chapter09.pcgne`: left-preconditioned CGNE.
* Problem P-9.5, `SaadSparse.Chapter09.centredPcgnr`: the conjugate gradient method for the centred
  system $A^H M^{-1} A x = A^H M^{-1} b$.
* Problem P-9.5, `SaadSparse.Chapter09.centredPcgne`: the conjugate gradient method for the centred
  system $A M^{-1} A^H u = b$.
* Problem P-9.5, `SaadSparse.Chapter09.centredPcgneX`: the iterate
  $x_j = x_0 + M^{-1} A^H (u_j - u_0)$ of the centred CGNE.

## Main results

* Algorithm 9.7, `SaadSparse.Chapter09.pcgnr_eq`: Algorithm 9.7 is Algorithm 9.1 for
  $A^H A x = A^H b$.
* Section 9.5, `SaadSparse.Chapter09.pcgnr_isMinResidual`: Algorithm 9.7 minimizes $\|b - Ax\|_2$
  over $x_0 + \mathcal{K}_m(M^{-1} A^H A, M^{-1} A^H r_0)$.
* Algorithm 9.8, `SaadSparse.Chapter09.pcgne_eq`: Algorithm 9.8 is Algorithm 9.1 for $A A^H u = b$,
  read through $x = A^H u$.
* Section 9.5, `SaadSparse.Chapter09.pcgne_isMinError`: Algorithm 9.8 minimizes $\|x_* - x\|_2$ over
  $x_0 + \mathcal{K}_m(A^H M^{-1} A, A^H M^{-1} r_0)$.
* Problem P-9.4, `SaadSparse.Chapter09.rightPcgnr_eq`: right-preconditioned CGNR is Algorithm 9.7
  after $x = M^{-1} u$.
* Problem P-9.4, `SaadSparse.Chapter09.splitPcgnr_eq`: split-preconditioned CGNR is Algorithm 9.7.
* Problem P-9.4, `SaadSparse.Chapter09.rightPcgne_eq`: right-preconditioned CGNE is Algorithm 9.8
  after $x = A^H M^{-1} w$.
* Problem P-9.4, `SaadSparse.Chapter09.splitPcgne_eq`: split-preconditioned CGNE is Algorithm 9.8
  after $x = A^H u$.
* Problem P-9.5, `SaadSparse.Chapter09.isSymmetric_centredNR`: $A^H M^{-1} A$ is symmetric when
  $M^{-1}$ is.
* Problem P-9.5, `SaadSparse.Chapter09.isSymmetric_centredNE`: $A M^{-1} A^H$ is symmetric when
  $M^{-1}$ is.
* Problem P-9.5, `SaadSparse.Chapter09.op_centredNR_apply`: $A^H M^{-1} A y = A^H(M^{-1}(Ay))$.
* Problem P-9.5, `SaadSparse.Chapter09.op_centredNE_apply`: $A M^{-1} A^H y = A(M^{-1}(A^H y))$.
* Problem P-9.5, `SaadSparse.Chapter09.centredPcgnr_residual_eq`: the residual of the centred CGNR
  is $A^H M^{-1}(b - A x_j)$.
* Problem P-9.5, `SaadSparse.Chapter09.centredPcgne_eq`: the residual of the centred CGNE is the
  true residual $b - A x_j$.
* Problem P-9.5, `SaadSparse.Chapter09.isSymmetricCoercive_centredNR`: $A^H M^{-1} A$ is symmetric
  positive definite for nonsingular $A$ and symmetric positive definite $M^{-1}$.
* Problem P-9.5, `SaadSparse.Chapter09.centredPcgnr_isGalerkinIterate`: the centred CGNR iterate is
  the Galerkin iterate over $x_0 + \mathcal{K}_m(A^H M^{-1} A, A^H M^{-1} r_0)$.

## Implementation notes

* The states of Algorithms 9.7 and 9.8 are `Krylov.CGNR.State` and `Krylov.CGNE.State`, with fields
  `x`, `r` and `p`. The vectors $\tilde r_j = A^H r_j$, $z_j$ and $w_j = A p_j$ are recomputed and
  not stored.
* Indices are $0$-based. Division by a vanishing quantity is $0$, which reproduces the breakdown
  behaviour of the book.
* The two optimality readings of Section 8.3 are restated for an arbitrary subspace $K$, because
  preconditioning replaces the Krylov space of the backbone by another one.
* The right- and split-preconditioned variants of Problem P-9.4 need no new algorithm: they are
  `SaadSparse.Chapter09.rightPcg` and `SaadSparse.Chapter09.splitPcg` applied to $A^H A$ and
  $A A^H$.
-/

open Matrix

open scoped Matrix SaadSparse

namespace SaadSparse.Chapter09

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

/-! ### Preliminaries: the two normal-equations operators -/

/-- For every $A \in \mathbb{K}^{n \times n}$, the operator of $A^H A$ is symmetric. It is the
coefficient operator of the system that Algorithm 9.7 of [saad2003iterative] preconditions. -/
theorem isSymmetric_conjTranspose_mul (A : Matrix (Fin n) (Fin n) 𝕜) :
    (op (Aᴴ * A)).IsSymmetric := by
  intro x y
  simp only [op_mul_apply]
  rw [Chapter08.inner_op_conjTranspose, Chapter07.inner_op_conjTranspose]

/-- For every $A \in \mathbb{K}^{n \times n}$, the operator of $A A^H$ is symmetric. It is the
coefficient operator of the system that Algorithm 9.8 of [saad2003iterative] preconditions. -/
theorem isSymmetric_mul_conjTranspose (A : Matrix (Fin n) (Fin n) 𝕜) :
    (op (A * Aᴴ)).IsSymmetric := by
  intro x y
  simp only [op_mul_apply]
  rw [Chapter07.inner_op_conjTranspose, Chapter08.inner_op_conjTranspose]

/-- $(A^H A p, p) = \|Ap\|_2^2$: the denominator in line 4 of Algorithm 9.7 is the one that
Algorithm 9.1 forms. -/
private theorem inner_conjTranspose_mul_self (A : Matrix (Fin n) (Fin n) 𝕜) (p : 𝔼) :
    inner 𝕜 p (op (Aᴴ * A) p) = (‖op A p‖ : 𝕜) ^ 2 := by
  rw [op_mul_apply, ← Chapter07.inner_op_conjTranspose, inner_self_eq_norm_sq_to_K]

/-- $(A^H q, A^H q) = (A A^H q, q)$: the denominator in line 4 of Algorithm 9.8 is the one that
Algorithm 9.1 forms, read through $p = A^H q$. -/
private theorem inner_mul_conjTranspose_self (A : Matrix (Fin n) (Fin n) 𝕜) (q : 𝔼) :
    inner 𝕜 (op Aᴴ q) (op Aᴴ q) = inner 𝕜 q (op (A * Aᴴ) q) := by
  rw [op_mul_apply, Chapter08.inner_op_conjTranspose]

/-- For $A, M \in \mathbb{K}^{n \times n}$, $v \in \mathbb{K}^n$ and $m \in \mathbb{N}$,
$$A^H \mathcal{K}_m(M^{-1} A A^H, v) = \mathcal{K}_m(A^H M^{-1} A, A^H v).$$
This is the change of variables $x = A^H u$ of Algorithm 9.8 of [saad2003iterative], and it
identifies the affine space that the algorithm searches. -/
theorem map_krylov_conjTranspose (A M : Matrix (Fin n) (Fin n) 𝕜)
    (v : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) :
    (Chapter06.krylov (M⁻¹ * (A * Aᴴ)) v m).map (op Aᴴ)
      = Chapter06.krylov (Aᴴ * (M⁻¹ * A)) (op Aᴴ v) m := by
  rw [Chapter06.krylov_eq, Chapter06.krylov_eq, ← Matrix.mul_assoc M⁻¹ A Aᴴ, op_mul (M⁻¹ * A) Aᴴ,
    op_mul Aᴴ (M⁻¹ * A), op_mul M⁻¹ A]
  exact Krylov.map_subspace_comp (op M⁻¹ ∘ₗ op A) (op Aᴴ) v m

/-!
### The two optimality readings, over an arbitrary subspace

The backbone module `Numlib.Krylov.NormalEquations` states both readings for the unpreconditioned
Krylov space $\mathcal{K}_m(A^H A, A^H r_0)$, which is all that Section 8.3 needs. Preconditioning
replaces that space by another one. Neither argument uses the form of the space, so both are
restated here for an arbitrary subspace $K$.
-/

/-- **Optimality of CGNR over an arbitrary subspace.** Let $A \in \mathbb{K}^{n \times n}$,
$b, x_0, x \in \mathbb{K}^n$ and $K$ a subspace of $\mathbb{K}^n$. Then $x$ is a Galerkin
iterate of the normal equations $A^H A x = A^H b$ over $x_0 + K$ if and only if $x$ is a
minimal-residual iterate of $Ax = b$ over $x_0 + K$. Both conditions say that $x - x_0 \in K$
and $b - Ax \perp AK$.

This is `Krylov.isGalerkinIterate_adjoint_comp_iff_isMinResidual` with the Krylov subspace
replaced by an arbitrary $K$. -/
theorem isGalerkin_adjoint_comp_iff_isMinResidual (A : Matrix (Fin n) (Fin n) 𝕜)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) (K : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n)))
    (x : EuclideanSpace 𝕜 (Fin n)) :
    IsGalerkin (op Aᴴ ∘ₗ op A) (op Aᴴ b) x₀ K x ↔ IsMinResidual (op A) b x₀ K x := by
  rw [IsMinResidual.iff_isPetrovGalerkin]
  constructor <;> rintro ⟨hmem, horth⟩
  · refine ⟨hmem, (Submodule.mem_orthogonal _ _).2 ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h := (Submodule.mem_orthogonal _ _).1 horth w hw
    rwa [LinearMap.comp_apply, ← map_sub,
      ← Chapter07.inner_op_conjTranspose A] at h
  · refine ⟨hmem, (Submodule.mem_orthogonal _ _).2 fun w hw => ?_⟩
    have h := (Submodule.mem_orthogonal _ _).1 horth (op A w) (Submodule.mem_map_of_mem hw)
    rwa [LinearMap.comp_apply, ← map_sub,
      ← Chapter07.inner_op_conjTranspose A]

/-- **Optimality of CGNE over an arbitrary subspace.** Let $A \in \mathbb{K}^{n \times n}$,
$b, u_0, u, x_* \in \mathbb{K}^n$ and $K$ a subspace of $\mathbb{K}^n$, with $A x_* = b$. Let
$x_0 = A^H u_0$, and let $u$ be a Galerkin iterate of $A A^H u = b$ over $u_0 + K$. Then
$x = x_0 + A^H(u - u_0)$ satisfies $x - x_0 \in A^H K$ and
$$\|x_* - x\|_2 \le \|x_* - y\|_2 \quad \text{for all } y \in x_0 + A^H K.$$

This is `Krylov.isMinError_of_isGalerkinIterate_comp_adjoint` with the Krylov subspace replaced
by an arbitrary $K$. -/
theorem isMinError_of_isGalerkin_comp_adjoint (A : Matrix (Fin n) (Fin n) 𝕜)
    {b x₀ u₀ u xstar : EuclideanSpace 𝕜 (Fin n)}
    {K : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin n))} (hx₀ : x₀ = op Aᴴ u₀)
    (hstar : op A xstar = b) (hu : IsGalerkin (op A ∘ₗ op Aᴴ) b u₀ K u) :
    IsMinError xstar x₀ (K.map (op Aᴴ)) (x₀ + op Aᴴ (u - u₀)) := by
  refine ⟨by rw [add_sub_cancel_left]; exact Submodule.mem_map_of_mem hu.mem, fun y hy => ?_⟩
  rw [show xstar - (x₀ + op Aᴴ (u - u₀)) = (xstar - x₀) - op Aᴴ (u - u₀) by abel,
    show xstar - y = (xstar - x₀) - (y - x₀) by abel]
  refine Submodule.norm_sub_le_of_forall_inner_eq_zero
    (Submodule.mem_map_of_mem hu.mem) ?_ hy
  rintro _ ⟨z, hz, rfl⟩
  have h1 : op A (op Aᴴ (u - u₀)) = (op A ∘ₗ op Aᴴ) u - (op A ∘ₗ op Aᴴ) u₀ := by
    rw [← LinearMap.comp_apply]
    exact map_sub _ _ _
  have h2 : op A x₀ = (op A ∘ₗ op Aᴴ) u₀ := by rw [hx₀, LinearMap.comp_apply]
  have hA : op A ((xstar - x₀) - op Aᴴ (u - u₀)) = b - (op A ∘ₗ op Aᴴ) u := by
    rw [map_sub, map_sub, hstar, h1, h2]; abel
  rw [← Chapter07.inner_op_conjTranspose A, hA,
    ← inner_conj_symm,
    (Submodule.mem_orthogonal _ _).1 hu.orth z hz, map_zero]

/-! ### Algorithm 9.7: left-preconditioned CGNR -/

section CGNR

variable (A M : Matrix (Fin n) (Fin n) 𝕜)

/-- Line 4 of Algorithm 9.7 of [saad2003iterative]: the step length
$\alpha_j = (z_j, \tilde r_j)/\|w_j\|_2^2$ on a state $(x_j, r_j, p_j)$, with
$\tilde r_j = A^H r_j$, $z_j = M^{-1} \tilde r_j$ and $w_j = A p_j$ recomputed and not stored. -/
noncomputable def pcgnrStepAlpha (s : Krylov.CGNR.State 𝔼 𝔼) : 𝕜 :=
  inner 𝕜 (op Aᴴ s.r) (op M⁻¹ (op Aᴴ s.r)) / (‖op A s.p‖ : 𝕜) ^ 2

/-- Line 6 of Algorithm 9.7 of [saad2003iterative]: the next residual
$r_{j+1} = r_j - \alpha_j w_j$, with $w_j = A p_j$. -/
noncomputable def pcgnrStepR (s : Krylov.CGNR.State 𝔼 𝔼) : 𝔼 :=
  s.r - pcgnrStepAlpha A M s • op A s.p

/-- Line 9 of Algorithm 9.7 of [saad2003iterative]: the coefficient $\beta_j = (z_{j+1}, \tilde
r_{j+1})/(z_j, \tilde r_j)$. -/
noncomputable def pcgnrStepBeta (s : Krylov.CGNR.State 𝔼 𝔼) : 𝕜 :=
  inner 𝕜 (op Aᴴ (pcgnrStepR A M s)) (op M⁻¹ (op Aᴴ (pcgnrStepR A M s))) /
    inner 𝕜 (op Aᴴ s.r) (op M⁻¹ (op Aᴴ s.r))

/-- One pass through lines 3–10 of Algorithm 9.7 of [saad2003iterative]. It maps the state
$(x_j, r_j, p_j)$ to $(x_j + \alpha_j p_j, \; r_{j+1}, \; z_{j+1} + \beta_j p_j)$, with
$z_{j+1} = M^{-1} A^H r_{j+1}$. -/
noncomputable def pcgnrStep (s : Krylov.CGNR.State 𝔼 𝔼) : Krylov.CGNR.State 𝔼 𝔼 :=
  { x := s.x + pcgnrStepAlpha A M s • s.p
    r := pcgnrStepR A M s
    p := op M⁻¹ (op Aᴴ (pcgnrStepR A M s)) + pcgnrStepBeta A M s • s.p }

/-- **Algorithm 9.7** of [saad2003iterative] (left-preconditioned CGNR). Let
$A, M \in \mathbb{K}^{n \times n}$ and $b, x_0 \in \mathbb{K}^n$. Set $r_0 = b - A x_0$,
$\tilde r_0 = A^H r_0$ and $p_0 = z_0 = M^{-1} \tilde r_0$. For $j = 0, 1, \ldots$ compute
$$w_j = A p_j, \quad \alpha_j = \frac{(z_j, \tilde r_j)}{\|w_j\|_2^2}, \quad x_{j+1} = x_j +
  \alpha_j p_j, \quad r_{j+1} = r_j - \alpha_j w_j,$$
$$\tilde r_{j+1} = A^H r_{j+1}, \quad z_{j+1} = M^{-1} \tilde r_{j+1}, \quad \beta_j =
  \frac{(z_{j+1}, \tilde r_{j+1})}{(z_j, \tilde r_j)}, \quad p_{j+1} = z_{j+1} + \beta_j p_j.$$
The value at $j$ is the state $(x_j, r_j, p_j)$ after $j$ steps. -/
noncomputable def pcgnr (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) : Krylov.CGNR.State 𝔼 𝔼 :=
  (pcgnrStep A M)^[j] { x := x₀, r := b - op A x₀, p := op M⁻¹ (op Aᴴ (b - op A x₀)) }

/-- Line 5 of Algorithm 9.7: $x_{j+1} = x_j + \alpha_j p_j$. -/
theorem pcgnrStep_x (s : Krylov.CGNR.State 𝔼 𝔼) :
    (pcgnrStep A M s).x = s.x + pcgnrStepAlpha A M s • s.p := rfl

/-- Line 6 of Algorithm 9.7: $r_{j+1} = r_j - \alpha_j w_j$. -/
theorem pcgnrStep_r (s : Krylov.CGNR.State 𝔼 𝔼) : (pcgnrStep A M s).r = pcgnrStepR A M s := rfl

/-- Line 10 of Algorithm 9.7: $p_{j+1} = z_{j+1} + \beta_j p_j$. -/
theorem pcgnrStep_p (s : Krylov.CGNR.State 𝔼 𝔼) :
    (pcgnrStep A M s).p
      = op M⁻¹ (op Aᴴ (pcgnrStepR A M s)) + pcgnrStepBeta A M s • s.p := rfl

/-- The state of Algorithm 9.7 after $j + 1$ steps is one step applied to the state after $j$ steps.
-/
theorem pcgnr_succ (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    pcgnr A M b x₀ (j + 1) = pcgnrStep A M (pcgnr A M b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

/-- Line 1 of Algorithm 9.7: the iteration starts at $x_0$. -/
@[simp] theorem pcgnr_zero_x (b x₀ : EuclideanSpace 𝕜 (Fin n)) : (pcgnr A M b x₀ 0).x = x₀ := rfl

/-- Line 1 of Algorithm 9.7: $r_0 = b - A x_0$. -/
@[simp] theorem pcgnr_zero_r (b x₀ : EuclideanSpace 𝕜 (Fin n)) :
    (pcgnr A M b x₀ 0).r = b - op A x₀ := rfl

/-- Line 1 of Algorithm 9.7: $p_0 = z_0 = M^{-1} A^H r_0$. -/
@[simp] theorem pcgnr_zero_p (b x₀ : EuclideanSpace 𝕜 (Fin n)) :
    (pcgnr A M b x₀ 0).p = op M⁻¹ (op Aᴴ (b - op A x₀)) := rfl

/-- The residual $r_j$ of Algorithm 9.7 is the true residual $b - A x_j$. The preconditioner is
applied to the normal-equations residual $\tilde r_j = A^H r_j$. -/
theorem pcgnr_residual_eq (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    (pcgnr A M b x₀ j).r = b - op A (pcgnr A M b x₀ j).x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pcgnr_succ, pcgnrStep_r, pcgnrStep_x, pcgnrStepR, ih, map_add, map_smul, sub_sub]

/-! ### The bridge to Algorithm 9.1 -/

variable {A M}

private theorem pcgnrStepAlpha_eq (hMinv : (op M⁻¹).IsSymmetric) (s : Krylov.CGNR.State 𝔼 𝔼) :
    pcgnrStepAlpha A M s = pcgStepAlpha (Aᴴ * A) M (s.x, op Aᴴ s.r, s.p) := by
  rw [pcgnrStepAlpha, pcgStepAlpha_def, hMinv (op Aᴴ s.r) (op Aᴴ s.r),
    inner_conjTranspose_mul_self]

private theorem pcgnrStepR_eq (hMinv : (op M⁻¹).IsSymmetric) (s : Krylov.CGNR.State 𝔼 𝔼) :
    op Aᴴ (pcgnrStepR A M s) = pcgStepR (Aᴴ * A) M (s.x, op Aᴴ s.r, s.p) := by
  rw [pcgnrStepR, pcgStepR_def, ← pcgnrStepAlpha_eq hMinv, map_sub, map_smul, op_mul_apply]

private theorem pcgnrStepBeta_eq (hMinv : (op M⁻¹).IsSymmetric) (s : Krylov.CGNR.State 𝔼 𝔼) :
    pcgnrStepBeta A M s = pcgStepBeta (Aᴴ * A) M (s.x, op Aᴴ s.r, s.p) := by
  rw [pcgnrStepBeta, pcgStepBeta_def, ← pcgnrStepR_eq hMinv,
    hMinv (op Aᴴ (pcgnrStepR A M s)) (op Aᴴ (pcgnrStepR A M s)), hMinv (op Aᴴ s.r) (op Aᴴ s.r)]

private theorem pcgnrStep_eq (hMinv : (op M⁻¹).IsSymmetric) (s : Krylov.CGNR.State 𝔼 𝔼) :
    ((pcgnrStep A M s).x, op Aᴴ (pcgnrStep A M s).r, (pcgnrStep A M s).p)
      = pcgStep (Aᴴ * A) M (s.x, op Aᴴ s.r, s.p) := by
  rw [pcgnrStep_x, pcgnrStep_r, pcgnrStep_p, pcgStep, pcgnrStepAlpha_eq hMinv,
    pcgnrStepBeta_eq hMinv, ← pcgnrStepR_eq hMinv]

/-- **Algorithm 9.7** of [saad2003iterative] as Algorithm 9.1 for the normal equations. Let
$A, M \in \mathbb{K}^{n \times n}$ with $M^{-1}$ symmetric. Then for all $b, x_0$ and all $j$,
the triple $(x_j, A^H r_j, p_j)$ of Algorithm 9.7 is the triple $(x_j, r_j, p_j)$ of Algorithm
9.1 for $A^H A x = A^H b$ with the preconditioner $M$.

The residual of Algorithm 9.1 is the normal-equations residual $\tilde r_j = A^H r_j$, and its
denominator $(A^H A p_j, p_j)$ is $\|w_j\|_2^2$. The symmetry of $M^{-1}$ moves it across the
inner products of lines 4 and 9. -/
theorem pcgnr_eq (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    ((pcgnr A M b x₀ j).x, op Aᴴ (pcgnr A M b x₀ j).r, (pcgnr A M b x₀ j).p)
      = pcg (Aᴴ * A) M (op Aᴴ b) x₀ j := by
  have hinit : op Aᴴ b - op (Aᴴ * A) x₀ = op Aᴴ (b - op A x₀) := by
    rw [op_mul_apply, ← map_sub]
  induction j with
  | zero => exact (congrArg (fun z : 𝔼 => (x₀, z, op M⁻¹ z)) hinit).symm
  | succ j ih => rw [pcgnr_succ, pcg_succ, ← ih, pcgnrStep_eq hMinv]

/-- Let $M^{-1}$ be symmetric. The iterate $x_j$ of Algorithm 9.7 is the iterate of Algorithm 9.1
for $A^H A x = A^H b$. -/
theorem pcgnrX_eq (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    (pcgnr A M b x₀ j).x = pcgX (Aᴴ * A) M (op Aᴴ b) x₀ j := by
  rw [pcgX, ← pcgnr_eq hMinv b x₀ j]

/-- **Section 9.5** of [saad2003iterative], optimality of Algorithm 9.7. Let $M$ be a
preconditioner, and let $A \in \mathbb{K}^{n \times n}$ satisfy $c\,(Mx, x) \le \|Ax\|_2^2$ for
all $x$, for some $c > 0$. Then for all $b, x_0$ and $m$, the iterate $x_m$ of Algorithm 9.7
satisfies $x_m - x_0 \in \mathcal{K}_m(M^{-1} A^H A, M^{-1} A^H r_0)$ and
$$\|b - A x_m\|_2 \le \|b - Ax\|_2 \quad \text{for all } x \in x_0 + \mathcal{K}_m(M^{-1} A^H A,
  M^{-1} A^H r_0).$$

The hypothesis is the generalized eigenvalue bound that makes $M^{-1} A^H A$ symmetric and
coercive in the $M$-inner product. For a nonsingular $A$ and a symmetric positive definite $M$
it holds with $c = \sigma_{\min}(A)^2/\lambda_{\max}(M)$. -/
theorem pcgnr_isMinResidual (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : 𝔼, c * RCLike.re (inner 𝕜 (op M x) x) ≤ ‖op A x‖ ^ 2)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) :
    IsMinResidual (op A) b x₀
        (Chapter06.krylov (M⁻¹ * (Aᴴ * A)) (op M⁻¹ (op Aᴴ (b - op A x₀))) m)
      (pcgnr A M b x₀ m).x := by
  have hinit : op Aᴴ b - op (Aᴴ * A) x₀ = op Aᴴ (b - op A x₀) := by
    rw [op_mul_apply, ← map_sub]
  have hcoer' : ∀ x : 𝔼, c * RCLike.re (inner 𝕜 (op M x) x)
      ≤ RCLike.re (inner 𝕜 (op (Aᴴ * A) x) x) := fun x => by
    rw [op_mul, Krylov.inner_adjoint_comp_self
      (LinearMap.isAdjointPair_inner_iff.2 (Chapter08.inner_op_conjTranspose A)) x,
      RCLike.ofReal_re]
    exact hcoer x
  have h := pcg_isGalerkinIterate (A := Aᴴ * A) (M := M) hM (isSymmetric_conjTranspose_mul A)
    hc hcoer' (op Aᴴ b) x₀ m
  rw [hinit, op_mul] at h
  rw [pcgnrX_eq hM.isSymmetric_inv]
  exact (isGalerkin_adjoint_comp_iff_isMinResidual A b x₀ _ _).1 h

end CGNR

/-! ### Algorithm 9.8: left-preconditioned CGNE -/

section CGNE

variable (A M : Matrix (Fin n) (Fin n) 𝕜)

/-- Line 4 of Algorithm 9.8 of [saad2003iterative]: the step length
$\alpha_j = (z_j, r_j)/(p_j, p_j)$ on a state $(x_j, r_j, p_j)$, with $z_j = M^{-1} r_j$
recomputed and not stored. The direction $p_j$ is $A^H q_j$ for the direction $q_j$ of Algorithm
9.1 for $A A^H u = b$, so $(p_j, p_j)$ is the quantity $(A A^H q_j, q_j)$ of that algorithm. -/
noncomputable def pcgneStepAlpha (s : Krylov.CGNE.State 𝔼 𝔼) : 𝕜 :=
  inner 𝕜 s.r (op M⁻¹ s.r) / inner 𝕜 s.p s.p

/-- Line 6 of Algorithm 9.8 of [saad2003iterative]: the next residual
$r_{j+1} = r_j - \alpha_j w_j$, with $w_j = A p_j$. -/
noncomputable def pcgneStepR (s : Krylov.CGNE.State 𝔼 𝔼) : 𝔼 :=
  s.r - pcgneStepAlpha M s • op A s.p

/-- Line 8 of Algorithm 9.8 of [saad2003iterative]: the coefficient
$\beta_j = (z_{j+1}, r_{j+1})/(z_j, r_j)$. -/
noncomputable def pcgneStepBeta (s : Krylov.CGNE.State 𝔼 𝔼) : 𝕜 :=
  inner 𝕜 (pcgneStepR A M s) (op M⁻¹ (pcgneStepR A M s)) / inner 𝕜 s.r (op M⁻¹ s.r)

/-- One pass through lines 3–9 of Algorithm 9.8 of [saad2003iterative]. It maps the state
$(x_j, r_j, p_j)$ to $(x_j + \alpha_j p_j, \; r_{j+1}, \; A^H z_{j+1} + \beta_j p_j)$, with
$z_{j+1} = M^{-1} r_{j+1}$. -/
noncomputable def pcgneStep (s : Krylov.CGNE.State 𝔼 𝔼) : Krylov.CGNE.State 𝔼 𝔼 :=
  { x := s.x + pcgneStepAlpha M s • s.p
    r := pcgneStepR A M s
    p := op Aᴴ (op M⁻¹ (pcgneStepR A M s)) + pcgneStepBeta A M s • s.p }

/-- **Algorithm 9.8** of [saad2003iterative] (left-preconditioned CGNE). Let
$A, M \in \mathbb{K}^{n \times n}$ and $b, x_0 \in \mathbb{K}^n$. Set $r_0 = b - A x_0$,
$z_0 = M^{-1} r_0$ and $p_0 = A^H z_0$. For $j = 0, 1, \ldots$ compute
$$w_j = A p_j, \quad \alpha_j = \frac{(z_j, r_j)}{(p_j, p_j)}, \quad x_{j+1} = x_j + \alpha_j
  p_j, \quad r_{j+1} = r_j - \alpha_j w_j,$$
$$z_{j+1} = M^{-1} r_{j+1}, \quad \beta_j = \frac{(z_{j+1}, r_{j+1})}{(z_j, r_j)}, \quad
  p_{j+1} = A^H z_{j+1} + \beta_j p_j.$$
The value at $j$ is the state $(x_j, r_j, p_j)$ after $j$ steps. -/
noncomputable def pcgne (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) : Krylov.CGNE.State 𝔼 𝔼 :=
  (pcgneStep A M)^[j] { x := x₀, r := b - op A x₀, p := op Aᴴ (op M⁻¹ (b - op A x₀)) }

/-- Line 5 of Algorithm 9.8: $x_{j+1} = x_j + \alpha_j p_j$. -/
theorem pcgneStep_x (s : Krylov.CGNE.State 𝔼 𝔼) :
    (pcgneStep A M s).x = s.x + pcgneStepAlpha M s • s.p := rfl

/-- Line 6 of Algorithm 9.8: $r_{j+1} = r_j - \alpha_j w_j$. -/
theorem pcgneStep_r (s : Krylov.CGNE.State 𝔼 𝔼) : (pcgneStep A M s).r = pcgneStepR A M s := rfl

/-- Line 9 of Algorithm 9.8: $p_{j+1} = A^H z_{j+1} + \beta_j p_j$. -/
theorem pcgneStep_p (s : Krylov.CGNE.State 𝔼 𝔼) :
    (pcgneStep A M s).p
      = op Aᴴ (op M⁻¹ (pcgneStepR A M s)) + pcgneStepBeta A M s • s.p := rfl

/-- The state of Algorithm 9.8 after $j + 1$ steps is one step applied to the state after $j$ steps.
-/
theorem pcgne_succ (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    pcgne A M b x₀ (j + 1) = pcgneStep A M (pcgne A M b x₀ j) :=
  Function.iterate_succ_apply' _ _ _

/-- Line 1 of Algorithm 9.8: the iteration starts at $x_0$. -/
@[simp] theorem pcgne_zero_x (b x₀ : EuclideanSpace 𝕜 (Fin n)) : (pcgne A M b x₀ 0).x = x₀ := rfl

/-- Line 1 of Algorithm 9.8: $r_0 = b - A x_0$. -/
@[simp] theorem pcgne_zero_r (b x₀ : EuclideanSpace 𝕜 (Fin n)) :
    (pcgne A M b x₀ 0).r = b - op A x₀ := rfl

/-- Line 1 of Algorithm 9.8: $p_0 = A^H z_0 = A^H M^{-1} r_0$. -/
@[simp] theorem pcgne_zero_p (b x₀ : EuclideanSpace 𝕜 (Fin n)) :
    (pcgne A M b x₀ 0).p = op Aᴴ (op M⁻¹ (b - op A x₀)) := rfl

/-- The residual $r_j$ of Algorithm 9.8 is the true residual $b - A x_j$. -/
theorem pcgne_residual_eq (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    (pcgne A M b x₀ j).r = b - op A (pcgne A M b x₀ j).x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pcgne_succ, pcgneStep_r, pcgneStep_x, pcgneStepR, ih, map_add, map_smul, sub_sub]

/-! ### The bridge to Algorithm 9.1 -/

variable {A M}

/-- **Algorithm 9.8** of [saad2003iterative] as Algorithm 9.1 for $A A^H u = b$, read in
$x = A^H u$. Let $A, M \in \mathbb{K}^{n \times n}$ with $M^{-1}$ symmetric, and let $u_0$
satisfy $A^H u_0 = x_0$. Let $(u_j, r_j', q_j)$ be the state of Algorithm 9.1 for $A A^H u = b$
with the preconditioner $M$, started at $u_0$. Then the state $(x_j, r_j, p_j)$ of Algorithm 9.8
satisfies, for all $j$,
$$x_j = x_0 + A^H(u_j - u_0), \qquad r_j = r_j', \qquad p_j = A^H q_j.$$

So no vector of the $u$-iteration has to be formed. The symmetry of $M^{-1}$ moves it across the
inner products of lines 4 and 8. -/
theorem pcgne_eq (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : EuclideanSpace 𝕜 (Fin n))
    {u₀ : EuclideanSpace 𝕜 (Fin n)} (hu₀ : op Aᴴ u₀ = x₀) (j : ℕ) :
    (pcgne A M b x₀ j).x = x₀ + op Aᴴ (pcgX (A * Aᴴ) M b u₀ j - u₀) ∧
      (pcgne A M b x₀ j).r = pcgR (A * Aᴴ) M b u₀ j ∧
      (pcgne A M b x₀ j).p = op Aᴴ (pcgP (A * Aᴴ) M b u₀ j) := by
  have hres : b - op (A * Aᴴ) u₀ = b - op A x₀ := by rw [op_mul_apply, hu₀]
  induction j with
  | zero =>
    refine ⟨?_, hres.symm, ?_⟩
    · change x₀ = x₀ + op Aᴴ (u₀ - u₀)
      rw [sub_self, map_zero, add_zero]
    · change op Aᴴ (op M⁻¹ (b - op A x₀)) = op Aᴴ (op M⁻¹ (b - op (A * Aᴴ) u₀))
      rw [hres]
  | succ j ih =>
    obtain ⟨hx, hr, hp⟩ := ih
    have halpha : pcgneStepAlpha M (pcgne A M b x₀ j) = pcgAlpha (A * Aᴴ) M b u₀ j := by
      rw [pcgneStepAlpha, pcgAlpha_eq, pcgZ, hr, hp, inner_mul_conjTranspose_self,
        hMinv (pcgR (A * Aᴴ) M b u₀ j) (pcgR (A * Aᴴ) M b u₀ j)]
    have hrstep : pcgneStepR A M (pcgne A M b x₀ j) = pcgR (A * Aᴴ) M b u₀ (j + 1) := by
      rw [pcgneStepR, pcgR_succ, halpha, hr, hp, op_mul_apply]
    have hbeta : pcgneStepBeta A M (pcgne A M b x₀ j) = pcgBeta (A * Aᴴ) M b u₀ j := by
      rw [pcgneStepBeta, hrstep, hr, pcgBeta_eq, pcgZ, pcgZ,
        hMinv (pcgR (A * Aᴴ) M b u₀ (j + 1)) (pcgR (A * Aᴴ) M b u₀ (j + 1)),
        hMinv (pcgR (A * Aᴴ) M b u₀ j) (pcgR (A * Aᴴ) M b u₀ j)]
    refine ⟨?_, ?_, ?_⟩
    · rw [pcgne_succ, pcgneStep_x, pcgX_succ, hx, hp, halpha]
      simp only [map_sub, map_add, map_smul]
      abel
    · rw [pcgne_succ, pcgneStep_r]
      exact hrstep
    · rw [pcgne_succ, pcgneStep_p, pcgP_succ, pcgZ, hrstep, hbeta, hp, map_add, map_smul]

/-- Let $M^{-1}$ be symmetric and $A^H u_0 = x_0$. The iterate of Algorithm 9.8 is
$x_j = x_0 + A^H(u_j - u_0)$, where $u_j$ is the iterate of Algorithm 9.1 for $A A^H u = b$
started at $u_0$. -/
theorem pcgneX_eq (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : EuclideanSpace 𝕜 (Fin n))
    {u₀ : EuclideanSpace 𝕜 (Fin n)} (hu₀ : op Aᴴ u₀ = x₀) (j : ℕ) :
    (pcgne A M b x₀ j).x = x₀ + op Aᴴ (pcgX (A * Aᴴ) M b u₀ j - u₀) :=
  (pcgne_eq hMinv b x₀ hu₀ j).1

/-- **Section 9.5** of [saad2003iterative], optimality of Algorithm 9.8. Let $M$ be a
preconditioner, and let $A \in \mathbb{K}^{n \times n}$ satisfy $c\,(Mx, x) \le \|A^H x\|_2^2$
for all $x$, for some $c > 0$. Let $b, x_0 \in \mathbb{K}^n$, let $x_0 = A^H u_0$ for some
$u_0$, and let $A x_* = b$. Then for every $m$, the iterate $x_m$ of Algorithm 9.8 satisfies
$x_m - x_0 \in \mathcal{K}_m(A^H M^{-1} A, A^H M^{-1} r_0)$ and
$$\|x_* - x_m\|_2 \le \|x_* - x\|_2 \quad \text{for all } x \in x_0 + \mathcal{K}_m(A^H M^{-1}
  A, A^H M^{-1} r_0).$$

This space is not the one that Algorithm 9.7 searches: preconditioning separates the two normal
equations. Only at $M = I$ do $\mathcal{K}_m(M^{-1} A^H A, M^{-1} A^H r_0)$ and
$\mathcal{K}_m(A^H M^{-1} A, A^H M^{-1} r_0)$ coincide
(`SaadSparse.Chapter08.subspace_adjoint_eq`). -/
theorem pcgne_isMinError (hM : Krylov.IsPreconditioner (op M) (op M⁻¹)) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x : 𝔼, c * RCLike.re (inner 𝕜 (op M x) x) ≤ ‖op Aᴴ x‖ ^ 2)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) {u₀ xstar : EuclideanSpace 𝕜 (Fin n)}
    (hu₀ : op Aᴴ u₀ = x₀) (hstar : op A xstar = b) (m : ℕ) :
    IsMinError xstar x₀
        (Chapter06.krylov (Aᴴ * (M⁻¹ * A)) (op Aᴴ (op M⁻¹ (b - op A x₀))) m)
      (pcgne A M b x₀ m).x := by
  have hres : b - op (A * Aᴴ) u₀ = b - op A x₀ := by rw [op_mul_apply, hu₀]
  have hcoer' : ∀ x : 𝔼, c * RCLike.re (inner 𝕜 (op M x) x)
      ≤ RCLike.re (inner 𝕜 (op (A * Aᴴ) x) x) := fun x => by
    rw [op_mul, Krylov.inner_adjoint_comp_self
      (LinearMap.isAdjointPair_inner_iff.2 (Chapter07.inner_op_conjTranspose A)) x,
      RCLike.ofReal_re]
    exact hcoer x
  have h := pcg_isGalerkinIterate (A := A * Aᴴ) (M := M) hM (isSymmetric_mul_conjTranspose A)
    hc hcoer' b u₀ m
  rw [hres, op_mul] at h
  rw [pcgneX_eq hM.isSymmetric_inv b x₀ hu₀ m,
    ← map_krylov_conjTranspose A M (op M⁻¹ (b - op A x₀)) m]
  exact isMinError_of_isGalerkin_comp_adjoint A hu₀.symm hstar h

end CGNE

/-!
### Problem P-9.4: the right- and split-preconditioned CGNR and CGNE

The book leaves these four variants to Problem P-9.4 ("Right and split preconditioner versions of
Algorithms 9.7 and 9.8 are not shown here"). Each is the same method as the left-preconditioned one
after a change of variables, and Section 9.2 already proves the two rearrangements that do the work,
`SaadSparse.Chapter09.rightPcg_eq_pcg` and `SaadSparse.Chapter09.splitPcg_eq_pcg`. So no new
algorithm is needed. The algorithms are `SaadSparse.Chapter09.rightPcg` and
`SaadSparse.Chapter09.splitPcg` applied to the normal-equations matrices $A^H A$ and $A A^H$, and
each theorem below composes one of these two rearrangements with `SaadSparse.Chapter09.pcgnr_eq` or
`SaadSparse.Chapter09.pcgne_eq`.
-/

section Variants

variable {A M L : Matrix (Fin n) (Fin n) 𝕜}

/-- **Problem P-9.4** of [saad2003iterative], right-preconditioned CGNR. Let
$A, M \in \mathbb{K}^{n \times n}$ with $M^{-1}$ symmetric. Let $(u_j, \rho_j, q_j)$ be the
state of the conjugate gradient method for the right-preconditioned normal equations
$(A^H A) M^{-1} u = A^H b$ in the $M^{-1}$-inner product, started at $u_0$. Then, for all $j$,
$$(M^{-1} u_j, \; \rho_j, \; M^{-1} q_j) = (x_j, \; A^H r_j, \; p_j),$$
where $(x_j, r_j, p_j)$ is the state of Algorithm 9.7 started at $x_0 = M^{-1} u_0$.

The $M^{-1}$-inner product keeps $(A^H A) M^{-1}$ self-adjoint. So in the variable
$x = M^{-1} u$ the method is Algorithm 9.7, and the residual $\rho_j$ that it carries is the
normal-equations residual $A^H r_j$. -/
theorem rightPcgnr_eq (hMinv : (op M⁻¹).IsSymmetric) (b u₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    (op M⁻¹ (rightPcg (Aᴴ * A) M (op Aᴴ b) u₀ j).1,
        (rightPcg (Aᴴ * A) M (op Aᴴ b) u₀ j).2.1,
        op M⁻¹ (rightPcg (Aᴴ * A) M (op Aᴴ b) u₀ j).2.2)
      = ((pcgnr A M b (op M⁻¹ u₀) j).x, op Aᴴ (pcgnr A M b (op M⁻¹ u₀) j).r,
          (pcgnr A M b (op M⁻¹ u₀) j).p) :=
  (rightPcg_eq_pcg (isSymmetric_conjTranspose_mul A) hMinv (op Aᴴ b) u₀ j).trans
    (pcgnr_eq hMinv b (op M⁻¹ u₀) j).symm

/-- **Problem P-9.4** of [saad2003iterative], split-preconditioned CGNR. Let
$A, L \in \mathbb{K}^{n \times n}$ and $M = L L^H$, with $M^{-1}$ symmetric. Then for all
$b, x_0$ and $j$, the state of Algorithm 9.2 for the normal equations $A^H A x = A^H b$ with the
factor $L$ is
$$(x_j, \; L^{-1} A^H r_j, \; p_j),$$
where $(x_j, r_j, p_j)$ is the state of Algorithm 9.7 started at $x_0$.

Algorithm 9.2 runs the conjugate gradient method for $L^{-1} A^H A L^{-H} u = L^{-1} A^H b$ and
already carries out the change of variables $x = L^{-H} u$, so its first component is $x_j$ and
not $u_j$. The two algorithms have the same iterates and the same directions, and the split
residual $\hat r_j = L^{-1} A^H r_j$ replaces $A^H r_j$. -/
theorem splitPcgnr_eq (hMinv : (op M⁻¹).IsSymmetric) (hM : M = L * Lᴴ)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    splitPcg (Aᴴ * A) L (op Aᴴ b) x₀ j
      = ((pcgnr A M b x₀ j).x, op L⁻¹ (op Aᴴ (pcgnr A M b x₀ j).r), (pcgnr A M b x₀ j).p) := by
  rw [splitPcg_eq_pcg hM, ← pcgnr_eq hMinv]

/-- **Problem P-9.4** of [saad2003iterative], right-preconditioned CGNE. Let
$A, M \in \mathbb{K}^{n \times n}$ with $M^{-1}$ symmetric, and let $w_0$ satisfy
$A^H M^{-1} w_0 = x_0$. Let $(w_j, \rho_j, q_j)$ be the state of the conjugate gradient method
for $(A A^H) M^{-1} w = b$ in the $M^{-1}$-inner product, started at $w_0$. Then the state
$(x_j, r_j, p_j)$ of Algorithm 9.8 satisfies, for all $j$,
$$x_j = x_0 + A^H M^{-1}(w_j - w_0), \qquad r_j = \rho_j, \qquad p_j = A^H M^{-1} q_j.$$

Two changes of variables are combined: $u = M^{-1} w$ undoes the right preconditioning, and
$x = A^H u$ undoes the normal equations. -/
theorem rightPcgne_eq (hMinv : (op M⁻¹).IsSymmetric) (b x₀ : EuclideanSpace 𝕜 (Fin n))
    {w₀ : EuclideanSpace 𝕜 (Fin n)} (hw₀ : op Aᴴ (op M⁻¹ w₀) = x₀) (j : ℕ) :
    (pcgne A M b x₀ j).x
        = x₀ + op Aᴴ (op M⁻¹ ((rightPcg (A * Aᴴ) M b w₀ j).1 - w₀)) ∧
      (pcgne A M b x₀ j).r = (rightPcg (A * Aᴴ) M b w₀ j).2.1 ∧
      (pcgne A M b x₀ j).p = op Aᴴ (op M⁻¹ (rightPcg (A * Aᴴ) M b w₀ j).2.2) := by
  have h := rightPcg_eq_pcg (isSymmetric_mul_conjTranspose A) hMinv b w₀ j
  have h₁ : op M⁻¹ (rightPcg (A * Aᴴ) M b w₀ j).1 = pcgX (A * Aᴴ) M b (op M⁻¹ w₀) j :=
    congrArg Prod.fst h
  have h₂ : (rightPcg (A * Aᴴ) M b w₀ j).2.1 = pcgR (A * Aᴴ) M b (op M⁻¹ w₀) j :=
    congrArg (fun s => s.2.1) h
  have h₃ : op M⁻¹ (rightPcg (A * Aᴴ) M b w₀ j).2.2 = pcgP (A * Aᴴ) M b (op M⁻¹ w₀) j :=
    congrArg (fun s => s.2.2) h
  obtain ⟨hx, hr, hp⟩ := pcgne_eq hMinv b x₀ hw₀ j
  refine ⟨?_, ?_, ?_⟩
  · have hsub : op M⁻¹ ((rightPcg (A * Aᴴ) M b w₀ j).1 - w₀)
        = pcgX (A * Aᴴ) M b (op M⁻¹ w₀) j - op M⁻¹ w₀ := by rw [map_sub, h₁]
    rw [hsub]; exact hx
  · rw [hr]; exact h₂.symm
  · rw [h₃]; exact hp

/-- **Problem P-9.4** of [saad2003iterative], split-preconditioned CGNE. Let
$A, L \in \mathbb{K}^{n \times n}$ and $M = L L^H$, with $M^{-1}$ symmetric, and let $u_0$
satisfy $A^H u_0 = x_0$. Let $(u_j, \hat r_j, q_j)$ be the state of Algorithm 9.2 for
$A A^H u = b$ with the factor $L$, started at $u_0$. Then the state $(x_j, r_j, p_j)$ of
Algorithm 9.8 satisfies, for all $j$,
$$x_j = x_0 + A^H(u_j - u_0), \qquad L^{-1} r_j = \hat r_j, \qquad p_j = A^H q_j.$$

Algorithm 9.2 runs the conjugate gradient method for $L^{-1} A A^H L^{-H} v = L^{-1} b$ and
carries out the change of variables $u = L^{-H} v$, so its first component is $u_j$. The
remaining change of variables $x = A^H u$ gives the iterate of Algorithm 9.8. -/
theorem splitPcgne_eq (hMinv : (op M⁻¹).IsSymmetric) (hM : M = L * Lᴴ)
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) {u₀ : EuclideanSpace 𝕜 (Fin n)} (hu₀ : op Aᴴ u₀ = x₀)
    (j : ℕ) :
    (pcgne A M b x₀ j).x = x₀ + op Aᴴ ((splitPcg (A * Aᴴ) L b u₀ j).1 - u₀) ∧
      op L⁻¹ (pcgne A M b x₀ j).r = (splitPcg (A * Aᴴ) L b u₀ j).2.1 ∧
      (pcgne A M b x₀ j).p = op Aᴴ (splitPcg (A * Aᴴ) L b u₀ j).2.2 := by
  have h := splitPcg_eq_pcg (A := A * Aᴴ) (L := L) hM b u₀ j
  have h₁ : (splitPcg (A * Aᴴ) L b u₀ j).1 = pcgX (A * Aᴴ) M b u₀ j := by rw [h]; rfl
  have h₂ : (splitPcg (A * Aᴴ) L b u₀ j).2.1 = op L⁻¹ (pcgR (A * Aᴴ) M b u₀ j) := by rw [h]; rfl
  have h₃ : (splitPcg (A * Aᴴ) L b u₀ j).2.2 = pcgP (A * Aᴴ) M b u₀ j := by rw [h]; rfl
  obtain ⟨hx, hr, hp⟩ := pcgne_eq hMinv b x₀ hu₀ j
  exact ⟨by rw [h₁]; exact hx, by rw [h₂, hr], by rw [h₃]; exact hp⟩

end Variants

/-!
### Problem P-9.5: the centred variants

Problem P-9.5 of [saad2003iterative] replaces the two one-sided systems of Section 9.5 by the
centred systems $A M^{-1} A^H u = b$ with $x = M^{-1} A^H u$ (the NE form) and
$A^H M^{-1} A x = A^H M^{-1} b$ (the NR form). It observes that "the coefficient matrices in the
above systems are all symmetric", and asks for the adapted conjugate gradient algorithms. These are
not rearrangements of Algorithm 9.1: $A^H M^{-1} A$ is a different matrix from $M^{-1} A^H A$. Its
Krylov space $\mathcal{K}_m(A^H M^{-1} A, A^H M^{-1} r_0)$ is the space of Algorithm 9.8, and it
differs from the space $\mathcal{K}_m(M^{-1} A^H A, M^{-1} A^H r_0)$ of Algorithm 9.7 in general
when $M \neq I$.
-/

/-- **Problem P-9.5** of [saad2003iterative], symmetry of the centred NR matrix. Let
$A, M \in \mathbb{K}^{n \times n}$ with $M^{-1}$ symmetric. Then $A^H M^{-1} A$ is symmetric,
for every $A$. It is the coefficient matrix of the centred NR system
$A^H M^{-1} A x = A^H M^{-1} b$. -/
theorem isSymmetric_centredNR (A : Matrix (Fin n) (Fin n) 𝕜) {M : Matrix (Fin n) (Fin n) 𝕜}
    (hMinv : (op M⁻¹).IsSymmetric) : (op (Aᴴ * (M⁻¹ * A))).IsSymmetric := by
  intro x y
  simp only [op_mul_apply]
  rw [Chapter08.inner_op_conjTranspose, hMinv, Chapter07.inner_op_conjTranspose]

/-- **Problem P-9.5** of [saad2003iterative], symmetry of the centred NE matrix. Let
$A, M \in \mathbb{K}^{n \times n}$ with $M^{-1}$ symmetric. Then $A M^{-1} A^H$ is symmetric. It
is the coefficient matrix of the centred NE system $A M^{-1} A^H u = b$. -/
theorem isSymmetric_centredNE (A : Matrix (Fin n) (Fin n) 𝕜) {M : Matrix (Fin n) (Fin n) 𝕜}
    (hMinv : (op M⁻¹).IsSymmetric) : (op (A * (M⁻¹ * Aᴴ))).IsSymmetric := by
  intro x y
  simp only [op_mul_apply]
  rw [Chapter07.inner_op_conjTranspose, hMinv, Chapter08.inner_op_conjTranspose]

/-- **Problem P-9.5** of [saad2003iterative], the product in the centred NR step. For
$A, M \in \mathbb{K}^{n \times n}$ and $y \in \mathbb{K}^n$,
$$A^H M^{-1} A y = A^H (M^{-1} (A y)).$$
So the product is one product with $A$, one solve with $M$ and one product with $A^H$; neither
$A^H M^{-1} A$ nor $M^{-1}$ is formed. -/
theorem op_centredNR_apply (A M : Matrix (Fin n) (Fin n) 𝕜) (y : EuclideanSpace 𝕜 (Fin n)) :
    op (Aᴴ * (M⁻¹ * A)) y = op Aᴴ (op M⁻¹ (op A y)) := by
  rw [op_mul_apply, op_mul_apply]

/-- **Problem P-9.5** of [saad2003iterative], the product in the centred NE step. For
$A, M \in \mathbb{K}^{n \times n}$ and $y \in \mathbb{K}^n$,
$$A M^{-1} A^H y = A (M^{-1} (A^H y)).$$
So the product is one product with $A^H$, one solve with $M$ and one product with $A$. -/
theorem op_centredNE_apply (A M : Matrix (Fin n) (Fin n) 𝕜) (y : EuclideanSpace 𝕜 (Fin n)) :
    op (A * (M⁻¹ * Aᴴ)) y = op A (op M⁻¹ (op Aᴴ y)) := by
  rw [op_mul_apply, op_mul_apply]

section Centred

variable (A M : Matrix (Fin n) (Fin n) 𝕜)

/-- **Problem P-9.5** of [saad2003iterative], the centred CGNR. Let
$A, M \in \mathbb{K}^{n \times n}$ and $b, x_0 \in \mathbb{K}^n$. The centred CGNR is the
conjugate gradient method for $A^H M^{-1} A x = A^H M^{-1} b$ started at $x_0$; its value at $j$
is the state after $j$ steps.

The coefficient matrix is symmetric (`SaadSparse.Chapter09.isSymmetric_centredNR`), so the
conjugate gradient recurrence applies unchanged. The adaptation is that the matrix-vector
product of each step is the three operations of `SaadSparse.Chapter09.op_centredNR_apply`. The
unknown is $x$ itself, so no change of variables is needed. The recurrence is the backbone
`CG.iterate`. -/
noncomputable def centredPcgnr (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) : CG.State 𝔼 :=
  CG.iterate (op (Aᴴ * (M⁻¹ * A))) (op Aᴴ (op M⁻¹ b)) x₀ j

/-- **Problem P-9.5** of [saad2003iterative], the centred CGNE. Let
$A, M \in \mathbb{K}^{n \times n}$ and $b, u_0 \in \mathbb{K}^n$. The centred CGNE is the
conjugate gradient method for $A M^{-1} A^H u = b$ started at $u_0$; its value at $j$ is the
state after $j$ steps.

The coefficient matrix is symmetric (`SaadSparse.Chapter09.isSymmetric_centredNE`), and the
matrix-vector product of each step is the three operations of
`SaadSparse.Chapter09.op_centredNE_apply`. The solution of $Ax = b$ is recovered by the change
of variables $x = M^{-1} A^H u$ (`SaadSparse.Chapter09.centredPcgneX`). -/
noncomputable def centredPcgne (b u₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) : CG.State 𝔼 :=
  CG.iterate (op (A * (M⁻¹ * Aᴴ))) b u₀ j

/-- **Problem P-9.5** of [saad2003iterative], the change of variables $x = M^{-1} A^H u$ of the
centred CGNE. For $b, u_0, x_0 \in \mathbb{K}^n$ the iterate is
$$x_j = x_0 + M^{-1} A^H (u_j - u_0),$$
where $u_j$ is the iterate of the centred CGNE started at $u_0$. This incremental form keeps
$x_0$ as given. -/
noncomputable def centredPcgneX (b u₀ x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) : 𝔼 :=
  x₀ + op M⁻¹ (op Aᴴ ((centredPcgne A M b u₀ j).x - u₀))

/-- **Problem P-9.5** of [saad2003iterative], the residual of the centred CGNR. For all $b, x_0$ and
$j$, the residual carried by the centred CGNR is the preconditioned normal-equations residual
$$r_j = A^H M^{-1} (b - A x_j).$$

So the true residual $b - A x_j$ is not available without extra work. This is the cost of
centring, and one reason why the book prints Algorithm 9.7. -/
theorem centredPcgnr_residual_eq (b x₀ : EuclideanSpace 𝕜 (Fin n)) (j : ℕ) :
    (centredPcgnr A M b x₀ j).r
      = op Aᴴ (op M⁻¹ (b - op A (centredPcgnr A M b x₀ j).x)) := by
  rw [centredPcgnr, CG.residual_eq, op_centredNR_apply, map_sub, map_sub]

/-- **Problem P-9.5** of [saad2003iterative], the centred CGNE read in $x$. Let
$b, u_0, x_0 \in \mathbb{K}^n$ with $x_0 = M^{-1} A^H u_0$, and let $u_j$ and $\rho_j$ be the
iterate and the residual of the centred CGNE started at $u_0$. Then the iterate $x_j$ of
`SaadSparse.Chapter09.centredPcgneX` satisfies, for all $j$,
$$x_j = x_0 + M^{-1} A^H (u_j - u_0), \qquad A x_j = (A M^{-1} A^H) u_j, \qquad \rho_j = b - A
  x_j.$$
So the residual carried by the $u$-iteration is the true residual of $Ax = b$.

This is for the centred system what `SaadSparse.Chapter09.pcgne_eq` is for $A A^H u = b$. -/
theorem centredPcgne_eq (b u₀ x₀ : EuclideanSpace 𝕜 (Fin n)) (hx₀ : op M⁻¹ (op Aᴴ u₀) = x₀)
    (j : ℕ) :
    centredPcgneX A M b u₀ x₀ j = x₀ + op M⁻¹ (op Aᴴ ((centredPcgne A M b u₀ j).x - u₀)) ∧
      op A (centredPcgneX A M b u₀ x₀ j) = op (A * (M⁻¹ * Aᴴ)) (centredPcgne A M b u₀ j).x ∧
      (centredPcgne A M b u₀ j).r = b - op A (centredPcgneX A M b u₀ x₀ j) := by
  have hdef : centredPcgneX A M b u₀ x₀ j
      = x₀ + op M⁻¹ (op Aᴴ ((centredPcgne A M b u₀ j).x - u₀)) := rfl
  have happ : op A (centredPcgneX A M b u₀ x₀ j)
      = op (A * (M⁻¹ * Aᴴ)) (centredPcgne A M b u₀ j).x := by
    rw [hdef, ← hx₀, op_centredNE_apply, map_add, map_sub, map_sub, map_sub]
    abel
  exact ⟨hdef, happ, by rw [happ, centredPcgne, CG.residual_eq]⟩

end Centred

/-- **Problem P-9.5** of [saad2003iterative], positive definiteness of the centred NR matrix. Let
$A, M \in \mathbb{K}^{n \times n}$, let $A$ be nonsingular, and let $M^{-1}$ be symmetric
positive definite. Then $A^H M^{-1} A$ is symmetric positive definite, since
$(A^H M^{-1} A x, x) = (M^{-1} A x, A x) > 0$ for $x \neq 0$.

This is the hypothesis under which the centred NR system is well posed and the conjugate
gradient method for it applies. In Lean, "nonsingular" is the injectivity of the operator of
$A$, and "symmetric positive definite" is `LinearMap.IsSymmetricCoercive`. -/
theorem isSymmetricCoercive_centredNR {A M : Matrix (Fin n) (Fin n) 𝕜}
    (hMinv : (op M⁻¹).IsSymmetricCoercive) (hA : Function.Injective (op A)) :
    (op (Aᴴ * (M⁻¹ * A))).IsSymmetricCoercive where
  isSymmetric := isSymmetric_centredNR A hMinv.isSymmetric
  isCoercive := (LinearMap.isCoercive_iff_forall_pos _).2 fun x hx => by
    rw [op_centredNR_apply, Chapter08.inner_op_conjTranspose]
    exact LinearMap.IsCoercive.inner_self_pos hMinv.isCoercive
      fun h => hx (hA (by rw [h, map_zero]))

/-- **Problem P-9.5** of [saad2003iterative], optimality of the centred CGNR. Let
$A, M \in \mathbb{K}^{n \times n}$, let $A$ be nonsingular, and let $M^{-1}$ be symmetric
positive definite. Then for all $b, x_0$ and $m$, the iterate $x_m$ of the centred CGNR is the
Galerkin iterate of $A^H M^{-1} A x = A^H M^{-1} b$ over $x_0 + \mathcal{K}_m(A^H M^{-1} A, A^H
M^{-1} r_0)$, with $r_0 = b - A x_0$.

Hence $x_m$ minimizes the $A^H M^{-1} A$-norm of the error over that space. The space is the one
of Algorithm 9.8, not of Algorithm 9.7. -/
theorem centredPcgnr_isGalerkinIterate {A M : Matrix (Fin n) (Fin n) 𝕜}
    (hMinv : (op M⁻¹).IsSymmetricCoercive) (hA : Function.Injective (op A))
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) :
    IsGalerkin (op (Aᴴ * (M⁻¹ * A))) (op Aᴴ (op M⁻¹ b)) x₀
        (Chapter06.krylov (Aᴴ * (M⁻¹ * A)) (op Aᴴ (op M⁻¹ (b - op A x₀))) m)
      (centredPcgnr A M b x₀ m).x := by
  have hinit : op Aᴴ (op M⁻¹ b) - op (Aᴴ * (M⁻¹ * A)) x₀ = op Aᴴ (op M⁻¹ (b - op A x₀)) := by
    rw [op_centredNR_apply, map_sub, map_sub]
  have h := CG.isGalerkinIterate (op Aᴴ (op M⁻¹ b)) x₀
    (isSymmetricCoercive_centredNR hMinv hA) m
  rw [Chapter06.krylov_eq, ← hinit]
  exact h

end SaadSparse.Chapter09
