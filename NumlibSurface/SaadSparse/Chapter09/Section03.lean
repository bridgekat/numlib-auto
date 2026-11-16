/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Preconditioned
import NumlibSurface.SaadSparse.Chapter06.Section05
import NumlibSurface.SaadSparse.Chapter09.Section02

/-!
# Saad, Section 9.3: Preconditioned GMRES

This module formalizes Section 9.3 of [saad2003iterative], with Problems P-9.11 and P-9.13. Both
preconditioned algorithms are GMRES (Algorithm 6.9) for another matrix. Algorithm 9.4, with left
preconditioning, is GMRES for $M^{-1} A x = M^{-1} b$, so it minimizes the preconditioned residual
$\|M^{-1}(b - Ax)\|_2$ over $x_0 + \mathcal{K}_m(M^{-1} A, M^{-1} r_0)$. Algorithm 9.5, with right
preconditioning, is GMRES for $A M^{-1} u = b$ started at $u_0 = M x_0$, with the iterate returned
as $x_m = x_0 + M^{-1} V_m y_m$. It minimizes the true residual $\|b - Ax\|_2$ over the same affine
space. The two search spaces agree because of (9.18), $s(M^{-1} A) M^{-1} r = M^{-1} s(A M^{-1}) r$
for every polynomial $s$. Proposition 9.1 gives the resulting common form $x_m = x_0 + s(M^{-1} A)
z_0 = x_0 + M^{-1} s(A M^{-1}) r_0$ with $\deg s < m$.

Section 9.3.1 also sketches GMRES in the $M$-inner product $(x, y)_M = (Mx, y)$ for a symmetric
positive definite $M$ and a nonsymmetric $A$ (Problem P-9.13). This method minimizes the
$M^{-1}$-norm of the true residual over the same preconditioned Krylov space. By (9.12) and
(9.14)–(9.15), every $M$-inner product that it forms is a Euclidean inner product of vectors that it
has already computed, so it needs no extra product with $M$. The proofs use the GMRES of
`NumlibSurface.SaadSparse.Chapter06.Section05` and the preconditioning layer
`Numlib.Krylov.Preconditioned`.

## Main definitions

* Algorithm 9.4, `SaadSparse.Chapter09.gmresLeft`: GMRES with left preconditioning.
* Algorithm 9.5, `SaadSparse.Chapter09.gmresRight`: GMRES with right preconditioning.
* Problem P-9.13, `SaadSparse.Chapter09.IsGMRESEnergyIterate`: the GMRES approximation of
  $M^{-1} A x = M^{-1} b$ computed in the $M$-inner product.

## Main results

* Algorithm 9.5, `SaadSparse.Chapter09.gmresRight_eq`: the iterate $x_0 + M^{-1} V_m y_m$ is
  $M^{-1} u_m$.
* Algorithm 9.4, `SaadSparse.Chapter09.gmresLeft_isMinResidual`: Algorithm 9.4 minimizes
  $\|M^{-1}(b - Ax)\|_2$ over $x_0 + \mathcal{K}_m(M^{-1} A, M^{-1} r_0)$.
* Algorithm 9.5, `SaadSparse.Chapter09.gmresRight_isMinResidual`: Algorithm 9.5 minimizes
  $\|b - Ax\|_2$ over the same affine space.
* Equation (9.18) and Problem P-9.11, `SaadSparse.Chapter09.equation_9_18`:
  $s(M^{-1} A) M^{-1} r = M^{-1} s(A M^{-1}) r$, and $M^{-1} \mathcal{K}_m(A M^{-1}, r) =
  \mathcal{K}_m(M^{-1} A, M^{-1} r)$.
* Proposition 9.1, `SaadSparse.Chapter09.proposition_9_1`: the preconditioned GMRES approximation
  has the form $x_0 + s(M^{-1} A) z_0 = x_0 + M^{-1} s(A M^{-1}) r_0$ with $\deg s < m$.
* Problem P-9.13, `SaadSparse.Chapter09.isGMRESEnergyIterate_iff`: GMRES in the $M$-inner product
  minimizes the $M^{-1}$-norm of the true residual over $x_0 + \mathcal{K}_m(M^{-1} A, M^{-1} r_0)$.
* Equations (9.12) and (9.14)–(9.15), `SaadSparse.Chapter09.equation_9_12`: the $M$-inner products
  of that method are Euclidean inner products of computed vectors.

## Implementation notes

* Split preconditioning (Section 9.3.3) is Algorithm 9.5 with $M = M_L M_R$, so it has no
  declaration of its own.
* GMRES is `SaadSparse.Chapter06.gmresFixed`, which runs exactly $m$ Arnoldi steps. The optimality
  results therefore assume $m \le$ the grade of the initial vector, and that the preconditioned
  matrix is nonsingular.
* GMRES in the $M$-inner product is the backbone GMRES specification `Krylov.IsMinResidualIterate`
  on the space with the $M$-inner product, `Krylov.IsPreconditioner.EnergySpace`.
-/

open Matrix Polynomial

open scoped SaadSparse

namespace SaadSparse.Chapter09

open Chapter06 (op)

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

local notation "𝔼" => EuclideanSpace 𝕜 (Fin n)

variable {A M : Matrix (Fin n) (Fin n) 𝕜}

/-! ### Algorithms 9.4 and 9.5 -/

/-- **Algorithm 9.4** of [saad2003iterative] (GMRES with left preconditioning). Let
$M, A \in \mathbb{K}^{n \times n}$, $b, x_0 \in \mathbb{K}^n$ and $m \in \mathbb{N}$. The
approximation $x_m$ is the result of $m$ steps of GMRES (Algorithm 6.9) for the matrix
$M^{-1} A$ with right-hand side $M^{-1} b$, started at $x_0$.

The Arnoldi basis spans $\mathcal{K}_m(M^{-1} A, M^{-1} r_0)$, and the residual that the
algorithm monitors is the preconditioned residual $M^{-1}(b - A x_m)$. GMRES is
`SaadSparse.Chapter06.gmresFixed`. -/
noncomputable def gmresLeft (M A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))
    (m : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  Chapter06.gmresFixed (leftPreconditioned M A) (op M⁻¹ b) x₀ m

/-- **Algorithm 9.5** of [saad2003iterative] (GMRES with right preconditioning). Let
$M, A \in \mathbb{K}^{n \times n}$, $b, x_0 \in \mathbb{K}^n$ and $m \in \mathbb{N}$. Let
$u_m = M x_0 + V_m y_m$ be the result of $m$ steps of GMRES (Algorithm 6.9) for the matrix
$A M^{-1}$ with right-hand side $b$, started at $u_0 = M x_0$. The approximation is
$$x_m = x_0 + M^{-1} (u_m - M x_0) = x_0 + M^{-1} V_m y_m.$$

The variable $u$ does not appear in the printed algorithm, and the residual that it monitors is
the true residual $b - A x_m$. With $M = M_L M_R$ this is the split-preconditioned algorithm of
Section 9.3.3. -/
noncomputable def gmresRight (M A : Matrix (Fin n) (Fin n) 𝕜) (b x₀ : EuclideanSpace 𝕜 (Fin n))
    (m : ℕ) : EuclideanSpace 𝕜 (Fin n) :=
  x₀ + op M⁻¹ (Chapter06.gmresFixed (rightPreconditioned M A) b (op M x₀) m - op M x₀)

/-- For a nonsingular matrix $M$, $M^{-1}(Mx) = x$. -/
private theorem inv_apply_apply' (hM : IsUnit M) (x : EuclideanSpace 𝕜 (Fin n)) :
    op M⁻¹ (op M x) = x := by
  have h1 : (op (1 : Matrix (Fin n) (Fin n) 𝕜)) = LinearMap.id := Matrix.toEuclideanLin_one
  rw [← op_mul_apply, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det M).1 hM), h1,
    LinearMap.id_apply]

/-- **Algorithm 9.5** of [saad2003iterative], the two forms of the iterate. Let $M$ be nonsingular.
Then the approximation $x_m = x_0 + M^{-1} V_m y_m$ of Algorithm 9.5 is $x_m = M^{-1} u_m$,
where $u_m$ is the GMRES approximation of $A M^{-1} u = b$ started at $u_0 = M x_0$. -/
theorem gmresRight_eq (hM : IsUnit M) (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) :
    gmresRight M A b x₀ m
      = op M⁻¹ (Chapter06.gmresFixed (rightPreconditioned M A) b (op M x₀) m) := by
  rw [gmresRight, map_sub, inv_apply_apply' hM]
  abel

/-- **Algorithm 9.4** of [saad2003iterative], optimality. Let $M, A \in \mathbb{K}^{n \times n}$
with $M^{-1} A$ nonsingular, and let $b, x_0 \in \mathbb{K}^n$. Let $m$ be at most the grade of
$v_1 = M^{-1} r_0 / \|M^{-1} r_0\|$ with respect to $M^{-1} A$, where $r_0 = b - A x_0$. Then
the approximation $x_m$ of Algorithm 9.4 satisfies $x_m - x_0 \in \mathcal{K}_m(M^{-1} A, M^{-1}
r_0)$ and
$$\|M^{-1}(b - A x_m)\|_2 \le \|M^{-1}(b - A x)\|_2 \quad \text{for all } x \in x_0 +
  \mathcal{K}_m(M^{-1} A, M^{-1} r_0).$$

That is, $x_m$ is the minimal-residual Krylov iterate of $M^{-1} A x = M^{-1} b$,
`Krylov.IsMinResidualIterate`. -/
theorem gmresLeft_isMinResidual (b x₀ : EuclideanSpace 𝕜 (Fin n)) {m : ℕ}
    (hMA : IsUnit (leftPreconditioned M A))
    (hm : m ≤ Chapter06.grade (leftPreconditioned M A)
      (Chapter06.v₁ (leftPreconditioned M A) (op M⁻¹ b) x₀)) :
    Krylov.IsMinResidualIterate (op (leftPreconditioned M A)) (op M⁻¹ b) x₀ m
      (gmresLeft M A b x₀ m) :=
  Chapter06.gmresFixed_isMinResidualIterate _ _ _ hm (Chapter06.isUnit_R_of_isUnit _ _ _ hMA hm)

/-- **Algorithm 9.5** of [saad2003iterative], optimality. Let $M, A \in \mathbb{K}^{n \times n}$
with $M$ and $A M^{-1}$ nonsingular, and let $b, x_0 \in \mathbb{K}^n$. Let $m$ be at most the
grade of $v_1 = r_0 / \|r_0\|$ with respect to $A M^{-1}$, where $r_0 = b - A x_0$. Then the
approximation $x_m$ of Algorithm 9.5 satisfies $x_m - x_0 \in \mathcal{K}_m(M^{-1} A, M^{-1}
r_0)$ and
$$\|b - A x_m\|_2 \le \|b - A x\|_2 \quad \text{for all } x \in x_0 + \mathcal{K}_m(M^{-1} A,
  M^{-1} r_0).$$

The affine space is the one that Algorithm 9.4 searches. This is the difference between left and
right preconditioning: the space is the same, but the norm that is minimized over it is not. -/
theorem gmresRight_isMinResidual (b x₀ : EuclideanSpace 𝕜 (Fin n)) {m : ℕ} (hM : IsUnit M)
    (hAM : IsUnit (rightPreconditioned M A))
    (hm : m ≤ Chapter06.grade (rightPreconditioned M A)
      (Chapter06.v₁ (rightPreconditioned M A) b (op M x₀))) :
    IsMinResidual (op A) b x₀
      (Krylov.subspace (op M⁻¹ ∘ₗ op A) (op M⁻¹ (b - op A x₀)) m) (gmresRight M A b x₀ m) := by
  have hu := Chapter06.gmresFixed_isMinResidualIterate (rightPreconditioned M A) b (op M x₀) hm
    (Chapter06.isUnit_R_of_isUnit _ _ _ hAM hm)
  rw [show op (rightPreconditioned M A) = op A ∘ₗ op M⁻¹ from op_mul A M⁻¹] at hu
  rw [gmresRight_eq hM]
  exact Krylov.isMinResidual_of_isMinResidualIterate_rightPreconditioned
    (inv_apply_apply' hM x₀).symm hu

/-! ### Equation (9.18) and Proposition 9.1 -/

/-- For linear maps $B, C$ and a polynomial $p$, $B \, p(CB) = p(BC) \, B$. -/
private theorem semiconjBy_aeval {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    (B C : Module.End 𝕜 E) (p : 𝕜[X]) :
    SemiconjBy B (aeval (C * B) p) (aeval (B * C) p) := by
  refine Polynomial.induction_on' p (fun q r hq hr => ?_) fun k a => ?_
  · simpa only [map_add] using hq.add_right hr
  · rw [aeval_monomial, aeval_monomial]
    exact SemiconjBy.mul_right (Algebra.commutes a B).symm
      (SemiconjBy.pow_right (mul_assoc B C B).symm k)

/-- **Equation (9.18)** and **Problem P-9.11** of [saad2003iterative]. Let
$M, A \in \mathbb{K}^{n \times n}$, let $s$ be a polynomial, $r \in \mathbb{K}^n$ and
$m \in \mathbb{N}$. Then
$$s(M^{-1} A) \, M^{-1} r = M^{-1} s(A M^{-1}) \, r,$$
and hence
$$M^{-1} \mathcal{K}_m(A M^{-1}, r) = \mathcal{K}_m(M^{-1} A, M^{-1} r).$$
So the preconditioned Krylov spaces (9.17) and (9.20) of the left- and right-preconditioned
algorithms are the same space.

No invertibility of $M$ is needed. The Krylov subspaces are the backbone `Krylov.subspace`. -/
theorem equation_9_18 (s : 𝕜[X]) (r : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) :
    aeval (op (leftPreconditioned M A)) s (op M⁻¹ r)
        = op M⁻¹ (aeval (op (rightPreconditioned M A)) s r)
      ∧ Submodule.map (op M⁻¹) (Krylov.subspace (op (rightPreconditioned M A)) r m)
          = Krylov.subspace (op (leftPreconditioned M A)) (op M⁻¹ r) m := by
  have hL : op (leftPreconditioned M A) = op M⁻¹ * op A := op_mul M⁻¹ A
  have hR : op (rightPreconditioned M A) = op A * op M⁻¹ := op_mul A M⁻¹
  refine ⟨?_, ?_⟩
  · have h : op M⁻¹ * aeval (op A * op M⁻¹) s = aeval (op M⁻¹ * op A) s * op M⁻¹ :=
      semiconjBy_aeval (op M⁻¹) (op A) s
    rw [hL, hR]
    exact (congrArg (fun T : Module.End 𝕜 (EuclideanSpace 𝕜 (Fin n)) => T r) h).symm
  · rw [hL, hR]
    exact Krylov.map_subspace_comp (op A) (op M⁻¹) r m

/-- **Proposition 9.1** of [saad2003iterative]. Let $M, A \in \mathbb{K}^{n \times n}$,
$b, x_0 \in \mathbb{K}^n$, $r_0 = b - A x_0$ and $z_0 = M^{-1} r_0$. If $x$ is the
minimal-residual Krylov iterate of $M^{-1} A x = M^{-1} b$ at step $m$, then there is a
polynomial $s$ with $\deg s < m$ such that
$$x = x_0 + s(M^{-1} A) z_0 = x_0 + M^{-1} s(A M^{-1}) r_0.$$

Which polynomial $s$ arises depends on the side of the preconditioning. On the right it
minimizes $\|b - A x_m\|_2$ (`SaadSparse.Chapter09.gmresRight_isMinResidual`), and on the left
$\|M^{-1}(b - A x_m)\|_2$ (`SaadSparse.Chapter09.gmresLeft_isMinResidual`). The statement takes
the iterate as the left-preconditioned minimal-residual iterate `Krylov.IsMinResidualIterate`;
the form $x_0 + s(M^{-1} A) z_0$ uses only that $x - x_0$ lies in the Krylov space. -/
theorem proposition_9_1 {b x₀ : EuclideanSpace 𝕜 (Fin n)} {m : ℕ}
    {x : EuclideanSpace 𝕜 (Fin n)}
    (hx : Krylov.IsMinResidualIterate (op (leftPreconditioned M A)) (op M⁻¹ b) x₀ m x) :
    ∃ s : 𝕜[X], s.degree < m ∧
      x = x₀ + aeval (op (leftPreconditioned M A)) s (op M⁻¹ (b - op A x₀)) ∧
      x = x₀ + op M⁻¹ (aeval (op (rightPreconditioned M A)) s (b - op A x₀)) := by
  have hL : op (leftPreconditioned M A) = op M⁻¹ ∘ₗ op A := op_mul M⁻¹ A
  rw [hL] at hx
  have hb : op M⁻¹ b = op M⁻¹ b := rfl
  obtain ⟨s, hs, hxs⟩ :=
    Krylov.exists_aeval_of_isMinResidualIterate_preconditioned (b := b) (hb ▸ hx)
  refine ⟨s, hs, by rw [hL]; exact hxs, ?_⟩
  rw [hxs, ← hL, (equation_9_18 (A := A) (M := M) s (b - op A x₀) m).1]

/-! ### Section 9.3.1 and Problem P-9.13: GMRES in the $M$-inner product -/

/-- **Problem P-9.13** of [saad2003iterative]. Let $A \in \mathbb{K}^{n \times n}$, let $M$ be a
preconditioner (symmetric positive definite, with inverse $M^{-1}$), and let
$b, x_0, x \in \mathbb{K}^n$. Then $x$ is the **GMRES approximation at step $m$ in the $M$-inner
product** of $M^{-1} A x = M^{-1} b$ if it is the minimal-residual Krylov iterate at step $m$ of
this system on the space $\mathbb{K}^n$ with the inner product $(x, y)_M = (Mx, y)$. The matrix
$A$ need not be symmetric.

This is the Arnoldi process and GMRES of the backbone run in the space with the $M$-inner
product, which is the modified Gram–Schmidt process of (9.10)–(9.11). The definition is
`Krylov.IsMinResidualIterate` for `hM.energyEnd (op M⁻¹ ∘ₗ op A)`, with each vector moved to
that space by `hM.toEnergy`. -/
def IsGMRESEnergyIterate (A : Matrix (Fin n) (Fin n) 𝕜)
    {M : Matrix (Fin n) (Fin n) 𝕜} (hM : Krylov.IsPreconditioner (op M) (op M⁻¹))
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) : Prop :=
  Krylov.IsMinResidualIterate (hM.energyEnd (op M⁻¹ ∘ₗ op A)) (hM.toEnergy (op M⁻¹ b))
    (hM.toEnergy x₀) m (hM.toEnergy x)

/-- **Problem P-9.13** of [saad2003iterative], optimality. Let $M$ be a preconditioner,
$A \in \mathbb{K}^{n \times n}$, $b, x_0, x \in \mathbb{K}^n$ and $r_0 = b - A x_0$. Then $x$ is
the GMRES approximation at step $m$ in the $M$-inner product if and only if $x - x_0 \in
\mathcal{K}_m(M^{-1} A, M^{-1} r_0)$ and
$$\|M^{-1}(b - Ax)\|_M \le \|M^{-1}(b - Ay)\|_M \quad \text{for all } y \in x_0 +
  \mathcal{K}_m(M^{-1} A, M^{-1} r_0).$$

The space is the one that Algorithms 9.4 and 9.5 search. The $M$-norm of the preconditioned
residual is the $M^{-1}$-norm of the true residual $b - Ax$. The norm $\|\cdot\|_M$ is
`energyNorm (op M)`. -/
theorem isGMRESEnergyIterate_iff (hM : Krylov.IsPreconditioner (op M) (op M⁻¹))
    (b x₀ : EuclideanSpace 𝕜 (Fin n)) (m : ℕ) (x : EuclideanSpace 𝕜 (Fin n)) :
    IsGMRESEnergyIterate A hM b x₀ m x ↔
      (x - x₀ ∈ Krylov.subspace (op M⁻¹ ∘ₗ op A) (op M⁻¹ (b - op A x₀)) m ∧
        ∀ y, y - x₀ ∈ Krylov.subspace (op M⁻¹ ∘ₗ op A) (op M⁻¹ (b - op A x₀)) m →
          energyNorm (op M) (op M⁻¹ (b - op A x))
            ≤ energyNorm (op M) (op M⁻¹ (b - op A y))) := by
  have hres : hM.toEnergy (op M⁻¹ b) - hM.energyEnd (op M⁻¹ ∘ₗ op A) (hM.toEnergy x₀)
      = hM.toEnergy (op M⁻¹ (b - op A x₀)) := by
    rw [Krylov.IsPreconditioner.energyEnd_apply, LinearMap.comp_apply, ← map_sub, ← map_sub]
  have h := hM.isMinResidual_energyEnd_iff (op A) b x₀
    (Krylov.subspace (op M⁻¹ ∘ₗ op A) (op M⁻¹ (b - op A x₀)) m) x
  rw [← Krylov.IsPreconditioner.subspace_energyEnd, ← hres] at h
  exact h

/-- **Equations (9.12)** and **(9.14)–(9.15)** of [saad2003iterative]. Let $M$ be a preconditioner
and $v, w \in \mathbb{K}^n$, and put $z = M^{-1} w$. Then
$$(z, v)_M = (w, v), \qquad \|z\|_M = (z, w)^{1/2}.$$
So every $M$-inner product that GMRES in the $M$-inner product forms is a Euclidean inner
product of vectors that it has already computed, and no extra product with $M$ is needed.

With $w = A v_j$ these give the coefficients $h_{ij}$ and the subdiagonal entry $h_{j+1,j}$ of
the $M$-orthogonal Arnoldi process. In Lean the first identity is
`energyInner (op M) (op M⁻¹ w) v = inner 𝕜 w v`, and the second takes the real part of the inner
product. -/
theorem equation_9_12 (hM : Krylov.IsPreconditioner (op M) (op M⁻¹))
    (v w : EuclideanSpace 𝕜 (Fin n)) :
    energyInner (op M) (op M⁻¹ w) v = inner 𝕜 w v ∧
      energyNorm (op M) (op M⁻¹ w) = Real.sqrt (RCLike.re (inner 𝕜 w (op M⁻¹ w))) := by
  refine ⟨by rw [energyInner, hM.apply_inv], by rw [energyNorm, hM.apply_inv]⟩

end SaadSparse.Chapter09
