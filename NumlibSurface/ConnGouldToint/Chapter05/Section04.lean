/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.Preconditioned
import NumlibSurface.ConnGouldToint.Chapter04.Section04

/-!
# Conn, Gould and Toint, Section 5.4: Problems with linear constraints

This module formalizes Section 5.4 of [conn2000trust]. Let $E$ and $F$ be real Hilbert spaces, let
$H : E \to E$ be linear, $c \in E$, and let the constraint $Ax = 0$ have its null space parametrized
as the range of a bounded linear map $N : F \to E$. Then the constrained quadratic problem
$$\min_x \ \tfrac{1}{2} \langle x, Hx \rangle + \langle c, x \rangle \quad \text{subject to} \quad
  Ax = 0$$
is equivalent to the unconstrained reduced problem in $F$ with the Hessian $N^* H N$ and the
gradient $N^* c$ (5.4.1)–(5.4.2). Algorithm 5.4.1 applies preconditioned conjugate gradients to the
reduced problem with a preconditioner $B$. Algorithm 5.4.2 runs the same method in $E$ with the
projected preconditioner $N B N^*$, and the two algorithms agree state by state. The section also
shows that $N B N^*$ solves the augmented system (5.4.5) and that a constrained minimizer satisfies
the augmented system (5.4.6).

The proofs specialize the PCG method of the backbone module `Numlib.Krylov.Preconditioned`.

## Main definitions

* Algorithm 5.4.2, `ConnGouldToint.Chapter05.projectedPCG`: preconditioned conjugate gradients in
  $E$ with the preconditioner $N B N^*$.

## Main results

* Equations (5.4.1)–(5.4.2), `ConnGouldToint.Chapter05.null_space_quadratic_5_4_2`: the reduced
  objective equals the original objective on the range of $N$, and the reduced minimizers give the
  feasible minimizers.
* Algorithms 5.4.1–5.4.2, `ConnGouldToint.Chapter05.algorithm_5_4_2_eq_reduced`: the projected and
  the reduced iterations agree after mapping by $N$ and $N^*$.
* Algorithm 5.4.2, `ConnGouldToint.Chapter05.projectedPCG_feasible`: the projected iterates,
  directions and preconditioned residuals lie in the null space of $A$.
* Equation (5.4.5), `ConnGouldToint.Chapter05.projected_inverse_5_4_5`: the projected preconditioned
  residual solves the augmented system.
* Equation (5.4.6), `ConnGouldToint.Chapter05.constrained_quadratic_system_5_4_6`: a constrained
  minimizer satisfies the augmented system.
* Equation (5.4.7), `ConnGouldToint.Chapter05.shifted_projected_system_5_4_7`: a shift of the
  right-hand side by $A^* y$ shifts the multiplier by $y$.

## Conventions

* The backbone PCG state carries the residual $b - Hx$. For the system $Hx = -c$ this is
  $-(Hx + c)$, the negative of the gradient $Hx + c$ that the source uses.

## Deviations from the source

* **Algorithms 5.4.1–5.4.2 and (5.4.1)–(5.4.7)** (generalization). The projected iterations
  use Hilbert-space maps and an explicit reduced inverse. The null-space reduction only
  assumes that the parametrization has the prescribed range. The augmented system (5.4.5)
  uses finite-dimensional spaces for the constraint map and allows a right inverse of the
  reduced operator.
-/

namespace ConnGouldToint.Chapter05

open Krylov
open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Algorithm 5.4.2** of [conn2000trust]. Let $E$ and $F$ be real Hilbert spaces, let
$H : E \to E$ and $B : F \to F$ be linear, let $N : F \to E$ be bounded linear, and let
$c \in E$ and $u_0 \in F$. The **projected preconditioned conjugate gradient method** is the
preconditioned conjugate gradient method for $Hx = -c$ from $x_0 = N u_0$, with the projected
preconditioner $N B N^*$ in place of the inverse preconditioner. Its $k$-th state consists of
the iterate $x_k$, the residual $-(Hx_k + c)$ and the search direction $p_k$.

The state is `Krylov.PCG.iterate`. The map $B$ stands for the inverse of the reduced
preconditioner.

**Reading.** Uses abstract projected inverse on Hilbert spaces and the backbone residual sign.
-/
noncomputable abbrev projectedPCG (H : E →ₗ[ℝ] E) (N : F →L[ℝ] E) (B : F →ₗ[ℝ] F)
    (c : E) (u₀ : F) (k : ℕ) : PCG.State E :=
  PCG.iterate H (N.toLinearMap ∘ₗ B ∘ₗ N.adjoint.toLinearMap) (-c) (N u₀) k

/-- **Algorithms 5.4.1–5.4.2** of [conn2000trust]. Let $E$, $F$, $H$, $N$, $B$, $c$ and $u_0$ be as
in `ConnGouldToint.Chapter05.projectedPCG`. Let $(u_k, s_k, d_k)$ be the states of the reduced
method, Algorithm 5.4.1: preconditioned conjugate gradients for $N^* H N u = -N^* c$ from $u_0$
with the inverse preconditioner $B$. Let $(x_k, r_k, p_k)$ be the states of Algorithm 5.4.2.
Then for every $k$
$$x_k = N u_k, \qquad N^* r_k = s_k, \qquad p_k = N d_k.$$

**Reading.** State-by-state projection identity for Hilbert-space maps at all indices.
-/
theorem algorithm_5_4_2_eq_reduced (H : E →ₗ[ℝ] E) (N : F →L[ℝ] E) (B : F →ₗ[ℝ] F)
    (c : E) (u₀ : F) (k : ℕ) :
    let HN := N.adjoint.toLinearMap ∘ₗ H ∘ₗ N.toLinearMap
    let s := PCG.iterate HN B (-(N.adjoint c)) u₀ k
    let t := projectedPCG H N B c u₀ k
    t.x = N s.x ∧ N.adjoint t.r = s.r ∧ t.p = N s.p := by
  let HN := N.adjoint.toLinearMap ∘ₗ H ∘ₗ N.toLinearMap
  let P := N.toLinearMap ∘ₗ B ∘ₗ N.adjoint.toLinearMap
  let S := PCG.iterate HN B (-(N.adjoint c)) u₀
  let T := PCG.iterate H P (-c) (N u₀)
  change (T k).x = N (S k).x ∧ N.adjoint (T k).r = (S k).r ∧ (T k).p = N (S k).p
  have hp (z : E) : P z = N (B (N.adjoint z)) := rfl
  have hhn (z : F) : HN z = N.adjoint (H (N z)) := rfl
  have hn (z : E) : ⟪z, P z⟫ = ⟪N.adjoint z, B (N.adjoint z)⟫ := by
    rw [hp, N.adjoint_inner_left]
  induction k with
  | zero =>
    have hr : N.adjoint (T 0).r = (S 0).r := by
      change N.adjoint (-c - H (N u₀)) = -(N.adjoint c) - HN u₀
      rw [map_sub, map_neg, hhn]
    exact ⟨rfl, hr, by
      change P ((T 0).r) = N (B (S 0).r)
      rw [hp, hr]⟩
  | succ k ih =>
    obtain ⟨hx, hr, hp'⟩ := ih
    have ha : PCG.alpha H P (T k) = PCG.alpha HN B (S k) := by
      rw [PCG.alpha, PCG.alpha, hn, hr, hp', hhn, N.adjoint_inner_left]
    have hr' : N.adjoint (T (k + 1)).r = (S (k + 1)).r := by
      simp only [T, S, PCG.iterate_succ, PCG.step_r]
      change N.adjoint ((T k).r - PCG.alpha H P (T k) • H (T k).p) =
        (S k).r - PCG.alpha HN B (S k) • HN (S k).p
      rw [map_sub, map_smul, ha, hr, hp', hhn]
    have ht : PCG.step H P (T k) = T (k + 1) := (PCG.iterate_succ H P (-c) (N u₀) k).symm
    have hs : PCG.step HN B (S k) = S (k + 1) :=
      (PCG.iterate_succ HN B (-(N.adjoint c)) u₀ k).symm
    have hb : PCG.beta H P (T k) = PCG.beta HN B (S k) := by
      simp only [PCG.beta, hn, ht, hs]
      change ⟪N.adjoint (T (k + 1)).r, B (N.adjoint (T (k + 1)).r)⟫ /
        ⟪N.adjoint (T k).r, B (N.adjoint (T k).r)⟫ =
        ⟪(S (k + 1)).r, B (S (k + 1)).r⟫ / ⟪(S k).r, B (S k).r⟫
      rw [hr', hr]
    refine ⟨?_, hr', ?_⟩
    · simp only [T, S, PCG.iterate_succ, PCG.step_x]
      change (T k).x + PCG.alpha H P (T k) • (T k).p =
        N ((S k).x + PCG.alpha HN B (S k) • (S k).p)
      rw [hx, ha, hp', map_add, map_smul]
    · rw [← ht, ← hs, PCG.step_p, PCG.step_p, ht, hs]
      change P (T (k + 1)).r + PCG.beta H P (T k) • (T k).p =
        N (B (S (k + 1)).r + PCG.beta HN B (S k) • (S k).p)
      rw [hp, hr', hb, hp', map_add, map_smul]

/-- **Equation (5.4.5)** of [conn2000trust]. Let $E$, $F$ and $Y$ be real Hilbert spaces, with $E$
and $Y$ finite-dimensional. Let $A : E \to Y$ and $N : F \to E$ be bounded linear maps with
$\operatorname{range} N = \ker A$, and let $M : E \to E$ and $B : F \to F$ be linear with
$N^* M N B z = z$ for all $z \in F$. Then for every $g \in E$ the vector $v = N B N^* g$
satisfies
$$Av = 0 \quad \text{and} \quad Mv + A^* w = g \text{ for some } w \in Y,$$
that is, $(v, w)$ solves the augmented system with the matrix
$\begin{bmatrix} M & A^* \\ A & 0 \end{bmatrix}$ and the right-hand side $(g, 0)$.

The hypothesis on $B$ says that $B$ is a right inverse of the reduced preconditioner $N^* M N$.

**Reading.** Augmented solve from a specified right inverse and exact kernel range.
-/
theorem projected_inverse_5_4_5 {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] [FiniteDimensional ℝ E] [FiniteDimensional ℝ Y]
    (A : E →L[ℝ] Y) (N : F →L[ℝ] E) (M : E →ₗ[ℝ] E) (B : F →ₗ[ℝ] F)
    (hN : LinearMap.range N.toLinearMap = LinearMap.ker A.toLinearMap)
    (hB : ∀ z : F, N.adjoint (M (N (B z))) = z) (g : E) :
    let v := N (B (N.adjoint g))
    A v = 0 ∧ ∃ w : Y, M v + A.adjoint w = g := by
  intro v
  have hv : v ∈ LinearMap.range N.toLinearMap := ⟨B (N.adjoint g), rfl⟩
  rw [hN] at hv
  refine ⟨hv, ?_⟩
  have ho : g - M v ∈ (LinearMap.ker A.toLinearMap)ᗮ := by
    rw [← hN, Submodule.mem_orthogonal]
    rintro _ ⟨d, rfl⟩
    change ⟪N d, g - M v⟫ = 0
    rw [← N.adjoint_inner_right, map_sub]
    change ⟪d, N.adjoint g - N.adjoint (M (N (B (N.adjoint g))))⟫ = 0
    rw [hB, sub_self, inner_zero_right]
  rw [LinearMap.orthogonal_ker] at ho
  obtain ⟨w, hw⟩ := ho
  exact ⟨w, eq_sub_iff_add_eq'.mp hw⟩

/-- **Equation (5.4.7)** of [conn2000trust]. Let $E$ and $Y$ be real Hilbert spaces, let
$A : E \to Y$ be bounded linear and $M : E \to E$ linear, and let $g, v \in E$ and $u, y \in Y$.
Then
$$Av = 0 \text{ and } Mv + A^*(y + u) = g \iff Av = 0 \text{ and } Mv + A^* u = g - A^* y.$$

Thus a shift of the right-hand side by $A^* y$ keeps the primal component $v$ and shifts the
multiplier by $y$.

**Reading.** Same shift identity with Hilbert-space adjoint.
-/
theorem shifted_projected_system_5_4_7 {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (A : E →L[ℝ] Y) (M : E →ₗ[ℝ] E) (g v : E) (u y : Y) :
    (A v = 0 ∧ M v + A.adjoint (y + u) = g) ↔
      (A v = 0 ∧ M v + A.adjoint u = g - A.adjoint y) := by
  rw [map_add, and_congr_right_iff]
  intro _
  rw [eq_sub_iff_add_eq]
  abel_nf


/-- **Equations (5.4.1)–(5.4.2)** of [conn2000trust]. Let $E$ and $F$ be real Hilbert spaces, let
$Y$ be a real vector space, let $A : E \to Y$ and $H : E \to E$ be linear, and let $N : F \to E$
be bounded linear with $\operatorname{range} N = \ker A$. Let $c \in E$, and let
$$q(x) = \tfrac{1}{2} \langle x, Hx \rangle + \langle c, x \rangle, \qquad q_N(z) = \tfrac{1}{2}
  \langle z, N^* H N z \rangle + \langle N^* c, z \rangle.$$
Then for every $u \in F$, $q(Nu) = q_N(u)$, and $u$ minimizes $q_N$ over $F$ if and only if $Nu$
minimizes $q$ over $\ker A$.

**Reading.** Parametrization can be any map with range equal to the kernel.
-/
theorem null_space_quadratic_5_4_2 {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (A : E →ₗ[ℝ] Y) (H : E →ₗ[ℝ] E) (N : F →L[ℝ] E) (c : E)
    (hN : LinearMap.range N.toLinearMap = LinearMap.ker A) (u : F) :
    let q (x : E) := (1 / 2 : ℝ) * ⟪x, H x⟫ + ⟪c, x⟫
    let qN (z : F) := (1 / 2 : ℝ) * ⟪z, N.adjoint (H (N z))⟫ + ⟪N.adjoint c, z⟫
    q (N u) = qN u ∧ (IsMinOn qN Set.univ u ↔ IsMinOn q (LinearMap.ker A) (N u)) := by
  intro q qN
  have hq (z : F) : q (N z) = qN z := by
    change (1 / 2 : ℝ) * ⟪N z, H (N z)⟫ + ⟪c, N z⟫ =
      (1 / 2 : ℝ) * ⟪z, N.adjoint (H (N z))⟫ + ⟪N.adjoint c, z⟫
    rw [N.adjoint_inner_right, N.adjoint_inner_left]
  refine ⟨hq u, ?_⟩
  constructor
  · intro h x hx
    rw [← hN] at hx
    obtain ⟨z, rfl⟩ := hx
    change q (N u) ≤ q (N z)
    rw [hq, hq]
    exact h (Set.mem_univ z)
  · intro h z _
    have hz : N z ∈ LinearMap.ker A := hN ▸ ⟨z, rfl⟩
    change qN u ≤ qN z
    rw [← hq, ← hq]
    exact h hz

/-- **Algorithm 5.4.2** of [conn2000trust], feasibility. Let $E$, $F$, $H$, $N$, $B$, $c$ and $u_0$
be as in `ConnGouldToint.Chapter05.projectedPCG`, let $Y$ be a real vector space, and let
$A : E \to Y$ be linear with $A N u = 0$ for all $u \in F$. Then for every $k$ the iterate
$x_k$, the direction $p_k$ and the preconditioned residual $N B N^* r_k$ of Algorithm 5.4.2 lie
in the null space of $A$.

**Reading.** Feasibility from range inclusion alone, in abstract spaces.
-/
theorem projectedPCG_feasible {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (A : E →ₗ[ℝ] Y) (H : E →ₗ[ℝ] E) (N : F →L[ℝ] E) (B : F →ₗ[ℝ] F)
    (hN : ∀ u, A (N u) = 0) (c : E) (u₀ : F) (k : ℕ) :
    let t := projectedPCG H N B c u₀ k
    A t.x = 0 ∧ A t.p = 0 ∧ A (N (B (N.adjoint t.r))) = 0 := by
  intro t
  obtain ⟨hx, _, hp⟩ := algorithm_5_4_2_eq_reduced H N B c u₀ k
  exact ⟨hx ▸ hN _, hp ▸ hN _, hN _⟩

open scoped Matrix

/-- **Equation (5.4.6)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$ be symmetric,
$A \in \mathbb{R}^{m \times n}$ and $c \in \mathbb{R}^n$. If $x$ minimizes
$\frac{1}{2} z^T H z + c^T z$ subject to $Az = 0$, then there is $y \in \mathbb{R}^m$ with
$$\begin{bmatrix} H & A^T \\ A & 0 \end{bmatrix} \begin{bmatrix} x \\ -y \end{bmatrix} =
  \begin{bmatrix} -c \\ 0 \end{bmatrix}.$$

The minimizer is `ConnGouldToint.Chapter04.IsEqualityQuadraticMin H A (-c) x 0`. -/
theorem constrained_quadratic_system_5_4_6 {m n : ℕ}
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (c x : Fin n → ℝ)
    (hmin : Chapter04.IsEqualityQuadraticMin H A (-c) x 0) :
    ∃ y : Fin m → ℝ, Matrix.saddleMatrix H Aᵀ 0 *ᵥ Sum.elim x (-y) = Sum.elim (-c) 0 := by
  obtain ⟨hx, ⟨y, hy⟩, _⟩ := (Chapter04.quadratic_minimum_4_4_14_iff hH A (-c) x 0).mp hmin
  exact ⟨y, (Chapter04.projection_system_4_4_8 H A x (-c) y 0).mpr ⟨hy, hx⟩⟩

end ConnGouldToint.Chapter05
