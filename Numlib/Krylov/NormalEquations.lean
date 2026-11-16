/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.CG
import Numlib.Krylov.Convergence.CG

/-!
# Krylov methods on the normal equations: CGNR and CGNE

Let $E$ and $F$ be inner product spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let
$A : E \to F$ be linear, and let $A^* : F \to E$ satisfy $\langle A^* u, v \rangle = \langle u, Av
\rangle$ for all $u \in F$, $v \in E$. A system $Ax = b$ that is not symmetric can be solved by a
symmetric Krylov method in two ways ([saad2003iterative], §8.3, Algorithms 8.4 and 8.5). CGNR is CG
on the normal equations $A^* A x = A^* b$. CGNE, or Craig's method, is CG on $A A^* u = b$ with
$x = A^* u$. The operator may be rectangular, as in [golub2013matrix], §11.3.9 and Figure 11.3.1:
CGNR is the normal-equation method for full-rank least squares, and CGNE is the method for
consistent underdetermined systems.

This file introduces no new algorithm. It proves the two optimality properties of
[saad2003iterative], §8.3, for the specifications of `Numlib.Krylov.Iterate` applied to $A^* A$ on
the Krylov space $\mathcal{K}_m(A^* A, A^* r_0)$, with $r_0 = b - A x_0$. Read in the original
variables, a Galerkin iterate of CGNR minimizes the residual $\|b - Ax\|$, and the CGNE iterate
minimizes the error $\|x^* - x\|$, both over $x_0 + \mathcal{K}_m(A^* A, A^* r_0)$. Every
convergence theorem for CG then applies with the spectrum of $A^* A$, that is with $\kappa(A)^2$ in
place of $\kappa(A)$. The file also defines the two recurrences as a program writes them, with one
application of $A$ and one of $A^*$ per step, and identifies them with the corresponding CG
iterates.

## Main definitions

* `Krylov.CGNR.iterate`: the CGNR recurrence, [saad2003iterative], Algorithm 8.4.
* `Krylov.CGNE.iterate`: the CGNE (Craig) recurrence, [saad2003iterative], Algorithm 8.5.

## Main results

* `Krylov.energyNorm_adjoint_comp`: $\|x\|_{A^* A} = \|Ax\|$.
* `Krylov.adjoint_comp_isSymmetricCoercive`: $A^* A$ is symmetric coercive when $A$ is bounded
  below.
* `Krylov.isGalerkinIterate_adjoint_comp_iff_isMinResidual`: a Galerkin iterate of the normal
  equations is a minimal-residual iterate of $Ax = b$ (the optimality of CGNR).
* `Krylov.isMinError_of_isGalerkinIterate_comp_adjoint`: the CGNE iterate minimizes the error (the
  optimality of CGNE).
* `Krylov.IsMinResidual.norm_residual_le_of_adjoint_comp`: the CG convergence bound for CGNR, with
  $\kappa = \sigma_{\max} / \sigma_{\min}$.
* `Krylov.CGNR.iterate_eq`, `Krylov.CGNE.iterate_eq`: the two recurrences compute the CG iterates of
  $A^* A$ and of $A A^*$.

## Implementation notes

* The map $A^*$ is a hypothesis, not `LinearMap.adjoint A`: the pair $(A, A^*)$ satisfies
  `LinearMap.IsAdjointPair` of the flipped `innerₛₗ`, which is $\langle A^* u, v \rangle = \langle
  u, Av \rangle$ by `LinearMap.isAdjointPair_inner_iff`. Therefore the file needs neither finite
  dimension nor completeness. Where the adjoint exists, Mathlib's `LinearMap.isAdjointPair_inner`
  supplies the hypothesis. In the Lean code $A^*$ is `Astar`, and $A^* A$ is `Astar ∘ₗ A`.
* The energy norm is $\|x\|_B = \sqrt{\operatorname{Re} \langle Bx, x \rangle}$ (`energyNorm`).
-/

open Krylov

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace Krylov

section Adjoint

variable {A : E →ₗ[𝕜] F} {Astar : F →ₗ[𝕜] E}

variable (hadj : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A Astar)
include hadj

/-- Let $A^*$ be an adjoint of $A$. For every $x \in E$, $\langle A^* A x, x \rangle = \|Ax\|^2$.

This identity turns every statement about the energy norm of $A^* A$ into a statement about the
norm of the residual of $A$. -/
theorem inner_adjoint_comp_self (x : E) :
    inner 𝕜 ((Astar ∘ₗ A) x) x = ((‖A x‖ ^ 2 : ℝ) : 𝕜) := by
  rw [LinearMap.comp_apply, hadj.inner_apply_eq, inner_self_eq_norm_sq_to_K]
  push_cast
  ring

/-- Let $A^*$ be an adjoint of $A$. For every $x \in E$, the energy norm of $A^* A$ is the norm of
the image under $A$: $\|x\|_{A^* A} = \|Ax\|$. -/
theorem energyNorm_adjoint_comp (x : E) : energyNorm (Astar ∘ₗ A) x = ‖A x‖ := by
  rw [energyNorm, inner_adjoint_comp_self hadj, RCLike.ofReal_re]
  exact Real.sqrt_sq (norm_nonneg _)

/-- Let $A^*$ be an adjoint of $A$. Then $A^* A$ is symmetric, for every $A$. -/
theorem adjoint_comp_isSymmetric : (Astar ∘ₗ A).IsSymmetric := by
  intro x y
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hadj.inner_apply_eq,
    ← LinearMap.inner_apply_eq_inner_apply_of_adjoint hadj]

/-- Let $A^*$ be an adjoint of $A$, and let $c \in \mathbb{R}$ satisfy $c \|x\|^2 \le \|Ax\|^2$ for
all $x \in E$. Then $c \|x\|^2 \le \operatorname{Re} \langle A^* A x, x \rangle$ for all $x$,
that is, $A^* A$ is coercive with the constant $c$. -/
theorem adjoint_comp_isCoerciveWith {c : ℝ} (hc : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2) :
    (Astar ∘ₗ A).IsCoerciveWith c := by
  intro x
  rw [inner_adjoint_comp_self hadj, RCLike.ofReal_re]
  exact hc x

/-- Let $A^*$ be an adjoint of $A$, and let $\sigma_{\min}, \sigma_{\max} \in \mathbb{R}$ satisfy
$$\sigma_{\min}^2 \|x\|^2 \le \|Ax\|^2 \le \sigma_{\max}^2 \|x\|^2$$
for all $x \in E$. Then $A^* A$ is symmetric, and its quadratic form satisfies $\sigma_{\min}^2
\|x\|^2 \le \operatorname{Re} \langle A^* A x, x \rangle \le \sigma_{\max}^2 \|x\|^2$.

Thus bounds on the singular values of $A$ become bounds on the quadratic form of $A^* A$
(`LinearMap.IsSymmetricBoundedBy`), which is the form in which the Chebyshev convergence theory
uses them. -/
theorem adjoint_comp_isSymmetricBoundedBy {smin smax : ℝ}
    (hmin : ∀ x : E, smin ^ 2 * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2)
    (hmax : ∀ x : E, ‖A x‖ ^ 2 ≤ smax ^ 2 * ‖x‖ ^ 2) :
    (Astar ∘ₗ A).IsSymmetricBoundedBy (smin ^ 2) (smax ^ 2) where
  isSymmetric := adjoint_comp_isSymmetric hadj
  le_re_inner x := by rw [inner_adjoint_comp_self hadj, RCLike.ofReal_re]; exact hmin x
  re_inner_le x := by rw [inner_adjoint_comp_self hadj, RCLike.ofReal_re]; exact hmax x

/-- Let $A^*$ be an adjoint of $A$, and let $c > 0$ satisfy $c \|x\| \le \|Ax\|$ for all $x \in E$.
Then $A^* A$ is symmetric coercive.

This is the hypothesis under which the normal equations are a well-posed symmetric positive
definite system, and hence under which CGNR and CGNE are well defined. -/
theorem adjoint_comp_isSymmetricCoercive {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : E, c * ‖x‖ ≤ ‖A x‖) : (Astar ∘ₗ A).IsSymmetricCoercive where
  isSymmetric := adjoint_comp_isSymmetric hadj
  isCoercive := ⟨c ^ 2, by positivity, adjoint_comp_isCoerciveWith hadj fun x => by
    have h := hbound x
    have h0 : 0 ≤ c * ‖x‖ := by positivity
    nlinarith [norm_nonneg (A x)]⟩

/-- Let $E$ be finite-dimensional, let $A^*$ be an adjoint of $A$, and let $A$ be injective. Then
$A^* A$ is symmetric coercive.

The quadratic form $\langle A^* A x, x \rangle = \|Ax\|^2$ is positive for $x \neq 0$, and
compactness of the unit sphere supplies the constant (`LinearMap.isCoercive_iff_forall_pos`). -/
theorem adjoint_comp_isSymmetricCoercive_of_injective [FiniteDimensional 𝕜 E]
    (hinj : Function.Injective A) : (Astar ∘ₗ A).IsSymmetricCoercive where
  isSymmetric := adjoint_comp_isSymmetric hadj
  isCoercive := (LinearMap.isCoercive_iff_forall_pos _).2 fun x hx => by
    rw [inner_adjoint_comp_self hadj, RCLike.ofReal_re]
    have : A x ≠ 0 := fun h => hx (hinj (by rw [h, map_zero]))
    positivity

end Adjoint

section Optimality

variable {A : E →ₗ[𝕜] F} {Astar : F →ₗ[𝕜] E}
  (hadj : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A Astar) (b : F) (x₀ : E)
include hadj

omit hadj in
/-- For every $b \in F$ and $x_0 \in E$, the initial residual of the normal equations is the image
of the initial residual of $Ax = b$:
$$A^* b - A^* A x_0 = A^* (b - A x_0).$$
-/
theorem adjoint_residual : Astar b - (Astar ∘ₗ A) x₀ = Astar (b - A x₀) :=
  (Astar.map_sub b (A x₀)).symm

/-- Let $A^*$ be an adjoint of $A$, let $b \in F$, $x_0 \in E$, $m \in \mathbb{N}$, and let
$r_0 = b - A x_0$. A point $x \in E$ is a Galerkin iterate at step $m$ for the normal equations
$A^* A x = A^* b$ from $x_0$ if and only if $x$ minimizes $\|b - Ax\|$ over
$x_0 + \mathcal{K}_m(A^* A, A^* r_0)$. This is the optimality of CGNR, [saad2003iterative],
§8.3.1.

Both sides say that $b - Ax$ is orthogonal to $A \mathcal{K}_m(A^* A, A^* r_0)$. On the left
this holds because the residual of the normal equations is $A^*(b - Ax)$, and on the right by
`IsMinResidual.iff_isPetrovGalerkin`. -/
theorem isGalerkinIterate_adjoint_comp_iff_isMinResidual (m : ℕ) (x : E) :
    IsGalerkinIterate (Astar ∘ₗ A) (Astar b) x₀ m x ↔
      IsMinResidual A b x₀ (subspace (Astar ∘ₗ A) (Astar (b - A x₀)) m) x := by
  rw [IsMinResidual.iff_isPetrovGalerkin]
  constructor <;> rintro ⟨hmem, horth⟩
  · rw [adjoint_residual (A := A) (Astar := Astar) b x₀] at hmem
    refine ⟨hmem, (Submodule.mem_orthogonal _ _).2 ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have h := (Submodule.mem_orthogonal _ _).1 horth w
      (by rwa [adjoint_residual (A := A) (Astar := Astar) b x₀])
    rwa [LinearMap.comp_apply, ← map_sub,
      ← LinearMap.inner_apply_eq_inner_apply_of_adjoint hadj] at h
  · rw [← adjoint_residual (A := A) (Astar := Astar) b x₀] at hmem
    refine ⟨hmem, (Submodule.mem_orthogonal _ _).2 fun w hw => ?_⟩
    rw [adjoint_residual (A := A) (Astar := Astar) b x₀] at hw
    have h := (Submodule.mem_orthogonal _ _).1 horth (A w) (Submodule.mem_map_of_mem hw)
    rwa [LinearMap.comp_apply, ← map_sub, ← LinearMap.inner_apply_eq_inner_apply_of_adjoint hadj]

/-- Let $A^*$ be an adjoint of $A$, let $b \in F$, let $x^* \in E$ satisfy $A x^* = b$, and let
$x_0 = A^* u_0$ for some $u_0 \in F$. Let $r_0 = b - A x_0$. If $u$ is a Galerkin iterate at
step $m$ for $A A^* u = b$ from $u_0$, then the point $x = x_0 + A^*(u - u_0)$ minimizes the
error $\|x^* - y\|$ over $y \in x_0 + \mathcal{K}_m(A^* A, A^* r_0)$. This is the optimality of
CGNE, [saad2003iterative], §8.3.2. CGNR minimizes the residual over the same affine space.

The conclusion is `IsMinError` over $\mathcal{K}_m(A^* A, A^* r_0)$, not
`Krylov.IsMinErrorIterate (Astar ∘ₗ A) xstar x₀ m x`. That specification is the one of SYMMLQ:
for an operator $B$ it minimizes over $x_0 + B \mathcal{K}_m(B, B(x^* - x_0))$, which for
$B = A^* A$ is $x_0 + \mathcal{K}_m(A^* A, A^* A A^* r_0)$, because $B(x^* - x_0) = A^* r_0$.
This space has one more factor $A^* A$ than the space that CGNE searches. -/
theorem isMinError_of_isGalerkinIterate_comp_adjoint {u₀ u : F} {xstar : E} {m : ℕ}
    (hx₀ : x₀ = Astar u₀) (hstar : A xstar = b)
    (hu : IsGalerkinIterate (A ∘ₗ Astar) b u₀ m u) :
    IsMinError xstar x₀ (subspace (Astar ∘ₗ A) (Astar (b - A x₀)) m)
      (x₀ + Astar (u - u₀)) := by
  have hres : b - (A ∘ₗ Astar) u₀ = b - A x₀ := by rw [LinearMap.comp_apply, hx₀]
  have hmem : u - u₀ ∈ subspace (A ∘ₗ Astar) (b - A x₀) m := by
    have h := hu.mem; rwa [hres] at h
  have horth : b - (A ∘ₗ Astar) u ∈ (subspace (A ∘ₗ Astar) (b - A x₀) m)ᗮ := by
    have h := hu.orth; rwa [hres] at h
  -- the transported Krylov space: `Aᴴ 𝒦_m(A Aᴴ, r₀) = 𝒦_m(Aᴴ A, Aᴴ r₀)`
  have hmap := map_subspace_comp A Astar (b - A x₀) m
  rw [← hmap]
  refine ⟨by rw [add_sub_cancel_left]; exact Submodule.mem_map_of_mem hmem, fun y hy => ?_⟩
  rw [show xstar - (x₀ + Astar (u - u₀)) = (xstar - x₀) - Astar (u - u₀) by abel,
    show xstar - y = (xstar - x₀) - (y - x₀) by abel]
  refine Submodule.norm_sub_le_of_forall_inner_eq_zero (Submodule.mem_map_of_mem hmem) ?_ hy
  rintro _ ⟨z, hz, rfl⟩
  have h1 : A (Astar (u - u₀)) = (A ∘ₗ Astar) u - (A ∘ₗ Astar) u₀ := by
    rw [← LinearMap.comp_apply]
    exact map_sub _ _ _
  have h2 : A x₀ = (A ∘ₗ Astar) u₀ := by rw [hx₀, LinearMap.comp_apply]
  have h3 : A ((xstar - x₀) - Astar (u - u₀)) = (A xstar - A x₀) - A (Astar (u - u₀)) := by
    rw [map_sub, map_sub]
  have hA : A ((xstar - x₀) - Astar (u - u₀)) = b - (A ∘ₗ Astar) u := by
    rw [h3, hstar, h1, h2]; abel
  rw [← LinearMap.inner_apply_eq_inner_apply_of_adjoint hadj, hA, ← inner_conj_symm,
    (Submodule.mem_orthogonal _ _).1 horth z hz, map_zero]

end Optimality

section Convergence

variable {A : E →ₗ[𝕜] F} {Astar : F →ₗ[𝕜] E}
  (hadj : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A Astar)
include hadj

/-- Let $A^*$ be an adjoint of $A$, let $0 < \sigma_{\min} \le \sigma_{\max}$, and let the quadratic
form of $A^* A$ satisfy $\sigma_{\min}^2 \|x\|^2 \le \operatorname{Re} \langle A^* A x, x
\rangle \le \sigma_{\max}^2 \|x\|^2$ for all $x$. Let $A x^* = b$, and let $x$ minimize
$\|b - Ax\|$ over $x_0 + \mathcal{K}_m(A^* A, A^* (b - A x_0))$. Then, with
$\kappa = \sigma_{\max} / \sigma_{\min}$,
$$\|b - Ax\| \le 2 \left( \frac{\kappa - 1}{\kappa + 1} \right)^m \|b - A x_0\|.$$
This is the CG convergence bound transported to CGNR.

The condition number of $A^* A$ is $\kappa^2$. This squaring is the cost of the normal
equations, and it is the reason that CGNR is slow on an ill-conditioned system. -/
theorem IsMinResidual.norm_residual_le_of_adjoint_comp {smin smax : ℝ} (hs : 0 < smin)
    (hss : smin ≤ smax) (hB : (Astar ∘ₗ A).IsSymmetricBoundedBy (smin ^ 2) (smax ^ 2))
    {b : F} {x₀ : E} {m : ℕ} {x xstar : E} (hstar : A xstar = b)
    (hx : IsMinResidual A b x₀ (subspace (Astar ∘ₗ A) (Astar (b - A x₀)) m) x) :
    ‖b - A x‖ ≤ 2 * ((smax / smin - 1) / (smax / smin + 1)) ^ m * ‖b - A x₀‖ := by
  have hgal : IsGalerkinIterate (Astar ∘ₗ A) (Astar b) x₀ m x :=
    (isGalerkinIterate_adjoint_comp_iff_isMinResidual hadj b x₀ m x).2 hx
  have hstar' : (Astar ∘ₗ A) xstar = Astar b := by rw [LinearMap.comp_apply, hstar]
  have h := IsGalerkinIterate.energyNorm_error_le (by positivity)
    (by nlinarith : smin ^ 2 ≤ smax ^ 2) hB hgal hstar'
  have hsqrt : Real.sqrt (smax ^ 2 / smin ^ 2) = smax / smin := by
    rw [← div_pow]
    exact Real.sqrt_sq (div_nonneg (by linarith) hs.le)
  rw [hsqrt, energyNorm_adjoint_comp hadj, energyNorm_adjoint_comp hadj, map_sub, map_sub,
    hstar] at h
  exact h

end Convergence

/-!
### The two recurrences

The recurrences of [saad2003iterative], Algorithms 8.4 and 8.5, in the original variables: one
application of $A$ and one of $A^*$ per step, without forming the product $A^* A$. Each is
identified with the corresponding `CG.iterate`, so the whole theory of CG (the orthogonality
relations, finite termination, the Chebyshev bounds) transfers without a second induction.
-/

namespace CGNR

/-- The state of the CGNR iteration ([saad2003iterative], Algorithm 8.4): the iterate $x$, the
residual $r = b - Ax$ and the search direction $p$. The residual $z = A^* r$ of the normal
equations is computed again at each step, not stored. -/
structure State (E F : Type*) where
  /-- The current iterate $x$. -/
  x : E
  /-- The residual $r = b - Ax$ of the original system. -/
  r : F
  /-- The search direction $p$. -/
  p : E

/-- The CGNR step length $\alpha = \|A^* r\|^2 / \|Ap\|^2$, which is the CG step length for $A^* A$.
It is $0$ when $Ap = 0$, by Lean's convention for division by zero. -/
noncomputable def alpha (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (s : State E F) : 𝕜 :=
  inner 𝕜 (Astar s.r) (Astar s.r) / inner 𝕜 (A s.p) (A s.p)

/-- One CGNR step: with $\alpha$ the step length, $r' = r - \alpha A p$ and
$\beta = \|A^* r'\|^2 / \|A^* r\|^2$, the new state is
$(x + \alpha p, \ r', \ A^* r' + \beta p)$. -/
noncomputable def step (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (s : State E F) : State E F :=
  let α := alpha A Astar s
  let r' := s.r - α • A s.p
  let β : 𝕜 := inner 𝕜 (Astar r') (Astar r') / inner 𝕜 (Astar s.r) (Astar s.r)
  { x := s.x + α • s.p, r := r', p := Astar r' + β • s.p }

/-- The CGNR direction update coefficient $\beta = \|A^* r'\|^2 / \|A^* r\|^2$, where $r'$ is the
residual after the step. -/
noncomputable def beta (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (s : State E F) : 𝕜 :=
  inner 𝕜 (Astar (step A Astar s).r) (Astar (step A Astar s).r) /
    inner 𝕜 (Astar s.r) (Astar s.r)

/-- The starting state of CGNR: the iterate $x_0$, the residual $r_0 = b - A x_0$ and the direction
$p_0 = A^* r_0$. -/
def init (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (b : F) (x₀ : E) : State E F :=
  { x := x₀, r := b - A x₀, p := Astar (b - A x₀) }

/-- The CGNR state at step $k$ for $Ax = b$ started at $x_0$: the $k$-th application of
`Krylov.CGNR.step` to `Krylov.CGNR.init`. -/
noncomputable def iterate (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (b : F) (x₀ : E) (k : ℕ) :
    State E F :=
  (step A Astar)^[k] (init A Astar b x₀)

variable (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (b : F) (x₀ : E)

/-- The state at step $k + 1$ is one `Krylov.CGNR.step` applied to the state at step $k$. -/
theorem iterate_succ (k : ℕ) :
    iterate A Astar b x₀ (k + 1) = step A Astar (iterate A Astar b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterate update of one CGNR step: $x' = x + \alpha p$. -/
theorem step_x (s : State E F) : (step A Astar s).x = s.x + alpha A Astar s • s.p := rfl

/-- The residual update of one CGNR step: $r' = r - \alpha A p$. -/
theorem step_r (s : State E F) : (step A Astar s).r = s.r - alpha A Astar s • A s.p := rfl

/-- The direction update of one CGNR step: $p' = A^* r' + \beta p$. -/
theorem step_p (s : State E F) :
    (step A Astar s).p = Astar (step A Astar s).r + beta A Astar s • s.p := rfl

/-- Let $A^*$ be an adjoint of $A$. CGNR is CG on the normal equations $A^* A x = A^* b$, state by
state: for every $k$, the CGNR iterate and search direction are the CG iterate and search
direction for $A^* A x = A^* b$ from $x_0$, the CG residual is $A^*$ applied to the CGNR
residual, and the CGNR residual is the true residual $b - A x_k$.

Therefore everything proved about `CG.iterate` (the orthogonality relations, finite termination,
the Chebyshev bounds) holds for CGNR. -/
theorem iterate_eq
    (hadj : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A Astar) (k : ℕ) :
    (iterate A Astar b x₀ k).x = (CG.iterate (Astar ∘ₗ A) (Astar b) x₀ k).x ∧
      Astar (iterate A Astar b x₀ k).r = (CG.iterate (Astar ∘ₗ A) (Astar b) x₀ k).r ∧
      (iterate A Astar b x₀ k).p = (CG.iterate (Astar ∘ₗ A) (Astar b) x₀ k).p ∧
      (iterate A Astar b x₀ k).r = b - A (iterate A Astar b x₀ k).x := by
  have hinit : Astar (b - A x₀) = Astar b - (Astar ∘ₗ A) x₀ := by
    rw [LinearMap.comp_apply, map_sub]
  induction k with
  | zero => exact ⟨rfl, hinit, hinit, rfl⟩
  | succ k ih =>
    obtain ⟨hx, hr, hp, hres⟩ := ih
    have hq : inner 𝕜 ((Astar ∘ₗ A) (iterate A Astar b x₀ k).p) (iterate A Astar b x₀ k).p
        = inner 𝕜 (A (iterate A Astar b x₀ k).p) (A (iterate A Astar b x₀ k).p) := by
      rw [LinearMap.comp_apply, hadj.inner_apply_eq]
    have halpha : alpha A Astar (iterate A Astar b x₀ k)
        = CG.alpha (Astar ∘ₗ A) (CG.iterate (Astar ∘ₗ A) (Astar b) x₀ k) := by
      rw [alpha, CG.alpha, ← hr, ← hp, hq]
    have hr' : Astar (iterate A Astar b x₀ (k + 1)).r
        = (CG.iterate (Astar ∘ₗ A) (Astar b) x₀ (k + 1)).r := by
      rw [iterate_succ, step_r, CG.iterate_succ_r, map_sub, map_smul, hr, hp, halpha,
        LinearMap.comp_apply]
    have hbeta : beta A Astar (iterate A Astar b x₀ k)
        = CG.beta (Astar ∘ₗ A) (CG.iterate (Astar ∘ₗ A) (Astar b) x₀ k) := by
      rw [beta, CG.beta_iterate, ← iterate_succ, hr', hr]
    refine ⟨?_, hr', ?_, ?_⟩
    · rw [iterate_succ, step_x, CG.iterate_succ_x, hx, hp, halpha]
    · rw [iterate_succ, step_p, ← iterate_succ, hr', hbeta, hp, CG.iterate_succ_p]
    · rw [iterate_succ, step_r, step_x, hres, map_add, map_smul, sub_sub]

/-- Let $A^*$ be an adjoint of $A$. For every $k$, the CGNR iterate of [saad2003iterative],
Algorithm 8.4, is the CG iterate for the normal equations $A^* A x = A^* b$ from $x_0$. -/
theorem iterate_x_eq
    (hadj : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A Astar) (k : ℕ) :
    (iterate A Astar b x₀ k).x = (CG.iterate (Astar ∘ₗ A) (Astar b) x₀ k).x :=
  (iterate_eq A Astar b x₀ hadj k).1

/-- Let $A^*$ be an adjoint of $A$. For every $k$, the residual stored in the CGNR state is the true
residual $b - A x_k$. -/
theorem residual_eq
    (hadj : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A Astar) (k : ℕ) :
    (iterate A Astar b x₀ k).r = b - A (iterate A Astar b x₀ k).x :=
  (iterate_eq A Astar b x₀ hadj k).2.2.2

end CGNR

namespace CGNE

/-- The state of the CGNE (Craig) iteration ([saad2003iterative], Algorithm 8.5): the iterate $x$,
the residual $r = b - Ax$ and the search direction $p$, which is $A^*$ applied to the search
direction of the system $A A^* u = b$. -/
structure State (E F : Type*) where
  /-- The current iterate $x$. -/
  x : E
  /-- The residual $r = b - Ax$. -/
  r : F
  /-- The search direction $p$. -/
  p : E

/-- The CGNE step length $\alpha = \|r\|^2 / \|p\|^2$. It is $0$ when $p = 0$, by Lean's convention
for division by zero.

Unlike the other step lengths of this file, it takes no operator, so the field $\mathbb{K}$ is
fixed only by the expected type, and call sites write `(alpha s : 𝕜)`. -/
noncomputable def alpha (s : State E F) : 𝕜 := inner 𝕜 s.r s.r / inner 𝕜 s.p s.p

/-- One CGNE step: with $\alpha$ the step length, $r' = r - \alpha A p$ and
$\beta = \|r'\|^2 / \|r\|^2$, the new state is $(x + \alpha p, \ r', \ A^* r' + \beta p)$. -/
noncomputable def step (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (s : State E F) : State E F :=
  let α : 𝕜 := alpha s
  let r' := s.r - α • A s.p
  let β : 𝕜 := inner 𝕜 r' r' / inner 𝕜 s.r s.r
  { x := s.x + α • s.p, r := r', p := Astar r' + β • s.p }

/-- The CGNE direction update coefficient $\beta = \|r'\|^2 / \|r\|^2$, where $r'$ is the residual
after the step. -/
noncomputable def beta (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (s : State E F) : 𝕜 :=
  inner 𝕜 (step A Astar s).r (step A Astar s).r / inner 𝕜 s.r s.r

/-- The starting state of CGNE: the iterate $x_0$, the residual $r_0 = b - A x_0$ and the direction
$p_0 = A^* r_0$. -/
def init (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (b : F) (x₀ : E) : State E F :=
  { x := x₀, r := b - A x₀, p := Astar (b - A x₀) }

/-- The CGNE state at step $k$ for $Ax = b$ started at $x_0$: the $k$-th application of
`Krylov.CGNE.step` to `Krylov.CGNE.init`. -/
noncomputable def iterate (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (b : F) (x₀ : E) (k : ℕ) :
    State E F :=
  (step A Astar)^[k] (init A Astar b x₀)

variable (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (b : F) (x₀ : E)

/-- The state at step $k + 1$ is one `Krylov.CGNE.step` applied to the state at step $k$. -/
theorem iterate_succ (k : ℕ) :
    iterate A Astar b x₀ (k + 1) = step A Astar (iterate A Astar b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterate update of one CGNE step: $x' = x + \alpha p$. -/
theorem step_x (s : State E F) : (step A Astar s).x = s.x + (alpha s : 𝕜) • s.p := rfl

/-- The residual update of one CGNE step: $r' = r - \alpha A p$. -/
theorem step_r (s : State E F) : (step A Astar s).r = s.r - (alpha s : 𝕜) • A s.p := rfl

/-- The direction update of one CGNE step: $p' = A^* r' + \beta p$. -/
theorem step_p (s : State E F) :
    (step A Astar s).p = Astar (step A Astar s).r + beta A Astar s • s.p := rfl

/-- Let $A^*$ be an adjoint of $A$, and let $u_0 \in F$ satisfy $A^* u_0 = x_0$. CGNE is CG on
$A A^* u = b$ read through $x = A^* u$: for every $k$, the CGNE iterate is $A^*$ applied to the
CG iterate for $A A^* u = b$ from $u_0$, the CGNE direction is $A^*$ applied to the CG
direction, and the two residuals are equal. This is Craig's method, [saad2003iterative],
Algorithm 8.5. -/
theorem iterate_eq
    (hadj : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A Astar) {u₀ : F}
    (hu₀ : Astar u₀ = x₀) (k : ℕ) :
    (iterate A Astar b x₀ k).x = Astar (CG.iterate (A ∘ₗ Astar) b u₀ k).x ∧
      (iterate A Astar b x₀ k).r = (CG.iterate (A ∘ₗ Astar) b u₀ k).r ∧
      (iterate A Astar b x₀ k).p = Astar (CG.iterate (A ∘ₗ Astar) b u₀ k).p := by
  have hinit : b - (A ∘ₗ Astar) u₀ = b - A x₀ := by rw [LinearMap.comp_apply, hu₀]
  induction k with
  | zero =>
    refine ⟨hu₀.symm, hinit.symm, ?_⟩
    change Astar (b - A x₀) = Astar (b - (A ∘ₗ Astar) u₀)
    rw [hinit]
  | succ k ih =>
    obtain ⟨hx, hr, hp⟩ := ih
    have hq : inner 𝕜 ((A ∘ₗ Astar) (CG.iterate (A ∘ₗ Astar) b u₀ k).p)
          (CG.iterate (A ∘ₗ Astar) b u₀ k).p
        = inner 𝕜 (Astar (CG.iterate (A ∘ₗ Astar) b u₀ k).p)
          (Astar (CG.iterate (A ∘ₗ Astar) b u₀ k).p) := by
      rw [LinearMap.comp_apply, ← inner_conj_symm,
        ← LinearMap.inner_apply_eq_inner_apply_of_adjoint hadj, inner_conj_symm]
    have halpha : (alpha (iterate A Astar b x₀ k) : 𝕜)
        = CG.alpha (A ∘ₗ Astar) (CG.iterate (A ∘ₗ Astar) b u₀ k) := by
      rw [alpha, CG.alpha, hq, hr, hp]
    have hAp : A (iterate A Astar b x₀ k).p
        = (A ∘ₗ Astar) (CG.iterate (A ∘ₗ Astar) b u₀ k).p := by
      rw [hp, LinearMap.comp_apply]
    have hr' : (iterate A Astar b x₀ (k + 1)).r = (CG.iterate (A ∘ₗ Astar) b u₀ (k + 1)).r := by
      rw [iterate_succ, step_r, CG.iterate_succ_r, hr, hAp, halpha]
    have hbeta : beta A Astar (iterate A Astar b x₀ k)
        = CG.beta (A ∘ₗ Astar) (CG.iterate (A ∘ₗ Astar) b u₀ k) := by
      rw [beta, CG.beta_iterate, ← iterate_succ, hr', hr]
    refine ⟨?_, hr', ?_⟩
    · rw [iterate_succ, step_x, CG.iterate_succ_x, hx, hp, halpha, map_add, map_smul]
    · rw [iterate_succ, step_p, ← iterate_succ, hr', hbeta, hp, CG.iterate_succ_p, map_add,
        map_smul]

/-- Let $A^*$ be an adjoint of $A$, and let $u_0 \in F$ satisfy $A^* u_0 = x_0$. For every $k$, the
CGNE iterate (Craig's method) is $A^*$ applied to the CG iterate for $A A^* u = b$ from $u_0$. -/
theorem iterate_x_eq
    (hadj : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A Astar) {u₀ : F}
    (hu₀ : Astar u₀ = x₀) (k : ℕ) :
    (iterate A Astar b x₀ k).x = Astar (CG.iterate (A ∘ₗ Astar) b u₀ k).x :=
  (iterate_eq A Astar b x₀ hadj hu₀ k).1

end CGNE

end Krylov
