/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.InnerProductSpace.Projection.Compression

/-!
# Specifications and well-posedness of projection methods

A projection method for the equation $Ax = b$ chooses an approximation $x$ in an affine trial space
$x_0 + K$ and fixes it by a condition on the residual $b - Ax$. This file gives the four standard
conditions as propositions ([saad2003iterative] Chapter 5, [fong2012cg] §2, [choi2006iterative]
Table 2.5, [han2009theoretical] Chapter 9). In the **Petrov–Galerkin** condition the residual is
orthogonal to a test space $L$. The **Galerkin** condition is the case $L = K$ (FOM, CG, the Lanczos
method). The **minimal-residual** condition asks that $x$ minimize $\|b - Ax\|$ over $x_0 + K$
(GMRES, MINRES, CR). The **minimal-error** condition asks that $x$ minimize $\|x^* - x\|$ over
$x_0 + K$ for a given target $x^*$ (SYMMLQ, CGNE).

The file proves well-posedness ([saad2003iterative] Proposition 5.1), the equivalence of minimal
residual with a Petrov–Galerkin condition (Proposition 5.3), the residual formula (Proposition 5.4),
exactness on invariant subspaces (Proposition 5.6), the matrix form (5.7) and the general error
bound (Theorem 5.7). The optimality characterizations of the Galerkin and minimal-error iterates are
in `Numlib.Projection.Optimality`. Below, $r_0 = b - Ax_0$ is the initial residual and $P_K$ is the
orthogonal projection onto $K$.

## Main definitions

* `IsPetrovGalerkin`: $x - x_0 \in K$ and $b - Ax \perp L$.
* `IsGalerkin`: the Petrov–Galerkin condition with $L = K$.
* `IsMinResidual`: $x \in x_0 + K$ minimizes $\|b - Ay\|$ over $y \in x_0 + K$.
* `IsMinError`: $x \in x_0 + K$ minimizes $\|x^* - y\|$ over $y \in x_0 + K$.

## Main results

* `IsMinResidual.iff_isPetrovGalerkin`: minimal residual over $x_0 + K$ is the Petrov–Galerkin
  condition with $L = AK$.
* `IsMinResidual.residual_eq`: for finite-dimensional $K$, a minimal-residual iterate has residual
  $r_0 - P_{AK} r_0$.
* `IsPetrovGalerkin.eq_of_invt`: if $K$ is invariant under $A$, $r_0 \in K$ and
  $K \cap L^\perp = 0$, the Petrov–Galerkin iterate solves $Ax = b$.
* `existsUnique_isGalerkin_of_isCoercive`: for coercive $A$ and finite-dimensional $K$, the Galerkin
  problem has a unique solution.
* `existsUnique_isPetrovGalerkin_of_finrank_eq`: if $\dim K = \dim L < \infty$ and no nonzero
  $z \in K$ has $Az \perp L$, the Petrov–Galerkin problem has a unique solution.
* `existsUnique_isMinResidual_of_injOn`: for finite-dimensional $K$ and $A$ injective on $K$, the
  minimal-residual problem has a unique solution.
* `isPetrovGalerkin_iff_mulVec`: in bases $V$ of $K$ and $W$ of $L$, the Petrov–Galerkin condition
  for $x_0 + Vy$ is $(W^H A V) y = W^H r_0$.
* `IsPetrovGalerkin.norm_residual_projected_le`: the general error bound of [saad2003iterative]
  Theorem 5.7.

## Implementation notes

* The operator may be rectangular, $A : E \to F$ with $b \in F$, in the Petrov–Galerkin and
  minimal-residual conditions and in every result that does not compare $Ax$ with $x$. The trial
  space $K$ lies in $E$ and the test space $L$ in $F$. This is the setting of the normal-equation
  methods for a rectangular system ([golub2013matrix] §11.3.9) and of the least-squares Krylov
  methods. The Galerkin condition $L = K$ and the results about coercivity or invariant subspaces
  need $E = F$.
* The inner product $\langle u, v \rangle$ is `inner 𝕜 u v`, which is conjugate-linear in $u$. The
  orthogonal complement $L^\perp$ is `Lᗮ`, and $P_K$ is `K.starProjection`.
* The target $x^*$ of the minimal-error condition is a parameter, so that the condition has a
  meaning also for singular $A$.
-/

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace Submodule

variable {K : Submodule 𝕜 E}

/-- Let $s$ be a subset of $E$. A vector $v$ lies in the orthogonal complement of
$\operatorname{span} s$ if and only if $\langle u, v \rangle = 0$ for every $u \in s$. -/
theorem mem_orthogonal_span {s : Set E} {v : E} :
    v ∈ (Submodule.span 𝕜 s)ᗮ ↔ ∀ u ∈ s, inner 𝕜 u v = 0 := by
  refine ⟨fun h u hu => h u (Submodule.subset_span hu), fun h u hu => ?_⟩
  induction hu using Submodule.span_induction with
  | mem z hz => exact h z hz
  | zero => simp
  | add z w _ _ hz hw => rw [inner_add_left, hz, hw, add_zero]
  | smul c z _ hz => rw [inner_smul_left, hz, mul_zero]

/-- Let $K$ be a subspace of $E$ that has an orthogonal projection $P_K$. For $w \in K$ and every
$u \in E$,
$$\langle w, P_K u \rangle = \langle w, u \rangle.$$
-/
theorem inner_starProjection_right [K.HasOrthogonalProjection] {w : E} (hw : w ∈ K) (u : E) :
    inner 𝕜 w (K.starProjection u) = inner 𝕜 w u := by
  have h : inner 𝕜 w (u - K.starProjection u) = (0 : 𝕜) :=
    inner_eq_zero_symm.1 (K.starProjection_inner_eq_zero u w hw)
  rw [inner_sub_right, sub_eq_zero] at h
  exact h.symm

/-- Let $K$ be a subspace of $E$, let $u \in E$, and let $v \in K$ be a best approximation of $u$
from $K$: $\|u - v\| \le \|u - w\|$ for all $w \in K$. Then $\langle u - v, w \rangle = 0$ for
every $w \in K$.

This is a pointwise form of `Submodule.norm_eq_iInf_iff_inner_eq_zero`. -/
theorem inner_eq_zero_of_forall_norm_sub_le {u v : E} (hv : v ∈ K)
    (h : ∀ w ∈ K, ‖u - v‖ ≤ ‖u - w‖) {w : E} (hw : w ∈ K) : inner 𝕜 (u - v) w = 0 := by
  have hbdd : BddBelow (Set.range fun z : K => ‖u - (z : E)‖) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact norm_nonneg _
  refine (K.norm_eq_iInf_iff_inner_eq_zero hv).1 ?_ w hw
  exact le_antisymm (le_ciInf fun z => h z z.2) (ciInf_le hbdd ⟨v, hv⟩)

/-- Let $K$ be a subspace of $E$, let $u \in E$ and $v \in K$, and assume
$\langle u - v, w \rangle = 0$ for every $w \in K$. Then $v$ is a best approximation of $u$ from
$K$: $\|u - v\| \le \|u - w\|$ for every $w \in K$. -/
theorem norm_sub_le_of_forall_inner_eq_zero {u v : E} (hv : v ∈ K)
    (h : ∀ w ∈ K, inner 𝕜 (u - v) w = 0) {w : E} (hw : w ∈ K) : ‖u - v‖ ≤ ‖u - w‖ := by
  have hvw : u - w = (u - v) + (v - w) := by abel
  have h0 : inner 𝕜 (u - v) (v - w) = (0 : 𝕜) := h _ (K.sub_mem hv hw)
  have h1 : ‖u - v‖ * ‖u - v‖ ≤ ‖u - w‖ * ‖u - w‖ := by
    rw [hvw, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0]
    nlinarith [norm_nonneg (v - w)]
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_mul_self (norm_nonneg _), Real.sqrt_mul_self (norm_nonneg _)] at h2

end Submodule

/-- The **Petrov–Galerkin condition** ([saad2003iterative], (5.1)–(5.2)). Let $A : E \to F$ be
linear, $b \in F$, $x_0 \in E$, and let $K \subseteq E$ and $L \subseteq F$ be subspaces. A
vector $x \in E$ satisfies the condition if
$$x \in x_0 + K \quad\text{and}\quad b - Ax \perp L.$$
-/
structure IsPetrovGalerkin (A : E →ₗ[𝕜] F) (b : F) (x₀ : E) (K : Submodule 𝕜 E) (L : Submodule 𝕜 F)
    (x : E) : Prop where
  /-- The iterate lies in the affine trial space: $x - x_0 \in K$. -/
  mem : x - x₀ ∈ K
  /-- The residual is orthogonal to the test space: $b - Ax \in L^\perp$. -/
  orth : b - A x ∈ Lᗮ

/-- The **Galerkin condition** (orthogonal projection method). Let $A : E \to E$ be linear,
$b, x_0 \in E$ and $K \subseteq E$ a subspace. A vector $x$ satisfies the condition if
$x \in x_0 + K$ and $b - Ax \perp K$. This is the Petrov–Galerkin condition `IsPetrovGalerkin`
with $L = K$. -/
abbrev IsGalerkin (A : E →ₗ[𝕜] E) (b x₀ : E) (K : Submodule 𝕜 E) (x : E) : Prop :=
  IsPetrovGalerkin A b x₀ K K x

/-- The **minimal-residual condition**. Let $A : E \to F$ be linear, $b \in F$, $x_0 \in E$ and
$K \subseteq E$ a subspace. A vector $x$ satisfies the condition if $x \in x_0 + K$ and
$$\|b - Ax\| \le \|b - Ay\| \quad\text{for all } y \in x_0 + K.$$
-/
structure IsMinResidual (A : E →ₗ[𝕜] F) (b : F) (x₀ : E) (K : Submodule 𝕜 E) (x : E) : Prop where
  /-- The iterate lies in the affine trial space: $x - x_0 \in K$. -/
  mem : x - x₀ ∈ K
  /-- The residual norm at $x$ is at most the residual norm at every $y \in x_0 + K$. -/
  min : ∀ y, y - x₀ ∈ K → ‖b - A x‖ ≤ ‖b - A y‖

/-- The **minimal-error condition**. Let $x^*, x_0 \in E$ and let $K \subseteq E$ be a subspace. A
vector $x$ satisfies the condition if $x \in x_0 + K$ and
$$\|x^* - x\| \le \|x^* - y\| \quad\text{for all } y \in x_0 + K.$$
That is, $x$ is a best approximation of $x^*$ from the affine space $x_0 + K$. No operator
appears in the condition.

The target $x^*$ is the solution of $Ax = b$. It is a parameter, so that the condition has a
meaning also for singular $A$. SYMMLQ uses $K = A \mathcal{K}_m$, and CGNE (Craig's method) uses
$K = A^H L$. -/
structure IsMinError (xstar x₀ : E) (K : Submodule 𝕜 E) (x : E) : Prop where
  /-- The iterate lies in the affine trial space: $x - x_0 \in K$. -/
  mem : x - x₀ ∈ K
  /-- The error at $x$ is at most the error at every $y \in x_0 + K$. -/
  min : ∀ y, y - x₀ ∈ K → ‖xstar - x‖ ≤ ‖xstar - y‖

namespace IsPetrovGalerkin

variable {A : E →ₗ[𝕜] F} {b : F} {x₀ : E} {K : Submodule 𝕜 E} {L : Submodule 𝕜 F} {x : E}

/-- Let $x$ satisfy the Petrov–Galerkin condition for $(A, b, x_0, K, L)$. Then the residual is
orthogonal to every test vector: $\langle w, b - Ax \rangle = 0$ for every $w \in L$. -/
theorem inner_residual_eq_zero (hx : IsPetrovGalerkin A b x₀ K L x) {w : F} (hw : w ∈ L) :
    inner 𝕜 w (b - A x) = 0 :=
  (Submodule.mem_orthogonal _ _).1 hx.orth w hw

/-- **Uniqueness of the Petrov–Galerkin iterate.** Let $x$ and $x'$ both satisfy the Petrov–Galerkin
condition for $(A, b, x_0, K, L)$. Assume that $A$ maps $K$ injectively modulo $L^\perp$: every
$z \in K$ with $Az \in L^\perp$ is $z = 0$. Then $x = x'$.

The hypothesis is the nondegeneracy condition of [saad2003iterative], Proposition 5.1. The proof
uses that $x - x'$ lies in $K$ and that $A(x - x')$ lies in $L^\perp$. -/
theorem eq_of_forall (hx : IsPetrovGalerkin A b x₀ K L x) {x' : E}
    (hx' : IsPetrovGalerkin A b x₀ K L x')
    (hKL : ∀ z ∈ K, A z ∈ Lᗮ → z = 0) : x = x' := by
  have hmem : x - x' ∈ K := by
    have h : x - x' = (x - x₀) - (x' - x₀) := by abel
    rw [h]; exact K.sub_mem hx.mem hx'.mem
  have hAz : A (x - x') ∈ Lᗮ := by
    have h : A (x - x') = (b - A x') - (b - A x) := by rw [map_sub]; abel
    rw [h]; exact Submodule.sub_mem _ hx'.orth hx.orth
  exact sub_eq_zero.1 (hKL _ hmem hAz)

/-- **Exactness on invariant subspaces** ([saad2003iterative], Proposition 5.6). Let $A : E \to E$
be linear, and let $x$ satisfy the Petrov–Galerkin condition for $(A, b, x_0, K, L)$. Assume
that $K$ is invariant under $A$, that the initial residual $b - Ax_0$ lies in $K$, and that
$K \cap L^\perp = 0$. Then $Ax = b$. -/
theorem eq_of_invt {A : E →ₗ[𝕜] E} {b : E} {L : Submodule 𝕜 E}
    (hx : IsPetrovGalerkin A b x₀ K L x) (hK : K ∈ Module.End.invtSubmodule A)
    (hr : b - A x₀ ∈ K) (hKL : ∀ z ∈ K, z ∈ Lᗮ → z = 0) : A x = b := by
  have h1 : b - A x ∈ K := by
    have h : b - A x = (b - A x₀) - A (x - x₀) := by rw [map_sub]; abel
    rw [h]
    exact K.sub_mem hr ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1 hK _ hx.mem)
  exact (sub_eq_zero.1 (hKL _ h1 hx.orth)).symm

/-- **Restart.** If $x$ satisfies the Petrov–Galerkin condition for $(A, b, x_0, K, L)$ and
$x_1 \in x_0 + K$, then $x$ also satisfies the Petrov–Galerkin condition for
$(A, b, x_1, K, L)$. -/
theorem of_mem (hx : IsPetrovGalerkin A b x₀ K L x) {x₁ : E} (hx₁ : x₁ - x₀ ∈ K) :
    IsPetrovGalerkin A b x₁ K L x := by
  refine ⟨?_, hx.orth⟩
  have h : x - x₁ = (x - x₀) - (x₁ - x₀) := by abel
  rw [h]; exact K.sub_mem hx.mem hx₁

end IsPetrovGalerkin

/-- The residual at $y$ in terms of the initial residual: $b - Ay = (b - Ax_0) - A(y - x_0)$. -/
theorem residual_eq_sub_apply_sub (A : E →ₗ[𝕜] F) (b : F) (x₀ y : E) :
    b - A y = (b - A x₀) - A (y - x₀) := by rw [map_sub]; abel

namespace IsMinResidual

variable {A : E →ₗ[𝕜] F} {b : F} {x₀ : E} {K : Submodule 𝕜 E} {x : E}

/-- **Minimal residual as a Petrov–Galerkin condition** ([saad2003iterative], Proposition 5.3). Let
$A : E \to F$ be linear. A vector $x$ satisfies the minimal-residual condition for
$(A, b, x_0, K)$ if and only if it satisfies the Petrov–Galerkin condition for
$(A, b, x_0, K, AK)$.

No hypothesis on the dimension of $K$ is needed. -/
theorem iff_isPetrovGalerkin :
    IsMinResidual A b x₀ K x ↔ IsPetrovGalerkin A b x₀ K (K.map A) x := by
  constructor
  · rintro ⟨hmem, hmin⟩
    refine ⟨hmem, (Submodule.mem_orthogonal' _ _).2 fun u hu => ?_⟩
    rw [residual_eq_sub_apply_sub A b x₀ x]
    refine Submodule.inner_eq_zero_of_forall_norm_sub_le (Submodule.mem_map_of_mem hmem) ?_ hu
    rintro _ hw
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hw
    have h := hmin (x₀ + z) (by simpa using hz)
    rwa [residual_eq_sub_apply_sub A b x₀ x, residual_eq_sub_apply_sub A b x₀ (x₀ + z),
      add_sub_cancel_left] at h
  · rintro ⟨hmem, horth⟩
    refine ⟨hmem, fun y hy => ?_⟩
    rw [residual_eq_sub_apply_sub A b x₀ x, residual_eq_sub_apply_sub A b x₀ y]
    refine Submodule.norm_sub_le_of_forall_inner_eq_zero (Submodule.mem_map_of_mem hmem) ?_
      (Submodule.mem_map_of_mem hy)
    intro w hw
    rw [← residual_eq_sub_apply_sub A b x₀ x]
    exact (Submodule.mem_orthogonal' _ _).1 horth w hw

/-- A minimal-residual iterate for $(A, b, x_0, K)$ satisfies the Petrov–Galerkin condition with
test space $L = AK$. This is the forward direction of `IsMinResidual.iff_isPetrovGalerkin`. -/
theorem isPetrovGalerkin (hx : IsMinResidual A b x₀ K x) :
    IsPetrovGalerkin A b x₀ K (K.map A) x :=
  (iff_isPetrovGalerkin).1 hx

/-- **The minimal-residual residual** ([saad2003iterative], Proposition 5.4). Let $K$ be
finite-dimensional, and let $x$ satisfy the minimal-residual condition for $(A, b, x_0, K)$.
With $r_0 = b - Ax_0$ and $P_{AK}$ the orthogonal projection onto $AK$,
$$b - Ax = (I - P_{AK}) r_0.$$
-/
theorem residual_eq [FiniteDimensional 𝕜 K] (hx : IsMinResidual A b x₀ K x) :
    b - A x = (b - A x₀) - (K.map A).starProjection (b - A x₀) := by
  have hproj : (K.map A).starProjection (b - A x₀) = A (x - x₀) :=
    Submodule.eq_starProjection_of_mem_orthogonal' (Submodule.mem_map_of_mem hx.mem)
      hx.isPetrovGalerkin.orth
      (by rw [residual_eq_sub_apply_sub A b x₀ x]; abel)
  rw [hproj, ← residual_eq_sub_apply_sub A b x₀ x]

/-- Let $K$ be finite-dimensional. Any two minimal-residual iterates $x, x'$ for $(A, b, x_0, K)$
have the same residual, $b - Ax = b - Ax'$, even when $x \neq x'$. -/
theorem residual_unique [FiniteDimensional 𝕜 K] (hx : IsMinResidual A b x₀ K x) {x' : E}
    (hx' : IsMinResidual A b x₀ K x') : b - A x = b - A x' := by
  rw [hx.residual_eq, hx'.residual_eq]

/-- A minimal-residual step does not increase the residual norm: if $x$ satisfies the
minimal-residual condition for $(A, b, x_0, K)$, then $\|b - Ax\| \le \|b - Ax_0\|$.

The proof compares $x$ with the starting point $x_0$, which lies in $x_0 + K$. -/
theorem norm_residual_le_norm_residual_zero (hx : IsMinResidual A b x₀ K x) :
    ‖b - A x‖ ≤ ‖b - A x₀‖ :=
  hx.min x₀ (by simp)

/-- **Monotonicity on nested subspaces.** Let $K \subseteq K'$, let $x$ satisfy the minimal-residual
condition for $(A, b, x_0, K)$, and let $x'$ satisfy it for $(A, b, x_0, K')$. Then
$\|b - Ax'\| \le \|b - Ax\|$. -/
theorem norm_residual_le {K' : Submodule 𝕜 E} {x' : E} (hx : IsMinResidual A b x₀ K x)
    (hx' : IsMinResidual A b x₀ K' x') (hKK' : K ≤ K') : ‖b - A x'‖ ≤ ‖b - A x‖ :=
  hx'.min x (hKK' hx.mem)

/-- Let $x$ satisfy the minimal-residual condition for $(A, b, x_0, K)$. If some $y \in x_0 + K$ has
$Ay = b$, then $Ax = b$. -/
theorem apply_eq_of_exists (hx : IsMinResidual A b x₀ K x) {y : E} (hy : y - x₀ ∈ K)
    (hAy : A y = b) :
    A x = b := by
  have h := hx.min y hy
  rw [hAy, sub_self, norm_zero] at h
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h)).symm

end IsMinResidual

/-- Let $K$ be a subspace of $E$ that has an orthogonal projection $P_K$. For all $x^*, x_0 \in E$,
the vector $x_0 + P_K(x^* - x_0)$ satisfies the minimal-error condition for $(x^*, x_0, K)$.

No hypothesis of finite dimension is needed, only the existence of $P_K$. -/
theorem isMinError_add_starProjection {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    (xstar x₀ : E) : IsMinError xstar x₀ K (x₀ + K.starProjection (xstar - x₀)) := by
  refine ⟨?_, fun y hy => ?_⟩
  · rw [add_sub_cancel_left]
    exact Submodule.starProjection_apply_mem K _
  · rw [show xstar - (x₀ + K.starProjection (xstar - x₀))
        = (xstar - x₀) - K.starProjection (xstar - x₀) by abel,
      show xstar - y = (xstar - x₀) - (y - x₀) by abel]
    exact Submodule.norm_sub_le_of_forall_inner_eq_zero (Submodule.starProjection_apply_mem K _)
      (fun w hw => K.starProjection_inner_eq_zero _ w hw) hy

section WellPosed

variable {A : E →ₗ[𝕜] E} (b x₀ : E) (K : Submodule 𝕜 E)

/-- Let $A : E \to E$ be coercive and let $K$ be a subspace. If $z \in K$ and $Az \in K^\perp$, then
$z = 0$. This is the nondegeneracy condition of [saad2003iterative], Proposition 5.1(i). -/
theorem eq_zero_of_isCoercive_of_apply_mem_orthogonal (hA : A.IsCoercive) {z : E} (hz : z ∈ K)
    (hAz : A z ∈ Kᗮ) : z = 0 := by
  obtain ⟨c, hc, hAc⟩ := hA
  have h0 : inner 𝕜 z (A z) = (0 : 𝕜) := (Submodule.mem_orthogonal _ _).1 hAz z hz
  have hre : RCLike.re (inner 𝕜 (A z) z) = 0 := by
    rw [← inner_conj_symm, h0, map_zero, map_zero]
  have hle := hAc z
  rw [hre] at hle
  have hz2 : ‖z‖ ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hz2)

/-- **Solvability of the Galerkin problem.** Let $A : E \to E$ be linear and $K$ a
finite-dimensional subspace. Assume that the compression $P_K A|_K : K \to K$ is injective. Then
some $x$ satisfies the Galerkin condition for $(A, b, x_0, K)$.

The compression is surjective because it is an injective map of a finite-dimensional space to
itself. So the projected equation $P_K A z = P_K r_0$ has a solution $z \in K$, and
$x = x_0 + z$ is a solution. -/
theorem exists_isGalerkin_of_injective_compression [FiniteDimensional 𝕜 K]
    (hinj : Function.Injective
      ((K.orthogonalProjectionOnto : E →ₗ[𝕜] K).comp (A.comp K.subtype))) :
    ∃ x, IsGalerkin A b x₀ K x := by
  obtain ⟨z, hz⟩ :=
    (LinearMap.injective_iff_surjective.1 hinj) (K.orthogonalProjectionOnto (b - A x₀))
  have hz' : K.starProjection (A (z : E)) = K.starProjection (b - A x₀) := by
    rw [Submodule.starProjection_apply, Submodule.starProjection_apply]
    exact congrArg Subtype.val hz
  refine ⟨x₀ + (z : E), by simp, (Submodule.mem_orthogonal _ _).2 fun w hw => ?_⟩
  have h1 : inner 𝕜 w (A (z : E)) = inner 𝕜 w (b - A x₀) := by
    rw [← Submodule.inner_starProjection_right hw (A (z : E)), hz',
      Submodule.inner_starProjection_right hw]
  rw [map_add, ← sub_sub, inner_sub_right, h1, sub_self]

/-- **Well-posedness of the Galerkin problem** ([saad2003iterative], Proposition 5.1(i)). Let
$A : E \to E$ be coercive and let $K$ be finite-dimensional. Then there is exactly one $x$ that
satisfies the Galerkin condition for $(A, b, x_0, K)$. -/
theorem existsUnique_isGalerkin_of_isCoercive (hA : A.IsCoercive) [FiniteDimensional 𝕜 K] :
    ∃! x, IsGalerkin A b x₀ K x := by
  have hKL : ∀ z ∈ K, A z ∈ Kᗮ → z = 0 := fun z hz hAz =>
    eq_zero_of_isCoercive_of_apply_mem_orthogonal K hA hz hAz
  -- the compression of `A` to `K` is injective, hence surjective
  have hinj : Function.Injective
      ((K.orthogonalProjectionOnto : E →ₗ[𝕜] K).comp (A.comp K.subtype)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : K.starProjection (A (z : E)) = 0 := by
      rw [Submodule.starProjection_apply]
      exact congrArg Subtype.val hz
    refine Subtype.ext (hKL _ z.2 ((Submodule.mem_orthogonal _ _).2 fun w hw => ?_))
    rw [← Submodule.inner_starProjection_right hw (A (z : E)), hz', inner_zero_right]
  obtain ⟨x, hgal⟩ := exists_isGalerkin_of_injective_compression b x₀ K hinj
  exact ⟨x, hgal, fun y hy => hy.eq_of_forall hgal hKL⟩

/-- **Well-posedness of the Petrov–Galerkin problem** ([saad2003iterative], Proposition 5.1). Let
$A : E \to F$ be linear, $b \in F$, $x_0 \in E$, and let $K \subseteq E$ and $L \subseteq F$ be
finite-dimensional subspaces with $\dim K = \dim L$. Assume that $A$ maps $K$ injectively modulo
$L^\perp$: every $z \in K$ with $Az \in L^\perp$ is $z = 0$. Then there is exactly one $x$ that
satisfies the Petrov–Galerkin condition for $(A, b, x_0, K, L)$.

The nondegeneracy hypothesis is that of `IsPetrovGalerkin.eq_of_forall`, which gives uniqueness.
The equal dimensions give existence: the map $z \mapsto P_L(Az)$ from $K$ to $L$ is injective,
hence surjective. -/
theorem existsUnique_isPetrovGalerkin_of_finrank_eq {A : E →ₗ[𝕜] F} (b : F) (x₀ : E)
    (K : Submodule 𝕜 E) (L : Submodule 𝕜 F) [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L)
    (hKL : ∀ z ∈ K, A z ∈ Lᗮ → z = 0) : ∃! x, IsPetrovGalerkin A b x₀ K L x := by
  set G : ↥K →ₗ[𝕜] ↥L := (L.orthogonalProjectionOnto : F →ₗ[𝕜] ↥L).comp (A.comp K.subtype) with hG
  have hinj : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    refine Subtype.ext (hKL (z : E) z.2 ?_)
    exact Submodule.orthogonalProjectionOnto_eq_zero_iff.1 (LinearMap.mem_ker.1 hz)
  obtain ⟨δ, hδ⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
    (L.orthogonalProjectionOnto (b - A x₀))
  have hPG : IsPetrovGalerkin A b x₀ K L (x₀ + δ) := by
    refine ⟨by simp, Submodule.orthogonalProjectionOnto_eq_zero_iff.1 ?_⟩
    have hres : b - A (x₀ + (δ : E)) = (b - A x₀) - A (δ : E) := by rw [map_add]; abel
    rw [hres, map_sub]
    change L.orthogonalProjectionOnto (b - A x₀) - G δ = 0
    rw [hδ, sub_self]
  exact ⟨x₀ + δ, hPG, fun y hy => hy.eq_of_forall hPG hKL⟩

/-- Let $K$ be finite-dimensional. For all $x^*, x_0 \in E$, some $x$ satisfies the minimal-error
condition for $(x^*, x_0, K)$. The proof takes the orthogonal projection of $x^*$ onto
$x_0 + K$. -/
theorem exists_isMinError [FiniteDimensional 𝕜 K] (xstar : E) : ∃ x, IsMinError xstar x₀ K x :=
  ⟨_, isMinError_add_starProjection (K := K) xstar x₀⟩

end WellPosed

section WellPosedMinResidual

variable {A : E →ₗ[𝕜] F} (b : F) (x₀ : E) (K : Submodule 𝕜 E)

/-- Let $A : E \to F$ be linear and let $K$ be finite-dimensional. For all $b \in F$ and
$x_0 \in E$, some $x$ satisfies the minimal-residual condition for $(A, b, x_0, K)$. -/
theorem exists_isMinResidual [FiniteDimensional 𝕜 K] : ∃ x, IsMinResidual A b x₀ K x := by
  obtain ⟨z, hz, hzeq⟩ := Submodule.mem_map.1
    (Submodule.starProjection_apply_mem (K.map A) (b - A x₀))
  refine ⟨x₀ + z, IsMinResidual.iff_isPetrovGalerkin.2 ⟨by simpa using hz, ?_⟩⟩
  have h : b - A (x₀ + z) = (b - A x₀) - (K.map A).starProjection (b - A x₀) := by
    rw [map_add, hzeq]; abel
  rw [h]
  exact Submodule.sub_starProjection_mem_orthogonal _

/-- **Well-posedness of the minimal-residual problem** ([saad2003iterative], Proposition 5.1(ii)).
Let $A : E \to F$ be linear, let $K$ be finite-dimensional, and let $A$ be injective on $K$.
Then there is exactly one $x$ that satisfies the minimal-residual condition for
$(A, b, x_0, K)$. -/
theorem existsUnique_isMinResidual_of_injOn [FiniteDimensional 𝕜 K] (hinj : Set.InjOn A K) :
    ∃! x, IsMinResidual A b x₀ K x := by
  obtain ⟨x, hx⟩ := exists_isMinResidual (A := A) b x₀ K
  refine ⟨x, hx, fun y hy => ?_⟩
  refine hy.isPetrovGalerkin.eq_of_forall hx.isPetrovGalerkin fun z hz hAz => ?_
  have h0 : A z = 0 :=
    inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 hAz (A z)
      (Submodule.mem_map_of_mem hz))
  exact hinj hz K.zero_mem (by rw [h0, map_zero])

end WellPosedMinResidual

section MatrixForm

variable {ι : Type*} [Fintype ι]
variable {A : E →ₗ[𝕜] F} {b : F} {x₀ : E} {K : Submodule 𝕜 E} {L : Submodule 𝕜 F}

/-- **Matrix form of the Petrov–Galerkin condition** ([saad2003iterative], (5.7)). Let
$V = (v_1, \dots, v_m)$ be a basis of $K$ and $W = (w_1, \dots, w_m)$ a basis of $L$, indexed by
the same finite set, and let $r_0 = b - Ax_0$. For $y \in \mathbb{K}^m$, where $\mathbb{K}$ is
the scalar field ($\mathbb{R}$ or $\mathbb{C}$), the vector $x_0 + \sum_j y_j v_j$ satisfies the
Petrov–Galerkin condition for $(A, b, x_0, K, L)$ if and only if
$$(W^H A V)\, y = W^H r_0,$$
where $(W^H A V)_{ij} = \langle w_i, A v_j \rangle$ and
$(W^H r_0)_i = \langle w_i, r_0 \rangle$. -/
theorem isPetrovGalerkin_iff_mulVec (V : Module.Basis ι 𝕜 K) (W : Module.Basis ι 𝕜 L)
    (y : ι → 𝕜) :
    IsPetrovGalerkin A b x₀ K L (x₀ + ∑ j, y j • (V j : E)) ↔
      (Matrix.of fun i j => inner 𝕜 (W i : F) (A (V j))).mulVec y =
        fun i => inner 𝕜 (W i : F) (b - A x₀) := by
  have hmem : (x₀ + ∑ j, y j • (V j : E)) - x₀ ∈ K := by
    simpa using Submodule.sum_mem _ fun j (_ : j ∈ Finset.univ) => K.smul_mem (y j) (V j).2
  have hinner : ∀ i : ι, inner 𝕜 (W i : F) (b - A (x₀ + ∑ j, y j • (V j : E)))
      = inner 𝕜 (W i : F) (b - A x₀)
        - (Matrix.of fun i j => inner 𝕜 (W i : F) (A (V j))).mulVec y i := by
    intro i
    have hres : b - A (x₀ + ∑ j, y j • (V j : E))
        = (b - A x₀) - ∑ j, y j • A (V j) := by
      simp only [map_add, map_sum, map_smul]; abel
    rw [hres, inner_sub_right, inner_sum]
    congr 1
    simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, inner_smul_right]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hL : Submodule.span 𝕜 (Set.range fun i => (W i : F)) = L := by
    have himg : (L.subtype '' Set.range W) = Set.range fun i => (W i : F) := by
      rw [← Set.range_comp]; rfl
    rw [← himg, ← Submodule.map_span, W.span_eq, Submodule.map_top, Submodule.range_subtype]
  constructor
  · intro h
    funext i
    have h0 := (Submodule.mem_orthogonal _ _).1 h.orth (W i : F) (W i).2
    rw [hinner i] at h0
    exact (sub_eq_zero.1 h0).symm
  · intro h
    refine ⟨hmem, ?_⟩
    rw [← hL, Submodule.mem_orthogonal_span]
    rintro _ ⟨i, rfl⟩
    rw [hinner i, congrFun h i, sub_self]

end MatrixForm

section Projected

/-!
### The general error bound

The projection step with $x_0 = 0$ is the equation $A_m x = Qb$ on $K$. Here $Q$ is a projector of
$E$ onto $K$, and $A_m = Q A|_K$ (`compressionBy Q A`) is the compression of $A$ through $Q$. In
[saad2003iterative], §5.2.3, $Q = Q_K^L$ is the oblique projector onto $K$ along $L^\perp$, which
exists exactly under the nondegeneracy condition of [saad2003iterative], Proposition 5.1. The bound
below says that the exact solution $x^*$ almost solves this equation, with a defect controlled by
the part of $x^*$ that $K$ misses.
-/

namespace IsPetrovGalerkin

/-- **The general error bound** ([saad2003iterative], Theorem 5.7). Let $A : E \to E$ be linear, and
let $K$ be a subspace with orthogonal projection $P_K$. Let $Q : E \to K$ be linear with
$Qz = z$ for $z \in K$, and let $A_m = Q A|_K$ be the compression of $A$ through $Q$. Let
$\gamma \in \mathbb{R}$ satisfy $\|QAz\| \le \gamma \|z\|$ for all $z \in K^\perp$. If $b \in K$
and $Ax^* = b$, then
$$\|b - A_m P_K x^*\| \le \gamma\, \|(I - P_K) x^*\|.$$

The hypothesis $b \in K$ is in the source, and it gives $Qb = b$. It holds for the Krylov choice
$K = \mathcal{K}_m(A, b)$ with $x_0 = 0$. The source takes $\gamma = \|QA(I - P_K)\|$. A
hypothesis on $\gamma$ in place of an operator norm keeps the statement valid for an unbounded
$A$ and for the sharper values of $\gamma$ that a particular $K$ gives. The proof uses the
identity $b - A_m P_K x^* = QA(I - P_K)x^*$. The eigenvalue analogue is
`Krylov.compression_residual_le`, with the same form of hypothesis on $\gamma$. -/
theorem norm_residual_projected_le {A : E →ₗ[𝕜] E} {b : E} {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {Q : E →ₗ[𝕜] K} (hQ : ∀ z : K, Q z = z) (hb : b ∈ K) {γ : ℝ}
    (hγ : ∀ z ∈ Kᗮ, ‖(Q (A z) : E)‖ ≤ γ * ‖z‖) {xstar : E} (hstar : A xstar = b) :
    ‖b - (compressionBy Q A (K.orthogonalProjectionOnto xstar) : E)‖
      ≤ γ * ‖xstar - K.starProjection xstar‖ := by
  have hQb : (Q b : E) = b := congrArg Subtype.val (hQ ⟨b, hb⟩)
  have key : b - (compressionBy Q A (K.orthogonalProjectionOnto xstar) : E)
      = (Q (A (xstar - K.starProjection xstar)) : E) := by
    have h1 : (Q (A (xstar - K.starProjection xstar)) : E)
        = (Q (A xstar) : E) - (Q (A (K.starProjection xstar)) : E) := by
      rw [map_sub, map_sub, Submodule.coe_sub]
    rw [h1, hstar, hQb]
    rfl
  rw [key]
  exact hγ _ (K.sub_starProjection_mem_orthogonal xstar)

end IsPetrovGalerkin

end Projected
