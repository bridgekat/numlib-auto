/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.TietzeExtension
import Numlib.Approximation.Chebyshev

/-!
# The abstract interpolation problem

Let $V_n$ be a subspace of a normed space $V$ over a field $\mathbb{K}$, and let $L_1, \dots, L_n$
be bounded linear functionals on $V$. The **interpolation problem** asks, for given data
$b \in \mathbb{K}^n$, for an element $u \in V_n$ with $L_i u = b_i$ for all $i$. The problem is
**unisolvent** if it has exactly one solution for every $b$. This file follows §3.2 and §3.3.4 of
[han2009theoretical].

When $V_n$ has dimension $n$ and $v_1, \dots, v_n$ is a basis, the problem is the linear system with
matrix $(L_i v_j)$, so it is unisolvent if and only if $\det(L_i v_j) \neq 0$. For point evaluations
$L_i f = f(x_i)$ on the space $C(X)$ of continuous real functions on a compact space $X$, a
unisolvent problem has a **cardinal basis** $\varphi_1, \dots, \varphi_n$ with
$\varphi_i(x_j) = \delta_{ij}$, and the **interpolation projection** $I f = \sum_i f(x_i) \varphi_i$
is a bounded projection of $C(X)$ onto the subspace. Its operator norm is the largest value of the
**Lebesgue function** $t \mapsto \sum_i |\varphi_i(t)|$.

## Main definitions

* `Approximation.interpMap`: the linear map $u \mapsto (L_1 u, \dots, L_n u)$ from $V_n$ to
  $\mathbb{K}^n$.
* `Approximation.IsUnisolvent`: the interpolation problem has exactly one solution for every datum.
* `Approximation.IsUnisolvent.interpolate`: the interpolation operator, a linear equivalence from
  the data to $V_n$.
* `Approximation.IsUnisolvent.cardinalBasisCM`: the cardinal basis $\varphi_i$ of a unisolvent
  point-evaluation problem on $C(X)$.
* `Approximation.IsUnisolvent.interpCLM`: the interpolation projection
  $f \mapsto \sum_i f(x_i) \varphi_i$.

## Main results

* `Approximation.isUnisolvent_iff_det_ne_zero`: for a basis $(v_j)$ of $V_n$, the problem is
  unisolvent if and only if $\det(L_i v_j) \neq 0$.
* `Approximation.isUnisolvent_tfae`: unique solvability, linear independence of the functionals on
  $V_n$, triviality of the homogeneous problem, and solvability for every datum are equivalent.
* `Approximation.IsUnisolvent.range_interpCLM`,
  `Approximation.IsUnisolvent.isIdempotentElem_interpCLM`: the interpolation projection is a bounded
  projection of $C(X)$ onto the subspace.
* `Approximation.IsUnisolvent.isGreatest_norm_interpCLM`,
  `Approximation.IsUnisolvent.norm_interpCLM`: the operator norm of the interpolation projection is
  the largest value of its Lebesgue function.
* `Approximation.haarCondition_iff_isUnisolvent`: an $n$-dimensional subspace of $C(X)$ satisfies
  the Haar condition if and only if the interpolation problem at every $n$ distinct points is
  unisolvent.

## Implementation notes

* The functionals are a family `L : Fin n → StrongDual 𝕜 V`, and the data are `b : Fin n → 𝕜`.
* Since unisolvence does not mention a basis, the determinant criterion shows that the nonvanishing
  of $\det(L_i v_j)$ does not depend on the choice of the basis.
* The Haar condition is `HaarCondition` of `Numlib.Approximation.Chebyshev`. It and unisolvence both
  say that a nonzero element of the subspace has fewer than $n$ zeros.
* The interpolation projection `Approximation.IsUnisolvent.interpCLM` is the general form of the
  Lagrange interpolation operator of `Numlib.Approximation.Interpolation`. It gives a projection
  onto a Haar subspace with no formula for a cardinal basis.
* The Lebesgue constant of the interpolation scheme is the quantity in which the uniform error
  bounds of §3.7.3 of [han2009theoretical] are stated.
-/

open scoped Matrix

namespace Approximation

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {n : ℕ}

/-- The **interpolation map** of a family of functionals $L_1, \dots, L_n$ on a subspace $V_n$: the
linear map $u \mapsto (L_1 u, \dots, L_n u)$ from $V_n$ to $\mathbb{K}^n$. The interpolation
problem for the data $b$ is the equation `Approximation.interpMap Vₙ L u = b`. -/
def interpMap (Vₙ : Submodule 𝕜 V) (L : Fin n → StrongDual 𝕜 V) : Vₙ →ₗ[𝕜] Fin n → 𝕜 where
  toFun u i := L i (u : V)
  map_add' u u' := by ext i; simp
  map_smul' c u := by ext i; simp

/-- The $i$-th component of the interpolation map at $u$ is $L_i u$. -/
@[simp]
theorem interpMap_apply (Vₙ : Submodule 𝕜 V) (L : Fin n → StrongDual 𝕜 V) (u : Vₙ)
    (i : Fin n) : interpMap Vₙ L u i = L i (u : V) := rfl

/-- The interpolation problem for the functionals $L_1, \dots, L_n$ on the subspace $V_n$ is
**unisolvent** if for every datum $b \in \mathbb{K}^n$ there is exactly one $u \in V_n$ with
$$L_i u = b_i \quad \text{for all } i = 1, \dots, n.$$

This is Definition 3.2.1 of [han2009theoretical], in the form of unique solvability. Theorem
3.2.3 of [han2009theoretical] gives the equivalent forms (`Approximation.isUnisolvent_tfae`). -/
def IsUnisolvent (Vₙ : Submodule 𝕜 V) (L : Fin n → StrongDual 𝕜 V) : Prop :=
  ∀ b : Fin n → 𝕜, ∃! u : Vₙ, ∀ i, L i (u : V) = b i

variable {Vₙ : Submodule 𝕜 V} {L : Fin n → StrongDual 𝕜 V}

/-- The interpolation problem is unisolvent if and only if the interpolation map
$u \mapsto (L_i u)_i$ is bijective. -/
theorem isUnisolvent_iff_bijective :
    IsUnisolvent Vₙ L ↔ Function.Bijective (interpMap Vₙ L) := by
  rw [Function.bijective_iff_existsUnique]
  exact forall_congr' fun b => existsUnique_congr fun u => (funext_iff (g := b)).symm

/-! ### The matrix of the problem in a basis -/

section Matrix

variable (v : Module.Basis (Fin n) 𝕜 Vₙ)

include v

/-- Let $v_1, \dots, v_n$ be a basis of $V_n$. For $u \in V_n$ with coordinates $c$ in this basis,
the interpolation map at $u$ is the matrix-vector product $(L_i v_j)_{ij}\, c$. -/
theorem interpMap_eq_mulVec (u : Vₙ) :
    interpMap Vₙ L u = (Matrix.of fun i j => L i (v j : V)) *ᵥ v.equivFun u := by
  have hu : (u : V) = ∑ j, v.equivFun u j • (v j : V) := by
    have h := map_sum Vₙ.subtype (fun j => v.equivFun u j • v j) Finset.univ
    rw [v.sum_equivFun u] at h
    exact h
  funext i
  rw [interpMap_apply, hu, map_sum]
  simp only [map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- For a basis $(v_j)$ of $V_n$, the interpolation map is the composition of the coordinate
isomorphism of the basis with multiplication by the matrix $(L_i v_j)$. -/
private theorem coe_interpMap_eq :
    ⇑(interpMap Vₙ L) = (Matrix.of fun i j => L i (v j : V)).mulVec ∘ v.equivFun :=
  funext fun u => interpMap_eq_mulVec v u

/-- For a basis $(v_j)$ of $V_n$, the interpolation map is injective if and only if the matrix
$(L_i v_j)$ is invertible. -/
private theorem injective_interpMap_iff_isUnit :
    Function.Injective (interpMap Vₙ L) ↔ IsUnit (Matrix.of fun i j => L i (v j : V)) := by
  classical
  rw [coe_interpMap_eq v, Function.Injective.of_comp_iff' _ v.equivFun.bijective,
    Matrix.mulVec_injective_iff_isUnit]

/-- For a basis $(v_j)$ of $V_n$, the interpolation map is surjective if and only if the matrix
$(L_i v_j)$ is invertible. -/
private theorem surjective_interpMap_iff_isUnit :
    Function.Surjective (interpMap Vₙ L) ↔ IsUnit (Matrix.of fun i j => L i (v j : V)) := by
  classical
  rw [coe_interpMap_eq v, Function.Surjective.of_comp_iff _ v.equivFun.surjective,
    Matrix.mulVec_surjective_iff_isUnit]

/-- For a basis $(v_j)$ of $V_n$, the interpolation problem is unisolvent if and only if the matrix
$(L_i v_j)$ is invertible. -/
theorem isUnisolvent_iff_isUnit :
    IsUnisolvent Vₙ L ↔ IsUnit (Matrix.of fun i j => L i (v j : V)) := by
  rw [isUnisolvent_iff_bijective]
  exact ⟨fun h => (injective_interpMap_iff_isUnit v).1 h.1,
    fun h => ⟨(injective_interpMap_iff_isUnit v).2 h, (surjective_interpMap_iff_isUnit v).2 h⟩⟩

/-- **The determinant criterion.** Let $V_n$ have a basis $v_1, \dots, v_n$, so that $\dim V_n = n$.
The interpolation problem for $L_1, \dots, L_n$ on $V_n$ is unisolvent if and only if
$$\det (L_i v_j)_{i,j=1}^n \neq 0.$$

This is Lemma 3.2.2 of [han2009theoretical]. Since unisolvence does not mention the basis, the
nonvanishing of the determinant does not depend on the choice of the basis. -/
theorem isUnisolvent_iff_det_ne_zero :
    IsUnisolvent Vₙ L ↔ (Matrix.of fun i j => L i (v j : V)).det ≠ 0 := by
  classical
  rw [isUnisolvent_iff_isUnit v, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- **The homogeneous form.** Let $V_n$ have a basis $v_1, \dots, v_n$. The interpolation problem is
unisolvent if and only if the only $u \in V_n$ with $L_i u = 0$ for all $i$ is $u = 0$.

This is part of Theorem 3.2.3 of [han2009theoretical]. -/
theorem isUnisolvent_iff_forall_eq_zero :
    IsUnisolvent Vₙ L ↔ ∀ u : Vₙ, (∀ i, L i (u : V) = 0) → u = 0 := by
  rw [isUnisolvent_iff_isUnit v, ← injective_interpMap_iff_isUnit v,
    injective_iff_map_eq_zero (interpMap Vₙ L)]
  exact forall_congr' fun u => imp_congr_left (funext_iff (g := (0 : Fin n → 𝕜)))

/-- **The solvability form.** Let $V_n$ have a basis $v_1, \dots, v_n$. The interpolation problem is
unisolvent if and only if for every datum $b \in \mathbb{K}^n$ there is some $u \in V_n$ with
$L_i u = b_i$ for all $i$. Thus, for $n$ functionals on an $n$-dimensional subspace, existence
of a solution implies its uniqueness. This is part of Theorem 3.2.3 of [han2009theoretical]. -/
theorem isUnisolvent_iff_forall_exists :
    IsUnisolvent Vₙ L ↔ ∀ b : Fin n → 𝕜, ∃ u : Vₙ, ∀ i, L i (u : V) = b i := by
  rw [isUnisolvent_iff_isUnit v, ← surjective_interpMap_iff_isUnit v]
  refine ⟨fun h b => ?_, fun h b => ?_⟩
  · obtain ⟨u, hu⟩ := h b
    exact ⟨u, fun i => congrFun hu i⟩
  · obtain ⟨u, hu⟩ := h b
    exact ⟨u, funext hu⟩

/-- **Linear independence of the functionals.** Let $V_n$ have a basis $v_1, \dots, v_n$. The
interpolation problem is unisolvent if and only if the restrictions of $L_1, \dots, L_n$ to
$V_n$ are linearly independent linear functionals on $V_n$.

This is the form of the definition in Definition 3.2.1 of [han2009theoretical], and its
equivalence with unique solvability is part of Theorem 3.2.3 of [han2009theoretical]. -/
theorem isUnisolvent_iff_linearIndependent :
    IsUnisolvent Vₙ L ↔
      LinearIndependent 𝕜 fun i => (L i : V →ₗ[𝕜] 𝕜).domRestrict Vₙ := by
  classical
  set M : Matrix (Fin n) (Fin n) 𝕜 := Matrix.of fun i j => L i (v j : V)
  have hrow : (fun i => (L i : V →ₗ[𝕜] 𝕜).domRestrict Vₙ) = fun i => v.constr 𝕜 (M.row i) := by
    funext i
    exact v.ext fun j => (v.constr_basis 𝕜 (M.row i) j).symm
  have hinjc : Function.Injective ⇑(v.constr (M' := 𝕜) 𝕜).toLinearMap :=
    (v.constr (M' := 𝕜) 𝕜).injective
  have hker : LinearMap.ker (v.constr (M' := 𝕜) 𝕜).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot_of_injective hinjc
  rw [isUnisolvent_iff_isUnit v, hrow, ← Matrix.linearIndependent_row_iff_isUnit]
  exact ⟨fun h => h.map' _ hker, fun h => h.of_comp (v.constr (M' := 𝕜) 𝕜).toLinearMap⟩

/-- **The four equivalent forms of unisolvence.** Let $V_n$ have a basis $v_1, \dots, v_n$. The
following are equivalent:

1. the interpolation problem is unisolvent: for every $b \in \mathbb{K}^n$ there is exactly one
   $u \in V_n$ with $L_i u = b_i$ for all $i$;
2. the restrictions of $L_1, \dots, L_n$ to $V_n$ are linearly independent;
3. if $u \in V_n$ and $L_i u = 0$ for all $i$, then $u = 0$;
4. for every $b \in \mathbb{K}^n$ there is some $u \in V_n$ with $L_i u = b_i$ for all $i$.

This is Theorem 3.2.3 of [han2009theoretical]. -/
theorem isUnisolvent_tfae :
    List.TFAE
      [IsUnisolvent Vₙ L,
        LinearIndependent 𝕜 fun i => (L i : V →ₗ[𝕜] 𝕜).domRestrict Vₙ,
        ∀ u : Vₙ, (∀ i, L i (u : V) = 0) → u = 0,
        ∀ b : Fin n → 𝕜, ∃ u : Vₙ, ∀ i, L i (u : V) = b i] := by
  tfae_have 1 ↔ 2 := isUnisolvent_iff_linearIndependent v
  tfae_have 1 ↔ 3 := isUnisolvent_iff_forall_eq_zero v
  tfae_have 1 ↔ 4 := isUnisolvent_iff_forall_exists v
  tfae_finish

end Matrix

/-! ### The interpolation operator -/

/-- **The interpolation operator** of a unisolvent problem: the linear equivalence from
$\mathbb{K}^n$ to $V_n$ that maps the data $b$ to the unique $u \in V_n$ with $L_i u = b_i$ for
all $i$.

This is the operator of (3.2.3) of [han2009theoretical]. It is the inverse of the interpolation
map `Approximation.interpMap`. -/
noncomputable def IsUnisolvent.interpolate (h : IsUnisolvent Vₙ L) : (Fin n → 𝕜) ≃ₗ[𝕜] Vₙ :=
  (LinearEquiv.ofBijective (interpMap Vₙ L) (isUnisolvent_iff_bijective.mp h)).symm

/-- For a unisolvent problem and data $b$, the interpolant $u$ of $b$ satisfies $L_i u = b_i$ for
every $i$. -/
@[simp]
theorem IsUnisolvent.apply_interpolate (h : IsUnisolvent Vₙ L) (b : Fin n → 𝕜) (i : Fin n) :
    L i ((h.interpolate b : Vₙ) : V) = b i := by
  have := (LinearEquiv.ofBijective (interpMap Vₙ L)
    (isUnisolvent_iff_bijective.mp h)).apply_symm_apply b
  exact congrFun this i

/-- For a unisolvent problem, if $u \in V_n$ satisfies $L_i u = b_i$ for all $i$, then $u$ is the
interpolant of $b$. -/
theorem IsUnisolvent.eq_interpolate (h : IsUnisolvent Vₙ L) {b : Fin n → 𝕜} {u : Vₙ}
    (hu : ∀ i, L i (u : V) = b i) : u = h.interpolate b :=
  ((h b).unique hu) fun i => h.apply_interpolate b i

/-! ### The interpolation projection at unisolvent nodes -/

section InterpCLM

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] {d : ℕ}
  {W : Submodule ℝ C(X, ℝ)} {x : Fin d → X}

/-- The **cardinal basis** of a unisolvent point-evaluation problem. Let $X$ be a compact space, let
$W$ be a subspace of $C(X)$, and let $x_1, \dots, x_d \in X$ be nodes at which the interpolation
problem $f(x_i) = b_i$ on $W$ is unisolvent. The function $\varphi_i$ is the unique element of
$W$ with $\varphi_i(x_i) = 1$ and $\varphi_i(x_j) = 0$ for $j \neq i$.

For polynomials, $\varphi_i$ is the $i$-th Lagrange basis function. -/
noncomputable def IsUnisolvent.cardinalBasisCM
    (h : IsUnisolvent W fun i => ContinuousMap.evalCLM ℝ (x i)) (i : Fin d) : C(X, ℝ) :=
  (h.interpolate (Pi.single i 1) : C(X, ℝ))

/-- Each cardinal basis function $\varphi_i$ lies in the subspace $W$. -/
theorem IsUnisolvent.cardinalBasisCM_mem
    (h : IsUnisolvent W fun i => ContinuousMap.evalCLM ℝ (x i)) (i : Fin d) :
    h.cardinalBasisCM i ∈ W :=
  (h.interpolate (Pi.single i 1)).2

/-- The cardinal basis function $\varphi_i$ takes the value $\varphi_i(x_j) = \delta_{ij}$ at the
node $x_j$. -/
@[simp]
theorem IsUnisolvent.cardinalBasisCM_apply_node
    (h : IsUnisolvent W fun i => ContinuousMap.evalCLM ℝ (x i)) (i j : Fin d) :
    h.cardinalBasisCM i (x j) = if j = i then 1 else 0 := by
  have := h.apply_interpolate (Pi.single i (1 : ℝ)) j
  simpa [IsUnisolvent.cardinalBasisCM, Pi.single_apply] using this

/-- **The interpolation projection** of a unisolvent point-evaluation problem on a subspace $W$ of
$C(X)$, with nodes $x_1, \dots, x_d$ and cardinal basis $\varphi_1, \dots, \varphi_d$: the
bounded linear operator
$$I f = \sum_{i=1}^d f(x_i)\, \varphi_i$$
on $C(X)$. It is a projection onto $W$ (`Approximation.IsUnisolvent.range_interpCLM`,
`Approximation.IsUnisolvent.isIdempotentElem_interpCLM`). -/
noncomputable def IsUnisolvent.interpCLM
    (h : IsUnisolvent W fun i => ContinuousMap.evalCLM ℝ (x i)) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  ∑ i, (ContinuousMap.evalCLM ℝ (x i)).smulRight (h.cardinalBasisCM i)

/-- The interpolation projection at a point $t$ is $I f(t) = \sum_i f(x_i)\, \varphi_i(t)$. -/
theorem IsUnisolvent.interpCLM_apply
    (h : IsUnisolvent W fun i => ContinuousMap.evalCLM ℝ (x i)) (f : C(X, ℝ)) (t : X) :
    h.interpCLM f t = ∑ i, f (x i) * h.cardinalBasisCM i t := by
  simp [IsUnisolvent.interpCLM]

/-- For every $f \in C(X)$, the interpolant $I f$ lies in the subspace $W$. -/
theorem IsUnisolvent.interpCLM_mem
    (h : IsUnisolvent W fun i => ContinuousMap.evalCLM ℝ (x i)) (f : C(X, ℝ)) :
    h.interpCLM f ∈ W := by
  have : h.interpCLM f = ∑ i, f (x i) • h.cardinalBasisCM i := by
    ext t; simp [IsUnisolvent.interpCLM_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h.cardinalBasisCM_mem i)

/-- The interpolant agrees with $f$ at the nodes: $I f(x_j) = f(x_j)$ for every $j$. -/
@[simp]
theorem IsUnisolvent.interpCLM_apply_node
    (h : IsUnisolvent W fun i => ContinuousMap.evalCLM ℝ (x i)) (f : C(X, ℝ)) (j : Fin d) :
    h.interpCLM f (x j) = f (x j) := by
  rw [IsUnisolvent.interpCLM_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Ne.symm hij]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The interpolation projection fixes the subspace: if $g \in W$, then $I g = g$. -/
theorem IsUnisolvent.interpCLM_eq_self
    (h : IsUnisolvent W fun i => ContinuousMap.evalCLM ℝ (x i)) {g : C(X, ℝ)} (hg : g ∈ W) :
    h.interpCLM g = g := by
  have h1 : (⟨h.interpCLM g, h.interpCLM_mem g⟩ : W) = h.interpolate fun i => g (x i) :=
    h.eq_interpolate fun i => h.interpCLM_apply_node g i
  have h2 : (⟨g, hg⟩ : W) = h.interpolate fun i => g (x i) :=
    h.eq_interpolate fun _ => rfl
  exact congrArg Subtype.val (h1.trans h2.symm)

/-- The interpolation projection is idempotent: $I \circ I = I$. -/
theorem IsUnisolvent.isIdempotentElem_interpCLM
    (h : IsUnisolvent W fun i => ContinuousMap.evalCLM ℝ (x i)) :
    IsIdempotentElem h.interpCLM :=
  ContinuousLinearMap.ext fun f => h.interpCLM_eq_self (h.interpCLM_mem f)

/-- The range of the interpolation projection $I$ is the subspace $W$. -/
theorem IsUnisolvent.range_interpCLM
    (h : IsUnisolvent W fun i => ContinuousMap.evalCLM ℝ (x i)) :
    LinearMap.range (h.interpCLM : C(X, ℝ) →ₗ[ℝ] C(X, ℝ)) = W := by
  apply le_antisymm
  · rintro g ⟨f, rfl⟩
    exact h.interpCLM_mem f
  · intro g hg
    exact ⟨g, h.interpCLM_eq_self hg⟩

/-- **The Lebesgue constant of an interpolation projection.** Let $X$ be a nonempty compact
Hausdorff space, and let the point-evaluation problem at the nodes $x_1, \dots, x_d$ be
unisolvent on a subspace $W$ of $C(X)$, with cardinal basis $\varphi_1, \dots, \varphi_d$. The
operator norm of the interpolation projection $I$ is the largest value of its **Lebesgue
function**:
$$\|I\| = \max_{t \in X} \sum_{i=1}^d |\varphi_i(t)|,$$
and the maximum is attained.

This is the Lebesgue constant of §3.7.3 of [han2009theoretical]. The upper bound is the triangle
inequality. For the lower bound, the combination $\sum_i \operatorname{sign}(\varphi_i(t_0))\,
\varphi_i$ takes the values $\operatorname{sign}(\varphi_i(t_0))$ at the nodes, and the Tietze
extension theorem replaces it by a continuous function with the same values at the nodes and
with values in $[-1, 1]$. -/
theorem IsUnisolvent.isGreatest_norm_interpCLM [Nonempty X] [T2Space X]
    (h : IsUnisolvent W fun i => ContinuousMap.evalCLM ℝ (x i)) :
    IsGreatest (Set.range fun t : X => ∑ i, |h.cardinalBasisCM i t|) ‖h.interpCLM‖ := by
  classical
  have hcont : Continuous fun t : X => ∑ i, |h.cardinalBasisCM i t| :=
    continuous_finsetSum _ fun i _ => (h.cardinalBasisCM i).continuous.abs
  obtain ⟨t₀, -, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  set M : ℝ := ∑ i, |h.cardinalBasisCM i t₀| with hM
  have hmax' : ∀ t : X, (∑ i, |h.cardinalBasisCM i t|) ≤ M := fun t => hmax (Set.mem_univ t)
  have hMnn : (0 : ℝ) ≤ M := by
    rw [hM]
    positivity
  -- the upper bound
  have hle : ‖h.interpCLM‖ ≤ M := by
    refine ContinuousLinearMap.opNorm_le_bound _ hMnn fun f => ?_
    rw [ContinuousMap.norm_le _ (by positivity)]
    intro t
    rw [Real.norm_eq_abs, IsUnisolvent.interpCLM_apply]
    calc |∑ i, f (x i) * h.cardinalBasisCM i t| ≤ ∑ i, |f (x i) * h.cardinalBasisCM i t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |f (x i)| * |h.cardinalBasisCM i t| := by simp [abs_mul]
      _ ≤ ∑ i, ‖f‖ * |h.cardinalBasisCM i t| := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hfi := f.norm_coe_le_norm (x i)
          rw [Real.norm_eq_abs] at hfi
          exact mul_le_mul_of_nonneg_right hfi (abs_nonneg _)
      _ = ‖f‖ * ∑ i, |h.cardinalBasisCM i t| := by rw [Finset.mul_sum]
      _ ≤ M * ‖f‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (hmax' t) (norm_nonneg _)
  -- the lower bound
  have hge : M ≤ ‖h.interpCLM‖ := by
    set σ : Fin d → ℝ := fun i => if 0 ≤ h.cardinalBasisCM i t₀ then 1 else -1 with hσ
    have hσmul : ∀ i, σ i * h.cardinalBasisCM i t₀ = |h.cardinalBasisCM i t₀| := by
      intro i
      by_cases hb : 0 ≤ h.cardinalBasisCM i t₀
      · simp [hσ, hb, abs_of_nonneg hb]
      · simp [hσ, hb, abs_of_neg (not_le.mp hb)]
    have hσmem : ∀ i, σ i ∈ Set.Icc (-1 : ℝ) 1 := by
      intro i
      by_cases hb : 0 ≤ h.cardinalBasisCM i t₀ <;> simp [hσ, hb, Set.mem_Icc]
    set g : C(X, ℝ) := ∑ i, σ i • h.cardinalBasisCM i with hg
    have hnode : ∀ j, g (x j) = σ j := by
      intro j
      rw [hg]
      simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
        IsUnisolvent.cardinalBasisCM_apply_node]
      simp
    have hclosed : IsClosed (Set.range x) := (Set.finite_range x).isClosed
    have hrange : ∀ u : (Set.range x : Set X),
        (g.restrict (Set.range x)) u ∈ Set.Icc (-1 : ℝ) 1 := by
      rintro ⟨-, i, rfl⟩
      rw [ContinuousMap.restrict_apply, hnode i]
      exact hσmem i
    obtain ⟨f, hfmem, hfeq⟩ := ContinuousMap.exists_restrict_eq_forall_mem_of_closed
      (g.restrict (Set.range x)) hrange ⟨0, by norm_num⟩ hclosed
    have hfnode : ∀ j, f (x j) = σ j := by
      intro j
      have hcongr := congrArg (fun G : C((Set.range x : Set X), ℝ) => G ⟨x j, ⟨j, rfl⟩⟩) hfeq
      simp only [ContinuousMap.restrict_apply] at hcongr
      rw [hcongr, hnode j]
    have hfnorm : ‖f‖ ≤ 1 := by
      rw [ContinuousMap.norm_le _ zero_le_one]
      intro u
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨(hfmem u).1, (hfmem u).2⟩
    have hval : h.interpCLM f t₀ = M := by
      rw [IsUnisolvent.interpCLM_apply, hM]
      exact Finset.sum_congr rfl fun i _ => by rw [hfnode i, hσmul i]
    calc M = |h.interpCLM f t₀| := by rw [hval, abs_of_nonneg hMnn]
      _ ≤ ‖h.interpCLM f‖ := by
          have hb := (h.interpCLM f).norm_coe_le_norm t₀
          rwa [Real.norm_eq_abs] at hb
      _ ≤ ‖h.interpCLM‖ * ‖f‖ := h.interpCLM.le_opNorm f
      _ ≤ ‖h.interpCLM‖ * 1 := mul_le_mul_of_nonneg_left hfnorm (norm_nonneg _)
      _ = ‖h.interpCLM‖ := mul_one _
  exact ⟨⟨t₀, (le_antisymm hle hge).symm⟩, by rintro _ ⟨t, rfl⟩; exact (hmax' t).trans hge⟩

/-- Let $X$ be a nonempty compact Hausdorff space, and let the point-evaluation problem at the nodes
$x_1, \dots, x_d$ be unisolvent on a subspace $W$ of $C(X)$. The operator norm of the
interpolation projection is the supremum of its Lebesgue function:
$$\|I\| = \sup_{t \in X} \sum_{i=1}^d |\varphi_i(t)|.$$
-/
theorem IsUnisolvent.norm_interpCLM [Nonempty X] [T2Space X]
    (h : IsUnisolvent W fun i => ContinuousMap.evalCLM ℝ (x i)) :
    ‖h.interpCLM‖ = sSup (Set.range fun t : X => ∑ i, |h.cardinalBasisCM i t|) :=
  h.isGreatest_norm_interpCLM.csSup_eq.symm

end InterpCLM

/-! ### The Haar condition -/

/-- **The Haar condition is unisolvence at every family of distinct points.** Let $X$ be a compact
space, and let $V_n$ be a subspace of $C(X)$ of dimension $n$. Then no nonzero element of $V_n$
vanishes at $n$ distinct points of $X$ (`HaarCondition`) if and only if, for all distinct points
$x_1, \dots, x_n \in X$, the interpolation problem $f(x_i) = b_i$ on $V_n$ is unisolvent.

This is the relation between the Haar condition and interpolation in §3.3.4 of
[han2009theoretical]. -/
theorem haarCondition_iff_isUnisolvent {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (Vₙ : Submodule ℝ C(X, ℝ)) [FiniteDimensional ℝ Vₙ] (hdim : Module.finrank ℝ Vₙ = n) :
    HaarCondition Vₙ n ↔
      ∀ x : Fin n → X, Function.Injective x →
        IsUnisolvent Vₙ fun i => ContinuousMap.evalCLM ℝ (x i) := by
  classical
  set v := Module.finBasisOfFinrankEq ℝ (Vₙ : Submodule ℝ C(X, ℝ)) hdim
  constructor
  · intro hhaar x hx
    refine (isUnisolvent_iff_forall_eq_zero v).mpr fun u hu => ?_
    by_contra hu0
    have hne : (u : C(X, ℝ)) ≠ 0 := fun h => hu0 (Subtype.ext h)
    have hzero : ∀ t ∈ Finset.univ.image x, (u : C(X, ℝ)) t = 0 := by
      rintro t ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
      exact hu i
    have hcard : (Finset.univ.image x).card = n := by
      rw [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
    exact absurd (hhaar _ u.2 hne _ hzero) (by omega)
  · intro huni g hg hg0 s hs
    by_contra hcard
    obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_lt hcard)
    set e := Finset.equivFinOfCardEq htcard
    set x : Fin n → X := fun i => ((e.symm i : t) : X)
    have hx : Function.Injective x := fun i j hij =>
      e.symm.injective (Subtype.ext hij)
    have huz := (isUnisolvent_iff_forall_eq_zero v).mp (huni x hx) ⟨g, hg⟩ fun i => by
      exact hs _ (hts (e.symm i).2)
    exact hg0 (by simpa using congrArg Subtype.val huz)

end Approximation
