/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Numlib.Analysis.InnerProductSpace.Spectrum
import Numlib.Krylov.Hessenberg
import Numlib.Krylov.Lanczos

/-!
# Krylov methods on singular and incompatible symmetric systems

This file studies the minimal-residual iteration for a symmetric operator $A$ that can be singular,
and for systems $Ax = b$ that can have no solution, following [choi2006iterative], Chapters 2 and 3.
The full Krylov space of $b$ leaves the range of $A$ only in the direction of $b$, so the grade of
$b$ is at most $\operatorname{rank} A + 1$, and at most $\operatorname{rank} A$ when
$b \in \operatorname{range} A$. Counted with eigenvalues, the grade is at most the number of nonzero
eigenvalues of $A$ when $b \in \operatorname{range} A$, and at most one more in general. Let $d$ be
the grade of $b$ and let $m \ge d$. If $b \in \operatorname{range} A$, the minimal-residual iterate
from $x_0 = 0$ at step $m$ is the minimum-norm solution $A^+ b$. In general, the residual of every
minimal-residual iterate at step $m$ is orthogonal to $\operatorname{range} A$, so the iterate
solves the least-squares problem over the whole space, and the minimal-residual iterate of least
norm (the specification of MINRES-QLP) is the minimum-norm least-squares solution $A^+ b$.

The file also reads the Givens rotations of `Numlib.Krylov.Hessenberg` in the Lanczos basis. The
residual norm after $m$ steps is $\|r_m\| = \|r_0\| \prod_{k<m} |s_k|$ with the Givens sines $s_k$.
The tridiagonal matrices $\bar T_m$ and $T_m$ satisfy every bound that $A$ satisfies. Consecutive
residuals satisfy $r_{m+1} = |s_m|^2 r_m - s_m g_m v_{m+1}$ ([choi2006iterative], Lemma 2.18), and
$A r_m$ has components only on the Lanczos vectors $v_m$ and $v_{m+1}$ ([choi2006iterative], Lemma
2.19).

## Main results

* `Krylov.grade_le_finrank_range`, `Krylov.grade_le_finrank_range_add_one`: the grade of $b$ is at
  most $\operatorname{rank} A$ if $b \in \operatorname{range} A$, and at most
  $\operatorname{rank} A + 1$ in general.
* `Krylov.grade_le_finrank_range_sub_algebraMap_add_one`: the grade is at most
  $\operatorname{rank}(A - cI) + 1$ for every scalar $c$.
* `Krylov.grade_le_card_of_mem_iSup_eigenspace`: a vector in the span of the eigenspaces of $t$
  scalars has grade at most $t$.
* `Lanczos.grade_le_card_eigenvalues_of_mem_range`, `Lanczos.grade_le_card_eigenvalues`: for
  symmetric $A$ in finite dimension, the grade is at most the number of nonzero eigenvalues if
  $b \in \operatorname{range} A$, and at most one more in general.
* `Krylov.IsMinResidualIterate.isLeast_norm_of_grade_le`: for $b \in \operatorname{range} A$, the
  minimal-residual iterate at the grade is the minimum-norm solution of $Ax = b$.
* `Krylov.IsMinResidualIterate.residual_mem_orthogonal_range_of_grade_le`,
  `Krylov.IsMinResidualIterate.norm_residual_le_of_grade_le`: at the grade, the residual is
  orthogonal to $\operatorname{range} A$, and the iterate minimizes $\|b - Ay\|$ over all $y$.
* `Krylov.IsMinResidualIterate.exists_generalizedInverse`: every minimal-residual iterate $x$ with
  $Ax \neq 0$ is $Xb$ for a $\{2,3\}$-inverse $X$ of $A$.
* `Krylov.IsMinNormMinResidualIterate.isLeast_norm_of_grade_le`: at the grade, the minimal-residual
  iterate of least norm is the minimum-norm least-squares solution.
* `Krylov.IsMinResidualIterate.norm_residual_eq_prod_givensS`:
  $\|r_m\| = \|r_0\| \prod_{k<m} |s_k|$.
* `Lanczos.norm_toEuclideanLin_tridiagExt_le`, `Lanczos.norm_toEuclideanLin_tridiag_le`: a bound
  $\|Az\| \le C \|z\|$ gives $\|\bar T_m y\| \le C \|y\|$ and $\|T_m y\| \le C \|y\|$.
* `Lanczos.residual_minRes_succ_eq`: the recurrence $r_{m+1} = |s_m|^2 r_m - s_m g_m v_{m+1}$.
* `Lanczos.apply_residual_minRes_eq`, `Lanczos.norm_apply_residual_minRes_eq`: $A r_m$ lies in the
  span of $v_m$ and $v_{m+1}$, with explicit coefficients and norm.

## Implementation notes

* The results on the specifications `Krylov.IsMinResidualIterate` and
  `Krylov.IsMinNormMinResidualIterate`, and the bounds on the tridiagonal matrices, need only the
  symmetry of $A$ and a finite-dimensional full Krylov space. The rank bounds and the eigenvalue
  counts assume that the whole space is finite-dimensional.
* The results on the minimum-norm solutions take the starting point $x_0 = 0$, so that the search
  space is $\mathcal{K}_m(A, b)$.
* The bounds on $A$, $\bar T_m$ and $T_m$ are stated as inequalities $\|Az\| \le C \|z\|$ for all
  $z$, so that no norm on the space of operators is needed.
-/

open Polynomial Krylov

namespace Krylov

/-! ### Termination of the Krylov sequence -/

section Grade

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- For every $i$, $A (A^i v) = A^{i+1} v$. -/
private theorem apply_pow_apply (A : Module.End K V) (v : V) (i : ℕ) :
    A ((A ^ i) v) = (A ^ (i + 1)) v := by rw [pow_succ']; rfl

/-- The full Krylov space leaves the range of $A$ only in the direction of $v$:
$$\mathcal{K}_\infty(A, v) \le K v + \operatorname{range} A.$$
Only the Krylov vector $A^0 v = v$ can lie outside $\operatorname{range} A$. -/
theorem fullSubspace_le_span_sup_range (A : Module.End K V) (v : V) :
    fullSubspace A v ≤ (K ∙ v) ⊔ LinearMap.range A := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  cases i with
  | zero => exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  | succ i => exact Submodule.mem_sup_right ⟨(A ^ i) v, apply_pow_apply A v i⟩

/-- If $v \in \operatorname{range} A$, then $\mathcal{K}_\infty(A, v) \le \operatorname{range} A$.
-/
theorem fullSubspace_le_range (A : Module.End K V) {v : V} (hv : v ∈ LinearMap.range A) :
    fullSubspace A v ≤ LinearMap.range A := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  cases i with
  | zero => exact hv
  | succ i => exact ⟨(A ^ i) v, apply_pow_apply A v i⟩

/-- Let $V$ be a finite-dimensional vector space over a field $K$, let $A$ be an endomorphism of
$V$, and let $v \in \operatorname{range} A$. Then
$$\operatorname{grade}(A, v) \le \operatorname{rank} A.$$
This is the compatible case of Proposition 2.2 and Corollary 2.3 of [choi2006iterative]: a
Krylov method started at a right-hand side in the range of $A$ terminates within
$\operatorname{rank} A$ steps.

The rank is `Module.finrank K (LinearMap.range A)`. -/
theorem grade_le_finrank_range [FiniteDimensional K V] (A : Module.End K V) {v : V}
    (hv : v ∈ LinearMap.range A) : grade A v ≤ Module.finrank K (LinearMap.range A) :=
  Submodule.finrank_mono (fullSubspace_le_range A hv)

/-- Let $V$ be a finite-dimensional vector space over a field $K$, let $A$ be an endomorphism of
$V$, and let $v \in V$. Then
$$\operatorname{grade}(A, v) \le \operatorname{rank} A + 1.$$
This is Corollary 2.3 of [choi2006iterative]: the Krylov sequence of any starting vector
terminates within $\operatorname{rank} A + 1$ steps.

The bound is one more than that of `Krylov.grade_le_finrank_range`, because $v$ need not lie in
the range of $A$. -/
theorem grade_le_finrank_range_add_one [FiniteDimensional K V] (A : Module.End K V) (v : V) :
    grade A v ≤ Module.finrank K (LinearMap.range A) + 1 := by
  have h1 : grade A v ≤ Module.finrank K ((K ∙ v) ⊔ LinearMap.range A : Submodule K V) :=
    Submodule.finrank_mono (fullSubspace_le_span_sup_range A v)
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (K ∙ v) (LinearMap.range A)
  have h3 : Module.finrank K (K ∙ v : Submodule K V) ≤ 1 := by
    rcases eq_or_ne v 0 with rfl | hv
    · rw [Submodule.span_zero_singleton K, finrank_bot]
      omega
    · exact le_of_eq (finrank_span_singleton hv)
  omega

/-- Let $V$ be a finite-dimensional vector space over a field $K$, let $A$ be an endomorphism of
$V$, and let $v \in V$. Then for every scalar $c \in K$,
$$\operatorname{grade}(A, v) \le \operatorname{rank}(A - cI) + 1.$$

This is `Krylov.grade_le_finrank_range_add_one` for $A - cI$, together with the shift invariance
of the grade (`Krylov.grade_add_algebraMap`). For a low-rank perturbation $A = I + E$ of the
identity, it bounds the number of steps of a Krylov method by $\operatorname{rank} E + 1$. This
is [golub2013matrix], Corollary 11.3.2, with the number of distinct eigenvalues replaced by a
rank. The shift $cI$ is `algebraMap K (Module.End K V) c`. -/
theorem grade_le_finrank_range_sub_algebraMap_add_one [FiniteDimensional K V]
    (A : Module.End K V) (v : V) (c : K) :
    grade A v ≤ Module.finrank K (LinearMap.range (A - algebraMap K (Module.End K V) c)) + 1 := by
  have h : grade (A - algebraMap K (Module.End K V) c) v = grade A v := by
    rw [sub_eq_add_neg, ← map_neg, grade_add_algebraMap]
  exact h ▸ grade_le_finrank_range_add_one _ v

/-- Let $A$ be an endomorphism of a vector space $V$ over a field $K$, let $v \in V$ have a
finite-dimensional full Krylov space, and let $S$ be a finite set of scalars. If $v$ lies in the
sum of the eigenspaces $\ker(A - \mu I)$ for $\mu \in S$, then
$$\operatorname{grade}(A, v) \le |S|.$$

The monic polynomial $\prod_{\mu \in S} (X - \mu)$ annihilates $v$. This is the algebraic core
of Theorem 2.4 of [choi2006iterative]. The symmetry of $A$ enters only through the spectral
decomposition, which puts $v$ in such a sum. -/
theorem grade_le_card_of_mem_iSup_eigenspace {A : Module.End K V} {v : V}
    [FiniteDimensional K (fullSubspace A v)] {S : Finset K}
    (hv : v ∈ ⨆ μ ∈ S, Module.End.eigenspace A μ) : grade A v ≤ S.card := by
  have hmonic : (∏ μ ∈ S, (X - C μ) : K[X]).Monic :=
    monic_prod_of_monic _ _ fun μ _ => monic_X_sub_C μ
  have hdeg : (∏ μ ∈ S, (X - C μ) : K[X]).natDegree = S.card := by
    rw [natDegree_prod _ _ fun μ _ => X_sub_C_ne_zero μ]
    simp
  have hker : (⨆ μ ∈ S, Module.End.eigenspace A μ) ≤
      LinearMap.ker (aeval A (∏ μ ∈ S, (X - C μ))) := by
    refine iSup_le fun μ => iSup_le fun hμ z hz => ?_
    obtain ⟨q, hq⟩ : (X - C μ) ∣ (∏ μ ∈ S, (X - C μ) : K[X]) := Finset.dvd_prod_of_mem _ hμ
    have hq' : (∏ μ ∈ S, (X - C μ) : K[X]) = q * (X - C μ) := by rw [hq]; ring
    have hz0 : aeval A (X - C μ) z = 0 := by
      have hev : A z = μ • z := Module.End.mem_eigenspace_iff.1 hz
      simp [hev]
    rw [LinearMap.mem_ker, hq', map_mul, Module.End.mul_apply, hz0, map_zero]
  refine (grade_le_iff A v).2 ((pow_apply_mem_subspace_iff_exists_monic A v _).2
    ⟨∏ μ ∈ S, (X - C μ), hmonic, hdeg, ?_⟩)
  exact LinearMap.mem_ker.1 (hker hv)

end Grade

/-!
### The minimal-residual iterate at termination

The specifications of `Numlib.Krylov.Iterate` search the affine space
$x_0 + \mathcal{K}_m(A, b - A x_0)$. The minimum-norm results of [choi2006iterative] are about the
start $x_0 = 0$, where the search space is $\mathcal{K}_m(A, b)$. The first private lemmas below
translate the general specifications to this start.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {A : E →ₗ[𝕜] E} {b x : E} {m : ℕ}

private theorem finiteDimensional_sub_apply_zero (A : E →ₗ[𝕜] E) (b : E)
    [FiniteDimensional 𝕜 (fullSubspace A b)] : FiniteDimensional 𝕜 (fullSubspace A (b - A 0)) := by
  rw [map_zero, sub_zero]
  infer_instance

private theorem isMinResidual_of_isMinResidualIterate_zero (hx : IsMinResidualIterate A b 0 m x) :
    IsMinResidual A b 0 (subspace A b m) x := by
  have h : IsMinResidual A b 0 (subspace A (b - A 0) m) x := hx
  rwa [map_zero, sub_zero] at h

private theorem isMinResidualIterate_zero_iff_sub_mem
    (hx : IsMinResidualIterate A b 0 m x) {y : E} :
    IsMinResidualIterate A b 0 m y ↔ y - x ∈ subspace A b m ⊓ LinearMap.ker A := by
  have h := isMinResidualIterate_iff_sub_mem (A := A) (b := b) (x₀ := 0) (m := m) (x := y) hx
  rwa [map_zero, sub_zero] at h

/-- If $A$ is symmetric, then $\operatorname{range} A \le (\ker A)^\perp$. -/
private theorem range_le_orthogonal_ker (hA : A.IsSymmetric) :
    LinearMap.range A ≤ (LinearMap.ker A)ᗮ := by
  rw [← hA.orthogonal_range]
  exact Submodule.le_orthogonal_orthogonal _

/-- Let $A$ be symmetric and $b \in \operatorname{range} A$. Then $A$ is injective on
$\mathcal{K}_m(A, b)$ for every $m$. The reason is that $\mathcal{K}_m(A, b)$ lies in
$(\ker A)^\perp$. -/
theorem injOn_subspace_of_mem_range (hA : A.IsSymmetric) (hb : b ∈ LinearMap.range A) (m : ℕ) :
    Set.InjOn A (subspace A b m : Set E) := by
  intro z hz w hw hzw
  have hker : z - w ∈ LinearMap.ker A := by
    rw [LinearMap.mem_ker, map_sub, hzw, sub_self]
  have horth : z - w ∈ (LinearMap.ker A)ᗮ :=
    subspace_le_orthogonal_ker hA hb m (Submodule.sub_mem _ hz hw)
  exact sub_eq_zero.1 ((inner_self_eq_zero (𝕜 := 𝕜)).1
    (Submodule.inner_right_of_mem_orthogonal hker horth))

namespace IsMinResidualIterate

/-- Let $A$ be symmetric, let $b \in \operatorname{range} A$ have a finite-dimensional full Krylov
space, and let $m$ be at least the grade of $b$. If $x$ is a minimal-residual iterate from
$x_0 = 0$ at step $m$, then $Ax = b$.

This is the exactness half of Theorem 2.25 of [choi2006iterative]: a compatible singular system
is solved exactly at termination. Symmetry and $b \in \operatorname{range} A$ put the whole
Krylov space in $(\ker A)^\perp$, and this gives the injectivity of $A$ on $\mathcal{K}_d(A, b)$
that `Krylov.IsMinResidualIterate.apply_eq_of_grade_le` needs. -/
theorem apply_eq_of_mem_range_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A b)]
    (hA : A.IsSymmetric) (hb : b ∈ LinearMap.range A) (hm : grade A b ≤ m)
    (hx : IsMinResidualIterate A b 0 m x) : A x = b := by
  have := finiteDimensional_sub_apply_zero A b
  refine hx.apply_eq_of_grade_le ?_ ?_
  · rw [map_zero, sub_zero]
    exact hm
  · rw [map_zero, sub_zero]
    exact injOn_subspace_of_mem_range hA hb _

/-- Let $A$ be symmetric, let $b \in \operatorname{range} A$ have a finite-dimensional full Krylov
space, and let $m$ be at least the grade of $b$. If $x$ is a minimal-residual iterate from
$x_0 = 0$ at step $m$, then $\|x\|$ is the least norm of a solution of $Ay = b$:
$$\|x\| = \min\{\|y\| : Ay = b\}.$$
This is Theorem 2.25 of [choi2006iterative].

Since $Ax = b$ (`Krylov.IsMinResidualIterate.apply_eq_of_mem_range_of_grade_le`), $x$ is the
minimum-norm solution, that is, the pseudoinverse solution $A^+ b$. The minimality is
`Krylov.norm_le_of_apply_eq`, which needs only $\mathcal{K}_m(A, b) \le (\ker A)^\perp$. The
statement is `IsLeast` of the set of norms of the solutions. -/
theorem isLeast_norm_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A b)] (hA : A.IsSymmetric)
    (hb : b ∈ LinearMap.range A) (hm : grade A b ≤ m) (hx : IsMinResidualIterate A b 0 m x) :
    IsLeast (norm '' {y : E | A y = b}) ‖x‖ := by
  have hAx : A x = b := apply_eq_of_mem_range_of_grade_le hA hb hm hx
  have hxm : x ∈ subspace A b m := by
    simpa using (isMinResidual_of_isMinResidualIterate_zero hx).mem
  refine ⟨⟨x, hAx, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact norm_le_of_apply_eq hA hxm hAx y hy

/-- Let $A$ be symmetric, let $b$ have a finite-dimensional full Krylov space, and let $m$ be at
least the grade of $b$. If $x$ is a minimal-residual iterate from $x_0 = 0$ at step $m$, then
the residual is in the kernel of $A$:
$$A (b - Ax) = 0.$$

The Krylov space $\mathcal{K}_m = \mathcal{K}_d$ is $A$-invariant and contains $b$ and $x$, so
it contains the residual $r = b - Ax$. By symmetry, the minimal-residual condition
$r \perp A \mathcal{K}_m$ becomes $A r \perp \mathcal{K}_m$, and $Ar \in \mathcal{K}_m \cap
\mathcal{K}_m^\perp = 0$. -/
theorem apply_residual_eq_zero_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A b)]
    (hA : A.IsSymmetric) (hm : grade A b ≤ m) (hx : IsMinResidualIterate A b 0 m x) :
    A (b - A x) = 0 := by
  have hx' := isMinResidual_of_isMinResidualIterate_zero hx
  have hKg : subspace A b m = fullSubspace A b := by
    rw [subspace_eq_of_grade_le A b hm, subspace_grade_eq_fullSubspace]
  have hinvt : ∀ z ∈ subspace A b m, A z ∈ subspace A b m := by
    rw [hKg]
    exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1
      (fullSubspace_mem_invtSubmodule A b)
  have hxm : x ∈ subspace A b m := by simpa using hx'.mem
  have hbm : b ∈ subspace A b m := by
    rw [hKg]
    exact Submodule.subset_span ⟨0, by simp⟩
  have hres : b - A x ∈ subspace A b m := Submodule.sub_mem _ hbm (hinvt x hxm)
  have horth : b - A x ∈ ((subspace A b m).map A)ᗮ := by
    have h := hx.residual_mem_orthogonal
    rwa [map_zero, sub_zero] at h
  have hAr : A (b - A x) ∈ (subspace A b m)ᗮ := by
    refine (Submodule.mem_orthogonal _ _).2 fun w hw => ?_
    rw [← hA w (b - A x)]
    exact (Submodule.mem_orthogonal _ _).1 horth (A w) (Submodule.mem_map_of_mem hw)
  exact (inner_self_eq_zero (𝕜 := 𝕜)).1
    (Submodule.inner_right_of_mem_orthogonal (hinvt _ hres) hAr)

/-- Let $A$ be symmetric, let $b$ have a finite-dimensional full Krylov space, and let $m$ be at
least the grade of $b$. If $x$ is a minimal-residual iterate from $x_0 = 0$ at step $m$, then
$$b - Ax \in (\operatorname{range} A)^\perp.$$
So $x$ satisfies the normal equations of the least-squares problem $\min_y \|b - Ay\|$, whether
the system $Ax = b$ has a solution or not. -/
theorem residual_mem_orthogonal_range_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A b)]
    (hA : A.IsSymmetric) (hm : grade A b ≤ m) (hx : IsMinResidualIterate A b 0 m x) :
    b - A x ∈ (LinearMap.range A)ᗮ := by
  refine (Submodule.mem_orthogonal _ _).2 ?_
  rintro _ ⟨u, rfl⟩
  rw [hA u (b - A x), apply_residual_eq_zero_of_grade_le hA hm hx, inner_zero_right]

/-- Let $A$ be symmetric, let $b$ have a finite-dimensional full Krylov space, and let $m$ be at
least the grade of $b$. If $x$ is a minimal-residual iterate from $x_0 = 0$ at step $m$, then
$x$ minimizes the residual over the whole space:
$$\|b - Ax\| \le \|b - Ay\| \quad \text{for all } y \in E.$$
This is the first half of Theorem 3.1 of [choi2006iterative].

So at termination the Krylov space is large enough to contain a least-squares solution. -/
theorem norm_residual_le_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A b)] (hA : A.IsSymmetric)
    (hm : grade A b ≤ m) (hx : IsMinResidualIterate A b 0 m x) (y : E) : ‖b - A x‖ ≤ ‖b - A y‖ := by
  have h0 : inner 𝕜 (b - A x) (A x - A y) = (0 : 𝕜) := by
    refine inner_eq_zero_symm.1 ?_
    exact (Submodule.mem_orthogonal _ _).1
      (residual_mem_orthogonal_range_of_grade_le hA hm hx) _ ⟨x - y, by rw [map_sub]⟩
  have hsplit : b - A y = (b - A x) + (A x - A y) := by abel
  have hsq : ‖b - A y‖ * ‖b - A y‖ = ‖b - A x‖ * ‖b - A x‖ + ‖A x - A y‖ * ‖A x - A y‖ := by
    rw [hsplit, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0]
  nlinarith [norm_nonneg (b - A x), norm_nonneg (b - A y), norm_nonneg (A x - A y)]

/-- Let $x$ be a minimal-residual iterate from $x_0 = 0$ at step $m$, and assume that $Ax \neq 0$.
Then $x = Xb$ for a $\{2,3\}$-inverse $X$ of $A$, that is, for a linear map $X$ with
$$XAX = X \quad \text{and} \quad AX \text{ symmetric}.$$
This is the $\{2,3\}$ half of Theorem 2.27 of [choi2006iterative].

The witness is the rank-one map $X z = (\langle Ax, z \rangle / \langle Ax, Ax \rangle)\, x$,
for which $AX$ is the orthogonal projection onto $\mathbb{K} Ax$. The only input is the
minimal-residual condition $\langle Ax, b - Ax \rangle = 0$, which every minimal-residual
iterate satisfies, so no termination hypothesis is needed. For the same reason the statement is
weak. The content of the theorem of [choi2006iterative] is the particular $X$ that the QLP
factorization gives, and the strengthening to a $\{1,2,3\}$-inverse ($AXA = A$) when
$\mathcal{K}_m$ contains $\operatorname{range} A$. Neither is formalized here. The hypothesis
$Ax \neq 0$ cannot be removed: for $A = 0$ the only $\{2,3\}$-inverse is $0$, so no nonzero $x$
has the form $Xb$. -/
theorem exists_generalizedInverse (hx : IsMinResidualIterate A b 0 m x) (hAx : A x ≠ 0) :
    ∃ X : E →ₗ[𝕜] E, X ∘ₗ A ∘ₗ X = X ∧ (A ∘ₗ X).IsSymmetric ∧ X b = x := by
  have hne : inner 𝕜 (A x) (A x) ≠ (0 : 𝕜) := fun h => hAx (inner_self_eq_zero.1 h)
  obtain ⟨c, hcinv, hcconj⟩ :
      ∃ c : 𝕜, c * inner 𝕜 (A x) (A x) = 1 ∧ starRingEnd 𝕜 c = c :=
    ⟨(inner 𝕜 (A x) (A x))⁻¹, inv_mul_cancel₀ hne, by rw [map_inv₀, inner_self_conj]⟩
  have hAxb : inner 𝕜 (A x) b = inner 𝕜 (A x) (A x) := by
    have hxm : x ∈ subspace A (b - A 0) m := by simpa using hx.mem
    have h0 : inner 𝕜 (A x) (b - A x) = (0 : 𝕜) :=
      (Submodule.mem_orthogonal _ _).1 hx.residual_mem_orthogonal (A x)
        (Submodule.mem_map_of_mem hxm)
    have hb : b = A x + (b - A x) := by abel
    rw [hb, inner_add_right, h0, add_zero]
  obtain ⟨X, hX⟩ : ∃ X : E →ₗ[𝕜] E, ∀ z, X z = (c * inner 𝕜 (A x) z) • x :=
    ⟨c • (LinearMap.toSpanSingleton 𝕜 E x ∘ₗ (innerSL 𝕜 (A x)).toLinearMap), fun z => by
      simp [LinearMap.toSpanSingleton_apply, smul_smul]⟩
  refine ⟨X, LinearMap.ext fun z => ?_, fun u v => ?_, ?_⟩
  · have hkey : c * ((c * inner 𝕜 (A x) z) * inner 𝕜 (A x) (A x))
        = c * inner 𝕜 (A x) z := by
      linear_combination (c * inner 𝕜 (A x) z) * hcinv
    simp only [LinearMap.comp_apply, hX, map_smul, inner_smul_right, hkey]
  · simp only [LinearMap.comp_apply, hX, map_smul, inner_smul_left, inner_smul_right, map_mul,
      hcconj, inner_conj_symm]
    ring
  · rw [hX, hAxb, hcinv, one_smul]

/-- Let $x_0 \in E$, let $r_0 = b - A x_0$ have a finite-dimensional full Krylov space, and let $m$
be less than the grade of $r_0$. If $x$ is a minimal-residual iterate at step $m$, then
$$\|b - Ax\| = \Bigl(\prod_{k=0}^{m-1} |s_k|\Bigr) \|r_0\|,$$
where $s_k$ are the Givens sines of the Arnoldi coefficients of $A$ at $r_0$. This is (2.21) of
[choi2006iterative].

The sines are `Krylov.givensS (Arnoldi.coeff A r₀) k`. For symmetric $A$ the Arnoldi
coefficients form the tridiagonal matrix $\bar T$ (`Lanczos.hessenberg_eq_map_tridiagExt`), so
the $s_k$ are the sines of the Lanczos rotations of [choi2006iterative]. The identity itself
needs no symmetry. -/
theorem norm_residual_eq_prod_givensS {x₀ : E} [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hm : m < grade A (b - A x₀)) (hx : IsMinResidualIterate A b x₀ m x) :
    ‖b - A x‖ =
      (∏ k ∈ Finset.range m, ‖givensS (Arnoldi.coeff A (b - A x₀)) k‖) * ‖b - A x₀‖ := by
  rw [hx.norm_residual_eq_norm_gamma hm, norm_gamma_eq_prod]
  simp

end IsMinResidualIterate

namespace IsMinNormMinResidualIterate

/-- Let $x$ be a minimal-residual iterate of least norm from $x_0 = 0$ at step $m$. Then
$\langle x, z \rangle = 0$ for every $z \in \mathcal{K}_m(A, b) \cap \ker A$.

The minimal-residual iterates differ from each other by exactly these vectors
(`Krylov.isMinResidualIterate_iff_sub_mem`). -/
theorem inner_eq_zero_of_mem (hx : IsMinNormMinResidualIterate A b 0 m x) {z : E}
    (hz : z ∈ subspace A b m ⊓ LinearMap.ker A) : inner 𝕜 x z = (0 : 𝕜) := by
  have hmin : ∀ w ∈ subspace A b m ⊓ LinearMap.ker A, ‖x - (0 : E)‖ ≤ ‖x - w‖ := by
    intro w hw
    rw [sub_zero]
    refine hx.norm_le _ ((isMinResidualIterate_zero_iff_sub_mem hx.isMinResidualIterate).2 ?_)
    rw [sub_sub_cancel_left]
    exact Submodule.neg_mem _ hw
  have h := Submodule.inner_eq_zero_of_forall_norm_sub_le
    (Submodule.zero_mem (subspace A b m ⊓ LinearMap.ker A)) hmin hz
  rwa [sub_zero] at h

/-- Let $A$ be symmetric, let $b$ have a finite-dimensional full Krylov space, and let $m$ be at
least the grade of $b$. If $x$ is a minimal-residual iterate of least norm from $x_0 = 0$ at
step $m$, then
$$x \in (\ker A)^\perp.$$

The Krylov space lies in $\mathbb{K} r + (\ker A)^\perp$, where $r = b - Ax$ is the residual. At
termination $r$ lies in $\ker A$
(`Krylov.IsMinResidualIterate.apply_residual_eq_zero_of_grade_le`) and in $\mathcal{K}_m$, and
the least-norm condition removes the component of $x$ along $r$. -/
theorem mem_orthogonal_ker_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A b)]
    (hA : A.IsSymmetric) (hm : grade A b ≤ m) (hx : IsMinNormMinResidualIterate A b 0 m x) :
    x ∈ (LinearMap.ker A)ᗮ := by
  have hx' := hx.isMinResidualIterate
  have hKg : subspace A b m = fullSubspace A b := by
    rw [subspace_eq_of_grade_le A b hm, subspace_grade_eq_fullSubspace]
  have hker : b - A x ∈ LinearMap.ker A :=
    LinearMap.mem_ker.2 (IsMinResidualIterate.apply_residual_eq_zero_of_grade_le hA hm hx')
  have hxm : x ∈ subspace A b m := by
    simpa using (isMinResidual_of_isMinResidualIterate_zero hx').mem
  have hinvt : ∀ z ∈ subspace A b m, A z ∈ subspace A b m := by
    rw [hKg]
    exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1
      (fullSubspace_mem_invtSubmodule A b)
  have hbm : b ∈ subspace A b m := by
    rw [hKg]
    exact Submodule.subset_span ⟨0, by simp⟩
  have hresm : b - A x ∈ subspace A b m := Submodule.sub_mem _ hbm (hinvt x hxm)
  have hxr : inner 𝕜 x (b - A x) = (0 : 𝕜) := inner_eq_zero_of_mem hx ⟨hresm, hker⟩
  -- the Krylov space is spanned by the residual together with `(ker A)ᗮ`
  have hle : subspace A b m ≤ (𝕜 ∙ (b - A x)) ⊔ (LinearMap.ker A)ᗮ := by
    rw [hKg]
    refine le_trans (fullSubspace_le_span_sup_range A b) (sup_le ?_ ?_)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.mem_sup.2 ⟨b - A x, Submodule.mem_span_singleton_self _, A x,
        range_le_orthogonal_ker hA ⟨x, rfl⟩, by abel⟩
    · exact le_trans (range_le_orthogonal_ker hA) le_sup_right
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (hle hxm)
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 hp
  have hnq : inner 𝕜 (b - A x) q = (0 : 𝕜) :=
    Submodule.inner_right_of_mem_orthogonal hker hq
  have hα : α * inner 𝕜 (b - A x) (b - A x) = 0 := by
    have h := congrArg (fun w => inner 𝕜 (b - A x) w) hpq
    simp only [inner_add_right, inner_smul_right, hnq, add_zero] at h
    rw [h, ← inner_conj_symm, hxr, map_zero]
  have hαzero : α • (b - A x) = 0 := by
    rcases eq_or_ne α 0 with rfl | hα0
    · rw [zero_smul]
    · rw [inner_self_eq_zero.1 ((mul_eq_zero.1 hα).resolve_left hα0), smul_zero]
  rw [← hpq, hαzero, zero_add]
  exact hq

/-- Let $A$ be symmetric, let $b$ have a finite-dimensional full Krylov space, and let $m$ be at
least the grade of $b$. If $x$ is a minimal-residual iterate of least norm from $x_0 = 0$ at
step $m$ (the specification of MINRES-QLP), then $\|x\|$ is the least norm of a least-squares
solution:
$$\|x\| = \min\{\|y\| : \|b - Ay\| \le \|b - Az\| \text{ for all } z \in E\}.$$
This is Theorem 3.1 of [choi2006iterative].

Since $x$ is itself a least-squares solution
(`Krylov.IsMinResidualIterate.norm_residual_le_of_grade_le`), $x$ is the minimum-norm
least-squares solution $A^+ b$. The system need not be compatible and $A$ need not be injective.
This is what the least-norm condition of `Krylov.IsMinNormMinResidualIterate` adds to
`Krylov.IsMinResidualIterate.isLeast_norm_of_grade_le`. The statement is `IsLeast` of the set of
norms of the least-squares solutions. -/
theorem isLeast_norm_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A b)] (hA : A.IsSymmetric)
    (hm : grade A b ≤ m) (hx : IsMinNormMinResidualIterate A b 0 m x) :
    IsLeast (norm '' {y : E | ∀ z : E, ‖b - A y‖ ≤ ‖b - A z‖}) ‖x‖ := by
  have hx' := hx.isMinResidualIterate
  have hlsq : ∀ z : E, ‖b - A x‖ ≤ ‖b - A z‖ :=
    IsMinResidualIterate.norm_residual_le_of_grade_le hA hm hx'
  refine ⟨⟨x, hlsq, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h0 : inner 𝕜 (b - A x) (A x - A y) = (0 : 𝕜) := by
    refine inner_eq_zero_symm.1 ?_
    exact (Submodule.mem_orthogonal _ _).1
      (IsMinResidualIterate.residual_mem_orthogonal_range_of_grade_le hA hm hx') _
      ⟨x - y, by rw [map_sub]⟩
  have hsplit : b - A y = (b - A x) + (A x - A y) := by abel
  have hsq : ‖b - A y‖ * ‖b - A y‖ = ‖b - A x‖ * ‖b - A x‖ + ‖A x - A y‖ * ‖A x - A y‖ := by
    rw [hsplit, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0]
  have hAeq : A y = A x := by
    have h1 : ‖b - A y‖ = ‖b - A x‖ := le_antisymm (hy x) (hlsq y)
    rw [h1] at hsq
    have hz2 : ‖A x - A y‖ * ‖A x - A y‖ = 0 := by linarith
    exact (sub_eq_zero.1 (norm_eq_zero.1 (mul_self_eq_zero.1 hz2))).symm
  have hyx : y - x ∈ LinearMap.ker A := by
    rw [LinearMap.mem_ker, map_sub, hAeq, sub_self]
  have hxk : inner 𝕜 x (y - x) = (0 : 𝕜) := by
    refine inner_eq_zero_symm.1 ?_
    exact (Submodule.mem_orthogonal _ _).1 (mem_orthogonal_ker_of_grade_le hA hm hx) _ hyx
  have hsq' : ‖y‖ * ‖y‖ = ‖x‖ * ‖x‖ + ‖y - x‖ * ‖y - x‖ := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x (y - x) hxk
    rwa [show x + (y - x) = y from by abel] at h
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (y - x)]

end IsMinNormMinResidualIterate

end Krylov

namespace Lanczos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### Termination and the number of distinct eigenvalues -/

section Eigenvalues

variable {A : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E]

private theorem le_iSup_eigenspace_of_forall (hA : A.IsSymmetric) {S : Finset 𝕜}
    (hS : ∀ μ : 𝕜, Module.End.eigenspace A μ ≠ ⊥ → μ ∈ S) :
    (⊤ : Submodule 𝕜 E) ≤ ⨆ μ ∈ S, Module.End.eigenspace A μ := by
  rw [← hA.iSup_eigenspace_eq_top]
  refine iSup_le fun μ => ?_
  rcases eq_or_ne (Module.End.eigenspace A μ) ⊥ with h0 | h0
  · rw [h0]
    exact bot_le
  · exact le_iSup₂ (f := fun μ (_ : μ ∈ S) => Module.End.eigenspace A μ) μ (hS μ h0)

/-- Let $A$ be symmetric on a finite-dimensional space, and let $S$ contain every nonzero eigenvalue
of $A$. Then $\operatorname{range} A$ lies in the sum of the eigenspaces of the elements of $S$. -/
private theorem range_le_iSup_eigenspace (hA : A.IsSymmetric) {S : Finset 𝕜}
    (hS : ∀ μ : 𝕜, μ ≠ 0 → Module.End.eigenspace A μ ≠ ⊥ → μ ∈ S) :
    LinearMap.range A ≤ ⨆ μ ∈ S, Module.End.eigenspace A μ := by
  rw [LinearMap.range_eq_map, ← hA.iSup_eigenspace_eq_top, Submodule.map_iSup]
  refine iSup_le fun μ => ?_
  rcases eq_or_ne μ 0 with rfl | hμ
  · rw [Module.End.eigenspace_zero]
    rintro _ ⟨z, hz, rfl⟩
    rw [LinearMap.mem_ker.1 hz]
    exact Submodule.zero_mem _
  · rcases eq_or_ne (Module.End.eigenspace A μ) ⊥ with h0 | h0
    · rw [h0, Submodule.map_bot]
      exact bot_le
    · refine le_trans ?_
        (le_iSup₂ (f := fun μ (_ : μ ∈ S) => Module.End.eigenspace A μ) μ (hS μ hμ h0))
      rintro _ ⟨z, hz, rfl⟩
      have hev : A z = μ • z := Module.End.mem_eigenspace_iff.1 hz
      rw [Module.End.mem_eigenspace_iff, hev, map_smul, hev]

/-- Let $E$ be finite-dimensional, let $A$ be symmetric, and let $S$ be a finite set of scalars that
contains every nonzero eigenvalue of $A$. If $b \in \operatorname{range} A$, then
$$\operatorname{grade}(A, b) \le |S|.$$
This is the compatible case of Theorem 2.4 of [choi2006iterative]: the Lanczos process on $b$
terminates within $|S|$ steps.

[choi2006iterative] counts only the eigenvalues along which $b$ has a nonzero component. That
sharper form is `Krylov.grade_le_card_of_mem_iSup_eigenspace` for the smaller set $S$. The
present result is the corollary that needs no knowledge of the components. -/
theorem grade_le_card_eigenvalues_of_mem_range (hA : A.IsSymmetric) {S : Finset 𝕜}
    (hS : ∀ μ : 𝕜, μ ≠ 0 → Module.End.HasEigenvalue A μ → μ ∈ S) {b : E}
    (hb : b ∈ LinearMap.range A) : grade A b ≤ S.card :=
  grade_le_card_of_mem_iSup_eigenspace (range_le_iSup_eigenspace hA hS hb)

/-- Let $E$ be finite-dimensional, let $A$ be symmetric, and let $S$ be a finite set of scalars that
contains every nonzero eigenvalue of $A$. Then for every $b \in E$,
$$\operatorname{grade}(A, b) \le |S| + 1.$$
This is Theorem 2.4 of [choi2006iterative]: the Lanczos process on any $b$ terminates within
$|S| + 1$ steps.

The bound is one more than that of `Lanczos.grade_le_card_eigenvalues_of_mem_range`, and the
extra step accounts for the component of $b$ in $\ker A$. The sharper count of
[choi2006iterative], over the eigenvalues along which $b$ has a component, is
`Krylov.grade_le_card_of_mem_iSup_eigenspace`. -/
theorem grade_le_card_eigenvalues (hA : A.IsSymmetric) {S : Finset 𝕜}
    (hS : ∀ μ : 𝕜, μ ≠ 0 → Module.End.HasEigenvalue A μ → μ ∈ S) (b : E) :
    grade A b ≤ S.card + 1 := by
  have hins : ∀ μ : 𝕜, Module.End.eigenspace A μ ≠ ⊥ → μ ∈ insert (0 : 𝕜) S := by
    intro μ hμ
    rcases eq_or_ne μ 0 with rfl | h0
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hS μ h0 hμ)
  exact le_trans
    (grade_le_card_of_mem_iSup_eigenspace
      (le_iSup_eigenspace_of_forall hA hins Submodule.mem_top))
    (Finset.card_insert_le _ _)

end Eigenvalues

/-! ### Bounds on the tridiagonal matrices -/

section Tridiag

variable {A : E →ₗ[𝕜] E} {b : E} [FiniteDimensional 𝕜 (fullSubspace A b)]

/-- Below the grade the Arnoldi vectors are orthonormal, so the norm of a combination
$\sum_i c_i v_i$ of the first $N$ Arnoldi vectors is the Euclidean norm of $c$. -/
private theorem norm_sum_smul_vec {N : ℕ} (hN : N ≤ grade A b) (c : Fin N → 𝕜) :
    ‖∑ i, c i • Arnoldi.vec A b (i : ℕ)‖ = ‖(WithLp.toLp 2 c : EuclideanSpace 𝕜 (Fin N))‖ :=
  Krylov.norm_sum_smul_vec_eq A b c fun i hi => absurd (lt_of_lt_of_le i.isLt hN) (not_lt.2 hi)

/-- Let $A$ be symmetric, let $b$ have a finite-dimensional full Krylov space, and let $m + 1$ be at
most the grade of $b$. If $\|Az\| \le C \|z\|$ for all $z \in E$, then the extended Lanczos
matrix $\bar T_m \in \mathbb{R}^{(m+1) \times m}$ satisfies
$$\|\bar T_m y\| \le C \|y\| \quad \text{for all } y \in \mathbb{K}^m.$$
This is the bound $\|\bar T_m\| \le \|A\|$ of Lemma 2.31 of [choi2006iterative], in a form that
needs no norm on the space of operators.

The reason is the relation $A V_m = V_{m+1} \bar T_m$, where $V_{m+1}$ is an isometry on
coordinates up to the grade. The matrix is `Lanczos.tridiagExt A b m`, mapped entrywise into
$\mathbb{K}$, and it acts on `EuclideanSpace 𝕜 (Fin m)` through `Matrix.toEuclideanLin`. -/
theorem norm_toEuclideanLin_tridiagExt_le (hA : A.IsSymmetric) {C : ℝ}
    (hC : ∀ z : E, ‖A z‖ ≤ C * ‖z‖) {m : ℕ} (hm : m + 1 ≤ grade A b)
    (y : EuclideanSpace 𝕜 (Fin m)) :
    ‖Matrix.toEuclideanLin ((tridiagExt A b m).map (algebraMap ℝ 𝕜)) y‖ ≤ C * ‖y‖ := by
  have hAsum : A (∑ j, (WithLp.ofLp y) j • Arnoldi.vec A b (j : ℕ)) =
      ∑ i : Fin (m + 1),
        ((tridiagExt A b m).map (algebraMap ℝ 𝕜)).mulVec (WithLp.ofLp y) i •
          Arnoldi.vec A b (i : ℕ) := by
    rw [Arnoldi.apply_sum A b m (WithLp.ofLp y), hessenberg_eq_map_tridiagExt b hA m]
  have hlhs : ‖Matrix.toEuclideanLin ((tridiagExt A b m).map (algebraMap ℝ 𝕜)) y‖
      = ‖A (∑ j, (WithLp.ofLp y) j • Arnoldi.vec A b (j : ℕ))‖ := by
    rw [hAsum, norm_sum_smul_vec hm, Matrix.toLpLin_apply]
  have hrhs : ‖∑ j, (WithLp.ofLp y) j • Arnoldi.vec A b (j : ℕ)‖ = ‖y‖ := by
    rw [norm_sum_smul_vec (by omega)]
  rw [hlhs, ← hrhs]
  exact hC _

/-- Let $A$ be symmetric, let $b$ have a finite-dimensional full Krylov space, and let $m + 1$ be at
most the grade of $b$. If $\|Az\| \le C \|z\|$ for all $z \in E$, then the Lanczos matrix
$T_m \in \mathbb{R}^{m \times m}$ satisfies
$$\|T_m y\| \le C \|y\| \quad \text{for all } y \in \mathbb{K}^m.$$
This is the bound $\|T_m\| \le \|\bar T_m\| \le \|A\|$ of Lemma 2.31 of [choi2006iterative].

The matrix $T_m$ is the leading $m \times m$ block of $\bar T_m$, so it satisfies every bound
that `Lanczos.norm_toEuclideanLin_tridiagExt_le` gives. The matrix is `Lanczos.tridiag A b m`,
mapped entrywise into $\mathbb{K}$. -/
theorem norm_toEuclideanLin_tridiag_le (hA : A.IsSymmetric) {C : ℝ}
    (hC : ∀ z : E, ‖A z‖ ≤ C * ‖z‖) {m : ℕ} (hm : m + 1 ≤ grade A b)
    (y : EuclideanSpace 𝕜 (Fin m)) :
    ‖Matrix.toEuclideanLin ((tridiag A b m).map (algebraMap ℝ 𝕜)) y‖ ≤ C * ‖y‖ := by
  have hcast : ∀ i : Fin m,
      ((tridiag A b m).map (algebraMap ℝ 𝕜)).mulVec (WithLp.ofLp y) i =
        ((tridiagExt A b m).map (algebraMap ℝ 𝕜)).mulVec (WithLp.ofLp y) i.castSucc := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, tridiagExt, tridiag, Matrix.of_apply,
      Fin.val_castSucc]
  have hsq : ‖Matrix.toEuclideanLin ((tridiag A b m).map (algebraMap ℝ 𝕜)) y‖ ^ 2 ≤
      ‖Matrix.toEuclideanLin ((tridiagExt A b m).map (algebraMap ℝ 𝕜)) y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
    have hterm : ∀ i : Fin m,
        ‖(Matrix.toEuclideanLin ((tridiag A b m).map (algebraMap ℝ 𝕜)) y) i‖ ^ 2 =
          ‖(Matrix.toEuclideanLin ((tridiagExt A b m).map (algebraMap ℝ 𝕜)) y) i.castSucc‖ ^ 2 := by
      intro i
      have h : (Matrix.toEuclideanLin ((tridiag A b m).map (algebraMap ℝ 𝕜)) y) i =
          (Matrix.toEuclideanLin ((tridiagExt A b m).map (algebraMap ℝ 𝕜)) y) i.castSucc := hcast i
      rw [h]
    have hsum : ∑ i : Fin m,
          ‖(Matrix.toEuclideanLin ((tridiag A b m).map (algebraMap ℝ 𝕜)) y) i‖ ^ 2 =
        ∑ i : Fin m,
          ‖(Matrix.toEuclideanLin ((tridiagExt A b m).map (algebraMap ℝ 𝕜)) y) i.castSucc‖ ^ 2 :=
      Finset.sum_congr rfl fun i _ => hterm i
    rw [hsum]
    exact le_add_of_nonneg_right (by positivity)
  have hle : ‖Matrix.toEuclideanLin ((tridiag A b m).map (algebraMap ℝ 𝕜)) y‖ ≤
      ‖Matrix.toEuclideanLin ((tridiagExt A b m).map (algebraMap ℝ 𝕜)) y‖ := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  exact hle.trans (norm_toEuclideanLin_tridiagExt_le hA hC hm y)

end Tridiag

/-! ### The residual recurrence of MINRES -/

section Residual

variable {A : E →ₗ[𝕜] E} {b x₀ : E} [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]

/-- Let $x_0 \in E$, let $r_0 = b - A x_0$ have a finite-dimensional full Krylov space, and let
$m + 1$ be at most the grade of $r_0$. Let $h$ be the Arnoldi coefficients of $A$ at $r_0$, with
Givens quantities $\rho_k$, $c_k$, $s_k$ and $\gamma_k$ (with $\gamma_0 = \|r_0\|$), and assume
$\rho_k \neq 0$ for $k \le m$. If $x$ and $x'$ are minimal-residual iterates at steps $m$ and
$m + 1$, then
$$b - Ax' = |s_m|^2 (b - Ax) - s_m g_m\, v_{m+1},$$
where $g_m = \bar c_m \gamma_m$ is the $m$-th entry of the rotated right-hand side and $v_{m+1}$
is an Arnoldi vector. This is Lemma 2.18 of [choi2006iterative], and (6.55) of
[saad2003iterative] for DQGMRES.

The real form $r_k = s_k^2 r_{k-1} - \phi_k c_k v_{k+1}$ of [choi2006iterative] is this identity
with $\gamma_m = \pm \phi_m$. Both residuals are read off the last row of the accumulated
rotation (`Krylov.IsMinResidualIterate.residual_eq_gamma_smul_sum`), and one step of that row is
`Krylov.givensQ_last_row_castSucc` and `Krylov.givensQ_last_row_last`. The factor $|s_m|^2$ is
$s_m$ from $\gamma_{m+1} = -s_m \gamma_m$ times $\bar s_m$ from the row. Nothing here needs
symmetry, and the same identity holds for GMRES, but [choi2006iterative] uses it for MINRES. The
quantities are `Krylov.givensS`, `Krylov.gvec` and `Krylov.givensRho` of `Arnoldi.coeff A r₀`,
and $v_{m+1}$ is `Arnoldi.vec A r₀ (m + 1)`. -/
theorem residual_minRes_succ_eq {m : ℕ} (hm : m + 1 ≤ grade A (b - A x₀))
    (hρ : ∀ k < m + 1, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0) {x x' : E}
    (hx : IsMinResidualIterate A b x₀ m x) (hx' : IsMinResidualIterate A b x₀ (m + 1) x') :
    b - A x' =
      ((‖givensS (Arnoldi.coeff A (b - A x₀)) m‖ ^ 2 : ℝ) : 𝕜) • (b - A x) -
        (givensS (Arnoldi.coeff A (b - A x₀)) m *
            gvec (Arnoldi.coeff A (b - A x₀)) ((‖b - A x₀‖ : ℝ) : 𝕜) m) •
          Arnoldi.vec A (b - A x₀) (m + 1) := by
  have hr := hx.residual_eq_gamma_smul_sum (by omega) fun k hk => hρ k (by omega)
  have hr' := hx'.residual_eq_gamma_smul_sum hm hρ
  have h1 : ∀ j : Fin (m + 1),
      (gamma (Arnoldi.coeff A (b - A x₀)) ((‖b - A x₀‖ : ℝ) : 𝕜) (m + 1) *
          (starRingEnd 𝕜) (givensQ (Arnoldi.coeff A (b - A x₀)) (m + 1)
            (Fin.last (m + 1)) j.castSucc)) •
          Arnoldi.vec A (b - A x₀) ((j.castSucc : Fin (m + 2)) : ℕ)
        = ((‖givensS (Arnoldi.coeff A (b - A x₀)) m‖ ^ 2 : ℝ) : 𝕜) •
          ((gamma (Arnoldi.coeff A (b - A x₀)) ((‖b - A x₀‖ : ℝ) : 𝕜) m *
              (starRingEnd 𝕜) (givensQ (Arnoldi.coeff A (b - A x₀)) m (Fin.last m) j)) •
            Arnoldi.vec A (b - A x₀) (j : ℕ)) := by
    intro j
    have hval : ((j.castSucc : Fin (m + 2)) : ℕ) = (j : ℕ) := rfl
    rw [hval, givensQ_last_row_castSucc, gamma_succ, map_mul, map_neg, smul_smul]
    congr 1
    have hc : givensS (Arnoldi.coeff A (b - A x₀)) m *
        (starRingEnd 𝕜) (givensS (Arnoldi.coeff A (b - A x₀)) m)
        = ((‖givensS (Arnoldi.coeff A (b - A x₀)) m‖ ^ 2 : ℝ) : 𝕜) := by
      rw [RCLike.mul_conj]
      push_cast
      ring
    linear_combination (gamma (Arnoldi.coeff A (b - A x₀)) ((‖b - A x₀‖ : ℝ) : 𝕜) m *
      (starRingEnd 𝕜) (givensQ (Arnoldi.coeff A (b - A x₀)) m (Fin.last m) j)) * hc
  have h2 : (gamma (Arnoldi.coeff A (b - A x₀)) ((‖b - A x₀‖ : ℝ) : 𝕜) (m + 1) *
        (starRingEnd 𝕜) (givensQ (Arnoldi.coeff A (b - A x₀)) (m + 1)
          (Fin.last (m + 1)) (Fin.last (m + 1)))) •
        Arnoldi.vec A (b - A x₀) ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)
      = -((givensS (Arnoldi.coeff A (b - A x₀)) m *
          gvec (Arnoldi.coeff A (b - A x₀)) ((‖b - A x₀‖ : ℝ) : 𝕜) m) •
        Arnoldi.vec A (b - A x₀) (m + 1)) := by
    have hval : ((Fin.last (m + 1) : Fin (m + 2)) : ℕ) = m + 1 := rfl
    rw [hval, givensQ_last_row_last, gamma_succ, gvec, ← neg_smul]
    congr 1
    ring
  rw [hr', Fin.sum_univ_castSucc, Finset.sum_congr rfl fun j _ => h1 j, ← Finset.smul_sum, ← hr,
    h2, ← sub_eq_add_neg]

/-- Let $A$ be symmetric, let $x_0 \in E$, let $r_0 = b - A x_0$ have a finite-dimensional full
Krylov space, and let $m$ be at most the grade of $r_0$. Let $h$ be the Arnoldi coefficients of
$A$ at $r_0$, let $R^{(m)}$ be the coefficient array after the first $m$ Givens rotations, and
assume $\rho_k \neq 0$ for $k < m$. If $x$ is a minimal-residual iterate at step $m$, then
$A r_m$, with $r_m = b - Ax$, has only two components in the Lanczos basis:
$$A r_m = \gamma_m \bigl(\overline{R^{(m)}_{m,m}}\, v_m + \overline{R^{(m)}_{m,m+1}}\,
  v_{m+1}\bigr),$$
where $\gamma_m$ is the last entry of the rotated right-hand side with $\gamma_0 = \|r_0\|$.
This is Lemma 2.19 of [choi2006iterative].

[choi2006iterative] writes the two entries as $\gamma^{(1)}_{k+1}$ and $\delta^{(1)}_{k+2}$ and
the factor as $\|r_k\|$, with $|\gamma_m| = \|r_m\|$. The index shift comes from the fact that
the rotation $Q_{k,k+1}$ of [choi2006iterative] is rotation $k - 1$ here. Through the Arnoldi
relation, the coefficient of $v_l$ in $A r_m$ is $\gamma_m \sum_i \overline{(Q_m)_{m,i}}\,
h_{l,i}$. By the Hermitian symmetry of the Lanczos coefficients, this is
$\gamma_m \overline{(Q_m \bar H)_{m,l}}$. It vanishes for $l < m$ because the rotated array is
upper triangular, which is the orthogonality $A r_m \perp \mathcal{K}_m$, and
`Krylov.rotated_row_eq_sum_givensQ` gives it at $l = m$ and $l = m + 1$. With
`h = Arnoldi.coeff A r₀`, the two entries are `Krylov.rotated h m m m` and
`Krylov.rotated h m m (m + 1)`, and the scalar `Krylov.gamma` gives the last entry of the
rotated right-hand side. -/
theorem apply_residual_minRes_eq (hA : A.IsSymmetric) {m : ℕ} (hm : m ≤ grade A (b - A x₀))
    (hρ : ∀ k < m, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0) {x : E}
    (hx : IsMinResidualIterate A b x₀ m x) :
    A (b - A x) =
      (gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m *
          (starRingEnd 𝕜) (rotated (Arnoldi.coeff A (b - A x₀)) m m m)) •
          Arnoldi.vec A (b - A x₀) m +
        (gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m *
            (starRingEnd 𝕜) (rotated (Arnoldi.coeff A (b - A x₀)) m m (m + 1))) •
          Arnoldi.vec A (b - A x₀) (m + 1) := by
  have hr := hx.residual_eq_gamma_smul_sum hm hρ
  have step1 : ∀ i : Fin (m + 1),
      A ((gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m *
            (starRingEnd 𝕜) (givensQ (Arnoldi.coeff A (b - A x₀)) m (Fin.last m) i)) •
          Arnoldi.vec A (b - A x₀) (i : ℕ))
        = ∑ l ∈ Finset.range (m + 2),
            ((gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m *
                (starRingEnd 𝕜) (givensQ (Arnoldi.coeff A (b - A x₀)) m (Fin.last m) i)) *
              Arnoldi.coeff A (b - A x₀) l (i : ℕ)) • Arnoldi.vec A (b - A x₀) l := by
    intro i
    rw [map_smul, Arnoldi.apply_vec_of_le A (b - A x₀) (show (i : ℕ) + 2 ≤ m + 2 by
      have := i.isLt; omega), Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => (smul_smul _ _ _)
  have step2 : ∀ l ∈ Finset.range (m + 2),
      (∑ i : Fin (m + 1),
          ((gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m *
              (starRingEnd 𝕜) (givensQ (Arnoldi.coeff A (b - A x₀)) m (Fin.last m) i)) *
            Arnoldi.coeff A (b - A x₀) l (i : ℕ)) • Arnoldi.vec A (b - A x₀) l)
        = (gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m *
            (starRingEnd 𝕜) (rotated (Arnoldi.coeff A (b - A x₀)) m m l)) •
          Arnoldi.vec A (b - A x₀) l := by
    intro l hl
    rw [Finset.mem_range] at hl
    rw [← Finset.sum_smul]
    congr 1
    rw [rotated_row_eq_sum_givensQ (Arnoldi.coeff A (b - A x₀)) m l (by omega), map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Arnoldi.coeff_conj_of_isSymmetric hA (b - A x₀) l (i : ℕ)]
    ring
  have step3 : ∀ l ∈ Finset.range m,
      (gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m *
          (starRingEnd 𝕜) (rotated (Arnoldi.coeff A (b - A x₀)) m m l)) •
        Arnoldi.vec A (b - A x₀) l = 0 := by
    intro l hl
    rw [Finset.mem_range] at hl
    rw [rotated_eq_zero_of_lt (Arnoldi.coeff A (b - A x₀))
      (Arnoldi.isUpperHessenberg_coeff A (b - A x₀)) m m l hl hl,
      map_zero, mul_zero, zero_smul]
  rw [hr, map_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => step1 i, Finset.sum_comm,
    Finset.sum_congr rfl step2, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero step3, zero_add]

/-- Let $A$ be symmetric, let $x_0 \in E$, let $r_0 = b - A x_0$ have a finite-dimensional full
Krylov space, and let $m + 1$ be less than the grade of $r_0$. Assume $\rho_k \neq 0$ for
$k < m$. If $x$ is a minimal-residual iterate at step $m$ with residual $r_m = b - Ax$, then
$$\|A r_m\| = \|r_m\| \sqrt{|R^{(m)}_{m,m}|^2 + |R^{(m)}_{m,m+1}|^2},$$
with $R^{(m)}$ as in `Lanczos.apply_residual_minRes_eq`. This is the norm form of Lemma 2.19 of
[choi2006iterative].

The two Lanczos vectors that carry $A r_m$ are orthonormal, and $|\gamma_m| = \|r_m\|$. -/
theorem norm_apply_residual_minRes_eq (hA : A.IsSymmetric) {m : ℕ}
    (hm : m + 1 < grade A (b - A x₀))
    (hρ : ∀ k < m, givensRho (Arnoldi.coeff A (b - A x₀)) k ≠ 0) {x : E}
    (hx : IsMinResidualIterate A b x₀ m x) :
    ‖A (b - A x)‖ = ‖b - A x‖ *
      Real.sqrt (‖rotated (Arnoldi.coeff A (b - A x₀)) m m m‖ ^ 2 +
        ‖rotated (Arnoldi.coeff A (b - A x₀)) m m (m + 1)‖ ^ 2) := by
  have hv1 : ‖Arnoldi.vec A (b - A x₀) m‖ = 1 :=
    Arnoldi.norm_vec_eq_one_of_lt_grade A (b - A x₀) (by omega)
  have hv2 : ‖Arnoldi.vec A (b - A x₀) (m + 1)‖ = 1 :=
    Arnoldi.norm_vec_eq_one_of_lt_grade A (b - A x₀) hm
  have hperp : ∀ a c : 𝕜, (inner 𝕜 (a • Arnoldi.vec A (b - A x₀) m)
      (c • Arnoldi.vec A (b - A x₀) (m + 1)) : 𝕜) = 0 := by
    intro a c
    rw [inner_smul_left, inner_smul_right,
      Arnoldi.inner_vec_eq_zero A (b - A x₀) (by omega : m ≠ m + 1), mul_zero, mul_zero]
  have hgamma : ‖gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m‖ = ‖b - A x‖ :=
    (hx.norm_residual_eq_norm_gamma (by omega)).symm
  have hsq : ‖A (b - A x)‖ ^ 2 = ‖b - A x‖ ^ 2 *
      (‖rotated (Arnoldi.coeff A (b - A x₀)) m m m‖ ^ 2 +
        ‖rotated (Arnoldi.coeff A (b - A x₀)) m m (m + 1)‖ ^ 2) := by
    rw [apply_residual_minRes_eq hA (by omega) hρ hx, pow_two,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (hperp _ _), ← pow_two, ← pow_two,
      norm_smul, norm_smul, hv1, hv2, mul_one, mul_one, norm_mul, norm_mul, RCLike.norm_conj,
      RCLike.norm_conj, hgamma]
    ring
  rw [← Real.sqrt_sq (norm_nonneg (A (b - A x))), hsq, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

end Residual

end Lanczos
