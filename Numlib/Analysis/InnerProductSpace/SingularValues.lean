/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.SingularValues`, beside Mathlib's
`LinearMap.singularValues`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Numlib.Analysis.InnerProductSpace.Spectrum
import Numlib.Analysis.Normed.Lp.ProdLp
import Numlib.Eigen.MinMax

/-!
# Singular values of a linear map

Let $E$ and $F$ be finite-dimensional inner product spaces over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, with $n = \dim E$, and let $T : E \to F$ be linear. Mathlib defines the singular
values $\sigma_0(T) \ge \sigma_1(T) \ge \dots$ of $T$ as `LinearMap.singularValues`: the square
roots of the eigenvalues of $T^* T$ in decreasing order, indexed by $\mathbb{N}$ from $0$, and
$\sigma_k(T) = 0$ for $k \ge n$. This file proves the main facts about them without coordinates,
following [golub2013matrix], §2.4 and §8.6.1–8.6.2. These are the max–min and min–max
characterizations (the Courant–Fischer theorem for $T^* T$), for example
$$\sigma_k(T) = \max_{\dim S = k + 1} \ \min_{x \in S,\, x \neq 0} \frac{\|Tx\|}{\|x\|} \qquad (k <
  n),$$
Weyl's inequality $\sigma_{i+j}(S + T) \le \sigma_i(S) + \sigma_j(T)$, the interlacing of the
singular values under restriction of the domain, the invariance under isometries and adjoints, and
the singular value decomposition of a map as a pair of orthonormal families.

The file also defines the Hermitian dilation $(x, y) \mapsto (A^* y, Ax)$ of a linear map
$A : E \to F$, a symmetric operator on $E \times F$, and shows that its eigenvalues in decreasing
order are $\sigma_0, \dots, \sigma_{p-1}, 0, \dots, 0, -\sigma_{p-1}, \dots, -\sigma_0$ with
$p = \min(\dim E, \dim F)$. Finally it proves the stacked-isometry identity
$\|Q_2\|^2 = 1 - \sigma_{n-1}(Q_1)^2$ when $\|Q_1 x\|^2 + \|Q_2 x\|^2 = \|x\|^2$ for all $x$.

## Main definitions

* `LinearMap.hermitianDilation`: the Hermitian dilation (Jordan–Wielandt operator)
  $(x, y) \mapsto (A^* y, Ax)$ on $E \times F$ with the Euclidean norm, for a given adjoint $A^*$ of
  $A$.

## Main results

* `LinearMap.isGreatest_singularValues` and `LinearMap.isLeast_singularValues`: the max–min and
  min–max characterizations of $\sigma_k(T)$ by the stretch $\|Tx\| / \|x\|$ on subspaces.
* `LinearMap.isLeast_singularValues_bilinear`: the min–max characterization by the bilinear form
  $\operatorname{Re} \langle y, Tx \rangle / (\|x\| \|y\|)$ of [golub2013matrix], Theorem 8.6.1.
* `LinearMap.le_singularValues_of_mul_norm_le` and `LinearMap.singularValues_le_of_norm_le_mul`:
  one-sided bounds on $\sigma_k(T)$ from a subspace of at least the right dimension on which $T$
  stretches by at least, or at most, $c$.
* `LinearMap.singularValues_add_le`: **Weyl's inequality** $\sigma_{i+j}(S + T) \le \sigma_i(S) +
  \sigma_j(T)$.
* `LinearMap.abs_singularValues_sub_le`: if $\|(T - S)x\| \le C \|x\|$ for all $x$, then
  $|\sigma_k(T) - \sigma_k(S)| \le C$.
* `LinearMap.singularValues_domRestrict_interlace`: if $K \le E$ has codimension $r$, then
  $\sigma_{k+r}(T) \le \sigma_k(T|_K) \le \sigma_k(T)$.
* `LinearMap.singularValues_eq_of_forall_norm_eq`,
  `LinearMap.singularValues_comp_linearIsometryEquiv` and `LinearMap.singularValues_adjoint`: two
  maps with the same stretch at every vector have the same singular values, the singular values are
  invariant under isometries, and $T^*$ has the same singular values as $T$.
* `LinearMap.singularValues_comp_linearIsometry_eq_succ`: deflation of a top singular pair.
* `LinearMap.exists_orthonormal_singularVectors`: if $\dim E \le \dim F$, there are an orthonormal
  basis $(v_i)$ of $E$ and an orthonormal family $(u_i)$ in $F$ with $T v_i = \sigma_i u_i$.
* `LinearMap.norm_toContinuousLinearMap_sq_eq_one_sub_sq_singularValues`: the **stacked-isometry
  identity**.
* `LinearMap.eigenvalues_hermitianDilation`: the $i$-th eigenvalue of the Hermitian dilation of $A$
  is $\sigma_i(A) - \sigma_{N-1-i}(A)$, where $N = \dim E + \dim F$.

## Proof outline

Every inequality follows from the two one-sided max–min bounds. A subspace of dimension at least
$k + 1$ on which $T$ stretches by at least $c$ gives $c \le \sigma_k(T)$, and a subspace of
dimension at least $n - k$ on which $T$ stretches by at most $c$ gives $\sigma_k(T) \le c$. The
spectrum of the dilation is also found in this way, not by the computation of an eigenbasis: the
graph $\{(\sigma x, Ax)\}$ of $A$ over a max–min subspace bounds the eigenvalues from below, and the
product of a min–max subspace with all of $F$ bounds them from above.

## Implementation notes

* The singular values are indexed from $0$, so $\sigma_0(T)$ is the largest one. This differs from
  the indexing from $1$ of [golub2013matrix].
* The module does not use matrices. It uses the Courant–Fischer theorem of `Numlib.Eigen.MinMax`.
  The matrix singular value decomposition in `Numlib.LinearAlgebra.Matrix.SVD` and the matrix
  results in `Numlib.Analysis.Matrix.SingularValues` build on it.
* `LinearMap.hermitianDilation` takes the adjoint as a second argument `Astar`, with the hypothesis
  `LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A Astar`, which says $\langle A^* u, x
  \rangle = \langle u, Ax \rangle$ for all $u$ and $x$ (`LinearMap.isAdjointPair_inner_iff`). This
  is the convention of `Numlib.Krylov.NormalEquations`. So the dilation needs neither completeness
  nor finite dimension. The space $E \times F$ with the Euclidean norm is `WithLp 2 (E × F)`, with
  the factor $E$ first, as in the matrix `Matrix.hermitianDilation A`, which is
  `fromBlocks 0 Aᴴ A 0`.
-/

open Module

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The Hermitian dilation -/

section Dilation

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The **Hermitian dilation** (Jordan–Wielandt operator) of a linear map $A : E \to F$ with a given
map $A^* : F \to E$: the operator
$$H(x, y) = (A^* y, Ax)$$
on $E \times F$ with the Euclidean norm $\|(x, y)\|^2 = \|x\|^2 + \|y\|^2$.

The space is `WithLp 2 (E × F)`, with the factor $E$ first. The matrix of $H$ is
`Matrix.hermitianDilation A`, which is `fromBlocks 0 Aᴴ A 0`. This is the Jordan–Wielandt matrix
$S_3 = \begin{bmatrix} 0 & A^T \\ A & 0 \end{bmatrix}$ of [golub2013matrix], §8.6.1, and the
matrix $\tilde{A}$ of (8.6.4); (10.4.16) of [golub2013matrix] writes it with the two factors
exchanged. When $A^*$ is the adjoint of $A$, the operator $H$ is symmetric
(`LinearMap.isSymmetric_hermitianDilation_adjoint`), and its eigenvalues are $\pm$ the singular
values of $A$, completed by zeros (`LinearMap.eigenvalues_hermitianDilation`). -/
noncomputable def hermitianDilation (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) :
    WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
    (Astar ∘ₗ WithLp.sndₗ 2 𝕜 E F).prod (A ∘ₗ WithLp.fstₗ 2 𝕜 E F)

/-- The Hermitian dilation maps $(x, y)$ to $(A^* y, Ax)$. -/
@[simp]
theorem hermitianDilation_apply (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) (z : WithLp 2 (E × F)) :
    hermitianDilation A Astar z = WithLp.toLp 2 (Astar z.snd, A z.fst) :=
  rfl

/-- The dilation of $-A$ with the map $-A^*$ is minus the dilation of $A$ with $A^*$. -/
theorem hermitianDilation_neg (A : E →ₗ[𝕜] F) (Astar : F →ₗ[𝕜] E) :
    hermitianDilation (-A) (-Astar) = -hermitianDilation A Astar :=
  LinearMap.ext fun z => by
    simp only [hermitianDilation_apply, neg_apply, ← WithLp.toLp_neg, Prod.neg_mk]

variable {A : E →ₗ[𝕜] F} {Astar : F →ₗ[𝕜] E}

/-- Let $A : E \to F$ and $A^* : F \to E$ be linear with $\langle A^* u, x \rangle = \langle u, Ax
\rangle$ for all $x \in E$ and $u \in F$. Then the Hermitian dilation
$(x, y) \mapsto (A^* y, Ax)$ is a symmetric operator on $E \times F$.

The hypothesis is `LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A Astar`; see
`LinearMap.isAdjointPair_inner_iff`. -/
theorem isSymmetric_hermitianDilation
    (hadj : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A Astar) :
    (hermitianDilation A Astar).IsSymmetric := by
  intro z w
  have h : inner 𝕜 (A z.fst) w.snd = inner 𝕜 z.fst (Astar w.snd) := by
    rw [← inner_conj_symm, ← hadj.inner_apply_eq, inner_conj_symm]
  simp only [hermitianDilation_apply, WithLp.prod_inner_apply, WithLp.ofLp_fst,
    WithLp.ofLp_snd, hadj.inner_apply_eq, h]
  ring

/-- Let $A^*$ be an adjoint of $A$, that is, $\langle A^* u, x \rangle = \langle u, Ax \rangle$ for
all $x$ and $u$. Then the quadratic form of the Hermitian dilation $H$ is
$$\operatorname{Re} \langle H(x, y), (x, y) \rangle = 2 \operatorname{Re} \langle Ax, y
  \rangle.$$
-/
theorem re_inner_hermitianDilation_apply_self
    (hadj : LinearMap.IsAdjointPair (innerₛₗ 𝕜).flip (innerₛₗ 𝕜).flip A Astar)
    (z : WithLp 2 (E × F)) :
    RCLike.re (inner 𝕜 (hermitianDilation A Astar z) z) =
      2 * RCLike.re (inner 𝕜 (A z.fst) z.snd) := by
  simp only [hermitianDilation_apply, WithLp.prod_inner_apply, WithLp.ofLp_fst,
    WithLp.ofLp_snd, hadj.inner_apply_eq, map_add]
  rw [inner_re_symm z.snd]
  ring

end Dilation

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

/-- Let $T : E \to F$ be linear, let $n = \dim E$, and let $v_0, \dots, v_{n-1}$ be the orthonormal
eigenbasis of $T^* T$ sorted by decreasing eigenvalue. Then the images $T v_i$ are pairwise
orthogonal, with $\|T v_j\|^2 = \sigma_j(T)^2$:
$$\langle T v_i, T v_j \rangle = \begin{cases} \sigma_j(T)^2 & \text{if } i = j, \\ 0 &
  \text{otherwise.} \end{cases}$$

The eigenbasis is `LinearMap.IsSymmetric.eigenvectorBasis` of $T^* T$. -/
theorem inner_apply_eigenvectorBasis_adjoint_comp_self {n : ℕ} (hn : finrank 𝕜 E = n)
    (i j : Fin n) :
    inner 𝕜 (T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn i))
        (T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn j))
      = if i = j then ((T.singularValues j ^ 2 : ℝ) : 𝕜) else 0 := by
  rw [← adjoint_inner_right, ← comp_apply, T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis,
    inner_smul_right,
    orthonormal_iff_ite.1 (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn).orthonormal i j,
    ← T.sq_singularValues_fin hn j]
  split_ifs <;> simp

/-- Let $T : E \to F$ be linear, let $n = \dim E$, and let $v_0, \dots, v_{n-1}$ be the orthonormal
eigenbasis of $T^* T$ sorted by decreasing eigenvalue. Then $\|T v_j\| = \sigma_j(T)$ for every
$j < n$.

The eigenbasis is `LinearMap.IsSymmetric.eigenvectorBasis` of $T^* T$. -/
theorem norm_apply_eigenvectorBasis_adjoint_comp_self {n : ℕ} (hn : finrank 𝕜 E = n) (j : Fin n) :
    ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn j)‖ = T.singularValues j := by
  have h := T.inner_apply_eigenvectorBasis_adjoint_comp_self hn j j
  rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn j)‖ ^ 2
      = T.singularValues j ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (T.singularValues_nonneg j) two_ne_zero).1 h2

/-- Let $T : E \to F$ be linear. Then $\sigma_i(T) = 0$ for every $i \ge \dim F$.

Mathlib's `LinearMap.singularValues_of_finrank_le` gives the same for $i \ge \dim E$. So at most
$\min(\dim E, \dim F)$ singular values are nonzero. -/
theorem singularValues_of_finrank_codomain_le {i : ℕ} (hi : finrank 𝕜 F ≤ i) :
    T.singularValues i = 0 :=
  T.singularValues_eq_zero_iff_le_finrank_range.2 ((Submodule.finrank_le _).trans hi)

/-- If $\sigma_k(T) > 0$, then $k < \dim E$. -/
theorem lt_finrank_of_singularValues_pos {k : ℕ} (hk : 0 < T.singularValues k) :
    k < finrank 𝕜 E := by
  by_contra h
  rw [T.singularValues_of_finrank_le (not_lt.1 h)] at hk
  exact lt_irrefl _ hk

/-! ### The max–min characterizations -/

/-- The Rayleigh quotient of $T^* T$ at $x \in E$ is
$$\frac{\langle T^* T x, x \rangle}{\|x\|^2} = \frac{\|Tx\|^2}{\|x\|^2}.$$

Both sides are $0$ at $x = 0$. -/
theorem rayleighQuotient_adjoint_comp_self (x : E) :
    (adjoint T ∘ₗ T).rayleighQuotient x = ‖T x‖ ^ 2 / ‖x‖ ^ 2 := by
  rw [rayleighQuotient, comp_apply, adjoint_inner_left, inner_self_eq_norm_sq]

/-- Let $c \ge 0$ and $x \neq 0$. Then $c^2$ is at most the Rayleigh quotient of $T^* T$ at $x$ if
and only if $c \|x\| \le \|Tx\|$. -/
theorem sq_le_rayleighQuotient_adjoint_comp_self_iff {c : ℝ} (hc : 0 ≤ c) {x : E} (hx : x ≠ 0) :
    c ^ 2 ≤ (adjoint T ∘ₗ T).rayleighQuotient x ↔ c * ‖x‖ ≤ ‖T x‖ := by
  rw [rayleighQuotient_adjoint_comp_self, le_div_iff₀ (pow_pos (norm_pos_iff.2 hx) 2), ← mul_pow]
  exact pow_le_pow_iff_left₀ (mul_nonneg hc (norm_nonneg x)) (norm_nonneg _) two_ne_zero

/-- Let $c \ge 0$ and $x \neq 0$. Then the Rayleigh quotient of $T^* T$ at $x$ is at most $c^2$ if
and only if $\|Tx\| \le c \|x\|$. -/
theorem rayleighQuotient_adjoint_comp_self_le_sq_iff {c : ℝ} (hc : 0 ≤ c) {x : E} (hx : x ≠ 0) :
    (adjoint T ∘ₗ T).rayleighQuotient x ≤ c ^ 2 ↔ ‖T x‖ ≤ c * ‖x‖ := by
  rw [rayleighQuotient_adjoint_comp_self, div_le_iff₀ (pow_pos (norm_pos_iff.2 hx) 2), ← mul_pow]
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg x)) two_ne_zero

/-- **Max–min bound, the easy direction.** Let $T : E \to F$ be linear, let $k \in \mathbb{N}$ and
$c \in \mathbb{R}$, and let $S$ be a subspace of $E$ with $\dim S \ge k + 1$. If
$c \|x\| \le \|Tx\|$ for all $x \in S$, then
$$c \le \sigma_k(T).$$
-/
theorem le_singularValues_of_mul_norm_le {k : ℕ} {c : ℝ} {S : Submodule 𝕜 E}
    (hS : k + 1 ≤ finrank 𝕜 S) (h : ∀ x ∈ S, c * ‖x‖ ≤ ‖T x‖) : c ≤ T.singularValues k := by
  rcases le_or_gt c 0 with hc | hc
  · exact hc.trans (T.singularValues_nonneg k)
  have hk : k < finrank 𝕜 E := by have := Submodule.finrank_le S; omega
  obtain ⟨x, hxS, hx0, hle⟩ :=
    T.isSymmetric_adjoint_comp_self.exists_mem_ne_zero_rayleighQuotient_le rfl ⟨k, hk⟩ hS
  rw [← T.sq_singularValues_of_lt rfl hk,
    T.rayleighQuotient_adjoint_comp_self_le_sq_iff (T.singularValues_nonneg k) hx0] at hle
  exact le_of_mul_le_mul_right ((h x hxS).trans hle) (norm_pos_iff.2 hx0)

/-- **Min–max bound, the easy direction.** Let $T : E \to F$ be linear, let $n = \dim E$, let
$k < n$ and $c \in \mathbb{R}$, and let $S$ be a subspace of $E$ with $\dim S \ge n - k$. If
$\|Tx\| \le c \|x\|$ for all $x \in S$, then
$$\sigma_k(T) \le c.$$
-/
theorem singularValues_le_of_norm_le_mul {k : ℕ} (hk : k < finrank 𝕜 E) {c : ℝ}
    {S : Submodule 𝕜 E} (hS : finrank 𝕜 E - k ≤ finrank 𝕜 S) (h : ∀ x ∈ S, ‖T x‖ ≤ c * ‖x‖) :
    T.singularValues k ≤ c := by
  obtain ⟨x, hxS, hx0, hle⟩ :=
    T.isSymmetric_adjoint_comp_self.exists_mem_ne_zero_le_rayleighQuotient rfl ⟨k, hk⟩ hS
  rw [← T.sq_singularValues_of_lt rfl hk,
    T.sq_le_rayleighQuotient_adjoint_comp_self_iff (T.singularValues_nonneg k) hx0] at hle
  exact le_of_mul_le_mul_right (hle.trans (h x hxS)) (norm_pos_iff.2 hx0)

/-- **Max–min characterization of the singular values.** Let $T : E \to F$ be linear and
$k < \dim E$. Then $\sigma_k(T)$ is the largest real number $c$ for which there is a subspace
$S$ of $E$ with $\dim S = k + 1$ and $c \|x\| \le \|Tx\|$ for all $x \in S$. That is,
$$\sigma_k(T) = \max_{\dim S = k + 1} \ \min_{x \in S,\, x \neq 0} \frac{\|Tx\|}{\|x\|}.$$
This is the right-hand form of Theorem 8.6.1 of [golub2013matrix].

The statement is `IsGreatest` of the set of such $c$. For $k = \dim E - 1$ the subspace is $E$,
so $\sigma_{n-1}(T)$ is the least stretch $\min_{x \neq 0} \|Tx\| / \|x\|$. -/
theorem isGreatest_singularValues {k : ℕ} (hk : k < finrank 𝕜 E) :
    IsGreatest {c : ℝ | ∃ S : Submodule 𝕜 E, finrank 𝕜 S = k + 1 ∧ ∀ x ∈ S, c * ‖x‖ ≤ ‖T x‖}
      (T.singularValues k) := by
  refine ⟨?_, fun c ⟨S, hS, h⟩ => T.le_singularValues_of_mul_norm_le hS.ge h⟩
  obtain ⟨⟨S, hS, h⟩, -⟩ := T.isSymmetric_adjoint_comp_self.isGreatest_eigenvalues rfl ⟨k, hk⟩
  refine ⟨S, hS, fun x hx => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have := h x hx hx0
  rwa [← T.sq_singularValues_of_lt rfl hk,
    T.sq_le_rayleighQuotient_adjoint_comp_self_iff (T.singularValues_nonneg k) hx0] at this

/-- **Min–max characterization of the singular values.** Let $T : E \to F$ be linear, let
$n = \dim E$ and $k < n$. Then $\sigma_k(T)$ is the least real number $c$ for which there is a
subspace $S$ of $E$ with $\dim S = n - k$ and $\|Tx\| \le c \|x\|$ for all $x \in S$. That is,
$$\sigma_k(T) = \min_{\dim S = n - k} \ \max_{x \in S,\, x \neq 0} \frac{\|Tx\|}{\|x\|}.$$

The statement is `IsLeast` of the set of such $c$. For $k = 0$ the subspace is $E$, so
$\sigma_0(T)$ is the operator norm of $T$. -/
theorem isLeast_singularValues {k : ℕ} (hk : k < finrank 𝕜 E) :
    IsLeast {c : ℝ | ∃ S : Submodule 𝕜 E, finrank 𝕜 S = finrank 𝕜 E - k ∧
      ∀ x ∈ S, ‖T x‖ ≤ c * ‖x‖} (T.singularValues k) := by
  refine ⟨?_, fun c ⟨S, hS, h⟩ => T.singularValues_le_of_norm_le_mul hk hS.ge h⟩
  obtain ⟨⟨S, hS, h⟩, -⟩ := T.isSymmetric_adjoint_comp_self.isLeast_eigenvalues rfl ⟨k, hk⟩
  refine ⟨S, hS, fun x hx => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have := h x hx hx0
  rwa [← T.sq_singularValues_of_lt rfl hk,
    T.rayleighQuotient_adjoint_comp_self_le_sq_iff (T.singularValues_nonneg k) hx0] at this

/-- **Bilinear min–max characterization of the singular values.** Let $T : E \to F$ be linear with
$F \neq 0$, let $n = \dim E$ and $k < n$. Then $\sigma_k(T)$ is the least real number $c$ for
which there is a subspace $S$ of $E$ with $\dim S = n - k$ and $\operatorname{Re} \langle y, Tx
\rangle \le c \, \|x\| \, \|y\|$ for all $x \in S$ and $y \in F$. That is,
$$\sigma_k(T) = \min_{\dim S = n - k} \ \max_{x \in S,\, y \in F} \frac{\operatorname{Re}
  \langle y, Tx \rangle}{\|x\| \, \|y\|}.$$
This is the left-hand form of Theorem 8.6.1 of [golub2013matrix].

The statement is `IsLeast` of the set of such $c$. The hypothesis $F \neq 0$ is
`[Nontrivial F]`. It is needed: for $F = 0$ the form is $0$, and every real number $c$ is a
bound. -/
theorem isLeast_singularValues_bilinear [Nontrivial F] {k : ℕ} (hk : k < finrank 𝕜 E) :
    IsLeast {c : ℝ | ∃ S : Submodule 𝕜 E, finrank 𝕜 S = finrank 𝕜 E - k ∧
      ∀ x ∈ S, ∀ y : F, RCLike.re (inner 𝕜 y (T x)) ≤ c * (‖x‖ * ‖y‖)} (T.singularValues k) := by
  obtain ⟨⟨S, hS, h⟩, hlow⟩ := T.isLeast_singularValues hk
  refine ⟨⟨S, hS, fun x hx y => ?_⟩, fun c ⟨S', hS', h'⟩ => hlow ⟨S', hS', fun x hx => ?_⟩⟩
  · calc RCLike.re (inner 𝕜 y (T x)) ≤ ‖y‖ * ‖T x‖ := re_inner_le_norm _ _
      _ ≤ ‖y‖ * (T.singularValues k * ‖x‖) := by gcongr; exact h x hx
      _ = T.singularValues k * (‖x‖ * ‖y‖) := by ring
  · -- test against `y = T x`, or against a nonzero `y` when `T x = 0`
    rcases eq_or_ne (T x) 0 with h0 | h0
    · rw [h0, norm_zero]
      rcases eq_or_ne x 0 with rfl | hx0
      · simp
      obtain ⟨y, hy⟩ := exists_ne (0 : F)
      have h2 := h' x hx y
      rw [h0, inner_zero_right, map_zero] at h2
      have hpos : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.2 hx0) (norm_pos_iff.2 hy)
      have : 0 ≤ c := nonneg_of_mul_nonneg_left h2 hpos
      positivity
    · have h1 := h' x hx (T x)
      rw [inner_self_eq_norm_sq] at h1
      have hpos : 0 < ‖T x‖ := norm_pos_iff.2 h0
      nlinarith

/-! ### Weyl's inequality -/

/-- For every $k \in \mathbb{N}$ there is a subspace $S$ of $E$ with $\dim S \ge \dim E - k$ and
$\|Tx\| \le \sigma_k(T) \|x\|$ for all $x \in S$.

The difference $\dim E - k$ is truncated at $0$; for $k \ge \dim E$ the subspace can be $\{0\}$. -/
theorem exists_submodule_norm_apply_le (k : ℕ) :
    ∃ S : Submodule 𝕜 E, finrank 𝕜 E - k ≤ finrank 𝕜 S ∧
      ∀ x ∈ S, ‖T x‖ ≤ T.singularValues k * ‖x‖ := by
  by_cases hk : k < finrank 𝕜 E
  · obtain ⟨S, hS, h⟩ := (T.isLeast_singularValues hk).1
    exact ⟨S, hS.ge, h⟩
  · refine ⟨⊥, by simp; omega, fun x hx => ?_⟩
    rw [(Submodule.mem_bot 𝕜).1 hx]
    simp

/-- **Weyl's inequality for singular values.** Let $S, T : E \to F$ be linear and let
$i, j \in \mathbb{N}$. Then
$$\sigma_{i+j}(S + T) \le \sigma_i(S) + \sigma_j(T).$$
This inequality (Weyl, 1949) is the principle behind Corollaries 2.4.4 and 8.6.2 of
[golub2013matrix] and the lower half of Theorem 2.4.8 of [golub2013matrix].

The proof intersects the min–max subspaces of $S$ at $i$ and of $T$ at $j$. The intersection has
dimension at least $\dim E - (i + j)$, and $S + T$ stretches every vector in it by at most
$\sigma_i(S) + \sigma_j(T)$. -/
theorem singularValues_add_le (S T : E →ₗ[𝕜] F) (i j : ℕ) :
    (S + T).singularValues (i + j) ≤ S.singularValues i + T.singularValues j := by
  by_cases h : finrank 𝕜 E ≤ i + j
  · rw [singularValues_of_finrank_le _ h]
    exact add_nonneg (S.singularValues_nonneg i) (T.singularValues_nonneg j)
  push Not at h
  obtain ⟨VS, hVS, hS⟩ := S.exists_submodule_norm_apply_le i
  obtain ⟨VT, hVT, hT⟩ := T.exists_submodule_norm_apply_le j
  refine (S + T).singularValues_le_of_norm_le_mul h (S := VS ⊓ VT) ?_ fun x hx => ?_
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq VS VT
    have h2 := Submodule.finrank_le (VS ⊔ VT)
    omega
  · rw [add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hS x hx.1) (hT x hx.2))

/-- Let $C \ge 0$ with $\|Tx\| \le C \|x\|$ for all $x \in E$. Then $\sigma_k(T) \le C$ for every
$k$. -/
theorem singularValues_le_of_forall_norm_apply_le {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖T x‖ ≤ C * ‖x‖) (k : ℕ) : T.singularValues k ≤ C := by
  by_cases hk : k < finrank 𝕜 E
  · exact T.singularValues_le_of_norm_le_mul hk (S := ⊤) (by simp) fun x _ => h x
  · rw [singularValues_of_finrank_le _ (not_lt.1 hk)]
    exact hC

/-- **Weyl's perturbation bound for singular values.** Let $S, T : E \to F$ be linear and let
$C \ge 0$ with $\|(T - S)x\| \le C \|x\|$ for all $x \in E$. Then for every $k$,
$$|\sigma_k(T) - \sigma_k(S)| \le C.$$
This is Corollary 8.6.2 and Corollary 2.4.4 of [golub2013matrix].

The proof applies `LinearMap.singularValues_add_le` with $j = 0$ twice. The hypothesis $C \ge 0$
is needed only when $E = 0$. -/
theorem abs_singularValues_sub_le {S T : E →ₗ[𝕜] F} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖(T - S) x‖ ≤ C * ‖x‖) (k : ℕ) :
    |T.singularValues k - S.singularValues k| ≤ C := by
  have h1 := singularValues_add_le S (T - S) k 0
  have h2 := singularValues_add_le T (S - T) k 0
  rw [add_sub_cancel, add_zero] at h1
  rw [add_sub_cancel, add_zero] at h2
  have h3 := (T - S).singularValues_le_of_forall_norm_apply_le hC h 0
  have h4 := (S - T).singularValues_le_of_forall_norm_apply_le hC
    (fun x => by rw [← neg_sub, neg_apply, norm_neg]; exact h x) 0
  rw [abs_le]
  constructor <;> linarith

/-! ### Interlacing and invariance -/

variable {E' F' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [FiniteDimensional 𝕜 F']

/-- Let $T : E \to F$ and $T' : E \to F'$ be linear with $\|Tx\| \le \|T'x\|$ for all $x \in E$.
Then $\sigma_k(T) \le \sigma_k(T')$ for every $k$. -/
theorem singularValues_le_of_forall_norm_le {T' : E →ₗ[𝕜] F'} (h : ∀ x, ‖T x‖ ≤ ‖T' x‖)
    (k : ℕ) : T.singularValues k ≤ T'.singularValues k := by
  by_cases hk : k < finrank 𝕜 E
  · obtain ⟨S, hS, hS'⟩ := (T.isGreatest_singularValues hk).1
    exact T'.le_singularValues_of_mul_norm_le hS.ge fun x hx => (hS' x hx).trans (h x)
  · rw [singularValues_of_finrank_le _ (not_lt.1 hk)]
    exact T'.singularValues_nonneg k

/-- Let $T : E \to F$ and $T' : E \to F'$ be linear with $\|Tx\| = \|T'x\|$ for all $x \in E$. Then
$T$ and $T'$ have the same singular values.

In particular, composition on the left with a linear isometry does not change the singular
values (`LinearMap.singularValues_linearIsometry_comp`). -/
theorem singularValues_eq_of_forall_norm_eq {T' : E →ₗ[𝕜] F'} (h : ∀ x, ‖T x‖ = ‖T' x‖) :
    T.singularValues = T'.singularValues := by
  ext k
  exact le_antisymm (T.singularValues_le_of_forall_norm_le (fun x => (h x).le) k)
    (T'.singularValues_le_of_forall_norm_le (fun x => (h x).ge) k)

/-- Let $f : F \to F'$ be a linear isometry. Then $f \circ T$ has the same singular values as $T$.
-/
theorem singularValues_linearIsometry_comp (f : F →ₗᵢ[𝕜] F') :
    (f.toLinearMap ∘ₗ T).singularValues = T.singularValues :=
  singularValues_eq_of_forall_norm_eq _ fun x => by simp

/-- The map $-T$ has the same singular values as $T$. -/
@[simp]
theorem singularValues_neg : (-T).singularValues = T.singularValues :=
  singularValues_eq_of_forall_norm_eq _ fun x => by simp

/-- Let $e : E' \to E$ be a linear isometry. Then $\sigma_k(T \circ e) \le \sigma_k(T)$ for every
$k$.

This is the upper half of the interlacing inequalities for the restriction of the domain. -/
theorem singularValues_comp_linearIsometry_le (e : E' →ₗᵢ[𝕜] E) (k : ℕ) :
    (T ∘ₗ e.toLinearMap).singularValues k ≤ T.singularValues k := by
  by_cases hk : k < finrank 𝕜 E'
  · obtain ⟨S, hS, h⟩ := ((T ∘ₗ e.toLinearMap).isGreatest_singularValues hk).1
    refine T.le_singularValues_of_mul_norm_le (S := S.map e.toLinearMap) ?_ ?_
    · rw [finrank_map_of_injective _ e.injective, hS]
    · rintro _ ⟨y, hy, rfl⟩
      simpa using h y hy
  · rw [singularValues_of_finrank_le _ (not_lt.1 hk)]
    exact T.singularValues_nonneg k

/-- Let $e : E' \to E$ be a linear isometry with $\dim E' + r = \dim E$. Then
$\sigma_{k+r}(T) \le \sigma_k(T \circ e)$ for every $k$.

This is the lower half of the interlacing inequalities for the restriction of the domain. -/
theorem singularValues_add_le_singularValues_comp_linearIsometry (e : E' →ₗᵢ[𝕜] E) {r : ℕ}
    (hr : finrank 𝕜 E' + r = finrank 𝕜 E) (k : ℕ) :
    T.singularValues (k + r) ≤ (T ∘ₗ e.toLinearMap).singularValues k := by
  by_cases hk : k < finrank 𝕜 E'
  · obtain ⟨S, hS, h⟩ := ((T ∘ₗ e.toLinearMap).isLeast_singularValues hk).1
    refine T.singularValues_le_of_norm_le_mul (by omega) (S := S.map e.toLinearMap) ?_ ?_
    · rw [finrank_map_of_injective _ e.injective, hS]
      omega
    · rintro _ ⟨y, hy, rfl⟩
      simpa using h y hy
  · rw [singularValues_of_finrank_le _ (by omega : finrank 𝕜 E ≤ k + r)]
    exact singularValues_nonneg _ k

/-- **Interlacing of singular values under restriction to a subspace.** Let $T : E \to F$ be linear
and let $K$ be a subspace of $E$ with $\dim K + r = \dim E$. Then for every $k$,
$$\sigma_{k+r}(T) \le \sigma_k(T|_K) \le \sigma_k(T).$$
This is Corollary 8.6.3 of [golub2013matrix] in operator form, for a subspace of any codimension
$r$; the corollary is the case $r = 1$.

The restriction $T|_K$ is `LinearMap.domRestrict T K`. -/
theorem singularValues_domRestrict_interlace (K : Submodule 𝕜 E) {r : ℕ}
    (hr : finrank 𝕜 K + r = finrank 𝕜 E) (k : ℕ) :
    T.singularValues (k + r) ≤ (T.domRestrict K).singularValues k ∧
      (T.domRestrict K).singularValues k ≤ T.singularValues k :=
  ⟨T.singularValues_add_le_singularValues_comp_linearIsometry K.subtypeₗᵢ hr k,
    T.singularValues_comp_linearIsometry_le K.subtypeₗᵢ k⟩

/-- **Singular values are unitarily invariant.** Let $e : E' \to E$ be a linear isometric
isomorphism and $f : F \to F'$ a linear isometry. Then $f \circ T \circ e$ has the same singular
values as $T$. -/
theorem singularValues_comp_linearIsometryEquiv (e : E' ≃ₗᵢ[𝕜] E) (f : F →ₗᵢ[𝕜] F') :
    (f.toLinearMap ∘ₗ T ∘ₗ e.toLinearIsometry.toLinearMap).singularValues =
      T.singularValues := by
  rw [singularValues_linearIsometry_comp]
  ext k
  refine le_antisymm (T.singularValues_comp_linearIsometry_le e.toLinearIsometry k) ?_
  have h := (T ∘ₗ e.toLinearIsometry.toLinearMap).singularValues_comp_linearIsometry_le
    e.symm.toLinearIsometry k
  have hT : (T ∘ₗ e.toLinearIsometry.toLinearMap) ∘ₗ e.symm.toLinearIsometry.toLinearMap = T := by
    ext x
    simp
  rwa [hT] at h

/-- For every $k$, $\sigma_k(T) \le \sigma_k(T^*)$.

The image under $T$ of a max–min subspace of $T$ is a max–min subspace of $T^*$, because
$\|Tx\|^2 = \operatorname{Re} \langle T^* T x, x \rangle \le \|T^* T x\| \, \|x\|$. -/
theorem singularValues_le_singularValues_adjoint (k : ℕ) :
    T.singularValues k ≤ (adjoint T).singularValues k := by
  rcases (T.singularValues_nonneg k).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact singularValues_nonneg _ k
  have hk := T.lt_finrank_of_singularValues_pos hpos
  obtain ⟨S, hS, h⟩ := (T.isGreatest_singularValues hk).1
  have hinj : Function.Injective (T ∘ₗ S.subtype) := by
    rw [← ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have h1 := h x x.2
    rw [mem_ker, comp_apply, Submodule.subtype_apply] at hx
    rw [hx, norm_zero] at h1
    have h2 : ‖(x : E)‖ ≤ 0 := by nlinarith [norm_nonneg (x : E)]
    exact Subtype.ext (norm_le_zero_iff.1 h2)
  refine (adjoint T).le_singularValues_of_mul_norm_le (S := S.map T) ?_ ?_
  · rw [← Submodule.range_subtype S, ← range_comp, finrank_range_of_inj hinj, hS]
  · rintro _ ⟨x, hx, rfl⟩
    have h1 := h x hx
    have h2 : ‖T x‖ ^ 2 ≤ ‖adjoint T (T x)‖ * ‖x‖ := by
      rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), ← adjoint_inner_left]
      exact re_inner_le_norm _ _
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have hx := norm_pos_iff.2 hx0
    refine le_of_mul_le_mul_right ?_ hx
    nlinarith [norm_nonneg (T x), norm_nonneg (adjoint T (T x))]

/-- **A linear map and its adjoint have the same singular values**: $\sigma_k(T^*) = \sigma_k(T)$
for every $k \in \mathbb{N}$.

The two sequences agree at all indices, including the zeros from $\dim E$ and from $\dim F$ on. -/
@[simp]
theorem singularValues_adjoint : (adjoint T).singularValues = T.singularValues := by
  ext k
  refine le_antisymm ?_ (T.singularValues_le_singularValues_adjoint k)
  simpa using (adjoint T).singularValues_le_singularValues_adjoint k

/-- For every $x \in E$, $\|Tx\| \le \sigma_0(T) \|x\|$. So $\sigma_0(T)$ is an upper bound for the
operator norm of $T$. -/
theorem norm_apply_le_singularValues_zero_mul (x : E) :
    ‖T x‖ ≤ T.singularValues 0 * ‖x‖ := by
  rcases Nat.eq_zero_or_pos (finrank 𝕜 E) with h0 | hpos
  · rw [Module.finrank_zero_iff.1 h0 |>.elim x 0, map_zero, norm_zero, norm_zero, mul_zero]
  · obtain ⟨S, hS, h⟩ := (T.isLeast_singularValues hpos).1
    have hS' : S = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hS]; omega)
    exact h x (hS' ▸ Submodule.mem_top)

/-- **Deflation of a top singular pair.** Let $T : E \to F$ be linear, and let $u \in F$ and
$v \in E$ be unit vectors with
$$Tv = \sigma_0(T) u, \qquad T^* u = \sigma_0(T) v.$$
Let $e : E' \to E$ be a linear isometry with $\dim E' + 1 = \dim E$ whose range is orthogonal to
$v$. Then for every $i$,
$$\sigma_i(T \circ e) = \sigma_{i+1}(T).$$

The map $T$ maps $v^\perp$ into $u^\perp$, and a max–min subspace of $T \circ e$ together with
$v$ is a max–min subspace of $T$ of one more dimension. This result makes the recursive
definition of the principal angles (`Submodule.principalAngle`) well posed. -/
theorem singularValues_comp_linearIsometry_eq_succ (e : E' →ₗᵢ[𝕜] E)
    (hr : finrank 𝕜 E' + 1 = finrank 𝕜 E) {u : F} {v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hTv : T v = (T.singularValues 0 : 𝕜) • u)
    (hTu : adjoint T u = (T.singularValues 0 : 𝕜) • v) (he : ∀ x, inner 𝕜 v (e x) = 0)
    (i : ℕ) : (T ∘ₗ e.toLinearMap).singularValues i = T.singularValues (i + 1) := by
  refine le_antisymm ?_ (T.singularValues_add_le_singularValues_comp_linearIsometry e hr i)
  set c := (T ∘ₗ e.toLinearMap).singularValues i with hc
  set σ := T.singularValues 0 with hσ
  have hc0 : 0 ≤ c := singularValues_nonneg _ i
  have hcσ : c ≤ σ := (T.singularValues_comp_linearIsometry_le e i).trans
    (T.singularValues_antitone (Nat.zero_le i))
  by_cases hi : i < finrank 𝕜 E'
  swap
  · rw [hc, singularValues_of_finrank_le _ (not_lt.1 hi)]
    exact T.singularValues_nonneg _
  obtain ⟨S, hS, h⟩ := ((T ∘ₗ e.toLinearMap).isGreatest_singularValues hi).1
  have hdisj : S.map e.toLinearMap ⊓ (𝕜 ∙ v) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨⟨y, -, rfl⟩, hx⟩
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hx
    have h1 := he y
    rw [LinearIsometry.coe_toLinearMap] at hb ⊢
    rw [← hb, inner_smul_right, inner_self_eq_norm_sq_to_K, hv] at h1
    rw [← hb, show b = 0 by simpa using h1, zero_smul]
  have hS' : i + 1 + 1 ≤ finrank 𝕜 ↥(S.map e.toLinearMap ⊔ (𝕜 ∙ v)) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (S.map e.toLinearMap) (𝕜 ∙ v)
    rw [hdisj, finrank_bot, add_zero, finrank_map_of_injective _ e.injective, hS,
      finrank_span_singleton (norm_ne_zero_iff.1 (by rw [hv]; norm_num))] at h1
    omega
  refine T.le_singularValues_of_mul_norm_le hS' fun x hx => ?_
  obtain ⟨_, ⟨y, hy, rfl⟩, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [LinearIsometry.coe_toLinearMap]
  have hTey : inner 𝕜 (T (e y)) u = 0 := by
    rw [← adjoint_inner_right, hTu, inner_smul_right, ← inner_conj_symm, he, map_zero, mul_zero]
  have hey : inner 𝕜 (e y) (b • v) = 0 := by
    rw [inner_smul_right, ← inner_conj_symm, he, map_zero, mul_zero]
  have h1 : ‖e y + b • v‖ ^ 2 = ‖y‖ ^ 2 + ‖b‖ ^ 2 := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hey
    rw [pow_two, pow_two, pow_two, this, e.norm_map, norm_smul, hv, mul_one]
  have h2 : ‖T (e y + b • v)‖ ^ 2 = ‖T (e y)‖ ^ 2 + ‖b‖ ^ 2 * σ ^ 2 := by
    rw [map_add, map_smul, hTv, smul_smul]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (T (e y)) ((b * σ) • u)
      (by rw [inner_smul_right, hTey, mul_zero])
    rw [pow_two, pow_two, this, norm_smul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg
      (T.singularValues_nonneg 0), hu, mul_one]
    ring
  have h3 : c * ‖y‖ ≤ ‖T (e y)‖ := h y hy
  refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
  rw [mul_pow, h1, h2]
  have h4 : (c * ‖y‖) ^ 2 ≤ ‖T (e y)‖ ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
  have h5 : c ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hc0 hcσ 2
  nlinarith [mul_le_mul_of_nonneg_left h5 (sq_nonneg ‖b‖)]

/-! ### The singular value decomposition of a map -/

/-- **The singular value decomposition of a linear map.** Let $T : E \to F$ be linear with
$\dim E = q \le \dim F$. Then there are an orthonormal basis $v_0, \dots, v_{q-1}$ of $E$ and an
orthonormal family $u_0, \dots, u_{q-1}$ in $F$ with
$$T v_i = \sigma_i(T) \, u_i \qquad (i < q).$$
This is Theorem 2.4.1 and Corollary 2.4.2 of [golub2013matrix] in operator form.

The basis $(v_i)$ is the eigenbasis of $T^* T$ sorted by decreasing eigenvalue. The vector $u_i$
is $\sigma_i^{-1} T v_i$ where $\sigma_i \neq 0$, and the other $u_i$ complete these to an
orthonormal family. -/
theorem exists_orthonormal_singularVectors {q : ℕ} (hq : finrank 𝕜 E = q)
    (hqF : q ≤ finrank 𝕜 F) :
    ∃ (v : OrthonormalBasis (Fin q) 𝕜 E) (u : Fin q → F), Orthonormal 𝕜 u ∧
      ∀ i, T (v i) = (T.singularValues i : 𝕜) • u i := by
  set v := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hq with hv
  set w : Fin (finrank 𝕜 F) → F := fun j =>
    if h : (j : ℕ) < q then ((T.singularValues j : 𝕜)⁻¹) • T (v ⟨j, h⟩) else 0 with hw
  set s : Set (Fin (finrank 𝕜 F)) := {j | (j : ℕ) < q ∧ T.singularValues j ≠ 0} with hs
  have hws : ∀ j (hj : j ∈ s), w j = ((T.singularValues j : 𝕜)⁻¹) • T (v ⟨j, hj.1⟩) :=
    fun j hj => by simp [hw, hj.1]
  have horth : Orthonormal 𝕜 (s.domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    rw [Set.domRestrict_apply, Set.domRestrict_apply, hws i hi, hws j hj, inner_smul_left,
      inner_smul_right, hv, inner_apply_eigenvectorBasis_adjoint_comp_self]
    simp only [Subtype.mk.injEq]
    by_cases hij : i = j
    · subst hij
      have h0 : (T.singularValues i : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hi.2
      simp only [ite_true, map_inv₀, RCLike.conj_ofReal, RCLike.ofReal_pow]
      field_simp
    · have : (⟨i, hi.1⟩ : Fin q) ≠ ⟨j, hj.1⟩ := fun h => hij (Fin.ext (Fin.mk.inj_iff.1 h))
      simp [this, hij]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨v, fun i => b (Fin.castLE hqF i), b.orthonormal.comp _ (Fin.castLE_injective hqF),
    fun i => ?_⟩
  dsimp only
  by_cases h0 : T.singularValues i = 0
  · rw [h0, RCLike.ofReal_zero, zero_smul, ← norm_eq_zero, hv,
      norm_apply_eigenvectorBasis_adjoint_comp_self, h0]
  · have hi : Fin.castLE hqF i ∈ s := ⟨i.2, h0⟩
    rw [hb _ hi, hws _ hi]
    simp only [Fin.val_castLE, Fin.eta, smul_smul]
    rw [mul_inv_cancel₀ (RCLike.ofReal_ne_zero.2 h0), one_smul]

/-! ### Stacked isometries -/

/-- **The stacked-isometry identity.** Let $E$ be a finite-dimensional inner product space with
$n = \dim E \ge 1$, let $F_1$ be a finite-dimensional inner product space, and let $F_2$ be a
normed space. Let $Q_1 : E \to F_1$ and $Q_2 : E \to F_2$ be linear with
$$\|Q_1 x\|^2 + \|Q_2 x\|^2 = \|x\|^2 \qquad \text{for all } x \in E,$$
that is, $x \mapsto (Q_1 x, Q_2 x)$ is an isometry. Then
$$\|Q_2\|^2 = 1 - \sigma_{n-1}(Q_1)^2,$$
where $\sigma_{n-1}(Q_1)$ is the least singular value, the least stretch of $Q_1$.

The norm $\|Q_2\|$ is the operator norm of `LinearMap.toContinuousLinearMap Q₂`. This identity
is behind the subspace distance identity of Theorem 2.5.1 of [golub2013matrix], the norms of the
blocks of a CS decomposition, the identity (7.3.19) of [golub2013matrix], and the one-sided gap
`Submodule.gap`. -/
theorem norm_toContinuousLinearMap_sq_eq_one_sub_sq_singularValues {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (Q₁ : E →ₗ[𝕜] F₁) (Q₂ : E →ₗ[𝕜] F₂)
    (hE : 0 < finrank 𝕜 E) (hQ : ∀ x, ‖Q₁ x‖ ^ 2 + ‖Q₂ x‖ ^ 2 = ‖x‖ ^ 2) :
    ‖LinearMap.toContinuousLinearMap Q₂‖ ^ 2 = 1 - Q₁.singularValues (finrank 𝕜 E - 1) ^ 2 := by
  set σ := Q₁.singularValues (finrank 𝕜 E - 1) with hσ
  have hk : finrank 𝕜 E - 1 < finrank 𝕜 E := by omega
  have hσ0 : 0 ≤ σ := Q₁.singularValues_nonneg _
  have hQ₁ : ∀ x, ‖Q₁ x‖ ≤ 1 * ‖x‖ := fun x => by
    rw [one_mul]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      (by nlinarith [hQ x, sq_nonneg ‖Q₂ x‖])
  have hσ1 : σ ≤ 1 := Q₁.singularValues_le_of_forall_norm_apply_le zero_le_one hQ₁ _
  -- the least stretch of `Q₁` is `σ`, on all of `E`
  have hlow : ∀ x, σ * ‖x‖ ≤ ‖Q₁ x‖ := by
    obtain ⟨S, hS, h⟩ := (Q₁.isGreatest_singularValues hk).1
    have hS' : S = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hS]; omega)
    exact fun x => h x (hS' ▸ Submodule.mem_top)
  apply le_antisymm
  · have hb : ‖LinearMap.toContinuousLinearMap Q₂‖ ≤ Real.sqrt (1 - σ ^ 2) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
      rw [LinearMap.coe_toContinuousLinearMap', ← Real.sqrt_sq (norm_nonneg x),
        ← Real.sqrt_mul (by nlinarith), ← Real.sqrt_sq (norm_nonneg (Q₂ x))]
      refine Real.sqrt_le_sqrt ?_
      nlinarith [hQ x, hlow x, mul_nonneg hσ0 (norm_nonneg x)]
    calc ‖LinearMap.toContinuousLinearMap Q₂‖ ^ 2 ≤ Real.sqrt (1 - σ ^ 2) ^ 2 := by
          gcongr
      _ = 1 - σ ^ 2 := Real.sq_sqrt (by nlinarith)
  · obtain ⟨S, hS, h⟩ := (Q₁.isLeast_singularValues hk).1
    have hS1 : 0 < finrank 𝕜 S := by rw [hS]; omega
    have : Nontrivial S := Module.finrank_pos_iff.1 hS1
    obtain ⟨⟨x, hxS⟩, hx0⟩ := exists_ne (0 : S)
    have hx0' : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    have h1 := h x hxS
    have h2 := (LinearMap.toContinuousLinearMap Q₂).le_opNorm x
    rw [LinearMap.coe_toContinuousLinearMap'] at h2
    have h3 : (1 - σ ^ 2) * ‖x‖ ^ 2 ≤ ‖LinearMap.toContinuousLinearMap Q₂‖ ^ 2 * ‖x‖ ^ 2 := by
      nlinarith [hQ x, norm_nonneg (Q₂ x), norm_nonneg (Q₁ x),
        mul_nonneg (norm_nonneg (LinearMap.toContinuousLinearMap Q₂)) (norm_nonneg x)]
    exact le_of_mul_le_mul_right h3 (by positivity)

/-! ### The spectrum of the Hermitian dilation -/

section DilationSpectrum

variable (A : E →ₗ[𝕜] F)

/-- Let $A : E \to F$ be linear. Then the Hermitian dilation $(x, y) \mapsto (A^* y, Ax)$ of $A$
with its adjoint $A^*$ is a symmetric operator on $E \times F$. -/
theorem isSymmetric_hermitianDilation_adjoint : (hermitianDilation A (adjoint A)).IsSymmetric :=
  isSymmetric_hermitianDilation (isAdjointPair_inner A)

/-- The $i$-th eigenvalue of the Hermitian dilation of $A$, in decreasing order, is at most
$\sigma_i(A)$. -/
private theorem eigenvalues_hermitianDilation_le {N : ℕ}
    (hN : finrank 𝕜 (WithLp 2 (E × F)) = N) (i : Fin N) :
    A.isSymmetric_hermitianDilation_adjoint.eigenvalues hN i ≤ A.singularValues i := by
  have hσ : 0 ≤ A.singularValues i := A.singularValues_nonneg i
  obtain ⟨V, hV, hVb⟩ := A.exists_submodule_norm_apply_le i
  let ψ : V × F →ₗ[𝕜] WithLp 2 (E × F) :=
    (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ V.subtype.prodMap LinearMap.id
  have hψ : ∀ p : V × F, ψ p = WithLp.toLp 2 ((p.1 : E), p.2) := fun _ => rfl
  have hinj : Function.Injective ψ := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    rw [hψ, hψ] at h
    have h' := (WithLp.toLp_injective 2) h
    simp only [Prod.mk.injEq] at h'
    exact Prod.ext (Subtype.ext h'.1) h'.2
  have hS : N - (i : ℕ) ≤ finrank 𝕜 (range ψ) := by
    rw [finrank_range_of_inj hinj, Module.finrank_prod]
    have := WithLp.finrank_prod 2 𝕜 E F
    omega
  obtain ⟨z, ⟨⟨x, y⟩, rfl⟩, hz0, hle⟩ :=
    A.isSymmetric_hermitianDilation_adjoint.exists_mem_ne_zero_le_rayleighQuotient hN i hS
  refine hle.trans ?_
  rw [rayleighQuotient, div_le_iff₀ (pow_pos (norm_pos_iff.2 hz0) 2),
    re_inner_hermitianDilation_apply_self (isAdjointPair_inner A),
    WithLp.prod_norm_sq_eq_of_L2, hψ]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  have h1 := re_inner_le_norm (𝕜 := 𝕜) (A x) y
  have h2 := mul_le_mul_of_nonneg_right (hVb x x.2) (norm_nonneg y)
  nlinarith [mul_nonneg hσ (sq_nonneg (‖(x : E)‖ - ‖y‖))]

/-- If $\sigma_i(A) > 0$, then $\sigma_i(A)$ is at most the $i$-th eigenvalue of the Hermitian
dilation of $A$, in decreasing order. -/
private theorem singularValues_le_eigenvalues_hermitianDilation {N : ℕ}
    (hN : finrank 𝕜 (WithLp 2 (E × F)) = N) (i : Fin N) (hσ : 0 < A.singularValues i) :
    A.singularValues i ≤ A.isSymmetric_hermitianDilation_adjoint.eigenvalues hN i := by
  set σ := A.singularValues i with hσdef
  have hi := A.lt_finrank_of_singularValues_pos hσ
  obtain ⟨V, hV, hVb⟩ := (A.isGreatest_singularValues hi).1
  let ψ : V →ₗ[𝕜] WithLp 2 (E × F) :=
    (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
      ((σ : 𝕜) • V.subtype).prod (A ∘ₗ V.subtype)
  have hψ : ∀ x : V, ψ x = WithLp.toLp 2 ((σ : 𝕜) • (x : E), A x) := fun _ => rfl
  have hinj : Function.Injective ψ := by
    intro x x' h
    rw [hψ, hψ] at h
    have h' := congrArg Prod.fst ((WithLp.toLp_injective 2) h)
    exact Subtype.ext (smul_right_injective E (RCLike.ofReal_ne_zero.2 hσ.ne') h')
  have hS : (i : ℕ) + 1 ≤ finrank 𝕜 (range ψ) := by rw [finrank_range_of_inj hinj, hV]
  obtain ⟨z, ⟨x, rfl⟩, hz0, hle⟩ :=
    A.isSymmetric_hermitianDilation_adjoint.exists_mem_ne_zero_rayleighQuotient_le hN i hS
  refine le_trans ?_ hle
  rw [rayleighQuotient, le_div_iff₀ (pow_pos (norm_pos_iff.2 hz0) 2),
    re_inner_hermitianDilation_apply_self (isAdjointPair_inner A),
    WithLp.prod_norm_sq_eq_of_L2, hψ]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [map_smul, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul, inner_self_eq_norm_sq,
    norm_smul, RCLike.norm_ofReal, abs_of_pos hσ]
  have h3 : (σ * ‖(x : E)‖) ^ 2 ≤ ‖A x‖ ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hσ.le (norm_nonneg _)) (hVb x x.2) 2
  nlinarith

/-- **The spectrum of the Hermitian dilation.** Let $A : E \to F$ be linear, let $H$ be the
Hermitian dilation $(x, y) \mapsto (A^* y, Ax)$ on $E \times F$, and let $N = \dim E + \dim F$.
Then the eigenvalues $\lambda_0 \ge \dots \ge \lambda_{N-1}$ of $H$ are
$$\lambda_i = \sigma_i(A) - \sigma_{N-1-i}(A) \qquad (i < N).$$
With $p = \min(\dim E, \dim F)$, at most one of the two terms is nonzero, because
$\sigma_k(A) = 0$ for $k \ge p$. So the eigenvalues are $\sigma_0, \dots, \sigma_{p-1}$, then
$N - 2p$ zeros, then $-\sigma_{p-1}, \dots, -\sigma_0$. This is (8.6.3) of [golub2013matrix] in
operator form.

The number $N$ is given as the dimension of `WithLp 2 (E × F)`, and the eigenvalues are
`LinearMap.IsSymmetric.eigenvalues`. The proof shows $\lambda_i \le \sigma_i$ for all $i$, and
$\sigma_i \le \lambda_i$ when $\sigma_i > 0$, from subspaces for the Courant–Fischer theorem.
The dilation of $-A$ is $-H$, whose eigenvalues in decreasing order are $-\lambda_{N-1-i}$, and
this gives the other half. -/
theorem eigenvalues_hermitianDilation {N : ℕ} (hN : finrank 𝕜 (WithLp 2 (E × F)) = N)
    (i : Fin N) :
    A.isSymmetric_hermitianDilation_adjoint.eigenvalues hN i =
      A.singularValues i - A.singularValues (N - 1 - i) := by
  have hNEF := WithLp.finrank_prod 2 𝕜 E F
  have hneg : ∀ j : Fin N, (-A).isSymmetric_hermitianDilation_adjoint.eigenvalues hN j =
      -A.isSymmetric_hermitianDilation_adjoint.eigenvalues hN j.rev := by
    intro j
    rw [← A.isSymmetric_hermitianDilation_adjoint.eigenvalues_neg hN j]
    exact IsSymmetric.eigenvalues_congr _ _ (by rw [map_neg, hermitianDilation_neg]) hN j
  have hrev : ((i.rev : Fin N) : ℕ) = N - 1 - i := by rw [Fin.val_rev]; omega
  have h1 := A.eigenvalues_hermitianDilation_le hN i
  have h3 := (-A).eigenvalues_hermitianDilation_le hN i.rev
  rw [hneg, Fin.rev_rev, singularValues_neg, hrev] at h3
  have hs := A.singularValues_nonneg i
  have hs' := A.singularValues_nonneg (N - 1 - i)
  rcases hs.eq_or_lt with h0 | hpos
  · rw [← h0]
    rw [← h0] at h1
    rcases hs'.eq_or_lt with h0' | hpos'
    · rw [← h0'] at h3 ⊢
      linarith
    · have h4 := (-A).singularValues_le_eigenvalues_hermitianDilation hN i.rev
        (by rwa [singularValues_neg, hrev])
      rw [hneg, Fin.rev_rev, singularValues_neg, hrev] at h4
      linarith
  · -- `σ_i > 0` forces `σ_{N-1-i} = 0`
    have hiF : (i : ℕ) < finrank 𝕜 F := by
      by_contra h
      rw [A.singularValues_of_finrank_codomain_le (not_lt.1 h)] at hpos
      exact lt_irrefl _ hpos
    have hz : A.singularValues (N - 1 - i) = 0 :=
      A.singularValues_of_finrank_le (by omega)
    have h2 := A.singularValues_le_eigenvalues_hermitianDilation hN i hpos
    rw [hz]
    linarith

end DilationSpectrum

end LinearMap
