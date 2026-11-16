/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Rayleigh`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Trace
import Numlib.Analysis.InnerProductSpace.Projection.Compression
import Numlib.Analysis.InnerProductSpace.Spectrum
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearAlgebra.Dimension.Finrank

/-!
# Courant–Fischer: the variational characterization of eigenvalues

Let $E$ be an inner product space of dimension $n$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$,
and let $T \colon E \to E$ be symmetric. Let $\lambda_0 \ge \lambda_1 \ge \dots \ge \lambda_{n-1}$
be the eigenvalues of $T$, sorted in decreasing order and indexed from $0$, with an orthonormal
basis $v_0, \dots, v_{n-1}$ of eigenvectors. The **Rayleigh quotient** of $T$ at $x \neq 0$ is
$r_T(x) = \operatorname{Re} \langle Tx, x \rangle / \|x\|^2$. The **min–max theorem** of Courant,
Fischer, Poincaré and Weyl characterizes each eigenvalue through the Rayleigh quotient on subspaces:
$$\lambda_i = \max_{\dim S = i + 1} \ \min_{0 \neq x \in S} r_T(x)
  = \min_{\dim S = n - i} \ \max_{0 \neq x \in S} r_T(x).$$
These are the two formulas of [saad2011numerical], Theorem 1.9, and the second one is
[kress1998numerical], Theorem 7.4. Mathlib has only the two extreme eigenvalues, through
`LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` and its `iInf` twin.

The file derives from this the standard consequences: Rayleigh's recursive characterization, Weyl's
inequality $|\lambda_i(A) - \lambda_i(B)| \le \|A - B\|$, Cauchy interlacing for compressions and
principal submatrices, low-rank interlacing, Ky Fan's maximum and minimum principles, the trace
inequality and the Hoffman–Wielandt inequality. It also computes the gradient of the Rayleigh
quotient and shows that its stationary points are the eigenvectors. Here $\lambda_i(A)$ is the
$i$-th eigenvalue of $A$ in decreasing order.

## Main definitions

* `LinearMap.rayleighQuotient`: the Rayleigh quotient $r_T(x) = \operatorname{Re} \langle Tx, x
  \rangle / \|x\|^2$ of a linear map.
* `LinearMap.IsSymmetric.eigenvectorSpan`: the span $V_s$ of the eigenvectors $v_i$ with $i \in s$.
* `Matrix.IsHermitian.sortedEigenvalues`: the eigenvalues of a Hermitian $n \times n$ matrix, in
  decreasing order and indexed by $\{0, \dots, n - 1\}$.

## Main results

* `LinearMap.IsSymmetric.exists_mem_ne_zero_rayleighQuotient_le` and
  `LinearMap.IsSymmetric.le_rayleighQuotient_of_mem_eigenvectorSpan_Iic`: the two directions of
  Courant–Fischer. Every subspace of dimension at least $i + 1$ contains an $x \neq 0$ with
  $r_T(x) \le \lambda_i$, and $r_T \ge \lambda_i$ on the span of $v_0, \dots, v_i$. These two
  statements are usually the most convenient ones to use.
* `LinearMap.IsSymmetric.isGreatest_eigenvalues` and `LinearMap.IsSymmetric.isLeast_eigenvalues`:
  the max–min and min–max characterizations, as the greatest or least element of an explicit set of
  reals.
* `LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf` and
  `LinearMap.IsSymmetric.eigenvalues_eq_iInf_iSup`: the same as $\sup\inf$ and $\inf\sup$ formulas.
* `LinearMap.IsSymmetric.isGreatest_rayleighQuotient_orthogonal`: Rayleigh's recursive form,
  $\lambda_i$ is the maximum of $r_T$ over the nonzero vectors orthogonal to $v_0, \dots, v_{i-1}$.
* `LinearMap.IsSymmetric.abs_eigenvalues_sub_le`: Weyl's inequality,
  $|\lambda_i(A) - \lambda_i(B)| \le C$ if $\|(A - B) x\| \le C \|x\|$ for all $x$.
* `LinearMap.IsSymmetric.eigenvalues_add_mem_Icc`: the two-sided Weyl inequality $\lambda_i(A) +
  \lambda_{\min}(B) \le \lambda_i(A + B) \le \lambda_i(A) + \lambda_{\max}(B)$ ([golub2013matrix],
  Theorem 8.1.5).
* `LinearMap.IsSymmetric.eigenvalues_interlace_of_linearIsometry`: Cauchy interlacing, $\lambda_{i +
  n - m}(T) \le \lambda_i(S) \le \lambda_i(T)$ when the quadratic form of $S$ on an $m$-dimensional
  space is that of $T$ pulled back along a linear isometry. Its special cases are
  `LinearMap.IsSymmetric.eigenvalues_restrict_interlace` for a subspace and
  `Matrix.IsHermitian.eigenvalues₀_submatrix_interlace` for a principal submatrix.
* `LinearMap.IsSymmetric.eigenvalues_le_of_finrank_range_sub_le`: low-rank interlacing, if
  $\operatorname{rank}(B - A) \le r$ then $\lambda_{i + r}(B) \le \lambda_i(A)$. With $B - A$
  positive this is `LinearMap.IsSymmetric.eigenvalues_le_of_isPositive_sub_of_finrank_range_le`
  ([golub2013matrix], Theorem 8.1.8, for $r = 1$).
* `LinearMap.IsSymmetric.sum_re_inner_le_sum_eigenvalues` and
  `LinearMap.IsSymmetric.sum_eigenvalues_le_sum_re_inner`: Ky Fan's maximum and minimum principles,
  $\sum_{i < k} \lambda_{n - k + i} \le \sum_{i < k} \operatorname{Re} \langle T x_i, x_i \rangle
  \le \sum_{i < k} \lambda_i$ for an orthonormal family $(x_i)_{i < k}$.
* `LinearMap.IsSymmetric.re_trace_comp_le_sum_eigenvalues_mul`: the trace inequality
  $\operatorname{Re} \operatorname{tr}(AB) \le \sum_i \lambda_i(A) \lambda_i(B)$.
* `LinearMap.IsSymmetric.sum_sq_eigenvalues_sub_le` and its matrix form
  `Matrix.IsHermitian.hoffman_wielandt`: the **Hoffman–Wielandt inequality** $\sum_k (\lambda_k(A) -
  \lambda_k(B))^2 \le \|A - B\|_F^2$ ([golub2013matrix], Theorem 8.1.4).
* `Matrix.IsHermitian.sortedEigenvalues_submatrix_castSucc_interlace`: Cauchy interlacing for the
  leading principal submatrix of order $n$ of a Hermitian matrix of order $n + 1$.
* `Matrix.IsHermitian.exists_unitary_conj_eq_diagonal_sortedEigenvalues`: the spectral decomposition
  with sorted eigenvalues, $U^H A U = \operatorname{diag}(\lambda_0, \dots, \lambda_{n-1})$
  ([golub2013matrix], Theorem 8.1.1).
* `ContinuousLinearMap.hasGradientAt_rayleighQuotient`: the gradient of the Rayleigh quotient is
  $\nabla r(x) = 2 (Tx - r(x) x) / \|x\|^2$ ([golub2013matrix], (10.1.1)).
* `LinearMap.IsSymmetric.hasFDerivAt_rayleighQuotient_eq_zero_iff`: the stationary points of the
  Rayleigh quotient are exactly the eigenvectors ([golub2013matrix], (12.5.23)). Mathlib has only
  the extremal case, `IsSelfAdjoint.hasEigenvector_of_isLocalExtrOn`.
* `LinearMap.IsSymmetric.eigenvalues_eq_of_apply_eq_ofReal_smul`: the sorted eigenvalues are those
  of any orthonormal eigenbasis with decreasing eigenvalues. So a statement about an arbitrary Schur
  decomposition reduces to the sorted eigenvalues, and the coordinate identities in such a basis are
  `OrthonormalBasis.repr_apply_of_apply_eq_smul` and the lemmas after it.
* `LinearMap.IsSymmetric.eigenvalues_neg`: $\lambda_i(-T) = -\lambda_{n-1-i}(T)$. This reduction
  turns a statement about a largest eigenvalue into the matching statement about a smallest one.
  `LinearMap.IsSymmetric.exists_smul_eigenvectorBasis_neg` transports the eigenvector at a simple
  eigenvalue.

## Proof outline

The first direction of Courant–Fischer is a dimension count: a subspace of dimension $i + 1$ and the
span of $v_i, \dots, v_{n-1}$, of dimension $n - i$, have dimensions with sum greater than $n$, so
they meet in a nonzero vector, and there $r_T \le \lambda_i$. The second direction is the bound
$r_T \ge \lambda_i$ on the span of $v_0, \dots, v_i$, read off the coordinates in the eigenbasis.
Cauchy interlacing follows because, through the isometry, the subspaces of the smaller space are
among the subspaces of $E$ of the same dimension. Ky Fan's principles follow from interlacing: the
sum $\sum_i \operatorname{Re} \langle T x_i, x_i \rangle$ is the trace of the compression of $T$ to
the span of the family, that is, the sum of the eigenvalues of the compression. The trace inequality
follows from Ky Fan by summation by parts, and the Hoffman–Wielandt inequality follows from the
trace inequality by expanding the square.

## Implementation notes

* The books index the eigenvalues from $1$ in decreasing order. So their $\lambda_k$ is
  `hT.eigenvalues hn i` for $i = k - 1$, and their subspace dimensions $k$ and $n + 1 - k$ are
  $i + 1$ and $n - i$ here.
* The $\sup$/$\inf$ forms quantify over subtypes, `{S : Submodule 𝕜 E // finrank 𝕜 S = i + 1}` and
  `{x : E // x ∈ S ∧ x ≠ 0}`, and not over all subspaces and all vectors with a nested `⨆ _ : P, ·`.
  The nested form gives wrong values: an `iSup` over a false proposition is `sSup ∅ = 0` in `ℝ`, so
  the statement would be silently cut off at $0$. The forms with `IsGreatest` and `IsLeast` contain
  no `iSup` at all and are the recommended interface.
* Weyl's inequality assumes a bound $\|(A - B) x\| \le C \|x\|$ for all $x$ and not a bound on an
  operator norm, because `E →ₗ[𝕜] E` has no norm and the assumed form does not force a topology on
  the user. `LinearMap.IsSymmetric.abs_eigenvalues_sub_le_opNorm` is the corollary for continuous
  linear maps. The underlying lemma `LinearMap.IsSymmetric.eigenvalues_le_add_of_re_inner_le`
  assumes even less: only the bound $\operatorname{Re} \langle Ax, x \rangle \le \operatorname{Re}
  \langle Bx, x \rangle + C \|x\|^2$ on the quadratic forms, which is what the proof in
  [kress1998numerical] uses. This library prefers that form for spectral hypotheses.
* The Rayleigh quotient is $0$ at $x = 0$, because $0 / 0 = 0$ in Lean. Every statement excludes
  $x = 0$ explicitly.
* The inner product $\langle x, y \rangle$ is conjugate-linear in $x$, and
  $\operatorname{Re} \langle Tx, x \rangle$ is `RCLike.re (inner 𝕜 (T x) x)`.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Let $V$ be a finite-dimensional vector space over a division ring, and let $S$ and $W$ be
subspaces with $\dim V < \dim S + \dim W$. Then $S \cap W$ contains a nonzero vector.

This is the dimension count behind Courant–Fischer. -/
theorem Submodule.exists_mem_inf_ne_zero {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {S W : Submodule K V}
    (h : Module.finrank K V < Module.finrank K S + Module.finrank K W) :
    ∃ x ∈ S ⊓ W, x ≠ 0 := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S W
  have hle : Module.finrank K (S ⊔ W : Submodule K V) ≤ Module.finrank K V :=
    Submodule.finrank_le _
  have hpos : 0 < Module.finrank K (S ⊓ W : Submodule K V) := by omega
  have : Nontrivial (S ⊓ W : Submodule K V) := Module.finrank_pos_iff.mp hpos
  obtain ⟨y, hy⟩ := exists_ne (0 : (S ⊓ W : Submodule K V))
  exact ⟨y, y.2, fun h0 => hy (Subtype.ext h0)⟩

namespace LinearMap

/-- The **Rayleigh quotient** of a linear map $T \colon E \to E$ at a vector $x$ is the real number
$$r_T(x) = \frac{\operatorname{Re} \langle Tx, x \rangle}{\|x\|^2}.$$

At $x = 0$ its value is $0$. This is the `LinearMap` counterpart of
`ContinuousLinearMap.rayleighQuotient`; the two agree by
`ContinuousLinearMap.rayleighQuotient_eq_toLinearMap`. -/
noncomputable abbrev rayleighQuotient (T : E →ₗ[𝕜] E) (x : E) : ℝ :=
  RCLike.re (inner 𝕜 (T x) x) / ‖x‖ ^ 2

/-- The Rayleigh quotient at the zero vector has the value $0$, since $0 / 0 = 0$ in Lean. This
value has no meaning, and every statement below excludes $x = 0$ explicitly. -/
@[simp]
theorem rayleighQuotient_apply_zero (T : E →ₗ[𝕜] E) : T.rayleighQuotient 0 = 0 := by
  simp [rayleighQuotient]

/-- Let $T \colon E \to E$ be linear and let $\|x\| = 1$. Then the Rayleigh quotient is the
quadratic form: $r_T(x) = \operatorname{Re} \langle Tx, x \rangle$.

The approximate eigenpairs of `Numlib.Eigen.Perturbation` are stated in this form. -/
theorem rayleighQuotient_of_norm_eq_one (T : E →ₗ[𝕜] E) {x : E} (hx : ‖x‖ = 1) :
    T.rayleighQuotient x = RCLike.re (inner 𝕜 (T x) x) := by
  rw [rayleighQuotient, hx, one_pow, div_one]

/-- The Rayleigh quotient is invariant under scaling. Let $T \colon E \to E$ be linear, let
$x \in E$, and let $c \in \mathbb{K}$ with $c \neq 0$. Then $r_T(cx) = r_T(x)$.

So a bound at a nonzero vector carries over to its normalization. -/
theorem rayleighQuotient_smul (T : E →ₗ[𝕜] E) (x : E) {c : 𝕜} (hc : c ≠ 0) :
    T.rayleighQuotient (c • x) = T.rayleighQuotient x := by
  have hc2 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  rw [rayleighQuotient, rayleighQuotient, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul, norm_smul, mul_pow,
    mul_div_mul_left _ _ hc2]

/-- The Rayleigh quotient is additive in the operator: $r_{A - B}(x) = r_A(x) - r_B(x)$ for all
linear maps $A, B$ and all $x$. -/
theorem rayleighQuotient_sub (A B : E →ₗ[𝕜] E) (x : E) :
    (A - B).rayleighQuotient x = A.rayleighQuotient x - B.rayleighQuotient x := by
  rw [rayleighQuotient, rayleighQuotient, rayleighQuotient, sub_apply, inner_sub_left, map_sub,
    sub_div]

/-- Let $T \colon E \to E$ be linear. Then $r_{-T}(x) = -r_T(x)$ for every $x \in E$.

This identity exchanges the max–min and the min–max characterizations of the eigenvalues
(`LinearMap.IsSymmetric.eigenvalues_neg`). -/
theorem rayleighQuotient_neg (T : E →ₗ[𝕜] E) (x : E) :
    (-T).rayleighQuotient x = -T.rayleighQuotient x := by
  simp [LinearMap.rayleighQuotient, inner_neg_left, neg_div]

/-- If $T \colon E \to E$ is symmetric, then $-T$ is symmetric.

This completes the Mathlib lemmas `LinearMap.IsSymmetric.add`, `LinearMap.IsSymmetric.sub` and
`LinearMap.IsSymmetric.smul`. -/
theorem IsSymmetric.neg {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) : (-T).IsSymmetric := fun x y => by
  simp only [LinearMap.neg_apply, inner_neg_left, inner_neg_right, hT x y]

/-- Let $T$ be linear, let $c, C, D \in \mathbb{R}$ with $C \ge 0$ and $0 < D \le \|x\|^2$, and
assume $c \|x\|^2 - \operatorname{Re} \langle Tx, x \rangle \le C D$. Then $c - r_T(x) \le C$. -/
theorem sub_rayleighQuotient_le_of_le (T : E →ₗ[𝕜] E) {x : E} {c C D : ℝ} (hC : 0 ≤ C)
    (hD : 0 < D) (hDx : D ≤ ‖x‖ ^ 2)
    (h : c * ‖x‖ ^ 2 - RCLike.re (inner 𝕜 (T x) x) ≤ C * D) :
    c - T.rayleighQuotient x ≤ C := by
  have hx : 0 < ‖x‖ ^ 2 := hD.trans_le hDx
  have hsplit : c - T.rayleighQuotient x =
      (c * ‖x‖ ^ 2 - RCLike.re (inner 𝕜 (T x) x)) / ‖x‖ ^ 2 := by
    rw [rayleighQuotient, sub_div, mul_div_assoc, div_self hx.ne', mul_one]
  rw [hsplit, div_le_iff₀ hx]
  exact h.trans (mul_le_mul_of_nonneg_left hDx hC)

end LinearMap

/-- Let $T \colon E \to E$ be a continuous linear map. Then the Rayleigh quotient of $T$
(`ContinuousLinearMap.rayleighQuotient`) equals the Rayleigh quotient of the underlying linear
map (`LinearMap.rayleighQuotient`) at every $x \in E$. -/
theorem ContinuousLinearMap.rayleighQuotient_eq_toLinearMap (T : E →L[𝕜] E) (x : E) :
    T.rayleighQuotient x = (T : E →ₗ[𝕜] E).rayleighQuotient x :=
  rfl

/-!
### An orthonormal eigenbasis

The statements in this section are about an arbitrary orthonormal basis $(b_i)$ of eigenvectors of
$T$, with $T b_i = \mu_i b_i$. The coordinates of $x$ in this basis are
$x_i = \langle b_i, x \rangle$. Mathlib's `LinearMap.IsSymmetric.eigenvectorBasis` is one such
basis, and the lemmas about it below are special cases of these. A textbook statement about an
arbitrary Schur decomposition uses these lemmas directly.
-/

namespace OrthonormalBasis

variable {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) {T : E →ₗ[𝕜] E}

section Eigenbasis

variable {μ : ι → 𝕜} (hb : ∀ i, T (b i) = μ i • b i)
include hb

/-- In an orthonormal eigenbasis, $T$ acts on coordinates by its eigenvalues: $(Tx)_i = \mu_i x_i$.
-/
theorem repr_apply_of_apply_eq_smul (x : E) (i : ι) : b.repr (T x) i = μ i * b.repr x i := by
  classical
  conv_lhs => rw [← b.sum_repr x]
  simp [map_sum, hb, smul_smul, Pi.single_apply, mul_comm]

/-- In an orthonormal eigenbasis, $T^k$ acts on coordinates by the $k$-th powers of the eigenvalues:
$(T^k x)_i = \mu_i^k x_i$. -/
theorem repr_pow_apply_of_apply_eq_smul (k : ℕ) (x : E) (i : ι) :
    b.repr ((T ^ k) x) i = μ i ^ k * b.repr x i := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih, b.repr_apply_of_apply_eq_smul hb]
      ring

/-- In an orthonormal eigenbasis, $\langle b_i, T^k x \rangle = \mu_i^k \langle b_i, x \rangle$. -/
theorem inner_pow_apply_of_apply_eq_smul (k : ℕ) (x : E) (i : ι) :
    (inner 𝕜 (b i) ((T ^ k) x) : 𝕜) = μ i ^ k * inner 𝕜 (b i) x := by
  simpa only [OrthonormalBasis.repr_apply_apply] using b.repr_pow_apply_of_apply_eq_smul hb k x i

/-- In an orthonormal eigenbasis, $p(T)$ acts on coordinates by the values of the polynomial $p$ at
the eigenvalues: $(p(T) x)_i = p(\mu_i) x_i$. -/
theorem repr_aeval_apply_of_apply_eq_smul (p : Polynomial 𝕜) (x : E) (i : ι) :
    b.repr (Polynomial.aeval T p x) i = p.eval (μ i) * b.repr x i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial k c =>
      have hmon : Polynomial.aeval T (Polynomial.monomial k c) x = c • (T ^ k) x := by
        simp [Polynomial.aeval_monomial]
      rw [hmon, map_smul, PiLp.smul_apply, smul_eq_mul, b.repr_pow_apply_of_apply_eq_smul hb,
        Polynomial.eval_monomial]
      ring

end Eigenbasis

section RealEigenbasis

variable {lam : ι → ℝ} (hb : ∀ i, T (b i) = (lam i : 𝕜) • b i)
include hb

/-- An operator that has an orthonormal eigenbasis with real eigenvalues is symmetric. -/
theorem isSymmetric_of_apply_eq_ofReal_smul : T.IsSymmetric := by
  intro x y
  rw [← b.sum_inner_mul_inner (T x) y, ← b.sum_inner_mul_inner x (T y)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := b.repr_apply_of_apply_eq_smul hb
  simp only [OrthonormalBasis.repr_apply_apply] at h1
  rw [h1, ← inner_conj_symm (T x), h1, map_mul, RCLike.conj_ofReal, inner_conj_symm]
  ring

/-- If $T b_i = \lambda_i b_i$ with real $\lambda_i$ in an orthonormal basis $(b_i)$, then
$\operatorname{Re} \langle Tx, x \rangle = \sum_i \lambda_i |x_i|^2$. -/
theorem re_inner_apply_self_eq_sum (x : E) :
    RCLike.re (inner 𝕜 (T x) x) = ∑ i, lam i * ‖b.repr x i‖ ^ 2 := by
  rw [← b.sum_inner_mul_inner (T x) x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [b.isSymmetric_of_apply_eq_ofReal_smul hb x (b i), hb, inner_smul_right,
    ← inner_conj_symm x (b i), mul_assoc, RCLike.conj_mul, OrthonormalBasis.repr_apply_apply]
  simp

/-- If $T b_i = \lambda_i b_i$ with real $\lambda_i$ in an orthonormal basis $(b_i)$, then for every
$c \in \mathbb{R}$
$$c \|x\|^2 - \operatorname{Re} \langle Tx, x \rangle = \sum_i (c - \lambda_i) |x_i|^2.$$
-/
theorem mul_norm_sq_sub_re_inner_eq_sum (c : ℝ) (x : E) :
    c * ‖x‖ ^ 2 - RCLike.re (inner 𝕜 (T x) x) = ∑ i, (c - lam i) * ‖b.repr x i‖ ^ 2 := by
  have hx : ‖x‖ ^ 2 = ∑ i, ‖b.repr x i‖ ^ 2 := by
    simpa only [OrthonormalBasis.repr_apply_apply] using (b.sum_sq_norm_inner_right x).symm
  rw [hx, b.re_inner_apply_self_eq_sum hb, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Let $T b_i = \lambda_i b_i$ with real $\lambda_i$ in an orthonormal basis $(b_i)$, let
$c \in \mathbb{R}$, and let $s$ be a finite set of indices such that $c \le \lambda_i$ or
$x_i = 0$ for each $i \notin s$. Then
$$c \|x\|^2 - \operatorname{Re} \langle Tx, x \rangle \le \sum_{i \in s} (c - \lambda_i)
  |x_i|^2.$$

This is the estimate behind every bound on an eigenvalue minus a Rayleigh quotient. -/
theorem mul_norm_sq_sub_re_inner_le_sum (c : ℝ) (x : E) {s : Finset ι}
    (hs : ∀ i ∉ s, c ≤ lam i ∨ b.repr x i = 0) :
    c * ‖x‖ ^ 2 - RCLike.re (inner 𝕜 (T x) x) ≤ ∑ i ∈ s, (c - lam i) * ‖b.repr x i‖ ^ 2 := by
  classical
  rw [b.mul_norm_sq_sub_re_inner_eq_sum hb, ← Finset.sum_add_sum_compl s]
  have : ∑ i ∈ sᶜ, (c - lam i) * ‖b.repr x i‖ ^ 2 ≤ 0 := by
    refine Finset.sum_nonpos fun i hi => ?_
    rcases hs i (Finset.mem_compl.1 hi) with h | h
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    · simp [h]
  linarith

end RealEigenbasis

end OrthonormalBasis

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ} {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n)
include hT

/-!
### The eigenbasis expansion

Every statement below is read off the coordinates $x_i = \langle v_i, x \rangle$ of a vector in the
orthonormal eigenvector basis `hT.eigenvectorBasis hn`. In these coordinates the norm and the
quadratic form are the two sums of this section.
-/

/-- Parseval's identity in the eigenvector basis: $\|x\|^2 = \sum_i |x_i|^2$. -/
theorem norm_sq_eq_sum_norm_repr_sq (x : E) :
    ‖x‖ ^ 2 = ∑ i, ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  simpa only [OrthonormalBasis.repr_apply_apply] using
    ((hT.eigenvectorBasis hn).sum_sq_norm_inner_right x).symm

/-- The quadratic form of a symmetric operator in the coordinates of its eigenvector basis:
$\operatorname{Re} \langle Tx, x \rangle = \sum_i \lambda_i |x_i|^2$. -/
theorem re_inner_apply_self_eq_sum (x : E) :
    RCLike.re (inner 𝕜 (T x) x) =
      ∑ i, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 :=
  (hT.eigenvectorBasis hn).re_inner_apply_self_eq_sum (hT.apply_eigenvectorBasis hn) x

/-- For a symmetric $T$ and every $c \in \mathbb{R}$, $c \|x\|^2 - \operatorname{Re} \langle Tx, x
\rangle = \sum_i (c - \lambda_i) |x_i|^2$ in the eigenvector basis.

This is the form in which an eigenvalue minus a Rayleigh quotient is estimated, one coordinate
at a time. -/
theorem mul_norm_sq_sub_re_inner_eq_sum (c : ℝ) (x : E) :
    c * ‖x‖ ^ 2 - RCLike.re (inner 𝕜 (T x) x) =
      ∑ i, (c - hT.eigenvalues hn i) * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 :=
  (hT.eigenvectorBasis hn).mul_norm_sq_sub_re_inner_eq_sum (hT.apply_eigenvectorBasis hn) c x

/-- The vectors $v_i$ of the eigenvector basis are nonzero. -/
theorem eigenvectorBasis_ne_zero (i : Fin n) : hT.eigenvectorBasis hn i ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [(hT.eigenvectorBasis hn).norm_eq_one i]; norm_num)

/-- The Rayleigh quotient at the eigenvector $v_i$ is its eigenvalue: $r_T(v_i) = \lambda_i$. -/
@[simp]
theorem rayleighQuotient_eigenvectorBasis (i : Fin n) :
    T.rayleighQuotient (hT.eigenvectorBasis hn i) = hT.eigenvalues hn i := by
  rw [T.rayleighQuotient_of_norm_eq_one ((hT.eigenvectorBasis hn).norm_eq_one i),
    hT.apply_eigenvectorBasis hn, inner_smul_left, inner_self_eq_norm_sq_to_K,
    (hT.eigenvectorBasis hn).norm_eq_one i]
  simp

/-! ### Spans of eigenvectors -/

/-- Let $T$ be a symmetric operator on an inner product space $E$ of dimension $n$, and let
$s \subseteq \{0, \dots, n - 1\}$. The **eigenvector span** $V_s$ is the span of the
eigenvectors $v_i$ with $i \in s$, in the orthonormal eigenvector basis `hT.eigenvectorBasis hn`
whose eigenvalues decrease.

Courant–Fischer uses two cases: $s = \{0, \dots, i\}$ (`Finset.Iic i`), the eigenvectors for the
$i + 1$ largest eigenvalues, and $s = \{i, \dots, n - 1\}$ (`Finset.Ici i`), the eigenvectors
for the $n - i$ smallest ones. -/
noncomputable def eigenvectorSpan (s : Finset (Fin n)) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (hT.eigenvectorBasis hn '' s)

/-- If $i \in s$, then $v_i \in V_s$. -/
theorem eigenvectorBasis_mem_eigenvectorSpan {s : Finset (Fin n)} {i : Fin n} (hi : i ∈ s) :
    hT.eigenvectorBasis hn i ∈ hT.eigenvectorSpan hn s :=
  Submodule.subset_span ⟨i, hi, rfl⟩

/-- Let $T$ be a symmetric operator on an inner product space of dimension $n$, and let
$s \subseteq \{0, \dots, n - 1\}$. A vector $x$ lies in $V_s$ if and only if its eigenbasis
coordinates $x_i$ vanish for all $i \notin s$. -/
theorem mem_eigenvectorSpan_iff {s : Finset (Fin n)} {x : E} :
    x ∈ hT.eigenvectorSpan hn s ↔ ∀ i ∉ s, (hT.eigenvectorBasis hn).repr x i = 0 := by
  rw [eigenvectorSpan, ← (hT.eigenvectorBasis hn).coe_toBasis,
    (hT.eigenvectorBasis hn).toBasis.mem_span_image, Finsupp.support_subset_iff]
  simp only [Finset.mem_coe, OrthonormalBasis.coe_toBasis_repr_apply]

/-- The eigenvectors span the whole space: $V_{\{0, \dots, n - 1\}} = E$. -/
@[simp]
theorem eigenvectorSpan_univ : hT.eigenvectorSpan hn Finset.univ = ⊤ :=
  eq_top_iff.mpr fun _x _ => (hT.mem_eigenvectorSpan_iff hn).mpr fun i hi =>
    absurd (Finset.mem_univ i) hi

/-- Let $T$ be a symmetric operator on an inner product space of dimension $n$, and let
$s \subseteq \{0, \dots, n - 1\}$. Then $\dim V_s = |s|$.

The eigenvector basis is orthonormal and hence linearly independent. This is the dimension count
of Courant–Fischer. -/
theorem finrank_eigenvectorSpan (s : Finset (Fin n)) :
    Module.finrank 𝕜 (hT.eigenvectorSpan hn s) = s.card := by
  have hli : LinearIndependent 𝕜 fun j : (s : Set (Fin n)) => hT.eigenvectorBasis hn j :=
    (hT.eigenvectorBasis hn).orthonormal.linearIndependent.comp _ Subtype.val_injective
  rw [eigenvectorSpan, Set.image_eq_range, finrank_span_eq_card hli]
  simp

/-! ### Bounds on the Rayleigh quotient over a span of eigenvectors -/

/-- If $\lambda_i \le c$ for all $i \in s$ and $x \in V_s$, then $\operatorname{Re} \langle Tx, x
\rangle \le c \|x\|^2$. -/
theorem re_inner_apply_self_le_of_mem_eigenvectorSpan {s : Finset (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, hT.eigenvalues hn i ≤ c) {x : E} (hx : x ∈ hT.eigenvectorSpan hn s) :
    RCLike.re (inner 𝕜 (T x) x) ≤ c * ‖x‖ ^ 2 := by
  rw [hT.re_inner_apply_self_eq_sum hn, hT.norm_sq_eq_sum_norm_repr_sq hn, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hc i hi) (sq_nonneg _)
  · rw [(hT.mem_eigenvectorSpan_iff hn).mp hx i hi]
    simp

/-- If $c \le \lambda_i$ for all $i \in s$ and $x \in V_s$, then $c \|x\|^2 \le \operatorname{Re}
\langle Tx, x \rangle$. -/
theorem le_re_inner_apply_self_of_mem_eigenvectorSpan {s : Finset (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, c ≤ hT.eigenvalues hn i) {x : E} (hx : x ∈ hT.eigenvectorSpan hn s) :
    c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x) x) := by
  rw [hT.re_inner_apply_self_eq_sum hn, hT.norm_sq_eq_sum_norm_repr_sq hn, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hc i hi) (sq_nonneg _)
  · rw [(hT.mem_eigenvectorSpan_iff hn).mp hx i hi]
    simp

/-- If $\lambda_i \le c$ for all $i \in s$ and $0 \neq x \in V_s$, then $r_T(x) \le c$. -/
theorem rayleighQuotient_le_of_mem_eigenvectorSpan {s : Finset (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, hT.eigenvalues hn i ≤ c) {x : E} (hx : x ∈ hT.eigenvectorSpan hn s)
    (hx0 : x ≠ 0) : T.rayleighQuotient x ≤ c := by
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
  rw [LinearMap.rayleighQuotient, div_le_iff₀ hpos]
  exact hT.re_inner_apply_self_le_of_mem_eigenvectorSpan hn hc hx

/-- If $c \le \lambda_i$ for all $i \in s$ and $0 \neq x \in V_s$, then $c \le r_T(x)$. -/
theorem le_rayleighQuotient_of_mem_eigenvectorSpan {s : Finset (Fin n)} {c : ℝ}
    (hc : ∀ i ∈ s, c ≤ hT.eigenvalues hn i) {x : E} (hx : x ∈ hT.eigenvectorSpan hn s)
    (hx0 : x ≠ 0) : c ≤ T.rayleighQuotient x := by
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
  rw [LinearMap.rayleighQuotient, le_div_iff₀ hpos]
  exact hT.le_re_inner_apply_self_of_mem_eigenvectorSpan hn hc hx

/-- If $\lambda_i \le c$ for all $i$, then $r_T(x) \le c$ for every $x \neq 0$. -/
theorem rayleighQuotient_le_of_forall {c : ℝ} (hc : ∀ i, hT.eigenvalues hn i ≤ c) {x : E}
    (hx0 : x ≠ 0) : T.rayleighQuotient x ≤ c :=
  hT.rayleighQuotient_le_of_mem_eigenvectorSpan hn (fun i _ => hc i)
    (by rw [hT.eigenvectorSpan_univ hn]; trivial) hx0

/-- If $c \le \lambda_i$ for all $i$, then $c \le r_T(x)$ for every $x \neq 0$. -/
theorem le_rayleighQuotient_of_forall {c : ℝ} (hc : ∀ i, c ≤ hT.eigenvalues hn i) {x : E}
    (hx0 : x ≠ 0) : c ≤ T.rayleighQuotient x :=
  hT.le_rayleighQuotient_of_mem_eigenvectorSpan hn (fun i _ => hc i)
    (by rw [hT.eigenvectorSpan_univ hn]; trivial) hx0

/-- Let $T$ be a symmetric operator on an inner product space of dimension $m + 1$, with eigenvalues
$\lambda_0 \ge \dots \ge \lambda_m$. Then every $x \neq 0$ satisfies
$$\lambda_m \le r_T(x) \le \lambda_0.$$
-/
theorem rayleighQuotient_mem_Icc {m : ℕ} (hn : Module.finrank 𝕜 E = m + 1) {x : E} (hx0 : x ≠ 0) :
    T.rayleighQuotient x ∈
      Set.Icc (hT.eigenvalues hn (Fin.last m)) (hT.eigenvalues hn 0) :=
  ⟨hT.le_rayleighQuotient_of_forall hn (fun i => hT.eigenvalues_antitone hn (Fin.le_last i)) hx0,
    hT.rayleighQuotient_le_of_forall hn
      (fun i => hT.eigenvalues_antitone hn (Fin.zero_le i)) hx0⟩

/-! ### The two directions of Courant–Fischer -/

/-- **Courant–Fischer, first direction.** Let $T$ be a symmetric operator on an inner product space
$E$ of dimension $n$, let $i < n$, and let $S$ be a subspace with $\dim S \ge i + 1$. Then there
is an $x \in S$ with $x \neq 0$ and $r_T(x) \le \lambda_i$.

The proof is the dimension count $(i + 1) + (n - i) > n$ against the span of
$v_i, \dots, v_{n-1}$. -/
theorem exists_mem_ne_zero_rayleighQuotient_le (i : Fin n) {S : Submodule 𝕜 E}
    (hS : (i : ℕ) + 1 ≤ Module.finrank 𝕜 S) :
    ∃ x ∈ S, x ≠ 0 ∧ T.rayleighQuotient x ≤ hT.eigenvalues hn i := by
  have hW : Module.finrank 𝕜 (hT.eigenvectorSpan hn (Finset.Ici i)) = n - (i : ℕ) := by
    rw [hT.finrank_eigenvectorSpan hn, Fin.card_Ici]
  have hlt : Module.finrank 𝕜 E <
      Module.finrank 𝕜 S + Module.finrank 𝕜 (hT.eigenvectorSpan hn (Finset.Ici i)) := by
    rw [hn, hW]; omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_inf_ne_zero hlt
  exact ⟨x, hx.1, hx0, hT.rayleighQuotient_le_of_mem_eigenvectorSpan hn
    (fun _j hj => hT.eigenvalues_antitone hn (Finset.mem_Ici.mp hj)) hx.2 hx0⟩

/-- **Courant–Fischer, first direction, dual form.** Let $T$ be a symmetric operator on an inner
product space $E$ of dimension $n$, let $i < n$, and let $S$ be a subspace with
$\dim S \ge n - i$. Then there is an $x \in S$ with $x \neq 0$ and $\lambda_i \le r_T(x)$. -/
theorem exists_mem_ne_zero_le_rayleighQuotient (i : Fin n) {S : Submodule 𝕜 E}
    (hS : n - (i : ℕ) ≤ Module.finrank 𝕜 S) :
    ∃ x ∈ S, x ≠ 0 ∧ hT.eigenvalues hn i ≤ T.rayleighQuotient x := by
  have hi := i.isLt
  have hW : Module.finrank 𝕜 (hT.eigenvectorSpan hn (Finset.Iic i)) = (i : ℕ) + 1 := by
    rw [hT.finrank_eigenvectorSpan hn, Fin.card_Iic]
  have hlt : Module.finrank 𝕜 E <
      Module.finrank 𝕜 S + Module.finrank 𝕜 (hT.eigenvectorSpan hn (Finset.Iic i)) := by
    rw [hn, hW]; omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_inf_ne_zero hlt
  exact ⟨x, hx.1, hx0, hT.le_rayleighQuotient_of_mem_eigenvectorSpan hn
    (fun _j hj => hT.eigenvalues_antitone hn (Finset.mem_Iic.mp hj)) hx.2 hx0⟩

/-- **Courant–Fischer, second direction.** Let $T$ be a symmetric operator on an inner product space
of dimension $n$, and let $i < n$. Then every nonzero $x$ in the span of $v_0, \dots, v_i$
satisfies $\lambda_i \le r_T(x)$.

This span has dimension $i + 1$, and the max–min is attained on it. -/
theorem le_rayleighQuotient_of_mem_eigenvectorSpan_Iic (i : Fin n) {x : E}
    (hx : x ∈ hT.eigenvectorSpan hn (Finset.Iic i)) (hx0 : x ≠ 0) :
    hT.eigenvalues hn i ≤ T.rayleighQuotient x :=
  hT.le_rayleighQuotient_of_mem_eigenvectorSpan hn
    (fun _j hj => hT.eigenvalues_antitone hn (Finset.mem_Iic.mp hj)) hx hx0

/-- **Courant–Fischer, second direction, dual form.** Let $T$ be a symmetric operator on an inner
product space of dimension $n$, and let $i < n$. Then every nonzero $x$ in the span of
$v_i, \dots, v_{n-1}$ satisfies $r_T(x) \le \lambda_i$.

This span has dimension $n - i$, and the min–max is attained on it. -/
theorem rayleighQuotient_le_of_mem_eigenvectorSpan_Ici (i : Fin n) {x : E}
    (hx : x ∈ hT.eigenvectorSpan hn (Finset.Ici i)) (hx0 : x ≠ 0) :
    T.rayleighQuotient x ≤ hT.eigenvalues hn i :=
  hT.rayleighQuotient_le_of_mem_eigenvectorSpan hn
    (fun _j hj => hT.eigenvalues_antitone hn (Finset.mem_Ici.mp hj)) hx hx0

/-- Let $T$ be a symmetric operator on an inner product space of dimension $n$, and let $i < n$. A
vector $x$ lies in the span of $v_i, \dots, v_{n-1}$ if and only if $\langle v_j, x \rangle = 0$
for all $j < i$.

This identifies the subspace in Rayleigh's recursive characterization with a span of
eigenvectors. -/
theorem mem_eigenvectorSpan_Ici_iff {i : Fin n} {x : E} :
    x ∈ hT.eigenvectorSpan hn (Finset.Ici i) ↔
      ∀ j < i, inner 𝕜 (hT.eigenvectorBasis hn j) x = 0 := by
  rw [hT.mem_eigenvectorSpan_iff hn]
  simp only [Finset.mem_Ici, not_le, OrthonormalBasis.repr_apply_apply]

/-! ### Courant–Fischer -/

/-- **Courant–Fischer, max–min form.** Let $T$ be a symmetric operator on an inner product space $E$
of dimension $n$, and let $i < n$. Then $\lambda_i$ is the greatest element of the set of real
numbers $c$ for which there is a subspace $S$ of dimension $i + 1$ with $c \le r_T(x)$ for all
nonzero $x \in S$.

This is the second formula of [saad2011numerical], Theorem 1.9. The statement contains no `iSup`
and hence no junk value. -/
theorem isGreatest_eigenvalues (i : Fin n) :
    IsGreatest {c : ℝ | ∃ S : Submodule 𝕜 E, Module.finrank 𝕜 S = (i : ℕ) + 1 ∧
      ∀ x ∈ S, x ≠ 0 → c ≤ T.rayleighQuotient x} (hT.eigenvalues hn i) := by
  refine ⟨⟨hT.eigenvectorSpan hn (Finset.Iic i), ?_,
    fun x hx hx0 => hT.le_rayleighQuotient_of_mem_eigenvectorSpan_Iic hn i hx hx0⟩, ?_⟩
  · rw [hT.finrank_eigenvectorSpan hn, Fin.card_Iic]
  · rintro c ⟨S, hS, hc⟩
    obtain ⟨x, hxS, hx0, hxle⟩ := hT.exists_mem_ne_zero_rayleighQuotient_le hn i hS.ge
    exact (hc x hxS hx0).trans hxle

/-- **Courant–Fischer, min–max form.** Let $T$ be a symmetric operator on an inner product space $E$
of dimension $n$, and let $i < n$. Then $\lambda_i$ is the least element of the set of real
numbers $c$ for which there is a subspace $S$ of dimension $n - i$ with $r_T(x) \le c$ for all
nonzero $x \in S$.

This is the first formula of [saad2011numerical], Theorem 1.9, and [kress1998numerical], Theorem
7.4. The statement contains no `iInf` and hence no junk value. -/
theorem isLeast_eigenvalues (i : Fin n) :
    IsLeast {c : ℝ | ∃ S : Submodule 𝕜 E, Module.finrank 𝕜 S = n - (i : ℕ) ∧
      ∀ x ∈ S, x ≠ 0 → T.rayleighQuotient x ≤ c} (hT.eigenvalues hn i) := by
  refine ⟨⟨hT.eigenvectorSpan hn (Finset.Ici i), ?_,
    fun x hx hx0 => hT.rayleighQuotient_le_of_mem_eigenvectorSpan_Ici hn i hx hx0⟩, ?_⟩
  · rw [hT.finrank_eigenvectorSpan hn, Fin.card_Ici]
  · rintro c ⟨S, hS, hc⟩
    obtain ⟨x, hxS, hx0, hxle⟩ := hT.exists_mem_ne_zero_le_rayleighQuotient hn i hS.ge
    exact hxle.trans (hc x hxS hx0)

/-- **Courant–Fischer, max–min form.** Let $T$ be a symmetric operator on an inner product space $E$
of dimension $n$, and let $i < n$. Then
$$\lambda_i = \sup_{\dim S = i + 1} \ \inf_{0 \neq x \in S} r_T(x),$$
where $S$ runs over the subspaces of $E$ of dimension $i + 1$.

This is the second formula of [saad2011numerical], Theorem 1.9. The supremum and the infimum are
attained. `LinearMap.IsSymmetric.isGreatest_eigenvalues` is the same statement without an
`iSup`. -/
theorem eigenvalues_eq_iSup_iInf (i : Fin n) :
    hT.eigenvalues hn i =
      ⨆ S : {S : Submodule 𝕜 E // Module.finrank 𝕜 S = (i : ℕ) + 1},
        ⨅ x : {x : E // x ∈ (S : Submodule 𝕜 E) ∧ x ≠ 0}, T.rayleighQuotient (x : E) := by
  have hlow : ∀ j, Finset.univ.inf' ⟨i, Finset.mem_univ i⟩ (hT.eigenvalues hn) ≤
      hT.eigenvalues hn j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  have hbdd : ∀ S : Submodule 𝕜 E, BddBelow
      (Set.range fun x : {x : E // x ∈ S ∧ x ≠ 0} => T.rayleighQuotient (x : E)) := by
    refine fun S => ⟨Finset.univ.inf' ⟨i, Finset.mem_univ i⟩ (hT.eigenvalues hn), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hT.le_rayleighQuotient_of_forall hn hlow x.2.2
  have hcard : Module.finrank 𝕜 (hT.eigenvectorSpan hn (Finset.Iic i)) = (i : ℕ) + 1 := by
    rw [hT.finrank_eigenvectorSpan hn, Fin.card_Iic]
  have hmem : hT.eigenvectorBasis hn i ∈ hT.eigenvectorSpan hn (Finset.Iic i) :=
    hT.eigenvectorBasis_mem_eigenvectorSpan hn (Finset.mem_Iic.mpr le_rfl)
  have hattain : ⨅ x : {x : E // x ∈ hT.eigenvectorSpan hn (Finset.Iic i) ∧ x ≠ 0},
      T.rayleighQuotient (x : E) = hT.eigenvalues hn i := by
    have : Nonempty {x : E // x ∈ hT.eigenvectorSpan hn (Finset.Iic i) ∧ x ≠ 0} :=
      ⟨⟨_, hmem, hT.eigenvectorBasis_ne_zero hn i⟩⟩
    refine le_antisymm ?_ (le_ciInf fun x =>
      hT.le_rayleighQuotient_of_mem_eigenvectorSpan_Iic hn i x.2.1 x.2.2)
    simpa using ciInf_le (hbdd _) ⟨_, hmem, hT.eigenvectorBasis_ne_zero hn i⟩
  refine (IsGreatest.csSup_eq (s := Set.range
    fun S : {S : Submodule 𝕜 E // Module.finrank 𝕜 S = (i : ℕ) + 1} =>
      ⨅ x : {x : E // x ∈ (S : Submodule 𝕜 E) ∧ x ≠ 0}, T.rayleighQuotient (x : E))
    ⟨⟨⟨_, hcard⟩, hattain⟩, ?_⟩).symm
  rintro _ ⟨S, rfl⟩
  obtain ⟨x, hxS, hx0, hxle⟩ := hT.exists_mem_ne_zero_rayleighQuotient_le hn i S.2.ge
  exact (ciInf_le (hbdd _) ⟨x, hxS, hx0⟩).trans hxle

/-- **Courant–Fischer, min–max form.** Let $T$ be a symmetric operator on an inner product space $E$
of dimension $n$, and let $i < n$. Then
$$\lambda_i = \inf_{\dim S = n - i} \ \sup_{0 \neq x \in S} r_T(x),$$
where $S$ runs over the subspaces of $E$ of dimension $n - i$, that is, of codimension $i$.

This is the first formula of [saad2011numerical], Theorem 1.9, and [kress1998numerical], Theorem
7.4. The infimum and the supremum are attained. `LinearMap.IsSymmetric.isLeast_eigenvalues` is
the same statement without an `iInf`. -/
theorem eigenvalues_eq_iInf_iSup (i : Fin n) :
    hT.eigenvalues hn i =
      ⨅ S : {S : Submodule 𝕜 E // Module.finrank 𝕜 S = n - (i : ℕ)},
        ⨆ x : {x : E // x ∈ (S : Submodule 𝕜 E) ∧ x ≠ 0}, T.rayleighQuotient (x : E) := by
  have hupp : ∀ j, hT.eigenvalues hn j ≤
      Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (hT.eigenvalues hn) :=
    fun j => Finset.le_sup' _ (Finset.mem_univ j)
  have hbdd : ∀ S : Submodule 𝕜 E, BddAbove
      (Set.range fun x : {x : E // x ∈ S ∧ x ≠ 0} => T.rayleighQuotient (x : E)) := by
    refine fun S => ⟨Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ (hT.eigenvalues hn), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hT.rayleighQuotient_le_of_forall hn hupp x.2.2
  have hcard : Module.finrank 𝕜 (hT.eigenvectorSpan hn (Finset.Ici i)) = n - (i : ℕ) := by
    rw [hT.finrank_eigenvectorSpan hn, Fin.card_Ici]
  have hmem : hT.eigenvectorBasis hn i ∈ hT.eigenvectorSpan hn (Finset.Ici i) :=
    hT.eigenvectorBasis_mem_eigenvectorSpan hn (Finset.mem_Ici.mpr le_rfl)
  have hattain : ⨆ x : {x : E // x ∈ hT.eigenvectorSpan hn (Finset.Ici i) ∧ x ≠ 0},
      T.rayleighQuotient (x : E) = hT.eigenvalues hn i := by
    have : Nonempty {x : E // x ∈ hT.eigenvectorSpan hn (Finset.Ici i) ∧ x ≠ 0} :=
      ⟨⟨_, hmem, hT.eigenvectorBasis_ne_zero hn i⟩⟩
    refine le_antisymm (ciSup_le fun x =>
      hT.rayleighQuotient_le_of_mem_eigenvectorSpan_Ici hn i x.2.1 x.2.2) ?_
    simpa using le_ciSup (hbdd _) ⟨_, hmem, hT.eigenvectorBasis_ne_zero hn i⟩
  refine (IsLeast.csInf_eq (s := Set.range
    fun S : {S : Submodule 𝕜 E // Module.finrank 𝕜 S = n - (i : ℕ)} =>
      ⨆ x : {x : E // x ∈ (S : Submodule 𝕜 E) ∧ x ≠ 0}, T.rayleighQuotient (x : E))
    ⟨⟨⟨_, hcard⟩, hattain⟩, ?_⟩).symm
  rintro _ ⟨S, rfl⟩
  obtain ⟨x, hxS, hx0, hxle⟩ := hT.exists_mem_ne_zero_le_rayleighQuotient hn i S.2.ge
  exact hxle.trans (le_ciSup (hbdd _) ⟨x, hxS, hx0⟩)

/-- **Rayleigh's recursive characterization.** Let $T$ be a symmetric operator on an inner product
space of dimension $n$, and let $i < n$. Then $\lambda_i$ is the greatest element of the set
$$\{ r_T(x) : x \neq 0,\ \langle v_j, x \rangle = 0 \text{ for all } j < i \}.$$

This is [saad2011numerical], Theorem 1.10, and [kress1998numerical], Theorem 7.3. The maximum is
attained at $v_i$. For $i = 0$ the orthogonality condition is empty, and $\lambda_0$ is the
global maximum of $r_T$. Unlike the min–max form, this form needs the eigenvectors for the
larger eigenvalues, so the min–max form is the one used for a priori bounds. -/
theorem isGreatest_rayleighQuotient_orthogonal (i : Fin n) :
    IsGreatest {c : ℝ | ∃ x : E, x ≠ 0 ∧
      (∀ j < i, inner 𝕜 (hT.eigenvectorBasis hn j) x = 0) ∧ T.rayleighQuotient x = c}
      (hT.eigenvalues hn i) := by
  constructor
  · exact ⟨hT.eigenvectorBasis hn i, hT.eigenvectorBasis_ne_zero hn i,
      fun _j hj => (hT.eigenvectorBasis hn).inner_eq_zero hj.ne,
      hT.rayleighQuotient_eigenvectorBasis hn i⟩
  · rintro c ⟨x, hx0, hxorth, rfl⟩
    exact hT.rayleighQuotient_le_of_mem_eigenvectorSpan_Ici hn i
      ((hT.mem_eigenvectorSpan_Ici_iff hn).mpr hxorth) hx0

/-- The sorted eigenvalues do not depend on the proof of $\dim E = n$, up to the cast of the index.
-/
theorem eigenvalues_eq_cast (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    hT.eigenvalues hn i = hT.eigenvalues rfl (Fin.cast hn.symm i) := by
  subst hn; rfl

end LinearMap.IsSymmetric

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ} {A B : E →ₗ[𝕜] E}

/-- **Monotonicity of the eigenvalues, with slack.** Let $A$ and $B$ be symmetric operators on an
inner product space of dimension $n$, and let $C \in \mathbb{R}$. If
$$\operatorname{Re} \langle Ax, x \rangle \le \operatorname{Re} \langle Bx, x \rangle + C
  \|x\|^2 \quad \text{for all } x,$$
then $\lambda_i(A) \le \lambda_i(B) + C$ for every $i < n$.

This hypothesis on the quadratic forms is what the proof of Weyl's inequality in
[kress1998numerical], Corollary 7.5, uses. -/
theorem eigenvalues_le_add_of_re_inner_le (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) {C : ℝ}
    (h : ∀ x : E, RCLike.re (inner 𝕜 (A x) x) ≤ RCLike.re (inner 𝕜 (B x) x) + C * ‖x‖ ^ 2)
    (i : Fin n) : hA.eigenvalues hn i ≤ hB.eigenvalues hn i + C := by
  have hcard : Module.finrank 𝕜 (hA.eigenvectorSpan hn (Finset.Iic i)) = (i : ℕ) + 1 := by
    rw [hA.finrank_eigenvectorSpan hn, Fin.card_Iic]
  obtain ⟨x, hxS, hx0, hxle⟩ := hB.exists_mem_ne_zero_rayleighQuotient_le hn i hcard.ge
  have hlb := hA.le_rayleighQuotient_of_mem_eigenvectorSpan_Iic hn i hxS hx0
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
  have key : A.rayleighQuotient x ≤ B.rayleighQuotient x + C := by
    rw [LinearMap.rayleighQuotient, div_le_iff₀ hpos, add_mul, LinearMap.rayleighQuotient,
      div_mul_cancel₀ _ hpos.ne']
    exact h x
  linarith

/-- **Monotonicity of the eigenvalues.** Let $A$ and $B$ be symmetric operators on an inner product
space of dimension $n$. If $\operatorname{Re} \langle Ax, x \rangle \le \operatorname{Re}
\langle Bx, x \rangle$ for all $x$, then $\lambda_i(A) \le \lambda_i(B)$ for every $i < n$. -/
theorem eigenvalues_le_of_re_inner_le (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n)
    (h : ∀ x : E, RCLike.re (inner 𝕜 (A x) x) ≤ RCLike.re (inner 𝕜 (B x) x)) (i : Fin n) :
    hA.eigenvalues hn i ≤ hB.eigenvalues hn i := by
  simpa using hA.eigenvalues_le_add_of_re_inner_le hB hn (C := 0) (by simpa using h) i

/-- Let $A$ and $B$ be symmetric and assume $\|(A - B) x\| \le C \|x\|$ for all $x$. Then
$\lambda_i(A) - \lambda_i(B) \le C$ for every $i$.

This is one half of Weyl's inequality; the proof bounds the quadratic form of $A - B$ by the
Cauchy–Schwarz inequality. -/
theorem eigenvalues_sub_le (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) {C : ℝ} (hC : ∀ x : E, ‖(A - B) x‖ ≤ C * ‖x‖) (i : Fin n) :
    hA.eigenvalues hn i - hB.eigenvalues hn i ≤ C := by
  refine sub_le_iff_le_add'.mpr (hA.eigenvalues_le_add_of_re_inner_le hB hn (fun x => ?_) i)
  have h1 : RCLike.re (inner 𝕜 ((A - B) x) x) ≤ ‖(A - B) x‖ * ‖x‖ := re_inner_le_norm _ _
  have h2 : ‖(A - B) x‖ * ‖x‖ ≤ C * ‖x‖ * ‖x‖ :=
    mul_le_mul_of_nonneg_right (hC x) (norm_nonneg x)
  rw [LinearMap.sub_apply, inner_sub_left, map_sub] at h1
  rw [LinearMap.sub_apply] at h2
  linarith

/-- **Weyl's inequality.** Let $A$ and $B$ be symmetric operators on an inner product space of
dimension $n$, and let $C \in \mathbb{R}$ with $\|(A - B) x\| \le C \|x\|$ for all $x$. Then for
every $i < n$
$$|\lambda_i(A) - \lambda_i(B)| \le C.$$

This is [kress1998numerical], Corollary 7.5. -/
theorem abs_eigenvalues_sub_le (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) {C : ℝ} (hC : ∀ x : E, ‖(A - B) x‖ ≤ C * ‖x‖) (i : Fin n) :
    |hA.eigenvalues hn i - hB.eigenvalues hn i| ≤ C := by
  refine abs_sub_le_iff.mpr ⟨hA.eigenvalues_sub_le hB hn hC i,
    hB.eigenvalues_sub_le hA hn (fun x => ?_) i⟩
  have hx := hC x
  rwa [show (B - A) x = -((A - B) x) by simp, norm_neg]

/-- **Weyl's inequality, operator-norm form.** Let $A$ and $B$ be continuous linear operators on an
inner product space of dimension $n$ that are symmetric. Then for every $i < n$
$$|\lambda_i(A) - \lambda_i(B)| \le \|A - B\|,$$
with the operator norm on the right. -/
theorem abs_eigenvalues_sub_le_opNorm {A B : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    |hA.eigenvalues hn i - hB.eigenvalues hn i| ≤ ‖A - B‖ := by
  refine hA.abs_eigenvalues_sub_le hB hn (fun x => ?_) i
  rw [← ContinuousLinearMap.toLinearMap_sub]
  exact (A - B).le_opNorm x

/-- **Weyl's inequality, two-sided form.** Let $A$ and $B$ be symmetric operators on an inner
product space of dimension $m + 1$, and assume that $A + B$ is symmetric. Then for every
$i \le m$
$$\lambda_i(A) + \lambda_m(B) \le \lambda_i(A + B) \le \lambda_i(A) + \lambda_0(B).$$

This is [golub2013matrix], Theorem 8.1.5, where the perturbation is called $E$ and the bounds
are $\lambda_i(A) + \lambda_{\min}(E) \le \lambda_i(A + E) \le \lambda_i(A) +
\lambda_{\max}(E)$. Both bounds are `LinearMap.IsSymmetric.eigenvalues_le_add_of_re_inner_le`,
with the bounds $\lambda_m(B) \|x\|^2 \le \operatorname{Re} \langle Bx, x \rangle \le
\lambda_0(B) \|x\|^2$ as the slack. The hypothesis that $A + B$ is symmetric follows from the
other two, and is there to name the eigenvalues of $A + B$. -/
theorem eigenvalues_add_mem_Icc {m : ℕ} (hA : A.IsSymmetric) (hE : B.IsSymmetric)
    (hAE : (A + B).IsSymmetric) (hn : Module.finrank 𝕜 E = m + 1) (i : Fin (m + 1)) :
    hAE.eigenvalues hn i ∈ Set.Icc (hA.eigenvalues hn i + hE.eigenvalues hn (Fin.last m))
      (hA.eigenvalues hn i + hE.eigenvalues hn 0) := by
  have huniv : ∀ x : E, x ∈ hE.eigenvectorSpan hn Finset.univ := fun x => by
    rw [hE.eigenvectorSpan_univ hn]; trivial
  have hup : ∀ x : E, RCLike.re (inner 𝕜 (B x) x) ≤ hE.eigenvalues hn 0 * ‖x‖ ^ 2 := fun x =>
    hE.re_inner_apply_self_le_of_mem_eigenvectorSpan hn
      (fun j _ => hE.eigenvalues_antitone hn (Fin.zero_le j)) (huniv x)
  have hlo : ∀ x : E, hE.eigenvalues hn (Fin.last m) * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (B x) x) :=
    fun x => hE.le_re_inner_apply_self_of_mem_eigenvectorSpan hn
      (fun j _ => hE.eigenvalues_antitone hn (Fin.le_last j)) (huniv x)
  constructor
  · have h := hA.eigenvalues_le_add_of_re_inner_le hAE hn
      (C := -hE.eigenvalues hn (Fin.last m)) (fun x => by
        rw [LinearMap.add_apply, inner_add_left, map_add]; linarith [hlo x]) i
    linarith
  · have h := hAE.eigenvalues_le_add_of_re_inner_le hA hn (C := hE.eigenvalues hn 0)
      (fun x => by rw [LinearMap.add_apply, inner_add_left, map_add]; linarith [hup x]) i
    linarith

end LinearMap.IsSymmetric

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ} {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n)
include hT

/-! ### Cauchy interlacing -/

/-- **Cauchy interlacing along a linear isometry.** Let $T$ be a symmetric operator on an inner
product space $E$ of dimension $n$, and let $S$ be a symmetric operator on an inner product
space $F$ of dimension $m \le n$. Let $\iota \colon F \to E$ be a linear isometry with
$$\operatorname{Re} \langle Sy, y \rangle = \operatorname{Re} \langle T \iota y, \iota y \rangle
  \quad \text{for all } y \in F.$$
Then for every $i < m$
$$\lambda_{i + (n - m)}(T) \le \lambda_i(S) \le \lambda_i(T).$$

Both inequalities are Courant–Fischer. Through $\iota$, the subspaces of $F$ are among the
subspaces of $E$ of the same dimension, so every candidate subspace in the max–min or the
min–max formula for $S$ is one for $T$. -/
theorem eigenvalues_interlace_of_linearIsometry {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] {S : F →ₗ[𝕜] F} (hS : S.IsSymmetric)
    {m : ℕ} (hm : Module.finrank 𝕜 F = m) (hmn : m ≤ n) (ι : F →ₗᵢ[𝕜] E)
    (hSι : ∀ y, RCLike.re (inner 𝕜 (S y) y) = RCLike.re (inner 𝕜 (T (ι y)) (ι y))) (i : Fin m) :
    hT.eigenvalues hn ⟨(i : ℕ) + (n - m), by omega⟩ ≤ hS.eigenvalues hm i ∧
      hS.eigenvalues hm i ≤ hT.eigenvalues hn (Fin.castLE hmn i) := by
  have hRQ : ∀ y, S.rayleighQuotient y = T.rayleighQuotient (ι y) := fun y => by
    rw [LinearMap.rayleighQuotient, LinearMap.rayleighQuotient, hSι, ι.norm_map]
  have hinj : Function.Injective ι.toLinearMap := ι.injective
  have hi := i.isLt
  constructor
  · obtain ⟨⟨S', hS', hb⟩, -⟩ := hS.isLeast_eigenvalues hm i
    refine (hT.isLeast_eigenvalues hn ⟨(i : ℕ) + (n - m), by omega⟩).2
      ⟨S'.map ι.toLinearMap, ?_, ?_⟩
    · rw [LinearMap.finrank_map_of_injective _ hinj, hS']
      simp only
      omega
    · rintro _ ⟨y, hy, rfl⟩ hx0
      rw [LinearIsometry.coe_toLinearMap, ← hRQ]
      exact hb y hy fun h => hx0 (by simp [h])
  · obtain ⟨⟨S', hS', hb⟩, -⟩ := hS.isGreatest_eigenvalues hm i
    refine (hT.isGreatest_eigenvalues hn (Fin.castLE hmn i)).2 ⟨S'.map ι.toLinearMap, ?_, ?_⟩
    · rw [LinearMap.finrank_map_of_injective _ hinj, hS']
      rfl
    · rintro _ ⟨y, hy, rfl⟩ hx0
      rw [LinearIsometry.coe_toLinearMap, ← hRQ]
      exact hb y hy fun h => hx0 (by simp [h])

/-- **Cauchy interlacing for a subspace.** Let $T$ be a symmetric operator on an inner product space
$E$ of dimension $n$, let $K$ be a subspace of dimension $m \le n$, and let $S \colon K \to K$
be symmetric with $\operatorname{Re} \langle Sy, y \rangle = \operatorname{Re} \langle Ty, y
\rangle$ for all $y \in K$. Then for every $i < m$
$$\lambda_{i + (n - m)}(T) \le \lambda_i(S) \le \lambda_i(T).$$

This is [saad2011numerical], Theorem 1.10, Theorem 8.1.7 of the 1989 edition of Golub and Van
Loan, *Matrix Computations*, and the weak half of [quarteroni2000numerical], Property 5.11. When
$S$ is the compression of $T$ to $K$, the upper inequality is
`LinearMap.IsSymmetric.eigenvalues_compression_le` of `Numlib.Eigen.RayleighRitz`. With the
hypothesis on the quadratic forms, the result applies both to the compression
(`Krylov.rayleighQuotient_compression`) and to a principal submatrix. -/
theorem eigenvalues_restrict_interlace {K : Submodule 𝕜 E} {S : K →ₗ[𝕜] K} (hS : S.IsSymmetric)
    {m : ℕ} (hm : Module.finrank 𝕜 K = m) (hmn : m ≤ n)
    (hSK : ∀ y : K, RCLike.re (inner 𝕜 (S y) y) = RCLike.re (inner 𝕜 (T y) (y : E))) (i : Fin m) :
    hT.eigenvalues hn ⟨(i : ℕ) + (n - m), by omega⟩ ≤ hS.eigenvalues hm i ∧
      hS.eigenvalues hm i ≤ hT.eigenvalues hn (Fin.castLE hmn i) :=
  hT.eigenvalues_interlace_of_linearIsometry hn hS hm hmn K.subtypeₗᵢ hSK i

end LinearMap.IsSymmetric

/-! ### Low-rank interlacing -/

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ} {A B : E →ₗ[𝕜] E}

/-- **Low-rank interlacing.** Let $A$ and $B$ be symmetric operators on an inner product space of
dimension $n$ with $\dim \operatorname{range}(B - A) \le r$. Then for every $i$ with $i + r < n$
$$\lambda_{i + r}(B) \le \lambda_i(A).$$

So a perturbation of rank at most $r$ moves every eigenvalue by at most $r$ places. Since
$B - A$ and $A - B$ have the same range, the same holds with $A$ and $B$ exchanged. The proof is
Courant–Fischer. On the span of $v_0(B), \dots, v_{i+r}(B)$, of dimension $i + r + 1$, the
Rayleigh quotient of $B$ is at least $\lambda_{i+r}(B)$. Its intersection with $\ker(B - A)$ has
dimension at least $i + 1$, so it contains a nonzero vector whose Rayleigh quotient for $A$,
which equals the one for $B$ there, is at most $\lambda_i(A)$. -/
theorem eigenvalues_le_of_finrank_range_sub_le (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) {r : ℕ} (hr : Module.finrank 𝕜 (LinearMap.range (B - A)) ≤ r)
    (i : Fin n) (hir : (i : ℕ) + r < n) :
    hB.eigenvalues hn ⟨(i : ℕ) + r, hir⟩ ≤ hA.eigenvalues hn i := by
  set S := hB.eigenvectorSpan hn (Finset.Iic ⟨(i : ℕ) + r, hir⟩)
  have hS : Module.finrank 𝕜 S = (i : ℕ) + r + 1 := by
    rw [hB.finrank_eigenvectorSpan hn, Fin.card_Iic]
  have hK : n - r ≤ Module.finrank 𝕜 (LinearMap.ker (B - A)) := by
    have := LinearMap.finrank_range_add_finrank_ker (B - A)
    omega
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq S (LinearMap.ker (B - A))
  have hle : Module.finrank 𝕜 (S ⊔ LinearMap.ker (B - A) : Submodule 𝕜 E) ≤ n :=
    hn ▸ Submodule.finrank_le _
  obtain ⟨x, hxW, hx0, hxle⟩ := hA.exists_mem_ne_zero_rayleighQuotient_le hn i
    (S := S ⊓ LinearMap.ker (B - A)) (by omega)
  have hBx : B x = A x := by
    have := (Submodule.mem_inf.mp hxW).2
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  have hlb := hB.le_rayleighQuotient_of_mem_eigenvectorSpan_Iic hn ⟨(i : ℕ) + r, hir⟩
    (Submodule.mem_inf.mp hxW).1 hx0
  rw [LinearMap.rayleighQuotient, hBx] at hlb
  exact hlb.trans hxle

/-- **Interlacing for a positive low-rank perturbation.** Let $A$ and $B$ be symmetric operators on
an inner product space of dimension $n$ such that $B - A$ is positive and
$\dim \operatorname{range}(B - A) \le r$. Then for every $i$ with $i + r < n$
$$\lambda_{i + r}(B) \le \lambda_i(A) \le \lambda_i(B).$$

[golub2013matrix], Theorem 8.1.8, is the case $r = 1$, $B - A = \tau c c^T$ with $\tau \ge 0$.
The first inequality is `LinearMap.IsSymmetric.eigenvalues_le_of_finrank_range_sub_le`, which
needs no positivity. The second is the monotonicity
`LinearMap.IsSymmetric.eigenvalues_le_of_re_inner_le`. -/
theorem eigenvalues_le_of_isPositive_sub_of_finrank_range_le (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (hBA : (B - A).IsPositive) {r : ℕ}
    (hr : Module.finrank 𝕜 (LinearMap.range (B - A)) ≤ r) (i : Fin n) (hir : (i : ℕ) + r < n) :
    hB.eigenvalues hn ⟨(i : ℕ) + r, hir⟩ ≤ hA.eigenvalues hn i ∧
      hA.eigenvalues hn i ≤ hB.eigenvalues hn i :=
  ⟨hA.eigenvalues_le_of_finrank_range_sub_le hB hn hr i hir,
    hA.eigenvalues_le_of_re_inner_le hB hn (fun x => by
      have := hBA.2 x
      rw [LinearMap.sub_apply, inner_sub_left, map_sub] at this
      linarith) i⟩

end LinearMap.IsSymmetric

/-! ### Ky Fan's principles and the Hoffman–Wielandt inequality -/

/-- Let $E$ be finite-dimensional, let $T \colon E \to E$ be linear, and let $(x_i)_{i < k}$ be
orthonormal. Then $\sum_i \operatorname{Re} \langle T x_i, x_i \rangle$ is the real part of the
trace of the compression of $T$ to the span of the $x_i$.

The family is an orthonormal basis of its span, and in this basis the diagonal entries of the
compression are $\langle x_i, T x_i \rangle$. -/
theorem LinearMap.sum_re_inner_eq_re_trace_compression [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E)
    {k : ℕ} {x : Fin k → E} (hx : Orthonormal 𝕜 x) :
    ∑ i, RCLike.re (inner 𝕜 (T (x i)) (x i)) =
      RCLike.re (LinearMap.trace 𝕜 _ (compression T (Submodule.span 𝕜 (Set.range x)))) := by
  set K := Submodule.span 𝕜 (Set.range x)
  let b : OrthonormalBasis (Fin k) 𝕜 K :=
    (Module.Basis.span hx.linearIndependent).toOrthonormalBasis
      (K.subtypeₗᵢ.orthonormal_comp_iff.mp (by convert hx; ext; simp))
  have hb : ∀ i, (b i : E) = x i := fun i => by simp [b]
  rw [LinearMap.trace_eq_sum_inner _ b, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [compression.inner_apply', hb, ← inner_conj_symm, RCLike.conj_re]

/-- Summation by parts: if every partial sum of $d$ is nonnegative and $f$ decreases, then
$f_{\text{last}} \sum_i d_i \le \sum_i f_i d_i$. -/
private theorem mul_sum_le_sum_mul_of_antitone {n : ℕ} {f d : Fin (n + 1) → ℝ} (hf : Antitone f)
    (hd : ∀ (k : ℕ) (hk : k ≤ n + 1), 0 ≤ ∑ i : Fin k, d (Fin.castLE hk i)) :
    f (Fin.last n) * ∑ i, d i ≤ ∑ i, f i * d i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (f := f ∘ Fin.castSucc) (d := d ∘ Fin.castSucc)
      (fun i j hij => hf (Fin.castSucc_le_castSucc_iff.mpr hij))
      (fun k hk => hd k (by omega))
    have h0 : 0 ≤ ∑ i : Fin (n + 1), d (Fin.castSucc i) := hd (n + 1) (by omega)
    have hfl : f (Fin.last (n + 1)) ≤ f (Fin.castSucc (Fin.last n)) := hf (Fin.le_last _)
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc (fun i => f i * d i), mul_add]
    simp only [Function.comp] at ih'
    nlinarith

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ} (hn : Module.finrank 𝕜 E = n)

section KyFan

variable {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
include hT

/-- **Ky Fan's maximum principle.** Let $T$ be a symmetric operator on an inner product space of
dimension $n$, let $k \le n$, and let $(x_i)_{i < k}$ be an orthonormal family. Then
$$\sum_{i < k} \operatorname{Re} \langle T x_i, x_i \rangle \le \sum_{i < k} \lambda_i,$$
the sum of the $k$ largest eigenvalues.

Equality holds at the leading eigenvectors
(`LinearMap.IsSymmetric.sum_re_inner_eigenvectorBasis`). The sum on the left is the real trace
of the compression of $T$ to the span of the family
(`LinearMap.sum_re_inner_eq_re_trace_compression`), that is, the sum of the eigenvalues of the
compression. By Cauchy interlacing, each of these is at most the corresponding eigenvalue of
$T$. -/
theorem sum_re_inner_le_sum_eigenvalues {k : ℕ} {x : Fin k → E} (hx : Orthonormal 𝕜 x)
    (hkn : k ≤ n) :
    ∑ i, RCLike.re (inner 𝕜 (T (x i)) (x i)) ≤
      ∑ i : Fin k, hT.eigenvalues hn (Fin.castLE hkn i) := by
  have hK : Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range x)) = k := by
    rw [finrank_span_eq_card hx.linearIndependent, Fintype.card_fin]
  have hS := compression.isSymmetric T (Submodule.span 𝕜 (Set.range x)) hT
  rw [T.sum_re_inner_eq_re_trace_compression hx, hS.re_trace_eq_sum_eigenvalues hK]
  exact Finset.sum_le_sum fun i _ =>
    (hT.eigenvalues_restrict_interlace hn hS hK hkn
      (fun y => by rw [compression.inner_apply]) i).2

/-- **Ky Fan's minimum principle.** Let $T$ be a symmetric operator on an inner product space of
dimension $n$, let $k \le n$, and let $(x_i)_{i < k}$ be an orthonormal family. Then
$$\sum_{i < k} \lambda_{i + (n - k)}
  \le \sum_{i < k} \operatorname{Re} \langle T x_i, x_i \rangle,$$
where the left side is the sum of the $k$ smallest eigenvalues.

This is the trace-minimization principle of [golub2013matrix], §10.6.5, for $B = I$. The proof
is the compression argument of `LinearMap.IsSymmetric.sum_re_inner_le_sum_eigenvalues`, with the
other half of Cauchy interlacing. -/
theorem sum_eigenvalues_le_sum_re_inner {k : ℕ} {x : Fin k → E} (hx : Orthonormal 𝕜 x)
    (hkn : k ≤ n) :
    ∑ i : Fin k, hT.eigenvalues hn ⟨(i : ℕ) + (n - k), by omega⟩ ≤
      ∑ i, RCLike.re (inner 𝕜 (T (x i)) (x i)) := by
  have hK : Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range x)) = k := by
    rw [finrank_span_eq_card hx.linearIndependent, Fintype.card_fin]
  have hS := compression.isSymmetric T (Submodule.span 𝕜 (Set.range x)) hT
  rw [T.sum_re_inner_eq_re_trace_compression hx, hS.re_trace_eq_sum_eigenvalues hK]
  exact Finset.sum_le_sum fun i _ =>
    (hT.eigenvalues_restrict_interlace hn hS hK hkn
      (fun y => by rw [compression.inner_apply]) i).1

/-- The equality case of Ky Fan's maximum principle: for $k \le n$, $\sum_{i < k} \operatorname{Re}
\langle T v_i, v_i \rangle = \sum_{i < k} \lambda_i$. -/
theorem sum_re_inner_eigenvectorBasis {k : ℕ} (hkn : k ≤ n) :
    ∑ i : Fin k, RCLike.re (inner 𝕜 (T (hT.eigenvectorBasis hn (Fin.castLE hkn i)))
        (hT.eigenvectorBasis hn (Fin.castLE hkn i))) =
      ∑ i : Fin k, hT.eigenvalues hn (Fin.castLE hkn i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← T.rayleighQuotient_of_norm_eq_one ((hT.eigenvectorBasis hn).norm_eq_one _),
    hT.rayleighQuotient_eigenvectorBasis]

/-- The trace of the square of a symmetric operator is the sum of the squares of its eigenvalues:
$\operatorname{tr}(T^2) = \sum_i \lambda_i^2$. -/
theorem trace_comp_self_eq_sum_sq :
    LinearMap.trace 𝕜 E (T ∘ₗ T) = ∑ i, ((hT.eigenvalues hn i : 𝕜)) ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner _ (hT.eigenvectorBasis hn)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, hT.apply_eigenvectorBasis, map_smul, hT.apply_eigenvectorBasis,
    smul_smul, inner_smul_right, inner_self_eq_norm_sq_to_K,
    (hT.eigenvectorBasis hn).norm_eq_one]
  simp [sq]

end KyFan

variable {A B : E →ₗ[𝕜] E}

/-- **The trace inequality for two symmetric operators.** Let $A$ and $B$ be symmetric operators on
an inner product space of dimension $n$. Then
$$\operatorname{Re} \operatorname{tr}(AB) \le \sum_{i < n} \lambda_i(A) \lambda_i(B),$$
with both lists of eigenvalues in decreasing order.

This is the symmetric case of von Neumann's trace inequality. In the eigenbasis $(v_i)$ of $B$
with eigenvalues $\mu_i$, $\operatorname{Re} \operatorname{tr}(AB) = \sum_i \mu_i a_i$ with
$a_i = \operatorname{Re} \langle A v_i, v_i \rangle$. The partial sums of $a$ are bounded by
those of $\lambda(A)$ by Ky Fan's principle
(`LinearMap.IsSymmetric.sum_re_inner_le_sum_eigenvalues`), with equality for the full sum, which
is the trace. Summation by parts against the decreasing $\mu$ gives the claim. -/
theorem re_trace_comp_le_sum_eigenvalues_mul (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    RCLike.re (LinearMap.trace 𝕜 E (A ∘ₗ B)) ≤
      ∑ i, hA.eigenvalues hn i * hB.eigenvalues hn i := by
  set v := hB.eigenvectorBasis hn
  set a : Fin n → ℝ := fun i => RCLike.re (inner 𝕜 (A (v i)) (v i))
  have htr : RCLike.re (LinearMap.trace 𝕜 E (A ∘ₗ B)) = ∑ i, hB.eigenvalues hn i * a i := by
    rw [LinearMap.trace_eq_sum_inner _ v, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.comp_apply, hB.apply_eigenvectorBasis, map_smul, inner_smul_right,
      ← hA, RCLike.re_ofReal_mul]
  have hsum : ∑ i, a i = ∑ i, hA.eigenvalues hn i := by
    rw [← hA.re_trace_eq_sum_eigenvalues hn, LinearMap.trace_eq_sum_inner _ v, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hA]
  rw [htr]
  obtain _ | m := n
  · simp
  have key := mul_sum_le_sum_mul_of_antitone (f := hB.eigenvalues hn)
    (d := fun i => hA.eigenvalues hn i - a i) (hB.eigenvalues_antitone hn) (fun k hk => by
      rw [Finset.sum_sub_distrib, sub_nonneg]
      exact hA.sum_re_inner_le_sum_eigenvalues hn
        (v.orthonormal.comp _ (Fin.castLE_injective hk)) hk)
  rw [Finset.sum_sub_distrib, hsum, sub_self, mul_zero] at key
  have : ∑ i, hB.eigenvalues hn i * (hA.eigenvalues hn i - a i) =
      ∑ i, hA.eigenvalues hn i * hB.eigenvalues hn i - ∑ i, hB.eigenvalues hn i * a i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- **The Hoffman–Wielandt inequality, operator form.** Let $A$ and $B$ be symmetric operators on an
inner product space of dimension $n$. Then, with both lists of eigenvalues in decreasing order,
$$\sum_{i < n} (\lambda_i(A) - \lambda_i(B))^2
  \le \operatorname{Re} \operatorname{tr}\bigl((A - B)^2\bigr).$$

The right side is the square of the Hilbert–Schmidt norm of $A - B$. The proof expands the
square: $\operatorname{tr} A^2 = \sum_i \lambda_i(A)^2$,
$\operatorname{tr} B^2 = \sum_i \lambda_i(B)^2$, and the cross term is bounded by the trace
inequality `LinearMap.IsSymmetric.re_trace_comp_le_sum_eigenvalues_mul`. -/
theorem sum_sq_eigenvalues_sub_le (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    ∑ i, (hA.eigenvalues hn i - hB.eigenvalues hn i) ^ 2 ≤
      RCLike.re (LinearMap.trace 𝕜 E ((A - B) ∘ₗ (A - B))) := by
  have hexp : (A - B) ∘ₗ (A - B) = A ∘ₗ A - A ∘ₗ B - B ∘ₗ A + B ∘ₗ B := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.comp_sub]; abel
  have hAA := congrArg RCLike.re (hA.trace_comp_self_eq_sum_sq hn)
  have hBB := congrArg RCLike.re (hB.trace_comp_self_eq_sum_sq hn)
  have hAB := re_trace_comp_le_sum_eigenvalues_mul hn hA hB
  have hBA : LinearMap.trace 𝕜 E (B ∘ₗ A) = LinearMap.trace 𝕜 E (A ∘ₗ B) :=
    (LinearMap.trace_comp_comm' B A).symm
  simp only [map_sum, ← RCLike.ofReal_pow, RCLike.ofReal_re] at hAA hBB
  rw [hexp, map_add, map_sub, map_sub, hBA, map_add, map_sub, map_sub, hAA, hBB]
  have : ∑ i, (hA.eigenvalues hn i - hB.eigenvalues hn i) ^ 2 =
      ∑ i, hA.eigenvalues hn i ^ 2 - 2 * ∑ i, hA.eigenvalues hn i * hB.eigenvalues hn i +
        ∑ i, hB.eigenvalues hn i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

end LinearMap.IsSymmetric

/-!
### Negation

Every statement about a largest eigenvalue is a statement about a smallest eigenvalue of $-T$, and
this section gives the translation: `LinearMap.IsSymmetric.eigenvalues_neg` for the eigenvalues,
`LinearMap.IsSymmetric.exists_smul_eigenvectorBasis_neg` for the eigenvectors at a simple
eigenvalue, and two congruence lemmas that let a rewrite happen inside the dependent types
`hT.eigenvalues hn` and `(compression.isSymmetric T K hT).eigenvalues hK`.
-/

namespace LinearMap.IsSymmetric

variable [FiniteDimensional 𝕜 E] {n : ℕ}

/-- The sorted eigenvalues depend only on the operator, and not on the proof that it is symmetric.
Let $T$ and $T'$ be symmetric operators on an inner product space of dimension $n$ with
$T = T'$. Then $\lambda_i(T) = \lambda_i(T')$ for every $i < n$.

The operators are variables, so that `subst` can do the transport that a `rw` inside a dependent
type cannot do. -/
theorem eigenvalues_congr {T T' : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hT' : T'.IsSymmetric)
    (h : T = T') (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    hT.eigenvalues hn i = hT'.eigenvalues hn i := by
  subst h; rfl

/-- The eigenvalues of the compressions to two equal subspaces agree. Let $T$ be symmetric, and let
$K = L$ be subspaces of dimension $m$ with orthogonal projections. Then the $i$-th eigenvalues
of the compressions of $T$ to $K$ and to $L$ are equal, for every $i < m$.

The subspaces are variables, so that `subst` can do the transport that a `rw` inside a dependent
type cannot do. -/
theorem eigenvalues_compression_congr {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {K L : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K = L) {m : ℕ}
    (hK : Module.finrank 𝕜 K = m) (hL : Module.finrank 𝕜 L = m) (i : Fin m) :
    (compression.isSymmetric T K hT).eigenvalues hK i
      = (compression.isSymmetric T L hT).eigenvalues hL i := by
  subst hKL; rfl

/-- **The eigenvalues of $-T$ are the negatives of those of $T$, in reverse order.** Let $T$ be a
symmetric operator on an inner product space of dimension $n$. With both lists in decreasing
order, for every $i < n$
$$\lambda_i(-T) = -\lambda_{n - 1 - i}(T).$$

The index $n - 1 - i$ is `i.rev`. The proof is Courant–Fischer: negation of the Rayleigh
quotient exchanges the max–min characterization of $\lambda_i(-T)$
(`LinearMap.IsSymmetric.isGreatest_eigenvalues`, over subspaces of dimension $i + 1$) with the
min–max characterization of $\lambda_{n-1-i}(T)$ (`LinearMap.IsSymmetric.isLeast_eigenvalues`,
over subspaces of dimension $n - (n - 1 - i) = i + 1$), so the two sets of bounds are the same. -/
theorem eigenvalues_neg {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : hT.neg.eigenvalues hn i = -hT.eigenvalues hn i.rev := by
  have hrev : n - ((i.rev : Fin n) : ℕ) = (i : ℕ) + 1 := by
    have := i.isLt
    simp only [Fin.val_rev]
    omega
  refine (hT.neg.isGreatest_eigenvalues hn i).unique ⟨?_, ?_⟩
  · obtain ⟨⟨S, hS, hbd⟩, -⟩ := hT.isLeast_eigenvalues hn i.rev
    refine ⟨S, by rw [hS, hrev], fun x hx hx0 => ?_⟩
    rw [rayleighQuotient_neg]
    linarith [hbd x hx hx0]
  · rintro c ⟨S, hS, hc⟩
    have hmem : -c ∈ {c : ℝ | ∃ S : Submodule 𝕜 E, Module.finrank 𝕜 S = n - ((i.rev : Fin n) : ℕ) ∧
        ∀ x ∈ S, x ≠ 0 → T.rayleighQuotient x ≤ c} := by
      refine ⟨S, by rw [hS, hrev], fun x hx hx0 => ?_⟩
      have := hc x hx hx0
      rw [rayleighQuotient_neg] at this
      linarith
    have := (hT.isLeast_eigenvalues hn i.rev).2 hmem
    linarith

/-- **The sorted eigenvalues are those of any orthonormal eigenbasis.** Let $T$ be a symmetric
operator on an inner product space of dimension $n$, let $(b_i)_{i < n}$ be an orthonormal
basis, and let $\lambda'_0 \ge \dots \ge \lambda'_{n-1}$ be real numbers with
$T b_i = \lambda'_i b_i$ for all $i$. Then $\lambda_i(T) = \lambda'_i$ for all $i$.

The proof applies `LinearMap.IsSymmetric.eigenvalues_eq_of_antitone` to the diagonal matrix of
$T$ in the basis $(b_i)$. Mathlib's `LinearMap.IsSymmetric.eigenvectorBasis` is one choice of
$(b_i)$. The textbook statements about an arbitrary Schur decomposition are reduced to the
sorted eigenvalues through this lemma. -/
theorem eigenvalues_eq_of_apply_eq_ofReal_smul {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (b : OrthonormalBasis (Fin n) 𝕜 E) {lam : Fin n → ℝ}
    (hb : ∀ i, T (b i) = (lam i : 𝕜) • b i) (hlam : Antitone lam) : hT.eigenvalues hn = lam := by
  classical
  have htoM : T.toMatrix b.toBasis b.toBasis = Matrix.diagonal (RCLike.ofReal ∘ lam) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [toMatrix_apply, hb, RCLike.real_smul_eq_coe_mul]
    · simp [toMatrix_apply, hb, h]
  have hroots : T.charpoly.roots = Multiset.map (RCLike.ofReal ∘ lam) Finset.univ.val := by
    rw [← charpoly_toMatrix _ b.toBasis, htoM, Matrix.charpoly_diagonal,
      Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
    simp
  exact hT.eigenvalues_eq_of_antitone hn hlam hroots

/-- **At a simple eigenvalue, $-T$ and $T$ have the same eigenvector line.** Let $T$ be a symmetric
operator on an inner product space of dimension $n$, and let $i < n$. Assume that the eigenvalue
$\lambda_{n-1-i}(T)$ is simple, that is, $\lambda_j(T) \neq \lambda_{n-1-i}(T)$ for all
$j \neq n - 1 - i$. Then the $i$-th eigenvector of $-T$ is $c \, v_{n-1-i}$ for some scalar
$c \neq 0$, where $v_{n-1-i}$ is the $(n - 1 - i)$-th eigenvector of $T$.

The eigenvectors are those of `LinearMap.IsSymmetric.eigenvectorBasis`. In the expansion of the
eigenvector of $-T$ in the eigenbasis of $T$, the coefficients at the other indices have the
factor $\lambda_j - \lambda_{n-1-i} \neq 0$ and vanish. -/
theorem exists_smul_eigenvectorBasis_neg {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n)
    (hsimple : ∀ j : Fin n, j ≠ i.rev → hT.eigenvalues hn j ≠ hT.eigenvalues hn i.rev) :
    ∃ c : 𝕜, c ≠ 0 ∧
      hT.neg.eigenvectorBasis hn i = c • hT.eigenvectorBasis hn i.rev := by
  set b := hT.eigenvectorBasis hn with hb
  set w := hT.neg.eigenvectorBasis hn i with hw
  have hTw : T w = (hT.eigenvalues hn i.rev : 𝕜) • w := by
    have h := hT.neg.apply_eigenvectorBasis hn i
    rw [eigenvalues_neg hT hn i, LinearMap.neg_apply] at h
    have h' := congrArg Neg.neg h
    rwa [neg_neg, RCLike.ofReal_neg, neg_smul, neg_neg] at h'
  have hzero : ∀ j : Fin n, j ≠ i.rev → b.repr w j = 0 := by
    intro j hj
    have h1 := hT.eigenvectorBasis_apply_self_apply hn w j
    rw [hTw, map_smul] at h1
    simp only [PiLp.smul_apply, smul_eq_mul] at h1
    have h2 : ((hT.eigenvalues hn j : 𝕜) - (hT.eigenvalues hn i.rev : 𝕜)) * b.repr w j = 0 := by
      rw [sub_mul]
      rw [← h1]
      ring
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (by exact_mod_cast sub_eq_zero.1 h3) (hsimple j hj)
    · exact h3
  have hsum : ∑ j, b.repr w j • b j = w := b.sum_repr w
  rw [Finset.sum_eq_single i.rev (fun j _ hj => by rw [hzero j hj, zero_smul])
    (fun h => absurd (Finset.mem_univ _) h)] at hsum
  refine ⟨b.repr w i.rev, ?_, hsum.symm⟩
  intro h0
  rw [h0, zero_smul] at hsum
  exact hT.neg.eigenvectorBasis_ne_zero hn i hsum.symm

end LinearMap.IsSymmetric

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Cauchy interlacing for a compression $V^H A V$.** Let $A$ be a Hermitian $N \times N$ matrix,
and let $V$ be an $N \times M$ matrix with $V^H V = I$ and $M \le N$. Then the Hermitian
$M \times M$ matrix $V^H A V$ satisfies, for every $k < M$,
$$\lambda_{k + (N - M)}(A) \le \lambda_k(V^H A V) \le \lambda_k(A),$$
with the eigenvalues in decreasing order.

This is [saad2011numerical], Theorem 1.10, and Theorem 8.1.7 of the 1989 edition of Golub and
Van Loan, *Matrix Computations*. The eigenvalues are `Matrix.IsHermitian.eigenvalues₀`. The
hypothesis that $V^H A V$ is Hermitian names its eigenvalues; it follows from the Hermitian
property of $A$. -/
theorem IsHermitian.eigenvalues₀_conjTranspose_mul_mul_interlace {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {V : Matrix n m 𝕜} (hV : Vᴴ * V = 1) (hB : (Vᴴ * A * V).IsHermitian)
    (hmn : Fintype.card m ≤ Fintype.card n) (k : Fin (Fintype.card m)) :
    hA.eigenvalues₀ ⟨(k : ℕ) + (Fintype.card n - Fintype.card m), by omega⟩ ≤ hB.eigenvalues₀ k ∧
      hB.eigenvalues₀ k ≤ hA.eigenvalues₀ (Fin.castLE hmn k) :=
  (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues_interlace_of_linearIsometry
    finrank_euclideanSpace (isSymmetric_toEuclideanLin_iff.mpr hB) finrank_euclideanSpace hmn
    (toEuclideanLinearIsometry hV) (fun y => by
      rw [toEuclideanLinearIsometry_apply, Matrix.toEuclideanLin_mul_apply,
        Matrix.toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_inner_left]) k

/-- **Cauchy interlacing for a principal submatrix.** Let $A$ be a Hermitian $N \times N$ matrix,
and let $f$ be an injective map from an index set of size $M$ to the indices of $A$. Then the
principal submatrix $A_f = (a_{f(i) f(j)})_{i, j}$, which is Hermitian, satisfies, for every
$k < M$,
$$\lambda_{k + (N - M)}(A) \le \lambda_k(A_f) \le \lambda_k(A),$$
with the eigenvalues in decreasing order.

This is the weak inequalities of [quarteroni2000numerical], Property 5.11, and Theorem 8.1.7 of
the 1989 edition of Golub and Van Loan, *Matrix Computations*. The matrix $A_f$ is
`A.submatrix f f`, and its Hermitian property is a hypothesis that names its eigenvalues. It is
the compression by the matrix $V$ = `(1 : Matrix n n 𝕜).submatrix id f` of the selected columns
of the identity, for which $V^H A V = A_f$. -/
theorem IsHermitian.eigenvalues₀_submatrix_interlace {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {f : m → n} (hf : Function.Injective f) (hB : (A.submatrix f f).IsHermitian)
    (k : Fin (Fintype.card m)) :
    hA.eigenvalues₀ ⟨(k : ℕ) + (Fintype.card n - Fintype.card m),
        by have := Fintype.card_le_of_injective f hf; omega⟩ ≤ hB.eigenvalues₀ k ∧
      hB.eigenvalues₀ k ≤ hA.eigenvalues₀ (Fin.castLE (Fintype.card_le_of_injective f hf) k) := by
  set V : Matrix n m 𝕜 := (1 : Matrix n n 𝕜).submatrix (Equiv.refl n) f with hVdef
  have hVH : Vᴴ = (1 : Matrix n n 𝕜).submatrix f (Equiv.refl n) := by
    rw [hVdef, conjTranspose_submatrix, conjTranspose_one]
  have hVV : Vᴴ * V = 1 := by
    rw [hVH, hVdef, one_submatrix_mul f (Equiv.refl n), submatrix_submatrix]
    simpa using submatrix_one_embedding (α := 𝕜) ⟨f, hf⟩
  have hVAV : Vᴴ * A * V = A.submatrix f f := by
    rw [hVH, hVdef, Matrix.mul_assoc, mul_submatrix_one (Equiv.refl n) f,
      one_submatrix_mul f (Equiv.refl n), submatrix_submatrix]
    simp
  have h := hA.eigenvalues₀_conjTranspose_mul_mul_interlace hVV (hVAV ▸ hB)
    (Fintype.card_le_of_injective f hf) k
  convert h using 3 <;> exact hVAV.symm

end Matrix

/-! ### Traces and the Hoffman–Wielandt inequality for Hermitian matrices -/

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of a Hermitian matrix is the sum of its sorted eigenvalues:
$\operatorname{tr} A = \sum_k \lambda_k$.

This is [golub2013matrix], P8.1.8. Mathlib's `Matrix.IsHermitian.trace_eq_sum_eigenvalues` is
the same statement for the eigenvalues indexed by the rows of $A$; here they are
`Matrix.IsHermitian.eigenvalues₀`. -/
theorem trace_eq_sum_eigenvalues₀ {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A.trace = ∑ k, (hA.eigenvalues₀ k : 𝕜) := by
  rw [← A.trace_toLin_eq (EuclideanSpace.basisFun n 𝕜).toBasis,
    ← toEuclideanLin_eq_toLin_orthonormal]
  exact_mod_cast (isSymmetric_toEuclideanLin_iff.mpr hA).trace_eq_sum_eigenvalues
    finrank_euclideanSpace

open scoped Matrix.Norms.Frobenius in
/-- For a Hermitian matrix $M$, the square of the Frobenius norm is the real part of the trace of
the square of the operator `Matrix.toEuclideanLin M`: $\|M\|_F^2 = \sum_{i, j} |m_{ij}|^2 =
\operatorname{Re} \operatorname{tr}(M M)$, since $m_{ji} = \overline{m_{ij}}$. -/
theorem re_trace_toEuclideanLin_comp_self {M : Matrix n n 𝕜} (hM : M.IsHermitian) :
    RCLike.re (LinearMap.trace 𝕜 _ (toEuclideanLin M ∘ₗ toEuclideanLin M)) = ‖M‖ ^ 2 := by
  rw [← toLpLin_mul_same, toLpLin_eq_toLin,
    LinearMap.trace_eq_matrix_trace 𝕜 (PiLp.basisFun 2 𝕜 n), LinearMap.toMatrix_toLin,
    frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num
  rw [trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diag_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hM.apply i j, RCLike.star_def, RCLike.conj_mul, RCLike.norm_conj, ← RCLike.ofReal_pow,
    RCLike.ofReal_re]

open scoped Matrix.Norms.Frobenius in
/-- **The Hoffman–Wielandt inequality.** Let $A$ and $B$ be Hermitian matrices of the same order.
With both lists of eigenvalues in decreasing order,
$$\sum_k (\lambda_k(A) - \lambda_k(B))^2 \le \|A - B\|_F^2.$$

This is [golub2013matrix], Theorem 8.1.4, where it is called the Wielandt–Hoffman theorem. The
eigenvalues are `Matrix.IsHermitian.eigenvalues₀`, and $\|\cdot\|_F$ is the Frobenius norm. The
proof is the operator form `LinearMap.IsSymmetric.sum_sq_eigenvalues_sub_le` for
`Matrix.toEuclideanLin`, with `Matrix.IsHermitian.re_trace_toEuclideanLin_comp_self` for the
right side. -/
theorem hoffman_wielandt {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ k, (hA.eigenvalues₀ k - hB.eigenvalues₀ k) ^ 2 ≤ ‖A - B‖ ^ 2 := by
  rw [← (hA.sub hB).re_trace_toEuclideanLin_comp_self, map_sub]
  exact LinearMap.IsSymmetric.sum_sq_eigenvalues_sub_le finrank_euclideanSpace
    (isSymmetric_toEuclideanLin_iff.mpr hA) (isSymmetric_toEuclideanLin_iff.mpr hB)

end Matrix.IsHermitian

/-! ### The sorted eigenvalues of a Hermitian matrix, indexed by `Fin n` -/

namespace Matrix.IsHermitian

variable {n : ℕ}

/-- The eigenvalues of a Hermitian $n \times n$ matrix $A$, **sorted in decreasing order and indexed
by $\{0, \dots, n - 1\}$**. The value at $k$ is the $(k + 1)$-th largest eigenvalue, the
$\lambda_{k+1}(A)$ of [golub2013matrix], §8.1.1.

This is Mathlib's `Matrix.IsHermitian.eigenvalues₀` reindexed along `Fintype.card_fin`, because
the index type `Fin (Fintype.card (Fin n))` of `eigenvalues₀` is not `Fin n` by definition. With
this reindexing, statements about the $k$-th eigenvalue of a matrix and of its leading principal
submatrices can use `Fin.succ` and `Fin.castSucc`. -/
noncomputable def sortedEigenvalues {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    Fin n → ℝ :=
  hA.eigenvalues₀ ∘ Fin.cast (Fintype.card_fin n).symm

/-- The sorted eigenvalues `Matrix.IsHermitian.sortedEigenvalues` at $k$ are Mathlib's
`Matrix.IsHermitian.eigenvalues₀` at the index $k$ cast to `Fin (Fintype.card (Fin n))`. -/
theorem sortedEigenvalues_apply {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) (k : Fin n) :
    hA.sortedEigenvalues k = hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm k) :=
  rfl

/-- The sorted eigenvalues depend only on the matrix, and not on the proof that it is Hermitian or
on the way it is written: if $A = B$, then the sorted eigenvalues of $A$ and $B$ are equal. -/
theorem sortedEigenvalues_congr {A B : Matrix (Fin n) (Fin n) 𝕜} (h : A = B) (hA : A.IsHermitian)
    (hB : B.IsHermitian) : hA.sortedEigenvalues = hB.sortedEigenvalues := by
  subst h
  rfl

/-- The sorted eigenvalues of a Hermitian matrix decrease: $\lambda_0 \ge \lambda_1 \ge \dots \ge
\lambda_{n-1}$. -/
theorem sortedEigenvalues_antitone {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    Antitone hA.sortedEigenvalues := fun i j hij =>
  hA.eigenvalues₀_antitone (show Fin.cast _ i ≤ Fin.cast _ j from hij)

/-- The roots of the characteristic polynomial of a Hermitian $n \times n$ matrix, counted with
multiplicity, are its sorted eigenvalues $\lambda_0, \dots, \lambda_{n-1}$, as a multiset. -/
theorem roots_charpoly_eq_sortedEigenvalues {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hA.sortedEigenvalues) Finset.univ.val := by
  rw [hA.roots_charpoly_eq_eigenvalues₀,
    ← Finset.map_univ_equiv (finCongr (Fintype.card_fin n).symm), Finset.map_val,
    Multiset.map_map]
  rfl

/-- **Cauchy interlacing for the leading principal submatrix.** Let $A$ be a Hermitian
$(n + 1) \times (n + 1)$ matrix, and let $A_n$ be its leading principal $n \times n$ submatrix,
which is Hermitian. With the sorted eigenvalues indexed from $0$, for every $k < n$
$$\lambda_{k+1}(A) \le \lambda_k(A_n) \le \lambda_k(A).$$

This is [golub2013matrix], Theorem 8.1.7, and the weak inequalities of
[quarteroni2000numerical], Property 5.11. The submatrix $A_n$ is
`A.submatrix Fin.castSucc Fin.castSucc`, and its Hermitian property is a hypothesis that names
its eigenvalues. This is `Matrix.IsHermitian.eigenvalues₀_submatrix_interlace` with the indices
in `Fin n`. -/
theorem sortedEigenvalues_submatrix_castSucc_interlace {A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜}
    (hA : A.IsHermitian) (hB : (A.submatrix Fin.castSucc Fin.castSucc).IsHermitian) (k : Fin n) :
    hA.sortedEigenvalues k.succ ≤ hB.sortedEigenvalues k ∧
      hB.sortedEigenvalues k ≤ hA.sortedEigenvalues k.castSucc := by
  have hmn : Fintype.card (Fin n) ≤ Fintype.card (Fin (n + 1)) := by simp
  have h := hA.eigenvalues₀_submatrix_interlace (Fin.castSucc_injective n) hB
    (Fin.cast (Fintype.card_fin n).symm k)
  have e1 : (⟨(Fin.cast (Fintype.card_fin n).symm k : ℕ) + (Fintype.card (Fin (n + 1))
      - Fintype.card (Fin n)), by simp⟩ : Fin (Fintype.card (Fin (n + 1))))
      = Fin.cast (Fintype.card_fin (n + 1)).symm k.succ := by
    ext; simp
  have e2 : Fin.castLE hmn (Fin.cast (Fintype.card_fin n).symm k)
      = Fin.cast (Fintype.card_fin (n + 1)).symm k.castSucc := by
    ext; simp
  rw [e1, e2] at h
  exact h

/-- **The spectral decomposition with sorted eigenvalues.** Let $A$ be a Hermitian $n \times n$
matrix with sorted eigenvalues $\lambda_0 \ge \dots \ge \lambda_{n-1}$. Then there is a unitary
matrix $U$ with columns $u_0, \dots, u_{n-1}$ such that
$$U^H A U = \operatorname{diag}(\lambda_0, \dots, \lambda_{n-1}), \qquad A u_k = \lambda_k u_k
  \text{ for all } k.$$

This is [golub2013matrix], Theorem 8.1.1, with $\lambda_1 \ge \dots \ge \lambda_n$ in the
indexing from $1$. The columns of $U$ are the eigenvector basis of `Matrix.toEuclideanLin A`,
which Mathlib sorts. Mathlib's `Matrix.IsHermitian.spectral_theorem` is the unsorted form. For
$\mathbb{K} = \mathbb{R}$ the unitary group is the orthogonal group. -/
theorem exists_unitary_conj_eq_diagonal_sortedEigenvalues {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) 𝕜,
      star U * A * U = Matrix.diagonal (fun k => (hA.sortedEigenvalues k : 𝕜)) ∧
        ∀ k, A *ᵥ U.col k = (hA.sortedEigenvalues k : 𝕜) • U.col k := by
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let b := (hT.eigenvectorBasis finrank_euclideanSpace).reindex (finCongr (Fintype.card_fin n))
  let U := (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis.toMatrix b.toBasis
  have hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜 :=
    (EuclideanSpace.basisFun (Fin n) 𝕜).toMatrix_orthonormalBasis_mem_unitary b
  have hcol : ∀ k, A *ᵥ U.col k = (hA.sortedEigenvalues k : 𝕜) • U.col k := fun k => by
    have h := hT.apply_eigenvectorBasis finrank_euclideanSpace
      (Fin.cast (Fintype.card_fin n).symm k)
    have hbk : b k = hT.eigenvectorBasis finrank_euclideanSpace
        (Fin.cast (Fintype.card_fin n).symm k) := by
      simp [b, OrthonormalBasis.reindex_apply]
    have hUk : U.col k = WithLp.ofLp (b k) := by
      ext i; simp [U, Matrix.col, Module.Basis.toMatrix_apply]
    rw [hUk, hbk, ← Matrix.ofLp_toEuclideanLin, h, WithLp.ofLp_smul]
    rfl
  have hAU : A * U = U * Matrix.diagonal (fun k => (hA.sortedEigenvalues k : 𝕜)) := by
    ext i k
    rw [Matrix.mul_diagonal]
    have := congrFun (hcol k) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.col, mul_comm] using this
  refine ⟨U, hU, ?_, hcol⟩
  rw [Matrix.mul_assoc, hAU, ← Matrix.mul_assoc, (Matrix.mem_unitaryGroup_iff').mp hU,
    Matrix.one_mul]

end Matrix.IsHermitian

/-! ### Stationary points of the Rayleigh quotient -/

section Gradient

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The gradient of the Rayleigh quotient.** Let $F$ be a real Hilbert space, let
$T \colon F \to F$ be a continuous linear map that is symmetric, and let $x \neq 0$. Then the
Rayleigh quotient $r(y) = \langle Ty, y \rangle / \|y\|^2$ has at $x$ the gradient
$$\nabla r(x) = \frac{2}{\|x\|^2} \bigl(Tx - r(x) x\bigr).$$

This is [golub2013matrix], (10.1.1). In particular the gradient lies in the span of $x$ and
$Tx$. The proof is the quotient rule for $\langle Ty, y \rangle$, with derivative
$2 \langle Tx, \cdot \rangle$ (Mathlib's
`LinearMap.IsSymmetric.hasStrictFDerivAt_reApplyInnerSelf`), over $\|y\|^2$, with derivative
$2 \langle x, \cdot \rangle$. The Rayleigh quotient is `ContinuousLinearMap.rayleighQuotient`. -/
theorem ContinuousLinearMap.hasGradientAt_rayleighQuotient [CompleteSpace F] {T : F →L[ℝ] F}
    (hT : (T : F →ₗ[ℝ] F).IsSymmetric) {x : F} (hx : x ≠ 0) :
    HasGradientAt T.rayleighQuotient
      ((2 / ‖x‖ ^ 2) • (T x - T.rayleighQuotient x • x)) x := by
  have hN : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hQ := (hT.hasStrictFDerivAt_reApplyInnerSelf x).hasFDerivAt
  have hD := (hasFDerivAt_inv hN).comp x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hQ.mul hD using 1
  · ext y; simp [ContinuousLinearMap.rayleighQuotient, div_eq_mul_inv]
  · ext y
    simp only [InnerProductSpace.toDual_apply_apply, add_apply, smul_apply, Function.comp_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, inner_smul_left, inner_sub_left,
      ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      RCLike.re_to_real, RCLike.conj_to_real, nsmul_eq_mul, Nat.cast_ofNat]
    rw [real_inner_comm y (T x), real_inner_comm y x]
    field_simp
    ring

/-- **The stationary points of the Rayleigh quotient are the eigenvectors.** Let $F$ be a
finite-dimensional real inner product space, let $T \colon F \to F$ be symmetric, and let
$x \neq 0$. If $f'$ is the Fréchet derivative at $x$ of the Rayleigh quotient
$r(y) = \langle Ty, y \rangle / \|y\|^2$, then
$$f' = 0 \iff Tx = r(x) \, x.$$

This is [golub2013matrix], (12.5.23). The derivative is the gradient of
`ContinuousLinearMap.hasGradientAt_rayleighQuotient`, a nonzero multiple of $Tx - r(x) x$.
Mathlib has only the extremal case, `IsSelfAdjoint.hasEigenvector_of_isLocalExtrOn`. -/
theorem LinearMap.IsSymmetric.hasFDerivAt_rayleighQuotient_eq_zero_iff
    [FiniteDimensional ℝ F] {T : F →ₗ[ℝ] F} (hT : T.IsSymmetric) {x : F} (hx : x ≠ 0)
    {f' : F →L[ℝ] ℝ} (hf : HasFDerivAt T.rayleighQuotient f' x) :
    f' = 0 ↔ T x = T.rayleighQuotient x • x := by
  set T' := LinearMap.toContinuousLinearMap T
  have hg := ContinuousLinearMap.hasGradientAt_rayleighQuotient (T := T') hT hx
  have heq : f' = InnerProductSpace.toDual ℝ F
      ((2 / ‖x‖ ^ 2) • (T' x - T'.rayleighQuotient x • x)) :=
    hf.unique (hasGradientAt_iff_hasFDerivAt.mp hg)
  have hN : 2 / ‖x‖ ^ 2 ≠ 0 :=
    div_ne_zero two_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  rw [heq, map_eq_zero_iff _ (InnerProductSpace.toDual ℝ F).injective, smul_eq_zero, sub_eq_zero]
  simp only [hN, false_or]
  rfl

end Gradient
