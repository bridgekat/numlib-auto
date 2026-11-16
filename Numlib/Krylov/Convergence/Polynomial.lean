/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Topology.Algebra.Polynomial
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.Analysis.InnerProductSpace.Projection.Compression
import Numlib.Eigen.MinMax

/-!
# Polynomials in a symmetric operator: spectral norm bounds

Let $A$ be a symmetric operator on a finite-dimensional inner product space $E$ over $\mathbb{R}$ or
$\mathbb{C}$, and let $p$ be a polynomial. Expanding a vector in an orthonormal basis of
eigenvectors of $A$ (`LinearMap.IsSymmetric.eigenvectorBasis`) gives
$$\|p(A) x\| \le \max_{\lambda \in \sigma(A)} |p(\lambda)| \, \|x\|,$$
and the same bound holds in the energy norm $\|x\|_A = \sqrt{\operatorname{Re} \langle Ax, x
\rangle}$ when $A$ is also coercive. If $A = X D X^{-1}$ with $D$ symmetric, the bound acquires the
factor $\|X\| \|X^{-1}\|$.

The Chebyshev convergence bounds need the form on a real interval. Suppose that $A$ is symmetric
with $a \|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle \le b \|x\|^2$ for all $x$. Then $\|p(A)
x\| \le \sup_{t \in [a, b]} |p(t)| \, \|x\|$ for every real polynomial $p$, in *any* inner product
space. The proof is the **compression argument**: the vector $p(A) x$ is computed inside the
finite-dimensional space $K = \operatorname{span}\{x, Ax, \dots, A^{\deg p} x\}$, where it equals
$p(P_K A|_K) x$ for the compression $P_K A|_K$, and the compression satisfies the same bounds $a$
and $b$. This argument appears in the proofs of Lemmas 6.28 and 6.31 of [saad2003iterative], in
Lemma 6.1 of [saad2011numerical], in (5.6.16)–(5.6.19) of [han2009theoretical], and in (3.7)–(3.8)
of [meurant2006lanczos].

## Main results

* `LinearMap.IsSymmetric.repr_aeval_apply`: in the eigenvector basis, $p(A)$ multiplies the $i$-th
  coordinate by $p(\lambda_i)$.
* `LinearMap.IsSymmetric.norm_aeval_apply_le`: if $|p(\mu)| \le C$ at every eigenvalue $\mu$ of $A$,
  then $\|p(A) x\| \le C \|x\|$.
* `LinearMap.IsSymmetric.energyNorm_aeval_apply_le`: the same bound in the energy norm, for
  symmetric coercive $A$.
* `norm_aeval_apply_le_of_conj`: for $A = X D X^{-1}$ with $D$ symmetric,
  $\|p(A) x\| \le \|X\| \|X^{-1}\| C \|x\|$ (Proposition 6.32 of [saad2003iterative]).
* `compression.isSymmetricBoundedBy`, `compression.isSymmetricCoercive`: bounds on the quadratic
  form, and coercivity, pass to compressions.
* `compression.energyNorm_apply`: the energy norm of the compression is the restriction of the
  energy norm of $A$.
* `LinearMap.IsSymmetricBoundedBy.norm_aeval_map_apply_le`:
  $\|p(A) x\| \le \sup_{[a, b]} |p| \, \|x\|$ in any inner product space.
* `LinearMap.IsSymmetricBoundedBy.energyNorm_aeval_map_apply_le`: the same bound in the energy norm,
  for $a > 0$.

## Notation

* $p(A)$ is `aeval A p`. A real polynomial $p$ acts on an operator over $\mathbb{R}$ or $\mathbb{C}$
  through `p.map (algebraMap ℝ 𝕜)`.

## Implementation notes

* The interval bounds are proved by the compression argument, not by the continuous functional
  calculus. A version for Hilbert spaces through the continuous functional calculus would be an
  alternative; the statements here do not need it.
-/

open Polynomial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

namespace LinearMap.IsSymmetric

variable {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
include hA

/-- Let $A$ be a symmetric operator on an inner product space $E$ of finite dimension $n$, and let
$(e_i)$ be the orthonormal basis of eigenvectors `LinearMap.IsSymmetric.eigenvectorBasis` with
the eigenvalues $\lambda_i$ (`LinearMap.IsSymmetric.eigenvalues`). For every polynomial $p$ and
every $x \in E$, the $i$-th coordinate of $p(A) x$ is $p(\lambda_i)$ times the $i$-th coordinate
of $x$:
$$\langle e_i, p(A) x \rangle = p(\lambda_i) \langle e_i, x \rangle.$$

This expansion is behind every bound on $p(A)$ by the values of $p$ on the spectrum, here and in
the Krylov eigenvalue estimates. The coordinates are those of `OrthonormalBasis.repr`, indexed
by `Fin n`. -/
theorem repr_aeval_apply {n : ℕ} (hn : Module.finrank 𝕜 E = n) (p : 𝕜[X]) (x : E)
    (i : Fin n) :
    (hA.eigenvectorBasis hn).repr (aeval A p x) i =
      p.eval (hA.eigenvalues hn i : 𝕜) * (hA.eigenvectorBasis hn).repr x i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial k c =>
      have hmon : aeval A (monomial k c) x = c • (A ^ k) x := by
        simp [aeval_monomial]
      rw [hmon, map_smul, PiLp.smul_apply, smul_eq_mul,
        (hA.eigenvectorBasis hn).repr_pow_apply_of_apply_eq_smul (hA.apply_eigenvectorBasis hn),
        eval_monomial]
      ring

/-- Let $A$ be a symmetric operator on a finite-dimensional inner product space $E$, let $p$ be a
polynomial, and let $C \in \mathbb{R}$ satisfy $|p(\mu)| \le C$ for every eigenvalue $\mu$ of
$A$. Then for every $x \in E$,
$$\|p(A) x\| \le C \|x\|.$$

The eigenvalues of $p(A)$ are the values $p(\lambda)$ at the eigenvalues $\lambda$ of $A$, and
the proof expands $x$ in an orthonormal basis of eigenvectors
(`LinearMap.IsSymmetric.repr_aeval_apply`). -/
theorem norm_aeval_apply_le {C : ℝ} (p : 𝕜[X])
    (hC : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → ‖p.eval μ‖ ≤ C) (x : E) :
    ‖aeval A p x‖ ≤ C * ‖x‖ := by
  set n := Module.finrank 𝕜 E with hn'
  have hn : Module.finrank 𝕜 E = n := rfl
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · have : Subsingleton E := Module.finrank_zero_iff.mp (hn'.symm.trans h0)
    simp [Subsingleton.elim x 0]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ (hA.hasEigenvalue_eigenvalues hn ⟨0, h0⟩))
  have key : ‖aeval A p x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [← (hA.eigenvectorBasis hn).sum_sq_norm_inner_right (aeval A p x), mul_pow,
      ← (hA.eigenvectorBasis hn).sum_sq_norm_inner_right x, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← OrthonormalBasis.repr_apply_apply, ← OrthonormalBasis.repr_apply_apply,
      hA.repr_aeval_apply hn, norm_mul, mul_pow]
    gcongr
    exact hC _ (hA.hasEigenvalue_eigenvalues hn i)
  have := Real.sqrt_le_sqrt key
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (mul_nonneg hC0 (norm_nonneg x))] at this

/-- Let $A$ be a symmetric coercive operator on a finite-dimensional inner product space $E$, let
$p$ be a polynomial, and let $C \in \mathbb{R}$ satisfy $|p(\mu)| \le C$ for every eigenvalue
$\mu$ of $A$. Then for every $x \in E$, in the energy norm $\|x\|_A = \sqrt{\operatorname{Re}
\langle Ax, x \rangle}$,
$$\|p(A) x\|_A \le C \|x\|_A.$$

Coercivity is `LinearMap.IsSymmetricCoercive`, and the energy norm is `energyNorm A`. -/
theorem energyNorm_aeval_apply_le (hA' : A.IsSymmetricCoercive) {C : ℝ} (p : 𝕜[X])
    (hC : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → ‖p.eval μ‖ ≤ C) (x : E) :
    energyNorm A (aeval A p x) ≤ C * energyNorm A x := by
  set n := Module.finrank 𝕜 E with hn'
  have hn : Module.finrank 𝕜 E = n := rfl
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · have : Subsingleton E := Module.finrank_zero_iff.mp (hn'.symm.trans h0)
    simp [Subsingleton.elim x 0, energyNorm]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ (hA.hasEigenvalue_eigenvalues hn ⟨0, h0⟩))
  have hpos : ∀ i : Fin n, 0 ≤ hA.eigenvalues hn i := fun i => by
    have h := hA'.re_pos_of_hasEigenvalue (hA.hasEigenvalue_eigenvalues hn i)
    simpa using h.le
  have key : RCLike.re (inner 𝕜 (A (aeval A p x)) (aeval A p x)) ≤
      C ^ 2 * RCLike.re (inner 𝕜 (A x) x) := by
    rw [hA.re_inner_apply_self_eq_sum hn, hA.re_inner_apply_self_eq_sum hn, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hA.repr_aeval_apply hn, norm_mul, mul_pow]
    have hle : ‖p.eval (hA.eigenvalues hn i : 𝕜)‖ ^ 2 ≤ C ^ 2 := by
      gcongr
      exact hC _ (hA.hasEigenvalue_eigenvalues hn i)
    have hnn : 0 ≤ hA.eigenvalues hn i * ‖(hA.eigenvectorBasis hn).repr x i‖ ^ 2 :=
      mul_nonneg (hpos i) (sq_nonneg _)
    linarith [mul_le_mul_of_nonneg_left hle hnn]
  calc energyNorm A (aeval A p x) ≤ Real.sqrt (C ^ 2 * RCLike.re (inner 𝕜 (A x) x)) :=
        Real.sqrt_le_sqrt key
    _ = C * energyNorm A x := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC0]; rfl

omit [FiniteDimensional 𝕜 E] in
/-- The eigenvalues of a symmetric operator on an inner product space are real: if $\mu$ is an
eigenvalue, then $\operatorname{Im} \mu = 0$. No finite dimension is assumed. -/
theorem im_eq_zero_of_hasEigenvalue {μ : 𝕜} (hμ : Module.End.HasEigenvalue A μ) :
    RCLike.im μ = 0 :=
  RCLike.conj_eq_iff_im.mp (hA.conj_eigenvalue_eq_self hμ)

end LinearMap.IsSymmetric

/-- Let $E$ be a finite-dimensional inner product space, let $X : E \to E$ be a continuous linear
isomorphism, let $D$ be symmetric, and let $A = X D X^{-1}$. If $p$ is a polynomial and
$|p(\mu)| \le C$ for every eigenvalue $\mu$ of $D$, then for every $x \in E$
$$\|p(A) x\| \le \|X\| \, \|X^{-1}\| \, C \, \|x\|,$$
where $\|X\| \|X^{-1}\|$ is the condition number $\kappa(X)$ of $X$. This is Proposition 6.32 of
[saad2003iterative], for a diagonalizable $A$.

The operator $D$ is required to be symmetric, so that the finite-dimensional bound
`LinearMap.IsSymmetric.norm_aeval_apply_le` applies to it. -/
theorem norm_aeval_apply_le_of_conj {A D : E →ₗ[𝕜] E} (X : E ≃L[𝕜] E)
    (hconj : A = (X : E →ₗ[𝕜] E) ∘ₗ D ∘ₗ (X.symm : E →ₗ[𝕜] E)) (hD : D.IsSymmetric) {C : ℝ}
    (p : 𝕜[X]) (hC : ∀ μ : 𝕜, Module.End.HasEigenvalue D μ → ‖p.eval μ‖ ≤ C) (x : E) :
    ‖aeval A p x‖ ≤ ‖(X : E →L[𝕜] E)‖ * ‖(X.symm : E →L[𝕜] E)‖ * C * ‖x‖ := by
  have hAe : A = (X.toLinearEquiv.conjAlgEquiv 𝕜) D := hconj
  have haeval : aeval A p = (X.toLinearEquiv.conjAlgEquiv 𝕜) (aeval D p) := by
    rw [hAe, ← aeval_algHom_apply]
  have hx : aeval A p x = X (aeval D p (X.symm x)) := by rw [haeval]; rfl
  rcases Nat.eq_zero_or_pos (Module.finrank 𝕜 E) with h0 | h0
  · have : Subsingleton E := Module.finrank_zero_iff.mp h0
    simp [Subsingleton.elim x 0]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ (hD.hasEigenvalue_eigenvalues rfl ⟨0, h0⟩))
  calc ‖aeval A p x‖ = ‖X (aeval D p (X.symm x))‖ := by rw [hx]
    _ ≤ ‖(X : E →L[𝕜] E)‖ * ‖aeval D p (X.symm x)‖ :=
        (X : E →L[𝕜] E).le_opNorm (aeval D p (X.symm x))
    _ ≤ ‖(X : E →L[𝕜] E)‖ * (C * ‖X.symm x‖) :=
        mul_le_mul_of_nonneg_left (hD.norm_aeval_apply_le p hC _) (norm_nonneg _)
    _ ≤ ‖(X : E →L[𝕜] E)‖ * (C * (‖(X.symm : E →L[𝕜] E)‖ * ‖x‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ((X.symm : E →L[𝕜] E).le_opNorm x) hC0) (norm_nonneg _)
    _ = ‖(X : E →L[𝕜] E)‖ * ‖(X.symm : E →L[𝕜] E)‖ * C * ‖x‖ := by ring

end FiniteDimensional

section Compression

/-!
### The compression argument

In $m$ steps, a Krylov method works inside the finite-dimensional space $\mathcal{K}_{m+1}$, on
which $A$ acts, up to the last step, as its compression $P_K A|_K$ (`compression A K`).
-/

namespace compression

variable (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]

/-- Let $K$ be a subspace with an orthogonal projection $P_K$. If $A$ is symmetric with
$\lambda_{\min} \|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle \le \lambda_{\max} \|x\|^2$
for all $x$ (`LinearMap.IsSymmetricBoundedBy`), then the compression $P_K A|_K$ of $A$ to $K$ is
symmetric and satisfies the same bounds with the same constants $\lambda_{\min}$ and
$\lambda_{\max}$. -/
theorem isSymmetricBoundedBy {lmin lmax : ℝ} (hA : A.IsSymmetricBoundedBy lmin lmax) :
    (compression A K).IsSymmetricBoundedBy lmin lmax :=
  hA.of_inner_eq (compression.isSymmetric A K hA.isSymmetric) K.subtypeₗᵢ
    fun x => compression.inner_apply A K x x

/-- Let $K$ be a subspace with an orthogonal projection $P_K$. If $A$ is symmetric and coercive,
then the compression $P_K A|_K$ of $A$ to $K$ is symmetric and coercive on $K$, with the same
coercivity constant.

The quadratic form of the compression is the restriction of the quadratic form of $A$
(`compression.inner_apply`), so the defining inequality is inherited directly. This lets the
finite-dimensional energy-norm bounds be applied inside $K$. -/
theorem isSymmetricCoercive (hA : A.IsSymmetricCoercive) :
    (compression A K).IsSymmetricCoercive := by
  obtain ⟨c, hc, hcA⟩ := hA.isCoercive
  refine ⟨compression.isSymmetric A K hA.isSymmetric, c, hc, fun x => ?_⟩
  rw [compression.inner_apply A K x x]
  exact hcA (x : E)

/-- The energy inner product of the compression is the restriction of the energy inner product of
$A$: for $x, y \in K$, $\langle P_K A x, y \rangle = \langle Ax, y \rangle$. -/
theorem energyInner_apply (x y : K) : energyInner (compression A K) x y = energyInner A x y :=
  compression.inner_apply A K x y

/-- Let $K$ be a subspace with an orthogonal projection $P_K$. For every $x \in K$, the energy norm
of $x$ for the compression $P_K A|_K$ equals its energy norm for $A$:
$$\|x\|_{P_K A|_K} = \|x\|_A.$$

This is what lets the compression argument carry an energy-norm bound, proved in the
finite-dimensional space $K$, back to $E$ with no loss in the constant. -/
theorem energyNorm_apply (x : K) : energyNorm (compression A K) x = energyNorm A x := by
  rw [energyNorm, energyNorm, compression.inner_apply A K x x]

end compression

end Compression

section Interval

/-- For a symmetric operator with quadratic form bounded by $a$ and $b$, the value of a real
polynomial $p$ at an eigenvalue of the operator is at most $\sup_{t \in [a, b]} |p(t)|$ in
absolute value. -/
private theorem norm_eval_map_le_sSup {A : E →ₗ[𝕜] E} {a b : ℝ}
    (hA : A.IsSymmetricBoundedBy a b) (p : ℝ[X]) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue A μ) :
    ‖(p.map (algebraMap ℝ 𝕜)).eval μ‖ ≤ sSup ((fun t => |p.eval t|) '' Set.Icc a b) := by
  have hre : ((RCLike.re μ : ℝ) : 𝕜) = μ :=
    RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr
      (hA.isSymmetric.im_eq_zero_of_hasEigenvalue hμ))
  have hmem : RCLike.re μ ∈ Set.Icc a b := hA.re_mem_Icc_of_hasEigenvalue hμ
  have hμ' : μ = algebraMap ℝ 𝕜 (RCLike.re μ) := by
    rw [RCLike.algebraMap_eq_ofReal]; exact hre.symm
  have heval : (p.map (algebraMap ℝ 𝕜)).eval μ = ((p.eval (RCLike.re μ) : ℝ) : 𝕜) := by
    conv_lhs => rw [hμ']
    rw [eval_map, eval₂_at_apply, RCLike.algebraMap_eq_ofReal]
  rw [heval, RCLike.norm_ofReal]
  exact le_csSup (isCompact_Icc.image p.continuous.abs).bddAbove ⟨RCLike.re μ, hmem, rfl⟩

end Interval

section CompressionSpace

/-- The Krylov subspace $\operatorname{span}\{x, Ax, \dots, A^d x\}$ of the compression argument: it
contains $x$, and $p(A) x$ can be computed inside it when $\deg p \le d$. -/
private noncomputable def compressionSpace (A : E →ₗ[𝕜] E) (d : ℕ) (x : E) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range fun i : Fin (d + 1) => (A ^ (i : ℕ)) x)

private instance (A : E →ₗ[𝕜] E) (d : ℕ) (x : E) :
    FiniteDimensional 𝕜 (compressionSpace A d x) :=
  FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)

private theorem pow_mem_compressionSpace {A : E →ₗ[𝕜] E} {d : ℕ} (x : E) {i : ℕ} (hi : i ≤ d) :
    (A ^ i) x ∈ compressionSpace A d x :=
  Submodule.subset_span ⟨⟨i, Nat.lt_succ_of_le hi⟩, rfl⟩

end CompressionSpace

namespace LinearMap.IsSymmetricBoundedBy

variable {A : E →ₗ[𝕜] E} {a b : ℝ} (hA : A.IsSymmetricBoundedBy a b)
include hA

/-- Let $E$ be an inner product space over $\mathbb{R}$ or $\mathbb{C}$, and let $A$ be symmetric
with $a \|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle \le b \|x\|^2$ for all $x \in E$.
For every real polynomial $p$ and every $x \in E$,
$$\|p(A) x\| \le \sup_{t \in [a, b]} |p(t)| \, \|x\|.$$

No finite dimension and no completeness are assumed. The proof applies the finite-dimensional
bound `LinearMap.IsSymmetric.norm_aeval_apply_le` to the compression of $A$ to
$\operatorname{span}\{x, Ax, \dots, A^{\deg p} x\}$. The supremum is `sSup` of the image of
`Set.Icc a b`, and the real polynomial acts on $A$ through `p.map (algebraMap ℝ 𝕜)`. -/
theorem norm_aeval_map_apply_le (p : ℝ[X]) (x : E) :
    ‖aeval A (p.map (algebraMap ℝ 𝕜)) x‖ ≤
      sSup ((fun t => |p.eval t|) '' Set.Icc a b) * ‖x‖ := by
  set q := p.map (algebraMap ℝ 𝕜) with hq
  set K := compressionSpace A p.natDegree x with hK
  have hxK : x ∈ K := by
    have := pow_mem_compressionSpace (A := A) (d := p.natDegree) (i := 0) x (Nat.zero_le _)
    simpa [hK] using this
  have hpow : ∀ i ≤ q.natDegree, (A ^ i) ((⟨x, hxK⟩ : K) : E) ∈ K := fun i hi =>
    pow_mem_compressionSpace x (hi.trans (hq ▸ natDegree_map_le))
  have h1 : ((aeval (compression A K) q (⟨x, hxK⟩ : K) : K) : E) = aeval A q x :=
    compression.aeval_apply_of_forall_pow_mem A K q hpow
  have h2 := (compression.isSymmetricBoundedBy A K hA).isSymmetric.norm_aeval_apply_le
    (C := sSup ((fun t => |p.eval t|) '' Set.Icc a b)) q
    (fun _ hμ => norm_eval_map_le_sSup (compression.isSymmetricBoundedBy A K hA) p hμ)
    (⟨x, hxK⟩ : K)
  have h3 : ‖aeval (compression A K) q (⟨x, hxK⟩ : K)‖ = ‖aeval A q x‖ := by rw [← h1]; rfl
  rwa [h3, show ‖(⟨x, hxK⟩ : K)‖ = ‖x‖ from rfl] at h2

/-- Let $E$ be an inner product space over $\mathbb{R}$ or $\mathbb{C}$, and let $A$ be symmetric
with $a \|x\|^2 \le \operatorname{Re} \langle Ax, x \rangle \le b \|x\|^2$ for all $x \in E$,
where $a > 0$. For every real polynomial $p$ and every $x \in E$, in the energy norm $\|x\|_A =
\sqrt{\operatorname{Re} \langle Ax, x \rangle}$,
$$\|p(A) x\|_A \le \sup_{t \in [a, b]} |p(t)| \, \|x\|_A.$$

The hypothesis $a > 0$ makes $A$ coercive. The proof applies
`LinearMap.IsSymmetric.energyNorm_aeval_apply_le` to a compression of $A$ and uses
`compression.energyNorm_apply` to return to $E$. -/
theorem energyNorm_aeval_map_apply_le (ha : 0 < a) (p : ℝ[X]) (x : E) :
    energyNorm A (aeval A (p.map (algebraMap ℝ 𝕜)) x) ≤
      sSup ((fun t => |p.eval t|) '' Set.Icc a b) * energyNorm A x := by
  set q := p.map (algebraMap ℝ 𝕜) with hq
  set K := compressionSpace A p.natDegree x with hK
  have hxK : x ∈ K := by
    have := pow_mem_compressionSpace (A := A) (d := p.natDegree) (i := 0) x (Nat.zero_le _)
    simpa [hK] using this
  have hpow : ∀ i ≤ q.natDegree, (A ^ i) ((⟨x, hxK⟩ : K) : E) ∈ K := fun i hi =>
    pow_mem_compressionSpace x (hi.trans (hq ▸ natDegree_map_le))
  have h1 : ((aeval (compression A K) q (⟨x, hxK⟩ : K) : K) : E) = aeval A q x :=
    compression.aeval_apply_of_forall_pow_mem A K q hpow
  have hAK := compression.isSymmetricBoundedBy A K hA
  have h2 := hAK.isSymmetric.energyNorm_aeval_apply_le (hAK.isSymmetricCoercive ha)
    (C := sSup ((fun t => |p.eval t|) '' Set.Icc a b)) q
    (fun _ hμ => norm_eval_map_le_sSup hAK p hμ) (⟨x, hxK⟩ : K)
  rw [compression.energyNorm_apply A K, compression.energyNorm_apply A K, h1] at h2
  exact h2

end LinearMap.IsSymmetricBoundedBy
