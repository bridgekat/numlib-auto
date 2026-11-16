/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.SVD
import Numlib.Topology.Algebra.Polynomial
import Numlib.Topology.Separation.Regular

/-!
# Pseudospectra

Let $A$ be a bounded operator on a normed space $E$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$,
and let $\varepsilon$ be real. The $\varepsilon$-pseudospectrum of $A$ is the set of scalars $z$ for
which some unit vector $w$ is an eigenvector to within $\varepsilon$, that is,
$\|Aw - zw\| < \varepsilon$. The closed $\varepsilon$-pseudospectrum $\Lambda_\varepsilon(A)$ uses
$\|Aw - zw\| \le \varepsilon$ instead. The open form is the definition of [saad2011numerical],
Definition 3.3, and of L. N. Trefethen and M. Embree, *Spectra and Pseudospectra* (2005); the closed
form is the definition of [golub2013matrix], (7.9.5), whose theorems are about it. In finite
dimension $\Lambda_\varepsilon(A)$ is the intersection of the open pseudospectra of larger radius,
so "the distinction has no impact in the matrix case", as [golub2013matrix], §7.9.1, says. This
module proves the standard characterizations and properties of pseudospectra, following
[golub2013matrix], §7.9, and the matrix examples of [golub2013matrix], §7.9.4.

Write $s(z) = \inf_{\|w\| = 1} \|Aw - zw\|$ for the least residual at $z$; for a matrix it is the
least singular value $\sigma_{\min}(zI - A)$. If $E$ is finite-dimensional and nonzero,
$z \in \Lambda_\varepsilon(A)$ holds exactly when $s(z) \le \varepsilon$, exactly when $z$ is an
eigenvalue or $\|(zI - A)^{-1}\| \ge 1/\varepsilon$ (for $\varepsilon > 0$), and, on an inner
product space, exactly when $z$ is an eigenvalue of $A + B$ for some $B$ with
$\|B\| \le \varepsilon$. Moreover $\Lambda_0(A)$ is the spectrum $\sigma(A)$,
$\Lambda_\varepsilon(A)$ is compact, it transforms affinely under $A \mapsto \alpha I + \beta A$,
and each of its connected components contains an eigenvalue. The pseudospectral abscissa and radius
are the largest real part and the largest modulus of a point of $\Lambda_\varepsilon(A)$, and
bounded powers $\|A^k\| \le M$ force $(\rho_\varepsilon(A) - 1)/\varepsilon \le M$.

## Main definitions

* `ContinuousLinearMap.pseudospectrum`: the open $\varepsilon$-pseudospectrum $\{z : \|Aw - zw\| <
  \varepsilon \text{ for some unit } w\}$.
* `ContinuousLinearMap.closedPseudospectrum`: the closed $\varepsilon$-pseudospectrum
  $\Lambda_\varepsilon(A) = \{z : \|Aw - zw\| \le \varepsilon \text{ for some unit } w\}$.
* `ContinuousLinearMap.pseudospectralAbscissa`: $\alpha_\varepsilon(A) = \sup \{\operatorname{Re} z
  : z \in \Lambda_\varepsilon(A)\}$, for a complex operator ([golub2013matrix], (7.9.8)).
* `ContinuousLinearMap.pseudospectralRadius`: $\rho_\varepsilon(A) = \sup \{|z| : z \in
  \Lambda_\varepsilon(A)\}$, for a complex operator ([golub2013matrix], (7.9.9)).
* `Matrix.pseudospectralAbscissa` and `Matrix.pseudospectralRadius`: the same quantities for a
  complex square matrix.

## Main results

* `ContinuousLinearMap.mem_closedPseudospectrum_iff_iInf`: if $E$ is finite-dimensional and nonzero,
  $z \in \Lambda_\varepsilon(A)$ if and only if $s(z) \le \varepsilon$ ([golub2013matrix], (7.9.5)).
* `ContinuousLinearMap.mem_closedPseudospectrum_iff_resolvent`: in finite dimension and for
  $\varepsilon > 0$, $z \in \Lambda_\varepsilon(A)$ if and only if $z \in \sigma(A)$ or
  $\|(zI - A)^{-1}\| \ge 1/\varepsilon$ ([golub2013matrix], (7.9.6)).
* `ContinuousLinearMap.mem_closedPseudospectrum_iff_exists_mem_spectrum_add`: on a
  finite-dimensional inner product space, $z \in \Lambda_\varepsilon(A)$ if and only if
  $z \in \sigma(A + B)$ for some $B$ with $\|B\| \le \varepsilon$ ([golub2013matrix], (7.9.7)).
* `ContinuousLinearMap.mem_pseudospectrum_iff`: on an inner product space, $z$ lies in the open
  $\varepsilon$-pseudospectrum if and only if $z$ is an eigenvalue of $A - B$ for some $B$ with
  $\|B\| < \varepsilon$ ([saad2011numerical], Proposition 3.7).
* `ContinuousLinearMap.closedPseudospectrum_zero`: in finite dimension, $\Lambda_0(A) = \sigma(A)$.
* `ContinuousLinearMap.closedPseudospectrum_eq_iInter_pseudospectrum`: in finite dimension,
  $\Lambda_\varepsilon(A)$ is the intersection of the open $\delta$-pseudospectra for
  $\delta > \varepsilon$.
* `ContinuousLinearMap.isCompact_closedPseudospectrum`: in finite dimension,
  $\Lambda_\varepsilon(A)$ is compact.
* `ContinuousLinearMap.closedPseudospectrum_smul_add`: for $\beta \neq 0$, $\Lambda_{\varepsilon
  |\beta|}(\alpha I + \beta A) = \alpha + \beta \Lambda_\varepsilon(A)$ ([golub2013matrix], Theorem
  7.9.1).
* `ContinuousLinearMap.mem_closedPseudospectrum_adjoint_iff`: on a finite-dimensional inner product
  space, $z \in \Lambda_\varepsilon(A^*)$ if and only if $\bar z \in \Lambda_\varepsilon(A)$.
* `ContinuousLinearMap.le_infDist_closedPseudospectrum`: every $z_0$ has distance at least
  $s(z_0) - \varepsilon$ from a nonempty $\Lambda_\varepsilon(A)$ ([golub2013matrix], Theorem
  7.9.8).
* `ContinuousLinearMap.closedPseudospectrum_subset_of_intertwine`: an isometric intertwiner carries
  pseudospectra into pseudospectra.
* `ContinuousLinearMap.closedPseudospectrum_units_conj_subset`: $\Lambda_\varepsilon(X^{-1} A X)
  \subseteq \Lambda_{\varepsilon \|X\| \|X^{-1}\|}(A)$ ([golub2013matrix], Theorem 7.9.2).
* `ContinuousLinearMap.pseudospectralRadius_sub_one_div_le_norm_pow`: if $E$ is finite-dimensional
  and nonzero and $\|A^k\| \le M$ for all $k$, then $(\rho_\varepsilon(A) - 1)/\varepsilon \le M$
  for every $\varepsilon > 0$ ([golub2013matrix], (7.9.11)).
* `ContinuousLinearMap.exists_mem_spectrum_mem_connectedComponentIn`: in finite dimension over
  $\mathbb{C}$, every connected component of $\Lambda_\varepsilon(A)$ contains an eigenvalue of $A$
  ([golub2013matrix], §7.9.3).
* `Matrix.closedPseudospectrum_conj_subset`: $\Lambda_\varepsilon(X^{-1} A X) \subseteq
  \Lambda_{\varepsilon \kappa_2(X)}(A)$ ([golub2013matrix], Theorem 7.9.2).
* `Matrix.closedPseudospectrum_unitary_conj`: $\Lambda_\varepsilon(U^H A U) =
  \Lambda_\varepsilon(A)$ for a unitary $U$ ([golub2013matrix], Corollary 7.9.3).
* `Matrix.closedPseudospectrum_diagonal`: the closed pseudospectrum of a diagonal matrix is the
  union of the closed discs of radius $\varepsilon$ about its diagonal entries ([golub2013matrix],
  Theorem 7.9.4).
* `Matrix.closedPseudospectrum_of_isStarNormal`: the closed pseudospectrum of a normal complex
  matrix is the union of the closed discs of radius $\varepsilon$ about its eigenvalues
  ([golub2013matrix], Corollary 7.9.5).
* `Matrix.closedPseudospectrum_fromBlocks_zero₂₁_supset`: for a block upper triangular $T$,
  $\Lambda_\varepsilon(T_{11}) \cup \Lambda_\varepsilon(T_{22}) \subseteq \Lambda_\varepsilon(T)$
  ([golub2013matrix], Theorem 7.9.6).
* `Matrix.closedPseudospectrum_fromBlocks_diagonal`:
  $\Lambda_\varepsilon(\operatorname{diag}(T_{11}, T_{22})) = \Lambda_\varepsilon(T_{11}) \cup
  \Lambda_\varepsilon(T_{22})$ ([golub2013matrix], Corollary 7.9.7).

## Proof outline

The bound on the pseudospectral radius comes from the Neumann series of the resolvent. The theorem
on connected components is proved by continuity of roots, not by the maximum modulus principle for
the resolvent. A component that misses the spectrum would split $\Lambda_\varepsilon(A)$ into two
disjoint compact parts. Take $B$ with $\|B\| \le \varepsilon$ and $z \in \sigma(A + B)$, by the
rank-one construction `ContinuousLinearMap.exists_hasEigenvalue_add_of_norm_sub_smul_le`, which
works in a normed space. Along $t \mapsto A + tB$ the number of eigenvalues in the part that
contains $z$ would have to jump (`Polynomial.countRootsIn_eq_of_preconnected`).

## Implementation notes

* Both pseudospectra are defined by approximate eigenvectors, not by the norm of the resolvent. So
  no convention for the resolvent on the spectrum is needed, and the equivalences with the other
  definitions are theorems.
* A square matrix $A$ over $\mathbb{K}$ is read through its Euclidean operator
  `Matrix.toEuclideanCLM A`, whose norm is the spectral norm. The matrix pseudospectral abscissa and
  radius are abbreviations for those of this operator.
* The pseudospectral abscissa and radius are defined only for complex operators. They are suprema in
  $\mathbb{R}$, with the value $0$ for an empty or unbounded set. On a nonzero finite-dimensional
  space and for $\varepsilon \ge 0$ they are maxima
  (`ContinuousLinearMap.exists_eq_pseudospectralAbscissa_radius`).
-/

open Metric Set

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]

section Normed

variable [NormedSpace 𝕜 E] {ε ε₁ ε₂ : ℝ} {A : E →L[𝕜] E} {z : 𝕜}

/-- The **$\varepsilon$-pseudospectrum** of a bounded operator $A$ on a normed space $E$: the set of
scalars $z$ for which some unit vector is an eigenvector to within $\varepsilon$, $$\{z \in
\mathbb{K} : \|Aw - zw\| < \varepsilon \text{ for some } w \in E \text{ with } \|w\| = 1\}.$$
This is Definition 3.3 of [saad2011numerical], in the form of its (3.55).

The source defines the pseudospectrum by the resolvent, $\|(A - zI)^{-1}\| > \varepsilon^{-1}$,
with the convention that the norm of the resolvent is infinite on the spectrum. The form here
needs no such convention, because an exact eigenvector has residual $0$, and it is the form that
the perturbation statements use. `ContinuousLinearMap.mem_pseudospectrum_iff` identifies it with
the backward-error form, and `ContinuousLinearMap.closedPseudospectrum` is the closed
counterpart. -/
def pseudospectrum (ε : ℝ) (A : E →L[𝕜] E) : Set 𝕜 :=
  {z | ∃ w : E, ‖w‖ = 1 ∧ ‖A w - z • w‖ < ε}

/-- The **closed $\varepsilon$-pseudospectrum** $\Lambda_\varepsilon(A)$ of a bounded operator $A$
on a normed space $E$: the set of scalars $z$ for which some unit vector has a residual of at
most $\varepsilon$, $$\Lambda_\varepsilon(A) = \{z \in \mathbb{K} : \|Aw - zw\| \le \varepsilon
\text{ for some } w \in E \text{ with } \|w\| = 1\}.$$ This is the definition (7.9.5) of
[golub2013matrix]. -/
def closedPseudospectrum (ε : ℝ) (A : E →L[𝕜] E) : Set 𝕜 :=
  {z | ∃ w : E, ‖w‖ = 1 ∧ ‖A w - z • w‖ ≤ ε}

/-- A scalar $z$ lies in the open $\varepsilon$-pseudospectrum of $A$ if and only if
$\|Aw - zw\| < \varepsilon$ for some unit vector $w$. -/
theorem mem_pseudospectrum :
    z ∈ pseudospectrum ε A ↔ ∃ w : E, ‖w‖ = 1 ∧ ‖A w - z • w‖ < ε := Iff.rfl

/-- A scalar $z$ lies in $\Lambda_\varepsilon(A)$ if and only if $\|Aw - zw\| \le \varepsilon$ for
some unit vector $w$. -/
theorem mem_closedPseudospectrum :
    z ∈ closedPseudospectrum ε A ↔ ∃ w : E, ‖w‖ = 1 ∧ ‖A w - z • w‖ ≤ ε := Iff.rfl

/-- The open $\varepsilon$-pseudospectrum of $A$ is contained in $\Lambda_\varepsilon(A)$. -/
theorem pseudospectrum_subset_closedPseudospectrum :
    pseudospectrum ε A ⊆ closedPseudospectrum ε A :=
  fun _ ⟨w, hw, h⟩ => ⟨w, hw, h.le⟩

/-- If $\varepsilon_1 < \varepsilon_2$, then $\Lambda_{\varepsilon_1}(A)$ is contained in the open
$\varepsilon_2$-pseudospectrum of $A$. -/
theorem closedPseudospectrum_subset_pseudospectrum (h : ε₁ < ε₂) :
    closedPseudospectrum ε₁ A ⊆ pseudospectrum ε₂ A :=
  fun _ ⟨w, hw, h'⟩ => ⟨w, hw, h'.trans_lt h⟩

/-- The open pseudospectra increase with the radius: if $\varepsilon_1 \le \varepsilon_2$, then the
open $\varepsilon_1$-pseudospectrum of $A$ is contained in the open
$\varepsilon_2$-pseudospectrum. -/
theorem pseudospectrum_mono (h : ε₁ ≤ ε₂) : pseudospectrum ε₁ A ⊆ pseudospectrum ε₂ A :=
  fun _ ⟨w, hw, h'⟩ => ⟨w, hw, h'.trans_le h⟩

/-- The closed pseudospectra increase with the radius: if $\varepsilon_1 \le \varepsilon_2$, then
$\Lambda_{\varepsilon_1}(A) \subseteq \Lambda_{\varepsilon_2}(A)$. This is stated in
[golub2013matrix], §7.9.3. -/
theorem closedPseudospectrum_mono (h : ε₁ ≤ ε₂) :
    closedPseudospectrum ε₁ A ⊆ closedPseudospectrum ε₂ A :=
  fun _ ⟨w, hw, h'⟩ => ⟨w, hw, h'.trans h⟩

/-- On the zero space there is no unit vector, so $\Lambda_\varepsilon(A)$ is empty for every
$\varepsilon$. -/
theorem closedPseudospectrum_eq_empty [Subsingleton E] : closedPseudospectrum ε A = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨w, hw, _⟩ => by
    rw [Subsingleton.elim w 0, norm_zero] at hw
    exact zero_ne_one hw

/-- If $z$ is an eigenvalue of $A$, then $Aw = zw$ for some unit vector $w$. -/
private theorem exists_norm_eq_one_apply_eq_smul
    (hz : Module.End.HasEigenvalue (A : E →ₗ[𝕜] E) z) : ∃ w : E, ‖w‖ = 1 ∧ A w = z • w := by
  obtain ⟨w, hw, hw0⟩ := hz.exists_hasEigenvector
  have hval : A w = z • w := by simpa using Module.End.mem_eigenspace_iff.1 hw
  refine ⟨(‖w‖ : 𝕜)⁻¹ • w, ?_, ?_⟩
  · exact norm_smul_inv_norm hw0
  · rw [map_smul, smul_comm z, hval]

/-- Let $\varepsilon > 0$. Every eigenvalue of $A$ lies in the open $\varepsilon$-pseudospectrum of
$A$.

An exact eigenvector has residual $0$. This is the inclusion
$\sigma(A) \subseteq \Lambda_\varepsilon(A)$, and it is the reason why the residual form of the
definition needs no convention for the norm of the resolvent on the spectrum. -/
theorem mem_pseudospectrum_of_hasEigenvalue (hε : 0 < ε)
    (hz : Module.End.HasEigenvalue (A : E →ₗ[𝕜] E) z) : z ∈ pseudospectrum ε A := by
  obtain ⟨w, hw, hAw⟩ := exists_norm_eq_one_apply_eq_smul hz
  exact ⟨w, hw, by rwa [hAw, sub_self, norm_zero]⟩

/-- Let $\varepsilon \ge 0$. Every eigenvalue of $A$ lies in $\Lambda_\varepsilon(A)$. -/
theorem mem_closedPseudospectrum_of_hasEigenvalue (hε : 0 ≤ ε)
    (hz : Module.End.HasEigenvalue (A : E →ₗ[𝕜] E) z) : z ∈ closedPseudospectrum ε A := by
  obtain ⟨w, hw, hAw⟩ := exists_norm_eq_one_apply_eq_smul hz
  exact ⟨w, hw, by rwa [hAw, sub_self, norm_zero]⟩

private theorem bddBelow_range_norm_sub_smul (A : E →L[𝕜] E) (z : 𝕜) :
    BddBelow (range fun w : {w : E // ‖w‖ = 1} => ‖A w - z • (w : E)‖) :=
  ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩

/-- The least residual $s(z) = \inf_{\|w\| = 1} \|Aw - zw\|$ is a lower bound by homogeneity: for
every $x \in E$, $$s(z) \, \|x\| \le \|Ax - zx\|.$$ For a matrix, $s(z)$ is the least singular
value $\sigma_{\min}(zI - A)$. -/
theorem iInf_norm_sub_smul_mul_norm_le (A : E →L[𝕜] E) (z : 𝕜) (x : E) :
    (⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖) * ‖x‖ ≤ ‖A x - z • x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖((‖x‖⁻¹ : ℝ) : 𝕜) • x‖ = 1 := by rw [RCLike.ofReal_inv]; exact norm_smul_inv_norm hx
  have h := ciInf_le (bddBelow_range_norm_sub_smul A z) ⟨_, hu⟩
  simp only [map_smul, smul_comm z, ← smul_sub, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (inv_pos.mpr hn)] at h
  calc (⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖) * ‖x‖
      ≤ ‖x‖⁻¹ * ‖A x - z • x‖ * ‖x‖ := by gcongr
    _ = ‖A x - z • x‖ := by field_simp

/-- The least residual $s(z) = \inf_{\|w\| = 1} \|Aw - zw\|$ is $1$-Lipschitz in $z$:
$s(z) \le s(z') + |z - z'|$ for all scalars $z$ and $z'$. -/
theorem iInf_norm_sub_smul_le_add (A : E →L[𝕜] E) (z z' : 𝕜) :
    ⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖ ≤
      (⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z' • (w : E)‖) + ‖z - z'‖ := by
  rcases isEmpty_or_nonempty {w : E // ‖w‖ = 1} with h | h
  · rw [Real.iInf_of_isEmpty, Real.iInf_of_isEmpty, zero_add]; exact norm_nonneg _
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun w => ?_
  rw [sub_le_iff_le_add]
  calc ⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖ ≤ ‖A w - z • (w : E)‖ :=
        ciInf_le (bddBelow_range_norm_sub_smul A z) w
    _ = ‖(A w - z' • (w : E)) - (z - z') • (w : E)‖ := by rw [sub_smul]; congr 1; abel
    _ ≤ ‖A w - z' • (w : E)‖ + ‖(z - z') • (w : E)‖ := norm_sub_le _ _
    _ = ‖A w - z' • (w : E)‖ + ‖z - z'‖ := by rw [norm_smul, w.2, mul_one]

/-- Distance to the pseudospectrum. Let $\Lambda_\varepsilon(A)$ be nonempty, and let $z_0$ be a
scalar. Then the distance from $z_0$ to $\Lambda_\varepsilon(A)$ is at least
$s(z_0) - \varepsilon$, where $s(z_0) = \inf_{\|w\| = 1} \|Aw - z_0 w\|$ is the least residual,
the $\sigma_{\min}(z_0 I - A)$ of the source. This is Theorem 7.9.8 of [golub2013matrix].

For $z_0 \notin \sigma(A)$ the least residual is at least $1/\|(z_0 I - A)^{-1}\|$
(`ContinuousLinearMap.inv_norm_inverse_le_norm_sub_smul`), which is the form of the source. The
proof: for $z \in \Lambda_\varepsilon(A)$ with a unit vector $w$, $\|Aw - z_0 w\| \le \|Aw -
zw\| + |z - z_0| \le \varepsilon + |z - z_0|$. -/
theorem le_infDist_closedPseudospectrum (hne : (closedPseudospectrum ε A).Nonempty) (z₀ : 𝕜) :
    (⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z₀ • (w : E)‖) - ε ≤
      infDist z₀ (closedPseudospectrum ε A) := by
  rw [le_infDist hne]
  rintro z ⟨w, hw, hz⟩
  have h1 := ciInf_le (bddBelow_range_norm_sub_smul A z₀) ⟨w, hw⟩
  have h2 : ‖A w - z₀ • w‖ ≤ ‖A w - z • w‖ + ‖z - z₀‖ := by
    calc ‖A w - z₀ • w‖ = ‖(A w - z • w) + (z - z₀) • w‖ := by rw [sub_smul]; congr 1; abel
      _ ≤ ‖A w - z • w‖ + ‖(z - z₀) • w‖ := norm_add_le _ _
      _ = ‖A w - z • w‖ + ‖z - z₀‖ := by rw [norm_smul, hw, mul_one]
  rw [dist_comm, dist_eq_norm]
  simp only at h1
  linarith

/-- For all scalars $\alpha$, $\beta$, $z$ and every $w$, $(\alpha I + \beta A) w - (\alpha + \beta
z) w = \beta (Aw - zw)$. -/
private theorem smul_add_apply_sub (α β : 𝕜) (w : E) :
    (α • (1 : E →L[𝕜] E) + β • A) w - (α + β * z) • w = β • (A w - z • w) := by
  simp only [add_apply, smul_apply, one_apply_eq_self, add_smul, mul_smul, smul_sub]
  abel

/-- Affine transformation of the pseudospectrum. Let $\alpha$ and $\beta$ be scalars with
$\beta \neq 0$. Then $$\Lambda_{\varepsilon |\beta|}(\alpha I + \beta A) = \alpha + \beta
\Lambda_\varepsilon(A) = \{\alpha + \beta z : z \in \Lambda_\varepsilon(A)\}.$$ This is Theorem
7.9.1 of [golub2013matrix]. -/
theorem closedPseudospectrum_smul_add (α : 𝕜) {β : 𝕜} (hβ : β ≠ 0) :
    closedPseudospectrum (ε * ‖β‖) (α • 1 + β • A) =
      (fun z => α + β * z) '' closedPseudospectrum ε A := by
  have hβn : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  ext z'
  constructor
  · rintro ⟨w, hw, h⟩
    refine ⟨β⁻¹ * (z' - α), ⟨w, hw, ?_⟩, by field_simp; ring⟩
    have e : z' = α + β * (β⁻¹ * (z' - α)) := by field_simp; ring
    rw [e, smul_add_apply_sub, norm_smul] at h
    exact le_of_mul_le_mul_left (by linarith) hβn
  · rintro ⟨z, ⟨w, hw, h⟩, rfl⟩
    refine ⟨w, hw, ?_⟩
    rw [smul_add_apply_sub, norm_smul, mul_comm ε]
    exact mul_le_mul_of_nonneg_left h hβn.le

/-- The open form of `ContinuousLinearMap.closedPseudospectrum_smul_add`. Let $\beta \neq 0$. Then
the open $\varepsilon |\beta|$-pseudospectrum of $\alpha I + \beta A$ is the image
$\{\alpha + \beta z\}$ of the open $\varepsilon$-pseudospectrum of $A$. -/
theorem pseudospectrum_smul_add (α : 𝕜) {β : 𝕜} (hβ : β ≠ 0) :
    pseudospectrum (ε * ‖β‖) (α • 1 + β • A) =
      (fun z => α + β * z) '' pseudospectrum ε A := by
  have hβn : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  ext z'
  constructor
  · rintro ⟨w, hw, h⟩
    refine ⟨β⁻¹ * (z' - α), ⟨w, hw, ?_⟩, by field_simp; ring⟩
    have e : z' = α + β * (β⁻¹ * (z' - α)) := by field_simp; ring
    rw [e, smul_add_apply_sub, norm_smul] at h
    exact lt_of_mul_lt_mul_left (by linarith) hβn.le
  · rintro ⟨z, ⟨w, hw, h⟩, rfl⟩
    refine ⟨w, hw, ?_⟩
    rw [smul_add_apply_sub, norm_smul, mul_comm ε]
    exact mul_lt_mul_of_pos_left h hβn

/-- If $z \notin \sigma(A)$, then $zI - A$ is invertible. -/
private theorem isUnit_smul_one_sub (hz : z ∉ spectrum 𝕜 A) : IsUnit (z • 1 - A) := by
  rwa [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, not_not] at hz

/-- The resolvent bounds the residual from below. Let $z \notin \sigma(A)$. Then for every
$x \in E$, $$\|x\| \le \|(zI - A)^{-1}\| \, \|Ax - zx\|.$$
-/
theorem norm_le_norm_inverse_mul_norm_sub_smul (hz : z ∉ spectrum 𝕜 A) (x : E) :
    ‖x‖ ≤ ‖Ring.inverse (z • 1 - A)‖ * ‖A x - z • x‖ := by
  have h1 : Ring.inverse (z • 1 - A) * (z • 1 - A) = 1 :=
    Ring.inverse_mul_cancel _ (isUnit_smul_one_sub hz)
  calc ‖x‖ = ‖Ring.inverse (z • 1 - A) ((z • 1 - A) x)‖ := by
        rw [← mul_apply_eq_comp, h1, one_apply_eq_self]
    _ ≤ ‖Ring.inverse (z • 1 - A)‖ * ‖(z • 1 - A) x‖ := le_opNorm _ _
    _ = ‖Ring.inverse (z • 1 - A)‖ * ‖A x - z • x‖ := by
        rw [sub_apply, smul_apply, one_apply_eq_self, norm_sub_rev]

/-- Let $z \notin \sigma(A)$. Then every unit vector $w$ has residual
$\|Aw - zw\| \ge 1/\|(zI - A)^{-1}\|$.

So $1/\|(zI - A)^{-1}\| \le \sigma_{\min}(zI - A)$, which gives the form of the distance bound
of [golub2013matrix], Theorem 7.9.8. The inverse is `Ring.inverse`, and $1/0$ means $0$. -/
theorem inv_norm_inverse_le_norm_sub_smul (hz : z ∉ spectrum 𝕜 A) {w : E} (hw : ‖w‖ = 1) :
    ‖Ring.inverse (z • 1 - A)‖⁻¹ ≤ ‖A w - z • w‖ := by
  have h := norm_le_norm_inverse_mul_norm_sub_smul hz w
  rw [hw] at h
  have hpos : 0 < ‖Ring.inverse (z • 1 - A)‖ := by
    by_contra h0
    push Not at h0
    nlinarith [norm_nonneg (Ring.inverse (z • 1 - A)), norm_nonneg (A w - z • w)]
  rw [inv_le_iff_one_le_mul₀' hpos]
  exact h

end Normed

section FiniteDimensional

variable [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] {ε : ℝ} {A : E →L[𝕜] E} {z : 𝕜}

/-- Let $E$ be finite-dimensional and nonzero. Then the least residual is attained on the unit
sphere: there is a unit vector $w$ with $\|Aw - zw\| = \inf_{\|v\| = 1} \|Av - zv\|$. -/
theorem exists_norm_sub_smul_eq_iInf [Nontrivial E] (A : E →L[𝕜] E) (z : 𝕜) :
    ∃ w : E, ‖w‖ = 1 ∧ ‖A w - z • w‖ = ⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖ := by
  have := FiniteDimensional.proper_rclike 𝕜 E
  have hc : Continuous fun w : E => ‖A w - z • w‖ :=
    (A.continuous.sub (continuous_const.smul continuous_id)).norm
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hw₀ : ‖((‖x‖⁻¹ : ℝ) : 𝕜) • x‖ = 1 := by rw [RCLike.ofReal_inv]; exact norm_smul_inv_norm hx
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    ⟨_, mem_sphere_zero_iff_norm.mpr hw₀⟩ hc.continuousOn
  rw [mem_sphere_zero_iff_norm] at hw
  have : Nonempty {w : E // ‖w‖ = 1} := ⟨⟨w, hw⟩⟩
  refine ⟨w, hw, le_antisymm (le_ciInf fun v => hmin (mem_sphere_zero_iff_norm.mpr v.2))
    (ciInf_le (bddBelow_range_norm_sub_smul A z) ⟨w, hw⟩)⟩

/-- Let $E$ be finite-dimensional and nonzero. Then $z \in \Lambda_\varepsilon(A)$ if and only if
the least residual is at most $\varepsilon$: $$\inf_{\|w\| = 1} \|Aw - zw\| \le \varepsilon.$$
The least residual is the $\sigma_{\min}(zI - A)$ of the source. This is (7.9.5) of
[golub2013matrix]. -/
theorem mem_closedPseudospectrum_iff_iInf [Nontrivial E] :
    z ∈ closedPseudospectrum ε A ↔ ⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖ ≤ ε := by
  constructor
  · rintro ⟨w, hw, h⟩
    exact (ciInf_le (bddBelow_range_norm_sub_smul A z) ⟨w, hw⟩).trans h
  · intro h
    obtain ⟨w, hw, heq⟩ := exists_norm_sub_smul_eq_iInf A z
    exact ⟨w, hw, heq ▸ h⟩

/-- In finite dimension, $z$ is an eigenvalue of $A$ as a linear map if and only if $z$ lies in the
spectrum of $A$. -/
private theorem hasEigenvalue_iff_mem_spectrum' :
    Module.End.HasEigenvalue (A : E →ₗ[𝕜] E) z ↔ z ∈ spectrum 𝕜 A := by
  have := FiniteDimensional.complete 𝕜 E
  rw [spectrum_eq, Module.End.hasEigenvalue_iff_mem_spectrum]

/-- Let $E$ be finite-dimensional and $\varepsilon \ge 0$. Then the spectrum of $A$ lies in
$\Lambda_\varepsilon(A)$. -/
theorem spectrum_subset_closedPseudospectrum (hε : 0 ≤ ε) :
    spectrum 𝕜 A ⊆ closedPseudospectrum ε A := fun _ hz =>
  mem_closedPseudospectrum_of_hasEigenvalue hε (hasEigenvalue_iff_mem_spectrum'.mpr hz)

/-- Let $E$ be finite-dimensional and $\varepsilon > 0$. Then the spectrum of $A$ lies in the open
$\varepsilon$-pseudospectrum of $A$. -/
theorem spectrum_subset_pseudospectrum (hε : 0 < ε) : spectrum 𝕜 A ⊆ pseudospectrum ε A :=
  fun _ hz => mem_pseudospectrum_of_hasEigenvalue hε (hasEigenvalue_iff_mem_spectrum'.mpr hz)

/-- Let $E$ be finite-dimensional. Then the closed pseudospectrum of radius $0$ is the spectrum:
$\Lambda_0(A) = \sigma(A)$. This is stated in [golub2013matrix], §7.9.1. -/
theorem closedPseudospectrum_zero : closedPseudospectrum 0 A = spectrum 𝕜 A := by
  refine Subset.antisymm ?_ (spectrum_subset_closedPseudospectrum le_rfl)
  rintro z ⟨w, hw, h⟩
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hAw : A w = z • w := sub_eq_zero.mp (norm_le_zero_iff.mp h)
  exact hasEigenvalue_iff_mem_spectrum'.mp (Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr hAw, hw0⟩)

/-- Let $E$ be finite-dimensional. Then the closed pseudospectrum is the intersection of the open
pseudospectra of larger radius: $$\Lambda_\varepsilon(A) = \bigcap_{\delta > \varepsilon} \{z :
\|Aw - zw\| < \delta \text{ for some unit } w\}.$$ This is the remark of [golub2013matrix],
§7.9.1, that the strict and the non-strict definitions agree for matrices. -/
theorem closedPseudospectrum_eq_iInter_pseudospectrum :
    closedPseudospectrum ε A = ⋂ δ > ε, pseudospectrum δ A := by
  cases subsingleton_or_nontrivial E
  · rw [closedPseudospectrum_eq_empty]
    refine (eq_empty_of_forall_notMem fun z hz => ?_).symm
    obtain ⟨w, hw, -⟩ := mem_iInter₂.mp hz (ε + 1) (by linarith)
    rw [Subsingleton.elim w 0, norm_zero] at hw
    exact zero_ne_one hw
  refine Subset.antisymm (fun z hz => mem_iInter₂.mpr fun δ hδ =>
    closedPseudospectrum_subset_pseudospectrum hδ hz) fun z hz => ?_
  rw [mem_closedPseudospectrum_iff_iInf]
  by_contra h
  push Not at h
  obtain ⟨w, hw, hlt⟩ := mem_iInter₂.mp hz _ h
  exact (ciInf_le (bddBelow_range_norm_sub_smul A z) ⟨w, hw⟩).not_gt hlt

/-- Let $E$ be finite-dimensional and $\varepsilon > 0$. Then $z \in \Lambda_\varepsilon(A)$ if and
only if $z$ is an eigenvalue of $A$ or the resolvent is large: $$z \in \sigma(A) \quad \text{or}
\quad \|(zI - A)^{-1}\| \ge 1/\varepsilon.$$ This is (7.9.6) of [golub2013matrix].

At $\varepsilon = 0$ the resolvent form degenerates, because $1/0 = 0$ in Lean;
`ContinuousLinearMap.closedPseudospectrum_zero` is the statement for that case. The inverse is
`Ring.inverse`. -/
theorem mem_closedPseudospectrum_iff_resolvent (hε : 0 < ε) :
    z ∈ closedPseudospectrum ε A ↔
      z ∈ spectrum 𝕜 A ∨ 1 / ε ≤ ‖Ring.inverse (z • 1 - A)‖ := by
  constructor
  · rintro ⟨w, hw, h⟩
    by_cases hz : z ∈ spectrum 𝕜 A
    · exact Or.inl hz
    · right
      have := norm_le_norm_inverse_mul_norm_sub_smul hz w
      rw [hw] at this
      rw [div_le_iff₀ hε]
      exact this.trans (mul_le_mul_of_nonneg_left h (norm_nonneg _))
  · rintro (hz | h)
    · exact spectrum_subset_closedPseudospectrum hε.le hz
    by_cases hz : z ∈ spectrum 𝕜 A
    · exact spectrum_subset_closedPseudospectrum hε.le hz
    cases subsingleton_or_nontrivial E
    · have h0 : Ring.inverse (z • 1 - A) = 0 := Subsingleton.elim _ _
      rw [h0, norm_zero] at h
      exact absurd h (not_le.mpr (by positivity))
    rw [mem_closedPseudospectrum_iff_iInf]
    set m := ⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖ with hm
    by_contra hlt
    push Not at hlt
    have hm0 : 0 < m := hε.trans hlt
    -- `‖(z I - A)⁻¹ v‖ ≤ ‖v‖ / m`, so `‖(z I - A)⁻¹‖ ≤ 1/m < 1/ε`
    have hR : ‖Ring.inverse (z • 1 - A)‖ ≤ 1 / m := by
      refine opNorm_le_bound _ (by positivity) fun v => ?_
      have h1 : (z • 1 - A) * Ring.inverse (z • 1 - A) = 1 :=
        Ring.mul_inverse_cancel _ (isUnit_smul_one_sub hz)
      have h2 := iInf_norm_sub_smul_mul_norm_le A z (Ring.inverse (z • 1 - A) v)
      have h3 : A (Ring.inverse (z • 1 - A) v) - z • Ring.inverse (z • 1 - A) v = -v := by
        have := congrArg (fun T : E →L[𝕜] E => T v) h1
        simp only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] at this
        rw [← neg_sub, this]
      rw [← hm, h3, norm_neg] at h2
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm0, mul_comm]
      exact h2
    have : 1 / m < 1 / ε := one_div_lt_one_div_of_lt hε hlt
    linarith

/-- Let $E$ be finite-dimensional. Then $\Lambda_\varepsilon(A)$ is compact for every $\varepsilon$.

It is bounded by $\|A\| + \varepsilon$, since $|z| = \|zw\| \le \|Aw\| + \varepsilon$ for a unit
vector $w$, and it is closed, since the least residual is continuous in $z$. -/
theorem isCompact_closedPseudospectrum (ε : ℝ) (A : E →L[𝕜] E) :
    IsCompact (closedPseudospectrum ε A) := by
  cases subsingleton_or_nontrivial E
  · rw [closedPseudospectrum_eq_empty]; exact isCompact_empty
  have hbdd : closedPseudospectrum ε A ⊆ closedBall 0 (‖A‖ + ε) := by
    rintro z ⟨w, hw, h⟩
    rw [mem_closedBall_zero_iff]
    calc ‖z‖ = ‖z • w‖ := by rw [norm_smul, hw, mul_one]
      _ = ‖A w - (A w - z • w)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖A w‖ + ‖A w - z • w‖ := norm_sub_le _ _
      _ ≤ ‖A‖ + ε := by
          gcongr
          simpa [hw] using A.le_opNorm w
  have hcont : Continuous fun z : 𝕜 => ⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖ := by
    refine (LipschitzWith.of_dist_le_mul fun z z' => ?_).continuous (K := 1)
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm, abs_sub_le_iff]
    exact ⟨sub_le_iff_le_add'.mpr (iInf_norm_sub_smul_le_add A z z'),
      sub_le_iff_le_add'.mpr ((iInf_norm_sub_smul_le_add A z' z).trans_eq
        (by rw [norm_sub_rev]))⟩
  have hclosed : IsClosed (closedPseudospectrum ε A) := by
    have : closedPseudospectrum ε A =
        {z | ⨅ w : {w : E // ‖w‖ = 1}, ‖A w - z • (w : E)‖ ≤ ε} := by
      ext z; exact mem_closedPseudospectrum_iff_iInf
    rw [this]
    exact isClosed_le hcont continuous_const
  exact isCompact_of_isClosed_isBounded hclosed (isBounded_closedBall.subset hbdd)

end FiniteDimensional

section InnerProduct

variable [InnerProductSpace 𝕜 E] {ε : ℝ}

/-- The **backward-error characterization of the pseudospectrum**. Let $E$ be an inner product
space. Then $z$ lies in the open $\varepsilon$-pseudospectrum of $A$ if and only if $z$ is an
eigenvalue of $A - B$ for some bounded operator $B$ with $\|B\| < \varepsilon$. This is
[saad2011numerical], Proposition 3.7, (iv) $\Leftrightarrow$ (v), with a strict inequality in
(v).

The source states (v) with $\|B\| \le \varepsilon$, but its own proof of (v) $\Rightarrow$ (iv)
needs the strict inequality, and with $\le$ the equivalence is false. For $A = 0$, every $z$
with $|z| = \varepsilon$ satisfies the right-hand side with the perturbation $B = -zI$ of norm
exactly $\varepsilon$, but no such $z$ satisfies the left-hand side, since
$\|0 - zw\| = \varepsilon$ for every unit vector $w$. The closed pseudospectrum has the
non-strict form, `ContinuousLinearMap.mem_closedPseudospectrum_iff_exists_mem_spectrum_add`. In
the forward direction the perturbation is the rank-one operator $(Aw - zw) w^H$, built from the
residual of the approximate eigenvector; in the backward direction an eigenvector of $A - B$ has
residual $Bw$ for $A$. -/
theorem mem_pseudospectrum_iff (A : E →L[𝕜] E) (z : 𝕜) :
    z ∈ pseudospectrum ε A ↔
      ∃ B : E →L[𝕜] E, ‖B‖ < ε ∧ Module.End.HasEigenvalue ((A - B : E →L[𝕜] E) :
        E →ₗ[𝕜] E) z := by
  constructor
  · rintro ⟨w, hw, hlt⟩
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    refine ⟨InnerProductSpace.rankOne 𝕜 (A w - z • w) w, ?_, ?_⟩
    · rwa [InnerProductSpace.norm_rankOne, hw, mul_one]
    · have huu : (inner 𝕜 w w : 𝕜) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hw]; norm_num
      refine Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 ?_, hw0⟩
      simp only [ContinuousLinearMap.coe_coe, sub_apply, InnerProductSpace.rankOne_apply, huu,
        one_smul, sub_sub_cancel]
  · rintro ⟨B, hB, hz⟩
    obtain ⟨w, hw, hAw⟩ := exists_norm_eq_one_apply_eq_smul hz
    refine ⟨w, hw, ?_⟩
    have hres : A w - z • w = B w := by
      rw [← hAw, sub_apply]; abel
    rw [hres]
    calc ‖B w‖ ≤ ‖B‖ * ‖w‖ := B.le_opNorm w
      _ = ‖B‖ := by rw [hw, mul_one]
      _ < ε := hB

/-- Let $E$ be a finite-dimensional inner product space. Then $z \in \Lambda_\varepsilon(A)$ if and
only if $z$ is an eigenvalue of $A + B$ for some operator $B$ with $\|B\| \le \varepsilon$: $$z
\in \Lambda_\varepsilon(A) \iff z \in \sigma(A + B) \text{ for some } B \text{ with } \|B\| \le
\varepsilon.$$ This is (7.9.7) of [golub2013matrix].

In the forward direction $B = -(Aw - zw) w^H$ for a unit vector $w$ with a small residual. In
the backward direction a unit eigenvector $w$ of $A + B$ has
$\|Aw - zw\| = \|Bw\| \le \varepsilon$. -/
theorem mem_closedPseudospectrum_iff_exists_mem_spectrum_add [FiniteDimensional 𝕜 E]
    (A : E →L[𝕜] E) (z : 𝕜) :
    z ∈ closedPseudospectrum ε A ↔ ∃ B : E →L[𝕜] E, ‖B‖ ≤ ε ∧ z ∈ spectrum 𝕜 (A + B) := by
  constructor
  · rintro ⟨w, hw, hle⟩
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    refine ⟨-InnerProductSpace.rankOne 𝕜 (A w - z • w) w, ?_, ?_⟩
    · rwa [norm_neg, InnerProductSpace.norm_rankOne, hw, mul_one]
    · have huu : (inner 𝕜 w w : 𝕜) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hw]; norm_num
      refine hasEigenvalue_iff_mem_spectrum'.mp (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 ?_, hw0⟩)
      simp only [ContinuousLinearMap.coe_coe, add_apply, neg_apply,
        InnerProductSpace.rankOne_apply, huu, one_smul]
      abel
  · rintro ⟨B, hB, hz⟩
    obtain ⟨w, hw, hAw⟩ := exists_norm_eq_one_apply_eq_smul
      (hasEigenvalue_iff_mem_spectrum'.mpr hz)
    refine ⟨w, hw, ?_⟩
    have hres : A w - z • w = -B w := by
      rw [← hAw, add_apply]; abel
    rw [hres, norm_neg]
    calc ‖B w‖ ≤ ‖B‖ * ‖w‖ := B.le_opNorm w
      _ = ‖B‖ := by rw [hw, mul_one]
      _ ≤ ε := hB

/-- A lower bound passes to the adjoint. Let $E$ be a finite-dimensional (hence complete) inner
product space, let $T$ be an operator on $E$, and let $c$ be real with $c \|x\| \le \|Tx\|$ for
every $x$. Then $c \|y\| \le \|T^* y\|$ for every $y$.

For $c > 0$, $T$ is injective and hence onto. Writing $y = Tx$, $\|y\|^2 = \operatorname{Re}
\langle T^* y, x \rangle \le \|T^* y\| \|x\| \le \|T^* y\| \|y\|/c$. -/
theorem le_norm_adjoint_apply_of_le [FiniteDimensional 𝕜 E] [CompleteSpace E] {T : E →L[𝕜] E}
    {c : ℝ} (h : ∀ x, c * ‖x‖ ≤ ‖T x‖) (y : E) : c * ‖y‖ ≤ ‖adjoint T y‖ := by
  rcases le_or_gt c 0 with hc | hc
  · exact (mul_nonpos_of_nonpos_of_nonneg hc (norm_nonneg _)).trans (norm_nonneg _)
  have hinj : Function.Injective (T : E →ₗ[𝕜] E) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have := h x
    rw [coe_coe] at hx
    rw [hx, norm_zero] at this
    exact norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right this hc) (norm_nonneg _))
  obtain ⟨x, rfl⟩ := LinearMap.injective_iff_surjective.mp hinj y
  rw [coe_coe]
  have hcs : ‖T x‖ ^ 2 ≤ ‖adjoint T (T x)‖ * ‖x‖ := by
    rw [← @inner_self_eq_norm_sq 𝕜, ← adjoint_inner_left]
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hx := h x
  rcases (norm_nonneg (T x)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  have : c * ‖T x‖ ^ 2 ≤ ‖adjoint T (T x)‖ * ‖T x‖ := by
    calc c * ‖T x‖ ^ 2 ≤ c * (‖adjoint T (T x)‖ * ‖x‖) := by gcongr
      _ = ‖adjoint T (T x)‖ * (c * ‖x‖) := by ring
      _ ≤ ‖adjoint T (T x)‖ * ‖T x‖ := by gcongr
  nlinarith

/-- Let $E$ be a finite-dimensional (hence complete) inner product space. Then
$z \in \Lambda_\varepsilon(A^*)$ if and only if $\bar z \in \Lambda_\varepsilon(A)$.

An operator and its adjoint have the same least value of $\|Tw\|$ on the unit sphere, by
`ContinuousLinearMap.le_norm_adjoint_apply_of_le` in both directions. -/
theorem mem_closedPseudospectrum_adjoint_iff [FiniteDimensional 𝕜 E] [CompleteSpace E]
    {A : E →L[𝕜] E} {z : 𝕜} :
    z ∈ closedPseudospectrum ε (adjoint A) ↔ star z ∈ closedPseudospectrum ε A := by
  cases subsingleton_or_nontrivial E
  · simp [closedPseudospectrum_eq_empty]
  -- the least residual of `T` bounds that of `T†`
  have key : ∀ (T : E →L[𝕜] E) (c : 𝕜),
      ⨅ w : {w : E // ‖w‖ = 1}, ‖T w - c • (w : E)‖ ≤
        ⨅ w : {w : E // ‖w‖ = 1}, ‖adjoint T w - star c • (w : E)‖ := by
    intro T c
    obtain ⟨w, hw, heq⟩ := exists_norm_sub_smul_eq_iInf (adjoint T) (star c)
    rw [← heq]
    have h := le_norm_adjoint_apply_of_le (T := T - c • 1)
      (c := ⨅ w : {w : E // ‖w‖ = 1}, ‖T w - c • (w : E)‖)
      (fun x => by
        have := iInf_norm_sub_smul_mul_norm_le T c x
        rwa [sub_apply, smul_apply, one_apply_eq_self]) w
    have h1 : adjoint (1 : E →L[𝕜] E) = 1 := by rw [← star_eq_adjoint, star_one]
    have hadj : adjoint (T - c • 1) w = adjoint T w - star c • w := by
      rw [map_sub, map_smulₛₗ, h1, sub_apply, smul_apply, one_apply_eq_self]
      rfl
    rw [hadj, hw, mul_one] at h
    exact h
  rw [mem_closedPseudospectrum_iff_iInf, mem_closedPseudospectrum_iff_iInf]
  constructor
  · intro h
    exact (key A (star z)).trans (by simpa using h)
  · intro h
    have := key (adjoint A) z
    rw [adjoint_adjoint] at this
    exact this.trans h

end InnerProduct

section Intertwine

variable [NormedSpace 𝕜 E] {ε : ℝ} {A : E →L[𝕜] E} {z : 𝕜}

/-- Outside the closed pseudospectrum every nonzero vector has a large residual: if
$z \notin \Lambda_\varepsilon(A)$ and $x \neq 0$, then $\varepsilon \|x\| < \|Ax - zx\|$. -/
theorem mul_norm_lt_norm_sub_smul_of_notMem (hz : z ∉ closedPseudospectrum ε A) {x : E}
    (hx : x ≠ 0) : ε * ‖x‖ < ‖A x - z • x‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖((‖x‖⁻¹ : ℝ) : 𝕜) • x‖ = 1 := by rw [RCLike.ofReal_inv]; exact norm_smul_inv_norm hx
  have h : ε < ‖A (((‖x‖⁻¹ : ℝ) : 𝕜) • x) - z • ((‖x‖⁻¹ : ℝ) : 𝕜) • x‖ :=
    not_le.mp fun h => hz ⟨_, hu, h⟩
  rw [map_smul, smul_comm z, ← smul_sub, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (inv_pos.mpr hn)] at h
  rwa [← lt_div_iff₀ hn, div_eq_inv_mul]

/-- Pseudospectra pass along isometric intertwiners. Let $F$ be a normed space, let $P$ be a bounded
operator on $F$, and let $J : F \to E$ be a linear isometry with $AJ = JP$. Then
$\Lambda_\varepsilon(P) \subseteq \Lambda_\varepsilon(A)$.

A unit vector $w$ with a small residual for $P$ gives the unit vector $Jw$ with the same
residual for $A$. This covers the restriction to an invariant subspace and unitary similarity. -/
theorem closedPseudospectrum_subset_of_intertwine {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {P : F →L[𝕜] F} {J : F →ₗ[𝕜] E} (hJ : ∀ w, ‖J w‖ = ‖w‖)
    (h : ∀ w, A (J w) = J (P w)) : closedPseudospectrum ε P ⊆ closedPseudospectrum ε A := by
  rintro z ⟨w, hw, hle⟩
  refine ⟨J w, by rw [hJ, hw], ?_⟩
  rwa [h, ← map_smul, ← map_sub, hJ]

/-- Let $X$ be an invertible bounded operator on $E$. Then $$\Lambda_\varepsilon(X^{-1} A X)
\subseteq \Lambda_{\varepsilon \|X\| \|X^{-1}\|}(A).$$ This is Theorem 7.9.2 of
[golub2013matrix].

From a unit vector $w$ with $\|(X^{-1} A X - zI) w\| \le \varepsilon$, the unit vector
$Xw/\|Xw\|$ has residual $\|X (X^{-1} A X - zI) w\|/\|Xw\| \le \|X\| \varepsilon \|X^{-1}\|$,
since $1 = \|X^{-1} X w\| \le \|X^{-1}\| \|Xw\|$. -/
theorem closedPseudospectrum_units_conj_subset (u : (E →L[𝕜] E)ˣ) (A : E →L[𝕜] E) (ε : ℝ) :
    closedPseudospectrum ε ((↑u⁻¹ : E →L[𝕜] E) * A * (u : E →L[𝕜] E)) ⊆
      closedPseudospectrum (ε * (‖(u : E →L[𝕜] E)‖ * ‖(↑u⁻¹ : E →L[𝕜] E)‖)) A := by
  rintro z ⟨w, hw, hle⟩
  set X : E →L[𝕜] E := (u : E →L[𝕜] E)
  set Y : E →L[𝕜] E := ↑u⁻¹
  have hXY : ∀ v, X (Y v) = v := fun v => by
    rw [← mul_apply_eq_comp, u.mul_inv, one_apply_eq_self]
  have hYX : ∀ v, Y (X v) = v := fun v => by
    rw [← mul_apply_eq_comp, u.inv_mul, one_apply_eq_self]
  have hXw : 1 ≤ ‖Y‖ * ‖X w‖ := by
    calc (1 : ℝ) = ‖Y (X w)‖ := by rw [hYX, hw]
      _ ≤ ‖Y‖ * ‖X w‖ := le_opNorm _ _
  have hXw0 : 0 < ‖X w‖ := by
    by_contra h0
    push Not at h0
    nlinarith [norm_nonneg Y, norm_nonneg (X w)]
  have hres : A (X w) - z • X w = X ((Y * A * X) w - z • w) := by
    simp only [mul_apply_eq_comp, map_sub, map_smul, hXY]
  refine ⟨((‖X w‖⁻¹ : ℝ) : 𝕜) • X w, ?_, ?_⟩
  · rw [RCLike.ofReal_inv]; exact norm_smul_inv_norm (norm_pos_iff.1 hXw0)
  rw [map_smul, smul_comm z, ← smul_sub, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (inv_pos.mpr hXw0), hres]
  have hinv : ‖X w‖⁻¹ ≤ ‖Y‖ := by
    rw [inv_le_iff_one_le_mul₀ hXw0]; linarith
  calc ‖X w‖⁻¹ * ‖X ((Y * A * X) w - z • w)‖ ≤ ‖Y‖ * (‖X‖ * ε) := by
        gcongr
        exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hle (norm_nonneg _))
    _ = ε * (‖X‖ * ‖Y‖) := by ring

end Intertwine

/-! ### The pseudospectral abscissa and radius -/

section Complex

variable [NormedSpace ℂ E]

/-- The **pseudospectral abscissa** of a bounded operator $A$ on a complex normed space, the
$\varepsilon$-analogue of the spectral abscissa: $$\alpha_\varepsilon(A) = \sup
\{\operatorname{Re} z : z \in \Lambda_\varepsilon(A)\}.$$ This is (7.9.8) of [golub2013matrix];
see also Trefethen and Embree, *Spectra and Pseudospectra*, §14.

The value is $0$ when $\Lambda_\varepsilon(A)$ is empty or its real parts are unbounded above.
On a nonzero finite-dimensional space and for $\varepsilon \ge 0$ the supremum is a maximum
(`ContinuousLinearMap.exists_eq_pseudospectralAbscissa_radius`). -/
noncomputable def pseudospectralAbscissa (ε : ℝ) (A : E →L[ℂ] E) : ℝ :=
  sSup ((fun z : ℂ => z.re) '' closedPseudospectrum ε A)

/-- The **pseudospectral radius** of a bounded operator $A$ on a complex normed space, the
$\varepsilon$-analogue of the spectral radius: $$\rho_\varepsilon(A) = \sup \{|z| : z \in
\Lambda_\varepsilon(A)\}.$$ This is (7.9.9) of [golub2013matrix].

The value is real because $\Lambda_\varepsilon(A)$ is bounded by $\|A\| + \varepsilon$. The
value is $0$ when $\Lambda_\varepsilon(A)$ is empty. -/
noncomputable def pseudospectralRadius (ε : ℝ) (A : E →L[ℂ] E) : ℝ :=
  sSup (norm '' closedPseudospectrum ε A)

variable [FiniteDimensional ℂ E] [Nontrivial E] {ε : ℝ}

/-- Let $E$ be a nonzero finite-dimensional complex normed space and $\varepsilon \ge 0$. Then
$\Lambda_\varepsilon(A)$ is nonempty, because it contains the eigenvalues of $A$. -/
theorem closedPseudospectrum_nonempty (hε : 0 ≤ ε) (A : E →L[ℂ] E) :
    (closedPseudospectrum ε A).Nonempty :=
  let ⟨_, hc⟩ := Module.End.exists_eigenvalue (A : E →ₗ[ℂ] E)
  ⟨_, mem_closedPseudospectrum_of_hasEigenvalue hε hc⟩

/-- The maxima in (7.9.8) and (7.9.9) of [golub2013matrix] are attained. Let $E$ be a nonzero
finite-dimensional complex normed space and $\varepsilon \ge 0$. Then some
$z_1 \in \Lambda_\varepsilon(A)$ has $\operatorname{Re} z_1 = \alpha_\varepsilon(A)$, and some
$z_2 \in \Lambda_\varepsilon(A)$ has $|z_2| = \rho_\varepsilon(A)$.

The proof uses the compactness of $\Lambda_\varepsilon(A)$. -/
theorem exists_eq_pseudospectralAbscissa_radius (hε : 0 ≤ ε) (A : E →L[ℂ] E) :
    (∃ z ∈ closedPseudospectrum ε A, z.re = pseudospectralAbscissa ε A) ∧
      ∃ z ∈ closedPseudospectrum ε A, ‖z‖ = pseudospectralRadius ε A := by
  have hK := isCompact_closedPseudospectrum ε A
  have hne := closedPseudospectrum_nonempty hε A
  constructor
  · obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne Complex.continuous_re.continuousOn
    refine ⟨z, hz, (IsGreatest.csSup_eq ⟨mem_image_of_mem _ hz, ?_⟩).symm⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hmax hv
  · obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    refine ⟨z, hz, (IsGreatest.csSup_eq ⟨mem_image_of_mem _ hz, ?_⟩).symm⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hmax hv

/-- The **transient growth bound**. Let $E$ be a nonzero finite-dimensional complex normed space,
and let $\|A^k\| \le M$ for every $k \in \mathbb{N}$. Then for every $\varepsilon > 0$,
$$\frac{\rho_\varepsilon(A) - 1}{\varepsilon} \le M,$$ that is, $\sup_k \|A^k\| \ge
(\rho_\varepsilon(A) - 1)/\varepsilon$. This is (7.9.11) of [golub2013matrix]; see also
Trefethen and Embree, *Spectra and Pseudospectra*, pp. 160–161.

Take $z \in \Lambda_\varepsilon(A)$ with $|z| = \rho_\varepsilon(A) > 1$. The Neumann series
$\sum_k A^k / z^{k+1}$ converges, since its terms are at most $M/|z|^{k+1}$, and its sum is
$(zI - A)^{-1}$. So $1/\varepsilon \le \|(zI - A)^{-1}\| \le M/(|z| - 1)$. -/
theorem pseudospectralRadius_sub_one_div_le_norm_pow (hε : 0 < ε) (A : E →L[ℂ] E) {M : ℝ}
    (hM : ∀ k : ℕ, ‖A ^ k‖ ≤ M) : (pseudospectralRadius ε A - 1) / ε ≤ M := by
  have := FiniteDimensional.complete ℂ E
  obtain ⟨-, z, hz, hzr⟩ := exists_eq_pseudospectralAbscissa_radius hε.le A
  have hM1 : 1 ≤ M := by simpa using hM 0
  rw [← hzr]
  rcases le_or_gt ‖z‖ 1 with h1 | h1
  · have : (‖z‖ - 1) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
    linarith
  have hz0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at h1; linarith
  set r := ‖z‖⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ h1
  set x : E →L[ℂ] E := z⁻¹ • A with hx
  have hxk : ∀ k : ℕ, ‖x ^ k‖ ≤ M * r ^ k := fun k => by
    rw [hx, smul_pow, norm_smul, norm_pow, norm_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM k) (by positivity)
  have hgeom : HasSum (fun k : ℕ => M * r ^ k) (M * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left M
  have hsum : Summable (x ^ ·) := Summable.of_norm_bounded hgeom.summable hxk
  set S := ∑' k : ℕ, x ^ k with hS
  have hS1 : S * (1 - x) = 1 := hsum.tsum_pow_mul_one_sub
  have hS2 : (1 - x) * S = 1 := hsum.one_sub_mul_tsum_pow
  have hzx : z • (1 : E →L[ℂ] E) - A = z • (1 - x) := by
    rw [hx, smul_sub, smul_smul, mul_inv_cancel₀ hz0, one_smul]
  let u : (E →L[ℂ] E)ˣ :=
    { val := z • 1 - A
      inv := z⁻¹ • S
      val_inv := by rw [hzx, smul_mul_smul_comm, mul_inv_cancel₀ hz0, one_smul, hS2]
      inv_val := by rw [hzx, smul_mul_smul_comm, inv_mul_cancel₀ hz0, one_smul, hS1] }
  have hnot : z ∉ spectrum ℂ A := by
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, not_not]
    exact u.isUnit
  have hres : 1 / ε ≤ ‖Ring.inverse (z • 1 - A)‖ :=
    ((mem_closedPseudospectrum_iff_resolvent hε).mp hz).resolve_left hnot
  have hinv : Ring.inverse (z • (1 : E →L[ℂ] E) - A) = z⁻¹ • S := Ring.inverse_unit u
  have hSn : ‖S‖ ≤ M * (1 - r)⁻¹ := tsum_of_norm_bounded hgeom hxk
  have hbound : ‖Ring.inverse (z • (1 : E →L[ℂ] E) - A)‖ ≤ M / (‖z‖ - 1) := by
    rw [hinv, norm_smul, norm_inv]
    calc ‖z‖⁻¹ * ‖S‖ ≤ ‖z‖⁻¹ * (M * (1 - r)⁻¹) := by gcongr
      _ = M / (‖z‖ - 1) := by
          rw [hr]
          field_simp
  have h2 : 1 / ε ≤ M / (‖z‖ - 1) := hres.trans hbound
  have hz1 : 0 < ‖z‖ - 1 := by linarith
  rw [div_le_div_iff₀ hε hz1] at h2
  rw [div_le_iff₀ hε]
  linarith

end Complex

end ContinuousLinearMap


namespace ContinuousLinearMap

/-! ### Connected components -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : ℝ}

/-- An approximate eigenvector gives a perturbation. Let $E$ be a complex normed space, let $w$ be a
unit vector, and let $\|Aw - zw\| \le \delta$. Then $z$ is an eigenvalue of $A + B$ for some
bounded operator $B$ with $\|B\| \le \delta$.

The perturbation is the rank-one operator $B = -(Aw - zw) \, g(\cdot)$, where $g$ is a norming
functional of $w$ given by the Hahn–Banach theorem. This is the normed-space form of the forward
direction of (7.9.7) of [golub2013matrix]. -/
theorem exists_hasEigenvalue_add_of_norm_sub_smul_le {A : E →L[ℂ] E} {z : ℂ} {w : E}
    (hw : ‖w‖ = 1) {δ : ℝ} (h : ‖A w - z • w‖ ≤ δ) :
    ∃ B : E →L[ℂ] E, ‖B‖ ≤ δ ∧ Module.End.HasEigenvalue ((A + B : E →L[ℂ] E) : E →ₗ[ℂ] E) z := by
  obtain ⟨g, hg1, hgw⟩ := exists_dual_vector ℂ w (by rw [hw]; exact one_ne_zero)
  refine ⟨-g.smulRight (A w - z • w), ?_, ?_⟩
  · rw [norm_neg, norm_smulRight_apply, hg1, one_mul]; exact h
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  refine Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 ?_, hw0⟩
  simp only [coe_coe, add_apply, neg_apply, smulRight_apply, hgw, hw, map_one, one_smul]
  abel

/-- Let $E$ be a complex normed space, and let $A$ and $B$ be bounded operators on $E$. Every
eigenvalue of $A + B$ lies in $\Lambda_{\|B\|}(A)$. -/
theorem mem_closedPseudospectrum_of_hasEigenvalue_add {A B : E →L[ℂ] E} {z : ℂ}
    (hz : Module.End.HasEigenvalue ((A + B : E →L[ℂ] E) : E →ₗ[ℂ] E) z) :
    z ∈ closedPseudospectrum ‖B‖ A := by
  obtain ⟨w, hw, hw0⟩ := hz.exists_hasEigenvector
  have hval : A w + B w = z • w := by simpa using Module.End.mem_eigenspace_iff.1 hw
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
  refine ⟨((‖w‖⁻¹ : ℝ) : ℂ) • w, ?_, ?_⟩
  · rw [Complex.ofReal_inv]; exact norm_smul_inv_norm hw0
  · have : A (((‖w‖⁻¹ : ℝ) : ℂ) • w) - z • ((‖w‖⁻¹ : ℝ) : ℂ) • w =
        ((‖w‖⁻¹ : ℝ) : ℂ) • -B w := by
      rw [map_smul, smul_comm z, ← smul_sub, ← hval]; congr 1; abel
    rw [this, norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.2 (norm_nonneg w))]
    calc ‖w‖⁻¹ * ‖B w‖ ≤ ‖w‖⁻¹ * (‖B‖ * ‖w‖) := by gcongr; exact B.le_opNorm w
      _ = ‖B‖ := by field_simp

variable [FiniteDimensional ℂ E]

/-- In finite dimension, the spectrum of a complex operator is finite. -/
private theorem finite_spectrum (A : E →L[ℂ] E) : (spectrum ℂ A).Finite := by
  have := FiniteDimensional.complete ℂ E
  rw [spectrum_eq]
  exact Module.End.finite_spectrum _

/-- Every connected component of the closed pseudospectrum contains an eigenvalue,
[golub2013matrix], §7.9.3: "each connected component of $\Lambda_\varepsilon(A)$ contains at
least one eigenvalue of $A$". Let $E$ be a finite-dimensional complex normed space, and let
$z \in \Lambda_\varepsilon(A)$. Then there is an eigenvalue $\mu \in \sigma(A)$ in the connected
component of $z$ in $\Lambda_\varepsilon(A)$.

The proof uses continuity of roots, not the maximum modulus principle. If the component missed
the finite spectrum, $\Lambda_\varepsilon(A)$ would split into disjoint compact parts $C \ni z$
and $D \supseteq \sigma(A)$. Take $B$ with $\|B\| \le \varepsilon$ and $z \in \sigma(A + B)$.
Along $t \mapsto A + tB$, $t \in [0, 1]$, all eigenvalues stay in
$\Lambda_\varepsilon(A) = C \cup D$, so the number of eigenvalues in $C$ is constant
(`Polynomial.countRootsIn_eq_of_preconnected`). But it is $0$ at $t = 0$ and at least $1$ at
$t = 1$. -/
theorem exists_mem_spectrum_mem_connectedComponentIn (A : E →L[ℂ] E) {z : ℂ}
    (hz : z ∈ closedPseudospectrum ε A) :
    ∃ μ ∈ spectrum ℂ A, μ ∈ connectedComponentIn (closedPseudospectrum ε A) z := by
  have := FiniteDimensional.complete ℂ E
  classical
  have hε : 0 ≤ ε := let ⟨_, _, h⟩ := hz; (norm_nonneg _).trans h
  by_contra hK
  push Not at hK
  obtain ⟨C, D, hC, hD, hCD, hΛ, hzC, hσD⟩ :=
    (isCompact_closedPseudospectrum ε A).exists_compact_split_of_finite (finite_spectrum A)
    (spectrum_subset_closedPseudospectrum hε) hz hK
  obtain ⟨w, hw, hle⟩ := hz
  obtain ⟨B, hB, hzB⟩ := exists_hasEigenvalue_add_of_norm_sub_smul_le hw hle
  -- the path of matrices
  set b := Module.finBasis ℂ E
  set N := Module.finrank ℂ E
  set M : ℝ → Matrix (Fin N) (Fin N) ℂ := fun t =>
    LinearMap.toMatrix b b (A : E →ₗ[ℂ] E) + (t : ℂ) • LinearMap.toMatrix b b (B : E →ₗ[ℂ] E)
    with hM
  have hMeq : ∀ t : ℝ, M t = LinearMap.toMatrix b b ((A + (t : ℂ) • B : E →L[ℂ] E) : E →ₗ[ℂ] E) :=
    fun t => by
      simp only [hM, toLinearMap_add, toLinearMap_smul, map_add, LinearEquiv.map_smul]
  have hMcont : Continuous M :=
    continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  -- roots of the characteristic polynomial are eigenvalues of `A + t B`
  have hroot : ∀ t : ℝ, ∀ μ, μ ∈ (M t).charpoly.roots ↔
      Module.End.HasEigenvalue ((A + (t : ℂ) • B : E →L[ℂ] E) : E →ₗ[ℂ] E) μ := by
    intro t μ
    rw [Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero, hMeq, LinearMap.charpoly_toMatrix,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  have hsub : ∀ t : Icc (0 : ℝ) 1, ∀ μ ∈ (M t.1).charpoly.roots, μ ∈ C ∪ D := by
    rintro ⟨t, ht0, ht1⟩ μ hμ
    rw [hΛ]
    refine closedPseudospectrum_mono ?_ (mem_closedPseudospectrum_of_hasEigenvalue_add
      ((hroot t μ).mp hμ))
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc t * ‖B‖ ≤ 1 * ε := mul_le_mul ht1 hB (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε
  have hcard : ∀ t : ℝ, Multiset.card (M t).charpoly.roots = N := fun t =>
    (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits (M t).charpoly)).trans
      ((Matrix.charpoly_natDegree_eq_dim _).trans (Fintype.card_fin N))
  have : PreconnectedSpace (Icc (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have key := Polynomial.countRootsIn_eq_of_preconnected (T := Icc (0 : ℝ) 1)
    (p := fun t => (M t.1).charpoly) (n := N) hC hD hCD
    (fun _ => Matrix.charpoly_monic _)
    (fun _ => (Matrix.charpoly_natDegree_eq_dim _).trans (Fintype.card_fin N))
    (fun t => hcard t.1) hsub
    (fun j => (Matrix.continuous_coeff_charpoly hMcont j).comp continuous_subtype_val)
    ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
  simp only at key
  -- at `t = 0` no root lies in `C`; at `t = 1`, `z` does
  have h0 : (M 0).charpoly.countRootsIn C = 0 := by
    rw [Polynomial.countRootsIn, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro μ hμ hμC
    have hμA : μ ∈ spectrum ℂ A := by
      have h := (hroot 0 μ).mp hμ
      rw [Complex.ofReal_zero, zero_smul, add_zero, Module.End.hasEigenvalue_iff_mem_spectrum,
        ← spectrum_eq] at h
      exact h
    exact Set.disjoint_left.mp hCD hμC (hσD hμA)
  have h1 : 0 < (M 1).charpoly.countRootsIn C := by
    rw [Polynomial.countRootsIn, Multiset.card_pos_iff_exists_mem]
    refine ⟨z, Multiset.mem_filter.mpr ⟨(hroot 1 z).mpr ?_, hzC⟩⟩
    rwa [Complex.ofReal_one, one_smul]
  omega

end ContinuousLinearMap

/-! ### Matrices -/

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

open ContinuousLinearMap

/-- Let $A$ be a square matrix over $\mathbb{K}$. The closed pseudospectrum of $A^H$ is the complex
conjugate of the closed pseudospectrum of $A$: $z \in \Lambda_\varepsilon(A^H)$ if and only if
$\bar z \in \Lambda_\varepsilon(A)$. -/
theorem mem_closedPseudospectrum_conjTranspose_iff {A : Matrix n n 𝕜} {ε : ℝ} {z : 𝕜} :
    z ∈ (toEuclideanCLM (n := n) (𝕜 := 𝕜) Aᴴ).closedPseudospectrum ε ↔
      star z ∈ (toEuclideanCLM (n := n) (𝕜 := 𝕜) A).closedPseudospectrum ε := by
  rw [← star_eq_conjTranspose, map_star, star_eq_adjoint]
  exact mem_closedPseudospectrum_adjoint_iff

/-- Let $A$ be an $n \times n$ matrix over $\mathbb{K}$ with $n \ge 1$. Then
$z \in \Lambda_\varepsilon(A)$ if and only if the least singular value of $zI - A$ is at most
$\varepsilon$: $$\sigma_{\min}(zI - A) \le \varepsilon.$$ This is (7.9.5) of [golub2013matrix]
for matrices.

The least singular value is the last entry of `Matrix.sortedSingularValues`, which lists the
singular values in nonincreasing order from index $0$, so it is the entry at index $n - 1$. It
equals the infimum of `Matrix.colSingularValues`
(`Matrix.sortedSingularValues_eq_iInf_colSingularValues`). The proof is
`ContinuousLinearMap.mem_closedPseudospectrum_iff_iInf`, with the least residual read as the
least singular value (`Matrix.iInf_colSingularValues_eq_iInf_norm`). -/
theorem mem_closedPseudospectrum_iff_iInf_colSingularValues [Nonempty n] {A : Matrix n n 𝕜}
    {ε : ℝ} {z : 𝕜} :
    z ∈ (toEuclideanCLM (n := n) (𝕜 := 𝕜) A).closedPseudospectrum ε ↔
      (z • 1 - A).sortedSingularValues (Fintype.card n - 1) ≤ ε := by
  rw [mem_closedPseudospectrum_iff_iInf, sortedSingularValues_eq_iInf_colSingularValues,
    iInf_colSingularValues_eq_iInf_norm]
  have h : ∀ w : {w : EuclideanSpace 𝕜 n // ‖w‖ = 1},
      ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A w - z • (w : EuclideanSpace 𝕜 n)‖ =
        ‖toEuclideanLin (z • 1 - A) w‖ := fun w => by
    rw [← norm_neg, neg_sub, toEuclideanLin_sub_apply, toEuclideanLin_smul_apply,
      toEuclideanLin_one_apply]
    rfl
  simp_rw [h]

section L2

open scoped Matrix.Norms.L2Operator

/-- Let $X$ be an invertible square matrix and $A$ a square matrix of the same size. Then
$$\Lambda_\varepsilon(X^{-1} A X) \subseteq \Lambda_{\varepsilon \kappa_2(X)}(A),$$ where
$\kappa_2(X) = \|X\|_2 \|X^{-1}\|_2$ is the condition number in the spectral norm. This is
Theorem 7.9.2 of [golub2013matrix].

The condition number is `NormedRing.condNumber X` for the spectral norm. The proof is
`ContinuousLinearMap.closedPseudospectrum_units_conj_subset` for the Euclidean operators. -/
theorem closedPseudospectrum_conj_subset {X : Matrix n n 𝕜} (hX : IsUnit X) (A : Matrix n n 𝕜)
    (ε : ℝ) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) (X⁻¹ * A * X)).closedPseudospectrum ε ⊆
      (toEuclideanCLM (n := n) (𝕜 := 𝕜) A).closedPseudospectrum (ε * NormedRing.condNumber X) := by
  obtain ⟨u, hu⟩ := hX.map (toEuclideanCLM (n := n) (𝕜 := 𝕜))
  have hinv : (↑u⁻¹ : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) =
      toEuclideanCLM (n := n) (𝕜 := 𝕜) X⁻¹ := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hu, ← map_mul, mul_nonsing_inv _ ((isUnit_iff_isUnit_det X).mp hX), map_one]
  have hcond : NormedRing.condNumber X =
      ‖(u : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)‖ *
        ‖(↑u⁻¹ : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)‖ := by
    rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse, hinv, hu]
    rfl
  rw [map_mul, map_mul, ← hu, ← hinv, hcond]
  exact closedPseudospectrum_units_conj_subset u _ ε

end L2

private theorem toEuclideanCLM_mul_apply (X Y : Matrix n n 𝕜)
    (w : EuclideanSpace 𝕜 n) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) (X * Y) w =
      toEuclideanCLM (n := n) (𝕜 := 𝕜) X (toEuclideanCLM (n := n) (𝕜 := 𝕜) Y w) := by
  rw [map_mul]
  rfl

private theorem closedPseudospectrum_unitary_conj_subset {V : Matrix n n 𝕜}
    (hV : V ∈ unitaryGroup n 𝕜) (B : Matrix n n 𝕜) (ε : ℝ) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) (star V * B * V)).closedPseudospectrum ε ⊆
      (toEuclideanCLM (n := n) (𝕜 := 𝕜) B).closedPseudospectrum ε := by
  rintro z ⟨w, hw, h⟩
  refine ⟨toEuclideanCLM (n := n) (𝕜 := 𝕜) V w, by
    rw [norm_toEuclideanCLM_apply_of_mem_unitaryGroup hV, hw], ?_⟩
  have hres : toEuclideanCLM (n := n) (𝕜 := 𝕜) B (toEuclideanCLM (n := n) (𝕜 := 𝕜) V w) -
      z • toEuclideanCLM (n := n) (𝕜 := 𝕜) V w =
      toEuclideanCLM (n := n) (𝕜 := 𝕜) V
        (toEuclideanCLM (n := n) (𝕜 := 𝕜) (star V * B * V) w - z • w) := by
    rw [map_sub, map_smul, ← toEuclideanCLM_mul_apply, ← toEuclideanCLM_mul_apply,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, Unitary.mul_star_self_of_mem hV, Matrix.one_mul]
  rw [hres, norm_toEuclideanCLM_apply_of_mem_unitaryGroup hV]
  exact h

/-- Unitary similarity preserves the closed pseudospectrum: for a unitary matrix $U$,
$$\Lambda_\varepsilon(U^H A U) = \Lambda_\varepsilon(A).$$ This is Corollary 7.9.3 of
[golub2013matrix].

A unitary matrix maps unit vectors with a small residual for $U^H A U$ to unit vectors with the
same residual for $A$, and conversely. -/
theorem closedPseudospectrum_unitary_conj {U : Matrix n n 𝕜} (hU : U ∈ unitaryGroup n 𝕜)
    (A : Matrix n n 𝕜) (ε : ℝ) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) (star U * A * U)).closedPseudospectrum ε =
      (toEuclideanCLM (n := n) (𝕜 := 𝕜) A).closedPseudospectrum ε := by
  refine Subset.antisymm (closedPseudospectrum_unitary_conj_subset hU A ε) ?_
  have hA : star (star U) * (star U * A * U) * star U = A := by
    have h1 : U * star U = 1 := Unitary.mul_star_self_of_mem hU
    rw [star_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc,
      h1, Matrix.mul_one]
  conv_lhs => rw [← hA]
  exact closedPseudospectrum_unitary_conj_subset (Unitary.star_mem hU) _ ε

/-- For a diagonal matrix $D = \operatorname{diag}(d)$, the residual is computed entrywise:
$((D - zI) w)_i = (d_i - z) w_i$. -/
private theorem toEuclideanCLM_diagonal_sub_smul_apply (d : n → 𝕜) (z : 𝕜)
    (w : EuclideanSpace 𝕜 n) (i : n) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) (diagonal d) w - z • w) i = (d i - z) * w i := by
  simp [mulVec_diagonal, sub_mul]

/-- The closed pseudospectrum of a diagonal matrix $D = \operatorname{diag}(d)$ is the union of the
closed discs of radius $\varepsilon$ about its diagonal entries: $$\Lambda_\varepsilon(D) =
\bigcup_i \{z : |z - d_i| \le \varepsilon\}.$$ This is Theorem 7.9.4 of [golub2013matrix].

For a unit vector $w$, $\|(D - zI) w\|^2 = \sum_i |d_i - z|^2 |w_i|^2 \ge \min_i |d_i - z|^2$,
with equality at a coordinate vector. -/
theorem closedPseudospectrum_diagonal (d : n → 𝕜) (ε : ℝ) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) (diagonal d)).closedPseudospectrum ε =
      ⋃ i, closedBall (d i) ε := by
  ext z
  simp only [mem_iUnion, mem_closedBall]
  constructor
  · rintro ⟨w, hw, h⟩
    by_contra hz
    push Not at hz
    rcases isEmpty_or_nonempty n with hn | hn
    · have : w = 0 := PiLp.ext fun i => (IsEmpty.false i).elim
      rw [this, norm_zero] at hw
      exact zero_ne_one hw
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => ‖d i - z‖)
      Finset.univ_nonempty
    have hδ : ε < ‖d i₀ - z‖ := by rw [← dist_eq_norm, dist_comm]; exact hz i₀
    have hε : 0 ≤ ε := (norm_nonneg _).trans h
    have hsq : ‖d i₀ - z‖ ^ 2 ≤
        ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) (diagonal d) w - z • w‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ‖d i₀ - z‖ ^ 2 = ‖d i₀ - z‖ ^ 2 * ‖w‖ ^ 2 := by rw [hw, one_pow, mul_one]
        _ = ∑ i, ‖d i₀ - z‖ ^ 2 * ‖w i‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
        _ ≤ _ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [toEuclideanCLM_diagonal_sub_smul_apply, norm_mul, mul_pow]
          gcongr
          exact hi₀ i (Finset.mem_univ i)
    have := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith
  · rintro ⟨i, hi⟩
    refine ⟨EuclideanSpace.single i 1, by simp, ?_⟩
    have : toEuclideanCLM (n := n) (𝕜 := 𝕜) (diagonal d) (EuclideanSpace.single i 1) -
        z • EuclideanSpace.single i 1 = EuclideanSpace.single i (d i - z) := by
      ext j
      rw [toEuclideanCLM_diagonal_sub_smul_apply]
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [this, PiLp.norm_single, ← dist_eq_norm, dist_comm]
    exact hi

/-- Let $\mathbb{K}$ be algebraically closed (that is, $\mathbb{K} = \mathbb{C}$), and let $A$ be a
normal square matrix. Then the closed pseudospectrum of $A$ is the union of the closed discs of
radius $\varepsilon$ about its eigenvalues: $$\Lambda_\varepsilon(A) = \bigcup_{\lambda \in
\sigma(A)} \{z : |z - \lambda| \le \varepsilon\}.$$ This is Corollary 7.9.5 of
[golub2013matrix].

The proof diagonalizes $A$ by a unitary matrix and uses
`Matrix.closedPseudospectrum_unitary_conj` and `Matrix.closedPseudospectrum_diagonal`. -/
theorem closedPseudospectrum_of_isStarNormal [IsAlgClosed 𝕜] {A : Matrix n n 𝕜}
    (hA : IsStarNormal A) (ε : ℝ) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) A).closedPseudospectrum ε =
      ⋃ μ ∈ spectrum 𝕜 A, closedBall μ ε := by
  obtain ⟨U, hU, d, hd⟩ := IsStarNormal.spectral_theorem.mp hA
  rw [← star_eq_conjTranspose] at hd
  have hspec : spectrum 𝕜 A = range d := by
    let u : (Matrix n n 𝕜)ˣ :=
      ⟨star U, U, Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU⟩
    have := spectrum.units_conjugate (R := 𝕜) (a := A) (u := u)
    rw [← spectrum_diagonal (R := 𝕜) d, ← hd, ← this]
    rfl
  rw [hspec, biUnion_range, ← closedPseudospectrum_diagonal, ← hd,
    closedPseudospectrum_unitary_conj hU]

/-- The isometric embedding $x \mapsto (x, 0)$ of $\mathbb{K}^m$ into $\mathbb{K}^{m + n}$. -/
private def inlL : EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 (m ⊕ n) where
  toFun x := WithLp.toLp 2 (Sum.elim (WithLp.ofLp x) 0)
  map_add' x y := by ext (i | i) <;> simp
  map_smul' c x := by ext (i | i) <;> simp

/-- The isometric embedding $y \mapsto (0, y)$ of $\mathbb{K}^n$ into $\mathbb{K}^{m + n}$. -/
private def inrL : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 (m ⊕ n) where
  toFun y := WithLp.toLp 2 (Sum.elim 0 (WithLp.ofLp y))
  map_add' x y := by ext (i | i) <;> simp
  map_smul' c x := by ext (i | i) <;> simp

omit [DecidableEq m] [DecidableEq n] in
/-- The Euclidean norm splits into the two halves: $\|(x, y)\|^2 = \|x\|^2 + \|y\|^2$. -/
private theorem norm_sq_eq_add (v : EuclideanSpace 𝕜 (m ⊕ n)) :
    ‖v‖ ^ 2 = ‖(WithLp.toLp 2 (WithLp.ofLp v ∘ Sum.inl) : EuclideanSpace 𝕜 m)‖ ^ 2 +
      ‖(WithLp.toLp 2 (WithLp.ofLp v ∘ Sum.inr) : EuclideanSpace 𝕜 n)‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
  rfl

omit [DecidableEq m] [DecidableEq n] in
private theorem norm_inlL (x : EuclideanSpace 𝕜 m) : ‖(inlL (n := n) x)‖ = ‖x‖ := by
  have h := norm_sq_eq_add (inlL (n := n) x)
  have h0 : (WithLp.toLp 2 (WithLp.ofLp (inlL (n := n) x) ∘ Sum.inr) : EuclideanSpace 𝕜 n) =
      0 := by
    ext j; simp [inlL]
  have h1 : (WithLp.toLp 2 (WithLp.ofLp (inlL (n := n) x) ∘ Sum.inl) : EuclideanSpace 𝕜 m) =
      x := by
    ext j; simp [inlL]
  rw [h0, h1, norm_zero] at h
  simpa [sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)] using h

omit [DecidableEq m] [DecidableEq n] in
private theorem norm_inrL (y : EuclideanSpace 𝕜 n) : ‖(inrL (m := m) y)‖ = ‖y‖ := by
  have h := norm_sq_eq_add (inrL (m := m) y)
  have h0 : (WithLp.toLp 2 (WithLp.ofLp (inrL (m := m) y) ∘ Sum.inl) : EuclideanSpace 𝕜 m) =
      0 := by
    ext j; simp [inrL]
  have h1 : (WithLp.toLp 2 (WithLp.ofLp (inrL (m := m) y) ∘ Sum.inr) : EuclideanSpace 𝕜 n) =
      y := by
    ext j; simp [inrL]
  rw [h0, h1, norm_zero] at h
  simpa [sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)] using h

/-- Let $T = \begin{bmatrix} T_{11} & T_{12} \\ 0 & T_{22} \end{bmatrix}$ be block upper triangular.
Then $$\Lambda_\varepsilon(T_{11}) \cup \Lambda_\varepsilon(T_{22}) \subseteq
\Lambda_\varepsilon(T).$$ This is Theorem 7.9.6 of [golub2013matrix].

$T_{11}$ acts on the invariant subspace of the vectors $(x, 0)$. For $T_{22}$, the proof passes
to the conjugate transposes (`Matrix.mem_closedPseudospectrum_conjTranspose_iff`), where
$T_{22}^H$ acts on the invariant subspace of the vectors $(0, y)$ of $T^H$. -/
theorem closedPseudospectrum_fromBlocks_zero₂₁_supset (T₁₁ : Matrix m m 𝕜)
    (T₁₂ : Matrix m n 𝕜) (T₂₂ : Matrix n n 𝕜) (ε : ℝ) :
    (toEuclideanCLM (n := m) (𝕜 := 𝕜) T₁₁).closedPseudospectrum ε ∪
        (toEuclideanCLM (n := n) (𝕜 := 𝕜) T₂₂).closedPseudospectrum ε ⊆
      (toEuclideanCLM (n := m ⊕ n) (𝕜 := 𝕜)
        (fromBlocks T₁₁ T₁₂ 0 T₂₂)).closedPseudospectrum ε := by
  refine union_subset ?_ fun z hz => ?_
  · refine closedPseudospectrum_subset_of_intertwine (J := inlL) norm_inlL fun w => ?_
    ext (i | i) <;> simp [inlL, fromBlocks_mulVec]
  · rw [← star_star z, ← mem_closedPseudospectrum_conjTranspose_iff] at hz ⊢
    rw [fromBlocks_conjTranspose, conjTranspose_zero]
    refine closedPseudospectrum_subset_of_intertwine (J := inrL) norm_inrL (fun w => ?_) hz
    ext (i | i) <;> simp [inrL, fromBlocks_mulVec]

/-- If $z \notin \Lambda_\varepsilon(P)$ and $\varepsilon \ge 0$, then
$\varepsilon^2 \|x\|^2 \le \|Px - zx\|^2$ for every $x$, with strict inequality for $x \neq 0$. -/
private theorem sq_mul_norm_sq_le {p : Type*} [Fintype p] [DecidableEq p] {P : Matrix p p 𝕜}
    {ε : ℝ} {z : 𝕜} (hz : z ∉ (toEuclideanCLM (n := p) (𝕜 := 𝕜) P).closedPseudospectrum ε)
    (hε : 0 ≤ ε) (x : EuclideanSpace 𝕜 p) :
    ε ^ 2 * ‖x‖ ^ 2 ≤ ‖toEuclideanCLM (n := p) (𝕜 := 𝕜) P x - z • x‖ ^ 2 ∧
      (x ≠ 0 → ε ^ 2 * ‖x‖ ^ 2 < ‖toEuclideanCLM (n := p) (𝕜 := 𝕜) P x - z • x‖ ^ 2) := by
  have hlt : x ≠ 0 → ε ^ 2 * ‖x‖ ^ 2 < ‖toEuclideanCLM (n := p) (𝕜 := 𝕜) P x - z • x‖ ^ 2 :=
    fun hx => by
      have := mul_norm_lt_norm_sub_smul_of_notMem hz hx
      rw [← mul_pow]
      exact pow_lt_pow_left₀ this (by positivity) two_ne_zero
  refine ⟨?_, hlt⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (hlt hx).le

/-- The closed pseudospectrum of a block diagonal matrix is the union of the closed pseudospectra of
its blocks: $$\Lambda_\varepsilon(\operatorname{diag}(T_{11}, T_{22})) =
\Lambda_\varepsilon(T_{11}) \cup \Lambda_\varepsilon(T_{22}).$$ This is Corollary 7.9.7 of
[golub2013matrix].

For the inclusion $\subseteq$: a unit vector $(u, w)$ has $\|(T - zI)(u, w)\|^2 = \|(T_{11} -
zI) u\|^2 + \|(T_{22} - zI) w\|^2$. If $z$ lay in neither pseudospectrum, the two terms would
exceed $\varepsilon^2 \|u\|^2$ and $\varepsilon^2 \|w\|^2$ (strictly for a nonzero half), so the
sum would exceed $\varepsilon^2$. -/
theorem closedPseudospectrum_fromBlocks_diagonal (T₁₁ : Matrix m m 𝕜) (T₂₂ : Matrix n n 𝕜)
    (ε : ℝ) :
    (toEuclideanCLM (n := m ⊕ n) (𝕜 := 𝕜) (fromBlocks T₁₁ 0 0 T₂₂)).closedPseudospectrum ε =
      (toEuclideanCLM (n := m) (𝕜 := 𝕜) T₁₁).closedPseudospectrum ε ∪
        (toEuclideanCLM (n := n) (𝕜 := 𝕜) T₂₂).closedPseudospectrum ε := by
  refine Subset.antisymm ?_ (closedPseudospectrum_fromBlocks_zero₂₁_supset T₁₁ 0 T₂₂ ε)
  rintro z ⟨v, hv, h⟩
  by_contra hz
  rw [mem_union, not_or] at hz
  have hε : 0 ≤ ε := (norm_nonneg _).trans h
  set u : EuclideanSpace 𝕜 m := WithLp.toLp 2 (WithLp.ofLp v ∘ Sum.inl) with hu
  set w : EuclideanSpace 𝕜 n := WithLp.toLp 2 (WithLp.ofLp v ∘ Sum.inr) with hw
  set r := toEuclideanCLM (n := m ⊕ n) (𝕜 := 𝕜) (fromBlocks T₁₁ 0 0 T₂₂) v - z • v with hr
  have hr2 : ‖r‖ ^ 2 = ‖toEuclideanCLM (n := m) (𝕜 := 𝕜) T₁₁ u - z • u‖ ^ 2 +
      ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) T₂₂ w - z • w‖ ^ 2 := by
    rw [norm_sq_eq_add]
    congr 3 <;> ext i <;> simp [r, u, w, fromBlocks_mulVec]
  have hv2 : ‖u‖ ^ 2 + ‖w‖ ^ 2 = 1 := by rw [← norm_sq_eq_add, hv, one_pow]
  obtain ⟨hu1, hu2⟩ := sq_mul_norm_sq_le hz.1 hε u
  obtain ⟨hw1, hw2⟩ := sq_mul_norm_sq_le hz.2 hε w
  have hle : ‖r‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rcases eq_or_ne u 0 with hu0 | hu0
  · have hw0 : w ≠ 0 := by
      rintro hw0
      rw [hu0, hw0, norm_zero] at hv2
      norm_num at hv2
    have := hw2 hw0
    nlinarith
  · have := hu2 hu0
    nlinarith

section L2

open scoped Matrix.Norms.L2Operator

/-- The **pseudospectral abscissa** $\alpha_\varepsilon(A)$ of a complex square matrix $A$, (7.9.8)
of [golub2013matrix]: the pseudospectral abscissa of its Euclidean operator, $\sup
\{\operatorname{Re} z : z \in \Lambda_\varepsilon(A)\}$. -/
noncomputable abbrev pseudospectralAbscissa (ε : ℝ) (A : Matrix n n ℂ) : ℝ :=
  (toEuclideanCLM (n := n) (𝕜 := ℂ) A).pseudospectralAbscissa ε

/-- The **pseudospectral radius** $\rho_\varepsilon(A)$ of a complex square matrix $A$, (7.9.9) of
[golub2013matrix]: the pseudospectral radius of its Euclidean operator,
$\sup \{|z| : z \in \Lambda_\varepsilon(A)\}$. -/
noncomputable abbrev pseudospectralRadius (ε : ℝ) (A : Matrix n n ℂ) : ℝ :=
  (toEuclideanCLM (n := n) (𝕜 := ℂ) A).pseudospectralRadius ε

/-- The maxima in (7.9.8) and (7.9.9) of [golub2013matrix] are attained for a matrix. Let $A$ be a
complex $n \times n$ matrix with $n \ge 1$, and let $\varepsilon \ge 0$. Then some
$z_1 \in \Lambda_\varepsilon(A)$ has $\operatorname{Re} z_1 = \alpha_\varepsilon(A)$, and some
$z_2 \in \Lambda_\varepsilon(A)$ has $|z_2| = \rho_\varepsilon(A)$. -/
theorem exists_eq_pseudospectralAbscissa_radius [Nonempty n] {ε : ℝ} (hε : 0 ≤ ε)
    (A : Matrix n n ℂ) :
    (∃ z ∈ (toEuclideanCLM (n := n) (𝕜 := ℂ) A).closedPseudospectrum ε,
        z.re = pseudospectralAbscissa ε A) ∧
      ∃ z ∈ (toEuclideanCLM (n := n) (𝕜 := ℂ) A).closedPseudospectrum ε,
        ‖z‖ = pseudospectralRadius ε A :=
  ContinuousLinearMap.exists_eq_pseudospectralAbscissa_radius hε _

/-- Let $A$ be a complex $n \times n$ matrix with $n \ge 1$, and let $\|A^k\|_2 \le M$ for every
$k \in \mathbb{N}$. Then for every $\varepsilon > 0$, $$\frac{\rho_\varepsilon(A) -
1}{\varepsilon} \le M.$$ This is (7.9.11) of [golub2013matrix] for matrices. -/
theorem pseudospectralRadius_sub_one_div_le_norm_pow [Nonempty n] {ε : ℝ} (hε : 0 < ε)
    (A : Matrix n n ℂ) {M : ℝ} (hM : ∀ k : ℕ, ‖A ^ k‖ ≤ M) :
    (pseudospectralRadius ε A - 1) / ε ≤ M :=
  ContinuousLinearMap.pseudospectralRadius_sub_one_div_le_norm_pow hε _ fun k => by
    rw [← map_pow, ← cstar_norm_def]
    exact hM k

end L2

end Matrix
