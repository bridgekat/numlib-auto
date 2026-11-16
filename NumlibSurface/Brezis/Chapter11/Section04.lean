/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.MeasureTheory.Function.L2Space
import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.InnerProductSpace.CompactSpectral.Normal
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Numlib.Analysis.Normed.Algebra.Spectrum
import Numlib.Analysis.Normed.Lp.Sequence
import Numlib.Analysis.Normed.Module.Annihilator
import Numlib.Analysis.Normed.Operator.Unbounded.Adjoint
import Numlib.Variational.Forms
import NumlibSurface.Brezis.Chapter01.Section03
import NumlibSurface.Brezis.Chapter01.Section04
import NumlibSurface.Brezis.Chapter05.Section01
import NumlibSurface.Brezis.Chapter05.Section03
import NumlibSurface.Brezis.Chapter11.Section02

/-!
# Brezis, Section 11.4: Banach spaces over $\mathbb{C}$: what is similar and what is different

This module formalizes Section 11.4 of [brezis2011functional], the only part of the surface library
over the complex numbers. Here $E$ is a complex normed space, a Banach space where the source says
so, and $H$ is a complex Hilbert space. The real space $E_\mathbb{R}$ is $E$ with the scalars
restricted to $\mathbb{R}$, and $H_\mathbb{R}$ is $H$ with the real scalar product
$\operatorname{Re}(u, v)$. The map $I : f \mapsto \operatorname{Re} f$ is an isometric bijection
from $E^*$ onto $E_\mathbb{R}^*$ (Proposition 11.22), and through it the real results of Chapters 1
and 5 hold over $\mathbb{C}$: the Hahn–Banach theorem (Propositions 11.23 and 11.24), the
Fenchel–Moreau theorem (Proposition 11.25), the projection onto a closed convex set, the
Riesz–Fréchet, Stampacchia and Lax–Milgram theorems (Propositions 11.26–11.29). The second half of
the section develops the spectral theory of $T \in \mathcal{L}(E)$: the spectrum is nonempty and
compact (Proposition 11.30), the spectral radius is $\max\{|\lambda| ; \lambda \in \sigma(T)\}$
(Proposition 11.31), and the spectral mapping theorem holds for polynomials (Proposition 11.32). On
a Hilbert space the spectrum lies in the closure of the numerical range $W(T)$ (Proposition 11.33),
and the section treats self-adjoint, normal, compact normal, isometric, unitary and skew-adjoint
operators (Propositions 11.34–11.37).

The real structures are Mathlib's instances `NormedSpace.complexToReal` and
`InnerProductSpace.complexToReal`, and the real scalar product is $\operatorname{Re}(u, v)$ by
`real_inner_eq_re_inner`. The spectral theory is Mathlib's theory of complex Banach algebras and
C⋆-algebras for `E →L[ℂ] E` and `H →L[ℂ] H`, together with the backbone modules
`Numlib.Analysis.Normed.Algebra.Spectrum` (numerical range, isometries, the spectral mapping theorem
for eigenvalues) and `Numlib.Analysis.InnerProductSpace.CompactSpectral.Normal` (compact normal
operators).

## Main definitions

* Proposition 11.22, `Brezis.Chapter11.reDual`: the map $I : E^* \to E_\mathbb{R}^*$,
  $f \mapsto \operatorname{Re} f$, as a real-linear isometric isomorphism.
* Section 11.4, definition of a closed real hyperplane, `Brezis.Chapter11.IsClosedRealHyperplane`: a
  set $[\operatorname{Re} f = \alpha]$ with $f \in E^*$, $f \neq 0$ and $\alpha \in \mathbb{R}$.
* Section 11.4, definition of separation, `Brezis.Chapter11.SeparatesRe`: $\operatorname{Re} \langle
  f, x \rangle \le \alpha$ on $A$ and $\operatorname{Re} \langle f, x \rangle \ge \alpha$ on $B$.
* Section 11.4, the real pairing, `Brezis.Chapter11.rePairing`: $\langle x, f \rangle \mapsto
  \operatorname{Re} \langle f, x \rangle$ on $E \times E^*$.
* Section 11.4, definition of the conjugate function, `Brezis.Chapter11.conjugateC`: $\varphi^*(f) =
  \sup_{x \in E} \{\operatorname{Re} \langle f, x \rangle - \varphi(x)\}$.
* Section 11.4, the biconjugate, `Brezis.Chapter11.biconjugateC`: $\varphi^{**}(x) = \sup_{f \in
  E^*} \{\operatorname{Re} \langle f, x \rangle - \varphi^*(f)\}$.
* Section 11.4, the right shift, `Brezis.Chapter11.rightShift`: $Tu = (0, u_1, u_2, \dots)$ on
  $\ell^2$.
* Section 11.4, definition of the numerical range, `Brezis.Chapter11.numericalRange_eq`:
  $W(T) = \{(Tu, u) ; u \in H, |u| = 1\}$.

## Main results

* Display (12), `Brezis.Chapter11.reDual_symm_apply`: the inverse of $I$ maps
  $\varphi \in E_\mathbb{R}^*$ to $f(x) = \varphi(x) - i \varphi(ix)$.
* Proposition 11.22, `Brezis.Chapter11.proposition_11_22`: $f \mapsto \operatorname{Re} f$ is an
  isometric bijection from $E^*$ onto $E_\mathbb{R}^*$.
* Proposition 11.23, `Brezis.Chapter11.proposition_11_23`: a continuous linear functional on a
  subspace $G \subseteq E$ extends to $E$ with the same norm.
* Section 11.4, `Brezis.Chapter11.isClosedRealHyperplane_iff`: the closed real hyperplanes of $E$
  are the closed hyperplanes of $E_\mathbb{R}$.
* Section 11.4, `Brezis.Chapter11.separatesRe_iff`: separation by $[\operatorname{Re} f = \alpha]$
  is separation by $[If = \alpha]$ in $E_\mathbb{R}$.
* Proposition 11.24, `Brezis.Chapter11.proposition_11_24`: two nonempty disjoint convex sets, one of
  them open, are separated by a closed real hyperplane.
* Section 11.4, the orthogonal, `Brezis.Chapter11.orthogonal_complex`: $M^\perp = \{f ;
  \operatorname{Re} \langle f, x \rangle = 0 \ \forall x \in M\}$ and
  $M^{\perp\perp} = \overline{M}$.
* Section 11.4, `Brezis.Chapter11.conjugateC_eq`: $\varphi^*(f) = \varphi_\mathbb{R}^*(If)$.
* Section 11.4, the conjugate of an indicator function, `Brezis.Chapter11.conjugateC_indicator`:
  $I_M^* = I_{M^\perp}$ for a linear subspace $M$.
* Proposition 11.25, `Brezis.Chapter11.proposition_11_25`: $\varphi^{**} = \varphi$ for a convex,
  lower semicontinuous $\varphi \not\equiv +\infty$.
* Section 11.4, `Brezis.Chapter11.inner_identities`: the algebraic identities of a complex scalar
  product and the Cauchy–Schwarz inequality.
* Section 11.4, `Brezis.Chapter11.inner_L2_complex`: the scalar product of $L^2(\mu; \mathbb{C})$ is
  $\int u \bar{v} \, d\mu$.
* Proposition 11.26, `Brezis.Chapter11.proposition_11_26`: the projection onto a nonempty closed
  convex set and its characterization by $\operatorname{Re}(f - u, v - u) \le 0$.
* Proposition 11.27, `Brezis.Chapter11.proposition_11_27`: every $\varphi \in H^*$ is
  $u \mapsto (u, f)$ for a unique $f \in H$, with $|f| = \|\varphi\|$.
* Proposition 11.28, `Brezis.Chapter11.proposition_11_28`: the Stampacchia theorem for a continuous
  coercive sesquilinear form.
* Proposition 11.28, `Brezis.Chapter11.proposition_11_28_symm`: for a Hermitian form, the solution
  minimizes $\frac12 a(v, v) - \operatorname{Re} \langle \varphi, v \rangle$ on $K$.
* Section 11.4, Lax–Milgram over $\mathbb{C}$, `Brezis.Chapter11.laxMilgram_complex`: for $K = H$
  the inequality becomes $a(u, v) = \overline{\langle \varphi, v \rangle}$ for all $v$, with a
  unique solution.
* Section 11.4, `Brezis.Chapter11.laxMilgram_complex_bijective`: an operator with
  $\operatorname{Re}(Tu, u) \ge \alpha |u|^2$ is bijective.
* Proposition 11.29, `Brezis.Chapter11.proposition_11_29`: an operator with
  $|(Tu, u)| \ge \alpha |u|^2$ is bijective.
* Remark 1, `Brezis.Chapter11.remark_11_1`: (17) implies (18), and (18) implies (17) for $\xi T$
  with some $|\xi| = 1$.
* Section 11.4, `Brezis.Chapter11.spectrum_eq_setOf_not_bijective`: the resolvent set, the spectrum
  and the eigenvalues over $\mathbb{C}$, with $EV(T) \subseteq \sigma(T)$.
* Section 11.4, `Brezis.Chapter11.example_rightShift`: the right shift on $\ell^2$ has no
  eigenvalue.
* Proposition 11.30, `Brezis.Chapter11.proposition_11_30`: $\sigma(T)$ is nonempty, compact and
  contained in $\{|\lambda| \le \|T\|\}$.
* Section 11.4, `Brezis.Chapter11.example_shift_two`: on $\mathbb{C}^2$, $T(u_1, u_2) = (u_2, 0)$
  has $\sigma(T) = \{0\}$ and $\|T\| = 1$.
* Section 11.4, the spectral radius, `Brezis.Chapter11.spectralRadius_eq_lim`:
  $r(T) = \lim_n \|T^n\|^{1/n}$ and $r(T) \le \|T\|$.
* Proposition 11.31, `Brezis.Chapter11.proposition_11_31`: $r(T) = \max\{|\lambda| ; \lambda \in
  \sigma(T)\}$.
* Proposition 11.32, `Brezis.Chapter11.proposition_11_32`: $Q(EV(T)) = EV(Q(T))$ for $\deg Q > 0$
  and $Q(\sigma(T)) = \sigma(Q(T))$; the two displays are
  `Brezis.Chapter11.proposition_11_32_eigenvalue` and `Brezis.Chapter11.proposition_11_32_spectrum`.
* Proposition 11.33, `Brezis.Chapter11.proposition_11_33`: $\sigma(T) \subseteq \overline{W(T)}$,
  the resolvent bound outside $\overline{W(T)}$, and the convexity of $W(T)$.
* Section 11.4, adjoints, `Brezis.Chapter11.adjoint_smul_conj`: $(\lambda T)^* = \bar{\lambda} T^*$
  for the Hilbert adjoint and $(\lambda T)^* = \lambda T^*$ for the Banach adjoint.
* Section 11.4, self-adjoint operators, `Brezis.Chapter11.selfAdjoint_spectrum_subset_real`:
  $(Tu, u) \in \mathbb{R}$, $W(T) \subseteq \mathbb{R}$ and $\sigma(T) \subseteq \mathbb{R}$.
* Proposition 11.34, `Brezis.Chapter11.proposition_11_34`: a compact self-adjoint operator has a
  Hilbert basis of eigenvectors with real eigenvalues.
* Section 11.4, definition of normal operators, `Brezis.Chapter11.isStarNormal_iff`:
  $T^* T = T T^*$, equivalently $|Tu| = |T^* u|$ for all $u$.
* Proposition 11.35, `Brezis.Chapter11.proposition_11_35`: a normal operator has $\max\{|\lambda| ;
  \lambda \in \sigma(T)\} = \|T\|$.
* Proposition 11.36, `Brezis.Chapter11.proposition_11_36`: a compact normal operator has a Hilbert
  basis of eigenvectors.
* Remark 2, `Brezis.Chapter11.remark_11_2`: for a compact normal operator, $\overline{W(T)} =
  \operatorname{conv} \sigma(T)$.
* Section 11.4, definition of isometries and unitary operators,
  `Brezis.Chapter11.unitary_iff_isometry_surjective`: a unitary operator is a surjective isometry.
* Proposition 11.37, `Brezis.Chapter11.proposition_11_37`: for an isometry, $EV(T) \subseteq S^1$,
  $\sigma(T) \subseteq S^1$ if $T$ is unitary, and $\sigma(T)$ is the closed unit disc otherwise;
  the clauses are `Brezis.Chapter11.proposition_11_37_eigenvalue`,
  `Brezis.Chapter11.proposition_11_37_unitary` and `Brezis.Chapter11.proposition_11_37_not_unitary`.
* Section 11.4, skew-adjoint operators, `Brezis.Chapter11.skewAdjoint_iff`: $T^* = -T$ if and only
  if $iT$ is self-adjoint.
* Section 11.4, `Brezis.Chapter11.skewAdjoint_spectrum_subset_imaginary`: for a skew-adjoint
  operator, $EV(T) \subseteq \sigma(T) \subseteq \overline{W(T)} \subseteq i\mathbb{R}$.
* Section 11.4, the paragraph on Chapter 7, `Brezis.Chapter11.hasDerivAt_norm_sq`: $\frac{d}{dt}
  |\varphi|^2 = 2 \operatorname{Re}(\varphi', \varphi)$.

## Conventions

* The scalar product $(u, v)$ of the source is linear in $u$ and conjugate-linear in $v$. Mathlib's
  `⟪u, v⟫_ℂ` is linear in $v$. So $(u, v)$ is `⟪v, u⟫_ℂ`, and in particular $(Tu, u)$ is
  `⟪u, T u⟫_ℂ`, as in the backbone numerical range.
* A form $a(u, v)$ that is linear in $u$ and conjugate-linear in $v$ is `a v u` for
  `a : SesqForm ℂ H`, which is conjugate-linear in its first argument.
* The map $I : f \mapsto \operatorname{Re} f$ is `Brezis.Chapter11.reDual E`. The real results of
  Chapters 1 and 5 are read over $\mathbb{C}$ through it: the closed real hyperplanes and the
  separation of the geometric Hahn–Banach theorem, the conjugate function against the real pairing
  $\operatorname{Re} \langle f, x \rangle$, and the Stampacchia theorem through Theorem 5.6 on
  $H_\mathbb{R}$.
* The set $EV(T)$ of eigenvalues is the set of $\lambda$ with `Module.End.HasEigenvalue T λ`, for
  $T$ viewed as a linear map. The resolvent set and the spectrum are Mathlib's `resolventSet ℂ T`
  and `spectrum ℂ T` in the Banach algebra $\mathcal{L}(E)$.

## Deviations from the source

* **The identities for a complex scalar product** (typo). The displayed expansion of $|u + v|^2$ has
  $|v|^2$ in place of $|u|^2$. See `Brezis.Chapter11.inner_identities`.
* **Proposition 11.32, display (20)** (correction). The identity $Q(EV(T)) = EV(Q(T))$ fails for a
  constant polynomial; the library assumes $\deg Q > 0$. See
  `Brezis.Chapter11.proposition_11_32_eigenvalue`.
* **Proposition 11.34** (generalization). The source assumes $H$ separable. The library states a
  Hilbert basis indexed by a subset of $H$ without separability. See
  `Brezis.Chapter11.proposition_11_34`.
* **Proposition 11.36** (generalization). The source assumes $H$ separable. The library states the
  result without separability. See `Brezis.Chapter11.proposition_11_36`.

## Not formalized

* **The prose comparisons with Chapters 1–7**, such as "Chapter 2. All the statements are
  unchanged".
* **The finite-dimensional motivation** of the spectral theory.
* **The numerical range of $T(u_1, u_2) = (u_2, 0)$.** The computation
  $W(T) = \{|\lambda| \le 1/2\}$.
* **Remark 2, second sentence.** The equality $\overline{W(T)} = \operatorname{conv} \sigma(T)$ for
  every normal operator, which the source quotes from Halmos.
-/

open Filter Metric Module.End Topology
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace Brezis.Chapter11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Chapter 1 over $\mathbb{C}$: the real dual, the Hahn–Banach theorem, conjugate functions -/

/-- **Proposition 11.22** of [brezis2011functional], the map $I$. Let $E$ be a complex normed space.
The map $$I : E^* \to E_\mathbb{R}^*, \qquad If = \operatorname{Re} f,$$ from the complex dual
of $E$ to the real dual of $E_\mathbb{R}$ is a real-linear isometric isomorphism.

The map is the inverse of Mathlib's `StrongDual.extendRCLikeₗᵢ`, whose forward direction is
display (12) of the source. -/
def reDual (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    StrongDual ℂ E ≃ₗᵢ[ℝ] StrongDual ℝ E :=
  (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := E)).symm

/-- The map $I$ of Proposition 11.22 is the real part: for $f \in E^*$ and $x \in E$,
$(If)(x) = \operatorname{Re} f(x)$. -/
@[simp]
theorem reDual_apply (f : StrongDual ℂ E) (x : E) : reDual E f x = (f x).re :=
  rfl

/-- **Display (12)** of [brezis2011functional]. The inverse of $I$ maps $\varphi \in E_\mathbb{R}^*$
to the functional $f \in E^*$ given by $$f(x) = \varphi(x) - i \varphi(ix), \qquad x \in E.$$
-/
theorem reDual_symm_apply (φ : StrongDual ℝ E) (x : E) :
    (reDual E).symm φ x = φ x - Complex.I * φ (Complex.I • x) :=
  rfl

/-- **Proposition 11.22** of [brezis2011functional]. Let $E$ be a complex normed space. The map $I :
f \in E^* \mapsto \operatorname{Re} f \in E_\mathbb{R}^*$ is a bijective isometry from $E^*$
onto $E_\mathbb{R}^*$: there is a real-linear isometric isomorphism $I : E^* \to E_\mathbb{R}^*$
with $(If)(x) = \operatorname{Re} f(x)$ for all $f \in E^*$ and $x \in E$.

The witness is `Brezis.Chapter11.reDual E`. -/
theorem proposition_11_22 :
    ∃ I : StrongDual ℂ E ≃ₗᵢ[ℝ] StrongDual ℝ E, ∀ (f : StrongDual ℂ E) (x : E), I f x = (f x).re :=
  ⟨reDual E, fun _ _ => rfl⟩

/-- **Proposition 11.23** of [brezis2011functional] (Hahn–Banach theorem over $\mathbb{C}$). Let $E$
be a complex normed space, let $G \subseteq E$ be a linear subspace, and let
$g : G \to \mathbb{C}$ be a continuous linear functional. Then there exists $f \in E^*$ that
extends $g$ and satisfies $$\|f\|_{E^*} = \|g\|_{G^*}.$$

The proof is Mathlib's `exists_extension_norm_eq` over `RCLike`, which proceeds as the source
does: Corollary 1.2 on $E_\mathbb{R}$, then Proposition 11.22. -/
theorem proposition_11_23 (G : Submodule ℂ E) (g : StrongDual ℂ G) :
    ∃ f : StrongDual ℂ E, (∀ x : G, f x = g x) ∧ ‖f‖ = ‖g‖ :=
  exists_extension_norm_eq G g

/-- **Section 11.4** of [brezis2011functional], definition of a closed real hyperplane. A set
$H \subseteq E$ is a **closed real hyperplane** if $$H = \{x \in E ; \operatorname{Re} \langle
f, x \rangle = \alpha\} = [\operatorname{Re} f = \alpha]$$ for some $f \in E^*$ with $f \neq 0$
and some $\alpha \in \mathbb{R}$.

For $\alpha = 0$ the set $H$ is a linear subspace of $E_\mathbb{R}$, but not of $E$. -/
def IsClosedRealHyperplane (H : Set E) : Prop :=
  ∃ (f : StrongDual ℂ E) (α : ℝ), f ≠ 0 ∧ H = {x | (f x).re = α}

/-- **Section 11.4** of [brezis2011functional]. A set $H \subseteq E$ is a closed real hyperplane if
and only if $H$ is closed and is a hyperplane $[\varphi = \alpha]$ of $E_\mathbb{R}$, with
$\varphi$ a nonzero real linear functional, in the sense of `Brezis.Chapter01.IsHyperplane`.

By Proposition 1.5 the functional $\varphi$ of a closed hyperplane is continuous, and $\varphi$
and $f$ correspond through Proposition 11.22. -/
theorem isClosedRealHyperplane_iff (H : Set E) :
    IsClosedRealHyperplane H ↔ Chapter01.IsHyperplane H ∧ IsClosed H := by
  constructor
  · rintro ⟨f, α, hf, rfl⟩
    refine ⟨⟨(reDual E f : E →ₗ[ℝ] ℝ), α, fun h => hf ?_, rfl⟩, ?_⟩
    · apply (reDual E).injective
      exact ContinuousLinearMap.coe_injective (by simpa using h)
    · exact isClosed_singleton.preimage (reDual E f).continuous
  · rintro ⟨⟨g, α, hg, rfl⟩, hcl⟩
    have hcont : Continuous g := (Chapter01.proposition_1_5 g hg α).1 hcl
    refine ⟨(reDual E).symm ⟨g, hcont⟩, α, fun h => hg ?_, ?_⟩
    · have := congrArg (reDual E) h
      rw [LinearIsometryEquiv.apply_symm_apply, map_zero] at this
      exact LinearMap.ext fun x => congrArg (fun φ : StrongDual ℝ E => φ x) this
    · ext x
      simp only [Set.mem_ofPred_eq, ← reDual_apply, LinearIsometryEquiv.apply_symm_apply]
      rfl

/-- **Section 11.4** of [brezis2011functional], definition of separation. For $f \in E^*$ and
$\alpha \in \mathbb{R}$, the hyperplane $[\operatorname{Re} f = \alpha]$ **separates** the sets
$A, B \subseteq E$ if $\operatorname{Re} \langle f, x \rangle \le \alpha$ for all $x \in A$ and
$\operatorname{Re} \langle f, x \rangle \ge \alpha$ for all $x \in B$. -/
def SeparatesRe (f : StrongDual ℂ E) (α : ℝ) (A B : Set E) : Prop :=
  (∀ x ∈ A, (f x).re ≤ α) ∧ ∀ x ∈ B, α ≤ (f x).re

/-- **Section 11.4** of [brezis2011functional]. The hyperplane $[\operatorname{Re} f = \alpha]$
separates $A$ and $B$ if and only if the hyperplane $[If = \alpha]$ of $E_\mathbb{R}$ separates
them in the sense of `Brezis.Chapter01.Separates`. -/
theorem separatesRe_iff (f : StrongDual ℂ E) (α : ℝ) (A B : Set E) :
    SeparatesRe f α A B ↔ Chapter01.Separates (reDual E f : E →ₗ[ℝ] ℝ) α A B :=
  Iff.rfl

/-- **Proposition 11.24** of [brezis2011functional] (geometric Hahn–Banach theorem over
$\mathbb{C}$). Let $E$ be a complex normed space, and let $A, B \subseteq E$ be two nonempty
disjoint convex sets, one of which is open. Then there exist $f \in E^*$ with $f \neq 0$ and
$\alpha \in \mathbb{R}$ such that the closed real hyperplane $[\operatorname{Re} f = \alpha]$
separates $A$ and $B$.

The proof applies Theorem 1.6 on $E_\mathbb{R}$, then Proposition 11.22. -/
theorem proposition_11_24 {A B : Set E} (hA : Convex ℝ A) (hAne : A.Nonempty) (hB : Convex ℝ B)
    (hBne : B.Nonempty) (hAB : Disjoint A B) (hopen : IsOpen A ∨ IsOpen B) :
    ∃ (f : StrongDual ℂ E) (α : ℝ), f ≠ 0 ∧ SeparatesRe f α A B := by
  obtain ⟨g, α, hg, hcl, hsep⟩ := Chapter01.theorem_1_6 hA hAne hB hBne hAB hopen
  have hcont : Continuous g := (Chapter01.proposition_1_5 g hg α).1 hcl
  refine ⟨(reDual E).symm ⟨g, hcont⟩, α, fun h => hg ?_, ?_⟩
  · have := congrArg (reDual E) h
    rw [LinearIsometryEquiv.apply_symm_apply, map_zero] at this
    exact LinearMap.ext fun x => congrArg (fun φ : StrongDual ℝ E => φ x) this
  · rw [separatesRe_iff, LinearIsometryEquiv.apply_symm_apply]
    exact hsep

/-- **Section 11.4** of [brezis2011functional], the orthogonal over $\mathbb{C}$. Let $M$ be a
linear subspace of $E$. Then $$M^\perp = \{f \in E^* ; \langle f, x \rangle = 0 \ \forall x \in
M\} = \{f \in E^* ; \operatorname{Re} \langle f, x \rangle = 0 \ \forall x \in M\},$$ and
$M^{\perp\perp} = \overline{M}$.

The source says that the definition of $M^\perp$ is unchanged, and the second description
follows by taking $ix$ in place of $x$. As in Chapter 1, $M^\perp$ is `M.strongDualAnnihilator`,
and $M^{\perp\perp} \subseteq E$ is its `Submodule.strongDualCoannihilator`. -/
theorem orthogonal_complex (M : Submodule ℂ E) :
    (∀ f : StrongDual ℂ E, f ∈ M.strongDualAnnihilator ↔ ∀ x ∈ M, f x = 0) ∧
      (∀ f : StrongDual ℂ E, f ∈ M.strongDualAnnihilator ↔ ∀ x ∈ M, (f x).re = 0) ∧
      M.strongDualAnnihilator.strongDualCoannihilator = M.topologicalClosure := by
  refine ⟨fun f => Submodule.mem_strongDualAnnihilator, fun f => ?_,
    M.strongDualCoannihilator_strongDualAnnihilator⟩
  rw [Submodule.mem_strongDualAnnihilator]
  refine ⟨fun h x hx => by rw [h x hx, Complex.zero_re], fun h x hx => ?_⟩
  have him := h (Complex.I • x) (M.smul_mem _ hx)
  rw [map_smul, smul_eq_mul, Complex.I_mul_re, neg_eq_zero] at him
  exact Complex.ext (h x hx) him

/-- **Section 11.4** of [brezis2011functional], the real pairing. The real bilinear pairing of $E$
with its complex dual is $$\langle x, f \rangle \mapsto \operatorname{Re} \langle f, x \rangle,
\qquad x \in E, \ f \in E^*.$$

It is the pairing of $E_\mathbb{R}$ with $E_\mathbb{R}^*$ of Chapter 1, composed with the map
$I$ of Proposition 11.22. The conjugate of a function on a complex space is taken against this
pairing. -/
def rePairing (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    E →ₗ[ℝ] StrongDual ℂ E →ₗ[ℝ] ℝ :=
  (topDualPairing ℝ E).flip.compl₂ (reDual E).toLinearEquiv.toLinearMap

/-- The real pairing `Brezis.Chapter11.rePairing` of $x \in E$ and $f \in E^*$ is
$\operatorname{Re} \langle f, x \rangle$. -/
@[simp]
theorem rePairing_apply (x : E) (f : StrongDual ℂ E) : rePairing E x f = (f x).re :=
  rfl

/-- **Section 11.4** of [brezis2011functional], definition of the conjugate function. Given
$\varphi : E \to (-\infty, +\infty]$, its **conjugate** $\varphi^* : E^* \to [-\infty, +\infty]$
is $$\varphi^*(f) = \sup_{x \in E} \{\operatorname{Re} \langle f, x \rangle - \varphi(x)\}.$$

As in Chapter 1, the function $\varphi$ has values in `EReal`. The definition is the backbone's
`ConvexAnalysis.convexConj` against the pairing `Brezis.Chapter11.rePairing E`. -/
def conjugateC (φ : E → EReal) : StrongDual ℂ E → EReal :=
  ConvexAnalysis.convexConj (rePairing E) φ

/-- The conjugate function of Section 11.4 is the supremum of its definition: for
$\varphi : E \to [-\infty, +\infty]$ and $f \in E^*$, $\varphi^*(f) = \sup_{x \in E}
\{\operatorname{Re} \langle f, x \rangle - \varphi(x)\}$. -/
theorem conjugateC_apply (φ : E → EReal) (f : StrongDual ℂ E) :
    conjugateC φ f = ⨆ x : E, (((f x).re : ℝ) : EReal) - φ x :=
  rfl

/-- **Section 11.4** of [brezis2011functional]. "With obvious notation we have
$\varphi^*(f) = \varphi_\mathbb{R}^*(If)$ for all $f \in E^*$": the conjugate of
$\varphi : E \to [-\infty, +\infty]$ over $\mathbb{C}$ is the real conjugate
$\varphi_\mathbb{R}^*$ of Chapter 1 on $E_\mathbb{R}$, evaluated at $If$.

The real conjugate is taken against the pairing `(topDualPairing ℝ E).flip` of $E_\mathbb{R}$
with $E_\mathbb{R}^*$. -/
theorem conjugateC_eq (φ : E → EReal) (f : StrongDual ℂ E) :
    conjugateC φ f = ConvexAnalysis.convexConj (topDualPairing ℝ E).flip φ (reDual E f) :=
  rfl

/-- **Section 11.4** of [brezis2011functional], the biconjugate over $\mathbb{C}$. Given
$\varphi : E \to (-\infty, +\infty]$, its **biconjugate** is the function on $E$
$$\varphi^{**}(x) = \sup_{f \in E^*} \{\operatorname{Re} \langle f, x \rangle -
\varphi^*(f)\}.$$

The definition is the backbone's `ConvexAnalysis.convexBiconj` against
`Brezis.Chapter11.rePairing E`. -/
def biconjugateC (φ : E → EReal) : E → EReal :=
  ConvexAnalysis.convexBiconj (rePairing E) φ

/-- The biconjugate of Section 11.4 is the supremum of its definition: for
$\varphi : E \to [-\infty, +\infty]$ and $x \in E$, $\varphi^{**}(x) = \sup_{f \in E^*}
\{\operatorname{Re} \langle f, x \rangle - \varphi^*(f)\}$. -/
theorem biconjugateC_apply (φ : E → EReal) (x : E) :
    biconjugateC φ x = ⨆ f : StrongDual ℂ E, (((f x).re : ℝ) : EReal) - conjugateC φ f :=
  rfl

/-- **Section 11.4** of [brezis2011functional], the conjugate of an indicator function. Let $M$ be a
linear subspace of $E$ and let $\varphi = I_M$ be its indicator function. Then $$\varphi^*(f) =
\sup_{x \in M} \operatorname{Re} \langle f, x \rangle = I_{M^\perp}(f), \qquad f \in E^*.$$

The indicator functions are `ConvexAnalysis.indicatorFn`. If $f \notin M^\perp$, some
$x_0 \in M$ has $\langle f, x_0 \rangle \neq 0$, and $x_1 = \overline{\langle f, x_0 \rangle}
x_0 \in M$ has $\operatorname{Re} \langle f, x_1 \rangle = |\langle f, x_0 \rangle|^2 > 0$, so
that the supremum is $+\infty$; the source rotates $x_0$ by $i$ or $-1$ instead. -/
theorem conjugateC_indicator (M : Submodule ℂ E) :
    conjugateC (ConvexAnalysis.indicatorFn (M : Set E)) =
      ConvexAnalysis.indicatorFn (M.strongDualAnnihilator : Set (StrongDual ℂ E)) := by
  funext f
  rw [conjugateC_apply]
  by_cases hf : f ∈ M.strongDualAnnihilator
  · rw [ConvexAnalysis.indicatorFn_of_mem hf]
    refine le_antisymm (iSup_le fun x => ?_) (le_iSup_of_le (0 : E) ?_)
    · by_cases hx : x ∈ M
      · rw [ConvexAnalysis.indicatorFn_of_mem hx, Submodule.mem_strongDualAnnihilator.1 hf x hx]
        simp
      · rw [ConvexAnalysis.indicatorFn_of_notMem hx, EReal.sub_top]
        exact bot_le
    · rw [ConvexAnalysis.indicatorFn_of_mem M.zero_mem]
      simp
  · rw [ConvexAnalysis.indicatorFn_of_notMem hf]
    obtain ⟨x₀, hx₀, hfx₀⟩ : ∃ x ∈ M, f x ≠ 0 := by
      by_contra h
      push Not at h
      exact hf (Submodule.mem_strongDualAnnihilator.2 h)
    -- a vector of `M` on which `Re f` is positive
    set x₁ : E := conj (f x₀) • x₀ with hx₁
    have hx₁M : x₁ ∈ M := M.smul_mem _ hx₀
    have hpos : 0 < (f x₁).re := by
      rw [hx₁, map_smul, smul_eq_mul, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
      positivity
    rw [iSup_eq_top]
    intro b hb
    induction b with
    | bot =>
      refine ⟨x₁, ?_⟩
      rw [ConvexAnalysis.indicatorFn_of_mem hx₁M, sub_zero]
      exact EReal.bot_lt_coe _
    | coe r =>
      -- scale `x₁` so that `Re f` exceeds `r`
      set t : ℝ := (|r| + 1) / (f x₁).re with ht
      refine ⟨(t : ℂ) • x₁, ?_⟩
      rw [ConvexAnalysis.indicatorFn_of_mem (M.smul_mem _ hx₁M), sub_zero, map_smul, smul_eq_mul,
        Complex.re_ofReal_mul, ht, div_mul_cancel₀ _ hpos.ne', EReal.coe_lt_coe_iff]
      linarith [le_abs_self r]
    | top => exact absurd hb (lt_irrefl _)

/-- **Proposition 11.25** of [brezis2011functional] (Fenchel–Moreau theorem over $\mathbb{C}$). Let
$E$ be a complex normed space, and let $\varphi : E \to (-\infty, +\infty]$ be convex and lower
semicontinuous with $\varphi \not\equiv +\infty$. Then $\varphi^{**} = \varphi$.

The hypothesis that $\varphi$ takes values in $(-\infty, +\infty]$ is `∀ x, φ x ≠ ⊥`, and
$\varphi \not\equiv +\infty$ is the nonemptiness of `ConvexAnalysis.convexDom φ`. The proof is
the first method of the source: Theorem 1.11 on $E_\mathbb{R}$, with
$\varphi^*(f) = \varphi_\mathbb{R}^*(If)$ by `Brezis.Chapter11.conjugateC_eq`, so that the
supremum defining $\varphi^{**}(x)$ is the real one reindexed along the bijection $I$. -/
theorem proposition_11_25 {φ : E → EReal} (hφ : ConvexAnalysis.ConvexFn φ)
    (hl : LowerSemicontinuous φ) (hbot : ∀ x, φ x ≠ ⊥)
    (hdom : (ConvexAnalysis.convexDom φ).Nonempty) : biconjugateC φ = φ := by
  funext x
  refine Eq.trans ?_ (congrFun (Chapter01.theorem_1_11 hφ hl hbot hdom) x)
  rw [biconjugateC_apply, Chapter01.biconjugate_apply]
  exact (reDual E).toEquiv.iSup_comp
    (g := fun g : StrongDual ℝ E => ((g x : ℝ) : EReal) - Chapter01.conjugate φ g)

/-! ### Chapter 5 over $\mathbb{C}$: complex Hilbert spaces -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

-- the book's `H_ℝ`: the real Hilbert space structure `Re ⟪u, v⟫` on `H`
attribute [local instance] InnerProductSpace.complexToReal

/-- **Section 11.4** of [brezis2011functional], the identities of the paragraph on Chapter 5. Let
$H$ be a complex inner product space, let $u, v \in H$ and $\lambda, \mu \in \mathbb{C}$. Then
$(\lambda u, \mu v) = \lambda \bar{\mu} (u, v)$, $$|u + v|^2 = |u|^2 + 2 \operatorname{Re}(u,
v) + |v|^2,$$ $|(u, v)| \le |u| |v|$ (the Cauchy–Schwarz inequality), and the real scalar
product of $H_\mathbb{R}$ is $\operatorname{Re}(u, v)$.

**Typo.** The displayed expansion of $|u + v|^2$ in the source has $|v|^2$ in place of $|u|^2$.

The Lean statement is in Mathlib's convention, with $(u, v)$ = `⟪v, u⟫_ℂ`: the first identity
reads `⟪l • u, m • v⟫_ℂ = conj l * m * ⟪u, v⟫_ℂ`. The real structure on $H_\mathbb{R}$ is
Mathlib's `InnerProductSpace.complexToReal`, which makes $H_\mathbb{R}$ a real Hilbert space
when $H$ is complete. -/
theorem inner_identities (u v : H) (l m : ℂ) :
    ⟪l • u, m • v⟫_ℂ = conj l * m * ⟪u, v⟫_ℂ ∧
      ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * (⟪u, v⟫_ℂ).re + ‖v‖ ^ 2 ∧
      ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ ∧ ⟪u, v⟫_ℝ = (⟪u, v⟫_ℂ).re :=
  ⟨by rw [inner_smul_left, inner_smul_right, mul_assoc], norm_add_sq (𝕜 := ℂ) u v,
    norm_inner_le_norm u v, rfl⟩

/-- **Section 11.4** of [brezis2011functional], the typical example. Let $\mu$ be a measure on a
measurable space. For $u, v \in L^2(\mu; \mathbb{C})$, the scalar product is $$(u, v) = \int u
\bar{v} \, d\mu.$$

In Mathlib's convention the statement is `⟪v, u⟫_ℂ = ∫ x, u x * conj (v x) ∂μ`. The source takes
the measure space $\Omega$. -/
theorem inner_L2_complex {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (u v : MeasureTheory.Lp ℂ 2 μ) : ⟪v, u⟫_ℂ = ∫ x, u x * conj (v x) ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply]

/-- **Proposition 11.26** of [brezis2011functional] (projection onto a closed convex set over
$\mathbb{C}$). Let $H$ be a complex Hilbert space, let $K \subseteq H$ be a nonempty closed
convex set, and let $f \in H$. Then there exists a unique $u \in K$ such that $$|f - u| =
\min_{v \in K} |f - v|.$$ An element $u$ has this property if and only if $u \in K$ and
$|f - u| = \operatorname{dist}(f, K)$, and also if and only if $u \in K$ and
$$\operatorname{Re}(f - u, v - u) \le 0 \quad \text{for all } v \in K.$$

The property "$u \in K$ and $|f - u| \le |f - v|$ for all $v \in K$" is the backbone predicate
`IsBestApprox K f u`. The proof is Theorem 5.2 on $H_\mathbb{R}$, whose scalar product is
$\operatorname{Re}(u, v)$. -/
theorem proposition_11_26 [CompleteSpace H] {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (f : H) :
    (∃! u, IsBestApprox K f u) ∧
      (∀ u, IsBestApprox K f u ↔ u ∈ K ∧ ‖f - u‖ = infDist f K) ∧
      ∀ u, IsBestApprox K f u ↔ u ∈ K ∧ ∀ v ∈ K, (⟪f - u, v - u⟫_ℂ).re ≤ 0 :=
  ⟨Chapter05.theorem_5_2 hne hcl hK f,
    fun _ => ⟨fun h => ⟨h.1, (Chapter05.theorem_5_2_infDist h.1).1 h⟩,
      fun h => (Chapter05.theorem_5_2_infDist h.1).2 h.2⟩,
    fun _ => ⟨fun h => ⟨h.1, (Chapter05.theorem_5_2_iff hK h.1).1 h⟩,
      fun h => (Chapter05.theorem_5_2_iff hK h.1).2 h.2⟩⟩

/-- **Proposition 11.27** of [brezis2011functional] (Riesz–Fréchet theorem over $\mathbb{C}$). Let
$H$ be a complex Hilbert space and let $\varphi \in H^*$. Then there exists a unique $f \in H$
such that $$\varphi(u) = (u, f) \quad \text{for all } u \in H,$$ and this $f$ satisfies
$|f| = \|\varphi\|_{H^*}$.

In Mathlib's convention the condition is `φ u = ⟪f, u⟫_ℂ`. The proof is Mathlib's
`InnerProductSpace.toDual`, stated over `RCLike`. -/
theorem proposition_11_27 [CompleteSpace H] (φ : StrongDual ℂ H) :
    (∃! f : H, ∀ u, φ u = ⟪f, u⟫_ℂ) ∧ ∀ f : H, (∀ u, φ u = ⟪f, u⟫_ℂ) → ‖f‖ = ‖φ‖ := by
  have hrep : ∀ f : H, (∀ u, φ u = ⟪f, u⟫_ℂ) → InnerProductSpace.toDual ℂ H f = φ :=
    fun f hf => ContinuousLinearMap.ext fun u => by
      rw [InnerProductSpace.toDual_apply_apply, hf u]
  refine ⟨⟨(InnerProductSpace.toDual ℂ H).symm φ, fun u => ?_, fun f hf => ?_⟩, fun f hf => ?_⟩
  · rw [InnerProductSpace.toDual_symm_apply]
  · rw [← hrep f hf, LinearIsometryEquiv.symm_apply_apply]
  · rw [← hrep f hf, LinearIsometryEquiv.norm_map]

/-- The real bilinear form $(u, v) \mapsto \operatorname{Re} a(u, v)$ on $H_\mathbb{R}$ of a
sesquilinear form $a$ that satisfies (13). -/
private def reBilin (a : SesqForm ℂ H) : Chapter05.BilinForm H :=
  LinearMap.mk₂ ℝ (fun u v => (a v u).re)
    (fun u₁ u₂ v => by rw [map_add, Complex.add_re])
    (fun c u v => by
      rw [← Complex.coe_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul, smul_eq_mul])
    (fun u v₁ v₂ => by rw [map_add, add_apply, Complex.add_re])
    (fun c u v => by
      rw [← Complex.coe_smul, map_smulₛₗ, smul_apply, smul_eq_mul, Complex.conj_ofReal,
        Complex.re_ofReal_mul, smul_eq_mul])

private theorem reBilin_apply (a : SesqForm ℂ H) (u v : H) : reBilin a u v = (a v u).re :=
  rfl

private theorem reBilin_isContinuousWith (a : SesqForm ℂ H) :
    (reBilin a).IsContinuousWith ‖a‖ := fun u v => by
  rw [reBilin_apply]
  calc |(a v u).re| ≤ ‖a v u‖ := Complex.abs_re_le_norm _
    _ ≤ ‖a‖ * ‖v‖ * ‖u‖ := a.le_opNorm₂ v u
    _ = ‖a‖ * ‖u‖ * ‖v‖ := by ring

private theorem reBilin_isCoerciveWith (a : SesqForm ℂ H) {α : ℝ} (ha : a.IsCoerciveWith α) :
    (reBilin a).IsCoerciveWith α := fun v => ha v

/-- **Proposition 11.28** of [brezis2011functional] (Stampacchia theorem over $\mathbb{C}$). Let $H$
be a complex Hilbert space, and let $a : H \times H \to \mathbb{C}$ be linear in the first
argument and conjugate-linear in the second (13), continuous (14), and coercive (15):
$\operatorname{Re} a(v, v) \ge \alpha |v|^2$ for all $v \in H$, with $\alpha > 0$. Let $K$ be a
nonempty closed convex set in $H$. Then for every $\varphi \in H^*$ there exists a unique
$u \in K$ such that $$\operatorname{Re} a(u, v - u) \ge \operatorname{Re} \langle \varphi, v - u
\rangle \quad \text{for all } v \in K. \tag{16}$$

The form $a(u, v)$ is `a v u` for `a : SesqForm ℂ H`; the continuity (14) is part of the type
`SesqForm`, and the coercivity is `SesqForm.IsCoerciveWith`. The proof is the one of the source:
Theorem 5.6 on $H_\mathbb{R}$ for the real form $\operatorname{Re} a$ and the real functional
$\operatorname{Re} \varphi$. -/
theorem proposition_11_28 [CompleteSpace H] (a : SesqForm ℂ H) {α : ℝ} (hα : 0 < α)
    (ha : a.IsCoerciveWith α) {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K)
    (hK : Convex ℝ K) (φ : StrongDual ℂ H) :
    ∃! u, u ∈ K ∧ ∀ v ∈ K, (φ (v - u)).re ≤ (a (v - u) u).re :=
  Chapter05.theorem_5_6 (reBilin_isContinuousWith a) hα (reBilin_isCoerciveWith a ha) hne hcl hK
    (reDual H φ)

/-- **Proposition 11.28** of [brezis2011functional], the case of a Hermitian form. Under the
hypotheses of `Brezis.Chapter11.proposition_11_28`, assume moreover that
$a(v, w) = \overline{a(w, v)}$ for all $v, w \in H$. Then $u$ satisfies $u \in K$ and (16) if
and only if $u \in K$ and $$\frac12 a(u, u) - \operatorname{Re} \langle \varphi, u \rangle =
\min_{v \in K} \Bigl\{\frac12 a(v, v) - \operatorname{Re} \langle \varphi, v \rangle\Bigr\}.$$
This minimizer exists and is unique.

For a Hermitian form $a(v, v)$ is real, so the Lean statement writes it as
$\operatorname{Re} a(v, v)$. The hypothesis is `SesqForm.IsHermitian`. -/
theorem proposition_11_28_symm [CompleteSpace H] (a : SesqForm ℂ H) {α : ℝ} (hα : 0 < α)
    (ha : a.IsCoerciveWith α) (hs : a.IsHermitian) {K : Set H} (hne : K.Nonempty)
    (hcl : IsClosed K) (hK : Convex ℝ K) (φ : StrongDual ℂ H) :
    (∀ u, (u ∈ K ∧ ∀ v ∈ K, (φ (v - u)).re ≤ (a (v - u) u).re) ↔
        (u ∈ K ∧ IsMinOn (fun v => 1 / 2 * (a v v).re - (φ v).re) K u)) ∧
      ∃! u, u ∈ K ∧ IsMinOn (fun v => 1 / 2 * (a v v).re - (φ v).re) K u := by
  have hsymm : LinearMap.BilinForm.IsSymm (reBilin a) :=
    LinearMap.BilinForm.isSymm_def.2 fun u v => by
      rw [reBilin_apply, reBilin_apply, hs v u, Complex.conj_re]
  exact Chapter05.theorem_5_6_symm (reBilin_isContinuousWith a) hα (reBilin_isCoerciveWith a ha)
    hsymm hne hcl hK (reDual H φ)

/-- **Section 11.4** of [brezis2011functional], the Lax–Milgram theorem over $\mathbb{C}$. Let $H$
be a complex Hilbert space, let $a$ be a continuous sesquilinear form with
$\operatorname{Re} a(v, v) \ge \alpha |v|^2$ for all $v$, where $\alpha > 0$, and let
$\varphi \in H^*$. "When $K = H$, (16) becomes $a(u, v) = \overline{\langle \varphi, v \rangle}$
for all $v \in H$": an element $u$ satisfies (16) for $K = H$ if and only if $$a(u, v) =
\overline{\langle \varphi, v \rangle} \quad \text{for all } v \in H,$$ and exactly one $u \in H$
has this property.

In Mathlib's convention the equation is `a v u = conj (φ v)`. The proof applies the backbone's
`SesqForm.laxMilgram` to the form $(u, v) \mapsto \overline{a(u, v)}$. -/
theorem laxMilgram_complex [CompleteSpace H] (a : SesqForm ℂ H) {α : ℝ} (hα : 0 < α)
    (ha : a.IsCoerciveWith α) (φ : StrongDual ℂ H) :
    (∀ u, (∀ v, (φ (v - u)).re ≤ (a (v - u) u).re) ↔ ∀ v, a v u = conj (φ v)) ∧
      ∃! u, ∀ v, a v u = conj (φ v) := by
  have key : ∀ u, (∀ v, (φ (v - u)).re ≤ (a (v - u) u).re) ↔ ∀ v, a v u = conj (φ v) := by
    intro u
    constructor
    · intro h
      -- `v - u` ranges over all of `H`
      have h' : ∀ w, (φ w).re ≤ (a w u).re := fun w => by simpa using h (w + u)
      intro w
      have h1 : (φ w).re = (a w u).re := by
        have := h' (-w)
        rw [map_neg, map_neg, neg_apply, Complex.neg_re, Complex.neg_re,
          neg_le_neg_iff] at this
        exact le_antisymm (h' w) this
      have h2 : (φ w).im = -(a w u).im := by
        have := h' (Complex.I • w)
        rw [map_smul, map_smulₛₗ, smul_apply, smul_eq_mul, smul_eq_mul,
          Complex.I_mul_re, Complex.conj_I, neg_mul, Complex.neg_re, Complex.I_mul_re,
          neg_neg, neg_le] at this
        have := h' (-(Complex.I • w))
        rw [map_neg, map_neg, neg_apply, Complex.neg_re, Complex.neg_re,
          map_smul, map_smulₛₗ, smul_apply, smul_eq_mul, smul_eq_mul,
          Complex.I_mul_re, Complex.conj_I, neg_mul, Complex.neg_re, Complex.I_mul_re] at this
        linarith
      exact Complex.ext (by rw [Complex.conj_re, h1]) (by rw [Complex.conj_im, h2, neg_neg])
    · intro h v
      rw [h (v - u), Complex.conj_re]
  refine ⟨key, ?_⟩
  -- the book's `a(u, v)` is linear in `u`; the backbone's Lax–Milgram puts the unknown in the
  -- conjugate-linear slot, so it is applied to the flipped form `(u, v) ↦ conj (a v u)`
  set a' : SesqForm ℂ H := SesqForm.ofOperator (ContinuousLinearMap.adjoint (SesqForm.toOperator a))
  have ha' : ∀ u v, a' u v = conj (a v u) := fun u v => by
    rw [SesqForm.ofOperator_apply, ContinuousLinearMap.adjoint_inner_left, ← inner_conj_symm,
      SesqForm.inner_toOperator]
  have hcoer : a'.IsCoerciveWith α := fun v => by
    rw [ha']
    exact (ha v).trans_eq (RCLike.conj_re _).symm
  refine (existsUnique_congr fun u => forall_congr' fun v => ?_).1 (a'.laxMilgram φ hα hcoer)
  rw [ha']
  exact ⟨fun h => by rw [← h, Complex.conj_conj], fun h => by rw [h, Complex.conj_conj]⟩

/-- **Proposition 11.29** of [brezis2011functional] (Lax–Milgram theorem, modulus form). Let $H$ be
a complex Hilbert space and let $T \in \mathcal{L}(H)$ satisfy $$|(Tu, u)| \ge \alpha |u|^2
\quad \text{for all } u \in H \tag{18}$$ for some $\alpha > 0$. Then $T$ is bijective from $H$
onto $H$.

The source refers to Remark 8 of Chapter 5: $T$ is injective with closed range because
$\alpha |u| \le |Tu|$, and its range is dense because $v \perp R(T)$ gives
$\alpha |v|^2 \le |(Tv, v)| = 0$. Mathlib's
`ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map` is this argument. -/
theorem proposition_11_29 [CompleteSpace H] (T : H →L[ℂ] H) {α : ℝ} (hα : 0 < α)
    (h : ∀ u, α * ‖u‖ ^ 2 ≤ ‖⟪u, T u⟫_ℂ‖) : Function.Bijective T :=
  ContinuousLinearMap.isUnit_iff_bijective.1 <|
    ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map T (c := ⟨α, hα.le⟩) hα fun u => by
      rw [← inner_conj_symm, RCLike.norm_conj, mul_comm]
      exact h u

/-- **Section 11.4** of [brezis2011functional]. "In particular any operator $T \in \mathcal{L}(H)$
satisfying $$\operatorname{Re}(Tu, u) \ge \alpha |u|^2 \quad \text{for all } u \in H, \tag{17}$$
for some $\alpha > 0$, is bijective from $H$ onto itself." Here $H$ is a complex Hilbert space.

The scalar product $(Tu, u)$ of the source is `⟪u, T u⟫_ℂ`. -/
theorem laxMilgram_complex_bijective [CompleteSpace H] (T : H →L[ℂ] H) {α : ℝ} (hα : 0 < α)
    (h : ∀ u, α * ‖u‖ ^ 2 ≤ (⟪u, T u⟫_ℂ).re) : Function.Bijective T :=
  proposition_11_29 T hα fun u => (h u).trans (Complex.re_le_norm _)

/-- **Remark 1** of [brezis2011functional], Section 11.4. Let $H$ be a complex inner product space,
$T \in \mathcal{L}(H)$ and $\alpha > 0$. Clearly (17) implies (18). Conversely, if (18) holds,
then there exists $\xi \in \mathbb{C}$ with $|\xi| = 1$ such that $$\operatorname{Re}(\xi T u,
u) \ge \alpha |u|^2 \quad \text{for all } u \in H. \tag{19}$$

For the converse, the numerical range $W(T)$ is convex (Proposition 11.33) and has distance at
least $\alpha$ from $0$, and a rotation moves the projection of $0$ onto $\overline{W(T)}$ to
the positive real axis. -/
theorem remark_11_1 (T : H →L[ℂ] H) {α : ℝ} (hα : 0 < α) :
    ((∀ u, α * ‖u‖ ^ 2 ≤ (⟪u, T u⟫_ℂ).re) → ∀ u, α * ‖u‖ ^ 2 ≤ ‖⟪u, T u⟫_ℂ‖) ∧
      ((∀ u, α * ‖u‖ ^ 2 ≤ ‖⟪u, T u⟫_ℂ‖) →
        ∃ ξ : ℂ, ‖ξ‖ = 1 ∧ ∀ u, α * ‖u‖ ^ 2 ≤ (⟪u, (ξ • T) u⟫_ℂ).re) :=
  ⟨fun h u => (h u).trans (Complex.re_le_norm _),
    fun h => T.exists_re_inner_smul_ge_of_norm_inner_ge hα h⟩

end Hilbert

/-! ### Chapter 6 over $\mathbb{C}$: resolvent set, spectrum, eigenvalues, spectral radius -/

section Banach

variable [CompleteSpace E]

/-- **Section 11.4** of [brezis2011functional], the definitions of Section 6.3 over $\mathbb{C}$.
Let $E$ be a complex Banach space and $T \in \mathcal{L}(E)$. Then the resolvent set is
$$\rho(T) = \{\lambda \in \mathbb{C} ; T - \lambda I \text{ is bijective from } E \text{ onto }
E\},$$ the spectrum is $\sigma(T) = \mathbb{C} \setminus \rho(T)$, a number $\lambda$ is an
eigenvalue of $T$ if and only if $N(T - \lambda I) \neq \{0\}$, and $EV(T) \subseteq \sigma(T)$.

The resolvent set is Mathlib's `resolventSet ℂ T`, defined by invertibility in $\mathcal{L}(E)$.
It agrees with the bijectivity condition by the open mapping theorem, which needs the
completeness of $E$. The spectrum is `spectrum ℂ T`, and an eigenvalue is
`Module.End.HasEigenvalue`. -/
theorem spectrum_eq_setOf_not_bijective (T : E →L[ℂ] E) :
    resolventSet ℂ T = {l | Function.Bijective ((T - l • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E → E)} ∧
      spectrum ℂ T = (resolventSet ℂ T)ᶜ ∧
      (∀ l : ℂ, Module.End.HasEigenvalue (T : Module.End ℂ E) l ↔
        LinearMap.ker ((T : E →ₗ[ℂ] E) - l • 1) ≠ ⊥) ∧
      {l | Module.End.HasEigenvalue (T : Module.End ℂ E) l} ⊆ spectrum ℂ T := by
  refine ⟨?_, rfl, fun l => ?_, fun l hl => ?_⟩
  · ext l
    rw [spectrum.mem_resolventSet_iff, Set.mem_ofPred_eq, ← IsUnit.neg_iff, neg_sub,
      Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.isUnit_iff_bijective]
  · rw [← Module.End.eigenspace_def]
    exact Iff.rfl
  · rw [ContinuousLinearMap.spectrum_eq]
    exact hl.mem_spectrum

end Banach

/-! ### The right shift on $\ell^2$ -/

section RightShift

variable (𝕜 : Type*) [RCLike 𝕜]

/-- **Section 11.4** of [brezis2011functional], the right shift. For $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, the **right shift** on $\ell^2(\mathbb{N}; \mathbb{K})$ is $$Tu = (0, u_1, u_2,
\dots).$$ It is an isometry, see `Brezis.Chapter11.norm_rightShift_apply`.

The operator is the backbone's `lp.shiftRightL 𝕜`. Sequences are indexed from $0$, so
$(Tu)_0 = 0$ and $(Tu)_{n+1} = u_n$. -/
def rightShift : lp (fun _ : ℕ => 𝕜) 2 →L[𝕜] lp (fun _ : ℕ => 𝕜) 2 :=
  lp.shiftRightL 𝕜

/-- The first entry of the image under the right shift $T$ is zero: $(Tu)_0 = 0$. -/
@[simp]
theorem rightShift_apply_zero (u : lp (fun _ : ℕ => 𝕜) 2) : rightShift 𝕜 u 0 = 0 :=
  lp.shiftRightL_apply_zero 𝕜 u

/-- The right shift $T$ moves every entry one place to the right: $(Tu)_{n+1} = u_n$. -/
@[simp]
theorem rightShift_apply_succ (u : lp (fun _ : ℕ => 𝕜) 2) (n : ℕ) :
    rightShift 𝕜 u (n + 1) = u n :=
  lp.shiftRightL_apply_succ 𝕜 u n

/-- The right shift $T$ is an isometry: $\|Tu\| = \|u\|$ for every $u \in \ell^2$. -/
theorem norm_rightShift_apply (u : lp (fun _ : ℕ => 𝕜) 2) : ‖rightShift 𝕜 u‖ = ‖u‖ :=
  lp.norm_shiftRightL_apply 𝕜 u

end RightShift

/-- **Section 11.4** of [brezis2011functional]. "It may happen that $EV(T) = \emptyset$": the right
shift $Tu = (0, u_1, u_2, \dots)$ on $\ell^2(\mathbb{N}; \mathbb{C})$ has no eigenvalue, that
is, no $\lambda \in \mathbb{C}$ is an eigenvalue of $T$.

If $Tu = \lambda u$, then $\lambda u_0 = 0$ and $u_n = \lambda u_{n+1}$ for all $n$. For
$\lambda = 0$ this gives $u = 0$ directly, and for $\lambda \neq 0$ it gives $u_0 = 0$ and then
$u_n = 0$ by induction. -/
theorem example_rightShift (l : ℂ) :
    ¬ Module.End.HasEigenvalue ((rightShift ℂ : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] _) :
      Module.End ℂ (lp (fun _ : ℕ => ℂ) 2)) l := by
  intro hl
  obtain ⟨u, hu⟩ := hl.exists_hasEigenvector
  have hTu : rightShift ℂ u = l • u := hu.apply_eq_smul
  have h0 : l * u 0 = 0 := by
    have := congrArg (fun v : lp (fun _ : ℕ => ℂ) 2 => v 0) hTu
    simpa [lp.coeFn_smul] using this.symm
  have hsucc : ∀ n, u n = l * u (n + 1) := fun n => by
    have := congrArg (fun v : lp (fun _ : ℕ => ℂ) 2 => v (n + 1)) hTu
    simpa [lp.coeFn_smul] using this
  refine hu.2 (lp.ext (funext fun n => ?_))
  rw [lp.coeFn_zero, Pi.zero_apply]
  rcases eq_or_ne l 0 with rfl | hl0
  · rw [hsucc n, zero_mul]
  · have hu0 : u 0 = 0 := (mul_eq_zero.1 h0).resolve_left hl0
    induction n with
    | zero => exact hu0
    | succ n ih =>
      have := hsucc n
      rw [ih] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hl0

section Banach

variable [CompleteSpace E]

/-- **Proposition 11.30** of [brezis2011functional]. Let $E \neq \{0\}$ be a complex Banach space
and $T \in \mathcal{L}(E)$. Then the spectrum $\sigma(T)$ is a nonempty compact set, and
$$\sigma(T) \subseteq \{\lambda \in \mathbb{C} ; |\lambda| \le \|T\|\}.$$

The nonemptiness is Liouville's theorem, Mathlib's `spectrum.nonempty`, which the source does
not prove. The hypothesis $E \neq \{0\}$ is `[Nontrivial E]`. -/
theorem proposition_11_30 [Nontrivial E] (T : E →L[ℂ] E) :
    (spectrum ℂ T).Nonempty ∧ IsCompact (spectrum ℂ T) ∧ spectrum ℂ T ⊆ closedBall 0 ‖T‖ :=
  ⟨spectrum.nonempty T, spectrum.isCompact T, spectrum.subset_closedBall_norm T⟩

end Banach

/-- **Section 11.4** of [brezis2011functional]. "The estimate $|\lambda| \le \|T\|$ is usually not
sharp": on $\mathbb{C}^2$ with the Euclidean norm, the operator $T(u_1, u_2) = (u_2, 0)$
satisfies $\sigma(T) = \{0\}$ and $\|T\| = 1$.

Since $T^2 = 0$, the spectral mapping theorem gives $\sigma(T) \subseteq \{0\}$, and
$\sigma(T) \neq \emptyset$. The norm is $1$ because $|Tu| = |u_2| \le |u|$, with equality at
$u = (0, 1)$. The coordinates $u_1, u_2$ are `u 0` and `u 1`. -/
theorem example_shift_two :
    ∃ T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      (∀ u, T u 0 = u 1 ∧ T u 1 = 0) ∧ spectrum ℂ T = {0} ∧ ‖T‖ = 1 := by
  set e₀ : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1 with he₀
  set T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).smulRight e₀ with hT
  have hTapply : ∀ u, T u = u 1 • e₀ := fun u => rfl
  have hTu : ∀ u : EuclideanSpace ℂ (Fin 2), T u 0 = u 1 ∧ T u 1 = 0 := fun u => by
    rw [hTapply, he₀]
    simp
  refine ⟨T, hTu, ?_, ?_⟩
  · -- `T ^ 2 = 0`
    have hsq : T ^ 2 = 0 := by
      ext u i
      rw [sq, mul_apply_eq_comp, hTapply (T u), (hTu u).2, zero_smul]
      simp
    have hsub : spectrum ℂ T ⊆ {0} := by
      intro l hl
      have hmem : l ^ 2 ∈ spectrum ℂ (T ^ 2) := by
        rw [spectrum.map_pow]
        exact ⟨l, hl, rfl⟩
      rw [hsq, spectrum.zero_eq] at hmem
      exact pow_eq_zero_iff two_ne_zero |>.1 hmem
    exact (Set.Nonempty.subset_singleton_iff (spectrum.nonempty T)).1 hsub
  · refine le_antisymm (ContinuousLinearMap.opNorm_le_bound T zero_le_one fun u => ?_) ?_
    · rw [one_mul, hTapply, norm_smul, he₀, PiLp.norm_single, norm_one, mul_one]
      exact PiLp.norm_apply_le u 1
    · have h1 : ‖T (EuclideanSpace.single 1 1)‖ = 1 := by
        rw [hTapply, he₀]
        simp
      have := T.le_opNorm (EuclideanSpace.single (1 : Fin 2) (1 : ℂ))
      rwa [h1, PiLp.norm_single, norm_one, mul_one] at this

section Banach

variable [CompleteSpace E]

/-- **Section 11.4** of [brezis2011functional], the spectral radius. Let $E$ be a complex Banach
space and $T \in \mathcal{L}(E)$. "$r(T) = \lim_{n \to \infty} \|T^n\|^{1/n}$ exists (Exercise
6.23), and clearly $r(T) \le \|T\|$." Here $r(T)$ is the spectral radius
$\sup\{|\lambda| ; \lambda \in \sigma(T)\}$.

Mathlib defines `spectralRadius ℂ T` as this supremum in `ℝ≥0∞`, and proves the limit formula of
Gelfand. So this theorem and Proposition 11.31 together show that the definition of the source
agrees with the one of Mathlib. If $\sigma(T) = \emptyset$, which happens only for $E = \{0\}$,
the supremum is $0$. -/
theorem spectralRadius_eq_lim (T : E →L[ℂ] E) :
    Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / n : ℝ)) atTop (𝓝 (spectralRadius ℂ T).toReal) ∧
      (spectralRadius ℂ T).toReal ≤ ‖T‖ :=
  ⟨spectrum.pow_norm_pow_one_div_tendsto_nhds_toReal_spectralRadius T, by
    have h := ENNReal.toReal_mono ENNReal.coe_ne_top (spectralRadius_le_nnnorm (𝕜 := ℂ) T)
    rwa [ENNReal.coe_toReal, coe_nnnorm] at h⟩

/-- **Proposition 11.31** of [brezis2011functional]. Let $E \neq \{0\}$ be a complex Banach space
and $T \in \mathcal{L}(E)$. Then $$r(T) = \max\{|\lambda| ; \lambda \in \sigma(T)\},$$ that is,
the maximum is attained and equals the spectral radius. -/
theorem proposition_11_31 [Nontrivial E] (T : E →L[ℂ] E) :
    IsGreatest ((fun l : ℂ => ‖l‖) '' spectrum ℂ T) (spectralRadius ℂ T).toReal := by
  obtain ⟨z, hz, hzr⟩ := spectrum.exists_nnnorm_eq_spectralRadius T
  refine ⟨⟨z, hz, ?_⟩, ?_⟩
  · rw [← hzr, ENNReal.coe_toReal, coe_nnnorm]
  · rintro _ ⟨l, hl, rfl⟩
    have h : (‖l‖₊ : ENNReal) ≤ spectralRadius ℂ T := by
      rw [spectralRadius_eq_of_unital]
      exact le_iSup₂ (f := fun l (_ : l ∈ spectrum ℂ T) => (‖l‖₊ : ENNReal)) l hl
    have := ENNReal.toReal_mono (spectrum.spectralRadius_ne_top T) h
    rwa [ENNReal.coe_toReal, coe_nnnorm] at this

open Polynomial in
/-- **Proposition 11.32** of [brezis2011functional], display (21). Let $E \neq \{0\}$ be a complex
Banach space, $T \in \mathcal{L}(E)$, and let $Q$ be a polynomial with complex coefficients.
Then $$\sigma(Q(T)) = Q(\sigma(T)).$$

The proof is Mathlib's `spectrum.map_polynomial_aeval`, which uses the factorization of
$Q - \mu$ as the source does. -/
theorem proposition_11_32_spectrum [Nontrivial E] (T : E →L[ℂ] E) (Q : ℂ[X]) :
    spectrum ℂ (aeval T Q) = (fun l => Q.eval l) '' spectrum ℂ T :=
  spectrum.map_polynomial_aeval T Q

omit [CompleteSpace E] in
open Polynomial in
/-- **Proposition 11.32** of [brezis2011functional], display (20). Let $E$ be a complex normed
space, $T \in \mathcal{L}(E)$, and let $Q$ be a polynomial with complex coefficients of positive
degree. Then $$EV(Q(T)) = Q(EV(T)),$$ where the eigenvalues are those of $T$ and $Q(T)$ as
linear maps.

**Correction.** The source does not assume $\deg Q > 0$. The identity fails for a constant
polynomial $Q = c$: for the right shift $T$, which has $EV(T) = \emptyset$ by
`Brezis.Chapter11.example_rightShift`, $EV(Q(T)) = EV(cI) = \{c\}$, but $Q(EV(T)) = \emptyset$. -/
theorem proposition_11_32_eigenvalue (T : E →L[ℂ] E) {Q : ℂ[X]} (hQ : 0 < Q.degree) :
    {μ | Module.End.HasEigenvalue (aeval (T : Module.End ℂ E) Q) μ} =
      (fun l => Q.eval l) '' {l | Module.End.HasEigenvalue (T : Module.End ℂ E) l} := by
  ext μ
  rw [Set.mem_ofPred_eq, Module.End.hasEigenvalue_aeval_iff _ hQ]
  exact ⟨fun ⟨ν, hν, h⟩ => ⟨ν, hν, h⟩, fun ⟨ν, hν, h⟩ => ⟨ν, hν, h⟩⟩

open Polynomial in
/-- **Proposition 11.32** of [brezis2011functional]. Let $E \neq \{0\}$ be a complex Banach space,
$T \in \mathcal{L}(E)$, and let $Q$ be a polynomial with complex coefficients of positive
degree. Then $$Q(EV(T)) = EV(Q(T)) \quad \text{and} \quad Q(\sigma(T)) = \sigma(Q(T)).$$

**Correction.** The source does not assume $\deg Q > 0$, which the first identity needs; see
`Brezis.Chapter11.proposition_11_32_eigenvalue`. -/
theorem proposition_11_32 [Nontrivial E] (T : E →L[ℂ] E) {Q : ℂ[X]} (hQ : 0 < Q.degree) :
    (fun l => Q.eval l) '' {l | Module.End.HasEigenvalue (T : Module.End ℂ E) l} =
        {μ | Module.End.HasEigenvalue (aeval (T : Module.End ℂ E) Q) μ} ∧
      (fun l => Q.eval l) '' spectrum ℂ T = spectrum ℂ (aeval T Q) :=
  ⟨(proposition_11_32_eigenvalue T hQ).symm, (proposition_11_32_spectrum T Q).symm⟩

end Banach


/-! ### Hilbert spaces over $\mathbb{C}$: numerical range, adjoints, normal operators, isometries -/

section HilbertSpectrum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Section 11.4** of [brezis2011functional], definition of the numerical range. Let $H$ be a
complex inner product space. The **numerical range** of $T \in \mathcal{L}(H)$ is $$W(T) =
\{(Tu, u) ; u \in H, \ |u| = 1\}.$$ It is equal to the backbone's `LinearMap.numericalRange`,
the set of the Rayleigh quotients $(Tx, x)/(x, x)$ for $x \neq 0$.

The scalar product $(Tu, u)$ is `⟪u, T u⟫_ℂ`. -/
theorem numericalRange_eq (T : H →L[ℂ] H) :
    (T : H →ₗ[ℂ] H).numericalRange = {z | ∃ u : H, ‖u‖ = 1 ∧ ⟪u, T u⟫_ℂ = z} := by
  ext z
  rw [LinearMap.mem_numericalRange, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    refine ⟨((‖x‖⁻¹ : ℝ) : ℂ) • x, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ hx']
    · rw [ContinuousLinearMap.coe_coe, map_smul, inner_smul_left, inner_smul_right,
        Complex.conj_ofReal, inner_self_eq_norm_sq_to_K, div_eq_inv_mul, ← mul_assoc]
      congr 1
      push_cast
      rw [sq, mul_inv]
      rfl
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, norm_ne_zero_iff.1 (hu ▸ one_ne_zero), ?_⟩
    rw [ContinuousLinearMap.coe_coe, inner_self_eq_norm_sq_to_K, hu]
    simp

variable [CompleteSpace H]

/-- **Proposition 11.33** of [brezis2011functional]. Let $H$ be a complex Hilbert space and
$T \in \mathcal{L}(H)$. Then:

(i) $\sigma(T) \subseteq \overline{W(T)}$;

(ii) more precisely, if $\lambda \notin \overline{W(T)}$, then $\lambda \in \rho(T)$ and
$$\|(T - \lambda I)^{-1}\| \le \frac{1}{\operatorname{dist}(\lambda, W(T))};$$

(iii) $W(T)$ is convex.

The inverse in (ii) is Mathlib's `resolvent T λ`, which is
$(\lambda I - T)^{-1} = -(T - \lambda I)^{-1}$ and has the same norm. If $H = \{0\}$, then
$W(T)$ is empty, its distance from $\lambda$ is $0$, and the bound reads
$\|(T - \lambda I)^{-1}\| \le 0$ because $1/0 = 0$ in Lean. Part (iii) is the Toeplitz–Hausdorff
theorem, which the source quotes from Halmos and the backbone proves. -/
theorem proposition_11_33 (T : H →L[ℂ] H) :
    spectrum ℂ T ⊆ closure (T : H →ₗ[ℂ] H).numericalRange ∧
      (∀ l ∉ closure (T : H →ₗ[ℂ] H).numericalRange, l ∈ resolventSet ℂ T ∧
        ‖resolvent T l‖ ≤ 1 / infDist l (T : H →ₗ[ℂ] H).numericalRange) ∧
      Convex ℝ (T : H →ₗ[ℂ] H).numericalRange :=
  ⟨T.spectrum_subset_closure_numericalRange, fun l hl =>
    ⟨T.mem_resolventSet_of_notMem_closure_numericalRange hl, by
      rw [one_div]
      exact T.norm_resolvent_le_inv_infDist_numericalRange hl⟩,
    LinearMap.convex_numericalRange _⟩

/-- **Section 11.4** of [brezis2011functional], the "word of caution" on adjoints. Let $H$ be a
complex Hilbert space, $T \in \mathcal{L}(H)$ and $\lambda \in \mathbb{C}$. With $H^*$
identified with $H$ by Proposition 11.27, the adjoint $T^* \in \mathcal{L}(H)$ satisfies
$(Tu, v) = (u, T^* v)$ for all $u, v \in H$, and $$(\lambda T)^* = \bar{\lambda} T^*. \tag{24}$$
In contrast, the adjoint $T^* \in \mathcal{L}(H^*)$ of Chapter 2 satisfies
$(\lambda T)^* = \lambda T^*$.

The Hilbert adjoint is Mathlib's `ContinuousLinearMap.adjoint`, and the adjoint of Chapter 2 is
`ContinuousLinearMap.strongDualMap`. In Mathlib's convention the first clause reads `⟪T u,
v⟫_ℂ = ⟪u, ContinuousLinearMap.adjoint T v⟫_ℂ`. -/
theorem adjoint_smul_conj (T : H →L[ℂ] H) (l : ℂ) :
    (∀ u v, ⟪T u, v⟫_ℂ = ⟪u, ContinuousLinearMap.adjoint T v⟫_ℂ) ∧
      ContinuousLinearMap.adjoint (l • T) = conj l • ContinuousLinearMap.adjoint T ∧
      (l • T).strongDualMap = l • T.strongDualMap :=
  ⟨fun u v => (ContinuousLinearMap.adjoint_inner_right T u v).symm,
    LinearIsometryEquiv.map_smulₛₗ _ l T, ContinuousLinearMap.ext fun v => by
      ext u
      simp⟩

/-- **Section 11.4** of [brezis2011functional], self-adjoint operators. Let $H$ be a complex Hilbert
space and let $T \in \mathcal{L}(H)$ be self-adjoint, $T^* = T$. Then
$(Tu, u) = (u, Tu) = \overline{(Tu, u)}$, so that $(Tu, u) \in \mathbb{R}$ for all $u \in H$; in
particular $W(T) \subseteq \mathbb{R}$, and thus $\sigma(T) \subseteq \mathbb{R}$. -/
theorem selfAdjoint_spectrum_subset_real {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    (∀ u, (⟪u, T u⟫_ℂ).im = 0) ∧ (∀ z ∈ (T : H →ₗ[ℂ] H).numericalRange, z.im = 0) ∧
      ∀ l ∈ spectrum ℂ T, l.im = 0 := by
  have hre : ∀ u, (⟪u, T u⟫_ℂ).im = 0 := fun u => by
    have h := hT.isSymmetric.conj_inner_sym u u
    rw [Complex.conj_eq_iff_im] at h
    rw [← inner_conj_symm, Complex.conj_im, neg_eq_zero]
    exact h
  have hW : ∀ z ∈ (T : H →ₗ[ℂ] H).numericalRange, z.im = 0 := by
    rw [numericalRange_eq]
    rintro _ ⟨u, -, rfl⟩
    exact hre u
  refine ⟨hre, hW, fun l hl => ?_⟩
  have hcl : closure (T : H →ₗ[ℂ] H).numericalRange ⊆ {z : ℂ | z.im = 0} :=
    closure_minimal (fun z hz => hW z hz) (isClosed_eq Complex.continuous_im continuous_const)
  exact hcl ((proposition_11_33 T).1 hl)

/-- **Proposition 11.34** of [brezis2011functional]. Let $H$ be a complex Hilbert space and let
$T \in \mathcal{L}(H)$ be a compact self-adjoint operator. Then there exists a Hilbert basis of
$H$ that consists of eigenvectors of $T$, and the corresponding eigenvalues are real.

**Generalization.** The source assumes that $H$ is separable and gives a basis indexed by
$\mathbb{N}$. The statement here needs no separability: the Hilbert basis is indexed by a subset
$w \subseteq H$ and consists of the elements of $w$.

The proof is Theorem 6.11 of Chapter 6, stated over `RCLike`, at $\mathbb{C}$. -/
theorem proposition_11_34 {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (hK : IsCompactOperator T) :
    ∃ (w : Set H) (b : HilbertBasis w ℂ H) (μ : w → ℝ),
      ⇑b = ((↑) : w → H) ∧ ∀ i, T (b i) = (μ i : ℂ) • b i :=
  ContinuousLinearMap.IsSymmetric.exists_hilbertBasis_eigenvectors hT.isSymmetric hK

/-- **Section 11.4** of [brezis2011functional], definition of normal operators. Let $H$ be a complex
Hilbert space. An operator $T \in \mathcal{L}(H)$ is **normal** if $T^* \circ T = T \circ T^*$.
The characterization of Problem 43 "still remains valid over $\mathbb{C}$": $T$ is normal if and
only if $|Tu| = |T^* u|$ for all $u \in H$.

Normality is Mathlib's `IsStarNormal T`. -/
theorem isStarNormal_iff (T : H →L[ℂ] H) :
    (IsStarNormal T ↔ ContinuousLinearMap.adjoint T ∘L T = T ∘L ContinuousLinearMap.adjoint T) ∧
      (IsStarNormal T ↔ ∀ u, ‖T u‖ = ‖ContinuousLinearMap.adjoint T u‖) :=
  ⟨by
    rw [_root_.isStarNormal_iff, Commute, SemiconjBy, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def],
    ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint⟩

/-- **Proposition 11.35** of [brezis2011functional]. Let $H \neq \{0\}$ be a complex Hilbert space
and let $T \in \mathcal{L}(H)$ be a normal operator. Then $$\max\{|\lambda| ; \lambda \in
\sigma(T)\} = \|T\|. \tag{25}$$

The proof combines Mathlib's `IsStarNormal.spectralRadius_eq_nnnorm` in the C⋆-algebra
$\mathcal{L}(H)$ with Proposition 11.31. -/
theorem proposition_11_35 [Nontrivial H] {T : H →L[ℂ] H} (hT : IsStarNormal T) :
    IsGreatest ((fun l : ℂ => ‖l‖) '' spectrum ℂ T) ‖T‖ := by
  have := hT
  have h := proposition_11_31 T
  rwa [IsStarNormal.spectralRadius_eq_nnnorm T, ENNReal.coe_toReal, coe_nnnorm] at h

/-- **Proposition 11.36** of [brezis2011functional]. Let $H$ be a complex Hilbert space and let
$T \in \mathcal{L}(H)$ be a compact normal operator. Then there exists a Hilbert basis of $H$
that consists of eigenvectors of $T$.

**Generalization.** The source assumes that $H$ is separable. The statement here needs no
separability: the Hilbert basis is indexed by a subset $w \subseteq H$ and consists of the
elements of $w$.

The eigenvalues need not be real. The backbone proof follows the source, "exactly as in the
proof of Theorem 6.11", with Proposition 11.35 in place of Corollary 6.10. -/
theorem proposition_11_36 {T : H →L[ℂ] H} (hT : IsStarNormal T) (hK : IsCompactOperator T) :
    ∃ (w : Set H) (b : HilbertBasis w ℂ H),
      ⇑b = ((↑) : w → H) ∧ ∀ i : w, ∃ μ : ℂ, T i = μ • (i : H) :=
  ContinuousLinearMap.IsStarNormal.exists_hilbertBasis_eigenvector hT hK

/-- **Remark 2** of [brezis2011functional], Section 11.4. Let $H$ be a complex Hilbert space and let
$T \in \mathcal{L}(H)$ be a compact normal operator. Then $$\overline{W(T)} =
\operatorname{conv} \sigma(T).$$

The convex hull of a compact subset of $\mathbb{C}$ is closed, so the plain convex hull appears.
In an eigenbasis, $(Tu, u) = \sum_i \lambda_i |u_i|^2$ with $\sum_i |u_i|^2 = 1$. The second
sentence of the remark, for every normal $T$, is not formalized. -/
theorem remark_11_2 {T : H →L[ℂ] H} (hT : IsStarNormal T) (hK : IsCompactOperator T) :
    closure (T : H →ₗ[ℂ] H).numericalRange = convexHull ℝ (spectrum ℂ T) :=
  ContinuousLinearMap.IsStarNormal.closure_numericalRange_eq_convexHull_spectrum hT hK

/-- **Section 11.4** of [brezis2011functional], definition of isometries and unitary operators. Let
$H$ be a complex Hilbert space. An operator $T \in \mathcal{L}(H)$ is an **isometry** if
$|Tu| = |u|$ for all $u \in H$, and a **unitary operator** if it is a surjective isometry.
Equivalently, $T$ is unitary if and only if $T^* T = T T^* = I$.

An isometry is Mathlib's `Isometry T`, and the condition $T^* T = T T^* = I$ is membership in
Mathlib's `unitary (H →L[ℂ] H)`. -/
theorem unitary_iff_isometry_surjective (T : H →L[ℂ] H) :
    (Isometry T ↔ ∀ u, ‖T u‖ = ‖u‖) ∧
      (T ∈ unitary (H →L[ℂ] H) ↔ Isometry T ∧ Function.Surjective T) := by
  refine ⟨AddMonoidHomClass.isometry_iff_norm T, fun hT => ⟨?_, fun v => ?_⟩,
    fun ⟨hi, hs⟩ => ContinuousLinearMap.mem_unitary_of_isometry_of_surjective hi hs⟩
  · rw [ContinuousLinearMap.isometry_iff_adjoint_comp_self, ← ContinuousLinearMap.mul_def,
      ← ContinuousLinearMap.star_eq_adjoint]
    exact Unitary.star_mul_self_of_mem hT
  · refine ⟨star T v, ?_⟩
    have h := Unitary.mul_star_self_of_mem hT
    rw [← mul_apply_eq_comp, h, one_apply_eq_self]

omit [CompleteSpace H] in
/-- **Proposition 11.37** of [brezis2011functional], eigenvalues. Let $H$ be a complex inner product
space and let $T \in \mathcal{L}(H)$ be an isometry. Then $$EV(T) \subseteq S^1 = \{\lambda \in
\mathbb{C} ; |\lambda| = 1\}.$$
-/
theorem proposition_11_37_eigenvalue {T : H →L[ℂ] H} (hT : Isometry T) :
    {l | Module.End.HasEigenvalue (T : Module.End ℂ H) l} ⊆ sphere (0 : ℂ) 1 := fun l hl => by
  rw [mem_sphere_zero_iff_norm]
  exact ContinuousLinearMap.norm_eq_one_of_hasEigenvalue_of_isometry hT hl

/-- **Proposition 11.37** of [brezis2011functional], unitary operators. Let $H$ be a complex Hilbert
space and let $T \in \mathcal{L}(H)$ be a unitary operator, that is, a surjective isometry. Then
$\sigma(T) \subseteq S^1$. -/
theorem proposition_11_37_unitary {T : H →L[ℂ] H} (hT : Isometry T)
    (hs : Function.Surjective T) : spectrum ℂ T ⊆ sphere (0 : ℂ) 1 :=
  spectrum.subset_circle_of_unitary ((unitary_iff_isometry_surjective T).2.2 ⟨hT, hs⟩)

/-- **Proposition 11.37** of [brezis2011functional], isometries that are not unitary. Let $H$ be a
complex Hilbert space and let $T \in \mathcal{L}(H)$ be an isometry that is not unitary. Then
$$\sigma(T) = \{\lambda \in \mathbb{C} ; |\lambda| \le 1\}.$$

The proof adapts question 6 of Problem 44. Here "not unitary" is non-membership in
`unitary (H →L[ℂ] H)`, which for an isometry means that $T$ is not surjective. -/
theorem proposition_11_37_not_unitary {T : H →L[ℂ] H} (hT : Isometry T)
    (hs : T ∉ unitary (H →L[ℂ] H)) : spectrum ℂ T = closedBall (0 : ℂ) 1 :=
  ContinuousLinearMap.spectrum_eq_closedBall_of_isometry_of_not_surjective hT fun h =>
    hs ((unitary_iff_isometry_surjective T).2.2 ⟨hT, h⟩)

/-- **Proposition 11.37** of [brezis2011functional]. Let $H$ be a complex Hilbert space and let
$T \in \mathcal{L}(H)$ be an isometry. Then $EV(T) \subseteq S^1$. If $T$ is unitary, then
$\sigma(T) \subseteq S^1$. If $T$ is not unitary, then $\sigma(T) = \{\lambda \in \mathbb{C} ;
|\lambda| \le 1\}$.
-/
theorem proposition_11_37 {T : H →L[ℂ] H} (hT : Isometry T) :
    {l | Module.End.HasEigenvalue (T : Module.End ℂ H) l} ⊆ sphere (0 : ℂ) 1 ∧
      (T ∈ unitary (H →L[ℂ] H) → spectrum ℂ T ⊆ sphere (0 : ℂ) 1) ∧
      (T ∉ unitary (H →L[ℂ] H) → spectrum ℂ T = closedBall (0 : ℂ) 1) :=
  ⟨proposition_11_37_eigenvalue hT, fun hu => spectrum.subset_circle_of_unitary hu,
    proposition_11_37_not_unitary hT⟩

/-- **Section 11.4** of [brezis2011functional], skew-adjoint operators. Let $H$ be a complex Hilbert
space. An operator $T \in \mathcal{L}(H)$ is skew-adjoint (or antisymmetric) if $T^* = -T$.
"Clearly $T$ is skew-adjoint if and only if $iT$ is self-adjoint (this follows from (24))." -/
theorem skewAdjoint_iff (T : H →L[ℂ] H) :
    ContinuousLinearMap.adjoint T = -T ↔ IsSelfAdjoint (Complex.I • T) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', (adjoint_smul_conj T Complex.I).2.1, Complex.conj_I,
    neg_smul]
  constructor
  · intro h
    rw [h, smul_neg, neg_neg]
  · intro h
    have := congrArg (fun S : H →L[ℂ] H => Complex.I • S) h
    simp only [smul_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul, neg_neg] at this
    rw [this]

/-- **Section 11.4** of [brezis2011functional]. "Thus, for any skew-adjoint operator we have $EV(T)
\subseteq \sigma(T) \subseteq \overline{W(T)} \subseteq i\mathbb{R}$." Let $H$ be a complex
Hilbert space and let $T \in \mathcal{L}(H)$ satisfy $T^* = -T$. Then
$\operatorname{Re}(Tu, u) = 0$ for all $u \in H$, and the closure of $W(T)$, the spectrum
$\sigma(T)$ and the set $EV(T)$ of eigenvalues all lie on the imaginary axis. -/
theorem skewAdjoint_spectrum_subset_imaginary {T : H →L[ℂ] H}
    (hT : ContinuousLinearMap.adjoint T = -T) :
    (∀ u, (⟪u, T u⟫_ℂ).re = 0) ∧
      (∀ z ∈ closure (T : H →ₗ[ℂ] H).numericalRange, z.re = 0) ∧
      (∀ l ∈ spectrum ℂ T, l.re = 0) ∧
      ∀ l, Module.End.HasEigenvalue (T : Module.End ℂ H) l → l.re = 0 := by
  have hre : ∀ u, (⟪u, T u⟫_ℂ).re = 0 := fun u => by
    have h : ⟪T u, u⟫_ℂ = -⟪u, T u⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hT, neg_apply, inner_neg_right]
    have h' : RCLike.re ⟪T u, u⟫_ℂ = RCLike.re (-⟪u, T u⟫_ℂ) := congrArg RCLike.re h
    rw [inner_re_symm, map_neg] at h'
    change RCLike.re ⟪u, T u⟫_ℂ = 0
    linarith
  have hW : ∀ z ∈ (T : H →ₗ[ℂ] H).numericalRange, z.re = 0 := by
    rw [numericalRange_eq]
    rintro _ ⟨u, -, rfl⟩
    exact hre u
  have hcl : ∀ z ∈ closure (T : H →ₗ[ℂ] H).numericalRange, z.re = 0 :=
    closure_minimal (fun z hz => hW z hz) (isClosed_eq Complex.continuous_re continuous_const)
  refine ⟨hre, hcl, fun l hl => hcl l ((proposition_11_33 T).1 hl), fun l hl =>
    hcl l ((proposition_11_33 T).1 ((spectrum_eq_setOf_not_bijective T).2.2.2 hl))⟩

end HilbertSpectrum

/-- **Section 11.4** of [brezis2011functional], the identity of the paragraph on Chapter 7. Let $H$
be a complex inner product space, and let $\varphi : \mathbb{R} \to H$ be differentiable at $t$
with derivative $\varphi'$. Then $|\varphi|^2$ is differentiable at $t$, and $$\frac{d}{dt}
|\varphi|^2 = 2 \operatorname{Re}(\varphi', \varphi),$$ because $(\varphi', \varphi) + (\varphi,
\varphi') = (\varphi', \varphi) + \overline{(\varphi', \varphi)}$.

In Mathlib's convention the derivative is `2 * (⟪φ', φ t⟫_ℂ).re`. The computations of Sections
7.2–7.4 use this identity over $\mathbb{C}$. The monotonicity condition
$\operatorname{Re}(Av, v) \ge 0$ is `LinearPMap.IsMonotone` of Chapter 7, which is already
stated with the real part. -/
theorem hasDerivAt_norm_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {φ : ℝ → H} {φ' : H} {t : ℝ} (h : HasDerivAt φ φ' t) :
    HasDerivAt (fun s => ‖φ s‖ ^ 2) (2 * (⟪φ', φ t⟫_ℂ).re) t := by
  let _ := InnerProductSpace.complexToReal (G := H)
  have := h.norm_sq
  rwa [real_inner_eq_re_inner (𝕜 := ℂ), inner_re_symm] at this


end Brezis.Chapter11

end
