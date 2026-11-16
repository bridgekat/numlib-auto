/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.FieldTheory.Minpoly.Field
import Numlib.Algebra.Polynomial.Taylor
import Numlib.Analysis.Calculus.HermiteInterpolation

/-!
# The primary functional calculus

Let $\mathbb{K}$ be a nontrivially normed field, let $A$ be a $\mathbb{K}$-algebra, and let
$a \in A$ be integral over $\mathbb{K}$ with a minimal polynomial that splits. Let $\lambda$ run
over the roots of the minimal polynomial, and let $m_\lambda$ be the multiplicity of $\lambda$ as a
root (the index of the eigenvalue $\lambda$). For $f : \mathbb{K} \to \mathbb{K}$, the **primary
functional calculus** is $f(a) = p(a)$, where $p$ is the Hermite interpolant of the Taylor
coefficients $f^{(j)}(\lambda)/j!$, $j < m_\lambda$, at the roots. This is Higham's definition of a
matrix function by interpolation (Higham, *Functions of Matrices*, Definition 1.4;
[golub2013matrix], §9.1), for any integral element of any algebra.

The definition is total and algebraic: $f(a)$ is a polynomial in $a$ by construction, and it depends
only on the derivatives $f^{(j)}(\lambda)$, $j < m_\lambda$ (`pfc_congr`). This is the formal
content of "$f$ is defined on the spectrum of $a$". The module proves the algebraic rules of the
calculus, the spectral decomposition $f(a) = \sum_\lambda \sum_{j < m_\lambda}
\frac{f^{(j)}(\lambda)}{j!} (a - \lambda)^j E_\lambda$ with the spectral idempotents $E_\lambda$,
and the spectral mapping theorem $\sigma(f(a)) = f(\sigma(a))$. The Jordan-form, power-series and
Cauchy-integral descriptions of $f(A)$ are theorems in `Numlib.Analysis.Matrix.Function.Basic`,
`Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Analytic` and
`Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Cauchy`.

## Main definitions

* `pfc`: the primary functional calculus $f(a)$.
* `spectralIdempotent`: the spectral idempotent $E_\mu$ of $a$ at $\mu$ (Frobenius covariant, Riesz
  projection), as a polynomial in $a$.
* `ContDiffOnSpectrum`: $f$ is $C^{m_\lambda - 1}$ at every root $\lambda$ of the minimal polynomial
  of $a$, the smoothness hypothesis of the algebraic rules.

## Main results

* `pfc_eq_aeval_of_isJetInterpolant`: the characterization through which all other results go. Any
  polynomial that interpolates the Taylor coefficients of $f$ on a multiset whose nodal polynomial
  the minimal polynomial divides computes $f(a)$.
* `pfc_congr`, `pfc_congr_of_eventuallyEq`, `pfc_congr_of_eqOn`: $f(a)$ depends only on the
  derivatives of $f$ at the eigenvalues, hence only on $f$ near the spectrum.
* `spectrum.mem_iff_isRoot_minpoly`, `spectrum.mem_iff_mem_roots_minpoly`: the spectrum of an
  integral element is the set of roots of its minimal polynomial.
* `pfc_polynomial`, `pfc_const`, `pfc_id`, `pfc_pow`: for a polynomial $p$, the calculus gives
  $p(a)$.
* `pfc_add`, `pfc_const_smul`, `pfc_mul`, `pfc_inv`: $f \mapsto f(a)$ is an algebra homomorphism on
  functions that are smooth enough at the eigenvalues.
* `commute_pfc`, `AlgHom.map_pfc`, `AlgEquiv.map_pfc`, `pfc_units_conj`: commutation with $a$,
  naturality, and similarity.
* `spectralIdempotent_mul_spectralIdempotent`, `sum_spectralIdempotent`,
  `pow_mul_spectralIdempotent`: the spectral idempotents are orthogonal idempotents that sum to $1$,
  and $(a - \mu)^{m_\mu} E_\mu = 0$.
* `pfc_eq_sum_spectralIdempotent`: the spectral decomposition (Sylvester's formula).
* `spectrum_pfc`: the spectral mapping theorem $\sigma(f(a)) = f(\sigma(a))$.

## Implementation notes

* `pfc f a` has a junk value when $a$ is not integral or its minimal polynomial does not split. If
  $a$ is not integral, its minimal polynomial is $0$, it has no roots, and `pfc f a = 0`.
* The derivatives are Mathlib's `iteratedDeriv`, which take junk values where $f$ is not
  differentiable. For this reason the algebraic rules assume `ContDiffOnSpectrum`.
* The definition uses a classical `DecidableEq 𝕜`, because multiplicities are counted with
  `Multiset.count`. Statements that mention jet interpolation take an arbitrary instance, and
  `pfc_def` converts between the two.
* The hypotheses `IsIntegral 𝕜 a` and `(minpoly 𝕜 a).Splits` hold automatically over an
  algebraically closed field in a finite-dimensional algebra, for example for complex matrices.
-/

open Polynomial Hermite

section Spectrum

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- Two polynomials in the same element commute: $p(a)\, q(a) = q(a)\, p(a)$ for $a$ in a
$K$-algebra and $p, q \in K[X]$. -/
theorem commute_aeval_aeval (a : A) (p q : K[X]) : Commute (aeval a p) (aeval a q) := by
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

/-- **The spectrum of an integral element is the set of roots of its minimal polynomial.** Let $K$
be a field, let $A$ be a $K$-algebra, and let $a \in A$ be integral over $K$. Then $\mu \in K$
lies in the spectrum $\sigma(a)$ if and only if $\mu$ is a root of the minimal polynomial of
$a$. -/
theorem spectrum.mem_iff_isRoot_minpoly {a : A} (ha : IsIntegral K a) {μ : K} :
    μ ∈ spectrum K a ↔ (minpoly K a).IsRoot μ := by
  rw [spectrum.mem_iff]
  constructor
  · intro hμ
    by_contra hroot
    apply hμ
    -- `minpoly = (X - μ) q + minpoly(μ)`, evaluated at `a`
    set q := minpoly K a /ₘ (X - C μ)
    have hdiv := modByMonic_add_div (minpoly K a) (X - C μ)
    rw [modByMonic_X_sub_C_eq_C_eval] at hdiv
    have h0 := congrArg (aeval a) hdiv
    rw [map_add, map_mul, minpoly.aeval, aeval_C, map_sub, aeval_X, aeval_C] at h0
    have hc : (minpoly K a).eval μ ≠ 0 := hroot
    have hcomm : Commute (algebraMap K A μ - a) (((minpoly K a).eval μ)⁻¹ • aeval a q) := by
      have := commute_aeval_aeval a (C μ - X) (C ((minpoly K a).eval μ)⁻¹ * q)
      simpa [Algebra.smul_def] using this
    have key : (algebraMap K A μ - a) * ((minpoly K a).eval μ)⁻¹ • aeval a q = 1 := by
      rw [mul_smul_comm, ← neg_sub, neg_mul, eq_neg_iff_add_eq_zero.mpr
        ((add_comm _ _).trans h0), neg_neg, Algebra.smul_def, ← map_mul,
        inv_mul_cancel₀ hc, map_one]
    exact ⟨⟨_, _, key, hcomm.eq.symm.trans key⟩, rfl⟩
  · intro hroot hunit
    have hne : minpoly K a ≠ 0 := minpoly.ne_zero ha
    obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hroot
    have hq0 : aeval a q = 0 := by
      have h := minpoly.aeval K a
      rw [hq, map_mul, map_sub, aeval_X, aeval_C, ← neg_sub, neg_mul, neg_eq_zero] at h
      exact (hunit.mul_right_eq_zero).mp h
    have hdvd := minpoly.dvd K a hq0
    have hq0' : q ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hq)
    have hdeg := natDegree_le_of_dvd hdvd hq0'
    rw [hq, natDegree_mul (X_sub_C_ne_zero μ) hq0', natDegree_X_sub_C] at hdeg
    omega

/-- Let $a$ be integral over the field $K$. Then $\mu \in \sigma(a)$ if and only if $\mu$ belongs to
the multiset of roots of the minimal polynomial of $a$. This is the form of
`spectrum.mem_iff_isRoot_minpoly` over which the lemmas on `pfc` quantify. -/
theorem spectrum.mem_iff_mem_roots_minpoly {a : A} (ha : IsIntegral K a) {μ : K} :
    μ ∈ spectrum K a ↔ μ ∈ (minpoly K a).roots := by
  rw [spectrum.mem_iff_isRoot_minpoly ha, mem_roots (minpoly.ne_zero ha)]

/-- A root of the minimal polynomial of $a$ lies in the spectrum of $a$. No integrality hypothesis
is needed: the minimal polynomial of an element that is not integral is $0$, and its multiset of
roots is empty. -/
theorem spectrum.mem_of_mem_roots_minpoly {a : A} {μ : K} (hμ : μ ∈ (minpoly K a).roots) :
    μ ∈ spectrum K a := by
  have ha : IsIntegral K a := by
    by_contra h
    rw [minpoly.eq_zero h, roots_zero] at hμ
    exact Multiset.notMem_zero μ hμ
  exact (spectrum.mem_iff_mem_roots_minpoly ha).2 hμ

end Spectrum

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [Ring A] [Algebra 𝕜 A]

open Classical in
/-- The **primary functional calculus**. Let $\mathbb{K}$ be a nontrivially normed field, let $A$ be
a $\mathbb{K}$-algebra, let $a \in A$ and let $f : \mathbb{K} \to \mathbb{K}$. Let $p$ be the
Hermite interpolant of $f$ at the roots of the minimal polynomial of $a$, each root $\lambda$
taken to its multiplicity $m_\lambda$. That is, $p$ is the unique polynomial of degree less than
the number of roots counted with multiplicity such that, at each root $\lambda$,
$$p \equiv \sum_{j < m_\lambda} \frac{f^{(j)}(\lambda)}{j!} (X - \lambda)^j \pmod{(X -
  \lambda)^{m_\lambda}}.$$
Then $f(a) = p(a)$. This is $f(A)$ of [golub2013matrix], §9.1, and Definition 1.4 of Higham,
*Functions of Matrices*.

The definition is meaningful when $a$ is integral over $\mathbb{K}$ and its minimal polynomial
splits; otherwise the value is a junk value, and it is $0$ when $a$ is not integral. The
derivatives are `iteratedDeriv`, and the interpolant is `Hermite.interpolateJet` of the roots
and of `Hermite.taylorJet f`. -/
noncomputable def pfc (f : 𝕜 → 𝕜) (a : A) : A :=
  aeval a (interpolateJet (minpoly 𝕜 a).roots (taylorJet f))

/-- `pfc f a` unfolded with an arbitrary decidable equality on $\mathbb{K}$: it is the value at $a$
of the Hermite interpolant of the Taylor coefficients `Hermite.taylorJet f` at the roots of the
minimal polynomial of $a$. -/
theorem pfc_def [h : DecidableEq 𝕜] (f : 𝕜 → 𝕜) (a : A) :
    pfc f a = aeval a (interpolateJet (minpoly 𝕜 a).roots (taylorJet f)) := by
  obtain rfl : h = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  rfl

section Characterization

variable [DecidableEq 𝕜] {a : A}

omit [DecidableEq 𝕜] in
/-- If $a$ is integral with a split minimal polynomial, the minimal polynomial is the nodal
polynomial $\prod_\lambda (X - \lambda)$ of its multiset of roots, each root counted with
multiplicity. -/
theorem minpoly_eq_nodalMultiset_roots (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) :
    minpoly 𝕜 a = nodalMultiset (minpoly 𝕜 a).roots :=
  eq_nodalMultiset_roots (minpoly.monic ha) hs

/-- Let $s$ be a multiset in $\mathbb{K}$ whose nodal polynomial $\prod_{x \in s} (X - x)$ is
divisible by the minimal polynomial of $a$. If two polynomials $p$ and $q$ interpolate the same
jets on $s$, then $p(a) = q(a)$. -/
theorem aeval_eq_aeval_of_isJetInterpolant {s : Multiset 𝕜} (hdvd : minpoly 𝕜 a ∣ nodalMultiset s)
    {y : 𝕜 → ℕ → 𝕜} {p q : 𝕜[X]} (hp : IsJetInterpolant s y p) (hq : IsJetInterpolant s y q) :
    aeval a p = aeval a q := by
  obtain ⟨r, hr⟩ := hdvd.trans (hp.nodalMultiset_dvd_sub hq)
  rw [← sub_eq_zero, ← map_sub, hr, map_mul, minpoly.aeval, zero_mul]

omit [DecidableEq 𝕜] in
/-- If the minimal polynomial of $a$ divides the nodal polynomial of a multiset $s$, then its
multiset of roots is contained in $s$, with multiplicities. -/
theorem roots_minpoly_le_of_dvd {s : Multiset 𝕜} (hdvd : minpoly 𝕜 a ∣ nodalMultiset s) :
    (minpoly 𝕜 a).roots ≤ s := by
  simpa using roots.le_of_dvd (monic_nodalMultiset s).ne_zero hdvd

/-- **The characterization of the primary functional calculus.** Let $a \in A$, and let $s$ be a
multiset in $\mathbb{K}$ whose nodal polynomial $\prod_{x \in s} (X - x)$ is divisible by the
minimal polynomial of $a$; for example, $s$ is the multiset of roots of the minimal polynomial,
or the eigenvalues of a matrix with their algebraic multiplicities. Let $p \in \mathbb{K}[X]$
interpolate the Taylor coefficients $f^{(j)}(x)/j!$ of $f$ at each node $x$ of $s$, for $j$
below the multiplicity of $x$ in $s$. Then $f(a) = p(a)$.

No differentiability of $f$ is needed. The divisibility hypothesis implies that $a$ is integral
and that its minimal polynomial splits. The interpolation condition is `Hermite.IsJetInterpolant
s (Hermite.taylorJet f) p`. -/
theorem pfc_eq_aeval_of_isJetInterpolant {s : Multiset 𝕜} (hdvd : minpoly 𝕜 a ∣ nodalMultiset s)
    {f : 𝕜 → 𝕜} {p : 𝕜[X]} (hp : IsJetInterpolant s (taylorJet f) p) : pfc f a = aeval a p := by
  have hne : minpoly 𝕜 a ≠ 0 := fun h =>
    (monic_nodalMultiset s).ne_zero (zero_dvd_iff.mp (h ▸ hdvd))
  have ha : IsIntegral 𝕜 a := by
    by_contra h
    exact hne (minpoly.eq_zero h)
  have hs : (minpoly 𝕜 a).Splits :=
    (splits_nodalMultiset s).of_dvd (monic_nodalMultiset s).ne_zero hdvd
  rw [pfc_def]
  exact aeval_eq_aeval_of_isJetInterpolant (minpoly_eq_nodalMultiset_roots ha hs).dvd
    (isJetInterpolant_interpolateJet _ _) (hp.of_le (roots_minpoly_le_of_dvd hdvd))

omit [DecidableEq 𝕜] in
/-- If $a$ is integral with a split minimal polynomial, the minimal polynomial divides the nodal
polynomial of its multiset of roots. -/
theorem minpoly_dvd_nodalMultiset_roots (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) :
    minpoly 𝕜 a ∣ nodalMultiset (minpoly 𝕜 a).roots :=
  (minpoly_eq_nodalMultiset_roots ha hs).dvd

end Characterization

section Algebraic

variable {a : A}

/-- **$f(a)$ depends only on the derivatives of $f$ at the eigenvalues.** Let $a \in A$ and
$f, g : \mathbb{K} \to \mathbb{K}$. If $f^{(j)}(\lambda) = g^{(j)}(\lambda)$ for every root
$\lambda$ of the minimal polynomial of $a$ and every $j < m_\lambda$, then $f(a) = g(a)$.

No hypothesis on $a$ is needed. The derivatives are `iteratedDeriv`. -/
theorem pfc_congr {f g : 𝕜 → 𝕜}
    (h : ∀ μ ∈ (minpoly 𝕜 a).roots, ∀ j < (minpoly 𝕜 a).rootMultiplicity μ,
      iteratedDeriv j f μ = iteratedDeriv j g μ) :
    pfc f a = pfc g a := by
  classical
  rw [pfc_def, pfc_def, interpolateJet_congr fun x hx j hj => ?_]
  rw [count_roots] at hj
  rw [taylorJet, taylorJet, h x hx j hj]

/-- If $f = g$ on a neighbourhood of every point of the spectrum of $a$, then $f(a) = g(a)$. -/
theorem pfc_congr_of_eventuallyEq {f g : 𝕜 → 𝕜} (h : ∀ μ ∈ spectrum 𝕜 a, f =ᶠ[nhds μ] g) :
    pfc f a = pfc g a :=
  pfc_congr fun μ hμ j _ =>
    (h μ (spectrum.mem_of_mem_roots_minpoly hμ)).iteratedDeriv_eq j

/-- If $f = g$ on an open set $U$ that contains the spectrum of $a$, then $f(a) = g(a)$. -/
theorem pfc_congr_of_eqOn {f g : 𝕜 → 𝕜} {U : Set 𝕜} (hU : IsOpen U) (hσ : spectrum 𝕜 a ⊆ U)
    (h : Set.EqOn f g U) : pfc f a = pfc g a :=
  pfc_congr_of_eventuallyEq fun _ hμ =>
    Filter.eventuallyEq_of_mem (hU.mem_nhds (hσ hμ)) h

/-- **Polynomials.** Let $\mathbb{K}$ have characteristic zero, and let $a \in A$ be integral over
$\mathbb{K}$ with a split minimal polynomial. For every polynomial $p \in \mathbb{K}[X]$, the
primary functional calculus of the function $z \mapsto p(z)$ at $a$ is $p(a)$. -/
theorem pfc_polynomial [CharZero 𝕜] (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits)
    (p : 𝕜[X]) : pfc (fun z => p.eval z) a = aeval a p := by
  classical
  exact pfc_eq_aeval_of_isJetInterpolant (minpoly_dvd_nodalMultiset_roots ha hs)
    (isJetInterpolant_taylorJet_polynomial _ p)

/-- If $\mathbb{K}$ has characteristic zero and $a$ is integral with a split minimal polynomial, the
constant function $c$ gives $c \cdot 1$. -/
theorem pfc_const [CharZero 𝕜] (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) (c : 𝕜) :
    pfc (fun _ => c) a = algebraMap 𝕜 A c := by
  simpa using pfc_polynomial ha hs (C c : 𝕜[X])

/-- If $\mathbb{K}$ has characteristic zero and $a$ is integral with a split minimal polynomial, the
identity function gives $a$. -/
theorem pfc_id [CharZero 𝕜] (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) :
    pfc (fun z : 𝕜 => z) a = a := by
  simpa using pfc_polynomial ha hs (X : 𝕜[X])

/-- If $\mathbb{K}$ has characteristic zero and $a$ is integral with a split minimal polynomial, the
function $z \mapsto z^n$ gives $a^n$. -/
theorem pfc_pow [CharZero 𝕜] (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) (n : ℕ) :
    pfc (fun z : 𝕜 => z ^ n) a = a ^ n := by
  simpa using pfc_polynomial ha hs ((X : 𝕜[X]) ^ n)

/-- A function $f : \mathbb{K} \to \mathbb{K}$ is **$C^{m_\lambda - 1}$ on the spectrum** of $a$ if,
at every root $\lambda$ of the minimal polynomial of $a$, $f$ is $C^{m_\lambda - 1}$ at
$\lambda$, where $m_\lambda$ is the multiplicity of $\lambda$ as a root (the index of the
eigenvalue $\lambda$).

Under this smoothness, $f \mapsto f(a)$ is an algebra homomorphism (`pfc_add`, `pfc_mul`,
`pfc_inv`), and compositions behave as expected (`pfc_comp`). It makes the derivatives
$f^{(j)}(\lambda)$, $j < m_\lambda$, on which $f(a)$ depends (`pfc_congr`), behave as true
derivatives. -/
def ContDiffOnSpectrum (f : 𝕜 → 𝕜) (a : A) : Prop :=
  ∀ μ ∈ (minpoly 𝕜 a).roots, ContDiffAt 𝕜 ((minpoly 𝕜 a).rootMultiplicity μ - 1 : ℕ) f μ

/-- $f$ is $C^{m_\lambda - 1}$ on the spectrum of $a$ if and only if $f$ is $C^{m_\lambda - 1}$ at
every root $\lambda$ of the minimal polynomial of $a$. -/
theorem contDiffOnSpectrum_iff {f : 𝕜 → 𝕜} :
    ContDiffOnSpectrum f a ↔
      ∀ μ ∈ (minpoly 𝕜 a).roots, ContDiffAt 𝕜 ((minpoly 𝕜 a).rootMultiplicity μ - 1 : ℕ) f μ :=
  Iff.rfl

open scoped ContDiff in
/-- A function that is $C^\infty$ at every root of the minimal polynomial of $a$ is
$C^{m_\lambda - 1}$ on the spectrum of $a$. -/
theorem ContDiffOnSpectrum.of_contDiffAt {f : 𝕜 → 𝕜}
    (h : ∀ μ ∈ (minpoly 𝕜 a).roots, ContDiffAt 𝕜 ∞ f μ) : ContDiffOnSpectrum f a :=
  fun μ hμ => (h μ hμ).of_le (WithTop.coe_le_coe.2 le_top)

/-- **Additivity.** Let $a \in A$, and let $f$ and $g$ be $C^{m_\lambda - 1}$ on the spectrum of $a$
(`ContDiffOnSpectrum`). Then $(f + g)(a) = f(a) + g(a)$.

The smoothness hypothesis is needed because Mathlib's derivatives have junk values: without it,
$(f + g)^{(j)}$ need not be $f^{(j)} + g^{(j)}$. -/
theorem pfc_add {f g : 𝕜 → 𝕜}
    (hf : ContDiffOnSpectrum f a)
    (hg : ContDiffOnSpectrum g a) :
    pfc (f + g) a = pfc f a + pfc g a := by
  classical
  rw [pfc_def, pfc_def, pfc_def, ← map_add, ← interpolateJet_add,
    interpolateJet_congr fun x hx j hj => ?_]
  rw [count_roots] at hj
  have hj' : (j : WithTop ℕ∞) ≤ ((minpoly 𝕜 a).rootMultiplicity x - 1 : ℕ) := by
    exact_mod_cast (by omega : j ≤ _)
  exact taylorJet_add ((hf x hx).of_le hj') ((hg x hx).of_le hj')

/-- For every scalar $c$, $(cf)(a) = c\, f(a)$. No hypothesis on $f$ or $a$ is needed. -/
theorem pfc_const_smul (c : 𝕜) (f : 𝕜 → 𝕜) : pfc (c • f) a = c • pfc f a := by
  classical
  have h : taylorJet (c • f) = c • taylorJet f := by
    ext x j
    rw [taylorJet_const_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [pfc_def, pfc_def, h, interpolateJet_smul, map_smul]

/-- If $f$ and $g$ are $C^{m_\lambda - 1}$ on the spectrum of $a$, then $(f - g)(a) = f(a) - g(a)$.
-/
theorem pfc_sub {f g : 𝕜 → 𝕜}
    (hf : ContDiffOnSpectrum f a)
    (hg : ContDiffOnSpectrum g a) :
    pfc (f - g) a = pfc f a - pfc g a := by
  have hg' : ContDiffOnSpectrum ((-1 : 𝕜) • g) a := fun μ hμ => (hg μ hμ).const_smul (-1 : 𝕜)
  rw [sub_eq_add_neg, ← neg_one_smul 𝕜 g, pfc_add hf hg', pfc_const_smul, neg_one_smul,
    ← sub_eq_add_neg]

/-- **Commutation** ([golub2013matrix], (9.1.7)): if $b$ commutes with $a$, then $b$ commutes with
$f(a)$. -/
theorem Commute.pfc_right {b : A} (h : Commute b a) (f : 𝕜 → 𝕜) : Commute b (pfc f a) := by
  classical
  rw [pfc]
  induction interpolateJet (minpoly 𝕜 a).roots (taylorJet f) using Polynomial.induction_on with
  | C c => simpa using Algebra.commute_algebraMap_right c b
  | add p q hp hq => simpa using hp.add_right hq
  | monomial n c _ => simpa using
      (Algebra.commute_algebraMap_right c b).mul_right (h.pow_right (n + 1))

/-- Let $a \in A$ and $f : \mathbb{K} \to \mathbb{K}$. Then $a$ commutes with $f(a)$:
$$a\, f(a) = f(a)\, a.$$
This is (9.1.7) of [golub2013matrix]. -/
theorem commute_pfc (a : A) (f : 𝕜 → 𝕜) : Commute a (pfc f a) :=
  (Commute.refl a).pfc_right f

/-- For all $f$ and $g$, the elements $f(a)$ and $g(a)$ commute. -/
theorem commute_pfc_pfc (a : A) (f g : 𝕜 → 𝕜) : Commute (pfc f a) (pfc g a) := by
  rw [pfc, pfc]
  exact commute_aeval_aeval a _ _

/-- **Naturality under algebra homomorphisms.** Let $\varphi : A \to B$ be a homomorphism of
$\mathbb{K}$-algebras, and let $a \in A$ be integral over $\mathbb{K}$ with a split minimal
polynomial. Then for every $f : \mathbb{K} \to \mathbb{K}$,
$$\varphi(f(a)) = f(\varphi(a)).$$
-/
theorem AlgHom.map_pfc {B : Type*} [Ring B] [Algebra 𝕜 B] (φ : A →ₐ[𝕜] B)
    (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) (f : 𝕜 → 𝕜) :
    φ (pfc f a) = pfc f (φ a) := by
  classical
  have hdvd : minpoly 𝕜 (φ a) ∣ nodalMultiset (minpoly 𝕜 a).roots :=
    (minpoly.dvd 𝕜 (φ a) (by rw [aeval_algHom_apply, minpoly.aeval, map_zero])).trans
      (minpoly_dvd_nodalMultiset_roots ha hs)
  rw [pfc_eq_aeval_of_isJetInterpolant hdvd (isJetInterpolant_interpolateJet _ _), pfc_def,
    aeval_algHom_apply]

/-- **Multiplicativity.** Let $\mathbb{K}$ have characteristic zero, let $a \in A$ be integral over
$\mathbb{K}$ with a split minimal polynomial, and let $f$ and $g$ be $C^{m_\lambda - 1}$ on the
spectrum of $a$. Then
$$(fg)(a) = f(a)\, g(a).$$

The proof combines the Leibniz rule for Taylor coefficients (`Hermite.taylorJet_mul`) with
products of interpolants (`Hermite.IsJetInterpolant.mul`). -/
theorem pfc_mul [CharZero 𝕜] (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) {f g : 𝕜 → 𝕜}
    (hf : ContDiffOnSpectrum f a)
    (hg : ContDiffOnSpectrum g a) :
    pfc (f * g) a = pfc f a * pfc g a := by
  classical
  have hP := (isJetInterpolant_interpolateJet (minpoly 𝕜 a).roots (taylorJet f)).mul
    (isJetInterpolant_interpolateJet (minpoly 𝕜 a).roots (taylorJet g))
  rw [← isJetInterpolant_congr fun x hx n hn => ?_] at hP
  · rw [pfc_eq_aeval_of_isJetInterpolant (minpoly_dvd_nodalMultiset_roots ha hs) hP, map_mul,
      pfc_def, pfc_def]
  · rw [count_roots] at hn
    have hn' : (n : WithTop ℕ∞) ≤ ((minpoly 𝕜 a).rootMultiplicity x - 1 : ℕ) := by
      exact_mod_cast (by omega : n ≤ _)
    exact taylorJet_mul ((hf x hx).of_le hn') ((hg x hx).of_le hn')

/-- Let $\mathbb{K}$ have characteristic zero, let $a$ be integral with a split minimal polynomial,
and let $f$ and $g$ be $C^{m_\lambda - 1}$ on the spectrum of $a$. If $fg = 1$ on a
neighbourhood of every root of the minimal polynomial, then $f(a)\, g(a) = 1$. -/
theorem pfc_mul_pfc_eq_one [CharZero 𝕜] (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits)
    {f g : 𝕜 → 𝕜}
    (hf : ContDiffOnSpectrum f a)
    (hg : ContDiffOnSpectrum g a)
    (hfg : ∀ μ ∈ (minpoly 𝕜 a).roots, (f * g) =ᶠ[nhds μ] fun _ => 1) :
    pfc f a * pfc g a = 1 := by
  rw [← pfc_mul ha hs hf hg, pfc_congr (g := fun _ => (1 : 𝕜))
    fun μ hμ j _ => (hfg μ hμ).iteratedDeriv_eq j, pfc_const ha hs, map_one]

/-- **Inverses.** Let $\mathbb{K}$ have characteristic zero, let $a \in A$ be integral over
$\mathbb{K}$ with a split minimal polynomial, and let $f$ be $C^{m_\lambda - 1}$ on the spectrum
of $a$ with $f(\lambda) \neq 0$ at every root $\lambda$ of the minimal polynomial. Then $f(a)$
is invertible, and
$$(1/f)(a) = f(a)^{-1}.$$
This covers the rational functions of [golub2013matrix], §9.1.

The inverse is `Ring.inverse`, and $1/f$ is $z \mapsto f(z)^{-1}$. -/
theorem pfc_inv [CharZero 𝕜] (ha : IsIntegral 𝕜 a)
    (hs : (minpoly 𝕜 a).Splits) {f : 𝕜 → 𝕜}
    (hf : ContDiffOnSpectrum f a)
    (h0 : ∀ μ ∈ (minpoly 𝕜 a).roots, f μ ≠ 0) :
    IsUnit (pfc f a) ∧ pfc (fun z => (f z)⁻¹) a = Ring.inverse (pfc f a) := by
  have hg : ContDiffOnSpectrum (fun z => (f z)⁻¹) a := fun μ hμ => (hf μ hμ).inv (h0 μ hμ)
  have h1 := pfc_mul_pfc_eq_one ha hs hf hg fun μ hμ =>
    ((hf μ hμ).continuousAt.eventually_ne (h0 μ hμ)).mono fun z hz => mul_inv_cancel₀ hz
  have h2 : pfc (fun z => (f z)⁻¹) a * pfc f a = 1 := (commute_pfc_pfc a f _).eq.symm.trans h1
  let u : Aˣ := ⟨pfc f a, pfc (fun z => (f z)⁻¹) a, h1, h2⟩
  exact ⟨u.isUnit, (Ring.inverse_unit u).symm⟩

/-- Let $\mathbb{K}$ have characteristic zero, and let $a$ be integral with a split minimal
polynomial and $0 \notin \sigma(a)$. Then the function $z \mapsto z^{-1}$ gives the inverse
$a^{-1}$ (`Ring.inverse a`). -/
theorem pfc_inv_id [CharZero 𝕜] (ha : IsIntegral 𝕜 a)
    (hs : (minpoly 𝕜 a).Splits) (h0 : (0 : 𝕜) ∉ spectrum 𝕜 a) :
    pfc (fun z : 𝕜 => z⁻¹) a = Ring.inverse a := by
  have h := (pfc_inv ha hs (f := fun z : 𝕜 => z) (fun μ _ => contDiffAt_id) fun μ hμ hμ0 => h0 ?_).2
  · rwa [pfc_id ha hs] at h
  · rw [← hμ0]
    exact spectrum.mem_of_mem_roots_minpoly hμ

end Algebraic

section AlgEquiv

variable {B : Type*} [Ring B] [Algebra 𝕜 B]

/-- **Naturality under algebra isomorphisms.** Let $\varphi : A \to B$ be an isomorphism of
$\mathbb{K}$-algebras. Then for every $a \in A$ and every $f : \mathbb{K} \to \mathbb{K}$,
$$\varphi(f(a)) = f(\varphi(a)).$$

No hypothesis on $a$ is needed, because an algebra isomorphism preserves the minimal polynomial.
Compare `AlgHom.map_pfc`, which needs $a$ integral with a split minimal polynomial. -/
theorem AlgEquiv.map_pfc (φ : A ≃ₐ[𝕜] B) (f : 𝕜 → 𝕜) (a : A) : φ (pfc f a) = pfc f (φ a) := by
  classical
  rw [pfc_def, pfc_def, minpoly.algEquiv_eq, ← aeval_algHom_apply]

/-- Conjugation $x \mapsto u x u^{-1}$ by a unit $u$, as an algebra automorphism. -/
private def unitsConjAlgEquiv (u : Aˣ) : A ≃ₐ[𝕜] A where
  toFun x := u * x * ↑u⁻¹
  invFun x := ↑u⁻¹ * x * u
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' c := by simp [Algebra.commutes, mul_assoc]

/-- **Similarity.** For a unit $u \in A$, every $a \in A$ and every $f$,
$f(u a u^{-1}) = u\, f(a)\, u^{-1}$. -/
theorem pfc_units_conj (u : Aˣ) (f : 𝕜 → 𝕜) (a : A) :
    pfc f (u * a * ↑u⁻¹) = u * pfc f a * ↑u⁻¹ :=
  ((unitsConjAlgEquiv u).map_pfc f a).symm

end AlgEquiv

/-! ### Spectral idempotents -/

section Idempotent

/-- The jet with the value $1$ at order $0$ at the node $\mu$, and $0$ at all other orders and
nodes. -/
private def idemJet [DecidableEq 𝕜] (μ : 𝕜) : 𝕜 → ℕ → 𝕜 := fun ν j =>
  if ν = μ ∧ j = 0 then 1 else 0

private theorem idemJet_mul [DecidableEq 𝕜] (μ : 𝕜) (y : 𝕜 → ℕ → 𝕜) :
    (fun ν n => ∑ i ∈ Finset.range (n + 1), idemJet μ ν i * y ν (n - i))
      = fun ν n => if ν = μ then y ν n else 0 := by
  funext ν n
  rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [idemJet, hb]) (by simp)]
  by_cases h : ν = μ <;> simp [idemJet, h]

private theorem mul_idemJet [DecidableEq 𝕜] (μ : 𝕜) (y : 𝕜 → ℕ → 𝕜) :
    (fun ν n => ∑ i ∈ Finset.range (n + 1), y ν i * idemJet μ ν (n - i))
      = fun ν n => if ν = μ then y ν n else 0 := by
  funext ν n
  rw [Finset.sum_eq_single n (fun b hb hbn => ?_) (by simp)]
  · by_cases h : ν = μ <;> simp [idemJet, h]
  · have : n - b ≠ 0 := by
      have := Finset.mem_range.mp hb
      omega
    simp [idemJet, this]

open Classical in
/-- The **spectral idempotent** $E_\mu$ of $a$ at $\mu \in \mathbb{K}$, also called the Frobenius
covariant or the Riesz projection. It is $E_\mu = p(a)$, where $p$ is the Hermite interpolant,
at the roots of the minimal polynomial of $a$ with their multiplicities, of the jet that is
$1, 0, 0, \dots$ at $\mu$ and $0$ at the other roots.

For a matrix, $E_\mu$ is the projection onto the generalized eigenspace of $\mu$ along the other
generalized eigenspaces. If $\mu$ is not a root, then $E_\mu = 0$
(`spectralIdempotent_eq_zero_of_notMem`). -/
noncomputable def spectralIdempotent (a : A) (μ : 𝕜) : A :=
  aeval a (interpolateJet (minpoly 𝕜 a).roots (idemJet μ))

variable [DecidableEq 𝕜] {a : A}

omit [DecidableEq 𝕜] in
private theorem spectralIdempotent_def [h : DecidableEq 𝕜] (a : A) (μ : 𝕜) :
    spectralIdempotent a μ = aeval a (interpolateJet (minpoly 𝕜 a).roots (idemJet μ)) := by
  obtain rfl : h = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  rfl

/-- **The spectral idempotents are orthogonal idempotents.** Let $a \in A$ be integral over
$\mathbb{K}$ with a split minimal polynomial. For all $\lambda, \mu \in \mathbb{K}$,
$$E_\lambda E_\mu = \begin{cases} E_\lambda & \text{if } \lambda = \mu, \\ 0 & \text{if }
  \lambda \neq \mu. \end{cases}$$
-/
theorem spectralIdempotent_mul_spectralIdempotent (ha : IsIntegral 𝕜 a)
    (hs : (minpoly 𝕜 a).Splits) (l μ : 𝕜) :
    spectralIdempotent a l * spectralIdempotent a μ =
      if l = μ then spectralIdempotent a l else 0 := by
  have hdvd := minpoly_dvd_nodalMultiset_roots ha hs
  have hP := (isJetInterpolant_interpolateJet (minpoly 𝕜 a).roots (idemJet l)).mul
    (isJetInterpolant_interpolateJet (minpoly 𝕜 a).roots (idemJet μ))
  rw [idemJet_mul] at hP
  rw [spectralIdempotent_def, spectralIdempotent_def, ← map_mul]
  split_ifs with h
  · subst h
    refine aeval_eq_aeval_of_isJetInterpolant hdvd
      ((isJetInterpolant_congr fun ν _ n _ => ?_).mp hP) (isJetInterpolant_interpolateJet _ _)
    by_cases hν : ν = l <;> simp [idemJet, hν]
  · rw [← map_zero (aeval (R := 𝕜) a)]
    refine aeval_eq_aeval_of_isJetInterpolant hdvd
      ((isJetInterpolant_congr fun ν _ n _ => ?_).mp hP) (isJetInterpolant_zero _)
    by_cases hν : ν = l
    · subst hν
      simp [idemJet, h]
    · simp [hν]

/-- **The spectral idempotents are a resolution of the identity.** Let $a \in A$ be integral over
$\mathbb{K}$ with a split minimal polynomial. Then
$$\sum_\lambda E_\lambda = 1,$$
where $\lambda$ runs over the distinct roots of the minimal polynomial of $a$. -/
theorem sum_spectralIdempotent (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) :
    ∑ l ∈ (minpoly 𝕜 a).roots.toFinset, spectralIdempotent a l = 1 := by
  have hdvd := minpoly_dvd_nodalMultiset_roots ha hs
  have hP := IsJetInterpolant.sum (minpoly 𝕜 a).roots.toFinset
    fun l _ => isJetInterpolant_interpolateJet (minpoly 𝕜 a).roots (idemJet l)
  have h1 :
      IsJetInterpolant (minpoly 𝕜 a).roots (fun _ j => if j = 0 then 1 else 0) (1 : 𝕜[X]) :=
    (isJetInterpolant_congr fun x _ j _ => by rw [taylor_one, coeff_C]).mp
      (isJetInterpolant_coeff_taylor (minpoly 𝕜 a).roots 1)
  simp_rw [spectralIdempotent_def, ← map_sum, ← map_one (aeval (R := 𝕜) a)]
  refine aeval_eq_aeval_of_isJetInterpolant hdvd
    ((isJetInterpolant_congr fun ν hν n _ => ?_).mp hP) h1
  simp only [Finset.sum_apply, idemJet]
  by_cases hn : n = 0
  · simp [hn, Multiset.mem_toFinset.mpr hν]
  · simp [hn]

omit [DecidableEq 𝕜] in
/-- The element $a$ commutes with each of its spectral idempotents $E_\mu$. -/
theorem commute_spectralIdempotent (a : A) (μ : 𝕜) : Commute a (spectralIdempotent a μ) := by
  classical
  rw [spectralIdempotent_def]
  have := commute_aeval_aeval a (X : 𝕜[X]) (interpolateJet (minpoly 𝕜 a).roots (idemJet μ))
  rwa [aeval_X] at this

omit [DecidableEq 𝕜] in
/-- Let $a \in A$ be integral over $\mathbb{K}$ with a split minimal polynomial, let
$\mu \in \mathbb{K}$, and let $m_\mu$ be the multiplicity of $\mu$ as a root of the minimal
polynomial ($m_\mu = 0$ if $\mu$ is not a root). Then
$$(a - \mu)^{m_\mu} E_\mu = 0.$$
So $a - \mu$ is nilpotent on the range of $E_\mu$, of index at most $m_\mu$. -/
theorem pow_mul_spectralIdempotent (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) (μ : 𝕜) :
    (a - algebraMap 𝕜 A μ) ^ (minpoly 𝕜 a).rootMultiplicity μ * spectralIdempotent a μ = 0 := by
  classical
  have hdvd := minpoly_dvd_nodalMultiset_roots ha hs
  have hP := (isJetInterpolant_coeff_taylor (minpoly 𝕜 a).roots
    ((X - C μ) ^ (minpoly 𝕜 a).rootMultiplicity μ)).mul
    (isJetInterpolant_interpolateJet (minpoly 𝕜 a).roots (idemJet μ))
  rw [mul_idemJet] at hP
  have hP0 := aeval_eq_aeval_of_isJetInterpolant (a := a) hdvd
    ((isJetInterpolant_congr fun ν hν n hn => ?_).mp hP) (isJetInterpolant_zero _)
  · rwa [map_zero, map_mul, map_pow, map_sub, aeval_X, aeval_C, ← spectralIdempotent_def] at hP0
  · by_cases h : ν = μ
    · subst h
      rw [count_roots] at hn
      simp [taylor_pow, taylor_X, coeff_X_pow, hn.ne]
    · simp [h]

omit [DecidableEq 𝕜] in
/-- If $\mu$ is not a root of the minimal polynomial of $a$, then $E_\mu = 0$. -/
theorem spectralIdempotent_eq_zero_of_notMem {μ : 𝕜} (hμ : μ ∉ (minpoly 𝕜 a).roots) :
    spectralIdempotent a μ = 0 := by
  classical
  rw [spectralIdempotent_def, interpolateJet_congr (y' := 0) fun ν hν j _ => ?_]
  · rw [← eq_interpolateJet (p := 0) (by simp) (isJetInterpolant_zero _),
      map_zero]
  · have : ν ≠ μ := fun h => hμ (h ▸ hν)
    simp [idemJet, this]

omit [DecidableEq 𝕜] in
/-- If $a$ is integral with a split minimal polynomial and $\mu$ is a root of its minimal
polynomial, then $E_\mu \neq 0$. -/
theorem spectralIdempotent_ne_zero (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) {μ : 𝕜}
    (hμ : μ ∈ (minpoly 𝕜 a).roots) : spectralIdempotent a μ ≠ 0 := by
  classical
  intro h0
  rw [spectralIdempotent_def] at h0
  have hdvd := (minpoly_eq_nodalMultiset_roots ha hs).symm.dvd.trans (minpoly.dvd 𝕜 a h0)
  have hX : X - C μ ∣ interpolateJet (minpoly 𝕜 a).roots (idemJet μ) :=
    (dvd_pow_self _ (Multiset.count_ne_zero.mpr hμ)).trans
      ((pow_count_dvd_nodalMultiset _ μ).trans hdvd)
  have h1 := isJetInterpolant_iff_coeff_taylor.mp
    (isJetInterpolant_interpolateJet (minpoly 𝕜 a).roots (idemJet μ)) μ hμ 0
    (Multiset.count_pos.mpr hμ)
  rw [taylor_coeff_zero, (dvd_iff_isRoot.mp hX).eq_zero] at h1
  simp [idemJet] at h1

/-- **The spectral decomposition of a polynomial in $a$.** Let $a \in A$ be integral over
$\mathbb{K}$ with a split minimal polynomial, let $y$ assign to each node $\lambda$ and order
$j$ a scalar $y_\lambda(j)$, and let $p \in \mathbb{K}[X]$ interpolate these jets at the roots
of the minimal polynomial, each root $\lambda$ to its multiplicity $m_\lambda$. Then
$$p(a) = \sum_\lambda \sum_{j < m_\lambda} y_\lambda(j)\, (a - \lambda)^j E_\lambda,$$
where $\lambda$ runs over the distinct roots of the minimal polynomial. -/
theorem aeval_eq_sum_spectralIdempotent (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits)
    {y : 𝕜 → ℕ → 𝕜} {p : 𝕜[X]} (hp : IsJetInterpolant (minpoly 𝕜 a).roots y p) :
    aeval a p = ∑ l ∈ (minpoly 𝕜 a).roots.toFinset,
      ∑ j ∈ Finset.range ((minpoly 𝕜 a).rootMultiplicity l),
        y l j • ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l) := by
  have hdvd := minpoly_dvd_nodalMultiset_roots ha hs
  set m := fun l => (minpoly 𝕜 a).rootMultiplicity l
  have hQ := IsJetInterpolant.sum (minpoly 𝕜 a).roots.toFinset fun l _ =>
    (isJetInterpolant_coeff_taylor (minpoly 𝕜 a).roots (jetPoly (y l) l (m l))).mul
      (isJetInterpolant_interpolateJet (minpoly 𝕜 a).roots (idemJet l))
  simp_rw [mul_idemJet] at hQ
  rw [aeval_eq_aeval_of_isJetInterpolant hdvd hp
    ((isJetInterpolant_congr fun ν hν n hn => ?_).mp hQ)]
  · simp only [map_sum, map_mul, spectralIdempotent_def]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [jetPoly, map_sum, map_mul, map_pow, map_sub, aeval_X, aeval_C, Finset.sum_mul,
      Algebra.smul_def, mul_assoc]
    rfl
  · rw [count_roots] at hn
    simp only [Finset.sum_apply]
    simp [Finset.sum_ite_eq, hν, coeff_taylor_jetPoly, hn, m]

/-- **The spectral decomposition** (Sylvester's formula; Higham, *Functions of Matrices*, (1.9)).
Let $a \in A$ be integral over $\mathbb{K}$ with a split minimal polynomial. For every
$f : \mathbb{K} \to \mathbb{K}$,
$$f(a) = \sum_\lambda \sum_{j < m_\lambda} \frac{f^{(j)}(\lambda)}{j!} (a - \lambda)^j
  E_\lambda,$$
where $\lambda$ runs over the distinct roots of the minimal polynomial of $a$.

The coefficient $f^{(j)}(\lambda)/j!$ is `Hermite.taylorJet f λ j`. -/
theorem pfc_eq_sum_spectralIdempotent (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits)
    (f : 𝕜 → 𝕜) :
    pfc f a = ∑ l ∈ (minpoly 𝕜 a).roots.toFinset,
      ∑ j ∈ Finset.range ((minpoly 𝕜 a).rootMultiplicity l),
        taylorJet f l j • ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l) := by
  rw [pfc_def]
  exact aeval_eq_sum_spectralIdempotent ha hs (isJetInterpolant_interpolateJet _ _)

/-- **Locally constant functions.** Let $a \in A$ be integral over $\mathbb{K}$ with a split minimal
polynomial, and let $f, c : \mathbb{K} \to \mathbb{K}$. If, for each root $\lambda$ of the
minimal polynomial, $f$ equals the constant $c(\lambda)$ on a neighbourhood of $\lambda$, then
$$f(a) = \sum_\lambda c(\lambda)\, E_\lambda,$$
where $\lambda$ runs over the distinct roots. This is the principle behind the remark of
[golub2013matrix], §9.4.1, that "all the derivatives of the sign function are zero". -/
theorem pfc_eq_sum_smul_spectralIdempotent_of_eventuallyEq (ha : IsIntegral 𝕜 a)
    (hs : (minpoly 𝕜 a).Splits) {f c : 𝕜 → 𝕜}
    (h : ∀ l ∈ (minpoly 𝕜 a).roots, f =ᶠ[nhds l] fun _ => c l) :
    pfc f a = ∑ l ∈ (minpoly 𝕜 a).roots.toFinset, c l • spectralIdempotent a l := by
  rw [pfc_eq_sum_spectralIdempotent ha hs]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Multiset.mem_toFinset.mp hl
  have hm : 0 < (minpoly 𝕜 a).rootMultiplicity l := by
    rw [← count_roots]
    exact Multiset.count_pos.mpr hl'
  rw [Finset.sum_eq_single 0 (fun j _ hj => ?_) (by simp [hm])]
  · simp [taylorJet, Filter.EventuallyEq.iteratedDeriv_eq 0 (h l hl')]
  · simp [taylorJet, Filter.EventuallyEq.iteratedDeriv_eq j (h l hl'), iteratedDeriv_const, hj]

omit [DecidableEq 𝕜] in
private theorem aeval_smul_eq_aeval_comp (a : A) (s : 𝕜) (q : 𝕜[X]) :
    aeval (s • a) q = aeval a (q.comp (C s * X)) := by
  rw [aeval_comp, map_mul, aeval_C, aeval_X, Algebra.smul_def]

/-- **The primary functional calculus along a ray.** Let $a \in A$ be integral over $\mathbb{K}$
with a split minimal polynomial. For every $s \in \mathbb{K}$, $s = 0$ included, and every $f$,
$$f(sa) = \sum_\lambda \sum_{j < m_\lambda} s^j \frac{f^{(j)}(s\lambda)}{j!} (a - \lambda)^j
  E_\lambda,$$
where $\lambda$ runs over the distinct roots of the minimal polynomial of $a$ and $E_\lambda$
are the spectral idempotents of $a$.

The spectral data of $sa$ are those of $a$, rescaled. -/
theorem pfc_smul (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) (s : 𝕜) (f : 𝕜 → 𝕜) :
    pfc f (s • a) = ∑ l ∈ (minpoly 𝕜 a).roots.toFinset,
      ∑ j ∈ Finset.range ((minpoly 𝕜 a).rootMultiplicity l),
        (s ^ j * taylorJet f (s * l) j) •
          ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l) := by
  set R := (minpoly 𝕜 a).roots
  set S := R.map (s * ·)
  have hcomp : (nodalMultiset S).comp (C s * X) = C s ^ Multiset.card R * nodalMultiset R := by
    have h1 : ∀ l : 𝕜, (X - C (s * l)).comp (C s * X) = C s * (X - C l) := fun l => by
      rw [sub_comp, X_comp, C_comp, map_mul]
      ring
    rw [nodalMultiset, multiset_prod_comp, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, h1, Multiset.prod_map_mul, Multiset.map_const',
      Multiset.prod_replicate]
    rfl
  have hdvd : minpoly 𝕜 (s • a) ∣ nodalMultiset S := by
    refine minpoly.dvd 𝕜 _ ?_
    rw [aeval_smul_eq_aeval_comp, hcomp, map_mul, ← minpoly_eq_nodalMultiset_roots ha hs,
      minpoly.aeval, mul_zero]
  have hP := isJetInterpolant_interpolateJet S (taylorJet f)
  rw [pfc_eq_aeval_of_isJetInterpolant hdvd hP, aeval_smul_eq_aeval_comp]
  refine aeval_eq_sum_spectralIdempotent ha hs (isJetInterpolant_iff_coeff_taylor.mpr ?_)
  intro l hl j hj
  rw [taylor_comp_C_mul_X, comp_C_mul_X_coeff, mul_comm _ (s ^ j)]
  congr 1
  refine isJetInterpolant_iff_coeff_taylor.mp hP (s * l) (Multiset.mem_map_of_mem _ hl) j
    (lt_of_lt_of_le hj ?_)
  rw [Multiset.count_eq_card_filter_eq, Multiset.count_map]
  exact Multiset.card_le_card (Multiset.monotone_filter_right R fun x hx => by rw [hx])

end Idempotent

/-! ### The spectral mapping theorem -/

/-- **The spectral mapping theorem.** Let $a \in A$ be integral over $\mathbb{K}$ with a split
minimal polynomial. For every $f : \mathbb{K} \to \mathbb{K}$,
$$\sigma(f(a)) = f(\sigma(a)).$$
No smoothness of $f$ is needed. -/
theorem spectrum_pfc {a : A} (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits)
    (f : 𝕜 → 𝕜) : spectrum 𝕜 (pfc f a) = f '' spectrum 𝕜 a := by
  classical
  set P := interpolateJet (minpoly 𝕜 a).roots (taylorJet f)
  have hmem : ∀ l, l ∈ spectrum 𝕜 a ↔ l ∈ (minpoly 𝕜 a).roots := fun l =>
    spectrum.mem_iff_mem_roots_minpoly ha
  have hPeval : ∀ l ∈ (minpoly 𝕜 a).roots, P.eval l = f l := fun l hl => by
    have := isJetInterpolant_iff_coeff_taylor.mp (isJetInterpolant_interpolateJet _ (taylorJet f))
      l hl 0 (Multiset.count_pos.mpr hl)
    rwa [taylor_coeff_zero, taylorJet_zero] at this
  rw [pfc_def]
  apply Set.Subset.antisymm
  · intro ξ hξ
    by_contra hne
    apply spectrum.mem_iff.mp hξ
    -- `C ξ - P` is coprime to the minimal polynomial
    have hcop : IsCoprime (C ξ - P) (minpoly 𝕜 a) := by
      rw [minpoly_eq_nodalMultiset_roots ha hs, nodalMultiset_eq_prod_count]
      refine IsCoprime.prod_right fun l hl => IsCoprime.pow_right ?_
      rw [isCoprime_comm, (irreducible_X_sub_C l).coprime_iff_not_dvd, dvd_iff_isRoot, IsRoot,
        eval_sub, eval_C, hPeval l (Multiset.mem_toFinset.mp hl), sub_eq_zero]
      exact fun h => hne ⟨l, (hmem l).mpr (Multiset.mem_toFinset.mp hl), h.symm⟩
    obtain ⟨u, v, huv⟩ := hcop
    have h1 := congrArg (aeval a) huv
    rw [map_add, map_mul, map_mul, minpoly.aeval, mul_zero, add_zero, map_one, map_sub,
      aeval_C] at h1
    have hc := commute_aeval_aeval a u (C ξ - P)
    rw [map_sub, aeval_C] at hc
    exact ⟨⟨_, _, hc.eq.symm.trans h1, h1⟩, rfl⟩
  · rintro _ ⟨l, hl, rfl⟩
    rw [← hPeval l ((hmem l).mp hl)]
    exact spectrum.subset_polynomial_aeval a P ⟨l, hl, rfl⟩
