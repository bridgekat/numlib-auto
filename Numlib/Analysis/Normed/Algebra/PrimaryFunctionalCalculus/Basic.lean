import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.FieldTheory.Minpoly.Field
import Numlib.Analysis.Calculus.HermiteInterpolation

/-!
# The primary functional calculus

For an element `a` of a `𝕜`-algebra `A` over a nontrivially normed field, integral over `𝕜` with a
split minimal polynomial, and a function `f : 𝕜 → 𝕜`, the **primary functional calculus** is

  `pfc f a = p(a)`,  `p` the Hermite interpolant of `f` and its derivatives at the roots of the
  minimal polynomial of `a`, each root `λ` to its multiplicity `m_λ` (the index of `λ`).

This is Higham's definition of a matrix function by interpolation (*Functions of Matrices*,
Definition 1.4; [golub2013matrix] §9.1), for any integral element of any algebra. It is total and
algebraic: `pfc f a` is a polynomial in `a` by construction, and it depends exactly on the jets
`f⁽ʲ⁾(λ)`, `j < m_λ` (`pfc_congr`) — the formal content of "`f` is defined on the spectrum of `a`".
The Jordan-form, power-series and Cauchy-integral definitions of `f(A)` are theorems
(`Numlib/Analysis/Matrix/Function/Basic`, `…/PrimaryFunctionalCalculus/Analytic`, `…/Cauchy`).

## Main definitions

* `pfc f a`: the primary functional calculus, with junk values when `a` is not integral or its
  minimal polynomial does not split.
* `spectralIdempotent a μ`: the spectral idempotent (Frobenius covariant, Riesz projection) of `a`
  at `μ`, as a polynomial in `a`.

## Main results

* `pfc_eq_aeval_of_isJetInterpolant`: the characterization every other result goes through — any
  polynomial interpolating the jets of `f` on any multiset whose nodal polynomial the minimal
  polynomial divides computes `pfc f a`.
* `pfc_polynomial`, `pfc_const`, `pfc_id`, `pfc_pow`: polynomials are evaluated at `a`.
* `pfc_add`, `pfc_const_smul`, `pfc_mul`, `pfc_inv`: `pfc · a` is an algebra homomorphism on
  functions smooth enough at the eigenvalues.
* `commute_pfc`, `AlgHom.map_pfc`: commutation and naturality.
* `spectralIdempotent_mul_spectralIdempotent`, `sum_spectralIdempotent`, … : the spectral
  idempotents are a resolution of the identity, and `pfc_eq_sum_spectralIdempotent` is the spectral
  decomposition (Sylvester's formula).
* `spectrum_pfc`: the spectral mapping theorem `σ(f(a)) = f(σ(a))`.

## Implementation notes

The definition uses a classical `DecidableEq 𝕜` (multiplicities are counted with `Multiset.count`);
statements that mention jet interpolation take an arbitrary instance and `pfc_def` converts. The
hypotheses `IsIntegral 𝕜 a` and `(minpoly 𝕜 a).Splits` are automatic over an algebraically closed
field in a finite-dimensional algebra (matrices over `ℂ`).
-/

open Polynomial Hermite

section Spectrum

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- Polynomials in one element commute. -/
theorem commute_aeval_aeval (a : A) (p q : K[X]) : Commute (aeval a p) (aeval a q) := by
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

/-- **The spectrum of an integral element is the set of roots of its minimal polynomial.** -/
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

end Spectrum

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [Ring A] [Algebra 𝕜 A]

open Classical in
/-- **The primary functional calculus**: `pfc f a = p(a)` for the Hermite interpolant `p` of the
jets of `f` at the roots of the minimal polynomial of `a`, counted with multiplicity
([golub2013matrix] §9.1's `f(A)`; Higham, *Functions of Matrices*, Definition 1.4). Junk when `a`
is not integral or `minpoly 𝕜 a` does not split. -/
noncomputable def pfc (f : 𝕜 → 𝕜) (a : A) : A :=
  aeval a (interpolateJet (minpoly 𝕜 a).roots (taylorJet f))

/-- `pfc` unfolded with any decidable equality on `𝕜`. -/
theorem pfc_def [h : DecidableEq 𝕜] (f : 𝕜 → 𝕜) (a : A) :
    pfc f a = aeval a (interpolateJet (minpoly 𝕜 a).roots (taylorJet f)) := by
  obtain rfl : h = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  rfl

section Characterization

variable [DecidableEq 𝕜] {a : A}

omit [DecidableEq 𝕜] in
/-- The minimal polynomial of an integral element with split minimal polynomial is the nodal
polynomial of its roots. -/
theorem minpoly_eq_nodalMultiset_roots (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) :
    minpoly 𝕜 a = nodalMultiset (minpoly 𝕜 a).roots :=
  eq_nodalMultiset_roots (minpoly.monic ha) hs

/-- **Two interpolants of the same jets on a multiset whose nodal polynomial the minimal polynomial
divides agree at `a`.** -/
theorem aeval_eq_aeval_of_isJetInterpolant {s : Multiset 𝕜} (hdvd : minpoly 𝕜 a ∣ nodalMultiset s)
    {y : 𝕜 → ℕ → 𝕜} {p q : 𝕜[X]} (hp : IsJetInterpolant s y p) (hq : IsJetInterpolant s y q) :
    aeval a p = aeval a q := by
  obtain ⟨r, hr⟩ := hdvd.trans (hp.nodalMultiset_dvd_sub hq)
  rw [← sub_eq_zero, ← map_sub, hr, map_mul, minpoly.aeval, zero_mul]

omit [DecidableEq 𝕜] in
/-- The roots of the minimal polynomial are among the nodes when it divides the nodal
polynomial. -/
theorem roots_minpoly_le_of_dvd {s : Multiset 𝕜} (hdvd : minpoly 𝕜 a ∣ nodalMultiset s) :
    (minpoly 𝕜 a).roots ≤ s := by
  simpa using roots.le_of_dvd (monic_nodalMultiset s).ne_zero hdvd

/-- **The characterization of `pfc`**: if the minimal polynomial of `a` divides the nodal
polynomial of `s` (e.g. `s` the roots of the minimal polynomial, or the eigenvalues of a matrix
with algebraic multiplicities) and `p` interpolates the jets of `f` on `s`, then
`pfc f a = p(a)`. No differentiability is needed anywhere. -/
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
/-- The minimal polynomial divides the nodal polynomial of its roots when it splits. -/
theorem minpoly_dvd_nodalMultiset_roots (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) :
    minpoly 𝕜 a ∣ nodalMultiset (minpoly 𝕜 a).roots :=
  (minpoly_eq_nodalMultiset_roots ha hs).dvd

end Characterization

section Algebraic

variable {a : A}

/-- **`pfc f a` depends only on the jets of `f` at the eigenvalues up to the index**: if
`f⁽ʲ⁾(λ) = g⁽ʲ⁾(λ)` at every root `λ` of the minimal polynomial for `j` below its multiplicity,
then `pfc f a = pfc g a`. -/
theorem pfc_congr {f g : 𝕜 → 𝕜}
    (h : ∀ μ ∈ (minpoly 𝕜 a).roots, ∀ j < (minpoly 𝕜 a).rootMultiplicity μ,
      iteratedDeriv j f μ = iteratedDeriv j g μ) :
    pfc f a = pfc g a := by
  classical
  rw [pfc_def, pfc_def, interpolateJet_congr fun x hx j hj => ?_]
  rw [count_roots] at hj
  rw [taylorJet, taylorJet, h x hx j hj]

/-- **Polynomials**: `pfc (p.eval ·) a = p(a)`. -/
theorem pfc_polynomial [CharZero 𝕜] (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits)
    (p : 𝕜[X]) : pfc (fun z => p.eval z) a = aeval a p := by
  classical
  exact pfc_eq_aeval_of_isJetInterpolant (minpoly_dvd_nodalMultiset_roots ha hs)
    (isJetInterpolant_taylorJet_polynomial _ p)

theorem pfc_const [CharZero 𝕜] (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) (c : 𝕜) :
    pfc (fun _ => c) a = algebraMap 𝕜 A c := by
  simpa using pfc_polynomial ha hs (C c : 𝕜[X])

theorem pfc_id [CharZero 𝕜] (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) :
    pfc (fun z : 𝕜 => z) a = a := by
  simpa using pfc_polynomial ha hs (X : 𝕜[X])

theorem pfc_pow [CharZero 𝕜] (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) (n : ℕ) :
    pfc (fun z : 𝕜 => z ^ n) a = a ^ n := by
  simpa using pfc_polynomial ha hs ((X : 𝕜[X]) ^ n)

/-- **Linearity** of `pfc` on functions that are `C^{m_λ - 1}` at every eigenvalue `λ`. The
smoothness is needed: with Mathlib's junk derivatives, `(f + g)⁽ʲ⁾` need not be `f⁽ʲ⁾ + g⁽ʲ⁾`. -/
theorem pfc_add {f g : 𝕜 → 𝕜}
    (hf : ∀ μ ∈ (minpoly 𝕜 a).roots,
      ContDiffAt 𝕜 ((minpoly 𝕜 a).rootMultiplicity μ - 1 : ℕ) f μ)
    (hg : ∀ μ ∈ (minpoly 𝕜 a).roots,
      ContDiffAt 𝕜 ((minpoly 𝕜 a).rootMultiplicity μ - 1 : ℕ) g μ) :
    pfc (f + g) a = pfc f a + pfc g a := by
  classical
  rw [pfc_def, pfc_def, pfc_def, ← map_add, ← interpolateJet_add,
    interpolateJet_congr fun x hx j hj => ?_]
  rw [count_roots] at hj
  have hj' : (j : WithTop ℕ∞) ≤ ((minpoly 𝕜 a).rootMultiplicity x - 1 : ℕ) := by
    exact_mod_cast (by omega : j ≤ _)
  exact taylorJet_add ((hf x hx).of_le hj') ((hg x hx).of_le hj')

theorem pfc_const_smul (c : 𝕜) (f : 𝕜 → 𝕜) : pfc (c • f) a = c • pfc f a := by
  classical
  have h : taylorJet (c • f) = c • taylorJet f := by
    ext x j
    rw [taylorJet_const_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [pfc_def, pfc_def, h, interpolateJet_smul, map_smul]

theorem pfc_sub {f g : 𝕜 → 𝕜}
    (hf : ∀ μ ∈ (minpoly 𝕜 a).roots,
      ContDiffAt 𝕜 ((minpoly 𝕜 a).rootMultiplicity μ - 1 : ℕ) f μ)
    (hg : ∀ μ ∈ (minpoly 𝕜 a).roots,
      ContDiffAt 𝕜 ((minpoly 𝕜 a).rootMultiplicity μ - 1 : ℕ) g μ) :
    pfc (f - g) a = pfc f a - pfc g a := by
  have hg' : ∀ μ ∈ (minpoly 𝕜 a).roots,
      ContDiffAt 𝕜 ((minpoly 𝕜 a).rootMultiplicity μ - 1 : ℕ) ((-1 : 𝕜) • g) μ :=
    fun μ hμ => (hg μ hμ).const_smul (-1 : 𝕜)
  rw [sub_eq_add_neg, ← neg_one_smul 𝕜 g, pfc_add hf hg', pfc_const_smul, neg_one_smul,
    ← sub_eq_add_neg]

/-- **Commutation** ([golub2013matrix] (9.1.7)): whatever commutes with `a` commutes with
`pfc f a`. -/
theorem Commute.pfc_right {b : A} (h : Commute b a) (f : 𝕜 → 𝕜) : Commute b (pfc f a) := by
  classical
  rw [pfc]
  induction interpolateJet (minpoly 𝕜 a).roots (taylorJet f) using Polynomial.induction_on with
  | C c => simpa using Algebra.commute_algebraMap_right c b
  | add p q hp hq => simpa using hp.add_right hq
  | monomial n c _ => simpa using
      (Algebra.commute_algebraMap_right c b).mul_right (h.pow_right (n + 1))

/-- `a` commutes with `pfc f a` ([golub2013matrix] (9.1.7), `A f(A) = f(A) A`). -/
theorem commute_pfc (a : A) (f : 𝕜 → 𝕜) : Commute a (pfc f a) :=
  (Commute.refl a).pfc_right f

theorem commute_pfc_pfc (a : A) (f g : 𝕜 → 𝕜) : Commute (pfc f a) (pfc g a) := by
  rw [pfc, pfc]
  exact commute_aeval_aeval a _ _

/-- **Naturality** under algebra homomorphisms: `φ (f(a)) = f(φ a)`. -/
theorem AlgHom.map_pfc {B : Type*} [Ring B] [Algebra 𝕜 B] (φ : A →ₐ[𝕜] B)
    (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) (f : 𝕜 → 𝕜) :
    φ (pfc f a) = pfc f (φ a) := by
  classical
  have hdvd : minpoly 𝕜 (φ a) ∣ nodalMultiset (minpoly 𝕜 a).roots :=
    (minpoly.dvd 𝕜 (φ a) (by rw [aeval_algHom_apply, minpoly.aeval, map_zero])).trans
      (minpoly_dvd_nodalMultiset_roots ha hs)
  rw [pfc_eq_aeval_of_isJetInterpolant hdvd (isJetInterpolant_interpolateJet _ _), pfc_def,
    aeval_algHom_apply]

/-- **Multiplicativity** of `pfc` on functions that are `C^{m_λ - 1}` at every eigenvalue: the
Leibniz rule for jets (`Hermite.taylorJet_mul`) and products of interpolants
(`Hermite.IsJetInterpolant.mul`). -/
theorem pfc_mul [CharZero 𝕜] (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits) {f g : 𝕜 → 𝕜}
    (hf : ∀ μ ∈ (minpoly 𝕜 a).roots,
      ContDiffAt 𝕜 ((minpoly 𝕜 a).rootMultiplicity μ - 1 : ℕ) f μ)
    (hg : ∀ μ ∈ (minpoly 𝕜 a).roots,
      ContDiffAt 𝕜 ((minpoly 𝕜 a).rootMultiplicity μ - 1 : ℕ) g μ) :
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

/-- Functions whose product is `1` near every eigenvalue give inverse elements. -/
theorem pfc_mul_pfc_eq_one [CharZero 𝕜] (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits)
    {f g : 𝕜 → 𝕜}
    (hf : ∀ μ ∈ (minpoly 𝕜 a).roots,
      ContDiffAt 𝕜 ((minpoly 𝕜 a).rootMultiplicity μ - 1 : ℕ) f μ)
    (hg : ∀ μ ∈ (minpoly 𝕜 a).roots,
      ContDiffAt 𝕜 ((minpoly 𝕜 a).rootMultiplicity μ - 1 : ℕ) g μ)
    (hfg : ∀ μ ∈ (minpoly 𝕜 a).roots, (f * g) =ᶠ[nhds μ] fun _ => 1) :
    pfc f a * pfc g a = 1 := by
  rw [← pfc_mul ha hs hf hg, pfc_congr (g := fun _ => (1 : 𝕜))
    fun μ hμ j _ => Filter.EventuallyEq.iteratedDeriv_eq j (hfg μ hμ), pfc_const ha hs, map_one]

/-- **Inverses**: if `f` is `C^{m_λ - 1}` and nonvanishing at every eigenvalue `λ`, then `f(a)` is
invertible with inverse `(1/f)(a)` ([golub2013matrix] §9.1's rational functions). -/
theorem pfc_inv [CharZero 𝕜] [CompleteSpace 𝕜] (ha : IsIntegral 𝕜 a)
    (hs : (minpoly 𝕜 a).Splits) {f : 𝕜 → 𝕜}
    (hf : ∀ μ ∈ (minpoly 𝕜 a).roots,
      ContDiffAt 𝕜 ((minpoly 𝕜 a).rootMultiplicity μ - 1 : ℕ) f μ)
    (h0 : ∀ μ ∈ (minpoly 𝕜 a).roots, f μ ≠ 0) :
    IsUnit (pfc f a) ∧ pfc (fun z => (f z)⁻¹) a = Ring.inverse (pfc f a) := by
  have hg : ∀ μ ∈ (minpoly 𝕜 a).roots,
      ContDiffAt 𝕜 ((minpoly 𝕜 a).rootMultiplicity μ - 1 : ℕ) (fun z => (f z)⁻¹) μ :=
    fun μ hμ => (hf μ hμ).inv (h0 μ hμ)
  have h1 := pfc_mul_pfc_eq_one ha hs hf hg fun μ hμ =>
    ((hf μ hμ).continuousAt.eventually_ne (h0 μ hμ)).mono fun z hz => mul_inv_cancel₀ hz
  have h2 : pfc (fun z => (f z)⁻¹) a * pfc f a = 1 := (commute_pfc_pfc a f _).eq.symm.trans h1
  let u : Aˣ := ⟨pfc f a, pfc (fun z => (f z)⁻¹) a, h1, h2⟩
  exact ⟨u.isUnit, (Ring.inverse_unit u).symm⟩

/-- The inverse of an element with `0` outside its spectrum is `pfc (·⁻¹)`. -/
theorem pfc_inv_id [CharZero 𝕜] [CompleteSpace 𝕜] (ha : IsIntegral 𝕜 a)
    (hs : (minpoly 𝕜 a).Splits) (h0 : (0 : 𝕜) ∉ spectrum 𝕜 a) :
    pfc (fun z : 𝕜 => z⁻¹) a = Ring.inverse a := by
  have h := (pfc_inv ha hs (f := fun z : 𝕜 => z) (fun μ _ => contDiffAt_id) fun μ hμ hμ0 => h0 ?_).2
  · rwa [pfc_id ha hs] at h
  · rw [spectrum.mem_iff_isRoot_minpoly ha, ← hμ0]
    exact (mem_roots (minpoly.ne_zero ha)).mp hμ

end Algebraic

/-! ### Spectral idempotents -/

section Idempotent

/-- The jet with a single `1` at order `0` at the node `μ`. -/
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
/-- The **spectral idempotent** (Frobenius covariant, Riesz projection) of `a` at `μ`: `E_μ = p(a)`
for the Hermite interpolant `p` of the jets `1, 0, 0, …` at `μ` and `0` at the other roots of the
minimal polynomial. For a matrix it is the projection onto the generalized eigenspace of `μ` along
the others. -/
noncomputable def spectralIdempotent (a : A) (μ : 𝕜) : A :=
  aeval a (interpolateJet (minpoly 𝕜 a).roots (idemJet μ))

variable [DecidableEq 𝕜] {a : A}

omit [DecidableEq 𝕜] in
private theorem spectralIdempotent_def [h : DecidableEq 𝕜] (a : A) (μ : 𝕜) :
    spectralIdempotent a μ = aeval a (interpolateJet (minpoly 𝕜 a).roots (idemJet μ)) := by
  obtain rfl : h = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  rfl

/-- The spectral idempotents are **orthogonal idempotents**: `E_λ E_μ = δ_{λμ} E_λ`. -/
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

/-- The spectral idempotents are a **resolution of the identity**: `∑_λ E_λ = 1`. -/
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
/-- The spectral idempotents commute with `a`. -/
theorem commute_spectralIdempotent (a : A) (μ : 𝕜) : Commute a (spectralIdempotent a μ) := by
  classical
  rw [spectralIdempotent_def]
  have := commute_aeval_aeval a (X : 𝕜[X]) (interpolateJet (minpoly 𝕜 a).roots (idemJet μ))
  rwa [aeval_X] at this

omit [DecidableEq 𝕜] in
/-- On the range of `E_μ`, `a - μ` is nilpotent of index at most the multiplicity `m_μ`:
`(a - μ)^{m_μ} E_μ = 0`. -/
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
/-- `E_μ = 0` when `μ` is not an eigenvalue. -/
theorem spectralIdempotent_eq_zero_of_notMem {μ : 𝕜} (hμ : μ ∉ (minpoly 𝕜 a).roots) :
    spectralIdempotent a μ = 0 := by
  classical
  rw [spectralIdempotent_def, interpolateJet_congr (y' := 0) fun ν hν j _ => ?_]
  · rw [← eq_interpolateJet (p := 0) (by simp) (isJetInterpolant_zero _),
      map_zero]
  · have : ν ≠ μ := fun h => hμ (h ▸ hν)
    simp [idemJet, this]

omit [DecidableEq 𝕜] in
/-- `E_μ ≠ 0` at an eigenvalue `μ`. -/
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

/-- **The spectral decomposition of a polynomial in `a`**: if `p` interpolates the jets `y` at the
roots of the minimal polynomial, then `p(a) = ∑_λ ∑_{j < m_λ} y λ j (a - λ)ʲ E_λ`. -/
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

/-- **The spectral decomposition** (Sylvester's formula; Higham, *Functions of Matrices*, (1.9)):
`f(a) = ∑_λ ∑_{j < m_λ} f⁽ʲ⁾(λ)/j! (a - λ)ʲ E_λ`. -/
theorem pfc_eq_sum_spectralIdempotent (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits)
    (f : 𝕜 → 𝕜) :
    pfc f a = ∑ l ∈ (minpoly 𝕜 a).roots.toFinset,
      ∑ j ∈ Finset.range ((minpoly 𝕜 a).rootMultiplicity l),
        taylorJet f l j • ((a - algebraMap 𝕜 A l) ^ j * spectralIdempotent a l) := by
  rw [pfc_def]
  exact aeval_eq_sum_spectralIdempotent ha hs (isJetInterpolant_interpolateJet _ _)

/-- **Locally constant functions** ([golub2013matrix] §9.4.1: "all the derivatives of the sign
function are zero"): if `f` is constant `c λ` near every eigenvalue `λ`, then
`f(a) = ∑_λ c λ • E_λ`. -/
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
/-- Coefficients of `q(sX)`. -/
private theorem coeff_comp_C_mul_X (q : 𝕜[X]) (s : 𝕜) (j : ℕ) :
    (q.comp (C s * X)).coeff j = s ^ j * q.coeff j := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc,
      ← C_mul, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with h
    · subst h
      ring
    · simp

omit [DecidableEq 𝕜] in
private theorem taylor_comp_C_mul_X (q : 𝕜[X]) (s l : 𝕜) :
    taylor l (q.comp (C s * X)) = (taylor (s * l) q).comp (C s * X) := by
  simp only [taylor_apply, comp_assoc, mul_comp, C_comp, X_comp, add_comp]
  congr 1
  rw [map_mul]
  ring

omit [DecidableEq 𝕜] in
private theorem aeval_smul_eq_aeval_comp (a : A) (s : 𝕜) (q : 𝕜[X]) :
    aeval (s • a) q = aeval a (q.comp (C s * X)) := by
  rw [aeval_comp, map_mul, aeval_C, aeval_X, Algebra.smul_def]

/-- **`pfc` along a ray**: `f(s a) = ∑_λ ∑_{j < m_λ} sʲ f⁽ʲ⁾(sλ)/j! (a - λ)ʲ E_λ` for every
`s : 𝕜`, `s = 0` included; the spectral data of `s • a` are those of `a`, rescaled. -/
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
  rw [taylor_comp_C_mul_X, coeff_comp_C_mul_X]
  congr 1
  refine isJetInterpolant_iff_coeff_taylor.mp hP (s * l) (Multiset.mem_map_of_mem _ hl) j
    (lt_of_lt_of_le hj ?_)
  rw [Multiset.count_eq_card_filter_eq, Multiset.count_map]
  exact Multiset.card_le_card (Multiset.monotone_filter_right R fun x hx => by rw [hx])

end Idempotent

/-! ### The spectral mapping theorem -/

/-- **The spectral mapping theorem**: `σ(f(a)) = f(σ(a))`. -/
theorem spectrum_pfc {a : A} (ha : IsIntegral 𝕜 a) (hs : (minpoly 𝕜 a).Splits)
    (f : 𝕜 → 𝕜) : spectrum 𝕜 (pfc f a) = f '' spectrum 𝕜 a := by
  classical
  set P := interpolateJet (minpoly 𝕜 a).roots (taylorJet f)
  have hmem : ∀ l, l ∈ spectrum 𝕜 a ↔ l ∈ (minpoly 𝕜 a).roots := fun l => by
    rw [spectrum.mem_iff_isRoot_minpoly ha, mem_roots (minpoly.ne_zero ha)]
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
