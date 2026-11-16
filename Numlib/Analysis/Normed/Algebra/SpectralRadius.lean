/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Algebra.Spectrum`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Spectral radius and convergence of powers

Let $\rho(a) = \sup\{|\lambda| : \lambda \in \sigma(a)\}$ be the spectral radius of an element $a$
of an algebra, a value in $[0, \infty]$. In a complex unital Banach algebra, $\rho(a) < 1$ holds if
and only if $a^n \to 0$, if and only if $\|a^n\| < 1$ for some $n$, and if and only if the Neumann
series $\sum_n a^n$ converges; then $\sum_n a^n = (1 - a)^{-1}$. The powers also decay geometrically
at any rate above $\rho(a)$. All of these are classical consequences of Gelfand's formula
$\|a^n\|^{1/n} \to \rho(a)$, which Mathlib provides as
`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`.

The module also proves the algebraic properties of the spectral radius (absolute homogeneity,
invariance under the star, the power rule $\rho(a^n) = \rho(a)^n$), and the bound $\rho(a) \le N(a)$
for an arbitrary algebra norm $N$ on a finite-dimensional algebra. With it comes the two-sided bound
$1/(1 + N(a)) \le N((1 - a)^{-1}) \le 1/(1 - N(a))$ of [quarteroni2000numerical], (1.26). Finally it
defines the spectral abscissa $\alpha(a) = \sup\{\operatorname{Re} \lambda : \lambda \in
\sigma(a)\}$ of [golub2013matrix], (9.3.3), the analogue of the spectral radius for half planes.

## Main definitions

* `spectralAbscissa`: the spectral abscissa $\alpha(a) = \sup\{\operatorname{Re} \lambda : \lambda
  \in \sigma(a)\}$.

## Main results

* `spectralRadius_smul`, `spectralRadius_star`, `spectralRadius_eq_iSup_diff_singleton_zero`:
  $\rho(ca) = |c| \rho(a)$ in any algebra over a normed field; the star and the eigenvalue $0$ do
  not change $\rho$.
* `spectralRadius_pow_of_nonempty`, `spectralRadius_pow`: the power rule $\rho(a^n) = \rho(a)^n$.
* `spectrum.spectralRadius_ne_top`,
  `spectrum.pow_norm_pow_one_div_tendsto_nhds_toReal_spectralRadius`: the spectral radius is finite,
  and Gelfand's formula holds as a limit in $\mathbb{R}$.
* `exists_norm_pow_le_of_spectralRadius_lt`: $\|a^n\| \le C r^n$ for every $r > \rho(a)$.
* `spectralRadius_lt_one_iff_tendsto_pow`, `spectralRadius_lt_one_iff_exists_norm_pow_lt_one`,
  `summable_pow_iff_spectralRadius_lt_one`: three criteria for $\rho(a) < 1$ in terms of the powers.
* `hasSum_pow_inverse_one_sub_of_spectralRadius_lt_one`: the Neumann series
  $\sum_n a^n = (1 - a)^{-1}$ under $\rho(a) < 1$ alone.
* `spectralRadius_le_algebraNorm`: $\rho(a) \le N(a)$ for an arbitrary algebra norm $N$ on a
  finite-dimensional algebra.
* `isUnit_one_sub_of_algebraNorm_lt_one`, `AlgebraNorm.norm_inverse_one_sub_le_of_lt_one`,
  `AlgebraNorm.one_div_one_add_le_norm_inverse_one_sub`: if $N(1) = 1$ and $N(a) < 1$, then $1 - a$
  is invertible and $1/(1 + N(a)) \le N((1 - a)^{-1}) \le 1/(1 - N(a))$.
* `re_le_spectralAbscissa`, `exists_mem_spectrum_re_eq_spectralAbscissa`,
  `spectralAbscissa_le_norm`: every eigenvalue has real part at most $\alpha(a)$, some eigenvalue
  attains it when the spectrum is nonempty and compact, and $\alpha(a) \le \|a\|$.

## Implementation notes

* The spectral radius is Mathlib's `spectralRadius`, with values in `ℝ≥0∞`.
* Several results do not assume $\|1\| = 1$ (`NormOneClass`). This matters for the operator algebra
  `E →L[𝕜] E`, in which $\|1\| = 1$ holds only for nontrivial `E`.
* An algebra norm is bundled as an `AlgebraNorm` and is not an instance; the sectioning comment
  before `spectralRadius_le_algebraNorm` gives the reason.
-/

open Filter Topology
open scoped ENNReal NNReal

section Homogeneous

open scoped Pointwise

variable {𝕜 B : Type*} [NormedField 𝕜] [Ring B] [Algebra 𝕜 B]

/-- Let $\mathbb{K}$ be a normed field and $B$ a $\mathbb{K}$-algebra. The spectral radius is
absolutely homogeneous: for every $c \in \mathbb{K}$ and $a \in B$,
$$\rho(ca) = |c|\, \rho(a).$$

The statement is algebraic. It restates `spectrum.unit_smul_eq_smul`, which gives
$\sigma(ca) = c\, \sigma(a)$ for $c \neq 0$; neither completeness of the algebra nor
submultiplicativity of a norm is used. The product is taken in $[0, \infty]$. -/
theorem spectralRadius_smul (c : 𝕜) (a : B) :
    spectralRadius 𝕜 (c • a) = ‖c‖₊ * spectralRadius 𝕜 a := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hset : spectrum 𝕜 (c • a) = c • spectrum 𝕜 a := by
      simpa [Units.smul_def] using spectrum.unit_smul_eq_smul a (Units.mk0 c hc)
    simp only [spectralRadius_eq_of_unital, hset, ← Set.image_smul, iSup_image, smul_eq_mul,
      nnnorm_mul, ENNReal.coe_mul, ENNReal.mul_iSup]

/-- Let $\mathbb{K}$ be a normed field, $B$ a $\mathbb{K}$-algebra and $a \in B$. The eigenvalue $0$
does not change the spectral radius:
$$\rho(a) = \sup_{\mu \in \sigma(a) \setminus \{0\}} |\mu|,$$
a supremum in $[0, \infty]$, which is $0$ for an empty set. -/
theorem spectralRadius_eq_iSup_diff_singleton_zero (a : B) :
    spectralRadius 𝕜 a = ⨆ μ ∈ spectrum 𝕜 a \ {0}, (‖μ‖₊ : ℝ≥0∞) := by
  rw [spectralRadius_eq_of_unital]
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) (iSup₂_le fun μ hμ =>
    le_iSup₂ (f := fun μ (_ : μ ∈ spectrum 𝕜 a) => ((‖μ‖₊ : ℝ≥0) : ℝ≥0∞)) μ hμ.1)
  rcases eq_or_ne μ 0 with rfl | h0
  · simp
  · exact le_iSup₂ (f := fun μ (_ : μ ∈ spectrum 𝕜 a \ {0}) => ((‖μ‖₊ : ℝ≥0) : ℝ≥0∞)) μ ⟨hμ, h0⟩

/-- Let $\mathbb{K}$ be a normed field with a star operation that preserves the norm, and let $B$ be
a $\mathbb{K}$-algebra with a star operation compatible with the scalar multiplication. Then for
every $a \in B$,
$$\rho(a^*) = \rho(a).$$

The proof uses $\sigma(a^*) = \overline{\sigma(a)}$ (`spectrum.map_star`) and the invariance of
the norm under the star. -/
theorem spectralRadius_star [StarRing 𝕜] [NormedStarGroup 𝕜] [StarRing B] [StarModule 𝕜 B]
    (a : B) : spectralRadius 𝕜 (star a) = spectralRadius 𝕜 a := by
  have key : ∀ b : B, spectralRadius 𝕜 (star b) ≤ spectralRadius 𝕜 b := fun b => by
    rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital]
    refine iSup₂_le fun k hk => ?_
    rw [spectrum.map_star, Set.mem_star] at hk
    calc ((‖k‖₊ : ℝ≥0) : ℝ≥0∞) = ‖star k‖₊ := by rw [nnnorm_star]
      _ ≤ ⨆ k ∈ spectrum 𝕜 b, ((‖k‖₊ : ℝ≥0) : ℝ≥0∞) :=
        le_iSup₂ (f := fun k (_ : k ∈ spectrum 𝕜 b) => ((‖k‖₊ : ℝ≥0) : ℝ≥0∞)) (star k) hk
  exact le_antisymm (key a) (by simpa using key (star a))

/-- **The power rule.** Let $\mathbb{K}$ be an algebraically closed normed field, let $B$ be a
$\mathbb{K}$-algebra, and let $a \in B$ have nonempty spectrum. Then for every
$n \in \mathbb{N}$,
$$\rho(a^n) = \rho(a)^n.$$

The spectral mapping theorem `spectrum.map_pow_of_nonempty` gives $\sigma(a^n) = \{\lambda^n :
\lambda \in \sigma(a)\}$, and $t \mapsto t^n$ commutes with the supremum. Nonemptiness is needed
only at $n = 0$, where it makes the algebra nontrivial. -/
theorem spectralRadius_pow_of_nonempty [IsAlgClosed 𝕜] {a : B} (ha : (spectrum 𝕜 a).Nonempty)
    (n : ℕ) : spectralRadius 𝕜 (a ^ n) = spectralRadius 𝕜 a ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Nontrivial B := by
      obtain ⟨z, hz⟩ := ha
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact spectrum.mem_iff.mp hz (isUnit_of_subsingleton _)
    simp
  refine le_antisymm ?_ (spectrum.spectralRadius_pow_le a n hn.ne')
  rw [spectralRadius_eq_of_unital, spectralRadius_eq_of_unital, spectrum.map_pow_of_nonempty ha n]
  refine iSup₂_le fun z hz => ?_
  obtain ⟨w, hw, rfl⟩ := hz
  calc (‖w ^ n‖₊ : ℝ≥0∞) = (‖w‖₊ : ℝ≥0∞) ^ n := by rw [nnnorm_pow, ENNReal.coe_pow]
    _ ≤ (⨆ k ∈ spectrum 𝕜 a, (‖k‖₊ : ℝ≥0∞)) ^ n :=
        pow_le_pow_left' (le_iSup₂ (f := fun k (_ : k ∈ spectrum 𝕜 a) => (‖k‖₊ : ℝ≥0∞)) w hw) n

end Homogeneous

section Finite

variable {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

/-- Let $\mathbb{K}$ be a normed field and $A$ a complete normed $\mathbb{K}$-algebra. The spectral
radius of every $a \in A$ is finite: $\rho(a) < \infty$.

The spectrum lies in the closed ball of radius $\|a\| \|1\|$, by
`spectrum.spectralRadius_le_pow_nnnorm_pow_one_div` at $n = 0$. -/
theorem spectrum.spectralRadius_ne_top (a : A) : spectralRadius 𝕜 a ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.coe_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.coe_ne_top))
    (spectrum.spectralRadius_le_pow_nnnorm_pow_one_div 𝕜 a 0)

end Finite

section Conjugate

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]

/-- Let $\mathbb{K}$ be a nontrivially normed field, $E$ a Banach space over $\mathbb{K}$, and $P$
and $v$ bounded operators on $E$ with $v$ invertible. Then
$$\rho(P) \le \|v P v^{-1}\|.$$

Similarity preserves the spectrum, and the spectral radius is at most the norm. The inverse is
`Ring.inverse v`. -/
theorem spectralRadius_le_nnnorm_conj {v : E →L[𝕜] E} (hv : IsUnit v) (P : E →L[𝕜] E) :
    spectralRadius 𝕜 P ≤ ‖v * P * Ring.inverse v‖₊ := by
  obtain ⟨u, rfl⟩ := hv
  rw [Ring.inverse_unit]
  rcases subsingleton_or_nontrivial E with _ | _
  · have : Subsingleton (E →L[𝕜] E) := ⟨fun _ _ => by ext x; exact Subsingleton.elim _ _⟩
    simp [spectralRadius]
  · rw [spectralRadius_eq_of_unital, ← spectrum.units_conjugate (a := P) (u := u)]
    exact iSup₂_le fun k hk => mod_cast spectrum.norm_le_norm_of_mem hk

end Conjugate

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

omit [NormOneClass A] in
/-- **Gelfand's formula, real-valued.** Let $A$ be a complex Banach algebra and $a \in A$. Then
$$\|a^n\|^{1/n} \to \rho(a) \qquad (n \to \infty)$$
in $\mathbb{R}$; the spectral radius is finite by `spectrum.spectralRadius_ne_top`.

This is Mathlib's `spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius` with the coercions
to `ℝ≥0∞` removed, which is the form that limit arguments independent of the norm use. -/
theorem spectrum.pow_norm_pow_one_div_tendsto_nhds_toReal_spectralRadius (a : A) :
    Tendsto (fun n : ℕ => ‖a ^ n‖ ^ (1 / n : ℝ)) atTop (𝓝 (spectralRadius ℂ a).toReal) := by
  have h := (ENNReal.tendsto_toReal (spectrum.spectralRadius_ne_top a)).comp
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a)
  refine h.congr fun k => ?_
  simp only [Function.comp_apply]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)

omit [NormOneClass A] in
/-- If $\rho(a) < r$, then Gelfand's formula gives $\|a^n\| \le r^n$ for all large $n$. -/
private theorem eventually_norm_pow_le_of_spectralRadius_lt (a : A) {r : NNReal}
    (hr : spectralRadius ℂ a < r) : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ (r : ℝ) ^ n := by
  have h := (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a).eventually_lt_const hr
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hn0 : n ≠ 0 := by omega
  have key : (‖a ^ n‖₊ : ℝ≥0∞) < (r : ℝ≥0∞) ^ n :=
    calc (‖a ^ n‖₊ : ℝ≥0∞) = ((‖a ^ n‖₊ : ℝ≥0∞) ^ ((n : ℝ)⁻¹)) ^ n :=
          (ENNReal.rpow_inv_natCast_pow hn0 _).symm
      _ < (r : ℝ≥0∞) ^ n := ENNReal.pow_lt_pow_left hn0 (by rwa [one_div] at hn)
  rw [← ENNReal.coe_pow, ENNReal.coe_lt_coe] at key
  exact_mod_cast key.le

omit [NormOneClass A] in
/-- **Geometric decay of the powers.** Let $A$ be a complex Banach algebra, let $a \in A$, and let
$r \ge 0$ with $\rho(a) < r$. Then there is a constant $C \ge 0$ with
$$\|a^n\| \le C r^n \qquad \text{for all } n \in \mathbb{N}.$$
-/
theorem exists_norm_pow_le_of_spectralRadius_lt (a : A) {r : NNReal}
    (hr : spectralRadius ℂ a < r) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖a ^ n‖ ≤ C * (r : ℝ) ^ n := by
  have hrne : r ≠ 0 := by rintro rfl; simp at hr
  have hr0 : (0 : ℝ) < r := by
    have : (0 : ℝ≥0) < r := pos_iff_ne_zero.mpr hrne
    exact_mod_cast this
  obtain ⟨N, hN⟩ :=
    eventually_atTop.mp (eventually_norm_pow_le_of_spectralRadius_lt a hr)
  set S : ℝ := ∑ i ∈ Finset.range N, ‖a ^ i‖ / (r : ℝ) ^ i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨1 + S, by linarith, fun n => ?_⟩
  have hrn : (0 : ℝ) < (r : ℝ) ^ n := by positivity
  rcases lt_or_ge n N with hn | hn
  · have h1 : ‖a ^ n‖ / (r : ℝ) ^ n ≤ S :=
      hS ▸ Finset.single_le_sum (f := fun i => ‖a ^ i‖ / (r : ℝ) ^ i)
        (fun i _ => by positivity) (Finset.mem_range.mpr hn)
    rw [div_le_iff₀ hrn] at h1
    nlinarith
  · have := hN n hn
    nlinarith

/-- Let $A$ be a complex Banach algebra with $\|1\| = 1$. If $\|a^n\| < 1$ for some $n$, then
$\rho(a) < 1$, because $\rho(a)^n = \rho(a^n) \le \|a^n\| < 1$. -/
theorem spectralRadius_lt_one_of_norm_pow_lt_one {a : A} {n : ℕ} (h : ‖a ^ n‖ < 1) :
    spectralRadius ℂ a < 1 := by
  have hn : n ≠ 0 := by rintro rfl; simp at h
  rcases lt_or_ge (spectralRadius ℂ a) 1 with h' | hc
  · exact h'
  have h1 : (1 : ℝ≥0∞) ≤ spectralRadius ℂ (a ^ n) :=
    (one_le_pow₀ hc).trans (spectrum.spectralRadius_pow_le a n hn)
  have h2 : spectralRadius ℂ (a ^ n) ≤ (‖a ^ n‖₊ : ℝ≥0∞) := spectralRadius_le_nnnorm _
  have h3 : (‖a ^ n‖₊ : ℝ≥0∞) < 1 := by
    rw [ENNReal.coe_lt_one_iff]
    exact_mod_cast h
  exact absurd (h1.trans_lt (h2.trans_lt h3)) (lt_irrefl 1)

omit [NormOneClass A] in
/-- Let $A$ be a complex Banach algebra and $a \in A$ with $\rho(a) < 1$. Then $a^n \to 0$ as
$n \to \infty$.

This half of `spectralRadius_lt_one_iff_tendsto_pow` does not need $\|1\| = 1$. This matters for
the operator algebra `E →L[𝕜] E`, in which $\|1\| = 1$ holds only for nontrivial `E`. -/
theorem tendsto_pow_of_spectralRadius_lt_one {a : A} (h : spectralRadius ℂ a < 1) :
    Tendsto (fun n => a ^ n) atTop (𝓝 0) := by
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  obtain ⟨C, _, hC⟩ := exists_norm_pow_le_of_spectralRadius_lt a hr1
  have hrlt : (r : ℝ) < 1 := by exact_mod_cast ENNReal.coe_lt_one_iff.mp hr2
  refine squeeze_zero_norm hC ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg hrlt).const_mul C

/-- Let $A$ be a complex Banach algebra with $\|1\| = 1$ and $a \in A$. Then $\rho(a) < 1$ if and
only if $a^n \to 0$ as $n \to \infty$. -/
theorem spectralRadius_lt_one_iff_tendsto_pow (a : A) :
    spectralRadius ℂ a < 1 ↔ Tendsto (fun n => a ^ n) atTop (𝓝 0) := by
  refine ⟨tendsto_pow_of_spectralRadius_lt_one, fun h => ?_⟩
  have hnorm : Tendsto (fun n => ‖a ^ n‖) atTop (𝓝 0) := by simpa using h.norm
  obtain ⟨n, hn⟩ := (hnorm.eventually_lt_const one_pos).exists
  exact spectralRadius_lt_one_of_norm_pow_lt_one hn

/-- Let $A$ be a complex Banach algebra with $\|1\| = 1$ and $a \in A$. If $\|a\| < 1$, then
$\rho(a) < 1$.

The converse fails: a nilpotent matrix of large norm has spectral radius $0$. The correct
converse is `spectralRadius_lt_one_iff_exists_norm_pow_lt_one`, which asks only that some power
of $a$ have norm less than $1$. -/
theorem spectralRadius_lt_one_of_norm_lt_one {a : A} (h : ‖a‖ < 1) : spectralRadius ℂ a < 1 :=
  spectralRadius_lt_one_of_norm_pow_lt_one (n := 1) (by rwa [pow_one])

/-- Let $A$ be a complex Banach algebra with $\|1\| = 1$ and $a \in A$. Then $\rho(a) < 1$ if and
only if $\|a^n\| < 1$ for some $n \in \mathbb{N}$. -/
theorem spectralRadius_lt_one_iff_exists_norm_pow_lt_one (a : A) :
    spectralRadius ℂ a < 1 ↔ ∃ n, ‖a ^ n‖ < 1 := by
  refine ⟨fun h => ?_, fun ⟨_, hn⟩ => spectralRadius_lt_one_of_norm_pow_lt_one hn⟩
  have hnorm : Tendsto (fun n => ‖a ^ n‖) atTop (𝓝 0) := by
    simpa using ((spectralRadius_lt_one_iff_tendsto_pow a).mp h).norm
  exact (hnorm.eventually_lt_const one_pos).exists

/-- Let $A$ be a complex Banach algebra with $\|1\| = 1$ and $a \in A$. The Neumann series
$\sum_n a^n$ is summable if and only if $\rho(a) < 1$. -/
theorem summable_pow_iff_spectralRadius_lt_one (a : A) :
    Summable (fun n => a ^ n) ↔ spectralRadius ℂ a < 1 := by
  refine ⟨fun h => (spectralRadius_lt_one_iff_tendsto_pow a).mpr h.tendsto_atTop_zero, fun h => ?_⟩
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  obtain ⟨C, _, hC⟩ := exists_norm_pow_le_of_spectralRadius_lt a hr1
  have hrlt : (r : ℝ) < 1 := by exact_mod_cast ENNReal.coe_lt_one_iff.mp hr2
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one r.coe_nonneg hrlt).mul_left C) hC

/-- Let $A$ be a complex Banach algebra with $\|1\| = 1$ and $a \in A$. If $\rho(a) < 1$, then
$1 - a$ is invertible.

The inverse is the sum of the Neumann series
(`hasSum_pow_inverse_one_sub_of_spectralRadius_lt_one`). -/
theorem isUnit_one_sub_of_spectralRadius_lt_one {a : A} (h : spectralRadius ℂ a < 1) :
    IsUnit (1 - a) :=
  have hs : Summable (a ^ ·) := (summable_pow_iff_spectralRadius_lt_one a).mpr h
  ⟨⟨1 - a, ∑' n : ℕ, a ^ n, hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩, rfl⟩

/-- **The Neumann series under the spectral radius hypothesis.** Let $A$ be a complex Banach algebra
with $\|1\| = 1$, and let $a \in A$ satisfy $\rho(a) < 1$. Then
$$\sum_{n=0}^\infty a^n = (1 - a)^{-1}.$$
This is Theorem 1.5, display (1.25), of [quarteroni2000numerical].

Mathlib's `NormedRing.tsum_geometric_of_norm_lt_one` and `geom_series_eq_inverse` assume
$\|a\| < 1$. The inverse is `Ring.inverse`, and the sum is `HasSum`. -/
theorem hasSum_pow_inverse_one_sub_of_spectralRadius_lt_one {a : A}
    (h : spectralRadius ℂ a < 1) : HasSum (fun n => a ^ n) (Ring.inverse (1 - a)) := by
  have hs : Summable (a ^ ·) := (summable_pow_iff_spectralRadius_lt_one a).mpr h
  let u : Aˣ := ⟨1 - a, ∑' n : ℕ, a ^ n, hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩
  have hu : Ring.inverse (1 - a) = ∑' n : ℕ, a ^ n := Ring.inverse_unit u
  rw [hu]
  exact hs.hasSum

/-- **The power rule** in a complex Banach algebra. Let $A$ be a complex Banach algebra with
$\|1\| = 1$. For every $a \in A$ and $n \in \mathbb{N}$,
$$\rho(a^n) = \rho(a)^n.$$
This is stated in [quarteroni2000numerical], §1.7.

It is `spectralRadius_pow_of_nonempty`, since the spectrum is nonempty by `spectrum.nonempty`.
Mathlib has the inequality `spectrum.spectralRadius_pow_le`. -/
theorem spectralRadius_pow (a : A) (n : ℕ) :
    spectralRadius ℂ (a ^ n) = spectralRadius ℂ a ^ n :=
  have : Nontrivial A := NormOneClass.nontrivial
  spectralRadius_pow_of_nonempty (spectrum.nonempty a) n

/-! ### The spectral abscissa -/

section Abscissa

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- The **spectral abscissa** of an element $a$ of a complex algebra $B$,
$$\alpha(a) = \sup\{\operatorname{Re} \lambda : \lambda \in \sigma(a)\},$$
the analogue of the spectral radius for half planes ([golub2013matrix], (9.3.3)).

The supremum is `sSup` in $\mathbb{R}$, so $\alpha(a) = 0$ when the spectrum is empty or the
real parts of its elements are unbounded above. In a nontrivial complex Banach algebra, and for
matrices of positive size, the spectrum is nonempty and compact, and the supremum is attained
(`exists_mem_spectrum_re_eq_spectralAbscissa`). -/
noncomputable def spectralAbscissa (a : B) : ℝ :=
  sSup ((fun z : ℂ => z.re) '' spectrum ℂ a)

/-- If the spectrum of $a$ is bounded, the real parts of its elements are bounded above. -/
theorem bddAbove_re_spectrum {a : B} (hb : Bornology.IsBounded (spectrum ℂ a)) :
    BddAbove ((fun z : ℂ => z.re) '' spectrum ℂ a) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  exact ⟨C, by
    rintro _ ⟨z, hz, rfl⟩
    exact (Complex.re_le_norm z).trans (hC z hz)⟩

/-- Let $a$ be an element of a complex algebra with bounded spectrum. Every $z \in \sigma(a)$
satisfies
$$\operatorname{Re} z \le \alpha(a).$$
-/
theorem re_le_spectralAbscissa {a : B} (hb : Bornology.IsBounded (spectrum ℂ a)) {z : ℂ}
    (hz : z ∈ spectrum ℂ a) : z.re ≤ spectralAbscissa a :=
  le_csSup (bddAbove_re_spectrum hb) ⟨z, hz, rfl⟩

/-- Let $a$ be an element of a complex algebra whose spectrum is nonempty and compact, for example
finite and nonempty. Then some $z \in \sigma(a)$ satisfies $\operatorname{Re} z = \alpha(a)$. -/
theorem exists_mem_spectrum_re_eq_spectralAbscissa {a : B} (hc : IsCompact (spectrum ℂ a))
    (hne : (spectrum ℂ a).Nonempty) : ∃ z ∈ spectrum ℂ a, z.re = spectralAbscissa a := by
  obtain ⟨z, hz, hmax⟩ := hc.exists_isMaxOn hne Complex.continuous_re.continuousOn
  have hg : IsGreatest ((fun w : ℂ => w.re) '' spectrum ℂ a) z.re := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hmax hw
  exact ⟨z, hz, hg.csSup_eq.symm⟩

end Abscissa

/-- Let $A$ be a complex Banach algebra with $\|1\| = 1$. For every $a \in A$, the spectral abscissa
satisfies
$$\alpha(a) \le \|a\|.$$
-/
theorem spectralAbscissa_le_norm (a : A) : spectralAbscissa a ≤ ‖a‖ := by
  have : Nontrivial A := NormOneClass.nontrivial
  refine csSup_le ((spectrum.nonempty a).image _) ?_
  rintro _ ⟨z, hz, rfl⟩
  exact (Complex.re_le_norm z).trans (spectrum.norm_le_norm_of_mem hz)

/-!
### An arbitrary algebra norm bounds the spectral radius

The bound $\rho(a) \le N(a)$ holds for every algebra norm $N$ on a finite-dimensional algebra, not
only for the norm that the algebra carries as a normed algebra. The norm is bundled as an
`AlgebraNorm` and is not an instance. A second `NormedRing` instance on the same type would bring
its own ring structure, unrelated to the one from which the spectrum is computed.

No analysis enters. A finite-dimensional algebra is Artinian, so an element that is not a right zero
divisor is a unit (`IsArtinianRing.isUnit_iff_isRightRegular`). Submultiplicativity of $N$ makes
$\mu \cdot 1 - a$ such an element as soon as $N(a) < |\mu|$.
-/

section AlgebraNorm

variable {𝕜 B : Type*} [NormedField 𝕜] [Ring B] [Algebra 𝕜 B]

/-- **The spectral radius is at most any algebra norm.** Let $\mathbb{K}$ be a normed field, let $B$
be a finite-dimensional $\mathbb{K}$-algebra, and let $N$ be an algebra norm on $B$: a
submultiplicative norm with $N(ca) = |c| N(a)$. Then for every $a \in B$,
$$\rho(a) \le N(a).$$

This is the general form of "$|\lambda| \le \|A\|$ for every consistent matrix norm".
Consistency is the submultiplicativity of $N$, and no relation between $N$ and a norm that $B$
may already carry is needed. Positive definiteness of $N$ is used and cannot be dropped: on
$\mathbb{K} \times \mathbb{K}$ with the componentwise product, $N(x, y) = |x|$ is a
submultiplicative seminorm with $N(ca) = |c| N(a)$ and $N(1) = 1$, but it vanishes at $(0, 1)$,
whose spectrum is $\{0, 1\}$ and whose spectral radius is $1$. On a matrix algebra, a
submultiplicative seminorm with $N(1) = 1$ is automatically a norm, because its kernel is a
two-sided ideal. The function $M \mapsto |\det M|^{1/2}$ on $2 \times 2$ matrices is
submultiplicative and absolutely homogeneous and vanishes on a matrix of rank one with spectral
radius $1$, but it fails the triangle inequality, so it is not a seminorm. -/
theorem spectralRadius_le_algebraNorm [FiniteDimensional 𝕜 B] (N : AlgebraNorm 𝕜 B) (a : B) :
    spectralRadius 𝕜 a ≤ ENNReal.ofReal (N a) := by
  rw [spectralRadius_eq_of_unital]
  refine iSup₂_le fun μ hμ => ?_
  have hle : ‖μ‖ ≤ N a := by
    by_contra hcon
    have hpos : ∀ y : B, y ≠ 0 → 0 < N y := fun y hy =>
      lt_of_le_of_ne (apply_nonneg N y) fun h => hy (eq_zero_of_map_eq_zero N h.symm)
    have hright : ∀ y : B, (‖μ‖ - N a) * N y ≤ N (y * (algebraMap 𝕜 B μ - a)) := by
      intro y
      have hsplit : y * algebraMap 𝕜 B μ = y * (algebraMap 𝕜 B μ - a) + y * a := by noncomm_ring
      have h1 : N (y * algebraMap 𝕜 B μ) ≤ N (y * (algebraMap 𝕜 B μ - a)) + N (y * a) := by
        rw [hsplit]; exact map_add_le_add N _ _
      have h2 : N (y * algebraMap 𝕜 B μ) = ‖μ‖ * N y := by
        rw [← Algebra.commutes, ← Algebra.smul_def]; exact map_smul_eq_mul N _ _
      have h3 : N (y * a) ≤ N y * N a := map_mul_le_mul N _ _
      nlinarith
    have : IsArtinianRing B := IsArtinianRing.of_finite 𝕜 B
    refine spectrum.mem_iff.mp hμ (IsArtinianRing.isUnit_iff_isRightRegular.mpr
      (isRightRegular_iff_left_eq_zero_of_mul.mpr fun y h0 => ?_))
    by_contra hy
    have h := hright y
    rw [h0, map_zero] at h
    nlinarith [hpos y hy]
  calc (‖μ‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖μ‖ := (ofReal_norm μ).symm
    _ ≤ ENNReal.ofReal (N a) := ENNReal.ofReal_le_ofReal hle

/-- Let $B$ be a finite-dimensional algebra over a normed field, and let $N$ be an algebra norm on
$B$. If $N(a) < 1$, then $1 - a$ is invertible.

The proof shows $1 \notin \sigma(a)$, because $\rho(a) \le N(a) < 1$. Finite dimension replaces
completeness, and no topology on $B$ enters. -/
theorem isUnit_one_sub_of_algebraNorm_lt_one [FiniteDimensional 𝕜 B] (N : AlgebraNorm 𝕜 B) {a : B}
    (h : N a < 1) : IsUnit (1 - a) := by
  have h1 : (1 : 𝕜) ∈ resolventSet 𝕜 a :=
    spectrum.mem_resolventSet_of_spectralRadius_lt <|
      (spectralRadius_le_algebraNorm N a).trans_lt (by simpa using ENNReal.ofReal_lt_one.mpr h)
  simpa using spectrum.mem_resolventSet_iff.mp h1

namespace AlgebraNorm

/-- Let $B$ be a finite-dimensional algebra over a normed field, let $N$ be an algebra norm on $B$,
and let $a \in B$ satisfy $N(a) < 1$. Then
$$N((1 - a)^{-1}) \le \frac{N(1)}{1 - N(a)}.$$

This form does not assume $N(1) = 1$. It follows from $(1 - a)^{-1} = 1 + a (1 - a)^{-1}$. The
inverse is `Ring.inverse`. -/
theorem norm_inverse_one_sub_le_div_of_lt_one [FiniteDimensional 𝕜 B] (N : AlgebraNorm 𝕜 B) {a : B}
    (h : N a < 1) : N (Ring.inverse (1 - a)) ≤ N 1 / (1 - N a) := by
  have hu := isUnit_one_sub_of_algebraNorm_lt_one N h
  set u := Ring.inverse (1 - a) with hu_def
  have key : u = 1 + a * u := by
    have := Ring.mul_inverse_cancel (1 - a) hu
    rw [← hu_def] at this
    calc u = (1 - a) * u + a * u := by noncomm_ring
      _ = 1 + a * u := by rw [this]
  have hle : N u ≤ 1 * N 1 + N a * N u := by
    calc N u = N (1 + a * u) := by rw [← key]
      _ ≤ N 1 + N (a * u) := map_add_le_add N _ _
      _ ≤ 1 * N 1 + N a * N u := by rw [one_mul]; gcongr; exact map_mul_le_mul N _ _
  rw [le_div_iff₀ (by linarith)]
  nlinarith [apply_nonneg N u]

/-- Let $B$ be an algebra over a normed field, let $N$ be an algebra norm on $B$, and let $1 - a$ be
invertible. Then
$$\frac{N(1)}{N(1) + N(a)} \le N((1 - a)^{-1}).$$

This form does not assume $N(1) = 1$. It follows from $N(1) = N((1 - a)(1 - a)^{-1}) \le (N(1) +
N(a))\, N((1 - a)^{-1})$. -/
theorem div_add_le_norm_inverse_one_sub (N : AlgebraNorm 𝕜 B) {a : B} (hu : IsUnit (1 - a)) :
    N 1 / (N 1 + N a) ≤ N (Ring.inverse (1 - a)) := by
  set u := Ring.inverse (1 - a) with hu_def
  have hmul : (1 - a) * u = 1 := Ring.mul_inverse_cancel (1 - a) hu
  have h1 : N 1 ≤ (N 1 + N a) * N u := by
    calc N 1 = N ((1 - a) * u) := by rw [hmul]
      _ ≤ N (1 - a) * N u := map_mul_le_mul N _ _
      _ ≤ (N 1 + N a) * N u := by gcongr; exact map_sub_le_add N 1 a
  rcases (add_nonneg (apply_nonneg N 1) (apply_nonneg N a)).lt_or_eq with hpos | hzero
  · exact (div_le_iff₀ hpos).mpr (by linarith)
  · rw [← hzero, div_zero]; exact apply_nonneg N u

/-- **The upper bound of [quarteroni2000numerical], (1.26)**, for an arbitrary algebra norm. Let $B$
be a finite-dimensional algebra over a normed field, let $N$ be an algebra norm on $B$ with
$N(1) = 1$, and let $a \in B$ satisfy $N(a) < 1$. Then
$$N((1 - a)^{-1}) \le \frac{1}{1 - N(a)}.$$

The inverse exists by `isUnit_one_sub_of_algebraNorm_lt_one`. For the norm of a normed algebra,
this bound is `NormedRing.norm_inverse_one_sub_le`; here $N$ is unrelated to any topology on
$B$. -/
theorem norm_inverse_one_sub_le_of_lt_one [FiniteDimensional 𝕜 B] (N : AlgebraNorm 𝕜 B)
    (h1 : N 1 = 1) {a : B} (h : N a < 1) : N (Ring.inverse (1 - a)) ≤ 1 / (1 - N a) :=
  h1 ▸ norm_inverse_one_sub_le_div_of_lt_one N h

/-- **The lower bound of [quarteroni2000numerical], (1.26)**, for an arbitrary algebra norm. Let $B$
be a finite-dimensional algebra over a normed field, let $N$ be an algebra norm on $B$ with
$N(1) = 1$, and let $a \in B$ satisfy $N(a) < 1$. Then
$$\frac{1}{1 + N(a)} \le N((1 - a)^{-1}).$$
-/
theorem one_div_one_add_le_norm_inverse_one_sub [FiniteDimensional 𝕜 B] (N : AlgebraNorm 𝕜 B)
    (h1 : N 1 = 1) {a : B} (h : N a < 1) : 1 / (1 + N a) ≤ N (Ring.inverse (1 - a)) :=
  h1 ▸ div_add_le_norm_inverse_one_sub N (isUnit_one_sub_of_algebraNorm_lt_one N h)

end AlgebraNorm

end AlgebraNorm

omit [NormOneClass A] in
/-- Let $A$ be a finite-dimensional complex Banach algebra, and let $N$ be an algebra norm on $A$.
If $N(a) < 1$, then $a^n \to 0$ in the topology of $A$. This is the convergence criterion for an
arbitrary consistent matrix norm.

The norm $N$ is related to the algebra only by its submultiplicativity. -/
theorem tendsto_pow_of_algebraNorm_lt_one [FiniteDimensional ℂ A] (N : AlgebraNorm ℂ A) {a : A}
    (h : N a < 1) : Tendsto (fun n => a ^ n) atTop (𝓝 0) :=
  tendsto_pow_of_spectralRadius_lt_one
    ((spectralRadius_le_algebraNorm N a).trans_lt (ENNReal.ofReal_lt_one.mpr h))
