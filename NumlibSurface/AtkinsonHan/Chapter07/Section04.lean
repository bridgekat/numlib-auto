/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Distribution.Sobolev
import Numlib.Analysis.Sobolev.FourierCharacterization
import NumlibSurface.AtkinsonHan.Chapter07.Section03

/-!
# Atkinson and Han, Section 7.4: The Fourier characterization of Sobolev spaces

This module formalizes Section 7.4 of [han2009theoretical], which describes the Sobolev spaces
$H^k(\mathbb{R}^d) = W^{k,2}(\mathbb{R}^d)$ by the Fourier transform. All functions in the section
may be complex-valued. Theorem 7.4.1 states that $v \in L^2(\mathbb{R}^d)$ lies in
$H^k(\mathbb{R}^d)$ if and only if $(1 + |\xi|^2)^{k/2} \mathcal{F}v \in L^2(\mathbb{R}^d)$, and
(7.4.1) states that the $L^2$ norm of this function is equivalent to the Sobolev norm
$(\sum_{|\alpha| \le k} \|\partial^\alpha v\|_{L^2}^2)^{1/2}$ of Definition 7.2.2. The display
(7.4.2) uses the Fourier condition to define $H^s(\mathbb{R}^d)$ for real $s$. Example 7.4.2 is the
embedding $H^k(\Omega) \hookrightarrow C(\bar\Omega)$ for $k > d/2$ with the bound (7.4.3), and
Example 7.4.3 is the interpolation inequality (7.4.4), $\|v\|_{C(\bar\Omega)} \le c
\|v\|_{H^d(\Omega)}^{1/2} \|v\|_{L^2(\Omega)}^{1/2}$.

The whole-space results specialize `Numlib.Analysis.Sobolev.FourierCharacterization` and
`Numlib.Analysis.Sobolev.Tempered`, which work for any orthonormal basis of a finite-dimensional
real inner product space and identify the space of Definition 7.2.2 on the whole space with
Mathlib's Bessel potential space `TemperedDistribution.MemSobolev`. The results on a domain use the
Sobolev embeddings and the extension operators of Section 7.3, in
`NumlibSurface.AtkinsonHan.Chapter07.Section03`.

## Main results

* Theorem 7.4.1, `AtkinsonHan.Chapter07.theorem_7_4_1_complex` and
  `AtkinsonHan.Chapter07.theorem_7_4_1`: a complex-valued, or a real-valued,
  $v \in L^2(\mathbb{R}^d)$ lies in $H^k(\mathbb{R}^d)$ if and only if $(1 + |\xi|^2)^{k/2}
  \mathcal{F}v \in L^2(\mathbb{R}^d)$.
* Equation (7.4.1), `AtkinsonHan.Chapter07.equation_7_4_1_complex` and
  `AtkinsonHan.Chapter07.equation_7_4_1`: there are $c_1, c_2 > 0$ with $c_1 \|v\|_{H^k} \le \|(1 +
  |\xi|^2)^{k/2} \mathcal{F}v\|_{L^2} \le c_2 \|v\|_{H^k}$ on $H^k(\mathbb{R}^d)$.
* Equation (7.4.2), `AtkinsonHan.Chapter07.equation_7_4_2`: for $s \ge 0$, a function
  $v \in L^2(\mathbb{R}^d)$ lies in the Bessel potential space $H^s(\mathbb{R}^d)$ if and only if
  $(1 + |\xi|^2)^{s/2} \mathcal{F}v \in L^2(\mathbb{R}^d)$.
* Equation (7.4.2), `AtkinsonHan.Chapter07.equation_7_4_2_norm`: for $s \ge 0$, the $L^2$ norm of
  the Bessel potential of order $s$ of $v$ equals $\|(1 + |\xi|^2)^{s/2} \mathcal{F}v\|_{L^2}$.
* Example 7.4.2, `AtkinsonHan.Chapter07.example_7_4_2`: on a bounded extension domain
  $\Omega \subseteq \mathbb{R}^{d+1}$ with $k > (d+1)/2$, the map from $v$ to its continuous
  representative is a bounded injective linear map $H^k(\Omega) \to C(\bar\Omega)$, which gives
  (7.4.3).
* Example 7.4.3, `AtkinsonHan.Chapter07.example_7_4_3_whole_space_complex` and
  `AtkinsonHan.Chapter07.example_7_4_3_whole_space`: the inequality (7.4.4) on
  $\Omega = \mathbb{R}^d$ for $d \ge 1$, for complex-valued and for real-valued functions.
* Example 7.4.3, `AtkinsonHan.Chapter07.example_7_4_3`: the inequality (7.4.4) on a bounded
  $C^{d+1}$ domain $\Omega \subseteq \mathbb{R}^{d+1}$.
* Exercise 7.4.2, `AtkinsonHan.Chapter07.exercise_7_4_2`: there are $c_1, c_2 > 0$ with $c_1
  (\sum_{|\alpha| \le k} |\xi^\alpha|^2)^{1/2} \le (1 + |\xi|^2)^{k/2} \le c_2 (\sum_{|\alpha| \le
  k} |\xi^\alpha|^2)^{1/2}$ for all $\xi \in \mathbb{R}^d$.

## Proof outline

The membership criterion of Theorem 7.4.1 comes from Mathlib's
`TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded`, a statement about bounded symbols
that carries no constants, so the norm equivalence (7.4.1) needs a separate proof. The Fourier
transform of a weak derivative on the whole space is $\mathcal{F}(\partial^\alpha v) = (2\pi i
\xi)^\alpha \mathcal{F}v$ (`fourier_weakDeriv_aeEq`). Plancherel's theorem then turns
$\sum_{|\alpha| \le k} \|\partial^\alpha v\|_{L^2}^2$ into $\int (\sum_{|\alpha| \le k}
(2\pi)^{2|\alpha|} |\xi^\alpha|^2) |\mathcal{F}v|^2 \, d\xi$, and the symbol inequality of Exercise
7.4.2 compares this integral with $\int (1 + |\xi|^2)^k |\mathcal{F}v|^2 \, d\xi$.

For (7.4.4) on $\mathbb{R}^d$, the continuous representative of $v \in H^d(\mathbb{R}^d)$ is the
inverse Fourier integral of $\mathcal{F}v \in L^1$, so $|v(x)| \le \int |\mathcal{F}v|$. The
Cauchy–Schwarz inequality against the weight $(1 + \lambda |\xi|^2)^{\pm d/2}$, with (7.4.1) on the
Fourier side, and the choice $\lambda = (\|v\|_{L^2} / \|v\|_{H^d})^{2/d}$ give the bound. On a
domain, the bound is applied to an extension of $v$ that is bounded both in $H^{d+1}$ and in $L^2$.

## Notation

* $\xi^\alpha = \prod_i \xi_i^{\alpha_i}$, the monomial of a multi-index $\alpha$:
  `AtkinsonHan.Chapter07.xiPow`.
* $\mathcal{F}v$: Mathlib's Fourier transform `𝓕 v` on $L^2(\mathbb{R}^d)$, with the kernel
  $e^{-2\pi i x \cdot \xi}$. For this normalization the Bessel potential of order $s$ is
  $(1 - (2\pi)^{-2} \Delta)^{s/2}$.

## Conventions

* For a real-valued $v$, $\mathcal{F}v$ is the Fourier transform of the complexification
  `Complex.ofRealCLM.compLp v`. The declarations with the suffix `_complex` state the results for
  the complex-valued functions that the section allows.
* $H^k(\Omega)$ is the space $W^{k,2}(\Omega)$ of Definition 7.2.2 in the multi-index reading,
  `SobolevMultiIndex ℝ (AtkinsonHan.Chapter07.stdBasis d) k 2 Ω volume` or
  `AtkinsonHan.Chapter07.definition_7_2_2_multiIndex`, with the derivatives $\partial^\alpha$ taken
  in the standard basis.
* In Examples 7.4.2 and 7.4.3 on a domain, the ambient space is $\mathbb{R}^{d+1}$, as in Definition
  7.2.1, so the dimension $d$ of the source is $d + 1$ here.

## Implementation notes

* $H^s(\mathbb{R}^d)$ for real $s$ is Mathlib's Bessel potential space
  `TemperedDistribution.MemSobolev s 2`: the tempered distributions whose Bessel potential of order
  $s$ is an $L^2$ function. At $s = 0$ it is $L^2(\mathbb{R}^d)$.
* In (7.4.1) and in Example 7.4.3 on $\mathbb{R}^d$, an element of $H^k(\mathbb{R}^d)$ is given as
  $v \in L^2(\mathbb{R}^d)$ together with a family $(w_\alpha)_{|\alpha| \le k}$ in
  $L^2(\mathbb{R}^d)$ such that each $w_\alpha$ is the weak derivative $\partial^\alpha v$. The
  $H^k$ norm is then $(\sum_\alpha \|w_\alpha\|_{L^2}^2)^{1/2}$.
* Example 7.4.2 is not proved by the route of the source. The source proves it by the Fourier
  transform on $\mathbb{R}^d$, the density of Theorem 7.3.4 and the extension operator of Theorem
  7.3.5 at order $k$. Here it is the Sobolev embedding of Theorem 7.3.8 (c): $W^{k,2}(\Omega)
  \hookrightarrow W^{1,r}(\Omega)$ for some $r > d + 1$, followed by Morrey's theorem through the
  extension operator of order one. This route needs the extension operator at order one only.

## Deviations from the source

* **Example 7.4.2** (reading). The source assumes a Lipschitz domain. The statement assumes a
  bounded open set that is a $W^{1,q}$ extension domain for every $q$; the bounded $C^1$ domains of
  Definition 7.2.1 are such sets. See `AtkinsonHan.Chapter07.example_7_4_2`.
* **Example 7.4.3** (reading). The source assumes a Lipschitz domain and uses the universal
  extension operator of Stein. The statement assumes a bounded $C^{d+1}$ domain and uses the
  extension operator of order $d + 1$ with its $L^2$ bound. See
  `AtkinsonHan.Chapter07.example_7_4_3`.

## Not formalized

* **Equation (7.4.2) for $s < 0$.** The proof reads the symbol off the $L^2$ representative by
  multiplication with $(1 + |\xi|^2)^{-s/2}$, which is bounded only when $s \ge 0$.
* **Exercise 7.4.3.**
* **Exercise 7.4.4.**
-/

open FourierTransform LineDeriv MeasureTheory TemperedDistribution TopologicalSpace

open scoped ENNReal NNReal SchwartzMap

namespace AtkinsonHan.Chapter07

/-! ### The Fourier definition (7.4.2) of $H^s(\mathbb{R}^d)$ -/

variable {d : ℕ}

/-- **Equation (7.4.2)** of [han2009theoretical]. Let $s \ge 0$ be real and let
$v \in L^2(\mathbb{R}^d)$ be complex-valued. Then $v$, as a tempered distribution, lies in the
Bessel potential space $H^s(\mathbb{R}^d)$ if and only if
$$(1 + |\xi|^2)^{s/2} \mathcal{F}v \in L^2(\mathbb{R}^d).$$

The source uses this condition to define $H^s(\mathbb{R}^d)$. Here $H^s(\mathbb{R}^d)$ is
`TemperedDistribution.MemSobolev s 2`, the tempered distributions whose Bessel potential of
order $s$ is an $L^2$ function; at $s = 0$ this is $L^2(\mathbb{R}^d)$ by
`TemperedDistribution.memSobolev_zero_iff`. This is not Theorem 7.4.1, whose left side is the
space $W^{k,2}(\mathbb{R}^d)$ of weak derivatives; `AtkinsonHan.Chapter07.theorem_7_4_1`
composes this result with the identification of the two spaces. The proof is
`TemperedDistribution.memSobolev_two_iff_memLp_symbol_mul_fourier`. -/
theorem equation_7_4_2 {s : ℝ} (hs : 0 ≤ s)
    (v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    MemSobolev s 2 (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) ↔
      MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume :=
  memSobolev_two_iff_memLp_symbol_mul_fourier hs v

/-- **Equation (7.4.2)** of [han2009theoretical], the norm. Let $s \ge 0$ be real and let
$v, w \in L^2(\mathbb{R}^d)$ be complex-valued. If the Bessel potential of order $s$ of $v$ is
the tempered distribution of $w$, then
$$\|w\|_{L^2(\mathbb{R}^d)} = \|(1 + |\xi|^2)^{s/2} \mathcal{F}v\|_{L^2(\mathbb{R}^d)}.$$

The number $\|w\|_{L^2}$ is the norm of $v$ in the Bessel potential space $H^s(\mathbb{R}^d)$,
so the norm of $H^s(\mathbb{R}^d)$ equals the Fourier norm and is not only equivalent to it. The
proof is Plancherel's theorem,
`TemperedDistribution.norm_eq_eLpNorm_symbol_mul_fourier_of_besselPotential_eq`. This is not
(7.4.1), which compares the Fourier norm with the Sobolev norm of Definition 7.2.2; see
`AtkinsonHan.Chapter07.equation_7_4_1`. -/
theorem equation_7_4_2_norm {s : ℝ} (hs : 0 ≤ s)
    {v w : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))}
    (hw : besselPotential (EuclideanSpace ℝ (Fin d)) ℂ s (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (w : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) :
    ‖w‖ =
      (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume).toReal :=
  norm_eq_eLpNorm_symbol_mul_fourier_of_besselPotential_eq hs hw

/-! ### Theorem 7.4.1 -/

/-- **Theorem 7.4.1** of [han2009theoretical], for complex-valued functions. Let $k \ge 0$ be an
integer and let $v \in L^2(\mathbb{R}^d)$ be complex-valued. Then $v \in H^k(\mathbb{R}^d)$,
that is, $v$ has a weak derivative $\partial^\alpha v \in L^2(\mathbb{R}^d)$ for each
multi-index $\alpha$ with $|\alpha| \le k$, if and only if
$$(1 + |\xi|^2)^{k/2} \mathcal{F}v \in L^2(\mathbb{R}^d).$$

The section of the source allows complex-valued functions throughout. The left side is
`MemSobolevMultiIndex (AtkinsonHan.Chapter07.stdBasis d) v k 2 ⊤ volume`, which is
`AtkinsonHan.Chapter07.definition_7_2_2_multiIndex` read for complex-valued functions. The proof
composes `AtkinsonHan.Chapter07.equation_7_4_2` with the identification of the Bessel potential
space with $W^{k,2}(\mathbb{R}^d)$ in `Numlib.Analysis.Sobolev.Tempered`. -/
theorem theorem_7_4_1_complex {k : ℕ} (v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    MemSobolevMultiIndex (stdBasis d) (v : EuclideanSpace ℝ (Fin d) → ℂ) k 2 ⊤ volume ↔
      MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume := by
  rw [← equation_7_4_2 (by positivity) v]
  exact (TemperedDistribution.memSobolev_iff_memSobolevMultiIndex
    (EuclideanSpace.basisFun (Fin d) ℝ)).symm

/-- **Theorem 7.4.1** of [han2009theoretical]. Let $k \ge 0$ be an integer and let
$v \in L^2(\mathbb{R}^d)$ be real-valued. Then $v \in H^k(\mathbb{R}^d)$, the space
$W^{k,2}(\mathbb{R}^d)$ of Definition 7.2.2, if and only if
$$(1 + |\xi|^2)^{k/2} \mathcal{F}v \in L^2(\mathbb{R}^d).$$

The Fourier transform $\mathcal{F}v$ is the Fourier transform of the complexification
`Complex.ofRealCLM.compLp v` of $v$. `AtkinsonHan.Chapter07.theorem_7_4_1_complex` is the
statement for complex-valued functions, and the norm equivalence (7.4.1) is
`AtkinsonHan.Chapter07.equation_7_4_1`. -/
theorem theorem_7_4_1 {k : ℕ} (v : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    definition_7_2_2_multiIndex k 2 ⊤ (v : EuclideanSpace ℝ (Fin d) → ℝ) ↔
      MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)
        * (𝓕 (Complex.ofRealCLM.compLp v)) ξ) 2 volume := by
  rw [← theorem_7_4_1_complex (Complex.ofRealCLM.compLp v)]
  have hae : ((Complex.ofRealCLM.compLp v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
      : EuclideanSpace ℝ (Fin d) → ℂ)
        =ᵐ[volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set _)]
      fun x ↦ (((v : EuclideanSpace ℝ (Fin d) → ℝ) x : ℝ) : ℂ) := by
    rw [show ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)))
      = Set.univ from rfl, Measure.restrict_univ]
    filter_upwards [Complex.ofRealCLM.coeFn_compLp v] with x hx using hx
  exact ⟨fun h ↦ (memSobolevMultiIndex_ofReal_iff.2 h).congr_ae hae.symm,
    fun h ↦ memSobolevMultiIndex_ofReal_iff.1 (h.congr_ae hae)⟩

/-! ### The norm equivalence (7.4.1) -/

section NormEquivalence

variable {d k : ℕ}

/-- The monomial $\xi^\alpha = \prod_i \xi_i^{\alpha_i}$ of a multi-index $\alpha$, for
$\xi \in \mathbb{R}^d$. -/
def xiPow (α : Fin d → ℕ) (ξ : EuclideanSpace ℝ (Fin d)) : ℝ := ∏ i, ξ i ^ α i

/-- The monomial $\xi^\alpha$ is the backbone monomial `OrthonormalBasis.coordMonomial` of the
standard basis of $\mathbb{R}^d$. -/
theorem xiPow_eq_coordMonomial (α : Fin d → ℕ) (ξ : EuclideanSpace ℝ (Fin d)) :
    xiPow α ξ = (EuclideanSpace.basisFun (Fin d) ℝ).coordMonomial α ξ := by
  simp [xiPow, OrthonormalBasis.coordMonomial, EuclideanSpace.inner_single_right]

/-- **Exercise 7.4.2** of [han2009theoretical]. Let $d, k \ge 0$ be integers. There are constants
$c_1, c_2 > 0$ such that for every $\xi \in \mathbb{R}^d$,
$$c_1 \Big(\sum_{|\alpha| \le k} |\xi^\alpha|^2\Big)^{1/2} \le (1 + |\xi|^2)^{k/2} \le c_2
  \Big(\sum_{|\alpha| \le k} |\xi^\alpha|^2\Big)^{1/2}.$$

This symbol inequality turns Plancherel's theorem into the norm equivalence (7.4.1). The
monomial $\xi^\alpha$ is `AtkinsonHan.Chapter07.xiPow`, and the sum runs over
`MultiIndexLE (Fin d) k`. The proof is `OrthonormalBasis.exists_bounds_rpow_one_add_norm_sq` for
the standard basis, with $c_1 = N^{-1/2}$, where $N$ is the number of multi-indices $\alpha$
with $|\alpha| \le k$, and $c_2 = (1 + d)^{k/2}$. The lower bound needs no multinomial
expansion, only a coordinate of largest absolute value. -/
theorem exercise_7_4_2 (d k : ℕ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ ξ : EuclideanSpace ℝ (Fin d),
        c₁ * Real.sqrt (∑ α : MultiIndexLE (Fin d) k, |xiPow α.1 ξ| ^ 2)
            ≤ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2)
          ∧ (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2)
            ≤ c₂ * Real.sqrt (∑ α : MultiIndexLE (Fin d) k, |xiPow α.1 ξ| ^ 2) := by
  have hS : ∀ ξ : EuclideanSpace ℝ (Fin d),
      (∑ α : MultiIndexLE (Fin d) k, |xiPow α.1 ξ| ^ 2)
        = (EuclideanSpace.basisFun (Fin d) ℝ).sumSqCoordMonomial k ξ := fun ξ ↦
    Finset.sum_congr rfl fun α _ ↦ by rw [sq_abs, xiPow_eq_coordMonomial]
  simpa only [hS] using
    (EuclideanSpace.basisFun (Fin d) ℝ).exists_bounds_rpow_one_add_norm_sq k

/-- **Equation (7.4.1)** of [han2009theoretical], for complex-valued functions. Let $d, k \ge 0$ be
integers. There are constants $c_1, c_2 > 0$ with the following property. Let
$v \in L^2(\mathbb{R}^d)$ be complex-valued, and for each multi-index $\alpha$ with
$|\alpha| \le k$ let $w_\alpha \in L^2(\mathbb{R}^d)$ be the weak derivative $\partial^\alpha v$
on $\mathbb{R}^d$. Then
$$c_1 \Big(\sum_{|\alpha| \le k} \|w_\alpha\|_{L^2}^2\Big)^{1/2} \le \|(1 + |\xi|^2)^{k/2}
  \mathcal{F}v\|_{L^2(\mathbb{R}^d)} \le c_2 \Big(\sum_{|\alpha| \le k}
  \|w_\alpha\|_{L^2}^2\Big)^{1/2}.$$

The sum $(\sum_\alpha \|\partial^\alpha v\|_{L^2}^2)^{1/2}$ is the norm
$\|v\|_{H^k(\mathbb{R}^d)}$ of Definition 7.2.2, which is the norm of `SobolevMultiIndex ℂ
(AtkinsonHan.Chapter07.stdBasis d) k 2 ⊤ volume` by `SobolevMultiIndex.norm_eq_sum`. The
hypothesis on $w$ is `HasWeakIteratedLineDerivOn` for the tuple of directions of $\alpha$; since
$v$ and each $w_\alpha$ lie in $L^2(\mathbb{R}^d)$, it says that $v \in H^k(\mathbb{R}^d)$. The
proof applies Plancherel's theorem to each $\partial^\alpha v$, whose Fourier transform is
$(2\pi i \xi)^\alpha \mathcal{F}v$, and then Exercise 7.4.2; it is
`OrthonormalBasis.exists_norm_equiv_eLpNorm_symbol_mul_fourier` for the standard basis. The
constants are $c_1 = ((2\pi)^{2k} N)^{-1/2}$, where $N$ is the number of multi-indices $\alpha$
with $|\alpha| \le k$, and $c_2 = (1 + d)^{k/2}$. -/
theorem equation_7_4_1_complex (d k : ℕ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
        (w : MultiIndexLE (Fin d) k → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))),
        (∀ α : MultiIndexLE (Fin d) k, HasWeakIteratedLineDerivOn
            (multiIndexTuple (stdBasis d) α.1) (v : EuclideanSpace ℝ (Fin d) → ℂ)
            (w α : EuclideanSpace ℝ (Fin d) → ℂ) ⊤ volume) →
        c₁ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)
            ≤ (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
                volume).toReal
          ∧ (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2
                volume).toReal ≤ c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).exists_norm_equiv_eLpNorm_symbol_mul_fourier k

/-- **Equation (7.4.1)** of [han2009theoretical]. Let $d, k \ge 0$ be integers. There are constants
$c_1, c_2 > 0$ with the following property. Let $v \in L^2(\mathbb{R}^d)$ be real-valued, and
for each multi-index $\alpha$ with $|\alpha| \le k$ let $w_\alpha \in L^2(\mathbb{R}^d)$ be the
weak derivative $\partial^\alpha v$ on $\mathbb{R}^d$ in the sense of Definition 7.1.3. Then
$$c_1 \|v\|_{H^k(\mathbb{R}^d)} \le \|(1 + |\xi|^2)^{k/2} \mathcal{F}v\|_{L^2(\mathbb{R}^d)} \le
  c_2 \|v\|_{H^k(\mathbb{R}^d)},$$
where $\|v\|_{H^k(\mathbb{R}^d)} = (\sum_{|\alpha| \le k} \|w_\alpha\|_{L^2}^2)^{1/2}$. So
$\|(1 + |\xi|^2)^{k/2} \mathcal{F}v\|_{L^2}$ is a norm on $H^k(\mathbb{R}^d)$ that is equivalent
to the norm of Definition 7.2.2.

The norm $\|v\|_{H^k}$ is the norm of `SobolevMultiIndex ℝ (AtkinsonHan.Chapter07.stdBasis d) k
2 ⊤ volume` by `AtkinsonHan.Chapter07.definition_7_2_2_multiIndex_norm`. The hypothesis on $w$
is `AtkinsonHan.Chapter07.definition_7_1_3_multiIndex`; since $v$ and each $w_\alpha$ lie in
$L^2(\mathbb{R}^d)$, it says that $v \in H^k(\mathbb{R}^d)$. As in
`AtkinsonHan.Chapter07.theorem_7_4_1`, $\mathcal{F}v$ is the Fourier transform of the
complexification of $v$. `AtkinsonHan.Chapter07.equation_7_4_1_complex` is the statement for
complex-valued functions. -/
theorem equation_7_4_1 (d k : ℕ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (v : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
        (w : MultiIndexLE (Fin d) k → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))),
        (∀ α : MultiIndexLE (Fin d) k, definition_7_1_3_multiIndex α.1
            (v : EuclideanSpace ℝ (Fin d) → ℝ) (w α : EuclideanSpace ℝ (Fin d) → ℝ) ⊤) →
        c₁ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)
            ≤ (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)
                * (𝓕 (Complex.ofRealCLM.compLp v)) ξ) 2 volume).toReal
          ∧ (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) : ℝ) : ℂ)
                * (𝓕 (Complex.ofRealCLM.compLp v)) ξ) 2 volume).toReal
            ≤ c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, h⟩ := equation_7_4_1_complex d k
  refine ⟨c₁, c₂, hc₁, hc₂, fun v w hw ↦ ?_⟩
  have hres : ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)))
      = Set.univ := rfl
  have hcoe : ∀ f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
      (fun x ↦ (((f : EuclideanSpace ℝ (Fin d) → ℝ) x : ℝ) : ℂ))
        =ᵐ[volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set _)]
        ((Complex.ofRealCLM.compLp f : Lp ℂ 2 _) : EuclideanSpace ℝ (Fin d) → ℂ) := by
    intro f
    rw [hres, Measure.restrict_univ]
    filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with x hx using hx.symm
  have key := h (Complex.ofRealCLM.compLp v) (fun α ↦ Complex.ofRealCLM.compLp (w α)) fun α ↦
    (HasWeakIteratedLineDerivOn.ofReal_iff.1 (hw α)).congr_ae (hcoe v) (hcoe (w α))
  simpa only [Lp.norm_ofRealCLM_compLp] using key

end NormEquivalence

/-! ### Example 7.4.2: $H^k(\Omega) \hookrightarrow C(\bar\Omega)$ for $k > d/2$ -/

section Embedding

variable {d : ℕ}

/-- **Example 7.4.2** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded
open set that is a $W^{1,q}$ extension domain for every $q \in [1, \infty]$, and let $k$ be an
integer with $k > (d+1)/2$. Then there is a bounded linear map
$\iota : H^k(\Omega) \to C(\bar\Omega)$ with these properties:

* for every $v \in H^k(\Omega)$ there is a continuous function $v'$ on $\mathbb{R}^{d+1}$ that
  equals $v$ almost everywhere on $\Omega$, and $\iota v = v'$ on $\bar\Omega$;
* $\iota$ is a continuous embedding in the sense of Definition 7.3.6, so
  $H^k(\Omega) \hookrightarrow C(\bar\Omega)$;
* there is a constant $c$ with $\|\iota v\|_{C(\bar\Omega)} \le c \|v\|_{H^k(\Omega)}$ for all
  $v \in H^k(\Omega)$, which is (7.4.3).

**Reading.** The source assumes a Lipschitz domain. The extension-domain hypothesis
`IsSobolevExtensionDomainAll` replaces it; the bounded $C^1$ domains of Definition 7.2.1 satisfy
it by `AtkinsonHan.Chapter07.isSobolevExtensionDomainAll_of_definition_7_2_1`.

$H^k(\Omega)$ is the space $W^{k,2}(\Omega)$ of Definition 7.2.2. The source proves the result
by the Fourier transform on $\mathbb{R}^d$ (Step 1, the Cauchy–Schwarz inequality against
$\int (1 + |\xi|^2)^{-k} \, d\xi < \infty$), the density of Theorem 7.3.4 (Step 2) and the
extension operator of Theorem 7.3.5 at order $k$ (Step 3). The proof here is the Sobolev
embedding `AtkinsonHan.Chapter07.theorem_7_3_8_c` instead: $W^{k,2}(\Omega) \hookrightarrow
W^{1,r}(\Omega)$ for some $r > d + 1$, followed by Morrey's theorem through the extension
operator of order one (`SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order`).
The extension operator at order $k$ is `AtkinsonHan.Chapter07.theorem_7_3_5_order`; the
universal extension operator of Stein is not formalized. -/
theorem example_7_4_2 {k : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsSobolevExtensionDomainAll (d + 1) Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hk : ((d + 1 : ℕ) : ℝ) / 2 < k) :
    haveI : CompactSpace (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
      isCompact_iff_compactSpace.1 hb.isCompact_closure
    ∃ ι : SobolevMultiIndex ℝ (stdBasis (d + 1)) k 2 Ω volume →L[ℝ]
        C(closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ℝ),
      (∀ v, ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous v' ∧
        SobolevMultiIndex.fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' ∧
        ∀ x, ι v x = v' x) ∧
      definition_7_3_6 ι.toLinearMap ∧ ∃ c : ℝ, ∀ v, ‖ι v‖ ≤ c * ‖v‖ := by
  have : CompactSpace (closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    isCompact_iff_compactSpace.1 hb.isCompact_closure
  have hk1 : 1 ≤ k := by
    have h1 : (0 : ℝ) < (d + 1 : ℕ) / 2 := by positivity
    exact_mod_cast h1.trans hk
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hk' : ((d + 1 : ℕ) : ℝ) / ((2 : ℝ≥0) : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    rw [NNReal.coe_ofNat]
    exact hk
  have : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  have h := SobolevEuclidean.exists_isCompactEmbedding_toContinuousMap_of_order (p := 2) k hΩ
    (Or.inr (by norm_num)) hk' (K := closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    subset_closure
  obtain ⟨ι, hι, hc⟩ := h
  exact ⟨ι, hι, hc.toIsContinuousEmbedding, ‖ι‖, ι.le_opNorm⟩

end Embedding

/-! ### Example 7.4.3 on the whole space: the interpolation inequality (7.4.4) -/

section Interpolation

variable {d : ℕ}

/-- **Example 7.4.3** of [han2009theoretical], on the whole space, for complex-valued functions. Let
$d \ge 1$. There is a constant $c \ge 0$ with the following property. Let
$v \in L^2(\mathbb{R}^d)$ be complex-valued, and for each multi-index $\alpha$ with
$|\alpha| \le d$ let $w_\alpha \in L^2(\mathbb{R}^d)$ be the weak derivative $\partial^\alpha v$
on $\mathbb{R}^d$, so that $v \in H^d(\mathbb{R}^d)$. Then $v$ has a continuous representative
$v'$ with
$$|v'(x)| \le c \, \|v\|_{H^d(\mathbb{R}^d)}^{1/2} \|v\|_{L^2(\mathbb{R}^d)}^{1/2} \quad
  \text{for all } x \in \mathbb{R}^d,$$
where $\|v\|_{H^d(\mathbb{R}^d)} = (\sum_{|\alpha| \le d} \|w_\alpha\|_{L^2}^2)^{1/2}$ is the
norm of Definition 7.2.2. This is (7.4.4) for $\Omega = \mathbb{R}^d$.

The proof follows the source. The continuous representative satisfies
$|v'(x)| \le \int |\mathcal{F}v|$ (`exists_continuous_ae_eq_of_integrable_fourier`, with
$\mathcal{F}v \in L^1$ by `TemperedDistribution.MemSobolev.fourier_memL1`). Then the
Cauchy–Schwarz inequality against the weight $(1 + \lambda |\xi|^2)^{\pm d/2}$
(`sq_toReal_lintegral_enorm_fourier_le`), with (7.4.1) on the Fourier side, and the choice
$\lambda = (\|v\|_{L^2} / \|v\|_{H^d})^{2/d}$ (`exists_rpow_neg_half_mul_add_eq`) give the
bound. The form on a domain is `AtkinsonHan.Chapter07.example_7_4_3`. -/
theorem example_7_4_3_whole_space_complex (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (w : MultiIndexLE (Fin d) d → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))),
      (∀ α : MultiIndexLE (Fin d) d, HasWeakIteratedLineDerivOn
          (multiIndexTuple (stdBasis d) α.1) (v : EuclideanSpace ℝ (Fin d) → ℂ)
          (w α : EuclideanSpace ℝ (Fin d) → ℂ) ⊤ volume) →
      ∃ v' : EuclideanSpace ℝ (Fin d) → ℂ, Continuous v' ∧
        (v : EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[volume] v' ∧
        ∀ x, ‖v' x‖ ≤ c * ((∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2)
          * ‖v‖ ^ ((1 : ℝ) / 2) := by
  obtain ⟨c₁, c₂, -, hc₂, hEq⟩ := equation_7_4_1_complex d d
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = (∫⁻ ξ : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ)))).toReal := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := hI ▸ ENNReal.toReal_nonneg
  refine ⟨Real.sqrt (2 ^ (d + 1) * I * c₂), Real.sqrt_nonneg _, fun v w hw ↦ ?_⟩
  -- membership in `H^d` and integrability of the Fourier transform
  have hres : ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)))
      = Set.univ := rfl
  have hv : MemSobolevMultiIndex (stdBasis d) (v : EuclideanSpace ℝ (Fin d) → ℂ) d 2 ⊤ volume := by
    refine ⟨?_, fun α hα ↦ ⟨(w ⟨α, hα⟩ : EuclideanSpace ℝ (Fin d) → ℂ), hw ⟨α, hα⟩, ?_⟩⟩
    · rw [hres, Measure.restrict_univ]; exact Lp.memLp v
    · rw [hres, Measure.restrict_univ]; exact Lp.memLp (w ⟨α, hα⟩)
  have hF : MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((d : ℝ) / 2) : ℝ) : ℂ) * (𝓕 v) ξ) 2 volume :=
    (theorem_7_4_1_complex v).1 hv
  have hMS : MemSobolev (d : ℝ) 2 (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) :=
    (equation_7_4_2 (by positivity) v).2 hF
  obtain ⟨g, hg⟩ := hMS.fourier_memL1 (by
    rw [finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : d < 2 * d))
  rw [Lp.fourier_toTemperedDistribution_eq] at hg
  have hgae := ae_eq_of_toTemperedDistribution_eq _ g hg
  have hFint : Integrable ((𝓕 v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
      : EuclideanSpace ℝ (Fin d) → ℂ) := (L1.integrable_coeFn g).congr hgae.symm
  -- the continuous representative
  obtain ⟨v', hv'c, hv'ae, hv'b⟩ := exists_continuous_ae_eq_of_integrable_fourier v hFint
  refine ⟨v', hv'c, hv'ae, fun x ↦ ?_⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℝ, J = (∫⁻ ξ, ‖(𝓕 v : Lp ℂ 2 (volume : Measure _)) ξ‖ₑ).toReal := ⟨_, rfl⟩
  have hJreal : ∫ ξ, ‖(𝓕 v : Lp ℂ 2 (volume : Measure _)) ξ‖ = J := by
    rw [hJ]; exact integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable _)
  have hJ0 : 0 ≤ J := hJ ▸ ENNReal.toReal_nonneg
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((d : ℝ) / 2) : ℝ) : ℂ)
      * (𝓕 v) ξ) 2 volume).toReal := ⟨_, rfl⟩
  have hNle : N ≤ c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2) := hN ▸ (hEq v w hw).2
  have hvN : ‖v‖ ≤ N := hN ▸ norm_le_toReal_eLpNorm_symbol_mul_fourier (Nat.cast_nonneg d) v hF
  have hSnn : (0 : ℝ) ≤ ∑ α, ‖w α‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hS : (0 : ℝ) ≤ (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hSnn _
  -- the case `v = 0`
  rcases eq_or_lt_of_le (norm_nonneg v) with hv0 | hv0
  · have hF0 : (fun ξ ↦ ‖(𝓕 v : Lp ℂ 2 (volume : Measure _)) ξ‖) =ᵐ[volume] 0 := by
      have : 𝓕 v = 0 := by
        rw [← norm_eq_zero, Lp.norm_fourier_eq, ← hv0]
      rw [this]
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure _))] with ξ hξ
      simp only [hξ, Pi.zero_apply, norm_zero]
    calc ‖v' x‖ ≤ ∫ ξ, ‖(𝓕 v : Lp ℂ 2 (volume : Measure _)) ξ‖ := hv'b x
      _ = 0 := by rw [integral_congr_ae hF0]; simp
      _ ≤ _ := by positivity
  -- the case `v ≠ 0`: the scaling
  have ha : 0 < ‖v‖ ^ 2 := by positivity
  have hb : 0 < (c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ 2 := by
    exact pow_pos (hv0.trans_le (hvN.trans hNle)) 2
  obtain ⟨l, hl, hopt⟩ := exists_rpow_neg_half_mul_add_eq (by omega : d ≠ 0) ha hb
  have hmain := sq_toReal_lintegral_enorm_fourier_le (k := d)
    (by rw [finrank_euclideanSpace_fin]; omega) v hF hl
  rw [finrank_euclideanSpace_fin, ← hJ, ← hI, ← hN] at hmain
  have hmain' : J ^ 2 ≤ 2 ^ (d + 1) * I * c₂ * ‖v‖ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    have hld : 0 ≤ l ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hl.le _
    have hN0 : 0 ≤ N := (norm_nonneg v).trans hvN
    calc J ^ 2 ≤ l ^ (-(d : ℝ) / 2) * I * (2 ^ d * (‖v‖ ^ 2 + l ^ d * N ^ 2)) := hmain
      _ ≤ l ^ (-(d : ℝ) / 2) * I * (2 ^ d
          * (‖v‖ ^ 2 + l ^ d * (c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ 2)) := by gcongr
      _ = 2 ^ d * I * (l ^ (-(d : ℝ) / 2)
          * (‖v‖ ^ 2 + l ^ d * (c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ 2)) := by ring
      _ = 2 ^ d * I * (2 * Real.sqrt (‖v‖ ^ 2)
          * Real.sqrt ((c₂ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ 2)) := by rw [hopt]
      _ = 2 ^ (d + 1) * I * c₂ * ‖v‖ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2) := by
          rw [Real.sqrt_sq (norm_nonneg v), Real.sqrt_sq (mul_nonneg hc₂.le hS)]
          ring
  calc ‖v' x‖ ≤ J := hJreal ▸ hv'b x
    _ = Real.sqrt (J ^ 2) := (Real.sqrt_sq hJ0).symm
    _ ≤ Real.sqrt (2 ^ (d + 1) * I * c₂ * ‖v‖ * (∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) :=
        Real.sqrt_le_sqrt hmain'
    _ = Real.sqrt (2 ^ (d + 1) * I * c₂) * ((∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2)
          * ‖v‖ ^ ((1 : ℝ) / 2) := by
        have hc0 : 0 ≤ 2 ^ (d + 1) * I * c₂ := mul_nonneg (mul_nonneg (by positivity) hI0) hc₂.le
        rw [Real.sqrt_mul (mul_nonneg hc0 (norm_nonneg v)), Real.sqrt_mul hc0]
        simp only [Real.sqrt_eq_rpow]
        ring

/-- **Example 7.4.3** of [han2009theoretical], on the whole space. Let $d \ge 1$. There is a
constant $c \ge 0$ with the following property. Let $v \in L^2(\mathbb{R}^d)$ be real-valued,
and for each multi-index $\alpha$ with $|\alpha| \le d$ let $w_\alpha \in L^2(\mathbb{R}^d)$ be
the weak derivative $\partial^\alpha v$ on $\mathbb{R}^d$ in the sense of Definition 7.1.3, so
that $v \in H^d(\mathbb{R}^d)$. Then $v$ has a continuous representative $v'$ with
$$|v'(x)| \le c \, \|v\|_{H^d(\mathbb{R}^d)}^{1/2} \|v\|_{L^2(\mathbb{R}^d)}^{1/2} \quad
  \text{for all } x \in \mathbb{R}^d,$$
where $\|v\|_{H^d(\mathbb{R}^d)} = (\sum_{|\alpha| \le d} \|w_\alpha\|_{L^2}^2)^{1/2}$ is the
norm of Definition 7.2.2.

This is the case $\Omega = \mathbb{R}^d$ of (7.4.4), to which the proof of the source reduces
the general case. `AtkinsonHan.Chapter07.example_7_4_3_whole_space_complex` is the statement for
complex-valued functions, and the form on a domain is `AtkinsonHan.Chapter07.example_7_4_3`. -/
theorem example_7_4_3_whole_space (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (v : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (w : MultiIndexLE (Fin d) d → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))),
      (∀ α : MultiIndexLE (Fin d) d, definition_7_1_3_multiIndex α.1
          (v : EuclideanSpace ℝ (Fin d) → ℝ) (w α : EuclideanSpace ℝ (Fin d) → ℝ) ⊤) →
      ∃ v' : EuclideanSpace ℝ (Fin d) → ℝ, Continuous v' ∧
        (v : EuclideanSpace ℝ (Fin d) → ℝ) =ᵐ[volume] v' ∧
        ∀ x, |v' x| ≤ c * ((∑ α, ‖w α‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2)
          * ‖v‖ ^ ((1 : ℝ) / 2) := by
  obtain ⟨c, hc0, h⟩ := example_7_4_3_whole_space_complex hd
  refine ⟨c, hc0, fun v w hw ↦ ?_⟩
  have hres : ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)))
      = Set.univ := rfl
  have hcoe : ∀ f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
      (fun x ↦ (((f : EuclideanSpace ℝ (Fin d) → ℝ) x : ℝ) : ℂ))
        =ᵐ[volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin d))) : Set _)]
        ((Complex.ofRealCLM.compLp f : Lp ℂ 2 _) : EuclideanSpace ℝ (Fin d) → ℂ) := by
    intro f
    rw [hres, Measure.restrict_univ]
    filter_upwards [Complex.ofRealCLM.coeFn_compLp f] with x hx using hx.symm
  obtain ⟨v', hv'c, hv'ae, hv'b⟩ := h (Complex.ofRealCLM.compLp v)
    (fun α ↦ Complex.ofRealCLM.compLp (w α)) fun α ↦
      (HasWeakIteratedLineDerivOn.ofReal_iff.1 (hw α)).congr_ae (hcoe v) (hcoe (w α))
  refine ⟨fun x ↦ (v' x).re, Complex.continuous_re.comp hv'c, ?_, fun x ↦ ?_⟩
  · have h1 := hcoe v
    rw [hres, Measure.restrict_univ] at h1
    filter_upwards [h1, hv'ae] with x hx hx'
    rw [← hx', ← hx, Complex.ofReal_re]
  · calc |(v' x).re| ≤ ‖v' x‖ := Complex.abs_re_le_norm _
      _ ≤ _ := hv'b x
      _ = _ := by simp only [Lp.norm_ofRealCLM_compLp]

/-! ### Example 7.4.3 on a domain -/

/-- An element $u$ of $W^{k,2}(\mathbb{R}^N)$ gives a function $V \in L^2(\mathbb{R}^N)$ equal to
$u$ almost everywhere, weak derivatives $W_\alpha = \partial^\alpha V \in L^2(\mathbb{R}^N)$ for
$|\alpha| \le k$, with $(\sum_\alpha \|W_\alpha\|^2)^{1/2} = \|u\|$ and
$\|V\|_{L^2} = \|u\|_{L^2}$; this passes from the measure that the typed space carries on
$\mathbb{R}^N$ to the Lebesgue measure. -/
private theorem exists_lp_data_of_top {N k : ℕ}
    (u : SobolevMultiIndex ℝ (stdBasis N) k 2 (⊤ : Opens (EuclideanSpace ℝ (Fin N))) volume) :
    ∃ (V : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin N))))
      (W : MultiIndexLE (Fin N) k → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin N)))),
      (V : EuclideanSpace ℝ (Fin N) → ℝ) =ᵐ[volume] SobolevMultiIndex.fn u ∧
      (∀ α : MultiIndexLE (Fin N) k, definition_7_1_3_multiIndex α.1
        (V : EuclideanSpace ℝ (Fin N) → ℝ) (W α : EuclideanSpace ℝ (Fin N) → ℝ) ⊤) ∧
      (∑ α, ‖W α‖ ^ 2) ^ ((1 : ℝ) / 2) = ‖u‖ ∧
      ‖V‖ = (eLpNorm (SobolevMultiIndex.fn u) 2 volume).toReal := by
  have hres : ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)))
      = Set.univ := rfl
  have hμ : (volume : Measure (EuclideanSpace ℝ (Fin N))).restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N))) = volume := by
    rw [hres, Measure.restrict_univ]
  -- the weak derivatives, as functions: naming them frees the rewrite `hμ` from the dependence
  -- of the type of `SobolevMultiIndex.weakDeriv u α` on the measure
  obtain ⟨g, hg⟩ : ∃ g : MultiIndexLE (Fin N) k → EuclideanSpace ℝ (Fin N) → ℝ,
      ∀ α, g α = (SobolevMultiIndex.weakDeriv u α : EuclideanSpace ℝ (Fin N) → ℝ) :=
    ⟨_, fun _ ↦ rfl⟩
  have hmemV : MemLp (SobolevMultiIndex.fn u) 2 (volume : Measure (EuclideanSpace ℝ (Fin N))) := by
    have h := SobolevMultiIndex.memLp u
    rwa [hμ] at h
  have hmemW : ∀ α : MultiIndexLE (Fin N) k,
      MemLp (g α) 2 (volume : Measure (EuclideanSpace ℝ (Fin N))) := fun α ↦ by
    have h : MemLp (g α) 2 ((volume : Measure (EuclideanSpace ℝ (Fin N))).restrict
        ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)))) := by
      rw [hg α]; exact Lp.memLp _
    rwa [hμ] at h
  refine ⟨hmemV.toLp _, fun α ↦ (hmemW α).toLp _, hmemV.coeFn_toLp, fun α ↦ ?_, ?_, ?_⟩
  · refine (SobolevMultiIndex.hasWeakIteratedLineDerivOn u α).congr_ae
      (hmemV.coeFn_toLp.symm.filter_mono (ae_mono Measure.restrict_le_self)) ?_
    refine Filter.EventuallyEq.filter_mono ?_ (ae_mono Measure.restrict_le_self)
    rw [← hg α]
    exact (hmemW α).coeFn_toLp.symm
  · rw [SobolevMultiIndex.norm_eq_sum (by simp) u]
    have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by simp
    rw [h2]
    congr 1
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [Real.rpow_two, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hmemW α).coeFn_toLp, ← hg α, hμ]
  · rw [Lp.norm_def, eLpNorm_congr_ae hmemV.coeFn_toLp]

/-- Example 7.4.3 on the whole space for $u$ in the typed space $W^{N,2}(\mathbb{R}^N)$ with
$N \ge 1$: $u$ has a continuous representative $u'$ with
$|u'(x)| \le c \|u\|^{1/2} \|u\|_{L^2}^{1/2}$ for all $x$. -/
private theorem example_7_4_3_whole_space_typed {N : ℕ} (hN : 1 ≤ N) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ u : SobolevMultiIndex ℝ (stdBasis N) N 2 (⊤ : Opens (EuclideanSpace ℝ (Fin N))) volume,
        ∃ u' : EuclideanSpace ℝ (Fin N) → ℝ, Continuous u' ∧
          SobolevMultiIndex.fn u =ᵐ[volume] u' ∧
          ∀ x, |u' x| ≤ c * ‖u‖ ^ ((1 : ℝ) / 2)
            * (eLpNorm (SobolevMultiIndex.fn u) 2 volume).toReal ^ ((1 : ℝ) / 2) := by
  obtain ⟨c₀, hc₀, hws⟩ := example_7_4_3_whole_space hN
  refine ⟨c₀, hc₀, fun u ↦ ?_⟩
  obtain ⟨V, W, hVfn, hW, hWnorm, hVnorm⟩ := exists_lp_data_of_top u
  obtain ⟨u', hu'c, hu'ae, hu'b⟩ := hws V W hW
  refine ⟨u', hu'c, hVfn.symm.trans hu'ae, fun x ↦ ?_⟩
  have h := hu'b x
  rwa [hWnorm, hVnorm] at h

/-- **Example 7.4.3** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded
open set whose boundary is of class $C^{d+1}$ in the sense of Definition 7.2.1. There is a
constant $c \ge 0$ such that every $v \in H^{d+1}(\Omega)$ has a representative $v'$, continuous
on all of $\mathbb{R}^{d+1}$ and equal to $v$ almost everywhere on $\Omega$, with
$$|v'(x)| \le c \, \|v\|_{H^{d+1}(\Omega)}^{1/2} \|v\|_{L^2(\Omega)}^{1/2} \quad \text{for all }
  x \in \mathbb{R}^{d+1}.$$
In particular $\|v\|_{C(\bar\Omega)} \le c \|v\|_{H^{d+1}(\Omega)}^{1/2}
\|v\|_{L^2(\Omega)}^{1/2}$, which is (7.4.4).

**Reading.** The source assumes a Lipschitz domain and takes the extension $Ev$ from the
universal extension operator of Stein in Theorem 7.3.5, which is bounded on $H^k$ for every $k$
at once. Here $\Omega$ is a bounded $C^{d+1}$ domain, and $E$ is the extension operator of order
$d + 1$ of `AtkinsonHan.Chapter07.theorem_7_3_5_order_lp`. This operator is bounded on
$H^{d+1}(\Omega)$ and also from $L^2(\Omega)$ to $L^2(\mathbb{R}^{d+1})$, because the reflection
is a finite sum of dilations; these are the two bounds that the argument needs.

The ambient dimension is written $d + 1$, as in Definition 7.2.1, so the dimension $d$ of the
source is $d + 1$ here, and the order of the Sobolev space equals the dimension. The norm of
$H^{d+1}(\Omega)$ is the norm of Definition 7.2.2 that the type carries, and
$\|v\|_{L^2(\Omega)}$ is `(eLpNorm (fn v) 2 (volume.restrict Ω)).toReal`. Step 3 of the proof of
the source is the estimate $\|v'\|_\infty \le c_0 \|Ev\|_{H^{d+1}}^{1/2} \|Ev\|_{L^2}^{1/2} \le
c_0 c_E \|v\|_{H^{d+1}(\Omega)}^{1/2} \|v\|_{L^2(\Omega)}^{1/2}$, where the first inequality is
`AtkinsonHan.Chapter07.example_7_4_3_whole_space`. -/
theorem example_7_4_3 {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : definition_7_2_1 {g | ContDiff ℝ (d + 1 : ℕ) g} Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) (d + 1) 2 Ω volume,
        ∃ v' : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous v' ∧
          SobolevMultiIndex.fn v
            =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v' ∧
          ∀ x, |v' x| ≤ c * ‖v‖ ^ ((1 : ℝ) / 2)
            * (eLpNorm (SobolevMultiIndex.fn v) 2
                (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal
              ^ ((1 : ℝ) / 2) := by
  obtain ⟨c₀, hc₀, hws⟩ := example_7_4_3_whole_space_typed (N := d + 1) (Nat.le_add_left 1 d)
  have hEx := theorem_7_3_5_order_lp (k := d + 1) (p := 2) (Nat.le_add_left 1 d) hΩ hb
  obtain ⟨E, hEae, cE, hEnorm, hElp⟩ := hEx
  have hcE : (0 : ℝ) ≤ max cE 0 := le_max_right _ _
  refine ⟨c₀ * max cE 0, by positivity, fun v ↦ ?_⟩
  have hwv := hws (E v)
  obtain ⟨v', hv'c, hv'ae, hv'b⟩ := hwv
  refine ⟨v', hv'c, (hEae v).symm.trans
    (hv'ae.filter_mono (ae_mono Measure.restrict_le_self)), fun x ↦ ?_⟩
  have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hL0 : (0 : ℝ) ≤ (eLpNorm (SobolevMultiIndex.fn v) 2
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal :=
    ENNReal.toReal_nonneg
  have h1 : ‖E v‖ ≤ max cE 0 * ‖v‖ :=
    (hEnorm v).trans (by gcongr; exact le_max_left _ _)
  have h2 : (eLpNorm (SobolevMultiIndex.fn (E v)) 2 volume).toReal
      ≤ max cE 0 * (eLpNorm (SobolevMultiIndex.fn v) 2
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal := by
    have hne : ENNReal.ofReal cE * eLpNorm (SobolevMultiIndex.fn v) 2
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (SobolevMultiIndex.memLp v).eLpNorm_ne_top
    refine (ENNReal.toReal_mono hne (hElp v)).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal']
  have hA : (max cE 0) ^ ((1 : ℝ) / 2) * (max cE 0) ^ ((1 : ℝ) / 2) = max cE 0 := by
    rw [← Real.rpow_add' hcE (by norm_num)]
    norm_num
  calc |v' x| ≤ c₀ * ‖E v‖ ^ ((1 : ℝ) / 2)
        * (eLpNorm (SobolevMultiIndex.fn (E v)) 2 volume).toReal ^ ((1 : ℝ) / 2) := hv'b x
    _ ≤ c₀ * (max cE 0 * ‖v‖) ^ ((1 : ℝ) / 2)
        * (max cE 0 * (eLpNorm (SobolevMultiIndex.fn v) 2
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal)
          ^ ((1 : ℝ) / 2) := by
        gcongr
    _ = c₀ * max cE 0 * ‖v‖ ^ ((1 : ℝ) / 2)
        * (eLpNorm (SobolevMultiIndex.fn v) 2
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal
          ^ ((1 : ℝ) / 2) := by
        rw [Real.mul_rpow hcE hv0, Real.mul_rpow hcE hL0]
        calc c₀ * ((max cE 0) ^ ((1 : ℝ) / 2) * ‖v‖ ^ ((1 : ℝ) / 2))
              * ((max cE 0) ^ ((1 : ℝ) / 2) * (eLpNorm (SobolevMultiIndex.fn v) 2
                (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal
                ^ ((1 : ℝ) / 2))
            = c₀ * ((max cE 0) ^ ((1 : ℝ) / 2) * (max cE 0) ^ ((1 : ℝ) / 2))
              * (‖v‖ ^ ((1 : ℝ) / 2) * (eLpNorm (SobolevMultiIndex.fn v) 2
                (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal
                ^ ((1 : ℝ) / 2)) := by ring
          _ = c₀ * max cE 0 * ‖v‖ ^ ((1 : ℝ) / 2)
              * (eLpNorm (SobolevMultiIndex.fn v) 2
                (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))).toReal
                ^ ((1 : ℝ) / 2) := by rw [hA]; ring


end Interpolation

end AtkinsonHan.Chapter07
