/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Wavelet.Daubechies
import Numlib.Analysis.Wavelet.Multiresolution
import NumlibSurface.AtkinsonHan.Chapter04.Section04

/-!
# Atkinson and Han, Section 4.5: Multiresolution analysis

This module formalizes Section 4.5 of [han2009theoretical], multiresolution analysis on
$L^2(\mathbb{R})$. A multiresolution analysis is an increasing sequence of closed subspaces $V_j$,
$j \in \mathbb{Z}$, of $L^2(\mathbb{R})$ together with a scaling function $\phi$ that satisfy five
axioms (Definition 4.5.1). Write $\phi_{j,k}(x) = 2^{j/2} \phi(2^j x - k)$. The scaling function
satisfies the scaling equation $\phi = \sum_k p_k \phi_{1,k}$ with the dilation coefficients
$p_k = (\phi_{1,k}, \phi)$, and these coefficients define the wavelet
$$\psi(x) = \sum_{k \in \mathbb{Z}} (-1)^k p_{1-k} \sqrt 2 \, \phi(2x - k).$$
The module proves that the $\phi_{j,k}$ are an orthonormal basis of $V_j$ (Proposition 4.5.2), the
scaling equation, the condition $\sum_k p_k p_{k-2l} = \delta_{0l}$ (Exercise 4.5.2), and Mallat's
theorem: the $\psi_{j,k}(x) = 2^{j/2} \psi(2^j x - k)$ are an orthonormal basis of the wavelet space
$W_j = V_{j+1} \ominus V_j$ for each $j$, and of $L^2(\mathbb{R})$ over all $j$ and $k$. It checks
that the Haar system of Section 4.4 is an example, and it proves that the Daubechies scaling
function $D_4$ of (4.5.5)–(4.5.7) exists and has the values of Exercise 4.5.5.

The proofs specialize the backbone modules `Numlib.Analysis.Wavelet.Multiresolution` and
`Numlib.Analysis.Wavelet.Daubechies`. The first has the predicate `IsMultiresolutionAnalysis`, the
systems `scalingSystem` and `waveletSystem`, the wavelet `mraWavelet` and the Haar example
`Haar.isMultiresolutionAnalysis`.

## Main definitions

* Definition 4.5.1, `AtkinsonHan.Chapter04.definition_4_5_1`: the five axioms of a multiresolution
  analysis, as an equivalence with `IsMultiresolutionAnalysis`.
* Equation (4.5.2), `AtkinsonHan.Chapter04.scalingCoeff`: the dilation coefficients
  $p_k = (\phi_{1,k}, \phi)$.

## Main results

* Proposition 4.5.2, `AtkinsonHan.Chapter04.proposition_4_5_2`: the $\phi_{j,k}$,
  $k \in \mathbb{Z}$, form an orthonormal basis of $V_j$.
* Equations (4.5.1) and (4.5.3), `AtkinsonHan.Chapter04.equation_4_5_2`: the scaling equation
  $\phi = \sum_k p_k \phi_{1,k}$, and the expansion of each $\phi_{j,l}$ in the system of level
  $j + 1$.
* Equation (4.5.4), `AtkinsonHan.Chapter04.equation_4_5_4`: the series that defines the wavelet
  $\psi$ converges in $L^2(\mathbb{R})$.
* Section 4.5, Mallat's theorem, `AtkinsonHan.Chapter04.theorem_wavelet_spaces`: the $\psi_{j,k}$
  form an orthonormal basis of $W_j$ for each $j$, the $W_j$ are mutually orthogonal, and all
  $\psi_{j,k}$ together form an orthonormal basis of $L^2(\mathbb{R})$.
* `AtkinsonHan.Chapter04.haar_scalingCoeff` and `AtkinsonHan.Chapter04.haar_mraWavelet`: for the
  Haar scaling function, $p_0 = p_1 = 1/\sqrt 2$ and $p_k = 0$ otherwise, and (4.5.4) gives the Haar
  wavelet of Section 4.4.
* Equations (4.5.5)–(4.5.7), `AtkinsonHan.Chapter04.equation_4_5_6`: the Daubechies scaling function
  $D_4$ exists, with support $[0, 3]$.
* Exercise 4.5.2, `AtkinsonHan.Chapter04.exercise_4_5_2`: $\sum_k p_k p_{k-2l} = \delta_{0l}$.
* Exercise 4.5.5, `AtkinsonHan.Chapter04.exercise_4_5_5` and
  `AtkinsonHan.Chapter04.exists_daubechies_values`: the values of the $D_4$ scaling function at
  $0, \tfrac14, \tfrac12, \tfrac32, 3$.
* Exercise 4.5.6, `AtkinsonHan.Chapter04.exercise_4_5_6_subset`: the $D_4$ wavelet vanishes outside
  $[-1, 2]$.

## Implementation notes

* Two of the five axioms of Definition 4.5.1 are stated in an equivalent form. Shift invariance says
  that the integer translates of $\phi$ are orthonormal and that $V_0$ is their closed span; the
  book says that the translates are an orthonormal basis of $V_0$. Scale invariance says
  $V_j = D_{2^j}(V_0)$ for the unitary dilation $D_c f = |c|^{1/2} f(c \, \cdot)$; the book says
  $f \in V_j \iff f(2^{-j} \, \cdot) \in V_0$. The forms used here are the ones that a construction
  proves, and images of spans are easy to compute in them.
* "Orthonormal basis" is not stated as a bundled `HilbertBasis`. Instead
  `AtkinsonHan.Chapter04.proposition_4_5_2` and `AtkinsonHan.Chapter04.theorem_wavelet_spaces` give
  orthonormality, the closed span, and the expansion $f = \sum_k (\phi_{j,k}, f) \phi_{j,k}$. This
  avoids a transport of a basis along $V_j = \overline{\operatorname{span}}\{\phi_{j,k}\}$. The
  bundled form is `IsMultiresolutionAnalysis.hilbertBasis`.
* The book writes the coefficients of the dilated scaling equation (4.5.3) as $p_{k-2l}$, the
  sequence of (4.5.1) shifted by $2l$. `AtkinsonHan.Chapter04.equation_4_5_2` states (4.5.3) with
  the coefficients $(\phi_{j+1,k}, \phi_{j,l})$. The identification with $p_{k-2l}$ comes from
  `translationₗᵢ_scalingSystem_one`: a unit translation at level $0$ is a translation by two at
  level $1$. This lemma is also the basis of Exercise 4.5.2, and
  `IsMultiresolutionAnalysis.hasSum_scalingSystem_low` is (4.5.3) in the book's form at every level.
* The existence of a scaling function for a given coefficient sequence (see below) does not follow
  from the obvious hypotheses. The scaling equation has the solution $\phi = 0$. The condition of
  Exercise 4.5.2 alone does not give a scaling function: the mask $m_0(\xi) = (1 + e^{3i\xi})/2$,
  that is, $p_0 = p_3 = 1/\sqrt 2$ and $p_k = 0$ otherwise, satisfies
  $\sum_k p_k p_{k-2l} = \delta_{0l}$, but its cascade limit $\tfrac13 1_{[0,3]}$ has integer
  translates that are not orthonormal. A correct statement needs a further hypothesis, such as
  Cohen's condition or $m_0 \ne 0$ on $[-\pi/2, \pi/2]$. The standard proofs use the Fourier
  transform: the infinite product $\hat\phi(\xi) = \prod_{j \ge 1} m_0(2^{-j} \xi)$ or the $L^2$
  convergence of the cascade iteration, the periodization $\sum_k |\hat\phi(\xi + 2\pi k)|^2 = 1$
  that characterizes orthonormal integer translates, and
  $\hat\phi(\xi) = m_0(\xi/2) \hat\phi(\xi/2)$. The library has the periodization identity $\int_0^T
  \sum_k g(x + kT) \, dx = \int_{\mathbb{R}} g$ with its corollary on Fourier coefficients
  (`Numlib.Analysis.Fourier.Periodisation`), and the transform rules that it needs
  (`Numlib.Analysis.Fourier.FourierIntegral`). It does not have $L^1$ uniqueness on the circle (an
  integrable function whose Fourier coefficients are those of $1$ is $1$ almost everywhere). Mathlib
  has the $L^2$ form of this uniqueness through `fourierBasis`; the usual proof of the $L^1$ form
  uses the Fejér kernel, or a density argument against continuous functions on the circle with
  `span_fourier_closure_eq_top`. The library also does not have Cohen's condition with the infinite
  product and its $L^2$ convergence.
* The existence of the $D_4$ function, `AtkinsonHan.Chapter04.equation_4_5_6`, needs none of this
  theory: for this one mask the cascade iteration converges by an elementary matrix estimate.
  Mallat's theorem does not need it either; the backbone proves it from the algebra of quadrature
  mirror filters in `Numlib.Analysis.Wavelet.QuadratureMirror`.

## Deviations from the source

* **Definition 4.5.1 and Equation (4.5.3)** (reading). The equivalent scale-invariance axiom
  uses unitary dilation. The dilated expansion writes the shifted coefficients as inner products.
* **The fourth property of the wavelet spaces** (correction). The closed span of the $W_j$
  is all of $L^2(\mathbb R)$. The set-theoretic union of the mutually orthogonal spaces
  is not dense. See `AtkinsonHan.Chapter04.theorem_wavelet_spaces`.
* **Exercises 4.5.5–4.5.6** (reading). The point values need only vanishing outside the
  support interval together with the equation and normalization. The wavelet support is
  proved to be contained in $[-1,2]$.

## Not formalized

* The existence half of the construction (4.5.1)–(4.5.3), which the book leaves to Daubechies: that
  a sequence $\{p_k\}$ is the coefficient sequence of a scaling function $\phi \in L^2(\mathbb{R})$
  with orthonormal integer translates. It needs the Fourier-side theory described in the
  implementation notes.
* The orthonormality of the integer translates of the $D_4$ scaling function. It is the same
  Fourier-side statement, so `AtkinsonHan.Chapter04.equation_4_5_6` gives the function of
  (4.5.5)–(4.5.7), not a multiresolution analysis built from it.
* The weaker form of axiom (1) with a stable basis in place of an orthonormal one. The book only
  remarks that one can renormalize to the orthonormal case.
* The property $f \in W_j \iff f(2^{-j} \, \cdot) \in W_0$ in the list of properties of the wavelet
  spaces. It is the scale invariance of the spaces and holds by construction, because $W_j$ is
  defined from $V_j$ and $V_{j+1}$.
* The equality $\operatorname{supp} \psi = [-1, 2]$ in Exercise 4.5.6. Only the inclusion is proved.
-/

open MeasureTheory Real

namespace AtkinsonHan.Chapter04

/-! ### The five axioms -/

/-- **Definition 4.5.1** of [han2009theoretical]. Let $V_j$, $j \in \mathbb{Z}$, be subspaces of
$L^2(\mathbb{R})$, and let $\phi \in L^2(\mathbb{R})$. Then $(\{V_j\}, \phi)$ is a
**multiresolution analysis** with scaling function $\phi$ if and only if it is

1. *shift invariant*: the integer translates $\phi(\cdot - k)$, $k \in \mathbb{Z}$, are
   orthonormal, and $V_0$ is the closure of their span;
2. *scale invariant*: for every $j$, $V_j$ is the image of $V_0$ under the unitary dilation
   $f \mapsto 2^{j/2} f(2^j \, \cdot)$;
3. *nested*: $V_j \subseteq V_{j+1}$ for every $j$;
4. *dense*: $\bigcup_j V_j$ is dense in $L^2(\mathbb{R})$, that is, the closure of the sum of
   the $V_j$ is $L^2(\mathbb{R})$;
5. *separated*: $\bigcap_j V_j = \{0\}$.

These five clauses are the fields of the backbone structure `IsMultiresolutionAnalysis`. Clauses
1 and 2 are equivalent forms of the book's clauses; see the module documentation. The translates
are `translates φ k` and the dilation is `MeasureTheory.Lp.dilationₗᵢ`. -/
theorem definition_4_5_1 (V : ℤ → Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)))
    (φ : Lp ℝ 2 (volume : Measure ℝ)) :
    IsMultiresolutionAnalysis V φ ↔
      ((Orthonormal ℝ (translates φ) ∧
          V 0 = (Submodule.span ℝ (Set.range (translates φ))).topologicalClosure) ∧
        (∀ j : ℤ, V j = (V 0).map (Lp.dilationₗᵢ ((2 : ℝ) ^ j)
          (zpow_ne_zero j two_ne_zero)).toLinearEquiv.toLinearMap) ∧
        (∀ j : ℤ, V j ≤ V (j + 1)) ∧
        (⨆ j : ℤ, V j).topologicalClosure = ⊤ ∧
        (⨅ j : ℤ, V j) = ⊥) :=
  ⟨fun h => ⟨⟨h.orthonormal_translates, h.eq_topologicalClosure_span⟩, h.eq_map_dilation,
      h.le_succ, h.topologicalClosure_iSup, h.iInf_eq_bot⟩,
    fun h => ⟨h.1.1, h.1.2, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

section

variable {V : ℤ → Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ))}
  {φ : Lp ℝ 2 (volume : Measure ℝ)}

/-- **Proposition 4.5.2** of [han2009theoretical]. Let $(\{V_j\}, \phi)$ be a multiresolution
analysis and $j \in \mathbb{Z}$. Then the functions $\phi_{j,k}(x) = 2^{j/2} \phi(2^j x - k)$,
$k \in \mathbb{Z}$, are an orthonormal basis of $V_j$:

1. they are orthonormal;
2. $V_j$ is the closure of their span;
3. every $f \in V_j$ is the sum of the series $\sum_{k \in \mathbb{Z}} (\phi_{j,k}, f) \,
   \phi_{j,k}$, which converges unconditionally in $L^2(\mathbb{R})$.

The function $\phi_{j,k}$ is `scalingSystem φ j k`. The expansion is stated instead of a bundled
`HilbertBasis`, because it is the form that a user needs and it needs no transport along $V_j =
\overline{\operatorname{span}}\{\phi_{j,k}\}$. -/
theorem proposition_4_5_2 (h : IsMultiresolutionAnalysis V φ) (j : ℤ) :
    Orthonormal ℝ (scalingSystem φ j) ∧
      V j = (Submodule.span ℝ (Set.range (scalingSystem φ j))).topologicalClosure ∧
      ∀ f ∈ V j,
        HasSum (fun k : ℤ => (inner ℝ (scalingSystem φ j k) f) • scalingSystem φ j k) f :=
  ⟨h.orthonormal_scaled j, h.eq_topologicalClosure_span_scalingSystem j,
    fun _ hf => h.hasSum_inner_smul j hf⟩

/-! ### The scaling equation -/

/-- **Equation (4.5.2)** of [han2009theoretical]. The **dilation coefficients** of a function
$\phi \in L^2(\mathbb{R})$ are
$$p_k = \int_{\mathbb{R}} \sqrt 2 \, \phi(2x - k) \, \phi(x) \, dx = (\phi_{1,k}, \phi), \qquad
  k \in \mathbb{Z}.$$

This is the backbone definition of the same name in the root namespace. -/
noncomputable abbrev scalingCoeff (φ : Lp ℝ 2 (volume : Measure ℝ)) (k : ℤ) : ℝ :=
  _root_.scalingCoeff φ k

/-- **Equations (4.5.1) and (4.5.3)** of [han2009theoretical], the scaling equation and its dilated
form. Let $(\{V_j\}, \phi)$ be a multiresolution analysis with dilation coefficients $p_k$. Then
$$\phi = \sum_{k \in \mathbb{Z}} p_k \sqrt 2 \, \phi(2x - k),$$
and for all $j, l \in \mathbb{Z}$,
$$\phi_{j,l} = \sum_{k \in \mathbb{Z}} (\phi_{j+1,k}, \phi_{j,l}) \, \phi_{j+1,k}.$$
Both series converge unconditionally in $L^2(\mathbb{R})$.

The proof expands $\phi \in V_0 \subseteq V_1$, and $\phi_{j,l} \in V_j \subseteq V_{j+1}$, in
the orthonormal basis of the finer space. The book writes the coefficients of the second series
as $p_{k-2l}$; this form is `IsMultiresolutionAnalysis.hasSum_scalingSystem_low`.

**Reading.** The dilated coefficients are expressed as inner products of neighboring scale
functions. These are the shifted coefficients $p_{k-2l}$ of (4.5.3). -/
theorem equation_4_5_2 (h : IsMultiresolutionAnalysis V φ) :
    HasSum (fun k : ℤ => scalingCoeff φ k • scalingSystem φ 1 k) φ ∧
      ∀ j l : ℤ, HasSum (fun k : ℤ =>
        (inner ℝ (scalingSystem φ (j + 1) k) (scalingSystem φ j l)) • scalingSystem φ (j + 1) k)
        (scalingSystem φ j l) :=
  ⟨h.hasSum_scalingEquation,
    fun j l => h.hasSum_inner_smul (j + 1) (h.le_succ j (h.scalingSystem_mem j l))⟩

/-- **Exercise 4.5.2** of [han2009theoretical]. Let $(\{V_j\}, \phi)$ be a multiresolution analysis
with dilation coefficients $p_k$. Then for every $l \in \mathbb{Z}$,
$$\sum_{k \in \mathbb{Z}} p_k \, p_{k-2l} = \delta_{0l},$$
with the series convergent.

This condition is necessary for the integer translates of $\phi$ to be orthonormal. The book
gives it as an example of the identities that constrain $\{p_k\}$, and remarks that it is
difficult to find coefficients that satisfy all of them. The constructions that do so are left
to Daubechies. -/
theorem exercise_4_5_2 (h : IsMultiresolutionAnalysis V φ) (l : ℤ) :
    HasSum (fun k : ℤ => scalingCoeff φ k * scalingCoeff φ (k - 2 * l))
      (if l = 0 then (1 : ℝ) else 0) :=
  h.hasSum_scalingCoeff_mul l

/-! ### The wavelet and the wavelet spaces -/

/-- **Equation (4.5.4)** of [han2009theoretical], the wavelet of a multiresolution analysis. Let
$(\{V_j\}, \phi)$ be a multiresolution analysis with dilation coefficients $p_k$. Then the
series
$$\psi(x) = \sum_{k \in \mathbb{Z}} (-1)^k p_{1-k} \sqrt 2 \, \phi(2x - k)$$
converges unconditionally in $L^2(\mathbb{R})$, and its sum is the wavelet $\psi$.

The wavelet is the backbone definition `mraWavelet φ`, which is a `tsum` of this series. The
content of the statement is the convergence, which holds because $\sum_k p_k^2 = 1$. -/
theorem equation_4_5_4 (h : IsMultiresolutionAnalysis V φ) :
    HasSum (fun k : ℤ => ((-1 : ℝ) ^ k * scalingCoeff φ (1 - k)) • scalingSystem φ 1 k)
      (mraWavelet φ) :=
  h.hasSum_mraWavelet

/-- **Section 4.5** of [han2009theoretical], the properties of the wavelet spaces (**Mallat's
theorem**). Let $(\{V_j\}, \phi)$ be a multiresolution analysis, let $\psi$ be its wavelet
(4.5.4), let $\psi_{j,k}(x) = 2^{j/2} \psi(2^j x - k)$, and let $W_j = V_{j+1} \cap V_j^\perp$.
Then:

1. $\psi \in V_1$, its integer translates $\psi(\cdot - k)$ are orthonormal, and $W_0$ is the
   closure of their span;
2. for every $j$, the $\psi_{j,k}$, $k \in \mathbb{Z}$, are orthonormal, and $W_j$ is the
   closure of their span;
3. $W_i$ and $W_j$ are orthogonal for $i \ne j$;
4. the family $\{\psi_{j,k}\}_{(j,k) \in \mathbb{Z}^2}$ is orthonormal, and every
   $f \in L^2(\mathbb{R})$ is the sum of the series
   $\sum_{(j,k)} (\psi_{j,k}, f) \, \psi_{j,k}$, which converges unconditionally.

The book lists these properties without proof and refers to Daubechies, whose proof uses the
Fourier transform. The backbone proves them without the Fourier transform, from the algebra of
quadrature mirror filters. The book's property $f \in W_j \iff f(2^{-j} \, \cdot) \in W_0$ is
not stated; it holds by construction, because $W_j$ (`waveletSpace V j`) is defined from $V_j$
and $V_{j+1}$. The function $\psi_{j,k}$ is `waveletSystem φ j k`.

**Correction.** The source's fourth property says the union of the wavelet spaces is dense.
For two nonzero orthogonal components in different spaces, their sum stays a positive
distance from the entire union. The algebraic span of the spaces is dense, as follows from
the full orthonormal expansion. -/
theorem theorem_wavelet_spaces (h : IsMultiresolutionAnalysis V φ) :
    mraWavelet φ ∈ V 1 ∧
      Orthonormal ℝ (translates (mraWavelet φ)) ∧
      waveletSpace V 0
        = (Submodule.span ℝ (Set.range (translates (mraWavelet φ)))).topologicalClosure ∧
      (∀ j : ℤ, Orthonormal ℝ (waveletSystem φ j) ∧
        waveletSpace V j
          = (Submodule.span ℝ (Set.range (waveletSystem φ j))).topologicalClosure) ∧
      (∀ i j : ℤ, i ≠ j → ∀ u ∈ waveletSpace V i, ∀ v ∈ waveletSpace V j,
        inner ℝ u v = (0 : ℝ)) ∧
      Orthonormal ℝ (fun jk : ℤ × ℤ => waveletSystem φ jk.1 jk.2) ∧
      ∀ f : Lp ℝ 2 (volume : Measure ℝ), HasSum (fun jk : ℤ × ℤ =>
        (inner ℝ (waveletSystem φ jk.1 jk.2) f) • waveletSystem φ jk.1 jk.2) f := by
  have h0 : waveletSystem φ 0 = translates (mraWavelet φ) := scalingSystem_zero (mraWavelet φ)
  refine ⟨h.mraWavelet_mem_V_one, ?_, ?_,
    fun j => ⟨h.orthonormal_waveletSystem j, h.waveletSpace_eq j⟩, ?_,
    h.orthonormal_waveletSystem_prod, h.hasSum_inner_smul_waveletSystem⟩
  · rw [← h0]
    exact h.orthonormal_waveletSystem 0
  · rw [← h0]
    exact h.waveletSpace_eq 0
  · intro i j hij u hu v hv
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact h.inner_waveletSpace_eq_zero_of_lt hlt hu hv
    · rw [real_inner_comm]
      exact h.inner_waveletSpace_eq_zero_of_lt hlt hv hu

end

/-- The dilation coefficients of the **Haar** multiresolution analysis, whose scaling function is
$\phi = 1_{[0,1)}$: $p_0 = p_1 = 1/\sqrt 2$, and $p_k = 0$ for $k \ne 0, 1$.

This is the two-scale relation $\phi(x) = \phi(2x) + \phi(2x - 1)$ of Section 4.4 of
[han2009theoretical], written in the normalized basis. It is the example of the dilation
coefficients (4.5.2) in Section 4.5. -/
theorem haar_scalingCoeff :
    scalingCoeff (Haar.scalingFun 0 0) 0 = (√2)⁻¹ ∧
      scalingCoeff (Haar.scalingFun 0 0) 1 = (√2)⁻¹ ∧
      ∀ k : ℤ, k ≠ 0 → k ≠ 1 → scalingCoeff (Haar.scalingFun 0 0) k = 0 := by
  have hsys : ∀ k : ℤ, scalingSystem (Haar.scalingFun 0 0) 1 k = Haar.scalingFun 1 k := by
    intro k
    have h1 : scalingSystem (Haar.scalingFun 0 0) 1 k
        = Lp.dilationₗᵢ ((2 : ℝ) ^ (1 : ℤ)) (zpow_ne_zero 1 two_ne_zero)
          (translates (Haar.scalingFun 0 0) k) := rfl
    rw [h1, Haar.translates_scalingFun_zero, ← Haar.scalingFun_eq_dilation]
  have hexp : Haar.scalingFun 0 0 = (√2)⁻¹ • (Haar.scalingFun 1 0 + Haar.scalingFun 1 1) := by
    simpa using Haar.scalingFun_two_scale 0 0
  have hcoeff : ∀ k : ℤ, scalingCoeff (Haar.scalingFun 0 0) k
      = (√2)⁻¹ * (inner ℝ (Haar.scalingFun 1 k) (Haar.scalingFun 1 0)
          + inner ℝ (Haar.scalingFun 1 k) (Haar.scalingFun 1 1)) := by
    intro k
    change inner ℝ (scalingSystem (Haar.scalingFun 0 0) 1 k) (Haar.scalingFun 0 0) = _
    rw [hsys k, hexp, real_inner_smul_right, inner_add_right]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcoeff, Haar.inner_scalingFun_self,
      Haar.inner_scalingFun_of_ne 1 (by norm_num : (0 : ℤ) ≠ 1)]
    ring
  · rw [hcoeff, Haar.inner_scalingFun_of_ne 1 (by norm_num : (1 : ℤ) ≠ 0),
      Haar.inner_scalingFun_self]
    ring
  · intro k hk0 hk1
    rw [hcoeff, Haar.inner_scalingFun_of_ne 1 hk0, Haar.inner_scalingFun_of_ne 1 hk1]
    ring

/-- The general construction (4.5.4) of [han2009theoretical] gives the **Haar wavelet** for the Haar
scaling function $\phi = 1_{[0,1)}$: `mraWavelet` $\phi$ is the Haar wavelet $\psi_{0,0}$ of
Section 4.4.

The Haar coefficients are $p_0 = p_1 = 1/\sqrt 2$, so the coefficients $(-1)^k p_{1-k}$ in
(4.5.4) are $1/\sqrt 2$ at $k = 0$, $-1/\sqrt 2$ at $k = 1$ and $0$ otherwise. Thus (4.5.4)
gives $\psi(x) = \phi(2x) - \phi(2x - 1)$. -/
theorem haar_mraWavelet : mraWavelet (Haar.scalingFun 0 0) = Haar.waveletFun 0 0 := by
  obtain ⟨hp0, hp1, hpk⟩ := haar_scalingCoeff
  have hsys : ∀ k : ℤ, scalingSystem (Haar.scalingFun 0 0) 1 k = Haar.scalingFun 1 k := by
    intro k
    have h1 : scalingSystem (Haar.scalingFun 0 0) 1 k
        = Lp.dilationₗᵢ ((2 : ℝ) ^ (1 : ℤ)) (zpow_ne_zero 1 two_ne_zero)
          (translates (Haar.scalingFun 0 0) k) := rfl
    rw [h1, Haar.translates_scalingFun_zero, ← Haar.scalingFun_eq_dilation]
  have hfin : HasSum (fun k : ℤ => qmfHigh (scalingCoeff (Haar.scalingFun 0 0)) k
        • scalingSystem (Haar.scalingFun 0 0) 1 k)
      (∑ k ∈ ({0, 1} : Finset ℤ), qmfHigh (scalingCoeff (Haar.scalingFun 0 0)) k
        • scalingSystem (Haar.scalingFun 0 0) 1 k) :=
    hasSum_sum_of_ne_finset_zero (fun k hk => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      rw [qmfHigh, hpk (1 - k) (by omega) (by omega), mul_zero, zero_smul])
  rw [Haar.isMultiresolutionAnalysis.hasSum_mraWavelet.unique hfin]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [qmfHigh, hsys, Haar.waveletFun, zpow_zero, zpow_one,
    show (1 : ℤ) - 0 = 1 from by ring, show (1 : ℤ) - 1 = 0 from by ring, hp0, hp1,
    show (2 : ℤ) * 0 = 0 from by ring, show (0 : ℤ) + 1 = 1 from by ring]
  module

/-! ### The Daubechies example -/

/-- **Exercise 4.5.5** of [han2009theoretical], the values of the Daubechies scaling function $D_4$
at the first dyadic points. Let $\phi : \mathbb{R} \to \mathbb{R}$ satisfy the three properties
(4.5.5)–(4.5.7):

1. $\phi(x) = 0$ for $x < 0$ and for $x > 3$;
2. the scaling equation
$$\phi(x) = \tfrac{1+\sqrt3}{4} \phi(2x) + \tfrac{3+\sqrt3}{4} \phi(2x-1) + \tfrac{3-\sqrt3}{4}
  \phi(2x-2) + \tfrac{1-\sqrt3}{4} \phi(2x-3) \quad \text{for all } x \in \mathbb{R};$$
3. $\phi(1) = (1+\sqrt3)/2$ and $\phi(2) = (1-\sqrt3)/2$.

Then $\phi(0) = \phi(3) = 0$, $\phi(1/2) = (2+\sqrt3)/4$, $\phi(3/2) = 0$ and
$\phi(1/4) = (5+3\sqrt3)/16$.

The values at the endpoints are not assumed. They follow from the scaling equation, because the
coefficients $(1+\sqrt3)/4$ and $(1-\sqrt3)/4$ of the two end terms are not $1$. The statement
does not assume that such a function exists; its existence is
`AtkinsonHan.Chapter04.equation_4_5_6`, and `AtkinsonHan.Chapter04.exists_daubechies_values`
combines the two.

**Generalization.** Continuity and exact support are unnecessary for the stated values.
Vanishing outside $[0,3]$ suffices with the refinement equation and normalization. -/
theorem exercise_4_5_5 {φ : ℝ → ℝ} (hsupp : ∀ x : ℝ, x < 0 ∨ 3 < x → φ x = 0)
    (hscal : ∀ x : ℝ, φ x = (1 + √3) / 4 * φ (2 * x) + (3 + √3) / 4 * φ (2 * x - 1)
      + (3 - √3) / 4 * φ (2 * x - 2) + (1 - √3) / 4 * φ (2 * x - 3))
    (hone : φ 1 = (1 + √3) / 2) (htwo : φ 2 = (1 - √3) / 2) :
    φ 0 = 0 ∧ φ 3 = 0 ∧ φ (1 / 2) = (2 + √3) / 4 ∧ φ (3 / 2) = 0 ∧
      φ (1 / 4) = (5 + 3 * √3) / 16 := by
  have hs3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs3lt : √3 < 3 := by nlinarith [Real.sqrt_nonneg 3]
  have hneg : ∀ x : ℝ, x < 0 → φ x = 0 := fun x hx => hsupp x (Or.inl hx)
  have hbig : ∀ x : ℝ, 3 < x → φ x = 0 := fun x hx => hsupp x (Or.inr hx)
  -- the endpoints, from the scaling equation alone
  have h0 : φ 0 = 0 := by
    have h := hscal 0
    rw [hneg ((2 : ℝ) * 0 - 1) (by norm_num), hneg ((2 : ℝ) * 0 - 2) (by norm_num),
      hneg ((2 : ℝ) * 0 - 3) (by norm_num), show (2 : ℝ) * 0 = 0 by norm_num] at h
    have hkey : ((3 - √3) / 4) * φ 0 = 0 := by linarith
    rcases mul_eq_zero.mp hkey with h' | h'
    · exact absurd h' (by intro hc; rw [div_eq_zero_iff] at hc; rcases hc with hc | hc <;> linarith)
    · exact h'
  have h3 : φ 3 = 0 := by
    have h := hscal 3
    rw [hbig ((2 : ℝ) * 3 - 1) (by norm_num), hbig ((2 : ℝ) * 3 - 2) (by norm_num),
      show (2 : ℝ) * 3 - 3 = 3 by norm_num, hbig ((2 : ℝ) * 3) (by norm_num)] at h
    have hkey : ((3 + √3) / 4) * φ 3 = 0 := by linarith
    rcases mul_eq_zero.mp hkey with h' | h'
    · exact absurd h' (by
        intro hc
        rw [div_eq_zero_iff] at hc
        rcases hc with hc | hc <;> nlinarith [Real.sqrt_nonneg 3])
    · exact h'
  -- the book's worked value at `1/2`, and Exercise 4.5.5
  have hhalf : φ (1 / 2) = (2 + √3) / 4 := by
    have h := hscal (1 / 2)
    rw [show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num,
      hneg ((2 : ℝ) * (1 / 2) - 2) (by norm_num), hneg ((2 : ℝ) * (1 / 2) - 3) (by norm_num),
      show (2 : ℝ) * (1 / 2) = 1 by norm_num, hone, h0] at h
    rw [h]
    linear_combination hs3 / 8
  refine ⟨h0, h3, hhalf, ?_, ?_⟩
  · have h := hscal (3 / 2)
    rw [show (2 : ℝ) * (3 / 2) - 1 = 2 by norm_num, show (2 : ℝ) * (3 / 2) - 2 = 1 by norm_num,
      show (2 : ℝ) * (3 / 2) - 3 = 0 by norm_num, show (2 : ℝ) * (3 / 2) = 3 by norm_num,
      h3, htwo, hone, h0] at h
    rw [h]
    linear_combination -hs3 / 4
  · have h := hscal (1 / 4)
    rw [hneg ((2 : ℝ) * (1 / 4) - 1) (by norm_num), hneg ((2 : ℝ) * (1 / 4) - 2) (by norm_num),
      hneg ((2 : ℝ) * (1 / 4) - 3) (by norm_num), show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num,
      hhalf] at h
    rw [h]
    linear_combination hs3 / 16

/-- **Exercise 4.5.6** of [han2009theoretical], the inclusion of the support. Let
$\phi : \mathbb{R} \to \mathbb{R}$ vanish outside $[0, 3]$, and let $\psi$ be the Daubechies
wavelet (4.5.8),
$$\psi(x) = -\tfrac{1+\sqrt3}{4} \phi(2x-1) + \tfrac{3+\sqrt3}{4} \phi(2x) - \tfrac{3-\sqrt3}{4}
  \phi(2x+1) + \tfrac{1-\sqrt3}{4} \phi(2x+2).$$
Then $\psi(x) = 0$ for $x < -1$ and for $x > 2$, so the support of $\psi$ is contained in
$[-1, 2]$.

The statement holds for every $\phi$ that vanishes outside $[0, 3]$. The book asks for the
equality $\operatorname{supp} \psi = [-1, 2]$. This is a statement about the $D_4$ function, and
it needs the counterpart for $\psi$ of `Daubechies.scalingFun_support`: that $\psi$ does not
vanish identically on any nondegenerate subinterval of $[-1, 2]$. The equality is not proved.

**Reading.** The declaration proves only inclusion of the topological support. The reverse
inclusion for the specific Daubechies wavelet is not stated. -/
theorem exercise_4_5_6_subset {φ ψ : ℝ → ℝ} (hsupp : ∀ x : ℝ, x < 0 ∨ 3 < x → φ x = 0)
    (hpsi : ∀ x : ℝ, ψ x = -((1 + √3) / 4) * φ (2 * x - 1) + (3 + √3) / 4 * φ (2 * x)
      - (3 - √3) / 4 * φ (2 * x + 1) + (1 - √3) / 4 * φ (2 * x + 2))
    {x : ℝ} (hx : x < -1 ∨ 2 < x) : ψ x = 0 := by
  rcases hx with hx | hx
  · rw [hpsi, hsupp (2 * x - 1) (Or.inl (by linarith)), hsupp (2 * x) (Or.inl (by linarith)),
      hsupp (2 * x + 1) (Or.inl (by linarith)), hsupp (2 * x + 2) (Or.inl (by linarith))]
    ring
  · rw [hpsi, hsupp (2 * x - 1) (Or.inr (by linarith)), hsupp (2 * x) (Or.inr (by linarith)),
      hsupp (2 * x + 1) (Or.inr (by linarith)), hsupp (2 * x + 2) (Or.inr (by linarith))]
    ring

/-- **Equations (4.5.5)–(4.5.7)** of [han2009theoretical], existence of the Daubechies scaling
function $D_4$. There is a continuous function $\phi : \mathbb{R} \to \mathbb{R}$ such that

1. $\phi(x) = 0$ for $x < 0$ and for $x > 3$, and the support of $\phi$ (the closure of
   $\{x : \phi(x) \ne 0\}$) is exactly $[0, 3]$;
2. $\phi$ satisfies the scaling equation
$$\phi(x) = \tfrac{1+\sqrt3}{4} \phi(2x) + \tfrac{3+\sqrt3}{4} \phi(2x-1) + \tfrac{3-\sqrt3}{4}
  \phi(2x-2) + \tfrac{1-\sqrt3}{4} \phi(2x-3) \quad \text{for all } x \in \mathbb{R};$$
3. $\phi(1) = (1+\sqrt3)/2$ and $\phi(2) = (1-\sqrt3)/2$.

The book introduces this function by these three properties and computes its values from them
(`AtkinsonHan.Chapter04.exercise_4_5_5`). The existence is Daubechies' theorem, which the book
states without proof. The backbone `Numlib.Analysis.Wavelet.Daubechies` proves it by the cascade
iteration. The convergence of the iteration rests on an explicit bound for the joint spectral
radius of the two matrices of this mask, and the exact support follows from the injectivity of
their transposes. -/
theorem equation_4_5_6 :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ (∀ x : ℝ, x < 0 ∨ 3 < x → φ x = 0) ∧
      closure (Function.support φ) = Set.Icc 0 3 ∧
      (∀ x : ℝ, φ x = (1 + √3) / 4 * φ (2 * x) + (3 + √3) / 4 * φ (2 * x - 1)
        + (3 - √3) / 4 * φ (2 * x - 2) + (1 - √3) / 4 * φ (2 * x - 3)) ∧
      φ 1 = (1 + √3) / 2 ∧ φ 2 = (1 - √3) / 2 :=
  Daubechies.exists_scalingFun

/-- **Exercise 4.5.5** of [han2009theoretical], for the Daubechies scaling function. There is a
continuous function $\phi : \mathbb{R} \to \mathbb{R}$ with support exactly $[0, 3]$ that
satisfies the scaling equation and the normalization of (4.5.5)–(4.5.7), and this function has
the values
$$\phi(0) = \phi(3) = 0, \quad \phi(1/2) = \frac{2+\sqrt3}{4}, \quad \phi(3/2) = 0, \quad
  \phi(1/4) = \frac{5+3\sqrt3}{16}.$$

The statement combines `AtkinsonHan.Chapter04.equation_4_5_6` with
`AtkinsonHan.Chapter04.exercise_4_5_5`, so the values of the exercise hold for a function that
exists. -/
theorem exists_daubechies_values :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ closure (Function.support φ) = Set.Icc 0 3 ∧
      (∀ x : ℝ, φ x = (1 + √3) / 4 * φ (2 * x) + (3 + √3) / 4 * φ (2 * x - 1)
        + (3 - √3) / 4 * φ (2 * x - 2) + (1 - √3) / 4 * φ (2 * x - 3)) ∧
      φ 1 = (1 + √3) / 2 ∧ φ 2 = (1 - √3) / 2 ∧
      φ 0 = 0 ∧ φ 3 = 0 ∧ φ (1 / 2) = (2 + √3) / 4 ∧ φ (3 / 2) = 0 ∧
      φ (1 / 4) = (5 + 3 * √3) / 16 := by
  obtain ⟨φ, hcont, hsupp, hclos, hscal, hone, htwo⟩ := equation_4_5_6
  obtain ⟨h0, h3, hhalf, h32, h14⟩ := exercise_4_5_5 hsupp hscal hone htwo
  exact ⟨φ, hcont, hclos, hscal, hone, htwo, h0, h3, hhalf, h32, h14⟩

end AtkinsonHan.Chapter04
