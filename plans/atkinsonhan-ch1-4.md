<!--
The tracker plan (the TOML group files beside this document) is the authority on which declarations
should exist, and the source is the authority on what they say. What is worth reading here is the
book alignment: which numbered result maps to which declaration, how each book-specific definition
relates to the backbone, and what was deferred and why. The result-by-result coverage table lives
in `proposals/atkinsonhan-ch1-4.md`.
-->

# Surface plan: Atkinson–Han — Chapters 1–4

Source: Atkinson–Han, *Theoretical Numerical Analysis* (3rd ed.): Ch. 1 (linear spaces), §2.1–2.2
and §2.6–2.9 (the parts of the operator chapter the earlier plan left out), §3.1–3.2 and §3.5 (the
parts of the approximation chapter it left out), and Ch. 4 (Fourier analysis and wavelets). The
already-covered §2.3–2.5 and §3.3–3.7 are in `atkinsonhan-ch2-3.md`, which this document extends
rather than replaces; its conventions are kept.

New backbone modules: `Numlib/Analysis/Fourier/{TrigonometricBasis,Dirichlet,DFT}`,
`Numlib/Analysis/Wavelet/{Haar,Multiresolution}`, `Numlib/Analysis/Normed/Operator/Compact`,
`Numlib/Analysis/Convex/Uniform`, `Numlib/Approximation/{Unisolvent,Hermite,OrthogonalPolynomial}`.

---

## 1. Conventions, beyond those of `atkinsonhan-ch2-3.md`

* **Chapter 1 states results, not definitions.** The rule and its defence are in
  `proposals/atkinsonhan-ch1-4.md` §1 (b): every numbered Theorem, Proposition, Lemma and Corollary
  of the chapter gets a node; no Definition, Example or Exercise does. A surface `def IsNorm` would
  compete with `NormedAddCommGroup` for a future agent's attention and would win, because it
  carries the book's number.

* **`L²(-π, π)` is `L²(AddCircle (2π))`.** Chapters 1 and 4 speak of `L²(-π, π)` but always mean
  the `2π`-periodic extension: the Fourier coefficients (4.1.2)–(4.1.3), the partial sums, and
  Theorem 1.3.13's basis are all statements about periodic functions. Mathlib's whole Fourier
  apparatus lives on `AddCircle T` with the probability measure `haarAddCircle`, and translating
  each statement back to an interval would cost a bridge lemma per result and buy nothing. The
  backbone therefore works on `AddCircle T` and the surface reads that as the book's space, noting
  the identification once. The exception is `Numlib/Analysis/Fourier/Dirichlet`, which works with
  `f : ℝ → ℝ` periodic and interval-integrable, because Theorem 4.1.1's hypotheses are one-sided
  limits *at a real point* and are awkward to phrase on a circle.

* **Two Fourier normalisations, one bridge.** The book's transform is
  `f̂(ξ) = (2π)^{-d/2} ∫ f(x) e^{-i x·ξ} dx`; Mathlib's `𝓕` is `e^{-2πi x·ξ}` with no prefactor. The
  surface defines `bookFourier` and proves `bookFourier f ξ = (2π)^{-d/2} • 𝓕 f ((2π)⁻¹ • ξ)` once;
  every other §4.2 node goes through that lemma. Doing it the other way round — restating each
  Mathlib theorem in the book's normalisation from scratch — would multiply the same computation
  eight times.

* **The book's `V_j` is a span; the plan's is its closure.** In §4.4 Atkinson–Han define `V_j` as
  the set of *finite* linear combinations of the `φ(2^j x - k)`, and then say in the next paragraph
  that one may equally take the `ℓ²`-coefficient version. The second reading is the one under which
  Theorem 4.4.1 (1) ("orthonormal basis of `V_j`") and (5) (`⋂ V_j = {0}` in `L²`) are true as
  stated, so `Haar.V j` is the closed span, and the surface records the book's span as its dense
  subspace.

* **"Piecewise continuous" becomes interval integrability plus one-sided limits.** Theorem 4.1.1's
  hypothesis is a class of functions Lean has no idiom for. The backbone proves Dini's criterion,
  which is weaker than every hypothesis the book uses and is stated with integrability conditions
  only; the surface's `theorem_4_1_1` is its instance for a function with one-sided limits and
  one-sided derivatives at the point.

## 2. Book-specific definitions

Each entry: book formulation → surface or backbone object → equivalence.

1. **Bounded operator** (Def 2.1.6): `AtkinsonHan.Ch02.IsBoundedOperator T`, "bounded sets have
   bounded images". Not `‖T‖ < ∞`: the point of Theorem 2.2.4 is that for a *linear* operator the
   two agree, so the surface must be able to state both. Bridges:
   `isBoundedOperator_iff_image_bounded` (the book's two readings) and
   `isBoundedOperator_iff_exists_bound` (Proposition 2.2.3, linear case).

2. **Weak convergence** (Def 2.7.1): the existing `AtkinsonHan.Ch03.WeakSeqTendsto`, which §3.3
   introduced for Example 3.3.5. The declaration should move to §2.7, where the book puts it; see
   the proposal file. No Mathlib counterpart is used: `WeakSpace 𝕜 V` gives the topological version,
   and `tendsto_iff_forall_dual_apply_tendsto` is stated only for the weak operator topology.

3. **Compact operator** (Def 2.8.1): Mathlib's `IsCompactOperator`, with
   `isCompactOperator_iff_isCompact_closure_image_closedBall` for the book's "the image of the unit
   ball has compact closure" and a surface lemma for its sequential reading. Finite rank
   (Def 2.8.3) is `FiniteDimensional 𝕜 (LinearMap.range K)`.

4. **Resolvent set, spectrum, resolvent operator** (Def 2.9.1): Mathlib's `resolventSet`,
   `spectrum` and `resolvent`. No surface definition.

5. **Interpolation problem, linear independence of functionals over `Vₙ`** (Def 3.2.1): the
   backbone `Approximation.IsUnisolvent Vₙ L`, with `isUnisolvent_iff_linearIndependent` as the
   bridge to the book's phrasing. Chosen over "the functionals are linearly independent" as the
   primary form because unique solvability is what every consumer wants.

6. **Weighted `L²_w(-1, 1)`** (3.5.1): `Lp ℝ 2 ((volume.restrict (Ioo (-1) 1)).withDensity w)`; a
   surface abbreviation, no new structure. The orthogonal polynomials of the weight are the backbone
   `OrthogonalPolynomial.family` of that measure.

7. **Real Fourier coefficients `a_j`, `b_j`** (4.1.2)–(4.1.3): the backbone `realFourierCoeff`,
   indexed by `ℤ` so that one family covers the book's three (constant, cosines, sines), with
   `realFourierCoeff_cos` and `realFourierCoeff_sin` recovering the book's normalisation and
   `realFourierCoeff_eq_fourierCoeff` giving (4.1.6).

8. **Partial sum `S_N`** (§4.1, and (3.7.6)'s `𝓕_n`): the backbone `fourierPartialSum`. The Fourier
   *projection* `PeriodicCont.fourierProj` planned in `Numlib/Approximation/Trigonometric` is its
   restriction to `C_p(2π)`; the proposal file asks for that module to be written that way rather
   than defining a second Dirichlet kernel.

9. **The book's Fourier transform** (4.2.1)/(4.2.3): `AtkinsonHan.Ch04.bookFourier`, with the
   normalisation bridge of §1 above.

10. **Schwartz space, tempered distributions** (Def 4.2.1–4.2.3): Mathlib's `SchwartzMap`,
    `TemperedDistribution` and `TemperedDistribution.fourier`. No surface definition; the nodes are
    identifications.

11. **DFT matrix `F_n`** (§4.3): the backbone `Matrix.dft`, with `Matrix.dft_eq_zmodDft` bridging
    to Mathlib's `ZMod.dft`, from which the inversion theorem comes for free.

12. **Haar scaling function, scaling spaces, wavelet, wavelet spaces** (4.4.1)–(4.4.2): the
    backbone `Haar.scalingFun`, `Haar.V`, `Haar.waveletFun`, `Haar.W`, all in
    `Lp ℝ 2 (volume : Measure ℝ)`. The unitary dilation `MeasureTheory.Lp.dilationₗᵢ` is defined
    there too, because Mathlib has `Lp.compMeasurePreserving` and nothing for a scaling.

13. **Multiresolution analysis** (Def 4.5.1): the backbone `IsMultiresolutionAnalysis`, a structure
    whose five fields are the book's five clauses, with `Haar.isMultiresolutionAnalysis` as the
    instance.

## 3. Where the work is

Four nodes carry most of the effort of this slice; everything else is a specialization or an
elementary computation.

* **`tendsto_fourierPartialSum_of_dini`** (Theorem 4.1.1). The classical proof — write
  `S_n f x - L` as an integral against `sin((n + 1/2) t)` and apply Riemann–Lebesgue. The friction
  is that Mathlib's Riemann–Lebesgue lemma is for the Fourier integral over `ℝ`, so the interval
  form has to be obtained by extending by zero. Keep that reduction private.

* **`Haar.topologicalClosure_iSup_V`** (Theorem 4.4.1 (4)). Density of the dyadic step functions in
  `L²(ℝ)`. The route that works is *continuous compactly supported functions are dense* (Mathlib)
  and then uniform continuity, giving an explicit `L²` bound for the level-`j` step approximation.
  Do not go via measurable sets and approximation by dyadic unions; it is strictly harder and buys
  nothing.

* **`trigBasis`** (Theorem 1.3.13). The orthonormality is a computation; completeness is the point.
  Take it from `span_fourier_closure_eq_top` through `realFourierCoeff_eq_fourierCoeff` — a real
  `L²` function orthogonal to every `cos(jx)` and `sin(jx)` has all complex Fourier coefficients
  zero — and not from a second Stone–Weierstrass argument.

* **`Hermite.exists_iteratedDeriv_eq_zero`** (the Hermite error formula). Rolle with
  multiplicities, by induction on the order, counting the zeros of `g'`. It strengthens the
  `exists_iteratedDeriv_eq_zero_of_forall_eq_zero` that `Numlib/Approximation/Interpolation` already
  plans for the Lagrange case.

Two more are moderate: `IsCompactOperator.adjoint` (Schauder, via Arzelà–Ascoli — see the module
description for the route that avoids the approximation property) and
`OrthogonalPolynomial.three_term_recurrence` together with the Legendre orthogonality, which is
`n`-fold integration by parts on the Rodrigues formula.

## 4. What Mathlib already had, and how much it saved

Worth recording, because the earlier plan assumed otherwise for Chapter 4:

| Book | Mathlib |
|---|---|
| Thm 2.6.5, `‖L‖ = sup_{‖v‖=1} |(Lv, v)|` | `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient` |
| Thm 2.8.10, the Fredholm alternative | `IsCompactOperator.hasEigenvalue_or_mem_resolventSet` |
| Thm 2.8.12 (2) | `ContinuousLinearMap.finite_dimensional_eigenspace` |
| Thm 2.8.15 | `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` |
| Lem 2.9.2 (qualitative half) | `spectrum.isOpen_resolventSet`, `spectrum.hasDerivAt_resolvent` |
| Thm 3.1.1, Thm 3.1.2 | `polynomialFunctions_closure_eq_top`, `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints` |
| Def 4.2.1, (4.2.9) | `SchwartzMap`, `SchwartzMap.fourierTransformCLE` |
| Def 4.2.2, Def 4.2.3, (4.2.13) | `TemperedDistribution`, `TemperedDistribution.fourier` |
| (4.2.4), (4.2.11) | `MeasureTheory.Integrable.fourierInv_fourier_eq` |
| Thm 4.2.4, Plancherel | `MeasureTheory.Lp.fourierTransformₗᵢ`, `Lp.norm_fourier_eq` |
| Thm 4.3.2 | `ZMod.dft_dft` |
| Thm 1.6.3, Arzelà–Ascoli | `Mathlib.Topology.UniformSpace.Ascoli` |

What Mathlib does **not** have, and which is therefore the backbone content of this slice: the real
trigonometric system, the Dirichlet kernel and pointwise convergence, the DFT in matrix form and
the radix-2 identity, the whole Haar system, the elementary closure properties of compact operators
and Schauder's theorem, the Radon–Riesz property, the abstract interpolation problem, Hermite
interpolation, and the orthogonal polynomials of a measure with the Legendre and Chebyshev
families.

## 5. Left out

The skip list, with obstructions, is in `proposals/atkinsonhan-ch1-4.md` §4. In one line each, the
seven that a reader of the book will miss: reflexivity and weak sequential compactness (Thm 2.7.5,
and with it Thm 3.3.8–3.3.14, already recorded in `Numlib/Variational/Minimization`); the Riesz
ascent–descent theory (Thm 2.8.12 (3), (5), Thm 2.8.14 (1)); the holomorphic functional calculus
and the Riesz spectral projection (Thm 2.9.3, Thm 2.9.4); Müntz's theorem (Thm 3.1.5); the M. Riesz
theorem behind (4.1.12) for `p ≠ 2`; the Fourier-side construction of general wavelets (§4.5 after
Prop 4.5.2); and the weakly singular kernels of §2.8.1.
