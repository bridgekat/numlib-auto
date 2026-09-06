# Proposal: Atkinson–Han, Chapters 1–4

Everything the plan for Atkinson–Han, *Theoretical Numerical Analysis* (3rd ed.), Chapters 1–4
needed that could not go into a new TOML group of its own. The plan itself is in the twelve new
backbone groups and the fifteen new surface groups listed at the end, and the reasoning is in
`plans/atkinsonhan-ch1-4.md`.

`lake exe tracker lint` prints `ok` with all of it in place.

---

## 1. The three things that matter most

**(a) Chapter 4 is not out of scope, and `backbone.md` §0.2 says it is.** That section reads
"Ch. 4, 7, 10, 13–14 (Fourier, Sobolev, FEM, BIE) are out of scope until Mathlib has Sobolev
spaces". Nothing in Chapter 4 uses a Sobolev space. It uses `L¹`, `L²`, the Schwartz space,
tempered distributions and the Fourier transform, and Mathlib now has all of them —
`SchwartzMap`, `SchwartzMap.fourierTransformCLE`, `TemperedDistribution` (`𝓢'(E, F)`) with
`TemperedDistribution.fourier`, `MeasureTheory.Lp.fourierTransformₗᵢ` (Plancherel, a linear
isometry equivalence), `MeasureTheory.Integrable.fourierInv_fourier_eq` (inversion), and
`ZMod.dft` with `ZMod.dft_dft`. §4.2 and §4.3 are therefore *thin*: the whole of §4.2 is a
normalisation bridge (`bookFourier_eq_fourierIntegral`) plus eight restatements, and §4.3 is
`ZMod.dft` in matrix clothes plus one new theorem. §4.1 and §4.4 need real backbone work, but of a
kind the project already does. **Requested**: amend `backbone.md` §0.2 to read "Ch. 7, 10, 13–14
(Sobolev, FEM, BIE) are out of scope until Mathlib has Sobolev spaces; Ch. 4 is phase 3", and
strike "distribution theory" from the out-of-scope bullet of §1.7, which is now false.

**(b) Chapter 1 should be stated, and only its numbered results.** Nearly all of Chapter 1 is
Mathlib, so a surface node for it specializes Mathlib rather than `Numlib`, which the README's
"a surface proof that did not specialize anything" clause could be read to forbid. The position
taken here, and the reason: that clause exists to stop *new mathematics* appearing in a surface,
not to stop a surface naming a result the book numbers. Chapter 1 contains no numerical analysis —
it is the book's functional-analysis review — so "specializing the backbone" is not available and
is not the right test. The right test is whether the node is worth a Lean name, and the rule
adopted is mechanical and auditable:

* **state every numbered Theorem, Proposition, Lemma and Corollary** of Chapter 1 (22 nodes,
  most of them one-liners);
* **state no Definition, Example or Exercise.** A surface `def IsNorm` or `def IsCauchySeq` would
  carry no information and would invite a future agent to use it in place of
  `NormedAddCommGroup` or `CauchySeq` — the single worst outcome this plan can produce. §1.4 has
  no numbered result at all and gets no group.

The chapter is not free of content under this rule: Theorem 1.3.13, the *real* trigonometric
orthonormal basis of `L²(-π, π)`, is not in Mathlib in any form (Mathlib has the complex
exponentials, `fourierBasis`), it is the backbone node `trigBasis`, and Chapter 4 uses it four
times. Theorem 1.2.14 also needs a decision Lean forces: two norms on one type cannot be
quantified over, so it is stated for two normed types and a linear equivalence between them.

**(c) The Riesz ascent–descent theory is the one real gap of Chapter 2, and it is not planned.**
Mathlib's Fredholm alternative (`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`) is exactly
Theorem 2.8.10, and the compact self-adjoint spectral theorem
(`orthogonalComplement_iSup_eigenspaces_eq_bot`, `finite_dimensional_eigenspace`) is most of
Theorem 2.8.15. What is missing is Theorem 2.8.12 (3), (5) — the chain
`N(λ-K) ⊊ N((λ-K)²) ⊊ ⋯` stabilises at a finite index and `V = N((λ-K)^ν) ⊕ R((λ-K)^ν)` — and
Theorem 2.8.14 (1), `dim N(λ-K) = dim N(λ̄-K*)`. That is a development of its own, the book states
it without proof, and its only consumers in the corpus are Theorem 2.9.4 (the Riesz spectral
projection, which needs contour integrals of operator-valued functions and is already out of scope
by `backbone.md` §1.7) and §2.8.5's remarks. Clauses (1), (2) and (4) of Theorem 2.8.12 and
clause (2) of Theorem 2.8.14 *are* planned, in `Numlib/Analysis/Normed/Operator/Compact`, because
they are short and because Chapter 12's projection methods for `I - K` will need the closed range.

---

## 2. Additions to existing groups

| Group | Node | Kind | Description | Deps | Why here |
|---|---|---|---|---|---|
| `NumlibSurface/AtkinsonHan/Chapter03/Section03` | `WeakSeqTendsto` | definition | Weak sequential convergence, `∀ ℓ : StrongDual 𝕜 V, Tendsto (fun n => ℓ (v n)) atTop (𝓝 (ℓ u))`. The declaration exists and is used by `example_3_3_5`; it is simply not a node, and `plans/README.md` says a surface's book-specific definitions are nodes. §2.7's three nodes want it in their `deps`. | — | It is already in that module; adding the node is bookkeeping. Better still, move the declaration to the new `Chapter02/Section07`, where the book puts it (Definition 2.7.1), and have §3.3 import it — see §3 below. |
| `NumlibSurface/AtkinsonHan/Chapter03/Section03` | `AreSeparated`, `AreStrictlySeparated`, `IsCoerciveFunctionalOn`, `IsStrictlyNormed`, `polyLE`, `rho` | definition | The other five book-specific definitions the module's own doc comment lists, none of which is a node today. | — | Same rule: the surface's vocabulary for the book is what a plan names. |
| `Numlib/Analysis/Normed/Module/WeakDual` | `bddAbove_range_norm_of_weak_tendsto` | theorem | A weakly convergent sequence in a normed space is bounded (Atkinson–Han Prop 2.7.2): uniform boundedness applied to its image in the double dual, then `NormedSpace.inclusionInDoubleDualLi`. | `norm_le_liminf_norm_of_weak_tendsto` | The proof already exists as the **private** `AtkinsonHan.Chapter03.exists_norm_le_of_weakSeqTendsto`; §2.7 needs it as a theorem with a book number, and the module's own description already says the weak-convergence lemmas proved in the surface move here in phase 2. |
| `Numlib/IntegralEquations/Basic` | `IntegralOperator.isCompactOperator_fredholm` | theorem | The Fredholm operator with a continuous kernel is a compact operator on `C(Icc a b, ℝ)` (Atkinson–Han §2.8.1 in the continuous-kernel case): the image of the unit ball is bounded and equicontinuous by uniform continuity of `k`, so Arzelà–Ascoli applies. | `IntegralOperator.fredholm`, `IntegralOperator.norm_fredholm` | Every object it mentions is in that module already, and Chapter 12's projection methods for `I - K` will need it. The weakly singular kernels of Atkinson–Han's (A₁)–(A₂) are **not** requested — see §4. |
| `Numlib/Approximation/Interpolation` | (amend `piecewiseLinearInterpCLM`) | — | Add the modulus-of-continuity bound `‖f - Π f‖_∞ ≤ ω(f, h)` for merely continuous `f`, Atkinson–Han (3.2.8), beside the `h²/8 ‖f''‖` bound the node already promises for `C²` functions. | — | (3.2.8) is the bound §3.2.3 states first, and it is one line from the definition. |
| `Numlib/Approximation/Interpolation` | (amend `trigInterpCLM`) | — | Note that the unique solvability of trigonometric interpolation at `2n+1` distinct nodes is `Approximation.IsUnisolvent` transported along `z = e^{ix}`, and add `Approximation.isUnisolvent_tfae` to its `deps`. | `Approximation.isUnisolvent_tfae` | The abstract framework is now available; otherwise that module re-proves it. |
| `Numlib/Approximation/Trigonometric` | (amend `PeriodicCont.fourierProj`) | — | Define the Fourier projection as `fourierPartialSum` of `Numlib/Analysis/Fourier/Dirichlet` restricted to `C_p(2π)`, and take (3.7.6)–(3.7.8) from `dirichletKernel`, `dirichletKernel_eq_sin_div` and `fourierPartialSum_eq_integral` rather than restating them. Add those to its `deps`. | `dirichletKernel`, `fourierPartialSum`, `fourierPartialSum_eq_integral` | Two modules would otherwise each define the Dirichlet kernel. §4.1 needs it for `L¹` functions, §3.7 for continuous ones; one definition, two consumers. |
| `Numlib/Approximation/Quadrature` | (amend `exists_gauss`) | — | Build the Gauss rule on `OrthogonalPolynomial.family` and `OrthogonalPolynomial.three_term_recurrence` of the new `Numlib/Approximation/OrthogonalPolynomial`, rather than on `Polynomial.christoffel_darboux` alone. | `OrthogonalPolynomial.family`, `OrthogonalPolynomial.integral_family_mul_family` | `Polynomial.christoffel_darboux` is the *algebraic* identity for a given recurrence; the orthogonal polynomials of a measure, which is what a Gauss rule needs, had no home before. |
| `NumlibSurface/AtkinsonHan/Chapter03/Section07` | (amend `theorem_3_7_3`) | — | Add `OrthogonalPolynomial.three_term_recurrence` to its `deps`, so that the Christoffel–Darboux hypothesis is discharged for the families §3.7 applies it to rather than assumed. | `OrthogonalPolynomial.three_term_recurrence` | Otherwise the surface theorem is conditional on an unverifiable hypothesis. |

Group descriptions to refresh (they name section ranges that are now too narrow):

* `NumlibSurface/AtkinsonHan/Chapter02.toml`: "§2.3–2.5" → "§2.1–2.9".
* `NumlibSurface/AtkinsonHan/Chapter03.toml`: "§3.3–3.7" → "§3.1–3.7".
* `NumlibSurface/AtkinsonHan.lean`: the module doc says "nineteen modules" and its outline table
  starts at §2.3. With this plan it becomes thirty-four modules spanning §1.1–9.4; the table needs
  the new rows. (A Lean file, so not edited here.)

---

## 3. Changes to existing declarations

1. **`AtkinsonHan.Chapter03.exists_norm_le_of_weakSeqTendsto` is `private`.** It is Atkinson–Han
   Proposition 2.7.2 — a numbered result of the book — proved as a helper for Example 3.3.5.
   Make it public and move it to the backbone as
   `bddAbove_range_norm_of_weak_tendsto` (§2 above); `AtkinsonHan.Chapter02.proposition_2_7_2` is then
   its restatement under the book's number, and §3.3 keeps working unchanged.

2. **`AtkinsonHan.Chapter03.WeakSeqTendsto` is in the wrong section.** It is Definition 2.7.1, not a
   §3.3 definition; §3.3 needed it first only because §2.7 was not planned. Move the declaration to
   `NumlibSurface/AtkinsonHan/Chapter02/Section07.lean` and have `Chapter03/Section03.lean` import
   it. The name does not change, so nothing downstream breaks; the tracker sees a module move, which
   `lint` reports and which is fixed by editing the group the node sits in.

3. **`Numlib/Approximation/Trigonometric`'s `jackson_trig` lists `PeriodicCont.fourierProj` as a
   dependency.** Jackson's theorem bounds the *best* trigonometric approximation and does not
   mention the Fourier projection; the dependency is spurious and should be dropped when that
   module is written (the convolution there is with the Jackson kernel, not the Dirichlet kernel).

4. **`backbone.md` §0.2 and §1.7**, as in §1 (a) above: Chapter 4 is not blocked on Sobolev spaces,
   and distribution theory is no longer absent from Mathlib. A new §11 recording the Fourier,
   wavelet and interpolation layers has been appended to `backbone.md`.

---

## 4. Not planned, and why

Chapter 1

* Definitions 1.1.1–1.1.16, 1.2.1–1.2.24, 1.3.1–1.3.10, 1.6.1 and all of §1.4 — restating
  `Module`, `NormedAddCommGroup`, `InnerProductSpace`, `IsCompact` and the Hölder classes under
  book numbers would add names without adding content, and would compete with Mathlib's.
* Examples 1.1.2–1.3.17 and Exercises 1.1.1–1.6.5 — illustrations; none is cited by a result in
  scope. Example 1.3.14 (the cosine basis of `L²(0, π)`) is the one with mathematical content, and
  it is a corollary of `trigBasis` that no other result uses.
* §1.5's Clarkson inequalities (1.5.5)–(1.5.6) — not in Mathlib; their only consumer is Exercise
  2.7.4 (b), that `Lᵖ` is uniformly convex, which is also not planned.
* Example 1.2.28 (b), Example 1.3.7 — Sobolev spaces `W^{m,p}`, `Hᵐ`.

Chapter 2

* Examples 2.1.2–2.1.7 — the differentiation operator on `C¹[0,1]`, which Mathlib does not have as
  a normed space, and which carries no theorem the book later uses.
* §2.7 Definition 2.7.4 and **Theorem 2.7.5** (a Banach space is reflexive iff bounded sequences
  have weakly convergent subsequences) — Eberlein–Šmulian plus Kakutani. Mathlib has neither
  reflexivity as a class nor Banach–Alaoglu in the needed form. This is the same obstruction
  already recorded for Theorems 3.3.8, 3.3.10–3.3.12 and 3.3.14 in
  `Numlib/Variational/Minimization`; §2.7 is where the book states it.
* §2.7's Dunford–Pettis criterion for `L¹` and Definition 2.7.6 (the book's idiosyncratic
  "strong" and "weak-\*" convergence of operators, which are norm and pointwise convergence) —
  the first needs uniform integrability theory, the second is a naming convention.
* §2.8.1 (A₁)–(A₂) and Examples 2.8.2, 2.8.9, 2.8.16 — compactness of integral operators with
  *weakly singular* kernels (`log|cos x - cos y|`, `|x-y|^{-γ}`, the single-layer kernel on the
  sphere). The continuous-kernel case is requested in §2 above; the weakly singular case needs the
  `ω(h) → 0` machinery of (2.8.3)–(2.8.8) and has no consumer in the corpus until Chapter 13.
* §2.8.3 — the `L²` kernel bound `‖K‖ ≤ B`; it is Example 2.6.1 with a name.
* **Theorem 2.8.12 (3), (5)** and **Theorem 2.8.14 (1)** — the Riesz ascent–descent theory, as in
  §1 (c).
* §2.9's classification of the spectrum into point, continuous and residual parts — a definition
  with no theorem attached in the book.
* **Theorems 2.9.3 and 2.9.4** — the multiplicativity of the holomorphic functional calculus and
  the Riesz spectral projection `E(λ₀, L) = (2πi)⁻¹ ∮ (λ - L)⁻¹ dλ`. Both are stated without proof
  in the book; both need contour integrals of `𝓛(V)`-valued functions, which `backbone.md` §1.7
  already lists as out of scope, and Theorem 2.9.4 needs the ascent–descent theory as well.

Chapter 3

* **Theorem 3.1.5 (Müntz)** — the Müntz–Szász theorem is not in Mathlib, its proof is a project of
  its own, and nothing else in the corpus uses it.
* §3.2.3's `H²(a, b)` estimates (3.2.10)–(3.2.12) — Sobolev spaces.
* (3.2.5), the divided-difference form of the interpolation error, and the Newton form of the
  interpolant — the book only cites them; no consumer.
* Example 3.2.5 and Table 3.1 — a numerical illustration.
* §3.5's `Hˢ(-1, 1)` error estimates for `P_N u` and `P_{1,N} u` after (3.5.2) and (3.5.7) —
  Sobolev spaces, and the book refers the reader elsewhere for them.

Chapter 4

* Examples 4.1.3–4.1.5 and the **Gibbs phenomenon** — Fourier series of a step function, of
  `|x|/π` and of `(π² - x²)²/π⁴`, drawn rather than proved; the Gibbs constant `(2/π) Si(π)` is
  asserted with a reference.
* (4.1.12) for `1 < p < ∞` — the uniform `Lᵖ` boundedness of the partial-sum operators is the
  M. Riesz theorem (equivalently, boundedness of the conjugate function). Not in Mathlib. Theorem
  4.1.2 itself, which is the *equivalence*, is planned, and its `p = 2` instance is unconditional.
* Definition 4.2.2's general theory of tempered distributions beyond what the transform needs, and
  the `Lᵖ` transform for `p ∉ {1, 2}` — the book only remarks that Definition 4.2.3 covers them.
* The FFT algorithm and its `O(n log n)` cost — algorithmic, with no theorem content beyond
  (4.3.8)–(4.3.9), which *is* planned as `Matrix.dft_radix_two`.
* **§4.5 beyond Definition 4.5.1 and Proposition 4.5.2**: the construction of a scaling function
  from dilation coefficients, the claim that the `ψ` of (4.5.4) generates the wavelet spaces, the
  four listed properties of the `W_j` of a general multiresolution analysis, the fixed-point
  computation of `φ`, and the Daubechies example (4.5.5)–(4.5.6). The book states every one of
  them without proof and refers to Daubechies; the standard arguments run through conditions on
  `φ̂` and need a piece of harmonic analysis Mathlib does not have. This is the only part of
  Chapter 4 that is genuinely out of reach.
* The stable-basis weakening of axiom (1) of Definition 4.5.1 — the book only remarks that one can
  renormalise to the orthonormal case.

---

## 5. Coverage summary

`P` = newly planned (node id given), `M` = already provable directly and planned as a node whose
proof is a Mathlib specialization, `D` = done (declaration exists), `S` = skipped (reason in §4).
Every numbered Theorem, Proposition, Lemma and Corollary of Chapters 1–4 appears; Definitions,
Examples and Exercises appear only when they are planned or when §4 records a decision about them.

### Chapter 1 — Linear Spaces (22 planned, 0 skipped)

| Result | State | Node |
|---|---|---|
| Thm 1.1.10 (dimension well defined) | P/M | `AtkinsonHan.Chapter01.theorem_1_1_10` |
| Prop 1.2.10 (norm continuous), (1.2.5) | P/M | `AtkinsonHan.Chapter01.proposition_1_2_10` |
| Thm 1.2.14 (norms equivalent in finite dim) | P | `AtkinsonHan.Chapter01.theorem_1_2_14` |
| Prop 1.2.23 (Cauchy + convergent subsequence) | P/M | `AtkinsonHan.Chapter01.proposition_1_2_23` |
| Thm 1.2.25 (completion) | P/M | `AtkinsonHan.Chapter01.theorem_1_2_25` |
| Thm 1.2.26 (dominated convergence) | P/M | `AtkinsonHan.Chapter01.theorem_1_2_26` |
| Thm 1.2.27 (Fubini) | P/M | `AtkinsonHan.Chapter01.theorem_1_2_27` |
| Thm 1.3.2 (Cauchy–Schwarz + equality case) | P/M | `AtkinsonHan.Chapter01.theorem_1_3_2` |
| Prop 1.3.3 (inner product continuous) | P/M | `AtkinsonHan.Chapter01.proposition_1_3_3` |
| Thm 1.3.4 (parallelogram law) | P/M | `AtkinsonHan.Chapter01.theorem_1_3_4` |
| Thm 1.3.11 (Bessel) | P/M | `AtkinsonHan.Chapter01.theorem_1_3_11` |
| Thm 1.3.12 (Parseval, ONB criteria) | P/M | `AtkinsonHan.Chapter01.theorem_1_3_12` |
| **Thm 1.3.13 (real trigonometric ONB)** | **P** | `AtkinsonHan.Chapter01.theorem_1_3_13`, backbone `trigBasis`, `trigFun`, `orthonormal_trigFun`, `realFourierCoeff`, `realFourierCoeff_eq_fourierCoeff`, `hasSum_trigSeries`, `tsum_sq_realFourierCoeff` |
| Thm 1.3.16 (Gram–Schmidt) | P/M | `AtkinsonHan.Chapter01.theorem_1_3_16` |
| §1.4 (no numbered result) | — | no group |
| Lem 1.5.1–1.5.4 (Young, Hölder, Minkowski) | P/M | `AtkinsonHan.Chapter01.lemma_1_5_1` … `lemma_1_5_4` |
| Thm 1.5.5 (a)(b)(c) | P/M | `AtkinsonHan.Chapter01.theorem_1_5_5` (three declarations) |
| Thm 1.5.6 (`C₀^∞` dense in `Lᵖ`) | P/M | `AtkinsonHan.Chapter01.theorem_1_5_6` |
| Thm 1.6.2 (Heine–Borel) | P/M | `AtkinsonHan.Chapter01.theorem_1_6_2` |
| Thm 1.6.3 (Arzelà–Ascoli) | P/M | `AtkinsonHan.Chapter01.theorem_1_6_3` |
| Clarkson (1.5.5)–(1.5.6) | S | not in Mathlib; only consumer is Ex 2.7.4 (b) |

### Chapter 2 — Linear Operators on Normed Spaces (32 newly planned, 22 done, 8 skipped)

| Result | State | Node |
|---|---|---|
| Def 2.1.6 (bounded operator) | P | `AtkinsonHan.Chapter02.IsBoundedOperator` |
| Prop 2.2.2, Prop 2.2.3, Thm 2.2.4 | P | `proposition_2_2_2`, `proposition_2_2_3`, `theorem_2_2_4` |
| Thm 2.2.5 (`𝓛(V,W)` normed), Thm 2.2.6 | P/M | `theorem_2_2_5`, `theorem_2_2_6` |
| Ex 2.2.8 (matrix `p`-norms) | P | `example_2_2_8` |
| Ex 2.2.9, (2.2.8) (integral operator norm) | P | `equation_2_2_8` → `IntegralOperator.norm_fredholm` |
| Thm 2.2.10 (`𝓛(V,W)` Banach) | P/M | `theorem_2_2_10` |
| Thm 2.3.1–2.3.5, §2.4, §2.5 | D | 22 declarations, unchanged |
| (2.6.1)–(2.6.4), Ex 2.6.1 | P/M | `equation_2_6_1`, `equation_2_6_3`, `equation_2_6_4` |
| Prop 2.6.2, Prop 2.6.3, Cor 2.6.4 | P/M | `proposition_2_6_2`, `proposition_2_6_3`, `corollary_2_6_4` |
| Thm 2.6.5 (`‖L‖ = sup |(Lv,v)|`) | P/M | `theorem_2_6_5` (Mathlib `norm_eq_iSup_rayleighQuotient`) |
| Prop 2.7.2 (weak ⇒ bounded) | P | `proposition_2_7_2`; backbone request in §2 |
| Ex 2.7.3 (Riemann–Lebesgue), Ex 2.7.2 | P | `example_2_7_3`, `exercise_2_7_2` |
| Ex 2.7.3/2.7.4 (a)(c) (Radon–Riesz) | P | `exercise_2_7_4`; backbone `tendsto_of_forall_dual_tendsto_of_tendsto_norm`, `tendsto_of_forall_inner_tendsto_of_tendsto_norm` |
| **Def 2.7.4, Thm 2.7.5 (reflexivity)** | **S** | Eberlein–Šmulian + Kakutani; not in Mathlib |
| Ex 2.7.4 (b) (`Lᵖ` uniformly convex) | S | Clarkson |
| Def 2.7.6, Dunford–Pettis | S | naming convention; uniform integrability |
| Def 2.8.1, Def 2.8.3 | P | `definition_2_8_1` |
| Prop 2.8.4, Prop 2.8.6, Prop 2.8.7 | P | `proposition_2_8_4/6/7`; backbone `IsCompactOperator.of_finiteDimensional_range`, `IsCompactOperator.of_tendsto` |
| §2.8.1 (A₁)–(A₂), Ex 2.8.2, 2.8.9, 2.8.16 | S | weakly singular kernels; continuous case requested in §2 |
| §2.8.3 (`L²` kernel bound) | S | = Example 2.6.1 |
| **Thm 2.8.10 (Fredholm alternative)** | P/M | `theorem_2_8_10` (Mathlib `hasEigenvalue_or_mem_resolventSet`) |
| Thm 2.8.12 (1), (2), (4) | P | `theorem_2_8_12`; backbone `IsCompactOperator.finite_setOf_hasEigenvalue_norm_le`, `.isClosed_range_smul_sub` |
| Thm 2.8.12 (3), (5) | S | Riesz ascent–descent |
| Lem 2.8.13 (Schauder) | P | `lemma_2_8_13`; backbone `IsCompactOperator.adjoint` |
| Thm 2.8.14 (2) | P | `theorem_2_8_14`; backbone `IsCompactOperator.range_smul_sub_eq_orthogonal_ker_adjoint` |
| Thm 2.8.14 (1) | S | Riesz ascent–descent |
| Thm 2.8.15 (compact self-adjoint spectral) | P/M | `theorem_2_8_15` (Mathlib `orthogonalComplement_iSup_eigenspaces_eq_bot`) |
| Def 2.9.1, Lem 2.9.2, (2.9.1)–(2.9.3) | P | `lemma_2_9_2`, `equation_2_9_3`, `spectrum_subset_closedBall` |
| **Thm 2.9.3, Thm 2.9.4** | **S** | holomorphic functional calculus; contour integrals of operator-valued functions |

### Chapter 3 — Approximation Theory (15 newly planned, 35 done, 24 open from the earlier plan, 5 skipped)

| Result | State | Node |
|---|---|---|
| Thm 3.1.1 (Weierstrass), Thm 3.1.2 (Stone–W.) | P/M | `AtkinsonHan.Chapter03.theorem_3_1_1`, `theorem_3_1_2` |
| Cor 3.1.3 (`ℝ^d` polynomials dense) | P | `corollary_3_1_3` |
| Cor 3.1.4 (trig polynomials dense) | P | `corollary_3_1_4` |
| **Thm 3.1.5 (Müntz)** | **S** | not in Mathlib, no consumer |
| Def 3.2.1, Lem 3.2.2, Thm 3.2.3 | P | `definition_3_2_1`, `lemma_3_2_2`, `theorem_3_2_3`; backbone `Approximation.IsUnisolvent`, `isUnisolvent_iff_det_ne_zero`, `isUnisolvent_tfae`, `IsUnisolvent.interpolate`, `haarCondition_iff_isUnisolvent` |
| (3.2.1)–(3.2.3) (Lagrange) | P | `equation_3_2_2` |
| Prop 3.2.4 (Lagrange error) | P | `proposition_3_2_4` → `Lagrange.exists_sub_interpolate_eq` |
| (3.2.5) (divided differences) | S | cited only |
| (3.2.6), general Hermite, its error | P | `equation_3_2_6`; backbone `Hermite.exists_iteratedDeriv_eq_zero`, `Hermite.isUnisolvent`, `Hermite.interpolate`, `Hermite.exists_sub_interpolate_eq` |
| (3.2.7)–(3.2.9) (piecewise linear) | P | `equation_3_2_9` → `piecewiseLinearInterpCLM` |
| (3.2.10)–(3.2.12) (`H²` estimates) | S | Sobolev spaces |
| (3.2.13)–(3.2.17) (trigonometric) | P | `equation_3_2_17` |
| §3.3, §3.4, §3.6, §3.7 | D / open | 35 proved, 24 open — earlier plan, unchanged |
| (3.5.1)–(3.5.2) (weighted `L²`, projection) | P | `equation_3_5_2`; backbone `OrthogonalPolynomial.family`, `.integral_family_mul_family`, `.three_term_recurrence`, `.isBestApprox_truncation` |
| (3.5.3)–(3.5.6) (Legendre) | P | `equation_3_5_5`; backbone `Polynomial.legendre`, `.integral_legendre_mul_legendre`, `.legendre_recurrence` |
| (3.5.8)–(3.5.9) (Chebyshev orthogonality) | P | `equation_3_5_9`; backbone `Polynomial.Chebyshev.integral_T_mul_T_div_sqrt` |
| §3.5 `Hˢ` estimates | S | Sobolev spaces |

### Chapter 4 — Fourier Analysis and Wavelets (26 planned, 7 skipped)

| Result | State | Node |
|---|---|---|
| (4.1.1)–(4.1.3), (4.1.4)–(4.1.6) | P | `AtkinsonHan.Chapter04.equation_4_1_3`, `equation_4_1_6` |
| (4.1.7)–(4.1.10) (sine/cosine series) | P | `equation_4_1_10` |
| **Thm 4.1.1 (pointwise convergence)** | **P** | `theorem_4_1_1`; backbone `dirichletKernel`, `integral_dirichletKernel`, `fourierPartialSum`, `fourierPartialSum_eq_integral`, `tendsto_fourierPartialSum_of_dini`, `tendsto_fourierPartialSum_of_hasDerivAt` |
| Thm 4.1.2 (`Lᵖ` convergence iff bounded) | P | `theorem_4_1_2` |
| (4.1.13)–(4.1.14) (Parseval) | P | `equation_4_1_13` |
| Ex 4.1.3–4.1.5, Gibbs | S | illustrations; Gibbs asserted with a reference |
| (4.1.12) for `1 < p < ∞` | S | M. Riesz theorem, not in Mathlib |
| (4.2.1)–(4.2.3) (the transform) | P | `bookFourier` |
| (4.2.5)–(4.2.6), Riemann–Lebesgue | P/M | `equation_4_2_6` |
| (4.2.7)–(4.2.8) (derivative rules) | P/M | `equation_4_2_8` |
| Def 4.2.1, (4.2.9) (Schwartz space) | P/M | `definition_4_2_1` |
| (4.2.10) (multiplication formula) | P/M | `equation_4_2_10` |
| (4.2.4), (4.2.11) (inversion) | P/M | `equation_4_2_11` |
| Def 4.2.2, Def 4.2.3, (4.2.13) | P/M | `definition_4_2_3` |
| **Thm 4.2.4 (Plancherel)** | P/M | `theorem_4_2_4` (Mathlib `Lp.fourierTransformₗᵢ`) |
| `Lᵖ` transform, `p ∉ {1,2}` | S | remarked only |
| Def 4.3.1, (4.3.1)–(4.3.2) | P | `definition_4_3_1`; backbone `Matrix.dft`, `Matrix.dft_eq_zmodDft` |
| **Thm 4.3.2 (inverse DFT)** | P | `theorem_4_3_2`; backbone `Matrix.conjTranspose_dft_mul_dft` |
| (4.3.6)–(4.3.9) (radix-2) | P | `equation_4_3_9`; backbone `Matrix.dft_radix_two` |
| FFT algorithm, `O(n log n)` | S | algorithmic |
| (4.4.1), the scaling spaces | P | `equation_4_4_1`; backbone `Lp.dilationₗᵢ`, `Haar.scalingFun`, `Haar.V` |
| **Thm 4.4.1 (1)–(5)** | **P** | `theorem_4_4_1`; backbone `Haar.orthonormal_scalingFun`, `.V_eq_map_dilation`, `.V_le_V_succ`, `.topologicalClosure_iSup_V`, `.iInf_V_eq_bot` |
| Thm 4.4.2, (4.4.2) | P | `theorem_4_4_2`; backbone `Haar.waveletFun`, `Haar.W`, `Haar.mem_W_iff` |
| The wavelet decomposition of `L²(ℝ)` | P | `equation_4_4_3`; backbone `Haar.isCompl_V_W` |
| Thm 4.4.3, Thm 4.4.4 | P | `theorem_4_4_3`, `theorem_4_4_4`; backbone `Haar.decomposition`, `Haar.reconstruction` |
| Def 4.5.1, Prop 4.5.2 | P | `definition_4_5_1`, `proposition_4_5_2`; backbone `IsMultiresolutionAnalysis`, `.orthonormal_scaled`, `Haar.isMultiresolutionAnalysis` |
| (4.5.1)–(4.5.3) (scaling equation) | P | `equation_4_5_2`; backbone `IsMultiresolutionAnalysis.hasSum_scalingEquation` |
| **(4.5.4)–(4.5.6), general wavelets, Daubechies** | **S** | stated without proof in the book; needs the Fourier-side construction |

### Headline

Of the **63 numbered Theorems, Propositions, Lemmas and Corollaries** in Chapters 1–4, **53 are
planned or already done** and **10 are skipped** (Thm 1.5.5's clauses counted once): Thm 2.7.5,
Thm 2.8.12 (3) and (5), Thm 2.8.14 (1), Thm 2.9.3, Thm 2.9.4, Thm 3.1.5, and — counted among the
displayed formulas rather than the numbered theorems — (4.1.12) for `p ≠ 2`, the general wavelet
construction of §4.5, and the weakly singular kernels of §2.8.1. Every skip has a named
obstruction: reflexivity and weak compactness (2), the Riesz ascent–descent theory (3), contour
integrals of operator-valued functions (2), Müntz–Szász (1), the M. Riesz theorem (1), the
Fourier-side wavelet construction (1), and the modulus-of-continuity theory of weakly singular
kernels (1). Nothing is skipped for want of effort, and nothing needs Sobolev spaces except the
five displayed estimates listed in §4.

---

## 6. What was created

Backbone groups (60 open nodes):

| Group | Nodes | What |
|---|---|---|
| `Numlib/Analysis/Fourier` | — | directory |
| `Numlib/Analysis/Fourier/TrigonometricBasis` | 7 | the real trigonometric Hilbert basis, `a_j`/`b_j`, Parseval |
| `Numlib/Analysis/Fourier/Dirichlet` | 6 | Dirichlet kernel, partial sums, Dini's criterion |
| `Numlib/Analysis/Fourier/DFT` | 4 | `Matrix.dft`, inversion, radix-2 |
| `Numlib/Analysis/Wavelet` | — | directory |
| `Numlib/Analysis/Wavelet/Haar` | 14 | the Haar system on `L²(ℝ)` |
| `Numlib/Analysis/Wavelet/Multiresolution` | 4 | Definition 4.5.1 as an interface |
| `Numlib/Analysis/Normed/Operator/Compact` | 6 | closure properties, Schauder, closed range |
| `Numlib/Analysis/Convex/Uniform` | 2 | Radon–Riesz |
| `Numlib/Approximation/Unisolvent` | 5 | the abstract interpolation problem |
| `Numlib/Approximation/Hermite` | 4 | Hermite interpolation and Rolle with multiplicities |
| `Numlib/Approximation/OrthogonalPolynomial` | 8 | orthogonal polynomials of a measure; Legendre, Chebyshev |

Surface groups (95 open nodes): `NumlibSurface/AtkinsonHan/Chapter01` with `Section01`, `02`,
`03`, `05`, `06`; `Chapter02/Section01`, `02`, `06`, `07`, `08`, `09`;
`Chapter03/Section01`, `02`, `05`; `Chapter04` with `Section01` … `Section05`.
