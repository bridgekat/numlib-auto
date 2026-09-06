# Proposal: Atkinson–Han, Chapter 5 onward

Everything this planning task could not put into a TOML group file, because the file already
exists and belongs to another agent, or because the entry is a decision rather than a node.

The slice is Atkinson & Han, *Theoretical Numerical Analysis* (3rd ed.), Chapter 5 onward, minus
what the surface already covers. What it produced: 13 new backbone groups (64 open nodes) and 17
new surface groups (59 open nodes). `lake exe tracker lint` prints `ok`.

New backbone groups

| Group | Nodes | Serves |
|---|---|---|
| `Numlib/Analysis/Convex/Gateaux` | 8 | AH Thm 5.3.17–5.3.19, Thm 11.2.1 |
| `Numlib/Analysis/Convex/SaddlePoint` | 5 | AH Def 8.6.1, Prop 8.6.2 |
| `Numlib/Analysis/InnerProductSpace/WeakCompactness` | 2 | AH Thm 11.4.1, 11.4.6 |
| `Numlib/Analysis/Normed/Operator/CollectivelyCompact` | 6 | AH Lem 12.1.3–12.1.4, 12.4.7 |
| `Numlib/FiniteDifference` (directory) | — | AH Ch. 6 |
| `Numlib/FiniteDifference/LaxEquivalence` | 10 | AH §6.2 in full |
| `Numlib/FiniteDifference/TwoLevel` | 1 | AH Thm 6.3.2 |
| `Numlib/IntegralEquations/SecondKind` | 10 | AH Thm 12.1.2, Lem 12.3.1, Thm 12.4.3, Thm 12.6.1 |
| `Numlib/Nonlinear/CompletelyContinuous` | 2 | AH Def 5.5.3, Prop 5.5.5 |
| `Numlib/Variational/AubinNitsche` | 2 | AH Thm 10.4.3, Cor 10.4.4 |
| `Numlib/Variational/Inequality` (directory) | — | AH Ch. 11 |
| `Numlib/Variational/Inequality/Basic` | 12 | AH §11.2–11.3 |
| `Numlib/Variational/Inequality/Approximation` | 6 | AH §11.4 |

New surface groups, all under `plans/NumlibSurface/AtkinsonHan/`: `Chapter05/Section05` (2),
`Chapter06` + `Section02` (10) + `Section03` (4), `Chapter08/Section06` (2), `Chapter10` +
`Section04` (2), `Chapter11` + `Section02` (3) + `Section03` (12) + `Section04` (6), `Chapter12` +
`Section01` (6) + `Section03` (3) + `Section04` (4) + `Section06` (3) + `Section07` (2).

---

## 1. Additions to existing groups

**A1. `Numlib/Nonlinear/FixedPoint`: a bundled strong-monotonicity predicate.**
Add `LinearMap`-style bundles for the hypotheses that `zarantonello`,
`norm_sub_le_of_strongly_monotone` and `contractingWith_damped` take unbundled:

* `IsStronglyMonotoneWith (A : E → E) (c : ℝ) : Prop := ∀ x y, c * ‖x - y‖ ^ 2 ≤ re ⟪A x - A y, x - y⟫`,
  kind `definition`, no deps.

Reason: with the elliptic-variational-inequality layer there are now seven consumers of that exact
hypothesis (`zarantonello`, `norm_sub_le_of_strongly_monotone`, `contractingWith_damped`, and the
four existence and stability nodes of `Numlib/Variational/Inequality/Basic`), plus the surface
predicate `AtkinsonHan.Chapter05.StronglyMonotoneWith` that already exists for AH (5.1.8). §1.3 of
`backbone.md` asks for a named bundle exactly at that point. It belongs in `Nonlinear/FixedPoint`
rather than in the new module because that is where the first consumer lives. **Until it exists**,
`Numlib/Variational/Inequality/Basic` states the hypothesis unbundled, in exactly the shape
`zarantonello` uses, so that nothing has to be translated; when the bundle lands, both modules
should switch together, in one task, because that is a restatement of proved declarations.

**A2. `Numlib/Variational/Minimization`: cross-reference the Hilbert-space minimizer.**
That module's description claims the territory "existence of minimizers of functionals on closed
sets" and then explains that the reflexive-space theorems (AH Thm 3.3.8, 3.3.10, 3.3.12, 3.3.14)
are not planned. Add a sentence pointing at
`Numlib/Variational/Inequality/Basic.existsUnique_isMinOn_energy_add`, which *is* an existence
theorem for a minimizer over a closed convex set and which sidesteps reflexivity entirely by using
the parallelogram law. AH Thm 8.8.5 and Thm 11.2.2 both invoke Thm 3.3.12 in the book, and only the
second is recovered this way; a reader of `Minimization.toml` should be told which.

**A3. `NumlibSurface/AtkinsonHan/Chapter05/Section03`: track the convexity results.**
`theorem_5_3_17`, `theorem_5_3_18`, `theorem_5_3_19` and `theorem_5_3_19_submodule` exist and are
proved in `NumlibSurface/AtkinsonHan/Chapter05/Section03.lean` but are **not** nodes of
`Chapter05/Section03.toml`, which tracks only `HasGateauxDerivAt` and `example_5_3_10`. They are
book-numbered results and `plans/README.md` says every one of those is a node. Add:

* `theorem_5_3_17`, `theorem_5_3_18`, `theorem_5_3_19`, `theorem_5_3_19_submodule`, kind `theorem`,
  deps on the new `Numlib/Analysis/Convex/Gateaux` nodes (see C1).

The same file also proves `proposition_5_3_3`, `proposition_5_3_5`–`proposition_5_3_7`,
`proposition_5_3_11`, `corollary_5_3_12`, `proposition_5_3_13`, `proposition_5_3_15_*` and
`example_5_3_8`, none of which is tracked. Whether the plan wants all of them is a judgement for
the owner of that file; §5.3 is otherwise complete, and the tracker currently reports Chapter 5 as
covering less of §5.3 than it does.

**A4. `NumlibSurface/AtkinsonHan/Chapter05.toml` and `Chapter08.toml`: widen the descriptions.**
`Chapter05.toml` says "§5.1–5.4, §5.6" and `Chapter08.toml` says "§8.2–8.3, §8.7"; this task adds
`Chapter05/Section05` and `Chapter08/Section06` beneath them. One word each.

**A5. `NumlibSurface/AtkinsonHan/Chapter12/Section04`: the Nyström instance, later.**
When `Numlib/IntegralEquations/Basic` and `Numlib/Approximation/Quadrature` exist, add
`lemma_12_4_2` and `theorem_12_4_4` — that the numerical integral operators
`K_n u (x) = Σ w_j k(x, t_j) u(t_j)` form a collectively compact pointwise convergent family on
`C(D)`, and the resulting error bound. Every step of the book's proof is
`IsCollectivelyCompactFamily` plus `theorem_12_4_3`, both of which this task plans, so the addition
is small; it is deferred only because the `C(D)` toolkit is being written by another agent right
now and the convergent-quadrature hypothesis is `Numlib/Approximation/Quadrature`'s
Banach–Steinhaus criterion.

---

## 2. Changes to existing declarations

**C1. Promote the convexity-through-derivatives lemmas out of the Atkinson–Han surface.**
`NumlibSurface/AtkinsonHan/Chapter05/Section03.lean` proves, in the surface,
`ConvexOn.add_lineDeriv_le`, `convexOn_of_add_lineDeriv_le`, `monotone_of_add_lineDeriv_le`,
`add_lineDeriv_le_of_monotone`, `StrictConvexOn.add_lineDeriv_lt`,
`strictConvexOn_of_add_lineDeriv_lt`, `strictMonotone_of_add_lineDeriv_lt`,
`add_lineDeriv_lt_of_strictMonotone` and the three book theorems built on them. They are general
statements about a convex function on a normed space, they carry no book-specific vocabulary, and
`plans/atkinsonhan-ch5.md` §3 lists them as "candidates for the backbone once a second consumer is
formalized". Chapter 11 is that consumer: AH Thm 11.2.1 is the same statement with an extra convex
term, and `Numlib/Variational/Inequality/Basic` depends on it through
`isMinOn_add_iff_forall_le`.

Requested change: once `Numlib/Analysis/Convex/Gateaux` is written, restate the eight surface
lemmas as one-line specializations of it and delete the duplicated proofs, keeping
`theorem_5_3_17`–`theorem_5_3_19` under their book names. This must be one task, since it changes
proved declarations. It is the largest duplication risk this plan creates and the reason the
backbone module carries the same lemma names: an agent writing `Gateaux.lean` from the group file
alone would otherwise reinvent them.

**C2. `Numlib/Variational/ProjectionMethod`: route the compactness argument through the new lemma.**
The description of `exists_isProjectionMethodSolution_of_isCompactOperator` says its proof shows
"`‖P_n K - K‖ → 0` by compactness (pointwise convergence is uniform on the compact closure of the
image of the ball)". That is exactly
`Numlib/Analysis/Normed/Operator/CollectivelyCompact.tendsto_opNorm_comp_of_isCompactOperator`
(AH Lemma 12.1.4), which this task plans and which AH Ch. 12 and Kress Ch. 12 both need. Requested:
add that node to the `deps` of `exists_isProjectionMethodSolution_of_isCompactOperator` and say in
the description that the estimate is imported rather than redone. Similarly, the quantitative
two-sided error estimate of AH Thm 12.1.2 is planned as
`Numlib/IntegralEquations/SecondKind.norm_sub_le_of_projection`; `ProjectionMethod` should keep the
definition and Kress's qualitative statement and not restate the bound.

**C3. `Numlib/Analysis/Normed/Operator/BanachSteinhaus`: where uniform-on-compacts belongs.**
`tendstoUniformlyOn_of_tendsto_of_isCompact` (AH Lemma 12.1.3) is planned in
`CollectivelyCompact` because that is where its consumers are, but its natural home is beside
`ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded` in `BanachSteinhaus`. If
`BanachSteinhaus` is written first, move it there and let `CollectivelyCompact` depend on it; if
not, leave it where it is. Either way it must exist once.

**C4. `Numlib/Variational/AubinNitsche` should end up inside `Numlib/Variational/Galerkin`.**
The two nodes are Galerkin theorems and would be four lines each in `Galerkin.lean`, next to
`IsGalerkinSolution.apply_sub_eq_zero`, which they use. They are a separate module only because
`Galerkin.toml` is an existing group file this task may not edit. Merging them when `Galerkin` is
next touched costs nothing and saves a module.

**C5. Correction to `plans/atkinsonhan-ch5.md` §3 item 3 and to
`Numlib/Krylov/Convergence/Superlinear.toml`: Mathlib now has the compact spectral theorem.**
Both documents say Winther's theorem (AH Thm 5.6.2) and (5.6.7)–(5.6.9) are "blocked by the
spectral theorem for compact self-adjoint operators (AH Thm 2.8.15; absent from Mathlib)". In the
pinned Mathlib (`v4.34.0-rc2`, rev `85e3a25`) that is no longer true:
`Mathlib/Analysis/InnerProductSpace/Spectrum.lean` has
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` (for a compact symmetric `T`,
the eigenspaces have trivial orthogonal complement — both statements are labelled "**The Spectral
Theorem** for compact self-adjoint operators"), `ContinuousLinearMap.finite_dimensional_eigenspace`
(eigenspaces for nonzero eigenvalues are finite-dimensional) and
`ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero`. What is still missing is only the
*enumeration*: a `HilbertBasis ℕ` of eigenvectors with the eigenvalues listed in decreasing order
of absolute value and tending to zero, which is a countability and ordering argument on top of what
is there. That is a much smaller obstruction than the one recorded, and the phase-2 Winther node
should be re-estimated accordingly. Outside this task's slice, so it is reported rather than
replanned.

---

## 3. Not planned, and why

Verified against the pinned Mathlib rather than assumed.

### Chapter 7, Sobolev spaces — the whole chapter

The claim in `backbone.md` §0.2 and §1.7 that Chapter 7 is out of scope "until Mathlib has Sobolev
spaces" needed checking, because the pinned Mathlib **does** contain a file called
`Mathlib/Analysis/Distribution/Sobolev.lean`. It is not the Sobolev theory this chapter needs.

*What is there.* `TemperedDistribution.besselPotential` and `TemperedDistribution.MemSobolev s p f`
— the Bessel potential spaces `H^{s,p}(E)` on a finite-dimensional real inner product space,
defined through the Fourier transform as a **predicate on tempered distributions**, with closure
under sums, scalars, bounded Fourier multipliers, line derivatives (`MemSobolev.lineDerivOp`) and
the Laplacian (`MemSobolev.laplacian`), plus `SchwartzMap.memSobolev` and the `p = 2`
characterization. Separately, `Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean` has the
Gagliardo–Nirenberg–Sobolev inequalities `eLpNorm_le_eLpNorm_fderiv*` for compactly supported `C¹`
functions on a finite-dimensional space.

*What is not there.* Searched by name and by concept, with nothing found: weak derivatives of an
`L¹_loc` function on an open set (`weakDeriv`, `HasWeakFDeriv` — no occurrences anywhere in
Mathlib); `W^{k,p}(Ω)` for an open `Ω` as a normed space (AH Def 7.2.2, Thm 7.2.3, Cor 7.2.4);
`W^{k,p}_0(Ω)` and `H^{-s}(Ω)` (Def 7.2.9, 7.2.11, 7.2.12); Sobolev spaces over a boundary
(Def 7.2.13); density of smooth functions (Thm 7.3.1–7.3.4); extension operators (Thm 7.3.5);
embedding and compact embedding theorems (Thm 7.3.7–7.3.9 — `Rellich` and `Kondrachov` have no
occurrences); trace operators (Thm 7.3.10–7.3.11 — `traceMap` has no occurrences); the
Deny–Lions / Bramble–Hilbert equivalent-norm theorems and the Poincaré–Friedrichs inequalities
they yield (Thm 7.3.12–7.3.14, Thm 7.3.17, Cor 7.3.18 — `Poincare` and `Friedrichs` occur nowhere
in analysis); the periodic Sobolev spaces `H^s(2π)` and their embedding and interpolation results
(§7.5); spherical harmonics and Sobolev spaces on the sphere (§7.5.5); and the divergence theorem
on a Lipschitz domain (Prop 7.6.1 — Mathlib's `MeasureTheory/Integral/DivergenceTheorem.lean` is
for boxes).

*Verdict.* Not planned, and the reason is precise rather than general: the chapter's subject is
`W^{k,p}(Ω)` for a Lipschitz domain `Ω`, and Mathlib has neither weak derivatives on a domain nor
any of the four structural theorems (density, extension, embedding, trace) that everything after
§7.2 rests on. Even AH Thm 7.4.1, which characterizes `H^k(ℝ^d)` by the Fourier transform and looks
like Mathlib's definition, has no content to state: Mathlib *defines* the space that way and has no
`H^k(ℝ^d)` built from weak derivatives to compare it with. One item is closer than the rest and is
worth recording for a later phase: the **periodic** Sobolev spaces `H^s(2π)` of §7.5 are a weighted
`ℓ²` space over the Fourier basis of `AddCircle`, need none of the domain machinery, and would
bring Prop 7.5.4–7.5.6 (including the trapezoidal rule for periodic integrands) and Thm 7.5.7
(trigonometric interpolation error) with them; they belong with
`Numlib/Approximation/Trigonometric` if that module is ever written.

### Chapter 8, the sections outside §8.2–8.3, 8.6, 8.7

* §8.1 (the model problem (8.1.1)–(8.1.4)), §8.4 (weak formulations with Dirichlet, Neumann, mixed
  and Robin conditions; Lemma 8.4.1, the quotient Poincaré inequality), §8.5 (linearized
  elasticity, Thm 8.5.1, which needs Korn's inequality): `H¹(Ω)`, `H¹₀(Ω)`, traces, and
  Poincaré — none of which exist, as above. This confirms the existing entry in
  `plans/atkinsonhan-ch8-9.md` §6.
* §8.6, Theorem 8.6.3 (Ekeland–Temam existence of a saddle point): needs weak compactness of
  bounded sets in a **reflexive Banach** space. Mathlib has Banach–Alaoglu
  (`WeakDual.isCompact_polar`) and its sequential form for separable spaces, but no reflexivity
  class and no Eberlein–Šmulian, so the hypotheses of the theorem cannot even be stated honestly.
  Definition 8.6.1 and Proposition 8.6.2 *are* planned, in `Chapter08/Section06`.
* §8.6, the abstract mixed problem (8.6.21)–(8.6.22): the book states the problem and refers every
  theorem about it to Brezzi. Nothing to formalize.
* §8.8 (Lemmas 8.8.1–8.8.4, Thm 8.8.5, the `p`-Laplacian-type problem): `W^{1,p}_0(Ω)`, its
  reflexivity, and AH Thm 3.3.12 for the direct method. The last is also unavailable — see A2.
  Note that the book's proof of Thm 8.8.5 is exactly Thm 3.3.12 plus Thm 5.3.19, both of which are
  reachable in a Hilbert space; only the space is out of reach.

### Chapter 9 — nothing left

§9.1–9.4 are complete in the surface but for `remark_9_2_2`, which is already an open node of
`Chapter09/Section02` waiting on the two Xu–Zikatanov nodes of `Variational/Galerkin`. There is no
§9.5. Exercise 9.1.4 (Galerkin as an existence proof by weak compactness) stays out for the reason
`plans/atkinsonhan-ch8-9.md` gives; the Hilbert-space half of it would now be reachable through
`exists_subseq_weak_tendsto`, but no theorem of the book cites it.

### Chapter 6, the concrete schemes

§6.1 in full (it has no numbered result), Examples 6.2.4, 6.2.8, 6.2.13, Examples 6.3.3, 6.3.4 and
every exercise of the chapter. They are the forward, backward and Crank–Nicolson schemes for
`u_t = ν u_xx`: Taylor expansions of a solution assumed smooth by hypothesis, the maximum principle
for the heat equation (quoted by the book from a PDE text), and the eigenvalues of a tridiagonal
Toeplitz matrix. None of it exercises the abstract theory, and formalizing it would be partial
differential equations. Exercise 6.3.1, the eigenvalues `a + 2√(bc) cos(jπ/(N+1))` of a
tridiagonal Toeplitz matrix, is the one piece with independent interest; it has no consumer in this
corpus and is left as a note rather than a node.

### Chapter 10, everything but the Aubin–Nitsche lemma

Prop 10.2.1 and Lemma 10.2.2 (affine-equivalent elements), Thm 10.3.1, 10.3.3–10.3.5,
Cor 10.3.7, Thm 10.3.9 (finite element interpolation error, which is the Bramble–Hilbert lemma and
hence AH Thm 7.3.12), Thm 10.4.1 and (10.4.11): all `W^{k,p}(K)` on a simplex, its scaling under an
affine map, and elliptic regularity. Thm 10.4.3 is planned; Cor 10.4.4 is planned with its
regularity hypothesis (10.4.9) made abstract.

### Chapter 12, the concrete methods

§12.2 in full (piecewise linear and trigonometric collocation, piecewise linear and trigonometric
Galerkin, uniform convergence, conditioning), Thm 12.3.3 and the superconvergence estimates of
§12.3, Lemma 12.4.2 and Thm 12.4.4 (deferred rather than skipped, see A5), §12.5 in full (product
integration for `log|x−y|` and `|x−y|^{γ−1}` kernels, Thm 12.5.1, 12.5.4, 12.5.6, Lemma 12.5.5,
graded meshes), §12.6.3–12.6.4, §12.7.3. These are estimates of `‖u − P_n u‖` or `‖(K − K_n) u‖`
for particular subspaces and quadrature rules; they need the interpolation, quadrature and
trigonometric branches of `Numlib/Approximation/` (all phase 3) and, for §12.5, Hölder spaces and
weakly singular kernels that no other source in the corpus asks for.

§12.7.2, the homotopy argument, is skipped for a different reason: it computes the index of
`v ↦ v − P_n T v` from that of `v ↦ v − T v` using the rotation of a completely continuous vector
field. Mathlib has no degree theory (`Brouwer` occurs only in order theory), and the book quotes
properties P1–P5 without proof. Equation (12.7.13), the sharp error bound with `γ_n → 0`, is quoted
from a paper; the weaker Exercise 12.7.3 form is planned instead.

### Chapter 5, §5.5

Thm 5.5.1 (Brouwer), Thm 5.5.4 (Schauder), and §5.5.1 (rotation and index, P1–P5): quoted without
proof by the book, no Mathlib support, and building either Brouwer or degree theory is algebraic
topology. Example 5.5.2, a Lipschitz self-map of the Hilbert unit ball with no fixed point, is
formalizable — it is a weighted shift on a `HilbertBasis` — but nothing cites it. Def 5.5.3 and
Prop 5.5.5 **are** planned, because §12.7 needs them.

### Chapter 13 and Chapter 14

* Chapter 13, boundary integral equations: Green's identities and the representation formula
  (Thm 13.1.1–13.1.2), the Kelvin transform, single and double layer potentials, the interior and
  exterior Dirichlet and Neumann problems, and §13.3. This is potential theory for the Laplacian on
  a planar domain: it needs the divergence theorem on a Lipschitz domain (AH Prop 7.6.1),
  the periodic Sobolev spaces `H^s(2π)` of §7.5, and the regularity of layer potentials. Nothing
  survives the removal of those. Not planned.
* Chapter 14, multivariable polynomial approximation: Thm 14.1.1 (a Jackson theorem for the unit
  ball of `ℝ^d`), Thm 14.2.3 (the triple recursion for orthogonal polynomials in two variables),
  Thm 14.2.4–14.2.5 (the norm of the orthogonal projection `C(𝔹₂) → Π_n`, quoted from Xu without
  proof), §14.3 (hyperinterpolation), §14.4 (a Galerkin method on the ball, in `H¹`). The
  formalizable core would be multivariate orthogonal polynomials on `L²(𝔹_d, W)` — Mathlib has
  `Polynomial.Chebyshev` and `MvPolynomial` but no orthogonal-polynomial theory in several
  variables, and no second consumer in this corpus asks for one. Two of the three substantial
  theorems are quoted without proof. Not planned.

---

## 4. Coverage summary

`already` = proved in `NumlibSurface` today; `planned` = an open node created by this task, with
the group; `deferred` = an open node that waits on a module another agent owns; `skipped` = §3
above. Only Chapters 5 onward are listed, the slice of this task.

### Chapter 5 (the gaps named in the assignment)

| Result | State | Where |
|---|---|---|
| §5.2.3 (5.2.7)–(5.2.9), Thm 5.2.2, 5.2.3 | deferred (already planned) | `Chapter05/Section02.theorem_5_2_2`, `theorem_5_2_3`; waits on `IntegralEquations/Basic` |
| §5.2.4 Thm 5.2.4 | deferred (already planned) | `Chapter05/Section02.theorem_5_2_4` |
| §5.3 Def 5.3.1–5.3.2, Prop 5.3.3–5.3.7, Ex 5.3.8, Prop 5.3.11, Cor 5.3.12, Prop 5.3.13, Prop 5.3.15, Thm 5.3.17–5.3.19 | **already** | `Chapter05/Section03.lean`, proved in full; only `example_5_3_10` (Urysohn derivative) is open, and only four of these are tracked nodes — see A3 |
| Cor 5.3.16 | skipped | an `iff` of continuity of the partials, provable from `proposition_5_3_15_of_partial`; noted, not planned |
| Ex 5.3.9 (Jacobian), Ex 5.3.10 | already recorded as out of scope / deferred | `plans/atkinsonhan-ch5.md` §4 |
| §5.5 Def 5.5.3 | planned | `Chapter05/Section05.IsCompletelyContinuousOn` |
| §5.5 Prop 5.5.5 | planned | `Chapter05/Section05.proposition_5_5_5` |
| §5.5 Thm 5.5.1, Ex 5.5.2, Thm 5.5.4, P1–P5 | skipped | no Brouwer, no degree theory |

The assignment named §5.3 as a gap. It is not one: `Chapter05/Section03.lean` is 595 lines and
proves every numbered result of §5.3 except Cor 5.3.16 and the two examples. What §5.3 needs is not
formalization but the tracking and backbone promotion of A3 and C1.

### Chapter 6

| Result | State | Where |
|---|---|---|
| §6.1, Ex 6.1.1–6.1.7 | skipped | no numbered results; specific schemes |
| Def 6.2.1, 6.2.2, 6.2.3 | planned | `Chapter06/Section02.IsSolution`, `IsWellPosed`, `solutionOperator` |
| Prop 6.2.5, Prop 6.2.6 | planned | `Chapter06/Section02.proposition_6_2_5`, `proposition_6_2_6` |
| Def 6.2.7, 6.2.9, 6.2.10 | planned | `Chapter06/Section02.IsConsistent`, `IsConvergent`, `IsStable` |
| **Thm 6.2.11 (Lax equivalence)** | planned | `Chapter06/Section02.theorem_6_2_11`, on `FiniteDifference.isStable_iff_isConvergent` |
| Cor 6.2.12 | planned | `Chapter06/Section02.corollary_6_2_12` |
| Ex 6.2.4, 6.2.8, 6.2.13, Ex 6.2.1–6.2.3 | skipped | heat equation |
| Def 6.3.1 | planned | `Chapter06/Section03.IsConsistentScheme`, `IsStableScheme`, `IsConvergentScheme` |
| Thm 6.3.2 | planned | `Chapter06/Section03.theorem_6_3_2`, on `FiniteDifference.norm_sub_le_of_stable` |
| Ex 6.3.3, 6.3.4, Ex 6.3.1–6.3.3 | skipped | heat equation; Ex 6.3.1 noted |

Chapter 6: 12 of 14 numbered items planned; the 2 skipped are the worked examples.

### Chapter 7

Nothing planned. 24 numbered results (Lemma 7.1.2 through Prop 7.6.1) skipped, with the obstruction
named per family in §3.

### Chapter 8 (the gaps named in the assignment)

| Result | State | Where |
|---|---|---|
| §8.1 (8.1.1)–(8.1.4) | skipped | `H¹₀(Ω)` |
| §8.4 Lemma 8.4.1 and all weak formulations | skipped | traces, Poincaré |
| §8.5 Thm 8.5.1 | skipped | Korn's inequality |
| §8.6 Def 8.6.1 | planned | `Chapter08/Section06.IsSaddlePoint` |
| §8.6 Prop 8.6.2, (8.6.12)–(8.6.14) | planned | `Chapter08/Section06.proposition_8_6_2` |
| §8.6 Thm 8.6.3 | skipped | reflexivity, weak compactness |
| §8.6 (8.6.21)–(8.6.22) | skipped | no theorem in the book |
| §8.8 Lemma 8.8.1–8.8.4, Thm 8.8.5 | skipped | `W^{1,p}_0(Ω)`, reflexivity |

Chapter 8's remaining gaps yield exactly two formalizable items, and both are planned.

### Chapter 9

Complete but for `remark_9_2_2`, already an open node. Nothing added.

### Chapter 10

| Result | State |
|---|---|
| Thm 10.4.3 (Aubin–Nitsche) | planned — `Chapter10/Section04.theorem_10_4_3` |
| Cor 10.4.4 | planned in abstract form — `Chapter10/Section04.corollary_10_4_4_abstract` |
| Prop 10.2.1, Lemma 10.2.2, Thm 10.3.1, 10.3.3, 10.3.4, 10.3.5, Cor 10.3.7, Def 10.3.6, Thm 10.3.9, Thm 10.4.1 | skipped — Sobolev spaces, Bramble–Hilbert, elliptic regularity |

### Chapter 11

| Result | State | Where |
|---|---|---|
| §11.1 Ex 11.1.1, 11.1.2, (11.1.9), (11.1.14) | skipped | `H¹₀(Ω)`, traces, regularity |
| Thm 11.2.1 | planned | `Chapter11/Section02.theorem_11_2_1` |
| Thm 11.2.2 | planned | `Chapter11/Section02.theorem_11_2_2` |
| Ex 11.2.1 (complex case) | planned | `Chapter11/Section02.exercise_11_2_1` |
| Ex 11.2.3, 11.2.4 | skipped | domains |
| Thm 11.3.1 | planned | `Chapter11/Section03.theorem_11_3_1` |
| Lemma 11.3.5 | planned | `Chapter11/Section03.lemma_11_3_5` (Mathlib `ConvexOn.exists_affine_le_of_lt`) |
| Thm 11.3.6 (Stampacchia) | planned | `Chapter11/Section03.theorem_11_3_6` |
| Thm 11.3.7 | planned | `Chapter11/Section03.theorem_11_3_7` |
| Lemma 11.3.8 (Minty) | planned | `Chapter11/Section03.lemma_11_3_8` |
| Thm 11.3.9 | planned | `Chapter11/Section03.theorem_11_3_9` |
| remark after Ex 11.3.11 (energy projection) | planned | `Chapter11/Section03.isBestApprox_energy_of_theorem_11_3_9` |
| Ex 11.3.2, 11.3.3, 11.3.10, 11.3.13 | planned | `Chapter11/Section03` |
| Thm 11.3.12 (regularity) | skipped | `W^{2,p}`, elliptic regularity |
| Ex 11.3.1, 11.3.4–11.3.9, 11.3.11, 11.3.12 | skipped | local Lipschitz exercise; the rest name domains |
| Thm 11.4.1 | planned | `Chapter11/Section04.theorem_11_4_1` |
| Thm 11.4.2 (Falk) | planned | `Chapter11/Section04.theorem_11_4_2` |
| Ex 11.4.2, 11.4.3 | planned | `Chapter11/Section04` |
| Thm 11.4.6, Thm 11.4.7 | planned | `Chapter11/Section04` |
| Thm 11.4.5, Ex 11.4.4 (Lagrange multipliers) | skipped | `H^{1/2}(Γ)`, `(L¹)' = L^∞` |
| Ex 11.4.3, 11.4.4 (examples), §11.5 in full | skipped | finite elements on a polygon; contact mechanics |

Chapter 11 abstract core: **every** numbered result of §11.2, §11.3 and §11.4 is planned except
the regularity theorem 11.3.12 and the Lagrange-multiplier theorem 11.4.5 — 15 of 17.

### Chapter 12

| Result | State | Where |
|---|---|---|
| Thm 12.1.2 | planned | `Chapter12/Section01.theorem_12_1_2` |
| Lemma 12.1.3, Lemma 12.1.4 | planned | `Chapter12/Section01.lemma_12_1_3`, `lemma_12_1_4` |
| Ex 12.1.3, 12.1.4 | planned | `Chapter12/Section01` |
| §12.1.1, §12.1.2 (collocation, Galerkin systems) | skipped | definitions on `C(D)`, `L²(D)` |
| §12.2 in full | skipped | interpolation and quadrature error estimates |
| Lemma 12.3.1, (12.3.1)–(12.3.3), (12.3.11) | planned | `Chapter12/Section03` |
| Thm 12.3.3, §12.3.1–12.3.2 concrete parts | skipped | piecewise quadratic collocation |
| **Thm 12.4.3 (Anselone)** | planned | `Chapter12/Section04.theorem_12_4_3` |
| A1–A3, Lemma 12.4.7 | planned | `Chapter12/Section04.IsCollectivelyCompactFamily`, `lemma_12_4_7` |
| abstract form of Thm 12.4.4 | planned | `Chapter12/Section04.exists_norm_inverse_le_of_isCollectivelyCompactFamily` |
| Lemma 12.4.2, Thm 12.4.4 (Nyström instance) | deferred | needs `IntegralEquations/Basic` + `Approximation/Quadrature`; see A5 |
| §12.5 in full (Thm 12.5.1, 12.5.4, 12.5.6, Lemma 12.5.5) | skipped | weakly singular kernels, Hölder spaces, graded meshes |
| (12.6.20)–(12.6.28), Thm 12.6.1 | planned | `Chapter12/Section06` |
| §12.6.3, §12.6.4 | skipped | linear systems, operation count |
| Lemma 12.7.1, Ex 12.7.1, Ex 12.7.3 | planned | `Chapter12/Section07` |
| §12.7.2 (homotopy), (12.7.13), §12.7.3 | skipped | degree theory; quoted result; implementation |

Chapter 12 abstract spine: 8 of 9 numbered abstract results planned, the ninth (Thm 12.4.4)
deferred with its route named.

### Chapters 13 and 14

Nothing planned; the obstruction is named per section in §3. 5 numbered results in Chapter 13 and 5
in Chapter 14 are skipped.

### Headline

Of the material in Chapters 5–14 that is not already formalized:

* **planned now**: 59 surface nodes over 13 sections of 6 chapters, on 64 new backbone nodes;
* **deferred** (planned elsewhere, waiting on a module in progress): AH Thm 5.2.2–5.2.4,
  Thm 12.4.4, remark 9.2.2;
* **skipped**: all of Chapters 7, 13 and 14, all of Chapter 10 but one theorem, §8.1, §8.4, §8.5,
  §8.8, §11.1, §11.5, and the concrete-scheme parts of Chapters 6 and 12.

The skip list is dominated by one obstruction: Mathlib has no weak derivatives on an open set and
therefore no `W^{k,p}(Ω)`. Every chapter whose subject is a boundary value problem on a domain goes
with it. What is left over — the Lax equivalence theorem, the elliptic-variational-inequality
theory, the second-kind operator theory, the Aubin–Nitsche argument, saddle points — is the part of
those chapters that Atkinson and Han wrote as functional analysis, and it is now planned in full.
