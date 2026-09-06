<!--
The tracker plan (the TOML group files beside this document) is the authority on which declarations
exist, and the source is the authority on what they say. What is worth reading here is the book
alignment: which numbered result maps to which declaration, how each book-specific definition
relates to the backbone, what was deferred and why, and what was deliberately left out.

The per-result coverage table for this range lives in `proposals/atkinsonhan-ch5-onward.md` §4,
because it is the artifact the orchestrator reads; this file holds the arguments.
-->

# Surface plan: Atkinson–Han — §5.5, Ch. 6, §8.6, §10.4, Ch. 11, Ch. 12

Scope: what remains of Atkinson & Han, *Theoretical Numerical Analysis* (3rd ed.) from Chapter 5
onward after `atkinsonhan-ch5.md` (§5.1–5.4, 5.6) and `atkinsonhan-ch8-9.md` (§8.2–8.3, 8.7,
Ch. 9). Six chapters contribute: §5.5 (completely continuous vector fields, two items), Chapter 6
(finite differences, §6.2–6.3), §8.6 (saddle points), §10.4 (Aubin–Nitsche), Chapter 11 (elliptic
variational inequalities, §11.2–11.4) and Chapter 12 (Fredholm equations of the second kind, the
abstract parts of §12.1, 12.3, 12.4, 12.6, 12.7).

Chapter 7 contributes nothing, and neither do Chapters 13 and 14; §8.1, §8.4, §8.5, §8.8, §11.1,
§11.5 and most of Chapter 10 contribute nothing. The reason is one and the same in every case and
is documented, with the searches that establish it, in `proposals/atkinsonhan-ch5-onward.md` §3 and
in `backbone.md` §11.8.

Generality as in the book. §11.2–11.4 are on a **real** Hilbert space; §6.2 is on a Banach space
over `ℝ` or `ℂ`, and the surface takes `ℝ`; §6.3 is in `ℝ^{N_x−1}` with a norm the book leaves
unspecified, and the surface takes an arbitrary real normed space for exactly that reason; §12.1,
§12.3, §12.4.3 and §12.6.2 are on a Banach space with a scalar `λ ≠ 0`; §8.6's saddle points are on
bare sets. The backbone modules of `backbone.md` §11 are stated over `RCLike 𝕜` wherever the
scalars matter, so each surface file is a specialization and, in §8.6 and §6.3, a renaming.

## 1. Files

| File | Book | Backbone modules used |
|---|---|---|
| `Chapter05/Section05.lean` | Def 5.5.3, Prop 5.5.5 | `Numlib/Nonlinear/CompletelyContinuous` |
| `Chapter06/Section02.lean` | Def 6.2.1–6.2.3, 6.2.7, 6.2.9, 6.2.10; Prop 6.2.5–6.2.6; Thm 6.2.11; Cor 6.2.12 | `Numlib/FiniteDifference/LaxEquivalence` |
| `Chapter06/Section03.lean` | Def 6.3.1, Thm 6.3.2 | `Numlib/FiniteDifference/TwoLevel` |
| `Chapter08/Section06.lean` | Def 8.6.1, Prop 8.6.2 | `Numlib/Analysis/Convex/SaddlePoint` |
| `Chapter10/Section04.lean` | Thm 10.4.3, Cor 10.4.4 | `Numlib/Variational/AubinNitsche`, `Numlib/Variational/Galerkin` |
| `Chapter11/Section02.lean` | Thm 11.2.1, 11.2.2, Ex 11.2.1 | `Numlib/Analysis/Convex/Gateaux`, `Numlib/Variational/Inequality/Basic` |
| `Chapter11/Section03.lean` | Thm 11.3.1, 11.3.6, 11.3.7, 11.3.9; Lem 11.3.5, 11.3.8; Ex 11.3.2, 11.3.3, 11.3.10, 11.3.13 | `Numlib/Variational/Inequality/Basic` |
| `Chapter11/Section04.lean` | Thm 11.4.1, 11.4.2, 11.4.6, 11.4.7; Ex 11.4.2, 11.4.3 | `Numlib/Variational/Inequality/Approximation`, `Numlib/Analysis/InnerProductSpace/WeakCompactness` |
| `Chapter12/Section01.lean` | Thm 12.1.2, Lem 12.1.3–12.1.4, Ex 12.1.3–12.1.4 | `Numlib/IntegralEquations/SecondKind`, `Numlib/Analysis/Normed/Operator/CollectivelyCompact`, `Numlib/Variational/ProjectionMethod` |
| `Chapter12/Section03.lean` | (12.3.1)–(12.3.3), Lem 12.3.1, (12.3.11) | `Numlib/IntegralEquations/SecondKind` |
| `Chapter12/Section04.lean` | Thm 12.4.3, A1–A3, Lem 12.4.7 | `Numlib/IntegralEquations/SecondKind`, `.../CollectivelyCompact` |
| `Chapter12/Section06.lean` | (12.6.20)–(12.6.28), Thm 12.6.1 | `Numlib/IntegralEquations/SecondKind` |
| `Chapter12/Section07.lean` | Lem 12.7.1, Ex 12.7.1, Ex 12.7.3 | `Numlib/Analysis/Calculus/MeanValue`, `Numlib/IntegralEquations/SecondKind` |

## 2. Book-specific definitions and how they are read

### D1. Completely continuous operator (Def 5.5.3)
*Book.* `T : K ⊆ V → W` is **compact** if `T(B)` is relatively compact for every bounded `B ⊆ K`,
and **completely continuous** if it is compact and continuous. *Lean.* The first half is the
backbone `IsCompactMap T K`; the second is `AtkinsonHan.Chapter05.IsCompletelyContinuousOn`, which adds
`ContinuousOn T K`. The two halves are separate because for a nonlinear map compactness does not
imply continuity — that is exactly the remark the book makes after the definition, and it is why
Mathlib's `IsCompactOperator`, which is the linear notion, cannot be reused directly.

### D2. The abstract initial value problem (6.2.1)–(6.2.3)
*Book.* `V` Banach, `V₀ ⊆ V` a dense subspace, `L : V₀ ⊆ V → V` linear and generally unbounded;
`u : [0,T] → V` solves `du/dt = L u`, `u(0) = u₀` when `u(t) ∈ V₀` for every `t` and the difference
quotient tends to `L u(t)`, with a right limit at `0` and a left limit at `T`. *Lean.*
`L : V →ₗ.[ℝ] V` (Mathlib's `LinearPMap`, as `Chapter08/Section02` already uses for closed
operators) with `Dense (L.domain : Set V)`, and the limit is `HasDerivWithinAt u (L ⟨u t, _⟩)
(Icc 0 T) t` — a derivative within a closed interval is precisely the book's one-sided convention
at the two ends, so no case split is needed. Well-posedness (Def 6.2.2) adds uniqueness as
`Set.EqOn` on `Icc 0 T`, not `∃!` over all of `ℝ → V`, since the book constrains `u` only there.

### D3. The solution operators and the generalized solution (Def 6.2.3)
*Book.* `S(t) u₀ = u(t)` on `V₀`, extended to `V` by the book's Theorem 2.4.1; `S(t) u₀` for
`u₀ ∈ V ∖ V₀` is the *generalized* solution. *Lean.* `S : ℝ → V →L[ℝ] V` obtained from the
extension theorem, which this surface already proves as `AtkinsonHan.Chapter02.theorem_2_4_1`. Note that
the equivalence theorem never uses the semigroup property (Prop 6.2.6); it is stated because the
book states it, and it must not become a hypothesis of Thm 6.2.11.

### D4. Consistency, stability, convergence (Def 6.2.7, 6.2.9, 6.2.10)
Three `Prop`-valued predicates on the pair `(S, C)`, in the specification style of the Krylov
layer — a scheme *is* consistent, it is not a bundle of data. Two readings are fixed here.
Consistency is written with the division cleared, `‖C(Δt) u(t) − u(t+Δt)‖ ≤ ε Δt`, so that no
`Δt⁻¹` occurs. Convergence quantifies over *sequences* `Δt i ∈ (0, Δ₀]` and `m i : ℕ` with
`m i · Δt i → t`, because that is the book's limit: it is not a limit along one sequence of step
sizes but along every refinement whose discrete time tends to `t`.

### D5. Two-level schemes (6.3.4)–(6.3.7)
*Book.* `v^{m+1} = Q v^m + h_t g^m`, `v^0 = u^0`, with `Q ∈ ℝ^{(N_x−1)×(N_x−1)}` depending on both
mesh parameters and the norm on `ℝ^{N_x−1}` left unspecified. *Lean.* An arbitrary real normed
space and `Q : E →L[ℝ] E`. Fixing `EuclideanSpace ℝ (Fin (N_x−1))` would be *less* faithful, since
the book's two worked examples use the maximum norm and a scaled two-norm on the same space and get
different stability conditions. The truncation error `τ^m` is defined by the relation (6.3.6) the
exact values satisfy, so it is data of the statement, not a derived quantity.

### D6. Saddle point (Def 8.6.1)
`IsSaddlePoint L A B u p`, on bare sets. The only formalization decision is Proposition 8.6.2: its
minimax equality is stated with `IsLeast` and `IsGreatest` of the images of the primal and dual
functionals, under explicit `BddAbove`/`BddBelow` hypotheses, rather than as an equality of `⨆`
and `⨅` over subtypes, because `sSup` of an unbounded set of reals is junk and the theorem would
then be false as stated for an unbounded Lagrangian.

### D7. Elliptic variational inequality (11.3.3), (11.3.8), (11.3.9), (11.3.12)–(11.3.14)
*Book.* Six displayed inequalities, differing in whether `j` is present, whether the constraint set
is a proper convex subset or the whole space, and whether the operator is `A` or the operator of a
bilinear form. *Lean.* **One** predicate, `IsVariationalInequalitySolution A j f K u`. The first
kind is `j = 0`, the second kind is `K = Set.univ`, and the bilinear cases are
`A = a.toOperator`. The book's device of extending `j` from `K` to `V` by `+∞` exists only to make
the two kinds one statement; in Lean the set argument already does that, so `j : V → ℝ` is total
with `ConvexOn ℝ K j` and `LowerSemicontinuousOn j K`, and no `EReal` appears. The datum is a
vector `f : V` rather than a functional, which is the book's own remark 11.3.4.

The discrete problem (11.4.3) is the *same* predicate with a different constraint set, so §11.4
introduces no new notion of discrete solution and its unique solvability is Theorem 11.3.1 again.

### D8. Strongly monotone and Lipschitz (11.3.1)–(11.3.2)
Already in this surface as `AtkinsonHan.Chapter05.StronglyMonotoneWith` (for Thm 5.1.4) with the bridges
`stronglyMonotoneWith_iff` and `lipschitzWith_toNNReal_iff`. Reuse them; do not restate. The
backbone takes both hypotheses unbundled, in exactly the shape `zarantonello` takes them, so the
bridge is the same one Chapter 5 already crosses.

### D9. Projection method for a second-kind equation (12.1.18)–(12.1.19)
*Book.* `P_n(λ − K) u_n = P_n f` with `u_n ∈ V_n`, equivalently `(λ − P_n K) u_n = P_n f` with
`u_n ∈ V`. *Lean.* The backbone's `IsProjectionMethodSolution` (`Numlib/Variational/ProjectionMethod`)
with the equivalence of the two forms as a surface lemma; the surface states everything for a single
bounded idempotent `P` and quantifies over `n` only where a limit is taken.

### D10. Collectively compact family (A1–A3, (12.4.53))
*Book.* `K_n u → K u` for every `u`, and `{K_n v : n ≥ 1, ‖v‖ ≤ 1}` has compact closure. *Lean.*
`IsCollectivelyCompact` is written in the shape of Mathlib's `IsCompactOperator` — a neighbourhood
of the origin whose union of images has compact closure — so that a one-element family is
collectively compact exactly when its member is a compact operator, and so that the two notions
share lemmas.

## 3. Three places where the surface must not follow the book's proof

* **Theorem 11.2.2.** The book derives the existence of the minimizer from its Theorem 3.3.12, which
  needs reflexivity and weak sequential compactness of bounded sets. Mathlib has neither, and
  `Numlib/Variational/Minimization.toml` records that. It is not needed: in a Hilbert space the
  parallelogram law makes any minimizing sequence Cauchy — the argument behind Mathlib's
  `exists_norm_eq_iInf_of_complete_convex` — and the convex lower semicontinuous `j` only needs the
  affine minorant of Lemma 11.3.5, which Mathlib has as `ConvexOn.exists_affine_le_of_lt`. The
  surface statement is the book's; only the route differs.
* **Theorem 11.4.1 versus Exercise 11.4.2.** The book proves convergence of the approximations by
  extracting a weakly convergent subsequence and passing to the limit through Minty's lemma. That
  argument needs `exists_subseq_weak_tendsto`, which does not exist yet. Exercise 11.4.2 reaches the
  same conclusion for internal approximations straight from the error inequality (11.4.7), with no
  weak compactness at all. Prove the exercise first; the general theorem should not hold up the
  chapter.
* **Theorem 12.4.4.** The book proves it for the Nyström operators on `C(D)`. Every step is
  Lemma 12.4.7 followed by Theorem 12.4.3, so the surface states the abstract version
  (`exists_norm_inverse_le_of_isCollectivelyCompactFamily`) now and adds the Nyström instance when
  `Numlib/IntegralEquations/Basic` and `Numlib/Approximation/Quadrature` exist.

## 4. Deferred and left out

Deferred, with the module named: AH Lemma 12.4.2 and Theorem 12.4.4 (the `C(D)` integral-operator
toolkit and a convergent quadrature rule); the Nyström and product-integration parts of §12.2 and
§12.5 (the interpolation, quadrature and trigonometric branches of `Numlib/Approximation/`).

Left out, with the obstruction: everything that names a domain `Ω` and hence a Sobolev space
(§8.1, §8.4, §8.5, §8.8, §11.1, §11.5, all of Chapter 7, all of Chapter 10 but Theorem 10.4.3, all
of Chapter 13); everything needing reflexivity or weak compactness in a Banach space (Theorem 8.6.3,
Theorem 8.8.5, and the reflexive-space theorems of §3.3 they cite); everything needing degree theory
(§5.5.1, §12.7.2); the specific difference schemes of Chapter 6; and Chapter 14, whose formalizable
core would be multivariate orthogonal polynomials on `L²(𝔹_d, W)`, which Mathlib does not have and
which no second source in the corpus asks for. `proposals/atkinsonhan-ch5-onward.md` §3 gives the
searches behind each of these.

## 5. Reading notes on the book text

* **Theorem 6.2.11, the backward direction.** The book's proof assumes without saying so that the
  family `{C(Δt)}` is uniformly bounded — that assumption is made when the family is introduced,
  a page earlier, and the bounded-`m` case of the argument uses it. The Lean statement must carry
  it as an explicit hypothesis; without it the step `sup_k ‖C(Δt_k)^{m_k}‖ ≤ sup_k ‖C(Δt_k)‖^{m_k}
  < ∞` is unjustified.
* **Lemma 11.3.5** is used in the proof of Theorem 11.3.1, not of Theorem 11.3.9; the book's
  sentence introducing it ("In the proof of Theorem 11.3.9, we applied the following result") is a
  slip.
* **Theorem 11.4.2** states its conclusion with `inf` over `K` and over `K_h`; the proof establishes
  the pointwise inequality for every `v ∈ K` and `v_h ∈ K_h`, which is the form the backbone node
  takes, the infima following by `le_ciInf`.
* **Theorem 12.4.3** is stated with `‖(T − S) S‖ < |λ| / ‖(λ − T)⁻¹‖`; the proof uses the equivalent
  `‖(λ − T)⁻¹‖ ‖(T − S) S‖ < |λ|`, which is the form to state in Lean, since it does not divide.
* **§12.4.3, assumption A2** is pointwise convergence `K_n u → K u`, not `‖K_n − K‖ → 0`; the whole
  point of the framework is that the latter fails for quadrature operators. Do not strengthen it.
* **Lemma 12.7.1** is the sharp second-order mean value inequality with the constant `½`, which the
  backbone already has as `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le`
  (`Numlib/Analysis/Calculus/MeanValue`, difficult-proof entry D15). Do not reprove it from
  Mathlib's `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`, which loses the `½`.
