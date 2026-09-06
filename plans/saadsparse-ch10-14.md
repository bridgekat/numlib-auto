<!--
The per-result Lean statements quoted below are historical wherever the result exists: the tracker
plan (the TOML group files beside this document) is the authority on which declarations exist, and
the source is the authority on what they say. Where the two disagree, this document is wrong.

What is worth reading here is the book alignment: which numbered result maps to which declaration,
how each book-specific definition relates to the backbone, what was deferred and why, and what was
deliberately left out. The skip list and the full coverage table are in
`plans/proposals/plan-saad10.md`.
-->

# Surface plan: Saad — Chapters 10–14

The surface `NumlibSurface.SaadSparse` for Saad, *Iterative Methods for Sparse Linear Systems*
(2nd edition), Ch. 10 (preconditioning techniques), Ch. 11 (parallel implementations), Ch. 12
(parallel preconditioners), Ch. 13 (multigrid) and Ch. 14 (domain decomposition). Conventions are
those of `plans/saadsparse-ch1-4-5.md` §0: real `n × n` matrices, `EuclideanSpace ℝ (Fin n)` for
vectors, `Matrix.toEuclideanLin` for the action, names `SaadSparse.Chapter13.theorem_13_3`,
`equation_13_43`, and docstrings carrying the book statement.

## 1. What this slice is, and is not

These five chapters are the least uniform stretch of the book. Two of them (11, and most of 12) are
about machines: storage formats, vector pipelines, message passing, colourings for parallel
triangular solves. They contain no numbered result — Chapter 11 has none of any kind, Chapter 12
has none either — and nothing is planned from them beyond §12.3. Two of them (13 and 14) look like
applied PDE chapters and turn out not to be: once the grids are stripped away, multigrid convergence
is a statement about an energy-orthogonal projector and a pair of dual seminorms, and the Schwarz
theory is a statement about a family of orthogonal projectors in a Hilbert space. Both are fully
planned. Chapter 10 is in between: an existence theorem for M-matrices with a genuinely hard proof,
a handful of one-line estimates, and a great deal of implementation.

The single design decision that makes 13 and 14 tractable is to state their theory in the *energy
inner product* and let `WithEnergy` (`Numlib/Analysis/InnerProductSpace/Energy`) carry it. Saad's
coarse-grid correction `I - I_H^h A_H⁻¹ I_h^H A_h` and his Schwarz projector `R_iᵀ A_i⁻¹ R_i A` are
then literally `Submodule.starProjection` in that space, his Lemma 13.1 and the self-adjointness
computation at the head of §14.3.4 are `starProjection`'s own properties, and his Theorems 13.3 and
14.9 become short. The mesh never appears.

The second decision is to make the model problems real objects rather than folklore.
`Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz` proves that `tridiag(-1,2,-1)` has eigenvalues
`4 sin²(kπ/2(n+1))` with sine eigenvectors forming an orthogonal basis, and
`Numlib/LinearAlgebra/Matrix/KroneckerSum` lifts that to the 2-D Laplacean via `A ⊗ 1 + 1 ⊗ B`.
Without those two modules every statement of §13.2 would be a definition with nothing behind it;
with them, "the oscillatory modes are damped by a factor at most `3/4` independently of `h`" is a
theorem.

## 2. Files

| File | Book |
|---|---|
| `NumlibSurface/SaadSparse/Chapter10/Section02.lean` | §10.2: (10.4)–(10.9), `M_SGS = LU`, `A − LU = −E D⁻¹ F` |
| `NumlibSurface/SaadSparse/Chapter10/Section03.lean` | §10.3: (10.11), Thm 10.1–10.2, Prop 10.3–10.4, ILU(0), Def 10.5, MILU |
| `NumlibSurface/SaadSparse/Chapter10/Section04.lean` | §10.4.1–10.4.2: `M̂` matrices (10.25)–(10.27), Thm 10.8 |
| `NumlibSurface/SaadSparse/Chapter10/Section05.lean` | §10.5: (10.43)–(10.48), Prop 10.9–10.14, Lemma 10.15 |
| `NumlibSurface/SaadSparse/Chapter10/Section08.lean` | §10.8.3: Prop 10.17 |
| `NumlibSurface/SaadSparse/Chapter12/Section02.lean` | §12.2: the overlapping block-Jacobi residual identity |
| `NumlibSurface/SaadSparse/Chapter12/Section03.lean` | §12.3: (12.3)–(12.14), Alg 12.1 |
| `NumlibSurface/SaadSparse/Chapter12/Section04.lean` | §12.4: the red–black block form and the reduced system (12.18) |
| `NumlibSurface/SaadSparse/Chapter12/Section07.lean` | §12.7.2: (12.24)–(12.25), the Winget regularization |
| `NumlibSurface/SaadSparse/Chapter13/Section02.lean` | §13.2: (13.4)–(13.14), (13.19)–(13.29) |
| `NumlibSurface/SaadSparse/Chapter13/Section03.lean` | §13.3: (13.30)–(13.38) |
| `NumlibSurface/SaadSparse/Chapter13/Section04.lean` | §13.4: (13.39)–(13.47), Lemma 13.1, Thm 13.2, Example 13.6 |
| `NumlibSurface/SaadSparse/Chapter13/Section05.lean` | §13.5: (13.57)–(13.65), Thm 13.3 |
| `NumlibSurface/SaadSparse/Chapter13/Section06.lean` | §13.6: (13.68)–(13.69) only |
| `NumlibSurface/SaadSparse/Chapter14/Section02.lean` | §14.2.1–14.2.2, §14.2.4–14.2.5: (14.4)–(14.7), Prop 14.1, (14.16), (14.20) |
| `NumlibSurface/SaadSparse/Chapter14/Section03.lean` | §14.3: (14.24)–(14.43), Prop 14.3, Lemma 14.4, Thm 14.5–14.9 |
| `NumlibSurface/SaadSparse/Chapter14/Section04.lean` | §14.4.1–14.4.2: Prop 14.10, the probing reconstruction |
| `NumlibSurface/SaadSparse/Chapter14/Section05.lean` | §14.5: (14.49)–(14.60), Prop 14.11–14.12 |
| `NumlibSurface/SaadSparse/Chapter14/Section06.lean` | §14.6.1, §14.6.3: Def 14.13, the spectral-bisection identity |

There is no `Chapter11` directory: see §5.

## 3. New backbone demanded by this slice

| Module | For |
|---|---|
| `Numlib/LinearAlgebra/Matrix/SchurComplement` | §14.2 (Prop 14.1), §14.5 (Prop 14.11–14.12), §12.4.2, and — through the `1 × 1`-pivot case — Saad Thm 10.1 |
| `Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz` | §13.2 1-D model problem |
| `Numlib/LinearAlgebra/Matrix/KroneckerSum` | §13.2 2-D model problem |
| `Numlib/RingTheory/Polynomial/KernelPolynomial` | §12.3.3 least-squares polynomials |
| `Numlib/LinearSolve/Preconditioner/{ILU,Polynomial,Chebyshev,ApproximateInverse}` | §10.3–10.5, §12.3 |
| `Numlib/LinearSolve/Multigrid/{Basic,TwoGrid,FullMultigrid}` | §13.4–13.5 |
| `Numlib/LinearSolve/DomainDecomposition/{Schwarz,Schur}` | §14.3, §14.4.1, §14.5 |

Additions to groups owned by other plans (M-matrix characterizations, the `shifted` recurrence, a
shared `WithEnergy.projection`) are in `plans/proposals/plan-saad10.md` §1.

## 4. Book-specific definitions and how they relate to the backbone

* **Saad's `ILU_P`** (§10.3.1) is `Matrix.IsILU P A L U`, stated declaratively: `L` unit lower, `U`
  upper, both zero on `P`, and `L U = A` off `P`. Saad defines the factors by an algorithm and then
  proves (Prop 10.3) that two loop orders agree; the declarative form is what every downstream
  statement uses, is satisfied by both loop orders, and does not pretend the factors are unique
  (they are not — Saad says so before Algorithm 10.4). Because it does not, `Matrix.IsILU` does
  *not* imply Prop 10.3, so the two loops are written down separately in
  `Chapter10/Section03.lean` (`kijSweep`, `ikjSweep`) and the proposition is proved there.
* **Saad's `M̂` matrix** (10.25)–(10.27) is weaker than his M-matrix: no nonsingularity, no
  nonnegative inverse, but a strictly negative sum of the entries to the right of the diagonal in
  every row but the last. It is a separate predicate, `Matrix.IsMHat`, not a specialization of
  `Matrix.IsMMatrix`.
* **The tensor sum `T_x ⊕ T_y`** of (13.12) is `Matrix.kroneckerSum` over Mathlib's `⊗ₖ`.
* **Saad's restriction `I_h^H`** is the *scaled* adjoint of the prolongation, `2^{-d} (I_H^h)ᵀ` by
  (13.37). The backbone takes the unscaled adjoint; the scaling cancels in
  `A_H = I_h^H A_h I_H^h` composed with `I_H^h A_H⁻¹ I_h^H`, and `equation_13_35` /
  `coarseProjection_eq_of_scaled` record that.
* **Saad's smoother** is given by its iteration `u ← S u + g`, but every statement of Ch. 13 is
  about the error, so the backbone takes the *error propagation operator* `S = I - B A` as primary
  (13.40)–(13.42) and derives `B`. The classical smoothers are then
  `Stationary.Splitting.iterationOperator` of the corresponding splitting.
* **Saad's Schwarz restriction matrices** `R_i` (§14.3.1) are boolean row selections; `A_i = R_i A
  R_iᵀ`, `P_i = R_iᵀ A_i⁻¹ R_i A`, `T_i = R_iᵀ A_i⁻¹ R_i`. The surface proves
  `P_i = WithEnergy`-projection onto `span {e_j : j ∈ S_i}` and everything else follows from the
  backbone. `A_i` is the Galerkin coarse operator of that subspace, so `Multigrid.galerkinCoarse`
  and the Schwarz local matrix are one definition seen twice.
* **The Frobenius inner product** `⟨X, Y⟩ = tr(Yᵀ X)` of (10.48) is a surface definition: Mathlib
  has the Frobenius *norm* as a scoped instance but no inner product space structure on `Matrix`.
  The surface supplies the isometry with `EuclideanSpace ℝ (n × n)`, which is how Prop 10.9 reaches
  the backbone's general least-squares derivative.
* **Saad's `T_k`** of §12.3.2 is `Polynomial.Chebyshev.shifted k α β 0`, already in the library from
  §6.11: `shifted m a b γ` is `t ↦ T_m((b + a − 2t)/(b − a)) / T_m((b + a − 2γ)/(b − a))`, which at
  `γ = 0` is exactly `C_k((θ − t)/δ)/C_k(θ/δ)`. That identification is the point where Chapter 12
  meets Chapter 6, and it means Chebyshev acceleration inherits the min–max optimality already
  proved.

**Two errata.** The closing display of Example 13.6 is wrong: Saad bounds `‖A_h⁻¹‖ = 1/λ_min`
using `sin x / x ≥ 1 - x²/6` at `x = πh/2`, but `λ_min = π² (sin x / x)²` carries a *square*, so the
bracket must be squared too; `1 - (πh/2)²/6` is not a lower bound for `(sin x/x)²` — at `h = 1/2`
they are `0.8105…` and `0.8971…`. `SaadSparse.Chapter13.example_13_6_le` states the corrected form,
and `example_13_6` itself is stated with the exact `λ_min` and is free of the slip.

The last equality of Saad (13.61), `𝒯_h = Null(I_h^H)`, is false. The
oscillatory subspace is `Null(I_h^H A_h)`, the `A_h`-orthogonal complement of `Ran(I_H^h)`,
while `Null(I_h^H)` is its Euclidean orthogonal complement; the argument of §13.5.1 compares two
decompositions with the same first summand and concludes that their second summands agree,
which does not follow. `SaadSparse.Chapter13.oscillatorySubspace_ne_ker_of_restriction` is a
counterexample with `tridiag(-1, 2, -1)` of order two. Nothing in the chapter uses the printed
form: the proof of Theorem 13.3 needs only that the oscillatory subspace is `A_h`-orthogonal to
`Ran(I_H^h)`.

## 5. Chapter 11, and the rest of what is not planned

Chapter 11 was read section by section rather than assumed: §11.1–11.4 (forms of parallelism,
architectures, types of operations), §11.5 (CSR/CSC, diagonal, Ellpack–Itpack and jagged-diagonal
matrix–vector products, distributed sparse matrices) and §11.6 (parallelism in forward sweeps,
level scheduling). It contains Algorithms 11.1–11.8 and Examples 11.1–11.2, and no theorem,
proposition, lemma, corollary or numbered definition. Level scheduling comes closest to having
content — the levels are the depths of the nodes of the dependency DAG of the triangular solve, and
the number of levels bounds the parallel depth — but the book states no property of them. Nothing
is planned and no surface group exists for the chapter.

The full skip list, with the obstruction named for each item, is `plans/proposals/plan-saad10.md`
§3. Its four largest entries: Saad Thm 10.2's graph-theoretic companions (Thm 10.6–10.7, needing a
symbolic elimination model); the results the book states without proof (Thm 10.6, 10.16, 10.18,
14.16); the algebraic-multigrid heuristics of §13.6, which Saad marks as non-rigorous himself; and
Theorem 14.2, which is a translation between two descriptions of the multiplicative Schwarz sweep
and needs the vertex-based partitioning bookkeeping of §14.2.3.

Several entries of that list were revisited and are now proved: Prop 10.3 (§10.3.1), §12.2's
residual identity, §12.4.2's reduced system, §12.7.2's Winget claim, Example 13.6, §14.2.4's
`S = ∑ S_i`, §14.4.2's probing reconstruction, and Definition 14.13. What is left, with the
obstruction in each case, is:

* **Thm 10.6 and 10.7** (fill-paths): a symbolic model of Gaussian elimination on a graph — the
  sequence of elimination graphs, or reachable sets through eliminated vertices — which nothing
  else in the library would use. Mathlib has `SimpleGraph.Walk` but no elimination graph. Saad
  quotes Thm 10.6 from Rose–Tarjan without proof.
* **(10.19)–(10.20)**, the ILU(0) stencil recurrence of §10.3.4: formalizable, low value — the
  explicit solution of the `IsILU0` constraints for the five-diagonal family, whose only difficulty
  is index bookkeeping at the grid boundary.
* **Thm 10.16** (§10.7, block ILU for block-tridiagonal M-matrices): needs the block-tridiagonal
  splitting as an object, the recurrence (10.79)–(10.80), and the "tridiagonal part of the inverse
  of a tridiagonal matrix" of §10.7.1. Saad writes "the following theorem can be shown" and gives no
  proof; the trap is that `Ω^{(3)}` is a *truncation* of the inverse, so the `Δ_i` are not Schur
  complements and the usual lemmas do not apply.
* **Thm 10.18** (§10.8.3): the incomplete Gram–Schmidt side exists in `Chapter10/Section08.lean`,
  but the incomplete Cholesky side does not — there is no `IsIC` companion to `Matrix.IsILU` — and
  Saad states the theorem without proof, citing Wang–Gallivan–Bramley.
* **Thm 14.2** (Chan–Goovaerts), as above.
* **The matrix form of §14.2.5**: the recurrence is proved at one eigenvalue; carrying it back to
  `T_k = f_k(B)` needs the inverse of `T_k` read on eigenvectors, `T_n = S_1` needs the block `LU`
  factorization of a block tridiagonal matrix, and the limit `Ŝ = (B + √(B² - 4I))/2` needs a
  matrix square root.
* **Defs 14.14–14.15 and Thm 14.16**: two definitions whose only consumer is a computational-geometry
  theorem needing stereographic projection into `S^d`, centerpoints and a random-great-circle
  argument. Def 14.13 is stated (§14.6.1); these are not.

## 6. Where the work is

`Matrix.IsMMatrix.exists_isILU` (Saad Thm 10.2) is the one ★★★ item: an induction over the index
set in which each step is a `1 × 1`-pivot Schur complement, Ky Fan's theorem keeps the M-matrix
property, and the dropped entries move the matrix *up* in the entrywise order, where Saad Thm 1.33
recovers it. It is also the only item in the slice that depends on plans owned by others
(`Matrix/Order` and `Stationary/RegularSplitting`, plus the three M-matrix characterizations
proposed for the latter), so it should be scheduled after those.

Two ★★ items follow: `Schwarz.le_re_inner_additiveOperator` and
`Schwarz.sum_norm_starProjection_sq_le` (Saad Thm 14.7 and Lemma 14.8), both resting on the
vector-valued Cauchy–Schwarz inequality that should be proved first as `Schwarz.inner_sum_le`.

Everything else is routine once the modules above exist. The two multigrid theorems are short —
Thm 13.3 is four inequalities, Thm 13.2 is an induction on a real recursion — and the model-problem
spectra are trigonometry. `Numlib/LinearAlgebra/Matrix/{SchurComplement,Tridiagonal,KroneckerSum}`
and `Numlib/RingTheory/Polynomial/KernelPolynomial` have no dependency inside this slice and can be
started immediately; `lake exe tracker ready` lists them.
