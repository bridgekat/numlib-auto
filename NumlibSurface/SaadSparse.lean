import NumlibSurface.SaadSparse.Chapter01.Basics
import NumlibSurface.SaadSparse.Chapter01.Section07
import NumlibSurface.SaadSparse.Chapter01.Section08
import NumlibSurface.SaadSparse.Chapter01.Section09
import NumlibSurface.SaadSparse.Chapter01.Section10
import NumlibSurface.SaadSparse.Chapter01.Section11
import NumlibSurface.SaadSparse.Chapter01.Section12
import NumlibSurface.SaadSparse.Chapter01.Section13
import NumlibSurface.SaadSparse.Chapter02.Section02
import NumlibSurface.SaadSparse.Chapter02.Section03
import NumlibSurface.SaadSparse.Chapter02.Section04
import NumlibSurface.SaadSparse.Chapter02.Section05
import NumlibSurface.SaadSparse.Chapter03.Section02
import NumlibSurface.SaadSparse.Chapter03.Section03
import NumlibSurface.SaadSparse.Chapter03.Section04
import NumlibSurface.SaadSparse.Chapter04.Section01
import NumlibSurface.SaadSparse.Chapter04.Section02
import NumlibSurface.SaadSparse.Chapter04.Section03
import NumlibSurface.SaadSparse.Chapter05.Section01
import NumlibSurface.SaadSparse.Chapter05.Section03
import NumlibSurface.SaadSparse.Chapter05.Section04
import NumlibSurface.SaadSparse.Chapter06.Common
import NumlibSurface.SaadSparse.Chapter06.Section02
import NumlibSurface.SaadSparse.Chapter06.Section03
import NumlibSurface.SaadSparse.Chapter06.Section04
import NumlibSurface.SaadSparse.Chapter06.Section05
import NumlibSurface.SaadSparse.Chapter06.Section06
import NumlibSurface.SaadSparse.Chapter06.Section07
import NumlibSurface.SaadSparse.Chapter06.Section08
import NumlibSurface.SaadSparse.Chapter06.Section09
import NumlibSurface.SaadSparse.Chapter06.Section10
import NumlibSurface.SaadSparse.Chapter06.Section11
import NumlibSurface.SaadSparse.Chapter06.Section12
import NumlibSurface.SaadSparse.Chapter07.Section01
import NumlibSurface.SaadSparse.Chapter07.Section02
import NumlibSurface.SaadSparse.Chapter07.Section03
import NumlibSurface.SaadSparse.Chapter07.Section04
import NumlibSurface.SaadSparse.Chapter08.Section01
import NumlibSurface.SaadSparse.Chapter08.Section02
import NumlibSurface.SaadSparse.Chapter08.Section03
import NumlibSurface.SaadSparse.Chapter08.Section04
import NumlibSurface.SaadSparse.Chapter09.Section01
import NumlibSurface.SaadSparse.Chapter09.Section02
import NumlibSurface.SaadSparse.Chapter09.Section03
import NumlibSurface.SaadSparse.Chapter09.Section04
import NumlibSurface.SaadSparse.Chapter09.Section05
import NumlibSurface.SaadSparse.Chapter09.Section06
import NumlibSurface.SaadSparse.Chapter10.Section02
import NumlibSurface.SaadSparse.Chapter10.Section03
import NumlibSurface.SaadSparse.Chapter10.Section04
import NumlibSurface.SaadSparse.Chapter10.Section05
import NumlibSurface.SaadSparse.Chapter10.Section08
import NumlibSurface.SaadSparse.Chapter11
import NumlibSurface.SaadSparse.Chapter12.Section02
import NumlibSurface.SaadSparse.Chapter12.Section03
import NumlibSurface.SaadSparse.Chapter12.Section04
import NumlibSurface.SaadSparse.Chapter12.Section07
import NumlibSurface.SaadSparse.Chapter13.Section02
import NumlibSurface.SaadSparse.Chapter13.Section03
import NumlibSurface.SaadSparse.Chapter13.Section04
import NumlibSurface.SaadSparse.Chapter13.Section05
import NumlibSurface.SaadSparse.Chapter13.Section06
import NumlibSurface.SaadSparse.Chapter14.Section02
import NumlibSurface.SaadSparse.Chapter14.Section03
import NumlibSurface.SaadSparse.Chapter14.Section04
import NumlibSurface.SaadSparse.Chapter14.Section05
import NumlibSurface.SaadSparse.Chapter14.Section06
import NumlibSurface.SaadSparse.Common

/-!
# Saad, *Iterative Methods for Sparse Linear Systems*

The surface library for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition
(SIAM, 2003): sixty-eight modules, one per section of the book the project covers, reaching every
chapter that states a numbered result. Each module states the book's results in the book's own
terms — Saad's non-symmetric "positive definite", the splitting `A = D - E - F`, the algorithms
written out as Lean functions — and proves them by specializing the general backbone under
`Numlib/`. Almost nothing is proved here that is not proved there: the surface exists to test the
backbone against a published account of the subject, and to give a reader of the book a Lean name
for every result in it. This module imports the section modules and adds nothing of its own.

Plan and per-result book alignment: the groups under `plans/NumlibSurface/SaadSparse/`, one file
per section, where every numbered result of the book is a node carrying its source and, when it is
not formalized, the reason.

## Naming

A declaration is named for the result it states, so the name is the index: `theorem_6_29` is
Theorem 6.29, `proposition_6_13` is Proposition 6.13, `equation_6_43` is (6.43), `algorithm_6_9` is
Algorithm 6.9 and `problem_6_25` is the book's exercise P-6.25. Where one numbered result needs
several declarations — its separate clauses, or the two directions of an equivalence — a trailing
word tells them apart, as in `problem_6_25_le`. Objects the book names but does not number keep a
descriptive name (`arnoldiCGS`, `gmresFixed`, `smoothEta`), and each such definition carries an
equivalence lemma to its backbone counterpart; those lemmas are the load-bearing part of the
library.

Declarations live in `SaadSparse.ChapterNN` for the chapter — the chapter spelled in full, as the
module path spells it — except in §1.11–1.13, where results about a matrix are stated in `Matrix`
so that dot notation reads as the book does. `SaadSparse.Common`
holds the conventions shared by the whole library, and `SaadSparse.Chapter06.Common` the `r₀`, `β`,
`v₁`, `e₁`, `mEff` vocabulary shared by every Krylov method of Chapter 6.

## The outline

| § | module | subject |
|---|---|---|
| | `Common` | conventions: the matrix–operator glue, `⬝`, `lambdaMin`/`lambdaMax`, `complexify` |
| **1** | | *Background in Linear Algebra* |
| 1.1–1.6 | `Chapter01.Basics` | Matrices, eigenvalues, types of matrices, norms, subspaces |
| 1.7 | `Chapter01.Section07` | Orthogonal vectors and subspaces; Gram–Schmidt, QR, Householder |
| 1.8 | `Chapter01.Section08` | Canonical forms: similarity, Jordan, Schur, powers of a matrix |
| 1.9 | `Chapter01.Section09` | Normal and Hermitian matrices; the field of values |
| 1.10 | `Chapter01.Section10` | Nonnegative matrices, M-matrices, Perron–Frobenius |
| 1.11 | `Chapter01.Section11` | Positive-definite matrices; Theorems 1.34 and 1.35 (Bendixson) |
| 1.12 | `Chapter01.Section12` | Projectors; Lemma 1.36, Prop. 1.37, Theorem 1.38, Cor. 1.39 |
| 1.13 | `Chapter01.Section13` | Linear systems: existence, matrix `p`-norms, conditioning, (1.76) |
| **2** | | *Discretization of PDEs* |
| 2.2 | `Chapter02.Section02` | Finite differences: truncation error, the model matrices, upwind |
| 2.3 | `Chapter02.Section03` | Finite elements: the Galerkin system, stiffness matrix, assembly |
| 2.4 | `Chapter02.Section04` | Mesh refinement: the midpoint refinement preserves angles |
| 2.5 | `Chapter02.Section05` | The finite volume method and its sign structure |
| **3** | | *Sparse Matrices* |
| 3.2 | `Chapter03.Section02` | The adjacency graph and the patterns of products |
| 3.3 | `Chapter03.Section03` | Permutations, reorderings and irreducibility |
| 3.4 | `Chapter03.Section04` | Storage schemes: coordinate, CSR, MSR, diagonal, Ellpack |
| **4** | | *Basic Iterative Methods* |
| 4.1 | `Chapter04.Section01` | Jacobi, Gauss–Seidel, SOR, SSOR as splittings; the preconditioners |
| 4.2 | `Chapter04.Section02` | Convergence: Theorem 4.1, diagonal dominance, the SOR theory |
| 4.3 | `Chapter04.Section03` | Alternating direction methods; Peaceman–Rachford |
| **5** | | *Projection Methods* |
| 5.1–5.2 | `Chapter05.Section01` | Projection methods; Propositions 5.1–5.6, Theorem 5.7 |
| 5.3 | `Chapter05.Section03` | One-dimensional processes; Kantorovich, Theorems 5.9 and 5.10 |
| 5.4 | `Chapter05.Section04` | Additive and multiplicative projection processes |
| **6** | | *Krylov Subspace Methods, Part I* |
| 6.1–6.2 | `Chapter06.Section02` | Krylov subspaces and the grade of a vector; Prop. 6.1–6.3 |
| 6.3 | `Chapter06.Section03` | Arnoldi's method; Propositions 6.4–6.6 |
| | `Chapter06.Common` | `r₀`, `β`, `v₁`, `e₁`, `mEff` and the `v₁`-to-`r₀` bridge lemmas |
| 6.4 | `Chapter06.Section04` | FOM, IOM, DIOM; Propositions 6.7 and 6.8 |
| 6.5 | `Chapter06.Section05` | Givens rotations, GMRES, DQGMRES, FOM–GMRES relations, smoothing |
| 6.6 | `Chapter06.Section06` | The symmetric Lanczos algorithm; Theorem 6.19 |
| 6.7 | `Chapter06.Section07` | The conjugate gradient method; Proposition 6.20 |
| 6.8 | `Chapter06.Section08` | The conjugate residual method |
| 6.9 | `Chapter06.Section09` | GCR, ORTHOMIN, ORTHODIR; Lemma 6.21 |
| 6.10 | `Chapter06.Section10` | Optimality and the Faber–Manteuffel condition; Prop. 6.22 |
| 6.11 | `Chapter06.Section11` | Chebyshev min–max, Theorem 6.25, and the convergence bounds |
| 6.12 | `Chapter06.Section12` | Block Krylov methods: Ruhe's variant, block FOM and block GMRES |
| **7** | | *Krylov Subspace Methods, Part II* |
| 7.1 | `Chapter07.Section01` | Lanczos biorthogonalization; Proposition 7.1 and the relations |
| 7.2 | `Chapter07.Section02` | The two-sided Lanczos algorithm as a Petrov–Galerkin process |
| 7.3 | `Chapter07.Section03` | BCG and QMR; Proposition 7.3, Theorem 7.4, the residual smoothing |
| **8** | | *Methods Related to the Normal Equations* |
| 8.1 | `Chapter08.Section01` | The normal equations and their conditioning |
| 8.2 | `Chapter08.Section02` | Row projection methods: Cimmino, Kaczmarz, NE-SOR |
| 8.3 | `Chapter08.Section03` | CGNR and CGNE and their optimality properties |
| 8.4 | `Chapter08.Section04` | Saddle-point problems, Uzawa's method, Example 8.2 |
| **9** | | *Preconditioned Iterations* |
| 9.1 | `Chapter09.Section01` | Left, right and split preconditioning, and their conjugacy |
| 9.2 | `Chapter09.Section02` | Preconditioned CG: the three variants and their equality |
| 9.3 | `Chapter09.Section03` | Preconditioned GMRES; the `M`-inner-product form |
| 9.4 | `Chapter09.Section04` | FGMRES and flexible DQGMRES; Propositions 9.2 and 9.3 |
| 9.5 | `Chapter09.Section05` | Preconditioned CG for the normal equations |
| 9.6 | `Chapter09.Section06` | The Concus–Golub–Widlund algorithm |
| **10** | | *Preconditioning Techniques* |
| 10.2 | `Chapter10.Section02` | Jacobi, SOR and SSOR preconditioners |
| 10.5 | `Chapter10.Section05` | Approximate inverse preconditioners |
| 10.8 | `Chapter10.Section08` | Incomplete Gram–Schmidt (Algorithm 10.17); Proposition 10.17 |
| **11** | | *Parallel Implementations* |
| 11.5 | `Chapter11` | The jagged diagonal format; Example 11.1 |
| **12** | | *Parallel Preconditioners* |
| 12.3 | `Chapter12.Section03` | Polynomial preconditioners |
| **13** | | *Multigrid Methods* |
| 13.2 | `Chapter13.Section02` | The model problems and the spectra of the smoothers |
| 13.3 | `Chapter13.Section03` | Inter-grid operations: prolongation and restriction |
| 13.4 | `Chapter13.Section04` | The Galerkin coarse problem, Lemma 13.1, the multigrid cycles |
| 13.5 | `Chapter13.Section05` | The two subspaces, Theorem 13.3, Examples 13.7 and 13.8 |
| 13.6 | `Chapter13.Section06` | Algebraic multigrid: the quadratic form (13.68)-(13.69) |
| **14** | | *Domain Decomposition Methods* |
| 14.2 | `Chapter14.Section02` | Block Gaussian elimination and the Schur complement |
| 14.3 | `Chapter14.Section03` | The Schwarz alternating procedures |
| 14.4 | `Chapter14.Section04` | Induced preconditioners for `S`; Proposition 14.10 |
| 14.5 | `Chapter14.Section05` | Full matrix methods; Propositions 14.11 and 14.12 |
| 14.6 | `Chapter14.Section06` | Graph partitioning and spectral bisection |

There is no `Chapter06.Section01`: §6.1 is the chapter's introduction, and its one substantive
paragraph is stated with §6.2. `Chapter05.Section01` likewise covers §5.1 together with §5.2, which
share the book's own numbering (5.1)–(5.11), and `Chapter01.Basics` covers §1.1–1.6 in one module
because almost all of it is Mathlib restated in Saad's notation. Chapter 11, on parallel
implementations, states no theorem anywhere; its module carries its one example with mathematical
content, the jagged diagonal format of §11.5.4.

## The ambient setting

* Vectors of `ℝⁿ` and `ℂⁿ` are `EuclideanSpace 𝕜 (Fin n)`, matrices are `Matrix (Fin n) (Fin n) 𝕜`,
  and the book's `A x` is `Matrix.toEuclideanLin A x`, written `A ⬝ x` with the scoped notation of
  `Common`; Chapter 6 abbreviates the operator as `op A`. Componentwise statements use the plain
  function type `Fin n → 𝕜` with `A *ᵥ x` and `x ⬝ᵥ y`, related to the Euclidean picture by
  `WithLp.toLp 2` and `WithLp.ofLp`.
* Saad's inner product `(x, y) = ∑ xᵢ ȳᵢ` is Mathlib's `inner 𝕜 y x`: Mathlib's inner product is
  conjugate-linear in the *first* slot, Saad's in the second. Over `ℝ` the two agree, and every
  complex statement here is written so that only `re`, `‖·‖` or `⟪·,·⟫ = 0` matters.
* Definitions and algorithms are polymorphic in `𝕜` with `[RCLike 𝕜]`, so that §6.5.9 (complex
  GMRES) is literally the same code as §6.5.3. Each *numbered result* is stated at the book's own
  generality: over `ℝ` where the book says real, over `ℂ` for §6.5.9, Theorem 6.11, Theorem 1.35,
  Lemma 6.23, Theorem 6.24 and Proposition 6.32.
* `λ_min(H)` and `λ_max(H)` of a Hermitian matrix are `lambdaMin` and `lambdaMax` of `Common`, the
  extreme values of `Matrix.IsHermitian.eigenvalues`. The backbone takes such spectral hypotheses
  as quadratic-form bounds (`LinearMap.IsSymmetricBoundedBy`) rather than as lists of eigenvalues,
  and `Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin` is the bridge; that is why no proof
  here diagonalizes `A`.
* Real matrices are viewed as complex ones through `Matrix.complexify`, and `ρ(A)` is
  `Matrix.complexSpectralRadius A`.

## Indexing

The book numbers the Arnoldi, Lanczos and incomplete-orthogonalization vectors from `1`; here they
are `ℕ`-indexed from `0`, so `arnoldiCGS A v₁ j` is the book's `v_{j+1}` and
`arnoldiCoeff A v₁ i j` is its `h_{i+1,j+1}`. The same shift applies to the Givens quantities
`c_i`, `s_i`, `γ_i`. The CG, CR and GCR iterates are `0`-based already in the book and are left
alone. Matrices assembled from these data keep the book's dimensions: `V_m` is
`Matrix (Fin n) (Fin m) 𝕜`, `H_m` is `Matrix (Fin m) (Fin m) 𝕜` and `H̄_m` is
`Matrix (Fin (m + 1)) (Fin m) 𝕜`.

Division by a vanishing quantity is `0` in Lean, and that is exactly the book's "if `h_{j+1,j} = 0`
then Stop": every later vector is `0`, and the recurrences and expansion identities stay true past
the breakdown with no finiteness hypothesis. The book's companion instruction "set `m := j`" is
`mEff`, that is `min m (grade A v₁)`.

## Not formalized

Chapter 13 is complete; Chapters 1 to 9 and 12 are closed but for the items below. The group
files under `plans/NumlibSurface/SaadSparse/` carry the reasoning result by result, and say what
the declarations that are still to be written are to be.

* **§7.4**, the transpose-free variants — the BCG residual and direction polynomials, CGS,
  BiCGSTAB and TFQMR with their residual identities (7.32)–(7.83). The largest gap left in the
  book, and an unblocked one: §7.3 supplies everything it rests on.
* **§10.3**, the ILU factorizations — zero patterns (10.11), Theorems 10.1 and 10.2, Proposition
  10.4, ILU(0) and MILU — and **§10.4**, the `M̂` matrices (10.25)–(10.27) with Theorem 10.8.
* **§14.4–14.5**, the Schur-complement preconditioners: Proposition 14.10 for the preconditioner
  an ILU factorization induces, and (14.49)/(14.55) with Propositions 14.11 and 14.12.
* Block relaxation (§4.1.1, Algorithms 4.1–4.2), which waits on the backbone's block-projection
  layer, and one identity of §9.6.

Every numbered item of the book has a node, examples and definitions included. A worked example
over a small matrix or graph is a theorem here — the storage layouts of §3.4 and §11.5, the
assembly of Example 2.1, the interpolation weights of Example 13.9 — and a definition the book
names is restated even where Mathlib carries the content, `definition_1_1` for the spectrum and
`definition_1_23` for the entrywise order being the two of Chapter 1. What is left open is what
cannot be stated faithfully: measured tables and figures (Examples 8.1, 10.1, 11.2, 12.2, 13.4 and
13.5), and the examples whose data live only in a figure the source text does not reproduce
(Examples 3.3–3.6, on the mesh of Figure 2.10). The group files say so item by item.
Implementation advice and the exercises the text does not cite are out of scope. §1.13's
differentiability statement (1.74)–(1.75) is Mathlib calculus rather than a specialization of the
backbone, and the plan lists it as a backbone candidate.

## Where the book needs reading with care

Formalizing a book tests it. None of the following is a false theorem, but each is a place where
the printed statement is not what the proof needs, and the module says so on the declaration.

* **Definition 4.5** as printed sums over the *row* index with the column fixed — column sums —
  while the proofs of Theorems 4.6 and 4.9 use row sums. Both conventions are stated, following the
  backbone's `Matrix.IsStrictDiagDominant` (rows) and `Matrix.IsStrictColDiagDominant` (columns).
* **§1.12.4**, "`‖P‖₂ = 1` for any orthogonal projector", needs `P ≠ 0`: the zero matrix is the
  orthogonal projector onto `{0}`.
* **Corollary 1.39** is read with `y*` ranging over `M`, as an `IsLeast` statement; a `y* ∉ M` at
  the same distance would break the literal "iff".
* **§5.1.2**, "`WᵀAV` is nonsingular iff no vector of `AK` is orthogonal to `L`", is literally
  false for `A = 0`; it is read as the backbone's nondegeneracy hypothesis, that `u ∈ K` and
  `u ≠ 0` imply `A u ∉ Lᗮ`.
* **Proposition 5.6** presupposes that `Q_K^L` exists, that is `K ∩ Lᗮ = {0}`; without it the
  statement fails, so the hypothesis is added.
* **Proposition 6.9** is stated with "`m` Arnoldi steps completed" (`m ≤ grade`) alongside the
  printed `m ≤ n`, because the proof uses it; Propositions 6.12–6.13, Lemma 6.16 and Proposition
  6.17 likewise make explicit the nonsingularity of `H_m` and the nonvanishing of `‖r^G_m‖` that
  their proofs need.
* **Theorem 6.25** reads "non-empty interval `[α, β]`" as nondegenerate, `α < β`, since (6.113)
  divides by `β - α`.
* **Theorem 4.16** reuses the name `M_SOR` for the SOR iteration matrix where (4.26) uses it for
  the preconditioner; the two are named apart here.
* **Theorem 14.6** needs its subdomains to have no coupling in `A`, which for a positive definite
  `A` is stronger than the disjointness the statement asks for; `theorem_14_6` carries the
  hypothesis its proof uses.

Chapter 13 is the one place where the printed text is wrong rather than merely imprecise, in four
statements, each corrected on the declaration that states it:

* **Example 13.2**'s restriction operator is off by a factor of four: the book's own stencil with
  full weighting gives a quarter of what it writes, the factor being the ratio of the two mesh
  squares.
* **Example 13.3** gives the Gauss–Seidel smoother as `(D - E)⁻¹ F`, where it is `(D - E)⁻¹`.
* **Lemma 13.1**'s third clause names the restriction where its own proof gives the prolongation.
* **The two-dimensional V-cycle constant** `7/3` does not follow from the book's own recurrence:
  the geometric sum is `4/3`.

## References

* Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003.
-/
