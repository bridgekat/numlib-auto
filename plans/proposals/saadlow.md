# Proposal: Saad, *Iterative Methods for Sparse Linear Systems*, the uncovered part of Ch. 1-6

Everything in this file is something the planning branch `agent/plan-saadlow` could not put into a
new TOML group: additions to group files another agent may be holding, changes to declarations that
already exist, the explicit skip list, and the coverage summary.

The slice is: §1.1–1.10, Ch. 2, Ch. 3, §4.3, and the gaps left in Ch. 6. The new groups it created
are

| new group | nodes | what it is for |
|---|---|---|
| `Numlib/LinearAlgebra/Matrix/PerronFrobenius` | 7 | Saad Prop 1.24(5), Cor 1.27, Thm 1.28, Thm 1.25 |
| `Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz` | 6 | `tridiag(a, b, a)` and the discrete sine basis |
| `Numlib/LinearAlgebra/Matrix/KroneckerSum` | 4 | `A ⊗ I + I ⊗ B` and its spectrum |
| `Numlib/LinearAlgebra/Matrix/QR` | 5 | Householder reflectors, `X = Q R` |
| `Numlib/LinearAlgebra/Sparse/{Pattern,Reordering}` | 6 + 4 | the graph of a matrix; orderings to block structure |
| `Numlib/Combinatorics/SimpleGraph/{Coloring,IndepSet,LevelSet}` | 4 + 2 + 4 | the three graph bricks Mathlib lacks |
| `Numlib/LinearSolve/Stationary/ADI` | 6 | Peaceman–Rachford, and the theorem §4.3 asserts |
| `NumlibSurface/SaadSparse/Chapter01/{Basics,Section07,Section08,Section09,Section10}` | 12 + 5 + 8 + 13 + 9 | §1.1–1.10 |
| `NumlibSurface/SaadSparse/Chapter02/{Section02,Section05}` | 18 + 4 | finite differences, finite volumes |
| `NumlibSurface/SaadSparse/Chapter03/{Section02,Section03}` | 3 + 8 | adjacency graph, permutations, reorderings |
| `NumlibSurface/SaadSparse/Chapter04/Section03` | 5 | §4.3 |

---

## 1. Additions to existing groups

### 1.1 `Numlib/Eigen/Normal` - the orthonormal eigenbasis of a normal operator

This is the most important entry in this file: it is the one backbone gap in §1.9, and it is small.

`Numlib/Eigen/Normal` proves that the eigenspaces of a normal operator over an algebraically closed
field are pairwise orthogonal (`LinearMap.IsStarNormal.orthogonalFamily_eigenspaces`), that they
span (`iSup_eigenspace_eq_top`) and that they decompose the space
(`direct_sum_isInternal`) - every ingredient of Saad Theorem 1.14 - but it stops short of
assembling them into a basis, which is what "unitarily similar to a diagonal matrix" means. Two
nodes, mirroring `LinearMap.IsSymmetric.eigenvectorBasis` and `Matrix.IsHermitian.spectral_theorem`
exactly:

* **group** `Numlib/Eigen/Normal`, **id** `LinearMap.IsStarNormal.eigenvectorBasis`,
  **kind** definition, **deps** `LinearMap.IsStarNormal.direct_sum_isInternal`,
  `LinearMap.IsStarNormal.orthogonalFamily_eigenspaces`.
  *An orthonormal basis of eigenvectors of a normal operator on a finite-dimensional inner product
  space over an algebraically closed `RCLike` field, with `apply_eigenvectorBasis` naming the
  eigenvalue at each index. `DirectSum.IsInternal.collectedOrthonormalBasis` of the orthogonal
  family, exactly as `LinearMap.IsSymmetric.eigenvectorBasis` is built.*
* **group** `Numlib/Eigen/Normal`, **id** `Matrix.IsStarNormal.spectral_theorem`, **kind** theorem,
  **deps** `LinearMap.IsStarNormal.eigenvectorBasis`, `Matrix.isStarNormal_toEuclideanLin_iff`.
  *The matrix form: `IsStarNormal A ↔ ∃ U ∈ Matrix.unitaryGroup n ℂ, ∃ d, Uᴴ * A * U =
  Matrix.diagonal d`, the reverse direction being a computation. Saad Theorem 1.14.*

Why here rather than in a new module: `Eigen/Normal` is the library's normal-operator theory, it
already proves everything these two need, and a second module would split the theory in half.
`NumlibSurface/SaadSparse/Chapter01/Section09`'s `theorem_1_14` and `corollary_1_16` are blocked on
them, as is Saad Lemma 1.13's alternative proof.

### 1.2 `Numlib/LinearAlgebra/Matrix/Order` - the two missing clauses of Saad Prop 1.24

`Order.toml` (being written on another branch) has clauses 2 and 3 of Saad Proposition 1.24 and
Proposition 1.26. Clauses 1 and 4 are missing, and Saad §1.10 uses both.

* **id** `Matrix.EntrywiseLE.antisymm`, **kind** theorem, **deps** `Matrix.EntrywiseLE`.
  *`EntrywiseLE A B → EntrywiseLE B A → A = B`, with the companions `EntrywiseLE.refl` and
  `EntrywiseLE.trans` (Saad Prop 1.24 clause 1). Entrywise from the order on the entries; the
  natural packaging is a scoped `PartialOrder` instance in a `Matrix.EntrywiseOrder` namespace, so
  that it cannot collide with Mathlib's Loewner instance.*
* **id** `Matrix.EntrywiseLE.transpose`, **kind** theorem, **deps** `Matrix.EntrywiseLE`.
  *`EntrywiseLE A B → EntrywiseLE Aᵀ Bᵀ` (Saad Prop 1.24 clause 4).*

Why here: they are the order calculus the module exists for, and restating them in
`PerronFrobenius` would be the duplication the plan forbids. Clause 5, the monotonicity of the
induced norms, is deliberately *not* proposed here: it is analytic rather than order-theoretic,
its only consumer is Saad Theorem 1.28, and it is a node of the new `PerronFrobenius` group.

### 1.3 `Numlib/LinearSolve/Stationary/RegularSplitting` - the M-matrix characterizations

`RegularSplitting.toml` says "Saad Thm 1.31-1.33 are not needed by any surface and are not
planned". They are now: `NumlibSurface/SaadSparse/Chapter01/Section10` states all three. They
belong beside `Matrix.IsMMatrix`, which that group owns.

* **id** `Matrix.isMMatrix_iff_complexSpectralRadius_jacobi_lt_one`, **kind** theorem, **deps**
  `Matrix.IsMMatrix`, `Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff`,
  `Matrix.jacobiSplitting_iterationOperator`.
  *Saad Thm 1.31: for a real matrix with positive diagonal and nonpositive off-diagonal entries,
  `A.IsMMatrix ↔ complexSpectralRadius (jacobiSplitting A h).iterationOperator < 1`. Thm 1.29
  applied to the Jacobi iteration matrix `B = 1 - D⁻¹ A`, which those two sign conditions make
  entrywise nonnegative, with `A = D * (1 - B)`.*
* **id** `Matrix.isMMatrix_of_offDiag_nonpos_of_inv_entrywiseNonneg`, **kind** theorem, **deps**
  `Matrix.isMMatrix_iff_complexSpectralRadius_jacobi_lt_one`.
  *Saad Thm 1.32: nonpositive off-diagonal entries, nonsingularity and an entrywise nonnegative
  inverse already force positive diagonal entries, so three of Definition 1.30's four clauses
  imply the fourth. From `(A * A⁻¹) i i = 1`.*
* **id** `Matrix.IsMMatrix.mono`, **kind** theorem, **deps**
  `Matrix.isMMatrix_iff_complexSpectralRadius_jacobi_lt_one`,
  `Matrix.complexSpectralRadius_le_of_entrywiseLE`.
  *Saad Thm 1.33: if `EntrywiseLE A B`, `B` has nonpositive off-diagonal entries and `A` is an
  M-matrix, so is `B`. The book's chain of entrywise inequalities between the two Jacobi matrices,
  then Thm 1.28.*

**Recommended refactor, which the orchestrator may take or leave.** `RegularSplitting` currently
owns three items that are not about splittings at all: `Matrix.IsMMatrix`, the weak Perron theorem
`Matrix.EntrywiseNonneg.exists_hasEigenvector_complexSpectralRadius`, and Saad Thm 1.29
`Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff`. They are nonnegative-matrix theory and
their natural home is beside the new `Numlib/LinearAlgebra/Matrix/PerronFrobenius`, which cannot
depend on them today without a `LinearAlgebra/Matrix` module importing `LinearSolve` - the wrong
direction for a module the plan calls an upstreaming candidate. Moving them (together with the
three nodes above) into `PerronFrobenius`, or into a sibling `Numlib/LinearAlgebra/Matrix/MMatrix`,
would leave `RegularSplitting` with exactly Saad Def 4.3 and Thm 4.4. The move is free right now,
because every node concerned is open, and it becomes expensive once the module is written. **The
plan on this branch is correct either way**: `PerronFrobenius` was deliberately written to depend
only on `Matrix/Order` and `Matrix/Complexify`, and no new node duplicates an existing id.

### 1.4 `NumlibSurface/SaadSparse/Chapter04/Section02` - Property A is two-colourability

* **id** `SaadSparse.Chapter04.hasPropertyA_iff_colorable_two`, **kind** theorem, **deps**
  `SaadSparse.Chapter04.HasPropertyA`, `Matrix.adjGraph`, `Matrix.apply_eq_zero_of_coloring_eq`.
  *Saad Definition 4.11 is exactly the two-colourability of the adjacency graph:
  `A.HasPropertyA ↔ (Matrix.adjGraph A).Colorable 2`, with the block form (4.42) -
  `∃ σ, A.submatrix σ σ` has diagonal diagonal blocks in a two-block split - as
  `hasPropertyA_iff_exists_submatrix`.*

Why there rather than in `Chapter03/Section03`: `HasPropertyA` is defined in the Chapter 4 file, and
the import order runs Chapter 3 → Chapter 4, so the bridge can only be stated on the Chapter 4
side. It matters because it turns the graph machinery of `Chapter03/Section03` into a way of
*checking* Property A, which the Chapter 4 surface currently has no means of doing, and because
Saad's own remark that a consistently ordered matrix has Property A becomes a corollary.

### 1.5 `NumlibSurface/SaadSparse/Chapter06/Section03` - identify the two Householder reflectors

* **id** `SaadSparse.Chapter06.householder_eq_toEuclideanLin`, **kind** theorem, **deps**
  `SaadSparse.Chapter06.householder`, `Matrix.householder`.
  *The `EuclideanSpace` reflector `SaadSparse.Chapter06.householder w` of Algorithm 6.3 is
  `Matrix.toEuclideanLin (Matrix.householder w)` of `Numlib/LinearAlgebra/Matrix/QR`, and the
  vector `householderVec` of Saad (1.24)-(1.26) is the one
  `Matrix.householder_mulVec_eq_smul_single` names.*

Why there: Chapter 6 already has the reflectors, written for Algorithm 6.3; Chapter 1 needs Saad
(1.20)-(1.28) and cannot import Chapter 6. Without this lemma the library would carry the same
object twice under two names, which is the outcome the plan most wants to avoid.

### 1.6 `NumlibSurface/SaadSparse/Chapter06/Section10` - the provable half of Theorem 6.24

* **id** `SaadSparse.Chapter06.theorem_6_24_mpr`, **kind** theorem, **deps** `SaadSparse.Chapter06.IsCGs`,
  `SaadSparse.Chapter06.ν`, `SaadSparse.Chapter06.lemma_6_23`.
  *`((minpoly ℂ A).natDegree ≤ s ∨ (IsStarNormal A ∧ ν A ≤ s - 1)) → IsCGs A s`, the direction of
  the Faber–Manteuffel theorem that follows from what is already proved. In the first case every
  starting vector has grade at most `s`, so the index range `i + s ≤ j ≤ μ(v₁) - 1` of `IsCGs` is
  empty and the conclusion is vacuous. In the second case `Aᴴ = q(A)` with `deg q ≤ s - 1`, so
  `⟪A v_j, v_i⟫ = ⟪v_j, q(A) v_i⟫ = 0` for `j ≥ i + s`, which is the argument of Proposition 6.22,
  already in the file.*

Why there: `IsCGs`, `ν` and `lemma_6_23` are all in that file, the module is written, and this
closes the only half of Theorem 6.24 that is reachable (see §3 for the other half).

### 1.7 Housekeeping

* `NumlibSurface/SaadSparse/Chapter01.toml`'s `desc` reads "spectral facts, projectors and
  conditioning (§1.11–1.13)". It should now read §1.1–1.13, listing the five new section files.
* `plans/backbone.md` §8.1's `SaadSparse` table has no rows for §1.1–1.10, Ch. 2, Ch. 3 or §4.3;
  §11 of that file (appended on this branch) supplies them.

---

## 2. Changes to existing declarations

1. **Saad's irreducibility should be defined once, in the backbone.**
   `plans/saadsparse-ch1-4-5.md` D15 plans a surface definition
   `SaadSparse.Chapter04.IsIrreducible A := Matrix.IsIrreducible (A.map ‖·‖)` inside
   `Chapter04/Section02`, and §3 item 4 of that document asks
   `Numlib/LinearSolve/Stationary/DiagDominant` to adopt it as *its* definition too. The new
   `Numlib/LinearAlgebra/Sparse/Pattern` defines exactly that, as `Matrix.IsPatternIrreducible`,
   with the equivalences to strong connectivity of the adjacency digraph and to the block
   triangular form - which is what Saad §3.3.4 actually says and what the Chapter 3 surface needs.
   Request: `Chapter04/Section02`'s `theorem_4_7`, `corollary_4_8_irred` and `theorem_4_9_irred`,
   and the phase-2 irreducible nodes of `Stationary/DiagDominant`, should take
   `Matrix.IsPatternIrreducible` rather than introducing a surface copy. All of those nodes are
   open, so nothing has to be rewritten.

2. **`Matrix.IsMMatrix`, the weak Perron theorem and Saad Thm 1.29 should move** out of
   `LinearSolve/Stationary/RegularSplitting`; see §1.3 above for the reason and for why the plan
   works without the move.

3. No restatement or rename of a *proved* declaration is requested. The one place where a proved
   statement is weaker than the book's is `SaadSparse.Chapter06.lemma_6_23`, which drops Saad's
   nonsingularity hypothesis and is therefore stronger, not weaker; that is already recorded in
   `plans/saadsparse-ch6.md` §6.

---

## 3. Not planned, and why

Numbered results and named claims in the slice that get no node, one line each.

**Chapter 1.**

* **Theorem 1.8, the Jordan canonical form.** Mathlib has no Jordan form and the book states it
  without proof; `backbone.md` §1.1 and §4.5 record that every use of it in the corpus has been
  replaced by Gelfand's formula or by generalized eigenspaces, and the two consumers (Saad §4.2.1's
  asymptotic convergence factor, Saad-eig Thm 3.7) are already left out.
* **The quasi-Schur (real Schur) form, §1.8.3.** Stated without proof; needs the `2 × 2`-block
  refinement of a Schur module that is itself still open, and nothing in the corpus uses it.
* **Proposition 1.18, the convexity of the field of values (Toeplitz-Hausdorff).** Stated without
  proof. The standard proof restricts to a two-dimensional subspace and shows the field of values
  of a `2 × 2` matrix is a filled ellipse - a self-contained but substantial development with no
  second consumer. The containment half and the normal case (Theorem 1.17) *are* planned.
* **The power inequality (1.36), `ν(A ^ k) ≤ ν(A) ^ k`.** Berger's inequality, attributed by the
  book to the literature; its proof is a unitary-dilation argument unrelated to anything else here.
* **Algebraic simplicity of the Perron eigenvalue (part of Theorem 1.25).** Only geometric
  simplicity is planned; the algebraic statement needs the derivative of the characteristic
  polynomial through the adjugate, and no result in the corpus uses it.
* **Problem P-1.27** (a rank-one perturbation of an M-matrix is an M-matrix): an exercise with no
  consumer.

**Chapter 2** (which has *no* numbered results at all).

* **§2.1, the partial differential equations.** Formalizing the Laplacian on a planar domain,
  Dirichlet/Neumann/Cauchy conditions and the general elliptic operator is not
  numerical-analysis work, and nothing later in the book uses it: Chapters 4-13 use the matrices.
* **§2.2.2's nine-point stencils** and "one of them is sixth order for harmonic functions". The
  stencils appear only in Figure 2.4, an image the text does not reproduce; Problem P-2.4 gives
  the recipe that would rebuild them, and nothing cites the claim.
* **§2.2.6's Buneman recurrences and the stability claim.** The recurrences are an algorithm; the
  claim that block cyclic reduction is unstable and Buneman's variant stable is made with no
  analysis anywhere in the book, so there is no statement to formalize. Operation counts likewise.
* **§2.3, the finite element method.** Its algebraic content is already in the library abstractly -
  `Numlib/Variational/{Forms,Galerkin}` with the Atkinson–Han Chapter 9 surface, where the
  stiffness matrix is the Gram matrix of a basis in the energy inner product and is positive
  definite for exactly Saad's reason. What is missing is the *concrete* space: a triangulation of a
  planar domain, piecewise-affine functions on it and integration over triangles, which is a
  substantial build in plane geometry and measure theory with no numerical-analysis content. And
  Green's formula (2.40), which carries §2.3's Neumann equation (2.47), needs the divergence
  theorem with a boundary measure and an outward normal field on a smooth-boundary domain, which
  Mathlib has only for boxes. Worth recording, against the expectation: the chapter states **no**
  Céa lemma, Lax–Milgram theorem, Poincaré inequality, trace theorem, interpolation estimate or
  convergence result, and uses no property of `H¹(Ω)` - the Sobolev framing is decorative and no
  Sobolev theory is needed for anything the chapter proves.
* **§2.4, mesh generation and refinement.** Its one claim with content, that connecting the
  midpoints preserves the angles, is the midsegment theorem of Euclidean geometry; the rest is
  descriptive text around figures and states no shape-regularity condition.
* **§2.5's derivation before the sign structure** - the conservation law, its weak form, the cell
  integration (2.49) and the cell averages (2.50)-(2.51). The book itself calls the averages crude
  and gives no error bound; (2.49) is derived by integrating by parts against the indicator of a
  cell, for which (2.39) does not hold, and should be read as the divergence theorem on the cell.
  The structural theorem that follows *is* planned, with the polygon lemma proved by rotating edge
  vectors instead of by the divergence theorem.

**Chapter 3.**

* **§3.4, storage schemes** (coordinate, CSR, CSC, MSR, diagonal, Ellpack-Itpack): the section
  states no theorem; the only formalizable content would be a round-trip specification the book
  never writes. Note for the record that this edition contains no jagged-diagonal or
  block-compressed format, contrary to what a reader of the first edition might expect.
* **§3.5, sparse matrix operations**: four code fragments and remarks on parallelism.
* **§3.6, sparse direct methods**: minimum degree and nested dissection are described
  algorithmically; the only quasi-theoretical claim never writes its bound down, and this edition
  states no fill-in or complexity result at all - no separator theorem, no operation count. The
  one theorem in the neighbourhood, that breadth-first level sets are separators, is §3.3.3's and
  is planned.
* **§3.7, test problems**: descriptive.
* **The Frobenius normal form of §3.3.4** (the diagonal blocks are the strongly connected
  components, in a topological order). The book states only the shape, without the ordering
  condition and without proof; the full statement needs a strongly-connected-component and
  topological-sort API for digraphs that Mathlib does not have. The two-block characterization,
  which is what "reducible" means and what Chapter 4 uses, *is* planned.
* **Example 3.3's fill-in claim** and **Problem P-3.12** (the structural inverse of an irreducible
  matrix is dense): both need a formal notion of structural fill-in or of the structural inverse,
  which the chapter never defines. P-3.12's mathematical kernel is planned, as
  `Matrix.IsIrreducible.entrywisePos_one_add_pow`.
* **Bandwidth, profile, envelope, skyline, and reverse Cuthill-McKee.** This edition defines none
  of the four and proves no bound about any of them; RCM is presented as George's observation with
  a picture.

**§4.3.**

* **The optimal and cyclic parameter sequences.** The book states no formula, no bound and no
  theorem, and cites Birkhoff-Varga-Young for a theory that exists only when `H` and `V` commute.
  There is nothing to formalize; note that the commutativity hypothesis, which the task brief
  expected to be a hypothesis of the convergence theorem, is not - the convergence proof needs no
  commutativity at all.
* **The `O(n² log n)` complexity of the model problem**: an operation count cited to Peaceman and
  Rachford.
* **"On the model problem, ADI with the optimal `r` has the asymptotic rate of SSOR with the
  optimal `ω`"**: an asymptotic remark with no constant and no proof.
* **The parabolic formulation (4.53)-(4.56)** and the time-stepping pair after it: a
  semi-discretization of a partial differential equation with no algebraic statement. As printed
  the pair is not the image of Algorithm 4.3 under `r = 2 / Δt`, the sign patterns differing.

**Chapter 6.**

* **Theorem 6.24, the Faber–Manteuffel theorem.** The direction
  `IsCGs A s → (minpoly degree ≤ s ∨ (normal ∧ ν(A) ≤ s - 1))` stays out. Saad states the theorem
  without proof; the known proofs (Faber–Manteuffel 1984, Liesen-Strakoš 2008) are research-level -
  the hard case is a matrix that is neither normal nor of small minimal degree, where one must
  build a starting vector whose Arnoldi run breaks the `s`-term recurrence, and the argument goes
  through a careful analysis of the eigenvalue multiplicities and the structure of the invariant
  subspaces. Nothing in `Numlib/Krylov/` would help, and the eigenvalue book does not need it. The
  *converse* direction is provable today and is requested in §1.6 above; with it, the surface
  covers everything of §6.10 except this one implication.
* **The final remark of §6.10** (`ν(A) ≤ 1` iff the minimal degree is at most `1`, or `A` is
  Hermitian, or `A = e^{iθ}(ρ + B)` with `B` skew-Hermitian): unnumbered, "easy to show", already
  recorded as left out in `plans/saadsparse-ch6.md` §5, and now reachable on `Eigen/Normal` if a
  second source ever cites it.
* **§6.6.2 (d) and (e)** are already open nodes of `Chapter06/Section06`
  (`equation_6_85_charpoly_isMinOn`, `equation_6_85_lanczos_charpoly`), waiting on
  `Arnoldi.charpoly_compression_isMinOn` (proved, in `Numlib/Eigen/RayleighRitz`) and
  `Lanczos.aeval_charpoly_tridiag` (open, in `Numlib/Krylov/OrthogonalPolynomials`). Nothing is
  added here; the second is the only thing standing between §6.6.2 and completion, and
  `Krylov/OrthogonalPolynomials` is `ready`.
* **§6.12, block Krylov methods**, is planned already as `Chapter06/Section12` and
  `Numlib/Krylov/Block`; untouched by this branch.

---

## 4. Coverage summary

### 4.1 Saad §1.1–1.10, every numbered item

| Item | Status | Where |
|---|---|---|
| Def 1.1 eigenvalue, spectrum | Mathlib | `spectrum`, `Matrix.hasEigenvalue_toEuclideanLin_iff` (proved) |
| Prop 1.2 nonsingular ⟺ invertible | planned | `Chapter01/Basics.proposition_1_2` |
| Prop 1.3 `conj μ ∈ σ(Aᴴ)`, left eigenvector | planned | `Chapter01/Basics.proposition_1_3` |
| Prop 1.4 unitary preserves the inner product | planned | `Chapter01/Basics.proposition_1_4` |
| Def 1.5 similarity | planned | `Chapter01/Section08.IsSimilar` |
| Thm 1.6 diagonalizable ⟺ `n` independent eigenvectors | planned | `Chapter01/Section08.theorem_1_6` |
| Prop 1.7 diagonalizable ⟺ all eigenvalues semisimple | planned | `Chapter01/Section08.proposition_1_7` |
| **Thm 1.8 Jordan form** | **skipped** | no Jordan form in Mathlib; stated without proof; avoided by design (§3) |
| Thm 1.9 Schur form | planned | `Chapter01/Section08.theorem_1_9`, on the open `Matrix.exists_unitary_conj_upperTriangular` |
| Thm 1.10 `Aᵏ → 0 ⟺ ρ < 1` | proved | `Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`; restated as `Chapter01/Section08.theorem_1_10` |
| Thm 1.11 Neumann series | proved | `summable_pow_iff_spectralRadius_lt_one`; restated as `theorem_1_11` |
| Thm 1.12 Gelfand | planned | `Chapter01/Section08.theorem_1_12`, on the open `Matrix.tendsto_pow_rpow_complexSpectralRadius` |
| Lemma 1.13 normal + triangular ⟹ diagonal | planned | `Chapter01/Section09.lemma_1_13` |
| Thm 1.14 normal ⟺ unitarily diagonalizable | planned | `Chapter01/Section09.theorem_1_14`, on the two `Eigen/Normal` nodes of §1.1 |
| Lemma 1.15 shared eigenvectors ⟺ normal | proved | `LinearMap.isStarNormal_of_adjoint_apply_eq_smul`, `…eigenspace_adjoint`; restated as `lemma_1_15` |
| Cor 1.16 normal + real spectrum ⟹ Hermitian | planned | `Chapter01/Section09.corollary_1_16` |
| Thm 1.17 field of values of a normal matrix | planned | `Chapter01/Section09.theorem_1_17` |
| Prop 1.18 field of values convex ⊇ hull | **half planned** | containment `Chapter01/Section09.proposition_1_18`; convexity skipped (Toeplitz-Hausdorff, §3) |
| Thm 1.19 Hermitian ⟹ real spectrum | Mathlib | `Matrix.IsHermitian.eigenvalues`; restated as `theorem_1_19` |
| Thm 1.20 Hermitian unitarily diagonalizable | Mathlib | `Matrix.IsHermitian.spectral_theorem`; restated as `theorem_1_20` |
| Thm 1.21 Courant–Fischer min-max | proved | `LinearMap.IsSymmetric.eigenvalues_eq_iInf_iSup`, `…iSup_iInf`; restated as `theorem_1_21` |
| Thm 1.22 Courant characterization | proved | `LinearMap.IsSymmetric.isGreatest_rayleighQuotient_orthogonal`; restated as `theorem_1_22` |
| Def 1.23 entrywise order | planned | `Matrix.EntrywiseLE` (`Matrix/Order`, open) |
| Prop 1.24 (5 clauses) | planned | clauses 2, 3 in `Matrix/Order`; clause 5 `Matrix.EntrywiseLE.linfty_opNorm_le`; clauses 1, 4 requested in §1.2; surface `Chapter01/Section10.proposition_1_24` |
| Thm 1.25 Perron–Frobenius | planned | `Matrix.IsIrreducible.exists_pos_hasEigenvector_complexSpectralRadius` + geometric simplicity; algebraic simplicity skipped |
| Prop 1.26 monotone multiplication | planned | `Matrix.EntrywiseLE.mul_of_entrywiseNonneg_left` (`Matrix/Order`, open) |
| Cor 1.27 `A ^ k ≤ B ^ k` | planned | `Matrix.EntrywiseLE.pow` |
| Thm 1.28 `ρ(A) ≤ ρ(B)` | planned | `Matrix.complexSpectralRadius_le_of_entrywiseLE` |
| Thm 1.29 `ρ(B) < 1 ⟺ (1 - B)⁻¹ ≥ 0` | planned | `Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff` (`RegularSplitting`, open) |
| Def 1.30 M-matrix | planned | `Matrix.IsMMatrix` (`RegularSplitting`, open) |
| Thm 1.31 M-matrix ⟺ `ρ(B) < 1` | planned | requested in §1.3; surface `Chapter01/Section10.theorem_1_31` |
| Thm 1.32 clause (1) is redundant | planned | requested in §1.3; surface `theorem_1_32` |
| Thm 1.33 M-matrix property is monotone | planned | requested in §1.3; surface `theorem_1_33` |

**33 numbered items: 6 already proved, 25 newly planned, 1 skipped outright (Thm 1.8), 1 planned in
half (Prop 1.18).** Unnumbered material planned alongside: Cauchy–Schwarz (1.2), the adjoint
identity (1.5), the matrix-norm formulas (1.13)-(1.16), Example 1.1, the range-kernel splitting
(1.18), the Gram–Schmidt breakdown criterion, the QR factorization (1.19), the Householder
reflectors (1.20)-(1.28), the field of values and the numerical radius, and Problem P-1.15.

### 4.2 Saad Ch. 2

The chapter has **no numbered results**. Of its inline assertions:

| Content | Status |
|---|---|
| (2.9)-(2.13), (2.16) Taylor truncation errors, and (2.17) the five-point error | planned, `Chapter02/Section02` (6 nodes) |
| the 1-D model matrix (§2.2.3) and its spectrum, positive definiteness, condition number | planned; the spectrum is *not* in the book and comes from `Matrix/TridiagonalToeplitz` |
| (2.20)-(2.23) the convection-diffusion problem: exact continuous and discrete solutions, the oscillation criterion, the M-matrix failure, the upwind sign structure | planned (5 nodes) |
| the 2-D five-point matrix (§2.2.5), (2.26)-(2.27) | planned, as a Kronecker sum, with its full spectrum - neither in the book |
| (2.28)-(2.29) the fast Poisson reduction, and the spectrum of `B` | planned (2 nodes) |
| (2.33), (2.36) the block cyclic reduction recurrence and its Chebyshev factorization | planned (1 node) |
| §2.5 (2.54)-(2.55) the finite volume sign structure, and `∑ s⃗_j = 0` | planned, `Chapter02/Section05` (4 nodes) |
| §2.1, §2.2.2 nine-point stencils, §2.2.6 Buneman and stability, §2.3 FEM, §2.4 meshes, §2.5 derivation | **skipped**, with the reasons in §3 |

So: the *model problem matrices and their spectra*, which is what the rest of the book cites, are
planned in full, together with every truncation error and the whole upwind analysis; the
partial-differential-equation modelling, the finite element space and the mesh geometry are
skipped. That is 22 surface nodes plus 10 backbone nodes in two new modules.

### 4.3 Saad Ch. 3

| Item | Status |
|---|---|
| Def 3.1 row/column permutation | planned, `Chapter03/Section03.proposition_3_2` (Mathlib restatement) |
| Prop 3.2 permutation as matrix multiplication | planned, same node (Mathlib restatement) |
| §3.2.1 adjacency graph; pattern of `A ^ k` = paths | planned, `Chapter03/Section02` (3 nodes) on `Sparse/Pattern` |
| §3.2.2 graphs of PDE matrices | **skipped** - the chapter states nothing (the claim is hedged and set as P-3.1) |
| §3.3.2 symmetric permutation = relabelling | planned, `Chapter03/Section03.adjGraph_submatrix` |
| §3.3.3 level sets are separators; CMK is block tridiagonal | planned, on `SimpleGraph/LevelSet` and `Sparse/Reordering` |
| §3.3.3 independent set size `≥ n/(1 + ν)` | planned, on `SimpleGraph/IndepSet` |
| §3.3.3 multicolouring: diagonal diagonal blocks; `≤ Δ + 1` colours; two colours on a bipartite graph | planned, on `SimpleGraph/Coloring` |
| §3.3.3 reverse Cuthill-McKee | **skipped** - an observation with a picture, no statement |
| §3.3.4 irreducible ⟺ no block triangular symmetric permutation | planned, `Sparse/Pattern` |
| §3.3.4 Frobenius normal form | **skipped** - stated without proof and incompletely; needs SCC/topological-sort API |
| §3.4–3.7 | **skipped** - no theorem content anywhere |
| P-3.2, P-3.4, P-3.5 | planned |
| P-3.9, P-3.10, P-3.11 | planned, on `SimpleGraph/Coloring` |
| P-3.12 structural inverse | **skipped**; its kernel planned as `Matrix.IsIrreducible.entrywisePos_one_add_pow` |

**Both numbered items planned; every inline claim of §3.2–3.3 planned except reverse
Cuthill-McKee and the Frobenius normal form; §3.4–3.7 skipped in full, honestly, because they
contain no theorem.** 11 surface nodes on 10 new backbone nodes across five modules, three of which
are Mathlib gaps worth upstreaming.

### 4.4 Saad §4.3 and the Chapter 6 gaps

| Item | Status |
|---|---|
| §4.3 Algorithm 4.3, (4.50)-(4.52), P-4.5 | planned, `Chapter04/Section03` (3 nodes) on `Stationary/ADI` |
| §4.3 "`H`, `V` SPD and `r > 0` ⟹ the stationary iteration converges" | planned and *proved in the plan* - the book asserts it without proof or citation |
| §4.3 the model problem splitting `A = H + V` | planned, as the Kronecker decomposition of `laplacian2D` |
| §4.3 optimal/cyclic parameters, complexity, SSOR comparison, parabolic form | **skipped**, §3 |
| §6.6.2 (a)-(c) | proved |
| §6.6.2 (d)-(e) | already open in `Chapter06/Section06`; blocked only on `Lanczos.aeval_charpoly_tridiag`, whose group is `ready` |
| §6.10 Prop 6.22, Lemma 6.23, `ν(A)`, `IsCGs`, the normality remarks | proved |
| §6.10 Thm 6.24, direction `⟸` | requested in §1.6 - provable today |
| §6.10 Thm 6.24, direction `⟹` | **skipped** - research-level, §3 |
| §6.10 final remark on `ν(A) ≤ 1` | skipped, already recorded in `saadsparse-ch6.md` §5 |

### 4.5 Headline

Of the slice, **everything that the book states as a numbered result is planned except three
items** - the Jordan canonical form, the convexity half of Proposition 1.18, and the hard direction
of Theorem 6.24 - each of which the book itself states without proof. Of the material the book
states *without* numbering, the model problem matrices with their full spectra, the whole upwind
analysis, the finite volume sign structure, the adjacency-graph and reordering theory, and the ADI
convergence theorem are planned; the partial-differential-equation modelling of §2.1, the finite
element space of §2.3, the mesh geometry of §2.4 and the storage-and-algorithm sections §3.4–3.7
are skipped, the first two because they need analysis or plane geometry that is not
numerical-analysis work, the last two because they state no theorem.
