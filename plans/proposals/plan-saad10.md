# Proposal: Saad, *Iterative Methods for Sparse Linear Systems*, Chapters 10–14

Everything a planning agent for Saad Ch. 10–14 could not put into its own new TOML group files:
additions to groups owned by others, changes it believes are needed, the explicit skip list, and
the coverage summary.

Groups created by this plan (all new files, no existing file edited):

| Group | Nodes |
|---|---|
| `Numlib/LinearAlgebra/Matrix/SchurComplement` | 7 |
| `Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz` | 6 |
| `Numlib/LinearAlgebra/Matrix/KroneckerSum` | 5 |
| `Numlib/RingTheory/Polynomial/KernelPolynomial` | 5 |
| `Numlib/LinearSolve/Preconditioner` (directory) + `ILU`, `Polynomial`, `Chebyshev`, `ApproximateInverse` | 25 |
| `Numlib/LinearSolve/Multigrid` (directory) + `Basic`, `TwoGrid`, `FullMultigrid` | 15 |
| `Numlib/LinearSolve/DomainDecomposition` (directory) + `Schwarz`, `Schur` | 18 |
| `NumlibSurface/SaadSparse/Chapter10` + `Section02/03/04/05/08` | 21 |
| `NumlibSurface/SaadSparse/Chapter12` + `Section03` | 10 |
| `NumlibSurface/SaadSparse/Chapter13` + `Section02/03/04/05/06` | 26 |
| `NumlibSurface/SaadSparse/Chapter14` + `Section02/03/04/05/06` | 22 |

81 backbone nodes, 79 surface nodes.

---

## 1. Additions to existing groups

### 1.1 `Numlib/LinearSolve/Stationary/RegularSplitting` — Saad Theorems 1.31–1.33

**Why here rather than in a new module**: `Matrix.IsMMatrix` is defined in that group, and these are
the equivalent characterizations of that predicate. Saad's ILU existence theorem (Thm 10.2, planned
as `Matrix.IsMMatrix.exists_isILU`) cannot be proved without Theorem 1.33, and Theorem 10.1 is
stated in terms of the conditions of Theorem 1.32. The group's description currently says
"Saad Thm 1.31–1.33 (equivalent characterizations of M-matrices) are not needed by any surface and
are not planned"; that sentence is now false and should be replaced by a pointer to Ch. 10 when the
nodes are added.

```toml
[[node]]
id = "Matrix.IsMMatrix.of_complexSpectralRadius_lt_one"
kind = "theorem"
desc = '''Saad Thm 1.31: for a real matrix with positive diagonal and nonpositive off-diagonal entries,
`A.IsMMatrix ↔ complexSpectralRadius (1 - D⁻¹ A) < 1` where `D` is the diagonal of `A`. Immediate
from `Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff` applied to `B = 1 - D⁻¹ A`, plus
`IsUnit (D⁻¹ A) ↔ IsUnit A` and `EntrywiseNonneg (D⁻¹ A)⁻¹ ↔ EntrywiseNonneg A⁻¹`.'''
deps = ["Matrix.IsMMatrix", "Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff"]
source = "Saad, Iterative Methods for Sparse Linear Systems, Theorem 1.31"

[[node]]
id = "Matrix.isMMatrix_of_entrywiseNonneg_inv"
kind = "theorem"
desc = '''Saad Thm 1.32: the positivity of the diagonal is implied by the other three conditions. If the
off-diagonal entries of `A` are nonpositive, `A` is a unit and `A⁻¹` is entrywise nonnegative, then
`0 < A i i` for every `i`, so `A.IsMMatrix`. From `(A * A⁻¹) i i = 1`: every term `a_ik c_ki` with
`k ≠ i` is nonpositive, so `a_ii c_ii ≥ 1` with `c_ii ≥ 0`. This is the form in which Saad's
Theorem 10.1 checks that a Schur complement is an M-matrix.'''
deps = ["Matrix.IsMMatrix", "Matrix.EntrywiseNonneg"]
source = "Saad, Iterative Methods for Sparse Linear Systems, Theorem 1.32"

[[node]]
id = "Matrix.IsMMatrix.of_entrywiseLE"
kind = "theorem"
desc = '''Saad Thm 1.33, the comparison theorem: if `A ≤ B` entrywise, the off-diagonal entries of `B` are
nonpositive and `A` is an M-matrix, then so is `B`. Proof as in the book: the diagonals satisfy
`D_B ≥ D_A > 0`, and `1 - D_A⁻¹ A ≥ D_A⁻¹ (D_B - B) ≥ D_B⁻¹ (D_B - B) = 1 - D_B⁻¹ B ≥ 0`, so
`ρ(1 - D_B⁻¹ B) ≤ ρ(1 - D_A⁻¹ A) < 1` by `Matrix.EntrywiseLE.complexSpectralRadius_le` and
Theorem 1.31. This is what makes the *dropping* step of the ILU existence theorem work: dropping a
nonpositive off-diagonal entry moves the matrix up in the entrywise order.'''
deps = ["Matrix.IsMMatrix.of_complexSpectralRadius_lt_one", "Matrix.EntrywiseLE", "Matrix.EntrywiseLE.complexSpectralRadius_le"]
source = "Saad, Iterative Methods for Sparse Linear Systems, Theorem 1.33"

[[node]]
id = "Matrix.EntrywiseLE.complexSpectralRadius_le"
kind = "theorem"
desc = '''Saad Thm 1.28: for real matrices with `0 ≤ A ≤ B` entrywise,
`complexSpectralRadius A ≤ complexSpectralRadius B`. Gelfand's formula in the `l1` operator norm
(`Matrix.Norms.Operator` on the transpose, or the `l∞` norm on the transpose) together with
`Matrix.EntrywiseLE.pow` and the monotonicity of that norm under the entrywise order on nonnegative
matrices. Needs `Matrix.exists_limsup_norm_pow_mulVec_rpow_eq` /
`Matrix.complexSpectralRadius` of `Numlib/LinearAlgebra/Matrix/Complexify`.'''
deps = ["Matrix.EntrywiseLE", "Matrix.EntrywiseLE.pow", "Matrix.complexSpectralRadius"]
source = "Saad, Iterative Methods for Sparse Linear Systems, Theorem 1.28"
```

### 1.2 `Numlib/LinearAlgebra/Matrix/Order` — Saad Theorem 1.27

**Why here**: it is the entrywise-order calculus the group already collects, and it is the missing
step of Theorem 1.28 above. That group currently has `EntrywiseNonneg.pow` but not the comparison
version.

```toml
[[node]]
id = "EntrywiseLE.pow"
kind = "theorem"
desc = '''Saad Prop 1.27: for `0 ≤ A ≤ B` entrywise, `A ^ k ≤ B ^ k` for every `k`. Induction, using
`EntrywiseLE.mul_of_entrywiseNonneg_left` and `EntrywiseLE.mul_of_entrywiseNonneg_right`.'''
deps = ["EntrywiseLE", "EntrywiseNonneg", "EntrywiseLE.mul_of_entrywiseNonneg_left", "EntrywiseNonneg.pow"]
source = "Saad, Iterative Methods for Sparse Linear Systems, Proposition 1.27"
```

### 1.3 `Numlib/RingTheory/Polynomial/ChebyshevMinimax` — the recurrence for `shifted`

**Why here**: `Polynomial.Chebyshev.shifted` is defined in that module, and this is the three-term
recurrence it inherits from `Polynomial.Chebyshev.T`. `Numlib/LinearSolve/Preconditioner/Chebyshev`
needs it to prove that Algorithm 12.1's residuals are `shifted k α β 0` applied to `r₀`; a second
consumer is any Chebyshev-accelerated eigenvalue filter (Saad, *Numerical Methods for Large
Eigenvalue Problems*, §4.4).

```toml
[[node]]
id = "shifted_succ"
kind = "theorem"
desc = '''The three-term recurrence of the shifted Chebyshev polynomials, Saad (12.8): with
`σ_k = T_k((b + a - 2γ)/(b - a))` and `ρ_k = σ_k/σ_{k+1}`,
`shifted (k+1) a b γ = ρ_k • (2 • (C ((b + a)/(b - a)) - (2/(b - a)) • X) * shifted k a b γ -
ρ_{k-1} • shifted (k-1) a b γ)`, together with `shifted_zero = 1`, `shifted_one`, and
`sigma_succ : σ_{k+1} = 2 σ₁ σ_k - σ_{k-1}`. From `Polynomial.Chebyshev.T_add_two` after the affine
change of variable; the normalizing denominators are what turn the monic recurrence into this
one.'''
deps = ["shifted", "one_le_eval_T"]
source = "Saad, Iterative Methods for Sparse Linear Systems, (12.6)–(12.8)"
```

### 1.4 `Numlib/Analysis/InnerProductSpace/Energy` — the `A`-orthogonal projector, once

**Why here**: three modules now want "the `A`-orthogonal projector of `E` onto a finite-dimensional
subspace `K`, as an endomorphism of `E`": `Numlib/LinearSolve/Multigrid/Basic`
(`Multigrid.coarseProjection`), `Numlib/LinearSolve/DomainDecomposition/Schwarz`
(`Schwarz.energyProjection`), and `Numlib/LinearSolve/Projection/Optimality`, which already builds
it inline inside `IsGalerkin.error_eq_starProjection`. Defining it three times is the duplication
the plan is supposed to prevent, and `Energy` is where `WithEnergy` and `WithEnergy.submoduleMap`
live.

```toml
[[node]]
id = "WithEnergy.projection"
kind = "definition"
desc = '''`WithEnergy.projection A hA K : E →ₗ[𝕜] E`, the `A`-orthogonal projector onto a
finite-dimensional `K ≤ E`: the transport of `(WithEnergy.submoduleMap A hA K).starProjection`
along `WithEnergy.equiv`. Comes with `projection_mem`, `projection_eq_self_of_mem`,
`isIdempotentElem_projection`, `energyInner_sub_projection_eq_zero` (the defining orthogonality),
`energyNorm_projection_le` and `range_projection = K`.'''
deps = ["WithEnergy", "WithEnergy.equiv", "WithEnergy.submoduleMap"]

[[node]]
id = "WithEnergy.projection_isGalerkin"
kind = "theorem"
desc = '''The characterization every consumer uses: for `A x* = b`,
`IsGalerkin A b x₀ K (x₀ + projection A hA K (x* - x₀))`, and conversely the Galerkin iterate on
`x₀ + K` is that vector. Saad's coarse-grid correction (Lemma 13.1) and his Schwarz projector
(14.24) are both this statement.'''
deps = ["WithEnergy.projection", "IsGalerkin", "IsGalerkin.error_eq_starProjection"]
```

If this is applied, `Multigrid.coarseProjection` and `Schwarz.energyProjection` should be *defined*
as `WithEnergy.projection` specializations rather than re-transported; their group descriptions say
so already in prose, and only the `deps` lists would change.

### 1.5 Nothing to add elsewhere

* `Numlib/LinearSolve/Projection/OneDimensional` already has the node Saad Prop 10.13's first half
  needs, `Projection.norm_residual_minResStep_sq_eq` (open). No addition; it should simply be
  raised in priority, since it is now wanted by two chapters.
* `Numlib/LinearSolve/Projection/Additive` and `Numlib/LinearSolve/Stationary/Block` cover Saad
  §12.2 (block Jacobi) and §12.4.2 (red–black systems) as far as those sections make claims. The
  Schwarz module *depends* on `Projection.additiveStep` / `Projection.multiplicativeStep` and
  proves the conjugation between them and the energy projectors
  (`Schwarz.error_multiplicativeStep_eq_errorOp`); nothing is duplicated.
* `Numlib/Krylov/NormalEquations` covers Saad §10.8.1 (CGNE/SSOR, CGNR/SSOR); the only claim in
  that section is that `Aᵀ A` and `A Aᵀ` are positive definite, which is
  `Krylov.adjoint_comp_isSymmetricCoercive`.

## 2. Changes to existing declarations

None are required. Two notes:

1. **`Numlib/LinearSolve/Stationary/RegularSplitting`'s group description** claims Saad Thm 1.31–1.33
   are unneeded. With Ch. 10 planned that is no longer true (see §1.1); the sentence should be
   replaced when the nodes are added.
2. **`Numlib/LinearSolve/Preconditioner/Chebyshev` vs. `Numlib/LinearSolve/Stationary/`.** Chebyshev
   acceleration is a semi-iterative method, not literally a preconditioner, and a reader coming from
   Kress §4.4 or from Varga would look for it under `Stationary/`. It is filed under
   `Preconditioner/` because that is where Saad puts it (§12.3.2) and because its analysis is the
   polynomial one, not the splitting one. If a second book makes `Stationary/Chebyshev` the better
   home, the move is a rename of one module and no statement changes.

## 3. Not planned, and why

**Chapter 10.**

* **Proposition 10.3** (the `KIJ` and `IKJ` loop orders produce identical factors). The plan's
  `Matrix.IsILU` is declarative and deliberately abstracts from the loop order, so neither algorithm
  exists as an object; the proposition would have to be preceded by two `for`-loop formalizations
  whose only theorem is that they agree. No downstream consumer.
* **Theorems 10.6 and 10.7** (fill-in at `(i,j)` iff there is a fill-path; level-of-fill `p` iff a
  fill-path of length `p+1`). Needs a symbolic model of Gaussian elimination on the adjacency graph
  — elimination orderings, reachable sets `Reach(u, V_k)` — that nothing else in the library uses,
  and Saad quotes Theorem 10.6 from the literature without proof.
* **§10.3.4** (matrices with regular structure): stencil arithmetic for the 5-point and 9-point
  matrices, giving scalar recurrences for the ILU(0) and ILU(1) factors. Concrete computation for
  one family of matrices; no theorem is stated.
* **§10.4.3–10.4.6** (ILUT implementation, ILUTP, ILUS, Crout ILU): data structures (heaps,
  quick-split, linked lists) and pivoting heuristics.
* **§10.5.6–10.5.8** (approximate inverses via bordering, AINV, improving a preconditioner):
  algorithms. Lemma 10.15, the one claim in them, *is* planned.
* **§10.6** (reordering for ILU): the section's content is Example 10.6, a table of experiments.
* **Theorem 10.16** (each block `Δ_i` of the block-ILU recurrence for a block-tridiagonal SPD
  matrix with diagonally dominant diagonal blocks is a symmetric M-matrix). Saad writes "the
  following theorem can be shown" and gives no proof; it also rests on the tridiagonal-part-of-the-
  inverse recurrence of §10.7.1, which is a separate construction with no other consumer.
* **Theorem 10.18** (incomplete modified Gram–Schmidt gives the same `L` as incomplete Cholesky on
  `A Aᵀ`, for a pattern closed under `(i,j) ∈ P_L, (i,k) ∉ P_L → (j,k) ∈ P_L`). Saad: "the
  following result is stated without proof".

**Chapter 11** (parallel implementations). *Checked, not assumed*: the chapter contains no theorem,
proposition, lemma, corollary or numbered definition — only Algorithms 11.1–11.8 and two examples.
Its subject is storage formats (CSR, CSC, DIA, Ellpack–Itpack, jagged diagonal), machine models
(pipelining, vector processors, shared and distributed memory) and level scheduling for triangular
solves. Level scheduling has a genuine combinatorial invariant (the depth of a node in the
dependency DAG), but the book states no property of it. Nothing is planned, and no surface group
is created.

**Chapter 12.** The chapter contains no numbered result at all; §12.3 is planned through its
displayed equations.

* **§12.2** (block-Jacobi preconditioners): the block splittings of
  `Numlib/LinearSolve/Stationary/Block`, already planned, with no new claim.
* **§12.3.3, (12.15)–(12.16) and the Gamma-function norm**: the explicit Jacobi-weight formula for
  `R_k` and the evaluation `‖p_k/p_k(0)‖²_{w'} = Γ²(μ+1) Γ(k+ν+1) Γ(k+1) / ((2k+μ+ν+1) Γ(k+μ+ν+1)
  Γ(k+μ+1))` need Jacobi polynomials, which Mathlib does not have (it has only
  `Polynomial.Chebyshev`). The qualitative conclusion — geometric decay for `α > 0`, `O(1/k)` for
  `α = 0` — is planned in the first case and skipped in the second.
* **§12.3.4** (the nonsymmetric case): Chebyshev polynomials on an ellipse are Saad Lemma 6.26 /
  Thm 6.27, already deferred to `Numlib/RingTheory/Polynomial/ChebyshevEllipse` (phase 3); the
  polygonal case is the Remez algorithm, a numerical procedure with no stated theorem.
* **§12.4** (multicoloring, red–black ordering): a permutation, after which the matrix is
  `fromBlocks D₁ E Eᵀ D₂` and the reduced system is its Schur complement — already planned in
  `Numlib/LinearAlgebra/Matrix/SchurComplement` — and the colouring condition is Property A of
  `Numlib/LinearSolve/Stationary/ConsistentlyOrdered`. No new claim.
* **§12.5** (multi-elimination ILU, ILUM), **§12.6** (distributed ILU and SSOR), **§12.7**
  (element-by-element techniques, parallel row projection): algorithms and data distributions.

**Chapter 13.**

* **Example 13.6 and the assumption (13.48)** (`‖u - u^h‖ ≤ c h^κ`, the discretization error of the
  model problem, verified from a bound on the fourth derivative of the exact solution). This is the
  one genuinely PDE-flavoured claim in the chapter. It needs the exact solution of the boundary
  value problem, a Taylor expansion of the truncation error, and a bound on `‖A_h⁻¹‖` in the
  discrete `L²` norm; the last is available (`Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz`) but the
  first two are analysis of a differential equation. Saad himself takes (13.48) as an assumption in
  Theorem 13.2, and the plan does the same.
* **Examples 13.1, 13.4, 13.5, 13.9** (stencil notation for the 2-D interpolation; numerical
  convergence tables for V-cycle and FMG; an AMG interpolation computation on a 9-point stencil):
  illustrations.
* **§13.6.1–13.6.4** (algebraic multigrid) beyond the quadratic-form identity (13.68)–(13.69). The
  smoothness criterion (13.70) is reached by an argument Saad explicitly marks as non-rigorous
  ("it cannot be rigorously argued that the bracketed term must be of the order 2ε, but one can say
  that on average this will be true"); the interpolation weights (13.74) come from three successive
  approximations, none of them an inequality; the coarsening heuristics of §13.6.3 are stated as
  guiding principles; and §13.6.4 (AMG via multilevel ILU) is a construction. Once an AMG
  prolongation is fixed, its *analysis* is Theorem 13.3 with `Vc = Ran(I_H^h)`, which is planned.
* **§13.7** (multigrid versus Krylov methods): discussion.

**Chapter 14.**

* **Theorem 14.2** (Chan–Goovaerts: with the consistent initial guess (14.22), the `y`-iterates of
  the multiplicative Schwarz sweep are those of a Gauss–Seidel sweep on the Schur complement
  system). Stated for the *vertex-based* partitioning of §14.2.3, whose block structure
  (14.8)–(14.14) — `s` subdomains, each with its own interior/interface splitting, local Schur
  complements `S_i`, and inter-subdomain interface couplings `E_ij` — is several definitions of
  pure bookkeeping with no other consumer in the library. The theorem is a translation between two
  descriptions of one iteration, not an estimate, and the projector-level content of §14.3 that the
  rest of the chapter actually uses is fully planned. This is the largest single omission in the
  slice and the one most worth revisiting if a second domain-decomposition source is added.
* **§14.2.3–14.2.5** (Schur complements for vertex-based and finite-element partitionings, and for
  the model problem): the same bookkeeping, plus §14.2.4's element-matrix assembly, which is finite
  element material.
* **§14.4.2** (probing: reconstruct a tridiagonal approximation to `S` from a few products `S v`)
  and **§14.4.3**: heuristics with no claim.
* **Definitions 14.13–14.15 and Theorem 14.16** (maps of a vertex set, `k`-ply neighborhood systems,
  `(α, k)`-overlap graphs, and the geometric separator theorem of Miller–Teng–Thurston–Vavasis).
  Saad quotes Theorem 14.16 from the literature without proof; it is a substantial result in
  computational geometry (a sphere-separator argument with a random conformal map) with no other
  consumer here.
* **§14.6.2, §14.6.4 and Algorithms 14.7–14.10** (coordinate and inertial bisection, pseudo-
  peripheral nodes, recursive graph bisection, multinode level-set expansion): partitioning
  heuristics; none of them comes with a claim. §14.6.3's spectral bisection *is* planned, because
  the identity `(L p, p) = 4 n_c` and the Fiedler characterization are theorems and Mathlib has the
  graph Laplacian.

---

## 4. Coverage summary

Numbered results in Saad Ch. 10–14. Chapters 11 and 12 contain no numbered result of any kind;
Ch. 11 contains no theorem-shaped content at all.

| Result | Status |
|---|---|
| Thm 10.1 (Ky Fan) | planned — `Matrix.IsMMatrix.isMMatrix_schurComplementSingle`, surface `SaadSparse.Chapter10.theorem_10_1` |
| Thm 10.2 (ILU exists for M-matrices, regular splitting) | planned — `Matrix.IsMMatrix.exists_isILU`, `Matrix.IsILU.isRegular`, surface `theorem_10_2` (★★★, the hard proof of the slice) |
| Prop 10.3 (KIJ = IKJ) | **skipped** — no algorithm objects exist; `Matrix.IsILU` abstracts from the loop order |
| Prop 10.4 (`A = LU - R`, `R` in the pattern) | planned — `Matrix.IsILU.sub_eq_zero_of_notMem`, surface `proposition_10_4` |
| Def 10.5 (level of fill) | planned as a definition — surface `definition_10_5`; the graph characterization is skipped |
| Thm 10.6 (fill-in iff fill-path) | **skipped** — needs a symbolic elimination model; unproved in the book |
| Thm 10.7 (level `p` iff fill-path of length `p+1`) | **skipped** — same |
| Thm 10.8 (ILUT existence for diagonally dominant `M̂`) | planned — `Matrix.IsMHat.ilut_rows`, surface `theorem_10_8` |
| Prop 10.9 (gradient of `‖I − AM‖_F²`) | planned — `Preconditioner.hasFDerivAt_normSq_sub_apply`, surface `proposition_10_9` |
| Prop 10.10 (`‖I − AM‖ < 1 ⇒ M` nonsingular) | planned — `Preconditioner.isUnit_of_norm_one_sub_mul_lt_one` |
| Prop 10.11 (sparsity of `M` follows that of `A⁻¹`) | planned — `Preconditioner.abs_sub_inv_apply_le` |
| Cor 10.12 (`τ`-equimodular `A⁻¹` forces dense `M`) | planned — surface `corollary_10_12` |
| Prop 10.13 (self-preconditioned MR: one-step factor, quadratic outer rate) | planned — `Projection.norm_residual_minResStep_sq_eq` (existing open node) + `Preconditioner.norm_le_norm_sq_of_isMinOn` |
| Prop 10.14 (global self-preconditioned MR is quadratic) | planned — `Preconditioner.norm_le_norm_sq_of_isMinOn`, `Preconditioner.residual_selfPreconditionedStep` |
| Lemma 10.15 (`δ_{k+1} > 0` for SPD in the bordering algorithm) | planned — surface `lemma_10_15` |
| Thm 10.16 (block-ILU blocks are M-matrices) | **skipped** — stated without proof in the book |
| Prop 10.17 (incomplete LQ completes for nonsingular `A`) | planned — surface `proposition_10_17` |
| Thm 10.18 (incomplete MGS `L` = incomplete Cholesky `L`) | **skipped** — stated without proof in the book |
| **Ch. 11** — no numbered results, no theorem content | **skipped in full**, checked section by section |
| **Ch. 12** — no numbered results | §12.3 planned through its equations: (12.3), (12.4)–(12.5), (12.6)–(12.9) with Alg 12.1, (12.10)–(12.14). §12.2, §12.4–12.7 **skipped**; (12.15)–(12.16) skipped (no Jacobi polynomials in Mathlib) |
| Lemma 13.1 (coarse-grid correction is an `A`-orthogonal projector) | planned — `Multigrid.coarseProjection_apply_eq`, `Multigrid.range_coarseCorrection`, surface `lemma_13_1` |
| Thm 13.2 (FMG error is of discretization order) | planned — `Multigrid.le_of_rec_of_half`, `Multigrid.norm_sub_fullMultigrid_le`, surface `theorem_13_2` |
| Thm 13.3 (two-grid convergence `√(1 − α/β)`) | planned — `Multigrid.energyNorm_twoGrid_le`, surface `theorem_13_3` |
| §13.2 spectra of the model problems (13.7), (13.14), (13.21)–(13.25), (13.29) | planned — `Matrix/Tridiagonal`, `Matrix/KroneckerSum`, surface `Chapter13/Section02` |
| §13.3 inter-grid operators (13.31), (13.35)–(13.38) | planned — surface `Chapter13/Section03` |
| §13.4 cycles and cost recurrence (13.44)–(13.47) | planned — surface `vcycle`, `equation_13_44` |
| §13.5.1 the two subspaces (13.57)–(13.61), Example 13.7 | planned — surface `equation_13_59`, `example_13_7` |
| Example 13.8 (weighted Jacobi has the smoothing property) | planned — `Multigrid.isSmootherWith_richardson` |
| Example 13.6 / assumption (13.48) | **skipped** — discretization error of a differential equation |
| §13.6 algebraic multigrid | (13.68)–(13.69) planned (`equation_13_68`); the rest **skipped** as explicitly heuristic |
| Prop 14.1 (Schur complement: nonsingular, SPD, `S⁻¹` is a block of `A⁻¹`) | planned — `Matrix/SchurComplement`, surface `proposition_14_1` |
| Thm 14.2 (Schwarz `y`-iterates = block Gauss–Seidel on `S`) | **skipped** — vertex-based partitioning bookkeeping, translation rather than estimate |
| Prop 14.3 (multiplicative Schwarz is a fixed-point iteration for `M⁻¹A = I − Q_s`) | planned — `Schwarz.one_sub_errorOp_eq_sum`, surface `proposition_14_3` |
| Lemma 14.4 (`Z_i`, `M_i` recurrences, (14.35)) | planned — `Schwarz.one_sub_errorOp_eq_sum`, surface `lemma_14_4` |
| Thm 14.5 (`λmax(A_J) ≤ s`) | planned — `Schwarz.re_inner_additiveOperator_le` |
| Thm 14.6 (`λmax(A_J) ≤ c` colours) | planned — same node's refinement |
| Thm 14.7 (`λmin(A_J) ≥ 1/K₀`) | planned — `Schwarz.le_re_inner_additiveOperator` (★★) |
| Lemma 14.8 | planned — `Schwarz.sum_norm_starProjection_sq_le` (★★) |
| Thm 14.9 (`‖Q_s‖_A ≤ √(1 − 1/(K₀(1+K₁)²))`) | planned — `Schwarz.norm_errorOp_le` |
| Prop 14.10 (induced ILU preconditioner for `S`) | planned — `DomainDecomposition.inducedPreconditioner_eq` |
| Prop 14.11 (block-preconditioned full system = reduced system) | planned — `DomainDecomposition.isMinRes_iff_isMinRes_schurComplement` |
| Prop 14.12 (same, with `S` preconditioned) | planned — surface `proposition_14_12` |
| Defs 14.13–14.15, Thm 14.16 (geometric separator theorem) | **skipped** — quoted without proof; computational geometry |
| §14.6.3 spectral bisection `(L p, p) = 4 n_c`, Fiedler vector | planned — surface `Chapter14/Section06` |

**Headline.** Chapters 10, 13 and 14 contain 37 numbered results (18 + 3 + 16); chapters 11 and 12
contain none. **27 of the 37 are planned and 10 are skipped**, and of the 10, four are results the
book itself states without proof (Thm 10.6, Thm 10.16, Thm 10.18, Thm 14.16). All three numbered
results of Chapter 13 are planned, and 11 of the 16 of Chapter 14. On top of the numbered results,
the plan covers the unnumbered but theorem-shaped material of §10.2 (the SGS factorization and its
error matrix), §10.3.2 and §10.3.5 (ILU(0), MILU and the row-sum property), all of §12.3, all of
§13.2–13.5 and §14.5.

Chapter 11 is skipped in full and Chapter 12 has one planned section out of six — that is the honest
shape of this slice: the two chapters about *how to run these methods on a parallel machine* have
essentially no mathematics in them, while the two chapters about multigrid and domain decomposition
turn out to be almost entirely formalizable, because their analysis is Hilbert-space projection
theory once the meshes are stripped away and their model problems are tridiagonal matrices with
explicit sine eigenvectors.
