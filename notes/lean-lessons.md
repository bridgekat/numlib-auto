# Lean and Mathlib lessons

A running record of what worked and what did not while formalizing this project, kept so that a
new agent does not repeat a dead end. Add an entry whenever you lose more than a few minutes to
something that a note would have prevented. Keep entries short and specific: the symptom, the
cause, the fix.

Pinned toolchain: Lean `v4.34.0-rc2`, Mathlib `v4.34.0-rc2` under `.lake/packages/mathlib`.

## Working in this repository

* Build one module with `lake build Numlib.Krylov.CG`, everything with `lake build Numlib`.
  `lake env lean Numlib/Krylov/CG.lean` type-checks a single file and prints all messages, which is
  the fastest edit loop; `lake build` is the check that counts because it also runs the linters.
* `lakefile.toml` sets `relaxedAutoImplicit = false` and Mathlib's standard linter set, with the
  header linter off. So an unbound identifier is an error, not an auto-implicit, and unused
  variables and unused hypotheses fail the build.
* Search Mathlib both ways: `grep`/`Grep` for exact names, and LeanSearch for concepts.
  `curl -s -X POST https://leansearch.net/search -H "Content-Type: application/json" -d '{"query":["orthogonal projection minimizes distance"],"num_results":8}'`
* Write patch scripts and Lean files with the Write tool, then run `python file.py`. Bash heredocs
  mangle unicode (`𝕜`, `‖`, `⟪⟫`) and fail above a few kilobytes.
* Line length: the only authority is the Mathlib linter that `lake build` runs. Counting bytes with
  `awk length>100` gives false positives on unicode-heavy lines.

## Syntax and elaboration gotchas

* `omit hA in` and `omit [inst] in` must come *before* the docstring of the declaration they apply
  to. After the docstring you get `unexpected token 'omit'`.
* Inside a declaration whose name starts with a namespace, a bare identifier resolves in that
  namespace first. In a theorem named `LinearPMap.foo`, `IsClosed` means `LinearPMap.IsClosed`;
  write `_root_.IsClosed` for the topological one.
* Dot notation on an `abbrev` type works only when the term's syntactic type is the abbreviation.
  For an ascribed term write the full name: `SesqForm.IsCoerciveWith (innerSL 𝕜 : SesqForm 𝕜 V) 1`.
* A `def` whose arguments come from a `variable` block can pick up unintended implicit arguments,
  which then mismatch at use sites. Bind the parameters explicitly, or bracket the section with
  `variable (A)` for the definitions and `variable {A}` for the theorems that follow.
* Recursive definitions over `ℕ` are easier to reason about than ones over `Fin (m + 1)`: the
  prefix of the sequence does not depend on the bound, so no re-indexing lemmas are needed. Build
  the `Fin`-indexed matrices at the end from the `ℕ`-indexed data.
* `fun i => if (i : ℕ) < m then _ else _` elaborates at type `ℕ → 𝕜` unless you annotate the
  binder: write `fun i : Fin (m + 1) => …`.
* A definition that mentions `Classical.choice` or a non-computable Mathlib operation needs
  `noncomputable def`. The error message says "consider marking as noncomputable"; believe it.
* An `InnerProductSpace.Core`-derived instance should carry `@[instance_reducible]`, otherwise the
  class is only semireducible and instance search fails downstream.

## Mathlib facts worth remembering

* `Module.Basis`, not `Basis`. `InnerProductSpace.ofCore` takes a `PreInnerProductSpace.Core`, so
  pass `(core).toCore`.
* `Matrix.PosDef` over `RCLike` needs `open scoped ComplexOrder` for the order on `𝕜`.
* The L2 operator norm lives in the scope `Matrix.Norms.L2Operator` in
  `Mathlib.Analysis.CStarAlgebra.Matrix`: `Matrix.l2_opNorm_def`, `toEuclideanCLM`.
* Hermitian matrix eigenvalues are in `Mathlib.Analysis.Matrix.Spectrum`, not
  `Mathlib.LinearAlgebra.Matrix.Spectrum`.
* `Matrix.isSymmetric_toEuclideanLin_iff` is the current name for symmetric ↔ Hermitian
  (`Mathlib/Analysis/Matrix/Hermitian.lean`); `Matrix.isHermitian_iff_isSymmetric` is deprecated.
* `NormMulClass` means the norm is *multiplicative* (`‖ab‖ = ‖a‖‖b‖`), which no matrix operator
  norm satisfies beyond `1 × 1`. For a submultiplicative matrix norm ask for
  `[NormedRing (Matrix n n ℝ)]` and open one of the scoped norm namespaces.
* `Submodule.HasOrthogonalProjection` is required for `starProjection`; it comes for free from
  `ofCompleteSpace`, from finite dimension, and there is an instance for the orthogonal complement.
  A span of a finite family needs its own `FiniteDimensional` instance before `starProjection`
  elaborates.
* `ContractingWith.fixedPoint` needs `[Nonempty α]`.
* `Convex ℝ s` needs a real normed space; over `RCLike 𝕜` state convexity results separately.
* `Module.Finite.span_of_finite` and `span_finset` live in `RingTheory/Finiteness/Basic.lean`;
  the `FiniteDimensional` versions in `FiniteDimensional/Defs.lean`.
* `WithLp.toLp p x` is the constructor for `EuclideanSpace`-valued terms.
* Useful names that are easy to guess wrong: `Submodule.finrank_sup_add_finrank_inf_eq`,
  `ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective`, `Matrix.charpoly_map`,
  `hasFDerivAt_ringInverse`, `spectrum.spectralRadius_le_nnnorm`.
* Mathlib has no Schur triangulation and no SVD factorization for matrices; do not plan proofs
  around them.

## Design conventions of this library

These are decided in `plans/backbone.md` §1.7; the short version for a proof author:

* Spectral hypotheses are quadratic-form bounds, `LinearMap.IsSymmetricBoundedBy A lmin lmax`, not
  lists of eigenvalues. Proofs that would use the spectral theorem in finite dimension go through
  the compression trick instead: compress to the relevant Krylov subspace, where the bounds are
  inherited (`compression.isSymmetricBoundedBy`), and no finite-dimensionality of the ambient space
  is needed.
* `Krylov.grade A v` is `Module.finrank K (fullSubspace A v)` under the hypothesis
  `[FiniteDimensional K (fullSubspace A v)]`. There is no `Fact` instance and no `ℕ∞`.
* Minimal-error statements name their target: `IsMinError xstar x₀ K x`.
