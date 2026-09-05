# Lean and Mathlib lessons

A running record of what worked and what did not while formalizing this project, kept so that a
new agent does not repeat a dead end. Add an entry whenever you lose more than a few minutes to
something a note would have prevented. Keep entries short and specific: symptom, cause, fix.

Pinned toolchain: Lean `v4.34.0-rc2`, Mathlib `v4.34.0-rc2` under `.lake/packages/mathlib`.

## Working in this repository

* Build one module with `lake build Numlib.Krylov.CG`, everything with `lake build Numlib`.
* **`lake env lean F.lean` type-checks against the built oleans of its imports.** After editing a
  dependency you must `lake build` that dependency, or every lemma you just added to it reads as
  `unknown identifier`. This was the single biggest time sink across the proof agents.
* `lakefile.toml` sets `relaxedAutoImplicit = false` and Mathlib's standard linter set, with the
  header linter off. An unbound identifier is an error, not an auto-implicit.
* Unused hypotheses and section variables are *warnings*, not errors, and the build still exits 0.
  They are a useful signal that a statement carries a hypothesis its proof does not need. To keep
  the statement and silence the linter use `set_option linter.unusedSectionVars false in`; `omit … in`
  also removes the argument at call sites, which changes the interface.
* Search Mathlib both ways: `grep` for exact names, LeanSearch for concepts.
  `curl -s -X POST https://leansearch.net/search -H "Content-Type: application/json" -d '{"query":["orthogonal projection minimizes distance"],"num_results":8}'`
* **Never pipe Lean source through a bash heredoc.** Unicode gets mangled into surrogates, and a
  script that opens the target for writing before it fails will truncate it: one agent lost 600
  lines this way. Write the patch script with the Write tool, run `python file.py`, and have it
  write to a temp file and rename so a crash cannot destroy the original.
* In a Python patch script, `𝕜` must be written `\U0001d55c`. A surrogate pair `𝕜`
  silently fails to match and, on Windows, raises on write.
* The Lean sources here use LF, and every writer must keep it that way. A Python patch script has
  to open with `io.open(p, 'w', encoding='utf-8', newline='')`, or it silently converts the file to
  CRLF and the whole file shows as changed.
* Line length: the only authority is `linter.style.longLine`. Counting with `awk length>100`
  over-reports, because it counts bytes and the mathematical symbols are multi-byte.

## Correctness traps

* **`include h` makes every later declaration in scope carry `h`.** A theorem that re-binds a
  weaker hypothesis of its own silently gets both, turning a general statement into a special case.
  One theorem meant for indefinite operators was thereby a trivial corollary of its own coercive
  version. Check the elaborated signature with `#check @foo`.
* **A bound constant is not free.** Hypotheses of the form `∀ w v, ‖a w v‖ ≤ M‖w‖‖v‖`, or anything
  quantified over `v ∈ K`, are vacuous on trivial spaces and for `K = ⊥`, so they do not imply
  `0 ≤ M`. Either assume it or work with `max M 0`.
* **Division by zero is zero and square roots of negatives are zero.** Identities stated with `/`
  or with an energy norm can be false exactly at the degenerate point, and are then invisible in
  testing. Check the breakdown case explicitly.
* Statements about an algorithm at the boundary `m = grade` usually need the strict form
  `m < grade`; the padded recurrences degenerate there.

## Syntax and elaboration

* `omit [inst] in` and `set_option … in` must come *before* the docstring and before any attribute,
  and `omit` is not sticky: one copy per declaration.
* Inside a declaration named `Foo.bar`, a bare identifier resolves in `Foo` first. Write
  `_root_.IsClosed` for the topological one.
* Dot notation resolves on the head of the *unfolded* type. For an `abbrev` such as
  `SesqForm 𝕜 V := V →L⋆[𝕜] V →L[𝕜] 𝕜`, `x.IsCoerciveWith` can resolve to
  `LinearMap.IsCoerciveWith`; write the full name.
* Section-variable argument order is *declaration* order, not `include` order.
* The style linter rejects a `show` that changes the goal, even up to definitional equality; use
  `change`. It also rejects a leading bare `show` and `haveI` on a `Prop`.
* A goal containing a beta redex, typical after `rintro _ ⟨i, rfl⟩` or after rewriting with a lemma
  whose statement is a literal lambda, defeats `rw`. Clear it with `dsimp only` or `change`.
* `rw [← h]` where the right-hand side of `h` is a bare local, as in `h : P x + (1 - P) x = x`,
  rewrites the `x` inside `P x` as well and silently generalises the goal. Aim it with
  `conv_rhs => rw [← h]`.
* `rw [h]` rewrites *all* occurrences, including inside `‖a‖` and inside `diagPart A`. Use
  `nth_rewrite`, restate the equation in a form that does not loop, or go entrywise.
* Avoid `set` when you will `rw` with library lemmas afterwards: the abbreviation is definitionally
  but not syntactically equal to what the rewrite produces.
* To `rw` with a `def`, add a private `foo_def : foo x = … := rfl` companion.
* Lemmas whose statement does not mention the scalar field need it supplied, as in
  `norm_sub_sq (𝕜 := 𝕜)`; otherwise the instance problem is stuck on `InnerProductSpace ?m E`.
* `linter.unusedDecidableInType` fires on a `[DecidableEq ι]` binder absent from the statement;
  drop it and open the proof with `classical`.
* `ExistsUnique` goals arrive beta-unreduced; prefix the uniqueness branch with `show ∀ v, …`.

## Tactics

* `module` is the right tactic for vector identities with symbolic scalars; `abel` cannot move
  scalars, and `ring` does not see through scalar actions. `noncomm_ring` handles ring identities
  with `Ring.inverse` as an atom.
* Prefer division-free forms for `linear_combination`. Replacing `ρ - 1 = αβ/α'` by
  `α'(ρ - 1) = αβ` turned a failing `field_simp; linear_combination` into an immediate success.
* `field_simp` often closes the goal by itself, after which a trailing `ring` errors with "No goals
  to be solved". It also runs `ring_nf`, which can reorder `j + 1` into `1 + j` and break a later
  match; prove such scalar identities as standalone lemmas over abstract reals.
* `match_scalars` can leave several different goals, each needing its own `linear_combination`.
* `positivity` does not see through `energyNorm`; keep a `energyNorm_nonneg` lemma at hand.
* `exact_mod_cast` needs the coercion syntactically present. A term that is `rfl`-equal to a cast
  is not enough; introduce the cast with an explicit `have` first.
* `simp only [f]` makes no progress on a partially applied `f`. Prove `f = fun v => …` by `funext`
  and rewrite with it.
* `simp only [map_sub, …]` can dissolve an opaque term you are mid-argument about; abstract the
  algebra into a `have` so the tactic cannot see inside.
* `rw` rewrites only the first instantiation of a lemma like `ite_eq_left`; with several `ite`s
  sharing a condition use `simp only`.
* Well-founded induction along a finite linear order: `induction i using WellFoundedLT.induction`.

## Mathlib names and API

`pow_left_inj₀ ha hb hn : a ^ n = b ^ n ↔ a = b` is the way to cancel the squares after comparing
two norms through `norm_add_sq`.

Deprecated or renamed in this toolchain: `if_pos`/`if_neg` to `ite_eq_left`/`ite_eq_right`;
`push_neg` to `push Not`; `Matrix.dotProduct` to root-level `dotProduct`; `LinearMap.mul_apply` to
`Module.End.mul_apply`; `orthogonalProjection` to `Submodule.orthogonalProjectionOnto` and
`Submodule.starProjection`; `ContinuousLinearMap.{sub,add,smul,sum}_apply` to the root-namespace
names and `ContinuousLinearMap.one_apply` to `one_apply_eq_self`; `Matrix.det_of_lowerTriangular` to
`det_of_isLowerTriangular`; `div_le_div_iff` to `div_le_div_iff₀`; `LinearMap.range_coe` to
`LinearMap.coe_range`; `linearIndependent_fin_succ'` to `linearIndependent_finSucc'`;
`Polynomial.degree_sub_lt` to `degree_sub_lt_left`; `RCLike.conj_conj` is only an alias, prefer
`starRingEnd_self_apply`. `sub_eq_sub_iff_add_eq_add` and `div_add_div_same` do not exist.

Structural facts worth knowing before planning a proof:

* **Gelfand's formula** is in `Mathlib.Analysis.Normed.Algebra.GelfandFormula`, not `…Algebra.Spectrum`.
  With `spectrum.spectralRadius_pow_le`, `spectralRadius_le_nnnorm` and `ENNReal.rpow_inv_natCast_pow`
  the whole `ρ(a) < 1 ↔ aⁿ → 0` story is short. Stay in `ℝ≥0∞`.
* `Summable.tsum_pow_mul_one_sub` gives `(∑' xⁿ)(1-x) = 1` from summability alone: that is the route
  from `ρ(a) < 1` to `IsUnit (1 - a)`. `tsum_geometric_le_of_norm_lt_one` is stated without
  `NormOneClass`, so state Neumann helpers with an explicit `‖(1:R)‖ ≤ 1` and they also apply to
  `E →L[𝕜] E`, which is `NormOneClass` only for nontrivial `E`. `NormOneClass` does not give
  `Nontrivial` by instance search; it is the theorem `NormOneClass.nontrivial`.
* `NormedRing` plus `NormOneClass` do **not** imply `ρ(a) ≤ ‖a‖`: they permit `‖x‖ = |x|^(1/2)`
  transported from `ℝ`. Ask for `NormedAlgebra`.
* `Matrix.BlockTriangular M b` unfolds to `b j < b i → M i j = 0`, so `BlockTriangular · id` is
  *upper* triangularity and `· OrderDual.toDual` is lower. Getting this backwards makes both
  statements false.
* `Matrix.toEuclideanLin` is an `abbrev` for `Matrix.toLpLin 2 2`, so `toLpLin_one`,
  `toLpLin_mul_same`, `toLpLin_pow`, `spectrum_toLpLin` and
  `toEuclideanLin_conjTranspose_eq_adjoint` already exist. Almost every glue lemma is one Mathlib
  name away.
* `Matrix.isSymmetric_toEuclideanLin_iff` is the current symmetric-versus-Hermitian bridge;
  `isHermitian_iff_isSymmetric` is deprecated. `Matrix.IsHermitian.spectrum_eq_image_range`
  converts Mathlib `eigenvalues` to `HasEigenvalue`.
* **Mathlib has no lemma that a unitary matrix preserves the Euclidean norm** (`‖U.mulVec v‖₂ = ‖v‖₂`).
  Any Givens or QR development needs it built first, via `Matrix.toEuclideanCLM`.
* `FiniteDimensional.proper` needs `[LocallyCompactSpace 𝕜]`, not `[CompleteSpace 𝕜]`. Proximinality
  of finite-dimensional subspaces genuinely fails over a complete but non-locally-compact field.
* Fréchet mean value theorems need `[IsRCLikeNormedField 𝕜]` and `[NormedSpace ℝ E]`, and give only
  a *constant* bound on the derivative difference. The statements really are false over a general
  nontrivially normed field: in characteristic `p`, `x ↦ x + xᵖ` has derivative 1 everywhere.
  A variable bound, needed for a sharp constant, requires
  `image_norm_le_of_norm_deriv_right_le_deriv_boundary` on `ℝ → E`.
* Perturbation of invertible operators between *different* Banach spaces has no direct lemma.
  Route through `T := e.symm ∘L A`, `Units.oneSub`, then `ContinuousLinearEquiv.unitsEquiv`.
  `ContinuousLinearMap.inverse_equiv` bridges the junk-valued `inverse` to a real inverse.
* `Submodule.mem_orthogonal` is `∀ u ∈ K, ⟪u,v⟫ = 0` and `mem_orthogonal'` is the other order.
  There is no lemma `x ∈ (span 𝕜 s)ᗮ ↔ ∀ u ∈ s, ⟪u,x⟫ = 0`; it is four lines by `span_induction`.
* `starProjection` needs `[K.HasOrthogonalProjection]`, free from completeness or finite dimension,
  but a span of a finite family needs its own `FiniteDimensional` instance first.
* Gram-Schmidt: `𝕜` is explicit in `gramSchmidt` and friends, implicit after `gramSchmidtNormed`.
  Mathlib lacks the phase fact `⟪gramSchmidtNormed 𝕜 f n, f n⟫ = ‖gramSchmidt 𝕜 f n‖`, which is what
  pins down the sign when identifying an orthonormalised sequence with a computed one; it is in
  `Numlib/Analysis/InnerProductSpace/GramSchmidt.lean`.
* For an auxiliary positive semidefinite form on a space that already has an inner product, build a
  `PreInnerProductSpace.Core` (marked `@[instance_reducible]`) and apply
  `InnerProductSpace.Core.inner_mul_inner_self_le`; it is defeq to your form, so `exact` works.
* Eigenvalue bounds give quadratic-form bounds in finite dimension with no spectral theorem:
  `LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional` says the extreme Rayleigh quotient
  *is* an eigenvalue. Needs `[Nontrivial E]`; split on `subsingleton_or_nontrivial E` first.
* `WithLp` is a structure now, not a type synonym. `EuclideanSpace.norm_sq_eq` avoids the square
  root and is handier than `norm_eq`.
* Chebyshev: `Trigonometric.Chebyshev.RootsExtrema` has the extremal facts, and `T_real_cosh` with
  `Real.arcosh` gives the closed form in five lines. For `x ≤ -1` use `P.comp (-X)`, not a parity
  argument.
* `IsCompact.exists_isGreatest` with `IsGreatest.csSup_eq` beats `BddAbove` bookkeeping.
* `LinearMap.injective_iff_surjective` is the workhorse for solvability of a compressed system.

## Design conventions of this library

Decided in `plans/backbone.md` §1.7; the short version for a proof author:

* Spectral hypotheses are quadratic-form bounds, `LinearMap.IsSymmetricBoundedBy A lmin lmax`, not
  lists of eigenvalues. Proofs that would use the spectral theorem go through the compression trick:
  compress to the relevant Krylov subspace, where the bounds are inherited, so no
  finite-dimensionality of the ambient space is needed. This works: Kantorovich, the steepest-descent
  rate and the Chebyshev error bounds are all proved this way in arbitrary inner product spaces.
* `Krylov.grade A v` is `Module.finrank K (fullSubspace A v)` under
  `[FiniteDimensional K (fullSubspace A v)]`. No `Fact`, no `ℕ∞`.
* Minimal-error statements name their target: `IsMinError xstar x₀ K x`.
* Breakdown is uniform because `(0:ℝ)⁻¹ = 0`: the Arnoldi expansion and recurrence identities hold
  past the grade with no finiteness hypothesis. Prefer the finiteness-free forms downstream.
* Build an induction on a single invariant record and derive the named lemmas from it, and let the
  private lemmas take the *fact* they need rather than the strong hypothesis. Retrofitting either
  choice is painful.
* The plan's difficulty estimates and suggested routes are guesses made before the proof was found.
  A ★★★ item can have a two-screen proof: Kato's lemma (2.1.7) was budgeted for a gap/angle API
  and fell to a rescaling trick with no adjoints and no completeness. Before building infrastructure
  the plan asks for, spend a little while looking for the elementary argument, and report back when
  the plan overestimated — the estimate is worth correcting for the next reader.
