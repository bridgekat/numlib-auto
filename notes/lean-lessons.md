# Lean and Mathlib lessons

A running record of what worked and what did not while formalizing this project, kept so that a
new agent does not repeat a dead end. Add an entry whenever you lose more than a few minutes to
something a note would have prevented. Keep entries short and specific: symptom, cause, fix.

Pinned toolchain: Lean `v4.34.0-rc2`, Mathlib `v4.34.0-rc2` under `.lake/packages/mathlib`.

## Working in this repository

* Build one module with `lake build Numlib.Krylov.CG`, everything with `lake build`.
* **`lake update` is a global operation when sub-agents are running, and will stall all of them.**
  `scripts/mkwt.ps1` makes a worktree cheap by junctioning its `.lake/packages` to the main
  checkout's, so every worktree shares one copy of Mathlib and of every other dependency. Changing
  a dependency there invalidates the build cache in all of them at once, and five worktrees then
  start full rebuilds that contend for the same cores. The isolation a worktree gives you covers
  source files, not packages: never touch the dependency set while agents are working.
* A shared `.lake/packages` also means a *concurrent* build elsewhere can make yours die with
  spurious `failed to read file '<mathlib>.olean'` or `failed to open file '….ir'`. That is I/O
  contention, not your code: retry rather than debug. And `lake` has no `-j`/`--jobs` flag, so
  there is no way to throttle a build when worktrees contend — stagger them instead.
* `lake exe tracker lint --no-check` prints `ok` and exits 0 when no cache exists at all, which is
  indistinguishable from "zero warnings". Run one full `lake exe tracker check` before trusting any
  later `--no-check` reading.
* Before demoting a tracked declaration out of the plan, grep `tracker/*.md` for its name. A
  declaration that looks like a throwaway `rfl` companion in Lean can be a numbered equation the
  book prose cites: `Krylov.gamma_succ` is `rfl`, and it is Saad's (6.47).
* A `lake update` interrupted partway leaves the package checkout and `lake-manifest.json`
  disagreeing — the manifest records the new revision while the working tree sits at the old one,
  and the built binary is then silently the old one. Check with
  `git -C .lake/packages/<dep> log --oneline -1` against the manifest's `rev`, not with the
  manifest alone.
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
* In a Python patch script every non-BMP character must be written as a `\U…` escape: `\U0001d55c`
  for `𝕜`, `\U0001d4ab` for `𝒫`, `\U0001d4dd` for `𝓝`. A raw surrogate pair silently fails to match
  and, on Windows, raises `UnicodeEncodeError` *on write* — after the file has already been
  truncated. Two agents have destroyed a file this way; the temp-file-and-`os.replace` discipline
  above is what makes such a failure harmless.
* The same trap applies to the *script itself*: a bash heredoc mangles non-BMP characters in the
  Python source you are feeding it, so a patch whose search string contains one silently fails to
  match. Write such a patch with the Write tool, or use the Edit tool directly.
* The Lean sources here use LF, and every writer must keep it that way. A Python patch script has
  to open with `io.open(p, 'w', encoding='utf-8', newline='')`, or it silently converts the file to
  CRLF and the whole file shows as changed.
* Line length: the only authority is `linter.style.longLine`. Counting with `awk length>100`
  over-reports, because it counts bytes and the mathematical symbols are multi-byte.
* **`lake env lean F.lean` does not apply the `leanOptions` of `lakefile.toml`**, so the Mathlib
  style linters are silent under it. Always run a real `lake build` before committing, or the long
  lines and unused variables only surface at merge time.
* Imports must precede the module doc comment, not follow it.

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
* To `rw` with a `def`, add a private `foo_def : foo x = … := rfl` companion. This is not optional
  for a body shaped like `Function.iterate`, where `rw [thatDef]` simply fails.
* **A surface wrapper of backbone data wants `noncomputable abbrev`, not `def`**, whenever the
  backbone lemmas about it are stated unwrapped: a `def` is opaque to unification, so
  `rw [backboneLemma]` stops matching. This bit the Saad Chapter 6 files on `r₀` and `β`.
  Conversely `rw` will not see through an `abbrev` when the lemma's head is `DFunLike.coe`
  (`map_smul`, `map_add`) — there `simp only` works, or state the unfolded equation as a `have`.
* **A `termination_by` definition does not reduce definitionally**, so `rfl` fails on its
  `_zero`/`_succ` companions: every one needs `rw [f, fAux]`, and a right-hand side mentioning the
  function at `j + 1` must first be rewritten down to `≤ j`. Factoring the recursion *body* into a
  separate plain `def` restores `rfl` for the projections, and lets variant algorithms that share a
  body be compared by a single lemma — that is how ORTHOMIN(k) reduces to GCR in four lines.
* At `𝕜 = ℝ` an `RCLike.ofReal` coercion silently blocks `rw` against an `RCLike`-polymorphic
  lemma. Write the scalar as `((‖x‖ : 𝕜))⁻¹` in the polymorphic layer and `simpa` when specializing.
* Structure-instance continuation lines must indent past the `{`.
* Lemmas whose statement does not mention the scalar field need it supplied, as in
  `norm_sub_sq (𝕜 := 𝕜)`; otherwise the instance problem is stuck on `InnerProductSpace ?m E`.
* `linter.unusedDecidableInType` fires on a `[DecidableEq ι]` binder absent from the statement;
  drop it and open the proof with `classical`.
* `ExistsUnique` goals arrive beta-unreduced; prefix the uniqueness branch with `show ∀ v, …`.
* A `local notation` used inside a `variable` binder silently breaks section-variable inclusion:
  the variable becomes an unknown identifier in term-mode bodies. Write the type out in binders.
* Dot notation resolves through the *unfolded* head, which bites on `def`s that unfold to a
  connective: `ConvexOn`/`StrictConvexOn` unfold to `And`, so `h.foo` on such a hypothesis looks up
  `And.foo`, and a project lemma named `ConvexOn.foo` must be applied by its full name. The same
  happens on an `IsIdempotentElem` hypothesis, which resolves into `Eq`, on `Matrix.PosDef`
  (`hA.eigenvalues_pos` looks up `And.eigenvalues_pos`), and on `Algebra.commutes c A`, which is an
  `Eq`, so `.mul_left` is `Eq.mul_left` — bind `have _ : Commute … := Algebra.commutes c A` first.
* For an equation whose left side mentions a structure parameter (`s.eq : A = s.N - s.M` with
  `s : BookSplitting A`), only `rw [← s.eq]` type-checks; the forward direction fails with "motive
  is not type correct".
* `open scoped Matrix` is required for `*ᵥ`; without it the error blames
  `Mathlib.Tactic.subscriptTerm` and says nothing about the missing scope.

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
* Never put a definition's unfolding lemma in the same `simp only` set as lemmas stated *about* that
  definition: the unfolding fires first and the others no longer match.
* `refine ⟨y, by …⟩` leaves the inner goal beta-unreduced, so `rw` fails inside it. Hoist the
  component to a `have` with an explicit type.
* `Orthonormal.comp` with `_` for the index embedding times out in `whnf`; pass the embedding
  explicitly.
* `simp only [map_sub, …]` can dissolve an opaque term you are mid-argument about; abstract the
  algebra into a `have` so the tactic cannot see inside.
* `rw` rewrites only the first instantiation of a lemma like `ite_eq_left`; with several `ite`s
  sharing a condition use `simp only`.
* `split_ifs` silently *discards* a branch whose condition contradicts a hypothesis already in
  context, so the number of goals depends on the context. Do not guess the bullet count; write the
  `ite` rewrites explicitly, or check first.
* `rw [Nat.add_sub_cancel]` fails with "motive is not type correct" whenever the goal carries a
  `Fin` index such as `⟨m - 1, proof⟩`. Do the arithmetic in a `have` first.
* `rw […, add_comm]` followed by `congr 1` is fragile; factor the reordering into a `have`.
* Well-founded induction along a finite linear order: `induction i using WellFoundedLT.induction`.
* Higher-order unification defeats several composition lemmas when the expected type is written as
  an explicit lambda: `HasFDerivAt.comp_hasDerivAt` against `fun t => f (g t)`, and
  `HasDerivAt.scomp` when the inner function is applied at a point. Bind the composite with a
  `have` whose type you state, then `exact` it.
* `Filter.Tendsto.const_mul` takes the constant as a leading *explicit* argument, so it will not
  elaborate inline inside `squeeze_zero`; nor can `squeeze_zero` infer its `g` from
  `refine … (fun k => ?_) ?_`. Bind the bound as a named `have` first.
* `positivity` ignores hypotheses: `S + s ≠ 0` from `0 < s` and `s < S` needs
  `ne_of_gt (by linarith)`.
* `liminf_le_liminf` does not auto-discharge its `IsCoboundedUnder (≥)` side goal.

## Mathlib names and API

`pow_left_inj₀ ha hb hn : a ^ n = b ^ n ↔ a = b` is the way to cancel the squares after comparing
two norms through `norm_add_sq`.

A real `V →L[ℝ] V →L[ℝ] ℝ` *is* a `SesqForm ℝ V` by definition, so bridges between them are
`Iff.rfl` — and `simp` cannot prove them, because the two coercion paths differ. Unification of
`starRingEnd ℝ` against `RingHom.id ℝ` also gets stuck, so pass `(𝕜 := ℝ)` explicitly.
`NormOneClass (E →L[𝕜] E)` now needs `NontrivialTopology`.

`if_pos`/`if_neg` are deprecated *and so is the replacement the deprecation warning suggests*
(`ite_cond_eq_true`). The live names are `ite_eq_left_of_eq_true a b (eq_true h)` and
`ite_eq_right_of_eq_false a b (eq_false h)`. `Finset.range_subset` is not the `↔` one expects;
supply the subset pointwise.

Deprecated or renamed in this toolchain: `if_pos`/`if_neg` to `ite_eq_left`/`ite_eq_right`;
`push_neg` to `push Not`; `Matrix.dotProduct` to root-level `dotProduct`; `LinearMap.mul_apply` to
`Module.End.mul_apply`; `orthogonalProjection` to `Submodule.orthogonalProjectionOnto` and
`Submodule.starProjection`; `ContinuousLinearMap.{sub,add,smul,sum}_apply` to the root-namespace
names and `ContinuousLinearMap.one_apply` to `one_apply_eq_self`; `Matrix.det_of_lowerTriangular` to
`det_of_isLowerTriangular`; `div_le_div_iff` to `div_le_div_iff₀`; `LinearMap.range_coe` to
`LinearMap.coe_range`; `linearIndependent_fin_succ'` to `linearIndependent_finSucc'`;
`Polynomial.degree_sub_lt` to `degree_sub_lt_left`; `Set.mem_setOf_eq` to `Set.mem_ofPred_eq`;
`RCLike.conj_conj` is only an alias, prefer `starRingEnd_self_apply`.
`sub_eq_sub_iff_add_eq_add`, `div_add_div_same`, `PiLp.sum_apply`, `Finset.range_subset` as an
`iff` and `LinearMap.one_apply` do not exist; for the last two use `Module.End.one_apply` and, for
`div_add_div_same`, `← add_div`.
`RCLike.inner_apply` orients as `⟪x, y⟫ = y * conj x`.

Structural facts worth knowing before planning a proof:

* **Gelfand's formula** is in `Mathlib.Analysis.Normed.Algebra.GelfandFormula`, not `…Algebra.Spectrum`.
  With `spectrum.spectralRadius_pow_le`, `spectralRadius_le_nnnorm` and `ENNReal.rpow_inv_natCast_pow`
  the whole `ρ(a) < 1 ↔ aⁿ → 0` story is short. Stay in `ℝ≥0∞`.
* `Summable.tsum_pow_mul_one_sub` gives `(∑' xⁿ)(1-x) = 1` from summability alone: that is the route
  from `ρ(a) < 1` to `IsUnit (1 - a)`. `tsum_geometric_le_of_norm_lt_one` is stated without
  `NormOneClass`, so state Neumann helpers with an explicit `‖(1:R)‖ ≤ 1` and they also apply to
  `E →L[𝕜] E`, which is `NormOneClass` only for nontrivial `E`. `NormOneClass` does not give
  `Nontrivial` by instance search; it is the theorem `NormOneClass.nontrivial`.
* **A class argument is a quantifier — over any type, concrete or variable — and a statement must
  not mix a quantified structure with a canonical one on the same type.** That is the real trap,
  not quantification itself. `[NormedRing (Matrix n n ℝ)]` bundles its own `Ring`, so in
  `complexSpectralRadius A ≤ ‖A‖₊` the norm is taken against an arbitrary ring structure while the
  left-hand side is computed from `Matrix.instRing`; nothing ties the two together, and the
  structure transported along a bare bijection `Matrix n n ℝ ≃ ℝ` satisfies every hypothesis while
  making the claim false. On a type *variable* the same quantification is harmless precisely
  because there is no second structure in play: everything in the statement flows through the one
  instance. The danger sign is a concrete type, because that is where a canonical instance also
  exists for the rest of the statement to pick up silently. `Matrix.complexSpectralRadius_le_of_norm`
  was false this way for a while. Check with `set_option pp.explicit` and look for two different
  instance paths for the same type; state what you need with a plain function argument, or with
  classes that take the algebraic operations as instance parameters so they are shared.
* Adding `NormedAlgebra ℝ` does not repair it: `ℝ` is an `ℝ`-algebra, so the transported structure
  is one too. And even against the canonical structures, submultiplicativity plus absolute
  homogeneity plus `‖1‖ = 1` do **not** bound the spectral radius — `B ↦ |det B|^(1/2)` satisfies
  all three and vanishes on a rank-one two-by-two matrix of spectral radius `1`. Positive
  definiteness is the missing third hypothesis.
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
* Mathlib has no lemma that a unitary matrix preserves the Euclidean norm; this project now does,
  as `Matrix.norm_toLp_mulVec_of_mem_unitaryGroup` and friends in `Analysis/Matrix/ToEuclideanLin`.
  The route is three lines: `Matrix.toEuclideanCLM` is a star-algebra equiv, so it carries
  `unitaryGroup` into `unitary`, and then `ContinuousLinearMap.norm_map_of_mem_unitary` applies.
* `Fin.snoc` is dependently typed and its motive is not inferred at use sites from a plain
  `Fin (n+1) → 𝕜`. Package the extension once as
  `∃ z, (∀ j, z j.castSucc = y j) ∧ z (Fin.last n) = 0` and never mention `snoc` again.
* `rw [Finset.sum_eq_single a]` closes the main goal itself when the residual equation is `rfl`, so
  the number of remaining goals varies; check before writing three bullets.
* `unitary.mem_iff` is spelled `Unitary.mem_iff`. After `EuclideanSpace.norm_sq_eq` a bare
  `simp only []` is what beta-reduces `(toLp 2 f).ofLp i` to `f i`.
* `FiniteDimensional.proper` needs `[LocallyCompactSpace 𝕜]`, not `[CompleteSpace 𝕜]`. Proximinality
  of finite-dimensional subspaces genuinely fails over a complete but non-locally-compact field.
* To run a real-segment mean value argument over an `IsRCLikeNormedField 𝕜` you do **not** need
  `[NormedSpace ℝ F]`, `[IsScalarTower ℝ 𝕜 E]` or `[IsScalarTower ℝ 𝕜 F]` as binders, which is what
  makes the sharp Newton constant free. Inside the proof write
  `let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜` and
  `let _ : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F`; both towers then come from the global
  `Real.isScalarTower` and `HasFDerivAt.restrictScalars ℝ` applies. Mathlib's own
  `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` does exactly this.
* `HasFDerivAt.comp_hasDerivAt` fails to elaborate against an expected `fun t => f (g t)` (the
  higher-order unification against `f ∘ g`). Bind it with `have h := …` first, then `exact h`.
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
  root and is handier than `norm_eq`. In the literal notation `!₂[…]` the subscript is the `Lp`
  exponent, not the dimension. `Matrix.cons_val_two` is not `@[simp]`, and `vecHead`/`vecTail` need
  unfolding when a `smul` sits under them.
* `Krylov.firstVec ‖b‖` keeps an `RCLike.ofReal` coercion even at `𝕜 = ℝ`; clear it with
  `simp [RCLike.ofReal_real_eq_id, id_eq]`.
* Chebyshev: `Trigonometric.Chebyshev.RootsExtrema` has the extremal facts, and `T_real_cosh` with
  `Real.arcosh` gives the closed form in five lines. For `x ≤ -1` use `P.comp (-X)`, not a parity
  argument. `Polynomial.Chebyshev.C` exists, so a local `C` clashes — use a selective
  `open Ns (a b c)`; and `T ℝ k` is noncomputable, so a wrapper needs `noncomputable abbrev`.
* `Matrix.PosDef.eigenvalues_pos` lives in `Mathlib.Analysis.Matrix.PosDef`, which `Numlib` does not
  import. `IsSymmetricCoercive.re_pos_of_hasEigenvalue` with
  `Matrix.IsHermitian.hasEigenvalue_toEuclideanLin_iff` gets there in four lines and no new import.
* `IsCompact.exists_isGreatest` with `IsGreatest.csSup_eq` beats `BddAbove` bookkeeping.
* `LinearMap.injective_iff_surjective` is the workhorse for solvability of a compressed system.

## Design conventions of this library

Decided in `tracker/backbone.md` §1.7; the short version for a proof author:

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
