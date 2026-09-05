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
* Before demoting a tracked declaration out of the plan, grep `plans/*.md` for its name. A
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
* **A missing *import* fails mutely where a missing lemma does not.** Dependencies computed from
  the compiled environment cover definitions only; tactic extensions and instances are invisible to
  that analysis and, when absent, give no hint that an import is what is wanted. Dropping
  `Mathlib.Tactic.Positivity.Finset` makes `positivity` report "failed to prove positivity" as if
  the goal were false; a missing `Normed.Module.Completion` or `SpecialFunctions.Pow.Real` surfaces
  only as "failed to synthesize instance". Suspect the import list before the proof.
* `Numlib.Analysis.Calculus.MeanValue` imports Mathlib's `Analysis.Calculus.MeanValue` but not
  `Analysis.Calculus.Deriv.MeanValue`, where the one-dimensional `exists_hasDerivAt_eq_slope` lives.
* Renaming a file invalidates the Read/Edit tools' file-state tracking: an edit prepared before a
  `git mv` fails with "File has not been read yet". Re-read after the move.
* **An agent forbidden to run `lake build` can still see the style linters.**
  `lake env lean -D weak.linter.mathlibStandardSet=true F.lean` applies Mathlib's standard set
  (`linter.style.longLine` and friends) without taking the build lock or touching the shared
  tracker cache, so parallel agents in one worktree can each meet a "no warnings" bar before the
  merging agent runs the real build.
* The scratchpad directory is shared between concurrently running sub-agents. Give every patch
  script a name of your own (`sor-patch3.py`, not `patch1.py`) or a sibling agent will overwrite it
  between the moment you write it and the moment you run it.

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
* A three-term relation `A v_j = β_j v_{j-1} + α_j v_j + δ_{j+1} v_{j+1}` written with a *normalized*
  `v_{j+1}` is false exactly at a serious breakdown, where `δ_{j+1} = 0` but the unnormalized
  vector is not. "No breakdown for all `j`" is the wrong repair: in finite dimension it never
  holds, because the process terminates. The right hypothesis is the local one, `δ_{j+1} = 0 →
  v̂_{j+1} = 0`, which holds generically *and* at a regular termination
  (`BiLanczos.NoSeriousBreakdown`).

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
* **The index of a structure cannot be rewritten, in either direction.** With `s : Splitting A`,
  the `A` occurs in the *type* of `s`, so any `rw` whose result replaces `A` fails with "motive is
  not type correct" — `rw [← s.m_sub_n]` on a goal mentioning `A`, and equally `rw [s.eq]` for
  `s.eq : A = s.N - s.M`. Which direction happens to work is a symptom, not the rule. Restate the
  identity so that it rewrites a *field* instead: `sub_eq_iff_eq_add.mp s.m_sub_n : s.m = A + s.n`
  replaces `s.m`, which appears in no type, and goes through.
* `open scoped Matrix` is required for `*ᵥ`; without it the error blames
  `Mathlib.Tactic.subscriptTerm` and says nothing about the missing scope.
* The `|a|` notation is a *hygienic* macro for `abs a`, so declaring `Matrix.abs` inside
  `namespace Matrix` does not break `|x|` anywhere. What it does break is any *bare* `abs`,
  `abs_zero`, `abs_nonneg`, … written inside `namespace Matrix` in a file that imports it: those
  now resolve to the `Matrix.`-prefixed names first. `Numlib/LinearAlgebra/Matrix/Order.lean`
  therefore declares only `Matrix.abs` and `Matrix.abs_apply`, and gives every other entrywise
  absolute-value lemma a name that cannot shadow a root one (`entrywiseNonneg_abs`,
  `abs_add_entrywiseLE`, `abs_mul_entrywiseLE`).
* A module that imports only the pieces of Mathlib it needs must import `Mathlib.Tactic.Ring`
  explicitly. Without it `ring` fails as **`unknown tactic`**, not as an unknown identifier, and
  `field_simp` still works (it calls `ring_nf` through its own import), so the diagnosis looks like
  a syntax error in a proof that is fine.
* A **phantom type parameter** — `def Bielecki (a b β : ℝ) : Type := C(Icc a b, ℝ)`, where `β` only
  selects the norm — trips `linter.unusedVariables`. Silence it with
  `set_option linter.unusedVariables false in` placed *before* the docstring.
* Inside `namespace Foo`, naming a lemma `Foo.Bar.rfl` shadows `rfl` for every later proof in the
  namespace, which then fails with a type mismatch against your own lemma. Name it `refl`.
* `set x := e with h` does not make `x`-applications reducible to `e` for `rw`; add
  `have hx : ∀ y, x y = … := fun _ => rfl` and rewrite with that.
* `inner_conj_symm x y : conj ⟪ y, x ⟫ = ⟪ x, y ⟫` — the arguments are in the *opposite* order to
  the inner product being conjugated, so `rw [← inner_conj_symm a b]` rewrites `⟪ a, b ⟫` into
  `conj ⟪ b, a ⟫`. Aiming it at the wrong pair silently rewrites the other factor of a product.
* A bare `map_mul` in a `rw` chain whose goal is headed by `RCLike.re` unifies against `re`, an
  `AddMonoidHom`, and fails with `failed to synthesize MulHomClass (𝕜 →+ ℝ)` rather than with
  anything about the multiplication meant. Name the hom: `map_mul (starRingEnd 𝕜)`.
* `Nat.mul_add_mod` and `Nat.mul_add_div` cancel against the *left* factor (`(?m * ?x + ?y) % ?m`),
  so for a block enumeration `j * p + i` the rewrite is `rw [mul_comm, Nat.mul_add_mod]`; without
  the `mul_comm` the error shows the pattern but not which factor is meant.
* **Pad a `Fin p`-indexed family into `ℕ` with its own `def`, never with an inline `dite`.**
  `f k = (A ^ (k / p)) (if h : k % p < p then v ⟨k % p, h⟩ else 0)` makes every later index rewrite
  fail with "motive is not type correct", because the `Fin.mk` proof mentions the term being
  rewritten. A separate `def pad v i := if h : i < p then v ⟨i, h⟩ else 0` moves the dependency out
  of sight.
* `Submodule.subset_span` passed directly as an argument to
  `Submodule.inner_right_of_mem_orthogonal` fails with "the expected type of this term could not be
  determined": the generating set is fixed only by the *other* argument. Bind the membership as a
  `have` with its type written out.
* `Submodule.mem_span_range_iff_exists_fun` takes the ring `R` as an *explicit* argument, so
  `h.1 hmem` fails with "Projections cannot be used on functions"; write
  `(Submodule.mem_span_range_iff_exists_fun 𝕜).1 hmem`.
* **A missing import can masquerade as broken dot notation.** `LinearMap.IsSymmetric` is a `def`
  that unfolds to a `∀`, so when the module defining `LinearMap.IsSymmetric.foo` is not imported,
  `hA.foo` does not say "unknown identifier": it says *"the environment does not contain
  `Function.foo`, so it is not possible to project the field `foo`"*, and prints the type of `hA`
  as `∀ x y, ⟪ A x, y ⟫ = ⟪ x, A y ⟫`. Nothing in the message mentions the name written. Check the
  import list before believing the notation is at fault.
* `have h : p.degree < (m : ℕ)` fails with "`p.degree` has type `WithBot ℕ`": under `<` the
  ascription on the right fixes the type first, so write `(m : WithBot ℕ)`. The same ascription is
  fine under `=`, which makes the failure look arbitrary.
* A two-step recurrence is easiest to define by carrying the pair `(f j, f (j+1))` through a plain
  structural recursion and projecting: every equation, the one at `j + 2` included, is then `rfl`.
  `Lanczos.polyPair` in `Numlib/Krylov/OrthogonalPolynomials.lean` does this.

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
* `fun_prop` does **not** prove `IntervalIntegrable`. Write
  `Continuous.intervalIntegrable (by fun_prop) _ _` in the integrability slots of
  `intervalIntegral.integral_add`, `integral_sub` and `integral_mono_on`.
* Feeding `simp` a hypothesis about `⟪x, x⟫` is useless when an `@[simp]` lemma rewrites the inner
  product first: `inner_self_eq_norm_sq_to_K` turns `⟪v i, v i⟫` into `(‖v i‖ : 𝕜) ^ 2` before
  `h : ⟪v i, v i⟫ = 1` can fire. Give `simp` the *norm* fact `‖v i‖ = 1` instead.
* To show `a⁻¹ - b ≥ 0` or `a⁻¹ - c⁻¹ ≥ 0` without hunting for the current name of the
  monotonicity lemma, `rw [← sub_nonneg]`, prove the difference equals an explicit quotient by
  `field_simp` (sometimes `field_simp; ring`), and finish with `div_nonneg`. `positivity` will not
  discharge the denominator, since it ignores hypotheses; pass `(mul_pos h1 h2).le` by hand.
* Whether `field_simp` leaves a goal for a trailing `ring` is unpredictable; `ring` on no goals is
  an error. Run the `field_simp` once and look before committing the `ring`.
* `liminf_le_liminf` does not auto-discharge its `IsCoboundedUnder (≥)` side goal.  Neither does
  `Filter.limsup_le_of_le` in `ℝ`: its `isBoundedDefault` autotactic only knows `OrderTop`/
  `OrderBot`.  For a nonnegative sequence it is three lines,
  `⟨0, fun a ha => (hnn k).trans hk⟩` with `k` obtained from `(Filter.eventually_map.mp ha).exists`.
* A lemma applied to `_` placeholders inside a `simp only` list can silently fail to fire, because
  the argument is elaborated before simp sees the goal:
  `simp only [pow_lt_one_iff_of_nonneg (abs_nonneg _) hn]` left the goal untouched where the same
  term in a following `rw` closed it.  Split such a step out of the `simp only`.
* `linarith`/`nlinarith` treat `RCLike.re z` and `z.re` as different atoms although they are
  `rfl`-equal at `𝕜 = ℂ`.  Give each `have` the spelling you want as an explicit type annotation;
  the transfer is then a defeq check that `exact` performs silently.
* **`simp` normalizes `ℕ` literals, so a disequality handed to it may not match.** After
  `rw [h : i + 1 = m]` the goal can contain `j + 1 + 1`, which `simp` rewrites to `j + 2`; a
  `(by omega : ¬(j + 1 + 1 = j))` passed as a simp argument is then reported *unused* while the
  goal it was meant to close survives as an implication. Evaluate `ite`s deterministically with
  `ite_eq_left h` / `ite_eq_right h` instead, one per occurrence (`rw` rewrites only the first
  instantiation, so a condition shared by two `ite`s with different branches needs two rewrites).
* `hk : k ∈ Set.Iio m` is not an arithmetic hypothesis as far as `omega` is concerned; re-bind it
  with `have hk' : k < m := hk` first.
* `gcongr` often closes the whole subgoal including the side conditions, so a following `exact …`
  errors with "No goals to be solved" — the same trap as `field_simp`.
* `rw [← Finset.sum_map …]` does not fire against `∑ j, F (Fin.castLE h j)`: the higher-order
  pattern `?f (?e x)` will not unify. State the collapse as a `have` with all three arguments
  explicit, `(Finset.sum_map Finset.univ (Fin.castLEEmb h) F).symm`, and `rw` with that.
* `rw [← one_pow 2]` to introduce a square rewrites the `1` inside every `m + 1` in the goal and
  then fails with "motive is not type correct" on the `Fin`/`castLE` proofs that depend on it.
  Compute the sum forward into a named `have` and rewrite with that.
* `positivity` does not know `0 ≤ Lanczos.beta A b j`; write
  `mul_nonneg (beta_nonneg A b m) (abs_nonneg _)`.
* `induction n using Nat.twoStepInduction` names its cases `zero`, `one`, `more`, and `more` binds
  `n`, `P n`, `P (n+1)` — not `H1/H2/H3`.

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
* **There is no `Abs` class.** `abs` is `def abs [Lattice α] [AddGroup α] (a : α) : α`, the
  `to_additive` image of `mabs a = a ⊔ a⁻¹`, so a binder `[Abs α]` fails with "type is not a class
  instance". `abs_nonneg` and `abs_zero` need order compatibility on top (`IsOrderedAddMonoid`, or
  the unbundled `AddLeftMono`/`AddRightMono`), and the triangle inequality is `abs_add_le`, not
  `abs_add` — the latter does not exist.
* `Matrix` has **no order instances at all** outside the Loewner ones scoped in `MatrixOrder`
  (`Mathlib/Analysis/Matrix/Order.lean`), because `Matrix m n α` is an opaque `def` for
  `m → n → α`. So `A ≤ B` on matrices simply does not elaborate by default, while `x ≤ y` and `|x|`
  on *vectors* are the `Pi` ones and are entrywise already. That asymmetry is why
  `Numlib/LinearAlgebra/Matrix/Order.lean` states `A ≤ₑ B` for matrices and plain `≤`/`|·|` for
  vectors in the same theorem.
* Before proving entrywise facts by hand: `Matrix.pow_apply_nonneg` (in `Mathlib.Data.Matrix.Mul`)
  already gives `0 ≤ (A ^ k) i j` from `0 ≤ A i j`, and `Matrix.mulVec_apply_eq_sum` is the `rfl`
  lemma for `(A *ᵥ x) i`. `Matrix.sum_apply` is in `Mathlib.Data.Matrix.Basic`, *not* in
  `.Mul` — importing only the latter makes it an unknown constant.
* `abs_add` does not exist; the triangle inequality for `|·|` is **`abs_add_le`**, and `abs_sub`
  is not the `|a - b| ≤ |a| + |b|` one either — go through `sub_eq_add_neg` and `abs_neg`.
  `add_le_add_right h c` adds `c` on the *left* of both sides here, so prefer `add_le_add h le_rfl`.
* `Finset.prod_le_prod` (the ordered-semiring one, with a nonnegativity side condition) lives in
  `Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset`, not in the `Ring` directory.
* `FloorSemiring.tendsto_pow_div_factorial_atTop x : Tendsto (fun n => x ^ n / n !) atTop (𝓝 0)`
  is in `Mathlib.Topology.Algebra.Order.Floor`. It is what turns a factorial bound into "some
  power of this map is a contraction".
* `inv_anti₀ (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹`; `RCLike.abs_re_le_norm z : |re z| ≤ ‖z‖`;
  `RCLike.conj_mul z : conj z * z = ‖z‖ ^ 2`; `one_add_mul_le_pow (H : -2 ≤ a) n` is Bernoulli.
* `IsCompact.exists_isMaxOn hs hne hf : ∃ x ∈ s, IsMaxOn f s x` is the extreme value theorem to
  reach for on a `CompactSpace`: `isCompact_univ.exists_isMaxOn Set.univ_nonempty f.continuous.continuousOn`,
  then `isMaxOn_iff.1`. `Continuous.exists_forall_ge` is about cocompact behaviour, not this.
* Parametric interval integrals over `C(Set.Icc a b, ℝ)`: clamp the real integration variable with
  `Set.projIcc a b hab` (continuous, and `projIcc_of_mem` evaluates it on the interval), then
  `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` for fixed endpoints and
  `…_of_continuous` for a variable upper limit. Both live in
  `Mathlib.MeasureTheory.Integral.DominatedConvergence` and need only `[TopologicalSpace X]`.
* To renorm a type with a weight, do not build a `NormedAddCommGroup` by hand: make the type a
  plain `def` synonym, copy `AddCommGroup`/`Module` with `inferInstanceAs`, and take
  `NormedAddCommGroup.induced E F f hinj` along the weighting `LinearMap`'s `toAddMonoidHom`. Then
  `‖x‖ = ‖f x‖` is `rfl`, `NormedSpace` is one `le_of_eq`, and completeness transfers by
  `(isometry_f.isUniformInducing.completeSpace_congr f_surjective).2 inferInstance`.
* There is no `ContinuousLinearMap.coe_pow`; `hom_coe_pow _ rfl (fun _ _ => rfl) L n` proves
  `⇑(L ^ n) = (⇑L)^[n]` in one line.
* From a spectral value of a *continuous* operator to an eigenvector: `ContinuousLinearMap.spectrum_eq`
  (`spectrum 𝕜 f = spectrum 𝕜 (f : Module.End 𝕜 E)`, needs `CompleteSpace`) and then
  `Module.End.hasEigenvalue_iff_mem_spectrum` in finite dimension.  In the other direction,
  `spectrum.spectralRadius_lt_of_forall_lt` turns "every spectral value has modulus `< r`" into
  `ρ < r` with no finiteness of the spectrum; it needs `Nontrivial (E →L[ℂ] E)`, so split on
  `subsingleton_or_nontrivial E` first, exactly as `Stationary/Basic.lean` already does.
* `Matrix.det_zero` takes `Nonempty n` as an *instance*, not an explicit argument.
* `le_of_forall_pos_le_add` exists only for `ℝ≥0∞`.  Over `ℝ` the tool is
  `le_of_forall_gt_imp_ge_of_dense`.
* `ℝ≥0∞` is notation from `open scoped ENNReal`; in a file without it, write `ENNReal` — the error
  is an unhelpful `expected token`.
* `Matrix.PosDef` over `ℂ` needs `open scoped ComplexOrder`, and `Matrix.posDef_diagonal_iff` needs
  a `StarOrderedRing`, whose instance for `ℝ` lives in `Mathlib.Algebra.Order.Star.Real`, which
  `Numlib` does not otherwise import.  `Matrix.PosDef`'s *statement* no longer mentions `Fintype` or
  `DecidableEq`, so a lemma about it whose proof goes through `toEuclideanLin` trips
  `linter.unusedFintypeInType` and `linter.unusedDecidableInType`.
* There is no `abs_le_max_abs_abs`; `p ≤ x → x ≤ q → |x| ≤ max |p| |q|` is one `abs_le.2` with
  `neg_abs_le` and `le_abs_self`.  Nor is there a `c ^ (1/k) → 1` for a constant `c > 0` indexed by
  `ℕ`: `Real.rpow_def_of_pos` with `tendsto_one_div_atTop_nhds_zero_nat` is four lines.
* `abs_sub` and `div_le_div_of_nonneg_right` do not exist in this toolchain: for
  `|a - b| ≤ |a| + |b|` use `abs_sub_le a 0 b` and `simpa`, and for `a/c ≤ b/c` use `gcongr`.
* **Real parts of an infinite sum.** `HasSum.map (RCLike.re : 𝕜 →+ ℝ) RCLike.continuous_re` takes
  real parts of a `HasSum`; with `HilbertBasis.hasSum_inner_mul_inner b v v` it gives Parseval as
  `HasSum (fun i => ‖⟪ b i, v ⟫‖ ^ 2) (‖v‖ ^ 2)`, which Mathlib does not state.
* **A diagonal operator needs no continuity.** For symmetric `T` with `T (φ i) = ν i • φ i` in a
  `HilbertBasis`, do *not* push `T` through `HilbertBasis.hasSum_repr` — that would need `T`
  bounded, i.e. Hellinger–Toeplitz and `[CompleteSpace E]`. Compute the coefficient directly,
  `⟪ φ i, T v ⟫ = ⟪ T (φ i), v ⟫ = ν i ⟪ φ i, v ⟫`, then apply Parseval to `v` and `T v` separately.
  This gives `‖T v‖ ≤ (sup |ν|) ‖v‖` and `IsSymmetricBoundedBy` with no completeness anywhere.
* AM–GM in the `(∏ b)^{1/k} ≤ (∑ b)/k` form is `Real.geom_mean_le_arith_mean` with all weights `1`;
  `Real.rpow_inv_natCast_pow` raises it back to `∏ b ≤ ((∑ b)/k)^k`, and
  `Real.continuous_const_rpow (h : a ≠ 0)` is what makes `a^{1/(2k)} → 1`.
* `Filter.Tendsto.div` produces the `Pi.div` form `f / g`, which `simpa` will not turn back into
  `fun j => f j / g j`; rewrite the limit value in the hypothesis and close with `exact` instead.
* Ritz values as matrix eigenvalues is four names deep and no more: `LinearMap.charpoly_toMatrix`,
  `Matrix.charpoly_map` (`(M.map f).charpoly = M.charpoly.map f`),
  `Matrix.mem_spectrum_iff_isRoot_charpoly` and `LinearMap.spectrum_toMatrix` — the last lives in
  `Mathlib.LinearAlgebra.Eigenspace.Matrix`, which `Numlib` does not otherwise import.
  `Polynomial.eval_map` with `Polynomial.eval₂_hom` moves a real root across `algebraMap ℝ 𝕜`.
* `Polynomial.modByMonic_add_div p q : p %ₘ q + q * (p /ₘ q) = p` takes **no** monic hypothesis
  (both sides are junk-defined so that it holds anyway); `degree_modByMonic_lt` and
  `natDegree_divByMonic` do take one. `natDegree_C_le` does not exist — use `(natDegree_C _).le`.
* `integral_finset_sum_measure` is deprecated in favour of `integral_finsetSum_measure`;
  `integrable_dirac (by simp)` supplies its integrability side conditions for a scaled Dirac sum.
* `Matrix.inv_diagonal` reads `(diagonal v)⁻¹ = diagonal v⁻¹ʳ`, and `v⁻¹ʳ` is `Ring.inverse`
  applied to the whole *Pi* element, which does not reduce entrywise. For
  `(diagPart A)⁻¹ = diagonal fun i => (A i i)⁻¹` you need `IsUnit (diagPart A)` and
  `Matrix.inv_eq_left_inv`; without it the statement is false, since a singular diagonal inverts
  to `0`.
* `Matrix.finite_spectrum` (in `Mathlib.LinearAlgebra.Eigenspace.Minpoly`, not in the spectrum
  files) turns "every eigenvalue has modulus `< 1`" into `ρ < 1` in five lines through
  `Finset.sup'` over `hfin.toFinset`; there is no need for a norm on `Matrix n n ℂ` and hence no
  instance-mixing hazard. `Finset.sup_lt_iff` wants `⊥ < a`, `Finset.sup'_lt_iff` wants nothing.
* Nonemptiness of the spectrum of a complex matrix is `Matrix.mem_spectrum_iff_isRoot_charpoly`
  plus `Matrix.charpoly_degree_eq_dim` plus `IsAlgClosed.exists_root` — again with no Banach
  algebra instance in sight.
* `spectrum.units_conjugate` is stated as `spectrum R (↑u * a * ↑u⁻¹)`. Write both coercions with
  explicit type ascriptions: `↑u⁻¹` on matrices otherwise elaborates as the *matrix* inverse of
  `↑u`, and the `rw` then silently fails to match.
* `Complex.sq_norm : ‖z‖ ^ 2 = normSq z` with `Complex.normSq_apply` is the route from a norm to
  `re² + im²`; `Complex.abs` is gone.
* `mul_lt_mul_left` now asks for a `MulRightStrictMono` instance that `ℝ` does not have in that
  form; `mul_lt_mul_of_pos_left` is the usable name.
* For an identity between complex numbers that is really an identity between reals, do the algebra
  in `ℝ` and cast once inside a `calc` with `push_cast; ring` at each step. Rewriting with
  `Complex.ofReal_add`/`_sub`/`_mul` in the middle of a goal loses to the first `↑(a - b)` that is
  not literally in that shape.

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
