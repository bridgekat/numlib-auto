# Lessons from `Numlib/Eigen/Normal.lean`

Written while proving the normal-operator spectral theory, discharging the last `sorry` of the
library (Saad §6.10, `exists_aeval_eq_conjTranspose_of_isStarNormal`), and then proving Saad's
Lemma 6.23 on top of it. Symptom, cause, fix — for folding into `notes/lean-lessons.md`.

## The mathematics: normal ⟹ diagonalizable, with no Schur form

The textbook proof of "a normal matrix is unitarily diagonalizable" goes through the Schur form,
which Mathlib does not have, and this made the item look like a large piece of missing
infrastructure for months. It is not. The whole chain is four short steps and never constructs a
unitary `Q`:

1. `‖A† v‖ = ‖A v‖` for normal `A`, because `⟪v, (A† A) v⟫` and `⟪v, (A A†) v⟫` are the two squared
   norms and normality equates the operators. Hence `ker A† = ker A`.
2. `ker N² = ker N` for normal `N`: if `N (N x) = 0` then `N x ∈ ker N = ker N†`, so
   `‖N x‖² = ⟪N† (N x), x⟫ = 0`. Induction gives `ker Nᵏ = ker N` for `k ≠ 0`.
3. A shift `A - μ` of a normal operator is normal, so by 2 every maximal generalized eigenspace of
   `A` is an eigenspace.
4. `Module.End.iSup_maxGenEigenspace_eq_top` (`Mathlib/LinearAlgebra/Eigenspace/Triangularizable`)
   makes the maximal generalized eigenspaces span over any `[IsAlgClosed 𝕜]` in finite dimension.
   With 3, the *eigenspaces* span. That is diagonalizability.

Step 2 applied to `A - μ` also gives `eigenspace A† (conj μ) = eigenspace A μ` in one line — the
easy half of Saad's Lemma 1.15 — since `(A - μ)† = A† - conj μ`.

Only steps 4 and its consequences need algebraic closure; 1–3 and the eigenspace identity hold over
`ℝ` too. State them that way: the hypothesis is the documentation.

Saad's Lemma 1.15 has a second half — an operator that shares its eigenvectors with its adjoint is
normal — which reads in the book as if it needed the full spectral theorem. It does not, and it
reuses the same four steps: `⟪x, A† x⟫ = ⟪A x, x⟫` pins the adjoint eigenvalue to `conj μ`, and the
*same* identity applied to `(A - μ) u = x` gives `‖x‖² = 0`, so `ker (A - μ)² = ker (A - μ)` again.
Factor steps 2–4 to take `ker N ≤ ker N†` as the hypothesis rather than normality, and both
directions of Lemma 1.15 fall out of one private lemma each.

## The "agree on a spanning family" pattern

Two operators that agree on each of a family of submodules whose supremum is `⊤` are equal. Doing
this by `Submodule.iSup_induction'` is clumsy. This is three lines:

```lean
have hker : (⨆ μ : 𝕜, eigenspace A μ) ≤ ker (aeval A q - A.adjoint) :=
  iSup_le fun μ x hx => by rw [mem_ker, sub_apply, sub_eq_zero]; exact key μ x hx
rw [hA.iSup_eigenspace_eq_top, top_le_iff, ker_eq_top] at hker
exact sub_eq_zero.1 hker
```

It is what turns "`q(A)` and `A†` both act as `conj μ` on the eigenspace at `μ`" into `q(A) = A†`.

## Index a family of eigenvectors by a `Finset 𝕜`, not by `Module.End.Eigenvalues`

Saad's Lemma 6.23 wants a vector `w = ∑ x_i` with one nonzero `x_i` per eigenspace. The obvious
index type is `Module.End.Eigenvalues T`, and it costs a coercion in every summand — `∑ i, conj ↑i •
x i`. That is worse than it looks: in a sum binder with no annotation, Lean elaborates `(i : 𝕜)`
by giving `i` the type `𝕜`, so `x i` then fails with "argument `i` has type ℂ" and the real error is
a stray `failed to synthesize Fintype ℂ`. Annotating every binder works but is noisy.

Index by `S : Finset 𝕜` instead — `(Module.End.finite_hasEigenvalue T).toFinset` — and make the
choice total with a junk value so `choose` produces `x : 𝕜 → E` rather than something dependent on
a membership proof:

```lean
have hexists : ∀ μ : 𝕜, ∃ y : E, μ ∈ S → y ∈ eigenspace T μ ∧ y ≠ 0 := by
  intro μ; by_cases hμ : μ ∈ S
  · obtain ⟨y, hy⟩ := (…).exists_hasEigenvector; exact ⟨y, fun _ => ⟨hy.1, hy.2⟩⟩
  · exact ⟨0, fun hc => absurd hc hμ⟩
choose x hx using hexists
```

Every sum is then over `∑ μ ∈ S, …` with `μ : 𝕜`, there is no coercion anywhere, and
`Finset.sum_eq_single_of_mem` extracts a coefficient in one line. `Module.End.HasEigenvalue` is a
`≠ ⊥` in disguise, so dot notation on `i.2` resolves into `Function`; write
`Module.End.HasEigenvalue.exists_hasEigenvector i.2` in full.

## Name-resolution traps

* **Dot notation does not reach a lemma named `LinearMap.IsStarNormal.foo`.** `IsStarNormal` is a
  root-level class, so `hA.foo` looks up `_root_.IsStarNormal.foo` and reports "the environment does
  not contain `IsStarNormal.foo`" — *even inside `namespace LinearMap`, and even in the very next
  declaration*. Every use has to be spelled `IsStarNormal.foo hA` (which does resolve to
  `LinearMap.IsStarNormal.foo` inside the namespace) or fully qualified from outside. Mathlib's
  `ContinuousLinearMap.IsStarNormal.ker_adjoint_eq_ker` has the same shape and the same cost. The
  error cascades: one failed declaration makes every later `hA.foo` report the same thing, so fix
  the *first* error and rebuild rather than reading the list.
* **Inside `namespace LinearMap`, a bare `id` is `LinearMap.id`.** Passing it as the nodal map to
  `Lagrange.interpolate s id r` produced `typeclass instance problem is stuck: Module ?m 𝕜`, which
  says nothing about the real cause. Write `_root_.id`. The same hazard exists for any short
  Mathlib name that `LinearMap`, `Matrix` or `Module.End` also owns.

## Mathlib API found and not found

* `ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint`,
  `ContinuousLinearMap.IsStarNormal.adjoint_apply_eq_zero_iff` and
  `ContinuousLinearMap.IsStarNormal.ker_adjoint_eq_ker` exist
  (`Mathlib/Analysis/InnerProductSpace/Adjoint.lean`, ~line 415). **There are no `LinearMap`
  versions.** Do not transport through `LinearMap.toContinuousLinearMap`: the direct proof for
  `E →ₗ[𝕜] E` is eight lines and needs no `CompleteSpace` juggling.
* `Module.End.aeval_apply_of_mem_apply_eq_smul (hx : f x = μ • x) : aeval f p x = p.eval μ • x` is
  the variant of `aeval_apply_of_hasEigenvector` that does **not** require `x ≠ 0`; use it and skip
  the `rcases eq_or_ne x 0` on that step.
* `Module.End.finite_hasEigenvalue f : Set.Finite {μ | f.HasEigenvalue μ}` is in
  `Mathlib/LinearAlgebra/Eigenspace/Minpoly.lean`, and is all that is needed to feed
  `Lagrange.interpolate` a `Finset` of nodes. `Lagrange.eval_interpolate_at_node` takes the value
  function `r` as its *first, explicit* argument (a section variable), before `Set.InjOn`.
* `Module.End.Eigenvalues f` is `{μ // f.HasUnifEigenvalue μ 1}` and its coercion to `𝕜` is
  `Module.End.UnifEigenvalues.val`, **not** `Subtype.val`. So `rw [iSup_ne_bot_subtype]` does not
  match a `⨆ μ : Eigenvalues A, …`; `change` the goal to `⨆ μ : {μ // eigenspace A μ ≠ ⊥}, …`
  first (Mathlib's `orthogonalComplement_iSup_eigenspaces_eq_bot'` uses a term-level `show` for the
  same reason). The two are defeq, so `change` succeeds.
* `OrthogonalFamily.isInternal_iff` (`InnerProductSpace/Projection/FiniteDimensional`) turns
  "eigenspaces span" plus "eigenspaces orthogonal" into `DirectSum.IsInternal`, which is the form
  `LinearMap.IsSymmetric.direct_sum_isInternal` is stated in. Match it.

## The matrix bridge is three names

`Matrix.toLpLinAlgEquiv 2 : Matrix n n 𝕜 ≃ₐ[𝕜] Module.End 𝕜 (EuclideanSpace 𝕜 n)`
(`Mathlib/Analysis/Normed/Lp/Matrix.lean`) is *definitionally* `Matrix.toEuclideanLin`, so:

* `Commute.map … (Matrix.toLpLinAlgEquiv 2)` transports `IsStarNormal` from the matrix to the
  operator, once `star (toEuclideanLin A) = toEuclideanLin (star A)` is established by
  `LinearMap.star_eq_adjoint`, `Matrix.star_eq_conjTranspose` and
  `Matrix.toEuclideanLin_conjTranspose_eq_adjoint` (which lives in
  `Mathlib/Analysis/InnerProductSpace/Adjoint.lean`, not in the matrix files);
* `Polynomial.aeval_algHom_apply (Matrix.toLpLinAlgEquiv 2) A q` gives
  `aeval (toEuclideanLin A) q = toEuclideanLin (aeval A q)`. State it as a `have` with the
  `toEuclideanLin` spelling and let `exact` do the defeq — `rw` will not match
  `toLpLinAlgEquiv 2 A` against `toEuclideanLin A`.

`Matrix.toEuclideanCLM` (a `≃⋆ₐ`) is the other road; it was not needed, because the general theorem
is about `E →ₗ[𝕜] E` and `toLpLinAlgEquiv` lands there directly.

## Imports

**`IsAlgClosed ℂ` needs `Mathlib.Analysis.Complex.Polynomial.Basic`** — the instance is the
fundamental theorem of algebra and lives with it. A backbone theorem stated over `[IsAlgClosed 𝕜]`
compiles fine without it and then fails to *instantiate* at `ℂ` in the surface with
"failed to synthesize instance of type class `IsAlgClosed ℂ`". The import belongs in the file that
instantiates, not in the polymorphic one.

## Process

* Re-confirmed the heredoc trap of `notes/lean-lessons.md`, this time on a Markdown file: a Python
  patch script fed through a bash heredoc turned `𝒦` (U+1D4A6) into a surrogate pair, and the write
  died with `UnicodeEncodeError` *after* the temp file had been opened. The temp-file-and-
  `os.replace` discipline made it a non-event; the original was untouched. Write the script with the
  Write tool and spell non-BMP characters `\U0001d4a6`.
* The source textbooks are on disk under `D:\Users\bridgecat\Documents\Projects\numlib-books\`, with
  OCR'd Markdown for Saad's *Iterative Methods*. Read the printed proof before trusting an
  alignment document's paraphrase of it: Saad's §6.10 proof of Lemma 6.23 uses a maximal vector and
  the nonsingularity of `A`, and the paraphrase in `plans/saadsparse-ch6.md` reproduced that
  route. A shorter one needs neither — and reading the print is what showed that the book's
  nonsingularity hypothesis is used only by *its* argument, so the formal statement can drop it.
* Truncated `ℕ` subtraction in a transcribed hypothesis deserves a check at the boundary. Saad's
  Lemma 6.23 reads `ν(A) ≤ s − 1`; at `s = 0` that is `ν(A) ≤ 0`, which `A = I` satisfies while
  `A^H v ∈ 𝒦_0(A, v) = ⊥` fails, so the transcription is false and the theorem needs `0 < s`. The
  book never says `s ≥ 1` because an `s`-term recurrence obviously has it. Evaluate every `n - 1`,
  `m - 1` in a copied statement at `0` before proving it.
