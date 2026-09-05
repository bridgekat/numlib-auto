import Numlib.Surface.SaadSparse.Chapter01.Section11
import Numlib.Surface.SaadSparse.Chapter01.Section12
import Numlib.Surface.SaadSparse.Chapter01.Section13
import Numlib.Surface.SaadSparse.Chapter04.Section01
import Numlib.Surface.SaadSparse.Chapter04.Section02
import Numlib.Surface.SaadSparse.Chapter05.Section01
import Numlib.Surface.SaadSparse.Chapter05.Section03
import Numlib.Surface.SaadSparse.Chapter05.Section04
import Numlib.Surface.SaadSparse.Chapter06.Section02
import Numlib.Surface.SaadSparse.Chapter06.Section03
import Numlib.Surface.SaadSparse.Chapter06.Section04
import Numlib.Surface.SaadSparse.Chapter06.Section05
import Numlib.Surface.SaadSparse.Chapter06.Section06
import Numlib.Surface.SaadSparse.Chapter06.Section07
import Numlib.Surface.SaadSparse.Chapter06.Section08
import Numlib.Surface.SaadSparse.Chapter06.Section09
import Numlib.Surface.SaadSparse.Chapter06.Section10
import Numlib.Surface.SaadSparse.Chapter06.Section11

/-!
# Saad, *Iterative Methods for Sparse Linear Systems*

The surface library for Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition
(SIAM, 2003): one module per section of the book, covering §1.11–§1.13, §4.1–§4.2, Chapter 5 and
Chapter 6. Each module states the book's results in the book's own terms — Saad's non-symmetric
"positive definite", the splitting `A = D - E - F`, the algorithms of Chapter 6 written out as Lean
functions — and proves them by specializing the general backbone under `Numlib/`. Almost nothing is
proved here that is not proved there: the surface exists to test the backbone against a published
account of the subject, and to give a reader of the book a Lean name for every result in it. This
module imports the section modules and adds nothing of its own.

Plan and per-result book alignment: `tracker/saadsparse-ch1-4-5.md`, `tracker/saadsparse-ch6.md`.

## Naming

A declaration is named for the result it states, so the name is the index: `theorem_6_29` is
Theorem 6.29, `proposition_6_13` is Proposition 6.13, `equation_6_43` is (6.43), `algorithm_6_9` is
Algorithm 6.9 and `problem_6_25` is the book's exercise P-6.25. Where one numbered result needs
several declarations — its separate clauses, or the two directions of an equivalence — a trailing
word tells them apart, as in `problem_6_25_le`. Objects the book names but does not number keep a
descriptive name (`arnoldiCGS`, `gmresFixed`, `smoothEta`), and each such definition carries an
equivalence lemma to its backbone counterpart; those lemmas are the load-bearing part of the
library.

Declarations live in `SaadSparse.ChNN` for the chapter, except in §1.11–§1.13, where results about
a matrix are stated in `Matrix` so that dot notation reads as the book does. `SaadSparse.Common`
holds the conventions shared by the whole library, and `SaadSparse.Chapter06.Common` the `r₀`, `β`,
`v₁`, `e₁`, `mEff` vocabulary shared by every Krylov method of Chapter 6.

## The outline

| § | module | subject |
|---|---|---|
| | `Common` | conventions: the matrix–operator glue, `⬝`, `lambdaMin`/`lambdaMax`, `complexify` |
| 1.11 | `Chapter01.Section11` | Positive-definite matrices; Theorems 1.34 and 1.35 (Bendixson) |
| 1.12 | `Chapter01.Section12` | Projectors; Lemma 1.36, Prop. 1.37, Theorem 1.38, Cor. 1.39 |
| 1.13 | `Chapter01.Section13` | Linear systems: existence, matrix `p`-norms, conditioning, (1.76) |
| 4.1 | `Chapter04.Section01` | Jacobi, Gauss–Seidel, SOR, SSOR as splittings; the preconditioners |
| 4.2 | `Chapter04.Section02` | Convergence: Theorem 4.1, Corollary 4.2, Gershgorin, Prop. 4.12 |
| 5.1–5.2 | `Chapter05.Section01` | Projection methods; Propositions 5.1–5.6, Theorem 5.7 |
| 5.3 | `Chapter05.Section03` | One-dimensional processes; Kantorovich, Theorems 5.9 and 5.10 |
| 5.4 | `Chapter05.Section04` | Additive and multiplicative projection processes |
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

There is no `Chapter06.Section01`: §6.1 is the chapter's introduction, and its one substantive
paragraph is stated with §6.2. `Chapter05.Section01` likewise covers §5.1 together with §5.2, which
share the book's own numbering (5.1)–(5.11).

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

Deferred to a later phase of the backbone, with the plans in `tracker/saadsparse-ch1-4-5.md` §3 and
`tracker/saadsparse-ch6.md` §4:

* §4.2.1, the convergence factors and rates, which need `‖complexify A‖ = ‖A‖` for the scoped
  operator norms before Gelfand's formula transports to a real matrix; Theorem 4.4 on regular
  splittings and M-matrices; Theorem 4.7 and the *irreducibly* diagonally dominant halves of
  Corollary 4.8 and Theorem 4.9; and the SOR theory of §4.2.4–§4.2.5 — Theorem 4.10, Definitions
  4.11 and 4.13, Propositions 4.14–4.15, Theorem 4.16 and the optimal parameter (4.47).
* Block relaxation (§4.1.1, Algorithms 4.1–4.2) and the identification of the additive procedure of
  §5.4 with the abstract additive projection process.
* §6.5.6: (6.56)–(6.58) and Theorem 6.11, which need the IOM iterate and a Gram–Schmidt
  factorization of the incomplete-orthogonalization basis.
* §6.6.2: that the characteristic polynomial of `T_m` minimizes `‖·‖_{v₁}` among monic polynomials
  of degree `m`, and that the Lanczos process computes `p_{T_m}(A) v₁` — Ritz values and orthogonal
  polynomials.
* §6.10: Lemma 6.23 and Theorem 6.24 (Faber–Manteuffel), which wait on the backbone's normal-matrix
  theory. The book itself states Theorem 6.24 without proof.
* §6.11.2 and §6.11.4: Lemma 6.26 (Zarantonello), Theorem 6.27 and Corollary 6.33, which need
  complex Chebyshev polynomials on ellipses.
* §6.12, block Krylov methods, has no module yet.

Left out deliberately: figures, numerical examples and tables, operation counts, implementation
advice, and the exercises the text does not cite. §1.13's differentiability statement (1.74)–(1.75)
is Mathlib calculus rather than a specialization of the backbone, and the plan lists it as a
backbone candidate.

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

## References

* Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003.
-/
