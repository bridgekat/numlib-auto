# Lessons from the Hermitian half of `Numlib/Eigen/RayleighRitz.lean`

Written while proving the three remaining nodes of `Numlib/Eigen/RayleighRitz` — the Ritz-value
range, the Ritz-value error and the Ritz-vector error — plus Cauchy interlacing and the API they
needed. Same rules as `notes/lean-lessons.md`: symptom, cause, fix.

## The book, against the plan

* The plan's `source` lines for these three nodes were right this time: Saad, *Numerical Methods
  for Large Eigenvalue Problems*, §4.3.2 (Prop 4.4, Cor 4.1, Thm 4.4 for the first; Lemma 4.1 and
  Thm 4.5 for the second; Thm 4.6 and Prop 4.5 for the third). Nothing in `backbone.md` §4.2
  disagreed with the printed text either. Read them anyway — the four things the paraphrases lost
  are below.
* **Saad's Thm 4.6 constant `δ` is not a gap between Ritz values.** It is "the distance between
  `λ` and the set of approximate eigenvalues other than `θ̃`" — the exact eigenvalue against the
  *other Ritz* values, not `θ̃` against them, and not `λ` against the other exact eigenvalues.
  Getting that wrong makes the bound false. What the proof uses is only
  `‖(A_K − λ) z‖ ≥ δ ‖z‖` for `z ∈ K` orthogonal to the `θ̃`-eigenspace of the compression, which
  is what the formal statement takes as a hypothesis;
  `LinearMap.IsSymmetric.mul_norm_le_norm_sub_smul` derives that from the separation, in an
  eigenvector basis, and is the lemma that pins the meaning of `δ` down.
* **Thm 4.6 needs a degenerate branch the book does not mention.** Saad picks `ũ` as a unit vector
  in the `θ̃`-eigenspace at angle `ψ` to `v = P_K u / ‖P_K u‖`; if the projection of `P_K u` onto
  that eigenspace is `0` there is no such `ũ`. The bound is then vacuous — `Q v = 0` forces
  `δ cos θ ≤ γ sin θ`, hence `(1 + γ²/δ²) sin²θ ≥ 1` — so any Ritz vector for `θ̃` serves, but the
  statement has to be an existence and has to assume that `θ` *is* a Ritz value
  (`Module.End.HasEigenvalue (compression A K) θ`). Two lines of case split, easy to miss.
* **Thm 4.6's proof is much shorter unnormalized.** Saad works with unit `v`, `w`, `ũ` and the
  angles `θ`, `ψ`, `γ` (his Fig. 4.1), and ends with the trigonometric identity
  `sin²∠(u, ũ) = sin²θ + sin²ψ cos²θ`. Taking `ũ := P_W (P_K u)` *unnormalized* replaces all of it:
  `P_{𝕜 ∙ ũ} u = ũ` outright (because `⟪ũ, u⟫ = ⟪ũ, P_K u⟫ = ⟪ũ, ũ⟫`), so
  `‖u − ũ‖² = ‖u − P_K u‖² + ‖P_K u − ũ‖²` is one application of Pythagoras and the identity above
  never has to be stated. Do not formalize the figure.
* Prop 4.5's proof as printed reads `θ̃ − λ = ((A − λI)(ũ − u), ũ)`, which is only correct with the
  `σ = (u, ũ)` that the OCR drops: the vector is `ũ − ⟪u, ũ⟫ u`, i.e. `ũ − P_{𝕜 ∙ u} ũ`, whose norm
  is `sin ∠(u, ũ) ‖ũ‖`. With `ũ − u` (both unit) the norm would be `2 sin(∠/2)` and the stated
  bound would be off by a factor of four.
* Saad's Thm 4.5 is stated for every index, with the previous approximate eigenvectors projected
  out by `Q̃_i`. Only `i = 1` is formalized (`Q̃_1 = 0`); the general case needs an
  "orthogonalize against the leading Ritz vectors" construction that nothing downstream asks for
  yet.

## Statement design

* **The Courant–Fischer statement to build on is the `IsGreatest` one, and it wants to be restated
  on `E`.** `LinearMap.IsSymmetric.isGreatest_eigenvalues` applied to `compression A K` quantifies
  over `Submodule 𝕜 ↥K` and uses the Rayleigh quotient of the compression, which is not what a
  consumer can check. `isGreatest_eigenvalues_compression` restates it over
  `{S : Submodule 𝕜 E // S ≤ K}` and the Rayleigh quotient of `A` — that *is* Saad's Prop 4.4 —
  and then Cauchy interlacing is two lines, because the two `IsGreatest` sets are literally nested.
  The translation is `Submodule.map K.subtype` one way, `Submodule.comap K.subtype` the other, with
  `Submodule.finrank_map_subtype_eq` and `(Submodule.comapSubtypeEquivOfLe h).finrank_eq` for the
  dimensions.
* `Krylov.rayleighQuotient_compression` (`(compression A K).rayleighQuotient y =
  A.rayleighQuotient (y : E)`) is the whole content of interlacing and is one `rfl` after
  `compression.inner_apply`. Prove it first; every later comparison of the two spectra goes
  through it.
* The house form for `‖A − λ‖` is the quadratic-form bound
  `∀ x, |re ⟪A x, x⟫ − λ ‖x‖²| ≤ C ‖x‖²`, matching `MinMax`'s
  `eigenvalues_le_add_of_re_inner_le` and the `γ` convention of this module.
  `Krylov.abs_re_inner_sub_le_opNorm` is the operator-norm reading. Restricting the hypothesis to
  `x ∈ Kᗮ` (which is all Lemma 4.1 uses) was tempting but would have made the three theorems carry
  three differently scoped constants; Prop 4.5 needs it at a vector that is *not* in `Kᗮ`.
* A Ritz value is real and equals its Rayleigh quotient with **no symmetry hypothesis**:
  `⟪u, A u⟫ = θ ‖u‖²` is just the Galerkin condition tested against `u`. Symmetry enters only for
  `conj θ = θ`. Splitting `IsRitzPair.rayleighQuotient_eq` from `IsRitzPair.conj_eq` keeps the
  first usable over a nonsymmetric `A`.
* `‖u − v‖² = ‖u − P_K u‖² + ‖P_K u − v‖²` for `v ∈ K` is not in Mathlib and not in
  `Numlib/Approximation/BestApprox`; it is four lines and it is what every "the angle to the Ritz
  vector splits" argument needs. It is here as `Submodule.norm_sub_sq_eq_add_of_mem`.

## Placement to fix later

* `Submodule.norm_sub_sq_eq_add_of_mem`, `Submodule.starProjection_span_singleton_eq_self`,
  `Submodule.cosAngle_span_singleton` and `Submodule.sinAngle_span_singleton_comm` are declared in
  `Numlib/Eigen/RayleighRitz.lean` and belong in
  `Numlib/Analysis/InnerProductSpace/Projection/Angle.lean`. They were put here to avoid editing a
  finished module (and its group's plan) while another agent was building on it. If `Angle` is ever
  revised, move them and their four nodes.
* **`Submodule.inner_starProjection_right` already exists**, in
  `Numlib/LinearSolve/Projection/Basic.lean`, with exactly the statement
  `⟪w, P_K u⟫ = ⟪w, u⟫` for `w ∈ K`. It is not reachable from `Numlib/Eigen`, and importing
  `Numlib/LinearSolve` from `Numlib/Eigen` would be the wrong dependency direction, so the fact is
  inlined here in three lines. It is a candidate for relocation into the `Analysis` layer, where
  both consumers could see it. Grep before adding a `Submodule.*` lemma: this project already has a
  fair number of them scattered across layers.

## Lean and Mathlib

* `Submodule.norm_coe (x : ↥K) : ‖(x : E)‖ = ‖x‖` and
  `Submodule.coe_inner K x y : ⟪x, y⟫ = ⟪(x : E), (y : E)⟫` are the two bridges for working inside
  a subspace. The coercion of a *compound* term is the trap: `Krylov.compression_residual_le`
  states its left-hand side as `(… - μ • … : E)`, which elaborates to
  `↑(A_K y) - μ • ↑y`, not to `↑(A_K y - μ • y)`, so `rw [Submodule.norm_coe]` finds nothing.
  Insert `have hcast : ↑a - c • ↑b = ↑(a - c • b) := rfl` first — it *is* `rfl`, the coercion is
  just not syntactically factored.
* `set x := e with h` inside a long proof is safe when the later steps are `have`s with explicit
  statements plus `exact`/`nlinarith`: `set` makes `x` a local definition, so
  `W.starProjection_apply_mem y : W.starProjection y ∈ W` still `exact`s against a goal displaying
  `p ∈ W`. What it does not survive is `rw` with a lemma whose left-hand side mentions the
  abbreviated term, so get every `rw`-heavy fact (here `compression_residual_le` and
  `mul_norm_sub_starProjection_le`) into context *before* the `set`s.
* From `a ^ 2 ≤ b ^ 2` and `0 ≤ b` to `a ≤ b`: `Real.sqrt_le_sqrt` then
  `rwa [Real.sqrt_sq ha, Real.sqrt_sq hb]` is more reliable than `nlinarith`, which fails on the
  variant `1 ≤ t` from `1 ≤ t ^ 2`, `0 ≤ t` (it needs the product `(1 − t)(1 + t)` and does not
  find it). `Real.sqrt_one` handles the `1` on the left.
* `pow_left_inj₀ ha hb two_ne_zero |>.1 : a ^ 2 = b ^ 2 → a = b` for nonnegative reals is the way
  to conclude `sinAngle` equalities from `cosAngle` equalities via
  `Submodule.cosAngle_sq_add_sinAngle_sq`.
* `inner_conj_symm x y : conj ⟪y, x⟫ = ⟪x, y⟫` — the arguments are in the *opposite* order to the
  inner product you are rewriting. `rw [← inner_conj_symm (A u) u]` turns `⟪A u, u⟫` into
  `conj ⟪u, A u⟫`; writing `inner_conj_symm u (A u)` silently aims at the wrong term and the
  rewrite fails with "did not find an occurrence".
* `RCLike.ofReal_pow` orients as `↑(r ^ n) = (↑r) ^ n`, and `inner_self_eq_norm_sq_to_K` produces
  the *right*-hand form, so getting to a coercion you can hit with `RCLike.re_ofReal_mul` needs
  `← RCLike.ofReal_pow`. This cost two rounds.
* `Submodule.mem_span_singleton` produces `∃ a, a • v = x`, not `∃ a, x = a • v`.
* `Real.sq_sqrt`, not `Real.sqrt_sq`, is the one that needs `0 ≤ x` for `(√x) ^ 2 = x`.
* `field_simp` closed `cosAngle_span_singleton` by itself, so a trailing `ring` errors with "No
  goals to be solved" — the same trap `lessons-angle.md` already records.
* `Fin.castLE h 0 = 0` is not `rfl`; `by ext; simp` does it.
* `Module.End.HasEigenvalue.exists_hasEigenvector` is the way out of `eigenspace ≠ ⊥`, and
  `Krylov.isRitzPair_of_hasEigenvector` takes that eigenvector straight to a Ritz pair.

## On the plan's estimate

The three nodes were budgeted as the hard remainder of the module, and Thm 4.6 was the only one
that deserved it. Cauchy interlacing is six lines once `rayleighQuotient_compression` exists, the
Ritz-value range is two, and Lemma 4.1 is fifteen. Thm 4.6 is about eighty, of which two thirds is
the `W`-splitting lemma (`mul_norm_sub_starProjection_le`) and the eigenbasis argument that gives
`δ` its meaning (`mul_norm_le_norm_sub_smul`) — both of which are reusable and neither of which the
plan mentions.
