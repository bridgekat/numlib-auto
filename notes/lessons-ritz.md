# Lessons from `Numlib/Eigen/RayleighRitz.lean`

Written while formalizing the seven non-Courant–Fischer nodes of `Numlib/Eigen/RayleighRitz`.
Same rules as `notes/lean-lessons.md`: symptom, cause, fix. The coordinator folds these in.

## Sources: check the book before trusting the plan's attribution

* The plan attributed `charpoly_compression_isMinOn` and `norm_ritz_residual_eq` to Saad,
  *Iterative Methods for Sparse Linear Systems*, Theorem 6.1 and Proposition 6.8. **Both are
  wrong.** That book has no Theorem 6.1 at all (its Chapter 6 theorem numbering starts at 6.11),
  and its Proposition 6.8 is about IOM and DIOM. The two results are Saad, *Numerical Methods for
  Large Eigenvalue Problems*, §6.1 Theorem 6.1 and §6.2 Proposition 6.8. The two books have
  overlapping section numbers and incompatible result numbers — Saad-eig's Prop 6.2 is
  Saad-iterative's Prop 6.1 — so a bare number is worthless without the title, which is exactly
  why the backbone forbids one.
* `plans/backbone.md` §4.2 had it right: everything it lists after "Serves Saad-eig §4.3" is
  Saad-eig, including the "§6.1–6.2" items. It was the `source` fields of the TOML that had drifted.
* The books are on disk at `D:\Users\bridgecat\Documents\Projects\numlib-books\`. Three have an
  OCR'd Markdown twin in a subdirectory; the rest are PDF. `numerical-methods-for-large-eigenvalue-problems-saad.pdf`
  is owner-password protected, so the Read tool refuses it — `pdftotext` (present in the Git Bash
  `/mingw64/bin`) extracts it without complaint. The extraction loses every Greek letter and every
  superscript, so `‖(Am - I)PK u 2   (I - PK )u 2` has to be read as
  `‖(A_m − λI) P_K u‖₂ ≤ γ ‖(I − P_K) u‖₂`; the surrounding proof text is what disambiguates.

## What the plan said and what is true

* Saad-eig Theorem 4.3's second constant really is `√(|λ|² + γ²)`, as §4.2 of `backbone.md` says.
  What the plan adds and the book does not need is the normalization `‖u‖ = 1`: both inequalities
  are homogeneous of degree one in `u` and hold for every eigenvector. Saad assumes `‖u‖ = 1` only
  because he is interpreting `‖(I − P_K)u‖` as a sine.
* Theorem 6.1 has no *stated* grade hypothesis, but it needs `m ≤ grade`: it speaks of the
  characteristic polynomial of `V_mᴴ A V_m` for an orthonormal basis `V_m` of `𝒦_m` with `m`
  columns, and by his own Prop 6.3 that basis exists iff `dim 𝒦_m = m`. The formal proof needs the
  same thing for the same reason (`charpoly.natDegree = finrank K` must be `m`). Non-strict `≤` is
  enough — at `m = grade` the minimum is `0` — so this is one of the places where the usual
  "`m < grade` at the boundary" warning does *not* apply.
* Prop 6.8 needs no hypothesis whatever, not even `m ≤ grade`: past breakdown `v_{m+1} = 0` forces
  `h_{m+1,m} = ⟪v_{m+1}, A v_m⟫ = 0`, and both sides of `‖(A − θ)ũ‖ = h_{m+1,m}|y_m|` are `0`.
  Stating it that way costs two lines (`rcases eq_or_ne (vec A b (m+1)) 0`) and removes the
  `[FiniteDimensional 𝕜 (fullSubspace A b)]` binder from the headline result of the file.
* `Prop 6.6` of Saad-eig is `(1 − P_m) A P_m = h_{m+1,m} v_{m+1} v_mᴴ`, so `‖(1 − P_m) A P_m‖ =
  h_{m+1,m}`. Theorem 4.3's constant is the *other* one, `γ = ‖P_m A (1 − P_m)‖`. They agree only
  because the intended application (§6.6.3) is Hermitian, where each is the adjoint of the other.
  Anyone writing the nonsymmetric Arnoldi bounds should not assume `γ = h_{m+1,m}`.

## Design: an operator norm as a hypothesis

`γ = ‖P_K A (1 − P_K)‖` is genuinely an operator norm, but making it one in the statement forces
`A : E →L[𝕜] E` on every consumer, and the whole Krylov layer is stated for `A : E →ₗ[𝕜] E`. The
form that costs nothing is a plain bound hypothesis

    hγ : ∀ x ∈ Kᗮ, ‖K.starProjection (A x)‖ ≤ γ * ‖x‖

— which is exactly how Saad *uses* `γ` in the proof of Theorem 4.3 (he applies it to the vector
`(I − P_K)u`), and which the Arnoldi case can discharge from one Hessenberg entry with no operator
norm in sight. The operator-norm reading is then one lemma,
`Krylov.norm_starProjection_apply_le_opNorm`, for `A : E →L[𝕜] E`. This is the same choice
`Numlib/Variational` makes with `SesqForm.IsBoundedWith`, and the opposite of
`Krylov/Convergence/CG.lean`, which does take `A : E →L[𝕜] E` because `‖A‖` appears in the
*conclusion* there rather than as a supplied constant.

## Lean and Mathlib

* **A specification that wants dot notation must be a `structure`, not a `def` returning `∧`.** The
  plan sketched `IsRitzPair … : Prop := u ∈ K ∧ u ≠ 0 ∧ …`, but then `h.hasEigenvector_of_invt`
  looks up `And.hasEigenvector_of_invt` (see the dot-notation entry in `lean-lessons.md`), and the
  planned node name `Krylov.IsRitzPair.hasEigenvector_of_invt` would be unusable in the notation it
  was named for. `IsPetrovGalerkin` in `LinearSolve/Projection/Basic.lean` is a structure for the
  same reason. For the same reason `IsRitzPair` is *not* an `abbrev` for `IsObliqueRitzPair A K K`:
  two three-field structures plus two one-line bridges keep dot notation working on both.
* `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` is stated with `‖x + y‖ * ‖x + y‖`, not
  `‖x + y‖ ^ 2`, despite the name. `simp only [pow_two]` before using it, then `ring`.
* `ContinuousLinearMap.one_apply_eq_self` does not exist; the live name is the root-level
  `one_apply_eq_self`, and `ContinuousLinearMap.sub_apply` is deprecated in favour of root
  `sub_apply`. `ContinuousLinearMap.coe_comp'` is deprecated too — `ContinuousLinearMap.comp_apply`
  is the rewrite that works on `(f ∘L g) x`.
* `rw [subspace_zero]` inside a goal mentioning `compression A (subspace A b m)` fails with "motive
  is not type correct": the `Module.Finite` instance argument of `LinearMap.charpoly` depends on the
  submodule being rewritten. Prove the degenerate case through `Submodule.mem_orthogonal` and
  rewrite in the *hypothesis* `w ∈ 𝒦_0` instead, where no instance rides along.
* `rw [Fin.sum_univ_castSucc] at h` splits the *first* `Fin (n+1)`-indexed sum it finds, which in
  the Arnoldi relation `A (∑ j : Fin (m+1), …) = ∑ i : Fin (m+2), …` is the one on the left. Pin it
  with `Fin.sum_univ_castSucc (n := m + 1)`.
* Indexing the last Arnoldi coefficient: state the theorem at `m + 1` and use `Fin.last m`, never
  at `m` with `⟨m - 1, _⟩` — `Fin.val_lt_last : i ≠ Fin.last n → (i : ℕ) < n` then does the
  Hessenberg-vanishing side condition in one step, and no `Nat` subtraction ever appears. But
  `Fin.val_last` is *not* applied by `rw` automatically: a goal showing `coeff A b ↑(Fin.last (m+1)) j`
  will not match a `coeff_eq_zero_of_lt` instantiated at `m + 1`, even though the two are defeq.
* `compressionBy.apply_aeval_of_forall_pow_lt_mem` (one degree less, after projecting) is the half of
  Saad's Prop 6.4 that the characteristic-polynomial argument needs; `aeval_apply_of_forall_pow_mem`
  is useless there, because it wants `A^m b ∈ 𝒦_m`, which holds only *past* the grade.
* `LinearMap.charpoly_natDegree` needs `[StrongRankCondition R]` (free over a field) and gives
  `natDegree = finrank`; with `Krylov.finrank_subspace` and `min_eq_left` that is the whole degree
  bookkeeping. `Module.Free 𝕜 ↥(subspace A b m)` is found by instance search over a field.
* From `a² ≤ c²` and `0 ≤ c` to `a ≤ c`: plain `nlinarith` does it, and no hypothesis `0 ≤ a` is
  needed. Worth a two-line private lemma rather than hunting for the current spelling of
  `pow_le_pow_iff_left`.
* `Submodule.inner_left_of_mem_orthogonal hK hKperp : ⟪v, u⟫ = 0` and `inner_right_of_mem_orthogonal
  hK hKperp : ⟪u, v⟫ = 0`, both taking `u ∈ K` first and `v ∈ Kᗮ` second. Picking the wrong one
  costs a `inner_conj_symm` round trip.

## Tracker

* `lake exe tracker lint` reports `desc is superseded by the module's doc comment; remove it` as
  soon as the module exists, even when the group still has open nodes. There is no way to keep a
  group `desc` alongside a written module and still get `ok`.
* The plan's namespaces are not always the library's. The nodes were planned as
  `Krylov.Arnoldi.charpoly_compression_isMinOn`, but `Numlib/Krylov/Arnoldi.lean` puts everything in
  a top-level `Arnoldi` namespace (`open Krylov; namespace Arnoldi`), which is what §1.4 of
  `backbone.md` prescribes. New Arnoldi declarations go in `Arnoldi`, and the node ids follow the
  code.
