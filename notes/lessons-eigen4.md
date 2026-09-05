# Lessons from `Eigen/{Deflation,PowerMethod,RayleighRitz,Perturbation}`

Written while proving the four later-phase groups under `Numlib/Eigen/`: Wielandt deflation (a new
module), inverse iteration, the three appended Rayleigh–Ritz nodes and five of the eight appended
perturbation nodes. Symptom, cause, fix; to be folded into `notes/lean-lessons.md`.

## The books, against the plan

* **Saad's Theorem 3.9 is false as printed at a multiple eigenvalue**, and the plan copied it. It
  bounds `sin ∠(x, 𝕜 ∙ u)` for *one* eigenvector `u` of `λ` by `‖r‖/δ` with
  `δ = dist(θ, σ(A) ∖ {λ})`. The proof's last step is "‖(A − θ)z‖ is at least the smallest
  eigenvalue of `A − θ` restricted to `u`'s orthogonal complement, which is precisely `δ`" — and
  that complement still meets the `λ`-eigenspace when `λ` is multiple, where `A − θ` is only
  `λ − θ`. `A = diag(1, 1, 5)`, `x = e₂`: residual `0`, `δ = 4`, angle `π/2`. State it for the
  **eigenspace**; the line version is the simple-eigenvalue corollary.
* Saad's Proposition 3.7(v) says `‖E‖ ≤ ε` and his own proof of (v) ⇒ (iv) uses `‖E‖ < ε`. With
  `≤` the equivalence is false (`A = 0`, `B = ε • 1` puts every `z` with `‖z‖ = ε` on the right and
  none on the left). The plan had already spotted this ("indeed `< ε`"); it is worth stating the
  strict form and saying why in the doc comment.
* Saad's Theorem 4.7 (the oblique residual bound) is **not** Theorem 4.3 with `P_K` replaced by an
  oblique `Q` throughout: his `A_m = Q_K^L A P_K` keeps the *orthogonal* projector on the right, so
  that `A_m` kills `Kᗮ` and the right-hand sides stay `‖(1 − P_K)u‖`. And the constant has to
  bound `Q (A − λ)`, not `Q A`, because `Q (1 − P_K) ≠ 0` for an oblique `Q` — the shift no longer
  drops out of the residual identity as it does in the orthogonal case.
* Saad's Theorem 4.5 at a general index needs no spectral projector at all. What its proof
  consumes is one nonzero vector of `K` orthogonal to the leading Ritz vectors, so the statement
  should take that competitor as data; the book's display is then the instance
  `y = P_K u_i − P_W u_i`, and his inequality `‖x_i − u_i‖² ≤ ‖(1 − P_K)u_i‖² + ‖Q̃_i u_i‖²` is in
  fact an **equality**, because `Q̃_i` annihilates `u_i − P_K u_i`.

## Proof routes that were shorter than the plan's

* **Wielandt's theorem needs no basis and no block matrix.** Deflation changes `A` by an operator
  with range in the line `𝕜 ∙ u`, so `A` and `A₁` induce the *same* map on `E ⧸ (𝕜 ∙ u)`, while the
  line is invariant for both. `LinearMap.det_eq_det_mul_det` (which exists, in
  `Mathlib/LinearAlgebra/Determinant.lean`, for `e.det = (e.restrict he).det * (W.mapQ W e he).det`)
  then factors `det (t − A)` and `det (t − A₁)` through one common quotient determinant, and
  `Polynomial.funext` — `𝕜` is a field of characteristic zero, hence infinite — turns the scalar
  identity into the polynomial one. There is no charpoly analogue of `det_eq_det_mul_det` in
  Mathlib, and none is needed.
* **Inverse iteration needs no spectral mapping theorem.** For `T = A − σ` a unit and `B = T⁻¹`,
  `B − ν = (−ν) · B · (A − μ)` when `ν = (μ − σ)⁻¹`, and `B` commutes with `A − μ`, so the identity
  survives `(·)^N` and carries *generalized* eigenvectors across at the same index. That is
  precisely the hypothesis `tendsto_smul_powerIterate` consumes, so the whole transfer is three
  short lemmas. `A.maxGenEigenspace σ = ⊥` (the shift is not an eigenvalue) is needed for the
  `μ = σ` branch of the supremum.
* **A hypothesis that is redundant should be dropped.** `⟪v, u⟫ = 1` already gives `u ≠ 0`, so
  Wielandt's theorem carries one hypothesis fewer than the plan proposed.

## Lean and Mathlib

* `LinearMap.restrict` wants `∀ x ∈ p, f x ∈ q`, while `LinearMap.det_eq_det_mul_det` is stated
  with `W ≤ W.comap e`. The two are definitionally equal but not syntactically, so a helper lemma
  about `(e.restrict h).det` must take the hypothesis as an argument of the `∀ x ∈ p` shape and be
  applied to whatever proof term the caller has.
* `LinearMap.det_eq_det_mul_det` takes `W` as an *explicit* first argument (a section variable
  declared before the instances), so it is `det_eq_det_mul_det _ _ hq`, not `_ hq`. The error is
  "did not find an occurrence of the pattern `LinearMap.det ?m`", which does not point at the
  arity.
* `Ring.inverse` lives in `namespace Ring` with the scoped postfix `⁻¹ʳ`; the cancellation lemmas
  are `Ring.mul_inverse_cancel x h` and `Ring.inverse_mul_cancel x h`, both taking `IsUnit x`
  explicitly. `Commute B T` from `B * T = 1 = T * B` is `(hBT.trans hTB.symm)` and typechecks
  directly, `Commute` being a def; `Commute B (c • 1)` is `(Commute.one_right B).smul_right c`.
* **`HasDerivAt.smul`, `HasDerivAt.add` and `HasFDerivAt.comp_hasDerivAt` are not imported by the
  inner-product files.** `HasDerivAt` itself elaborates (it comes in transitively), so the failure
  is a bare `Unknown constant HasDerivAt.add`, which reads like a rename. Add
  `Mathlib.Analysis.Calculus.Deriv.{Add,Mul,Comp}`.
* Dot notation on a `HasDerivAt` hypothesis resolves into `HasFDerivAtFilter`, since `HasDerivAt`
  unfolds to it: `hu.smul hf` reports "the environment does not contain
  `HasFDerivAtFilter.smul`". Write `HasDerivAt.smul hu hf`.
* After `HasDerivAt.add h1 h3` the function is displayed as `f + g` and no `rw`/`simp only [heig]`
  will rewrite inside it. `HasDerivAt.congr_of_eventuallyEq h (Filter.Eventually.of_forall …)` is
  the way to move a derivative along a pointwise equality of functions.
* `(hasDerivAt_id 0).smul h` gives `HasDerivAt (id • f)`, and `simpa` then cannot match
  `fun t => t • f t`. Bind `hid : HasDerivAt (fun t : 𝕜 => t) 1 0 := hasDerivAt_id 0` first, so the
  lambda beta-reduces to the wanted shape, and clean the derivative with
  `rw [zero_smul, one_smul, zero_add]` rather than `simpa`.
* `Submodule.sub_starProjection_mem_orthogonal` takes the submodule after the vector, so the
  explicit form `Submodule.sub_starProjection_mem_orthogonal W x` fails where
  `W.sub_starProjection_mem_orthogonal x` works. Prefer dot notation for the whole
  `starProjection` family.
* `Submodule.sinAngle_congr` (rewrite a subspace under `sinAngle`) did not exist; it is the twin of
  `Submodule.tanAngle_congr` and is proved the same way, `subst h; rfl`.
* `norm_inner_le_norm x y` has `𝕜` implicit; passing it explicitly gives "argument `w` has type `E`
  but is expected to have type `Type`".
* `inner_self_eq_norm_sq_to_K` produces `(↑‖u‖ : 𝕜) ^ 2`, so the norm of it needs `norm_pow` before
  `RCLike.norm_ofReal` — a repeat of the trap `lessons-ritz2.md` records for `RCLike.ofReal_pow`.
* `mul_div_mul_left` does not exist for a `GroupWithZero`; only the group version
  `mul_div_mul_left_eq_div`. For a scale-invariance proof over `ℝ` whose denominator may vanish,
  `rcases eq_or_ne … 0` and `field_simp` on the nonzero branch is shorter than hunting for a lemma.
* `field_simp` closed two goals outright here, after which the trailing `ring` errors with "No
  goals to be solved" — the third time this file's notes record that trap.
* `Matrix.spectrum_transpose` is a `simp` lemma, so the column-sum Gershgorin theorem is three
  lines from the row-sum one.
* `Polynomial.funext` needs `[Infinite R]`, which instance search finds for an `RCLike` field
  through `CharZero`; no `Infinite 𝕜` binder is needed.

## Placement issues found

* `LinearMap.IsSymmetric.mul_norm_sub_starProjection_le` and `…mul_norm_le_norm_sub_smul` live in
  `Numlib/Eigen/RayleighRitz.lean`, but they are pure `IsSymmetric`-plus-projection material and
  `Numlib/Eigen/Perturbation.lean` needs exactly them for Saad's Thm 3.9. Perturbation cannot see
  them without importing the Krylov layer, which would be the wrong direction, so the argument is
  redone there from the eigenbasis (about thirty lines). Both belong in `Numlib/Eigen/MinMax.lean`,
  which is below both.
* `Submodule.sinAngle_congr` (added here) belongs in
  `Numlib/Analysis/InnerProductSpace/Projection/Angle.lean` beside `Submodule.tanAngle_congr` —
  which itself sits in `Numlib/Eigen/KrylovEigen.lean` for the same reason.
