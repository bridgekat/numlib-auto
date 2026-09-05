# Lessons from `Numlib/Eigen/KrylovEigen`

Written while formalizing Saad, *Numerical Methods for Large Eigenvalue Problems*, §6.6 (Lemma
6.1, Thm 6.3, Thm 6.4). Same rules as `notes/lean-lessons.md`: symptom, cause, fix.

## Reading the source

* `pdftotext -q numerical-methods-for-large-eigenvalue-problems-saad.pdf out.txt` works, as the
  earlier agents recorded. What is new: the extraction also **drops relation symbols**, not only
  Greek letters and subscripts. Lemma 6.1's hypothesis comes out as `if Piv1 = 0`; the statement
  is `P_i v₁ ≠ 0`, and the surrounding proof (it divides by `‖P_i v₁‖`) is the only way to tell.
  Reading a hypothesis off the extraction alone would have produced a theorem that is false.
* Thm 6.3's proof text says the second factor is "any polynomial of degree `k − i`". There is no
  `k` in the theorem; it is `m − i`, as the degree count `(i − 1) + (m − i) = m − 1` shows.
* Thm 6.4 is proved in the book **only for `i = 1`**. The general index is asserted with "can be
  shown", resting on the claim that the part of `𝒦_m` orthogonal to the first `i − 1` Ritz
  vectors is `{q(A) v₁ : deg q ≤ m − 1, q(θ_j) = 0 for j < i}`. Only the easy inclusion is
  needed, and it is short: for `deg q < m` the compression satisfies `q(A_m) v = q(A) v`
  (`compression.aeval_apply_of_forall_pow_mem`), and in the compression's own eigenbasis
  `repr (q(A_m) v) j = q(θ_j) · repr v j`. So the general index cost nothing extra, and neither
  Saad's `Q̃_i` nor any spectral projector of the Ritz values was needed.

## Hypotheses the book leaves implicit

Every one of these is needed to keep a constant finite, and none is stated in the print:

* Thm 6.3 divides by `λ_j − λ_i` for `j < i` and by `λ_{i+1} − λ_n`, and normalizes the Chebyshev
  polynomial at `λ_i` outside `[λ_n, λ_{i+1}]`. So it needs `λ_n < λ_{i+1} < λ_i` and
  `λ_i < λ_j` for every `j < i` — strictly, not just the sorting.
* Thm 6.4's `κ_i^{(m)}` divides by `θ_j^{(m)} − λ_i`, so it needs `λ_i < θ_j^{(m)}` for `j < i`.
  That is *not* implied by interlacing, which only gives `θ_j ≤ λ_j`.
* Thm 6.4 speaks of `θ_i^{(m)}` for `i` up to `m`, which presupposes `dim 𝒦_m = m`, that is
  `m ≤ grade`. It appears as `hm : finrank 𝕜 (Krylov.subspace A v m) = m`.

## Statement design

* **State the interval as data.** Both Chebyshev bounds were first written with `λ_{i+1}` and
  `λ_n` inlined and drowned in `Fin` arithmetic (`⟨i + 1, _⟩`, `⟨n - 1, _⟩`, `Nat` subtraction in
  the Chebyshev degree). Taking `lo hi : ℝ` with `∀ j > i, λ j ∈ Set.Icc lo hi` instead gives a
  *more general* theorem whose proof has no index arithmetic at all, and the book's form is then
  a fifteen-line corollary. The same trick handles the indices themselves: pass `iS` with
  `(i : ℕ) + 1 = iS` and `first`/`last` with `∀ j, first ≤ j` / `∀ j, j ≤ last`, rather than
  constructing them. The book's constant `λ₁ − λ_n` also turns out not to be the sharp one:
  `λ_i − λ_n` works, and is what the general form proves.
* **The Chebyshev degree wants its own variable.** `T ℝ (m - 1 - i)` elaborates the index in `ℤ`
  (the index of `Polynomial.Chebyshev.T` is an integer), so `m - 1 - i` is *integer* subtraction
  and `one_le_eval_T`, stated for a `ℕ` index, no longer applies. Writing the theorem with a
  fresh `k : ℕ` and the hypothesis `(i : ℕ) + k < m` removes the truncated subtraction, makes the
  degree count `deg (deflator * shifted) ≤ i + k < m` immediate, and generalizes the statement to
  every `m` past the minimum.
* Saad's normalized `y_i = (I − P_i)v₁ / ‖(I − P_i)v₁‖` with its explicit `y_i = 0` convention is
  not worth carrying: `‖p(A) y_i‖ · tan θ(u_i, v₁)` is `‖p(A) w‖ / ‖⟪u_i, v₁⟫‖` with
  `w = v₁ − ⟪u_i, v₁⟫ u_i`, the degenerate case included, because `‖0‖⁻¹ = 0` on one side matches
  `0 / c` on the other. Prove the ratio form and derive the book's in six lines.
* Lemma 6.1 needs **one eigenpair, not an eigenbasis**: for symmetric `A`, `A u = μ u` with `μ`
  real already makes `𝕜 ∙ u` and its complement invariant, which is the whole content. Stating it
  that way drops `[FiniteDimensional 𝕜 E]`, `hn : finrank 𝕜 E = n` and the basis from the
  signature. The eigenbasis is needed only from Thm 6.3 on, where the *other* eigenvalues are
  estimated.
* Using the rank-one projector onto `𝕜 ∙ u_i` rather than Saad's spectral projector onto the
  eigenspace of `λ_i` is a correction, not a weakening: with a multiple eigenvalue the components
  of `v₁` along the other eigenvectors for `λ_i` must count against the angle, since no Krylov
  subspace can separate them from `u_i`.

## Junk values, again

The angle API is all quotients, so the degenerate points have to be checked one at a time.

* `Submodule.tanAngle_span_singleton hu x : (𝕜 ∙ x).tanAngle u = ‖x - ⟪u,x⟫ • u‖ / ‖⟪u,x⟫‖` needs
  no hypothesis beyond `‖u‖ = 1`: at `⟪u, x⟫ = 0` both sides are `0`, and `x = 0` is that case.
* `tan_angle_eq_iInf` holds at `m = 0` with no hypothesis: `𝒦_0 = ⊥` gives the junk `0` on the
  left, and the index type `{p // p.degree < 0 ∧ p.eval μ = 1}` is empty, so `Real.iInf_of_isEmpty`
  gives `0` on the right. Two junk conventions agreeing again — worth checking before adding
  `0 < m`.
* The intermediate step of Saad's proof, "minimize `tan θ(x, u_i)` over `x ∈ 𝒦_m`", is **not**
  formalizable as an `⨅` over `x ∈ 𝒦_m`: any `x` orthogonal to `u_i` contributes the junk value
  `0` and collapses the infimum. The polynomial index set is what repairs it, because
  `p(λ_i) = 1` is exactly the constraint that keeps `⟪u_i, p(A) v⟫` away from `0`. The book's
  reparametrization `p = q / q(λ_i)` is doing this silently.

## Lean and Mathlib

* `rw` cannot rewrite a submodule under `tanAngle`, `sinAngle` or `starProjection`: the
  `HasOrthogonalProjection` instance argument depends on it and the motive fails. A congruence
  lemma proved by `subst h; rfl` (`Submodule.tanAngle_congr`) is the fix — `HasOrthogonalProjection`
  is a `Prop` class, so proof irrelevance makes the two instances defeq and `rfl` closes it. This
  bit three times: on `Krylov.subspace_zero`, on `Submodule.span_zero_singleton` and on
  `Submodule.span_singleton_smul_eq`.
* `iInf_of_isEmpty` is for complete lattices, so it does not apply to `ℝ`. The name for the
  conditionally complete case is `Real.iInf_of_isEmpty`, and it does pick up an `IsEmpty` instance
  introduced by a plain `have`.
* `le_or_lt` no longer exists in this toolchain; `le_or_gt` does.
* `div_le_div_of_nonneg_right (h : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c` wants `0 ≤ c`, not
  `0 < c`, and `div_le_div_of_nonneg_left (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) : a / b ≤ a / c`
  wants the strict one. Passing the wrong one is an application type mismatch, not a failed
  unification, so the error is at least readable.
* `field_simp` needs the `≠ 0` fact **in the context**, not merely derivable by `linarith`:
  `rw [eq_div_iff (by linarith : d ≠ 0)]; field_simp` left a goal `ring` could not close, while
  `have hne : d ≠ 0 := by linarith; field_simp; ring` closed it at once.
* `Fin.card_Iio : #(Finset.Iio b) = b` exists (`Fin` namespace) and is what turns the degree of a
  deflating product over `Finset.Iio i` into `(i : ℕ)`.
* `Polynomial.natDegree_lt_iff_degree_lt` needs `p ≠ 0`; the cheap source of that here is that the
  polynomial takes the value `1` somewhere.
* `compression.aeval_apply_of_forall_pow_mem` does not infer its `x : K` from the goal when the
  result is used inside `Subtype.ext`. Pass `(x := ⟨v, hvK⟩)` and the submodule explicitly.
* A section variable named `k` and a bound variable named `k` in a `∏ k ∈ …` inside the same proof
  silently shadow each other and produce an unprovable goal. Rename the bound one.
* `nlinarith [norm_nonneg _, mul_nonneg _ _]` is still the way from `a² ≤ b²` and `0 ≤ b` to
  `a ≤ b`, as `notes/lessons-ritz.md` records; `pow_left_inj₀ ha hb two_ne_zero` is the equality
  version and is what turns two Pythagoras identities into `‖u − P x u‖ = ‖x − ⟪u,x⟫u‖ / ‖x‖`.

## On the plan's estimate

`plans/backbone.md` §4.4 calls this "the direct analogue of `Krylov/Convergence/CG`", and that
is exactly right about the *shape*: a min–max, a polynomial norm bound, a variational
characterization. What it does not say is that the eigenvalue side needs one more ingredient that
the linear-solve side does not — a polynomial with prescribed roots, to remove the eigenvalues
(Thm 6.3) or the Ritz values (Thm 6.4) that the estimate cannot control. Factoring that out as
`Polynomial.deflator` and `Polynomial.exists_deflated_chebyshev`, stated over an arbitrary finite
index set, is what makes Thm 6.3 and Thm 6.4 twenty lines each instead of two hundred; it is the
same lesson as `notes/lessons-minmax.md` draws about `eigenvectorSpan`. The plan also expected
Thm 6.4 to rest on Courant–Fischer "on `𝒦_m`" in the `iSup`/`iInf` form; what it actually uses is
Rayleigh's recursive form (`isGreatest_rayleighQuotient_orthogonal`) applied to the compression,
because the competitor is a single vector orthogonal to the previous Ritz vectors rather than a
subspace of the right dimension.
