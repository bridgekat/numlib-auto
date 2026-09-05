# Lessons from `Analysis/InnerProductSpace/Projection/Angle`

Written while formalizing `Submodule.cosAngle`/`sinAngle`/`tanAngle`/`angle`/`gap`. Format as in
`notes/lean-lessons.md`: symptom, cause, fix. Fold in as the coordinator sees fit.

## Junk values are the whole design problem here

Every definition in this module is a quotient of norms, so `(0 : ℝ)⁻¹ = 0` gives each of them a
value where the denominator vanishes. The useful discovery is that *checking* the degenerate point
is cheap and changes the statement roughly half the time, in both directions:

* `cosAngle_mul_norm`, `sinAngle_mul_norm`, `sinAngle_of_mem`, `tanAngle_of_mem`,
  `cosAngle_le_of_le`, `sinAngle_le_of_le` and `sinAngle_eq_inv_norm_mul_infDist` are true at
  `u = 0` with *no* hypothesis: both sides evaluate to `0` there. Adding `u ≠ 0` out of caution
  would have made every consumer discharge a hypothesis it does not need.
* `tanAngle_mul_norm` genuinely needs `K.starProjection u ≠ 0`: at `P_K u = 0` the left side is `0`
  and the right side is `‖u‖`. Same for `tanAngle_le_of_le`, and there the hypothesis belongs to
  the *smaller* subspace, which is the counter-intuitive half.
* `sinAngle_bot`, `cosAngle_of_mem` and `sinAngle_eq_zero_iff` need `u ≠ 0` for the ordinary reason
  that `‖u‖ / ‖u‖` is `0` and not `1` at the origin.
* The nicest accident: **`tan_angle : Real.tan (K.angle u) = K.tanAngle u` needs only `u ≠ 0`.** At
  `P_K u = 0` the angle is `π / 2`, and Lean's `Real.tan (π / 2) = 0` is exactly the junk value
  `‖u‖ / 0 = 0` on the other side. Two junk conventions agreeing is worth checking for before
  assuming a hypothesis is needed.
* By contrast `sin_angle` needs `u ≠ 0` for a real reason: `K.angle 0 = π / 2` (from
  `Real.arccos 0`), so the left side is `1` while `K.sinAngle 0 = 0`.

Practical form of the rule: write the statement with no hypothesis, try the proof by
`rcases eq_or_ne u 0 with rfl | hu` and `simp` on the first branch, and only add a hypothesis when
that branch actually fails.

## Match the book's vocabulary before inventing names

`Submodule.gap` was nearly a coin flip. There are two "gaps" between subspaces in the literature:
the symmetric `‖P_K − P_L‖` and the one-sided `sup {dist(x, L) | x ∈ K, ‖x‖ = 1}`, which is
`‖(1 − P_L) P_K‖` and is generally strictly smaller. Saad, *Numerical Methods for Large Eigenvalue
Problems*, §3.1 defines `ω(K, L) = max {‖(1 − P_K) P_L‖, ‖(1 − P_L) P_K‖}` and states it equals
`‖P_K − P_L‖`, so the symmetric one is what the eigenvalue bounds mean. Reading the section before
writing the definition took ten minutes and would have cost three consumer modules a refactor.
The same section pins the angle: Saad's `∠(x, S) = min_{y ∈ S} ∠(x, y)` with `∠` *acute*, attained
at `y = P_S x` by his Theorem 3.1, and since `⟪x, P_S x⟫ = ‖P_S x‖ ^ 2` its cosine is
`‖P_S x‖ / ‖x‖`. `Submodule.angle_eq_angle_starProjection` records that against Mathlib's
`InnerProductGeometry.angle` over `ℝ`, which is the only cross-check available — Mathlib has no
angle over `RCLike`, and none between a vector and a subspace at all.

The books live at `D:\Users\bridgecat\Documents\Projects\numlib-books\`. The Saad eigenvalue PDF is
password-protected and the `Read` tool refuses it, but `pdftotext` (on `PATH` via TeXLive/mingw)
extracts the whole book to text in a second: `pdftotext -q book.pdf out.txt`, then `grep` it. The
OCR mangles display math (`max` becomes `min`, subscripts migrate to the following line), so read
the surrounding prose rather than trusting a formula's rendering.

## Mathlib names and API found or missing

* `Submodule.norm_sq_eq_add_norm_sq_starProjection x S : ‖x‖ ^ 2 = ‖S.starProjection x‖ ^ 2 +
  ‖Sᗮ.starProjection x‖ ^ 2` is Pythagoras, and `starProjection_orthogonal_val` (`K` implicit,
  `@[simp]`) converts its second summand to `u - K.starProjection u`. `rw [← starProjection_orthogonal_val
  (K := K) u]` in *that* direction is the workhorse: it turns the ad-hoc `u - P_K u` back into a
  projection so the whole `norm_starProjection_apply_le` API applies to it.
* `Submodule.starProjection_comp_starProjection_of_le (h : K ≤ L) : K.starProjection ∘L
  L.starProjection = K.starProjection` is what makes `‖P_K u‖ ≤ ‖P_L u‖` a two-liner. Use it as
  `simpa using DFunLike.congr_fun … u`; the raw `congr_fun` leaves a `∘L` application that `rw`
  will not match.
* `Submodule.norm_starProjection (hK : K ≠ ⊥) : ‖K.starProjection‖ = 1` exists (not just the
  `orthogonalProjectionOnto` version).
* `‖(P_K − P_L) x‖ ≤ ‖x‖` for two *orthogonal* projections is not in Mathlib and is four lines:
  `P_K x − P_L x = P_K (x − P_L x) − P_{Kᗮ}(P_L x)`, the two pieces are orthogonal (one in `K`, one
  in `Kᗮ`), each is bounded by the corresponding piece of the `L`-splitting of `x`, and Pythagoras
  over `L` finishes. This is the whole content of `gap_le_one`, and Saad's `ω = ‖P₁ − P₂‖` identity
  would need the adjoint API on top of it (`‖P_K(1 − P_L)‖ = ‖(1 − P_L)P_K‖`), so it was left out.
* `⟪u, P_K u⟫ = ‖P_K u‖ ^ 2` is not in Mathlib either; the route is
  `rw [← real_inner_self_eq_norm_sq, ← sub_eq_zero, ← inner_sub_left]` and then Mathlib's
  `Submodule.starProjection_inner_eq_zero`. Going forwards instead — splitting `u` as
  `P u + (u − P u)` and rewriting — loops, because the rewrite's right-hand side mentions `u`.
* `div_le_one_of_le₀ (h : a ≤ b) (hb : 0 ≤ b) : a / b ≤ 1` handles `b = 0` and so proves
  `cosAngle_le_one` and `sinAngle_le_one` with no case split.
* `div_div_div_cancel_right₀ (hc : c ≠ 0) (a b) : a / c / (b / c) = a / b` is the lemma that turns
  `sinAngle / cosAngle` into `tanAngle` in one rewrite, junk value at `b = 0` included.
* `Real.arccos_le_pi_div_two : arccos x ≤ π / 2 ↔ 0 ≤ x` and `Real.arccos_le_arccos` (antitone, no
  side conditions) are the two facts needed for the range and the monotonicity of `angle`.
* Confirming a lesson already in `lean-lessons.md`:
  `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` needs `(𝕜 := 𝕜)` supplied, and it is stated
  with `‖·‖ * ‖·‖`, not `^ 2`.
* Another confirmation: `field_simp` closed the last goal of `angle_eq_angle_starProjection` by
  itself, so the trailing `ring` errored with "No goals to be solved".

## Two traps specific to this file

* `simpa [sq] using h` after rewriting with an orthogonal splitting will `simp`-normalize
  `Kᗮ.starProjection y` (via the `@[simp]` `starProjection_orthogonal_val`) on *one* side of the
  goal only, leaving `‖a − b‖` against `‖b − a‖` and a mismatch that reads as a completely
  unrelated type error. Close such a goal with an explicit `rw [hsplit, pow_two, pow_two, pow_two,
  h, norm_neg]` instead of letting `simp` see inside.
* `[FiniteDimensional 𝕜 K]` alongside `[K.HasOrthogonalProjection]` on the same theorem is safe
  even though the former implies the latter: `HasOrthogonalProjection` is a `Prop` class, so proof
  irrelevance makes the two instance paths definitionally equal and `exact` unifies them. Stating
  `finrank_eq_of_gap_lt_one` with `[FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]` rather than
  `[FiniteDimensional 𝕜 E]` keeps it usable for Krylov subspaces of an infinite-dimensional space,
  which is where the subspace-iteration bounds live.
