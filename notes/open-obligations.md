# Open proof obligations

The nine `sorry` placeholders left in `Numlib/`, with the obstruction for each. Every one is marked
with an explanatory comment at the declaration itself. Remove an entry here when its proof lands.

## `Numlib/Krylov/Hessenberg.lean` (5, all in `section GivensArnoldi`)

`IsMinResIterate.norm_residual_eq_norm_gamma`, `IsMinResIterate.exists_mulVec_rotated_eq`,
`IsMinResIterate.norm_residual_succ_eq`, `isUnit_hessenbergSq_iff_givensC_ne_zero`,
`IsGalerkinIterate.norm_residual_eq_div_norm_givensC`.

These share one root cause: **Mathlib has no lemma that a unitary matrix preserves the Euclidean
norm**, `‖U.mulVec v‖₂ = ‖v‖₂`. It has `Matrix.unitaryGroup` but no `mulVec` isometry. The natural
route is through `Matrix.toEuclideanCLM` and the fact that a unitary element of a C-star algebra is
an isometry. This is itself a good upstreaming candidate for `Numlib/Analysis/Matrix/`.

Two further ingredients are needed on top of it: the residual splitting
`‖Q(βe₁) − R̄y‖² = ‖g − Ry‖² + ‖γ_m‖²` from `rotated_last_row`, and solvability of `R_m y = g_m`,
i.e. `det R_m = ∏ ρ_k ≠ 0` via the upper-triangular determinant.
`isUnit_hessenbergSq_iff_givensC_ne_zero` additionally needs a block decomposition of the rotation
product, since `givensQ_mul_hessenbergOf` only gives the rectangular identity.

`IsGalerkinIterate.norm_residual_eq_div_norm_givensC` is also suspect at `c_m = 0`, where the
method breaks down and Lean's division by zero makes the right-hand side vanish while the residual
need not. A hypothesis `c_m ≠ 0`, equivalently that the Hessenberg block is a unit, is very likely
the right minimal correction, but no counterexample was constructed.

## `Numlib/Analysis/InnerProductSpace/Projection/ObliqueProjection.lean` (1)

`ContinuousLinearMap.IsIdempotentElem.norm_one_sub_eq`, Kato's `‖1 − P‖ = ‖P‖`.

Every route goes through the minimal-gap characterisation `1/‖P‖² = 1 − ‖P_N P_M‖²` with
`M = range P` and `N = ker P`, plus the symmetry `‖P_M P_N‖ = ‖P_N P_M‖`. Mathlib has none of the
three ingredients, so this is 150 to 250 lines of supremum and infimum bookkeeping.

Dead ends already tried, recorded at the `sorry`: setting `T := P + P⋆ − 1` gives
`T² = P P⋆ + Q⋆Q = P⋆P + Q Q⋆`, where in each decomposition the two positive summands annihilate
each other, hence `‖T‖² = max(‖P‖², ‖Q‖²)` and `‖P‖, ‖Q‖ ≤ ‖T‖`, but not equality. The direct
estimate `‖Qx‖ ≤ ‖P‖‖x‖` reduces to a circular identity. The statement itself was checked true on a
two-by-two example.

## `Numlib/Nonlinear/Newton.lean` (2)

`Newton.norm_step_sub_le`: the obstruction is the *sharp* constant `L/2`.
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` accepts only a constant bound on
`‖F' z − φ‖`, which yields `L`, and `2L` once both points must lie in one ball. The sharp constant
needs the integral form, i.e. `image_norm_le_of_norm_deriv_right_le_deriv_boundary` applied to
`t ↦ F(x + t v) − F x − t F' x v` with boundary `B t = L‖v‖²(t − t²/2)`. That requires three further
instance arguments on a public statement, which was judged not worth it without a consumer.

`Newton.kantorovich`: needs the majorant method, i.e. the scalar Newton sequence for
`p t = (L/(2β))t² − t/β + η` with a simultaneous induction bounding `‖x_{k+1} − x_k‖` by
`t_{k+1} − t_k` and `‖(F' x_k)⁻¹‖` by `β/(1 − βL(t_k − t_0))`, then the closed form of `t_k`. It also
needs the blocked second-order Taylor estimate above. Reduction to `ContractingWith` does not work:
the Newton map is not a contraction on the ball, only the error sequence is dominated by the
majorant. Reduction to `tendsto_iterate` gives neither the a priori radius nor root existence,
which is the whole content.

## `Numlib/LinearAlgebra/Matrix/Complexify.lean` (1)

`Matrix.complexSpectralRadius_le_of_norm`. The statement is true as now stated, with
`[NormedRing]`, `[NormOneClass]` and `[NormedAlgebra ℝ]`, but the proof does not go through
mechanically. Those hypotheses are instance *arguments*, so they carry their own
`Module ℝ (Matrix n n ℝ)` structure, which local instance search prefers over `Matrix.instModule`;
Mathlib's `FiniteDimensional` and norm-equivalence lemmas therefore do not apply without explicit
instance surgery. Opening a scoped matrix norm inside the declaration does not help, since that
re-elaborates `‖A‖₊` against a different instance than the hypothesis provides. Granting the norm
comparison, the finish is a separate `ENNReal.rpow` limit as `k → ∞`.
