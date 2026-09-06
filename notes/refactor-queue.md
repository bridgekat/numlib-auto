# Refactor queue

Work that is *known* to be wanted and is deliberately not done yet, because it changes existing
declarations. Additive tasks touch only their own module and can run in parallel; a rename or a
restatement has to run alone, on a tree nobody else is writing to (`README.md`,
`tools/tracker/README.md` §Workflow). This file is where those tasks wait.

Each entry says what to move, where, and why it is not already there. An entry is deleted when it
is done — this is a queue, not a history.

## Must run alone

### R1. One Hessenberg relation, not three

`Krylov.HessenbergRelation` (`Numlib/Krylov/Hessenberg.lean`) is single-family: its field is
`A (v j) = ∑ i ∈ range (j + 2), h i j • v i`. Two things that are not instances of it now exist
beside it:

* `Krylov.HessenbergRelation₂ A z v h` (`Numlib/Krylov/QuasiMinRes.lean`) — two unrelated families,
  which is what FGMRES (Saad (9.22)) and TFQMR (Saad (7.70)) satisfy.
* `Krylov.BandRelation` (`Numlib/Krylov/Block.lean`) — bandwidth `p`, for block Arnoldi.

Both belong in `Krylov/Hessenberg`, with `HessenbergRelation` redefined as the diagonal case of
`HessenbergRelation₂` and `BandRelation` at bandwidth one. The agent that wrote `HessenbergRelation₂`
checked the move and reports it is verbatim: the structure and `apply_eq_range`/`apply_sum`/
`residual_eq`/`residual_eq_of_mulVec_eq` transfer with `A (v j) → A (z j)`, no new imports, and all
nine existing surface uses construct the structure or use dot notation, which resolves through the
unfolded head. The one obligation is that `Krylov.HessenbergRelation.{apply_sum, residual_eq,
residual_eq_of_mulVec_eq}` are tracked nodes, so keep one-line wrappers under those names — written
`HessenbergRelation₂.residual_eq hv`, not `hv.residual_eq`, which would self-resolve inside the
namespace. `Krylov.givensRho_ne_zero_of_subdiag_ne_zero` should travel with it, beside
`givensRho_ne_zero_of_rotated_ne_zero`.

### R2. The QMR layer is proved twice

`Numlib/Krylov/BiLanczos.lean` proves `QMR.quasiResidual`, `QMR.IsQuasiMinRes`,
`QMR.norm_residual_le_norm_quasiResidual` (Saad Prop 7.3), `QMR.norm_quasiResidual_eq_norm_gamma`
(7.18) and `QMR.norm_residual_le` (Thm 7.4); `Numlib/Krylov/QuasiMinRes.lean`, written concurrently,
proves all five in general. The reduction is mechanical, and the agent that found it wrote it out:
`‖QMR.quasiResidual A B v₁ w₁ β m y‖` is `Krylov.quasiResidual (BiLanczos.coeff …) β m y` by `rfl`;
the two `IsQuasiMinRes` predicates differ only in the order of their conjuncts; Prop 7.3 is
`HessenbergRelation₂.norm_residual_le` of the diagonal case; (7.18) is `quasiResidual_eq_norm_gamma`;
Thm 7.4 is `IsQuasiMinResIterate.norm_residual_le_mul`, whose hypotheses are *weaker* (it derives
`0 ≤ C` from `0 < c` and needs no `NoBreakdown`).

### R3. Names that say the wrong thing

* `Matrix.IsConsistentlyOrdered.isMinOn_complexSpectralRadius_sor` concludes about
  `spectralRadius ℂ`, not `Matrix.complexSpectralRadius` (which takes a *real* matrix). Rename to
  `isMinOn_spectralRadius_sor`, in the same commit as
  `plans/NumlibSurface/SaadSparse/Chapter04/Section02.toml`, which names it.
* `Numlib/LinearAlgebra/Matrix/Schur` is Schur *triangulation*; `SchurComplement` is the Schur
  *complement*. Both are correct and the pair is confusable; if a third Schur arrives, rename the
  first to `Triangulation`.

### R8. One irreducibility, not two

`Matrix.IsIrreducibleAbs` (`Numlib/LinearSolve/Stationary/DiagDominant.lean`) and
`Matrix.IsPatternIrreducible` (`Numlib/LinearAlgebra/Sparse/Pattern.lean`) are the same definition
character for character — `Matrix.IsIrreducible (A.map (‖·‖))` over `[Norm R]`. They were written
by two agents in the same hour. Delete `IsIrreducibleAbs` rather than aliasing it, and restate its
four dependants (`IsIrreduciblyDiagDominant`, `IsIrreducibleAbs.norm_sub_eq_of_mem_frontier`, and
the Saad Cor 4.8 and Thm 4.9 nodes) over `IsPatternIrreducible`. The spectral one keeps its home:
`IsPatternIrreducible.norm_sub_eq_of_mem_frontier` stays in `DiagDominant`, because it is spectral
theory and not pattern theory.

The import direction is already right — `Sparse/Pattern` depends only on Mathlib, so
`LinearSolve/Stationary/DiagDominant` may import it. What `Pattern` then supplies for free is
permutation invariance, agreement with Mathlib's `IsIrreducible` on entrywise nonnegative reals,
the positive-length path form, and the block-triangular characterization. The one thing the
dependants must add is `[Nontrivial n]` wherever they route through the block-triangular form.

## Additive — can run in any batch that touches the target module

### R4. Private copies that want one home

| what | copies now in | belongs in |
|---|---|---|
| the `gramSchmidtNormed` facts (`span_gsn_Iio`, `eq_sum_inner_smul_gsn`, orthogonality) | `Krylov/{Arnoldi,Hessenberg,Block}.lean` — **three** copies | `Analysis/InnerProductSpace/GramSchmidt.lean` |
| `eval_map_ofReal` | `Eigen/KrylovEigen.lean`, `Krylov/OrthogonalPolynomials.lean` | a polynomial module |
| `Matrix.IsHermitian.spectrum_complexify_eq`, `Matrix.posDef_complexify_iff`, `Matrix.complexifyRingHom` | private in `LinearSolve/Stationary/SPD.lean` | `LinearAlgebra/Matrix/Complexify.lean` |
| `Splitting.iterationOperator_map` | private in `Stationary/SPD.lean` | `Stationary/Splitting.lean` |
| `Matrix.complexSpectralRadius_affine`, `complexSpectralRadius_eq_of_forall_le` | private in `Stationary/SPD.lean` | `Complexify.lean`, if `ConsistentlyOrdered` wants them |
| `Matrix.toEuclideanLin_mul_apply`, `Matrix.inner_toEuclideanLin_of_isHermitian`, `Matrix.mul_eq_zero_of_conjTranspose_mul_self_mul_eq_zero` | `LinearAlgebra/Matrix/SVD.lean` | `Analysis/Matrix/ToEuclideanLin.lean` |

### R5. Declarations in the wrong module, where it has already cost work

* `LinearMap.IsSymmetric.mul_norm_sub_starProjection_le` and `…mul_norm_le_norm_sub_smul` are in
  `Eigen/RayleighRitz` but are pure symmetric-plus-projection facts. `Eigen/Perturbation` needs
  exactly them, cannot import RayleighRitz, and redoes the argument in about thirty lines. Move
  both to `Eigen/MinMax`.
* `Submodule.tanAngle_congr` (`Eigen/KrylovEigen`) and `Submodule.sinAngle_congr`
  (`Eigen/Perturbation`) belong in `Analysis/InnerProductSpace/Projection/Angle`, with the four
  lemmas `notes/lessons-ritz2.md` already flags.
* `LinearMap.IsSymmetric.aeval_map` is in `Krylov/Convergence/Superlinear` and is the *only* reason
  `Krylov/OrthogonalPolynomials` imports it — which drags in `Krylov.CG`, `Krylov.Iterate` and
  `Convergence.CG`. Move to `Krylov/Convergence/Polynomial`.
* `Krylov.aeval_eq_zero_iff_of_degree_lt_grade` → `Krylov/Subspace`.
* `LinearMap.IsSymmetricBoundedBy.energyNorm_le_sqrt_mul_norm` (`Convergence/Superlinear`) and
  `Krylov.energyEnd` / `energyEnd_apply` (`Krylov/Preconditioned`) →
  `Analysis/InnerProductSpace/Energy`.
* `HasLineDerivAt.hasDerivAt_line` is parked in `Analysis/Convex/Gateaux` because no
  `Analysis/Calculus/LineDeriv` module exists. Move it there if one is ever created.
* `Numlib/Variational/AubinNitsche` is two lemmas that use nothing from `Variational/Galerkin`
  except `SesqForm.IsBoundedWith`. Paste them into `Galerkin.lean` next time it is touched.
* `Approximation.polyLE` is defined in `Approximation/Chebyshev` and imported by
  `Approximation/Interpolation`; if `Quadrature` or `Trigonometric` also want it, its home is
  `Approximation/BestApprox`.

### R9. `ChebyshevMinimax` owes two things to the preconditioner modules

* **`Polynomial.Chebyshev.shifted_add_two`.** The plan called it `shifted_succ` and expected a
  two-term recurrence; it is a *three*-term one. With `σ_m := eval ((b+a-2γ)/(b-a)) (T ℝ m)` and
  `L := C ((b+a)/(b-a)) - C (2/(b-a)) * X`, for `a < b` and `γ ∉ Icc a b`,
  `shifted (m+2) a b γ = C (2 σ_{m+1}/σ_{m+2}) * (L * shifted (m+1) a b γ) - C (σ_m/σ_{m+2}) * shifted m a b γ`.
  The instance needed for Chebyshev acceleration is proved privately as
  `Preconditioner.Chebyshev.resPoly_add_two` (the `γ = 0`, `[θ-δ, θ+δ]` case) and should move.
* **Make `eval_shifted` public.** It is `private`, so `Preconditioner/Chebyshev` re-derives the
  evaluation of `shifted` by unfolding the definition. One public lemma removes that and makes
  `shifted_add_two` a five-line proof by `Polynomial.funext`.

### R6. Interfaces several modules now want

* **`WithEnergy.projection`** in `Analysis/InnerProductSpace/Energy` — the `A`-orthogonal projector
  as an endomorphism of `E`. `Multigrid.coarseProjection`, `Schwarz.energyProjection` and
  `LinearSolve/Projection/Optimality` each build it inline.
* **`IsStronglyMonotoneWith`** in `Nonlinear/FixedPoint` — seven consumers, several in
  `Variational/Inequality`.
* **`Matrix.EntrywiseLE.pow`** in `LinearAlgebra/Matrix/Order`, and Saad Thm 1.28 and 1.31–1.33.
  `Matrix/Order.toml` says the last three are "not needed by any surface"; the ILU existence
  theorem (Saad Thm 10.2) cannot be proved without Thm 1.33, so that sentence needs revising too.
* **A projection-gap lemma** in `Analysis/InnerProductSpace/Projection/Angle`: from
  `‖w_j − x_j‖ ≤ δ` for two bases and a coordinate bound, conclude `‖P_X − P_W‖ ≤ M δ`. It is the
  single missing statement for `Krylov.gap_subspaceIterate_le`, which is in turn the only thing
  blocking `Eigen/QRAlgorithm`. Both Mathlib ingredients exist (`Basis.coord` with
  `LinearMap.continuous_of_finiteDimensional`; `ContinuousLinearMap.adjoint` for
  `‖P_X(1−P_W)‖ = ‖(1−P_W)P_X‖`), and the second one-sided bound follows from the first by
  inverting the basis-transport map.

### R11. The Krylov interfaces are single-space where the books are rectangular

`Krylov.adjoint_comp_isSymmetricCoercive` and `…_of_injective` take `A` and `Aᴴ` as endomorphisms of
one space, so they do not apply to Saad §8.1's least-squares problem at all, and that surface had to
prove its coercivity from `LinearMap.isCoercive_iff_forall_pos` instead. `IsMinRes`, `IsGalerkin` and
`IsPetrovGalerkin` have the same shape. Generalizing the first family to `A : E →ₗ[𝕜] F` with the
adjoint as a separate `Astar : F →ₗ[𝕜] E` would cost nothing — the adjoint is already a hypothesis
rather than `LinearMap.adjoint` — and would serve §8.1, §8.3 and any least-squares source. `IsMinError`
is the exception and needs no change: no operator appears in its statement, and it was used unchanged.

### R12. `NumlibSurface/SaadSparse/Common.lean` should hold the adjoint identity

`⟪B x, y⟫ = ⟪x, Bᴴ y⟫` for matrices is proved three times, once each in the Chapter 7, 8 and 9
surfaces (`inner_op_conjTranspose`, `inner_conjTranspose`, `inner_op_conjTranspose`). It belongs in
`Common.lean` beside `ofLp_toEuclideanLin` — together with a **rectangular** `ofLp_toEuclideanLin`,
since the existing one is square-only and forced a private copy in Chapter 8.

### R10. The `Lp` dilation isometry wants to be general

`MeasureTheory.Lp.dilationₗᵢ` (`Numlib/Analysis/Wavelet/Haar.lean`) is stated for dyadic dilations
of `L²(ℝ)`, because that is what the Haar system needs. Atkinson-Han's Theorem 4.2.4 is proved in
`NumlibSurface/AtkinsonHan/Chapter04/Section02.lean` only on the Schwartz space, not as the `L²`
isometry equivalence in the book's normalization, and the general dilation is the single missing
piece: with it, that node finishes at `Lp` level in three lines.

The general shape, worked out by the agent that wrote the special case: `Lp F p μ ≃ₗᵢ[ℝ] Lp F p μ`
for `μ` an additive Haar measure on a finite-dimensional real normed space `E`, `p ≠ ∞`, `F` a real
normed space, with compensating factor `|c ^ finrank ℝ E| ^ (1 / p.toReal)` — which collapses to the
existing `|c| ^ (1/2)` at `E = F = ℝ`, `p = 2`, since `finrank ℝ ℝ = 1`. Every step of the existing
proof carries over with three substitutions: `Real.map_volume_mul_left` becomes
`Measure.map_addHaar_smul`, `Real.volume_preimage_mul_left` becomes `Measure.addHaar_preimage_smul`,
and `Measure.quasiMeasurePreserving_smul` is already general. The step expected to need real work is
`dilationₗ_comp`, where a single `mul_assoc` chain has to split into an outer scalar `smul_smul` and
an inner argument one. Three call sites in `Haar.lean` then need updating.

### R7. Plan bookkeeping

* `plans/NumlibSurface/AtkinsonHan/Chapter05/Section03.toml` should gain `theorem_5_3_17`,
  `theorem_5_3_18`, `theorem_5_3_19`, `theorem_5_3_19_submodule` as nodes — all proved, all
  book-numbered, currently untracked, so §5.3 reads thinner than it is. Note `theorem_5_3_19` lost
  its `Convex ℝ K` binder when it became a specialization.
* `NumlibSurface/SaadSparse.lean`'s index needs the same rewrite `NumlibSurface/AtkinsonHan.lean`
  is getting: chapters have been added since it was written.
* `plans/backbone.md` §3.11 says the CR Steihaug item carries "the global no-breakdown hypothesis";
  it had to be strengthened to positivity. §3.12's sketch of `Krylov/NormalEquations` should drop
  LSQR/LSMR, which were not attempted.
