# Proposal: Saad, *Iterative Methods for Sparse Linear Systems*, Chapters 7–9

Everything this slice needs that could not be written into a new TOML group of its own: nodes to
be added to groups other agents own, restatements of existing declarations, the explicit skip
list, and the coverage table.

Written against the plan as of `28a0401`. New groups created by this slice (these are *not*
proposals; they are in the tree):

| Group | Nodes | What it is |
|---|---|---|
| `Numlib/Krylov/QuasiMinRes` | 14 | the quasi-minimal-residual layer (below, §1.1) |
| `NumlibSurface/SaadSparse/Chapter07` + `Section01..04` | 48 | Saad Ch. 7 |
| `NumlibSurface/SaadSparse/Chapter08` + `Section01..04` | 34 | Saad Ch. 8 |
| `NumlibSurface/SaadSparse/Chapter09` + `Section01..06` | 38 | Saad Ch. 9 |

---

## 1. Additions to existing groups

### 1.1 Why `Numlib/Krylov/QuasiMinRes` is a new module rather than nodes in `Krylov/Hessenberg`

The one structural finding of this slice: **`Krylov.HessenbergRelation` cannot state the relation
that FGMRES and TFQMR satisfy.** Its field is `A (v j) = ∑ i ∈ range (j + 2), h i j • v i`, one
family; FGMRES has `A z_j = ∑ h_ij v_i` with `z_j = M_j⁻¹ v_j` an unrelated family (Saad (9.22)),
and TFQMR has `A u_j = ∑ r_i (B̄)_ij` with the residual vectors on the right (Saad (7.70)). The
existing plan is aware of this only implicitly: `Krylov/Preconditioned.toml`'s `FGMRES.isMinRes`
says its proof comes "from `Krylov.HessenbergRelation.residual_eq` applied with the basis `Z_m` on
the left and the orthonormal `V_{m+1}` on the right", which that lemma does not permit.

`Krylov.HessenbergRelation₂ A z v h` is therefore defined in the new module, with
`HessenbergRelation₂.of_hessenbergRelation` embedding the one-family case. **Its natural long-term
home is `Numlib/Krylov/Hessenberg`**, with `HessenbergRelation` redefined as the diagonal case and
`residual_eq`, `residual_eq_of_mulVec_eq`, `apply_sum` proved once; that is a change to an existing
module, so it is proposed here rather than done. If the orchestrator moves it, `Krylov/QuasiMinRes`
keeps only the `IsQuasiMinResIterate` layer and imports it.

### 1.2 `Numlib/Krylov/Preconditioned` (owned by another agent, being written now)

| node | kind | change |
|---|---|---|
| `Krylov.FGMRES.isMinRes` | theorem | **restate the proof route**: it is `Krylov.IsQuasiMinResIterate.isMinOn_norm_residual` of `Krylov/QuasiMinRes` applied to the two-family relation (9.22), not `HessenbergRelation.residual_eq`. Add `Krylov.HessenbergRelation₂` and `Krylov.IsQuasiMinResIterate` to its `deps`. |
| `Krylov.FGMRES.apply_eq_iff_coeff_eq_zero` | theorem | same: the relation it needs is `Krylov.HessenbergRelation₂.residual_eq_of_mulVec_eq`, which carries the `A Z_j = V_j H_j + v̂_{j+1} e_jᵀ` form (9.23) valid at `h_{j+1,j} = 0`. |

New nodes for that group (Saad §9.2.1, all three stated in the running text and all needed by the
Ch. 9 surface):

* `Krylov.PCG.splitIterate_eq` — **theorem**. For `M = L Lᴴ`, the split-preconditioned CG recurrence
  (Saad Alg. 9.2) and `PCG.iterate` (Alg. 9.1) produce the same iterates, both equal to
  `CG.iterate` for `L⁻¹ A L⁻ᴴ` transported by `u = Lᴴ x`. Deps: `PCG.iterate`, `CG.iterate`.
  *Why here*: it is a statement about `PCG.iterate`, and the surface theorem
  `SaadSparse.Chapter09.splitPcg_eq_pcg` should specialize it rather than redo a change of variables.
* `Krylov.PCG.iterate_eq_rightPreconditioned` — **theorem**. Left-preconditioned CG in the
  `M`-inner product equals right-preconditioned CG (for `A M⁻¹`, `x = M⁻¹ u`) in the `M⁻¹`-inner
  product. Deps: `PCG.iterate`, `WithEnergy`. *Why here*: same reason; it is the closing paragraph
  of §9.2.1 and belongs with the object it is about.

### 1.3 `Numlib/Analysis/InnerProductSpace/Energy`

Saad §9.2.1's three self-adjointness observations are `WithEnergy` facts with no Krylov content,
and Ch. 9's §9.2, §9.3 and §9.6 all use them:

* `LinearMap.IsSymmetricCoercive.isSymmetric_inv_comp_withEnergy` — **theorem**. For symmetric `A`
  and symmetric coercive `M`, `M⁻¹ A` is symmetric as an operator on `WithEnergy M`:
  `⟪M⁻¹ A x, y⟫_M = ⟪A x, y⟫ = ⟪x, M⁻¹ A y⟫_M`. Deps: `WithEnergy`, `WithEnergy.inner_equiv`,
  `LinearMap.IsSymmetricCoercive`.
* `LinearMap.IsSymmetricCoercive.isSymmetric_comp_inv_withEnergy` — **theorem**. The companion for
  `A M⁻¹` on `WithEnergy (M⁻¹)`, and for `M⁻¹ A` on `WithEnergy A` when `A` is coercive (P-9.2).
* `LinearMap.isSkewAdjoint_inv_comp_withEnergy` — **theorem**. If `Nᴴ = -N` and `M` is symmetric
  coercive then `M⁻¹ N` is skew-adjoint on `WithEnergy M`. This is what makes the
  Concus–Golub–Widlund tridiagonal (9.29) work; it is one `rw` from the previous one.

*Why there rather than in `Krylov/Preconditioned`*: they mention no Krylov object, they are the
reason the energy space exists, and the eigenvalue and variational layers will want them too.

### 1.4 `Numlib/Krylov/Arnoldi`

* `Arnoldi.coeff_add_conj_of_shifted_adjoint` — **theorem**. If the adjoint of `A` is `c • 1 - A`
  (that is, `A - (c/2)` is skew-adjoint) then
  `coeff A b i j + conj (coeff A b j i) = c * ⟪v_i, v_j⟫`, so the Arnoldi coefficient array is
  tridiagonal with `re h_jj = c/2` and `h_{j,j+1} = -conj h_{j+1,j}`. Deps: `Arnoldi.coeff`,
  `Arnoldi.coeff_eq_zero_of_adjoint_mem`.
  *Why here*: it is the skew companion of `Arnoldi.coeff_conj_of_isSymmetric` and sits beside
  `Arnoldi.coeff_eq_zero_of_adjoint_mem`, which already gives the band structure (with `s = 2`,
  since `(c • 1 - A) v ∈ span {v, A v}`). **Both halves were prototyped and compile without
  `sorry`**, five lines each; the whole of Saad (9.29) is these two facts. Serves Saad §9.6 (CGW),
  §6.10 (Faber–Manteuffel, `ν(A) ≤ 1`) and any later "CG for normal matrices" material.

### 1.5 `Numlib/Analysis/InnerProductSpace/Coercive`

* `LinearMap.IsSymmetricCoercive.comp_inv_comp` — **theorem**. If `A : E →ₗ[𝕜] E` is symmetric
  coercive and `B : F →ₗ[𝕜] E` is injective with closed range (automatic in finite dimension), then
  the Schur complement `Bᴴ ∘ A⁻¹ ∘ B : F →ₗ[𝕜] F` is symmetric coercive. Deps:
  `LinearMap.IsSymmetricCoercive`, `LinearMap.IsCoerciveWith`.
  *Why here*: it is a statement about coercivity alone, the module's subject, and it is the whole
  mathematical content of Saad Corollary 8.1 (Uzawa) — the rest is the Richardson iteration.
  A second consumer is any finite-element or Stokes source (`inf–sup` gives the constant), so it
  should not be buried in a Saad surface file.

### 1.6 `Numlib/LinearSolve/Projection/Additive`

The Cimmino identification of Saad §8.2 needs the least-squares variant with a *relaxation
parameter* and its residual identity, which the group's `residual_additiveStep` already has. No
change is proposed; `Projection/Additive` as planned covers §8.2 exactly, and the surface
(`SaadSparse.Chapter08.cimmino_eq_additiveStep`) goes through `SaadSparse.Chapter05.additiveStep`, which
already exists. **Answer to the question posed in the brief: yes, Saad §8.2 is a surface
specialization of `Projection/Additive` and needs nothing new from it** — Cimmino is
`additiveStep` for `AᴴA x = Aᴴb` over the coordinate subspaces, and the NE/NR-SOR sweeps are
`multiplicativeStep` over the same family.

---

## 2. Changes to existing declarations

* **Done: `SaadSparse.Chapter07.equation_7_29` was renamed `equation_7_30`.** It states (7.30), the
  *iterate* form of the smoothing relation, as its own doc comment said; the residual forms the
  book labels (7.28) and (7.29) were unstated and are now `equation_7_28` and `equation_7_29`.
* **`SaadSparse.Chapter07.bcgAlpha` and `bcgBeta` are in `Chapter07/Section04.lean` and belong in
  `Section03`**, beside Algorithm 7.3, which is where every other reading of that algorithm's lines
  lives. They were defined in the §7.4 file because §7.4 was written first and needed them.
  Section03 therefore states lines 4 and 8 under the neutral names `bcg_alpha_eq` and
  `bcg_beta_eq`, and P-7.7 spells the coefficients as `BCG.alpha`/`BCG.beta` rather than shadowing
  the Section04 abbrevs. Moving the two abbrevs up would let both files use one name; it is a
  change to a file another agent had just landed, so it is proposed rather than done.
* **`Krylov/Hessenberg`: generalize `HessenbergRelation` to two families** (§1.1). Runs alone, per
  the tracker README's rule for restatements.
* **`SaadSparse/Chapter06/Section05`: re-base the QGMRES layer on the backbone.**
  `SaadSparse.Chapter06.qgmres`, `quasiResidualNorm`, `z`, `ζ`, `equation_6_50`, `equation_6_51`,
  `equation_6_55`, `problem_6_25` are already stated for an arbitrary `u`, `h` satisfying
  `Krylov.HessenbergRelation (op A) u h` — that is, they *are* the quasi-minimal-residual theory,
  written in a surface file. They should become specializations of `Krylov/QuasiMinRes`:
  `qgmres` of `Krylov.IsQuasiMinResIterate`, `equation_6_51` of
  `Krylov.IsQuasiMinResIterate.norm_residual_le`. Without this, Chapter 7 either duplicates them or
  depends on a Chapter 6 surface declaration for its backbone content, which the README forbids in
  spirit even where the tracker cannot see it.
* **`SaadSparse/Chapter06`: Theorem 6.11 is missing and should be added**, as
  `SaadSparse.Chapter06.theorem_6_11` in `Chapter06/Section05.toml`. `Chapter06/Section05.lean`'s own
  header reports it as "not formalized here (reported to the plan)", and `plans/saadsparse-ch6.md`
  §R31 estimates ~60 lines because it planned to build a Gram–Schmidt factorization `S` of the IOP
  basis. With `Krylov.IsQuasiMinResIterate.norm_residual_le_mul` it is a two-line corollary:
  `κ₂(V_{m+1})` enters as the ratio `C/c` of the two-sided bound `c‖y‖₂ ≤ ‖V_{m+1} y‖₂ ≤ C‖y‖₂`,
  no factorization and no separate full-rank hypothesis. Saad's Theorem 7.4 is the same statement,
  which is why the backbone lemma pays for itself twice.
* **`Numlib/Krylov/BiLanczos`: `QMR.IsQuasiMinRes` and `QMR.norm_residual_le` should specialize
  `Krylov/QuasiMinRes` rather than restate it.** `QMR.IsQuasiMinRes` as planned is
  `Krylov.IsQuasiMinResIterate` at the two-sided Lanczos data, and `QMR.norm_residual_le` is
  Prop 7.3 + Thm 7.4, both of which are backbone theorems about arbitrary Hessenberg relations. The
  Ch. 7 surface (`SaadSparse.Chapter07.qmr_isQuasiMinResIterate`, `proposition_7_3`, `theorem_7_4`)
  names both the general and the BiLanczos node in its `deps`, so either route works, but proving
  them twice would be waste.

---

## 3. Not planned, and why

| Item | Reason |
|---|---|
| §7.1.2 look-ahead Lanczos (Parlett–Taylor–Liu, the `2×2` pivots, the "added complexity" discussion) | a description of a family of implementations, with no claim attached. **Revised:** the rest of §7.1.2 is *not* of that kind and is now planned — the lucky-breakdown claim (`noSeriousBreakdown_of_bilanczosVhat_eq_zero`, `krylov_mem_invtSubmodule_of_bilanczosVhat_eq_zero`, `lanczosSolve_eq_of_bilanczosVhat_eq_zero`) and the formal orthogonal polynomials of (7.7) with their moment matrix (`bilanczosPoly`, `polyForm`, `momentMatrix`, and the backbone layer in `Numlib/Krylov/BiLanczos`). Only the `LU` factorization `M_k = L_k U_k` remains skipped |
| **P-7.1** (arbitrary dual coefficients `h_ij`) | part (b), that the `v_i` and `T_m` do not depend on the `h_ij`, is a real independence theorem and *not* a copy of Proposition 7.1. It needs a second, parameterized two-sided process in the backbone plus a uniqueness argument for the primal family (`v_j` in the Krylov subspace, orthogonal to the dual Krylov subspace, normalized by `(v_j, w_j) = 1`); and the printed "modify line 4" answer `α_j = (A v_j, w_j)` is not correct for an arbitrary dual basis, since the modified `w_j` are no longer biorthogonal to the `v_i`. Left open |
| **P-7.4** (`(v_i, w_j) = ±δ_ij` with `T_m` Hermitian tridiagonal) | the off-diagonal half is `BiLanczos.norm_beta_succ`, `|β_{j+1}| = δ_{j+1}`, which is stated. The Hermitian claim also needs the diagonal `α_j = (A v_j, w_j)` to be *real*, which holds over the reals but not over the complexes; a faithful statement is therefore a third algorithm variant restricted to `ℝ`. Left open |
| P-7.5, third part ("derive a general look-ahead procedure") | asks for an algorithm and states no theorem. The first part is now `SaadSparse.Chapter07.problem_7_5` — in a range one index shorter than the printed one, which is off by one (see the declaration's doc comment) |
| P-7.8 (a general consistent polynomial family `ψ_j` and its recurrences) | a five-part algebra exercise producing an algorithm the book does not state a theorem about; BICGSTAB is its `ψ_{j+1} = (1 - ω_j t) ψ_j` case and is planned. Its natural home is `Chapter07/Section04.lean`, whose `bcgResidualPoly` layer it would reuse; part (a), `ψ_j(0) = 1`, is two lines there |
| P-7.11 (block two-sided Lanczos, block BCG/QMR) | belongs with `Numlib/Krylov/Block` (phase 3), not with this slice |
| §7.4 residual-norm estimate strategies, Tables 7.1–7.3 | numerical experiments |
| Saad §8.1, the spectrum `±σ_i(A)` of `[[0, A], [Aᴴ, 0]]`, and **P-8.4** | **SKIP.** Needs a singular value decomposition: Mathlib has `LinearMap.singularValues` but no factorization theorem, and `Numlib/LinearAlgebra/Matrix/SVD` is phase 3 and unwritten. That each `±σ_i` *is* an eigenvalue can be had without a factorization (pair `(u, ±v)` for `Aᴴ A v = σ² v`; M difficulty); what needs the factorization is the multiplicity count — "these are all of them" — which is the book's claim and what P-8.4's plot of `‖B(α)‖₂` rests on. Reopen only with `Matrix/SVD` |
| **P-8.6 (c), (d)** (CG on the singular consistent system `P A P x = P b`, and the `QR` variant) | (a) and (b) are now proved (`constraintProjector`, `problem_8_6_projector`, `equation_8_35`) and the "which subspace" half of (c) is `problem_8_6_cg_subspace`. **The old reason — "needs `Numlib/Krylov/Singular` (Choi, phase 2), unwritten" — is stale: that module exists.** It carries the *minimal-residual* singular theory, not CG on a semidefinite consistent system. The one missing backbone theorem: for symmetric positive **semi**definite `A` and `b ∈ Ran A`, CG from `x₀ = 0` is well defined, its iterates lie in `𝒦_m(A, b) ⊆ Ran A`, and it terminates at `A⁺ b`, the minimum-norm solution. Plan it in `Krylov/Singular.lean`; (d) additionally needs a `QR` factorization of a rectangular `B`, which Mathlib has only as Gram–Schmidt |
| **P-8.9** (inexact Uzawa: convergence when the inner solves have residual `≤ ε_k → 0`) | needs a perturbed-fixed-point theorem (`x_{k+1} = T x_k + e_k`, `‖e_k‖ → 0`, `‖T‖ < 1` ⇒ convergence) that no other source in the corpus asks for; `Numlib/Nonlinear/FixedPoint` has the exact version only. Not one node but three: the real-sequence lemma `a_{k+1} ≤ q a_k + ε_k` ⇒ `a_k → 0`, the perturbed Banach iteration with the geometric-tail bound for `ε_k ≤ α^k`, and `‖·‖₂ = ρ` for the symmetric `I − ω S` (since (8.33) bounds the spectral radius, not the norm) — plus a surface definition of the inexact iteration, which the book gives only through the threshold `ε_{k+1}` |
| P-8.11 | empty in the source |
| §9.2.2 operation counts, Example 9.1, **P-9.7**, **P-9.8**, **P-9.9** | arithmetic-cost accounting, no theorem content; the algebraic identity (9.8) that makes Eisenstat's trick possible *is* planned |
| **P-9.4** (right/split preconditioned CGNR and CGNE), **P-9.5** (the "centered" variants `A M⁻¹ Aᴴ` and `Aᴴ M⁻¹ A`) | six rearrangements of Algorithm 9.1 in six inner products; the two the book writes out are planned and the rest are the same derivation |
| §9.4.1 closing remark, "FGMRES converges if one `z_j` per cycle is a steepest descent direction" | true and provable from Proposition 9.2 plus `Projection.residualNormSDStep`, but the book states no theorem and gives no hypotheses; planning it would be inventing the statement |
| §9.6 inner–outer variants (Golub–Overton) | mentioned in the notes only |
| Saad §9.6's claim that CGW has a *minimization* property | it has none: `M⁻¹A` is not `M`-self-adjoint, only `1 + skew`. The surface states the Galerkin property, which is what the derivation actually gives |

---

## 4. Coverage summary

Numbered results, algorithms and the equations the book labels and uses later. "Planned" means a
node exists (in a group created by this slice, or in `Krylov/{BiLanczos,NormalEquations,
Preconditioned}` written concurrently).

### Chapter 7

| Book | Status | Node |
|---|---|---|
| Algorithm 7.1 | planned | `SaadSparse.Chapter07.bilanczosV`, `bilanczosV_eq` → `BiLanczos.vec` |
| (7.1) | planned | `SaadSparse.Chapter07.equation_7_1`, `equation_7_1_norm`, `inner_smul_smul_eq_one` → `BiLanczos.delta_mul_beta_succ` |
| (7.2) | planned | `SaadSparse.Chapter07.bilanczosCoeff`, `T`, `norm_bilanczosBeta_succ` |
| **Proposition 7.1** | planned | `SaadSparse.Chapter07.proposition_7_1`, `proposition_7_1_span` → `BiLanczos.inner_vec_dualVec` |
| (7.3), (7.4), (7.5) | planned | `SaadSparse.Chapter07.equation_7_3`, `equation_7_5` |
| (7.6) | planned | `SaadSparse.Chapter07.NoBreakdown`, `NoSeriousBreakdown` |
| §7.1.2 lucky breakdown | planned | `SaadSparse.Chapter07.noSeriousBreakdown_of_bilanczosVhat_eq_zero`, `krylov_mem_invtSubmodule_of_bilanczosVhat_eq_zero`, `span_bilanczosV_succ`, `lanczosSolve_eq_of_bilanczosVhat_eq_zero` |
| (7.7), moment matrix | planned | `SaadSparse.Chapter07.polyForm`, `bilanczosPoly`, `momentMatrix` and their theorems; the `LU` factorization `M_k = L_k U_k` is *not* planned (no general `LU`-existence theorem is available) |
| Algorithm 7.2, (7.9) | planned | `SaadSparse.Chapter07.lanczosSolve`, `equation_7_9` |
| Algorithm 7.3, (7.10)–(7.12) | planned | `SaadSparse.Chapter07.bcg`, `bcg_eq_lanczosSolve` → `BCG.iterate` |
| **Proposition 7.2**, (7.13)–(7.14), P-7.10 | planned | `SaadSparse.Chapter07.proposition_7_2` → `BCG.inner_residual_dualResidual_eq_zero` |
| Algorithm 7.4, (7.15)–(7.17) | planned | `SaadSparse.Chapter07.qmr`, `qmr_isQuasiMinResIterate`, `equation_7_16` |
| (7.18), (7.19), (7.20) | planned | `SaadSparse.Chapter07.equation_7_18`, `equation_7_19`, `equation_7_20` |
| **Proposition 7.3**, (7.21)–(7.22) | planned | `SaadSparse.Chapter07.proposition_7_3` → `Krylov.IsQuasiMinResIterate.norm_residual_le` |
| **Theorem 7.4** | planned | `SaadSparse.Chapter07.theorem_7_4` → `Krylov.IsQuasiMinResIterate.norm_residual_le_mul` |
| (7.23), (7.24) | planned | `SaadSparse.Chapter07.equation_7_23`, `equation_7_24` |
| **Proposition 7.5**, (7.25) | planned | `SaadSparse.Chapter07.proposition_7_5` |
| (7.26)–(7.31), Algorithm 7.5 | planned | `SaadSparse.Chapter07.equation_7_26`, `equation_7_28`, `equation_7_29`, `equation_7_30`, `qmrSmoothing` |
| (7.32)–(7.39) | planned | `SaadSparse.Chapter07.bcgResidualPoly`, `bcg_residual_eq_aeval` |
| Algorithm 7.6, (7.40)–(7.45) | planned | `SaadSparse.Chapter07.cgs`, `cgs_residual_eq` |
| Algorithm 7.7, (7.46)–(7.55) | planned | `SaadSparse.Chapter07.bicgstab`, `bicgstab_residual_eq`, `equation_7_53`, `equation_7_55` |
| Algorithm 7.8, (7.56)–(7.82) | planned | `SaadSparse.Chapter07.tfqmr`, `equation_7_70`, `equation_7_76`, `tfqmr_isQuasiMinResIterate` |
| (7.83) | planned | `SaadSparse.Chapter07.equation_7_83` |
| P-7.2, P-7.6 | planned | `SaadSparse.Chapter07.problem_7_2`, `problem_7_6` |
| P-7.3 | planned | `SaadSparse.Chapter07.problem_7_3` |
| P-7.5 (first part) | planned | `SaadSparse.Chapter07.problem_7_5` |
| **P-7.7** | planned | `SaadSparse.Chapter07.problem_7_7`, `problem_7_7_direction`, `problem_7_7_start`. *This problem appeared in neither the coverage table nor the skip list of the original pass; the "7 skipped" headline silently counted it* |
| P-7.9 | planned | answered inside `SaadSparse.Chapter07.equation_7_70` and `equation_7_76`, which are stated for an arbitrary column scaling |
| P-7.1, P-7.4, P-7.8, P-7.11 | skipped | §3 |

**Chapter 7: 5 of 5 numbered results planned, 8 of 8 algorithms planned, 7 of 11 problems planned
(P-7.2, P-7.3, P-7.5, P-7.6, P-7.7, P-7.9, P-7.10) and 4 skipped (P-7.1, P-7.4, P-7.8, P-7.11).**

### Chapter 8

| Book | Status | Node |
|---|---|---|
| (8.1)–(8.4) | planned | `SaadSparse.Chapter08.equation_8_1`, `equation_8_3` |
| (8.5)–(8.7), P-8.1 | planned | `SaadSparse.Chapter08.equation_8_5` |
| spectrum of `[[0,A],[Aᴴ,0]]`, P-8.4 | skipped | §3 -- the reason changed: `Numlib/LinearAlgebra/Matrix/SVD` now exists, and what is left is the multiplicity count |
| (8.8) | planned | `SaadSparse.Chapter08.equation_8_8` |
| Algorithm 8.1, (8.11)–(8.15) | planned | `SaadSparse.Chapter08.neSorStep`, `neSorStep_isPetrovGalerkin` |
| Algorithm 8.2, (8.16)–(8.18) | planned | `SaadSparse.Chapter08.nrSorStep`, `nrSorStep_isGalerkin` |
| Algorithm 8.3, (8.19)–(8.21) | planned | `SaadSparse.Chapter08.cimmino`, `cimmino_eq_additiveStep` |
| (8.22), P-8.2 | planned | `SaadSparse.Chapter08.cimmino_eq_richardson`, `equation_8_22` |
| (8.23)–(8.25), P-8.8 | planned | `SaadSparse.Chapter08.equation_8_24`, `equation_8_25` |
| (8.26)–(8.27) | planned | `SaadSparse.Chapter08.blockCimmino` |
| Algorithm 8.4 and its optimality | planned | `SaadSparse.Chapter08.cgnr`, `cgnr_eq`, `cgnr_isMinRes` → `Krylov.CGNR.iterate` |
| Algorithm 8.5 and its optimality | planned | `SaadSparse.Chapter08.cgne`, `cgne_eq`, `cgne_isMinError` |
| "the same subspace" | planned | `SaadSparse.Chapter08.subspace_adjoint_eq` |
| (8.28)–(8.30) | planned | `SaadSparse.Chapter08.saddleMatrix`, `equation_8_30` |
| Algorithm 8.6, (8.31)–(8.32), P-8.7 | planned | `SaadSparse.Chapter08.uzawa`, `equation_8_32` |
| **Corollary 8.1** | planned | `SaadSparse.Chapter08.corollary_8_1`, `schur_posDef` |
| "(8.32) is the `A⁻¹`-normal equations", P-8.5(a) | planned | `SaadSparse.Chapter08.equation_8_32_isMinRes` |
| P-8.5 (b) | planned | `SaadSparse.Chapter08.problem_8_5b` |
| Algorithm 8.7 | planned | `SaadSparse.Chapter08.arrowHurwicz` |
| Example 8.2 | planned | `SaadSparse.Chapter08.example_8_2` |
| P-8.3 | planned | `SaadSparse.Chapter08.cimminoNE`, `cimminoNE_eq_additiveStep`, `cimminoNE_eq_jacobi` |
| P-8.6 (a), (b) | planned | `SaadSparse.Chapter08.constraintProjector`, `problem_8_6_projector`, `equation_8_35` |
| P-8.6 (c) (the subspace half) | planned | `SaadSparse.Chapter08.problem_8_6_cg_subspace` |
| P-8.6 (c) (CG itself), P-8.6 (d) | skipped | §3 |
| P-8.9 | skipped | §3 |
| P-8.10 | planned | `SaadSparse.Chapter08.problem_8_10` |
| P-8.11 | skipped | empty in the source |
| P-8.12 (1), (2), (3), (5) | planned | `SaadSparse.Chapter08.problem_8_12_indefinite`, `problem_8_12_residual`, `problem_8_12_steepestDescent_stalls`, `problem_8_12_minRes_stalls`, `problem_8_12_reduced` |

**Chapter 8: 1 of 1 numbered result, 7 of 7 algorithms, and -- after the gap pass -- 10 of 12
problems: P-8.1, P-8.2, P-8.3, P-8.5, P-8.6 (a), (b) and the subspace half of (c), P-8.7, P-8.8,
P-8.10, P-8.12 (1), (2), (3), (5). Left: P-8.4 and P-8.9, plus P-8.6 (c), (d) and P-8.11 (empty in
the source); one non-numbered claim, the `±σ_i` spectrum, still open, but for the multiplicity
count rather than for want of an SVD.**

### Chapter 9

| Book | Status | Node |
|---|---|---|
| (9.1)–(9.3), P-9.1, P-9.10 | planned | `SaadSparse.Chapter09.leftPreconditioned`, `solution_iff`, `problem_9_1` |
| §9.2.1 self-adjointness | planned | `SaadSparse.Chapter09.isSymmetric_energy` (+ §1.3 backbone nodes) |
| Algorithm 9.1 | planned | `SaadSparse.Chapter09.pcg`, `pcg_eq` → `Krylov.PCG.iterate` |
| Algorithm 9.2 and "the iterates are identical", P-9.3 | planned | `SaadSparse.Chapter09.splitPcg`, `splitPcg_eq_pcg` |
| right-preconditioned CG in the `M⁻¹` product | planned | `SaadSparse.Chapter09.rightPcg_eq_pcg` |
| P-9.2 | planned | `SaadSparse.Chapter09.pcgEnergyA` |
| P-9.6 | planned | `SaadSparse.Chapter09.problem_9_6` → `Krylov.PCG.energyNorm_error_le` |
| (9.5)–(9.8), Algorithm 9.3 | planned | `SaadSparse.Chapter09.equation_9_8`, `eisenstat` |
| §9.2.2 counts, Example 9.1, P-9.7, P-9.9, P-9.8 (a), (b) | skipped | §3 |
| P-9.8 (c) | planned | `SaadSparse.Chapter09.problem_9_8c`, `problem_9_8c_ssor` |
| Algorithm 9.4, Algorithm 9.5, §9.3.3 | planned | `SaadSparse.Chapter09.gmresLeft`, `gmresRight` and their `isMinRes` |
| (9.17)–(9.21), (9.18), P-9.11 | planned | `SaadSparse.Chapter09.equation_9_18` |
| **Proposition 9.1** | planned | `SaadSparse.Chapter09.proposition_9_1` → `Krylov.exists_aeval_of_isMinResIterate_preconditioned` |
| (9.10)–(9.15), P-9.13 | planned | `SaadSparse.Chapter09.gmresEnergy`, `equation_9_12` |
| Algorithm 9.6, (9.22)–(9.26) | planned | `SaadSparse.Chapter09.fgmres`, `equation_9_22` |
| **Proposition 9.2** | planned | `SaadSparse.Chapter09.proposition_9_2` → `Krylov.IsQuasiMinResIterate.isMinOn_norm_residual` |
| **Proposition 9.3** and its remark | planned | `SaadSparse.Chapter09.proposition_9_3`, `hessenbergSq_isUnit_of_linearIndependent` |
| §9.4.1 steepest-descent remark | skipped | no statement in the book, §3 |
| §9.4.2, (9.28) | planned | `SaadSparse.Chapter09.fdqgmres` (algorithm-only) |
| Algorithm 9.7, Algorithm 9.8 | planned | `SaadSparse.Chapter09.pcgnr`, `pcgne` and their `_eq` |
| P-9.4 | planned | `SaadSparse.Chapter09.rightPcgnr_eq`, `splitPcgnr_eq`, `rightPcgne_eq`, `splitPcgne_eq` |
| P-9.5 | planned | `SaadSparse.Chapter09.isSymmetric_centredNR`, `centredPcgnr`, `centredPcgne`, `centredPcgne_eq` |
| P-9.12 | planned | `SaadSparse.Chapter09.pcr`, `pcr_eq` |
| §9.6, (9.29) and the CGW recurrence | planned | `SaadSparse.Chapter09.cgwM`, `isSkewAdjoint_energy`, `equation_9_29`, `cgw`, `cgw_alpha`, `cgw_isGalerkinIterate` |

**Chapter 9: 3 of 3 numbered results, 8 of 8 algorithms, and -- after the gap pass -- 12 of 13
problems: P-9.1 to P-9.6, P-9.8 (c), P-9.10 to P-9.13. Left: P-9.7, P-9.9 and P-9.8 (a), (b), all
operation counts.**

### Headline

**All 9 numbered results and all 23 algorithms of Chapters 7–9 are planned.** What is skipped is
20 of the 36 end-of-chapter problems (algorithm variants, operation counts, and three that need
machinery the library does not have: an SVD, the singular-system layer, and a perturbed
fixed-point theorem) and the two implementation topics the book itself states no theorem about
(look-ahead Lanczos, Eisenstat's operation counts).
