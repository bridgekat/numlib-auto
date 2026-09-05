<!--
The item inventory that used to live here is the tracker plan now: the TOML group files beside this
document list every key declaration, and the declarations themselves carry the signatures and the
doc comments. What remains here is the reasoning — why the library is shaped this way — which no
tool can derive from the compiled environment.

Signature blocks have been dropped everywhere. Where the code exists, `lake exe tracker show
<group>` prints the real signatures; where it does not, the planned statements are the open nodes
of the group files — the phase 2–4 modules such as `Numlib/Krylov/Singular.toml`, and the
later-phase items appended to finished groups — each with its description, its suggested
dependencies among the key declarations and its source, and `lake exe tracker ready` lists the
ones that can be started. This file names the groups and keeps the arguments.
-->

# Backbone design notes

This is the design record for the `Numlib` backbone, the general layer of the library described in
[README.md](../README.md). It proposes a spanning tree of general definitions and theorems for
the corpus of §0, places every item in the module hierarchy under `Numlib/`, gives the key Lean
statements, describes the difficult proofs, and says what is left to the surface layer.

The Lean modules under `Numlib/` (imported by `Numlib.lean`) implement the phase-1 part of this
plan (§7): every phase-1 statement is stated there with its final name and hypotheses, and the Lean
blocks of §2–§5 for phase-1 modules give the main statements with those names and hypotheses
(`variable` declarations and repeated hypotheses abbreviated, routine API lemmas omitted). Where a
Lean block describes a later phase it is a sketch. The per-book surface plans in ``
cite the section numbers §1–§10 of this file; their code goes into the `Surface/` libraries of §8.

---

## 0. Corpus and phase-1 scope

### 0.1 The eight sources and what each contributes

| Source | Core content | Structure it uses | Role in the backbone |
|---|---|---|---|
| Saad, *Iterative Methods for Sparse Linear Systems* (2003) | Projection methods (Petrov–Galerkin), Krylov methods (Arnoldi, FOM, GMRES, Lanczos, CG, CR, GCR), convergence via Chebyshev polynomials, stationary methods (Jacobi/GS/SOR), regular splittings, preconditioning | Inner product spaces + a linear operator for Ch. 5–6 and 9; matrix entries, nonnegativity and graphs for Ch. 4; Jordan form for asymptotics | **The spine.** Almost all of Ch. 5–6 generalizes verbatim to bounded operators on Hilbert spaces with finite-dimensional search spaces. |
| Fong & Saunders, *CG versus MINRES* (2012) | Minimization properties of CG/CR/MINRES; monotonicity of `‖x_k‖`, `‖x−x_k‖`, `‖x−x_k‖_A`, `‖r_k‖`, backward errors; stopping rules | Inner product + self-adjoint positive `A`; finite termination for the sign arguments | Integration test for the abstract Galerkin / minimal-residual specifications and the CG/CR recurrences. |
| Atkinson & Han, *Theoretical Numerical Analysis* (2009) | Neumann series and perturbation theorem with explicit bounds, uniform boundedness ⇒ quadrature convergence, best approximation, projections, Lebesgue lemma, Banach fixed point with error bounds, Newton/Kantorovich, CG for operator equations, Lax–Milgram, Galerkin/Céa/Petrov–Galerkin/inf–sup, Lax equivalence, Sobolev/FEM/integral equations | Banach and Hilbert spaces throughout | **The generality guide.** Its "functional analysis framework" is exactly the backbone philosophy; it fixes the natural level of generality of most items. |
| Choi, *Iterative methods for singular linear equations and least-squares problems* (2006) | Lanczos process, CG/SYMMLQ/MINRES as subproblems on `T̄_k`, MINRES on singular/incompatible systems, MINRES-QLP, norm/condition estimates, preconditioning | Inner product + self-adjoint `A` (any rank); finite-dimensional pseudoinverse; reflector algebra | Extends the Krylov spine to singular systems and minimum-norm solutions; QR/QLP implementation layer. |
| Meurant & Strakoš, *Lanczos and CG in finite precision* (2007) | Lanczos ↔ orthogonal polynomials ↔ Gauss quadrature; CG error identities (HS 6:1, 6:3), `A`-norm error as Gauss remainder; Paige's finite-precision theory; Greenbaum's backward-like analysis | Spectral measure of a self-adjoint operator; unreduced tridiagonal matrices; floating-point model for §4–5 | Polynomial/measure layer of the Krylov spine (exact arithmetic); template for the floating-point layer. |
| Saad, *Numerical Methods for Large Eigenvalue Problems* (2011) | Projectors, resolvent, Bauer–Fike, residual bounds, Gershgorin, Courant–Fischer, power/inverse/subspace iteration, Rayleigh–Ritz, Arnoldi/Lanczos eigenvalue bounds (Kaniel–Paige–Saad), Chebyshev filtering | Shares Ch. 1 and Ch. 6 (Krylov, Arnoldi, Lanczos) with the sparse-systems book | Second consumer of the Krylov spine; drives the eigenvalue layer. |
| Kress, *Numerical Analysis* (1998) | Gaussian elimination/QR, Banach fixed point, Jacobi/GS/SOR (incl. Young's theory), condition numbers, SVD, Tikhonov, Newton, eigenvalue estimates (Gershgorin, Bauer–Fike), Jacobi/QR eigenvalue algorithms, interpolation, quadrature, IVPs/BVPs, integral equations | Mixture of finite-dimensional and Banach-space statements | Cross-check for the stationary, perturbation and approximation layers; source of the interpolation/quadrature/ODE branches. |
| Higham, *Accuracy and Stability of Numerical Algorithms* (2002) | Standard model of floating point, `γ_n` calculus, backward error of dot products, triangular solves, LU, Cholesky, QR; perturbation theory (Rigal–Gaches, Oettli–Prager, Skeel); stationary iterations in finite precision; matrix powers | Real numbers with relative perturbations `δ`; entrywise matrix order; normwise bounds derived from componentwise ones | Reserved floating-point layer (§6); its exact-arithmetic parts (Ch. 6–7) belong to the perturbation layer (2.2). |

Theorem numbers for Saad-eig refer to the revised edition; Kress is GTM 181.

### 0.2 Phase-1 books and sections

Phase 1 formalizes three books, chosen to maximize reuse of the spine and to exercise the
Banach/Hilbert-space level of generality:

1. **Saad, *Iterative Methods for Sparse Linear Systems*** — §1.11–1.13, Ch. 4 (§4.1–4.2), Ch. 5,
   Ch. 6 in full; Ch. 7–9 are phase 2. It is the densest source of the spine and shares its Ch. 1
   and Ch. 6 with the eigenvalue book.
2. **Fong & Saunders, *CG versus MINRES*** — complete. Short, theorem-dense, and it exercises exactly
   the README's motivating example ("abstract MINRES as iterative argmins of residuals" with
   several implementations satisfying it).
3. **Atkinson & Han, *Theoretical Numerical Analysis*** — Ch. 2 (§2.3–2.5), §3.3–3.7, Ch. 5
   (§5.1–5.4, 5.6), §8.2–8.3, 8.7, Ch. 9; §6.2 (Lax equivalence) and Ch. 11–12 (abstract parts)
   are phase 3; Ch. 7, 10, 13–14 (Sobolev, FEM, BIE) are out of scope until Mathlib has Sobolev
   spaces. It supplies the Banach/Hilbert-space forms in which the backbone is stated, and its CG
   chapters (5.6, 9.4) meet Saad's CG in the middle.

   *Amended (§13).* Chapter 4 was listed here as out of scope "until Mathlib has Sobolev spaces",
   which was simply wrong: Fourier series, the Fourier transform, the DFT and Haar wavelets use no
   Sobolev space. Mathlib has `SchwartzMap`, `TemperedDistribution` with its Fourier transform,
   `Lp.fourierTransformₗᵢ` (Plancherel), `Integrable.fourierInv_fourier_eq` and `ZMod.dft`, so the
   chapter is planned in §13. What Mathlib does lack, and what really blocks Ch. 7, 10 and 13–14,
   is a weak derivative on an open set: see §14.

Choi's thesis is the natural fourth book (phase 2): it fits the same spine (singular systems,
MINRES-QLP, norm estimates) but is implementation-heavy and less theorem-dense than
Atkinson–Han, and it would leave the Banach-space layer untested if taken earlier.

### 0.3 Definition of done for phase 1

The backbone modules listed as phase 1 in §7 proved without `sorry`; surface libraries
`SaadSparse`, `FongSaunders`, `AtkinsonHan` with chapter files for the ranges above, each
theorem proved by specializing the backbone (with equivalence lemmas for book-specific
definitions), following the surface plans in ``.

---

## 1. Design principles and conventions

### 1.1 The generality ladder

Every item is placed on the lowest rung (most general) at which its proof works; more concrete rungs
instantiate it. This is the "interfaces over implementations" rule from the README.

| Rung | Setting | Typical content |
|---|---|---|
| L0 algebraic | `Module.End R M`, `R` a commutative ring or field | Krylov subspaces, polynomial evaluation `p(A)v`, invariance, grade |
| L1 inner product | `[RCLike 𝕜] [InnerProductSpace 𝕜 E]`, **no completeness**, `A : E →ₗ[𝕜] E` (bounded when needed) | Petrov–Galerkin specs, minimal residual / Galerkin optimality, Arnoldi/Lanczos relations, CG/CR recurrences and invariants, FOM–GMRES relations, monotonicity, Chebyshev bounds via the compression trick |
| L2 Banach/Hilbert | `[CompleteSpace E]`, `E →L[𝕜] E`, normed rings/algebras | Neumann series, perturbation of inverses, condition numbers, spectral radius and stationary iterations, Lax–Milgram, Céa, Banach fixed point, Newton |
| L3 finite-dimensional | `[FiniteDimensional 𝕜 E]` | termination, spectral theorem for symmetric operators (eigenvalue bounds ⇔ quadratic-form bounds), Bauer–Fike, Courant–Fischer, Faber–Manteuffel, the Fong–Saunders sign arguments |
| L4 matrices | `Matrix n n 𝕜` with a basis / an order on `n` | splittings `A = D − E − F`, Jacobi/GS/SOR, diagonal dominance, Gershgorin, M-matrices, Hessenberg/tridiagonal parts, Property A |

Rules of thumb:

* Krylov and projection theory needs only L1: the search spaces are finite-dimensional, so
  orthogonal projections exist (`Submodule.HasOrthogonalProjection` holds for finite-dimensional
  submodules) without completeness of `E`. Those results are stated for `A : E →ₗ[𝕜] E`;
  `E →L[𝕜] E` is used exactly where `‖A‖`, the spectral radius or completeness enter, and the
  finite-dimensional surface coerces between the two.
* "Positive definite" means two different things in the corpus. Saad's real "positive definite"
  (`(Au,u) > 0`, no symmetry) and Atkinson–Han's "strongly monotone/V-elliptic" are both
  **coercivity** `re ⟪A x, x⟫ ≥ c ‖x‖²`; SPD/HPD is coercive + symmetric. In finite dimension
  coercive ⇔ positive definite; in infinite dimension coercivity is the right hypothesis (it is what
  makes `A⁻¹` bounded and the energy norm equivalent to the norm). The backbone uses
  `LinearMap.IsCoerciveWith`, `LinearMap.IsCoercive` and `LinearMap.IsSymmetricCoercive` (2.1.4)
  and proves the finite-dimensional bridges to `Matrix.PosDef`
  (`Matrix.posDef_iff_isSymmetricCoercive`) and `LinearMap.IsPositive`.
* Spectral hypotheses are quadratic-form bounds. "The spectrum of `A` lies in `[λmin, λmax]`" is
  `LinearMap.IsSymmetricBoundedBy A lmin lmax` (symmetric with
  `lmin ‖x‖² ≤ re ⟪A x, x⟫ ≤ lmax ‖x‖²`), stated in any inner product space; it is the hypothesis
  of every Chebyshev-type bound (Kantorovich, Saad Thm 5.9/6.29, AH Thm 5.6.1, the Lanczos bound
  `α_j ∈ [λmin, λmax]`, Bendixson). It passes to compressions, which is how the bounds are proved
  without a functional calculus (3.9). Bridges: eigenvalue form in finite dimension
  (`LinearMap.IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue`), `±‖A‖` for bounded
  symmetric operators (`isSymmetricBoundedBy_neg_norm_norm`), and Mathlib's Hermitian-matrix
  eigenvalues (`Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin`, 2.1.14).
* Real vs complex: everything is stated over `RCLike 𝕜` with `RCLike.re` where the books take
  real parts (Saad §6.5.9, Choi §1.2, Fong–Saunders with `Re`); eigenvalue statements compare
  `RCLike.re μ` with real intervals, and `open scoped ComplexOrder` is used wherever
  `Matrix.PosDef` appears. The backbone offers no real `abbrev`s: the real surfaces state real
  theorems and strip the decorations through `_real` lemmas (`SesqForm.isCoerciveWith_real_iff`,
  `SesqForm.isHermitian_real_iff`, 5.2.1). Spectral radius and "powers tend to zero" are stated
  for complex Banach algebras (Gelfand's formula is only in Mathlib over `ℂ`); `spectralRadius ℝ`
  is never used for convergence (the real rotation matrix has empty real spectrum but its powers
  do not tend to `0`), and real matrices go through `Matrix.complexify` and
  `Matrix.complexSpectralRadius` (2.1.11). Real Banach spaces beyond matrices are out of scope
  until Mathlib has complexification of operators.
* Finite termination (`x_ℓ = x`) is used by the Fong–Saunders sign arguments and by Choi's rank
  lemmas; those are stated at L3. Everything that only uses nesting of subspaces and orthogonal
  projections is stated at L1.

### 1.2 Specifications versus implementations

Following the README, the *canonical* objects are Prop-valued specifications quantified over an
arbitrary iterate or sequence of iterates, e.g. `IsMinRes A b x₀ K x` ("`x ∈ x₀ + K` minimizes
`‖b − A x‖`"). Theorems about "MINRES" are theorems about any `x : ℕ → E` with
`∀ k, Krylov.IsMinResIterate A b x₀ k (x k)`; MINRES, CR, GMRES, MINRES-QLP (on nonsingular
systems) all satisfy it. This has three benefits: the Lanczos/Givens machinery becomes a
*transport* layer (Choi's "same method, different implementations"), Fong–Saunders' transfer "CR
results ⇒ MINRES results" becomes literally a specialization, and the surface only needs to prove
"my book's algorithm satisfies the spec". Restarted methods satisfy the per-cycle specification
`∀ k, IsMinResIterate A b (x k) m (x (k+1))`, so Saad Thm 6.30 is a backbone theorem
(`Krylov.restarted_minRes_tendsto`, 3.10); truncated methods (IOM, DIOM, DQGMRES, ORTHOMIN(k))
satisfy no global specification and are algorithm-only surface material, stated through
`Krylov.HessenbergRelation` (3.5).

Concrete recurrences go into the backbone only when at least two sources use them in identical
form: Hestenes–Stiefel CG (Saad Alg. 6.18, AH (5.6.2)/§9.4, Fong–Saunders Table 2.1, Meurant–Strakoš
(3.2), Choi Table 2.7), Stiefel CR (Saad Alg. 6.20, Fong–Saunders Table 2.1, Choi Table 2.12), the
Lanczos three-term recurrence (all Krylov sources), and the Givens QR of a Hessenberg/tridiagonal
matrix (Saad §6.5.3, Choi §2.2.3, Fong–Saunders §4.2). Everything else (IOM/DIOM, DQGMRES,
Householder GMRES, SYMMLQ's LQ, MINRES-QLP's QLP, restarts) is surface material until a second book
needs it.

### 1.3 Hypothesis bundles (named interfaces)

| Name | Meaning | Used by |
|---|---|---|
| `LinearMap.IsCoerciveWith A c` | `∀ x, c‖x‖² ≤ re⟪A x, x⟫` | explicit constants: Saad Thm 5.10/6.30, Hilbert-space inverse bound, energy-norm equivalence |
| `LinearMap.IsCoercive A` | `∃ c > 0, A.IsCoerciveWith c` | Saad PD, AH strongly monotone; Galerkin well-posedness (Saad Prop 5.1) |
| `LinearMap.IsSymmetricCoercive A` | `isSymmetric : A.IsSymmetric`, `isCoercive : A.IsCoercive` | SPD/HPD: energy norm, CG, SD, Fong–Saunders |
| `LinearMap.IsSymmetricBoundedBy A lmin lmax` | symmetric, `lmin‖x‖² ≤ re⟪A x, x⟫ ≤ lmax‖x‖²` | Kantorovich, Saad Thm 5.9/6.29, AH 5.6.1, Lanczos `α_j`, Bendixson |
| `WithEnergy A hA` | type synonym of `E` carrying the inner product `⟪A x, y⟫` | A-orthogonal projections (Saad Prop 5.5), Galerkin = orthogonal projection in the energy norm |
| `Stationary.Splitting a` | `m` with `IsUnit m`, `n := m − a` | Jacobi/GS/SOR/SSOR/Richardson, regular splittings |
| `Krylov.HessenbergRelation A v h` | `A v_j = ∑_{i ≤ j+1} h_ij v_i`, `h` upper Hessenberg | FOM/GMRES residual formulas for any basis; IOM/DIOM/DQGMRES/QMR |
| `SesqForm.IsCoerciveWith a c`, `SesqForm.IsHermitian a`, `SesqForm₂.InfSupWith a α` | bounded forms `V →L⋆[𝕜] V →L[𝕜] 𝕜` | Lax–Milgram, Céa, Babuška–Nečas |
| `FloatingPoint.RoundingModel K` | abstract arithmetic with relative error `u` (relational) | floating-point layer (reserved, §6) |

Mathlib bundles reused as is: `LinearMap.IsSymmetric`, `IsSelfAdjoint`, `LinearMap.IsPositive`,
`Matrix.PosDef`, `Matrix.IsHermitian`, `ContractingWith`, `IsCoercive` (real bilinear forms),
`Submodule.HasOrthogonalProjection`, `IsCompactOperator`, `ContinuousLinearMap.IsFredholm`.

### 1.4 Naming and namespaces

* No global `Numlib` namespace. Mathlib-style extensions use the Mathlib namespace of the type they
  extend (`LinearMap.IsCoercive`, `Matrix.IsUpperHessenberg`, `NormedRing.condNumber`), so that dot
  notation and future upstreaming work. Numerical-analysis-specific theories use short topical
  namespaces: `Krylov`, `Arnoldi`, `Lanczos`, `CG`, `CR`, `Stationary`, `Projection`, `SesqForm`,
  `Newton`, `FloatingPoint`.
* Specifications are `Is…` predicates (`IsPetrovGalerkin`, `IsGalerkin`, `IsMinRes`, `IsMinError`,
  `Krylov.IsMinResIterate`, `Krylov.IsGalerkinIterate`, `Krylov.IsMinErrorIterate`,
  `IsGalerkinSolution`, `IsBestApprox`).
* Scoped notation: `𝒦[A, v] m` for `Krylov.subspace A v m` (scoped in `Krylov`); `⟪x, y⟫_[A]` /
  `‖x‖_[A]` for the energy inner product and norm (scoped in `Energy`); `κ a` for the condition
  number (scoped in `NormedRing`).
* Book numbering appears only in docstrings and in the surface (`SaadSparse.Ch06.prop_6_5`), never
  in backbone names.
* One theorem per statement, Mathlib naming conventions (`norm_residual_le`,
  `spectralRadius_lt_one_iff_tendsto_pow`); `⨅`-statements are the primary form of min–max
  results, with `IsLeast` forms added as corollaries when a consumer needs them.

### 1.5 Repository layout

```
Numlib.lean                     -- imports all backbone modules
Numlib/                         -- backbone (this plan, §2–§6)
  Analysis/Normed/…             -- upstreaming candidates: Neumann-series bounds, κ, spectral radius
  Analysis/InnerProductSpace/…  -- upstreaming candidates: coercivity, energy norm, compression,
                                --   Gram–Schmidt flags, oblique projections
  Analysis/Matrix/…             -- upstreaming candidate: matrices as operators on EuclideanSpace
  LinearAlgebra/Matrix/…        -- upstreaming candidates: Hessenberg parts, complexification
  RingTheory/Polynomial/…       -- upstreaming candidate: Chebyshev min–max
  LinearSolve/…                 -- perturbation, stationary, projection methods
  Krylov/…                      -- Krylov subspaces and methods
  Eigen/…                       -- eigenvalue perturbation and projection methods
  Approximation/…               -- best approximation, Chebyshev, interpolation, quadrature
  Variational/…                 -- forms, Lax–Milgram, Galerkin
  Nonlinear/…                   -- fixed point, Newton
  IntegralEquations/…           -- integral operators on C[a,b] (phase 3)
  FloatingPoint/…               -- reserved (phase 4)
NumlibSurface/                  -- the second Lake library, one directory per book
  SaadSparse/ChapterNN/SectionNN.lean
  FongSaunders/SectionN.lean
  AtkinsonHan/ChapterNN/SectionNN.lean
plans/                        -- the plan: a copy of both trees, `.lean` replaced by `.toml`
  backbone.md                   -- this file
  <book>.md                     -- per-book surface alignment
```

Upstreaming candidates are not segregated into a separate directory: they live in the topical
folders `Analysis/`, `InnerProductSpace/`, `Matrix/`, `Polynomial/` mirroring Mathlib's own tree,
each module starting with a comment "Upstreaming candidate … natural home: `Mathlib.…`", written
in Mathlib conventions and free of dependencies on the numerical-analysis layers. The
numerical-analysis layers use them only through their Mathlib-style names.

`lakefile.toml` registers two libraries, both default targets: `Numlib`, the backbone, and
`NumlibSurface`, holding every book's surface. The books share one library rather than getting one
each, because they share vocabulary — `NumlibSurface.SaadSparse.Common` and the like — and a
library boundary between them would have to be paid for in duplication. The boundary that earns its
keep is the one between the layers: `NumlibSurface` imports `Numlib`, and Lake makes the reverse
impossible rather than merely discouraged.

### 1.6 Mathlib reuse table (Mathlib `v4.34.0-rc2`, the pinned version)

| Concept | Mathlib name(s) | Use |
|---|---|---|
| Orthogonal projection onto a submodule | `Submodule.starProjection`, `Submodule.orthogonalProjectionOnto`, `starProjection_minimal`, `sub_starProjection_mem_orthogonal`, `starProjection_norm_le` | reuse; instance `HasOrthogonalProjection` for finite-dimensional `K` |
| Projection onto closed convex sets | `exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero` | reuse (AH 3.4.1–3.4.3) |
| Gram–Schmidt | `InnerProductSpace.gramSchmidtNormed`, `gramSchmidtNormed_orthonormal'`, `span_gramSchmidt_Iic` | Arnoldi vectors are literally `gramSchmidtNormed` of the Krylov sequence |
| Symmetric operators, spectral theorem | `LinearMap.IsSymmetric`, `LinearMap.IsSymmetric.eigenvectorBasis`, `.eigenvalues`, `IsSelfAdjoint`, `LinearMap.IsPositive` | reuse for the L3 polynomial bounds (3.9) and the eigenvalue bridges of 2.1.4 |
| Rayleigh quotient | `ContinuousLinearMap.rayleighQuotient`, `hasEigenvalue_iSup_of_finiteDimensional`, `spectralRadius_eq_nnnorm` | reuse; Courant–Fischer is missing (4.2) |
| Hermitian matrices | `Matrix.IsHermitian.eigenvalues`, `eigenvectorBasis`, `spectral_theorem`, `Matrix.PosDef`, `PosDef.eigenvalues_pos` | bridge lemmas to `LinearMap.IsSymmetricCoercive` / `IsSymmetricBoundedBy` (2.1.4, 2.1.14) |
| Neumann series / units | `Units.oneSub`, `Units.ofNearby`, `Units.add`, `NormedRing.inverse_one_sub`, `NormedRing.tsum_geometric_of_norm_lt_one`, `inverse_add_norm_diff_first_order`, `ContinuousLinearEquiv.isOpen` | qualitative parts; the explicit constants (AH (2.3.13)–(2.3.15)) are 2.1.1 |
| Spectral radius, Gelfand | `spectralRadius`, `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` (ℂ), `spectrum.spectralRadius_pow_le`, `spectrum.subset_closedBall_norm` | reuse; "`ρ<1 ↔ aⁿ→0`" is 2.1.3 |
| Matrix norms | scoped `Matrix.Norms.L2Operator` (`l2_opNorm_def`, `l2_opNorm_conjTranspose_mul_self`), `Matrix.Norms.Operator` (`linfty_opNorm_*`), `Matrix.Norms.Frobenius` | reuse; equivalence constants (Higham Table 6.2) are phase 4 |
| Gershgorin, diagonal dominance | `eigenvalue_mem_ball`, `Matrix.det_ne_zero_of_sum_row_lt_diag` | reuse (2.3.3, 4.1) |
| Chebyshev polynomials | `Polynomial.Chebyshev.T`, `abs_eval_T_real_le_one`, `leadingCoeff_le_of_forall_abs_le_one`, `eval_iterate_derivative_le_of_forall_abs_le_one`, `roots_T_real`, Chebyshev–Gauss quadrature | min–max on `[a,b]` with `p(γ)=1` is 2.1.9 |
| Lagrange interpolation | `Lagrange.interpolate`, `Lagrange.basis` | reuse for the interpolation branch (5.1.3) |
| Banach fixed point | `ContractingWith.fixedPoint`, `apriori_dist_iterate_fixedPoint_le`, `aposteriori_dist_iterate_fixedPoint_le`, `dist_fixedPoint_fixedPoint_of_dist_le'` | reuse (AH 5.1.3) |
| Lax–Milgram (real) | `IsCoercive`, `IsCoercive.continuousLinearEquivOfBilin` | the `RCLike` version is 5.2.2 |
| Compact operators, Fredholm | `IsCompactOperator`, `IsCompactOperator.hasEigenvalue_or_mem_resolventSet`, `ContinuousLinearMap.IsFredholm` | reuse for the AH §2.8 surface |
| Singular values, LDL | `LinearMap.singularValues`, `Matrix.LDL.lower_conj_diag` | reuse (Choi, Kress §5.2) |
| Picard–Lindelöf, Gronwall | `IsPicardLindelof`, `norm_le_gronwallBound_of_norm_deriv_right_le` | reuse (AH 5.2.4, Kress 10.1) |
| Weierstrass | `polynomialFunctions_closure_eq_top`, `exists_polynomial_near_continuousMap` | reuse (AH 2.4.4 quadrature convergence) |
| Polynomials in an endomorphism | `Polynomial.aeval`, `Module.AEval'`, `Polynomial.degreeLT`, `minpoly` | Krylov subspaces; `Module.AEval'` gives the cyclic-module view |
| Subspace dimension counting | `Submodule.finrank_sup_add_finrank_inf_eq` | Courant–Fischer (4.2) |
| Closed range | `ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective` | Lax–Milgram, AH §8.2 (5.2.2) |
| Floating point | `Mathlib/Data/FP/Basic.lean` (definitions only, no theorems) | not usable; third-party Lean libraries listed in §6 |

Absent from Mathlib (so backbone content): Krylov subspaces, Arnoldi/Lanczos, condition number,
explicit Neumann-series perturbation bounds, `ρ<1 ↔ Gᵏ→0`, Courant–Fischer, Bauer–Fike, Kantorovich
inequality, Chebyshev min–max on an interval, Céa/Petrov–Galerkin/inf–sup, complex Lax–Milgram,
Newton's local convergence and Kantorovich's theorem, Jordan form, Schur form, Perron–Frobenius
(only irreducibility is there), orthogonal polynomials beyond Chebyshev, Gauss quadrature,
Hessenberg matrices and Givens QR, the gap metric between subspaces, the `γ_n` calculus.

### 1.7 Design decisions

Decisions that cut across sections, stated once here:

* **Operator type.** `E →ₗ[𝕜] E` at L0/L1 (projection and Krylov layers), `E →L[𝕜] E` where
  norms, spectral radius or completeness enter (2.1.1–2.1.3, 2.2, 2.3.1, 5.2, 5.3); statements at
  the boundary take `A : E →L[𝕜] E` and coerce (`(A : E →ₗ[𝕜] E).IsCoerciveWith c`).
* **Energy structures are operator-based.** `WithEnergy A hA` takes `A : E →ₗ[𝕜] E` with
  `A.IsSymmetricCoercive` (2.1.5); bounded forms reach it through `SesqForm.toOperator` on Hilbert
  spaces (5.2.1). A form-based energy space for non-complete `V` is deferred to the finite-element
  phase; when it is added, the operator version becomes its instance.
* **No `Fact` instances and no `ℕ∞`-valued grade.** `Krylov.grade` is `Module.finrank` of the
  cyclic subspace with the hypothesis `[FiniteDimensional K (fullSubspace A v)]` (3.1).
* **Explicit targets.** `IsMinError xstar x₀ K x` names the target `xstar` rather than an
  operator, so minimal-error iterates exist for singular `A` (2.4.1, 3.4).
* **One-directional spectral-radius statements outside finite dimension.** `ρ(G) < 1 ⇒`
  convergence holds in every complex Banach space; the converse only in finite dimension (2.3.1).
* **Givens rotations are `ℕ`-indexed** recursions on the infinite coefficient function, so prefix
  stability across `m` is automatic; `Fin`-matrices are built at the end (3.5).
* **Floating point is relational** (`FloatingPoint.RoundingModel`, §6), phase 4.
* **Out of scope** (no Mathlib support, not planned): the Banach closed range theorem (unbounded
  Banach adjoints), Sobolev spaces on a domain and FEM, nonlinear CG (AH Algorithm 2), analytic
  perturbation theory via contour integrals of operator-valued functions. *Amended (§13, §14):*
  "distribution theory" used to be on this list and is not any more — Mathlib has tempered
  distributions with their Fourier transform. The Sobolev entry means `W^{k,p}(Ω)` for an open
  `Ω ⊆ ℝⁿ`, built from a weak derivative; Mathlib's `TemperedDistribution.MemSobolev` is the
  Bessel-potential space on all of `ℝⁿ` and is not a substitute. The *periodic* spaces `H^s(2π)`
  of AH §7.5 are a weighted `ℓ²` over the `AddCircle` Fourier basis and need none of it.

---

## 2. Tree of contents, part I: normed-space, stationary and projection layers

Items are listed in logical progression order (each item only depends on earlier items or on
Mathlib). Each item names its module, the books it serves, the key Lean statements, and any
difficult proof. Rung labels (L0–L4) refer to §1.1. Phases refer to §7.

### 2.1 Mathlib-shaped upstreaming candidates

These are stated in Mathlib's own vocabulary so that they can be upstreamed, and each one names
its natural home in Mathlib in a comment at the top of the module. Their paths mirror Mathlib's
own: a module destined for `Mathlib.Analysis.InnerProductSpace.Positive` sits in
`Numlib/Analysis/InnerProductSpace/`, one destined for the directory
`Mathlib.Analysis.InnerProductSpace.Projection` sits in
`Numlib/Analysis/InnerProductSpace/Projection/`, and so on (§1.5). The numerical-analysis layers
below use them only through their Mathlib-style names.

#### 2.1.1 `Analysis/Normed/Ring/Inverse.lean` (L2) — explicit Neumann-series and perturbation bounds
Serves AH Thm 2.3.1, Cor 2.3.3, Thm 2.3.5 (bounds (2.3.13)–(2.3.16)), Saad §1.13, Kress Thm 3.48
(Neumann series with a priori/a posteriori bounds), Saad-eig (3.14)/Prop 3.2 (resolvent Neumann
expansion), Higham Thm 7.2. Mathlib has the qualitative facts (`Units.oneSub`, `Units.ofNearby`,
`ContinuousLinearEquiv.isOpen`) but not the constants.

Proofs: the first bound is a corollary of `NormedRing.tsum_geometric_of_norm_lt_one`; factor
`x + t = x (1 + x⁻¹ t)` and apply the `1 − t` bounds; the two-space version needs `L⁻¹` on the
complete side. Nothing difficult.

#### 2.1.2 `Analysis/Normed/Ring/CondNumber.lean` (L2)
Serves Saad §1.13, AH §2.4.3, Kress §5.1, Higham Ch. 6–7, Choi §2.4.5.

Matrix versions are the same definition under the scoped norm instances
(`open scoped Matrix.Norms.L2Operator` gives `κ₂`, `Matrix.Norms.Operator` gives `κ_∞`).
`Matrix.condNumber_l2_eq_div_singularValues` (L3, `κ₂ = σ_max/σ_min` via
`LinearMap.singularValues`) is phase 2; Saad Example 1.5 (`κ_∞(I + α e₁ eₙᵀ) = (1+|α|)²`) is
surface.

#### 2.1.3 `Analysis/Normed/Algebra/SpectralRadius.lean` (L2, complex; L4 real matrices)
Serves Saad Thm 1.10–1.12, 4.1; Kress §5.2.2/AH §5.2.2; Higham Ch. 18.

Difficult proof (moderate): `⇒` picks `ρ < r < 1`, uses
`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` to get `‖aⁿ‖ ≤ rⁿ` eventually;
`⇐` uses `spectrum.spectralRadius_pow_le` and `spectralRadius_le_nnnorm`:
`ρ(a)ⁿ ≤ ρ(aⁿ) ≤ ‖aⁿ‖ → 0`. The bookkeeping is in `ENNReal`/`NNReal`; keep a real-valued
helper if it gets painful. No Jordan form is needed anywhere (Saad's proofs via Jordan form are
replaced by Gelfand).

Real matrices: `spectralRadius ℝ A` is *not* the spectral radius (the rotation
`![![0, -1], ![1, 0]]` has empty real spectrum, so `spectralRadius ℝ` of it is `0` although its
powers do not tend to `0`). Every statement about the spectral radius of a real matrix is made
with `Matrix.complexSpectralRadius A := spectralRadius ℂ (Matrix.complexify A)` (2.1.11) and
proved by transporting the complex results through `complexify`.

#### 2.1.4 `Analysis/InnerProductSpace/Coercive.lean` (L1/L2/L3)
Serves Saad §1.11 (Thm 1.34), §1.8.3 (Hermitian part), Prop 5.1, Thm 5.10, 6.30; AH 5.1.4
(linear case), 8.3, 9.4; Kress Thm 3.29, 4.12.

The Hilbert-space inverse bound is the linear case of AH Thm 5.1.4; prove it directly from
Mathlib's real Lax–Milgram applied to the real part of `⟪A x, y⟫` (see 5.2.2 for the trick that
also gives the complex Lax–Milgram), or via closed range: `‖A x‖ ≥ c‖x‖` ⇒ closed range, coercivity
⇒ `range ᗮ = ⊥`.

#### 2.1.5 `Analysis/InnerProductSpace/Energy.lean` (L1)
Serves Saad Prop 5.2, 5.5, Thm 5.9, Lemma 6.28, PCG; AH §5.6, §9.4; Fong–Saunders; Meurant §3.

Construction of `WithEnergy` (Mathlib's `Matrix.toInnerProductSpace` pattern): the plain
`AddCommGroup`/`Module` instances are *local* to the section that defines the
`InnerProductSpace.Core`; only the core-derived normed instances are global, which avoids an
`AddCommMonoid` diamond between the two; `WithEnergy.equiv` is defined afterwards with `rfl`
fields, so `inner_equiv`/`norm_equiv` are `rfl`. Only `A : E →ₗ[𝕜] E` and `IsSymmetricCoercive`
are needed for the instance; `continuous_equiv` needs `A` bounded, and completeness of
`WithEnergy` follows from the norm equivalence when `E` is complete and `A` bounded. With this,
Saad Prop 5.5 ("the Galerkin error is `(I − P^A_K) d₀`") is `starProjection` in `WithEnergy`
(`IsGalerkin.error_eq_starProjection`, 2.4.2), and Céa with constant 1 (5.2.3) is
`starProjection_minimal` there.

#### 2.1.6 `Analysis/InnerProductSpace/Projection/Compression.lean` (L1)
Serves Saad Prop 6.3, 6.5 (`V_mᴴ A V_m = H_m`), Saad-eig Ch. 4 (Rayleigh–Ritz), Meurant §2, and
the compression trick of 3.9.

The lemmas that make the compression the carrier of Chebyshev bounds in any inner product space
(`compression.isSymmetricBoundedBy`, `isSymmetricCoercive`, `energyInner_apply`,
`energyNorm_apply`) live in `Krylov/Convergence/Polynomial.lean` (3.9).

#### 2.1.7 `Analysis/InnerProductSpace/Projection/ObliqueProjection.lean` (L1; Kato L2)
Serves Saad §1.12 (Lemma 1.36, Prop 1.37, (1.39)–(1.44)), Saad-eig §3.1, Saad §5.2.2 (`Q_K^L`),
AH Rem 9.2.2 (Xu–Zikatanov). Mathlib has `LinearMap.IsSymmetricProjection` and
`IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker` (= Saad Prop 1.37).

Kato's lemma looked like the deep item of this module and is not: it needs neither the minimal-gap
characterisation `1/‖P‖² = 1 − ‖P_N P_M‖²`, nor the symmetry `‖P_M P_N‖ = ‖P_N P_M‖`, nor adjoints,
nor completeness, so both of this module's bounded-operator theorems sit at L1 rather than L2. The proof is the exchange trick.
Decompose `x = u + v` with `u = P x`, `v = (1 − P) x`, and feed `1 − P` the rescaled vector
`(‖v‖/‖u‖) • u + (‖u‖/‖v‖) • v`: the two scalars multiply to `1`, so the cross term
`2 re ⟪u, v⟫` survives untouched while the two squared norms are exchanged, and the rescaled vector
still has norm `‖x‖` (`norm_smul_add_smul_eq_norm_add`). Since `1 − P` kills `u` and fixes `v`, its
value there has norm exactly `‖P x‖`, giving `‖P‖ ≤ ‖1 − P‖`; the reverse inequality is the same
statement for `1 − P`. The degenerate `x` (either component zero) fall to `1 ≤ ‖1 − P‖`.
What does *not* work, for the record: `T := P + P⋆ − 1` satisfies
`T² = P P⋆ + Q⋆Q = P⋆P + Q Q⋆` with `Q = 1 − P`, and in each decomposition the two positive
summands annihilate each other, so `‖T‖² = max(‖P‖², ‖Q‖²)` and `‖P‖, ‖Q‖ ≤ ‖T‖` — inequalities,
not the equality. The unrescaled estimate `‖Q x‖ ≤ ‖P‖‖x‖` closes into a circular identity.

#### 2.1.8 Polynomial glue (L0; in `Krylov/Subspace.lean` and `Krylov/Iterate.lean`)
Glue between `Polynomial.degreeLT`, `Polynomial.aeval` at an endomorphism and spans of iterates;
it lives next to the Krylov subspaces rather than in a separate module.

#### 2.1.9 `RingTheory/Polynomial/ChebyshevMinimax.lean` (analysis)
Serves Saad Thm 6.25/6.29, AH (5.6.5), Meurant (3.9), Saad-eig Thm 4.8, Ch. 6 (Kaniel–Paige–Saad).

The general-`γ` version is the primary statement (the eigenvalue book needs it) and `γ = 0` is
derived. Difficult proof (moderate): Mathlib's `eval_iterate_derivative_le_of_forall_abs_le_one`
(k = 0) says `|P| ≤ 1` on `[−1,1]` ⇒ `P(x) ≤ T_m(x)` for `x ≥ 1`. Compose `p` with the affine map
`t ↦ (b + a − 2t)/(b − a)` (so `[a,b] ↦ [−1,1]`), rescale by the sup, and replace `p` by
`q.comp (-X)` when the image of `γ` is `≤ −1`, which avoids a separate parity argument. Degree
bookkeeping for `Polynomial.comp` and `sSup` of a continuous image of a compact interval are the
only frictions. The complex ellipse results (Saad Lemma 6.26, Thm 6.27, Cor 6.33) are phase 3.

#### 2.1.10 `LinearAlgebra/Matrix/Hessenberg.lean` (L4)
Serves Saad §4.1 (`A = D − E − F`), §6.3–6.5, Choi §2.2, Fong–Saunders §4.2, Kress §7.5.

Only predicates and triangular parts are matrix-level; the Givens QR of the Hessenberg
coefficients is `ℕ`-indexed and lives with the Krylov transport layer (3.5). Keep this minimal —
no general QR theory.

#### 2.1.11 `LinearAlgebra/Matrix/Complexify.lean` (L4)
Serves every real-matrix statement about spectral radii (Saad Thm 1.10–1.12, 4.1; Kress Thm 4.1).

The norm must be passed as a *function*. Stating the bound with `[NormedRing (Matrix n n ℝ)]` and
friends makes it **false**, and the reason is not that class arguments quantify — they always do,
on concrete and variable types alike — but that this statement then mixes two unrelated structures
on one type: `NormedRing` bundles its own `Ring`, which need not be `Matrix.instRing`, while
`complexSpectralRadius A` is computed from the canonical one. Only a concrete type can go wrong
this way, since only there is a canonical instance lying around for the rest of the statement to
pick up. Transporting `ℝ`'s normed-field structure along any bijection
`Matrix n n ℝ ≃ ℝ` that fixes `1` satisfies all three classes at once — `NormedAlgebra ℝ` does not
rule this out, since `ℝ` is an `ℝ`-algebra — while leaving `‖·‖` unrelated to
`complexSpectralRadius`, which is computed from the canonical structures. Concretely one gets
`‖A‖ = 0` with `ρ(A) = 2`.

The three hypotheses on `f` are exactly what the proof needs and none is removable.
Submultiplicativity and homogeneity turn the matrix-unit identity
`single i i 1 * B * single j j 1 = B i j • single i j 1` into a uniform entrywise bound
`‖B i j‖ ≤ c * f B`, where positive definiteness is what makes the constant finite; the powers of
`t⁻¹ • A` then decay entrywise for `f A < t`, so `ρ(t⁻¹ • A) < 1` by
`tendsto_pow_iff_complexSpectralRadius_lt_one` and `complexSpectralRadius_smul` undoes the scaling.
Subadditivity is never used. Positive definiteness cannot be dropped: `B ↦ |det B|^(1/2)` on
two-by-two matrices is submultiplicative and absolutely homogeneous with `f 1 = 1`, and kills
`!![1,0;0,0]`, whose spectral radius is `1`. Norm preservation under `complexify` for the scoped
`l∞`/Frobenius norms is added when a surface statement needs it (phase 2).

#### 2.1.12 `LinearAlgebra/Matrix/Order.lean` (L4, phase 2)
Entrywise order and absolute value (`|A| ≤ |B|`, `|A * B| ≤ |A| * |B|`, monotonicity of products by
nonnegative matrices; Saad Prop 1.24/1.26, Higham §3.5). Watch out: Mathlib's `Matrix` order
instance in `Analysis/Matrix/Order.lean` is the *Loewner* order; the entrywise order must be a
scoped instance or go through `Matrix.of`/`Pi`. Needed by regular splittings (2.3.4) and by the
floating-point layer (§6). Plan: `Numlib/LinearAlgebra/Matrix/Order.toml`, as a predicate
`Matrix.EntrywiseLE` with scoped notation rather than an instance.

#### 2.1.13 `Analysis/InnerProductSpace/GramSchmidt.lean` (L1) — uniqueness of orthonormal bases of a flag
Serves Saad §6.3.2 (MGS and Householder Arnoldi agree with Alg 6.1 up to signs), P-6.1(f), Choi
and Fong–Saunders' identifications of Lanczos with CG/CR quantities, and block variants.

The normalization is `0 < ⟪u_j, f_j⟫` in the `ComplexOrder` sense: the inner product is a positive
*real*, not merely of positive real part. Over `ℝ` this is the same hypothesis; over `ℂ` positivity
of the real part is not enough, since it leaves the phase of `u_j` free.

#### 2.1.14 `Analysis/Matrix/ToEuclideanLin.lean` (L4) — matrices as operators on `EuclideanSpace`
The glue every matrix-level surface statement uses to reach the operator-level backbone.
Symmetric ↔ Hermitian is Mathlib's `Matrix.isSymmetric_toEuclideanLin_iff`; `Matrix.PosDef` ↔
symmetric coercive is `Matrix.posDef_iff_isSymmetricCoercive` (2.1.4).

The Euclidean isometry of unitary matrices, `‖U *ᵥ v‖₂ = ‖v‖₂` for `U ∈ Matrix.unitaryGroup`,
belongs in this module too: Mathlib has the unitary group but no `mulVec` isometry, and the Givens
residual identities of 3.5 are blocked on it. Route: `Matrix.toEuclideanCLM` and the fact that a
unitary element of a C⋆-algebra is an isometry.

### 2.2 `Numlib/LinearSolve/Perturbation.lean` (L2)
Serves Saad §1.13.2, AH §2.4.3 ((2.4.1) `cond(L)`), Kress Def 5.2/Thm 5.3 (stated for Banach
spaces), Higham Thm 7.1–7.2, Choi Thm 2.34, Fong–Saunders §3.

Proof of Rigal–Gaches: `(A + ΔA) y − b − Δb = 0` gives `‖r‖ ≤ ‖ΔA‖‖y‖ + ‖Δb‖`; the minimizer is
`ΔA = ((1−ω)/‖y‖²) r ⊗ y`, `Δb = −ω r` (rank one, so its operator norm equals `‖r‖/‖y‖`).
Stated in inner product spaces (rank-one operators via `inner`); the Banach version would use
`exists_dual_vector`. Componentwise theory (Oettli–Prager, Skeel) is phase 4 with Higham.

### 2.3 `Numlib/LinearSolve/Stationary/`

#### 2.3.1 `Stationary/Basic.lean` (L2, L3)
Serves Saad §4.2.1 (Thm 4.1, Cor 4.2, convergence factor), AH §5.2.2 and Ex 2.3.8/2.3.10,
Kress Thm 3.48 (a priori/a posteriori bounds), Thm 4.1 (convergence ⇔ `ρ < 1`), Thm 3.32
(`ρ ≤ ‖·‖`, and `∀ ε ∃` norm with `‖A‖ ≤ ρ + ε` — replaced here by Gelfand), §4.3 defect correction,
Saad-eig §3.5 (3.56)–(3.60), Higham Ch. 17 exact part.

The sharp form of the convergence factor (`limsup ‖G^k d‖^{1/k} = ρ(G)` for the worst `d`) is a
phase-2 sketch. Real spaces: apply to the complexification (matrices via 2.1.11; general real
Banach spaces are out of scope until Mathlib has complexification of operators).

#### 2.3.2 `Stationary/Splitting.lean` (L2 ring-level, L4 constructors)
Serves Saad §4.1 (Jacobi, GS, SOR, SSOR, (4.5)–(4.27)), AH §5.2.2, Kress §4.1–4.2, Higham Ch. 17.

Saad's `A = D − E − F` is `D = diagPart A`, `E = −strictLower A`, `F = −strictUpper A`
(`Matrix.diagPart_sub_neg_strictLower_sub_neg_strictUpper`, 2.1.10); Atkinson–Han's convention
`A = N − M` swaps the roles of the letters, which the surface handles by an equivalence lemma.
Block splittings and the non-overlapping block Jacobi/GS (Saad Alg 4.1–4.2) are phase 2 and
reuse `Projection/Additive.lean`; plan: `Stationary/Block.toml`. Overlapping blocks have no
theorem in the book and are not planned.

#### 2.3.3 `Stationary/DiagDominant.lean` (L4)
Serves Saad Thm 4.6–4.9, Cor 4.8; Kress Thm 4.2 (Jacobi with the explicit constant `q_∞`), Thm 4.3
(Sassenfeld criterion for Gauss–Seidel), Cor 4.4, Problem 4.4 (column dominance); AH Ex 5.2.2.

Proofs: Jacobi via the `‖·‖_∞` operator norm (which also gives Kress's rate) or via Gershgorin
(`eigenvalue_mem_ball`) on `D⁻¹(E+F)`; Gauss–Seidel via Saad's eigenvector argument with the split
sums `σ₁, σ₂`. Irreducibly diagonally dominant matrices (Thm 4.7, second half of 4.9) need
`Matrix.IsIrreducible` (in Mathlib, for nonnegative matrices, hence applied to `A.map ‖·‖`) and are
phase 2, together with Gauss–Seidel under column dominance: the open nodes of
`Stationary/DiagDominant.toml`.

#### 2.3.4 `Stationary/RegularSplitting.lean` (L4, phase 2)
Saad Def 4.3, Thm 4.4, M-matrices (Thm 1.29–1.33). Blocked on Perron–Frobenius (Mathlib only has
`Matrix.IsIrreducible`/`IsPrimitive`). Minimal route: prove the weak Perron theorem for nonnegative
matrices (existence of a nonnegative eigenvector for `ρ(B)`) via `(I − B/r)⁻¹ ≥ 0` for `r > ρ(B)`
and compactness; that suffices for Thm 1.29 and Thm 4.4. Needs 2.1.12. Plan:
`Stationary/RegularSplitting.toml`, with the weak Perron theorem as its own node.

#### 2.3.5 `Stationary/SPD.lean` (L3/L4, phase 2)
Richardson with optimal parameter (Saad Ex 4.1, AH Ex 5.2.3), Jacobi over-relaxation (Kress
Thm 4.9), Kahan's necessary condition `0 < ω < 2` (Kress Thm 4.11: `det G(ω) = (1 − ω)ⁿ`), the
Householder–John / Ostrowski–Reich theorem in operator form — `A` symmetric coercive, `A = M − N`,
`M + Mᴴ − A` coercive ⇒ `ρ(M⁻¹ N) < 1` (Saad Thm 4.10, Kress Thm 4.12 is `M = D/ω + E`; proof by
the Rayleigh-quotient identity for eigenvalues of `M⁻¹N`, as in Kress, or by the energy-norm
contraction), Young's SOR theory (Saad Prop 4.12–Thm 4.16, Kress Def 4.13–Cor 4.16: consistently
ordered ⇒ `ω_opt`, `ρ_GS = ρ_J²`) — matrix-combinatorial, shared by two books, so backbone
(phase 2) but last in priority. Plan: two groups, `Stationary/SPD.toml` (Richardson, JOR, Kahan,
Ostrowski–Reich and its converse) and `Stationary/ConsistentlyOrdered.toml` (Young's theory),
the latter taking Kress's spectral definition of consistent ordering — the property the proofs
use — as primary, with Saad's labelling (Def 4.13) and Property A as sufficient conditions.

### 2.4 `Numlib/LinearSolve/Projection/`

#### 2.4.1 `Projection/Basic.lean` (L1)
Serves Saad §5.1–5.2 (Prop 5.1, 5.3, 5.4, 5.6, (5.7)), §1.12 (Thm 1.38, Cor 1.39 via Mathlib),
Fong–Saunders §2, Choi Table 2.5, AH §9 (bridge in 5.2.3).

Saad Thm 5.7 (`‖b − A_m x*‖ ≤ ‖Q A (1 − P_K)‖ ‖(1 − P_K) x*‖` for the projected operator) is
phase 2 (`IsPetrovGalerkin.norm_residual_projected_le`, open in `Projection/Basic.toml`); its
Galerkin/minimal-residual special cases are covered by 2.4.2.

#### 2.4.2 `Projection/Optimality.lean` (L1)
Serves Saad Prop 5.2, 5.5; Fong–Saunders §2.1–2.2; Choi Table 2.5, §8.3 (CGNE/Craig); AH (5.6.14).

#### 2.4.3 `Projection/OneDimensional.lean` (L1)
Serves Saad §5.3 (Alg 5.2–5.4, Lemma 5.8, Thm 5.9, 5.10), Thm 6.30; AH (5.6.4) one-step rate;
Kress/AH Richardson.

Kantorovich is proved by the compression trick (3.9) from the quadratic-form bounds: compress `A`
to `span {x, y}`, where the spectral theorem and the convexity of `t ↦ 1/t` on the convex hull of
the spectrum apply. RNSD = SD on the normal equations is a one-line corollary once `Aᴴ A` is
symmetric coercive (surface).

#### 2.4.4 `Projection/Additive.lean` (L1, phase 2)
Saad §5.4: additive/multiplicative projection procedures, residual `r_{k+1} = (1 − Σ P_i) r_k`
with `P_i` the projector onto `A K_i` orthogonal to `K_i`; block Jacobi/GS are instances. Plan:
`Projection/Additive.toml` (the step, the projectors, the least-squares option and the exactness
criterion) with the block instances in `Stationary/Block.toml`; the exact one-step identities of
Saad (5.18) and (5.20) are open nodes of `Projection/OneDimensional.toml`.

---

## 3. Tree of contents, part II: the Krylov layer (`Numlib/Krylov/`)

This is the spanning tree shared by Saad (both books), Fong–Saunders, Choi and Meurant–Strakoš, and
by Atkinson–Han §5.6/§9.4. Import order: Subspace → Arnoldi → Lanczos → Iterate → Relations →
Hessenberg → CG, CR → Convergence → Monotonicity → (phase 2–3) Preconditioned, Singular,
OrthogonalPolynomials, BiLanczos. Indices are `0`-based throughout: `Arnoldi.vec A b 0 = b/‖b‖`,
`𝒦[A, v] m = span {v, …, A^(m−1) v}`.

### 3.1 `Krylov/Subspace.lean` (L0, L3)
Serves Saad §6.2 (Prop 6.1, 6.2), Saad-eig §6.1, Choi Def 2.1, Meurant §2.1.

Grade convention: `grade` is `finrank` of the cyclic subspace and the finite-grade hypothesis is
the instance `[FiniteDimensional K (fullSubspace A v)]` (automatic when `V` is finite-dimensional);
`grade_eq_sInf` recovers Saad's definition, `pow_apply_mem_subspace_iff_exists_monic` the
minimal-polynomial one. The minimal polynomial of `v` as a monic generator of its annihilator in
`Module.AEval' A` (with `natDegree = grade`) is phase 2 (`Krylov.minpolyVec`, open in
`Krylov/Subspace.toml`). Operators `A : E →L[𝕜] E` coerce to
`E →ₗ[𝕜] E`; matrices go through `Matrix.krylov_subspace_toEuclideanLin` (2.1.14). Difficult
proof: `linearIndependent_of_le_grade` — a dependence among `v, …, A^{m−1} v` gives the least `j`
with `A^j v ∈ 𝒦_j`, contradicting minimality of the grade; use `linearIndependent_iff'` and
`Submodule.mem_span_range_iff_exists_fun`.

### 3.2 `Krylov/Arnoldi.lean` (L1)
Serves Saad §6.3 (Alg 6.1–6.2, Prop 6.4–6.6, Prop 6.22), Saad-eig §6.2 (Prop 6.6), Choi
(2.42)–(2.44), Meurant §2.1.

Difficult proof: identification of the Gram–Schmidt definition with the classical recurrence
(`vec_succ_eq`, `coeff_succ_self`). Mathlib gives `gramSchmidtNormed f (j+1) ∝ f (j+1) −
P_{𝒦_{j+1}} f (j+1)` while the classical `w_j = A v_j − P_{𝒦_{j+1}} (A v_j)`; both unit vectors
span the one-dimensional space `𝒦_{j+2} ⊓ 𝒦_{j+1}ᗮ`, and they coincide because both have
positive real inner product with `A^{j+1} b` (the leading coefficients of `v_j` as a polynomial in
`A` applied to `b` are positive reals, by induction). Nothing else in phase 1 depends on these two
lemmas. The Gram–Schmidt definition is preferred because Mathlib supplies orthonormality, spans
and the breakdown behaviour (`gramSchmidtNormed` is `0` on dependent vectors) for free; the
flag-uniqueness lemmas of 2.1.13 identify MGS, Householder and block variants with it.
Householder Arnoldi (Alg 6.3), MGS variants and reorthogonalization are surface (or floating-point
phase) material.

### 3.3 `Krylov/Lanczos.lean` (L1, symmetric `A`)
Serves Saad §6.6 (Thm 6.19, Alg 6.15, (6.87)–(6.91)), Saad-eig §6.3, Choi §2.1 ((2.4)), Meurant
§2.1, Fong–Saunders §1.1. Indexing: `alpha A b j = ⟪v_j, A v_j⟫` and `beta A b j = h_{j+1,j} = ‖w_j‖`.

Choi Prop 2.2 / Cor 2.3 / Thm 2.4 (termination index ≤ `rank A + 1`, ≤ number of distinct
eigenvalues with nonzero weight) are L3 statements for `Krylov/Singular.lean` (phase 2).

### 3.4 `Krylov/Iterate.lean` (L1)
Serves Saad §6.4–6.5 (Prop 6.7, 6.10, Lemma 6.28, 6.31), Fong–Saunders §2, Choi Table 2.5,
Thm 2.25/3.1 (abstract core), AH (5.6.12)–(5.6.14).

Proof of `norm_le_of_apply_eq`: for symmetric `A`, `range A ⟂ ker A`; `b ∈ range A` gives
`𝒦_m(A, b) ≤ (ker A)ᗮ`; if `A y = b` then `y − x ∈ ker A` and Pythagoras. No completeness or finite
dimension needed. The MINRES-QLP specification (minimum-norm element of the minimal-residual set,
`Krylov.IsMinNormMinResIterate`) is an open node of `Krylov/Iterate.toml`; its theorems are in
`Krylov/Singular.toml`.

### 3.5 `Krylov/Hessenberg.lean` (transport to small problems; L1 + finite matrices)
Serves Saad §6.4 ((6.16)–(6.18)), §6.5 ((6.27)–(6.47), Prop 6.9, (6.62), (6.75), (6.80)–(6.81),
Lemma 6.16), Choi §2.2 ((2.18)–(2.24), Lemma 2.18–2.20), Fong–Saunders §4.2, Meurant (3.1). Three
layers: the Hessenberg relation for an arbitrary basis, FOM/GMRES in Arnoldi coordinates, and the
`ℕ`-indexed Givens QR with its spec-level identifications.

Because the rotations are computed from the infinite coefficient function, prefix stability across
`m` is automatic and no `Fin` casts appear before the final matrices; the spec-level identities
`|s_m| = ‖r^G_{m+1}‖/‖r^G_m‖`, `|c_m| = ‖r^G_{m+1}‖/‖r^F_{m+1}‖` make the Givens data
non-blocking for the Cullum–Greenbaum relations (3.6), which are proved without it. All finite-index
bookkeeping over an orthonormal family; this is where Saad's, Choi's and Fong–Saunders'
implementations meet. The FOM/GMRES ratio is the useful form exactly when `c_m ≠ 0`, which by
`isUnit_hessenbergSq_iff_givensC_ne_zero` is exactly when the Galerkin iterate is unique.

The five Arnoldi identifications, `norm_residual_eq_norm_gamma` through
`norm_residual_eq_div_norm_givensC`, all pass through one missing brick: *a unitary matrix is a
Euclidean isometry*, `‖U *ᵥ v‖₂ = ‖v‖₂`. Mathlib has `Matrix.unitaryGroup` but no `mulVec`
isometry; the route is `Matrix.toEuclideanCLM` plus "a unitary element of a C⋆-algebra is an
isometry", and the statement belongs in `Analysis/Matrix/` (2.1.14). On top of it they need the
residual splitting `‖Q(βe₁) − R̄y‖² = ‖g − Ry‖² + |γ_m|²` from `rotated_last_row`, and the
solvability of `R_m y = g_m` through `det R_m = ∏ ρ_k ≠ 0`;
`isUnit_hessenbergSq_iff_givensC_ne_zero` also needs a block decomposition of the rotation product,
since `givensQ_mul_hessenbergOf` gives only the rectangular identity.

The Lanczos specializations (Choi (2.21) `‖r_k‖ = φ_k = β₁ s₁ ⋯ s_k`, the
MINRES residual recurrence `r_k = s_k² r_{k−1} − φ_k c_k v_{k+1}` of Choi Lemma 2.18 / Saad (6.55),
and Choi Lemma 2.19) are phase-2 sketches for `Krylov/Singular.lean`; the Galerkin residual in
Lanczos terms, `r_k = (−1)^k ‖r_k‖ v_{k+1}` (Saad (6.87)), is `CG.arnoldi_vec_eq` (3.7). SYMMLQ's
LQ factorization and MINRES-QLP's QLP are surface (Choi) unless a second source needs them.

### 3.6 `Krylov/Relations.lean` (L1)
Serves Saad §6.5.7–6.5.8 (Prop 6.12–6.17, Lemma 6.18, Alg 6.14, (6.65), (6.74), (6.79)),
Fong–Saunders (4.1), Choi Prop 2.16(3), Greenbaum Lemma 5.4.1.

Difficult proof (Cullum–Greenbaum without Givens): smooth the Galerkin sequence with `mrs`;
Galerkin residuals lie in `span{v_{i+1}}` and are pairwise orthogonal, so Weiss's lemma gives the
harmonic recurrence; `r_m^S ∈ r₀ + A 𝒦_m` and is minimal by induction, using
`map_subspace_succ_eq_sup_span` to see that the minimization over `A 𝒦_{m+1}` is the
one-dimensional minimization along `r^F_{m+1} − r^G_m`; hence `r_m^S = r_m^G` by uniqueness of the
minimal residual. This keeps the result at L1 and independent of any factorization; the Givens
route in 3.5 gives the same identity and the `c_m, s_m` interpretation.

### 3.7 `Krylov/CG.lean` (L1; termination facts L3)
Serves Saad §6.7 (Alg 6.16–6.19, Prop 6.20, §6.7.2–6.7.3), AH (5.6.2)/§9.4 Alg 1, Fong–Saunders
Table 2.1 and Table 5.1 (CG column), Meurant §3 (Thm 11, 12, (3.3)–(3.4)), Choi Table 2.7.

Difficult proofs: the invariants are a joint induction (standard; keep the induction hypothesis
as a bundled `CG.Invariant k` structure with the four orthogonality facts and the span equalities,
proved for `k+1` from `k`). Steihaug's monotonicity uses `⟪r_i, p_j⟫ = ‖r_j‖²` for `j ≥ i` and hence
`⟪p_i, p_j⟫ ≥ 0` — a local argument, no termination needed. The Lanczos coefficients in terms of
the CG coefficients (Saad (6.102)–(6.103)) are surface corollaries of `arnoldi_vec_eq`; the
D-Lanczos / `LDLᵀ` derivation is surface (Saad Alg 6.17, Choi Table 2.6).

### 3.8 `Krylov/CR.lean` (L1; sign results L3)
Serves Saad §6.8–6.9 (Alg 6.20, Lemma 6.21), Fong–Saunders Thm 2.1–2.5, Choi Table 2.12.

CR on symmetric coercive `A` is well defined (`⟪r, A r⟫ > 0` unless `r = 0`); on indefinite `A`
the recurrence may break down while the minimal-residual iterate still exists — that is why the
spec, not the recurrence, is canonical.

### 3.9 `Krylov/Convergence/Polynomial.lean` (L3 spectral bounds; L1 via the compression trick)
Serves Saad Thm 6.29 (proof), Prop 6.32, Cor 6.33; AH (5.6.16)–(5.6.19); Meurant (3.7)–(3.8);
Saad-eig Lemma 6.1.

The compression trick: everything a Krylov method does in `m` steps happens inside the
finite-dimensional `𝒦_{m+1}`, on which `A` acts as its compression up to the last step. To bound
`p(A) x`, compress `A` to `K = span {x, A x, …, A^{deg p} x}`; `compression.aeval_apply_of_forall_pow_mem`
gives `p(A_K) x = p(A) x`, `compression.isSymmetricBoundedBy` transports the hypothesis, and the
finite-dimensional bound applies to `A_K`. This makes AH Thm 5.6.1 and Kantorovich (2.4.3) fully
general without a functional calculus. Mathlib's continuous functional calculus for self-adjoint
elements of `E →L[𝕜] E` (`cfc`, `‖cfc f a‖ = sup_{σ(a)} |f|`) is a phase-2 alternative route to
the same statements.

### 3.10 `Krylov/Convergence/CG.lean`
Serves Saad Thm 6.29, Thm 6.30, (6.123)–(6.128); AH Thm 5.6.1 ((5.6.4)–(5.6.6)); Meurant (3.9);
Fong–Saunders §1.

Proof: 3.4 (energy-norm polynomial characterization) + 3.9 (compression trick) + 2.1.9 with
`[a, b] = [λmin, λmax]`. The Chebyshev-type bounds therefore hold in *any* inner product space,
with no completeness, no finite-dimensionality and no functional calculus: `m` steps of the method
live inside the finite-dimensional `𝒦_{m+1}`, the compression of `A` to it inherits the
quadratic-form bounds (`compression.isSymmetricBoundedBy`), and the spectral theorem is applied
there. Phase 2: the minimal-residual (MINRES) bound for symmetric indefinite `A`
via Chebyshev on two intervals (`Krylov/Convergence/MinRes.toml`, at the finite-dimensional rung,
with the two-interval polynomial as a node of `ChebyshevMinimax.toml`); Winther's superlinear
convergence for `A = 1 − K`, `K` compact self-adjoint (AH Thm 5.6.2). *Done*, with the eigenbasis
taken as data and a sharper constant than the book's — `(Δ/δ)^{1/(2k)}` rather than `(Δ/δ)^{3/(2k)}`,
the exponent `3/2` being an artefact of routing through the residual. The reason once given for
taking the eigenbasis as data — that Mathlib lacks the compact spectral theorem — **was wrong**: it
has `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` and
`ContinuousLinearMap.finite_dimensional_eigenspace`. What it lacks is the decreasing *enumeration*
of the eigenvalues in infinite dimension, which needs the accumulation-at-`0` fact
(`{μ | HasEigenvalue T μ ∧ ε ≤ ‖μ‖}` is finite) and separability of the space. Supplying those
three would turn the hypotheses `hlam`, `hanti` and `hlim` of `Krylov.winther` into conclusions
with no change to its proof.

### 3.11 `Krylov/Monotonicity.lean` (Fong–Saunders; L3)
Serves Fong–Saunders §2–3 and Table 5.1; Choi Lemma 2.14, 2.20; Steihaug.

Proof route: identify the iterates with the CR/CG iterates and use the sign lemma of 3.8
(Fong–Saunders Thm 2.2), whose parts (d)–(f) use finite termination `x_ℓ = x*` and the orthonormal
expansion in `{A p_i/‖A p_i‖}`. The stopping rule (3.4) is `backwardError_le_iff` (2.2); the
monotonicity of both optimal perturbations `‖E_k‖/‖A‖`, `‖f_k‖/‖b‖` follows from
`exists_optimal_perturbation` (2.2). Phase 2: Steihaug's generalization to indefinite `A` (`‖x_k‖`
increasing while `⟪A p_j, p_j⟫ > 0` for `j ≤ k` (CG), resp. also `⟪r_j, A r_j⟫ > 0` (CR/MINRES)) —
open as `CG.norm_iterate_lt_of_re_inner_apply_direction_pos` and `CR.norm_iterate_lt_of_pos`, the
latter with the global no-breakdown hypothesis the paper's proof needs; Choi Lemma 2.20 / (3.21)
(`‖A x_k‖` nondecreasing for minimal-residual iterates), open in `Krylov/Monotonicity.toml`. Extending to
Hilbert spaces (infinite orthonormal expansions, `x_k → x*`) is a phase-3 improvement.

### 3.12 Phase 2–3 Krylov modules

The later Krylov modules are planned as groups, each with a description saying what the module is
for and why it has the shape it has, and nodes for its statements: `Krylov/Preconditioned.toml`
(PCG as CG for `M⁻¹ A` in `WithEnergy M`, Saad Prop 9.1–9.3, AH §9.4's Riesz-representative
residual), `Krylov/Singular.toml` (Choi Ch. 2–3: termination indices, MINRES and MINRES-QLP on
singular systems, the Lanczos residual recurrences and norm estimates),
`Krylov/OrthogonalPolynomials.toml` (Meurant–Strakoš §2–3: the spectral measure, Lanczos
polynomials, Gauss quadrature, the CG error identity, persistence, Christoffel–Darboux),
`Krylov/BiLanczos.toml` (Saad Ch. 7: two-sided Lanczos, BCG, QMR as a `HessenbergRelation` with a
non-orthonormal basis), `Krylov/Block.toml` (Saad §6.12), `Krylov/NormalEquations.toml` (§10:
CGNR, CGNE, LSQR/LSMR as CG/MINRES on `Aᴴ A`) and, for phase 4, `Krylov/Perturbed.toml`. What
stays here is the one item that is not a module:

* Faber–Manteuffel (Saad §6.10, L3, unique to Saad) — Saad surface; the normal-matrix theory it
  rests on is `Eigen/Normal.lean`, which is where a second book's normal-operator statements should
  also go. Lemma 6.23 ("`Aᴴ v ∈ 𝒦_s(A,v)` for all `v` iff `A` normal with `ν(A) ≤ s−1`") stays in
  the Saad surface.

---

## 4. Tree of contents, part III: the eigenvalue layer (`Numlib/Eigen/`)

Shared by Saad-eig (whole book), Saad §1.8–1.9/§4/§6.6, Kress Ch. 7, Higham Ch. 18, Meurant §2
(Ritz values), Choi §2.1. Phase 1 contains only what the Krylov layer and the phase-1 surfaces
need (4.1); the rest is phase 2–3 and is driven by the Saad-eig surface. The structural principle
of this layer: linear-system projection methods (§2.4) and eigenvalue projection methods (4.2)
are the same object, the compression `compression A K` of 2.1.6, with Céa's `‖A‖/c` and
Saad-eig's `γ = ‖P_K A (1 − P_K)‖` as the two error constants.

### 4.1 `Eigen/Perturbation.lean` (L3, L4)
Serves Saad-eig Ch. 3 (Cor 3.3 Hermitian residual bound, Lemma 3.2/Thm 3.8/Cor 3.4 Kato–Temple,
Thm 3.6 Bauer–Fike, Prop 3.4 backward error, Thm 3.11 Gershgorin), Saad-eig Thm 1.9–1.10 and
Kress Thm 7.3–7.4 (Rayleigh quotient bounds), Kress Thm 7.7 (Gershgorin), Kress Problem 7.6,
Saad Thm 1.35 (Bendixson), Meurant §2.1, Choi §2.4 (Ritz-value bounds), Higham §18. In the
symmetric statements `θ` abbreviates the Rayleigh quotient `RCLike.re (inner 𝕜 (A x) x)` of a
unit vector `x` and `r := A x - (θ : 𝕜) • x` its residual.

Difficult proof: Bauer–Fike is short once `‖(D − μ)⁻¹‖₂ = 1/dist(μ, σ)` is available for
diagonal matrices (Mathlib's `Matrix.l2_opNorm` API needs a small lemma for diagonal matrices);
Bendixson follows from `rayleigh_mem_Icc` applied to `H` at an eigenvector of `A`.

The later-phase items — the eigenvector residual bound (Saad-eig Thm 3.9), the column-sum
Gershgorin discs and the disc counting (Thm 3.12, blocked on the continuity of eigenvalues, which
Mathlib lacks), the condition numbers of a simple eigenvalue and of an eigenvector with the
first-order perturbation formula (Def 3.1–3.2, Prop 3.5; the implicit function theorem on `det`,
with `HasStrictDerivAt` of `Polynomial.eval` at a simple root), and pseudospectra (Def 3.3,
Prop 3.7) — are the open nodes of `Eigen/Perturbation.toml`. Weyl's inequality (Kress Cor 7.5) is
done, in `Eigen/MinMax`. Saad-eig Thm 3.7/Cor 3.2 (the Jordan version of Bauer–Fike) stay in the
surface; Wielandt–Hoffman and Davis–Kahan are not planned.

### 4.2 `Eigen/RayleighRitz.lean` (L1 definitions, L3 bounds; phase 2)
Serves Saad-eig §4.3 (Prop 4.3 exactness on invariant subspaces, Thm 4.3/4.7 residual bounds with
`γ`, Prop 4.4/Cor 4.1/Thm 4.4 Ritz values via min–max, Lemma 4.1/Thm 4.5 Ritz-value errors,
Thm 4.6 Ritz-vector angle, Prop 4.5), §6.1–6.2 (Prop 6.4 compression commutes with low-degree
polynomials, Thm 6.1 optimality of the characteristic polynomial of `H_m`, Prop 6.8 cheap residual
`‖(A − θ)ũ‖ = h_{m+1,m}|e_mᵀ y|`), Thm 8.1 (Davidson monotonicity), Meurant §2 (Ritz values),
Choi §2.4.4 (Ritz-value estimates), Kress Thm 11.17 (Céa in operator form: the linear-system twin).

Everything the sketch here used to list is written — Ritz pairs and oblique Ritz pairs as
eigenpairs of the compression, exactness on invariant subspaces, the residual bounds with `γ`,
the variational characterization and interlacing of Ritz values, the Ritz-value and Ritz-vector
errors, the optimality of the characteristic polynomial and the cheap Arnoldi residual
(`tracker show Eigen/RayleighRitz`) — and Courant–Fischer, the missing Mathlib brick, is
`Eigen/MinMax`, proved by the dimension count on `S ⊓ span{u_k, …, u_n}` with
`Submodule.finrank_sup_add_finrank_inf_eq`; it also gave Weyl's inequalities and the interlacing
that the Lanczos bounds (4.4) use. The open nodes of `Eigen/RayleighRitz.toml` are Thm 4.5 for
every index, the oblique residual bounds of Thm 4.7 and the monotonicity of the Ritz values in
the subspace (the mechanism of Thm 8.1).

### 4.3 `Eigen/PowerMethod.lean` (L3; phase 3)
Serves Saad-eig Thm 4.1 (power method with a semi-simple dominant eigenvalue), §4.1.2–4.1.3
(shifted/inverse iteration, RQI stated), Thm 4.2/Prop 4.1–4.2 (Wielandt and Schur–Wielandt
deflation), Thm 5.1–5.2 (subspace iteration), Kress §7.2 (power method for diagonalizable `A`,
Lemma 7.18 subspace iteration, Thm 7.19 orthogonal iteration, Thm 7.20 QR algorithm).

The power method and subspace iteration are written; the module doc comment is the description.
Three corrections to what was planned here, kept because the reasons matter.

*Gelfand is not needed, and neither is the spectrum of a restriction.* The plan proposed to bound
`‖(A|_W)^k‖` by Gelfand's formula (2.1.3) after computing `spectrum (A|_W) = σ(A) ∖ {λ₁}`. The
elementary route is shorter and far more general: for a single generalized eigenvector,
`(A − μ)^N w = 0` and `‖μ‖ < r` give `‖A^k w‖ ≤ C r^k` by induction on `N`, because
`A^{k+1} w = μ A^k w + A^k (A − μ) w` turns a bound for `(A − μ) w` into the scalar recursion
`a_{k+1} ≤ ‖μ‖ a_k + C r^k`, whose solution is `(‖w‖ + C/(r − ‖μ‖)) r^k`. The vectors obeying such
a bound form a submodule, so the supremum of the subdominant generalized eigenspaces inherits it
with no finiteness argument and no uniform gap. The result holds over any `RCLike` field, in any
normed space, with `A` neither continuous nor acting on a complete space; finite dimension and
algebraic closedness are used only to split `x₀` at all.

*Semi-simplicity is a hypothesis on `x₀`, not on `A`.* The book assumes the dominant eigenvalue
semi-simple (not simple, as an earlier reading had it). The statement here takes the splitting
`x₀ = u + w` with `A u = λ₁ u` and `w ∈ W` as hypotheses rather than a spectral projector, which
is weaker still — only the `λ₁`-component of *this* `x₀` has to be an eigenvector — and recovers
the semi-simple and simple forms as corollaries. This avoids a projector API entirely; where a
projector is wanted it is `Krylov.spectralProjector` below, which is `Submodule.projection` of the
splitting and is the correct *oblique* projector — `starProjection` is wrong here, the
decomposition being non-orthogonal for non-normal `A`. On the direction: Saad's algorithm normalizes by the entry of
largest modulus, so it converges outright, while a norm-normalized iterate can only converge up to
a unimodular factor; the book's own notion for that case, "converges essentially", is what the
module states, with the factor `(λ₁/‖λ₁‖)^k` made explicit.

*Subspace iteration is not a gap statement, and it is cheap.* Saad-eig Thm 5.2 bounds
`‖(I − P_k) u_i‖`, the distance from a dominant eigenvector to `S_k = A^k S₀`, which
`Submodule.starProjection` already expresses; the plan's name `subspaceIterate_gap_le` came from a
paraphrase, and the module now states what the book proves, as
`Krylov.exists_norm_sub_starProjection_subspaceIterate_le`. Two estimates were budgeted for it and
neither was needed. The analytic core is the decay estimate above plus *one candidate vector*:
`λ^{-k} A^k s` lies in `S_k` and its error is `λ^{-k} A^k (s − u)`, so the best approximation from
`S_k` does at least as well — that is `Krylov.norm_sub_starProjection_subspaceIterate_le`, which
mentions no spectrum, no projector and no finite dimension of the ambient space. The linear algebra
is `Krylov.isCompl_iSup_maxGenEigenspace` (the splitting for a *set* of eigenvalues, from
`iSupIndep.disjoint_biSup_biSup` and `iSup_split`, with the one-eigenvalue case now a corollary),
`Krylov.spectralProjector` (`Submodule.projection` of that splitting — Mathlib's `projection` is
already the endomorphism form, and supplies `ker`, `range`, idempotence and the fixed-point lemma)
and `Krylov.existsUnique_mem_spectralProjector_eq` (rank–nullity plus
`Submodule.eq_of_le_of_finrank_le`). The book's hypothesis that the `P x_i` be linearly independent
is `Disjoint S₀ W`, which is `Krylov.injOn_spectralProjector_iff`.

*The gap form is Kress's theorem, not Saad's, and its obstruction is elsewhere.* The gap statement
is genuinely different and strictly stronger — `Submodule.sinAngle_le_gap` derives the per-vector
bound *from* a gap bound, for every vector of the invariant subspace and not only for its
eigenvectors — and it is **Kress Lemma 7.18**, `‖P_{A^k S} − P_T‖ ≤ M |λ_{m+1}/λ_m|^k` for
diagonalizable `A`, on which his Thm 7.19 (orthogonal iteration) and Thm 7.20 (QR) rest. It is
`Krylov.gap_subspaceIterate_le`, still open. Kress's proof does **not** use Saad-eig (3.8), a
uniform decay estimate on `W`, or the decay of `(A|_M)^{−k}`: it applies the per-vector decay to
the `m` vectors of one basis and then compares the two orthogonal projections through their normal
equations. So the one missing brick is a *quantitative continuity of the projector in its spanning
family* — from `‖w_j − x_j‖ ≤ δ` conclude `‖P_{span w} − P_{span x}‖ ≤ M δ` — which Mathlib does
not have in any form, there being no Gram-matrix formula for `Submodule.starProjection`. The node
records both Kress's route (perturbation of the Gram system, his Thm 5.3) and a two-sided
alternative that ends in the `≤` half of Saad-eig (3.8); that half needs `[CompleteSpace E]`, which
is why `Projection/Angle` left it out, but is free here because the statement already assumes
finite dimension. "A projector family with `‖P − Q‖ < 1` has constant rank" (Saad-eig Thm 3.2) is
done, as `Submodule.finrank_eq_of_gap_lt_one`.

The rest is planned as open nodes: inverse iteration with a shift (`Krylov.inverseIterate` in
`Eigen/PowerMethod.toml`, a `simp` lemma over the power method with the spectrum mapped by
`(· − σ)⁻¹`), Wielandt and Schur–Wielandt deflation (`Eigen/Deflation.toml`, Saad-eig Thm 4.2,
Prop 4.1–4.2), and orthogonal iteration with the QR algorithm (`Eigen/QRAlgorithm.toml`, Kress
Thm 7.19–7.20), whose convergence rests on the *gap* form `Krylov.gap_subspaceIterate_le` applied
to the canonical flag one dimension at a time — the per-eigenvector bound is not enough for it.

### 4.4 `Eigen/KrylovEigen.lean` (L3; phase 2)
Serves Saad-eig §6.6 (Lemma 6.1, Thm 6.3 angle bound, Thm 6.4 Kaniel–Paige–Saad, §6.6.3 Ritz
vectors), §6.7 (Lemma 6.2, Thm 6.5–6.7 Haar characterization, Prop 6.10, Thm 6.8 ellipse bound),
§4.4 (Thm 4.8 min–max with `p(γ) = 1`, Lemma 4.3 Zarantonello, Thm 4.9 ellipses), Saad §6.6,
Meurant §2.3 (Ritz values as Gauss nodes).

The three §6.6 items are written (`tracker show Eigen/KrylovEigen`); their doc comments record what
the statements needed beyond the book's, since the book leaves the finiteness of its own constants
implicit — the projector onto the *line* through `u_i` rather than the eigenspace, which keeps
Lemma 6.1 true at a multiple eigenvalue; the strict orderings without which `γ_i` and `κ_i` divide
by zero; and, for Kaniel–Paige–Saad at a general index, only the easy inclusion of the book's
characterization of `𝒦_m ⊖ {ũ_1, …, ũ_{i−1}}`. The open nodes of `Eigen/KrylovEigen.toml` are the
basis-free `‖(1 − P_m) A P_m‖ = h_{m+1,m}` (Prop 6.6), the Lanczos Ritz-vector bound (§6.6.3), and
the non-Hermitian Arnoldi bounds (Lemma 6.2, Prop 6.10, Thm 6.8), the last two waiting on the
ellipse module `RingTheory/Polynomial/ChebyshevEllipse.toml`; the Ritz values as eigenvalues of
`T_m` and roots of the Lanczos polynomial are in `Krylov/OrthogonalPolynomials.toml`.
Proofs combine 2.1.9 (Saad-eig Thm 4.8, the general-`γ` Chebyshev min–max, which the book states
without proof), 3.9 (polynomial norm bounds) and 4.2 (Courant–Fischer on `𝒦_m`); this is a direct
analogue of 3.10 and should be done right after 4.2.

### 4.5 Phase 3 eigenvalue material
Analytic perturbation theory via Riesz–Dunford projectors (Saad-eig §3.1.3–3.1.5, Thm 3.3–3.5,
Prop 3.3: needs contour integrals of operator-valued functions — Mathlib has the Cauchy integral
formula for `ℂ`-valued functions only; use `Module.End.maxGenEigenspace` projectors instead, which
give Thm 3.3 algebraically), deflation (Saad-eig §4.2), subspace iteration (Ch. 5), restarting/
filtering/Chebyshev iteration (Ch. 7), Davidson/Jacobi–Davidson (Ch. 8), generalized/quadratic
problems (Ch. 9), Jacobi's method (Kress Thm 7.11–7.14: Frobenius-norm descent, independent of the
Krylov core), Hessenberg reduction (Kress Thm 7.22) and the QR algorithm (Kress Thm 7.19–7.20),
Higham Ch. 18 (matrix powers in finite precision, phase 4). The normal-matrix theory behind
Saad Lemma 6.23/Thm 6.24 is no longer phase 3: `Eigen/Normal.lean` is written (see 3.12), and it
gets diagonalizability of a normal operator from `ker N² = ker N` and
`Module.End.iSup_maxGenEigenspace_eq_top` rather than from a triangulation theorem. Schur form is
still not in Mathlib and is still a phase-3 upstreaming candidate under `Numlib/Matrix/`, but
nothing here waits on it. Jordan form is not in Mathlib either and is avoided:
every use here is replaced by Gelfand's formula or by generalized eigenspaces; Saad-eig
Thm 3.7/Cor 3.2 and P-5.6 are the only results that need the Jordan index and stay in the surface.

Of this list, deflation is `Eigen/Deflation.toml`, Jacobi's method `Eigen/Jacobi.toml`, orthogonal
iteration and the QR algorithm `Eigen/QRAlgorithm.toml` (Hessenberg reduction is a cost remark and
is not planned), the Schur form `LinearAlgebra/Matrix/Schur.toml` and the SVD with the
pseudoinverse and Tikhonov regularization `LinearAlgebra/Matrix/SVD.toml`. The analytic
perturbation theory, restarting and filtering, Davidson and the generalized problems have no plan
yet; they wait for a Saad-eig surface to be written section by section, which is when their
backbone shape can be decided.

---

## 5. Tree of contents, part IV: approximation, variational and nonlinear layers

### 5.1 `Numlib/Approximation/`

#### 5.1.1 `Approximation/BestApprox.lean` (L2)
Serves AH §3.3–3.4, §3.6–3.7 (Lebesgue lemma), Kress Thm 3.50–3.54 (existence in
finite-dimensional subspaces, orthogonality characterization, projection theorem, normal
equations), Saad §1.12, Saad-eig Thm 3.1.

Existence needs `[LocallyCompactSpace 𝕜]` on top of completeness: proximinality of a
finite-dimensional subspace is `FiniteDimensional.proper`, which is what makes closed bounded sets
compact. Instance search supplies it for `ℝ`, `ℂ` and any `RCLike 𝕜`, so no call site sees it.

Orthogonal ⇔ self-adjoint projection (AH Prop 3.6.9) is Mathlib's
`IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker`. AH Thm 3.3.14 (existence from a closed
convex set of a reflexive space) is phase 3: Mathlib lacks reflexivity/weak compactness, and
`Variational/Minimization.toml` says why the reflexive theorems are not even planned as nodes.

#### 5.1.2 `Approximation/Chebyshev.lean` (phase 3)
Chebyshev equioscillation (AH Thm 3.3.19, Kress) — not in Mathlib (Haar condition, de la
Vallée-Poussin). The min–max results the Krylov layer needs are in 2.1.9; Chebyshev
expansions/uniform bounds (AH Ex 3.7.4) belong with the trigonometric module below. Plan:
`Approximation/Chebyshev.toml`, with the Haar condition stated separately so that the
trigonometric case (AH Thm 3.3.20) is the same theorem.

#### 5.1.3 `Approximation/Interpolation.lean` (phase 3)
Lagrange interpolation (`Lagrange.interpolate` in Mathlib), the error formula
`f(x) − p(x) = f^{(n+1)}(ξ) ∏(x − x_i)/(n+1)!` (AH §3.2, Kress §8.1; needs a generalized Rolle from
`exists_hasDerivAt_eq_zero` by induction), Lebesgue constants of interpolation projections,
piecewise-linear/spline interpolation (Kress §8.3) and trigonometric interpolation with Rivlin's
bound (AH (3.7.19)–(3.7.20)). Plan: `Approximation/Interpolation.toml`; AH Ex 3.6.5–3.6.6 are the
second consumer.

#### 5.1.4 `Approximation/Quadrature.lean` (phase 3)
Interpolatory quadrature, degree of exactness, Gauss quadrature via orthogonal polynomials (3.12
`OrthogonalPolynomials`, Meurant §2.3, Kress §9.3), convergence of quadrature rules for
continuous integrands via Banach–Steinhaus (AH §2.4.4/Kress Thm 9.10 (Szegő): bounded weights +
exactness on a dense set; Mathlib `banach_steinhaus` + `polynomialFunctions_closure_eq_top`),
Peano kernel error representation (Kress). Placed after 3.12 because the Gauss-rule existence
proof is the Lanczos/Jacobi-matrix argument. Plan: `Approximation/Quadrature.toml`; the
Banach–Steinhaus density criterion it rests on, which the Atkinson–Han surface proves for itself
today, is `Analysis/Normed/Operator/BanachSteinhaus.toml`.

#### 5.1.5 `Approximation/Trigonometric.lean` (phase 3)
The Fourier projection on `C_p(2π)`, the Dirichlet kernel and the Lebesgue constants, Jackson's
theorems (AH Thm 3.7.1–3.7.2) and their consequences (3.7.11)–(3.7.12), (3.7.22), Ex 3.7.4. None
of the objects exist in Mathlib (Fourier series are there in `L²` on `AddCircle`, not the uniform
theory); Jackson's theorem is the hard item. Plan: `Approximation/Trigonometric.toml`. The norm
identity `‖𝓕_n‖ = L_n` needs the integral-operator norm formula of `IntegralEquations/Basic.toml`
(5.4).

### 5.2 `Numlib/Variational/`

#### 5.2.1 `Variational/Forms.lean` (L2)
Serves AH Thm 8.3.1–8.3.3, §8.7 (inf–sup condition), §9.1 (Ritz), §9.4 (energy norm), Kress §11.
Bounded forms are `SesqForm 𝕜 V := V →L⋆[𝕜] V →L[𝕜] 𝕜` (conjugate-linear in the first slot, as
`innerSL`; Mathlib's `IsCoercive` is the real case). Over `ℝ` a `V →L[ℝ] V →L[ℝ] ℝ` *is* a
`SesqForm ℝ V` (the same defeq Mathlib's `LaxMilgram.lean` uses), so the real surfaces need no
conversion; the `_real` lemmas remove the `re`/`conj` decorations (1.7).

The statements are in `Numlib/Variational/Forms.lean` (`tracker show Variational/Forms`): the
predicates `IsBoundedWith`, `IsCoerciveWith`, `IsCoercive`, `IsHermitian`, the `_real` lemmas, the
operator ↔ form dictionary `toOperator`/`ofOperator`/`rieszRep` on Hilbert spaces, the energy
functional and energy norm with the equivalence `√c ‖v‖ ≤ ‖v‖_a ≤ √M ‖v‖`, and the two-space
`SesqForm₂` with `InfSupWith` and `IsNondegenerate`.

#### 5.2.2 `Variational/LaxMilgram.lean` (L2)
Serves AH Thm 8.3.3–8.3.4, Ex 8.3.5, (8.3.3) (variational inequalities), Thm 8.2.1–8.2.4,
Thm 8.7.1 (Babuška–Nečas) and its converse; Kress §11; Saad Prop 5.1–5.2 (bridge). All statements
assume `[CompleteSpace V]`.

Difficult proof (complex Lax–Milgram): the closed-range argument (AH proof #2): `‖A u‖ ≥ c‖u‖`
for `A = toOperator a` gives `AntilipschitzWith`, hence closed range
(`ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective`), and coercivity kills
`(range A)ᗮ`; this is `bijective_of_le_norm_of_orthogonal_range_eq_bot` and yields
`babuska_necas` with the same skeleton (there `(range A)ᗮ = ⊥` is the nondegeneracy hypothesis).
The alternative is to apply Mathlib's real theorem to `(u, v) ↦ re (a u v)` on `V` viewed as a
real inner product space (`InnerProductSpace.rclikeToReal`), recovering the imaginary parts by
substituting `v ↦ I • v`; the direct proof is shorter. AH proof #1 is
`contractingWith_damped_toOperator` plus the Banach fixed-point theorem. The Banach closed range
theorem in its general form is out of scope (1.7).

#### 5.2.3 `Variational/Galerkin.lean` (L1/L2)
Serves AH §9.1–9.3 (Prop 9.1.3 Céa, Cor 9.1.4, (9.1.5) stiffness matrix, (9.1.7)–(9.1.8) energy
best approximation, Thm 9.2.1 Babuška, Cor 9.2.3, Rem 9.2.2 Xu–Zikatanov, Thm 9.3.1 Strang), §9.4;
Kress Thm 11.17 (Céa for `P_n A u_n = P_n f`, operator form) and Ch. 12 (projection methods for
`I − K`, `K` compact: stability from Neumann series — phase 3); bridge to Saad Ch. 5, Saad-eig §4.3
and to CG.

The Babuška and Strang bounds carry `0 ≤ M` (and `0 ≤ δ`) as explicit hypotheses. A boundedness
hypothesis quantified over a subspace is vacuous when that subspace is trivial, so unlike
`SesqForm.IsBoundedWith` on the whole space it does not force its own constant to be nonnegative,
and the constants `1 + M/α`, `δ/c` in the conclusions would otherwise be meaningless.

Phase 2: the Xu–Zikatanov sharpening of Babuška's bound to `M/α_N` via Kato's lemma (2.1.7) — the
Petrov–Galerkin projector and the sharpened bound are open nodes of `Variational/Galerkin.toml`.
Kress Ch. 12 (projection methods for `I − K`) and his operator-form Céa (Thm 11.17) are
`Variational/ProjectionMethod.toml`; the general form of AH Thm 3.3.13 that AH Ch. 11 reuses is
`Variational/Minimization.toml`.

AH §9.4 (CG in variational form; the "residual" is the Riesz representative of `ℓ − a(u_k, ·)`) is
CG (3.7) run on the operator `A = a.toOperator` in `V`; AH §9.4's `‖u − u_k‖_a ≤ 2((√κ−1)/(√κ+1))^k`
is 3.10 with `κ = ‖a‖/c`. On a Krylov space everything is finite-dimensional, so the L3 bound
applies to the compression of `A` to `𝒦_{k+1}`, whose quadratic-form bounds are inherited
(`compression.isSymmetricBoundedBy`, 2.1.6); this gives the Hilbert-space CG bound without
functional calculus and is the route taken in 3.9–3.10.

### 5.3 `Numlib/Nonlinear/`

#### 5.3.1 `Nonlinear/FixedPoint.lean` (L2, metric)
Serves AH Thm 5.1.3–5.1.4, Thm 5.2.1, Ex 5.1.2, Ex 5.1.4, (5.1.11); Kress Thm 3.45–3.46 (Banach
with a priori/a posteriori bounds), Thm 6.1–6.2 (scalar), Thm 6.7 (mean value inequality),
Thm 6.8–6.9 (`sup ‖f'‖ < 1` criterion, local version), Problem 3.17 (`Aᵐ` contraction); Saad §4.2
(linear instance). Mathlib: `ContractingWith`, `ContractingWith.fixedPoint`,
`apriori_dist_iterate_fixedPoint_le`, `aposteriori_dist_iterate_fixedPoint_le`, `efixedPoint'`
(maps-to version on a complete subset).

The linear instance (the stationary iteration with `‖G‖ < 1`) is stated in 2.3.1. Bielecki
weighted norms (AH Thm 5.2.3, Volterra) and generalized Picard–Lindelöf (Thm 5.2.4) are phase 3
(Mathlib has `IsPicardLindelof` in finite dimension), planned with the `C[a, b]` integral-operator
toolkit as `IntegralEquations/Basic.toml` (5.4).

#### 5.3.2 `Nonlinear/Newton.lean` (L2, Banach)
Serves AH Thm 5.4.1–5.4.2, Kress Thm 6.14 (semi-local Newton–Kantorovich with `αβγ < ½`, `r = 2α`),
Thm 6.20 (quadratic rate `(βγ/2)‖x* − x_ν‖²`), Cor 6.15 (local convergence for `C²`), Thm 6.21
(simplified Newton), Saad §9 (Newton–Krylov mention). Stated over a `NontriviallyNormedField 𝕜`
with the derivative supplied as a function `F' : E → E →L[𝕜] F` and inverted by
`ContinuousLinearMap.inverse` (`0` when `F' x` is not invertible).

The scalar field of the quadratic section is real or complex (`[IsRCLikeNormedField 𝕜]`, with
`[NormedSpace ℝ E]` for the segments), not an arbitrary nontrivially normed field. The estimates go
through the mean value inequality along the real segment from `x` to `x*`, and they are genuinely
false without it: in characteristic `p`, `x ↦ x + xᵖ` has derivative `1` everywhere while the
Newton step does not vanish. The definitions `step` and `iterate` stay over any
`NontriviallyNormedField`.

Phase 2: AH's stronger Kantorovich statement (uniqueness in `B̄(x₀, t**)`, error
`(1 − √(1−2h))^{2ⁿ}/(2ⁿ a L)`, existence localized to `B̄(x₁, t* − η)`) and the modified (chord)
Newton method with frozen derivative (linear convergence via 5.3.1, AH Ex 5.4.5; Kress Thm 6.21) —
open nodes of `Nonlinear/Newton.toml`.

Difficult proof: the quadratic estimate uses the integral form of the mean value theorem
`F(x*) − F(x) − F'(x)(x* − x) = ∫₀¹ (F'(x + t(x* − x)) − F'(x)) (x* − x) dt`; in Mathlib the
inequality form `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` avoids Bochner integrals but
accepts only a *constant* bound on `‖F' z − φ‖`, which costs the sharp constant: it yields `L`, and
`2L` once both points are required to lie in one ball, where `L/2` is wanted. The sharp form needs
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` applied to
`t ↦ F(x + t v) − F x − t F' x v` with boundary `B t = L‖v‖²(t − t²/2)`, at the cost of three
further instance arguments on a public statement. Invertibility of `F' x` near `x*` with a uniform
bound comes from 2.1.1. Kantorovich needs the majorant-sequence argument (`t_{n+1} = t_n −
p(t_n)/p'(t_n)` for `p t = (L/(2β))t² − t/β + η`, with a simultaneous induction bounding
`‖x_{k+1} − x_k‖` by `t_{k+1} − t_k` and `‖(F' x_k)⁻¹‖` by `β/(1 − βL(t_k − t_0))`, then the closed
form of `t_k`); reduction to `ContractingWith` does not work, since the Newton map is not a
contraction on the ball — only the error sequence is dominated by the majorant. Ortega–Rheinboldt
§12.6 / Deuflhard's affine-invariant version are the references.

### 5.4 `Numlib/IntegralEquations/` (phase 3)

Integral operators on `C(Icc a b, ℝ)` and the equations built on them: the Fredholm, Volterra and
Urysohn operators, the norm formula `‖K‖ = max_x ∫ |k(x, y)| dy` (AH (2.2.8)), Lipschitz bounds,
the Volterra factorial estimate and the Bielecki norm — the toolkit that AH Thm 5.2.2–5.2.4 and
Ex 2.3.2, 2.3.4 need, and that AH Ch. 12 and Kress Ch. 10–12 would build on. A layer of its own
rather than a corner of `Nonlinear/`, because two books have chapters that are nothing else.
Plan: `IntegralEquations/Basic.toml`.

---

## 6. Reserved: floating-point layer (`Numlib/FloatingPoint/`, phase 4)

Higham is the sole source; Paige/Greenbaum finite-precision Lanczos (Meurant §4–5) and Higham
Ch. 17 are the consumers. Only the *interface* is fixed here so that exact-arithmetic results are
stated in a way that survives perturbation. Plan: `FloatingPoint.toml` (the directory group
carrying the design rules), `FloatingPoint/Model.toml` (the relational `RoundingModel`, `γ_n` and
its calculus, `IsRelPert`), `FloatingPoint/InnerProduct.toml` (recursive summation, the
componentwise inner-product and matrix-product bounds), `FloatingPoint/Stationary.toml` (Higham
Thm 17.1–17.2 as a perturbed 2.3.1 iteration) and `Krylov/Perturbed.toml` (the perturbed
Arnoldi/Lanczos relation `Arnoldi.IsPerturbedRelation`, of which the exact relation is the `ε = 0`
instance).

Design rules: the model is relational (a rounding *relation*, never a rounding function);
componentwise statements first, normwise as corollaries through `LinearAlgebra/Matrix/Order.lean` (2.1.12);
results about *algorithms* are stated for an explicit evaluation order (a `SumTree`/fold), never
for "the" floating-point sum; keep `K` abstract (`ℝ` with a rounding relation), so that a concrete
IEEE model (flean / FloatSpec) can instantiate `FloatingPoint.RoundingModel` later. Gaussian
elimination/Cholesky/QR error analysis (Higham Ch. 8–10, 19) are Higham surface; only the model,
the `γ` calculus and the inner-product lemmas are backbone.

---

## 7. Phasing and work estimate

Sizes are rough line counts of finished Lean (statements + proofs), calibrated on comparable
Mathlib files. Difficulty: ★ routine, ★★ needs care, ★★★ real proof engineering. The phase-1
modules are exactly the modules under `Numlib/` (§11).

### Phase 1 — the spine (what the three selected books need)

| Module | Items | Size | Difficulty | Blocking |
|---|---|---|---|---|
| `Analysis/Normed/Ring/{Inverse,CondNumber}` | 2.1.1–2.1.2 | 250 | ★ | — |
| `Analysis/Normed/Algebra/SpectralRadius` | 2.1.3 | 200 | ★★ (ENNReal bookkeeping) | — |
| `InnerProductSpace/{Coercive,Energy,Compression,ObliqueProjection,GramSchmidt}` | 2.1.4–2.1.7, 2.1.13 | 700 | ★★ (`WithEnergy` instance D17; Kato's lemma D20 turned out routine) | — |
| `RingTheory/Polynomial/ChebyshevMinimax` | 2.1.9 | 300 | ★★ | — |
| `Matrix/{Hessenberg,Complexify,ToEuclideanLin}` | 2.1.10–2.1.11, 2.1.14 | 400 | ★★ | — |
| `LinearSolve/Perturbation` | 2.2 | 200 | ★ | 2.1.1–2.1.2 |
| `LinearSolve/Stationary/{Basic,Splitting,DiagDominant}` | 2.3.1–2.3.3 | 450 | ★★ (GS convergence) | 2.1.3, 2.1.11 |
| `LinearSolve/Projection/{Basic,Optimality,OneDimensional}` | 2.4.1–2.4.3 | 600 | ★★ (Kantorovich) | 2.1.4–2.1.7 |
| `Krylov/{Subspace,Arnoldi,Lanczos}` | 2.1.8, 3.1–3.3 | 700 | ★★★ (Arnoldi = Gram–Schmidt) | 2.1.13 |
| `Krylov/{Iterate,Hessenberg,Relations}` | 3.4–3.6 | 800 | ★★★ (Givens residual identities D21) | 2.1.10, 2.1.14, 2.4 |
| `Krylov/{CG,CR}` | 3.7–3.8 | 600 | ★★ (invariant induction) | 3.4 |
| `Krylov/Convergence/{Polynomial,CG}` | 3.9–3.10 | 350 | ★★ | 2.1.6, 2.1.9, 3.4 |
| `Krylov/Monotonicity` | 3.11 | 350 | ★★ (finite termination) | 3.7–3.8 |
| `Eigen/Perturbation` | 4.1 | 250 | ★★ | 2.1.2, 2.1.4 |
| `Approximation/BestApprox` | 5.1.1 | 200 | ★ | — |
| `Variational/{Forms,LaxMilgram,Galerkin}` | 5.2 | 600 | ★★ (complex Lax–Milgram) | 2.1.4–2.1.5, 2.4.1 |
| `Nonlinear/{FixedPoint,Newton}` | 5.3 | 400 | ★★★ (Kantorovich majorants, sharp Newton constant D15) | 2.1.1, 2.3.1 |
| Surface `SaadSparse` (§1.11–1.13, 4.1–4.2, 5, 6) | §8.1 | 1200 | ★ (if the backbone is right) | all above |
| Surface `FongSaunders` (complete) | §8.2 | 300 | ★ | 3.7–3.11 |
| Surface `AtkinsonHan` (selected sections) | §8.3 | 900 | ★ | 2.1, §5 |

Total ≈ 10 k lines. Recommended order: upstreaming candidates (2.1) → Projection → Krylov
(Subspace … Relations) → CG/CR → Convergence → Monotonicity → surfaces `FongSaunders` then
`SaadSparse` (Krylov chapters first). Perturbation, Stationary, `Eigen/Perturbation`,
Variational and Nonlinear are independent of the Krylov chain and can proceed in parallel with
it; `Krylov/Monotonicity` is the tail of the Krylov chain. Within `Krylov/`, the import order is
Subspace → Arnoldi → Lanczos → Iterate → Relations → Hessenberg → CG, CR → Convergence →
Monotonicity (§3).

### Phase 2 — second batch (Saad Ch. 7–9, Choi, remaining AH)
Every item is a group or an open node now; `lake exe tracker ready` orders them. Groups:
`LinearAlgebra/Matrix/Order`, `LinearSolve/Stationary/{RegularSplitting,SPD,ConsistentlyOrdered,Block}`,
`LinearSolve/Projection/Additive`, `Krylov/{Preconditioned,Singular,NormalEquations}`,
`Krylov/Convergence/{MinRes,Superlinear}`, `Variational/Minimization`,
`Analysis/Normed/Operator/BanachSteinhaus`, `Analysis/Convex/StrictConvexSpace`,
`Analysis/Normed/Module/WeakDual`. Open nodes appended to finished groups: the irreducible and
column-dominance results of `Stationary/DiagDominant`, Saad Thm 5.7 in `Projection/Basic`, the
one-step identities of `Projection/OneDimensional`, the minimal polynomial in `Krylov/Subspace`,
the MINRES-QLP specification in `Krylov/Iterate`, the Steihaug-type results in `Krylov/CG`,
`Krylov/CR` and `Krylov/Monotonicity`, the Gelfand transport for real matrices in
`LinearAlgebra/Matrix/Complexify`, arbitrary algebra norms in `Analysis/Normed/Algebra/SpectralRadius`,
the two-space condition number in `Analysis/Normed/Ring/CondNumber` and `LinearSolve/Perturbation`,
the sharp convergence factor in `LinearSolve/Stationary/Basic`, the eigenvector bound, condition
numbers and pseudospectra in `Eigen/Perturbation`, Thm 4.5/4.7/8.1 in `Eigen/RayleighRitz`, the
Ritz-vector and Arnoldi bounds in `Eigen/KrylovEigen`, inverse iteration in `Eigen/PowerMethod`,
Xu–Zikatanov in `Variational/Galerkin`, and the Kantorovich variants with the chord method in
`Nonlinear/Newton`. Courant–Fischer and Kaniel–Paige–Saad, listed here before, are done. The
continuous-functional-calculus form of 3.9 for bounded self-adjoint operators is not planned: the
compression trick covers every consumer so far.

### Phase 3 — Meurant–Strakoš exact part, Kress, remaining Saad-eig
Groups: `Krylov/{OrthogonalPolynomials,BiLanczos,Block}`, `RingTheory/Polynomial/ChebyshevEllipse`
(Saad Lemma 6.26, Thm 6.27, Cor 6.33; Saad-eig Thm 4.9, 6.8), `Eigen/{Deflation,QRAlgorithm,Jacobi}`
(the power method and subspace iteration are done; the gap form `Krylov.gap_subspaceIterate_le`
stays open and the QR algorithm waits on it), `LinearAlgebra/Matrix/{Schur,SVD}` (Kress
Thm 5.4–5.10), `Approximation/{Chebyshev,Interpolation,Quadrature,Trigonometric}`,
`Variational/ProjectionMethod` (Kress Ch. 12), `IntegralEquations/Basic` (AH 5.2.3–5.2.4, Bielecki
norms, Picard–Lindelöf); and, appended, Saad §6.6.2 (d)–(e) in the Saad surface, the non-Hermitian
Arnoldi bounds in `Eigen/KrylovEigen`, disc counting in `Eigen/Perturbation`. Not planned as nodes,
for want of Mathlib support or of a second consumer: AH Thm 3.3.14 and the reflexive-space
minimizers (see `Variational/Minimization.toml`), AH 6.2 Lax equivalence, Kress-specific direct
methods (LU/Cholesky/QR existence: Mathlib has `LDL`, no LU/QR), a form-based energy space for
non-complete `V` (1.7), and the Saad-eig chapters on restarting, Davidson and generalized problems.

### Phase 4 — floating point (Higham; Paige/Greenbaum)
§6: `FloatingPoint/{Model,InnerProduct,Stationary}` and `Krylov/Perturbed`; Higham Ch. 18 (matrix
powers in finite precision) is not planned.

---

## 8. Surface libraries

Rules (README): chapter-to-chapter files; statements in the book's generality (real matrices,
`ℝⁿ`, real bilinear forms); each proof a specialization of a backbone result, through equivalence
lemmas for book-specific definitions; no new mathematics — anything that does not specialize is a
demand on the backbone and goes into this plan. The per-book surface plans in ``
refine the tables below theorem by theorem.

### 8.1 `SaadSparse` (Surface/SaadSparse/ChNN/*.lean)

| Book location | Surface file | Backbone items used | Surface-specific definitions (need equivalence lemmas) |
|---|---|---|---|
| §1.8–1.9 normal/Hermitian matrices (Thm 1.7–1.9 spectral facts) | `Ch01/Spectral.lean` | Mathlib `Matrix.IsHermitian.eigenvalues`, spectral theorem; Schur form phase 3 (4.5) | `Matrix.IsNormal`? (Mathlib has `IsStarNormal`) |
| §1.11 Thm 1.34–1.35 (positive definite, Bendixson) | `Ch01/PositiveDefinite.lean` | 2.1.4, 2.1.14, 4.1 | Saad's "positive definite" = `IsCoercive` of `toEuclideanLin`; `Matrix.symmPart`/`skewPart` |
| §1.12 Lemma 1.36, Prop 1.37, Thm 1.38, Cor 1.39 (projectors) | `Ch01/Projectors.lean` | 2.1.7, Mathlib `starProjection_minimal` | matrix projector `V (Wᴴ V)⁻¹ Wᴴ` via `LinearMap.obliqueProjectionOfBases` |
| §1.13 (1.76) perturbation, `κ(A)` | `Ch01/Conditioning.lean` | 2.1.2, 2.2 | `κ_p` for matrix `p`-norms (scoped instances) |
| §4.1 Jacobi/GS/SOR/SSOR matrices (4.5)–(4.27) | `Ch04/Splittings.lean` | 2.3.2 | `(jacobiSplitting A h).iterationOperator` with `jacobiSplitting_iterationOperator` etc. |
| §4.2 Thm 4.1–4.4, Cor 4.2 | `Ch04/Convergence.lean` | 2.1.3, 2.1.11, 2.3.1, 2.3.4 (phase 2) | real matrices via `complexify` |
| §4.2.3 Thm 4.6–4.9 diagonal dominance | `Ch04/DiagDominant.lean` | 2.3.3 | irreducible variant (phase 2) |
| §4.2.4–4.2.5 Thm 4.10–4.16 SPD/SOR/Young | `Ch04/SPD.lean` | 2.3.5 (phase 2) | consistent ordering, Property A (surface-only) |
| §5.1–5.2 Prop 5.1–5.7 | `Ch05/Projection.lean` | 2.4.1–2.4.2 | matrix form `x = x₀ + V (Wᵀ A V)⁻¹ Wᵀ r₀` (5.7) with the equivalence to `IsPetrovGalerkin` |
| §5.3 Lemma 5.8, Thm 5.9–5.10, Alg 5.2–5.4 | `Ch05/OneDimensional.lean` | 2.4.3 | — |
| §5.4 Alg 5.5–5.6 | `Ch05/Additive.lean` | 2.4.4 (phase 2) | — |
| §6.2 Prop 6.1–6.2 | `Ch06/Krylov.lean` | 3.1 | `Matrix` Krylov space `𝒦_m(A, v)` as a `Submodule ℝ (n → ℝ)` |
| §6.3 Alg 6.1–6.3, Prop 6.4–6.6 | `Ch06/Arnoldi.lean` | 2.1.13, 3.2 | Alg 6.2 (MGS) and 6.3 (Householder) as functions with equality to `Arnoldi.vec` in exact arithmetic |
| §6.4 (6.16)–(6.18), Prop 6.7, Alg 6.4–6.6 (FOM, restarted, IOM) | `Ch06/FOM.lean` | 3.4–3.5 | `FOM.iterate` := `x₀ + V_m H_m⁻¹ (β e₁)` with `IsGalerkinIterate` |
| §6.5 (6.27)–(6.47), Prop 6.9–6.12, Alg 6.9–6.13, Thm 6.30 | `Ch06/GMRES.lean` | 3.4–3.6, 3.10 | `GMRES.iterate` (least-squares form) with `IsMinResIterate`; breakdown/stagnation |
| §6.5.7–6.5.8 Prop 6.13–6.17, Lemma 6.18 | `Ch06/Relations.lean` | 3.6 | — |
| §6.6 Alg 6.15, Thm 6.19; §6.7 Alg 6.16–6.19, Prop 6.20; §6.7.3 | `Ch06/Lanczos.lean`, `Ch06/CG.lean` | 3.3, 3.7 | D-Lanczos (`LDLᵀ`) equals CG |
| §6.8–6.9 Alg 6.20–6.22, Lemma 6.21 | `Ch06/CR.lean`, `Ch06/GCR.lean` | 3.8 | ORTHOMIN(k)/ORTHODIR as functions; only the full versions satisfy the spec |
| §6.10 Lemma 6.22–6.24 Faber–Manteuffel | `Ch06/FaberManteuffel.lean` | surface-only (phase 3) | — |
| §6.11 Thm 6.25–6.29, Lemma 6.26–6.27, Prop 6.32, Cor 6.33 | `Ch06/Convergence.lean` | 2.1.9, 3.9–3.10 | complex ellipse results (phase 3) |
| §6.12 block methods | — | phase 3 | — |
| Ch. 7–9 | `Ch07..Ch09/` | 3.12 (phase 2) | — |

Restarted and truncated variants (GMRES(m), IOM, DIOM, ORTHOMIN(k)) are functions in the surface;
GMRES(m) satisfies the per-cycle specification and its convergence theorem is backbone (3.10),
truncated methods are algorithm-only (1.2).

### 8.2 `FongSaunders` (Surface/FongSaunders/SecN.lean)

| Paper | Surface file | Backbone items |
|---|---|---|
| §1–1.1 setting, Lanczos, Table 2.1 (CG, CR) | `Sec1.lean`, `Sec2.lean` | 3.3, 3.7, 3.8 — the paper's CG/CR are literally `CG.iterate`/`CR.iterate` with `x₀ = 0`, `A : Matrix n n ℝ` symmetric positive definite (`Matrix.PosDef`), via 2.1.14 |
| §2.1–2.2 minimization properties (2.1)–(2.2) | `Sec2.lean` | 2.4.2, 3.4 (`IsGalerkin.iff_energyNorm_min`, `norm_residual_eq_iInf`) |
| Thm 2.1–2.5 | `Sec2.lean` | 3.8 (Thm 2.1–2.2), 3.11 (Thm 2.3–2.5) |
| §3 backward errors (3.1)–(3.6), Thm 3.1, stopping rules | `Sec3.lean` | 2.2 (`isLeast_backwardError`), 3.11 |
| §4.1 numerics — no theorems; §4.2 (4.1) FOM/GMRES relation; Steihaug indefinite | `Sec4.lean` | 3.6, 3.11 |
| §5 Table 5.1 | `Sec5.lean` | restatement of all of the above as one `structure` of properties per method |

Surface-specific: Frobenius norm `‖A‖_F` in the backward-error formula (equality with the operator
norm for the rank-one optimal perturbation; state both), `x₀ = 0` throughout, real symmetric
matrices; the strict-monotonicity forms of the paper's theorems are surface corollaries of the
non-strict backbone statements (3.11); `CG.alpha/beta`, `CR.alpha` are exposed for the paper's
coefficient formulas.

### 8.3 `AtkinsonHan` (Surface/AtkinsonHan/ChNN/*.lean)

| Book | Surface file | Backbone items |
|---|---|---|
| Thm 2.3.1, Cor 2.3.3, Thm 2.3.4–2.3.5 | `Ch02/GeometricSeries.lean` | 2.1.1 |
| Thm 2.4.1–2.4.5 (Banach–Steinhaus), §2.4.4 quadrature convergence, (2.4.1) `cond(L)` | `Ch02/Operators.lean` | Mathlib `banach_steinhaus`; 2.2; 5.1.4 (phase 3) |
| §2.5 Hahn–Banach, Riesz | `Ch02/Functionals.lean` | Mathlib |
| Thm 3.3.12–3.3.21, Lemma 3.4.1–Thm 3.4.7, Prop 3.6.9, Ex 3.6.7, Lebesgue lemma | `Ch03/BestApprox.lean`, `Ch03/Projections.lean` | 5.1.1 |
| Thm 3.7.1–3.7.3 (Jackson etc.) | — | phase 3 |
| Thm 5.1.3–5.1.4, 5.2.1, Ex 5.1.2, (5.1.11) | `Ch05/FixedPoint.lean` | 5.3.1 |
| §5.2.2 linear systems | `Ch05/LinearIteration.lean` | 2.3.1–2.3.3 |
| Thm 5.2.2–5.2.4 (Urysohn, Volterra, Picard) | `Ch05/IntegralEquations.lean` | phase 3 |
| Thm 5.4.1–5.4.2 | `Ch05/Newton.lean` | 5.3.2 |
| Thm 5.6.1–5.6.3 (CG for operator equations) | `Ch05/ConjugateGradient.lean` | 3.7, 3.10 with the compression trick (3.9, 5.2.3); Winther (5.6.2) phase 2 |
| Thm 8.2.1, 8.2.4, 8.2.7–8.2.8; Thm 8.3.1–8.3.4; Thm 8.7.1 | `Ch08/Existence.lean`, `Ch08/LaxMilgram.lean` | 5.2.1–5.2.2 |
| Prop 9.1.3, Cor 9.1.4, Thm 9.2.1, Rem 9.2.2, Cor 9.2.3, Thm 9.3.1 | `Ch09/Galerkin.lean`, `Ch09/PetrovGalerkin.lean`, `Ch09/Strang.lean` | 5.2.3 |
| §9.4 CG variational | `Ch09/CG.lean` | 3.7 via `SesqForm.toOperator` |

Surface-specific definitions: real bilinear forms `a : V → V → ℝ` with `IsBoundedBilinearMap`
(equivalence with `V →L[ℝ] V →L[ℝ] ℝ`, which is `SesqForm ℝ V` by definition), "V-elliptic",
"strongly monotone", `‖·‖_a`, AH's "projection operator" (Def 3.6.3) = `IsIdempotentElem` on
`V →L[𝕜] V`. Out of scope for this surface: the Banach closed range theorem, Algorithm 2
(nonlinear CG), everything needing Sobolev spaces (1.7).

### 8.4 Parked demands from the other five sources
* **Choi**: 3.12 `Singular` (pseudoinverse solutions, MINRES-QLP), `Lanczos` termination bounds;
  everything else specializes 3.3–3.6.
* **Meurant–Strakoš**: 3.12 `OrthogonalPolynomials`; §3 identities are in 3.7 (HS 6:1/6:3) and
  2.1.5; §4–5 finite precision in §6.
* **Saad-eig**: §4 (theorem numbers integrated there); shares Ch. 1 with `SaadSparse/Ch01`, §4.3
  with 2.4/2.1.6, §4.4 with 2.1.9, Ch. 6 with 3.1–3.3; Ch. 3 analytic perturbation theory
  (Riesz–Dunford) and Ch. 7–9 are phase 3.
* **Kress**: Ch. 3 → 2.1.1, 2.3.1, 5.1.1, 5.3.1; Ch. 4 → 2.3.2–2.3.5 (Kress is the second source
  for Young's theory and the two-grid Thm 4.18 — the latter surface-only); Ch. 5 → 2.2 plus SVD/
  pseudoinverse/Tikhonov (Thm 5.4–5.10: Mathlib has `LinearMap.singularValues` but no SVD
  factorization — an upstreaming candidate under `Numlib/Matrix/` in phase 3); Ch. 6 → 5.3;
  Ch. 7 → 4.1–4.3, 4.5; Ch. 8–12 (interpolation, quadrature, IVP/BVP, integral equations) phase 3.
* **Higham**: §6 plus 2.2 (Rigal–Gaches); Ch. 8–10, 19 surface.

---

## 9. Difficult-proof index

| # | Result | Where | Approach / reference |
|---|---|---|---|
| D1 | `ρ(a) < 1 ↔ aⁿ → 0` in complex Banach algebras | 2.1.3 | Gelfand's formula in Mathlib (`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`); `⇐` via `spectralRadius_pow_le`. The converse fails in ∞-dim for pointwise convergence; keep the norm version. Kreyszig §7.5 |
| D2 | Chebyshev min–max on `[a,b]` | 2.1.9 | affine change of variables + Mathlib `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one` (k = 0); parity avoided via `q.comp (-X)`; Rivlin *Chebyshev Polynomials* Thm 1.10 |
| D3 | `‖p(A)x‖ ≤ max_{σ(A)} |p| ‖x‖`, energy-norm version | 3.9 | `LinearMap.IsSymmetric.eigenvectorBasis` expansion (finite-dim), transported to Hilbert spaces by the compression trick (2.1.6); CFC form in phase 2. Saad Lemma 6.28/6.31 |
| D4 | Arnoldi vectors = `gramSchmidtNormed` of the Krylov sequence | 3.2 | induction on positive leading coefficients; or define by recursion and prove equality; the one-dimensional space `𝒦_{j+2} ⊓ 𝒦_{j+1}ᗮ` for the recurrence form. Saad Prop 6.4–6.5 |
| D5 | Independence of `v, …, A^{m−1}v` for `m ≤ grade` | 3.1 | minimality of `grade` with `linearIndependent_iff'`. Saad Prop 6.2 |
| D6 | CG invariants ⇒ Galerkin | 3.7 | bundled `CG.Invariant k` induction; Saad Prop 6.20; Hestenes–Stiefel 1952 §5 |
| D7 | Cullum–Greenbaum harmonic relation without Givens | 3.6 | residual smoothing (Weiss 1994; Saad Lemma 6.18) + uniqueness of minimal residual, with `Krylov.map_subspace_succ_eq_sup_span`; Cullum–Greenbaum 1996 |
| D8 | Fong–Saunders sign lemma and monotonicity | 3.8, 3.11 | finite termination; orthonormal expansion in `{A p_i}`; Fong–Saunders 2012 Thm 2.2; Steihaug 1983 |
| D9 | Kantorovich inequality | 2.4.3 | spectral theorem + convexity of `t ↦ 1/t` on the convex hull of the spectrum, via the compression to `span{x, y}`; Saad Lemma 5.8; Householder 1964 |
| D10 | Gauss–Seidel convergence under diagonal dominance | 2.3.3 | eigenvector argument (Saad Thm 4.9); Jacobi via `‖·‖_∞` |
| D11 | Complex Lax–Milgram | 5.2.2 | closed-range argument (`AntilipschitzWith` ⇒ closed range) or real parts on `rclikeToReal`; AH Thm 8.3.4 proof #2 |
| D12 | Rigal–Gaches optimal perturbation | 2.2 | rank-one construction `r ⊗ y/‖y‖²`; Higham Thm 7.1 |
| D13 | Minimum-norm Krylov solution | 3.4 | `range A ≤ (ker A)ᗮ` for symmetric `A`; Choi Thm 2.25 |
| D14 | Power method via generalized eigenspaces + Gelfand | 4.3 | `Module.End.iSup_maxGenEigenspace_eq_top`; avoids Jordan form. Saad-eig Thm 4.1 |
| D15 | Newton local quadratic convergence | 5.3.2 | The sharp constant `L/2` needs the integral form, `image_norm_le_of_norm_deriv_right_le_deriv_boundary` with boundary `B t = C‖y−x‖²t²/2`, packaged as `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le` in `Analysis/Calculus/MeanValue`. It costs **no** extra instance arguments: introduce `NormedSpace ℝ F` inside the proof by `restrictScalars`, as Mathlib's own mean value lemmas do. `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` takes only a constant bound and loses the `1/2`. AH Thm 5.4.1; Ortega–Rheinboldt 10.2.2 |
| D16 | Courant–Fischer | 4.2 | dimension counting on `S ⊓ span{u_k..u_n}`; Horn–Johnson Thm 4.2.6 |
| D17 | `WithEnergy` inner-product instance and its completeness | 2.1.5 | `InnerProductSpace.Core` on a type synonym, following Mathlib's `Matrix.toInnerProductSpace`: the plain `AddCommGroup`/`Module` instances are local to the defining section, only the core-derived normed instances are global, `WithEnergy.equiv` is defined afterwards with `rfl` fields; norm equivalence and `continuous_equiv` need `A : E →L[𝕜] E` |
| D18 | Subspace iteration in Saad-eig's generality (Thm 5.2) | 4.3 | **done, and overestimated twice over**: no Gelfand (the elementary decay estimate of D14 covers it) and no gap API (the theorem is per-eigenvector). Spectral projector onto the dominant generalized eigenspaces + one candidate vector in `A^k S₀`. The gap form is a separate, strictly stronger theorem, `Krylov.gap_subspaceIterate_le`, still open |
| D19 | Householder–John / Ostrowski–Reich in operator form | 2.3.5 | Rayleigh-quotient identity for an eigenpair of `M⁻¹N` (Kress Thm 4.12 proof) generalizes verbatim with `M + Mᴴ − A` coercive; Saad Thm 4.10 |
| D20 | Kato's lemma `‖1 − P‖ = ‖P‖` | 2.1.7 | **not difficult after all**: the exchange trick on `x = P x + (1 − P) x`, rescaling the two components so as to swap their norms (`norm_smul_add_smul_eq_norm_add`). No gap API, no adjoints, no completeness. The minimal-gap route and the `T = P + P⋆ − 1` shortcut are both unnecessary; 2.1.7 records why the latter stops at inequalities. Szyld 2006 |
| D21 | Givens residual identities (the `γ_m`, `s_m`, `c_m` formulas for `‖r^G_m‖`) | 3.5 | All rest on "a unitary matrix is a Euclidean isometry", `‖U *ᵥ v‖₂ = ‖v‖₂`, which Mathlib lacks; it is three lines through `Matrix.toEuclideanCLM` as a star-algebra equiv (2.1.14). Then the residual splitting from `rotated_last_row` and the diagonal of the triangular factor. No block decomposition of the rotation product is needed, and `norm_residual_eq_div_norm_givensC` needs no `c_m ≠ 0`: at `c_m = 0` its Galerkin hypothesis is contradictory. Saad §6.5.3 |

---

## 10. Extensibility

* **A second Krylov book** (Greenbaum; Liesen–Strakoš; van der Vorst; Trefethen–Bau Lectures
  32–38): everything is stated against 3.4's specs and 3.5's transport, so a new implementation
  (GMRES with Householder, BiCGStab, LSQR) only needs "algorithm ⇒ spec" plus the spec-level
  theorems. LSQR/LSMR (Fong's thesis, Table 5.2) are CG/MINRES on `AᵀA` — provide
  `Krylov/NormalEquations.lean` as the instance in phase 2.
* **A finite-element book** (Brenner–Scott, Ern–Guermond): 5.2 is stated for abstract Hilbert
  spaces and closed subspaces, so only Sobolev spaces are missing (not in Mathlib), plus the
  form-based energy space of 1.7.
* **An optimization book** (Nocedal–Wright): CG as a minimizer of a quadratic (2.4.2, the energy
  functional) is the bridge; convex conjugates/Fenchel (README example) would go into a new
  `Numlib/Convex/` layer next to `Nonlinear/`.
* **Finite-precision papers** (Paige, Greenbaum, Meurant–Strakoš §4–5): §6's perturbed-relation
  structure is the hook; exact results are written so that `ε = 0` recovers them.
* **Naming discipline for discoverability**: specs are `Is…` predicates (`IsMinRes`,
  `IsGalerkin`, `IsPetrovGalerkin`, `IsMinError`, `IsRitzPair`, `IsBestApprox`,
  `IsGalerkinSolution`, `IsPetrovGalerkinSolution`); algorithms are namespaces with
  `State`/`step`/`iterate` (`CG`, `CR`, `Arnoldi`, `Lanczos`, `Stationary`, `Newton`); hypotheses
  are bundled in `LinearMap.Is…` (`IsCoerciveWith`, `IsSymmetricCoercive`, `IsSymmetricBoundedBy`)
  or `SesqForm.Is…`; Mathlib-shaped lemmas keep Mathlib's naming (`norm_…_le`, `…_iff_…`,
  `exists_…`).

---


## 11. Addendum: the quasi-minimal-residual layer (`Numlib/Krylov/QuasiMinRes`, phase 2)

Added when Saad Ch. 7–9 were planned (`plans/saadsparse-ch7-9.md`,
`plans/proposals/saad-ch7-9.md`). It is the only backbone module that slice needed beyond
`Krylov/{BiLanczos,NormalEquations,Preconditioned}` and `LinearSolve/Projection/Additive`, and it
exists for two reasons.

**A Hessenberg relation needs two families.** `Krylov.HessenbergRelation A v h` (3.5) says
`A v_j = ∑_{i ≤ j+1} h_ij v_i` with one sequence. Flexible GMRES satisfies `A z_j = ∑ h_ij v_i`
with `z_j = M_j⁻¹ v_j` an unrelated sequence (Saad (9.22)), and TFQMR satisfies
`A u_j = ∑ r_i (B̄)_ij` with the residual vectors on the right (Saad (7.70)); neither is an
instance of the one-family structure. `Krylov.HessenbergRelation₂ A z v h` — iterate basis on the
left, residual basis on the right — covers both, and `HessenbergRelation` is its diagonal case.
The natural home for it is `Krylov/Hessenberg`, and moving it there (redefining
`HessenbergRelation` as `HessenbergRelation₂ A v v`) is a restatement task that must run alone;
until then it lives in the new module.

**Quasi-minimal residual is a specification, not an implementation.**
`Krylov.IsQuasiMinResIterate z h β x₀ m x` — "`x = x₀ + Z_m y` with `y` minimizing
`‖β e₁ − H̄_m y‖₂`" — is what `Krylov.IsMinResIterate` (3.4) becomes when the residual basis is
not orthonormal, and it is satisfied by QMR (Saad Alg. 7.4), TFQMR (Alg. 7.8), QGMRES/DQGMRES
(Alg. 6.12–6.13) and FGMRES (Alg. 9.6). It is the one place where §1.2's rule "specifications are
backbone" applies to a method that minimizes *the wrong thing*: the theorems say how wrong. Three
of them are each proved twice in the book:

* `‖b − A x‖ ≤ C ‖γ_m‖` when `‖∑ w_i v_i‖ ≤ C ‖w‖₂` (so `C = √(m+1)` for unit vectors) — Saad
  Prop 7.3, (6.51), (7.83);
* `‖r^Q_m‖ ≤ (C/c) ‖r_m‖` when also `c ‖w‖₂ ≤ ‖∑ w_i v_i‖` — Saad Thm 7.4 and Thm 6.11, with
  `C/c = κ₂(V_{m+1})`. The proof is `‖V t^Q‖ ≤ C‖t^Q‖ ≤ C‖t‖ ≤ (C/c)‖V t‖`; the Gram–Schmidt
  factorization of `V_{m+1}` that the book's proof builds, and the full-rank hypothesis it
  assumes, are both unnecessary. This is why the module pays for itself: Theorem 6.11 was
  estimated at 60 lines of surface work in `saadsparse-ch6.md` §R31 and left unformalized;
  through this lemma it and Theorem 7.4 are corollaries.
* with an orthonormal residual basis and an arbitrary iterate basis, the quasi-minimal-residual
  iterate minimizes the true residual over `x₀ + span z` — Saad Prop 9.2 (FGMRES).

The harmonic relations (Saad (7.23)–(7.24), Prop 7.5, the analogues of (6.65)–(6.67) and Prop
6.15) are stated here in pure Givens form, about `Krylov.gamma` and `Krylov.givensC` alone, since
the versions in `Krylov/Relations` (3.6) are about true residuals and assume orthonormality.

Phase 2 accordingly gains one group, `Krylov/QuasiMinRes`, and the following open nodes appended
to finished groups (see `plans/proposals/saad-ch7-9.md` §1 for the statements): the three
`WithEnergy` self-adjointness facts of Saad §9.2.1 in `Analysis/InnerProductSpace/Energy`
(`M⁻¹A` symmetric for `⟪·,·⟫_M` and for `⟪·,·⟫_A`, `A M⁻¹` for `⟪·,·⟫_{M⁻¹}`); the shifted-skew
Arnoldi identity `h_ij + conj h_ji = c δ_ij` in `Krylov/Arnoldi`, which with the existing
`Arnoldi.coeff_eq_zero_of_adjoint_mem` (`s = 2`) is the whole of Saad (9.29) and the
Concus–Golub–Widlund tridiagonal; the Schur-complement coercivity
`Bᴴ ∘ A⁻¹ ∘ B` symmetric coercive in `Analysis/InnerProductSpace/Coercive`, which is the
mathematical content of Saad Cor 8.1 (Uzawa) and the hook for a later Stokes or finite-element
source; and the split/right preconditioned CG equivalences of Saad §9.2.1 in
`Krylov/Preconditioned`.

Not planned, for want of a second consumer or of Mathlib support: a saddle-point module
(`LinearSolve/SaddlePoint`) — Saad §8.4 is the corpus's only source for Uzawa and Arrow–Hurwicz,
so by §1.2 the recurrences stay in the Saad surface and only the Schur-complement lemma is
backbone; a perturbed fixed-point theorem for inexact Uzawa (Saad P-8.9); and the singular
value decomposition that Saad §8.1's `±σ_i` spectrum needs
(`LinearAlgebra/Matrix/SVD` is phase 3).

---

---

## 12. The sparse-matrix and model-problem layers (Saad Ch. 1-4, the parts phase 1 left out)

Added with the plan of Saad §1.1-§1.10, Ch. 2, Ch. 3 and §4.3 (`plans/proposals/saadlow.md` holds
the coverage table and the skip list). Five arguments are worth keeping here, because they decided
where the new modules sit.

### 12.1 Nonnegative matrices are one theory in two places, on purpose

`Numlib/LinearAlgebra/Matrix/PerronFrobenius` holds the order-monotonicity results (Saad
Prop 1.24 clause 5, Cor 1.27, Thm 1.28) and the *irreducible* Perron-Frobenius theorem (Thm 1.25);
`Numlib/LinearSolve/Stationary/RegularSplitting` keeps the *weak* Perron theorem, Thm 1.29 and
`Matrix.IsMMatrix`. That split is not tidy and §1 of the proposal asks for it to be undone by
moving the latter three up. It is nevertheless sound as it stands, and the reason is worth
recording: the irreducible theorem does **not** imply the reducible one cheaply. Perturbing to
`A + εJ` and letting `ε → 0` needs continuity of the spectral radius in the entries, which nothing
in the library has; the resolvent argument planned in `RegularSplitting` (`(r - B)⁻¹ ≥ 0` for
`r > ρ(B)`, normalize, extract a convergent subsequence) is a genuinely different proof. Neither
module is redundant. What is *not* acceptable is a `LinearAlgebra/Matrix` module importing
`LinearSolve`, which is why `PerronFrobenius` was written to depend on `Matrix/Order` and
`Matrix/Complexify` alone.

The Perron eigenvector is proved by Collatz-Wielandt maximization rather than by the resolvent,
because the positivity of the eigenvector - which is the whole content of the irreducible case -
comes out of `(1 + A) ^ (n - 1) > 0`, and that same lemma is the kernel of Saad's Problem P-3.12
about structural inverses.

### 12.2 The model problem is a Kronecker sum of tridiagonal Toeplitz matrices

`Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz` and `KroneckerSum` exist because the matrices of
Saad Ch. 2 are cited by every later chapter and by every other book in the corpus, while the book
states almost nothing about them: it gives the spectrum of the block `tridiag(-1, 4, -1)` of (2.27)
and of nothing else - not of the one-dimensional Laplacian, not of the two-dimensional five-point
matrix. Both follow from one trigonometric identity and one tensor argument, and the payoff is out
of proportion to the cost: the `O(h⁻²)` condition number that motivates preconditioning, the
spectral bounds every Chebyshev estimate of Ch. 6 is instantiated at, and the positive definiteness
that Ch. 4's SPD theorems need, all become computations rather than assumptions.

The two modules are separate because the Kronecker sum is a general construction with a general
statement ("eigenvalues of a Kronecker sum add") whose natural Mathlib home is beside
`Matrix.Kronecker`, while the sine basis is specific to the tridiagonal Toeplitz family. Neither
module knows what a partial differential equation is; the claim that these matrices *discretize*
anything is surface material, and Saad's derivation of them is not formalized at all.

### 12.3 Graph theory is entered through Mathlib's vocabulary, not through matrices

Saad Ch. 3's reorderings rest on three facts about a finite simple graph that Mathlib does not
have: greedy colouring uses at most `maxDegree + 1` colours, a maximal independent set has at least
`card V / (1 + maxDegree)` vertices, and the distance spheres around a root separate the graph.
They are stated in `Numlib/Combinatorics/SimpleGraph/{Coloring,IndepSet,LevelSet}` with no matrix
in sight, so that each can be upstreamed on its own; the matrix consequences - block
tridiagonality of a level-set ordering, diagonal diagonal blocks of a multicolour ordering, the
form (3.3) of an independent-set ordering - are `Numlib/LinearAlgebra/Sparse/Reordering`, and they
are stated for the *labelling*, never for the algorithm that computes it. No traversal is
formalized anywhere, and none needs to be: Algorithms 3.1-3.6 produce labellings with the stated
property, and the theorems are about the property.

Two modelling points the book forces, both settled in `Numlib/LinearAlgebra/Sparse/Pattern`. Saad's
adjacency graph is directed and has self-loops at the nonzero diagonal entries, so it is a
`Digraph`; `SimpleGraph` carries only the symmetrized loopless graph that §3.3.3 acts on, and both
are defined so that no downstream statement has to choose. And every claim about the pattern of a
product assumes away numerical cancellation: the unconditional half is what is stated, and the
converse is cited from Mathlib for entrywise nonnegative matrices. Saad's irreducibility, which
applies to arbitrary matrices unlike Mathlib's, is `Matrix.IsPatternIrreducible`, defined once here
rather than inline in two surfaces.

### 12.4 ADI is a Cayley transform, and needs no commutativity

Saad §4.3 states no numbered result and asserts its convergence claim in one sentence. The claim is
a theorem, and `Numlib/LinearSolve/Stationary/ADI` proves it from a single inequality: for `A`
symmetric with `re ⟪A x, x⟫ ≥ c ‖x‖²` and `r > 0`,

  `‖A x - r x‖² + 4 r c ‖x‖² ≤ ‖A x + r x‖²`,

which is the expansion of both sides. It says the Cayley transform `(A - r)(A + r)⁻¹` is a strict
contraction with an explicit factor, and the Peaceman-Rachford operator (4.50) is conjugate to a
product of two of them. Three things fall out that the literature's framing obscures: the
commutativity of `H` and `V` is not used anywhere (it belongs to the theory of the optimal
parameter *sequence*, which the book only cites); the splitting identity (4.52) `M - N = H + V`
needs no commutativity either, the `H V` terms cancelling; and the statement holds in any inner
product space, matrices entering only through `Matrix.toEuclideanCLM`. The Cayley inequality is an
upstreaming candidate in its own right and should move to
`Numlib/Analysis/InnerProductSpace/Coercive` as soon as a second consumer appears.

### 12.5 Where the corpus stops being numerical analysis

Saad Ch. 2 is the sharpest test of the scope rule, and the answer is cleaner than expected. The
chapter's finite element section states no Céa lemma, no Lax-Milgram theorem, no Poincaré
inequality, no trace theorem and no convergence result, and it uses no property of `H¹(Ω)`: the
Sobolev framing is decorative, and **no Sobolev theory is needed to formalize anything the chapter
proves**. Its algebraic content - bilinearity, the nodal basis, the Galerkin reduction, the
symmetry and positive definiteness of the stiffness matrix, the assembly `A = ∑ P_e A_{K_e} P_eᵀ` -
is already in `Numlib/Variational/{Forms,Galerkin}` in abstract form, where the stiffness matrix is
the Gram matrix of a basis in the energy inner product. What is missing is only the concrete space:
a triangulation of a planar domain, piecewise-affine functions on it, integration over triangles,
and Green's formula on a domain with a smooth boundary. That is plane geometry and measure theory,
not numerical analysis, and it is where the chapter is left. The same line puts §2.1 (the partial
differential equations), §2.4 (mesh refinement) and §3.4-§3.7 (storage formats, sparse
matrix-vector products, direct-method heuristics) outside; the last group for a different reason,
that it states no theorem at all.

---

## 13. Fourier, wavelet and interpolation layers (Atkinson–Han Ch. 1–4)

Added when Atkinson–Han Chapters 1–4 were planned. The alignment is in
`atkinsonhan-ch1-4.md` and the requests against existing groups in
`proposals/atkinsonhan-ch1-4.md`.

**§0.2 and §1.7 are out of date on two points.** §0.2 says Atkinson–Han "Ch. 4, 7, 10, 13–14
(Fourier, Sobolev, FEM, BIE) are out of scope until Mathlib has Sobolev spaces". Chapter 4 uses no
Sobolev space; it uses `L¹`, `L²`, the Schwartz space, tempered distributions and the Fourier
transform, and Mathlib has all of them. §1.7's out-of-scope bullet lists "distribution theory" for
the same reason and is likewise false: `Mathlib.Analysis.Distribution.TemperedDistribution` gives
`𝓢'(E, F)` with its Fourier transform, and `Mathlib.Analysis.Fourier.LpSpace` gives Plancherel as a
linear isometry equivalence of `L²`. What remains out of scope in Chapter 4 is the Fourier-side
construction of general wavelets (§4.5 after Prop 4.5.2), which the book itself states without
proof.

### 13.1 `Analysis/Fourier/` (phase 3)

Three modules, all upstreaming candidates with natural home `Mathlib.Analysis.Fourier`.

`TrigonometricBasis.lean` — the *real* trigonometric system `1`, `√2 cos(2πnx/T)`, `√2 sin(2πnx/T)`
as a `HilbertBasis ℤ ℝ (Lp ℝ 2 haarAddCircle)`, the real coefficients `a_j`, `b_j`, the dictionary
to Mathlib's complex `fourierCoeff`, and Parseval in real form. Mathlib has only the complex
exponentials (`fourierBasis`), and every classical statement in the corpus — Atkinson–Han
Thm 1.3.13, (1.3.10), §3.7, (4.1.1)–(4.1.3), (4.1.13) — is about the real system. Completeness comes
from `span_fourier_closure_eq_top` through the real–complex dictionary, not from a second
Stone–Weierstrass argument.

`Dirichlet.lean` — the Dirichlet kernel with its closed form, the partial-sum operator
`fourierPartialSum`, its kernel representation, and **Dini's criterion** for pointwise convergence,
of which Atkinson–Han Thm 4.1.1 is an instance. This is the module that `Approximation/Trigonometric`
(5.1.5) should build `PeriodicCont.fourierProj` on; two definitions of the Dirichlet kernel would
be a duplication the plan is meant to prevent.

`DFT.lean` — `Matrix.dft`, the matrix `F_n` of Atkinson–Han §4.3, with `dft_eq_zmodDft` bridging to
Mathlib's `ZMod.dft` (from which the inversion theorem Thm 4.3.2 is free) and the radix-2 identity
`dft_radix_two`, which is the correctness statement of the fast Fourier transform. The algorithm
and its cost are not planned, by the rule that excludes purely algorithmic material.

### 13.2 `Analysis/Wavelet/` (phase 3)

`Haar.lean` and `Multiresolution.lean`: the Haar system on `L²(ℝ)` — scaling functions, scaling
spaces, wavelet, wavelet spaces, decomposition and reconstruction (Atkinson–Han Thm 4.4.1–4.4.4) —
and Definition 4.5.1 as a bundled interface with the Haar system as its instance. Nothing here is
in Mathlib. The unitary dilation `MeasureTheory.Lp.dilationₗᵢ` is defined in `Haar.lean` because
Mathlib has `Lp.compMeasurePreserving` and nothing for a scaling.

Difficult proof: `Haar.topologicalClosure_iSup_V` (Thm 4.4.1 (4)), density of `⋃ V_j` in `L²(ℝ)`.
Route: continuous compactly supported functions are dense (Mathlib), then uniform continuity gives
an explicit `L²` bound for the level-`j` dyadic step approximation. The route through measurable
sets approximated by dyadic unions is strictly harder and unnecessary.

The general wavelet construction — a scaling function from its dilation coefficients, the wavelet
of (4.5.4), Daubechies' compactly supported families — is **not planned**: the book states it
without proof, and the standard arguments need conditions on `φ̂` that would be a harmonic-analysis
project of their own.

### 13.3 `Analysis/Normed/Operator/Compact.lean` and `Analysis/Convex/Uniform.lean` (phase 2)

The compact-operator facts Atkinson–Han §2.8 needs and Mathlib does not have: a bounded finite-rank
operator is compact, an operator-norm limit of compact operators is compact, Schauder's theorem
(the adjoint of a compact operator on a Hilbert space is compact, proved by Arzelà–Ascoli rather
than by finite-rank approximation), the finiteness of the set of eigenvalues of modulus at least
`ε`, and the closed range of `λ - K` with the orthogonality `range (λ - K) = (ker (λ̄ - K*))ᗮ`.
Mathlib supplies the Fredholm alternative itself
(`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`) and the compact self-adjoint spectral
theorem. The Riesz ascent–descent theory (Thm 2.8.12 (3), (5), Thm 2.8.14 (1)) is **not planned**:
its only consumers in the corpus are results the book states without proof, one of which needs
contour integrals of operator-valued functions anyway.

`Analysis/Convex/Uniform.lean` is the Radon–Riesz property — weak convergence plus convergence of
norms gives norm convergence — in a uniformly convex space and, separately, in an inner product
space, Atkinson–Han Exercises 2.7.3 and 2.7.4 (c). The weak-convergence hypothesis is written in
the same shape as `Analysis/Normed/Module/WeakDual`'s, so that the two compose.

### 13.4 `Approximation/{Unisolvent,Hermite,OrthogonalPolynomial}.lean` (phase 3)

`Unisolvent.lean` is Atkinson–Han's abstract interpolation problem (Def 3.2.1, Lemma 3.2.2,
Thm 3.2.3): `n` bounded functionals on an `n`-dimensional subspace, unique solvability, the
determinant criterion, and the interpolation operator. It is the frame in which the book settles
Lagrange, Hermite, trigonometric and moment interpolation at once, and it carries the bridge
`haarCondition_iff_isUnisolvent` to `Approximation/Chebyshev`'s Haar condition. It is separate from
`Approximation/Interpolation` (5.1.3), which is about the Lagrange *operator* and its Lebesgue
constant.

`Hermite.lean` is Hermite interpolation with multiplicities and its error formula, resting on a
Rolle theorem with multiplicities that strengthens the one `Interpolation.lean` plans for Lagrange.

`OrthogonalPolynomial.lean` is the family of orthogonal polynomials of a measure with finite
moments, its three-term recurrence, the truncated expansion as a best `L²(μ)` approximation
(Atkinson–Han (3.5.2)), and the Legendre and Chebyshev families with their orthogonality relations
((3.5.4)–(3.5.9)). It is what `Approximation/Quadrature`'s Gauss rules need and had no source for:
`Krylov/OrthogonalPolynomials` (3.12) owns the Lanczos polynomials of `⟪p(A)v, q(A)v⟫` and the
purely algebraic `Polynomial.christoffel_darboux`, which this module reuses rather than restates,
and `Approximation/Chebyshev` (5.1.2) owns the sup-norm min–max theory, which is a different inner
product. Lowest priority of the group: Atkinson–Han §3.5 states no numbered result.

*Corrected after the module was written.* Two claims here did not survive contact. The Chebyshev
orthogonality relations are **in Mathlib now** (`Polynomial.Chebyshev.measureT` and its family, and
Chebyshev–Gauss quadrature with it), so `integral_T_mul_T_div_sqrt` is two lines rather than a
development. And the reuse of `Polynomial.christoffel_darboux` does not typecheck as planned: that
node is stated for **orthonormal** polynomials (`p_{n+1} = (a_n X + b_n) p_n - c_n p_{n-1}`) while
`OrthogonalPolynomial.three_term_recurrence` is the **monic** one, so the two do not meet. Whoever
writes it should state it in the monic-with-weights form
`∑_{n ≤ N} p_n(x) p_n(t)/h_n = (p_{N+1}(x) p_N(t) - p_N(x) p_{N+1}(t))/(h_N (x - t))`, which both
specialize to, or plan the normalization bridge as a node of its own. `AtkinsonHan.Ch03.theorem_3_7_3`
is blocked on this and on nothing else.

One thing this module was expected to supply and does not: **the zeros of the orthogonal
polynomials**, which `Approximation/Quadrature`'s `exists_gauss` needs. They belong here; the
argument is the classical sign-change one against `integral_family_mul_of_degree_lt`, and its Lean
cost sits in "a real polynomial all of whose roots have even multiplicity has constant sign", for
which Mathlib appears to have nothing.

### 13.5 Surface

`NumlibSurface/AtkinsonHan/` gains `Chapter01/{Section01,02,03,05,06}`,
`Chapter02/{Section01,02,06,07,08,09}`, `Chapter03/{Section01,02,05}` and
`Chapter04/{Section01,…,Section05}` — 95 nodes. Chapter 1 is a thin chapter by design: it states
the book's numbered results and none of its definitions, because restating `NormedAddCommGroup`
under a book number would compete with Mathlib's name for a future agent's attention. Its one piece
of real content is Thm 1.3.13, which is 11.1's `trigBasis`.

---

## 14. Tree of contents, part V: variational inequalities, second-kind equations, finite differences

Added when Atkinson–Han Chapters 5 onward were planned out. Everything here is phase 3, and all of
it is stated in the Banach or Hilbert generality the sources use; the per-result alignment is in
`atkinsonhan-ch6-12.md` and the decisions that could not go into a group file are in
`proposals/atkinsonhan-ch5-onward.md`.

### 14.1 `Numlib/Analysis/Convex/` — convexity through directional derivatives, saddle points

`Analysis/Convex/Gateaux.lean` (upstreaming candidate, natural home `Mathlib.Analysis.Convex.Deriv`,
which today has only the one-dimensional statements). For `f : V → ℝ` on a convex set whose
directional derivatives are represented by `f' : V → V →L[ℝ] ℝ`: convexity, the gradient inequality
and monotonicity of the gradient are equivalent, with their strict forms, and a constrained
minimizer is characterized by a variational inequality — including the version with a second,
non-differentiable convex term (AH Thm 5.3.17–5.3.19 and Thm 11.2.1). The bounded-linear
representation is data, not derived: `HasLineDerivAt` gives one scalar per direction and does not
bundle it, and the book's Gâteaux derivative is required to be bounded linear. **These statements
already exist, proved, inside `NumlibSurface/AtkinsonHan/Chapter05/Section03.lean`**; the module is
their promotion, and the surface lemmas must be restated as its specializations in the same task
that writes it. That is the single largest duplication risk in this part of the plan.

`Analysis/Convex/SaddlePoint.lean`. `IsSaddlePoint L A B u p` for `L : α → β → ℝ` on bare sets, and
the minimax equality: the primal functional attains its least value at `u`, the dual functional its
greatest at `p`, and the two agree with `L u p` (AH Def 8.6.1, Prop 8.6.2, (8.6.11)–(8.6.14)). No
convexity anywhere; the only trap is the junk value of `sSup`/`sInf`, so both extremal statements
carry explicit boundedness hypotheses.

### 14.2 `Numlib/Analysis/InnerProductSpace/WeakCompactness.lean` — the one analysis prerequisite

Two statements Mathlib lacks: a bounded sequence in a Hilbert space has a weakly convergent
subsequence, and a closed convex set is sequentially weakly closed (Mazur). They are what AH
Thm 11.4.1 and 11.4.6 need, and they are reachable: the pinned Mathlib has the sequential
Banach–Alaoglu theorem `WeakDual.isSeqCompact_closedBall` for a **separable** normed space, and the
separability is removed by working in the closed span of the sequence and pushing the limit back
with the orthogonal projection. The **general Banach-space forms stay out of scope**: Mathlib has no
reflexivity class for Banach spaces and no Eberlein–Šmulian, so AH Thm 2.7.5, Thm 3.3.8, 3.3.10,
3.3.12, 3.3.14 and Thm 8.6.3 remain unplanned, as `Variational/Minimization.toml` already says. The
boundary is deliberate: everything the corpus needs happens in a Hilbert space.

### 14.3 `Numlib/Variational/Inequality/` — elliptic variational inequalities (AH Ch. 11)

`Inequality/Basic.lean`: `IsVariationalInequalitySolution A j f K u`, uniqueness and Lipschitz
dependence from strong monotonicity alone, existence for a strongly monotone Lipschitz `A` and a
convex lower semicontinuous `j` on a nonempty closed convex `K` (AH Thm 11.3.1), Stampacchia's
theorem as the case `j = 0`, the bilinear-form version, Minty's lemma, and the equivalence with a
constrained minimization problem when the operator comes from a symmetric form (AH Thm 11.2.2).
This generalizes §5.2.2 in two independent directions — a convex set instead of a subspace, and a
non-differentiable term — and `SesqForm.laxMilgram` is the corner where both degenerate.

The existence engine is `existsUnique_isMinOn_energy_add`: the unique minimizer of
`½ a(v,v) + j v − ℓ v` over a nonempty closed convex set of a Hilbert space. The book derives it
from its reflexive-space Thm 3.3.12; that route is unavailable and is not needed, because the
parallelogram law makes any minimizing sequence Cauchy — the argument behind Mathlib's
`exists_norm_eq_iInf_of_complete_convex` — and the convex lower semicontinuous `j` only needs an
affine minorant, which Mathlib has as `ConvexOn.exists_affine_le_of_lt` (AH Lemma 11.3.5).

`Inequality/Approximation.lean`: Falk's generalized Céa lemma (AH Thm 11.4.2), which is pure
algebra — strong monotonicity, Lipschitz continuity, Young's inequality, no topology and no limit —
and everything else in the module specializes it. Convergence of *internal* approximations needs no
weak compactness (AH Ex 11.4.2) and should be proved first; the general external case (AH Thm
11.4.1) is the only consumer of 11.2.

**Hypothesis shape.** Strong monotonicity and Lipschitz continuity are taken unbundled, in exactly
the form `Nonlinear/FixedPoint`'s `zarantonello` takes them, so that the two compose without a
translation lemma. A bundled `IsStronglyMonotoneWith` is now worth adding to `Nonlinear/FixedPoint`
(seven consumers); when it lands, both modules switch in one task.

### 14.4 `Numlib/Variational/AubinNitsche.lean` — duality error estimates

The Aubin–Nitsche argument (AH Thm 10.4.3) stated for two inner product spaces and a continuous
linear `ι : V →L[𝕜] H`, with no infimum, no supremum and no existence claim: given a Galerkin error
`e` orthogonal to `K` and a solution `φ` of the dual problem, `‖ι e‖² ≤ M ‖e‖ ‖φ − w‖` for every
`w ∈ K`. That is the whole content, and it is the one result of AH Chapter 10 that survives the
absence of Sobolev spaces. It belongs inside `Variational/Galerkin` and is a separate module only
because that group file was owned elsewhere when it was planned.

### 14.5 `Numlib/FiniteDifference/` — the Lax equivalence theorem (AH Ch. 6)

`FiniteDifference/LaxEquivalence.lean`: the abstract initial value problem `u' = L u` for a densely
defined `L : V →ₗ.[𝕜] V`, its solutions and well-posedness, the solution operators and the
generalized solution, consistency, stability, convergence, the equivalence theorem and the
convergence-order corollary. The theorem uses only `S 0 = 1`, a uniform bound on `‖S t‖` and strong
continuity, so it is stated for a family `S` rather than reconstructed from `L`, and the bridge from
the initial value problem is a separate node; **the semigroup property is recorded but is not a
hypothesis anywhere**. Both directions rest on `Analysis/Normed/Operator/BanachSteinhaus`: forward
through the density argument, backward through uniform boundedness.

`FiniteDifference/TwoLevel.lean`: one theorem, the error accumulation `‖u^m − v^m‖ ≤ M₀ T δ` for a
two-level recursion whose exact values carry a local truncation error (AH Thm 6.3.2). It is a
geometric-sum estimate with explicit constants; no mesh family, no limit, no order symbol.

The specific difference schemes are **not** planned, in either layer: the forward, backward and
Crank–Nicolson schemes for the heat equation are Taylor expansions of a solution assumed smooth plus
the maximum principle, they exercise nothing in the theory above, and formalizing them would be
partial differential equations.

### 14.6 Second-kind equations: `IntegralEquations/SecondKind`, `Operator/CollectivelyCompact`

The abstract theory of `(λ − K) u = f` and its approximations (AH Ch. 12), which is operator theory
in a Banach space with no kernel and no quadrature in sight. Two independent perturbation theorems:

* the **norm-convergent** case, where `‖K − K_n‖ → 0` and the geometric series theorem of §2.1.1
  suffices. This covers projection methods, because `‖K − P_n K‖ → 0` for compact `K` and pointwise
  convergent projections. AH Thm 12.1.2, with the two-sided estimate that makes `‖u − u_n‖` and
  `‖u − P_n u‖` tend to zero at exactly the same rate.
* the **collectively compact** case (Anselone), where `‖K − K_n‖` does not tend to zero but
  `‖(K − K_n) K_n‖` does. AH Thm 12.4.3; the geometric series is applied to a correction term and
  injectivity is upgraded to invertibility by the Fredholm alternative for the compact operator.
  This is the difficult item, and it is what makes the Nyström method analysable at all.

Also: Jacobson's identity for units (`λ − AB` invertible iff `λ − BA` is, AH Lemma 12.3.1), Sloan's
iterated projection solution with its error equation, and the two-grid iteration with its
contraction factor. `Analysis/Normed/Operator/CollectivelyCompact.lean` carries
`IsCollectivelyCompact` in the shape of Mathlib's `IsCompactOperator`, the Banach–Steinhaus fact
that a pointwise convergent family converges uniformly on compact sets, and the single composition
lemma `‖A_n ∘ M‖ → 0` for `A_n → 0` pointwise and `M` compact — which is AH Lemma 12.1.4 and
Lemma 12.4.7(3) at once, and which `Variational/ProjectionMethod` should import rather than
rederive.

### 14.7 `Numlib/Nonlinear/CompletelyContinuous.lean`

`IsCompactMap` for a nonlinear map, and one theorem: the Fréchet derivative of a completely
continuous operator is a **compact linear** operator (AH Prop 5.5.5). It is the bridge from a
nonlinear fixed point problem to §14.6, and AH §12.7 is its consumer. Brouwer, Schauder and the
rotation of a completely continuous vector field are not planned: Mathlib has none of them, the book
quotes all of them without proof, and building degree theory is algebraic topology.

### 14.8 What Chapter 7 does and does not change

§0.2 and §1.7 say Sobolev spaces are out of scope until Mathlib has them. That was re-checked
against the pinned Mathlib rather than repeated. The pinned version **does** have
`Mathlib/Analysis/Distribution/Sobolev.lean` — but that is `TemperedDistribution.MemSobolev`, the
Bessel potential spaces `H^{s,p}` on a finite-dimensional space, a predicate on tempered
distributions defined through the Fourier transform, together with the Gagliardo–Nirenberg–Sobolev
inequalities for compactly supported `C¹` functions. It has **no** weak derivative of an `L¹_loc`
function on an open set, no `W^{k,p}(Ω)` as a normed space, no `W^{k,p}_0`, no `H^{-s}`, no density
of smooth functions, no extension operator, no embedding or compact embedding theorem, no trace
operator, no Poincaré or Friedrichs inequality, and no divergence theorem beyond boxes. The scope
decision stands, and its reason is now precise. One item is closer than the rest and belongs with
`Approximation/Trigonometric` when that is written: the **periodic** Sobolev spaces `H^s(2π)` of AH
§7.5 are a weighted `ℓ²` space over the Fourier basis of `AddCircle`, need none of the domain
machinery, and would bring the trapezoidal rule for periodic integrands (Prop 7.5.6) and the
trigonometric interpolation error (Thm 7.5.7) with them.

---

## 15. Preconditioning, multigrid and domain decomposition (Saad Ch. 10–14)

*(Appended by the Saad Ch. 10–14 planning pass. The bare "§11" in §7's opening sentence points at an
earlier module inventory that has since moved into the TOML plan, not at this section.)*

Three layers are added by Saad, *Iterative Methods for Sparse Linear Systems*, Ch. 10, 12, 13 and 14.
The per-result alignment is `saadsparse-ch10-14.md`; the skip list and the coverage table are
`proposals/plan-saad10.md`. Chapter 11, and §12.1–12.2 and §12.4–12.7, contain no theorem and add
nothing.

### 15.1 What the layers are

* `LinearSolve/Preconditioner/` — the *manufacture* of `M`, as opposed to `Krylov/Preconditioned`,
  which consumes it. `ILU` (L4) holds the declarative predicate `Matrix.IsILU P A L U` and the
  existence theorem for M-matrices (Saad Thm 10.1–10.2, D22 below); `Polynomial` and `Chebyshev`
  (L1, L3 for the spectral bounds) hold polynomial preconditioning, the Neumann identity and
  Chebyshev acceleration; `ApproximateInverse` (L2 ring-level, L4 for the sparsity estimate) holds
  the Frobenius least-squares theory of Saad §10.5.
* `LinearSolve/Multigrid/` (L1, with `FiniteDimensional` for the adjoint) — the Galerkin coarse
  operator, the coarse-grid correction as an energy-orthogonal projector, the two-grid convergence
  theorem from a smoothing and an approximation property, and the FMG error bound.
* `LinearSolve/DomainDecomposition/` (L1 / L4) — the abstract Schwarz theory (a finite family of
  subspaces, `A_J = ∑ P_i`, `Q_s = ∏ (1 − P_i)`, Saad Thm 14.5–14.9) and the Schur complement
  reduction of §14.2 and §14.5.

Supporting upstreaming candidates, all L4: `LinearAlgebra/Matrix/SchurComplement` (the Schur
complement, its inverse block and the block LDU factorization; Mathlib has the determinant formulas
and the positive *semi*definite criterion but names no Schur complement),
`LinearAlgebra/Matrix/TridiagonalToeplitz` (the symmetric Toeplitz tridiagonal matrix and its sine
eigenbasis) and `LinearAlgebra/Matrix/KroneckerSum` (`A ⊗ 1 + 1 ⊗ B` and its spectrum). One more
sits beside the Chebyshev min–max module: `RingTheory/Polynomial/KernelPolynomial`, the `L²`
counterpart of 2.1.9.

### 15.2 The three decisions worth recording

* **Multigrid and Schwarz are one theory in the energy inner product.** Saad's coarse-grid
  correction `I − I_H^h A_H⁻¹ I_h^H A_h` (13.43) and his Schwarz projector `R_iᵀ A_i⁻¹ R_i A`
  (14.24) are both the `A`-orthogonal projector onto a subspace, so both are
  `Submodule.starProjection` in `WithEnergy A hA` (2.1.5). Lemma 13.1 and the self-adjointness
  computation opening §14.3.4 are then `starProjection`'s own properties, the subspace decomposition
  (13.59)–(13.61) is its range/kernel API, and Thm 13.3 and Thm 14.9 are four inequalities each.
  It is also why neither module mentions a mesh: the meshes are in the surface, where they
  instantiate the subspaces. A shared `WithEnergy.projection` is proposed for 2.1.5 so that the
  projector is defined once (`proposals/plan-saad10.md` §1.4).
* **The model problems are theorems, not folklore.** Saad §13.2's claims — that the spectral radius
  of a relaxation on the discrete Laplacean is `1 − O(h²)` while the oscillatory half of the
  spectrum is damped by a mesh-independent factor — rest on the eigen-decomposition of
  `tridiag(−1, 2, −1)`. That is elementary trigonometry (`sin((j−1)θ) + sin((j+1)θ) =
  2 sin(jθ) cos θ`, with the endpoint conditions supplying `θ_k = kπ/(n+1)`), and the 2-D case is
  the Kronecker sum. Mathlib has neither, so both are new modules; without them §13.2 would be a
  page of definitions with nothing behind them. No PDE theory is used anywhere in Ch. 13.
* **Hypotheses that cannot be verified algebraically are named, not proved.** Saad's smoothing and
  approximation properties (13.62)–(13.63), his FMG assumptions (13.49)–(13.51), and the Schwarz
  Assumptions 1 and 2 of §14.3.4 are all of this kind — they hold for finite-element discretizations
  of elliptic problems and are proved there, not here. Each becomes a `Prop`-valued bundle
  (`Multigrid.IsSmootherWith`, `Multigrid.IsApproximationWith`,
  `Schwarz.IsStableDecompositionWith`, `Schwarz.IsStrengthenedCauchySchwarzWith`), following 1.3.
  The one concrete verification the book gives, weighted Jacobi's smoothing property with
  `α = ω(2 − ωγ)` (Example 13.8), is a node.

  A subsidiary decision: Saad states (13.62)–(13.63) with the pair `‖·‖_{D⁻¹}`, `‖·‖_D` for the
  diagonal `D`. Carrying `D⁻¹` costs an invertibility hypothesis and buys nothing, so the backbone
  abstracts the only property the proof uses, `|⟪u, w⟫| ≤ q u · p w`, into
  `Multigrid.IsDualSeminormPair`, with the `D`/`D⁻¹` pair as an instance. `p = q = ‖·‖` then covers
  the textbook variants that measure the smoothing property in the Euclidean norm.

### 15.3 Additions to the difficult-proof index (§9)

| # | Result | Where | Approach / reference |
|---|---|---|---|
| D22 | ILU exists for an M-matrix and gives a regular splitting | 11.1 `Preconditioner/ILU` | Induction over the index set: one elimination step is the `1 × 1`-pivot Schur complement, Ky Fan's theorem (Saad Thm 10.1) keeps the M-matrix property, and dropping a nonpositive off-diagonal entry moves the matrix *up* in the entrywise order, where Saad Thm 1.33 recovers it. Needs `LinearAlgebra/Matrix/Order` and three M-matrix characterizations proposed for `Stationary/RegularSplitting`. Saad Thm 10.2; Meijerink–van der Vorst 1977 |
| D23 | `λmin(A_J) ≥ 1/K₀`, and the multiplicative Schwarz rate | 11.1 `DomainDecomposition/Schwarz` | Both rest on the vector-valued Cauchy–Schwarz inequality `∑ ⟪x_i, y_i⟫ ≤ (∑‖x_i‖²)^{1/2} (∑‖y_i‖²)^{1/2}`, which should be proved first; then `‖u‖² = ∑ ⟪u_i, P_i u⟫` and the stable decomposition. Saad Thm 14.7, Lemma 14.8, Thm 14.9; Dryja–Widlund, Xu |
| D24 | Eigen-decomposition of `tridiag(a, b, a)` | 11.1 `Matrix/Tridiagonal` | `sin((j−1)θ) + sin((j+1)θ) = 2 sin(jθ) cos θ`, with `sin 0 = sin((n+1)θ_k) = 0` supplying the boundary rows; orthogonality of the sine vectors makes the eigenpairs exhaustive. Saad (13.5)–(13.9) |

### 15.4 Phasing

Phase 2, alongside the rest of Saad Ch. 7–9: `LinearAlgebra/Matrix/{SchurComplement,Tridiagonal,
KroneckerSum}` and `RingTheory/Polynomial/KernelPolynomial` first (no dependency inside the slice,
ready now), then `LinearSolve/Multigrid/*` and `LinearSolve/DomainDecomposition/*`, then
`LinearSolve/Preconditioner/{Polynomial,Chebyshev,ApproximateInverse}`.
`LinearSolve/Preconditioner/ILU` waits on `LinearAlgebra/Matrix/Order` and
`LinearSolve/Stationary/RegularSplitting` and should be scheduled last. Estimated 2.5 k lines of
backbone and 1.5 k of surface.

### 15.5 Extensibility (adds to §10)

* **A domain-decomposition or finite-element book** (Toselli–Widlund, Smith–Bjørstad–Gropp,
  Brenner–Scott Ch. 7): the Schwarz module is stated for a family of subspaces of a Hilbert space,
  so such a book supplies only the two assumptions for its own discretization and inherits
  Thm 14.5–14.9. Its "the additive Schwarz preconditioner is spectrally equivalent to `A`" is
  `Schwarz.isSymmetricBoundedBy_additiveOperator`.
* **A multigrid book** (Briggs–Henson–McCormick, Trottenberg–Oosterlee–Schüller, Hackbusch): the
  two-grid theorem and the FMG bound are stated for an arbitrary coarse subspace, a smoother given
  by its error operator and an abstract dual pair of seminorms, so a new book contributes its own
  smoothing and approximation estimates and nothing else. The V- and W-cycle recursions stay in the
  surface until a second book proves something about them.
* **A sparse-direct book** (Davis, Duff–Erisman–Reid): `Matrix.IsILU` with `P = ∅` is exact `LU`,
  and `Matrix.schurComplementSingle` is one elimination step, so the elimination-tree and fill-path
  theory would attach there — that is the natural home for Saad Thm 10.6–10.7, which are skipped
  here for want of a second consumer.

---
