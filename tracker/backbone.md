<!--
The item inventory that used to live here is the tracker plan now: the TOML group files beside this
document list every key declaration, and the declarations themselves carry the signatures and the
doc comments. What remains here is the reasoning — why the library is shaped this way — which no
tool can derive from the compiled environment.

Signature blocks have been dropped where the code exists; run `lake exe tracker show <group>` for
those. Blocks that remain describe items not yet written, where the statement below is still the
plan.
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
Lean block describes a later phase it is a sketch. The per-book surface plans in `plans/surface/`
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
   are phase 3; Ch. 4, 7, 10, 13–14 (Fourier, Sobolev, FEM, BIE) are out of scope until Mathlib
   has Sobolev spaces. It supplies the Banach/Hilbert-space forms in which the backbone is
   stated, and its CG chapters (5.6, 9.4) meet Saad's CG in the middle.

Choi's thesis is the natural fourth book (phase 2): it fits the same spine (singular systems,
MINRES-QLP, norm estimates) but is implementation-heavy and less theorem-dense than
Atkinson–Han, and it would leave the Banach-space layer untested if taken earlier.

### 0.3 Definition of done for phase 1

The backbone modules listed as phase 1 in §7 proved without `sorry`; surface libraries
`SaadSparse`, `FongSaunders`, `AtkinsonHan` with chapter files for the ranges above, each
theorem proved by specializing the backbone (with equivalence lemmas for book-specific
definitions), following the surface plans in `plans/surface/`.

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
  FloatingPoint/…               -- reserved (phase 4)
Surface/
  SaadSparse/ChNN/….lean        -- one Lake library per book, srcDir = "Surface"
  FongSaunders/SecN.lean
  AtkinsonHan/ChNN/….lean
plans/
  backbone.md                   -- this file
  surface/…                     -- per-book surface plans
```

Upstreaming candidates are not segregated into a separate directory: they live in the topical
folders `Analysis/`, `InnerProductSpace/`, `Matrix/`, `Polynomial/` mirroring Mathlib's own tree,
each module starting with a comment "Upstreaming candidate … natural home: `Mathlib.…`", written
in Mathlib conventions and free of dependencies on the numerical-analysis layers. The
numerical-analysis layers use them only through their Mathlib-style names.

`lakefile.toml` registers four libraries: `Numlib` (the default target) and the surface libraries
`SaadSparse`, `FongSaunders`, `AtkinsonHan` with `srcDir = "Surface"`. Surface libraries import
`Numlib` only (never each other).

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
  Banach adjoints), Sobolev spaces and FEM, nonlinear CG (AH Algorithm 2), analytic perturbation
  theory via contour integrals of operator-valued functions.

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

#### 2.1.12 `Matrix/Order.lean` (L4, phase 2)
Entrywise order and absolute value (`|A| ≤ |B|`, `|A * B| ≤ |A| * |B|`, monotonicity of products by
nonnegative matrices; Saad Prop 1.24/1.26, Higham §3.5). Watch out: Mathlib's `Matrix` order
instance in `Analysis/Matrix/Order.lean` is the *Loewner* order; the entrywise order must be a
scoped instance or go through `Matrix.of`/`Pi`. Needed by regular splittings (2.3.4) and by the
floating-point layer (§6).

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
Block splittings and the general overlapping block Jacobi/GS (Saad Alg 4.1–4.2) are phase 2 and
reuse `Projection/Additive.lean`.

#### 2.3.3 `Stationary/DiagDominant.lean` (L4)
Serves Saad Thm 4.6–4.9, Cor 4.8; Kress Thm 4.2 (Jacobi with the explicit constant `q_∞`), Thm 4.3
(Sassenfeld criterion for Gauss–Seidel), Cor 4.4, Problem 4.4 (column dominance); AH Ex 5.2.2.

Proofs: Jacobi via the `‖·‖_∞` operator norm (which also gives Kress's rate) or via Gershgorin
(`eigenvalue_mem_ball`) on `D⁻¹(E+F)`; Gauss–Seidel via Saad's eigenvector argument with the split
sums `σ₁, σ₂`. Irreducibly diagonally dominant matrices (Thm 4.7, second half of 4.9) need
`Matrix.IsIrreducible` (in Mathlib) and are phase 2.

#### 2.3.4 `Stationary/RegularSplitting.lean` (L4, phase 2)
Saad Def 4.3, Thm 4.4, M-matrices (Thm 1.29–1.33). Blocked on Perron–Frobenius (Mathlib only has
`Matrix.IsIrreducible`/`IsPrimitive`). Minimal route: prove the weak Perron theorem for nonnegative
matrices (existence of a nonnegative eigenvector for `ρ(B)`) via `(I − B/r)⁻¹ ≥ 0` for `r > ρ(B)`
and compactness; that suffices for Thm 1.29 and Thm 4.4. Needs 2.1.12.

#### 2.3.5 `Stationary/SPD.lean` (L3/L4, phase 2)
Richardson with optimal parameter (Saad Ex 4.1, AH Ex 5.2.3), Jacobi over-relaxation (Kress
Thm 4.9), Kahan's necessary condition `0 < ω < 2` (Kress Thm 4.11: `det G(ω) = (1 − ω)ⁿ`), the
Householder–John / Ostrowski–Reich theorem in operator form — `A` symmetric coercive, `A = M − N`,
`M + Mᴴ − A` coercive ⇒ `ρ(M⁻¹ N) < 1` (Saad Thm 4.10, Kress Thm 4.12 is `M = D/ω + E`; proof by
the Rayleigh-quotient identity for eigenvalues of `M⁻¹N`, as in Kress, or by the energy-norm
contraction), Young's SOR theory (Saad Prop 4.12–Thm 4.16, Kress Def 4.13–Cor 4.16: consistently
ordered ⇒ `ω_opt`, `ρ_GS = ρ_J²`) — matrix-combinatorial, shared by two books, so backbone
(phase 2) but last in priority.

### 2.4 `Numlib/LinearSolve/Projection/`

#### 2.4.1 `Projection/Basic.lean` (L1)
Serves Saad §5.1–5.2 (Prop 5.1, 5.3, 5.4, 5.6, (5.7)), §1.12 (Thm 1.38, Cor 1.39 via Mathlib),
Fong–Saunders §2, Choi Table 2.5, AH §9 (bridge in 5.2.3).

Saad Thm 5.7 (`‖b − A_m x*‖ ≤ ‖Q A (1 − P_K)‖ ‖(1 − P_K) x*‖` for the projected operator) is a
phase-2 sketch (`norm_projected_residual_le`); its Galerkin/minimal-residual special cases are
covered by 2.4.2.

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
with `P_i` the projector onto `A K_i` orthogonal to `K_i`; block Jacobi/GS are instances.

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
`Module.AEval' A` (with `natDegree = grade`) is phase 2. Operators `A : E →L[𝕜] E` coerce to
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
`Krylov.IsMinNormMinResIterate`) is a phase-2 sketch.

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
via Chebyshev on two intervals; Winther's superlinear convergence for `A = 1 − K`, `K` compact
self-adjoint (AH Thm 5.6.2; needs the compact spectral theorem, not in Mathlib).

### 3.11 `Krylov/Monotonicity.lean` (Fong–Saunders; L3)
Serves Fong–Saunders §2–3 and Table 5.1; Choi Lemma 2.14, 2.20; Steihaug.

Proof route: identify the iterates with the CR/CG iterates and use the sign lemma of 3.8
(Fong–Saunders Thm 2.2), whose parts (d)–(f) use finite termination `x_ℓ = x*` and the orthonormal
expansion in `{A p_i/‖A p_i‖}`. The stopping rule (3.4) is `backwardError_le_iff` (2.2); the
monotonicity of both optimal perturbations `‖E_k‖/‖A‖`, `‖f_k‖/‖b‖` follows from
`exists_optimal_perturbation` (2.2). Phase 2: Steihaug's generalization to indefinite `A` (`‖x_k‖`
increasing while `⟪A p_j, p_j⟫ > 0` for `j ≤ k` (CG), resp. also `⟪r_j, A r_j⟫ > 0` (CR/MINRES));
Choi Lemma 2.20 / (3.21) (`‖A x_k‖` nondecreasing for minimal-residual iterates). Extending to
Hilbert spaces (infinite orthonormal expansions, `x_k → x*`) is a phase-3 improvement.

### 3.12 Phase 2–3 Krylov modules

* `Krylov/Preconditioned.lean` — PCG is CG for `M⁻¹ A` in `WithEnergy M` (Saad Alg 9.1, Prop
  9.1 left/right GMRES equivalence, Prop 9.2–9.3 flexible GMRES; AH §9.4's residual = Riesz
  representative is PCG with `M` = the Gram operator of `V`). Structural reuse of 3.7 with a
  different inner product; also Concus–Golub–Widlund (Saad §9.6) as an instance.
* `Krylov/Singular.lean` — Choi Ch. 2–3: termination-index bounds (Prop 2.2–Thm 2.4), MINRES on
  compatible singular systems returns `A† b` (Thm 2.25, from 3.4), incompatible case (Thm 2.27:
  a `{2,3}`-inverse solution), MINRES-QLP spec and Thm 3.1, norm/condition estimates (Lemmas
  2.31–2.33, (3.18)–(3.21)), the Lanczos-specialized residual recurrences (Lemma 2.18–2.19),
  preconditioning caveats (§3.4.2–3.4.3).
* `Krylov/OrthogonalPolynomials.lean` — Meurant §2.2–2.3, §3.3: the spectral measure of `(A, v)`
  (L3: `∑ ω_l δ_{λ_l}`), Lanczos polynomials orthonormal for it, Ritz values = roots of `p_{k+1}` =
  eigenvalues of `T_k`, Gauss quadrature (Thm 1) with weight formulas, `‖ε_k‖_A² = ‖r₀‖²
  [(T_n⁻¹e₁, e₁) − (T_k⁻¹e₁, e₁)]` (Thm 9), spectral formulas (Thm 8), persistence (Thm 5, 7:
  theorems about unreduced symmetric tridiagonal matrices). Also feeds Kress §9.3 (Gauss
  quadrature) and Saad §6.6.2 ((d)–(e) of that section are deferred with it).
* `Krylov/BiLanczos.lean` — Saad Ch. 7: two-sided Lanczos (Prop 7.1), BCG (Prop 7.2), QMR
  (Prop 7.3, Thm 7.4, (7.23)–(7.25)) as instances of `Krylov.HessenbergRelation` (3.5) with a
  non-orthonormal basis (quasi-residual); CGS/BiCGSTAB/TFQMR are surface.
* `Krylov/Block.lean` — Saad §6.12 block Krylov methods: phase 3, together with the eigenvalue
  book's block methods.
* Faber–Manteuffel (Saad §6.10, L3, unique to Saad) — Saad surface; its Lemma 6.23 ("`Aᴴ v ∈ 𝒦_s(A,v)`
  for all `v` iff `A` normal with `ν(A) ≤ s−1`") and the normal-matrix theory behind Thm 6.24 move
  to `Eigen/Normal.lean` (phase 3) if the eigenvalue book needs them.

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

Sketches for later phases of this module (phase 2 unless marked):

```lean
/-- Eigenvector bound (Saad-eig Thm 3.9): `sin θ(ũ, u) ≤ ‖r‖/δ`. -/
theorem LinearMap.IsSymmetric.sin_angle_le_norm_residual_div …
/-- Weyl (Kress Cor 7.5): `|λ_j(A) − λ_j(B)| ≤ ‖A − B‖` for symmetric `A, B` (needs Courant–Fischer,
4.2); Kress Cor 7.6 (diagonal entries vs eigenvalues) and Cor 7.9 (Schur inequality) as corollaries. -/
theorem LinearMap.IsSymmetric.abs_eigenvalues_sub_le …
/-- Column-sum Gershgorin discs; disc counting (Saad-eig Thm 3.12) needs continuity of eigenvalues
— phase 3. -/
/-- Condition number of a simple eigenvalue `1/|⟪u, w⟫|` (Saad-eig Def 3.1) and the first-order
perturbation `λ(ε) = λ + ε ⟪ΔA u, w⟫/⟪u, w⟫ + O(ε²)` (Prop 3.5, via the implicit function theorem on
`det`); eigenvector condition number `‖S(λ)(1 − P)‖` (Def 3.2) and its Hermitian value
`1/dist(λ, σ(A)∖{λ})`. Saad-eig Thm 3.7/Cor 3.2 (Jordan version of Bauer–Fike) stay in the surface. -/
/-- Pseudospectra (Saad-eig Def 3.3/Prop 3.7): `‖(A − z)⁻¹‖ > 1/ε ↔ ∃ E, ‖E‖ ≤ ε ∧ z ∈ σ(A − E)` —
Hilbert-space level. Wielandt–Hoffman, Davis–Kahan `sin θ` (phase 3). -/
```
The eigenvalue-condition-number result needs differentiability of a simple root of the
characteristic polynomial (Mathlib: `HasStrictDerivAt` of `Polynomial.eval` + implicit function
theorem).

### 4.2 `Eigen/RayleighRitz.lean` (L1 definitions, L3 bounds; phase 2)
Serves Saad-eig §4.3 (Prop 4.3 exactness on invariant subspaces, Thm 4.3/4.7 residual bounds with
`γ`, Prop 4.4/Cor 4.1/Thm 4.4 Ritz values via min–max, Lemma 4.1/Thm 4.5 Ritz-value errors,
Thm 4.6 Ritz-vector angle, Prop 4.5), §6.1–6.2 (Prop 6.4 compression commutes with low-degree
polynomials, Thm 6.1 optimality of the characteristic polynomial of `H_m`, Prop 6.8 cheap residual
`‖(A − θ)ũ‖ = h_{m+1,m}|e_mᵀ y|`), Thm 8.1 (Davidson monotonicity), Meurant §2 (Ritz values),
Choi §2.4.4 (Ritz-value estimates), Kress Thm 11.17 (Céa in operator form: the linear-system twin).

```lean
/-- Ritz pairs of `A` on `K`: eigenpairs of the compression `compression A K` (2.1.6). -/
def IsRitzPair (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (θ : 𝕜) (u : E) :
    Prop :=
  u ∈ K ∧ u ≠ 0 ∧ A u - θ • u ∈ Kᗮ
theorem isRitzPair_iff_hasEigenvector (θ u) :
    IsRitzPair A K θ (u : E) ↔ Module.End.HasEigenvector (compression A K) θ u
/-- Oblique (Petrov–Galerkin) Ritz pairs: `u ∈ K`, `A u − θ u ⟂ L`. -/
def IsObliqueRitzPair …
/-- Saad-eig Prop 4.3: on an `A`-invariant `K`, every Ritz pair is an exact eigenpair. -/
theorem IsRitzPair.hasEigenvector_of_invt (hK : K ∈ Module.End.invtSubmodule A) …
/-- Saad-eig Thm 4.3 (any Hilbert space, bounded `A`, closed `K`): with `γ = ‖P_K A (1 − P_K)‖` and
an exact unit eigenpair `(λ, u)`, `‖(A_K − λ) P_K u‖ ≤ γ ‖(1 − P_K) u‖` and
`‖(A_K − λ) u‖ ≤ √(|λ|² + γ²) ‖(1 − P_K) u‖`; Thm 4.7 is the oblique version with `Q_K^L`. -/
theorem compression_residual_le …
/-- Hermitian case (Prop 4.4, Cor 4.1, Thm 4.4): Ritz values are min–max values over subspaces of
`K`, hence `θ_i ≤ λ_i` (interlacing from below) and `θ ∈ [λ_min, λ_max]`. -/
theorem IsRitzPair.mem_Icc (hA : A.IsSymmetric) … : θ ∈ Set.Icc lmin lmax
/-- Saad-eig Lemma 4.1: `|λ − ⟪A P_K u, P_K u⟫/‖P_K u‖²| ≤ ‖A − λ‖ ‖(1 − P_K) u‖²/‖P_K u‖²`, so
`0 ≤ λ₁ − θ₁ ≤ ‖A − λ₁‖ tan²θ(u₁, K)`; Thm 4.5 for the `i`-th eigenvalue. -/
theorem IsSymmetric.ritz_value_error_le …
/-- Saad-eig Thm 4.6: `sin θ(u, ũ) ≤ √(1 + γ²/δ²) sin θ(u, K)` for the Ritz vector of the closest
Ritz value; Prop 4.5: `|λ − θ| ≤ ‖A − λ‖ sin²θ(u, ũ)`. -/
theorem IsSymmetric.sin_angle_ritzVector_le …
/-- Saad-eig Thm 6.1: the characteristic polynomial of the compression to `𝒦_m` minimizes
`‖p(A) v‖` over monic `p` of degree `m` (Cayley–Hamilton + Prop 6.4); Prop 6.8: for a Ritz pair
`(θ, V_m y)` of the Arnoldi compression, `‖(A − θ) ũ‖ = h_{m+1,m} |y_m|`. -/
theorem Arnoldi.charpoly_compression_isMinOn … ; theorem Arnoldi.norm_ritz_residual_eq …
/-- Courant–Fischer min–max (Saad-eig Thm 1.9, Kress Thm 7.4; not in Mathlib):
`λ_k = max_{dim S = k} min_{x ∈ S} R(x)`; Rayleigh's recursive form (Saad-eig Thm 1.10, Kress
Thm 7.3). -/
theorem LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf …
```
Courant–Fischer is the main missing Mathlib brick here (only the extreme eigenvalues are in
Mathlib via `hasEigenvalue_iSup_of_finiteDimensional`); the standard dimension-counting proof
(`S ⊓ span{u_k, …, u_n} ≠ ⊥`) is ~100 lines with `Submodule.finrank_sup_add_finrank_inf_eq`. It
also gives Weyl's inequalities and the interlacing needed by Lanczos (3.3) and by Choi's
Ritz-value estimates.

### 4.3 `Eigen/PowerMethod.lean` (L3; phase 3)
Serves Saad-eig Thm 4.1 (power method with a semi-simple dominant eigenvalue), §4.1.2–4.1.3
(shifted/inverse iteration, RQI stated), Thm 4.2/Prop 4.1–4.2 (Wielandt and Schur–Wielandt
deflation), Thm 5.1–5.2 (subspace iteration), Kress §7.2 (power method for diagonalizable `A`,
Lemma 7.18 subspace iteration, Thm 7.19 orthogonal iteration, Thm 7.20 QR algorithm).

```lean
noncomputable def powerIterate (A : E →ₗ[𝕜] E) (x₀ : E) (k : ℕ) : E :=
  (‖(A ^ k) x₀‖)⁻¹ • (A ^ k) x₀
/-- If `λ₁` is a simple eigenvalue of strictly largest modulus and `x₀` has a nonzero component in
its spectral projector, then `A^k x₀ / λ₁^k → P₁ x₀` (hence `powerIterate` converges in direction)
at rate `|λ₂/λ₁|^k`. -/
theorem powerIterate_tendsto [FiniteDimensional ℂ F] (A : F →ₗ[ℂ] F) {l₁ : ℂ}
    (h₁ : Module.End.HasEigenvalue A l₁) (hsimple : finrank (A.maxGenEigenspace l₁) = 1)
    (hdom : ∀ l ∈ spectrum ℂ A, l ≠ l₁ → ‖l‖ < ‖l₁‖) (x₀ : F) (hx₀ : P₁ x₀ ≠ 0) :
    Tendsto (fun k => (l₁ ^ k)⁻¹ • (A ^ k) x₀) atTop (nhds (P₁ x₀)) ∧
      (geometric rate for every `r > max_{l ≠ l₁} |l|/|l₁|`)
/-- Inverse iteration / shift-and-invert: the power method for `(A − σ)⁻¹` (a `simp` lemma
reusing the above with the spectrum mapped by `(· − σ)⁻¹`). -/
/-- Subspace iteration (Saad-eig Thm 5.2; Kress Lemma 7.18 is the diagonalizable case): if
`|λ_m| > |λ_{m+1}|` and the spectral projector `P_m` onto the dominant invariant subspace is
injective on `S₀`, then `gap(A^k S₀, range P_m) ≤ C (|λ_{m+1}/λ_m| + ε)^k`; the power method is
`m = 1`. -/
theorem subspaceIterate_gap_le …
/-- Wielandt deflation (Saad-eig Thm 4.2): `σ(A − σ u₁ vᴴ) = {λ₁ − σ, λ₂, …}` when `vᴴ u₁ = 1`. -/
/-- QR algorithm = orthogonal iteration on the canonical flag (Kress Thm 7.20, algebraic part);
convergence (Kress Thm 7.19) from subspace iteration. -/
```
Difficult proof: use the generalized-eigenspace decomposition (Mathlib
`Module.End.iSup_maxGenEigenspace_eq_top` and `independent_maxGenEigenspace` over `ℂ`) to split
`x₀ = P₁ x₀ + w`, with `w` in the complementary `A`-invariant subspace
`W = ⨆_{μ ≠ λ₁} maxGenEigenspace μ` on which `spectrum (A|_W) = σ(A) ∖ {λ₁}`; Gelfand (2.1.3)
gives `‖(A|_W)^k‖ ≤ C r^k` for `r > max |λ|`, so `λ₁^{−k} A^k w → 0`. No Jordan form needed.
Subspace iteration follows the same pattern with `Submodule.map` and the gap between subspaces
(`‖P₁ − P₂‖`, Saad-eig §3.1; not in Mathlib: canonical angles / `Submodule` gap metric, deferred
with this module); it also needs "a projector family with `‖P − Q‖ < 1` has constant rank"
(Saad-eig Thm 3.2, easy).

### 4.4 `Eigen/KrylovEigen.lean` (L3; phase 2)
Serves Saad-eig §6.6 (Lemma 6.1, Thm 6.3 angle bound, Thm 6.4 Kaniel–Paige–Saad, §6.6.3 Ritz
vectors), §6.7 (Lemma 6.2, Thm 6.5–6.7 Haar characterization, Prop 6.10, Thm 6.8 ellipse bound),
§4.4 (Thm 4.8 min–max with `p(γ) = 1`, Lemma 4.3 Zarantonello, Thm 4.9 ellipses), Saad §6.6,
Meurant §2.3 (Ritz values as Gauss nodes).

```lean
/-- Saad-eig Lemma 6.1: `tan θ(u_i, 𝒦_m) = min_{deg p ≤ m−1, p(λ_i)=1} ‖p(A) y_i‖ · tan θ(u_i, v₁)`
(Hermitian). -/
theorem Lanczos.tan_angle_eq_iInf …
/-- Saad-eig Thm 6.3: `tan θ(u_i, 𝒦_m) ≤ κ_i tan θ(v₁, u_i) / T_{m−i}(1 + 2γ_i)`,
`γ_i = (λ_i − λ_{i+1})/(λ_{i+1} − λ_n)`, `κ_i = ∏_{j<i} (λ_j − λ_n)/(λ_j − λ_i)`. -/
theorem Lanczos.tan_angle_le …
/-- Kaniel–Paige–Saad (Saad-eig Thm 6.4):
`0 ≤ λ_i − θ_i^{(m)} ≤ (λ₁ − λ_n) (κ_i^{(m)} tan θ(v₁, u_i) / T_{m−i}(1 + 2γ_i))²`. -/
theorem kaniel_paige_saad …
/-- Ritz-vector bound (§6.6.3): Thm 4.6 with `γ = β_{m+1}` (Saad-eig Prop 6.6 basis-free form
`‖P_m A (1 − P_m)‖ = h_{m+1,m}`). -/
/-- Non-Hermitian Arnoldi (Saad-eig Lemma 6.2): `‖(1 − P_m) u₁‖ ≤ ξ₁ ε₁^{(m)}` with
`ε₁^{(m)} = min_{p(λ₁)=1} max_{λ ∈ σ(A)∖{λ₁}} |p(λ)|`; Prop 6.10 (circle enclosure
`(ρ/|λ₁ − c|)^{m−1}`), Thm 6.8 (ellipse) — phase 3 with the complex Chebyshev results of 2.1.9. -/
/-- Ritz values of the Lanczos process are the eigenvalues of `T_m` and the roots of the Lanczos
polynomial (Meurant §2.3). -/
```
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
Higham Ch. 18 (matrix powers in finite precision, phase 4), the normal-matrix theory behind
Saad Lemma 6.23/Thm 6.24 (`Eigen/Normal.lean`, see 3.12). Schur form is not in Mathlib: a phase-3
upstreaming candidate under `Numlib/Matrix/`. Jordan form is not in Mathlib either and is avoided:
every use here is replaced by Gelfand's formula or by generalized eigenspaces; Saad-eig
Thm 3.7/Cor 3.2 and P-5.6 are the only results that need the Jordan index and stay in the surface.

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
convex set of a reflexive space) is phase 3: Mathlib lacks reflexivity/weak compactness.

#### 5.1.2 `Approximation/Chebyshev.lean` (phase 3)
Chebyshev equioscillation (AH Thm 3.3.19, Kress) — not in Mathlib (Haar condition, de la
Vallée-Poussin). The min–max results the Krylov layer needs are in 2.1.9; Chebyshev
expansions/uniform bounds (AH Ex 3.7.4) belong here.

#### 5.1.3 `Approximation/Interpolation.lean` (phase 3)
Lagrange interpolation (`Lagrange.interpolate` in Mathlib), the error formula
`f(x) − p(x) = f^{(n+1)}(ξ) ∏(x − x_i)/(n+1)!` (AH §3.2, Kress §8.1; needs a generalized Rolle from
`exists_hasDerivAt_eq_zero` by induction), Lebesgue constants of interpolation projections,
piecewise-linear/spline interpolation (Kress §8.3) — Kress surface unless a second book needs it.

#### 5.1.4 `Approximation/Quadrature.lean` (phase 3)
Interpolatory quadrature, degree of exactness, Gauss quadrature via orthogonal polynomials (3.12
`OrthogonalPolynomials`, Meurant §2.3, Kress §9.3), convergence of quadrature rules for
continuous integrands via Banach–Steinhaus (AH §2.4.4/Kress Thm 9.10 (Szegő): bounded weights +
exactness on a dense set; Mathlib `banach_steinhaus` + `polynomialFunctions_closure_eq_top`),
Peano kernel error representation (Kress). Placed after 3.12 because the Gauss-rule existence
proof is the Lanczos/Jacobi-matrix argument.

### 5.2 `Numlib/Variational/`

#### 5.2.1 `Variational/Forms.lean` (L2)
Serves AH Thm 8.3.1–8.3.3, §8.7 (inf–sup condition), §9.1 (Ritz), §9.4 (energy norm), Kress §11.
Bounded forms are `SesqForm 𝕜 V := V →L⋆[𝕜] V →L[𝕜] 𝕜` (conjugate-linear in the first slot, as
`innerSL`; Mathlib's `IsCoercive` is the real case). Over `ℝ` a `V →L[ℝ] V →L[ℝ] ℝ` *is* a
`SesqForm ℝ V` (the same defeq Mathlib's `LaxMilgram.lean` uses), so the real surfaces need no
conversion; the `_real` lemmas remove the `re`/`conj` decorations (1.7).

```lean
abbrev SesqForm (𝕜 V : Type*) [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] :=
  V →L⋆[𝕜] V →L[𝕜] 𝕜
namespace SesqForm   -- (a : SesqForm 𝕜 V)
def IsBoundedWith (M : ℝ) : Prop := ∀ u v, ‖a u v‖ ≤ M * ‖u‖ * ‖v‖
/-- `c ‖v‖² ≤ re (a v v)` (AH: `V`-elliptic with constant `c`; strongly positive). -/
def IsCoerciveWith (c : ℝ) : Prop := ∀ v, c * ‖v‖ ^ 2 ≤ RCLike.re (a v v)
def IsCoercive : Prop := ∃ c : ℝ, 0 < c ∧ a.IsCoerciveWith c
def IsHermitian : Prop := ∀ u v, a u v = starRingEnd 𝕜 (a v u)
theorem isBoundedWith_opNorm : a.IsBoundedWith ‖a‖
theorem opNorm_le_of_isBoundedWith (hM : 0 ≤ M) (h : a.IsBoundedWith M) : ‖a‖ ≤ M
theorem IsCoerciveWith.mono (h : a.IsCoerciveWith c) (hc : c' ≤ c) : a.IsCoerciveWith c'
theorem IsCoerciveWith.norm_le_norm_apply (h : a.IsCoerciveWith c) (u : V) : c * ‖u‖ ≤ ‖a u‖
theorem isCoerciveWith_real_iff (a : SesqForm ℝ V) (c : ℝ) :
    a.IsCoerciveWith c ↔ ∀ v, c * ‖v‖ ^ 2 ≤ a v v
theorem isHermitian_real_iff (a : SesqForm ℝ V) : a.IsHermitian ↔ ∀ u v, a u v = a v u
theorem innerSL_isCoerciveWith : SesqForm.IsCoerciveWith (innerSL 𝕜 : SesqForm 𝕜 V) 1
theorem innerSL_isHermitian : SesqForm.IsHermitian (innerSL 𝕜 : SesqForm 𝕜 V)
/-- The form of an operator, `ofOperator A u v = ⟪A u, v⟫`. -/
noncomputable def ofOperator (A : V →L[𝕜] V) : SesqForm 𝕜 V := (innerSL 𝕜).comp A
-- [CompleteSpace V] from here on
/-- Operators ⟷ forms (AH (8.3.1) via Riesz, (9.4.5)): `⟪toOperator a u, v⟫ = a u v`;
Mathlib's `InnerProductSpace.continuousLinearMapOfBilin`. -/
noncomputable abbrev toOperator : V →L[𝕜] V := InnerProductSpace.continuousLinearMapOfBilin a
theorem inner_toOperator (u v : V) : inner 𝕜 (toOperator a u) v = a u v
/-- The Riesz representative `f` of a functional, `⟪f, v⟫ = ℓ v`. -/
noncomputable def rieszRep (ℓ : V →L[𝕜] 𝕜) : V := (InnerProductSpace.toDual 𝕜 V).symm ℓ
theorem inner_rieszRep (ℓ : V →L[𝕜] 𝕜) (v : V) : inner 𝕜 (rieszRep ℓ) v = ℓ v
theorem norm_rieszRep (ℓ : V →L[𝕜] 𝕜) : ‖rieszRep ℓ‖ = ‖ℓ‖
theorem toOperator_ofOperator (A : V →L[𝕜] V) : toOperator (ofOperator A) = A
theorem ofOperator_toOperator : ofOperator (toOperator a) = a
theorem isCoerciveWith_iff_toOperator (c : ℝ) :
    a.IsCoerciveWith c ↔ (toOperator a : V →ₗ[𝕜] V).IsCoerciveWith c
theorem isHermitian_iff_toOperator_isSymmetric :
    a.IsHermitian ↔ (toOperator a : V →ₗ[𝕜] V).IsSymmetric
theorem norm_toOperator : ‖toOperator a‖ = ‖a‖
/-- `a u v = ℓ v` for all `v` iff `A u = f`. -/
theorem forall_apply_eq_iff_toOperator_eq (ℓ : V →L[𝕜] 𝕜) (u : V) :
    (∀ v, a u v = ℓ v) ↔ toOperator a u = rieszRep ℓ
/-- Energy functional `E v = ½ re (a v v) − re (ℓ v)` (AH Thm 8.3.3, (9.1.7)) and energy norm. -/
noncomputable def energy (ℓ : V →L[𝕜] 𝕜) (v : V) : ℝ :=
  (1 / 2 : ℝ) * RCLike.re (a v v) - RCLike.re (ℓ v)
noncomputable def energyNorm (v : V) : ℝ := Real.sqrt (RCLike.re (a v v))
theorem energyNorm_eq_energyNorm_toOperator [CompleteSpace V] (v : V) :
    a.energyNorm v = _root_.energyNorm (toOperator a : V →ₗ[𝕜] V) v
/-- Norm equivalence `√c ‖v‖ ≤ ‖v‖_a ≤ √M ‖v‖` (AH §9.4, Thm 8.3.3). -/
theorem sqrt_mul_norm_le_energyNorm (hc : 0 ≤ c) (h : a.IsCoerciveWith c) (v : V) :
    Real.sqrt c * ‖v‖ ≤ a.energyNorm v
theorem energyNorm_le_sqrt_mul_norm (h : a.IsBoundedWith M) (v : V) :
    a.energyNorm v ≤ Real.sqrt M * ‖v‖
end SesqForm

/-- Two-space bounded forms `U × V → 𝕜` (Petrov–Galerkin, Babuška–Nečas). -/
abbrev SesqForm₂ (𝕜 U V : Type*) … := U →L⋆[𝕜] V →L[𝕜] 𝕜
namespace SesqForm₂   -- (a : SesqForm₂ 𝕜 U V)
/-- Inf–sup (Babuška–Brezzi) condition in operator-norm form: `α ‖u‖ ≤ ‖a u‖` (AH (8.7.2)). -/
def InfSupWith (α : ℝ) : Prop := ∀ u, α * ‖u‖ ≤ ‖a u‖
/-- Transposed nondegeneracy (AH (8.7.3)). -/
def IsNondegenerate : Prop := ∀ v, v ≠ 0 → ∃ u, a u v ≠ 0
/-- The book's inf–sup quantity `sup_{v ≠ 0} |a u v|/‖v‖` is the operator norm `‖a u‖`. -/
theorem iSup_norm_div_eq_norm (u : U) : (⨆ v : {v : V // v ≠ 0}, ‖a u v‖ / ‖(v : V)‖) = ‖a u‖
/-- Coercive one-space forms satisfy the inf–sup condition (AH Ex 8.7.1). -/
theorem _root_.SesqForm.IsCoerciveWith.infSupWith (h : a.IsCoerciveWith c) :
    SesqForm₂.InfSupWith (a : SesqForm₂ 𝕜 V V) c
end SesqForm₂
```

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

Phase 2: the Xu–Zikatanov sharpening of Babuška's bound to `M/α_N` via Kato's lemma (2.1.7).

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
weighted norms (AH Thm 5.2.3, Volterra) and generalized Picard–Lindelöf (Thm 5.2.4) are AH surface
/ phase 3 (Mathlib has `IsPicardLindelof` in finite dimension).

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
`(1 − √(1−2h))^{2ⁿ}/(2ⁿ a L)`) and the modified (chord) Newton method with frozen derivative
(linear convergence via 5.3.1, AH Ex 5.4.5).

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

---

## 6. Reserved: floating-point layer (`Numlib/FloatingPoint/`, phase 4)

Higham is the sole source; Paige/Greenbaum finite-precision Lanczos (Meurant §4–5) and Higham
Ch. 17 are the consumers. Only the *interface* is fixed here so that exact-arithmetic results are
stated in a way that survives perturbation.

```lean
/-- Standard model (Higham (2.4)): an abstract rounding relation with unit roundoff `u`. -/
structure FloatingPoint.RoundingModel (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] where
  u : K
  u_nonneg : 0 ≤ u
  Rounds : K → K → Prop            -- `Rounds x y`: `y` is an admissible rounding of `x`
  abs_sub_le : ∀ x y, Rounds x y → |y - x| ≤ u * |x|
/-- `γ_n = n u / (1 − n u)` and its calculus (Higham Lemma 3.1, 3.3): `(1 + u)^n ≤ 1 + γ_n`,
`∏ (1 + δ_i)^{±1} = 1 + θ_n`, `|θ_n| ≤ γ_n`, `γ_j + γ_k + γ_j γ_k ≤ γ_{j+k}`. -/
noncomputable def FloatingPoint.gamma (u : K) (n : ℕ) : K := n * u / (1 - n * u)
/-- Relative perturbation bookkeeping: `IsRelPert u n x y := ∃ θ, |θ| ≤ γ_n ∧ y = x * (1 + θ)`. -/
/-- Componentwise inner-product bound (Higham (3.4)): `|fl(xᵀy) − xᵀy| ≤ γ_n |x|ᵀ|y|`;
matrix–vector, matrix–matrix ((3.12)–(3.13)); recursive summation (Ch. 4). -/
/-- Perturbed Arnoldi/Lanczos relation `A V_m = V_{m+1} H̄_m + F_m`, `‖F_m‖ ≤ ε` and orthogonality
defect `‖V_mᴴ V_m − I‖ ≤ ε'` (Paige; Meurant Thm 14–15) as a *structure*
`Arnoldi.IsPerturbedRelation`, with exact results restated as the "`ε = 0` instance". -/
/-- Higham Thm 17.1–17.2 (stationary iteration in finite precision) as an instance of a
perturbed 2.3.1 iteration. -/
```
Design rules: the model is relational (a rounding *relation*, never a rounding function);
componentwise statements first, normwise as corollaries through `Matrix/Order.lean` (2.1.12);
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
2.1.12 matrix order, 2.3.4 regular splittings (needs weak Perron–Frobenius), 2.3.5
SPD/Ostrowski–Reich, 2.4.4 additive projections, 3.12 `Preconditioned`/`Singular`/`BiLanczos`,
`Krylov/NormalEquations` (§10), 4.1 sketches (eigenvector bound, Weyl, eigenvalue condition
numbers, pseudospectra), 4.2 Courant–Fischer + Ritz bounds, 4.4 Kaniel–Paige–Saad, 5.2.3
Xu–Zikatanov (Kato's lemma, 2.1.7), 5.3.2 AH's Kantorovich variant and the chord method, Winther's
theorem (AH Thm 5.6.2), irreducible diagonal dominance (2.3.3), the continuous-functional-calculus
form of 3.9 for bounded self-adjoint operators (the compression trick covers the
Hilbert-space consumers; the CFC form is for statements about `A` itself).

### Phase 3 — Meurant–Strakoš exact part, Kress, remaining Saad-eig
3.12 `OrthogonalPolynomials` (Gauss quadrature, error identities), `Krylov/Block` (Saad §6.12),
Saad §6.6.2 (d)–(e), complex Chebyshev polynomials on ellipses (Saad Lemma 6.26, Thm 6.27,
Cor 6.33; Saad-eig Thm 4.9, 6.8), normal-matrix theory (`Eigen/Normal.lean`: Saad Lemma 6.23,
Thm 6.24, Faber–Manteuffel), 4.3 power/subspace iteration with the gap metric between subspaces,
4.5 (Schur form as an upstreaming candidate under `Numlib/Matrix/`, Jacobi, QR algorithm,
analytic perturbation theory), 5.1.2–5.1.4 (equioscillation, interpolation, quadrature
convergence), AH Thm 3.3.14 (reflexive spaces), AH 6.2 Lax equivalence, AH 5.2.3–5.2.4 (Bielecki
norms, Picard–Lindelöf), Kress-specific direct methods (LU/Cholesky/QR existence: Mathlib has
`LDL`, no LU/QR), SVD/pseudoinverse/Tikhonov (Kress Thm 5.4–5.10), Kress Ch. 12 (projection
methods for `I − K`), a form-based energy space for non-complete `V` (1.7).

### Phase 4 — floating point (Higham; Paige/Greenbaum)
§6: model, `γ` calculus, inner products, perturbed Krylov relations, Higham Ch. 17–18.

---

## 8. Surface libraries

Rules (README): chapter-to-chapter files; statements in the book's generality (real matrices,
`ℝⁿ`, real bilinear forms); each proof a specialization of a backbone result, through equivalence
lemmas for book-specific definitions; no new mathematics — anything that does not specialize is a
demand on the backbone and goes into this plan. The per-book surface plans in `plans/surface/`
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
| D18 | Subspace iteration in Saad-eig's generality (Thm 5.2) | 4.3 | spectral projector onto the dominant generalized eigenspaces + Gelfand on the complement; gap between subspaces needs a `Submodule` gap/angle API (not in Mathlib). Kress Lemma 7.18 (diagonalizable) as a warm-up |
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

