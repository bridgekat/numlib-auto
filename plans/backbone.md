# Backbone plan

This is the plan for the `Numlib` backbone, the general layer of the library described in
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
  Analysis/…                    -- upstreaming candidates: Neumann-series bounds, κ, spectral radius
  InnerProductSpace/…           -- upstreaming candidates: coercivity, energy norm, compression,
                                --   Gram–Schmidt flags, oblique projections
  Matrix/…                      -- upstreaming candidates: Hessenberg parts, complexify, toEuclideanLin
  Polynomial/…                  -- upstreaming candidates: Chebyshev min–max
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

These live in the topical folders `Numlib/Analysis/`, `Numlib/InnerProductSpace/`,
`Numlib/Matrix/`, `Numlib/Polynomial/` (§1.5) and are stated in Mathlib's own vocabulary so that
they can be upstreamed; the numerical-analysis layers below use them only through their
Mathlib-style names.

#### 2.1.1 `Analysis/NormedRing/Inverse.lean` (L2) — explicit Neumann-series and perturbation bounds
Serves AH Thm 2.3.1, Cor 2.3.3, Thm 2.3.5 (bounds (2.3.13)–(2.3.16)), Saad §1.13, Kress Thm 3.48
(Neumann series with a priori/a posteriori bounds), Saad-eig (3.14)/Prop 3.2 (resolvent Neumann
expansion), Higham Thm 7.2. Mathlib has the qualitative facts (`Units.oneSub`, `Units.ofNearby`,
`ContinuousLinearEquiv.isOpen`) but not the constants.

```lean
variable {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]

theorem NormedRing.norm_inverse_one_sub_le {t : R} (h : ‖t‖ < 1) :
    ‖Ring.inverse (1 - t)‖ ≤ 1 / (1 - ‖t‖)
theorem NormedRing.norm_inverse_one_sub_sub_one_le {t : R} (h : ‖t‖ < 1) :
    ‖Ring.inverse (1 - t) - 1‖ ≤ ‖t‖ / (1 - ‖t‖)
/-- AH Cor 2.3.3: `‖tᵐ‖ < 1` suffices, with the bound (2.3.6). -/
theorem NormedRing.isUnit_one_sub_of_norm_pow_lt_one {t : R} {m : ℕ} (h : ‖t ^ m‖ < 1) : IsUnit (1 - t)
theorem NormedRing.norm_inverse_one_sub_le_of_norm_pow_lt_one {t : R} {m : ℕ} (h : ‖t ^ m‖ < 1) :
    ‖Ring.inverse (1 - t)‖ ≤ (∑ i ∈ Finset.range m, ‖t ^ i‖) / (1 - ‖t ^ m‖)
theorem Units.isUnit_add_of_norm_lt (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) : IsUnit ((x : R) + t)
/-- AH (2.3.13). -/
theorem Units.norm_inverse_add_le (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    ‖Ring.inverse ((x : R) + t)‖ ≤ ‖(↑x⁻¹ : R)‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖)
/-- AH (2.3.14). -/
theorem Units.norm_inverse_add_sub_le (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    ‖Ring.inverse ((x : R) + t) - ↑x⁻¹‖ ≤
      ‖(↑x⁻¹ : R)‖ ^ 2 * ‖t‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖)

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace E]

/-- AH Thm 2.3.5, two-space form, carrying both (2.3.13) and (2.3.14); completeness of `E`
suffices. -/
theorem ContinuousLinearEquiv.exists_symm_norm_le_of_add (e : E ≃L[𝕜] F) (t : E →L[𝕜] F)
    (h : ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖ < 1) :
    ∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = (e : E →L[𝕜] F) + t ∧
      ‖(e'.symm : F →L[𝕜] E)‖ ≤
        ‖(e.symm : F →L[𝕜] E)‖ / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖) ∧
      ‖(e'.symm : F →L[𝕜] E) - (e.symm : F →L[𝕜] E)‖ ≤
        ‖(e.symm : F →L[𝕜] E)‖ ^ 2 * ‖t‖ / (1 - ‖(e.symm : F →L[𝕜] E)‖ * ‖t‖)
/-- AH (2.3.16): consistency + stability ⇒ convergence. -/
theorem ContinuousLinearEquiv.norm_sub_le_of_apply_eq (L : E →L[𝕜] F) (Ln : E ≃L[𝕜] F) {v vn : E}
    (h : L v = Ln vn) : ‖v - vn‖ ≤ ‖(Ln.symm : F →L[𝕜] E)‖ * ‖(L - Ln) v‖
```
Proofs: the first bound is a corollary of `NormedRing.tsum_geometric_of_norm_lt_one`; factor
`x + t = x (1 + x⁻¹ t)` and apply the `1 − t` bounds; the two-space version needs `L⁻¹` on the
complete side. Nothing difficult.

#### 2.1.2 `Analysis/NormedRing/CondNumber.lean` (L2)
Serves Saad §1.13, AH §2.4.3, Kress §5.1, Higham Ch. 6–7, Choi §2.4.5.

```lean
/-- Condition number `‖a‖ ‖a⁻¹‖`; `0` (junk) if `a` is not a unit. -/
noncomputable def NormedRing.condNumber {R : Type*} [NormedRing R] (a : R) : ℝ :=
  ‖a‖ * ‖Ring.inverse a‖
scoped notation "κ" => NormedRing.condNumber
theorem NormedRing.one_le_condNumber [NormOneClass R] {a : R} (ha : IsUnit a) : 1 ≤ condNumber a
theorem NormedRing.condNumber_smul [NormedField 𝕜] [NormedAlgebra 𝕜 R] {c : 𝕜} (hc : c ≠ 0) (a : R) :
    condNumber (c • a) = condNumber a
theorem ContinuousLinearEquiv.condNumber_eq (e : E ≃L[𝕜] E) :
    NormedRing.condNumber (e : E →L[𝕜] E) = ‖(e : E →L[𝕜] E)‖ * ‖(e.symm : E →L[𝕜] E)‖
```
Matrix versions are the same definition under the scoped norm instances
(`open scoped Matrix.Norms.L2Operator` gives `κ₂`, `Matrix.Norms.Operator` gives `κ_∞`).
`Matrix.condNumber_l2_eq_div_singularValues` (L3, `κ₂ = σ_max/σ_min` via
`LinearMap.singularValues`) is phase 2; Saad Example 1.5 (`κ_∞(I + α e₁ eₙᵀ) = (1+|α|)²`) is
surface.

#### 2.1.3 `Analysis/SpectralRadius.lean` (L2, complex; L4 real matrices)
Serves Saad Thm 1.10–1.12, 4.1; Kress §5.2.2/AH §5.2.2; Higham Ch. 18.

```lean
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- Geometric decay at any rate above the spectral radius (Gelfand). -/
theorem exists_norm_pow_le_of_spectralRadius_lt (a : A) {r : NNReal} (hr : spectralRadius ℂ a < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖a ^ n‖ ≤ C * (r : ℝ) ^ n
/-- `ρ(a) < 1 ↔ aⁿ → 0` (Saad Thm 1.10, valid in every complex Banach algebra). -/
theorem spectralRadius_lt_one_iff_tendsto_pow (a : A) :
    spectralRadius ℂ a < 1 ↔ Tendsto (fun n => a ^ n) atTop (𝓝 0)
theorem spectralRadius_lt_one_of_norm_lt_one {a : A} (h : ‖a‖ < 1) : spectralRadius ℂ a < 1
theorem spectralRadius_lt_one_iff_exists_norm_pow_lt_one (a : A) :
    spectralRadius ℂ a < 1 ↔ ∃ n, ‖a ^ n‖ < 1
/-- Saad Thm 1.11: the Neumann series converges iff `ρ(a) < 1`, and then `1 − a` is a unit. -/
theorem summable_pow_iff_spectralRadius_lt_one (a : A) :
    Summable (fun n => a ^ n) ↔ spectralRadius ℂ a < 1
theorem isUnit_one_sub_of_spectralRadius_lt_one {a : A} (h : spectralRadius ℂ a < 1) : IsUnit (1 - a)
```
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

#### 2.1.4 `InnerProductSpace/Coercive.lean` (L1/L2/L3)
Serves Saad §1.11 (Thm 1.34), §1.8.3 (Hermitian part), Prop 5.1, Thm 5.10, 6.30; AH 5.1.4
(linear case), 8.3, 9.4; Kress Thm 3.29, 4.12.

```lean
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `c ‖x‖² ≤ re ⟪A x, x⟫` for all `x`. -/
def LinearMap.IsCoerciveWith (A : E →ₗ[𝕜] E) (c : ℝ) : Prop :=
  ∀ x, c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x)
/-- Coercive: Saad's "positive definite" (real, non-symmetric allowed), AH's "strongly monotone". -/
def LinearMap.IsCoercive (A : E →ₗ[𝕜] E) : Prop := ∃ c : ℝ, 0 < c ∧ A.IsCoerciveWith c
/-- SPD / HPD / strongly positive self-adjoint. -/
structure LinearMap.IsSymmetricCoercive (A : E →ₗ[𝕜] E) : Prop where
  isSymmetric : A.IsSymmetric
  isCoercive : A.IsCoercive
/-- "The spectrum lies in `[lmin, lmax]`", as quadratic-form bounds (§1.1). -/
structure LinearMap.IsSymmetricBoundedBy (A : E →ₗ[𝕜] E) (lmin lmax : ℝ) : Prop where
  isSymmetric : A.IsSymmetric
  le_re_inner : ∀ x, lmin * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x)
  re_inner_le : ∀ x, RCLike.re (inner 𝕜 (A x) x) ≤ lmax * ‖x‖ ^ 2

theorem LinearMap.IsCoercive.inner_self_pos (hA : A.IsCoercive) {x : E} (hx : x ≠ 0) :
    0 < RCLike.re (inner 𝕜 (A x) x)
theorem LinearMap.IsCoercive.injective (hA : A.IsCoercive) : Function.Injective A
theorem LinearMap.IsCoercive.ker_eq_bot (hA : A.IsCoercive) : LinearMap.ker A = ⊥
/-- Saad Thm 1.34 (finite dimension). -/
theorem LinearMap.isCoercive_iff_forall_pos [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E) :
    A.IsCoercive ↔ ∀ x ≠ 0, 0 < RCLike.re (inner 𝕜 (A x) x)
/-- Best coercivity constant of a symmetric operator is its smallest eigenvalue. -/
theorem LinearMap.IsSymmetric.isCoerciveWith_iff_forall_hasEigenvalue [FiniteDimensional 𝕜 E]
    (hA : A.IsSymmetric) (c : ℝ) :
    A.IsCoerciveWith c ↔ ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → c ≤ RCLike.re μ
-- `IsSymmetricBoundedBy` API
theorem LinearMap.IsSymmetricBoundedBy.isCoerciveWith (hA : A.IsSymmetricBoundedBy lmin lmax) :
    A.IsCoerciveWith lmin
theorem LinearMap.IsSymmetricBoundedBy.isSymmetricCoercive (hA) (hl : 0 < lmin) : A.IsSymmetricCoercive
theorem LinearMap.IsSymmetricBoundedBy.rayleigh_mem_Icc (hA) {x : E} (hx : x ≠ 0) :
    RCLike.re (inner 𝕜 (A x) x) / ‖x‖ ^ 2 ∈ Set.Icc lmin lmax
theorem LinearMap.IsSymmetricBoundedBy.mono (hA) (h₁ : lmin' ≤ lmin) (h₂ : lmax ≤ lmax') :
    A.IsSymmetricBoundedBy lmin' lmax'
/-- Transport along an isometric embedding with the same quadratic form (restrictions,
compressions). -/
theorem LinearMap.IsSymmetricBoundedBy.of_inner_eq (hA) {B : F →ₗ[𝕜] F} (hB : B.IsSymmetric)
    (ι : F →ₗᵢ[𝕜] E) (h : ∀ x, inner 𝕜 (B x) x = inner 𝕜 (A (ι x)) (ι x)) :
    B.IsSymmetricBoundedBy lmin lmax
theorem LinearMap.IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue [FiniteDimensional 𝕜 E]
    (hA : A.IsSymmetric) (lmin lmax : ℝ) :
    A.IsSymmetricBoundedBy lmin lmax ↔
      ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∈ Set.Icc lmin lmax
theorem LinearMap.IsSymmetric.isSymmetricBoundedBy_neg_norm_norm {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) : (A : E →ₗ[𝕜] E).IsSymmetricBoundedBy (-‖A‖) ‖A‖
/-- Damped-Richardson estimate `‖x − θ A x‖² ≤ (1 − 2θc + θ²‖A‖²) ‖x‖²` (AH proof #1 of Thm 8.3.4
and Thm 5.1.4; Saad Thm 5.10 / 6.30; Kress Richardson). -/
theorem ContinuousLinearMap.norm_sub_smul_apply_sq_le {A : E →L[𝕜] E} {c : ℝ}
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {θ : ℝ} (hθ : 0 ≤ θ) (x : E) :
    ‖x - (θ : 𝕜) • A x‖ ^ 2 ≤ (1 - 2 * θ * c + θ ^ 2 * ‖A‖ ^ 2) * ‖x‖ ^ 2
/-- Lax–Milgram flavour: coercive + bounded on a Hilbert space ⇒ invertible with `‖A⁻¹‖ ≤ 1/c`. -/
theorem ContinuousLinearMap.exists_equiv_of_isCoerciveWith [CompleteSpace E] {A : E →L[𝕜] E} {c : ℝ}
    (hc : 0 < c) (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) :
    ∃ e : E ≃L[𝕜] E, (e : E →L[𝕜] E) = A ∧ ‖(e.symm : E →L[𝕜] E)‖ ≤ 1 / c
/-- The Hermitian part `½(A + A†)` has the same quadratic form; the best coercivity constant of
`A` is `λmin(½(A + A†))` (Saad Thm 6.30's `μ`, (5.15)). -/
theorem ContinuousLinearMap.re_inner_hermitianPart_apply [CompleteSpace E] (A : E →L[𝕜] E) (x : E) :
    RCLike.re (inner 𝕜 (((2⁻¹ : 𝕜) • (A + adjoint A)) x) x) = RCLike.re (inner 𝕜 (A x) x)
theorem ContinuousLinearMap.isCoerciveWith_iff_hermitianPart [CompleteSpace E] (A : E →L[𝕜] E) (c : ℝ) :
    (A : E →ₗ[𝕜] E).IsCoerciveWith c ↔
      (((2⁻¹ : 𝕜) • (A + adjoint A) : E →L[𝕜] E) : E →ₗ[𝕜] E).IsCoerciveWith c
theorem Matrix.posDef_iff_isSymmetricCoercive (M : Matrix n n 𝕜) :
    M.PosDef ↔ (Matrix.toEuclideanLin M).IsSymmetricCoercive
```
The Hilbert-space inverse bound is the linear case of AH Thm 5.1.4; prove it directly from
Mathlib's real Lax–Milgram applied to the real part of `⟪A x, y⟫` (see 5.2.2 for the trick that
also gives the complex Lax–Milgram), or via closed range: `‖A x‖ ≥ c‖x‖` ⇒ closed range, coercivity
⇒ `range ᗮ = ⊥`.

#### 2.1.5 `InnerProductSpace/Energy.lean` (L1)
Serves Saad Prop 5.2, 5.5, Thm 5.9, Lemma 6.28, PCG; AH §5.6, §9.4; Fong–Saunders; Meurant §3.

```lean
/-- Energy inner product `⟪x, y⟫_A := ⟪A x, y⟫` and energy norm. -/
noncomputable def energyInner (A : E →ₗ[𝕜] E) (x y : E) : 𝕜 := inner 𝕜 (A x) y
noncomputable def energyNorm (A : E →ₗ[𝕜] E) (x : E) : ℝ := Real.sqrt (RCLike.re (inner 𝕜 (A x) x))
scoped[Energy] notation "⟪" x ", " y "⟫_[" A "]" => energyInner A x y
scoped[Energy] notation "‖" x "‖_[" A "]" => energyNorm A x
theorem LinearMap.IsSymmetricCoercive.energyNorm_sq (hA : A.IsSymmetricCoercive) (x : E) :
    energyNorm A x ^ 2 = RCLike.re (inner 𝕜 (A x) x)
/-- Norm equivalence `√c ‖x‖ ≤ ‖x‖_A ≤ √‖A‖ ‖x‖` (`A` bounded for the upper bound). -/
theorem LinearMap.IsCoerciveWith.norm_le_energyNorm {c : ℝ} (hc : 0 ≤ c) (hA : A.IsCoerciveWith c)
    (x : E) : Real.sqrt c * ‖x‖ ≤ energyNorm A x
theorem LinearMap.IsSymmetricCoercive.energyNorm_le_norm {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetricCoercive) (x : E) :
    energyNorm (A : E →ₗ[𝕜] E) x ≤ Real.sqrt ‖A‖ * ‖x‖
/-- `‖x* − x‖_A² = re⟪x* − x, r⟫` with `r = b − A x` (Saad Thm 5.9 proof, Meurant §3.3). -/
theorem LinearMap.IsSymmetricCoercive.energyNorm_error_sq_eq (hA : A.IsSymmetricCoercive)
    {b xstar x : E} (hstar : A xstar = b) :
    energyNorm A (xstar - x) ^ 2 = RCLike.re (inner 𝕜 (xstar - x) (b - A x))

/-- Type synonym of `E` carrying the energy inner product. -/
def WithEnergy (A : E →ₗ[𝕜] E) (_hA : A.IsSymmetricCoercive) : Type _ := E
noncomputable def WithEnergy.core : InnerProductSpace.Core 𝕜 (WithEnergy A hA)
noncomputable instance : NormedAddCommGroup (WithEnergy A hA)   -- `(core A hA).toNormedAddCommGroup`
noncomputable instance : InnerProductSpace 𝕜 (WithEnergy A hA)  -- `InnerProductSpace.ofCore`
def WithEnergy.equiv : E ≃ₗ[𝕜] WithEnergy A hA
@[simp] theorem WithEnergy.inner_equiv (x y : E) :
    inner 𝕜 (equiv A hA x) (equiv A hA y) = energyInner A x y   -- `rfl`
@[simp] theorem WithEnergy.norm_equiv (x : E) : ‖equiv A hA x‖ = energyNorm A x   -- `rfl`
/-- Orthogonality in the energy space is `A`-conjugacy. -/
theorem WithEnergy.inner_equiv_eq_zero_iff (x y : E) :
    inner 𝕜 (equiv A hA x) (equiv A hA y) = 0 ↔ inner 𝕜 (A x) y = 0
noncomputable def WithEnergy.submoduleMap (K : Submodule 𝕜 E) : Submodule 𝕜 (WithEnergy A hA) :=
  K.map (equiv A hA).toLinearMap
instance (K : Submodule 𝕜 E) [FiniteDimensional 𝕜 K] : FiniteDimensional 𝕜 (submoduleMap A hA K)
theorem WithEnergy.continuous_equiv {A : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetricCoercive) :
    Continuous (equiv (A : E →ₗ[𝕜] E) hA) ∧ Continuous (equiv (A : E →ₗ[𝕜] E) hA).symm
```
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

#### 2.1.6 `InnerProductSpace/Compression.lean` (L1)
Serves Saad Prop 6.3, 6.5 (`V_mᴴ A V_m = H_m`), Saad-eig Ch. 4 (Rayleigh–Ritz), Meurant §2, and
the compression trick of 3.9.

```lean
/-- Compression through an arbitrary projector `Q : E →ₗ K` with `Q x = x` on `K` (oblique
Rayleigh–Ritz; Saad Prop 6.3 for any projector). -/
def compressionBy {K : Submodule 𝕜 E} (Q : E →ₗ[𝕜] K) (A : E →ₗ[𝕜] E) : K →ₗ[𝕜] K :=
  Q.comp (A.comp K.subtype)
/-- Saad Prop 6.3: `p(A_K) x = p(A) x` if `Aⁱ x ∈ K` for `i ≤ deg p`; `Q (p(A) x) = p(A_K) x` if
`Aⁱ x ∈ K` for `i < deg p`. -/
theorem compressionBy.aeval_apply_of_forall_pow_mem (hQ : ∀ x : K, Q x = x) (p : 𝕜[X]) {x : K}
    (hx : ∀ i ≤ p.natDegree, (A ^ i) (x : E) ∈ K) :
    (aeval (compressionBy Q A) p x : E) = aeval A p (x : E)
theorem compressionBy.apply_aeval_of_forall_pow_lt_mem (hQ) (p : 𝕜[X]) {x : K}
    (hx : ∀ i < p.natDegree, (A ^ i) (x : E) ∈ K) :
    Q (aeval A p (x : E)) = aeval (compressionBy Q A) p x
/-- The compression (section) `P_K A|_K` of `A` to a subspace. -/
noncomputable def compression (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    K →ₗ[𝕜] K :=
  (K.orthogonalProjectionOnto : E →ₗ[𝕜] K).comp (A.comp K.subtype)
theorem compression.eq_compressionBy :
    compression A K = compressionBy (K.orthogonalProjectionOnto : E →ₗ[𝕜] K) A
theorem compression.aeval_apply_of_forall_pow_mem (p : 𝕜[X]) {x : K}
    (hx : ∀ i ≤ p.natDegree, (A ^ i) (x : E) ∈ K) :
    (aeval (compression A K) p x : E) = aeval A p (x : E)
theorem compression.inner_apply (x y : K) : inner 𝕜 (compression A K x) y = inner 𝕜 (A x) (y : E)
theorem compression.isSymmetric (hA : A.IsSymmetric) : (compression A K).IsSymmetric
/-- Matrix of the compression in an orthonormal basis `b` of `K` is `⟪b i, A (b j)⟫`. -/
theorem compression.toMatrix_orthonormalBasis (b : OrthonormalBasis ι 𝕜 K) :
    LinearMap.toMatrix b.toBasis b.toBasis (compression A K) =
      Matrix.of fun i j => inner 𝕜 (b i : E) (A (b j))
/-- On an `A`-invariant subspace the compression is the restriction. -/
theorem compression.apply_of_invt (hK : K ∈ Module.End.invtSubmodule A) (x : K) :
    (compression A K x : E) = A x
/-- Residual identity behind Saad-eig Thm 4.3. -/
theorem compression.apply_sub_smul_orthogonalProjection {u : E} {μ : 𝕜} (hu : A u = μ • u) :
    (compression A K (K.orthogonalProjectionOnto u) - μ • K.orthogonalProjectionOnto u : E) =
      K.starProjection (A (u - K.starProjection u))
```
The lemmas that make the compression the carrier of Chebyshev bounds in any inner product space
(`compression.isSymmetricBoundedBy`, `isSymmetricCoercive`, `energyInner_apply`,
`energyNorm_apply`) live in `Krylov/Convergence/Polynomial.lean` (3.9).

#### 2.1.7 `InnerProductSpace/ObliqueProjection.lean` (L1; Kato L2)
Serves Saad §1.12 (Lemma 1.36, Prop 1.37, (1.39)–(1.44)), Saad-eig §3.1, Saad §5.2.2 (`Q_K^L`),
AH Rem 9.2.2 (Xu–Zikatanov). Mathlib has `LinearMap.IsSymmetricProjection` and
`IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker` (= Saad Prop 1.37).

```lean
theorem LinearMap.IsIdempotentElem.ext_of_range_eq_of_ker_eq {P Q : E →ₗ[𝕜] E} (hP : IsIdempotentElem P)
    (hQ : IsIdempotentElem Q) (hr : LinearMap.range P = LinearMap.range Q)
    (hk : LinearMap.ker P = LinearMap.ker Q) : P = Q
/-- Saad (1.41): `P x` is the unique element of `K` with `x − P x ⟂ L`. -/
theorem LinearMap.IsIdempotentElem.apply_eq_iff {P : E →ₗ[𝕜] E} (hP : IsIdempotentElem P)
    {K L : Submodule 𝕜 E} (hr : LinearMap.range P = K) (hk : LinearMap.ker P = Lᗮ) (x y : E) :
    P x = y ↔ y ∈ K ∧ x - y ∈ Lᗮ
/-- Saad §1.12.1: existence and uniqueness iff `K ⊓ Lᗮ = ⊥` (equal finite dimensions). -/
theorem LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot {K L : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) (hKL : K ⊓ Lᗮ = ⊥) :
    ∃! P : E →ₗ[𝕜] E, IsIdempotentElem P ∧ LinearMap.range P = K ∧ LinearMap.ker P = Lᗮ
/-- `Wᴴ V = (⟪W i, V j⟫)` and the projector `V (Wᴴ V)⁻¹ Wᴴ` (Saad (1.44)). -/
noncomputable def LinearMap.crossGram (𝕜) (V W : ι → E) : Matrix ι ι 𝕜
noncomputable def LinearMap.obliqueProjectionOfBases (𝕜) (V W : ι → E) : E →ₗ[𝕜] E
theorem LinearMap.obliqueProjectionOfBases_isIdempotentElem (hVW : IsUnit (crossGram 𝕜 V W)) :
    IsIdempotentElem (obliqueProjectionOfBases 𝕜 V W)
theorem LinearMap.range_obliqueProjectionOfBases (hVW) :
    LinearMap.range (obliqueProjectionOfBases 𝕜 V W) = Submodule.span 𝕜 (Set.range V)
theorem LinearMap.ker_obliqueProjectionOfBases (hVW) :
    LinearMap.ker (obliqueProjectionOfBases 𝕜 V W) = (Submodule.span 𝕜 (Set.range W))ᗮ
theorem LinearMap.sub_obliqueProjectionOfBases_apply_mem_orthogonal (hVW) (x : E) :
    x - obliqueProjectionOfBases 𝕜 V W x ∈ (Submodule.span 𝕜 (Set.range W))ᗮ
theorem LinearMap.obliqueProjectionOfBases_self_eq_starProjection (hV : Orthonormal 𝕜 V) :
    obliqueProjectionOfBases 𝕜 V V = ((Submodule.span 𝕜 (Set.range V)).starProjection : E →ₗ[𝕜] E)
/-- Saad Thm 1.36 / AH Ex 3.6.7: a nonzero projector has norm `≥ 1`, `= 1` iff orthogonal. -/
theorem ContinuousLinearMap.IsIdempotentElem.norm_eq_one_iff_isSymmetric [CompleteSpace E]
    {P : E →L[𝕜] E} (hP : IsIdempotentElem P) (h0 : P ≠ 0) : ‖P‖ = 1 ↔ (P : E →ₗ[𝕜] E).IsSymmetric
/-- Kato's lemma `‖1 − P‖ = ‖P‖` (Szyld 2006; consumer: Xu–Zikatanov, phase 2). -/
theorem ContinuousLinearMap.IsIdempotentElem.norm_one_sub_eq [CompleteSpace E] {P : E →L[𝕜] E}
    (hP : IsIdempotentElem P) (h0 : P ≠ 0) (h1 : P ≠ 1) : ‖1 - P‖ = ‖P‖
```

#### 2.1.8 Polynomial glue (L0; in `Krylov/Subspace.lean` and `Krylov/Iterate.lean`)
Glue between `Polynomial.degreeLT`, `Polynomial.aeval` at an endomorphism and spans of iterates;
it lives next to the Krylov subspaces rather than in a separate module.

```lean
/-- `p ↦ p(A) v`. -/
noncomputable def Krylov.polyEval (A : Module.End R M) (v : M) : R[X] →ₗ[R] M
/-- Saad Prop 6.1: `𝒦_m = {p(A) v | deg p < m}`. -/
theorem Krylov.subspace_eq_map_degreeLT (A : Module.End R M) (v : M) (m : ℕ) :
    subspace A v m = (degreeLT R m).map (polyEval A v)
theorem Krylov.mem_subspace_iff_exists_aeval {x : M} {m : ℕ} :
    x ∈ subspace A v m ↔ ∃ p : R[X], p.degree < m ∧ aeval A p v = x
theorem Krylov.aeval_apply_mem_subspace {p : R[X]} {m : ℕ} (hp : p.degree < m) :
    aeval A p v ∈ subspace A v m
/-- Residual polynomials: `x − x₀ ∈ 𝒦_m(A, r₀)` ⇒ `b − A x = p(A) r₀` with `deg p ≤ m`, `p(0) = 1`,
and conversely every such `p` arises (`Krylov/Iterate.lean`). -/
theorem Krylov.exists_residual_poly (hx : x - x₀ ∈ subspace A (b - A x₀) m) :
    ∃ p : 𝕜[X], p.degree ≤ m ∧ p.eval 0 = 1 ∧ b - A x = aeval A p (b - A x₀)
theorem Krylov.exists_mem_of_residual_poly (p : 𝕜[X]) (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) :
    ∃ x, x - x₀ ∈ subspace A (b - A x₀) m ∧ b - A x = aeval A p (b - A x₀)
```

#### 2.1.9 `Polynomial/ChebyshevMinimax.lean` (analysis)
Serves Saad Thm 6.25/6.29, AH (5.6.5), Meurant (3.9), Saad-eig Thm 4.8, Ch. 6 (Kaniel–Paige–Saad).

```lean
namespace Polynomial.Chebyshev
/-- Closed form and the two-sided estimate `½ wᵐ ≤ T_m(x)`, `w = x + √(x²−1)`, `x ≥ 1`. -/
theorem eval_T_eq_half_add_pow {x : ℝ} (hx : 1 ≤ x) (m : ℕ) :
    (T ℝ m).eval x = ((x + Real.sqrt (x ^ 2 - 1)) ^ m + (x - Real.sqrt (x ^ 2 - 1)) ^ m) / 2
theorem half_pow_le_eval_T {x : ℝ} (hx : 1 ≤ x) (m : ℕ) :
    (x + Real.sqrt (x ^ 2 - 1)) ^ m / 2 ≤ (T ℝ m).eval x
theorem one_le_eval_T {x : ℝ} (hx : 1 ≤ x) (m : ℕ) : 1 ≤ (T ℝ m).eval x
/-- The shifted Chebyshev polynomial `T_m((b+a−2t)/(b−a)) / T_m((b+a−2γ)/(b−a))`, `= 1` at `γ`. -/
noncomputable def shifted (m : ℕ) (a b γ : ℝ) : ℝ[X]
theorem shifted_degree_le (m : ℕ) (a b γ : ℝ) : (shifted m a b γ).degree ≤ m
theorem shifted_eval_self (m : ℕ) {a b γ : ℝ} (hab : a < b) (hγ : γ ∉ Set.Icc a b) :
    (shifted m a b γ).eval γ = 1
/-- Min–max with general normalization point `γ ∉ [a, b]` (Saad Thm 6.25, Saad-eig Thm 4.8):
lower bound for every `p` with `deg p ≤ m`, `p(γ) = 1`, attained by `shifted`. -/
theorem one_div_eval_T_le_sSup_abs_eval (m : ℕ) {a b γ : ℝ} (hab : a < b) (hγ : γ ∉ Set.Icc a b)
    (p : ℝ[X]) (hp : p.degree ≤ m) (hpγ : p.eval γ = 1) :
    1 / |(T ℝ m).eval ((b + a - 2 * γ) / (b - a))| ≤ sSup ((fun t => |p.eval t|) '' Set.Icc a b)
theorem sSup_abs_eval_shifted (m : ℕ) {a b γ : ℝ} (hab : a < b) (hγ : γ ∉ Set.Icc a b) :
    sSup ((fun t => |(shifted m a b γ).eval t|) '' Set.Icc a b) =
      1 / |(T ℝ m).eval ((b + a - 2 * γ) / (b - a))|
/-- Special case `γ = 0`, `0 < a < b` (Saad Thm 6.29's ingredient). -/
theorem one_div_eval_T_le_sSup_abs_eval_of_eval_zero (m : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (p : ℝ[X]) (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) :
    1 / (T ℝ m).eval ((b + a) / (b - a)) ≤ sSup ((fun t => |p.eval t|) '' Set.Icc a b)
/-- `1 / T_m((κ+1)/(κ−1)) ≤ 2 ((√κ − 1)/(√κ + 1))^m` for `κ > 1` (Saad (6.128)). -/
theorem one_div_eval_T_le_two_mul_pow {κ : ℝ} (hκ : 1 < κ) (m : ℕ) :
    1 / (T ℝ m).eval ((κ + 1) / (κ - 1)) ≤ 2 * ((Real.sqrt κ - 1) / (Real.sqrt κ + 1)) ^ m
end Polynomial.Chebyshev
```
The general-`γ` version is the primary statement (the eigenvalue book needs it) and `γ = 0` is
derived. Difficult proof (moderate): Mathlib's `eval_iterate_derivative_le_of_forall_abs_le_one`
(k = 0) says `|P| ≤ 1` on `[−1,1]` ⇒ `P(x) ≤ T_m(x)` for `x ≥ 1`. Compose `p` with the affine map
`t ↦ (b + a − 2t)/(b − a)` (so `[a,b] ↦ [−1,1]`), rescale by the sup, and replace `p` by
`q.comp (-X)` when the image of `γ` is `≤ −1`, which avoids a separate parity argument. Degree
bookkeeping for `Polynomial.comp` and `sSup` of a continuous image of a compact interval are the
only frictions. The complex ellipse results (Saad Lemma 6.26, Thm 6.27, Cor 6.33) are phase 3.

#### 2.1.10 `Matrix/Hessenberg.lean` (L4)
Serves Saad §4.1 (`A = D − E − F`), §6.3–6.5, Choi §2.2, Fong–Saunders §4.2, Kress §7.5.

```lean
def Matrix.IsUpperHessenberg {n R} [LinearOrder n] [Zero R] (H : Matrix n n R) : Prop :=
  ∀ i j, (∃ k, j < k ∧ k < i) → H i j = 0
def Matrix.IsTridiagonal [Zero R] (T : Matrix n n R) : Prop
theorem Matrix.IsTridiagonal.isUpperHessenberg (hT : T.IsTridiagonal) : T.IsUpperHessenberg
/-- Rectangular `(m+1) × m` upper Hessenberg (Arnoldi's `H̄_m`). -/
def Matrix.IsUpperHessenbergRect [Zero R] {m : ℕ} (H : Matrix (Fin (m + 1)) (Fin m) R) : Prop :=
  ∀ (i : Fin (m + 1)) (j : Fin m), (j : ℕ) + 1 < (i : ℕ) → H i j = 0
/-- Strict lower / strict upper / diagonal parts. -/
def Matrix.strictLower (A : Matrix n n R) : Matrix n n R
def Matrix.strictUpper (A : Matrix n n R) : Matrix n n R
def Matrix.diagPart [DecidableEq n] (A : Matrix n n R) : Matrix n n R := Matrix.diagonal A.diag
theorem Matrix.diagPart_add_strictLower_add_strictUpper (A) : diagPart A + strictLower A + strictUpper A = A
/-- Saad's convention `A = D − E − F` with `E = −strictLower A`, `F = −strictUpper A`. -/
theorem Matrix.diagPart_sub_neg_strictLower_sub_neg_strictUpper (A) :
    diagPart A - (-strictLower A) - (-strictUpper A) = A
```
Only predicates and triangular parts are matrix-level; the Givens QR of the Hessenberg
coefficients is `ℕ`-indexed and lives with the Krylov transport layer (3.5). Keep this minimal —
no general QR theory.

#### 2.1.11 `Matrix/Complexify.lean` (L4)
Serves every real-matrix statement about spectral radii (Saad Thm 1.10–1.12, 4.1; Kress Thm 4.1).

```lean
def Matrix.complexify (A : Matrix n n ℝ) : Matrix n n ℂ := A.map Complex.ofReal
theorem Matrix.complexify_add / complexify_smul / complexify_mul / complexify_one / complexify_pow
theorem Matrix.isUnit_complexify_iff (A : Matrix n n ℝ) : IsUnit (complexify A) ↔ IsUnit A
theorem Matrix.mem_spectrum_complexify_iff (A : Matrix n n ℝ) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify A) ↔ (A.charpoly.map (algebraMap ℝ ℂ)).IsRoot μ
theorem Matrix.ofReal_mem_spectrum_complexify_iff (A : Matrix n n ℝ) (μ : ℝ) :
    (μ : ℂ) ∈ spectrum ℂ (complexify A) ↔ μ ∈ spectrum ℝ A
/-- The spectral radius of a real matrix, computed over `ℂ` (2.1.3). -/
noncomputable def Matrix.complexSpectralRadius (A : Matrix n n ℝ) : ENNReal :=
  spectralRadius ℂ (complexify A)
/-- `Aᵏ → 0 ↔ ρ(A) < 1` for real matrices (via 2.1.3). -/
theorem Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one (A : Matrix n n ℝ) :
    Tendsto (fun k => A ^ k) atTop (𝓝 0) ↔ complexSpectralRadius A < 1
theorem Matrix.complexSpectralRadius_le_of_norm {A : Matrix n n ℝ} [SeminormedAddCommGroup (Matrix n n ℝ)]
    [NormOneClass (Matrix n n ℝ)] [NormMulClass (Matrix n n ℝ)] : complexSpectralRadius A ≤ ‖A‖₊
```
Norm preservation under `complexify` for the scoped `l∞`/Frobenius norms is added when a
surface statement needs it (phase 2).

#### 2.1.12 `Matrix/Order.lean` (L4, phase 2)
Entrywise order and absolute value (`|A| ≤ |B|`, `|A * B| ≤ |A| * |B|`, monotonicity of products by
nonnegative matrices; Saad Prop 1.24/1.26, Higham §3.5). Watch out: Mathlib's `Matrix` order
instance in `Analysis/Matrix/Order.lean` is the *Loewner* order; the entrywise order must be a
scoped instance or go through `Matrix.of`/`Pi`. Needed by regular splittings (2.3.4) and by the
floating-point layer (§6).

#### 2.1.13 `InnerProductSpace/GramSchmidt.lean` (L1) — uniqueness of orthonormal bases of a flag
Serves Saad §6.3.2 (MGS and Householder Arnoldi agree with Alg 6.1 up to signs), P-6.1(f), Choi
and Fong–Saunders' identifications of Lanczos with CG/CR quantities, and block variants.

```lean
/-- An orthonormal family spanning the same flag as `f` is Gram–Schmidt up to unimodular scalars,
and equals it under the sign normalization `re ⟪u_j, f_j⟫ > 0`. -/
theorem InnerProductSpace.exists_norm_eq_one_smul_gramSchmidtNormed {f u : ℕ → E} (hu : Orthonormal 𝕜 u)
    (hspan : ∀ j, Submodule.span 𝕜 (u '' Set.Iic j) = Submodule.span 𝕜 (f '' Set.Iic j)) (j : ℕ) :
    ∃ ε : 𝕜, ‖ε‖ = 1 ∧ u j = ε • gramSchmidtNormed 𝕜 f j
theorem InnerProductSpace.eq_gramSchmidtNormed_of_re_inner_pos {f u : ℕ → E} (hu : Orthonormal 𝕜 u)
    (hspan : ∀ j, Submodule.span 𝕜 (u '' Set.Iic j) = Submodule.span 𝕜 (f '' Set.Iic j)) (j : ℕ)
    (hpos : 0 < RCLike.re (inner 𝕜 (u j) (f j))) : u j = gramSchmidtNormed 𝕜 f j
```

#### 2.1.14 `Matrix/ToEuclideanLin.lean` (L4) — matrices as operators on `EuclideanSpace`
The glue every matrix-level surface statement uses to reach the operator-level backbone.
Symmetric ↔ Hermitian is Mathlib's `Matrix.isSymmetric_toEuclideanLin_iff`; `Matrix.PosDef` ↔
symmetric coercive is `Matrix.posDef_iff_isSymmetricCoercive` (2.1.4).

```lean
theorem Matrix.toEuclideanLin_one : toEuclideanLin (1 : Matrix n n 𝕜) = LinearMap.id
theorem Matrix.toEuclideanLin_mul (A B : Matrix n n 𝕜) :
    toEuclideanLin (A * B) = toEuclideanLin A ∘ₗ toEuclideanLin B
theorem Matrix.toEuclideanLin_pow (A : Matrix n n 𝕜) (k : ℕ) : toEuclideanLin (A ^ k) = toEuclideanLin A ^ k
theorem Matrix.toEuclideanLin_conjTranspose (A : Matrix n n 𝕜) :
    toEuclideanLin Aᴴ = LinearMap.adjoint (toEuclideanLin A)
theorem Matrix.hasEigenvalue_toEuclideanLin_iff (A : Matrix n n 𝕜) (μ : 𝕜) :
    Module.End.HasEigenvalue (toEuclideanLin A) μ ↔ μ ∈ spectrum 𝕜 A
theorem Matrix.IsHermitian.hasEigenvalue_toEuclideanLin_iff (hA : A.IsHermitian) (μ : 𝕜) :
    Module.End.HasEigenvalue (toEuclideanLin A) μ ↔ ∃ i, (hA.eigenvalues i : 𝕜) = μ
theorem Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin (hA : A.IsHermitian) {lmin lmax : ℝ}
    (h : ∀ i, hA.eigenvalues i ∈ Set.Icc lmin lmax) : (toEuclideanLin A).IsSymmetricBoundedBy lmin lmax
theorem Matrix.krylov_subspace_toEuclideanLin (A : Matrix n n 𝕜) (v : EuclideanSpace 𝕜 n) (m : ℕ) :
    Krylov.subspace (toEuclideanLin A) v m =
      Submodule.span 𝕜 (Set.range fun i : Fin m => toEuclideanLin (A ^ (i : ℕ)) v)
/-- `V y = ∑ y_j • (column j of V)`: between the book's `V_m y` and the backbone's `∑ y_j • vec j`. -/
theorem Matrix.toEuclideanLin_apply_eq_sum (V : Matrix n m 𝕜) (y : m → 𝕜) :
    toEuclideanLin V (WithLp.toLp 2 y) = ∑ j, y j • (WithLp.toLp 2 (Vᵀ j) : EuclideanSpace 𝕜 n)
theorem Matrix.l2_opNorm_eq_norm_toEuclideanLin (A : Matrix n n 𝕜) :
    ‖A‖ = ‖LinearMap.toContinuousLinearMap (toEuclideanLin A)‖   -- scoped `Matrix.Norms.L2Operator`
```

### 2.2 `Numlib/LinearSolve/Perturbation.lean` (L2)
Serves Saad §1.13.2, AH §2.4.3 ((2.4.1) `cond(L)`), Kress Def 5.2/Thm 5.3 (stated for Banach
spaces), Higham Thm 7.1–7.2, Choi Thm 2.34, Fong–Saunders §3.

```lean
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Residual–error relation `‖x − y‖/‖x‖ ≤ κ(A) ‖b − A y‖/‖b‖` (AH (2.4.1), Kress). -/
theorem relative_error_le_condNumber_mul_relative_residual (A : E ≃L[𝕜] E) {b x y : E}
    (hx : A x = b) (hb : b ≠ 0) :
    ‖x - y‖ / ‖x‖ ≤ condNumber (A : E →L[𝕜] E) * (‖b - A y‖ / ‖b‖)
/-- Normwise perturbation bound (Saad (1.76) exact form, Higham Thm 7.2, Kress Thm 5.3). -/
theorem relative_error_le_condNumber [CompleteSpace E] (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E)
    {b Δb x y : E} (hx : A x = b) (hy : ((A : E →L[𝕜] E) + ΔA) y = b + Δb)
    (hsmall : ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ < 1) (hx0 : x ≠ 0) (hb : b ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤ condNumber (A : E →L[𝕜] E) / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖)
      * (‖ΔA‖ / ‖(A : E →L[𝕜] E)‖ + ‖Δb‖ / ‖b‖)
theorem exists_perturbed_solution [CompleteSpace E] (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E)
    (hsmall : ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ < 1) (b' : E) : ∃! y, ((A : E →L[𝕜] E) + ΔA) y = b'

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Normwise backward error with tolerances `α` on `A`, `β` on `b` (Fong–Saunders (3.2)). -/
noncomputable def backwardError (A : E →L[𝕜] E) (b y : E) (α β : ℝ) : ℝ :=
  ‖b - A y‖ / (α * ‖A‖ * ‖y‖ + β * ‖b‖)
/-- Rigal–Gaches / Titley-Péloquin (Higham Thm 7.1, Fong–Saunders (3.2)–(3.3)). -/
theorem isLeast_backwardError (A : E →L[𝕜] E) (b y : E) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hpos : 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖) :
    IsLeast {ξ : ℝ | ∃ (ΔA : E →L[𝕜] E) (Δb : E), (A + ΔA) y = b + Δb ∧
        ‖ΔA‖ ≤ ξ * α * ‖A‖ ∧ ‖Δb‖ ≤ ξ * β * ‖b‖}
      (backwardError A b y α β)
/-- The optimal perturbations `ΔA = ((1−ω)/‖y‖²) r ⊗ y`, `Δb = −ω r`. -/
theorem exists_optimal_perturbation (A : E →L[𝕜] E) (b y : E) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hpos : 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖) :
    ∃ (ΔA : E →L[𝕜] E) (Δb : E), (A + ΔA) y = b + Δb ∧
      ‖ΔA‖ = backwardError A b y α β * α * ‖A‖ ∧ ‖Δb‖ = backwardError A b y α β * β * ‖b‖
/-- Stopping rule (Fong–Saunders (3.4)). -/
theorem backwardError_le_iff (A : E →L[𝕜] E) (b y : E) {α β ξ : ℝ}
    (hpos : 0 < α * ‖A‖ * ‖y‖ + β * ‖b‖) :
    backwardError A b y α β ≤ ξ ↔ ‖b - A y‖ ≤ ξ * (α * ‖A‖ * ‖y‖ + β * ‖b‖)
```
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

```lean
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- One affine step `x ↦ G x + f`. -/
def Stationary.step (G : E →L[𝕜] E) (f : E) (x : E) : E := G x + f
theorem Stationary.step_iterate_sub {x' : E} (hfix : G x' + f = x') (x₀ : E) (k : ℕ) :
    (step G f)^[k] x₀ - x' = (G ^ k) (x₀ - x')
theorem Stationary.step_fixed_iff (x : E) : step G f x = x ↔ (1 - G) x = f
/-- Cor 4.2 / Kress Thm 3.48: `‖G‖ < 1` gives a contraction with the a priori bound (a posteriori form alongside). -/
theorem Stationary.contractingWith (hG : ‖G‖ < 1) : ContractingWith ⟨‖G‖, norm_nonneg _⟩ (step G f)
theorem Stationary.norm_iterate_sub_le [CompleteSpace E] (hG : ‖G‖ < 1) {x' : E} (hfix : G x' + f = x')
    (x₀ : E) (k : ℕ) : ‖(step G f)^[k] x₀ - x'‖ ≤ ‖G‖ ^ k / (1 - ‖G‖) * ‖step G f x₀ - x₀‖

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Saad Thm 4.1 (⇒), any complex Banach space. -/
theorem Stationary.tendsto_of_spectralRadius_lt_one [CompleteSpace F] (G : F →L[ℂ] F)
    (hG : spectralRadius ℂ G < 1) (f x₀ : F) :
    Tendsto (fun k => (step G f)^[k] x₀) atTop (𝓝 (Ring.inverse (1 - G) f))
theorem Stationary.isUnit_one_sub_of_spectralRadius_lt_one [CompleteSpace F] (G : F →L[ℂ] F)
    (hG : spectralRadius ℂ G < 1) : IsUnit (1 - G)
/-- Saad Thm 4.1 (⇐), finite dimension only (false in infinite dimension — e.g. the left shift). -/
theorem Stationary.spectralRadius_lt_one_of_forall_tendsto [FiniteDimensional ℂ F] (G : F →L[ℂ] F)
    (h : ∀ x₀, Tendsto (fun k => (G ^ k) x₀) atTop (𝓝 0)) : spectralRadius ℂ G < 1
theorem Stationary.forall_tendsto_iff_spectralRadius_lt_one [FiniteDimensional ℂ F] (G : F →L[ℂ] F) :
    (∀ f x₀, ∃ x, Tendsto (fun k => (step G f)^[k] x₀) atTop (𝓝 x)) ↔ spectralRadius ℂ G < 1
/-- Convergence factor: geometric rate at every `r > ρ(G)`. -/
theorem Stationary.exists_norm_iterate_sub_le [CompleteSpace F] (G : F →L[ℂ] F) {r : NNReal}
    (hr : spectralRadius ℂ G < r) (f : F) {x' : F} (hfix : G x' + f = x') :
    ∃ C : ℝ, ∀ x₀ k, ‖(step G f)^[k] x₀ - x'‖ ≤ C * (r : ℝ) ^ k * ‖x₀ - x'‖
```
The sharp form of the convergence factor (`limsup ‖G^k d‖^{1/k} = ρ(G)` for the worst `d`) is a
phase-2 sketch. Real spaces: apply to the complexification (matrices via 2.1.11; general real
Banach spaces are out of scope until Mathlib has complexification of operators).

#### 2.3.2 `Stationary/Splitting.lean` (L2 ring-level, L4 constructors)
Serves Saad §4.1 (Jacobi, GS, SOR, SSOR, (4.5)–(4.27)), AH §5.2.2, Kress §4.1–4.2, Higham Ch. 17.

```lean
/-- A splitting `a = m − n` with `m` a unit, in any ring (matrices, `E →L[𝕜] E`), determined by
`m` alone; `n := m − a` is derived, so the structure has no propositional field beyond `isUnit`. -/
@[ext] structure Stationary.Splitting {R : Type*} [Ring R] (a : R) where
  m : R
  isUnit : IsUnit m
def Stationary.Splitting.n (s : Splitting a) : R := s.m - a
theorem Stationary.Splitting.m_sub_n (s : Splitting a) : s.m - s.n = a
/-- Iteration operator `G = 1 − m⁻¹ a = m⁻¹ n` (Saad (4.28)/(4.30)). -/
noncomputable def Stationary.Splitting.iterationOperator (s : Splitting a) : R := 1 - Ring.inverse s.m * a
theorem Stationary.Splitting.iterationOperator_eq (s : Splitting a) :
    s.iterationOperator = Ring.inverse s.m * s.n
theorem Stationary.Splitting.one_sub_iterationOperator (s : Splitting a) :
    1 - s.iterationOperator = Ring.inverse s.m * a
/-- Consistency: fixed points of `x ↦ G x + m⁻¹ b` are exactly the solutions of `a x = b`. -/
theorem Stationary.Splitting.eq_iterationOperator_mul_add_iff (s : Splitting a) (x b : R) :
    x = s.iterationOperator * x + Ring.inverse s.m * b ↔ a * x = b
/-- Richardson: `m = α⁻¹ • 1`, `G = 1 − α • a`. -/
noncomputable def Stationary.Splitting.richardson [Field 𝕜] [Algebra 𝕜 R] (a : R) {α : 𝕜} (hα : α ≠ 0) :
    Splitting a
theorem Stationary.Splitting.richardson_iterationOperator (a : R) {α : 𝕜} (hα : α ≠ 0) :
    (richardson a hα).iterationOperator = 1 - α • a
-- matrix constructors (`[LinearOrder n]`, `[Field 𝕜]`), in Saad's letters `D`, `E`, `F`
theorem Matrix.isUnit_diagPart_iff (A : Matrix n n 𝕜) : IsUnit (diagPart A) ↔ ∀ i, A i i ≠ 0
theorem Matrix.isUnit_diagPart_add_strictLower / isUnit_diagPart_add_strictUpper (h : IsUnit (diagPart A))
noncomputable def Matrix.jacobiSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) : Splitting A   -- M = D
theorem Matrix.jacobiSplitting_iterationOperator (A) (h) :
    (jacobiSplitting A h).iterationOperator = -(diagPart A)⁻¹ * (strictLower A + strictUpper A)
noncomputable def Matrix.gaussSeidelSplitting (A) (h) : Splitting A          -- M = D − E
theorem Matrix.gaussSeidelSplitting_n (A) (h) : (gaussSeidelSplitting A h).n = -strictUpper A
noncomputable def Matrix.backwardGaussSeidelSplitting (A) (h) : Splitting A  -- M = D − F
noncomputable def Matrix.sorSplitting (A) (h) {ω : 𝕜} (hω : ω ≠ 0) : Splitting A   -- M = ω⁻¹ (D − ω E)
theorem Matrix.sorSplitting_iterationOperator (A) (h) (hω) :
    (sorSplitting A h hω).iterationOperator =
      (diagPart A + ω • strictLower A)⁻¹ * ((1 - ω) • diagPart A - ω • strictUpper A)
noncomputable def Matrix.ssorSplitting (A) (h) {ω : 𝕜} (hω : ω ≠ 0) (hω2 : ω ≠ 2) : Splitting A   -- (4.27)
theorem Matrix.sorSplitting_one (A) (h) : sorSplitting A h one_ne_zero = gaussSeidelSplitting A h
```
Saad's `A = D − E − F` is `D = diagPart A`, `E = −strictLower A`, `F = −strictUpper A`
(`Matrix.diagPart_sub_neg_strictLower_sub_neg_strictUpper`, 2.1.10); Atkinson–Han's convention
`A = N − M` swaps the roles of the letters, which the surface handles by an equivalence lemma.
Block splittings and the general overlapping block Jacobi/GS (Saad Alg 4.1–4.2) are phase 2 and
reuse `Projection/Additive.lean`.

#### 2.3.3 `Stationary/DiagDominant.lean` (L4)
Serves Saad Thm 4.6–4.9, Cor 4.8; Kress Thm 4.2 (Jacobi with the explicit constant `q_∞`), Thm 4.3
(Sassenfeld criterion for Gauss–Seidel), Cor 4.4, Problem 4.4 (column dominance); AH Ex 5.2.2.

```lean
def Matrix.IsStrictDiagDominant (A : Matrix n n 𝕜) : Prop :=
  ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖
def Matrix.IsStrictColDiagDominant (A : Matrix n n 𝕜) : Prop :=
  ∀ j, ∑ i ∈ Finset.univ.erase j, ‖A i j‖ < ‖A j j‖
theorem Matrix.IsStrictColDiagDominant.transpose_iff (A) : A.transpose.IsStrictDiagDominant ↔ A.IsStrictColDiagDominant
theorem Matrix.IsStrictDiagDominant.diag_ne_zero (hA) (i) : A i i ≠ 0
theorem Matrix.IsStrictDiagDominant.isUnit_diagPart (hA) : IsUnit (diagPart A)
/-- Saad Thm 4.6 (Mathlib `det_ne_zero_of_sum_row_lt_diag`). -/
theorem Matrix.IsStrictDiagDominant.isUnit (hA : A.IsStrictDiagDominant) : IsUnit A
/-- Kress Thm 4.2: `q_∞ = max_i ∑_{j≠i} |a_ij| / |a_ii|`. -/
noncomputable def Matrix.jacobiContraction [Nonempty n] (A : Matrix n n 𝕜) : ℝ
theorem Matrix.IsStrictDiagDominant.jacobiContraction_lt_one [Nonempty n] (hA) : jacobiContraction A < 1
/-- Sassenfeld numbers (Kress Thm 4.3), as the solution of `(|D| − |L|) p = |U| 𝟙`. -/
noncomputable def Matrix.sassenfeld (A : Matrix n n 𝕜) : n → ℝ
theorem Matrix.sassenfeld_eq (h : IsUnit (diagPart A)) (i : n) :
    sassenfeld A i = ((∑ j ∈ Finset.univ.filter (· < i), ‖A i j‖ * sassenfeld A j) +
      ∑ j ∈ Finset.univ.filter (i < ·), ‖A i j‖) / ‖A i i‖
-- `open scoped Matrix.Norms.Operator`
theorem Matrix.linfty_opNorm_jacobi_iterMatrix [Nonempty n] (A) (h : IsUnit (diagPart A)) :
    ‖(jacobiSplitting A h).iterationOperator‖ = jacobiContraction A
theorem Matrix.linfty_opNorm_gaussSeidel_iterMatrix_le [Nonempty n] (A) (h) :
    ‖(gaussSeidelSplitting A h).iterationOperator‖ ≤ Finset.univ.sup' Finset.univ_nonempty (sassenfeld A)
/-- Saad Thm 4.9. -/
theorem Matrix.jacobi_spectralRadius_lt_one (A : Matrix n n ℂ) (hA : A.IsStrictDiagDominant)
    (h : IsUnit (diagPart A)) : spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1
theorem Matrix.gaussSeidel_spectralRadius_lt_one (A : Matrix n n ℂ) (hA) (h) :
    spectralRadius ℂ (gaussSeidelSplitting A h).iterationOperator < 1
theorem Matrix.jacobi_spectralRadius_lt_one_of_col (A : Matrix n n ℂ) (hA : A.IsStrictColDiagDominant) (h) :
    spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1
```
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

```lean
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Petrov–Galerkin specification: `x ∈ x₀ + K`, `b − A x ⟂ L`. -/
structure IsPetrovGalerkin (A : E →ₗ[𝕜] E) (b x₀ : E) (K L : Submodule 𝕜 E) (x : E) : Prop where
  mem : x - x₀ ∈ K
  orth : b - A x ∈ Lᗮ
abbrev IsGalerkin (A : E →ₗ[𝕜] E) (b x₀ : E) (K : Submodule 𝕜 E) (x : E) : Prop :=
  IsPetrovGalerkin A b x₀ K K x
/-- Minimal residual over `x₀ + K`. -/
structure IsMinRes (A : E →ₗ[𝕜] E) (b x₀ : E) (K : Submodule 𝕜 E) (x : E) : Prop where
  mem : x - x₀ ∈ K
  min : ∀ y, y - x₀ ∈ K → ‖b - A x‖ ≤ ‖b - A y‖
/-- Minimal Euclidean error over `x₀ + K` with an explicit target (SYMMLQ, CGNE); no operator
appears, so the specification is meaningful for singular `A`. -/
structure IsMinError (xstar x₀ : E) (K : Submodule 𝕜 E) (x : E) : Prop where
  mem : x - x₀ ∈ K
  min : ∀ y, y - x₀ ∈ K → ‖xstar - x‖ ≤ ‖xstar - y‖

theorem IsPetrovGalerkin.inner_residual_eq_zero (hx : IsPetrovGalerkin A b x₀ K L x) {w : E}
    (hw : w ∈ L) : inner 𝕜 w (b - A x) = 0
/-- Uniqueness under Saad Prop 5.1's nondegeneracy condition. -/
theorem IsPetrovGalerkin.eq_of_forall (hx) {x' : E} (hx' : IsPetrovGalerkin A b x₀ K L x')
    (hKL : ∀ z ∈ K, A z ∈ Lᗮ → z = 0) : x = x'
/-- Saad Prop 5.6: exactness on invariant subspaces. -/
theorem IsPetrovGalerkin.eq_of_invt (hx) (hK : K ∈ Module.End.invtSubmodule A) (hr : b - A x₀ ∈ K)
    (hKL : ∀ z ∈ K, z ∈ Lᗮ → z = 0) : A x = b
/-- Restarting: a step from `x₀` is a step from any `x₁ ∈ x₀ + K`. -/
theorem IsPetrovGalerkin.of_mem (hx) {x₁ : E} (hx₁ : x₁ - x₀ ∈ K) : IsPetrovGalerkin A b x₁ K L x
/-- Saad Prop 5.3: `L = A K` ⇔ residual minimization. -/
theorem IsMinRes.iff_isPetrovGalerkin [FiniteDimensional 𝕜 K] :
    IsMinRes A b x₀ K x ↔ IsPetrovGalerkin A b x₀ K (K.map A) x
/-- Saad Prop 5.4: the residual is `(1 − P_{A K}) r₀`, hence unique even when `x` is not. -/
theorem IsMinRes.residual_eq [FiniteDimensional 𝕜 K] (hx : IsMinRes A b x₀ K x) :
    b - A x = (b - A x₀) - (K.map A).starProjection (b - A x₀)
theorem IsMinRes.residual_unique [FiniteDimensional 𝕜 K] (hx) {x' : E} (hx' : IsMinRes A b x₀ K x') :
    b - A x = b - A x'
theorem IsMinRes.norm_residual_le_norm_residual_zero (hx) : ‖b - A x‖ ≤ ‖b - A x₀‖
/-- Nested subspaces: residual norms are nonincreasing. -/
theorem IsMinRes.norm_residual_le {K' : Submodule 𝕜 E} {x' : E} (hx : IsMinRes A b x₀ K x)
    (hx' : IsMinRes A b x₀ K' x') (hKK' : K ≤ K') : ‖b - A x'‖ ≤ ‖b - A x‖
/-- Saad Prop 5.1 (i), (ii); existence needs nothing. -/
theorem existsUnique_isGalerkin_of_isCoercive (hA : A.IsCoercive) [FiniteDimensional 𝕜 K] :
    ∃! x, IsGalerkin A b x₀ K x
theorem existsUnique_isMinRes_of_injOn [FiniteDimensional 𝕜 K] (hinj : Set.InjOn A K) :
    ∃! x, IsMinRes A b x₀ K x
theorem exists_isMinRes [FiniteDimensional 𝕜 K] : ∃ x, IsMinRes A b x₀ K x
theorem exists_isMinError [FiniteDimensional 𝕜 K] (xstar : E) : ∃ x, IsMinError xstar x₀ K x
/-- Saad (5.7): with bases `V` of `K`, `W` of `L`, `x₀ + V y` is Petrov–Galerkin iff `(Wᴴ A V) y = Wᴴ r₀`. -/
theorem isPetrovGalerkin_iff_mulVec (V : Module.Basis ι 𝕜 K) (W : Module.Basis ι 𝕜 L) (y : ι → 𝕜) :
    IsPetrovGalerkin A b x₀ K L (x₀ + ∑ j, y j • (V j : E)) ↔
      (Matrix.of fun i j => inner 𝕜 (W i : E) (A (V j))).mulVec y =
        fun i => inner 𝕜 (W i : E) (b - A x₀)
```
Saad Thm 5.7 (`‖b − A_m x*‖ ≤ ‖Q A (1 − P_K)‖ ‖(1 − P_K) x*‖` for the projected operator) is a
phase-2 sketch (`norm_projected_residual_le`); its Galerkin/minimal-residual special cases are
covered by 2.4.2.

#### 2.4.2 `Projection/Optimality.lean` (L1)
Serves Saad Prop 5.2, 5.5; Fong–Saunders §2.1–2.2; Choi Table 2.5, §8.3 (CGNE/Craig); AH (5.6.14).

```lean
/-- Saad Prop 5.2 / HS Thm 4:3: for symmetric coercive `A`, Galerkin ⇔ energy-norm error
minimization (`⇒` for any `K`, `⇔` for finite-dimensional `K`). -/
theorem IsGalerkin.energyNorm_le (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x)
    (hstar : A xstar = b) {y : E} (hy : y - x₀ ∈ K) :
    energyNorm A (xstar - x) ≤ energyNorm A (xstar - y)
theorem IsGalerkin.iff_energyNorm_min (hA : A.IsSymmetricCoercive) (hstar : A xstar = b)
    [FiniteDimensional 𝕜 K] :
    IsGalerkin A b x₀ K x ↔
      x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K → energyNorm A (xstar - x) ≤ energyNorm A (xstar - y)
theorem IsGalerkin.energyInner_error_eq_zero (hA) (hx) (hstar) {z : E} (hz : z ∈ K) :
    energyInner A (xstar - x) z = 0
theorem IsGalerkin.energyNorm_le_of_le (hA) {K' : Submodule 𝕜 E} {x' : E} (hx : IsGalerkin A b x₀ K x)
    (hx' : IsGalerkin A b x₀ K' x') (hKK' : K ≤ K') (hstar : A xstar = b) :
    energyNorm A (xstar - x') ≤ energyNorm A (xstar - x)
/-- Fong–Saunders (2.1): the Galerkin iterate minimizes `φ(x) = ½ re⟪A x, x⟫ − re⟪b, x⟫`. -/
theorem IsGalerkin.quadratic_le (hA) (hx) {y : E} (hy : y - x₀ ∈ K) :
    RCLike.re (inner 𝕜 (A x) x) / 2 - RCLike.re (inner 𝕜 b x) ≤
      RCLike.re (inner 𝕜 (A y) y) / 2 - RCLike.re (inner 𝕜 b y)
/-- Saad Prop 5.5: the Galerkin error is the energy-orthogonal projection of `d₀` onto `K^{⟂_A}`. -/
theorem IsGalerkin.error_eq_starProjection (hA : A.IsSymmetricCoercive) (hx : IsGalerkin A b x₀ K x)
    (hstar : A xstar = b) [FiniteDimensional 𝕜 K] :
    WithEnergy.equiv A hA (xstar - x) =
      (WithEnergy.submoduleMap A hA K)ᗮ.starProjection (WithEnergy.equiv A hA (xstar - x₀))
-- minimal error
theorem IsMinError.norm_error_le_of_le {K' : Submodule 𝕜 E} {x' : E} (hx : IsMinError xstar x₀ K x)
    (hx' : IsMinError xstar x₀ K' x') (hKK' : K ≤ K') : ‖xstar - x'‖ ≤ ‖xstar - x‖
theorem IsMinError.eq_starProjection [K.HasOrthogonalProjection] (hx : IsMinError xstar x₀ K x) :
    x - x₀ = K.starProjection (xstar - x₀)
theorem IsMinError.unique (hx) (hx' : IsMinError xstar x₀ K x') : x = x'
/-- Minimal error over `x₀ + A† L` is Petrov–Galerkin with test space `L` (CGNE / Craig). -/
theorem IsMinError.isPetrovGalerkin_of_map_adjoint [FiniteDimensional 𝕜 E] {L : Submodule 𝕜 E}
    (hK : K = L.map (LinearMap.adjoint A)) (hstar : A xstar = b) (hx : IsMinError xstar x₀ K x) :
    IsPetrovGalerkin A b x₀ K L x
```

#### 2.4.3 `Projection/OneDimensional.lean` (L1)
Serves Saad §5.3 (Alg 5.2–5.4, Lemma 5.8, Thm 5.9, 5.10), Thm 6.30; AH (5.6.4) one-step rate;
Kress/AH Richardson.

```lean
/-- One projection step with `K = span{v}`, `L = span{w}`: `x + (⟪w, r⟫/⟪w, A v⟫) v` (Saad (5.12)). -/
noncomputable def Projection.step1 (A : E →ₗ[𝕜] E) (b : E) (v w : E) (x : E) : E :=
  x + (inner 𝕜 w (b - A x) / inner 𝕜 w (A v)) • v
theorem Projection.step1_isPetrovGalerkin (v w x : E) (h : inner 𝕜 w (A v) ≠ 0) :
    IsPetrovGalerkin A b x (𝕜 ∙ v) (𝕜 ∙ w) (step1 A b v w x)
noncomputable def Projection.steepestDescentStep (A : E →ₗ[𝕜] E) (b : E) (x : E) : E :=
  step1 A b (b - A x) (b - A x) x
noncomputable def Projection.minResStep (A : E →ₗ[𝕜] E) (b : E) (x : E) : E :=
  step1 A b (b - A x) (A (b - A x)) x
/-- Residual-norm steepest descent: `v = A† r`, `w = A v`. -/
noncomputable def Projection.residualNormSDStep [CompleteSpace E] (A : E →L[𝕜] E) (b : E) (x : E) : E
theorem Projection.steepestDescentStep_isGalerkin (x : E) (hA : A.IsCoercive) :
    IsGalerkin A b x (𝕜 ∙ (b - A x)) (steepestDescentStep A b x)
theorem Projection.minResStep_isMinRes (x : E) (hA : A.IsCoercive) :
    IsMinRes A b x (𝕜 ∙ (b - A x)) (minResStep A b x)
/-- Kantorovich inequality (Saad Lemma 5.8), inverse-free (`hy : A y = x`) and in any inner
product space. -/
theorem Projection.kantorovich_inequality {lmin lmax : ℝ} (hl : 0 < lmin)
    (hA : A.IsSymmetricBoundedBy lmin lmax) (x : E) {y : E} (hy : A y = x) :
    RCLike.re (inner 𝕜 (A x) x) * RCLike.re (inner 𝕜 y x) ≤
      (lmax + lmin) ^ 2 / (4 * lmax * lmin) * ‖x‖ ^ 4
/-- Saad Thm 5.9. -/
theorem Projection.energyNorm_steepestDescentStep_le {lmin lmax : ℝ} (hl : 0 < lmin)
    (hA : A.IsSymmetricBoundedBy lmin lmax) {xstar : E} (hstar : A xstar = b) (x : E) :
    energyNorm A (xstar - steepestDescentStep A b x) ≤
      (lmax - lmin) / (lmax + lmin) * energyNorm A (xstar - x)
/-- Saad Thm 5.10 (bounded coercive `A`, any inner product space): `‖r'‖ ≤ √(1 − c²/‖A‖²) ‖r‖`. -/
theorem Projection.norm_residual_minResStep_le {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) (b x : E) :
    ‖b - A (minResStep (A : E →ₗ[𝕜] E) b x)‖ ≤ Real.sqrt (1 - c ^ 2 / ‖A‖ ^ 2) * ‖b - A x‖
```
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

```lean
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- `𝒦_m(A, v) = span {v, A v, …, A^(m−1) v}`. -/
def Krylov.subspace (A : Module.End R M) (v : M) (m : ℕ) : Submodule R M :=
  Submodule.span R (Set.range fun i : Fin m => (A ^ (i : ℕ)) v)
scoped notation "𝒦[" A ", " v "] " m:max => Krylov.subspace A v m
/-- `span {A^i v | i : ℕ}`, the smallest `A`-invariant subspace containing `v`. -/
def Krylov.fullSubspace (A : Module.End R M) (v : M) : Submodule R M :=
  Submodule.span R (Set.range fun i : ℕ => (A ^ i) v)
instance (m : ℕ) : Module.Finite R (subspace A v m)
theorem Krylov.pow_apply_mem_subspace {i m : ℕ} (h : i < m) : (A ^ i) v ∈ subspace A v m
theorem Krylov.subspace_mono : Monotone (subspace A v)
theorem Krylov.fullSubspace_mem_invtSubmodule : fullSubspace A v ∈ Module.End.invtSubmodule A
theorem Krylov.subspace_eq_map_degreeLT (m : ℕ) : subspace A v m = (degreeLT R m).map (polyEval A v)
/-- `𝒦_{m+1} = 𝒦_m ↔ A^m v ∈ 𝒦_m`, and then `𝒦_m` is `A`-invariant. -/
theorem Krylov.subspace_succ_eq_iff (m : ℕ) :
    subspace A v (m + 1) = subspace A v m ↔ (A ^ m) v ∈ subspace A v m

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (A : Module.End K V) (v : V)

/-- The grade of `v`: the dimension of the cyclic subspace `𝒦_∞(A, v)`; `0` (junk) when that
subspace is infinite-dimensional. -/
noncomputable def Krylov.grade : ℕ := Module.finrank K (fullSubspace A v)
theorem Krylov.finiteDimensional_fullSubspace_iff :
    FiniteDimensional K (fullSubspace A v) ↔ ∃ m, (A ^ m) v ∈ subspace A v m
/-- `A^m v ∈ 𝒦_m ↔ ∃ p monic of degree m, p(A) v = 0`: the grade is the degree of the minimal
polynomial of `v` (Saad §6.2). -/
theorem Krylov.pow_apply_mem_subspace_iff_exists_monic (m : ℕ) :
    (A ^ m) v ∈ subspace A v m ↔ ∃ p : K[X], p.Monic ∧ p.natDegree = m ∧ aeval A p v = 0
theorem Krylov.grade_le_finrank [FiniteDimensional K V] : grade A v ≤ Module.finrank K V

variable [FiniteDimensional K (fullSubspace A v)]

/-- Saad's definition: the grade is the least `m` with `A^m v ∈ 𝒦_m`. -/
theorem Krylov.grade_eq_sInf : grade A v = sInf {m | (A ^ m) v ∈ subspace A v m}
theorem Krylov.grade_le_iff {m : ℕ} : grade A v ≤ m ↔ (A ^ m) v ∈ subspace A v m
/-- Saad Prop 6.1: `𝒦_m = 𝒦_grade` for `m ≥ grade`, and `𝒦_grade = 𝒦_∞` is invariant. -/
theorem Krylov.subspace_eq_of_grade_le {m : ℕ} (h : grade A v ≤ m) :
    subspace A v m = subspace A v (grade A v)
theorem Krylov.subspace_grade_mem_invtSubmodule : subspace A v (grade A v) ∈ Module.End.invtSubmodule A
theorem Krylov.linearIndependent_of_le_grade {m : ℕ} (h : m ≤ grade A v) :
    LinearIndependent K (fun i : Fin m => (A ^ (i : ℕ)) v)
/-- Saad Prop 6.2: `dim 𝒦_m = min(m, grade)`. -/
theorem Krylov.finrank_subspace (m : ℕ) : Module.finrank K (subspace A v m) = min m (grade A v)
```
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

```lean
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Arnoldi vectors: Gram–Schmidt of the Krylov sequence; `0` after breakdown. -/
noncomputable def Arnoldi.vec (A : E →ₗ[𝕜] E) (b : E) : ℕ → E :=
  InnerProductSpace.gramSchmidtNormed 𝕜 (fun i : ℕ => (A ^ i) b)
/-- `h i j = ⟪v i, A v j⟫`. -/
noncomputable def Arnoldi.coeff (A : E →ₗ[𝕜] E) (b : E) (i j : ℕ) : 𝕜 :=
  inner 𝕜 (vec A b i) (A (vec A b j))
theorem Arnoldi.vec_zero (hb : b ≠ 0) : vec A b 0 = (‖b‖⁻¹ : 𝕜) • b
theorem Arnoldi.norm_vec_eq_one_of_lt_grade [FiniteDimensional 𝕜 (fullSubspace A b)] {j : ℕ}
    (h : j < grade A b) : ‖vec A b j‖ = 1
/-- Saad Prop 6.6: breakdown at step `j` iff `j ≥ grade`. -/
theorem Arnoldi.vec_eq_zero_iff [FiniteDimensional 𝕜 (fullSubspace A b)] (j : ℕ) :
    vec A b j = 0 ↔ grade A b ≤ j
theorem Arnoldi.inner_vec_eq_zero {i j : ℕ} (h : i ≠ j) : inner 𝕜 (vec A b i) (vec A b j) = 0
theorem Arnoldi.orthonormal [FiniteDimensional 𝕜 (fullSubspace A b)] :
    Orthonormal 𝕜 (fun i : Fin (grade A b) => vec A b i)
/-- Saad Prop 6.4. -/
theorem Arnoldi.span_vec (m : ℕ) : Submodule.span 𝕜 (vec A b '' Set.Iio m) = subspace A b m
theorem Arnoldi.vec_mem_subspace (j : ℕ) : vec A b j ∈ subspace A b (j + 1)
noncomputable def Arnoldi.orthonormalBasis [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) : OrthonormalBasis (Fin m) 𝕜 (subspace A b m)
/-- Hessenberg structure. -/
theorem Arnoldi.coeff_eq_zero_of_lt {i j : ℕ} (h : j + 1 < i) : coeff A b i j = 0
/-- Arnoldi relation `A v_j = ∑_{i ≤ j+1} h_ij v_i` (Saad (6.9), Prop 6.5). -/
theorem Arnoldi.apply_vec (j : ℕ) :
    A (vec A b j) = ∑ i ∈ Finset.range (j + 2), coeff A b i j • vec A b i
/-- Algorithmic form (Saad Alg 6.1): `w_j = A v_j − ∑_{i≤j} h_ij v_i`, `h_{j+1,j} = ‖w_j‖`,
`v_{j+1} = w_j / ‖w_j‖`. -/
noncomputable def Arnoldi.w (j : ℕ) : E :=
  A (vec A b j) - ∑ i ∈ Finset.range (j + 1), coeff A b i j • vec A b i
theorem Arnoldi.w_eq_sub_starProjection (j : ℕ) :
    w A b j = A (vec A b j) - (subspace A b (j + 1)).starProjection (A (vec A b j))
theorem Arnoldi.coeff_succ_self (j : ℕ) : coeff A b (j + 1) j = (‖w A b j‖ : 𝕜)
theorem Arnoldi.vec_succ_eq (j : ℕ) : vec A b (j + 1) = (‖w A b j‖⁻¹ : 𝕜) • w A b j
theorem Arnoldi.coeff_succ_self_eq_zero_iff [FiniteDimensional 𝕜 (fullSubspace A b)] (j : ℕ) :
    coeff A b (j + 1) j = 0 ↔ grade A b ≤ j + 1
/-- Saad Prop 6.22 (band structure; Lanczos tridiagonality is `s = 2`): if `A` has an adjoint `B`
with `B v ∈ 𝒦_s(A, v)` for every `v`, then `h i j = 0` for `i + s ≤ j`. -/
theorem Arnoldi.coeff_eq_zero_of_adjoint_mem {B : E →ₗ[𝕜] E}
    (hB : ∀ x y, inner 𝕜 (A x) y = inner 𝕜 x (B y)) {s : ℕ} (hs : ∀ v, B v ∈ subspace A v s)
    {i j : ℕ} (h : i + s ≤ j) : coeff A b i j = 0
/-- `H̄_m : Matrix (Fin (m+1)) (Fin m) 𝕜`, `H_m`, `A V_m = V_{m+1} H̄_m`, `H_m = V_mᴴ A V_m`. -/
noncomputable def Arnoldi.hessenberg (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) 𝕜
noncomputable def Arnoldi.hessenbergSq (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜
theorem Arnoldi.hessenberg_isUpperHessenbergRect (m : ℕ) : (hessenberg A b m).IsUpperHessenbergRect
theorem Arnoldi.apply_sum (m : ℕ) (y : Fin m → 𝕜) :
    A (∑ j, y j • vec A b j) = ∑ i : Fin (m + 1), (hessenberg A b m).mulVec y i • vec A b i
theorem Arnoldi.hessenbergSq_eq_toMatrix_compression [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) :
    hessenbergSq A b m =
      LinearMap.toMatrix (orthonormalBasis A b hm).toBasis (orthonormalBasis A b hm).toBasis
        (compression A (subspace A b m))
/-- Basis-free Arnoldi relation `(1 − P_{m+1}) A v_m = h_{m+1,m} v_{m+1}` (Saad-eig Prop 6.6). -/
theorem Arnoldi.starProjection_apply_vec (m : ℕ) :
    A (vec A b m) - (subspace A b (m + 1)).starProjection (A (vec A b m)) =
      coeff A b (m + 1) m • vec A b (m + 1)
```
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

```lean
theorem Arnoldi.coeff_conj_of_isSymmetric (hA : A.IsSymmetric) (b : E) (i j : ℕ) :
    coeff A b i j = starRingEnd 𝕜 (coeff A b j i)
/-- Tridiagonal structure. -/
theorem Arnoldi.coeff_eq_zero_of_isSymmetric (hA : A.IsSymmetric) (b : E) {i j : ℕ} (h : i + 1 < j) :
    coeff A b i j = 0
theorem Arnoldi.coeff_diag_re_of_isSymmetric (hA) (b) (j : ℕ) : coeff A b j j = (RCLike.re (coeff A b j j) : 𝕜)
noncomputable def Lanczos.alpha (A : E →ₗ[𝕜] E) (b : E) (j : ℕ) : ℝ := RCLike.re (Arnoldi.coeff A b j j)
noncomputable def Lanczos.beta (A : E →ₗ[𝕜] E) (b : E) (j : ℕ) : ℝ := ‖Arnoldi.w A b j‖
theorem Lanczos.coe_beta (j : ℕ) : (beta A b j : 𝕜) = Arnoldi.coeff A b (j + 1) j
theorem Lanczos.coe_alpha (hA : A.IsSymmetric) (j : ℕ) : (alpha A b j : 𝕜) = Arnoldi.coeff A b j j
/-- `T_m` (real symmetric tridiagonal, even for complex Hermitian `A`) and `T̄_m`. -/
noncomputable def Lanczos.tridiag (A : E →ₗ[𝕜] E) (b : E) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ
noncomputable def Lanczos.tridiagExt (A : E →ₗ[𝕜] E) (b : E) (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℝ
theorem Lanczos.tridiag_isTridiagonal (m : ℕ) : (tridiag A b m).IsTridiagonal
theorem Lanczos.tridiag_isSymm (m : ℕ) : (tridiag A b m).IsSymm
/-- Three-term recurrence (Saad Alg 6.15): `A v_0 = α_0 v_0 + β_0 v_1` and
`A v_{j+1} = β_j v_j + α_{j+1} v_{j+1} + β_{j+1} v_{j+2}`. -/
theorem Lanczos.apply_vec_zero (hA : A.IsSymmetric) :
    A (Arnoldi.vec A b 0) = (alpha A b 0 : 𝕜) • Arnoldi.vec A b 0 + (beta A b 0 : 𝕜) • Arnoldi.vec A b 1
theorem Lanczos.apply_vec (hA : A.IsSymmetric) (j : ℕ) :
    A (Arnoldi.vec A b (j + 1)) =
      (beta A b j : 𝕜) • Arnoldi.vec A b j + (alpha A b (j + 1) : 𝕜) • Arnoldi.vec A b (j + 1) +
        (beta A b (j + 1) : 𝕜) • Arnoldi.vec A b (j + 2)
theorem Lanczos.w_succ_eq (hA) (j : ℕ) :
    Arnoldi.w A b (j + 1) = A (Arnoldi.vec A b (j + 1)) -
      (alpha A b (j + 1) : 𝕜) • Arnoldi.vec A b (j + 1) - (beta A b j : 𝕜) • Arnoldi.vec A b j
theorem Lanczos.beta_eq_zero_iff (hA) [FiniteDimensional 𝕜 (fullSubspace A b)] (j : ℕ) :
    beta A b j = 0 ↔ grade A b ≤ j + 1
/-- Rayleigh bound `α_j ∈ [λmin, λmax]`. -/
theorem Lanczos.alpha_mem_Icc (hA : A.IsSymmetric) {lmin lmax : ℝ} (hA' : A.IsSymmetricBoundedBy lmin lmax)
    [FiniteDimensional 𝕜 (fullSubspace A b)] {j : ℕ} (hj : j < grade A b) :
    alpha A b j ∈ Set.Icc lmin lmax
/-- `H_m = T_m` (Saad Thm 6.19). -/
theorem Lanczos.hessenbergSq_eq_map_tridiag (hA) (m : ℕ) :
    Arnoldi.hessenbergSq A b m = (tridiag A b m).map (algebraMap ℝ 𝕜)
theorem Lanczos.hessenberg_eq_map_tridiagExt (hA) (m : ℕ) :
    Arnoldi.hessenberg A b m = (tridiagExt A b m).map (algebraMap ℝ 𝕜)
/-- `A V_m = V_m T_m + β_m v_m e_mᵀ` (Saad (6.91)), coordinate form. -/
theorem Lanczos.apply_sum (hA) (m : ℕ) (y : Fin (m + 1) → 𝕜) :
    A (∑ j, y j • Arnoldi.vec A b j) =
      ∑ i : Fin (m + 1), ((tridiag A b (m + 1)).map (algebraMap ℝ 𝕜)).mulVec y i • Arnoldi.vec A b i +
        ((beta A b m : 𝕜) * y (Fin.last m)) • Arnoldi.vec A b (m + 1)
/-- Termination (Choi (2.4)): at `ℓ = grade`, `A V_ℓ = V_ℓ T_ℓ` and `𝒦_ℓ` is invariant. -/
theorem Lanczos.apply_sum_grade (hA) [FiniteDimensional 𝕜 (fullSubspace A b)] (y : Fin (grade A b) → 𝕜) :
    A (∑ j, y j • Arnoldi.vec A b j) =
      ∑ i : Fin (grade A b), ((tridiag A b (grade A b)).map (algebraMap ℝ 𝕜)).mulVec y i • Arnoldi.vec A b i
```
Choi Prop 2.2 / Cor 2.3 / Thm 2.4 (termination index ≤ `rank A + 1`, ≤ number of distinct
eigenvalues with nonzero weight) are L3 statements for `Krylov/Singular.lean` (phase 2).

### 3.4 `Krylov/Iterate.lean` (L1)
Serves Saad §6.4–6.5 (Prop 6.7, 6.10, Lemma 6.28, 6.31), Fong–Saunders §2, Choi Table 2.5,
Thm 2.25/3.1 (abstract core), AH (5.6.12)–(5.6.14).

```lean
/-- GMRES / MINRES / CR specification at step `m`. -/
abbrev Krylov.IsMinResIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) (x : E) : Prop :=
  IsMinRes A b x₀ (subspace A (b - A x₀) m) x
/-- FOM / CG / Lanczos-method specification. -/
abbrev Krylov.IsGalerkinIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) (x : E) : Prop :=
  IsGalerkin A b x₀ (subspace A (b - A x₀) m) x
/-- SYMMLQ / CGNE specification: minimal Euclidean error over `x₀ + A 𝒦_m(A, A (x* − x₀))`, with
the target `x*` explicit (2.4.1). -/
abbrev Krylov.IsMinErrorIterate (A : E →ₗ[𝕜] E) (xstar x₀ : E) (m : ℕ) (x : E) : Prop :=
  IsMinError xstar x₀ ((subspace A (A (xstar - x₀)) m).map A) x
theorem Krylov.residual_mem_subspace_succ (hx : x - x₀ ∈ subspace A (b - A x₀) m) :
    b - A x ∈ subspace A (b - A x₀) (m + 1)
-- minimal residual
theorem Krylov.exists_isMinResIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) : ∃ x, IsMinResIterate A b x₀ m x
theorem Krylov.existsUnique_isMinResIterate_of_injective (hA : Function.Injective A) (b x₀ : E) (m : ℕ) :
    ∃! x, IsMinResIterate A b x₀ m x
/-- Saad Lemma 6.31: `‖r_m‖ = min_{deg p ≤ m, p(0)=1} ‖p(A) r₀‖`. -/
theorem Krylov.IsMinResIterate.norm_residual_eq_iInf (hx : IsMinResIterate A b x₀ m x) :
    ‖b - A x‖ = ⨅ p : {p : 𝕜[X] // p.degree ≤ m ∧ p.eval 0 = 1}, ‖aeval A p.1 (b - A x₀)‖
theorem Krylov.IsMinResIterate.norm_residual_le_norm_aeval (hx) (p : 𝕜[X]) (hp : p.degree ≤ m)
    (hp0 : p.eval 0 = 1) : ‖b - A x‖ ≤ ‖aeval A p (b - A x₀)‖
theorem Krylov.IsMinResIterate.norm_residual_antitone {x : ℕ → E}
    (hx : ∀ k, IsMinResIterate A b x₀ k (x k)) : Antitone fun k => ‖b - A (x k)‖
/-- Lucky breakdown (Saad Prop 6.10 ⇒): at `m ≥ grade` the minimal-residual iterate is exact if
`A` is injective on `𝒦_grade`; converse (⇐, P-6.13) without any injectivity. -/
theorem Krylov.IsMinResIterate.apply_eq_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hx : IsMinResIterate A b x₀ m x) (hm : grade A (b - A x₀) ≤ m)
    (hinj : Set.InjOn A (subspace A (b - A x₀) (grade A (b - A x₀)))) : A x = b
theorem Krylov.grade_le_of_apply_eq [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hx : x - x₀ ∈ subspace A (b - A x₀) m) (hAx : A x = b) : grade A (b - A x₀) ≤ m
-- minimal error
theorem Krylov.IsMinErrorIterate.unique (hx : IsMinErrorIterate A xstar x₀ m x) (hx' : …) : x = x'
theorem Krylov.IsMinErrorIterate.norm_error_antitone {x : ℕ → E}
    (hx : ∀ k, IsMinErrorIterate A xstar x₀ k (x k)) : Antitone fun k => ‖xstar - x k‖
-- Galerkin
theorem Krylov.existsUnique_isGalerkinIterate_of_isCoercive (hA : A.IsCoercive) (b x₀ : E) (m : ℕ) :
    ∃! x, IsGalerkinIterate A b x₀ m x
/-- Saad Lemma 6.28: energy-norm analogue. -/
theorem Krylov.IsGalerkinIterate.energyNorm_error_eq_iInf (hA : A.IsSymmetricCoercive)
    (hx : IsGalerkinIterate A b x₀ m x) {xstar : E} (hstar : A xstar = b) :
    energyNorm A (xstar - x) =
      ⨅ p : {p : 𝕜[X] // p.degree ≤ m ∧ p.eval 0 = 1}, energyNorm A (aeval A p.1 (xstar - x₀))
theorem Krylov.IsGalerkinIterate.energyNorm_error_le_energyNorm_aeval (hA) (hx) (hstar) (p : 𝕜[X])
    (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) : energyNorm A (xstar - x) ≤ energyNorm A (aeval A p (xstar - x₀))
/-- Saad Prop 6.7: the Galerkin residual is a multiple of `v_m`; Galerkin residuals are orthogonal. -/
theorem Krylov.IsGalerkinIterate.residual_mem_span (hx : IsGalerkinIterate A b x₀ m x) :
    b - A x ∈ 𝕜 ∙ Arnoldi.vec A (b - A x₀) m
theorem Krylov.IsGalerkinIterate.inner_residual_eq_zero (hx) (hx' : IsGalerkinIterate A b x₀ m' x')
    (h : m ≠ m') : inner 𝕜 (b - A x) (b - A x') = 0
theorem Krylov.IsGalerkinIterate.apply_eq_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hx : IsGalerkinIterate A b x₀ m x) (hm : grade A (b - A x₀) ≤ m) : A x = b
theorem Krylov.IsGalerkinIterate.energyNorm_error_antitone (hA : A.IsSymmetricCoercive) {x : ℕ → E}
    (hx : ∀ k, IsGalerkinIterate A b x₀ k (x k)) {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => energyNorm A (xstar - x k)
/-- Any exact Krylov solution of a compatible system with symmetric `A` is the minimum-norm
solution (core of Choi Thm 2.25/3.1). -/
theorem Krylov.norm_le_of_apply_eq (hA : A.IsSymmetric) {b x : E} {m : ℕ} (hx : x ∈ subspace A b m)
    (hAx : A x = b) (y : E) (hy : A y = b) : ‖x‖ ≤ ‖y‖
```
Proof of `norm_le_of_apply_eq`: for symmetric `A`, `range A ⟂ ker A`; `b ∈ range A` gives
`𝒦_m(A, b) ≤ (ker A)ᗮ`; if `A y = b` then `y − x ∈ ker A` and Pythagoras. No completeness or finite
dimension needed. The MINRES-QLP specification (minimum-norm element of the minimal-residual set,
`Krylov.IsMinNormMinResIterate`) is a phase-2 sketch.

### 3.5 `Krylov/Hessenberg.lean` (transport to small problems; L1 + finite matrices)
Serves Saad §6.4 ((6.16)–(6.18)), §6.5 ((6.27)–(6.47), Prop 6.9, (6.62), (6.75), (6.80)–(6.81),
Lemma 6.16), Choi §2.2 ((2.18)–(2.24), Lemma 2.18–2.20), Fong–Saunders §4.2, Meurant (3.1). Three
layers: the Hessenberg relation for an arbitrary basis, FOM/GMRES in Arnoldi coordinates, and the
`ℕ`-indexed Givens QR with its spec-level identifications.

```lean
def Krylov.hessenbergOf (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) 𝕜 := Matrix.of fun i j => h i j
def Krylov.hessenbergSqOf (h : ℕ → ℕ → 𝕜) (m : ℕ) : Matrix (Fin m) (Fin m) 𝕜
/-- `β e₁ ∈ 𝕜^m`. -/
def Krylov.firstVec (β : 𝕜) (m : ℕ) : Fin m → 𝕜
/-- `A v_j = ∑_{i ≤ j+1} h i j v_i` with `h` upper Hessenberg, *without* orthogonality (Saad
(6.6)–(6.9)); IOM/DIOM/DQGMRES and the bi-Lanczos basis of QMR are instances. -/
structure Krylov.HessenbergRelation (A : E →ₗ[𝕜] E) (v : ℕ → E) (h : ℕ → ℕ → 𝕜) : Prop where
  apply_eq : ∀ j, A (v j) = ∑ i ∈ range (j + 2), h i j • v i
  eq_zero_of_lt : ∀ i j, j + 1 < i → h i j = 0
theorem Krylov.HessenbergRelation.apply_sum (hv) (m : ℕ) (y : Fin m → 𝕜) :
    A (∑ j, y j • v j) = ∑ i : Fin (m + 1), (hessenbergOf h m).mulVec y i • v i
/-- Saad (6.27): with `r₀ = β v₀`, the residual of `x₀ + V_m y` is `V_{m+1} (β e₁ − H̄_m y)`. -/
theorem Krylov.HessenbergRelation.residual_eq (hv) {b x₀ : E} {β : 𝕜} (hr : b - A x₀ = β • v 0)
    (m : ℕ) (y : Fin m → 𝕜) :
    b - A (x₀ + ∑ j, y j • v j) =
      ∑ i : Fin (m + 1), (firstVec β (m + 1) - (hessenbergOf h m).mulVec y) i • v i
/-- Saad Prop 6.7 / (6.18): `H_m y = β e₁` ⇒ residual `−(h_{m,m−1} y_{m−1}) v_m`. -/
theorem Krylov.HessenbergRelation.residual_eq_of_mulVec_eq (hv) (hr) {m : ℕ} (hm : 0 < m) (y : Fin m → 𝕜)
    (hy : (hessenbergSqOf h m).mulVec y = firstVec β m) :
    b - A (x₀ + ∑ j, y j • v j) = -(h m (m - 1) * y ⟨m - 1, _⟩) • v m
theorem Arnoldi.hessenbergRelation (A : E →ₗ[𝕜] E) (b : E) : HessenbergRelation A (vec A b) (coeff A b)

-- FOM / GMRES in Arnoldi coordinates, `[FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]`
/-- Saad (6.28): for `m ≤ grade`, `‖b − A (x₀ + V_m y)‖ = ‖β e₁ − H̄_m y‖₂`. -/
theorem Krylov.norm_residual_eq_norm_firstVec_sub_mulVec {m : ℕ} (hm : m ≤ grade A (b - A x₀)) (y : Fin m → 𝕜) :
    ‖b - A (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j)‖ =
      ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
        (Arnoldi.hessenberg A (b - A x₀) m).mulVec y) : EuclideanSpace 𝕜 (Fin (m + 1)))‖
/-- FOM (Saad (6.16)–(6.17)): `x₀ + V_m y` is the Galerkin iterate iff `H_m y = β e₁`; FOM is well
defined iff `H_m` is a unit. -/
theorem Krylov.isGalerkinIterate_iff_mulVec_eq {m : ℕ} (hm : m ≤ grade A (b - A x₀)) (y : Fin m → 𝕜) :
    IsGalerkinIterate A b x₀ m (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j) ↔
      (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec y = firstVec (‖b - A x₀‖ : 𝕜) m
theorem Krylov.isGalerkinIterate_iff_exists_mulVec_eq {m : ℕ} (hm) (x : E) :
    IsGalerkinIterate A b x₀ m x ↔ ∃ y : Fin m → 𝕜,
      (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec y = firstVec (‖b - A x₀‖ : 𝕜) m ∧
        x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j
theorem Krylov.existsUnique_isGalerkinIterate_iff_isUnit {m : ℕ} (hm : m ≤ grade A (b - A x₀)) :
    (∃! x, IsGalerkinIterate A b x₀ m x) ↔ IsUnit (Arnoldi.hessenbergSq A (b - A x₀) m)
theorem Krylov.residual_galerkin_eq {m : ℕ} (hm : 0 < m) (y : Fin m → 𝕜)
    (hy : (Arnoldi.hessenbergSq A (b - A x₀) m).mulVec y = firstVec (‖b - A x₀‖ : 𝕜) m) :
    b - A (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j) =
      -(Arnoldi.coeff A (b - A x₀) m (m - 1) * y ⟨m - 1, _⟩) • Arnoldi.vec A (b - A x₀) m
/-- GMRES (Saad (6.29)–(6.30)): `x₀ + V_m y` is the minimal-residual iterate iff `y` minimizes
`‖β e₁ − H̄_m z‖₂`. -/
theorem Krylov.isMinResIterate_iff_isMinOn {m : ℕ} (hm : m ≤ grade A (b - A x₀)) (y : Fin m → 𝕜) :
    IsMinResIterate A b x₀ m (x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j) ↔
      IsMinOn (fun z : Fin m → 𝕜 => ‖(WithLp.toLp 2 (firstVec (‖b - A x₀‖ : 𝕜) (m + 1) -
        (Arnoldi.hessenberg A (b - A x₀) m).mulVec z) : EuclideanSpace 𝕜 (Fin (m + 1)))‖) Set.univ y

-- Givens rotations, `ℕ`-indexed (Saad (6.37), (6.44)–(6.47), (6.80)–(6.81))
/-- Coefficients after `k` rotations; rotation `k` acts on rows `k, k+1` and annihilates `(k+1, k)`
with `[[c̄_k, s̄_k], [−s_k, c_k]]`, `ρ_k = √(|a|² + |d|²)`, `c_k = a/ρ_k`, `s_k = d/ρ_k`. -/
noncomputable def Krylov.rotated (h : ℕ → ℕ → 𝕜) : ℕ → ℕ → ℕ → 𝕜
noncomputable def Krylov.givensRho (h : ℕ → ℕ → 𝕜) (k : ℕ) : ℝ
noncomputable def Krylov.givensC (h : ℕ → ℕ → 𝕜) (k : ℕ) : 𝕜
noncomputable def Krylov.givensS (h : ℕ → ℕ → 𝕜) (k : ℕ) : 𝕜
/-- `γ_0 = β`, `γ_{k+1} = −s_k γ_k`; `g_k = c̄_k γ_k` (the rotated right-hand side). -/
noncomputable def Krylov.gamma (h : ℕ → ℕ → 𝕜) (β : 𝕜) : ℕ → 𝕜
noncomputable def Krylov.gvec (h : ℕ → ℕ → 𝕜) (β : 𝕜) (k : ℕ) : 𝕜
theorem Krylov.gamma_succ (β : 𝕜) (k : ℕ) : gamma h β (k + 1) = -givensS h k * gamma h β k
theorem Krylov.norm_gamma_eq_prod (β : 𝕜) (m : ℕ) : ‖gamma h β m‖ = (∏ k ∈ range m, ‖givensS h k‖) * ‖β‖
theorem Krylov.norm_givensC_sq_add_norm_givensS_sq (k : ℕ) (hρ : givensRho h k ≠ 0) :
    ‖givensC h k‖ ^ 2 + ‖givensS h k‖ ^ 2 = 1
theorem Krylov.rotated_succ_self (k : ℕ) : rotated h (k + 1) k k = (givensRho h k : 𝕜)
theorem Krylov.rotated_eq_of_le (k i j : ℕ) (hi : k + 1 ≤ i) : rotated h k i j = h i j
theorem Krylov.rotated_succ_eq_of_lt (hh : ∀ i j, j + 1 < i → h i j = 0) (k j : ℕ) (hj : j < k) (i : ℕ) :
    rotated h (k + 1) i j = rotated h k i j
theorem Krylov.rotated_eq_zero_of_lt (hh) (k i j : ℕ) (hj : j < k) (hij : j < i) : rotated h k i j = 0
theorem Krylov.rotated_last_row (hh) (m j : ℕ) (hj : j < m) : rotated h m m j = 0
/-- `Fin`-matrices built at the end: `Ω_k`, `Q_m = Ω_{m−1} ⋯ Ω_0`, `Q_m H̄_m = R̄_m`, `Q_m (β e₁)`. -/
noncomputable def Krylov.givensMatrix (h) (k m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜
noncomputable def Krylov.givensQ (h) (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜
theorem Krylov.givensMatrix_mem_unitaryGroup (k m : ℕ) (hρ : givensRho h k ≠ 0) :
    givensMatrix h k m ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜
theorem Krylov.givensQ_mul_hessenbergOf (m : ℕ) : givensQ h m * hessenbergOf h m = hessenbergOf (rotated h m) m
theorem Krylov.givensQ_mem_unitaryGroup (m : ℕ) (hρ : ∀ k < m, givensRho h k ≠ 0) :
    givensQ h m ∈ Matrix.unitaryGroup (Fin (m + 1)) 𝕜
theorem Krylov.givensQ_mulVec_firstVec (β : 𝕜) (m : ℕ) :
    (givensQ h m).mulVec (firstVec β (m + 1)) =
      fun i : Fin (m + 1) => if (i : ℕ) < m then gvec h β i else gamma h β m

-- identifications for the Arnoldi coefficients (`β = ‖r₀‖`, `h = Arnoldi.coeff A r₀`)
/-- Saad (6.42), Prop 6.9(3): `‖r^G_m‖ = |γ_m|`; (6.43)/(6.30): `R_m y = g_m`. -/
theorem Krylov.IsMinResIterate.norm_residual_eq_norm_gamma {m : ℕ} (hm : m ≤ grade A (b - A x₀)) {x : E}
    (hx : IsMinResIterate A b x₀ m x) :
    ‖b - A x‖ = ‖gamma (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) m‖
theorem Krylov.IsMinResIterate.exists_mulVec_rotated_eq {m : ℕ} (hm) {x : E} (hx) :
    ∃ y : Fin m → 𝕜, (hessenbergSqOf (rotated (Arnoldi.coeff A (b - A x₀)) m) m).mulVec y =
        (fun i : Fin m => gvec (Arnoldi.coeff A (b - A x₀)) (‖b - A x₀‖ : 𝕜) i) ∧
      x = x₀ + ∑ j, y j • Arnoldi.vec A (b - A x₀) j
/-- `‖r^G_{m+1}‖ = |s_m| ‖r^G_m‖` (Saad (6.47), Prop 6.9). -/
theorem Krylov.IsMinResIterate.norm_residual_succ_eq {m : ℕ} (hm : m + 1 ≤ grade A (b - A x₀)) {x x' : E}
    (hx : IsMinResIterate A b x₀ m x) (hx' : IsMinResIterate A b x₀ (m + 1) x') :
    ‖b - A x'‖ = ‖givensS (Arnoldi.coeff A (b - A x₀)) m‖ * ‖b - A x‖
/-- `H_{m+1}` is a unit iff `c_m ≠ 0` (Prop 6.9(1), Lemma 6.16); `‖r^F_{m+1}‖ = ‖r^G_{m+1}‖/|c_m|` (6.75). -/
theorem Krylov.isUnit_hessenbergSq_iff_givensC_ne_zero {m : ℕ} (hm : m + 1 ≤ grade A (b - A x₀)) :
    IsUnit (Arnoldi.hessenbergSq A (b - A x₀) (m + 1)) ↔ givensC (Arnoldi.coeff A (b - A x₀)) m ≠ 0
theorem Krylov.IsGalerkinIterate.norm_residual_eq_div_norm_givensC {m : ℕ} (hm : m + 1 ≤ grade A (b - A x₀))
    {xF xG : E} (hF : IsGalerkinIterate A b x₀ (m + 1) xF) (hG : IsMinResIterate A b x₀ (m + 1) xG) :
    ‖b - A xF‖ = ‖b - A xG‖ / ‖givensC (Arnoldi.coeff A (b - A x₀)) m‖
/-- `s_m` is real and nonnegative for Arnoldi coefficients (Saad §6.5.9). -/
theorem Krylov.givensS_arnoldi_eq (m : ℕ) :
    givensS (Arnoldi.coeff A (b - A x₀)) m =
      (‖Arnoldi.w A (b - A x₀) m‖ / givensRho (Arnoldi.coeff A (b - A x₀)) m : ℝ)
```
Because the rotations are computed from the infinite coefficient function, prefix stability across
`m` is automatic and no `Fin` casts appear before the final matrices; the spec-level identities
`|s_m| = ‖r^G_{m+1}‖/‖r^G_m‖`, `|c_m| = ‖r^G_{m+1}‖/‖r^F_{m+1}‖` make the Givens data
non-blocking for the Cullum–Greenbaum relations (3.6), which are proved without it. All finite-index
bookkeeping over an orthonormal family; this is where Saad's, Choi's and Fong–Saunders'
implementations meet. The Lanczos specializations (Choi (2.21) `‖r_k‖ = φ_k = β₁ s₁ ⋯ s_k`, the
MINRES residual recurrence `r_k = s_k² r_{k−1} − φ_k c_k v_{k+1}` of Choi Lemma 2.18 / Saad (6.55),
and Choi Lemma 2.19) are phase-2 sketches for `Krylov/Singular.lean`; the Galerkin residual in
Lanczos terms, `r_k = (−1)^k ‖r_k‖ v_{k+1}` (Saad (6.87)), is `CG.arnoldi_vec_eq` (3.7). SYMMLQ's
LQ factorization and MINRES-QLP's QLP are surface (Choi) unless a second source needs them.

### 3.6 `Krylov/Relations.lean` (L1)
Serves Saad §6.5.7–6.5.8 (Prop 6.12–6.17, Lemma 6.18, Alg 6.14, (6.65), (6.74), (6.79)),
Fong–Saunders (4.1), Choi Prop 2.16(3), Greenbaum Lemma 5.4.1.

```lean
/-- Weiss's smoothing coefficient: `s' = s + η (r − s)` with the residual-minimizing `η`. -/
noncomputable def Krylov.smoothingCoeff (s r : E) : 𝕜 := inner 𝕜 (r - s) (-s) / (‖r - s‖ ^ 2 : ℝ)
/-- Saad Lemma 6.18 (Weiss): if `r ⟂ s` then `1/‖s'‖² = 1/‖s‖² + 1/‖r‖²`. -/
theorem Krylov.inv_sq_norm_smoothing {s r : E} (hs : s ≠ 0) (hr : r ≠ 0) (horth : inner 𝕜 r s = 0) :
    let s' := s + (smoothingCoeff s r : 𝕜) • (r - s)
    1 / ‖s'‖ ^ 2 = 1 / ‖s‖ ^ 2 + 1 / ‖r‖ ^ 2
/-- Cullum–Greenbaum (Saad (6.65)). -/
theorem Krylov.inv_sq_norm_residual_minRes {m : ℕ} {xG xG' xF : E}
    (hG : IsMinResIterate A b x₀ m xG) (hG' : IsMinResIterate A b x₀ (m + 1) xG')
    (hF : IsGalerkinIterate A b x₀ (m + 1) xF) (h0 : b - A xG' ≠ 0) :
    1 / ‖b - A xG'‖ ^ 2 = 1 / ‖b - A xG‖ ^ 2 + 1 / ‖b - A xF‖ ^ 2
/-- Cor 6.14 and its consequences `‖r_m^G‖ ≤ ‖r_m^F‖`, Prop 6.15. -/
theorem Krylov.inv_sq_norm_residual_minRes_eq_sum {m : ℕ} {xG : E} {xF : ℕ → E}
    (hG : IsMinResIterate A b x₀ m xG) (hF : ∀ i ≤ m, IsGalerkinIterate A b x₀ i (xF i))
    (h0 : b - A xG ≠ 0) : 1 / ‖b - A xG‖ ^ 2 = ∑ i ∈ Finset.range (m + 1), 1 / ‖b - A (xF i)‖ ^ 2
theorem Krylov.norm_residual_minRes_le_galerkin {m : ℕ} {xG xF : E}
    (hG : IsMinResIterate A b x₀ m xG) (hF : IsGalerkinIterate A b x₀ m xF) : ‖b - A xG‖ ≤ ‖b - A xF‖
theorem Krylov.exists_norm_residual_galerkin_le {m : ℕ} {xG : E} {xF : ℕ → E} (hG) (hF) :
    ∃ i ≤ m, ‖b - A (xF i)‖ ≤ Real.sqrt (m + 1) * ‖b - A xG‖
/-- Iterate relation (6.74): `x_{m+1}^G = s_m² x_m^G + c_m² x_{m+1}^F`, `c_m² = ‖r^G_{m+1}‖²/‖r^F_{m+1}‖²`. -/
theorem Krylov.minRes_eq_combination {m : ℕ} {xG xG' xF : E} (hG) (hG') (hF) (hinj : Function.Injective A)
    (h0 : b - A xF ≠ 0) :
    xG' = ((1 - ‖b - A xG'‖ ^ 2 / ‖b - A xF‖ ^ 2 : ℝ) : 𝕜) • xG +
      ((‖b - A xG'‖ ^ 2 / ‖b - A xF‖ ^ 2 : ℝ) : 𝕜) • xF
/-- Brown (Prop 6.17, L3): stagnation at step `m+1` iff no Galerkin iterate exists there. -/
theorem Krylov.norm_residual_minRes_eq_iff_not_exists_galerkin [FiniteDimensional 𝕜 E] {m : ℕ} {xG xG' : E}
    (hG) (hG') (h0 : b - A xG' ≠ 0) [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))]
    (hm : m + 1 ≤ grade A (b - A x₀)) :
    ‖b - A xG'‖ = ‖b - A xG‖ ↔ ¬ ∃ xF, IsGalerkinIterate A b x₀ (m + 1) xF
/-- `A 𝒦_{m+1} = A 𝒦_m ⊔ 𝕜 ∙ (r^F_{m+1} − r^G_m)`: the key step of the smoothing proof. -/
theorem Krylov.map_subspace_succ_eq_sup_span {m : ℕ} {xG xF : E} (hG : IsMinResIterate A b x₀ m xG)
    (hF : IsGalerkinIterate A b x₀ (m + 1) xF) (hF0 : b - A xF ≠ 0) (hinj : Function.Injective A)
    [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] (hm : m + 1 ≤ grade A (b - A x₀)) :
    (subspace A (b - A x₀) (m + 1)).map A = (subspace A (b - A x₀) m).map A ⊔ 𝕜 ∙ ((b - A xF) - (b - A xG))
/-- Weiss's minimal-residual smoothing of a sequence of iterates (Saad Alg 6.14). -/
noncomputable def Krylov.mrs (A : E →ₗ[𝕜] E) (b : E) (xO : ℕ → E) : ℕ → E
/-- Saad §6.5.8 (Weiss, Zhou–Walker): smoothing the Galerkin iterates gives the minimal-residual
iterates; (6.79) the smoothed residual is the weighted average of the Galerkin residuals. -/
theorem Krylov.IsGalerkinIterate.mrs_isMinResIterate {xO : ℕ → E}
    (hO : ∀ m, IsGalerkinIterate A b x₀ m (xO m)) (hinj : Function.Injective A) (m : ℕ) :
    IsMinResIterate A b x₀ m (mrs A b xO m)
theorem Krylov.residual_mrs_eq {xO : ℕ → E} (hO) (hinj) (m : ℕ) (h0 : ∀ j ≤ m, b - A (xO j) ≠ 0) :
    b - A (mrs A b xO m) =
      (((∑ j ∈ Finset.range (m + 1), 1 / ‖b - A (xO j)‖ ^ 2)⁻¹ : ℝ) : 𝕜) •
        ∑ j ∈ Finset.range (m + 1), ((1 / ‖b - A (xO j)‖ ^ 2 : ℝ) : 𝕜) • (b - A (xO j))
```
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

```lean
structure CG.State (E : Type*) where (x r p : E)
/-- `α = ⟪r, r⟫ / ⟪A p, p⟫`; the Hestenes–Stiefel step; `β = ⟪r', r'⟫ / ⟪r, r⟫`. -/
noncomputable def CG.alpha (A : E →ₗ[𝕜] E) (s : State E) : 𝕜 := inner 𝕜 s.r s.r / inner 𝕜 (A s.p) s.p
noncomputable def CG.step (A : E →ₗ[𝕜] E) (s : State E) : State E
noncomputable def CG.beta (A : E →ₗ[𝕜] E) (s : State E) : 𝕜
def CG.init (A : E →ₗ[𝕜] E) (b x₀ : E) : State E := { x := x₀, r := b - A x₀, p := b - A x₀ }
noncomputable def CG.iterate (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : State E := (step A)^[k] (init A b x₀)
theorem CG.residual_eq (k : ℕ) : (iterate A b x₀ k).r = b - A (iterate A b x₀ k).x
-- with `(hA : A.IsSymmetricCoercive)`
/-- Well-definedness: `⟪A p_k, p_k⟫ > 0` as long as `r_k ≠ 0`; stationary once `r_k = 0`. -/
theorem CG.re_inner_apply_direction_pos {k : ℕ} (hr : (iterate A b x₀ k).r ≠ 0) :
    0 < RCLike.re (inner 𝕜 (A (iterate A b x₀ k).p) (iterate A b x₀ k).p)
theorem CG.iterate_eq_of_residual_eq_zero {k : ℕ} (hr : (iterate A b x₀ k).r = 0) (j : ℕ) :
    iterate A b x₀ (k + j) = iterate A b x₀ k
/-- Invariants (Saad Prop 6.20, HS): orthogonal residuals, `A`-conjugate directions,
`⟪r_i, p_j⟫ = ‖r_i‖²` for `i ≤ j` (`= 0` for `j < i`), `span{p_i} = span{r_i} = 𝒦_k`. -/
theorem CG.inner_residual_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).r = 0
theorem CG.inner_apply_direction_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (A (iterate A b x₀ i).p) (iterate A b x₀ j).p = 0
theorem CG.inner_residual_direction_eq {i j : ℕ} (h : i ≤ j) :
    inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p = (‖(iterate A b x₀ i).r‖ ^ 2 : ℝ)
theorem CG.span_direction_eq (k : ℕ) :
    Submodule.span 𝕜 (Set.range fun i : Fin k => (iterate A b x₀ i).p) = subspace A (b - A x₀) k
theorem CG.iterate_sub_mem (k : ℕ) : (iterate A b x₀ k).x - x₀ ∈ subspace A (b - A x₀) k
/-- CG realises the Galerkin specification. -/
theorem CG.isGalerkinIterate (k : ℕ) : IsGalerkinIterate A b x₀ k (iterate A b x₀ k).x
/-- CG residuals are the Lanczos vectors up to sign (Saad (6.101), Meurant (3.4)). -/
theorem CG.arnoldi_vec_eq (k : ℕ) (hr : (iterate A b x₀ k).r ≠ 0) :
    Arnoldi.vec A (b - A x₀) k =
      ((-1 : 𝕜) ^ k * (‖(iterate A b x₀ k).r‖⁻¹ : ℝ)) • (iterate A b x₀ k).r
/-- Termination (L3): `r_k = 0` iff `k ≥ grade`. -/
theorem CG.residual_eq_zero_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {k : ℕ}
    (hk : grade A (b - A x₀) ≤ k) : (iterate A b x₀ k).r = 0
theorem CG.residual_ne_zero_of_lt_grade [FiniteDimensional …] {k : ℕ} (hk : k < grade A (b - A x₀)) :
    (iterate A b x₀ k).r ≠ 0
-- with `(hstar : A xstar = b)`
/-- HS Thm 6:1 (Meurant Thm 11): `‖ε_k‖_A² − ‖ε_{k+1}‖_A² = α_k ‖r_k‖²`. -/
theorem CG.energyNorm_error_sq_sub (k : ℕ) :
    energyNorm A (xstar - (iterate A b x₀ k).x) ^ 2 - energyNorm A (xstar - (iterate A b x₀ (k + 1)).x) ^ 2 =
      RCLike.re (alpha A (iterate A b x₀ k)) * ‖(iterate A b x₀ k).r‖ ^ 2
/-- HS Thm 6:3 (Meurant Thm 12): `‖x* − x_k‖` is nonincreasing; so is `‖x* − x_k‖_A`. -/
theorem CG.norm_error_antitone : Antitone fun k => ‖xstar - (iterate A b x₀ k).x‖
theorem CG.energyNorm_error_antitone : Antitone fun k => energyNorm A (xstar - (iterate A b x₀ k).x)
/-- Steihaug: `‖x_k‖` is nondecreasing from `x₀ = 0`; `re ⟪p_i, p_j⟫ ≥ 0`. -/
theorem CG.norm_iterate_monotone : Monotone fun k => ‖(iterate A b 0 k).x‖
theorem CG.re_inner_direction_nonneg (i j : ℕ) : 0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (iterate A b x₀ j).p)
-- three-term form (Saad §6.7.2, Alg 6.19, (6.96)–(6.98))
noncomputable def CG.gamma (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) : 𝕜   -- `⟪r_m, r_m⟫ / ⟪A r_m, r_m⟫`
noncomputable def CG.rho (A : E →ₗ[𝕜] E) (b x₀ : E) : ℕ → 𝕜         -- `ρ_0 = 1`, (6.98)
theorem CG.iterate_succ_eq_three_term (hA : A.IsSymmetricCoercive) (m : ℕ)
    (hr : ∀ j ≤ m, (iterate A b x₀ j).r ≠ 0) :
    (iterate A b x₀ (m + 1)).x =
      rho A b x₀ m • ((iterate A b x₀ m).x + gamma A b x₀ m • (iterate A b x₀ m).r) +
        (1 - rho A b x₀ m) • (iterate A b x₀ (m - 1)).x
theorem CG.residual_succ_eq_three_term (hA) (m : ℕ) (hr) :
    (iterate A b x₀ (m + 1)).r =
      rho A b x₀ m • ((iterate A b x₀ m).r - gamma A b x₀ m • A (iterate A b x₀ m).r) +
        (1 - rho A b x₀ m) • (iterate A b x₀ (m - 1)).r
```
Difficult proofs: the invariants are a joint induction (standard; keep the induction hypothesis
as a bundled `CG.Invariant k` structure with the four orthogonality facts and the span equalities,
proved for `k+1` from `k`). Steihaug's monotonicity uses `⟪r_i, p_j⟫ = ‖r_i‖²` for `j ≥ i` and hence
`⟪p_i, p_j⟫ > 0` — a local argument, no termination needed. The Lanczos coefficients in terms of
the CG coefficients (Saad (6.102)–(6.103)) are surface corollaries of `arnoldi_vec_eq`; the
D-Lanczos / `LDLᵀ` derivation is surface (Saad Alg 6.17, Choi Table 2.6).

### 3.8 `Krylov/CR.lean` (L1; sign results L3)
Serves Saad §6.8–6.9 (Alg 6.20, Lemma 6.21), Fong–Saunders Thm 2.1–2.5, Choi Table 2.12.

```lean
structure CR.State (E : Type*) where (x r p q : E)   -- `q = A p`
/-- `α = ⟪r, A r⟫ / ⟪A p, A p⟫`; the Stiefel step with `β = ⟪r', A r'⟫ / ⟪r, A r⟫`, `q' = A r' + β q`. -/
noncomputable def CR.alpha (A : E →ₗ[𝕜] E) (s : State E) : 𝕜 := inner 𝕜 s.r (A s.r) / inner 𝕜 s.q s.q
noncomputable def CR.step (A : E →ₗ[𝕜] E) (s : State E) : State E
def CR.init (A : E →ₗ[𝕜] E) (b x₀ : E) : State E
noncomputable def CR.iterate (A : E →ₗ[𝕜] E) (b x₀ : E) (k : ℕ) : State E := (step A)^[k] (init A b x₀)
theorem CR.iterate_succ / residual_eq
theorem CR.q_eq (k : ℕ) : (iterate A b x₀ k).q = A (iterate A b x₀ k).p
-- with `(hA : A.IsSymmetricCoercive)`
/-- Fong–Saunders Thm 2.1 / Luenberger: `⟪A p_i, A p_j⟫ = 0` (`i ≠ j`), `⟪r_i, A p_j⟫ = 0` (`j < i`),
`⟪r_i, A r_j⟫ = 0` (`i ≠ j`). -/
theorem CR.inner_apply_direction_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (A (iterate A b x₀ i).p) (A (iterate A b x₀ j).p) = 0
theorem CR.inner_residual_apply_direction_eq_zero {i j : ℕ} (h : j < i) :
    inner 𝕜 (iterate A b x₀ i).r (A (iterate A b x₀ j).p) = 0
theorem CR.inner_residual_apply_residual_eq_zero {i j : ℕ} (h : i ≠ j) :
    inner 𝕜 (iterate A b x₀ i).r (A (iterate A b x₀ j).r) = 0
theorem CR.span_direction_eq (k : ℕ) : … = subspace A (b - A x₀) k
/-- CR realises the minimal-residual specification (`= MINRES = GMRES` on symmetric systems). -/
theorem CR.isMinResIterate (k : ℕ) : IsMinResIterate A b x₀ k (iterate A b x₀ k).x
/-- Fong–Saunders Thm 2.2 (a)–(f) on SPD systems (parts (d)–(f) use finite termination). -/
theorem CR.re_alpha_nonneg (k : ℕ) : 0 ≤ RCLike.re (alpha A (iterate A b x₀ k))
theorem CR.re_inner_direction_apply_direction_nonneg (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (A (iterate A b x₀ j).p))
theorem CR.re_inner_direction_nonneg [FiniteDimensional 𝕜 E] (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).p (iterate A b x₀ j).p)
theorem CR.re_inner_iterate_direction_nonneg [FiniteDimensional 𝕜 E] (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b 0 i).x (iterate A b 0 j).p)
theorem CR.re_inner_residual_direction_nonneg [FiniteDimensional 𝕜 E] (i j : ℕ) :
    0 ≤ RCLike.re (inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).p)
/-- Fong–Saunders Thm 2.3–2.5. -/
theorem CR.norm_iterate_monotone [FiniteDimensional 𝕜 E] : Monotone fun k => ‖(iterate A b 0 k).x‖
theorem CR.norm_error_antitone [FiniteDimensional 𝕜 E] {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => ‖xstar - (iterate A b x₀ k).x‖
theorem CR.energyNorm_error_antitone [FiniteDimensional 𝕜 E] {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => energyNorm A (xstar - (iterate A b x₀ k).x)
theorem CR.residual_eq_zero_of_grade_le [FiniteDimensional 𝕜 (fullSubspace A (b - A x₀))] {k : ℕ}
    (hk : grade A (b - A x₀) ≤ k) : (iterate A b x₀ k).r = 0
/-- Symmetric, possibly indefinite or singular `A`: without breakdown, CR is still minimal-residual. -/
theorem CR.isMinResIterate_of_no_breakdown (hA : A.IsSymmetric) (k : ℕ)
    (h1 : ∀ j < k, inner 𝕜 (iterate A b x₀ j).r (A (iterate A b x₀ j).r) ≠ 0)
    (h2 : ∀ j < k, (iterate A b x₀ j).q ≠ 0) : IsMinResIterate A b x₀ k (iterate A b x₀ k).x
/-- Saad Lemma 6.21 (GCR / ORTHOMIN / ORTHODIR): `AᴴA`-orthogonal directions spanning `𝒦_m` and
the update `x_{j+1} = x_j + (⟪A p_j, r_j⟫/‖A p_j‖²) p_j` give the minimal-residual iterate. -/
theorem Krylov.isMinResIterate_of_orthogonal_directions {A : E →ₗ[𝕜] E} {b x₀ : E} {m : ℕ} (p : ℕ → E)
    (horth : ∀ i < m, ∀ j < m, i ≠ j → inner 𝕜 (A (p i)) (A (p j)) = 0) (hne : ∀ i < m, A (p i) ≠ 0)
    (hspan : Submodule.span 𝕜 (Set.range fun i : Fin m => p i) = subspace A (b - A x₀) m)
    (x : ℕ → E) (hx0 : x 0 = x₀)
    (hstep : ∀ j, x (j + 1) = x j + (inner 𝕜 (A (p j)) (b - A (x j)) / inner 𝕜 (A (p j)) (A (p j))) • p j) :
    IsMinResIterate A b x₀ m (x m)
```
CR on symmetric coercive `A` is well defined (`⟪r, A r⟫ > 0` unless `r = 0`); on indefinite `A`
the recurrence may break down while the minimal-residual iterate still exists — that is why the
spec, not the recurrence, is canonical.

### 3.9 `Krylov/Convergence/Polynomial.lean` (L3 spectral bounds; L1 via the compression trick)
Serves Saad Thm 6.29 (proof), Prop 6.32, Cor 6.33; AH (5.6.16)–(5.6.19); Meurant (3.7)–(3.8);
Saad-eig Lemma 6.1.

```lean
/-- Spectral norm bound for polynomials in a symmetric operator (finite dimension), Euclidean and
energy-norm versions. -/
theorem LinearMap.IsSymmetric.norm_aeval_apply_le [FiniteDimensional 𝕜 E] (hA : A.IsSymmetric) {C : ℝ}
    (p : 𝕜[X]) (hC : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → ‖p.eval μ‖ ≤ C) (x : E) :
    ‖aeval A p x‖ ≤ C * ‖x‖
theorem LinearMap.IsSymmetric.energyNorm_aeval_apply_le [FiniteDimensional 𝕜 E] (hA : A.IsSymmetric)
    (hA' : A.IsSymmetricCoercive) {C : ℝ} (p : 𝕜[X]) (hC) (x : E) :
    energyNorm A (aeval A p x) ≤ C * energyNorm A x
/-- Saad Prop 6.32: `A = X D X⁻¹` with symmetric `D` ⇒ `‖p(A) x‖ ≤ κ(X) max_{σ(D)} |p| ‖x‖`. -/
theorem norm_aeval_apply_le_of_conj [FiniteDimensional 𝕜 E] {A D : E →ₗ[𝕜] E} (X : E ≃L[𝕜] E)
    (hconj : A = (X : E →ₗ[𝕜] E) ∘ₗ D ∘ₗ (X.symm : E →ₗ[𝕜] E)) (hD : D.IsSymmetric) {C : ℝ}
    (p : 𝕜[X]) (hC : ∀ μ : 𝕜, Module.End.HasEigenvalue D μ → ‖p.eval μ‖ ≤ C) (x : E) :
    ‖aeval A p x‖ ≤ ‖(X : E →L[𝕜] E)‖ * ‖(X.symm : E →L[𝕜] E)‖ * C * ‖x‖
/-- The compression trick: quadratic-form bounds, coercivity and the energy norm pass to
`compression A K` (2.1.6). -/
theorem compression.isSymmetricBoundedBy (A) (K) [K.HasOrthogonalProjection] {lmin lmax : ℝ}
    (hA : A.IsSymmetricBoundedBy lmin lmax) : (compression A K).IsSymmetricBoundedBy lmin lmax
theorem compression.isSymmetricCoercive (A) (K) (hA : A.IsSymmetricCoercive) :
    (compression A K).IsSymmetricCoercive
theorem compression.energyNorm_apply (x : K) : energyNorm (compression A K) x = energyNorm A x
/-- Real-interval form in any inner product space: `‖p(A) x‖ ≤ sup_{[a,b]} |p| ‖x‖`, and the
energy-norm version for `0 < a`. -/
theorem LinearMap.IsSymmetricBoundedBy.norm_aeval_map_apply_le (hA : A.IsSymmetricBoundedBy a b)
    (p : ℝ[X]) (x : E) :
    ‖aeval A (p.map (algebraMap ℝ 𝕜)) x‖ ≤ sSup ((fun t => |p.eval t|) '' Set.Icc a b) * ‖x‖
theorem LinearMap.IsSymmetricBoundedBy.energyNorm_aeval_map_apply_le (hA) (ha : 0 < a) (p : ℝ[X]) (x : E) :
    energyNorm A (aeval A (p.map (algebraMap ℝ 𝕜)) x) ≤
      sSup ((fun t => |p.eval t|) '' Set.Icc a b) * energyNorm A x
```
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

```lean
variable {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin < lmax) (hA : A.IsSymmetricBoundedBy lmin lmax)

/-- Sharp Chebyshev form (Saad (6.123)) and the geometric form (Saad Thm 6.29, AH (5.6.5)), for
*any* sequence of Galerkin iterates in any inner product space. -/
theorem Krylov.IsGalerkinIterate.energyNorm_error_le_div_eval_T {m : ℕ} {x xstar : E}
    (hx : IsGalerkinIterate A b x₀ m x) (hstar : A xstar = b) :
    energyNorm A (xstar - x) ≤ energyNorm A (xstar - x₀) / (T ℝ m).eval ((lmax + lmin) / (lmax - lmin))
theorem Krylov.IsGalerkinIterate.energyNorm_error_le {m : ℕ} {x xstar : E}
    (hx : IsGalerkinIterate A b x₀ m x) (hstar : A xstar = b) :
    energyNorm A (xstar - x) ≤
      2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ m * energyNorm A (xstar - x₀)
/-- The same bound for the residual of minimal-residual iterates on symmetric coercive systems. -/
theorem Krylov.IsMinResIterate.norm_residual_le {m : ℕ} {x : E} (hx : IsMinResIterate A b x₀ m x) :
    ‖b - A x‖ ≤ 2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ m * ‖b - A x₀‖
/-- One-step steepest-descent comparison (AH (5.6.6)). -/
theorem Krylov.sqrt_ratio_le_ratio {κ : ℝ} (hκ : 1 ≤ κ) :
    (Real.sqrt κ - 1) / (Real.sqrt κ + 1) ≤ (κ - 1) / (κ + 1)
/-- Saad Thm 6.30: each cycle of a restarted minimal-residual iteration on a bounded coercive `A`
beats one minimal-residual step (2.4.3), hence restarted GMRES(m) converges. -/
theorem Krylov.IsMinResIterate.norm_residual_le_of_isCoerciveWith {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {b x₀ x : E} {m : ℕ} (hm : 1 ≤ m)
    (hx : IsMinResIterate (A : E →ₗ[𝕜] E) b x₀ m x) :
    ‖b - A x‖ ≤ Real.sqrt (1 - c ^ 2 / ‖A‖ ^ 2) * ‖b - A x₀‖
theorem Krylov.restarted_minRes_tendsto {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hA : (A : E →ₗ[𝕜] E).IsCoerciveWith c) {b : E} {m : ℕ} (hm : 1 ≤ m) (x : ℕ → E)
    (hx : ∀ k, IsMinResIterate (A : E →ₗ[𝕜] E) b (x k) m (x (k + 1))) :
    Tendsto (fun k => ‖b - A (x k)‖) atTop (𝓝 0)
```
Proof: 3.4 (energy-norm polynomial characterization) + 3.9 (compression trick) + 2.1.9 with
`[a, b] = [λmin, λmax]`. Phase 2: the minimal-residual (MINRES) bound for symmetric indefinite `A`
via Chebyshev on two intervals; Winther's superlinear convergence for `A = 1 − K`, `K` compact
self-adjoint (AH Thm 5.6.2; needs the compact spectral theorem, not in Mathlib).

### 3.11 `Krylov/Monotonicity.lean` (Fong–Saunders; L3)
Serves Fong–Saunders §2–3 and Table 5.1; Choi Lemma 2.14, 2.20; Steihaug.

```lean
variable [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetricCoercive) {b : E}

/-- On SPD systems the minimal-residual iterates are the CR iterates and the Galerkin iterates
are the CG iterates (uniqueness from 2.4.1 / 3.4). -/
theorem Krylov.IsMinResIterate.eq_CR_iterate {x₀ : E} {k : ℕ} {x : E} (hx : IsMinResIterate A b x₀ k x) :
    x = (CR.iterate A b x₀ k).x
theorem Krylov.IsGalerkinIterate.eq_CG_iterate {x₀ : E} {k : ℕ} {x : E} (hx : IsGalerkinIterate A b x₀ k x) :
    x = (CG.iterate A b x₀ k).x
/-- Fong–Saunders Thm 2.3–2.5 in specification form. -/
theorem Krylov.IsMinResIterate.norm_monotone {x : ℕ → E} (hx : ∀ k, IsMinResIterate A b 0 k (x k)) :
    Monotone fun k => ‖x k‖
theorem Krylov.IsMinResIterate.norm_error_antitone {x₀ : E} {x : ℕ → E}
    (hx : ∀ k, IsMinResIterate A b x₀ k (x k)) {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => ‖xstar - x k‖
theorem Krylov.IsMinResIterate.energyNorm_error_antitone {x₀ : E} {x : ℕ → E}
    (hx : ∀ k, IsMinResIterate A b x₀ k (x k)) {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => energyNorm A (xstar - x k)
/-- Fong–Saunders Thm 3.1: the normwise relative backward error `‖r_k‖/(α ‖A‖ ‖x_k‖ + β ‖b‖)`
(2.2) is nonincreasing; `0 < β` and `b ≠ 0` keep the denominator positive. The pure-ratio form
`‖r_k‖/‖x_k‖` is antitone from step `1` on (`‖b‖/‖0‖` is junk at `k = 0`). -/
theorem Krylov.IsMinResIterate.backwardError_antitone {x : ℕ → E} (hx : ∀ k, IsMinResIterate A b 0 k (x k))
    {normA α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) (hnormA : 0 ≤ normA) (hb : b ≠ 0) :
    Antitone fun k => ‖b - A (x k)‖ / (α * normA * ‖x k‖ + β * ‖b‖)
theorem Krylov.IsMinResIterate.norm_residual_div_norm_antitoneOn {x : ℕ → E}
    (hx : ∀ k, IsMinResIterate A b 0 k (x k)) (hb : b ≠ 0) :
    AntitoneOn (fun k => ‖b - A (x k)‖ / ‖x k‖) (Set.Ici 1)
/-- Steihaug (Table 5.1, CG column) and HS Thm 6:3 in specification form. -/
theorem Krylov.IsGalerkinIterate.norm_monotone {x : ℕ → E} (hx : ∀ k, IsGalerkinIterate A b 0 k (x k)) :
    Monotone fun k => ‖x k‖
theorem Krylov.IsGalerkinIterate.norm_error_antitone {x₀ : E} {x : ℕ → E}
    (hx : ∀ k, IsGalerkinIterate A b x₀ k (x k)) {xstar : E} (hstar : A xstar = b) :
    Antitone fun k => ‖xstar - x k‖
```
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

```lean
namespace LinearMap.IsSymmetric
-- [FiniteDimensional 𝕜 E], {A : E →ₗ[𝕜] E}, (hA : A.IsSymmetric)
/-- Residual bound (Saad-eig Cor 3.3): some eigenvalue lies within `‖A x − θ x‖/‖x‖` of `θ`. -/
theorem exists_hasEigenvalue_dist_le (θ : ℝ) {x : E} (hx : x ≠ 0) :
    ∃ μ : 𝕜, Module.End.HasEigenvalue A μ ∧ ‖μ - (θ : 𝕜)‖ ≤ ‖A x - (θ : 𝕜) • x‖ / ‖x‖
/-- Saad-eig Lemma 3.2: if `(α, β) ∋ θ` contains no eigenvalue, `(β − θ)(θ − α) ≤ ‖r‖²`. -/
theorem rayleigh_gap_le_norm_residual_sq {x : E} (hx : ‖x‖ = 1) {α β : ℝ} (hαβ : α < θ ∧ θ < β)
    (hfree : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∉ Set.Ioo α β) :
    (β - θ) * (θ - α) ≤ ‖r‖ ^ 2
/-- Kato–Temple (Saad-eig Thm 3.8): if `(a, b) ∋ θ` contains exactly one eigenvalue `μ`, then
`−‖r‖²/(θ − a) ≤ re μ − θ ≤ ‖r‖²/(b − θ)`. -/
theorem kato_temple {x : E} (hx : ‖x‖ = 1) {a b : ℝ} {μ : 𝕜} (hμ : Module.End.HasEigenvalue A μ)
    (hab : a < θ ∧ θ < b) (hμab : RCLike.re μ ∈ Set.Ioo a b)
    (hunique : ∀ μ' : 𝕜, Module.End.HasEigenvalue A μ' → RCLike.re μ' ∈ Set.Ioo a b → μ' = μ) :
    -(‖r‖ ^ 2 / (θ - a)) ≤ RCLike.re μ - θ ∧ RCLike.re μ - θ ≤ ‖r‖ ^ 2 / (b - θ)
/-- Saad-eig Cor 3.4: `|re μ − θ| ≤ ‖r‖²/δ` with `δ` the gap from `θ` to the other eigenvalues,
given that `μ` is the eigenvalue within `‖r‖` of `θ`. -/
theorem abs_sub_rayleigh_le_norm_residual_sq_div {x : E} (hx : ‖x‖ = 1) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue A μ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ μ' : 𝕜, Module.End.HasEigenvalue A μ' → μ' ≠ μ → δ ≤ |RCLike.re μ' - θ|)
    (hclose : |RCLike.re μ - θ| ≤ ‖r‖) : |RCLike.re μ - θ| ≤ ‖r‖ ^ 2 / δ
/-- Rayleigh quotient bounds (Saad-eig Thm 1.9, Kress Thm 7.3): `λmin ≤ re⟪A x, x⟫/‖x‖² ≤ λmax`. -/
theorem rayleigh_mem_Icc {lmin lmax : ℝ}
    (hspec : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ → RCLike.re μ ∈ Set.Icc lmin lmax) {x : E}
    (hx : x ≠ 0) : RCLike.re (inner 𝕜 (A x) x) / ‖x‖ ^ 2 ∈ Set.Icc lmin lmax
end LinearMap.IsSymmetric

/-- Backward error of an approximate eigenpair (Saad-eig Prop 3.4, the eigenvalue analogue of
Rigal–Gaches): the least `‖ΔA‖` with `(A − ΔA) u = θ u` (`‖u‖ = 1`) is `‖A u − θ u‖`, attained by
the rank-one `r uᴴ`. -/
theorem isLeast_eigen_backwardError (A : E →L[𝕜] E) {u : E} (hu : ‖u‖ = 1) (θ : 𝕜) :
    IsLeast {ε : ℝ | ∃ ΔA : E →L[𝕜] E, (A - ΔA) u = θ • u ∧ ‖ΔA‖ = ε} ‖A u - θ • u‖
/-- Bendixson (Saad Thm 1.35): the real part of every eigenvalue of `A` lies between the bounds of
its symmetric part `H = (A + A†)/2`, given through `IsSymmetricBoundedBy` (1.3). -/
theorem re_hasEigenvalue_mem_Icc_of_symmetricPart {A H : E →ₗ[𝕜] E} {lmin lmax : ℝ}
    (hH : H.IsSymmetricBoundedBy lmin lmax)
    (hHA : ∀ x, RCLike.re (inner 𝕜 (H x) x) = RCLike.re (inner 𝕜 (A x) x)) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue A μ) : RCLike.re μ ∈ Set.Icc lmin lmax

namespace Matrix   -- open scoped Matrix.Norms.L2Operator
/-- Bauer–Fike (Saad-eig Thm 3.6, Kress Problem 7.6): for `A = X D X⁻¹` and `μ ∈ σ(A + ΔA)`,
`dist(μ, σ(A)) ≤ κ₂(X) ‖ΔA‖₂`. -/
theorem bauer_fike (X : Matrix n n ℂ) (d : n → ℂ) (hX : IsUnit X) (ΔA : Matrix n n ℂ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (X * Matrix.diagonal d * X⁻¹ + ΔA)) :
    ∃ i, ‖μ - d i‖ ≤ NormedRing.condNumber X * ‖ΔA‖
/-- Residual form: `dist(θ, σ(A)) ≤ κ₂(X) ‖A u − θ u‖` for a unit approximate eigenpair. -/
theorem bauer_fike_residual (X : Matrix n n ℂ) (d : n → ℂ) (hX : IsUnit X)
    {u : EuclideanSpace ℂ n} (hu : ‖u‖ = 1) (θ : ℂ) :
    ∃ i, ‖θ - d i‖ ≤ NormedRing.condNumber X *
      ‖Matrix.toEuclideanLin (X * Matrix.diagonal d * X⁻¹) u - θ • u‖
/-- Gershgorin discs, union form (Saad-eig Thm 3.11, Kress Thm 7.7); Mathlib's
`eigenvalue_mem_ball` is the pointwise version. -/
theorem spectrum_subset_iUnion_closedBall (A : Matrix n n ℂ) :
    spectrum ℂ A ⊆ ⋃ i, Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖)
end Matrix
```
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

```lean
/-- `v ∈ K` is a best approximation of `u` from `K`. -/
def IsBestApprox (K : Set V) (u v : V) : Prop := v ∈ K ∧ ∀ w ∈ K, ‖u - v‖ ≤ ‖u - w‖
theorem IsBestApprox.norm_sub_eq_infDist (h : IsBestApprox K u v) : ‖u - v‖ = Metric.infDist u K
theorem isBestApprox_iff_norm_sub_eq_infDist (hv : v ∈ K) :
    IsBestApprox K u v ↔ ‖u - v‖ = Metric.infDist u K
/-- AH Thm 3.3.12: the set of best approximations from a convex set is convex. -/
theorem convex_setOf_isBestApprox (hK : Convex ℝ K) (u : V) : Convex ℝ {v | IsBestApprox K u v}
/-- AH Thm 3.3.16 / Kress Thm 3.50: existence from finite-dimensional subspaces. -/
theorem exists_isBestApprox_of_finiteDimensional [CompleteSpace 𝕜] (K : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 K] (u : V) : ∃ v, IsBestApprox (K : Set V) u v
/-- AH Thm 3.3.15: existence from a closed subset of a finite-dimensional subspace. -/
theorem exists_isBestApprox_of_isClosed_of_finiteDimensional [CompleteSpace 𝕜] (hK : IsClosed K)
    (hne : K.Nonempty) (S : Submodule 𝕜 V) [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (u : V) :
    ∃ v, IsBestApprox K u v
/-- AH Thm 3.3.21: uniqueness in strictly convex spaces (Mathlib `StrictConvexSpace`). -/
theorem IsBestApprox.unique [StrictConvexSpace ℝ V] (hK : Convex ℝ K) (h₁ : IsBestApprox K u v₁)
    (h₂ : IsBestApprox K u v₂) : v₁ = v₂
/-- AH Lemma 3.4.1 (real inner product spaces, convex `K`; Mathlib
`norm_eq_iInf_iff_real_inner_le_zero`). -/
theorem isBestApprox_iff_inner_le_zero (hK : Convex ℝ K) (hv : v ∈ K) :
    IsBestApprox K u v ↔ ∀ w ∈ K, inner ℝ (u - v) (w - v) ≤ 0
/-- AH Prop 3.4.4: the metric projection onto a convex set is monotone and non-expansive. -/
theorem IsBestApprox.dist_le_dist (hK : Convex ℝ K) (h₁ : IsBestApprox K u₁ v₁)
    (h₂ : IsBestApprox K u₂ v₂) : 0 ≤ inner ℝ (v₁ - v₂) (u₁ - u₂) ∧ ‖v₁ - v₂‖ ≤ ‖u₁ - u₂‖
/-- AH Thm 3.4.6 / Kress Thm 3.51–3.52 (subspaces): the error is orthogonal; the best
approximation is `K.starProjection u` (Mathlib `Submodule.starProjection`). -/
theorem isBestApprox_iff_mem_orthogonal (K : Submodule 𝕜 V) (hv : v ∈ K) :
    IsBestApprox (K : Set V) u v ↔ u - v ∈ Kᗮ
theorem isBestApprox_starProjection (K : Submodule 𝕜 V) [K.HasOrthogonalProjection] (u : V) :
    IsBestApprox (K : Set V) u (K.starProjection u)
theorem IsBestApprox.eq_starProjection (K : Submodule 𝕜 V) [K.HasOrthogonalProjection]
    (h : IsBestApprox (K : Set V) u v) : v = K.starProjection u
/-- Kress Cor 3.53 (normal equations) for a spanning family `u i`. -/
theorem isBestApprox_sum_iff (u : ι → V) (a : ι → 𝕜) (w : V) :
    IsBestApprox (Submodule.span 𝕜 (Set.range u) : Set V) w (∑ i, a i • u i) ↔
      ∀ j, ∑ i, a i * inner 𝕜 (u j) (u i) = inner 𝕜 (u j) w
/-- Lebesgue lemma (AH (3.7.11)/(3.7.14)/(3.7.21) abstracted): for a bounded projection `P` onto
`S = range P`, `‖u − P u‖ ≤ (1 + ‖P‖) dist(u, S)`; pointwise form. -/
theorem norm_sub_apply_le_of_isIdempotentElem (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) :
    ‖u - P u‖ ≤ (1 + ‖P‖) * Metric.infDist u (LinearMap.range (P : V →ₗ[𝕜] V) : Set V)
theorem norm_sub_apply_le_of_isIdempotentElem_of_mem (P : V →L[𝕜] V) (hP : IsIdempotentElem P)
    (u : V) (hq : q ∈ LinearMap.range (P : V →ₗ[𝕜] V)) : ‖u - P u‖ ≤ (1 + ‖P‖) * ‖u - q‖
/-- AH Ex 3.6.7: a nonzero bounded projection has norm `≥ 1`. -/
theorem one_le_norm_of_isIdempotentElem (hP : IsIdempotentElem P) (h0 : P ≠ 0) : 1 ≤ ‖P‖
```
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

```lean
namespace SesqForm   -- (a : SesqForm 𝕜 V) (ℓ : V →L[𝕜] 𝕜)
/-- Lax–Milgram over `RCLike 𝕜` (AH Thm 8.3.4; Mathlib has the real case
`IsCoercive.continuousLinearEquivOfBilin`). -/
theorem laxMilgram (hc : 0 < c) (ha : a.IsCoerciveWith c) : ∃! u, ∀ v, a u v = ℓ v
theorem norm_le_of_forall_apply_eq (hc : 0 < c) (ha : a.IsCoerciveWith c) (hu : ∀ v, a u v = ℓ v) :
    ‖u‖ ≤ ‖ℓ‖ / c
/-- Lipschitz dependence on the data (AH (5.1.11) / (8.3.6)). -/
theorem norm_sub_le_of_forall_apply_eq (hc : 0 < c) (ha : a.IsCoerciveWith c)
    (h₁ : ∀ v, a u₁ v = ℓ₁ v) (h₂ : ∀ v, a u₂ v = ℓ₂ v) : ‖u₁ - u₂‖ ≤ ‖ℓ₁ - ℓ₂‖ / c
/-- The solution operator `ℓ ↦ u` is a continuous linear equivalence `V' ≃L V` (AH (8.3.5)). -/
theorem exists_solutionEquiv (hc : 0 < c) (ha : a.IsCoerciveWith c) :
    ∃ S : (V →L[𝕜] 𝕜) ≃L[𝕜] V, (∀ ℓ v, a (S ℓ) v = ℓ v) ∧ ‖(S : (V →L[𝕜] 𝕜) →L[𝕜] V)‖ ≤ 1 / c
/-- AH proof #1: the damped iteration `u ↦ u − θ (A u − f)` is a contraction with factor
`√(1 − 2θc + θ²‖a‖²)` for `0 < θ < 2c/‖a‖²` (via `contractingWith_damped`, 5.3.1). -/
theorem contractingWith_damped_toOperator (hc : 0 < c) (ha : a.IsCoerciveWith c) (ha0 : 0 < ‖a‖)
    (hθ : 0 < θ) (hθ' : θ < 2 * c / ‖a‖ ^ 2) :
    ContractingWith (Real.toNNReal (Real.sqrt (1 - 2 * θ * c + θ ^ 2 * ‖a‖ ^ 2)))
      (fun u => u - (θ : 𝕜) • (toOperator a u - rieszRep ℓ))
/-- AH Thm 8.3.3 (subspace case; `ha : a.IsHermitian`): `u ∈ K` solves `a u v = ℓ v` on `K` iff it
minimizes the energy on `K`. -/
theorem isMinOn_energy_iff (hc : 0 < c) (hcoer : a.IsCoerciveWith c) (K : Submodule 𝕜 V)
    (hu : u ∈ K) : IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, a u v = ℓ v
/-- AH (8.3.3), real scalars: on a convex `K` the energy minimizer is characterized by the
variational inequality `ℓ (v − u) ≤ a u (v − u)`; existence and uniqueness on nonempty closed
convex `K` (via Mathlib's `exists_norm_eq_iInf_of_complete_convex`). -/
theorem isMinOn_energy_iff_forall_le {a : SesqForm ℝ V} (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ)
    (hc : 0 < c) (hcoer : a.IsCoerciveWith c) (hK : Convex ℝ K) (hu : u ∈ K) :
    IsMinOn (a.energy ℓ) K u ↔ ∀ v ∈ K, ℓ (v - u) ≤ a u (v - u)
theorem existsUnique_isMinOn_energy {a : SesqForm ℝ V} (ha : a.IsHermitian) (ℓ : V →L[ℝ] ℝ)
    (hc : 0 < c) (hcoer : a.IsCoerciveWith c) (hK : Convex ℝ K) (hKc : IsClosed K)
    (hne : K.Nonempty) : ∃! u, u ∈ K ∧ IsMinOn (a.energy ℓ) K u
/-- Energy identity `E(v) − E(u) = ½ ‖v − u‖_a²` at the solution (AH Ex 8.3.5, Saad Prop 5.2). -/
theorem energy_sub_energy_eq (ha : a.IsHermitian) (hu : ∀ v, a u v = ℓ v) (v : V) :
    a.energy ℓ v - a.energy ℓ u = (1 / 2 : ℝ) * a.energyNorm (v - u) ^ 2
end SesqForm

namespace SesqForm₂   -- (a : SesqForm₂ 𝕜 U V) (ℓ : V →L[𝕜] 𝕜), U and V complete
/-- Babuška–Nečas (AH Thm 8.7.1): inf–sup + nondegeneracy ⇒ unique solvability, `‖u‖ ≤ ‖ℓ‖/α`. -/
theorem babuska_necas (hα : 0 < α) (hinf : a.InfSupWith α) (hnd : a.IsNondegenerate) :
    ∃! u, ∀ v, a u v = ℓ v
theorem norm_le_of_infSupWith (hα : 0 < α) (hinf : a.InfSupWith α) (hu : ∀ v, a u v = ℓ v) :
    ‖u‖ ≤ ‖ℓ‖ / α
/-- The inf–sup condition is necessary (Nečas): well-posedness with `‖u‖ ≤ C ‖ℓ‖` for all `ℓ`
gives `a.InfSupWith (1 / C)`. -/
theorem infSupWith_of_forall_exists (hC : 0 < C)
    (h : ∀ ℓ : V →L[𝕜] 𝕜, ∃ u, (∀ v, a u v = ℓ v) ∧ ‖u‖ ≤ C * ‖ℓ‖) : a.InfSupWith (1 / C)
end SesqForm₂

/-- Existence from a priori estimates (AH §8.2): a bounded-below operator has closed range; with
dense range it is bijective; the closed-operator version for `L : V →ₗ.[𝕜] W`. -/
theorem ContinuousLinearMap.isClosed_range_of_le_norm (L : V →L[𝕜] W) (hc : 0 < c)
    (h : ∀ v, c * ‖v‖ ≤ ‖L v‖) : IsClosed (LinearMap.range (L : V →ₗ[𝕜] W) : Set W)
theorem ContinuousLinearMap.bijective_of_le_norm_of_orthogonal_range_eq_bot (L : V →L[𝕜] W)
    (hc : 0 < c) (h : ∀ v, c * ‖v‖ ≤ ‖L v‖) (hdense : (LinearMap.range (L : V →ₗ[𝕜] W))ᗮ = ⊥) :
    Function.Bijective L
theorem LinearPMap.isClosed_range_of_isClosed_of_le_norm (L : V →ₗ.[𝕜] W) (hL : L.IsClosed)
    (hc : 0 < c) (h : ∀ v : L.domain, c * ‖(v : V)‖ ≤ ‖L v‖) :
    _root_.IsClosed (LinearMap.range L.toFun : Set W)
/-- AH (8.2.2): the a priori estimate as a bound on the inverse, `‖v‖ ≤ ‖L v‖/c`. -/
theorem ContinuousLinearMap.norm_le_of_le_norm (L : V →L[𝕜] W) (hc : 0 < c)
    (h : ∀ v, c * ‖v‖ ≤ ‖L v‖) (hv : L v = w) : ‖v‖ ≤ ‖w‖ / c
```
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

```lean
/-- Galerkin (variational) specification (AH (9.1.4)): `u ∈ K`, `a u v = ℓ v` for all `v ∈ K`. -/
def IsGalerkinSolution (a : SesqForm 𝕜 V) (ℓ : V →L[𝕜] 𝕜) (K : Submodule 𝕜 V) (u : V) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, a u v = ℓ v
/-- Petrov–Galerkin with trial `K ≤ U` and test `L ≤ V` (AH (9.2.5)). -/
def IsPetrovGalerkinSolution (a : SesqForm₂ 𝕜 U V) (ℓ : V →L[𝕜] 𝕜) (K : Submodule 𝕜 U)
    (L : Submodule 𝕜 V) (u : U) : Prop :=
  u ∈ K ∧ ∀ v ∈ L, a u v = ℓ v
theorem isGalerkinSolution_iff_isPetrovGalerkinSolution (a ℓ K u) :
    IsGalerkinSolution a ℓ K u ↔ IsPetrovGalerkinSolution (a : SesqForm₂ 𝕜 V V) ℓ K K u
namespace IsGalerkinSolution
/-- Bridge to the operator specification (2.4.1): Galerkin for the form is Galerkin for
`A = toOperator a`, `b = rieszRep ℓ`, `x₀ = 0`. -/
theorem iff_isGalerkin [CompleteSpace V] :
    IsGalerkinSolution a ℓ K u ↔
      IsGalerkin (SesqForm.toOperator a : V →ₗ[𝕜] V) (SesqForm.rieszRep ℓ) 0 K u
/-- Well-posedness on any complete subspace (Lax–Milgram on `K`). -/
theorem existsUnique (hc : 0 < c) (ha : a.IsCoerciveWith c) [CompleteSpace K] :
    ∃! u, IsGalerkinSolution a ℓ K u
/-- Galerkin orthogonality. -/
theorem apply_sub_eq_zero (hN : IsGalerkinSolution a ℓ K u) (hstar : ∀ v, a ustar v = ℓ v)
    (hv : v ∈ K) : a (ustar - u) v = 0
/-- Céa's lemma (AH Prop 9.1.3), pointwise and infimum forms. -/
theorem norm_sub_le (hc : 0 < c) (hM : a.IsBoundedWith M) (ha : a.IsCoerciveWith c)
    (hN : IsGalerkinSolution a ℓ K u) (hstar : ∀ v, a ustar v = ℓ v) (hv : v ∈ K) :
    ‖ustar - u‖ ≤ M / c * ‖ustar - v‖
theorem norm_sub_le_infDist … : ‖ustar - u‖ ≤ M / c * Metric.infDist ustar (K : Set V)
/-- Hermitian case (AH (9.1.7)–(9.1.8)): energy-norm best approximation, hence `√(M/c)`. -/
theorem energyNorm_sub_le (ha : a.IsHermitian) (hN : IsGalerkinSolution a ℓ K u)
    (hstar : ∀ v, a ustar v = ℓ v) (hv : v ∈ K) : a.energyNorm (ustar - u) ≤ a.energyNorm (ustar - v)
theorem norm_sub_le_sqrt (hc : 0 < c) (hM : a.IsBoundedWith M) (ha : a.IsCoerciveWith c)
    (hh : a.IsHermitian) (hN : IsGalerkinSolution a ℓ K u) (hstar : ∀ v, a ustar v = ℓ v)
    (hv : v ∈ K) : ‖ustar - u‖ ≤ Real.sqrt (M / c) * ‖ustar - v‖
/-- Stiffness-matrix form (AH (9.1.5)) for a basis `φ` of `K`. -/
theorem iff_mulVec (φ : Module.Basis ι 𝕜 K) (ξ : ι → 𝕜) :
    IsGalerkinSolution a ℓ K (∑ j, ξ j • (φ j : V)) ↔
      (Matrix.of fun i j => a (φ j : V) (φ i)).mulVec ξ = fun i => ℓ (φ i)
end IsGalerkinSolution
/-- Distances to a monotone family of subspaces with dense union tend to zero (shared by
AH Cor 9.1.4, Cor 9.2.3, Kress §11). -/
theorem tendsto_infDist_of_monotone_dense (hmono : Monotone K) (hdense : Dense (⋃ n, (K n : Set V)))
    (u : V) : Filter.Tendsto (fun n => Metric.infDist u (K n : Set V)) Filter.atTop (nhds 0)
/-- AH Cor 9.1.4: Galerkin solutions on a monotone dense family converge to the solution. -/
theorem IsGalerkinSolution.tendsto (hc : 0 < c) (hM : a.IsBoundedWith M) (ha : a.IsCoerciveWith c)
    (hmono : Monotone K) (hdense : Dense (⋃ n, (K n : Set V)))
    (hN : ∀ n, IsGalerkinSolution a ℓ (K n) (uN n)) (hstar : ∀ v, a ustar v = ℓ v) :
    Filter.Tendsto uN Filter.atTop (nhds ustar)
namespace IsPetrovGalerkinSolution
/-- Discrete inf–sup condition (AH (9.2.6)), with the restricted functional's norm. -/
def DiscreteInfSup (a : SesqForm₂ 𝕜 U V) (K : Submodule 𝕜 U) (L : Submodule 𝕜 V) (α : ℝ) : Prop :=
  ∀ w ∈ K, α * ‖w‖ ≤ ‖(a w).comp L.subtypeL‖
/-- Babuška (AH Thm 9.2.1): `dim K = dim L` + discrete inf–sup ⇒ unique solvability and
`‖u − u_N‖ ≤ (1 + M/α) inf_{w ∈ K} ‖u − w‖`; Cor 9.2.3 convergence on monotone dense families. -/
theorem existsUnique [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) (hα : 0 < α) (hinf : DiscreteInfSup a K L α) :
    ∃! u, IsPetrovGalerkinSolution a ℓ K L u
theorem norm_sub_le [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 L]
    (hdim : Module.finrank 𝕜 K = Module.finrank 𝕜 L) (hα : 0 < α)
    (hM : ∀ w v, ‖a w v‖ ≤ M * ‖w‖ * ‖v‖) (hinf : DiscreteInfSup a K L α)
    (hN : IsPetrovGalerkinSolution a ℓ K L u) (hstar : ∀ v, a ustar v = ℓ v) (hw : w ∈ K) :
    ‖ustar - u‖ ≤ (1 + M / α) * ‖ustar - w‖
theorem tendsto … (hinf : ∀ n, DiscreteInfSup a (K n) (L n) α) (hmono : Monotone K)
    (hdense : Dense (⋃ n, (K n : Set U))) … : Filter.Tendsto uN Filter.atTop (nhds ustar)
end IsPetrovGalerkinSolution
/-- Generalized Galerkin (AH §9.3) on one abstract normed space `W` (the book's `V + V_N` with
`‖·‖_N`); the Hilbert space `V` and the original problem never enter. -/
def IsGeneralizedGalerkinSolution (aN : W →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (ℓN : W →ₗ[𝕜] 𝕜) (K : Submodule 𝕜 W)
    (uN : W) : Prop :=
  uN ∈ K ∧ ∀ v ∈ K, aN uN v = ℓN v
/-- Strang's first lemma (AH Thm 9.3.1) in pointwise form with an explicit consistency bound `δ`:
`‖u − u_N‖ ≤ (1 + M/c) ‖u − v‖ + δ/c`. -/
theorem strang_first (hc : 0 < c) (hM : ∀ w, ∀ v ∈ K, ‖aN w v‖ ≤ M * ‖w‖ * ‖v‖)
    (hcoer : ∀ v ∈ K, c * ‖v‖ ^ 2 ≤ RCLike.re (aN v v)) (hN : IsGeneralizedGalerkinSolution aN ℓN K uN)
    (u : W) (hδ : ∀ w ∈ K, ‖aN u w - ℓN w‖ ≤ δ * ‖w‖) (hv : v ∈ K) :
    ‖u - uN‖ ≤ (1 + M / c) * ‖u - v‖ + δ / c
theorem existsUnique_isGeneralizedGalerkinSolution (aN ℓN K) [FiniteDimensional 𝕜 K] (hc : 0 < c)
    (hcoer : ∀ v ∈ K, c * ‖v‖ ^ 2 ≤ RCLike.re (aN v v)) :
    ∃! uN, IsGeneralizedGalerkinSolution aN ℓN K uN
```
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

```lean
/-- Linear rate (AH (5.1.6)): `dist (f^[n+1] x) x* ≤ K dist (f^[n] x) x*`. -/
theorem ContractingWith.dist_iterate_succ_fixedPoint_le [Nonempty α] [CompleteSpace α]
    (hf : ContractingWith K f) (x : α) (n : ℕ) :
    dist (f^[n + 1] x) (fixedPoint f hf) ≤ K * dist (f^[n] x) (fixedPoint f hf)
/-- AH Thm 5.1.3 / Kress Thm 3.45 on a closed subset mapped into itself: existence, uniqueness
and the a priori bound (5.1.4). -/
theorem exists_unique_fixedPoint_of_mapsTo [CompleteSpace α] (hs : IsClosed s) (hne : s.Nonempty)
    (hmaps : Set.MapsTo f s s) (hK0 : 0 ≤ K) (hK : K < 1)
    (hf : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) : ∃! x, x ∈ s ∧ f x = x
theorem dist_iterate_le_of_mapsTo [CompleteSpace α] (hs : IsClosed s) (hmaps : Set.MapsTo f s s)
    (hK0 : 0 ≤ K) (hK : K < 1) (hf : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y)
    (hx' : x' ∈ s) (hfix : f x' = x') (hx₀ : x₀ ∈ s) (n : ℕ) :
    dist (f^[n] x₀) x' ≤ K ^ n / (1 - K) * dist (f x₀) x₀
/-- AH Ex 5.1.2 / Kress Problem 3.17: continuous `T` with `T^[m]` a contraction. -/
theorem exists_unique_fixedPoint_of_iterate_contractingWith [CompleteSpace α] (hT : Continuous T)
    (hm : 0 < m) (hK : ContractingWith K T^[m]) : ∃! x, T x = x
theorem tendsto_iterate_of_iterate_contractingWith [CompleteSpace α] (hT : Continuous T)
    (hm : 0 < m) (hK : ContractingWith K T^[m]) (x : α) :
    ∃ x', T x' = x' ∧ Tendsto (fun n => T^[n] x) atTop (𝓝 x')
/-- Kress Thm 6.8 / AH Thm 5.2.1: `sup ‖T'‖ ≤ q` on a convex set ⇒ `q`-Lipschitz there (Mathlib
`Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`). -/
theorem lipschitzOnWith_of_hasFDerivWithinAt (hs : Convex ℝ s)
    (hT : ∀ x ∈ s, HasFDerivWithinAt T (T' x) s x) (hT' : ∀ x ∈ s, ‖T' x‖₊ ≤ q) :
    LipschitzOnWith q T s
/-- Zarantonello / AH Thm 5.1.4: strongly monotone + Lipschitz on a Hilbert space ⇒ bijective;
the damped iteration `x ↦ x − θ (T x − b)` contracts with factor `√(1 − 2θc + θ²L²)` for
`0 < θ < 2c/L²`; Lipschitz dependence `‖x₁ − x₂‖ ≤ ‖b₁ − b₂‖/c` (AH (5.1.11)). -/
theorem zarantonello [CompleteSpace E] {T : E → E} {c L : ℝ} (hc : 0 < c)
    (hmono : ∀ x y, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x - T y) (x - y)))
    (hlip : LipschitzWith (Real.toNNReal L) T) (b : E) : ∃! x, T x = b
theorem contractingWith_damped [CompleteSpace E] (hc : 0 < c) (hL : 0 < L) (hmono : …)
    (hlip : LipschitzWith (Real.toNNReal L) T) (b : E) (hθ : 0 < θ) (hθ' : θ < 2 * c / L ^ 2) :
    ContractingWith (Real.toNNReal (Real.sqrt (1 - 2 * θ * c + θ ^ 2 * L ^ 2)))
      (fun x => x - (θ : 𝕜) • (T x - b))
theorem norm_sub_le_of_strongly_monotone [CompleteSpace E] (hc : 0 < c) (hmono : …)
    (h₁ : T x₁ = b₁) (h₂ : T x₂ = b₂) : ‖x₁ - x₂‖ ≤ ‖b₁ - b₂‖ / c
```
The linear instance (the stationary iteration with `‖G‖ < 1`) is stated in 2.3.1. Bielecki
weighted norms (AH Thm 5.2.3, Volterra) and generalized Picard–Lindelöf (Thm 5.2.4) are AH surface
/ phase 3 (Mathlib has `IsPicardLindelof` in finite dimension).

#### 5.3.2 `Nonlinear/Newton.lean` (L2, Banach)
Serves AH Thm 5.4.1–5.4.2, Kress Thm 6.14 (semi-local Newton–Kantorovich with `αβγ < ½`, `r = 2α`),
Thm 6.20 (quadratic rate `(βγ/2)‖x* − x_ν‖²`), Cor 6.15 (local convergence for `C²`), Thm 6.21
(simplified Newton), Saad §9 (Newton–Krylov mention). Stated over a `NontriviallyNormedField 𝕜`
with the derivative supplied as a function `F' : E → E →L[𝕜] F` and inverted by
`ContinuousLinearMap.inverse` (`0` when `F' x` is not invertible).

```lean
namespace Newton
noncomputable def step (Fn : E → F) (F' : E → E →L[𝕜] F) (x : E) : E := x - (F' x).inverse (Fn x)
noncomputable def iterate (Fn : E → F) (F' : E → E →L[𝕜] F) (x₀ : E) (k : ℕ) : E :=
  (step Fn F')^[k] x₀
theorem iterate_succ (Fn F' x₀ k) : iterate Fn F' x₀ (k + 1) = step Fn F' (iterate Fn F' x₀ k)
theorem step_eq_self_of_eq_zero (Fn F') (hx : Fn x = 0) : step Fn F' x = x
-- [CompleteSpace E] [CompleteSpace F] from here on
/-- Local quadratic convergence (AH Thm 5.4.1, Kress Thm 6.20): `F'(x*)` invertible (inverse `e`)
and `F'` `L`-Lipschitz on a ball ⇒ `‖step x − x*‖ ≤ C ‖x − x*‖²` on a smaller ball. -/
theorem exists_ball_norm_step_sub_le (hstar : Fn xstar = 0) (e : E ≃L[𝕜] F)
    (he : (e : E →L[𝕜] F) = F' xstar) (hr : 0 < r) (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ δ > 0, ∃ C : ℝ, ∀ x ∈ Metric.ball xstar δ, ‖step Fn F' x - xstar‖ ≤ C * ‖x - xstar‖ ^ 2
/-- The explicit constant `L ‖(F' x)⁻¹‖ / 2` whenever `F' x` is invertible. -/
theorem norm_step_sub_le (hstar : Fn xstar = 0) (hF : …) (hL : …) (hx : x ∈ Metric.ball xstar r)
    (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x) :
    ‖step Fn F' x - xstar‖ ≤ L * ‖(e.symm : F →L[𝕜] E)‖ / 2 * ‖x - xstar‖ ^ 2
/-- Local convergence: from every `x₀` in a small ball the Newton iterates converge to `x*`. -/
theorem tendsto_iterate (hstar : Fn xstar = 0) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' xstar)
    (hr : 0 < r) (hF : …) (hL : …) :
    ∃ δ > 0, ∀ x₀ ∈ Metric.ball xstar δ, Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar)
/-- Newton–Kantorovich (Kress Thm 6.14's variant, AH Thm 5.4.2): `‖(F' x₀)⁻¹‖ ≤ β`,
`‖(F' x₀)⁻¹ F x₀‖ ≤ η`, `F'` `L`-Lipschitz on `closedBall x₀ r`, `h := βLη ≤ ½` and
`t* := (1 − √(1 − 2h))/(βL) ≤ r` ⇒ the iterates stay in the ball, converge to a root `x*` with
`‖x* − x₀‖ ≤ t*`, and `‖x_k − x*‖ ≤ (2h)^{2^k} η/(2^k h)` when `h > 0`. -/
theorem kantorovich (hβ : 0 < β) (hL : 0 < L) (hη : 0 ≤ η) (e : E ≃L[𝕜] F)
    (he : (e : E →L[𝕜] F) = F' x₀) (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r, ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hh : β * L * η ≤ 1 / 2) (hr : (1 - Real.sqrt (1 - 2 * (β * L * η))) / (β * L) ≤ r) :
    ∃ xstar ∈ Metric.closedBall x₀ ((1 - Real.sqrt (1 - 2 * (β * L * η))) / (β * L)),
      Fn xstar = 0 ∧ Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar) ∧
      (∀ k, iterate Fn F' x₀ k ∈ Metric.closedBall x₀ r) ∧
      (0 < β * L * η → ∀ k, ‖iterate Fn F' x₀ k - xstar‖ ≤
        (2 * (β * L * η)) ^ (2 ^ k) * η / (2 ^ k * (β * L * η)))
end Newton
```
Phase 2: AH's stronger Kantorovich statement (uniqueness in `B̄(x₀, t**)`, error
`(1 − √(1−2h))^{2ⁿ}/(2ⁿ a L)`) and the modified (chord) Newton method with frozen derivative
(linear convergence via 5.3.1, AH Ex 5.4.5).

Difficult proof: the quadratic estimate uses the integral form of the mean value theorem
`F(x*) − F(x) − F'(x)(x* − x) = ∫₀¹ (F'(x + t(x* − x)) − F'(x)) (x* − x) dt`; in Mathlib use the
inequality form `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` (bound of
`‖F y − F x − F' x (y − x)‖` by `sup ‖F' z − F' x‖ ‖y − x‖`, which is `≤ L‖y − x‖²`) to avoid
Bochner integrals; invertibility of `F' x` near `x*` with a uniform bound comes from 2.1.1.
Kantorovich needs the majorant-sequence argument (`t_{n+1} = t_n − p(t_n)/p'(t_n)` for the scalar
quadratic `p`); Ortega–Rheinboldt §12.6 / Deuflhard's affine-invariant version are the references.

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
| `Analysis/NormedRing/{Inverse,CondNumber}` | 2.1.1–2.1.2 | 250 | ★ | — |
| `Analysis/SpectralRadius` | 2.1.3 | 200 | ★★ (ENNReal bookkeeping) | — |
| `InnerProductSpace/{Coercive,Energy,Compression,ObliqueProjection,GramSchmidt}` | 2.1.4–2.1.7, 2.1.13 | 700 | ★★ (`WithEnergy` instance) | — |
| `Polynomial/ChebyshevMinimax` | 2.1.9 | 300 | ★★ | — |
| `Matrix/{Hessenberg,Complexify,ToEuclideanLin}` | 2.1.10–2.1.11, 2.1.14 | 400 | ★★ | — |
| `LinearSolve/Perturbation` | 2.2 | 200 | ★ | 2.1.1–2.1.2 |
| `LinearSolve/Stationary/{Basic,Splitting,DiagDominant}` | 2.3.1–2.3.3 | 450 | ★★ (GS convergence) | 2.1.3, 2.1.11 |
| `LinearSolve/Projection/{Basic,Optimality,OneDimensional}` | 2.4.1–2.4.3 | 600 | ★★ (Kantorovich) | 2.1.4–2.1.7 |
| `Krylov/{Subspace,Arnoldi,Lanczos}` | 2.1.8, 3.1–3.3 | 700 | ★★★ (Arnoldi = Gram–Schmidt) | 2.1.13 |
| `Krylov/{Iterate,Hessenberg,Relations}` | 3.4–3.6 | 800 | ★★ (Givens bookkeeping) | 2.1.10, 2.4 |
| `Krylov/{CG,CR}` | 3.7–3.8 | 600 | ★★ (invariant induction) | 3.4 |
| `Krylov/Convergence/{Polynomial,CG}` | 3.9–3.10 | 350 | ★★ | 2.1.6, 2.1.9, 3.4 |
| `Krylov/Monotonicity` | 3.11 | 350 | ★★ (finite termination) | 3.7–3.8 |
| `Eigen/Perturbation` | 4.1 | 250 | ★★ | 2.1.2, 2.1.4 |
| `Approximation/BestApprox` | 5.1.1 | 200 | ★ | — |
| `Variational/{Forms,LaxMilgram,Galerkin}` | 5.2 | 600 | ★★ (complex Lax–Milgram) | 2.1.4–2.1.5, 2.4.1 |
| `Nonlinear/{FixedPoint,Newton}` | 5.3 | 400 | ★★ (Kantorovich majorants) | 2.1.1, 2.3.1 |
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
| D15 | Newton local quadratic convergence | 5.3.2 | `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` for the Taylor remainder, 2.1.1 for `(F' x)⁻¹`; AH Thm 5.4.1; Ortega–Rheinboldt 10.2.2 |
| D16 | Courant–Fischer | 4.2 | dimension counting on `S ⊓ span{u_k..u_n}`; Horn–Johnson Thm 4.2.6 |
| D17 | `WithEnergy` inner-product instance and its completeness | 2.1.5 | `InnerProductSpace.Core` on a type synonym, following Mathlib's `Matrix.toInnerProductSpace`: the plain `AddCommGroup`/`Module` instances are local to the defining section, only the core-derived normed instances are global, `WithEnergy.equiv` is defined afterwards with `rfl` fields; norm equivalence and `continuous_equiv` need `A : E →L[𝕜] E` |
| D18 | Subspace iteration in Saad-eig's generality (Thm 5.2) | 4.3 | spectral projector onto the dominant generalized eigenspaces + Gelfand on the complement; gap between subspaces needs a `Submodule` gap/angle API (not in Mathlib). Kress Lemma 7.18 (diagonalizable) as a warm-up |
| D19 | Householder–John / Ostrowski–Reich in operator form | 2.3.5 | Rayleigh-quotient identity for an eigenpair of `M⁻¹N` (Kress Thm 4.12 proof) generalizes verbatim with `M + Mᴴ − A` coercive; Saad Thm 4.10 |

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

## 11. Module map

The backbone modules under `Numlib/`, all imported by `Numlib.lean`, and the plan items they
implement. Modules in `Analysis/`, `InnerProductSpace/`, `Matrix/`, `Polynomial/` are the
upstreaming candidates of 2.1 (1.5).

| Module | Plan items |
|---|---|
| `Analysis/NormedRing/Inverse`, `Analysis/NormedRing/CondNumber`, `Analysis/SpectralRadius` | 2.1.1–2.1.3 |
| `InnerProductSpace/Coercive`, `Energy`, `Compression`, `ObliqueProjection`, `GramSchmidt` | 2.1.4–2.1.7, 2.1.13 (`IsSymmetricBoundedBy`, `WithEnergy`, `compressionBy`, projectors from bases, Kato's lemma, flag uniqueness) |
| `Polynomial/ChebyshevMinimax` | 2.1.9 |
| `Matrix/Hessenberg`, `Matrix/Complexify`, `Matrix/ToEuclideanLin` | 2.1.10–2.1.11, 2.1.14 |
| `LinearSolve/Perturbation` | 2.2 |
| `LinearSolve/Stationary/Basic`, `Splitting`, `DiagDominant` | 2.3.1–2.3.3 |
| `LinearSolve/Projection/Basic`, `Optimality`, `OneDimensional` | 2.4.1–2.4.3 |
| `Krylov/Subspace`, `Arnoldi`, `Lanczos`, `Iterate`, `Hessenberg`, `Relations`, `CG`, `CR`, `Convergence/Polynomial`, `Convergence/CG`, `Monotonicity` | 3.1–3.11 (the polynomial glue 2.1.8 lives in `Subspace` and `Iterate`) |
| `Eigen/Perturbation` | 4.1 |
| `Approximation/BestApprox` | 5.1.1 |
| `Variational/Forms`, `LaxMilgram`, `Galerkin` | 5.2.1–5.2.3 |
| `Nonlinear/FixedPoint`, `Newton` | 5.3.1–5.3.2 |

The surface libraries `SaadSparse`, `FongSaunders`, `AtkinsonHan` live under `Surface/` (§8) and
import `Numlib` only.
