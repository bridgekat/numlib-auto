# Backbone plan v1

This is the master plan for the `Numlib` backbone, written according to the process in
[README.md](../README.md). It covers the whole corpus in `../numlib-books`, proposes a spanning
tree of general definitions and theorems, places every item in the module hierarchy, gives Lean
statements for the key items (all statements marked ✓ were type-checked against Mathlib
`v4.34.0-rc2` with `sorry` bodies; others are unchecked sketches), describes the difficult proofs,
and lists what is left to the surface layer. The phase-1 Lean skeleton (`Numlib/`, compiling
with `sorry`) is the full-signature sub-plan for every phase-1 section; sub-plans for later
phases (e.g. `plans/floating-point.md`) are split off when their formalization starts.

The analyses that this plan was distilled from (per-book theorem inventories produced by
sub-agents from low-quality OCR text) have been removed; the three selected books were
re-converted with better OCR and the chapter-level surface plans in `plans/surface/` were
written from the new text.
The prototype files that backed the ✓ marks in v0 were superseded by the skeleton and removed.

---

## 0. Corpus and the first formalization batch

### 0.1 The eight sources and what each contributes

| Source | Core content | Structure it uses | Role in the backbone |
|---|---|---|---|
| Saad, *Iterative Methods for Sparse Linear Systems* (2003) | Projection methods (Petrov–Galerkin), Krylov methods (Arnoldi, FOM, GMRES, Lanczos, CG, CR, GCR), convergence via Chebyshev polynomials, stationary methods (Jacobi/GS/SOR), regular splittings, preconditioning | Inner product spaces + a linear operator for Ch. 5–6 and 9; matrix entries, nonnegativity and graphs for Ch. 4; Jordan form for asymptotics | **The spine.** Almost all of Ch. 5–6 generalizes verbatim to bounded operators on Hilbert spaces with finite-dimensional search spaces. |
| Fong & Saunders, *CG versus MINRES* (2012) | Minimization properties of CG/CR/MINRES; monotonicity of `‖x_k‖`, `‖x−x_k‖`, `‖x−x_k‖_A`, `‖r_k‖`, backward errors; stopping rules | Inner product + self-adjoint positive `A`; finite termination for the sign arguments | Integration test for the abstract Galerkin / minimal-residual specifications and the CG/CR recurrences. |
| Atkinson & Han, *Theoretical Numerical Analysis* (2009) | Neumann series and perturbation theorem with explicit bounds, uniform boundedness ⇒ quadrature convergence, best approximation, projections, Lebesgue lemma, Banach fixed point with error bounds, Newton/Kantorovich, CG for operator equations, Lax–Milgram, Galerkin/Céa/Petrov–Galerkin/inf–sup, Lax equivalence, Sobolev/FEM/integral equations | Banach and Hilbert spaces throughout | **The generality guide.** Its "functional analysis framework" is exactly the backbone philosophy; it fixes the natural level of generality of most items. |
| Choi, *Iterative methods for singular linear equations and least-squares problems* (2006) | Lanczos process, CG/SYMMLQ/MINRES as subproblems on `T̄_k`, MINRES on singular/incompatible systems, MINRES-QLP, norm/condition estimates, preconditioning | Inner product + self-adjoint `A` (any rank); finite-dimensional pseudoinverse; reflector algebra | Extends the Krylov spine to singular systems and minimum-norm solutions; QR/QLP implementation layer. |
| Meurant & Strakoš, *Lanczos and CG in finite precision* (2007) | Lanczos ↔ orthogonal polynomials ↔ Gauss quadrature; CG error identities (HS 6:1, 6:3), `A`-norm error as Gauss remainder; Paige's finite-precision theory; Greenbaum's backward-like analysis | Spectral measure of a self-adjoint operator; unreduced tridiagonal matrices; floating-point model for §4–5 | Polynomial/measure layer of the Krylov spine (exact arithmetic); template for the floating-point layer. |
| Saad, *Numerical Methods for Large Eigenvalue Problems* (2011) | Projectors, resolvent, Bauer–Fike, residual bounds, Gershgorin, Courant–Fischer, power/inverse/subspace iteration, Rayleigh–Ritz, Arnoldi/Lanczos eigenvalue bounds (Kaniel–Paige–Saad), Chebyshev filtering | Shares Ch. 1 and Ch. 6 (Krylov, Arnoldi, Lanczos) with the sparse-systems book | Second consumer of the Krylov spine; drives the eigenvalue layer. |
| Kress, *Numerical Analysis* (1998) | Gaussian elimination/QR, Banach fixed point, Jacobi/GS/SOR (incl. Young's theory), condition numbers, SVD, Tikhonov, Newton, eigenvalue estimates (Gershgorin, Bauer–Fike), Jacobi/QR eigenvalue algorithms, interpolation, quadrature, IVPs/BVPs, integral equations | Mixture of finite-dimensional and Banach-space statements | Cross-check for the stationary, perturbation and approximation layers; sources of the interpolation/quadrature/ODE branches. |
| Higham, *Accuracy and Stability of Numerical Algorithms* (2002) | Standard model of floating point, `γ_n` calculus, backward error of dot products, triangular solves, LU, Cholesky, QR; perturbation theory (Rigal–Gaches, Oettli–Prager, Skeel); stationary iterations in finite precision; matrix powers | Real numbers with relative perturbations `δ`; entrywise matrix order; normwise bounds derived from componentwise ones | Reserved floating-point layer; its exact-arithmetic parts (Ch. 6, 7, 18) join the perturbation layer now. |

### 0.2 Selected for formalization now (recommendation)

1. **Saad, *Iterative Methods for Sparse Linear Systems*** — §1.11–1.13, Ch. 4 (§4.1–4.2), Ch. 5, Ch. 6 in full; Ch. 7–9 as phase 2. It is the densest source of the spine and shares its Ch. 1 and Ch. 6 with the eigenvalue book, so it maximizes reuse.
2. **Fong & Saunders, *CG versus MINRES*** — complete. Short, theorem-dense, and it exercises exactly the README's motivating example ("abstract MINRES as iterative argmins of residuals" with several implementations satisfying it).
3. **Atkinson & Han, *Theoretical Numerical Analysis*** — Ch. 2 (§2.3–2.5), §3.3–3.7, Ch. 5 (§5.1–5.4, 5.6), §8.2–8.3, 8.7, Ch. 9 now; Ch. 6.2 (Lax equivalence), 11–12 (abstract parts) later; Ch. 4, 7, 10, 13–14 (Fourier, Sobolev, FEM, BIE) are out of scope until Mathlib has Sobolev spaces. It supplies the Banach/Hilbert-space forms that the backbone should be stated in, and its CG chapters (5.6, 9.4) meet Saad's CG in the middle.

Alternative third choice: Choi's thesis, if the user prefers a Krylov-only sprint. It fits the same spine (phase 2–3 items below: singular systems, MINRES-QLP, norm estimates) but is more implementation-heavy and less theorem-dense than Atkinson–Han, and would leave the Banach-space layer untested.

### 0.3 Definition of done for phase 1

Backbone modules listed as phase 1 in §7 compiled without `sorry`; surface libraries `SaadSparse`, `FongSaunders`, `AtkinsonHan` with chapter files for the ranges above, each theorem proved by specializing the backbone (equivalence lemmas for book-specific definitions); reviews per README §"Reviewing a formalization".

---

> **Status (v1, 2026-09-04).** The phase-1 backbone skeleton is written and compiles with
> `sorry` (37 modules, `Numlib.lean`); proof filling is paused. The adversarial review (v0,
> issues R1–R20, addressed and removed) and the surface plans (`plans/surface/`) are folded
> into §12, which overrides §1–§11 wherever they differ. A "✓" in §2–§6 means "elaborates",
> not "proved" (R5).

## 1. Design principles and conventions

### 1.1 The generality ladder

Every item is placed on the lowest rung (most general) at which its proof works; more concrete rungs
instantiate it. This is the "interfaces over implementations" rule from the README.

| Rung | Setting | Typical content |
|---|---|---|
| L0 algebraic | `Module.End R M`, `R` a commutative ring or field | Krylov subspaces, polynomial evaluation `p(A)v`, invariance, grade |
| L1 inner product | `[RCLike 𝕜] [InnerProductSpace 𝕜 E]`, **no completeness**, `A : E →ₗ[𝕜] E` (bounded when needed) | Petrov–Galerkin specs, minimal residual / Galerkin optimality, Arnoldi/Lanczos relations, CG/CR recurrences and invariants, FOM–GMRES relations, monotonicity |
| L2 Banach/Hilbert | `[CompleteSpace E]`, `E →L[𝕜] E`, normed rings/algebras | Neumann series, perturbation of inverses, condition numbers, spectral radius and stationary iterations, Lax–Milgram, Céa, Banach fixed point, Newton |
| L3 finite-dimensional | `[FiniteDimensional 𝕜 E]` | grade < ∞, termination, `dim 𝒦_m = min(m, grade)`, spectral theorem for symmetric operators (eigenvalue bounds ⇒ Chebyshev bounds), Bauer–Fike, Courant–Fischer, Faber–Manteuffel |
| L4 matrices | `Matrix n n 𝕜` with a basis / an order on `n` | splittings `A = D − E − F`, Jacobi/GS/SOR, diagonal dominance, Gershgorin, M-matrices, Hessenberg/tridiagonal/Givens, Property A |

Rules of thumb that came out of the analyses:

* Krylov and projection theory needs only L1: the search spaces are finite-dimensional, so
  orthogonal projections exist (`Submodule.HasOrthogonalProjection` holds for finite-dimensional
  submodules) without completeness of `E`. State those results for `A : E →ₗ[𝕜] E`; continuity is
  irrelevant to the algebra and only enters convergence bounds.
* "Positive definite" means two different things in the corpus. Saad's real "positive definite"
  (`(Au,u) > 0`, no symmetry) and Atkinson–Han's "strongly monotone/V-elliptic" are both
  **coercivity** `re ⟪A x, x⟫ ≥ c ‖x‖²`; SPD/HPD is coercive + symmetric. In finite dimension
  coercive ⇔ positive definite; in infinite dimension coercivity is the right hypothesis (it is what
  makes `A⁻¹` bounded and the energy norm equivalent to the norm). The backbone uses
  `LinearMap.IsCoercive` and `LinearMap.IsSymmetricCoercive` (§2.1.4) and proves the finite-dimensional
  equivalences with `Matrix.PosDef` and `LinearMap.IsPositive`.
* Real vs complex: state over `RCLike 𝕜` with `RCLike.re` where the books take real parts; every
  proof in the corpus goes through this way (Saad §6.5.9, Choi §1.2, Fong–Saunders with `Re`).
  Spectral radius and "powers tend to zero" are stated for complex Banach algebras (Gelfand's
  formula is only in Mathlib over ℂ); real matrices go through `Matrix.map Complex.ofReal`.
* Finite termination (`x_ℓ = x`) is used by the Fong–Saunders sign arguments and by Choi's rank
  lemmas; those are stated at L3. Everything that only uses nesting of subspaces and orthogonal
  projections is stated at L1.

### 1.2 Specifications versus implementations

Following the README, the *canonical* objects are Prop-valued specifications quantified over an
arbitrary iterate or sequence of iterates, e.g. `IsMinRes A b x₀ K x` ("`x ∈ x₀ + K` minimizes
`‖b − A x‖`"). Theorems about "MINRES" are theorems about any `x : ℕ → E` with
`∀ k, Krylov.IsMinResIterate A b x₀ k (x k)`; MINRES, CR, GMRES, MINRES-QLP (on nonsingular
systems) all satisfy it. This has three benefits found in the analyses: the Lanczos/Givens
machinery becomes a *transport* layer (Choi's "same method, different implementations"),
Fong–Saunders' transfer "CR results ⇒ MINRES results" becomes literally a specialization, and the
surface only needs to prove "my book's algorithm satisfies the spec".

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
| `LinearMap.IsCoercive A` | `∃ c > 0, ∀ x, c‖x‖² ≤ re⟪A x, x⟫` | Saad PD, AH strongly monotone; MR iteration, GMRES(m), Galerkin well-posedness |
| `LinearMap.IsSymmetricCoercive A` | `A.IsSymmetric ∧ A.IsCoercive` | SPD/HPD: energy norm, CG, SD, Kantorovich, Chebyshev bound, Fong–Saunders |
| `WithEnergy A hA` | type synonym of `E` carrying the inner product `⟪A x, y⟫` | A-orthogonal projections (Saad Prop 5.5), Galerkin = orthogonal projection in the energy norm, Céa with constant 1 |
| `Matrix.Splitting A` | `M N` with `A = M − N`, `IsUnit M` | Jacobi/GS/SOR/SSOR/Richardson, regular splittings |
| `Fl.RoundingModel K` | abstract arithmetic with relative error `u` | floating-point layer (reserved) |

Mathlib bundles reused as is: `LinearMap.IsSymmetric`, `IsSelfAdjoint`, `LinearMap.IsPositive`,
`Matrix.PosDef`, `Matrix.IsHermitian`, `ContractingWith`, `IsCoercive` (real bilinear forms),
`Submodule.HasOrthogonalProjection`, `IsCompactOperator`, `ContinuousLinearMap.IsFredholm`.

### 1.4 Naming and namespaces

* No global `Numlib` namespace. Mathlib-style extensions use the Mathlib namespace of the type they
  extend (`LinearMap.IsCoercive`, `Matrix.IsUpperHessenberg`, `NormedRing.condNumber`), so that dot
  notation and future upstreaming work. Numerical-analysis-specific theories use short topical
  namespaces: `Krylov`, `Arnoldi`, `Lanczos`, `CG`, `CR`, `Stationary`, `Projection`, `Galerkin`,
  `Fl`.
* Specifications are `Is…` structures (`IsPetrovGalerkin`, `IsGalerkin`, `IsMinRes`, `IsMinError`,
  `Krylov.IsMinResIterate`, `Krylov.IsGalerkinIterate`).
* Scoped notation: `𝒦[A, v] m` for `Krylov.subspace A v m`; `⟪x, y⟫_[A]` / `‖x‖_[A]` for the
  energy inner product and norm; `κ a` for the condition number.
* Book numbering appears only in docstrings and in the surface (`SaadSparse.Ch06.prop_6_5`), never
  in backbone names.
* One theorem per statement, `Mathlib` naming conventions (`norm_residual_le`,
  `spectralRadius_lt_one_iff_tendsto_pow`).

### 1.5 Repository layout

```
Numlib.lean                     -- imports all backbone modules
Numlib/                         -- backbone (this plan, §2–§6)
  Analysis/…                    -- upstreaming candidates: spectral radius, Neumann series, κ
  InnerProductSpace/…           -- upstreaming candidates: coercivity, energy norm, compression,
                                --   Gram–Schmidt, oblique projections
  Matrix/…                      -- upstreaming candidates: Hessenberg, complexify, toEuclideanLin
  Polynomial/…                  -- upstreaming candidates: Chebyshev min–max
  LinearSolve/…                 -- perturbation, stationary, projection methods
  Krylov/…                      -- Krylov subspaces and methods
  Eigen/…                       -- eigenvalue perturbation and projection methods
  Approximation/…               -- best approximation, Chebyshev, interpolation, quadrature
  Variational/…                 -- forms, Lax–Milgram, Galerkin
  Nonlinear/…                   -- fixed point, Newton
  FloatingPoint/…               -- reserved
Surface/
  SaadSparse/ChNN/….lean        -- one Lake library per book, srcDir = "Surface"
  FongSaunders/SecN.lean
  AtkinsonHan/ChNN/….lean
plans/
  backbone.md                   -- this file; sub-plans next to it
```

`lakefile.toml` additions:

```toml
[[lean_lib]]
name = "SaadSparse"
srcDir = "Surface"

[[lean_lib]]
name = "FongSaunders"
srcDir = "Surface"

[[lean_lib]]
name = "AtkinsonHan"
srcDir = "Surface"
```

with `defaultTargets = ["Numlib", "SaadSparse", "FongSaunders", "AtkinsonHan"]` so CI builds
everything. Surface libraries import `Numlib` only (never each other).

### 1.6 Mathlib reuse table (verified in the local `v4.34.0-rc2` checkout)

| Concept | Mathlib name(s) | Status for us |
|---|---|---|
| Orthogonal projection onto a submodule | `Submodule.starProjection`, `Submodule.orthogonalProjectionOnto`, `starProjection_minimal`, `sub_starProjection_mem_orthogonal`, `starProjection_norm_le` | reuse; instance `HasOrthogonalProjection` for finite-dimensional `K` |
| Projection onto closed convex sets | `exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero` | reuse (AH 3.4.1–3.4.3) |
| Gram–Schmidt | `InnerProductSpace.gramSchmidtNormed`, `gramSchmidtNormed_orthonormal'`, `span_gramSchmidt_Iic` | Arnoldi vectors are literally `gramSchmidtNormed` of the Krylov sequence |
| Symmetric operators, spectral theorem | `LinearMap.IsSymmetric`, `LinearMap.IsSymmetric.eigenvectorBasis`, `.eigenvalues`, `IsSelfAdjoint`, `LinearMap.IsPositive` | reuse for L3 Chebyshev bounds and Kantorovich |
| Rayleigh quotient | `ContinuousLinearMap.rayleighQuotient`, `hasEigenvalue_iSup_of_finiteDimensional`, `spectralRadius_eq_nnnorm` | reuse; Courant–Fischer is missing |
| Hermitian matrices | `Matrix.IsHermitian.eigenvalues`, `eigenvectorBasis`, `spectral_theorem`, `Matrix.PosDef`, `PosDef.eigenvalues_pos` | bridge lemmas to `LinearMap.IsSymmetricCoercive` |
| Neumann series / units | `Units.oneSub`, `Units.ofNearby`, `Units.add`, `NormedRing.inverse_one_sub`, `inverse_add_norm_diff_first_order`, `ContinuousLinearEquiv.isOpen` | qualitative parts; explicit bounds (AH (2.3.13)–(2.3.15)) to add |
| Spectral radius, Gelfand | `spectralRadius`, `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` (ℂ), `spectrum.spectralRadius_pow_le`, `spectrum.subset_closedBall_norm` | reuse; "`ρ<1 ↔ aⁿ→0`" to add |
| Matrix norms | scoped `Matrix.Norms.L2Operator` (`l2_opNorm_def`, `l2_opNorm_conjTranspose_mul_self`), `Matrix.Norms.Operator` (`linfty_opNorm_*`), `Matrix.Norms.Frobenius` | reuse; equivalence constants (Higham Table 6.2) to add |
| Gershgorin, diagonal dominance | `eigenvalue_mem_ball`, `Matrix.det_ne_zero_of_sum_row_lt_diag` | reuse |
| Chebyshev polynomials | `Polynomial.Chebyshev.T`, `abs_eval_T_real_le_one`, `leadingCoeff_le_of_forall_abs_le_one`, `eval_iterate_derivative_le_of_forall_abs_le_one`, `roots_T_real`, Chebyshev–Gauss quadrature | min–max on `[a,b]` with `p(γ)=1` to add (short, see §2.4) |
| Lagrange interpolation | `Lagrange.interpolate`, `Lagrange.basis` | reuse for the interpolation branch |
| Banach fixed point | `ContractingWith.fixedPoint`, `apriori_dist_iterate_fixedPoint_le`, `aposteriori_dist_iterate_fixedPoint_le`, `dist_fixedPoint_fixedPoint_of_dist_le'` | reuse (AH 5.1.3) |
| Lax–Milgram (real) | `IsCoercive`, `IsCoercive.continuousLinearEquivOfBilin` | complex version to add as a corollary |
| Compact operators, Fredholm | `IsCompactOperator`, `IsCompactOperator.hasEigenvalue_or_mem_resolventSet`, `ContinuousLinearMap.IsFredholm` | reuse for AH §2.8 surface |
| Singular values, LDL | `LinearMap.singularValues`, `Matrix.LDL.lower_conj_diag` | reuse (Choi, Kress §5.2) |
| Picard–Lindelöf, Gronwall | `IsPicardLindelof`, `norm_le_gronwallBound_of_norm_deriv_right_le` | reuse (AH 5.2.4, Kress 10.1) |
| Weierstrass | `polynomialFunctions_closure_eq_top`, `exists_polynomial_near_continuousMap` | reuse (AH 2.4.4 quadrature convergence) |
| Polynomials in an endomorphism | `Polynomial.aeval`, `Module.AEval'`, `Polynomial.degreeLT`, `minpoly` | Krylov subspaces; `Module.AEval'` gives the cyclic-module view |
| Floating point | `Mathlib/Data/FP/Basic.lean` (definitions only, no theorems) | not usable; third-party Lean libraries listed in §6 |

Absent from Mathlib (so backbone content): Krylov subspaces, Arnoldi/Lanczos, condition number,
explicit Neumann-series perturbation bounds, `ρ<1 ↔ Gᵏ→0`, Courant–Fischer, Bauer–Fike, Kantorovich
inequality, Chebyshev min–max on an interval, Céa/Petrov–Galerkin/inf–sup, complex Lax–Milgram,
Newton's local convergence and Kantorovich's theorem, Jordan form, Perron–Frobenius (only
irreducibility is there), orthogonal polynomials beyond Chebyshev, Gauss quadrature, Hessenberg
matrices and Givens QR, the `γ_n` calculus.
---

## 2. Tree of contents, part I: normed-space, stationary and projection layers

Items are listed in logical progression order (each item only depends on earlier items or on
Mathlib). Each item names its module, the books it serves, the key Lean statements, and any
difficult proof. Rung labels (L0–L4) refer to §1.1. Phases refer to §7.

### 2.1 Mathlib-shaped gaps (upstreaming candidates)

These live in the topical folders `Numlib/Analysis/`, `Numlib/InnerProductSpace/`,
`Numlib/Matrix/`, `Numlib/Polynomial/` (mirroring Mathlib's tree; there is no separate
`ForMathlib` folder) and are stated in Mathlib's own vocabulary so they can be upstreamed. Each
such module starts with a comment "Upstreaming candidate … natural home: `Mathlib.…`"; the
numerical-analysis layers below only use them through their Mathlib-style names.

#### 2.1.1 `Analysis/NormedRing/Inverse.lean` (L2) — explicit Neumann-series and perturbation bounds
Serves AH Thm 2.3.1, Cor 2.3.3, Thm 2.3.5 (bounds (2.3.13)–(2.3.15)), Saad §1.13, Kress Thm 3.48
(Neumann series with a priori/a posteriori bounds), Saad-eig (3.14)/Prop 3.2 (resolvent Neumann
expansion), Higham Thm 7.2. Mathlib has the qualitative facts (`Units.oneSub`, `Units.ofNearby`,
`ContinuousLinearEquiv.isOpen`) but not the constants.

```lean
variable {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]

theorem NormedRing.norm_inverse_one_sub_le {t : R} (h : ‖t‖ < 1) :
    ‖Ring.inverse (1 - t)‖ ≤ 1 / (1 - ‖t‖)
theorem NormedRing.norm_inverse_one_sub_sub_one_le {t : R} (h : ‖t‖ < 1) :
    ‖Ring.inverse (1 - t) - 1‖ ≤ ‖t‖ / (1 - ‖t‖)
/-- AH Cor 2.3.3: `‖tᵐ‖ < 1` suffices. -/
theorem NormedRing.isUnit_one_sub_of_norm_pow_lt_one {t : R} {m : ℕ} (h : ‖t ^ m‖ < 1) :
    IsUnit (1 - t) ∧ ‖Ring.inverse (1 - t)‖ ≤ (∑ i ∈ Finset.range m, ‖t‖ ^ i) / (1 - ‖t ^ m‖)
/-- AH (2.3.13). ✓ -/
theorem Units.norm_inverse_add_le (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    ‖Ring.inverse ((x : R) + t)‖ ≤ ‖(↑x⁻¹ : R)‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖)
/-- AH (2.3.14). ✓ -/
theorem Units.norm_inverse_add_sub_le (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) :
    ‖Ring.inverse ((x : R) + t) - ↑x⁻¹‖ ≤
      ‖(↑x⁻¹ : R)‖ ^ 2 * ‖t‖ / (1 - ‖(↑x⁻¹ : R)‖ * ‖t‖)
```
plus the `E →L[𝕜] F` two-space version of AH 2.3.5 (only one of `V, W` complete) and the
"consistency + stability ⇒ convergence" corollary (2.3.16)
`‖v − vₙ‖ ≤ ‖Lₙ⁻¹‖ ‖(L − Lₙ) v‖`. Proofs: factor `x + t = x (1 + x⁻¹ t)` and apply the
`1 − t` bounds; the two-space version needs `L⁻¹` on the complete side. Nothing difficult.

#### 2.1.2 `Analysis/NormedRing/CondNumber.lean` (L2)
Serves Saad §1.13, AH §2.4.3, Kress §5.1, Higham Ch. 6–7, Choi §2.4.5.

```lean
/-- Condition number `‖a‖ ‖a⁻¹‖`; `0` (junk) if `a` is not a unit. ✓ -/
noncomputable def NormedRing.condNumber {R : Type*} [NormedRing R] (a : R) : ℝ :=
  ‖a‖ * ‖Ring.inverse a‖
theorem NormedRing.one_le_condNumber [NormOneClass R] {a : R} (ha : IsUnit a) : 1 ≤ condNumber a   -- ✓
theorem NormedRing.condNumber_smul (c : 𝕜) (hc : c ≠ 0) (a : R) : condNumber (c • a) = condNumber a
theorem ContinuousLinearEquiv.condNumber_eq (e : E ≃L[𝕜] E) : condNumber (e : E →L[𝕜] E) = ‖(e : E →L[𝕜] E)‖ * ‖(e.symm : E →L[𝕜] E)‖
```
Matrix versions are the same definition under the scoped norm instances
(`open scoped Matrix.Norms.L2Operator` gives `κ₂`, `Matrix.Norms.Operator` gives `κ_∞`); add
`Matrix.condNumber_l2_eq_div_singularValues` (L3, phase 2: `κ₂ = σ_max/σ_min` via
`LinearMap.singularValues`) and Saad Example 1.5 (`κ_∞(I + α e₁ eₙᵀ) = (1+|α|)²`) in the surface.

#### 2.1.3 `Analysis/SpectralRadius.lean` (L2, complex; L4 real matrices)
Serves Saad Thm 1.10–1.12, 4.1; Kress §5.2.2/AH §5.2.2; Higham Ch. 18.

```lean
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- `ρ(a) < 1 ↔ aⁿ → 0` (Saad Thm 1.10, valid in every complex Banach algebra). -/
theorem spectralRadius_lt_one_iff_tendsto_pow (a : A) :
    spectralRadius ℂ a < 1 ↔ Filter.Tendsto (fun n => a ^ n) Filter.atTop (nhds 0)
/-- Geometric decay at any rate above the spectral radius (Gelfand). -/
theorem exists_norm_pow_le_of_spectralRadius_lt (a : A) {r : NNReal} (hr : spectralRadius ℂ a < r) :
    ∃ C : ℝ, ∀ n, ‖a ^ n‖ ≤ C * r ^ n
/-- Saad Thm 1.11: the Neumann series converges iff `ρ(a) < 1`, and then `1 − a` is a unit. -/
theorem summable_pow_iff_spectralRadius_lt_one (a : A) : Summable (fun n => a ^ n) ↔ spectralRadius ℂ a < 1
```
Difficult proof (moderate): `⇒` picks `ρ < r < 1`, uses
`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` to get `‖aⁿ‖ ≤ rⁿ` eventually;
`⇐` uses `spectrum.spectralRadius_pow_le` and `spectralRadius_le_nnnorm`:
`ρ(a)ⁿ ≤ ρ(aⁿ) ≤ ‖aⁿ‖ → 0`. The bookkeeping is in `ENNReal`/`NNReal`; keep a real-valued
`spectralRadius'` helper if it gets painful. Real matrices: `Matrix.map Complex.ofReal` (see
2.1.11); no Jordan form is needed anywhere (Saad's proofs via Jordan form are replaced by Gelfand).

#### 2.1.4 `InnerProductSpace/Coercive.lean` (L1/L2/L3)
Serves Saad §1.11 (Thm 1.34), Prop 5.1, Thm 5.10; AH 5.1.4 (linear case), 8.3, 9.4; Kress Thm 3.29, 4.12.

```lean
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Coercive: Saad's "positive definite" (real, non-symmetric allowed), AH's "strongly monotone". ✓ -/
def LinearMap.IsCoercive (A : E →ₗ[𝕜] E) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x)
/-- SPD / HPD / strongly positive self-adjoint. ✓ -/
structure LinearMap.IsSymmetricCoercive (A : E →ₗ[𝕜] E) : Prop where
  isSymmetric : A.IsSymmetric
  isCoercive : A.IsCoercive

theorem LinearMap.IsCoercive.injective (hA : A.IsCoercive) : Function.Injective A
/-- Lax–Milgram flavour: coercive + bounded on a Hilbert space ⇒ invertible with `‖A⁻¹‖ ≤ 1/c`. -/
theorem ContinuousLinearMap.IsCoercive.exists_inverse [CompleteSpace E] {A : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsCoercive) : ∃ e : E ≃L[𝕜] E, (e : E →L[𝕜] E) = A ∧ ‖(e.symm : E →L[𝕜] E)‖ ≤ 1 / c
/-- Finite dimension: coercive ⇔ `re⟪A x, x⟫ > 0` for `x ≠ 0` (Saad Thm 1.34). -/
theorem LinearMap.isCoercive_iff_pos [FiniteDimensional 𝕜 E] (A : E →ₗ[𝕜] E) :
    A.IsCoercive ↔ ∀ x ≠ 0, 0 < RCLike.re (inner 𝕜 (A x) x)
theorem Matrix.posDef_iff_isSymmetricCoercive (M : Matrix n n 𝕜) :
    M.PosDef ↔ (Matrix.toEuclideanLin M).IsSymmetricCoercive
theorem LinearMap.IsSymmetricCoercive.coercive_const_eq_iInf_eigenvalues [FiniteDimensional 𝕜 E] … -- best `c` = `λ_min`
```
The Hilbert-space inverse bound is the linear case of AH Thm 5.1.4; prove it directly from
Mathlib's real Lax–Milgram applied to the real part of `⟪A x, y⟫` (see 5.2 for the trick that also
gives the complex Lax–Milgram), or via closed range: `‖A x‖ ≥ c‖x‖` ⇒ closed range, coercivity ⇒
`range ᗮ = ⊥`.

#### 2.1.5 `InnerProductSpace/Energy.lean` (L1)
Serves Saad Prop 5.2, 5.5, Thm 5.9, Lemma 6.28, PCG; AH §5.6, §9.4; Fong–Saunders; Meurant §3.

```lean
/-- Energy inner product `⟪x, y⟫_A := ⟪A x, y⟫` and energy norm of a symmetric coercive `A`. ✓ -/
noncomputable def energyInner (A : E →ₗ[𝕜] E) (x y : E) : 𝕜 := inner 𝕜 (A x) y
noncomputable def energyNorm (A : E →ₗ[𝕜] E) (x : E) : ℝ := Real.sqrt (RCLike.re (inner 𝕜 (A x) x))
/-- Type synonym of `E` carrying the energy inner product. -/
def WithEnergy (A : E →ₗ[𝕜] E) (_hA : A.IsSymmetricCoercive) : Type _ := E
noncomputable instance : InnerProductSpace 𝕜 (WithEnergy A hA)   -- via `InnerProductSpace.Core`
def WithEnergy.equiv : E ≃ₗ[𝕜] WithEnergy A hA
theorem WithEnergy.norm_equiv (x : E) : ‖WithEnergy.equiv x‖ = energyNorm A x
/-- Norm equivalence `c‖x‖² ≤ ‖x‖_A² ≤ ‖A‖‖x‖²` (needs `A` bounded for the upper bound). -/
theorem energyNorm_le / le_energyNorm
/-- `‖x* − x‖_A² = re⟪A⁻¹ r, r⟫` with `r = b − A x` (Saad Thm 5.9 proof, Meurant §3.3). -/
theorem energyNorm_error_sq_eq (hstar : A xstar = b) : energyNorm A (xstar - x) ^ 2 = RCLike.re (inner 𝕜 (xstar - x) (b - A x))
```
With this, Saad Prop 5.5 ("the Galerkin error is `(I − P^A_K) d₀`") is `starProjection` in
`WithEnergy`, and Céa with constant 1 (§5.3) is `starProjection_minimal` there. Completeness of
`WithEnergy` follows from norm equivalence when `E` is complete and `A` bounded.

#### 2.1.6 `InnerProductSpace/Compression.lean` (L1)
Serves Saad Prop 6.3, 6.5 (`V_mᴴ A V_m = H_m`), Saad-eig Ch. 4 (Rayleigh–Ritz), Meurant §2.

```lean
/-- The compression (section) `P_K A|_K` of `A` to a subspace. ✓ -/
noncomputable def compression (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] : K →ₗ[𝕜] K :=
  (K.orthogonalProjectionOnto : E →ₗ[𝕜] K).comp (A.comp K.subtype)
theorem inner_compression (x y : K) : inner 𝕜 (compression A K x) y = inner 𝕜 (A x) y
theorem compression_isSymmetric (hA : A.IsSymmetric) : (compression A K).IsSymmetric
/-- Matrix of the compression in an orthonormal basis `v` of `K` is `⟪v i, A (v j)⟫`. -/
theorem toMatrix_compression (b : OrthonormalBasis ι 𝕜 K) : LinearMap.toMatrix b b (compression A K) = Matrix.of fun i j => inner 𝕜 (b i : E) (A (b j))
/-- Saad Prop 6.3: `q(A) v = q(A_m) v` for `deg q < m` and `v ∈ 𝒦_m`; `P q(A) v = q(A_m) v` for `deg q ≤ m`. -/
theorem aeval_compression_krylov …
```

#### 2.1.7 `InnerProductSpace/ObliqueProjection.lean` (L1)
Serves Saad §1.12 (Lemma 1.36, Prop 1.37), Saad-eig §3.1, Saad §5.2.2 (`Q_K^L`).
Mathlib already has `LinearMap.IsSymmetricProjection` and
`IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker` (= Prop 1.37). Add: for finite-dimensional
`K, L` with `finrank K = finrank L`, `K ⊓ Lᗮ = ⊥ ↔ IsCompl K Lᗮ`, the projector
`obliqueProjection K L : E →ₗ[𝕜] E` (range `K`, kernel `Lᗮ`), its characterization
`P x ∈ K ∧ x − P x ∈ Lᗮ`, `P x = 0 ↔ x ∈ Lᗮ`, and Kato's lemma `‖P‖ = ‖1 − P‖` for bounded
idempotents on Hilbert spaces (phase 2; Xu–Zikatanov).

#### 2.1.8 `Polynomial/DegreeLT.lean` (L0)
Glue between `Polynomial.degreeLT`, `Polynomial.aeval` at an endomorphism and spans of iterates:

```lean
/-- `p ↦ p(A) v`. ✓ -/
noncomputable def Krylov.polyEval (A : Module.End R M) (v : M) : R[X] →ₗ[R] M
theorem Krylov.subspace_eq_map_degreeLT (A : Module.End R M) (v : M) (m : ℕ) :
    Krylov.subspace A v m = (Polynomial.degreeLT R m).map (Krylov.polyEval A v)   -- ✓
/-- Residual polynomials: `x − x₀ ∈ 𝒦_m(A, r₀)` ⇒ `b − A x = p(A) r₀` with `deg p ≤ m`, `p(0) = 1`. ✓ -/
theorem Krylov.exists_residual_poly …
```

#### 2.1.9 `Polynomial/ChebyshevMinimax.lean` (analysis)
Serves Saad Thm 6.25/6.29, AH (5.6.5), Meurant (3.9), Saad-eig Ch. 4/6 (Kaniel–Paige–Saad).

```lean
open Polynomial.Chebyshev in
/-- `min_{deg p ≤ m, p(0)=1} max_{t∈[a,b]} |p(t)| = 1/T_m((b+a)/(b−a))` for `0 < a < b`: lower bound. ✓ -/
theorem chebyshev_minimax_bound (m : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b) (p : ℝ[X])
    (hp : p.degree ≤ m) (hp0 : p.eval 0 = 1) :
    1 / (T ℝ m).eval ((b + a) / (b - a)) ≤ sSup ((fun t => |p.eval t|) '' Set.Icc a b)
/-- Attained by the shifted Chebyshev polynomial. -/
theorem chebyshev_minimax_attained …
/-- Closed form and the two-sided estimate `½ w^m ≤ T_m(x) ≤ w^m`, `w = x + √(x²−1)`, `x ≥ 1`. -/
theorem eval_T_real_eq_half_add_pow …
/-- `1 / T_m(1 + 2η) ≤ 2 ((√κ − 1)/(√κ + 1))^m` with `κ = b/a`, `η = a/(b−a)` (Saad (6.128)). -/
theorem one_div_eval_T_le …
```
General-`γ` version (Saad Thm 6.25, `p(γ) = 1`, `γ ∉ [a,b]`) is needed by the eigenvalue book;
state it and derive `γ = 0`.
Difficult proof (moderate): Mathlib's `eval_iterate_derivative_le_of_forall_abs_le_one` (k = 0)
says `|P| ≤ 1` on `[−1,1]` ⇒ `P(x) ≤ T_m(x)` for `x ≥ 1`. Compose `p` with the affine map
`t ↦ (2t − (a+b))/(b−a)` (so `[a,b] ↦ [−1,1]`, `0 ↦ −(b+a)/(b−a) < −1`), rescale by the sup, and
use `T_m(−x) = (−1)^m T_m(x)` to move to `x ≥ 1`. Degree bookkeeping for `Polynomial.comp` and
`sSup` of a continuous image of a compact interval are the only frictions. The complex ellipse
results (Saad Lemma 6.26, Thm 6.27) are phase 3.

#### 2.1.10 `Matrix/Hessenberg.lean` (L4)
Serves Saad §6.3–6.5, §6.5.7, Choi §2.2, Fong–Saunders §4.2, Kress §7.5.

```lean
def Matrix.IsUpperHessenberg {n R} [LinearOrder n] [Zero R] (H : Matrix n n R) : Prop :=
  ∀ i j, (∃ k, j < k ∧ k < i) → H i j = 0   -- ✓
def Matrix.IsTridiagonal … -- ✓
/-- Givens rotation in the `(i, i+1)` plane, unitary. -/
def Matrix.givens (i : Fin m) (c s : 𝕜) : Matrix (Fin (m+1)) (Fin (m+1)) 𝕜
/-- Progressive QR of an `(m+1) × m` upper Hessenberg matrix by `m` rotations (Saad (6.34)–(6.40)). -/
structure HessenbergQR (H : Matrix (Fin (m+1)) (Fin m) 𝕜) where (Q : …) (R : …) (rotations : …) (hQ : unitary) (hR : upper triangular, last row 0) (hQH : Q * H = R)
/-- `‖β e₁ − H̄ y‖² = |γ_{m+1}|² + ‖g − R y‖²` (Saad (6.43)); `γ_{j+1} = −s_j γ_j` (6.47). -/
```
Everything is finite index bookkeeping; the only care point is the complex rotation convention
(Saad (6.80): `s_i ≥ 0` real, `c_i` complex). Keep it minimal — no general QR theory.

#### 2.1.11 `Matrix/Complexify.lean` (L4)
`Matrix.complexify A := A.map Complex.ofReal` as an `ℝ`-algebra hom `Matrix n n ℝ →ₐ[ℝ] Matrix n n ℂ`;
`spectrum ℂ (complexify A) = {roots of charpoly}` (via `Matrix.mem_spectrum_iff_isRoot_charpoly` and
`charpoly_map`); norms are preserved for the `l∞` operator norm and the Frobenius norm;
`Matrix.spectralRadius A := spectralRadius ℂ (complexify A)` with the corollary
`(∀ x, Aᵏ x → 0) ↔ spectralRadius A < 1` for real matrices (via 2.1.3).

#### 2.1.12 `Matrix/Order.lean` (L4, phase 2)
Entrywise order and absolute value (`|A| ≤ |B|`, `|A * B| ≤ |A| * |B|`, monotonicity of products by
nonnegative matrices; Saad Prop 1.24/1.26, Higham §3.5). Watch out: Mathlib's `Matrix` order
instance in `Analysis/Matrix/Order.lean` is the *Loewner* order; the entrywise order must be a
scoped instance or go through `Matrix.of`/`Pi`. Needed by regular splittings (2.3.4) and by the
floating-point layer (§6).

### 2.2 `Numlib/LinearSolve/Perturbation.lean` (L2)
Serves Saad §1.13.2, AH §2.4.3 ((2.4.1) `cond(L)`), Kress Def 5.2/Thm 5.3 (already stated for Banach
spaces), Higham Thm 7.1–7.2, Choi Thm 2.34, Fong–Saunders §3.

```lean
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Residual–error relation `‖x − y‖/‖x‖ ≤ κ(A) ‖b − A y‖/‖b‖` (Saad (1.13.2) end, Kress). -/
theorem relative_error_le_condNumber_mul_relative_residual (A : E ≃L[𝕜] E) {b x y : E} (hx : A x = b) (hb : b ≠ 0) :
    ‖x - y‖ / ‖x‖ ≤ NormedRing.condNumber (A : E →L[𝕜] E) * (‖b - A y‖ / ‖b‖)
/-- Normwise perturbation bound (Saad (1.76) exact form, Higham Thm 7.2, AH (2.4.1)). ✓ (stated over ℂ in the prototype) -/
theorem relative_error_le_condNumber (A : E ≃L[𝕜] E) (ΔA : E →L[𝕜] E) (b Δb x y : E)
    (hx : A x = b) (hy : ((A : E →L[𝕜] E) + ΔA) y = b + Δb)
    (hsmall : ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖ < 1) (hx0 : x ≠ 0) (hb : b ≠ 0) :
    ‖y - x‖ / ‖x‖ ≤ NormedRing.condNumber (A : E →L[𝕜] E) / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖ΔA‖)
      * (‖ΔA‖ / ‖(A : E →L[𝕜] E)‖ + ‖Δb‖ / ‖b‖)
/-- Rigal–Gaches / Titley-Péloquin (Higham Thm 7.1, Fong–Saunders (3.2)–(3.3)): the normwise
relative backward error of `y` is `‖b − A y‖ / (α ‖A‖ ‖y‖ + β ‖b‖)`, attained by a rank-one perturbation. -/
theorem backwardError_eq [InnerProductSpace 𝕜 E] (A : E →L[𝕜] E) (b y : E) {α β : ℝ} … :
    IsLeast {ξ | ∃ ΔA Δb, (A + ΔA) y = b + Δb ∧ ‖ΔA‖ ≤ ξ * α * ‖A‖ ∧ ‖Δb‖ ≤ ξ * β * ‖b‖}
      (‖b - A y‖ / (α * ‖A‖ * ‖y‖ + β * ‖b‖))
```
Proof of the last: `(A + ΔA) y − b − Δb = 0` gives `‖r‖ ≤ ‖ΔA‖‖y‖ + ‖Δb‖`; the minimizer is
`ΔA = ((1−ω)/‖y‖²) r ⊗ y`, `Δb = −ω r` (rank one, so its operator norm equals `‖r‖/‖y‖`).
Stated in Hilbert space (rank-one operators via `inner`); the Banach version would use
`exists_dual_vector`. Componentwise theory (Oettli–Prager, Skeel) is phase 4 with Higham.

### 2.3 `Numlib/LinearSolve/Stationary/`

#### 2.3.1 `Stationary/Basic.lean` (L2, L3)
Serves Saad §4.2.1 (Thm 4.1, Cor 4.2, convergence factor), AH §5.2.2 and Ex 2.3.8/2.3.10,
Kress Thm 3.48 (a priori/a posteriori bounds), Thm 4.1 (convergence ⇔ `ρ < 1`), Thm 3.32
(`ρ ≤ ‖·‖`, and `∀ ε ∃` norm with `‖A‖ ≤ ρ + ε` — replaced here by Gelfand), §4.3 defect correction,
Saad-eig §3.5 (3.56)–(3.60), Higham Ch. 17 exact part.

```lean
/-- One affine step `x ↦ G x + f`. ✓ -/
def Stationary.step (G : E →L[𝕜] E) (f : E) (x : E) : E := G x + f
theorem Stationary.step_iterate_sub (hfix : G x' + f = x') (x₀ : E) (k : ℕ) :
    (Stationary.step G f)^[k] x₀ - x' = (G ^ k) (x₀ - x')
/-- Saad Thm 4.1 (⇒): in a complex Banach space, `ρ(G) < 1` gives `1 − G` invertible and convergence for all `f, x₀`. -/
theorem Stationary.tendsto_of_spectralRadius_lt_one [CompleteSpace F] (G : F →L[ℂ] F) (hG : spectralRadius ℂ G < 1) (f x₀ : F) :
    Filter.Tendsto (fun k => (Stationary.step G f)^[k] x₀) Filter.atTop (nhds (Ring.inverse (1 - G) f))
/-- Saad Thm 4.1 (⇐): finite dimension (false in infinite dimension — e.g. the left shift). ✓ (as an iff in the prototype) -/
theorem Stationary.spectralRadius_lt_one_of_forall_tendsto [FiniteDimensional ℂ F] (G : F →L[ℂ] F)
    (h : ∀ x₀, Filter.Tendsto (fun k => (G ^ k) x₀) Filter.atTop (nhds 0)) : spectralRadius ℂ G < 1
/-- Cor 4.2 / Kress: if `‖G‖ < 1` the map is a contraction; a priori bound `‖x_k − x*‖ ≤ ‖G‖^k/(1−‖G‖) ‖x₁ − x₀‖`. -/
theorem Stationary.contractingWith (hG : ‖G‖ < 1) : ContractingWith ⟨‖G‖, _⟩ (Stationary.step G f)
/-- Convergence factor is the spectral radius: `limsup ‖G^k d‖^{1/k} ≤ ρ(G)` and `= ρ(G)` for the worst `d`. -/
```
Real spaces: apply to the complexification (matrices via 2.1.11; general real Banach spaces are
out of scope until Mathlib has complexification of operators).

#### 2.3.2 `Stationary/Splitting.lean` (L2 ring-level, L4 constructors)
Serves Saad §4.1 (Jacobi, GS, SOR, SSOR, (4.18)–(4.27)), AH §5.2.2, Kress §4.1–4.2, Higham Ch. 17.

```lean
/-- A splitting `a = m − n` with `m` a unit, in any ring (matrices, `E →L[𝕜] E`); `n := m - a` is
derived, so the structure has no propositional field (R10). -/
@[ext] structure Stationary.Splitting {R : Type*} [Ring R] (a : R) where
  m : R
  isUnit : IsUnit m
def Stationary.Splitting.n (s : Splitting a) : R := s.m - a
/-- Iteration operator `G = 1 − m⁻¹ a = m⁻¹ n`. -/
noncomputable def Stationary.Splitting.iterationOperator (s : Splitting a) : R := 1 - Ring.inverse s.m * a
theorem Stationary.Splitting.iterationOperator_eq (s : Splitting a) : s.iterationOperator = Ring.inverse s.m * s.n
theorem Stationary.Splitting.eq_iterationOperator_mul_add_iff (s : Splitting a) : x = s.iterationOperator * x + Ring.inverse s.m * b ↔ a * x = b
/-- Fixed points of `x ↦ G x + m⁻¹ b` are exactly the solutions of `a x = b` (consistency). -/
-- matrix constructors (index type with a linear order):
def Matrix.strictLower / strictUpper / diagPart   -- ✓
noncomputable def Matrix.jacobiSplitting (A) (h : IsUnit (diagPart A)) : Stationary.Splitting A   -- M = D ✓
noncomputable def Matrix.gaussSeidelSplitting … -- M = D − E
noncomputable def Matrix.sorSplitting (ω : 𝕜) … -- M = ω⁻¹ (D − ω E)
noncomputable def Matrix.ssorSplitting (ω) …
def Stationary.Splitting.richardson (α : 𝕜) (a) : Splitting a   -- m = α⁻¹ • 1
/-- The preconditioned-system view: the iteration solves `m⁻¹ a x = m⁻¹ b`. -/
```
Block splittings and the general overlapping block Jacobi/GS (Saad Alg 4.1–4.2) are phase 2 and
reuse `Projection/Additive.lean`.

#### 2.3.3 `Stationary/DiagDominant.lean` (L4)
Serves Saad Thm 4.6–4.9, Cor 4.8; Kress Thm 4.2 (Jacobi with the explicit constants `q_∞, q₁, q₂`
and Banach-type error bounds), Thm 4.3 (Sassenfeld criterion for Gauss–Seidel), Cor 4.4, Thm 4.7
(irreducible weak dominance); AH Ex 5.2.2.

```lean
def Matrix.IsStrictDiagDominant (A : Matrix n n 𝕜) : Prop := ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖   -- ✓ (row); column variant
theorem Matrix.IsStrictDiagDominant.isUnit (hA) : IsUnit A   -- from Mathlib `det_ne_zero_of_sum_row_lt_diag`
/-- Saad Thm 4.9 (Jacobi). ✓ -/
theorem Matrix.jacobi_spectralRadius_lt_one (A : Matrix n n ℂ) (hA : IsStrictDiagDominant A) (h : IsUnit (diagPart A)) :
    spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1
theorem Matrix.gaussSeidel_spectralRadius_lt_one …
theorem Matrix.linfty_opNorm_jacobi_lt_one … -- the quantitative `‖G_J‖_∞ = max_i Σ_{j≠i}|a_ij|/|a_ii| < 1` (Kress Thm 4.2)
/-- Sassenfeld (Kress Thm 4.3): `‖(D − E)⁻¹ F‖_∞ ≤ p := max_j p_j` with the recursively defined `p_j`; strict row dominance gives `p ≤ q_∞` (Cor 4.4). -/
theorem Matrix.linfty_opNorm_gaussSeidel_le_sassenfeld …
```
Proofs: Jacobi via Gershgorin (`eigenvalue_mem_ball`) on `D⁻¹(E+F)` or directly via the
`‖·‖_∞` operator norm (the latter is simpler and also gives Kress's rate); Gauss–Seidel via Saad's
eigenvector argument with the split sums `σ₁, σ₂`. Irreducibly diagonally dominant matrices
(Thm 4.7, second half of 4.9) need `Matrix.IsIrreducible` (in Mathlib) and are phase 2.

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
Serves Saad §5.1–5.2 (Prop 5.1, 5.4–5.7), §1.12 (Thm 1.38, Cor 1.39 via Mathlib), Fong–Saunders §2,
Choi Table 2.5, AH §9 (bridge in §5.3).

```lean
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Petrov–Galerkin specification: `x ∈ x₀ + K`, `b − A x ⟂ L`. ✓ -/
structure IsPetrovGalerkin (A : E →ₗ[𝕜] E) (b x₀ : E) (K L : Submodule 𝕜 E) (x : E) : Prop where
  mem : x - x₀ ∈ K
  orth : b - A x ∈ Lᗮ
abbrev IsGalerkin (A) (b x₀) (K) (x) : Prop := IsPetrovGalerkin A b x₀ K K x   -- ✓
/-- Minimal residual over `x₀ + K`. ✓ -/
structure IsMinRes (A : E →ₗ[𝕜] E) (b x₀ : E) (K : Submodule 𝕜 E) (x : E) : Prop where
  mem : x - x₀ ∈ K
  min : ∀ y, y - x₀ ∈ K → ‖b - A x‖ ≤ ‖b - A y‖
/-- Minimal Euclidean error over `x₀ + K` (SYMMLQ, CGNE). ✓ -/
structure IsMinError … 

/-- Saad Prop 5.1 (i). ✓ -/
theorem existsUnique_isGalerkin_of_isCoercive (hA : A.IsCoercive) (b x₀) (K) [FiniteDimensional 𝕜 K] : ∃! x, IsGalerkin A b x₀ K x
/-- Saad Prop 5.1 (ii). ✓ -/
theorem existsUnique_isMinRes_of_injOn (A) (b x₀) (K) [FiniteDimensional 𝕜 K] (hinj : Set.InjOn A K) : ∃! x, IsMinRes A b x₀ K x
/-- Existence of a minimal-residual iterate needs nothing (projection onto `A K`); the residual is unique. -/
theorem exists_isMinRes … ; theorem IsMinRes.residual_eq (hx : IsMinRes A b x₀ K x) : b - A x = (b - A x₀) - (K.map A).starProjection (b - A x₀)   -- ✓ (Prop 5.4)
/-- Saad Prop 5.6: exactness on invariant subspaces. ✓ -/
theorem IsPetrovGalerkin.eq_of_invt (hx) (hK : K ∈ Module.End.invtSubmodule A) (hr : b - A x₀ ∈ K) (hKL : ∀ z ∈ K, z ∈ Lᗮ → z = 0) : A x = b
/-- Saad Thm 5.7: `‖b − A_m x*‖ ≤ ‖Q A (1 − P_K)‖ ‖(1 − P_K) x*‖` for the projected operator. -/
theorem norm_projected_residual_le …
/-- Matrix representation with bases `V` of `K`, `W` of `L`: `x = x₀ + V (Wᴴ A V)⁻¹ Wᴴ r₀` (Saad (5.7)). -/
theorem isPetrovGalerkin_iff_toMatrix …
```

#### 2.4.2 `Projection/Optimality.lean` (L1)
Serves Saad Prop 5.2, 5.3, 5.5; Fong–Saunders §2.1–2.2; Choi Table 2.5; AH (5.6.14).

```lean
/-- Saad Prop 5.3: `L = A K` ⇔ residual minimization. ✓ -/
theorem isMinRes_iff_isPetrovGalerkin (A) (b x₀) (K) [FiniteDimensional 𝕜 K] (x) :
    IsMinRes A b x₀ K x ↔ IsPetrovGalerkin A b x₀ K (K.map A) x
/-- Saad Prop 5.2 / HS Thm 4:3: for symmetric coercive `A`, Galerkin ⇔ energy-norm error minimization. ✓ (one direction) -/
theorem isGalerkin_iff_energy_min (hA : A.IsSymmetricCoercive) (hstar : A xstar = b) [FiniteDimensional 𝕜 K] :
    IsGalerkin A b x₀ K x ↔ (x - x₀ ∈ K ∧ ∀ y, y - x₀ ∈ K → energyNorm A (xstar - x) ≤ energyNorm A (xstar - y))
/-- Saad Prop 5.5: the Galerkin error is the energy-orthogonal projection of `d₀` onto `Kᗮ_A`. -/
theorem IsGalerkin.error_eq (hA) … : xstar - x = WithEnergy.equiv.symm ((K.energy hA)ᗮ.starProjection (WithEnergy.equiv (xstar - x₀)))
/-- Nested subspaces: residual norms are nonincreasing. ✓ -/
theorem IsMinRes.norm_residual_le (hx : IsMinRes A b x₀ K x) (hx' : IsMinRes A b x₀ K' x') (hKK' : K ≤ K') : ‖b - A x'‖ ≤ ‖b - A x‖
theorem IsGalerkin.energyNorm_le … -- same for the energy norm of the error
/-- Fong–Saunders §2.1: the Galerkin iterate is the minimizer of `φ(x) = ½⟪A x, x⟫ − re⟪b, x⟫` over `x₀ + K`. -/
theorem isGalerkin_iff_isMinOn_quadratic …
```

#### 2.4.3 `Projection/OneDimensional.lean` (L1–L3)
Serves Saad §5.3 (Alg 5.2–5.4, Lemma 5.8, Thm 5.9, 5.10), Thm 6.30; AH (5.6.4) one-step rate;
Kress/AH Richardson.

```lean
/-- One projection step with `K = span{v}`, `L = span{w}`: `x + (⟪r, w⟫/⟪A v, w⟫) v` (Saad (5.12)). -/
noncomputable def Projection.step1 (A : E →ₗ[𝕜] E) (b : E) (v w : E) (x : E) : E
theorem Projection.step1_isPetrovGalerkin …
noncomputable def steepestDescentStep (A) (b) (x) := Projection.step1 A b r r
noncomputable def minimalResidualStep (A) (b) (x) := Projection.step1 A b r (A r)
noncomputable def residualNormSDStep (A : E →L[𝕜] E) (b) (x) := Projection.step1 A b (A† r) (A (A† r))
/-- Kantorovich inequality (Saad Lemma 5.8), inverse-free and in any inner product space (R2, R3):
proved by the compression trick (12.4) from the quadratic-form bounds. -/
theorem kantorovich_inequality {lmin lmax : ℝ} (hl : 0 < lmin) (hA : A.IsSymmetricBoundedBy lmin lmax)
    {x y : E} (hy : A y = x) :
    RCLike.re (inner 𝕜 (A x) x) * RCLike.re (inner 𝕜 y x) ≤ (lmax + lmin) ^ 2 / (4 * lmax * lmin) * ‖x‖ ^ 4
/-- Saad Thm 5.9. -/
theorem steepestDescent_energyNorm_le … : energyNorm A (xstar - steepestDescentStep A b x) ≤ (lmax - lmin) / (lmax + lmin) * energyNorm A (xstar - x)
/-- Saad Thm 5.10 (coercive bounded `A`, any Hilbert space): `‖r'‖ ≤ √(1 − c²/‖A‖²) ‖r‖`. -/
theorem minimalResidual_norm_le {A : E →L[𝕜] E} {c : ℝ} (hc : 0 < c) (hcoer : ∀ x, c * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (A x) x)) (b x : E) :
    ‖b - A (minimalResidualStep A b x)‖ ≤ Real.sqrt (1 - c ^ 2 / ‖A‖ ^ 2) * ‖b - A x‖
```
Kantorovich in a general Hilbert space (spectrum in `[lmin, lmax]`) can follow later from the
continuous functional calculus (see 3.9). RNSD = SD on the normal equations is a one-line
corollary once `Aᴴ A` is symmetric coercive.

#### 2.4.4 `Projection/Additive.lean` (L1, phase 2)
Saad §5.4: additive/multiplicative projection procedures, residual `r_{k+1} = (1 − Σ P_i) r_k`
with `P_i` the projector onto `A K_i` orthogonal to `K_i`; block Jacobi/GS are instances.
---

## 3. Tree of contents, part II: the Krylov layer (`Numlib/Krylov/`)

This is the spanning tree shared by Saad (both books), Fong–Saunders, Choi and Meurant–Strakoš, and
by Atkinson–Han §5.6/§9.4. Dependency order: Subspace → Arnoldi → Lanczos → Iterate → Hessenberg
→ Relations → CG, CR → Convergence → Monotonicity → (phase 2–3) Preconditioned, Singular,
OrthogonalPolynomials, BiLanczos.

### 3.1 `Krylov/Subspace.lean` (L0, L3)
Serves Saad §6.2 (Prop 6.1, 6.2), Saad-eig §6.1, Choi Def 2.1, Meurant §2.1.

```lean
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- `𝒦_m(A, v) = span {v, A v, …, A^(m−1) v}`. ✓ -/
def Krylov.subspace (A : Module.End R M) (v : M) (m : ℕ) : Submodule R M :=
  Submodule.span R (Set.range fun i : Fin m => (A ^ (i : ℕ)) v)
scoped notation "𝒦[" A ", " v "] " m => Krylov.subspace A v m
/-- `span {A^i v | i : ℕ}`, the smallest `A`-invariant subspace containing `v`. ✓ -/
def Krylov.fullSubspace (A : Module.End R M) (v : M) : Submodule R M
theorem Krylov.subspace_mono (A v) : Monotone (Krylov.subspace A v)                     -- ✓
theorem Krylov.map_subspace_le (A v m) : (𝒦[A, v] m).map A ≤ 𝒦[A, v] (m + 1)              -- ✓
theorem Krylov.fullSubspace_mem_invtSubmodule (A v) : fullSubspace A v ∈ Module.End.invtSubmodule A  -- ✓
theorem Krylov.subspace_eq_map_degreeLT …                                                -- ✓ (2.1.8)
/-- `𝒦_{m+1} = 𝒦_m ↔ 𝒦_m` is `A`-invariant ↔ `A^m v ∈ 𝒦_m`. -/
theorem Krylov.subspace_succ_eq_iff …

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
/-- The full Krylov space `⨆ m, 𝒦_m = span {Aⁱ v}`; finite-dimensional iff the sequence stabilises
(automatic in finite dimension). ✓ -/
def Krylov.fullSubspace (A : Module.End K V) (v : V) : Submodule K V
theorem Krylov.finiteDimensional_fullSubspace_iff : FiniteDimensional K (fullSubspace A v) ↔ ∃ m, (A ^ m) v ∈ 𝒦[A, v] m
/-- The grade is `finrank (fullSubspace A v)` (R4; `0` in the infinite-grade case). ✓ -/
noncomputable def Krylov.grade (A) (v) : ℕ := Module.finrank K (fullSubspace A v)
theorem Krylov.grade_eq_sInf [FiniteDimensional K (fullSubspace A v)] : grade A v = sInf {m | (A ^ m) v ∈ 𝒦[A, v] m}
/-- Saad Prop 6.1: `𝒦_m = 𝒦_grade` for `m ≥ grade`, and `𝒦_grade` is invariant. ✓ -/
theorem Krylov.subspace_eq_of_grade_le [FiniteDimensional K (fullSubspace A v)] (h : grade A v ≤ m) : 𝒦[A, v] m = 𝒦[A, v] (grade A v)
/-- Saad Prop 6.2: `dim 𝒦_m = min(m, grade)`. ✓ -/
theorem Krylov.finrank_subspace [FiniteDimensional K (fullSubspace A v)] (m) : Module.finrank K (𝒦[A, v] m) = min m (grade A v)
/-- `Aᵐ v ∈ 𝒦_m ↔ ∃ p monic of degree m, aeval A p v = 0`: the grade is the degree of the minimal
polynomial of `v` (Saad Ch. 6, G4). -/
theorem Krylov.pow_apply_mem_subspace_iff_exists_monic
/-- Minimal polynomial of `v` w.r.t. `A` (phase 2): monic generator of the annihilator of `v` in `Module.AEval' A`; `natDegree = grade`. -/
```
Also coercions for `A : E →L[𝕜] E` (via `(A : E →ₗ[𝕜] E)`) and matrices (`Matrix.toLin'`), with
`simp` lemmas. Difficult proof: `finrank_subspace` — linear independence of `v, …, A^{m−1} v` for
`m ≤ grade`: a dependence gives the least `j` with `A^j v ∈ 𝒦_j`, contradicting minimality of
`grade`; use `linearIndependent_iff'` and `Submodule.mem_span_range_iff_exists_fun`.

### 3.2 `Krylov/Arnoldi.lean` (L1)
Serves Saad §6.3 (Alg 6.1–6.2, Prop 6.4–6.6), Saad-eig §6.2, Choi (2.42)–(2.44), Meurant §2.1.

```lean
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Arnoldi vectors: Gram–Schmidt of the Krylov sequence; `0` after breakdown. ✓ -/
noncomputable def Arnoldi.vec (A : E →ₗ[𝕜] E) (b : E) : ℕ → E :=
  InnerProductSpace.gramSchmidtNormed 𝕜 (fun i : ℕ => (A ^ i) b)
/-- `h i j = ⟪v i, A v j⟫`. ✓ -/
noncomputable def Arnoldi.coeff (A) (b) (i j : ℕ) : 𝕜 := inner 𝕜 (Arnoldi.vec A b i) (A (Arnoldi.vec A b j))
theorem Arnoldi.orthonormal (A b) : Orthonormal 𝕜 (fun i : {i // Arnoldi.vec A b i ≠ 0} => Arnoldi.vec A b i)
theorem Arnoldi.span_vec (A b m) : Submodule.span 𝕜 (Arnoldi.vec A b '' Set.Iio m) = 𝒦[A, b] m     -- ✓ (Prop 6.4)
theorem Arnoldi.vec_eq_zero_iff (A b j) : Arnoldi.vec A b j = 0 ↔ Krylov.grade A b ≤ j                  -- Prop 6.6 (breakdown ⇔ grade)
theorem Arnoldi.coeff_eq_zero_of_lt (h : j + 1 < i) : Arnoldi.coeff A b i j = 0                          -- ✓ (Hessenberg)
/-- Arnoldi relation `A v_j = ∑_{i ≤ j+1} h_ij v_i` (Saad (6.9), Prop 6.5). ✓ -/
theorem Arnoldi.apply_vec (A b j) : A (Arnoldi.vec A b j) = ∑ i ∈ Finset.range (j + 2), Arnoldi.coeff A b i j • Arnoldi.vec A b i
/-- Algorithmic form (Saad Alg 6.1): `w_j = A v_j − ∑_{i≤j} h_ij v_i`, `h_{j+1,j} = ‖w_j‖`, `v_{j+1} = w_j / ‖w_j‖`. -/
theorem Arnoldi.vec_succ_eq (A b j) : Arnoldi.vec A b (j + 1) = (‖w‖)⁻¹ • w   -- with `w := A v_j − ∑_{i ≤ j} h_ij • v_i`
theorem Arnoldi.coeff_succ_self (A b j) : Arnoldi.coeff A b (j + 1) j = (‖w‖ : 𝕜)   -- real, ≥ 0
/-- `H̄_m : Matrix (Fin (m+1)) (Fin m) 𝕜`, `H_m`, and `H_m = V_mᴴ A V_m` (compression, 2.1.6). -/
noncomputable def Arnoldi.hessenberg (A b m) : Matrix (Fin (m + 1)) (Fin m) 𝕜
theorem Arnoldi.hessenberg_isUpperHessenberg …
theorem Arnoldi.apply_sum (y : Fin m → 𝕜) : A (∑ j, y j • v j) = ∑ i : Fin (m+1), (hessenberg A b m).mulVec y i • v i   -- `A V_m = V_{m+1} H̄_m`
```
Difficult proof: identification of the Gram–Schmidt definition with the classical recurrence
(`vec_succ_eq`). Mathlib gives `gramSchmidtNormed f (j+1) ∝ f (j+1) − P_{𝒦_{j+1}} f (j+1)`; the
classical `w_j = A v_j − P_{𝒦_{j+1}} (A v_j)` differs by the leading coefficient `c_j` of `v_j` as a
polynomial in `A` applied to `b`. Show by induction that all leading coefficients are positive
reals (both normalizations divide by a norm), hence the two unit vectors coincide (over `ℂ` too).
Alternative: define `Arnoldi.vec` by the classical recursion and prove it equals Gram–Schmidt;
the Gram–Schmidt definition is preferred because Mathlib supplies orthonormality, spans and the
breakdown behaviour (`gramSchmidtNormed` is `0` on dependent vectors) for free.
Householder Arnoldi (Alg 6.3), MGS variants and reorthogonalization are surface (or floating-point
phase) material.

### 3.3 `Krylov/Lanczos.lean` (L1, symmetric `A`)
Serves Saad §6.6 (Thm 6.19, Alg 6.15), Saad-eig §6.3, Choi §2.1, Meurant §2.1, Fong–Saunders §1.1.

```lean
theorem Arnoldi.coeff_eq_zero_of_isSymmetric (hA : A.IsSymmetric) (h : i + 1 < j) : Arnoldi.coeff A b i j = 0  -- ✓ (tridiagonal)
theorem Arnoldi.coeff_conj_of_isSymmetric (hA) : Arnoldi.coeff A b j (j+1) = conj (Arnoldi.coeff A b (j+1) j)   -- real, so `= β_{j+1}`
noncomputable def Lanczos.alpha (A b j) : ℝ := RCLike.re (Arnoldi.coeff A b j j)
noncomputable def Lanczos.beta (A b j) : ℝ := ‖…‖   -- `β_{j+1} = h_{j+1,j} ≥ 0`
/-- Three-term recurrence `A v_j = β_j v_{j−1} + α_j v_j + β_{j+1} v_{j+1}` (Saad Alg 6.15). ✓ (as `apply_arnoldi_of_isSymmetric`) -/
theorem Lanczos.apply_vec (hA) (j) : A (v (j+1)) = (β (j+1) : 𝕜) • v j + (α (j+1) : 𝕜) • v (j+1) + (β (j+2) : 𝕜) • v (j+2)
/-- `T_m` (real symmetric tridiagonal, even for complex Hermitian `A`) and `T̄_m`. -/
noncomputable def Lanczos.tridiag (A b m) : Matrix (Fin m) (Fin m) ℝ
noncomputable def Lanczos.tridiagExt (A b m) : Matrix (Fin (m + 1)) (Fin m) ℝ
theorem Lanczos.tridiag_isTridiagonal …; theorem Lanczos.hessenberg_eq_tridiagExt (hA) …
/-- Rayleigh bound `λ_min ≤ α_j ≤ λ_max` (L3). -/
theorem Lanczos.alpha_mem_Icc …
/-- Termination: `β_{grade} = 0`, `A V_ℓ = V_ℓ T_ℓ`, and `𝒦_ℓ` is invariant (Choi (2.4), Meurant §2.1). -/
```
Choi Prop 2.2 / Cor 2.3 / Thm 2.4 (termination index ≤ `rank A + 1`, ≤ number of distinct
eigenvalues with nonzero weight) are L3 statements for `Krylov/Singular.lean` (phase 2).

### 3.4 `Krylov/Iterate.lean` (L1)
Serves Saad §6.4–6.5 (Prop 6.7, 6.10, Lemma 6.28, 6.31), Fong–Saunders §2, Choi Table 2.5,
Thm 2.25/3.1 (abstract core), AH (5.6.12)–(5.6.14).

```lean
/-- GMRES / MINRES / CR specification at step `m`. ✓ -/
abbrev Krylov.IsMinResIterate (A : E →ₗ[𝕜] E) (b x₀ : E) (m : ℕ) (x : E) : Prop :=
  IsMinRes A b x₀ (𝒦[A, b - A x₀] m) x
/-- FOM / CG / Lanczos-method specification. ✓ -/
abbrev Krylov.IsGalerkinIterate (A) (b x₀) (m) (x) : Prop := IsGalerkin A b x₀ (𝒦[A, b - A x₀] m) x
/-- SYMMLQ / CGNE specification: minimal Euclidean error over `x₀ + A 𝒦_m`. -/
abbrev Krylov.IsMinErrorIterate (A) (xstar x₀) (m) (x) : Prop := IsMinError xstar x₀ ((𝒦[A, A (xstar - x₀)] m).map A) x   -- explicit target (R5)
/-- MINRES-QLP specification (phase 2): minimum-norm element of the minimal-residual set. -/
structure Krylov.IsMinNormMinResIterate …

/-- Saad Lemma 6.31: `‖r_m‖ = min_{deg p ≤ m, p(0)=1} ‖p(A) r₀‖`. ✓ -/
theorem Krylov.IsMinResIterate.norm_residual_eq_iInf (hx : Krylov.IsMinResIterate A b x₀ m x) :
    ‖b - A x‖ = ⨅ p : {p : 𝕜[X] // p.degree ≤ m ∧ p.eval 0 = 1}, ‖aeval A p.1 (b - A x₀)‖
/-- Saad Lemma 6.28: energy-norm analogue for Galerkin iterates. -/
theorem Krylov.IsGalerkinIterate.energyNorm_error_eq_iInf (hA : A.IsSymmetricCoercive) …
/-- Saad Prop 6.7: the Galerkin residual is a multiple of `v_{m+1}`; hence Galerkin residuals are mutually orthogonal. -/
theorem Krylov.IsGalerkinIterate.residual_mem_span (hx) : b - A x ∈ 𝕜 ∙ Arnoldi.vec A (b - A x₀) m
/-- Lucky breakdown (Prop 5.6 + Prop 6.6): at `m ≥ grade`, minimal-residual iterates are exact and Galerkin iterates (if they exist) are exact. -/
theorem Krylov.IsMinResIterate.apply_eq_of_grade_le (hx) (h : Krylov.grade A (b - A x₀) ≤ m) (hinj : Function.Injective A) : A x = b
/-- Any exact Krylov solution of a compatible system with symmetric `A` is the minimum-norm solution (core of Choi Thm 2.25/3.1). ✓ -/
theorem Krylov.norm_le_of_apply_eq (hA : A.IsSymmetric) (hx : x ∈ 𝒦[A, b] m) (hAx : A x = b) (y) (hy : A y = b) : ‖x‖ ≤ ‖y‖
/-- Existence/uniqueness: minimal-residual iterates always exist; unique iff `A` is injective on `𝒦_m`; Galerkin iterates exist and are unique for coercive `A`. -/
```
Proof of `norm_le_of_apply_eq`: for symmetric `A`, `range A ⟂ ker A`; `b ∈ range A` gives
`𝒦_m(A, b) ≤ (ker A)ᗮ`; if `A y = b` then `y − x ∈ ker A` and Pythagoras. No completeness or finite
dimension needed.

### 3.5 `Krylov/Hessenberg.lean` (transport to small problems; L1 + finite matrices)
Serves Saad §6.4 ((6.16)–(6.18)), §6.5 ((6.27)–(6.30), Prop 6.9, (6.62)), Choi §2.2 ((2.18)–(2.24),
Lemma 2.18–2.20), Fong–Saunders §4.2, Meurant (3.1).

```lean
/-- Isometry: for `x = x₀ + ∑ y_j v_j`, `‖b − A x‖ = ‖β e₁ − H̄_m y‖` (Saad (6.28)). -/
theorem Krylov.norm_residual_eq_norm_hessenberg (y : Fin m → 𝕜) (hm : m < grade) :
    ‖b - A (x₀ + ∑ j, y j • v j)‖ = ‖(‖r₀‖ : 𝕜) • Pi.single 0 1 - (Arnoldi.hessenberg A r₀ m).mulVec y‖
/-- FOM: `H_m y = β e₁` ⇒ Galerkin iterate (Saad (6.16)); GMRES: least squares ⇒ minimal-residual iterate (6.30). -/
theorem Krylov.isGalerkinIterate_of_mulVec_eq … ; theorem Krylov.isMinResIterate_of_isLeast …
/-- With the Givens QR of 2.1.10: `‖r_m‖ = |γ_{m+1}|`, `γ_{j+1} = −s_j γ_j`, so `‖r_m^G‖ = |s_m| ‖r_{m−1}^G‖` (Saad Prop 6.9, (6.62)); FOM residual `‖r_m^F‖ = ‖r_m^G‖/|c_m|` (Prop 6.12). -/
/-- Lanczos specialization (Choi (2.21)): `‖r_k‖ = φ_k = β₁ s₁ ⋯ s_k`; MINRES residual recurrence `r_k = s_k² r_{k−1} − φ_k c_k v_{k+1}` (Choi Lemma 2.18, Saad (6.55)); `A r_k ⟂ 𝒦_k` and the `‖A r_k‖` formula (Choi Lemma 2.19). -/
/-- Galerkin residual in Lanczos terms: `r_k = (−1)^k ‖r_k‖ v_{k+1}` and `‖r_k‖ = β_{k+1} |e_kᵀ y_k|` (Saad (6.87), Meurant §3.1). -/
```
All finite-index bookkeeping over an orthonormal family; this is where Saad's, Choi's and
Fong–Saunders' implementations meet. SYMMLQ's LQ factorization and MINRES-QLP's QLP are surface
(Choi) unless a second source needs them.

### 3.6 `Krylov/Relations.lean` (L1)
Serves Saad §6.5.7–6.5.8 (Prop 6.12–6.17, Lemma 6.18), Fong–Saunders (4.1), Choi Prop 2.16(3),
Greenbaum Lemma 5.4.1.

```lean
/-- Cullum–Greenbaum (Saad (6.65)). ✓ -/
theorem Krylov.inv_sq_norm_residual_minRes (hG : IsMinResIterate A b x₀ m xG) (hG' : IsMinResIterate A b x₀ (m+1) xG')
    (hF : IsGalerkinIterate A b x₀ (m+1) xF) (h0 : b - A xG' ≠ 0) :
    1 / ‖b - A xG'‖ ^ 2 = 1 / ‖b - A xG‖ ^ 2 + 1 / ‖b - A xF‖ ^ 2
/-- Cor 6.14: `1/‖r_m^G‖² = ∑_{i ≤ m} 1/‖r_i^F‖²`, hence `‖r_m^G‖ ≤ ‖r_m^F‖`; Prop 6.15: `‖r_m^G‖ ≤ min_i ‖r_i^F‖ ≤ √(m+1) ‖r_m^G‖`. -/
/-- Iterate relation `x_m^G = s_m² x_{m−1}^G + c_m² x_m^F`, residual relation (6.74)–(6.75), with `c_m² = ‖r_m^G‖²/‖r_m^F‖²`. -/
/-- Weiss's residual smoothing (Lemma 6.18): if the original residuals are orthogonal to the previous smoothed residual, `1/‖r_m^S‖² = 1/‖r_{m−1}^S‖² + 1/‖r_m^O‖²`. -/
/-- Brown (Prop 6.17, L3): GMRES stagnates at step `m` iff the FOM iterate is undefined (`H_m` singular). -/
```
Difficult proof (Cullum–Greenbaum without Givens): define the minimal-residual smoothing of the
Galerkin sequence, `r_m^S := r_{m−1}^S + η_m (r_m^F − r_{m−1}^S)` with the optimal `η_m`; Galerkin
residuals lie in `span{v_{i+1}}` and are pairwise orthogonal, so Weiss's lemma gives the harmonic
recurrence; `r_m^S ∈ r₀ + A 𝒦_m` and is minimal by induction, hence `r_m^S = r_m^G` by uniqueness of
the minimal residual. This keeps the result at L1 and independent of any factorization; the
Givens route in 3.5 gives the same identity and the `c_m, s_m` interpretation.

### 3.7 `Krylov/CG.lean` (L1; termination facts L3)
Serves Saad §6.7 (Alg 6.16–6.19, Prop 6.20, §6.7.3), AH (5.6.2)/§9.4 Alg 1, Fong–Saunders Table 2.1
and Table 5.1 (CG column), Meurant §3 (Thm 11, 12, (3.3)–(3.4)), Choi Table 2.7.

```lean
structure CG.State (E : Type*) where (x r p : E)                       -- ✓
/-- Hestenes–Stiefel step. ✓ -/
noncomputable def CG.step (A : E →ₗ[𝕜] E) (s : CG.State E) : CG.State E
noncomputable def CG.iterate (A) (b x₀) (k) : CG.State E := (CG.step A)^[k] ⟨x₀, b - A x₀, b - A x₀⟩   -- ✓
theorem CG.residual_eq (A b x₀ k) : (CG.iterate A b x₀ k).r = b - A (CG.iterate A b x₀ k).x          -- ✓
/-- Well-definedness: `⟪A p_k, p_k⟫ ≠ 0` as long as `r_k ≠ 0` (symmetric coercive `A`). -/
theorem CG.inner_apply_direction_pos …
/-- Invariants (Saad Prop 6.20, HS): orthogonal residuals, `A`-conjugate directions, `span{p_i} = span{r_i} = 𝒦_k`. ✓ -/
theorem CG.inner_residual_eq_zero (hA : A.IsSymmetricCoercive) (h : i ≠ j) : inner 𝕜 (iterate A b x₀ i).r (iterate A b x₀ j).r = 0
theorem CG.inner_apply_direction_eq_zero (hA) (h : i ≠ j) : inner 𝕜 (A (iterate A b x₀ i).p) (iterate A b x₀ j).p = 0
/-- CG realises the Galerkin specification. ✓ -/
theorem CG.isGalerkinIterate (hA : A.IsSymmetricCoercive) (b x₀ k) : Krylov.IsGalerkinIterate A b x₀ k (CG.iterate A b x₀ k).x
/-- CG residuals are the Lanczos vectors up to sign: `v_{k+1} = (−1)^k r_k/‖r_k‖` (Meurant (3.4)); Lanczos coefficients from CG coefficients (Saad (6.101)–(6.103)). -/
theorem CG.arnoldi_vec_eq … ; theorem CG.lanczos_alpha_eq … ; theorem CG.lanczos_beta_eq …
/-- Three-term residual recurrence (Saad Alg 6.19 / Meurant (3.3)). -/
/-- HS Thm 6:1 (local form, Meurant Thm 11): `‖ε_k‖_A² − ‖ε_{k+1}‖_A² = γ_k ‖r_k‖²`. ✓ -/
theorem CG.energy_error_sub_energy_error_succ …
/-- HS Thm 6:3 (Meurant Thm 12): `‖x* − x_k‖` is nonincreasing; the identity `‖ε_k‖² − ‖ε_{k+1}‖² = (‖ε_k‖_A² + ‖ε_{k+1}‖_A²)/μ(p_k)`. ✓ (monotonicity) -/
theorem CG.norm_error_antitone …
/-- Steihaug: `‖x_k‖` is nondecreasing from `x₀ = 0` (while `⟪A p_j, p_j⟫ > 0`). ✓ -/
theorem CG.norm_iterate_monotone …
/-- Termination (L3): `r_k = 0` for `k ≥ grade`; CG is a direct method in `≤ n` steps. -/
```
Difficult proofs: the invariants are a joint induction (standard; keep the induction hypothesis
as a bundled `CG.Invariant k` structure with the four orthogonality facts and the span equalities,
proved for `k+1` from `k`). Steihaug's monotonicity uses `⟪r_i, p_j⟫ = ‖r_i‖²` for `j ≥ i` and hence
`⟪p_i, p_j⟫ > 0` — a local argument, no termination needed. D-Lanczos / `LDLᵀ` derivation is surface
(Saad Alg 6.17, Choi Table 2.6).

### 3.8 `Krylov/CR.lean` (L1; sign results L3)
Serves Saad §6.8–6.9 (Alg 6.20, Lemma 6.21), Fong–Saunders Thm 2.1–2.2, Choi Table 2.12.

```lean
structure CR.State (E) where (x r p q : E)   -- `q = A p` ✓
noncomputable def CR.step / CR.iterate                                                       -- ✓
/-- Fong–Saunders Thm 2.1 / Luenberger: `⟪A p_i, A p_j⟫ = 0` (`i ≠ j`), `⟪r_i, A p_j⟫ = 0` (`j < i`). -/
/-- CR realises the minimal-residual specification (`= MINRES = GMRES` on symmetric systems). ✓ -/
theorem CR.isMinResIterate (hA : A.IsSymmetricCoercive) (b x₀ k) : Krylov.IsMinResIterate A b x₀ k (CR.iterate A b x₀ k).x
/-- Saad Lemma 6.21 (GCR): with `Aᴴ A`-orthogonal directions spanning `𝒦_j`, the minimal-residual iterate is `x_m = x_{m−1} + (⟪r_{m−1}, A p_{m−1}⟫/‖A p_{m−1}‖²) p_{m−1}`. -/
theorem Krylov.isMinResIterate_of_orthogonal_directions …
/-- Fong–Saunders Thm 2.2 (L3): all of `α_i, β_i, ⟪p_i, A p_j⟫, ⟪p_i, p_j⟫, ⟪x_i, p_j⟫, ⟪r_i, p_j⟫` are `≥ 0` on SPD systems. -/
/-- Fong–Saunders Thm 2.3: `‖x_k‖` nondecreasing. ✓ -/
theorem CR.norm_iterate_monotone …
```
CR on symmetric coercive `A` is well defined (`⟪r, A r⟫ > 0` unless `r = 0`); on indefinite `A`
the recurrence may break down while the minimal-residual iterate still exists — that is why the
spec, not the recurrence, is canonical.

### 3.9 `Krylov/Convergence/Polynomial.lean` (L3; L2 via functional calculus in phase 2)
Serves Saad Thm 6.29 (proof), Prop 6.32, Cor 6.33; AH (5.6.16)–(5.6.19); Meurant (3.7)–(3.8);
Saad-eig Ch. 6.

```lean
/-- Spectral norm bound for polynomials in a symmetric operator (finite dimension). -/
theorem LinearMap.IsSymmetric.norm_aeval_apply_le [FiniteDimensional 𝕜 E] (hA : A.IsSymmetric) (p : 𝕜[X]) (x : E) :
    ‖aeval A p x‖ ≤ (⨆ i, ‖p.eval (hA.eigenvalues rfl i : 𝕜)‖) * ‖x‖
theorem LinearMap.IsSymmetricCoercive.energyNorm_aeval_apply_le …   -- same in the energy norm
/-- Minimal-residual bound for symmetric `A`: `‖r_m‖ ≤ min_{p(0)=1} max_{λ ∈ σ(A)} |p(λ)| ‖r₀‖`. -/
/-- Saad Prop 6.32: for `A = X Λ X⁻¹`, `‖r_m‖ ≤ κ₂(X) ε^{(m)} ‖r₀‖`. (L4) -/
```
Phase 2 upgrade to Hilbert spaces: Mathlib's continuous functional calculus for self-adjoint
elements of the C*-algebra `E →L[𝕜] E` (`cfc`, with `‖cfc f a‖ = sup_{σ(a)} |f|`) gives
`‖p(A)‖ ≤ sup_{σ(A)} |p|` directly, which makes AH Thm 5.6.1 and the Kantorovich inequality fully
general (spectrum in `[c, ‖A‖]` for coercive bounded self-adjoint `A`).

### 3.10 `Krylov/Convergence/CG.lean`
Serves Saad Thm 6.29, Thm 6.30; AH Thm 5.6.1 ((5.6.4)–(5.6.6)); Meurant (3.9); Fong–Saunders §1.

```lean
/-- Chebyshev bound for any sequence of Galerkin iterates (Saad Thm 6.29, AH (5.6.5)). ✓ -/
theorem Krylov.IsGalerkinIterate.energyNorm_error_le (A : E →ₗ[𝕜] E)   -- any inner product space (R3)
    {lmin lmax : ℝ} (hl : 0 < lmin) (hll : lmin ≤ lmax) (hA : A.IsSymmetricBoundedBy lmin lmax)
    (hx : Krylov.IsGalerkinIterate A b x₀ m x) (hstar : A xstar = b) :
    energyNorm A (xstar - x) ≤ 2 * ((Real.sqrt (lmax / lmin) - 1) / (Real.sqrt (lmax / lmin) + 1)) ^ m * energyNorm A (xstar - x₀)
/-- Sharper form `‖ε_m‖_A ≤ ‖ε₀‖_A / T_m(1 + 2η)`, `η = λ_min/(λ_max − λ_min)` (Saad (6.123)). -/
/-- One-step steepest-descent comparison: `(√κ−1)/(√κ+1) ≤ (κ−1)/(κ+1)` (AH (5.6.6)). -/
/-- Saad Thm 6.30: restarted minimal-residual iterations converge for coercive `A` (each cycle beats one MR step, 2.4.3). -/
theorem Krylov.restarted_minRes_tendsto …
/-- Minimal-residual (MINRES) bound for symmetric indefinite `A` via Chebyshev on two intervals — phase 2. -/
/-- Winther superlinear convergence for `A = 1 − K`, `K` compact self-adjoint (AH Thm 5.6.2) — phase 2 (needs the compact spectral theorem: Mathlib gap). -/
```
Proof: 3.4 (energy-norm polynomial characterization) + 3.9 + 2.1.9 with `[a, b] = [λ_min, λ_max]`.
The `ℝ` restriction in the ✓ statement is only from the prototype; state over `RCLike 𝕜`.

### 3.11 `Krylov/Monotonicity.lean` (Fong–Saunders; L3)
Serves Fong–Saunders §2–3 and Table 5.1; Choi Lemma 2.14, 2.20; Steihaug.

```lean
/-- Fong–Saunders Thm 2.3 in specification form: for any sequence of Krylov minimal-residual iterates on an SPD system (`x₀ = 0`), `‖x_k‖` is nondecreasing. ✓ -/
theorem Krylov.IsMinResIterate.norm_monotone [FiniteDimensional 𝕜 E] (hA : A.IsSymmetricCoercive) (hx : ∀ k, Krylov.IsMinResIterate A b 0 k (x k)) : Monotone fun k => ‖x k‖
/-- Thm 2.4: `‖x* − x_k‖` nonincreasing; Thm 2.5: `‖x* − x_k‖_A` nonincreasing (strictly while `r_k ≠ 0`). -/
theorem Krylov.IsMinResIterate.norm_error_antitone … ; theorem Krylov.IsMinResIterate.energyNorm_error_antitone …
/-- Thm 3.1: normwise relative backward error `‖r_k‖/(α‖A‖‖x_k‖ + β‖b‖)` (2.2) and both optimal perturbations `‖E_k‖/‖A‖`, `‖f_k‖/‖b‖` are nonincreasing. (needs `0 < β` and `b ≠ 0`; the pure-ratio form is `AntitoneOn … (Set.Ici 1)`, R5) -/
theorem Krylov.IsMinResIterate.backwardError_antitone …
/-- Stopping rule (3.4): `ξ_k ≤ 1 ↔ ‖r_k‖ ≤ α‖A‖‖x_k‖ + β‖b‖`. -/
/-- Steihaug's generalization (indefinite `A`): `‖x_k‖` increasing while `⟪A p_j, p_j⟫ > 0` for `j ≤ k` (CG) resp. also `⟪r_j, A r_j⟫ > 0` (CR/MINRES). -/
/-- Choi Lemma 2.20 / (3.21): `‖A x_k‖` nondecreasing for minimal-residual iterates (`‖A x_k‖² = ‖A x_{k−1}‖² + τ_k²`). -/
```
Proof route: the specification-form theorems are proved by first showing that on SPD systems the
minimal-residual iterates coincide with the CR iterates (3.8, uniqueness from 2.4.1) and then using
Fong–Saunders' sign lemma (Thm 2.2), whose parts (d)–(f) use finite termination `x_ℓ = x*` and the
orthonormal expansion in `{A p_i/‖A p_i‖}`. Extending to Hilbert spaces (infinite orthonormal
expansions, `x_k → x*`) is a phase-3 improvement.

### 3.12 Phase 2–3 Krylov modules

* `Krylov/Preconditioned.lean` — PCG is CG for `M⁻¹ A` in `WithEnergy M` (Saad Alg 9.1, Prop
  9.1 left/right GMRES equivalence, Prop 9.2–9.3 flexible GMRES; AH §9.4's residual = Riesz
  representative is PCG with `M` = the Gram operator of `V`). Structural reuse of 3.7 with a
  different inner product; also Concus–Golub–Widlund (Saad §9.6) as an instance.
* `Krylov/Singular.lean` — Choi Ch. 2–3: termination-index bounds (Prop 2.2–Thm 2.4), MINRES on
  compatible singular systems returns `A† b` (Thm 2.25, from 3.4), incompatible case (Thm 2.27:
  a `{2,3}`-inverse solution), MINRES-QLP spec and Thm 3.1, norm/condition estimates (Lemmas
  2.31–2.33, (3.18)–(3.21)), preconditioning caveats (§3.4.2–3.4.3).
* `Krylov/OrthogonalPolynomials.lean` — Meurant §2.2–2.3, §3.3: the spectral measure of `(A, v)`
  (L3: `∑ ω_l δ_{λ_l}`), Lanczos polynomials orthonormal for it, Ritz values = roots of `p_{k+1}` =
  eigenvalues of `T_k`, Gauss quadrature (Thm 1) with weight formulas, `‖ε_k‖_A² = ‖r₀‖²
  [(T_n⁻¹e₁, e₁) − (T_k⁻¹e₁, e₁)]` (Thm 9), spectral formulas (Thm 8), persistence (Thm 5, 7:
  theorems about unreduced symmetric tridiagonal matrices). Also feeds Kress §9.3 (Gauss
  quadrature) and Saad §6.6.2.
* `Krylov/BiLanczos.lean` — Saad Ch. 7: two-sided Lanczos (Prop 7.1), BCG (Prop 7.2), QMR
  (Prop 7.3, Thm 7.4, (7.23)–(7.25)) as instances of 3.5–3.6 with a non-orthonormal basis
  (quasi-residual); CGS/BiCGSTAB/TFQMR are surface.
* `Krylov/Block.lean` — Saad §6.12: surface unless the eigenvalue book's block methods are done.
* Faber–Manteuffel (Saad §6.10, L3, unique to Saad) — Saad surface; its Lemma 6.23 ("`Aᴴ v ∈ 𝒦_s(A,v)`
  for all `v` iff `A` normal with `ν(A) ≤ s−1`") could move to `Eigen/Normal.lean` if the eigenvalue
  book needs normal-matrix theory.
---

## 4. Tree of contents, part III: the eigenvalue layer (`Numlib/Eigen/`)

Shared by Saad-eig (whole book), Saad §1.8–1.9/§4/§6.6, Kress Ch. 7, Higham Ch. 18, Meurant §2
(Ritz values), Choi §2.1. Phase 1 contains only what the Krylov layer needs (4.1, part of 4.2);
the rest is phase 2–3 and is driven by the Saad-eig surface. Theorem numbers follow the survey
the Saad-eig/Kress analysis notes, since removed (Saad-eig = revised edition; Kress = GTM 181). The survey's
main structural finding is adopted here: linear-system projection methods (§2.4) and eigenvalue
projection methods (4.2) are the same object, the compression `compression A K` of 2.1.6, with
Céa's `‖A‖/c` and Saad-eig's `γ = ‖P_K A (1 − P_K)‖` as the two error constants.

### 4.1 `Eigen/Perturbation.lean` (L3, L4)
Serves Saad-eig Ch. 3 (Thm 3.6 Bauer–Fike, Thm 3.7/Cor 3.2 Jordan version, Cor 3.3 Hermitian
residual bound, Lemma 3.2/Thm 3.8/Cor 3.4 Kato–Temple, Thm 3.9 eigenvector bound, Prop 3.4/Thm 3.10
backward error, Def 3.1–3.2/Prop 3.5 conditioning, Thm 3.11–3.12 Gershgorin, Prop 3.6, Def 3.3/
Prop 3.7 pseudospectra), Saad-eig Thm 1.9–1.10 and Kress Thm 7.3–7.4 (Rayleigh/Courant–Fischer),
Kress Cor 7.5 (Weyl), Cor 7.6, Thm 7.7 (Gershgorin), Cor 7.9 (Schur inequality), Saad Thm 1.35
(Bendixson), Choi §2.4 (Ritz-value bounds), Higham §18.

```lean
/-- Residual bound (Hermitian; Saad-eig Cor 3.3): every approximate eigenpair has an eigenvalue within `‖A x − μ x‖/‖x‖`. ✓ -/
theorem LinearMap.IsSymmetric.exists_eigenvalue_dist_le [FiniteDimensional 𝕜 E] (hA : A.IsSymmetric) (x : E) (hx : x ≠ 0) (μ : ℝ) :
    ∃ i, |hA.eigenvalues rfl i - μ| ≤ ‖A x - (μ : 𝕜) • x‖ / ‖x‖
/-- Bauer–Fike (Saad-eig Thm 3.6, Kress Problem 7.6): `A = X Λ X⁻¹` diagonalizable, then `dist(μ, σ(A)) ≤ κ₂(X) ‖ΔA‖₂` for every `μ ∈ σ(A + ΔA)`; residual form `dist(μ, σ(A)) ≤ κ₂(X) ‖r‖`. ✓ -/
theorem Matrix.bauer_fike (X Λ ΔA) (hX : IsUnit X) (hΛ : Λ.IsDiag) (μ) (hμ : μ ∈ spectrum ℂ (X * Λ * X⁻¹ + ΔA)) :
    ∃ i, ‖μ - Λ i i‖ ≤ NormedRing.condNumber X * ‖ΔA‖
/-- Kato–Temple (Saad-eig Lemma 3.2, Thm 3.8, Cor 3.4): with Rayleigh quotient `μ`, residual `r`, and `(a, b) ∋ μ` containing exactly one eigenvalue `λ`, `−‖r‖²/(μ − a) ≤ λ − μ ≤ ‖r‖²/(b − μ)`; hence `|λ − μ| ≤ ‖r‖²/δ` with `δ` the gap to the other eigenvalues. -/
theorem LinearMap.IsSymmetric.kato_temple …
/-- Eigenvector bound (Saad-eig Thm 3.9): `sin θ(ũ, u) ≤ ‖r‖/δ`. -/
theorem LinearMap.IsSymmetric.sin_angle_le_norm_residual_div …
/-- Backward error of an approximate eigenpair (Saad-eig Prop 3.4, the eigenvalue analogue of Rigal–Gaches): `min {‖E‖ | (A − E) u = λ u} = ‖r‖`, attained at `r uᴴ`. -/
theorem eigen_backwardError_eq …
/-- Weyl (Kress Cor 7.5): `|λ_j(A) − λ_j(B)| ≤ ‖A − B‖` for symmetric `A, B` (needs Courant–Fischer, 4.2); Kress Cor 7.6 (diagonal entries vs eigenvalues) as a corollary. -/
theorem LinearMap.IsSymmetric.abs_eigenvalues_sub_le …
/-- Rayleigh quotient bounds: `λ_min ≤ re⟪A x, x⟫/‖x‖² ≤ λ_max` (Mathlib has `rayleighQuotient`, `iSup`/`iInf` attained). -/
/-- Bendixson (Saad Thm 1.35): `λ ∈ σ(A)` ⇒ `re λ ∈ [λ_min(H), λ_max(H)]`, `H = (A + Aᴴ)/2`; likewise `im λ` with the skew part. -/
theorem bendixson …
/-- Gershgorin (Saad-eig Thm 3.11, Kress Thm 7.7) is Mathlib's `eigenvalue_mem_ball`; add the union-of-discs form and the row/column variants. Disc counting (Saad-eig Thm 3.12) needs continuity of eigenvalues — phase 3. -/
/-- Condition number of a simple eigenvalue `1/|⟪u, w⟫|` (Saad-eig Def 3.1) and first-order perturbation `λ(ε) = λ + ε ⟪ΔA u, w⟫/⟪u, w⟫ + O(ε²)` (phase 2, via the implicit function theorem on `det`); eigenvector condition number `‖S(λ)(1 − P)‖` (Def 3.2) and its Hermitian value `1/dist(λ, σ(A)∖{λ})`. -/
/-- Pseudospectra (Saad-eig Def 3.3/Prop 3.7): `‖(A − z)⁻¹‖ > 1/ε ↔ ∃ E, ‖E‖ ≤ ε ∧ z ∈ σ(A − E)` — Hilbert-space level, phase 2. Wielandt–Hoffman, Davis–Kahan `sin θ` (phase 3). -/
```
Difficult proof: Bauer–Fike is short once `‖(Λ − μ)⁻¹‖₂ = 1/dist(μ, σ)` is available for diagonal
matrices (Mathlib's `Matrix.l2_opNorm` API for diagonal matrices needs a small lemma); the
eigenvalue-condition-number result needs differentiability of a simple root of the characteristic
polynomial (Mathlib: `HasStrictDerivAt` of `Polynomial.eval` + implicit function theorem).

### 4.2 `Eigen/RayleighRitz.lean` (L1 definitions, L3 bounds)
Serves Saad-eig §4.3 (Prop 4.3 exactness on invariant subspaces, Thm 4.3/4.7 residual bounds with
`γ`, Prop 4.4/Cor 4.1/Thm 4.4 Ritz values via min–max, Lemma 4.1/Thm 4.5 Ritz-value errors,
Thm 4.6 Ritz-vector angle, Prop 4.5), §6.1–6.2 (Prop 6.4 compression commutes with low-degree
polynomials, Thm 6.1 optimality of the characteristic polynomial of `H_m`, Prop 6.8 cheap residual
`‖(A − θ)ũ‖ = h_{m+1,m}|e_mᵀ y|`), Thm 8.1 (Davidson monotonicity), Meurant §2 (Ritz values),
Choi §2.4.4 (Ritz-value estimates), Kress Thm 11.17 (Céa in operator form: the linear-system twin).

```lean
/-- Ritz pairs of `A` on `K`: eigenpairs of the compression `compression A K` (2.1.6). -/
def IsRitzPair (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (θ : 𝕜) (u : E) : Prop :=
  u ∈ K ∧ u ≠ 0 ∧ A u - θ • u ∈ Kᗮ
theorem isRitzPair_iff_hasEigenvector (θ u) : IsRitzPair A K θ (u : E) ↔ Module.End.HasEigenvector (compression A K) θ u
/-- Oblique (Petrov–Galerkin) Ritz pairs: `u ∈ K`, `A u − θ u ⟂ L`. -/
def IsObliqueRitzPair …
/-- Saad-eig Prop 4.3: on an `A`-invariant `K`, every Ritz pair is an exact eigenpair. -/
theorem IsRitzPair.hasEigenvector_of_invt (hK : K ∈ Module.End.invtSubmodule A) …
/-- Saad-eig Thm 4.3 (any Hilbert space, bounded `A`, closed `K`): with `γ = ‖P_K A (1 − P_K)‖` and an exact unit eigenpair `(λ, u)`, `‖(A_K − λ) P_K u‖ ≤ γ ‖(1 − P_K) u‖` and `‖(A_K − λ) u‖ ≤ √(|λ|² + γ²) ‖(1 − P_K) u‖`; Thm 4.7 is the oblique version with `Q_K^L`. -/
theorem compression_residual_le …
/-- Hermitian case (Prop 4.4, Cor 4.1, Thm 4.4): Ritz values are min–max values over subspaces of `K`, hence `θ_i ≤ λ_i` (interlacing from below) and `θ ∈ [λ_min, λ_max]`. -/
theorem IsRitzPair.mem_Icc (hA : A.IsSymmetric) … : θ ∈ Set.Icc (λ_min) (λ_max)
/-- Saad-eig Lemma 4.1: `|λ − ⟪A P_K u, P_K u⟫/‖P_K u‖²| ≤ ‖A − λ‖ ‖(1 − P_K) u‖²/‖P_K u‖²`, so `0 ≤ λ₁ − θ₁ ≤ ‖A − λ₁‖ tan²θ(u₁, K)`; Thm 4.5 for the `i`-th eigenvalue. -/
theorem IsSymmetric.ritz_value_error_le …
/-- Saad-eig Thm 4.6: `sin θ(u, ũ) ≤ √(1 + γ²/δ²) sin θ(u, K)` for the Ritz vector of the closest Ritz value; Prop 4.5: `|λ − θ| ≤ ‖A − λ‖ sin²θ(u, ũ)`. -/
theorem IsSymmetric.sin_angle_ritzVector_le …
/-- Saad-eig Thm 6.1: the characteristic polynomial of the compression to `𝒦_m` minimizes `‖p(A) v‖` over monic `p` of degree `m` (Cayley–Hamilton + Prop 6.4); Prop 6.8: for a Ritz pair `(θ, V_m y)` of the Arnoldi compression, `‖(A − θ) ũ‖ = h_{m+1,m} |y_m|`. -/
theorem Arnoldi.charpoly_compression_isMinOn … ; theorem Arnoldi.norm_ritz_residual_eq …
/-- Courant–Fischer min–max (Saad-eig Thm 1.9, Kress Thm 7.4; Mathlib gap; phase 2): `λ_k = max_{dim S = k} min_{x ∈ S} R(x)`; Rayleigh's recursive form (Saad-eig Thm 1.10, Kress Thm 7.3). -/
theorem LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf …
```
Courant–Fischer is the main missing Mathlib brick here (only the extreme eigenvalues are in
Mathlib via `hasEigenvalue_iSup_of_finiteDimensional`); the standard dimension-counting proof
(`S ⊓ span{u_k, …, u_n} ≠ ⊥`) is ~100 lines with `Submodule.finrank_sup_add_finrank_inf_eq`. It also
gives Weyl's inequalities and the interlacing needed by Lanczos (3.3) and by Choi's Ritz-value
estimates.

### 4.3 `Eigen/PowerMethod.lean` (L3)
Serves Saad-eig Thm 4.1 (power method with a semi-simple dominant eigenvalue), §4.1.2–4.1.3
(shifted/inverse iteration, RQI stated), Thm 4.2/Prop 4.1–4.2 (Wielandt and Schur–Wielandt
deflation), Thm 5.1–5.2 (subspace iteration), Kress §7.2 (power method for diagonalizable `A`,
Lemma 7.18 subspace iteration, Thm 7.19 orthogonal iteration, Thm 7.20 QR algorithm).

```lean
noncomputable def powerIterate (A : E →ₗ[𝕜] E) (x₀ : E) (k : ℕ) : E := (‖(A ^ k) x₀‖)⁻¹ • (A ^ k) x₀
/-- If `λ₁` is a simple eigenvalue of strictly largest modulus and `x₀` has a nonzero component in its
spectral projector, then `A^k x₀ / λ₁^k → P₁ x₀` (hence `powerIterate` converges in direction) at rate `|λ₂/λ₁|^k`. -/
theorem powerIterate_tendsto [FiniteDimensional ℂ F] (A : F →ₗ[ℂ] F) {l₁ : ℂ} (h₁ : Module.End.HasEigenvalue A l₁)
    (hsimple : finrank (A.maxGenEigenspace l₁) = 1) (hdom : ∀ l ∈ spectrum ℂ A, l ≠ l₁ → ‖l‖ < ‖l₁‖)
    (x₀ : F) (hx₀ : spectral projector applied to x₀ ≠ 0) :
    Tendsto (fun k => (l₁ ^ k)⁻¹ • (A ^ k) x₀) atTop (nhds (P₁ x₀)) ∧ (geometric rate for every `r > max_{l ≠ l₁} |l|/|l₁|`)
/-- Inverse iteration / shift-and-invert: the power method for `(A − σ)⁻¹` (a `simp` lemma reusing the above with the spectrum mapped by `(· − σ)⁻¹`). -/
/-- Subspace iteration (Saad-eig Thm 5.2; Kress Lemma 7.18 is the diagonalizable case): if `|λ_m| > |λ_{m+1}|` and the spectral projector `P_m` onto the dominant invariant subspace is injective on `S₀`, then `gap(A^k S₀, range P_m) ≤ C (|λ_{m+1}/λ_m| + ε)^k`. Phase 3; the power method is `m = 1`. -/
theorem subspaceIterate_gap_le …
/-- Wielandt deflation (Saad-eig Thm 4.2): `σ(A − σ u₁ vᴴ) = {λ₁ − σ, λ₂, …}` when `vᴴ u₁ = 1`. Phase 3. -/
/-- QR algorithm = orthogonal iteration on the canonical flag (Kress Thm 7.20, algebraic part); convergence (Kress Thm 7.19) from subspace iteration. Phase 3. -/
```
Difficult proof: use the generalized-eigenspace decomposition (Mathlib
`Module.End.iSup_maxGenEigenspace_eq_top` over `ℂ`) to split `x₀ = P₁ x₀ + w`, with `w` in the
complementary `A`-invariant subspace `W` on which `spectrum (A|_W) = σ(A) ∖ {λ₁}`; Gelfand (2.1.3)
gives `‖(A|_W)^k‖ ≤ C r^k` for `r > max |λ|`, so `λ₁^{−k} A^k w → 0`. No Jordan form needed.
Subspace iteration follows the same pattern with `Submodule.map` and the gap between subspaces
(`‖P₁ − P₂‖`, Saad-eig §3.1; Mathlib gap: canonical angles / `Submodule` gap metric); it also
needs "a projector family with `‖P − Q‖ < 1` has constant rank" (Saad-eig Thm 3.2, easy).

### 4.4 `Eigen/KrylovEigen.lean` (L3)
Serves Saad-eig §6.6 (Lemma 6.1, Thm 6.3 angle bound, Thm 6.4 Kaniel–Paige–Saad, §6.6.3 Ritz
vectors), §6.7 (Lemma 6.2, Thm 6.5–6.7 Haar characterization, Prop 6.10, Thm 6.8 ellipse bound),
§4.4 (Thm 4.8 min–max with `p(γ) = 1`, Lemma 4.3 Zarantonello, Thm 4.9 ellipses), Saad §6.6,
Meurant §2.3 (Ritz values as Gauss nodes).

```lean
/-- Saad-eig Lemma 6.1: `tan θ(u_i, 𝒦_m) = min_{deg p ≤ m−1, p(λ_i)=1} ‖p(A) y_i‖ · tan θ(u_i, v₁)` (Hermitian). -/
theorem Lanczos.tan_angle_eq_iInf …
/-- Saad-eig Thm 6.3: `tan θ(u_i, 𝒦_m) ≤ κ_i tan θ(v₁, u_i) / T_{m−i}(1 + 2γ_i)`, `γ_i = (λ_i − λ_{i+1})/(λ_{i+1} − λ_n)`, `κ_i = ∏_{j<i} (λ_j − λ_n)/(λ_j − λ_i)`. -/
theorem Lanczos.tan_angle_le …
/-- Kaniel–Paige–Saad (Saad-eig Thm 6.4): `0 ≤ λ_i − θ_i^{(m)} ≤ (λ₁ − λ_n) (κ_i^{(m)} tan θ(v₁, u_i) / T_{m−i}(1 + 2γ_i))²`. -/
theorem kaniel_paige_saad …
/-- Ritz-vector bound (§6.6.3): Thm 4.6 with `γ = β_{m+1}` (Saad-eig Prop 6.6 basis-free form `‖P_m A (1 − P_m)‖ = h_{m+1,m}`). -/
/-- Non-Hermitian Arnoldi (Saad-eig Lemma 6.2): `‖(1 − P_m) u₁‖ ≤ ξ₁ ε₁^{(m)}` with `ε₁^{(m)} = min_{p(λ₁)=1} max_{λ ∈ σ(A)∖{λ₁}} |p(λ)|`; Prop 6.10 (circle enclosure `(ρ/|λ₁ − c|)^{m−1}`), Thm 6.8 (ellipse) — phase 3 with the complex Chebyshev results of 2.1.9. -/
/-- Ritz values of the Lanczos process are the eigenvalues of `T_m` and the roots of the Lanczos polynomial (Meurant §2.3). -/
```
Proofs combine 2.1.9 (Saad-eig Thm 4.8, the general-`γ` Chebyshev min–max, which the book states
without proof), 3.9 (polynomial norm bounds) and 4.2 (Courant–Fischer on `𝒦_m`); this is a direct
analogue of 3.10 and should be done right after it.

### 4.5 Phase 3 eigenvalue material
Analytic perturbation theory via Riesz–Dunford projectors (Saad-eig §3.1.3–3.1.5, Thm 3.3–3.5,
Prop 3.3: needs contour integrals of operator-valued functions — Mathlib has the Cauchy integral
formula for `ℂ`-valued functions only; use `Module.End.maxGenEigenspace` projectors instead, which
give Thm 3.3 algebraically), deflation (Saad-eig §4.2), subspace iteration (Ch. 5), restarting/
filtering/Chebyshev iteration (Ch. 7), Davidson/Jacobi–Davidson (Ch. 8), generalized/quadratic
problems (Ch. 9), Jacobi's method (Kress Thm 7.11–7.14: Frobenius-norm descent, independent of the
Krylov core), Hessenberg reduction (Kress Thm 7.22) and the QR algorithm (Kress Thm 7.19–7.20),
Higham Ch. 18 (matrix powers in finite precision, phase 4). Schur form (not in Mathlib: a phase-3
upstreaming candidate, R13), Jordan form (not in Mathlib; avoid: every use here is replaced by Gelfand or
by generalized eigenspaces; Saad-eig Thm 3.7/Cor 3.2 and P-5.6 are the only results that need the
Jordan index and stay in the surface).

---

## 5. Tree of contents, part IV: approximation, variational and nonlinear layers

### 5.1 `Numlib/Approximation/`

#### 5.1.1 `Approximation/BestApprox.lean` (L2)
Serves AH §3.3–3.4, §3.6–3.7 (Lebesgue lemma), Kress Thm 3.50–3.54 (existence in finite-dimensional
subspaces, orthogonality characterization, projection theorem, normal equations), Saad §1.12,
Saad-eig Thm 3.1.

```lean
/-- Best approximation from a set: `IsBestApprox K u v := v ∈ K ∧ ∀ w ∈ K, ‖u − v‖ ≤ ‖u − w‖`. -/
def IsBestApprox {V} [SeminormedAddCommGroup V] (K : Set V) (u v : V) : Prop
/-- AH Thm 3.3.16: existence from a finite-dimensional subspace (Heine–Borel). -/
theorem exists_isBestApprox_of_finiteDimensional (K : Submodule 𝕜 V) [FiniteDimensional 𝕜 K] (u : V) : ∃ v, IsBestApprox (K : Set V) u v
/-- AH Thm 3.3.14: existence from a closed convex set of a reflexive space — phase 3 (Mathlib lacks reflexivity/weak compactness). -/
/-- AH Thm 3.3.21: uniqueness in strictly convex spaces (Mathlib `StrictConvexSpace`). -/
theorem IsBestApprox.unique [StrictConvexSpace ℝ V] (hK : Convex ℝ K) (h₁ : IsBestApprox K u v₁) (h₂ : IsBestApprox K u v₂) : v₁ = v₂
/-- AH Lemma 3.4.1 / Thm 3.4.3 / Thm 3.4.6: Hilbert-space characterizations — Mathlib (`norm_eq_iInf_iff_real_inner_le_zero`, `Submodule.starProjection`, `exists_norm_eq_iInf_of_complete_convex`); provide the `IsBestApprox` glue lemmas. -/
/-- Lebesgue lemma (AH (3.7.11)/(3.7.14)/(3.7.21) abstracted): for a bounded projection `P` onto `S`, `‖u − P u‖ ≤ (1 + ‖P‖) dist(u, S)` and `≤ ‖1 − P‖ dist(u, S)`. -/
theorem norm_sub_projection_le (P : V →L[𝕜] V) (hP : IsIdempotentElem P) (u : V) : ‖u - P u‖ ≤ (1 + ‖P‖) * Metric.infDist u (LinearMap.range P)
/-- AH Prop 3.6.9 / Ex 3.6.7: `‖P‖ ≥ 1` for a nonzero projection; orthogonal ⇔ self-adjoint projection (Mathlib `IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker`). -/
```

#### 5.1.2 `Approximation/Chebyshev.lean`
Chebyshev equioscillation (AH Thm 3.3.19, Kress) — phase 3, Mathlib gap (Haar condition, de la
Vallée-Poussin). The min–max results the Krylov layer needs are already in 2.1.9; Chebyshev
expansions/uniform bounds (AH Ex 3.7.4) are phase 3.

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
Serves AH Thm 8.3.1–8.3.3, §9.1 (Ritz), Kress §11.

```lean
/-- Bounded sesquilinear forms are `V →L⋆[𝕜] V →L[𝕜] 𝕜` (Mathlib convention; `IsCoercive` in Mathlib is the real case). -/
def SesqForm.IsCoerciveWith (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (c : ℝ) : Prop := ∀ v, c * ‖v‖ ^ 2 ≤ RCLike.re (a v v)
def SesqForm.IsHermitian (a) : Prop := ∀ u v, a u v = conj (a v u)
/-- Operators ⟷ forms (AH Thm 8.3.1): `a u v = ⟪A u, v⟫` with `‖A‖ = ‖a‖`, via `InnerProductSpace.toDual`. -/
noncomputable def SesqForm.toOperator [CompleteSpace V] (a) : V →L[𝕜] V ; theorem inner_toOperator … ; theorem norm_toOperator …
theorem SesqForm.isCoerciveWith_iff (a) : a.IsCoerciveWith c ↔ (∀ v, c * ‖v‖ ^ 2 ≤ RCLike.re (inner 𝕜 (a.toOperator v) v))
/-- Energy functional `E v = ½ re (a v v) − re (ℓ v)`; for Hermitian coercive `a` its minimizers over a closed convex `K` are the solutions of the variational inequality (AH Thm 8.3.2–8.3.3), and over a subspace of the variational equation. -/
theorem SesqForm.isMinOn_energy_iff …
```

#### 5.2.2 `Variational/LaxMilgram.lean` (L2)
Serves AH Thm 8.3.4, Ex 8.2.5, Thm 8.2.4, Thm 8.7.1; Kress §11; Saad Prop 5.1 (bridge).

```lean
/-- Lax–Milgram over `RCLike 𝕜` (Mathlib has the real case `IsCoercive.continuousLinearEquivOfBilin`). -/
theorem laxMilgram [CompleteSpace V] (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) {c : ℝ} (hc : 0 < c) (ha : a.IsCoerciveWith c) (ℓ : V →L[𝕜] 𝕜) :
    ∃! u, ∀ v, a u v = ℓ v
theorem laxMilgram_norm_le … : ‖u‖ ≤ ‖ℓ‖ / c
/-- Bundled: the form's operator is a `ContinuousLinearEquiv` with `‖A⁻¹‖ ≤ 1/c`. -/
noncomputable def SesqForm.IsCoerciveWith.toEquiv …
/-- AH Thm 8.2.4 (Hilbert, bounded case): stability estimate `‖L v‖ ≥ c‖v‖` + `(range L)ᗮ = ⊥` ⇒ `L` bijective. -/
theorem bijective_of_antilipschitz_of_orthogonal_range_eq_bot …
/-- Babuška–Nečas (AH Thm 8.7.1): inf–sup + nondegeneracy ⇒ unique solvability with `‖u‖ ≤ ‖ℓ‖/α`. Phase 2. -/
theorem babuska_necas (a : U →L⋆[𝕜] V →L[𝕜] 𝕜) {α} (hα : 0 < α) (hinfsup : ∀ u, α * ‖u‖ ≤ ⨆ v ≠ 0, ‖a u v‖ / ‖v‖) (hnd : ∀ v ≠ 0, ∃ u, a u v ≠ 0) (ℓ) : ∃! u, ∀ v, a u v = ℓ v
```
Difficult proof (complex Lax–Milgram): apply Mathlib's real theorem to the real bilinear form
`(u, v) ↦ re (a u v)` on `V` viewed as a real inner product space (`InnerProductSpace.rclikeToReal`),
which is coercive with the same `c`; a real-linear solution `u` of `re a(u, v) = re ℓ(v)` for all `v`
also satisfies the imaginary parts by substituting `v ↦ I • v`. Alternatively prove it directly by
the closed-range argument (AH proof #2): `‖A u‖ ≥ c‖u‖` gives `AntilipschitzWith`, hence closed
range (`ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective`), and coercivity kills `(range A)ᗮ`.
The direct proof is probably shorter and also yields `babuska_necas` with the same skeleton.

#### 5.2.3 `Variational/Galerkin.lean` (L1/L2)
Serves AH §9.1–9.3 (Prop 9.1.3 Céa, Cor 9.1.4, Thm 9.2.1 Babuška, Rem 9.2.2 Xu–Zikatanov,
Thm 9.3.1 Strang), §9.4; Kress Thm 11.17 (Céa for `P_n A u_n = P_n f`, operator form) and Ch. 12
(projection methods for `I − K`, `K` compact: stability from Neumann series — phase 3); bridge to
Saad Ch. 5, Saad-eig §4.3 and to CG.

```lean
/-- Galerkin (variational) specification: `u ∈ K`, `a u v = ℓ v` for all `v ∈ K`. -/
structure IsGalerkinSolution (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (ℓ : V →L[𝕜] 𝕜) (K : Submodule 𝕜 V) (u : V) : Prop where
  mem : u ∈ K
  eq : ∀ v ∈ K, a u v = ℓ v
/-- Petrov–Galerkin with trial `K` and test `L`. -/
structure IsPetrovGalerkinSolution … (K L : Submodule 𝕜 V) …
/-- Well-posedness on any complete subspace (Lax–Milgram on `K`). -/
theorem existsUnique_isGalerkinSolution [CompleteSpace K] (ha : a.IsCoerciveWith c) (hc : 0 < c) : ∃! u, IsGalerkinSolution a ℓ K u
/-- Galerkin orthogonality: `a (u − u_K) v = 0` for `v ∈ K`. -/
/-- Céa's lemma (AH Prop 9.1.3, any subspace). ✓ -/
theorem cea (ha : a.IsCoerciveWith c) (hc : 0 < c) (hu : ∀ v, a u v = ℓ v) (huK : IsGalerkinSolution a ℓ K uK) :
    ‖u - uK‖ ≤ ‖a‖ / c * ⨅ v : K, ‖u - v‖
/-- Hermitian case: energy-norm best approximation (constant 1) and `‖u − u_K‖ ≤ √(‖a‖/c) inf ‖u − v‖`. -/
theorem cea_hermitian …
/-- Cor 9.1.4: nested subspaces with dense union ⇒ `u_n → u`. -/
theorem tendsto_galerkin_of_dense_iUnion …
/-- Babuška (AH Thm 9.2.1): discrete inf–sup `α_N` ⇒ unique solvability and `‖u − u_N‖ ≤ (1 + M/α_N) inf ‖u − w‖`; Xu–Zikatanov sharpening to `M/α_N` via Kato's lemma (2.1.7). Phase 2. -/
/-- First Strang lemma (AH Thm 9.3.1): approximation + consistency error. Phase 2 (`V + V_N` setting: state on an ambient space `W` with `V, V_N ≤ W` and an `N`-dependent norm — a type-synonym per `N`). -/
/-- Bridge: for `a u v = ⟪A u, v⟫`, `ℓ v = ⟪b, v⟫`: `IsGalerkinSolution a ℓ K u ↔ IsGalerkin A b 0 K u` (2.4.1), and `IsPetrovGalerkinSolution … ↔ IsPetrovGalerkin …`. -/
theorem isGalerkinSolution_iff_isGalerkin …
```
AH §9.4 (CG in variational form; the "residual" is the Riesz representative of `ℓ − a(u_k, ·)`) is
CG (3.7) run on the operator `A = a.toOperator` in `V`; AH §9.4's `‖u − u_k‖_a ≤ 2((√κ−1)/(√κ+1))^k`
is 3.10 with `κ = ‖a‖/c` — this needs the Hilbert-space (CFC) version of 3.9 or the
finite-dimensional statement restricted to the Krylov space. Note: on a Krylov space everything is
finite-dimensional, so the L3 bound applies to the *compression* of `A` to `𝒦_{k+1}`, whose
spectrum lies in `[c, ‖A‖]` by 4.2 — this gives the Hilbert-space CG bound without CFC. Record this
trick in `Convergence/CG.lean`.

### 5.3 `Numlib/Nonlinear/`

#### 5.3.1 `Nonlinear/FixedPoint.lean` (L2, metric)
Serves AH Thm 5.1.3–5.1.4, Thm 5.2.1, Ex 5.1.2, Ex 5.1.4; Kress Thm 3.45–3.46 (Banach with a priori/
a posteriori bounds), Thm 6.1–6.2 (scalar), Thm 6.7 (mean value inequality), Thm 6.8–6.9
(`sup ‖f'‖ < 1` criterion, local version), Problem 3.17 (`Aᵐ` contraction); Saad §4.2 (linear instance).
Mathlib: `ContractingWith`, `ContractingWith.fixedPoint`, `apriori_dist_iterate_fixedPoint_le`,
`aposteriori_dist_iterate_fixedPoint_le`, `efixedPoint'` (maps-to version on a complete subset).

```lean
/-- AH Thm 5.1.3 packaged: a contraction of a closed subset of a complete space; the three bounds (5.1.4)–(5.1.6). -/
theorem ContractingWith.dist_iterate_fixedPoint_le_of_mapsTo …   -- glue over Mathlib's `efixedPoint'`
/-- AH Ex 5.1.2: `T` continuous with `T^[m]` a contraction ⇒ unique fixed point, iteration converges. -/
theorem exists_unique_fixedPoint_of_iterate_contracting …
/-- Lipschitz constant from the derivative on a convex set (Mathlib `Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`) ⇒ contraction criterion `sup ‖T'‖ < 1`. -/
/-- AH Thm 5.1.4 (Zarantonello): strongly monotone + Lipschitz on a Hilbert space ⇒ bijective, with `‖u₁ − u₂‖ ≤ ‖b₁ − b₂‖/c`; the damped iteration `u ↦ u − θ (T u − b)` contracts with factor `√(1 − 2θc + θ²L²)`. -/
theorem zarantonello [CompleteSpace E] (T : E → E) {c L : ℝ} (hc : 0 < c)
    (hmono : ∀ x y, c * ‖x - y‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x - T y) (x - y))) (hlip : LipschitzWith L T) (b : E) :
    ∃! x, T x = b
/-- Linear instance: the stationary iteration 2.3.1 with `‖G‖ < 1`. -/
```
Bielecki weighted norms (AH Thm 5.2.3, Volterra) and generalized Picard–Lindelöf (Thm 5.2.4) are
AH surface / phase 3 (Mathlib has `IsPicardLindelof` in finite dimension).

#### 5.3.2 `Nonlinear/Newton.lean` (L2, Banach)
Serves AH Thm 5.4.1–5.4.2, Kress Thm 6.14 (semi-local Newton–Kantorovich with `αβγ < ½`, `r = 2α`),
Thm 6.20 (quadratic rate `(βγ/2)‖x* − x_ν‖²`), Cor 6.15 (local convergence for `C²`), Thm 6.21
(simplified Newton), Saad §9 (Newton–Krylov mention).

```lean
/-- Newton step with a supplied derivative-inverse `Df⁻¹ : E → (F →L[𝕜] E)`. -/
noncomputable def newtonStep (f : E → F) (Df : E → F ≃L[𝕜] E) (x : E) : E := x - (Df x) (f x)
/-- AH Thm 5.4.1: local quadratic convergence. -/
theorem newton_local_quadratic [CompleteSpace E] [CompleteSpace F] {f : E → F} {x* : E} (hroot : f x* = 0)
    {f' : E → E →L[𝕜] F} (hderiv : ∀ x ∈ Metric.ball x* r, HasFDerivAt f (f' x) x)
    (hlip : LipschitzOnWith L f' (Metric.ball x* r)) (hinv : ∃ e : E ≃L[𝕜] F, (e : E →L[𝕜] F) = f' x*) :
    ∃ δ > 0, ∃ M, M * δ < 1 ∧ ∀ x₀ ∈ Metric.ball x* δ, ∀ n,
      (newton sequence stays in the ball) ∧ ‖x_{n+1} − x*‖ ≤ M * ‖x_n − x*‖ ^ 2 ∧ ‖x_n − x*‖ ≤ (M * δ) ^ (2 ^ n) / M
/-- Newton–Kantorovich (AH Thm 5.4.2; Kress Thm 6.14 is the simpler variant with a uniform bound `‖f'(x)⁻¹‖ ≤ β` on `D` and `αβγ < ½`): existence in `B̄(x₁, t* − b)`, uniqueness in `B̄(x₀, t**)`, error `‖x_n − x*‖ ≤ (1 − √(1−2h))^{2ⁿ}/(2ⁿ a L)`. Do Kress's variant first (its proof is a direct induction), AH's as phase 2. -/
theorem newton_kantorovich …
/-- Modified (chord) Newton with frozen derivative: linear convergence via 5.3.1 (AH Ex 5.4.5). -/
```
Difficult proof: Thm 5.4.1 uses the integral form of the mean value theorem
`f(x*) − f(x) − f'(x)(x* − x) = ∫₀¹ (f'(x + t(x* − x)) − f'(x)) (x* − x) dt`; in Mathlib use the
inequality form `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` (bound of
`‖f y − f x − f' x (y − x)‖` by `sup ‖f' z − f' x‖ ‖y − x‖`, which is `≤ L‖y − x‖²`) to avoid Bochner
integrals; invertibility of `f' x` near `x*` with a uniform bound `c₀` comes from 2.1.1. Kantorovich
needs the majorant-sequence argument (`t_{n+1} = t_n − p(t_n)/p'(t_n)` for the scalar quadratic
`p`); Ortega–Rheinboldt §12.6 / Deuflhard's affine-invariant version are the references.

---

## 6. Reserved: floating-point layer (`Numlib/FloatingPoint/`, phase 4)

Higham is the sole source now; Paige/Greenbaum finite-precision Lanczos (Meurant §4–5) and Higham
Ch. 17 are the consumers. Only the *interface* is fixed now so that exact-arithmetic results are
stated in a way that survives perturbation.

```lean
/-- Standard model (Higham (2.4)): an abstract rounding with unit roundoff `u`. ✓ -/
structure Fl.RoundingModel (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  u : K
  u_nonneg : 0 ≤ u
  Rounds : K → K → Prop            -- `Rounds x y`: `y` is an admissible rounding of `x`
  abs_sub_le : ∀ x y, Rounds x y → |y - x| ≤ u * |x|
/-- `γ_n = n u / (1 − n u)` and its calculus (Higham Lemma 3.1, 3.3): `(1 + u)^n ≤ 1 + γ_n`, `∏ (1 + δ_i)^{±1} = 1 + θ_n`, `|θ_n| ≤ γ_n`, `γ_j + γ_k + γ_j γ_k ≤ γ_{j+k}`. ✓ (definition) -/
noncomputable def Fl.gamma (u : K) (n : ℕ) : K := n * u / (1 - n * u)
/-- Relative perturbation bookkeeping: `IsRelPert u n x y := ∃ θ, |θ| ≤ γ_n ∧ y = x * (1 + θ)`. -/
/-- Componentwise inner-product bound (Higham (3.4)): `|fl(xᵀy) − xᵀy| ≤ γ_n |x|ᵀ|y|`; matrix–vector, matrix–matrix ((3.12)–(3.13)); recursive summation (Ch. 4). -/
/-- Perturbed Arnoldi/Lanczos relation `A V_m = V_{m+1} H̄_m + F_m`, `‖F_m‖ ≤ ε` and orthogonality defect `‖V_mᴴ V_m − I‖ ≤ ε'` (Paige; Meurant Thm 14–15) as a *structure* `Arnoldi.IsPerturbedRelation`, with exact results restated as "`ε = 0` instance". -/
/-- Higham Thm 17.1–17.2 (stationary iteration in finite precision) as an instance of a perturbed 2.3.1 iteration. -/
```
Design rules (from the Higham analysis notes, since removed): componentwise statements first, normwise as
corollaries through `Matrix/Order.lean` (2.1.12); results about *algorithms* are stated for an
explicit evaluation order (a `SumTree`/fold), never for "the" floating-point sum; keep `K` abstract
(`ℝ` with a rounding relation), so that a concrete IEEE model (flean / FloatSpec) can instantiate
`Fl.RoundingModel` later. Gaussian elimination/Cholesky/QR error analysis (Higham Ch. 8–10, 19)
are Higham surface; only the model, the `γ` calculus and the inner-product lemmas are backbone.
---

## 7. Phasing and work estimate

Sizes are rough line counts of finished Lean (statements + proofs), based on the prototypes
(the v0 prototypes, since removed) and on comparable Mathlib files. Difficulty: ★ routine, ★★ needs care,
★★★ real proof engineering.

### Phase 1 — the spine (what the three selected books need)

| Module | Items | Size | Difficulty | Blocking |
|---|---|---|---|---|
| `Analysis/NormedRing/{Inverse,CondNumber}` | 2.1.1–2.1.2 | 250 | ★ | — |
| `Analysis/SpectralRadius` | 2.1.3 | 200 | ★★ (ENNReal bookkeeping) | — |
| `InnerProductSpace/{Coercive,Energy,Compression}` | 2.1.4–2.1.6 | 500 | ★★ (`WithEnergy` instance) | — |
| `Polynomial/{DegreeLT,ChebyshevMinimax}` | 2.1.8–2.1.9 | 400 | ★★ | — |
| `Matrix/{Hessenberg,Complexify}` | 2.1.10–2.1.11 | 400 | ★★ (Givens bookkeeping) | — |
| `LinearSolve/Perturbation` | 2.2 | 200 | ★ | 2.1.1–2.1.2 |
| `LinearSolve/Stationary/{Basic,Splitting,DiagDominant}` | 2.3.1–2.3.3 | 450 | ★★ (GS convergence) | 2.1.3, 2.1.11 |
| `LinearSolve/Projection/{Basic,Optimality,OneDimensional}` | 2.4.1–2.4.3 | 600 | ★★ (Kantorovich) | 2.1.4–2.1.7 |
| `Krylov/{Subspace,Arnoldi,Lanczos}` | 3.1–3.3 | 700 | ★★★ (Arnoldi = Gram–Schmidt) | 2.1.8 |
| `Krylov/{Iterate,Hessenberg,Relations}` | 3.4–3.6 | 700 | ★★ | 2.1.10, 2.4 |
| `Krylov/{CG,CR}` | 3.7–3.8 | 600 | ★★ (invariant induction) | 3.4 |
| `Krylov/Convergence/{Polynomial,CG}` | 3.9–3.10 | 350 | ★★ | 2.1.9, 3.4 |
| `Krylov/Monotonicity` | 3.11 | 350 | ★★ (finite termination) | 3.7–3.8 |
| `Eigen/Perturbation` (residual bound, Bauer–Fike, Bendixson) | 4.1 | 250 | ★★ | 2.1.6 |
| `Approximation/BestApprox` | 5.1.1 | 200 | ★ | — |
| `Variational/{Forms,LaxMilgram,Galerkin}` | 5.2 | 500 | ★★ (complex Lax–Milgram) | 2.1.4 |
| `Nonlinear/{FixedPoint,Newton}` (5.4.1 only) | 5.3 | 350 | ★★ | 2.1.1 |
| Surface `SaadSparse` (§1.11–1.13, 4.1–4.2, 5, 6) | §8.1 | 1200 | ★ (if backbone is right) | all above |
| Surface `FongSaunders` (complete) | §8.2 | 300 | ★ | 3.7–3.11 |
| Surface `AtkinsonHan` (selected sections) | §8.3 | 900 | ★ | 2.1, §5 |

Total ≈ 9.5 k lines. Recommended order: upstreaming candidates (2.1) → Projection → Krylov (Subspace…Relations) →
CG/CR → Convergence → Monotonicity → surfaces `FongSaunders` then `SaadSparse` (Krylov chapters
first), with Stationary/Perturbation/Variational/Nonlinear in parallel by a second worker since
they are independent of the Krylov chain. The skeleton in `Numlib/` is the full-signature
sub-plan for the Krylov chain and for the other layers.

### Phase 2 — second batch (Saad Ch. 7–9, Choi, remaining AH)
2.1.7 Kato's lemma, 2.1.12 matrix order, 2.3.4 regular splittings (needs weak Perron–Frobenius),
2.3.5 SPD/Ostrowski–Reich, 2.4.4 additive projections, 3.12 `Preconditioned`/`Singular`/`BiLanczos`,
4.2 Courant–Fischer + Ritz bounds, 4.4 Kaniel–Paige–Saad, 5.2.2 Babuška–Nečas, 5.2.3 Babuška/
Xu–Zikatanov/Strang, 5.3.2 Kantorovich, Hilbert-space CG bounds via CFC or compression (3.9).

### Phase 3 — Meurant–Strakoš exact part, Kress, remaining Saad-eig
3.12 `OrthogonalPolynomials` (Gauss quadrature, error identities), 4.3 power/subspace iteration,
4.5, 5.1.2–5.1.4 (equioscillation, interpolation, quadrature convergence), AH 6.2 Lax equivalence,
AH 5.2.3–5.2.4 (Bielecki norms, Picard–Lindelöf), Kress-specific direct methods (LU/Cholesky/QR
existence: Mathlib has `LDL`, no LU/QR).

### Phase 4 — floating point (Higham; Paige/Greenbaum)
§6: model, `γ` calculus, inner products, perturbed Krylov relations, Higham Ch. 17.

---

## 8. Surface libraries

Rules (README): chapter-to-chapter files; statements in the book's generality (real matrices,
`ℝⁿ`, real bilinear forms); each proof a specialization of a backbone result, through equivalence
lemmas for book-specific definitions; no new mathematics — anything that does not specialize is a
demand on the backbone and goes back into this plan.

### 8.1 `SaadSparse` (Surface/SaadSparse/ChNN/*.lean)

| Book location | Surface file | Backbone items used | Surface-specific definitions (need equivalence lemmas) |
|---|---|---|---|
| §1.8–1.9 normal/Hermitian matrices (Thm 1.7–1.9 spectral facts) | `Ch01/Spectral.lean` | Mathlib `Matrix.IsHermitian.eigenvalues`, `Matrix.schur_triangulation` | `Matrix.IsNormal`? (Mathlib has `IsStarNormal`) |
| §1.11 Thm 1.34–1.35 (positive definite, Bendixson) | `Ch01/PositiveDefinite.lean` | 2.1.4, 4.1 | Saad's "positive definite" = `IsCoercive` of `toEuclideanLin`; `Matrix.symmPart`/`skewPart` |
| §1.12 Lemma 1.36, Prop 1.37, Thm 1.38, Cor 1.39 (projectors) | `Ch01/Projectors.lean` | 2.1.7, Mathlib `starProjection_minimal` | matrix projector `V (Wᴴ V)⁻¹ Wᴴ` |
| §1.13 (1.76) perturbation, `κ(A)` | `Ch01/Conditioning.lean` | 2.1.2, 2.2 | `κ_p` for matrix `p`-norms (scoped instances) |
| §4.1 Jacobi/GS/SOR/SSOR matrices (4.5)–(4.27) | `Ch04/Splittings.lean` | 2.3.2 | `(jacobiSplitting A h).iterationOperator` with `jacobiSplitting_iterationOperator` etc. |
| §4.2 Thm 4.1–4.4, Cor 4.2 | `Ch04/Convergence.lean` | 2.1.3, 2.3.1, 2.3.4 (phase 2) | real matrices via `complexify` |
| §4.2.3 Thm 4.6–4.9 diagonal dominance | `Ch04/DiagDominant.lean` | 2.3.3 | irreducible variant (phase 2) |
| §4.2.4–4.2.5 Thm 4.10–4.16 SPD/SOR/Young | `Ch04/SPD.lean` | 2.3.5 (phase 2) | consistent ordering, Property A (surface-only) |
| §5.1–5.2 Prop 5.1–5.7 | `Ch05/Projection.lean` | 2.4.1–2.4.2 | matrix form `x = x₀ + V (Wᵀ A V)⁻¹ Wᵀ r₀` (5.7) with the equivalence to `IsPetrovGalerkin` |
| §5.3 Lemma 5.8, Thm 5.9–5.10, Alg 5.2–5.4 | `Ch05/OneDimensional.lean` | 2.4.3 | — |
| §5.4 Alg 5.5–5.6 | `Ch05/Additive.lean` | 2.4.4 (phase 2) | — |
| §6.2 Prop 6.1–6.2 | `Ch06/Krylov.lean` | 3.1 | `Matrix` Krylov space `𝒦_m(A, v)` as a `Submodule ℝ (n → ℝ)` |
| §6.3 Alg 6.1–6.3, Prop 6.4–6.6 | `Ch06/Arnoldi.lean` | 3.2 | Alg 6.2 (MGS) and 6.3 (Householder) as functions with equality to `Arnoldi.vec` in exact arithmetic |
| §6.4 (6.16)–(6.18), Prop 6.7, Alg 6.4–6.6 (FOM, restarted, IOM) | `Ch06/FOM.lean` | 3.4–3.5 | `FOM.iterate` := `x₀ + V_m H_m⁻¹ (β e₁)` with `IsGalerkinIterate` |
| §6.5 (6.27)–(6.47), Prop 6.9–6.12, Alg 6.9–6.13, Thm 6.30 | `Ch06/GMRES.lean` | 3.4–3.6, 3.10 | `GMRES.iterate` (least-squares form) with `IsMinResIterate`; breakdown/stagnation |
| §6.5.7–6.5.8 Prop 6.13–6.17, Lemma 6.18 | `Ch06/Relations.lean` | 3.6 | — |
| §6.6 Alg 6.15, Thm 6.19; §6.7 Alg 6.16–6.19, Prop 6.20; §6.7.3 | `Ch06/Lanczos.lean`, `Ch06/CG.lean` | 3.3, 3.7 | D-Lanczos (`LDLᵀ`) equals CG |
| §6.8–6.9 Alg 6.20–6.22, Lemma 6.21 | `Ch06/CR.lean`, `Ch06/GCR.lean` | 3.8 | ORTHOMIN(k)/ORTHODIR as functions; only the full versions satisfy the spec |
| §6.10 Lemma 6.22–6.24 Faber–Manteuffel | `Ch06/FaberManteuffel.lean` | surface-only (phase 3) | — |
| §6.11 Thm 6.25–6.29, Lemma 6.26–6.27, Prop 6.32, Cor 6.33 | `Ch06/Convergence.lean` | 2.1.9, 3.9–3.10 | complex ellipse results (phase 3) |
| §6.12 block methods | — | phase 3 | — |
| Ch. 7–9 | `Ch07..Ch09/` | 3.12 (phase 2) | — |

### 8.2 `FongSaunders` (Surface/FongSaunders/SecN.lean)

| Paper | Surface file | Backbone items |
|---|---|---|
| §1–1.1 setting, Lanczos, Table 2.1 (CG, CR) | `Sec1.lean`, `Sec2.lean` | 3.3, 3.7, 3.8 — the paper's CG/CR are literally `CG.iterate`/`CR.iterate` with `x₀ = 0`, `A : Matrix n n ℝ` symmetric positive definite (`Matrix.PosDef`) |
| §2.1–2.2 minimization properties (2.1)–(2.2) | `Sec2.lean` | 2.4.2, 3.4 (`isGalerkin_iff_energy_min`, `norm_residual_eq_iInf`) |
| Thm 2.1–2.5 | `Sec2.lean` | 3.8 (Thm 2.1–2.2), 3.11 (Thm 2.3–2.5) |
| §3 backward errors (3.1)–(3.6), Thm 3.1, stopping rules | `Sec3.lean` | 2.2 (`backwardError_eq`), 3.11 |
| §4.1 numerics — no theorems; §4.2 (4.1) FOM/GMRES relation; Steihaug indefinite | `Sec4.lean` | 3.6, 3.11 |
| §5 Table 5.1 | `Sec5.lean` | restatement of all of the above as one `structure` of properties per method |

Surface-specific: Frobenius norm `‖A‖_F` in the backward-error formula (equality with the operator
norm for the rank-one optimal perturbation; state both), `x₀ = 0` throughout, real symmetric
matrices.

### 8.3 `AtkinsonHan` (Surface/AtkinsonHan/ChNN/*.lean)

| Book | Surface file | Backbone items |
|---|---|---|
| Thm 2.3.1, Cor 2.3.3, Thm 2.3.4–2.3.5 | `Ch02/GeometricSeries.lean` | 2.1.1 |
| Thm 2.4.1–2.4.5 (Banach–Steinhaus), §2.4.4 quadrature convergence, (2.4.1) `cond(L)` | `Ch02/Operators.lean` | Mathlib `banach_steinhaus`; 2.2; 5.1.4 (phase 3) |
| §2.5 Hahn–Banach, Riesz | `Ch02/Functionals.lean` | Mathlib |
| Thm 3.3.14–3.3.21, Lemma 3.4.1–Thm 3.4.7, Prop 3.6.9, Lebesgue lemma | `Ch03/BestApprox.lean`, `Ch03/Projections.lean` | 5.1.1 |
| Thm 3.7.1–3.7.3 (Jackson etc.) | — | phase 3 (Mathlib gap) |
| Thm 5.1.3–5.1.4, 5.2.1, Ex 5.1.2 | `Ch05/FixedPoint.lean` | 5.3.1 |
| §5.2.2 linear systems | `Ch05/LinearIteration.lean` | 2.3.1–2.3.3 |
| Thm 5.2.2–5.2.4 (Urysohn, Volterra, Picard) | `Ch05/IntegralEquations.lean` | phase 3 |
| Thm 5.4.1–5.4.2 | `Ch05/Newton.lean` | 5.3.2 |
| Thm 5.6.1–5.6.3 (CG for operator equations) | `Ch05/ConjugateGradient.lean` | 3.7, 3.10 with the compression trick (5.2.3); Winther (5.6.2) phase 2 |
| Thm 8.2.1, 8.2.4, 8.2.7–8.2.8; Thm 8.3.1–8.3.4; Thm 8.7.1 | `Ch08/Existence.lean`, `Ch08/LaxMilgram.lean` | 5.2.1–5.2.2 |
| Prop 9.1.3, Cor 9.1.4, Thm 9.2.1, Rem 9.2.2, Cor 9.2.3, Thm 9.3.1 | `Ch09/Galerkin.lean`, `Ch09/PetrovGalerkin.lean`, `Ch09/Strang.lean` | 5.2.3 |
| §9.4 CG variational | `Ch09/CG.lean` | 3.7 via `SesqForm.toOperator` |

Surface-specific definitions: real bilinear forms `a : V → V → ℝ` with `IsBoundedBilinearMap`
(equivalence with `V →L[ℝ] V →L[ℝ] ℝ`), "V-elliptic", "strongly monotone", `‖·‖_a`, AH's
"projection operator" (Def 3.6.3) = `IsIdempotentElem` on `V →L[𝕜] V`.

### 8.4 Parked demands from the other five sources
* **Choi**: 3.12 `Singular` (pseudoinverse solutions, MINRES-QLP), `Lanczos` termination bounds;
  everything else specializes 3.3–3.6.
* **Meurant–Strakoš**: 3.12 `OrthogonalPolynomials`; §3 identities are in 3.7 (HS 6:1/6:3) and 2.1.5;
  §4–5 finite precision in §6.
* **Saad-eig**: §4 (numbers integrated above from the Saad-eig/Kress analysis notes, since removed); shares
  Ch. 1 with `SaadSparse/Ch01`, §4.3 with 2.4/2.1.6, §4.4 with 2.1.9, Ch. 6 with 3.1–3.3; Ch. 3
  analytic perturbation theory (Riesz–Dunford) and Ch. 7–9 are phase 3.
* **Kress**: Ch. 3 → 2.1.1, 2.3.1, 5.1.1, 5.3.1; Ch. 4 → 2.3.2–2.3.5 (Kress is the second source for
  Young's theory and the two-grid Thm 4.18 — the latter surface-only); Ch. 5 → 2.2 plus SVD/
  pseudoinverse/Tikhonov (Thm 5.4–5.10: Mathlib has `LinearMap.singularValues` but no SVD
  factorization — an upstreaming candidate under `Numlib/Matrix/` in phase 3); Ch. 6 → 5.3; Ch. 7 → 4.1–4.3, 4.5; Ch. 8–12
  (interpolation, quadrature, IVP/BVP, integral equations) phase 3.
* **Higham**: §6 plus 2.2 (Rigal–Gaches); Ch. 8–10, 19 surface.

---

## 9. Difficult-proof index

| # | Result | Where | Approach / reference |
|---|---|---|---|
| D1 | `ρ(a) < 1 ↔ aⁿ → 0` in complex Banach algebras | 2.1.3 | Gelfand's formula in Mathlib (`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`); `⇐` via `spectralRadius_pow_le`. The converse fails in ∞-dim for pointwise convergence; keep the norm version. Kreyszig §7.5 |
| D2 | Chebyshev min–max on `[a,b]` | 2.1.9 | affine change of variables + Mathlib `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one` (k = 0) + parity; Rivlin *Chebyshev Polynomials* Thm 1.10 |
| D3 | `‖p(A)x‖ ≤ max_{σ(A)} |p| ‖x‖`, energy-norm version | 3.9 | `LinearMap.IsSymmetric.eigenvectorBasis` expansion (finite-dim); later CFC. Saad Lemma 6.28/6.31 |
| D4 | Arnoldi vectors = `gramSchmidtNormed` of the Krylov sequence | 3.2 | induction on positive leading coefficients; or define by recursion and prove equality. Saad Prop 6.4–6.5 |
| D5 | Independence of `v, …, A^{m−1}v` for `m ≤ grade` | 3.1 | minimality of `grade` with `linearIndependent_iff'`. Saad Prop 6.2 |
| D6 | CG invariants ⇒ Galerkin | 3.7 | bundled `CG.Invariant k` induction; Saad Prop 6.20; Hestenes–Stiefel 1952 §5 |
| D7 | Cullum–Greenbaum harmonic relation without Givens | 3.6 | residual smoothing (Weiss 1994; Saad Lemma 6.18) + uniqueness of minimal residual; Cullum–Greenbaum 1996 |
| D8 | Fong–Saunders sign lemma and monotonicity | 3.8, 3.11 | finite termination; orthonormal expansion in `{A p_i}`; Fong–Saunders 2012 Thm 2.2; Steihaug 1983 |
| D9 | Kantorovich inequality | 2.4.3 | spectral theorem + convexity of `t ↦ 1/t` on the convex hull of the spectrum; Saad Lemma 5.8; Householder 1964 |
| D10 | Gauss–Seidel convergence under diagonal dominance | 2.3.3 | eigenvector argument (Saad Thm 4.9); Jacobi via `‖·‖_∞` |
| D11 | Complex Lax–Milgram | 5.2.2 | closed-range argument (`AntilipschitzWith` ⇒ closed range) or real parts on `rclikeToReal`; AH Thm 8.3.4 proof #2 |
| D12 | Rigal–Gaches optimal perturbation | 2.2 | rank-one construction `r ⊗ y/‖y‖²`; Higham Thm 7.1 |
| D13 | Minimum-norm Krylov solution | 3.4 | `range A ≤ (ker A)ᗮ` for symmetric `A`; Choi Thm 2.25 |
| D14 | Power method via generalized eigenspaces + Gelfand | 4.3 | `Module.End.iSup_maxGenEigenspace_eq_top`; avoids Jordan form. Saad-eig Thm 4.1 |
| D15 | Newton local quadratic convergence | 5.3.2 | `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` for the Taylor remainder, 2.1.1 for `f'(x)⁻¹`; AH Thm 5.4.1; Ortega–Rheinboldt 10.2.2 |
| D16 | Courant–Fischer | 4.2 | dimension counting on `S ⊓ span{u_k..u_n}`; Horn–Johnson Thm 4.2.6 |
| D17 | `WithEnergy` inner-product instance and its completeness | 2.1.5 | `InnerProductSpace.Core`; norm equivalence needs `A` bounded — take `A : E →L[𝕜] E` for the instance and derive the `→ₗ` case in finite dimension |
| D18 | Subspace iteration in Saad-eig's generality (Thm 5.2) | 4.3 | spectral projector onto the dominant generalized eigenspaces + Gelfand on the complement; gap between subspaces needs a `Submodule` gap/angle API (Mathlib gap). Kress Lemma 7.18 (diagonalizable) as a warm-up |
| D19 | Householder–John / Ostrowski–Reich in operator form | 2.3.5 | Rayleigh-quotient identity for an eigenpair of `M⁻¹N` (Kress Thm 4.12 proof) generalizes verbatim with `M + Mᴴ − A` coercive; Saad Thm 4.10 |

---

## 10. Extensibility

* **A second Krylov book** (Greenbaum; Liesen–Strakoš; van der Vorst; Trefethen–Bau Lectures
  32–38): everything is stated against 3.4's specs and 3.5's transport, so a new implementation
  (GMRES with Householder, BiCGStab, LSQR) only needs "algorithm ⇒ spec" plus the spec-level
  theorems. LSQR/LSMR (Fong's thesis, Table 5.2) are CG/MINRES on `AᵀA` — provide
  `Krylov/NormalEquations.lean` as the instance in phase 2.
* **A finite-element book** (Brenner–Scott, Ern–Guermond): 5.2 is stated for abstract Hilbert
  spaces and closed subspaces, so only Sobolev spaces are missing (Mathlib gap).
* **An optimization book** (Nocedal–Wright): CG as a minimizer of a quadratic (2.4.2, the energy
  functional) is the bridge; convex conjugates/Fenchel (README example) would go into a new
  `Numlib/Convex/` layer next to `Nonlinear/`.
* **Finite-precision papers** (Paige, Greenbaum, Meurant–Strakoš §4–5): §6's perturbed-relation
  structure is the hook; exact results are written so that `ε = 0` recovers them.
* **Naming discipline for discoverability**: specs are `Is…` structures (`IsMinRes`,
  `IsGalerkin`, `IsPetrovGalerkin`, `IsMinError`, `IsRitzPair`, `IsBestApprox`,
  `IsGalerkinSolution`); algorithms are namespaces with `State`/`step`/`iterate`
  (`CG`, `CR`, `Arnoldi`, `Lanczos`, `Stationary`); hypotheses are bundled in `LinearMap.Is…`
  (`IsCoercive`, `IsSymmetricCoercive`) or `SesqForm.Is…`; Mathlib-shaped lemmas keep Mathlib's
  naming (`norm_…_le`, `…_iff_…`, `exists_…`).

---

## 11. Open questions for the reviewer (answered in §12.4)

1. **`LinearMap` vs `ContinuousLinearMap` as the default operator type.** Prototypes use
   `E →ₗ[𝕜] E` for the projection/Krylov layer (no norms of `A` needed) and `E →L[𝕜] E` where
   `‖A‖`, spectral radius or completeness enter. The alternative is `→L` everywhere with a
   `FiniteDimensional` instance supplying continuity; this simplifies `WithEnergy` (D17) and the
   Hilbert-space convergence bounds but adds coercions in the finite-dimensional surface.
2. **Real symmetric vs `RCLike`.** All Krylov statements are over `RCLike 𝕜` with `RCLike.re`;
   the surface books are real. Is the `re` noise acceptable, or should the backbone offer real
   specializations as `abbrev`s (`IsSymmetricCoercive` over `ℝ` is `PosDef`-like)?
3. **Spectral hypotheses.** Phase 1 states spectral bounds with explicit `lmin, lmax` and
   `∀ μ, HasEigenvalue A μ → μ ∈ Icc lmin lmax` (finite-dim). The Hilbert-space form would be
   `spectrum 𝕜 A ⊆ Icc` and the CFC. Choose whether to invest in CFC-based 3.9 in phase 1
   (it makes AH 5.6.1 exact) or use the compression trick.
4. **Grade convention.** `Krylov.grade` is `sInf {m | A^m v ∈ 𝒦_m}` with junk `0` for infinite
   grade, guarded by `FiniteDimensional K (fullSubspace A v)`. Alternative: `ℕ∞`-valued grade.
5. **Where the matrix layer stops.** Givens/Hessenberg QR (2.1.10) is the only genuinely matrix
   algorithm in phase 1; everything else is operator-level. Is a small `Matrix.givens` API
   acceptable, or should GMRES's residual formula be derived from the abstract 3.6 relations only
   (possible: `‖r_m^G‖ = |s_m| ‖r_{m−1}^G‖` is a *definition* of `s_m` then)?
6. **Surface of Saad's algorithms.** Restarted/truncated variants (GMRES(m), IOM, DIOM, ORTHOMIN(k))
   do not satisfy the global specs; the surface will state only what the book proves (e.g.
   Thm 6.30 for GMRES(m)). Confirm this is the intended level of fidelity.
7. **Prototype files.** `plans/prototypes/Proto1.lean`, `Proto2.lean` type-check with `sorry`
   against the pinned Mathlib and are the evidence behind every ✓ in §2–§6; they should be
   deleted once the real skeleton exists.

---

## 12. Review outcome, surface demands and skeleton status (v1, 2026-09-04)

This section records what changed after the adversarial review
(issues R1–R20; the review file was removed once addressed) and the six chapter-level surface plans
(`plans/surface/*.md`, written from the high-quality OCR text). Where it contradicts §1–§11, this
section wins; the earlier sections are kept as the design rationale and have been patched only
where a name or path changed.

### 12.1 Status

* The phase-1 backbone skeleton exists and compiles with `sorry` bodies: 37 modules under
  `Numlib/` (list in `Numlib.lean`), about 520 `sorry`s, no statement-level `sorry`. Statements are
  the specification; proofs are being filled file by file (isolated working copies per agent,
  merged by the coordinator; see README "General instructions for agents").
* Surface libraries `SaadSparse`, `FongSaunders`, `AtkinsonHan` are registered in
  `lakefile.toml` (`srcDir = "Surface"`) with empty root modules; chapter files follow the plans
  in `plans/surface/`.
* The prototypes `plans/prototypes/Proto1.lean`, `Proto2.lean` were superseded by the skeleton and
  have been removed (R20); Proto1's `tendsto_affineIter_iff` was false in infinite dimension (R5).
  **A "✓" in §2–§6 means "elaborates", not "true"** (R5).

### 12.2 Layout change: no `ForMathlib` folder

Upstreaming candidates are not segregated into a `ForMathlib/` directory. They live in topical
folders mirroring Mathlib's own tree — `Numlib/Analysis/` (`SpectralRadius`,
`NormedRing/Inverse`, `NormedRing/CondNumber`), `Numlib/InnerProductSpace/` (`Coercive`, `Energy`,
`Compression`, `GramSchmidt`, `ObliqueProjection`), `Numlib/Matrix/` (`Hessenberg`, `Complexify`,
`ToEuclideanLin`), `Numlib/Polynomial/` (`ChebyshevMinimax`) — and each such module starts with a
comment block "Upstreaming candidate … natural home: `Mathlib.…`". The rule for these modules:
Mathlib conventions throughout, no dependency on the numerical-analysis layers.

### 12.3 Decisions on the blocking review issues

| Issue | Decision (implemented in the skeleton) |
|---|---|
| R1 `WithEnergy` did not elaborate | Rebuilt on Mathlib's `Matrix.toInnerProductSpace` pattern: the plain `AddCommGroup`/`Module` instances are *local* to the section that defines the `InnerProductSpace.Core`; only the core-derived normed instances are global; `WithEnergy.equiv : E ≃ₗ[𝕜] WithEnergy A hA` is defined afterwards with `rfl` fields; `inner_equiv`/`norm_equiv` are `rfl`; `submoduleMap K := K.map equiv.toLinearMap` with a `FiniteDimensional` instance. Only `A : E →ₗ[𝕜] E` and `IsSymmetricCoercive` are needed for the instance; `continuous_equiv` needs `A : E →L[𝕜] E`. |
| R2 `RCLike` statements that cannot elaborate | Convention: `open scoped ComplexOrder` wherever `Matrix.PosDef` appears; eigenvalue statements compare `RCLike.re μ` with real intervals; Kantorovich is inverse-free (`hy : A y = x`). |
| R3 spectral hypotheses | `LinearMap.IsSymmetricBoundedBy A lmin lmax` (`isSymmetric`, `lmin‖x‖² ≤ re⟪Ax,x⟫ ≤ lmax‖x‖²`) is the hypothesis of every Chebyshev-type bound (Kantorovich, Saad Thm 5.9/6.29, AH 5.6.1, Lanczos `α_j ∈ [λmin, λmax]`, Bendixson). It is stated in any inner product space (no `FiniteDimensional`); proofs go through the compression trick (12.4). Bridges: `IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue` (finite dimension), `IsSymmetric.isSymmetricBoundedBy_neg_norm_norm` (bounded operators), `Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin`. |
| R4 grade / `Fact` | `Krylov.grade A v := Module.finrank K (fullSubspace A v)`; hypothesis `[FiniteDimensional K (fullSubspace A v)]` (automatic in finite dimension); `grade_eq_sInf`, `finiteDimensional_fullSubspace_iff`, `pow_apply_mem_subspace_iff_exists_monic` (grade = degree of the minimal polynomial, Saad Ch. 6 G4) are lemmas. No `Fact`, no `ℕ∞`. |
| R5 false "✓" statements | `backwardError_antitone` requires `0 < β` and `b ≠ 0`, the pure-ratio form is `AntitoneOn … (Set.Ici 1)`; Proto1's `tendsto_affineIter_iff` is not in the skeleton (one-directional statements only; `Matrix.complexSpectralRadius` for real matrices, 12.5); `IsMinError xstar x₀ K x` now takes the target explicitly (best approximation of `xstar` from `x₀ + K`, no operator), so `exists_isMinError` is true for singular `A` and `Krylov.IsMinErrorIterate A xstar x₀ m x` uses `K = A 𝒦_m(A, A (xstar - x₀))`. |

### 12.4 Decisions on the should-fix issues and the §11 questions

* **§11 Q1** `→ₗ` at L0/L1, `→L` where norms/completeness enter (unchanged). **Q2** `RCLike` with
  `RCLike.re`; no real `abbrev`s; the surfaces state real theorems (`SesqForm.isCoerciveWith_real_iff`
  etc. remove the decorations). **Q3** quadratic-form bounds (R3). **Q4** `finrank` grade (R4).
  **Q5 / R11** Givens rotations are `ℕ`-indexed recursions on the infinite coefficient function
  (`Krylov.rotated`, `givensC/S/Rho`, `gamma`, `gvec`; `Krylov/Hessenberg.lean`), so prefix stability
  across `m` is automatic; the `Fin`-matrices `hessenbergOf`, `givensMatrix`, `givensQ` are built at
  the end. The spec-level identities `|s_m| = ‖r^G_{m+1}‖/‖r^G_m‖`, `|c_m| = ‖r^G_{m+1}‖/‖r^F_{m+1}‖`
  make 2.1.10 non-blocking for the Cullum–Greenbaum relations (3.6). **Q6** GMRES(m) satisfies the
  per-cycle spec `∀ k, IsMinResIterate A b (x k) m (x (k+1))`, so Saad Thm 6.30 is the backbone
  theorem `restarted_minRes_tendsto`; only truncated methods are algorithm-only. **Q7** see 12.1.
* **R6** Gram–Schmidt = classical recurrence (`Arnoldi.vec_succ_eq`, `coeff_succ_self`) stays in
  `Krylov/Arnoldi.lean` but is off the critical path (nothing in phase 1 uses it); proof via the
  one-dimensional space `𝒦_{j+2} ⊓ 𝒦_{j+1}ᗮ` as suggested. The flag-uniqueness lemmas
  (`InnerProductSpace/GramSchmidt.lean`, Saad Ch. 6 G8) serve MGS/Householder/block variants.
* **R7** the smoothing argument's gap is closed by `Krylov.map_subspace_succ_eq_sup_span`
  (`A 𝒦_{m+1} = A 𝒦_m ⊔ 𝕜 ∙ (r^F_{m+1} - r^G_m)`); Weiss's smoothing is exported as
  `Krylov.mrs`, `IsGalerkinIterate.mrs_isMinResIterate`, `residual_mrs_eq` (G9).
* **R8** real Banach spaces: `spectralRadius ℝ` is never used for convergence; real matrices use
  `Matrix.complexSpectralRadius A := spectralRadius ℂ (complexify A)` (`Numlib/Matrix/Complexify.lean`,
  with the rotation counterexample in the docstring).
* **R9** the energy structure stays operator-based (`WithEnergy A hA`); forms reach it through
  `SesqForm.toOperator = InnerProductSpace.continuousLinearMapOfBilin` (Hilbert spaces). A
  form-based `WithEnergy` for non-complete `V` is deferred to the finite-element phase; when it is
  added, the operator version becomes `WithEnergy (energyForm A)`.
* **R10** `Stationary.Splitting a` has fields `m`, `isUnit` only; `n := m - a`,
  `iterationOperator := 1 - Ring.inverse m * a`; constructors `Matrix.jacobiSplitting`,
  `gaussSeidelSplitting`, `backwardGaussSeidelSplitting`, `sorSplitting`, `ssorSplitting`,
  `Stationary.Splitting.richardson`; `@[ext]`.
* **R12** phasing: `Eigen/Perturbation` and `Variational/*` are independent of the Krylov chain
  and are being proved in parallel; `Krylov/Monotonicity` is the tail.
* **R13** name corrections applied in §1.6/§2/§4: no `Matrix.schur_triangulation` in Mathlib
  (Schur form is a phase-3 gap), `Submodule.finrank_sup_add_finrank_inf_eq`,
  `ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective`,
  `ContinuousLinearMap.toLinearMap_pow`; 2.1.1's first bound is a corollary of
  `NormedRing.tsum_geometric_of_norm_lt_one`; Cor 2.3.3's bound uses `∑ ‖tⁱ‖` (AH (2.3.6)), and
  the two-space perturbation theorem carries both (2.3.13) and (2.3.14).
* **R14** `IsMinResIterate.apply_eq_of_grade_le` (injective on `𝒦_grade`) and its converse
  `Krylov.grade_le_of_apply_eq` (no injectivity; G5) give Saad Prop 5.6/6.10 in both directions.
* **R15** the floating-point layer will be relational (`FloatingPoint` namespace), phase 4.
* **R16** names kept: `IsMinRes`, `compression`, `Arnoldi.vec`, `IsStrictDiagDominant` (with the
  `Col` variant); `IsSymmetricCoercive`'s docstring mentions SPD/HPD/`Matrix.PosDef`.
* **R18** power/subspace iteration (phase 2, 4.2) goes through `Module.End.iSup_maxGenEigenspace_eq_top` and `independent_maxGenEigenspace` with the restriction to `⨆_{μ ≠ λ₁} maxGenEigenspace μ`; the gap metric between subspaces is a Mathlib gap and is postponed.
* **R17** Chebyshev min–max avoids parity (`q.comp (-X)`). **R19** `⨅` statements kept; `IsLeast`
  forms can be added as corollaries when a consumer needs them.

### 12.5 Backbone additions demanded by the surface plans

From `plans/surface/SaadSparse-Ch6.md` (G1–G14) and `SaadSparse-Ch1-4-5.md`:
`Krylov.HessenbergRelation` with residual formulas for non-orthogonal bases (G1; IOM/DIOM/DQGMRES and
QMR are instances), `Arnoldi.coeff_eq_zero_of_adjoint_mem` (G2; Lanczos tridiagonality is `s = 2`),
`compressionBy` (Saad Prop 6.3 for arbitrary projectors, G3), `pow_apply_mem_subspace_iff_exists_monic`
(G4), `grade_le_of_apply_eq` (G5), FOM ⇔ `IsUnit (hessenbergSq …)` and the coordinate forms of
FOM/GMRES (G6), explicit Givens data with the spec-level identifications (G7), flag uniqueness (G8),
smoothing theorems (G9), three-term CG with the book's `γ_m, ρ_m` (G10; `CG.gamma`, `CG.rho`,
`iterate_succ_eq_three_term`, `residual_succ_eq_three_term`), the Hermitian-part constants
`ContinuousLinearMap.isCoerciveWith_iff_hermitianPart` (G11), `Numlib/Matrix/ToEuclideanLin.lean`
(G12), `CR.isMinResIterate_of_no_breakdown` for symmetric indefinite `A` and the book-exact GCR
lemma hypotheses (G14), projectors from bases `V (Wᴴ V)⁻¹ Wᴴ` (`LinearMap.obliqueProjectionOfBases`),
`Stationary.Splitting` constructors for SSOR/backward GS. Phase-2/3 gaps (G13): complex Chebyshev
on ellipses (Lemma 6.26, Thm 6.27, Cor 6.33), normal-matrix theory (Lemma 6.23, Thm 6.24 stated
without proof — left out), §6.6.2 (d)–(e), block Krylov.

From `plans/surface/FongSaunders.md`: `CG.alpha/beta`, `CR.alpha` exposed; `backwardError` with
`0 < β` (R5); termination converse; strict monotonicity forms are surface corollaries.

From `plans/surface/AtkinsonHan-Ch2-3.md`, `-Ch5.md`, `-Ch8-9.md`: the sharper Cor 2.3.3 bound,
(2.3.14) in the two-space theorem, Banach fixed point on closed invariant subsets
(`exists_unique_fixedPoint_of_mapsTo`, `dist_iterate_le_of_mapsTo`), the real derivative criterion
`lipschitzOnWith_of_hasFDerivWithinAt`, best approximation from closed subsets of finite-dimensional
subspaces and the pointwise Lebesgue lemma, `isBestApprox_iff_inner_le_zero` and
`IsBestApprox.dist_le_dist` (real Hilbert spaces), the compression trick
(`compression.aeval_apply_of_forall_pow_mem`, `compression.isSymmetricBoundedBy`,
`compression.energyNorm_apply`) that proves AH Thm 5.6.1 in Hilbert spaces without functional
calculus, `SesqForm` (`V →L⋆[𝕜] V →L[𝕜] 𝕜`) with `toOperator` an `abbrev` of
`InnerProductSpace.continuousLinearMapOfBilin`, `_real` specializations, the damped-iteration
estimate `ContinuousLinearMap.norm_sub_smul_apply_sq_le`, the two-space `SesqForm₂` with
`InfSupWith` in operator-norm form and `‖u‖ ≤ ‖ℓ‖/α`, `IsPetrovGalerkinSolution`, Babuška's
theorem with `finrank K = finrank L`, Strang's first lemma on one abstract normed space `W`,
`tendsto_infDist_of_monotone_dense`, the stiffness-matrix equivalence, the closed-operator version
of AH Thm 8.2.4 (`LinearPMap.isClosed_range_of_isClosed_of_le_norm`), Kato's lemma
(`ContinuousLinearMap.IsIdempotentElem.norm_one_sub_eq`, phase 2 consumer), Newton with
`ContinuousLinearMap.inverse` and the explicit `L/2` constant, Newton–Kantorovich. Out of scope:
the Banach closed range theorem (no unbounded Banach adjoints in Mathlib), Algorithm 2 (nonlinear
CG), everything needing Sobolev spaces.

### 12.6 Module map of the phase-1 skeleton

| Module | Content (plan section) |
|---|---|
| `Analysis/NormedRing/Inverse`, `…/CondNumber`, `Analysis/SpectralRadius` | 2.1.1–2.1.3 |
| `InnerProductSpace/Coercive`, `Energy`, `Compression`, `GramSchmidt`, `ObliqueProjection` | 2.1.4–2.1.7 (+ `IsSymmetricBoundedBy`, `compressionBy`, flag uniqueness, projectors from bases, Kato) |
| `Polynomial/ChebyshevMinimax` | 2.1.9 |
| `Matrix/Hessenberg`, `Complexify`, `ToEuclideanLin` | 2.1.10–2.1.11, G12 |
| `LinearSolve/Perturbation` | 2.2 |
| `LinearSolve/Stationary/Basic`, `Splitting`, `DiagDominant` | 2.3 |
| `LinearSolve/Projection/Basic`, `Optimality`, `OneDimensional` | 2.4 |
| `Krylov/Subspace`, `Arnoldi`, `Lanczos`, `Iterate`, `Hessenberg`, `Relations`, `CG`, `CR`, `Convergence/Polynomial`, `Convergence/CG`, `Monotonicity` | 3.1–3.11 |
| `Eigen/Perturbation` | 4.1 |
| `Approximation/BestApprox` | 5.1 |
| `Variational/Forms`, `LaxMilgram`, `Galerkin` | 5.2 |
| `Nonlinear/FixedPoint`, `Newton` | 5.3 |
