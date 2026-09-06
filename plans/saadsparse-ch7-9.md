<!--
The tracker plan (the TOML group files under `NumlibSurface/SaadSparse/Chapter0{7,8,9}/`) is the
authority on which declarations should exist, and once they exist the source is the authority on
what they say. What is worth reading here is the book alignment: which numbered result maps to
which declaration, how each book-specific definition relates to the backbone, and what was left
out and why.
-->

# Surface plan: Saad, Iterative Methods — Chapters 7, 8 and 9

Surface library `SaadSparse`, file sets `NumlibSurface/SaadSparse/Chapter07/*.lean`,
`Chapter08/*.lean`, `Chapter09/*.lean`. Companion to `saadsparse-ch1-4-5.md` and
`saadsparse-ch6.md`; the proposals this slice makes on other groups, and its coverage table, are
in `proposals/saad-ch7-9.md`.

These three chapters are the least theorem-dense of the book: **9 numbered results and 23
algorithms in 250 pages**, against Chapter 6's 33 numbered results. Almost everything in them is a
*derivation* — a rearrangement of a method already proved correct, into a form that is cheaper,
or transpose-free, or preconditioned. The plan therefore leans hard on §1.2 of `backbone.md`:
specifications are backbone, recurrences are surface definitions with equivalence lemmas, and a
recurrence with no theorem attached to it is a definition and nothing more.

## 1. Conventions

The conventions of `saadsparse-ch6.md` §1 carry over unchanged: `𝕜` with `[RCLike 𝕜]`,
`𝔼 := EuclideanSpace 𝕜 (Fin n)`, `op A := Matrix.toEuclideanLin A`, the book's `(x, y)` is
Mathlib's `inner 𝕜 y x`, algorithm vectors are `ℕ`-indexed and `0`-based (`v j` is the book's
`v_{j+1}`), and "Stop" is Lean's division by zero. `Chapter06/Common.lean` supplies `r₀`, `β`,
`v₁`, `e₁`, `mEff`; `Chapter07/Section01.lean` adds `w₁`, the dual starting vector.

Two conventions specific to these chapters:

* **Breakdown is a hypothesis, not a case.** Algorithm 7.1 stops when `(v̂_{j+1}, ŵ_{j+1}) = 0`, and
  every statement of §7.1–7.3 carries `∀ j < m, (v̂_{j+1}, ŵ_{j+1}) ≠ 0`, exactly as the book
  does. The recursion still returns `0` after a breakdown, so the definitions are total.
* **Normalization.** Algorithm 7.1 scales so that `(v_j, w_j) = 1`; from (7.18) on the book
  switches, "without loss of generality", to `‖v_j‖₂ = 1`. Both are admissible by (7.1), and the
  switch is a hypothesis `∀ j, ‖v_j‖₂ = 1` on the statements after (7.18) rather than a second
  definition.

## 2. File layout

| File | Book | Contents |
|---|---|---|
| `Chapter07/Section01.lean` | §7.1 | Algorithm 7.1, `T`, `T̄`, Proposition 7.1, (7.3)–(7.5), the Hessenberg relation, P-7.2, P-7.6 |
| `Chapter07/Section02.lean` | §7.2 | Algorithm 7.2, the Petrov–Galerkin identification, (7.9) |
| `Chapter07/Section03.lean` | §7.3 | Algorithm 7.3 (BCG), Proposition 7.2, the `LDU` derivation (7.10)–(7.12); Algorithm 7.4 (QMR), (7.15)–(7.31), Propositions 7.3, 7.5, Theorem 7.4, Algorithm 7.5 |
| `Chapter07/Section04.lean` | §7.4 | the BCG polynomials `φ_j`, `π_j`; Algorithms 7.6 (CGS), 7.7 (BICGSTAB), 7.8 (TFQMR) with their polynomial identifications and (7.70), (7.76), (7.83) |
| `Chapter08/Section01.lean` | §8.1 | (8.1)–(8.8) |
| `Chapter08/Section02.lean` | §8.2 | Algorithms 8.1–8.3 and their identification with the projection processes of §5.3–5.4; (8.22)–(8.27), P-8.8 |
| `Chapter08/Section03.lean` | §8.3 | Algorithms 8.4 (CGNR), 8.5 (CGNE) and the two optimality properties |
| `Chapter08/Section04.lean` | §8.4 | (8.28)–(8.35), Algorithm 8.6 (Uzawa), Corollary 8.1, Algorithm 8.7, Example 8.2, P-8.7 |
| `Chapter09/Section01.lean` | §9.1 | (9.1)–(9.3), P-9.1, P-9.10 |
| `Chapter09/Section02.lean` | §9.2 | Algorithms 9.1–9.3, the three self-adjointness facts, the equality of the three CG variants, (9.5)–(9.8), P-9.2, P-9.3, P-9.6 |
| `Chapter09/Section03.lean` | §9.3 | Algorithms 9.4, 9.5, split preconditioning, (9.17)–(9.21), Proposition 9.1, the `M`-inner-product GMRES of P-9.13 |
| `Chapter09/Section04.lean` | §9.4 | Algorithm 9.6 (FGMRES), (9.22)–(9.26), Propositions 9.2, 9.3, flexible DQGMRES |
| `Chapter09/Section05.lean` | §9.5 | Algorithms 9.7, 9.8 |
| `Chapter09/Section06.lean` | §9.6 | the CGW splitting, (9.29), the algorithm and its Galerkin property |

Import order: `Chapter07/Section01 → 02 → 03 → 04`; `Chapter08/Section01 → 02, 03 → 04`;
`Chapter09/Section01 → 02 → 03 → 04, 05, 06`. `Chapter07/Section03` imports `Chapter06/Section05`
(the QGMRES layer), `Chapter08/Section02` imports `Chapter05/Section03` and `Chapter05/Section04`
(the one-dimensional and additive projection processes) and `Chapter04/Section02` (Example 4.1),
`Chapter09/Section05` imports `Chapter08/Section03`.

## 3. The four structural claims

Everything else in these files is bookkeeping around four claims.

### 3.1 QMR is QGMRES on the two-sided Lanczos basis (§7.3.2)

The book says so ("just as in GMRES, except that the Arnoldi process is replaced by the Lanczos
process", and "it is easy to adapt the DQGMRES algorithm"), and the surface is built to make it
literally true. `Chapter06/Section05.lean` already states `qgmres`, `quasiResidualNorm`, `z`, `ζ`,
`equation_6_50`, `equation_6_51`, `equation_6_53`–`equation_6_55` and `problem_6_25` for an
*arbitrary* pair `(u, h)` with `Krylov.HessenbergRelation (op A) u h`, "because that is precisely
the book's reason why (6.41) and its consequences survive the loss of orthogonality". Chapter 7
supplies the instance `u := bilanczosV`, `h := bilanczosCoeff` through
`bilanczos_hessenbergRelation`, and §7.3.2 is then §6.5.6 read again.

The one thing Chapter 6 does not have is Theorem 6.11, and Theorem 7.4 is its twin. Both are
`Krylov.IsQuasiMinResIterate.norm_residual_le_mul` of the new `Numlib/Krylov/QuasiMinRes`:
`‖r^Q‖ ≤ (C/c)‖r^G‖` whenever `c‖y‖₂ ≤ ‖V y‖₂ ≤ C‖y‖₂`. The proof is
`‖V t^Q‖ ≤ C‖t^Q‖ ≤ C‖t^G‖ ≤ (C/c)‖V t^G‖`, four inequalities, the middle one being minimality of
the quasi-residual. `plans/saadsparse-ch6.md` §R31 estimated 60 lines for a Gram–Schmidt
factorization of `V_{m+1}`; none is needed, and the full-rank hypothesis the book assumes in
Theorem 6.11 is subsumed in `0 < c`.

### 3.2 The transpose-free methods are polynomial identities (§7.4)

CGS, BICGSTAB and TFQMR have no numbered result in the book. What they have — and what the surface
states — is that each computes a *named polynomial* in `A` applied to `r₀`:

| method | residual | direction |
|---|---|---|
| BCG | `φ_j(A) r₀` | `π_j(A) r₀` |
| CGS | `φ_j(A)² r₀` | `π_j(A)² r₀` |
| BICGSTAB | `ψ_j(A) φ_j(A) r₀` | `ψ_j(A) π_j(A) r₀` |

with `φ_{j+1} = φ_j - α_j t π_j`, `π_{j+1} = φ_{j+1} + β_j π_j` (7.35)–(7.36) and
`ψ_{j+1} = (1 - ω_j t) ψ_j` (7.47), the coefficients being those of the BCG run. Everything else in
§7.4 — (7.37)–(7.45), (7.48)–(7.54) — is the algebra of moving these polynomials across the inner
product, which is why the definitions of `φ`, `π`, `ψ` are the load-bearing declarations. The
`ω_j` of (7.55) is a one-dimensional minimal-residual step (`Projection.minResStep`), so the
"stabilization" is steepest descent on the residual, and that is stated.

TFQMR is different in kind: (7.70) `A U_m = R_{m+1} B̄_m` is a Hessenberg relation *between two
families*, the iterate basis `u` and the residual basis `r`. `Krylov.HessenbergRelation` cannot
state it; `Krylov.HessenbergRelation₂` can, and then (7.76) says the CGS iterates are its FOM
iterates, TFQMR is its quasi-minimal-residual iterate, and (7.83) `‖b - A x_m‖ ≤ √(m+1) τ_m` is
`Krylov.IsQuasiMinResIterate.norm_residual_le` with `C = √(m+1)`. The hard declaration of the
chapter is `tfqmr_isQuasiMinResIterate`: the `θ, c, τ, η, d` recurrence of Algorithm 7.8 solves the
least-squares problem. It is DQGMRES with `k = 1` on a bidiagonal matrix, so
`SaadSparse.Chapter06.dqgmres_eq_qgmres` does the work once (7.70) is available.

### 3.3 Chapter 8 is recognition, not construction

The chapter introduces no method that is not an old method on a new system.

* §8.2 row projection = §5.3–5.4 projection processes with `K_i = span {e_i}`. One NR-SOR
  relaxation is `SaadSparse.Chapter05.mrStep` along `e_i`; one NE-SOR (Kaczmarz) relaxation is
  `Projection.step1` with `K = span {Aᴴ e_i}`, `L = span {e_i}`; the sweeps are
  `SaadSparse.Chapter05.multiplicativeSweep`; Cimmino is `SaadSparse.Chapter05.additiveStep` for
  `AᴴA x = Aᴴb`. With normalized columns Cimmino is Richardson on the normal equations, so
  (8.22) is `SaadSparse.Chapter04.example_4_1_spectralRadius`. The block version (8.26)–(8.27) is the
  same with `dim K_i > 1` and a least-squares subproblem.
* §8.3 CGNR/CGNE = `Numlib/Krylov/NormalEquations`, whose two theorems are exactly Saad's two
  optimality properties. The section's own contribution is the last observation: both draw from
  `x₀ + 𝒦_m(AᴴA, Aᴴr₀)`, and `Aᴴ 𝒦_m(A Aᴴ, r₀)` is that same space.
* §8.4 Uzawa = Richardson on the Schur complement `S = Bᴴ A⁻¹ B`. Corollary 8.1, the chapter's
  only numbered result, is `Stationary.tendsto_of_spectralRadius_lt_one` once `S` is known to be
  symmetric positive definite; that lemma is proposed for
  `Numlib/Analysis/InnerProductSpace/Coercive`. The KKT statement (8.28)–(8.30) is a two-line
  computation, `f(x') - f(x) = ½(A(x'-x), x'-x) ≥ 0` for admissible `x'`.

### 3.4 Chapter 9 is transport (§9.2–9.5), except §9.6

`Numlib/Krylov/Preconditioned` states the transport: PCG is `CG.iterate` for `M⁻¹A` in
`WithEnergy M`, so its Galerkin property and its Chebyshev bound with `κ(M⁻¹A)` are inherited.
What the surface adds is the book's three "the iterates are identical" claims — Algorithm 9.1 =
Algorithm 9.2 = right-preconditioned CG in the `M⁻¹` inner product — each a change of variables,
and Proposition 9.1, which says that left and right preconditioned GMRES search the *same* affine
space (through the commutation (9.18) `s(M⁻¹A) M⁻¹ r = M⁻¹ s(A M⁻¹) r`) while minimizing
`‖M⁻¹ r‖₂` and `‖r‖₂` respectively.

§9.6 is the exception. `M = (A + Aᴴ)/2`, `N = -(A - Aᴴ)/2`, and `M⁻¹A = 1 - M⁻¹N` with `M⁻¹N`
*skew*-adjoint in the `M`-inner product. The Arnoldi coefficient array of such an operator is
tridiagonal — `Arnoldi.coeff_eq_zero_of_adjoint_mem` (Saad Prop 6.22, the Faber–Manteuffel band
structure) with `s = 2`, since the adjoint `2 - M⁻¹A` sends `v` into `span {v, M⁻¹A v}` — with
`h_ij + conj h_ji = 2 δ_ij`, which is (9.29). Both facts were prototyped and each is five lines.
CGW is then the Galerkin (FOM) method for `M⁻¹A` in the `M`-inner product with a three-term
recurrence; it has **no** minimization property, because `M⁻¹A` is not `M`-self-adjoint, and the
surface claims none.

## 4. Deferred and not planned

Full list with reasons in `proposals/saad-ch7-9.md` §3. The four that matter:

* **Look-ahead Lanczos (§7.1.2)**, with the indefinite bilinear form (7.7), the Hankel moment
  matrix and its `LU` factorization. The book proves nothing here; it describes a family of
  implementations and says where the pivots vanish. Nothing to be faithful to.
* **The spectrum of `[[0, A], [Aᴴ, 0]]` (§8.1) and P-8.4.** Needs a singular value decomposition.
  Mathlib has `LinearMap.singularValues` but no factorization, and
  `Numlib/LinearAlgebra/Matrix/SVD` is a phase-3 group with no nodes proved.
* **P-8.6**, CG on the singular consistent system `P A P x = P b`. This is Choi's material and
  belongs in `Numlib/Krylov/Singular`; it should be planned there, with the Saad problem as a
  consumer.
* **P-8.9**, inexact Uzawa. Needs "if `x_{k+1} = T x_k + e_k` with `‖T‖ < 1` and `‖e_k‖ → 0` then
  `x_k` converges", which `Numlib/Nonlinear/FixedPoint` does not have and which no other source in
  the corpus asks for. One node would do it if a second consumer appears; it is cheap but it is
  not in the corpus's interest yet.

Also not planned, as arithmetic rather than mathematics: Eisenstat's operation counts (§9.2.2,
Example 9.1, P-9.7–P-9.9), the six preconditioned normal-equation variants of P-9.4 and P-9.5, and
the numerical tables 7.1–7.3 and 8.1.
