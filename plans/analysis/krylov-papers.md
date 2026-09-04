# Krylov subspace methods: mathematical content of three sources

Sources (pdftotext output, formulas partly garbled; reconstructions from the well-known
originals are marked "[uncertain]" where the OCR did not allow a verbatim reading):

* **(A)** D. Fong, M. Saunders, *CG versus MINRES: an empirical comparison*, SQU J. Sci. 17 (2012) 44-62
  (Report SOL 2011-2R).
* **(B)** S.-C. Choi, *Iterative methods for singular linear equations and least-squares problems*,
  PhD thesis, Stanford 2006 (MINRES-QLP).
* **(C)** G. Meurant, Z. Strakos, *The Lanczos and conjugate gradient algorithms in finite precision
  arithmetic*, Acta Numerica 16 (2007) 1-71.

Conventions in this file. `(u,v)` is the inner product (real symmetric case unless stated;
`^T` may be read as adjoint `^H`), `||.||` the induced norm, `||u||_A^2 = (u, A u)` for `A` positive,
`K_k(A,b) = span{b, Ab, ..., A^{k-1} b}`, `e_j` the `j`-th unit vector, `T_k` the `k x k`
symmetric tridiagonal Lanczos matrix, `T̄_k` (Choi's notation) the `(k+1) x k` matrix
`[T_k ; β_{k+1} e_k^T]`. For every numbered result we give: statement with all hypotheses;
the structure the proof uses; a proof sketch.

---------------------------------------------------------------------------------------------------

# Part A. Fong & Saunders, "CG versus MINRES" (complete analysis)

## A.0 Setting and notation (§1, §1.1)

* Standing assumption for §§2-3: `A x = b` real, `A` symmetric positive definite (spd) `n x n`,
  unique solution `x`; `x_0 = 0`; `r_k = b - A x_k`; `||v||` = 2-norm, `||A||` = Frobenius norm;
  `A ≻ 0` means spd.
* Lanczos with starting vector `b` produces `V_k = [v_1 ... v_k]` (theoretically orthonormal,
  spanning `K_k(A,b)`) and a `(k+1) x k` "Hessenberg tridiagonal" matrix (printed `T_k` in the paper;
  the underbar distinguishing it from the square matrix was lost by OCR; it is Choi's `T̄_k`) with
  `A V_k = V_{k+1} T̄_k`, `k = 1, 2, ...`, and `A V_ℓ = V_ℓ T_ℓ` for some `ℓ ≤ n`, `T_ℓ` square
  tridiagonal. Approximate solutions are `x_k = V_k y_k`.
* "As shown in [Paige-Saunders 1975], CG, MINRES, SYMMLQ are obtained by choosing `y_k`
  appropriately. CG is well defined if `A` is spd; MINRES and SYMMLQ are stable for any symmetric
  nonsingular `A`." SYMMLQ forms `x_{k+1} = V_{k+1} y_{k+1} ∈ K_{k+1}` while CG/MINRES form
  `x_k ∈ K_k` (citing Choi [2]).
* Termination index `ℓ`: the step at which the Lanczos process terminates (`β_{ℓ+1} = 0`); the same
  `ℓ` at which CR/CG terminate with `r_ℓ = 0` (Note after Table 2.1).

## A.1 Minimization properties (§2)

**Principle (§2, citing Freund-Golub-Nachtigal [9]).** Krylov solvers minimize some convex
function over the expanding subspaces `K_k(A,b)` so that `x_k = V_k y_k` improves as `k → ℓ`.

**CG characterization (§2.1).** For `A ≻ 0`, `φ(x) = ½ x^T A x - b^T x` is bounded below with
unique minimizer `A^{-1} b`, and
`x_k^C = V_k y_k^C`, `y_k^C = argmin_y φ(V_k y)`.
Since `2 φ(x_k) = x_k^T A x_k - 2 x_k^T A x = ||x - x_k||_A^2 - ||x||_A^2`, this is equivalent to
`x_k^C = argmin_{u ∈ K_k(A,b)} ||x - u||_A` ("energy norm of the error").
*Structure:* inner product, positivity of `A`, `b = A x`. No finite dimension needed for the
equivalence itself.

**MINRES characterization (§2.2, eq. (2.1)).** For nonsingular (possibly indefinite) symmetric `A`
`x_k^M = V_k y_k^M`, `y_k^M = argmin_y ||b - A V_k y||`, i.e. MINRES minimizes `||r_k||` over
`K_k(A,b)`. This was also the aim of Stiefel's Conjugate Residual method CR (1955) for spd `A`
(and Luenberger's 1969/1970 extensions to indefinite `A`). Hence **CR and MINRES generate the same
iterates on spd systems** (uniqueness of the minimizer of a strictly convex function over a
subspace once `A` is injective on `K_k`). The paper uses this to transfer CR results to MINRES.

## A.2 The algorithms CG and CR (Table 2.1)

CG (no iteration index): `x = 0, r = b, ρ = ||r||^2, p = r`; repeat: `q = A p`; `α = ρ / p^T q`;
`x ← x + α p`; `r ← r - α q`; `ρ̄ = ρ, ρ = r^T r`; `β = ρ / ρ̄`; `p ← r + β p`.

CR (no index): `x = 0, r = b, s = A r, ρ = r^T s, p = r, q = s`; repeat: (`q = A p`, not computed
as such); `α = ρ / ||q||^2`; `x ← x + α p`; `r ← r - α q`; `s = A r`; `ρ̄ = ρ, ρ = r^T s`;
`β = ρ / ρ̄`; `p ← r + β p`; `q ← s + β q`. Termination when `r = 0` (`ρ = β = 0`).

CR with indices (used in the proofs):
```
x_0 = 0, r_0 = b, s_0 = A r_0, ρ_0 = r_0^T s_0, p_0 = r_0, q_0 = s_0
for k = 1, 2, ...:
  (q_{k-1} = A p_{k-1})
  α_k = ρ_{k-1} / ||q_{k-1}||^2
  x_k = x_{k-1} + α_k p_{k-1}
  r_k = r_{k-1} - α_k q_{k-1}
  s_k = A r_k
  ρ_k = r_k^T s_k
  β_k = ρ_k / ρ_{k-1}
  p_k = r_k + β_k p_{k-1}
  q_k = s_k + β_k q_{k-1}
```
Termination at `k = ℓ ≤ n` with `r_ℓ = 0` (then `ρ_ℓ = β_ℓ = 0`, `r_ℓ = s_ℓ = p_ℓ = q_ℓ = 0`).
Invariants: `q_k = A p_k`, `s_k = A r_k`, `x_k ∈ K_k`, `p_k, r_k ∈ K_{k+1}`, `q_k ∈ A K_{k+1}`.

## A.3 Theorems of §2

**Theorem 2.1 (CR orthogonality; proof: Luenberger 1970, Thm 1).** For Algorithm CR (hypotheses of
§2.3: `A` spd; the relations themselves hold for symmetric `A` as long as the algorithm is defined):
(a) `q_i^T q_j = 0` for `i ≠ j` (i.e. `(A p_i, A p_j) = 0`: the directions are `A^2`-conjugate);
(b) `r_i^T q_j = 0` for `i ≥ j + 1` (i.e. `r_i ⊥ A p_j` for `j < i`: `r_i ⊥ A K_i`, the
minimal-residual/Petrov-Galerkin condition).
*Structure:* inner product + symmetry of `A` + induction; equivalent to `r_i^T A r_j = 0 (i ≠ j)`.
*Sketch:* induction on the recurrences using symmetry: `r_i^T q_j = r_i^T A p_j`; standard CR theory.

**Theorem 2.2 (sign properties of CR; new proof in the paper).** For Algorithm CR with `A` spd
(inequalities strict until `i = ℓ`, where `r_ℓ = 0`):
(a) `α_i ≥ 0` (strictly `> 0` for `i ≤ ℓ`, since `ρ_{i-1} = r_{i-1}^T A r_{i-1} > 0`),
(b) `β_i ≥ 0` (`> 0` before termination),
(c) `p_i^T q_j ≥ 0` for all `i, j` (with `p_i^T q_i = p_i^T A p_i > 0`),
(d) `p_i^T p_j ≥ 0` for all `i, j < ℓ`,
(e) `x_i^T p_j ≥ 0`,
(f) `r_i^T p_j ≥ 0`.
[Whether the printed statement uses `>` or `≥` is not recoverable from the OCR; the proofs give
`≥` with strictness for the "diagonal" cases.]
*Structure:* (a),(b): positivity of `A` only. (c): Thm 2.1(b), induction on `|i - j|`.
(d): **uses finite termination**: at termination `P := span{p_0..p_{ℓ-1}} = K_ℓ(A,b)`,
`Q := span{q_0..q_{ℓ-1}} = span{Ab, ..., A^ℓ b}`; `x ∈ P`, `r_ℓ = 0 ⇒ b = A x ∈ Q`, so `P ⊆ Q`;
by Thm 2.1(a) `{q_i/||q_i||}` is an orthonormal basis of `Q`; expanding
`p_i = Σ_k (p_i^T q_k / q_k^T q_k) q_k` with nonnegative coordinates by (c) gives `p_i^T p_j ≥ 0`.
(e): `x_i = Σ_{k=1}^i α_k p_{k-1}` (`x_0 = 0`), then (a),(d).
(f): `r_i = Σ_{k=i+1}^{ℓ} α_k q_{k-1}` (telescoping to `r_ℓ = 0`), then (a),(c).
*Sketch of (c):* Case `i = j`: `p_i^T A p_i > 0`. Case `i - j = k > 0`:
`p_i^T q_{i-k} = r_i^T q_{i-k} + β_i p_{i-1}^T q_{i-k} = β_i p_{i-1}^T q_{i-k} ≥ 0` by Thm 2.1(b), (b)
and induction. Case `j - i = k > 0`: `p_i^T q_{i+k} = p_i^T A(r_{i+k} + β_{i+k} p_{i+k-1})
= q_i^T r_{i+k} + β_{i+k} p_i^T q_{i+k-1} = β_{i+k} p_i^T q_{i+k-1} ≥ 0`.

**Theorem 2.3 (main result: solution norms increase).** For CR (hence MINRES) on an spd system,
`||x_k||` increases monotonically (`||x_i|| ≥ ||x_{i-1}||`). The analogous CG result is
Steihaug 1983.
*Sketch:* `||x_i||^2 - ||x_{i-1}||^2 = 2 α_i x_{i-1}^T p_{i-1} + α_i^2 p_{i-1}^T p_{i-1} ≥ 0` by
Thm 2.2 (a),(d),(e). *Structure:* inner product + Thm 2.2 (hence finite termination through (d)).

**Theorem 2.4 (Euclidean error decreases).** For CR (hence MINRES) on spd `A x = b`, `||x - x_k||`
decreases monotonically. (Known for CG [Hestenes-Stiefel]; for CR a consequence of
[HS, Thm 7:5], whose second half `||x - x_{k-1}^C|| > ||x - x_k^M||` "rarely holds in machine
arithmetic"; the paper gives a proof independent of CG.)
*Sketch:* with `x_ℓ = x`: `x = x_k + α_{k+1} p_k + ... + α_ℓ p_{ℓ-1}
= x_{k-1} + α_k p_{k-1} + α_{k+1} p_k + ... ` (eqs (2.3)-(2.4); the paper's printed indices on the
last term are off by one), hence
`||x - x_{k-1}||^2 - ||x - x_k||^2 = 2 α_k p_{k-1}^T (α_{k+1} p_k + ... ) + α_k^2 ||p_{k-1}||^2 ≥ 0`
by Thm 2.2 (a),(d). *Structure:* finite termination (`x_ℓ = x`) + Thm 2.2.

**Theorem 2.5 (energy-norm error strictly decreases).** For CR (hence MINRES) on spd `A x = b`,
`||x - x_k||_A` is strictly decreasing. (For CG this holds by definition; for CR it is
[HS, Thm 7:4].)
*Sketch:* `||x - x_{k-1}||_A^2 - ||x - x_k||_A^2 = 2 α_k p_{k-1}^T A(α_{k+1} p_k + ...) + α_k^2 p_{k-1}^T A p_{k-1}
= 2 α_k q_{k-1}^T(α_{k+1} p_k + ...) + α_k^2 q_{k-1}^T p_{k-1} > 0` by Thm 2.2 (a),(c) and
`q_{k-1}^T p_{k-1} > 0`. *Structure:* as Thm 2.4.

## A.4 Backward error analysis (§3)

**Definition (acceptable solution, after Titley-Peloquin [25]), eq. (3.1).** For consistent
`A x = b`, `x_k` is *acceptable* iff there exist `E, f` with
`(A + E) x_k = b + f`, `||E|| / ||A|| ≤ α`, `||f|| / ||b|| ≤ β`, tolerances `α, β ≥ 0`
reflecting data accuracy.

**Definition (normwise relative backward error, NRBE).** Let
`min_{ξ,E,f} ξ  s.t. (A+E) x_k = b + f, ||E||/||A|| ≤ ξ α, ||f||/||b|| ≤ ξ β`
have optimum `ξ_k, E_k, f_k` (functions of `x_k, α, β`). Then `x_k` is acceptable iff `ξ_k ≤ 1`;
`ξ_k` is the NRBE of `x_k`.

**Formulas (3.2)-(3.3) (from [25]; special cases in Higham [12, p.12] (`β = 0`) and
[12, §7.1, p.336] (Rigal-Gaches, `α = β`)).** With `r_k = b - A x_k`:
```
ξ_k = ||r_k|| / (α ||A|| ||x_k|| + β ||b||),
ω_k = β ||b|| / (α ||A|| ||x_k|| + β ||b||),
E_k = ((1 - ω_k) / ||x_k||^2) r_k x_k^T,      f_k = -ω_k r_k .
```
(Check: `(A + E_k) x_k = b - r_k + (1-ω_k) r_k = b - ω_k r_k = b + f_k`.)
*Structure:* inner product norms only (`E_k` is rank one, so Frobenius = 2-norm).

**Stopping rule (3.4), §3.1.** `ξ_k ≤ 1` ⇔ `||r_k|| ≤ α ||A|| ||x_k|| + β ||b||`
(= LSQR rule S1 [19, p.54] for consistent systems).

**Eqs (3.5)-(3.6), §3.2.** `||E_k|| = (1-ω_k)||r_k||/||x_k|| = α||A|| ||r_k|| /(α||A|| ||x_k|| + β||b||)`,
`||f_k|| = ω_k ||r_k|| = β||b|| ||r_k|| /(α||A|| ||x_k|| + β||b||)`.
Since `||x_k||` increases for CG and MINRES, `ω_k` decreases for both.

**Theorem 3.1 (monotone backward errors).** Suppose `α > 0`, `β > 0`. For CR and MINRES (but not
CG) on spd `A x = b`, `||E_k||/||A||` and `||f_k||/||b||` decrease monotonically.
*Sketch:* (3.5)-(3.6) with `||x_k||` increasing (Thm 2.3) and `||r_k||` decreasing (minimal residual
over nested subspaces); CG's `||r_k||` is not monotone. *Structure:* Thm 2.3 + nestedness.
*Corollary used in §4.1:* with `β = 0`, `||E_k|| = ||r_k||/||x_k||` decreases for CR/MINRES.

## A.5 Numerical section, §4 (mathematical content only)

* §4: test set from UF sparse collection; diagonal preconditioning `A ← D A D`, `b ← D b/||Db||`,
  `D = diag(1/sqrt(diag A))`; stopping `||r_k|| ≤ 10^{-8} ||b||` (rule (3.4), `α = 0`, `β = 10^{-8}`).
* **Eq. (4.1) (Greenbaum [10, Lemma 5.4.1], Titley-Peloquin [26]):**
  `||r_k^C|| = ||r_k^M|| / sqrt(1 - ||r_k^M||^2 / ||r_{k-1}^M||^2)`.
  Consequence: if MINRES stalls at step `k` (`||r_k^M|| ≈ ||r_{k-1}^M||`) then `||r_k^C|| ≫ ||r_k^M||`;
  if MINRES drops a lot, `||r_k^C|| ≈ ||r_k^M||`.
  *Structure:* holds whenever both iterates exist (CG needs `T_k` nonsingular); standard
  Galerkin-vs-minimal-residual relation (`||r_k^M|| = ||r_{k-1}^M|| |s_k|`, `||r_k^C|| = ||r_k^M||/|c_k|`
  with Givens cosines/sines of the QR of `T̄_k`; see Choi Prop 2.16(3)).
* **Lag argument (§4.1.1):** with `α = 0` in (3.4) both methods stop when `||r_k|| ≤ β ||b||`; if this
  happens at `ℓ`, `Π_{k=1}^{ℓ} ||r_k||/||r_{k-1}|| = ||r_ℓ||/||b|| ≤ β`, so on average
  `||r_k^M||/||r_{k-1}^M||` is closer to 1 when `ℓ` is large ⇒ by (4.1) CG lags MINRES more for
  large problems.
* Empirically (Figs 4.2-4.5): MINRES backward error 1-2 orders of magnitude ahead of CG; CG better in
  both error norms; `||x_k||` rises to `||x||` faster for CG.

## A.6 Indefinite systems and trust regions (§4.2)

* **Steihaug 1983 [21] (quoted, black box):** when CG is applied to symmetric (possibly indefinite)
  `A x = b` with `x_0 = 0`, `||x_1||, ..., ||x_k||` are strictly increasing as long as
  `p_j^T A p_j > 0` for all `1 ≤ j ≤ k` (notation of Table 2.1). Key to Steihaug's trust-region
  CG (see also Conn-Gould-Toint [4]).
* **Remark (from the proof of Thm 2.2):** the same holds for CR and MINRES as long as
  `p_j^T A p_j > 0` and `r_j^T A r_j > 0` for `1 ≤ j ≤ k` (these are exactly what make `α_j, β_j > 0`).
* **Counterexample (4.2):** for the nonsingular indefinite system
  `A = [[2,1,1],[1,0,1],[1,1,2]]`, `b = (0,1,1)^T` [uncertain ordering of `b`], MINRES gives
  non-monotone `||x_k||` and non-monotone `||r_k||/||x_k||` (Fig 4.6).
* **MINRES-QLP viewpoint (Choi-Paige-Saunders [3]):** both MINRES and MINRES-QLP compute
  `x_k^M = V_k y_k^M`, `y_k^M = argmin_{y ∈ R^k} ||T̄_k y - β_1 e_1||` (and possibly
  `T_ℓ y_ℓ^M = β_1 e_1` at the end). When `A` is nonsingular or `A x = b` is consistent, `y_k^M` is
  unique for each `k ≤ ℓ` and both methods produce the same iterates by different numerics. Both
  compute expanding QR factorizations `Q_k [T̄_k  β_1 e_1] = [[R_k, t_k],[0, φ_k]]` (`R_k` upper
  tridiagonal); MINRES-QLP also computes `R_k P_k = L_k` (`L_k` lower tridiagonal), sets
  `W_k = V_k P_k`, `L_k u_k = t_k`, `x_k^M = W_k u_k`. The first `k-3` columns of `W_k` and first `k-3`
  entries of `u_k` are unchanged from step `k-1`; since `W_k` has orthonormal columns
  `||x_k^M|| = ||u_k||` with the first `k-2` entries of `u_k` never altered later. Hence the norm
  estimate ([3, §6.5])
  `χ^2 ← χ^2 + μ̂_{k-2}^2`,  `||x_k^M||^2 = χ^2 + μ̃_{k-1}^2 + μ̄_k^2`,
  where `χ^2` increases monotonically and the last two terms are of unpredictable size, so
  `||x_k^M||` is "approximately monotone" even for indefinite `A` (empirically 83-90% of steps
  increase `||x_k||`, 91-98% decrease `||r_k||/||x_k||`, Figs 4.7-4.8).

## A.7 Summary table (Table 5.1) and conclusions (§5)

Properties on an spd system (increasing ↑ / decreasing ↓):

| quantity | CG | MINRES (= CR) |
|---|---|---|
| `||x_k||` ↑ | Steihaug [21, Thm 2.1] | Thm 2.3 |
| `||x - x_k||` ↓ | HS [11, Thm 6:3] | Thm 2.4, HS [11, Thm 7:5] |
| `||x - x_k||_A` ↓ | HS [11, Thm 4:3] (by definition) | Thm 2.5, HS [11, Thm 7:4] |
| `||r_k||` ↓ | not monotone | Paige-Saunders [18], HS [11, Thm 7:2] |
| `||r_k|| / ||x_k||` ↓ | not monotone | Thm 3.1 |

(The row/column association of HS theorem numbers is reconstructed from the text of §2 and from
Meurant-Strakos Thm 11/12, which identify HS 6:1 = A-norm identity and HS 6:3 = Euclidean error
decrease; HS §7 treats the conjugate residual variant.)

Table 5.2 (from Fong's thesis [7]): LSQR and LSMR (= CG and MINRES on the normal equations
`A^T A x = A^T b`) have the analogous properties: `||x_k||` ↑, `||x - x_k||` ↓, `||r - r_k||` ↓,
`||A^T r_k||` (↓ for LSMR only), `||r_k||` ↓ (both), `(||A^T r_k||/||r_k||)_{LSQR} ≥ (...)_{LSMR}`,
and both converge to the minimum-norm `x` for singular systems.

---------------------------------------------------------------------------------------------------

# Part B. Choi, "Iterative methods for singular linear equations and least-squares problems"

## B.1 Chapter 1 (summary)

* Motivation: PageRank / inverse iteration `(A - I) x_k = v_{k-1}` with intentionally singular
  matrix; null vectors via least squares. Key observation (§1.1.2): for `min ||A x - b||` the optimal
  residual satisfies `A^T r = 0`, so `r` is a null vector of `A^T`; to get a null vector of `A`, solve
  `min_y ||A^T y - c||` for arbitrary `c` and take `s = c - A^T y` (`A s = 0`). Converges sooner than
  forcing an exploding solution.
* Symmetric case (§1.1.3): natural solvers are SYMMLQ and MINRES; for singular `A`, MINRES since it
  allows `r ≠ 0`; the optimal residual satisfies `A r = 0`. Experimental/theoretical finding: MINRES
  returns the minimum-length solution when `b ∈ R(A)`, but NOT when the optimal `r ≠ 0`. This
  motivates MINRES-QLP. (Ipsen-Meyer: general Krylov methods (e.g. GMRES) on singular compatible
  systems yield only the Drazin-inverse solution; on inconsistent systems no solution.)
* **Problem statement (§1.2.1), eqs (1.6)-(1.9).** `A x = b`, `A ∈ R^{n x n}` symmetric.
  *Consistent/compatible* iff `b ∈ R(A)`. If `A` nonsingular: unique solution. If `A` singular and
  compatible: infinitely many solutions; select the **minimum-length solution**. If incompatible:
  solve the singular symmetric least-squares problem and select the minimum-length solution:
  `min ||x||_2  s.t.  x ∈ argmin ||A x - b||_2`   (1.8).
  The minimum-length solution of (1.6) or (1.7) is unique and is the **pseudoinverse solution**
  `x = (A^T A)^† A^T b = (A^2)^† A b = A^† b`.
* Shifts `A - σ I` handled inside the Lanczos process. Notation §1.2.4: `K_k(A,b)`, `A^†`, `R(A)`,
  `N(A)`, `κ(A)`, `A ≻ 0`, `A x ≈ b` shorthand for `min ||A x - b||`; "most results extend directly to
  complex Hermitian matrices" (superscript `H`).

## B.2 Chapter 2: Lanczos process and CG / SYMMLQ / MINRES

Standing assumptions of ch. 2: `A ∈ R^{n x n}` symmetric, `b ∈ R^n`, `A ≠ 0`, `b ≠ 0`; extends to
Hermitian `A`, complex `b` (with `α_k` real).

### B.2.1 The Lanczos process (§2.1)

Definitions (2.1)-(2.4):
```
v_0 = 0,  β_1 v_1 = b  (β_1 = ||b|| normalizes v_1),
p_k = A v_k,  α_k = v_k^T p_k,
β_{k+1} v_{k+1} = p_k - α_k v_k - β_k v_{k-1}   (β_{k+1} ≥ 0 normalizes v_{k+1}).
A V_k = V_{k+1} T̄_k,   V_k = [v_1 ... v_k],                              (2.3)
T̄_k = [T_k ; β_{k+1} e_k^T]  ((k+1) x k),  T_k = tridiag(β_i, α_i, β_{i+1}) (k x k),
T_k = [[T_{k-1}, β_k e_{k-1}],[β_k e_{k-1}^T, α_k]].
In exact arithmetic V_k has orthonormal columns; the process stops when β_{k+1} = 0 (k ≤ n),
and then A V_k = V_k T_k.                                                  (2.4)
```
Shifted version replaces `A` by `A - σ I` (LanczosStep(A, v_k, v_{k-1}, β_k, σ), Table 2.1;
Tridiag(A, b, σ, maxit), Table 2.2). Cost per step: one product `A v`, 2 inner products, 3 saxpy-like
operations. **The Lanczos process stops in at most `min{rank(A)+1, n}` iterations**; sooner when
`A` has clustered eigenvalues or `b` has components along few eigenvectors.

**Definition 2.1 (Krylov subspace).** For square `A ∈ R^{n x n}` and `b`, `k ≥ 1`:
`K_k(A,b) := span{b, Ab, ..., A^{k-1} b} = span{v_1, ..., v_k}` (2.5) (second equality valid while the
Lanczos vectors exist, i.e. `β_i > 0` for `i ≤ k`).

**Proposition 2.2 (Lanczos vectors vs. range and null space).** `A` symmetric, `β_i > 0` for
`i = 1..k`, `β_{k+1} = 0`. Then
1. If `b ∈ N(A)`: `α_1 = 0`, `β_2 v_2 = 0` (so `k = 1`) and `rank(A) ≤ n - 1` [OCR: "rank(A) ≤ 1",
   read as `< n`; uncertain].
2. If `b ∈ R(A)`: `v_1 ∥ b` and `v_2, ..., v_k ⊥ b` are `k` orthogonal vectors lying in `R(A)`, so
   `n ≥ rank(A) ≥ k`.
3. If `b ∉ R(A)` and `b ∉ N(A)`: `v_1, ..., v_k` have nonzero components in `R(A)` and
   `n > rank(A) ≥ k - 1`.
*Structure:* orthogonal decomposition `R^n = R(A) ⊕ N(A)` (symmetry), rank arguments (finite dim).
*Sketch of 3:* write `b = b_R + b_N`; by induction `v_{i+1,N} ∥ v_{1,N} ∥ b_N` and
`α_i = v_{i,R}^T A v_{i,R}`; so `V_k = [v_{1,R} ... v_{k,R}] + v_{1,N} c^T` (rank-1 perturbation of
a rank-`k` matrix), hence `rank(A) ≥ rank[v_{1,R} ... v_{k,R}] ∈ {k-1, k}`.

**Corollary 2.3.** `A` symmetric, `r = rank(A)`. (1) If `b ∈ R(A)`, `β_{k+1} = 0` for some
`k ≤ r ≤ n`. (2) If `r < n` and `b ∉ R(A)`, `β_{k+1} = 0` for some `k ≤ r + 1 ≤ n`.

**Theorem 2.4 (termination index from spectral data).** `A` symmetric with `s` distinct nonzero
eigenvalues; `b` has nonzero components along `t ≤ s` eigenvectors belonging to `t` distinct
nonzero eigenvalues. Then `β_{k+1} = 0` for some `k ≤ min{t+1, s}` if `b ∉ R(A)`, and `k ≤ t` if
`b ∈ R(A)`. *Structure:* spectral decomposition; `dim K_∞(A,b)` = number of distinct eigenvalues
with nonzero weight (plus one for the null component). Example 1 lists diagonal cases.

### B.2.2 Lanczos-based methods as subproblems (§2.2)

**Master identity.** For `x_k = V_k y ∈ K_k(A,b)`:
`r_k = b - A x_k = V_{k+1}(β_1 e_1 - T̄_k y)`, so all methods make `β_1 e_1 - T̄_k y` small.
CG: first `k` equations `T_k y = β_1 e_1` (Cholesky of `T_k`). SYMMLQ: the first `k-1` equations,
in practice the underdetermined `T̄_k^T y = β_1 e_1` (LQ of `T̄_k^T`). MINRES: minimize
`||β_1 e_1 - T̄_k y||_2` (QR of `T̄_k`).

**Framework (Paige 1974 / Saunders 1995):** "An iterative process generates certain quantities from
the data. At each iteration a subproblem is defined ... Different subproblems define different
methods for solving the original problem. Different ways of solving a subproblem lead to different
implementations of the associated method." CG and LanczosCG are two implementations of one method.

**Table 2.3 (subproblem definitions).**

| Method | Subproblem | Factorization | `x_k` |
|---|---|---|---|
| LanczosCG / CG | `T_k y_k = β_1 e_1` | Cholesky `T_k = L_k D_k L_k^T` | `x_k = V_k y_k ∈ K_k` |
| SYMMLQ | `y_{k+1} = argmin{ ||y|| : T̄_k^T y = β_1 e_1, y ∈ R^{k+1} }` | LQ `T̄_k^T Q_k = [L_k 0]` | `x_k = V_{k+1} y_{k+1} ∈ K_{k+1}` |
| MINRES | `y_k = argmin_{y ∈ R^k} ||T̄_k y - β_1 e_1||` | QR `Q_k T̄_k = [R_k ; 0]` | `x_k = V_k y_k ∈ K_k` |

**Table 2.4 (bases and subproblem solutions).**
LanczosCG: `W_k := V_k L_k^{-T}`, `L_k D_k z_k = β_1 e_1`, `x_k = W_k z_k`.
CG: `W_k := V_k L_k^{-T} Δ_k`, `Δ_k = diag(||r_0||, ..., ||r_{k-1}||)` [index convention uncertain],
`L_k D_k Δ_k z_k = β_1 e_1`. SYMMLQ: `W_k := V_{k+1} Q_k [I_k ; 0]`, `L_k z_k = β_1 e_1`,
`x_k = W_k z_k`. MINRES: `D_k := V_k R_k^{-1}`, `R_k z_k = β_1 [I_k 0] Q_k e_1`, `x_k = D_k z_k`.

**Classification (Demmel §6.6.2), Table 2.5.**
1. Minimum-residual: `x_k ∈ K_k` with `||r_k||` minimal.
2. Orthogonal-residual / Galerkin: `x_k ∈ K_k` with `r_k ⊥ K_k` (`V_k^T r_k = 0`).
3. Minimum-error: `x_k = argmin_{u ∈ K_k} ||x - u||`.
Table 2.5: **CG** (`A ≻ 0`): `min ||r_k||_{A^{-1}}`, `r_k ⊥ K_k`, `A r_k ⊥ K_{k-1}`; error
`min ||x - x_k||_A`. **SYMMLQ**: `r_k ⊥ K_k`, `A r_k ⊥ K_{k-1}`; error `min ||x - x_k||_2`
(over `x_k ∈ A K_k(A,b)`, the standard SYMMLQ characterization [uncertain whether stated so]).
**MINRES**: `min ||r_k||_2`; `A r_k ⊥ K_k`; `β_{k+1} = 0 ⇒ r_k ⊥ K_k`; no error property.
Figure 2.1: loss of orthogonality of `V_k` in finite precision coincides with convergence of the
solver (cited Paige, Paige-Saunders).

### B.2.3 CG (§2.2.1)

* `T_k = L_k D_k L_k^T` (unit lower bidiagonal `L_k`, `D_k = diag(δ_1..δ_k)`), recurrences of
  LanczosCG (Table 2.6; assumes `A` symmetric only, stops if `δ_k ≤ 0`, "indefinite, perhaps unstable
  to continue"): `δ_1 = α_1, γ_1 = β_1`; `η_k = β_k/δ_{k-1}`, `δ_k = α_k - β_k η_k` [uncertain
  symbols]; `w_k = v_k - η_k w_{k-1}`, `x_k = x_{k-1} + ζ_k w_k`, `||r_k|| = |ζ_k| β_{k+1}`.
* Standard CG (Table 2.7, assumes `A ≻ 0`): `x_0 = 0, r_0 = b, q_1 = r_0`;
  `s_k = A q_k, δ_k = q_k^T s_k`; if `δ_k ≤ 0` stop (`q_k` is a null vector);
  `α_k = ρ_{k-1}^2/δ_k` [with `ρ_{k-1} = ||r_{k-1}||`], `x_k = x_{k-1} + α_k q_k`,
  `r_k = r_{k-1} - α_k s_k`, `ρ_k = ||r_k||`, `β_{k+1} = ρ_k^2/ρ_{k-1}^2`, `q_{k+1} = r_k + β_{k+1} q_k`.
  Estimates `||A||`, `κ(A)` from `max/min` of Ritz-like quantities.

**Proposition 2.5 (`||A r_k||` for CG).** `||A r_0|| = ||r_0|| sqrt(α_1^2 + β_2^2)`;
for `k ≥ 1`, `||A r_k||` is given by an explicit expression in `α_{k+1}`, `β_{k+1}`, `β_{k+2}`
(CG coefficients) — obtained from `A r_k = (-1)^k ||r_k|| (β_{k+2} v_{k+2} + α_{k+1} v_{k+1} + β_{k+1} v_k)`
(see §2.4.2). [Exact printed formula in CG coefficients not recoverable.]

**Lemma 2.6.** `r_k = 0` iff `A r_k = 0` (for CG: since `r_k ∝ v_{k+1}` and the Lanczos vectors are
never in `N(A)` unless the process stops). Consequence: CG applies to compatible systems only.

**Proposition 2.7 (null vector from breakdown).** Exact arithmetic, `A ⊁ 0` (not positive
definite): if `δ_k = q_k^T A q_k = 0` then `α_k` undefined, CG breaks down, and `q_k` is a null
vector of `A`. [Requires `A ⪰ 0`; for indefinite `A`, `q_k^T A q_k = 0` need not give a null vector,
see CGI below.]
**Proposition 2.8.** Finite precision: if `δ_k = O(ε)`, `α_k` and `x_k` explode and normalized `x_k`
approximates a null vector.
* CG applies to symmetric positive semidefinite `A` if `b ∈ R(A)`; variant **CGI** (Table 2.8,
  stopping on `δ_k = 0` instead of `δ_k ≤ 0`) sometimes works for indefinite singular `A`.
**Propositions 2.9-2.10** = 2.7-2.8 for CGI with "`q_k` solves `x^T A x = 0`".
**Example 2:** `A = diag(-20, ..., 20)`, `b = A e`: `b^T A b = 0`, CG and CGI fail at step 1, while
SYMMLQ and MINRES succeed.

### B.2.4 SYMMLQ (§2.2.2)

* Subproblem (2.8): `y_{k+1} = argmin{ ||y|| : T̄_k^T y = β_1 e_1, y ∈ R^{k+1} }`, solved via LQ
  (2.9): `T̄_k^T P_k = [L_k 0]`, `P_k = P_{1,2} P_{2,3} ... P_{k,k+1}`, each `P_{i,i+1}` (2.10) a
  symmetric orthogonal 2x2 reflector `[[c_i, s_i],[s_i, -c_i]]` annihilating `β_{k+1}` in
  `[γ_k^{(1)}, β_{k+1}] [[c_k, s_k],[s_k, -c_k]] = [γ_k^{(2)}, 0]`,
  `γ_k^{(2)} = sqrt((γ_k^{(1)})^2 + β_{k+1}^2)`, `c_k = γ_k^{(1)}/γ_k^{(2)}`, `s_k = β_{k+1}/γ_k^{(2)}`
  (stable version SymOrtho, Table 2.9).
* With `y_{k+1} = P_k z̄_{k+1}`, (2.11): `L_k z_k = β_1 e_1`, `z̄_{k+1} = [z_k ; 0]`; (2.12):
  `x_k = V_{k+1} y_{k+1} = V_{k+1} P_k [z_k;0] = W_k z_k = x_{k-1} + ζ_k w_k`, where
  `V_{k+1} P_k = [W_k  w̄_{k+1}]`; (2.13): `ζ_k = -(ε_k ζ_{k-2} + δ_k^{(2)} ζ_{k-1})/γ_k^{(2)}`
  [uncertain symbol names], `w_k = c_k w̄_k + s_k v_{k+1}`, `w̄_{k+1} = s_k w̄_k - c_k v_{k+1}`.

**Proposition 2.11 (`r_k` of SYMMLQ).** `r_0 = β_1 v_1 = b`. For `k ≥ 1` there are scalars
(products of `β_{k+1}`, `β_{k+2}`, `ζ`'s and reflector entries) such that
`r_k = ϖ_{k+1} v_{k+1} - ϖ_{k+2} v_{k+2}` and `||r_k|| = sqrt(ϖ_{k+1}^2 + ϖ_{k+2}^2)` (2.14)-(2.15)
[exact scalar definitions uncertain]. Hence **`V_k^T r_k = 0`** (Galerkin). `||r_k||` is available
only at iteration `k+1`.
**Proposition 2.12 (`A r_k` of SYMMLQ).** `A r_0 = β_1(α_1 v_1 + β_2 v_2)`,
`||A r_0|| = β_1 sqrt(α_1^2 + β_2^2)`; `A r_k` is a combination of `v_k, ..., v_{k+3}` with explicit
coefficients (2.16)-(2.17). *Structure:* (2.3) applied to (2.14).
**Lemma 2.13.** `||A r_k|| = 0 ⇔ ||r_k|| = 0`: SYMMLQ cannot produce a least-squares residual with
`A r = 0, r ≠ 0`; not applicable to incompatible systems.
**Lemma 2.14 (SYMMLQ solution norm is monotone).** With `χ_0 = 0`:
`||x_k||^2 = ||z_k||^2 = χ_{k-1}^2 + ζ_k^2` (i.e. `||x_k||^2 = ||x_{k-1}||^2 + ζ_k^2`) increases
monotonically. *Structure:* `x_k = W_k z_k` with `W_k` orthonormal columns and `z_k = [z_{k-1}; ζ_k]`;
purely inner-product; holds for any symmetric `A` while the algorithm is defined.
**Proposition 2.15 (breakdown).** Exact arithmetic: if `γ_k^{(2)} = 0` SYMMLQ breaks down; if
also `γ_k^{(1)} = 0` [i.e. `β_{k+1} = 0` too] then `x_{k-1}` is the solution; otherwise `b ∉ R(A)`
and SYMMLQ gives no solution.
**Proposition 2.16 (transfer to the CG point; `A` symmetric positive semidefinite).**
Let `x_k^C` be the CG iterate, `ρ_k^C = ||r_k^C||`. Then
1. `x_k^C = x_k + (ζ_k s_k / c_k) w̄_{k+1}`;
2. `||x_k^C||^2 = ||x_k||^2 + (ζ_k s_k/c_k)^2 ≥ ||x_k||^2`;
3. `ρ_k^C = β_1 |s_1 s_2 ... s_k| / |c_k| = (|c_{k-1}| s_k / |c_k|) ρ_{k-1}^C` [uncertain].
*Structure:* CG iterate = Galerkin solution in `K_k`, expressed in the SYMMLQ basis; `w̄_{k+1} ⊥ W_k`.
**Lemma 2.17 (null vector from SYMMLQ).** If `β_{k+1} = 0` and `γ_k^{(2)} = 0` then `w̄_k` is a unit
null vector of `A`. *Sketch:* `β_{k+1} = 0 ⇒ L_k = T_k Q_{k-1}` [with last column zero]; then
`A w̄_k = A V_k Q_{k-1} e_k = V_k T_k Q_{k-1} e_k = V_k L_k e_k = 0`, `||w̄_k|| = 1`.

### B.2.5 MINRES (§2.2.3)

* Subproblem (2.18): `y_k = argmin_{y ∈ R^k} ||β_1 e_1 - T̄_k y||_2`. QR (2.19):
  `Q_k T̄_k = [R_k ; 0]`, `Q_k(β_1 e_1) = [t_k ; φ_k]`, `Q_k = Q_{k,k+1} ... Q_{2,3} Q_{1,2}` a product
  of `(k+1) x (k+1)` reflectors annihilating the subdiagonal `β`'s; `R_k` upper tridiagonal with
  diagonal `γ_i^{(2)}`, superdiagonal `δ_{i+1}^{(2)}`, second superdiagonal `ε_{i+2}`. (This is the
  transpose of SYMMLQ's LQ, `Q_k = P_k^T`.) Equivalent form (2.20):
  `y_k = argmin ||[t_k ; φ_k] - [R_k ; 0] y||`, so `R_k y_k = t_k` when `R_k` is nonsingular and
  `||r_k|| = |φ_k|`.
* (2.21): `t_k = β_1 (c_1, s_1 c_2, s_1 s_2 c_3, ..., s_1...s_{k-1} c_k)^T`, `φ_k = β_1 s_1 s_2 ... s_k`
  (with the SymOrtho sign convention `s_i = β_{i+1}/sqrt((γ_i^{(1)})^2 + β_{i+1}^2) ≥ 0`, so `φ_k ≥ 0`).
* (2.22) one step of the QR update:
  `[[c_k, s_k],[s_k, -c_k]] [[γ_k^{(1)}, δ_{k+1}^{(1)}, 0],[β_{k+1}, α_{k+1}, β_{k+2}]]
  = [[γ_k^{(2)}, δ_{k+1}^{(2)}, ε_{k+2}],[0, γ_{k+1}^{(1)}, δ_{k+2}^{(1)}]]`.
* (2.23)-(2.24): `x_k = V_k y_k = V_k R_k^{-1} t_k =: D_k t_k = x_{k-1} + τ_k d_k`, with
  `d_k = (v_k - δ_k^{(2)} d_{k-1} - ε_k d_{k-2}) / γ_k^{(2)}` (`τ_k` = last entry of `t_k`).
  MINRES needs 5 working `n`-vectors and `2 ν + 9 n` flops per iteration (`ν` = nnz(A)).
  If `γ_k^{(2)} = 0` the algorithm sets `x_k := x_{k-1}`.
* CR (Table 2.12, Saad Alg. 6.20): `x_0 = 0, r_0 = p_0 = b, z_0 = A r_0, w_0 = A p_0, μ_0 = r_0^T z_0`;
  `α_k = μ_{k-1}/||w_{k-1}||^2`, `x_k = x_{k-1} + α_k p_{k-1}`, `r_k = r_{k-1} - α_k w_{k-1}`,
  `z_k = A r_k`, `μ_k = r_k^T z_k`, `β_k = μ_k/μ_{k-1}`, `p_k = r_k + β_k p_{k-1}`,
  `w_k = z_k + β_k w_{k-1}`. "CR is to MINRES as CG is to LanczosCG."

**Lemma 2.18 (`r_k` of MINRES and monotonicity).**
`r_k = s_k^2 r_{k-1} - φ_k c_k v_{k+1}`, `||r_k|| = ||r_{k-1}|| s_k` (`= φ_k = β_1 s_1...s_k`), hence
`||r_k|| ≤ ||r_{k-1}||`. Intermediate `r_k` are not orthogonal to `K_k` except when `β_{k+1} = 0`
(then `s_k = 0` and `r_k = -φ_k v_{k+1}` [uncertain sign] is orthogonal to `K_k`).
*Structure:* `r_k = V_{k+1} Q_k^T [0; φ_k]` and the structure of `Q_k^T e_{k+1}` (see Prop 3.2 proof).
**Lemma 2.19 (`A r_k` of MINRES).** `A r_k = ||r_k|| (γ_{k+1}^{(1)} v_{k+1} + δ_{k+2}^{(1)} v_{k+2})`,
`||A r_k|| = ||r_k|| sqrt((γ_{k+1}^{(1)})^2 + (δ_{k+2}^{(1)})^2)`. (So `A r_k ⊥ K_k`, the
normal-equation condition of the residual minimization; `||A r_k||` is often oscillatory.)
**Lemma 2.20 (`||A x_k||`).** `||A x_k||_2 = ||t_k|| = ||[t_{k-1}; τ_k]||`, i.e.
`||A x_k||^2 = ||A x_{k-1}||^2 + τ_k^2` (monotone increasing). *Sketch:*
`A x_k = V_{k+1} T̄_k y_k`, `||T̄_k y_k|| = ||Q_k T̄_k y_k|| = ||R_k y_k|| = ||t_k||`.
**Proposition 2.21.** If `b ∈ R(A)`, `β_i > 0` for `i ≤ k`, `β_{k+1} = 0`, then `γ_k^{(1)} ≠ 0`
[printed `> 0`], so `T_k` and `R_k` are nonsingular. *Sketch:* if `γ_k^{(1)} = 0` then `s_k = 0`,
`||r_k|| = s_k ||r_{k-1}|| = 0`, `R_k` singular of rank `k-1`, MINRES sets `x_k := x_{k-1}`, so
`||r_{k-1}|| = ||r_k|| = 0`, contradicting that the method had not stopped at `k-1`.
**Corollary 2.22.** If `β_i > 0` (`i ≤ k`), `β_{k+1} = 0` and `γ_k^{(1)} = 0`, then `T_k, R_k` are
singular (rank `k-1`) and `b ∉ R(A)`.

**Definition 2.23 (Moore-Penrose pseudoinverse).** `X` is the pseudoinverse of `A` (m x n) iff
(1) `A X A = A`, (2) `X A X = X`, (3) `(A X)^H = A X`, (4) `(X A)^H = X A`.
**Theorem 2.24.** The pseudoinverse exists and is unique (Golub-Van Loan). For nonsingular square
`A`, `A^† = A^{-1}`; minimum-length solution `x = A^† b = V Σ^{-1} U^T b` from the reduced SVD.

**Theorem 2.25 (MINRES gives the pseudoinverse solution of compatible systems).**
If `b ∈ R(A)`, `β_i > 0` for `i = 1..k`, `β_{k+1} = 0`, then `x_k` is the pseudoinverse solution of
`A x = b`. *Hypotheses:* `A` symmetric (possibly singular), compatible.
*Sketch (thesis):* by Prop 2.21 `R_k^{-1}` exists; (2.25) `x_k = V_k R_k^{-1} t_k
= V_k R_k^{-1} [I_k 0] Q_k V_k^T b ... = V_k T_k^{-1} V_k^T b`. Define `A^‡ := V_k T_k^{-1} V_k^T`.
Then `A A^‡ = V_k T_k T_k^{-1} V_k^T = V_k V_k^T = A^‡ A` (using `A V_k = V_k T_k`), symmetric, so
MP(3),(4); assuming `span(V_k) = R(A)` (the thesis assumes this "for simplicity; without it the
result is still true but the proof more complicated"), `V_k V_k^T A = A` gives MP(1),(2).
*Cleaner structural argument (not in the thesis):* the minimum-length solution of a compatible
system is the unique solution lying in `N(A)^⊥ = R(A^T) = R(A)`; since `b ∈ R(A)`,
`K_k(A,b) ⊆ R(A)`, so any exact solution found in a Krylov subspace is the pseudoinverse solution.
This covers CG, SYMMLQ, MINRES, MINRES-QLP, GMRES (symmetric) simultaneously and only needs an
inner product and self-adjointness.

### B.2.6 MINRES on singular incompatible systems (§2.3, §2.3.1)

MINRES's `x_k` is a least-squares solution (`||r_k||` minimal) but not necessarily minimum-length.

**Definition 2.26 (generalized inverses).** `X` is an `{i}`-inverse of `A` if it satisfies MP
condition `i`; `{i,j}`-, `{i,j,k}`-inverses analogously (Ben-Israel-Greville).

**Theorem 2.27 (MINRES on singular symmetric least squares).** `A = A^T` singular, `b ∉ R(A)`.
If `β_i ≠ 0` for `i ≤ k`, `β_{k+1} = γ_k^{(1)} = 0` and `A r_k = 0` [the last is a consequence],
then `x_k := x_{k-1}` is a `{2,3}`-inverse solution (`x_k = X b` for a `{2,3}`-inverse `X` of `A`);
moreover a `{1,2,3}`-inverse solution if the range components of the columns of `V_k` span `R(A)`.
It is in general NOT the pseudoinverse solution (MP(4) fails).
*Sketch:* with `β_{k+1} = γ_k^{(1)} = 0`, (2.20) becomes an underdetermined problem with
`R_k = [[R_{k-1}, s],[0, 0]]`, `s = 0` [since `γ_k^{(1)} = s_{k-2} ... = 0`]; choosing the last
component of `y_k` as zero reduces to the `(k-1)`-th subproblem, so `x_k = x_{k-1}`,
`r_k = r_{k-1}` (`||r_{k-1}|| > 0`), `A r_k = 0` (2.26)-(2.28); (2.29)-(2.31)
`x_k = V_k R_k^‡ Q_k^{-1} V_k^T b =: A^‡ b` with `R_k^‡ = [[R_{k-1}^{-1}, 0],[0, 0]]`;
(2.32) `A V_k = V_k Q_k^{-1} R_k`, `V_k^T A V_k = T_k`; then `A A^‡ = V_k Q_k^{-1} diag(I_{k-1}, 0) Q_k V_k^T`
symmetric (MP3), `A^‡ A = V_k R_k^‡ R_k V_k^T` not symmetric (MP4 fails), MP2 holds since
`R_k^‡ R_k R_k^‡ = R_k^‡`, MP1 iff `V_{k,R}` spans `R(A)`.
**Example 3.** `A = diag(1,1,0)`, `b = (1,1,1)^T`: minimum-length solution `(1,1,0)^T`,
`r = (0,0,1)^T`, `A r = 0`; MINRES returns `x = (1,1,1)^T` (same residual). Hence a new stopping
condition on `||A r_k||` and a modified algorithm are needed.

### B.2.7 GMRES, LSQR, QMR (§2.3.2-2.3.4)

* **Arnoldi (2.42)-(2.44):** `β_1 v_1 = b`, `w_k = A v_k`, `h_{i,k} = w_k^T v_i`,
  `h_{k+1,k} v_{k+1} = w_k - Σ_{i ≤ k} h_{i,k} v_i`; `A V_k = V_{k+1} H̄_k`, `H̄_k = [H_k ; h_{k+1,k} e_k^T]`,
  `H_k` upper Hessenberg; stops when `h_{k+1,k} = 0`, then `A V_k = V_k H_k`. Modified Gram-Schmidt on
  the Krylov basis; for symmetric `A` it is the Lanczos process.
* **GMRES:** `y_k = argmin_{y ∈ R^k} ||H̄_k y - β_1 e_1||`, `x_k = V_k y_k ∈ K_k(A,b)`; stores all
  `v_i`; QR of `[H̄_k β_1 e_1]` by Givens (Table 2.16). For `A = A^T` mathematically equivalent to
  MINRES (no short recurrence). Restarted GMRES(m) may stagnate. Ipsen-Meyer: on singular compatible
  systems Krylov methods such as GMRES yield in general the Drazin-inverse solution; on
  inconsistent systems no solution in general.
* **Golub-Kahan bidiagonalization (Bidiag1):** `β_1 u_1 = b`, `α_1 v_1 = A^T u_1`,
  `β_{k+1} u_{k+1} = A v_k - α_k u_k`, `α_{k+1} v_{k+1} = A^T u_{k+1} - β_{k+1} v_k`;
  `A V_k = U_{k+1} B̄_k`, `A^T U_{k+1} = V_{k+1} B_{k+1}^T` (i.e. `V_k B̄_k^T + α_{k+1} v_{k+1} e_{k+1}^T`)
  with `B̄_k` lower bidiagonal `(k+1) x k` (diag `α_i`, subdiag `β_{i+1}`); stops when
  `α_{k+1} = 0` or `β_{k+1} = 0`. Derivable as Lanczos on `[[I, A],[A^T, 0]]` applied to `[b;0]`.
* **LSQR:** `min_y ||B̄_k y - β_1 e_1||`, `x_k = V_k y_k ∈ K_k(A^T A, A^T b)`, QR of `B̄_k` by
  reflectors (Table 2.18); mathematically CG on the normal equations; converges to the
  minimum-length solution for any shape/rank (convergence governed by distinct nonzero singular
  values; Example 4: complex symmetric non-Hermitian `A`, 1 iteration).
* **Two-sided Lanczos / QMR / SQMR:** biorthogonal `W_k^T V_k = D` diagonal nonsingular,
  `span(V_k) = K_k(A, v_1)`, `span(W_k) = K_k(A^T, w_1)`; Bi-CG, Bi-CGSTAB not for incompatible
  systems; QMR `y_k = argmin ||T̄_k y - β_1 e_1||` with unsymmetric tridiagonal `T̄_k` (quasi-minimal
  residual); SQMR for symmetric `A`; unpreconditioned QMR/SQMR on symmetric `A` are equivalent
  to MINRES.

Table 2.13/2.14 summarize: MINRES (Lanczos, `T̄_k` symmetric tridiagonal), GMRES (Arnoldi,
`H̄_k` Hessenberg), QMR (bi-Lanczos, `T̄_k` unsymmetric tridiagonal), LSQR (Golub-Kahan, `B̄_k`
lower bidiagonal, subspace `K_k(A^T A, A^T b)`); all subproblems are `argmin ||M̄_k y - β_1 e_1||`
solved by QR, with bases `D_k = V_k R_k^{-1}` or `W_k = V_k R_k^{-1}`.

### B.2.8 Stopping conditions and norm estimates (§2.4)

Recommended family of stopping rules (for CG, SYMMLQ, MINRES):
```
Lanczos:     β_{k+1} ≤ n ε ||A||,   k = maxit
NRBE:        ||r_k|| / (||A|| ||x_k|| + ||b||) ≤ tol,   ||A r_k|| / (||A|| ||r_k||) ≤ tol
Regularize:  κ(A) ≥ maxcond,   ||x_k|| ≥ maxxnorm
```
Relative norms (2.45) use `||A||_F`, (2.46) use `||A||_2`; since `||A||_F ≥ ||A||_2`, (2.45) stops
sooner.
* §2.4.1 residual: LanczosCG `r_k = (-1)^k ||r_k|| v_{k+1}`, `||r_k|| = |ζ_k| β_{k+1}`; SYMMLQ
  as Prop 2.11; MINRES `||r_k|| = φ_k = φ_{k-1} s_k`.
* §2.4.2 `||A r_k||`: LanczosCG `A r_0 = ||r_0||(β_2 v_2 + α_1 v_1)`,
  `A r_k = (-1)^k ||r_k|| (β_{k+2} v_{k+2} + α_{k+1} v_{k+1} + β_{k+1} v_k)`,
  `||A r_k|| = ||r_k|| sqrt(β_{k+1}^2 + α_{k+1}^2 + β_{k+2}^2)`; CG via Prop 2.5; SYMMLQ via
  Prop 2.12; MINRES via Lemma 2.19.
* §2.4.3 solution norms: compute directly for CG/MINRES; SYMMLQ `||x_k||^2 = χ_{k-1}^2 + ζ_k^2`.
* **Lemma 2.28 (SVD norms).** `||A||_2 = σ_1`, `||A||_F = (Σ σ_i^2)^{1/2} ≥ ||A||_2`.
* **Theorem 2.29 (interlacing of singular values, Thompson 1972).** `B` = `A` with one column (or
  row) deleted; then `σ_1(A) ≥ σ_1(B) ≥ σ_2(A) ≥ σ_2(B) ≥ ...` (equalities if the deleted
  column is zero). **Corollary 2.30.** `||B||_2 ≤ ||A||_2` for any submatrix.
* **Lemma 2.31.** For LanczosCG, SYMMLQ, MINRES: `||A||_2 ≥ ||T̄_k||_2 ≥ ||T_k||_2`.
  *Sketch:* `||A||_2 ≥ ||A V_k||_2 = ||V_{k+1} T̄_k||_2 = ||T̄_k||_2` (orthonormal `V_{k+1}`).
* **Lemma 2.32.** `||A||_2 ≥ max_{i ≤ k} ||T̄_i e_i||_2`, `||T̄_i e_i|| = ||(β_i, α_i, β_{i+1})||`;
  the running maximum `A_2^{(k)}` is an increasing lower estimate (`p_i = A v_i = V_{i+1} T̄_i e_i`).
  Paige 1976: `|β_k^2 + α_k^2 + β_{k+1}^2 - ||p_k||^2| ≤ 4k(3n + 19 + m ...) ε ||A||^2` [garbled].
* **Lemma 2.33.** `||A||_F ≥ ||T̄_k||_F`; `A_F^{(k)} := sqrt((A_F^{(k-1)})^2 + ||T̄_k e_k||^2)` strictly
  increasing estimate. *Sketch:* `||T̄_k||_F = ||A V_k||_F = ||Σ V^T V_k||_F ≤ ||Σ||_F` using
  orthonormal rows/columns and Cor 2.30.
* **Theorem 2.34 (Trefethen-Bau 12.1-12.2).** Condition numbers of `x ↦ A x` and `b ↦ A^{-1} b`
  are `||A|| ||x||/||b||` and `||A^{-1}|| ||b||/||x||`, both `≤ κ(A)`.
* **Lemma 2.35.** Nonsingular triangular `U`: `κ(U) ≥ max_i |u_ii| / min_i |u_ii|`.
  Applications (2.48)-(2.50): `κ(T_k) ≤ max δ_i / min δ_i` for CG/Cholesky [uncertain direction];
  for MINRES/SYMMLQ `κ_2(A V_k) = κ_2(T̄_k) = κ_2(R_k) = κ_2(L_k) ≥ max_i |γ_i^{(2)}| / min_i |γ_i^{(2)}|`.

## B.3 Chapter 3: MINRES-QLP

### B.3.1 Motivation (§3.1)

* Rounding errors in MINRES (§3.1.1): MINRES computes `x_k = (V_k R_k^{-1}) t_k = D_k t_k
= x_{k-1} + τ_k d_k`; `D_k` may be large and there may be cancellation; Sleijpen-van der
Vorst-Modersitzki (2000) analyze the `n` triangular solves defining the rows of `D_k`; recurred
`||r_k||` (`φ_k`) can be misleadingly small compared with the true residual on ill-conditioned spd
systems (Fig 3.1). MINRES-QLP uses a single lower-triangular solve per step without storing `V_k`.
* §3.1.2: alternatives for minimum-length symmetric least squares — normal equations
  `A^2 x = A b`, augmented systems `[[I, A],[A^T, γ I]] [s;x] = [b;0]` (AMRES), two-step procedure
  (LS solution then min-length solution of `A x = A x_LS`), MINRES-L; all expensive or unstable.
* §3.1.3: complete orthogonal decompositions `A = U [[T, 0],[0, 0]] V`; QR with column pivoting
  `Q A Π = R` (R-values ≈ singular values); Hanson-Lawson; Stewart's pivoted QLP (3.4)-(3.5):
  `A = Q L P` with `L` lower triangular, L-values better singular-value estimates: (3.6)
  `σ_1 ≥ max L_ii ≥ max R_ii`, `min R_ii ≥ min L_ii ≥ σ_n` [uncertain], in particular accurate for
  extreme singular values.

### B.3.2 The MINRES-QLP subproblem (§3.2)

**Subproblem (3.7).** `min ||y||  s.t.  y ∈ argmin_{y ∈ R^k} ||T̄_k y - β_1 e_1||`;
`x_k = V_k y_k ∈ K_k(A,b)`. When `T̄_k` has full column rank, `y_k` and `x_k` coincide with MINRES.
(`T_k`, `T̄_k` may be singular when `A` is singular; rank `k` or `k-1`.)

**QLP decomposition (unpivoted, updatable).** `Q_k T̄_k = [R_k ; 0]`, `R_k P_k = L_k`
(`R_k` upper tridiagonal, `L_k` lower tridiagonal), `Q_k = ... Q_{34} Q_{23} Q_{12}`,
`P_k = P_{12} P_{13} P_{23} P_{24} P_{34} P_{35} P_{45} ...`; left reflector `Q_{k,k+1}` and right
reflectors `P_{k-2,k}, P_{k-1,k}` are interleaved so that only the lower-right 3x3 block changes at
step `k` (Fig 3.2). With `y = P_k u` the subproblem becomes (3.8)
`min ||u||  s.t.  u ∈ argmin_{u ∈ R^k} ||[L_k ; 0] u - [t_k ; φ_k]||`,
`t_k, φ_k` as in the MINRES QR. The first `k-3` components of `u_k` are already final.
Case `rank(L_k) = k`: solve the bottom three equations of `L_k u_k = t_k`.
Case `rank(L_k) = k-1`: last row and column of `L_k` are zero; `L_k = [[L_{k-1}^{(2)}, 0],[0, 0]]`,
solve `L_{k-1}^{(2)} u_{k-1}^{(2)} = t_{k-1}`, `u_k = [u_{k-1}^{(2)} ; 0]` (minimum-norm choice).
Basis change (3.9): `W_k = V_k P_k = [W_{k-3}, W_k(:, k-2:k)]`,
`x_k = W_k u_k = x_{k-3}^{(2)} + μ_{k-2}^{(3)} w_{k-2}^{(4)} + μ_{k-1}^{(2)} w_{k-1}^{(3)} + μ_k^{(1)} w_k^{(2)}`
(superscripts count updates; `x_{k-2}^{(2)}` := first two terms is kept).
If `β_{k+1} = 0`, MINRES stops (`s_k = 0`, `r_k = 0`); MINRES-QLP still applies the right
reflectors to obtain the minimum-length solution.

**Theorem 3.1 (pseudoinverse solution of MINRES-QLP).** In MINRES-QLP, if `β_i > 0` for
`i = 1..k` and `β_{k+1} = 0`, then `x_k` is the pseudoinverse solution of `A x ≈ b`
(compatible or incompatible). *Hypotheses:* `A` symmetric (Hermitian), arbitrary rank.
*Sketch:* "follows from the proofs of Thm 2.25 and Thm 2.27 with slight modification": at
termination `A V_k = V_k T_k`, `K_k` is `A`-invariant and contains `b`; the LS problem restricted to
`K_k` is the full LS problem (the complement `K_k^⊥` is invariant); choosing the minimum-norm `y`
gives the minimum-norm `x = V_k y` (`V_k` isometric), i.e. `x_k = V_k T_k^† V_k^T b = A^† b`.
*Structure:* inner product, self-adjointness, invariance of `K_k` at termination, finite-dim
pseudoinverse of `T_k`.

Tables 3.2-3.3 add MINRES-QLP to Tables 2.3-2.4: subproblem `y_k = argmin ||y|| s.t.
y = argmin ||T̄_k y - β_1 e_1||`, factorization QLP `Q_k T̄_k P_k = [L_k ; 0]`, basis `W_k := V_k P_k`,
`L_k u_k = β_1 [I_k 0] Q_k e_1`, `x_k = W_k u_k`. Cost: one more vector than MINRES, 4 more saxpy and
3 more scalings per iteration. §3.2.4: transfer from MINRES to MINRES-QLP when `κ(T_k)` estimate
exceeds `trancond`: at the transfer step `x_k^M = D_k t_k = W_k u_k = W_k L_k^{-1} t_k`, so
`W_k = D_k L_k` (3.10) and `x_{k-2}^{(2)} = x_k^M - μ_{k-1}^{(2)} w_{k-1}^{(3)} - μ_k^{(1)} w_k^{(2)}` (3.11).

### B.3.3 Stopping conditions and norm estimates for MINRES-QLP (§3.3)

Same three groups of stopping rules as MINRES (Lanczos, NRBE, regularization).

**Proposition 3.2 (`r_k` and monotonicity).**
`r_k = s_k^2 r_{k-1} - φ_k c_k v_{k+1}` and `||r_k|| = ||r_{k-1}|| s_k` if `rank(L_k) = k`;
`r_k = r_{k-1}`, `||r_k|| = ||r_{k-1}||` if `rank(L_k) = k-1`. Hence `||r_k|| ≤ ||r_{k-1}||`.
Intermediate `r_k` are not `⊥ K_k`; if `β_{k+1} = 0` then `s_k = 0` and `r_k = -φ_k c_k v_{k+1}` [sign
uncertain] `⊥ K_k`.
*Sketch (3.12)-(3.15):* `r_k = V_{k+1}(β_1 e_1 - T̄_k y_k) = V_{k+1} Q_k^T ([t_k;φ_k] - [L_k;0] u_k)`
(using `y_k = P_k u_k`, `Q_k^T Q_k = I`); `φ_k = β_1 s_1...s_k ≥ 0`. Case rank `k`:
`L_k u_k = t_k` so `r_k = φ_k V_{k+1} Q_k^T e_{k+1}`; with `Q_k^T e_{k+1} = [s_k Q_{k-1}^T e_k ; -c_k]`
[uncertain sign] one gets `r_k = φ_k s_k V_k Q_{k-1}^T e_k - φ_k c_k v_{k+1} = s_k^2 r_{k-1} - φ_k c_k v_{k+1}`
and `||r_k|| = φ_k sqrt(s_k^2 + c_k^2) = φ_k`.
*Structure:* orthonormality of `V_{k+1}`, reflector algebra; no positivity.

**Proposition 3.3 (`A r_k`).** If `rank(L_k) = k`: `A r_k = ||r_k|| (γ_{k+1}^{(1)} v_{k+1} + δ_{k+2}^{(1)} v_{k+2})`,
`||A r_k|| = ||r_k|| sqrt((γ_{k+1}^{(1)})^2 + (δ_{k+2}^{(1)})^2)`; if `rank(L_k) = k-1`: `A r_k = A r_{k-1}`.
In all cases `A r_k ⊥ K_k(A,b)`.
*Sketch (3.16)-(3.17):* `A r_k = φ_k A V_{k+1} Q_k^T e_{k+1} = φ_k V_{k+2} T̄_{k+1} Q_k^T e_{k+1}`; compute
`Q_k e_k`, `Q_k e_{k+1}` explicitly (only last two reflectors act) and read off the last row of
`T̄_{k+1} Q_k^T e_{k+1} = [0; γ_{k+1}^{(1)}; δ_{k+2}^{(1)}]` using (2.22).

**Matrix norm and condition estimates (§3.3.3-3.3.4).** For symmetric singular `A`,
`κ_2(A) := max|λ_i| / min_{λ_i ≠ 0} |λ_i| = ||A||_2 ||A^†||_2`. Estimates:
`||A||_2 ≥ max_i ||T̄_i e_i||` (3.18) and, by (3.6), the improved monotone estimate
`A_2^{(k)} := max{A_2^{(k-1)}, ||T̄_k e_k||, γ_{k-2}, γ_{k-1}, |γ_k|}` (3.19) using the diagonal of
`L_k`; other schemes (`||T_k||_1`, `||T_k^T T_k||_1^{1/2}`, `||T_j||_2`, NORMEST). Condition number
(3.20): `κ_2(A) ≥ κ_2(T̄_k) ≥ max_i γ_i / min_i γ_i` (diagonal of `L_k`).

**Solution norms (§3.3.5).** `||x_k|| = ||V_k P_k u_k|| = ||u_k||`; maintain `χ = ||u_k(1:k-2)||`
(= `||x_{k-2}^{(2)}||`), then `||x_k|| = ||(χ, μ_{k-1}^{(2)}, μ_k^{(1)})||`. `χ` increases monotonically
but `||x_k||` need not (Figs 1.3, 3.6). Regularization: if `||x_k|| > maxxnorm`, the last (then
second-to-last, then third-to-last) element of `u_k` is set to zero (truncated-SVD-like), justified
by `x_k = W_k u_k` with orthonormal `W_k` (Example 5).
**Eq. (3.21) (projection of `b` onto `K_k`).** `||A x_k|| = ||T̄_k y_k|| = ||R_k y_k|| = ||t_k||`, so
`ω_k := ||A x_k||_2 = ||(ω_{k-1}, τ_k)||`, `ω_0 = 0`.

### B.3.4 Preconditioning (§3.4)

* Two-sided preconditioning with `M = C C^T ≻ 0` preserves symmetry: solve
  `Ã x̃ = b̃`, `Ã = M^{-1/2} A M^{-1/2}`, `b̃ = M^{-1/2} b`, `x = M^{-1/2} x̃` (3.22). WLOG
  `C = M^{1/2}` (spectral square root).
* **Preconditioned Lanczos (3.23)-(3.24):** with `z_k = β_k M^{1/2} v_k`, `q_k = β_k M^{-1/2} v_k`
  (`M q_k = z_k`): `β_k = ||z_k||_{M^{-1}} = ||q_k||_M = sqrt(q_k^T z_k)`, `α_k = q_k^T A q_k / β_k^2`,
  `z_{k+1} = (1/β_k) A q_k - (α_k/β_k) z_k - (β_k/β_{k-1}) z_{k-1}`; one solve `M q_{k+1} = z_{k+1}` per
  step. PMINRES (Table 3.4): `d_k = (q_k/β_k - δ_k^{(2)} d_{k-1} - ε_k d_{k-2})/γ_k^{(2)}`,
  `x_k = x_{k-1} + τ_k d_k` (with `d_k = M^{-1/2} d̃_k`). PMINRES-QLP (Table 3.5): `W_k = M^{-1/2} Ṽ_k P_k`,
  `x_k = x_{k-2}^{(2)} + μ_{k-1}^{(2)} w_{k-1}^{(3)} + μ_k^{(1)} w_k^{(2)}` (3.26)-(3.27).
* Indefinite `A`: cannot achieve `M^{-1/2} A M^{-1/2} ≈ I`, but `≈ ±I` via `M = L|D|L^T` from a
  block `LDL^T` (Gill-Murray-Ponceleon-Saunders); SQMR can use indefinite preconditioners.
* **§3.4.2 (singular compatible `A x = b`).** MINRES-QLP finds the minimum-length solution; with
  nonsingular `M` the preconditioned system is compatible with min-length solution `x̃`, but
  `x = M^{-1/2} x̃` is a solution of `A x = b` that is **not necessarily minimum-length**
  (Example 6: rank-2 `A = B B^T`, diagonal `D`, `x = D y ≠ x^†`).
* **§3.4.3 (singular incompatible).** Augmented system `[[I, A],[A, 0]][r;x] = [b;0]` is singular
  but always compatible: preconditioning yields some LS solution `x = x^† + x_N`, `x_N ∈ N(A)`, with
  the unique `r`. Giant KKT system (3.28) for `min ||x||^2 s.t. min ||A x - b||^2`: symmetric,
  compatible, upper-left 3x3 block nonsingular so `(r, x, y)` unique and `x = x^†`. Regularization
  (3.29): `min ||[A; δ I] x - [b; 0]||`, equivalent normal equations `(A^T A + δ^2 I) x = A^T b` (3.30),
  augmented (3.31), two-layered (3.32) `[[I, A^2],[A^2, -δ^2 A^2]] [x; v] = [0; A b]`
  (Bobrovnikova-Vavasis), KKT-like (3.33); `x → x^†` as `δ → 0`.
* §3.5: diagonal scaling `d_j = 1/sqrt(max{δ, |a_jj|, max_{i≠j}|a_ij|})` (3.35), binormalization
  (Livne-Golub), incomplete Cholesky (IC0, Cholesky-infinity).

## B.4 Chapters 4-6 (brief)

* **Ch. 4** compares MINRES-QLP with EVD/TEVD solutions `x_EVD = Σ_{λ_i ≠ 0} u_i u_i^T b / λ_i`,
  `x_TEVD = Σ_{|λ_i| > c ε ||A||} u_i u_i^T b / λ_i`, and with Matlab/SOL implementations
  (Table 4.1: stopping rules per code). Test problems: singular indefinite system (ID 1239), two
  Laplacians (almost compatible, LS), Hermitian problems (without/with diagonal
  preconditioning/binormalization), rounding-error effects (§4.4). Conclusion: Lanczos-based
  methods have built-in regularization, often matching TEVD; MINRES-QLP more accurate than MINRES
  on ill-conditioned and singular problems; Matlab MINRES/SYMMLQ use a local reorthogonalization
  of `v_2` (4.1).
* **Ch. 5** null vectors: inverse iteration vs the least-squares approach (Table 5.1: which
  normalized vector is the null vector for CG/SYMMLQ/MINRES/MINRES-QLP/LSQR with or without stopping
  rules); multiple null vectors by MCGLS (Larsen), MLSQR, MLSQRnull (successive right-hand sides
  orthogonalized against previous residuals; `r_1^T r_2 = r_1^T c_2 - y_2^T A r_1 = 0`); PageRank
  experiments (LSQR vs power method), helioseismology example.
* **Ch. 6** summary (Table 6.1 problem types vs algorithms), contributions (MINRES-QLP as
  `x_k = (V_k P_k) u_k` with one triangular solve; recurrences for `||A r_k||`, `||A x_k||`; new
  stopping rules; regularization), ongoing work (error analysis a la Sleijpen et al.,
  GMRES-QLP/QMR-QLP, convergence of `A w̄_k` in SYMMLQ, multiple RHS, PLS connection, error bounds by
  moments/quadrature).

---------------------------------------------------------------------------------------------------

# Part C. Meurant & Strakos, "The Lanczos and CG algorithms in finite precision arithmetic"

## C.1 Section 2: the Lanczos algorithm in exact arithmetic

### C.1.1 Basic properties (§2.1)

Hypotheses: `A` real `n x n` nonsingular symmetric (nonsingularity is only needed for CG later),
`v` with `||v|| = 1`. `K_k(v, A) = span{v, Av, ..., A^{k-1} v}`; `dim K_k = k` iff `k ≤` degree of
the minimal polynomial of `v` w.r.t. `A` (≤ degree of the minimal polynomial of `A`).

* **Arnoldi** (Gram-Schmidt on the Krylov basis, no symmetry): `h_{i,j} = (A v_j, v_i)`,
  `v̂_j = A v_j - Σ_{i ≤ j} h_{i,j} v_i`, `h_{j+1,j} = ||v̂_j||` (stop if 0), `v_{j+1} = v̂_j/h_{j+1,j}`;
  `A V_k = V_k H_k + h_{k+1,k} v_{k+1} e_k^T`, `V_k^T A V_k = H_k` unreduced upper Hessenberg.
* **Lanczos:** `A` symmetric ⇒ `H_k` symmetric ⇒ tridiagonal. `v_1 = v`, `v_0 = 0`, `β_1 = 0`;
  `α_k = (A v_k, v_k)`, `v̂_{k+1} = A v_k - α_k v_k - β_k v_{k-1}`, `β_{k+1} = ||v̂_{k+1}||` (stop if 0),
  `v_{k+1} = v̂_{k+1}/β_{k+1}`. Modified Gram-Schmidt variant (2.1): `u_k = A v_k - β_k v_{k-1}`,
  `α_k = (u_k, v_k)`, `v̂_{k+1} = u_k - α_k v_k` (Paige's preferred form, two vectors of storage).
* Matrix form: `A V_k = V_k T_k + β_{k+1} v_{k+1} e_k^T`, `T_k = tridiag(β, α, β)` unreduced symmetric
  tridiagonal with positive subdiagonal. `α_k` is a Rayleigh quotient: `λ_min(A) ≤ α_k ≤ λ_max(A)`.
  Eigenvalues `λ_1 ≤ ... ≤ λ_n` of `A`, eigenvectors `q_i`, `Q = (q_1..q_n)`.
* **Termination:** if `β_j ≠ 0` for `j = 2..n` then `A V_n = V_n T_n` (`v̂_{n+1} ⊥` an orthonormal
  basis of `R^n`, so `v̂_{n+1} = 0`); otherwise `β_{m+1} = 0` for some `m < n`, `A V_m = V_m T_m`, an
  invariant subspace, eigenvalues of `T_m` ⊂ eigenvalues of `A`. If no early termination the
  eigenvalues of `A` are simple (`A ~ T_n` unreduced); multiple eigenvalues force early termination;
  Lanczos cannot detect multiplicity.
* **Ritz values/vectors:** `θ_1^{(k)} < ... < θ_k^{(k)}` eigenvalues of `T_k` (distinct, since
  unreduced), normalized eigenvectors `z_j^{(k)} = (ζ_{1,j}^{(k)}, ..., ζ_{k,j}^{(k)})^T`,
  `Z_k = (z_1^{(k)} .. z_k^{(k)})`; Ritz vectors `x_j^{(k)} = V_k z_j^{(k)}`. Residual:
  `r_j^{(k)} = A x_j^{(k)} - θ_j^{(k)} x_j^{(k)} = (A V_k - V_k T_k) z_j^{(k)} = β_{k+1} ζ_{k,j}^{(k)} v_{k+1}`,
  `||r_j^{(k)}|| = β_{k+1} |ζ_{k,j}^{(k)}|` (all Ritz residuals are multiples of `v_{k+1}`).
  **A posteriori bound:** `min_i |λ_i - θ_j^{(k)}| ≤ β_{k+1} |ζ_{k,j}^{(k)}|`.
  *Structure:* spectral decomposition of `A` and `||x_j^{(k)}|| = 1` (exact orthonormality).

### C.1.2 Orthogonal polynomials, Riemann-Stieltjes integral, Gauss quadrature (§2.2)

* (2.2)-(2.3): `v_{k+1} = p_{k+1}(A) v_1`, `p_1 = 1`, `p_0 = 0`,
  `β_{k+1} p_{k+1}(λ) = (λ - α_k) p_k(λ) - β_k p_{k-1}(λ)`.
  With `χ_{1,k}(λ) = det(T_k - λ I)` (`χ_0 = 1`, `χ_1 = α_1 - λ`,
  `χ_k = (α_k - λ) χ_{k-1} - β_k^2 χ_{k-2}`): `p_{k+1}(λ) = (-1)^k χ_{1,k}(λ) / (β_2 ... β_{k+1})`.
* **(2.4) Distribution function.** `(p, q) = ∫_{λ_1}^{λ_n} p q dω = Σ_{l=1}^n ω_l p(λ_l) q(λ_l)`,
  `ω_l = |(v_1, q_l)|^2`, `Σ ω_l = 1`; `ω(λ)` non-decreasing piecewise constant with jumps `ω_l` at
  `λ_l` (assume distinct eigenvalues for exposition). The `p_k` are orthonormal w.r.t. (2.4)
  (from orthonormality of the `v_k` and the spectral decomposition).
* `P_k(λ) = (p_1(λ), ..., p_k(λ))^T` satisfies `λ P_k(λ) = T_k P_k(λ) + β_{k+1} p_{k+1}(λ) e_k`; roots
  of `p_{k+1}` = eigenvalues of `T_k` = Ritz values.
* **Minimization property.** `(-1)^k χ_{1,k} = argmin_{ψ ∈ M_k} ∫ ψ^2 dω`, `M_k` = monic polynomials of
  degree `≤ k` [`= k`], `k = 1..n`.
* **(2.5)** `T_k` is also the result of Lanczos applied to `T_k` with starting vector `e_1`; hence
  `p_1..p_{k+1}` are orthonormal w.r.t. `(p,q)_k = Σ_{l=1}^k ω_l^{(k)} p(θ_l^{(k)}) q(θ_l^{(k)})`,
  `ω_l^{(k)} = |(z_l^{(k)}, e_1)|^2` (squared first components of the eigenvectors of `T_k`).

**Theorem 1 (Lanczos = Gauss quadrature).** (2.5) is the `k`-point Gauss quadrature of (2.4):
nodes = Ritz values, weights = squared first eigenvector components of `T_k`; exact for
polynomials of degree `≤ 2k-1`.
*Structure:* orthogonality of `p_1..p_k` w.r.t. both inner products; pure polynomial algebra; valid
for any positive measure with finite moments.
*Sketch:* for `deg ψ ≤ 2k-1` write `ψ = p_{k+1} ψ_1 + ψ_2 = p_{k+1} ψ_1 + Σ_{l=2}^k ν_l p_l + ν_1`; both
integrals equal `ν_1`. Weight formula (2.6): using `χ_{k-1}(λ) = -χ_k(λ)/(λ - θ_l^{(k)}) + lower`,
`ω_l^{(k)} = |(z_l^{(k)}, e_1)|^2 = -β_2^2 ... β_k^2 / (χ_{k-1}(θ_l^{(k)}) χ_k'(θ_l^{(k)}))`.
Similarly (2.7) `|(z_l^{(k)}, e_k)|^2 = -β_2^2...β_k^2 / (χ_{2,k}(θ_l) χ_k'(θ_l))` (`χ_{2,k}` =
characteristic polynomial of `T_k` with first row/column removed), and (2.8)
`|(z_l, e_1)|^2 = -χ_{2,k}(θ_l)/χ_k'(θ_l)`, `|(z_l, e_k)|^2 = -χ_{k-1}(θ_l)/χ_k'(θ_l)`, using
`χ_{2,k}(θ_l) χ_{1,k-1}(θ_l) = β_2^2...β_k^2`. These are facts about any unreduced symmetric
tridiagonal matrix (sign of subdiagonal irrelevant).

Four equivalent formulations of the Lanczos algorithm: (i) orthonormal basis of `K_k(v_1, A)` in
`R^n`; (ii) the sequence of unreduced symmetric tridiagonal `T_k`; (iii) orthonormal polynomials
w.r.t. (2.4); (iv) Gauss quadrature approximations (2.5) of (2.4).

### C.1.3 Approximation from subspaces, persistence theorem (§2.3)

**Theorem 2 (Stewart 2001, p.285).** `U` orthonormal, `B = U^T A U`, `θ` the angle between the
eigenvector `q_i` (`A q_i = λ_i q_i`) and `range(U)`. Then there is `E` with
`||E|| ≤ (sin θ / sqrt(1 - sin^2 θ)) ||A||` such that `λ_i` is an eigenvalue of `B + E`.
**Corollary 3.** There is an eigenvalue `μ` of `B` with `|μ - λ_i| ≤ ||E||`.
*Structure:* Rayleigh-Ritz perturbation theory; finite dimension (matrix perturbation theorem).

**Proposition 4 (Ritz values are convex combinations of eigenvalues).** `A = Q Λ Q^T`,
`T_k = Z_k Θ_k Z_k^T`, `V̄_k = Q^T V_k`, `W_k = V̄_k Z_k = (w_1^{(k)} .. w_k^{(k)})`,
`w_j^{(k)} = (ω_{1,j}^{(k)}, ..., ω_{n,j}^{(k)})^T`. Then `Θ_k = W_k^T Λ W_k`,
`θ_j^{(k)} = Σ_l (ω_{l,j}^{(k)})^2 λ_l`, `Σ_l (ω_{l,j}^{(k)})^2 = 1`.
*Sketch:* `T_k = V_k^T A V_k`, `W_k^T W_k = Z_k^T V_k^T Q Q^T V_k Z_k = I`.

**Theorem 5 (Persistence theorem, Paige 1971/1980).** Let `t < k`. Then
`min_j |θ_s^{(t)} - θ_j^{(k)}| ≤ β_{t+1} |ζ_{t,s}^{(t)}|`.
I.e. once an eigenvalue is approximated at step `t` with small residual it stays approximated to
comparable accuracy by some Ritz value at every later step, for every unreduced symmetric
tridiagonal extension `T_k` of `T_t`. *Structure:* tridiagonal-matrix (Wilkinson) argument only.

**Definition 6.** An eigenvalue `θ_s^{(t)}` of `T_t` is *stabilized to within* `δ = β_{t+1} |ζ_{t,s}^{(t)}|`.

**Theorem 7 (Paige).** `(θ_s^{(t)} - θ_j^{(k)}) (z_j^{(k)})^T [z_s^{(t)} ; 0] = β_{t+1} ζ_{t,s}^{(t)} ζ_{t+1,j}^{(k)}`.
Consequence for `k = t+1` (interlacing: `j = s` or `s+1`):
`β_{t+1} |ζ_{t,s}^{(t)} ζ_{t+1,j}^{(t+1)}| ≤ |θ_s^{(t)} - θ_j^{(t+1)}|`; close Ritz values at
consecutive steps indicate convergence (further: Wülling 2005).
*Structure:* multiply the identity `T_{t+1..}` block structure by eigenvectors; tridiagonal algebra.

## C.2 Section 3: the conjugate gradient algorithm in exact arithmetic

### C.2.1 CG from Lanczos (§3, §3.1)

Hypotheses: `A` spd, `x_0` given, `r_0 = b - A x_0`, `v_1 = r_0/||r_0||`.
* Seek `x_k = x_0 + V_k y_k` with `r_k ⊥ V_k` (Galerkin); then `0 = V_k^T r_k = V_k^T r_0 - T_k y_k`
  gives **(3.1)** `T_k y_k = ||r_0|| e_1`, `x_k = x_0 + V_k y_k`; `r_n = 0` (direct method in ≤ n steps).
* `r_k = r_0 - (V_k T_k + β_{k+1} v_{k+1} e_k^T) y_k = -β_{k+1} (y_k, e_k) v_{k+1}
  = (-1)^k v_{k+1} ||r_0|| β_2 ... β_{k+1} / det(T_k)` (adjugate of `T_k`).
* **Hestenes-Stiefel CG (3.2):** `p_0 = r_0`; for `k ≥ 1`:
  `γ_{k-1} = ||r_{k-1}||^2 / (p_{k-1}, A p_{k-1})`, `x_k = x_{k-1} + γ_{k-1} p_{k-1}`,
  `r_k = r_{k-1} - γ_{k-1} A p_{k-1}`, `δ_k = ||r_k||^2/||r_{k-1}||^2`, `p_k = r_k + δ_k p_{k-1}`.
* Facts (HS, by induction): `K_k(v_1, A) = span{r_0..r_{k-1}} = span{p_0..p_{k-1}}`;
  `(r_i, r_j) = 0`, `(p_i, A p_j) = 0` for `i ≠ j`; hence `r_k ⊥ K_k` and (3.1) ≡ (3.2) up to signs.
* **Three-term recurrence (3.3):** `-(1/γ_{k-1}) r_k = A r_{k-1} - (1/γ_{k-1} + δ_{k-1}/γ_{k-2}) r_{k-1}
  + (δ_{k-1}/γ_{k-2}) r_{k-2}`; comparison with (2.1) gives **(3.4)** `v_{k+1} = (-1)^k r_k/||r_k||`.
* **Coefficient relations:** `α_k = 1/γ_{k-1} + δ_{k-1}/γ_{k-2}` (`δ_0 = 0`, `γ_{-1} = 1`),
  `β_{k+1} = sqrt(δ_k)/γ_{k-1}`. Conversely CG = Lanczos + `L D L^T` of `T_k` (Householder 1964,
  Paige-Saunders 1975).
* Termination: `v̂_{m+1} = 0` ⇒ `r_0 ∈ A K_m` ⇒ `r_m = 0`: Lanczos termination = CG convergence.
* **Indefinite `A` (symmetric nonsingular):** `x_k = x_0 + ||r_0|| V_k T_k^{-1} e_1` exists iff `T_k`
  nonsingular; `T_m` (final) is nonsingular; if `T_k` and `T_{k+1}` are both singular then
  `T_{k+2}..T_m` are singular (contradiction), so **at least every second `T_k` is nonsingular** and
  the CG iterate exists at least every second step; (3.2) breaks down when `T_k` is singular
  (Cholesky fails). Paige-Saunders compute the CG iterates via SYMMLQ's auxiliary iterates and
  propose MINRES for indefinite systems; cf. Fridman 1963 (OD), Luenberger 1969/70, Fletcher 1976,
  Stoer-Freund 1982 (STOD).

### C.2.2 Orthogonality and optimality (§3.2)

* **(3.5)** `||x - x_k||_A = min_{u ∈ x_0 + K_k(v_1,A)} ||x - u||_A`; equivalently
  `(r_j, A(x - x_k)) = (r_j, r_k) = (v_{j+1}, r_k) = 0` for `j = 0..k-1`, which uniquely determines the
  Galerkin iterate. *Structure:* inner product, `A ≻ 0`.
* Error expansion (CG terminating at `m` with `x_m = x`): `x - x_k = Σ_{l=k+1}^m γ_{l-1} p_{l-1}`,
  `||x - x_k||_A^2 = Σ_{l=k+1}^m γ_{l-1} ||r_{l-1}||^2` (using `(p_i, A p_j) = 0`, `γ_{l-1}(p_{l-1}, A p_{l-1}) = ||r_{l-1}||^2`).
* **(3.6)** `||x - x_0||_A^2 = Σ_{l=1}^k γ_{l-1} ||r_{l-1}||^2 + ||x - x_k||_A^2`, `k = 1..m`.
  Derived here from *global* A-orthogonality (not preserved numerically); a local proof is given
  under Theorem 11.
* **Polynomial formulation:** `r_k = φ_k(A) r_0`, `φ_k(0) = 1`, `x - x_k = φ_k(A)(x - x_0)`;
  `φ_k(λ) = p_{k+1}(λ)/p_{k+1}(0)` (spd ⇒ roots of `p_k` ≥ `λ_1 > 0` ⇒ `p_k(0) ≠ 0`).

**Theorem 8 (spectral expressions).** With `ω_i = |(v_1, q_i)|^2`, `v_1 = r_0/||r_0||`:
`||r_k||^2/||r_0||^2 = Σ_i ω_i Π_{l=1}^k (1 - λ_i/θ_l^{(k)})^2`,
`||x - x_k||^2/||r_0||^2 = Σ_i ω_i λ_i^{-2} Π_l (1 - λ_i/θ_l^{(k)})^2`,
`||x - x_k||_A^2/||r_0||^2 = Σ_i ω_i λ_i^{-1} Π_l (1 - λ_i/θ_l^{(k)})^2`.
*Sketch:* `x - x_0 = A^{-1} r_0`, `φ_k(λ_i)^2 = p_{k+1}(λ_i)^2/p_{k+1}(0)^2 = Π_l (1 - λ_i/θ_l)^2`.
*Structure:* spectral decomposition (finite dim; extends to spectral measure).
* **(3.7)** `||x - x_k||_A ≤ min_{φ ∈ π_k} max_i |φ(λ_i)| ||x - x_0||_A` (`π_k` = degree ≤ k, `φ(0) = 1`);
  worst-case bound, sharp for some initial vector (Greenbaum 1979; (3.8) explicit minimax value on a
  subset `{μ_1..μ_{k+1}}` of eigenvalues). **(3.9)** Chebyshev bound
  `||x - x_k||_A/||x - x_0||_A ≤ 2 [((√κ-1)/(√κ+1))^k + ((√κ+1)/(√κ-1))^k]^{-1} ≤ 2 ((√κ-1)/(√κ+1))^k`,
  `κ = λ_n/λ_1` (Meinardus 1963, Kaniel 1966, Daniel 1967). Convergence depends on the whole
  spectrum, not just `κ`.

### C.2.3 Quadratic forms and error identities (§3.3)

* `||ε_k||_A^2 = (A^{-1} r_k, r_k)`, `ε_k = x - x_k`; quadratic forms `u^T f(A) u = Σ_i ω_i f(λ_i)
  = ∫ f dω =: I[f]` (WLOG `||u|| = 1`); polarization `u^T f(A) v = ½[u^T f(A) u + v^T f(A) v - (u-v)^T f(A)(u-v)]`.
* **Quadrature with prescribed nodes:** `∫ f dω = Σ_{j=1}^k ω_j^{(k)} f(θ_j^{(k)}) + Σ_{l=1}^M ν_l^{(M)} f(τ_l^{(M)}) + R_{k,M}[f]`,
  `R_{k,M}[f] = f^{(2k+M)}(η)/(2k+M)! ∫ Π_l (λ - τ_l) Π_j (λ - θ_j)^2 dω`, `λ_1 < η < λ_n`;
  `M = 0` Gauss, `M = 1` with `τ_1 ∈ {λ_1, λ_n}` Gauss-Radau, `M = 2` Gauss-Lobatto.
* **Gauss rule in matrix form:** `L_G^{(k)}[f] = Σ_j ω_j^{(k)} f(θ_j^{(k)}) = (e_1)^T f(T_k) e_1`,
  `R_G^{(k)}[f] = f^{(2k)}(η)/(2k)! ∫ Π_j (λ - θ_j^{(k)})^2 dω`. If `f^{(2k)} > 0` on `(λ_1, λ_n)` then
  `L_G[f] ≤ I[f]` (lower bound); applies to `f(λ) = 1/λ`. So
  `||ε_0||_A^2 = (A^{-1} r_0, r_0) = ||r_0||^2 (T_n^{-1} e_1, e_1)`, `L_G^{(k)}[1/λ] = (T_k^{-1} e_1, e_1)`,
  `||r_0||^2 [(T_n^{-1} e_1, e_1) - (T_k^{-1} e_1, e_1)] = ||r_0||^2 R_G^{(k)}[1/λ] ≥ 0`.

**Theorem 9 (A-norm of the CG error as a Gauss remainder; Dahlquist-Golub-Nash 1978).**
`||ε_k||_A^2 = ||r_0||^2 R_G^{(k)}[1/λ] = ||r_0||^2 [(T_n^{-1} e_1, e_1) - (T_k^{-1} e_1, e_1)]
= ||r_0||^2 [Σ_{j=1}^n (z_j^{(n)}, e_1)^2/λ_j - Σ_{j=1}^k (z_j^{(k)}, e_1)^2/θ_j^{(k)}]`.
*Hypotheses:* `A` spd, exact arithmetic, CG (3.1) (`x_0` arbitrary).
*Sketch (new proof):* `||ε_k||_A^2 = (A^{-1} r_0, r_0) - 2 (r_0, V_k y_k) + (A V_k y_k, V_k y_k)`;
`(r_0, V_k y_k) = ||r_0||^2 (T_k^{-1} e_1, e_1)` and `(A V_k y_k, V_k y_k) = (T_k y_k, y_k) = ||r_0||^2 (T_k^{-1} e_1, e_1)`.
*Structure:* first identity needs only `V_k^T A V_k = T_k`, orthonormality, `A` invertible (Hilbert
space OK with `(A^{-1} r_0, r_0)` in place of the `T_n` term); the `T_n`/spectral forms need finite dim.

**Theorem 10.** For each `k` there is `ξ_k ∈ [λ_1, λ_n]` with
`||ε_k||_A^2 = ||r_0||^2 ξ_k^{-(2k+1)} Σ_i ω_i Π_{j=1}^k (λ_i - θ_j^{(k)})^2`.
*Sketch:* Gauss remainder with `f = 1/λ`, `f^{(2k)}(ξ)/(2k)! = ξ^{-(2k+1)}`. Consequence: when a Ritz
value has converged to `λ_i`, the component of the initial residual along `q_i` is eliminated.

**Theorem 11 (HS 1952, Thm 6:1).** `||ε_0||_A^2 = Σ_{l=1}^k γ_{l-1} ||r_{l-1}||^2 + ||ε_k||_A^2`;
hence the Gauss quadrature is `L_G^{(k)}[1/λ] = (T_k^{-1} e_1, e_1) = Σ_{l=1}^k γ_{l-1} ||r_{l-1}||^2/||r_0||^2`.
*Local proof (Strakos-Tichy 2002), independent of global orthogonality:*
`||ε_k||_A^2 - ||ε_{k+1}||_A^2 = ||x_{k+1} - x_k||_A^2 + 2 (x - x_{k+1})^T A (x_{k+1} - x_k)
= γ_k^2 (p_k, A p_k) + 2 γ_k (r_{k+1}, p_k) = γ_k ||r_k||^2`, using only `(r_{k+1}, p_k) = 0` and
`γ_k (p_k, A p_k) = ||r_k||^2`. *Structure:* inner product + local orthogonality; valid in Hilbert
space; this independence is what makes the finite-precision analysis of §5.3 possible.

**Theorem 12 (HS 1952, Thm 6:3).**
`||ε_k||^2 - ||ε_{k+1}||^2 = (||ε_k||_A^2 + ||ε_{k+1}||_A^2) / μ(p_k)`, `μ(p_k) = (p_k, A p_k)/||p_k||^2`.
Consequently the Euclidean norm of the CG error is strictly decreasing. *Structure:* inner product
identities of CG (uses `x - x_k = Σ γ p`-type expansions or local relations) [proof not reproduced].

**Theorem 13 (Meurant 2003).**
`||ε_k||^2 = ||r_0||^2 [(e_1, T_n^{-2} e_1) - (e_1, T_k^{-2} e_1)] - 2 [(e_k, T_k^{-2} e_1)/(e_k, T_k^{-1} e_1)] ||ε_k||_A^2`
[uncertain placement of the last factor]; relates the Euclidean error to eigenvalues and Ritz values.
*Structure:* finite dim (`T_n`).

## C.3 Section 4: the Lanczos algorithm in finite precision (statements only)

### C.3.1 Model (§4.1)

Standard model (Higham 2002): `fl(x op y) = (x op y)(1 + δ)`, `|δ| ≤ u_M`, `op ∈ {+,-,*,/}`,
`u_M = ½ β^{1-t}` (unit roundoff; IEEE double `u_M = 2^{-53} ≈ 1.11e-16`, machine epsilon
`ε_M = 2^{-52}`). Paige's notation: products `Π(1 + δ_i) = 1 + ε_p` with `|ε_p - 1| ≤ p u_M`
[i.e. bounded by `p u_M` up to higher order]; `fl(x^T y) = x^T y + n ε |x^T| |y|`,
`fl(x^T x) = (1 + n ε) x^T x`, `fl(A x) = (A + δA) x`, `|δA| ≤ m_A ε |A|` (`m_A` = max nonzeros per
row), `||δA|| ≤ m_A σ ε ||A||` with `|| |A| || = σ ||A||`.
Example matrix D30: `λ_i = λ_1 + (i-1)/(n-1) (λ_n - λ_1) ρ^{n-i}`, `n = 30`, `λ_1 = 0.1`, `λ_n = 100`,
`ρ = 0.8`; `V_30^T V_30` far from identity (Fig 4.1).

### C.3.2 Paige's theory (§4.2)

**Theorem 14 (Paige 1976; local errors).** Let `ε_0 = 2(n+4) ε_M < 1/12`, `ε_1 = 2(7 + m_A σ) ε_M`
[constants as printed; Paige 1980 uses twice these]. The computed Lanczos quantities satisfy
`A V_k = V_k T_k + β_{k+1} v_{k+1} e_k^T + δV_k`, and for `j = 1..k`:
`|(v_{j+1})^T v_{j+1} - 1| ≤ ε_0`, `||δv_j|| ≤ ε_1 ||A||`, `β_{j+1} |(v_j)^T v_{j+1}| ≤ 2 ε_0 ||A||`,
`|β_j^2 + α_j^2 + β_{j+1}^2 - ||A v_j||^2| ≤ 4 j (3 ε_0 + ε_1) ||A||^2`.
(Floating-point model of §4.1; quantities: `n`, `m_A`, `||A||`, step `k`.)

**Theorem 15 (Paige; propagation of loss of orthogonality).** Write
`V_k^T V_k = R_k^T + diag((v_j)^T v_j) + R_k` with `R_k` strictly upper triangular. Then
`T_k R_k - R_k T_k = β_{k+1} V_k^T v_{k+1} e_k^T + H_k` with `H_k` upper triangular,
`|(H_k)_{1,1}| ≤ 2 ε_0 ||A||`, `|(H_k)_{j,j}| ≤ 4 ε_0 ||A||`, `|(H_k)_{j-1,j}| ≤ 2(ε_0 + ε_1) ||A||`,
`|(H_k)_{i,j}| ≤ 2 ε_1 ||A||` (`i ≤ j-2`); `||H_k||_F ≤ k ε_2 ||A||`, `ε_2 = √2 max(6 ε_0, ε_1)` [uncertain].
[The paper calls the perturbation matrix `R_k` too; renamed `H_k` here.]

**Theorem 16 (Paige; loss of orthogonality ⇒ convergence).** With `ε_{l,j}^{(k)} = (z_l^{(k)})^T H_k z_j^{(k)}`:
`|ε_{l,j}^{(k)}| ≤ k ε_2 ||A||` and `(x_j^{(k)})^T v_{k+1} = -ε_{j,j}^{(k)} / (β_{k+1} ζ_{k,j}^{(k)})`
[sign/absolute value uncertain]. Hence `v_{k+1}` can lose orthogonality only against Ritz vectors
whose `β_{k+1} |ζ_{k,j}^{(k)}|` is tiny (∝ `k ε_2 ||A||`): *orthogonality is lost only in directions
of converged Ritz vectors*. *Sketch:* multiply Theorem 15's identity by eigenvectors of `T_k`:
`(θ_l - θ_j)(z_l)^T R_k z_j = β_{k+1} (x_l^{(k)})^T v_{k+1} ζ_{k,j} + ε_{l,j}`; take `l = j`.

Auxiliary bounds (Paige 1980, (3.15)): `min_i |λ_i - θ_j^{(k)}| ≤ (β_{k+1} |ζ_{k,j}| (1 + ε_0) + k ε_1 ||A||) / ||x_j^{(k)}||`;
Ritz vector accuracy (Strakos-Greenbaum Lemma 3.4): `min_{l ≠ i} ||x_j - (x_j, q_i) q_i|| ≤ (β_{k+1}|ζ_{k,j}| + k ε_1 ||A||)/|λ_l - θ_j|` [garbled].

**Theorem 17 (Paige 1980, pp. 241-249).** For a Ritz value `θ_j^{(k)}` of the computed `T_k`:
`min_i |λ_i - θ_j^{(k)}| ≤ max{ 2.5 (β_{k+1} |ζ_{k,j}^{(k)}| + k^{1/2} ||A|| ε_1), [(k+1)^3 + 3 n^2] ||A|| ε_2 }`.
No spurious Ritz values: a stabilized Ritz value is always close to an eigenvalue of `A`, however
many other Ritz values are nearby.

**Theorem 18.** If `β_{k+1} |ζ_{k,j}^{(k)}| ≤ √3 k^2 ||A|| ε_2` then there exist `1 ≤ t ≤ k`, `1 ≤ s ≤ t`
with `β_{t+1} |ζ_{t,s}^{(t)}| ≤ √3 t^2 ||A|| ε_2`, `||x_s^{(t)}|| ≥ 1/2`, `min_i |λ_i - θ_s^{(t)}| ≤ 5 t^2 ||A|| ε_2`,
and `(θ_s^{(t)}, x_s^{(t)})` is an exact eigenpair of a matrix within `5 t^2 ||A|| ε_2` of `A`.
Also (Paige (3.21)): if `min_{l ≠ j} |θ_j^{(k)} - θ_l^{(k)}| ≥ k^{5/2} ||A|| ε_2` then `0.42 < ||x_j^{(k)}|| < 1.4`.

**Theorem 19 (Paige 1980, Thm 4.1).** If `n(3 ε_0 + ε_1) ≤ 1`, at least one eigenvalue of `T_n` is
within `(n+1)^3 ||A|| ε_2` of an eigenvalue of `A`, and there are `1 ≤ s ≤ t ≤ n` with
`β_{t+1} |ζ_{t,s}^{(t)}| ≤ 5 t^2 ||A|| ε_2`.

**Theorem 20 (Scott 1979, Thm 4.3).** `A` symmetric with distinct eigenvalues, `δ_A = min_{l≠i} |λ_i - λ_l|`.
There is a starting vector `v_1` (constructed via (4.1): weights `ω_l = -ĉ/(χ_{n-1}(λ_l) χ_n'(λ_l))`
with prescribed Ritz values of `T_{n-1}`, e.g. midpoints between eigenvalues) such that for exact
Lanczos every Ritz pair at every step `j < n` has residual norm `> δ_A/4`; hence (by persistence) no
Ritz value stabilizes before step `n` and, numerically, essentially no loss of orthogonality.
Consequences: (i) orthogonality is lost only in converged Ritz directions; (ii) loss of
orthogonality depends strongly on `v_1`.

Rayleigh-quotient bound (Paige (3.48)): `λ_min(A) - k^{5/2} ||A|| ε_2 ≤ θ_j^{(k)} ≤ λ_max(A) + k^{5/2} ||A|| ε_2`.

**Theorem 21 (Paige 1980, Thm 4.2; backward stability before convergence).** If at step `k`
(4.2) `β_{l+1} |ζ_{l,j}^{(l)}| ≥ √3 k^2 ||A|| ε_2` for all `1 ≤ j ≤ l ≤ k`, then `||R_k||_F < 1/12`, all
singular values of `V_k` lie in `(0.41, 1.6)`, and there exists `A^{(k)}` within `(3k)^{1/2} ||A|| ε_2`
[uncertain] of `A` such that `v_1, ..., v_l` span the Krylov subspaces of `A^{(k)}` with `v_1`, for
`l = 1..k+1`. Until a Ritz value stabilizes to within `√3 k^2 ||A|| ε_2`, finite precision Lanczos
behaves like Lanczos with full (MGS) reorthogonalization.

### C.3.3 Greenbaum's backward-like analysis (§4.3)

Idea: the computed `T_k` equals `T_k` of exact Lanczos on any `k x k` `B` with the same eigenvalues
and starting vector components `Z_k^T e_1`; require in addition that all eigenvalues of `B` lie near
eigenvalues of `A` and that the total weight near each `λ_i` equals `ω_i`. Equivalent to extending
`T_k` to a larger unreduced symmetric tridiagonal `T_{k+K}` with eigenvalues near those of `A`
(`B = T_{k+K}`, `v_B^1 = e_1`). Greenbaum constructs it by a hypothetical continuation with exact
orthogonalization against a cleverly chosen orthonormal set `Y_{k-m_k}` (avoiding converged Ritz
directions), reaching `β_{k+K+1} = 0` with `K = n + m_k - k`:
`A V_{k+K} = V_{k+K} T_{k+K} + F_{k+K}`, with small perturbation columns `f_k..f_{k+K}`.

**Theorem 22 (Greenbaum 1989).** The `T_k` generated at step `k` of finite precision Lanczos on
`(A, v_1)` equals the `T_k` of an exact Lanczos recurrence applied to an `(n + m_k) x (n + m_k)`
matrix `B` whose eigenvalues lie within `O((n + m_k)^3) max{ε_M ||A||, ||f_k||, ..., ||f_{n+m_k}||}` of
eigenvalues of `A`, where `f_j` are the smallest perturbations forcing some `β_{j+1} = 0` at or
before step `n + m_k`. (Strakos 1991, Thm 4.2: conversely every such `B` has an eigenvalue near each
`λ_i` with nonzero weight.) Extensions: Greenbaum-Strakos 1992 (a priori `B` by spreading
eigenvalues in tiny intervals), Lanczos phenomenon resolved by Druskin-Knizhnerman (every eigenvalue
eventually approximated), conjectures C1-C3 on clusters (Strakos-Greenbaum 1992) answered by
Wülling 2005: C1 yes (tight well-separated clusters of ≥ 2 Ritz values stabilize), C2 no, C3 yes
(weights stabilize), via contour integrals (4.3)-(4.4) of `χ_{k-1}/χ_k`.

### C.3.4 §4.4-4.6

* §4.4: Ritz values can be accurate even when the computed `T_k` entries have no correct digits
  (power of backward-like analysis).
* §4.5 (reorthogonalization): semi-orthogonality `||V_k^T v_{k+1}|| ≤ √ε_M` (4.5); selective
  reorthogonalization (against Ritz vectors with `β_{k+1}|ζ_{k,l}| < √k ε_M ||A||` [garbled]);
  partial reorthogonalization (Simon). **Theorem 23 (Simon 1984).** If some reorthogonalization
  maintains semi-orthogonality, then `T_k` is, up to a full perturbation of norm `O(ε ||A||)`, the
  orthogonal projection of `A` onto `span(V_k)`. Parlett 1992 Thm 4.4: extra full
  reorthogonalization helps only if semi-orthogonality was maintained.
* §4.6 (forward analysis via perturbed three-term recurrences; Meurant 2006, Zemke 2003):
  computed relation (4.6) `β̃_{k+1} ṽ_{k+1} = A ṽ_k - α̃_k ṽ_k - β̃_k ṽ_{k-1} + f_k`; projected onto
  eigenvectors (4.7). **Theorem 24:** the solution of the scalar recurrence
  `β_{k+1} s_{k+1} = (λ - α_k) s_k - β_k s_{k-1} + f_k` (`s_0 = 0`) is
  `s_{k+1} = p_{1,k+1}(λ) s_1 + Σ_{l=1}^k p_{l+1,k+1}(λ) f_l/β_{l+1}` with associated polynomials
  `p_{j,j-1} = 0`, `p_{j,j} = 1`, `β_{k+1} p_{j,k+1} = (λ - α_k) p_{j,k} - β_k p_{j,k-1}`.
  **Lemma 25:** `p_{j,k}(λ) = (-1)^{k-j} χ_{j,k-1}(λ)/(β_{j+1}...β_k)` (`χ_{j,k}` = char. polynomial of
  `T_k` with first `j-1` rows/columns deleted). **Theorem 26:**
  `ṽ_{k+1} = p̃_{1,k+1}(A) v_1 + Σ_l p̃_{l+1,k+1}(A) f_l/β̃_{l+1}`. **Theorem 27:** `ṽ_{k+1} - v_{k+1}`
  = terms from local errors `f_l` plus terms from coefficient differences `g_l(λ)` (4.10)-(4.11).
  **Theorems 28-29:** explicit inverse of the bidiagonal-plus-tridiagonal system `L_{k+1} s = [g; h]`
  in terms of `T_k^{-1}`; **Theorem 30:** the perturbation term is bounded by
  `C k ||h^{(i)}|| / (|v̄_i^1| min_j |θ_j^{(k)} - λ_i|)` when `(q_i, v_1) ≠ 0` — small while no Ritz value
  is close to `λ_i`. Empirical pattern: `|p̃_{1,k}(λ_i)|` decreases to `√ε_M` then rises to `O(1)`;
  each return to `O(1)` creates a new Ritz copy.

## C.4 Section 5: CG in finite precision (statements only)

* (5.1) perturbed CG recurrences with terms `δ_γ^{k-1}`, `δ_x^k`, `δ_r^k`, `δ_δ^k`, `δ_p^k` bounded in
  terms of `ε_M, n, ||A||` and the computed quantities (Strakos-Tichy 2002, (7.9)-(7.14)); local
  orthogonality `(r_{k+1}, r_k)`, `(r_{k+1}, p_k)`, `(p_{k+1}, A p_k)` bounded (depending also on `κ(A)`).
* **Theorem 31 (CG-Lanczos recurrence in finite precision).** With CG-Lanczos vectors
  `w_{k+1} = (-1)^k r_k/||r_k||`: `β_{k+1} w_{k+1} = A w_k - α_k w_k - β_k w_{k-1} + δ_w^k`, `k ≥ 2`,
  `α_k = 1/γ_{k-1} + δ_{k-1}/γ_{k-2}`, `β_{k+1} = sqrt(δ_k)/γ_{k-1}`, `γ_k = ||r_k||^2/(A p_k, p_k)`,
  `δ_k = ||r_k||^2/||r_{k-1}||^2` (coefficients from the computed vectors exactly), initial
  `w_1 = r_0/||r_0|| + δ_w^0`, `β_2 w_2 = A w_1 - α_1 w_1 - δ_w^1`.
* §5.2: Greenbaum's analysis applies: the `T_k` of finite precision CG equals that of exact CG for a
  matrix with eigenvalues in tiny intervals around those of `A`; residual norms coincide with those
  of the constructed exact recurrence; A-norm reduced at approximately the same rate (Greenbaum
  Thm 3). Delay of convergence at step `k` = rank deficiency (numerical rank) of the computed
  `W_k = (w_1..w_k)` (Paige-Strakos 1999). Bounds must use minimax polynomials on unions of tiny
  intervals (Notay 1993 for outliers).
* §5.3 error estimates: from Theorem 9/11 with `d` extra steps,
  `||ε_k||_A^2/||r_0||^2 = [(k+d)-th Gauss quadrature - k-th Gauss quadrature] + ||ε_{k+d}||_A^2/||r_0||^2`,
  so the difference of Gauss quadratures is a lower bound; proven valid in finite precision until
  `||ε_k||_A/||r_0|| ~ √ε_M` (Golub-Strakos 1994), stable implementation Golub-Meurant 1997.
  **(5.3) (Strakos-Tichy 2002):** in finite precision CG
  `||ε_k||_A^2 - ||ε_{k+1}||_A^2 = γ_k ||r_k||^2 + ν_k`, `ν_k` small (depends on the local loss of
  orthogonality between `r_{k+1}` and `p_k`). **(5.4)** `η_{k,k+d} = Σ_{l=k}^{k+d-1} γ_l ||r_l||^2`
  is a lower bound for `||ε_k||_A^2`, not significantly affected by rounding until
  `||ε_k||_A/||ε_0||_A ∝ ε_M`. Relative version: `||ε_k||_A^2/||x||_A^2 ≥ η_{k,d}/μ̄_{k+d}`,
  `μ̄_{k+d} = η_{0,k+d} + b^T x_0 + r_0^T x_0`, valid if `||x - x_0||_A ≤ ||x||_A` (choose
  `x_0 ← (b^T x_0/x_0^T A x_0) x_0` if needed). Choice of `d` is an open problem.
* §5.4 maximal attainable accuracy: recursive vs true residual;
  `||r_k - (b - A x_k)|| ≤ ||δ_r^0|| + Σ_{l ≤ k} (||δ_r^l|| + ||A δ_x^l||)` (Greenbaum 1989 Thm 2);
  **(5.5)** `||r_k - (b - A x_k)|| / (||A|| ||x||) ≤ O(k) ε_M (1 + max_{l ≤ k} ||x_l||/||x||)`
  (Sleijpen-van der Vorst-Fokkema 1994, Greenbaum 1994/1997). Since ideally `||x - x_k||` decreases,
  `||x_k|| ≤ 2 ||x|| + ||x_0||`, so CG attains high accuracy if `||A||` is not too large; three-term
  recurrence implementations are more vulnerable (Gutknecht-Strakos 2000: gap amplified by
  `max_{l<j≤k} ||r_j||^2/||r_l||^2`).
* §5.5: **Theorem 32/33:** finite precision CG residual
  `r_k = (-1)^k (||r_k||/||r_0||) p_{1,k+1}(A) r_0 + (-1)^k ||r_k|| Σ_l p_{l+1,k+1}(A) δ_w^l/β_{l+1}`;
  residual components along converged eigenvectors decrease then rise again (oscillations; less
  pronounced in `r_k` than in `w_{k+1}` because of the factor `||r_k||`).
  **Proposition 34 (Meurant 2006).** With `ε_k := A^{-1} r_k` for the recursive residual:
  `||ε_{k+1}||_A^2 = ||ε_k||_A^2 - γ_k ||r_k||^2 + ε_M C_k^1 ||r_k||^2 + ε_M^2 C_k^2 ||r_k||^2`, `|C_k^1|`,
  `|C_k^2|` bounded by quantities involving `||r_k||`, `||p_k||`.
  **Theorem 35.** If `κ(A) < 1/(ε_M |C_k^1|) + O(ε_M)` [uncertain] for all `k` then
  `||ε_{k+1}||_A < ||ε_k||_A` (strict decrease persists). Strict decrease without a condition-number
  restriction, and `r_k → 0` for the recursive residual, remain open.
* §6: conclusions (no theorems).

---------------------------------------------------------------------------------------------------

# Part D. Structural observations

## D.1 Unified notation table

| Object | Fong-Saunders (A) | Choi (B) | Meurant-Strakos (C) | suggested backbone name |
|---|---|---|---|---|
| operator / rhs | `A` spd `n x n`, `b`; solution `x` | `A` symmetric (Hermitian), `b`; `A x ≈ b` for LS | `A` symmetric (spd for CG), `b`, `x_0` arbitrary, `r_0` | `A : E →L[𝕜] E` self-adjoint, `b : E` |
| Krylov subspace | `K_k(A,b) = span{b,..,A^{k-1}b}` | `K_k(A,b)` (Def 2.1) | `K_k(v,A) = span{v,..,A^{k-1}v}`, `v = r_0/||r_0||` | `krylov A b k` (`Submodule`), nested, `dim ≤ k` |
| Lanczos vectors | `V_k = [v_1..v_k]`, `v_1 = b/||b||` | `V_k`, `v_0 = 0`, `β_1 v_1 = b` | `V_k = (v_1..v_k)`, `||v_1|| = 1`, `v_0 = 0`, `β_1 = 0` | orthonormal basis of `krylov` from Gram-Schmidt |
| coefficients | implicit | `α_k = v_k^T A v_k`, `β_{k+1} = ||p_k - α_k v_k - β_k v_{k-1}||` | `α_k = (A v_k, v_k)`, `β_{k+1} = ||v̂_{k+1}||` | `lanczosAlpha`, `lanczosBeta` |
| square tridiagonal | `T_ℓ` (`ℓ x ℓ`, at termination) | `T_k` (`k x k`) | `T_k` (`k x k`) | `T k : Matrix (Fin k) (Fin k) ℝ` |
| rectangular | printed `T_k` `(k+1) x k` "Hessenberg tridiagonal" (underbar lost) | `T̄_k = [T_k; β_{k+1} e_k^T]` | none (writes `V_k T_k + β_{k+1} v_{k+1} e_k^T`) | `Tbar k` |
| Lanczos relation | `A V_k = V_{k+1} T̄_k`; `A V_ℓ = V_ℓ T_ℓ` | (2.3), (2.4) at `β_{k+1} = 0` | `A V_k = V_k T_k + β_{k+1} v_{k+1} e_k^T` | same |
| termination index | `ℓ ≤ n` (`β_{ℓ+1} = 0` ⇔ `r_ℓ = 0` for CG/CR) | `k` with `β_{k+1} = 0`, `k ≤ min{rank A + 1, n}` | `m ≤ n`, `β_{m+1} = 0`; `m = n` ⇒ simple spectrum | `krylov A b (ℓ+1) = krylov A b ℓ` (invariant) |
| iterate / residual | `x_k = V_k y_k`, `r_k = b - A x_k`, `x_0 = 0` | same; `r_k = V_{k+1}(β_1 e_1 - T̄_k y_k)` | `x_k = x_0 + V_k y_k`; `r_k = (-1)^k ||r_k|| v_{k+1}` (CG) | `x k`, `r k` |
| error | `x - x_k`; energy norm `||.||_A` | `x - x_k`, `||.||_A` in Table 2.5 | `ε_k = x - x_k`, `||u||_A = (u, A u)^{1/2}` | `err k`, `Anorm` |
| QR of `T̄_k` | `Q_k [T̄_k β_1 e_1] = [[R_k, t_k],[0, φ_k]]` | (2.19)-(2.21), Givens `c_k, s_k`, `γ_k^{(1,2)}, δ^{(1,2)}, ε` | — | (implementation layer only) |
| QLP | `R_k P_k = L_k`, `W_k = V_k P_k`, `L_k u_k = t_k` | §3.2, `u_k`, `μ_k^{(i)}`, `w_k^{(i)}` | — | (implementation layer) |
| CG coefficients | `α = ρ/p^T q`, `β = ρ/ρ̄` | `α_k = ρ_{k-1}^2/δ_k`, `β_{k+1} = ρ_k^2/ρ_{k-1}^2`, directions `q_k` | `γ_{k-1} = ||r_{k-1}||^2/(p_{k-1},Ap_{k-1})`, `δ_k = ||r_k||^2/||r_{k-1}||^2`, `p_k` | `cgStep`, `cgBeta` |
| CR coefficients | `α_k = ρ_{k-1}/||q_{k-1}||^2`, `β_k = ρ_k/ρ_{k-1}`, `ρ_k = r_k^T A r_k` | Table 2.12: `α_k = μ_{k-1}/||w_{k-1}||^2`, `μ_k = r_k^T A r_k` | — | `crStep` |
| Ritz values | — | eigenvalues of `T_k` (implicit; `γ`'s of `L_k` ≈ singular values) | `θ_j^{(k)}`, eigvecs `z_j^{(k)}` (`ζ_{i,j}^{(k)}`), Ritz vectors `x_j^{(k)} = V_k z_j^{(k)}` | `ritz k` |
| residual polynomial | — | — | `φ_k`, `r_k = φ_k(A) r_0`, `φ_k(0) = 1`; Lanczos polys `p_k`, `χ_{j,k}` | `resPoly` |
| spectral measure | — | — | `ω(λ)`, weights `ω_l = |(v_1,q_l)|^2`, Gauss weights `ω_l^{(k)}` | spectral measure of `A` at `b/||b||` |
| pseudoinverse | — | `A^†`, min-length solution `A^† b` | — | `A^† b` = unique solution in `(ker A)^⊥` |
| norms | `||v||` 2-norm, `||A||` Frobenius | `||.||` 2-norm / Frobenius, `||.||_2` | Euclidean | `‖·‖` |
| unit roundoff | `ε` | `ε = 2^{-52}` | `u_M = 2^{-53}`, `ε_M = 2^{-52}` | (later phase) |

## D.2 Abstract Krylov subspace method specifications

All methods: `x_k ∈ S_k`, a `k`-dimensional (or `k+1`) nested subspace determined by `(A, b)`;
`r_k = b - A x_k`. The defining condition is an optimality or Galerkin condition; the Lanczos
machinery only *transports* the condition to a small problem on `T̄_k` via the isometry
`y ↦ V_k y` (`||V_k y|| = ||y||`, `A V_k y = V_{k+1} T̄_k y`, `||b - A V_k y|| = ||β_1 e_1 - T̄_k y||`).

1. **CG** (Hestenes-Stiefel). Subspace `K_k(A,b)` (or `x_0 + K_k(A, r_0)`). Condition (all
   equivalent for `A` self-adjoint positive definite): Galerkin `r_k ⊥ K_k`; `argmin_{K_k} ||x - u||_A`;
   `argmin_{K_k} φ(u) = ½(Au,u) - (b,u)`; `argmin_{K_k} ||r||_{A^{-1}}`; `T_k y_k = β_1 e_1`; residual
   polynomial minimizing `||φ(A) b||_{A^{-1}}` over `φ(0) = 1`, `deg ≤ k`. Assumptions: `A` spd
   (well-defined for positive semidefinite `A` with `b ∈ R(A)`; for indefinite `A` exists iff `T_k`
   nonsingular, at least every second step). Proven: `||x - x_k||_A` strictly ↓ (nesting);
   `||x - x_k||` ↓ (HS 6:3 / C-Thm 12); `||x_k||` ↑ (Steihaug, needs only `p_j^T A p_j > 0`);
   `r_k ∝ v_{k+1}`, `(r_i,r_j) = 0`, `(p_i,Ap_j) = 0`; `||r_k||` not monotone; identities C-Thm 9, 10,
   11, 13; spectral formulas C-Thm 8; bounds (3.7)-(3.9); `||r_k^C|| = ||r_k^M||/sqrt(1 - ||r_k^M||^2/||r_{k-1}^M||^2)`;
   `||A r_k||` recurrence (B-Prop 2.5); at termination `x_ℓ = A^† b` if `b ∈ R(A)` (D.3 below).
2. **CR** (Stiefel; Luenberger). Subspace `K_k(A,b)`. Condition: `argmin_{K_k} ||r||`, implemented
   by `A^2`-conjugate directions (`(Ap_i, Ap_j) = 0`) and `(r_i, A r_j) = 0`. Assumptions: `A` spd for
   the sign results; the recurrences work for symmetric `A` while `p_j^T A p_j ≠ 0`, `r_j^T A r_j ≠ 0`.
   Proven (A-Thm 2.1-2.5, 3.1): same iterates as MINRES on spd; `||x_k||` ↑, `||x - x_k||` ↓,
   `||x - x_k||_A` strictly ↓, `||r_k||` ↓, backward errors `||E_k||/||A||`, `||f_k||/||b||` ↓.
3. **MINRES** (Paige-Saunders). Subspace `K_k(A,b)`. Condition: `argmin_{u ∈ K_k} ||b - A u||`
   ⇔ `r_k ⊥ A K_k` ⇔ (self-adjoint) `A r_k ⊥ K_k` ⇔ `y_k = argmin ||T̄_k y - β_1 e_1||` ⇔ residual
   polynomial minimizing `||φ(A) b||` over `φ(0) = 1`. If `T̄_k` is rank-deficient (only possible at
   the final step and only when `b ∉ R(A)`), MINRES takes `y_k = [y_{k-1}; 0]` (B-Thm 2.27).
   Assumptions: `A` self-adjoint (nonsingular or singular, definite or indefinite). Proven:
   `||r_k|| = ||r_{k-1}|| s_k` ↓ (B-Lemma 2.18); `A r_k` and `||A r_k||` recurrences (B-Lemma 2.19);
   `||A x_k||` ↑ (B-Lemma 2.20); compatible `b ∈ R(A)` ⇒ terminates at `x_ℓ = A^† b` (B-Thm 2.25);
   incompatible ⇒ LS solution (`A r = 0`, `||r||` minimal) that is a `{2,3}`-inverse solution but
   not minimum-length (B-Thm 2.27, Example 3); on spd: `||x_k||` ↑, errors ↓, backward errors ↓
   (A-Thms 2.3-2.5, 3.1); on indefinite `A`, `||x_k||` not monotone (A-(4.2)) but "approximately"
   (MINRES-QLP decomposition); = GMRES = unpreconditioned QMR/SQMR on symmetric `A`; `||A||`, `κ`
   estimates (B-Lemmas 2.31-2.33).
4. **SYMMLQ** (Paige-Saunders). Subspace: `x_k ∈ K_{k+1}(A,b)`, more precisely `x_k ∈ A K_k(A,b)`.
   Condition: `y_{k+1}` = minimum-norm solution of `T̄_k^T y = β_1 e_1`, `x_k = V_{k+1} y_{k+1}`;
   equivalently `argmin_{u ∈ A K_k} ||x - u||` (minimum Euclidean error) with Galerkin `r_k ⊥ K_k`,
   `A r_k ⊥ K_{k-1}`. Assumptions: `A` self-adjoint, system compatible (breaks down otherwise,
   B-Prop 2.15, Lemma 2.13). Proven: `||x_k||^2 = ||x_{k-1}||^2 + ζ_k^2` ↑ (B-Lemma 2.14);
   `r_k ∈ span{v_{k+1}, v_{k+2}}` (B-Prop 2.11); CG iterate recovered as `x_k^C = x_k + (ζ_k s_k/c_k) w̄_{k+1}`
   with `||x_k^C|| ≥ ||x_k||` (B-Prop 2.16); null vector `w̄_k` at breakdown (B-Lemma 2.17).
5. **GMRES** (Saad-Schultz). Subspace `K_k(A,b)` via Arnoldi. Condition: `argmin_{K_k} ||b - A u||`,
   `y_k = argmin ||H̄_k y - β_1 e_1||`. Assumptions: any square `A` (no symmetry). Proven: `||r_k||` ↓;
   equals MINRES for symmetric `A`; singular compatible ⇒ Drazin-inverse solution in general
   (Ipsen-Meyer); restarted version may stagnate.
6. **MINRES-QLP** (Choi-Paige-Saunders). Subspace `K_k(A,b)`. Condition: `y_k` = minimum-norm
   element of `argmin_y ||T̄_k y - β_1 e_1||` (3.7); i.e. among all residual minimizers in `K_k`
   (they differ by `N(T̄_k)`-directions) take the one of minimum norm. Assumptions: `A`
   self-adjoint, any rank, compatible or not. Proven: coincides with MINRES when `T̄_k` has full
   column rank; `||r_k||` ↓ (B-Prop 3.2); `A r_k ⊥ K_k` with recurrences (B-Prop 3.3); at termination
   `x_k = A^† b` for both compatible and incompatible systems (B-Thm 3.1); `||A x_k||` ↑ (3.21);
   `||x_k|| = ||u_k||` with monotone dominant part `χ`; preconditioning destroys the min-length
   property (B-§3.4.2).
7. **LSQR** (Paige-Saunders 1982). Subspace `K_k(A^T A, A^T b)` via Golub-Kahan. Condition:
   `argmin ||b - A u||` over that subspace (= CG on `A^T A x = A^T b`); `y_k = argmin ||B̄_k y - β_1 e_1||`.
   Assumptions: any `m x n` `A`, any rank. Proven: converges to the minimum-length LS solution;
   (Fong) `||x_k||` ↑, `||x - x_k||` ↓, `||r - r_k||` ↓, `||r_k||` ↓. **LSMR** = MINRES on the normal
   equations (`||A^T r_k||` ↓ additionally).
8. **QMR / SQMR** (Freund-Nachtigal). Subspace `K_k(A, b)` via two-sided Lanczos (bases `V_k`,
   `W_k` biorthogonal). Condition: `y_k = argmin ||T̄_k y - β_1 e_1||` with unsymmetric tridiagonal
   `T̄_k` (quasi-minimal: not the true residual norm since `V_{k+1}` is not orthonormal).
   Assumptions: square `A`; SQMR for symmetric `A` (allows indefinite preconditioners). Proven
   (cited): equivalent to MINRES for symmetric `A` without preconditioning.
9. Mentioned only: CGLS/CGNE (CG on normal equations), CRAIG, Bi-CG, Bi-CGSTAB, CGS, TFQMR,
   AMRES, MINRES-L, CGI (CG with `δ_k = 0` stopping), and the Lanczos eigenvalue method
   (Ritz values `θ_j^{(k)}` with a posteriori bound `β_{k+1}|ζ_{k,j}^{(k)}|`).

## D.3 What holds in a general (real or complex) Hilbert space vs. what needs finite dimension

Let `E` be an inner product space over `ℝ` or `ℂ` (completeness needed only where noted),
`A : E → E` bounded self-adjoint, `b ∈ E`. Then:

**Purely inner-product / self-adjointness (no dimension assumption, no completeness):**
* Krylov subspaces are nested finite-dimensional subspaces; `dim K_{k+1} ≤ dim K_k + 1`; if
  `K_{k+1} = K_k` then `K_k` is `A`-invariant and all later `K_j = K_k`.
* Gram-Schmidt on `b, Ab, ...` gives the Lanczos vectors; the three-term recurrence, real `α_k`,
  `β_{k+1} ≥ 0`, `A V_k = V_{k+1} T̄_k`, `T_k = V_k^* A V_k` symmetric tridiagonal, `v_{k+1} = p_{k+1}(A) v_1`
  (C-(2.2)-(2.3)); orthonormal polynomial recurrence.
* Existence/uniqueness of the MINRES residual (orthogonal projection of `b` onto the
  finite-dimensional subspace `A K_k`); uniqueness of `x_k^M` when `A|_{K_k}` is injective;
  `||r_k^M||` non-increasing; `r_k ⊥ A K_k`, `A r_k ⊥ K_k`; the transport to
  `argmin ||T̄_k y - β_1 e_1||`; `||r_k|| = φ_k = β_1 s_1...s_k`, B-Lemmas 2.18-2.20, B-Prop 3.2-3.3
  (pure reflector algebra on `T̄_k` plus orthonormality of `V_{k+1}`).
* MINRES-QLP definition (minimum-norm minimizer in `R^k`) and the identity `||x_k|| = ||u_k||`.
* Galerkin/CG iterate exists and is unique whenever `(Av,v) > 0` for `0 ≠ v ∈ K_k` (finite-dim
  Lax-Milgram); characterization as `argmin ||x - u||_A` requires a solution `x` of `A x = b` to
  exist (true if `A` is coercive: `(Av,v) ≥ c||v||^2`, `E` complete, or simply `b ∈ R(A)`);
  `||x - x_k||_A` non-increasing by nesting; A-Thm 2.1 (CR orthogonality), A-Thm 2.2 (a)-(c);
  C-Thm 11 (local proof), C-Thm 12 (HS 6:3), C-Thm 9 first identity, the CG/Lanczos coefficient
  relations, `r_k ∝ v_{k+1}`, the polynomial formulation `r_k = φ_k(A) r_0`; Steihaug's
  `||x_k^C||` ↑ (local argument: `r_i^T p_j = ||r_i||^2` for `j ≥ i` ⇒ `p_i^T p_j > 0`);
  SYMMLQ's `||x_k||` ↑ (B-Lemma 2.14: orthogonal update); B-Prop 2.16 (CG point); Fong-Saunders
  backward-error formulas (3.2)-(3.6) and Thm 3.1 given monotone `||x_k||` and `||r_k||`;
  relation A-(4.1).
* Minimum-length solutions: for a compatible system the min-norm solution is the unique
  solution in `(ker A)^⊥ = closure(R(A^*)) = closure(R(A))`; `b ∈ R(A)` ⇒ `K_k(A,b) ⊆ R(A)`, so
  **any exact Krylov solution is the minimum-length solution** (abstract core of B-Thm 2.25, 3.1;
  needs only self-adjointness for `(ker A)^⊥ = closure R(A)`). At Lanczos termination
  `K_ℓ` is invariant, `A` restricts to a self-adjoint operator on a finite-dimensional space, and all
  of B-Thm 2.25/2.27/3.1 reduce to finite-dimensional statements inside `K_ℓ` (for the
  incompatible case the LS problem also reduces to `K_ℓ` since `K_ℓ^⊥` is invariant and `b ∈ K_ℓ`).
* C-Thm 1 (Gauss quadrature): a statement about orthogonal polynomials of any positive measure with
  finite moments; with the spectral measure `μ_{v_1}` of a bounded self-adjoint operator
  (`∫ f dμ_{v_1} = (f(A) v_1, v_1)`) all of C-§2.2 and the Gauss-quadrature form of C-Thm 9/10
  (`||ε_k||_A^2 = (A^{-1} r_0, r_0) - ||r_0||^2 (T_k^{-1} e_1, e_1)`) hold for coercive `A` on a Hilbert
  space (completeness needed for `A^{-1}`). Ritz values lie in the numerical range, hence in
  `[min σ(A), max σ(A)]` (C-Prop 4 in measure form). C-Thm 5, 7 are statements about unreduced
  symmetric tridiagonal matrices only.

**Need finite termination / finite dimension (as proven in the sources):**
* A-Thm 2.2(d)-(f), 2.3, 2.4, 2.5 (use `x_ℓ = x`, `P ⊆ Q` and finite orthonormal expansions; in a
  Hilbert space with coercive `A` they extend via convergence `x_k → x` and infinite orthonormal
  expansions, but that is extra work). Any statement "CG/MINRES terminates with the exact solution
  in `≤ n` steps".
* B-Prop 2.2, Cor 2.3, Thm 2.4 (rank, number of distinct eigenvalues), B-Lemmas 2.28-2.33 and
  Thm 2.29 (SVD, interlacing, Frobenius norm), B-Thm 2.34-2.35, B-(3.6) QLP estimates; the
  Moore-Penrose-based proofs of B-Thm 2.25/2.27/3.1 as written (matrix pseudoinverse; in Hilbert
  space `A^†` is bounded only if `R(A)` is closed).
* C-§2.1 a posteriori bound `min_i |λ_i - θ| ≤ β_{k+1}|ζ|` as stated with a spectral
  decomposition (in Hilbert space: `dist(θ, σ(A)) ≤ ||A x - θ x||` for unit `x`, still true);
  C-Thm 2/Cor 3 (matrix perturbation); C-Thm 8 as sums over eigenvalues (integral form is
  general); C-Thm 9's `T_n` form, C-Thm 13; the "every second `T_k` nonsingular" argument (uses `T_m`
  final); C-Thm 20 (Scott's construction, `n` distinct eigenvalues); all of C-§4-5 (floating
  point, `n`-dependent constants, matrices of size `n + m_k`).
* Complex Hermitian: B says all results extend "once `α_k` is typecast real"; A is stated for real
  spd only but every proof uses only `(u, A v) = (A u, v)`, real `α_k, β_k` and real inner products of
  real quantities — with `Re` inserted where needed (e.g. `||x_i||^2 - ||x_{i-1}||^2 = 2 α_i Re(x_{i-1}, p_{i-1}) + ...`,
  and `Re(x_{i-1},p_{i-1}) ≥ 0` follows since all the pairings in A-Thm 2.2 are real for Hermitian
  `A`), so the backbone can be stated over `RCLike 𝕜`.

## D.4 Black-box results used by Fong-Saunders (and where the other sources prove them)

1. **Luenberger 1970, Theorem 1** (→ A-Thm 2.1): CR orthogonality `(Ap_i, Ap_j) = 0` (`i ≠ j`),
   `(r_i, A p_j) = 0` (`j < i`). Provable directly by induction from the CR recurrences; not proved in
   B or C (B-Table 2.12 only lists CR).
2. **Steihaug 1983, Theorem 2.1**: for CG (`x_0 = 0`) on symmetric `A`, `||x_k||` strictly increasing
   while `p_j^T A p_j > 0`, `j ≤ k`. Used for the CG column of Table 5.1 and §4.2.
3. **Hestenes-Stiefel 1952**: Thm 4:3 (CG minimizes `||x - u||_A` over `x_0 + K_k`; = C-(3.5)),
   Thm 6:1 (`||ε_0||_A^2 = Σ γ_l ||r_l||^2 + ||ε_k||_A^2`; = C-Thm 11), Thm 6:3 (Euclidean error
   decreases; = C-Thm 12), Thms 7:2, 7:4, 7:5 (for the conjugate-residual variant: `||r_k||` ↓,
   `||x - x_k||_A` ↓, `||x - x_k||` ↓ and `||x - x_{k-1}^C|| > ||x - x_k^M||`).
4. **Paige-Saunders 1975** [18]: Lanczos-based derivation of CG/SYMMLQ/MINRES via choices of `y_k`;
   MINRES minimizes `||r_k||` over `K_k`; stability for symmetric nonsingular `A`; `||r_k||` ↓.
   Reproduced in B-§2.2 (Tables 2.3-2.4, Lemma 2.18) and C-§3.1.
5. **Freund-Golub-Nachtigal 1992** [9]: Krylov solvers as minimizers of convex functions on
   expanding subspaces; CG minimizes the quadratic form.
6. **Titley-Peloquin 2010** [25] (and Higham [12] for `β = 0`, `α = β` — Rigal-Gaches): optimal
   normwise relative backward error `ξ_k = ||r_k||/(α||A|| ||x_k|| + β||b||)` with minimizers
   `E_k = ((1-ω_k)/||x_k||^2) r_k x_k^T`, `f_k = -ω_k r_k`. Elementary (Cauchy-Schwarz + rank-one
   construction) but not proved in any of the three sources.
7. **Paige-Saunders 1982 (LSQR) rule S1** [19]: stopping rule `||r_k|| ≤ α||A|| ||x_k|| + β||b||`.
8. **Greenbaum 1997, Lemma 5.4.1** [10] and Titley-Peloquin [26]: `||r_k^C|| = ||r_k^M||/sqrt(1 - ||r_k^M||^2/||r_{k-1}^M||^2)`
   (Galerkin vs minimal residual). Follows from B-Prop 2.16(3) / the Givens structure
   (`||r_k^M|| = |s_k| ||r_{k-1}^M||`, `||r_k^C|| = ||r_k^M||/|c_k|`).
9. **Choi-Paige-Saunders 2011** [3], §5.3 and §6.5: MINRES-QLP factorization structure
   (`W_k = V_k P_k`, unchanged first `k-3` columns/components) and the norm-update formulas
   `χ^2 ← χ^2 + μ̂^2_{k-2}`, `||x_k^M||^2 = χ^2 + μ̃^2_{k-1} + μ̄^2_k`. Reproduced in B-§3.2-3.3.5.
10. **Stiefel 1955** [23], **Luenberger 1969/1970** [15,16]: CR and its indefinite extensions
    (hyperbolic pairs). **Choi 2006** [2]: SYMMLQ iterate lies in `K_{k+1}`. **Conn-Gould-Toint**
    [4]: trust-region context. **van der Vorst** [27, p.85]: "MINRES for indefinite systems".
11. Numerical black boxes: UF sparse collection [5]; `eigs` for condition numbers.

**Dependencies of Choi's chapter 2-3 results, for completeness:** Paige-Saunders 1975 (SYMMLQ/MINRES
properties, Props 2.11-2.16 "presented and succinctly proved in [81, §5]"), Saunders 1995
(subproblem framework, Tables 2.3-2.4), Golub-Van Loan (pseudoinverse Thm 2.24, SVD),
Ben-Israel-Greville (generalized inverses), Trefethen-Bau (Thm 2.34, Lemma 2.28), Thompson 1972
(Thm 2.29), Stewart 1999 (QLP, (3.6)), Sleijpen-van der Vorst-Modersitzki 2000 (MINRES rounding),
Paige 1976 (Lanczos local bound in §2.4.4), Saad (CR Alg. 6.20, GMRES), Demmel (classification),
Ipsen-Meyer 1998 (Drazin inverse), Bobrovnikova-Vavasis (MINRES-L, two-layered systems),
Gill-Murray-Ponceleon-Saunders (indefinite preconditioners), Larsen (MCGLS).

## D.5 Remarks for the backbone design

* The cleanest abstract layer: `residualMin A b k := argmin over K_k of ||b - A u||` (exists as a
  set; unique residual; unique iterate iff `A` injective on `K_k`), `galerkin A b k` (unique when `A`
  positive on `K_k`), `minErrorAK A b k` (SYMMLQ), and `minNormResidualMin A b k` (MINRES-QLP: the
  minimum-norm element of `residualMin`). Monotonicity of `||r_k^M||`, `||x - x_k^C||_A` and the
  termination-implies-pseudoinverse theorem follow at this layer from nesting, projections and
  `K_k ⊆ R(A)` respectively.
* The Lanczos layer provides the isometry `R^k ≅ K_k` and the identity
  `||b - A V_k y|| = ||β_1 e_1 - T̄_k y||`, transporting each abstract condition to `T̄_k`; all
  Givens/QLP/short-recurrence material (B-§2.2.2-2.2.3, §3.2) is implementation detail on top.
* The sign/monotonicity results specific to spd `A` (A-Thm 2.2-2.5, 3.1; Steihaug; HS 6:3) are the
  only ones needing the CR/CG *recurrences* (directions `p_k`, coefficients `α_k, β_k`) rather than
  the abstract minimizers; they use finite termination as proven.
* The polynomial/measure layer (C-§2.2, §3.3) is the natural home for error identities and
  convergence bounds; finite-precision results (C-§4-5) are separate and need a floating-point
  model plus `n`-dependent constants.
