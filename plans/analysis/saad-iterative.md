# Saad, *Iterative Methods for Sparse Linear Systems* (2nd ed., SIAM 2003) — theorem inventory for a Lean/Mathlib backbone

Source: pdftotext dump of the book (formulas garbled; statements below reconstructed from the text plus
knowledge of the book). Items marked `[uncertain]` are reconstructions I am not fully sure of.
Equation numbers `(6.7)` etc. are the book's.

## 0. Conventions used in this file

* `A ∈ 𝔽^{n×n}`, `𝔽 = ℝ` or `ℂ`. Saad writes most of Chapters 4–6 for **real** matrices but the
  Krylov theory is stated to carry over to ℂ with the Hermitian inner product (Section 6.5.9).
* `(x,y) = yᴴx` Euclidean inner product; `‖·‖₂`; `Aᴴ` conjugate transpose (`Aᵀ` when real).
* `Ran(P)`, `Null(P)`; `ρ(A)` spectral radius; `σ(A)` spectrum; `κ(A)=‖A‖‖A⁻¹‖`; `κ₂` for the 2-norm.
* "**positive definite**" (Saad's convention, Section 1.11): a **real** matrix with `(Au,u) > 0` for all
  real `u ≠ 0` — *no symmetry assumed*. SPD = symmetric + positive definite. HPD = Hermitian + `(Au,u)>0`.
* `(x,y)_B = (Bx,y)`, `‖x‖_B` for `B` SPD/HPD ("energy norm", "A-norm").
* `K_m(A,v) = span{v, Av, …, A^{m-1}v}` Krylov subspace; `P_k` = polynomials of degree ≤ k.
* `x*` exact solution, `r = b − Ax` residual, `d = x* − x` error. Note `A d = r`.
* "Uses:" lines list the structure a proof genuinely relies on, to guide the level of generality.

---

## 1. Background, Sections 1.1–1.10 (brief)

Notions used later: complex/real matrices, `Aᴴ`, eigenvalues and eigenvectors, characteristic and
**minimal polynomial** (Cayley–Hamilton is invoked in 6.2), similarity, unitary matrices, Hermitian,
skew-Hermitian, normal, positive-definite, projector, permutation, (block-)triangular, Hessenberg,
banded/tridiagonal matrices; vector inner products and `p`-norms; induced matrix norms, Frobenius norm,
consistency `‖AB‖ ≤ ‖A‖‖B‖`; `‖A‖₂ = ρ(AᴴA)^{1/2}`; subspaces, `Ran`, `Null`, rank–nullity,
orthogonal complements `Ran(A)^⊥ = Null(Aᴴ)`; Gram–Schmidt, modified Gram–Schmidt, Householder QR
(Algorithms 1.1–1.3); Rayleigh quotient and field of values.

Numbered items (statements condensed):

* Def 1.1 eigenvalue; Prop 1.2 nonsingular ⇔ invertible; Prop 1.3 `λ ∈ σ(A) ⇒ λ̄ ∈ σ(Aᴴ)`, and
  left/right eigenvectors for distinct eigenvalues are orthogonal.
* Prop 1.4 unitary matrices preserve the Euclidean inner product.
* Def 1.5 similarity; Thm 1.6 diagonalizable ⇔ `n` linearly independent eigenvectors;
  Prop 1.7 diagonalizable ⇔ every eigenvalue semisimple.
* Thm 1.8 **Jordan canonical form**; Thm 1.9 **Schur form** (`A = QRQᴴ`, `Q` unitary, `R` upper
  triangular); real Schur form (quasi-triangular) remarked.
* Thm 1.10 `A^k → 0 ⇔ ρ(A) < 1` (proof via Jordan form). Thm 1.11 `Σ A^k` converges ⇔ `ρ(A) < 1`,
  and then `I − A` invertible with `(I−A)⁻¹ = Σ A^k`. Thm 1.12 `lim ‖A^k‖^{1/k} = ρ(A)` for every
  matrix norm (Gelfand; proof via Jordan form, Exercise 10). Also `ρ(A) ≤ ‖A‖` for any consistent norm.
* Lemma 1.13 normal + triangular ⇒ diagonal; Thm 1.14 normal ⇔ unitarily diagonalizable;
  Lemma 1.15 `A` normal ⇔ every eigenvector of `A` is an eigenvector of `Aᴴ` (with conjugate
  eigenvalue) — used in the Faber–Manteuffel Lemma 6.23; Cor 1.16 normal with real spectrum ⇒
  Hermitian; Thm 1.17 field of values of a normal matrix = convex hull of spectrum; Prop 1.18 field of
  values is convex (Hausdorff–Toeplitz) and contains the spectrum; `ρ(A^k) = ρ(A)^k` (1.36).
* Thm 1.19 Hermitian ⇒ real spectrum; Thm 1.20 Hermitian ⇒ unitarily similar to a real diagonal
  matrix (orthonormal eigenbasis); Thm 1.21 **Courant–Fischer min–max** `λ_k = min_{dim S = n−k+1}
  max_{x∈S∖0} (Ax,x)/(x,x)` (eigenvalues in descending order); Thm 1.22 recursive Rayleigh-quotient
  characterization `λ_k = max{(Ax,x)/(x,x) : x ⊥ q_1,…,q_{k−1}}`; consequences (1.38)–(1.40):
  `λ_min(A) ≤ (Ax,x)/(x,x) ≤ λ_max(A)`, `λ_min = min RQ`, `λ_max = max RQ`.
* Def 1.23 entrywise partial order `A ≤ B`, nonnegative/positive matrices; Prop 1.24 basic properties
  (`0 ≤ A ≤ B ⇒ ‖A‖₁ ≤ ‖B‖₁`, `‖A‖_∞ ≤ ‖B‖_∞`, products/sums/powers of nonnegative matrices are
  nonnegative). Reducible/irreducible (permutation to block upper triangular).
* Thm 1.25 **Perron–Frobenius** (nonnegative irreducible ⇒ `ρ(A)` is a simple eigenvalue with a
  positive eigenvector; reducible ⇒ nonnegative eigenvector).
* Prop 1.26 `0 ≤ A ≤ B`, `C ≥ 0` ⇒ `AC ≤ BC`, `CA ≤ CB`; Cor 1.27 `A^k ≤ B^k`;
  Thm 1.28 `0 ≤ A ≤ B ⇒ ρ(A) ≤ ρ(B)` (via Thm 1.12 with the 1-norm);
  Thm 1.29 `B ≥ 0`: `ρ(B) < 1 ⇔ I−B` nonsingular with `(I−B)⁻¹ ≥ 0` (Neumann series + Perron–Frobenius).
* Def 1.30 **M-matrix** (`a_ii > 0`, `a_ij ≤ 0` off-diagonal, nonsingular, `A⁻¹ ≥ 0`);
  Thm 1.31 given signs, M-matrix ⇔ `ρ(I − D⁻¹A) < 1`; Thm 1.32 `a_ij ≤ 0` off-diag + nonsingular +
  `A⁻¹ ≥ 0` ⇒ `a_ii > 0` and `ρ(I−D⁻¹A) < 1`; Thm 1.33 `A ≤ B`, `b_ij ≤ 0` off-diag, `A` M-matrix ⇒
  `B` M-matrix (comparison theorem).

Uses (all of 1.8–1.10): finite dimension essentially everywhere (Jordan/Schur forms, Cayley–Hamilton,
entrywise order, Perron–Frobenius, graph irreducibility). Only Thm 1.11/1.12 have Banach-algebra
analogues (Neumann series; Gelfand's formula).

---

## 2. Section 1.11 Positive-Definite Matrices

Definitions. Real `A` is **positive definite** ("positive real") if `(Au,u) > 0 ∀ u ∈ ℝⁿ∖0` (1.48).
Remark: the definition must be restricted to real `u`; requiring `(Au,u)` real for all complex `u`
forces `A` Hermitian (Exercise 15). Decomposition (1.49)–(1.51) of any square complex matrix:
`A = H + iS`, `H = (A + Aᴴ)/2` (Hermitian part), `S = (A − Aᴴ)/(2i)` (Hermitian; `iS` is the
skew-Hermitian part). For real `A` and real `u`: `(Au,u) = (Hu,u)` (1.52).

**Theorem 1.34 (coercivity of real positive definite matrices).**
Let `A ∈ ℝ^{n×n}` be positive definite. Then `A` is nonsingular, and there is `α > 0` such that
`(Au,u) ≥ α ‖u‖₂²` for all real `u` (1.53); one may take `α = λ_min(H)`, `H = (A+Aᵀ)/2`.
* Uses: real inner product space; symmetric part; min-max/Rayleigh quotient bound for symmetric `H`
  (spectral theorem in finite dimension, or just compactness of the unit sphere).
* Proof: singular `A` gives `u ≠ 0` with `(Au,u)=0`; `(Au,u)=(Hu,u) ≥ λ_min(H)(u,u)` and `λ_min(H) > 0`
  since `H` is SPD.

**Theorem 1.35 (Bendixson-type localization).**
Let `A ∈ ℂ^{n×n}`, `H = (A+Aᴴ)/2`, `S = (A−Aᴴ)/(2i)`. Every eigenvalue `λ_j` of `A` satisfies
`λ_min(H) ≤ Re λ_j ≤ λ_max(H)` (1.54) and `λ_min(S) ≤ Im λ_j ≤ λ_max(S)` (1.55).
* Uses: Rayleigh quotient of a unit eigenvector, `λ = (Au,u) = (Hu,u) + i(Su,u)`; real-valuedness of
  Hermitian Rayleigh quotients; bounds (1.38)–(1.40). Works verbatim for bounded operators on a Hilbert
  space for eigenvalues (and, with the numerical range, for the whole spectrum).

Remarks in the section: the spectrum lies in the rectangle `[λ_min(H),λ_max(H)] × i[λ_min(S),λ_max(S)]`;
for real `A` the eigenvalues of `iS` are symmetric w.r.t. the real axis. For `B` SPD/HPD,
`(x,y)_B := (Bx,y)` (1.57) is an inner product (energy norm / A-norm). A non-Hermitian `A` may be
self-adjoint w.r.t. `(·,·)_B`: e.g. `A = B⁻¹C` or `A = CB` with `C` Hermitian, `B` HPD (used in Ch. 9
for PCG: `M⁻¹A` is `M`-self-adjoint and `A`-self-adjoint).

---

## 3. Section 1.12 Projection Operators

**Definition.** A projector is a linear `P : ℂⁿ → ℂⁿ` with `P² = P`.
Basic facts (proved inline): `I − P` is a projector; `Null(P) = Ran(I−P)` (1.58);
`Null(P) ∩ Ran(P) = {0}`; `ℂⁿ = Null(P) ⊕ Ran(P)`; conversely each direct-sum decomposition
`ℂⁿ = M ⊕ S` determines a unique projector with `Ran P = M`, `Null P = S`; `Px` is characterized by
`Px ∈ M`, `x − Px ∈ S`. Writing `L = S^⊥` (so `dim L = dim M = m` when `rank P = m`), `u = Px` is
characterized by `u ∈ M` (1.59) and `x − u ⊥ L` (1.60): "projector onto `M` orthogonal to `L`".

**Lemma 1.36.** Let `M, L ⊂ ℂⁿ` be subspaces of the same dimension `m`. TFAE:
(i) no nonzero vector of `M` is orthogonal to `L` (i.e. `M ∩ L^⊥ = {0}`);
(ii) for every `x ∈ ℂⁿ` there is a unique `u` with `u ∈ M` and `x − u ⊥ L`.
Then `Ran P = M`, `Null P = L^⊥`, and `Px = 0 ⇔ x ⊥ L` (1.62).
* Uses: finite-dimensional inner product space, dimension count `dim L^⊥ = n − m`, direct sums.
  (Hilbert-space version: `M` closed, `L` closed, `M ⊕ L^⊥ = H` needed; dimension counting fails in
  general — the equal-dimension hypothesis is what makes (i) ⇒ (ii) work.)
* Proof: (i) ⇔ `M ∩ L^⊥ = {0}` ⇔ `ℂⁿ = M ⊕ L^⊥` (dimensions) ⇔ unique decomposition `x = u + w`.

**Matrix representations (1.12.2).** `V = [v_1..v_m]` basis of `M`, `W = [w_1..w_m]` basis of `L`;
bases biorthogonal if `WᴴV = I` (1.63). Then `P = VWᴴ` (1.65); in general `P = V(WᴴV)⁻¹Wᴴ` (1.66),
where `WᴴV` is nonsingular iff `M ∩ L^⊥ = {0}` (stated; proof left).
* Uses: matrices/bases; the nonsingularity of `WᴴV` is exactly Lemma 1.36.

**Orthogonal vs oblique projectors (1.12.3).** `P` is orthogonal if `L = M`, i.e. `Null P = (Ran P)^⊥`,
characterized by `Px ∈ M`, `(I−P)x ⊥ M` (1.67). The adjoint `Pᴴ` is a projector,
`Null(Pᴴ) = Ran(P)^⊥` (1.69), `Null(P) = Ran(Pᴴ)^⊥` (1.70).

**Proposition 1.37.** A projector is orthogonal iff it is Hermitian (`P = Pᴴ`).
* Uses: (1.69)–(1.70) and uniqueness of a projector given its range and null space. Holds for bounded
  idempotents on Hilbert spaces (closed range).
* Orthogonal projector onto `M` with orthonormal basis `V`: `P = VVᴴ` (representation not unique;
  `V_1V_1ᴴ = V_2V_2ᴴ`).

**Properties (1.12.4).** For orthogonal `P`: `‖x‖₂² = ‖Px‖₂² + ‖(I−P)x‖₂²`, `‖Px‖₂ ≤ ‖x‖₂`, `‖P‖₂ = 1`
(if `P ≠ 0`), eigenvalues ⊂ {0,1}.

**Theorem 1.38 (best approximation).** `P` orthogonal projector onto `M`, `x ∈ ℂⁿ`:
`min_{y∈M} ‖x − y‖₂ = ‖x − Px‖₂` (1.71), attained at `y = Px`.
* Uses: Pythagoras in an inner product space; nothing finite-dimensional (Hilbert space, `M` closed).

**Corollary 1.39 (characterization of the minimizer).** `min_{y∈M}‖x−y‖₂ = ‖x−ỹ‖₂` iff `ỹ ∈ M` and
`x − ỹ ⊥ M`. (Used in Ch. 5 both for the Euclidean and for the `A`-inner product.)

---

## 4. Section 1.13 Basic Concepts in Linear Systems

**1.13.1 Existence.** For `Ax = b`: Case 1 `A` nonsingular ⇒ unique `x = A⁻¹b`; Case 2 `A` singular,
`b ∈ Ran A` ⇒ solution set `x_0 + Null A` (infinitely many); Case 3 `A` singular, `b ∉ Ran A` ⇒ none.

**1.13.2 Perturbation analysis** (no numbered theorem; the derivation is the content).
`A` nonsingular, `E` any matrix, `e` any vector. For `|ε|` small `A + εE` is nonsingular (Exercise 37;
Neumann series). Let `x(ε)` solve `(A+εE)x(ε) = b + εe` (1.74). Then
`x(ε) − x = ε (A+εE)⁻¹(e − Ex)`, so `x` is differentiable at 0 with `x'(0) = A⁻¹(e − Ex)` (1.75);
`‖x(ε)−x‖/‖x‖ ≤ ‖A⁻¹‖ (‖e‖/‖x‖ + ‖E‖) |ε| + o(ε)`, and using `‖b‖ ≤ ‖A‖‖x‖`:
`‖x(ε)−x‖/‖x‖ ≤ ‖A‖‖A⁻¹‖ (‖e‖/‖b‖ + ‖E‖/‖A‖) |ε| + o(ε)` (1.76).
**Definition:** condition number `κ(A) = ‖A‖‖A⁻¹‖` (norm-dependent; `κ_p`). Scaling invariance vs
determinant; Example 1.5: `A_n = I + α e_1 e_nᵀ` has all eigenvalues 1 but `κ_∞ = (1+|α|)²`.
Residual–error relation used for stopping criteria: `‖x − x̃‖/‖x‖ ≤ κ(A) ‖r‖/‖b‖`, `r = b − Ax̃`
(from `x − x̃ = A⁻¹r` and `‖b‖ ≤ ‖A‖‖x‖`).
* Uses: any normed space + consistent operator norm; Neumann series. Fully Banach-space general.

---

## 5. Chapter 4 Basic Iterative Methods (4.1, 4.2)

### 5.1 Definitions and algorithms (4.1)
Setting: `A ∈ ℝ^{n×n}` with nonzero diagonal, `b ∈ ℝⁿ`. Splitting `A = D − E − F` (4.2): `D` diagonal,
`−E` strict lower, `−F` strict upper part.

* **Jacobi** (4.4)/(4.5): `ξ_i^{(k+1)} = (β_i − Σ_{j≠i} a_ij ξ_j^{(k)})/a_ii`, i.e.
  `x_{k+1} = D⁻¹(E+F)x_k + D⁻¹b`; derived from annihilating `(b − Ax_{k+1})_i` using old components.
* **Gauss–Seidel** (4.7)/(4.8): `x_{k+1} = (D−E)⁻¹F x_k + (D−E)⁻¹b`; backward GS `(D−F)x_{k+1} = Ex_k + b`
  (4.9); symmetric GS = forward then backward sweep.
* **General splitting iteration** (4.10)–(4.11): `A = M − N`, `M` nonsingular, `M x_{k+1} = N x_k + b`.
  Jacobi `M = D`; GS `M = D − E`; backward GS `M = D − F`.
* **SOR** (4.12): splitting `A = (1/ω)(D − ωE) − (1/ω)(ωF + (1−ω)D)`;
  `(D − ωE)x_{k+1} = [ωF + (1−ω)D]x_k + ωb`; componentwise `ξ_i^{(k+1)} = ω ξ_i^{GS} + (1−ω)ξ_i^{(k)}`.
* **SSOR** (4.13)–(4.14): forward SOR half-step then backward SOR half-step;
  `x_{k+1} = G_ω x_k + f_ω`, `G_ω = (D−ωF)⁻¹(ωE + (1−ω)D)(D−ωE)⁻¹(ωF + (1−ω)D)`,
  `f_ω = ω(2−ω)(D−ωF)⁻¹D(D−ωE)⁻¹b`.
* **Block relaxation (4.1.1):** partition `A = (A_ij)` with square nonsingular diagonal blocks;
  block `D, E, F`; block Jacobi/GS/SOR are the same formulas with block `D, E, F`. Line relaxation.
  **General (overlapping) block Jacobi:** set-decomposition `S_1 ∪ … ∪ S_p = {1..n}` (overlaps allowed),
  `V_i = [e_{m_i(1)}, …, e_{m_i(n_i)}]` (prolongation), `W_i` = weighted columns with `W_iᵀV_i = I`
  (restriction); `A_ij = W_iᵀ A V_j`; `V_iW_iᵀ` is a projector onto `K_i = span V_i`;
  update (4.17): `ξ_i^{(k+1)} = ξ_i^{(k)} + A_ii⁻¹ W_iᵀ(b − Ax_k)`.
  **Algorithm 4.1 (general block Jacobi):** for each `i`: solve `A_ii δ_i = W_iᵀ(b − Ax_k)`, then
  `x_{k+1} = x_k + Σ_i V_i δ_i`. **Algorithm 4.2 (general block GS):** same but `x` updated immediately
  after each `i` (`x := x + V_i δ_i` using the current residual).
* **Iteration matrices / preconditioning (4.1.2):** `x_{k+1} = G x_k + f` (4.18) with
  `G_JA = I − D⁻¹A` (4.19), `G_GS = I − (D−E)⁻¹A` (4.20); for a splitting `G = M⁻¹N = I − M⁻¹A`,
  `f = M⁻¹b` (4.22)–(4.23). The fixed-point iteration solves `(I−G)x = f`, i.e. the **preconditioned
  system** `M⁻¹Ax = M⁻¹b`; preconditioners `M_JA = D`, `M_GS = D−E`, `M_SOR = (1/ω)(D − ωE)`,
  `M_SSOR = (1/(ω(2−ω)))(D − ωE)D⁻¹(D − ωF)` (4.24)–(4.27). Computing `w = M⁻¹Av` as `r = Av; solve Mw = r`,
  or `w = v − M⁻¹Nv`.

### 5.2 Convergence (4.2)
Consistency: if `x_{k+1} = Gx_k + f` converges, the limit satisfies `x = Gx + f` (4.29); with
`G = M⁻¹N`, `f = M⁻¹b` this is `Ax = b`. Error `d_k = x_k − x*` satisfies `d_k = G^k d_0` (4.30);
`x_{k+1} − x_k = G^k(f − (I−G)x_0)`.

**Theorem 4.1 (convergence of linear fixed-point iteration).** `G` square with `ρ(G) < 1` ⇒ `I − G` is
nonsingular and `x_{k+1} = Gx_k + f` converges for every `f` and `x_0`. Conversely, if the iteration
converges for every `f` and `x_0`, then `ρ(G) < 1`.
* Uses: Thm 1.10 (`G^k → 0 ⇔ ρ(G) < 1`, via Jordan form), Thm 1.11 (`I−G` nonsingular).
  In infinite dimension the forward direction holds for bounded operators (Gelfand formula gives
  `‖G^k‖ → 0`); the converse (pointwise convergence ⇒ `ρ<1`) is **false** in infinite dimension
  (e.g. left shift on ℓ²), so the "conversely" needs finite dimension (or uniform convergence).
* Proof: forward from (4.30); converse: convergence for all `x_0, f` ⇒ `G^k v → 0 ∀ v` ⇒ `ρ(G) < 1`.

**Corollary 4.2.** If `‖G‖ < 1` for some matrix norm, then `I−G` nonsingular and the iteration converges
for every `x_0`. Uses `ρ(G) ≤ ‖G‖`.

**Convergence factor/rate (inline).** `d_k = G^k d_0`; via the Jordan form with a single dominant
eigenvalue `λ` in a block of size `p`: `‖d_k‖ ≈ C |λ|^{k−p+1} binom(k,p−1)`. Specific convergence factor
`ρ = lim_k (‖d_k‖/‖d_0‖)^{1/k}`, convergence rate `τ = −ln ρ`; general convergence factor
`φ = lim_k (max_{x_0} ‖d_k‖/‖d_0‖)^{1/k} = lim_k ‖G^k‖^{1/k} = ρ(G)` (Thm 1.12). Uses Jordan form.

**Example 4.1 (Richardson iteration)** `x_{k+1} = x_k + α(b − Ax_k)` (4.31), `G = I − αA`. If
`σ(A) ⊂ [λ_min, λ_max]` real: eigenvalues of `G` in `[1−αλ_max, 1−αλ_min]`; if `λ_min < 0 < λ_max` it
diverges for every `α`; if `λ_min > 0`, converges iff `0 < α < 2/λ_max`;
`ρ(G) = max{|1−αλ_min|, |1−αλ_max|}`, minimized at `α_opt = 2/(λ_min + λ_max)` (4.33) with
`ρ_opt = (λ_max − λ_min)/(λ_max + λ_min)`. Uses: real spectrum (e.g. `A` diagonalizable with real
eigenvalues; the spectral-radius computation is exact for any such `A`).

**Definition 4.3 (regular splitting).** `A = M − N` with `M` nonsingular, `M⁻¹ ≥ 0`, `N ≥ 0` (entrywise).

**Theorem 4.4.** `M, N` regular splitting of `A`. Then `ρ(M⁻¹N) < 1` iff `A` is nonsingular and `A⁻¹ ≥ 0`.
(Hence the iteration (4.34) converges whenever `A` is an M-matrix and the splitting is regular.)
* Uses: entrywise nonnegativity, Perron–Frobenius (Thm 1.25/1.29), `A = M(I − G)`, identity
  `A⁻¹N = (I−G)⁻¹G` (4.36). Strictly matrix/nonnegativity theory; finite-dimensional.
* Proof: (⇒) Thm 1.29 gives `(I−G)⁻¹ ≥ 0`, so `A⁻¹ = (I−G)⁻¹M⁻¹ ≥ 0`. (⇐) `G ≥ 0`, Perron eigenvector
  `x ≥ 0`, `Gx = ρ(G)x`; then `A⁻¹Nx = ρ/(1−ρ) x ≥ 0` forces `0 ≤ ρ < 1` (`ρ ≠ 1` since `I−G` nonsingular).

**Definition 4.5 (diagonal dominance).** (weakly) diagonally dominant: `|a_jj| ≥ Σ_{i≠j}|a_ij|` for all
`j`; strictly: strict inequality for all `j`; irreducibly diagonally dominant: `A` irreducible, weakly
dominant, strict for at least one `j`. (Saad's sums run over the column index `i` — i.e. column sums
— but the results are symmetric under transposition.) `[uncertain: row vs column; immaterial]`

**Theorem 4.6 (Gershgorin).** Every eigenvalue of `A ∈ ℂ^{n×n}` lies in some disc
`D(a_ii, ρ_i)`, `ρ_i = Σ_{j≠i}|a_ij|` (4.37). Also holds with column sums (apply to `Aᵀ`).
* Uses: matrix entries; eigenvector component of largest modulus. Proof: normalize `|ξ_m| = 1 ≥ |ξ_i|`;
  `(λ − a_mm)ξ_m = −Σ_{j≠m} a_mj ξ_j` ⇒ `|λ − a_mm| ≤ ρ_m` (4.38).
  Remark (unproved): a union of `m` discs disjoint from the others contains exactly `m` eigenvalues.

**Theorem 4.7.** `A` irreducible, eigenvalue `λ` on the boundary of the union of the Gershgorin discs ⇒
`λ` lies on the boundary of **every** disc.
* Uses: irreducibility ⇔ connected adjacency graph; equality case in (4.38) forces `|ξ_j| = 1` for all
  `j` with `a_mj ≠ 0`; propagate along a path.

**Corollary 4.8.** Strictly diagonally dominant or irreducibly diagonally dominant ⇒ nonsingular.
* Proof: strict: `0` lies in no disc. Irreducible: if singular, `0` is on the boundary of the union,
  hence on the boundary of every disc, contradicting strictness for one `j`.

**Theorem 4.9.** `A` strictly or irreducibly diagonally dominant ⇒ Jacobi and Gauss–Seidel converge for
every `x_0`.
* Uses: entries; Gershgorin-type argument on the iteration matrix; Cor 4.8 for the irreducible case.
* Proof: Jacobi `G = D⁻¹(E+F)`: for eigenvector normalized as in Gershgorin,
  `|λ| ≤ Σ_{j≠m}|a_mj|/|a_mm| < 1`. GS `G = (D−E)⁻¹F`: from `λ(D−E)x = Fx`,
  `|λ| ≤ σ_2/(|a_mm| − σ_1)`, `σ_1 = Σ_{j<m}|a_mj|`, `σ_2 = Σ_{j>m}|a_mj|`, `< 1` by strict dominance.
  Irreducible case: the same shows `ρ ≤ 1`; if `|λ| = 1` then `λM − N` is singular, but `λM − N` is
  irreducibly diagonally dominant, contradicting Cor 4.8.

**Theorem 4.10 (Ostrowski–Reich; stated without proof).** `A` symmetric with positive diagonal,
`0 < ω < 2`: SOR converges for every `x_0` iff `A` is positive definite.
* Uses: symmetry, SPD, `ω ∈ (0,2)`. (Standard proof: `‖G_ω‖_A < 1` via the energy identity.)

**Definition 4.11 (Property A).** Adjacency graph bipartite: vertices split `S_1 ∪ S_2` with every edge
between the two sets; equivalently `A` permutable to `[[D_1, −F],[−E, D_2]]` with `D_1, D_2` diagonal (4.42).

**Proposition 4.12.** `B = [[0, B_12],[B_21, 0]]`, `L, U` its lower/upper triangular parts. Then
(1) `μ ∈ σ(B) ⇒ −μ ∈ σ(B)`; (2) the eigenvalues of `B(α) = αL + α⁻¹U` (`α ≠ 0`) are independent of `α`.
* Proof: `(x, −v)` is an eigenvector for `−μ`; `B(α) = XBX⁻¹` with `X = diag(I, αI)`.

**Definition 4.13 (consistently ordered, Young).** Vertices partitioned into `S_1, …, S_p` such that
for any edge `(i,j)`: `i ∈ S_k` ⇒ `j ∈ S_{k−1}` if `j < i` and `j ∈ S_{k+1}` if `j > i`.
Consistently ordered ⇒ Property A. Example 4.2: block tridiagonal with diagonal diagonal blocks
("T-matrices") are consistently ordered.

**Proposition 4.14.** `A` consistently ordered ⇒ ∃ permutation `P` with `PᵀAP` a T-matrix and
`(PᵀAP)_L = PᵀA_LP`, `(PᵀAP)_U = PᵀA_UP` (4.45) (strict lower/upper parts are preserved).

**Proposition 4.15.** `B` the Jacobi matrix of a consistently ordered `A`, `L,U` its parts. Then the
eigenvalues of `B(α) = αL + α⁻¹U` (`α ≠ 0`) do not depend on `α`.
* Proof: reduce to a T-matrix by Prop 4.14; `B(α) = XBX⁻¹`, `X = diag(I, αI, α²I, …, α^{p−1}I)`.
  Remarks (unproved): Property A is invariant under symmetric permutations; `A` has Property A iff some
  symmetric permutation is consistently ordered.

**Theorem 4.16 (Young's SOR eigenvalue relation).** `A` consistently ordered, `a_ii ≠ 0`, `ω ≠ 0`,
`M_SOR = (I − ωL)⁻¹(ωU + (1−ω)I)` with `L = D⁻¹E`, `U = D⁻¹F`, Jacobi matrix `B = L + U`.
If `λ ≠ 0` is an eigenvalue of `M_SOR` and `μ` satisfies `(λ + ω − 1)² = λω²μ²` (4.46), then `μ ∈ σ(B)`;
conversely if `μ ∈ σ(B)` and `λ` satisfies (4.46) then `λ ∈ σ(M_SOR)`.
* Uses: determinants; Prop 4.15 with `α = λ^{1/2}`; matrix entries/ordering.
* Proof: `det(λI − M_SOR) = 0 ⇔ det((λ+ω−1)I − ω(λL + U)) = 0 ⇔ (λ+ω−1)/(ωλ^{1/2}) ∈ σ(λ^{1/2}L + λ^{−1/2}U) = σ(B)`.
* Consequence (stated without proof): `ω_opt = 2/(1 + sqrt(1 − ρ(B)²))` (4.47) (when `σ(B)` real,
  `ρ(B) < 1`).

Section 4.3 (ADI) skipped as instructed.

---

## 6. Chapter 5 Projection Methods

### 6.1 Definitions (5.1)
`A ∈ ℝ^{n×n}` (also viewed as a linear map), `K, L ⊂ ℝⁿ` subspaces of dimension `m`.
**Projection method onto `K` orthogonal to `L` (Petrov–Galerkin):** find `x̃ ∈ x_0 + K` with
`b − Ax̃ ⊥ L` (5.3). With `x̃ = x_0 + δ`, `r_0 = b − Ax_0`: `δ ∈ K`, `(r_0 − Aδ, w) = 0 ∀ w ∈ L`
(5.5)–(5.6). **Orthogonal** projection method: `L = K` (Galerkin); **oblique**: `L ≠ K`.
Example 5.1: one Gauss–Seidel relaxation step = projection with `K = L = span{e_i}`.

**Matrix representation (5.1.2).** `V` basis of `K`, `W` basis of `L`, `x̃ = x_0 + Vy`:
`WᵀAVy = Wᵀr_0`; if `WᵀAV` nonsingular, `x̃ = x_0 + V(WᵀAV)⁻¹Wᵀr_0` (5.7).
**Algorithm 5.1 (prototype projection method):** loop: choose `K, L`, bases `V, W`; `r = b − Ax`;
`y = (WᵀAV)⁻¹Wᵀr`; `x = x + Vy`.
`WᵀAV` nonsingular iff no nonzero vector of `AK` is orthogonal to `L` (i.e. `AK ∩ L^⊥ = {0}`;
stated as easily verified — it is Lemma 1.36 applied to `(AK, L)` when `A|_K` injective).
Example 5.2: `A = [[0, I],[I, I]]` nonsingular but `WᵀAV = 0` for `V = W = [e_1..e_m]`.

**Proposition 5.1 (well-posedness).** If (i) `A` is positive definite (real, Saad's sense) and `L = K`,
or (ii) `A` nonsingular and `L = AK`, then `B = WᵀAV` is nonsingular for every choice of bases
`V` of `K`, `W` of `L`.
* Uses: (i) `W = VG`, `G` nonsingular, `B = Gᵀ(VᵀAV)`, and `VᵀAV` positive definite (`(VᵀAVy,y) = (AVy,Vy) > 0`
  for `y ≠ 0` since `V` injective); (ii) `W = AVG`, `B = Gᵀ(AV)ᵀ(AV)`, `AV` full column rank.
  Only needs: inner product space, injectivity of `A|_K` in (ii), coercivity on `K` in (i).
* Remark: `A` symmetric, `L = K`, `W = V` ⇒ `B = VᵀAV` symmetric; `A` SPD ⇒ `B` SPD.

### 6.2 General theory (5.2)

**Proposition 5.2 (Galerkin = A-norm error minimization).** `A` SPD, `L = K`. `x̃` is the result of the
orthogonal projection method onto `K` from `x_0` iff `x̃` minimizes `E(x) = (A(x*−x), x*−x)^{1/2} = ‖x*−x‖_A`
over `x ∈ x_0 + K`.
* Uses: `A`-inner product (needs SPD), Corollary 1.39 in the `A`-inner product: minimizer iff
  `x* − x̃ ⊥_A K`, i.e. `(A(x*−x̃), v) = (b − Ax̃, v) = 0 ∀ v ∈ K`. Generalizes to bounded coercive
  self-adjoint operators on a Hilbert space with `K` closed.

**Proposition 5.3 (Petrov–Galerkin with `L = AK` = residual minimization).** `A` arbitrary square,
`L = AK`. `x̃` is the result of the oblique projection onto `K` orthogonal to `AK` from `x_0` iff `x̃`
minimizes `R(x) = ‖b − Ax‖₂` over `x_0 + K`. `A` need not be nonsingular (then the minimizer may be
non-unique but every minimizer satisfies the condition).
* Uses: Corollary 1.39 for the subspace `AK`: `b − Ax̃ ⊥ AK`. Hilbert-space general (`AK` closed).

**Proposition 5.4 (residual projection).** `L = AK`, `r̃ = b − Ax̃`. Then `r̃ = (I − P) r_0` (5.10) with
`P` the orthogonal projector onto `AK`. Consequently `‖r̃‖₂ ≤ ‖r_0‖₂`.
* Proof: `r̃ = r_0 − Aδ` and `Aδ ∈ AK` with `r_0 − Aδ ⊥ AK` ⇒ `Aδ = P r_0`.

**Proposition 5.5 (error projection).** `A` SPD, `L = K`, `d̃ = x* − x̃`, `d_0 = x* − x_0`. Then
`d̃ = (I − P_A) d_0` with `P_A` the `A`-orthogonal projector onto `K`. Consequently `‖d̃‖_A ≤ ‖d_0‖_A`.
* Proof: `(A(d_0 − δ), w) = 0 ∀ w ∈ K` ⇔ `(d_0 − δ, w)_A = 0` ⇒ `δ = P_A d_0`.

**Section 5.2.3 setup.** `P_K` orthogonal projector onto `K`; `Q_K^L` oblique projector onto `K`
orthogonal to `L` (`Q_K^L x ∈ K`, `x − Q_K^L x ⊥ L`); `A_m := Q_K^L A P_K`. With `x_0 = 0` the projected
problem (5.5)–(5.6) is equivalent (by (1.62)) to `Q_K^L(b − Ax̃) = 0`, i.e. `A_m x̃ = Q_K^L b`, `x̃ ∈ K`
— an `m`-dimensional system approximating the `n`-dimensional one.

**Proposition 5.6 (exactness on invariant subspaces).** `K` invariant under `A`, `x_0 = 0`, `b ∈ K` ⇒ the
approximate solution of any (oblique or orthogonal) projection method onto `K` is exact. Extension:
for `x_0 ≠ 0`, require `r_0 ∈ K`.
* Uses: `Q_K^L` is the identity on `K` (`Q b = b`, `Q A x̃ = A x̃`), so `Q(b − Ax̃) = 0 ⇒ b − Ax̃ = 0`.
  Implicit hypothesis: the projected problem is solvable/`x̃` exists. Hilbert-space general.
  This is the source of "lucky breakdown" in Arnoldi/FOM/GMRES (Prop 6.6 remarks).

**Theorem 5.7 (general residual bound for the projected operator).** Let `γ = ‖Q_K^L A (I − P_K)‖₂`,
`b ∈ K`, `x_0 = 0`. Then the exact solution `x*` satisfies `‖b − A_m x*‖₂ ≤ γ ‖(I − P_K)x*‖₂` (5.11).
Matrix form for `L = K`, `V` orthonormal, `W = V`: `‖Vᵀb − (VᵀAV)Vᵀx*‖₂ ≤ γ ‖(I−P_K)x*‖₂`.
The quantity `‖(I−P_K)x*‖₂/‖x*‖₂` is the sine of the angle between `x*` and `K`; also
`‖x̃ − x*‖₂ ≥ ‖(I − P_K)x*‖₂` trivially.
* Uses: `b = Q b` (since `b ∈ K`), `b − A_m x* = Q A (x* − P_K x*) = Q A (I−P_K)(I−P_K)x*`, and
  `(I − P_K)² = I − P_K`; operator norms. Hilbert-space general.

### 6.3 One-dimensional projection processes (5.3)
`K = span{v}`, `L = span{w}`: `x ← x + αv`, `α = (r,w)/(Av,w)` (5.12).

**Steepest descent (5.3.1)** — `A` SPD, `v = w = r`: `α = (r,r)/(Ar,r)`, `x ← x + αr`.
**Algorithm 5.2:** `r = b − Ax`, `p = Ar`; loop: `α = (r,r)/(p,r)`, `x ← x + αr`, `r ← r − αp`, `p = Ar`.
Each step minimizes `f(x) = ‖x* − x‖_A²` along `−∇f = 2r` (direction of the residual).

**Lemma 5.8 (Kantorovich inequality).** `B` real SPD with extreme eigenvalues `λ_max, λ_min`:
`(Bx,x)(B⁻¹x,x)/(x,x)² ≤ (λ_max + λ_min)²/(4 λ_max λ_min)` for all `x ≠ 0` (5.13).
* Uses: spectral theorem for `B` (`B = QᵀDQ`), convexity of `1/λ` on `[λ_1, λ_n]`: with `y = Qx`,
  `(Bx,x) = Σ β_i λ_i =: λ̄` (a convex combination), `(B⁻¹x,x) = Σ β_i/λ_i ≤ 1/λ_1 + 1/λ_n − λ̄/(λ_1λ_n)`;
  maximize `λ̄(1/λ_1 + 1/λ_n − λ̄/(λ_1λ_n))` at `λ̄ = (λ_1+λ_n)/2`. (Extends to bounded self-adjoint
  positive operators with spectrum in `[λ_min, λ_max]` via the spectral theorem/measure.)

**Theorem 5.9 (steepest descent convergence).** `A` SPD. The `A`-norms of the errors `d_k = x* − x_k` of
Algorithm 5.2 satisfy `‖d_{k+1}‖_A ≤ ((λ_max − λ_min)/(λ_max + λ_min)) ‖d_k‖_A` (5.14); hence
convergence for every `x_0`.
* Uses: SPD (`A`-inner product), `r_{k+1} ⊥ r_k` (the Galerkin condition), Kantorovich.
* Proof: `‖d_{k+1}‖_A² = (d_{k+1}, r_k)` (since `(d_{k+1}, r_k)_A = (r_{k+1}, r_k) = 0`)
  `= (A⁻¹r_k, r_k) − α_k (r_k, r_k) = ‖d_k‖_A² [1 − (r_k,r_k)²/((r_k,Ar_k)(r_k,A⁻¹r_k))]`, then (5.13).
  Note the identity `‖d_k‖_A² = (A⁻¹r_k, r_k)`.

**Minimal residual iteration (5.3.2)** — `A` real positive definite (non-symmetric allowed),
`v = r`, `w = Ar`: `α = (Ar,r)/(Ar,Ar)`.
**Algorithm 5.3:** `r = b − Ax`, `p = Ar`; loop: `α = (p,r)/(p,p)`, `x ← x + αr`, `r ← r − αp`, `p = Ar`.
Each step minimizes `‖b − Ax‖₂` along `r`.

**Theorem 5.10 (MR convergence).** `A` real positive definite, `μ = λ_min((A+Aᵀ)/2)`, `σ = ‖A‖₂`. Then
`‖r_{k+1}‖₂ ≤ (1 − μ²/σ²)^{1/2} ‖r_k‖₂` (5.15); convergence for every `x_0`.
* Uses: Thm 1.34 (`(Ax,x) ≥ μ‖x‖²`), the orthogonality `r_{k+1} ⊥ Ar_k`, `‖Ar‖ ≤ σ‖r‖`.
* Proof: `‖r_{k+1}‖² = (r_k − α_kAr_k, r_k) = ‖r_k‖² [1 − (Ar_k,r_k)²/((r_k,r_k)(Ar_k,Ar_k))]` (5.18)–(5.19)
  `= ‖r_k‖² sin²θ_k`, `cos θ_k = (Ar_k,r_k)/(‖Ar_k‖‖r_k‖)`; then `(Ar,r)/(r,r) ≥ μ`, `‖Ar‖ ≤ σ‖r‖`.
  Alternative bound (5.20): `‖r_{k+1}‖² ≤ (1 − μ(A)μ(A⁻¹)) ‖r_k‖²`, `μ(B) = λ_min((B+Bᵀ)/2)`, using that
  `A⁻¹` is also positive definite. Convergence factor `≤ max_{x≠0} sin ∠(x, Ax) < 1`.
  Hilbert-space general (coercive bounded operator).

**Residual norm steepest descent (5.3.3)** — `A` nonsingular (only), `v = Aᵀr`, `w = Av`:
`α = ‖v‖₂²/‖Av‖₂²` (5.21). **Algorithm 5.4:** `r = b − Ax`; loop: `v = Aᵀr`, `α = ‖v‖²/‖Av‖²`,
`x ← x + αv`, `r ← r − αAv`. Minimizes `‖b − Ax‖₂²` along `−∇ = 2Aᵀr`; equals steepest descent on the
normal equations `AᵀAx = Aᵀb`, hence converges by Thm 5.9 (with `κ(AᵀA) = κ₂(A)²`).
Exercise 5.3: a Galerkin method for `AᵀAx = Aᵀb` on `K` = Petrov–Galerkin for `Ax = b` with `L = AK`.

### 6.4 Additive and multiplicative processes (5.4)
Set-decomposition `S_1 ∪ … ∪ S_p = {1..n}`, `V_i` columns of `I` indexed by `S_i`; more generally any
`p` orthonormal systems `V_i` with distinct spans; `A_i = V_iᵀAV_i`. Block Jacobi/GS (Algs 4.1, 4.2) are
sequences of orthogonal projection steps onto `K_i = span V_i` ((4.17) = (5.7) with `W = V = V_i`).
**Algorithm 5.5 (additive projection procedure):** `y_i = A_i⁻¹V_iᵀ(b − Ax_k)`, `i = 1..p`;
`x_{k+1} = x_k + Σ_i V_i y_i` (5.22). Residual: `r_{k+1} = (I − Σ_i P_i) r_k`,
`P_i = AV_i(V_iᵀAV_i)⁻¹V_iᵀ` = projector onto `AK_i` orthogonal to `K_i`. With relaxation parameters
`ω_i`: `r_{k+1} = (I − Σ ω_i P_i) r_k` (5.23). Least-squares option `L_i = AK_i`:
`P_i = AV_i((AV_i)ᵀAV_i)⁻¹(AV_i)ᵀ` orthogonal projectors onto `AK_i`; if the `AK_i` are mutually
orthogonal and `Σ rank P_i = n`, one outer step is exact (`I − ΣP_i = 0`).
**Algorithm 5.6 (multiplicative projection procedure):** for `i = 1..p`: `y = A_i⁻¹V_iᵀ(b − Ax)`,
`x := x + V_i y` (block Gauss–Seidel analogue).
* Uses: projectors (1.12), (5.7). Hilbert-space general.

---

## 7. Chapter 6 Krylov Subspace Methods, Part I

### 7.1 Setup (6.1)
A Krylov subspace method is a projection method with `K_m = K_m(A, r_0) = span{r_0, Ar_0, …, A^{m−1}r_0}`,
so `x_m = x_0 + q_{m−1}(A) r_0` with `q_{m−1} ∈ P_{m−1}` (polynomial approximation of `A⁻¹b`). Choices:
`L_m = K_m` (FOM/CG/Lanczos), `L_m = AK_m` (GMRES/CR/GCR/MINRES-type), `L_m = K_m(Aᵀ, r_0)` (Ch. 7).

### 7.2 Krylov subspaces (6.2)
`K_m(A,v) = {p(A)v : p ∈ P_{m−1}}`. **Minimal polynomial of `v`** (w.r.t. `A`): the monic `p ≠ 0` of least
degree with `p(A)v = 0`; its degree is the **grade** `μ` of `v`; `μ ≤ n` by Cayley–Hamilton.

**Proposition 6.1.** `μ` = grade of `v`. Then `K_μ` is invariant under `A` and `K_m = K_μ` for all `m ≥ μ`.
* Uses: `A^μ v ∈ K_μ` from the minimal polynomial; finite-dimensional (existence of `μ` needs `v` to be
  of finite grade — in a Hilbert space a vector may have infinite grade, and then all `K_m` are distinct).

**Proposition 6.2.** `dim K_m = m ⇔ grade(v) ≥ m` (6.3); hence `dim K_m = min{m, grade(v)}` (6.4).
* Proof: `v, Av, …, A^{m−1}v` independent iff no nonzero `p ∈ P_{m−1}` annihilates `v`.

**Proposition 6.3 (sections of `A` and polynomials).** `Q_m` any projector onto `K_m`,
`A_m := Q_m A|_{K_m}` (the section of `A` in `K_m`). Then for `q ∈ P_{m−1}`: `q(A)v = q(A_m)v`; and for
`q ∈ P_m`: `Q_m q(A) v = q(A_m) v`.
* Uses: only `Q_m|_{K_m} = id` and `A^i v ∈ K_m` for `i ≤ m−1`; induction on monomials. Works for any
  idempotent onto `K_m` (oblique or orthogonal). Hilbert-space general (finite `m`).

### 7.3 Arnoldi's method (6.3)
**Algorithm 6.1 (Arnoldi, classical GS).** `‖v_1‖₂ = 1`; for `j = 1..m`: `h_ij = (Av_j, v_i)`, `i ≤ j`;
`w_j = Av_j − Σ_{i≤j} h_ij v_i`; `h_{j+1,j} = ‖w_j‖₂`; stop if `0`; `v_{j+1} = w_j/h_{j+1,j}`.
**Algorithm 6.2 (Arnoldi–MGS):** same with `w_j := Av_j; for i ≤ j: h_ij = (w_j, v_i); w_j := w_j − h_ij v_i`
(mathematically equivalent; numerically preferable; optional reorthogonalization).
**Algorithm 6.3 (Householder Arnoldi, Walker):** builds the QR factorization
`Q_m[v, Av_1, …, Av_m] = [h_0, …, h_m]` (6.12) with `Q_j = P_j⋯P_1`, `v_j = P_1⋯P_j e_j`,
`z_{j+1} = P_j⋯P_1 A v_j`, `h_j = Q_{j+1}Av_j`; yields the same `AV_m = V_{m+1}H̄_m` and the same `v_i`
up to sign. Cost table: GS/MGS `2m²n`, MGSR `4m²n`, Householder `4m²n − 4m³/3`.

**Proposition 6.4.** If Algorithm 6.1 does not stop before step `m`, then `v_1, …, v_m` is an orthonormal
basis of `K_m(A, v_1)`.
* Proof: orthonormal by construction; `v_j = q_{j−1}(A)v_1` with `deg q_{j−1} = j−1` by induction on
  `h_{j+1,j}v_{j+1} = Av_j − Σ h_ij v_i` (6.5) (leading coefficient nonzero since `h_{j+1,j} ≠ 0`).

**Proposition 6.5 (Arnoldi relations).** `V_m = [v_1..v_m]`, `H̄_m ∈ ℝ^{(m+1)×m}` upper Hessenberg with
entries `h_ij`, `H_m` = `H̄_m` without its last row. Then
`A V_m = V_m H_m + w_m e_mᵀ` (6.6) `= V_{m+1} H̄_m` (6.7), and `V_mᵀ A V_m = H_m` (6.8).
* Uses: (6.9) `Av_j = Σ_{i≤j+1} h_ij v_i` (a rewrite of lines 4–7) and orthonormality of the `v_i` for
  (6.8). Purely algebraic; Hilbert-space general for finite `m`.

**Proposition 6.6 (breakdown).** Arnoldi breaks down at step `j` (`h_{j+1,j} = 0`) iff the minimal
polynomial of `v_1` has degree `j`; then `K_j` is invariant under `A`.
* Uses: Props 6.1, 6.2, 6.4. Corollary (with Prop 5.6): a projection method onto `K_j` is exact at a
  breakdown ("lucky breakdown"), provided `r_0 ∈ K_j` (true for `v_1 = r_0/β`).
  Finite-dimensional statement (grade); the "if" direction (`w_j = 0 ⇒ K_j` invariant, `dim K_j = j`)
  holds in any Hilbert space.

### 7.4 FOM (6.4)
Orthogonal projection (`L = K = K_m(A, r_0)`), `v_1 = r_0/β`, `β = ‖r_0‖₂`. Galerkin condition
`b − Ax_m ⊥ K_m` (6.15). Since `V_mᵀAV_m = H_m` and `V_mᵀ r_0 = β e_1`:
`x_m = x_0 + V_m y_m`, `y_m = H_m⁻¹(β e_1)` (6.16)–(6.17) (requires `H_m` nonsingular).
**Algorithm 6.4 (FOM):** Arnoldi-MGS from `v_1 = r_0/β` for `m` steps (if `h_{j+1,j} = 0` set `m := j`),
then `y_m = H_m⁻¹(βe_1)`, `x_m = x_0 + V_m y_m`.

**Proposition 6.7 (FOM residual).** `b − Ax_m = −h_{m+1,m} (e_mᵀ y_m) v_{m+1}`, hence
`‖b − Ax_m‖₂ = h_{m+1,m} |e_mᵀ y_m|` (6.18). In particular `r_m ∥ v_{m+1}` and the FOM residuals are
mutually orthogonal.
* Uses: (6.6) and `H_m y_m = βe_1`: `r_0 − AV_m y_m = βv_1 − V_mH_my_m − h_{m+1,m}e_mᵀy_m v_{m+1}`.
  Does **not** use orthogonality of the `v_i` (hence still valid for IOM/DIOM).
Cost per step ≈ `2 Nz(A) + 2mn`; storage `(m+3)n + m²/2`.

**Algorithm 6.5 (restarted FOM, FOM(m)):** run FOM for `m` steps, set `x_0 := x_m`, repeat.

**Incomplete orthogonalization (6.4.2).** **Algorithm 6.6 (IOM process):** Arnoldi-MGS but
orthogonalize only against `v_i`, `i = max(1, j−k+1)..j` (`k` previous vectors); `H_m` becomes banded
Hessenberg with bandwidth `k+1` (6.19). **Algorithm 6.7 (IOM):** FOM with Alg 6.6.
**Algorithm 6.8 (DIOM):** progressive form. `H_m = L_m U_m` (LU without pivoting; `L_m` unit lower
bidiagonal, `U_m` banded upper triangular with `k` diagonals); `P_m := V_m U_m⁻¹`, `z_m := L_m⁻¹(βe_1)`;
`x_m = x_0 + P_m z_m` (6.20); last column `p_m = (v_m − Σ_{i=m−k+1}^{m−1} u_im p_i)/u_mm`;
`z_m = [z_{m−1}; ζ_m]`, `ζ_m = −l_{m,m−1} ζ_{m−1}` (`ζ_1 = β`); update `x_m = x_{m−1} + ζ_m p_m` (6.21).
Stops if `u_mm = 0` (pivoting variant exists). Residual: `‖b − Ax_m‖₂ = h_{m+1,m}|e_mᵀy_m| = h_{m+1,m}|ζ_m|/|u_mm|`.

**Proposition 6.8.** IOM/DIOM are mathematically equivalent to a projection process onto `K_m`
orthogonal to `L_m = span{z_1..z_m}`, `z_i = v_i − (v_i, v_{m+1}) v_{m+1}`.
* Proof: `r_m ∥ v_{m+1}` and `v_{m+1} ⊥ z_i` by construction.
Stated properties (6.22)–(6.24): `(r_j, r_i) = 0` for `|i−j| ≥ k, i ≠ j` (local orthogonality);
`(Ap_j, v_i) = 0` for `j−k+1 < i < j`; for `k = ∞` (FOM) the `p_j` are semi-conjugate: `(Ap_j, p_i) = 0`, `i < j`.

### 7.5 GMRES (6.5)
Projection with `K = K_m`, `L = AK_m`, `v_1 = r_0/β`; by Prop 5.3 it minimizes `‖b − Ax‖₂` over `x_0 + K_m`.
For `x = x_0 + V_m y`: `b − Ax = r_0 − AV_m y = βv_1 − V_{m+1}H̄_m y = V_{m+1}(βe_1 − H̄_m y)` (6.27), so
`J(y) = ‖b − A(x_0+V_my)‖₂ = ‖βe_1 − H̄_m y‖₂` (6.28) by orthonormality of `V_{m+1}`. Hence
`x_m = x_0 + V_m y_m`, `y_m = argmin_y ‖βe_1 − H̄_m y‖₂` (6.29)–(6.30) — an `(m+1)×m` least-squares
problem. **Algorithm 6.9 (GMRES):** Arnoldi-MGS for `m` steps (breakdown ⇒ `m := j`), then (6.29)–(6.30).
Second derivation: (5.7) with `W_m = AV_m` (Exercise 5).
**Algorithm 6.10 (Householder GMRES):** Householder Arnoldi; `x_m = x_0 + z`, `z` built by the Horner-like
recursion `z := P_j(η_j e_j + z)`, `j = m..1` (6.31)–(6.33); only the Householder vectors are stored;
residual norm `‖h_0 − Σ η_j h_j‖₂`.

**Givens-rotation implementation (6.5.3).** Rotations `Ω_i` (6.34) with `c_i² + s_i² = 1`,
`s_i = h_{i+1,i}/sqrt((h_ii^{(i−1)})² + h_{i+1,i}²)`, `c_i = h_ii^{(i−1)}/sqrt(…)` (6.37);
`Q_m = Ω_m⋯Ω_1` (6.38), `R̄_m = Q_m H̄_m` (6.39) upper triangular with zero last row,
`ḡ_m = Q_m(βe_1) = (γ_1, …, γ_{m+1})ᵀ` (6.40); `min‖βe_1 − H̄_m y‖ = min‖ḡ_m − R̄_m y‖`.
Progressive update: append the new column, apply previous rotations, compute `Ω_m`; then
**`γ_{j+1} = −s_j γ_j`** (6.47), so `γ_{m+1} = (−1)^m s_1⋯s_m β`; `s_j = 0` ⇒ exact solution at step `j`.
FOM uses the same machinery with the last rotation omitted (`H_m y = βe_1` solved via QR of `H_m`).

**Proposition 6.9.** `m ≤ n`; `Ω_i`, `R̄_m`, `ḡ_m` as above; `R_m`, `g_m` obtained by deleting the last
row/component. Then (1) `rank(AV_m) = rank(R_m)`; in particular `r_mm = 0 ⇒ A` singular;
(2) `y_m = R_m⁻¹ g_m`; (3) `b − Ax_m = V_{m+1}(βe_1 − H̄_m y_m) = V_{m+1} Q_mᵀ (γ_{m+1} e_{m+1})` (6.41),
hence `‖b − Ax_m‖₂ = |γ_{m+1}|` (6.42).
* Uses: (6.7), unitarity of `Q_m` and orthonormality of `V_{m+1}` (so `V_{m+1}Q_mᵀ` has orthonormal
  columns), `‖βe_1 − H̄_m y‖² = |γ_{m+1}|² + ‖g_m − R_m y‖²` (6.43). `V_m` full rank ⇒ `AV_m` rank
  deficient ⇒ `A` singular.

**Proposition 6.10 (GMRES breakdown = convergence).** `A` nonsingular. GMRES breaks down at step `j`
(`h_{j+1,j} = 0`) iff `x_j` is exact.
* Proof: `h_{j+1,j} = 0 ⇒ s_j = 0` (since `r_jj ≠ 0` by Prop 6.9(1) and `A` nonsingular) ⇒ `γ_{j+1} = 0`
  ⇒ `r_j = 0`. Conversely exact at `j` but not `j−1` ⇒ `s_j = 0` ⇒ `h_{j+1,j} = 0` by (6.37).
  Uses nonsingularity of `A`; finite `m`; otherwise Hilbert-space general.

**Algorithm 6.11 (restarted GMRES, GMRES(m)).** Restart with `x_0 := x_m`. Full GMRES converges in at most
`n` steps (finite dimension); GMRES(m) can stagnate when `A` is not positive definite.

**Truncated GMRES (6.5.6).** **Algorithm 6.12 (Quasi-GMRES):** GMRES with Alg 6.6 (IOM process).
**Algorithm 6.13 (DQGMRES):** progressive version: banded `H̄_m` ⇒ `R̄_m` banded with `k+1` diagonals;
`P_m = V_m R_m⁻¹`, `x_m = x_0 + P_m g_m = x_{m−1} + γ_m p_m`, `p_m = (v_m − Σ_{i=m−k}^{m−1} r_im p_i)/r_mm`,
`γ_{m+1} = −s_m γ_m`, `γ_m := c_m γ_m`. DQGMRES only minimizes the **quasi-residual**
`‖βe_1 − H̄_m y‖₂` (equals the true residual iff the `v_i` are orthonormal). Identities that survive
(no orthogonality used): `b − Ax_m = V_{m+1}(βe_1 − H̄_m y_m)` and
`b − Ax_m = V_{m+1}Q_mᵀ(γ_{m+1}e_{m+1}) = γ_{m+1} z_{m+1}` (6.50), `z_{m+1}` = last column of
`Z_{m+1} = V_{m+1}Q_mᵀ` (6.52); `z_{m+1} = −s_m z_m + c_m v_{m+1}` (6.53); hence
`r_m = s_m² r_{m−1} + c_m γ_{m+1} v_{m+1}` (6.55). Bounds: `‖b − Ax_m‖₂ ≤ sqrt(m − k + 1) |γ_{m+1}|` (6.51)
(local orthogonality of `k+1` consecutive `v_i` + Cauchy–Schwarz); `‖z_{m+1}‖ ≤ |s_m|‖z_m‖ + |c_m|`,
so `ζ_{m+1} = |s_m|ζ_m + |c_m|` bounds `‖z_{m+1}‖` (6.54). Relation to IOM/DIOM residual `r_m^I`:
`r_m^I = −h_{m+1,m}(e_mᵀy_m)v_{m+1}`, `γ_{m+1} v_{m+1} = c_m r_m^I` (6.56), `ρ_m^Q = |c_m| ρ_m^I` (6.57)
(`ρ_m^Q = |γ_{m+1}|` quasi-residual norm, `ρ_m^I = ‖r_m^I‖`), `r_m = s_m² r_{m−1} + c_m² r_m^I` (6.58).

**Theorem 6.11 (Freund–Nachtigal; quasi-minimal vs minimal residual).** If `V_{m+1}` (the incomplete
Arnoldi basis of DQGMRES) has full rank, then `‖r_m^Q‖₂ ≤ κ₂(V_{m+1}) ‖r_m^G‖₂` (6.59), `r_m^G` the true
GMRES residual.
* Uses: `V_{m+1} = W_{m+1}S⁻¹` with `W_{m+1}` orthonormal, `S` nonsingular; the residual set
  `R = {V_{m+1}t : t = βe_1 − H̄_m y}` contains `r_m^G`; `‖r_m^Q‖ ≤ ‖S⁻¹‖‖t_m‖`, `‖t_m‖ ≤ ‖S‖‖r‖ ∀ r ∈ R`;
  `κ₂(V_{m+1}) = κ₂(S)`. Finite `m`; Hilbert-space general.

### 7.6 Relations between FOM and GMRES (6.5.7)
Notation: `ρ_m^F`, `ρ_m^G` residual norms at step `m`; `ρ_0^F = ρ_0^G = β`. From (6.47):
`ρ_m^G = |s_m| ρ_{m−1}^G`, `ρ_m^G = |s_1 s_2 ⋯ s_m| β` (6.62) (the `s_i ≥ 0` for real data).
FOM: `ρ_m^F = h_{m+1,m}|e_mᵀ y_m| = (h_{m+1,m}/|h_mm^{(m−1)}|)|s_1⋯s_{m−1}|β = (|s_m|/|c_m|)|s_1⋯s_{m−1}|β`.

**Proposition 6.12 (Brown).** After `m` Arnoldi steps with `H_m` nonsingular, `δ = (Q_{m−1}H̄_m)_{mm}`,
`h = h_{m+1,m}`: `ρ_m^F = ρ_m^G/|c_m| = ρ_m^G sqrt(1 + h²/δ²)` (6.63).

**Proposition 6.13 (Cullum–Greenbaum).** Same hypotheses: `ρ_m^F = ρ_m^G / sqrt(1 − (ρ_m^G/ρ_{m−1}^G)²)` (6.64);
equivalently `1/(ρ_m^F)² + 1/(ρ_{m−1}^G)² = 1/(ρ_m^G)²` (6.65).

**Corollary 6.14.** Summing (6.65): `1/(ρ_m^G)² = Σ_{i=0}^m 1/(ρ_i^F)²` (6.66), i.e.
`ρ_m^G = (Σ_{i=0}^m (ρ_i^F)^{−2})^{−1/2}` (6.67). Consequently `ρ_m^G ≤ ρ_m^F`.

**Proposition 6.15.** `m` steps of GMRES and FOM (FOM steps with singular `H_m` skipped); `ρ̃_m^F` the
smallest FOM residual norm among steps `0..m`. Then `ρ_m^G ≤ ρ̃_m^F ≤ sqrt(m+1) ρ_m^G` (6.68).

**Lemma 6.16.** `R̃_m` = upper `m×m` part of `Q_{m−1}H̄_m`, `R_m` = upper part of `Q_mH̄_m`; `g̃_m`, `g_m` the
first `m` components of `Q_{m−1}(βe_1)`, `Q_m(βe_1)`; `ỹ_m = R̃_m⁻¹g̃_m` (FOM), `y_m = R_m⁻¹g_m` (GMRES). Then
`y_m − [y_{m−1}; 0] = c_m² (ỹ_m − [y_{m−1}; 0])` (6.69).
* Uses: `R_m` and `R̃_m` differ only in entry `(m,m)` (`ξ_m` vs `ξ̃_m`), right-hand sides only in the
  last component `γ_m = c_m γ̃_m` (6.70); `ξ_m = c_m ξ̃_m + s_m h_{m+1,m} = ξ̃_m / c_m` (6.71); block
  back-substitution (6.72)–(6.73) gives `γ_m/ξ_m = c_m² γ̃_m/ξ̃_m`.
* Consequences: `x_m^G − x_{m−1}^G = c_m²(x_m^F − x_{m−1}^G)`, i.e. `x_m^G = s_m² x_{m−1}^G + c_m² x_m^F` (6.74)
  and `r_m^G = s_m² r_{m−1}^G + c_m² r_m^F` (6.75). Not specific to GMRES/FOM: any pair
  (least-squares method, Galerkin method) built on the same Hessenberg least-squares problem (6.30)
  obeys the same relation (used for QMR/BCG in Ch. 7).

**Proposition 6.17 (Brown; stagnation ⇔ FOM breakdown; stated without proof).** If GMRES makes no
progress at step `m` (`x_m^G = x_{m−1}^G`) then `H_m` is singular and `x_m^F` is undefined; conversely if
`H_m` is singular at step `m` and `A` is nonsingular then `x_m^G = x_{m−1}^G`. (Direction "⇐" from (6.74):
`c_m = 0 ⇔ h_mm^{(m−1)} = 0 ⇔ H_m` singular.)
* Uses (6.5.7 as a whole): Givens/QR of Hessenberg matrices; orthonormality of `V_{m+1}`; `A` real or
  complex (complex rotations in 6.5.9). Finite `m`; Hilbert-space general.

### 7.7 Residual smoothing (6.5.8)
Given an original sequence `x_m^O`, `r_m^O`, define `x_m^S = x_{m−1}^S + η_m(x_m^O − x_{m−1}^S)`,
`r_m^S = r_{m−1}^S + η_m(r_m^O − r_{m−1}^S)`. **Minimal residual smoothing (Algorithm 6.14):** `η_m` minimizes
`‖r_m^S‖₂`: `η_m = −(r_{m−1}^S, r_m^O − r_{m−1}^S)/‖r_m^O − r_{m−1}^S‖₂²` (a one-dimensional MR projection along
`x_m^O − x_{m−1}^S`). (6.74)–(6.75) show GMRES = MR-smoothed FOM with `η_m = c_m²`.

**Lemma 6.18 (Weiss).** If `r_m^O ⊥ r_{m−1}^S` for every `m ≥ 1`, then
`1/‖r_m^S‖₂² = 1/‖r_{m−1}^S‖₂² + 1/‖r_m^O‖₂²` (6.76) and `η_m = ‖r_{m−1}^S‖²/(‖r_{m−1}^S‖² + ‖r_m^O‖²)` (6.77).
* Proof: orthogonality gives `(r_{m−1}^S, r_m^O − r_{m−1}^S) = −‖r_{m−1}^S‖²`, `‖r_m^O − r_{m−1}^S‖² = ‖r_m^O‖² + ‖r_{m−1}^S‖²`;
  then `‖r_m^S‖² = ‖r_{m−1}^S‖² − η_m²‖r_m^O − r_{m−1}^S‖²`.
* Hypothesis holds when the original residuals are mutually orthogonal (FOM: each `r_k^S` is a
  combination of `r_i^O`, `i ≤ k`). Then (6.76) coincides with (6.65), so MR-smoothed FOM has the GMRES
  residual norms, hence (same subspace + minimality) equals GMRES. Alternative proof: the `p_j = x_j^O − x_{j−1}^S`
  are `AᵀA`-orthogonal and Lemma 6.21 applies (Exercise 26).
* (6.78)–(6.79): with `ρ_j = ‖r_j^O‖`, `τ_j = ‖r_j^S‖`: `r_m^S = (τ_{m−1}^{−2} r_{m−1}^S + ρ_m^{−2} r_m^O)/(τ_{m−1}^{−2} + ρ_m^{−2})`
  and `r_m^S = (Σ_{j=0}^m ρ_j^{−2})^{−1} Σ_{j=0}^m ρ_j^{−2} r_j^O` `[uncertain: index range 0..m vs 1..m]` —
  the smoothed residual is a convex combination of the original residuals with weights `∝ 1/ρ_j²`.
* **QMRS (quasi-minimal residual smoothing):** define instead `η_m = τ_m²/ρ_m²`, `1/τ_m² = 1/τ_{m−1}² + 1/ρ_m²`
  recursively; then (6.79) still holds with `τ_j` in place of `‖r_j^S‖`. Applied to IOM/DIOM it reproduces
  QGMRES/DQGMRES iterates (via (6.47), (6.57), (6.58)): `|c_m| = |γ_{m+1}|/ρ_m`, `|s_m| = |γ_{m+1}/γ_m|`,
  `1/γ_{m+1}² = 1/γ_m² + 1/ρ_m²`.

**GMRES for complex systems (6.5.9).** Same algorithm with the complex inner product; complex Givens
rotations `[[c̄_i, s̄_i],[−s_i, c_i]]` (6.80), `|c_i|² + |s_i|² = 1`; `s_i = h_{i+1,i}/(|h_ii^{(i−1)}|² + h_{i+1,i}²)^{1/2}` is
real nonnegative, `c_i` complex (6.81); the diagonal of `R` and the `γ_i` are real.

### 7.8 The symmetric Lanczos algorithm (6.6)

**Theorem 6.19.** Arnoldi applied to a real symmetric `A` produces `h_ij = 0` for `1 ≤ i < j−1` (6.82) and
`h_{j,j+1} = h_{j+1,j}` (6.83): `H_m` is symmetric tridiagonal.
* Proof: `H_m = V_mᵀAV_m` is symmetric and Hessenberg. (Same for Hermitian `A` with `H_m` Hermitian
  tridiagonal; the `h_{j+1,j} > 0` are real so `T_m` is real symmetric tridiagonal even for complex Hermitian `A`.)
Notation `α_j = h_jj`, `β_j = h_{j−1,j}`, `T_m = tridiag(β_j, α_j, β_{j+1})` (6.84).

**Algorithm 6.15 (Lanczos).** `‖v_1‖ = 1`, `β_1 = 0`, `v_0 = 0`; for `j = 1..m`: `w_j = Av_j − β_j v_{j−1}`;
`α_j = (w_j, v_j)`; `w_j := w_j − α_j v_j`; `β_{j+1} = ‖w_j‖₂` (stop if 0); `v_{j+1} = w_j/β_{j+1}`.
Three-term recurrence `β_{j+1}v_{j+1} = Av_j − α_j v_j − β_j v_{j−1}`; relations
`AV_m = V_mT_m + β_{m+1}v_{m+1}e_mᵀ = V_{m+1}T̄_m`, `V_mᵀAV_m = T_m` (special case of Prop 6.5).
Orthogonality is exact only in exact arithmetic (loss of orthogonality; Parlett; reorthogonalization).

**Relation with orthogonal polynomials (6.6.2).** If `grade(v_1) ≥ m`, `q ↦ q(A)v_1` is an isomorphism
`P_{m−1} → K_m`; the bilinear form `<p,q>_{v_1} = (p(A)v_1, q(A)v_1)` (6.85) is a nondegenerate inner
product on `P_{m−1}` (for `m ≤ μ`); `v_i = q_{i−1}(A)v_1` and orthogonality of the `v_i` = orthogonality of
the `q_i` for (6.85). Lanczos = Stieltjes procedure for these orthogonal polynomials (three-term
recurrence of orthogonal polynomials). Stated facts: the characteristic polynomial of `T_m` minimizes
`‖p(A)v_1‖` over monic `p` of degree `m`; Lanczos computes (scaled) `p_{T_m}(A)v_1` via the recurrence for
characteristic polynomials of tridiagonal matrices.
* Uses: symmetric `A` (real inner product ⇒ `<p,q>` symmetric), finite grade. Analogue in Hilbert space:
  `A` self-adjoint, inner product on polynomials induced by the spectral measure of `v_1`.

### 7.9 The Conjugate Gradient algorithm (6.7)
CG = orthogonal projection onto `K_m(A, r_0)` for `A` SPD, i.e. FOM with the Lanczos recurrence;
`x_m = x_0 + V_m y_m`, `y_m = T_m⁻¹(βe_1)` (6.86).

**Algorithm 6.16 (Lanczos method for linear systems):** `v_1 = r_0/β`, `m` Lanczos steps, `x_m = x_0 + V_mT_m⁻¹(βe_1)`.
Residual (6.87): `b − Ax_m = −β_{m+1}(e_mᵀy_m) v_{m+1}` (from (6.6)/(6.18)).

**Algorithm 6.17 (D-Lanczos):** progressive version via `T_m = L_mU_m` (`L_m` unit lower bidiagonal with
`λ_i`, `U_m` upper bidiagonal with diagonal `η_i` and superdiagonal `β_{i+1}`):
`λ_m = β_m/η_{m−1}` (6.88), `η_m = α_m − λ_mβ_m` (6.89); `P_m = V_mU_m⁻¹`, `z_m = L_m⁻¹(βe_1)`,
`p_m = η_m⁻¹(v_m − β_m p_{m−1})`, `ζ_m = −λ_mζ_{m−1}` (`ζ_1 = β`), `x_m = x_{m−1} + ζ_m p_m`.
(Gaussian elimination without pivoting on `T_m`; pivoting/LQ variants — SYMMLQ — mentioned.)

**Proposition 6.20.** For Algorithms 6.16/6.17: (1) `r_m = σ_m v_{m+1}` for scalars `σ_m`; hence the
residuals are mutually orthogonal; (2) the `p_i` are `A`-conjugate: `(Ap_i, p_j) = 0` for `i ≠ j`.
* Proof: (1) from (6.87). (2) `P_mᵀAP_m = U_m^{−T} V_mᵀAV_m U_m⁻¹ = U_m^{−T}T_mU_m⁻¹ = U_m^{−T}L_m`, which is
  lower triangular and symmetric, hence diagonal. Uses symmetry of `A` and `T_m = L_mU_m`.

**Algorithm 6.18 (Conjugate Gradient, standard form).** `r_0 = b − Ax_0`, `p_0 = r_0`; for `j ≥ 0`:
`α_j = (r_j, r_j)/(Ap_j, p_j)`; `x_{j+1} = x_j + α_j p_j`; `r_{j+1} = r_j − α_j Ap_j`;
`β_j = (r_{j+1}, r_{j+1})/(r_j, r_j)`; `p_{j+1} = r_{j+1} + β_j p_j`.
Derivation from the two conditions "`r_j` mutually orthogonal, `p_j` `A`-conjugate" and the ansatz
`x_{j+1} = x_j + α_jp_j` (6.90), `r_{j+1} = r_j − α_jAp_j` (6.91), `p_{j+1} = r_{j+1} + β_jp_j` (6.93):
`(r_{j+1}, r_j) = 0 ⇒ α_j = (r_j,r_j)/(Ap_j,r_j)` (6.92); `(Ap_j, r_j) = (Ap_j, p_j)` since `Ap_j ⊥ p_{j−1}`;
`(p_{j+1}, Ap_j) = 0 ⇒ β_j = −(r_{j+1}, Ap_j)/(p_j, Ap_j)`; with `Ap_j = −(r_{j+1} − r_j)/α_j` (6.94) this is
`β_j = (r_{j+1}, r_{j+1})/(r_j, r_j)`. The CG `α_j, β_j` differ from the Lanczos `α, β`; the CG `p_j` are
multiples of the D-Lanczos `p_{j+1}`. Storage: `x, p, Ap, r` (4 vectors) vs 5 for D-Lanczos.
Invariants (exact arithmetic): `x_j ∈ x_0 + K_j(A, r_0)`, `span{p_0..p_{j−1}} = span{r_0..r_{j−1}} = K_j`,
`r_j ⊥ K_j` (Galerkin), `(r_i, r_j) = 0`, `(Ap_i, p_j) = 0` for `i ≠ j`, `‖x* − x_j‖_A` minimal over
`x_0 + K_j` (Prop 5.2), `(r_j, p_i) = 0` for `i < j`, `(r_j, p_j) = (r_j, r_j)`.
* Uses: `A` SPD (real) — or HPD complex with the same formulas; the `A`-inner product; finite `m`.

**Algorithm 6.19 (CG, three-term recurrence variant).** Residual polynomials `r_m(t)` (`r_m = r_m(A)r_0`,
`r_m(0) = 1`) satisfy `r_{m+1}(t) = ρ_m(r_m(t) − γ_m t r_m(t)) + (1 − ρ_m) r_{m−1}(t)` (6.95), i.e.
`r_{m+1} = ρ_m(r_m − γ_mAr_m) + (1−ρ_m)r_{m−1}` (6.96) with `γ_m = (r_m,r_m)/(Ar_m,r_m)` (`= 1/α_m^{Lanczos}`)
and `ρ_m = [1 − (γ_m/γ_{m−1})((r_m,r_m)/(r_{m−1},r_{m−1}))(1/ρ_{m−1})]⁻¹` (6.97), `ρ_0 = 1`, `x_{−1} = 0`.
Solution recurrence (6.98) via `r_m(t) = 1 − t s_{m−1}(t)`: `x_{m+1} = ρ_m(x_m + γ_m r_m) + (1−ρ_m)x_{m−1}`
(the book prints `x_m − γ_m r_m` and `x_1 = x_0 − γ_0r_0`; the sign consistent with `r_1 = r_0 − γ_0Ar_0`
is `+`; `[uncertain: typo in the book]`). Storage: `r_j, Ar_j, r_{j−1}, x_j, x_{j−1}`.
* Uses: three-term recurrence of the Lanczos vectors (⇒ of the residuals) and consistency `r_m(0) = 1`;
  orthogonality of residuals to compute `ρ_m`.

**Eigenvalue estimates from CG coefficients (6.7.3).** With `T_m = tridiag(η_j, δ_j, η_{j+1})` the
Lanczos matrix and `r_j = scalar · v_{j+1}` (6.99), `r_j = p_j − β_{j−1}p_{j−1}` (6.100):
`δ_{j+1} = (Ar_j, r_j)/(r_j, r_j) = (Ap_j,p_j)/(r_j,r_j) + β_{j−1}²(Ap_{j−1},p_{j−1})/(r_j,r_j) = 1/α_j + β_{j−1}/α_{j−1}`
(6.101) for `j > 0`, `δ_1 = 1/α_0` (6.102); `η_{j+1} = |(Ar_{j−1}, r_j)|/(‖r_{j−1}‖‖r_j‖) = sqrt(β_{j−1})/α_{j−1}`
(using `(Ar_{j−1}, r_j) = −(r_j, r_j)/α_{j−1}`). Full matrix (6.103):
`T_m = tridiag( sqrt(β_{j−1})/α_{j−1} ; 1/α_j + β_{j−1}/α_{j−1} ; sqrt(β_j)/α_j )` with `δ_1 = 1/α_0`.
Eigenvalues of `T_m` (Ritz values) estimate extreme eigenvalues of `A`, hence `κ(A)` and error bounds.
* Uses: `A`-conjugacy and residual orthogonality; symmetric `A`.

### 7.10 The Conjugate Residual method (6.8)
Analogue of GMRES for Hermitian `A` (in practice HPD so that `(r_j, Ar_j) ≠ 0`): residuals `A`-orthogonal
(conjugate), `Ap_i` mutually orthogonal (`p_i` are `AᵀA`-orthogonal).
**Algorithm 6.20 (CR):** `r_0 = b − Ax_0`, `p_0 = r_0`; `α_j = (r_j, Ar_j)/(Ap_j, Ap_j)`; `x_{j+1} = x_j + α_jp_j`;
`r_{j+1} = r_j − α_jAp_j`; `β_j = (r_{j+1}, Ar_{j+1})/(r_j, Ar_j)`; `p_{j+1} = r_{j+1} + β_jp_j`;
`Ap_{j+1} = Ar_{j+1} + β_jAp_j` (one matvec per step; 5 stored vectors). Minimizes `‖b − Ax‖₂` over
`x_0 + K_m` (mathematically = GMRES/MINRES for Hermitian `A`).

### 7.11 GCR, ORTHOMIN, ORTHODIR (6.9)

**Lemma 6.21 (minimal residual via `AᵀA`-orthogonal directions).** Let `p_0, …, p_{m−1}` be such that for
each `j ≤ m`, `{p_0..p_{j−1}}` is a basis of `K_j(A, r_0)`, and `(Ap_i, Ap_k) = 0` for `i ≠ k`. Then the
minimal-residual approximation in `x_0 + K_m(A, r_0)` is
`x_m = x_0 + Σ_{i<m} ((r_0, Ap_i)/(Ap_i, Ap_i)) p_i` (6.104), and
`x_m = x_{m−1} + ((r_{m−1}, Ap_{m−1})/(Ap_{m−1}, Ap_{m−1})) p_{m−1}` (6.105).
* Uses: Prop 5.3 (`r_m ⊥ AK_m`), orthogonality of the `Ap_i` to decouple coefficients;
  `(r_{m−1}, Ap_{m−1}) = (r_0, Ap_{m−1})`. Hilbert-space general. Requires `Ap_i ≠ 0` (`A` injective on `K_m`).

**Algorithm 6.21 (GCR):** `p_0 = r_0`; `α_j = (r_j, Ap_j)/(Ap_j, Ap_j)`; `x_{j+1} = x_j + α_jp_j`;
`r_{j+1} = r_j − α_jAp_j`; `β_ij = −(Ar_{j+1}, Ap_i)/(Ap_i, Ap_i)`, `i ≤ j`; `p_{j+1} = r_{j+1} + Σ_{i≤j} β_ij p_i`
(and `Ap_{j+1} = Ar_{j+1} + Σ β_ij Ap_i` to keep one matvec/step). Mathematically equivalent to full GMRES;
stores `p_i` and `Ap_i` (double GMRES storage). **GCR(m)** restarted; **ORTHOMIN(k)**: orthogonalize only
against the last `k` directions (`i = j−k+1..j`). **ORTHODIR:** `p_{j+1} = Ap_j + Σ_{i≤j} β_ij p_i` (6.107) with
`β_ij = −(A²p_j, Ap_i)/(Ap_i, Ap_i)`; restarted/truncated versions.

### 7.12 The Faber–Manteuffel theorem (6.10)
Question: which `A` admit optimal (error/residual-minimizing) Krylov methods with short recurrences?
If Arnoldi reduces to the `s`-term IOM (`h_ij = 0` for `i < j−s+1`) then `(s−1)`-term update recurrences exist,
and conversely; so it suffices to study when Arnoldi's `H_m` is banded.

**Proposition 6.22.** If `Aᵀv ∈ K_s(A, v)` for every `v`, then DIOM(s) is mathematically equivalent to FOM.
* Proof: `h_ij = (Av_j, v_i) = (v_j, Aᵀv_i) = (v_j, q_{v_i}(A)v_i)` with `deg q ≤ s−1`, so `h_ij = 0` for `i < j−s+1`.
* Remark: `Aᵀ = q(A)` for a polynomial `q` ⇒ `A` normal; conversely `A` normal ⇒ `∃ q` of degree `≤ n−1`
  with `Aᴴ = q(A)` (interpolate `q(λ_j) = λ̄_j` on the unitary diagonalization). `ν(A)` := least such degree.

**Lemma 6.23 (Faber–Manteuffel).** `A` nonsingular. `Aᴴv ∈ K_s(A, v)` for every `v` iff `A` is normal and
`ν(A) ≤ s − 1`.
* Uses: Lemma 1.15 (eigenvectors of `A` are eigenvectors of `Aᴴ` ⇒ normal), minimal polynomial of `A`
  (degree `μ` = number of distinct eigenvalues for normal `A`), a vector `w` of grade `μ`, linear
  independence of `w, Aw, …, A^{μ−1}w`, nonsingularity to exclude `Aᴴw = 0`. Finite-dimensional.

**Theorem 6.24 (Faber–Manteuffel; stated without proof).** Define `CG(s)` = matrices such that for every
`v_1`, `(Av_j, v_i) = 0` whenever `i + s ≤ j ≤ μ(v_1) − 1` (Arnoldi with any inner product). Then
`A ∈ CG(s)` iff the minimal polynomial of `A` has degree `≤ s`, or `A` is normal with `ν(A) ≤ s−1`.
Case `ν(A) ≤ 1` (three-term recurrences, `s = 2`): `A` has minimal polynomial of degree ≤ 1, or is
Hermitian, or `A = e^{iθ}(ηI + B)` with `θ, η` real and `B` skew-Hermitian (CG; the skew-Hermitian CG variant
of Ch. 9 (Concus–Golub–Widlund)).
* Uses: finite dimension throughout (minimal polynomial, grade).

### 7.13 Convergence analysis (6.11)

**Real Chebyshev polynomials (6.11.1).** `C_k(t) = cos(k arccos t)` on `[−1,1]` (6.109);
`C_{k+1} = 2tC_k − C_{k−1}`, `C_0 = 1`, `C_1 = t`; `C_k(t) = cosh(k arccosh t)` for `|t| ≥ 1` (6.110);
`C_k(t) = ½[(t + sqrt(t²−1))^k + (t + sqrt(t²−1))^{−k}]` (6.111); `C_k(t) ≈ ½(t + sqrt(t²−1))^k` (6.112).

**Theorem 6.25 (Chebyshev min–max; proof referred to Cheney).** `[α, β] ⊂ ℝ` nonempty, `γ ∉ [α, β]`. Then
`min_{p ∈ P_k, p(γ)=1} max_{t∈[α,β]} |p(t)|` is attained by
`Ĉ_k(t) = C_k(1 + 2(α − t)/(β − α)) / C_k(1 + 2(α − γ)/(β − α))` (6.113), and equals
`1/|C_k(1 + 2(α−γ)/(β−α))| = 1/|C_k(2(μ − γ)/(β − α))|`, `μ = (α+β)/2` (corollary).
* Uses: real approximation theory (equioscillation). Pure analysis; no linear algebra.

**Complex Chebyshev polynomials (6.11.2).** `C_k(z) = ½(w^k + w^{−k})` where `z = ½(w + w⁻¹)` (6.114)
(independent of the root chosen); same recurrence (6.115). Joukowski map `J(w) = ½(w + w⁻¹)` sends the circle
`C(0,ρ)` to the ellipse with foci `±1`, semi-axes `½(ρ + ρ⁻¹)`, `½|ρ − ρ⁻¹|` (take `ρ ≥ 1`; `ρ = 1` gives
`[−1,1]`). Chebyshev polynomials are **not** optimal on ellipses in general, only asymptotically.

**Lemma 6.26 (Zarantonello; proof referred out).** Circle `C(0,ρ)`, `γ` not enclosed (`|γ| > ρ`):
`min_{p∈P_k, p(γ)=1} max_{|z|=ρ} |p(z)| = (ρ/|γ|)^k` (6.116), attained by `(z/γ)^k`. Shifted version for
`C(c,ρ)`: value `(ρ/|γ − c|)^k`.

**Theorem 6.27 (asymptotic optimality on ellipses).** `E` = image of `C(0,ρ)` under `J` (`ρ ≥ 1`), `γ` not
enclosed by `E`, `w_γ` the dominant root of `J(w) = γ`. Then
`(ρ/|w_γ|)^k ≤ min_{p∈P_k, p(γ)=1} max_{z∈E} |p(z)| ≤ (ρ^k + ρ^{−k})/|w_γ^k + w_γ^{−k}|` (6.117).
* Proof: upper bound from the trial polynomial `(w^k + w^{−k})/(w_γ^k + w_γ^{−k})` (scaled Chebyshev),
  whose maximum on `E` is at `w = ρ`; lower bound by writing `p(z) = w^{−k}·(polynomial of degree 2k in w)/(…)`
  and applying Zarantonello on `C(0,ρ)` to the degree-`2k` polynomial normalized at `w_γ`. Gap → 0 as `k → ∞`.
* General ellipse `E(c, d, a)` (center `c`, focal distance `d`, semi-major axis `a`; `d, a` may be purely
  imaginary): near-best polynomial `Ĉ_k(z) = C_k((c − z)/d)/C_k((c − γ)/d)` (6.119), with
  `max_{E} |Ĉ_k| = |C_k(a/d)|/|C_k((c−γ)/d)|` (attained at `c + a`), explicit (6.120) and asymptotic
  `≈ ((a + sqrt(a² − d²))/(c − γ + sqrt((c−γ)² − d²)))^k` (6.121). (Fischer–Freund give sharper results.)

**Lemma 6.28 (CG polynomial characterization).** `x_m` the `m`-th CG iterate, `d_m = x* − x_m`. Then
`x_m = x_0 + q_m(A)r_0` with `q_m ∈ P_{m−1}` such that `‖(I − Aq_m(A))d_0‖_A = min_{q∈P_{m−1}} ‖(I − Aq(A))d_0‖_A`.
* Uses: Prop 5.2 (A-norm optimality over `x_0 + K_m`) and `K_m = {q(A)r_0}`; `d = d_0 − q(A)r_0 = (I − Aq(A))d_0`.

**Theorem 6.29 (CG convergence bound).** `A` SPD, `η = λ_min/(λ_max − λ_min)` (6.122). Then
`‖x* − x_m‖_A ≤ ‖x* − x_0‖_A / C_m(1 + 2η)` (6.123). Equivalently (6.128), with `κ = λ_max/λ_min`:
`‖x* − x_m‖_A ≤ 2 ((sqrt κ − 1)/(sqrt κ + 1))^m ‖x* − x_0‖_A`.
* Uses: Lemma 6.28 ⇒ `‖d_m‖_A = min_{r∈P_m, r(0)=1} ‖r(A)d_0‖_A`; spectral theorem
  (`‖r(A)d_0‖_A² = Σ λ_i r(λ_i)² ξ_i² ≤ max_{λ∈[λ_min,λ_max]} r(λ)² ‖d_0‖_A²`); Theorem 6.25 with
  `[α,β] = [λ_min, λ_max]`, `γ = 0`: `1 + 2(α − 0)/(β − α) = 1 + 2η`; then (6.111)–(6.127):
  `C_m(1+2η) ≥ ½(1 + 2η + 2sqrt(η(η+1)))^m = ½((sqrt κ + 1)/(sqrt κ − 1))^m`.
  Extends verbatim to bounded self-adjoint coercive operators on a Hilbert space with
  `σ(A) ⊂ [λ_min, λ_max]` (spectral measure replaces the eigen-expansion); only `m` finite.
  Comparison: steepest descent has factor `(κ−1)/(κ+1)` per step; CG replaces `κ` by `sqrt κ`.

**Theorem 6.30 (GMRES(m) convergence for positive definite `A`).** `A` real positive definite (Saad's
sense) ⇒ GMRES(m) converges for every `m ≥ 1`.
* Proof: `K_m ∋ r_0` at each restart, so each outer step reduces the residual at least as much as one MR
  step (Alg 5.3); apply (5.15): `‖r‖` decreases by the factor `(1 − μ²/σ²)^{1/2} < 1` per cycle.
  Uses Thm 5.10 (coercivity); Hilbert-space general.

**Lemma 6.31 (GMRES polynomial characterization).** `x_m = x_0 + q_m(A)r_0`, `q_m ∈ P_{m−1}`, with
`‖r_m‖₂ = ‖(I − Aq_m(A))r_0‖₂ = min_{q∈P_{m−1}} ‖(I − Aq(A))r_0‖₂` (Prop 5.3 + `K_m = {q(A)r_0}`).
Remark: no analogue of Thm 6.29 unless `A` is normal.

**Proposition 6.32 (GMRES bound for diagonalizable `A`).** `A = XΛX⁻¹`, `Λ = diag(λ_i)`;
`ε^{(m)} = min_{p∈P_m, p(0)=1} max_i |p(λ_i)|`. Then `‖r_m‖₂ ≤ κ₂(X) ε^{(m)} ‖r_0‖₂`.
* Proof: for any admissible `p` with `b − Ax = p(A)r_0`: `‖p(A)r_0‖ = ‖Xp(Λ)X⁻¹r_0‖ ≤ ‖X‖‖X⁻¹‖ max_i|p(λ_i)| ‖r_0‖`;
  minimality of `r_m`. Uses diagonalizability; for normal `A`, `κ₂(X) = 1`.

**Corollary 6.33 (ellipse bound).** `A` diagonalizable with spectrum in an ellipse `E(c, d, a)` not
enclosing the origin. Then `‖r_m‖₂ ≤ κ₂(X) |C_m(a/d)|/|C_m(c/d)| ‖r_0‖₂`, and
`|C_m(a/d)|/|C_m(c/d)| ≈ ((a + sqrt(a² − d²))/(c + sqrt(c² − d²)))^m`.
* Proof: bound `ε^{(m)}` by the max over the ellipse (maximum modulus principle) using the trial
  polynomial `Ĉ_m` (6.119) with `γ = 0`. Of limited practical value since `κ₂(X)` is unknown/large
  unless `A` is nearly normal.

### 7.14 Block Krylov methods (6.12, brief)
**Algorithm 6.22 (block Arnoldi):** `V_1 ∈ ℝ^{n×p}` orthonormal; `H_ij = V_iᵀAV_j`; `W_j = AV_j − Σ_{i≤j} V_iH_ij`;
QR `W_j = V_{j+1}H_{j+1,j}`. With `U_m = [V_1..V_m]`, `H_m = (H_ij)` band-Hessenberg (`p` subdiagonals),
`E_m` = last `p` columns of `I_{mp}`: `AU_m = U_mH_m + V_{m+1}H_{m+1,m}E_mᵀ` (6.129).
**Algorithm 6.23 (block MGS variant).** **Algorithm 6.24 (Ruhe's variant):** vectors processed one at a
time with a delay of `p`: `Av_k` orthogonalized against `v_1..v_j`, `k = j − p + 1`; `Av_k = Σ_{i≤k+p} h_ik v_i`,
`AV_m = V_{m+p}H̄_m` (6.130), `H̄_m ∈ ℝ^{(m+p)×m}`; `p = 1` is Arnoldi. Block FOM/GMRES for `AX = B`
(multiple right-hand sides) follow by replacing `βe_1` with the `R` factor of `R_0 = V_1R_1`.
* Uses: same algebra as Arnoldi; matrices/blocks.

---

## 8. Chapter 7 Krylov Subspace Methods Part II (summary)

Setting: `A ∈ ℝ^{n×n}` nonsymmetric; `L_m = K_m(Aᵀ, w_1)`.

* **Algorithm 7.1 (Lanczos biorthogonalization / two-sided Lanczos).** `(v_1, w_1) = 1`; `α_j = (Av_j, w_j)`;
  `v̂_{j+1} = Av_j − α_jv_j − β_jv_{j−1}`; `ŵ_{j+1} = Aᵀw_j − α_jw_j − δ_jw_{j−1}`; `δ_{j+1} = |(v̂_{j+1}, ŵ_{j+1})|^{1/2}`
  (stop if 0); `β_{j+1} = (v̂_{j+1}, ŵ_{j+1})/δ_{j+1}`; `w_{j+1} = ŵ_{j+1}/β_{j+1}`, `v_{j+1} = v̂_{j+1}/δ_{j+1}`. Any scaling
  with `δ_{j+1}β_{j+1} = (v̂_{j+1}, ŵ_{j+1})` (7.1) works. `T_m = tridiag(δ_j, α_j, β_{j+1})` (7.2), nonsymmetric.
* **Proposition 7.1.** If no breakdown before step `m`: `(v_j, w_i) = δ_ij` (biorthogonal system);
  `{v_i}` basis of `K_m(A, v_1)`, `{w_i}` basis of `K_m(Aᵀ, w_1)`; `AV_m = V_mT_m + δ_{m+1}v_{m+1}e_mᵀ` (7.3),
  `AᵀW_m = W_mT_mᵀ + β_{m+1}w_{m+1}e_mᵀ` (7.4), `W_mᵀAV_m = T_m` (7.5). Proof by induction using the
  recurrences and `(Av_j, w_i) = (v_j, Aᵀw_i)`. Uses only bilinear pairing + transpose; Hilbert-space general.
* Breakdown: `(v̂_{j+1}, ŵ_{j+1}) = 0` with (a) `v̂ = 0` or `ŵ = 0` (lucky: invariant subspace) or (b) both nonzero
  (serious breakdown; look-ahead Lanczos). Practical variants: normalize by 2-norms (then `(v_j,w_j) ≠ 1`).
* **Algorithm 7.2 (two-sided Lanczos for linear systems):** `v_1 = r_0/β`, `x_m = x_0 + V_mT_m⁻¹(βe_1)`
  (oblique projection onto `K_m(A,r_0)` orthogonal to `K_m(Aᵀ,w_1)`); residual (7.9):
  `‖b − Ax_j‖₂ = |δ_{j+1} e_jᵀ y_j| ‖v_{j+1}‖₂`.
* **Algorithm 7.3 (BCG, Lanczos 1952 / Fletcher 1974).** `r_0`, `r*_0` with `(r_0, r*_0) ≠ 0`, `p_0 = r_0`, `p*_0 = r*_0`;
  `α_j = (r_j, r*_j)/(Ap_j, p*_j)`; `x_{j+1} = x_j + α_jp_j`; `r_{j+1} = r_j − α_jAp_j`; `r*_{j+1} = r*_j − α_jAᵀp*_j`;
  `β_j = (r_{j+1}, r*_{j+1})/(r_j, r*_j)`; `p_{j+1} = r_{j+1} + β_jp_j`; `p*_{j+1} = r*_{j+1} + β_jp*_j`. Derived from
  `T_m = L_mU_m`, `P_m = V_mU_m⁻¹`, `P*_m = W_mL_m^{−T}` (7.10)–(7.12) with `(P*_m)ᵀAP_m = I` (`A`-biconjugate).
  Solves the dual system `Aᵀx* = b*` simultaneously. Mathematically = Alg 7.2 (Galerkin/Petrov–Galerkin).
* **Proposition 7.2.** `(r_j, r*_i) = 0` for `i ≠ j` (7.13) (biorthogonal residuals), `(Ap_j, p*_i) = 0` for
  `i ≠ j` (7.14) (`A`-biconjugate directions). (Proof left as exercise.)
* **QMR (7.3.2).** `AV_m = V_{m+1}T̄_m` (7.15), `T̄_m = [T_m; δ_{m+1}e_mᵀ]`; `b − A(x_0 + V_my) = V_{m+1}(βe_1 − T̄_my)` (7.16);
  since `V_{m+1}` is not orthonormal, minimize the **quasi-residual** `J(y) = ‖βe_1 − T̄_my‖₂` instead.
  **Algorithm 7.4 (QMR):** DQGMRES-style Givens QR of `T̄_m` with only two previous rotations;
  `p_m = (v_m − Σ_{i=m−2}^{m−1} t_im p_i)/t_mm`, `x_m = x_{m−1} + γ_m p_m`. Identities: `ρ_m^Q = |s_1⋯s_m|‖r_0‖ = |s_m|ρ_{m−1}^Q`
  (7.18); BCG residual `r_m^B = −h_{m+1,m}(e_mᵀy_m)v_{m+1}`; `γ_{m+1}v_{m+1} = c_m r_m^B` (7.19); `ρ_m^Q = |c_m| ρ_m^B` (7.20).
* **Proposition 7.3.** `‖b − Ax_m^Q‖₂ ≤ ‖V_{m+1}‖₂ |s_1⋯s_m| ‖r_0‖₂` (7.21); with `‖V_{m+1}‖₂ ≤ sqrt(m+1)` if the
  `v_i` are unit vectors.
* **Theorem 7.4.** (No breakdown up to `m`) `‖r_m^Q‖₂ ≤ κ₂(V_{m+1}) ‖r_m^G‖₂` — same proof as Thm 6.11;
  `V_{m+1}` is automatically full rank here.
* (7.23)–(7.24): `1/(ρ_j^Q)² = 1/(ρ_{j−1}^Q)² + 1/(ρ_j^B)²`, `ρ_m^Q = (Σ_{i=0}^m (ρ_i^B)^{−2})^{−1/2}` (harmonic-mean
  smoothing of the BCG residuals); **Proposition 7.5:** `ρ_m^Q ≤ ρ̃_m^B ≤ sqrt(m+1) ρ_m^Q` (7.25) with `ρ̃_m^B` the best BCG
  residual norm in the first `m` steps. Exact residual: `b − Ax_m^Q = γ_{m+1}z_{m+1}` (7.26), `z_{m+1} = −s_mz_m + c_mv_{m+1}` (7.27).
  **Algorithm 7.5 (QMR smoothing):** QMRS applied to BCG gives QMR.
* **Transpose-free variants (7.4):** CGS (Algorithm 7.6; residual polynomial `φ_j(A)²r_0`), BiCGSTAB (Algorithm 7.7;
  `ψ_j(A)φ_j(A)r_0` with `ψ_j(t) = (1 − ω_jt)ψ_{j−1}(t)`, `ω_j` local MR step), TFQMR (Algorithm 7.8; QMR smoothing
  of CGS). No numbered theorems; derivations via polynomial recurrences.

## 9. Chapter 8 Methods related to the normal equations (summary)

* **8.1:** NR (normal residual) system `AᵀAx = Aᵀb` (8.1); NE (normal error) system `AAᵀu = b`, `x = Aᵀu` (8.3);
  both SPD when `A` nonsingular; `κ₂(AᵀA) = κ₂(A)²`; least-squares (overdetermined) and minimum-norm
  (underdetermined) interpretations.
* **8.2 Row projection methods:** relaxation on (8.1)/(8.3) needs one row/column of `A` at a time.
  NE-SOR / Kaczmarz (Algorithm 8.1): `x ← x + ω (β_i − (x, a_i))/‖a_i‖² a_i` with `a_i = Aᵀe_i` (projection of
  `x` onto the hyperplane of equation `i`); NR-SOR (Algorithm 8.2): coordinate relaxation on `AᵀA` using
  columns; **Cimmino** (Algorithm 8.3): additive (Jacobi-like) row projection `x_{k+1} = x_k + ω Σ_i (β_i − (x_k,a_i))/‖a_i‖² a_i`
  = Richardson on `AD⁻¹Aᵀ`-type systems; convergence from Chapter 4 theory (Theorem 4.10 for SOR on SPD).
* **8.3 CG on normal equations:** **CGNR (Algorithm 8.4):** CG on `AᵀAx = Aᵀb`; `z_i = Aᵀr_i`, `w_i = Ap_i`,
  `α_i = ‖z_i‖²/‖w_i‖²`, `β_i = ‖z_{i+1}‖²/‖z_i‖²`, `p_{i+1} = z_{i+1} + β_ip_i`. Optimality: minimizes
  `‖b − Ax‖₂` over `x_0 + K_m(AᵀA, Aᵀr_0)` (the `AᵀA`-norm of the error = residual norm). **CGNE / Craig
  (Algorithm 8.5):** CG on `AAᵀu = b` rewritten in `x = Aᵀu`: `α_i = (r_i,r_i)/(p_i,p_i)`, `p_{i+1} = Aᵀr_{i+1} + β_ip_i`;
  minimizes `‖x* − x‖₂` over `x_0 + K_m(AᵀA, Aᵀr_0)` (`AAᵀ`-norm of the `u`-error = 2-norm of the `x`-error).
  Both suffer from `κ²`.
* **8.4 Saddle-point problems:** `[[A, B],[Bᵀ, 0]][x;y] = [b;c]` (8.30) (Lagrangian of `min ½(Ax,x) − (b,x)` s.t. `Bᵀx = c`).
  **Uzawa (Algorithm 8.6):** `x_{k+1} = A⁻¹(b − By_k)`, `y_{k+1} = y_k + ω(Bᵀx_{k+1} − c)` = Richardson on the Schur
  complement system `BᵀA⁻¹By = BᵀA⁻¹b − c` (8.32). **Corollary 8.1:** `A` SPD, `B` full column rank ⇒ `S = BᵀA⁻¹B` SPD
  and Uzawa converges iff `0 < ω < 2/λ_max(S)`; `ω_opt = 2/(λ_min(S) + λ_max(S))` (from Example 4.1).
  **Arrow–Hurwicz (Algorithm 8.7)** (inexact inner solve). Uses: Richardson theory, SPD Schur complements.

## 10. Chapter 9 Preconditioned iterations (summary)

* **9.1:** left `M⁻¹Ax = M⁻¹b` (9.1), right `AM⁻¹u = b, x = M⁻¹u` (9.2), split `M_L⁻¹AM_R⁻¹u = M_L⁻¹b` (9.3).
* **9.2 PCG.** `A`, `M` SPD. `M⁻¹A` is self-adjoint for `(·,·)_M` and for `(·,·)_A` (Section 1.11 remark).
  **Algorithm 9.1 (PCG):** CG for `M⁻¹A` in the `M`-inner product, written with `r_j = b − Ax_j`, `z_j = M⁻¹r_j`:
  `α_j = (r_j, z_j)/(Ap_j, p_j)`, `x_{j+1} = x_j + α_jp_j`, `r_{j+1} = r_j − α_jAp_j`, `z_{j+1} = M⁻¹r_{j+1}`,
  `β_j = (r_{j+1}, z_{j+1})/(r_j, z_j)`, `p_{j+1} = z_{j+1} + β_jp_j`. Invariants: `(r_i, z_j) = 0` (`i ≠ j`),
  `(Ap_i, p_j) = 0`, minimizes `‖x* − x‖_A` over `x_0 + K_m(M⁻¹A, z_0)`; convergence bound (6.128) with `κ(M⁻¹A)`.
  **Algorithm 9.2 (split-preconditioner CG, `M = LLᵀ`):** CG on `L⁻¹AL^{−T}`; produces **identical iterates**
  to Alg 9.1 (change of variables `p̂ = Lᵀp`, `u = Lᵀx`, `r̂ = L⁻¹r`). Efficient implementations (9.2.2):
  Eisenstat's trick for SSOR-type `M = (D−E)D⁻¹(D−F)` (Algorithm 9.3: `w = Âv` with one triangular solve
  each), diagonal scaling.
* **9.3 Preconditioned GMRES.** **Algorithm 9.4 (left):** GMRES on `M⁻¹A` from `z_0 = M⁻¹r_0`; minimizes
  `‖M⁻¹(b − Ax)‖₂` over `x_0 + K_m(M⁻¹A, z_0)`; residual estimate is the preconditioned residual.
  **Algorithm 9.5 (right):** Arnoldi on `AM⁻¹` from `v_1 = r_0/β`; `x_m = x_0 + M⁻¹V_my_m`; minimizes `‖b − Ax‖₂`
  over `x_0 + M⁻¹K_m(AM⁻¹, r_0)`; residual available directly. Split: `M = LU`, `L⁻¹AU⁻¹`.
  **Proposition 9.1:** both give `x_m = x_0 + s_{m−1}(M⁻¹A)z_0 = x_0 + M⁻¹s_{m−1}(AM⁻¹)r_0` for a polynomial `s_{m−1}`;
  left minimizes `‖M⁻¹(b − Ax_m)‖`, right minimizes `‖b − Ax_m‖` over the **same** affine space
  (`K_m(M⁻¹A, M⁻¹r_0) = M⁻¹K_m(AM⁻¹, r_0)`). Differences matter only for ill-conditioned `M`.
* **9.4 Flexible variants.** **Algorithm 9.6 (FGMRES):** `z_j = M_j⁻¹v_j` (variable preconditioner, any `z_j`),
  `w = Az_j` orthogonalized against `v_1..v_j`, `x_m = x_0 + Z_my_m`, `y_m = argmin‖βe_1 − H̄_my‖`. Relations
  `AZ_m = V_{m+1}H̄_m` (9.22), `AZ_m = V_mH_m + v̂_{m+1}e_mᵀ` (9.23); `b − A(x_0 + Z_my) = V_{m+1}(βe_1 − H̄_my)`.
  **Proposition 9.2:** `x_m` minimizes `‖b − Ax‖₂` over `x_0 + span{Z_m}`. **Proposition 9.3:** if `β ≠ 0`,
  `h_{i+1,i} ≠ 0` for `i < j`, and `H_j` nonsingular, then `x_j` is exact iff `h_{j+1,j} = 0` (unlike GMRES,
  nonsingularity of `H_j` must be assumed). **DQGMRES** flexible version (9.4.2): truncated FGMRES.
* **9.5** PCG for the normal equations (Algorithms 9.7/9.8, left-preconditioned CGNR/CGNE).
* **9.6 Concus–Golub–Widlund:** `A = M − N` with `M` SPD and `N` skew-symmetric; then `M⁻¹A = I − M⁻¹N` is
  self-adjoint-plus-skew in the `M`-inner product, so a three-term (Lanczos-type) recurrence exists
  (Faber–Manteuffel case `A = ηI + B`, `B` skew).

---

## 11. Structural observations

### 11.1 Generality of hypotheses (general / normal / Hermitian / SPD / real symmetric)

| Result | Field / symmetry hypothesis actually used |
|---|---|
| 1.12 projectors, Lemma 1.36, Prop 1.37, Thm 1.38, Cor 1.39 | any (complex) inner product space; no symmetry of any operator |
| 1.13 perturbation, `κ(A)` | any normed space, `A` invertible |
| Thm 1.34 | **real** `A`, positive definite in Saad's (non-symmetric) sense |
| Thm 1.35 | any complex square `A` |
| Thm 4.1, Cor 4.2, Richardson Example 4.1 | any `G`; Richardson optimal `α` needs real spectrum |
| Thm 4.4 (regular splitting) | entrywise nonnegativity — real matrices |
| Thms 4.6–4.9 (Gershgorin, diag. dominance) | complex entries allowed; uses entries and (for 4.7/4.9) irreducibility |
| Thm 4.10 (SOR ⇔ SPD) | real symmetric |
| Props 4.12–4.16 (Property A, consistent ordering, Young) | any entries; graph structure/ordering |
| Prop 5.1(i), Prop 5.2, Prop 5.5, Lemma 5.8, Thm 5.9, Alg 5.2 | **SPD** (real symmetric positive definite; HPD works identically) |
| Prop 5.1(ii), Prop 5.3, Prop 5.4, Lemma 6.21, GMRES/GCR/ORTHOMIN/ORTHODIR | **arbitrary** square `A` (Prop 5.3 does not even need nonsingularity) |
| Prop 5.6, Thm 5.7 | arbitrary `A` |
| Alg 5.3 / Thm 5.10 / Thm 6.30 | real **positive definite** (coercive), non-symmetric allowed |
| Alg 5.4 (RNSD), CGNR/CGNE | `A` nonsingular only |
| Props 6.1–6.8, Arnoldi, FOM, IOM/DIOM, GMRES, DQGMRES, 6.5.7, 6.5.8 | arbitrary `A` over ℝ or ℂ |
| Thm 6.11, Thm 7.4 | arbitrary `A` |
| Thm 6.19, Lanczos, 6.6.2, Prop 6.20, CG, CR, 6.7.3 | **symmetric** (Hermitian) for the structure; **SPD/HPD** for well-definedness of `α_j` (CG: `(Ap,p) ≠ 0`; CR: `(r, Ar) ≠ 0`) and optimality |
| Prop 6.22, Lemma 6.23, Thm 6.24 | general complex; conclusions involve **normality** |
| Thm 6.25, Lemma 6.26, Thm 6.27 | pure approximation theory (real interval / complex ellipse) |
| Lemma 6.28, Thm 6.29 | SPD (spectral theorem) |
| Lemma 6.31, Prop 6.32, Cor 6.33 | diagonalizable (`κ₂(X)`); normal gives `κ₂(X)=1` |
| Ch. 7 (two-sided Lanczos, BCG, QMR) | arbitrary real (or complex with `Aᵀ`/bilinear form) |
| Ch. 9 PCG | `A`, `M` SPD; Prop 9.1–9.3 arbitrary `A`, `M` nonsingular |

Saad states almost everything for real matrices but notes (6.5.9, 1.11) that the Krylov theory transfers
to ℂ with the Hermitian inner product; the one genuinely real-only notion is "positive definite" in the
non-symmetric sense (Thm 1.34, Thm 5.10, Thm 6.30): for complex `A` the analogous hypothesis is
`Re (Au,u) > 0`, i.e. `H = (A + Aᴴ)/2` HPD, and the proofs go through with `Re`.

### 11.2 What generalizes to bounded operators on Hilbert spaces, what needs finite dimension

**Hilbert-space general (bounded operators; finite `m`; subspaces `K`, `L` finite-dimensional or closed):**
* All of Section 1.12 except the dimension-count in Lemma 1.36 (replace "same dimension `m`" by
  `M ⊕ L^⊥ = H`, or keep `M, L` finite-dimensional of equal dimension — then the proof is unchanged).
* Perturbation analysis / condition number (Banach spaces, Neumann series).
* Thm 1.35 (for eigenvalues; for the spectrum via the closure of the numerical range).
* Thm 4.1 forward direction (`ρ(G) < 1 ⇒` convergence, via Gelfand), Cor 4.2; **not** the converse.
  Convergence factor `= ρ(G)` uses Jordan form (finite-dimensional); Gelfand's formula gives the
  uniform version in general.
* Chapter 5 entirely (Props 5.1–5.6, Thm 5.7, steepest descent, MR, Kantorovich via spectral theorem,
  Thms 5.9, 5.10, additive/multiplicative procedures), with `K, L` finite-dimensional and
  "positive definite" read as coercive (`Re(Au,u) ≥ μ‖u‖²`); Thm 5.9/5.10 need `λ_min, λ_max` replaced
  by spectral bounds / coercivity and operator-norm constants.
* Prop 6.3, Arnoldi relations (Props 6.4, 6.5), FOM residual (Prop 6.7), GMRES optimality and all Givens
  identities (Prop 6.9, 6.10, (6.47), (6.62)), DQGMRES identities, Thm 6.11, the FOM–GMRES relations
  (Props 6.12–6.17, Lemma 6.16), residual smoothing (Lemma 6.18), Lanczos (Thm 6.19 for self-adjoint `A`),
  CG/CR derivations and invariants (Prop 6.20), Lemma 6.21 (GCR), Chebyshev min–max theory, CG bound
  Thm 6.29 (self-adjoint coercive `A`, spectral theorem), Thm 6.30, Lemma 6.31, two-sided Lanczos (Prop 7.1),
  BCG/QMR identities, PCG/FGMRES propositions — all hold for a bounded operator on a Hilbert space as
  long as the process has not broken down (`h_{j+1,j} ≠ 0`, `(Ap,p) ≠ 0`, etc.). Breakdown handling
  ("`w_j = 0 ⇒ K_j` invariant ⇒ exact") also holds.
* Prop 6.32 / Cor 6.33 need a "diagonalizable" structure: in Hilbert space the natural analogue is a
  normal operator (`κ₂(X)=1`, spectrum in a compact set) or a Riesz basis of eigenvectors.

**Needs finite dimension:**
* Jordan/Schur forms; Thm 1.10 converse; Thm 4.1 converse; the asymptotic convergence-factor analysis.
* Cayley–Hamilton, **minimal polynomial**, **grade** of a vector, Prop 6.1 (invariance of `K_μ`), Prop 6.2
  in the form `dim K_m = min(m, μ)` (in infinite dimension `dim K_m = m` for all `m` is possible), Prop 6.6
  ("breakdown ⇔ grade = j" — the "⇐" direction and "eventual breakdown" need finite grade), the statement
  "full GMRES/CG converge in at most `n` steps", Faber–Manteuffel (Lemma 6.23, Thm 6.24: minimal
  polynomial of `A`, `ν(A)`, `Aᴴ = q(A)`), Prop 6.32 as stated (finitely many eigenvalues).
* Everything entrywise: Gershgorin, diagonal dominance, irreducibility, Property A, consistent ordering,
  Young's theorem, nonnegative matrices/M-matrices/regular splittings, Jacobi/GS/SOR themselves (they can
  be phrased via a decomposition `A = D − E − F` w.r.t. a fixed basis, which is finite-dimensional or at
  least basis-dependent).
* Block Krylov relations are finite-dimensional bookkeeping but hold for operators as well.

**Real vs complex:** the Krylov algebra is field-independent (any field with a conjugation-compatible
inner product); only positive definiteness (needs an ordered field for `(Au,u) > 0`), Chebyshev bounds
(`ℝ`/`ℂ` analysis) and Givens rotations (real `s_i`, complex `c_i`) care.

### 11.3 Dependency graph (main results)

```
1.12 projectors (Lemma 1.36, Thm 1.38, Cor 1.39)
   ├─> 5.1 well-posedness (Prop 5.1)  ──> 5.2 optimality (Prop 5.2 [SPD], Prop 5.3 [any A])
   │        Prop 5.4 (residual projector, L=AK), Prop 5.5 (A-error projector, L=K)
   │        Prop 5.6 (invariant K ⇒ exact) ──> Prop 6.6 remark / Prop 6.10 (lucky breakdown)
   │        Thm 5.7 (projected residual bound)
   ├─> 5.3 one-dim: Alg 5.2 SD (Prop 5.2 + Thm 1.21 + Lemma 5.8 Kantorovich ⇒ Thm 5.9)
   │                Alg 5.3 MR  (Prop 5.3 + Thm 1.34 ⇒ Thm 5.10) ──> Thm 6.30 (GMRES(m) for PD A)
   │                Alg 5.4 RNSD = SD on normal eqns ──> Ch. 8 CGNR/CGNE
   └─> 5.4 additive/multiplicative ⇐ 4.1.1 block Jacobi/GS

1.8–1.10 (Jordan; Thm 1.10–1.12; Perron–Frobenius; Thm 1.29; M-matrices)
   ├─> Thm 4.1 / Cor 4.2 (ρ(G)<1) ──> Example 4.1 Richardson ──> Cor 8.1 (Uzawa)
   ├─> Thm 4.4 (regular splittings; uses Thm 1.29, Perron–Frobenius)
   ├─> Thm 4.6 Gershgorin ──> Thm 4.7 (irreducible) ──> Cor 4.8 ──> Thm 4.9 (Jacobi/GS converge)
   ├─> Thm 4.10 (SOR ⇔ SPD; unproved)
   └─> Prop 4.12 ──> Def 4.13 ──> Prop 4.14 ──> Prop 4.15 ──> Thm 4.16 (Young) ──> ω_opt (4.47)

6.2 Krylov (Prop 6.1, 6.2 [grade], Prop 6.3 [sections])
   └─> 6.3 Arnoldi (Prop 6.4 basis, Prop 6.5 AV_m = V_{m+1}H̄_m, Prop 6.6 breakdown)
        ├─> 6.4 FOM (Prop 6.7 residual ∥ v_{m+1}) ──> IOM/DIOM (Prop 6.8; LU of H_m)
        │      └─> 6.6 Lanczos (Thm 6.19: H_m tridiagonal for symmetric A) ──> 6.7 CG
        │             (Alg 6.16/6.17 D-Lanczos, Prop 6.20 orthogonal residuals + A-conjugate directions
        │              ⇒ Alg 6.18 CG; 3-term variant 6.19; T_m from CG coefficients 6.7.3)
        │             └─> Lemma 6.28 + Thm 6.25 (Chebyshev) ⇒ Thm 6.29 (CG bound √κ)
        ├─> 6.5 GMRES (Prop 5.3 + Prop 6.5 ⇒ (6.28); Givens: Prop 6.9, (6.47); Prop 6.10 breakdown)
        │      ├─> QGMRES/DQGMRES ((6.50)–(6.58); Thm 6.11 quasi vs true residual)
        │      ├─> 6.5.7 FOM–GMRES (Prop 6.12, 6.13, Cor 6.14, Prop 6.15, Lemma 6.16, (6.74)–(6.75), Prop 6.17)
        │      │      └─> 6.5.8 residual smoothing (Lemma 6.18, QMRS) ──> Ch. 7 QMR ≡ smoothed BCG
        │      ├─> 6.8 CR (Hermitian A), 6.9 Lemma 6.21 ⇒ GCR/ORTHOMIN/ORTHODIR
        │      └─> Lemma 6.31 + Prop 6.32 (κ₂(X)) + Thm 6.27/Lemma 6.26 (complex Chebyshev) ⇒ Cor 6.33
        └─> 6.10 Faber–Manteuffel (Prop 6.22 via h_ij = (v_j, Aᵀv_i); Lemma 6.23 uses Lemma 1.15; Thm 6.24)

Ch. 7: Alg 7.1 ⇒ Prop 7.1 (biorthogonality, AV_m = V_mT_m + …, W_mᵀAV_m = T_m) ⇒ Alg 7.2 ⇒ BCG (Prop 7.2, via LU)
        ⇒ QMR (7.15)–(7.17), Prop 7.3, Thm 7.4 (= Thm 6.11 proof), (7.23)–(7.24), Prop 7.5 (= 6.5.7 argument)
Ch. 8: CGNR/CGNE = CG (Ch. 6) on AᵀA / AAᵀ; Kaczmarz/Cimmino = GS/Jacobi (Ch. 4) on normal equations; Uzawa = Richardson
Ch. 9: PCG = CG in M-inner product (1.11 remark on B-self-adjointness); Alg 9.2 ≡ Alg 9.1;
        left/right GMRES = GMRES on M⁻¹A / AM⁻¹ (Prop 9.1); FGMRES: AZ_m = V_{m+1}H̄_m ⇒ Prop 9.2, 9.3
```

### 11.4 Concepts shared with the neighbouring literature

* **Saad, *Numerical Methods for Large Eigenvalue Problems*:** Krylov subspaces, grade/minimal polynomial
  of a vector, Prop 6.3 (sections `Q_mA|_{K_m}`, which is exactly the Rayleigh–Ritz projected operator),
  Arnoldi (Props 6.4–6.6, Householder/MGS variants, block Arnoldi, Ruhe's variant), symmetric Lanczos
  (Thm 6.19, loss of orthogonality, orthogonal polynomials 6.6.2), two-sided Lanczos (Prop 7.1), Ritz
  values from `H_m`/`T_m` (used in 6.7.3 to estimate eigenvalues from CG coefficients), Chebyshev
  polynomials/ellipses (Lemma 6.26, Thm 6.27 — Chebyshev acceleration), Courant–Fischer min–max (Thm 1.21),
  Schur form, field of values, orthogonal/oblique projectors (1.12), Gershgorin, normal matrices.
* **Fong & Saunders, "CG versus MINRES":** CG = Galerkin (FOM) for SPD, MINRES = minimal residual (GMRES/CR)
  for symmetric `A`; the Lanczos relation `AV_m = V_{m+1}T̄_m`; the Galerkin/MR residual relations
  (Props 6.12–6.15, Cor 6.14: `1/ρ_m^{MR,2} = Σ 1/ρ_i^{G,2}`, `ρ_m^G ≥ ρ_m^{MR}`), (6.74)–(6.75) (MINRES iterate
  as convex combination `s_m²x_{m−1}^{MR} + c_m²x_m^{CG}`), monotone decrease of `‖x* − x‖_A` (CG) and `‖r‖₂`
  (MINRES), residual smoothing (Lemma 6.18), Givens QR of the tridiagonal (6.5.3 with `T̄_m`),
  eigenvalue estimates from `T_m`, three-term recurrences.
* **Choi, MINRES-QLP thesis:** Lanczos tridiagonalization, `AV_m = V_{m+1}T̄_m`, least-squares subproblem
  `min‖βe_1 − T̄_my‖` (= (6.30) with `T̄_m`), Givens rotations `c_m, s_m`, recurrences `γ_{m+1} = −s_mγ_m`,
  progressive solution updates `x_m = x_{m−1} + γ_mp_m` with `P_m = V_mR_m⁻¹` (DQGMRES/QMR style), the
  quasi-residual vs true residual distinction (Thm 6.11), singular/rank-deficient `A` (Prop 6.9(1):
  `r_mm = 0 ⇒ A` singular), minimum-length solutions (CGNE/Craig), the SYMMLQ remark (LQ factorization of
  `T_m`, 6.7.1), CR for symmetric indefinite systems, breakdown ⇔ exact solution (Prop 6.10).
* **Meurant & Strakoš, "The Lanczos and conjugate gradient algorithms in finite precision arithmetic":**
  Lanczos three-term recurrence and `T_m`, the CG ⇔ Lanczos correspondence (`r_j ∥ v_{j+1}`, `T_m` from
  `α_j, β_j` (6.101)–(6.103), `T_m = L_mU_m` LU/Cholesky viewpoint of D-Lanczos), orthogonal polynomials
  and the Stieltjes procedure (6.6.2; Gauss quadrature / moment matching), Krylov subspace and grade,
  `A`-norm error minimization (Prop 5.2, Lemma 6.28), `‖d_k‖_A² = (A⁻¹r_k, r_k)` (Thm 5.9 proof), the
  Chebyshev bound (6.128) and its limitations, loss of orthogonality remarks (6.6.1), Ritz values.
* Common to all four plus Saad: Petrov–Galerkin framework (Ch. 5), orthogonal projectors (1.12),
  Rayleigh quotient bounds (1.9.2), condition number (1.13), Kantorovich inequality (steepest descent),
  Chebyshev min–max (Thm 6.25), polynomial characterizations `r_m = p_m(A)r_0`, `p_m(0) = 1`.

### 11.5 Suggested backbone layering (derived from the above)

1. **Inner-product-space layer (Hilbert, no dimension):** projectors/idempotents, orthogonal projector
   best-approximation (Thm 1.38/Cor 1.39), Petrov–Galerkin projection step with subspaces `K, L`
   (Props 5.1–5.7 with "coercive" replacing "positive definite" and `L = AK` / `L = K`), one-dimensional
   projections (SD/MR/RNSD with Thms 5.9/5.10; Kantorovich for self-adjoint positive operators),
   Arnoldi/Lanczos relations and breakdown ⇒ invariance, Krylov polynomial representation, FOM/GMRES
   optimality and residual identities, Lemma 6.21, FOM–GMRES/Galerkin–MR relations and residual smoothing,
   CG/CR invariants, Chebyshev-based CG bound (spectral theorem for bounded self-adjoint operators),
   PCG as CG in the `M`-inner product, FGMRES.
2. **Finite-dimensional layer:** grade/minimal polynomial, `dim K_m = min(m, μ)`, termination in `≤ n`
   steps, Faber–Manteuffel, diagonalizable GMRES bounds (`κ₂(X)`), Jordan-form convergence factors,
   Thm 4.1 converse.
3. **Matrix-entry layer (ℝ^{n×n} with a basis):** `A = D − E − F`, Jacobi/GS/SOR/SSOR and their
   preconditioners, Gershgorin/diagonal dominance/irreducibility, nonnegative matrices, M-matrices,
   regular splittings, Property A / consistent ordering / Young's theorem, Givens-rotation implementation
   details (Hessenberg QR), block partitions and restriction/prolongation operators.
4. **Analysis layer:** real and complex Chebyshev polynomials (Thm 6.25, Lemma 6.26, Thm 6.27), Joukowski
   map/ellipses, asymptotic estimates (6.112), (6.121).
