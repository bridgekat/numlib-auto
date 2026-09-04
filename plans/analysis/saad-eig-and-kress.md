# Survey: Saad, *Numerical Methods for Large Eigenvalue Problems* (rev. ed.) and Kress, *Numerical Analysis* (GTM 181)

Purpose: theorem inventory of the selected chapters plus a cross-book commonality report for the
Krylov / iterative-methods / functional-analysis core of a Lean 4 + Mathlib formalization backbone.

Conventions.
- Sources are `pdftotext -layout` dumps; formulas were reconstructed from context and from the
  standard editions. Reconstructions I am not fully sure of are tagged `[uncertain]`.
- "Structure" = the ambient mathematical setting a statement genuinely needs (its *natural* home),
  as opposed to the setting in which the book states it. Abbreviations:
  `FDIPS` = finite-dimensional inner product space (over ℂ unless noted), `Mat(ℂ)` = concrete matrices
  with entries (entrywise hypotheses such as diagonal dominance), `Banach`, `Hilbert`, `NS` = normed space.
- Saad works exclusively in ℂⁿ with the Euclidean inner product; Kress works in normed / pre-Hilbert /
  Banach / Hilbert spaces whenever possible and specialises to ℂⁿ or ℝⁿ.
- Saad's eigenvalues are labelled decreasingly in the Hermitian case, `λ₁ ≥ … ≥ λₙ`; Kress likewise.
- OCR quirk in Kress: theorems printed as "Theorem 1.22 / 1.23 / 1.24" in Chapter 7 are 7.22–7.24.

---------------------------------------------------------------------------------------------------

## Part A — Saad, *Numerical Methods for Large Eigenvalue Problems*

### A.0 Background results from Chapter 1 that the later chapters lean on

- **Thm 1.1 / Prop 1.3.** `A ∈ ℂⁿˣⁿ` is diagonalizable iff it has `n` independent eigenvectors iff all
  eigenvalues are semi-simple (algebraic = geometric multiplicity). Structure: finite-dim vector space
  over ℂ. Proof: `AX = XD` with `X` invertible.
- **Thm 1.2 (Jordan form)** and **Thm 1.3 (spectral decomposition).** Every `A` can be written
  `A = Σᵢ (λᵢ Pᵢ + Dᵢ)`, `i = 1..p` over the distinct eigenvalues, where the `Pᵢ` are projectors with
  `Ran Pᵢ = Mᵢ := Null (A − λᵢI)^{ℓᵢ}` (`ℓᵢ` = index), `Pᵢ Pⱼ = δᵢⱼ Pᵢ`, `Σ Pᵢ = I`, and
  `Dᵢ = (A − λᵢI)Pᵢ` nilpotent of index `ℓᵢ`, with `A Pᵢ = Pᵢ A = λᵢ Pᵢ + Dᵢ` and
  `Aᵏ Pᵢ = Pᵢ (λᵢ I + Dᵢ)ᵏ` (1.23). Structure: finite-dim over ℂ (algebraically closed field).
  Proof: define `Pᵢ` through the Jordan basis; verify the three projector identities.
- **Cor 1.1 (Gelfand).** For any matrix norm, `limₖ ‖Aᵏ‖^{1/k} = ρ(A)`; equivalently
  `‖Aᵏ‖ = (ρ(A) + εₖ)ᵏ` with `εₖ → 0`. Structure: finite-dim normed algebra (proof via Jordan form;
  true in any Banach algebra). Proof: exercise P-1.8; from Thm 1.3, `Aᵏ = Σᵢ Pᵢ(λᵢI + Dᵢ)ᵏ`
  and the binomial expansion is bounded by a polynomial in `k` times `ρ(A)ᵏ`.
- **Thm 1.4 (Schur).** There is unitary `Q` with `Qᴴ A Q = R` upper triangular; first `k` Schur vectors
  span an `A`-invariant subspace, `A Q_k = Q_k R_k` ("partial Schur decomposition"). Structure: FDIPS
  over ℂ. Proof: induction on `n`, complete an eigenvector to an orthonormal basis.
- **Thm 1.5 / Cor 1.2 / Thm 1.7 / Thm 1.8.** Normal ⇔ unitarily diagonalizable; normal with real
  spectrum ⇒ Hermitian; Hermitian ⇒ real eigenvalues and an orthonormal eigenbasis.
- **Thm 1.6 / Prop 1.5.** Field of values `{(Ax,x)/(x,x)}` is convex (Hausdorff–Toeplitz), contains
  the convex hull of the spectrum, and equals it for normal `A`.
- **Thm 1.9 (Min–Max, Courant–Fischer).** `A` Hermitian, `λ₁ ≥ … ≥ λₙ`:
  `λₖ = min_{dim S = n−k+1} max_{x∈S∖0} (Ax,x)/(x,x) = max_{dim S = k} min_{x∈S∖0} (Ax,x)/(x,x)`.
  Structure: FDIPS, self-adjoint operator. Proof: a `k`-dim and an `(n−k+1)`-dim subspace intersect
  nontrivially; test on `span{q₁..qₖ}` resp. `span{qₖ..qₙ}`.
- **Thm 1.10 (Courant, recursive).** `λₖ = max{ (Ax,x)/(x,x) : x ≠ 0, x ⟂ q₁,…,q_{k−1} }`, attained at
  `qₖ`. Structure: FDIPS. Proof: expand `x` in the eigenbasis.
- **Thm 1.11 (Perron–Frobenius).** `A ≥ 0` entrywise and irreducible ⇒ `ρ(A)` is a simple eigenvalue
  with a positive eigenvector. Structure: Mat(ℝ), entrywise order. (Stated, not proved.)

### A.3 Chapter 3 — Perturbation theory and error analysis

**§3.1 Projectors.** A projector is `P² = P`; `ℂⁿ = Null P ⊕ Ran P`, and conversely every direct sum
determines a unique projector. `P` is *orthogonal* if `Null P = (Ran P)^⟂`; otherwise *oblique*.

- **Prop 3.1.** A projector is orthogonal iff it is Hermitian (`P = Pᴴ`). Structure: FDIPS.
  Proof: `Null Pᴴ = (Ran P)^⟂`, `Null P = (Ran Pᴴ)^⟂`; a projector is determined by range and null
  space. Consequences: `P = V Vᴴ` for any orthonormal basis `V` of `Ran P`; `‖P‖₂ = 1`.
- **Thm 3.1 (optimality of orthogonal projection).** `P` orthogonal projector onto `S`:
  `min_{y∈S} ‖x − y‖₂ = ‖x − Px‖₂`, equivalently `θ(x,S) = θ(x,Px)` where
  `cos θ(x,y) = |(x,y)|/(‖x‖‖y‖)` and `θ(x,S) = min_{y∈S} θ(x,y)`. Structure: Hilbert space with
  closed `S` (book: FDIPS). Proof: Pythagoras, `x − Px ⟂ S ∋ Px − y`.
- Gap between subspaces: `ω(M₁,M₂) = max{‖(I−P₁)P₂‖₂, ‖(I−P₂)P₁‖₂}`, and (stated) `ω = ‖P₁ − P₂‖₂`.
- **Oblique projectors (3.9)–(3.11).** `P` onto `M` orthogonal to `L` (i.e. along `L^⟂`):
  `Px ∈ M`, `(I−P)x ⟂ L`. With biorthogonal bases `V` of `M`, `W` of `L` (`Wᴴ V = I`): `P = V Wᴴ`.
  `‖P‖₂ ≥ 1`, can be arbitrarily large.
- **Thm 3.2.** For any matrix norm, if two projectors satisfy `‖P − Q‖ < 1` then `rank P = rank Q`.
  Structure: finite-dim normed algebra. Proof: `x ∈ Ran Q`, `Px = 0` ⇒ `(Q−P)x = x` ⇒ `x = 0`, so `P`
  is injective on `Ran Q`; symmetric. Corollary: a continuous family `P(t)` has constant rank; a gap
  `< 1` forces equal dimensions.

**§3.1.3–3.1.4 Resolvent and spectral projector.** `R(A,z) = (A − zI)⁻¹` for `z ∉ σ(A)`;
Taylor expansion `R(z) = Σₖ (z−z₀)ᵏ R(z₀)^{k+1}` for `|z−z₀| < 1/ρ(R(z₀))` (Neumann series);
poles at eigenvalues are not essential (Cramer), so `R` is meromorphic. First resolvent identity
`R(z₁) − R(z₂) = (z₁−z₂)R(z₁)R(z₂)`; second `R(A₁,z) − R(A₂,z) = R(A₁,z)(A₂−A₁)R(A₂,z)`.
Riesz–Dunford integral `Pᵢ = −(1/2πi)∮_{Γᵢ} R(z) dz` over a Jordan curve enclosing only `λᵢ`.

- **Thm 3.3.** The `Pᵢ` so defined satisfy (1) `Pᵢ² = Pᵢ`, (2) `PᵢPⱼ = 0` for `i ≠ j`, (3) `Σᵢ Pᵢ = I`.
  Structure: finite-dim over ℂ, but the proof is the Banach-algebra one (contour integrals of an
  operator-valued analytic function). Proof: (1) two nested contours + first resolvent identity +
  Cauchy's formula; (3) merge contours into a big circle, substitute `t = 1/z`, expand `(I−tA)⁻¹` in
  its Neumann series, residue theorem.
- **Lemma 3.1.** `Ran Pᵢ = Null (A − λᵢI)^{ℓᵢ}`, hence the Dunford projectors coincide with the Jordan
  projectors of Thm 1.3. Proof: for `x` in the generalized eigenspace expand `R(z)x` as a finite
  Laurent series; conversely `(1/2πi)∮ (z−λᵢ)ᵏ R(z) dz = (A−λᵢI)ᵏ Pᵢ` vanishes for large `k`.
  Remark: the projector onto a *group* of eigenvalues is the sum of the individual ones; its rank is
  the sum of the algebraic multiplicities.

**§3.1.5 Linear perturbations `A(t) = A + tH`.**
- **Prop 3.2.** `R(t,z) = (A + tH − zI)⁻¹ = R(z)(I + tR(z)H)⁻¹` is analytic in `t` for
  `|t| < 1/ρ(R(z)H)`. Proof: Neumann series.
- **Thm 3.4.** Let `Γ` be a Jordan curve around some eigenvalues and `a = inf_{z∈Γ} 1/ρ(R(z)H)`.
  Then `a > 0` and `P(t) = −(1/2πi)∮_Γ R(t,z) dz` is analytic for `|t| < a`. Proof: `‖R(z)‖` is
  continuous on the compact `Γ`, so `a ≥ 1/(max_Γ ‖R(z)‖·‖H‖) > 0`.
- **Cor 3.1.** The number of eigenvalues of `A(t)` (with multiplicity) inside `Γ` is constant for
  `|t| < a`. Proof: rank of an analytic projector family is constant (Thm 3.2).
- **Thm 3.5.** `A(t)P(t)` and the averaged eigenvalue `λ̂(t) = (1/m) tr(A(t)P(t))` are analytic on
  `|t| < a`. Hence a simple eigenvalue and its eigenvector `uᵢ(t) = Pᵢ(t)uᵢ` are analytic in `t`;
  branches of a multiple eigenvalue need not be (Example 3.1: `±√t`).
- **Prop 3.3.** Every eigenvalue `λᵢ(t)` of `A(t)` inside `Γ` satisfies `|λᵢ(t) − λᵢ| = O(|t|^{1/ℓᵢ})`,
  `ℓᵢ` the index. Proof: `f(z) = (z−λᵢ)^{ℓᵢ}`, `f(A)Pᵢ = 0`; then
  `|λᵢ(t)−λᵢ|^{ℓᵢ} ≤ ‖f(A(t))P(t) − f(A)Pᵢ‖ = O(t)` by analyticity. (Example 3.2: Jordan block +
  `t·eₙe₁ᵀ` has eigenvalues `t^{1/n}·(roots of unity)`.)

**§3.2 A-posteriori error bounds.** Residual `r = Aũ − λ̃ũ`, `‖ũ‖₂ = 1`.
- **Thm 3.6 (Bauer–Fike).** `A = XDX⁻¹` diagonalizable. Then some eigenvalue `λ` satisfies
  `|λ − λ̃| ≤ Cond₂(X) ‖r‖₂`, `Cond₂(X) = ‖X‖₂‖X⁻¹‖₂`. Structure: finite-dim normed space with
  operator 2-norm (any induced `p`-norm works since `‖(D−λ̃I)⁻¹‖_p = max |λᵢ−λ̃|⁻¹`). Proof:
  `ũ = X(D−λ̃I)⁻¹X⁻¹r`, take norms.
- **Thm 3.7.** Nondiagonalizable version: `A = XJX⁻¹` Jordan; some `λ` with index `ℓ` satisfies
  `|λ−λ̃|^ℓ / (1 + |λ−λ̃| + … + |λ−λ̃|^{ℓ−1}) ≤ Cond₂(X)‖r‖₂`. Proof: `(Jᵢ−λ̃I)⁻¹ = Σⱼ (λᵢ−λ̃)^{−j}(−E)^{j−1}`,
  `‖E‖₂ = 1`, block-diagonal 2-norm = max over blocks.
- **Cor 3.2 (Kahan–Parlett–Jiang 1980).** Same hypotheses: `|λ−λ̃|^ℓ/(1+|λ−λ̃|)^{ℓ−1} ≤ Cond₂(X)‖r‖₂`.
- **Cor 3.3 (Hermitian residual bound).** `A` Hermitian ⇒ some eigenvalue with `|λ − λ̃| ≤ ‖r‖₂`.
  Structure: self-adjoint operator on FDIPS (Bauer–Fike with `Cond₂(X) = 1`).
- **Lemma 3.2.** `A` Hermitian, `‖ũ‖ = 1`, `λ̃ = (Aũ,ũ)` (Rayleigh quotient), `(α,β) ∋ λ̃` an interval
  containing no eigenvalue. Then `(β − λ̃)(λ̃ − α) ≤ ‖r‖₂²`. Proof: `r ⟂ ũ`, so
  `((A−αI)ũ,(A−βI)ũ) = ‖r‖² + (λ̃−α)(λ̃−β)`; the left side is `Σ|ξᵢ|²(λᵢ−α)(λᵢ−β) ≥ 0`.
- **Thm 3.8 (Kato–Temple).** As in Lemma 3.2, if `(a,b)` contains `λ̃` and exactly one eigenvalue `λ`:
  `−‖r‖₂²/(λ̃ − a) ≤ λ − λ̃ ≤ ‖r‖₂²/(b − λ̃)`. Proof: apply the lemma with `(α,β) = (λ,b)` or `(a,λ)`.
- **Cor 3.4.** `λ` the closest eigenvalue to `λ̃`, `δ = min_{λᵢ≠λ}|λᵢ − λ̃|`: `|λ̃ − λ| ≤ ‖r‖₂²/δ`.
- **Thm 3.9 (eigenvector bound).** Same setting, `u` the eigenvector for `λ`:
  `sin θ(ũ,u) ≤ ‖r‖₂/δ`. Proof: `ũ = u cos θ + z sin θ`, `z ⟂ u`; `(A−λ̃I)u ⟂ (A−λ̃I)z`;
  `‖r‖² ≥ sin²θ ‖(A−λ̃I)z‖² ≥ sin²θ δ²` since `A−λ̃I` restricted to `u^⟂` has smallest singular
  value `δ`. Structure: self-adjoint on FDIPS. (Problem P-3.17 gives the sharper
  `sin θ ≤ √(‖r‖² − ε²)/√(δ² − ε²)` with `ε = |λ − λ̃|`.)
- Practical remark: lower-bound `δ` by `|λ̃ − λ̃ⱼ| − ‖rⱼ‖₂` using Cor 3.3 (Examples 3.3, 3.4).

**§3.2.3 Kahan–Parlett–Jiang (backward error).**
- **Prop 3.4.** For unit `u`, scalar `λ`, `r = Au − λu`, `𝓔 = {E : (A−E)u = λu}`: `min_{E∈𝓔} ‖E‖₂ = ‖r‖₂`,
  attained at `E₀ = r uᴴ`. Proof: `Eu = r` forces `‖E‖₂ ≥ ‖r‖₂`; `‖ruᴴ‖₂ = ‖r‖₂`.
- **Thm 3.10 (KPJ, simple version; statement).** Unit `u, w` with `(u,w) ≠ 0`, `r = Au − λu`,
  `s = Aᴴw − λ̄w`, `𝓔 = {E : (A−E)u = λu, (A−E)ᴴw = λ̄w}`: `min_{E∈𝓔} ‖E‖₂ = max{‖r‖₂, ‖s‖₂}`.
  (Proof sketch in the book: explicit two-parameter family `E(τ) = ruᴴ + wsᴴ − ε̄wuᴴ − τxyᴴ`; the
  original KPJ result is a block version, also in Frobenius norm.)

**§3.3 Conditioning.** `Cond(A) = ‖A‖‖A⁻¹‖` recalled for linear systems.
- **Def 3.1 (condition number of a simple eigenvalue).** `Cond(λ) = 1/cos θ(u,w)`, `u,w` right/left
  eigenvectors. Derivation: `λ'(0) = (Eu,w)/(u,w)` for `A + tE`, so `|λ'(0)| ≤ ‖E‖₂/cos θ(u,w)`.
  Normal ⇒ `Cond(λ) = 1`; Example 3.7 shows `(n−1)! ≤ Cond(λ₁) ≤ (n−1)!·n` for a bidiagonal matrix.
- **Reduced resolvent.** `S(λ) = ((A−λI)|_{Null P})⁻¹` with `S(λ)(A−λI)x = (I−P)x` (3.40).
- **Def 3.2.** `Cond(u) = ‖S(λ)(I−P)‖₂` (from `u'(0) = −S(λ)(I−P)Eu` under normalization `Pu(t) = u`).
  Hermitian: `Cond(u) = 1/dist(λ, σ(A)∖{λ})` (3.45); diagonalizable: `S(λᵢ)(I−Pᵢ) = Σ_{j≠i} Pⱼ/(λⱼ−λᵢ)`.
- **Prop 3.5 (invariant subspace, simple eigenvalue).** With `Q` the orthogonal projector onto the
  eigenvector and `S⁺(λ)` the inverse of `(A−λI)` on `Ran(I−Q)`:
  `sin θ(M, M(t)) ≈ |t| ‖S⁺(λ)(I−Q)EQ(t)‖` to second order. Generalized to `r`-dimensional invariant
  subspaces through the Sylvester operator `X ↦ (I−Q)A(I−Q)X − XR` (invertible iff spectra disjoint).

**§3.4 Localization.**
- **Thm 3.11 (Gershgorin).** Every eigenvalue lies in some disc `{|λ − aᵢᵢ| ≤ Σ_{j≠i}|aᵢⱼ|}`;
  also the column version. Structure: Mat(ℂ) entrywise. Proof (norm-based, unlike Kress):
  if `|λ−aᵢᵢ| > Σ_{j≠i}|aᵢⱼ|` for all `i`, then `C = (D−λI)⁻¹H` has `‖C‖_∞ < 1`, so `I + C` and hence
  `A − λI = (D−λI)(I+C)` are invertible.
- **Thm 3.12.** If the union `S` of `m` discs is disjoint from the others, `S` contains exactly `m`
  eigenvalues (with multiplicity). Proof: continuity of eigenvalues along `A(t) = D + tH`, `t ∈ [0,1]`.
- **Prop 3.6.** (Hermitian.) `λ` the eigenvalue closest to `aᵢᵢ`, `μ` the next; `εᵢ` = 2-norm of column
  `i` without its diagonal entry: `|λ − aᵢᵢ| ≤ εᵢ²/|μ − aᵢᵢ|` (and trivially `≤ εᵢ`). Proof:
  Kato–Temple with `ũ = eᵢ`.

**§3.5 Pseudo-eigenvalues.**
- **Def 3.3.** `Λ_ε(A) = {z : ‖R(z)‖₂ > 1/ε} = {z : σ_min(A − zI) < ε}`.
- **Prop 3.7.** Equivalent: (i) `z ∈ Λ_ε(A)`; (ii) `σ_min(A−zI) < ε`; (iii) ∃ unit `v`,
  `‖(A−zI)⁻¹v‖ > 1/ε`; (iv) ∃ unit `w`, `‖(A−zI)w‖ < ε`; (v) ∃ `E`, `‖E‖₂ ≤ ε`, `z ∈ σ(A−E)`.
  Proof: (iv)⇔(v) is Prop 3.4. Structure: FDIPS / operator 2-norm.
- Discussion (3.56)–(3.60): stationary iteration `x_{k+1} = Gx_k + f` has error `Gᵏ(x₀ − x)`,
  converges iff `ρ(G) < 1`; via the Dunford integral
  `Gᵏ = Σⱼ Σ_{l ≤ min(k,ℓⱼ−1)} C(k,l) λⱼ^{k−l} Pⱼ Dⱼˡ` (3.60), explaining transient growth for
  non-normal `G` while `‖Gᵏ‖^{1/k} → ρ(G)`.

### A.4 Chapter 4 — Tools of spectral approximation

**§4.1 Single-vector iterations.**
- **Alg 4.1 (power method):** `vₖ = Avₖ₋₁/αₖ`, `αₖ` = component of largest modulus.
- **Thm 4.1.** Assume a unique eigenvalue `λ₁` of largest modulus, semi-simple. Then either
  `P₁v₀ = 0` or `vₖ` converges to an eigenvector for `λ₁` and `αₖ → λ₁`. Convergence factor
  `|λ₂/λ₁|`. Structure: finite-dim over ℂ (needs spectral projectors + nilpotents, Thm 1.3); the
  argument is the Riesz-projection one and works for a bounded operator with a dominant isolated
  semi-simple eigenvalue. Proof: `Aᵏv₀ = λ₁ᵏ[P₁v₀ + Σ_{i≥2} λ₁^{−k}(λᵢPᵢ + Dᵢ)ᵏPᵢv₀]` and
  `ρ((λᵢPᵢ+Dᵢ)/λ₁) < 1` ⇒ the bracket → `P₁v₀`.
- §4.1.2 shifted power method `A + σI` (same eigenvectors, shifted spectrum; optimal real shift is
  Problem P-4.5). §4.1.3 inverse iteration `vₖ = (A−σI)⁻¹vₖ₋₁/αₖ`: converges to the eigenvector of
  the eigenvalue closest to `σ` with factor `|λ₁−σ|/|λ₂−σ|` (4.5). **Alg 4.3 (RQI)**: `σₖ = (Avₖ₋₁,vₖ₋₁)`;
  stated (citing Parlett): globally convergent for Hermitian `A`, cubic rate; at most quadratic and
  no global result in the non-normal case.

**§4.2 Deflation.**
- **Thm 4.2 (Wielandt).** `A₁ = A − σ u₁ vᴴ` with `vᴴu₁ = 1`: `σ(A₁) = {λ₁ − σ, λ₂, …, λₚ}`. Left
  eigenvectors `w₂..wₚ` and right eigenvector `u₁` preserved; other right eigenvectors become
  `uᵢ − γᵢ(v)u₁` with `γᵢ = σ vᴴuᵢ / (σ − (λ₁ − λᵢ))` (4.8). Proof: `wᵢ ⟂ u₁` for `i ≠ 1`.
- §4.2.2 optimality: `Cond(λ̃₂)` minimized when `γ₂(v) = cos θ(u₁,u₂)`; among `v ∈ span{u₁,u₂}`
  the optimum is (4.13) and `Cond(λ̃₂) = Cond(λ₂) sin θ(u₁,u₂)` (4.14); `v = u₁` nearly optimal.
- **Prop 4.1.** `A₁ = A − σu₁u₁ᴴ` (`‖u₁‖ = 1`) has eigenvalues `λ₁−σ, λ₂, …` and the *same Schur
  vectors* as `A`. Proof: `A₁U = U(R − σe₁e₁ᴴ)`.
- **Prop 4.2.** `Aⱼ = A − Qⱼ Σⱼ Qⱼᴴ` (`Qⱼ` Schur vectors, `Σⱼ` diagonal) has eigenvalues `λᵢ − σᵢ`
  (`i ≤ j`), `λᵢ` (`i > j`), same Schur vectors. Alg 4.4 Schur–Wielandt deflation builds
  `AQⱼ = QⱼRⱼ` incrementally.

**§4.3 General projection methods.** Petrov–Galerkin: seek `ũ ∈ K` (right/trial subspace), `λ̃ ∈ ℂ`,
with `Aũ − λ̃ũ ⟂ L` (left/test subspace). Orthogonal if `L = K`, oblique otherwise.
- §4.3.1: with orthonormal `V` of `K`, `ũ = Vy`, `Bₘ y = λ̃ y`, `Bₘ = Vᴴ A V` (**Alg 4.5, Rayleigh–Ritz**).
  Operator form: `P_K A ũ = λ̃ ũ`, `ũ ∈ K`, i.e. the eigenproblem of the *section*
  `Aₘ := P_K A|_K`, extended by `Aₘ = P_K A P_K` (extra eigenvalue 0 on `K^⟂`).
- **Prop 4.3.** If `K` is `A`-invariant, every Ritz pair is an exact eigenpair. Proof: `P_K Aũ = Aũ`.
  Structure: any vector space with a projector onto `K`.
- **Thm 4.3 (residual of exact pairs w.r.t. the projected problem).** `γ = ‖P_K A (I−P_K)‖₂`,
  `(λ,u)` exact with `‖u‖ = 1`:
  `‖(Aₘ − λI)P_K u‖₂ ≤ γ ‖(I−P_K)u‖₂` (4.23), `‖(Aₘ − λI)u‖₂ ≤ √(λ² + γ²) ‖(I−P_K)u‖₂` (4.24).
  Matrix form: `‖(VᴴAV − λI)y_u‖ ≤ γ tan θ(u,K)`. Structure: Hilbert space, bounded `A`, closed `K`
  (proof uses only `P_K` orthogonal and Pythagoras). Proof: `(Aₘ−λI)P_K u = P_K(A−λI)(I−P_K)u`.
  Note `γ ≤ ‖A‖₂` and `‖(I−P_K)u‖₂ = sin θ(u,K)` = gap between `K` and `span u`.

**§4.3.2 Hermitian case.** `(Aₘx,x) = (Ax,x)` for `x ∈ K`, so
`λ̃₁ = max_{x∈K} (Ax,x)/(x,x)`, `λ̃ₘ = min_{x∈K}` (4.25).
- **Prop 4.4.** `λ̃ᵢ = max_{S⊂K, dim S=i} min_{x∈S} (Ax,x)/(x,x)`. **Cor 4.1.** `λᵢ ≥ λ̃ᵢ`, `i = 1..m`.
  Proof: maximize over fewer subspaces. Structure: self-adjoint on FDIPS (min–max).
- **Thm 4.4.** `λ̃ᵢ = (Aũᵢ,ũᵢ)/(ũᵢ,ũᵢ) = max{(Ax,x)/(x,x) : x ∈ K, x ⟂ ũ₁..ũᵢ₋₁}` (Courant form).
- **Lemma 4.1.** `(λ,u)` exact, `μ = (A P_K u, P_K u)/(P_K u, P_K u)`:
  `|λ − μ| ≤ ‖A − λI‖₂ ‖(I−P_K)u‖₂²/‖P_K u‖₂²`. Proof: `((A−λI)P_Ku,P_Ku) = ((A−λI)(I−P_K)u,(I−P_K)u)`
  by self-adjointness, then Cauchy–Schwarz. Consequence:
  `0 ≤ λ₁ − λ̃₁ ≤ ‖A−λ₁I‖₂ tan² θ(u₁,K)`.
- **Lemma 4.2 / Thm 4.5 (i-th eigenvalue).** `Q̃ᵢ` = orthogonal projector onto `span{ũ₁..ũᵢ₋₁}`:
  `0 ≤ λᵢ − λ̃ᵢ ≤ ‖A − λᵢI‖₂ (‖Q̃ᵢuᵢ‖₂² + ‖(I−P_K)uᵢ‖₂²)/‖(I−Q̃ᵢ)P_K uᵢ‖₂²` (4.31). Proof: test vector
  `xᵢ = (I−Q̃ᵢ)P_Kuᵢ/‖·‖` in Thm 4.4 + Lemma 4.2. ("Semi-a-priori": needs previous Ritz vectors.)
- **Thm 4.6 (Ritz vector angle, Saad).** `γ = ‖P_K A(I−P_K)‖₂`, `(λ,u)` exact, `λ̃` the closest Ritz
  value, `δ = dist(λ, {other Ritz values})`. Then some Ritz vector `ũ` for `λ̃` satisfies
  `sin θ(u,ũ) ≤ √(1 + γ²/δ²) · sin θ(u,K)` (4.32). Structure: self-adjoint on Hilbert space with
  closed `K` (book: FDIPS). Proof: `u = v cos ω + w sin ω` (`v = P_Ku/‖·‖`), project `(A−λI)u = 0`
  onto `K`: `‖P_K(A−λI)v‖ cos ω = ‖P_KA(I−P_K)w‖ sin ω ≤ γ sin ω`; decompose `v = ũ cos ψ + z sin ψ`
  with `z ∈ K ⟂ ũ`, `‖P_K(A−λI)z‖ ≥ δ`; combine with `sin²θ = sin²ω + sin²ψ cos²ω`.
  (Stewart extended it to the non-symmetric case.)
- **Prop 4.5.** `|λ − λ̃| ≤ ‖A − λI‖₂ sin² θ(u,ũ)`. Proof: `λ̃ − λ = ((A−λI)(ũ−ηu),(ũ−ηu))` with
  `η = (u,ũ)`.

**§4.3.3 Oblique projection.** `((A−λ̃I)ũ, v) = 0 ∀v ∈ L`; with biorthogonal `V, W`: `Bₘ = WᴴAV`.
Requires `det(WᴴV) ≠ 0` ⇔ no vector of `L` is orthogonal to `K` ⇔ the oblique projector `Q_K^L`
(onto `K`, orthogonal to `L`) exists. Then the approximate operator is `Q_K^L A|_K`, extended as
`Aₘ = Q_K^L A P_K`. Prop 4.3 extends verbatim.
- **Thm 4.7.** `γ = ‖Q_K^L(A − λI)(I−P_K)‖₂`: `‖(Aₘ−λI)P_Ku‖₂ ≤ γ‖(I−P_K)u‖₂`,
  `‖(Aₘ−λI)u‖₂ ≤ √(|λ|²+γ²)‖(I−P_K)u‖₂`. Proof: as Thm 4.3 using `Q_K^L P_K = P_K`, `Aₘ(I−P_K) = 0`.
  Caveat: `γ` no longer bounded by `‖A‖₂` since `‖Q_K^L‖₂ ≥ 1` is uncontrolled.

**§4.4 Chebyshev polynomials.** `Cₖ(t) = cos(k arccos t)` on `[−1,1]`, `= cosh(k arccosh t)` for
`|t| ≥ 1`; `C₀ = 1`, `C₁ = t`, `C_{k+1} = 2tCₖ − C_{k−1}`;
`Cₖ(t) = ½[(t+√(t²−1))ᵏ + (t+√(t²−1))^{−k}]` (4.48); complex: `Cₖ(z) = ½(wᵏ + w^{−k})`, `z = ½(w + w⁻¹)`.
- **Thm 4.8 (real min–max; stated, proof cited to Cheney).** `[α,β]` nonempty, `γ ∉ [α,β]`
  (say `γ ≥ β`, the other side symmetric). Then
  `min_{p∈P_k, p(γ)=1} max_{t∈[α,β]} |p(t)|` is attained by
  `Ĉₖ(t) = Cₖ(1 + 2(α−t)/(β−α)) / Cₖ(1 + 2(α−γ)/(β−α))`, and the minimum equals
  `1/|Cₖ(1 + 2(α−γ)/(β−α))| = 1/|Cₖ(2(γ−μ)/(β−α))|`, `μ = (α+β)/2`. Structure: real polynomials on
  an interval (approximation theory; alternation argument). *This is the single most reused fact
  in the book* (Thms 6.3, 6.4, 6.8, Chebyshev iteration §7.4).
- **Lemma 4.3 (Zarantonello).** `C(0,ρ)` circle, `γ` outside: `min_{p∈P_k,p(γ)=1} max_{|z|=ρ}|p(z)| = (ρ/|γ|)ᵏ`,
  attained by `(z/γ)ᵏ`; by translation for `C(c,ρ)`: `(ρ/|γ−c|)ᵏ`. (Cited to Rivlin.)
- **Thm 4.9 (complex ellipse, asymptotic optimality).** `E` = image of `C(0,ρ)`, `ρ ≥ 1`, under the
  Joukowski map `J(w) = ½(w+w⁻¹)` (foci `±1`), `γ` outside `E`, `w_γ` the dominant root of `J(w) = γ`:
  `ρᵏ/|w_γ|ᵏ ≤ min_{p∈P_k,p(γ)=1} max_{z∈E} |p(z)| ≤ (ρᵏ+ρ^{−k})/|w_γᵏ + w_γ^{−k}|`.
  The scaled Chebyshev polynomial `Cₖ(z)/Cₖ(γ)` attains the right side; the gap between the two
  sides → 0. Proof: write `p` in the `wʲ + w^{−j}` basis; lower bound via Lemma 4.3 applied to a
  degree-`2k` polynomial in `w`. Remark: Clayton's claimed exact optimality is false (Fischer–Freund).
  For an ellipse with centre `c` and focal distance `d`: near-best polynomial `Cₖ((z−c)/d)`.

### A.5 Chapter 5 — Subspace iteration

- **Alg 5.1 / 5.2.** `Xₖ = orth(A Xₖ₋₁)` (QR), or `orth(A^{iter} X)`; `span Xₖ = span AᵏX₀`.
- **Thm 5.1 (convergence to Schur vectors).** `|λ₁| > |λ₂| > … > |λₘ| > |λ_{m+1}|`; `Q = [q₁..qₘ]` the
  Schur vectors, `Pᵢ` the spectral projector for `λ₁..λᵢ`; assume `rank(Pᵢ[x₁..xᵢ]) = i` for
  `i = 1..m`. Then column `i` of `Xₖ` converges *essentially* (up to unimodular scalars) to `qᵢ`,
  with factor `|λᵢ₊₁/λᵢ|`; moreover the orthogonal projectors onto the first `i` columns converge.
  Structure: finite-dim over ℂ (Schur form + spectral projectors; no diagonalizability needed).
  Proof: `X₀ = QG₁ + WG₂`, `AQ = QR₁`, `AW = WR₂`; `AᵏX₀G₁⁻¹ = [Q + Eₖ]R₁ᵏ` with
  `Eₖ = WR₂ᵏG₂G₁⁻¹R₁^{−k} → 0` since `ρ(R₂)ρ(R₁⁻¹) = |λ_{m+1}/λₘ| < 1`; uniqueness of QR gives
  convergence of the `Q`-factor; induction on columns via `P_{i+1}^{(k)} − P_i^{(k)} → q_{i+1}q_{i+1}ᴴ`.
- **Alg 5.3 (with projection / Rayleigh–Ritz).** `Z = orth(A^{iter}X)`, `B = ZᴴAZ`, Schur vectors `Y`
  of `B`, `X_new = ZY`.
- **Thm 5.2 (angle bound).** `|λₘ| > |λ_{m+1}|`, `P` the spectral projector for `λ₁..λₘ`, `S₀ = span X₀`
  with `{Pxᵢ}` independent. Then for each eigenvector `uᵢ` (`i ≤ m`) there is a unique `sᵢ ∈ S₀` with
  `Psᵢ = uᵢ`, and `‖(I − Pₖ)uᵢ‖₂ ≤ ‖uᵢ − sᵢ‖₂ (|λ_{m+1}/λᵢ| + εₖ)ᵏ`, `εₖ → 0` (`Pₖ` = orthogonal
  projector onto `Sₖ = AᵏS₀`). Proof: `y = λᵢ^{−k}Aᵏsᵢ ∈ Sₖ`, `y − uᵢ = λᵢ^{−k}(A|_W)ᵏw`, `w = (I−P)sᵢ`
  in the complementary invariant subspace `W`; Gelfand (Cor 1.1) gives `‖(A|_W)ᵏ/λᵢᵏ‖ = (|λ_{m+1}/λᵢ| + εₖ)ᵏ`;
  finish with Thm 3.1. Diagonalizable case: `εₖ = 0` (5.10), (5.11); in general
  `‖Bᵏ‖₂ ≤ α k^{ℓ−1} ρ(B)ᵏ` (Problem P-5.6, `ℓ` = largest Jordan block) gives an explicit `εₖ`.
  Hypothesis ⇔ `det(UᴴS₀) ≠ 0` for any basis `U` of `Ran P`.
- §5.3: locking (Alg 5.4), linear shifts (optimal `σ = (λ_{m+1}+λₙ)/2` for real spectra),
  preconditioning by shift-and-invert or Chebyshev polynomial `Tₘ((A−σI)/ρ)` in place of `A^{iter}`.

### A.6 Chapter 6 — Krylov subspace methods

**§6.1 Krylov subspaces.** `Kₘ = Kₘ(A,v) = span{v, Av, …, A^{m−1}v}`.
- **Prop 6.1.** `Kₘ = {p(A)v : deg p ≤ m−1}`. Structure: any vector space over any field.
- **Prop 6.2.** `μ` = degree of the minimal polynomial of `v` (the *grade* of `v`): `K_μ` is
  `A`-invariant and `Kₘ = K_μ` for `m ≥ μ`. Grade `≤ n`.
- **Prop 6.3.** `dim Kₘ = m` iff grade `> m−1`. Proof: linear dependence of `v..A^{m−1}v` ⇔ a
  nonzero annihilating polynomial of degree `≤ m−1`.
- **Prop 6.4.** `Qₘ` any projector onto `Kₘ`, `Aₘ = QₘA|_{Kₘ}` its section. Then `q(A)v = q(Aₘ)v`
  for `deg q ≤ m−1` and `Qₘq(A)v = q(Aₘ)v` for `deg q ≤ m`. Structure: any vector space with a
  projector onto `Kₘ` (orthogonality not needed). Proof: induction on monomials; `A^{i+1}v ∈ Kₘ`
  for `i+1 ≤ m−1` so `Qₘ` acts as identity.
- **Thm 6.1 (optimality of the projected characteristic polynomial).** Orthogonal projection onto
  `Kₘ`; `p̄ₘ` = characteristic polynomial of `Aₘ` (i.e. of `VₘᴴAVₘ`, independent of the basis). Then
  `p̄ₘ` minimizes `‖p(A)v‖₂` over monic polynomials of degree `m`. Structure: FDIPS. Proof:
  Cayley–Hamilton `p̄ₘ(Aₘ) = 0` ⇒ `Pₘ p̄ₘ(A)v = 0` (Prop 6.4) ⇒ `p̄ₘ(A)v ⟂ Kₘ` ⇒ normal equations of
  `min_{deg s ≤ m−1} ‖Aᵐv − s(A)v‖`. (Only known optimality in the non-Hermitian case; equivalence
  with Erdélyi's and Manteuffel's methods.)

**§6.2 Arnoldi.**
- **Alg 6.1 (Arnoldi, classical GS):** `hᵢⱼ = (Avⱼ,vᵢ)`, `wⱼ = Avⱼ − Σᵢ hᵢⱼvᵢ`, `h_{j+1,j} = ‖wⱼ‖₂`,
  `v_{j+1} = wⱼ/h_{j+1,j}`; stop if `h_{j+1,j} = 0`. (Alg 6.2: MGS variant; Householder variant, Walker.)
- **Prop 6.5.** `v₁..vₘ` is an orthonormal basis of `Kₘ(A,v₁)`. Proof: `vⱼ = q_{j−1}(A)v₁` with
  `deg q_{j−1} = j−1`, induction on (6.7). Structure: FDIPS (Gram–Schmidt).
- **Prop 6.6 (Arnoldi relations).** `AVₘ = VₘHₘ + h_{m+1,m} v_{m+1} eₘᵀ` (6.8), `VₘᴴAVₘ = Hₘ` (6.9),
  `Hₘ` upper Hessenberg. Proof: `Avⱼ = Σ_{i≤j+1} hᵢⱼvᵢ` (6.10). Basis-free form (used in §6.6.3):
  `(I−Pₘ)APₘ = h_{m+1,m} v_{m+1}vₘᴴ`, hence `‖PₘA(I−Pₘ)‖₂ = h_{m+1,m}` (P-6.1).
- **Prop 6.7 (breakdown).** Arnoldi breaks down at step `j` (`wⱼ = 0`) iff grade of `v₁` is `j`; then
  `Kⱼ` is invariant and the Ritz pairs are exact (Prop 4.3). "Lucky breakdown."
- **Prop 6.8 (cheap residual).** `Hₘy = θy`, `ũ = Vₘy`: `(A − θI)ũ = h_{m+1,m}(eₘᵀy)v_{m+1}`, so
  `‖(A−θI)ũ‖₂ = h_{m+1,m}|eₘᵀy|`. Proof: multiply (6.8) by `y`.
- Alg 6.3 (restarted Arnoldi), Alg 6.4 (deflated, locked Schur vectors; the lower block equals
  Arnoldi on `(I−Pₖ)A`, P-6.3).

**§6.3 Hermitian Lanczos.**
- **Thm 6.2.** For Hermitian `A` the Arnoldi coefficients are real, `hᵢⱼ = 0` for `i < j−1`,
  `h_{j,j+1} = h_{j+1,j}`: `Hₘ` is real symmetric tridiagonal. Proof: `Hₘ = VₘᴴAVₘ` Hermitian and
  Hessenberg. Structure: self-adjoint on FDIPS.
- **Alg 6.5 (Lanczos):** `αⱼ = (Avⱼ − βⱼv_{j−1}, vⱼ)`, `wⱼ = Avⱼ − αⱼvⱼ − βⱼv_{j−1}`, `β_{j+1} = ‖wⱼ‖`,
  `v_{j+1} = wⱼ/β_{j+1}`. Three-term recurrence; orthogonality only in exact arithmetic.
- §6.3.2: with `⟨p,q⟩_{v₁} = (p(A)v₁, q(A)v₁)` (nondegenerate for `m ≤` grade), `vᵢ = q_{i−1}(A)v₁`
  are orthogonal polynomials; Lanczos = Stieltjes algorithm; by Thm 6.1 the characteristic polynomial
  of `Tₘ` minimizes `‖·‖_{v₁}` among monic polynomials; P-6.8: `v_{m+1} ∝ pₘ(A)v₁` with `pₘ = char. poly of Hₘ`.

**§6.4 Non-Hermitian Lanczos.**
- **Alg 6.6:** two sequences, `αⱼ = (Avⱼ,wⱼ)`, `v̂_{j+1} = Avⱼ − αⱼvⱼ − βⱼv_{j−1}`,
  `ŵ_{j+1} = Aᴴwⱼ − ᾱⱼwⱼ − δ̄ⱼw_{j−1}`, `δ_{j+1}β_{j+1} = (v̂_{j+1},ŵ_{j+1})` (6.28), any such scaling.
- **Prop 6.9.** If no breakdown before step `m`: `(vⱼ,wᵢ) = δᵢⱼ`, `{vᵢ}` basis of `Kₘ(A,v₁)`, `{wᵢ}`
  basis of `Kₘ(Aᴴ,w₁)`, and `AVₘ = VₘTₘ + δ_{m+1}v_{m+1}eₘᵀ`, `AᴴWₘ = WₘTₘᴴ + β̄_{m+1}w_{m+1}eₘᵀ`,
  `WₘᴴAVₘ = Tₘ` (tridiagonal). Structure: FDIPS (biorthogonality). Proof: induction using
  `(Avⱼ,w_{j−1}) = (vⱼ,Aᴴw_{j−1})` and the recurrences. Interpretation: oblique projection onto
  `Kₘ(A,v₁)` orthogonally to `Kₘ(Aᴴ,w₁)`; residual formula (6.32) `‖(A−θI)ũ‖ = |δ_{m+1}eₘᵀy|`;
  left eigenvectors approximated by `Wₘz`. Breakdown `(v̂,ŵ) = 0` ⇔ some vector of `Kₘ(A,v₁)` is
  orthogonal to `Kₘ(Aᴴ,w₁)` ⇔ the oblique projector fails to exist ("serious breakdown");
  look-ahead via the indefinite form `⟨p,q⟩ = (p(A)v₁, q(Aᴴ)w₁)` and `LU` of the Hankel moment matrix.

**§6.5 Block Krylov.** Algs 6.7–6.9 (block Arnoldi, MGS block, Ruhe's variant `r = 1` ⇒ Arnoldi);
`AUₘ = UₘHₘ + V_{m+1}H_{m+1,m}Eₘᴴ` with band-Hessenberg `Hₘ`.

**§6.6 Convergence of Hermitian Lanczos (Kaniel–Paige–Saad).** `λ₁ ≥ … ≥ λₙ`.
- **Lemma 6.1.** `Pᵢ` spectral projector of `λᵢ`, `Pᵢv₁ ≠ 0`, `yᵢ = (I−Pᵢ)v₁/‖(I−Pᵢ)v₁‖`:
  `tan θ(uᵢ,Kₘ) = min_{p∈P_{m−1}, p(λᵢ)=1} ‖p(A)yᵢ‖₂ · tan θ(uᵢ,v₁)`. Proof: `x = q(A)v₁ = q(A)Pᵢv₁ + q(A)(I−Pᵢ)v₁`
  orthogonal decomposition; `tan θ(x,uᵢ) = ‖q(A)yᵢ‖ ‖(I−Pᵢ)v₁‖/(|q(λᵢ)| ‖Pᵢv₁‖)`.
  Structure: self-adjoint on FDIPS (spectral theorem).
- **Thm 6.3 (angle between eigenvector and Krylov subspace).**
  `tan θ(uᵢ,Kₘ) ≤ κᵢ tan θ(v₁,uᵢ) / C_{m−i}(1 + 2γᵢ)`, with `γᵢ = (λᵢ − λᵢ₊₁)/(λᵢ₊₁ − λₙ)`,
  `κ₁ = 1`, `κᵢ = Π_{j<i} (λⱼ − λₙ)/(λⱼ − λᵢ)`. Proof: `‖p(A)y₁‖² ≤ max_{[λₙ,λ₂]}|p|²` and Thm 4.8 with
  `[α,β] = [λₙ,λ₂]`, `γ = λ₁`; for `i > 1` use `p(λ) = Π_{j<i} (λⱼ−λ)/(λⱼ−λᵢ) · q(λ)`, `deg q ≤ m−i`.
- **Thm 6.4 (Ritz value error).** `0 ≤ λᵢ − λᵢ^{(m)} ≤ (λ₁ − λₙ) [κᵢ^{(m)} tan θ(v₁,uᵢ) / C_{m−i}(1+2γᵢ)]²`,
  `κ₁^{(m)} = 1`, `κᵢ^{(m)} = Π_{j<i} (λⱼ^{(m)} − λₙ)/(λⱼ^{(m)} − λᵢ)`. Proof (`i = 1`): Cor 4.1 gives
  `≥ 0`; `λ₁ − λ₁^{(m)} = min_{q∈P_{m−1}} ((λ₁I−A)q(A)v₁, q(A)v₁)/(q(A)v₁,q(A)v₁)`, expand in the
  eigenbasis, bound by `(λ₁−λₙ) max_{[λₙ,λ₂]}|p|² tan²θ(u₁,v₁)` with `p = q/q(λ₁)`, then Thm 4.8.
  `i > 1`: Courant–Fischer on the subspace of `Kₘ` orthogonal to the first `i−1` Ritz vectors
  `= {q(A)v₁ : q(λⱼ^{(m)}) = 0, j < i}`.
- **§6.6.3 (Ritz vector error).** From Thm 4.6 with `γ = ‖PₘA(I−Pₘ)‖₂ = β_{m+1}`:
  `sin θ(uᵢ,ũᵢ) ≤ √(1 + β_{m+1}²/δᵢ²) · κᵢ tan θ(v₁,uᵢ)/C_{m−i}(1+2γᵢ)` (`δᵢ` = distance from `λᵢ` to the
  other Ritz values).

**§6.7 Convergence of Arnoldi (diagonalizable `A`).** `εᵢ^{(m)} = min_{p∈P*_{m−1}} max_{λ∈σ(A)∖{λᵢ}} |p(λ)|`
over polynomials with `p(λᵢ) = 1`.
- **Lemma 6.2.** `v₁ = Σₖ αₖuₖ` (unit eigenvectors), `αᵢ ≠ 0`: `‖(I−Pₘ)uᵢ‖₂ ≤ ξᵢ εᵢ^{(m)}`,
  `ξᵢ = Σ_{k≠i}|αₖ|/|αᵢ|`. Proof: `‖(I−Pₘ)αᵢuᵢ‖ = min_q ‖αᵢuᵢ − q(A)v₁‖`, restrict to `q(λᵢ) = 1`,
  triangle inequality. Structure: finite-dim normed (eigenbasis not orthogonal ⇒ `ξᵢ` absorbs
  conditioning).
- **Thm 6.5 (characterization of best uniform approximation, Haar/Kolmogorov form; cited).** `S` a
  `k`-dim Haar subspace on compact `Ω ⊂ ℂ`: `p ∈ S` is the best uniform approximation of `f` iff there
  are `r` extremal points (`k+1 ≤ r ≤ 2k+1`) and positive `μᵢ` with `Σ μᵢ [f(zᵢ) − p(zᵢ)] φ̄(zᵢ) = 0`
  for all `φ ∈ S` (`r = k+1` when `Ω ⊂ ℝ`).
- **Thm 6.6.** The optimal `1 − p(z) = 1 − (z−λ₁)q(z)` attains its max at `r` eigenvalues
  (`m+1 ≤ r ≤ 2m+1`), and for any `m+1` of them, `1 − p(z) = Σₖ e^{iθₖ}lₖ(z) / Σₖ e^{iθₖ}lₖ(λ₁)`
  (Lagrange polynomials `lₖ` on `λ₂..λ_{m+2}`), so `ε₁^{(m+1)} = 1/|Σₖ e^{iθₖ} lₖ(λ₁)|` (6.50).
  (First-edition statement was wrong in the complex case; corrected here.)
- **Lemma 6.3 / Thm 6.7.** When `r = m+1` (e.g. real spectrum), the phases are determined and
  `ε₁^{(m+1)} = [ Σ_{j=2}^{m+2} Π_{k≠j} |λₖ − λ₁|/|λₖ − λⱼ| ]⁻¹` (6.58). Proof: solve the
  underdetermined system (6.55) in the basis `(z−λ₁)l̂ⱼ(z)`; the solution is `ζₖ = Π_{j≠k}(λ₁−λⱼ)/(λₖ−λⱼ)`.
  Examples: uniform real spectrum on `[0,1]`, `m = n−1` ⇒ `ε₁^{(m)} = 1/(2^m − 1)`; uniform on the unit
  circle ⇒ `ε₁^{(m)} = 1/m` (slow even for normal `A`).
- **Prop 6.10.** If `C(c,ρ)` encloses all eigenvalues except `λ₁`: `ε₁^{(m)} ≤ (ρ/|λ₁ − c|)^{m−1}`
  (optimal by Lemma 4.3).
- **Thm 6.8.** If all eigenvalues except `λ₁` lie in the ellipse with centre `c`, foci `c ± e`, major
  semi-axis `a`: `ε₁^{(m)} ≤ C_{m−1}(a/e)/|C_{m−1}((λ₁−c)/e)|`, asymptotically sharp (Thm 4.9).

### A.7–A.9 Chapters 7, 8, 9 (brief)

**Ch. 7 Filtering and restarting.** Polynomial filtering `v ← p(A)v` (damping coefficients, Def 7.1);
explicitly restarted Arnoldi (Alg 7.1 with deflation); **implicitly restarted Arnoldi** (Alg 7.2 `q`-step
shifted QR on `Hₘ`, Alg 7.3 IRA; the key identity `AVₖ = VₖHₖ + …` after `q` shifted QR steps is
equivalent to restarting with `v₁ ← Π(A−μⱼI)v₁`, i.e. IRA = filtered explicit restart); choice of
filter polynomials (exact shifts, Chebyshev, least squares). **Chebyshev iteration** (Alg 7.4): iterate
`zₖ = pₖ(A)z₀` with scaled/shifted Chebyshev polynomials for an ellipse `E(c,e,a)`; §7.4.1 convergence:
coefficient of `uᵢ` damped like `κᵢᵏ`, `κᵢ = |wᵢ/w₁|` with `wᵢ` the Joukowski preimage — the rate follows
from Thm 4.9; §7.4.2 optimal ellipse (Manteuffel's approach). Chebyshev subspace iteration (Alg 7.5).
**Least-squares Arnoldi** (§7.6): minimize a weighted `L²` norm of `p` over a polygon `H` containing the
unwanted eigenvalues; **Prop 7.1** Gram matrix entries via Chebyshev expansions; **Prop 7.2** recurrence
of expansion coefficients; **Thm 7.1** the least-squares residual polynomial from a Cholesky factor of
the Gram matrix and a Hessenberg matrix `Hₖ = Lᵀ(Tₖ − λ₁I)`; **Thm 7.2** (kernel polynomial) among
`p(λ₁) = 1` the `L²`-minimal one is `Kₖ(λ₁,λ)/Kₖ(λ₁,λ₁)`; **Thm 7.3** generalization to constraints
`Σ μⱼp(λⱼ) = 1`; **Prop 7.3** coefficient formula `η = Mₖ⁻¹t`; Algs 7.6–7.7.

**Ch. 8 Preconditioning.** Shift-and-invert `(A − σI)⁻¹` (eigenvalues `1/(λᵢ−σ)`), complex shifts on
real matrices via `Re`/`Im` parts (**Prop 8.1** `B₋ = B̄₊` [uncertain notation]), Alg 8.1 shift-invert
Arnoldi; polynomial preconditioning (Alg 8.2); **Davidson's method** (Alg 8.3) and **Thm 8.1**: if the
Ritz vector `u₁^{(j)} ∈ K_{j+1}`, the largest Ritz values increase monotonically and converge; with
uniformly bounded, uniformly positive definite preconditioners on `Kⱼ^⟂` the limit is an eigenvalue and
a subsequence of Ritz vectors converges (proof by Courant–Fischer monotonicity + compactness);
Jacobi–Davidson: Olsen's method, connection with Newton's method (**Prop 8.2** solutions of the singular
correction equation, the projected system `(I−zzᴴ)(A−θI)(I−zzᴴ)v = −r`); CMS–AMLS: spectral Schur
complements, **Lemma 8.1** (Rayleigh–Ritz invariance under change of basis), **Prop 8.3** (nonlinear
eigenproblem `S(λ)y = λy` ⇔ eigenpair of the original problem).

**Ch. 9 Non-standard problems.** Generalized `Ax = λBx`: Defs 9.1–9.2 (singular/regular pairs,
equivalence), **Prop 9.1** (`(Auᵢ,wⱼ) = (Buᵢ,wⱼ) = 0` for distinct eigenvalues), **Thm 9.1** (Möbius
transformation of pairs), **Cor 9.1** (simultaneous diagonalization when `n` distinct eigenvalues),
**Thm 9.2** (Weierstrass–Kronecker form `(diag(J,I), diag(I,N))`), **Thm 9.3** (generalized Schur:
`Q₁ᴴAQ₂`, `Q₁ᴴBQ₂` both triangular); reduction to standard form, deflation, shift-and-invert
`(A−σB)⁻¹B`, projection methods, Hermitian definite case with `B`-inner product (Algs 9.1–9.3 `B`-Lanczos
and spectral-transformation Lanczos); quadratic eigenproblems via linearization.

---------------------------------------------------------------------------------------------------

## Part B — Kress, *Numerical Analysis*

### B.2 Chapter 2 — Linear systems (brief)

Thm 2.7 operation count of Gaussian elimination (`n³/3 + O(n²)` multiplications); Def 2.8 / **Thm 2.9**
Gaussian elimination without pivoting yields an `LR` decomposition of a nonsingular `A` (when it runs);
Def 2.10 QR; Def 2.11 Householder matrix `H = I − 2vv*`, Remark 2.12 (unitary, self-adjoint);
**Thm 2.13** every `n×n` matrix has a QR decomposition, via `n−1` Householder reflections (cost
`2n³/3`); Example 2.4 least squares via normal equations. Structure: Mat(ℂ).

### B.3 Chapter 3 — Basic functional analysis

- **Def 3.1–3.4, Thm 3.5.** Norm axioms; convergence; uniqueness of limits. Structure: NS.
- **Thm 3.7.** Two norms are equivalent (same convergent sequences) iff `c‖x‖_a ≤ ‖x‖_b ≤ C‖x‖_a`.
  Proof: otherwise pick `‖xₙ‖_a = 1`, `‖xₙ‖_b ≥ n²`, then `xₙ/n`.
- **Thm 3.8.** On a finite-dimensional space all norms are equivalent. Proof: compare with the
  coefficient max-norm; Bolzano–Weierstrass.
- **Thm 3.11.** Bounded sequences in finite-dimensional NS have convergent subsequences.
- **Def 3.12, Thm 3.14 (Cauchy–Schwarz), Thm 3.15** (`‖x‖ = (x,x)^{1/2}` is a norm). Structure: pre-Hilbert.
- **Thm 3.17.** Orthonormal systems are linearly independent.
- **Thm 3.18 (Gram–Schmidt).** Independent `u₀,u₁,…` in a pre-Hilbert space ⇒ unique orthogonal
  `qₙ = uₙ + rₙ`, `rₙ ∈ span{u₀..u_{n−1}}`, `span{u₀..uₙ} = span{q₀..qₙ}`. Proof: induction. (This is
  the engine behind Arnoldi, Prop 6.5 of Saad, and Kress Thm 9.15 orthogonal polynomials.)
- **Defs 3.19–3.22, Thms 3.21, 3.23, 3.24, Remark 3.25.** Continuity of linear maps at one point ⇒
  everywhere; bounded ⇔ `‖A‖ = sup_{‖x‖=1}‖Ax‖ < ∞`; bounded ⇔ continuous; `‖BA‖ ≤ ‖B‖‖A‖`. Structure: NS.
- **Thm 3.26 (matrix norms).** Every matrix is bounded in every norm; `‖A‖₁ = maxₖ Σⱼ|aⱼₖ|`,
  `‖A‖_∞ = maxⱼ Σₖ|aⱼₖ|`, `‖A‖₂ ≤ (Σ|aⱼₖ|²)^{1/2}`. Structure: Mat(ℂ). Proof: attain with unit vectors /
  sign vectors; Cauchy–Schwarz.
- **Thm 3.27 (Schur).** Unitary `Q` with `Q*AQ` upper triangular. Proof: induction, Gram–Schmidt.
- **Lemma 3.28.** `(Ax,y) = (x,A*y)`. **Thm 3.29.** Hermitian ⇒ real eigenvalues, orthonormal
  eigenbasis (from Schur). Positive (semi)definite ⇒ eigenvalues `> 0` (`≥ 0`).
- **Def 3.30.** `ρ(A) = max{|λ|}`. **Thm 3.31.** `‖A‖₂ = √ρ(A*A)`; Hermitian ⇒ `‖A‖₂ = ρ(A)`. Proof:
  orthonormal eigenbasis of `A*A`.
- **Thm 3.32.** For every norm on ℂⁿ, `ρ(A) ≤ ‖A‖`; conversely for each `A` and `ε > 0` there is a norm
  with `‖A‖ ≤ ρ(A) + ε`. Structure: finite-dim (Schur form). Proof: `‖x‖ := ‖V⁻¹x‖_∞` with `V = QD`,
  `D = diag(1,δ,…,δ^{n−1})`, `δ` small so the scaled triangular `D⁻¹BD` has off-diagonal row sums `≤ ε`.
- **Defs 3.33, 3.35, Thm 3.34, Examples 3.36–3.38, Thm 3.39, Remark 3.40.** Cauchy sequences;
  Banach/Hilbert spaces; `C[a,b]` with max-norm complete, with `L¹`/`L²` norms not; finite-dim NS are
  Banach; complete ⇒ closed, closed subsets of complete sets are complete.
- **Def 3.41, Remark 3.42, Def 3.43, Thm 3.44.** Contraction (`‖Ax − Ay‖ ≤ q‖x−y‖`, `q < 1`) is
  continuous; at most one fixed point.
- **Thm 3.45 (Banach).** `U` complete subset of a NS, `A : U → U` contraction ⇒ unique fixed point.
  Proof: `xₙ₊₁ = Axₙ`, `‖xₘ − xₙ‖ ≤ qⁿ/(1−q) ‖x₁ − x₀‖` (3.12), Cauchy, continuity of `A`.
- **Thm 3.46 (error estimates).** Same setting: `xₙ → x` for every `x₀ ∈ U`, with
  *a priori* `‖xₙ − x‖ ≤ qⁿ/(1−q) ‖x₁ − x₀‖` and *a posteriori* `‖xₙ − x‖ ≤ q/(1−q) ‖xₙ − xₙ₋₁‖`.
  Proof: let `m → ∞` in (3.12); apply the a priori bound from `xₙ₋₁`. Iteration count
  `n ≥ ln ε'/ln q`. Structure: complete metric space (nothing linear is used).
- **Example 3.47.** `f(x) = x + 1/(1+x)` on `[0,∞)`: `|f(x)−f(y)| < |x−y|` but no fixed point
  (weak contraction insufficient; Problem 3.18: sufficient on complete sequentially compact sets;
  Problem 3.17: `Aᵐ` a contraction suffices).
- **Thm 3.48 (Neumann series / linear successive approximations).** `X` Banach, `B ∈ L(X)`,
  `‖B‖ < 1`. Then `I − B` is bijective; `xₙ₊₁ = Bxₙ + z` converges to the solution of `x − Bx = z` for
  every `x₀`, with a priori `‖xₙ − x‖ ≤ ‖B‖ⁿ/(1−‖B‖) ‖x₁ − x₀‖`, a posteriori
  `‖xₙ − x‖ ≤ ‖B‖/(1−‖B‖) ‖xₙ − xₙ₋₁‖`, and `‖(I−B)⁻¹‖ ≤ 1/(1−‖B‖)`. Proof: `x ↦ Bx + z` is a
  contraction with `q = ‖B‖`; with `x₀ = z`, `xₙ = Σ_{k≤n} Bᵏz`. Structure: Banach space
  (Problem 3.16: `Σ Bᵏ = (I−B)⁻¹` in `L(X,X)`).
- **Def 3.49, Thm 3.50.** Best approximation in a finite-dimensional subspace `U` of a NS exists.
  Proof: minimizing sequence bounded, Thm 3.11.
- **Thm 3.51.** `U` a linear subspace of a pre-Hilbert space: `v ∈ U` is a best approximation of `w`
  iff `(w − v, u) = 0 ∀u ∈ U`; at most one exists. Proof: `‖w−u‖² = ‖w−v‖² + 2Re(w−v,v−u) + ‖v−u‖²`.
- **Thm 3.52 (projection theorem).** `U` complete subspace of a pre-Hilbert space ⇒ unique best
  approximation for every `w`; the map `P : X → U` is linear, bounded, `P² = P`, `‖P‖ = 1` (orthogonal
  projection). Proof: minimizing sequence is Cauchy via the parallelogram law.
- **Cor 3.53 (normal equations).** `U = span{u₁..uₙ}`: `v = Σ aₖuₖ` is the best approximation iff
  `Σₖ aₖ(uₖ,uⱼ) = (w,uⱼ)`, `j = 1..n`. **Cor 3.54.** Orthonormal basis ⇒ `Pw = Σ (w,uₖ)uₖ`.
  Structure: pre-Hilbert / Hilbert space; finite-dim `U` automatically complete.

### B.4 Chapter 4 — Iterative methods for linear systems

- **Thm 4.1.** `B ∈ ℂⁿˣⁿ`: `x_{ν+1} = Bx_ν + z` converges for every `z` and every `x₀` iff `ρ(B) < 1`.
  Structure: finite-dim (uses Thm 3.32 + Thm 3.8); remark: true for bounded operators on Banach
  spaces with a deeper proof. Proof: (⇐) choose a norm with `‖B‖ < 1`, Thm 3.48; (⇒) an eigenvector `x`
  with `|λ| ≥ 1`, `z = x₀ = x` gives `x_ν = (Σ_{k≤ν} λᵏ)x`, divergent. (Problem 4.3: `Aᵛ → 0` iff `ρ(A) < 1`.)
- Setting: `A = D + A_L + A_R` (diagonal, strict lower, strict upper), `aⱼⱼ ≠ 0`.
  Jacobi: `x_{ν+1} = −D⁻¹(A_L + A_R)x_ν + D⁻¹y`. Gauss–Seidel: `(D + A_L)x_{ν+1} = −A_R x_ν + y`.
- **Thm 4.2 (Jacobi).** If `q_∞ = maxⱼ Σ_{k≠j}|aⱼₖ/aⱼⱼ| < 1` (strict row diagonal dominance (4.4)), or
  `q₁ = maxₖ Σ_{j≠k}|aⱼₖ/aⱼⱼ| < 1`, or `q₂ = (Σ_{j≠k}|aⱼₖ/aⱼⱼ|²)^{1/2} < 1`, then Jacobi converges for all
  `y, x₀` to the unique solution, with a priori `‖x_ν − x‖_μ ≤ q_μ^ν/(1−q_μ) ‖x₁ − x₀‖_μ` and a posteriori
  `‖x_ν − x‖_μ ≤ q_μ/(1−q_μ) ‖x_ν − x_{ν−1}‖_μ` (`μ = 1,2,∞`). Structure: Mat(ℂ) entrywise. Proof: the
  Jacobi matrix has `‖·‖_∞ = q_∞`, `‖·‖₁ = q₁`, `‖·‖₂ ≤ q₂` (Thm 3.26) + Thm 3.48. Strict column
  dominance (4.5) also suffices (Problem 4.4).
- **Thm 4.3 (Gauss–Seidel, Sassenfeld).** `p₁ = Σ_{k≥2}|a₁ₖ/a₁₁|`,
  `pⱼ = Σ_{k<j}|aⱼₖ/aⱼⱼ| pₖ + Σ_{k>j}|aⱼₖ/aⱼⱼ|`; if `p = max pⱼ < 1`, Gauss–Seidel converges with a priori
  `‖x_ν − x‖_∞ ≤ pᵛ/(1−p)‖x₁−x₀‖_∞` and a posteriori `≤ p/(1−p)‖x_ν − x_{ν−1}‖_∞`. Proof: for
  `x = −(D+A_L)⁻¹A_R z`, `‖z‖_∞ = 1`, induction gives `|xⱼ| ≤ pⱼ`, so `‖(D+A_L)⁻¹A_R‖_∞ ≤ p`; Thm 3.48.
- **Cor 4.4.** Strict row diagonal dominance ⇒ Gauss–Seidel converges (`pⱼ ≤ q_∞`).
- **Example 4.5.** `tridiag(−1,2,−1)`: `q_∞ = 1` but `pⱼ = 1 − 2^{−j}`, `p = 1 − 2^{−(n−1)} < 1`.
- **Def 4.6.** Reducible: a partition `N ∪ M` of indices with `aⱼₖ = 0` for `j ∈ N, k ∈ M`
  (⇔ permutation to block upper triangular, Problem 4.5).
- **Thm 4.7.** `A` irreducible and weakly row diagonally dominant (`Σ_{k≠j}|aⱼₖ| ≤ |aⱼⱼ|` with strict
  inequality in at least one row) ⇒ Jacobi converges for all `y, x₀`. Proof: `‖B‖_∞ ≤ 1` ⇒ `ρ(B) ≤ 1`;
  if `|λ| = 1` with `‖x‖_∞ = 1`, the index set `N = {j : |xⱼ| = 1}` is proper (by the strict row) and
  irreducibility produces `j₀ ∈ N, k₀ ∉ N` with `a_{j₀k₀} ≠ 0`, contradicting equality in (4.7); Thm 4.1.
- **Def 4.8 (Jacobi relaxation, JOR).** `x_{ν+1} = x_ν + ωD⁻¹(y − Ax_ν)`, iteration matrix `(1−ω)I + ωB`.
- **Thm 4.9.** If the Jacobi matrix `B` has real eigenvalues and `ρ(B) < 1`, then
  `ω_opt = 2/(2 − λ_max − λ_min)` minimizes `ρ((1−ω)I + ωB)`, with value `(λ_max − λ_min)/(2 − λ_max − λ_min)`;
  faster than plain Jacobi iff `λ_min ≠ −λ_max`. Proof: eigenvalues `1 − ω + ωλ`; balance the extremes.
- **Def 4.10 (SOR).** `(D + ωA_L)x_{ν+1} = ωy + [(1−ω)D − ωA_R]x_ν`, `B(ω) = (D+ωA_L)⁻¹[(1−ω)D − ωA_R]`.
- **Thm 4.11 (Kahan).** SOR convergent ⇒ `0 < ω < 2`. Proof: `Π μⱼ = det B(ω) = (1−ω)ⁿ` ⇒
  `ρ(B(ω)) ≥ |1−ω|`.
- **Thm 4.12 (Ostrowski; Ostrowski–Reich).** `A` Hermitian positive definite ⇒ SOR converges for all
  `x₀, y` and all `0 < ω < 2`. Structure: FDIPS + the splitting `D, A_L, A_R = A_L*` (Hermitian). Proof:
  for an eigenpair `(μ,x)` of `B(ω)`, `μ = ((2−ω)d − ωa + iωs)/((2−ω)d + ωa + iωs)` with `a = (Ax,x) > 0`,
  `d = (Dx,x) > 0`, `s = i(A_Rx − A_Lx, x) ∈ ℝ`; hence `|μ| < 1`; Thm 4.1.
  (Problem 4.17: Jacobi may fail for positive definite `A`.)
- **Def 4.13 / Remark 4.14.** Consistently ordered: eigenvalues of `C(α) = −αD⁻¹A_L − α⁻¹D⁻¹A_R`
  independent of `α`; tridiagonal with nonzero diagonal ⇒ consistently ordered (similarity by
  `S(α) = diag(1,α,…,α^{n−1})`).
- **Thm 4.15 (Young).** `A` consistently ordered, Jacobi matrix with real eigenvalues and
  `λ := ρ(B_J) < 1` ⇒ SOR converges for `0 < ω < 2`; `ω_opt = 2/(1 + √(1−λ²)) ≥ 1` and
  `ρ(B(ω_opt)) = ω_opt − 1 = (1 − √(1−λ²))/(1 + √(1−λ²))`. Proof: `μ ≠ 0` is an eigenvalue of `B(ω)` iff
  `(μ + ω − 1)/(√μ ω)` is an eigenvalue of `B_J` (4.8); solve the quadratic; `|μ(ω)|` is monotone in
  `|λ|`, decreasing on `(0,ω₀)`, `= ω − 1` on `(ω₀,2)`.
- **Cor 4.16.** Under Thm 4.15, `ρ(B_GS) = ρ(B_J)²`: Gauss–Seidel is twice as fast as Jacobi.
- **Example 4.17.** For `tridiag(−1,2,−1)`: `λⱼ(B_J) = cos(πj/(n+1))`, `ω_opt = 2/(1 + sin(π/(n+1)))`,
  `ρ(B(ω_opt)) ≈ 1 − 2π/(n+1)`, so `N(SOR)/N(Jacobi) ≈ π/(4(n+1))`.
- **§4.3 Defect correction.** `x_{ν+1} = x_ν + A_approx⁻¹(y − Ax_ν)` (4.15) converges iff
  `ρ(I − A_approx⁻¹A) < 1` (Thm 4.1) — this is the general splitting `A = M − N` iteration with
  `M = A_approx`. Two-grid method for the model problem: eigenpairs (4.18)–(4.19) of `A^{(h)}`, damped
  Jacobi (`ω = ½`) is a smoother (high-frequency error factors `cos²(πjh/2) ≤ ½`), restriction
  `R^{(h)}` (weighted, (4.21)), prolongation `P^{(h)} = 2R^{(h)ᵀ}` (linear interpolation, (4.22)),
  iteration matrix `T_N = [I − P^{(h)}(A^{(2h)})⁻¹R^{(h)}A^{(h)}](I − ½(D^{(h)})⁻¹A^{(h)})^N` (4.23).
- **Thm 4.18.** For `N = 1`, `ρ(T) = ½`: the two-grid iteration converges independently of `h`. Proof:
  `T` acts on the pairs `(vⱼ^{(h)}, v_{n+1−j}^{(h)})` by a `2×2` block with eigenvalues `0, ½·(…)`
  [uncertain: the book computes the block eigenvalues as `0` and `½`], plus `Tv_{(n+1)/2} = ½v_{(n+1)/2}`.
  (Problem 4.20: `ρ(T_N) ≤ max_{0≤t≤1}[t(1−t)^N + (1−t)ᴺt]`.) Multigrid = recursion.

### B.5 Chapter 5 — Ill-conditioned linear systems

- **Example 5.1.** Hilbert matrix from least-squares polynomial approximation; instability.
- **Def 5.2.** `cond(A) = ‖A‖‖A⁻¹‖ ≥ 1` for a bounded bijection between normed spaces. Structure: NS.
- **Thm 5.3 (perturbation).** `X, Y` Banach, `A` bounded with bounded inverse, `A^δ` bounded with
  `‖A⁻¹‖‖A^δ − A‖ < 1`, `Ax = y`, `A^δx^δ = y^δ`. Then
  `‖x^δ − x‖/‖x‖ ≤ cond(A)/(1 − cond(A)‖A^δ−A‖/‖A‖) · (‖y^δ − y‖/‖y‖ + ‖A^δ − A‖/‖A‖)`.
  Proof: `A^δ = A[I + A⁻¹(A^δ − A)]`, Thm 3.48 gives `‖(A^δ)⁻¹‖ ≤ ‖A⁻¹‖/(1 − ‖A⁻¹‖‖A^δ−A‖)`;
  `A^δ(x^δ − x) = y^δ − y − (A^δ − A)x`; `‖A‖‖x‖ ≥ ‖y‖`. Structure: Banach spaces (already the natural
  generality). Hermitian: `cond₂(A) = |λ_max|/|λ_min|` (Thm 3.31); nonsingular: `σ_max/σ_min`.
- **Thm 5.4 (SVD).** `A ∈ ℂ^{m×n}` of rank `r`: singular values `μ₁ ≥ … ≥ μ_r > 0 = μ_{r+1} = …` and
  orthonormal `u₁..uₙ`, `v₁..vₘ` with `Auⱼ = μⱼvⱼ`, `A*vⱼ = μⱼuⱼ` (`j ≤ r`), `Auⱼ = 0`, `A*vⱼ = 0` beyond;
  `Ax = Σ_{j≤r} μⱼ(x,uⱼ)vⱼ`, i.e. `A = VDU*`. Proof: eigenbasis of `A*A`, `vⱼ = Auⱼ/μⱼ`, extend by
  Gram–Schmidt; `N(A) = N(A*A)`. Structure: FDIPS (linear maps between two of them).
- **Thm 5.5.** `Ax = y` solvable iff `y ⟂ N(A*)`; then `x₀ = Σ_{j≤r} μⱼ⁻¹(y,vⱼ)uⱼ` solves it and is the
  unique minimum-norm solution; in general it is the unique minimum-norm least-squares solution
  (pseudo-inverse `A†`, (5.13)). Proof: expand in the singular bases; Pythagoras.
- **Thm 5.6 (spectral cut-off + discrepancy principle).** `y ∈ A(ℂⁿ)`, `‖y^δ − y‖₂ ≤ δ ≤ ‖y^δ‖₂`: there is a
  smallest `p = p(δ)` with `‖Ax_p − y^δ‖₂ ≤ δ` (`x_p = Σ_{j≤p} μⱼ⁻¹(y^δ,vⱼ)uⱼ`), and `x_p → A†y` as `δ → 0`.
  Proof: `F(p) = Σ_{j>p}|(y^δ,vⱼ)|² − δ²` is nonincreasing, `F(0) ≥ 0`, `F(r) ≤ 0`; `A†Av = v` on the range.
- **Thm 5.7 (Tikhonov).** `α > 0`: `αx_α + A*Ax_α = A*y` is uniquely solvable, `x_α = Σ_{j≤r} μⱼ/(α+μⱼ²) (y,vⱼ)uⱼ`.
  Proof: `αI + A*A` positive definite; singular system `(α + μⱼ², uⱼ, uⱼ)`. **Cor 5.8.**
  `(αI + A*A)⁻¹A*y → A†y` as `α → 0`.
- **Thm 5.9 (penalized least squares).** `x_α` is the unique minimizer of `‖Ax − y‖₂² + α‖x‖₂²`.
  Proof: the identity `‖Ax−y‖² + α‖x‖² = ‖Ax_α−y‖² + α‖x_α‖² + 2Re(x−x_α, αx_α + A*Ax_α − A*y) + …`,
  same pattern as Thm 3.51. Structure: FDIPS; Problem 5.18 generalizes to any finite-dim pre-Hilbert
  spaces with adjoints. `cond₂(αI + A*A) = (α + μ₁²)/(α + μₙ²) ≤ 2μ₁²/α` (5.22); error splitting
  `E_total ≤ E_data + E_approx`, `E_data ≤ (μ_r/(α + μ_r²))δ` [uncertain constant, Problem 5.16 gives `1/(2√α)`].
- **Thm 5.10 (discrepancy principle for Tikhonov).** `y ∈ A(ℂⁿ)`, `‖y^δ − y‖₂ ≤ δ < ‖y^δ‖₂`: unique
  `α = α(δ)` with `‖Ax_α − y^δ‖₂ = δ`, and `x_{α(δ)} → A†y` as `δ → 0`. Proof: `F(α) = Σ α²/(α+μⱼ²)² |(y^δ,vⱼ)|² − δ²`
  strictly increasing from `−δ²` to `‖y^δ‖² − δ² > 0`; then `α → 0` via `α‖Ax_α‖ ≤ ‖AA*‖δ`.

### B.6 Chapter 6 — Iterative methods for nonlinear systems

- **Thm 6.1.** `D ⊂ ℝ` closed interval, `f : D → D` `C¹` with `q = sup|f'| < 1` ⇒ unique fixed point;
  `x_{ν+1} = f(x_ν)` converges for every `x₀ ∈ D` with the a priori / a posteriori estimates of Thm 3.46.
  Proof: mean value theorem ⇒ contraction; Thm 3.46.
- **Thm 6.2 (local convergence, 1-D).** Fixed point `x` with `|f'(x)| < 1` ⇒ convergence for `x₀` in
  a neighbourhood. Proof: `f` maps `[x−δ,x+δ]` into itself and contracts there.
  Examples 6.3–6.6 (`2x − ax²` for `1/a`, Heron for `√a`, `cos x`, `e^{−x}` vs `−ln x`).
- **Thm 6.7 (mean value inequality).** `D ⊂ ℝⁿ` open convex, `f ∈ C¹(D,ℝⁿ)`:
  `‖f(x) − f(y)‖ ≤ max_{0≤λ≤1}‖f'(λx + (1−λ)y)‖ ‖x − y‖` for every norm. Proof:
  `f(x) − f(y) = ∫₀¹ f'(λx+(1−λ)y)(x−y)dλ` and `‖∫g‖ ≤ ∫‖g‖` (6.1) (Riemann sums). Structure: works
  verbatim for Fréchet-differentiable maps between Banach spaces.
- **Thm 6.8.** `D ⊂ ℝⁿ` closed convex, `f : D → D` continuous, `C¹` inside with `sup_D ‖f'(x)‖ < 1` in
  some norm ⇒ unique fixed point, global convergence of successive approximations with the a priori
  and a posteriori estimates (`q = sup‖f'‖`). Sufficient entrywise conditions via Thm 3.26.
- **Thm 6.9.** Local version in ℝⁿ: `‖f'(x)‖ < 1` at a fixed point ⇒ local convergence.
- **Def 6.11 (Newton).** `x_{ν+1} = x_ν − [f'(x_ν)]⁻¹f(x_ν)` (solve a linear system each step).
- **Thm 6.14 (Newton–Kantorovich type, semi-local).** `D ⊂ ℝⁿ` open convex, `f ∈ C¹`, a norm, `x₀ ∈ D`
  with (a) `‖f'(x) − f'(y)‖ ≤ γ‖x − y‖` on `D`; (b) `f'(x)` invertible on `D` with `‖[f'(x)]⁻¹‖ ≤ β`;
  (c) `α := ‖[f'(x₀)]⁻¹f(x₀)‖` and `q := αβγ < ½`; (d) `B[x₀, r] ⊂ D` with `r = 2α`. Then `f` has a
  unique zero `x*` in `B[x₀,r]`, Newton's iteration is well defined, converges to `x*`, and
  `‖x_ν − x*‖ ≤ α q^{2^ν − 1}/(1 − q^{2^ν})` [uncertain exact form; from the proof
  `‖x_{ν+1} − x_ν‖ ≤ α q^{2^ν−1}` summed geometrically]. Proof: (6.5) `‖f(y)−f(x)−f'(x)(y−x)‖ ≤ (γ/2)‖y−x‖²`
  from Thm 6.7's integral form; induction `‖x_{ν+1} − x_ν‖ ≤ β(γ/2)‖x_ν − x_{ν−1}‖² ≤ αq^{2^ν−1}`;
  Cauchy; `f(x_ν) → 0`; uniqueness via `g(x) = x − [f'(x₀)]⁻¹f(x)` being a contraction (`2q < 1`) on
  the ball. Structure: Banach space with Fréchet derivative (proof is dimension-free).
- **Cor 6.15.** `f ∈ C²`, `x*` a zero with `f'(x*)` invertible ⇒ Newton converges locally. Proof:
  Lipschitz `f'` near `x*`; invertibility of `f'(x)` nearby by Thm 3.48 (Neumann series); choose `x₀`
  with `‖f(x₀)‖` small so (c),(d) hold. **Cor 6.16.** 1-D, simple zero ⇒ local convergence.
- **Def 6.19.** Order-`p` convergence: `‖x_{ν+1} − x‖ ≤ C‖x_ν − x‖^p`. (Banach iteration is linear.)
- **Thm 6.20.** Under Thm 6.14 Newton converges quadratically: `‖x* − x_{ν+1}‖ ≤ (βγ/2)‖x* − x_ν‖²`.
  Proof: `x* − x_{ν+1} = [f'(x_ν)]⁻¹[f(x*) − f(x_ν) − f'(x_ν)(x* − x_ν)]` and (6.5).
- **Thm 6.21.** Simplified (frozen) Newton `x_{ν+1} = x_ν − [f'(x₀)]⁻¹f(x_ν)` converges linearly to the
  unique zero in `B[x₀,r]`. Proof: `g` above is a contraction mapping the ball into itself
  (`‖g(x) − x₀‖ ≤ (2q+1)α < 2α`); Thm 3.46. Secant method (6.9), Broyden (mentioned).
- **§6.3 Zeros of polynomials.** Horner scheme; **Thm 6.22** complete Horner scheme yields
  `p^{(k)}(z)/k!`; deflation strategy; multiple zero of order `m` ⇒ Newton is a fixed-point iteration
  with `g'(z) = 1 − 1/m` (linear convergence, Problem 6.14 restores quadratic); Bairstow; conditioning
  `z(ε) ≈ z₀ − ε q(z₀)/p'(z₀)` (6.13), Wilkinson's example.
- **§6.4 Least squares / Levenberg–Marquardt.** Gauss–Newton matrix (6.20), damped system (6.21)
  interpolating between Newton and steepest descent; algorithm only, no theorem.

### B.7 Chapter 7 — Matrix eigenvalue problems

- **Examples 7.1–7.2.** FD discretization of `−v'' + pv = λv` and Nyström discretization of an
  integral operator eigenproblem.
- **Thm 7.3 (Rayleigh).** `A` Hermitian, `λ₁ ≥ … ≥ λₙ`, orthonormal eigenvectors `xⱼ`:
  `λⱼ = max{(Ax,x)/(x,x) : 0 ≠ x ⟂ x₁..x_{j−1}}`. Structure: self-adjoint on FDIPS. Proof: expand in
  the eigenbasis. (= Saad Thm 1.10.)
- **Thm 7.4 (Courant min–max).** `λⱼ = min_{U ⊂ ℂⁿ, dim U = n+1−j} max_{x∈U∖0} (Ax,x)/(x,x)`. Proof: an
  `(n+1−j)`-dim `U` contains `x ⟂ x_{j+1}..xₙ` (underdetermined system), giving `max ≥ λⱼ`; equality on
  `Vⱼ = {x ⟂ x₁..x_{j−1}}`. (= Saad Thm 1.9.)
- **Cor 7.5 (Weyl's perturbation inequality).** `A, B` Hermitian: `|λⱼ(A) − λⱼ(B)| ≤ ‖A − B‖` for every
  norm on ℂⁿ. Proof: `(Ax,x) ≤ (Bx,x) + ‖A−B‖₂‖x‖²` in the min–max; then `‖A−B‖₂ = ρ(A−B) ≤ ‖A−B‖`
  (Thms 3.31, 3.32). Structure: self-adjoint on FDIPS with operator norm.
- **Cor 7.6.** Hermitian `A`: `|λᵢ − a'ᵢᵢ|² ≤ Σ_{j≠k}|aⱼₖ|²` where `a'ᵢᵢ` is the decreasing rearrangement of
  the diagonal. Proof: `B = diag(aⱼⱼ)`, `‖·‖₂ ≤ ‖·‖_F`.
- **Thm 7.7 (Gershgorin).** Every eigenvalue lies in `(⋃ⱼ row discs) ∩ (⋃ⱼ column discs)`,
  row disc `{|λ − aⱼⱼ| ≤ Σ_{k≠j}|aⱼₖ|}`. Structure: Mat(ℂ). Proof: pick the component of an eigenvector
  with `|xⱼ| = ‖x‖_∞ = 1`; columns via `A*`. (Elementwise proof, vs. Saad's norm proof; no
  "`m` discs ⇒ `m` eigenvalues" statement, unlike Saad Thm 3.12. Problem 7.6 is Bauer–Fike.)
- **Lemma 7.8.** Frobenius norm is unitarily invariant (`tr(AB) = tr(BA)`).
- **Cor 7.9 (Schur's inequality).** `Σ|λⱼ|² ≤ ‖A‖_F²`, equality iff `A` normal. Proof: Schur form,
  `‖A‖_F² = Σ|λⱼ|² + Σ_{j<k}|rⱼₖ|²`; normal triangular ⇒ diagonal.
- **Lemma 7.10.** Normal: `Σ|λⱼ|² = Σ|aⱼⱼ|² + N(A)²`, `N(A)² = Σ_{j≠k}|aⱼₖ|²`.
- **Lemma 7.11–7.13 (Jacobi rotations).** Plane rotation `U` in the `(j,k)` plane is unitary; for real
  symmetric `A`, `B = U*AU` changes only rows/columns `j,k` (explicit formulas); choosing
  `tan 2φ = 2aⱼₖ/(aⱼⱼ − aₖₖ)` (`φ = π/4` if equal) annihilates `bⱼₖ` and `N(B)² = N(A)² − 2aⱼₖ²`.
- **Thm 7.14 (classical Jacobi converges).** Annihilating the largest off-diagonal entry each step:
  `N(A_ν) ≤ qᵛ N(A₀)`, `q = (1 − 2/(n(n−1)))^{1/2} < 1`, so `A_ν → diag(λ)`. Proof:
  `aⱼₖ² ≥ N(A)²/(n(n−1))` for the largest entry + Lemma 7.13. A posteriori: `|λⱼ − aⱼⱼ,ν| ≤ N(A_ν)`
  (Cor 7.6). Eigenvectors from `Q_ν = U₁⋯U_ν`. Cyclic/threshold variants mentioned.
- **Def 7.16 / Thm 7.17.** Diagonalizable iff `n` independent eigenvectors (= Saad Thm 1.1).
- **Power method (unnumbered).** `A` diagonalizable, `|λ₁| > |λ₂| ≥ …`, `v₀ = Σ aₖxₖ`, `a₁ ≠ 0`:
  `λ₁^{−ν}Aᵛv₀ → a₁x₁`. (Problem 7.11: Rayleigh quotient error `≤ C|λ₂/λ₁|ᵛ`.) Interpreted as iteration
  of the 1-dim subspace `S = span v₀`.
- **Lemma 7.18 (subspace iteration).** `A` diagonalizable, `|λₘ| > |λ_{m+1}|`, `T = span{x₁..xₘ}`,
  `U = span{x_{m+1}..xₙ}`, `S` an `m`-dim subspace with `S ∩ U = {0}`. Then the orthogonal projections
  satisfy `‖P_{AᵛS} − P_T‖₂ ≤ M |λ_{m+1}/λₘ|ᵛ`. Proof: choose a basis `zⱼ = xⱼ + uⱼ` of `S` (`uⱼ ∈ U`,
  possible since `S ∩ U = 0`); `wⱼᵥ = λⱼ^{−ν}Aᵛzⱼ = xⱼ + λⱼ^{−ν}Aᵛuⱼ`, `‖wⱼᵥ − xⱼ‖ ≤ L|λ_{m+1}/λₘ|ᵛ`;
  compare the normal equations (Cor 3.53) of the two projections using the perturbation Thm 5.3.
  Structure: FDIPS, diagonalizable. (Compare Saad Thm 5.1/5.2: no diagonalizability, Schur vectors.)
- Invariant subspace ⇒ block triangularization `P*AP = [[A₁₁, A₁₂],[0, A₂₂]]`.
- **Thm 7.19 (simultaneous / orthogonal iteration).** `A` diagonalizable with `|λ₁| > |λ₂| > … > |λₙ|`
  [uncertain: the book requires `|λₘ| > |λ_{m+1}|` for all `m`], `Uₘ = span{x_{m+1}..xₙ}`; orthonormal
  `q₁₀..qₙ₀` with `Sₘ = span{q₁₀..qₘ₀}`, `Sₘ ∩ Uₘ = {0}` for all `m`; orthonormal `qⱼᵥ` with
  `AᵛSₘ = span{q₁ᵥ..qₘᵥ}`; `Q_ν = (q₁ᵥ..qₙᵥ)`, `A_ν = Q_ν*AQ_ν`. Then `aⱼₖ,ν → 0` for `k < j` and
  `aⱼⱼ,ν → λⱼ`. Proof: Lemma 7.18 for each `m` with the common rate `r = max|λ_{m+1}/λₘ|`; the projected
  vectors `wₘᵥ = P_{AᵛSₘ}xₘ − P_{AᵛS_{m−1}}xₘ` are eventually independent (Bolzano–Weierstrass) and
  span `AᵛSₘ`; Gram–Schmidt of `(wₘᵥ)` vs. of `(xₘ)` differ by `O(rᵛ)`; `qₘᵥ = φₘᵥ vₘᵥ` with phases
  `|φ| = 1`; `A_{ν+1} = D_ν*V_ν*AV_νD_ν` → upper triangular with `λⱼ` on the diagonal (superdiagonal need
  not converge because of the phases).
- **Thm 7.20 (QR algorithm).** Same hypotheses with `S_m = span{e₁..eₘ}`, i.e. (7.24)
  `span{e₁..eₘ} ∩ span{x_{m+1}..xₙ} = {0}` for all `m` (⇔ `X⁻¹` admits an `LR` decomposition, i.e.
  its leading principal minors are nonzero). Then `A₁ = A`, `A_ν = Q_νR_ν`, `A_{ν+1} = R_νQ_ν` gives
  `aⱼₖ,ν → 0` (`k < j`), `aⱼⱼ,ν → λⱼ`. Proof: `AQ_{ν−1} = Q_{ν−1}A_ν = Q_{ν−1}Q̃_νR_ν`, so one QR step is
  one step of Thm 7.19's simultaneous iteration (7.22)–(7.23). Remarks: convergence still holds without
  (7.24) but unordered; equal moduli give non-converging `2×2` blocks; shifts `A − σI` and deflation;
  Hessenberg form preserved (Problem 7.16), tridiagonal preserved for symmetric `A`.
- **Def 7.21 / Thm 7.22.** Hessenberg matrices; every `A` is unitarily similar to a Hessenberg matrix
  via `n−2` Householder reflections (`Q = H_{n−2}⋯H₁`, `B = Q*AQ`), cost `5n³/3` (Problem 7.17).
  Structure: FDIPS. (This is the dense counterpart of full Arnoldi: `AQ = QB`.)
- **Examples 7.23–7.24.** Symmetric tridiagonal: `pₖ(λ) = (aₖ − λ)p_{k−1} − cₖ²p_{k−2}` and its derivative
  (7.25)–(7.26); Newton on the characteristic polynomial with Gershgorin start values.
- **Thm 7.25 (Hyman's method).** `B` irreducible Hessenberg (`b_{j,j−1} ≠ 0`): backward recursions
  for `ξ, η` give `p(λ)/p'(λ) = ζ/β` without forming the characteristic polynomial. Proof: Cramer's rule
  `p(λ) = (−1)^{n−1}b₂₁⋯b_{n,n−1} ζ(λ)`, differentiate the triangular system.

### B.8–B.12 Chapters 8–12 (brief, main theorems)

**Ch. 8 Interpolation.** Thm 8.1 (a polynomial of degree `≤ n` with `> n` zeros vanishes), 8.2
(monomials independent), **8.3** (unique Lagrange interpolant `Lₙf = Σ f(xⱼ)ℓⱼ`), Def 8.4 / Lemma 8.6 /
**Thm 8.7** (Newton form with divided differences), **8.9** (Neville–Aitken recursion),
**8.10** (error `f(x) − (Lₙf)(x) = f^{(n+1)}(ξ)/(n+1)! Π(x−xⱼ)`), Cor 8.11 (`‖Rₙf‖_∞ ≤ ‖f^{(n+1)}‖_∞ ‖qₙ₊₁‖_∞/(n+1)!`),
Example 8.12–8.15 (linear/quadratic, Chebyshev nodes minimize `‖Π(x−xⱼ)‖_∞`, equidistant nodes),
**8.16 (Marcinkiewicz)** for each `f ∈ C[a,b]` some node sequence gives uniform convergence,
**8.17 (Faber)** for each node sequence some `f` fails (uniform boundedness principle),
**8.18–8.19** Hermite interpolation and its error `f^{(2n+2)}(ξ)/(2n+2)! Π(x−xⱼ)²`; trigonometric:
8.21–8.23 (uniqueness/existence of degree-`n` trigonometric interpolants at `2n+1` nodes), **8.24–8.25**
(equidistant nodes: explicit discrete Fourier coefficients, `2n+1` and `2n` points); splines: Def 8.26,
Lemmas 8.28–8.29 (minimal `L²` curvature / uniqueness), **8.30** (unique interpolating spline of odd
degree `2ℓ−1` with `ℓ−1` boundary derivatives), 8.31–8.32 (B-splines form a basis), **8.33–8.34**
(cubic spline errors `‖f − s‖_∞ ≤ h^{3/2}‖f''‖₂/2`, `‖f' − s'‖_∞ ≤ h^{1/2}‖f''‖₂`; `O(h⁴)` for `C⁴` on
equidistant grids); Bézier/Bernstein: 8.37 (partition of unity), 8.39–8.42 (de Casteljau,
endpoint derivatives, subdivision).

**Ch. 9 Numerical integration.** **Thm 9.1–9.2** (interpolatory quadrature of order `n` has weights
`aₖ = ∫ℓₖ`, uniquely determined by exactness on `Pₙ`), 9.3 (Newton–Cotes weights), **9.4/9.5**
(trapezoidal `−h³f''(ξ)/12`, Simpson `−h⁵f^{(4)}(ξ)/90`), **9.7/9.8** (composite rules `O(h²)`, `O(h⁴)`),
Def 9.9, **Thm 9.10 (Szegő)** a sequence of quadratures converging on polynomials converges on
`C[a,b]` iff the weight sums `Σ|aₖ^{(n)}|` are bounded, **Cor 9.11 (Steklov)** nonnegative weights +
polynomial convergence ⇒ convergence; Gaussian: Def 9.12, Lemma 9.13–9.14 (nodes are zeros of the
orthogonal polynomial `qₙ₊₁` w.r.t. `w`), **Lemma 9.15** (orthogonal polynomials exist uniquely, via
Gram–Schmidt Thm 3.18 — three-term recurrence not stated but implicit), **9.16** (`qₙ` has `n` simple
zeros in `(a,b)`), **Thm 9.17** (unique Gaussian formula of order `n`, exact on `P_{2n+1}`),
**9.18** (positive weights), **Cor 9.19** (Gaussian formulae converge on `C[a,b]`), **9.20** (error
`f^{(2n+2)}(ξ)/(2n+2)! ∫w qₙ₊₁²`); periodic: Def 9.23–Lemma 9.25 (Bernoulli polynomials), **Thm 9.26
(Euler–Maclaurin)**, **Cor 9.27** (rectangular rule for `2π`-periodic `C^{2m+1}` functions: error
`O(n^{−2m−1})`), Thm 9.28 [uncertain] derivative-free estimates; Romberg: **9.29** (`O(h^{2m})`),
9.30 (positive weights), 9.31 (convergence), 9.32 (Romberg = extrapolation of `Tₕ` in `h²`); improper
integrals 9.33 (graded/transformed quadrature with Hölder-type remainder).

**Ch. 10 Initial value problems.** **Thm 10.5 (Picard–Lindelöf)**: `f` continuous with Lipschitz
constant `L` in `u` on a domain `G ⊂ ℝ^{n+1}` ⇒ unique local solution on `[x₀−a, x₀+a]`; proof: Volterra
operator is a contraction on `C[x₀−a,x₀+a]` for `La < 1` (Banach Thm 3.45); **Cor 10.6**: Picard
iterates converge uniformly with a posteriori estimate `‖u − u_ν‖_∞ ≤ La/(1−La) ‖u_ν − u_{ν−1}‖_∞`
(Thm 3.46). Defs 10.8–10.14 (Euler, implicit/trapezoidal Euler, improved Euler/Heun, general one-step
`u_{j+1} = uⱼ + hφ(xⱼ,uⱼ;h)`), Def 10.16 local discretization error `d(x,u;h) = [η(x+h) − η(x)]/h − φ(x,u;h)`,
consistency (`sup|d| → 0`), order `p` (`|d| ≤ Kh^p`); **Thm 10.17** consistent iff `φ(x,u;h) → f(x,u)`
uniformly; **10.18–10.19** Euler order 1, Heun order 2; **Lemma 10.21** discrete Gronwall
(`|ξ_{j+1}| ≤ (1+A)|ξⱼ| + B ⇒ |ξⱼ| ≤ e^{jA}|ξ₀| + (e^{jA} − 1)B/A`); **Thm 10.22 (Lax-type equivalence
for one-step methods)**: if `φ` is continuous and Lipschitz in `u`, the method is convergent iff
consistent, with `E(h) ≤ c(h)(e^{M(b−a)} − 1)/M`; **Thm 10.23**: consistency order `p` ⇒ convergence
order `p`, `|eⱼ| ≤ (K/M)(e^{M(xⱼ−x₀)} − 1)h^p`; Cor 10.24; Def 10.25 / **Thm 10.26** classical
Runge–Kutta has order 4 (for `f ∈ C⁴`). Multistep: Def 10.27, Def 10.28, **Thm 10.29** (Adams-type
methods with `s` quadrature points are consistent of order `s+1`), Def 10.30 (consistent starting
values), Def 10.32–**Thm 10.33 (root condition)**: the linear difference equation is stable iff all roots
of `ρ(λ) = λ^r + Σ aₘλ^m` satisfy `|λ| ≤ 1` with unimodular roots simple; Lemma 10.34 (variation of
constants); Def 10.35 stability of a multistep method; Lemma 10.37 (Gronwall variant);
**Thm 10.38 (Dahlquist)**: `φ` Lipschitz, method consistent and stable, starting values consistent ⇒
convergent; order `p` if both have order `p`. Stiffness/absolute stability discussed informally.

**Ch. 11 Boundary value problems.** Shooting (§11.1), **Thm 11.4** (`−u'' + qu = r`, `q ≥ 0`, Dirichlet
⇒ unique `C²` solution), **Thm 11.5** (FD system uniquely solvable: matrix irreducible + weakly
diagonally dominant, Thm 4.7), **Lemma 11.6** (`A⁻¹ ≥ 0` entrywise and `≤ A₀⁻¹`, proved by monotone
Jacobi iterates — an M-matrix argument), Lemma 11.7 (central difference consistency `h²‖u^{(4)}‖/12`),
**Thm 11.8** (FD error `|u(xⱼ) − uⱼ| ≤ h²‖u^{(4)}‖_∞(b−a)²/96` [uncertain constant]), 11.10 (variable
coefficient version), **Thm 11.11 (Riesz representation)**, Def 11.12 strictly coercive
(`Re(Au,u) ≥ c‖u‖²`), **Thm 11.13 (Lax–Milgram, operator form)**: bounded strictly coercive `A` on a
Hilbert space has a bounded inverse, `‖A⁻¹‖ ≤ 1/c`; proof: `‖Au‖ ≥ c‖u‖` gives injectivity and closed
range, coercivity of the adjoint gives density of the range; Def 11.14, **Thm 11.15** (bounded strictly
coercive sesquilinear `S` ⇔ operator `A` with `S(u,v) = (u,Av)`, via Riesz), **Cor 11.16 (Lax–Milgram,
form version)**: unique `u` with `S(v,u) = F(v) ∀v`; **Thm 11.17 (Céa)**: for the Galerkin equations
`(Au_n, v) = (f,v) ∀v ∈ X_n` (finite-dim `X_n`), unique solvability and
`‖u_n − u‖ ≤ M inf_{v∈X_n}‖v − u‖` with `M = ‖A‖/c` (proof: `A_n = P_nA|_{X_n}` strictly coercive with
the same `c`, `u_n − u = (A_n⁻¹P_nA − I)(u − v)`, `‖P_n‖ = 1` by Thm 3.52); Sobolev `H¹[a,b]` (Thms
11.19–11.22: Hilbert, `C¹` dense, `H¹ ⊂ C`, `H¹₀` closed), **Thm 11.24** (unique weak solution for
`p > 0`, `q ≥ 0`, via Cor 11.16), **11.25** (weak ⇒ classical), Lemma 11.26 (linear interpolation
`L²` estimates), **Thms 11.27–11.28** (linear finite elements: `‖u_n − u‖_{H¹} ≤ C‖u''‖h`,
`‖u_n − u‖_{L²} ≤ C‖u''‖h²` by the Aubin–Nitsche duality trick).

**Ch. 12 Integral equations.** Def 12.1 compact operator, **Thm 12.2 (Riesz theory / Fredholm
alternative)**: `A` compact on a normed space ⇒ `I − A` surjective iff injective, and then `(I−A)⁻¹`
bounded (proved via Problems 12.13–12.16; Riesz lemma), **Thm 12.3 (Arzelà–Ascoli)**, **12.4** (integral
operators with continuous kernel are compact on `C[a,b]`), 12.5 (`‖A‖_∞ = max_x ∫|K(x,y)|dy`),
**Thm 12.6 (norm-convergent approximation)**: `I − A` injective, `‖A_n − A‖ → 0` ⇒ `(I − A_n)⁻¹` exist
and are uniformly bounded for large `n`, `‖φ_n − φ‖ ≤ C(‖(A_n − A)φ‖ + ‖f_n − f‖)` (proof: Neumann series
Thm 3.48 on `I − (I−A)⁻¹(A−A_n)`), **Thm 12.7 (uniform boundedness / Banach–Steinhaus)**, Def 12.8
collectively compact, **Lemma 12.9** (`B_n → B` pointwise, `(A_n)` collectively compact ⇒
`‖(B_n − B)A_n‖ → 0`), **Thm 12.10 (Anselone)**: `I − A` injective, `(A_n)` collectively compact and
pointwise convergent ⇒ same conclusions as 12.6 (proof: approximate inverse `I + (I−A)⁻¹A_n`, Lemma 12.9,
Neumann series), **Thm 12.11** (Nyström: solution of the discretized equation is determined by its
values at the nodes via the natural interpolation), 12.12 (norm of quadrature operators),
**Thm 12.13** (convergent quadrature ⇒ `(A_n)` collectively compact and pointwise convergent but not
norm convergent), hence Nyström converges with the quadrature error rate; collocation: **Thm 12.16**
(`‖L_nA − A‖ → 0` ⇒ unique solvability and `‖φ_n − φ‖ ≤ C‖L_nφ − φ‖`), **Cor 12.17** (pointwise
convergent interpolation suffices, by Lemma 12.9), 12.18 (linear spline collocation converges),
Lemma 12.20 / **Thm 12.21** (trigonometric collocation converges for `C¹` periodic data); stability:
**12.23** (Nyström condition numbers uniformly bounded), **12.24** (collocation condition number
`≤ C cond(E_n)`), **Thm 12.25** (a compact operator has a bounded inverse iff `X` is finite-dimensional
⇒ first-kind equations are ill-posed).

---------------------------------------------------------------------------------------------------

## Cross-book commonality report

Summary table (S = Saad eigenvalue book, K = Kress):

| # | Theme | S | K | Natural generality |
|---|-------|---|---|--------------------|
| 1 | spectral radius / Gelfand / stationary iteration | Cor 1.1, §3.5 | 3.30–3.32, 3.48, 4.1 | Banach algebra / Banach space |
| 2 | splittings, Jacobi/GS/SOR, dominance, SPD | (1.11 only) | 4.2–4.18 | Mat(ℂ) entrywise + FDIPS for SPD |
| 3 | cond, perturbation of `Ax = b`, Neumann series | (3.14), 3.2, §3.3 | 3.48, 5.2–5.3 | Banach space |
| 4 | Krylov, Arnoldi, Lanczos | 6.1–6.9, Thm 6.1–6.2 | — (GS 3.18, Hessenberg 7.22) | vector space / FDIPS |
| 5 | Petrov–Galerkin projection | §4.3 | 11.17, 3.51–3.53, 12.6–12.17 | Hilbert space |
| 6 | Chebyshev min–max | 4.8–4.9, 6.3–6.8 | — (9.15 only) | real polynomials + spectral calculus |
| 7 | eigenvalue perturbation/localization | ch. 3, 1.9–1.10 | 7.3–7.9 | self-adjoint on FDIPS / Mat(ℂ) |
| 8 | Banach FPT, Newton | (3.56), 4.3 RQI | 3.44–3.48, 6.1–6.21, 10.5 | complete metric / Banach space |
| 9 | best approximation, projection, Lax–Milgram, Céa | 3.1, 6.1, §7.6 | 3.49–3.54, 11.11–11.17 | Hilbert space |
| 10 | power / subspace iteration / QR | 4.1, 5.1–5.2 | 7.18–7.20, 7.14 | finite-dim over ℂ (Schur) |

### Theme 1 — Spectral radius, `Tᵏ → 0 ⇔ ρ(T) < 1`, Gelfand, stationary iterations

- **Kress.** Def 3.30 `ρ`; Thm 3.31 `‖A‖₂ = √ρ(A*A)`; **Thm 3.32** `ρ(A) ≤ ‖A‖` for every norm and
  `∀ε ∃ norm: ‖A‖ ≤ ρ(A) + ε` (finite-dim proof via Schur form + diagonal scaling); **Thm 3.48**
  Neumann series with a priori/a posteriori bounds and `‖(I−B)⁻¹‖ ≤ 1/(1−‖B‖)` (Banach space);
  **Thm 4.1** `x_{ν+1} = Bx_ν + z` converges `∀z, x₀` ⇔ `ρ(B) < 1` (finite-dim; remark that it holds in
  Banach spaces); Problem 4.3 `Aᵛ → 0 ⇔ ρ(A) < 1`; Cor 4.16 uses `−ln ρ` as the convergence speed.
  Kress never states Gelfand's formula explicitly — Thm 3.32 is his substitute.
- **Saad.** **Cor 1.1** (Gelfand `lim‖Aᵏ‖^{1/k} = ρ(A)` for any matrix norm, from the Jordan/spectral
  decomposition Thm 1.3); **P-5.6** `‖Bᵏ‖₂ ≤ α k^{ℓ−1}ρ(B)ᵏ`; §3.5 (3.56)–(3.57) `x_{k+1} = Gx_k + f`
  converges when `ρ(G) < 1` with asymptotic rate `ρ(G)ᵏ`, and (3.60) the exact expansion of `Gᵏ` in
  spectral projectors and nilpotents (transient growth ↔ pseudospectra); resolvent Neumann expansion
  (3.14); Thm 5.2's proof is exactly "`‖(A|_W)ᵏ‖^{1/k} → ρ`" applied to the complementary invariant
  subspace.
- **Most general natural statement.** For a bounded operator `T` on a complex Banach space (or an
  element of a complex unital Banach algebra): `ρ(T) = lim ‖Tⁿ‖^{1/n} = inf ‖Tⁿ‖^{1/n}` (Gelfand);
  `Tⁿ → 0` in norm ⇔ `ρ(T) < 1` ⇔ `∃ n: ‖Tⁿ‖ < 1` ⇔ `∃` equivalent norm with `‖T‖ < 1`
  (renorming `|x| = Σₖ (ρ+ε)^{−k}‖Tᵏx‖` replaces Kress's Schur-form construction); and for
  `x_{k+1} = Tx_k + c`: convergence for every `c, x₀` ⇔ `ρ(T) < 1`, in which case the limit is
  `(I−T)⁻¹c` and `‖x_k − x‖ ≤ ‖Tᵏ‖‖x₀ − x‖`. Kress 3.48 is the quantitative special case `‖T‖ < 1`;
  Kress 4.1 (⇒) needs an eigenvector, so in infinite dimensions one uses `ρ(T) ≥ 1 ⇒ ‖Tⁿ‖ ↛ 0`
  directly from Gelfand. Mathlib already has the spectral radius and (for complex Banach algebras) a
  Gelfand-formula statement, so the backbone lemma "`Tⁿ → 0 ⇔ ρ(T) < 1`" and the stationary-iteration
  corollary should be proved once at Banach-algebra level and specialised to `Matrix n n ℂ` with any
  induced norm. Saad's (3.60) and P-5.6 (polynomial-times-geometric bound with Jordan index) are the
  finite-dimensional refinement.

### Theme 2 — Splittings, Jacobi / Gauss–Seidel / SOR, diagonal dominance, SPD criteria, M-matrices

- **Kress** proves the whole classical theory: Thm 4.2 (Jacobi under strict row/column/Frobenius
  dominance, with explicit contraction constants `q_∞, q₁, q₂` and Banach-type error bounds), Thm 4.3
  (Gauss–Seidel under Sassenfeld, `‖(D+A_L)⁻¹A_R‖_∞ ≤ p`), Cor 4.4, Thm 4.7 (irreducible + weak
  dominance ⇒ Jacobi converges, via `ρ ≤ 1` and an index-set argument), Thm 4.9 (optimal JOR), Thm 4.11
  (Kahan `0 < ω < 2`), **Thm 4.12 (Ostrowski: SPD ⇒ SOR converges for all `ω ∈ (0,2)`)**, Thm 4.15
  (Young: consistently ordered ⇒ `ω_opt`, `ρ = ω_opt − 1`), Cor 4.16 (`ρ_GS = ρ_J²`), Example 4.17
  (`ρ ≈ 1 − 2π/(n+1)`), §4.3 defect correction `x_{ν+1} = x_ν + M⁻¹(y − Ax_ν)`, Thm 4.18 two-grid
  `ρ = ½`. *Regular splittings / M-matrices* appear only in embryonic form: Problem 4.16 (`A ≥ 0`,
  `ρ(A) < 1 ⇒ (I−A)⁻¹ ≥ 0`) and Lemma 11.6 (`A⁻¹ ≥ 0` for the FD matrix via monotone Jacobi iterates).
  There is no abstract "`A = M − N`, convergence iff `ρ(M⁻¹N) < 1`" theorem, but defect correction
  (4.15) *is* that statement with `M = A_approx`.
- **Saad (eigenvalue book)** contains essentially nothing here: Thm 1.11 (Perron–Frobenius, stated),
  the definition of irreducibility (§1.10), and the remark in §3.5 that stationary methods are
  `x_{k+1} = Gx_k + f`. (The splitting theory lives in Saad's *Iterative Methods for Sparse Linear
  Systems*, ch. 4, outside this survey.)
- **Most general natural statement.** Three layers: (i) *abstract splitting*: `A = M − N` with `M`
  invertible on any finite-dim space (or Banach space): the iteration `Mx_{k+1} = Nx_k + b` converges
  for all data iff `ρ(M⁻¹N) < 1` — a direct corollary of Theme 1, no matrix entries needed;
  (ii) *entrywise criteria* (diagonal dominance, Sassenfeld, irreducibility, M-matrices, regular
  splittings `M⁻¹ ≥ 0, N ≥ 0 ⇒ ρ(M⁻¹N) < 1 ⇔ A⁻¹ ≥ 0`) live on `Matrix n n ℂ` / `Matrix n n ℝ` with the
  entrywise order and the `∞`/`1` norms (Kress Thm 3.26); Kress Thm 4.7's proof is the standard
  Taussky-type argument and should be formalised via the digraph of `A`; (iii) the *SPD criterion*: the
  natural form is the Householder–John / Ostrowski–Reich theorem — `A` Hermitian positive definite,
  `A = M − N`, `M + Mᴴ − A` (equivalently `M + Nᴴ`) positive definite ⇒ `ρ(M⁻¹N) < 1`; Kress 4.12 is
  the case `M = D/ω + A_L`, where `M + Mᴴ − A = (2/ω − 1)D`, and the proof by the Rayleigh-quotient
  identity for `μ` generalises to the `A`-inner-product energy argument. This belongs to FDIPS
  (self-adjoint positive operators on a finite-dim inner product space), not to entrywise matrices.
  Young's theory (consistently ordered, `ρ_GS = ρ_J²`) is genuinely matrix-combinatorial and lower
  priority for a Krylov backbone.

### Theme 3 — Condition number, perturbation of `Ax = b`, Neumann series

- **Kress.** Def 5.2 `cond(A) = ‖A‖‖A⁻¹‖` for bounded bijections between normed spaces; **Thm 5.3**
  (perturbation of both `A` and `y`, Banach spaces, hypothesis `‖A⁻¹‖‖A^δ − A‖ < 1`, conclusion the
  standard relative bound); **Thm 3.48** (Neumann series, `‖(I−B)⁻¹‖ ≤ 1/(1−‖B‖)`, error bounds);
  Problem 3.16 (`Σ Bᵏ = (I−B)⁻¹` in `L(X)`); Problem 5.8 (`1/cond(A) = min{‖B‖ : A + B singular}/‖A‖`);
  Thm 3.31 (`cond₂` of Hermitian = `|λ_max/λ_min|`), SVD Thms 5.4–5.5 (`cond₂ = μ₁/μ_r`), Tikhonov
  (5.22) `cond₂(αI + A*A) ≤ 2μ₁²/α`. Also Cor 6.15 uses Thm 3.48 to keep `f'(x)` invertible near `x*`,
  and Thms 12.6/12.10 use it for stability of `I − A_n`.
- **Saad.** §3.3 recalls `Cond(A) = ‖A‖‖A⁻¹‖`; Thm 3.6 (Bauer–Fike) is a perturbation result whose
  proof is a one-line Neumann-free norm inequality with `Cond₂(X)`; the Neumann series is used for the
  resolvent (3.14), Prop 3.2, Thm 3.3(3), Thm 3.4 (`a > 0`), and Gershgorin (3.50)
  (`‖C‖_∞ < 1 ⇒ I + C` invertible); Thm 3.2 (`‖P − Q‖ < 1 ⇒` equal rank) is another `‖E‖ < 1`
  argument.
- **Most general natural statement.** Both books use exactly the Banach-space statements: for `X`
  Banach, `‖B‖ < 1 ⇒ I − B ∈ GL(X)` with `(I−B)⁻¹ = Σ Bᵏ`, `‖(I−B)⁻¹‖ ≤ 1/(1−‖B‖)`; the group of units is
  open with `‖(A+E)⁻¹ − A⁻¹‖ ≤ ‖A⁻¹‖²‖E‖/(1 − ‖A⁻¹‖‖E‖)`; and Kress 5.3 verbatim. Mathlib has the
  Neumann series for complete normed rings (`NormedRing.inverse_one_sub`, openness of units); the
  perturbation theorem 5.3 and the "relative condition" formulation are the missing thin layer. The
  eigenvalue-side analogue (Theme 7: Bauer–Fike) is the same inequality applied to
  `(D − λ̃I)⁻¹`. Saad's resolvent analyticity (Prop 3.2, Thm 3.4) is the Banach-algebra fact that
  `z ↦ (A − z)⁻¹` is analytic off the spectrum; Mathlib has this (`spectrum.hasDerivAt_resolvent`,
  resolvent analytic on the resolvent set) — useful if Riesz projections (Thm 3.3) are ever wanted.

### Theme 4 — Krylov subspaces, Arnoldi, Lanczos, grade, minimal polynomial, invariance

- **Saad** is the only source: **Prop 6.1** (`Kₘ = {p(A)v : deg p < m}`), **Prop 6.2** (grade `μ` =
  degree of the minimal polynomial of `v`; `K_μ` invariant and `Kₘ = K_μ` for `m ≥ μ`), **Prop 6.3**
  (`dim Kₘ = m ⇔ μ > m−1`), **Prop 6.4** (for *any* projector `Qₘ` onto `Kₘ`, `q(A)v = q(Aₘ)v` for
  `deg q < m` and `Qₘq(A)v = q(Aₘ)v` for `deg q ≤ m`, `Aₘ = QₘA|_{Kₘ}`), **Thm 6.1** (characteristic
  polynomial of the orthogonal section minimises `‖p(A)v‖₂` over monic `p` of degree `m`),
  **Props 6.5–6.8** (Arnoldi basis, `AVₘ = VₘHₘ + h_{m+1,m}v_{m+1}eₘᵀ`, breakdown ⇔ grade, residual
  `h_{m+1,m}|eₘᵀy|`), **Thm 6.2** (Hermitian ⇒ tridiagonal, Lanczos), §6.3.2 (Lanczos = Stieltjes
  orthogonal polynomials for `⟨p,q⟩ = (p(A)v,q(A)v)`), **Prop 6.9** (two-sided Lanczos,
  `WₘᴴAVₘ = Tₘ`, biorthogonality), P-6.1 (`‖(I−Pₘ)APₘ‖ = h_{m+1,m}`), P-6.8 (`v_{m+1} ∝ p_{Hₘ}(A)v₁`),
  block versions §6.5, and IRA in ch. 7 (`q` shifted QR steps on `Hₘ` = restart with
  `Π(A − μⱼ)v₁`).
- **Kress** has no Krylov subspaces. The relevant building blocks are: **Thm 3.18** (Gram–Schmidt with
  the nested-span property — Arnoldi is Gram–Schmidt applied to `v, Av, A²v, …`, which is precisely the
  proof of Saad Prop 6.5), **Lemma 9.15** (orthogonal polynomials via Gram–Schmidt — the polynomial
  side of Lanczos), Def 7.21 / **Thm 7.22** (Householder reduction to Hessenberg form `Q*AQ = B` —
  the `m = n` Arnoldi relation `AQ = QB` computed by reflections), **Thm 7.25** / Problem 7.15
  (irreducible Hessenberg matrices; cf. Saad P-1.17: unreduced Hessenberg ⇒ non-derogatory), and
  Problem 7.16 (Hessenberg form is invariant under QR steps — the fact IRA relies on).
- **Most general natural statement.** Layered: (i) *algebraic layer over an arbitrary field*: for
  `A ∈ End(V)`, `v ∈ V`, `Kₘ(A,v) = image of {p : deg p < m}` under `p ↦ aeval A p v`; the annihilator
  ideal of `v` is principal, generated by the minimal polynomial `μ_v` of `v`; `dim Kₘ = min(m, deg μ_v)`;
  `K_{deg μ_v}` is the smallest `A`-invariant subspace containing `v`; Prop 6.4 holds for any
  complement/projector. This needs only `Polynomial.aeval`, `Module.End`, and Mathlib's `minpoly`
  machinery (adapted from elements to vectors). (ii) *inner-product layer* (FDIPS over ℝ or ℂ, or a
  Hilbert space with `A` bounded): Arnoldi = Gram–Schmidt on the Krylov sequence; the identity
  `(I − Pₘ)APₘ = h_{m+1,m} v_{m+1}vₘ*` (rank one), `PₘAPₘ|_{Kₘ}` is represented by an unreduced
  Hessenberg `Hₘ`; residual formula; Thm 6.1 via normal equations (Theme 9). (iii) *self-adjoint layer*:
  `Hₘ` tridiagonal, three-term recurrence, orthogonal polynomials w.r.t. the spectral measure of `v`.
  (iv) *oblique layer*: two-sided Lanczos as Petrov–Galerkin on `(Kₘ(A,v), Kₘ(A*,w))` (Theme 5),
  breakdown ⇔ `Kₘ(A,v) ∩ Kₘ(A*,w)^⟂ ≠ 0`. All Saad proofs here are dimension-free except for
  `grade ≤ n` and Cayley–Hamilton in Thm 6.1 (replace by `μ_v` of degree `m` when `m` = grade, or keep
  finite-dim).

### Theme 5 — Projection (Petrov–Galerkin) methods: linear systems vs eigenproblems

- **Saad (eigenproblems).** §4.3 defines the Petrov–Galerkin condition `Aũ − λ̃ũ ⟂ L`, `ũ ∈ K`; the
  section `Aₘ = P_KA|_K` (orthogonal) or `Q_K^LA|_K` (oblique, needs `K ∩ L^⟂ = 0`); matrix forms
  `VᴴAV`, `WᴴAV` (biorthogonal `V,W`); **Prop 4.3** invariance ⇒ exactness; **Thms 4.3/4.7** residual of
  the exact pair for the section bounded by `γ‖(I−P_K)u‖`; Hermitian: **Prop 4.4, Cor 4.1, Thm 4.4**
  (Ritz values interlace below: `λ̃ᵢ ≤ λᵢ`, Courant–Fischer on `K`), **Lemma 4.1–Thm 4.5** (eigenvalue
  error `≤ ‖A − λI‖ tan²θ` type bounds), **Thm 4.6** (`sin θ(u,ũ) ≤ √(1 + γ²/δ²) sin θ(u,K)`),
  **Prop 4.5**; Krylov specialisation via **Prop 6.4**, **Thm 6.1**; **Prop 6.9** for oblique Krylov;
  Thm 8.1 (Davidson, monotone Ritz values); Lemma 8.1 (Rayleigh–Ritz is basis-independent).
- **Kress (linear operator equations).** **Thm 11.17 (Céa)**: Galerkin equations
  `P_nAu_n = P_nf` in `X_n` for bounded strictly coercive `A` on a Hilbert space; unique solvability
  and quasi-optimality `‖u_n − u‖ ≤ (‖A‖/c) inf_{v∈X_n}‖u − v‖`; the proof's key identity
  `u_n − u = (A_n⁻¹P_nA − I)(u − v)` with `A_n⁻¹P_nAv = v` for `v ∈ X_n` is the linear-system twin of
  Saad Prop 4.3 ("exact on the trial space"). **Cor 3.53** (normal equations = Galerkin for `A = I`),
  **Thm 3.51/3.52** (orthogonal projection), **Thm 5.9** (Tikhonov normal equations); ch. 12:
  **Thms 12.6, 12.10, 12.16, Cor 12.17** (projection/collocation methods `L_nAφ_n = L_nf` for
  `I − A` with `A` compact: stability `(I − L_nA)⁻¹` uniformly bounded, error `≤ C‖L_nφ − φ‖`) — a
  Céa-type result without coercivity, using compactness + Neumann series; **Lemma 7.18 / Thm 7.19**
  (subspace iteration compares projections onto `AᵛS` and `T` through normal equations) and Alg 5.3
  of Saad (subspace iteration *with* Rayleigh–Ritz) are the same idea from both sides.
- **Common abstract structure.** Fix a Hilbert space `X` (finite-dim suffices for both books), a
  bounded `A`, a closed trial subspace `K` and test subspace `L` with `X = K ⊕ L^⟂` (⇔ the oblique
  projector `Q = Q_K^L` onto `K` along `L^⟂` exists; `Q = P_K` when `L = K`). The *compression*
  `A_K := QA|_K ∈ End(K)`. Then:
  - linear system `Ax = b`: Petrov–Galerkin solution `x_K ∈ K` with `Q(Ax_K − b) = 0`, i.e.
    `A_K x_K = Qb`; exactness on invariant/solvable subspaces (`x ∈ K ⇒ x_K = x`, Kress's `A_n⁻¹P_nAv = v`);
    Céa when `A_K` is uniformly invertible (coercivity gives `‖A_K⁻¹‖ ≤ 1/c` for `L = K`; for Krylov
    methods CG/GMRES/FOM, `K = Kₘ`, `L = Kₘ` or `AKₘ`);
  - eigenproblem: `A_K ũ = λ̃ũ`; exactness on invariant subspaces (Prop 4.3); residual bounds
    (Thm 4.3/4.7) where the constant `γ = ‖QA(I−P_K)‖` plays the role of Céa's `‖A‖/c`;
  - in both cases the error is controlled by `dist(x, K)` resp. `sin θ(u,K)`, and the Hermitian/coercive
    case gives sharper monotone/interlacing statements (Courant–Fischer on `K`, Cor 4.1; Céa with
    constant `√(‖A‖/c)` in the energy norm).
  The natural formal object is therefore "a linear map compressed to a subspace along a complement",
  with two instantiations (solve vs. eigen). Formalising `A_K` once, with lemmas (a) `A_K = A|_K` on
  invariant `K`, (b) `Q(A − λ)(I − P_K)` residual identity, (c) matrix representation `WᴴAV` for
  biorthogonal bases, (d) `‖P_K‖ = 1` and `‖Q‖ ≥ 1`, covers Saad §4.3, Kress 11.17, and the Krylov
  methods (Prop 6.4 says the compression commutes with polynomials of degree `< m` on `v`).

### Theme 6 — Chebyshev polynomials, min–max property, convergence bounds

- **Saad.** §4.4: definition, three-term recurrence, closed forms (4.47)–(4.48), complex extension
  via the Joukowski map; **Thm 4.8** (real min–max on `[α,β]` with normalisation at `γ ∉ [α,β]`;
  *stated without proof*, value `1/|Cₖ(1 + 2(α−γ)/(β−α))|`); **Lemma 4.3** (Zarantonello, circles);
  **Thm 4.9** (ellipses: two-sided bound, scaled Chebyshev asymptotically optimal). Applications:
  **Thm 6.3** (`tan θ(uᵢ,Kₘ) ≤ κᵢ tan θ(v₁,uᵢ)/C_{m−i}(1+2γᵢ)`), **Thm 6.4** (Kaniel–Paige–Saad Ritz value
  bound, squared Chebyshev denominator), §6.6.3 (Ritz vectors), **Prop 6.10 / Thm 6.8** (Arnoldi,
  circle/ellipse enclosures), §5.3.3 (Chebyshev-accelerated subspace iteration), §7.4 (Chebyshev
  iteration, damping coefficients `κᵢ = |wᵢ/w₁|` from Thm 4.9), §7.6 (least-squares polynomials in
  Chebyshev bases). The book explicitly notes the same polynomial is what drives CG.
- **Kress.** Chebyshev polynomials of the first kind never appear as an extremal object. Related:
  Lemma 9.15–9.16 (orthogonal polynomials for a weight, of which `Cₖ` is the case `w = (1−x²)^{−1/2}`),
  Example 8.13–8.14 [uncertain numbering] (Chebyshev nodes minimise `‖Π(x−xⱼ)‖_∞` — the *monic*
  min–max property, `2^{1−n}`), Thm 8.16's proof cites the Chebyshev alternation theorem, and the SOR
  rate `1 − O(h)` of Example 4.17 contrasts with the `1 − O(√)` rates that Chebyshev/CG achieve.
- **Most general natural statement.** Two independent pieces. (a) *Pure polynomial extremal theorem*
  (real analysis, no linear algebra): for `k ≥ 0`, `α < β`, `γ ∉ [α,β]`,
  `min{‖p‖_{∞,[α,β]} : p ∈ ℝ[x], deg p ≤ k, p(γ) = 1} = 1/|Cₖ(1 + 2(α−γ)/(β−α))| = 1/Cₖ(1 + 2 dist(γ,[α,β])/(β−α))`,
  with the explicit minimiser, proved by the alternation/equioscillation argument (`Cₖ` has `k+1`
  alternation points on `[−1,1]`); plus the growth estimate `Cₖ(1+2η) ≥ ½(1 + 2√η)^k` [uncertain
  form; standard: `Cₖ(t) ≥ ½(t + √(t²−1))ᵏ` for `t ≥ 1`] that turns denominators into geometric rates
  (`((√κ−1)/(√κ+1))ᵏ` for CG, `(1+2√γᵢ)^{−(m−i)}`-type rates for Lanczos). Mathlib has
  `Polynomial.Chebyshev.T` (any commutative ring), the recurrence and `T_complex_cos`; the extremal
  property and the closed form (4.48) are not there. (b) *Spectral-calculus transfer*: for a bounded
  self-adjoint `A` on a Hilbert space with `σ(A) ⊂ [α,β]` and `p` a real polynomial,
  `‖p(A)x‖ ≤ max_{σ(A)}|p| ‖x‖` (finite-dim: expand in an orthonormal eigenbasis, which is what Saad's
  Thm 6.3/6.4 proofs do; Hilbert: continuous functional calculus, which Mathlib has). Everything else
  (Lanczos bounds, CG bound, Chebyshev semi-iteration) is (a)+(b)+Theme 5. The complex versions
  (Lemma 4.3, Thm 4.9) are needed only for non-Hermitian Arnoldi/Chebyshev iteration and can be
  deferred; Thm 4.9 is only an asymptotic optimality statement anyway.

### Theme 7 — Eigenvalue perturbation and localisation

- **Kress.** **Thm 7.3** (Rayleigh, recursive max), **Thm 7.4** (Courant–Fischer, `dim = n+1−j` form),
  **Cor 7.5** (Weyl: `|λⱼ(A) − λⱼ(B)| ≤ ‖A − B‖`, any norm, Hermitian), **Cor 7.6** (diagonal entries
  vs eigenvalues, Frobenius off-diagonal — the *global* a-posteriori bound for the Jacobi method),
  **Thm 7.7** (Gershgorin, rows ∩ columns, eigenvector proof), **Cor 7.9** (Schur inequality,
  equality ⇔ normal), Lemma 7.10; Problem 7.6 is Bauer–Fike in `p`-norms (`|λ − λⱼ| ≤ cond_p(C)‖B‖_p`);
  Problem 7.11 power-method Rayleigh-quotient error; Thm 3.32 (`ρ ≤ ‖·‖` — the crudest localisation,
  also Saad §3.4 opening).
- **Saad.** **Thm 1.9/1.10** (min–max, Courant); ch. 3: **Thm 3.6** (Bauer–Fike), **Thm 3.7 / Cor 3.2**
  (nondiagonalizable, index `ℓ`), **Cor 3.3** (Hermitian `|λ − λ̃| ≤ ‖r‖`), **Lemma 3.2 / Thm 3.8
  (Kato–Temple) / Cor 3.4 / Thm 3.9** (quadratic residual bounds for Rayleigh quotients and the
  `sin θ ≤ ‖r‖/δ` eigenvector bound), **Prop 3.4 / Thm 3.10** (backward error: `min‖E‖₂ = ‖r‖₂`, KPJ
  two-sided `max{‖r‖,‖s‖}`), **Defs 3.1–3.2, Prop 3.5** (condition numbers `1/cos θ(u,w)`,
  `‖S(λ)(I−P)‖`, invariant subspaces via Sylvester operators), **Thm 3.11–3.12** (Gershgorin + "`m`
  isolated discs contain `m` eigenvalues" by continuity), **Prop 3.6** (Kato–Temple for diagonal
  entries: quadratic in the off-diagonal norm, sharper than Gershgorin), **Def 3.3 / Prop 3.7**
  (pseudospectra ⇔ backward errors), **Thms 3.4–3.5, Prop 3.3** (analytic perturbation, Hölder
  exponent `1/ℓ`), and the Ritz-side bounds **Cor 4.1, Thms 4.5–4.6, Prop 4.5** (Theme 5).
- **Most general natural statement.**
  - *Min–max / Courant / Weyl*: self-adjoint operators on a FDIPS (Mathlib: `LinearMap.IsSymmetric`
    with `eigenvalues` via `LinearMap.IsSymmetric.eigenvectorBasis`); Courant–Fischer in either
    dimension convention, Weyl `|λⱼ(A) − λⱼ(B)| ≤ ‖A − B‖_op`, interlacing for compressions
    (Saad Cor 4.1) — one family of lemmas. Extends to compact self-adjoint operators on Hilbert spaces
    (eigenvalues of finite multiplicity) but the backbone needs the finite-dim version.
  - *Bauer–Fike*: `A` diagonalizable on a finite-dim normed space, any operator norm induced by a vector
    norm for which diagonal matrices have norm `max|dᵢ|` (all `ℓᵖ` norms): `dist(λ̃, σ(A)) ≤ κ(X)‖r‖`.
    Saad's Thm 3.7 (Jordan) is the non-diagonalizable extension; its natural form is
    `‖(A − λ̃)⁻¹‖ ≤ κ(X) max_i Σ_{j<ℓᵢ} |λᵢ − λ̃|^{−j−1}`.
  - *Hermitian residual / Kato–Temple / eigenvector bounds*: self-adjoint operator on a Hilbert space
    with an isolated eigenvalue; the FDIPS proofs (orthonormal eigenbasis) transfer via the spectral
    theorem, so state them for FDIPS first with hypotheses only on `σ(A)` (gap `δ`), not on `n`.
    Kress Cor 7.6 is Weyl applied to `B = diag(A)`; Saad Prop 3.6 is Kato–Temple applied to `eᵢ`; both
    are corollaries once the abstract versions exist.
  - *Gershgorin*: `Matrix n n ℂ` (entrywise; two proofs — Kress's `‖x‖_∞` component argument, Saad's
    `‖·‖_∞ < 1 ⇒ I + C` invertible, the latter reusable for block-Gershgorin). The disc-counting
    Thm 3.12 needs continuity of eigenvalues in the entries (roots of polynomials) — nontrivial in
    Lean, lower priority.
  - *Backward error / pseudospectra*: Prop 3.4 is just `‖ruᴴ‖₂ = ‖r‖₂` — trivial in FDIPS; Prop 3.7's
    equivalences are Hilbert-space level (`σ_min(A − z) = 1/‖(A−z)⁻¹‖`).

### Theme 8 — Banach fixed-point theorem with error estimates; Newton's method

- **Kress.** **Thm 3.45** (Banach), **Thm 3.46** (a priori `qⁿ/(1−q)‖x₁ − x₀‖`, a posteriori
  `q/(1−q)‖xₙ − xₙ₋₁‖`), **Thm 3.48** (linear case, Neumann series), Problems 3.17–3.18 (`Aᵐ` contraction;
  weak contraction on compact sets), **Thm 6.1/6.2** (1-D, `sup|f'| < 1`; local), **Thm 6.7** (mean
  value inequality), **Thm 6.8/6.9** (ℝⁿ, `sup‖f'‖ < 1` in some norm; local), **Thm 6.14**
  (Newton–Kantorovich-type semi-local theorem with `h = αβγ < ½`, unique zero in `B[x₀,2α]`, error
  `α q^{2^ν−1}/(1−q^{2^ν})`), **Cor 6.15/6.16** (local convergence for `C²`, simple zero), **Thm 6.20**
  (quadratic), **Thm 6.21** (simplified Newton linear), secant (6.9), Problem 6.15 (Newton–Schulz
  `A_{ν+1} = A_ν(2I − AA_ν)` quadratic for `A⁻¹`), Problem 6.14 (multiple zeros), **Thm 10.5 / Cor 10.6**
  (Picard–Lindelöf as Banach on `C[x₀−a,x₀+a]` with a posteriori bound), Thm 4.2/4.3 (Jacobi/GS error
  bounds are Thm 3.48's), Thm 12.6/12.10 (Neumann series for stability).
- **Saad.** No fixed-point theorem as such. Related: §3.5 stationary iteration `x = Gx + f` (linear
  contraction when `‖G‖ < 1`; only `ρ(G) < 1` discussed), Alg 4.3 RQI (cubic convergence *cited*),
  §8.4.2 Jacobi–Davidson as Newton on `(A − θI)u = 0, (u,u) = 1` (Olsen's method; Prop 8.2 solves the
  singular correction equation), Thm 8.1 (Davidson monotone convergence — a compactness argument, not
  a contraction), Kress Problem 6.18 / 7.19 (Newton for the eigenproblem) and Saad §8.4 describe the
  same iteration.
- **Most general natural statement.** Banach FPT on complete metric spaces with both estimates —
  already in Mathlib (`ContractingWith.fixedPoint`, `ContractingWith.apriori_dist_iterate_fixedPoint_le`,
  `ContractingWith.aposteriori_dist_iterate_fixedPoint_le`); Kress 3.46 is a direct specialisation and
  Kress 3.48 = Banach applied to the affine map `x ↦ Bx + z` plus `‖(I−B)⁻¹‖ ≤ 1/(1−‖B‖)`. Newton:
  the natural home is a Banach space with Fréchet derivative — Kress's Thm 6.14 proof uses only the
  integral mean-value bound (6.1)/(6.5), which holds for `C¹` maps on convex open sets of Banach spaces
  (Mathlib: `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`), the Neumann-series lemma for
  invertibility of `f'(x)` (Cor 6.15), and a contraction argument for uniqueness; so the theorem should
  be stated as Newton–Kantorovich in Banach spaces (`h = αβγ ≤ ½`, Kress uses `< ½`, with the
  Kantorovich radius `r = (1 − √(1−2h))/(βγ)`; Kress's `r = 2α` is the simpler but slightly weaker
  variant). Quadratic convergence (Thm 6.20) and the simplified-Newton linear rate (Thm 6.21) are
  corollaries. For the eigenvalue backbone, Newton enters through RQI and Jacobi–Davidson; the
  finite-dim Newton–Kantorovich theorem plus Bauer–Fike-type conditioning is enough.

### Theme 9 — Best approximation, orthogonal projection, Lax–Milgram, Céa

- **Kress.** **Def 3.49, Thm 3.50** (existence in finite-dim subspaces of any NS), **Thm 3.51**
  (pre-Hilbert: characterisation `w − v ⟂ U`, uniqueness), **Thm 3.52** (complete subspace: existence,
  `P` linear, `P² = P`, `‖P‖ = 1`), **Cor 3.53** (normal equations), **Cor 3.54** (`Pw = Σ(w,uₖ)uₖ`),
  Problem 3.20 (Fourier partial sums), **Thm 5.5** (minimum-norm least squares / pseudo-inverse),
  **Thm 5.9** (Tikhonov = penalised least squares, same proof pattern as 3.51), **Thm 11.11** (Riesz),
  **Thm 11.13** (Lax–Milgram, operator form, `‖A⁻¹‖ ≤ 1/c`), **Thm 11.15 / Cor 11.16** (form version),
  **Thm 11.17** (Céa, `M = ‖A‖/c`), Thms 11.27–11.28 (FEM error via Céa + interpolation + Nitsche).
- **Saad.** **Thm 3.1** (orthogonal projector minimises distance; `θ(x,S) = θ(x,Px)`), Prop 3.1
  (orthogonal ⇔ Hermitian, `P = VVᴴ`), oblique `P = VWᴴ` (3.11), gap `ω(M₁,M₂)` and P-3.8–P-3.12
  (canonical angles, `ω = sin θ_max`), **Thm 6.1** (optimal characteristic polynomial: "`p̄ₘ(A)v ⟂ Kₘ` ⇔
  normal equations for `min‖Aᵐv − s(A)v‖`" — Kress Thm 3.51/Cor 3.53 verbatim), **Lemma 6.1/6.2**
  (`‖(I−Pₘ)u‖ = min_{q}‖u − q(A)v‖` — Thm 3.1 on a Krylov subspace), **Thm 5.2**'s use of
  `‖(I−Pₖ)uᵢ‖ = min_{y∈Sₖ}‖y − uᵢ‖`, **§7.6 Thms 7.2–7.3** (best `L²(w)` polynomial under a point
  constraint = kernel polynomial `Kₖ(λ₁,·)/Kₖ(λ₁,λ₁)` — the Cor 3.54 formula in an orthonormal
  polynomial basis), Prop 7.1 (Gram matrix). No Lax–Milgram/Céa (eigenproblems are not coercive
  equations), but Theme 5 shows Thm 4.3 is its eigen-analogue.
- **Most general natural statement.** Hilbert-space projection theorem (closed convex sets ⇒ unique
  nearest point; closed subspaces ⇒ orthogonal projection, self-adjoint idempotent of norm `≤ 1`),
  normal equations for finite-dim subspaces, Riesz, Lax–Milgram — all in Mathlib
  (`orthogonalProjection`, `norm_eq_iInf_iff_real_inner_eq_zero`, `InnerProductSpace.toDual`,
  `IsCoercive.continuousLinearEquivOfBilin`). Missing and cheap: Céa in the form "`A` bounded,
  coercive (`Re⟨Ax,x⟩ ≥ c‖x‖²`), `K` closed subspace, `P_K` the orthogonal projection; then
  `P_KA|_K` is invertible with `‖(P_KA|_K)⁻¹‖ ≤ 1/c` and `‖x_K − x‖ ≤ (‖A‖/c) dist(x,K)`" (plus the
  self-adjoint improvement `√(‖A‖/c)`). Saad's Thm 3.1 is the angle-formulation of the projection
  theorem; the gap/canonical-angle material (P-3.9–3.12) is the natural FDIPS package ("principal
  angles = arccos of singular values of `VᴴW`") and is needed for subspace-iteration convergence
  (Theme 10) and Thm 4.6. Oblique projectors: natural statement `X = K ⊕ L^⟂` ⇒ unique idempotent with
  range `K`, kernel `L^⟂`, `‖Q‖ ≥ 1`, `Q* = ` projector onto `L` along `K^⟂` (P-3.1).

### Theme 10 — Power method, inverse iteration, subspace iteration, QR algorithm

- **Saad.** **Thm 4.1** (power method; hypotheses: unique dominant eigenvalue, semi-simple,
  `P₁v₀ ≠ 0`; proof via spectral projectors + nilpotents; rate `|λ₂/λ₁|`), shifted power method,
  inverse iteration (rate `|λ₁−σ|/|λ₂−σ|`), RQI (cubic, cited), Wielandt/Schur–Wielandt deflation
  (**Thm 4.2, Props 4.1–4.2**, Alg 4.4), **Thm 5.1** (subspace iteration converges column-wise to Schur
  vectors under `|λᵢ| > |λᵢ₊₁|`, `i ≤ m`, and `rank Pᵢ[x₁..xᵢ] = i`; no diagonalizability), **Thm 5.2**
  (angle bound `‖(I−Pₖ)uᵢ‖ ≤ ‖uᵢ − sᵢ‖(|λ_{m+1}/λᵢ| + εₖ)ᵏ` via Gelfand), Alg 5.3 (subspace iteration +
  Rayleigh–Ritz = "orthogonal iteration with projection"), ch. 7 Alg 7.2 (shifted QR on `Hₘ` inside
  IRA; the QR algorithm itself is used as a black box), Chebyshev acceleration (§5.3.3, §7.5).
- **Kress.** Power method (unnumbered, diagonalizable, `|λ₁| > |λ₂|`, `a₁ ≠ 0`; Problem 7.11 rate),
  **Lemma 7.18** (subspace iteration: `‖P_{AᵛS} − P_T‖ ≤ M|λ_{m+1}/λₘ|ᵛ`, diagonalizable, `S ∩ U = 0`),
  **Thm 7.19** (orthogonal/simultaneous iteration: `Q_ν*AQ_ν` → upper triangular with ordered `λⱼ`,
  needs all `|λₘ| > |λ_{m+1}|` and `Sₘ ∩ Uₘ = 0`), **Thm 7.20** (QR algorithm = simultaneous iteration
  from the canonical basis; condition ⇔ `X⁻¹` has an LR factorisation), **Thm 7.14** (Jacobi's method,
  `N(A_ν) ≤ qᵛN(A)`), Thm 7.22 (Hessenberg reduction), Problem 7.16 (Hessenberg preserved by QR),
  Thm 7.25 (Hyman), shifts/deflation discussed informally.
- **Most general natural statement.**
  - *Power method*: bounded operator `A` on a Banach space with an isolated dominant eigenvalue `λ₁`
    (`|λ₁| > sup{|z| : z ∈ σ(A)∖{λ₁}}`) that is semi-simple, `P₁` its Riesz projection; then for
    `P₁v₀ ≠ 0`, `λ₁^{−k}Aᵏv₀ → P₁v₀` with rate `ρ(A|_{Ran(I−P₁)})/|λ₁| + ε`. Saad's proof *is* this proof
    (Thm 1.3 = Riesz decomposition, Cor 1.1 = Gelfand); Kress's diagonalizable version is the
    special case with an eigenbasis. In FDIPS the clean statement: `sin θ(Aᵏv₀, u₁) ≤ C(|λ₂/λ₁| + ε)ᵏ`,
    Rayleigh quotient error `O(rᵏ)` (Hermitian: `O(r^{2k})`).
  - *Subspace / orthogonal iteration*: the invariant statement is about subspaces, not bases:
    `Sₖ = AᵏS₀` converges in gap to the dominant `m`-dimensional invariant subspace `Ran Pₘ` (spectral
    projector of `λ₁..λₘ`) with rate `|λ_{m+1}/λₘ| + ε`, provided `Pₘ|_{S₀}` is injective
    (Saad: `det(UᴴS₀) ≠ 0`; Kress: `S ∩ U = {0}` — the same condition). This requires only
    `|λₘ| > |λ_{m+1}|` and works for any square matrix over ℂ (Saad Thm 5.2, proof via
    `A|_W` and Gelfand); Kress Lemma 7.18 adds diagonalizability and gets the clean `Mrᵛ` (no `ε`),
    which Saad recovers in (5.10)–(5.11). Column-wise convergence to Schur vectors (Saad 5.1) and the
    triangularisation `Q_ν*AQ_ν → R` (Kress 7.19) are the same theorem applied to the nested family
    `S₀^{(1)} ⊂ … ⊂ S₀^{(n−1)}`, Kress requiring *all* moduli distinct, Saad only the first `m`.
    Kress 7.20 then identifies the QR algorithm with orthogonal iteration on the canonical flag —
    a purely algebraic lemma (`A_{ν+1} = Q̃_ν*A_νQ̃_ν`, `Q_ν = Q̃₁⋯Q̃_ν`, `Aᵛ = Q_νR_ν⋯R₁`) that should be
    formalised separately from the convergence analysis.
  - So the backbone needs: (i) Riesz/spectral projectors in finite dimension (Saad 1.3/3.3),
    (ii) Gelfand (Theme 1), (iii) gap/canonical angles between subspaces (Theme 9), (iv) one
    subspace-iteration theorem in Saad's generality, from which power method (`m = 1`), Kress 7.18/7.19,
    and the QR algorithm (7.20) follow; Jacobi's method (Kress 7.14) is an independent Frobenius-norm
    descent argument on real symmetric matrices, orthogonal to the Krylov core.

### Overall assessment for the formalization backbone

1. The two books overlap in *substance* only on Themes 1, 3, 7, 9, 10 and — crucially — the overlaps
   are exactly the places where the natural generality is a Hilbert/Banach space or a self-adjoint
   operator on a FDIPS, never matrix entries: Gelfand + Neumann series (Banach algebra), projection
   theorem + Céa + oblique projectors (Hilbert), min–max/Weyl/Kato–Temple (self-adjoint on FDIPS),
   Riesz projections + subspace iteration (finite-dim over ℂ with Schur form).
2. Kress supplies the *analytic scaffolding* (Banach FPT with estimates, Neumann series, projection
   theorem, Lax–Milgram/Céa, perturbation Thm 5.3, Riesz theory) that Saad uses tacitly; Saad supplies
   the *spectral-approximation core* (Krylov subspaces, Petrov–Galerkin compressions, Chebyshev
   min–max, Lanczos/Arnoldi bounds, resolvent/spectral projectors) that Kress lacks entirely.
3. The genuinely entrywise material (Kress ch. 4 dominance/SOR/Young, Gershgorin, Jacobi's method) is
   self-contained and can be built on `Matrix n n ℂ` later; Ostrowski–Reich should nevertheless be
   proved in the operator form `M + Mᴴ − A ≻ 0`.
4. The single most valuable shared abstraction is the *compression `A_K = QA|_K` of an operator to a
   trial subspace along a test subspace* (Theme 5), with the two error constants `‖A‖/c` (Céa) and
   `γ = ‖QA(I−P_K)‖` (Saad 4.3/4.7) and the interlacing/monotonicity in the self-adjoint case; Krylov
   methods for linear systems and for eigenvalues are then both "compression to `Kₘ(A,v)`" plus the
   Chebyshev extremal theorem (Theme 6).
