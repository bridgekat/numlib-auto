# Atkinson & Han, *Theoretical Numerical Analysis: A Functional Analysis Framework* (3rd ed., Springer TAM 39, 2009) — theorem inventory for a Lean 4 / Mathlib "backbone" library

Source: pdftotext dump of the book (OCR readable for prose, garbled for
formulas). Statements below are reconstructed from the text plus knowledge of
the book; anything not reconstructed with confidence is tagged `[uncertain]`.
Book numbering (Theorem 2.3.5 etc.) is used everywhere so the planner can
cross-reference.

## Conventions used in this file

* `K` = scalar field, `R` or `C`. `V, W` normed spaces; `||.||` norm; `(.,.)`
  inner product; `<.,.>` duality pairing `V' x V`.
* `L(V,W)` = bounded (= continuous) linear operators with the operator norm;
  `L(V) = L(V,V)`; `V' = L(V,K)` the dual.
* `N(T)` null space, `R(T)` range, `D(T)` domain.
* "Banach" = complete normed; "Hilbert" = complete inner product space.
* "V-elliptic" (= coercive = strongly positive): `a(v,v) >= alpha ||v||^2` for
  all `v`, some `alpha > 0`. "Bounded bilinear": `|a(u,v)| <= M ||u|| ||v||`.
* `lambda - K` abbreviates `lambda*I - K`.
* Proof-source tags: **[proved]** = proof in book; **[quoted]** = stated
  without proof (reference given); **[exercise]** = left to reader.

Global remark on the book's style: almost every "numerical analysis" theorem is
an *explicit-constant* corollary of one of five functional-analytic engines:
(E1) completeness / Cauchy sequences; (E2) the geometric series theorem and its
perturbation corollary; (E3) Baire-category results (open mapping, uniform
boundedness); (E4) Hahn–Banach / Riesz representation; (E5) the projection
theorem onto closed convex sets in Hilbert space. The Banach fixed-point theorem
(E1 again) and weak sequential compactness in reflexive spaces supply the
nonlinear results.

---

## 1. Chapter 1 — Linear Spaces (only 1.1–1.3, 1.6; brief)

Purpose here: record which standard facts are invoked later.

### 1.1 Linear spaces
* **Def 1.1.1** linear space over `K`; **1.1.3** subspace; **1.1.5** linear
  (in)dependence; **1.1.8** span; **1.1.9** finite-dimensional; **Thm 1.1.10**
  every basis of a finite-dimensional space has the same cardinality [quoted];
  **1.1.13** linear map; **1.1.14** isomorphism; **1.1.16** Cartesian product
  `U x V`.

### 1.2 Normed spaces
* **Def 1.2.1** norm; **1.2.2** semi-norm. **Ex 1.2.3–1.2.5**: `R^d` with
  `p`-norms, `l^p`, `C[a,b]` with max norm, `C^m[a,b]`, `L^p`.
* **Def 1.2.6–1.2.8** balls, open/closed sets, convergence. **Def 1.2.9**
  continuity (sequential). **Prop 1.2.10** the norm is continuous (reverse
  triangle inequality) [proved].
* **Def 1.2.12** equivalent norms. **Thm 1.2.14** on a finite-dimensional
  space all norms are equivalent [quoted].
* **Def 1.2.17** series; **1.2.18** dense subset; **1.2.20** (Schauder) basis
  of an infinite-dimensional normed space.
* **Def 1.2.21** Cauchy sequence. **Prop 1.2.23** a Cauchy sequence with a
  convergent subsequence converges to the same limit [proved].
* **Def 1.2.24** complete normed space = Banach space.
* **Thm 1.2.25 (Completion)** every normed space `V` has a completion `W`
  (isometric embedding with dense image), unique up to isometric isomorphism
  [quoted]. Used in 2.4.1 and 6.2.
* **Thm 1.2.26** Lebesgue dominated convergence; **Thm 1.2.27** Fubini
  [quoted] (used in 8.8 and in integral-operator examples).
* **Ex 1.2.28** `C^m[a,b]` Banach; `W^{m,p}(a,b)` defined as the completion
  of `C^m[a,b]` under the Sobolev norm.

### 1.3 Inner product spaces
* **Def 1.3.1** inner product (`K = R` or `C`).
* **Thm 1.3.2 (Cauchy–Schwarz)** `|(u,v)|^2 <= (u,u)(v,v)`, equality iff
  linearly dependent [proved, real case].
* **Prop 1.3.3** inner product is jointly continuous [proved].
* Polarization identities (1.3.1)/(1.3.2): the inner product is determined by
  the norm.
* **Thm 1.3.4** a norm is induced by an inner product iff the parallelogram law
  `||u+v||^2 + ||u-v||^2 = 2||u||^2 + 2||v||^2` holds [proved, real case].
* **Def 1.3.5** Hilbert space. **Ex 1.3.6** `C^d`, `l^2`, `L^2(Omega)`,
  weighted `L^2_w`. **Ex 1.3.7** `H^m(a,b) = W^{m,2}(a,b)`.
* **Def 1.3.8–1.3.10** orthogonality, orthogonal complement `U^perp` (always a
  closed subspace), orthonormal system / orthonormal basis.
* **Thm 1.3.11** `{v_j}` orthonormal in a Hilbert space `V`: (a) Bessel
  `sum |(v,v_j)|^2 <= ||v||^2`; (b) `sum (v,v_j) v_j` converges; (c) if
  `v = sum a_j v_j` then `a_j = (v,v_j)`; (d) `sum a_j v_j` converges iff
  `sum |a_j|^2 < inf` [proved; completeness used in (b),(d)].
* **Thm 1.3.12** for an orthonormal system in a Hilbert space TFAE: (a) it is
  an orthonormal basis; (b) `(u,v) = sum (u,v_j) conj((v,v_j))`; (c) Parseval
  `||v||^2 = sum |(v,v_j)|^2`; (d) its span is dense; (e) `(v,v_j)=0` for all
  `j` implies `v=0` [proved].
* **Thm 1.3.13** `{1/sqrt(2 pi), cos(jx)/sqrt(pi), sin(jx)/sqrt(pi)}` is an
  orthonormal basis of `L^2(-pi,pi)` [proved via Cor 3.1.4 + density of `C`].
* **Thm 1.3.16 (Gram–Schmidt)** linearly independent `{w_n}` in an inner
  product space yield an orthonormal `{v_n}` with equal finite spans [proved].
  Ex 1.3.17: Legendre polynomials.

### 1.6 Compact sets
* **Def 1.6.1** compact (open covers) = sequentially compact (in normed
  spaces); precompact = closure compact. A compact set is closed and bounded.
* **Thm 1.6.2 (Heine–Borel)** in a finite-dimensional normed space, compact
  iff closed and bounded; moreover a normed space is finite-dimensional iff
  every closed bounded set is compact [quoted].
* **Thm 1.6.3 (Arzelà–Ascoli)** `S subset C(D)`, `D subset R^d` closed
  bounded, `S` uniformly bounded and equicontinuous ⇒ `S` precompact in
  `C(D)` [quoted]. Used for compactness of integral operators (2.8.1).

---

## 2. Chapter 2 — Linear Operators on Normed Spaces (complete inventory)

### 2.1 Operators
* Domain/range/null set; **Def 2.1.1** injective/surjective/bijective,
  inverse; **Def 2.1.6** continuity (sequential, on `D(T)`) and boundedness
  (`||v|| <= r ⇒ ||T v|| <= R`, i.e. bounded sets go to bounded sets) for
  *possibly nonlinear* `T`.
* Ex 2.1.2–2.1.5: identity; matrices (rank conditions); `d/dx` on
  `C^1[0,1] ⊂ C[0,1]` (surjective, not injective); `v ↦ (v', v(0))` is a
  bijection `C^1[0,1] → C[0,1] x R`. Ex 2.1.7: `d/dx` is unbounded for the sup
  norm on `C^1`, bounded for the `C^1` norm.

### 2.2 Continuous linear operators
* **Def 2.2.1** linear operator.
* **Prop 2.2.2** linear `L: V → W` (normed) is continuous everywhere iff
  continuous at 0 [proved].
* **Prop 2.2.3** linear `L` is bounded iff `∃ γ ≥ 0: ||Lv|| ≤ γ ||v||` [proved].
* **Thm 2.2.4** linear `L` continuous iff bounded; then Lipschitz with
  constant `||L||` (2.2.3) [proved].
* Operator norm (2.2.4): `||L|| = sup_{v≠0} ||Lv||/||v|| = sup_{||v||≤1} ||Lv||
  = sup_{||v||=1} ||Lv|| = (1/r) sup_{||v||≤r} ||Lv||`; `||Lv|| ≤ ||L|| ||v||`.
* **Thm 2.2.5** `L(V,W)` is a normed space with the operator norm [exercise].
* **Thm 2.2.6** composition: `||L_2 L_1|| ≤ ||L_1|| ||L_2||`; hence
  `||L^n|| ≤ ||L||^n` [proved].
* `L` injective iff `N(L) = {0}`.
* Ex 2.2.7 `||I|| = 1`; Ex 2.2.8 matrix operator norms (`∞`: max row sum; `1`:
  max column sum; `2`: `sqrt(r(A*A))`); Ex 2.2.9 integral operator
  `Kv(x) = ∫_a^b k(x,y) v(y) dy`, `k ∈ C([a,b]^2)`, on `C[a,b]`: bounded with
  `||K|| = max_x ∫_a^b |k(x,y)| dy` (2.2.8) [exercise; used constantly later
  for Lebesgue constants].
* **Thm 2.2.10** `V` normed, `W` Banach ⇒ `L(V,W)` Banach [proved: pointwise
  Cauchy ⇒ pointwise limit, which is linear and bounded, and
  `||L_n − L|| ≤ ε_n → 0`]. Uses only completeness of `W`.

### 2.3 The geometric series theorem and its variants
* **Thm 2.3.1 (Geometric series / Neumann series)** `V` Banach, `L ∈ L(V)`,
  `||L|| < 1`. Then `I − L` is a bijection of `V`, `(I−L)^{-1} ∈ L(V)`,
  `(I−L)^{-1} = Σ_{n≥0} L^n` (convergent in `L(V)`), and
  `||(I−L)^{-1}|| ≤ 1/(1 − ||L||)` (2.3.2) [proved]. Proof: partial sums
  `M_n = Σ_{i≤n} L^i` are Cauchy in `L(V)` since `||M_{n+p} − M_n|| ≤
  ||L||^{n+1}/(1−||L||)` (2.3.3); `L(V)` complete (2.2.10);
  `(I−L)M_n = M_n(I−L) = I − L^{n+1} → I`.
  Consequences noted in text: unique solvability of `(I−L)u = f`; continuous
  dependence `||u_1 − u_2|| ≤ ||f_1 − f_2||/(1−||L||)`; truncated-series
  approximation (2.3.5) `u_n = Σ_{j≤n} L^j f → u`; operator functions
  `f(L) = Σ a_n L^n` when `||L|| < ρ` (radius of convergence): `e^L`, `sin L`,
  `arctan L`.
  *Generality*: holds in any unital Banach algebra (Mathlib states it that way).
* **Ex 2.3.2** second-kind Fredholm equation `λu − Ku = f` on `C[a,b]`: unique
  solvability if `||K|| = max_x ∫|k(x,y)|dy < |λ|` (2.3.8), with
  `||(λ−K)^{-1}|| ≤ 1/(|λ| − ||K||)` and `||u|| ≤ ||f||/(|λ| − ||K||)`.
* **Cor 2.3.3** `V` Banach, `L ∈ L(V)`, `||L^m|| < 1` for some `m ≥ 1` ⇒ `I−L`
  bijective with bounded inverse and
  `||(I−L)^{-1}|| ≤ (Σ_{i=0}^{m−1} ||L||^i) / (1 − ||L^m||)` (2.3.11)
  [proved via `(I−L) Σ_{i<m} L^i = Σ_{i<m} L^i (I−L) = I − L^m` and
  Thm 2.3.1 applied to `L^m`].
* **Ex 2.3.4** Volterra operator `Lv(x) = ∫_0^x l(x,y)v(y)dy` on `C[0,B]`,
  `l` continuous, `M = max|l|`: iterated kernels satisfy
  `|l_k(x,y)| ≤ M^k (x−y)^{k−1}/(k−1)!`, so `||L^k|| ≤ M^k B^k/k! → 0` and
  Cor 2.3.3 applies for *every* kernel size (unconditional solvability of
  Volterra equations of the second kind).
* **Thm 2.3.5 (Perturbation theorem)** `V, W` normed, *at least one of them
  complete*; `L ∈ L(V,W)` with bounded inverse `L^{-1} ∈ L(W,V)`;
  `M ∈ L(V,W)` with `||M − L|| < 1/||L^{-1}||` (2.3.12). Then `M: V → W` is a
  bijection, `M^{-1} ∈ L(W,V)`, and
  (2.3.13) `||M^{-1}|| ≤ ||L^{-1}|| / (1 − ||L^{-1}|| ||L−M||)`;
  (2.3.14) `||L^{-1} − M^{-1}|| ≤ ||L^{-1}||^2 ||L−M|| / (1 − ||L^{-1}|| ||L−M||)`;
  (2.3.15) if `Lv_1 = w` and `Mv_2 = w` then
  `||v_1 − v_2|| ≤ ||M^{-1}|| ||(L−M)v_1||`.
  [proved]. Proof: factor `M = [I − (L−M)L^{-1}] L` (if `W` complete) or
  `M = L[I − L^{-1}(L−M)]` (if `V` complete), apply Thm 2.3.1 to the bracket;
  `L^{-1} − M^{-1} = M^{-1}(M−L)L^{-1}`;
  `v_1 − v_2 = (L^{-1} − M^{-1})w = M^{-1}(M−L)v_1`.
  Discussion (central for the backbone): for approximations `L_n → L`, (2.3.16)
  `||v − v_n|| ≤ ||L_n^{-1}|| ||(L − L_n)v||`: *consistency* (`(L−L_n)v → 0`)
  plus *stability* (`sup ||L_n^{-1}|| < ∞`) implies convergence — an a priori
  estimate; the mirrored use `||v − v_n|| ≤ ||M^{-1}|| ||(M − M_n) v_n||` is an
  a posteriori estimate.
  *Generality*: this is "the invertible elements of `L(V,W)` form an open set
  and inversion is locally Lipschitz"; valid in any Banach algebra.
* **Ex 2.3.6** `λu(x) − ∫_0^1 sin(xy)u(y)dy = f(x)`: compare with the
  degenerate kernel `xy` (solvable in closed form (2.3.20)) to enlarge the set
  of admissible `λ` beyond `|λ| > 1 − cos 1`.
* Exercises that are candidate backbone lemmas: 2.3.3 (`L + εM_ε` solvable and
  the iteration `u_{n+1} = L^{-1}(f − M u_n)` converges for small `ε`); 2.3.4
  (nilpotent `L` ⇒ `I−L` invertible, `(I−L)^{-1} = Σ_{i<m} L^i`); 2.3.7
  (`||I − L|| < 1` ⇒ `L^{-1} = Σ (I−L)^i`); 2.3.8 (Picard iteration
  `u_n = f + L u_{n−1}` with error bound `||L||^n ||u_0 − u||`); 2.3.10
  (`||M−L|| < 1/(2||L^{-1}||)` ⇒ the iteration `u_{n+1} = u_n + M^{-1}(f − L u_n)`
  converges to `L^{-1}f`; "preconditioned Richardson"); 2.3.9 (Green's
  function `k(x,y) = min(x,y)(1 − max(x,y))` for `−u'' = f`, and unique
  solvability of `−u'' + a(x)u = f` for `||a||_∞` small).

### 2.4 Some more results on linear operators
* **Thm 2.4.1 (Extension theorem)** `V` normed with completion `V̂`, `W`
  Banach, `L ∈ L(V,W)` ⇒ ∃! `L̂ ∈ L(V̂,W)` extending `L`, and `||L̂|| = ||L||`
  [proved: `L̂v = lim L v_n`; well-defined, linear, bounded, unique].
  Ex 2.4.2: extends `d/dx: C^1[0,1] → L^2` to `H^1(0,1) → L^2`.
  *Generality*: uniformly continuous maps from a dense subset into a complete
  metric space extend (Mathlib: `DenseInducing.extend`,
  `ContinuousLinearMap.extend`).
* **Thm 2.4.3 (Open mapping / bounded inverse)** `V, W` Banach, `L ∈ L(V,W)`
  bijective ⇒ `L^{-1} ∈ L(W,V)` [quoted; Baire category]. Discussion:
  stability `||v − v̂|| ≤ ||L^{-1}|| ||w − ŵ||`; relative error bound (2.4.1)
  `||v−v̂||/||v|| ≤ cond(L) ||w−ŵ||/||w||` with `cond(L) = ||L|| ||L^{-1}|| ≥ 1`
  (sharp, Ex 2.4.6); well-posed vs ill-posed (`L^{-1}` unbounded on `R(L)`).
* **Thm 2.4.4 (Principle of uniform boundedness)** `{L_n} ⊂ L(V,W)`, `V`
  Banach, `W` normed, `sup_n ||L_n v|| < ∞` for every `v ∈ V` ⇒
  `sup_n ||L_n|| < ∞` [quoted; Baire].
* **Thm 2.4.5 (Banach–Steinhaus)** `V` Banach, `W` normed, `L, L_n ∈ L(V,W)`,
  `V_0 ⊂ V` a dense subspace. Then `L_n v → L v` for all `v ∈ V` iff
  (a) `L_n v → Lv` for all `v ∈ V_0` and (b) `sup_n ||L_n|| < ∞`
  [proved: ⇒ by 2.4.4; ⇐ by an ε/3 argument]. *Generality*: a dense *subset*
  suffices in (a); `W` need not be complete.
* **2.4.4 Convergence of numerical quadratures** (no theorem number; the key
  "numerical-analysis flavoured" corollary of E3). Setting: `Lv = ∫_0^1 w v dx`,
  `w ≥ 0`, `w ∈ L^1`; quadrature functionals `L_n v = Σ_{i=0}^n w_i^{(n)}
  v(x_i^{(n)})` on `V = C[0,1]` (sup norm). Facts: (2.4.4)
  `||L_n||_{V'} = Σ_i |w_i^{(n)}|` [exercise 2.4.2]. **Statement**: if `L_n`
  has degree of precision `d(n) → ∞` (i.e. `L_n p = L p` for `p ∈ P_{d(n)}`)
  then `L_n v → Lv` for every `v ∈ C[0,1]` iff `sup_n Σ_i |w_i^{(n)}| < ∞`
  [proved: Banach–Steinhaus with `V_0` = polynomials, dense by Weierstrass
  3.1.1]. Corollary [exercise 2.4.3]: non-negative weights and `d(n) → ∞` ⇒
  convergence (then `Σ_i w_i = ∫ w` is bounded); Gaussian quadrature has
  positive weights. Ex 2.4.7: Newton–Cotes (uniform nodes) diverges for some
  `v`, hence `sup_n Σ|w_i^{(n)}| = ∞` while `Σ_i w_i^{(n)} = 1`. Ex 2.4.5:
  composite trapezoidal rule converges for all `v ∈ C[0,1]` (fixed precision,
  refined mesh). Ex 2.4.4: pointwise limit of bounded operators on a Banach
  space is bounded with `||L|| ≤ liminf ||L_n||`. Ex 2.4.1: two complete norms
  with `||.||_2 ≤ c||.||_1` are equivalent (open mapping).

### 2.5 Linear functionals
* `V' = L(V,K)` is always Banach (2.2.10). Ex 2.5.1: `(L^p(Ω))' = L^{p'}(Ω)`
  for `1 ≤ p < ∞`; `(L^∞)' ⊋ L^1`.
* **Thm 2.5.2 (Hahn–Banach, normed form)** `V_0 ⊂ V` subspace, `ℓ ∈ V_0'` ⇒
  ∃ extension `ℓ̂ ∈ V'` with `||ℓ̂|| = ||ℓ||` [quoted; follows from 2.5.5 with
  `p(v) = ||ℓ|| ||v||`, Ex 2.5.1]. Not unique unless `V_0` is dense.
  Ex 2.5.3: extension of point evaluation `[v] ↦ v(c)` from `C[0,1]` to
  `L^∞(0,1)` (norm 1), retaining order and continuity-point properties — used
  in analysis of numerical integral equations.
* **Def 2.5.4** sublinear functional (subadditive, positively homogeneous).
* **Thm 2.5.5 (Generalized Hahn–Banach)** `V` real linear space, `p: V → R`
  sublinear, `ℓ` linear on a subspace `V_0` with `ℓ ≤ p` on `V_0` ⇒ `ℓ` extends
  to `V` with `ℓ ≤ p` everywhere [quoted].
* **Cor 2.5.6** for `0 ≠ v ∈ V` ∃ `ℓ_v ∈ V'` with `||ℓ_v|| = 1`,
  `ℓ_v(v) = ||v||` [exercise]. Used in 2.7.2, 3.3.5, 5.3.11.
* **Cor 2.5.7** `||v|| = sup{|ℓ(v)| : ℓ ∈ V', ||ℓ|| = 1}` [proved].
* **Thm 2.5.8 (Riesz representation)** `V` real or complex Hilbert, `ℓ ∈ V'` ⇒
  ∃! `u ∈ V` with `ℓ(v) = (v,u)` for all `v`, and `||ℓ|| = ||u||` (2.5.6)
  [proved, real case; two existence proofs: (i) `V = N(ℓ) ⊕ N(ℓ)^⊥`
  (projection theorem, Sec. 3.6), `u = (ℓ(v_2)/||v_2||^2) v_2`; (ii) `u` =
  unique minimizer of `½||v||^2 − ℓ(v)` by Thm 3.3.12]. Ex 2.5.9: `(L^2)' =
  L^2`; in `H^1(a,b)` the representer of `v ↦ v(c)` solves `−u'' + u = δ_c`,
  `u(a)=u(b)=0`. Ex 2.5.4: `u = Σ_j ℓ(e_j) e_j` for an ONB `{e_j}`.

### 2.6 Adjoint operators (real Hilbert spaces in the text)
* Construction: `V, W` Hilbert, `L ∈ L(V,W)`; for each `w`, `v ↦ (Lv,w)` lies
  in `V'` with norm `≤ ||L|| ||w||`; Riesz gives `L* w` with
  `(Lv,w)_W = (v, L*w)_V` (2.6.1). Proved in text: `L*` linear, bounded,
  `||L*|| ≤ ||L||` (2.6.2), `(L*)* = L` (2.6.3), hence `||L*|| = ||L||`
  (2.6.4). Self-adjoint: `V = W`, `L* = L`. Ex 2.6.1: `(αL_1 + βL_2)* =
  αL_1* + βL_2*`, `(L_1L_2)* = L_2*L_1*`, `L** = L`.
* **Ex 2.6.1 (in text)** Hilbert–Schmidt integral operator on `L^2(a,b)`:
  `||K|| ≤ (∫∫|k|^2)^{1/2}`, `K*` has kernel `k(y,x)`; self-adjoint iff `k`
  symmetric.
* **Prop 2.6.2** real linear combinations of self-adjoint operators are
  self-adjoint [proved].
* **Prop 2.6.3** `L_1, L_2` self-adjoint ⇒ `L_1L_2` self-adjoint iff
  `L_1L_2 = L_2L_1` [proved].
* **Cor 2.6.4** `L` self-adjoint ⇒ `L^n` and `p(L)` (real polynomial) are
  self-adjoint.
* **Thm 2.6.5** `L ∈ L(V)` self-adjoint (real Hilbert) ⇒
  `||L|| = sup_{||v||=1} |(Lv,v)|` (2.6.5) [proved via the identity
  `(Lu,v) = ¼[(L(u+v),u+v) − (L(u−v),u−v)]` and the parallelogram law].
  Ex 2.6.3 asks for `|(Lu,v)| ≤ |||L||| ||u|| ||v||` with
  `|||L||| = sup_{||v||=1}|(Lv,v)|` for "general" `L` [uncertain: as stated
  this fails for a 90° rotation of `R^2`; read it as an exercise for
  self-adjoint `L`].
  *Generality*: complex Hilbert spaces (conjugate-linear adjoint); the norm
  formula holds for normal operators in the complex case.

### 2.7 Weak convergence and weak compactness
* **Def 2.7.1** `u_n ⇀ u` iff `ℓ(u_n) → ℓ(u)` for all `ℓ ∈ V'`. Strong ⇒ weak.
* **Prop 2.7.2** weakly convergent sequences are bounded [proved: canonical
  embedding `J: V → V''`, uniform boundedness on the Banach space `V'`, and
  Cor 2.5.7 (`||Jv|| = ||v||`)].
* Ex 2.7.3: `sin(nx) ⇀ 0` in `L^2(0,2π)` but not strongly (Riemann–Lebesgue).
* Bidual and canonical isometry `J` (uses Cor 2.5.6). **Def 2.7.4** reflexive
  iff `J(V) = V''`; reflexive ⇒ Banach; Hilbert ⇒ reflexive (Riesz).
* **Thm 2.7.5 (Eberlein–Šmulian, sequential form)** a Banach space is
  reflexive iff every bounded sequence has a weakly convergent subsequence
  [quoted]. `L^p`, `1 < p < ∞`, reflexive; `L^1` not (Dunford–Pettis /
  uniform integrability stated in prose).
* **Def 2.7.6** for operators: `L_n → L` in operator norm (the book calls this
  "strong" convergence!) vs pointwise `L_n v → Lv` for all `v` (called
  "weak-*" / pointwise). Ex 2.7.1: Riemann sums converge pointwise but not in
  norm to `∫`. Ex 2.7.2: `||u|| ≤ liminf ||u_n||` when `u_n ⇀ u`. Ex 2.7.3/
  2.7.4: in inner product spaces (more generally uniformly convex spaces)
  `u_n → u` iff `u_n ⇀ u` and `||u_n|| → ||u||` (Radon–Riesz); Hilbert and
  `L^p` (`1<p<∞`, Clarkson) are uniformly convex. Ex 2.7.5: `u(nx) ⇀ mean(u)`
  in `L^p`.

### 2.8 Compact linear operators
* **Def 2.8.1** `K: V → W` linear is compact iff `K(unit ball)` is precompact
  iff every bounded sequence `{v_n}` has `{Kv_n}` with a convergent
  subsequence. The book assumes `V, W` Banach when using compactness.
* **2.8.1 Compact integral operators on `C(D)`**, `D ⊂ R^d` closed bounded,
  `Kv(x) = ∫_D k(x,y)v(y)dy`. Under (A1) `ω(h) := sup_{|x−z|≤h} ∫_D |k(x,y) −
  k(z,y)|dy → 0` as `h → 0`, and (A2) `sup_x ∫_D |k(x,y)|dy < ∞`:
  `K: C(D) → C(D)` is bounded with `||K|| = max_x ∫|k(x,y)|dy` (2.8.6),
  `|Kv(x) − Kv(y)| ≤ ω(|x−y|)||v||_∞` (2.8.5), and `K` is compact
  (Arzelà–Ascoli) [proved]. Kernels satisfying (A1)–(A2): continuous kernels;
  `log|x−y|`; `|x−y|^{−β}`, `β<1`, on `[a,b]`; `|x−y|^{−β}`, `β<d`, on
  `D ⊂ R^d`; sums of products `h_i l_i` with `l_i` continuous and `h_i`
  satisfying (A1)–(A2) (Ex 2.8.2: `log|cos x − cos y|`).
* **Def 2.8.3** finite rank operator. **Prop 2.8.4** bounded finite-rank ⇒
  compact [proved: Heine–Borel in `R(K)`]. Ex 2.8.5: degenerate kernels
  `k = Σ_{i≤n} α_i(x)β_i(y)` give bounded finite-rank operators on `C[a,b]`.
* **Prop 2.8.6** composition of a bounded and a compact operator (either
  order) is compact [exercise].
* **Prop 2.8.7** `W` complete, `K_n` compact, `K_n → K` in operator norm ⇒ `K`
  compact [quoted]. Ex 2.8.8/2.8.9: continuous kernels and `|x−y|^{−β}` are
  norm limits of degenerate / continuous kernels ⇒ compact.
* **2.8.3 Integral operators on `L^2(a,b)`**: Hilbert–Schmidt kernels
  (`M = (∫∫|k|^2)^{1/2} < ∞`) give `||K|| ≤ M` (2.8.17) and compactness (norm
  limit of degenerate kernels) [proved/sketched]; `|x−y|^{−β}` with
  `½ ≤ β < 1` is still compact on `L^2` but not Hilbert–Schmidt [quoted].
* **Thm 2.8.10 (Fredholm alternative)** `V` Banach, `K: V → V` compact,
  `λ ≠ 0`. Then `(λ − K)u = f` has a unique solution `u ∈ V` for every
  `f ∈ V` iff the homogeneous equation `(λ−K)v = 0` has only `v = 0`; in that
  case `(λ−K)^{-1} ∈ L(V)` [proved for `K` a norm-limit of bounded finite-rank
  operators; general case quoted (Kress, Conway)]. Proof: (a) `K` finite
  rank with `R(K) = span{φ_1..φ_n}`: `u = (f + Σ c_i φ_i)/λ`, and
  `(λ−K)u = f` is equivalent (solution-for-solution) to the `n×n` system
  (2.8.23) `λ c_i − Σ_j a_ij c_j = γ_i`; uniqueness for the homogeneous
  system ⇒ existence; `(λ−K)^{-1}` bounded by the open mapping theorem (2.4.3).
  (b) general: choose `K_m` finite rank with `||K − K_m|| < |λ|` (2.8.25);
  `Q_m := [λ − (K − K_m)]^{-1}` exists with `||Q_m|| ≤ 1/(|λ| − ||K − K_m||)`
  by the geometric series theorem; then `(λ−K)u = f` ⟺
  `u − Q_m K_m u = Q_m f` with `Q_m K_m` bounded finite rank; apply (a).
  **Book's remark (important generalization)**: the proof needs only *one*
  operator `K_m` that is *compact* (not necessarily finite rank) with
  `||K − K_m|| < |λ|`. Hence the alternative holds for any bounded `K` whose
  distance to the compact operators is `< |λ|` (i.e. `|λ|` exceeds the
  essential norm of `K`).
* **Def 2.8.11** eigenvalue / eigenvector.
* **Thm 2.8.12 (Riesz–Schauder theory)** `V` Banach, `K` compact: (1) the
  eigenvalues form a discrete subset of `C` with `0` the only possible
  accumulation point; (2) each nonzero eigenvalue has finitely many linearly
  independent eigenvectors; (3) each nonzero eigenvalue `λ` has finite index
  (ascent) `ν(λ) ≥ 1`: `N(λ−K) ⊊ N((λ−K)^2) ⊊ … ⊊ N((λ−K)^ν) = N((λ−K)^{ν+1})`,
  with `N((λ−K)^ν)` finite-dimensional (generalized eigenvectors); (4) for
  `λ ≠ 0`, `R(λ−K)` is closed; (5) `V = N((λ−K)^ν) ⊕ R((λ−K)^ν)`, both
  `K`-invariant; (6) Thm 2.8.10 and (1)–(5) remain true if merely `K^m` is
  compact for some `m > 1` [quoted].
* **Lemma 2.8.13** `V` complex Hilbert, `K` compact ⇒ `K*` compact [quoted].
* **Thm 2.8.14** `V` complex Hilbert, `K` compact, `λ ≠ 0` eigenvalue of `K`:
  (1) `conj(λ)` is an eigenvalue of `K*` and `dim N(λ−K) = dim N(conj λ − K*)`;
  (2) `(λ−K)u = f` is solvable iff `(f,v) = 0` for all `v ∈ N(conj λ − K*)`,
  i.e. `R(λ−K) = N(conj λ − K*)^⊥` and `V = N(conj λ − K*) ⊕ R(λ−K)` (2.8.30)
  [quoted].
* **Thm 2.8.15 (Spectral theorem, compact self-adjoint)** `V` complex Hilbert,
  `K` compact self-adjoint: all eigenvalues are real with index 1; the
  eigenvectors can be chosen orthonormal; ordering nonzero eigenvalues
  `|λ_1| ≥ |λ_2| ≥ … > 0` with multiplicity, `Ku_i = λ_i u_i`,
  `(u_i,u_j) = δ_ij`, and `{u_i}` is an orthonormal basis of `closure(R(K))`
  [quoted]. Ex 2.8.16: single-layer operator on the unit sphere,
  eigenfunctions = spherical harmonics, eigenvalues `4π/(2k+1)`.
  *Generality*: 2.8.13–2.8.15 hold verbatim in real Hilbert spaces; this is
  the form used in 5.6 (`A = I − K`).
* Ex 2.8.5: condition number of `λ − K` for `k = e^{x−y}`; Ex 2.8.7: the Abel
  operator has eigenfunctions `x^λ` for every `λ ≥ 0` ⇒ not compact.

### 2.9 The resolvent operator
* **Def 2.9.1** `V` complex Banach, `L ∈ L(V)`: resolvent set
  `ρ(L) = {λ ∈ C : (λ−L)^{-1} ∈ L(V)}`, resolvent `R(λ) = (λ−L)^{-1}`, spectrum
  `σ(L) = C \ ρ(L)`. `{|λ| > ||L||} ⊂ ρ(L)` (geometric series).
* **Lemma 2.9.2** `ρ(L)` is open (so `σ(L)` is closed); for
  `|λ − λ_0| < 1/||R(λ_0)||` one has `λ ∈ ρ(L)` and
  `||R(λ) − R(λ_0)|| ≤ |λ−λ_0| ||R(λ_0)||^2 / (1 − |λ−λ_0| ||R(λ_0)||)` (2.9.2),
  so `R` is continuous [proved via Thm 2.3.5]. Classification: point /
  continuous / residual spectrum; for compact `L` on infinite-dimensional
  `V`, `0 ∈ σ(L)`, and if `0` is not an eigenvalue then `L^{-1}` is unbounded
  on `R(L)` (ill-posed first-kind equations).
* **2.9.1 `R(λ)` is holomorphic**: (2.9.3) `R(λ) = Σ_k (−1)^k (λ−λ_0)^k
  R(λ_0)^{k+1}` for `|λ−λ_0| < 1/||R(λ_0)||` [exercise 2.9.3]. Riesz–Dunford
  functional calculus (2.9.4) `g(L) = (1/2πi) ∮_Γ (μ−L)^{-1} g(μ) dμ` for `g`
  analytic on an open set containing `σ(L)`, `Γ ⊂ ρ(L)` piecewise smooth.
* **Thm 2.9.3** `f, g ∈ F(L)`: (a) `(fg)(L) = f(L)g(L)`; (b) if `f = Σ a_n λ^n`
  on a disk containing `σ(L)` then `f(L) = Σ a_n L^n` [quoted; Dunford–Schwartz].
* **Thm 2.9.4** `L` compact, `λ_0 ≠ 0` an eigenvalue,
  `E(λ_0,L) = (1/2πi) ∮_{|λ−λ_0|=ε} (λ−L)^{-1} dλ` with `ε <
  dist(λ_0, σ(L)\{λ_0})`: (a) `E` is a projection; (b) `E(λ_0,L)V =
  N((λ_0−L)^{ν(λ_0)})` = span of ordinary and generalized eigenvectors
  [quoted]. Exercises: 2.9.1 `||(λ−L)^{-1}|| ≥ 1/dist(λ,σ(L))`; 2.9.2 Volterra
  operator has `σ = {0}`; 2.9.4 `R` bounded on compact `F ⊂ ρ(L)`; 2.9.5
  `L_n → L` in norm ⇒ compact `F ⊂ ρ(L)` lies in `ρ(L_n)` for large `n` (no
  spurious eigenvalues); 2.9.6 `E(σ_n,L_n) → E(λ_0,L)` in norm and
  `E(σ_n,L_n)u → u` for generalized eigenvectors `u` (convergence of
  approximate eigenspaces).

---

## 3. Chapter 3 — Approximation Theory

### 3.1 Approximation of continuous functions by polynomials (summary)
* **Thm 3.1.1 (Weierstrass)** `f ∈ C[a,b]`, `ε > 0` ⇒ ∃ polynomial `p` with
  `||f − p||_∞ ≤ ε` [quoted; Bernstein polynomials mentioned].
* **Thm 3.1.2 (Stone–Weierstrass)** `D ⊂ R^d` compact, `S ⊂ C(D)` a subspace
  containing constants, closed under products, separating points ⇒ `S` dense
  in `C(D)` [quoted].
* **Cor 3.1.3** polynomials dense in `C(D)`, `D ⊂ R^d` compact. **Cor 3.1.4**
  trigonometric polynomials dense in `C_p[−π,π]` (2π-periodic continuous).
* **Thm 3.1.5 (Müntz)** `0 < λ_1 < λ_2 < …`, `λ_n → ∞`: `span{x^{λ_j}}` dense in
  `L^2(0,1)` iff `Σ 1/λ_j = ∞` [quoted].
* Exercises: density of polynomials in `C^m[a,b]` / `C^m(Ω̄)` (3.1.7–3.1.8);
  moments determine `f` (3.1.4).

### 3.2 Interpolation theory (summary)
* Abstract interpolation problem: `V_n ⊂ V` `n`-dimensional with basis
  `{v_j}`, functionals `L_i ∈ V'`, data `b_i`: find `u_n ∈ V_n` with
  `L_i u_n = b_i`.
* **Def 3.2.1** `{L_i}` linearly independent over `V_n`; **Lemma 3.2.2** iff
  `det(L_i v_j) ≠ 0` [proved].
* **Thm 3.2.3** TFAE: unique solvability for all data; `{L_i}` independent over
  `V_n`; homogeneous problem has only `u_n = 0`; existence for all data
  [proved; finite linear algebra].
* **3.2.1 Lagrange interpolation**: nodes `x_0 < … < x_n`, `p_n ∈ P_n`,
  `p_n(x_i) = f(x_i)`; existence/uniqueness by Vandermonde / Lagrange basis
  `ℓ_i(x) = Π_{j≠i}(x−x_j)/(x_i−x_j)` / homogeneous argument; extends to
  distinct complex nodes.
* **Prop 3.2.4 (Interpolation error)** `f ∈ C^{n+1}[a,b]` ⇒ for each `x` ∃
  `ξ_x` in the hull of `{x, x_i}` with
  `f(x) − p_n(x) = ω_n(x) f^{(n+1)}(ξ_x)/(n+1)!`, `ω_n(x) = Π_{i=0}^n (x − x_i)`
  [proved by repeated Rolle]. Also (3.2.5) `f − p_n = ω_n f[x_0,…,x_n,x]`
  (divided differences). Runge phenomenon; Chebyshev nodes recommended.
* **3.2.2 Hermite interpolation**: `p_{2n−1}` matching `f, f'` at `n` nodes;
  general Hermite with multiplicities `m_i`, `N = Σ(m_i+1) − 1`; unique;
  error `f(x) − p_N(x) = Π_i (x−x_i)^{m_i+1} f^{(N+1)}(ξ)/(N+1)!` for
  `f ∈ C^{N+1}`.
* **3.2.3 Piecewise linear interpolation** `Π_h f` on a partition with mesh
  `h`: (3.2.8) `||f − Π f||_∞ ≤ ω(f,h)` (modulus of continuity); (3.2.9)
  `||f − Π f||_∞ ≤ (h^2/8)||f''||_∞` for `f ∈ C^2`; `L^2`-estimates
  `||f − Π f||_{L^2} ≤ c h^2 |f|_{H^2}`, `||(f − Π f)'||_{L^2} ≤ c h |f|_{H^2}`
  for `f ∈ H^2(a,b)` (scaling argument via the reference interval, (3.2.10)).
  Also error for general piecewise polynomial degree stated in exercises.
* **3.2.4 Trigonometric interpolation** on `2n+1` nodes `x_j = 2πj/(2n+1)`;
  reduces to complex polynomial interpolation on the unit circle via
  `z_j = e^{i x_j}`; unique. (Error bounds in 3.7.3.)
* Exercises 3.2.6–3.2.10 include Hermite error formula, cubic spline
  existence/uniqueness, reproducing-kernel Hilbert spaces.

### 3.3 Best approximation (detailed)
Throughout, `V` real or complex; minimization problems are over real
functionals.

#### 3.3.1 Convexity, lower semicontinuity
* **Def 3.3.1** convex set; convex combinations (3.3.1). **Def 3.3.2** convex /
  strictly convex function `f: K → R` on a convex `K`.
* **Def 3.3.3** closed set; *weakly closed* set (`v_n ∈ K`, `v_n ⇀ v` ⇒
  `v ∈ K`). Weakly closed ⇒ closed; converse false in general.
* **Def 3.3.4** (sequentially) lower semicontinuous (l.s.c.): `v_n → v` ⇒
  `f(v) ≤ liminf f(v_n)`; *weakly* l.s.c. (w.l.s.c.): the same for `v_n ⇀ v`.
  Continuous ⇒ l.s.c.; w.l.s.c. ⇒ l.s.c.
* **Ex 3.3.5** the norm is w.l.s.c. on any normed space [proved via Cor 2.5.6;
  simpler proof in inner product spaces].
* **Def 3.3.6** separated / strictly separated sets (by a nonzero `ℓ ∈ V'`).
* **Thm 3.3.7 (Separation)** `V` real normed, `A, B` nonempty disjoint convex,
  one compact and the other closed ⇒ strictly separated [quoted; from 2.5.5].
  Used in 8.2.1 and 11.3.5.

#### 3.3.2 Abstract existence results (minimization `inf_{v∈K} f(v)` (3.3.2))
* **Thm 3.3.8** `V` reflexive Banach, `K ⊂ V` bounded and weakly closed,
  `f: K → R` w.l.s.c. ⇒ a minimizer exists (and `inf f > −∞`) [proved:
  minimizing sequence, Thm 2.7.5, weak closedness, w.l.s.c.].
* **Def 3.3.9** `f` coercive on `K`: `f(v) → ∞` as `||v|| → ∞`, `v ∈ K`.
* **Thm 3.3.10** `V` reflexive Banach, `K` weakly closed, `f` w.l.s.c. and
  coercive ⇒ minimizer exists [proved: restrict to the bounded weakly closed
  sublevel set `K_0 = {f ≤ f(v_0)}` and apply 3.3.8].
* **Thm 3.3.11 (Mazur's lemma)** `v_n ⇀ u` in a normed space ⇒ there are convex
  combinations `u_n = Σ_{i=n}^{N(n)} λ_i^{(n)} v_i` with `u_n → u` strongly
  [quoted]. Corollaries [exercise 3.3.6]: convex + closed ⇒ weakly closed;
  convex + l.s.c. ⇒ w.l.s.c.; in particular `||u|| ≤ liminf ||u_n||`.
* **Thm 3.3.12 (Main existence/uniqueness theorem)** `V` reflexive Banach,
  `K ⊂ V` convex and closed, `f: K → R` convex and l.s.c.; if (a) `K` bounded
  or (b) `f` coercive on `K`, then a minimizer exists; if `f` is strictly
  convex, the minimizer is unique [proved from 3.3.10 + 3.3.11; uniqueness by
  the midpoint argument].
  *Generality*: reflexivity is used only to extract weakly convergent
  subsequences; any "`K` weakly sequentially compact after truncation" setting
  works.
* **Thm 3.3.13** same as 3.3.12 with `V` merely normed but `K` a convex,
  closed, *finite-dimensional* subset (subset of a finite-dimensional
  subspace) [stated; Heine–Borel replaces weak compactness].

#### 3.3.3 Existence of best approximation (`inf_{v∈K} ||u − v||` (3.3.3))
`f(v) = ||u − v||` is convex, continuous, coercive if `K` unbounded.
* **Thm 3.3.14** `K` closed convex in a reflexive Banach space ⇒ a best
  approximation `û ∈ K` exists.
* **Thm 3.3.15** `K` closed convex finite-dimensional subset of a normed space
  ⇒ best approximation exists.
* **Thm 3.3.16** `K` a finite-dimensional subspace of a normed space ⇒ best
  approximation exists (direct proof via Heine–Borel in Ex 3.3.7).
* **Ex 3.3.17** best `L^p`-approximation by `P_n` exists for every `f ∈ C[a,b]`
  or `L^p(a,b)`, `1 ≤ p ≤ ∞` (`p = ∞`: best uniform approximation).

#### 3.3.4 Uniqueness of best approximation
* **Thm 3.3.18** if `v ↦ ||v||^p` is strictly convex for some `p ≥ 1` and `K`
  is convex, then best approximations from `K` are unique [proved as in
  3.3.12]. Inner product spaces (`p=2`, Ex 3.3.8) and `L^p`, `1<p<∞`
  (Clarkson) qualify. Strict convexity is sufficient, not necessary: `L^∞`.
* **Thm 3.3.19 (Chebyshev equioscillation)** `f ∈ C[a,b]`, `n ≥ 0`: the best
  uniform approximation `p_n ∈ P_n` is unique and characterized by the
  existence of `n+2` points `x_0 < … < x_{n+1}` with
  `f(x_j) − p_n(x_j) = σ(−1)^j ρ_n(f)`, `σ = ±1` [quoted].
* **Thm 3.3.20** best uniform approximation of a continuous 2π-periodic `g`
  from trigonometric polynomials `T_n` is unique [quoted].
* Strictly normed space: `||u+v|| = ||u|| + ||v||`, `u ≠ 0` ⇒ `v = λu`, `λ ≥ 0`.
* **Thm 3.3.21** `V` strictly normed, `K` nonempty convex ⇒ at most one best
  approximation from `K` [proved]. Inner product spaces (Ex 3.3.9) and
  `L^p`, `1<p<∞`, are strictly normed.

### 3.4 Best approximation in inner product spaces; projection onto closed convex sets
(`V` a *real* inner product space throughout; complex analogues with `Re`.)
* **Lemma 3.4.1 (Variational characterization)** `K ⊂ V` convex, `u ∈ V`:
  `û ∈ K` is a best approximation of `u` iff (3.4.1)
  `(u − û, v − û) ≤ 0` for all `v ∈ K` [proved: derivative of
  `φ(λ) = ||u − (û + λ(v − û))||^2` at `0`; converse by expanding the square].
* **Cor 3.4.2** best approximation from a convex set is unique [proved: add
  the two inequalities ⇒ `||û_1 − û_2||^2 ≤ 0`].
* **Thm 3.4.3 (Projection theorem, closed convex sets)** `K` nonempty closed
  convex in a Hilbert space `V` ⇒ for every `u ∈ V` there is a unique `û ∈ K`
  with `||u − û|| = inf_{v∈K} ||u − v||`, characterized by (3.4.1) [proved
  from 3.3.14 + 3.4.2, and directly: a minimizing sequence is Cauchy by the
  parallelogram law since `(u_n + u_m)/2 ∈ K`]. Notation `û = P_K(u)`;
  `P_K` is nonlinear in general.
* **Prop 3.4.4** `P_K` is monotone, `(P_K u − P_K v, u − v) ≥ 0`, and
  non-expansive, `||P_K u − P_K v|| ≤ ||u − v||` [exercise 3.4.7].
* **Thm 3.4.5** `K` closed convex finite-dimensional subset of an inner product
  space ⇒ unique best approximation exists.
* **Thm 3.4.6** `K` a *complete subspace* of an inner product space `V` ⇒
  unique best approximation `û` exists, characterized by (3.4.2)
  `(u − û, v) = 0` for all `v ∈ K` (orthogonality of the error) [stated;
  proof via the parallelogram argument; equivalence (3.4.1)⟺(3.4.2) for
  subspaces is Ex 3.4.8].
  *Generality*: neither `V` complete nor `K` finite-dimensional is needed —
  only `K` complete (Mathlib's `orthogonalProjection` is stated this way).
* **Thm 3.4.7 (Orthogonal projection)** `K` complete subspace of an inner
  product space: `P_K: V → V` is linear, self-adjoint `(P_K u, v) = (u, P_K v)`,
  `||v||^2 = ||P_K v||^2 + ||v − P_K v||^2` (Pythagoras), and `||P_K|| = 1`
  (if `K ≠ {0}`) [exercise 3.4.9].
* With an orthonormal basis `{φ_i}` of `V` and `V_n = span{φ_1..φ_n}`:
  `P_n u = Σ_{i≤n} (u,φ_i) φ_i` (3.4.6) (least squares approximation), and
  `u = Σ_i (u,φ_i)φ_i`. **Ex 3.4.8** Legendre expansion in `L^2(−1,1)` with
  Parseval; **Ex 3.4.9** Fourier series as least-squares approximation in
  `L^2(0,2π)`. Exercises: projection onto a ball (3.4.1), onto `{v_1 ≤ v_2}`
  in `L^2 × L^2` (3.4.2), circulant approximation of Toeplitz matrices in
  Frobenius norm (3.4.12).

### 3.5 Orthogonal polynomials (detailed summary)
* Weighted space `L^2_w(−1,1)` (weight `w > 0` a.e., integrable), inner
  product `(u,v)_{0,w} = ∫ u v w`. Gram–Schmidt on monomials gives orthogonal
  polynomials `{p_n}`, `deg p_n = n`; best approximation from `P_N` is the
  orthogonal projection (3.5.2) `P_N u = Σ_{n≤N} ((u,p_n)_{0,w}/||p_n||^2_{0,w})
  p_n`.
* Jacobi weights `(1−x)^α(1+x)^β`. **Legendre** (`α=β=0`): Rodrigues formula
  (3.5.4), `(L_m,L_n) = 2/(2n+1) δ_mn` (3.5.5), ODE `((1−x^2)L_n')' + n(n+1)L_n
  = 0`, three-term recursion (3.5.6) `L_{n+1} = ((2n+1)/(n+1)) x L_n −
  (n/(n+1)) L_{n−1}`. **Chebyshev** (`α=β=−½`): `T_n(x) = cos(n arccos x)`,
  `(T_m,T_n)_w = (π/2) c_n δ_mn`, recursion `T_{n+1} = 2xT_n − T_{n−1}`.
* Error estimates for `L^2`-projection (`u ∈ H^s(−1,1)`) [quoted, Canuto–
  Quarteroni]: `||u − P_N u||_0 ≤ c N^{−s} ||u||_s`,
  `||u − P_N u||_1 ≤ c N^{3/2−s} ||u||_s`; the `H^1`-projection `P_{1,N}`
  satisfies (3.5.7) `||u − P_{1,N} u||_k ≤ c N^{k−s} ||u||_s`, `k = 0,1`.
* Exercises: general three-term recurrence for any orthogonal polynomial
  family (3.5.5–3.5.6 with explicit coefficients), Chebyshev 2nd kind,
  Lobatto polynomials (3.5.11).

### 3.6 Projection operators
* **Def 3.6.1** direct sum `V = V_1 ⊕ V_2` (unique decomposition); orthogonal
  direct sum in inner product spaces.
* **Prop 3.6.2** `V = V_1 ⊕ V_2` iff there is a linear `P` with `P^2 = P`,
  `V_1 = P(V)`, `V_2 = (I−P)(V)` [proved].
* **Def 3.6.3** projection operator on a Banach space: `P ∈ L(V)`, `P^2 = P`;
  topological direct sum `V = P(V) ⊕ (I−P)(V)`. Orthogonal projection (Hilbert
  case) iff `(Pv, (I−P)w) = 0` for all `v, w` (3.6.2).
* Examples: Lagrange interpolation projection on `C[a,b] → P_n` (3.6.5),
  piecewise linear interpolation (3.6.6), `Pv = Σ (u_i, v) u_i` for an
  orthonormal basis of a finite-dimensional subspace (3.6.7), Fourier partial
  sum `F_n` on `L^2(0,2π)` / `C_p(2π)` (3.6.8).
* **Prop 3.6.9 (Orthogonal projection)** `V_1` closed subspace of a Hilbert
  space `V`, `P: V → V_1`: (a) `P` is an orthogonal projection iff it is a
  self-adjoint projection; (b) every orthogonal projection is continuous with
  `||P|| ≤ 1`, `= 1` if `P ≠ 0`; (c) `V = V_1 ⊕ V_1^⊥`; (d) there is exactly
  one orthogonal projection onto `V_1`, and `||v − Pv|| = inf_{w∈V_1}||v − w||`;
  `I − P` is the orthogonal projection onto `V_1^⊥`; (e) if `P` is an
  orthogonal projection, `P(V)` is closed and `V = P(V) ⊕ (I−P)(V)`
  [exercise 3.6.6]. Ex 3.6.7: for any nonzero bounded projection on a Banach
  space, `||P|| ≥ 1`.

### 3.7 Uniform error bounds (Jackson theorems, Lebesgue constants)
* Reduction `g(θ) = f(cos θ)` links best uniform polynomial approximation on
  `[−1,1]` to best trigonometric approximation of even 2π-periodic functions
  (3.7.1)–(3.7.2) [sketched].
* **Thm 3.7.1 (Jackson, periodic)** `g` 2π-periodic, `g ∈ C^k`, `g^{(k)}`
  Hölder-`α` with constant `M_k` (`g ∈ C_p^{k,α}(2π)`) ⇒ best approximation
  `q_n ∈ T_n` satisfies `||g − q_n||_∞ ≤ c^{k+1} M_k / n^{k+α}`,
  `c = 1 + π^2/2` [quoted; Meinardus].
* **Thm 3.7.2 (Jackson, algebraic)** `f ∈ C^k[−1,1]`, `f^{(k)}` Hölder-`α` ⇒
  `||f − p_n||_∞ ≤ d_k c^{k+1} M_k / n^{k+α}` with `d_k ≥ n^{k+α}/(n(n−1)…(n−k)
  · (n−k)^α)` [quoted].
* **3.7.1 Fourier partial sums**: `||f − F_n f||_2 ≤ sqrt(2π) ||f − F_n f||_∞`
  (3.7.5); Dirichlet kernel representation (3.7.6)–(3.7.8)
  `F_n f(x) = (1/π)∫ D_n(x−y) f(y) dy`, `D_n(θ) = sin((n+½)θ)/(2 sin(θ/2))`;
  `F_n: C_p(2π) → T_n` is a bounded projection with
  `||F_n|| = L_n = (2/π) ∫_0^π |D_n(y)| dy` (3.7.9) (Lebesgue constant; equality
  via (2.2.8)), and `L_n = (4/π^2) log n + O(1)` (3.7.10) [quoted; Zygmund].
  ⇒ `{||F_n||}` unbounded ⇒ by Banach–Steinhaus (2.4.5) there is
  `f ∈ C_p(2π)` whose Fourier series does not converge uniformly (although it
  converges in `L^2`, where `||F_n|| = 1`).
  **Lebesgue-type error bound** (3.7.11): for any projection `F_n` onto `T_n`
  and best approximation `q_n`, `f − F_n f = (I − F_n)(f − q_n)` gives
  `||f − F_n f||_∞ ≤ (1 + ||F_n||) ||f − q_n||_∞ ≤ (1 + ||F_n||) c^{k+1} M_k
  n^{−k−α}`, hence (3.7.12) `||f − F_n f||_∞ ≤ c_k n^{−k−α} log n`. So Fourier
  series of any `f ∈ C_p^{0,α}` converge uniformly.
* **3.7.2 `L^2`-approximation by polynomials**: for orthonormal `{p_n}` in
  `L^2_w(−1,1)`, the projection `P_N u = Σ (u,p_n)_{0,w} p_n` is the integral
  operator (3.7.15) with kernel `K(x,t) = Σ_{n≤N} p_n(x)p_n(t)` (3.7.16), so on
  `C[−1,1]` `||P_N|| = max_x ∫ |K(x,t)| dt` (3.7.17) and (3.7.14)
  `||u − P_N u||_∞ ≤ (1 + ||P_N||) ||u − q||_∞` for any `q ∈ P_N`.
* **Thm 3.7.3 (Christoffel–Darboux)** `Σ_{n≤N} p_n(x)p_n(t) = (p_{N+1}(x)p_N(t) −
  p_N(x)p_{N+1}(t)) / (a_N (x−t))` for `x ≠ t` (and the derivative form for
  `x = t`), `a_N = A_{N+1}/A_N` with `A_n` the leading coefficient [quoted].
* **Ex 3.7.4** Chebyshev case: `||P_N||_{C→C} = (4/π^2) log N + O(1)`, hence
  Chebyshev expansions converge uniformly for `u ∈ C^{0,α}[−1,1]`.
* **3.7.3 Interpolatory projections**: trigonometric interpolation `I_n` at
  `2n+1` equispaced nodes is a projection `C_p(2π) → T_n` with Lagrange form
  (3.7.19) `I_n f(x) = (2/(2n+1)) Σ_j D_n(x − x_j) f(x_j)`,
  `||I_n|| = (2/(2n+1)) max_x Σ_j |D_n(x−x_j)| ≤ 1 + (2/π) log n` (3.7.20)
  [quoted; Rivlin] and exactly of order `log n`; hence (3.7.21)–(3.7.22)
  `||f − I_n f||_∞ ≤ (1 + ||I_n||) c^{k+1} M_k n^{−k−α} ≤ c_k n^{−k−α} log n`
  for `f ∈ C_p^{k,α}`.

**Backbone-relevant abstraction of 3.7**: *Lebesgue lemma*: if `P` is a
(bounded, linear) projection onto a subspace `S` of a normed space `V` then
`||u − Pu|| ≤ (1 + ||P||) dist(u, S)` (and `≤ ||I − P|| dist(u,S)`); combined
with a Jackson-type approximation rate and a Lebesgue-constant growth rate this
yields uniform convergence rates. The book proves it inline ((3.7.11),
(3.7.14), (3.7.21)).

---

## 5. Chapter 5 — Nonlinear Equations and Their Solution by Iteration (complete)

Setting: `V` Banach, `K ⊂ V`, `T: K → V`; fixed-point problem `u = T(u)`
(5.0.1); iteration `u_{n+1} = T(u_n)` (5.1.1) requires `T(K) ⊂ K` (5.1.2).
Reformulation of `f(u) = 0` as `u = u − F(f(u))` with `F(w) = 0 ⟺ w = 0`.

### 5.1 The Banach fixed-point theorem
* **Ex 5.1.1** affine `Tx = ax + b` on `R`: iteration converges iff `|a| < 1`.
* **Def 5.1.2** `T: K → V` contractive with constant `α ∈ [0,1)`:
  `||T(u) − T(v)|| ≤ α||u − v||`; non-expansive (`α = 1`); Lipschitz
  (constant `L ≥ 0`). Contractive ⇒ non-expansive ⇒ Lipschitz ⇒ continuous.
* **Thm 5.1.3 (Banach fixed-point theorem)** `K` nonempty closed subset of a
  Banach space `V`, `T: K → K` contractive with constant `α ∈ [0,1)`. Then:
  (1) ∃! `u ∈ K` with `u = T(u)`; (2) for any `u_0 ∈ K`, `u_n → u`, with
  (5.1.4) a priori `||u_n − u|| ≤ α^n/(1−α) ||u_0 − u_1||`;
  (5.1.5) a posteriori `||u_n − u|| ≤ α/(1−α) ||u_{n−1} − u_n||`;
  (5.1.6) linear rate `||u_n − u|| ≤ α ||u_{n−1} − u||`
  [proved: `||u_m − u_n|| ≤ α^n/(1−α) ||u_1 − u_0||` (5.1.7) ⇒ Cauchy ⇒
  limit in closed `K`; continuity of `T`; uniqueness by contraction].
  *Generality*: complete metric space (Mathlib `ContractingWith`).
  Ex 5.1.1: each hypothesis necessary; `||Tu − Tv|| < ||u − v||` insufficient.
  Ex 5.1.2: if `T` continuous and `T^m` contractive for some `m`, then `T` has
  a unique fixed point and the iteration converges. Ex 5.1.3: fixed point of
  `v = T(v) + y` depends continuously on `y`. Ex 5.1.4: local version on a
  ball with `T(0) = 0`.
* **Thm 5.1.4 (Strongly monotone + Lipschitz ⇒ bijective; "nonlinear
  Lax–Milgram" / Zarantonello)** `V` Hilbert, `T: V → V` with
  (5.1.8) `(T(v_1) − T(v_2), v_1 − v_2) ≥ c_1 ||v_1 − v_2||^2` and
  (5.1.9) `||T(v_1) − T(v_2)|| ≤ c_2 ||v_1 − v_2||`, `c_1, c_2 > 0`. Then for
  every `b ∈ V` the equation `T(u) = b` has a unique solution, and
  `||u_1 − u_2|| ≤ (1/c_1) ||b_1 − b_2||` (5.1.11) [proved: `T_θ(v) = v −
  θ(T(v) − b)` satisfies `||T_θ v_1 − T_θ v_2||^2 ≤ (1 − 2θc_1 + θ^2 c_2^2)
  ||v_1 − v_2||^2`, a contraction for `θ ∈ (0, 2c_1/c_2^2)`; Lipschitz
  dependence from (5.1.8) + Cauchy–Schwarz]. Used again in 8.3 (Ex 8.3.1:
  Lax–Milgram is the linear case) and 11.3.
  Note: the contraction argument also gives a convergent iteration
  `u_{n+1} = u_n − θ(T(u_n) − b)` (Richardson / gradient-type), with
  contraction factor `sqrt(1 − 2θc_1 + θ^2c_2^2)`, optimal `θ = c_1/c_2^2`.

### 5.2 Applications to iterative methods
* **Thm 5.2.1** scalar case: `T: [a,b] → [a,b]` contractive ⇒ unique fixed
  point and the three error bounds of 5.1.3 [specialization]. Sufficient:
  `sup |T'| < 1` (mean value theorem).
* **5.2.2 Linear algebraic systems** `Ax = b` via splitting `A = N − M`:
  iteration `N x_n = M x_{n−1} + b`, error `x − x_n = (N^{-1}M)^n (x − x_0)`
  (5.2.5); converges for all `x_0` iff `r(N^{-1}M) < 1` (spectral radius);
  sufficient: `||N^{-1}M|| < 1` in some induced norm. Facts listed [quoted]:
  `r(A) ≤ ||A||` for any induced norm; `∀ε ∃` induced norm with
  `||A|| ≤ r(A) + ε`; `r(A) = lim ||A^n||^{1/n}` (Gelfand). Jacobi
  (`N = D`), Gauss–Seidel (`N = D + L`), SOR (`N = D/ω + L`). Ex 5.2.2:
  diagonal dominance ⇒ Jacobi and Gauss–Seidel converge. Ex 5.2.3: Richardson
  `x_n = x_{n−1} + θ(b − Ax_{n−1})` for SPD `A` converges iff
  `0 < θ < 2/λ_max`, with optimal `θ`.
* **5.2.3 Integral equations**. Linear Fredholm (5.2.7): fixed-point iteration
  (5.2.9) has contractivity `α = ||K||/|λ|`, condition (5.2.8) as in Ex 2.3.2;
  equivalent to the truncated Neumann series (Ex 5.2.5).
  **Thm 5.2.2 (Urysohn equation)** `u(x) = μ∫_a^b k(x,y,u(y))dy + f(x)`,
  `f ∈ C[a,b]`, `k ∈ C([a,b]^2 × R)` uniformly Lipschitz in the third
  argument with constant `M` (5.2.12), `|μ| M (b−a) < 1` ⇒ unique solution in
  `C[a,b]`, and the iteration (5.2.13) converges [exercise 5.2.4; direct
  application of 5.1.3]. Hammerstein and Nekrasov equations mentioned.
  **Thm 5.2.3 (Nonlinear Volterra equation)** `u(t) = ∫_a^t k(t,s,u(s))ds +
  f(t)`, `k` continuous for `a ≤ s ≤ t ≤ b`, `u ∈ R`, uniformly Lipschitz in
  `u` with constant `M`, `f ∈ C[a,b]` ⇒ unique solution in `C[a,b]` and the
  iteration (5.2.16) converges for every `u_0 ∈ C[a,b]` — *no smallness
  condition* [proved two ways: (1) `||T^m u − T^m v||_∞ ≤ (M(b−a))^m/m!
  ||u − v||_∞`, so `T^m` is a contraction for large `m`, then Ex 5.1.2;
  (2) the weighted (Bielecki) norm `|||v||| = max_t e^{−βt}|v(t)|`, `β > M`,
  is equivalent to `||.||_∞` and makes `T` a contraction with constant
  `M/β`]. Extends to `[a,∞)`.
* **5.2.4 ODEs in Banach spaces**: `u'(t) = f(t,u(t))`, `u(t_0) = z`, `f:
  [t_0−a, t_0+a] × V → V` continuous, equivalent to `u(t) = z + ∫_{t_0}^t
  f(s,u(s))ds` (5.2.19); Picard iteration (5.2.20).
  **Thm 5.2.4 (Generalized Picard–Lindelöf)** `Q_b = {(t,u): |t−t_0| ≤ a,
  ||u − z|| ≤ b}`; `f: Q_b → V` continuous and uniformly Lipschitz in `u`
  with constant `L`; `M = max_{Q_b} ||f||`, `a_0 = min{a, b/M}`. Then the IVP
  has a unique `C^1` solution on `[t_0−a_0, t_0+a_0]`, the Picard iterates
  converge uniformly there for any `u_0` with `||z − u_0|| < b`, and with
  `α = 1 − e^{−L a_0}` the weighted error `max_{|t−t_0|≤a_0} ||u_n(t) − u(t)||
  e^{−L|t−t_0|}` obeys the three Banach-fixed-point bounds (a priori
  `α^n/(1−α)·[u_1−u_0]`, a posteriori, linear) [exercise 5.2.11; proof =
  5.1.3 with the weighted norm of Thm 5.2.3].
  Ex 5.2.12–5.2.13: Gronwall's inequality (integral form, with `h ∈ L^1`,
  `h ≥ 0`) and continuous dependence of ODE solutions on data:
  `||u_1(t) − u_2(t)|| ≤ e^{L|t−t_0|}(||u_{1,0} − u_{2,0}|| + a max ||r_1 − r_2||)`.

### 5.3 Differential calculus for nonlinear operators
* Motivation: `f: R → R` differentiable iff `f(x_0+h) = f(x_0) + ah + o(|h|)`;
  Jacobian for `R^d → R^m`; directional derivative (5.3.4) is weaker.
  Convention: differentiability at `u_0` presumes `u_0` interior to `K`.
* **Def 5.3.1 (Fréchet derivative)** `f: K ⊂ V → W`, normed spaces: `f'(u_0) =
  A ∈ L(V,W)` with `f(u_0 + h) = f(u_0) + Ah + o(||h||)`. Unique [proved].
  `f': K_0 → L(V,W)`; second derivative `f'' : K_0 → L(V, L(V,W)) ≅
  L(V × V, W)` (bilinear).
* **Def 5.3.2 (Gâteaux derivative)** `A ∈ L(V,W)` with `lim_{t→0} (f(u_0 + th)
  − f(u_0))/t = Ah` for every `h ∈ V` (note: the book requires the Gâteaux
  derivative to be *linear and bounded*).
* **Prop 5.3.3** Fréchet differentiable at `u_0` ⇒ continuous at `u_0`.
* **Prop 5.3.4** Fréchet ⇒ Gâteaux; conversely, if the Gâteaux limit is
  uniform in `||h|| = 1`, or if the Gâteaux derivative is continuous at `u_0`
  (as a map into `L(V,W)`), then it is a Fréchet derivative [stated].
  Ex 5.3.2 gives a Gâteaux-but-not-Fréchet example; Ex 5.3.1 partials without
  Gâteaux.
* **Prop 5.3.5 (Sum rule)**, **Prop 5.3.6 (Product rule)** for a bounded
  bilinear `b: V_1 × V_2 → W`: `B(u) = b(f_1(u), f_2(u))` has
  `B'(u_0)h = b(f_1'(u_0)h, f_2(u_0)) + b(f_1(u_0), f_2'(u_0)h)`;
  **Prop 5.3.7 (Chain rule)** `(g∘f)'(u_0) = g'(f(u_0)) f'(u_0)` when both are
  Fréchet; if `f'` is only Gâteaux and `g'` Fréchet, then `g∘f` is Gâteaux
  differentiable with the same formula [exercises 5.3.4–5.3.6].
* **Ex 5.3.8** affine `f(v) = Lv + b`: `f' ≡ L`. **Ex 5.3.9** Jacobian.
  **Ex 5.3.10** Urysohn operator `T(u)(t) = g(t) + ∫_a^b k(t,s,u(s))ds` on
  `C[a,b]`: `T'(u_0)h(t) = ∫ ∂_u k(t,s,u_0(s)) h(s) ds` when `∂_u k` is
  continuous.
* **Prop 5.3.11 (Mean value inequality)** `U, V` real Banach, `K ⊂ U` open,
  `F: K → V` differentiable with `F'` continuous `K → L(U,V)`, segment
  `[u,w] ⊂ K` ⇒ `||F(u) − F(w)|| ≤ sup_{0≤θ≤1} ||F'((1−θ)u + θw)|| ||u − w||`
  (5.3.7) [proved: pick `T ∈ V'` with `||T|| = 1`, `T(F(u) − F(w)) =
  ||F(u) − F(w)||` (Cor 2.5.6); apply the scalar MVT to `g(t) =
  T(F(tu + (1−t)w))`, differentiable by the chain rule].
  *Generality*: completeness is not used; Gâteaux differentiability along
  the segment suffices; the equality form of the MVT fails in general
  (Ex 5.3.7) but the integral form `F(b) − F(a) = ∫_0^1 F'(a + t(b−a))dt (b−a)`
  holds (Ex 5.3.8).
* **Cor 5.3.12** `K` connected open, `F' ≡ 0` on `K` ⇒ `F` constant.
* **Prop 5.3.13 (Taylor remainder)** `F` twice continuously differentiable on
  open `K`, segment `[u_0, u_0 + h] ⊂ K` ⇒
  `||F(u_0 + h) − F(u_0) − F'(u_0)h|| ≤ ½ sup_{0≤θ≤1} ||F''(u_0 + θh)|| ||h||^2`
  [exercise 5.3.10]. Used in 12.7.1.
* **Def 5.3.14** partial derivatives `f_u, f_v` of `f: U × V → W`.
  **Prop 5.3.15** Fréchet differentiable at `(u_0,v_0)` ⇒ partials exist and
  `f'(u_0,v_0)(h,k) = f_u h + f_v k` (5.3.8); conversely partials existing near
  and continuous at `(u_0,v_0)` ⇒ Fréchet differentiable [proved].
  **Cor 5.3.16** `f` is `C^1` near `(u_0,v_0)` iff `f_u, f_v` are continuous
  near it.
* **5.3.4 Gâteaux derivative and convex minimization** (`V` normed, `K ⊂ V`
  nonempty convex, `f: K → R` Gâteaux differentiable with `f'(u) ∈ V'`,
  written `<f'(u), v>`):
  **Thm 5.3.17** TFAE: (a) `f` convex; (b) `f(v) ≥ f(u) + <f'(u), v − u>`
  for all `u, v ∈ K`; (c) `<f'(v) − f'(u), v − u> ≥ 0` (monotone gradient)
  [proved; (c)⇒(b) via the scalar function `φ(t) = f(u + t(v−u))` and the
  scalar MVT].
  **Thm 5.3.18** TFAE: `f` strictly convex; strict inequality in (b) for
  `u ≠ v`; strict monotonicity in (c) [exercise 5.3.11].
  **Thm 5.3.19 (First-order optimality)** `f` convex and Gâteaux
  differentiable on convex `K`: `u ∈ K` minimizes `f` over `K` iff
  (5.3.10) `<f'(u), v − u> ≥ 0` for all `v ∈ K` (a variational inequality);
  if `K` is a subspace this is `<f'(u), v> = 0` for all `v ∈ K` (5.3.11)
  [proved].
  Exercises: Hessian characterization of convexity in `R^d` (5.3.12); strict
  convexity of `(1+|ξ|^2)^{p/2}/p` for `p ≥ ½` (5.3.13, used in 8.8);
  `f(v) = ½(Av,v)` has `f'(v) = ½(A + A*)v` (5.3.15); `f(v) = ½a(v,v) − ℓ(v)`
  has `f'(u) = a(u,·) − ℓ` (5.3.16, the energy functional of Ch. 8–9).

### 5.4 Newton's method
* Newton iteration in Banach spaces: `F: U → V` Fréchet differentiable,
  `u_{n+1} = u_n − [F'(u_n)]^{-1} F(u_n)` (5.4.2).
* **Thm 5.4.1 (Local convergence, quadratic)** `U, V` Banach; `u*` a solution
  of `F(u) = 0` with `[F'(u*)]^{-1} ∈ L(V,U)`; `F'` locally Lipschitz near
  `u*`: `||F'(u) − F'(v)|| ≤ L||u − v||` on a neighbourhood `N(u*)`. Then ∃
  `δ > 0` such that for `||u_0 − u*|| ≤ δ` the Newton sequence is well
  defined, stays in `B(u*,δ)`, converges to `u*`, and for some `M` with
  `Mδ < 1`: (5.4.3) `||u_{n+1} − u*|| ≤ M ||u_n − u*||^2` and (5.4.4)
  `||u_n − u*|| ≤ (Mδ)^{2^n}/M` [proved]. Proof: by the perturbation theorem
  (2.3.5) `F'(u)^{-1}` exists near `u*` with `c_0 = sup ||F'(u)^{-1}|| < ∞`;
  `T(u) = u − F'(u)^{-1}F(u)` satisfies `T(u) − u* = F'(u)^{-1}[F(u*) − F(u)
  − F'(u)(u* − u)] = F'(u)^{-1} ∫_0^1 [F'(u + t(u*−u)) − F'(u)]dt (u* − u)`,
  hence `||T(u) − u*|| ≤ (c_0 L/2)||u − u*||^2` (5.4.5); choose `δ <
  2/(c_0L)`, `M = c_0L/2`.
* **Thm 5.4.2 (Kantorovich)** [quoted; Zeidler] Suppose (a) `F: D(F) ⊂ U → V`
  is differentiable on an open convex set `D(F)` with `||F'(u) − F'(v)|| ≤
  L||u − v||`; (b) for some `u_0`, `[F'(u_0)]^{-1}` exists and is bounded,
  and `h := a b L ≤ ½` where `a ≥ ||[F'(u_0)]^{-1}||`, `b ≥ ||[F'(u_0)]^{-1}
  F(u_0)||` (= `||u_1 − u_0||`); set `t* = (1 − sqrt(1−2h))/(aL)`,
  `t** = (1 + sqrt(1−2h))/(aL)`; (c) `B̄(u_1, r) ⊂ D(F)` with `r = t* − b`.
  Then `F(u) = 0` has a solution `u* ∈ B̄(u_1, r)`, unique in
  `B̄(u_0, t**) ∩ D(F)`; the Newton sequence converges to `u*` with
  `||u_n − u*|| ≤ (1 − sqrt(1−2h))^{2^n} / (2^n a L)` [reconstructed from the
  garbled text; matches the standard statement — mark the exact form of the
  error bound as [uncertain]].
* **5.4.2 Applications**: nonlinear systems in `R^d` (solve
  `F'(x_n)δ_n = −F(x_n)`); nonlinear integral equation `u = ∫_0^1 k(t,s,u(s))ds`
  on `C[0,1]` with `F'(u)v = v − ∫ ∂_u k(t,s,u(s)) v(s) ds` (each Newton step is
  a linear Fredholm equation (5.4.10)); modified Newton with frozen derivative
  `F'(u_0)` (5.4.11) (linearly convergent, Ex 5.4.5 via Banach fixed point);
  two-point BVP `u'' = f(t,u)` in `C_0^2[0,1]` with linearized BVPs.

### 5.5 Completely continuous vector fields (brief)
* **Thm 5.5.1 (Brouwer)** `K ⊂ R^d` bounded closed convex, `T: K → K`
  continuous ⇒ fixed point [quoted].
* **Ex 5.5.2** (Kakutani-type) on the unit ball of an infinite-dimensional
  Hilbert space there is a Lipschitz `T: K → K` without fixed points ⇒ extra
  hypotheses needed.
* **Def 5.5.3** nonlinear `T: K → W` compact (bounded sets ↦ precompact sets);
  completely continuous = compact + continuous.
* **Thm 5.5.4 (Schauder)** `V` Banach, `K` bounded closed convex, `T: K → K`
  completely continuous ⇒ fixed point [quoted].
* **Prop 5.5.5** `T` completely continuous on open `K` and differentiable at
  `v_0` ⇒ `T'(v_0)` is a compact linear operator [quoted]. (So the Fredholm
  alternative applies to the linearization `I − T'(v_0)`.)
* **5.5.1 Rotation (topological degree) of `Φ = I − T`** on the boundary of a
  bounded open `B`: properties P1 (`Rot ≠ 0` ⇒ fixed point in `B`), P2
  (homotopy invariance), P3 (index of isolated fixed points; `Rot` = sum of
  indices), P4 (if `1 ∉ σ(T'(v_0))` the index is `(−1)^β`, `β` = number of
  real eigenvalues `> 1` with multiplicity, and `v_0` is isolated), P5 (index
  zero iff unstable under small completely continuous perturbations)
  [quoted; Krasnoselskii]. Used in 12.7.2.

### 5.6 Conjugate gradient method for operator equations (detailed)
* Setting: `V` *real, separable* Hilbert space; `A ∈ L(V)` bounded,
  self-adjoint, positive definite; `Au = f` (5.6.1) uniquely solvable with
  bounded `A^{-1}` by Thm 5.1.4 (with `c_1` the coercivity constant,
  `c_2 = ||A||`).
* **CG iteration (5.6.2)**: `r_0 = f − Au_0`, `s_0 = r_0`; for `k ≥ 0`:
  `α_k = ||r_k||^2 / (As_k, s_k)`, `u_{k+1} = u_k + α_k s_k`,
  `r_{k+1} = f − Au_{k+1}` (`= r_k − α_k A s_k`),
  `β_k = ||r_{k+1}||^2 / ||r_k||^2`, `s_{k+1} = r_{k+1} + β_k s_k`.
  Energy inner product `(v,u)_A = (Av,u)`, `||v||_A = sqrt((v,v)_A)`.
* **Thm 5.6.1 (Linear convergence)** [quoted; Patterson] Let `A` be bounded,
  self-adjoint and satisfy (5.6.3) `m||v|| ≤ ||v||_A ≤ M||v||` for all `v`,
  `m, M > 0` (so `||.||_A` and `||.||` are equivalent). Then `u_k → u` and
  (5.6.4) `||u − u_{k+1}||_A ≤ ((M − m)/(M + m)) ||u − u_k||_A`, `k ≥ 0`.
  Improved bound (5.6.5) [quoted; Patterson]:
  `||u − u_k||_A ≤ 2 ((sqrt M − sqrt m)/(sqrt M + sqrt m))^k ||u − u_0||_A`,
  and (5.6.6) `(sqrt M − sqrt m)/(sqrt M + sqrt m) ≤ (M − m)/(M + m)`
  [exercise 5.6.1].
  **[uncertain — internal inconsistency in the book's normalization]**: (5.6.3)
  as printed bounds the *norms* (`m||v|| ≤ ||v||_A`, i.e. `m^2||v||^2 ≤
  (Av,v)`), but later (5.6.9)–(5.6.10) identify `m = δ = inf(1−λ_j)` and
  `M = Λ = sup(1−λ_j)` = bounds on the *spectrum* of `A`, i.e.
  `δ||v||^2 ≤ (Av,v) ≤ Λ||v||^2`. The standard theorem (Saad Thm 6.29;
  Luenberger) is: if `m||v||^2 ≤ (Av,v) ≤ M||v||^2` (`κ = M/m`) then the
  A-norm error satisfies the `2((sqrt κ − 1)/(sqrt κ + 1))^k` bound, and the
  one-step bound `(κ−1)/(κ+1)` is the steepest-descent rate, which CG also
  satisfies. For the backbone use the spectral-bound form.
* **Krylov / optimality facts used (quoted from Luenberger)**: (5.6.12)
  `u_k = u_0 + P_{k−1}(A) r_0` with `deg P_{k−1} ≤ k − 1`, i.e. `u_k − u_0 ∈
  K_k(A, r_0) = span{r_0, Ar_0, …, A^{k−1}r_0}`; (5.6.14) optimality: for any
  other `y_k = u_0 + Q_{k−1}(A) r_0`, `||u − u_k||_A ≤ ||u − y_k||_A`; i.e.
  `||u − u_k||_A = min_{y ∈ u_0 + K_k(A)} ||u − y||_A` (last paragraph of 5.6).
* **Thm 5.6.2 (Superlinear convergence, Winther)** `K` compact self-adjoint on
  the Hilbert space `V`, `A = I − K` self-adjoint positive definite (⟺
  `sup_j λ_j < 1` (5.6.8), eigenvalues `|λ_1| ≥ |λ_2| ≥ … → 0` with
  orthonormal eigenvectors `φ_j` by Thm 2.8.15/2.8.12; `δ = inf(1−λ_j) =
  1/||A^{-1}||`, `Λ = sup(1−λ_j) = ||A||`). Then the CG iterates satisfy
  `||u − u_k|| ≤ (c_k)^k ||u − u_0||` with `c_k → 0`, explicitly (5.6.21)
  `c_k = (Λ^{3/2}/δ)^{1/k} · (2/k) Σ_{j=1}^k |λ_j|/(1 − λ_j)` [proved]. Proof:
  choose the comparison polynomial `Q_k(λ) = Π_{j≤k} (λ − λ_j)/(1 − λ_j)`
  (so `Q_k(1) = 1`, `Q_k(A)φ_j = 0` for `j ≤ k`), write `Q_k(λ) = 1 −
  (1−λ)P_{k−1}(λ)`, `y_k = u_0 + P_{k−1}(K)r_0`; then `r̃_k = f − Ay_k =
  Q_k(A)r_0` (5.6.17) expands in eigenvectors `j > k` only, so
  `||r̃_k|| ≤ σ_k ||r_0||`, `σ_k = sup_{j>k}|Q_k(λ_j)| ≤ Π_{j≤k} 2|λ_j|/(1−λ_j)`
  (5.6.19); by AM–GM `σ_k ≤ ((2/k)Σ_{j≤k}|λ_j|/(1−λ_j))^k → 0` (5.6.20);
  finally `||u − u_k|| ≤ δ^{−1/2}||u − u_k||_A ≤ δ^{−1/2}||u − y_k||_A ≤
  δ^{−1}||r̃_k||` (5.6.16) and `||r_0|| ≤ Λ^{1/2}||u − u_0||_A ≤ Λ ||u − u_0||`
  [the exponent bookkeeping `Λ^{3/2}/δ` is from the text; details uncertain].
* **Thm 5.6.3 (Rate of `c_k → 0` for integral operators, Flores)** `V =
  L^2(a,b)`, `K` the integral operator (5.6.22), `A = I − K` positive definite;
  `σ_k := (1/k)Σ_{j≤k}|λ_j|/(1−λ_j)` (5.6.23). (a) `K` self-adjoint
  Hilbert–Schmidt ⇒ `(1/k)|λ_1|/(1−λ_1) ≤ σ_k ≤ (1/k) ||K||_{HS} ||(I−K)^{-1}||`
  (5.6.24) [proved via `Σλ_j^2 = ||K||_HS^2` ⇒ `|λ_j| ≤ ||K||_HS/sqrt j`];
  (b) `k(t,s)` symmetric with continuous partial derivatives up to order
  `p ≥ 1` ⇒ `σ_k ≤ M ζ(p + ½) ||(I−K)^{-1}|| / k` (5.6.25) [proved from
  `j^{p+½}λ_j → 0` (Fenyő–Stolle)]. Conclusion: `σ_k = O(1/k)` at best,
  `O(k^{−1/2})` typically; the superlinear bound (5.6.11) is essentially
  `||u − u_k|| ≤ (C/k)^k ||u − u_0||`.
* Closing remarks: `u_k − u_0 ∈ K_k(A)`, `||u − u_k||_A = min_{y ∈ u_0 +
  K_k(A)} ||u − y||_A`; other Krylov methods choose differently
  (nonsymmetric case, cf. Freund–Golub–Nachtigal); nonlinear CG exists.
  Exercises 5.6.1–5.6.3 fill in (5.6.6), (5.6.12), (5.6.20).

---

## 6.2 Chapter 6 — Lax equivalence theorem (abstract statement)

* Framework: `V` Banach, `V_0 ⊂ V` dense subspace, `L: V_0 → V` linear
  (typically unbounded, a differential operator). Abstract IVP (6.2.1):
  `du/dt = Lu(t)`, `0 ≤ t ≤ T`, `u(0) = u_0`.
* **Def 6.2.1** solution: `u: [0,T] → V` with `u(t) ∈ V_0`,
  `||(u(t+Δt) − u(t))/Δt − Lu(t)|| → 0` as `Δt → 0` (one-sided at the ends),
  `u(0) = u_0`.
* **Def 6.2.2** well-posed: for every `u_0 ∈ V_0` there is a unique solution
  and (6.2.3) `sup_{0≤t≤T} ||u(t) − ū(t)|| ≤ c_0 ||u_0 − ū_0||`. Then the
  solution operator `S(t): V_0 → V` is linear with `sup_t ||S(t)|| ≤ c_0`, and
  extends uniquely (Thm 2.4.1) to `S(t) ∈ L(V)`.
* **Def 6.2.3** generalized solution `u(t) = S(t)u_0` for `u_0 ∈ V \ V_0`.
* **Prop 6.2.5** the generalized solution is continuous in `t` [proved: ε/3
  with a `V_0`-approximation of `u_0`]. **Prop 6.2.6** semigroup property
  `S(t_1 + t_0) = S(t_1)S(t_0)` for `t_0 + t_1 ≤ T` [proved via uniqueness].
* Difference method: a family `C(Δt) ∈ L(V)`, `0 < Δt ≤ Δt_0`, *uniformly
  bounded* (`||C(Δt)|| ≤ c`); approximate solution `u_{Δt}(mΔt) = C(Δt)^m u_0`.
* **Def 6.2.7 (Consistency)** ∃ dense subspace `V_c ⊂ V` such that for every
  `u_0 ∈ V_c` the solution `u` satisfies
  `sup_{t∈[0,T]} ||(C(Δt)u(t) − u(t+Δt))/Δt|| → 0` as `Δt → 0`
  (equivalently `(C(Δt) − I)/Δt · u(t) → Lu(t)` uniformly).
* **Def 6.2.9 (Convergence)** for every `t ∈ [0,T]` and `u_0 ∈ V`,
  `||[C(Δt_i)^{m_i} − S(t)]u_0|| → 0` whenever `m_i Δt_i → t`, `Δt_i → 0`.
* **Def 6.2.10 (Stability)** `{C(Δt)^m : 0 < Δt ≤ Δt_0, mΔt ≤ T}` is uniformly
  bounded: `||C(Δt)^m|| ≤ M_0`.
* **Thm 6.2.11 (Lax equivalence theorem)** assume the IVP (6.2.1) is
  well-posed. Then for a consistent difference method, stability ⟺
  convergence [proved]. Proof: (stability ⇒ convergence) telescoping
  `C^m u_0 − u(t) = Σ_{j} C^j [C u((m−1−j)Δt) − u((m−j)Δt)] + u(mΔt) − u(t)`
  gives (6.2.10) `||C(Δt)^m u_0 − u(t)|| ≤ M_0 mΔt sup_t ||(C(Δt)u(t) −
  u(t+Δt))/Δt|| + ||u(mΔt) − u(t)||` for `u_0 ∈ V_c`; density of `V_c` +
  stability + well-posedness give the general `u_0` (ε/2 argument).
  (convergence ⇒ stability) if unstable, pick `||C(Δt_k)^{m_k}|| → ∞` with
  `m_k Δt_k ≤ T`; convergence gives `sup_k ||C(Δt_k)^{m_k} u_0|| < ∞` for every
  `u_0`, contradicting the uniform boundedness principle (2.4.4).
* **Cor 6.2.12 (Convergence order)** if `u_0 ∈ V_c` and the local truncation
  error satisfies `sup_t ||(C(Δt)u(t) − u(t+Δt))/Δt|| ≤ c(Δt)^k` then
  `||C(Δt)^m u_0 − u(t)|| ≤ c(Δt)^k` for `mΔt = t` (with `c` absorbing `M_0 T`)
  [proved from (6.2.10)].
* Examples 6.2.4/6.2.8/6.2.13: heat equation `u_t = ν u_xx` on `[0,π]` in
  `V = C_0[0,π]` (sup norm), `V_0` = trigonometric polynomials; forward scheme
  `||C(Δt)|| ≤ |1−2r| + 2r`, stable for `r = νΔt/(Δx)^2 ≤ ½`; backward scheme
  `||C(Δt)|| ≤ 1` unconditionally.
* Section 6.3 gives a variant with a different consistency definition
  (Thm 6.3.2: consistent + stable ⇒ convergent, with error order).
  Infrastructure needed to formalize 6.2: nothing beyond Banach spaces, the
  extension theorem 2.4.1 and the uniform boundedness principle; the examples
  need `C[0,π]`, Fourier sine series and the maximum principle.

---

## 8. Chapter 8 — Weak Formulations of Elliptic Boundary Value Problems (8.2, 8.3, 8.6, 8.7, 8.8)

### 8.1 Model problem (context)
Poisson problem `−Δu = f`, `u = 0` on `∂Ω` ⇒ weak form (8.1.3): `u ∈ H_0^1(Ω)`,
`∫∇u·∇v = ∫fv` for all `v ∈ H_0^1(Ω)`; abstract form (8.1.4) `a(u,v) = ℓ(v)`;
operator form `Au = ℓ` with `A: H_0^1 → H^{−1}`, `<Au,v> = a(u,v)`.

### 8.2 General existence and uniqueness results (abstract operator equations)
* Problem (8.2.1): `L: D(L) ⊂ V → W` linear, `f ∈ W`; solvability for all `f`
  ⟺ `R(L) = W`; uniqueness ⟺ `N(L) = {0}`.
* **Thm 8.2.1** `V, W` Hilbert, `L: D(L) ⊂ V → W` linear ⇒ `R(L) = W` iff
  `R(L)` is closed and `R(L)^⊥ = {0}` [proved: if `R(L)` is a proper closed
  subspace, separate `w ∉ R(L)` from it (Thm 3.3.7) by `w* ∈ W'` and use
  linearity to get `0 ≠ w* ∈ R(L)^⊥`].
  *Generality*: Banach `W` with `R(L)^⊥` replaced by the annihilator
  `R(L)^a ⊂ W'` (this is what the proof actually shows).
* **Def 8.2.2** closed operator: `v_n ∈ D(T)`, `v_n → v`, `T v_n → w` ⇒
  `v ∈ D(T)`, `Tv = w`. Continuous ⇒ closed; Ex 8.2.3: `−Δ` is closed but not
  continuous on `L^2`.
* **Thm 8.2.4 (Closed + stability estimate ⇒ well-posed)** `V, W` Hilbert,
  `L: D(L) ⊂ V → W` linear closed, with the *stability estimate* (8.2.2)
  `||Lv||_W ≥ c||v||_V` for all `v ∈ D(L)` (`c > 0`), and `R(L)^⊥ = {0}`.
  Then `Lu = f` has a unique solution for every `f ∈ W` [proved: (8.2.2)
  makes preimages of Cauchy sequences Cauchy; completeness of `V` and
  closedness of `L` give closed range; then 8.2.1; uniqueness from (8.2.2)].
  *Generality*: `V` Banach suffices (only completeness of `V` is used); `W`
  Banach with annihilator version of 8.2.1; continuity of `L` may replace
  closedness.
* **Ex 8.2.5** `V` Hilbert, `L ∈ L(V,V')` strongly monotone (`<Lv,v> ≥ c||v||^2`)
  ⇒ (8.2.2) holds with the same `c` and `R(L)^⊥ = {0}`, hence `L` is a
  bijection `V → V'` (a proof of Lax–Milgram via 8.2.4). Ex 8.2.6: Poisson
  problem, `L: H_0^1 → H^{−1}` with `||L|| = 1`, `<Lv,v> = ||v||^2`.
* Banach-space version: `L: D(L) ⊂ V → W` densely defined; dual operator
  `L*: D(L*) ⊂ W' → V'` by `<L*w*, v> = <w*, Lv>`; annihilators `N(L)^a`,
  `N(L*)_a`.
* **Thm 8.2.7 (Closed range theorem, Banach)** `V, W` Banach, `L` densely
  defined closed ⇒ TFAE: (a) `R(L)` closed in `W`; (b) `R(L) = {w : <w*,w> = 0
  ∀ w* ∈ N(L*)}`; (c) `R(L*)` closed in `V'`; (d) `R(L*) = N(L)^a` [quoted;
  Yosida/Zeidler]. Consequence (abstract Fredholm alternative): if `R(L)` is
  closed then `Lu = f` is solvable iff `<w*,f> = 0` for all `w* ∈ N(L*)`;
  closedness follows from a stability estimate `||Lv|| ≥ c||v||`.
* **Thm 8.2.8 (Uniqueness for nonlinear equations)** `V, W` Banach,
  `T: D(T) ⊂ V → W`; then `T(u) = w` has at most one solution if either
  (a) stability `||T(u) − T(v)|| ≥ c||u − v||`, or (b) `T − I` is strictly
  contractive-like: `||(T(u) − u) − (T(v) − v)|| < ||u − v||` for `u ≠ v`
  [proved; trivial].

### 8.3 The Lax–Milgram Lemma
* **Thm 8.3.1 (Operators ⟷ bilinear forms)** `V` real Banach: `A ∈ L(V,V')`
  and bounded bilinear `a: V × V → R` correspond bijectively via
  `<Au, v> = a(u,v)` (8.3.1), with `||A|| = ` the bound of `a` [proved].
  Dictionary (Hilbert `V`): `a` bounded / positive / strictly positive /
  strongly positive (V-elliptic, `a(v,v) ≥ α||v||^2`) / symmetric ⟺ the same
  for `A` (`<Av,v> ≥ …`).
* **Thm 8.3.2 (Quadratic minimization on a closed convex set)** `K` nonempty
  closed convex in a Hilbert space `V`, `ℓ ∈ V'`, `E(v) = ½||v||^2 − ℓ(v)` ⇒
  ∃! minimizer `u ∈ K`, characterized by the variational inequality
  `(u, v − u) ≥ ℓ(v − u)` for all `v ∈ K`; if `K` is a subspace, by
  `(u,v) = ℓ(v)` for all `v ∈ K` [restates 3.4.3 with Riesz: `E(v) =
  ½||v − w||^2 − ½||w||^2` where `ℓ = (·,w)`].
* **Thm 8.3.3 (Symmetric Lax–Milgram / energy minimization)** `K` nonempty
  closed convex in a Hilbert space `V`; `a` bilinear, symmetric, bounded,
  V-elliptic; `ℓ ∈ V'`; `E(v) = ½a(v,v) − ℓ(v)`. Then ∃! `u ∈ K` minimizing
  `E` over `K` (8.3.2), which is also the unique solution of the variational
  inequality (8.3.3) `u ∈ K, a(u, v − u) ≥ ℓ(v − u) ∀v ∈ K`, and, if `K` is
  a subspace, of the variational equation (8.3.4) `a(u,v) = ℓ(v) ∀v ∈ K`
  [proved: `a` is an inner product with norm equivalent to `||.||`
  (`sqrt α ||v|| ≤ ||v||_a ≤ sqrt M ||v||`); apply 8.3.2 in `(V, (·,·)_a)`].
* **Thm 8.3.4 (Lax–Milgram Lemma)** `V` Hilbert, `a: V × V → R` bounded and
  V-elliptic (not necessarily symmetric), `ℓ ∈ V'` ⇒ ∃! `u ∈ V` with
  `a(u,v) = ℓ(v)` for all `v ∈ V` (8.3.5) [proved twice].
  Proof #1 (Banach fixed point): `P_θ(u)` defined by `(P_θ u, v) = (u,v) −
  θ[a(u,v) − ℓ(v)]` (exists by 8.3.2/Riesz); with `J: V' → V` the Riesz map,
  `P_θ u_1 − P_θ u_2 = (I − θJA)(u_1 − u_2)` and `||(I − θJA)w||^2 ≤ (1 − 2θα
  + θ^2M^2)||w||^2 < ||w||^2` for `θ ∈ (0, 2α/M^2)`; apply Thm 5.1.3.
  Proof #2 (closed range): `L = JA ∈ L(V)`; `||Lw|| ≥ α||w||` ⇒ `R(L)` closed;
  `u ⊥ R(L)` ⇒ `a(u,u) = 0` ⇒ `u = 0`; apply Thm 8.2.1.
  Also Ex 8.3.1: deduce it from Thm 5.1.4 (`T = JA` is strongly monotone and
  Lipschitz), which yields the stability bound `||u|| ≤ ||ℓ||/α`.
  *Generality*: complex version with sesquilinear `a` and `Re a(v,v) ≥
  α||v||^2`; Banach-space version is Thm 8.7.1 (Nečas).
* **Ex 8.3.5** Poisson problem has a unique weak solution.
* 8.4–8.5 (not requested): weak formulations with Dirichlet / Neumann / mixed
  / Robin boundary conditions, general second-order elliptic operators
  (`−Σ∂_j(a_ij ∂_i u) + Σ b_i ∂_i u + cu = f`), Lemma 8.4.1 (a Poincaré-type
  inequality on a quotient space) and linearized elasticity (Thm 8.5.1 via
  Korn's inequality). All need Sobolev spaces, traces and Poincaré/Korn
  inequalities from Ch. 7.

### 8.6 Mixed and dual formulations (brief)
* Model problem `−Δu = f`, `u|_∂Ω = 0`; primal energy `E(v) = ½∫|∇v|^2 − ∫fv`
  (8.6.4); Lagrangian `L(v,q) = ∫[q·∇v − ½|q|^2 − fv]` (8.6.7); dual problem
  (8.6.9) `sup_{q ∈ Q_f} −½∫|q|^2` where `Q_f = {q ∈ L^2(Ω)^d : ∫q·∇v = ∫fv
  ∀v ∈ H_0^1}` (weak `−div q = f`).
* **Def 8.6.1** saddle point of `L: A × B → R`: `L(u,q) ≤ L(u,p) ≤ L(v,p)`
  for all `(v,q)`. **Prop 8.6.2** `(u,p)` is a saddle point iff
  `max_q inf_v L = min_v sup_q L`, attained at `(u,p)` [stated].
* **Thm 8.6.3 (Existence of saddle points)** [quoted; Ekeland–Temam]
  `V, Q` reflexive Banach; `A ⊂ V`, `B ⊂ Q` nonempty closed convex;
  `v ↦ L(v,q)` convex l.s.c. on `A` for each `q`; `q ↦ L(v,q)` concave u.s.c.
  on `B` for each `v`; `A` bounded or ∃`q_0`: `L(v,q_0) → ∞` as `||v|| → ∞`;
  `B` bounded or ∃`v_0`: `L(v_0,q) → −∞` as `||q|| → ∞` (or the `limsup/
  liminf` variants (f'),(g')). Then a saddle point exists; strict convexity /
  concavity give uniqueness of `u` / `p`. Consequences: primal
  `inf_A E`, `E(v) = sup_q L`, and dual `sup_B E^c`, `E^c(q) = inf_v L`, both
  attained with equal values (8.6.14).
* Mixed formulations (8.6.16)–(8.6.19): find `(u,p) ∈ H_0^1 × L^2(Ω)^d` with
  `∫p·q − ∫q·∇u = 0`, `−∫p·∇v = −∫fv`; or `(u,p) ∈ L^2 × H(div;Ω)`. Abstract
  saddle-point framework (8.6.21)–(8.6.22): `V, Q` Hilbert, `a` on `V × V`,
  `b` on `V × Q` bounded bilinear, `f ∈ V'`, `g ∈ Q'`: find `(u,p)` with
  `a(u,v) + b(v,p) = <f,v> ∀v`, `b(u,q) = <g,q> ∀q`. (Brezzi theory referred
  to [43]; not proved.) Ex 8.6.4: Stokes.

### 8.7 Generalized Lax–Milgram Lemma (Nečas; Babuška–Nečas inf–sup)
* **Thm 8.7.1** `U, V` real Hilbert, `a: U × V → R` bilinear, `ℓ ∈ V'`;
  assume constants `M, α > 0` with
  (8.7.1) `|a(u,v)| ≤ M||u||_U||v||_V`;
  (8.7.2) inf–sup: `sup_{0≠v∈V} a(u,v)/||v||_V ≥ α||u||_U` for all `u ∈ U`;
  (8.7.3) `sup_{u∈U} a(u,v) > 0` for every `0 ≠ v ∈ V`.
  Then ∃! `u ∈ U` with `a(u,v) = ℓ(v) ∀v ∈ V` (8.7.4), and (8.7.5)
  `||u||_U ≤ ||ℓ||_{V'}/α` [proved: `A: U → V` with `(Au,v)_V = a(u,v)`,
  `||A|| ≤ M`; (8.7.2) ⇒ `||Au||_V ≥ α||u||_U` ⇒ injective, closed range;
  (8.7.3) ⇒ `R(A)^⊥ = {0}`; conclude by Thm 8.2.1 applied to `Au = Jℓ`].
  Ex 8.7.1: with `U = V` and V-ellipticity, (8.7.2)–(8.7.3) hold with the
  same `α` ⇒ Lax–Milgram. Ex 8.7.2: "very weak" solutions `u ∈ L^2` of the
  Poisson problem with `f ∈ (H^2)'` (e.g. point loads for `d ≤ 3`).
  *Generality*: `U` Banach, `V` reflexive Banach (Banach–Nečas–Babuška); the
  three conditions are equivalent to `A: U → V'` being an isomorphism with
  `||A^{-1}|| ≤ 1/α`.

### 8.8 A nonlinear problem (brief)
* `p`-Laplacian-type problem `−div((1 + |∇u|^2)^{p/2−1}∇u) = f`, `u|_∂Ω = 0`,
  `p ∈ (1,∞)`; `V = W_0^{1,p}(Ω)` with norm `||∇v||_{L^p}` (8.8.5) (equivalent
  to the standard norm), reflexive; `f ∈ V' = W^{−1,p'}`. Weak form (8.8.6)
  `a(u;u,v) = ℓ(v)` with `a(w;u,v) = ∫(1+|∇w|^2)^{p/2−1}∇u·∇v`; energy (8.8.10)
  `E(v) = (1/p)∫(1+|∇v|^2)^{p/2} − ∫fv`.
* **Lemma 8.8.1** `E` coercive (`E(v) ≥ ||v||^p/p − ||f|| ||v||`) [proved].
  **Lemma 8.8.2** `E` continuous [proved via a 1-D integral estimate].
  **Lemma 8.8.3** `E` strictly convex [from Ex 5.3.13]. **Lemma 8.8.4** `E`
  Gâteaux differentiable with `<E'(u),v> = a(u;u,v) − ℓ(v)` (8.8.11) [proved
  via dominated convergence].
* **Thm 8.8.5** for `f ∈ V'`, `p ∈ (1,∞)`: the weak formulation (8.8.6) and
  the minimization (8.8.9) are equivalent and both have a unique solution
  [proved: Thm 3.3.12 (reflexive, coercive, continuous, strictly convex) +
  Thm 5.3.19]. Ex 8.8.3: for `p ≥ 2`, `E` is Fréchet differentiable.
  Infrastructure: `W^{1,p}_0`, its reflexivity, Hölder, dominated convergence.

---

## 9. Chapter 9 — The Galerkin Method and Its Variants (complete)

### 9.1 The Galerkin method
* Setting: `V` Hilbert, `a: V × V → R` bilinear, bounded (9.1.2) with constant
  `M`, V-elliptic (9.1.3) with constant `c_0`; `ℓ ∈ V'`; problem (9.1.1)
  `u ∈ V`, `a(u,v) = ℓ(v) ∀v ∈ V`, uniquely solvable by Lax–Milgram.
* Galerkin problem (9.1.4): `V_N ⊂ V` an `N`-dimensional subspace,
  `u_N ∈ V_N`, `a(u_N, v) = ℓ(v) ∀v ∈ V_N`; uniquely solvable (Lax–Milgram on
  `V_N`). Matrix form (9.1.5) `Aξ = b`, `A_ij = a(φ_j,φ_i)` (stiffness
  matrix), `b_i = ℓ(φ_i)`; symmetric `a` ⇒ symmetric `A`; V-elliptic ⇒ `A`
  positive definite (Ex 9.1.2). If `a` is symmetric, (9.1.1) ⟺ minimizing
  `E(v) = ½a(v,v) − ℓ(v)` (9.1.6)–(9.1.7) and (9.1.4) ⟺ minimizing `E` over
  `V_N` (Ritz method, (9.1.8); Ex 9.1.1).
* **Ex 9.1.1** `−u'' = f` on `(0,1)`, `V_N = span{x^i(1−x)}`: stiffness matrix
  badly conditioned (`cond ≈ 1.1e13` at `N = 10`). **Ex 9.1.2** `V_N =
  span{sin(iπx)}`: `a`-orthogonal basis ⇒ diagonal system; Galerkin solution
  `u_N = ∫ K_N(x,t) f(t)dt` with truncated Green's-function Fourier series
  (9.1.10); Ex 9.1.3.
* **Prop 9.1.3 (Céa's lemma)** `V` Hilbert, `V_N ⊂ V` a subspace, `a`
  bounded (`M`) and V-elliptic (`c_0`), `ℓ ∈ V'`, `u` and `u_N` the solutions
  of (9.1.1) and (9.1.4). Then (9.1.11) `||u − u_N||_V ≤ c inf_{v ∈ V_N}
  ||u − v||_V` with `c = M/c_0` [proved: Galerkin orthogonality (9.1.12)
  `a(u − u_N, v) = 0 ∀v ∈ V_N`; then `c_0||u − u_N||^2 ≤ a(u − u_N, u − u_N) =
  a(u − u_N, u − v) ≤ M||u − u_N|| ||u − v||`]. Symmetric case: `a` is an inner
  product, `||v||_a = sqrt(a(v,v))` equivalent to `||v||`; `u_N` is the
  `a`-orthogonal projection of `u` onto `V_N` and `||u − u_N||_a = inf_{v∈V_N}
  ||u − v||_a` (energy-norm optimality). [Not stated but immediate: in the
  symmetric case `c` can be taken `sqrt(M/c_0)`.]
  *Generality*: `V_N` need not be finite-dimensional (any closed subspace);
  the finite dimension is only used for solvability via Lax–Milgram, which
  works on any closed subspace. The lemma is a statement about
  `a`-orthogonal ("Galerkin") projections in Hilbert spaces.
* **Cor 9.1.4 (Convergence of Galerkin)** under the assumptions of 9.1.3, if
  `V_1 ⊂ V_2 ⊂ …` are finite-dimensional subspaces with `closure(∪ V_n) = V`
  (9.1.13) then `||u − u_n||_V → 0` (9.1.14) [proved: pick `v_n ∈ V_n`,
  `v_n → u`, apply Céa]. Requires `V` separable.
* Ex 9.1.4: Galerkin as an existence proof (bounded `{u_n}` ⇒ weak limit
  solves (9.1.1); strong convergence follows).

### 9.2 The Petrov–Galerkin method
* Setting: `U, V` real Hilbert, `a: U × V → R` bilinear, `ℓ ∈ V'`; problem
  (9.2.1) `u ∈ U`, `a(u,v) = ℓ(v) ∀v ∈ V`; well-posed under (9.2.2) boundedness
  `M`, (9.2.3) inf–sup with constant `α`, (9.2.4) `sup_u a(u,v) > 0` for `v ≠ 0`
  (Thm 8.7.1).
* Petrov–Galerkin scheme (9.2.5): `U_N ⊂ U`, `V_N ⊂ V` with `dim U_N = dim V_N
  = N`; `u_N ∈ U_N`, `a(u_N, v_N) = ℓ(v_N) ∀v_N ∈ V_N`.
* **Thm 9.2.1 (Babuška)** under the above assumptions, if the *discrete
  inf–sup condition* (9.2.6) `sup_{0≠v_N∈V_N} a(u_N,v_N)/||v_N||_V ≥ α_N
  ||u_N||_U ∀u_N ∈ U_N` holds with `α_N > 0`, then (9.2.5) has a unique
  solution and (9.2.7) `||u − u_N||_U ≤ (1 + M/α_N) inf_{w_N∈U_N} ||u − w_N||_U`
  [proved: (9.2.6) ⇒ injectivity ⇒ (square system) unique solvability;
  Galerkin orthogonality (9.2.8) `a(u − u_N, v_N) = 0 ∀v_N ∈ V_N`;
  `α_N||u_N − w_N|| ≤ sup a(u_N − w_N, v_N)/||v_N|| = sup a(u − w_N, v_N)/||v_N||
  ≤ M||u − w_N||`; triangle inequality (9.2.9)].
* **Remark 9.2.2 (Xu–Zikatanov improvement)** (9.2.10) `||u − u_N||_U ≤
  (M/α_N) inf_{w_N} ||u − w_N||_U` [quoted]; for `U = V`, `U_N = V_N` this is
  Céa with `c = M/α_N`. Key ingredient (Kato's lemma): for a Hilbert space `H`
  and a bounded projection `P` with `0 ≠ P ≠ I`, `||P|| = ||I − P||`; applied
  to the Petrov–Galerkin projection `P_N u = u_N`.
* **Cor 9.2.3 (Convergence)** if additionally `α_N ≥ α_0 > 0` uniformly
  (9.2.11) and `U_{N_1} ⊂ U_{N_2} ⊂ …` with `closure(∪U_{N_i}) = U` (9.2.12)
  then `||u − u_{N_i}||_U → 0` [stated]. Remark: convergence only needs
  `max{1, α_N^{-1}} inf_{w_N}||u − w_N|| → 0`; uniform (9.2.13)–(9.2.14)
  `inf_{u_N} sup_{v_N} a(u_N,v_N)/(||u_N|| ||v_N||) ≥ α_0` is the
  *Babuška–Brezzi / inf–sup (LBB) condition*, needed for optimal-order
  estimates and central for mixed FEM.
  *Generality*: `U` Banach, `V` reflexive Banach; for infinite-dimensional
  closed `U_N, V_N` one needs the discrete inf–sup on both sides (or a
  compactness/dimension argument) for solvability.

### 9.3 Generalized Galerkin method (variational crimes; first Strang lemma)
* Problem (9.3.1): `u_N ∈ V_N`, `a_N(u_N, v_N) = ℓ_N(v_N) ∀v_N ∈ V_N`, where
  `V_N` is finite-dimensional but *not necessarily* `⊂ V` (non-conforming
  elements, polygonal domain approximation, quadrature).
* **Thm 9.3.1 (Strang-type estimate)** Assume a discretization-dependent norm
  `||.||_N`, `a_N` and `ℓ_N` are defined on `V + V_N = {v + v_N}`, and there
  are constants `M, α_0, c_0 > 0` independent of `N` with
  `|a_N(w, v_N)| ≤ M||w||_N||v_N||_N ∀w ∈ V + V_N, v_N ∈ V_N`;
  `a_N(v_N,v_N) ≥ α_0||v_N||_N^2 ∀v_N ∈ V_N`; `|ℓ_N(v_N)| ≤ c_0||v_N||_N`.
  Then (9.3.1) has a unique solution and (9.3.2)
  `||u − u_N||_N ≤ (1 + M/α_0) inf_{w_N∈V_N} ||u − w_N||_N + (1/α_0)
  sup_{v_N∈V_N} |a_N(u,v_N) − ℓ_N(v_N)| / ||v_N||_N`
  [proved: Lax–Milgram on `V_N`; `α_0||w_N − u_N||^2 ≤ a_N(w_N − u_N, w_N − u_N)
  = a_N(w_N − u, w_N − u_N) + [a_N(u, w_N − u_N) − ℓ_N(w_N − u_N)]`].
  The first term is the approximation error, the second the *consistency
  error* (how well `u` satisfies the discrete problem). Ex 9.3.1: conforming
  case reduces to Céa.

### 9.4 Conjugate gradient method: variational formulation (detailed)
* Setting: `V` real Hilbert; `a: V × V → R` continuous (9.4.1, constant `M`),
  symmetric (9.4.2), V-elliptic (9.4.3, constant `α`); `ℓ ∈ V'`; problem
  (9.4.4) `a(u,v) = ℓ(v) ∀v`. Riesz representation gives `A ∈ L(V)` and `f ∈ V`
  with `(Au,v) = a(u,v)` (9.4.5), `(f,v) = ℓ(v)` (9.4.6); then `||A|| ≤ M`,
  `A` self-adjoint, `(Av,v) ≥ α||v||^2` (positive definite / coercive),
  `||f|| = ||ℓ||`; (9.4.4) ⟺ `Au = f` (9.4.7).
* **Algorithm 1 (CG for the linear variational problem)**: choose `u_0`;
  residual `r_0 ∈ V` by `(r_0, v) = ℓ(v) − a(u_0, v) ∀v` (i.e. `r_0 = f − Au_0`
  via Riesz); `s_0 = r_0`; for `k ≥ 0`: `α_k = ||r_k||^2 / a(s_k, s_k)`,
  `u_{k+1} = u_k + α_k s_k`, `r_{k+1}` by `(r_{k+1}, v) = ℓ(v) − a(u_{k+1}, v)`,
  `β_k = ||r_{k+1}||^2/||r_k||^2`, `s_{k+1} = r_{k+1} + β_k s_k`. Convergence
  follows from Thm 5.6.1 (with spectral bounds `α ≤ … ≤ M`); stopping
  criterion `||r_{k+1}|| ≤ ε`.
  Note: each residual computation is itself a Riesz representation
  (solving `(r,v) = …` in `V`, e.g. an `H^1` projection) — this is the
  "preconditioned by the `V`-inner product" viewpoint.
* Observation: (9.4.4) ⟺ `min_V E`, `E(v) = ½a(v,v) − ℓ(v)`, with Gâteaux
  derivative `<E'(u), v> = a(u,v) − ℓ(v)`, so `(r_k, v) = −<E'(u_k), v>`
  (the residual is minus the Riesz representative of the gradient).
* **Algorithm 2 (Nonlinear CG for `min_V J`)**, `J: V → R` strictly convex and
  Gâteaux differentiable (unique minimizer by Sec. 3.3): `r_0` by
  `(r_0,v) = −<J'(u_0),v>`, `s_0 = r_0`; `u_{k+1} = u_k + α_k s_k` with `α_k`
  from the exact line search `J(u_k + α_k s_k) = inf_α J(u_k + αs_k)`;
  `(r_{k+1},v) = −<J'(u_{k+1}),v>`; `β_k = ||r_{k+1}||^2/||r_k||^2`
  (Fletcher–Reeves); `s_{k+1} = r_{k+1} + β_k s_k`. Convergence [quoted;
  Glowinski] if `J ∈ C^1(V;R)` is coercive and `J'` is Lipschitz and strongly
  monotone on bounded sets: for each `R` there are `M_R, α_R > 0` with
  `||J'(u) − J'(v)||_{V'} ≤ M_R||u − v||` and `<J'(u) − J'(v), u − v> ≥ α_R
  ||u − v||^2` for `||u||, ||v|| ≤ R`.

---

## Summaries of the remaining chapters (what is there; infrastructure needed)

### Chapter 4 — Fourier Analysis and Wavelets
* 4.1 Fourier series: pointwise convergence (Thm 4.1.1: piecewise continuous
  2π-periodic `f` with one-sided derivatives ⇒ series converges to the
  average of one-sided limits); `L^p` convergence (Thm 4.1.2: `S_N f → f` in
  `L^p` for all `f` iff `sup_N ||S_N||_{L^p→L^p} < ∞` — another
  Banach–Steinhaus corollary); Riesz's theorem for `1<p<∞` mentioned.
* 4.2 Fourier transform: Schwartz space `S(R^d)` (Def 4.2.1), tempered
  distributions (4.2.2), transform on `S'`, Plancherel (Thm 4.2.4: `F` is an
  isometry of `L^2(R^d)` onto itself).
* 4.3 Discrete Fourier transform, inverse (Thm 4.3.2), FFT.
* 4.4 Haar wavelets: nested spaces `V_j`, orthonormal bases (Thm 4.4.1),
  Haar wavelet `ψ`, decompositions `V_{j+1} = V_j ⊕ W_j` (Thms 4.4.2–4.4.4).
* 4.5 Multiresolution analysis (Def 4.5.1: shift/scale invariance, nesting,
  density, trivial intersection), scaling equation, Prop 4.5.2.
* Infrastructure: `L^2` of the circle/line (measure theory), Hilbert bases,
  Schwartz space & distributions. Mathlib has `L^2`, `fourierBasis` on
  `AddCircle`, the Fourier transform on Schwartz functions and Plancherel;
  wavelets/MRA absent. Little of this is needed by Ch. 2/5/8/9.

### Chapter 7 — Sobolev Spaces
* 7.1 weak derivatives (Def 7.1.3, uniqueness Lemma 7.1.4, compatibility with
  classical derivatives 7.1.5, product/chain rules 7.1.10–7.1.12).
* 7.2 `W^{k,p}(Ω)` Banach (Thm 7.2.3), `H^k` Hilbert (Cor 7.2.4), `W_0^{k,p}`
  (Def 7.2.9), fractional order `W^{s,p}` (7.2.10–7.2.13), spaces on
  boundaries.
* 7.3 density of smooth functions (7.3.1–7.3.4), extension operators (7.3.5),
  Sobolev embeddings `W^{k,p} ↪ L^q`, `C^{m,α}` and compact embeddings
  (7.3.7–7.3.10, Rellich–Kondrachov), trace theorem (7.3.11–7.3.12),
  **equivalent norms / generalized Poincaré–Friedrichs** (Thm 7.3.13: seminorms
  `f_j` bounded and vanishing only on … ⇒ `|v|_{k,p} + Σf_j(v)` is an
  equivalent norm; 7.3.14 piecewise version; Cor 7.3.18 Poincaré inequality),
  quotient space `W^{k+1,p}/P_k` with norm `|·|_{k+1,p}` (Thm 7.3.17 — the
  basis of the Bramble–Hilbert lemma used in Ch. 10).
* 7.4 characterization of `H^k(R^d)` via Fourier transform (Thm 7.4.1).
* 7.5 periodic Sobolev spaces `H^s(2π)` via Fourier coefficients (Def 7.5.1,
  Thm 7.5.2), duality, embeddings (Props 7.5.4–7.5.6), trigonometric
  interpolation error `||φ − I_n φ||_r ≤ c n^{r−s}||φ||_s` (Thm 7.5.7),
  spherical harmonics (7.5.8–7.5.10).
* 7.6 integration by parts / Green's formulas (Prop 7.6.1).
* Infrastructure: Lebesgue integration on domains in `R^d`, distributions,
  Lipschitz domains, traces, compact embeddings — essentially all absent from
  Mathlib; this is the largest infrastructure gap and is what makes Ch. 8.4,
  8.5, 10, 11.5, 13 hard to formalize. The *abstract* results of Ch. 8.2–8.3,
  8.7, 9 do not need it.

### Chapter 10 — Finite Element Analysis
* 10.1 1-D examples (linear/high-order elements, condensation, reference
  element). 10.2 finite element definition `(K, P_K, Σ_K)`, affine-equivalent
  elements, unisolvence (Prop 10.2.1), finite element spaces `V_h ⊂ H^1`
  (continuity across faces), Lemma 10.2.2 (scaling of Sobolev seminorms under
  affine maps). 10.3 interpolation error: local estimates on the reference
  element via Bramble–Hilbert (Thm 10.3.3), transfer to `K` (Thm 10.3.4:
  `|v − Π_K v|_{m,K} ≤ c (h_K^{k+1}/ρ_K^m) |v|_{k+1,K}`), global estimates
  for regular families (Def 10.3.6, Cor 10.3.7, Thm 10.3.9:
  `||v − Π_h v||_{m,Ω} ≤ c h^{k+1−m}|v|_{k+1,Ω}`). 10.4 convergence: Céa +
  interpolation ⇒ Thm 10.4.1 `||u − u_h||_1 ≤ c h^k |u|_{k+1}`;
  **Thm 10.4.3 (Aubin–Nitsche)** `||u − u_h||_0 ≤ M ||u − u_h||_1 sup_g
  (1/||g||_0) inf_{v_h} ||φ_g − v_h||_1` with `φ_g` the adjoint solution
  `a(v,φ_g) = (g,v)`, and Cor 10.4.4 `||u − u_h||_0 ≤ c h ||u − u_h||_1 ≤
  c h^{k+1}|u|_{k+1}` under `H^2`-regularity. Abstract parts (Aubin–Nitsche
  duality argument) live in the Hilbert-space Galerkin framework of Ch. 9 and
  can be stated abstractly: for the Galerkin projection `u_h` and any
  bounded functional / auxiliary Hilbert norm, `||e||_H ≤ M ||e||_V ·
  sup_g dist(φ_g, V_h)/||g||_H`. Everything else needs Sobolev spaces and
  polynomial interpolation on simplices.

### Chapter 11 — Elliptic Variational Inequalities and Their Numerical Approximations
* 11.1 obstacle problem and a frictional problem as examples.
* 11.2 **Thm 11.2.1** (extends 5.3.19): `f` convex Gâteaux differentiable,
  `j` convex on convex `K` ⇒ `u` minimizes `f + j` over `K` iff `<f'(u), v−u>
  + j(v) − j(u) ≥ 0 ∀v ∈ K`. **Thm 11.2.2**: `V` Hilbert, `K` closed convex,
  `a` bounded symmetric V-elliptic, `j` convex l.s.c. ⇒ `E = ½a(v,v) + j(v)
  − ℓ(v)` has a unique minimizer on `K`, characterized by `a(u, v−u) + j(v) −
  j(u) ≥ ℓ(v−u) ∀v ∈ K` [from 3.3.12 + 11.2.1].
* 11.3 **Thm 11.3.1 (main EVI theorem)**: `V` real Hilbert, `K` closed convex,
  `A: V → V` strongly monotone and Lipschitz, `j: K → R` convex l.s.c. ⇒ the
  EVI `(A(u), v−u) + j(v) − j(u) ≥ (f, v−u) ∀v ∈ K` has a unique solution,
  Lipschitz in `f` [proved: Banach fixed point on the map `u ↦ w = P_θ u`
  defined by an auxiliary symmetric EVI solved via 11.2.2 — the nonlinear
  analogue of Lax–Milgram proof #1]. **Lemma 11.3.5** proper convex l.s.c.
  `j` is bounded below by a continuous affine functional [proved via
  separation 3.3.7]. **Thm 11.3.6** (first kind, `j = 0`) and **Thm 11.3.7**
  (second kind, `K = V`), **Lemma 11.3.8 (Minty)** `u` solves the EVI iff
  `(A(v), v−u) + j(v) − j(u) ≥ (f, v−u) ∀v ∈ K` (only monotonicity +
  hemicontinuity needed), **Thm 11.3.9** bilinear-form version (generalizes
  Lax–Milgram to closed convex `K` and to nondifferentiable `j`),
  Thm 11.3.12 regularity of the obstacle problem.
* 11.4 numerical approximation: **Thm 11.4.1** abstract convergence of
  `K_h → K` approximations (Mosco-type conditions (a),(b)) [proved via
  boundedness + Minty]; Falk-type error estimates (11.4.7); Thms 11.4.5–11.4.7
  (friction problem, numerical integration of `j`, Céa-type bound
  `||u − u_h|| ≤ c inf_{v_h}(||u − v_h|| + |R_h(v_h,u)|^{1/2})`).
* 11.5 contact problems in elasticity (needs Ch. 7 + 8.5).
* Infrastructure for 11.2–11.4: only Hilbert spaces, convex analysis of
  Ch. 3.3, Ch. 5.1/5.3 — formalizable abstractly. 11.1, 11.3.12, 11.5 need
  Sobolev spaces.

### Chapter 12 — Numerical Solution of Fredholm Integral Equations of the Second Kind
* 12.1 projection methods (collocation, Galerkin) for `(λ − K)u = f`, `K`
  compact on a Banach space `V`, `P_n` bounded projections onto `V_n`:
  discrete problem `(λ − P_nK)u_n = P_nf`. **Thm 12.1.2 (abstract
  convergence)**: `K` bounded, `λ − K` bijective, `||K − P_nK|| → 0` ⇒ for
  `n ≥ N` `(λ − P_nK)^{-1}` exists, `sup_{n≥N}||(λ − P_nK)^{-1}|| < ∞`,
  `u − u_n = λ(λ − P_nK)^{-1}(u − P_nu)` and the two-sided estimate
  `(|λ|/||λ − P_nK||)||u − P_nu|| ≤ ||u − u_n|| ≤ |λ| ||(λ − P_nK)^{-1}||
  ||u − P_nu||` [proved via the geometric series theorem applied to
  `λ − P_nK = (λ−K)[I + (λ−K)^{-1}(K − P_nK)]`; only `||K − P_nK|| <
  1/||(λ−K)^{-1}||` for large `n` is needed]. **Lemma 12.1.3** pointwise
  convergence of bounded operators is uniform on compact sets (UBP +
  Arzelà–Ascoli). **Lemma 12.1.4** `P_n u → u ∀u` and `K` compact ⇒
  `||K − P_nK|| → 0`. 12.2 concrete examples (piecewise linear collocation,
  trigonometric collocation, Galerkin) with rates.
* 12.3 iterated projection methods (`û_n = (f + Ku_n)/λ`), **Lemma 12.3.1**
  `(λ − AB)^{-1}` exists ⇒ `(λ − BA)^{-1} = (I + B(λ − AB)^{-1}A)/λ`;
  superconvergence of iterated Galerkin (Thm 12.3.3 and Sec. 12.3.1 use
  `||K(I − P_n)||` and adjoints via Thm 3.4.7).
* 12.4 Nyström method `K_n u(x) = Σ_j w_j k(x,x_j)u(x_j)`; `K_n → K`
  pointwise but not in norm; **Thm 12.4.3 (perturbation theorem for
  collectively compact approximations)**: `S` compact, `λ − T` bijective,
  `||(T − S)S|| < |λ|/||(λ − T)^{-1}||` ⇒ `(λ − S)^{-1}` exists with
  `||(λ − S)^{-1}|| ≤ (1 + ||(λ−T)^{-1}|| ||S||)/(|λ| − ||(λ−T)^{-1}|| ||(T−S)S||)`
  and `||u − z|| ≤ ||(λ − S)^{-1}|| ||Tu − Su||` [proved via geometric series
  + Fredholm alternative]; **Thm 12.4.4** convergence of Nyström for
  continuous kernels and convergent quadrature; 12.4.3 *collectively compact
  operator approximations* (Anselone): axioms A1–A3 and **Lemma 12.4.7**
  (`(K − K_n)M → 0` for compact `M`, `||(K − K_n)K_n|| → 0`).
* 12.5 product integration for weakly singular kernels (graded meshes),
  12.6 two-grid iteration for Nyström (Thm 12.6.1), 12.7 projection methods
  for nonlinear equations `u = T(u)` (linearization Lemma 12.7.1 via 5.3.11/
  5.3.13; homotopy/rotation argument via 5.5.1; Newton–Kantorovich-type
  convergence).
* Infrastructure: Ch. 2 (compact operators, Fredholm alternative, geometric
  series, UBP), `C(D)` and `L^2` function spaces, quadrature convergence from
  2.4.4, interpolation projections from 3.2/3.6/3.7. The abstract theorems
  12.1.2, 12.1.3, 12.1.4, 12.3.1, 12.4.3, 12.4.7 are pure operator theory and
  belong in the backbone.

### Chapter 13 — Boundary Integral Equations
* Laplace equation in the plane: Green's identities, representation formula,
  Kelvin transform, exterior problems (Thm 13.1.1 existence/uniqueness for
  Dirichlet/Neumann), divergence theorem (Thm 13.1.2); direct BIEs of the
  second kind (double-layer potential, compact operator on `C(S)` for smooth
  curves, solved by Nyström/Fredholm theory of Ch. 2 and 12); first-kind
  equation (single layer) in periodic Sobolev spaces `H^s(2π)` (Ch. 7.5) with
  a Galerkin method (Thm 13.3.x via Lax–Milgram/coercivity of the logarithmic
  kernel). Infrastructure: `C^2` boundary curves, potential theory, `H^s(2π)`.

### Chapter 14 — Multivariable Polynomial Approximations
* Best approximation on the unit ball `B^d` (Thm 14.1.1, Ragozin: Jackson-type
  rate `n^{−k}`), multivariable orthogonal polynomials (Lemma 14.2.1, triple
  recursion 14.2.1), orthogonal projection operator norm `||P_n||_{C→C} = O(n)`
  (Thm 14.2.4), uniform convergence rate (Thm 14.2.5 via the Lebesgue lemma
  again), hyperinterpolation (norm `O(n)`), Galerkin method for `−Δu + γu = f`
  on the ball using `X_n = (1 − |x|^2)P_n` (Lemma 14.4.1: `Δ: X_n → P_n`
  bijective). Infrastructure: multivariate polynomials, integration on balls
  and spheres, Sobolev spaces on the ball.

---

## Structural observations

### S1. Standard functional analysis (likely in Mathlib) vs numerical-analysis-flavoured variants

Legend: **[M]** = standard result, almost certainly in Mathlib (name given
where I am fairly confident; verify); **[M?]** = plausibly in Mathlib in some
form; **[NA]** = numerical-analysis flavoured variant that Mathlib will not
have and which the backbone should provide; **[gap]** = standard FA result not
(or not fully) in Mathlib as far as I know.

**Geometric series / Neumann series**
* Thm 2.3.1 **[M]**: `NormedRing.inverse_one_sub`, `NormedRing.tsum_geometric_of_norm_lt_one`,
  `Units.oneSub` (complete normed ring), and `NormedRing.inverse_add_norm_le`-type
  bounds. The explicit bound `||(I−L)^{-1}|| ≤ 1/(1−||L||)` is essentially
  `NormedRing.norm_inverse_one_sub`/`tsum_geometric` **[M?]**.
* Cor 2.3.3 (`||L^m|| < 1`) **[NA]** (easy consequence; spectral-radius version:
  `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` gives
  `r(L) < 1 ⟺ some ||L^m|| < 1` **[M]**).
* Thm 2.3.5 perturbation with the three explicit bounds (2.3.13)–(2.3.15)
  **[NA]**; the qualitative part "invertibles are open, inverse is continuous"
  **[M]** (`Units.isOpen`, `NormedRing.inverse_continuousAt`,
  `ContinuousLinearEquiv.isOpen`/`ContinuousLinearMap.isOpen_units`-type
  results — verify names). The a priori/a posteriori estimate (2.3.16) and
  "consistency + stability ⇒ convergence" **[NA]**.
* Truncated Neumann series error, Picard iteration `u_n = f + Lu_{n−1}`,
  preconditioned Richardson (Ex 2.3.8, 2.3.10) **[NA]**.

**Baire-category results**
* Open mapping / bounded inverse 2.4.3 **[M]** (`ContinuousLinearMap.isOpenMap`,
  `ContinuousLinearEquiv.ofBijective`, `LinearEquiv.toContinuousLinearEquivOfContinuous`).
* Uniform boundedness 2.4.4 **[M]** (`banach_steinhaus`, `banach_steinhaus_iSup_nnnorm`).
* Banach–Steinhaus convergence criterion 2.4.5 (dense subspace + uniform
  bound ⟺ pointwise convergence) **[M?/NA]**: the ⇐ direction is an easy ε/3
  lemma probably not in Mathlib in this form; worth a backbone lemma
  `tendsto_of_dense_of_bounded`.
* Convergence of quadrature rules (2.4.4): `||L_n|| = Σ|w_i|`, "precision
  → ∞ and bounded weight sums ⇒ convergence", positive weights corollary,
  Newton–Cotes divergence **[NA]**. Needs Weierstrass density (**[M]**:
  `polynomialFunctions_closure_eq_top`, Bernstein).
* Extension theorem 2.4.1 **[M]** (`ContinuousLinearMap.extend`, `DenseInducing.extend`).
* Lax equivalence theorem 6.2.11 **[NA]** (uses only 2.4.1 + 2.4.4).
* Lemma 12.1.3 (pointwise convergence uniform on compacta) **[M?]**
  (`TendstoUniformlyOn` from equicontinuity: `Equicontinuous`,
  `tendstoUniformlyOn_of_...` in Mathlib's equicontinuity library).

**Hahn–Banach / duality**
* Thms 2.5.2, 2.5.5, Cors 2.5.6–2.5.7 **[M]** (`exists_extension_norm_eq`,
  `exists_dual_vector`, `norm_eq_iSup_dual`-style lemma `ContinuousLinearMap.opNorm...`;
  separation 3.3.7 **[M]** `geometric_hahn_banach_compact_closed`).
* Riesz representation 2.5.8 **[M]** (`InnerProductSpace.toDual`,
  `InnerProductSpace.toDualMap`).
* Adjoint 2.6 **[M]** (`ContinuousLinearMap.adjoint`, `IsSelfAdjoint`,
  `adjoint_adjoint`, norm preservation); Thm 2.6.5 (`||L|| = sup|(Lv,v)|` for
  self-adjoint) **[M?]** (numerical radius; possibly missing — small gap).
* Weak convergence, boundedness of weakly convergent sequences 2.7.2 **[M?]**
  (`WeakDual`/`WeakSpace`; sequence-boundedness via Banach–Steinhaus is an easy
  lemma); reflexivity and Eberlein–Šmulian 2.7.5 **[gap]** (Mathlib has
  Banach–Alaoglu `WeakDual.isCompact_polar` but no reflexivity API as far as I
  know; for the backbone, Hilbert spaces suffice: bounded sequences have
  weakly convergent subsequences — can be proved directly from separability +
  diagonal argument, or one can *assume* weak sequential compactness as a
  hypothesis).
* Closed range theorem 8.2.7 **[gap]**; Thm 8.2.1/8.2.4 (closed range +
  trivial orthogonal complement ⇒ surjective; stability estimate + closed ⇒
  closed range) **[NA/easy]** — small lemmas worth having.

**Projection theorem and best approximation**
* Thm 3.4.3 (projection onto closed convex set), Lemma 3.4.1
  (characterization), Cor 3.4.2 **[M]** (`exists_norm_eq_iInf_of_complete_convex`,
  `norm_eq_iInf_iff_real_inner_le_zero`); Prop 3.4.4 (monotone,
  non-expansive) **[M?]** (likely partially present).
* Thm 3.4.6/3.4.7/3.6.9 orthogonal projection onto complete subspace **[M]**
  (`orthogonalProjection`, `orthogonalProjection_minimal`,
  `Submodule.orthogonalProjection` self-adjoint, norm ≤ 1, `K ⊕ K^⊥`).
* Existence of minimizers of coercive convex l.s.c. functionals on reflexive
  spaces (3.3.8, 3.3.10, 3.3.12) **[gap]**; finite-dimensional versions 3.3.13,
  3.3.15, 3.3.16 **[M?]** (compactness in finite dimension + continuity:
  `IsCompact.exists_isMinOn`); Mazur's lemma 3.3.11 **[gap]**; uniqueness via
  strict convexity 3.3.18/3.3.21 **[M?]** (`StrictConvexSpace`,
  `UniformConvexSpace`; Mathlib knows inner product spaces and `lp`/`Lp`
  spaces are uniformly convex — verify for `Lp`).
* Chebyshev equioscillation 3.3.19/3.3.20, Jackson theorems 3.7.1–3.7.2,
  Lebesgue constant asymptotics (3.7.10), (3.7.20), Christoffel–Darboux 3.7.3
  **[gap/NA]**. The abstract *Lebesgue lemma* `||u − Pu|| ≤ (1+||P||) dist(u,S)`
  **[NA]** (trivial, but central to 3.7, 12, 14).
* Bessel/Parseval/Gram–Schmidt (1.3.11, 1.3.12, 1.3.16) **[M]**
  (`Orthonormal.tsum_inner_products_le`, `HilbertBasis`, `gramSchmidt`).

**Compact operators / Fredholm theory**
* Def 2.8.1, Prop 2.8.4 (finite rank ⇒ compact), 2.8.6 (ideal property),
  2.8.7 (closed in norm) **[M]** (`IsCompactOperator`, `IsCompactOperator.comp_clm`,
  `isClosed_setOf_isCompactOperator`, finite-rank ⇒ compact via
  `isCompactOperator_iff_...`/finite-dimensional range — verify).
* Fredholm alternative 2.8.10, Riesz–Schauder 2.8.12, 2.8.14, spectral
  theorem for compact self-adjoint 2.8.15 **[gap]** (Mathlib has the
  finite-dimensional spectral theorem and general spectrum theory
  `spectrum`, `spectrum.isOpen_resolventSet`, resolvent analytic, Gelfand
  formula **[M]**, but no Riesz–Schauder / no infinite-dimensional compact
  spectral theorem as far as I know). The book's generalization "distance to
  compacts `< |λ|`" and Thm 12.4.3 (collectively compact perturbation) are
  **[NA]** but depend on this gap.
* Resolvent 2.9.2 (open resolvent set, continuity/analyticity) **[M]**;
  Riesz projections 2.9.4 **[gap]**.

**Fixed points and nonlinear analysis**
* Banach fixed point 5.1.3 with a priori/a posteriori bounds **[M]**
  (`ContractingWith.exists_fixedPoint`, `ContractingWith.apriori_dist_iterate_fixedPoint_le`,
  `ContractingWith.aposteriori_dist_iterate_fixedPoint_le`,
  `ContractingWith.dist_fixedPoint_fixedPoint_of_dist_le'`); "`T^m`
  contractive" (Ex 5.1.2) **[M?]** (`ContractingWith.fixedPoint` for iterates —
  there is a lemma for `f^[n]` contracting, I believe).
* Thm 5.1.4 strongly monotone + Lipschitz ⇒ bijective (nonlinear
  Lax–Milgram / Zarantonello) **[gap/NA]** — a key backbone theorem (it
  implies Lax–Milgram, the EVI theorem 11.3.1, and gives a convergent
  Richardson iteration with explicit rate).
* Picard–Lindelöf 5.2.4 **[M]** (`IsPicardLindelof`,
  `IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq`) — but Mathlib's
  version is qualitative; the weighted-norm error bounds of the Picard
  iterates **[NA]**. Gronwall **[M]** (`norm_le_gronwallBound_of_norm_deriv_right_le`).
  Nonlinear Volterra/Urysohn theorems 5.2.2–5.2.3 **[NA]** (need `C[a,b]`
  as `BoundedContinuousFunction`/`ContinuousMap` and the Bielecki norm).
* Fréchet derivative, chain/product/sum rules, mean value inequality 5.3.11,
  Taylor remainder 5.3.13, partial derivatives 5.3.15 **[M]** (`HasFDerivAt`,
  `HasFDerivAt.comp`, `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`,
  `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`; Taylor:
  `Convex.taylor_approx_two_segment`-type lemmas exist). Gâteaux derivative
  **[M?]** (`HasLineDerivAt`/`lineDeriv` exist; the "Gâteaux derivative is a
  bounded linear map" notion of the book is not a Mathlib primitive).
* Convexity via Gâteaux derivative 5.3.17–5.3.19 (monotone gradient, first
  order optimality / variational inequality) **[M?/gap]**: Mathlib has
  `ConvexOn` characterizations for real functions (monotone derivative) but
  not the Banach-space `<f'(u), v−u>` form; **[NA]**-worthy.
* Newton local quadratic convergence 5.4.1 and Kantorovich 5.4.2 **[gap]**.
* Brouwer/Schauder 5.5.1/5.5.4 **[gap]** (Brouwer is not in Mathlib as of my
  knowledge).
* CG in Hilbert space 5.6.1–5.6.3, 9.4 **[gap/NA]**.

**Variational problems / Galerkin**
* Lax–Milgram 8.3.4 **[M]** (`IsCoercive.continuousLinearEquivOfBilin`,
  real Hilbert spaces; check whether the complex/sesquilinear version exists).
  The symmetric energy-minimization form 8.3.3 and the closed-convex-set form
  8.3.2 **[M?]** (8.3.2 is the projection theorem in disguise).
* Generalized Lax–Milgram / inf–sup 8.7.1 **[gap]** (`IsCoercive` is the
  special case; BNB not in Mathlib) — a central backbone theorem.
* Céa 9.1.3, Galerkin convergence 9.1.4, Petrov–Galerkin 9.2.1 (+ Xu–Zikatanov
  and Kato's `||P|| = ||I−P||`), Strang 9.3.1, Aubin–Nitsche 10.4.3 **[NA]**.
* Saddle point existence 8.6.3, Brezzi theory **[gap]**.
* EVI theorems 11.2.1, 11.2.2, 11.3.1, 11.3.6–11.3.9, Minty 11.3.8, abstract
  convergence 11.4.1 **[gap/NA]**.

### S2. Dependency graph of the main results (chapters 2, 3, 5, 8, 9; plus 6, 10–12 hooks)

Notation `X ← Y, Z` means the book's proof of `X` uses `Y` and `Z`.
`[ext]` = quoted from the literature (no in-book proof).

```
Ch1 facts:  completeness(1.2.24), Schwarz(1.3.2), parallelogram(1.3.4),
            Bessel/Parseval(1.3.11-12), Heine-Borel(1.6.2)[ext], Arzela-Ascoli(1.6.3)[ext],
            Weierstrass(3.1.1)[ext]

2.2.10 L(V,W) Banach            <- completeness of W
2.3.1  geometric series         <- 2.2.10, 2.2.6 (submultiplicativity)
2.3.3  ||L^m||<1 variant        <- 2.3.1
2.3.5  perturbation theorem     <- 2.3.1
2.4.1  extension theorem        <- completeness of W, density
2.4.3  open mapping             [ext] (Baire)
2.4.4  uniform boundedness      [ext] (Baire)
2.4.5  Banach-Steinhaus         <- 2.4.4 (=>), density + eps/3 (<=)
2.4.4* quadrature convergence   <- 2.4.5, 3.1.1 (Weierstrass), (2.4.4) norm formula
2.5.2/2.5.5 Hahn-Banach         [ext]
2.5.6, 2.5.7                    <- 2.5.5
2.5.8  Riesz representation     <- 3.6.9/3.4.6 (projection theorem)  OR  3.3.12 (minimization)
2.6    adjoint, ||L*||=||L||    <- 2.5.8
2.6.5  ||L||=sup|(Lv,v)|        <- polarization identity, parallelogram law
2.7.2  weak conv => bounded     <- 2.4.4, 2.5.7
2.7.5  reflexive <=> weak seq. compact   [ext]
2.8.1* integral ops compact on C(D)      <- 1.6.3
2.8.4  finite rank => compact   <- 1.6.2
2.8.7  norm-limit of compacts   [ext]
2.8.10 Fredholm alternative     <- 2.3.1, 2.4.3, finite-dim linear algebra, (2.8.7)
2.8.12-2.8.15 Riesz-Schauder / spectral thm   [ext]
2.9.2  resolvent set open       <- 2.3.5
2.9.3-2.9.4 functional calculus, Riesz projections   [ext]

3.3.7  separation               [ext] <- 2.5.5
3.3.8  existence (bounded K)    <- 2.7.5
3.3.10 existence (coercive)     <- 3.3.8
3.3.11 Mazur                    [ext]
3.3.12 main existence/uniq.     <- 3.3.10, 3.3.11 (convex closed => weakly closed; convex lsc => wlsc)
3.3.13 finite-dim version       <- 1.6.2
3.3.14/15/16 best approx exists <- 3.3.12 / 3.3.13
3.3.18, 3.3.21 uniqueness       <- strict convexity of norm^p / strictly normed
3.4.1  variational char.        <- inner product algebra
3.4.2  uniqueness (convex K)    <- 3.4.1
3.4.3  projection theorem       <- 3.3.14 + 3.4.2   OR  parallelogram law + completeness
3.4.4  P_K monotone, nonexp.    <- 3.4.1
3.4.6/3.4.7 orthogonal proj.    <- 3.4.3 (or direct), 3.4.1
3.6.9  orthogonal projection    <- 3.4.7
3.7.x  Lebesgue-constant bounds <- (2.2.8) norm of integral operator, 2.4.5 (divergence), Jackson [ext]

5.1.3  Banach fixed point       <- completeness (closed K in Banach V)
5.1.4  strongly monotone+Lipschitz => bijective   <- 5.1.3, Schwarz
5.2.1-5.2.3 scalar / Urysohn / Volterra           <- 5.1.3 (+ Ex 5.1.2 or weighted norm)
5.2.4  Picard-Lindelof          <- 5.1.3, weighted norm of 5.2.3
5.3.11 mean value inequality    <- 2.5.6, 5.3.7 (chain rule), scalar MVT
5.3.13 Taylor remainder         <- same technique
5.3.15 partial derivatives      <- definitions
5.3.17/18 convexity via f'      <- Gateaux def., scalar MVT
5.3.19 first-order optimality   <- 5.3.17
5.4.1  Newton local convergence <- 2.3.5 (inverse of F'(u) near u*), integral form of 5.3.11, contraction
5.4.2  Kantorovich              [ext]
5.5.1, 5.5.4, 5.5.5             [ext]
5.6.1  CG linear rate           [ext] (Krylov optimality (5.6.14) [ext])
5.6.2  CG superlinear (I-K)     <- (5.6.12),(5.6.14) [ext], 2.8.15, 2.8.12, AM-GM
5.6.3  eigenvalue decay rates   <- 2.8.15, Hilbert-Schmidt identity, Fenyo-Stolle [ext]

6.2.11 Lax equivalence          <- 2.4.1 (extension), 2.4.4 (UBP), density, telescoping identity

8.2.1  R(L)=W <=> closed & R^perp=0      <- 3.3.7 (separation)
8.2.4  closed + stability => well-posed  <- 8.2.1, completeness
8.2.7  closed range theorem     [ext]
8.3.1  operators <-> forms      <- Riesz / definition of V'
8.3.2  quadratic min on convex K<- 3.4.3 (projection theorem) via Riesz
8.3.3  symmetric Lax-Milgram    <- 8.3.2 + norm equivalence
8.3.4  Lax-Milgram              <- proof#1: 5.1.3, 8.3.2, Riesz ; proof#2: 8.2.1 ; Ex 8.3.1: 5.1.4
8.6.3  saddle points            [ext]
8.7.1  generalized Lax-Milgram  <- 8.2.1 (same skeleton as proof#2 of 8.3.4)
8.8.5  nonlinear problem        <- 3.3.12, 5.3.19, Lemmas 8.8.1-8.8.4 (Sobolev facts)

9.1.3  Cea                      <- 8.3.4 (existence of u, u_N), Galerkin orthogonality, ellipticity, boundedness
9.1.4  Galerkin convergence     <- 9.1.3, density
9.2.1  Petrov-Galerkin          <- 8.7.1 (existence of u), discrete inf-sup, Galerkin orthogonality
9.2.2  Xu-Zikatanov constant    [ext] (Kato: ||P||=||I-P||)
9.2.3  PG convergence           <- 9.2.1
9.3.1  Strang                   <- 8.3.4 on V_N, ellipticity of a_N
9.4    CG for a(u,v)=l(v)       <- Riesz (8.3.1), 5.6.1 ; Algorithm 2 <- 3.3.12, 5.3.19, [ext] Glowinski

10.4.1 FEM H^1 estimate         <- 9.1.3 + interpolation estimates (Bramble-Hilbert 7.3.17, scaling)
10.4.3 Aubin-Nitsche            <- Galerkin orthogonality + adjoint problem (8.3.4)
11.2.1 <- 5.3.19 ; 11.2.2 <- 3.3.12, 11.2.1 ; 11.3.5 <- 3.3.7 ; 11.3.1 <- 5.1.3, 11.2.2, 11.3.5 ;
11.3.6/7/9 <- 11.3.1 ; 11.3.8 Minty <- monotonicity ; 11.4.1 <- 11.3.8, boundedness
12.1.2 <- 2.3.1 ; 12.1.3 <- 2.4.4 (+Ascoli) ; 12.1.4 <- 12.1.3 ; 12.3.1 algebra ;
12.4.3 <- 2.3.1, 2.8.10 ; 12.4.4 <- 12.4.3 ; 12.4.7 collectively compact ; 12.7.1 <- 5.3.11, 5.3.13
```

Backbone "spine" suggested by the graph (each layer only needs the previous):
1. Completeness of `L(V,W)` → geometric series → perturbation theorem →
   (a) resolvent openness, (b) Fredholm alternative (with Riesz–Schauder as
   an external interface), (c) projection-method theorem 12.1.2, (d) Newton
   local convergence.
2. Baire results (UBP, open mapping) → Banach–Steinhaus criterion → quadrature
   convergence, Lax equivalence, Lemma 12.1.3/12.1.4, divergence of Fourier /
   interpolation projections (Lebesgue constants).
3. Hahn–Banach → separation → closed-range lemma 8.2.1 → generalized
   Lax–Milgram 8.7.1 → Petrov–Galerkin 9.2.1.
4. Projection theorem on closed convex sets → Riesz → adjoint → Lax–Milgram
   (symmetric via minimization; general via Banach fixed point or 8.2.1) →
   Céa → Galerkin convergence, Strang, Aubin–Nitsche.
5. Banach fixed point → 5.1.4 (strongly monotone + Lipschitz) → Lax–Milgram
   (again), EVI theory (Ch. 11), Picard–Lindelöf, Volterra/Urysohn.
6. Spectral theorem for compact self-adjoint operators (external) → CG
   superlinear convergence for `I − K`.

### S3. The book's conjugate gradient method (5.6, 9.4) versus Saad's matrix CG

**Assumptions used by the book.** `V` real Hilbert (separable, only for the
eigenbasis argument in 5.6.2); `A ∈ L(V)` with
* bounded: `||A|| ≤ M` (from continuity of `a`: `|a(u,v)| ≤ M||u|| ||v||`);
* self-adjoint: `(Au,v) = (u,Av)` (from symmetry of `a`);
* positive definite in the *coercive* sense: `(Av,v) ≥ α||v||^2` for all `v`
  (V-ellipticity of `a`), which is exactly `<Au,u> ≥ c||u||^2`. This is what
  makes `A^{-1}` bounded (`||A^{-1}|| ≤ 1/α` by Thm 5.1.4 / Lax–Milgram) and
  gives the spectrum `σ(A) ⊂ [α, M]`. Mere strict positivity `(Av,v) > 0`
  would *not* suffice in infinite dimensions (e.g. `A = I − K` with `1 ∈
  closure{λ_j}` has unbounded inverse).
In 5.6.2–5.6.3 the extra structure `A = I − K`, `K` compact self-adjoint, is
used (eigenbasis `φ_j`, `λ_j → 0`), with coercivity ⟺ `sup λ_j < 1`.
The 9.4 form is the same algorithm with `A` = Riesz representative of `a`;
no additional assumptions. (Book-internal glitch: (5.6.3) is printed as a
bound on norms `m||v|| ≤ ||v||_A ≤ M||v||` while later `m, M` are used as
spectral bounds; the standard theorem uses `m||v||^2 ≤ (Av,v) ≤ M||v||^2`.)

**Correspondence with Saad (*Iterative Methods for Sparse Linear Systems*, 2nd ed.).**
* *Algorithm.* (5.6.2) / Algorithm 1 of 9.4 is literally Saad's Algorithm
  6.18 (CG): `α_j = (r_j,r_j)/(Ap_j,p_j)`, `x_{j+1} = x_j + α_j p_j`,
  `r_{j+1} = r_j − α_j A p_j`, `β_j = (r_{j+1},r_{j+1})/(r_j,r_j)`,
  `p_{j+1} = r_{j+1} + β_j p_j`, with `p ↔ s`. The book recomputes
  `r_{k+1} = f − Au_{k+1}` instead of the update; equivalent in exact
  arithmetic. In 9.4 the residual is the Riesz representative of
  `ℓ − a(u_k,·)`, i.e. the `V`-inner product acts as a preconditioner
  (Saad Ch. 9: PCG with `M = ` the Gram operator of `V`).
* *Galerkin on Krylov subspaces.* Saad Prop. 6.x / Sec. 6.7: CG = orthogonal
  projection method onto `K_m(A, r_0)` with `L = K` (Galerkin condition
  `r_m ⊥ K_m`), equivalently `x_m` minimizes the A-norm of the error over
  `x_0 + K_m` (Saad Prop. 5.2 / Thm 6.x). The book states exactly these two
  facts: (5.6.12) `u_k ∈ u_0 + K_k(A, r_0)` and (5.6.14) `||u − u_k||_A =
  min_{y ∈ u_0 + K_k(A)} ||u − y||_A`, citing Luenberger. It does *not* derive
  them (no Lanczos / no orthogonality relations proved). Note the link with
  Ch. 9: (5.6.14) says `u_k` is the *Galerkin (Ritz) approximation* of `Au = f`
  in the finite-dimensional subspace `u_0 + K_k`, i.e. Céa's lemma in the
  energy norm with constant 1 — so the backbone can derive the A-norm
  optimality of CG from Prop 9.1.3 (symmetric case) once the Galerkin
  condition `r_k ⊥ K_k` is established.
* *A-norm error minimization and polynomial bounds.* Saad Thm 6.29
  (`||x* − x_m||_A ≤ 2 ((sqrt κ − 1)/(sqrt κ + 1))^m ||x* − x_0||_A`) via
  Chebyshev polynomials on `[λ_min, λ_max]` is the book's (5.6.5) with
  `κ = M/m` (quoted from Patterson). The book's one-step bound (5.6.4)
  `(M−m)/(M+m)` corresponds to Saad's steepest-descent bound
  (Saad Thm 5.9 / (5.24)-type, `(κ−1)/(κ+1)`), and (5.6.6) records that the
  CG rate is better. The superlinear result 5.6.2 is the operator analogue of
  Saad's remarks on clustered eigenvalues / "superlinear convergence of CG":
  the comparison polynomial `Q_k(λ) = Π_{j≤k}(λ − λ_j)/(1 − λ_j)` annihilates
  the `k` largest eigencomponents (Saad's argument that CG converges in at most
  as many steps as there are distinct eigenvalues, here with an infinite,
  accumulating spectrum). In infinite dimensions there is no finite
  termination (Saad's `n`-step property disappears); the book replaces it by
  `(c_k)^k` with `c_k → 0` at rate governed by eigenvalue decay
  (`Σ|λ_j|/(1−λ_j)`, Thm 5.6.3), which has no counterpart in Saad.
* *Three-term recurrences / Lanczos.* Saad derives CG from the Lanczos
  tridiagonalization (Algorithm 6.15 → 6.18, `T_m = L D L^T`) and discusses
  the three-term recurrence for residual polynomials; the book has none of
  this (the only three-term recurrences in the book are for orthogonal
  polynomials, Sec. 3.5, Ex 3.5.5–3.5.6, and Christoffel–Darboux 3.7.3). The
  connection — CG residuals are orthogonal polynomials in `A` w.r.t. the
  spectral measure of `r_0`, hence satisfy a three-term recurrence — is implicit
  in (5.6.12)/(5.6.17) but not made.
* *Convergence via condition number.* Book: `κ = M/m = ||A|| ||A^{-1}|| = Λ/δ`
  (5.6.9); Saad: `κ_2(A) = λ_max/λ_min`. Identical for SPD `A`; the book's
  `cond(L) = ||L|| ||L^{-1}||` (Sec. 2.4.2) is the operator-theoretic version.
* *Nonlinear CG.* Algorithm 2 (9.4) with exact line search and Fletcher–Reeves
  `β_k` is the Hilbert-space version of nonlinear CG (Saad only treats linear
  systems; cf. Glowinski / Nocedal–Wright); convergence quoted under
  coercivity + local Lipschitz/strong monotonicity of `J'`.

**Minimal abstract CG interface for the backbone (from the book).**
Inputs: real Hilbert `V`; `A ∈ L(V)` self-adjoint with `α||v||^2 ≤ (Av,v) ≤
M||v||^2`; `f ∈ V`; `u_0`. Outputs to prove: (i) well-definedness of (5.6.2)
(`(As_k,s_k) > 0` unless `r_k = 0`, in which case `u_k = u`); (ii) Krylov
membership `u_k − u_0 ∈ K_k(A,r_0)` and Galerkin orthogonality `r_k ⊥ K_k`;
(iii) A-norm optimality (via Céa/orthogonal projection in `(V,(·,·)_A)`);
(iv) polynomial bound `||u − u_k||_A ≤ min_{p ∈ P_k, p(0)=1} sup_{λ∈[α,M]}|p(λ)|
· ||u − u_0||_A` (needs a functional calculus for polynomials in a
self-adjoint operator and `||p(A)|| ≤ sup_{σ(A)}|p|`, i.e. the spectral
mapping/norm bound for self-adjoint operators — a **[gap]** item; for the
`I − K` compact case the eigenbasis of 2.8.15 gives it directly);
(v) Chebyshev bound `2((sqrt κ − 1)/(sqrt κ + 1))^k` (Chebyshev polynomials
**[M]**: `Polynomial.Chebyshev.T`, plus the extremal property **[gap]**);
(vi) superlinear bound for `A = I − K` (5.6.2).
