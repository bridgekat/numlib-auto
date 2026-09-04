# Higham, *Accuracy and Stability of Numerical Algorithms* (2nd ed., SIAM 2002) — survey for a Lean 4 / Mathlib floating-point backbone

Source: OCR text `scratchpad/books/accuracy-and-stability-of-numerical-algorithms-higham.txt` (38 839 lines; TOC at lines 40-560; chapter 2 body starts ~line 3280, chapter 3 ~4700, chapter 4 ~5841, chapter 6 ~7440, chapter 7 ~8040, chapter 8 ~9040, chapter 9 ~10080, chapter 10 ~12100, chapter 17 ~18855, chapter 18 ~19845, chapter 19 ~20700). Formulas were reconstructed from the OCR plus knowledge of the book; anything I could not confirm from the text is tagged **[uncertain]**.

Conventions used below (Higham's): a hat denotes a computed quantity; `u` is the unit roundoff; `|A|` is the entrywise absolute value and inequalities between matrices/vectors are entrywise; `γ_n := nu/(1-nu)` (implicitly `nu < 1`); `θ_n` denotes *any* quantity with `|θ_n| ≤ γ_n`; `γ̃_n := cnu/(1-cnu)` for an unspecified small integer constant `c` (eq. (3.8)); `cond(A,x) = ‖ |A⁻¹||A||x| ‖_∞/‖x‖_∞`, `cond(A) = ‖ |A⁻¹||A| ‖_∞`, `κ(A) = ‖A‖‖A⁻¹‖`.

---

## 1. Chapter 2 — Floating Point Arithmetic (detailed)

### 2.1 Floating point number system

**Definition (2.1).** `F = F(β, t, e_min, e_max)` is the set of numbers `y = ± m · β^{e-t}` with integers `m` (significand), `e` (exponent), `0 ≤ m ≤ β^t − 1`, `e_min ≤ e ≤ e_max`. Normalization: for `y ≠ 0` require `m ≥ β^{t-1}` (unique representation). `0` is special. Range of nonzero normalized numbers: `β^{e_min−1} ≤ |y| ≤ β^{e_max}(1 − β^{−t})`. Equivalent positional form (2.2): `y = ±β^e · 0.d_1 d_2 … d_t`, `0 ≤ d_i ≤ β−1`, `d_1 ≠ 0`.

- Machine epsilon `ε_M = β^{1−t}` = distance from 1.0 to the next float. Spacing between 1/β and 1 is `ε_M/β`.
- **Lemma 2.1.** The spacing between a normalized `x ∈ F` and an adjacent normalized float is at least `β^{−1} ε_M |x|` and at most `ε_M |x|`. (Proof: Problem 2.2; direct from the representation — within a binade spacing is `β^{e−t}` and `β^{e−1} ≤ |x| < β^e`.)
- Subnormals: `y = ±m·β^{e_min−t}`, `0 < m < β^{t−1}`; smallest normalized `λ = β^{e_min−1}`, smallest subnormal `μ = β^{e_min−t} = λ ε_M`; they are equally spaced with spacing `λ ε_M`.
- Rounding: let `G ⊃ F` be the numbers of form (2.1) with unrestricted exponent; `fl(x)` = an element of `G` nearest to `x`; ties broken by round-to-even (IEEE default) or round-away. **Rounding is monotone:** `x ≥ y ⇒ fl(x) ≥ fl(y)`. `fl(x)` *overflows* if `|fl(x)| > max{|y| : y ∈ F}`, *underflows* if `0 < |fl(x)| < min{|y| : 0 ≠ y ∈ F}`; underflow is *gradual* if subnormals are included.
- **Unit roundoff** `u := ½ β^{1−t}` (so `u = ε_M/2`).

**Theorem 2.2.** If `x ∈ ℝ` lies in the range of `F` then `fl(x) = x(1+δ)` with `|δ| < u`.
*Proof.* WLOG `x > 0`; write `x = μ·β^{e−t}` with real `μ ∈ [β^{t−1}, β^t)`. Neighbours are `⌊μ⌋β^{e−t}` and `⌈μ⌉β^{e−t}` so `|fl(x) − x| ≤ ½β^{e−t}`; divide by `x ≥ β^{t−1}β^{e−t}` to get `≤ ½β^{1−t} = u`, strict unless `μ = β^{t−1}` in which case `δ = 0`. ∎

**Theorem 2.3.** If `x ∈ ℝ` lies in the range of `F` then `fl(x) = x/(1+δ)` with `|δ| ≤ u`. (Problem 2.4: same argument but divide the absolute error `½β^{e−t}` by `|fl(x)| ≥ β^{e−1}`.)

Remarks: the factor `1+δ` could be replaced by `e^{ε}` (Olver's *relative precision*, §3.4). *Wobbling precision*: relative spacing varies by a factor `β` across a binade, so the actual relative representation error ranges between `β^{−t}` and `β^{1−t}`. `ulp(y) = β^{e−t}`. IEEE single: `β=2, t=24, e_min=−125, e_max=128, u=2^{−24}`; double: `t=53, e_min=−1021, e_max=1024, u=2^{−53} ≈ 1.11e−16`.

### 2.2 Model of arithmetic

**Standard model (2.4).** For `x, y ∈ F`, `op ∈ {+, −, ×, /}`:
`fl(x op y) = (x op y)(1+δ), |δ| ≤ u`, and the same is assumed for `sqrt`.
**Variant (2.5).** `fl(x op y) = (x op y)/(1+δ), |δ| ≤ u`.
Notes made explicit by Higham: (i) `fl(·)` applied to an *expression* means the computed value of that expression; (ii) the model does **not** require `δ = 0` when `x op y ∈ F` (so it does not capture exactness, monotonicity, or Sterbenz); (iii) IEEE arithmetic satisfies (2.4) and (2.5) by Theorems 2.2/2.3 since results are correctly rounded; (iv) "All the error analysis in this book is carried out under (2.4), sometimes making use of (2.5)."

**No-guard-digit model (2.6).** `fl(x ± y) = x(1+α) ± y(1+β)`, `|α|,|β| ≤ u` (the true property for such machines is `αβ = 0, |α|+|β| ≤ u`); `fl(x op y) = (x op y)(1+δ)` for `op ∈ {×, /}`. Most results survive with slightly bigger constants; compensated summation and Kahan's Heron formula do not.

### 2.3 IEEE arithmetic (brief)
IEEE 754-1985: binary, single (32 bit, 23+1 significand bits, 8 exponent bits) and double (64 bit, 52+1, 11); hidden bit. All operations (incl. sqrt) "computed as if to infinite precision and then rounded" under one of four modes (nearest-even default, +∞, −∞, toward zero); this implies (2.4). Closed system: NaN, ±∞, ±0 (with `+0 = −0`), subnormals (gradual underflow), five exceptions (invalid, overflow, divide-by-zero, underflow, inexact) set flags by default. Extended formats (≥ 79 bits, `u ≤ 5.42e−20`); *double rounding* can differ from direct rounding. IEEE 854 (radix-independent, bases 2 and 10). §2.4: Cray machines lacked a guard digit ⇒ model (2.6).

### 2.5 Exact subtraction
**Theorem 2.4 (Ferguson).** If `x, y ∈ F` and `e(x − y) ≤ min(e(x), e(y))`, where `e(·)` is the exponent in normalized representation, then `fl(x − y) = x − y` (barring underflow). *Proof:* the exponents differ by ≤ 1; if equal, the difference is exact; otherwise scale so `β^{−1} ≤ y < 1 ≤ x < β`; the exact difference has leading digit 0 and hence at most `t` significant digits, so rounding is exact. ∎

**Theorem 2.5 (Sterbenz).** If `x, y ∈ F` with `y/2 ≤ x ≤ 2y` then `fl(x − y) = x − y` (barring underflow; with gradual underflow the proviso is unnecessary — Problem 2.19, Hauser). Used to prove Kahan's Heron formula `A = ¼√((a+(b+c))(c−(a−b))(c+(a−b))(a+(b−c)))` (2.7) accurate for `a ≥ b ≥ c` (Problem 2.23).

### 2.6 Fused multiply-add
`fl(x·y + z) = (x·y + z)(1+δ), |δ| ≤ u` — one rounding for two operations. Consequences: an inner product costs `n` instead of `2n−1` rounding errors; Newton reciprocal iteration `x_{k+1} = x_k + (1 − x_k a)x_k` as two FMAs (IA-64 division); **exact product**: `a = fl(xy)`, `b = fl(xy − a)` gives `a + b = xy` exactly (Problem 2.26 — this is a *structural* fact about `F`, not a model consequence); Kahan's 2×2 determinant `w = bc; e = w − bc (FMA); x = (ad − w) + e` has high relative accuracy (Problem 2.27).

§§2.7–2.11 (not needed for the backbone): base choice/Benford distribution; rounding errors are not random (Kahan's `(x+x)−x`, Problem 2.25 `f(x) = (((x−0.5)+x)−0.5)+x ≠ 0`); level-index and logarithmic arithmetic; elementary functions (table maker's dilemma); accuracy tests (Paranoia).

---

## 2. Chapter 3 — Basics (detailed)

### 3.1 Inner and outer products
Recursive evaluation `ŝ_1 = fl(x_1y_1)`, `ŝ_i = fl(ŝ_{i−1} + fl(x_i y_i))`. Expanding with (2.4):
- (3.2)/(3.3): `ŝ_n = x_1y_1(1+θ_n) + x_2y_2(1+θ'_n) + x_3y_3(1+θ_{n−1}) + … + x_ny_n(1+θ_2)` (each `θ_k` a different product of `k` factors `1+δ_i`, bounded via Lemma 3.1).
- **(3.4) Backward error, any evaluation order:** `fl(xᵀy) = (x + Δx)ᵀy = xᵀ(y + Δy)`, `|Δx| ≤ γ_n|x|`, `|Δy| ≤ γ_n|y|` (entrywise).
- **(3.5) Forward error:** `|xᵀy − fl(xᵀy)| ≤ γ_n Σ_i |x_iy_i| = γ_n |x|ᵀ|y|`. High relative accuracy when `y = x` (sum of squares); not in general when `|xᵀy| ≪ |x|ᵀ|y|`.
- Same bounds under the no-guard-digit model (2.6).
- Constants: splitting into `k` blocks gives `γ_{n/k+k−1}`, optimal `k ≈ √n` giving `γ_{2√n−1}`; pairwise summation of the products gives `γ_{⌈log₂n⌉+1}`.
- Extended precision accumulation (`u_e ≪ u`) then one final rounding: `|ŝ_n − xᵀy| ≤ u|xᵀy| + γ^e_n(1+u)|x|ᵀ|y|` [uncertain: exact form], i.e. "as good as the rounded exact inner product" when `n u_e |x|ᵀ|y| ≲ u|xᵀy|`.
- **Outer product (3.6):** `Â = xyᵀ + Δ`, `|Δ| ≤ u|xyᵀ|` — small *forward* error but **not backward stable** (Â is not rank 1). General principle: backward stability is likelier when #outputs ≪ #inputs.

### 3.2 Purpose of rounding error analysis
Existence of an a priori bound is what matters; constants are least important; put bounds in interpretable form; sharp bounds are a posteriori (running error analysis, explicit backward errors, iterative refinement).

### 3.3 Running error analysis
Using (2.5): `z_i := fl(x_iy_i) = x_iy_i/(1+δ_i)` so `x_iy_i = z_i + δ_i z_i`; `(1+ε_i)ŝ_i = ŝ_{i−1} + z_i`. With `e_i := ŝ_i − s_i`: `e_i = e_{i−1} − ε_i ŝ_i − δ_i z_i` [uncertain sign conventions], hence `|e_n| ≤ u μ_n` with `μ_i = μ_{i−1} + |ŝ_i| + |z_i|`, `μ_0 = 0`. **Algorithm 3.2** computes `s` and `μ` simultaneously (`μ = μ + |s| + |z|` each step, then `μ = μ·u`). Key inequality: `|x op y − fl(x op y)| ≤ u|fl(x op y)|` — computable from stored quantities. Rounding errors in computing `μ` are negligible for `nu ≪ 1` (not formalized by Higham).

### 3.4 Notation for error analysis
(3.7): first-order form `|xᵀy − fl(xᵀy)| ≤ nu|x|ᵀ|y| + O(u²)`; Higham warns that `O(u²)` hides structure in vector inequalities.

**Lemma 3.1.** If `|δ_i| ≤ u` and `ρ_i = ±1` for `i = 1:n`, and `nu < 1`, then `∏_{i=1}^n (1+δ_i)^{ρ_i} = 1 + θ_n` where `|θ_n| ≤ nu/(1−nu) =: γ_n`.
*Proof (Problem 3.1):* `(1−u)^n ≤ ∏ ≤ (1−u)^{−n}`; `(1−u)^{−n} − 1 ≤ nu/(1−nu)` because `(1−u)^n ≥ 1 − nu` (Bernoulli); `1 − (1−u)^n ≤ nu ≤ γ_n`. ∎
Problem 3.2 (Kiełbasiński–Schwetlick): if all `ρ_i = 1` then `|θ_n| ≤ nu/(1 − nu/2)` for `nu < 2` [uncertain: the OCR shows "nu/(1−nu) … nu < 2"; the `nu/2` denominator is what the Lemma 3.4 proof technique gives].

**Lemma 3.3.** For positive integers `k`, let `θ_k` denote a quantity with `|θ_k| ≤ γ_k = ku/(1−ku)`. Then (each equation reads "there exists a quantity of the indicated kind"):
1. `(1+θ_k)(1+θ_j) = 1 + θ_{k+j}`;
2. `(1+θ_k)/(1+θ_j) = 1 + θ_{k+j}` if `j ≤ k`, `= 1 + θ_{k+2j}` if `j > k`;
3. `γ_k γ_j ≤ γ_{min(k,j)}` provided `max(j,k)u ≤ 1/2`;
4. `i γ_k ≤ γ_{ik}`;
5. `γ_k + u ≤ γ_{k+1}`;
6. `γ_k + γ_j + γ_kγ_j ≤ γ_{k+j}`.
(Proof: Problem 3.4, elementary.) Remark: a *known product* `∏_{i≤k}(1+δ_i)^{±1}/∏_{i≤j}(1+δ_i)^{±1}` is `1+θ_{k+j}`, but given only the bounds on `θ_k, θ_j` one cannot do better than `θ_{k+2j}` for `j > k`.

(3.8) `γ̃_k := cku/(1−cku)`, `c` a small unspecified integer: e.g. `3γ_n = γ̃_n`, `mγ_n = nγ_m = γ̃_{mn}`, `γ_2 + γ_3(1+γ_5) = γ̃_1`.

**Lemma 3.4 (Forsythe–Moler).** If `|δ_i| ≤ u`, `i = 1:n`, and `nu ≤ 0.01`, then `∏(1+δ_i) = 1 + η_n` with `|η_n| ≤ 1.01 nu`. *Proof:* `(1+u)^n − 1 ≤ nu + (nu)²/2! + … ≤ nu/(1 − nu/2) ≤ nu/0.995 < 1.01nu`, and `1 − (1−u)^n ≤ nu`. ∎ (Wilkinson's version: `nu < 0.1 ⇒ 1.06 nu`.) Gives (3.9): `|xᵀy − fl(xᵀy)| ≤ 1.01 nu |x|ᵀ|y|`.

Other notations: Stewart's counters `<k> = ∏_{i=1}^k(1+δ_i)^{ρ_i}` with `<j><k> = <j+k>`, `<j>/<k> = <j+k>`; Kahan's `[a + [bc]]`; Olver's relative precision `y ≈ x; rp(α)` meaning `y = e^δ x, |δ| ≤ α` (symmetric and additive).

### 3.5 Matrix multiplication
- Matrix–vector, from (3.4): **(3.11)** `ŷ = (A + ΔA)x`, `|ΔA| ≤ γ_n|A|` (`A ∈ ℝ^{m×n}`); **(3.12)** `|y − ŷ| ≤ γ_n|A||x|`; normwise `‖y − ŷ‖_p ≤ γ_n‖A‖_p‖x‖_p` for `p = 1, ∞`, and `‖y − ŷ‖_2 ≤ γ_n ‖|A|‖_2‖x‖_2 ≤ min(m,n)^{1/2} γ_n ‖A‖_2‖x‖_2` via Lemma 6.6.
- "sdot" (inner product) and "saxpy" loop orders commit *identical* rounding errors — rounding-error equivalence of mathematically identical algorithms.
- Matrix–matrix `C = AB`: all six loop orders equivalent; `ĉ_j = (A + ΔA_j)b_j`, `|ΔA_j| ≤ γ_n|A|` (columnwise backward error, but no small backward error for `C` as a whole — Problem 3.5); **(3.13)** `|C − Ĉ| ≤ γ_n|A||B|`; `‖C − Ĉ‖_p ≤ γ_n‖A‖_p‖B‖_p`, `p = 1, ∞, F`. (3.13) is sharp relative to componentwise perturbations of the data.

### 3.6 Complex arithmetic
Model (3.14): `x ± y = (a ± c) + i(b ± d)`; `xy = (ac − bd) + i(ad + bc)`; `x/y = ((ac+bd) + i(bc−ad))/(c²+d²)`.
**Lemma 3.5.** Under (2.4): `fl(x ± y) = (x ± y)(1+δ), |δ| ≤ u`; `fl(xy) = xy(1+δ), |δ| ≤ √2 γ_2`; `fl(x/y) = (x/y)(1+δ), |δ| ≤ √2 γ_4`, where `δ ∈ ℂ`. *Proof:* expand each real op with its own `δ_i`, then `|e|² ≤ γ²((|ac|+|bd|)² + (|ad|+|bc|)²) ≤ 2γ²(a²+b²)(c²+d²)` by Cauchy–Schwarz. ∎ Only accuracy relative to `|x op y|`, not of real/imaginary parts separately. Smith's overflow-avoiding division (27.1) gives the same form with a larger constant. Consequence: essentially all real results transfer to ℂ with larger constants.

### 3.7 Miscellany
- **Lemma 3.6.** If `X_j + ΔX_j ∈ ℝ^{n×n}` satisfy `‖ΔX_j‖ ≤ δ_j‖X_j‖` for a consistent norm, then `‖∏_j(X_j + ΔX_j) − ∏_j X_j‖ ≤ (∏_j(1+δ_j) − 1)∏_j‖X_j‖`. (Induction, Problem 3.9.)
- **Lemma 3.7** [reconstructed; the OCR lost it]. If `‖ΔX_j‖_F ≤ δ_j‖X_j‖_2` then `‖∏(X_j + ΔX_j) − ∏X_j‖_F ≤ (∏(1+δ_j) − 1)∏‖X_j‖_2` (uses `‖AB‖_F ≤ ‖A‖_2‖B‖_F`, Problem 6.5; the point is that for orthogonal `X_j` the product of 2-norms is 1 — used for Householder sequences).
- **Lemma 3.8** [reconstructed]. Componentwise: if `|ΔX_j| ≤ δ_j|X_j|` then `|∏(X_j + ΔX_j) − ∏X_j| ≤ (∏(1+δ_j) − 1)∏|X_j|`.
- **Lemma 3.9 (rank-1 update).** For `a, b, x ∈ ℝ^n`, `ŷ = fl(x − a(bᵀx))` satisfies `ŷ = y + Δy`, `|Δy| ≤ γ_{n+3}(I + |a||bᵀ|)|x|`, hence `‖Δy‖_2 ≤ γ_{n+3}(1 + ‖a‖_2‖b‖_2)‖x‖_2`. *Proof:* `ŵ = (a+Δa)bᵀ(x+Δx)` with `|Δa| ≤ u|a|`, `|Δx| ≤ γ_n|x|`; final subtraction adds `u|·|`; collect with Lemma 3.3. ∎

### 3.8 Error analysis demystified
Any algorithm for `z = f(a)`, `f: ℝ^n → ℝ^m`, is `x_1 = a`, `x_{k+1} = g_k(x_k)` (`k = 1:p`, each `g_k` one flop; `x_k` holds all data so far), `z = I x_{p+1}`. In floating point `x̂_{k+1} = g_k(x̂_k) + Δx_{k+1}`; to first order `ẑ = f(a) + J h` where `J = I[J_p…J_2, J_p…J_3, …, I]` and `h = (Δx_2, …, Δx_{p+1})`. Forward error analysis = bounding products of Jacobians; backward error analysis = solving the underdetermined system `J_f Δa = J h` for a minimum-norm (normwise) or minimum-`‖·‖_∞`-after-scaling (componentwise: `Δa = D e`, `|Δa| ≤ ε|a|`) solution. §3.9: linearized bounds, process graphs, automatic error analysis.

---

## 3. Chapter 4 — Summation

### 4.2 Error analysis (all methods as instances of Algorithm 4.1: repeatedly pick two elements, replace by their sum)
- (4.1) `T̂_i = (X_{i1} + Y_{i1})/(1+δ_i)`, `|δ_i| ≤ u`, `i = 1:n−1` (using (2.5)); local error `δ_i T̂_i`.
- (4.2) `E_n := ŝ_n − s_n = Σ_{i=1}^{n−1} δ_i T̂_i` (summation is linear, so global error = sum of local errors).
- (4.3) `|E_n| ≤ u Σ_{i=1}^{n−1}|T̂_i|` — the smallest possible bound of this form (a running error bound).
- (4.4) `|E_n| ≤ (n−1)u Σ|x_i| + O(u²)`; **backward error:** `ŝ_n = Σ x_i(1+ε_i)`, `|ε_i| ≤ γ_{n−1}` (no `x_i` takes part in more than `n−1` additions).
- (4.6) Pairwise summation: `|E_n| ≤ γ_{⌈log₂n⌉} Σ|x_i|` (each addend in `log₂n` additions).
- Ordering: minimizing `Σ|T̂_i|` is NP-hard; for recursive summation of nonnegative numbers the increasing order minimizes the a priori bound; decreasing order wins under heavy cancellation (example `x = [1, M, 2M, −3M]`); insertion method minimizes (4.3) for nonnegative data.

### 4.3 Compensated summation
- **(4.7) Exact error recovery (Dekker, Knuth, Linnainmaa):** for floats `a, b` with `|a| ≥ |b|`, in *base 2 with round to nearest*, `ŝ = fl(a+b)` and `ê = fl(fl(a − ŝ) + b)` satisfy `ŝ + ê = a + b` exactly; in particular `(a+b) − ŝ ∈ F` (Problem 4.6). This needs the discrete structure of `F` (not a consequence of the standard model; false in some bases and without a guard digit).
- **Algorithm 4.2 (Kahan).** `s = 0; e = 0; for i: temp = s; y = x_i + e; s = temp + y; e = (temp − s) + y`.
- **(4.8) (Knuth; Goldberg's expanded proof):** `ŝ_n = Σ_{i=1}^n (1+μ_i)x_i`, `|μ_i| ≤ 2u + O(nu²)`. Higham notes the proofs "use the model (2.4) with a subtle induction" — i.e. the *bound* is a standard-model consequence, though (4.7) is not; it fails under the no-guard-digit model (2.6). Kahan's variant with final `s = s + e`: `|μ_i| ≤ 2u + O((n−i+1)u²)`.
- (4.9) forward: `|E_n| ≤ (2u + O(nu²))Σ|x_i|` — constant independent of `n` (vs (4.4), (4.6)); still no small relative error when `Σ|x_i| ≫ |Σx_i|`.
- (4.10) Neumaier/Kiełbasiński variant (corrections accumulated separately): `|μ_i| ≤ 2u + O(n²u²)`? — stated as holding for `nu ≤ 0.1` with `|μ_i| ≤ 2.1u` if `n²u ≤ 0.1`. Priest's doubly compensated summation (§4.4): relative error `≤ 2u` [from memory]. Euler's method example: compensated summation flattens the U-shaped error curve.
§§4.4–4.6: other methods, statistical estimates (`√n u` typical), choice of method.

---

## 4. Chapter 6 — Norms (brief)

- Vector norms; Hölder `p`-norms; dual vector `z` with `z*y = ‖z‖_D‖y‖ = 1` (6.3); attainable equivalence (6.4): `‖x‖_{p₂} ≤ ‖x‖_{p₁} ≤ n^{1/p₁ − 1/p₂}‖x‖_{p₂}` for `p₁ ≤ p₂`.
- **Definition 6.1.** A norm on ℂⁿ is *monotone* if `|x| ≤ |y| ⇒ ‖x‖ ≤ ‖y‖`, *absolute* if `‖|x|‖ = ‖x‖`. **Theorem 6.2 (Bauer–Stoer–Witzgall).** Monotone ⇔ absolute.
- Matrix norms: Frobenius; subordinate `‖A‖ = max_{x≠0}‖Ax‖/‖x‖` (6.5); `‖A‖_1` = max column sum, `‖A‖_∞` = max row sum `= ‖|A|e‖_∞`, `‖A‖_2 = ρ(A*A)^{1/2} = σ_max(A)`. Consistency `‖AB‖ ≤ ‖A‖‖B‖` (Frobenius and subordinate norms; the max norm is not consistent: `‖AB‖_M ≤ n‖A‖_M‖B‖_M`). Unitarily invariant norms (2 and F); `‖A*A‖_2 = ‖A‖_2²`. Similarity `X(A+E)X⁻¹` magnifies error by `κ(X)`.
- **Table 6.1** (vector): `‖x‖_p ≤ α_{pq}‖x‖_q` with `α_{12} = α_{1∞} = √n, n` (`‖x‖_1 ≤ √n‖x‖_2 ≤ n‖x‖_∞`), all other constants 1 in the upward direction.
- **Table 6.2** (matrix, `A ∈ ℂ^{m×n}`, norms 1, 2, ∞, F, M = max entry, S = sum of entries): e.g. `‖A‖_2 ≤ √n‖A‖_1`, `‖A‖_2 ≤ √m‖A‖_∞`, `‖A‖_2 ≤ ‖A‖_F ≤ √rank(A)‖A‖_2`, `‖A‖_1 ≤ m‖A‖_M`, `‖A‖_∞ ≤ n‖A‖_M`, `‖A‖_2 ≤ √(mn)‖A‖_M`, `‖A‖_F ≤ √(mn)‖A‖_M`, `‖A‖_M ≤ ‖A‖_{1,2,∞,F}`, `‖A‖_S ≤ mn‖A‖_M`, etc.
- Mixed subordinate norm (6.6) `‖A‖_{α,β} = max ‖Ax‖_β/‖x‖_α`; (6.7) `‖AB‖_{α,β} ≤ ‖A‖_{γ,β}‖B‖_{α,γ}`.
- **Lemma 6.3.** Given `‖x‖_α = ‖y‖_β = 1` there is `B` with `‖B‖_{α,β} = 1` and `Bx = y` (`B = y z*`, `z` dual to `x`).
- **Theorem 6.4.** `κ_{α,β}(A) := lim sup_{ε→0} ‖(A+ΔA)⁻¹ − A⁻¹‖_{β,α}/(ε‖A⁻¹‖_{β,α})` over `‖ΔA‖_{α,β} ≤ ε‖A‖_{α,β}` equals `‖A‖_{α,β}‖A⁻¹‖_{β,α}`.
- **Theorem 6.5 (Gastinel, Kahan).** `dist_{α,β}(A) := min{‖ΔA‖_{α,β}/‖A‖_{α,β} : A + ΔA singular} = κ_{α,β}(A)⁻¹`.
- **Lemma 6.6.** `A, B ∈ ℝ^{m×n}`: (a) if `|A| ≤ B` [uncertain: possibly the weaker "columnwise 2-norm" hypothesis] then `‖A‖_F ≤ ‖B‖_F` and `‖A‖_2 ≤ √rank(B)‖B‖_2`; (b) `|A| ≤ B ⇒ ‖A‖_2 ≤ ‖B‖_2`; (c) `|A| ≤ |B| ⇒ ‖A‖_2 ≤ √rank(B)‖B‖_2`; (d) `‖A‖_2 ≤ ‖|A|‖_2 ≤ √rank(A)‖A‖_2`. (These convert componentwise/columnwise bounds into 2-norm bounds; the `√rank` is sharp.)
- §6.3: (6.12) `max_j‖A(:,j)‖_p ≤ ‖A‖_p ≤ n^{1−1/p}max_j‖A(:,j)‖_p`; (6.13) analogous row bound with `m^{1/p}` and `p/(p−1)`; Schneider–Strang (6.14); `‖A‖_2 ≤ √(‖A‖_1‖A‖_∞)`; Riesz–Thorin `‖A‖_p ≤ ‖A‖_1^{1/p}‖A‖_∞^{1−1/p}` [uncertain numbering]. §6.4 SVD.

---

## 5. Chapter 7 — Perturbation Theory for Linear Systems

### 7.1 Normwise analysis (any vector norm and its subordinate matrix norm; `E`, `f` tolerances)
**Theorem 7.1 (Rigal–Gaches).** `η_{E,f}(y) := min{ε : (A+ΔA)y = b+Δb, ‖ΔA‖ ≤ ε‖E‖, ‖Δb‖ ≤ ε‖f‖}` equals `‖r‖/(‖E‖‖y‖ + ‖f‖)`, `r = b − Ay`. *Proof:* RHS is a lower bound (take norms in `r = ΔAy − Δb`); attained by `ΔA_min = (‖E‖‖y‖/(‖E‖‖y‖+‖f‖)) r zᵀ`, `Δb_min = −(‖f‖/(‖E‖‖y‖+‖f‖)) r`, `z` dual to `y`. ∎ (`E = A, f = b`: normwise relative backward error `η_{A,b}`.)

**Theorem 7.2.** If `Ax = b`, `(A+ΔA)y = b+Δb`, `‖ΔA‖ ≤ ε‖E‖`, `‖Δb‖ ≤ ε‖f‖`, and `ε‖A⁻¹‖‖E‖ < 1`, then
`‖x − y‖/‖x‖ ≤ ε/(1 − ε‖A⁻¹‖‖E‖) · (‖A⁻¹‖‖f‖/‖x‖ + ‖A⁻¹‖‖E‖)`, attainable to first order. *Proof:* from `A(y − x) = Δb − ΔAx + ΔA(x − y)`. ∎ Condition number (7.5) `κ_{E,f}(A,x) = ‖A⁻¹‖‖f‖/‖x‖ + ‖A⁻¹‖‖E‖`; with `E = A, f = b`: `κ(A) ≤ κ_{A,b} ≤ 2κ(A)` and the familiar `‖x−y‖/‖x‖ ≤ 2εκ(A)/(1 − εκ(A))`.

### 7.2 Componentwise analysis
Componentwise backward error (7.7): `ω_{E,f}(y) := min{ε : (A+ΔA)y = b+Δb, |ΔA| ≤ εE, |Δb| ≤ εf}`, `E, f ≥ 0`. Choices: `E = |A|, f = |b|` (componentwise relative; scaling invariant, preserves sparsity); `E = |A|eeᵀ, f = |b|` row-wise; `E = eeᵀ|A|` columnwise; `E = ‖A‖eeᵀ, f = ‖b‖e` normwise up to a constant.
**Theorem 7.3 (Oettli–Prager).** `ω_{E,f}(y) = max_i |r_i|/(E|y| + f)_i`, `r = b − Ay`, with `0/0 = 0`, `ξ/0 = ∞`. *Proof:* lower bound is immediate; attained by `ΔA = D_1 E D_2`, `Δb = −D_1 f` with `D_1 = diag(r_i/(E|y|+f)_i)`, `D_2 = diag(sign(y_i))`. ∎
**Theorem 7.4 (Skeel-type).** If `Ax = b`, `(A+ΔA)y = b+Δb`, `|ΔA| ≤ εE`, `|Δb| ≤ εf`, and `ε‖|A⁻¹|E‖ < 1` for an absolute norm, then `‖x − y‖/‖x‖ ≤ ε/(1 − ε‖|A⁻¹|E‖) · ‖|A⁻¹|(E|x| + f)‖/‖x‖`; attainable to first order for the ∞-norm. Condition numbers (7.11)–(7.14): `cond_{E,f}(A,x) = ‖|A⁻¹|(E|x|+f)‖_∞/‖x‖_∞`; Skeel's `cond(A,x) = ‖|A⁻¹||A||x|‖_∞/‖x‖_∞`, `cond(A) = ‖|A⁻¹||A|‖_∞ ≤ κ_∞(A)`; (7.15) `min{κ_∞(DA) : D diagonal} = cond(A)` (row equilibration); Chandrasekaran–Ipsen inequalities (7.16); Kahan's 3×3 example (7.17) with `κ_∞ = 2(1+ε⁻¹)`, `cond(A) = 3 + (2ε)⁻¹` but `cond(A,x) = 5/2 + ε`. Table 7.1 (four perturbation classes and their condition numbers).

### 7.3 Scaling (brief)
Theorem 7.5 (van der Sluis): row/column equilibration is within `m^{1/p}` / `n^{1−1/p}` of optimal one-sided scaling; Corollary 7.6: for SPD `A`, `D_* = diag(a_ii)^{−1/2}` gives `κ_2(D_*AD_*) ≤ n·min_D κ_2(DAD)`; Theorem 7.7 (Stewart–Sun, Frobenius); Theorem 7.8 (Bauer): `min_{D_1,D_2} κ_∞(D_1AD_2) = ρ(|A⁻¹||A|)` under irreducibility [uncertain which product], attained via Perron vectors.

### 7.4 Matrix inverse
Componentwise condition number (7.25): `μ_E(A) := lim sup ‖ΔX‖_∞/(ε‖X‖_∞)` over `|ΔA| ≤ εE` satisfies `μ_E(A) ≤ ‖|A⁻¹|E|A⁻¹|‖_∞/‖A⁻¹‖_∞`, with equality when `|A⁻¹| = D_1A⁻¹D_2` for signature matrices. Componentwise distance to singularity `d_E(A)` (Rohn: `1/max_{S_1,S_2} ρ_0(S_1A⁻¹S_2E)`, NP-hard); (7.26) `1/ρ(|A⁻¹|E) ≤ d_E(A) ≤ (3+2√2)n/ρ(|A⁻¹|E)` (Demmel; Rump).

### 7.6 Numerical stability (informal definitions)
- *Normwise backward stable*: `η_{A,b}(x̂) = O(u)` (for all `A, b`; "performed in a backward stable manner" for a particular instance).
- *Componentwise backward stable*: `ω_{|A|,|b|}(x̂) = O(u)` — the errors are equivalent to rounding the data.
- *Normwise forward stable*: `‖x − x̂‖/‖x‖ = O(κ(A)u)`; *componentwise forward stable*: `= O(cond(A,x)u)`.
- Table 7.2: componentwise backward ⇒ componentwise forward; componentwise backward ⇒ normwise backward ⇒ normwise forward; componentwise forward ⇒ normwise forward. Examples forward-but-not-backward stable: Cramer's rule (`n = 2`), Gauss–Jordan, seminormal equations. Row-wise backward stability: `η_{|A|eeᵀ,|b|}(x̂) = O(u)`.
- §7.7 practical bounds: (7.27) exact formulas; (7.28)/(7.29) `‖x − x̂‖_∞/‖x‖_∞ ≤ ‖|A⁻¹||r|‖_∞/‖x̂‖_∞` and Lemma 7.9 (this is the best bound of the (7.28) type); (7.30) computed residual `r̂ = r + Δr`, `|Δr| ≤ γ_{n+1}(|A||x̂| + |b|)`; (7.31) strict bound used by LAPACK `xyyRFS`. §7.8 perturbation theory by calculus.

---

## 6. Chapter 8 — Triangular Systems

**Algorithm 8.1** (back substitution) `x_i = (b_i − Σ_{j>i} u_{ij}x_j)/u_{ii}`.
**Lemma 8.2.** If `y = (c − Σ_{i=1}^{k−1} a_ib_i)/b_k` is evaluated as `s = c; for i: s = s − a_ib_i; y = s/b_k`, then `b_k ŷ(1+θ_k) = c − Σ_{i=1}^{k−1} a_ib_i(1+θ_i)`, `|θ_i| ≤ γ_i`. *Proof:* `ŝ = c(1+δ_1)…(1+δ_{k−1}) − Σ a_ib_i(1+ε_i)(1+δ_i)…(1+δ_{k−1})`; `ŷ = ŝ/(b_k(1+δ_k))` by (2.5); divide through by `(1+δ_1)…(1+δ_{k−1})` and apply Lemma 3.1. ∎ (`c` is deliberately unperturbed so that `b` is unperturbed in the theorem.)
**Theorem 8.3.** For Algorithm 8.1: `(U + ΔU)x̂ = b` with `|Δu_{ij}| ≤ γ_{n−i+1}|u_{ii}|` for `i = j`, `γ_{|i−j|}|u_{ij}|` for `i ≠ j` (order-dependent constants).
**Lemma 8.4 (any evaluation order).** If `y = (c − Σ_{i=1}^{k−1}a_ib_i)/b_k` is evaluated in any order, then `b_kŷ(1+θ_k^{(0)}) = c − Σ_{i=1}^{k−1}a_ib_i(1+θ_k^{(i)})`, `|θ_k^{(i)}| ≤ γ_k`; if `b_k = 1` (no division) then `|θ_k^{(i)}| ≤ γ_{k−1}`. ("A formal proof is tedious to write down" — a natural target for formalization: it is a statement about *all* binary evaluation trees.)
**Theorem 8.5.** Let `Tx = b` (`T ∈ ℝ^{n×n}` triangular nonsingular) be solved by substitution with any ordering. Then `(T + ΔT)x̂ = b`, `|ΔT| ≤ γ_n|T|`. *Proof:* apply Lemma 8.4 row by row; each row's `θ`'s perturb only that row of `T`. ∎ (Tiny componentwise relative backward error; forward error then from Theorem 7.4.)

### 8.2 Forward error analysis
- (8.2) `‖x − x̂‖_∞/‖x‖_∞ ≤ cond(T,x)γ_n/(1 − cond(T)γ_n)`; `cond(T,x)` is row-scaling invariant so only "rows with off-diagonal entries large relative to the diagonal" hurt. Example (8.3) `U(α)` (`u_ii = 1, u_ij = −α`): `(U(α)⁻¹)_{ij} = α(1+α)^{j−i−1}` for `j > i`, `cond(U(α)) ~ 2α^{n−1}`. For any `T` the system `Tx = e_1` (upper) has `cond(T,x) = 1`.
- **Lemma 8.6.** If `U` satisfies (8.5) `|u_ii| ≥ |u_ij|` for all `j > i`, then `W = |U⁻¹||U|` (unit upper triangular) satisfies `w_ij ≤ 2^{j−i}` (`j > i`), hence `cond(U) ≤ 2^n − 1`. *Proof:* `V = D⁻¹U`, `|v_ij| ≤ 1`, `|(V⁻¹)_{ij}| ≤ 2^{j−i−1}`. ∎
- **Theorem 8.7.** Under (8.5), `|x_i − x̂_i| ≤ 2^{n−i+1}γ_n max_{j≥i}|x̂_j|`, `i = 1:n` (later components always accurate relative to earlier ones). Applies to the `L` from GEPP/rook/complete pivoting, `U` from rook/complete pivoting, `R` from pivoted Cholesky/QR. Note `cond(Tᵀ)` may be arbitrarily large even if `T` satisfies (8.5).
- **Lemma 8.8.** If `U` is row diagonally dominant (`|u_ii| ≥ Σ_{j>i}|u_ij|`) then `(|U⁻¹||U|)_{ij} ≤ i + j − 1` and `cond(U) ≤ 2n − 1` — such systems are solved to essentially perfect normwise accuracy.
- Comparison matrix (8.7) `M(T)`: `m_ii = |t_ii|`, `m_ij = −|t_ij|`; `|T⁻¹| ≤ M(T)⁻¹`. **Lemma 8.9.** `cond(T,x) ≤ cond(M(T),x) = ‖(2M(T)⁻¹diag(|t_ii|) − I)|x|‖_∞/‖x‖_∞`.
- **Theorem 8.10.** The substitution solution satisfies `|x − x̂| ≤ μ_n M(T)⁻¹|b|` where `μ_n` solves `μ_k = (1+γ_{n+1})μ_{k−1} + γ_{n+1}`, `μ_0 = u`, i.e. `μ_n ≤ (1+u)(1+γ_{n+1})^n − 1 ≈ (n²+ … )u` [uncertain: closed form lost in OCR]. *Proof:* induction on components using an analogue of Lemma 8.4; proved directly, not derivable from Theorem 8.5 (can be much weaker since `‖M(T)⁻¹‖ ≫ ‖T⁻¹‖` is possible).
- **Corollary 8.11.** If `T = M(T)` (triangular M-matrix) and `b ≥ 0` then `|x − x̂| ≤ μ_n |x|` — high relative accuracy in every component (no subtractions of like-signed numbers). Inverse of a triangular M-matrix computable to high relative accuracy.

### 8.3 Bounds for the inverse
- **Theorem 8.12.** For nonsingular upper triangular `U`: `|U⁻¹| ≤ M(U)⁻¹ ≤ W(U)⁻¹ ≤ Z(U)⁻¹`, where `W(U)_{ii} = |u_ii|`, `W(U)_{ij} = −max_{k>i}|u_{ik}|` (`i<j`), and `Z(U)_{ii} = |u_ii|`, `Z(U)_{ij} = −β|u_ii|` with `β = max_i max_{k>i}|u_{ik}|/|u_{ii}|` [uncertain: exact definition of `Z`]. Hence for any `z ≥ 0` and absolute norm `‖|U⁻¹|z‖ ≤ ‖M(U)⁻¹z‖ ≤ ‖W(U)⁻¹z‖ ≤ ‖Z(U)⁻¹z‖`; taking `z = |U|e, |U||x|, e` bounds `cond(U), cond(U,x), κ_∞(U)` at cost `O(n²), O(n), O(1)` flops. **Algorithm 8.13** computes `‖M(U)⁻¹‖_∞ ≥ ‖U⁻¹‖_∞`. Bidiagonal: `|T⁻¹| = M(T)⁻¹`.
- **Theorem 8.14.** Under (8.5), for the 1-, 2-, ∞-norms: `1/min_i|u_ii| ≤ ‖U⁻¹‖ ≤ ‖M(U)⁻¹‖ ≤ ‖W(U)⁻¹‖ ≤ ‖Z(U)⁻¹‖ ≤ 2^{n−1}/min_i|u_ii|` (equalities from the second onwards for `u_ii = 1, u_ij = −1`).
§8.4 parallel fan-in algorithm (forward error bound with `cond`; not backward stable componentwise); §8.5 notes (LAPACK `xTRTRS`, `xTRCON`).

---

## 7. Chapter 9 — LU Factorization and Linear Equations

- **Theorem 9.1.** `A ∈ ℝ^{n×n}` has a *unique* LU factorization iff `A_k = A(1:k,1:k)` is nonsingular for `k = 1:n−1`; if some `A_k` is singular the factorization may exist but is not unique. Algorithm 9.2 (Doolittle, `u_kj = a_kj − Σ_{i<k}l_ki u_ij`, `l_ik = (a_ik − Σ_{j<k}l_ij u_jk)/u_kk`) commits the same rounding errors as classical GE; pivoting = GE on a permuted matrix.
- Componentwise pre-theorem: `|a_kj − Σ_{i=1}^k l̂_ki û_ij| ≤ γ_k Σ_{i=1}^k |l̂_ki||û_ij|` (`j ≥ k`), `|a_ik − Σ_{j=1}^k l̂_ij û_jk| ≤ γ_k Σ_{j=1}^k|l̂_ij||û_jk|` (`i > k`), from Lemma 8.4.
- **Theorem 9.3.** If GE on `A ∈ ℝ^{m×n}` (`m ≥ n`) runs to completion, the computed factors satisfy `L̂Û = A + ΔA`, `|ΔA| ≤ γ_n|L̂||Û|`.
- **Theorem 9.4.** For `A ∈ ℝ^{n×n}`, GE + substitution gives `(A + ΔA)x̂ = b`, `|ΔA| ≤ γ_{3n}|L̂||Û|`. *Proof:* `(L̂+ΔL)(Û+ΔU)x̂ = b` with `|ΔL| ≤ γ_n|L̂|`, `|ΔU| ≤ γ_n|Û|` (Theorem 8.5); `ΔA = ΔA_1 + L̂ΔU + ΔLÛ + ΔLΔU`, bounded by `(γ_n + 2γ_n + γ_n²)|L̂||Û| ≤ γ_{3n}|L̂||Û|` via Lemma 3.3. ∎
- Interpretation: stability governed by `|L̂||Û|` not by the multipliers. If `L, U ≥ 0` (e.g. totally nonnegative `A`): (9.8)–(9.9) `|L̂||Û| ≤ |A|/(1−γ_n)`, so `|ΔA| ≤ (γ_{3n}/(1−γ_n))|A|` — componentwise backward stable. (For inverses of totally nonnegative matrices `|A| = |L||U|` too.)
- Growth factor `ρ_n := max_{i,j,k}|a_ij^{(k)}| / max_{i,j}|a_ij|`; with partial pivoting `|l_ij| ≤ 1` and `|u_ij| ≤ 2^{i−1}max_k|a_kj|`.
- **Theorem 9.5 (Wilkinson).** GEPP: `(A + ΔA)x̂ = b`, `‖ΔA‖_∞ ≤ n²γ_{3n}ρ_n‖A‖_∞` (from `‖|L̂||Û|‖_∞ ≤ ‖L̂‖_∞‖Û‖_∞ ≤ n · nρ_n‖A‖_∞`; Higham admits the "illicit manoeuvre" of using bounds valid for the exact `L, U`).
- **Lemma 9.6.** For GE without pivoting: `‖|L||U|‖_∞ ≤ (1 + 2(n²−n)ρ_n)‖A‖_∞`.
- Bounds: `ρ_n ≤ 2^{n−1}` (partial pivoting, attained by Wilkinson's matrix); **Theorem 9.7 (Higham–Higham)** characterizes all real matrices with `ρ_n^p = 2^{n−1}`: `A = DMD · [T, θd; 0, α]`-type products [uncertain: exact block form] with `D = diag(±1)`, `M` unit lower triangular with `m_ij = −1` (`i > j`), `T` an arbitrary nonsingular upper triangular matrix of order `n−1`, `d = (1,2,4,…,2^{n−1})ᵀ`, `α = |a_{1n}| = max|a_ij|` (no interchanges occur, every multiplier is `±1`); **Theorem 9.8 (Higham–Higham)** lower bound `ρ_n ≥ θ := (αβ)⁻¹` with `α = max|a_ij|`, `β = max|(A⁻¹)_ij|`, `θ ≤ n`, for any pivoting (examples: sine matrix `(n+1)/2`, Hadamard `n`, Fourier `n`); complete pivoting: Wilkinson's `ρ_n ≤ n^{1/2}(2·3^{1/2}⋯n^{1/(n−1)})^{1/2} ~ n^{1/2 + ¼log n}` and Gould's counterexample to `ρ_n ≤ n`; rook pivoting `ρ_n ≤ 1.5n^{(3/4)log n}`; Trefethen–Schreiber statistical `n^{2/3}` / `n^{1/2}`.
- §9.5: **Theorem 9.9 (Wilkinson)** diagonally dominant by rows or columns ⇒ `ρ_n ≤ 2` without pivoting (column dominance ⇒ partial pivoting does no interchanges); **Theorem 9.10** upper Hessenberg ⇒ `ρ_n ≤ n`; **Theorem 9.11 (Bohte)** bandwidths `p` ⇒ `ρ_n ≤ 2^{2p−1} − (p−1)2^{p−2}`. §9.6 tridiagonal: **Theorems 9.13/9.14** for (a) row/column diagonally dominant, (b) SPD, (c) M-matrix, (d) totally nonnegative: `|L̂||Û| ≈ |A|` and `(A+ΔA)x̂ = b`, `|ΔA| ≤ c u|A|` with `c ≈ 4` [uncertain constant]. §9.7 more bounds (`|ΔA| ≤ ...` in terms of `|A|` with `ρ_n`; Amodio–Mazzia / Chan–Foulser). §9.8 scaling & pivoting choice; §9.9 variants (Crout, outer-product, left-looking share the same bound). §9.10 a posteriori tests (`‖|L̂||Û|‖/‖A‖`). §9.11 **Theorem 9.15 (Barrlund, Sun)** perturbation of LU factors: `‖ΔL‖_F/‖L‖_2, ‖ΔU‖_F/‖U‖_2 ≲ κ-type quantities × ‖ΔA‖`, first order. §9.12 rank-revealing LU; §9.13 history (Hotelling's pessimism, von Neumann–Goldstine, Turing, Wilkinson).

---

## 8. Chapter 10 — Cholesky Factorization

- **Theorem 10.1.** SPD `A` has a unique upper triangular `R` with positive diagonal and `A = RᵀR` (constructive induction: `R_{n−1}ᵀr = c`, `β² = α − rᵀr > 0` by `det`). Algorithm 10.2 (jik form): `r_ij = (a_ij − Σ_{k<i}r_ki r_kj)/r_ii`, `r_jj = (a_jj − Σ_{k<j}r_kj²)^{1/2}`; `n³/3` flops. `LDLᵀ` variant.
- (10.4) `|a_ij − Σ_{k=1}^i r̂_ki r̂_kj| ≤ γ_{i+1}Σ_{k=1}^i|r̂_ki||r̂_kj|` [uncertain: `γ_i` vs `γ_{i+1}`], and for the diagonal via a square-root analogue of Lemma 8.4 (Problem 10.3) `|a_jj − Σ_{k=1}^j r̂_kj²| ≤ γ_{j+1}Σ_{k=1}^j r̂_kj²`.
- **Theorem 10.3.** If Cholesky on SPD `A` runs to completion, `R̂ᵀR̂ = A + ΔA`, `|ΔA| ≤ γ_{n+1}|R̂ᵀ||R̂|`.
- **Theorem 10.4.** With the two triangular solves: `(A + ΔA)x̂ = b`, `|ΔA| ≤ γ_{3n+1}|R̂ᵀ||R̂|` (proof as Theorem 9.4).
- Normwise consequence ("perfect normwise backward stability"): `‖|Rᵀ||R|‖_2 ≤ ‖|R|‖_2² ≤ n‖R‖_2² = n‖A‖_2` (Lemma 6.6(d)); for the computed factor `‖|R̂ᵀ||R̂|‖_2 ≤ n‖A‖_2/(1 − nγ_{n+1})`; so `‖ΔA‖_2 ≤ nγ_{3n+1}‖A‖_2/(1 − nγ_{n+1}) ≤ c n²u‖A‖_2` assuming `max((3n+1)u, nγ_{n+1}) < 1/2`. Growth factor for GE on SPD is exactly 1 (Problem 10.4); multipliers can be huge with no effect. `ΔA` is not symmetric in general (Problem 7.12).
- **Theorem 10.5 (Demmel).** `R̂ᵀR̂ = A + ΔA` with `|ΔA| ≤ (1 − γ_{n+1})⁻¹γ_{n+1} d dᵀ`, `d_i = a_ii^{1/2}`. *Proof:* `‖r̂_i‖_2² = a_ii + Δa_ii ≤ a_ii + γ_{n+1}‖r̂_i‖²`, so `‖r̂_i‖² ≤ (1−γ_{n+1})⁻¹a_ii`, then Cauchy–Schwarz `(|R̂ᵀ||R̂|)_{ij} ≤ ‖r̂_i‖‖r̂_j‖`. ∎
- Scaling `A = DHD`, `D = diag(A)^{1/2}`; Corollary 7.6 ⇒ `κ_2(H) ≤ n·min_F κ_2(FAF) ≤ nκ_2(A)`; `1 ≤ ‖H‖_2 ≤ n`.
- **Theorem 10.6 (Demmel, Wilkinson).** If Cholesky succeeds, `‖D(x − x̂)‖_2/‖Dx‖_2 ≤ ε κ_2(H)/(1 − εκ_2(H))` with `ε = n(1−γ_{n+1})⁻¹γ_{3n+1}`. *Proof:* `(A+ΔA)x̂ = b` with `ΔA = ΔA_1 + Δ_1R̂ + R̂ᵀΔ_2 + Δ_1Δ_2`; scale by `D⁻¹`; `‖D⁻¹ΔAD⁻¹‖_2 ≤ (γ_{n+1}/(1−γ_{n+1}))‖eeᵀ‖_2 + (2γ_n + γ_n²)‖D⁻¹|R̂ᵀ||R̂|D⁻¹‖_2 ≤ n(1−γ_{n+1})⁻¹γ_{3n+1}` using (10.8) and Lemma 3.3. ∎ (Components of `x` obtained to good relative accuracy when `H` is well conditioned even if `κ_2(D)` is huge.)
- **Theorem 10.7 (Demmel) — when Cholesky succeeds.** With `A = DHD`: if `λ_min(H) > nγ_{n+1}/(1 − γ_{n+1})` then Cholesky succeeds (barring under/overflow) and produces nonsingular `R̂`; if `λ_min(H) ≤ −nγ_{n+1}/(1 − γ_{n+1})` it is certain to fail. Weakened: success if `κ_2(H) nγ_{n+1}/(1 − γ_{n+1}) < 1` (since `‖H‖_2 ≥ 1`). Wilkinson's original: success if `20n^{3/2}κ_2(A)u ≤ 1`. *Proof:* induction on stages; Theorem 10.5's error analysis remains valid even if a computed `r̂_kk` would be imaginary; `λ_min(D_k⁻¹(A_k+ΔA_k)D_k⁻¹) ≥ λ_min(H_k) − kγ_{k+1}/(1−γ_{k+1}) > 0` by eigenvalue interlacing, so `A_k + ΔA_k` is positive definite and `R̂_k` real. ∎ (Formal note: needs "runs to completion" = every square-root argument positive, and the algorithm is scale invariant for power-of-`β` scalings.)
- §10.2 **Theorem 10.8 (Sun)** perturbation of the Cholesky factor: for symmetric `ΔA` with `‖A⁻¹ΔA‖_2 < 1`, `‖ΔR‖_F/‖R‖_2 ≤ 2^{−1/2}κ_2(A)ε/(1 − κ_2(A)ε)` [uncertain constant], `ε = ‖ΔA‖_2/‖A‖_2`, plus a first-order `triu(·)` expression.
- §10.3 semidefinite: **Theorem 10.9** existence (pivoted `Πᵀ A Π = RᵀR` with `R = [R_11 R_12; 0 0]`); Lemmas 10.10–10.13 on Schur complements `S_k(A)`; **Theorem 10.14** backward error of pivoted outer-product Cholesky on rank-`r` semidefinite `A` (a bound of the form `‖A − R̂ᵀR̂‖_2 ≤ c_r u (1 + ‖W‖_2)² ‖A‖_2`-type with `W = R_11⁻¹R_12` and `‖W‖_2 ≤ ((n−r)(4^r−1)/3)^{1/2}` [uncertain: exact form]), "just about the best result that could have been expected". §10.4 matrices with positive definite symmetric part (GE without pivoting stable iff `‖S‖‖A⁻¹‖`-type quantity modest).

---

## 9. Chapter 17 — Stationary Iterative Methods

No numbered theorems in this chapter; the results are the numbered inequalities (17.8), (17.13), (17.15), (17.19), (17.20), (17.31), (17.32) (from Higham–Knight 1993a,b).

**Setting.** `A = M − N` nonsingular, `M` nonsingular, `ρ(G) < 1` with `G := M⁻¹N`; iteration `Mx_{k+1} = Nx_k + b`. `c_n` denotes a constant of order `n`.

**Error model (17.1)–(17.2).** The computed iterates satisfy `(M + ΔM_{k+1})x̂_{k+1} = Nx̂_k + b + f_k`, written as
`M x̂_{k+1} = N x̂_k + b + ξ_k`, `ξ_k = ΔM_{k+1}x̂_{k+1} − f_k`.
Assume `M` triangular (Jacobi, Gauss–Seidel, SOR, Richardson) so `|ΔM_{k+1}| ≤ c_n u|M|` (Theorem 8.5) and `f_k` collects the errors in forming `Nx̂_k + b` ((3.11)); hence
**(17.2)** `|ξ_k| ≤ c_n u(|M||x̂_{k+1}| + |N||x̂_k| + |b|)`.
This is the whole interface to floating point; everything after is exact algebra on a perturbed recurrence.

**Forward error.** (17.3) `x̂_{m+1} = G^{m+1}x̂_0 + Σ_{k=0}^m G^kM⁻¹(b − ξ_{m−k})`; (17.4) `x = G^{m+1}x + Σ G^kM⁻¹b`; (17.5) `e_{m+1} := x − x̂_{m+1} = G^{m+1}e_0 + Σ_{k=0}^m G^kM⁻¹ξ_{m−k}`; (17.6) `|e_{m+1}| ≤ |G^{m+1}e_0| + Σ_k |G^kM⁻¹|μ_{m−k}` (`μ_k` the bound in (17.2)). First term = exact-arithmetic error (negligible for large `m`); the second determines the *limiting accuracy*.
- Normwise, with (17.7) `γ_x := sup_k ‖x̂_k‖_∞/‖x‖_∞`:
  **(17.8)** `‖e_{m+1}‖_∞ ≤ ‖G^{m+1}e_0‖_∞ + c_n u(1+γ_x)(‖M‖_∞ + ‖N‖_∞)‖x‖_∞ Σ_{k=0}^∞ ‖G^kM⁻¹‖_∞` (sum converges since `ρ(G) < 1`, Problem 17.1). If `‖G‖_∞ = q < 1`: `… ≤ … ‖M⁻¹‖_∞/(1−q)`.
- Componentwise, with (17.9) `θ_x := sup_k max_i |(x̂_k)_i|/|x_i|` (so `|x̂_k| ≤ θ_x|x|`): (17.10) `|ξ_k| ≤ c_n u(1+θ_x)(|M|+|N|)|x|`; (17.11) `|e_{m+1}| ≤ |G^{m+1}e_0| + c_n u(1+θ_x)Σ_{k=0}^m|G^kM⁻¹|(|M|+|N|)|x|`; since `Σ_k G^kM⁻¹ = (I−G)⁻¹M⁻¹ = A⁻¹`, define **(17.12)** `c(A) := min{ε : Σ_{k≥0}|(M⁻¹N)^kM⁻¹| ≤ ε|Σ_{k≥0}(M⁻¹N)^kM⁻¹| = ε|A⁻¹|} ≥ 1`. Final bound
  **(17.13)** `|e_{m+1}| ≤ |G^{m+1}e_0| + c_n u(1+θ_x)c(A)|A⁻¹|(|M|+|N|)|x|`, and **(17.15)** `‖e_{m+1}‖_∞ ≤ ‖G^{m+1}e_0‖_∞ + c_n u(1+θ_x)c(A)‖|A⁻¹|(|M|+|N|)|x|‖_∞`.
  If `θ_x c(A) = O(1)` and `|M| + |N| ≤ α|A|` with `α = O(1)`, this is `c_n cond(A,x)u` as `m → ∞`: **componentwise forward stability**. Scale invariance when `M, N` are entrywise multiples of `A` (Jacobi, SOR; not Richardson).
- `c(A)`: `= 1` if `M⁻¹ ≥ 0` and `M⁻¹N ≥ 0` (e.g. M-matrices with Jacobi/GS/SOR `0 ≤ ω ≤ 1`); can be infinite (Jacobi/GS on `a_ij = min(i,j)`, `n ≥ 3`); for diagonal `G` with eigenvalues `λ_i`, `c(A) = max_i|1−λ_i|/(1−|λ_i|)`, giving the heuristic **(17.14)** `c(A) ≳ max_i |1−λ_i(G)|/(1 − |λ_i(G)|)`. `θ_x` can be redefined via `(|M|+|N|)|x̂_k|` to avoid zero components (bounds hold with `2θ_x`).
- §17.2.1 Jacobi (`M = D`, `|M|+|N| = |A|`): **(17.16)** `‖e_{m+1}‖_∞ ≤ ‖G^{m+1}e_0‖_∞ + c_n u(1+θ_x)c(A)‖|A⁻¹||A||x|‖_∞`; M-matrix ⇒ `c(A) = 1` ⇒ componentwise forward stable. Woźniakowski's 3×3 example `a = 1/2 − ε`: `c(A) ≈ (3ε)⁻¹` explains instability (Tables 17.2/17.3 show the predicted factor-8 growth).
- §17.2.2 SOR (`M = ω⁻¹(D + ωL)`, `N = ω⁻¹((1−ω)D − ωU)`): (17.17) `|M| + |N| ≤ ((1 + |1−ω|)/ω)|A| =: f(ω)|A|`, `f(ω) = 1` on `[1,2]`, `→ ∞` as `ω → 0`; M-matrix and `0 ≤ ω ≤ 1` ⇒ `c(A) = 1`. Gauss–Seidel (`ω = 1`) has the same form of bound as Jacobi.

**Backward error (§17.3).** `r_{m+1} = b − Ax̂_{m+1}`; with `H := NM⁻¹` (`AG^k = H^kA`): **(17.18)** `r_{m+1} = H^{m+1}r_0 + Σ_{k=0}^m H^k(I−H)ξ_{m−k}`; **(17.19)** `‖r_{m+1}‖_∞ ≤ ‖H^{m+1}r_0‖_∞ + c_n u(1+γ_x)(‖M‖_∞ + ‖N‖_∞)‖x‖_∞ σ`, `σ := ‖Σ_{k≥0}|H^k(I−H)|‖_∞`; `σ ≤ ‖I−H‖_∞/(1−q)` if `‖H‖_∞ = q < 1`; if `H = XDX⁻¹` diagonalizable, **(17.20)** `σ ≤ κ_∞(X) max_i |1−λ_i|/(1−|λ_i|)` (`λ_i = λ_i(M⁻¹N)`; real eigenvalues near `+1` are harmless). So for large `m` the normwise backward error `η_{A,b}(x̂_m) ≲ c_n u(1+γ_x)σ(‖M‖_∞+‖N‖_∞)/‖A‖_∞`, and `‖M‖+‖N‖ ≤ 2‖A‖` for Jacobi/GS/SOR (`ω ≥ 1`). No useful componentwise residual bound. SOR example of Hammarling–Wilkinson: `c(A) = O(10^{45})`, `σ = O(10^{30})`, `κ_∞(A) ≈ 5` — divergence from nonnormality (powers of `G` reach `10^{28}`); pseudospectra explain it (§18.3).

**Singular systems (§17.4).** Drazin inverse `A^D`, index; `G` *semiconvergent* iff `lim G^m` exists iff `G = P[I 0; 0 Γ]P⁻¹`, `ρ(Γ) < 1` iff `index(I−G) = 1`; (17.25) `lim G^m = I − (I−G)^D(I−G)`; (17.26) limit `x = (I − (I−G)^D(I−G))x_0 + (I−G)^D M⁻¹b`. Error split into `range(I−G)`/`null(I−G)` parts: **(17.31)** normwise bound with an extra term growing like `(m+1)‖(I−E)M⁻¹‖_∞` (linear growth of the null-space component), `E := (I−G)^D(I−G)`; **(17.32)** componentwise analogue with `c(A)` redefined via `Σ G^iE = (I−G)^D`; conditions for componentwise forward stability. §17.5 stopping criteria: (17.33a–c) `‖r‖ ≤ ε‖b‖`, `‖r‖ ≤ ε‖A‖‖y‖`, `‖r‖ ≤ ε(‖A‖‖y‖ + ‖b‖)` ⇔ backward errors (Theorem 7.1); the third is preferred; a mat-vec has `|ΔA| ≤ γ_m|A|` (`m` = max nonzeros per row) so componentwise backward error below `γ_m` is unattainable.

---

## 10. Chapter 18 — Matrix Powers

### 18.1 Exact arithmetic
- Jordan form (18.1) `A = XJX⁻¹`, `J = diag(J_1,…,J_s)`, `J_i` of size `n_i` with eigenvalue `λ_i`. `A^k → 0 ⇔ ρ(A) < 1` ("convergent"); `ρ(A) > 1 ⇒ ‖A^k‖ → ∞`; `ρ(A) = 1`: diverges if some `|λ| = 1` is defective, does not converge if a nondefective `λ ≠ 1` with `|λ| = 1`, converges to nonzero if the only unimodular eigenvalue is a nondefective 1.
- **Gelfand:** `ρ(A) = lim_{k→∞}‖A^k‖^{1/k}` for any norm. Lower bound `ρ(A)^k ≤ ‖A^k‖` (consistent norm).
- The "hump" `max_k‖A^k‖` is arbitrarily large for convergent nonnormal `A` (e.g. `J = [λ α; 0 λ]`: `‖J^{k+1}‖_∞/‖J^k‖_∞ = λ(1 + (k+1)α)/(1+kα)`, increasing until `k > λ/(1−λ) − 1/α`; hump `≈ α/(pe·log p)`-type expression with `p = λ⁻¹`). For normal `A`, `‖A^k‖_2 = ρ(A)^k`.
- Bounds: `‖A^k‖ ≤ ‖A‖^k`; numerical radius `‖A^k‖_2 ≤ 2r(A)^k`; diagonalizable (18.4) `‖A^k‖_p ≤ κ_p(X)ρ(A)^k`; defective (18.5) `‖A^k‖ ≤ κ(X)‖δ⁻¹J-scaled‖…` — precisely, with `XJX⁻¹` the Jordan form of `δ⁻¹A`: `‖A^k‖ ≤ κ(X)(δ + ρ(A))^k`-type bound for all `δ > 0` [uncertain form]; Gautschi (18.6) `‖A^k‖ ≤ c k^{p−1}ρ(A)^k` (`p` largest Jordan block among nonzero eigenvalues); Henrici's departure from normality `Δ(A) = min‖N‖` over Schur forms, `Δ_F(A) = (‖A‖_F² − Σ|λ_i|²)^{1/2}` and (18.7) `‖A^k‖_2 ≤ Σ_{i=0}^{n−1}(k choose i)ρ(A)^{k−i}Δ_2(A)^i`; Golub–Van Loan Schur-based bound; `κ_2(X) ≥ (1 + Δ_F(A)²/‖A‖_F²)^{1/2}`; pseudospectral bound (18.8) `‖A^k‖_2 ≤ ρ_ε(A)^{k+1}/ε` (Trefethen) with `ρ_ε(A) = max{|z| : z ∈ Λ_ε(A)}`; Bai–Demmel–Gu bound in terms of distance to instability `d(A)`; Kreiss matrix theorem `K(A) ≤ sup_k‖A^k‖_2 ≤ n e K(A)`.

### 18.2 Finite precision
- Repeated multiplication (any loop order; not binary powering/Strassen). Computing column `j` of `A^m` as `fl(A(A(…(Ae_j)…)))`: **(18.10)** `x̂_j = (A + ΔA_m)(A + ΔA_{m−1})⋯(A + ΔA_1)e_j`, **(18.11)** `|ΔA_i| ≤ γ_{n+2}|A|` (real or complex; Problem 3.7 for the complex constant) [uncertain: `γ_n` real / `γ_{n+2}` complex]. Hence `|fl(A^m)| ≤ ((1+γ_{n+2})|A|)^m` and **(18.12)** a sufficient condition for `fl(A^m) → 0` is `ρ(|A|) < (1 + γ_{n+2})⁻¹`. Useful when `ρ(|A|) = ρ(A)` (triangular, checkerboard sign pattern), `ρ(|A|) ≤ √n ρ(A)` (normal), Markov chains (`|A| = A`); but `ρ(|A|)/ρ(A)` can be arbitrarily large (Problem 18.2).
- **Theorem 18.1 (Higham–Knight).** Let `A ∈ ℂ^{n×n}` have Jordan form (18.1) with `ρ(A) < 1`, `t := max_i n_i`. A sufficient condition for `fl(A^m) → 0` is **(18.13)** `γ_{n+2} κ_∞(X)‖A‖_∞ < (1 − ρ(A))^t / d_t` with `d_t = 4(t−1)` for `t ≥ 2` (any `d_1 > 1` for `t = 1`) [uncertain: exact constant; the proof shows any constant `≥ 1/f(θ_*)`, `f(θ_*) = (t−1)⁻¹(1 − t⁻¹)^t ∈ [(4(t−1))⁻¹, e⁻¹)` works]. *Proof:* it suffices to find nonsingular `S` with `‖S⁻¹(A + ΔA_i)S‖_∞ ≤ ‖S⁻¹AS‖_∞ + κ_∞(S)‖ΔA_i‖_∞ < 1` for all `i` (18.14); take `S = XP(ε)`, `P(ε)` block diagonal scaling `diag((1−|λ_i|−ε)^{1−n_i}, …, 1)` so that `‖S⁻¹AS‖_∞ ≤ 1 − ε` (18.15) and `κ_∞(S) ≤ κ_∞(X)(1 − ρ(A) − ε)^{1−t}`; choose `ε = θ(1 − ρ(A))` and optimize `θ`. ∎ Normal case: `ρ(A) < 1/(1 + c_nu)`. Sharpness demonstrated on Chebyshev spectral differentiation matrices `gallery('chebspec', n)` (nilpotent, one Jordan block): `uκ_2(X)‖A‖_2/(1−ρ)^{13}` of `0.01` vs `13.05` correctly separates converging/diverging computed powers.
- **Theorem 18.2 (Higham–Knight).** If `A` is diagonalizable, `A = X diag(λ_i)X⁻¹`, with a unique eigenvalue of largest modulus, `X` normalized so that `‖X‖_1 = Σ_i|x_{i1}|` and `‖X⁻¹‖_∞ = Σ_j|y_{1j}|` (`X⁻¹ = (y_ij)`), and `ρ_ε(A) < 1` for `ε = c_n u‖A‖_2` (`c_n = 4n²(n+2)`), then, ignoring a certain `O(ε²)` term, `fl(A^m) → 0`. *Proof:* [620] constructs `Ã = A + ΔA`, `‖ΔA‖_2 = ε`, with `ρ(Ã) ≥ ρ(A) + κ_2(X)ε/n² − O(ε²)`; then `ρ_ε(A) < 1` gives `κ_2(X)ε/n² < 1 − ρ(A)` and Theorem 18.1 applies with `t = 1`. ∎ Rule of thumb: computed powers converge if the spectral radius computed by a backward stable eigensolver is `< 1`.
- §18.3 application to stationary iteration: `e_k = (M⁻¹N)^k e_0`; the SOR example's `G` has computed powers reaching `10^{28}` at `k = 99` before decaying (consistent with (18.12) since `G` is triangular); part of the `u‖G‖_2`-pseudospectrum lies outside the unit disc. No rigorous link between pseudospectra and stationary-iteration behaviour is known.

---

## 11. Chapter 19 — QR Factorization

### 19.1–19.2 Householder transformations and QR
`P = I − βvvᵀ`, `β = 2/(vᵀv)`, symmetric orthogonal; for `x` choose `v = x ∓ ‖x‖_2e_1` so `Px = ±‖x‖_2e_1`: (19.1) `v_1 = x_1 + sign(x_1)‖x‖_2` (no cancellation), (19.2) alternative `v_1 = x_1 − ‖x‖_2 = −(x_2² + … + x_n²)/(x_1 + ‖x‖_2)` for the other sign. QR by `R = P_n⋯P_1A =: QᵀA`; never form `P_k`; cost `2n²(m − n/3)`; forming `Q` right-to-left same cost.

### 19.3 Error analysis of Householder computations (columnwise; uses `γ̃_k = cku/(1−cku)`)
- **Lemma 19.1.** For `x ∈ ℝⁿ` and either construction of `(β, v)` (`v = x`; `s = sign(x_1)‖x‖_2`; `v_1 = v_1 + s` (or (19.2)); `β = 1/(sv_1)`), the computed quantities satisfy `v̂(2:n) = v(2:n)`, `v̂_1 = v_1(1 + θ̃_n)`, `β̂ = β(1 + θ̃_n)` [uncertain: exact indices; proof shows `ŝ = s(1+θ_{n+1})`, `ŵ = w(1+θ_{n+2})` because there is no cancellation in `v_1 + s`]. Renormalizing to `P = I − vvᵀ` with `‖v‖_2 = √2`: **(19.5)** `v̂ = v + Δv`, `|Δv| ≤ γ̃_m|v|`.
- **Lemma 19.2.** For `b ∈ ℝ^m` and `y = Pb = b − v(vᵀb)` computed with `v̂` satisfying (19.5): `ŷ = (P + ΔP)b`, `‖ΔP‖_F ≤ γ̃_m`. *Proof* (cf. Lemma 3.9): `ŵ = (v + Δv + Δv')(v + Δv)ᵀ(b + Δb)` with `|Δb| ≤ γ_m|b|`; `|ŷ − Pb| ≤ u|b| + γ̃_m|v||vᵀ||b|`, so `‖Δy‖_2 ≤ γ̃_m‖b‖_2`; set `ΔP = Δy bᵀ/bᵀb`. ∎
- **Lemma 19.3.** `A_{k+1} = P_kA_k`, `k = 1:r`, `A_1 = A ∈ ℝ^{m×n}`, `P_k = I − v_kv_kᵀ`, computed with `v̂_k` satisfying (19.5) and assuming **(19.6)** `rγ̃_m < 1/2` [uncertain: 1/2]. Then `Â_{r+1} = Qᵀ(A + ΔA)`, `Q = P_r⋯P_1`ᵀ-ordered product, with **(19.8)** `‖Δa_j‖_2 ≤ rγ̃_m‖a_j‖_2`, `j = 1:n` (columnwise). For `n = 1`: `â^{(r+1)} = (Q + ΔQ)ᵀa`, `‖ΔQ‖_F ≤ rγ̃_m`. *Proof:* `â_j^{(r+1)} = (P_r + ΔP_r)⋯(P_1 + ΔP_1)a_j` (19.9), Lemma 3.7 with `‖P_k‖_2 = 1` gives `‖Δa_j‖_2 ≤ ((1+γ̃_m)^r − 1)‖a_j‖_2 ≤ rγ̃_m/(1 − rγ̃_m)‖a_j‖_2 = rγ̃'_m‖a_j‖_2` (Lemma 3.1 + (19.6)). ∎ Normwise: `‖ΔA‖_F ≤ rγ̃_m‖A‖_F` (Lemma 6.6).
- **Theorem 19.4 (Householder QR backward error).** Let `R̂ ∈ ℝ^{m×n}` be the computed upper trapezoidal factor of `A ∈ ℝ^{m×n}` (`m ≥ n`) by Householder QR (either sign choice). Then there is an *exactly orthogonal* `Q ∈ ℝ^{m×m}` with `A + ΔA = QR̂`, **(19.11)** `‖Δa_j‖_2 ≤ γ̃_{mn}‖a_j‖_2`, `j = 1:n`; `Q = (P_nP_{n−1}⋯P_1)ᵀ` where `P_k` is the Householder matrix corresponding to the exact application of step `k` to the *computed* `Â_k`. *Proof:* Lemma 19.3 with `r = n`; the explicitly zeroed subdiagonal entries are handled by noting the corresponding rows of `ΔP` can be taken zero. ∎ Refinement: `γ̃_{mn}` can be `γ̃_{mj}` for column `j`. Weaker normwise form `‖ΔA‖_F ≤ γ̃_{mn}‖A‖_F`; equivalently (19.12) with `A = BD_c`, `D_c = diag(‖a_j‖_2)`: `(B + ΔB)D_c = QR̂`, `‖ΔB‖_2/‖B‖_2 = O(u)`. `Q` is theoretical; the explicitly formed `Q̂ = Q(I + ΔI)`, `‖ΔI(:,j)‖_2 ≤ γ̃_{mn}` gives (19.13) `‖Q̂ − Q‖_F ≤ √n γ̃_{mn}` and `‖(A − Q̂R̂)(:,j)‖_2 ≤ √n γ̃_{mn}‖a_j‖_2`.
- **Theorem 19.5 (linear system via Householder QR).** `A` nonsingular; solve `Rx = Qᵀb`. Then `(A + ΔA)x̂ = b + Δb` with `‖Δa_j‖_2 ≤ γ̃_{n²}‖a_j‖_2`, `‖Δb‖_2 ≤ γ̃_{n²}‖b‖_2`; and (19.14) a version with only `A` perturbed, `‖Δa_j‖_2 ≤ γ̃_{n²}‖a_j‖_2`. *Proof:* Theorem 19.4 for `R̂`; Lemma 19.3 (`n = 1`) for `ĉ = Qᵀ(b + Δb)` with the *same* `Q`; Theorem 8.5 for `(R̂ + ΔR)x̂ = ĉ`, `|ΔR| ≤ γ_n|R̂|`; premultiply by `Q`. ∎ `R̂` nonsingular if `κ_2(A)n^{1/2}γ̃_{mn} < 1`.
- §19.4 **Theorem 19.6 (Powell–Reid; Cox–Higham).** With column pivoting (19.15) and sign choice (19.1): `(A + ΔA)Π = QR̂` with a *row-wise* bound `‖ΔA(i,:)‖_2 ≤ γ̃_{mn}α_i‖A(i,:)‖_2`-type, where `α_i = max_{j,k}|a_ij^{(k)}|/max_j|a_ij|` (row growth factors), controlled by row pivoting or row sorting [uncertain exact form]. §19.5 aggregated (WY/compact WY) Householder: same backward error form.
- §19.6 Givens: **Lemma 19.7** computed `ĉ = c(1+θ_4)`, `ŝ = s(1+θ_4)`; **Lemma 19.8** `ŷ = (G_ij + ΔG_ij)x`, `‖ΔG_ij‖_F ≤ √2γ_6` (from `|ŷ − G_ijx| ≤ γ_6|G_ij||x|`; only rows `i, j` of `ΔG` nonzero); **Lemma 19.9** for `A_{k+1} = W_kA_k` with `W_k` products of *disjoint* rotations: `Â_{r+1} = Qᵀ(A + ΔA)`, `‖Δa_j‖_2 ≤ γ̃_r‖a_j‖_2` (Lemma 3.6 with `‖ΔW_k‖_2 ≤ √2γ_6`); **Theorem 19.10** Givens QR: `A + ΔA = QR̂`, `‖Δa_j‖_2 ≤ γ̃_{m+n−2}‖a_j‖_2` (`r = m + n − 2` disjoint stages) — a factor `n` better than Householder, "an artefact of the analysis".
- §19.7 iterative refinement with QR (columnwise ⇒ `|b − Ax̂| ≤ u(G|A||x̂| + H|b|)` with `G ≈ n²eeᵀ`, then Theorem 12.4). §19.8 Gram–Schmidt: CGS has no useful bound; **Theorem 19.13 (Björck; Björck–Paige)** MGS on full-rank `A`: `A + ΔA_1 = Q̂R̂` with `‖ΔA_1‖_2 ≤ c_1mnu‖A‖_2` [uncertain: exact constants], `‖Q̂ᵀQ̂ − I‖_2 ≤ c_2mnuκ_2(A)/(1 − c_2mnuκ_2(A))`, and there is an exactly orthonormal `Q` with `A + ΔA_2 = QR̂`, `‖ΔA_2‖_2 ≤ c_3mnu‖A‖_2` (MGS = Householder QR on `[0; A]`). §19.9 sensitivity of QR (Stewart, Sun; `κ_2(A)` bounds). LAPACK `xGEQRF`, `xGEQP3`.

---

## 12. Brief summaries of the remaining chapters

- **Ch. 1 Principles of Finite Precision Computation.** Relative error and significant digits; sources of error; precision vs accuracy; backward/forward/mixed error (Figures 1.1–1.2, `forward error ≲ condition number × backward error`); conditioning; cancellation (harmless if the cancelled quantities are exact); worked examples — quadratic formula, sample variance (one-pass formula unstable), GEPP vs Cramer, accumulation of errors, instability without cancellation (need for pivoting; `x_{k+1}` recurrences; an "infinite sum"), increasing precision does not always help, cancellation of rounding errors (`(e^x−1)/x` via `log`, Householder QR), rounding errors can be beneficial (deflation), stability depends on the problem, rounding errors are not random (Table 1.x), design principles for stable algorithms (avoid subtracting contaminated quantities, minimize intermediate sizes, look for mathematically-not-numerically equivalent formulations, use orthogonal transformations, take precautions such as pivoting, do backward error analysis), misconceptions. **Lemma 1.1** (2-norm): `min{‖ΔA‖_2/‖A‖_2 : (A+ΔA)y = b} = ‖r‖_2/(‖A‖_2‖y‖_2)`.
- **Ch. 5 Polynomials.** Horner: `p̂(x) = Σ_i (1+θ_{2i})a_ix^i` [uncertain indices] ⇒ backward error `|Δa_i| ≤ γ_{2n}|a_i|` and forward `|p(x) − p̂(x)| ≤ γ_{2n}p̃(|x|)` (`p̃` has coefficients `|a_i|`); running error bound (Algorithm 5.2); derivatives by repeated synthetic division (componentwise backward error for all derivatives); Newton form and polynomial interpolation (divided differences; Leja ordering improves stability); matrix polynomials (Horner vs Paterson–Stockmeyer, stable in the `‖·‖`-of-`|coefficients|` sense).
- **Ch. 11 Symmetric Indefinite and Skew-Symmetric Systems.** Block `LDLᵀ` with 1×1/2×2 pivots: complete pivoting (Bunch–Parlett), partial (Bunch–Kaufman; `‖L‖` unbounded but Theorem 11.4/11.7: `(A+ΔA)x̂ = b`, `‖ΔA‖_M ≤ p(n)u(‖A‖_M + ‖L̂‖_M‖D̂‖_M‖L̂ᵀ‖_M)` and `‖L̂‖‖D̂‖‖L̂ᵀ‖` is bounded ⇒ backward stable), rook pivoting (bounded `L`), tridiagonal case; Aasen's `LTLᵀ` (Theorem 11.8: backward stable, growth ≤ `4^{n−2}`); skew-symmetric block `LDLᵀ`.
- **Ch. 12 Iterative Refinement.** `r = b − Ax̂` (precision `ū`), solve `Ad = r`, `y = x̂ + d`. Theorem 12.1 (mixed precision, `ū = u²`-ish): forward error converges to `O(u)` if `uκ` small enough; Theorem 12.2 (fixed precision): forward error `≈ 2n cond(A,x)u`-type limit — componentwise forward stable; Theorem 12.3/12.4 (Higham): if the solver satisfies `|b − Ax̂| ≤ u(G|A||x̂| + H|b|)` then one step of fixed-precision refinement gives `ω_{|A|,|b|}(ŷ) ≤ 2(n+1)u`-type bound provided `uσ(A,x)·(‖G‖-terms)` is small, where `σ(A,x) = max_i(|A||x|)_i/min_i(|A||x|)_i` — GEPP becomes componentwise backward stable after one step unless `|A||x|` is badly scaled (Skeel's theorem generalized).
- **Ch. 13 Block LU Factorization.** Partitioned (algorithmically blocked, same factors) vs block LU (different factorization, `L` block unit triangular). Theorem 13.5: partitioned LU has the same componentwise bound as point LU given stable block operations (13.4)–(13.6). Theorems 13.6–13.8: block LU backward error `‖ΔA‖ ≤ c_nu(‖A‖ + ‖L̂‖‖Û‖ + …)`; stable for block diagonally dominant (by columns) and SPD matrices (Lemma 13.9 `‖A_{21}A_{11}⁻¹‖_2 ≤ κ_2(A)^{1/2}` ⇒ bound `c_nuκ_2(A)^{1/2}‖A‖`); unstable in general.
- **Ch. 14 Matrix Inversion.** Use and abuse of `A⁻¹` (solving by `A⁻¹b` is not backward stable but forward error comparable); triangular inversion: unblocked Methods 1/2 satisfy a right residual `|X̂T − I| ≤ c_nu|X̂||T|` **or** a left residual, never both (Lemmas 14.1–14.3), blocked variants; full inversion via LU (Methods A–D: residual bounds `|AX̂ − I| ≤ c_nu|A||L̂||Û||X̂|`-type; LAPACK `xGETRI` = Method D); Gauss–Jordan (Theorem 14.5: forward error bound `‖x − x̂‖ ≤ c_nuρ_nκ(A)‖x‖`-type, residual not small ⇒ forward but not backward stable; Corollaries 14.6–14.7 for special classes); parallel inversion (Newton–Schulz, Csanky unstable); determinant and Hyman's method (Hessenberg, backward stable).
- **Ch. 15 Condition Number Estimation.** Componentwise condition numbers reduce to `‖|A⁻¹|d‖_∞ = ‖A⁻¹D‖_∞`; `p`-norm power method (Boyd, Tao) and Lemma 15.2; LAPACK 1-norm estimator (Hager/Higham, `xLACON`: `≥ n` matrix–vector products, typically 4–5, estimate is a lower bound, exact with high probability); block 1-norm estimator (Higham–Tisseur, `normest1`); other estimators (LINPACK, Cline–Rew counterexamples, Theorem 15.6 Dixon's probabilistic bound); tridiagonal condition numbers exactly in `O(n)` (Theorems 15.7–15.9).
- **Ch. 16 The Sylvester Equation** `AX + XB = C`. Bartels–Stewart via Schur forms; backward error: the natural residual bound `‖R‖ ≤ c_nu(‖A‖+‖B‖)‖X̂‖` does **not** imply a small backward error — explicit backward error formula/bounds (Higham 1993) show it can be large when `X` is ill conditioned or `[A, B]` far from having a solution `X` of comparable norm; Lyapunov special case; perturbation result via `sep(A,−B)` and `Φ = ‖(I⊗A + Bᵀ⊗I)⁻¹‖`; practical error bounds; extensions (generalized Sylvester, `AXB + CXD = E`).
- **Ch. 20 The Least Squares Problem.** Perturbation theory (Theorem 20.1 Wedin: `‖Δx‖/‖x‖ ≲ κ_2(A)(ε_1 + ε_2‖b‖/(‖A‖‖x‖)) + κ_2(A)²ε_1‖r‖/(‖A‖‖x‖)`; Theorem 20.2 componentwise); Householder QR (Theorem 20.3: backward stable, `(A+ΔA)`, `b+Δb`, columnwise `γ̃_{mn}`); MGS (backward stable as LS solver, Björck–Paige); normal equations (forward error `κ_2²u`, not backward stable; Theorem 20.4 residual analysis); iterative refinement (Björck's augmented system; mixed precision converges); seminormal equations `RᵀRx = Aᵀb` (forward error `κ²u` unless corrected); backward error of an approximate LS solution (Theorem 20.5 Waldén–Karlson–Sun: `min‖ΔA‖_F = min{η, σ_min([A, C])}`-type formula, `η = ‖r‖_2/‖y‖_2`; Lemma 20.6); weighted LS (Powell–Reid row-wise stability, Theorem 20.7); equality constrained LS (null space and elimination methods; Theorems 20.8, 20.10 Cox–Higham); proof of Wedin's theorem; Lemmas 20.11–20.12 on pseudo-inverse perturbation.
- **Ch. 21 Underdetermined Systems** (`m ≤ n`, minimum 2-norm solution). Methods: `Q` method via QR of `Aᵀ` (row-wise backward stable, Theorem 21.4), seminormal equations `x = Aᵀ(AAᵀ)⁻¹b` via `R` only (forward stable only); perturbation theory (Theorem 21.1 Demmel–Higham; Lemma 21.2 Kiełbasiński–Schwetlick); backward error (Theorem 21.3 Sun–Sun formula).
- **Ch. 22 Vandermonde Systems.** Explicit inverse; Björck–Pereyra `O(n²)` algorithms for primal `Vx = b` and dual `Vᵀa = f` as products of bidiagonal matrices; Theorem 22.4 forward error bound `|x − x̂| ≤ c_nu|V⁻¹|…|b|`-type in terms of `|L||U|`-like factors; Corollary 22.5: for `0 ≤ α_0 < … < α_n` and alternating-sign `b` the solution is obtained to high *relative* accuracy (no cancellation — explains observed accuracy); residual bound Theorem 22.6 and Corollary 22.7; instability for other data and remedies (ordering, partial pivoting variants); generalized (Vandermonde-like) systems.
- **Ch. 23 Fast Matrix Multiplication.** Winograd's inner product formula (Theorem 23.1: error bound involves `‖x‖‖y‖`-type products, not `|x|ᵀ|y|` — not componentwise stable; scaling fixes); Strassen (Theorem 23.2 Brent: `‖C − Ĉ‖ ≤ [(n/n_0)^{log₂12}(n_0² + 5n_0) − 5n]u‖A‖‖B‖ + O(u²)` normwise only, `‖·‖_M`; Theorem 23.3 Winograd-variant with `log₂18`; componentwise bound impossible); Theorem 23.4 (Bini–Lotti) general bilinear noncommutative algorithms satisfy normwise bounds; 3M complex multiplication (`(a+ib)(c+id)` with 3 real products: imaginary part loses relative accuracy but normwise fine).
- **Ch. 24 FFT and Applications.** Theorem 24.1 Cooley–Tukey radix-2 factorization `F_n = A_t⋯A_1P_n`; Theorem 24.2: `‖ŷ − F_nx‖_2 ≤ tη/(1−tη)‖F_nx‖_2`-type bound (`n = 2^t`, `η` depends on the accuracy of the computed twiddle factors, e.g. `η = √2γ_4 + μ`) — tiny normwise forward error, `O(log n)` growth; Theorem 24.3 (Yalamov): circulant systems solved via FFT have small normwise backward error.
- **Ch. 25 Nonlinear Systems and Newton's Method.** Newton in floating point with errors in evaluating `F`, the Jacobian and the linear solve; Theorems 25.1–25.2 (Tisseur): convergence to a limiting accuracy `‖x̂ − x_*‖ ≲ ‖J(x_*)⁻¹‖·(error in F) + …` provided `uκ(J)` and the residual errors are small enough; special cases (approximate Jacobians, inexact solves), conditioning of nonlinear systems, stopping criteria.
- **Ch. 26 Automatic Error Analysis.** Direct search optimization (alternating directions, multidirectional search, Nelder–Mead) over inputs to maximize instability measures — finds counterexamples (condition estimators, fast inversion, cubic roots); interval arithmetic (directed rounding, dependency problem, Rump's verification methods, `intlab`); other work (Miller's software, Chaitin-Chatelin's PRECISE, CESTAC/stochastic arithmetic).
- **Ch. 27 Software Issues in Floating Point Arithmetic.** Exploiting IEEE (NaN/∞ propagation, exception flags, `isnan`), subtleties (`x == y` vs `x − y == 0`, `(x+y)−y`), Cray peculiarities, compilers (x87 extended precision, FMA contraction, unsafe optimizations), determining machine parameters (Malcolm's algorithm, `LAPACK xLAMCH`), testing arithmetic (Paranoia), portability (LAPACK 2×2 problems `xLASV2`, numerical constants, models of arithmetic in software), avoiding underflow/overflow (scaled 2-norm, Smith's complex division (27.1)), multiple precision (Brent's MP, Bailey's MPFUN, ARPREC), extended and mixed precision BLAS (XBLAS), the Patriot missile clock-drift failure.
- **Ch. 28 A Gallery of Test Matrices.** Hilbert/Cauchy (exact inverses, `κ_2(H_n) ~ e^{3.5n}`, rounding the entries already dominates), random matrices (Edelman's distribution of `κ_2`, `E[log κ_2] ≈ log n + 1.537`), `randsvd`, Pascal (exact inverse, `κ ~ 16^n/(πn)`), tridiagonal Toeplitz (explicit eigenpairs; Theorem 28.1 Stewart on random triangular matrices `‖T⁻¹‖ ~ 2^n`), companion matrices; MATLAB `gallery`.
- **Appendices.** A solutions to problems; B acquiring software (Netlib, MATLAB, NAG); C program libraries (BLAS levels 1–3, EISPACK, LINPACK, LAPACK structure); D the Matrix Computation Toolbox.

---

## 13. Design notes for a floating-point backbone

### 13.1 Minimal abstract axiomatization of the standard model

**Observation A (almost everything is "real numbers with δ's").** Inspecting the proofs of chapters 3, 4, 8, 9, 10, 17, 18, 19: every theorem is proved by (i) writing each elementary operation of the algorithm as `computed = exact · (1+δ)` or `exact/(1+δ)` with `|δ| ≤ u`, (ii) pure algebra and the `γ_n` calculus (Lemmas 3.1, 3.3, 3.4), (iii) exact linear algebra on the resulting perturbed equations (Neumann series, norms, eigenvalue interlacing, Jordan/Schur forms). Nowhere in those chapters is it used that `fl(x)` is a *function*, that `F` is discrete, that rounding is monotone, that `fl(x) = x` for `x ∈ F`, or that any operation is exact. The book states this explicitly (§2.2: "the model does not require that δ = 0 when `x op y ∈ F`"; "all the error analysis in this book is carried out under (2.4), sometimes making use of (2.5)").

Hence the *minimal* structure is:

```
-- Layer 0: a linearly ordered field K (ℝ for anything with sqrt/eigenvalues; ℚ suffices for
-- the purely algebraic parts), a parameter u with 0 ≤ u (< 1, and hypotheses n*u < 1 as needed).
-- Layer A: the "rounding relation"
def RelRounds (u : K) (x y : K) : Prop := |y - x| ≤ u * |x|        -- y = x(1+δ), |δ| ≤ u   (2.4)
def RelRounds' (u : K) (x y : K) : Prop := |y - x| ≤ u * |y|       -- y = x/(1+δ), |δ| ≤ u  (2.5)
```

(`|y − x| ≤ u|x|` is equivalent to `∃ δ, |δ| ≤ u ∧ y = x(1+δ)`; stating it as an inequality avoids the existential. The two forms are inter-derivable with `u ↦ u/(1−u)`; both hold simultaneously under round-to-nearest, Theorems 2.2/2.3.) An algorithm in floating point is then a **nondeterministic program**: every arithmetic node may return *any* `y` related to the exact result by `RelRounds u`. A theorem of the form "the computed `x̂` from Algorithm X satisfies P" becomes "for every execution (every choice of admissible `y` at every node), P". This matches Higham's "no matter what the order of evaluation" results (Lemma 8.4, Theorem 8.5, Theorem 9.3–9.4, (3.4)), whose formal content is precisely a quantification over all binary evaluation trees *and* all admissible roundings.

Concretely I would recommend:

1. **A `RoundingModel K` structure** with fields `u`, `u_nonneg`, and a relation `Rounds : K → K → Prop` plus the axiom `Rounds x y → |y − x| ≤ u * |x|` (optionally also the dual `≤ u*|y|`, and a `sqrt` variant `Rounds (√x) y` for `x ≥ 0`). Instances: (a) **`exact`**: `u = 0`, `Rounds = Eq` — the whole exact-arithmetic Krylov library is the `u = 0` specialization of the same statements; (b) **`adversarial u`**: `Rounds x y ↔ |y − x| ≤ u|x|` — the model in which every theorem of chapters 3–19 is proved; (c) **`ofFormat F`**: `Rounds x y ↔ y = fl_F(x)` for a concrete discrete format with round-to-nearest, whose model-satisfaction is Theorem 2.2 (and 2.3). Layer-A theorems are stated for an arbitrary model satisfying the axiom, so they automatically hold for (a), (b), (c) and for IEEE binary64, for the complex model of Lemma 3.5 (with a bigger `u`), and for the no-guard-digit model when stated with the split form (2.6).
2. **An algorithm/execution layer.** Two options: (i) *per-algorithm hypotheses*: state Lemma 8.4 as "if `ŷ, ŝ_i` satisfy `ŝ_i = (ŝ_{i−1} − fl_i)(1+δ_i)`, …, then …" — simplest, but every "any ordering" result needs an inductive description of trees anyway; (ii) a tiny **expression language** `FlExpr` (constants, `+ − × / √`) with an inductive relational semantics `Evals (M : RoundingModel) : FlExpr → K → Prop` (`Evals (a + b) y ↔ ∃ ya yb, Evals a ya ∧ Evals b yb ∧ M.Rounds (ya + yb) y`). Then "any summation tree of `x_1,…,x_n`" is a set of `FlExpr`s and (4.4)/Lemma 8.4/Theorem 8.5 become single theorems by structural induction (the invariant: "each leaf `x_i` carries a factor `∏(1+δ)` with at most `depth_i ≤ n−1` factors"). Option (ii) is what makes Higham's "tedious to write down" proof of Lemma 8.4 a routine induction. It also makes the *rounding-error equivalence* remarks (sdot vs saxpy, six loop orders of matrix multiply, Doolittle vs classical GE) into literal equalities of expression trees.
3. **The `θ/γ` calculus** as a small theory over `K` (see 13.2), with `simp`/`gcongr`-style lemmas so that bounds compose mechanically; a decision of whether to carry exact integer constants (recommended: yes — the book's `γ̃_n` with "unspecified `c`" should be replaced by explicit constants; Lean can keep them and one can prove `γ̃`-style corollaries `∃ c ≤ C, …` afterwards).

**What genuinely needs the discrete structure of `F` (Layer B)**, i.e. a type of floats `F(β,t,e_min,e_max)` (or Flocq-style `{m·β^e : |m| < β^t}` as a subset of `K`), round-to-nearest defined as an argmin, ties, exponent function `e(x)`:
- Theorem 2.2 / 2.3 / Lemma 2.1 themselves (they *derive* `u` and the model from `F`); the range hypotheses (no overflow/underflow) and subnormals;
- Theorem 2.4 (Ferguson) and **Theorem 2.5 (Sterbenz)** — exactness of subtraction of close numbers; used for Kahan's Heron formula, and pervasively in modern compensated/error-free-transformation algorithms;
- the **error-free transformations**: (4.7) `(a+b) − fl(a+b) ∈ F` and is computed exactly by FastTwoSum (needs base 2, round-to-nearest, `|a| ≥ |b|`); the FMA exact product (Problem 2.26); Kahan's determinant (Problem 2.27); Dekker/Veltkamp splitting (in ch. 27 / references);
- **monotonicity of `fl`** (`x ≥ y ⇒ fl(x) ≥ fl(y)`), idempotence (`x ∈ F ⇒ fl(x) = x`), sign/absolute-value exactness, exact scaling by powers of `β` (used only in remarks in chapters 3–19, e.g. the scale-invariance comment for Theorem 10.7, and for stopping tests `fl(x) = x + Δx, |Δx| ≤ u|x|` for vectors — the latter is just Theorem 2.2 applied entrywise);
- everything IEEE-specific (Layer C): NaN, ±∞, ±0, exception flags, directed rounding (needed for interval arithmetic, ch. 26), double rounding, `Float` ↔ bit-pattern encodings.

**Interesting borderline cases:**
- Compensated summation's bound (4.8) `ŝ_n = Σ(1+μ_i)x_i`, `|μ_i| ≤ 2u + O(nu²)` is, per Higham (and Goldberg's proof), a standard-model result (it fails only under the *weaker* no-guard-digit model), whereas the exactness (4.7) is Layer B. So even Kahan summation's headline theorem is Layer A — but its proof is a long, delicate algebraic induction, a good stress test for the `θ`-calculus automation.
- Theorem 10.7 ("Cholesky succeeds") needs a notion of *partial* execution: `√` is only admissible on nonnegative arguments, and "runs to completion" is the predicate "every square-root argument in every admissible execution is positive". The relational semantics handles this naturally (an execution exists iff the algorithm succeeds), and the proof shows, by induction and Theorem 10.5, that under `λ_min(H) > nγ_{n+1}/(1−γ_{n+1})` every partial execution can be extended. No `F`-structure needed.
- Running error analysis (§3.3) uses (2.5) and is Layer A, but its *point* (the bound is itself computed in floating point and remains valid) requires a second-order argument that Higham leaves informal.
- Lemma 3.5 (complex arithmetic) is Layer A over `ℝ²`; it yields a `RoundingModel ℂ` with `u_ℂ = √2γ_4`, so complex results are instances of the same abstract theorems.

**Which field?** Chapters 3, 4, 8, 9 (LU part) and the `γ` calculus work over any linearly ordered field (`ℚ` even, so the exact-arithmetic numlib core can be reused verbatim). Square roots (Cholesky, Householder `‖x‖_2`, Givens) need `ℝ` (or a real closed field); eigenvalue/SVD/2-norm arguments (Lemma 6.6, Theorems 10.6–10.7, 18.1–18.2, `κ_2`) need Mathlib's `ℝ`/`ℂ` spectral theory. Jordan canonical form is not in Mathlib; Theorem 18.1 only needs "`ρ(A) < 1 ⇒ ∃ S, ‖S⁻¹AS‖_∞ ≤ 1 − ε` with a bound on `κ_∞(S)`", which can be obtained from a Schur triangularization plus diagonal scaling (Golub–Van Loan Lemma 7.3.2 route; Higham's Problem 18.4) rather than from Jordan form. Mathlib does have `spectralRadius` and Gelfand's formula (`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`) for complex Banach algebras, which covers the exact-arithmetic part of §18.1.

### 13.2 The `γ_n` calculus — exact statements (the reusable core)

Definitions (over an ordered field `K`, `u ≥ 0`, `n : ℕ`):
- `γ u n := n*u / (1 − n*u)`, meaningful for `n*u < 1`.
- `IsTheta u n θ := |θ| ≤ γ u n` (Higham's "`θ_n` denotes a quantity bounded by `γ_n`").
- `γ̃ u n := ∃ c : ℕ, c ≤ C ∧ … c*n*u/(1 − c*n*u)` — better: keep `c` explicit.

**Lemma 3.1.** `(∀ i < n, |δ_i| ≤ u) → (∀ i, ρ_i = ±1) → n*u < 1 → ∃ θ, |θ| ≤ γ u n ∧ ∏_{i<n}(1+δ_i)^{ρ_i} = 1 + θ`.
Proof: `(1−u)^n ≤ ∏ ≤ (1−u)^{−n}`; Bernoulli `(1−u)^n ≥ 1 − nu` gives `(1−u)^{−n} − 1 ≤ nu/(1−nu)` and `1 − (1−u)^n ≤ nu ≤ γ_n`. (Sharper for all `ρ_i = +1`: `|θ| ≤ nu/(1 − nu/2)` for `nu < 2`, Problem 3.2 [uncertain as noted].)

**Lemma 3.3** (each "`=`" is an existence statement about a new `θ`): with `|θ_k| ≤ γ_k`, `|θ_j| ≤ γ_j`:
1. `(1+θ_k)(1+θ_j) = 1 + θ_{k+j}`;
2. `(1+θ_k)/(1+θ_j) = 1 + θ_{k+j}` if `j ≤ k`, and `= 1 + θ_{k+2j}` if `j > k`;
3. `γ_kγ_j ≤ γ_{min(k,j)}` provided `max(j,k)·u ≤ 1/2`;
4. `i·γ_k ≤ γ_{ik}`;
5. `γ_k + u ≤ γ_{k+1}`;
6. `γ_k + γ_j + γ_kγ_j ≤ γ_{k+j}`.
Useful additional facts (implicit in the book): `γ` is monotone in `n` and in `u`; `γ_n ≥ nu`; `γ_n ≤ 1.01nu` when `nu ≤ 0.01` (Lemma 3.4 form: `|∏_{i<n}(1+δ_i) − 1| ≤ 1.01nu`); `(1+γ_k)^r − 1 ≤ rγ_k/(1 − rγ_k)` for `rγ_k < 1` (used in Lemma 19.3, eq. (19.10)); `θ`-terms absorb into `γ̃`: `3γ_n = γ̃_n`, `mγ_n = γ̃_{mn}`.

**Lemma 3.4.** `(∀ i < n, |δ_i| ≤ u) → n*u ≤ 1/100 → |∏_{i<n}(1+δ_i) − 1| ≤ (101/100)·n*u`.

**Product/perturbation lemmas built on it** (Lemmas 3.6–3.8): for `‖ΔX_j‖ ≤ δ_j‖X_j‖` (consistent norm), or `‖ΔX_j‖_F ≤ δ_j‖X_j‖_2`, or `|ΔX_j| ≤ δ_j|X_j|`: `‖∏(X_j+ΔX_j) − ∏X_j‖ ≤ (∏(1+δ_j) − 1)∏‖X_j‖` (resp. `‖·‖_F` with `∏‖X_j‖_2`, resp. entrywise with `∏|X_j|`). With `δ_j ≤ γ_k` and Lemma 3.1 the right side is `≤ γ_{rk}`-type. These four lemmas plus (3.4)/(3.11) and Lemma 8.4 are the entire "engine": Theorems 8.5, 9.3, 9.4, 10.3, 10.4, 19.3, 19.4, 19.9, 19.10, (18.10) are short corollaries.

Lean shape suggestion: a predicate `IsRelPert (ε : K) (x y : K) : Prop := |y − x| ≤ ε|x|` with lemmas `IsRelPert.mul : IsRelPert (γ k) x x' → IsRelPert (γ j) y y' → IsRelPert (γ (k+j)) (x*y) (x'*y')` etc., so `θ`-bookkeeping is done by `gcongr`-like composition rather than by exhibiting `δ`'s. The `γ` monotonicity lemmas let one always round indices *up* (Higham's practice).

### 13.3 Componentwise (entry-level) vs normwise results

Componentwise (statements with `|·|` entrywise, `≤` entrywise; these are the primary results and the strongest):
- (3.4) inner product backward error; (3.6) outer product; (3.11)–(3.13) mat-vec/mat-mat; Lemma 3.8; Lemma 3.9; Lemma 8.2, 8.4; **Theorem 8.3, 8.5** (`|ΔT| ≤ γ_n|T|`); Theorem 8.10/Cor. 8.11 (via `M(T)⁻¹`); Theorem 8.12 (entrywise inverse bounds); **Theorems 9.3, 9.4** (`|ΔA| ≤ γ_n|L̂||Û|`, `γ_{3n}|L̂||Û|`), (9.9) totally nonnegative; Theorems 9.13–9.14 (tridiagonal `|ΔA| ≤ cu|A|`); **Theorems 10.3, 10.4, 10.5** (`γ_{n+1}|R̂ᵀ||R̂|`, `γ_{3n+1}|R̂ᵀ||R̂|`, `ddᵀ`); Theorems 7.3, 7.4 (Oettli–Prager, Skeel); (17.2), (17.10)–(17.13), (17.32); (18.10)–(18.12); Lemma 19.8's intermediate `|ŷ − G_ijx| ≤ γ_6|G_ij||x|`; Horner (ch. 5); iterative refinement (ch. 12); Vandermonde (ch. 22).
- Their proofs never take norms; they need the entrywise order on `Matrix m n K`, entrywise `abs`, and monotonicity of matrix multiplication for nonnegative matrices (`|AB| ≤ |A||B|`, `A ≤ B ∧ C ≥ 0 → AC ≤ BC`). In Mathlib, `Matrix m n K` is a `Pi` type so the entrywise `≤`, `|·|` and lattice structure exist (`Pi.instLattice`, `Pi.instAbs`-style instances may need `Matrix.of`-unfolding lemmas); a small API `Matrix.abs`, `Matrix.abs_mul_le`, `Matrix.mul_le_mul_of_nonneg` would be the foundation.

Columnwise (intermediate; chapter 19): `‖Δa_j‖_2 ≤ γ̃‖a_j‖_2` for each column — Theorems 19.4, 19.5, 19.10, Lemma 19.3, 19.9, LS Theorem 20.3. Row-wise: Theorems 19.6, 20.7, 21.4.

Normwise (derived, or the only kind available):
- Theorems 7.1, 7.2 (Rigal–Gaches, normwise perturbation), Theorem 6.5; **Theorem 9.5** (`‖ΔA‖_∞ ≤ n²γ_{3n}ρ_n‖A‖_∞`), Lemma 9.6, all growth-factor results; Cholesky `‖ΔA‖_2 ≤ cn²u‖A‖_2`, Theorems 10.6–10.8, 10.14; (17.8), (17.19)–(17.20), (17.31); §18.1 bounds, Theorems 18.1–18.2; the weaker forms `‖ΔA‖_F ≤ γ̃_{mn}‖A‖_F` of Theorem 19.4; MGS Theorem 19.13; block LU (ch. 13), symmetric indefinite (ch. 11, `‖·‖_M`), fast matrix multiplication (ch. 23 — *provably* not componentwise), FFT (ch. 24), Sylvester (ch. 16).
- Conversion lemmas: Lemma 6.6 and Table 6.2 (componentwise ⇒ 2-norm with `√rank` or `√n` factors), `‖|A|‖_{1,∞} = ‖A‖_{1,∞}`, `‖A‖_∞ = ‖|A|e‖_∞`. Mathlib provides the entrywise sup norm, the `L∞`-operator norm (`Matrix.linftyOpNormedAlgebra`), Frobenius (`Matrix.frobeniusNormedAlgebra`) and the `L2` operator norm (`Matrix.l2OpNormedAlgebra`) as scoped instances in `Mathlib/Analysis/Matrix.lean`; the `L1` operator norm is the `L∞` norm of the transpose. The equivalence constants of Tables 6.1/6.2 are mostly not there and would be a natural early deliverable.

Design consequence: state every backbone theorem in its componentwise form first (it is both the strongest and the easiest to prove — no norms), and derive normwise corollaries through a single conversion module.

### 13.4 How finite-precision Lanczos/CG (Paige; Greenbaum; Meurant–Strakoš) and chapter 17 sit on top

The shape is always the same three-layer sandwich, and chapter 17 is the cleanest template:

1. **Model lemma (Layer A, floating point appears only here).** The computed iteration satisfies the exact recurrence *plus an explicit perturbation with an explicit bound*: (17.1)–(17.2) `Mx̂_{k+1} = Nx̂_k + b + ξ_k`, `|ξ_k| ≤ c_nu(|M||x̂_{k+1}| + |N||x̂_k| + |b|)`, obtained from Theorem 8.5 (triangular solve with `M`) and (3.11) (mat-vec with `N`). For Lanczos/CG the analogous lemma (Paige 1976/1980) says: the computed `V_{k} = [v_1,…,v_k]`, `T_k` (tridiagonal with `α_j, β_j`) satisfy
   `A V_k = V_k T_k + β_{k+1}v_{k+1}e_kᵀ + F_k`, `‖f_j‖_2 ≤ ε_1‖A‖_2`,
   `|v_jᵀv_j − 1| ≤ ε_0`, `|β_{j+1}v_{j+1}ᵀv_j| ≤ 2ε_0‖A‖_2` (local orthogonality),
   with `ε_0 = O(nu)` and `ε_1 = O((m + ‖|A|‖/‖A‖)u)` (`m` = max nonzeros per row), plus the analogous relations for the CG residual/direction recurrences `r_{k+1} = r_k − α_kAp_k + δr_k`, `x_{k+1} = x_k + α_kp_k + δx_k`, `p_{k+1} = r_{k+1} + β_kp_k + δp_k` with `‖δ·‖ ≤ c u(…)`. Each of these is a direct instance of (3.4), (3.11), sqrt-rounding and the axpy bound. This is exactly the interface the backbone must export: **"perturbed-recurrence hypotheses with `γ`-bounds"**.
2. **Exact-arithmetic theorem about perturbed recurrences (no `fl` at all).** Chapter 17's (17.5)–(17.13), (17.18)–(17.20) are pure algebra: Neumann series, `AG^k = H^kA`, Jordan/diagonalizability of `M⁻¹N`, the constant `c(A)`, `σ`. Paige's theorem has the same nature: *given* `AV_k = V_kT_k + β_{k+1}v_{k+1}e_kᵀ + F_k` and the local orthogonality bounds, the Ritz pairs `(θ_i^{(k)}, y_i^{(k)} = V_kz_i)` satisfy `‖Ay_i − θ_iy_i‖ ≤ β_{k+1}|e_kᵀz_i| + ε_1‖A‖` and, crucially, `v_{k+1}ᵀy_i^{(k)} = ε_{ki}/(β_{k+1}e_kᵀz_i)` with `|ε_{ki}| ≤ c u‖A‖`: orthogonality is lost precisely in the direction of *converged* Ritz vectors. Greenbaum's backward-error theorem (finite-precision CG/Lanczos for `A` behaves for `k` steps like exact CG for a larger matrix `Â` with eigenvalues in tiny intervals `[λ_i − δ, λ_i + δ]`, `δ = O(u‖A‖·poly(n,k))`) and the Meurant–Strakoš Acta Numerica (2006) account are likewise theorems about *exact* three-term recurrences with bounded perturbation terms. So they belong to the exact-arithmetic Krylov library, parametrized by perturbation bounds `ε_0, ε_1` (with `ε = 0` recovering the exact theory: orthogonality, finite termination, the Ritz-value/Chebyshev bounds).
3. **Instantiation.** Plug layer 1 into layer 2 to get the finite-precision statement with `u`-dependent constants.

Statement shapes to reserve room for:
- *Limiting accuracy* (ch. 17 style): `‖e_{m+1}‖ ≤ ‖G^{m+1}e_0‖ + C·u·(problem-dependent constants)`, i.e. exact-arithmetic decay term + floor. Both `θ_x` (a bound on the computed iterates relative to the solution — a hypothesis on the *execution*, not on the data) and `c(A)`/`σ` (spectral constants of the splitting) appear; a formalization should keep them as explicit hypotheses/definitions rather than hiding them in `O(·)`.
- *Backward error at each step* (residual recurrences (17.18); for CG the *true* residual `b − Ax_k` vs the *recursively updated* residual differ by `‖ΔA‖`-type accumulations: `‖(b − Ax̂_k) − r̂_k‖ ≤ c k u ‖A‖ max_{j≤k}‖x̂_j‖` — Greenbaum 1997; Sleijpen–van der Vorst).
- *Perturbed-recurrence structure theorems* (Paige): quantified over `F_k, ε_0, ε_1`, output orthogonality-loss identities.
- *Products of perturbed matrices* (ch. 18, (18.10)): `∏(A + ΔA_i)` with `|ΔA_i| ≤ γ|A|` — needs the `S`-similarity lemma of Theorem 18.1 or the pseudospectral radius; both live in the exact library.

The exact-arithmetic backbone can therefore *reserve* the floating-point place by (a) stating its Krylov/stationary-iteration theorems with explicit perturbation terms and hypotheses, i.e. `perturbedLanczos (F : Fin k → K^n) (ε₀ ε₁ : K) …`, and (b) keeping the componentwise matrix-inequality API (13.3) available, so that the Layer-A lemmas can later discharge those hypotheses. Note that the Lanczos/CG results are stated *normwise* (`‖f_j‖_2 ≤ ε_1‖A‖_2`), so the conversion module of 13.3 (componentwise mat-vec bound (3.11) ⇒ `‖Δ(Av)‖_2 ≤ γ_m‖|A|‖_2‖v‖_2 ≤ √n γ_m ‖A‖_2‖v‖_2`) is on the critical path.

### 13.5 Existing formalizations

- **Coq:** *Flocq* (Boldo–Melquiond) is the reference: generic formats as subsets of ℝ (`{m·β^e}` with a format predicate), rounding to nearest/directed as functions with proofs of Theorem 2.2-type bounds, Sterbenz, FMA, IEEE-754 binary encodings; *Gappa*, *CoqInterval*; **VCFloat** (Appel–Kellison) for C-level verification; **LAProof** (Kellison, Appel et al., ARITH 2023) formalizes exactly Higham's chapter-3 material — dot product, matrix–vector, backward/forward `γ_n`-style bounds — on top of Flocq/VST, and would be the closest existing analogue of "Layer A on Layer B". Boldo et al.'s wave-equation and Clément's numerical-scheme verifications also use this style.
- **Isabelle/HOL:** `IEEE_Floating_Point` (AFP; Yu, Lochbihler), used with the HOL-Analysis reals. **HOL Light:** Harrison's floating-point theory (used for Intel transcendental verification; proves the standard model from the format). **ACL2:** Russinoff's RTL library. **PVS:** NASA's `float` library.
- **Lean 4 core:** `Float` is opaque (`structure Float where val : floatSpec.float`, where `floatSpec : FloatSpec` is an axiomatized structure with *no algebraic laws*); operations are `@[extern]` C calls. There are essentially **no theorems** about `Float` arithmetic in core or Batteries, so nothing can be proved about it; it is unusable as Layer B.
- **Mathlib:** `Mathlib/Data/FP/Basic.lean` (ported from Lean 3 core, M. Carneiro) defines `FP.RMode`, `FP.FloatCfg` (precision `prec`, `emax`, `emin`), an inductive `FP.Float` (inf/nan/finite with sign, exponent, mantissa), rounding of rationals (`FP.Float.ofPosRatDn/Up/Nearest`), `next_up/down`, and partial definitions of `add` (with `mul`/`div` left as TODO); it has **no theorems** and is a definitional sketch only. Mathlib does provide the exact ingredients Layer A needs: ordered fields, `abs`, `Finset.prod` bounds (Bernoulli's inequality `one_add_mul_le_pow`), matrices with entrywise order, several matrix norms (13.3), `spectralRadius` + Gelfand, Hermitian spectral theorem, `Matrix.PosDef`, `Matrix.det`, `LU`-free but `Matrix.BlockTriangular`, Cholesky is absent, interlacing is absent, Jordan form is absent, Schur triangularization is absent as a matrix statement (there is `Module.End` triangularizability over algebraically closed fields via `iSup_maxGenEigenspace_eq_top`).
- **Lean 4 third-party (quick web check, 2026):** (i) **flean** (MinusGix) — formalizes floating-point formats, all five IEEE 754 rounding modes, arithmetic operations and their error bounds, generic over any linearly ordered field, following Muller et al.'s *Handbook of Floating-Point Arithmetic*; (ii) **FloatSpec** (Beneficial-AI-Foundation, on Reservoir, depends on Mathlib v4.25) — a foundation for rounding, ulp, error bounds and IEEE 754 encodings/decodings, i.e. Flocq-like; (iii) **FLoPS** (Rutgers APL) — a Lean 4 formalization of the IEEE P3109 small-format standard's semantics (uses Mathlib's `EReal`). None of these provides the `γ_n` calculus or matrix-level backward error theorems; any of them (or a purpose-built minimal `F(β,t,e_min,e_max)`) could serve as the `ofFormat` instance of the `RoundingModel` interface, whose only obligation is Theorem 2.2/2.3 (and, for Layer-B extras, Sterbenz and error-free transformations). I have not audited their maturity or licences.
  Sources: [flean](https://github.com/MinusGix/flean), [FloatSpec on Reservoir](https://reservoir.lean-lang.org/@Beneficial-AI-Foundation/FloatSpec), [FLoPS paper](https://arxiv.org/html/2602.15965), [FLoPS repo](https://github.com/rutgers-apl/FLoPS).

### 13.6 Summary recommendation

1. Make the backbone *model-polymorphic*: theorems over `(M : RoundingModel K)`; exact arithmetic is `M = exact` (`u = 0`), so no result is stated twice.
2. Put `γ/θ` (13.2), the perturbed-product lemmas (3.6–3.8), the inner-product/mat-vec lemmas ((3.4), (3.11)–(3.13)) and Lemma 8.4 (any-order summation with a division) in a single `FloatModel/Basic` module; these plus entrywise matrix inequalities generate Theorems 8.5, 9.3–9.4, 10.3–10.5, 19.3–19.4 as short corollaries.
3. State iterative-method results (ch. 17, Lanczos/CG) as exact theorems about perturbed recurrences with explicit `ε` hypotheses; the floating-point content is a separate "model lemma" discharging those hypotheses.
4. Keep Layer B (`F` as a discrete set, `fl` as a function, Sterbenz, error-free transformations, monotonicity) as an optional instance; only chapter 2 (§2.1, 2.5, 2.6), (4.7), and chapters 26–27 depend on it.
5. Componentwise first, normwise by conversion (Lemma 6.6 / Table 6.2).

### 13.7 Sketch of interface signatures (Lean-flavoured pseudocode, not checked)

```lean
/-- Layer 0/A: an abstract "arithmetic with relative error u". -/
structure RoundingModel (K : Type*) [LinearOrderedField K] where
  u : K
  u_nonneg : 0 ≤ u
  Rounds : K → K → Prop                       -- `Rounds x y`: y is an admissible computed value of x
  abs_sub_le : ∀ x y, Rounds x y → |y - x| ≤ u * |x|       -- (2.4)
  abs_sub_le' : ∀ x y, Rounds x y → |y - x| ≤ u * |y|      -- (2.5); derivable with u ↦ u/(1-u)

namespace RoundingModel
def exact (K) : RoundingModel K := ⟨0, le_rfl, Eq, by simp, by simp⟩
def adversarial (u : K) (hu : 0 ≤ u) (hu1 : u < 1) : RoundingModel K :=
  ⟨u, hu, fun x y => |y - x| ≤ u * |x|, fun _ _ h => h, …⟩
-- `ofFormat` : from a discrete format with round-to-nearest; obligation = Theorems 2.2/2.3.
end RoundingModel

/-- γ_n and the θ-predicate. -/
def gamma (u : K) (n : ℕ) : K := n * u / (1 - n * u)
def IsRelPert (ε x y : K) : Prop := |y - x| ≤ ε * |x|        -- y = x(1+θ), |θ| ≤ ε

theorem gamma_mono {u : K} (hu : 0 ≤ u) {m n : ℕ} (h : m ≤ n) (hn : n * u < 1) : gamma u m ≤ gamma u n
theorem lemma_3_1 {u : K} (hu : 0 ≤ u) (δ : Fin n → K) (ρ : Fin n → ℤˣ) (hδ : ∀ i, |δ i| ≤ u)
    (hn : n * u < 1) : |∏ i, (1 + δ i) ^ (ρ i : ℤ) - 1| ≤ gamma u n
theorem lemma_3_3_mul (h₁ : |θ₁| ≤ gamma u k) (h₂ : |θ₂| ≤ gamma u j) (hkj : (k + j) * u < 1) :
    |(1 + θ₁) * (1 + θ₂) - 1| ≤ gamma u (k + j)
theorem lemma_3_3_div_le (h₁ : |θ₁| ≤ gamma u k) (h₂ : |θ₂| ≤ gamma u j) (hjk : j ≤ k) … :
    |(1 + θ₁) / (1 + θ₂) - 1| ≤ gamma u (k + j)
theorem lemma_3_4 (hδ : ∀ i, |δ i| ≤ u) (hn : n * u ≤ 1 / 100) : |∏ i, (1 + δ i) - 1| ≤ (101/100) * n * u

/-- Nondeterministic evaluation of expression trees (option (ii) of 13.1). -/
inductive FlExpr (K) | const : K → FlExpr K | add | sub | mul | div : FlExpr K → FlExpr K → FlExpr K | sqrt : FlExpr K → FlExpr K
inductive Evals (M : RoundingModel K) : FlExpr K → K → Prop
  | const : Evals M (.const c) c
  | add  : Evals M a ya → Evals M b yb → M.Rounds (ya + yb) y → Evals M (.add a b) y
  | …
/-- All binary summation trees over a list (any order, any bracketing). -/
inductive SumTree (K) : List K → FlExpr K → Prop

/-- (3.4) inner product, any order.  Componentwise backward error. -/
theorem dot_backward (M : RoundingModel K) (x y : Fin n → K) (e) (he : DotTree x y e) (s) (hs : Evals M e s)
    (hn : n * M.u < 1) : ∃ Δy : Fin n → K, (∀ i, |Δy i| ≤ gamma M.u n * |y i|) ∧ s = ∑ i, x i * (y i + Δy i)

/-- Lemma 8.4 and Theorem 8.5 (entrywise order on matrices). -/
theorem triangular_solve_backward (M : RoundingModel K) (T : Matrix (Fin n) (Fin n) K) (hT : T.BlockTriangular id)
    (hdet : IsUnit T.det) (b x̂ : Fin n → K) (hx̂ : SubstitutionExec M T b x̂) (hn : n * M.u < 1) :
    ∃ ΔT, (∀ i j, |ΔT i j| ≤ gamma M.u n * |T i j|) ∧ (T + ΔT).mulVec x̂ = b

/-- Theorem 9.3 / 9.4. -/
theorem lu_backward … : ∃ ΔA, (∀ i j, |ΔA i j| ≤ gamma M.u n * (|L̂| * |Û|) i j) ∧ L̂ * Û = A + ΔA
theorem ge_solve_backward … : ∃ ΔA, (∀ i j, |ΔA i j| ≤ gamma M.u (3*n) * (|L̂| * |Û|) i j) ∧ (A + ΔA).mulVec x̂ = b

/-- Chapter 17 interface: model lemma + exact perturbed-recurrence theorem. -/
theorem stationary_model_lemma (M : RoundingModel K) … (hexec : StationaryExec M Mtx N b x̂) :
    ∀ k, ∃ ξ, Mtx.mulVec (x̂ (k+1)) = N.mulVec (x̂ k) + b + ξ ∧
      ∀ i, |ξ i| ≤ c n * M.u * ((|Mtx|.mulVec |x̂ (k+1)| + |N|.mulVec |x̂ k| + |b|) i)
theorem stationary_forward_error_exact (G := Mtx⁻¹ * N) (hρ : spectralRadius ℂ G < 1) (ξ : ℕ → Fin n → K)
    (hξ : ∀ k i, |ξ k i| ≤ μ i) (hrec : ∀ k, Mtx.mulVec (x̂ (k+1)) = N.mulVec (x̂ k) + b + ξ k) :
    ∀ m i, |x i - x̂ (m+1) i| ≤ |(G^(m+1)).mulVec (x - x̂ 0) i| + (∑ k in range (m+1), (|G^k * Mtx⁻¹|.mulVec μ) i)
```

The `exact` instance makes every `Evals`-theorem specialize to the exact-arithmetic backbone: `Evals (exact K) e y ↔ y = eval e`. The `adversarial` instance is what all of chapters 3–19 are really about. `ofFormat` is optional and can be supplied later by any of the Lean float libraries in 13.5.

---

## 14. Result index: layer, form, dependencies (formalization order)

Legend — Layer: **A** = standard model only (real numbers with δ's); **B** = needs the discrete format `F` (round-to-nearest as a function, exponents, base); **C** = IEEE-specific. Form: **cw** componentwise/entrywise, **col** columnwise 2-norm, **nw** normwise, **ex** exact-arithmetic (no `u` at all).

| Result | Layer | Form | Depends on | Notes |
|---|---|---|---|---|
| Lemma 2.1 (spacing) | B | — | def. of `F` | needs exponent structure |
| Thm 2.2 `fl(x) = x(1+δ)` | B | — | Lemma 2.1 | *produces* the model; obligation of `ofFormat` |
| Thm 2.3 `fl(x) = x/(1+δ)` | B | — | Thm 2.2 proof | dual form |
| Model (2.4)/(2.5)/(2.6) | A (axiom) | — | — | the interface |
| Thm 2.4 Ferguson, Thm 2.5 Sterbenz | B | — | digits/exponents | not derivable from (2.4) |
| FMA model, exact product (Pb 2.26) | A / B | — | — | model part A; exactness B |
| (3.3)–(3.5) inner product | A | cw | L3.1 | first application; `SumTree` induction |
| (3.6) outer product | A | cw | — | forward only, not backward stable |
| Alg 3.2 running error | A | cw | (2.5) | a posteriori |
| Lemma 3.1 | A | — | Bernoulli | core |
| Lemma 3.3 | A | — | L3.1 | core; 6 rules |
| Lemma 3.4 | A | — | `exp` bound | optional sharper constant |
| Lemma 3.5 complex ops | A | — | L3.1, L3.3, C–S | gives `RoundingModel ℂ` |
| Lemmas 3.6–3.8 products | A | nw/F/cw | L3.1 | needed by ch. 19 and (18.10) |
| Lemma 3.9 rank-1 update | A | cw | (3.4) | Householder/Gram–Schmidt |
| (3.11)–(3.13) mat-vec/mat-mat | A | cw (+nw) | (3.4), L6.6 | mat-vec is the Krylov interface |
| (4.1)–(4.4), (4.6) summation | A | cw | (2.5) | any tree; pairwise `log n` |
| (4.7) FastTwoSum exactness | B | — | base 2, RN | error-free transformation |
| (4.8)–(4.9) Kahan bound | A | cw | model only | long induction (Knuth/Goldberg) |
| Def 6.1, Thm 6.2, Lemma 6.3, Thm 6.4, Thm 6.5 | ex | nw | duality | Mathlib has most ingredients |
| Lemma 6.6, Tables 6.1/6.2 | ex | cw→nw | SVD/Frobenius | the conversion module |
| Thm 7.1 Rigal–Gaches | ex | nw | dual vector | backward error formula |
| Thm 7.2 | ex | nw | Neumann series | perturbation bound |
| Thm 7.3 Oettli–Prager | ex | cw | — | backward error formula |
| Thm 7.4 Skeel | ex | cw | `|A⁻¹|` Neumann | perturbation bound |
| Thms 7.5–7.8 scaling | ex | nw | (6.12), Perron | optional |
| §7.6 stability definitions | ex | both | 7.1, 7.3 | definitions only |
| (7.30)–(7.31), Lemma 7.9 | A/ex | cw | (3.11) | practical bounds |
| Lemma 8.2, Thm 8.3 | A | cw | L3.1 | fixed order |
| Lemma 8.4 | A | cw | `SumTree` | any order + division |
| **Thm 8.5** | A | cw | L8.4 | `|ΔT| ≤ γ_n|T|` |
| (8.2) forward bound | ex | cw | 8.5, 7.4 | |
| Lemma 8.6, Thm 8.7 | A/ex | cw | 8.5 | pivoted triangles |
| Lemma 8.8 | ex | cw | — | row diag. dominant |
| Lemma 8.9, Thm 8.10, Cor 8.11 | A/ex | cw | M-matrix theory | direct forward analysis |
| Thm 8.12, Alg 8.13, Thm 8.14 | ex | cw/nw | M-matrix theory | inverse bounds |
| Thm 9.1 | ex | — | leading minors | existence/uniqueness |
| **Thm 9.3** | A | cw | L8.4 | `|ΔA| ≤ γ_n|L̂||Û|` |
| **Thm 9.4** | A | cw | 9.3, 8.5, L3.3 | `γ_{3n}` |
| (9.9) totally nonneg. | A | cw | 9.4 | `L,U ≥ 0` |
| Thm 9.5 Wilkinson | A→nw | nw | 9.4, growth | uses exact-`L,U` bounds ("illicit") |
| Lemma 9.6, Thms 9.7–9.11 growth | ex | nw | combinatorics | growth factor theory |
| Thms 9.13–9.14 tridiagonal | A | cw | 9.3/9.4 specialised | |
| Thm 9.15 LU perturbation | ex | nw | — | optional |
| Thm 10.1, Alg 10.2 | ex | — | induction on `n` | Cholesky exists (absent in Mathlib) |
| **Thm 10.3, 10.4** | A | cw | L8.4 + sqrt variant, 8.5 | `γ_{n+1}`, `γ_{3n+1}` |
| Cholesky nw bound | A→nw | nw | 10.4, L6.6(d) | `cn²u‖A‖_2` |
| Thm 10.5 Demmel | A | cw | 10.3, C–S | `ddᵀ` form |
| Thm 10.6 | A→nw | nw (scaled) | 10.5, Cor 7.6 | `κ_2(H)` |
| **Thm 10.7** (success) | A | nw | 10.5, interlacing | needs partial-execution semantics |
| Thm 10.8 Sun, §10.3–10.4 | ex/A | nw | — | optional |
| (17.1)–(17.2) model lemma | A | cw | 8.5, (3.11) | the *only* floating-point step in ch. 17 |
| (17.3)–(17.13), (17.15) forward | ex | cw/nw | Neumann, `c(A)` | perturbed recurrence |
| (17.18)–(17.20) backward | ex | nw | `H = NM⁻¹`, diagonalization | `σ` |
| §17.4 singular | ex | cw/nw | Drazin inverse | optional |
| (17.33) stopping tests | ex | nw/cw | 7.1, 7.3 | |
| §18.1 exact powers, Gelfand | ex | nw | Jordan/Schur, pseudospectra | Mathlib: `spectralRadius` |
| (18.10)–(18.12) | A | cw | (3.11), L3.8 | product of perturbed matrices |
| Thm 18.1 | A→nw | nw | Jordan form or Schur+scaling | needs `κ(X)` |
| Thm 18.2 | A→nw | nw | 18.1, pseudospectra | heuristic `O(ε²)` |
| Lemma 19.1 | A | — | L3.1, sqrt | Householder vector |
| Lemma 19.2 | A | col | L3.9 | `‖ΔP‖_F ≤ γ̃_m` |
| Lemma 19.3 | A | col | 19.2, L3.7, L3.1 | sequence of reflectors |
| **Thm 19.4** | A | col | 19.3 | exact orthogonal `Q` |
| Thm 19.5 | A | col | 19.4, 19.3, 8.5 | linear solve by QR |
| Thm 19.6 | A | row | 19.3 + pivoting | Powell–Reid |
| Lemmas 19.7–19.9, Thm 19.10 Givens | A | col | L3.6 | disjoint rotations |
| Thm 19.13 MGS | A | nw | Householder on `[0;A]` | |
| Paige/Greenbaum (external) | A + ex | nw | (3.4), (3.11), sqrt; exact 3-term recurrence theory | see 13.4 |

Reading the table bottom-up gives a formalization order: (1) `gamma`/`IsRelPert` + Lemmas 3.1/3.3/3.4; (2) `FlExpr`/`SumTree` + (3.4), Lemma 8.4; (3) entrywise matrix API + (3.11)–(3.13), Lemmas 3.6–3.9; (4) Theorems 8.5, 9.3, 9.4, 10.3, 10.4, 10.5; (5) conversion module (Lemma 6.6, Tables 6.1/6.2) and Theorems 7.1–7.4; (6) Householder/Givens chain 19.1–19.4, 19.10; (7) the chapter 17 model lemma and (18.10) as the hooks for the iterative-methods library; (8) Layer B (`ofFormat`, Theorem 2.2, Sterbenz, (4.7)) whenever a concrete format is wanted.
