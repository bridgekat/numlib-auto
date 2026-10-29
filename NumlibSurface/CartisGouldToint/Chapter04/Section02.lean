import Mathlib.Basic.Real.ENatENNReal
import Numlib.Optimization.Complexity.CarmonChain
import NumlibSurface.CartisGouldToint.Chapter04.Section01

/-!
# Cartis–Gould–Toint §4.2: A lower complexity bound for finding first-order stationary points

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], §4.2, after Carmon, Duchi, Hinder
and Sidford. The content is in the backbone modules `Numlib.Optimization.Complexity.ZeroChain`,
`ResistingOracle` and `CarmonChain`.

## Notation

Functions are on `ℝⁿ = EuclideanSpace ℝ (Fin n)`, `n` arbitrary; a function of variable dimension
is a pair `⟨n, f⟩ : Σ n, ℝⁿ → ℝ`. Coordinates are `0`-based: the book's `[x]_j`, `j ∈ [1 : n]`, is
`x ⟨j - 1, _⟩`, and `e_j` is `EuclideanSpace.single j 1`.

* `functionClass Δ L p` — the class `𝓕(Δ, p)` (§4.2.1.1), with the Lipschitz constant `L` of
  `∇^p f` explicit; its members are `C^∞`, as in the book (footnote 29).
* `methodClassM p`, `methodClassZR p` — the classes `𝓜(p)` and `𝓜_ZR(p)` (§4.2.1.2, (4.2.1)) of
  deterministic `p`-th order methods starting at `x₀ = 0` (one method in every dimension, whose
  iterates are functions of `f(x_i), ∇f(x_i), …, ∇^p f(x_i)` at the previous iterates).
* `complexity 𝓜 𝓕 ε` — `#_ε(𝓜, 𝓕) = inf_{M ∈ 𝓜} sup_{f ∈ 𝓕} k_ε(M, f)` (4.2.2), in `ℕ∞`, where
  `k_ε(M, f)` is the index of the first iterate with `‖∇f(x_k)‖ ≤ ε` (`⊤` if there is none).
* `Optimization.IsZeroChain f p` — the zero-chain property (4.2.4).
* `hardFunction k̄` — the difficult function `f^D` of (4.2.6), and
  `Optimization.CarmonChain.lipschitzConst p` the constant `L^D_p` of Lemma 4.2.5 (iv).

## Main results

* `lemma_4_2_1`, `lemma_4_2_2`, `lemma_4_2_3` — zero chains and zero-respecting methods.
* `theorem_4_2_4_i`, `theorem_4_2_4_ii` — Theorem 4.2.4 (proved in the backbone by a resisting
  oracle; the book cites Carmon et al. for the proof).
* `lemma_4_2_5_i` – `lemma_4_2_5_iv`, `lemma_4_2_5_iv_growth` — properties of the difficult
  function.
* `theorem_4_2_6_i` — the lower bound (4.2.7).
* `arpOracleMethod` — ARp (§4.1, first-order mode) as a method of `𝓜(p)`;
  `complexity_le_arpComplexityBound` — the upper bound (4.2.3); `theorem_4_2_6_ii` — tightness:
  `#_ε(𝓜(p), 𝓕(Δ, p))` is of exact order `ε^{-(p+1)/p}` as `ε → 0`.

## Deviations from the book

* **(4.2.6)**: the first term of `f^D` is `-Ψ(1) Φ([x]_1)` (as in Carmon et al.), not the printed
  `-Ψ([x]_1) Φ([x]_1)`, with which `∇f^D(0) = 0` and Lemma 4.2.5 (ii) fails at `x = 0`.
* **Theorem 4.2.6**: with `k̄ = ⌊Δ/12 (L/L^D_p)^{1/p} ε^{-(p+1)/p}⌋`, the proof gives `#_ε ≥ k̄` for
  both classes; the book's `#_ε(𝓜(p), 𝓕(Δ, p)) ≥ 2 k̄` does not follow from Theorem 4.2.4. The
  form `c₀ Δ (L/L^D_p)^{1/p} ε^{-(p+1)/p}` (with `c₀ = 1/24`) needs that quantity to be at least
  `12`, i.e. `ε` small enough: for large `ε` the complexity is `0`.
* Lemma 4.2.5 (iv) is proved with an explicit constant `L^D_p` independent of `k̄`, and the growth
  bound `L^D_p ≤ exp(5/2 p log p + c₁ p)` holds with `c₁ = 20` (`lemma_4_2_5_iv_growth`).
* **(4.2.3) and tightness**: the upper bound uses the constants of Theorem 4.1.5 (i) with
  `L_{f,p} = max(1, L)` and is stated with an integer part. The upper bound scales like
  `Δ L^{(p+1)/p}` and the lower bound (4.2.7) like `Δ L^{1/p}`, so only the order in `ε` is
  tight; this is what `theorem_4_2_6_ii` states.
* Theorem 4.2.4 and the orthogonal invariance of `𝓕(Δ, p)` (footnote 30) assume `L ≥ 0`.
* A zero-respecting method is required to keep `[x_{k+1}]_j = 0` when `e_j` is a null direction
  of all `∇^q f(x_i)` (the multilinear map vanishes whenever one argument is `e_j`); for the
  symmetric derivatives of `C^p` functions this is the book's `∇^q f(x_i) e_j = 0`.
* Lemmas 4.2.2, 4.2.3 and Theorem 4.2.4 are stated without the unused hypotheses `ε > 0`,
  `p ≥ 1` and (for Lemma 4.2.2) `f ∈ 𝓕(Δ, p)`. Lemma 4.2.3 cites (4.2.3) for `#_ε`; it is
  (4.2.2).
-/

open Set Optimization
open scoped ContDiff

namespace CartisGouldToint.Chapter04

variable {n p : ℕ}

/-! ### §4.2.1 Problems and methods of interest -/

/-- The function class `𝓕(Δ, p)` of [cartis2022evaluation], §4.2.1.1: infinitely differentiable
`f : ℝⁿ → ℝ` (any `n`) whose `p`-th derivative is Lipschitz continuous with constant `L` (f.DpL),
bounded below (f.Bb) with `f(0) - inf f ≤ Δ`. -/
def functionClass (Δ L : ℝ) (p : ℕ) : Set (Σ n, EuclideanSpace ℝ (Fin n) → ℝ) :=
  smoothClass Δ L p

theorem functionClass_eq (Δ L : ℝ) (p : ℕ) : functionClass Δ L p = smoothClass Δ L p := rfl

theorem mem_functionClass {Δ L : ℝ} {F : Σ n, EuclideanSpace ℝ (Fin n) → ℝ} :
    F ∈ functionClass Δ L p ↔ ContDiff ℝ ∞ F.2 ∧ IteratedFDerivLipschitzOn F.2 p L univ ∧
      BddBelow (range F.2) ∧ F.2 0 - ⨅ x, F.2 x ≤ Δ :=
  Iff.rfl

/-- **Orthogonal invariance of `𝓕(Δ, p)`** ([cartis2022evaluation], §4.2.1.1, footnote 30): for
`f ∈ 𝓕(Δ, p)` on `ℝⁿ` and `U ∈ O(n̄, n)` (a linear isometry `ℝⁿ → ℝ^n̄`), `f_U = f ∘ Uᵀ` is in
`𝓕(Δ, p)`. -/
theorem comp_adjoint_mem_functionClass {Δ L : ℝ} (hL : 0 ≤ L) {m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ⟨n, f⟩ ∈ functionClass Δ L p)
    (U : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) :
    ⟨m, f ∘ isometryAdjoint U⟩ ∈ functionClass Δ L p :=
  comp_adjoint_mem_smoothClass hL hf U

/-- The class `𝓜(p)` of [cartis2022evaluation], §4.2.1.2: deterministic `p`-th order methods,
one in every dimension `n`, starting at `x₀ = 0`, whose iterate `x_{k+1}` is a function of
`f(x_i), ∇f(x_i), …, ∇^p f(x_i)`, `i ≤ k`. -/
abbrev methodClassM (p : ℕ) : Set (JetMethod p) := methodClass p

/-- The class `𝓜_ZR(p)` of zero-respecting methods of [cartis2022evaluation], §4.2.1.2, (4.2.1):
methods in `𝓜(p)` that, for every function, keep `[x_{k+1}]_j = 0` whenever `e_j` is a null
direction of `∇^q f(x_i)` for all `q ∈ [1 : p]` and `i ≤ k`. -/
abbrev methodClassZR (p : ℕ) : Set (JetMethod p) := zeroRespectingClass p

theorem methodClassZR_subset : methodClassZR p ⊆ methodClassM p :=
  zeroRespectingClass_subset_methodClass

/-- The complexity `#_ε(𝓜, 𝓕) = inf_{M ∈ 𝓜} sup_{f ∈ 𝓕} k_ε(M, f)` of a class of methods on a
class of functions ([cartis2022evaluation], (4.2.2)), where `k_ε(M, f) ∈ ℕ∞` is the index of the
first iterate of `M` on `f` with `‖∇f(x_k)‖ ≤ ε` (`⊤` if there is none). -/
noncomputable abbrev complexity (𝓜 : Set (JetMethod p))
    (𝓕 : Set (Σ n, EuclideanSpace ℝ (Fin n) → ℝ)) (ε : ℝ) : ℕ∞ :=
  classComplexity 𝓜 𝓕 ε

/-! ### §4.2.2 Zero chains -/

/-- **Lemma 4.2.1 (scale invariance of zero chains)** of [cartis2022evaluation]. If `f` is a
`p`-th order zero chain, `μ₁ ∈ ℝ` and `μ₂ ≠ 0`, then `x ↦ μ₁ f(x/μ₂)` is a `p`-th order zero
chain. -/
theorem lemma_4_2_1 {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsZeroChain f p) (μ₁ : ℝ) {μ₂ : ℝ}
    (hμ₂ : μ₂ ≠ 0) : IsZeroChain (fun x => μ₁ * f (μ₂⁻¹ • x)) p :=
  hf.comp_smul μ₁ hμ₂

/-- **Lemma 4.2.2 (zero-respecting methods applied to zero chains)** of [cartis2022evaluation].
If `M ∈ 𝓜_ZR(p)` and `f : ℝⁿ → ℝ` is a `p`-th order zero chain, the iterates of `M` on `f`
satisfy `[x_k]_j = 0` for all `j ∈ [k + 1 : n]` (`0`-based: all coordinates `j ≥ k`). -/
theorem lemma_4_2_2 {M : JetMethod p} (hM : M ∈ methodClassZR p)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsZeroChain f p) (k : ℕ) (j : Fin n) (hkj : k ≤ j) :
    M.iter n f k j = 0 :=
  (hM n f).iterate_apply_eq_zero hf k j hkj

/-- **Lemma 4.2.3 (zero-respecting methods are slow on zero chains)** of [cartis2022evaluation].
Let `⟨n, f⟩ ∈ 𝓕(Δ, p)` be a `p`-th order zero chain with `‖∇f(x)‖ > ε` whenever `[x]_n = 0`
(4.2.5). Then `#_ε(𝓜_ZR(p), 𝓕(Δ, p)) ≥ #_ε(𝓜_ZR(p), {f}) ≥ n`. -/
theorem lemma_4_2_3 {Δ L ε : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ⟨n, f⟩ ∈ functionClass Δ L p) (hf : IsZeroChain f p)
    (hgrad : ∀ (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)), x ⟨n - 1, by omega⟩ = 0 →
      ε < ‖fderiv ℝ f x‖) :
    complexity (methodClassZR p) {⟨n, f⟩} ε ≤ complexity (methodClassZR p) (functionClass Δ L p) ε ∧
      (n : ℕ∞) ≤ complexity (methodClassZR p) {⟨n, f⟩} ε :=
  ⟨classComplexity_mono_right (singleton_subset_iff.2 hF),
    (le_classComplexity_of_isZeroChain hf hgrad hF).1⟩

/-- Members of `𝓕(Δ, p)` are `C^p` and differentiable. -/
theorem contDiff_differentiable_of_mem_functionClass {Δ L : ℝ}
    {F : Σ n, EuclideanSpace ℝ (Fin n) → ℝ} (hF : F ∈ functionClass Δ L p) :
    ContDiff ℝ p F.2 ∧ Differentiable ℝ F.2 :=
  ⟨hF.1.of_le (by exact_mod_cast le_top), hF.1.differentiable (by simp)⟩

/-- **Theorem 4.2.4** of [cartis2022evaluation], first part: for every `ε`,
`#_ε(𝓜(p), 𝓕(Δ, p)) ≥ #_ε(𝓜_ZR(p), 𝓕(Δ, p))`. -/
theorem theorem_4_2_4_i {Δ L : ℝ} (hL : 0 ≤ L) (ε : ℝ) :
    complexity (methodClassZR p) (functionClass Δ L p) ε ≤
      complexity (methodClassM p) (functionClass Δ L p) ε :=
  classComplexity_zeroRespecting_le _ (fun _ hF _ U => comp_adjoint_mem_functionClass hL hF U)
    (fun _ hF => contDiff_differentiable_of_mem_functionClass hF) ε

/-- **Theorem 4.2.4** of [cartis2022evaluation], second part: if `⟨n, f⟩ ∈ 𝓕(Δ, p)` and
`#_ε(𝓜_ZR(p), {f}) ≥ k̄`, then `#_ε(𝓜(p), 𝓕(Δ, p)) ≥ #_ε(𝓜(p), {f_U}) ≥ k̄`, where `{f_U}` is the
set of all `f_U = f ∘ Uᵀ : ℝ^{n+k̄} → ℝ` with `U ∈ O(n + k̄, n)`. -/
theorem theorem_4_2_4_ii {Δ L ε : ℝ} (hL : 0 ≤ L) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ⟨n, f⟩ ∈ functionClass Δ L p) {k : ℕ}
    (hk : (k : ℕ∞) ≤ complexity (methodClassZR p) {⟨n, f⟩} ε) :
    complexity (methodClassM p) {F | ∃ U : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (n + k)), F = ⟨n + k, f ∘ isometryAdjoint U⟩} ε ≤
        complexity (methodClassM p) (functionClass Δ L p) ε ∧
      (k : ℕ∞) ≤ complexity (methodClassM p) {F | ∃ U : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (n + k)), F = ⟨n + k, f ∘ isometryAdjoint U⟩} ε := by
  obtain ⟨hc, hd⟩ := contDiff_differentiable_of_mem_functionClass hF
  refine ⟨classComplexity_mono_right ?_, le_classComplexity_comp_adjoint _ hc hd hk⟩
  rintro _ ⟨U, rfl⟩
  exact comp_adjoint_mem_functionClass hL hF U

/-! ### The difficult function -/

/-- The difficult function `f^D : ℝ^k̄ → ℝ` of [cartis2022evaluation], (4.2.6), with the first
term corrected to `-Ψ(1) Φ([x]_1)`:
`f^D(x) = -Ψ(1) Φ([x]_1) + ∑_{i=2}^{k̄} [Ψ(-[x]_{i-1}) Φ(-[x]_i) - Ψ([x]_{i-1}) Φ([x]_i)]`,
where `Ψ(y) = 0` for `y ≤ 1/2`, `Ψ(y) = exp(1 - (2y - 1)^{-2})` otherwise
(`Optimization.CarmonChain.psi`), and `Φ(y) = e^{1/2} ∫_{-∞}^y e^{-t²/2} dt`
(`Optimization.CarmonChain.phi`). -/
noncomputable def hardFunction (k : ℕ) : EuclideanSpace ℝ (Fin k) → ℝ :=
  CarmonChain.chain k

theorem hardFunction_eq (k : ℕ) : hardFunction k = CarmonChain.chain k := rfl

/-- **Lemma 4.2.5 (i)** of [cartis2022evaluation]: for every `p ≥ 1`, `f^D` is a `p`-th order
zero chain. (It holds for every `p`.) -/
theorem lemma_4_2_5_i (k p : ℕ) : IsZeroChain (hardFunction k) p :=
  CarmonChain.isZeroChain_chain p

/-- **Lemma 4.2.5 (ii)** of [cartis2022evaluation]: if `|[x]_i| < 1` for some `i ≤ k̄`, there is
`j ≤ i` with `|[x]_j| < 1` and `‖∇f^D(x)‖ ≥ |∂f^D/∂[x]_j (x)| > 1`. -/
theorem lemma_4_2_5_ii {k : ℕ} {x : EuclideanSpace ℝ (Fin k)} {i : Fin k} (hi : |x i| < 1) :
    ∃ j : Fin k, j ≤ i ∧ |x j| < 1 ∧
      |fderiv ℝ (hardFunction k) x (EuclideanSpace.single j 1)| ≤
        ‖fderiv ℝ (hardFunction k) x‖ ∧
      1 < |fderiv ℝ (hardFunction k) x (EuclideanSpace.single j 1)| := by
  obtain ⟨j, hji, hxj, hj, -⟩ := CarmonChain.exists_abs_partial_chain_gt_one hi
  refine ⟨j, hji, hxj, ?_, hj⟩
  rw [← Real.norm_eq_abs]
  refine ((fderiv ℝ (hardFunction k) x).le_opNorm _).trans_eq ?_
  simp

/-- **Lemma 4.2.5 (iii)** of [cartis2022evaluation]: `f^D` is bounded below and
`f^D(0) - f^D_low ≤ 12 k̄`, with `f^D_low = inf f^D`. -/
theorem lemma_4_2_5_iii (k : ℕ) :
    BddBelow (range (hardFunction k)) ∧ hardFunction k 0 - ⨅ x, hardFunction k x ≤ 12 * k :=
  CarmonChain.chain_zero_sub_iInf_le

/-- **Lemma 4.2.5 (iv)** of [cartis2022evaluation], without the growth estimate: for every
`p ≥ 1`, `∇^p f^D` is Lipschitz continuous (f.DpL) with a constant
`L^D_p = Optimization.CarmonChain.lipschitzConst p > 0` that does not depend on `k̄`. -/
theorem lemma_4_2_5_iv {p : ℕ} (hp : 1 ≤ p) :
    0 < CarmonChain.lipschitzConst p ∧ ∀ k : ℕ,
      IteratedFDerivLipschitzOn (hardFunction k) p (CarmonChain.lipschitzConst p) univ :=
  ⟨CarmonChain.lipschitzConst_pos p, fun _ => CarmonChain.lipschitzOn_iteratedFDeriv_chain hp⟩

/-- **Lemma 4.2.5 (iv)** of [cartis2022evaluation], with the growth estimate: there is an
absolute constant `c₁ > 0` such that for every `p ≥ 1`, `∇^p f^D` is Lipschitz continuous
(f.DpL) with the constant `L^D_p = Optimization.CarmonChain.lipschitzConst p`, independent of
`k̄`, and `L^D_p ≤ exp(5/2 p log p + c₁ p)`. One may take `c₁ = 20`
(`Optimization.CarmonChain.lipschitzConst_le_exp_twenty`). -/
theorem lemma_4_2_5_iv_growth :
    ∃ c₁ > 0, ∀ p : ℕ, 1 ≤ p →
      (∀ k : ℕ, IteratedFDerivLipschitzOn (hardFunction k) p (CarmonChain.lipschitzConst p) univ) ∧
        CarmonChain.lipschitzConst p ≤ Real.exp (5 / 2 * p * Real.log p + c₁ * p) := by
  obtain ⟨c₁, hc₁, h⟩ := CarmonChain.lipschitzConst_le_exp
  exact ⟨c₁, hc₁, fun p hp => ⟨(lemma_4_2_5_iv hp).2, h p hp⟩⟩

/-! ### The lower bound -/

/-- `⌊x⌋ ≥ x / 2` for `x ≥ 1`. -/
private theorem div_two_le_floor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ ⌊x⌋₊ := by
  have h := Nat.lt_floor_add_one x
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.le_floor (by simpa using hx)
  linarith

/-- **Theorem 4.2.6 (lower complexity bound)** of [cartis2022evaluation], corrected. Let
`p ≥ 1`, `Δ, L, ε > 0`, `L^D_p = Optimization.CarmonChain.lipschitzConst p` (Lemma 4.2.5 (iv)) and
`Y = Δ (L/L^D_p)^{1/p} ε^{-(p+1)/p}`. Then
`#_ε(𝓜(p), 𝓕(Δ, p)) ≥ #_ε(𝓜_ZR(p), 𝓕(Δ, p)) ≥ ⌊Y/12⌋` and `#_ε(𝓜(p), 𝓕(Δ, p)) ≥ ⌊Y/12⌋`;
consequently, (4.2.7) holds with `c₀ = 1/24` whenever `Y ≥ 12`: both complexities are at least
`c₀ Y` (compared in `ℝ≥0∞`). -/
theorem theorem_4_2_6_i (hp : 1 ≤ p) {Δ L ε : ℝ} (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε) :
    let Y := Δ * (L / CarmonChain.lipschitzConst p) ^ (1 / p : ℝ) * ε ^ (-((p + 1 : ℝ) / p))
    complexity (methodClassZR p) (functionClass Δ L p) ε ≤
        complexity (methodClassM p) (functionClass Δ L p) ε ∧
      ((⌊Y / 12⌋₊ : ℕ) : ℕ∞) ≤ complexity (methodClassZR p) (functionClass Δ L p) ε ∧
      ((⌊Y / 12⌋₊ : ℕ) : ℕ∞) ≤ complexity (methodClassM p) (functionClass Δ L p) ε ∧
      (12 ≤ Y → ENNReal.ofReal (1 / 24 * Y) ≤
        (complexity (methodClassZR p) (functionClass Δ L p) ε : ENNReal) ∧
        ENNReal.ofReal (1 / 24 * Y) ≤
          (complexity (methodClassM p) (functionClass Δ L p) ε : ENNReal)) := by
  intro Y
  have hY : Y / 12 = Δ / 12 * (L / CarmonChain.lipschitzConst p) ^ (1 / p : ℝ) *
      ε ^ (-((p + 1 : ℝ) / p)) := by simp only [Y]; ring
  obtain ⟨h1, h2⟩ := CarmonChain.le_classComplexity_smoothClass_methodClass hp hΔ hL hε
  rw [← hY] at h1 h2
  have hc : ∀ c : ℕ∞, ((⌊Y / 12⌋₊ : ℕ) : ℕ∞) ≤ c → 12 ≤ Y →
      ENNReal.ofReal (1 / 24 * Y) ≤ (c : ENNReal) := by
    intro c hc hY12
    refine le_trans ?_ (ENat.toENNReal_le.2 hc)
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have := div_two_le_floor (x := Y / 12) (by linarith)
    linarith
  exact ⟨theorem_4_2_4_i hL.le ε, h1, h2, fun hY12 => ⟨hc _ h1 hY12, hc _ h2 hY12⟩⟩

/-! ### ARp as a method of `𝓜(p)` and the tightness of the lower bound -/

namespace ARpOracle

theorem taylorSum_jetSeries_jetOracle (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (jetSeries (jetOracle f p x)).taylorSum p = (ftaylorSeries ℝ f x).taylorSum p :=
  FormalMultilinearSeries.taylorSum_congr fun _ hi => jetSeries_jetOracle f x hi

theorem regularizedModel_jetSeries_jetOracle (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (σ : ℝ) :
    regularizedModel (jetSeries (jetOracle f p x)) p σ =
      regularizedModel (ftaylorSeries ℝ f x) p σ := by
  funext s
  rw [regularizedModel_def, regularizedModel_def, taylorSum_jetSeries_jetOracle]

theorem taylorDecrement_jetSeries_jetOracle (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) :
    (jetSeries (jetOracle f p x)).taylorDecrement p s =
      (ftaylorSeries ℝ f x).taylorDecrement p s := by
  simp only [FormalMultilinearSeries.taylorDecrement_def, taylorSum_jetSeries_jetOracle]

/-- The first-order termination test (4.1.5) on a jet: `‖J₁‖ ≤ ε`. -/
def jetTest (ε : ℝ) (J : Jet (EuclideanSpace ℝ (Fin n)) p) : Prop :=
  ‖jetSeries J 1‖ ≤ ε

theorem jetTest_jetOracle (hp : 1 ≤ p) {ε : ℝ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    jetTest ε (jetOracle f p x) ↔ ‖gradient f x‖ ≤ ε := by
  rw [jetTest, jetSeries_jetOracle f x hp, norm_gradient_eq]
  simp [ftaylorSeries]

/-- The state of ARp: the iterate, the regularization weight and the jet at the iterate. -/
abbrev State (n p : ℕ) :=
  EuclideanSpace ℝ (Fin n) × ℝ × Jet (EuclideanSpace ℝ (Fin n)) p

/-- The step of ARp at a state: a (classically chosen) global minimizer of the model (4.1.2),
which exists in finite dimension for `σ > 0`, `p ≥ 1` (`0` otherwise). -/
noncomputable def step (st : State n p) : EuclideanSpace ℝ (Fin n) :=
  if h : 0 < st.2.1 ∧ 1 ≤ p then
    Classical.choose (exists_isMinOn_regularizedModel (D := jetSeries st.2.2) h.1 h.2)
  else 0

theorem isMinOn_step {st : State n p} (hσ : 0 < st.2.1) (hp : 1 ≤ p) :
    IsMinOn (regularizedModel (jetSeries st.2.2) p st.2.1) univ (step st) := by
  rw [step, dite_eq_left ⟨hσ, hp⟩]
  exact (Classical.choose_spec
    (exists_isMinOn_regularizedModel (D := jetSeries st.2.2) hσ hp)).1

/-- The ratio (4.1.15) computed from the jet at the iterate and the answer `a` at the trial
point. -/
noncomputable def ratio (st : State n p) (a : Jet (EuclideanSpace ℝ (Fin n)) p) : ℝ :=
  (jetValue st.2.2 - jetValue a) / (jetSeries st.2.2).taylorDecrement p (step st)

open Classical in
/-- One iteration of ARp, given the answer `a` of the oracle at the trial point: nothing after
termination; otherwise the trial point and its jet are accepted with the same weight if
`ρ ≥ η₁`, and rejected with the weight multiplied by `γ₂` otherwise. -/
noncomputable def update (P : ARpParams) (ε : ℝ) (st : State n p)
    (a : Jet (EuclideanSpace ℝ (Fin n)) p) : State n p :=
  if jetTest ε st.2.2 then st
  else if P.η₁ ≤ ratio st a then (st.1 + step st, st.2.1, a) else (st.1, P.γ₂ * st.2.1, st.2.2)

open Classical in
/-- The next query of ARp at a state: the trial point `x_k + s_k`, or `x_k` after termination. -/
noncomputable def query (ε : ℝ) (st : State n p) : EuclideanSpace ℝ (Fin n) :=
  if jetTest ε st.2.2 then st.1 else st.1 + step st

/-- The states of ARp reconstructed from the sequence of answers `a`: `(0, σ₀, a₀)`, then
`update`. -/
noncomputable def states (P : ARpParams) (ε : ℝ) (a : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p) :
    ℕ → State n p
  | 0 => (0, P.σ₀, a 0)
  | k + 1 => update P ε (states P ε a k) (a (k + 1))

theorem states_congr (P : ARpParams) (ε : ℝ) {a a' : ℕ → Jet (EuclideanSpace ℝ (Fin n)) p} :
    ∀ k, (∀ i ≤ k, a i = a' i) → states P ε a k = states P ε a' k
  | 0, h => by simp [states, h 0 le_rfl]
  | k + 1, h => by
    simp only [states]
    rw [states_congr P ε k fun i hi => h i (hi.trans k.le_succ), h (k + 1) le_rfl]

end ARpOracle

open ARpOracle in
/-- **ARp as a deterministic `p`-th order method** ([cartis2022evaluation], (4.2.3) and
Theorem 4.2.6), first-order mode with tolerance `ε`: in every dimension, start at `x₀ = 0`;
the state `(x_k, σ_k, jet at x_k)` is reconstructed from the oracle answers by `states`; the
next query is the trial point `x_k + s_k`, `s_k` a (classically chosen) global minimizer of the
model (4.1.2); the trial point is accepted iff `ρ_k ≥ η₁` (4.1.15). Of the admissible updates
(4.1.16) the method takes `σ_{k+1} = σ_k` after a successful iteration and `σ_{k+1} = γ₂ σ_k` after
an unsuccessful one; once `‖∇f(x_k)‖ ≤ ε`, it repeats `x_k`. In the oracle model of §4.2 every
query returns the full jet `f, ∇f, …, ∇^p f` at the trial point (ARp itself needs the derivatives
only after successful iterations), so the method's iteration count `k` corresponds to `k + 1`
evaluations of `f`. -/
noncomputable def arpOracleMethod (P : ARpParams) (ε : ℝ) : JetMethod p := fun _ =>
  { x₀ := 0
    next := fun k b => query ε (states P ε (fun i => if h : i < k + 1 then b ⟨i, h⟩ else 0) k) }

theorem arpOracleMethod_mem (P : ARpParams) (ε : ℝ) :
    arpOracleMethod (p := p) P ε ∈ methodClassM p :=
  fun _ => rfl

namespace ARpOracle

variable (P : ARpParams) (ε : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)

/-- The answers of the jet oracle at the queries of `arpOracleMethod`. -/
noncomputable def answers (p : ℕ) (k : ℕ) : Jet (EuclideanSpace ℝ (Fin n)) p :=
  jetOracle f p ((arpOracleMethod (p := p) P ε).iter n f k)

theorem iter_succ (k : ℕ) :
    (arpOracleMethod (p := p) P ε).iter n f (k + 1) = query ε (states P ε (answers P ε f p) k) := by
  rw [JetMethod.iter_eq, OracleMethod.iterate_succ]
  exact congrArg (query ε) (states_congr P ε k fun i hi => by
    rw [dite_eq_left (Nat.lt_succ_of_le hi)]; rfl)

theorem iter_zero : (arpOracleMethod (p := p) P ε).iter n f 0 = 0 := rfl

variable {P ε f}

/-- The invariant of the reconstruction: the jet of the state is the oracle answer at the
iterate, the iterate is an earlier query, and the weight stays above `σ_min`. -/
theorem states_spec (k : ℕ) :
    (states P ε (answers P ε f p) k).2.2 = jetOracle f p (states P ε (answers P ε f p) k).1 ∧
      (∃ j ≤ k, (states P ε (answers P ε f p) k).1 = (arpOracleMethod (p := p) P ε).iter n f j) ∧
      P.σmin ≤ (states P ε (answers P ε f p) k).2.1 := by
  induction k with
  | zero => exact ⟨rfl, ⟨0, le_rfl, rfl⟩, P.σmin_le_σ₀⟩
  | succ k ih =>
    obtain ⟨hJ, ⟨j, hj, hx⟩, hσ⟩ := ih
    have hσ0 : 0 ≤ (states P ε (answers P ε f p) k).2.1 := P.σmin_nonneg.trans hσ
    have hq := iter_succ (p := p) P ε f k
    simp only [states, update]
    split_ifs with ht hs
    · exact ⟨hJ, ⟨j, hj.trans k.le_succ, hx⟩, hσ⟩
    · rw [query, ite_eq_right ht] at hq
      exact ⟨by rw [answers, hq], ⟨k + 1, le_rfl, hq.symm⟩, hσ⟩
    · exact ⟨hJ, ⟨j, hj.trans k.le_succ, hx⟩,
        hσ.trans (le_mul_of_one_le_left hσ0 P.toARParams.one_le_γ₂)⟩

/-- **The reconstructed sequences form an ARp run** ([cartis2022evaluation], (4.2.3)): for `f`
`C^p` (`p ≥ 1`) and `ε > 0`, the iterates `x_k`, steps `s_k` and weights `σ_k` reconstructed by
`arpOracleMethod` form a run of Algorithm 4.1.1 in first-order mode (`ε₂ = ε₃ = +∞`) from
`x₀ = 0`, whose queries are the trial points (`y_{k+1} = x_k + s_k` before termination) and whose
iterates are earlier queries (`x_k = y_j` for some `j ≤ k`). -/
theorem exists_run (hp : 1 ≤ p) (hε : 0 < ε) (hf : ContDiff ℝ p f) :
    ∃ x s σ, x 0 = 0 ∧ algorithm_4_1_1 f p P ε none none x s σ ∧
      (∀ k, ¬ arpTest f p P ε none none x s σ k →
        (arpOracleMethod (p := p) P ε).iter n f (k + 1) = x k + s k) ∧
      ∀ k, ∃ j ≤ k, x k = (arpOracleMethod (p := p) P ε).iter n f j := by
  set st := states P ε (answers P ε f p)
  set x : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (st k).1
  set s : ℕ → EuclideanSpace ℝ (Fin n) := fun k => step (st k)
  set σ : ℕ → ℝ := fun k => (st k).2.1
  have hspec := states_spec (P := P) (ε := ε) (f := f) (p := p)
  have hσpos : ∀ k, 0 < σ k := fun k => P.σmin_pos.trans_le (hspec k).2.2
  have htest : ∀ k, arpTest f p P ε none none x s σ k ↔ jetTest ε (st k).2.2 := fun k => by
    rw [arpTest, arpStopTest_none, (hspec k).1, jetTest_jetOracle hp]
  have hmin : ∀ k, IsMinOn (regularizedModel (ftaylorSeries ℝ f (x k)) p (σ k)) univ (s k) :=
    fun k => by
      have := isMinOn_step (st := st k) (hσpos k) hp
      rwa [(hspec k).1, regularizedModel_jetSeries_jetOracle] at this
  have hquery : ∀ k, ¬ arpTest f p P ε none none x s σ k →
      (arpOracleMethod (p := p) P ε).iter n f (k + 1) = x k + s k := fun k hk => by
    rw [iter_succ, query, ite_eq_right ((htest k).not.1 hk)]
  have hratio : ∀ k, ¬ arpTest f p P ε none none x s σ k →
      ratio (st k) (answers P ε f p (k + 1)) = taylorRatio f p x s k := fun k hk => by
    rw [ratio, taylorRatio_def, reductionRatio, (hspec k).1, jetValue_jetOracle, answers,
      jetValue_jetOracle, hquery k hk, taylorDecrement_jetSeries_jetOracle]
  refine ⟨x, s, σ, rfl, ⟨hp, by simpa using hp, hε, by simp, by simp, fun _ => rfl, ?_⟩,
    hquery, fun k => (hspec k).2.1⟩
  refine ⟨rfl, fun k _ hk => ?_, fun k hk => ?_⟩
  · -- Step 2: the global model minimizer
    have hg : ε < ‖fderiv ℝ f (x k)‖ := by
      rw [← norm_gradient_eq]; simpa using hk
    have hdec := regularizedModel_lt_of_isMinOn_of_fderiv_ne_zero (hmin k) (by
      rw [fderiv_regularizedModel_ftaylorSeries_zero hf.contDiffAt hp]
      intro h0; rw [h0, norm_zero] at hg; linarith)
    exact isARpStep_of_isMinOn P.toARpParams (fun h => absurd h (by simp)) (hmin k) hdec
      (fun h => absurd h (by simp))
  · -- Steps 3–4
    have hk' : ¬ arpTest f p P ε none none x s σ k := fun h => hk k le_rfl (Or.inl h)
    have hst : st (k + 1) = update P ε (st k) (answers P ε f p (k + 1)) := rfl
    have hσ0 := (hσpos k).le
    have hσm := (hspec k).2.2
    change ARAcceptance P.toARParams (taylorRatio f p x s k) (x k) (s k) (st (k + 1)).1 (σ k)
      (st (k + 1)).2.1
    rw [hst, update, ite_eq_right ((htest k).not.1 hk'), hratio k hk']
    by_cases hs : P.η₁ ≤ taylorRatio f p x s k
    · rw [ite_eq_left hs]
      refine ⟨by rw [ite_eq_left hs], ⟨fun _ => ⟨max_le hσm (mul_le_of_le_one_left hσ0
        P.toARParams.γ₁_le_one), le_rfl⟩, fun _ _ => ⟨le_rfl, le_mul_of_one_le_left hσ0
        P.toARParams.one_le_γ₂⟩, fun h => absurd hs (not_le.2 h)⟩⟩
    · rw [ite_eq_right hs]
      refine ⟨by rw [ite_eq_right hs], ⟨fun h => absurd (P.η₁_le_η₂.trans h) hs,
        fun h => absurd h hs, fun _ => ⟨le_rfl, mul_le_mul_of_nonneg_right P.γ₂_le_γ₃ hσ0⟩⟩⟩

end ARpOracle

/-- For `f` satisfying f.Bb and f.DpL, the first `ε`-stationary query of `arpOracleMethod` on `f`
has index at most some `k` (the termination index of the reconstructed ARp run, every accepted
iterate being an earlier query) with `k + 1 ≤ κ^A (f(0) - f_low)/ε^{(p+1)/p} + κ^C`
(Theorem 4.1.5 (i)). -/
theorem firstStationaryIndex_arpOracleMethod_le {p : ℕ} (hp : 1 ≤ p) (P : ARpParams) {ε L flow : ℝ}
    (hε : 0 < ε) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hb : Chapter02.AssumptionBb f flow)
    (hf : AssumptionDpL f p L) :
    ∃ k : ℕ, firstStationaryIndex ((arpOracleMethod (p := p) P ε).iter n f) f ε ≤ k ∧
      (k + 1 : ℝ) ≤ kappaSARp P p L 1 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
        (f 0 - flow) / ε ^ (((p : ℝ) + 1) / p) + kappaCARp P L := by
  obtain ⟨x, s, σ, hx0, hrun, -, hmem⟩ := ARpOracle.exists_run (P := P) hp hε hf.contDiff
  obtain ⟨kε, hk, hF, -⟩ := theorem_4_1_5_i hb hf hrun
  obtain ⟨j, hj, hxj⟩ := hmem kε
  refine ⟨kε, (firstStationaryIndex_le (k := j) ?_).trans (by exact_mod_cast hj), ?_⟩
  · rw [← hxj, ← norm_gradient_eq]; exact hk.test
  · rw [funEvalCount_eq, hx0] at hF; exact_mod_cast hF

/-- The bound `κ^A Δ/ε^{(p+1)/p} + κ^C` of (4.2.3), with the constants of Theorem 4.1.5 (i) for
`L_{f,p} = max(1, L)`. -/
noncomputable def arpComplexityBound (P : ARpParams) (p : ℕ) (Δ L ε : ℝ) : ℝ :=
  kappaSARp P p (max 1 L) 1 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) * Δ /
    ε ^ (((p : ℝ) + 1) / p) + kappaCARp P (max 1 L)

/-- The worst case `sup_{f ∈ 𝓕(Δ, p)} k_ε(ARp, f)` of ARp (`arpOracleMethod`) on the class
`𝓕(Δ, p)`. -/
noncomputable def arpWorstCase (P : ARpParams) (p : ℕ) (Δ L ε : ℝ) : ℕ∞ :=
  ⨆ F ∈ functionClass Δ L p,
    firstStationaryIndex ((arpOracleMethod (p := p) P ε).iter F.1 F.2) F.2 ε

/-- **ARp attains the upper bound (4.2.3)** ([cartis2022evaluation], §4.2.3): for `p ≥ 1` and
`ε > 0`, ARp (`arpOracleMethod`, a method of `𝓜(p)`) finds an `ε`-stationary point of every
`f ∈ 𝓕(Δ, p)` within the first `⌊κ^A Δ ε^{-(p+1)/p} + κ^C⌋` queries (constants of Theorem 4.1.5 (i)
with `L_{f,p} = max(1, L)`; uniform in the dimension). -/
theorem arpWorstCase_le_arpComplexityBound {p : ℕ} (hp : 1 ≤ p) (P : ARpParams) {Δ L ε : ℝ}
    (hε : 0 < ε) : arpWorstCase P p Δ L ε ≤ ((⌊arpComplexityBound P p Δ L ε⌋₊ : ℕ) : ℕ∞) := by
  refine iSup₂_le fun F hF => ?_
  obtain ⟨hc, hlip, hbdd, hΔ⟩ := mem_functionClass.1 hF
  have hb : Chapter02.AssumptionBb F.2 (⨅ y, F.2 y) := fun y => ciInf_le hbdd y
  have hf : AssumptionDpL F.2 p (max 1 L) :=
    assumptionDpL_iff.2 ⟨hc.of_le (by exact_mod_cast le_top), le_max_left _ _,
      iteratedFDerivLipschitzOn_iff.2 fun x hx y hy =>
        (iteratedFDerivLipschitzOn_iff.1 hlip x hx y hy).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩
  obtain ⟨k, hk, hkB⟩ := firstStationaryIndex_arpOracleMethod_le hp P hε hb hf
  refine hk.trans (Nat.cast_le.2 (Nat.le_floor ?_))
  have hκ := kappaSARp_pos (P := P) (p := p) (L := max 1 L) (by positivity) 1
  have hlog : 0 ≤ 1 + |Real.log P.γ₁| / Real.log P.γ₂ := by
    have := P.toARParams.log_γ₂_pos; positivity
  have hE : 0 < ε ^ (((p : ℝ) + 1) / p) := Real.rpow_pos_of_pos hε _
  have : kappaSARp P p (max 1 L) 1 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) *
      (F.2 0 - ⨅ y, F.2 y) /
      ε ^ (((p : ℝ) + 1) / p) ≤ kappaSARp P p (max 1 L) 1 *
        (1 + |Real.log P.γ₁| / Real.log P.γ₂) * Δ / ε ^ (((p : ℝ) + 1) / p) := by
    gcongr
  rw [arpComplexityBound]
  linarith

/-- The complexity of `𝓜(p)` on `𝓕(Δ, p)` is at most ARp's worst case. -/
theorem complexity_le_arpWorstCase (P : ARpParams) {p : ℕ} (Δ L ε : ℝ) :
    complexity (methodClassM p) (functionClass Δ L p) ε ≤ arpWorstCase P p Δ L ε :=
  iInf₂_le (f := fun M (_ : M ∈ methodClassM p) =>
    ⨆ F ∈ functionClass Δ L p, firstStationaryIndex (M.iter F.1 F.2) F.2 ε)
    (arpOracleMethod P ε) (arpOracleMethod_mem P ε)

/-- **The upper bound (4.2.3)** ([cartis2022evaluation], §4.2.3):
`#_ε(𝓜(p), 𝓕(Δ, p)) ≤ ⌊κ^A Δ ε^{-(p+1)/p} + κ^C⌋`, attained by ARp. -/
theorem complexity_le_arpComplexityBound {p : ℕ} (hp : 1 ≤ p) (P : ARpParams) {Δ L ε : ℝ}
    (hε : 0 < ε) :
    complexity (methodClassM p) (functionClass Δ L p) ε ≤
      ((⌊arpComplexityBound P p Δ L ε⌋₊ : ℕ) : ℕ∞) :=
  (complexity_le_arpWorstCase P Δ L ε).trans (arpWorstCase_le_arpComplexityBound hp P hε)

/-- **Theorem 4.2.6, tightness** of [cartis2022evaluation] ("the bound (4.2.3) is tight, and ARp
has the optimal order of evaluation complexity for methods in `𝓜(p)`"). For `p ≥ 1`, ARp
constants `P` and `Δ, L > 0`: (a) ARp's own worst case on `𝓕(Δ, p)`, hence the complexity of
`𝓜(p)`, is at most `⌊κ^A Δ ε^{-(p+1)/p} + κ^C⌋` (4.2.3) for every `ε > 0`; (b) together with the
lower bound of Theorem 4.2.6 (i), there are `c, C > 0` and `ε₀ > 0` with
`c ε^{-(p+1)/p} ≤ #_ε(𝓜(p), 𝓕(Δ, p)) ≤ sup_f k_ε(ARp, f) ≤ C ε^{-(p+1)/p}` for all
`ε ∈ (0, ε₀]` (compared in `ℝ≥0∞`): ARp has the optimal order. Only the order in `ε` is tight:
the upper bound grows like `Δ L^{(p+1)/p}` and the lower bound like `Δ L^{1/p}`. -/
theorem theorem_4_2_6_ii {p : ℕ} (hp : 1 ≤ p) (P : ARpParams) {Δ L : ℝ} (hΔ : 0 < Δ)
    (hL : 0 < L) :
    (∀ ε, 0 < ε → arpWorstCase P p Δ L ε ≤ ((⌊arpComplexityBound P p Δ L ε⌋₊ : ℕ) : ℕ∞) ∧
      complexity (methodClassM p) (functionClass Δ L p) ε ≤
        ((⌊arpComplexityBound P p Δ L ε⌋₊ : ℕ) : ℕ∞)) ∧
    ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ENNReal.ofReal (c * ε ^ (-((p + 1 : ℝ) / p))) ≤
          (complexity (methodClassM p) (functionClass Δ L p) ε : ENNReal) ∧
        complexity (methodClassM p) (functionClass Δ L p) ε ≤ arpWorstCase P p Δ L ε ∧
        (arpWorstCase P p Δ L ε : ENNReal) ≤ ENNReal.ofReal (C * ε ^ (-((p + 1 : ℝ) / p))) := by
  refine ⟨fun ε hε => ⟨arpWorstCase_le_arpComplexityBound hp P hε,
    complexity_le_arpComplexityBound hp P hε⟩, ?_⟩
  set a : ℝ := (p + 1 : ℝ) / p
  have ha : 0 < a := by positivity
  set K := Δ * (L / CarmonChain.lipschitzConst p) ^ (1 / p : ℝ)
  have hK : 0 < K := by
    have := CarmonChain.lipschitzConst_pos p
    positivity
  have hκA : 0 ≤ kappaSARp P p (max 1 L) 1 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) := by
    have := kappaSARp_pos (P := P) (p := p) (L := max 1 L) (by positivity) 1
    have := P.toARParams.log_γ₂_pos
    positivity
  have hκC := two_le_kappaCARp (P := P) (max 1 L)
  set ε₀ := min 1 ((K / 12) ^ (1 / a))
  have hε₀ : 0 < ε₀ := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨1 / 24 * K, kappaSARp P p (max 1 L) 1 * (1 + |Real.log P.γ₁| / Real.log P.γ₂) * Δ +
    kappaCARp P (max 1 L), ε₀, by positivity, by positivity, hε₀,
    fun ε hε hεε₀ => ⟨?_, complexity_le_arpWorstCase P Δ L ε, ?_⟩⟩
  · -- the lower bound of Theorem 4.2.6 (i)
    have hY : 12 ≤ K * ε ^ (-a) := by
      have h1 : ((K / 12) ^ (1 / a)) ^ (-a) ≤ ε ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos hε (hεε₀.trans (min_le_right _ _)) (by linarith)
      rw [← Real.rpow_mul (by positivity), show 1 / a * -a = -1 by field_simp, Real.rpow_neg_one,
        inv_div] at h1
      have := mul_le_mul_of_nonneg_left h1 hK.le
      rwa [mul_div_cancel₀ _ hK.ne'] at this
    have := (theorem_4_2_6_i hp hΔ hL hε).2.2.2 (by simpa only [K, mul_assoc] using hY)
    simpa only [K, mul_assoc] using this.2
  · -- the upper bound (4.2.3)
    refine (ENat.toENNReal_le.2 (arpWorstCase_le_arpComplexityBound hp P hε)).trans ?_
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ((Nat.floor_le (by
      rw [arpComplexityBound]; have := Real.rpow_pos_of_pos hε a; positivity)).trans ?_)
    have hε1 : 1 ≤ ε ^ (-a) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε (hεε₀.trans (min_le_left _ _))
        (by linarith)
    rw [arpComplexityBound, div_eq_mul_inv, ← Real.rpow_neg hε.le]
    nlinarith [mul_nonneg hκA hΔ.le]

end CartisGouldToint.Chapter04
