import Mathlib.Basic.Real.ENatENNReal
import Numlib.Optimization.Complexity.CarmonChain

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
  `∇^p f` explicit.
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
* `lemma_4_2_5_i` – `lemma_4_2_5_iv` — properties of the difficult function.
* `theorem_4_2_6_i` — the lower bound (4.2.7).

## Deviations from the book

* **(4.2.6)**: the first term of `f^D` is `-Ψ(1) Φ([x]_1)` (as in Carmon et al.), not the printed
  `-Ψ([x]_1) Φ([x]_1)`, with which `∇f^D(0) = 0` and Lemma 4.2.5 (ii) fails at `x = 0`.
* **Theorem 4.2.6**: with `k̄ = ⌊Δ/12 (L/L^D_p)^{1/p} ε^{-(p+1)/p}⌋`, the proof gives `#_ε ≥ k̄` for
  both classes; the book's `#_ε(𝓜(p), 𝓕(Δ, p)) ≥ 2 k̄` does not follow from Theorem 4.2.4. The
  form `c₀ Δ (L/L^D_p)^{1/p} ε^{-(p+1)/p}` (with `c₀ = 1/24`) needs that quantity to be at least
  `12`, i.e. `ε` small enough: for large `ε` the complexity is `0`.
* Lemma 4.2.5 (iv) is proved with an explicit constant `L^D_p` independent of `k̄`; the growth
  bound `L^D_p ≤ exp(5/2 p log p + c₁ p)` is not formalized, and neither is the tightness claim of
  Theorem 4.2.6 (it needs the ARp complexity of §4.1 phrased as a method of `𝓜(p)`).
* Members of `𝓕(Δ, p)` are assumed `C^∞` (footnote 29), and Theorem 4.2.4 and the orthogonal
  invariance of `𝓕(Δ, p)` (footnote 30) assume `L ≥ 0`. A zero-respecting method is required to
  keep `[x_{k+1}]_j = 0` when `e_j` is a null direction of all `∇^q f(x_i)` (the multilinear map
  vanishes whenever one argument is `e_j`); for the symmetric derivatives of `C^p` functions this
  is the book's `∇^q f(x_i) e_j = 0`.
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

end CartisGouldToint.Chapter04
