/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.SobolevDensity`, beside
`Mathlib.Analysis.Distribution.Sobolev` and `Mathlib.Analysis.Distribution.Mollification`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Numlib.Analysis.Sobolev.Domain
import Numlib.Analysis.Sobolev.Mollification

/-!
# Density of smooth functions in Sobolev spaces

Two density theorems, both for `1 ≤ p < ∞`.

On the **whole space**, mollification smooths a function at no cost in position — there is no
boundary to keep away from — so a single mollification approximates a function of `W^{k,p}(ℝ^d)`
together with all its weak derivatives of order at most `k`. Cutting the result off outside a
large ball costs, by the Leibniz bound, only a constant times the `L^p` mass of the derivatives
far from the origin, which tends to `0`. That is the density of `C_0^∞(ℝ^d)` in `W^{k,p}(ℝ^d)`.

On an **arbitrary open set** `Ω` a fixed mollification radius is unavailable near the boundary,
and the classical remedy is to exhaust `Ω` by relatively compact opens, to take a smooth partition
of unity subordinate to the exhaustion, and to mollify each piece at its own radius. The sum of
the pieces is smooth on `Ω` because the partition of unity is locally finite, and it approximates
`f` because each piece does. That is the theorem of Meyers and Serrin, `H = W`.

For the classical statements see N. G. Meyers and J. Serrin, *H = W*, Proceedings of the National
Academy of Sciences of the United States of America **51** (1964), 1055–1056; R. A. Adams and
J. J. F. Fournier, *Sobolev Spaces*, 2nd edition, Academic Press, 2003, Theorems 3.17 and 3.22; or
H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
2011, §9.1. They are Theorems 7.3.1 and 7.3.4 of Kendall Atkinson and Weimin Han, *Theoretical
Numerical Analysis: A Functional Analysis Framework*, 3rd edition, Springer, 2009.

## Main results

* `sobolevNorm_le_of_forall_eLpNorm_le` and `eLpNorm_weakIteratedFDeriv_le_sobolevNorm`: the
  Sobolev norm is bounded by, and bounds, the `L^p(Ω)` norms of the weak derivatives of the orders
  `n ≤ k`, up to the factor `k + 1`.
* `MemSobolev.tendsto_sobolevNorm_convolution_sub`: **mollification approximates in
  `W^{k,p}(ℝ^d)`**, the mollifications of `f` converging to `f` in the Sobolev norm of the whole
  space as the radii tend to `0`.
* `MeasureTheory.MemLp.tendsto_eLpNorm_indicator_compl_ball`: the `L^p` mass of a function outside
  a large ball tends to `0`.
* `exists_seq_contDiff_hasCompactSupport_tendsto_sobolevNorm_sub`: **truncation approximates in
  `W^{k,p}(ℝ^d)`**, for a function all of whose classical derivatives of order at most `k` lie in
  `L^p`.
* `MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm`: **`C_0^∞(ℝ^d)` is dense in
  `W^{k,p}(ℝ^d)`**.
* `hasWeakIteratedFDerivOn_of_tendsto_eLpNorm_one`: **the weak derivative is closed under `L^1`
  limits**.
* `MemSobolev.exists_seq_contDiff_tendsto_eLpNorm`: **local approximation in `W^{k,p}(Ω)`**, at
  all orders at once, on a relatively compact open subset of `Ω`.
* `TopologicalSpace.Opens.exists_partitionOfUnity`: **a smooth partition of unity subordinate to
  an exhaustion** of an open set, telescoping and locally finite in a strong sense.
* `eLpNorm_iteratedFDeriv_smul_sub_le` and `eLpNorm_iteratedFDeriv_sub_patch_le`: the `L^p`
  Leibniz estimate for one piece, and the patching estimate that adds the pieces up.
* `MemSobolev.exists_seq_contDiffOn_tendsto_sobolevNorm`: **the Meyers–Serrin theorem `H = W`**,
  that `C^∞(Ω) ∩ W^{k,p}(Ω)` is dense in `W^{k,p}(Ω)` for any open `Ω`.

## Implementation notes

**No Leibniz rule for weak derivatives is needed anywhere**, in either theorem, and that is what
keeps the development to one file. The received account of Meyers–Serrin has one prove
`ψ_j f ∈ W^{k,p}(Ω)` for each member `ψ_j` of the partition of unity, which is the order-`n`
product rule for a weak derivative against a smooth factor and is genuinely hard. It is avoided
here by comparing the patched function `v = ∑_j ψ_j g_j` not with `f` but with a *single* smooth
approximation `G` of `f` on a relatively compact open set: since the `ψ_j` sum to `1` there,

`∂^n v - ∂^n G = ∑_j ∂^n (ψ_j (g_j - G))`

is an identity between classical derivatives of smooth functions, and only the Leibniz *bound*
`norm_iteratedFDeriv_smul_le` is used to estimate it. Letting `G` run through a sequence
approximating `f` gives the theorem. The same device settles the whole-space theorem, where the
two approximation steps are taken in the order mollify-then-truncate so that the function being
truncated is already smooth.

The cut-off of the whole-space theorem is `x ↦ η (R⁻¹ • x)` for one fixed `η` that is `1` on the
closed unit ball and supported in the ball of radius `2`. Its derivatives are bounded uniformly in
`R ≥ 1` by `iteratedFDeriv_comp_const_smul`, which contributes a factor `R ^ (-i)`; the point of
fixing `η` once and scaling it, rather than taking a family of bumps of growing radius, is exactly
that this factor stays visible.

The partition of unity is the telescoping one, `ψ_j = χ_j - χ_{j-1}` for smooth Urysohn functions
`χ_j` attached to an exhaustion `U 0 ⊆ U 1 ⊆ …`. Its local finiteness comes in the strongest
possible form — on `U N` every `ψ_j` with `j > N` vanishes *identically*, and `ψ_0, …, ψ_N` already
sum to `1` — so the patched function is a *finite* sum on each `U N` and no theory of locally
finite sums is needed: a `tsum` that is finitely supported at each point, and
`Filter.EventuallyEq.iteratedFDeriv`, do everything.

`MeasureTheory.eLpNorm_add_le_of_norm`, `MeasureTheory.eLpNorm_sum_le_of_norm` and
`MeasureTheory.MemLp.add_of_norm` are Mathlib lemmas restated for a `NormedAddCommGroup`. Mathlib
states them over an `ESeminormedAddMonoid`, and resolving that class for `E [×n]→L[ℝ] F` with `n`
a variable costs more than the whole default heartbeat budget; restating them once with the group
abstract makes every use in this file cheap. Anyone extending this file should reach for the
restatements rather than the originals.
-/

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal Topology

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} {n k : ℕ} {p : ℝ≥0∞} {f : E → F}

/-! ### The Sobolev norm through a chosen family of weak derivatives -/

section Norm

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]

/-- The `L^p(Ω)` norm of the chosen weak derivative of order `n` of `f` is the `L^p(Ω)` norm of
any weak derivative of order `n` of `f`. -/
theorem HasWeakIteratedFDerivOn.eLpNorm_weakIteratedFDeriv {w : E → E [×n]→L[ℝ] F}
    (h : HasWeakIteratedFDerivOn n f w Ω μ) :
    eLpNorm (weakIteratedFDeriv n f Ω μ) p (μ.restrict (Ω : Set E))
      = eLpNorm w p (μ.restrict (Ω : Set E)) :=
  eLpNorm_congr_ae <| (ae_restrict_iff' Ω.isOpen.measurableSet).2 h.weakIteratedFDeriv_ae_eq

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- The chosen weak derivative of order `n ≤ k` of a function of `W^{k,p}(Ω)` is one. -/
theorem MemSobolev.hasWeakIteratedFDerivOn (h : MemSobolev f k p Ω μ) (hn : n ≤ k) :
    HasWeakIteratedFDerivOn n f (weakIteratedFDeriv n f Ω μ) Ω μ := by
  obtain ⟨w, hw, -⟩ := h.exists_hasWeakIteratedFDerivOn (n := n) (Nat.cast_le.2 hn)
  exact hw.hasWeakIteratedFDerivOn_weakIteratedFDeriv

/-- The chosen weak derivative of order `n ≤ k` of a function of `W^{k,p}(Ω)` lies in
`L^p(Ω)`. -/
theorem MemSobolev.memLp_weakIteratedFDeriv (h : MemSobolev f k p Ω μ) (hn : n ≤ k) :
    MemLp (weakIteratedFDeriv n f Ω μ) p (μ.restrict (Ω : Set E)) := by
  obtain ⟨w, hw, hwp⟩ := h.exists_hasWeakIteratedFDerivOn (n := n) (Nat.cast_le.2 hn)
  have hae : weakIteratedFDeriv n f Ω μ =ᵐ[μ.restrict (Ω : Set E)] w :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).2 hw.weakIteratedFDeriv_ae_eq
  exact hwp.ae_eq hae.symm

end Norm

/-- A bound on the `L^p(Ω)` norms of the chosen weak derivatives of all orders `n ≤ k` bounds the
Sobolev norm, at the cost of the factor `k + 1`: the norm is an `ℓ^p` sum of `k + 1` terms, and
`(k + 1) ^ (1 / p) ≤ k + 1`. -/
theorem sobolevNorm_le_of_forall_eLpNorm_le (hp : 1 ≤ p) (hp' : p ≠ ⊤) {c : ℝ≥0∞}
    (h : ∀ n ≤ k, eLpNorm (weakIteratedFDeriv n f Ω μ) p (μ.restrict (Ω : Set E)) ≤ c) :
    sobolevNorm f k p Ω μ ≤ (k + 1) * c := by
  have hp₀ : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp'
  simp only [sobolevNorm, hp', ↓reduceIte]
  calc (∑ i : Fin (k + 1), eLpNorm (weakIteratedFDeriv i f Ω μ) p (μ.restrict (Ω : Set E))
          ^ p.toReal) ^ (1 / p.toReal)
      ≤ (∑ _i : Fin (k + 1), c ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr with i _
        exact h i (Nat.lt_succ_iff.1 i.2)
    _ = ((k + 1 : ℝ≥0∞) * c ^ p.toReal) ^ (1 / p.toReal) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_cast
    _ = (k + 1 : ℝ≥0∞) ^ (1 / p.toReal) * c := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hP.ne', ENNReal.rpow_one]
    _ ≤ (k + 1 : ℝ≥0∞) * c := by
        have hle : (k + 1 : ℝ≥0∞) ^ (1 / p.toReal) ≤ (k + 1 : ℝ≥0∞) := by
          nth_rewrite 2 [← ENNReal.rpow_one (k + 1 : ℝ≥0∞)]
          refine ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          rw [div_le_one hP, ← ENNReal.toReal_one]
          exact ENNReal.toReal_mono hp' hp
        exact mul_le_mul' hle le_rfl

/-! ### Elementary tools

A dyadic budget, a uniform bound on the derivatives of a smooth compactly supported function, the
crude form of the Leibniz bound that both density theorems use, and three Mathlib lemmas restated
for a normed group to keep the instance search cheap (see the implementation notes). -/

section Tools

omit [MeasurableSpace E] [NormedSpace ℝ F] in
/-- A dyadic budget: the partial sums of `a / 2 ^ (j + 1)` never exceed `a`. -/
theorem ENNReal.sum_range_div_two_pow_succ_add (a : ℝ≥0∞) (M : ℕ) :
    (∑ j ∈ Finset.range M, a / 2 ^ (j + 1)) + a / 2 ^ M = a := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hhalf : a / 2 ^ (M + 1) = a / 2 ^ M / 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, pow_succ, mul_assoc,
        ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (ENNReal.pow_ne_top (by simp)))]
    rw [Finset.sum_range_succ, add_assoc, hhalf, ENNReal.add_halves, ih]

omit [MeasurableSpace E] [NormedSpace ℝ F] in
/-- The partial sums of the dyadic budget are bounded by `a`. -/
theorem ENNReal.sum_range_div_two_pow_succ_le (a : ℝ≥0∞) (M : ℕ) :
    (∑ j ∈ Finset.range M, a / 2 ^ (j + 1)) ≤ a :=
  le_self_add.trans (le_of_eq (ENNReal.sum_range_div_two_pow_succ_add a M))

omit [MeasurableSpace E] in
/-- A uniform bound on the derivatives of order at most `k` of a smooth compactly supported
function. -/
theorem exists_bound_norm_iteratedFDeriv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r ≤ k, ∀ x, ‖iteratedFDeriv ℝ r ψ x‖ ≤ M := by
  have h : ∀ r : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖iteratedFDeriv ℝ r ψ x‖ ≤ M := fun r ↦ by
    obtain ⟨M, hM⟩ := (hψc.iteratedFDeriv r).exists_bound_of_continuous
      (hψ.continuous_iteratedFDeriv (by simp))
    exact ⟨max M 0, le_max_right _ _, fun x ↦ (hM x).trans (le_max_left _ _)⟩
  choose M hM0 hM using h
  refine ⟨∑ r ∈ Finset.range (k + 1), M r, Finset.sum_nonneg fun r _ ↦ hM0 r, fun r hr x ↦ ?_⟩
  exact (hM r x).trans (Finset.single_le_sum (f := M) (fun i _ ↦ hM0 i)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hr)))

omit [MeasurableSpace E] in
/-- **The Leibniz bound in a crude uniform form.** If every derivative of order at most `k` of the
smooth scalar `ψ` is bounded by `M`, then for `h` smooth and `m ≤ k` the derivative of order `m` of
`ψ h` is bounded by `(k + 1) 2^k M` times the sum of the derivatives of `h` of order at most `k`.

The point of the crude form is that the constant does not depend on `m` or on `h`. -/
theorem norm_iteratedFDeriv_smul_le_const_mul_sum {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) {h : E → F}
    (hh : ContDiff ℝ ∞ h) {M : ℝ} (hM : ∀ r ≤ k, ∀ x, ‖iteratedFDeriv ℝ r ψ x‖ ≤ M) {m : ℕ}
    (hm : m ≤ k) (x : E) :
    ‖iteratedFDeriv ℝ m (fun y ↦ ψ y • h y) x‖
      ≤ ((k + 1) * 2 ^ k * M) * ∑ s ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ s h x‖ := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (Nat.zero_le k) x)
  set H : ℝ := ∑ s ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ s h x‖ with hHdef
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hHle : ∀ s ≤ k, ‖iteratedFDeriv ℝ s h x‖ ≤ H := fun s hs ↦
    Finset.single_le_sum (f := fun s ↦ ‖iteratedFDeriv ℝ s h x‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hs))
  refine (norm_iteratedFDeriv_smul_le hψ hh x (n := m) (by simp)).trans ?_
  calc ∑ r ∈ Finset.range (m + 1), (m.choose r : ℝ) * ‖iteratedFDeriv ℝ r ψ x‖
          * ‖iteratedFDeriv ℝ (m - r) h x‖
      ≤ ∑ _r ∈ Finset.range (m + 1), 2 ^ k * M * H := by
        refine Finset.sum_le_sum fun r hr ↦ ?_
        have hrm : r ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
        have hchoose : (m.choose r : ℝ) ≤ 2 ^ k := by
          have h1 : m.choose r ≤ 2 ^ m := by
            rw [← Nat.sum_range_choose m]
            exact Finset.single_le_sum (f := fun i ↦ m.choose i) (fun _ _ ↦ Nat.zero_le _) hr
          have h2 : (2 : ℕ) ^ m ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hm
          exact_mod_cast h1.trans h2
        exact mul_le_mul (mul_le_mul hchoose (hM r (hrm.trans hm) x) (norm_nonneg _)
          (by positivity)) (hHle (m - r) ((Nat.sub_le m r).trans hm)) (norm_nonneg _)
          (mul_nonneg (by positivity) hM0)
    _ = ((m : ℝ) + 1) * (2 ^ k * M * H) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ((k : ℝ) + 1) * (2 ^ k * M * H) := by
        have hmk : ((m : ℝ) + 1) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hm
        exact mul_le_mul_of_nonneg_right hmk (by positivity)
    _ = ((k + 1) * 2 ^ k * M) * H := by ring

omit [MeasurableSpace E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Minkowski's inequality for a normed group, stated so that the instance search does not go
through `ESeminormedAddMonoid`. Mathlib's `MeasureTheory.eLpNorm_add_le` is stated over an
`ESeminormedAddMonoid`, and resolving that class for a `ContinuousMultilinearMap` type whose arity
is a variable costs more than the default heartbeat budget; specializing once, with the group
abstract, makes every later use cheap. -/
theorem MeasureTheory.eLpNorm_add_le_of_norm {X G : Type*} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup G] {a b : X → G} (ha : AEStronglyMeasurable a ν)
    (hb : AEStronglyMeasurable b ν) (hp : 1 ≤ p) :
    eLpNorm (a + b) p ν ≤ eLpNorm a p ν + eLpNorm b p ν :=
  eLpNorm_add_le ha hb hp

omit [MeasurableSpace E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Minkowski's inequality for a finite sum in a normed group, stated so that the instance search
does not go through `ESeminormedAddCommMonoid`; see
`MeasureTheory.eLpNorm_add_le_of_norm`. -/
theorem MeasureTheory.eLpNorm_sum_le_of_norm {X G ι : Type*} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup G] {a : ι → X → G} {s : Finset ι}
    (ha : ∀ i ∈ s, AEStronglyMeasurable (a i) ν) (hp : 1 ≤ p) :
    eLpNorm (∑ i ∈ s, a i) p ν ≤ ∑ i ∈ s, eLpNorm (a i) p ν :=
  eLpNorm_sum_le ha hp

omit [MeasurableSpace E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- `L^p` membership is closed under addition, stated for a normed group so that the instance
search does not go through the `ENorm` hierarchy; see
`MeasureTheory.eLpNorm_add_le_of_norm`. -/
theorem MeasureTheory.MemLp.add_of_norm {X G : Type*} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup G] {a b : X → G} (ha : MemLp a p ν) (hb : MemLp b p ν) :
    MemLp (a + b) p ν :=
  ha.add hb

end Tools

/-! ### Mollification on the whole space

On the whole space every mollification is available at every point, so the commutation of the weak
derivative with mollification holds everywhere and the mollifications of a function of
`W^{k,p}(ℝ^d)` converge to it in the Sobolev norm. -/

section Mollify

open ContinuousLinearMap

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [BorelSpace E]
  [CompleteSpace F] in
/-- The measure restricted to the whole space, read as the top open set, is the measure. -/
theorem MeasureTheory.Measure.restrict_coe_top (μ : Measure E) :
    μ.restrict ((⊤ : Opens E) : Set E) = μ := by
  simp

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- A function of `W^{k,p}(ℝ^d)` lies in `L^p` of the whole space. -/
theorem MemSobolev.memLp_top (h : MemSobolev f k p ⊤ μ) : MemLp f p μ := by
  simpa [Measure.restrict_coe_top] using h.memLp

omit [CompleteSpace F] in
/-- The mollification of a function that is locally integrable on the whole space is smooth. -/
theorem MeasureTheory.LocallyIntegrable.contDiff_convolution_normed
    (hf : LocallyIntegrable f μ) (φ : ContDiffBump (0 : E)) :
    ContDiff ℝ ∞ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hf

omit [CompleteSpace F] in
/-- **The weak derivative commutes with mollification on the whole space**: the classical
derivative of order `n ≤ k` of the mollification of `f ∈ W^{k,p}(ℝ^d)` is the mollification of the
weak derivative of order `n` of `f`, at every point. -/
theorem MemSobolev.iteratedFDeriv_convolution_normed (hf : MemSobolev f k p ⊤ μ)
    (φ : ContDiffBump (0 : E)) (hn : n ≤ k) (x : E) :
    iteratedFDeriv ℝ n (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x
      = (φ.normed μ ⋆[lsmul ℝ ℝ, μ] weakIteratedFDeriv n f ⊤ μ) x :=
  (hf.hasWeakIteratedFDerivOn hn).iteratedFDeriv_convolution φ.contDiff_normed
    (le_of_eq (φ.tsupport_normed_eq (μ := μ))) (by simp)

/-- The mollification of a function of `W^{k,p}(ℝ^d)` lies in `W^{k,p}(ℝ^d)` and is smooth. -/
theorem MemSobolev.convolution_normed (hf : MemSobolev f k p ⊤ μ) (hp : 1 ≤ p)
    (φ : ContDiffBump (0 : E)) : MemSobolev (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) k p ⊤ μ := by
  have hloc : LocallyIntegrable f μ := hf.memLp_top.locallyIntegrable hp
  have hsm : ContDiff ℝ ∞ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) := hloc.contDiff_convolution_normed φ
  have hφ1 : MemLp (φ.normed μ) 1 μ := memLp_one_iff_integrable.2 φ.integrable_normed
  refine ⟨by simpa [Measure.restrict_coe_top] using MemLp.convolution hp hφ1 hf.memLp_top,
    fun m hm ↦ ⟨iteratedFDeriv ℝ m (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f),
      ContDiffOn.hasWeakIteratedFDerivOn hsm.contDiffOn (by simp), ?_⟩⟩
  have hm' : m ≤ k := Nat.cast_le.1 hm
  have hwp : MemLp (weakIteratedFDeriv m f ⊤ μ) p μ := by
    simpa [Measure.restrict_coe_top] using hf.memLp_weakIteratedFDeriv hm'
  refine MemLp.ae_eq (Filter.Eventually.of_forall fun x ↦
    (hf.iteratedFDeriv_convolution_normed φ hm' x).symm) ?_
  simpa [Measure.restrict_coe_top] using MemLp.convolution hp hφ1 hwp

/-- **Mollification approximates in `W^{k,p}(ℝ^d)`.** For `f ∈ W^{k,p}(ℝ^d)` with `1 ≤ p < ∞` and
a family of bump functions whose outer radii tend to `0`, the mollifications of `f` tend to `f` in
the Sobolev norm of order `k`.

On the whole space there is no boundary to keep away from, so the commutation of the weak
derivative with mollification holds at every point and the statement reduces to the `L^p`
convergence of mollification, `ContDiffBump.tendsto_eLpNorm_convolution_sub`, applied to each of
the `k + 1` weak derivatives at once. -/
theorem MemSobolev.tendsto_sobolevNorm_convolution_sub {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)} (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0))
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hf : MemSobolev f k p ⊤ μ) :
    Tendsto (fun i ↦ sobolevNorm ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f - f) k p ⊤ μ) l (𝓝 0) := by
  have hloc : LocallyIntegrable f μ := hf.memLp_top.locallyIntegrable hp
  have hwp : ∀ m ≤ k, MemLp (weakIteratedFDeriv m f ⊤ μ) p μ := fun m hm ↦ by
    simpa [Measure.restrict_coe_top] using hf.memLp_weakIteratedFDeriv hm
  set c : ι → ℝ≥0∞ := fun i ↦ ∑ m ∈ Finset.range (k + 1),
    eLpNorm ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] weakIteratedFDeriv m f ⊤ μ
      - weakIteratedFDeriv m f ⊤ μ) p μ with hcdef
  have hct : Tendsto c l (𝓝 0) := by
    have h0 : Tendsto c l (𝓝 (∑ _m ∈ Finset.range (k + 1), (0 : ℝ≥0∞))) :=
      tendsto_finsetSum _ fun m hm ↦
        ContDiffBump.tendsto_eLpNorm_convolution_sub hφ hp hp'
          (hwp m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)))
    simpa using h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (?_ : Tendsto (fun i ↦ (k + 1 : ℝ≥0∞) * c i) l (𝓝 0)) (fun _ ↦ zero_le) (fun i ↦ ?_)
  · simpa using ENNReal.Tendsto.const_mul hct (Or.inr (by simp))
  · refine sobolevNorm_le_of_forall_eLpNorm_le hp hp' fun m hm ↦ ?_
    have hsm : ContDiff ℝ ∞ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f) :=
      hloc.contDiff_convolution_normed (φ i)
    have hsub : HasWeakIteratedFDerivOn m ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f - f)
        (iteratedFDeriv ℝ m ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f) - weakIteratedFDeriv m f ⊤ μ)
        ⊤ μ :=
      (ContDiffOn.hasWeakIteratedFDerivOn hsm.contDiffOn (by simp)).sub
        (hf.hasWeakIteratedFDerivOn hm)
    rw [hsub.eLpNorm_weakIteratedFDeriv, Measure.restrict_coe_top]
    have heq : (iteratedFDeriv ℝ m ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f)
          - weakIteratedFDeriv m f ⊤ μ)
        = ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] weakIteratedFDeriv m f ⊤ μ
          - weakIteratedFDeriv m f ⊤ μ) :=
      funext fun x ↦ by
        simp only [Pi.sub_apply, hf.iteratedFDeriv_convolution_normed (φ i) hm x]
    rw [heq, hcdef]
    exact Finset.single_le_sum (f := fun m ↦ eLpNorm ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ]
      weakIteratedFDeriv m f ⊤ μ - weakIteratedFDeriv m f ⊤ μ) p μ)
      (fun _ _ ↦ zero_le) (Finset.mem_range.2 (Nat.lt_succ_of_le hm))

end Mollify

/-! ### Truncation on the whole space

A smooth function all of whose derivatives of order at most `k` lie in `L^p` is approximated in
`W^{k,p}` by its products with the cut-offs `x ↦ η (R⁻¹ x)`, because the Leibniz *bound* pays for
each derivative of the cut-off with a factor `R^{-i} ≤ 1`, and what is left is the `L^p` mass of
the derivatives of the function outside the ball of radius `R`. -/

section Truncate

variable [FiniteDimensional ℝ E] [BorelSpace E]

/-- **The `L^p` mass outside a large ball tends to `0`.** For `f ∈ L^p(μ)` with `p ≠ ∞` and radii
tending to infinity, the `L^p` norm of `f` restricted to the complement of the ball of that radius
tends to `0`.

The proof replaces `f` by a compactly supported approximation, which the complement of a large
enough ball does not see at all. -/
theorem MeasureTheory.MemLp.tendsto_eLpNorm_indicator_compl_ball [μ.IsAddHaarMeasure]
    (hp' : p ≠ ⊤) (hf : MemLp f p μ) {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    Tendsto (fun j ↦ eLpNorm ((Metric.ball (0 : E) (r j))ᶜ.indicator f) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨u, hucs, hule, -, -⟩ :=
    MemLp.exists_hasCompactSupport_eLpNorm_sub_le hp' hf hε.ne'
  obtain ⟨R, hR⟩ := hucs.isBounded.subset_closedBall (0 : E)
  filter_upwards [hr (Ioi_mem_atTop (R + 1))] with j hj
  have hzero : ∀ x ∈ (Metric.ball (0 : E) (r j))ᶜ, u x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport fun hmem ↦ ?_
    have h1 : ‖x‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hR hmem
    have h2 : r j ≤ ‖x‖ := by simpa [mem_ball, dist_eq_norm, not_lt] using hx
    have h3 : R + 1 < r j := hj
    linarith
  have heq : (Metric.ball (0 : E) (r j))ᶜ.indicator f
      = (Metric.ball (0 : E) (r j))ᶜ.indicator (f - u) := by
    funext x
    by_cases hx : x ∈ (Metric.ball (0 : E) (r j))ᶜ
    · simp [Set.indicator_of_mem hx, hzero x hx]
    · simp [Set.indicator_of_notMem hx]
  rw [heq]
  exact (eLpNorm_indicator_le _).trans hule

/-- A smooth cut-off on a finite-dimensional real normed space: a function equal to `1` on the
closed unit ball, supported in the ball of radius `2`, with values in `[0, 1]`. -/
theorem exists_contDiff_eqOn_one_closedBall_one (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ η : E → ℝ, ContDiff ℝ ∞ η ∧ EqOn η 1 (closedBall 0 1) ∧ tsupport η ⊆ ball 0 2 ∧
      ∀ x, η x ∈ Icc (0 : ℝ) 1 :=
  (isCompact_closedBall (0 : E) 1).exists_contDiff_eqOn_one isOpen_ball
    (closedBall_subset_ball (by norm_num))

variable [CompleteSpace F] [μ.IsAddHaarMeasure]

/-- **Truncation approximates in `W^{k,p}(ℝ^d)`.** If `g` is smooth and all its classical
derivatives of order at most `k` lie in `L^p`, then `g` is the `W^{k,p}(ℝ^d)` limit of a sequence
of smooth functions with compact support, namely the products of `g` with the cut-offs
`x ↦ η (R⁻¹ x)` as `R → ∞`.

Only the Leibniz *bound* `norm_iteratedFDeriv_smul_le` is needed, because both factors are smooth:
the derivatives of the cut-off carry a factor `R^{-i} ≤ 1` and vanish inside the ball of radius
`R`, so the whole difference is bounded there by a fixed multiple of the sum of the derivatives of
`g`, whose `L^p` mass outside a large ball tends to `0`. -/
theorem exists_seq_contDiff_hasCompactSupport_tendsto_sobolevNorm_sub (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {g : E → F} (hg : ContDiff ℝ ∞ g) (hgp : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m g) p μ) :
    ∃ v : ℕ → E → F, (∀ j, ContDiff ℝ ∞ (v j)) ∧ (∀ j, HasCompactSupport (v j)) ∧
      Tendsto (fun j ↦ sobolevNorm (v j - g) k p ⊤ μ) atTop (𝓝 0) := by
  obtain ⟨η, hηs, hη1, hηsupp, -⟩ := exists_contDiff_eqOn_one_closedBall_one E
  have hηc : HasCompactSupport η :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 2) isClosed_closure
      (hηsupp.trans ball_subset_closedBall)
  obtain ⟨M, hM0, hM⟩ := exists_bound_norm_iteratedFDeriv hηs hηc k
  set R : ℕ → ℝ := fun j ↦ (j : ℝ) + 1 with hRdef
  have hR1 : ∀ j, (1 : ℝ) ≤ R j := fun j ↦ by
    simp only [hRdef, le_add_iff_nonneg_left]
    positivity
  have hRpos : ∀ j, 0 < R j := fun j ↦ lt_of_lt_of_le one_pos (hR1 j)
  set c : ℕ → E → ℝ := fun j x ↦ η ((R j)⁻¹ • x) with hcdef
  set v : ℕ → E → F := fun j x ↦ c j x • g x with hvdef
  have hcs : ∀ j, ContDiff ℝ ∞ (c j) := fun j ↦ hηs.comp (contDiff_id.const_smul _)
  have hvs : ∀ j, ContDiff ℝ ∞ (v j) := fun j ↦ (hcs j).smul hg
  have hccs : ∀ j, HasCompactSupport (c j) := fun j ↦ by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R j)) fun x hx ↦ ?_
    have hnx : 2 * R j < ‖x‖ := by
      simpa [mem_closedBall, dist_eq_norm, not_le] using hx
    simp only [hcdef]
    refine image_eq_zero_of_notMem_tsupport (f := η) (x := (R j)⁻¹ • x) fun hmem ↦ ?_
    have h := hηsupp hmem
    rw [mem_ball, dist_eq_norm, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos (hRpos j), inv_mul_lt_iff₀ (hRpos j)] at h
    linarith
  have hvcs : ∀ j, HasCompactSupport (v j) := fun j ↦ (hccs j).smul_right
  have hlocal : ∀ j, ∀ x ∈ ball (0 : E) (R j), ∀ m : ℕ,
      iteratedFDeriv ℝ m (v j) x = iteratedFDeriv ℝ m g x := by
    intro j x hx m
    have hev : v j =ᶠ[𝓝 x] g := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      have hy0 : ‖y‖ < R j := by simpa [mem_ball, dist_eq_norm] using hy
      have hy1 : ‖(R j)⁻¹ • y‖ ≤ 1 := by
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hRpos j),
          inv_mul_le_iff₀ (hRpos j)]
        linarith
      have hone : η ((R j)⁻¹ • y) = 1 := hη1 (mem_closedBall_zero_iff.2 hy1)
      simp [hvdef, hcdef, hone]
    exact (Filter.EventuallyEq.iteratedFDeriv ℝ hev m).self_of_nhds
  have hcderiv : ∀ j, ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i (c j) x‖ ≤ M := by
    intro j i hi x
    have h1 : iteratedFDeriv ℝ i (c j) x
        = ((R j)⁻¹ : ℝ) ^ i • iteratedFDeriv ℝ i η ((R j)⁻¹ • x) :=
      congrFun (iteratedFDeriv_comp_const_smul ((R j)⁻¹) (hηs.of_le (by simp))) x
    have hinv0 : (0 : ℝ) ≤ (R j)⁻¹ := le_of_lt (inv_pos.2 (hRpos j))
    have hinv : (R j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hR1 j)
    rw [h1, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hinv0]
    calc (R j)⁻¹ ^ i * ‖iteratedFDeriv ℝ i η ((R j)⁻¹ • x)‖
        ≤ 1 * M :=
          mul_le_mul (pow_le_one₀ hinv0 hinv) (hM i hi _) (norm_nonneg _) zero_le_one
      _ = M := one_mul _
  set H : E → ℝ := fun x ↦ ∑ m ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ m g x‖ with hHdef
  have hH0 : ∀ x, 0 ≤ H x := fun x ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hHle : ∀ m ≤ k, ∀ x, ‖iteratedFDeriv ℝ m g x‖ ≤ H x := fun m hm x ↦
    Finset.single_le_sum (f := fun m ↦ ‖iteratedFDeriv ℝ m g x‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hm))
  set C : ℝ := 1 + ((k : ℝ) + 1) * 2 ^ k * M with hCdef
  have hC0 : 0 ≤ C := add_nonneg zero_le_one (mul_nonneg (by positivity) hM0)
  have hHp : MemLp H p μ :=
    memLp_finsetSum _ fun m hm ↦ (hgp m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))).norm
  have hCHp : MemLp (fun x ↦ C * H x) p μ := hHp.const_mul C
  have hkey : ∀ j, ∀ m ≤ k, ∀ x, ‖iteratedFDeriv ℝ m (v j) x - iteratedFDeriv ℝ m g x‖
      ≤ ‖(ball (0 : E) (R j))ᶜ.indicator (fun y ↦ C * H y) x‖ := by
    intro j m hm x
    by_cases hx : x ∈ ball (0 : E) (R j)
    · simp [hlocal j x hx m]
    · have hxc : x ∈ (ball (0 : E) (R j))ᶜ := hx
      rw [Set.indicator_of_mem hxc, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hC0 (hH0 x))]
      have hle1 : ‖iteratedFDeriv ℝ m (v j) x‖ ≤ (((k : ℝ) + 1) * 2 ^ k * M) * H x :=
        norm_iteratedFDeriv_smul_le_const_mul_sum (hcs j) hg (hcderiv j) hm x
      have hle2 : ‖iteratedFDeriv ℝ m g x‖ ≤ H x := hHle m hm x
      calc ‖iteratedFDeriv ℝ m (v j) x - iteratedFDeriv ℝ m g x‖
          ≤ ‖iteratedFDeriv ℝ m (v j) x‖ + ‖iteratedFDeriv ℝ m g x‖ := norm_sub_le _ _
        _ ≤ (((k : ℝ) + 1) * 2 ^ k * M) * H x + H x := by gcongr
        _ = C * H x := by rw [hCdef]; ring
  refine ⟨v, hvs, hvcs, ?_⟩
  have hind : Tendsto
      (fun j ↦ eLpNorm ((ball (0 : E) (R j))ᶜ.indicator (fun y ↦ C * H y)) p μ) atTop (𝓝 0) :=
    hCHp.tendsto_eLpNorm_indicator_compl_ball hp'
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (?_ : Tendsto (fun j ↦ (k + 1 : ℝ≥0∞) *
      eLpNorm ((ball (0 : E) (R j))ᶜ.indicator (fun y ↦ C * H y)) p μ) atTop (𝓝 0))
    (fun _ ↦ zero_le) (fun j ↦ ?_)
  · simpa using ENNReal.Tendsto.const_mul hind (Or.inr (by simp))
  · refine sobolevNorm_le_of_forall_eLpNorm_le hp hp' fun m hm ↦ ?_
    have hsub : HasWeakIteratedFDerivOn m (v j - g)
        (iteratedFDeriv ℝ m (v j) - iteratedFDeriv ℝ m g) ⊤ μ :=
      (ContDiffOn.hasWeakIteratedFDerivOn (hvs j).contDiffOn (by simp)).sub
        (ContDiffOn.hasWeakIteratedFDerivOn hg.contDiffOn (by simp))
    rw [hsub.eLpNorm_weakIteratedFDeriv, Measure.restrict_coe_top]
    exact eLpNorm_mono fun x ↦ hkey j m hm x

end Truncate

/-! ### `C_0^∞(ℝ^d)` is dense in `W^{k,p}(ℝ^d)` -/

section Density

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- One weak derivative is measured by the Sobolev norm: the `L^p(Ω)` norm of the chosen weak
derivative of order `n ≤ k` is at most `‖f‖_{k,p,Ω}`. -/
theorem eLpNorm_weakIteratedFDeriv_le_sobolevNorm (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hn : n ≤ k) :
    eLpNorm (weakIteratedFDeriv n f Ω μ) p (μ.restrict (Ω : Set E)) ≤ sobolevNorm f k p Ω μ := by
  have hp₀ : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp'
  set a : Fin (k + 1) → ℝ≥0∞ :=
    fun i ↦ eLpNorm (weakIteratedFDeriv i f Ω μ) p (μ.restrict (Ω : Set E)) with hadef
  have hsob : sobolevNorm f k p Ω μ = (∑ i, a i ^ p.toReal) ^ (1 / p.toReal) := by
    simp only [sobolevNorm, hp', ↓reduceIte, hadef]
  have hmem : a ⟨n, Nat.lt_succ_of_le hn⟩
      = eLpNorm (weakIteratedFDeriv n f Ω μ) p (μ.restrict (Ω : Set E)) := rfl
  rw [hsob, ← hmem]
  have h1 : a ⟨n, Nat.lt_succ_of_le hn⟩ ^ p.toReal ≤ ∑ i, a i ^ p.toReal :=
    Finset.single_le_sum (f := fun i ↦ a i ^ p.toReal) (fun _ _ ↦ zero_le) (Finset.mem_univ _)
  calc a ⟨n, Nat.lt_succ_of_le hn⟩
      = (a ⟨n, Nat.lt_succ_of_le hn⟩ ^ p.toReal) ^ (1 / p.toReal) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hP.ne', ENNReal.rpow_one]
    _ ≤ (∑ i, a i ^ p.toReal) ^ (1 / p.toReal) := ENNReal.rpow_le_rpow h1 (by positivity)

omit [μ.IsAddHaarMeasure] in
/-- On the whole space, the `L^p` norm of any weak derivative of order `n ≤ k` is at most the
Sobolev norm. -/
theorem HasWeakIteratedFDerivOn.eLpNorm_le_sobolevNorm_top {w : E → E [×n]→L[ℝ] F}
    (h : HasWeakIteratedFDerivOn n f w ⊤ μ) (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hn : n ≤ k) :
    eLpNorm w p μ ≤ sobolevNorm f k p ⊤ μ := by
  have h1 : eLpNorm w p μ
      = eLpNorm (weakIteratedFDeriv n f ⊤ μ) p (μ.restrict ((⊤ : Opens E) : Set E)) := by
    rw [h.eLpNorm_weakIteratedFDeriv, Measure.restrict_coe_top]
  rw [h1]
  exact eLpNorm_weakIteratedFDeriv_le_sobolevNorm hp hp' hn

/-- The classical derivatives of order `n ≤ k` of a smooth function of `W^{k,p}(Ω)` lie in
`L^p(Ω)`. -/
theorem MemSobolev.memLp_iteratedFDeriv (h : MemSobolev f k p Ω μ) (hf : ContDiffOn ℝ ∞ f Ω)
    (hn : n ≤ k) : MemLp (iteratedFDeriv ℝ n f) p (μ.restrict (Ω : Set E)) := by
  refine (h.memLp_weakIteratedFDeriv hn).ae_eq ?_
  exact (ae_restrict_iff' Ω.isOpen.measurableSet).2
    ((ContDiffOn.hasWeakIteratedFDerivOn hf (by simp)).weakIteratedFDeriv_ae_eq (μ := μ))

/-- A sequence of bump functions centred at the origin whose outer radii tend to `0`. -/
theorem exists_seq_contDiffBump_tendsto_rOut_zero (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] :
    ∃ φ : ℕ → ContDiffBump (0 : E), Tendsto (fun j ↦ (φ j).rOut) atTop (𝓝 0) := by
  refine ⟨fun j ↦ ⟨1 / (2 * (j + 2)), 1 / (j + 2), by positivity, ?_⟩, ?_⟩
  · apply div_lt_div_of_pos_left one_pos (by positivity)
    nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  · exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)

/-- **`C_0^∞(ℝ^d)` approximates in `W^{k,p}(ℝ^d)`**, in the form with an explicit tolerance: for
`f ∈ W^{k,p}(ℝ^d)` with `1 ≤ p < ∞` and any `ε ≠ 0` there is a smooth compactly supported `v` with
`‖v - f‖_{k,p} ≤ ε`.

Mollify to within `ε / (2(k+1))`, then truncate the mollification to within the same, and add. -/
theorem MemSobolev.exists_contDiff_hasCompactSupport_sobolevNorm_sub_le (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : MemSobolev f k p ⊤ μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ v : E → F, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧ sobolevNorm (v - f) k p ⊤ μ ≤ ε := by
  set δ : ℝ≥0∞ := ε / (2 * ((k : ℝ≥0∞) + 1)) with hδdef
  have hne0 : (2 * ((k : ℝ≥0∞) + 1)) ≠ 0 := by
    simp
  have hnetop : (2 * ((k : ℝ≥0∞) + 1)) ≠ ⊤ := ENNReal.mul_ne_top (by simp) (by simp)
  have hδpos : 0 < δ := ENNReal.div_pos hε hnetop
  -- mollify
  obtain ⟨φ, hφ⟩ := exists_seq_contDiffBump_tendsto_rOut_zero E
  obtain ⟨j, hj⟩ := (ENNReal.tendsto_nhds_zero.1
    (hf.tendsto_sobolevNorm_convolution_sub hφ hp hp') δ hδpos).exists
  set g : E → F := (φ j).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f with hgdef
  have hgs : ContDiff ℝ ∞ g :=
    (hf.memLp_top.locallyIntegrable hp).contDiff_convolution_normed (φ j)
  have hgS : MemSobolev g k p ⊤ μ := hf.convolution_normed hp (φ j)
  have hgLp : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m g) p μ := fun m hm ↦ by
    simpa [Measure.restrict_coe_top] using hgS.memLp_iteratedFDeriv hgs.contDiffOn hm
  -- truncate
  obtain ⟨v, hv1, hv2, hv3⟩ :=
    exists_seq_contDiff_hasCompactSupport_tendsto_sobolevNorm_sub hp hp' hgs hgLp
  obtain ⟨i, hi⟩ := (ENNReal.tendsto_nhds_zero.1 hv3 δ hδpos).exists
  refine ⟨v i, hv1 i, hv2 i, ?_⟩
  refine le_trans (sobolevNorm_le_of_forall_eLpNorm_le hp hp' (c := δ + δ) fun m hm ↦ ?_) ?_
  · have hA : HasWeakIteratedFDerivOn m (v i - g)
        (iteratedFDeriv ℝ m (v i) - iteratedFDeriv ℝ m g) ⊤ μ :=
      (ContDiffOn.hasWeakIteratedFDerivOn (hv1 i).contDiffOn (by simp)).sub
        (ContDiffOn.hasWeakIteratedFDerivOn hgs.contDiffOn (by simp))
    have hB : HasWeakIteratedFDerivOn m (g - f)
        (iteratedFDeriv ℝ m g - weakIteratedFDeriv m f ⊤ μ) ⊤ μ :=
      (ContDiffOn.hasWeakIteratedFDerivOn hgs.contDiffOn (by simp)).sub
        (hf.hasWeakIteratedFDerivOn hm)
    have hC : HasWeakIteratedFDerivOn m (v i - f)
        (iteratedFDeriv ℝ m (v i) - weakIteratedFDeriv m f ⊤ μ) ⊤ μ :=
      (ContDiffOn.hasWeakIteratedFDerivOn (hv1 i).contDiffOn (by simp)).sub
        (hf.hasWeakIteratedFDerivOn hm)
    rw [hC.eLpNorm_weakIteratedFDeriv, Measure.restrict_coe_top]
    have hsplit : (iteratedFDeriv ℝ m (v i) - weakIteratedFDeriv m f ⊤ μ)
        = (iteratedFDeriv ℝ m (v i) - iteratedFDeriv ℝ m g)
          + (iteratedFDeriv ℝ m g - weakIteratedFDeriv m f ⊤ μ) := by
      funext x
      simp only [Pi.sub_apply, Pi.add_apply]
      abel
    have hm1 : AEStronglyMeasurable
        (iteratedFDeriv ℝ m (v i) - iteratedFDeriv ℝ m g) μ :=
      ((hv1 i).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable.sub
        (hgs.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable
        (iteratedFDeriv ℝ m g - weakIteratedFDeriv m f ⊤ μ) μ := by
      refine (hgs.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable.sub ?_
      simpa [Measure.restrict_coe_top] using
        (hf.memLp_weakIteratedFDeriv hm).aestronglyMeasurable
    have hle1 : eLpNorm (iteratedFDeriv ℝ m (v i) - iteratedFDeriv ℝ m g) p μ ≤ δ :=
      (hA.eLpNorm_le_sobolevNorm_top hp hp' hm).trans hi
    have hle2 : eLpNorm (iteratedFDeriv ℝ m g - weakIteratedFDeriv m f ⊤ μ) p μ ≤ δ :=
      (hB.eLpNorm_le_sobolevNorm_top hp hp' hm).trans hj
    rw [hsplit]
    exact (eLpNorm_add_le hm1 hm2 hp).trans (add_le_add hle1 hle2)
  · calc ((k : ℝ≥0∞) + 1) * (δ + δ) = (2 * ((k : ℝ≥0∞) + 1)) * δ := by
          rw [← two_mul]; ring
      _ = ε := ENNReal.mul_div_cancel' (fun h ↦ absurd h hne0) (fun h ↦ absurd h hnetop)
      _ ≤ ε := le_rfl

/-- **`C_0^∞(ℝ^d)` is dense in `W^{k,p}(ℝ^d)`** for `1 ≤ p < ∞`: every function of the Sobolev
space of the whole space is the limit, in the Sobolev norm of order `k`, of a sequence of smooth
functions with compact support.

This is Theorem 7.3.4 of Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A
Functional Analysis Framework*, 3rd edition, Springer, 2009; see also R. A. Adams and
J. J. F. Fournier, *Sobolev Spaces*, 2nd edition, Academic Press, 2003, Theorem 3.22. The whole
space is exactly the case in which no partition of unity is needed: one mollification serves at
every point at once, and the passage to compact support is a truncation. -/
theorem MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : MemSobolev f k p ⊤ μ) :
    ∃ v : ℕ → E → F, (∀ i, ContDiff ℝ ∞ (v i)) ∧ (∀ i, HasCompactSupport (v i)) ∧
      Tendsto (fun i ↦ sobolevNorm (v i - f) k p ⊤ μ) atTop (𝓝 0) := by
  have key : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ v : E → F, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      sobolevNorm (v - f) k p ⊤ μ ≤ ε := fun ε hε ↦
    hf.exists_contDiff_hasCompactSupport_sobolevNorm_sub_le hp hp' hε
  choose! V hV1 hV2 hV3 using key
  have hne : ∀ i : ℕ, ((i : ℝ≥0∞))⁻¹ ≠ 0 := fun i ↦ ENNReal.inv_ne_zero.2 (by simp)
  refine ⟨fun i ↦ V ((i : ℝ≥0∞))⁻¹, fun i ↦ hV1 _ (hne i), fun i ↦ hV2 _ (hne i), ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ zero_le) (fun i ↦ hV3 _ (hne i))

end Density

/-! ### The weak derivative is closed under `L^1` limits

An identity between integrals against a fixed test function passes to an `L^1` limit, so a
function that is the `L^1` limit of functions with weak derivatives, whose weak derivatives
converge in `L^1` as well, has the limit as its weak derivative. This is what replaces the Leibniz
formula below: the weak derivative of a product `ψ f` is obtained as a limit of the classical
derivatives of `ψ g` for smooth `g` approximating `f`, and never written down. -/

section Closed

variable [OpensMeasurableSpace E]

omit [OpensMeasurableSpace E] in
/-- Composing with a continuous linear map multiplies the `L^1` norm by at most its operator
norm. -/
theorem MeasureTheory.eLpNorm_one_comp_continuousLinearMap_le {X G G' : Type*}
    [MeasurableSpace X] {ν : Measure X} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup G'] [NormedSpace ℝ G'] (Λ : G →L[ℝ] G') (h : X → G) :
    eLpNorm (fun x ↦ Λ (h x)) 1 ν ≤ ‖Λ‖ₑ * eLpNorm h 1 ν := by
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
    ← lintegral_const_mul' _ _ (enorm_ne_top (x := Λ))]
  exact lintegral_mono fun x ↦ Λ.le_opENorm (h x)

/-- **The weak derivative is closed under `L^1` limits**: if `u i` is a weak derivative of order
`n` of `g i` on `Ω` for every `i`, and `g i → f` and `u i → w` in `L^1(Ω)`, then `w` is a weak
derivative of order `n` of `f` on `Ω`.

The local integrability of `f` and of `w` has to be assumed: `L^1(Ω)` convergence does not by
itself place the limit in `L^1_loc(Ω)` when `μ Ω = ∞`, and in the applications it is known
anyway. -/
theorem hasWeakIteratedFDerivOn_of_tendsto_eLpNorm_one {g : ℕ → E → F}
    {u : ℕ → E → E [×n]→L[ℝ] F} {w : E → E [×n]→L[ℝ] F}
    (hg : ∀ i, HasWeakIteratedFDerivOn n (g i) (u i) Ω μ)
    (hfl : LocallyIntegrableOn f Ω μ) (hwl : LocallyIntegrableOn w Ω μ)
    (h1 : Tendsto (fun i ↦ eLpNorm (g i - f) 1 (μ.restrict (Ω : Set E))) atTop (𝓝 0))
    (h2 : Tendsto (fun i ↦ eLpNorm (u i - w) 1 (μ.restrict (Ω : Set E))) atTop (𝓝 0)) :
    HasWeakIteratedFDerivOn n f w Ω μ where
  locallyIntegrableOn := hfl
  locallyIntegrableOn_weakDeriv := hwl
  integral_smul_eq φ y := by
    set a : 𝓓(Ω, ℝ) := φ.iteratedFDerivApply n y with hadef
    obtain ⟨Ca, hCa⟩ := a.hasCompactSupport.exists_bound_of_continuous a.contDiff.continuous
    obtain ⟨Cφ, hCφ⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous
    have hCa' : ∀ x, |a x| ≤ Ca := fun x ↦ by simpa [Real.norm_eq_abs] using hCa x
    have hCφ' : ∀ x, |φ x| ≤ Cφ := fun x ↦ by simpa [Real.norm_eq_abs] using hCφ x
    set Λ : (E [×n]→L[ℝ] F) →L[ℝ] F :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) F y with hΛdef
    -- the left-hand sides converge
    have hIg : ∀ i, IntegrableOn (fun x ↦ a x • g i x) (Ω : Set E) μ := fun i ↦
      ((hg i).integrable_smul a).integrableOn
    have hIf : IntegrableOn (fun x ↦ a x • f x) (Ω : Set E) μ :=
      (LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset hfl a.contDiff.continuous
        a.hasCompactSupport a.tsupport_subset).integrableOn
    have hA : Tendsto (fun i ↦ ∫ x in (Ω : Set E), a x • g i x ∂μ) atTop
        (𝓝 (∫ x in (Ω : Set E), a x • f x ∂μ)) := by
      rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_enorm_tendsto_zero]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (?_ : Tendsto (fun i ↦ ENNReal.ofReal Ca *
          eLpNorm (g i - f) 1 (μ.restrict (Ω : Set E))) atTop (𝓝 0))
        (fun _ ↦ zero_le) (fun i ↦ ?_)
      · simpa using ENNReal.Tendsto.const_mul h1 (Or.inr (by simp))
      · rw [← integral_sub (hIg i) hIf]
        have heq : (fun x ↦ a x • g i x - a x • f x) = fun x ↦ a x • (g i - f) x :=
          funext fun x ↦ by simp [smul_sub]
        rw [heq]
        exact enorm_integral_smul_le_of_bound (μ := μ.restrict (Ω : Set E)) hCa'
    -- the right-hand sides converge
    have hIu : ∀ i, IntegrableOn (fun x ↦ φ x • Λ (u i x)) (Ω : Set E) μ := fun i ↦
      ((hg i).integrable_smul_weakDeriv_apply φ y).integrableOn
    have hIw : IntegrableOn (fun x ↦ φ x • Λ (w x)) (Ω : Set E) μ :=
      (LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset
        (hwl.comp_continuousLinearMap Λ) φ.contDiff.continuous φ.hasCompactSupport
        φ.tsupport_subset).integrableOn
    have hB : Tendsto (fun i ↦ ∫ x in (Ω : Set E), φ x • Λ (u i x) ∂μ) atTop
        (𝓝 (∫ x in (Ω : Set E), φ x • Λ (w x) ∂μ)) := by
      rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_enorm_tendsto_zero]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (?_ : Tendsto (fun i ↦ (ENNReal.ofReal Cφ * ‖Λ‖ₑ) *
          eLpNorm (u i - w) 1 (μ.restrict (Ω : Set E))) atTop (𝓝 0))
        (fun _ ↦ zero_le) (fun i ↦ ?_)
      · simpa using ENNReal.Tendsto.const_mul h2
          (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (enorm_ne_top (x := Λ))))
      · rw [← integral_sub (hIu i) hIw]
        have heq : (fun x ↦ φ x • Λ (u i x) - φ x • Λ (w x))
            = fun x ↦ φ x • Λ ((u i - w) x) :=
          funext fun x ↦ by simp only [Pi.sub_apply, map_sub, smul_sub]
        rw [heq, mul_assoc]
        refine (enorm_integral_smul_le_of_bound (μ := μ.restrict (Ω : Set E)) hCφ').trans ?_
        gcongr
        exact eLpNorm_one_comp_continuousLinearMap_le Λ _
    have hAB : ∀ i, (∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x y • g i x ∂μ)
        = (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), φ x • Λ (u i x) ∂μ := fun i ↦
      (hg i).integral_smul_eq φ y
    have hax : ∀ x, a x = iteratedFDeriv ℝ n (φ : E → ℝ) x y := fun _ ↦ rfl
    have hA' : Tendsto (fun i ↦ (-1 : ℝ) ^ n • ∫ x in (Ω : Set E), φ x • Λ (u i x) ∂μ) atTop
        (𝓝 (∫ x in (Ω : Set E), iteratedFDeriv ℝ n (φ : E → ℝ) x y • f x ∂μ)) := by
      simpa only [hax, hAB] using hA
    exact tendsto_nhds_unique hA' (hB.const_smul ((-1 : ℝ) ^ n))

end Closed

/-! ### Local approximation in `W^{k,p}`, at all orders at once

The mollifications of a function of `W^{k,p}(Ω)` approximate it, together with *every* weak
derivative of order at most `k`, in `L^p` of a relatively compact open subset of `Ω`. This is the
bundled form of `HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm`, which fixes one
tuple of directions; the point of the bundled form is that a single sequence of smooth functions
serves all the orders at once, which is what a Leibniz estimate needs. -/

section LocalApprox

open ContinuousLinearMap

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure]

/-- **Local approximation in `W^{k,p}`**: for `f ∈ W^{k,p}(Ω)` with `1 ≤ p < ∞` and `V` an open
set whose closure is a compact subset of `Ω`, there are globally smooth `g 0, g 1, …` with
`∂^m (g i) → ∂^m f` in `L^p(V)` for every order `m ≤ k` at once.

The `g i` are the mollifications of the truncation of `f` to a compact neighbourhood of
`closure V` in `Ω`; the identification of `∂^m (g i)` on `V` with the mollification of the weak
derivative is `HasWeakIteratedFDerivOn.iteratedFDeriv_convolution`, and the convergence is
`ContDiffBump.tendsto_eLpNorm_convolution_sub`. -/
theorem MemSobolev.exists_seq_contDiff_tendsto_eLpNorm (hf : MemSobolev f k p Ω μ) (hp : 1 ≤ p)
    (hp' : p ≠ ⊤) {V : Set E} (hVo : IsOpen V) (hVc : IsCompact (closure V))
    (hVΩ : closure V ⊆ (Ω : Set E)) :
    ∃ g : ℕ → E → F, (∀ i, ContDiff ℝ ∞ (g i)) ∧
      Tendsto (fun i ↦ eLpNorm (g i - f) p (μ.restrict V)) atTop (𝓝 0) ∧ ∀ m ≤ k,
      Tendsto (fun i ↦ eLpNorm (iteratedFDeriv ℝ m (g i) - weakIteratedFDeriv m f Ω μ) p
        (μ.restrict V)) atTop (𝓝 0) := by
  obtain ⟨W, -, hWo, hVW, -, hWc, hWΩ, -⟩ := hVc.exists_pos_forall_closedBall_subset Ω.isOpen hVΩ
  obtain ⟨V', ε, hV'o, hVV', hε, -, -, hV'ball⟩ := hVc.exists_pos_forall_closedBall_subset hWo hVW
  set C : Set E := closure W with hCdef
  have hCmeas : MeasurableSet C := hWc.isClosed.measurableSet
  have hWC : W ⊆ interior C := interior_maximal subset_closure hWo
  have hVC : V ⊆ C := (subset_closure.trans hVW).trans subset_closure
  have hCΩ : C ⊆ (Ω : Set E) := hWΩ
  set f' : E → F := C.indicator f with hf'def
  have hf'Lp : MemLp f' p μ := (memLp_indicator_iff_restrict (f := f) hCmeas).2
    (hf.memLp.mono_measure (Measure.restrict_mono hCΩ le_rfl))
  have hf'loc : LocallyIntegrable f' μ := hf'Lp.locallyIntegrable hp
  have hw'Lp : ∀ m ≤ k, MemLp (C.indicator (weakIteratedFDeriv m f Ω μ)) p μ := fun m hm ↦
    (memLp_indicator_iff_restrict (f := weakIteratedFDeriv m f Ω μ) hCmeas).2
      ((hf.memLp_weakIteratedFDeriv hm).mono_measure (Measure.restrict_mono hCΩ le_rfl))
  have hint : ∀ m ≤ k, HasWeakIteratedFDerivOn m f' (C.indicator (weakIteratedFDeriv m f Ω μ))
      ⟨interior C, isOpen_interior⟩ μ := fun m hm ↦
    ((hf.hasWeakIteratedFDerivOn hm).mono (interior_subset.trans hCΩ)).congr_ae
      (Filter.eventually_of_mem (self_mem_ae_restrict isOpen_interior.measurableSet)
        fun z hz ↦ (Set.indicator_of_mem (interior_subset hz) f).symm)
      (Filter.eventually_of_mem (self_mem_ae_restrict isOpen_interior.measurableSet)
        fun z hz ↦ (Set.indicator_of_mem (interior_subset hz) _).symm)
  set φ : ℕ → ContDiffBump (0 : E) := fun j ↦
    ⟨ε / (2 * (j + 2)), ε / (j + 2), by positivity, by
      apply div_lt_div_of_pos_left hε (by positivity)
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]⟩ with hφdef
  have hrOut : ∀ j, (φ j).rOut = ε / (j + 2) := fun j ↦ rfl
  have hrOutle : ∀ j, (φ j).rOut ≤ ε := fun j ↦ by
    rw [hrOut, div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have htend : Tendsto (fun j ↦ (φ j).rOut) atTop (𝓝 0) := by
    simp only [hrOut]
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  set g : ℕ → E → F := fun j ↦ (φ j).normed μ ⋆[lsmul ℝ ℝ, μ] f' with hgdef
  have hball : ∀ j, ∀ x ∈ V, closedBall x (φ j).rOut ⊆ interior C := fun j x hx ↦
    ((closedBall_subset_closedBall (hrOutle j)).trans
      (hV'ball x (hVV' (subset_closure hx)))).trans hWC
  have hderivEq : ∀ m ≤ k, ∀ j, ∀ x ∈ V, iteratedFDeriv ℝ m (g j) x
      = ((φ j).normed μ ⋆[lsmul ℝ ℝ, μ] C.indicator (weakIteratedFDeriv m f Ω μ)) x :=
    fun m hm j x hx ↦ (hint m hm).iteratedFDeriv_convolution (φ j).contDiff_normed
      (le_of_eq ((φ j).tsupport_normed_eq (μ := μ))) (hball j x hx)
  refine ⟨g, fun j ↦ (φ j).hasCompactSupport_normed.contDiff_convolution_left _
    (φ j).contDiff_normed hf'loc, ?_, fun m hm ↦ ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ContDiffBump.tendsto_eLpNorm_convolution_sub htend hp hp' hf'Lp)
      (fun _ ↦ zero_le) (fun j ↦ ?_)
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_))
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
    filter_upwards [self_mem_ae_restrict hVo.measurableSet] with x hx
    rw [Pi.sub_apply, Pi.sub_apply, hf'def, Set.indicator_of_mem (hVC hx) f]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ContDiffBump.tendsto_eLpNorm_convolution_sub htend hp hp' (hw'Lp m hm))
    (fun _ ↦ zero_le) (fun j ↦ ?_)
  refine le_trans (le_of_eq (eLpNorm_congr_ae ?_))
    (eLpNorm_mono_measure _ Measure.restrict_le_self)
  filter_upwards [self_mem_ae_restrict hVo.measurableSet] with x hx
  rw [Pi.sub_apply, Pi.sub_apply, hderivEq m hm j x hx,
    Set.indicator_of_mem (hVC hx) (weakIteratedFDeriv m f Ω μ)]

end LocalApprox

/-! ### The telescoping partition of unity of an exhaustion

An open set is exhausted by relatively compact opens `U 0 ⊆ U 1 ⊆ …`; taking smooth Urysohn
functions `χ_j` that are `1` on `closure (U j)` and supported in `U (j+1)`, the differences
`ψ_j = χ_j - χ_{j-1}` form a smooth partition of unity on `Ω` whose partial sums telescope. It is
locally finite in the strongest possible sense: on `U N` all but the first `N + 1` of the `ψ_j`
vanish identically, and the first `N + 1` already sum to `1` there. -/

section PartitionOfUnity

variable [FiniteDimensional ℝ E]

omit [MeasurableSpace E] in
/-- The support of a difference is contained in the union of the supports, in the closed form. -/
theorem tsupport_sub_subset {X : Type*} [TopologicalSpace X] {G : Type*} [SubtractionMonoid G]
    (a b : X → G) : tsupport (a - b) ⊆ tsupport a ∪ tsupport b := by
  have hs : Function.support (a - b) ⊆ Function.support a ∪ Function.support b := by
    intro x hx
    by_contra hcon
    simp only [Set.mem_union, Function.mem_support, ne_eq, not_or, not_not] at hcon
    exact hx (by simp [Pi.sub_apply, hcon.1, hcon.2])
  calc tsupport (a - b) ⊆ closure (Function.support a ∪ Function.support b) := closure_mono hs
    _ = tsupport a ∪ tsupport b := closure_union

omit [MeasurableSpace E] in
/-- **A smooth partition of unity subordinate to an exhaustion of an open set.** There is an
exhaustion `U 0 ⊆ U 1 ⊆ …` of `Ω` by relatively compact open sets and a sequence `ψ 0, ψ 1, …` of
smooth compactly supported functions with `tsupport (ψ j) ⊆ U (j + 1)` such that, on `U N`, the
functions `ψ 0, …, ψ N` sum to `1` and every later one vanishes.

This is the telescoping construction `ψ_j = χ_j - χ_{j-1}` from the smooth Urysohn lemma
`IsCompact.exists_contDiff_eqOn_one`; the local finiteness it gives is the strong form above,
which is what makes the sums below finite on each `U N` rather than merely locally finite. -/
theorem TopologicalSpace.Opens.exists_partitionOfUnity (Ω : Opens E) :
    ∃ (U : ℕ → Opens E) (ψ : ℕ → E → ℝ),
      (∀ j, IsCompact (closure (U j : Set E))) ∧ (∀ j, closure (U j : Set E) ⊆ U (j + 1)) ∧
        (⋃ j, (U j : Set E)) = Ω ∧ (∀ j, ContDiff ℝ ∞ (ψ j)) ∧
        (∀ j, HasCompactSupport (ψ j)) ∧ (∀ j, tsupport (ψ j) ⊆ (U (j + 1) : Set E)) ∧
        (∀ N, ∀ x ∈ (U N : Set E), ∑ j ∈ Finset.range (N + 1), ψ j x = 1) ∧
        (∀ N j, N < j → ∀ x ∈ (U N : Set E), ψ j x = 0) := by
  obtain ⟨U, hUc, hUs, hUΩ⟩ := Ω.exists_exhaustion
  have hUmono : Monotone fun j ↦ (U j : Set E) :=
    monotone_nat_of_le_succ fun j ↦ subset_closure.trans (hUs j)
  -- the Urysohn functions
  have hχ : ∀ j : ℕ, ∃ c : E → ℝ, ContDiff ℝ ∞ c ∧ EqOn c 1 (closure (U j : Set E)) ∧
      tsupport c ⊆ (U (j + 1) : Set E) := fun j ↦ by
    obtain ⟨c, hc1, hc2, hc3, -⟩ :=
      (hUc j).exists_contDiff_eqOn_one (U (j + 1)).isOpen (hUs j)
    exact ⟨c, hc1, hc2, hc3⟩
  choose χ hχs hχ1 hχsupp using hχ
  -- shifted by one, so that the telescoping starts at zero
  set c : ℕ → E → ℝ := fun j ↦ Nat.rec (0 : E → ℝ) (fun i _ ↦ χ i) j with hcdef
  have hc0 : c 0 = 0 := rfl
  have hcsucc : ∀ i, c (i + 1) = χ i := fun _ ↦ rfl
  have hcs : ∀ j, ContDiff ℝ ∞ (c j) := fun j ↦ by
    cases j with
    | zero => rw [hc0]; exact contDiff_const
    | succ i => rw [hcsucc]; exact hχs i
  have hcsupp : ∀ j, tsupport (c j) ⊆ (U j : Set E) := fun j ↦ by
    cases j with
    | zero => rw [hc0]; simp [tsupport]
    | succ i => rw [hcsucc]; exact hχsupp i
  have hcone : ∀ i, ∀ x ∈ closure (U i : Set E), c (i + 1) x = 1 := fun i x hx ↦ by
    rw [hcsucc]; exact hχ1 i hx
  refine ⟨U, fun j ↦ c (j + 1) - c j, hUc, hUs, hUΩ, fun j ↦ (hcs (j + 1)).sub (hcs j),
    fun j ↦ ?_, fun j ↦ ?_, fun N x hx ↦ ?_, fun N j hNj x hx ↦ ?_⟩
  · exact (hUc (j + 1)).of_isClosed_subset isClosed_closure
      (((tsupport_sub_subset _ _).trans
        (Set.union_subset (hcsupp (j + 1)) ((hcsupp j).trans (hUmono (Nat.le_succ j))))).trans
        subset_closure)
  · exact (tsupport_sub_subset _ _).trans
      (Set.union_subset (hcsupp (j + 1)) ((hcsupp j).trans (hUmono (Nat.le_succ j))))
  · have := Finset.sum_range_sub (fun j ↦ c j x) (N + 1)
    simp only [Pi.sub_apply] at this ⊢
    rw [this, hc0, Pi.zero_apply, sub_zero]
    exact hcone N x (subset_closure hx)
  · have hj : N ≤ j - 1 := by omega
    have hxj : x ∈ closure (U (j - 1) : Set E) :=
      subset_closure (hUmono hj hx)
    have h1 : c j x = 1 := by
      have : j - 1 + 1 = j := by omega
      rw [← this]
      exact hcone (j - 1) x hxj
    have h2 : c (j + 1) x = 1 := hcone j x (subset_closure (hUmono (le_of_lt hNj) hx))
    simp [Pi.sub_apply, h1, h2]

end PartitionOfUnity

/-! ### The `L^p` Leibniz estimate for one piece of a partition of unity -/

section Piece

variable [FiniteDimensional ℝ E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
/-- **The `L^p` Leibniz estimate.** For `ψ` smooth, supported in an open set `V`, with every
derivative of order at most `k` bounded by `M`, and `a`, `b` smooth, the `L^p` norm of the
derivative of order `n ≤ k` of `ψ (a - b)` is at most `(k+1) 2^k M` times the sum, over the orders
`s ≤ k`, of the `L^p(V)` distances between the derivatives of `a` and of `b`.

Only the classical Leibniz *bound* is used, both factors being smooth. Note that the measure on
the left is arbitrary: the derivative of `ψ (a - b)` vanishes outside `V`, so the estimate is
really an estimate over `V`. -/
theorem eLpNorm_iteratedFDeriv_smul_sub_le {V W : Set E} (hV : IsOpen V) {ψ : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψsupp : tsupport ψ ⊆ V) {M : ℝ}
    (hM : ∀ r ≤ k, ∀ x, ‖iteratedFDeriv ℝ r ψ x‖ ≤ M) {a b : E → F} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hp : 1 ≤ p) {m : ℕ} (hm : m ≤ k) :
    eLpNorm (iteratedFDeriv ℝ m fun y ↦ ψ y • (a y - b y)) p (μ.restrict W)
      ≤ ENNReal.ofReal (((k : ℝ) + 1) * 2 ^ k * M) * ∑ s ∈ Finset.range (k + 1),
        eLpNorm (iteratedFDeriv ℝ s a - iteratedFDeriv ℝ s b) p (μ.restrict V) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (Nat.zero_le k) 0)
  have hD0 : (0 : ℝ) ≤ ((k : ℝ) + 1) * 2 ^ k * M := by positivity
  have hS0 : ∀ y : E, (0 : ℝ) ≤ ∑ s ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ s a y - iteratedFDeriv ℝ s b y‖ :=
    fun y ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hpt : ∀ x, ‖iteratedFDeriv ℝ m (fun y ↦ ψ y • (a y - b y)) x‖ₑ
      ≤ ‖V.indicator (fun y ↦ (((k : ℝ) + 1) * 2 ^ k * M) * ∑ s ∈ Finset.range (k + 1),
          ‖iteratedFDeriv ℝ s a y - iteratedFDeriv ℝ s b y‖) x‖ₑ := by
    intro x
    by_cases hx : x ∈ V
    · rw [Set.indicator_of_mem hx, ← ofReal_norm,
        Real.enorm_eq_ofReal (mul_nonneg hD0 (hS0 x))]
      refine ENNReal.ofReal_le_ofReal ?_
      refine (norm_iteratedFDeriv_smul_le_const_mul_sum (k := k) hψ (ha.sub hb) hM hm x).trans ?_
      refine le_of_eq ?_
      congr 1
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      congr 1
      exact iteratedFDeriv_sub_apply (ha.contDiffAt.of_le (by simp))
        (hb.contDiffAt.of_le (by simp))
    · have hz : iteratedFDeriv ℝ m (fun y ↦ ψ y • (a y - b y)) x = 0 := by
        have hns : x ∉ tsupport ψ := fun hmem ↦ hx (hψsupp hmem)
        have hev : (fun y ↦ ψ y • (a y - b y)) =ᶠ[𝓝 x] (0 : E → F) := by
          filter_upwards [(isClosed_closure (s := Function.support ψ)).isOpen_compl.mem_nhds hns]
            with y hy
          simp [image_eq_zero_of_notMem_tsupport hy]
        rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev m).self_of_nhds]
        simp
      rw [hz, Set.indicator_of_notMem hx]
      simp [← ofReal_norm]
  calc eLpNorm (iteratedFDeriv ℝ m fun y ↦ ψ y • (a y - b y)) p (μ.restrict W)
      ≤ eLpNorm (iteratedFDeriv ℝ m fun y ↦ ψ y • (a y - b y)) p μ :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ eLpNorm (V.indicator fun y ↦ (((k : ℝ) + 1) * 2 ^ k * M) *
          ∑ s ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ s a y - iteratedFDeriv ℝ s b y‖) p μ :=
        eLpNorm_mono_enorm hpt
    _ = eLpNorm (fun y ↦ (((k : ℝ) + 1) * 2 ^ k * M) *
          ∑ s ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ s a y - iteratedFDeriv ℝ s b y‖) p
          (μ.restrict V) := eLpNorm_indicator_eq_eLpNorm_restrict hV.measurableSet
    _ ≤ ENNReal.ofReal (((k : ℝ) + 1) * 2 ^ k * M) *
          eLpNorm (fun y ↦ ∑ s ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ s a y - iteratedFDeriv ℝ s b y‖) p (μ.restrict V) := by
        have hsm : (fun y ↦ (((k : ℝ) + 1) * 2 ^ k * M) *
              ∑ s ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ s a y - iteratedFDeriv ℝ s b y‖)
            = (((k : ℝ) + 1) * 2 ^ k * M) • fun y ↦ ∑ s ∈ Finset.range (k + 1),
              ‖iteratedFDeriv ℝ s a y - iteratedFDeriv ℝ s b y‖ := rfl
        rw [hsm]
        refine le_trans eLpNorm_const_smul_le (le_of_eq ?_)
        rw [Real.enorm_eq_ofReal hD0]
    _ ≤ ENNReal.ofReal (((k : ℝ) + 1) * 2 ^ k * M) * ∑ s ∈ Finset.range (k + 1),
          eLpNorm (iteratedFDeriv ℝ s a - iteratedFDeriv ℝ s b) p (μ.restrict V) := by
        refine mul_le_mul' le_rfl ?_
        have hSsum : (fun y ↦ ∑ s ∈ Finset.range (k + 1),
              ‖iteratedFDeriv ℝ s a y - iteratedFDeriv ℝ s b y‖)
            = ∑ s ∈ Finset.range (k + 1),
              fun y ↦ ‖iteratedFDeriv ℝ s a y - iteratedFDeriv ℝ s b y‖ := by
          funext y
          simp
        rw [hSsum]
        refine le_trans (eLpNorm_sum_le ?_ hp) (le_of_eq ?_)
        · intro s _
          exact (((ha.continuous_iteratedFDeriv (m := s) (by simp)).sub
            (hb.continuous_iteratedFDeriv (m := s) (by simp))).norm).aestronglyMeasurable
        · exact Finset.sum_congr rfl fun s _ ↦ eLpNorm_norm _

end Piece

/-! ### The patching estimate

The step of the Meyers–Serrin argument in which the pieces are put together: on `U N`, where the
first `N + 1` members of the partition of unity already sum to `1`, the patched function `v` and
any smooth `G` differ by `∑_{j ≤ N} ψ j (g j - G)`, so their derivatives of order `n ≤ k` differ
in `L^p(U N)` by at most the sum of the Leibniz estimates for the pieces. Everything here is a
classical derivative of a smooth function. -/

section Patch

open ContinuousLinearMap

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure]

omit [μ.IsAddHaarMeasure] in
/-- **The patching estimate of the Meyers–Serrin argument.** With `ψ` a partition of unity
subordinate to an exhaustion `U`, `g j` a smooth function attached to the piece `ψ j`, `v` the
patched function `∑ j, ψ j (g j)` and `G` any smooth function, the `L^p(U N)` distance between
`∂^n v` and `∂^n G` is bounded by the pieces' Leibniz estimates against the `L^p` distances from
`∂^s (g j)` and `∂^s G` to the weak derivative `∂^s f`. -/
theorem eLpNorm_iteratedFDeriv_sub_patch_le {U : ℕ → Opens E} {ψ : ℕ → E → ℝ} {M D : ℕ → ℝ}
    {g : ℕ → E → F} {G v : E → F} {δ : ℕ → ℝ≥0∞} {N n : ℕ}
    (hp : 1 ≤ p) (hn : n ≤ k)
    (hUmono : Monotone fun j ↦ (U j : Set E))
    (hUsubΩ : ∀ j, (U j : Set E) ⊆ (Ω : Set E))
    (hψs : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hψsupp : ∀ j, tsupport (ψ j) ⊆ (U (j + 1) : Set E))
    (hψsum : ∀ x ∈ (U N : Set E), ∑ j ∈ Finset.range (N + 1), ψ j x = 1)
    (hMb : ∀ j, ∀ r ≤ k, ∀ x, ‖iteratedFDeriv ℝ r (ψ j) x‖ ≤ M j)
    (hDdef : ∀ j, D j = ((k : ℝ) + 1) * 2 ^ k * M j)
    (hgs : ∀ j, ContDiff ℝ ∞ (g j)) (hGs : ContDiff ℝ ∞ G) (hf : MemSobolev f k p Ω μ)
    (hgA : ∀ j, (∑ s ∈ Finset.range (k + 1),
      eLpNorm (iteratedFDeriv ℝ s (g j) - weakIteratedFDeriv s f Ω μ) p
        (μ.restrict (U (j + 1) : Set E))) ≤ δ j)
    (hviter : ∀ m : ℕ, ∀ x ∈ (U N : Set E), iteratedFDeriv ℝ m v x
      = ∑ j ∈ Finset.range (N + 1), iteratedFDeriv ℝ m (fun y ↦ ψ j y • g j y) x) :
    eLpNorm (iteratedFDeriv ℝ n v - iteratedFDeriv ℝ n G) p (μ.restrict (U N : Set E))
      ≤ ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (D j) * (δ j +
        ∑ s ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ s G - weakIteratedFDeriv s f Ω μ) p
          (μ.restrict (U (N + 1) : Set E))) := by
  have hid : ∀ x ∈ (U N : Set E), iteratedFDeriv ℝ n v x - iteratedFDeriv ℝ n G x
      = ∑ j ∈ Finset.range (N + 1),
        iteratedFDeriv ℝ n (fun y ↦ ψ j y • (g j y - G y)) x := by
    intro x hx
    have hGid : iteratedFDeriv ℝ n G x
        = ∑ j ∈ Finset.range (N + 1), iteratedFDeriv ℝ n (fun y ↦ ψ j y • G y) x := by
      have hev : G =ᶠ[𝓝 x] fun y ↦ ∑ j ∈ Finset.range (N + 1), ψ j y • G y := by
        filter_upwards [(U N).isOpen.mem_nhds hx] with y hy
        rw [← Finset.sum_smul, hψsum y hy, one_smul]
      rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev n).self_of_nhds]
      exact iteratedFDeriv_fun_sum_apply
        fun j _ ↦ (((hψs j).smul hGs).contDiffAt).of_le (by simp)
    rw [hviter n x hx, hGid, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hfun : (fun y ↦ ψ j y • (g j y - G y))
        = (fun y ↦ ψ j y • g j y) - fun y ↦ ψ j y • G y := by
      funext y
      simp [Pi.sub_apply, smul_sub]
    rw [hfun]
    exact (iteratedFDeriv_sub_apply (f := fun y ↦ ψ j y • g j y) (g := fun y ↦ ψ j y • G y)
      (((hψs j).smul (hgs j)).contDiffAt.of_le (by simp))
      (((hψs j).smul hGs).contDiffAt.of_le (by simp))).symm
  have hAE : ∀ j, AEStronglyMeasurable (iteratedFDeriv ℝ n fun y ↦ ψ j y • (g j y - G y))
      (μ.restrict (U N : Set E)) := fun j ↦
    ((((hψs j).smul ((hgs j).sub hGs)).continuous_iteratedFDeriv (m := n)
      (by simp))).aestronglyMeasurable
  have hpiece : ∀ j ∈ Finset.range (N + 1),
      eLpNorm (iteratedFDeriv ℝ n fun y ↦ ψ j y • (g j y - G y)) p
        (μ.restrict (U N : Set E)) ≤ ENNReal.ofReal (D j) * (δ j +
          ∑ s ∈ Finset.range (k + 1),
            eLpNorm (iteratedFDeriv ℝ s G - weakIteratedFDeriv s f Ω μ) p
              (μ.restrict (U (N + 1) : Set E))) := by
    intro j hj
    have hjN : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [hDdef j]
    refine le_trans (eLpNorm_iteratedFDeriv_smul_sub_le (U (j + 1)).isOpen (hψs j)
      (hψsupp j) (hMb j) (hgs j) hGs hp hn) (mul_le_mul' le_rfl ?_)
    refine le_trans (Finset.sum_le_sum (g := fun s ↦
      eLpNorm (iteratedFDeriv ℝ s (g j) - weakIteratedFDeriv s f Ω μ) p
          (μ.restrict (U (j + 1) : Set E))
        + eLpNorm (weakIteratedFDeriv s f Ω μ - iteratedFDeriv ℝ s G) p
          (μ.restrict (U (j + 1) : Set E))) fun s hs ↦ ?_) ?_
    · have hs' : s ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
      have hmw : AEStronglyMeasurable (weakIteratedFDeriv s f Ω μ)
          (μ.restrict (U (j + 1) : Set E)) :=
        ((hf.memLp_weakIteratedFDeriv hs').aestronglyMeasurable).mono_measure
          (Measure.restrict_mono (hUsubΩ (j + 1)) le_rfl)
      have h1 : AEStronglyMeasurable
          (iteratedFDeriv ℝ s (g j) - weakIteratedFDeriv s f Ω μ)
          (μ.restrict (U (j + 1) : Set E)) :=
        ((hgs j).continuous_iteratedFDeriv (m := s) (by simp)).aestronglyMeasurable.sub hmw
      have h2 : AEStronglyMeasurable
          (weakIteratedFDeriv s f Ω μ - iteratedFDeriv ℝ s G)
          (μ.restrict (U (j + 1) : Set E)) :=
        hmw.sub (hGs.continuous_iteratedFDeriv (m := s) (by simp)).aestronglyMeasurable
      have hpteq : eLpNorm (iteratedFDeriv ℝ s (g j) - iteratedFDeriv ℝ s G) p
            (μ.restrict (U (j + 1) : Set E))
          = eLpNorm ((iteratedFDeriv ℝ s (g j) - weakIteratedFDeriv s f Ω μ)
              + (weakIteratedFDeriv s f Ω μ - iteratedFDeriv ℝ s G)) p
            (μ.restrict (U (j + 1) : Set E)) := by
        refine eLpNorm_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
        simp only [Pi.sub_apply, Pi.add_apply]
        abel
      rw [hpteq]
      exact eLpNorm_add_le_of_norm h1 h2 hp
    · rw [Finset.sum_add_distrib]
      refine add_le_add (hgA j) (Finset.sum_le_sum fun s _ ↦ ?_)
      refine le_trans (le_of_eq (eLpNorm_sub_comm _ _ _ _)) ?_
      exact eLpNorm_mono_measure _
        (Measure.restrict_mono (hUmono (by omega : j + 1 ≤ N + 1)) le_rfl)
  calc eLpNorm (iteratedFDeriv ℝ n v - iteratedFDeriv ℝ n G) p (μ.restrict (U N : Set E))
      = eLpNorm (∑ j ∈ Finset.range (N + 1),
          iteratedFDeriv ℝ n fun y ↦ ψ j y • (g j y - G y)) p (μ.restrict (U N : Set E)) := by
        refine eLpNorm_congr_ae ?_
        filter_upwards [self_mem_ae_restrict (U N).isOpen.measurableSet] with x hx
        rw [Pi.sub_apply, hid x hx, Finset.sum_apply]
    _ ≤ ∑ j ∈ Finset.range (N + 1),
        eLpNorm (iteratedFDeriv ℝ n fun y ↦ ψ j y • (g j y - G y)) p
          (μ.restrict (U N : Set E)) := eLpNorm_sum_le_of_norm (fun j _ ↦ hAE j) hp
    _ ≤ _ := Finset.sum_le_sum hpiece

end Patch

/-! ### Meyers–Serrin: `C^∞(Ω) ∩ W^{k,p}(Ω)` is dense in `W^{k,p}(Ω)` -/

section MeyersSerrin

open ContinuousLinearMap

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- An `L^p` bound on every member of a directed family of sets is an `L^p` bound on their
union. -/
theorem MeasureTheory.eLpNorm_restrict_iUnion_le {G : Type*} [NormedAddCommGroup G] {F' : E → G}
    {s : ℕ → Set E} (hd : Directed (· ⊆ ·) s) (hp₀ : p ≠ 0) (hp' : p ≠ ⊤) {c : ℝ≥0∞}
    (h : ∀ N, eLpNorm F' p (μ.restrict (s N)) ≤ c) :
    eLpNorm F' p (μ.restrict (⋃ N, s N)) ≤ c := by
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp'
  refine (ENNReal.rpow_le_rpow_iff hP).1 ?_
  rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm hp₀ hp', setLIntegral_iUnion_of_directed _ hd]
  refine iSup_le fun N ↦ ?_
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm hp₀ hp']
  exact ENNReal.rpow_le_rpow (h N) hP.le

/-- **The Meyers–Serrin theorem, with an explicit tolerance.** For `f ∈ W^{k,p}(Ω)` with
`1 ≤ p < ∞` and `0 ≠ ε ≠ ∞` there is a `v ∈ C^∞(Ω) ∩ W^{k,p}(Ω)` with `‖v - f‖_{k,p,Ω} ≤ ε`.

The construction is the classical one: an exhaustion `U 0 ⊆ U 1 ⊆ …` of `Ω` with a telescoping
smooth partition of unity `ψ 0, ψ 1, …` subordinate to it, and `v = ∑ j, ψ j (g j)` for
mollifications `g j` of `f` chosen fine enough on the piece `U (j+1)` that carries `ψ j`. The sum
is finite on each `U N`, so `v` is smooth on `Ω`.

The estimate compares `v` not with `f` but with a *single* smooth approximation `G i` of `f` on
`U (N+1)`: since `∑_{j ≤ N} ψ j = 1` there, `∂^n v - ∂^n (G i) = ∑_{j ≤ N} ∂^n (ψ j (g j - G i))`
on `U N`, an identity between *classical* derivatives of smooth functions. So only the Leibniz
bound `norm_iteratedFDeriv_smul_le` is used, and no product rule for weak derivatives is needed
anywhere — which is what makes the proof of the size it is. Letting `i → ∞` and then `N → ∞`
finishes. -/
theorem MemSobolev.exists_contDiffOn_sobolevNorm_sub_le (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : MemSobolev f k p Ω μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) (hεtop : ε ≠ ⊤) :
    ∃ v : E → F, ContDiffOn ℝ ∞ v (Ω : Set E) ∧ MemSobolev v k p Ω μ ∧
      sobolevNorm (v - f) k p Ω μ ≤ ε := by
  have hp₀ : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  -- the exhaustion and the partition of unity
  obtain ⟨U, ψ, hUc, hUs, hUΩ, hψs, hψc, hψsupp, hψsum, hψzero⟩ := Ω.exists_partitionOfUnity
  have hUmono : Monotone fun j ↦ (U j : Set E) :=
    monotone_nat_of_le_succ fun j ↦ subset_closure.trans (hUs j)
  have hUsubΩ : ∀ j, (U j : Set E) ⊆ (Ω : Set E) := fun j x hx ↦ by
    rw [← hUΩ]; exact Set.mem_iUnion.2 ⟨j, hx⟩
  have hUclΩ : ∀ j, closure (U j : Set E) ⊆ (Ω : Set E) := fun j ↦ (hUs j).trans (hUsubΩ (j + 1))
  -- the Leibniz constants
  obtain ⟨M, hM0, hMb⟩ : ∃ M : ℕ → ℝ, (∀ j, 0 ≤ M j) ∧
      ∀ j, ∀ r ≤ k, ∀ x, ‖iteratedFDeriv ℝ r (ψ j) x‖ ≤ M j := by
    choose M hM0 hMb using fun j ↦ exists_bound_norm_iteratedFDeriv (hψs j) (hψc j) k
    exact ⟨M, hM0, hMb⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ → ℝ, ∀ j, D j = ((k : ℝ) + 1) * 2 ^ k * M j :=
    ⟨_, fun _ ↦ rfl⟩
  -- the budget
  obtain ⟨ε₁, hε₁def⟩ : ∃ e : ℝ≥0∞, e = ε / ((k : ℝ≥0∞) + 1) := ⟨_, rfl⟩
  have hε₁ : ε₁ ≠ 0 := by rw [hε₁def]; exact (ENNReal.div_pos hε (by simp)).ne'
  have hε₁top : ε₁ ≠ ⊤ := by rw [hε₁def]; exact ENNReal.div_ne_top hεtop (by simp)
  obtain ⟨δ, hδdef⟩ : ∃ d : ℕ → ℝ≥0∞,
      ∀ j, d j = ε₁ / 2 ^ (j + 1) / (ENNReal.ofReal (D j) + 1) := ⟨_, fun _ ↦ rfl⟩
  have hδ : ∀ j, δ j ≠ 0 := fun j ↦ by
    rw [hδdef]
    exact (ENNReal.div_pos (ENNReal.div_pos hε₁ (ENNReal.pow_ne_top (by simp))).ne'
      (by simp [ENNReal.ofReal_ne_top])).ne'
  have hδkey : ∀ j, ENNReal.ofReal (D j) * δ j ≤ ε₁ / 2 ^ (j + 1) := fun j ↦ by
    rw [hδdef]
    calc ENNReal.ofReal (D j) * (ε₁ / 2 ^ (j + 1) / (ENNReal.ofReal (D j) + 1))
        ≤ (ENNReal.ofReal (D j) + 1) * (ε₁ / 2 ^ (j + 1) / (ENNReal.ofReal (D j) + 1)) :=
          mul_le_mul' le_self_add le_rfl
      _ = ε₁ / 2 ^ (j + 1) := ENNReal.mul_div_cancel' (fun h ↦ by simp at h)
          (fun h ↦ by simp [ENNReal.ofReal_ne_top] at h)
  -- the pieces
  obtain ⟨g, hgs, hgA⟩ : ∃ g : ℕ → E → F, (∀ j, ContDiff ℝ ∞ (g j)) ∧ ∀ j,
      (∑ s ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ s (g j) - weakIteratedFDeriv s f Ω μ)
        p (μ.restrict (U (j + 1) : Set E))) ≤ δ j := by
    have hex : ∀ j, ∃ gj : E → F, ContDiff ℝ ∞ gj ∧
        (∑ s ∈ Finset.range (k + 1),
          eLpNorm (iteratedFDeriv ℝ s gj - weakIteratedFDeriv s f Ω μ) p
            (μ.restrict (U (j + 1) : Set E))) ≤ δ j := by
      intro j
      obtain ⟨G, hGs, -, hGt⟩ := hf.exists_seq_contDiff_tendsto_eLpNorm hp hp'
        (U (j + 1)).isOpen (hUc (j + 1)) (hUclΩ (j + 1))
      have hsum : Tendsto (fun i ↦ ∑ s ∈ Finset.range (k + 1),
          eLpNorm (iteratedFDeriv ℝ s (G i) - weakIteratedFDeriv s f Ω μ) p
            (μ.restrict (U (j + 1) : Set E))) atTop (𝓝 0) := by
        have h0 := tendsto_finsetSum (Finset.range (k + 1))
          (fun s hs ↦ hGt s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)))
        simpa using h0
      obtain ⟨i, hi⟩ := (ENNReal.tendsto_nhds_zero.1 hsum (δ j)
        (pos_iff_ne_zero.2 (hδ j))).exists
      exact ⟨G i, hGs i, hi⟩
    choose g hgs hgA using hex
    exact ⟨g, hgs, hgA⟩
  -- the patched function
  obtain ⟨v, hvdef⟩ : ∃ v : E → F, ∀ x, v x = ∑' j, ψ j x • g j x := ⟨_, fun _ ↦ rfl⟩
  have hvloc : ∀ N, ∀ x ∈ (U N : Set E),
      v x = ∑ j ∈ Finset.range (N + 1), ψ j x • g j x := by
    intro N x hx
    rw [hvdef]
    refine tsum_eq_sum fun j hj ↦ ?_
    have hNj : N < j := by simpa [Finset.mem_range, Nat.lt_succ_iff, not_le] using hj
    rw [hψzero N j hNj x hx, zero_smul]
  have hsmoothSum : ∀ N, ContDiff ℝ ∞ fun y ↦ ∑ j ∈ Finset.range (N + 1), ψ j y • g j y :=
    fun N ↦ ContDiff.sum fun j _ ↦ (hψs j).smul (hgs j)
  have hvsmooth : ContDiffOn ℝ ∞ v (Ω : Set E) := by
    intro x hx
    rw [← hUΩ] at hx
    obtain ⟨N, hN⟩ := Set.mem_iUnion.1 hx
    refine ContDiffAt.contDiffWithinAt ?_
    refine (hsmoothSum N).contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [(U N).isOpen.mem_nhds hN] with y hy using hvloc N y hy
  have hviter : ∀ N, ∀ m : ℕ, ∀ x ∈ (U N : Set E), iteratedFDeriv ℝ m v x
      = ∑ j ∈ Finset.range (N + 1), iteratedFDeriv ℝ m (fun y ↦ ψ j y • g j y) x := by
    intro N m x hx
    have hev : v =ᶠ[𝓝 x] fun y ↦ ∑ j ∈ Finset.range (N + 1), ψ j y • g j y := by
      filter_upwards [(U N).isOpen.mem_nhds hx] with y hy using hvloc N y hy
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev m).self_of_nhds]
    exact iteratedFDeriv_fun_sum_apply
      fun j _ ↦ (((hψs j).smul (hgs j)).contDiffAt).of_le (by simp)
  -- the main estimate on each `U N`
  have hmain : ∀ n ≤ k, ∀ N, eLpNorm (iteratedFDeriv ℝ n v - weakIteratedFDeriv n f Ω μ) p
      (μ.restrict (U N : Set E)) ≤ ε₁ := by
    intro n hn N
    obtain ⟨G, hGs, -, hGt⟩ := hf.exists_seq_contDiff_tendsto_eLpNorm hp hp'
      (U (N + 1)).isOpen (hUc (N + 1)) (hUclΩ (N + 1))
    obtain ⟨B, hBdef⟩ : ∃ b : ℕ → ℝ≥0∞, ∀ i, b i = ∑ s ∈ Finset.range (k + 1),
        eLpNorm (iteratedFDeriv ℝ s (G i) - weakIteratedFDeriv s f Ω μ) p
          (μ.restrict (U (N + 1) : Set E)) := ⟨_, fun _ ↦ rfl⟩
    have hB : Tendsto B atTop (𝓝 0) := by
      have h0 := tendsto_finsetSum (Finset.range (k + 1))
        (fun s hs ↦ hGt s (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)))
      have hBfun : B = fun i ↦ ∑ s ∈ Finset.range (k + 1),
          eLpNorm (iteratedFDeriv ℝ s (G i) - weakIteratedFDeriv s f Ω μ) p
            (μ.restrict (U (N + 1) : Set E)) := funext hBdef
      rw [hBfun]
      simpa using h0
    obtain ⟨C, hCdef⟩ : ∃ c : ℝ≥0∞, c = ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (D j) :=
      ⟨_, rfl⟩
    have hCtop : C ≠ ⊤ := by
      rw [hCdef]
      exact ENNReal.sum_ne_top.2 fun j _ ↦ ENNReal.ofReal_ne_top
    have hstep : ∀ i, eLpNorm (iteratedFDeriv ℝ n v - weakIteratedFDeriv n f Ω μ) p
        (μ.restrict (U N : Set E)) ≤ ε₁ + C * B i + B i := by
      intro i
      have hmeas1 : AEStronglyMeasurable
          (iteratedFDeriv ℝ n v - iteratedFDeriv ℝ n (G i)) (μ.restrict (U N : Set E)) := by
        refine AEStronglyMeasurable.sub ?_
          ((hGs i).continuous_iteratedFDeriv (m := n) (by simp)).aestronglyMeasurable
        exact ((hvsmooth.continuousOn_iteratedFDeriv (m := n) (by simp)).mono
          (hUsubΩ N)).aestronglyMeasurable (U N).isOpen.measurableSet
      have hmeas2 : AEStronglyMeasurable
          (iteratedFDeriv ℝ n (G i) - weakIteratedFDeriv n f Ω μ)
          (μ.restrict (U N : Set E)) := by
        refine AEStronglyMeasurable.sub
          ((hGs i).continuous_iteratedFDeriv (m := n) (by simp)).aestronglyMeasurable ?_
        exact ((hf.memLp_weakIteratedFDeriv hn).aestronglyMeasurable).mono_measure
          (Measure.restrict_mono (hUsubΩ N) le_rfl)
      have hsplit : (iteratedFDeriv ℝ n v - weakIteratedFDeriv n f Ω μ)
          = (iteratedFDeriv ℝ n v - iteratedFDeriv ℝ n (G i))
            + (iteratedFDeriv ℝ n (G i) - weakIteratedFDeriv n f Ω μ) := by
        funext x
        simp only [Pi.sub_apply, Pi.add_apply]
        abel
      rw [hsplit]
      refine (eLpNorm_add_le_of_norm hmeas1 hmeas2 hp).trans (add_le_add ?_ ?_)
      · refine le_trans (eLpNorm_iteratedFDeriv_sub_patch_le hp hn hUmono hUsubΩ hψs hψsupp
          (hψsum N) hMb hDdef hgs (hGs i) hf hgA (hviter N)) ?_
        rw [← hBdef i]
        calc ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (D j) * (δ j + B i)
            = (∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (D j) * δ j) + C * B i := by
              rw [hCdef, Finset.sum_mul, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun j _ ↦ mul_add _ _ _
          _ ≤ ε₁ + C * B i :=
              add_le_add (le_trans (Finset.sum_le_sum fun j _ ↦ hδkey j)
                (ENNReal.sum_range_div_two_pow_succ_le ε₁ (N + 1))) le_rfl
      · rw [hBdef i]
        refine le_trans (eLpNorm_mono_measure _
          (Measure.restrict_mono (hUmono (Nat.le_succ N)) le_rfl)) ?_
        exact Finset.single_le_sum (f := fun s ↦ eLpNorm
          (iteratedFDeriv ℝ s (G i) - weakIteratedFDeriv s f Ω μ) p
            (μ.restrict (U (N + 1) : Set E))) (fun _ _ ↦ zero_le)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
    have hlim : Tendsto (fun i ↦ ε₁ + C * B i + B i) atTop (𝓝 ε₁) := by
      have h0 : Tendsto (fun i ↦ ε₁ + C * B i + B i) atTop (𝓝 (ε₁ + C * 0 + 0)) :=
        (tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hB (Or.inr hCtop))).add hB
      simpa using h0
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall hstep)
  -- from `U N` to `Ω`
  have hΩ : ∀ n ≤ k, eLpNorm (iteratedFDeriv ℝ n v - weakIteratedFDeriv n f Ω μ) p
      (μ.restrict (Ω : Set E)) ≤ ε₁ := by
    intro n hn
    rw [← hUΩ]
    exact MeasureTheory.eLpNorm_restrict_iUnion_le hUmono.directed_le hp₀ hp' (hmain n hn)
  -- `v` and its derivatives lie in `L^p(Ω)`
  have hvw : ∀ n ≤ k, HasWeakIteratedFDerivOn n (v - f)
      (iteratedFDeriv ℝ n v - weakIteratedFDeriv n f Ω μ) Ω μ := fun n hn ↦
    (ContDiffOn.hasWeakIteratedFDerivOn hvsmooth (by simp)).sub (hf.hasWeakIteratedFDerivOn hn)
  have hvmeas : ∀ m : ℕ, AEStronglyMeasurable (iteratedFDeriv ℝ m v)
      (μ.restrict (Ω : Set E)) := fun m ↦
    (hvsmooth.continuousOn_iteratedFDeriv (m := m) (by simp)).aestronglyMeasurable
      Ω.isOpen.measurableSet
  have hdiffLp : ∀ n ≤ k, MemLp (iteratedFDeriv ℝ n v - weakIteratedFDeriv n f Ω μ) p
      (μ.restrict (Ω : Set E)) := fun n hn ↦
    ⟨(hvmeas n).sub (hf.memLp_weakIteratedFDeriv hn).aestronglyMeasurable,
      lt_of_le_of_lt (hΩ n hn) (lt_top_iff_ne_top.2 hε₁top)⟩
  have hviterLp : ∀ n ≤ k, MemLp (iteratedFDeriv ℝ n v) p (μ.restrict (Ω : Set E)) :=
    fun n hn ↦ by
      have h := (hdiffLp n hn).add_of_norm (hf.memLp_weakIteratedFDeriv hn)
      have he : (iteratedFDeriv ℝ n v - weakIteratedFDeriv n f Ω μ) + weakIteratedFDeriv n f Ω μ
          = iteratedFDeriv ℝ n v := by
        funext x
        simp only [Pi.add_apply, Pi.sub_apply]
        abel
      rwa [he] at h
  -- the order-zero case, read on the functions themselves
  have hzeroNorm : eLpNorm (v - f) p (μ.restrict (Ω : Set E)) ≤ ε₁ := by
    refine le_trans (le_of_eq (eLpNorm_congr_norm_ae ?_)) (hΩ 0 (Nat.zero_le k))
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).2
      ((hasWeakIteratedFDerivOn_zero (hf.memLp.locallyIntegrableOn hp)).weakIteratedFDeriv_ae_eq
        (μ := μ))] with x hx
    rw [Pi.sub_apply, Pi.sub_apply, hx, iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp_apply]
    rw [← map_sub]
    exact (LinearIsometryEquiv.norm_map _ _).symm
  have hvfLp : MemLp (v - f) p (μ.restrict (Ω : Set E)) :=
    ⟨(hvsmooth.continuousOn.aestronglyMeasurable Ω.isOpen.measurableSet).sub
      hf.memLp.aestronglyMeasurable, lt_of_le_of_lt hzeroNorm (lt_top_iff_ne_top.2 hε₁top)⟩
  have hvLp : MemLp v p (μ.restrict (Ω : Set E)) := by
    have h := hvfLp.add hf.memLp
    have he : (v - f) + f = v := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      abel
    rwa [he] at h
  refine ⟨v, hvsmooth, ⟨hvLp, fun m hm ↦ ⟨iteratedFDeriv ℝ m v,
    ContDiffOn.hasWeakIteratedFDerivOn hvsmooth (by simp), hviterLp m (Nat.cast_le.1 hm)⟩⟩, ?_⟩
  refine le_trans (sobolevNorm_le_of_forall_eLpNorm_le hp hp' (c := ε₁) fun m hm ↦ ?_) ?_
  · rw [(hvw m hm).eLpNorm_weakIteratedFDeriv]
    exact hΩ m hm
  · rw [hε₁def]
    exact le_of_eq (ENNReal.mul_div_cancel' (fun h ↦ by simp at h) (fun h ↦ by simp at h))

/-- **The Meyers–Serrin theorem, `H = W`.** For `1 ≤ p < ∞`, every function of `W^{k,p}(Ω)` is the
limit, in the Sobolev norm of order `k`, of a sequence of functions that are smooth on `Ω` and lie
in `W^{k,p}(Ω)`; that is, `C^∞(Ω) ∩ W^{k,p}(Ω)` is dense in `W^{k,p}(Ω)`.

This is the theorem of N. G. Meyers and J. Serrin, *H = W*, Proceedings of the National Academy of
Sciences of the United States of America **51** (1964), 1055–1056; it is Theorem 7.3.1 of Kendall
Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd
edition, Springer, 2009. No regularity of the boundary of `Ω` is assumed, and none is available:
the approximating functions are smooth in the interior only. -/
theorem MemSobolev.exists_seq_contDiffOn_tendsto_sobolevNorm (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : MemSobolev f k p Ω μ) :
    ∃ v : ℕ → E → F, (∀ i, ContDiffOn ℝ ∞ (v i) (Ω : Set E)) ∧ (∀ i, MemSobolev (v i) k p Ω μ) ∧
      Tendsto (fun i ↦ sobolevNorm (v i - f) k p Ω μ) atTop (𝓝 0) := by
  have key : ∀ ε : ℝ≥0∞, ε ≠ 0 → ε ≠ ⊤ → ∃ v : E → F, ContDiffOn ℝ ∞ v (Ω : Set E) ∧
      MemSobolev v k p Ω μ ∧ sobolevNorm (v - f) k p Ω μ ≤ ε := fun ε hε hεtop ↦
    hf.exists_contDiffOn_sobolevNorm_sub_le hp hp' hε hεtop
  choose! V hV1 hV2 hV3 using key
  have hne : ∀ i : ℕ, ((i : ℝ≥0∞) + 1)⁻¹ ≠ 0 := fun i ↦ ENNReal.inv_ne_zero.2 (by simp)
  have hnetop : ∀ i : ℕ, ((i : ℝ≥0∞) + 1)⁻¹ ≠ ⊤ := fun i ↦ ENNReal.inv_ne_top.2 (by simp)
  have hlim : Tendsto (fun i : ℕ ↦ ((i : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ zero_le)
      (fun i ↦ ENNReal.inv_le_inv.2 le_self_add)
  refine ⟨fun i ↦ V ((i : ℝ≥0∞) + 1)⁻¹, fun i ↦ hV1 _ (hne i) (hnetop i),
    fun i ↦ hV2 _ (hne i) (hnetop i), ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le)
    (fun i ↦ hV3 _ (hne i) (hnetop i))

end MeyersSerrin
