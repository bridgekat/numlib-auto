/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the Bessel potential spaces on the
whole space that already live there.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.WeakDeriv

/-!
# Sobolev spaces of integer order on an open set

`MemSobolev f k p Ω μ` says that `f` belongs to the Sobolev space `W^{k,p}(Ω)` of Atkinson and Han,
*Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition, Definition 7.2.2:
`f` lies in `L^p(Ω)` and, for every order `n ≤ k`, the weak derivative of order `n` exists on `Ω`
and lies in `L^p(Ω)` too. `sobolevNorm f k p Ω μ` is the accompanying norm.
`Numlib/Analysis/Sobolev/Space.lean` carries the same space as a *type*, `Sobolev F k p Ω μ`, whose
norm is `sobolevNorm` and which is a Banach space.

Mathlib's `Mathlib/Analysis/Distribution/Sobolev.lean` is a different subject: the Bessel potential
spaces `H^{s,p}` of tempered distributions on the *whole* space, with no domain in sight.

## Main definitions

* `MemSobolev f k p Ω μ`, membership of `W^{k,p}(Ω)`;
* `weakIteratedFDeriv n f Ω μ`, a choice of weak derivative of order `n`, or `0` when there is
  none; it is determined almost everywhere on `Ω` by
  `HasWeakIteratedFDerivOn.weakIteratedFDeriv_ae_eq`;
* `sobolevNorm f k p Ω μ` and `sobolevSeminorm f k p Ω μ`, the norm and seminorm of
  Atkinson–Han, Definition 7.2.2.

## Main statements

* `MemSobolev.congr_ae`: membership only sees the function up to a null set of `Ω`;
* `MemSobolev.mono_order`, `MemSobolev.mono_set` and `MemSobolev.mono_exponent`: `W^{k,p}(Ω)`
  decreases in `k`, is inherited by open subsets, and increases as `p` decreases on a set of finite
  measure;
* `memSobolev_zero_order`: `W^{0,p}(Ω) = L^p(Ω)`;
* `MemSobolev.add`, `.const_smul`, `.neg`, `.sub` and `memSobolev_zero`: `W^{k,p}(Ω)` is a linear
  subspace of `L^p(Ω)`.

## Implementation notes

This file, like `Numlib/Analysis/Sobolev/WeakDeriv.lean`, stands in for Mathlib PR 32305 and its
continuation `grunweg/SobolevSlobodeckij` (Michael Rothgang, Filippo Nuccio and Floris van Doorn),
whose `MemSobolev` and `sobolevNorm` this follows in name and in argument order so that migrating
is a rename.

Derivatives of order `n` are collected into a single `ContinuousMultilinearMap`-valued function
rather than indexed by multi-indices, so `sobolevNorm` sums the `L^p` norms of the derivative
*tensors*, each measured in the operator norm, over the orders `n ≤ k`. Atkinson–Han instead sum
over the multi-indices `α` with `|α| ≤ k`. The two norms are equivalent — on `ℝ^d` the operator
norm of a symmetric `n`-tensor is comparable to any norm on its finitely many entries — but they
are not equal, so `sobolevNorm` is not literally the displayed formula of Definition 7.2.2. A
consequence is that `sobolevNorm f k 2 Ω μ` is not an inner-product norm, since the operator norm
on multilinear maps is not; Atkinson–Han's Corollary 7.2.4, that `H^k(Ω)` is a Hilbert space, is
therefore not available in this formulation and would need the multi-index indexing — see the
implementation notes of `Numlib/Analysis/Sobolev/Space.lean`, where the completeness of Theorem
7.2.3 is proved and this is the one thing that stands between it and the corollary.
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped Distributions ENNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} {n : ℕ} {k : ℕ∞} {p : ℝ≥0∞} {f : E → F}

/-! ### Preliminaries -/

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A function of `L^p(Ω)`, for `1 ≤ p`, is locally integrable on `Ω`. -/
theorem MeasureTheory.MemLp.locallyIntegrableOn [OpensMeasurableSpace E] [IsLocallyFiniteMeasure μ]
    (hf : MemLp f p (μ.restrict Ω)) (hp : 1 ≤ p) : LocallyIntegrableOn f (Ω : Set E) μ :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable hp)

/-- Every locally integrable function has a weak derivative of order `0`, namely itself. -/
theorem hasWeakIteratedFDerivOn_zero (hf : LocallyIntegrableOn f (Ω : Set E) μ) :
    HasWeakIteratedFDerivOn 0 f
      (fun x ↦ (continuousMultilinearCurryFin0 ℝ E F).symm (f x)) Ω μ where
  locallyIntegrableOn := hf
  locallyIntegrableOn_weakDeriv := hf.comp_continuousLinearMap
    (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
  integral_smul_eq φ y := by simp

/-! ### Membership of `W^{k,p}(Ω)` -/

/-- `MemSobolev f k p Ω μ` says that `f` belongs to the Sobolev space `W^{k,p}(Ω)`: it lies in
`L^p(Ω)` and, for every order `n ≤ k`, it has a weak derivative of order `n` on `Ω` which lies in
`L^p(Ω)` as well. This is Atkinson and Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Definition 7.2.2; a tuple of `n` directions plays the role of a
multi-index `α` with `|α| = n`. -/
def MemSobolev (f : E → F) (k : ℕ∞) (p : ℝ≥0∞) (Ω : Opens E) (μ : Measure E) : Prop :=
  MemLp f p (μ.restrict Ω) ∧ ∀ n : ℕ, (n : ℕ∞) ≤ k →
    ∃ w : E → E [×n]→L[ℝ] F, HasWeakIteratedFDerivOn n f w Ω μ ∧ MemLp w p (μ.restrict Ω)

namespace MemSobolev

/-- A function of `W^{k,p}(Ω)` lies in `L^p(Ω)`. -/
theorem memLp (h : MemSobolev f k p Ω μ) : MemLp f p (μ.restrict Ω) := h.1

/-- A function of `W^{k,p}(Ω)` has, for every order `n ≤ k`, a weak derivative of order `n`
in `L^p(Ω)`. -/
theorem exists_hasWeakIteratedFDerivOn (h : MemSobolev f k p Ω μ) (hn : (n : ℕ∞) ≤ k) :
    ∃ w : E → E [×n]→L[ℝ] F, HasWeakIteratedFDerivOn n f w Ω μ ∧ MemLp w p (μ.restrict Ω) :=
  h.2 n hn

/-- Membership of `W^{k,p}(Ω)` only sees the function up to a null set of `Ω`. -/
theorem congr_ae {f' : E → F} (h : MemSobolev f k p Ω μ)
    (hf : f =ᵐ[μ.restrict (Ω : Set E)] f') : MemSobolev f' k p Ω μ := by
  refine ⟨h.1.ae_eq hf, fun n hn ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.2 n hn
  exact ⟨w, hw.congr_ae hf (Filter.EventuallyEq.refl _ _), hwp⟩

/-- `W^{k,p}(Ω)` decreases as the order `k` increases. -/
theorem mono_order {k' : ℕ∞} (h : MemSobolev f k p Ω μ) (hk : k' ≤ k) : MemSobolev f k' p Ω μ :=
  ⟨h.1, fun n hn ↦ h.2 n (hn.trans hk)⟩

/-- Membership of `W^{k,p}` is inherited by open subsets. -/
theorem mono_set [OpensMeasurableSpace E] {Ω' : Opens E} (h : MemSobolev f k p Ω μ)
    (hΩ : Ω' ≤ Ω) : MemSobolev f k p Ω' μ := by
  refine ⟨h.1.mono_measure (Measure.restrict_mono hΩ le_rfl), fun n hn ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.2 n hn
  exact ⟨w, hw.mono hΩ, hwp.mono_measure (Measure.restrict_mono hΩ le_rfl)⟩

/-- On a set of finite measure, `W^{k,p}(Ω)` increases as the exponent `p` decreases. -/
theorem mono_exponent {q : ℝ≥0∞} (h : MemSobolev f k p Ω μ) (hpq : q ≤ p)
    (hΩ : μ (Ω : Set E) ≠ ⊤) : MemSobolev f k q Ω μ := by
  have : IsFiniteMeasure (μ.restrict (Ω : Set E)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hΩ⟩
  refine ⟨h.1.mono_exponent hpq, fun n hn ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.2 n hn
  exact ⟨w, hw, hwp.mono_exponent hpq⟩

end MemSobolev

/-- `W^{0,p}(Ω)` is `L^p(Ω)`: Atkinson and Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Definition 7.2.2 with `k = 0`. -/
theorem memSobolev_zero_order [OpensMeasurableSpace E] [IsLocallyFiniteMeasure μ] (hp : 1 ≤ p) :
    MemSobolev f 0 p Ω μ ↔ MemLp f p (μ.restrict Ω) := by
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun n hn ↦ ?_⟩⟩
  obtain rfl : n = 0 := by exact_mod_cast le_antisymm hn (Nat.cast_le.2 n.zero_le)
  refine ⟨_, hasWeakIteratedFDerivOn_zero (h.locallyIntegrableOn hp), ?_⟩
  exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    |>.comp_memLp' h

/-! ### The linear structure -/

section Linear

variable [OpensMeasurableSpace E]

omit [OpensMeasurableSpace E] in
/-- The zero function lies in every `W^{k,p}(Ω)`. -/
theorem memSobolev_zero : MemSobolev (0 : E → F) k p Ω μ :=
  ⟨MemLp.zero, fun n _ ↦ ⟨(0 : E → E [×n]→L[ℝ] F), HasWeakIteratedFDerivOn.zero, MemLp.zero⟩⟩

namespace MemSobolev

/-- `W^{k,p}(Ω)` is closed under addition. -/
protected theorem add {f₁ f₂ : E → F} (h₁ : MemSobolev f₁ k p Ω μ) (h₂ : MemSobolev f₂ k p Ω μ) :
    MemSobolev (f₁ + f₂) k p Ω μ := by
  refine ⟨h₁.1.add h₂.1, fun n hn ↦ ?_⟩
  obtain ⟨w₁, hw₁, hw₁p⟩ := h₁.2 n hn
  obtain ⟨w₂, hw₂, hw₂p⟩ := h₂.2 n hn
  exact ⟨w₁ + w₂, hw₁.add hw₂, hw₁p.add hw₂p⟩

omit [OpensMeasurableSpace E] in
/-- `W^{k,p}(Ω)` is closed under scalar multiplication. -/
protected theorem const_smul (h : MemSobolev f k p Ω μ) (c : ℝ) :
    MemSobolev (c • f) k p Ω μ := by
  refine ⟨h.1.const_smul c, fun n hn ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.2 n hn
  exact ⟨c • w, hw.const_smul c, hwp.const_smul c⟩

omit [OpensMeasurableSpace E] in
/-- `W^{k,p}(Ω)` is closed under negation. -/
protected theorem neg (h : MemSobolev f k p Ω μ) : MemSobolev (-f) k p Ω μ := by
  refine ⟨h.1.neg, fun n hn ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.2 n hn
  exact ⟨-w, hw.neg, hwp.neg⟩

/-- `W^{k,p}(Ω)` is closed under subtraction. -/
protected theorem sub {f₁ f₂ : E → F} (h₁ : MemSobolev f₁ k p Ω μ) (h₂ : MemSobolev f₂ k p Ω μ) :
    MemSobolev (f₁ - f₂) k p Ω μ := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

end MemSobolev

end Linear

/-! ### The Sobolev norm -/

open Classical in
/-- A choice of weak derivative of order `n` of `f` on `Ω`, and `0` when `f` has none. It is
determined almost everywhere on `Ω` by `HasWeakIteratedFDerivOn.weakIteratedFDeriv_ae_eq`. -/
noncomputable def weakIteratedFDeriv (n : ℕ) (f : E → F) (Ω : Opens E) (μ : Measure E) :
    E → E [×n]→L[ℝ] F :=
  if h : ∃ w, HasWeakIteratedFDerivOn n f w Ω μ then h.choose else 0

/-- If `f` has any weak derivative of order `n` on `Ω`, then the chosen one is one. -/
theorem HasWeakIteratedFDerivOn.hasWeakIteratedFDerivOn_weakIteratedFDeriv
    {w : E → E [×n]→L[ℝ] F} (h : HasWeakIteratedFDerivOn n f w Ω μ) :
    HasWeakIteratedFDerivOn n f (weakIteratedFDeriv n f Ω μ) Ω μ := by
  rw [weakIteratedFDeriv]
  split
  · exact Exists.choose_spec ‹_›
  · exact absurd (⟨w, h⟩ : ∃ w, HasWeakIteratedFDerivOn n f w Ω μ) ‹_›

/-- The chosen weak derivative agrees almost everywhere on `Ω` with any weak derivative. -/
theorem HasWeakIteratedFDerivOn.weakIteratedFDeriv_ae_eq [FiniteDimensional ℝ E] [BorelSpace E]
    [CompleteSpace F] {w : E → E [×n]→L[ℝ] F} (h : HasWeakIteratedFDerivOn n f w Ω μ) :
    ∀ᵐ x ∂μ, x ∈ (Ω : Set E) → weakIteratedFDeriv n f Ω μ x = w x :=
  h.hasWeakIteratedFDerivOn_weakIteratedFDeriv.ae_eq h

/-- The norm of `W^{k,p}(Ω)`: Atkinson and Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Definition 7.2.2, with the derivatives of each order collected
into one tensor rather than indexed by multi-indices — see the implementation notes of this
file. -/
noncomputable def sobolevNorm (f : E → F) (k : ℕ) (p : ℝ≥0∞) (Ω : Opens E) (μ : Measure E) :
    ℝ≥0∞ :=
  if p = ⊤ then ⨆ n : Fin (k + 1), eLpNorm (weakIteratedFDeriv n f Ω μ) ⊤ (μ.restrict Ω)
  else (∑ n : Fin (k + 1), eLpNorm (weakIteratedFDeriv n f Ω μ) p (μ.restrict Ω) ^ p.toReal)
    ^ (1 / p.toReal)

/-- The seminorm of `W^{k,p}(Ω)`, built from the derivatives of top order alone: Atkinson and Han,
*Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition, Definition 7.2.2. -/
noncomputable def sobolevSeminorm (f : E → F) (k : ℕ) (p : ℝ≥0∞) (Ω : Opens E) (μ : Measure E) :
    ℝ≥0∞ :=
  eLpNorm (weakIteratedFDeriv k f Ω μ) p (μ.restrict Ω)
