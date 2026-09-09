/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the Bessel potential spaces on the
whole space that already live there.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.WeakDeriv

/-!
# Sobolev spaces of integer order on an open set, and the regularity of its boundary

`MemSobolev f k p Ω μ` says that `f` belongs to the Sobolev space `W^{k,p}(Ω)` of Atkinson and Han,
*Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition, Definition 7.2.2:
`f` lies in `L^p(Ω)` and, for every order `n ≤ k`, the weak derivative of order `n` exists on `Ω`
and lies in `L^p(Ω)` too. `sobolevNorm f k p Ω μ` is the accompanying norm.
`Numlib/Analysis/Sobolev/Space.lean` carries the same space as a *type*, `Sobolev F k p Ω μ`, whose
norm is `sobolevNorm` and which is a Banach space.

Mathlib's `Mathlib/Analysis/Distribution/Sobolev.lean` is a different subject: the Bessel potential
spaces `H^{s,p}` of tempered distributions on the *whole* space, with no domain in sight.

The last section of this file is about the *domain* rather than the space: `IsBoundaryOfClass V Ω`
says that the boundary of `Ω ⊆ ℝ^{d+1}` is locally, after a rigid motion of the coordinates, the
graph of a function of the class `V`, with `Ω` lying on one side of it. It is Definition 7.2.1 of
the same source, and it is the hypothesis under which the structure theory of Sobolev spaces on a
domain — extension, density up to the boundary, the trace — is stated.

## Main definitions

* `MemSobolev f k p Ω μ`, membership of `W^{k,p}(Ω)`;
* `weakIteratedFDeriv n f Ω μ`, a choice of weak derivative of order `n`, or `0` when there is
  none; it is determined almost everywhere on `Ω` by
  `HasWeakIteratedFDerivOn.weakIteratedFDeriv_ae_eq`;
* `sobolevNorm f k p Ω μ` and `sobolevSeminorm f k p Ω μ`, the norm and seminorm of
  Atkinson–Han, Definition 7.2.2;
* `IsBoundaryOfClass V Ω`, the regularity of the boundary of a domain `Ω ⊆ ℝ^{d+1}` measured by a
  class `V` of functions of `d` variables, and its two named instances `IsLipschitzDomain` and
  `IsContDiffDomain`.

## Main statements

* `MemSobolev.congr_ae`: membership only sees the function up to a null set of `Ω`;
* `MemSobolev.mono_order`, `MemSobolev.mono_set` and `MemSobolev.mono_exponent`: `W^{k,p}(Ω)`
  decreases in `k`, is inherited by open subsets, and increases as `p` decreases on a set of finite
  measure;
* `memSobolev_zero_order`: `W^{0,p}(Ω) = L^p(Ω)`;
* `MemSobolev.add`, `.const_smul`, `.neg`, `.sub` and `memSobolev_zero`: `W^{k,p}(Ω)` is a linear
  subspace of `L^p(Ω)`;
* `IsBoundaryOfClass.exists_finite_cover`: the boundary of a bounded set of class `V` is covered by
  finitely many balls in each of which it is a graph.

## Implementation notes

This file, like `Numlib/Analysis/Sobolev/WeakDeriv.lean`, stands in for Mathlib PR 32305 and its
continuation `grunweg/SobolevSlobodeckij` (Michael Rothgang, Filippo Nuccio and Floris van Doorn),
whose `MemSobolev` and `sobolevNorm` this follows in name and in argument order so that migrating
is a rename.

The boundary regularity of the last section is *not* part of that: PR 32305 works over an
arbitrary open set and introduces no condition on `∂Ω`, and Mathlib has no `IsLipschitzDomain`,
`IsBoundaryOfClass` or `EuclideanSpace.init` under those or any neighbouring names. So the two
halves of this file migrate independently — the `MemSobolev` half by a rename, the boundary half
not at all — and there is no name to avoid. Should the section grow, splitting it into a file of
its own would cost nothing, nothing above it depending on it.

Derivatives of order `n` are collected into a single `ContinuousMultilinearMap`-valued function
rather than indexed by multi-indices, so `sobolevNorm` sums the `L^p` norms of the derivative
*tensors*, each measured in the operator norm, over the orders `n ≤ k`. Atkinson–Han instead sum
over the multi-indices `α` with `|α| ≤ k`. The two norms are equivalent — on `ℝ^d` the operator
norm of a symmetric `n`-tensor is comparable to any norm on its finitely many entries — but they
are not equal, so `sobolevNorm` is not literally the displayed formula of Definition 7.2.2. A
consequence is that for `k ≥ 2` and `dim E ≥ 2` the norm `sobolevNorm f k 2 Ω μ` is not an
inner-product norm, the operator norm on multilinear maps of order `n ≥ 2` on a space of
dimension at least `2` not being one; for `k ≤ 1` or `dim E ≤ 1` it is.
`Numlib/Analysis/Sobolev/MultiIndex.lean` carries the multi-index indexing, and hence the book's
own norm and, at `p = 2`, its inner product; `MemSobolev.memSobolevMultiIndex` is the comparison.
Nothing there is needed for the space, the norm or the completeness proved from this file; it is
needed for `H^k(Ω)` to be a *Hilbert* space,
Atkinson–Han's Corollary 7.2.4.
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

/-! ### Regularity of the boundary -/

section Boundary

variable {d : ℕ} {V : Set (EuclideanSpace ℝ (Fin d) → ℝ)}
  {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))}

/-- The first `d` coordinates `(x_1, …, x_d)` of a point `x` of `ℝ^{d+1}`, as a point of `ℝ^d`.
This is `Fin.init` read between Euclidean spaces; it is the projection along which the boundary of
a domain is written as a graph in `IsBoundaryGraphAt`. -/
def EuclideanSpace.init (x : EuclideanSpace ℝ (Fin (d + 1))) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i ↦ x i.castSucc

/-- The coordinates of `EuclideanSpace.init x` are the first `d` coordinates of `x`. -/
@[simp]
theorem EuclideanSpace.init_apply (x : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin d) :
    EuclideanSpace.init x i = x i.castSucc :=
  rfl

/-- `IsBoundaryGraphAt V Ω x₀ r` says that, in the ball of radius `r` about `x₀` and after a rigid
motion `T` of the coordinate system, the set `Ω ⊆ ℝ^{d+1}` is the region lying strictly above the
graph of some `g ∈ V`:
`Ω ∩ B(x₀, r) = {x ∈ B(x₀, r) : x_{d+1} > g (x_1, …, x_d)}` in the coordinates `T x`.

This is the local condition of Atkinson and Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Definition 7.2.1, with the radius named so that a covering of
the boundary by such balls can be spoken of; `IsBoundaryOfClass` quantifies it over the
boundary. -/
def IsBoundaryGraphAt (V : Set (EuclideanSpace ℝ (Fin d) → ℝ))
    (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) (x₀ : EuclideanSpace ℝ (Fin (d + 1))) (r : ℝ) :
    Prop :=
  ∃ T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)), ∃ g ∈ V,
    Ω ∩ Metric.ball x₀ r =
      {x ∈ Metric.ball x₀ r | g (EuclideanSpace.init (T x)) < T x (Fin.last d)}

/-- **The boundary `∂Ω` is of class `V`**: every boundary point of `Ω ⊆ ℝ^{d+1}` has a ball in
which `Ω` is, after a rigid motion of the coordinate system, the region strictly above the graph of
some function `g` of the class `V` of functions on `ℝ^d`.

This is Atkinson and Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd
edition, Definition 7.2.1, whose `Ω` is open and bounded; neither hypothesis is imposed here, and
both are carried by the results that need them (`IsBoundaryOfClass.exists_finite_cover` asks for
boundedness). Taking `V` to be the Lipschitz functions gives a Lipschitz domain,
`IsLipschitzDomain`, and taking it to be the `C^n` functions a `C^n` domain, `IsContDiffDomain`;
taking it to be the `C^{k,α}` functions gives a Hölder boundary of class `C^{k,α}`. -/
def IsBoundaryOfClass (V : Set (EuclideanSpace ℝ (Fin d) → ℝ))
    (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) : Prop :=
  ∀ x₀ ∈ frontier Ω, ∃ r > 0, IsBoundaryGraphAt V Ω x₀ r

/-- **A Lipschitz domain**: an open set of `ℝ^{d+1}` whose boundary is, locally and after a rigid
motion of the coordinate system, the graph of a Lipschitz continuous function of `d` variables,
with the set lying on one side of it. This is `IsBoundaryOfClass` for the class of Lipschitz
functions, which is Atkinson and Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Definition 7.2.1. Boundedness, which that source assumes throughout, is
*not* part of this definition: a hypothesis `Bornology.IsBounded Ω` is written beside it where it
is needed, as in the phrase "bounded Lipschitz domain". -/
def IsLipschitzDomain (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) : Prop :=
  IsOpen Ω ∧ IsBoundaryOfClass {g | ∃ K, LipschitzWith K g} Ω

/-- **A `C^n` domain**: an open set of `ℝ^{d+1}` whose boundary is, locally and after a rigid
motion of the coordinate system, the graph of a `C^n` function of `d` variables, with the set lying
on one side of it. This is `IsBoundaryOfClass` for the class of `C^n` functions, which is Atkinson
and Han, *Theoretical Numerical Analysis: A Functional Analysis Framework*, 3rd edition,
Definition 7.2.1. As for `IsLipschitzDomain`, boundedness is not part of the definition. -/
def IsContDiffDomain (n : WithTop ℕ∞) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) : Prop :=
  IsOpen Ω ∧ IsBoundaryOfClass {g | ContDiff ℝ n g} Ω

/-- A Lipschitz domain is open. -/
theorem IsLipschitzDomain.isOpen (h : IsLipschitzDomain Ω) : IsOpen Ω := h.1

/-- The boundary of a Lipschitz domain is locally the graph of a Lipschitz function. -/
theorem IsLipschitzDomain.isBoundaryOfClass (h : IsLipschitzDomain Ω) :
    IsBoundaryOfClass {g | ∃ K, LipschitzWith K g} Ω := h.2

/-- A `C^n` domain is open. -/
theorem IsContDiffDomain.isOpen {n : WithTop ℕ∞} (h : IsContDiffDomain n Ω) : IsOpen Ω := h.1

/-- The boundary of a `C^n` domain is locally the graph of a `C^n` function. -/
theorem IsContDiffDomain.isBoundaryOfClass {n : WithTop ℕ∞} (h : IsContDiffDomain n Ω) :
    IsBoundaryOfClass {g | ContDiff ℝ n g} Ω := h.2

/-- The local graph condition grows with the class `V` of graph functions. -/
theorem IsBoundaryGraphAt.mono {V' : Set (EuclideanSpace ℝ (Fin d) → ℝ)} (hV : V ⊆ V')
    {x₀ : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ} (h : IsBoundaryGraphAt V Ω x₀ r) :
    IsBoundaryGraphAt V' Ω x₀ r :=
  let ⟨T, g, hg, hgraph⟩ := h
  ⟨T, g, hV hg, hgraph⟩

/-- The condition that `∂Ω` be of class `V` grows with the class `V` of graph functions. -/
theorem IsBoundaryOfClass.mono {V' : Set (EuclideanSpace ℝ (Fin d) → ℝ)} (hV : V ⊆ V')
    (h : IsBoundaryOfClass V Ω) : IsBoundaryOfClass V' Ω :=
  fun x₀ hx₀ ↦ let ⟨r, hr, hgraph⟩ := h x₀ hx₀; ⟨r, hr, hgraph.mono hV⟩

/-- **A bounded set whose boundary is of class `V` has its boundary covered by finitely many balls
in which it is a graph**: there are finitely many points `x_i` of `∂Ω` and radii `r_i > 0` with
`∂Ω ⊆ ⋃ i, B(x_i, r_i)` and with `Ω ∩ B(x_i, r_i)` the region above the graph of some `g_i ∈ V`.
This is the remark following Atkinson and Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Definition 7.2.1, and it is the form in which that definition is
used; `∂Ω` is compact because `Ω` is bounded. -/
theorem IsBoundaryOfClass.exists_finite_cover (hΩ : Bornology.IsBounded Ω)
    (h : IsBoundaryOfClass V Ω) :
    ∃ s : Finset (EuclideanSpace ℝ (Fin (d + 1)) × ℝ),
      (∀ q ∈ s, q.1 ∈ frontier Ω ∧ 0 < q.2 ∧ IsBoundaryGraphAt V Ω q.1 q.2) ∧
        frontier Ω ⊆ ⋃ q ∈ s, Metric.ball q.1 q.2 := by
  have hc : IsCompact (frontier Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hΩ.closure.subset frontier_subset_closure)
  set S : Set (EuclideanSpace ℝ (Fin (d + 1)) × ℝ) :=
    {q | q.1 ∈ frontier Ω ∧ 0 < q.2 ∧ IsBoundaryGraphAt V Ω q.1 q.2} with hS
  have hcov : frontier Ω ⊆ ⋃ q ∈ S, Metric.ball q.1 q.2 := fun x hx ↦
    let ⟨r, hr, hgraph⟩ := h x hx
    Set.mem_biUnion (show (x, r) ∈ S from ⟨hx, hr, hgraph⟩) (Metric.mem_ball_self hr)
  obtain ⟨s, hsS, hsfin, hs⟩ := hc.elim_finite_subcover_image (fun q _ ↦ Metric.isOpen_ball) hcov
  exact ⟨hsfin.toFinset, fun q hq ↦ hsS (hsfin.mem_toFinset.1 hq), by
    simpa only [Set.Finite.mem_toFinset] using hs⟩

/-- The upper half-space of `ℝ^{d+1}` has boundary of class `V` whenever the zero function belongs
to `V`: it is already the region above the graph of `0`, in the given coordinates. This fixes the
orientation convention of `IsBoundaryGraphAt` — the set lies *above* the graph. -/
theorem isBoundaryOfClass_upperHalfSpace (hV : (0 : EuclideanSpace ℝ (Fin d) → ℝ) ∈ V) :
    IsBoundaryOfClass V {x : EuclideanSpace ℝ (Fin (d + 1)) | 0 < x (Fin.last d)} := by
  refine fun x₀ _ ↦ ⟨1, one_pos, AffineIsometryEquiv.refl ℝ _, 0, hV, ?_⟩
  ext x
  simp [and_comm]

end Boundary
