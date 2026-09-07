import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Polynomial
import Numlib.Analysis.Convex.StrictConvexSpace
import Numlib.Analysis.Normed.Module.WeakDual
import Numlib.Approximation.BestApprox
import Numlib.Approximation.Chebyshev
import Numlib.Variational.Minimization
import Numlib.Variational.WeakMinimization

/-!
# Atkinson–Han §3.3: best approximation

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §3.3: the book's best approximation (3.3.3) is the
backbone's `IsBestApprox` (`Numlib.Approximation.BestApprox`); `isBestApprox_iff_norm_eq_iInf` is
the bridge to the book's `‖u - û‖ = inf_{v ∈ K} ‖u - v‖` phrasing.

Definitions 3.3.1–3.3.2 (convex set, convex and strictly convex functional) are Mathlib's
`Convex ℝ K`, `ConvexOn ℝ K f` and `StrictConvexOn ℝ K f`; the book quantifies `λ ∈ (0,1)` where
Mathlib uses `[0,1]`, which is the same condition (`convex_iff_openSegment_subset`). The
convex-combination statement (3.3.1) is Mathlib's `Convex.sum_mem`, and closed versus sequentially
closed sets (Definition 3.3.3) agree in metric spaces (`isSeqClosed_iff_isClosed`), as do
sequential and topological lower semicontinuity.

## Book-specific definitions

* `WeakSeqTendsto` — weak sequential convergence (Definition 2.7.1), only the sequential form and
  over any `RCLike 𝕜`; `tendsto_toWeakSpace_iff_weakSeqTendsto` identifies it with convergence in
  Mathlib's `WeakSpace` topology, and `weakSeqTendsto_iff_root` with the backbone's real-scalar
  `_root_.WeakSeqTendsto`, in which the direct method of `Numlib.Variational.WeakMinimization` is
  stated.
* `AreSeparated`, `AreStrictlySeparated` — Definition 3.3.6.
* `IsStrictlyNormed` — §3.3.4, equivalent to Mathlib's `StrictConvexSpace ℝ V`.
* `polyLE`, `rho` — the space `𝒫ₙ` of polynomials of degree `≤ n` on `[a, b]` and the best
  uniform approximation error `ρₙ(f)`.

Definition 3.3.9 (a coercive functional) is the backbone's `IsCoerciveFunctionalOn`, which is
*not* the backbone's `IsCoercive`: the latter is the operator condition `re ⟪A x, x⟫ ≥ c ‖x‖²`
(the book's "strongly monotone").

## Main results

* `example_3_3_5` — the norm is weakly sequentially lower semicontinuous.
* `theorem_3_3_7`, `theorem_3_3_7'` — strict separation of a compact convex set from a disjoint
  closed convex set, in either order.
* `theorem_3_3_8`, `theorem_3_3_10`, `theorem_3_3_12` — existence of minimizers in a reflexive
  Banach space, on a bounded weakly closed set, on an unbounded one with a coercive functional, and
  on a closed convex set with a convex functional.
* `theorem_3_3_11`, `theorem_3_3_11_isWeakSeqClosed`, `theorem_3_3_11_weakSeqLsc` — Mazur's lemma
  and its two corollaries.
* `theorem_3_3_13` — existence (and uniqueness) of minimizers on finite-dimensional closed sets.
* `theorem_3_3_14`, `theorem_3_3_15`, `theorem_3_3_16`, `example_3_3_17` — existence of best
  approximations.
* `theorem_3_3_18`, `theorem_3_3_21` — uniqueness under strict convexity of `‖·‖ᵖ`, resp. strict
  normedness.
* `theorem_3_3_19`, `theorem_3_3_19_equioscillates`, `theorem_3_3_19_alternation` — the Chebyshev
  equi-oscillation theorem: a unique best uniform polynomial approximation on `[a, b]`, and its
  characterization by an alternation of length `n + 2`.
* `theorem_3_3_20` — the same existence and uniqueness for trigonometric polynomials on `C_p(2π)`.
* `exercise_3_3_8`, `exercise_3_3_8_rpow`, `exercise_3_3_9` — inner product spaces satisfy
  both criteria.

## Reflexivity

Theorems 3.3.8, 3.3.10, 3.3.12 and 3.3.14 assume a reflexive Banach space, and Mathlib has no
reflexivity class. What their proofs use of reflexivity is the book's own characterization of it,
Theorem 2.7.5: every bounded sequence has a weakly convergent subsequence. That property is the
class `WeaklySeqCompactSpace` of `Numlib.Variational.WeakMinimization`, and it is the hypothesis
carried here in place of reflexivity; every Hilbert space is an instance of it, which is where this
corpus applies these theorems. The book itself says as much in the paragraph before its
Theorem 3.3.13: "the reflexivity of `V` is used only to extract a weakly convergent subsequence
from a bounded sequence in `K`".

The book's "weakly sequentially lower semicontinuous" is `WeakSeqLowerSemicontinuousOn`, which is
phrased as `∀ y < f u, ∀ᶠ n, y < f (vₙ)` rather than as the book's `f u ≤ liminf f (vₙ)`. The two
agree whenever `f (vₙ)` is bounded below, but a real `liminf` is junk (namely `0`) for a sequence
that is not, and with the literal transcription Theorem 3.3.8 is false: on `K = [0, 1]` the
function `f 0 = 0`, `f x = -1/x` satisfies it and has no minimum.

Theorems 3.3.19 and 3.3.20 are stated here and proved from the backbone
`Numlib/Approximation/Chebyshev.lean`; the book's `𝕋ₙ` is the backbone's `trigPolyLE (2π) n` and
its `C_p(2π)` is `C(ℝ / 2πℤ, ℝ)`, so no vocabulary of its own is introduced for them.
-/

open Filter Topology Bornology

namespace AtkinsonHan.Chapter03

/-! ### The book's best-approximation vocabulary -/

section Iinf

variable {V : Type*} [SeminormedAddCommGroup V]

/-- The book's phrasing (3.3.3) of best approximation, `‖u - û‖ = inf_{v ∈ K} ‖u - v‖`, agrees
with the backbone's `IsBestApprox`. -/
theorem isBestApprox_iff_norm_eq_iInf (K : Set V) (u v : V) :
    IsBestApprox K u v ↔ v ∈ K ∧ ‖u - v‖ = ⨅ w : K, ‖u - (w : V)‖ := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    rw [h.norm_sub_eq_infDist, Metric.infDist_eq_iInf]
    simp [dist_eq_norm]
  · rintro ⟨hv, hnorm⟩
    refine (isBestApprox_iff_norm_sub_eq_infDist hv).2 ?_
    rw [hnorm, Metric.infDist_eq_iInf]
    simp [dist_eq_norm]

end Iinf

/-! ### Definitions 3.3.3, 3.3.6 and 3.3.9 -/

section Defs

variable (𝕜 : Type*) {V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Weak sequential convergence** `vₙ ⇀ u` (Definition 2.7.1): `ℓ(vₙ) → ℓ(u)` for every bounded
linear functional `ℓ`. Only the sequential notion is defined, which is all §3.3 uses; Mathlib's
`WeakSpace` carries the topological version. -/
def WeakSeqTendsto (v : ℕ → V) (u : V) : Prop :=
  ∀ ℓ : StrongDual 𝕜 V, Tendsto (fun n => ℓ (v n)) atTop (𝓝 (ℓ u))

end Defs

section RealDefs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Separated sets** (Definition 3.3.6): a nonzero bounded linear functional and a level `α`
with `A` on one side and `B` on the other. -/
def AreSeparated (A B : Set E) : Prop :=
  ∃ (ℓ : StrongDual ℝ E) (α : ℝ), ℓ ≠ 0 ∧ (∀ u ∈ A, ℓ u ≤ α) ∧ ∀ v ∈ B, α ≤ ℓ v

/-- **Strictly separated sets** (Definition 3.3.6), with strict inequalities. -/
def AreStrictlySeparated (A B : Set E) : Prop :=
  ∃ (ℓ : StrongDual ℝ E) (α : ℝ), ℓ ≠ 0 ∧ (∀ u ∈ A, ℓ u < α) ∧ ∀ v ∈ B, α < ℓ v

/-- Strict separation follows from the conclusion shape of Mathlib's geometric Hahn–Banach
theorems: take `α = (u + v) / 2`.

Only this direction holds. The converse fails: over `ℝ`, `A = Iio 0` and `B = Ioi 0` are strictly
separated in the sense of Definition 3.3.6 by `ℓ = id` and `α = 0`, but there is no pair
`u < v` with `A ⊆ {ℓ < u}` and `B ⊆ {v < ℓ}`. -/
theorem areStrictlySeparated_of_exists {A B : Set E} (hA : A.Nonempty) (hB : B.Nonempty)
    (h : ∃ (f : StrongDual ℝ E) (u v : ℝ), (∀ a ∈ A, f a < u) ∧ u < v ∧ ∀ b ∈ B, v < f b) :
    AreStrictlySeparated A B := by
  obtain ⟨f, u, v, hu, huv, hv⟩ := h
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  refine ⟨f, (u + v) / 2, ?_, fun x hx => (hu x hx).trans (by linarith), fun y hy => ?_⟩
  · rintro rfl
    have h₁ : (0 : ℝ) < u := by simpa using hu a ha
    have h₂ : v < (0 : ℝ) := by simpa using hv b hb
    linarith
  · exact lt_of_lt_of_le (by linarith) (hv y hy).le

/-- Strict separation implies separation (Definition 3.3.6). -/
theorem AreStrictlySeparated.areSeparated {A B : Set E} (h : AreStrictlySeparated A B) :
    AreSeparated A B := by
  obtain ⟨ℓ, α, h0, hA, hB⟩ := h
  exact ⟨ℓ, α, h0, fun u hu => (hA u hu).le, fun v hv => (hB v hv).le⟩

/-- **Strictly normed space** (§3.3.4): `‖u + v‖ = ‖u‖ + ‖v‖` with `u ≠ 0` forces `v = λ u` for
some `λ ≥ 0`. -/
def IsStrictlyNormed (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ u v : E, ‖u + v‖ = ‖u‖ + ‖v‖ → u ≠ 0 → ∃ lam : ℝ, 0 ≤ lam ∧ v = lam • u

/-- The book's strictly normed spaces are exactly Mathlib's strictly convex spaces, so the
backbone's `IsBestApprox.unique` applies to them. -/
theorem isStrictlyNormed_iff_strictConvexSpace :
    IsStrictlyNormed E ↔ StrictConvexSpace ℝ E := by
  constructor
  · intro h
    refine StrictConvexSpace.of_norm_add fun x y hx hy hxy => ?_
    have hx0 : x ≠ 0 := by
      intro hx0
      rw [hx0, norm_zero] at hx
      exact zero_ne_one hx
    obtain ⟨lam, hlam, rfl⟩ := h x y (by rw [hxy, hx, hy]; norm_num) hx0
    exact SameRay.sameRay_nonneg_smul_right x hlam
  · intro h u v hnorm hu
    obtain ⟨r, hr, hrv⟩ := (sameRay_iff_norm_add.2 hnorm).exists_nonneg_left hu
    exact ⟨r, hr, hrv.symm⟩

end RealDefs

/-! ### Example 3.3.5: weak lower semicontinuity of the norm -/

section WeakLsc

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Weak sequential convergence in the sense of Definition 3.3.3 is convergence in Mathlib's
`WeakSpace` topology, which is how the backbone states its two weak-convergence lemmas. -/
theorem tendsto_toWeakSpace_iff_weakSeqTendsto {v : ℕ → V} {u : V} :
    Tendsto (fun n => toWeakSpace 𝕜 V (v n)) atTop (𝓝 (toWeakSpace 𝕜 V u)) ↔
      WeakSeqTendsto 𝕜 v u :=
  tendsto_toWeakSpace_iff

/-- Over the reals, Definition 3.3.3 is the backbone's `WeakSeqTendsto`, in which
`Numlib.Variational.WeakMinimization` states the direct method. -/
theorem weakSeqTendsto_iff_root {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {v : ℕ → V}
    {u : V} : WeakSeqTendsto ℝ v u ↔ _root_.WeakSeqTendsto v u :=
  Iff.rfl

/-- **Example 3.3.5.** The norm is weakly sequentially lower semicontinuous:
`vₙ ⇀ u` implies `‖u‖ ≤ liminf ‖vₙ‖`. The book proves the same statement again as
Exercise 2.7.2; both specialize the backbone's `norm_le_liminf_norm_of_weak_tendsto`. -/
theorem example_3_3_5 (v : ℕ → V) (u : V) (hweak : WeakSeqTendsto 𝕜 v u) :
    ‖u‖ ≤ liminf (fun n => ‖v n‖) atTop :=
  norm_le_liminf_norm_of_weak_tendsto (tendsto_toWeakSpace_iff_weakSeqTendsto.2 hweak)

end WeakLsc

/-! ### Theorem 3.3.7: strict separation -/

section Separation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 3.3.7.** Two nonempty disjoint convex sets in a real normed space, one compact and
the other closed, are strictly separated in the sense of Definition 3.3.6. -/
theorem theorem_3_3_7 {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B) (hAne : A.Nonempty)
    (hBne : B.Nonempty) (hdisj : Disjoint A B) (hAc : IsCompact A) (hBc : IsClosed B) :
    AreStrictlySeparated A B :=
  areStrictlySeparated_of_exists hAne hBne
    (geometric_hahn_banach_compact_closed hA hAc hB hBc hdisj)

/-- **Theorem 3.3.7**, the symmetric case: `A` closed and `B` compact. -/
theorem theorem_3_3_7' {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B) (hAne : A.Nonempty)
    (hBne : B.Nonempty) (hdisj : Disjoint A B) (hAc : IsClosed A) (hBc : IsCompact B) :
    AreStrictlySeparated A B :=
  areStrictlySeparated_of_exists hAne hBne
    (geometric_hahn_banach_closed_compact hA hAc hB hBc hdisj)

end Separation

/-! ### Theorems 3.3.8–3.3.14: minimizers in a reflexive Banach space -/

section Reflexive

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

set_option linter.unusedVariables false in
/-- **Theorem 3.3.8.** A weakly sequentially lower semicontinuous functional on a nonempty bounded
weakly sequentially closed subset of a reflexive Banach space attains its minimum.

Reflexivity enters only through the book's own characterization of it (their Theorem 2.7.5), that
every bounded sequence has a weakly convergent subsequence; that is the class
`WeaklySeqCompactSpace`. Completeness is the book's hypothesis and is not used.

`IsWeakSeqClosed K` is the book's "weakly closed": their Definition 3.3.3 defines it sequentially,
as "`vₙ ∈ K` and `vₙ ⇀ v` imply `v ∈ K`". -/
theorem theorem_3_3_8 [CompleteSpace V] [WeaklySeqCompactSpace V] {K : Set V} {f : V → ℝ}
    (hne : K.Nonempty) (hbd : IsBounded K) (hKc : IsWeakSeqClosed K)
    (hf : WeakSeqLowerSemicontinuousOn f K) : ∃ u ∈ K, IsMinOn f K u :=
  exists_isMinOn_of_isWeakSeqClosed hne hbd hKc hf

set_option linter.unusedVariables false in
/-- **Theorem 3.3.10.** The boundedness of `K` in Theorem 3.3.8 may be traded for coercivity of the
functional: the book cuts the problem down to the sublevel set `{v ∈ K | f v ≤ f v₀}`, which
coercivity makes bounded. -/
theorem theorem_3_3_10 [CompleteSpace V] [WeaklySeqCompactSpace V] {K : Set V} {f : V → ℝ}
    (hne : K.Nonempty) (hKc : IsWeakSeqClosed K) (hf : WeakSeqLowerSemicontinuousOn f K)
    (hcoer : IsCoerciveFunctionalOn f K) : ∃ u ∈ K, IsMinOn f K u :=
  exists_isMinOn_of_isCoerciveFunctionalOn hne hKc hf hcoer

/-- **Theorem 3.3.11** (Mazur's lemma). If `vₙ ⇀ u` in a normed space, then there are convex
combinations `uₙ = ∑_{i=n}^{N(n)} λᵢ⁽ⁿ⁾ vᵢ` of the tails of the sequence with `‖uₙ - u‖ → 0`. No
reflexivity is needed. -/
theorem theorem_3_3_11 {v : ℕ → V} {u : V} (h : WeakSeqTendsto ℝ v u) :
    ∃ (N : ℕ → ℕ) (lam : ℕ → ℕ → ℝ), (∀ n, n ≤ N n) ∧ (∀ n i, 0 ≤ lam n i) ∧
      (∀ n, ∑ i ∈ Finset.Icc n (N n), lam n i = 1) ∧
      Tendsto (fun n => ∑ i ∈ Finset.Icc n (N n), lam n i • v i) atTop (𝓝 u) :=
  exists_seq_convexCombination_tendsto h

/-- **Theorem 3.3.11**, first corollary: a closed convex set is weakly sequentially closed, so the
weak hypothesis of Theorems 3.3.8 and 3.3.10 is implied by the ordinary one. "Weakly closed" is
`IsWeakSeqClosed`, the book's Definition 3.3.3. -/
theorem theorem_3_3_11_isWeakSeqClosed {K : Set V} (hconv : Convex ℝ K) (hcl : IsClosed K) :
    IsWeakSeqClosed K :=
  hconv.isWeakSeqClosed hcl

/-- **Theorem 3.3.11**, second corollary: a convex lower semicontinuous functional is weakly
sequentially lower semicontinuous, its sublevel sets being convex. -/
theorem theorem_3_3_11_weakSeqLsc {K : Set V} {f : V → ℝ} (hf : ConvexOn ℝ K f)
    (hlsc : LowerSemicontinuousOn f K) : WeakSeqLowerSemicontinuousOn f K :=
  hf.weakSeqLowerSemicontinuousOn hlsc

set_option linter.unusedVariables false in
/-- **Theorem 3.3.12.** In a reflexive Banach space, a convex lower semicontinuous functional on a
nonempty closed convex set attains its minimum, provided the set is bounded or the functional is
coercive. Every hypothesis here is for the norm topology: the two corollaries of Mazur's lemma
convert them to the weak hypotheses of Theorems 3.3.8 and 3.3.10.

This is the infinite-dimensional twin of `theorem_3_3_13`, and `theorem_3_3_13_unique` is the
uniqueness clause of both. -/
theorem theorem_3_3_12 [CompleteSpace V] [WeaklySeqCompactSpace V] {K : Set V} {f : V → ℝ}
    (hne : K.Nonempty) (hcl : IsClosed K) (hconv : Convex ℝ K) (hf : ConvexOn ℝ K f)
    (hlsc : LowerSemicontinuousOn f K)
    (h : IsBounded K ∨ IsCoerciveFunctionalOn f K) : ∃ u ∈ K, IsMinOn f K u :=
  exists_isMinOn_of_convexOn hne hcl hconv hf hlsc h

set_option linter.unusedVariables false in
/-- **Theorem 3.3.14.** In a reflexive Banach space every point has a best approximation from a
nonempty closed convex set: the distance to the point is convex, continuous and coercive, so this
is the coercive case of Theorem 3.3.12. It is the infinite-dimensional twin of `theorem_3_3_15`;
in a Hilbert space it is `theorem_3_4_3`. -/
theorem theorem_3_3_14 [CompleteSpace V] [WeaklySeqCompactSpace V] {K : Set V} (hne : K.Nonempty)
    (hcl : IsClosed K) (hconv : Convex ℝ K) (u : V) : ∃ uhat, IsBestApprox K u uhat :=
  exists_isBestApprox_of_convex hne hcl hconv u

end Reflexive

/-! ### Theorem 3.3.13: minimizers on finite-dimensional closed sets -/

section Minimization

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

set_option linter.unusedVariables false in
/-- **Theorem 3.3.13.** A lower semicontinuous functional on a nonempty closed subset `K` of a
finite-dimensional subspace attains its minimum, provided `K` is bounded or `f` is coercive on
`K`. The book's convexity hypotheses on `K` and `f` are kept for faithfulness; neither the book's
proof nor this one uses them at this rung. -/
theorem theorem_3_3_13 [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {K : Set V} (S : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hcl : IsClosed K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (f : V → ℝ) (hf : ConvexOn ℝ K f) (hlsc : LowerSemicontinuousOn f K)
    (h : IsBounded K ∨ IsCoerciveFunctionalOn f K) : ∃ u ∈ K, IsMinOn f K u :=
  exists_isMinOn_of_isClosed_of_finiteDimensional S hKS hcl hne hlsc
    (h.elim IsCoerciveFunctionalOn.of_isBounded id)

/-- **Theorem 3.3.13**, uniqueness clause: a strictly convex functional has at most one
minimizer. -/
theorem theorem_3_3_13_unique [NormedSpace ℝ V] {K : Set V} {f : V → ℝ} (hf : StrictConvexOn ℝ K f)
    {u₁ u₂ : V} (hu₁ : IsMinOn f K u₁) (hu₂ : IsMinOn f K u₂) (h₁ : u₁ ∈ K) (h₂ : u₂ ∈ K) :
    u₁ = u₂ :=
  IsMinOn.eq_of_strictConvexOn hf hu₁ hu₂ h₁ h₂

end Minimization

/-! ### Theorems 3.3.15–3.3.16 and Example 3.3.17: existence of best approximations -/

section Existence

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

set_option linter.unusedVariables false in
/-- **Theorem 3.3.15.** Every point has a best approximation from a nonempty closed convex subset
of a finite-dimensional subspace. Convexity is kept for faithfulness and is not used. -/
theorem theorem_3_3_15 [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {K : Set V} (S : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hK : IsClosed K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (u : V) : ∃ uhat, IsBestApprox K u uhat :=
  exists_isBestApprox_of_isClosed_of_finiteDimensional hK hne S hKS u

/-- **Theorem 3.3.16.** Every point has a best approximation from a finite-dimensional
subspace. -/
theorem theorem_3_3_16 (K : Submodule 𝕜 V) [FiniteDimensional 𝕜 K] (u : V) :
    ∃ uhat, IsBestApprox (K : Set V) u uhat :=
  exists_isBestApprox_of_finiteDimensional K u

end Existence

section Polynomials

/-- The space `𝒫ₙ` of (restrictions to `[a, b]` of) real polynomials of degree at most `n`,
as a subspace of `C[a, b]`. -/
noncomputable def polyLE (a b : ℝ) (n : ℕ) : Submodule ℝ C(Set.Icc a b, ℝ) :=
  (Polynomial.degreeLT ℝ (n + 1)).map
    (Polynomial.toContinuousMapOnAlgHom (Set.Icc a b)).toLinearMap

/-- `𝒫n` is finite dimensional: it is the image of the finite-dimensional space of
polynomials of degree `< n + 1` under a linear map. -/
instance (a b : ℝ) (n : ℕ) : FiniteDimensional ℝ (polyLE a b n) := by
  unfold polyLE
  infer_instance

/-- `ρₙ(f)`, the error of best uniform approximation of `f ∈ C[a, b]` from `𝒫ₙ`. -/
noncomputable def rho (a b : ℝ) (n : ℕ) (f : C(Set.Icc a b, ℝ)) : ℝ :=
  ⨅ p : polyLE a b n, ‖f - (p : C(Set.Icc a b, ℝ))‖

/-- `ρₙ(f)` is attained: it is the distance from `f` to any of its best approximations in
`𝒫ₙ`. -/
theorem rho_eq_norm_sub_of_isBestApprox {a b : ℝ} {n : ℕ} {f p : C(Set.Icc a b, ℝ)}
    (h : IsBestApprox (polyLE a b n : Set C(Set.Icc a b, ℝ)) f p) : ‖f - p‖ = rho a b n f :=
  ((isBestApprox_iff_norm_eq_iInf _ _ _).1 h).2

/-- **Example 3.3.17.** Best uniform polynomial approximations on `[a, b]` exist: `𝒫ₙ` is a
finite-dimensional subspace of `C[a, b]`, so Theorem 3.3.16 applies. The book's `Lᵖ(a, b)` case
is out of scope. -/
theorem example_3_3_17 (a b : ℝ) (n : ℕ) (f : C(Set.Icc a b, ℝ)) :
    ∃ p, IsBestApprox (polyLE a b n : Set C(Set.Icc a b, ℝ)) f p :=
  exists_isBestApprox_of_finiteDimensional (polyLE a b n) f

/-- The book's `𝒫ₙ` on `[a, b]` is the backbone's `polyLE`: the polynomials of degree `< n + 1` and
those of degree `≤ n` are the same subspace of `ℝ[X]`. -/
theorem polyLE_eq (a b : ℝ) (n : ℕ) : polyLE a b n = _root_.polyLE (Set.Icc a b) n := by
  rw [polyLE, _root_.polyLE, Polynomial.degreeLT_succ_eq_degreeLE]

/-- **Theorem 3.3.19** (Chebyshev equi-oscillation theorem), the existence and uniqueness clause:
on a nondegenerate interval the minimization problem `ρₙ(f) = min_{p ∈ 𝒫ₙ} ‖f - p‖_∞` has exactly
one solution. -/
theorem theorem_3_3_19 {a b : ℝ} (hab : a < b) (n : ℕ) (f : C(Set.Icc a b, ℝ)) :
    ∃! p : C(Set.Icc a b, ℝ), IsBestApprox (polyLE a b n : Set C(Set.Icc a b, ℝ)) f p := by
  have : Infinite (Set.Icc a b) := Set.Icc.infinite hab
  rw [polyLE_eq]
  exact existsUnique_isBestApprox_polyLE n f

/-- **Theorem 3.3.19**, the characterization: `p ∈ 𝒫ₙ` is a best uniform approximation of `f` on
`[a, b]` exactly when the error `f - p` attains `± ‖f - p‖_∞` with alternating signs at `n + 2`
increasing points of `[a, b]`. -/
theorem theorem_3_3_19_equioscillates {a b : ℝ} (hab : a < b) {n : ℕ} {f p : C(Set.Icc a b, ℝ)}
    (hp : p ∈ polyLE a b n) :
    IsBestApprox (polyLE a b n : Set C(Set.Icc a b, ℝ)) f p ↔ Equioscillates (f - p) (n + 2) := by
  have : Infinite (Set.Icc a b) := Set.Icc.infinite hab
  rw [polyLE_eq] at hp ⊢
  exact isBestApprox_iff_equioscillates hp

/-- **Theorem 3.3.19** in the book's display: for the best approximation `p̂ₙ` there are `n + 2`
points `a ≤ x₀ < ⋯ < x_{n+1} ≤ b` and a sign `σ = ±1` with `f(xⱼ) - p̂ₙ(xⱼ) = σ (-1)ʲ ρₙ(f)`. -/
theorem theorem_3_3_19_alternation {a b : ℝ} (hab : a < b) {n : ℕ} {f p : C(Set.Icc a b, ℝ)}
    (h : IsBestApprox (polyLE a b n : Set C(Set.Icc a b, ℝ)) f p) :
    ∃ (σ : ℝ) (x : Fin (n + 2) → Set.Icc a b), (σ = 1 ∨ σ = -1) ∧
      StrictMono (fun i => (x i : ℝ)) ∧
      ∀ i : Fin (n + 2), f (x i) - p (x i) = σ * (-1) ^ (i : ℕ) * rho a b n f := by
  obtain ⟨σ, x, hσ, hmono, hval⟩ := (theorem_3_3_19_equioscillates hab h.1).1 h
  exact ⟨σ, x, hσ, hmono, fun i => by
    simpa [rho_eq_norm_sub_of_isBestApprox h] using hval i⟩

end Polynomials

/-! ### Theorem 3.3.20: best uniform approximation by trigonometric polynomials -/

section TrigonometricPolynomials

open scoped Real

/-- **Theorem 3.3.20.** For a continuous `2π`-periodic function `g` — an element of `C_p(2π)`,
realized as `C(ℝ / 2πℤ, ℝ)` — and an integer `n ≥ 0` there is exactly one trigonometric polynomial
`q̂ₙ ∈ 𝕋ₙ` of degree at most `n` with `‖g - q̂ₙ‖_∞ = min_{q ∈ 𝕋ₙ} ‖g - q‖_∞`.

Existence is Theorem 3.3.16, `𝕋ₙ` being a `2 n + 1`-dimensional subspace; uniqueness is the Haar
condition for the trigonometric polynomials, a nonzero one of degree at most `n` having at most
`2 n` zeros in a period. -/
theorem theorem_3_3_20 (n : ℕ) (g : C(AddCircle (2 * π), ℝ)) :
    ∃! q : C(AddCircle (2 * π), ℝ),
      IsBestApprox (trigPolyLE (2 * π) n : Set C(AddCircle (2 * π), ℝ)) g q :=
  existsUnique_isBestApprox_trigPolyLE n g

end TrigonometricPolynomials

/-! ### Theorems 3.3.18 and 3.3.21: uniqueness of best approximations -/

section Uniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option linter.unusedVariables false in
/-- **Theorem 3.3.18.** If `‖·‖ᵖ` is strictly convex for some `p ≥ 1`, best approximations from a
convex set are unique. -/
theorem theorem_3_3_18 {p : ℝ} (hp : 1 ≤ p)
    (hconv : StrictConvexOn ℝ (Set.univ : Set E) fun v : E => ‖v‖ ^ p) {K : Set E}
    (hK : Convex ℝ K) {u v₁ v₂ : E} (h₁ : IsBestApprox K u v₁) (h₂ : IsBestApprox K u v₂) :
    v₁ = v₂ :=
  have : StrictConvexSpace ℝ E := StrictConvexSpace.of_strictConvexOn_norm_rpow hp hconv
  h₁.unique hK h₂

set_option linter.unusedVariables false in
/-- **Theorem 3.3.21.** In a strictly normed space, best approximations from a nonempty convex
set are unique. -/
theorem theorem_3_3_21 (hV : IsStrictlyNormed E) {K : Set E} (hne : K.Nonempty) (hK : Convex ℝ K)
    {u v₁ v₂ : E} (h₁ : IsBestApprox K u v₁) (h₂ : IsBestApprox K u v₂) : v₁ = v₂ :=
  have : StrictConvexSpace ℝ E := isStrictlyNormed_iff_strictConvexSpace.1 hV
  h₁.unique hK h₂

end Uniqueness

/-! ### Exercises 3.3.8 and 3.3.9 -/

section InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Exercise 3.3.8.** In an inner product space `‖·‖²` is strictly convex, because
`a ‖x‖² + b ‖y‖² - ‖a x + b y‖² = a b ‖x - y‖²` when `a + b = 1`. With Theorem 3.3.18 this gives
uniqueness of best approximations from convex sets (Corollary 3.4.2). -/
theorem exercise_3_3_8 : StrictConvexOn ℝ (Set.univ : Set H) fun v : H => ‖v‖ ^ 2 :=
  strictConvexOn_norm_sq

/-- **Exercise 3.3.8**, in the real-exponent form that Theorem 3.3.18 consumes (`p = 2`). -/
theorem exercise_3_3_8_rpow :
    StrictConvexOn ℝ (Set.univ : Set H) fun v : H => ‖v‖ ^ (2 : ℝ) :=
  strictConvexOn_norm_rpow_two

/-- **Exercise 3.3.9.** Inner product spaces are strictly normed. -/
theorem exercise_3_3_9 : IsStrictlyNormed H :=
  isStrictlyNormed_iff_strictConvexSpace.2 inferInstance

end InnerProduct

end AtkinsonHan.Chapter03
