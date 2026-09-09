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
import NumlibSurface.AtkinsonHan.Chapter01.Section02
import NumlibSurface.AtkinsonHan.Chapter02.Section07

/-!
# Atkinson–Han §3.3: best approximation

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §3.3: the book's best approximation (3.3.3) is the
backbone's `IsBestApprox` (`Numlib.Approximation.BestApprox`); `isBestApprox_iff_norm_eq_iInf` is
the bridge to the book's `‖u - û‖ = inf_{v ∈ K} ‖u - v‖` phrasing.

Definitions 3.3.1–3.3.4 are restated here under their numbers: a convex set and a convex or
strictly convex functional are Mathlib's `Convex ℝ K`, `ConvexOn ℝ K f` and `StrictConvexOn ℝ K f`,
the book's `λ ∈ (0,1)` and Mathlib's `[0,1]` being the same condition; a closed set is `IsClosed`,
sequential and topological closedness agreeing in a metric space, and a lower semicontinuous
functional is `LowerSemicontinuousOn`; and the two weak clauses are the backbone's
`IsWeakSeqClosed` and `WeakSeqLowerSemicontinuousOn`. The two convergences the last four are
written over are the earlier restatements rather than their Mathlib originals: `vₙ → v` is
`Chapter01.definition_1_2_8` and `vₙ ⇀ v` is §2.7's `Chapter02.WeakSeqTendsto`, the book's
Definition 2.7.1, which this module uses throughout rather than defining a second time.

## Main definitions

* `definition_3_3_1`, `definition_3_3_2`, `definition_3_3_2_strict` — a convex set, a convex
  functional and a strictly convex functional, with (3.3.1) as `definition_3_3_1_sum`.
* `definition_3_3_3`, `definition_3_3_3_weak` — a closed and a weakly closed set.
* `definition_3_3_4`, `definition_3_3_4_weak` — a lower semicontinuous and a weakly sequentially
  lower semicontinuous functional.
* `definition_3_3_9` — a functional coercive over `K`.

## Book-specific definitions

* `AreSeparated`, `AreStrictlySeparated` — Definition 3.3.6.
* `IsStrictlyNormed` — §3.3.4, equivalent to Mathlib's `StrictConvexSpace ℝ V`.
* `polyLE`, `rho` — the space `𝒫ₙ` of polynomials of degree `≤ n` on `[a, b]` and the best
  uniform approximation error `ρₙ(f)`.

Definition 3.3.9 (a coercive functional) is restated as `definition_3_3_9` and identified by
`definition_3_3_9_iff` with the backbone's `IsCoerciveFunctionalOn`, which is *not* the backbone's
`IsCoercive`: the latter is the operator condition `re ⟪A x, x⟫ ≥ c ‖x‖²` (the book's "strongly
monotone").

## Main results

* `definition_3_3_1_iff`, `definition_3_3_2_iff`, `definition_3_3_2_strict_iff`,
  `definition_3_3_3_iff`, `definition_3_3_3_weak_iff`, `definition_3_3_4_iff`,
  `definition_3_3_4_weak_iff`, `definition_3_3_9_iff` — each restated definition read back as the
  Mathlib or backbone notion the theorems below are stated in; `definition_3_3_3_of_weak` is the
  book's remark that a weakly closed set is closed.
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
function `f 0 = 0`, `f x = -1/x` satisfies it and has no minimum. This is why `definition_3_3_4`
and `definition_3_3_4_weak` take their `liminf` in `EReal`, where it is the limit inferior of the
book rather than a junk value; over `EReal` the equivalence with the two semicontinuity predicates
is unconditional, and `le_liminf_ereal_iff` is the one step that converts between the two
phrasings.

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

/-! ### Definitions 3.3.1 and 3.3.2: convex sets and convex functionals -/

section Convexity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Definition 3.3.1.** A subset `K` of a linear space is *convex* when
`λ u + (1 - λ) v ∈ K` for all `u, v ∈ K` and all `λ ∈ (0, 1)`.

This is Mathlib's `Convex ℝ K`, whose interval is the closed `[0, 1]`; the two agree, which is
`definition_3_3_1_iff`. The convex-combination statement (3.3.1) is
`definition_3_3_1_sum`. -/
def definition_3_3_1 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, ∀ lam : ℝ, 0 < lam → lam < 1 → lam • u + (1 - lam) • v ∈ K

/-- Definition 3.3.1 is Mathlib's `Convex ℝ K`: the book's open interval `(0, 1)` and Mathlib's
closed `[0, 1]` describe the same sets. -/
theorem definition_3_3_1_iff (K : Set V) : definition_3_3_1 K ↔ Convex ℝ K := by
  rw [convex_iff_openSegment_subset]
  constructor
  · rintro h u hu v hv z ⟨a, b, ha, hb, hab, rfl⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    exact h u hu v hv a ha (by linarith)
  · intro h u hu v hv lam h0 h1
    exact h hu hv ⟨lam, 1 - lam, h0, by linarith, by ring, rfl⟩

/-- **(3.3.1).** Every convex combination of elements of a convex set lies in the set. -/
theorem definition_3_3_1_sum {K : Set V} (hK : definition_3_3_1 K) {n : ℕ} {lam : Fin n → ℝ}
    {v : Fin n → V} (hlam : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1) (hv : ∀ i, v i ∈ K) :
    ∑ i, lam i • v i ∈ K :=
  ((definition_3_3_1_iff K).mp hK).sum_mem (fun i _ => hlam i) hsum fun i _ => hv i

/-- **Definition 3.3.2.** A functional `f : K → ℝ` on a convex set `K` is *convex* when
`f (λ u + (1 - λ) v) ≤ λ f u + (1 - λ) f v` for all `u, v ∈ K` and `λ ∈ [0, 1]`.

This is Mathlib's `ConvexOn ℝ K f`, which bundles the convexity of `K` into the predicate;
`definition_3_3_2_iff` is the correspondence for a `K` convex in the sense of Definition 3.3.1. -/
def definition_3_3_2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V)
    (f : V → ℝ) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    f (lam • u + (1 - lam) • v) ≤ lam * f u + (1 - lam) * f v

/-- **Definition 3.3.2**, second clause. `f` is *strictly convex* on `K` when the inequality of
Definition 3.3.2 is strict for `u ≠ v` and `λ ∈ (0, 1)`.

This is Mathlib's `StrictConvexOn ℝ K f`; `definition_3_3_2_strict_iff` is the correspondence. -/
def definition_3_3_2_strict {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V)
    (f : V → ℝ) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, u ≠ v → ∀ lam : ℝ, 0 < lam → lam < 1 →
    f (lam • u + (1 - lam) • v) < lam * f u + (1 - lam) * f v

/-- Definition 3.3.2 is Mathlib's `ConvexOn`, in which `theorem_3_3_12` and
`theorem_3_3_11_weakSeqLsc` are stated. -/
theorem definition_3_3_2_iff {K : Set V} (hK : definition_3_3_1 K) (f : V → ℝ) :
    definition_3_3_2 K f ↔ ConvexOn ℝ K f := by
  refine ⟨fun h => ⟨(definition_3_3_1_iff K).mp hK, ?_⟩, fun h u hu v hv lam h0 h1 => ?_⟩
  · rintro u hu v hv a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    exact h u hu v hv a ha (by linarith)
  · simpa using h.2 hu hv h0 (by linarith : (0 : ℝ) ≤ 1 - lam) (by ring)

/-- The second clause of Definition 3.3.2 is Mathlib's `StrictConvexOn`, in which
`theorem_3_3_13_unique` is stated. -/
theorem definition_3_3_2_strict_iff {K : Set V} (hK : definition_3_3_1 K) (f : V → ℝ) :
    definition_3_3_2_strict K f ↔ StrictConvexOn ℝ K f := by
  refine ⟨fun h => ⟨(definition_3_3_1_iff K).mp hK, ?_⟩,
    fun h u hu v hv hne lam h0 h1 => ?_⟩
  · rintro u hu v hv hne a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    exact h u hu v hv hne a ha (by linarith)
  · simpa using h.2 hu hv hne h0 (by linarith : (0 : ℝ) < 1 - lam) (by ring)

end Convexity

/-! ### Definitions 3.3.3, 3.3.6 and 3.3.9 -/

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

/-! ### Definitions 3.3.3 and 3.3.4: closed sets and lower semicontinuous functionals -/

section Closedness

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Definition 3.3.3.** A subset `K` of a normed space is *closed* when `vₙ ∈ K` and `vₙ → v`
imply `v ∈ K`. The convergence `vₙ → v` is Definition 1.2.8.

This is Mathlib's `IsClosed`, the sequential and topological readings agreeing in a metric space;
`definition_3_3_3_iff` is the correspondence. -/
def definition_3_3_3 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V) : Prop :=
  ∀ (v : ℕ → V) (u : V), (∀ n, v n ∈ K) → Chapter01.definition_1_2_8 v u → u ∈ K

/-- **Definition 3.3.3**, second clause. `K` is *weakly closed* when `vₙ ∈ K` and `vₙ ⇀ v` imply
`v ∈ K`, the relation `⇀` being Definition 2.7.1.

This is the backbone's `IsWeakSeqClosed`, which `theorem_3_3_8`, `theorem_3_3_10` and
`theorem_3_3_11_isWeakSeqClosed` take directly. -/
def definition_3_3_3_weak {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V) :
    Prop :=
  ∀ (v : ℕ → V) (u : V), (∀ n, v n ∈ K) → Chapter02.WeakSeqTendsto ℝ v u → u ∈ K

/-- Definition 3.3.3 is Mathlib's `IsClosed`. -/
theorem definition_3_3_3_iff (K : Set V) : definition_3_3_3 K ↔ IsClosed K := by
  rw [← isSeqClosed_iff_isClosed]
  simp only [definition_3_3_3, Chapter01.definition_1_2_8_iff]
  exact ⟨fun h _ _ hv hu => h _ _ hv hu, fun h v u hv hu => h hv hu⟩

/-- The second clause of Definition 3.3.3 is the backbone's `IsWeakSeqClosed`. -/
theorem definition_3_3_3_weak_iff (K : Set V) :
    definition_3_3_3_weak K ↔ IsWeakSeqClosed K :=
  Iff.rfl

/-- A weakly closed set is closed, as the book records beside Definition 3.3.3: a norm-convergent
sequence converges weakly to the same limit. The converse fails in infinite dimensions. -/
theorem definition_3_3_3_of_weak {K : Set V} (h : definition_3_3_3_weak K) :
    definition_3_3_3 K :=
  fun v u hv hu =>
    h v u hv (WeakSeqTendsto.of_tendsto ((Chapter01.definition_1_2_8_iff v u).mp hu))

/-- **Definition 3.3.4.** A functional `f` is *(sequentially) lower semicontinuous* on `K` when
`vₙ ∈ K` and `vₙ → v ∈ K` imply `f v ≤ liminf f (vₙ)`, the convergence being Definition 1.2.8.

The `liminf` of a real sequence is read in `EReal`, which is what the book's `liminf` means: Lean's
real `liminf` is junk for a sequence that is unbounded, and the literal real transcription would
make Theorem 3.3.8 false. This is Mathlib's `LowerSemicontinuousOn` by `definition_3_3_4_iff`. -/
def definition_3_3_4 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V)
    (f : V → ℝ) : Prop :=
  ∀ (v : ℕ → V) (u : V), (∀ n, v n ∈ K) → u ∈ K → Chapter01.definition_1_2_8 v u →
    (f u : EReal) ≤ liminf (fun n => (f (v n) : EReal)) atTop

/-- **Definition 3.3.4**, second clause. `f` is *weakly sequentially lower semicontinuous* on `K`
when the same holds for `vₙ ⇀ v ∈ K`.

This is the backbone's `WeakSeqLowerSemicontinuousOn`, which `theorem_3_3_8`, `theorem_3_3_10` and
`theorem_3_3_11_weakSeqLsc` take directly; `definition_3_3_4_weak_iff` is the correspondence. -/
def definition_3_3_4_weak {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V)
    (f : V → ℝ) : Prop :=
  ∀ (v : ℕ → V) (u : V), (∀ n, v n ∈ K) → u ∈ K → Chapter02.WeakSeqTendsto ℝ v u →
    (f u : EReal) ≤ liminf (fun n => (f (v n) : EReal)) atTop

/-- A real number below the `EReal` limit inferior of a sequence is eventually below its terms;
and conversely, a bound that holds eventually bounds the limit inferior. This is the arithmetic
that turns the `liminf` phrasing of Definition 3.3.4 into the `∀ y < f u, ∀ᶠ n, y < f (vₙ)` form of
Mathlib's and the backbone's semicontinuity predicates. -/
private theorem le_liminf_ereal_iff {g : ℕ → ℝ} {c : ℝ} :
    ((c : EReal) ≤ liminf (fun n => (g n : EReal)) atTop) ↔ ∀ y < c, ∀ᶠ n in atTop, y < g n := by
  constructor
  · intro h y hy
    have hy' : (y : EReal) < liminf (fun n => (g n : EReal)) atTop :=
      lt_of_lt_of_le (by exact_mod_cast hy) h
    filter_upwards [eventually_lt_of_lt_liminf hy'] with n hn
    exact_mod_cast hn
  · intro h
    by_contra hc
    rw [not_le] at hc
    obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real hc
    have hylt : y < c := by exact_mod_cast hy2
    have := h y hylt
    have hle : (y : EReal) ≤ liminf (fun n => (g n : EReal)) atTop := by
      refine le_liminf_of_le ?_ ?_
      · exact isCoboundedUnder_ge_of_le _ (fun _ => le_top)
      · filter_upwards [this] with n hn
        exact_mod_cast hn.le
    exact absurd hle (not_le.mpr hy1)

/-- Definition 3.3.4 is Mathlib's `LowerSemicontinuousOn`: sequential and topological lower
semicontinuity agree on a metric space. -/
theorem definition_3_3_4_iff (K : Set V) (f : V → ℝ) :
    definition_3_3_4 K f ↔ LowerSemicontinuousOn f K := by
  constructor
  · intro h u hu y hy
    by_contra hcon
    have hne : (𝓝[K] u).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (subset_closure hu)
    have h1 : ∃ᶠ z in 𝓝[K] u, ¬ y < f z := by rwa [Filter.not_eventually] at hcon
    have hfreq : ∃ᶠ z in 𝓝[K] u, z ∈ K ∧ f z ≤ y :=
      (h1.and_eventually self_mem_nhdsWithin).mono fun z hz => ⟨hz.2, not_lt.mp hz.1⟩
    obtain ⟨v, hvt, hv⟩ := exists_seq_forall_of_frequently hfreq
    have hK : ∀ n, v n ∈ K := fun n => (hv n).1
    have hlim : Chapter01.definition_1_2_8 v u :=
      (Chapter01.definition_1_2_8_iff v u).mpr (hvt.mono_right nhdsWithin_le_nhds)
    obtain ⟨n, hn⟩ := ((le_liminf_ereal_iff.mp (h v u hK hu hlim)) y hy).exists
    exact absurd hn (not_lt.mpr (hv n).2)
  · intro h v u hv hu hlim
    refine le_liminf_ereal_iff.mpr fun y hy => ?_
    have hwithin : Tendsto v atTop (𝓝[K] u) :=
      tendsto_nhdsWithin_iff.mpr ⟨(Chapter01.definition_1_2_8_iff v u).mp hlim,
        Eventually.of_forall hv⟩
    exact hwithin.eventually (h u hu y hy)

/-- The second clause of Definition 3.3.4 is the backbone's `WeakSeqLowerSemicontinuousOn`. -/
theorem definition_3_3_4_weak_iff (K : Set V) (f : V → ℝ) :
    definition_3_3_4_weak K f ↔ WeakSeqLowerSemicontinuousOn f K := by
  constructor
  · intro h v u hv hu hweak
    exact le_liminf_ereal_iff.mp (h v u hv hu hweak)
  · intro h v u hv hu hweak
    exact le_liminf_ereal_iff.mpr fun y hy => h v u hv hu hweak y hy

end Closedness

/-! ### Example 3.3.5: weak lower semicontinuity of the norm -/

section WeakLsc

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Example 3.3.5.** The norm is weakly sequentially lower semicontinuous:
`vₙ ⇀ u` implies `‖u‖ ≤ liminf ‖vₙ‖`. The book proves the same statement again as
Exercise 2.7.2; both specialize the backbone's `norm_le_liminf_norm_of_weak_tendsto`. -/
theorem example_3_3_5 (v : ℕ → V) (u : V) (hweak : Chapter02.WeakSeqTendsto 𝕜 v u) :
    ‖u‖ ≤ liminf (fun n => ‖v n‖) atTop :=
  norm_le_liminf_norm_of_weak_tendsto (Chapter02.tendsto_toWeakSpace_iff_weakSeqTendsto.2 hweak)

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

/-- **Definition 3.3.9.** A real-valued functional `f` on a normed space is *coercive over* a
subset `K` when `f v → ∞` as `‖v‖ → ∞`, `v ∈ K`.

The book's limit is read as convergence to `atTop` along the filter `comap ‖·‖ atTop ⊓ 𝓟 K`, which
is "`‖v‖ → ∞` inside `K`" verbatim. This is the backbone's `IsCoerciveFunctionalOn`, which
`theorem_3_3_10` and `theorem_3_3_12` take directly; `definition_3_3_9_iff` is the correspondence.

It is *not* the backbone's `IsCoercive`: that is the condition `re ⟪A v, v⟫ ≥ c ‖v‖²` on an
*operator* or a sesquilinear form — the book's "strongly monotone" — a lower bound of quadratic
order rather than a growth condition. -/
def definition_3_3_9 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : Set V)
    (f : V → ℝ) : Prop :=
  Tendsto f (comap norm atTop ⊓ 𝓟 K) atTop

/-- Definition 3.3.9 is the backbone's `IsCoerciveFunctionalOn`: for every level `M` there is a
radius `R` beyond which `f ≥ M` on `K`. -/
theorem definition_3_3_9_iff (K : Set V) (f : V → ℝ) :
    definition_3_3_9 K f ↔ IsCoerciveFunctionalOn f K := by
  simp only [definition_3_3_9, IsCoerciveFunctionalOn, tendsto_atTop, eventually_inf_principal,
    eventually_comap, eventually_atTop]
  refine ⟨fun h M => ?_, fun h M => ?_⟩
  · obtain ⟨R, hR⟩ := h M
    exact ⟨R, fun x hx hxR => hR ‖x‖ hxR x rfl hx⟩
  · obtain ⟨R, hR⟩ := h M
    exact ⟨R, fun r hr x hx hxK => hR x hxK (hx ▸ hr)⟩

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
theorem theorem_3_3_11 {v : ℕ → V} {u : V} (h : Chapter02.WeakSeqTendsto ℝ v u) :
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
