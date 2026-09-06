import Numlib.Variational.Inequality.Basic
import NumlibSurface.AtkinsonHan.Chapter05.Section01
import NumlibSurface.AtkinsonHan.Chapter08.Section03

/-!
# Atkinson–Han §11.3: existence and uniqueness for elliptic variational inequalities

Surface formalization of §11.3 of Kendall Atkinson and Weimin Han, *Theoretical Numerical
Analysis: A Functional Analysis Framework*, 3rd edition, Springer, 2009.

The section studies, on a real Hilbert space `V`, the inequality (11.3.3)

  `u ∈ K`,  `(A u, v - u) + j(v) - j(u) ≥ (f, v - u)`  for all `v ∈ K`,

and the five variants the book displays beside it: the inequality *of the first kind* (11.3.8) is
`j = 0`, the inequality *of the second kind* (11.3.9) is `K = V`, and (11.3.12)–(11.3.14) are the
same three with `A` the operator of a bounded `V`-elliptic bilinear form.  All six are one
predicate, `AtkinsonHan.Ch11.IsVariationalInequalitySolution`, which is the backbone's
`IsVariationalInequalitySolution` written with the book's `≥`; the identification is
`isVariationalInequalitySolution_iff`, and the four unfoldings the book uses are
`isVariationalInequalitySolution_zero_iff`, `..._univ_iff`, `..._univ_zero_iff` and
`..._toOperator_iff`.

Because the six displays differ only in the arguments of that one predicate,
**Theorem 11.3.9 is a single theorem covering (11.3.12), (11.3.13) and (11.3.14)**, and
Theorem 11.3.6 is Theorem 11.3.1 at `j = 0`.

The book's vocabulary is already in this surface: strong monotonicity (11.3.1) is
`AtkinsonHan.Ch05.StronglyMonotoneWith`, introduced for Theorem 5.1.4, and the Lipschitz condition
(11.3.2) crosses to Mathlib's `LipschitzWith` by `AtkinsonHan.Ch05.lipschitzWith_toNNReal_iff`.
`V`-ellipticity of a bilinear form is `AtkinsonHan.BilinForm.IsEllipticWith` of §8.3.

## Main results

* `lemma_11_3_5` — a convex lower semicontinuous functional on a closed convex set has a
  continuous affine minorant.
* `theorem_11_3_1` — unique solvability of (11.3.3) and Lipschitz dependence on `f`.
* `theorem_11_3_6` — Stampacchia's theorem, the inequality of the first kind.
* `theorem_11_3_7` — the inequality of the second kind.
* `lemma_11_3_8` — Minty's lemma, the equivalent form (11.3.10) with `A` at the test point.
* `theorem_11_3_9` — the bilinear-form problems (11.3.12)–(11.3.14).
* `isBestApprox_energy_of_theorem_11_3_9` — for symmetric `a` and `j = 0` the solution is the best
  approximation to the solution of the variational equation in the energy norm.
* `exercise_11_3_2`, `exercise_11_3_3`, `exercise_11_3_10`, `exercise_11_3_13`.

## Deviations from the book

Minty's lemma is stated with **right-continuity of `A` along the segments of `K` issuing from
`u`**, which is what the proof consumes, rather than with the book's continuity of `A` on the
finite-dimensional subspaces of `V`; the latter implies it, because the segment from `u` to `v`
lies in the span of `u` and `v`.  `continuousWithinAt_segment_of_continuous` records the cheap
sufficient condition, which already covers the Lipschitz operators of Theorem 11.3.1.

Not formalized: Theorem 11.3.12 (`W^{2,p}` regularity of the obstacle problem, quoted from
Brezis–Stampacchia), Examples 11.3.10 and 11.3.11 and the one-dimensional solution formula
following them, and Exercises 11.3.1, 11.3.4–11.3.9, 11.3.11 and 11.3.12, all of which name a
domain.
-/

open Filter Set Topology
open scoped InnerProductSpace

namespace AtkinsonHan.Ch11

/-! ### Lemma 11.3.5: the affine minorant -/

/-- **Lemma 11.3.5.**  A convex, lower semicontinuous functional on a nonempty closed convex
subset `K` of a real normed space is bounded below there by a continuous affine functional,
`j v ≥ ℓ(v) + c` for all `v ∈ K`.

The book proves it by separating the epigraph of `j` from a point below its graph; that separation
argument is Mathlib's `ConvexOn.exists_affine_le_of_lt`.  The book's `j : V → ℝ ∪ {+∞}` is proper,
so its effective domain is a set on which it is real-valued, and that set is the `K` here. -/
theorem lemma_11_3_5 {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {K : Set W}
    (hKne : K.Nonempty) (hKcl : IsClosed K) {j : W → ℝ} (hj : ConvexOn ℝ K j)
    (hjlsc : LowerSemicontinuousOn j K) : ∃ (ℓ : W →L[ℝ] ℝ) (c : ℝ), ∀ v ∈ K, ℓ v + c ≤ j v := by
  obtain ⟨x₀, hx₀⟩ := hKne
  obtain ⟨l, c, hle, -⟩ :=
    ConvexOn.exists_affine_le_of_lt (𝕜 := ℝ) (a := j x₀ - 1) hx₀ (by linarith) hKcl hjlsc hj
  exact ⟨l, c, fun z hz => by simpa using hle ⟨z, hz⟩⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The variational inequality (11.3.3) and its five variants -/

/-- **The elliptic variational inequality (11.3.3).**  `u ∈ K` satisfies

  `(A u, v - u) + j(v) - j(u) ≥ (f, v - u)`  for every `v ∈ K`.

The inequality of the first kind (11.3.8) is `j = 0`, that of the second kind (11.3.9) is
`K = Set.univ`, and (11.3.12)–(11.3.14) are the same three with `A` the operator of a bilinear
form.  This is the backbone's `IsVariationalInequalitySolution`
(`isVariationalInequalitySolution_iff`); the datum is a vector `f` rather than a functional, which
is the book's own Remark 11.3.4. -/
def IsVariationalInequalitySolution (A : V → V) (j : V → ℝ) (f : V) (K : Set V) (u : V) : Prop :=
  u ∈ K ∧ ∀ v ∈ K, ⟪A u, v - u⟫_ℝ + j v - j u ≥ ⟪f, v - u⟫_ℝ

/-- (11.3.3) is the backbone's variational inequality. -/
theorem isVariationalInequalitySolution_iff (A : V → V) (j : V → ℝ) (f : V) (K : Set V) (u : V) :
    IsVariationalInequalitySolution A j f K u ↔
      _root_.IsVariationalInequalitySolution A j f K u := Iff.rfl

/-- **(11.3.8), the inequality of the first kind.**  With `j = 0` the variational inequality reads
`(A u, v - u) ≥ (f, v - u)` for all `v ∈ K`. -/
theorem isVariationalInequalitySolution_zero_iff (A : V → V) (f : V) (K : Set V) (u : V) :
    IsVariationalInequalitySolution A 0 f K u ↔
      u ∈ K ∧ ∀ v ∈ K, ⟪A u, v - u⟫_ℝ ≥ ⟪f, v - u⟫_ℝ := by
  simp [IsVariationalInequalitySolution]

/-- **(11.3.9), the inequality of the second kind.**  With `K = V` the membership clause is
vacuous and the test vectors range over the whole space. -/
theorem isVariationalInequalitySolution_univ_iff (A : V → V) (j : V → ℝ) (f : V) (u : V) :
    IsVariationalInequalitySolution A j f univ u ↔
      ∀ v, ⟪A u, v - u⟫_ℝ + j v - j u ≥ ⟪f, v - u⟫_ℝ := by
  simp [IsVariationalInequalitySolution]

/-- On the whole space and with `j = 0` the variational inequality degenerates to the equation
`A u = f`: testing at `u + w` and at `u - w` turns the inequality into an identity.  This is what
makes Exercises 11.3.2 and 11.3.13 corollaries of Theorem 11.3.6. -/
theorem isVariationalInequalitySolution_univ_zero_iff (A : V → V) (f : V) (u : V) :
    IsVariationalInequalitySolution A 0 f univ u ↔ A u = f := by
  rw [isVariationalInequalitySolution_zero_iff]
  constructor
  · rintro ⟨-, h⟩
    refine (ext_inner_right ℝ fun w => ?_).symm
    have h₁ := h (u + w) (mem_univ _)
    have h₂ := h (u - w) (mem_univ _)
    rw [show u + w - u = w by abel] at h₁
    rw [show u - w - u = -w by abel, inner_neg_right, inner_neg_right] at h₂
    linarith
  · rintro rfl
    exact ⟨mem_univ _, fun v _ => le_rfl⟩

/-! ### Theorem 11.3.1 and its two specializations -/

/-- The book's hypothesis (11.3.1) in the shape the backbone takes it. -/
private theorem isStronglyMonotoneWith_of {A : V → V} {c : ℝ}
    (hmono : Ch05.StronglyMonotoneWith A c) : IsStronglyMonotoneWith ℝ A c :=
  fun x y => by simpa using hmono x y

section Existence

variable [CompleteSpace V] {A : V → V} {c₀ M : ℝ} {j : V → ℝ} {K : Set V}

/-- **Theorem 11.3.1.**  Let `K` be a nonempty closed convex subset of a real Hilbert space `V`,
let `A : V → V` be strongly monotone (11.3.1) with constant `c₀ > 0` and Lipschitz (11.3.2) with
constant `M ≥ 0`, and let `j : V → ℝ` be convex and lower semicontinuous on `K`.  Then the
variational inequality (11.3.3) has exactly one solution for every `f ∈ V`, and the solution
depends Lipschitz continuously on the datum, `‖u₁ - u₂‖ ≤ (1/c₀) ‖f₁ - f₂‖`.

Neither Lipschitz continuity nor convexity of `j` is used for the second clause; that is the
backbone's `IsVariationalInequalitySolution.norm_sub_le`. -/
theorem theorem_11_3_1 (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K) (hc₀ : 0 < c₀)
    (hM : 0 ≤ M) (hmono : Ch05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖) (hj : ConvexOn ℝ K j)
    (hjlsc : LowerSemicontinuousOn j K) :
    (∀ f : V, ∃! u, IsVariationalInequalitySolution A j f K u) ∧
      ∀ f₁ f₂ u₁ u₂ : V, IsVariationalInequalitySolution A j f₁ K u₁ →
        IsVariationalInequalitySolution A j f₂ K u₂ → ‖u₁ - u₂‖ ≤ 1 / c₀ * ‖f₁ - f₂‖ := by
  refine ⟨fun f => existsUnique_isVariationalInequalitySolution hKne hKcl hKcv hc₀
      (isStronglyMonotoneWith_of hmono) ((Ch05.lipschitzWith_toNNReal_iff hM).1 hlip) hj hjlsc f,
    fun f₁ f₂ u₁ u₂ h₁ h₂ => ?_⟩
  have h := IsVariationalInequalitySolution.norm_sub_le hc₀ (isStronglyMonotoneWith_of hmono)
    h₁ h₂
  rwa [one_div, inv_mul_eq_div]

/-- **Theorem 11.3.6, Stampacchia's theorem.**  The inequality of the first kind (11.3.8) — the
case `j = 0` of (11.3.3) — has exactly one solution for every `f`, depending Lipschitz
continuously on `f`.  `isVariationalInequalitySolution_zero_iff` unfolds the statement to the
book's display. -/
theorem theorem_11_3_6 (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K) (hc₀ : 0 < c₀)
    (hM : 0 ≤ M) (hmono : Ch05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖) :
    (∀ f : V, ∃! u, IsVariationalInequalitySolution A 0 f K u) ∧
      ∀ f₁ f₂ u₁ u₂ : V, IsVariationalInequalitySolution A 0 f₁ K u₁ →
        IsVariationalInequalitySolution A 0 f₂ K u₂ → ‖u₁ - u₂‖ ≤ 1 / c₀ * ‖f₁ - f₂‖ :=
  theorem_11_3_1 hKne hKcl hKcv hc₀ hM hmono hlip (convexOn_const 0 hKcv)
    lowerSemicontinuousOn_const

/-- **Theorem 11.3.7.**  The inequality of the second kind (11.3.9) — the case `K = V` of
(11.3.3), for a `j` convex and lower semicontinuous on the whole space — has exactly one solution
for every `f`, depending Lipschitz continuously on `f`.

The book's `j` takes values in `ℝ ∪ {+∞}` and is proper; a real-valued `j` on the whole space is
that hypothesis with the effective domain equal to `V`, which is what makes `K = Set.univ` the
right reading. -/
theorem theorem_11_3_7 (hc₀ : 0 < c₀) (hM : 0 ≤ M) (hmono : Ch05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖) (hj : ConvexOn ℝ univ j)
    (hjlsc : LowerSemicontinuous j) :
    (∀ f : V, ∃! u, IsVariationalInequalitySolution A j f univ u) ∧
      ∀ f₁ f₂ u₁ u₂ : V, IsVariationalInequalitySolution A j f₁ univ u₁ →
        IsVariationalInequalitySolution A j f₂ univ u₂ → ‖u₁ - u₂‖ ≤ 1 / c₀ * ‖f₁ - f₂‖ :=
  theorem_11_3_1 univ_nonempty isClosed_univ convex_univ hc₀ hM hmono hlip hj
    (hjlsc.lowerSemicontinuousOn univ)

/-- **Exercise 11.3.13.**  For `A` strongly monotone and Lipschitz on a real Hilbert space the
equation `A u = f` has exactly one solution for every `f`, and it depends Lipschitz continuously
on `f`.  This is Theorem 11.3.6 at `K = V`, and it is the statement of Theorem 5.1.4. -/
theorem exercise_11_3_13 (hc₀ : 0 < c₀) (hM : 0 ≤ M) (hmono : Ch05.StronglyMonotoneWith A c₀)
    (hlip : ∀ v₁ v₂ : V, ‖A v₁ - A v₂‖ ≤ M * ‖v₁ - v₂‖) :
    (∀ f : V, ∃! u, A u = f) ∧
      ∀ f₁ f₂ u₁ u₂ : V, A u₁ = f₁ → A u₂ = f₂ → ‖u₁ - u₂‖ ≤ 1 / c₀ * ‖f₁ - f₂‖ := by
  obtain ⟨hex, hlipdep⟩ :=
    theorem_11_3_6 (K := (univ : Set V)) univ_nonempty isClosed_univ convex_univ hc₀ hM hmono hlip
  refine ⟨fun f => ?_, fun f₁ f₂ u₁ u₂ h₁ h₂ => ?_⟩
  · simpa only [isVariationalInequalitySolution_univ_zero_iff] using hex f
  · exact hlipdep f₁ f₂ u₁ u₂ ((isVariationalInequalitySolution_univ_zero_iff A f₁ u₁).2 h₁)
      ((isVariationalInequalitySolution_univ_zero_iff A f₂ u₂).2 h₂)

end Existence

/-! ### Lemma 11.3.8, Minty's lemma -/

/-- A continuous operator is right-continuous along every segment, which is the hypothesis of
Minty's lemma below.  In particular the Lipschitz operators of Theorem 11.3.1 satisfy it. -/
theorem continuousWithinAt_segment_of_continuous {A : V → V} (hA : Continuous A) (u v : V) :
    ContinuousWithinAt (fun t : ℝ => A (u + t • (v - u))) (Ioi 0) 0 :=
  (hA.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousWithinAt

/-- **Lemma 11.3.8, Minty's lemma.**  For a monotone `A` — strong monotonicity (11.3.1) with
constant `0` — a `j` convex on a convex `K`, and a point `u ∈ K` along whose segments in `K` the
operator is right-continuous, the variational inequality (11.3.3) is equivalent to the form
(11.3.10) with `A` evaluated at the test point:

  `(A v, v - u) + j(v) - j(u) ≥ (f, v - u)`  for every `v ∈ K`.

One direction is monotonicity; the other tests at `u + t (v - u)`, uses convexity of `j` and lets
`t → 0⁺`.  The book asks instead for continuity of `A` on the finite-dimensional subspaces of `V`,
which implies the hypothesis here because the segment from `u` to `v` lies in the span of `u` and
`v`; the weaker form is what the proof consumes and what a weak-limit argument can supply. -/
theorem lemma_11_3_8 {A : V → V} {j : V → ℝ} {f : V} {K : Set V} (hKcv : Convex ℝ K)
    (hj : ConvexOn ℝ K j) (hmono : Ch05.StronglyMonotoneWith A 0) {u : V} (hu : u ∈ K)
    (hA : ∀ v ∈ K, ContinuousWithinAt (fun t : ℝ => A (u + t • (v - u))) (Ioi 0) 0) :
    IsVariationalInequalitySolution A j f K u ↔
      ∀ v ∈ K, ⟪A v, v - u⟫_ℝ + j v - j u ≥ ⟪f, v - u⟫_ℝ :=
  IsVariationalInequalitySolution.iff_minty hKcv hj (isStronglyMonotoneWith_of hmono) hu hA

/-! ### Theorem 11.3.9 and the bilinear-form problems -/

section BilinearForm

variable [CompleteSpace V] {a : BilinForm V} {M α : ℝ}

/-- The variational inequality for the operator of a bilinear form, written with the form and the
functional themselves: `u ∈ K` and `a(u, v - u) + j(v) - j(u) ≥ ℓ(v - u)` for all `v ∈ K`.  This
is the book's (11.3.12), and (11.3.13), (11.3.14) are its cases `j = 0` and `K = V`. -/
theorem isVariationalInequalitySolution_toOperator_iff (hM : a.IsBoundedWith M) (j : V → ℝ)
    (ℓ : StrongDual ℝ V) (K : Set V) (u : V) :
    IsVariationalInequalitySolution (BilinForm.toOperator a hM) j (SesqForm.rieszRep ℓ) K u ↔
      u ∈ K ∧ ∀ v ∈ K, a u (v - u) + j v - j u ≥ ℓ (v - u) := by
  simp only [IsVariationalInequalitySolution, BilinForm.inner_toOperator,
    BilinForm.inner_rieszRep]

/-- **Theorem 11.3.9.**  For a bounded, `V`-elliptic bilinear form `a` — not assumed symmetric — a
functional `ℓ ∈ V'`, a nonempty closed convex `K` and a `j` convex and lower semicontinuous on
`K`, the variational inequality

  `u ∈ K`,  `a(u, v - u) + j(v) - j(u) ≥ ℓ(v - u)`  for all `v ∈ K`

has exactly one solution, and it depends Lipschitz continuously on `ℓ`, `‖u₁ - u₂‖ ≤ (1/α)‖ℓ₁ -
ℓ₂‖`.

**This one statement is (11.3.12), (11.3.13) and (11.3.14) at once**: those three displays differ
only in the arguments `j` and `K` of one predicate, the second being the case `j = 0` and the
third the case `K = V`. -/
theorem theorem_11_3_9 (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α)
    {K : Set V} (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K) {j : V → ℝ}
    (hj : ConvexOn ℝ K j) (hjlsc : LowerSemicontinuousOn j K) :
    (∀ ℓ : StrongDual ℝ V, ∃! u, u ∈ K ∧ ∀ v ∈ K, a u (v - u) + j v - j u ≥ ℓ (v - u)) ∧
      ∀ (ℓ₁ ℓ₂ : StrongDual ℝ V) (u₁ u₂ : V),
        (u₁ ∈ K ∧ ∀ v ∈ K, a u₁ (v - u₁) + j v - j u₁ ≥ ℓ₁ (v - u₁)) →
        (u₂ ∈ K ∧ ∀ v ∈ K, a u₂ (v - u₂) + j v - j u₂ ≥ ℓ₂ (v - u₂)) →
        ‖u₁ - u₂‖ ≤ 1 / α * ‖ℓ₁ - ℓ₂‖ := by
  have hcoer : SesqForm.IsCoerciveWith (a.toCLM hM) α := (a.isEllipticWith_iff_isCoerciveWith hM).1
    ha
  have hmono : IsStronglyMonotoneWith ℝ (BilinForm.toOperator a hM : V → V) α :=
    LinearMap.IsCoerciveWith.isStronglyMonotoneWith
      ((SesqForm.isCoerciveWith_iff_toOperator (a.toCLM hM) α).mp hcoer)
  have hriesz : ∀ ℓ₁ ℓ₂ : StrongDual ℝ V,
      SesqForm.rieszRep ℓ₁ - SesqForm.rieszRep ℓ₂ = SesqForm.rieszRep (V := V) (ℓ₁ - ℓ₂) := by
    intro ℓ₁ ℓ₂
    refine ext_inner_right ℝ fun v => ?_
    rw [inner_sub_left, SesqForm.inner_rieszRep, SesqForm.inner_rieszRep, SesqForm.inner_rieszRep]
    simp
  constructor
  · intro ℓ
    exact (existsUnique_congr fun u => isVariationalInequalitySolution_toOperator_iff hM j ℓ K u).mp
      (existsUnique_isVariationalInequalitySolution_of_isCoercive hα hcoer hKne hKcl hKcv hj
        hjlsc ℓ)
  · intro ℓ₁ ℓ₂ u₁ u₂ h₁ h₂
    have h := IsVariationalInequalitySolution.norm_sub_le hα hmono
      ((isVariationalInequalitySolution_toOperator_iff hM j ℓ₁ K u₁).2 h₁)
      ((isVariationalInequalitySolution_toOperator_iff hM j ℓ₂ K u₂).2 h₂)
    rw [hriesz ℓ₁ ℓ₂, SesqForm.norm_rieszRep] at h
    rwa [one_div, inv_mul_eq_div]

/-- **The remark following Example 11.3.11.**  For a symmetric `V`-elliptic form `a` and `j = 0`,
the solution `u` of (11.3.13) is the best approximation in `K`, measured in the energy norm
`‖·‖_a`, to the solution `w` of the variational equation `a(w, v) = ℓ(v)`.

So the inequality can be solved by solving the equation and then projecting onto `K` in the energy
inner product. -/
theorem isBestApprox_energy_of_theorem_11_3_9 (hM : a.IsBoundedWith M) (hα : 0 < α)
    (ha : a.IsEllipticWith α) (hs : LinearMap.BilinForm.IsSymm a) (ℓ : StrongDual ℝ V)
    {K : Set V} (hKcv : Convex ℝ K) {w u : V} (hw : ∀ v, a w v = ℓ v)
    (hu : u ∈ K ∧ ∀ v ∈ K, a u (v - u) ≥ ℓ (v - u)) :
    ∀ v ∈ K, a.energyNorm (w - u) ≤ a.energyNorm (w - v) := by
  have hsc : (BilinForm.toOperator a hM : V →ₗ[ℝ] V).IsSymmetricCoercive :=
    BilinForm.isSymmetricCoercive_toOperator hM hα ha hs
  have hwr : BilinForm.toOperator a hM w = SesqForm.rieszRep ℓ :=
    (BilinForm.toOperator_eq_rieszRep_iff hM ℓ w).2 hw
  have hsol : _root_.IsVariationalInequalitySolution
      (BilinForm.toOperator a hM : V → V) 0 (SesqForm.rieszRep ℓ) K u := by
    refine (isVariationalInequalitySolution_toOperator_iff hM 0 ℓ K u).2 ⟨hu.1, fun v hv => ?_⟩
    simpa using hu.2 v hv
  have hbest := IsVariationalInequalitySolution.isBestApprox_energy hsc hKcv hwr hsol
  intro v hv
  have h := hbest.2 (WithEnergy.equiv _ hsc v) ⟨v, hv, rfl⟩
  rw [← map_sub, ← map_sub, WithEnergy.norm_equiv, WithEnergy.norm_equiv] at h
  rwa [a.energyNorm_eq_energyNorm_toOperator hM, a.energyNorm_eq_energyNorm_toOperator hM]

/-- **Exercise 11.3.2.**  Theorem 11.3.6 generalizes the Lax–Milgram lemma: taking `K = V` and `A`
the operator of a bounded `V`-elliptic bilinear form turns the inequality of the first kind into
the variational equation `a(u, v) = ℓ(v)`, and its unique solvability is Theorem 8.3.4. -/
theorem exercise_11_3_2 (hM : a.IsBoundedWith M) (hα : 0 < α) (ha : a.IsEllipticWith α)
    (ℓ : StrongDual ℝ V) : ∃! u, ∀ v, a u v = ℓ v := by
  have hmono : Ch05.StronglyMonotoneWith (BilinForm.toOperator a hM : V → V) α :=
    fun x y => Ch08.stronglyMonotone_toOperator hM ha x y
  have hlip : ∀ v₁ v₂ : V, ‖BilinForm.toOperator a hM v₁ - BilinForm.toOperator a hM v₂‖
      ≤ ‖BilinForm.toOperator a hM‖ * ‖v₁ - v₂‖ := by
    intro v₁ v₂
    rw [← map_sub]
    exact (BilinForm.toOperator a hM).le_opNorm _
  obtain ⟨hex, -⟩ := theorem_11_3_6 (K := (univ : Set V)) univ_nonempty isClosed_univ convex_univ
    hα (norm_nonneg (BilinForm.toOperator a hM)) hmono hlip
  obtain ⟨u, hu, huniq⟩ := hex (SesqForm.rieszRep ℓ)
  rw [isVariationalInequalitySolution_univ_zero_iff] at hu
  refine ⟨u, (BilinForm.toOperator_eq_rieszRep_iff hM ℓ u).1 hu, fun y hy => ?_⟩
  exact huniq y ((isVariationalInequalitySolution_univ_zero_iff _ _ y).2
    ((BilinForm.toOperator_eq_rieszRep_iff hM ℓ y).2 hy))

/-- **Exercise 11.3.3.**  When `K` is a convex cone, the inequality of the first kind (11.3.13) is
equivalent to the pair of relations `a(u, v) ≥ ℓ(v)` for all `v ∈ K` and `a(u, u) = ℓ(u)`.

Testing at `2u` and at `0` gives the equality and testing at `u + v` the inequality; conversely
subtracting the equality from the inequality at `v` returns the variational inequality. -/
theorem exercise_11_3_3 (hM : a.IsBoundedWith M) {K : Set V} (hKcv : Convex ℝ K)
    (hKcone : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K, t • x ∈ K) (ℓ : StrongDual ℝ V) {u : V} (hu : u ∈ K) :
    (u ∈ K ∧ ∀ v ∈ K, a u (v - u) ≥ ℓ (v - u)) ↔
      ((∀ v ∈ K, a u v ≥ ℓ v) ∧ a u u = ℓ u) := by
  have hiff := IsVariationalInequalitySolution.iff_of_isCone
    (A := (BilinForm.toOperator a hM : V → V)) (f := SesqForm.rieszRep ℓ) hKcv hKcone hu
  have hz : IsVariationalInequalitySolution (BilinForm.toOperator a hM) 0
      (SesqForm.rieszRep ℓ) K u ↔ (u ∈ K ∧ ∀ v ∈ K, a u (v - u) ≥ ℓ (v - u)) := by
    rw [isVariationalInequalitySolution_toOperator_iff hM 0 ℓ K u]
    simp
  refine hz.symm.trans (hiff.trans ?_)
  simp only [BilinForm.inner_toOperator, BilinForm.inner_rieszRep, ge_iff_le]

/-- **Exercise 11.3.10.**  For an inequality of the second kind (11.3.14) whose `j` is convex and
positively homogeneous, the inequality is equivalent to `a(u, v) + j(v) ≥ ℓ(v)` for every `v`
together with `a(u, u) + j(u) = ℓ(u)`.

Convexity and positive homogeneity make `j` subadditive, which is what turns the test at `u + v`
into the inequality at `v`. -/
theorem exercise_11_3_10 (hM : a.IsBoundedWith M) {j : V → ℝ} (hj : ConvexOn ℝ univ j)
    (hhom : ∀ t : ℝ, 0 < t → ∀ v : V, j (t • v) = t * j v) (ℓ : StrongDual ℝ V) {u : V} :
    (∀ v, a u (v - u) + j v - j u ≥ ℓ (v - u)) ↔
      ((∀ v, a u v + j v ≥ ℓ v) ∧ a u u + j u = ℓ u) := by
  have hiff := IsVariationalInequalitySolution.iff_of_isPositiveHomogeneous
    (A := (BilinForm.toOperator a hM : V → V)) (f := SesqForm.rieszRep ℓ) hj hhom (u := u)
  simp only [BilinForm.inner_toOperator, BilinForm.inner_rieszRep] at hiff
  rw [← hiff, ← isVariationalInequalitySolution_iff,
    isVariationalInequalitySolution_univ_iff]
  simp only [BilinForm.inner_toOperator, BilinForm.inner_rieszRep]

end BilinearForm

end AtkinsonHan.Ch11
