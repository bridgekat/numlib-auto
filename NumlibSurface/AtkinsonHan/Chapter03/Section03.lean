import Numlib.Approximation.BestApprox
import NumlibSurface.AtkinsonHan.Chapter02.Section04
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Atkinson–Han §3.3: best approximation

Statements from Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework* (3rd ed.), §3.3. The book's best approximation (3.3.3) is the backbone's
`IsBestApprox` (`Numlib.Approximation.BestApprox`); `isBestApprox_iff_norm_eq_iInf` is the bridge
to the book's `‖u - û‖ = inf_{v ∈ K} ‖u - v‖` phrasing.

Definitions 3.3.1–3.3.2 (convex set, convex and strictly convex functional) are Mathlib's
`Convex ℝ K`, `ConvexOn ℝ K f` and `StrictConvexOn ℝ K f`; the book quantifies `λ ∈ (0,1)` where
Mathlib uses `[0,1]`, which is the same condition (`convex_iff_openSegment_subset`). The
convex-combination statement (3.3.1) is Mathlib's `Convex.sum_mem`, and closed versus sequentially
closed sets (Definition 3.3.3) agree in metric spaces (`isSeqClosed_iff_isClosed`), as do
sequential and topological lower semicontinuity.

## Book-specific definitions

* `WeakSeqTendsto` — weak sequential convergence (Definition 3.3.3), only the sequential form.
* `AreSeparated`, `AreStrictlySeparated` — Definition 3.3.6.
* `IsCoerciveFunctionalOn` — Definition 3.3.9. This is *not* the backbone's `IsCoercive`, which
  is the operator condition `re ⟪A x, x⟫ ≥ c ‖x‖²` (the book's "strongly monotone").
* `IsStrictlyNormed` — §3.3.4, equivalent to Mathlib's `StrictConvexSpace ℝ V`.
* `polyLE`, `rho` — the space `𝒫ₙ` of polynomials of degree `≤ n` on `[a, b]` and the best
  uniform approximation error `ρₙ(f)`.

## Main results

* `example_3_3_5` — the norm is weakly sequentially lower semicontinuous.
* `theorem_3_3_7` — strict separation of a compact convex set from a disjoint closed convex set.
* `theorem_3_3_13` — existence (and uniqueness) of minimizers on finite-dimensional closed sets.
* `theorem_3_3_15`, `theorem_3_3_16`, `example_3_3_17` — existence of best approximations.
* `theorem_3_3_18`, `theorem_3_3_21` — uniqueness under strict convexity of `‖·‖ᵖ`, resp. strict
  normedness.
* `exercise_3_3_8`, `exercise_3_3_8_rpow`, `exercise_3_3_9` — inner product spaces satisfy
  both criteria.

## Not formalized here

Theorems 3.3.8, 3.3.10, 3.3.11 (Mazur), 3.3.12 and 3.3.14 concern minimizers in reflexive Banach
spaces; they wait on weak sequential compactness (the book's Thm 2.7.5), which Mathlib does not
have. Theorems 3.3.19–3.3.20 (Chebyshev equioscillation) wait on the Haar condition and the
de la Vallée-Poussin theorem. Both are phase-3 backbone items.
-/

open Filter Topology Bornology

namespace AtkinsonHan.Ch03

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

/-- **Weak sequential convergence** `vₙ ⇀ u` (Definition 3.3.3): `ℓ(vₙ) → ℓ(u)` for every bounded
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

/-- **Coercive functional on `K`** (Definition 3.3.9): `f(v) → ∞ as ‖v‖ → ∞` within `K`.
This is unrelated to the backbone's `LinearMap.IsCoercive`, which is the operator inequality
`re ⟪A x, x⟫ ≥ c ‖x‖²` (the book's "strongly monotone"). -/
def IsCoerciveFunctionalOn (f : E → ℝ) (K : Set E) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, ∀ v ∈ K, R ≤ ‖v‖ → M ≤ f v

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

/-- A weakly convergent sequence is bounded: uniform boundedness applied to the images of the
`vₙ` in the (complete) double dual. -/
private theorem exists_norm_le_of_weakSeqTendsto {v : ℕ → V} {u : V}
    (h : WeakSeqTendsto 𝕜 v u) : ∃ C : ℝ, ∀ n, ‖v n‖ ≤ C := by
  have hb : ∀ ℓ : StrongDual 𝕜 V,
      ∃ C : ℝ, ∀ n, ‖NormedSpace.inclusionInDoubleDual 𝕜 V (v n) ℓ‖ ≤ C := by
    intro ℓ
    exact Ch02.exists_norm_le_of_tendsto (h ℓ)
  obtain ⟨C, hC⟩ := banach_steinhaus hb
  refine ⟨C, fun n => ?_⟩
  rw [← (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map (v n)]
  exact hC n

/-- **Example 3.3.5.** The norm is weakly sequentially lower semicontinuous:
`vₙ ⇀ u` implies `‖u‖ ≤ liminf ‖vₙ‖`. -/
theorem example_3_3_5 (v : ℕ → V) (u : V) (hweak : WeakSeqTendsto 𝕜 v u) :
    ‖u‖ ≤ liminf (fun n => ‖v n‖) atTop := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_weakSeqTendsto hweak
  obtain ⟨ℓ, hℓ, hval⟩ := exists_dual_vector'' 𝕜 u
  have hlim : Tendsto (fun n => ‖ℓ (v n)‖) atTop (𝓝 ‖ℓ u‖) := (hweak ℓ).norm
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop fun n => ‖v n‖ := by
    refine ⟨C, fun a ha => ?_⟩
    rw [Filter.eventually_map] at ha
    obtain ⟨n, hn⟩ := ha.exists
    exact hn.trans (hC n)
  have hle : ∀ n, ‖ℓ (v n)‖ ≤ ‖v n‖ := fun n =>
    (ℓ.le_opNorm (v n)).trans (by simpa using mul_le_mul_of_nonneg_right hℓ (norm_nonneg (v n)))
  calc ‖u‖ = ‖ℓ u‖ := by rw [hval, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg u)]
    _ = liminf (fun n => ‖ℓ (v n)‖) atTop := hlim.liminf_eq.symm
    _ ≤ liminf (fun n => ‖v n‖) atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall hle) hlim.isBoundedUnder_ge hcobdd

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

/-! ### Theorem 3.3.13: minimizers on finite-dimensional closed sets -/

section Minimization

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- A closed bounded subset of a finite-dimensional subspace is compact: the finite-dimensional
subspace is a proper metric space. -/
private theorem isCompact_of_subset_finiteDimensional {K : Set V} (S : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hcl : IsClosed K) (hbd : IsBounded K) : IsCompact K := by
  have : ProperSpace S := FiniteDimensional.proper 𝕜 S
  have hpre : IsCompact (Subtype.val ⁻¹' K : Set S) := by
    refine Metric.isCompact_of_isClosed_isBounded (hcl.preimage continuous_subtype_val) ?_
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hbd
    refine (Metric.isBounded_closedBall (x := (0 : S)) (r := C)).subset fun w hw => ?_
    simpa [Metric.mem_closedBall, dist_zero_right] using hC _ hw
  have himg : K = Subtype.val '' (Subtype.val ⁻¹' K : Set S) := by
    ext x
    exact ⟨fun hx => ⟨⟨x, hKS hx⟩, hx, rfl⟩, by rintro ⟨w, hw, rfl⟩; exact hw⟩
  rw [himg]
  exact hpre.image continuous_subtype_val

set_option linter.unusedVariables false in
/-- **Theorem 3.3.13.** A lower semicontinuous functional on a nonempty closed subset `K` of a
finite-dimensional subspace attains its minimum, provided `K` is bounded or `f` is coercive on
`K`. The book's convexity hypotheses on `K` and `f` are kept for faithfulness; neither the book's
proof nor this one uses them at this rung. -/
theorem theorem_3_3_13 [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] {K : Set V} (S : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hcl : IsClosed K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (f : V → ℝ) (hf : ConvexOn ℝ K f) (hlsc : LowerSemicontinuousOn f K)
    (h : IsBounded K ∨ IsCoerciveFunctionalOn f K) : ∃ u ∈ K, IsMinOn f K u := by
  rcases h with hbd | hcoer
  · exact hlsc.exists_isMinOn hne (isCompact_of_subset_finiteDimensional S hKS hcl hbd)
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨R, hR⟩ := hcoer (f v₀ + 1)
  set R' := max R ‖v₀‖ with hR'def
  set K' := K ∩ Metric.closedBall (0 : V) R' with hK'def
  have hsub : K' ⊆ K := Set.inter_subset_left
  have hv₀' : v₀ ∈ K' := ⟨hv₀, by simp [Metric.mem_closedBall, dist_zero_right, hR'def]⟩
  have hcpt : IsCompact K' :=
    isCompact_of_subset_finiteDimensional S (hsub.trans hKS)
      (hcl.inter Metric.isClosed_closedBall)
      (Metric.isBounded_closedBall.subset Set.inter_subset_right)
  obtain ⟨a, haK', hamin⟩ := (hlsc.mono hsub).exists_isMinOn ⟨v₀, hv₀'⟩ hcpt
  refine ⟨a, hsub haK', isMinOn_iff.2 fun v hv => ?_⟩
  by_cases hvb : v ∈ Metric.closedBall (0 : V) R'
  · exact isMinOn_iff.1 hamin v ⟨hv, hvb⟩
  · have hnorm : R ≤ ‖v‖ := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le, hR'def] at hvb
      exact (le_max_left R ‖v₀‖).trans hvb.le
    have h1 : f v₀ + 1 ≤ f v := hR v hv hnorm
    have h2 : f a ≤ f v₀ := isMinOn_iff.1 hamin v₀ hv₀'
    linarith

/-- **Theorem 3.3.13**, uniqueness clause: a strictly convex functional has at most one
minimizer. -/
theorem theorem_3_3_13_unique [NormedSpace ℝ V] {K : Set V} {f : V → ℝ} (hf : StrictConvexOn ℝ K f)
    {u₁ u₂ : V} (hu₁ : IsMinOn f K u₁) (hu₂ : IsMinOn f K u₂) (h₁ : u₁ ∈ K) (h₂ : u₂ ∈ K) :
    u₁ = u₂ :=
  hf.eq_of_isMinOn hu₁ hu₂ h₁ h₂

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

end Polynomials

/-! ### Theorems 3.3.18 and 3.3.21: uniqueness of best approximations -/

section Uniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `‖·‖ᵖ` is strictly convex for some `p ≥ 1` then the space is strictly convex, so the
backbone's `IsBestApprox.unique` applies. (An upstreaming candidate once a second consumer
appears.) -/
private theorem strictConvexSpace_of_strictConvexOn_norm_rpow {p : ℝ} (hp : 1 ≤ p)
    (hconv : StrictConvexOn ℝ (Set.univ : Set E) fun v : E => ‖v‖ ^ p) :
    StrictConvexSpace ℝ E := by
  refine StrictConvexSpace.of_norm_combo_lt_one fun x y hx hy hne => ?_
  refine ⟨1 / 2, 1 / 2, by norm_num, ?_⟩
  have h := hconv.2 (Set.mem_univ x) (Set.mem_univ y) hne (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
  simp only [hx, hy, Real.one_rpow, smul_eq_mul] at h
  by_contra hge
  rw [not_lt] at hge
  have hmono : (1 : ℝ) ^ p ≤ ‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y‖ ^ p :=
    Real.rpow_le_rpow zero_le_one hge (by linarith)
  rw [Real.one_rpow] at hmono
  linarith

set_option linter.unusedVariables false in
/-- **Theorem 3.3.18.** If `‖·‖ᵖ` is strictly convex for some `p ≥ 1`, best approximations from a
convex set are unique. -/
theorem theorem_3_3_18 {p : ℝ} (hp : 1 ≤ p)
    (hconv : StrictConvexOn ℝ (Set.univ : Set E) fun v : E => ‖v‖ ^ p) {K : Set E}
    (hK : Convex ℝ K) {u v₁ v₂ : E} (h₁ : IsBestApprox K u v₁) (h₂ : IsBestApprox K u v₂) :
    v₁ = v₂ :=
  have : StrictConvexSpace ℝ E := strictConvexSpace_of_strictConvexOn_norm_rpow hp hconv
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
theorem exercise_3_3_8 : StrictConvexOn ℝ (Set.univ : Set H) fun v : H => ‖v‖ ^ 2 := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have hexp : ‖a • x + b • y‖ ^ 2
      = a ^ 2 * ‖x‖ ^ 2 + 2 * (a * b) * inner ℝ x y + b ^ 2 * ‖y‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb]
    ring
  have hdiff : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := norm_sub_sq_real x y
  have hpos : 0 < a * b * ‖x - y‖ ^ 2 := by
    have hne : x - y ≠ 0 := sub_ne_zero.2 hxy
    have : 0 < ‖x - y‖ := norm_pos_iff.2 hne
    positivity
  have hkey : a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 - ‖a • x + b • y‖ ^ 2 = a * b * ‖x - y‖ ^ 2 := by
    have hb' : b = 1 - a := by linarith
    rw [hexp, hdiff, hb']
    ring
  simp only [smul_eq_mul]
  linarith

/-- **Exercise 3.3.8**, in the real-exponent form that Theorem 3.3.18 consumes (`p = 2`). -/
theorem exercise_3_3_8_rpow :
    StrictConvexOn ℝ (Set.univ : Set H) fun v : H => ‖v‖ ^ (2 : ℝ) := by
  simpa only [Real.rpow_two] using (exercise_3_3_8 (H := H))

/-- **Exercise 3.3.9.** Inner product spaces are strictly normed. -/
theorem exercise_3_3_9 : IsStrictlyNormed H :=
  isStrictlyNormed_iff_strictConvexSpace.2 inferInstance

end InnerProduct

end AtkinsonHan.Ch03
