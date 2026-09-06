import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Existence of minimizers of a functional on a closed set

The finite-dimensional existence theorem of [han2009theoretical] (their Thm 3.3.13): a lower
semicontinuous functional on a nonempty closed subset `K` of a finite-dimensional subspace attains
its infimum as soon as `K` is bounded, or the functional is coercive on `K` in the sense of
`IsCoerciveFunctionalOn` — `f x → ∞` as `‖x‖ → ∞` inside `K`.  Neither the set nor the functional
needs to be convex: convexity enters only in the uniqueness clause `IsMinOn.eq_of_strictConvexOn`.

The infinite-dimensional theorems of the same section — existence on a closed convex set of a
*reflexive* space — are in `Numlib.Variational.WeakMinimization`.  They rest on weak sequential
compactness of bounded sets, which is what reflexivity is used for and which that module carries as
the class `WeaklySeqCompactSpace`, Mathlib having no reflexivity class of its own.
-/

open Bornology

section Coercive

variable {V : Type*} [SeminormedAddCommGroup V]

/-- A functional is **coercive on a set** when it tends to `+∞` along the set as the norm grows: for
every level `M` there is a radius `R` beyond which `f ≥ M` on `K` ([han2009theoretical], Def 3.3.9).

This is the condition on a *functional*, and is unrelated to the coercivity of an *operator* or of a
sesquilinear form, `re ⟪A x, x⟫ ≥ c ‖x‖²`, which is a lower bound of quadratic order rather than a
growth condition. -/
def IsCoerciveFunctionalOn (f : V → ℝ) (K : Set V) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, ∀ x ∈ K, R ≤ ‖x‖ → M ≤ f x

/-- A functional is coercive on every subset of a bounded set, vacuously: take `R` past the bound.
-/
theorem IsCoerciveFunctionalOn.of_isBounded {f : V → ℝ} {K : Set V} (hK : IsBounded K) :
    IsCoerciveFunctionalOn f K := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hK
  exact fun M => ⟨C + 1, fun x hx hx' => absurd (hC x hx) (by linarith)⟩

/-- Coercivity is inherited by subsets. -/
theorem IsCoerciveFunctionalOn.mono {f : V → ℝ} {K K' : Set V} (h : IsCoerciveFunctionalOn f K)
    (hKK : K' ⊆ K) : IsCoerciveFunctionalOn f K' :=
  fun M => (h M).imp fun _ hR x hx => hR x (hKK hx)

end Coercive

section Existence

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [LocallyCompactSpace 𝕜]

/-- A closed bounded subset of a finite-dimensional subspace is compact, because a
finite-dimensional subspace is a proper metric space. -/
theorem isCompact_of_isBounded_of_subset_finiteDimensional {K : Set V} (S : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hcl : IsClosed K) (hbd : IsBounded K) :
    IsCompact K := by
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

/-- **Existence of a minimizer** ([han2009theoretical], Thm 3.3.13): a lower semicontinuous
functional on a nonempty closed subset `K` of a finite-dimensional subspace `S` attains its minimum,
provided `K` is bounded or `f` is coercive on `K`.

The two cases are one argument.  Coercivity confines the search to a sublevel set, closed by lower
semicontinuity and bounded by coercivity; a bounded `K` is coercive on itself vacuously
(`IsCoerciveFunctionalOn.of_isBounded`), so only the coercive case is proved.  Convexity of `K` or
of `f`, which the book assumes, is not used: it is what `IsMinOn.eq_of_strictConvexOn` needs, not
what existence needs. -/
theorem exists_isMinOn_of_isClosed_of_finiteDimensional {K : Set V} (S : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hcl : IsClosed K) (hne : K.Nonempty) {f : V → ℝ}
    (hlsc : LowerSemicontinuousOn f K) (hf : IsCoerciveFunctionalOn f K) :
    ∃ u ∈ K, IsMinOn f K u := by
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨R, hR⟩ := hf (f v₀ + 1)
  set R' := max R ‖v₀‖ with hR'
  set K' := K ∩ Metric.closedBall (0 : V) R' with hK'
  have hsub : K' ⊆ K := Set.inter_subset_left
  have hv₀' : v₀ ∈ K' := ⟨hv₀, by simp [Metric.mem_closedBall, dist_zero_right, hR']⟩
  have hcpt : IsCompact K' :=
    isCompact_of_isBounded_of_subset_finiteDimensional S (hsub.trans hKS)
      (hcl.inter Metric.isClosed_closedBall)
      (Metric.isBounded_closedBall.subset Set.inter_subset_right)
  obtain ⟨a, haK', hamin⟩ := (hlsc.mono hsub).exists_isMinOn ⟨v₀, hv₀'⟩ hcpt
  refine ⟨a, hsub haK', isMinOn_iff.2 fun v hv => ?_⟩
  by_cases hvb : v ∈ Metric.closedBall (0 : V) R'
  · exact isMinOn_iff.1 hamin v ⟨hv, hvb⟩
  · have hnorm : R ≤ ‖v‖ := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le, hR'] at hvb
      exact (le_max_left R ‖v₀‖).trans hvb.le
    have h1 : f v₀ + 1 ≤ f v := hR v hv hnorm
    have h2 : f a ≤ f v₀ := isMinOn_iff.1 hamin v₀ hv₀'
    linarith

/-- `exists_isMinOn_of_isClosed_of_finiteDimensional` in the bounded case: a lower semicontinuous
functional on a nonempty closed bounded subset of a finite-dimensional subspace attains its minimum.
-/
theorem exists_isMinOn_of_isBounded_of_finiteDimensional {K : Set V} (S : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S] (hKS : K ⊆ S) (hcl : IsClosed K) (hbd : IsBounded K)
    (hne : K.Nonempty) {f : V → ℝ} (hlsc : LowerSemicontinuousOn f K) :
    ∃ u ∈ K, IsMinOn f K u :=
  exists_isMinOn_of_isClosed_of_finiteDimensional S hKS hcl hne hlsc
    (IsCoerciveFunctionalOn.of_isBounded hbd)

end Existence

section Uniqueness

variable {V : Type*} [AddCommMonoid V] [Module ℝ V]

/-- **Uniqueness of a minimizer** (the second clause of [han2009theoretical], Thm 3.3.13, and of
their Thm 3.3.12): a strictly convex functional has at most one minimizer on a set.  This is
Mathlib's `StrictConvexOn.eq_of_isMinOn` in the vocabulary of this module, kept so that the module
states the whole theorem. -/
theorem IsMinOn.eq_of_strictConvexOn {f : V → ℝ} {K : Set V} (hf : StrictConvexOn ℝ K f)
    {u₁ u₂ : V} (h₁ : IsMinOn f K u₁) (h₂ : IsMinOn f K u₂) (hu₁ : u₁ ∈ K) (hu₂ : u₂ ∈ K) :
    u₁ = u₂ :=
  StrictConvexOn.eq_of_isMinOn hf h₁ h₂ hu₁ hu₂

end Uniqueness
