import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
the class `WeaklySeqCompactSpace`.  Reflexivity itself is `NormedSpace.IsReflexive` of
`Numlib.Analysis.Normed.Module.Reflexive`, and `WeaklySeqCompactSpace.of_isReflexive` is the
instance that derives the class from it, so a reflexive space satisfies those hypotheses with no
further assumption.  Mathlib has no reflexivity class for normed spaces of its own: its
`Module.IsReflexive` is the algebraic double dual, a different condition.
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

/-- **A functional bounded below by `c ‖x‖^p − C ‖x‖` with `c > 0`, `p > 1`, is coercive**
(`IsCoerciveFunctionalOn`, [han2009theoretical] Definition 3.3.9): the power beats the linear
term. -/
theorem isCoerciveFunctionalOn_of_rpow_sub_mul_le {f : V → ℝ} {K : Set V} {c C r : ℝ}
    (hc : 0 < c) (hr : 1 < r)
    (hf : ∀ x ∈ K, c * ‖x‖ ^ r - C * ‖x‖ ≤ f x) : IsCoerciveFunctionalOn f K := by
  intro M
  have hr1 : 0 < r - 1 := by linarith
  refine ⟨max 1 (max M ((max (C + 1) 0 / c) ^ (1 / (r - 1)))), fun x hx hxR ↦ ?_⟩
  have h1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hxR
  have hM : M ≤ ‖x‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans hxR
  have hA : (max (C + 1) 0 / c) ^ (1 / (r - 1)) ≤ ‖x‖ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hxR
  -- `c ‖x‖^{r−1} ≥ C + 1`
  have hpow : max (C + 1) 0 / c ≤ ‖x‖ ^ (r - 1) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hA hr1.le
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hr1.ne', Real.rpow_one] at this
  have hkey : C + 1 ≤ c * ‖x‖ ^ (r - 1) := by
    rw [div_le_iff₀ hc] at hpow
    linarith [le_max_left (C + 1) 0]
  have hsplit : ‖x‖ ^ r = ‖x‖ ^ (r - 1) * ‖x‖ := by
    rw [← Real.rpow_add_one (by positivity : ‖x‖ ≠ 0)]
    ring_nf
  calc M ≤ ‖x‖ := hM
    _ ≤ (c * ‖x‖ ^ (r - 1) - C) * ‖x‖ := by nlinarith
    _ = c * ‖x‖ ^ r - C * ‖x‖ := by rw [hsplit]; ring
    _ ≤ f x := hf x hx

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

section StrongConvex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **A strongly convex functional is coercive**: if `f` is `m`-strongly convex on a set `K` with
`0 < m` and is bounded below on `K ∩ ball x₀ r` for one point `x₀ ∈ K` and one radius `r > 0`, then
`IsCoerciveFunctionalOn f K`.

Strong convexity alone does not give coercivity: a discontinuous linear functional `ℓ` on an
infinite-dimensional space is convex, so on a Hilbert space `x ↦ ℓ x + ‖x‖ ^ 2` is strongly convex
while tending to `-∞` along a suitable sequence, and it is unbounded below on every ball. A local
lower bound is therefore part of the hypotheses; lower semicontinuity at a point of `K` supplies
one, which is how `existsUnique_isMinOn_of_strongConvexOn` uses this.

The proof is the standard interpolation argument: for `y ∈ K` far from `x₀`, the point
`z = (1 - t) • x₀ + t • y` with `t = r / (2 ‖y - x₀‖)` lies in `K ∩ ball x₀ r`, so it is subject to
the lower bound, and the strong convexity inequality at `z` reads
`f y ≥ (m/4) ‖y - x₀‖² - A ‖y - x₀‖` with `A = 2 (|c| + |f x₀|) / r`: the quadratic term beats the
linear one. `StrongConvexOn K m f` is Mathlib's `UniformConvexOn K (fun ρ => m / 2 * ρ ^ 2) f`, so
a modulus `ρ ‖x - y‖²` in the literature is `m = 2 ρ` here. -/
theorem StrongConvexOn.isCoerciveFunctionalOn {K : Set V} {f : V → ℝ} {m : ℝ}
    (hf : StrongConvexOn K m f) (hm : 0 < m) {x₀ : V} (hx₀ : x₀ ∈ K) {r : ℝ} (hr : 0 < r)
    (hbdd : BddBelow (f '' (K ∩ Metric.ball x₀ r))) : IsCoerciveFunctionalOn f K := by
  obtain ⟨c, hc⟩ := hbdd
  set A : ℝ := 2 * (|c| + |f x₀|) / r with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  intro M
  refine ⟨‖x₀‖ + max r (4 / m * (A + |M| + 1) + 1), fun y hy hynorm => ?_⟩
  set s : ℝ := ‖y - x₀‖ with hsdef
  have hsge : max r (4 / m * (A + |M| + 1) + 1) ≤ s := by
    have h1 : ‖y‖ - ‖x₀‖ ≤ s := by rw [hsdef]; exact norm_sub_norm_le y x₀
    linarith
  have hsr : r ≤ s := (le_max_left _ _).trans hsge
  have hs1 : 4 / m * (A + |M| + 1) + 1 ≤ s := (le_max_right _ _).trans hsge
  have hspos : 0 < s := lt_of_lt_of_le hr hsr
  set t : ℝ := r / (2 * s) with htdef
  have htpos : 0 < t := by rw [htdef]; exact div_pos hr (by linarith)
  have hthalf : t ≤ 1 / 2 := by
    rw [htdef, div_le_iff₀ (by linarith)]; linarith
  have ht1 : 0 ≤ 1 - t := by linarith
  have hts : t * s = r / 2 := by rw [htdef]; field_simp
  have hzK : (1 - t) • x₀ + t • y ∈ K := hf.1 hx₀ hy ht1 htpos.le (by ring)
  have hzball : (1 - t) • x₀ + t • y ∈ Metric.ball x₀ r := by
    have hrw : (1 - t) • x₀ + t • y - x₀ = t • (y - x₀) := by module
    rw [Metric.mem_ball, dist_eq_norm, hrw, norm_smul, Real.norm_eq_abs, abs_of_pos htpos,
      ← hsdef, hts]
    linarith
  have hcz : c ≤ f ((1 - t) • x₀ + t • y) := hc ⟨_, ⟨hzK, hzball⟩, rfl⟩
  have hsc := hf.2 hx₀ hy ht1 htpos.le (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul] at hsc
  rw [norm_sub_rev, ← hsdef] at hsc
  have hfx₀ : (1 - t) * f x₀ ≤ |f x₀| :=
    calc (1 - t) * f x₀ ≤ (1 - t) * |f x₀| := mul_le_mul_of_nonneg_left (le_abs_self _) ht1
      _ ≤ 1 * |f x₀| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ = |f x₀| := one_mul _
  have key : c - |f x₀| + m / 4 * (t * s ^ 2) ≤ t * f y := by
    have h2 : m / 4 * (t * s ^ 2) ≤ (1 - t) * t * (m / 2 * s ^ 2) := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg htpos.le (sq_nonneg s)) hm.le)
        (by linarith : (0 : ℝ) ≤ 1 - 2 * t)]
    linarith
  have hAts : A * (t * s) = |c| + |f x₀| := by rw [hts, hA]; field_simp
  have hfy : m / 4 * s ^ 2 - A * s ≤ f y := by
    refine le_of_mul_le_mul_left ?_ htpos
    have hrw : t * (m / 4 * s ^ 2 - A * s) = m / 4 * (t * s ^ 2) - A * (t * s) := by ring
    rw [hrw, hAts]
    linarith [neg_abs_le c]
  have hs1' : (1 : ℝ) ≤ s := by
    have : 0 ≤ 4 / m * (A + |M| + 1) := by positivity
    linarith
  have hlin : |M| + 1 ≤ m / 4 * s - A := by
    have hmul : m / 4 * (4 / m * (A + |M| + 1) + 1) ≤ m / 4 * s :=
      mul_le_mul_of_nonneg_left hs1 (by positivity)
    have hid : m / 4 * (4 / m * (A + |M| + 1) + 1) = A + |M| + 1 + m / 4 := by field_simp
    rw [hid] at hmul
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hlin hspos.le, le_abs_self M, abs_nonneg M]

/-- Strong convexity on the whole space restricts to any convex set. -/
theorem StrongConvexOn.mono_of_univ {K : Set V} {f : V → ℝ} {m : ℝ}
    (hf : StrongConvexOn Set.univ m f) (hK : Convex ℝ K) : StrongConvexOn K m f :=
  ⟨hK, fun x _ y _ _ _ hs ht hst ↦ hf.2 (Set.mem_univ x) (Set.mem_univ y) hs ht hst⟩

/-- A strongly convex continuous functional is coercive on any nonempty set: the local lower
bound that `StrongConvexOn.isCoerciveFunctionalOn` asks for comes from continuity at a point. -/
theorem StrongConvexOn.isCoerciveFunctionalOn_of_continuous {K : Set V} {f : V → ℝ} {m : ℝ}
    (hf : StrongConvexOn K m f) (hm : 0 < m) (hne : K.Nonempty) (hc : Continuous f) :
    IsCoerciveFunctionalOn f K := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ x ∈ Metric.ball x₀ r, f x₀ - 1 < f x := by
    have h := (hc.tendsto x₀).eventually (lt_mem_nhds (show f x₀ - 1 < f x₀ by linarith))
    rw [Metric.eventually_nhds_iff_ball] at h
    exact h
  refine hf.isCoerciveFunctionalOn hm hx₀ hr ⟨f x₀ - 1, ?_⟩
  rintro _ ⟨x, ⟨-, hxb⟩, rfl⟩
  exact (hball x hxb).le

variable [FiniteDimensional ℝ V]

/-- **Existence and uniqueness of the minimizer of a strongly convex functional** on a nonempty
closed set of a finite-dimensional real normed space: a lower semicontinuous `m`-strongly convex
`f` with `0 < m` has exactly one minimizer on `K`.

Convexity of `K` is part of `StrongConvexOn K m f`. Lower semicontinuity cannot be dropped, though
textbook statements often do: on `K = [0, 1]` the function `f x = (x - 1) ^ 2` for `x < 1` and
`f 1 = 5` is strongly convex on `K` and has no minimizer there. Existence is
`exists_isMinOn_of_isClosed_of_finiteDimensional` fed by `StrongConvexOn.isCoerciveFunctionalOn`,
whose local lower bound comes from lower semicontinuity at a point of `K`; uniqueness is
`IsMinOn.eq_of_strictConvexOn` applied to `StrongConvexOn.strictConvexOn`. -/
theorem existsUnique_isMinOn_of_strongConvexOn {K : Set V} (hcl : IsClosed K) (hne : K.Nonempty)
    {f : V → ℝ} {m : ℝ} (hm : 0 < m) (hf : StrongConvexOn K m f)
    (hlsc : LowerSemicontinuousOn f K) : ∃! u, u ∈ K ∧ IsMinOn f K u := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ x ∈ Metric.ball x₀ r, x ∈ K → f x₀ - 1 < f x := by
    have h := hlsc x₀ hx₀ (f x₀ - 1) (by linarith)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at h
    exact h
  have hbdd : BddBelow (f '' (K ∩ Metric.ball x₀ r)) := by
    refine ⟨f x₀ - 1, ?_⟩
    rintro _ ⟨x, ⟨hxK, hxb⟩, rfl⟩
    exact (hball x hxb hxK).le
  obtain ⟨u, huK, humin⟩ :=
    exists_isMinOn_of_isClosed_of_finiteDimensional (𝕜 := ℝ) (⊤ : Submodule ℝ V) (by simp) hcl
      ⟨x₀, hx₀⟩ hlsc (hf.isCoerciveFunctionalOn hm hx₀ hr hbdd)
  refine ⟨u, ⟨huK, humin⟩, ?_⟩
  rintro v ⟨hvK, hvmin⟩
  exact IsMinOn.eq_of_strictConvexOn (hf.strictConvexOn hm) hvmin humin hvK huK

end StrongConvex
