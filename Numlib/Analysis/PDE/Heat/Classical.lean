import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Numlib.Analysis.Calculus.SpaceTime

/-!
# The classical maximum principle for the heat equation

The pointwise side of the heat equation: the parabolic maximum principle of [brezis2011functional]
Theorem 10.6 for a function `u (x, t)` that is differentiable in `t`, `C²` in `x`, and satisfies
`∂ₜ u - ν Δ u ≤ 0` on a bounded cylinder `Ω × (0, T)` — its maximum over `closure Ω × [0, T]` is
attained on the *parabolic boundary* `P = (closure Ω × {0}) ∪ (frontier Ω × [0, T])`. Nothing here
uses a Sobolev space: the function of two variables is `u : E × ℝ → ℝ` uncurried, `E` a
finite-dimensional real inner product space (the surface takes `EuclideanSpace ℝ (Fin N)`), the
Laplacian is Mathlib's `InnerProductSpace.laplacian` (`Δ f x`), and a diffusion constant `ν > 0`
is carried (`∂ₜ u - ν Δ u ≤ 0`), the book's case being `ν = 1`, because the consumer
`AtkinsonHan.Chapter06.example_6_2_4` has `u_t = ν u_xx`.

## Main definitions

* `Heat.parabolicBoundary Ω T`: the parabolic boundary `P` of the cylinder `Ω × (0, T)`, closed,
  contained in `closure Ω ×ˢ Icc 0 T`, compact for bounded `Ω`.
* `Heat.IsClassicalSubsolution ν Ω T u`: the hypotheses (20)–(22) of Theorem 10.6 — continuity on
  the closed cylinder, differentiability in `t` and `C²` in `x` at every point of the open
  cylinder, and `∂ₜ u - ν Δ u ≤ 0` there; `Heat.IsClassicalSolution ν Ω T u` is the version with
  `= 0`, so that `u` and `-u` are both subsolutions. The book's (21), "of class `C¹` in `t` and
  `C²` in `x`", asks a little more continuity than the proof uses.

## Main statements

* `Heat.mem_parabolicBoundary_of_isMaxOn_of_lt`: a *strict* subsolution (`∂ₜ v - ν Δ v < 0`)
  attains its maximum over `closure Ω ×ˢ Icc 0 T'` only on the parabolic boundary — at an interior
  maximum `Δ v ≤ 0` (`IsLocalMax.laplacian_nonpos` of `Numlib.Analysis.Calculus.DerivativeTest`)
  and, `t` ranging over `[0, T']`, the one-sided time derivative is `≥ 0`.
* `Heat.IsClassicalSubsolution.le_of_le_on_parabolicBoundary` and
  `Heat.IsClassicalSubsolution.exists_isMaxOn_parabolicBoundary`: **Theorem 10.6**, as a bound
  (`u ≤ M` on the parabolic boundary gives `u ≤ M` on the closed cylinder) and as the existence of
  a maximum point on the parabolic boundary.
* `Heat.IsClassicalSolution.abs_le_of_eq_zero_frontier`: the form the numerical books use — a
  solution vanishing on the lateral boundary satisfies `|u (x, t)| ≤ M` whenever `|u (·, 0)| ≤ M`
  on `closure Ω`, Theorem 10.6 applied to `u` and `-u`.
* `Heat.IsClassicalSolution.iteratedLaplacian_eq_zero_frontier`: **Remark 4 of chapter 10**, the
  necessity of the compatibility conditions `Δ^j u₀ = 0` on `∂Ω` for a solution which is `C^∞` on
  `E × ℝ` and vanishes on the lateral boundary — from the iterated heat equation
  `∂ₜ^j u = ν^j Δ^j u` (`IsClassicalSolution.timeDeriv_iterate_eqOn`), which rests on the
  commutation `∂ₜ Δ_x = Δ_x ∂ₜ` of the two partial operators `Heat.timeDeriv` and
  `Heat.spaceLaplacian` on smooth functions of `(x, t)` (`timeDeriv_spaceLaplacian` of
  `Numlib.Analysis.Calculus.SpaceTime`, a consequence of the symmetry of the iterated
  derivative).

## Implementation notes

The book perturbs by `ε |x|²`; the perturbation used here is `v = u - ε t`, which has
`∂ₜ v - ν Δ v ≤ -ε < 0` in every dimension (including `dim E = 0`, where `Δ |x|² = 2N` vanishes),
needs no computation of `Δ |x|²`, and costs the same limit `ε → 0`. The book's footnote — work on
`[0, T']` with `T' < T`, where `v` is differentiable in `t` up to the right endpoint, then let
`T' → T` — is made explicit: the bound is first proved on `closure Ω ×ˢ Ico 0 T` and then passed
to `t = T` by continuity (`ContinuousWithinAt.closure_le`).

The one-sided sign of the time derivative at a maximum with `t₀ ∈ (0, T']` is Mathlib's
`IsLocalMaxOn.hasFDerivWithinAt_nonpos` applied to the direction `-t₀` of the positive tangent
cone of `Icc 0 T'` at `t₀`, so the cases `t₀ < T'` and `t₀ = T'` of the book are one case.

## References

[brezis2011functional], §10.2, Theorem 10.6 and its footnote 8.
-/

open Filter Set Topology InnerProductSpace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Heat

/-! ### The parabolic boundary -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The parabolic boundary** `P = (closure Ω × {0}) ∪ (frontier Ω × [0, T])` of the cylinder
`Ω × (0, T)` ([brezis2011functional] Theorem 10.6): the bottom and the lateral surface, without
the top. -/
def parabolicBoundary (Ω : Set E) (T : ℝ) : Set (E × ℝ) :=
  closure Ω ×ˢ {0} ∪ frontier Ω ×ˢ Icc 0 T

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The parabolic boundary lies in the closed cylinder `closure Ω × [0, T]`. -/
theorem parabolicBoundary_subset {Ω : Set E} {T : ℝ} (hT : 0 ≤ T) :
    parabolicBoundary Ω T ⊆ closure Ω ×ˢ Icc 0 T := by
  rintro ⟨x, t⟩ (⟨hx, ht⟩ | ⟨hx, ht⟩)
  · exact ⟨hx, by simp only [mem_singleton_iff] at ht; rw [ht]; exact ⟨le_rfl, hT⟩⟩
  · exact ⟨frontier_subset_closure hx, ht⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The parabolic boundary grows with the time horizon. -/
theorem parabolicBoundary_mono {Ω : Set E} {T T' : ℝ} (h : T' ≤ T) :
    parabolicBoundary Ω T' ⊆ parabolicBoundary Ω T :=
  union_subset_union_right _ (prod_mono_right (Icc_subset_Icc_right h))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The parabolic boundary is closed. -/
theorem isClosed_parabolicBoundary (Ω : Set E) (T : ℝ) : IsClosed (parabolicBoundary Ω T) :=
  (isClosed_closure.prod isClosed_singleton).union (isClosed_frontier.prod isClosed_Icc)

/-- The parabolic boundary of a bounded cylinder is compact. -/
theorem isCompact_parabolicBoundary {Ω : Set E} (hb : Bornology.IsBounded Ω) (T : ℝ) :
    IsCompact (parabolicBoundary Ω T) :=
  (hb.isCompact_closure.prod isCompact_singleton).union
    ((hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure).prod
      isCompact_Icc)

/-! ### Classical subsolutions and solutions -/

/-- **A classical subsolution of the heat equation** `∂ₜ u - ν Δ u ≤ 0` on the cylinder
`Ω × (0, T)`: the hypotheses (20)–(22) of [brezis2011functional] Theorem 10.6. The function
`u : E × ℝ → ℝ` is continuous on the closed cylinder `closure Ω × [0, T]`; at every point
`(x, t)` of `Ω × (0, T)` it is differentiable in `t` and `C²` in `x`; and
`∂ₜ u (x, t) - ν Δ u (·, t) (x) ≤ 0` there. The book's "of class `C¹` in `t` and `C²` in `x`"
asks a little more continuity than the proof uses. -/
structure IsClassicalSubsolution (ν : ℝ) (Ω : Set E) (T : ℝ) (u : E × ℝ → ℝ) : Prop where
  /-- `u` is continuous on the closed cylinder. -/
  continuousOn : ContinuousOn u (closure Ω ×ˢ Icc 0 T)
  /-- `u` is differentiable in `t` at every point of the open cylinder. -/
  differentiableAt_snd : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (fun s ↦ u (x, s)) t
  /-- `u` is `C²` in `x` at every point of the open cylinder. -/
  contDiffAt_fst : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ u (y, t)) x
  /-- The differential inequality `∂ₜ u - ν Δ u ≤ 0` on the open cylinder. -/
  deriv_sub_laplacian_nonpos : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T,
    deriv (fun s ↦ u (x, s)) t - ν * Δ (fun y ↦ u (y, t)) x ≤ 0

/-- **A classical solution of the heat equation** `∂ₜ u = ν Δ u` on the cylinder `Ω × (0, T)`,
with the regularity of `IsClassicalSubsolution`: continuous on the closed cylinder, differentiable
in `t` and `C²` in `x` on the open one. No boundary or initial condition is prescribed. -/
structure IsClassicalSolution (ν : ℝ) (Ω : Set E) (T : ℝ) (u : E × ℝ → ℝ) : Prop where
  /-- `u` is continuous on the closed cylinder. -/
  continuousOn : ContinuousOn u (closure Ω ×ˢ Icc 0 T)
  /-- `u` is differentiable in `t` at every point of the open cylinder. -/
  differentiableAt_snd : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (fun s ↦ u (x, s)) t
  /-- `u` is `C²` in `x` at every point of the open cylinder. -/
  contDiffAt_fst : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ u (y, t)) x
  /-- The heat equation `∂ₜ u = ν Δ u` on the open cylinder. -/
  deriv_eq_laplacian : ∀ x ∈ Ω, ∀ t ∈ Ioo 0 T,
    deriv (fun s ↦ u (x, s)) t = ν * Δ (fun y ↦ u (y, t)) x

variable {ν T : ℝ} {Ω : Set E} {u : E × ℝ → ℝ}

/-- A classical solution is a classical subsolution. -/
theorem IsClassicalSolution.isClassicalSubsolution (hu : IsClassicalSolution ν Ω T u) :
    IsClassicalSubsolution ν Ω T u :=
  ⟨hu.continuousOn, hu.differentiableAt_snd, hu.contDiffAt_fst, fun x hx t ht =>
    (sub_eq_zero.2 (hu.deriv_eq_laplacian x hx t ht)).le⟩

/-- The negative of a classical solution is a classical solution (the heat equation is linear). -/
theorem IsClassicalSolution.neg (hu : IsClassicalSolution ν Ω T u) :
    IsClassicalSolution ν Ω T (-u) := by
  refine ⟨hu.continuousOn.neg, fun x hx t ht => (hu.differentiableAt_snd x hx t ht).neg,
    fun x hx t ht => (hu.contDiffAt_fst x hx t ht).neg, fun x hx t ht => ?_⟩
  have h1 : (fun s ↦ (-u) (x, s)) = -(fun s ↦ u (x, s)) := rfl
  have h2 : (fun y ↦ (-u) (y, t)) = -(fun y ↦ u (y, t)) := rfl
  rw [h1, h2, deriv.neg, laplacian_neg, Pi.neg_apply, hu.deriv_eq_laplacian x hx t ht, mul_neg]

/-! ### The maximum principle -/

/-- **A strict subsolution attains its maximum only on the parabolic boundary.** If `v` is
differentiable in `t`, `C²` in `x` and satisfies `∂ₜ v - ν Δ v < 0` at every point of
`Ω × (0, T']` (the right endpoint included), then a maximum point of `v` over the closed cylinder
`closure Ω × [0, T']` lies on `parabolicBoundary Ω T'`. At a maximum `(x₀, t₀)` with `x₀ ∈ Ω`
and `t₀ > 0`, the Laplacian in `x` is `≤ 0` (`IsLocalMax.laplacian_nonpos`) and the time
derivative is `≥ 0`, since `t ↦ v (x₀, t)` has a local maximum at `t₀` among `t ∈ [0, T']` and
`-t₀` is in the positive tangent cone of `[0, T']` at `t₀`; so `∂ₜ v - ν Δ v ≥ 0` there. -/
theorem mem_parabolicBoundary_of_isMaxOn_of_lt (hΩ : IsOpen Ω) (hν : 0 < ν) {v : E × ℝ → ℝ}
    {T' : ℝ} (hd : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T', DifferentiableAt ℝ (fun s ↦ v (x, s)) t)
    (hx : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T', ContDiffAt ℝ 2 (fun y ↦ v (y, t)) x)
    (hlt : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T', deriv (fun s ↦ v (x, s)) t - ν * Δ (fun y ↦ v (y, t)) x < 0)
    {p : E × ℝ} (hp : p ∈ closure Ω ×ˢ Icc 0 T') (hmax : IsMaxOn v (closure Ω ×ˢ Icc 0 T') p) :
    p ∈ parabolicBoundary Ω T' := by
  obtain ⟨x₀, t₀⟩ := p
  obtain ⟨hx₀, ht₀⟩ := hp
  by_contra hnot
  simp only [parabolicBoundary, mem_union, mem_prod, mem_singleton_iff, not_or, not_and] at hnot
  have hx₀Ω : x₀ ∈ Ω := by
    have : x₀ ∈ closure Ω \ frontier Ω := ⟨hx₀, fun h => hnot.2 h ht₀⟩
    rwa [closure_sdiff_frontier, hΩ.interior_eq] at this
  have ht₀pos : 0 < t₀ := lt_of_le_of_ne ht₀.1 fun h => hnot.1 hx₀ h.symm
  have ht₀' : t₀ ∈ Ioc 0 T' := ⟨ht₀pos, ht₀.2⟩
  -- the Laplacian in `x` is `≤ 0` at the maximum
  have hΔ : Δ (fun y ↦ v (y, t₀)) x₀ ≤ 0 := by
    refine IsLocalMax.laplacian_nonpos ?_ (hx x₀ hx₀Ω t₀ ht₀')
    exact eventually_of_mem (hΩ.mem_nhds hx₀Ω) fun y hy => hmax ⟨subset_closure hy, ht₀⟩
  -- the time derivative is `≥ 0` at the maximum (one-sided, from the left)
  have hderiv : 0 ≤ deriv (fun s ↦ v (x₀, s)) t₀ := by
    have hmaxOn : IsMaxOn (fun s ↦ v (x₀, s)) (Icc 0 T') t₀ := fun s hs => hmax ⟨hx₀, hs⟩
    have hmax' : IsLocalMaxOn (fun s ↦ v (x₀, s)) (Icc 0 T') t₀ := hmaxOn.isLocalMaxOn
    have hseg : (-t₀ : ℝ) ∈ posTangentConeAt (Icc 0 T') t₀ := by
      refine mem_posTangentConeAt_of_segment_subset ?_
      rw [add_neg_cancel]
      exact (convex_Icc 0 T').segment_subset ht₀ ⟨le_rfl, ht₀.2.trans' ht₀.1⟩
    have h := hmax'.hasFDerivWithinAt_nonpos
      (hd x₀ hx₀Ω t₀ ht₀').hasDerivAt.hasFDerivAt.hasFDerivWithinAt hseg
    rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
    nlinarith
  have := hlt x₀ hx₀Ω t₀ ht₀'
  nlinarith [mul_nonneg hν.le (neg_nonneg.2 hΔ)]

/-- **Theorem 10.6, the bound form**: a classical subsolution on a bounded cylinder that is at most
`M` on the parabolic boundary is at most `M` on the closed cylinder. For `t < T` and `ε > 0`,
the strict subsolution `v = u - ε t` on `[0, T']`, `t ≤ T' < T`, attains its maximum on the
parabolic boundary (`mem_parabolicBoundary_of_isMaxOn_of_lt`), where `v ≤ u ≤ M`; hence
`u (x, t) ≤ M + ε T`, and `ε → 0`. The value at `t = T` follows by continuity. -/
theorem IsClassicalSubsolution.le_of_le_on_parabolicBoundary (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hν : 0 < ν) (hT : 0 < T) (hu : IsClassicalSubsolution ν Ω T u)
    {M : ℝ} (hM : ∀ p ∈ parabolicBoundary Ω T, u p ≤ M) :
    ∀ q ∈ closure Ω ×ˢ Icc 0 T, u q ≤ M := by
  -- first on `closure Ω ×ˢ Ico 0 T`, by the perturbation `u - ε t` on `[0, T']`, `T' < T`
  have key : ∀ q ∈ closure Ω ×ˢ Ico 0 T, u q ≤ M := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set ε' := ε / T with hε'
    have hε'pos : 0 < ε' := by positivity
    set T' := (t + T) / 2 with hT'
    have hT'pos : 0 < T' := by rw [hT']; linarith [ht.1]
    have hT'T : T' < T := by rw [hT']; linarith [ht.2]
    have htT' : t ≤ T' := by rw [hT']; linarith [ht.2]
    have hK : IsCompact (closure Ω ×ˢ Icc 0 T') := hb.isCompact_closure.prod isCompact_Icc
    have hKne : (closure Ω ×ˢ Icc 0 T').Nonempty := ⟨(x, t), hx, ht.1, htT'⟩
    have hsub : closure Ω ×ˢ Icc 0 T' ⊆ closure Ω ×ˢ Icc 0 T :=
      prod_mono_right (Icc_subset_Icc_right hT'T.le)
    have hvc : ContinuousOn (fun p : E × ℝ ↦ u p - ε' * p.2) (closure Ω ×ˢ Icc 0 T') :=
      (hu.continuousOn.mono hsub).sub (continuous_const.mul continuous_snd).continuousOn
    obtain ⟨p, hp, hpmax⟩ := hK.exists_isMaxOn hKne hvc
    have hpP : p ∈ parabolicBoundary Ω T' := by
      refine mem_parabolicBoundary_of_isMaxOn_of_lt hΩ hν ?_ ?_ ?_ hp hpmax
      · intro y hy s hs
        exact (hu.differentiableAt_snd y hy s ⟨hs.1, hs.2.trans_lt hT'T⟩).sub
          ((differentiableAt_id).const_mul ε')
      · intro y hy s hs
        exact (hu.contDiffAt_fst y hy s ⟨hs.1, hs.2.trans_lt hT'T⟩).sub
          (contDiffAt_const (c := ε' * s))
      · intro y hy s hs
        have hs' : s ∈ Ioo 0 T := ⟨hs.1, hs.2.trans_lt hT'T⟩
        have h1 : deriv (fun r ↦ u (y, r) - ε' * r) s = deriv (fun r ↦ u (y, r)) s - ε' := by
          have hsum : HasDerivAt (fun r ↦ u (y, r) - ε' * r)
              (deriv (fun r ↦ u (y, r)) s - ε' * 1) s :=
            (hu.differentiableAt_snd y hy s hs').hasDerivAt.sub ((hasDerivAt_id s).const_mul ε')
          rw [mul_one] at hsum
          exact hsum.deriv
        have h2 : Δ (fun z ↦ u (z, s) - ε' * s) y = Δ (fun z ↦ u (z, s)) y := by
          have hsub' : (fun z ↦ u (z, s) - ε' * s) = (fun z ↦ u (z, s)) - fun _ ↦ ε' * s := rfl
          rw [hsub', (hu.contDiffAt_fst y hy s hs').laplacian_sub contDiffAt_const,
            laplacian_const, Pi.zero_apply, sub_zero]
        change deriv (fun r ↦ u (y, r) - ε' * r) s - ν * Δ (fun z ↦ u (z, s) - ε' * s) y < 0
        rw [h1, h2]
        linarith [hu.deriv_sub_laplacian_nonpos y hy s hs']
    have hvp : u p - ε' * p.2 ≤ M := by
      have hp0 : 0 ≤ p.2 := (parabolicBoundary_subset hT'pos.le hpP).2.1
      calc u p - ε' * p.2 ≤ u p := by nlinarith
        _ ≤ M := hM p (parabolicBoundary_mono hT'T.le hpP)
    have hvq : u (x, t) - ε' * t ≤ u p - ε' * p.2 := hpmax ⟨hx, ht.1, htT'⟩
    rw [hε'] at hvq hvp
    calc u (x, t) = (u (x, t) - ε / T * t) + ε / T * t := by ring
      _ ≤ M + ε / T * T := by
          have : ε / T * t ≤ ε / T * T := by gcongr; exact ht.2.le
          linarith
      _ = M + ε := by rw [div_mul_cancel₀ _ hT.ne']
  -- then on the closed cylinder, by continuity
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  have hcl : (x, t) ∈ closure (closure Ω ×ˢ Ico 0 T) := by
    rw [closure_prod_eq, closure_closure, closure_Ico hT.ne]
    exact ⟨hx, ht⟩
  refine ContinuousWithinAt.closure_le hcl ?_ continuousWithinAt_const key
  exact (hu.continuousOn (x, t) ⟨hx, ht⟩).mono (prod_mono_right Ico_subset_Icc_self)

/-- **The parabolic maximum principle** ([brezis2011functional] Theorem 10.6): a classical
subsolution `u` of `∂ₜ u - ν Δ u ≤ 0` on a bounded cylinder `Ω × (0, T)` (nonempty `Ω`, so that
the maximum exists) attains its maximum over `closure Ω × [0, T]` at a point of the parabolic
boundary `P = (closure Ω × {0}) ∪ (frontier Ω × [0, T])`:
`max_{closure Ω × [0, T]} u = max_P u`. -/
theorem IsClassicalSubsolution.exists_isMaxOn_parabolicBoundary (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) (hν : 0 < ν) (hT : 0 < T)
    (hu : IsClassicalSubsolution ν Ω T u) :
    ∃ p ∈ parabolicBoundary Ω T, IsMaxOn u (closure Ω ×ˢ Icc 0 T) p := by
  obtain ⟨x, hx⟩ := hne
  have hPne : (parabolicBoundary Ω T).Nonempty := ⟨(x, 0), Or.inl ⟨subset_closure hx, rfl⟩⟩
  obtain ⟨p, hp, hpmax⟩ := (isCompact_parabolicBoundary hb T).exists_isMaxOn hPne
    (hu.continuousOn.mono (parabolicBoundary_subset hT.le))
  exact ⟨p, hp, fun q hq =>
    hu.le_of_le_on_parabolicBoundary hΩ hb hν hT (fun r hr => hpmax hr) q hq⟩

/-- **The maximum principle in the form the numerical books use**: a classical solution of
`∂ₜ u = ν Δ u` on a bounded cylinder that vanishes on the lateral boundary `frontier Ω × [0, T]`
satisfies `|u (x, t)| ≤ M` on the closed cylinder as soon as `|u (·, 0)| ≤ M` on `closure Ω` —
the bound `max_x |u (x, t)| ≤ max_x |u₀ (x)|`, Theorem 10.6 applied to `u` and to `-u`. -/
theorem IsClassicalSolution.abs_le_of_eq_zero_frontier (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hν : 0 < ν) (hT : 0 < T) (hu : IsClassicalSolution ν Ω T u)
    (hΓ : ∀ x ∈ frontier Ω, ∀ t ∈ Icc 0 T, u (x, t) = 0) {M : ℝ}
    (hM : ∀ y ∈ closure Ω, |u (y, 0)| ≤ M) :
    ∀ x ∈ closure Ω, ∀ t ∈ Icc 0 T, |u (x, t)| ≤ M := by
  have hP : ∀ p ∈ parabolicBoundary Ω T, u p ≤ M ∧ -u p ≤ M := by
    rintro ⟨y, t⟩ (⟨hy, ht⟩ | ⟨hy, ht⟩)
    · simp only [mem_singleton_iff] at ht
      subst ht
      exact ⟨(le_abs_self _).trans (hM y hy), (neg_le_abs _).trans (hM y hy)⟩
    · have h0 : 0 ≤ M := (abs_nonneg _).trans (hM y (frontier_subset_closure hy))
      rw [hΓ y hy t ht]
      simp only [neg_zero]
      exact ⟨h0, h0⟩
  intro x hx t ht
  refine abs_le.2 ⟨?_, ?_⟩
  · have := hu.neg.isClassicalSubsolution.le_of_le_on_parabolicBoundary hΩ hb hν hT
      (fun p hp => (hP p hp).2) (x, t) ⟨hx, ht⟩
    simpa only [Pi.neg_apply, neg_le] using this
  · exact hu.isClassicalSubsolution.le_of_le_on_parabolicBoundary hΩ hb hν hT
      (fun p hp => (hP p hp).1) (x, t) ⟨hx, ht⟩


/-! ### The compatibility conditions are necessary (Remark 4) -/

variable {ν T : ℝ} {Ω : Set E} {u : E × ℝ → ℝ}

open scoped ContDiff in
/-- **The iterated heat equation**: a smooth classical solution of `∂ₜ u = ν Δ u` on
`Ω × (0, T)` satisfies `∂ₜ^j u = ν^j Δ^j u` there, for every `j`: by induction, using the
commutation `∂ₜ Δ_x^j = Δ_x^j ∂ₜ` of smooth functions (`timeDeriv_spaceLaplacian_iterate`) and
the locality of both operators on the open cylinder. -/
theorem IsClassicalSolution.timeDeriv_iterate_eqOn (hΩ : IsOpen Ω)
    (hu : IsClassicalSolution ν Ω T u) (hsmooth : ContDiff ℝ ∞ u) (j : ℕ) :
    EqOn (timeDeriv^[j] u) (ν ^ j • spaceLaplacian^[j] u) (Ω ×ˢ Ioo 0 T) := by
  have hV : IsOpen (Ω ×ˢ Ioo 0 T) := hΩ.prod isOpen_Ioo
  have heq : EqOn (timeDeriv u) (ν • spaceLaplacian u) (Ω ×ˢ Ioo 0 T) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact hu.deriv_eq_laplacian x hx t ht
  induction j with
  | zero => intro p _; simp
  | succ j ih =>
    intro p hp
    rw [Function.iterate_succ_apply', timeDeriv_eqOn hV ih hp, timeDeriv_const_smul,
      timeDeriv_spaceLaplacian_iterate hsmooth, Pi.smul_apply,
      spaceLaplacian_iterate_eqOn hV heq j hp,
      spaceLaplacian_iterate_const_smul ν (contDiff_spaceLaplacian hsmooth) j,
      Function.iterate_succ_apply, pow_succ]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

open scoped ContDiff in
/-- **Remark 4: the compatibility conditions are necessary.** Let `u` be a classical solution of
`∂ₜ u = ν Δ u` on the cylinder `Ω × (0, T)` (`ν ≠ 0`, `T > 0`, `Ω` open) which is `C^∞` on
`E × ℝ` and vanishes on the lateral boundary `frontier Ω × (0, T)`. Then the initial datum
`u (·, 0)` satisfies `Δ^j (u (·, 0)) = 0` on `frontier Ω` for every `j`, the compatibility
conditions (8) of [brezis2011functional] Theorem 10.2 (c).

Proof, [brezis2011functional] chapter 10 Remark 4: `∂ₜ^j u = ν^j Δ_x^j u` on `Ω × (0, T)`
(`IsClassicalSolution.timeDeriv_iterate_eqOn`, the iterated commutation of `∂ₜ` with `Δ_x`);
`∂ₜ^j u = 0` on `frontier Ω × (0, T)` since `u` vanishes there (`iterate_deriv_eq_zero_of_eqOn`);
both sides are continuous on `E × ℝ`, so the identities pass to the closures
`closure Ω × [0, T]` and `frontier Ω × [0, T]`, and comparing them at `(x, 0)` for
`x ∈ frontier Ω` gives `ν^j Δ^j (u (·, 0)) x = 0`.

The book states the remark for `u ∈ C^∞(Ω̄ × [0, ∞))` in the sense of its footnote 16, where
`u (·, 0)` is only known to be continuous on `Ω̄` and `Δ^j (u (·, 0))` on the boundary refers to
the continuous extension of `Δ^j u`; the smoothness of `u` on all of `E × ℝ` assumed here makes
the statement meaningful as written, and is what Theorem 10.2 (c)'s solutions have on the
interior of their domain of smoothness. -/
theorem IsClassicalSolution.iteratedLaplacian_eq_zero_frontier (hΩ : IsOpen Ω) (hν : ν ≠ 0)
    (hT : 0 < T) (hu : IsClassicalSolution ν Ω T u) (hsmooth : ContDiff ℝ ∞ u)
    (hΓ : ∀ x ∈ frontier Ω, ∀ t ∈ Ioo 0 T, u (x, t) = 0) (j : ℕ) :
    ∀ x ∈ frontier Ω, (Laplacian.laplacian^[j] fun y ↦ u (y, 0)) x = 0 := by
  intro x hx
  -- `∂ₜ^j u = ν^j Δ_x^j u` on the closed cylinder, by continuity
  have hcl : EqOn (timeDeriv^[j] u) (ν ^ j • spaceLaplacian^[j] u) (closure Ω ×ˢ Icc 0 T) := by
    have h := hu.timeDeriv_iterate_eqOn hΩ hsmooth j
    refine h.of_subset_closure (contDiff_timeDeriv_iterate hsmooth j).continuous.continuousOn
      ((contDiff_spaceLaplacian_iterate hsmooth j).continuous.const_smul _).continuousOn
      (prod_mono subset_closure Ioo_subset_Icc_self) ?_
    rw [closure_prod_eq, closure_Ioo hT.ne]
  -- `∂ₜ^j u (x, 0) = 0`, by continuity from the lateral boundary
  have hzero : timeDeriv^[j] u (x, 0) = 0 := by
    have h1 : EqOn (fun s ↦ timeDeriv^[j] u (x, s)) 0 (Ioo 0 T) := by
      rw [timeDeriv_iterate_slice]
      exact iterate_deriv_eq_zero_of_eqOn isOpen_Ioo (fun t ht ↦ hΓ x hx t ht) j
    have h2 : EqOn (fun s ↦ timeDeriv^[j] u (x, s)) 0 (Icc 0 T) := by
      rw [← closure_Ioo hT.ne]
      exact h1.of_subset_closure ((contDiff_timeDeriv_iterate hsmooth j).continuous.comp
        (continuous_const.prodMk continuous_id)).continuousOn continuousOn_const subset_closure
        subset_rfl
    exact h2 (left_mem_Icc.2 hT.le)
  have h3 := hcl (x := (x, 0)) ⟨frontier_subset_closure hx, left_mem_Icc.2 hT.le⟩
  rw [hzero, Pi.smul_apply, smul_eq_mul, eq_comm, mul_eq_zero,
    or_iff_right (pow_ne_zero j hν)] at h3
  rw [← spaceLaplacian_iterate_slice]
  exact h3

end Heat
