import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Numlib.Variational.Galerkin

/-!
# Projection methods for operator equations

The operator-level twin of `Numlib.Variational.Galerkin`: instead of a sesquilinear form on a
Hilbert space, the data is a bounded operator `A` and a bounded projection `P` of the space onto
the trial space, and the discrete problem is `P (A u) = P f` with `u ∈ range P`
(`IsProjectionMethodSolution`, Kress[^kress] (11.30)).  For an orthogonal projection this is the
Galerkin specification `IsGalerkin A f 0 (range P) u` of `Numlib.LinearSolve.Projection.Basic`
(`isProjectionMethodSolution_starProjection_iff`), and Céa's lemma reads
`‖u* - u_n‖ ≤ (‖A‖ / c) inf_{v ∈ range P} ‖u* - v‖` for a strictly coercive `A`
(`IsProjectionMethodSolution.norm_sub_le_of_isCoercive`).

## References

[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
  Theorem 11.17 for Céa's lemma in operator form, and Chapter 12 for projection methods for
  equations of the second kind.
-/

section Defs

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **The projection method** for the operator equation `A u = f` (Kress, *Numerical Analysis*,
(11.30)): the approximation `u` lies in the range of the bounded projection `P` and satisfies the
projected equation `P (A u) = P f`.

Only the *projected* residual is required to vanish, which is what makes this a computable
finite-dimensional problem when `range P` is finite dimensional.  For an orthogonal projection on
a Hilbert space it is exactly the Galerkin specification with `x₀ = 0`, see
`isProjectionMethodSolution_starProjection_iff`. -/
def IsProjectionMethodSolution (A : X →ₗ[𝕜] X) (f : X) (P : X →L[𝕜] X) (u : X) : Prop :=
  u ∈ LinearMap.range (P : X →ₗ[𝕜] X) ∧ P (A u) = P f

/-- Membership in the trial space, in the form in which it is usually used: a projection fixes
its range, so `P u = u`. -/
theorem IsProjectionMethodSolution.apply_eq_self {A : X →ₗ[𝕜] X} {f : X} {P : X →L[𝕜] X}
    (hP : IsIdempotentElem P) {u : X} (h : IsProjectionMethodSolution A f P u) : P u = u := by
  obtain ⟨v, rfl⟩ := h.1
  exact DFunLike.congr_fun hP v

end Defs

section Hilbert

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]

/-- For an orthogonal projection the projection method is the Galerkin method with `x₀ = 0`: the
projected equation `P (A u) = P f` says exactly that the residual `f - A u` is orthogonal to the
trial space (Kress, *Numerical Analysis*, §12.1; the same specification is
`Numlib.LinearSolve.Projection.Basic`'s `IsGalerkin`). -/
theorem isProjectionMethodSolution_starProjection_iff (A : X →ₗ[𝕜] X) (f : X)
    (K : Submodule 𝕜 X) [K.HasOrthogonalProjection] (u : X) :
    IsProjectionMethodSolution A f K.starProjection u ↔ IsGalerkin A f 0 K u := by
  have hzero : ∀ z : X, K.starProjection z = 0 ↔ z ∈ Kᗮ := by
    intro z
    rw [Submodule.starProjection_apply, ← Submodule.coe_zero (p := K),
      Subtype.coe_inj, Submodule.orthogonalProjectionOnto_eq_zero_iff]
  have hrange : ∀ z : X, z ∈ LinearMap.range (K.starProjection : X →ₗ[𝕜] X) ↔ z ∈ K := by
    intro z
    exact ⟨by rintro ⟨y, rfl⟩; exact K.starProjection_apply_mem y,
      fun h => ⟨z, Submodule.starProjection_eq_self_iff.2 h⟩⟩
  constructor
  · rintro ⟨hu, heq⟩
    refine ⟨by simpa using (hrange u).1 hu, (hzero _).1 ?_⟩
    rw [map_sub, heq, sub_self]
  · rintro ⟨hu, horth⟩
    refine ⟨(hrange u).2 (by simpa using hu), ?_⟩
    have h0 : K.starProjection (f - A u) = 0 := (hzero _).2 horth
    rw [map_sub, sub_eq_zero] at h0
    exact h0.symm

variable [CompleteSpace X]

/-- **Céa's lemma in operator form** (Kress, *Numerical Analysis*, Thm 11.17): for a bounded and
strictly coercive `A` and an orthogonal projection onto `K`, the projection method solution obeys
`‖u* - u‖ ≤ (‖A‖ / c) inf_{v ∈ K} ‖u* - v‖`, so it is quasi-optimal.

This is the operator reading of `IsGalerkinSolution.norm_sub_le_infDist`: the form `⟪A u, v⟫` has
the same coercivity constant as `A` and the same norm, so the constant `M / c` of Céa's lemma
becomes `‖A‖ / c`. -/
theorem IsProjectionMethodSolution.norm_sub_le_of_isCoercive {A : X →L[𝕜] X} {c : ℝ} (hc : 0 < c)
    (hA : (A : X →ₗ[𝕜] X).IsCoerciveWith c) {f : X} {K : Submodule 𝕜 X}
    [K.HasOrthogonalProjection] {u : X}
    (hu : IsProjectionMethodSolution (A : X →ₗ[𝕜] X) f K.starProjection u) {ustar : X}
    (hstar : A ustar = f) : ‖ustar - u‖ ≤ ‖A‖ / c * Metric.infDist ustar (K : Set X) := by
  set a : SesqForm 𝕜 X := SesqForm.ofOperator A with ha
  have hop : SesqForm.toOperator a = A := SesqForm.toOperator_ofOperator A
  have hcoer : a.IsCoerciveWith c := by
    rw [SesqForm.isCoerciveWith_iff_toOperator, hop]
    exact hA
  have hbdd : a.IsBoundedWith ‖A‖ := by
    have h := SesqForm.isBoundedWith_opNorm a
    rwa [← SesqForm.norm_toOperator a, hop] at h
  have hriesz : SesqForm.rieszRep (innerSL 𝕜 f) = f :=
    ext_inner_right 𝕜 fun v => SesqForm.inner_rieszRep _ v
  have hgal : IsGalerkinSolution a (innerSL 𝕜 f) K u := by
    rw [IsGalerkinSolution.iff_isGalerkin, hop, hriesz]
    exact (isProjectionMethodSolution_starProjection_iff _ _ _ _).1 hu
  have hstar' : ∀ v, a ustar v = innerSL 𝕜 f v :=
    (SesqForm.forall_apply_eq_iff_toOperator_eq a _ ustar).2 (by rw [hop, hriesz, hstar])
  exact IsGalerkinSolution.norm_sub_le_infDist hc hbdd hcoer hgal hstar'

/-- Unique solvability of the projection equations for a strictly coercive `A` on a complete trial
space (Kress, *Numerical Analysis*, Thm 11.17): Lax–Milgram applied to the restricted form. -/
theorem existsUnique_isProjectionMethodSolution_of_isCoercive {A : X →L[𝕜] X} {c : ℝ} (hc : 0 < c)
    (hA : (A : X →ₗ[𝕜] X).IsCoerciveWith c) (f : X) (K : Submodule 𝕜 X)
    [K.HasOrthogonalProjection] [CompleteSpace K] :
    ∃! u, IsProjectionMethodSolution (A : X →ₗ[𝕜] X) f K.starProjection u := by
  set a : SesqForm 𝕜 X := SesqForm.ofOperator A with ha
  have hop : SesqForm.toOperator a = A := SesqForm.toOperator_ofOperator A
  have hcoer : a.IsCoerciveWith c := by
    rw [SesqForm.isCoerciveWith_iff_toOperator, hop]
    exact hA
  have hriesz : SesqForm.rieszRep (innerSL 𝕜 f) = f :=
    ext_inner_right 𝕜 fun v => SesqForm.inner_rieszRep _ v
  have hiff : ∀ y : X, IsProjectionMethodSolution (A : X →ₗ[𝕜] X) f K.starProjection y
      ↔ IsGalerkinSolution a (innerSL 𝕜 f) K y := by
    intro y
    rw [isProjectionMethodSolution_starProjection_iff, IsGalerkinSolution.iff_isGalerkin, hop,
      hriesz]
  simpa only [hiff] using
    IsGalerkinSolution.existsUnique (a := a) (ℓ := innerSL 𝕜 f) (K := K) hc hcoer

end Hilbert

/-! ### Equations of the second kind -/

section SecondKind

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- A pointwise convergent sequence of bounded operators is uniformly bounded (Banach–Steinhaus:
a convergent sequence of reals is bounded, so the pointwise hypothesis of the uniform boundedness
principle holds). -/
private theorem exists_norm_le_of_tendsto {P : ℕ → (X →L[𝕜] X)}
    (hP : ∀ x, Filter.Tendsto (fun n => P n x) Filter.atTop (nhds x)) : ∃ C : ℝ, ∀ n, ‖P n‖ ≤ C :=
  banach_steinhaus fun x => by
    obtain ⟨M, hM⟩ := ((hP x).norm).bddAbove_range
    exact ⟨M, fun n => hM ⟨n, rfl⟩⟩

/-- **Pointwise convergence becomes uniform against a compact operator**: if `P n x → x` for every
`x` and `T` is compact, then `‖P n T - T‖ → 0`.  This is the one place where compactness of `T`
is used, and it is what lets a Neumann series perturb `1 - T` into `1 - P n T`.

The proof is the classical `ε/3` argument: the `P n` are uniformly bounded by Banach–Steinhaus,
the image of the unit ball under `T` is totally bounded, and pointwise convergence at the finitely
many centres of a `δ`-net is uniform. -/
private theorem tendsto_norm_comp_sub_of_isCompactOperator {T : X →L[𝕜] X}
    (hT : IsCompactOperator T) {P : ℕ → (X →L[𝕜] X)}
    (hP : ∀ x, Filter.Tendsto (fun n => P n x) Filter.atTop (nhds x)) :
    Filter.Tendsto (fun n => ‖P n ∘L T - T‖) Filter.atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_tendsto hP
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  obtain ⟨S, hScpt, hSsub⟩ := hT.image_closedBall_subset_compact (r := 1)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (2 * (C + 2)) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]; positivity
  obtain ⟨t, htfin, htcover⟩ := Metric.totallyBounded_iff.1 hScpt.totallyBounded δ hδ0
  have hev : ∀ᶠ n in Filter.atTop, ∀ y ∈ t, ‖P n y - y‖ < δ := by
    refine htfin.eventually_all.2 fun y _ => ?_
    have hy : Filter.Tendsto (fun n => ‖P n y - y‖) Filter.atTop (nhds 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hP y)
    exact hy.eventually (eventually_lt_nhds hδ0)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  -- a constant bound on the unit ball
  have hunit : ∀ x : X, ‖x‖ ≤ 1 → ‖(P n ∘L T - T) x‖ ≤ (C + 2) * δ := by
    intro x hx
    have hmem : T x ∈ S :=
      hSsub ⟨x, by simpa [Metric.mem_closedBall, dist_zero_right] using hx, rfl⟩
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.1 (htcover hmem)
    have h1 : ‖P n (T x) - P n y‖ ≤ C * δ := by
      have := (P n).le_opNorm (T x - y)
      rw [map_sub] at this
      refine this.trans ?_
      have hδ' : ‖T x - y‖ ≤ δ := by
        rw [← dist_eq_norm]
        exact (Metric.mem_ball.1 hy).le
      exact mul_le_mul (hC n) hδ' (norm_nonneg _) hC0
    have h2 : ‖P n y - y‖ ≤ δ := (hN n hn y hyt).le
    have h3 : ‖y - T x‖ ≤ δ := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact (Metric.mem_ball.1 hy).le
    have hsplit : (P n ∘L T - T) x = (P n (T x) - P n y) + (P n y - y) + (y - T x) := by
      simp only [sub_apply, ContinuousLinearMap.comp_apply]
      abel
    calc ‖(P n ∘L T - T) x‖ ≤ ‖P n (T x) - P n y‖ + ‖P n y - y‖ + ‖y - T x‖ := by
          rw [hsplit]
          exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ C * δ + δ + δ := by gcongr
      _ = (C + 2) * δ := by ring
  -- and hence the operator norm bound, by homogeneity
  have hop : ‖P n ∘L T - T‖ ≤ (C + 2) * δ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hc : ((‖x‖ : ℝ) : 𝕜) ≠ 0 := by
      simpa using hxpos.ne'
    have hy1 : ‖(((‖x‖ : ℝ) : 𝕜))⁻¹ • x‖ ≤ 1 := by
      rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hxpos, inv_mul_cancel₀ hxpos.ne']
    have hxeq : x = ((‖x‖ : ℝ) : 𝕜) • ((((‖x‖ : ℝ) : 𝕜))⁻¹ • x) := by
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    calc ‖(P n ∘L T - T) x‖
        = ‖x‖ * ‖(P n ∘L T - T) ((((‖x‖ : ℝ) : 𝕜))⁻¹ • x)‖ := by
          conv_lhs => rw [hxeq]
          rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos hxpos]
      _ ≤ ‖x‖ * ((C + 2) * δ) := by
          exact mul_le_mul_of_nonneg_left (hunit _ hy1) (norm_nonneg _)
      _ = (C + 2) * δ * ‖x‖ := by ring
  have hlt : (C + 2) * δ < ε := by
    rw [hδdef]
    rw [mul_div_assoc'] at *
    have hpos : 0 < 2 * (C + 2) := by linarith
    rw [div_lt_iff₀ hpos]
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact lt_of_le_of_lt hop hlt

/-- **Stability and convergence of a projection method for an equation of the second kind**
(Kress, *Numerical Analysis*, Ch. 12): let `T` be a compact operator with `1 - T` injective — by
the Fredholm alternative, invertible — and let `P n` be bounded projections converging pointwise
to the identity.  Then for all large `n` the projected equations are uniquely solvable, and the
error is bounded by the projection error of the exact solution, with a constant independent of
`n`.

The proof is `‖1 - P n T‖ → ‖1 - T‖` in operator norm
(`tendsto_norm_comp_sub_of_isCompactOperator`), so that `1 - P n T` is invertible with uniformly
bounded inverse by the Neumann perturbation `ContinuousLinearEquiv.exists_symm_norm_le_of_add`.
On the range of `P n` the projected equation `P n ((1 - T) u) = P n f` *is* `(1 - P n T) u = P n f`,
and `1 - P n T` preserves that range in both directions; the error identity
`(1 - P n T) (u - u*) = P n u* - u*` finishes the estimate. -/
theorem exists_isProjectionMethodSolution_of_isCompactOperator {T : X →L[𝕜] X}
    (hT : IsCompactOperator T) (hinj : Function.Injective (1 - T : X →L[𝕜] X))
    {P : ℕ → (X →L[𝕜] X)} (hP : ∀ n, IsIdempotentElem (P n))
    (hPtend : ∀ x, Filter.Tendsto (fun n => P n x) Filter.atTop (nhds x)) :
    ∃ C : ℝ, ∀ᶠ n in Filter.atTop, ∀ ustar : X, ∃ u,
      IsProjectionMethodSolution ((1 - T : X →L[𝕜] X) : X →ₗ[𝕜] X)
          ((1 - T : X →L[𝕜] X) ustar) (P n) u ∧
        (∀ u', IsProjectionMethodSolution ((1 - T : X →L[𝕜] X) : X →ₗ[𝕜] X)
            ((1 - T : X →L[𝕜] X) ustar) (P n) u' → u' = u) ∧
        ‖u - ustar‖ ≤ C * ‖P n ustar - ustar‖ := by
  -- the Fredholm alternative: `1 - T` is invertible
  have hres : (1 : 𝕜) ∈ resolventSet 𝕜 T := by
    refine (IsCompactOperator.hasEigenvalue_or_mem_resolventSet hT one_ne_zero).resolve_left ?_
    intro hev
    obtain ⟨x, hx, hx0⟩ := hev.exists_hasEigenvector
    refine hx0 (hinj ?_)
    have hTx : T x = x := by simpa using (Module.End.mem_eigenspace_iff.1 hx)
    simp [hTx]
  have hunit : IsUnit ((1 : X →L[𝕜] X) - T) := by
    have h : IsUnit (algebraMap 𝕜 (X →L[𝕜] X) 1 - T) := hres
    rwa [map_one] at h
  obtain ⟨v, hv⟩ := hunit
  set e : X ≃L[𝕜] X := ContinuousLinearEquiv.ofUnit v with he
  have hecoe : (e : X →L[𝕜] X) = 1 - T := hv
  set B : ℝ := ‖(e.symm : X →L[𝕜] X)‖ with hB
  refine ⟨2 * B, ?_⟩
  -- for large `n` the perturbation is small enough for the Neumann series
  have hsmall : ∀ᶠ n in Filter.atTop,
      B * ‖(1 - P n ∘L T : X →L[𝕜] X) - (e : X →L[𝕜] X)‖ < 1 / 2 := by
    have hd : ∀ n, (1 - P n ∘L T : X →L[𝕜] X) - (e : X →L[𝕜] X) = -(P n ∘L T - T) := by
      intro n
      rw [hecoe]
      abel
    have hlim : Filter.Tendsto (fun n => B * ‖(1 - P n ∘L T : X →L[𝕜] X) - (e : X →L[𝕜] X)‖)
        Filter.atTop (nhds 0) := by
      have := (tendsto_norm_comp_sub_of_isCompactOperator hT hPtend).const_mul B
      simpa only [hd, norm_neg, mul_zero] using this
    exact hlim.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hsmall] with n hn ustar
  obtain ⟨e', he'coe, he'norm, -⟩ :=
    ContinuousLinearEquiv.exists_symm_norm_le_of_add e
      ((1 - P n ∘L T : X →L[𝕜] X) - (e : X →L[𝕜] X)) (by linarith)
  have he'eq : (e' : X →L[𝕜] X) = 1 - P n ∘L T := by
    rw [he'coe]; abel
  have hBnn : 0 ≤ B := norm_nonneg _
  have hbound : ‖(e'.symm : X →L[𝕜] X)‖ ≤ 2 * B := by
    refine he'norm.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  -- the projected equation is `(1 - P n T) u = P n f` on the range of `P n`
  have hfix : ∀ u : X, u ∈ LinearMap.range ((P n : X →L[𝕜] X) : X →ₗ[𝕜] X) → P n u = u := by
    rintro _ ⟨w, rfl⟩
    exact DFunLike.congr_fun (hP n) w
  have hproj : ∀ u : X, P n u = u →
      P n (((1 - T : X →L[𝕜] X) : X →ₗ[𝕜] X) u) = (e' : X →L[𝕜] X) u := by
    intro u hu
    rw [he'eq]
    simp only [ContinuousLinearMap.coe_coe, sub_apply, one_apply_eq_self,
      ContinuousLinearMap.comp_apply, map_sub, hu]
  have hmemrange : ∀ y : X, e'.symm y ∈ LinearMap.range ((P n : X →L[𝕜] X) : X →ₗ[𝕜] X) ↔
      y ∈ LinearMap.range ((P n : X →L[𝕜] X) : X →ₗ[𝕜] X) := by
    intro y
    constructor
    · intro hy
      have := hproj _ (hfix _ hy)
      rw [ContinuousLinearEquiv.coe_coe, e'.apply_symm_apply] at this
      exact this ▸ LinearMap.mem_range_self _ _
    · intro hy
      have hval : e'.symm y = y + P n (T (e'.symm y)) := by
        have h1 : (e' : X →L[𝕜] X) (e'.symm y) = y := e'.apply_symm_apply y
        rw [he'eq] at h1
        simp only [sub_apply, one_apply_eq_self,
          ContinuousLinearMap.comp_apply] at h1
        exact sub_eq_iff_eq_add.1 h1
      rw [hval]
      exact Submodule.add_mem _ hy (LinearMap.mem_range_self _ _)
  set f : X := (1 - T : X →L[𝕜] X) ustar with hf
  have hPf : P n f ∈ LinearMap.range ((P n : X →L[𝕜] X) : X →ₗ[𝕜] X) :=
    LinearMap.mem_range_self _ _
  refine ⟨e'.symm (P n f), ⟨(hmemrange _).2 hPf, ?_⟩, ?_, ?_⟩
  · rw [hproj _ (hfix _ ((hmemrange _).2 hPf)), ContinuousLinearEquiv.coe_coe,
      e'.apply_symm_apply]
  · rintro u' ⟨hu'mem, hu'eq⟩
    have h1 : (e' : X →L[𝕜] X) u' = P n f := by
      rw [← hproj _ (hfix _ hu'mem)]
      exact hu'eq
    have h2 : u' = e'.symm ((e' : X →L[𝕜] X) u') := (e'.symm_apply_apply u').symm
    rw [h2, h1]
  · have hAu : (e' : X →L[𝕜] X) (e'.symm (P n f)) = P n f := e'.apply_symm_apply _
    have herr : (e' : X →L[𝕜] X) (e'.symm (P n f) - ustar) = P n ustar - ustar := by
      rw [map_sub, hAu, he'eq, hf]
      simp only [sub_apply, one_apply_eq_self,
        ContinuousLinearMap.comp_apply, map_sub]
      abel
    have hsol : e'.symm (P n f) - ustar = e'.symm (P n ustar - ustar) := by
      rw [← herr, ContinuousLinearEquiv.coe_coe, e'.symm_apply_apply]
    rw [hsol]
    exact (ContinuousLinearMap.le_opNorm (e'.symm : X →L[𝕜] X) _).trans
      (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))

end SecondKind
