/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Numlib.Analysis.Normed.Operator.CollectivelyCompact
import Numlib.Variational.Galerkin

/-!
# Projection methods for operator equations

Let $X$ be a normed space, $A : X \to X$ a linear operator, $f \in X$, and $P$ a bounded projection
of $X$ onto a trial space. The **projection method** for the equation $Au = f$ seeks
$$u \in \operatorname{range} P, \qquad P(Au) = Pf,$$
as in (11.30) of [kress1998numerical]. This is the operator form of the Galerkin method of
`Numlib.Variational.Galerkin`: the data are an operator and a projection instead of a sesquilinear
form. For an orthogonal projection onto a subspace $K$ of a Hilbert space, the projection method is
the Galerkin method on $K$. If $A$ is bounded and coercive with constant $c > 0$, Céa's lemma then
reads
$$\|u^* - u\| \le \frac{\|A\|}{c} \inf_{v \in K} \|u^* - v\|,$$
where $u^*$ is the exact solution. For an equation of the second kind $(I - T)u = f$ with $T$
compact, projections that converge pointwise to the identity give a stable and convergent method.

## Main definitions

* `IsProjectionMethodSolution`: $u$ is a solution of the projection method for $Au = f$ with the
  projection $P$.

## Main results

* `isProjectionMethodSolution_starProjection_iff`: for an orthogonal projection, the projection
  method is the Galerkin method.
* `IsProjectionMethodSolution.norm_sub_le_of_isCoercive`: Céa's lemma in operator form for a bounded
  coercive $A$.
* `existsUnique_isProjectionMethodSolution_of_isCoercive`: for a bounded coercive $A$ and a complete
  trial space, the projection method has exactly one solution.
* `exists_isProjectionMethodSolution_of_isCompactOperator`: for $T$ compact with $I - T$ injective
  and projections that converge pointwise to the identity, the projection method for $(I - T)u = f$
  is uniquely solvable for all large $n$, with an error bound uniform in $n$.
-/

section Defs

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **The projection method** for the operator equation $Au = f$. Let $X$ be a normed space,
$A : X \to X$ linear, $f \in X$, and $P : X \to X$ bounded and linear. A point $u$ **solves the
projection method** if
$$u \in \operatorname{range} P \qquad \text{and} \qquad P(Au) = Pf.$$
This is (11.30) of [kress1998numerical].

Only the projected residual must vanish. This makes the problem computable and
finite-dimensional when the range of $P$ is finite-dimensional. The definition does not require
$P$ to be idempotent; the results that need it assume it. For an orthogonal projection on a
Hilbert space, the definition is the Galerkin method with initial guess $0$
(`isProjectionMethodSolution_starProjection_iff`). -/
def IsProjectionMethodSolution (A : X →ₗ[𝕜] X) (f : X) (P : X →L[𝕜] X) (u : X) : Prop :=
  u ∈ LinearMap.range (P : X →ₗ[𝕜] X) ∧ P (A u) = P f

/-- If $P$ is idempotent and $u$ solves the projection method with $P$, then $Pu = u$. -/
theorem IsProjectionMethodSolution.apply_eq_self {A : X →ₗ[𝕜] X} {f : X} {P : X →L[𝕜] X}
    (hP : IsIdempotentElem P) {u : X} (h : IsProjectionMethodSolution A f P u) : P u = u := by
  obtain ⟨v, rfl⟩ := h.1
  exact DFunLike.congr_fun hP v

end Defs

section Hilbert

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]

/-- **The projection method for an orthogonal projection is the Galerkin method.** Let $X$ be an
inner product space, $A : X \to X$ linear, $f \in X$, and $K$ a subspace of $X$ with orthogonal
projection $P_K$. Then $u$ solves the projection method with $P_K$ if and only if
$$u \in K \qquad \text{and} \qquad f - Au \perp K.$$
See §12.1 of [kress1998numerical].

The right-hand side is `IsGalerkin A f 0 K u` of `Numlib.Projection.Basic`, and $P_K$ is
`K.starProjection`. -/
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

/-- **Céa's lemma in operator form.** Let $X$ be a Hilbert space, let $A : X \to X$ be bounded,
linear and coercive with constant $c > 0$, that is, $\operatorname{Re} \langle Ax, x \rangle \ge
c \|x\|^2$ for all $x$, and let $K$ be a subspace of $X$ with orthogonal projection $P_K$. Let
$u^*$ satisfy $Au^* = f$, and let $u$ solve the projection method for $Au = f$ with $P_K$. Then
$$\|u^* - u\| \le \frac{\|A\|}{c} \operatorname{dist}(u^*, K),$$
so the projection method is quasi-optimal. This is Theorem 11.17 of [kress1998numerical].

This is the operator form of `IsGalerkinSolution.norm_sub_le_infDist`. The form
$(u, v) \mapsto \langle Au, v \rangle$ has the same coercivity constant and the same norm as
$A$, so the constant $M / c$ of Céa's lemma becomes $\|A\| / c$. -/
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

/-- **Unique solvability of the projection method for a coercive operator.** Let $X$ be a Hilbert
space, let $A : X \to X$ be bounded, linear and coercive with constant $c > 0$, and let $K$ be a
complete subspace of $X$ with orthogonal projection $P_K$. Then for every $f \in X$ the
projection method for $Au = f$ with $P_K$ has exactly one solution. This is part of Theorem
11.17 of [kress1998numerical].

The proof applies the Lax–Milgram lemma to the restriction of the form
$(u, v) \mapsto \langle Au, v \rangle$ to $K$. -/
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

/-- If $P_n x \to x$ for every $x$ and $T$ is compact, then $\|P_n T - T\| \to 0$; this is
`tendsto_opNorm_comp_of_isCompactOperator` for the family $P_n - I$, and it is the only use of
the compactness of $T$. -/
private theorem tendsto_norm_comp_sub_of_isCompactOperator {T : X →L[𝕜] X}
    (hT : IsCompactOperator T) {P : ℕ → (X →L[𝕜] X)}
    (hP : ∀ x, Filter.Tendsto (fun n => P n x) Filter.atTop (nhds x)) :
    Filter.Tendsto (fun n => ‖P n ∘L T - T‖) Filter.atTop (nhds 0) := by
  have hid : ∀ n, P n ∘L T - T = (P n - 1 : X →L[𝕜] X) ∘L T := fun n => by
    ext x
    simp
  have hzero : ∀ x, Filter.Tendsto (fun n => (P n - 1 : X →L[𝕜] X) x) Filter.atTop (nhds 0) :=
    fun x => by simpa using (hP x).sub (tendsto_const_nhds (x := x))
  simpa only [hid] using tendsto_opNorm_comp_of_isCompactOperator hzero hT

/-- **Stability and convergence of a projection method for an equation of the second kind.** Let $X$
be a Banach space, let $T : X \to X$ be a compact operator with $I - T$ injective, and let
$P_n : X \to X$ be bounded projections with $P_n x \to x$ for every $x \in X$. Then there is a
constant $C$ such that for all large $n$ and every $u^* \in X$ the projection method for
$$(I - T)u = f, \qquad f = (I - T)u^*,$$
with the projection $P_n$ has exactly one solution $u$, and
$$\|u - u^*\| \le C \|P_n u^* - u^*\|.$$
See Chapter 12 of [kress1998numerical].

By the Fredholm alternative, $I - T$ is invertible, so every $f$ has this form. Compactness of
$T$ makes $P_n T \to T$ in operator norm, so $I - P_n T$ is invertible with uniformly bounded
inverse by the Neumann series perturbation `ContinuousLinearEquiv.exists_symm_norm_le_of_add`.
On the range of $P_n$ the projected equation $P_n(I - T)u = P_n f$ is $(I - P_n T)u = P_n f$,
and the error identity $(I - P_n T)(u - u^*) = P_n u^* - u^*$ gives the estimate. -/
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
