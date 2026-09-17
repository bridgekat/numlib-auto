/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Normed.Operator.Unbounded.ClosedRange`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Normed.Operator.BanachSteinhaus
import Numlib.Analysis.Normed.Operator.Unbounded.Adjoint
import Numlib.Analysis.Normed.Operator.Unbounded.Basic

/-!
# The closed range theorem, and the characterization of surjective operators

For a densely defined closed operator `A : D(A) ⊆ E → F` between Banach spaces over `RCLike 𝕜`
with Banach adjoint `A* : D(A*) ⊆ F* → E*` (`LinearPMap.strongDualAdjoint`), this file proves
Banach's **closed range theorem** and the two **surjectivity criteria** of
[brezis2011functional] §2.7:

* Theorem 2.19: `R(A)` is closed ⟺ `R(A*)` is closed ⟺ `R(A) = N(A*)^⊥` ⟺ `R(A*) = N(A)^⊥`;
* Theorem 2.20: `A` is onto ⟺ `‖v‖ ≤ C ‖A* v‖` on `D(A*)` ⟺ `A*` is injective with closed range;
* Theorem 2.21: `A*` is onto ⟺ `‖u‖ ≤ C ‖A u‖` on `D(A)` ⟺ `A` is injective with closed range;

together with the finite-dimensional equivalences of Remark 2.20 and the specializations to a
bounded operator `T` and its adjoint `T.strongDualMap`, which the Fredholm alternative and the
reflexivity theory consume.

## The route

The book proves Theorem 2.19 by transporting the characterization of closed sums
(`Submodule.tfae_isClosed_sup`, Theorem 2.16) to `X = E × F` with `G = G(A)`, `L = E × {0}`,
which requires carrying `(E × F)* ≃ E* × F*` through annihilators, sums and closures. Here every
implication is proved directly, and the two substantial ones are:

* **Theorem 2.20 (b) ⇒ (a)**, the method of a priori estimates: a separation argument
  (`LinearPMap.ball_subset_closure_image_of_norm_le_norm_strongDualAdjoint`) shows that the
  closure of `A(B_{D(A)})` contains the ball of radius `1 / C`, and the second step of the open
  mapping theorem for a closed operator (`LinearPMap.IsClosed.exists_preimage_norm_le_of_approx`)
  turns the approximate preimages into exact ones;
* **Theorem 2.19 (ii) ⇒ (i)**: with `Z := closure R(A)` and `A₁ : D(A) ⊆ E → Z` the operator
  with restricted codomain, `A₁` is closed with dense range, so `A₁*` is injective;
  `R(A₁*) = R(A*)` by Hahn–Banach extension and restriction
  (`LinearPMap.range_strongDualAdjoint_codRestrict`);
  the closed range criterion for the closed injective `A₁*` gives `‖ζ‖ ≤ C ‖A₁* ζ‖`, and
  Theorem 2.20 (b) ⇒ (a) for `A₁` makes it onto `Z`.

Everything else is short: 2.19 (i) ⇒ (iv) is the closed range criterion `dist (u, N(A)) ≤ C ‖A u‖`
followed by a Hahn–Banach extension of `A u ↦ f u` from `R(A)`; (i) ⇒ (iii) is Corollary 2.18 (iv);
2.20 (a) ⇒ (b) is the uniform boundedness principle on `{v ∈ D(A*) | ‖A* v‖ ≤ 1}`; the remaining
clauses are the closed range criteria of `Numlib.Analysis.Normed.Operator.Unbounded.Basic` for
`A` and for `A*`.

## Hypotheses

Each statement carries only the completeness it uses: Theorem 2.20 (a) ⇒ (b) needs `F` complete,
(b) ⇒ (a) needs `E` complete, the closed range theorem needs both. `A` is assumed closed
(`hc : A.IsClosed`) where the proof uses it and densely defined (`hd : Dense (A.domain : Set E)`)
throughout, since the adjoint is only meaningful then. Names put the direction in the suffix
(`…_of_isClosed_range`, `…_of_range_eq_top`), and the `iff`/`TFAE` forms are separate theorems.

## References

[brezis2011functional], §2.7 (Theorems 2.19–2.21, Remarks 18–20) and Exercise 2.14; Atkinson and
Han, *Theoretical Numerical Analysis*, Theorem 8.2.7, which is Theorem 2.19 verbatim.
-/

open Filter Metric Topology

noncomputable section

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {A : E →ₗ.[𝕜] F}

/-!
### The separation step, and Theorem 2.20
-/

open scoped ComplexOrder in
/-- The image of the open unit ball of `D(A)` under `A` is absolutely convex. -/
private theorem absConvex_image_ball (A : E →ₗ.[𝕜] F) :
    AbsConvex 𝕜 ((fun u : A.domain => A u) '' {u | ‖(u : E)‖ < 1}) := by
  refine ⟨fun c hc => ?_, ?_⟩
  · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨c • u, ?_, by simp [map_smul]⟩
    change ‖((c • u : A.domain) : E)‖ < 1
    rw [Submodule.coe_smul, norm_smul]
    calc ‖c‖ * ‖(u : E)‖ ≤ 1 * ‖(u : E)‖ := by gcongr
      _ < 1 := by rw [one_mul]; exact hu
  · let _ : NormedSpace ℝ A.domain := NormedSpace.restrictScalars ℝ 𝕜 A.domain
    have : IsScalarTower ℝ 𝕜 A.domain := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have hball : Convex 𝕜 (ball (0 : A.domain) 1) :=
      convex_RCLike_iff_convex_real.2 (convex_ball 0 1)
    have hset : {u : A.domain | ‖(u : E)‖ < 1} = ball 0 1 := by
      ext u
      simp [Submodule.norm_coe]
    rw [hset]
    exact hball.linear_image A.toFun

open scoped ComplexOrder in
/-- **The separation step of Theorem 2.20 (b) ⇒ (a)** ([brezis2011functional], the argument of
Theorem 2.16 (b) ⇒ (a), (24) ⇒ (25), transposed to a closed operator). If
`‖v‖ ≤ C ‖A* v‖` for every `v ∈ D(A*)`, then the closure of `A(B_{D(A)})`, `B_{D(A)}` the open
unit ball of `D(A)`, contains the ball of radius `1 / C` of `F`.

If `y₀` with `‖y₀‖ < 1 / C` were outside that closed absolutely convex set,
`AbsConvex.exists_norm_apply_le_one_of_isClosed_of_notMem` would give `v ∈ F*` with
`‖v (A u)‖ ≤ ‖u‖` on `D(A)` and `1 < ‖v y₀‖`; then `v ∈ D(A*)` with `‖A* v‖ ≤ 1`, so `‖v‖ ≤ C` and
`‖v y₀‖ ≤ ‖v‖ ‖y₀‖ < 1`. Neither completeness nor closedness of `A` enters. -/
theorem ball_subset_closure_image_of_norm_le_norm_strongDualAdjoint
    (hd : Dense (A.domain : Set E)) {C : ℝ} (hC : 0 < C)
    (h : ∀ v : A.strongDualAdjoint.domain, ‖(v : StrongDual 𝕜 F)‖ ≤ C * ‖A.strongDualAdjoint v‖) :
    ball (0 : F) (1 / C) ⊆ _root_.closure ((fun u : A.domain => A u) '' {u | ‖(u : E)‖ < 1}) := by
  -- the real structure of `F`, for the separation theorem
  let _ : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F
  have : IsScalarTower ℝ 𝕜 F := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  set S := (fun u : A.domain => A u) '' {u | ‖(u : E)‖ < 1} with hS
  intro y₀ hy₀
  by_contra hy
  rw [mem_ball_zero_iff] at hy₀
  have hK : AbsConvex 𝕜 (_root_.closure S) := (absConvex_image_ball A).closure
  have hKne : (_root_.closure S).Nonempty :=
    ⟨0, subset_closure ⟨0, by simp, by simp⟩⟩
  obtain ⟨v, hvK, hvy⟩ :=
    hK.exists_norm_apply_le_one_of_isClosed_of_notMem hKne isClosed_closure hy
  -- `‖v (A u)‖ ≤ ‖u‖` on `D(A)`, by scaling into the unit ball
  have hbound : ∀ u : A.domain, ‖v (A u)‖ ≤ ‖(u : E)‖ := fun u => by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have ht : 0 < ‖(u : E)‖ + ε := by positivity
    set t : 𝕜 := ((‖(u : E)‖ + ε : ℝ) : 𝕜) with htdef
    have ht0 : t ≠ 0 := by
      rw [htdef, Ne, RCLike.ofReal_eq_zero]
      exact ht.ne'
    have hmem : A (t⁻¹ • u) ∈ S := ⟨t⁻¹ • u, by
      change ‖((t⁻¹ • u : A.domain) : E)‖ < 1
      rw [Submodule.coe_smul, norm_smul, norm_inv, htdef, RCLike.norm_ofReal, abs_of_pos ht,
        inv_mul_lt_iff₀ ht, mul_one]
      linarith, rfl⟩
    have := hvK _ (subset_closure hmem)
    rw [map_smul, _root_.map_smul, smul_eq_mul, norm_mul, norm_inv, htdef, RCLike.norm_ofReal,
      abs_of_pos ht, inv_mul_le_iff₀ ht, mul_one] at this
    exact this
  have hvD : v ∈ A.strongDualAdjoint.domain :=
    (A.mem_strongDualAdjoint_domain_iff v).2 ⟨1, fun u => by rw [one_mul]; exact hbound u⟩
  -- `‖A* v‖ ≤ 1`, by density of `D(A)`
  have hAv : ‖A.strongDualAdjoint ⟨v, hvD⟩‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    have hcl : _root_.IsClosed {x : E | ‖A.strongDualAdjoint ⟨v, hvD⟩ x‖ ≤ ‖x‖} :=
      isClosed_le (by fun_prop) (by fun_prop)
    have hsub : (A.domain : Set E) ⊆ {x : E | ‖A.strongDualAdjoint ⟨v, hvD⟩ x‖ ≤ ‖x‖} := by
      intro x hx
      change ‖A.strongDualAdjoint ⟨v, hvD⟩ (⟨x, hx⟩ : A.domain)‖ ≤ ‖x‖
      rw [strongDualAdjoint_apply hd]
      exact hbound ⟨x, hx⟩
    have hall : (Set.univ : Set E) ⊆ {x : E | ‖A.strongDualAdjoint ⟨v, hvD⟩ x‖ ≤ ‖x‖} := by
      rw [← hd.closure_eq]
      exact closure_minimal hsub hcl
    exact hall (Set.mem_univ x)
  -- the contradiction
  have hv : ‖v‖ ≤ C := (h ⟨v, hvD⟩).trans (by simpa using mul_le_mul_of_nonneg_left hAv hC.le)
  have : ‖v y₀‖ ≤ C * ‖y₀‖ := (v.le_opNorm y₀).trans (by gcongr)
  have hCy : C * ‖y₀‖ < 1 := by
    have := mul_lt_mul_of_pos_left hy₀ hC
    rwa [mul_one_div, div_self hC.ne'] at this
  linarith

/-- **Theorem 2.20 (b) ⇒ (a), the method of a priori estimates** ([brezis2011functional],
Theorem 2.20 and Remark 2.19): if `A` is closed, densely defined, `E` is complete and
`‖v‖ ≤ C ‖A* v‖` on `D(A*)`, then `A` is onto. The separation step puts the ball of radius
`1 / C` in the closure of `A(B_{D(A)})`, and the second step of the open mapping theorem for a
closed operator produces exact preimages. Completeness of `F` is not needed. -/
theorem IsClosed.range_eq_top_of_norm_le_norm_strongDualAdjoint [CompleteSpace E]
    (hc : A.IsClosed) (hd : Dense (A.domain : Set E)) {C : ℝ} (hC : 0 < C)
    (h : ∀ v : A.strongDualAdjoint.domain, ‖(v : StrongDual 𝕜 F)‖ ≤ C * ‖A.strongDualAdjoint v‖) :
    LinearMap.range A.toFun = ⊤ := by
  have hball := ball_subset_closure_image_of_norm_le_norm_strongDualAdjoint hd hC h
  rw [eq_top_iff]
  rintro y -
  obtain ⟨u, hu, -⟩ := hc.exists_preimage_norm_le_of_approx
    (A.exists_dist_le_of_ball_subset_closure_image hball (s := 1 / (2 * C)) (by positivity)
      (div_lt_div_of_pos_left one_pos hC (by linarith))) y
  exact LinearMap.mem_range.2 ⟨u, hu⟩

/-- **Theorem 2.20 (a) ⇒ (b)** ([brezis2011functional]): if `A` is densely defined and onto the
Banach space `F`, there is `C` with `‖v‖ ≤ C ‖A* v‖` for every `v ∈ D(A*)`. The set
`B* := {v ∈ D(A*) | ‖A* v‖ ≤ 1}` is bounded at every `f₀ = A u₀` (`|v f₀| = |(A* v) u₀| ≤ ‖u₀‖`),
hence bounded in norm by the uniform boundedness principle
(`StrongDual.isBounded_of_forall_eval_isBounded`); homogeneity gives the estimate, and `A* v = 0`
forces `v = 0` because `A` is onto. Closedness of `A` and completeness of `E` are not used. -/
theorem exists_norm_le_norm_strongDualAdjoint_of_range_eq_top [CompleteSpace F]
    (hd : Dense (A.domain : Set E)) (h : LinearMap.range A.toFun = ⊤) :
    ∃ C : ℝ, ∀ v : A.strongDualAdjoint.domain,
      ‖(v : StrongDual 𝕜 F)‖ ≤ C * ‖A.strongDualAdjoint v‖ := by
  set B : Set (StrongDual 𝕜 F) :=
    {v | ∃ hv : v ∈ A.strongDualAdjoint.domain, ‖A.strongDualAdjoint ⟨v, hv⟩‖ ≤ 1} with hB
  have hBb : Bornology.IsBounded B := by
    refine StrongDual.isBounded_of_forall_eval_isBounded fun f₀ => ?_
    obtain ⟨u₀, hu₀⟩ := LinearMap.mem_range.1 (h ▸ Submodule.mem_top (x := f₀))
    refine isBounded_iff_forall_norm_le.2 ⟨‖(u₀ : E)‖, ?_⟩
    rintro _ ⟨v, ⟨hv, hAv⟩, rfl⟩
    change ‖v f₀‖ ≤ ‖(u₀ : E)‖
    rw [← hu₀, toFun_eq_coe, ← strongDualAdjoint_apply hd ⟨v, hv⟩ u₀]
    have hle := mul_le_mul_of_nonneg_right hAv (norm_nonneg (u₀ : E))
    rw [one_mul] at hle
    exact (ContinuousLinearMap.le_opNorm _ _).trans hle
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hBb
  refine ⟨C, fun v => ?_⟩
  rcases eq_or_ne (A.strongDualAdjoint v) 0 with h0 | h0
  · -- `A* v = 0` forces `v = 0`, since `A` is onto
    have hv : (v : StrongDual 𝕜 F) = 0 := by
      have := ker_strongDualAdjoint_eq_bot_of_range_eq_top hd h
      rw [ker_eq_bot'] at this
      have := this v h0
      rw [this]
      rfl
    rw [hv, h0, norm_zero, norm_zero, mul_zero]
  · -- rescale `v` into `B*`
    have hn : 0 < ‖A.strongDualAdjoint v‖ := norm_pos_iff.2 h0
    set c : 𝕜 := ((‖A.strongDualAdjoint v‖⁻¹ : ℝ) : 𝕜) with hcdef
    have hcn : ‖c‖ = ‖A.strongDualAdjoint v‖⁻¹ := by
      rw [hcdef, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hn)]
    have hmem : c • (v : StrongDual 𝕜 F) ∈ B := by
      refine ⟨(c • v).2, ?_⟩
      have hsmul : A.strongDualAdjoint ⟨c • (v : StrongDual 𝕜 F), (c • v).2⟩ =
          c • A.strongDualAdjoint v := A.strongDualAdjoint.map_smul c v
      rw [hsmul, norm_smul, hcn, inv_mul_cancel₀ hn.ne']
    have := hC _ hmem
    rw [norm_smul, hcn, inv_mul_le_iff₀ hn] at this
    linarith

/-- **Theorem 2.20 (a) ⇔ (b)** ([brezis2011functional]): a closed densely defined operator between
Banach spaces is onto iff `‖v‖ ≤ C ‖A* v‖` on `D(A*)` for some constant `C`. -/
theorem IsClosed.range_eq_top_iff_exists_norm_le_norm_strongDualAdjoint [CompleteSpace E]
    [CompleteSpace F] (hc : A.IsClosed) (hd : Dense (A.domain : Set E)) :
    LinearMap.range A.toFun = ⊤ ↔ ∃ C : ℝ, ∀ v : A.strongDualAdjoint.domain,
      ‖(v : StrongDual 𝕜 F)‖ ≤ C * ‖A.strongDualAdjoint v‖ := by
  refine ⟨exists_norm_le_norm_strongDualAdjoint_of_range_eq_top hd, ?_⟩
  rintro ⟨C, hC⟩
  refine hc.range_eq_top_of_norm_le_norm_strongDualAdjoint hd
    (lt_of_lt_of_le one_pos (le_max_right C 1)) fun v => (hC v).trans ?_
  gcongr
  exact le_max_left _ _

/-- **Theorem 2.20 (a) ⇔ (c)** ([brezis2011functional]): a closed densely defined operator between
Banach spaces is onto iff `A*` is injective with closed range. Both directions go through the a
priori estimate (b): it gives the trivial kernel and the closed range of the closed operator `A*`
(`LinearPMap.ker_eq_bot_of_norm_le`, `LinearPMap.IsClosed.isClosed_range_of_norm_le`), and
conversely the closed range criterion for `A*` with `N(A*) = 0` reads `‖v‖ ≤ C ‖A* v‖`. -/
theorem IsClosed.range_eq_top_iff_ker_strongDualAdjoint_eq_bot_and_isClosed_range_strongDualAdjoint
    [CompleteSpace E] [CompleteSpace F] (hc : A.IsClosed) (hd : Dense (A.domain : Set E)) :
    LinearMap.range A.toFun = ⊤ ↔ A.strongDualAdjoint.ker = ⊥ ∧
      _root_.IsClosed (LinearMap.range A.strongDualAdjoint.toFun : Set (StrongDual 𝕜 E)) := by
  rw [hc.range_eq_top_iff_exists_norm_le_norm_strongDualAdjoint hd]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨ker_eq_bot_of_norm_le hC, (strongDualAdjoint_isClosed hd).isClosed_range_of_norm_le hC⟩
  · rintro ⟨hker, hrange⟩
    obtain ⟨C, hC⟩ :=
      (strongDualAdjoint_isClosed hd).isClosed_range_iff_exists_infDist_ker_le.1 hrange
    refine ⟨C, fun v => ?_⟩
    have := hC v
    rwa [hker, Submodule.bot_coe, infDist_singleton, dist_zero_right] at this

/-!
### The closed range theorem
-/

/-- **`R(A*) = N(A)^⊥` when `R(A)` is closed** ([brezis2011functional], Theorem 2.19 (i) ⇒ (iv)),
for a closed densely defined operator between Banach spaces. Given `f ∈ N(A)^⊥`, the functional
`A u ↦ f u` is well defined on `R(A)` and bounded by `C ‖f‖`, where `dist (u, N(A)) ≤ C ‖A u‖` is
the closed range criterion (`LinearPMap.IsClosed.isClosed_range_iff_exists_infDist_ker_le`); a
Hahn–Banach extension `v ∈ F*` of it satisfies `v (A u) = f u` on `D(A)`, so `v ∈ D(A*)` and
`A* v = f`. -/
theorem IsClosed.range_strongDualAdjoint_eq_annihilator_ker_of_isClosed_range [CompleteSpace E]
    [CompleteSpace F] (hc : A.IsClosed) (hd : Dense (A.domain : Set E))
    (h : _root_.IsClosed (LinearMap.range A.toFun : Set F)) :
    LinearMap.range A.strongDualAdjoint.toFun = A.ker.strongDualAnnihilator := by
  refine le_antisymm ((LinearMap.range A.strongDualAdjoint.toFun).le_topologicalClosure.trans
    (closure_range_strongDualAdjoint_le_annihilator_ker hd)) fun f hf => ?_
  rw [Submodule.mem_strongDualAnnihilator] at hf
  obtain ⟨C, hC⟩ := hc.isClosed_range_iff_exists_infDist_ker_le.1 h
  -- `‖f u‖ ≤ ‖f‖ dist (u, N(A))`, since `f` vanishes on `N(A)`
  have hfu : ∀ u : A.domain, ‖f u‖ ≤ ‖f‖ * infDist (u : E) (A.ker : Set E) := fun u => by
    have : Nonempty (A.ker : Set E) := ⟨⟨0, A.ker.zero_mem⟩⟩
    rw [infDist_eq_iInf, Real.mul_iInf_of_nonneg (norm_nonneg f)]
    refine le_ciInf fun z => ?_
    calc ‖f u‖ = ‖f ((u : E) - z)‖ := by rw [_root_.map_sub, hf z z.2, sub_zero]
      _ ≤ ‖f‖ * ‖(u : E) - z‖ := f.le_opNorm _
      _ = ‖f‖ * dist (u : E) z := by rw [dist_eq_norm]
  -- the functional `A u ↦ f u` on `R(A)`, through the quotient by `ker A`
  have hker : LinearMap.ker A.toFun ≤ LinearMap.ker ((f : E →ₗ[𝕜] 𝕜).comp A.domain.subtype) := by
    intro u hu
    rw [LinearMap.mem_ker] at hu ⊢
    exact hf u (mem_ker_iff.2 ⟨u, rfl, hu⟩)
  let φ₀ : LinearMap.range A.toFun →ₗ[𝕜] 𝕜 :=
    ((LinearMap.ker A.toFun).liftQ ((f : E →ₗ[𝕜] 𝕜).comp A.domain.subtype) hker).comp
      A.toFun.quotKerEquivRange.symm.toLinearMap
  have hφ₀ : ∀ u : A.domain, φ₀ ⟨A.toFun u, LinearMap.mem_range_self _ u⟩ = f u := fun u => by
    simp only [φ₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply,
      ContinuousLinearMap.coe_coe, Submodule.subtype_apply]
  have hφ₀b : ∀ y : LinearMap.range A.toFun, ‖φ₀ y‖ ≤ C * ‖f‖ * ‖y‖ := fun y => by
    obtain ⟨u, hu⟩ := LinearMap.mem_range.1 y.2
    have hy : y = ⟨A.toFun u, LinearMap.mem_range_self _ u⟩ := Subtype.ext hu.symm
    rw [hy, hφ₀ u]
    change ‖f u‖ ≤ C * ‖f‖ * ‖A u‖
    calc ‖f u‖ ≤ ‖f‖ * infDist (u : E) (A.ker : Set E) := hfu u
      _ ≤ ‖f‖ * (C * ‖A u‖) := by gcongr; exact hC u
      _ = C * ‖f‖ * ‖A u‖ := by ring
  obtain ⟨v, hv, -⟩ := exists_extension_norm_eq (LinearMap.range A.toFun)
    (φ₀.mkContinuous (C * ‖f‖) hφ₀b)
  have hvA : ∀ u : A.domain, f u = v (A u) := fun u => by
    have := hv ⟨A.toFun u, LinearMap.mem_range_self _ u⟩
    rw [LinearMap.mkContinuous_apply, hφ₀ u] at this
    exact this.symm
  have hvD : v ∈ A.strongDualAdjoint.domain := mem_strongDualAdjoint_domain_of_exists v ⟨f, hvA⟩
  exact ⟨⟨v, hvD⟩, strongDualAdjoint_apply_eq hd _ hvA⟩

/-- **`R(A) = N(A*)^⊥` when `R(A)` is closed** ([brezis2011functional], Theorem 2.19 (i) ⇒ (iii);
Atkinson–Han, Theorem 8.2.7 (a) ⇒ (b)), the abstract Fredholm alternative: `A u = f` is solvable
iff `v f = 0` for every `v ∈ D(A*)` with `A* v = 0`. This is Corollary 2.18 (iv) with the closure
removed; neither closedness of `A` nor completeness is needed. -/
theorem range_eq_strongDualCoannihilator_ker_strongDualAdjoint_of_isClosed_range
    (hd : Dense (A.domain : Set E)) (h : _root_.IsClosed (LinearMap.range A.toFun : Set F)) :
    LinearMap.range A.toFun = A.strongDualAdjoint.ker.strongDualCoannihilator := by
  rw [strongDualCoannihilator_ker_strongDualAdjoint_eq_closure_range hd,
    h.submodule_topologicalClosure_eq]

/-- The restriction of the codomain of a closed operator to a subspace containing its range is
closed: its graph is the preimage of `G(A)` under the continuous map `E × p → E × F`. -/
theorem IsClosed.codRestrict (hc : A.IsClosed) (p : Submodule 𝕜 F) (H : ∀ x, A x ∈ p) :
    (A.codRestrict p H).IsClosed := by
  have hc' : _root_.IsClosed (A.graph : Set (E × F)) := hc
  have hgraph : ((A.codRestrict p H).graph : Set (E × p)) =
      (fun q : E × p => (q.1, (q.2 : F))) ⁻¹' (A.graph : Set (E × F)) := by
    ext ⟨x, z⟩
    simp only [SetLike.mem_coe, mem_graph_iff, Set.mem_preimage]
    constructor
    · rintro ⟨u, hu, hAu⟩
      exact ⟨u, hu, by rw [← hAu]; rfl⟩
    · rintro ⟨u, hu, hAu⟩
      exact ⟨u, hu, Subtype.ext hAu⟩
  change _root_.IsClosed _
  rw [hgraph]
  exact hc'.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- **Restricting the codomain does not change the range of the adjoint**: for a densely defined
`A` and a subspace `p ⊆ F` containing `R(A)`, the adjoint of `A₁ : D(A) ⊆ E → p` has the same
range in `E*` as `A*`. A `ζ ∈ D(A₁*)` extends by Hahn–Banach to `v ∈ F*` with `v (A u) = ζ (A₁ u)`,
so `v ∈ D(A*)` and `A* v = A₁* ζ`; conversely `v ∈ D(A*)` restricts to
`ζ := v ∘ p.subtypeL ∈ D(A₁*)` with `A₁* ζ = A* v`. -/
theorem range_strongDualAdjoint_codRestrict (hd : Dense (A.domain : Set E)) (p : Submodule 𝕜 F)
    (H : ∀ x, A x ∈ p) :
    LinearMap.range (A.codRestrict p H).strongDualAdjoint.toFun =
      LinearMap.range A.strongDualAdjoint.toFun := by
  have hd' : Dense (((A.codRestrict p H).domain : Submodule 𝕜 E) : Set E) := hd
  ext f
  simp only [LinearMap.mem_range, toFun_eq_coe]
  constructor
  · rintro ⟨ζ, rfl⟩
    obtain ⟨v, hv, -⟩ := exists_extension_norm_eq p (ζ : StrongDual 𝕜 p)
    have hrel : ∀ u : A.domain, (A.codRestrict p H).strongDualAdjoint ζ u = v (A u) := fun u => by
      rw [strongDualAdjoint_apply hd' ζ u]
      exact (hv ⟨A u, H u⟩).symm
    have hvD : v ∈ A.strongDualAdjoint.domain := mem_strongDualAdjoint_domain_of_exists v ⟨_, hrel⟩
    exact ⟨⟨v, hvD⟩, strongDualAdjoint_apply_eq hd _ hrel⟩
  · rintro ⟨v, rfl⟩
    set ζ : StrongDual 𝕜 p := (v : StrongDual 𝕜 F).comp p.subtypeL with hζ
    have hrel : ∀ u : A.domain, A.strongDualAdjoint v u = ζ ((A.codRestrict p H) u) := fun u => by
      rw [strongDualAdjoint_apply hd v u]
      rfl
    have hζD : ζ ∈ (A.codRestrict p H).strongDualAdjoint.domain :=
      mem_strongDualAdjoint_domain_of_exists ζ ⟨_, hrel⟩
    exact ⟨⟨ζ, hζD⟩, strongDualAdjoint_apply_eq hd' _ hrel⟩

/-- The range of `A`, restricted to `closure R(A)`, is dense there. -/
private theorem dense_range_codRestrict_topologicalClosure (A : E →ₗ.[𝕜] F) :
    Dense ((LinearMap.range (A.codRestrict (LinearMap.range A.toFun).topologicalClosure
      fun u => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u)).toFun :
        Submodule 𝕜 (LinearMap.range A.toFun).topologicalClosure) :
          Set (LinearMap.range A.toFun).topologicalClosure) := by
  intro z
  rw [closure_subtype]
  have hval : Subtype.val '' ((LinearMap.range (A.codRestrict
      (LinearMap.range A.toFun).topologicalClosure
        fun u => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u)).toFun :
          Submodule 𝕜 (LinearMap.range A.toFun).topologicalClosure) :
            Set (LinearMap.range A.toFun).topologicalClosure) =
      (LinearMap.range A.toFun : Set F) := by
    ext y
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨_, ⟨u, rfl⟩, rfl⟩
  rw [hval, ← Submodule.topologicalClosure_coe]
  exact z.2

/-- **`R(A)` is closed when `R(A*)` is** ([brezis2011functional], Theorem 2.19 (ii) ⇒ (i)), the
substance of the closed range theorem, for a closed densely defined operator between Banach
spaces. Let `Z := closure R(A)` and `A₁ : D(A) ⊆ E → Z` be `A` with its codomain restricted. Then
`A₁` is closed with dense range, so `A₁*` is injective (`N(A₁*) = R(A₁)^⊥ = 0`); `R(A₁*) = R(A*)`
is closed (`range_strongDualAdjoint_codRestrict`); the closed range criterion for the closed
injective operator `A₁*` gives `‖ζ‖ ≤ C ‖A₁* ζ‖` on `D(A₁*)`, and Theorem 2.20 (b) ⇒ (a) for `A₁`
makes it onto `Z`, i.e. `R(A) = Z`. -/
theorem IsClosed.isClosed_range_of_isClosed_range_strongDualAdjoint [CompleteSpace E]
    [CompleteSpace F] (hc : A.IsClosed) (hd : Dense (A.domain : Set E))
    (h : _root_.IsClosed (LinearMap.range A.strongDualAdjoint.toFun : Set (StrongDual 𝕜 E))) :
    _root_.IsClosed (LinearMap.range A.toFun : Set F) := by
  set Z := (LinearMap.range A.toFun).topologicalClosure with hZ
  have hZc : _root_.IsClosed (Z : Set F) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace Z := hZc.completeSpace_coe
  have hmem : ∀ u : A.domain, A u ∈ Z := fun u =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u)
  set A₁ := A.codRestrict Z hmem with hA₁
  have hd₁ : Dense ((A₁.domain : Submodule 𝕜 E) : Set E) := hd
  have hc₁ : A₁.IsClosed := hc.codRestrict Z hmem
  -- `A₁*` is injective, with the closed range of `A*`
  have hker : A₁.strongDualAdjoint.ker = ⊥ := by
    rw [ker_strongDualAdjoint_eq_annihilator_range hd₁, Submodule.strongDualAnnihilator_eq_bot_iff]
    exact A.dense_range_codRestrict_topologicalClosure
  have hrange : _root_.IsClosed (LinearMap.range A₁.strongDualAdjoint.toFun :
      Set (StrongDual 𝕜 E)) := by
    rw [hA₁, range_strongDualAdjoint_codRestrict hd Z hmem]
    exact h
  -- the closed range criterion for the closed injective `A₁*`
  obtain ⟨C, hC⟩ :=
    (strongDualAdjoint_isClosed hd₁).isClosed_range_iff_exists_infDist_ker_le.1 hrange
  have hbound : ∀ ζ : A₁.strongDualAdjoint.domain,
      ‖(ζ : StrongDual 𝕜 Z)‖ ≤ max C 1 * ‖A₁.strongDualAdjoint ζ‖ := fun ζ => by
    have := hC ζ
    rw [hker, Submodule.bot_coe, infDist_singleton, dist_zero_right] at this
    calc ‖(ζ : StrongDual 𝕜 Z)‖ ≤ C * ‖A₁.strongDualAdjoint ζ‖ := this
      _ ≤ max C 1 * ‖A₁.strongDualAdjoint ζ‖ := by gcongr; exact le_max_left _ _
  -- `A₁` is onto `Z`, so `R(A) = Z`
  have htop := hc₁.range_eq_top_of_norm_le_norm_strongDualAdjoint hd₁
    (lt_of_lt_of_le one_pos (le_max_right C 1)) hbound
  have hZle : Z ≤ LinearMap.range A.toFun := fun z hz => by
    have hz' : (⟨z, hz⟩ : Z) ∈ LinearMap.range A₁.toFun := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨u, hu⟩ := LinearMap.mem_range.1 hz'
    exact ⟨u, congrArg Subtype.val hu⟩
  rw [le_antisymm (Submodule.le_topologicalClosure _) hZle]
  exact hZc

/-- **Theorem 2.19 (i) ⇔ (ii)** ([brezis2011functional]): for a closed densely defined operator
between Banach spaces, `R(A*)` is closed iff `R(A)` is. -/
theorem IsClosed.isClosed_range_strongDualAdjoint_iff [CompleteSpace E] [CompleteSpace F]
    (hc : A.IsClosed) (hd : Dense (A.domain : Set E)) :
    _root_.IsClosed (LinearMap.range A.strongDualAdjoint.toFun : Set (StrongDual 𝕜 E)) ↔
      _root_.IsClosed (LinearMap.range A.toFun : Set F) := by
  refine ⟨hc.isClosed_range_of_isClosed_range_strongDualAdjoint hd, fun h => ?_⟩
  rw [hc.range_strongDualAdjoint_eq_annihilator_ker_of_isClosed_range hd h]
  exact Submodule.isClosed_strongDualAnnihilator _

/-- **The closed range theorem** ([brezis2011functional], Theorem 2.19; Atkinson–Han,
Theorem 8.2.7). For a closed densely defined operator `A : D(A) ⊆ E → F` between Banach spaces
over `RCLike 𝕜`, the following are equivalent: (i) `R(A)` is closed; (ii) `R(A*)` is closed;
(iii) `R(A) = N(A*)^⊥`; (iv) `R(A*) = N(A)^⊥`. -/
theorem IsClosed.isClosed_range_tfae [CompleteSpace E] [CompleteSpace F] (hc : A.IsClosed)
    (hd : Dense (A.domain : Set E)) :
    [_root_.IsClosed (LinearMap.range A.toFun : Set F),
      _root_.IsClosed (LinearMap.range A.strongDualAdjoint.toFun : Set (StrongDual 𝕜 E)),
      LinearMap.range A.toFun = A.strongDualAdjoint.ker.strongDualCoannihilator,
      LinearMap.range A.strongDualAdjoint.toFun = A.ker.strongDualAnnihilator].TFAE := by
  tfae_have 1 → 4 := hc.range_strongDualAdjoint_eq_annihilator_ker_of_isClosed_range hd
  tfae_have 4 → 2 := fun h => by
    rw [h]
    exact Submodule.isClosed_strongDualAnnihilator _
  tfae_have 2 → 1 := hc.isClosed_range_of_isClosed_range_strongDualAdjoint hd
  tfae_have 1 → 3 := range_eq_strongDualCoannihilator_ker_strongDualAdjoint_of_isClosed_range hd
  tfae_have 3 → 1 := fun h => by
    rw [h]
    exact Submodule.isClosed_strongDualCoannihilator _
  tfae_finish

/-!
### Theorem 2.21 and Remark 2.20
-/

/-- **Theorem 2.21 (a) ⇔ (c)** ([brezis2011functional]): for a closed densely defined operator
between Banach spaces, `A*` is onto iff `A` is injective with closed range. Forward: `N(A) =
R(A*)^⊥ = 0` and `R(A)` is closed by the closed range theorem since `R(A*) = E*` is; backward:
`R(A*) = N(A)^⊥ = 0^⊥ = E*`. -/
theorem IsClosed.range_strongDualAdjoint_eq_top_iff_ker_eq_bot_and_isClosed_range [CompleteSpace E]
    [CompleteSpace F] (hc : A.IsClosed) (hd : Dense (A.domain : Set E)) :
    LinearMap.range A.strongDualAdjoint.toFun = ⊤ ↔
      A.ker = ⊥ ∧ _root_.IsClosed (LinearMap.range A.toFun : Set F) := by
  constructor
  · intro h
    refine ⟨hc.ker_eq_bot_of_range_strongDualAdjoint_eq_top hd h, ?_⟩
    refine hc.isClosed_range_of_isClosed_range_strongDualAdjoint hd ?_
    rw [h]
    exact isClosed_univ
  · rintro ⟨hker, hrange⟩
    rw [hc.range_strongDualAdjoint_eq_annihilator_ker_of_isClosed_range hd hrange, hker,
      Submodule.strongDualAnnihilator_bot]

/-- **Theorem 2.21 (a) ⇔ (b)** ([brezis2011functional]): for a closed densely defined operator
between Banach spaces, `A*` is onto iff `‖u‖ ≤ C ‖A u‖` on `D(A)` for some constant `C`. Through
(c): the estimate gives a trivial kernel and a closed range (`LinearPMap.ker_eq_bot_of_norm_le`,
`LinearPMap.IsClosed.isClosed_range_of_norm_le`), and conversely the closed range criterion with
`N(A) = 0` reads `‖u‖ ≤ C ‖A u‖`. -/
theorem IsClosed.range_strongDualAdjoint_eq_top_iff_exists_norm_le_norm [CompleteSpace E]
    [CompleteSpace F] (hc : A.IsClosed) (hd : Dense (A.domain : Set E)) :
    LinearMap.range A.strongDualAdjoint.toFun = ⊤ ↔
      ∃ C : ℝ, ∀ u : A.domain, ‖(u : E)‖ ≤ C * ‖A u‖ := by
  rw [hc.range_strongDualAdjoint_eq_top_iff_ker_eq_bot_and_isClosed_range hd]
  constructor
  · rintro ⟨hker, hrange⟩
    obtain ⟨C, hC⟩ := hc.isClosed_range_iff_exists_infDist_ker_le.1 hrange
    refine ⟨C, fun u => ?_⟩
    have := hC u
    rwa [hker, Submodule.bot_coe, infDist_singleton, dist_zero_right] at this
  · rintro ⟨C, hC⟩
    exact ⟨ker_eq_bot_of_norm_le hC, hc.isClosed_range_of_norm_le hC⟩

/-- **Remark 2.20, the finite-dimensional case** ([brezis2011functional]): if `E` or `F` is
finite-dimensional, a closed densely defined operator between Banach spaces is onto iff `A*` is
injective, because `R(A*)` is then finite-dimensional, hence closed. -/
theorem IsClosed.range_eq_top_iff_ker_strongDualAdjoint_eq_bot_of_finiteDimensional
    [CompleteSpace E] [CompleteSpace F] (hc : A.IsClosed) (hd : Dense (A.domain : Set E))
    (h : FiniteDimensional 𝕜 E ∨ FiniteDimensional 𝕜 F) :
    LinearMap.range A.toFun = ⊤ ↔ A.strongDualAdjoint.ker = ⊥ := by
  refine ⟨ker_strongDualAdjoint_eq_bot_of_range_eq_top hd, fun hk => ?_⟩
  rw [hc.range_eq_top_iff_ker_strongDualAdjoint_eq_bot_and_isClosed_range_strongDualAdjoint hd]
  refine ⟨hk, ?_⟩
  have : FiniteDimensional 𝕜 (LinearMap.range A.strongDualAdjoint.toFun) := by
    rcases h with hE | hF
    · infer_instance
    · have : FiniteDimensional 𝕜 A.strongDualAdjoint.domain := inferInstance
      infer_instance
  exact Submodule.closed_of_finiteDimensional _

/-- **Remark 2.20, the dual finite-dimensional case** ([brezis2011functional]): if `E` or `F` is
finite-dimensional, `A*` is onto iff `A` is injective, because `R(A)` is then finite-dimensional,
hence closed. -/
theorem IsClosed.range_strongDualAdjoint_eq_top_iff_ker_eq_bot_of_finiteDimensional
    [CompleteSpace E] [CompleteSpace F] (hc : A.IsClosed) (hd : Dense (A.domain : Set E))
    (h : FiniteDimensional 𝕜 E ∨ FiniteDimensional 𝕜 F) :
    LinearMap.range A.strongDualAdjoint.toFun = ⊤ ↔ A.ker = ⊥ := by
  refine ⟨hc.ker_eq_bot_of_range_strongDualAdjoint_eq_top hd, fun hk => ?_⟩
  rw [hc.range_strongDualAdjoint_eq_top_iff_ker_eq_bot_and_isClosed_range hd]
  refine ⟨hk, ?_⟩
  have : FiniteDimensional 𝕜 (LinearMap.range A.toFun) := by
    rcases h with hE | hF
    · have : FiniteDimensional 𝕜 A.domain := inferInstance
      infer_instance
    · infer_instance
  exact Submodule.closed_of_finiteDimensional _

end LinearPMap

/-!
### Bounded operators
-/

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The range of a linear map restricted to the whole space, as a `LinearPMap`, is its range. -/
private theorem range_toPMap_top (f : E →ₗ[𝕜] F) :
    LinearMap.range (f.toPMap ⊤).toFun = LinearMap.range f := by
  change LinearMap.range (f.comp (⊤ : Submodule 𝕜 E).subtype) = LinearMap.range f
  rw [LinearMap.range_comp, Submodule.range_subtype, ← LinearMap.range_eq_map]

/-- The whole space is a dense subspace. -/
private theorem dense_top : Dense (((⊤ : Submodule 𝕜 E) : Submodule 𝕜 E) : Set E) := by
  rw [Submodule.top_coe]
  exact dense_univ

/-- **The closed range theorem for a bounded operator** ([brezis2011functional], Theorem 2.19
(i) ⇔ (ii)): for `T : E →L[𝕜] F` between Banach spaces, `R(T*)` is closed iff `R(T)` is. -/
theorem isClosed_range_strongDualMap_iff [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F) :
    IsClosed (Set.range T.strongDualMap) ↔ IsClosed (Set.range T) := by
  have := (T.isClosed_toPMap (p := ⊤) isClosed_univ).isClosed_range_strongDualAdjoint_iff dense_top
  rwa [T.toPMap_strongDualAdjoint dense_top, range_toPMap_top, range_toPMap_top,
    LinearMap.coe_range, LinearMap.coe_range, coe_coe, coe_coe] at this

/-- **`R(T) = N(T*)^⊥` for a bounded operator with closed range** ([brezis2011functional],
Theorem 2.19 (i) ⇒ (iii)), the shape of the Fredholm alternative `R(I - T) = N(I - T*)^⊥`
(Theorem 6.6): `N(T*) = R(T)^⊥` and the bipolar identity. No completeness is needed. -/
theorem range_eq_strongDualCoannihilator_ker_strongDualMap (T : E →L[𝕜] F)
    (h : IsClosed (Set.range T)) :
    LinearMap.range (T : E →ₗ[𝕜] F) = T.strongDualMap.ker.strongDualCoannihilator := by
  rw [ker_strongDualMap_eq_annihilator_range,
    Submodule.strongDualCoannihilator_strongDualAnnihilator,
    IsClosed.submodule_topologicalClosure_eq]
  rwa [LinearMap.coe_range, coe_coe]

/-- **`R(T*) = N(T)^⊥` for a bounded operator with closed range** between Banach spaces
([brezis2011functional], Theorem 2.19 (i) ⇒ (iv)). -/
theorem range_strongDualMap_eq_annihilator_ker [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F)
    (h : IsClosed (Set.range T)) :
    LinearMap.range (T.strongDualMap : StrongDual 𝕜 F →ₗ[𝕜] StrongDual 𝕜 E) =
      T.ker.strongDualAnnihilator := by
  have h' : IsClosed ((LinearMap.range ((T : E →ₗ[𝕜] F).toPMap ⊤).toFun : Submodule 𝕜 F) :
      Set F) := by
    rwa [range_toPMap_top, LinearMap.coe_range, coe_coe]
  have := (T.isClosed_toPMap (p := ⊤)
    isClosed_univ).range_strongDualAdjoint_eq_annihilator_ker_of_isClosed_range dense_top h'
  rwa [T.toPMap_strongDualAdjoint dense_top, range_toPMap_top, LinearMap.toPMap_ker, top_inf_eq]
    at this

/-- **Theorem 2.20 for a bounded operator** ([brezis2011functional]): `T : E →L[𝕜] F` between
Banach spaces is onto iff `‖v‖ ≤ C ‖T* v‖` for every `v ∈ F*`. -/
theorem range_eq_top_iff_exists_norm_le_norm_strongDualMap [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F) :
    Function.Surjective T ↔ ∃ C : ℝ, ∀ v : StrongDual 𝕜 F, ‖v‖ ≤ C * ‖T.strongDualMap v‖ := by
  have := (T.isClosed_toPMap (p := ⊤)
    isClosed_univ).range_eq_top_iff_exists_norm_le_norm_strongDualAdjoint dense_top
  rw [T.toPMap_strongDualAdjoint dense_top, range_toPMap_top, LinearMap.range_eq_top, coe_coe]
    at this
  rw [this]
  simp only [LinearMap.toPMap_domain, LinearMap.toPMap_apply, coe_coe, Subtype.forall,
    Submodule.mem_top, forall_const]

/-- **Theorem 2.21 for a bounded operator** ([brezis2011functional]): the adjoint of
`T : E →L[𝕜] F` between Banach spaces is onto iff `‖u‖ ≤ C ‖T u‖` for every `u`, i.e. iff `T` is
bounded below (Mathlib's `AntilipschitzWith`; with
`ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective` this is Theorem 2.21 (a) ⇔ (c)
once more). -/
theorem range_strongDualMap_eq_top_iff_exists_norm_le_norm [CompleteSpace E] [CompleteSpace F]
    (T : E →L[𝕜] F) :
    Function.Surjective T.strongDualMap ↔ ∃ C : ℝ, ∀ u, ‖u‖ ≤ C * ‖T u‖ := by
  have := (T.isClosed_toPMap (p := ⊤)
    isClosed_univ).range_strongDualAdjoint_eq_top_iff_exists_norm_le_norm dense_top
  rw [T.toPMap_strongDualAdjoint dense_top, range_toPMap_top, LinearMap.range_eq_top, coe_coe]
    at this
  rw [this]
  simp only [LinearMap.toPMap_domain, LinearMap.toPMap_apply, coe_coe, Subtype.forall,
    Submodule.mem_top, forall_const]

end ContinuousLinearMap

end
