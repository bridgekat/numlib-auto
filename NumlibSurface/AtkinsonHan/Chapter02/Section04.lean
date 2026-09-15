import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Analysis.Sobolev.Interval
import Numlib.Approximation.Quadrature

/-!
# Atkinson–Han §2.4: more results on linear operators

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §2.4.

The book's `cond(L) = ‖L⁻¹‖ ‖L‖` is defined here as `AtkinsonHan.Chapter02.cond`, with
`cond_eq_condNumber` identifying it, for `V = W`, with the backbone's
`NormedRing.condNumber` (`Numlib.Analysis.Normed.Ring.CondNumber`).

## Main results

* `theorem_2_4_1` — the extension theorem, for the completion of a normed space.
* `theorem_2_4_3` — the bounded inverse theorem (a corollary of the open mapping theorem).
* `stability_of_isomorphism`, `equation_2_4_1`, `one_le_cond` — the conditioning bounds (2.4.1).
* `theorem_2_4_4` — the principle of uniform boundedness.
* `theorem_2_4_5` — the Banach–Steinhaus theorem on a dense subspace.
* `tendsto_of_tendsto_on_dense_of_bounded` — its ε/3 half, in the generality it is proved in.
* `equation_2_4_4`, `quadrature_convergence` — §2.4.4, the convergence of numerical quadrature.
* `example_2_4_2_norm_le`, `example_2_4_2_dense`, `example_2_4_2`, `example_2_4_2_opNorm_le` —
  Example 2.4.2, the differentiation operator `D v = v'` on `C¹[0, 1]` and its extension to
  `H¹(0, 1)`.

Theorems 2.4.4 and 2.4.5 are Mathlib's `banach_steinhaus` and the backbone's
`ContinuousLinearMap.tendsto_iff_tendsto_on_dense_of_completeSpace`
(`Numlib/Analysis/Normed/Operator/BanachSteinhaus.lean`), which is where the ε/3 argument lives.

## Example 2.4.2

The book gives `C¹[0, 1]` the inner product norm `‖v‖_{1,2} = (‖v‖₂² + ‖v'‖₂²)^{1/2}` and calls
its completion `H¹(0, 1)`. Here `H¹(0, 1)` is the backbone's `SobolevInterval 1 0 1`
(`Numlib/Analysis/Sobolev/Interval.lean`), and `C¹[0, 1]` carrying `‖·‖_{1,2}` is its image under
the injective inclusion `ContDiffMapIcc.toSobolevInterval`, which carries `‖·‖_{1,2}` to the `H¹`
norm by construction. That `H¹(0, 1)` *is* a completion of it is then `example_2_4_2_dense`
together with the completeness of `H¹(0, 1)`, and the extension theorem takes the form
`example_2_4_2`: a unique continuous extension off a dense subspace.
-/

open Filter Topology NNReal

namespace AtkinsonHan.Chapter02

variable {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-! ### Theorem 2.4.1: the extension theorem -/

/-- **Extension theorem** (Theorem 2.4.1). A bounded linear operator `L ∈ 𝓛(V, W)` from a normed
space `V` into a Banach space `W` extends uniquely to a bounded linear operator on the completion
`V̂` of `V`, and the extension has the same norm. -/
theorem theorem_2_4_1 [CompleteSpace W] (L : V →L[𝕜] W) :
    ∃ Lhat : UniformSpace.Completion V →L[𝕜] W, (∀ v : V, Lhat ↑v = L v) ∧ ‖Lhat‖ = ‖L‖ ∧
      ∀ L' : UniformSpace.Completion V →L[𝕜] W, (∀ v : V, L' ↑v = L v) → L' = Lhat := by
  have hdense : DenseRange (UniformSpace.Completion.toComplL : V →L[𝕜] UniformSpace.Completion V) :=
    UniformSpace.Completion.denseRange_coe
  have hind :
      IsUniformInducing (UniformSpace.Completion.toComplL : V →L[𝕜] UniformSpace.Completion V) :=
    UniformSpace.Completion.isUniformInducing_coe V
  set Lhat := L.extend (UniformSpace.Completion.toComplL : V →L[𝕜] UniformSpace.Completion V)
    with hLhat
  have heq : ∀ v : V, Lhat ↑v = L v := fun v => L.extend_eq hdense hind v
  refine ⟨Lhat, heq, le_antisymm ?_ ?_, ?_⟩
  · have hbound : ∀ x : V, ‖x‖ ≤ (1 : ℝ≥0) *
        ‖(UniformSpace.Completion.toComplL : V →L[𝕜] UniformSpace.Completion V) x‖ := by
      intro x
      simp
    simpa using L.opNorm_extend_le hdense hbound
  · refine L.opNorm_le_bound (norm_nonneg _) fun v => ?_
    rw [← heq v]
    simpa [UniformSpace.Completion.norm_coe] using Lhat.le_opNorm (↑v : UniformSpace.Completion V)
  · intro L' hL'
    rw [hLhat]
    exact (ContinuousLinearMap.extend_unique L hdense hind L' (by ext v; exact hL' v)).symm

/-! ### Theorem 2.4.3: the bounded inverse theorem -/

/-- **Bounded inverse theorem** (Theorem 2.4.3). A bounded linear bijection between Banach spaces
has a bounded inverse; equivalently, it is a continuous linear equivalence. -/
theorem theorem_2_4_3 [CompleteSpace V] [CompleteSpace W] (L : V →L[𝕜] W)
    (hL : Function.Bijective L) : ∃ e : V ≃L[𝕜] W, (e : V →L[𝕜] W) = L := by
  refine ⟨ContinuousLinearEquiv.ofBijective L ?_ ?_, ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
  · exact LinearMap.ker_eq_bot.2 hL.1
  · exact LinearMap.range_eq_top.2 hL.2

/-- Stability of a well-posed linear problem (the remark after Theorem 2.4.3): the solution of
`L v = w` depends Lipschitz-continuously on the data, with constant `‖L⁻¹‖`. -/
theorem stability_of_isomorphism (L : V ≃L[𝕜] W) (v vhat : V) :
    ‖v - vhat‖ ≤ ‖(L.symm : W →L[𝕜] V)‖ * ‖L v - L vhat‖ := by
  have hv : (L.symm : W →L[𝕜] V) (L v - L vhat) = v - vhat := by simp
  calc ‖v - vhat‖ = ‖(L.symm : W →L[𝕜] V) (L v - L vhat)‖ := by rw [hv]
    _ ≤ ‖(L.symm : W →L[𝕜] V)‖ * ‖L v - L vhat‖ := (L.symm : W →L[𝕜] V).le_opNorm _

/-! ### The condition number (2.4.1) -/

/-- The **condition number** `cond(L) = ‖L⁻¹‖ ‖L‖` of a bijection `L : V → W` with bounded
inverse (Atkinson–Han §2.4.2). -/
noncomputable def cond (L : V ≃L[𝕜] W) : ℝ :=
  ‖(L.symm : W →L[𝕜] V)‖ * ‖(L : V →L[𝕜] W)‖

/-- For an operator of a space into itself the book's `cond` is the backbone's
`NormedRing.condNumber` of the underlying element of the ring `V →L[𝕜] V`. -/
theorem cond_eq_condNumber (L : V ≃L[𝕜] V) :
    cond L = NormedRing.condNumber (L : V →L[𝕜] V) := by
  rw [cond, ContinuousLinearEquiv.condNumber_eq, mul_comm]

/-- `cond(L) ≥ 1`, because `L⁻¹L = I` has norm `1` (Atkinson–Han §2.4.2). -/
theorem one_le_cond [Nontrivial V] (L : V ≃L[𝕜] W) : 1 ≤ cond L := by
  rw [cond, mul_comm]
  exact L.one_le_norm_mul_norm_symm

/-- **Relative error bound (2.4.1).** The relative error in the solution is bounded by `cond(L)`
times the relative error in the data: with `w = L v` and `ŵ = L v̂`,
`‖v - v̂‖ / ‖v‖ ≤ cond(L) ‖w - ŵ‖ / ‖w‖`. -/
theorem equation_2_4_1 (L : V ≃L[𝕜] W) {v vhat : V} (hv : v ≠ 0) :
    ‖v - vhat‖ / ‖v‖ ≤ cond L * (‖L v - L vhat‖ / ‖L v‖) := by
  have ha : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hb : 0 < ‖L v‖ := norm_pos_iff.2 fun h => hv (by simpa using congrArg L.symm h)
  have hd : ‖v - vhat‖ ≤ ‖(L.symm : W →L[𝕜] V)‖ * ‖L v - L vhat‖ :=
    stability_of_isomorphism L v vhat
  have hq : ‖L v‖ ≤ ‖(L : V →L[𝕜] W)‖ * ‖v‖ := (L : V →L[𝕜] W).le_opNorm v
  rw [cond, mul_div_assoc', div_le_div_iff₀ ha hb]
  have hp : 0 ≤ ‖(L.symm : W →L[𝕜] V)‖ := norm_nonneg _
  have hr : 0 ≤ ‖L v - L vhat‖ := norm_nonneg _
  nlinarith [mul_nonneg hp hr]

/-! ### Theorems 2.4.4 and 2.4.5: uniform boundedness -/

/-- **Principle of uniform boundedness** (Theorem 2.4.4). A family of bounded operators from a
Banach space that is pointwise bounded is uniformly bounded in norm. -/
theorem theorem_2_4_4 [CompleteSpace V] (Ln : ℕ → V →L[𝕜] W) (h : ∀ v, ∃ C, ∀ n, ‖Ln n v‖ ≤ C) :
    ∃ C, ∀ n, ‖Ln n‖ ≤ C :=
  banach_steinhaus h

/-- The `⇐` half of Theorem 2.4.5, in the generality in which it is proved: pointwise convergence
on a dense *subset*, together with a uniform bound on the operator norms, gives pointwise
convergence everywhere. Neither completeness of `V` nor linearity of the dense set is used; only
the boundedness of the limit operator `L`, which the book also assumes. This is the ε/3 argument,
and it is the backbone's `ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded`
(`Numlib/Analysis/Normed/Operator/BanachSteinhaus.lean`), which states it along an arbitrary
filter on an arbitrary index type. -/
theorem tendsto_of_tendsto_on_dense_of_bounded {s : Set V} (hs : Dense s) {L : V →L[𝕜] W}
    {Ln : ℕ → V →L[𝕜] W} {C : ℝ} (hC : ∀ n, ‖Ln n‖ ≤ C)
    (h : ∀ v ∈ s, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) (v : V) :
    Tendsto (fun n => Ln n v) atTop (𝓝 (L v)) :=
  ContinuousLinearMap.tendsto_of_tendsto_on_dense_of_bounded hs hC h v

/-- **Banach–Steinhaus theorem** (Theorem 2.4.5). For bounded operators `L, Lₙ` from a Banach
space `V` and a dense subspace `V₀ ⊆ V`, one has `Lₙ v → L v` for every `v ∈ V` if and only if
(a) `Lₙ v → L v` for every `v ∈ V₀` and (b) the norms `‖Lₙ‖` are uniformly bounded.

The book's `V₀` is a subspace; the backbone's
`ContinuousLinearMap.tendsto_iff_tendsto_on_dense_of_completeSpace` needs only a dense set. -/
theorem theorem_2_4_5 [CompleteSpace V] (L : V →L[𝕜] W) (Ln : ℕ → V →L[𝕜] W) (V₀ : Submodule 𝕜 V)
    (hV₀ : Dense (V₀ : Set V)) :
    (∀ v, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) ↔
      (∀ v ∈ V₀, Tendsto (fun n => Ln n v) atTop (𝓝 (L v))) ∧ ∃ C, ∀ n, ‖Ln n‖ ≤ C :=
  ContinuousLinearMap.tendsto_iff_tendsto_on_dense_of_completeSpace hV₀ L Ln

/-! ### §2.4.4: convergence of numerical quadrature

The book studies the quadrature functionals `Lₙ v = ∑_{i=0}^{n} wᵢ⁽ⁿ⁾ v(xᵢ⁽ⁿ⁾)` on `C[0,1]`,
approximating `L v = ∫₀¹ w v`. Both results are the backbone's, specialized to `[0, 1]`; the
quadrature functional is `Quadrature.functional` of `Numlib/Approximation/Quadrature`. -/

/-- **(2.4.4)** (Exercise 2.4.2). The norm of the quadrature functional
`Lₙ v = ∑ᵢ wᵢ v(xᵢ)` on `C[0, 1]` is the absolute sum of its weights, provided the nodes are
distinct. -/
theorem equation_2_4_4 {n : ℕ} (w : Fin n → ℝ) {x : Fin n → Set.Icc (0 : ℝ) 1}
    (hx : Function.Injective x) : ‖Quadrature.functional w x‖ = ∑ i, |w i| :=
  Quadrature.norm_functional w hx

/-- **§2.4.4** and **Exercise 2.4.3**, the convergence of numerical quadrature. Let the rules
`Lₖ v = ∑ᵢ wᵢ⁽ᵏ⁾ v(xᵢ⁽ᵏ⁾)` at distinct nodes of `[0, 1]` be exact for `L` on the polynomials of
degree at most `d k`, with `d k → ∞`. Then `Lₖ v → L v` for every `v ∈ C[0, 1]` if and only if the
absolute sums of the weights are bounded; and if the weights are nonnegative, convergence always
holds. -/
theorem quadrature_convergence {m d : ℕ → ℕ} {w : ∀ k, Fin (m k) → ℝ}
    {x : ∀ k, Fin (m k) → Set.Icc (0 : ℝ) 1} (hx : ∀ k, Function.Injective (x k))
    {L : C(Set.Icc (0 : ℝ) 1, ℝ) →L[ℝ] ℝ} (hd : Tendsto d atTop atTop)
    (hexact : ∀ k, Quadrature.IsExactOn L (w k) (x k) (d k)) :
    ((∀ v, Tendsto (fun k => Quadrature.functional (w k) (x k) v) atTop (𝓝 (L v))) ↔
        ∃ C, ∀ k, ∑ i, |w k i| ≤ C) ∧
      ((∀ k i, 0 ≤ w k i) →
        ∀ v, Tendsto (fun k => Quadrature.functional (w k) (x k) v) atTop (𝓝 (L v))) :=
  ⟨Quadrature.tendsto_iff_bddAbove_sum_abs hx hd hexact,
    fun hw => Quadrature.tendsto_of_nonneg hx hd hexact hw⟩

/-! ### Example 2.4.2: the differentiation operator on `C¹[0, 1]` and its extension -/

section Example242

open MeasureTheory Set

-- TODO(backbone): a general fact about `H^1(a, b)`; natural home
-- `Numlib/Analysis/Sobolev/Interval.lean`, beside `SobolevInterval.norm_sq_eq`.
/-- `‖u‖_{H^1} ≤ ‖u‖_{L²} + ‖u'‖_{L²}`, from `‖u‖² = ‖u‖_{L²}² + ‖u'‖_{L²}²`. -/
theorem sobolevInterval_norm_le_add {a b : ℝ} (u : SobolevInterval 1 a b) :
    ‖u‖ ≤ ‖SobolevInterval.deriv u 0‖ + ‖SobolevInterval.deriv u 1‖ := by
  have h := SobolevInterval.norm_sq_eq u
  rw [Fin.sum_univ_two] at h
  rw [← pow_le_pow_iff_left₀ (norm_nonneg u) (by positivity) two_ne_zero, h]
  nlinarith [mul_nonneg (norm_nonneg (SobolevInterval.deriv u 0))
    (norm_nonneg (SobolevInterval.deriv u 1))]

-- TODO(backbone): a general fact about `H^1(a, b)`; natural home
-- `Numlib/Analysis/Sobolev/Interval.lean`, beside `ContDiffMapIcc.toSobolevInterval`, whose doc
-- comment records that density is not proved there.
/-- **`C¹[a, b]` is dense in `H^1(a, b)`.** Given `u ∈ H^1(a, b)`, approximate its weak derivative
`u'` in `L²(a, b)` by a test function `ψ` (`exists_testFunction_norm_sub_toLp_le`) and take
`v = u(a) + ∫_a^x ψ`, which is `C^∞` on `[a, b]`. Then `v - u = ∫_a^x (ψ - u')` vanishes at `a`,
so Poincaré's inequality `SobolevInterval.norm_le_of_eq_integral` bounds `‖v - u‖_{L²}` by
`((b - a)/√2) ‖ψ - u'‖_{L²}`, and `‖v - u‖_{H^1} ≤ (1 + (b - a)/√2) ‖ψ - u'‖_{L²}`. No
mollification of `u` itself is needed. -/
theorem denseRange_toSobolevInterval_one {a b : ℝ} (hab : a < b) :
    DenseRange (ContDiffMapIcc.toSobolevInterval hab.le hab 1) := by
  rw [Metric.denseRange_iff]
  intro u ε hε
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab.le
  set w : Lp ℝ 2 (volume.restrict (Ioo a b)) := SobolevInterval.deriv u 1 with hwdef
  set K : ℝ := 1 + (b - a) / Real.sqrt 2 with hKdef
  have hK0 : 0 < K := by
    have : (0 : ℝ) ≤ (b - a) / Real.sqrt 2 := by positivity
    linarith
  obtain ⟨ψ, hψ⟩ := exists_testFunction_norm_sub_toLp_le hab w (ε := ε / (2 * K)) (by positivity)
  set ψC : C(Icc a b, ℝ) := ⟨fun t => ψ t, ψ.continuous.comp continuous_subtype_val⟩ with hψC
  set p : Fin 2 → C(Icc a b, ℝ) :=
    ![ContinuousMap.antideriv hab.le ψC (SobolevInterval.repConst u), ψC] with hp
  have hderiv : ∀ j : Fin 1, ContinuousMap.HasDerivIcc hab.le (p j.castSucc) (p j.succ) := by
    intro j
    fin_cases j
    exact ContinuousMap.hasDerivIcc_antideriv hab.le ψC _
  set v : ContDiffMapIcc hab.le 1 := ContDiffMapIcc.mk hab.le p hderiv with hv
  refine ⟨v, ?_⟩
  set d : SobolevInterval 1 a b := ContDiffMapIcc.toSobolevInterval hab.le hab 1 v - u with hd
  have hIcc : ∀ x ∈ Icc a b, IccExtend hab.le ψC x = ψ x := fun x hx => by
    rw [IccExtend_of_mem hab.le _ hx]; rfl
  have hmid : (IccExtend hab.le (v.deriv 1) : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo a b)] (ψ : ℝ → ℝ) :=
    (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => by
      have hv1 : v.deriv 1 = ψC := rfl
      rw [hv1]
      exact hIcc x (Ioo_subset_Icc_self hx))
  have h1 : SobolevInterval.deriv d 1 = ψ.toLp₂ - w := by
    rw [hd, SobolevInterval.deriv_sub]
    congr 1
    exact Lp.ext (((ContDiffMapIcc.coeFn_derivLp v 1).trans hmid).trans ψ.coeFn_toLp₂.symm)
  have hWae : ((ψ.toLp₂ - w : Lp ℝ 2 (volume.restrict (Ioo a b))) : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo a b)] fun t => (ψ : ℝ → ℝ) t - w t := by
    filter_upwards [Lp.coeFn_sub ψ.toLp₂ w, ψ.coeFn_toLp₂] with t ht1 ht2
    rw [ht1, Pi.sub_apply, ht2]
  have hv0 : (IccExtend hab.le (v.deriv 0) : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo a b)]
      fun x => SobolevInterval.repConst u + ∫ s in a..x, (ψ : ℝ → ℝ) s := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
    have hxI : x ∈ Icc a b := Ioo_subset_Icc_self hx
    have hv0' : v.deriv 0 = ContinuousMap.antideriv hab.le ψC (SobolevInterval.repConst u) := rfl
    rw [hv0', IccExtend_of_mem hab.le _ hxI, ContinuousMap.antideriv_apply]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hx.1.le] at hs
    exact hIcc s ⟨hs.1, hs.2.trans hxI.2⟩
  have hu0 : (SobolevInterval.deriv u 0 : ℝ → ℝ) =ᵐ[volume.restrict (Ioo a b)]
      fun x => SobolevInterval.repConst u + ∫ t in a..x, w t :=
    SobolevInterval.fn_ae_eq_rep hab u
  have h0 : ((SobolevInterval.deriv d 0 : Lp ℝ 2 (volume.restrict (Ioo a b))) : ℝ → ℝ)
      =ᵐ[volume.restrict (Ioo a b)]
      fun x => ∫ t in a..x, ((ψ.toLp₂ - w : Lp ℝ 2 (volume.restrict (Ioo a b))) : ℝ → ℝ) t := by
    have hsub : SobolevInterval.deriv d 0 = v.derivLp 0 - SobolevInterval.deriv u 0 := by
      rw [hd, SobolevInterval.deriv_sub]; rfl
    rw [hsub]
    filter_upwards [Lp.coeFn_sub (v.derivLp 0) (SobolevInterval.deriv u 0),
      ContDiffMapIcc.coeFn_derivLp v 0, hv0, hu0, ae_restrict_mem measurableSet_Ioo] with
      x hxs hx1 hx2 hx3 hxI
    have hxIcc : x ∈ Icc a b := Ioo_subset_Icc_self hxI
    rw [hxs, Pi.sub_apply, hx1, hx2, hx3, intervalIntegral_congr_ae_Ioo hWae hxIcc,
      intervalIntegral.integral_sub (ψ.continuous.intervalIntegrable _ _)
        ((SobolevInterval.integrableOn_deriv u 1).intervalIntegrable_of_Ioo
          (left_mem_Icc.2 hab.le) hxIcc)]
    ring
  have hb0 : ‖SobolevInterval.deriv d 0‖ ≤ (b - a) / Real.sqrt 2 * (ε / (2 * K)) := by
    refine (SobolevInterval.norm_le_of_eq_integral hab.le h0).trans ?_
    gcongr
    rw [norm_sub_rev]; exact hψ
  have hb1 : ‖SobolevInterval.deriv d 1‖ ≤ ε / (2 * K) := by
    rw [h1, norm_sub_rev]; exact hψ
  have hfin : (b - a) / Real.sqrt 2 * (ε / (2 * K)) + ε / (2 * K) = ε / 2 := by
    rw [hKdef]
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    ring
  calc dist u (ContDiffMapIcc.toSobolevInterval hab.le hab 1 v) = ‖d‖ := by
        rw [hd, dist_eq_norm']
    _ ≤ ‖SobolevInterval.deriv d 0‖ + ‖SobolevInterval.deriv d 1‖ := sobolevInterval_norm_le_add d
    _ ≤ (b - a) / Real.sqrt 2 * (ε / (2 * K)) + ε / (2 * K) := by gcongr
    _ = ε / 2 := hfin
    _ < ε := by linarith

/-- **Example 2.4.2**, the bound `‖D v‖₂ ≤ ‖v‖_{1,2}` on `C¹[0, 1]`: the `L²` norm of the
derivative of `v` is at most the `H¹` norm of `v`, so the differentiation operator
`D : C¹[0, 1] → L²(0, 1)` has `‖D‖_{V,W} ≤ 1` for the norm `‖·‖_{1,2}` of the book. -/
theorem example_2_4_2_norm_le (v : ContDiffMapIcc (zero_le_one : (0 : ℝ) ≤ 1) 1) :
    ‖v.derivLp 1‖ ≤
      ‖ContDiffMapIcc.toSobolevInterval (zero_le_one : (0 : ℝ) ≤ 1) zero_lt_one 1 v‖ := by
  rw [← ContDiffMapIcc.deriv_toSobolevInterval (zero_le_one : (0 : ℝ) ≤ 1) zero_lt_one v 1]
  exact SobolevInterval.norm_deriv_le _ 1

/-- **Example 2.4.2**, the completion: `C¹[0, 1]` with the norm `‖·‖_{1,2}` is dense in
`H¹(0, 1)`, which is complete, so `H¹(0, 1)` is the completion of `C¹[0, 1]` in that norm. The
inclusion is injective (`ContDiffMapIcc.toSobolevInterval_injective`). -/
theorem example_2_4_2_dense :
    DenseRange (ContDiffMapIcc.toSobolevInterval (zero_le_one : (0 : ℝ) ≤ 1) zero_lt_one 1) :=
  denseRange_toSobolevInterval_one zero_lt_one

/-- **Example 2.4.2**: the differentiation operator `D v = v'` of `C¹[0, 1]` into `L²(0, 1)`
extends uniquely to a bounded operator `D̂ ∈ 𝓛(H¹(0, 1), L²(0, 1))`, the extension supplied by
Theorem 2.4.1 once `H¹(0, 1)` is identified with the completion of `C¹[0, 1]`
(`example_2_4_2_dense`). The extension is the weak derivative `SobolevInterval.derivL`, the
"more concrete realization" the book promises for Chapter 7, and `‖D̂‖ ≤ 1`
(`example_2_4_2_opNorm_le`). -/
theorem example_2_4_2 :
    ∃! D : SobolevInterval 1 0 1 →L[ℝ] Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)),
      ∀ v : ContDiffMapIcc (zero_le_one : (0 : ℝ) ≤ 1) 1,
        D (ContDiffMapIcc.toSobolevInterval (zero_le_one : (0 : ℝ) ≤ 1) zero_lt_one 1 v) =
          v.derivLp 1 := by
  refine ⟨SobolevInterval.derivL 1 0 1 1, fun v => rfl, fun D hD => ?_⟩
  refine ContinuousLinearMap.coe_injective (DFunLike.coe_injective ?_)
  exact example_2_4_2_dense.equalizer D.continuous
    (SobolevInterval.derivL 1 0 1 1).continuous (funext fun v => hD v)

/-- **Example 2.4.2**: the extension has `‖D̂‖ ≤ 1`, as Theorem 2.4.1 and
`example_2_4_2_norm_le` give. -/
theorem example_2_4_2_opNorm_le : ‖SobolevInterval.derivL 1 (0 : ℝ) 1 1‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Example242

end AtkinsonHan.Chapter02
