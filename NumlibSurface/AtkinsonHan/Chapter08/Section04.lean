/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.AtkinsonHan.Chapter07.Section03

/-!
# Atkinson and Han, Section 8.4: Weak formulations of linear elliptic boundary value problems

This module formalizes the one numbered result of Section 8.4 of [han2009theoretical], Lemma 8.4.1.
Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded connected domain, and let
$V = H^1(\Omega)/\mathbb{R}$ be the quotient of $H^1(\Omega)$ by the constant functions, with the
quotient norm $\|[v]\|_V = \inf_{\alpha \in \mathbb{R}} \|v + \alpha\|_1$. The lemma states that
this norm is equivalent to the seminorm $|v|_1 = \|\nabla v\|_{L^2(\Omega)}$. This makes the
bilinear form $\bar a([u], [v]) = \int_\Omega \nabla u \cdot \nabla v \, dx$ of the pure Neumann
problem (8.4.10) elliptic on $V$.

The source calls the lemma a special case of Theorem 7.3.17. Here it is proved from the Deny–Lions
norm equivalence `AtkinsonHan.Chapter07.theorem_7_3_12` with $k = 1$, $p = 2$ and the one seminorm
$f_1(v) = |\int_\Omega v \, dx|$. The supporting results below show that the constant function $1$
is in $H^1(\Omega)$, that $|\cdot|_1$ does not see constants, that $v \mapsto \int_\Omega v \, dx$
is a bounded linear functional, and that $f_1$ satisfies the hypotheses of Theorem 7.3.12.

## Main results

* Lemma 8.4.1, `AtkinsonHan.Chapter08.lemma_8_4_1`: on a connected bounded extension domain, $c_1
  |v|_1 \le \inf_{\alpha \in \mathbb{R}} \|v + \alpha\|_1 \le c_2 |v|_1$ for all
  $v \in H^1(\Omega)$.

## Proof outline

For $v \in H^1(\Omega)$ take $\alpha = -(\int_\Omega v \, dx)/|\Omega|$. Then $f_1(v + \alpha) = 0$,
and the Deny–Lions inequality gives $\inf_\beta \|v + \beta\|_1 \le \|v + \alpha\|_1 \le c\,|v +
\alpha|_1 = c\,|v|_1$. The lower bound holds with $c_1 = 1$, because
$|v|_1 = |v + \beta|_1 \le \|v + \beta\|_1$ for every $\beta$.

## Notation

* `𝟚`: the exponent $p = 2$, written `((2 : ℝ≥0) : ℝ≥0∞)` as the backbone's Rellich–Kondrachov
  theorem requires.

## Implementation notes

* $H^1(\Omega)$ is `SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume`, the space of Definition
  7.2.2 in the multi-index form. The seminorm $|v|_1$ is `SobolevMultiIndex.topSeminorm`.
* The constant function $1$ is any element `one` of $H^1(\Omega)$ whose function is $1$ almost
  everywhere on $\Omega$. `AtkinsonHan.Chapter08.exists_fn_ae_eq_one` gives one. The class $[v]$ is
  not formed: the quotient norm is the infimum $\inf_\alpha \|v + \alpha \cdot 1\|$ over the
  representatives.

## Deviations from the source

* **Lemma 8.4.1** (generalization). The source assumes a Lipschitz domain. The lemma here assumes a
  connected bounded $W^{1,2}$-extension domain, which includes the $C^1$ domains of Definition
  7.2.1. See `AtkinsonHan.Chapter08.lemma_8_4_1`.

## Not formalized

* **The weak formulations (8.4.1)–(8.4.22)** of the homogeneous and non-homogeneous Dirichlet
  problems, the Neumann and pure Neumann problems, the mixed problem and the general second-order
  problem. They are stated with the trace $\gamma : H^1(\Omega) \to H^{1/2}(\Gamma)$ of Theorem
  7.3.10. Their abstract content is the Lax–Milgram lemma `AtkinsonHan.Chapter08.theorem_8_3_4`.
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped ContDiff ENNReal NNReal Topology

namespace AtkinsonHan.Chapter08

open AtkinsonHan.Chapter07 SobolevMultiIndex

/-- The exponent $p = 2$ as the element `((2 : ℝ≥0) : ℝ≥0∞)`, in the form that the backbone's
Rellich–Kondrachov theorem in `Numlib.Analysis.Sobolev.Compactness` takes, since it has
`p : ℝ≥0`. The space `SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume` is by definition the
space $H^1(\Omega)$ of `AtkinsonHan.Chapter07.corollary_7_2_4`, and the instance `Fact (1 ≤ 𝟚)`
is `fact_one_le_coe_two_ennreal`. -/
local notation "𝟚" => ((2 : ℝ≥0) : ℝ≥0∞)

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set. Then the constant function $1$ is
in $H^1(\Omega)$: there is an element $\mathbb{1} \in H^1(\Omega)$ whose function is equal to
$1$ almost everywhere on $\Omega$.

The element is the restriction to $\Omega$ of a smooth function with compact support that is
equal to $1$ on the closure of $\Omega$. -/
theorem exists_fn_ae_eq_one
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ one : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
      fn one =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] 1 := by
  obtain ⟨R, -, hR⟩ := hb.subset_ball_lt 0 0
  have hcl : closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ Metric.closedBall 0 R :=
    closure_minimal (hR.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall
  obtain ⟨φ, hφ, hφ1, hφs, -⟩ := hb.isCompact_closure.exists_contDiff_eqOn_one
    (Metric.isOpen_ball (x := (0 : EuclideanSpace ℝ (Fin (d + 1)))) (ε := R + 1))
    (hcl.trans (Metric.closedBall_subset_ball (by linarith)))
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) (R + 1))
      ((subset_tsupport φ).trans (hφs.trans Metric.ball_subset_closedBall))
  obtain ⟨one, hone⟩ := hφ.exists_sobolevMultiIndex_of_hasCompactSupport
    (b := stdBasis (d + 1)) (k := 1) (p := 𝟚) (Ω := Ω) (μ := volume) hφc
  refine ⟨one, hone.trans ?_⟩
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact hφ1 (subset_closure hx)

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open, and let $\mathbb{1} \in H^1(\Omega)$ have the
function $1$ almost everywhere on $\Omega$. Then all first weak derivatives of $\mathbb{1}$ are
zero, so $|\mathbb{1}|_1 = 0$. -/
theorem topSeminorm_eq_zero_of_fn_ae_eq_one
    {one : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume}
    (hone : fn one =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] 1) :
    topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume one = 0 := by
  rw [topSeminorm_eq_zero_iff]
  intro α
  rcases MultiIndexLE.eq_zero_or_exists_eq_single α.1 with h0 | ⟨i, hi⟩
  · have := α.2
    rw [h0] at this
    simp at this
  · rw [hi]
    -- the constant `1` has weak derivative `0` along every direction
    have h1 : HasWeakIteratedLineDerivOn ![stdBasis (d + 1) i] (fn one)
        (weakDeriv one (MultiIndexLE.singleLE i)) Ω volume :=
      hasWeakIteratedLineDerivOn_single (k := 0) one i
    have h2 : HasWeakIteratedLineDerivOn ![stdBasis (d + 1) i] (fn one) (fun _ ↦ (0 : ℝ))
        Ω volume := by
      have h := ((contDiff_const (c := (1 : ℝ))).hasWeakFDerivOn (Ω := Ω)
        (μ := volume)).lineDeriv ![stdBasis (d + 1) i]
      refine h.congr_ae hone.symm (Eventually.of_forall fun x ↦ ?_)
      simp
    exact Lp.ext (Filter.EventuallyEq.trans
      ((ae_restrict_iff' Ω.isOpen.measurableSet).2 (h1.ae_eq h2)) (Lp.coeFn_zero ℝ 𝟚 _).symm)

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open, and let $\mathbb{1} \in H^1(\Omega)$ have the
function $1$ almost everywhere on $\Omega$. Then the seminorm $|\cdot|_1$ does not see
constants: for all $v \in H^1(\Omega)$ and $\alpha \in \mathbb{R}$,
$$|v + \alpha \mathbb{1}|_1 = |v|_1.$$
-/
theorem topSeminorm_add_smul_one
    {one : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume}
    (hone : fn one =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] 1)
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume) (α : ℝ) :
    topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume (v + α • one)
      = topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v :=
  (topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume).apply_add_smul_of_eq_zero
    (topSeminorm_eq_zero_of_fn_ae_eq_one hone) v α

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set. Then the integral
$v \mapsto \int_\Omega v \, dx$ is a bounded linear functional on $H^1(\Omega)$: there is
$\ell \in H^1(\Omega)'$ with $\ell(v) = \int_\Omega v \, dx$ for all $v$.

The proof uses $L^2(\Omega) \subseteq L^1(\Omega)$ on a set of finite measure, and then the
Bochner integral. -/
theorem exists_integralCLM (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ ℓ : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume →L[ℝ] ℝ,
      ∀ v, ℓ v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), fn v x := by
  have hfin : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    isFiniteMeasure_restrict.2 (hb.measure_lt_top (μ := volume)).ne
  obtain ⟨M, hM⟩ : ∃ M : Lp ℝ 𝟚 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) →L[ℝ]
      Lp ℝ 1 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      ∀ g, (M g : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] g :=
    ⟨Lp.monoExponentL ℝ _ 𝟚 1 (by norm_num), fun g ↦ Lp.coeFn_monoExponentL (by norm_num) g⟩
  refine ⟨(L1.integralCLM (μ := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (E := ℝ)).comp (M.comp (fnL ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume)), fun v ↦ ?_⟩
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← L1.integral_eq,
    L1.integral_eq_integral]
  refine integral_congr_ae ((hM _).trans ?_)
  exact Eventually.of_forall fun x ↦ by rw [fnL_apply]

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a nonempty bounded open set. If $v \in H^1(\Omega)$
is equal almost everywhere on $\Omega$ to a constant polynomial and $\int_\Omega v \, dx = 0$,
then $v = 0$.

This is hypothesis (H2) of `AtkinsonHan.Chapter07.theorem_7_3_12` with $k = 1$ for the seminorm
$f_1(v) = |\int_\Omega v \, dx|$. A constant polynomial is an element of
`MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ 0`. -/
theorem eq_zero_of_integral_eq_zero
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
    (v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume)
    (hv : ∃ q ∈ MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ 0, fn v
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ MvPolynomial.eval (fun i ↦ x i) q)
    (hint : ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), fn v x = 0) : v = 0 := by
  have hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤ :=
    (hb.measure_lt_top (μ := volume)).ne
  have hvol : 0 < volume.real (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    ENNReal.toReal_pos (Ω.isOpen.measure_pos volume hne).ne' hμ
  obtain ⟨q, hq, hvq⟩ := hv
  rw [MvPolynomial.mem_restrictTotalDegree, Nat.le_zero,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hq
  have hvc : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun _ ↦ q.coeff 0 := by
    refine hvq.trans (Eventually.of_forall fun x ↦ ?_)
    change MvPolynomial.eval (fun i ↦ x i) q = q.coeff 0
    conv_lhs => rw [hq]
    rw [MvPolynomial.eval_C]
  rw [integral_congr_ae hvc, setIntegral_const, smul_eq_mul] at hint
  have hzero : q.coeff 0 = 0 := (mul_eq_zero.1 hint).resolve_left hvol.ne'
  refine ext_of_fn_ae_eq (hvc.trans ?_)
  rw [hzero]
  exact fn_zero.symm

/-- The Deny–Lions inequality with the seminorm $|\int_\Omega v \, dx|$. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a nonempty, bounded and connected $W^{1,2}$-extension
domain, and let $\ell \in H^1(\Omega)'$ satisfy $\ell(v) = \int_\Omega v \, dx$ for all $v$.
Then there is $C > 0$ such that for all $v \in H^1(\Omega)$,
$$\|v\|_1 \le C \left( |v|_1 + |\ell(v)| \right).$$

This is `AtkinsonHan.Chapter07.theorem_7_3_12` with $k = 1$, $p = 2$ and the one seminorm
$f_1(v) = |\ell(v)|$. Connectedness is the hypothesis `IsPreconnected`. -/
theorem exists_norm_le_topSeminorm_add_abs_integral (hΩ : IsSobolevExtensionDomain (d + 1) 𝟚 Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
    {ℓ : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume →L[ℝ] ℝ}
    (hℓ : ∀ v, ℓ v = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), fn v x) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
      ‖v‖ ≤ C * (topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v + |ℓ v|) := by
  have hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤ :=
    (hb.measure_lt_top (μ := volume)).ne
  have h2 : ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
      (∃ q ∈ MvPolynomial.restrictTotalDegree (Fin (d + 1)) ℝ 0, fn v
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
          fun x ↦ MvPolynomial.eval (fun i ↦ x i) q) → ℓ v = 0 → v = 0 := fun v hv h0 ↦
    eq_zero_of_integral_eq_zero hb hne v hv ((hℓ v).symm.trans h0)
  have h := SobolevEuclidean.exists_norm_le_topSeminorm_add_abs_of_isPreconnected
    (N := d + 1) (k := 0) (p := 2) hΩ hμ hc ℓ h2
  exact h

/-- **Lemma 8.4.1** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a nonempty,
bounded and connected $W^{1,2}$-extension domain, and let $\mathbb{1} \in H^1(\Omega)$ have the
function $1$ almost everywhere on $\Omega$. Then the quotient norm $\|[v]\|_V = \inf_{\alpha \in
\mathbb{R}} \|v + \alpha \mathbb{1}\|_1$ of $V = H^1(\Omega)/\mathbb{R}$ is equivalent to the
seminorm $|v|_1$: there are $c_1, c_2 > 0$ such that for all $v \in H^1(\Omega)$,
$$c_1 |v|_1 \le \inf_{\alpha \in \mathbb{R}} \|v + \alpha \mathbb{1}\|_1 \le c_2 |v|_1.$$

**Generalization.** The source assumes a Lipschitz domain. The lemma here assumes that $\Omega$
is a $W^{1,2}$-extension domain (`IsSobolevExtensionDomain`). The $C^1$ domains of Definition
7.2.1 are extension domains by
`AtkinsonHan.Chapter07.isSobolevExtensionDomainAll_of_definition_7_2_1`. A Lipschitz domain is
one by the extension theorems of Stein or Calderón, which are not formalized.

The source calls the lemma a special case of Theorem 7.3.17. The proof here applies the
Deny–Lions equivalence `AtkinsonHan.Chapter07.theorem_7_3_12` in the form
`AtkinsonHan.Chapter08.exists_norm_le_topSeminorm_add_abs_integral` to the representative
$v + \alpha \mathbb{1}$ with $\alpha = -(\int_\Omega v \, dx)/|\Omega|$, where the integral
vanishes (`Seminorm.ciInf_norm_add_smul_le_mul`). The lower bound holds with $c_1 = 1$, because
$|\mathbb{1}|_1 = 0$ gives $|v|_1 \le \|v + \alpha \mathbb{1}\|_1$ for every $\alpha$
(`Seminorm.le_ciInf_norm_add_smul`). $H^1(\Omega)$ is the space of Definition 7.2.2, and $|v|_1$
is its top-order seminorm `SobolevMultiIndex.topSeminorm`, the norm $\|\nabla v\|_{L^2(\Omega)}$
of the gradient. -/
theorem lemma_8_4_1 (hΩ : IsSobolevExtensionDomain (d + 1) 𝟚 Ω)
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : IsPreconnected (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hne : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).Nonempty)
    {one : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume}
    (hone : fn one =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] 1) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ v : SobolevMultiIndex ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume,
      c₁ * topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v ≤ ⨅ α : ℝ, ‖v + α • one‖ ∧
      ⨅ α : ℝ, ‖v + α • one‖ ≤ c₂ * topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume v := by
  have hμ : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤ :=
    (hb.measure_lt_top (μ := volume)).ne
  have hvol : 0 < volume.real (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) :=
    ENNReal.toReal_pos (Ω.isOpen.measure_pos volume hne).ne' hμ
  have h := exists_integralCLM hb
  obtain ⟨ℓ, hℓ⟩ := h
  have hℓone : ℓ one ≠ 0 :=
    ((hℓ one).trans ((integral_congr_ae hone).trans (by simp))).trans_ne hvol.ne'
  have h' := exists_norm_le_topSeminorm_add_abs_integral hΩ hb hc hne hℓ
  obtain ⟨C, hC, hle⟩ := h'
  have h0 := topSeminorm_eq_zero_of_fn_ae_eq_one hone
  refine ⟨1, C, one_pos, hC, fun v ↦ ⟨?_, ?_⟩⟩
  · exact (one_mul _).trans_le (Seminorm.le_ciInf_norm_add_smul
      (topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume) topSeminorm_le_norm h0 v)
  · exact Seminorm.ciInf_norm_add_smul_le_mul (topSeminorm ℝ (stdBasis (d + 1)) 1 𝟚 Ω volume)
      ℓ h0 hℓone hle v

end AtkinsonHan.Chapter08
