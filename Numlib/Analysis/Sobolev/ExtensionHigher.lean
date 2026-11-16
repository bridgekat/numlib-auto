/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Extension.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Vandermonde
import Numlib.Analysis.Calculus.ContDiffConstOffCompact
import Numlib.Analysis.Sobolev.Compactness
import Numlib.Analysis.Sobolev.DenyLions
import Numlib.Analysis.Sobolev.Extension

/-!
# The extension operator of every order on a $C^k$ domain

Let $\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^k$, $k \ge 1$, with bounded boundary,
and let $1 \le p \le \infty$. This module constructs a bounded linear extension operator
$P : W^{k,p}(\Omega) \to W^{k,p}(\mathbb{R}^N)$ with $Pu = u$ on $\Omega$, which is also bounded
from $L^p(\Omega)$ to $L^p(\mathbb{R}^N)$, and the operators of all exponents $p$ are given by one
map on functions. As a consequence, the restrictions to $\Omega$ of the functions of
$C_c^\infty(\mathbb{R}^N)$ are dense in $W^{k,p}(\Omega)$ for $p < \infty$. The case $k = 1$ is
Theorem 9.7 and Corollary 9.8 of [brezis2011functional], formalized in
`Numlib.Analysis.Sobolev.Extension`. The operator of higher order is the classical variant by
higher-order reflection ([brezis2011functional], §9.2, Lemma 9.2, and Comments on Chapter 9, 3;
Lions and Magenes; Evans, *Partial Differential Equations*, §5.4, remark after Theorem 1). The
results correspond to Theorems 7.3.2 and 7.3.5 of [han2009theoretical].

Write $x = (x', x_N)$ for a point of $\mathbb{R}^N$, $N = d + 1$, write
$S_\lambda(x', x_N) = (x', \lambda x_N)$, and let $Q_r = \{x : |x'| < r, |x_N| < r\}$ be the
cylinder of radius $r$, with upper half $Q_r^+ = Q_r \cap \{x_N > 0\}$. For coefficients
$a_1, \dots, a_m$ and distinct scales $\lambda_1, \dots, \lambda_m \in [-1, 0)$, the **higher-order
reflection** of a function $u$ on the upper half is $P_a u = u$ on $\{x_N \ge 0\}$ and
$$(P_a u)(x', x_N) = \sum_j a_j\, u(x', \lambda_j x_N) \qquad (x_N < 0).$$
If the $a_j$ solve the Vandermonde system $\sum_j a_j \lambda_j^i = 1$ for $i < k$, the one-sided
normal derivatives of order less than $k$ agree on the hyperplane $x_N = 0$, and $P_a$ maps
$W^{k,p}(Q_r^+)$ into $W^{k,p}(Q_r)$.

## Main definitions

* `higherReflection`: the higher-order reflection $P_a$ across the hyperplane $x_N = 0$.
* `SobolevMultiIndex.higherReflectionL`: $P_a$ as a bounded linear map
  $W^{1,p}(Q_r^+) \to W^{1,p}(Q_r)$, for $\sum_j a_j = 1$.
* `ContDiffChart.opensUr`: the image $U_r = H(Q_r)$ of the cylinder $Q_r$, $r < 1$, under a chart
  $H$.
* `SobolevEuclidean.chartExtendLr`: the chart-local extension $W^{1,p}(\Omega) \to W^{1,p}(U_r)$,
  $u \mapsto P_a(u \circ H) \circ H^{-1}$.
* `IsSobolevExtensionDomainOfOrder`: $\Omega$ has a bounded linear extension operator
  $W^{k,p}(\Omega) \to W^{k,p}(\mathbb{R}^N)$.

## Main results

* `hasWeakFDerivOn_indicator_lowerHalf_of_contDiff`: the gluing lemma; if $g \in C^1$ vanishes on
  $x_N = 0$, then $1_{\{x_N < 0\}} g$ has the weak derivative $1_{\{x_N < 0\}} \nabla g$.
* `hasWeakFDerivOn_higherReflection`: for $\sum_j a_j = 1$ and $w \in W^{1,p}(Q_r^+)$, the
  reflection $P_a w$ has the piecewise weak derivative on $Q_r$.
* `MemSobolev.higherReflection`: for $\sum_j a_j = 1$, $P_a$ maps $W^{1,p}(Q_r^+)$ into
  $W^{1,p}(Q_r)$.
* `HasWeakIteratedLineDerivOn.higherReflection_single`: a tangential derivative of $P_a u$ is $P_a$
  of the derivative, and the normal derivative is $P_{a\lambda}(\partial_N u)$ with the coefficients
  $a_j \lambda_j$.
* `MemSobolevMultiIndex.higherReflection_of_order`: under the Vandermonde conditions of order $k$,
  $P_a$ maps $W^{k,p}(Q_r^+)$ into $W^{k,p}(Q_r)$.
* `exists_vandermonde_coeffs`: for the scales $\lambda_j = -1/(j+1)$ the Vandermonde system of order
  $k$ has a solution.
* `SobolevEuclidean.chartExtendLr_mem_of_order`: for a chart of class $C^k$, the chart-local
  extension maps $W^{k,p}(\Omega)$ into $W^{k,p}(U_r)$.
* `SobolevEuclidean.extension_mem_of_ops`: the operator assembled from a partition of unity maps
  $W^{k,p}(\Omega)$ into $W^{k,p}(\mathbb{R}^N)$.
* `SobolevEuclidean.exists_extensionL_of_order_of_atlas`: the extension operator of order $k$ for an
  explicit atlas and partition of unity.
* `SobolevEuclidean.exists_extensionL_of_order_uniform`: the extension theorem of order $k$, with
  one map on functions for all exponents $p$.
* `SobolevEuclidean.exists_extensionL_of_order`: the extension theorem of order $k$ for one exponent
  $p$.
* `IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain`: an open set of class $C^k$ with
  bounded boundary is a $W^{k,p}$-extension domain.
* `SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_order`: on a
  $W^{k,p}$-extension domain, $p < \infty$, the restrictions of $C_c^\infty(\mathbb{R}^N)$ functions
  are dense in $W^{k,p}(\Omega)$.
* `SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_isContDiffChartDomain`: the
  same density on an open set of class $C^k$ with bounded boundary.

## Proof outline

At order one, $P_a w \in W^{1,p}$ cannot be proved as Lemma 9.2 of [brezis2011functional] proves it
for the even reflection, because the cancellation across the interface is lost. Instead, the even
reflection of $w$ is approximated near each compact piece of $Q_r$ by smooth functions $g_n$. For
smooth $g_n$ one has $P_a g_n = g_n + 1_{\{x_N < 0\}} G_n$ with $G_n = \sum_j a_j\, g_n \circ
S_{\lambda_j} - g_n$, which vanishes on the hyperplane because $\sum_j a_j = 1$, so the gluing lemma
gives the piecewise weak derivative, and the identity passes to the limit in $L^1$. Every order
follows by induction on $k$: the tangential derivatives of $P_a u$ are $P_a(\partial_i u)$ and the
normal one is $P_{a\lambda}(\partial_N u)$, and the coefficients $a_j \lambda_j$ satisfy the
Vandermonde conditions one order lower. The space $W^{k,p}$ is preserved by composition with a $C^k$
diffeomorphism (`MemSobolevMultiIndex.comp_diffeoOn_of_order`, by induction on $k$ with the chain
rule $\partial_i (w \circ J) = \sum_l (\partial_i J)_l\, (\partial_l w) \circ J$ and the Leibniz
rule for a $C^1$ multiplier, `HasWeakIteratedLineDerivOn.mul_contDiffOn_one`). The operator $P_1$ of
order one built as in Theorem 9.7, with the higher-order reflection in place of the even one,
therefore maps $W^{k,p}(\Omega)$ into $W^{k,p}(\mathbb{R}^N)$. Its restriction to $W^{k,p}(\Omega)$
is bounded by the closed graph theorem (`SobolevMultiIndex.exists_continuousLinearMap_of_order`),
because convergence in $W^{k,p}$ implies convergence in $W^{1,p}$, where $P_1$ is continuous. The
closed graph theorem does not change the function of $P_1$, so the $L^p$ bound of $P_1$ and its
formula on functions, which involves no exponent, hold for the operator of order $k$.

## Implementation notes

* The space is `EuclideanSpace ℝ (Fin (d + 1))`, so $N = d + 1$. The last coordinate $x_N$ is
  `x (Fin.last d)`. The cylinder $Q_r$ is `cylinder d r`. The upper half $V_+$ of an open set $V$ is
  `posHalf (single (Fin.last d) 1) V`. The map `scaleLast l` is $S_l$. The scales are `l j`, indexed
  from $0$.
* Several lemmas take the operators of the construction as variables, together with the formulas for
  their functions: `SobolevEuclidean.chartExtend_mem_of_ops`,
  `SobolevEuclidean.extension_mem_of_ops` and `SobolevEuclidean.exists_extensionL_of_order_of_ops`.
  The concrete operators are substituted once.
* The construction gives one operator for every exponent $p$ at a fixed order $k$, but not one
  operator for every order $k$, because the Vandermonde coefficients depend on $k$.
* The general tools of the proof are in other modules: the algebra of `MemSobolevMultiIndex`, the
  $C^k$ multipliers and the zero extension at every order in `Numlib.Analysis.Sobolev.Cutoff`; the
  closed graph step in `Numlib.Analysis.Sobolev.Operators`; the maps `scaleLast` and the cylinders
  $Q_r$ in `Numlib.Analysis.Sobolev.Extension`; the restriction of a diffeomorphism with bounded
  Jacobians in `Numlib.Analysis.Sobolev.Chart`; the transport of $W^{k,p}$ along a $C^k$
  diffeomorphism in `Numlib.Analysis.Sobolev.Calculus`. The Rellich–Kondrachov theorem at
  $p = \infty$ is in `Numlib.Analysis.Sobolev.Compactness`, and the bounded inclusion
  $W^{m+1+j,p}(\Omega) \to W^{j+1,r}(\Omega)$ of an extension domain
  (`SobolevEuclidean.exists_continuousLinearMap_lower_of_order`) is in
  `Numlib.Analysis.Sobolev.EmbeddingDomain`.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace EuclideanSpace
open scoped ContDiff Distributions ENNReal NNReal Topology RealInnerProductSpace

noncomputable section



/-! ### The two halves of an open set, and the maps $S_\lambda$ between them -/

section Halves

variable {d : ℕ} {V : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- The **negative half** $V_- = V \cap \{x_N < 0\}$ of an open set $V \subseteq \mathbb{R}^{d+1}$.

The positive half $V_+ = V \cap \{x_N > 0\}$ is `posHalf (single (Fin.last d) 1) V` of
`Numlib.Analysis.Sobolev.Reflection`. -/
def negHalf (V : Opens (EuclideanSpace ℝ (Fin (d + 1)))) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  (V : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ {x | x (Fin.last d) < 0}

/-- A point $x$ lies in $V_-$ if and only if $x \in V$ and $x_N < 0$. -/
theorem mem_negHalf {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ negHalf V ↔ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∧ x (Fin.last d) < 0 :=
  Iff.rfl

/-- The negative half $V_-$ is open. -/
theorem isOpen_negHalf' : IsOpen (negHalf V) :=
  V.isOpen.inter (isOpen_lt continuous_apply_last continuous_const)

/-- A point $x$ lies in the positive half $V_+$ if and only if $x \in V$ and $x_N > 0$. -/
theorem mem_posHalf_last_iff {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _) ↔
      x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∧ 0 < x (Fin.last d) := by
  rw [coe_posHalf]
  simp [EuclideanSpace.inner_single_last_one]

/-- The positive half $V_+$ is a subset of $V$. -/
theorem posHalf_last_subset :
    (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _) ⊆ (V : Set (EuclideanSpace ℝ (Fin (d + 1))))
      :=
  fun _ hx ↦ (mem_posHalf_last_iff.1 hx).1

/-- The negative half $V_-$ is a subset of $V$. -/
theorem negHalf_subset : negHalf V ⊆ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))) := fun _ hx ↦ hx.1

/-- The hyperplane $\{x_N = 0\}$ is a null set: almost every $x \in \mathbb{R}^{d+1}$ has
$x_N \ne 0$. -/
theorem ae_apply_last_ne_zero : ∀ᵐ x : EuclideanSpace ℝ (Fin (d + 1)), x (Fin.last d) ≠ 0 := by
  have hv : (single (Fin.last d) (1 : ℝ) : EuclideanSpace ℝ (Fin (d + 1))) ≠ 0 :=
    ne_zero_of_norm_ne_zero (by rw [EuclideanSpace.norm_single_last_one]; exact one_ne_zero)
  filter_upwards [ae_inner_ne_zero hv] with x hx
  rwa [EuclideanSpace.inner_single_last_one] at hx

/-- Let $G$, $A$, $B$ be functions with values in a normed group. If $G = A$ on $V_+$ and $G = B$ on
$V_-$, then $G = 1_{V_+} A + 1_{V_-} B$ almost everywhere on $V$. -/
theorem ae_eq_indicator_add_of_piecewise {F : Type*} [NormedAddCommGroup F] {G A B : _ → F}
    (hA : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), 0 < x (Fin.last d) → G x = A x)
    (hB : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → G x = B x) :
    G =ᵐ[volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _).indicator A + (negHalf V).indicator B := by
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet, ae_restrict_of_ae ae_apply_last_ne_zero]
    with x hxV hx
  rcases lt_or_gt_of_ne hx with h | h
  · have hxm : x ∈ negHalf V := ⟨hxV, h⟩
    have hxp : x ∉ (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _) := fun h' ↦
      lt_asymm h (mem_posHalf_last_iff.1 h').2
    rw [Pi.add_apply, Set.indicator_of_notMem hxp, Set.indicator_of_mem hxm, zero_add, hB x hxV h]
  · have hxp : x ∈ (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _) :=
      mem_posHalf_last_iff.2 ⟨hxV, h⟩
    have hxm : x ∉ negHalf V := fun h' ↦ lt_asymm h h'.2
    rw [Pi.add_apply, Set.indicator_of_mem hxp, Set.indicator_of_notMem hxm, add_zero, hA x hxV h]

/-- Let $G = A$ on $V_+$ and $G = B$ on $V_-$. If $A$ is almost everywhere strongly measurable on
$V_+$ and $B$ is so on $V_-$, then $G$ is almost everywhere strongly measurable on $V$. -/
theorem aestronglyMeasurable_of_piecewise {F : Type*} [NormedAddCommGroup F] {G A B : _ → F}
    (hA : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), 0 < x (Fin.last d) → G x = A x)
    (hB : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → G x = B x)
    (hAm : AEStronglyMeasurable A
      (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)))
    (hBm : AEStronglyMeasurable B (volume.restrict (negHalf V))) :
    AEStronglyMeasurable G (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  have h1 : AEStronglyMeasurable ((posHalf (single (Fin.last d) (1 : ℝ)) V : Set _).indicator A
      + (negHalf V).indicator B) volume :=
    ((aestronglyMeasurable_indicator_iff (posHalf _ V).isOpen.measurableSet).2 hAm).add
      ((aestronglyMeasurable_indicator_iff isOpen_negHalf'.measurableSet).2 hBm)
  exact (h1.mono_measure Measure.restrict_le_self).congr (ae_eq_indicator_add_of_piecewise hA
    hB).symm

/-- Let $1 \le p \le \infty$. If $G = A$ on $V_+$ and $G = B$ on $V_-$, then $\|G\|_{L^p(V)} \le
\|A\|_{L^p(V_+)} + \|B\|_{L^p(V_-)}$. -/
theorem eLpNorm_le_of_piecewise {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {G A B : _ → F}
    (hA : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), 0 < x (Fin.last d) → G x = A x)
    (hB : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → G x = B x) :
    eLpNorm G p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      ≤ eLpNorm A p (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _))
        + eLpNorm B p (volume.restrict (negHalf V)) := by
  calc eLpNorm G p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      = eLpNorm ((posHalf (single (Fin.last d) (1 : ℝ)) V : Set _).indicator A
          + (negHalf V).indicator B) p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1)))))
            :=
        eLpNorm_congr_ae (ae_eq_indicator_add_of_piecewise hA hB)
    _ ≤ eLpNorm ((posHalf (single (Fin.last d) (1 : ℝ)) V : Set _).indicator A) p
          (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        + eLpNorm ((negHalf V).indicator B) p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d +
          1))))) := eLpNorm_add_le hp
    _ ≤ eLpNorm ((posHalf (single (Fin.last d) (1 : ℝ)) V : Set _).indicator A) p volume
        + eLpNorm ((negHalf V).indicator B) p volume :=
        add_le_add (eLpNorm_mono_measure _ Measure.restrict_le_self)
          (eLpNorm_mono_measure _ Measure.restrict_le_self)
    _ = _ := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict
            (posHalf _ V).isOpen.measurableSet.nullMeasurableSet,
          eLpNorm_indicator_eq_eLpNorm_restrict isOpen_negHalf'.measurableSet.nullMeasurableSet]

/-- Let $\lambda < 0$, and let $S_\lambda$ map every point of $V_-$ into $V$. Then $S_\lambda$ maps
every point of $V_-$ into $V_+$. -/
theorem scaleLast_mem_posHalf {l : ℝ} (hl : l < 0)
    (hV : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → scaleLast l x ∈ V)
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ negHalf V) :
    scaleLast l x ∈ (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _) :=
  mem_posHalf_last_iff.2 ⟨hV x hx.1 hx.2, by
    rw [scaleLast_apply_last]; exact mul_pos_of_neg_of_neg hl hx.2⟩

/-- Let $\lambda < 0$, and let $S_\lambda$ map $V_-$ into $V$. Then
$V_- \subseteq S_\lambda^{-1}(V_+)$. -/
theorem negHalf_subset_preimage_scaleLast {l : ℝ} (hl : l < 0)
    (hV : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → scaleLast l x ∈ V)
      :
    negHalf V ⊆ scaleLast l ⁻¹' (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _) :=
  fun _ hx ↦ scaleLast_mem_posHalf hl hV hx

/-- Let $\lambda < 0$, and let $S_\lambda$ map $V_-$ into $V$. Then $S_\lambda(V_-) \subseteq V_+$.
-/
theorem image_negHalf_scaleLast_subset {l : ℝ} (hl : l < 0)
    (hV : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → scaleLast l x ∈ V)
      :
    scaleLast l '' negHalf V ⊆ (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _) := by
  rintro _ ⟨x, hx, rfl⟩
  exact scaleLast_mem_posHalf hl hV hx

/-- Let $\lambda < 0$, let $S_\lambda$ map $V_-$ into $V$, and let $p \in [0, \infty]$. There is a
finite constant $D$ with the following properties. If $f$ is almost everywhere strongly
measurable on $V_+$, then $f \circ S_\lambda$ is almost everywhere strongly measurable on $V_-$
and $\|f \circ S_\lambda\|_{L^p(V_-)} \le D \|f\|_{L^p(V_+)}$. If a property holds for almost
every point of $V_+$, then it holds at $S_\lambda x$ for almost every $x \in V_-$.

The constant is stated existentially, so that the users of the lemma do not see the Jacobian of
$S_\lambda$. -/
theorem exists_scaleLast_negHalf_facts {l : ℝ} (hl : l < 0)
    (hV : ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → scaleLast l x ∈ V)
      (p : ℝ≥0∞) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧
      (∀ {F : Type*} [NormedAddCommGroup F] (f : EuclideanSpace ℝ (Fin (d + 1)) → F),
        AEStronglyMeasurable f
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) →
        AEStronglyMeasurable (fun x ↦ f (scaleLast l x)) (volume.restrict (negHalf V)) ∧
        eLpNorm (fun x ↦ f (scaleLast l x)) p (volume.restrict (negHalf V))
          ≤ D * eLpNorm f p
            (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _))) ∧
      (∀ {P : EuclideanSpace ℝ (Fin (d + 1)) → Prop},
        (∀ᵐ x ∂volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _), P x) →
        ∀ᵐ x ∂volume.restrict (negHalf V), P (scaleLast l x)) := by
  obtain ⟨M, hS⟩ := scaleLast_isDiffeoOnWithBoundedJacobian hl.ne
    (posHalf (single (Fin.last d) (1 : ℝ)) V)
  obtain ⟨D, -, hD⟩ := hS.exists_abs_det_fderiv_invFun_le
  have hA : IsOpen (negHalf V) := isOpen_negHalf'
  have hAs := negHalf_subset_preimage_scaleLast hl hV
  have himg := image_negHalf_scaleLast_subset hl hV
  refine ⟨ENNReal.ofReal D ^ (1 / p.toReal), ENNReal.rpow_ne_top_of_nonneg (by positivity)
    ENNReal.ofReal_ne_top, fun f hf ↦ ⟨?_, ?_⟩, fun {P} hP ↦ ?_⟩
  · exact hS.aestronglyMeasurable_comp hA hAs
      (hf.mono_measure (Measure.restrict_mono himg le_rfl))
  · refine (hS.eLpNorm_comp_le hD hA hAs (hf.mono_measure (Measure.restrict_mono himg le_rfl))
      p).trans ?_
    gcongr
  · exact hS.ae_comp hA hAs (ae_restrict_of_ae_restrict_of_subset himg hP)

end Halves

/-! ### The higher-order reflection -/

section HigherReflection

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}

/-- The **higher-order reflection** across the hyperplane $x_N = 0$, for coefficients
$a \in \mathbb{R}^m$ and scales $\lambda \in \mathbb{R}^m$: for a function $w$ on
$\mathbb{R}^{d+1}$,
$$(P_a w)(x) = \begin{cases} w(x) & \text{if } x_N \ge 0, \\ \sum_j a_j\, w(S_{\lambda_j} x) &
  \text{if } x_N < 0. \end{cases}$$

The definition puts no condition on the scales; the results below take $-1 \le \lambda_j < 0$.
For $m = 1$, $a = 1$ and $\lambda = -1$ it is the even reflection
`evenReflection (single (Fin.last d) 1) w`. If $a$ solves the Vandermonde system
$\sum_j a_j \lambda_j^i = 1$ for $i < k$, it preserves $W^{k,p}$ ([brezis2011functional],
Comments on Chapter 9, 3; Lions and Magenes); see
`MemSobolevMultiIndex.higherReflection_of_order`. -/
def higherReflection (a l : Fin m → ℝ) (w : EuclideanSpace ℝ (Fin (d + 1)) → F)
    (x : EuclideanSpace ℝ (Fin (d + 1))) : F :=
  if 0 ≤ x (Fin.last d) then w x else ∑ j, a j • w (scaleLast (l j) x)

/-- The **reflected derivative**: for a field $Dw$ of linear maps on $\mathbb{R}^{d+1}$, it is
$Dw(x)$ if $x_N \ge 0$, and $\sum_j a_j\, Dw(S_{\lambda_j} x) \circ S_{\lambda_j}$ if $x_N < 0$.
This is the chain rule applied to each term of the higher-order reflection `higherReflection`. -/
def higherReflectionFDeriv (a l : Fin m → ℝ)
    (Dw : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F)
    (x : EuclideanSpace ℝ (Fin (d + 1))) : EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F :=
  if 0 ≤ x (Fin.last d) then Dw x
  else ∑ j, a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j))

variable (a l : Fin m → ℝ)

/-- On $\{x_N \ge 0\}$ the higher-order reflection is the function: $(P_a w)(x) = w(x)$. -/
theorem higherReflection_of_nonneg {w : EuclideanSpace ℝ (Fin (d + 1)) → F}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : 0 ≤ x (Fin.last d)) :
    higherReflection a l w x = w x := by
  simp only [higherReflection, hx, ↓reduceIte]

/-- On $\{x_N < 0\}$ the higher-order reflection is the combination
$(P_a w)(x) = \sum_j a_j\, w(S_{\lambda_j} x)$. -/
theorem higherReflection_of_neg {w : EuclideanSpace ℝ (Fin (d + 1)) → F}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x (Fin.last d) < 0) :
    higherReflection a l w x = ∑ j, a j • w (scaleLast (l j) x) := by
  simp only [higherReflection, not_le.2 hx, ↓reduceIte]

/-- On $\{x_N \ge 0\}$ the reflected derivative `higherReflectionFDeriv a l Dw` is $Dw(x)$. -/
theorem higherReflectionFDeriv_of_nonneg
    {Dw : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : 0 ≤ x (Fin.last d)) :
    higherReflectionFDeriv a l Dw x = Dw x := by
  simp only [higherReflectionFDeriv, hx, ↓reduceIte]

/-- On $\{x_N < 0\}$ the reflected derivative `higherReflectionFDeriv a l Dw` is $\sum_j a_j\,
Dw(S_{\lambda_j} x) \circ S_{\lambda_j}$. -/
theorem higherReflectionFDeriv_of_neg
    {Dw : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x (Fin.last d) < 0) :
    higherReflectionFDeriv a l Dw x
      = ∑ j, a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j)) := by
  simp only [higherReflectionFDeriv, not_le.2 hx, ↓reduceIte]

/-- The higher-order reflection is additive: $P_a(f + g) = P_a f + P_a g$. -/
theorem higherReflection_add (f g : EuclideanSpace ℝ (Fin (d + 1)) → F) :
    higherReflection a l (f + g) = higherReflection a l f + higherReflection a l g := by
  funext x
  simp only [higherReflection, Pi.add_apply]
  split_ifs
  · rfl
  · simp only [smul_add, Finset.sum_add_distrib]

/-- The higher-order reflection commutes with real scalar multiplication: $P_a(c f) = c\, P_a f$. -/
theorem higherReflection_smul (c : ℝ) (f : EuclideanSpace ℝ (Fin (d + 1)) → F) :
    higherReflection a l (c • f) = c • higherReflection a l f := by
  funext x
  simp only [higherReflection, Pi.smul_apply]
  split_ifs
  · rfl
  · simp only [Finset.smul_sum, smul_comm c]

variable {V : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {a l}

/-- The **standing hypotheses on the scales and the set**: every scale satisfies
$-1 \le \lambda_j < 0$, and every $S_{\lambda_j}$ maps the negative half $V_-$ into $V$. -/
structure IsReflectionSet (l : Fin m → ℝ) (V : Opens (EuclideanSpace ℝ (Fin (d + 1)))) : Prop where
  /-- Every scale is negative: $\lambda_j < 0$. -/
  neg : ∀ j, l j < 0
  /-- Every scale is at least $-1$: $-1 \le \lambda_j$. -/
  neg_one_le : ∀ j, -1 ≤ l j
  /-- Every $S_{\lambda_j}$ maps each point $x \in V$ with $x_N < 0$ into $V$. -/
  mem : ∀ j, ∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (d + 1)))), x (Fin.last d) < 0 → scaleLast (l j)
    x ∈ V

/-- If $-1 \le \lambda_j < 0$ for every $j$, then every cylinder $Q_r$ satisfies the standing
hypotheses `IsReflectionSet` for the scales $\lambda$. -/
theorem isReflectionSet_cylinder (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j) (r : ℝ) :
    IsReflectionSet l (cylinder d r) :=
  ⟨hl, hl1, fun j _ hx _ ↦
    scaleLast_mem_cylinder (abs_le.2 ⟨hl1 j, (hl j).le.trans zero_le_one⟩) hx⟩

/-- Let the scales $\lambda$ and the open set $V$ satisfy `IsReflectionSet`, let
$a \in \mathbb{R}^m$ and $1 \le p \le \infty$. There is a finite constant $C$ with the following
properties. If $w$ is almost everywhere strongly measurable on $V_+$, then $P_a w$ is almost
everywhere strongly measurable on $V$ and $\|P_a w\|_{L^p(V)} \le C \|w\|_{L^p(V_+)}$. The same
holds, with the same constant, for a field $Dw$ of linear maps and its reflected derivative
`higherReflectionFDeriv a l Dw`. If a property holds for almost every point of $V_+$, then for
almost every $x \in V_-$ it holds at $S_{\lambda_j} x$ for every $j$. -/
theorem IsReflectionSet.exists_facts (hV : IsReflectionSet l V) (a : Fin m → ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      (∀ w : EuclideanSpace ℝ (Fin (d + 1)) → F,
        AEStronglyMeasurable w
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) →
        AEStronglyMeasurable (higherReflection a l w) (volume.restrict (V : Set (EuclideanSpace ℝ
          (Fin (d + 1))))) ∧
        eLpNorm (higherReflection a l w) p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d +
          1)))))
          ≤ C * eLpNorm w p
            (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _))) ∧
      (∀ Dw : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F,
        AEStronglyMeasurable Dw
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) →
        AEStronglyMeasurable (higherReflectionFDeriv a l Dw) (volume.restrict (V : Set
          (EuclideanSpace ℝ (Fin (d + 1))))) ∧
        eLpNorm (higherReflectionFDeriv a l Dw) p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin
          (d + 1)))))
          ≤ C * eLpNorm Dw p
            (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _))) ∧
      (∀ {P : EuclideanSpace ℝ (Fin (d + 1)) → Prop},
        (∀ᵐ x ∂volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _), P x) →
        ∀ᵐ x ∂volume.restrict (negHalf V), ∀ j, P (scaleLast (l j) x)) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  choose D hD hDf hDP using fun j ↦ exists_scaleLast_negHalf_facts (hV.neg j) (hV.mem j) p
  obtain ⟨K, hK⟩ : ∃ K : Fin m → ℝ≥0∞, K = fun j ↦ ENNReal.ofReal ‖scaleLast (l j)‖ :=
    ⟨fun j ↦ ENNReal.ofReal ‖scaleLast (l j)‖, rfl⟩
  have hK' : ∀ j, K j ≠ ⊤ := fun j ↦ by rw [hK]; exact ENNReal.ofReal_ne_top
  obtain ⟨C, hC⟩ : ∃ C : ℝ≥0∞, C = 1 + ∑ j, ‖a j‖ₑ * (1 + K j) * D j := ⟨_, rfl⟩
  have hC' : C ≠ ⊤ := by
    rw [hC]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.sum_ne_top.2 fun j _ ↦
      ENNReal.mul_ne_top (ENNReal.mul_ne_top enorm_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hK' j⟩)) (hD j)⟩
  refine ⟨C, hC', fun w hw ↦ ⟨?_, ?_⟩, fun Dw hDw ↦ ⟨?_, ?_⟩, fun {P} hP ↦ ?_⟩
  · refine aestronglyMeasurable_of_piecewise (A := w)
      (B := fun x ↦ ∑ j, a j • w (scaleLast (l j) x))
      (fun x _ hx ↦ higherReflection_of_nonneg a l hx.le)
      (fun x _ hx ↦ higherReflection_of_neg a l hx) hw ?_
    exact Finset.aestronglyMeasurable_fun_sum Finset.univ
      (f := fun j x ↦ a j • w (scaleLast (l j) x)) fun j _ ↦ ((hDf j w hw).1).const_smul (a j)
  · refine (eLpNorm_le_of_piecewise hp (A := w)
      (B := fun x ↦ ∑ j, a j • w (scaleLast (l j) x))
      (fun x _ hx ↦ higherReflection_of_nonneg a l hx.le)
      (fun x _ hx ↦ higherReflection_of_neg a l hx)).trans ?_
    have hB : eLpNorm (fun x ↦ ∑ j, a j • w (scaleLast (l j) x)) p (volume.restrict (negHalf V))
        ≤ ∑ j, ‖a j‖ₑ * D j * eLpNorm w p
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) := by
      have e : (fun x ↦ ∑ j, a j • w (scaleLast (l j) x))
          = ∑ j, fun x ↦ a j • w (scaleLast (l j) x) := by
        funext x; simp only [Finset.sum_apply]
      rw [e]
      refine (eLpNorm_sum_le hp).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      have e' : (fun x ↦ a j • w (scaleLast (l j) x)) = a j • fun x ↦ w (scaleLast (l j) x) := rfl
      rw [e', eLpNorm_const_smul, mul_assoc]
      gcongr
      exact (hDf j w hw).2
    calc _ ≤ eLpNorm w p (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _))
          + ∑ j, ‖a j‖ₑ * D j * eLpNorm w p
            (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) :=
          add_le_add le_rfl hB
      _ = (1 + ∑ j, ‖a j‖ₑ * D j) * eLpNorm w p
            (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) := by
          rw [add_mul, one_mul, Finset.sum_mul]
      _ ≤ C * eLpNorm w p (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) := by
          gcongr
          rw [hC]
          gcongr with j _
          exact le_mul_of_one_le_right zero_le (le_add_right le_rfl)
  · refine aestronglyMeasurable_of_piecewise (A := Dw)
      (B := fun x ↦ ∑ j, a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j)))
      (fun x _ hx ↦ higherReflectionFDeriv_of_nonneg a l hx.le)
      (fun x _ hx ↦ higherReflectionFDeriv_of_neg a l hx) hDw ?_
    refine Finset.aestronglyMeasurable_fun_sum Finset.univ
      (f := fun j x ↦ a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j)))
      fun j _ ↦ AEStronglyMeasurable.const_smul ?_ (a j)
    exact (((ContinuousLinearMap.compL ℝ _ _ F).flip (scaleLast (l j))).continuous
      |>.comp_aestronglyMeasurable (hDf j Dw hDw).1).congr (Eventually.of_forall fun x ↦ by simp)
  · refine (eLpNorm_le_of_piecewise hp (A := Dw)
      (B := fun x ↦ ∑ j, a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j)))
      (fun x _ hx ↦ higherReflectionFDeriv_of_nonneg a l hx.le)
      (fun x _ hx ↦ higherReflectionFDeriv_of_neg a l hx)).trans ?_
    have hB : eLpNorm (fun x ↦ ∑ j, a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j))) p
        (volume.restrict (negHalf V))
        ≤ ∑ j, ‖a j‖ₑ * K j * D j * eLpNorm Dw p
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) := by
      have e : (fun x ↦ ∑ j, a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j)))
          = ∑ j, fun x ↦ a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j)) := by
        funext x; simp only [Finset.sum_apply]
      rw [e]
      refine (eLpNorm_sum_le hp).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      have e' : (fun x ↦ a j • (Dw (scaleLast (l j) x)).comp (scaleLast (l j)))
          = a j • fun x ↦ (Dw (scaleLast (l j) x)).comp (scaleLast (l j)) := rfl
      rw [e', eLpNorm_const_smul]
      have hm : AEStronglyMeasurable (fun x ↦ (Dw (scaleLast (l j) x)).comp (scaleLast (l j)))
          (volume.restrict (negHalf V)) :=
        (((ContinuousLinearMap.compL ℝ _ _ F).flip (scaleLast (l j))).continuous
          |>.comp_aestronglyMeasurable (hDf j Dw hDw).1).congr
          (Eventually.of_forall fun x ↦ by simp)
      have hΛ := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm (g := fun x ↦ Dw (scaleLast (l j) x))
        (c := ‖scaleLast (l j)‖) (Eventually.of_forall fun x ↦ by
          rw [mul_comm]
          exact ContinuousLinearMap.opNorm_comp_le _ _) p
      calc ‖a j‖ₑ * eLpNorm (fun x ↦ (Dw (scaleLast (l j) x)).comp (scaleLast (l j))) p
            (volume.restrict (negHalf V))
          ≤ ‖a j‖ₑ * (ENNReal.ofReal ‖scaleLast (l j)‖ * (D j * eLpNorm Dw p
              (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)))) := by
            gcongr
            refine hΛ.trans ?_
            gcongr
            exact (hDf j Dw hDw).2
        _ = ‖a j‖ₑ * K j * D j * eLpNorm Dw p
              (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) := by
            rw [hK]; ring
    calc _ ≤ eLpNorm Dw p (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _))
          + ∑ j, ‖a j‖ₑ * K j * D j * eLpNorm Dw p
            (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) :=
          add_le_add le_rfl hB
      _ = (1 + ∑ j, ‖a j‖ₑ * K j * D j) * eLpNorm Dw p
            (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) := by
          rw [add_mul, one_mul, Finset.sum_mul]
      _ ≤ C * eLpNorm Dw p (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set _)) := by
          gcongr
          rw [hC]
          gcongr with j _
          exact le_add_left le_rfl
  · rw [ae_all_iff]
    exact fun j ↦ hDP j hP

end HigherReflection

/-! ### The gluing lemma: a $C^1$ function that vanishes on the hyperplane, cut to the lower half -/

section Gluing

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The inner product of $x$ with $-e_N$ is $-x_N$. -/
theorem inner_neg_single_last (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ⟪x, -single (Fin.last d) (1 : ℝ)⟫ = -x (Fin.last d) := by
  rw [inner_neg_right, EuclideanSpace.inner_single_last_one]

/-- $x - S_0 x = x_N e_N$. -/
theorem sub_scaleLast_zero (x : EuclideanSpace ℝ (Fin (d + 1))) :
    x - scaleLast 0 x = x (Fin.last d) • single (Fin.last d) (1 : ℝ) := by
  ext i
  simp only [PiLp.sub_apply, scaleLast_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h; ring
  · ring

/-- $\|x - S_0 x\| = |x_N|$. -/
theorem norm_sub_scaleLast_zero (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ‖x - scaleLast 0 x‖ = |x (Fin.last d)| := by
  rw [sub_scaleLast_zero, norm_smul, EuclideanSpace.norm_single_last_one, mul_one,
    Real.norm_eq_abs]

/-- The lower half space $\{x_N < 0\}$ is measurable. -/
theorem measurableSet_lowerHalf :
    MeasurableSet {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0} :=
  (isOpen_lt continuous_apply_last continuous_const).measurableSet

/-- The **gluing lemma**. Let $F$ be a real normed space, and let $g : \mathbb{R}^{d+1} \to F$ be of
class $C^1$ with $g(x) = 0$ whenever $x_N = 0$. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a
convex open set with compact closure such that $S_0 x = (x', 0) \in \Omega$ for every
$x \in \Omega$. Then on $\Omega$ the function $1_{\{x_N < 0\}}\, g$ has the weak derivative
$1_{\{x_N < 0\}}\, Dg$.

The proof shows that $\eta_n g \to 1_{\{x_N < 0\}}\, g$ in $W^{1,1}(\Omega)$ for the cut-off
functions $\eta_n(x) = \eta(-(n+1) x_N)$, which are $1$ on $\{x_N \le -1/(n+1)\}$ and $0$ on
$\{x_N \ge -1/(2(n+1))\}$. The term $g\, \nabla\eta_n$ stays bounded, because $|g| \le M |x_N|$
by the mean value theorem and $|\nabla\eta_n| \le C(n+1)$ on a strip of width $1/(n+1)$, and it
tends to $0$ off the hyperplane. The weak derivative is closed under limits in $L^1$
(`hasWeakIteratedFDerivOn_of_tendsto_eLpNorm_one`). -/
theorem hasWeakFDerivOn_indicator_lowerHalf_of_contDiff {g : EuclideanSpace ℝ (Fin (d + 1)) → F}
    (hg : ContDiff ℝ 1 g) (hg0 : ∀ x, x (Fin.last d) = 0 → g x = 0)
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hΩc : IsCompact (closure (Ω : Set (EuclideanSpace
      ℝ (Fin (d + 1))))))
    (hΩv : Convex ℝ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΩ0 : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), scaleLast 0 x ∈ Ω) :
    HasWeakFDerivOn ({x | x (Fin.last d) < 0}.indicator g)
      ({x | x (Fin.last d) < 0}.indicator (fderiv ℝ g)) Ω volume := by
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin (d + 1)), v = -single (Fin.last d) (1 : ℝ) :=
    ⟨_, rfl⟩
  have hvx : ∀ x, ⟪x, v⟫ = -x (Fin.last d) := fun x ↦ by rw [hv, inner_neg_single_last]
  have hL : MeasurableSet {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0} :=
    measurableSet_lowerHalf
  have hΩm : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := Ω.isOpen.measurableSet
  have hΩfin : volume (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤ :=
    ((measure_mono subset_closure).trans_lt hΩc.measure_lt_top).ne
  -- bounds for `g` and `∇g` on `Ω`
  obtain ⟨M, hM⟩ := hΩc.exists_bound_of_continuousOn hg.continuous.continuousOn
  obtain ⟨M'₀, hM'₀⟩ :=
    hΩc.exists_bound_of_continuousOn (hg.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨M', hM'def⟩ : ∃ M' : ℝ, M' = max M'₀ 0 := ⟨_, rfl⟩
  have hM' : ∀ x ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ‖fderiv ℝ g x‖ ≤ M' :=
    fun x hx ↦ (hM'₀ x hx).trans (by rw [hM'def]; exact le_max_left _ _)
  have hM'0 : 0 ≤ M' := by rw [hM'def]; exact le_max_right _ _
  -- the mean value bound `‖g x‖ ≤ M' |x_N|` on `Ω`
  have hgx : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), ‖g x‖ ≤ M' * |x (Fin.last d)| := by
    intro x hx
    have h0 : g (scaleLast 0 x) = 0 := hg0 _ (by rw [scaleLast_apply_last, zero_mul])
    have := hΩv.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ (hg.differentiable one_ne_zero).differentiableAt)
      (fun z hz ↦ hM' z (subset_closure hz)) (hΩ0 x hx) hx
    rwa [h0, sub_zero, norm_sub_scaleLast_zero] at this
  obtain ⟨Cη, hCη0, hCη⟩ := exists_abs_deriv_reflectionCutoff_le
  -- the cut-offs and the approximants
  obtain ⟨η, hη⟩ : ∃ η : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
    η = fun (n : ℕ) x ↦ reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) := ⟨_, rfl⟩
  have hηx : ∀ n x, η n x = reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) := fun n x ↦ by rw [hη]
  have hηs : ∀ n, ContDiff ℝ ∞ (η n) := fun n ↦ by
    rw [hη]
    exact contDiff_reflectionCutoff.comp (contDiff_const.mul (contDiff_id.inner ℝ contDiff_const))
  have hη01 : ∀ n x, |η n x| ≤ 1 := fun n x ↦ by rw [hηx]; exact abs_reflectionCutoff_le_one _
  have hηd : ∀ n x, HasFDerivAt (η n)
      (deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) • (((n : ℝ) + 1) • innerSL ℝ v)) x :=
    fun n x ↦ by rw [hη]; exact hasFDerivAt_reflectionCutoff_inner v _ x
  -- pointwise limits of the cut-offs off the hyperplane
  have hηlim : ∀ x, x (Fin.last d) ≠ 0 →
      Tendsto (fun n ↦ η n x) atTop (𝓝 ({x | x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x)) :=
        by
    intro x hx
    rcases lt_or_gt_of_ne hx with h | h
    · rw [Set.indicator_of_mem (show x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0}
        from h)]
      simp only [hηx, hvx]
      exact tendsto_reflectionCutoff_mul (neg_pos.2 h)
    · rw [Set.indicator_of_notMem (show x ∉ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) <
      0}
        from not_lt.2 h.le)]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun n ↦ ?_)
      change (0 : ℝ) = η n x
      rw [hηx, hvx, reflectionCutoff_of_le_half]
      have : ((n : ℝ) + 1) * -x (Fin.last d) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (neg_nonpos.2 h.le)
      linarith
  have hη'lim : ∀ x, x (Fin.last d) ≠ 0 →
      ∀ᶠ n : ℕ in atTop, deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) = 0 := by
    intro x hx
    rcases lt_or_gt_of_ne hx with h | h
    · rw [hvx]
      exact eventually_deriv_reflectionCutoff_mul_eq_zero (neg_pos.2 h)
    · refine Eventually.of_forall fun n ↦ deriv_reflectionCutoff_eq_zero (Or.inl ?_)
      rw [hvx]
      have : ((n : ℝ) + 1) * -x (Fin.last d) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (neg_nonpos.2 h.le)
      linarith
  -- the bound on the derivative term `g ∇η_n`
  have hgη : ∀ (n : ℕ) x, x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) →
      ‖g x‖ * (|deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)| * (((n : ℝ) + 1) * ‖innerSL ℝ v‖))
        ≤ M' * Cη * ‖innerSL ℝ v‖ := by
    intro n x hx
    by_cases h1 : 1 < ((n : ℝ) + 1) * ⟪x, v⟫
    · rw [deriv_reflectionCutoff_eq_zero (Or.inr h1), abs_zero, zero_mul, mul_zero]
      exact mul_nonneg (mul_nonneg hM'0 hCη0) (norm_nonneg _)
    · rcases le_or_gt ⟪x, v⟫ 0 with hxv | hxv
      · have : ((n : ℝ) + 1) * ⟪x, v⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hxv
        rw [deriv_reflectionCutoff_eq_zero (Or.inl (by linarith)), abs_zero, zero_mul, mul_zero]
        exact mul_nonneg (mul_nonneg hM'0 hCη0) (norm_nonneg _)
      · have hxv' : |x (Fin.last d)| = ⟪x, v⟫ := by
          rw [hvx] at hxv ⊢
          rw [abs_of_neg (by linarith)]
        calc ‖g x‖ * (|deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)|
              * (((n : ℝ) + 1) * ‖innerSL ℝ v‖))
            ≤ (M' * |x (Fin.last d)|) * (Cη * (((n : ℝ) + 1) * ‖innerSL ℝ v‖)) :=
              mul_le_mul (hgx x hx) (mul_le_mul_of_nonneg_right (hCη _) (by positivity))
                (by positivity) (mul_nonneg hM'0 (abs_nonneg _))
          _ = M' * Cη * ‖innerSL ℝ v‖ * (((n : ℝ) + 1) * ⟪x, v⟫) := by rw [hxv']; ring
          _ ≤ M' * Cη * ‖innerSL ℝ v‖ * 1 := by
              gcongr
              exact not_lt.1 h1
          _ = M' * Cη * ‖innerSL ℝ v‖ := mul_one _
  -- the approximants `g_n = η_n g` are `C^1`, with the classical derivative as weak derivative
  obtain ⟨G, hG⟩ : ∃ G : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → F,
    G = fun (n : ℕ) x ↦ η n x • g x := ⟨_, rfl⟩
  have hGx : ∀ n x, G n x = η n x • g x := fun n x ↦ by rw [hG]
  have hGs : ∀ n, ContDiff ℝ 1 (G n) := fun n ↦ by
    rw [hG]
    exact ((hηs n).of_le (by simp)).smul hg
  have hGd : ∀ n x, HasFDerivAt (G n) (η n x • fderiv ℝ g x
      + (deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) • (((n : ℝ) + 1) • innerSL ℝ v)).smulRight
        (g x)) x := fun n x ↦ by
    rw [hG]
    exact (hηd n x).smul (hg.differentiable one_ne_zero x).hasFDerivAt
  have hGw : ∀ n, HasWeakIteratedFDerivOn 1 (G n)
      (fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm (fderiv ℝ
        (G n) x)) Ω volume := by
    intro n
    have := (hGs n).contDiffOn.hasWeakIteratedFDerivOn (Ω := Ω) (μ := volume) (m := 1) le_rfl
    refine this.congr_ae (EventuallyEq.refl _ _) (Eventually.of_forall fun x ↦ ?_)
    ext m
    simp [iteratedFDeriv_one_apply]
  -- the limit function and derivative are locally integrable
  have hfl : LocallyIntegrableOn ({x | x (Fin.last d) < 0}.indicator g) Ω volume :=
    (hg.continuous.locallyIntegrable.indicator hL).locallyIntegrableOn _
  have hwl : LocallyIntegrableOn (fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin
    (d + 1))) F).symm
      ({x | x (Fin.last d) < 0}.indicator (fderiv ℝ g) x)) Ω volume := by
    have h1 : LocallyIntegrable ({x | x (Fin.last d) < 0}.indicator (fderiv ℝ g)) volume :=
      (hg.continuous_fderiv one_ne_zero).locallyIntegrable.indicator hL
    exact (h1.locallyIntegrableOn _).comp_continuousLinearMap
      (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
        F).symm.toContinuousLinearEquiv.toContinuousLinearMap
  -- the dominated convergence of the two `L^1(Ω)` norms
  have key := hasWeakIteratedFDerivOn_of_tendsto_eLpNorm_one hGw hfl hwl ?_ ?_
  · exact key
  · -- `G n → 1_{x_N<0} g` in `L^1(Ω)`
    have hmeas : ∀ n, AEStronglyMeasurable (G n - {x | x (Fin.last d) < 0}.indicator g)
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := fun n ↦
      (hGs n).continuous.aestronglyMeasurable.sub
        (hg.continuous.aestronglyMeasurable.indicator hL)
    refine Tendsto.congr (fun n ↦ (eLpNorm_one_eq_lintegral_enorm (hmeas n)).symm) ?_
    rw [show (0 : ℝ≥0∞) = ∫⁻ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), (0 : ℝ≥0∞) from by
      simp]
    refine tendsto_lintegral_of_dominated_convergence' (fun _ ↦ ENNReal.ofReal M)
      (fun n ↦ (hmeas n).enorm) (fun n ↦ ?_) ?_ ?_
    · filter_upwards [ae_restrict_mem hΩm] with x hx
      rw [Pi.sub_apply, hGx]
      have hb : ‖η n x • g x - {x | x (Fin.last d) < 0}.indicator g x‖ ≤ M := by
        have e : η n x • g x - {x | x (Fin.last d) < 0}.indicator g x
            = (η n x - {x | x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x) • g x := by
          rw [sub_smul]
          congr 1
          by_cases h : x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0}
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_smul]
          · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_smul]
        rw [e, norm_smul, Real.norm_eq_abs]
        have h1 : |η n x - {x | x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x| ≤ 1 := by
          have := hη01 n x
          have h0 : 0 ≤ η n x := by rw [hηx]; exact reflectionCutoff_nonneg _
          by_cases h : x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0}
          · rw [Set.indicator_of_mem h]
            rw [abs_le] at this ⊢
            constructor <;> linarith
          · rw [Set.indicator_of_notMem h, sub_zero]
            exact this
        calc |η n x - {x | x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x| * ‖g x‖
            ≤ 1 * M := mul_le_mul h1 (hM x (subset_closure hx)) (norm_nonneg _) zero_le_one
          _ = M := one_mul _
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hb
    · rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΩfin
    · filter_upwards [ae_restrict_of_ae ae_apply_last_ne_zero] with x hx
      have h1 := ((hηlim x hx).sub (tendsto_const_nhds (x := {x : EuclideanSpace ℝ (Fin (d + 1)) |
        x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x))).smul_const (g x)
      rw [sub_self, zero_smul] at h1
      have h2 : Tendsto (fun n ↦ G n x - {x | x (Fin.last d) < 0}.indicator g x) atTop (𝓝 0) := by
        refine h1.congr fun n ↦ ?_
        rw [hGx, sub_smul]
        congr 1
        by_cases h : x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0}
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_smul]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_smul]
      have := (continuous_enorm.tendsto (0 : F)).comp h2
      simpa [Function.comp_def, enorm_zero] using this
  · -- `∇G n → 1_{x_N<0} ∇g` in `L^1(Ω)`
    obtain ⟨e, he⟩ : ∃ e : (EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F) ≃ₗᵢ[ℝ]
        (EuclideanSpace ℝ (Fin (d + 1)) [×1]→L[ℝ] F),
      e = (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm := ⟨_, rfl⟩
    have hmeas : ∀ n, AEStronglyMeasurable
        ((fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
          (fderiv ℝ (G n) x))
          - fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
            ({x | x (Fin.last d) < 0}.indicator (fderiv ℝ g) x)) (volume.restrict (Ω : Set
              (EuclideanSpace ℝ (Fin (d + 1))))) :=
      fun n ↦ ((continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
        F).symm.continuous.comp_aestronglyMeasurable
        ((hGs n).continuous_fderiv one_ne_zero).aestronglyMeasurable).sub
        ((continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
          F).symm.continuous.comp_aestronglyMeasurable
          ((hg.continuous_fderiv one_ne_zero).aestronglyMeasurable.indicator hL))
    refine Tendsto.congr (fun n ↦ (eLpNorm_one_eq_lintegral_enorm (hmeas n)).symm) ?_
    rw [show (0 : ℝ≥0∞) = ∫⁻ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), (0 : ℝ≥0∞) from by
      simp]
    refine tendsto_lintegral_of_dominated_convergence'
      (fun _ ↦ ENNReal.ofReal (M' + M' * Cη * ‖innerSL ℝ v‖))
      (fun n ↦ (hmeas n).enorm) (fun n ↦ ?_) ?_ ?_
    · filter_upwards [ae_restrict_mem hΩm] with x hx
      rw [Pi.sub_apply, ← map_sub, ← ofReal_norm, LinearIsometryEquiv.norm_map]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [(hGd n x).fderiv]
      have e1 : η n x • fderiv ℝ g x
          + (deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) • (((n : ℝ) + 1) • innerSL ℝ
            v)).smulRight
            (g x) - {x | x (Fin.last d) < 0}.indicator (fderiv ℝ g) x
          = (η n x - {x | x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x) • fderiv ℝ g x
            + (deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)
              • (((n : ℝ) + 1) • innerSL ℝ v)).smulRight (g x) := by
        rw [sub_smul]
        by_cases h : x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0}
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_smul]; abel
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_smul]; abel
      rw [e1]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        have h1 : |η n x - {x | x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x| ≤ 1 := by
          have := hη01 n x
          have h0 : 0 ≤ η n x := by rw [hηx]; exact reflectionCutoff_nonneg _
          by_cases h : x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0}
          · rw [Set.indicator_of_mem h]
            rw [abs_le] at this ⊢
            constructor <;> linarith
          · rw [Set.indicator_of_notMem h, sub_zero]
            exact this
        calc |η n x - {x | x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x| * ‖fderiv ℝ g x‖
            ≤ 1 * M' := mul_le_mul h1 (hM' x (subset_closure hx)) (norm_nonneg _) zero_le_one
          _ = M' := one_mul _
      · rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_smul, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), mul_comm]
        exact hgη n x hx
    · rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΩfin
    · filter_upwards [ae_restrict_of_ae ae_apply_last_ne_zero] with x hx
      have h1 := ((hηlim x hx).sub (tendsto_const_nhds (x := {x : EuclideanSpace ℝ (Fin (d + 1)) |
        x (Fin.last d) < 0}.indicator (fun _ ↦ (1 : ℝ)) x))).smul_const (fderiv ℝ g x)
      rw [sub_self, zero_smul] at h1
      have h2 : Tendsto (fun n : ℕ ↦ (deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)
          • (((n : ℝ) + 1) • innerSL ℝ v)).smulRight (g x)) atTop (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hη'lim x hx] with n hn
        rw [hn, zero_smul, ContinuousLinearMap.zero_smulRight]
      have h3 : Tendsto (fun n ↦ fderiv ℝ (G n) x - {x | x (Fin.last d) < 0}.indicator (fderiv ℝ g)
        x)
          atTop (𝓝 0) := by
        have := h1.add h2
        rw [add_zero] at this
        refine this.congr fun n ↦ ?_
        rw [(hGd n x).fderiv, sub_smul]
        by_cases h : x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0}
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_smul]; abel
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_smul]; abel
      have h4 := ((continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
        F).symm.continuous.tendsto 0).comp h3
      rw [map_zero] at h4
      have := (continuous_enorm.tendsto (0 : EuclideanSpace ℝ (Fin (d + 1)) [×1]→L[ℝ] F)).comp h4
      simpa [Function.comp_def, map_sub, enorm_zero] using this

end Gluing

/-! ### The higher-order reflection at order one: the derivative -/

section ReflectionIdentity

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
  {V : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- Every compact subset $K$ of the cylinder $Q_r$ lies in a cylinder $Q_{r'}$ with $r' < r$. -/
theorem exists_lt_subset_cylinder {r : ℝ} {K : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hK : IsCompact K) (hKQ : K ⊆ cylinder d r) : ∃ r', r' < r ∧ K ⊆ cylinder d r' := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨r - 1, by linarith, empty_subset _⟩
  obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hne
    (continuous_init.norm.max continuous_abs_apply_last).continuousOn
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max ‖init x₀‖ |x₀ (Fin.last d)| := ⟨_, rfl⟩
  have hm1 : m < r := by rw [hm]; exact max_lt (hKQ hx₀).1 (hKQ hx₀).2
  refine ⟨(m + r) / 2, by linarith, fun x hx ↦ ?_⟩
  have h : max ‖init x‖ |x (Fin.last d)| ≤ m := by rw [hm]; exact hmax hx
  exact ⟨by linarith [le_max_left ‖init x‖ |x (Fin.last d)|],
    by linarith [le_max_right ‖init x‖ |x (Fin.last d)|]⟩

/-- If $r' < r$, the closure of $Q_{r'}$ lies in $Q_r$. -/
theorem closure_cylinder_subset_cylinder {r' r : ℝ} (h : r' < r) :
    closure (cylinder d r' : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ cylinder d r :=
  fun _ hx ↦ ⟨(closure_cylinder_subset r' hx).1.trans_lt h,
    (closure_cylinder_subset r' hx).2.trans_lt h⟩

/-- The higher-order reflection of a difference: $P_a(f - g) = P_a f - P_a g$. -/
theorem higherReflection_sub (a l : Fin m → ℝ) (f g : EuclideanSpace ℝ (Fin (d + 1)) → F) :
    higherReflection a l (f - g) = higherReflection a l f - higherReflection a l g := by
  rw [sub_eq_add_neg, higherReflection_add, sub_eq_add_neg]
  congr 1
  rw [← neg_one_smul ℝ g, higherReflection_smul, neg_one_smul]

/-- The reflected derivative `higherReflectionFDeriv` of a difference is the difference of the
reflected derivatives. -/
theorem higherReflectionFDeriv_sub (a l : Fin m → ℝ)
    (D₁ D₂ : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F) :
    higherReflectionFDeriv a l (D₁ - D₂)
      = higherReflectionFDeriv a l D₁ - higherReflectionFDeriv a l D₂ := by
  funext x
  simp only [higherReflectionFDeriv, Pi.sub_apply]
  split_ifs
  · rfl
  · simp only [ContinuousLinearMap.sub_comp, smul_sub, Finset.sum_sub_distrib]

/-- The higher-order reflection of any function $g$ is the function plus a correction on the lower
half:
$$P_a g = g + 1_{\{x_N < 0\}} \Big( \sum_j a_j\, g \circ S_{\lambda_j} - g \Big).$$
-/
theorem higherReflection_eq_add_indicator (a l : Fin m → ℝ)
    (g : EuclideanSpace ℝ (Fin (d + 1)) → F) :
    higherReflection a l g = g + {x | x (Fin.last d) < 0}.indicator
      (fun x ↦ ∑ j, a j • g (scaleLast (l j) x) - g x) := by
  funext x
  by_cases hx : x (Fin.last d) < 0
  · rw [Pi.add_apply, higherReflection_of_neg a l hx, Set.indicator_of_mem
      (show x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0} from hx)]
    abel
  · rw [Pi.add_apply, higherReflection_of_nonneg a l (not_lt.1 hx), Set.indicator_of_notMem
      (show x ∉ {x : EuclideanSpace ℝ (Fin (d + 1)) | x (Fin.last d) < 0} from hx), add_zero]

/-- Let $g$ be of class $C^1$. At every point $x$, the correction
$G = \sum_j a_j\, g \circ S_{\lambda_j} - g$ has the derivative $\sum_j a_j\, Dg(S_{\lambda_j}
x) \circ S_{\lambda_j} - Dg(x)$. -/
theorem hasFDerivAt_sum_comp_scaleLast_sub (a l : Fin m → ℝ)
    {g : EuclideanSpace ℝ (Fin (d + 1)) → F} (hg : ContDiff ℝ 1 g)
    (x : EuclideanSpace ℝ (Fin (d + 1))) :
    HasFDerivAt (fun x ↦ ∑ j, a j • g (scaleLast (l j) x) - g x)
      (∑ j, a j • (fderiv ℝ g (scaleLast (l j) x)).comp (scaleLast (l j)) - fderiv ℝ g x) x := by
  refine HasFDerivAt.sub (HasFDerivAt.fun_sum fun j _ ↦ HasFDerivAt.const_smul ?_ (a j))
    (hg.differentiable one_ne_zero x).hasFDerivAt
  exact (hg.differentiable one_ne_zero (scaleLast (l j) x)).hasFDerivAt.comp x
    (scaleLast (l j)).hasFDerivAt

/-- If $g$ is of class $C^1$, the correction $\sum_j a_j\, g \circ S_{\lambda_j} - g$ is of class
$C^1$. -/
theorem contDiff_sum_comp_scaleLast_sub (a l : Fin m → ℝ)
    {g : EuclideanSpace ℝ (Fin (d + 1)) → F} (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 fun x ↦ ∑ j, a j • g (scaleLast (l j) x) - g x :=
  (ContDiff.sum fun j _ ↦ (hg.comp (scaleLast (l j)).contDiff).const_smul (a j)).sub hg

/-- Let $\sum_j a_j = 1$, let $g : \mathbb{R}^{d+1} \to F$ be of class $C^1$, and let
$r \in \mathbb{R}$. Then on the cylinder $Q_r$ the higher-order reflection $P_a g$ has the
reflected derivative `higherReflectionFDeriv a l (fderiv ℝ g)` as weak derivative.

The proof writes $P_a g = g + 1_{\{x_N < 0\}} G$ with
$G = \sum_j a_j\, g \circ S_{\lambda_j} - g$. The function $G$ vanishes on the hyperplane,
because $S_{\lambda_j}$ fixes it and $\sum_j a_j = 1$, and the gluing lemma
`hasWeakFDerivOn_indicator_lowerHalf_of_contDiff` applies. The statement needs no hypothesis on
the scales. -/
theorem hasWeakFDerivOn_higherReflection_of_contDiff {a l : Fin m → ℝ} (ha : ∑ j, a j = 1)
    {g : EuclideanSpace ℝ (Fin (d + 1)) → F} (hg : ContDiff ℝ 1 g) (r : ℝ) :
    HasWeakFDerivOn (higherReflection a l g) (higherReflectionFDeriv a l (fderiv ℝ g))
      (cylinder d r) volume := by
  obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin (d + 1)) → F,
    G = fun x ↦ ∑ j, a j • g (scaleLast (l j) x) - g x := ⟨_, rfl⟩
  have hGs : ContDiff ℝ 1 G := by rw [hG]; exact contDiff_sum_comp_scaleLast_sub a l hg
  have hG0 : ∀ x, x (Fin.last d) = 0 → G x = 0 := by
    intro x hx
    rw [hG]
    simp only
    simp_rw [scaleLast_of_apply_last_eq_zero _ hx, ← Finset.sum_smul, ha, one_smul, sub_self]
  have hGd : ∀ x, fderiv ℝ G x
      = ∑ j, a j • (fderiv ℝ g (scaleLast (l j) x)).comp (scaleLast (l j)) - fderiv ℝ g x := by
    intro x
    rw [hG]
    exact (hasFDerivAt_sum_comp_scaleLast_sub a l hg x).fderiv
  have h1 := hasWeakFDerivOn_indicator_lowerHalf_of_contDiff hGs hG0 (isCompact_closure_cylinder r)
    (convex_cylinder r) (fun x hx ↦ scaleLast_mem_cylinder (by simp) hx)
  have h2 : HasWeakFDerivOn g (fderiv ℝ g) (cylinder d r) volume := by
    have := hg.contDiffOn.hasWeakIteratedFDerivOn (Ω := cylinder d r) (μ := volume) (m := 1) le_rfl
    refine this.congr_ae (EventuallyEq.refl _ _) (Eventually.of_forall fun x ↦ ?_)
    ext m
    simp [iteratedFDeriv_one_apply]
  have h3 := (h2 : HasWeakIteratedFDerivOn 1 g _ (cylinder d r) volume).add
    (h1 : HasWeakIteratedFDerivOn 1 _ _ (cylinder d r) volume)
  refine h3.congr_ae (Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
  · rw [higherReflection_eq_add_indicator a l g, hG]
  · simp only [Pi.add_apply, ← map_add]
    congr 1
    by_cases hx : x (Fin.last d) < 0
    · rw [Set.indicator_of_mem (show x ∈ {x : EuclideanSpace ℝ (Fin (d + 1)) |
          x (Fin.last d) < 0} from hx), higherReflectionFDeriv_of_neg a l hx, hGd]
      abel
    · rw [Set.indicator_of_notMem (show x ∉ {x : EuclideanSpace ℝ (Fin (d + 1)) |
          x (Fin.last d) < 0} from hx), higherReflectionFDeriv_of_nonneg a l (not_lt.1 hx),
            add_zero]

/-- Let the scales $\lambda$ and the open set $V$ satisfy `IsReflectionSet`, and let $f_i$ be almost
everywhere strongly measurable on $V_+$. If $\|f_i\|_{L^1(V_+)} \to 0$, then
$\|P_a f_i\|_{L^1(V)} \to 0$. -/
theorem tendsto_eLpNorm_higherReflection_of_tendsto {a l : Fin m → ℝ} (hl : IsReflectionSet l V)
    {f : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → F}
    (hf : ∀ i, AEStronglyMeasurable (f i)
      (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set (EuclideanSpace ℝ (Fin (d +
        1))))))
    (h : Tendsto (fun i ↦ eLpNorm (f i) 1
      (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set (EuclideanSpace ℝ (Fin (d +
        1)))))) atTop (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (higherReflection a l (f i)) 1
      (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1)))))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hCf, -, -⟩ := hl.exists_facts (F := F) a 1
  have h' := ENNReal.Tendsto.const_mul h (Or.inr hC)
  rw [mul_zero] at h'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h' (fun _ ↦ zero_le)
    fun i ↦ (hCf (f i) (hf i)).2

/-- Let the scales $\lambda$ and the open set $V$ satisfy `IsReflectionSet`, and let $D_i$ be fields
of linear maps, almost everywhere strongly measurable on $V_+$. If $\|D_i\|_{L^1(V_+)} \to 0$,
then the reflected derivatives $\tilde D_i$ = `higherReflectionFDeriv a l (D i)` satisfy
$\|\tilde D_i\|_{L^1(V)} \to 0$. -/
theorem tendsto_eLpNorm_higherReflectionFDeriv_of_tendsto {a l : Fin m → ℝ}
    (hl : IsReflectionSet l V)
    {D : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F}
    (hD : ∀ i, AEStronglyMeasurable (D i)
      (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set (EuclideanSpace ℝ (Fin (d +
        1))))))
    (h : Tendsto (fun i ↦ eLpNorm (D i) 1
      (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V : Set (EuclideanSpace ℝ (Fin (d +
        1)))))) atTop (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (higherReflectionFDeriv a l (D i)) 1
      (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1)))))) atTop (𝓝 0) := by
  obtain ⟨C, hC, -, hCD, -⟩ := hl.exists_facts (F := F) a 1
  have h' := ENNReal.Tendsto.const_mul h (Or.inr hC)
  rw [mul_zero] at h'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h' (fun _ ↦ zero_le)
    fun i ↦ (hCD (D i) (hD i)).2

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Let $V$ be an open set of finite measure and $1 \le p \le \infty$. If $w$ has the weak
derivative $Dw$ on $V$ and both $w$ and $Dw$ lie in $L^p(V)$, then $w \in W^{1,1}(V)$ in the
formulation `MemSobolev` with iterated derivatives. -/
theorem memSobolev_one_of_hasWeakFDerivOn {V : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hVfin : volume (V : Set (EuclideanSpace ℝ (Fin (d + 1)))) ≠ ⊤)
    {w : EuclideanSpace ℝ (Fin (d + 1)) → F}
    {Dw : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F}
    (hw : HasWeakFDerivOn w Dw V volume)
    (hwp : MemLp w p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hDp : MemLp Dw p (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    MemSobolev w 1 1 V volume := by
  have hfin : IsFiniteMeasure (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hVfin⟩
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hw1 : MemLp w 1 (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hwp.mono_exponent hp
  have hD1 : MemLp Dw 1 (volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    hDp.mono_exponent hp
  refine ⟨hw1, fun n hn ↦ ?_⟩
  have hn' : n ≤ 1 := by exact_mod_cast hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn' with rfl | rfl
  · refine ⟨fun x ↦ (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
      (w x), hasWeakIteratedFDerivOn_zero (hw1.locallyIntegrableOn le_rfl), ?_⟩
    exact (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
      F).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hw1
  · refine ⟨fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
      (Dw x), hw, ?_⟩
    exact (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
      F).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hD1

variable [CompleteSpace F]

/-- Let $F$ be a real Banach space, $1 \le p \le \infty$ and $r \in \mathbb{R}$. Let
$a, \lambda \in \mathbb{R}^m$ with $\sum_j a_j = 1$ and $-1 \le \lambda_j < 0$ for every $j$.
Let $w \in L^p(Q_r^+; F)$ have the weak derivative $Dw \in L^p(Q_r^+)$ on $Q_r^+$. Then on $Q_r$
the higher-order reflection $P_a w$ has the weak derivative
$$D(P_a w)(x) = \begin{cases} Dw(x) & \text{if } x_N \ge 0, \\ \sum_j a_j\, Dw(S_{\lambda_j} x)
  \circ S_{\lambda_j} & \text{if } x_N < 0. \end{cases}$$

This is the analogue, for the reflection with several scales, of Lemma 9.2 of
[brezis2011functional]. The derivative is `higherReflectionFDeriv a l Dw`. The cancellation
across the interface that the even reflection has is lost here. The proof therefore approximates
the even reflection of $w$, which lies in $W^{1,1}(Q_r)$ by Lemma 9.2, on a smaller cylinder
$Q_{r'}$ by smooth functions $g_i$ (`MemSobolev.exists_seq_contDiff_tendsto_eLpNorm`), applies
`hasWeakFDerivOn_higherReflection_of_contDiff` to the $g_i$, and passes to the limit in
$L^1(Q_{r'})$. -/
theorem hasWeakFDerivOn_higherReflection {r : ℝ} {a l : Fin m → ℝ} (ha : ∑ j, a j = 1)
    (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j) {w : EuclideanSpace ℝ (Fin (d + 1)) → F}
    {Dw : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F}
    (hw : HasWeakFDerivOn w Dw (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume)
    (hwp : MemLp w p
      (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace
        ℝ (Fin (d + 1))))))
    (hDp : MemLp Dw p
      (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace
        ℝ (Fin (d + 1)))))) :
    HasWeakFDerivOn (higherReflection a l w) (higherReflectionFDeriv a l Dw) (cylinder d r)
      volume := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hv : ‖(single (Fin.last d) (1 : ℝ) : EuclideanSpace ℝ (Fin (d + 1)))‖ = 1 :=
    EuclideanSpace.norm_single_last_one
  have hV := hyperplaneReflection_image_cylinder (d := d) r
  have hQ : IsReflectionSet l (cylinder d r) := isReflectionSet_cylinder hl hl1 r
  have hQfin : volume (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ
    (Fin (d + 1)))) ≠ ⊤ :=
    ((measure_mono (posHalf_le _ _)).trans_lt (volume_cylinder_lt_top r)).ne
  -- Lemma 9.2 for the even reflection, at exponent one
  have hu1 : MemSobolev w 1 1 (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume :=
    memSobolev_one_of_hasWeakFDerivOn hQfin hw hwp hDp
  have hev : HasWeakFDerivOn (evenReflection (single (Fin.last d) (1 : ℝ)) w)
      (reflectFDeriv (single (Fin.last d) (1 : ℝ)) Dw) (cylinder d r) volume :=
    hw.evenReflection hv hV hp hwp hDp
  have hevs : MemSobolev (evenReflection (single (Fin.last d) (1 : ℝ)) w) 1 1 (cylinder d r)
      volume := hu1.evenReflection hv hV le_rfl
  -- local integrability of the reflected function and derivative
  obtain ⟨C, hC, hCf, hCD, -⟩ := hQ.exists_facts (F := F) a p
  have hRp : MemLp (higherReflection a l w) p
      (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    (hCf w hwp.aestronglyMeasurable).2.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) hwp)
  have hRDp : MemLp (higherReflectionFDeriv a l Dw) p
      (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    (hCD Dw hDp.aestronglyMeasurable).2.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) hDp)
  have hRl : LocallyIntegrableOn (higherReflection a l w) (cylinder d r) volume :=
    hRp.locallyIntegrableOn hp
  have hRDl : LocallyIntegrableOn (fun x ↦ (continuousMultilinearCurryFin1 ℝ
      (EuclideanSpace ℝ (Fin (d + 1))) F).symm (higherReflectionFDeriv a l Dw x))
      (cylinder d r) volume :=
    (hRDp.locallyIntegrableOn hp).comp_continuousLinearMap
      (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
        F).symm.toContinuousLinearEquiv.toContinuousLinearMap
  -- locality: it suffices to prove the identity on the cylinders `Q_{r'}`, `r' < r`
  refine HasWeakIteratedFDerivOn.of_forall_isCompact_closure_subset hRl hRDl fun Ω' hΩ'c hΩ'Q ↦ ?_
  obtain ⟨r', hr', hΩ'r'⟩ := exists_lt_subset_cylinder hΩ'c hΩ'Q
  refine HasWeakIteratedFDerivOn.mono ?_ (subset_closure.trans hΩ'r')
  have hQ' : IsReflectionSet l (cylinder d r') := isReflectionSet_cylinder hl hl1 r'
  have hQ'Q : (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r') : Set (EuclideanSpace ℝ (Fin
    (d + 1))))
      ⊆ (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d +
        1)))) := fun x hx ↦
    mem_posHalf_last_iff.2 ⟨closure_cylinder_subset_cylinder hr'
      (subset_closure (mem_posHalf_last_iff.1 hx).1), (mem_posHalf_last_iff.1 hx).2⟩
  -- the smooth approximants of `u^⋆` on `Q_{r'}`
  obtain ⟨g, hgs, hg0, hg1⟩ := hevs.exists_seq_contDiff_tendsto_eLpNorm le_rfl ENNReal.one_ne_top
    (cylinder d r').isOpen (isCompact_closure_cylinder r') (closure_cylinder_subset_cylinder hr')
  have hg1' := hg1 1 (by simp)
  -- the smooth approximants satisfy the identity
  have hGw : ∀ i, HasWeakIteratedFDerivOn 1 (higherReflection a l (g i))
      (fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
        (higherReflectionFDeriv a l (fderiv ℝ (g i)) x)) (cylinder d r') volume := fun i ↦
    hasWeakFDerivOn_higherReflection_of_contDiff ha ((hgs i).of_le (by simp)) r'
  refine hasWeakIteratedFDerivOn_of_tendsto_eLpNorm_one hGw
    (hRl.mono_set (subset_closure.trans (closure_cylinder_subset_cylinder hr')))
    (hRDl.mono_set (subset_closure.trans (closure_cylinder_subset_cylinder hr'))) ?_ ?_
  · -- `P g_i → P u` in `L^1(Q_{r'})`
    have hsub : ∀ i, higherReflection a l (g i) - higherReflection a l w
        = higherReflection a l (g i - w) := fun i ↦ (higherReflection_sub a l _ _).symm
    simp only [hsub]
    refine tendsto_eLpNorm_higherReflection_of_tendsto hQ'
      (fun i ↦ (hgs i).continuous.aestronglyMeasurable.sub
        (hwp.aestronglyMeasurable.mono_measure (Measure.restrict_mono hQ'Q le_rfl))) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg0 (fun _ ↦ zero_le)
      fun i ↦ ?_
    calc eLpNorm (g i - w) 1 (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ))
          (cylinder d r') : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        = eLpNorm (g i - evenReflection (single (Fin.last d) (1 : ℝ)) w) 1
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r') : Set
            (EuclideanSpace ℝ (Fin (d + 1))))) := by
          refine eLpNorm_congr_ae ?_
          filter_upwards [ae_restrict_mem (posHalf _ (cylinder d r')).isOpen.measurableSet]
            with x hx
          rw [Pi.sub_apply, Pi.sub_apply, evenReflection_of_nonneg]
          rw [EuclideanSpace.inner_single_last_one]
          exact (mem_posHalf_last_iff.1 hx).2.le
      _ ≤ eLpNorm (g i - evenReflection (single (Fin.last d) (1 : ℝ)) w) 1
          (volume.restrict (cylinder d r' : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono (posHalf_le _ _) le_rfl)
  · -- the derivatives converge in `L^1(Q_{r'})`
    have hsub : ∀ i, (fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
          F).symm (higherReflectionFDeriv a l (fderiv ℝ (g i)) x))
        - (fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
          (higherReflectionFDeriv a l Dw x))
        = fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
          (higherReflectionFDeriv a l (fderiv ℝ (g i) - Dw) x) := fun i ↦ by
      funext x
      rw [Pi.sub_apply, ← map_sub, higherReflectionFDeriv_sub, Pi.sub_apply]
    simp only [hsub]
    obtain ⟨C', hC'0, hC'f, hC'D, -⟩ := hQ'.exists_facts (F := F) a 1
    have hmeasD : ∀ i, AEStronglyMeasurable (fderiv ℝ (g i) - Dw)
        (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r') : Set
          (EuclideanSpace ℝ (Fin (d + 1))))) :=
      fun i ↦ ((hgs i).continuous_fderiv (by simp)).aestronglyMeasurable.sub
        (hDp.aestronglyMeasurable.mono_measure (Measure.restrict_mono hQ'Q le_rfl))
    have hiso : ∀ i, eLpNorm (fun x ↦ (continuousMultilinearCurryFin1 ℝ
          (EuclideanSpace ℝ (Fin (d + 1))) F).symm (higherReflectionFDeriv a l
            (fderiv ℝ (g i) - Dw) x)) 1 (volume.restrict (cylinder d r' : Set (EuclideanSpace ℝ
              (Fin (d + 1)))))
        = eLpNorm (higherReflectionFDeriv a l (fderiv ℝ (g i) - Dw)) 1
          (volume.restrict (cylinder d r' : Set (EuclideanSpace ℝ (Fin (d + 1))))) := fun i ↦ by
      refine eLpNorm_congr_enorm_ae ((continuousMultilinearCurryFin1 ℝ
        (EuclideanSpace ℝ (Fin (d + 1))) F).symm.continuous.comp_aestronglyMeasurable
        (hC'D _ (hmeasD i)).1) (hC'D _ (hmeasD i)).1 (Eventually.of_forall fun x ↦ ?_)
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, LinearIsometryEquiv.nnnorm_map]
    simp only [hiso]
    refine tendsto_eLpNorm_higherReflectionFDeriv_of_tendsto hQ' hmeasD ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg1' (fun _ ↦ zero_le)
      fun i ↦ ?_
    have hae : ∀ᵐ x ∂volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r') : Set
      (EuclideanSpace ℝ (Fin (d + 1)))),
        ‖(fderiv ℝ (g i) - Dw) x‖ₑ = ‖(iteratedFDeriv ℝ 1 (g i)
          - weakIteratedFDeriv 1 (evenReflection (single (Fin.last d) (1 : ℝ)) w) (cylinder d r)
            volume) x‖ₑ := by
      filter_upwards [ae_restrict_mem (posHalf _ (cylinder d r')).isOpen.measurableSet,
        ae_restrict_of_ae hev.weakIteratedFDeriv_ae_eq] with x hx hx'
      rw [Pi.sub_apply, Pi.sub_apply, hx' (closure_cylinder_subset_cylinder hr'
        (subset_closure (mem_posHalf_last_iff.1 hx).1)), reflectFDeriv_of_nonneg]
      · rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
        congr 1
        have e : iteratedFDeriv ℝ 1 (g i) x = (continuousMultilinearCurryFin1 ℝ
            (EuclideanSpace ℝ (Fin (d + 1))) F).symm (fderiv ℝ (g i) x) := by
          ext m
          simp [iteratedFDeriv_one_apply]
        rw [e, ← map_sub, LinearIsometryEquiv.nnnorm_map]
      · rw [EuclideanSpace.inner_single_last_one]
        exact (mem_posHalf_last_iff.1 hx).2.le
    calc eLpNorm (fderiv ℝ (g i) - Dw) 1
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r') : Set
            (EuclideanSpace ℝ (Fin (d + 1)))))
        ≤ eLpNorm (iteratedFDeriv ℝ 1 (g i) - weakIteratedFDeriv 1
            (evenReflection (single (Fin.last d) (1 : ℝ)) w) (cylinder d r) volume) 1
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r') : Set
            (EuclideanSpace ℝ (Fin (d + 1))))) :=
          eLpNorm_mono_enorm_ae (hmeasD i) (hae.mono fun x hx ↦ hx.le)
      _ ≤ eLpNorm (iteratedFDeriv ℝ 1 (g i) - weakIteratedFDeriv 1
            (evenReflection (single (Fin.last d) (1 : ℝ)) w) (cylinder d r) volume) 1
          (volume.restrict (cylinder d r' : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono (posHalf_le _ _) le_rfl)

end ReflectionIdentity

/-! ### The higher-order reflection at order one: membership and the bundled operator -/

section ReflectionMembership

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
  {V : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {a l : Fin m → ℝ}

/-- Let the scales $\lambda$ and the open set $V$ satisfy `IsReflectionSet`. If $f = g$ almost
everywhere on $V_+$, then $P_a f = P_a g$ almost everywhere on $V$. -/
theorem IsReflectionSet.higherReflection_congr_ae (hV : IsReflectionSet l V) (a : Fin m → ℝ)
    {f g : EuclideanSpace ℝ (Fin (d + 1)) → F}
    (h : f =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) V :
      Set (EuclideanSpace ℝ (Fin (d + 1))))] g) :
    _root_.higherReflection a l f =ᵐ[volume.restrict (V : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      _root_.higherReflection a l g := by
  obtain ⟨-, -, -, -, hP⟩ := hV.exists_facts (F := F) a 1
  have h1 : ∀ᵐ x ∂volume, x ∈ (posHalf (single (Fin.last d) (1 : ℝ)) V :
      Set (EuclideanSpace ℝ (Fin (d + 1)))) → f x = g x :=
    (ae_restrict_iff' (posHalf _ V).isOpen.measurableSet).1 h
  have h2 : ∀ᵐ x ∂volume, x ∈ negHalf V → ∀ j, f (scaleLast (l j) x) = g (scaleLast (l j) x) :=
    (ae_restrict_iff' isOpen_negHalf'.measurableSet).1 (hP h)
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet, ae_restrict_of_ae ae_apply_last_ne_zero,
    ae_restrict_of_ae h1, ae_restrict_of_ae h2] with x hxV hx hx1 hx2
  rcases lt_or_gt_of_ne hx with h | h
  · rw [higherReflection_of_neg a l h, higherReflection_of_neg a l h]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hx2 ⟨hxV, h⟩ j]
  · rw [higherReflection_of_nonneg a l h.le, higherReflection_of_nonneg a l h.le]
    exact hx1 (mem_posHalf_last_iff.2 ⟨hxV, h⟩)

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ (EuclideanSpace ℝ (Fin (d + 1)))}
  [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {r : ℝ}

/-- Let $F$ be a real Banach space, $1 \le p \le \infty$ and $r \in \mathbb{R}$. Let
$a, \lambda \in \mathbb{R}^m$ with $\sum_j a_j = 1$ and $-1 \le \lambda_j < 0$ for every $j$. If
$u \in W^{1,p}(Q_r^+; F)$, then $P_a u \in W^{1,p}(Q_r; F)$.

This is the analogue of Lemma 9.2 of [brezis2011functional] for the reflection with several
scales. Here $W^{1,p}$ is the formulation `MemSobolev` with iterated derivatives. -/
theorem MemSobolev.higherReflection (ha : ∑ j, a j = 1) (hl : ∀ j, l j < 0)
    (hl1 : ∀ j, -1 ≤ l j) {u : EuclideanSpace ℝ (Fin (d + 1)) → F}
    (hu : MemSobolev u 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    MemSobolev (_root_.higherReflection a l u) 1 p (cylinder d r) volume := by
  obtain ⟨w, hw, hwp⟩ := hu.exists_hasWeakIteratedFDerivOn (n := 1) le_rfl
  obtain ⟨e, he⟩ : ∃ e : (EuclideanSpace ℝ (Fin (d + 1)) [×1]→L[ℝ] F) ≃ₗᵢ[ℝ]
      (EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F),
    e = continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F := ⟨_, rfl⟩
  have hw' : HasWeakFDerivOn u (fun x ↦ e (w x))
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume := by
    unfold HasWeakFDerivOn
    rw [he]
    simpa using hw
  have hwp' : MemLp (fun x ↦ e (w x)) p (volume.restrict
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d +
        1))))) :=
    e.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hwp
  have hid := hasWeakFDerivOn_higherReflection ha hl hl1 hw' hu.memLp hwp'
  obtain ⟨C, hC, hCf, hCD, -⟩ := (isReflectionSet_cylinder hl hl1 r).exists_facts (F := F) a p
  have hup : MemLp (_root_.higherReflection a l u) p
      (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    (hCf u hu.memLp.aestronglyMeasurable).2.trans_lt
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) hu.memLp)
  have hWp : MemLp (higherReflectionFDeriv a l fun x ↦ e (w x)) p
      (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    (hCD _ hwp'.aestronglyMeasurable).2.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) hwp')
  refine ⟨hup, fun n hn ↦ ?_⟩
  have hn' : n ≤ 1 := by exact_mod_cast hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn' with rfl | rfl
  · refine ⟨fun x ↦ (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
      (_root_.higherReflection a l u x), hasWeakIteratedFDerivOn_zero hid.locallyIntegrableOn, ?_⟩
    exact (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
      F).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hup
  · refine ⟨fun x ↦ (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1))) F).symm
      (higherReflectionFDeriv a l (fun x ↦ e (w x)) x), hid, ?_⟩
    exact (continuousMultilinearCurryFin1 ℝ (EuclideanSpace ℝ (Fin (d + 1)))
      F).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hWp

/-- Let $\sum_j a_j = 1$ and $-1 \le \lambda_j < 0$ for every $j$, and let $b$ be a basis of
$\mathbb{R}^{d+1}$. If $u \in W^{1,p}(Q_r^+; F)$ in the multi-index formulation
`MemSobolevMultiIndex` over $b$, then $P_a u \in W^{1,p}(Q_r; F)$ in the same formulation. -/
theorem MemSobolevMultiIndex.higherReflection (ha : ∑ j, a j = 1) (hl : ∀ j, l j < 0)
    (hl1 : ∀ j, -1 ≤ l j) {u : EuclideanSpace ℝ (Fin (d + 1)) → F}
    (hu : MemSobolevMultiIndex b u 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r))
      volume) :
    MemSobolevMultiIndex b (_root_.higherReflection a l u) 1 p (cylinder d r) volume :=
  (hu.memSobolev.higherReflection ha hl hl1).memSobolevMultiIndex

namespace SobolevMultiIndex

variable (ha : ∑ j, a j = 1) (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j)
include ha hl hl1

/-- The higher-order reflection on the Sobolev spaces: for $\sum_j a_j = 1$ and
$-1 \le \lambda_j < 0$, the element of $W^{1,p}(Q_r)$ whose function is $P_a u$, for
$u \in W^{1,p}(Q_r^+)$.

The element is chosen by `MemSobolevMultiIndex.higherReflection`. It is linear and bounded, and
`SobolevMultiIndex.higherReflectionL` is the bundled bounded linear map. -/
def higherReflection (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    SobolevMultiIndex F b 1 p (cylinder d r) volume :=
  ((memSobolevMultiIndex u).higherReflection ha hl hl1).exists_sobolevMultiIndex.choose

/-- The function of `SobolevMultiIndex.higherReflection ha hl hl1 u` is $P_a u$ almost everywhere on
$Q_r$. -/
theorem fn_higherReflection (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    fn (higherReflection ha hl hl1 u)
      =ᵐ[volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        _root_.higherReflection a l (fn u) :=
  ((memSobolevMultiIndex u).higherReflection ha hl hl1).exists_sobolevMultiIndex.choose_spec

/-- On $Q_r^+$, the function of `SobolevMultiIndex.higherReflection ha hl hl1 u` is almost
everywhere the function of $u$. -/
theorem fn_higherReflection_restrict (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    fn (higherReflection ha hl hl1 u)
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))] fn u := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (posHalf_le _ _)
    (fn_higherReflection ha hl hl1 u),
    ae_restrict_mem (posHalf _ (cylinder d r)).isOpen.measurableSet] with x hx hxV
  rw [hx, higherReflection_of_nonneg a l (mem_posHalf_last_iff.1 hxV).2.le]

/-- `SobolevMultiIndex.higherReflection` is additive. -/
theorem higherReflection_add (u w : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    higherReflection ha hl hl1 (u + w)
      = higherReflection ha hl hl1 u + higherReflection ha hl hl1 w := by
  refine ext_of_fn_ae_eq ((fn_higherReflection ha hl hl1 (u + w)).trans (EventuallyEq.trans ?_
    (fn_add _ _).symm))
  refine ((isReflectionSet_cylinder hl hl1 r).higherReflection_congr_ae a (fn_add u w)).trans ?_
  rw [_root_.higherReflection_add]
  exact ((fn_higherReflection ha hl hl1 u).add (fn_higherReflection ha hl hl1 w)).symm

/-- `SobolevMultiIndex.higherReflection` commutes with real scalar multiplication. -/
theorem higherReflection_smul (c : ℝ) (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    higherReflection ha hl hl1 (c • u) = c • higherReflection ha hl hl1 u := by
  refine ext_of_fn_ae_eq ((fn_higherReflection ha hl hl1 (c • u)).trans (EventuallyEq.trans ?_
    (fn_smul _ _).symm))
  refine ((isReflectionSet_cylinder hl hl1 r).higherReflection_congr_ae a (fn_smul c u)).trans ?_
  rw [_root_.higherReflection_smul]
  exact ((fn_higherReflection ha hl hl1 u).const_smul c).symm

/-- Let $u \in W^{1,p}(Q_r^+)$, and let $w \in L^p(Q_r^+)$ be a weak derivative of the function of
$u$ on $Q_r^+$. Then for every index $i$ the weak partial derivative of
`SobolevMultiIndex.higherReflection ha hl hl1 u` along the basis vector $b_i$ is
$x \mapsto \tilde w(x)(b_i)$, almost everywhere on $Q_r$, where $\tilde w$ is the reflected
derivative `higherReflectionFDeriv a l w`. -/
theorem weakDeriv_higherReflection_single (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume)
    {w : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] F}
    (hw : HasWeakFDerivOn (fn u) w (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume)
    (hwp : MemLp w p (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
      Set (EuclideanSpace ℝ (Fin (d + 1)))))) (i : ι) :
    weakDeriv (higherReflection ha hl hl1 u) (MultiIndexLE.single i)
      =ᵐ[volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ higherReflectionFDeriv a l w x (b i) := by
  have h1 := (hasWeakIteratedLineDerivOn (higherReflection ha hl hl1 u)
    (MultiIndexLE.single i)).of_perm (multiIndexTuple_single_perm (b : ι → _) i)
  have h2 := (((hasWeakFDerivOn_higherReflection ha hl hl1 hw (memLp u) hwp) :
    HasWeakIteratedFDerivOn 1 _ _ (cylinder d r) volume).lineDeriv ![b i]).congr_ae
    (fn_higherReflection ha hl hl1 u).symm (EventuallyEq.refl _ _)
  filter_upwards [(ae_restrict_iff' (cylinder d r).isOpen.measurableSet).2 (h1.ae_eq h2)] with x hx
  simpa using hx

/-- `SobolevMultiIndex.higherReflection` is bounded: there is a constant $C$ with $\|P_a
u\|_{W^{1,p}(Q_r)} \le C \|u\|_{W^{1,p}(Q_r^+)}$ for every $u$. -/
theorem exists_norm_higherReflection_le :
    ∃ C : ℝ, ∀ u : SobolevMultiIndex F b 1 p
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume,
      ‖higherReflection ha hl hl1 u‖ ≤ C * ‖u‖ := by
  obtain ⟨C₀, hC₀, hCf, hCD, -⟩ := (isReflectionSet_cylinder hl hl1 r).exists_facts (F := F) a p
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = Fintype.card ι • ‖b.equivFunL.toContinuousLinearMap‖ :=
    ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = ∑ i, ‖b i‖ := ⟨_, rfl⟩
  have hMb0 : 0 ≤ Mb := by rw [hMb]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞, B = ENNReal.ofReal Mb * (C₀ * ENNReal.ofReal Cb) := ⟨_, rfl⟩
  have hB' : B ≠ ⊤ := by
    rw [hB]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top)
  refine ⟨_, fun u ↦ norm_le_mul_norm_of_eLpNorm_le (higherReflection ha hl hl1 u) u hC₀ hB'
    ?_ fun i ↦ ?_⟩
  · rw [eLpNorm_congr_ae (fn_higherReflection ha hl hl1 u)]
    exact (hCf (fn u) (memLp u).aestronglyMeasurable).2
  obtain ⟨w, hw, hwp, -, hwn⟩ := exists_hasWeakFDerivOn_fn u
  rw [← hCb] at hwn
  have h1 : eLpNorm (weakDeriv (higherReflection ha hl hl1 u) (MultiIndexLE.single i)) p
      (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      ≤ ENNReal.ofReal Mb * eLpNorm (higherReflectionFDeriv a l w) p
        (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Lp.memLp _).aestronglyMeasurable ?_ p
    filter_upwards [weakDeriv_higherReflection_single ha hl hl1 u hw hwp i] with x hx
    rw [hx, hMb]
    calc ‖higherReflectionFDeriv a l w x (b i)‖ ≤ ‖higherReflectionFDeriv a l w x‖ * ‖b i‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖higherReflectionFDeriv a l w x‖ * ∑ j, ‖b j‖ := by
          gcongr
          exact Finset.single_le_sum (f := fun j ↦ ‖b j‖) (fun _ _ ↦ norm_nonneg _)
            (Finset.mem_univ i)
      _ = (∑ j, ‖b j‖) * ‖higherReflectionFDeriv a l w x‖ := mul_comm _ _
  calc eLpNorm (weakDeriv (higherReflection ha hl hl1 u) (MultiIndexLE.single i)) p
        (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      ≤ ENNReal.ofReal Mb * (C₀ * (ENNReal.ofReal Cb
        * ∑ j, eLpNorm (weakDeriv u (MultiIndexLE.single j)) p
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
            Set (EuclideanSpace ℝ (Fin (d + 1))))))) := by
        refine h1.trans ?_
        gcongr
        exact (hCD w hwp.aestronglyMeasurable).2.trans (by gcongr)
    _ = B * ∑ j, eLpNorm (weakDeriv u (MultiIndexLE.single j)) p
          (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
            Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
        rw [hB]; ring

variable (F b p) in
/-- The higher-order reflection as a linear map $W^{1,p}(Q_r^+) \to W^{1,p}(Q_r)$. -/
def higherReflectionₗ :
    SobolevMultiIndex F b 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume →ₗ[ℝ]
      SobolevMultiIndex F b 1 p (cylinder d r) volume where
  toFun := higherReflection ha hl hl1
  map_add' := higherReflection_add ha hl hl1
  map_smul' := higherReflection_smul ha hl hl1

variable (F b p) in
/-- The **higher-order reflection as a bounded linear map** $W^{1,p}(Q_r^+) \to W^{1,p}(Q_r)$,
$u \mapsto P_a u$, for coefficients with $\sum_j a_j = 1$ and scales with
$-1 \le \lambda_j < 0$. Its function is $P_a u$ (`SobolevMultiIndex.fn_higherReflectionL`), it
equals $u$ on $Q_r^+$ (`SobolevMultiIndex.fn_higherReflectionL_restrict`), and its $L^p(Q_r)$
norm is at most a constant times $\|u\|_{L^p(Q_r^+)}$
(`SobolevMultiIndex.exists_eLpNorm_fn_higherReflectionL_le`).

It replaces the even reflection `SobolevEuclidean.cubeReflectL` in the chart-local step of the
proof of the extension theorem, when the Vandermonde conditions of higher order are imposed on
$a$. -/
def higherReflectionL :
    SobolevMultiIndex F b 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume →L[ℝ]
      SobolevMultiIndex F b 1 p (cylinder d r) volume :=
  (higherReflectionₗ F b p ha hl hl1).mkContinuousOfExistsBound
    (exists_norm_higherReflection_le ha hl hl1)

/-- `SobolevMultiIndex.higherReflectionL` applied to $u$ is
`SobolevMultiIndex.higherReflection ha hl hl1 u`. -/
@[simp]
theorem higherReflectionL_apply (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    higherReflectionL F b p ha hl hl1 u = higherReflection ha hl hl1 u :=
  rfl

/-- The function of `SobolevMultiIndex.higherReflectionL F b p ha hl hl1 u` is $P_a u$ almost
everywhere on $Q_r$. -/
theorem fn_higherReflectionL (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    fn (higherReflectionL F b p ha hl hl1 u)
      =ᵐ[volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        _root_.higherReflection a l (fn u) :=
  fn_higherReflection ha hl hl1 u

/-- On $Q_r^+$, the function of `SobolevMultiIndex.higherReflectionL F b p ha hl hl1 u` is almost
everywhere the function of $u$. -/
theorem fn_higherReflectionL_restrict (u : SobolevMultiIndex F b 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    fn (higherReflectionL F b p ha hl hl1 u)
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))] fn u :=
  fn_higherReflection_restrict ha hl hl1 u

/-- There is a finite constant $C$ such that $\|P_a u\|_{L^p(Q_r)} \le C \|u\|_{L^p(Q_r^+)}$ for
every $u \in W^{1,p}(Q_r^+)$, where $P_a u$ is the function of
`SobolevMultiIndex.higherReflectionL F b p ha hl hl1 u`. -/
theorem exists_eLpNorm_fn_higherReflectionL_le : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ u : SobolevMultiIndex F b 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume,
      eLpNorm (fn (higherReflectionL F b p ha hl hl1 u)) p
        (volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        ≤ C * eLpNorm (fn u) p (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ))
          (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  obtain ⟨C, hC, hCf, -, -⟩ := (isReflectionSet_cylinder hl hl1 r).exists_facts (F := F) a p
  refine ⟨C, hC, fun u ↦ ?_⟩
  rw [eLpNorm_congr_ae (fn_higherReflectionL ha hl hl1 u)]
  exact (hCf (fn u) (memLp u).aestronglyMeasurable).2

end SobolevMultiIndex

end ReflectionMembership

/-! ### The higher-order reflection at every order -/

section ReflectionHigher

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {m : ℕ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {r : ℝ} {a l : Fin m → ℝ}

open SobolevMultiIndex

/-- $S_\lambda$ on the standard basis vectors: $S_\lambda e_N = \lambda e_N$, and
$S_\lambda e_i = e_i$ for $i \ne N$. -/
theorem scaleLast_single (l : ℝ) (i : Fin (d + 1)) :
    scaleLast l (single i (1 : ℝ)) = if i = Fin.last d then l • single i 1 else single i 1 := by
  ext j
  by_cases hi : i = Fin.last d
  · subst hi
    by_cases hj : j = Fin.last d
    · subst hj; simp [scaleLast_apply]
    · simp [scaleLast_apply, hj]
  · by_cases hj : j = Fin.last d
    · subst hj; simp [scaleLast_apply, hi, Ne.symm hi]
    · simp [scaleLast_apply, hi, hj]

/-- Let $F$ be a real Banach space and $1 \le p \le \infty$. Let $\sum_j a_j = 1$ and
$-1 \le \lambda_j < 0$ for every $j$. Let $u \in W^{1,p}(Q_r^+; F)$ in the multi-index
formulation over the standard basis, and let $g$ be a weak derivative of $u$ along $e_i$ on
$Q_r^+$. Then on $Q_r$ the higher-order reflection $P_a u$ has a weak derivative along $e_i$,
namely
$$\partial_i (P_a u) = \begin{cases} P_a g & \text{if } i \ne N, \\ P_{a\lambda}\, g & \text{if
  } i = N, \end{cases}$$
where $P_{a\lambda}$ is the higher-order reflection with the coefficients $a_j \lambda_j$ and
the same scales.

The proof applies the chain rule to each term $a_j\, u \circ S_{\lambda_j}$: the map
$S_{\lambda_j}$ fixes $e_i$ for $i \ne N$ and scales $e_N$ by $\lambda_j$. In Lean the
coefficients $a_j \lambda_j$ are `a * l`. -/
theorem HasWeakIteratedLineDerivOn.higherReflection_single (ha : ∑ j, a j = 1)
    (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j) {u : EuclideanSpace ℝ (Fin (d + 1)) → F}
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis u 1 p
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume)
    (i : Fin (d + 1)) {g : EuclideanSpace ℝ (Fin (d + 1)) → F}
    (hg : HasWeakIteratedLineDerivOn ![single i (1 : ℝ)] u g
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume) :
    HasWeakIteratedLineDerivOn ![single i (1 : ℝ)] (_root_.higherReflection a l u)
      (_root_.higherReflection (if i = Fin.last d then a * l else a) l g) (cylinder d r) volume :=
        by
  obtain ⟨U, hU⟩ := hu.exists_sobolevMultiIndex
  obtain ⟨Dw, hDw, hDwp, hDwi, -⟩ := exists_hasWeakFDerivOn_fn U
  have hDw' : HasWeakFDerivOn u Dw (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume :=
    HasWeakIteratedFDerivOn.congr_ae hDw hU (EventuallyEq.refl _ _)
  have hDwg : (fun y ↦ Dw y (single i 1)) =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ))
      (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))] g := by
    have h1 := ((hasWeakIteratedLineDerivOn U (MultiIndexLE.single i)).of_perm
      (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis :
        Fin (d + 1) → EuclideanSpace ℝ (Fin (d + 1))) i)).congr_ae hU (EventuallyEq.refl _ _)
    rw [EuclideanSpace.basisFun_toBasis_apply] at h1
    have h2 := (ae_restrict_iff' (posHalf _ (cylinder d r)).isOpen.measurableSet).2 (h1.ae_eq hg)
    have h3 := hDwi i
    rw [EuclideanSpace.basisFun_toBasis_apply] at h3
    exact h3.trans h2
  have hid := hasWeakFDerivOn_higherReflection ha hl hl1 hDw' hu.memLp hDwp
  have h1 := (hid : HasWeakIteratedFDerivOn 1 _ _ (cylinder d r) volume).lineDeriv
    ![single i (1 : ℝ)]
  refine h1.congr_ae (EventuallyEq.refl _ _) ?_
  -- the pointwise identification of the derivative
  obtain ⟨-, -, -, -, hP⟩ := (isReflectionSet_cylinder hl hl1 r).exists_facts (F := F) a 1
  have hneg : ∀ᵐ x ∂volume, x ∈ negHalf (cylinder d r) →
      ∀ j, Dw (scaleLast (l j) x) (single i 1) = g (scaleLast (l j) x) :=
    (ae_restrict_iff' isOpen_negHalf'.measurableSet).1 (hP hDwg)
  have hpos : ∀ᵐ x ∂volume, x ∈ (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
      Set (EuclideanSpace ℝ (Fin (d + 1)))) → Dw x (single i 1) = g x :=
    (ae_restrict_iff' (posHalf _ (cylinder d r)).isOpen.measurableSet).1 hDwg
  filter_upwards [ae_restrict_mem (cylinder d r).isOpen.measurableSet,
    ae_restrict_of_ae ae_apply_last_ne_zero, ae_restrict_of_ae hneg, ae_restrict_of_ae hpos]
    with x hxV hx hx1 hx2
  simp only [continuousMultilinearCurryFin1_symm_apply, Matrix.cons_val_zero]
  rcases lt_or_gt_of_ne hx with h | h
  · rw [higherReflectionFDeriv_of_neg a l h, higherReflection_of_neg _ l h]
    simp only [sum_apply, smul_apply, ContinuousLinearMap.comp_apply, scaleLast_single]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs with hi
    · rw [map_smul, hx1 ⟨hxV, h⟩ j, Pi.mul_apply, mul_smul]
    · rw [hx1 ⟨hxV, h⟩ j]
  · rw [higherReflectionFDeriv_of_nonneg a l h.le, higherReflection_of_nonneg _ l h.le]
    exact hx2 (mem_posHalf_last_iff.2 ⟨hxV, h⟩)

/-- The Vandermonde conditions one order lower for the coefficients $a_j \lambda_j$: if
$\sum_j a_j \lambda_j^i = 1$ for every $i < k + 1$, then
$\sum_j (a_j \lambda_j) \lambda_j^i = 1$ for every $i < k$. -/
theorem vandermonde_mul_of_succ {k : ℕ} (h : ∀ i < k + 1, ∑ j, a j * l j ^ i = 1) :
    ∀ i < k, ∑ j, (a * l) j * l j ^ i = 1 := fun i hi ↦ by
  have := h (i + 1) (by omega)
  rw [← this]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [Pi.mul_apply, pow_succ]; ring

/-- The **higher-order reflection preserves $W^{k,p}$**. Let $F$ be a real Banach space,
$1 \le p \le \infty$, $r \in \mathbb{R}$ and $k \in \mathbb{N}$. Let $-1 \le \lambda_j < 0$ for
every $j$, and let the coefficients $a$ satisfy the Vandermonde conditions
$$\sum_j a_j \lambda_j^i = 1 \qquad (i < k).$$
If $u \in W^{k,p}(Q_r^+; F)$, then $P_a u \in W^{k,p}(Q_r; F)$.

The result is stated in [brezis2011functional], Comments on Chapter 9, and in Lions and Magenes.
Here $W^{k,p}$ is the multi-index formulation `MemSobolevMultiIndex` over the standard basis,
and the statement holds for every $a$ at once, as the induction needs. For $k = 0$ there is no
condition on $a$. The proof is an induction on $k$ through `memSobolevMultiIndex_succ_iff`: the
tangential derivatives of $P_a u$ are $P_a(\partial_i u)$ and the normal one is
$P_{a\lambda}(\partial_N u)$ (`HasWeakIteratedLineDerivOn.higherReflection_single`), and the
coefficients $a_j \lambda_j$ satisfy the Vandermonde conditions of order $k - 1$
(`vandermonde_mul_of_succ`). -/
theorem MemSobolevMultiIndex.higherReflection_of_order (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j)
    (k : ℕ) : ∀ (a : Fin m → ℝ), (∀ i < k, ∑ j, a j * l j ^ i = 1) →
    ∀ {u : EuclideanSpace ℝ (Fin (d + 1)) → F},
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis u k p
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume →
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (_root_.higherReflection a l u) k p (cylinder d r) volume := by
  induction k with
  | zero =>
    intro a _ u hu
    rw [memSobolevMultiIndex_zero_iff] at hu ⊢
    obtain ⟨C, hC, hCf, -, -⟩ := (isReflectionSet_cylinder hl hl1 r).exists_facts (F := F) a p
    exact (hCf u hu.aestronglyMeasurable).2.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC)
      hu)
  | succ k ih =>
    intro a ha u hu
    have ha0 : ∑ j, a j = 1 := by
      have := ha 0 (Nat.succ_pos k)
      simpa using this
    obtain ⟨hu0, hud⟩ := memSobolevMultiIndex_succ_iff.1 hu
    have hu1 : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis u 1 p
        (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume := hu.mono_order (by omega)
    refine memSobolevMultiIndex_succ_iff.2 ⟨ih a (fun i hi ↦ ha i (by omega)) hu0, fun i ↦ ?_⟩
    obtain ⟨g, hg, hgk⟩ := hud i
    rw [EuclideanSpace.basisFun_toBasis_apply] at hg ⊢
    refine ⟨_root_.higherReflection (if i = Fin.last d then a * l else a) l g,
      hg.higherReflection_single ha0 hl hl1 hu1 i, ?_⟩
    split_ifs with hi
    · exact ih (a * l) (vandermonde_mul_of_succ ha) hgk
    · exact ih a (fun i hi ↦ ha i (by omega)) hgk

/-- The **Vandermonde coefficients**. For every $k \in \mathbb{N}$ there are coefficients
$a_0, \dots, a_{k-1}$ such that
$$\sum_{j=0}^{k-1} a_j \Big( -\frac{1}{j+1} \Big)^i = 1 \qquad \text{for every } i < k.$$

The scales $\lambda_j = -1/(j+1)$ are distinct, so the Vandermonde matrix of these nodes is
invertible. The indices start at $0$. -/
theorem exists_vandermonde_coeffs (k : ℕ) :
    ∃ a : Fin k → ℝ, ∀ i < k, ∑ j, a j * (-((j : ℕ) + 1 : ℝ)⁻¹) ^ i = 1 := by
  obtain ⟨l, hl⟩ : ∃ l : Fin k → ℝ, l = fun j : Fin k ↦ -(((j : ℕ) : ℝ) + 1)⁻¹ := ⟨_, rfl⟩
  have hinj : Function.Injective l := by
    intro j j' h
    rw [hl] at h
    simp only [neg_inj, inv_inj, add_left_inj, Nat.cast_inj] at h
    exact Fin.ext h
  have hdet : (Matrix.vandermonde l).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.2 hinj
  refine ⟨((Matrix.vandermonde l).transpose)⁻¹.mulVec 1, fun i hi ↦ ?_⟩
  have key : (Matrix.vandermonde l).transpose.mulVec (((Matrix.vandermonde l).transpose)⁻¹.mulVec
    1) = 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mulVec]
  have := congrFun key ⟨i, hi⟩
  rw [Matrix.mulVec_apply_eq_sum, Pi.one_apply] at this
  refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans this
  have hlj : l j = -(((j : ℕ) : ℝ) + 1)⁻¹ := by rw [hl]
  rw [Matrix.transpose_apply, Matrix.vandermonde_apply, hlj, mul_comm]

end ReflectionHigher

/-! ### The chart-local extension on the cylinders $Q_r$ -/

section ChartCylinder

variable {d : ℕ} {n : WithTop ℕ∞} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- For $r < 1$, the upper half of $Q_r$ is $Q_r^+ = Q_r \cap Q_+$, where $Q_+$ is the upper half
`unitChartCubePos d` of the unit cylinder. -/
theorem coe_posHalf_cylinder_eq_inter {r : ℝ} (hr : r < 1) :
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))
      = (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ unitChartCubePos d := by
  ext x
  rw [mem_posHalf_last_iff, mem_inter_iff, mem_unitChartCubePos]
  exact ⟨fun h ↦ ⟨h.1, cylinder_subset_unitChartCube hr.le h.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩

namespace ContDiffChart

variable (c : ContDiffChart n (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) {r : ℝ} (hr : r < 1)
include hr

/-- For a chart $H : Q \to U$ with inverse $H^{-1}$ and $r < 1$, the image of the cylinder is
$H(Q_r) = U \cap (H^{-1})^{-1}(Q_r)$. -/
theorem image_cylinder_eq :
    c.toFun '' (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))
      = c.U ∩ c.invFun ⁻¹' (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyQ : y ∈ unitChartCube d := cylinder_subset_unitChartCube hr.le hy
    exact ⟨c.mapsTo hyQ, by rw [mem_preimage, c.invFun_toFun hyQ]; exact hy⟩
  · rintro ⟨hx, hx'⟩
    exact ⟨c.invFun x, hx', c.toFun_invFun hx⟩

/-- The image $U_r = H(Q_r)$ of the cylinder $Q_r$, $r < 1$, under a chart $H : Q \to U$ of
$\Omega$, as an open set. It is the open subset of $U$ on which the chart-local extension of
higher order lives.

The set is open because $H(Q_r) = U \cap (H^{-1})^{-1}(Q_r)$ and $H^{-1}$ is continuous on $U$.
The condition $r < 1$ gives $Q_r$ a compact closure inside the unit cylinder $Q$, on whose
closure the chart is of class $C^k$. -/
def opensUr : Opens (EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨c.toFun '' (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))), by
    rw [c.image_cylinder_eq hr]
    exact (c.contDiffOn_invFun.continuousOn.mono subset_closure).isOpen_inter_preimage c.isOpen_U
      (cylinder d r).isOpen⟩

/-- The underlying set of `c.opensUr hr` is $H(Q_r)$. -/
@[simp]
theorem coe_opensUr : (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))
    = c.toFun '' (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) := rfl

/-- $U_r \subseteq U$. -/
theorem opensUr_subset : (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ c.U :=
  fun _ ⟨_, hy, hxy⟩ ↦ hxy ▸ c.mapsTo (cylinder_subset_unitChartCube hr.le hy)

/-- The open set $U_r \cap \Omega$. -/
def opensInterr : Opens (EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨(c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ Ω, (c.opensUr hr).isOpen.inter Ω.isOpen⟩

/-- The underlying set of `c.opensInterr hr` is $U_r \cap \Omega$. -/
@[simp]
theorem coe_opensInterr : (c.opensInterr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))
    = (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ Ω := rfl

/-- $U_r \cap \Omega \subseteq \Omega$. -/
theorem opensInterr_le : c.opensInterr hr ≤ Ω := fun _ hx ↦ hx.2

/-- $U_r \cap \Omega \subseteq U_r$. -/
theorem opensInterr_le_opensUr : c.opensInterr hr ≤ c.opensUr hr := fun _ hx ↦ hx.1

/-- For $r < 1$, the chart maps the upper half of the cylinder onto $U_r \cap \Omega$:
$H(Q_r^+) = U_r \cap \Omega$. -/
theorem image_posHalf_cylinder :
    c.toFun '' (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
      Set (EuclideanSpace ℝ (Fin (d + 1)))) = c.opensInterr hr := by
  rw [coe_opensInterr, coe_opensUr, coe_posHalf_cylinder_eq_inter hr,
    c.injOn.image_inter (cylinder_subset_unitChartCube hr.le) unitChartCubePos_subset, c.image_pos,
    ← inter_assoc]
  congr 1
  exact inter_eq_left.2 (c.opensUr_subset hr)

/-- Let the chart be of class $C^n$ with $n \ge 1$, and let $r < 1$. Then there is a constant $M$
such that $H$, restricted to $Q_r^+$, is a $C^1$ diffeomorphism onto $U_r \cap \Omega$ with
inverse $H^{-1}$, and the derivatives of $H$ and $H^{-1}$ are bounded by $M$. -/
theorem exists_isDiffeoOnWithBoundedJacobian_posHalf_cylinder (hn : 1 ≤ n) :
    ∃ M, IsDiffeoOnWithBoundedJacobian c.toFun c.invFun
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))
      (c.opensInterr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))) M := by
  obtain ⟨M, hM⟩ := c.isDiffeoOnWithBoundedJacobian_pos hn Ω.isOpen
  have := hM.restrict (posHalf _ (cylinder d r)).isOpen (by
    rw [coe_posHalf_cylinder_eq_inter hr]; exact inter_subset_right)
  rw [c.image_posHalf_cylinder hr] at this
  exact ⟨M, this⟩

/-- Let the chart be of class $C^n$ with $n \ge 1$, and let $r < 1$. Then there is a constant $M$
such that $H$, restricted to $Q_r$, is a $C^1$ diffeomorphism onto $U_r$ with inverse $H^{-1}$,
and the derivatives of $H$ and $H^{-1}$ are bounded by $M$. -/
theorem exists_isDiffeoOnWithBoundedJacobian_cylinder (hn : 1 ≤ n) :
    ∃ M, IsDiffeoOnWithBoundedJacobian c.toFun c.invFun
      (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))
      (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))) M := by
  obtain ⟨M, hM⟩ := c.isDiffeoOnWithBoundedJacobian hn
  exact ⟨M, hM.restrict (cylinder d r).isOpen (cylinder_subset_unitChartCube hr.le)⟩

/-- For $r < 1$, the closure of $U_r$ lies in $H(\overline{Q_r})$, which is compact. -/
theorem closure_opensUr_subset_image_closure :
    closure (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))
      ⊆ c.toFun '' closure (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) := by
  have hc : IsCompact (c.toFun '' closure (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    (isCompact_closure_cylinder r).image_of_continuousOn
      (c.continuousOn.mono (closure_mono (cylinder_subset_unitChartCube hr.le)))
  exact closure_minimal (image_mono subset_closure) hc.isClosed

/-- For $r < 1$, the closure of $U_r$ lies in $U$. -/
theorem closure_opensUr_subset :
    closure (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ c.U :=
  (c.closure_opensUr_subset_image_closure hr).trans
    ((image_mono (closure_cylinder_subset_unitChartCube hr)).trans c.mapsTo.image_subset)

/-- For $r < 1$, the closure of $U_r$ is compact. -/
theorem isCompact_closure_opensUr :
    IsCompact (closure (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  ((isCompact_closure_cylinder r).image_of_continuousOn
    (c.continuousOn.mono (closure_mono (cylinder_subset_unitChartCube hr.le)))).of_isClosed_subset
    isClosed_closure (c.closure_opensUr_subset_image_closure hr)

omit hr in
/-- Every compact subset $K$ of $U$ lies in $U_r$ for some $r < 1$. -/
theorem exists_lt_one_subset_opensUr {K : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hK : IsCompact K)
    (hKU : K ⊆ c.U) : ∃ r, ∃ hr : r < 1, K ⊆ c.opensUr hr := by
  have hK' : IsCompact (c.invFun '' K) :=
    hK.image_of_continuousOn ((c.contDiffOn_invFun.continuousOn.mono subset_closure).mono hKU)
  obtain ⟨r, hr, hKr⟩ := exists_lt_one_subset_cylinder hK' (image_subset_iff.2 fun x hx ↦
    c.mapsTo_invFun (hKU hx))
  refine ⟨r, hr, fun x hx ↦ ⟨c.invFun x, hKr (mem_image_of_mem _ hx), c.toFun_invFun (hKU hx)⟩⟩

end ContDiffChart

end ChartCylinder

section ChartLocalMem

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {m : ℕ}
  {a l : Fin m → ℝ}

namespace SobolevEuclidean

/-- The chart-local extension preserves $W^{k,p}$, with the operators as variables. Let $r < 1$,
$-1 \le \lambda_j < 0$, and let $a$ satisfy the Vandermonde conditions
$\sum_j a_j \lambda_j^i = 1$ for $i < k$. Let $R : W^{1,p}(\Omega) \to W^{1,p}(\Omega_c)$,
$T_1 : W^{1,p}(\Omega_c) \to W^{1,p}(Q_r^+)$, $S : W^{1,p}(Q_r^+) \to W^{1,p}(Q_r)$ and
$T_2 : W^{1,p}(Q_r) \to W^{1,p}(U)$ be bounded linear maps whose functions are $Ru = u$ on
$\Omega_c \subseteq \Omega$, $T_1 v = v \circ H$, $S w = P_a w$ and $T_2 w = w \circ H^{-1}$,
almost everywhere. Let $H$ be a $C^1$ diffeomorphism with bounded Jacobians from $Q_r^+$ onto
$\Omega_c$ and from $Q_r$ onto $U$, with inverse $H^{-1}$, let $H$ be of class $C^k$ on the unit
cylinder $Q$, let $H^{-1}$ be of class $C^k$ on an open set $W$ that contains the closure of
$U$, and let the closure of $U$ be compact. If $u \in W^{1,p}(\Omega)$ and the function of $u$
lies in $W^{k,p}(\Omega)$, then the function of $T_2(S(T_1(Ru)))$ lies in $W^{k,p}(U)$.

The two transports preserve $W^{k,p}$ by `MemSobolevMultiIndex.comp_diffeoOn_of_order`, and the
reflection does by `MemSobolevMultiIndex.higherReflection_of_order`. -/
theorem chartExtend_mem_of_ops {r : ℝ} (hr : r < 1) (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j)
    {k : ℕ} {Ωc U : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    {H Hinv : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))} {M M' : ℝ}
    (R : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p Ωc)
    (T₁ : SobolevEuclidean (d + 1) 1 p Ωc →L[ℝ] SobolevEuclidean (d + 1) 1 p
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)))
    (S : SobolevEuclidean (d + 1) 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) →L[ℝ]
      SobolevEuclidean (d + 1) 1 p (cylinder d r))
    (T₂ : SobolevEuclidean (d + 1) 1 p (cylinder d r) →L[ℝ] SobolevEuclidean (d + 1) 1 p U)
    (hRfn : ∀ u, SobolevMultiIndex.fn (R u)
      =ᵐ[volume.restrict (Ωc : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn u)
    (hT₁fn : ∀ v, SobolevMultiIndex.fn (T₁ v)
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))] fun y ↦ SobolevMultiIndex.fn v (H y))
    (hSfn : ∀ w, SobolevMultiIndex.fn (S w)
      =ᵐ[volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        higherReflection a l (SobolevMultiIndex.fn w))
    (hT₂fn : ∀ w, SobolevMultiIndex.fn (T₂ w)
      =ᵐ[volume.restrict (U : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ SobolevMultiIndex.fn w (Hinv x))
    (hT₁ : IsDiffeoOnWithBoundedJacobian H Hinv
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))
      (Ωc : Set (EuclideanSpace ℝ (Fin (d + 1)))) M)
    (hT₂ : IsDiffeoOnWithBoundedJacobian H Hinv
      (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))
      (U : Set (EuclideanSpace ℝ (Fin (d + 1)))) M')
    (hHk : ContDiffOn ℝ k H (unitChartCube d)) {W : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hW : IsOpen W) (hHinvk : ContDiffOn ℝ k Hinv W)
    (hUW : closure (U : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ W)
    (hUc : IsCompact (closure (U : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hΩc : Ωc ≤ Ω) (hak : ∀ i < k, ∑ j, a j * l j ^ i = 1)
    (u : SobolevEuclidean (d + 1) 1 p Ω)
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn u) k p Ω volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn (T₂ (S (T₁ (R u))))) k p U volume := by
  have h1 : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn (R u)) k p Ωc volume :=
    (hu.mono_set hΩc).congr_ae (hRfn u).symm
  have h2 : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn (T₁ (R u))) k p
      (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) volume := by
    refine (MemSobolevMultiIndex.comp_diffeoOn_of_order k hT₁.symm isOpen_unitChartCube hHk
      (isCompact_closure_cylinder r) ?_ (closure_cylinder_subset_unitChartCube hr) h1).congr_ae
      (hT₁fn (R u)).symm
    exact fun x hx ↦ subset_closure (posHalf_le _ _ hx)
  have h3 : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn (S (T₁ (R u)))) k p (cylinder d r) volume :=
    (MemSobolevMultiIndex.higherReflection_of_order hl hl1 k a hak h2).congr_ae
      (hSfn (T₁ (R u))).symm
  exact (MemSobolevMultiIndex.comp_diffeoOn_of_order k hT₂ hW hHinvk hUc subset_closure hUW
    h3).congr_ae (hT₂fn (S (T₁ (R u)))).symm

end SobolevEuclidean

end ChartLocalMem

section ChartLocalHigher

variable {d : ℕ} {n : WithTop ℕ∞} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {m : ℕ} {a l : Fin m → ℝ}

namespace SobolevEuclidean

variable (p) (c : ContDiffChart n (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (hn : 1 ≤ n)
  {r : ℝ} (hr : r < 1) (ha : ∑ j, a j = 1) (hl : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j)

/-- The restriction $W^{1,p}(\Omega) \to W^{1,p}(U_r \cap \Omega)$, as a bounded linear map. -/
def chartRestrictLr :
    SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p (c.opensInterr hr) :=
  SobolevMultiIndex.restrictL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p volume
    (c.opensInterr_le hr)

/-- The transfer $v \mapsto v \circ H$ from $W^{1,p}(U_r \cap \Omega)$ to $W^{1,p}(Q_r^+)$ along a
chart $H$ of class $C^n$, $n \ge 1$, as a bounded linear map. -/
def chartTransferLr : SobolevEuclidean (d + 1) 1 p (c.opensInterr hr) →L[ℝ]
    SobolevEuclidean (d + 1) 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) :=
  SobolevMultiIndex.compDiffeoL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume
    (c.exists_isDiffeoOnWithBoundedJacobian_posHalf_cylinder hr hn).choose_spec

/-- The higher-order reflection $W^{1,p}(Q_r^+) \to W^{1,p}(Q_r)$ over the standard basis,
`SobolevMultiIndex.higherReflectionL`, for $\sum_j a_j = 1$ and $-1 \le \lambda_j < 0$. -/
def cubeReflectLr : SobolevEuclidean (d + 1) 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r)) →L[ℝ]
    SobolevEuclidean (d + 1) 1 p (cylinder d r) :=
  SobolevMultiIndex.higherReflectionL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p ha hl
    hl1

/-- The transfer back $w \mapsto w \circ H^{-1}$ from $W^{1,p}(Q_r)$ to $W^{1,p}(U_r)$, as a bounded
linear map. -/
def chartRetransferLr : SobolevEuclidean (d + 1) 1 p (cylinder d r) →L[ℝ]
    SobolevEuclidean (d + 1) 1 p (c.opensUr hr) :=
  SobolevMultiIndex.compDiffeoL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume
    (c.exists_isDiffeoOnWithBoundedJacobian_cylinder hr hn).choose_spec.symm

/-- The **chart-local extension of higher order**: for a chart $H$ of $\Omega$ of class $C^n$ with
$n \ge 1$, a radius $r < 1$, coefficients with $\sum_j a_j = 1$ and scales with
$-1 \le \lambda_j < 0$, the bounded linear map $W^{1,p}(\Omega) \to W^{1,p}(U_r)$ that restricts
$u$ to $U_r \cap \Omega$, transfers it to $Q_r^+$ along $H$, reflects it to $Q_r$ by the
higher-order reflection $P_a$, and transfers it back to $U_r$ along $H^{-1}$. Its function is
$P_a(u \circ H) \circ H^{-1}$.

It agrees with $u$ on $U_r \cap \Omega$ (`SobolevEuclidean.chartExtendLr_fn_ae_eq`). For a chart
of class $C^k$ and coefficients that satisfy the Vandermonde conditions of order $k$, it maps
the functions of $W^{k,p}(\Omega)$ into $W^{k,p}(U_r)$
(`SobolevEuclidean.chartExtendLr_mem_of_order`). -/
def chartExtendLr : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p (c.opensUr
  hr) :=
  chartRetransferLr p c hn hr ∘L cubeReflectLr p ha hl hl1 ∘L chartTransferLr p c hn hr ∘L
    chartRestrictLr p c hr

/-- `SobolevEuclidean.chartExtendLr` applied to $u$ is the composite of its four steps. -/
theorem chartExtendLr_apply (u : SobolevEuclidean (d + 1) 1 p Ω) :
    chartExtendLr p c hn hr ha hl hl1 u = chartRetransferLr p c hn hr (cubeReflectLr p ha hl hl1
      (chartTransferLr p c hn hr (chartRestrictLr p c hr u))) :=
  rfl

/-- The function of the restriction `SobolevEuclidean.chartRestrictLr` of $u$ is the function of
$u$, almost everywhere on $U_r \cap \Omega$. -/
theorem fn_chartRestrictLr (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (chartRestrictLr p c hr u)
      =ᵐ[volume.restrict (c.opensInterr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        SobolevMultiIndex.fn u :=
  SobolevMultiIndex.fn_restrictL _ _

/-- The function of the transfer `SobolevEuclidean.chartTransferLr` of $v$ is $v \circ H$, almost
everywhere on $Q_r^+$. -/
theorem fn_chartTransferLr (v : SobolevEuclidean (d + 1) 1 p (c.opensInterr hr)) :
    SobolevMultiIndex.fn (chartTransferLr p c hn hr v)
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))] fun y ↦ SobolevMultiIndex.fn v (c.toFun y) :=
  SobolevMultiIndex.fn_compDiffeoL _ _

/-- The function of the reflection `SobolevEuclidean.cubeReflectLr` of $w$ is $P_a w$, almost
everywhere on $Q_r$. -/
theorem fn_cubeReflectLr (w : SobolevEuclidean (d + 1) 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r))) :
    SobolevMultiIndex.fn (cubeReflectLr p ha hl hl1 w)
      =ᵐ[volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        higherReflection a l (SobolevMultiIndex.fn w) :=
  SobolevMultiIndex.fn_higherReflectionL ha hl hl1 w

/-- On $Q_r^+$, the function of the reflection `SobolevEuclidean.cubeReflectLr` of $w$ is almost
everywhere the function of $w$. -/
theorem fn_cubeReflectLr_restrict (w : SobolevEuclidean (d + 1) 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r))) :
    SobolevMultiIndex.fn (cubeReflectLr p ha hl hl1 w)
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn w :=
  SobolevMultiIndex.fn_higherReflectionL_restrict ha hl hl1 w

/-- The function of the transfer back `SobolevEuclidean.chartRetransferLr` of $w$ is
$w \circ H^{-1}$, almost everywhere on $U_r$. -/
theorem fn_chartRetransferLr (w : SobolevEuclidean (d + 1) 1 p (cylinder d r)) :
    SobolevMultiIndex.fn (chartRetransferLr p c hn hr w)
      =ᵐ[volume.restrict (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ SobolevMultiIndex.fn w (c.invFun x) :=
  SobolevMultiIndex.fn_compDiffeoL _ _

include hn in
/-- For a chart of class $C^n$, $n \ge 1$: if a property holds for almost every point of $Q_r^+$,
then it holds at $H^{-1}(x)$ for almost every $x \in U_r \cap \Omega$. -/
theorem ae_comp_chart_invFun_cylinder {P : EuclideanSpace ℝ (Fin (d + 1)) → Prop}
    (hP : ∀ᵐ y ∂volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
      Set (EuclideanSpace ℝ (Fin (d + 1)))), P y) :
    ∀ᵐ x ∂volume.restrict (c.opensInterr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      P (c.invFun x) :=
  (c.exists_isDiffeoOnWithBoundedJacobian_posHalf_cylinder hr hn).choose_spec.symm.ae_comp_restrict
    hP

/-- The function of the chart-local extension `SobolevEuclidean.chartExtendLr` of $u$ equals the
function of $u$ almost everywhere on $U_r \cap \Omega$. -/
theorem chartExtendLr_fn_ae_eq (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (chartExtendLr p c hn hr ha hl hl1 u)
      =ᵐ[volume.restrict (c.opensInterr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        SobolevMultiIndex.fn u := by
  rw [chartExtendLr_apply]
  exact SobolevEuclidean.chartExtend_fn_of_ops (chartRestrictLr p c hr) (chartTransferLr p c hn hr)
    (cubeReflectLr p ha hl hl1) (chartRetransferLr p c hn hr) (fn_chartRestrictLr p c hr)
    (fn_chartTransferLr p c hn hr) (fn_cubeReflectLr_restrict p ha hl hl1)
    (fn_chartRetransferLr p c hn hr) (fun h ↦ ae_comp_chart_invFun_cylinder c hn hr h)
    (c.opensInterr_le_opensUr hr) (fun x hx ↦ c.toFun_invFun (c.opensUr_subset hr hx.1)) u

/-- The **chart-local extension preserves $W^{k,p}$**. Let $H$ be a chart of $\Omega$ of class $C^n$
with $n \ge 1$, let $k \le n$, let $r < 1$, let $-1 \le \lambda_j < 0$, and let the coefficients
satisfy $\sum_j a_j = 1$ and the Vandermonde conditions $\sum_j a_j \lambda_j^i = 1$ for
$i < k$. If $u \in W^{1,p}(\Omega)$ and the function of $u$ lies in $W^{k,p}(\Omega)$, then the
function of `SobolevEuclidean.chartExtendLr p c hn hr ha hl hl1 u` lies in $W^{k,p}(U_r)$.

Here $W^{k,p}$ is the multi-index formulation `MemSobolevMultiIndex` over the standard basis.
The proof specializes `SobolevEuclidean.chartExtend_mem_of_ops`. -/
theorem chartExtendLr_mem_of_order {k : ℕ} (hnk : (k : WithTop ℕ∞) ≤ n)
    (hak : ∀ i < k, ∑ j, a j * l j ^ i = 1) (u : SobolevEuclidean (d + 1) 1 p Ω)
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn u) k p Ω volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn (chartExtendLr p c hn hr ha hl hl1 u)) k p (c.opensUr hr) volume := by
  rw [chartExtendLr_apply]
  exact chartExtend_mem_of_ops hr hl hl1 (chartRestrictLr p c hr) (chartTransferLr p c hn hr)
    (cubeReflectLr p ha hl hl1) (chartRetransferLr p c hn hr) (fn_chartRestrictLr p c hr)
    (fn_chartTransferLr p c hn hr) (fn_cubeReflectLr p ha hl hl1) (fn_chartRetransferLr p c hn hr)
    (c.exists_isDiffeoOnWithBoundedJacobian_posHalf_cylinder hr hn).choose_spec
    (c.exists_isDiffeoOnWithBoundedJacobian_cylinder hr hn).choose_spec
    ((c.contDiffOn.of_le hnk).mono subset_closure) c.isOpen_U
    ((c.contDiffOn_invFun.of_le hnk).mono subset_closure) (c.closure_opensUr_subset hr)
    (c.isCompact_closure_opensUr hr) (c.opensInterr_le hr) hak u hu

/-- The $L^p$ bound of the chart-local extension of higher order: there is a finite constant $C$
such that, for every $u \in W^{1,p}(\Omega)$, the function $w$ of
`SobolevEuclidean.chartExtendLr p c hn hr ha hl hl1 u` satisfies $\|w\|_{L^p(U_r)} \le C
\|u\|_{L^p(U_r \cap \Omega)}$.

After the restriction, each step changes the $L^p$ norm by at most a constant factor: the two
transports along the chart (`SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le`) and the
higher-order reflection, which is a finite sum of dilations
(`SobolevMultiIndex.exists_eLpNorm_fn_higherReflectionL_le`). -/
theorem exists_eLpNorm_fn_chartExtendLr_le : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      eLpNorm (SobolevMultiIndex.fn (chartExtendLr p c hn hr ha hl hl1 u)) p
          (volume.restrict (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        ≤ C * eLpNorm (SobolevMultiIndex.fn u) p
          (volume.restrict (c.opensInterr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le (F := ℝ)
    (b := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis) (p := p) (μ := volume)
    (c.exists_isDiffeoOnWithBoundedJacobian_posHalf_cylinder hr hn).choose_spec
  obtain ⟨C₂, hC₂, h₂⟩ := SobolevMultiIndex.exists_eLpNorm_fn_higherReflectionL_le (F := ℝ)
    (b := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis) (p := p) (r := r) ha hl hl1
  obtain ⟨C₃, hC₃, h₃⟩ := SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le (F := ℝ)
    (b := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis) (p := p) (μ := volume)
    (c.exists_isDiffeoOnWithBoundedJacobian_cylinder hr hn).choose_spec.symm
  refine ⟨C₃ * (C₂ * C₁), ENNReal.mul_ne_top hC₃ (ENNReal.mul_ne_top hC₂ hC₁), fun u ↦ ?_⟩
  rw [chartExtendLr_apply]
  refine (h₃ _).trans ?_
  rw [mul_assoc]
  gcongr
  refine (h₂ _).trans ?_
  rw [mul_assoc]
  gcongr
  exact (h₁ _).trans_eq (by rw [eLpNorm_congr_ae (fn_chartRestrictLr p c hr u)])

/-- The function of the chart-local extension on all of $U_r$: the function of
`SobolevEuclidean.chartExtendLr p c hn hr ha hl hl1 u` equals $P_a(u \circ H) \circ H^{-1}$
almost everywhere on $U_r$.

`SobolevEuclidean.chartExtendLr_fn_ae_eq` is the restriction of this formula to
$U_r \cap \Omega$. The formula shows that the operator does not depend on the exponent $p$ at
the level of functions. -/
theorem chartExtendLr_fn_ae_eq_higherReflection (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (chartExtendLr p c hn hr ha hl hl1 u)
      =ᵐ[volume.restrict (c.opensUr hr : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ higherReflection a l (fun y ↦ SobolevMultiIndex.fn u (c.toFun y)) (c.invFun x) := by
  have h₁ : SobolevMultiIndex.fn (chartTransferLr p c hn hr (chartRestrictLr p c hr u))
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) :
        Set (EuclideanSpace ℝ (Fin (d + 1))))] fun y ↦ SobolevMultiIndex.fn u (c.toFun y) :=
    (fn_chartTransferLr p c hn hr _).trans
      ((c.exists_isDiffeoOnWithBoundedJacobian_posHalf_cylinder hr hn).choose_spec.ae_comp_restrict
        (fn_chartRestrictLr p c hr u))
  have h₂ : SobolevMultiIndex.fn (cubeReflectLr p ha hl hl1
      (chartTransferLr p c hn hr (chartRestrictLr p c hr u)))
      =ᵐ[volume.restrict (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        higherReflection a l (fun y ↦ SobolevMultiIndex.fn u (c.toFun y)) :=
    (fn_cubeReflectLr p ha hl hl1 _).trans
      ((isReflectionSet_cylinder hl hl1 r).higherReflection_congr_ae a h₁)
  rw [chartExtendLr_apply]
  exact (fn_chartRetransferLr p c hn hr _).trans
    ((c.exists_isDiffeoOnWithBoundedJacobian_cylinder hr hn).choose_spec.symm.ae_comp_restrict h₂)

end SobolevEuclidean

end ChartLocalHigher

/-! ### The extension operator of every order -/

section AssemblyHigher

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- The assembled operator preserves $W^{k,p}$, with the operators as variables. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ and $U_1, \dots, U_n$ be open sets, $1 \le p \le \infty$,
and $k \in \mathbb{N}$. Let $\theta_0$ and $\theta_1, \dots, \theta_n$ be smooth real functions
such that $\theta_0 - \kappa$ has compact support for some constant $\kappa$, the support of
$\theta_0$ is disjoint from $\partial\Omega$, and each $\theta_i$ has compact support in $U_i$.
Let the bounded linear maps $E_0 : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^{d+1})$ and $E_i :
W^{1,p}(U_i) \to W^{1,p}(\mathbb{R}^{d+1})$ have the functions $1_\Omega\, \theta_0 u$ and
$1_{U_i}\, \theta_i w$ almost everywhere, let $C_i : W^{1,p}(\Omega) \to W^{1,p}(U_i)$ be
bounded linear maps that map the functions of $W^{k,p}(\Omega)$ into $W^{k,p}(U_i)$, and let
$$P u = E_0 u + \sum_i E_i (C_i u).$$
If $u \in W^{1,p}(\Omega)$ and the function of $u$ lies in $W^{k,p}(\Omega)$, then the function
of $P u$ lies in $W^{k,p}(\mathbb{R}^{d+1})$.

The proof applies the zero extension of every order,
`MemSobolevMultiIndex.indicator_mul_of_hasCompactSupport_sub`, to each term. -/
theorem SobolevEuclidean.extension_mem_of_ops {k n : ℕ}
    {U : Fin n → Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    {E₀ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤}
    {E : ∀ i, SobolevEuclidean (d + 1) 1 p (U i) →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤}
    {C : ∀ i, SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p (U i)}
    {P : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤}
    {θ₀ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {θ : Fin n → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hE₀fn : ∀ u, SobolevMultiIndex.fn (E₀ u) =ᵐ[volume]
      (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator fun x ↦ θ₀ x • SobolevMultiIndex.fn u x)
    (hEfn : ∀ i w, SobolevMultiIndex.fn (E i w) =ᵐ[volume]
      (U i : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator fun x ↦ θ i x • SobolevMultiIndex.fn w
        x)
    (hP : ∀ u, P u = E₀ u + ∑ i, E i (C i u))
    (hθ₀ : ContDiff ℝ ∞ θ₀) (hθ₀κ : ∃ κ : ℝ, HasCompactSupport fun x ↦ θ₀ x - κ)
    (hθ₀Γ : Disjoint (tsupport θ₀) (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hθ : ∀ i, ContDiff ℝ ∞ (θ i)) (hθc : ∀ i, HasCompactSupport (θ i))
    (hθU : ∀ i, tsupport (θ i) ⊆ U i)
    (hC : ∀ i (u : SobolevEuclidean (d + 1) 1 p Ω),
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (SobolevMultiIndex.fn u) k p Ω volume →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (SobolevMultiIndex.fn (C i u)) k p (U i) volume)
    (u : SobolevEuclidean (d + 1) 1 p Ω)
    (hu : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn u) k p Ω volume) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      (SobolevMultiIndex.fn (P u)) k p ⊤ volume := by
  have h0 := MemSobolevMultiIndex.indicator_mul_of_hasCompactSupport_sub
    (b := (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis) (p := p) (μ := volume) k hθ₀ hθ₀κ
    hθ₀Γ hu
  have hi : ∀ i, MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((U i : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator fun x ↦
        θ i x * SobolevMultiIndex.fn (C i u) x) k p ⊤ volume := fun i ↦ by
    refine MemSobolevMultiIndex.indicator_mul_of_hasCompactSupport_sub k (hθ i)
      ⟨0, by simpa using hθc i⟩ ?_ (hC i u hu)
    exact (Set.disjoint_iff_inter_eq_empty.2 (U i).isOpen.inter_frontier_eq).mono_left (hθU i)
  have hsum := MemSobolevMultiIndex.add h0
    (MemSobolevMultiIndex.finset_sum Finset.univ fun i _ ↦ hi i)
  refine hsum.congr_ae (ae_restrict_of_ae ?_)
  have h1 := SobolevEuclidean.fn_extension_of_ops hP u
  have h2 : ∀ᵐ x ∂volume, ∀ i, SobolevMultiIndex.fn (E i (C i u)) x
      = (U i : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator
        (fun x ↦ θ i x • SobolevMultiIndex.fn (C i u) x) x :=
    ae_all_iff.2 fun i ↦ hEfn i (C i u)
  filter_upwards [h1, hE₀fn u, h2] with x hx hx0 hxi
  rw [Pi.add_apply, Finset.sum_apply, hx, Pi.add_apply, Finset.sum_apply, hx0,
    Finset.sum_congr rfl fun i _ ↦ hxi i]
  rfl

/-- For $0 \le j < k$, the scale $\lambda_j = -1/(j+1)$ is negative. -/
theorem neg_inv_succ_lt_zero {k : ℕ} (j : Fin k) : -(((j : ℕ) : ℝ) + 1)⁻¹ < 0 := by
  have : (0 : ℝ) < ((j : ℕ) : ℝ) + 1 := by positivity
  exact neg_neg_of_pos (inv_pos.2 this)

/-- For $0 \le j < k$, the scale $\lambda_j = -1/(j+1)$ is at least $-1$. -/
theorem neg_one_le_neg_inv_succ {k : ℕ} (j : Fin k) : -1 ≤ -(((j : ℕ) : ℝ) + 1)⁻¹ := by
  rw [neg_le_neg_iff]
  exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ (j : ℕ))])

/-- For $k \ge 1$ there are scales $\lambda \in \mathbb{R}^k$ with $-1 \le \lambda_j < 0$ and
coefficients $a \in \mathbb{R}^k$ with $\sum_j a_j = 1$ and $\sum_j a_j \lambda_j^i = 1$ for
every $i < k$. -/
theorem exists_vandermonde_coeffs_scales (k : ℕ) (hk : 1 ≤ k) :
    ∃ a l : Fin k → ℝ, (∀ j, l j < 0) ∧ (∀ j, -1 ≤ l j) ∧ ∑ j, a j = 1 ∧
      ∀ i < k, ∑ j, a j * l j ^ i = 1 := by
  obtain ⟨a, ha⟩ := exists_vandermonde_coeffs k
  refine ⟨a, fun j : Fin k ↦ -(((j : ℕ) : ℝ) + 1)⁻¹, fun j ↦ neg_inv_succ_lt_zero j,
    fun j ↦ neg_one_le_neg_inv_succ j, ?_, ha⟩
  simpa using ha 0 hk

/-- From an operator of order one that preserves $W^{k,p}$ to an operator of order $k$. Let
$k \ge 1$ and let $P_1 : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^{d+1})$ be a bounded linear map
such that $P_1 u = u$ almost everywhere on $\Omega$, the function of $P_1 u$ lies in
$W^{k,p}(\mathbb{R}^{d+1})$ whenever the function of $u$ lies in $W^{k,p}(\Omega)$, and $\|P_1
u\|_{L^p(\mathbb{R}^{d+1})} \le K \|u\|_{L^p(\Omega)}$ with a finite constant $K$. Then there
are a bounded linear map $P : W^{k,p}(\Omega) \to W^{k,p}(\mathbb{R}^{d+1})$ and a constant $C$
such that, for every $u \in W^{k,p}(\Omega)$, the function of $P u$ is the function of $P_1 u$
almost everywhere, $P u = u$ almost everywhere on $\Omega$, $\|P u\|_{L^p(\mathbb{R}^{d+1})} \le
C \|u\|_{L^p(\Omega)}$, and $\|P u\| \le C \|u\|$.

The operator $P$ is given by the closed graph theorem,
`SobolevMultiIndex.exists_continuousLinearMap_of_order`. In $P_1 u$, the element $u$ is seen in
$W^{1,p}(\Omega)$ through `SobolevMultiIndex.toLowerOrderL`. -/
theorem SobolevEuclidean.exists_extensionL_of_order_of_ops {k : ℕ} (hk : 1 ≤ k)
    (P₁ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤)
    (hid : ∀ u, SobolevMultiIndex.fn (P₁ u)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn u)
    (hmem : ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (SobolevMultiIndex.fn u) k p Ω volume →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (SobolevMultiIndex.fn (P₁ u)) k p ⊤ volume)
    {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hlp : ∀ u, eLpNorm (SobolevMultiIndex.fn (P₁ u)) p volume
      ≤ K * eLpNorm (SobolevMultiIndex.fn u) p
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ (P : SobolevEuclidean (d + 1) k p Ω →L[ℝ] SobolevEuclidean (d + 1) k p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) k p Ω,
        SobolevMultiIndex.fn (P u) =ᵐ[volume] SobolevMultiIndex.fn (P₁
          (SobolevMultiIndex.toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p Ω
            volume hk u)) ∧
        SobolevMultiIndex.fn (P u)
          =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume ≤ ENNReal.ofReal C
          * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨Pk, hPk⟩ := SobolevMultiIndex.exists_continuousLinearMap_of_order hk P₁ fun u ↦
    hmem (SobolevMultiIndex.toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p Ω
      volume hk u) (SobolevMultiIndex.memSobolevMultiIndex u)
  have hfn : ∀ u, SobolevMultiIndex.fn (Pk u) =ᵐ[volume] SobolevMultiIndex.fn (P₁
      (SobolevMultiIndex.toLowerOrderL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p Ω
        volume hk u)) := fun u ↦ eventuallyEq_restrict_coe_top_iff.1 (hPk u)
  refine ⟨Pk, max K.toReal ‖Pk‖, fun u ↦ ⟨hfn u,
    Filter.EventuallyEq.trans
      (ae_restrict_of_ae_restrict_of_subset (subset_univ _) (hPk u)) (hid _), ?_,
    (Pk.le_opNorm u).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩⟩
  have hKC : K ≤ ENNReal.ofReal (max K.toReal ‖Pk‖) :=
    calc K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hK).symm
      _ ≤ ENNReal.ofReal (max K.toReal ‖Pk‖) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  -- the function of `u` read at order one is the function of `u`, by definition
  have h₁ : eLpNorm (SobolevMultiIndex.fn (P₁ (SobolevMultiIndex.toLowerOrderL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p Ω volume hk u))) p volume
      ≤ K * eLpNorm (SobolevMultiIndex.fn u) p
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := hlp _
  exact (eLpNorm_congr_ae (hfn u)).trans_le (h₁.trans (by gcongr))

/-- The **extension operator of every order for an explicit atlas, for every exponent at once**. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open and $k \ge 1$. Let $H_1, \dots, H_n$ be charts of
$\Omega$ of class $C^k$, with radii $r_i < 1$. Let $\theta_0, \theta_1, \dots, \theta_n$ be
smooth real functions with $\theta_0 + \sum_i \theta_i = 1$ everywhere, such that
$\theta_0 - \kappa$ has compact support for some constant $\kappa$, the support of $\theta_0$ is
disjoint from $\partial\Omega$, and each $\theta_i$ has compact support in $H_i(Q_{r_i})$. Let
$-1 \le \lambda_j < 0$, $\sum_j a_j = 1$, and $\sum_j a_j \lambda_j^i = 1$ for $i < k$. Then
there is a map $E$ on real functions such that for every $1 \le p \le \infty$ there are a
bounded linear map $P : W^{k,p}(\Omega) \to W^{k,p}(\mathbb{R}^{d+1})$ and a constant $C$ with,
for every $u \in W^{k,p}(\Omega)$,
$$P u = E u \text{ almost everywhere}, \quad P u = u \text{ on } \Omega, \quad \|P
  u\|_{L^p(\mathbb{R}^{d+1})} \le C \|u\|_{L^p(\Omega)}, \quad \|P u\| \le C \|u\|.$$

The map constructed in the proof is
$$E f = 1_\Omega\, \theta_0 f + \sum_i 1_{H_i(Q_{r_i})}\, \theta_i \cdot \big( P_a(f \circ H_i)
  \circ H_i^{-1} \big),$$
with the higher-order reflection $P_a$. At order one the operator is
$P_1 = E_0 + \sum_i E_i \circ C_i$, with the zero extensions $E_0$ and $E_i$ of $\theta_0 u$ and
$\theta_i w$ and the chart-local extensions $C_i$ of `SobolevEuclidean.chartExtendLr`. Its
function is $E u$ by `SobolevEuclidean.chartExtendLr_fn_ae_eq_higherReflection`, and its $L^p$
bound is `SobolevEuclidean.eLpNorm_fn_extension_le_of_ops`. The closed graph theorem
(`SobolevEuclidean.exists_extensionL_of_order_of_ops`) lifts $P_1$ to order $k$ without changing
its function. -/
theorem SobolevEuclidean.exists_extensionL_of_order_of_atlas {k n : ℕ} (hk : 1 ≤ k)
    (c : Fin n → ContDiffChart k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {θ₀ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {θ : Fin n → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hθ₀ : ContDiff ℝ ∞ θ₀) (hθ₀κ : ∃ κ : ℝ, HasCompactSupport fun x ↦ θ₀ x - κ)
    (hθ₀Γ : Disjoint (tsupport θ₀) (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (hθ : ∀ i, ContDiff ℝ ∞ (θ i)) (hθc : ∀ i, HasCompactSupport (θ i))
    (hsum : ∀ x, θ₀ x + ∑ i, θ i x = 1) {r : Fin n → ℝ} (hr : ∀ i, r i < 1)
    (hθr : ∀ i, tsupport (θ i) ⊆ (c i).opensUr (hr i)) {m : ℕ} {a l : Fin m → ℝ}
    (ha0 : ∑ j, a j = 1) (hl0 : ∀ j, l j < 0) (hl1 : ∀ j, -1 ≤ l j)
    (hak : ∀ i < k, ∑ j, a j * l j ^ i = 1) :
    ∃ E : (EuclideanSpace ℝ (Fin (d + 1)) → ℝ) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
        ∃ (P : SobolevEuclidean (d + 1) k p Ω →L[ℝ] SobolevEuclidean (d + 1) k p ⊤) (C : ℝ),
          ∀ u : SobolevEuclidean (d + 1) k p Ω,
            SobolevMultiIndex.fn (P u) =ᵐ[volume] E (SobolevMultiIndex.fn u) ∧
            SobolevMultiIndex.fn (P u)
              =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
              SobolevMultiIndex.fn u ∧
            eLpNorm (SobolevMultiIndex.fn (P u)) p volume ≤ ENNReal.ofReal C
              * eLpNorm (SobolevMultiIndex.fn u) p
                (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) ∧
            ‖P u‖ ≤ C * ‖u‖ := by
  have hn : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hk
  have hα₀ : IsSobolevCutoff Ω θ₀ :=
    IsSobolevCutoff.of_hasCompactSupport_sub hθ₀ hθ₀κ.choose_spec hθ₀Γ
  have hα : ∀ i, IsSobolevCutoff ((c i).opensUr (hr i)) (θ i) := fun i ↦
    IsSobolevCutoff.of_hasCompactSupport (hθ i) (hθc i) (hθr i)
  have hM₀' := hα₀.exists_nonneg_bound
  obtain ⟨M₀, -, hM₀⟩ := hM₀'
  have hM' := fun i ↦ (hα i).exists_nonneg_bound
  choose M hM0 hM using hM'
  have hE' :
      ∃ E : (EuclideanSpace ℝ (Fin (d + 1)) → ℝ) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
        E = fun f x ↦ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator (fun y ↦ θ₀ y • f y) x
          + ∑ i, ((c i).opensUr (hr i) : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator
            (fun y ↦ θ i y • higherReflection a l (fun z ↦ f ((c i).toFun z)) ((c i).invFun y))
              x := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ := hE'
  refine ⟨E, fun p _ ↦ ?_⟩
  have hB' := fun i ↦
    SobolevEuclidean.exists_eLpNorm_fn_chartExtendLr_le p (c i) hn (hr i) ha0 hl0 hl1
  choose B hB hBu using hB'
  have hP₁' :
      ∃ P₁ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤,
        ∀ u, P₁ u = SobolevMultiIndex.extendZeroMulL ℝ
            (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume hα₀ u
          + ∑ i, SobolevMultiIndex.extendZeroMulL ℝ
              (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume (hα i)
              (SobolevEuclidean.chartExtendLr p (c i) hn (hr i) ha0 hl0 hl1 u) :=
    ⟨SobolevMultiIndex.extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p
        volume hα₀
      + ∑ i, (SobolevMultiIndex.extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
          p volume (hα i)).comp (SobolevEuclidean.chartExtendLr p (c i) hn (hr i) ha0 hl0 hl1),
      fun u ↦ by simp only [add_apply, sum_apply, ContinuousLinearMap.comp_apply]⟩
  obtain ⟨P₁, hP₁⟩ := hP₁'
  have hid : ∀ u, SobolevMultiIndex.fn (P₁ u)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      SobolevMultiIndex.fn u := fun u ↦
    SobolevEuclidean.fn_extension_ae_eq_of_ops (Ωc := fun i ↦ (c i).opensInterr (hr i))
      (fun _ ↦ rfl) (χ := fun _ ↦ 1) (fun x _ ↦ hsum x)
      (fun i x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hθr i h))
      (fun u ↦ SobolevMultiIndex.fn_extendZeroMulL hα₀ u)
      (fun i w ↦ SobolevMultiIndex.fn_extendZeroMulL (hα i) w)
      (fun i u ↦ SobolevEuclidean.chartExtendLr_fn_ae_eq p (c i) hn (hr i) ha0 hl0 hl1 u)
      hP₁ u (Eventually.of_forall fun x ↦ (one_mul _).symm)
  have hmem : ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (SobolevMultiIndex.fn u) k p Ω volume →
      MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
        (SobolevMultiIndex.fn (P₁ u)) k p ⊤ volume :=
    fun u hu ↦ SobolevEuclidean.extension_mem_of_ops
      (fun u ↦ SobolevMultiIndex.fn_extendZeroMulL hα₀ u)
      (fun i w ↦ SobolevMultiIndex.fn_extendZeroMulL (hα i) w) hP₁ hθ₀ hθ₀κ hθ₀Γ hθ hθc hθr
      (fun i u hu ↦ SobolevEuclidean.chartExtendLr_mem_of_order p (c i) hn (hr i) ha0 hl0 hl1
        le_rfl hak u hu) u hu
  have hlp : ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      eLpNorm (SobolevMultiIndex.fn (P₁ u)) p volume
        ≤ (ENNReal.ofReal M₀ + ∑ i, ENNReal.ofReal (M i) * B i)
          * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := fun u ↦
    SobolevEuclidean.eLpNorm_fn_extension_le_of_ops (Ωc := fun i ↦ (c i).opensInterr (hr i))
      (fun _ ↦ rfl)
      (fun u ↦ SobolevMultiIndex.eLpNorm_fn_extendZeroMulL_le hα₀ (fun x ↦ (hM₀ x).1) u)
      (fun i w ↦ SobolevMultiIndex.eLpNorm_fn_extendZeroMulL_le (hα i) (fun x ↦ (hM i x).1) w)
      (fun i u ↦ hBu i u) hP₁ u
  have hK : ENNReal.ofReal M₀ + ∑ i, ENNReal.ofReal (M i) * B i ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.sum_ne_top.2 fun i _ ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hB i)⟩
  have hP' := SobolevEuclidean.exists_extensionL_of_order_of_ops hk P₁ hid hmem hK hlp
  obtain ⟨P, C, hP⟩ := hP'
  -- the function of `P₁ v` is `E` applied to the function of `v`, summand by summand
  have hsummand : ∀ v i, SobolevMultiIndex.fn (SobolevMultiIndex.extendZeroMulL ℝ
      (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume (hα i)
        (SobolevEuclidean.chartExtendLr p (c i) hn (hr i) ha0 hl0 hl1 v))
      =ᵐ[volume] ((c i).opensUr (hr i) : Set (EuclideanSpace ℝ (Fin (d + 1)))).indicator
        (fun y ↦ θ i y • higherReflection a l (fun z ↦ SobolevMultiIndex.fn v ((c i).toFun z))
          ((c i).invFun y)) := fun v i ↦ by
    filter_upwards [SobolevMultiIndex.fn_extendZeroMulL (hα i)
        (SobolevEuclidean.chartExtendLr p (c i) hn (hr i) ha0 hl0 hl1 v),
      (ae_restrict_iff' ((c i).opensUr (hr i)).isOpen.measurableSet).1
        (SobolevEuclidean.chartExtendLr_fn_ae_eq_higherReflection p (c i) hn (hr i) ha0 hl0 hl1
          v)] with x hx1 hx2
    rw [hx1]
    by_cases hx : x ∈ ((c i).opensUr (hr i) : Set (EuclideanSpace ℝ (Fin (d + 1))))
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hx2 hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  have hfn : ∀ v, SobolevMultiIndex.fn (P₁ v) =ᵐ[volume] E (SobolevMultiIndex.fn v) := by
    intro v
    filter_upwards [SobolevEuclidean.fn_extension_of_ops hP₁ v,
      SobolevMultiIndex.fn_extendZeroMulL hα₀ v, ae_all_iff.2 (hsummand v)] with x hx0 hx1 hx2
    rw [hE, hx0]
    simp only [Pi.add_apply, Finset.sum_apply, hx1]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ hx2 i
  -- the function of `u` read at order one is the function of `u`, by definition
  exact ⟨P, C, fun u ↦ ⟨(hP u).1.trans (hfn _), (hP u).2⟩⟩

/-- The **extension theorem of every order, with one map for every exponent**. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be an open set of class $C^k$, $k \ge 1$, with bounded
boundary. Then there is a map $E$ on real functions such that for every $1 \le p \le \infty$
there are a bounded linear extension operator $P : W^{k,p}(\Omega) \to
W^{k,p}(\mathbb{R}^{d+1})$ and a constant $C$ with, for every $u \in W^{k,p}(\Omega)$,
$$P u = E u \text{ almost everywhere}, \quad P u = u \text{ on } \Omega, \quad \|P
  u\|_{L^p(\mathbb{R}^{d+1})} \le C \|u\|_{L^p(\Omega)}, \quad \|P
  u\|_{W^{k,p}(\mathbb{R}^{d+1})} \le C \|u\|_{W^{k,p}(\Omega)}.$$

This is the result of [brezis2011functional], Comments on Chapter 9, and of Lions and Magenes,
and Theorem 7.3.5 of [han2009theoretical] at order $k$. "Of class $C^k$" is
`IsContDiffChartDomain k Ω`: every boundary point lies in the range of a chart of class $C^k$.
The operator is built at order one as in the proof of Theorem 9.7 of [brezis2011functional]: the
partition of unity $\theta_0, \theta_i$ of Lemma 9.3 for a finite atlas of $C^k$ charts, the
zero extension of $\theta_0 u$, and for each chart the zero extension of $\theta_i$ times the
chart-local extension `SobolevEuclidean.chartExtendLr` on a cylinder $Q_{r_i}$ with
$H_i^{-1}(\operatorname{supp} \theta_i) \subseteq Q_{r_i}$. The even reflection is replaced by
the higher-order reflection of `MemSobolevMultiIndex.higherReflection_of_order`, with
coefficients that solve the Vandermonde system of order $k$ (`exists_vandermonde_coeffs`). This
operator maps the functions of $W^{k,p}(\Omega)$ into $W^{k,p}(\mathbb{R}^{d+1})$
(`SobolevEuclidean.extension_mem_of_ops`), and the closed graph theorem
(`SobolevMultiIndex.exists_continuousLinearMap_of_order`) makes its restriction to
$W^{k,p}(\Omega)$ bounded without changing its function. None of these choices involves $p$, so
one map $E$ serves all exponents. The construction does not give one operator for every order
$k$. -/
theorem SobolevEuclidean.exists_extensionL_of_order_uniform {k : ℕ} (hk : 1 ≤ k)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ E : (EuclideanSpace ℝ (Fin (d + 1)) → ℝ) → EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
        ∃ (P : SobolevEuclidean (d + 1) k p Ω →L[ℝ] SobolevEuclidean (d + 1) k p ⊤) (C : ℝ),
          ∀ u : SobolevEuclidean (d + 1) k p Ω,
            SobolevMultiIndex.fn (P u) =ᵐ[volume] E (SobolevMultiIndex.fn u) ∧
            SobolevMultiIndex.fn (P u)
              =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
              SobolevMultiIndex.fn u ∧
            eLpNorm (SobolevMultiIndex.fn (P u)) p volume ≤ ENNReal.ofReal C
              * eLpNorm (SobolevMultiIndex.fn u) p
                (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) ∧
            ‖P u‖ ≤ C * ‖u‖ := by
  -- the atlas and the partition of unity
  -- (each existential is named before it is destructured: `obtain … := term` would first
  -- generalize `term` in this large goal, and that check is expensive)
  have hatlas := hΩ.exists_finite_atlas hΓ
  obtain ⟨n, c, hc⟩ := hatlas
  have hK : IsCompact (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier hΓ
  have hpart := hK.exists_contDiff_partitionOfUnity (fun i ↦ (c i).isOpen_U) hc
  obtain ⟨θ₀, θ, hθ₀, hθ, -, -, hsum, hθc, hθU, hθ₀K⟩ := hpart
  -- the radii `rᵢ < 1` with `supp θᵢ ⊆ Hᵢ(Q_{rᵢ})`
  have hradii := fun i ↦ (c i).exists_lt_one_subset_opensUr (hθc i) (hθU i)
  choose r hr hθr using hradii
  -- the scales and the Vandermonde coefficients
  have hvdm := exists_vandermonde_coeffs_scales k hk
  obtain ⟨a, l, hl0, hl1, ha0, hak⟩ := hvdm
  -- `θ₀ − 1 = −∑ θ i` is compactly supported
  have hθ₀κ : HasCompactSupport fun x ↦ θ₀ x - 1 := by
    have e : (fun x ↦ θ₀ x - 1) = -(∑ i, θ i) := by
      funext x
      rw [Pi.neg_apply, Finset.sum_apply]
      linarith [hsum x]
    rw [e]
    exact (HasCompactSupport.finset_sum fun i _ ↦ hθc i).neg
  exact SobolevEuclidean.exists_extensionL_of_order_of_atlas hk c hθ₀ ⟨1, hθ₀κ⟩ hθ₀K hθ hθc hsum
    hr hθr ha0 hl0 hl1 hak

/-- The **extension theorem of every order**. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be an open set
of class $C^k$, $k \ge 1$, with bounded boundary, and let $1 \le p \le \infty$. Then there are a
bounded linear extension operator $P : W^{k,p}(\Omega) \to W^{k,p}(\mathbb{R}^{d+1})$ and a
constant $C$ such that, for every $u \in W^{k,p}(\Omega)$,
$$P u = u \text{ on } \Omega, \quad \|P u\|_{L^p(\mathbb{R}^{d+1})} \le C \|u\|_{L^p(\Omega)},
  \quad \|P u\|_{W^{k,p}(\mathbb{R}^{d+1})} \le C \|u\|_{W^{k,p}(\Omega)}.$$

This is the result of [brezis2011functional], Comments on Chapter 9, and of Lions and Magenes,
and Theorem 7.3.5 of [han2009theoretical] at order $k$. One operator is bounded at the orders
$0$ and $k$ at once. The theorem is `SobolevEuclidean.exists_extensionL_of_order_uniform` at one
exponent. At $k = 1$ it is a second proof of Theorem 9.7 of [brezis2011functional]
(`SobolevEuclidean.exists_extensionL`). -/
theorem SobolevEuclidean.exists_extensionL_of_order {k : ℕ} (hk : 1 ≤ k)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ (P : SobolevEuclidean (d + 1) k p Ω →L[ℝ] SobolevEuclidean (d + 1) k p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) k p Ω,
        SobolevMultiIndex.fn (P u)
          =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume ≤ ENNReal.ofReal C
          * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨E, hE⟩ := SobolevEuclidean.exists_extensionL_of_order_uniform hk hΩ hΓ
  obtain ⟨P, C, hP⟩ := hE p
  exact ⟨P, C, fun u ↦ (hP u).2⟩

variable (p Ω) in
/-- An open set $\Omega \subseteq \mathbb{R}^N$ is a **$W^{k,p}$-extension domain** if there is a
bounded linear map $P : W^{k,p}(\Omega) \to W^{k,p}(\mathbb{R}^N)$ with $P u = u$ almost
everywhere on $\Omega$ for every $u \in W^{k,p}(\Omega)$.

At $k = 1$ this is the condition `IsSobolevExtensionDomain N p Ω` (see
`IsSobolevExtensionDomainOfOrder.isSobolevExtensionDomain`). The open sets of class $C^k$ with
bounded boundary are examples (`IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain`). -/
def IsSobolevExtensionDomainOfOrder (N k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∃ P : SobolevEuclidean N k p Ω →L[ℝ] SobolevEuclidean N k p ⊤,
    ∀ u : SobolevEuclidean N k p Ω, SobolevMultiIndex.fn (P u)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] SobolevMultiIndex.fn u

/-- An open set $\Omega \subseteq \mathbb{R}^{d+1}$ of class $C^k$, $k \ge 1$, with bounded boundary
is a $W^{k,p}$-extension domain for every $1 \le p \le \infty$.

This is the extension theorem `SobolevEuclidean.exists_extensionL_of_order` stated as a property
of the domain. -/
theorem IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain {k : ℕ} (hk : 1 ≤ k)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    IsSobolevExtensionDomainOfOrder (d + 1) k p Ω := by
  obtain ⟨P, _, hP⟩ := SobolevEuclidean.exists_extensionL_of_order (p := p) hk hΩ hΓ
  exact ⟨P, fun u ↦ (hP u).1⟩

/-- A $W^{1,p}$-extension domain in the sense of `IsSobolevExtensionDomainOfOrder` is a
$W^{1,p}$-extension domain in the sense of `IsSobolevExtensionDomain`. -/
theorem IsSobolevExtensionDomainOfOrder.isSobolevExtensionDomain {N : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin N))} (h : IsSobolevExtensionDomainOfOrder N 1 p Ω) :
    IsSobolevExtensionDomain N p Ω := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P.comp (Submodule.subtypeL _), fun u ↦ hP u⟩

end AssemblyHigher

/-!
### Density of $C_c^\infty(\mathbb{R}^N)$ in $W^{k,p}(\Omega)$ on a $W^{k,p}$-extension domain
-/

section DensityExtensionHigher

variable {N : ℕ} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Density of the restrictions of $C_c^\infty(\mathbb{R}^N)$ functions in $W^{k,p}(\Omega)$.**
Let $\Omega \subseteq \mathbb{R}^N$ be a $W^{k,p}$-extension domain, $1 \le p < \infty$, and
$u \in W^{k,p}(\Omega)$. Then there are smooth functions $v_n$ with compact support on
$\mathbb{R}^N$ and elements $w_n \in W^{k,p}(\Omega)$ such that $w_n = v_n$ almost everywhere on
$\Omega$ and $w_n \to u$ in $W^{k,p}(\Omega)$.

This extends Corollary 9.8 of [brezis2011functional] to every order; it corresponds to Theorem
7.3.2 of [han2009theoretical]. The proof approximates the extension
$P u \in W^{k,p}(\mathbb{R}^N)$ by functions of $C_c^\infty(\mathbb{R}^N)$ in the norm of
$W^{k,p}(\mathbb{R}^N)$ with iterated derivatives
(`MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm`). That norm dominates the
multi-index norm (`SobolevMultiIndex.ofReal_norm_le_sobolevNorm_of_order`), and the restriction
to $\Omega$ is $1$-Lipschitz. -/
theorem SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_order (hp' : p ≠ ⊤)
    (hΩ : IsSobolevExtensionDomainOfOrder N k p Ω) (u : SobolevEuclidean N k p Ω) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin N) → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧
      (∀ n, HasCompactSupport (v n)) ∧ ∃ w : ℕ → SobolevEuclidean N k p Ω,
        (∀ n, SobolevMultiIndex.fn (w n)
          =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] v n) ∧
        Tendsto w atTop (𝓝 u) := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨P, hP⟩ := hΩ
  have hPu : MemSobolev (SobolevMultiIndex.fn (P u)) k p ⊤ volume :=
    (SobolevMultiIndex.memSobolevMultiIndex (P u)).memSobolev
  obtain ⟨v, hvs, hvc, hvt⟩ := hPu.exists_seq_hasCompactSupport_tendsto_sobolevNorm hp hp'
  choose V hV using fun n ↦ (hvs n).exists_sobolevMultiIndex_of_hasCompactSupport
    (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (k := k) (p := p)
    (Ω := (⊤ : Opens (EuclideanSpace ℝ (Fin N)))) (μ := volume) (hvc n)
  obtain ⟨R, hR⟩ : ∃ R : SobolevEuclidean N k p ⊤ →L[ℝ] SobolevEuclidean N k p Ω,
      R = SobolevMultiIndex.restrictL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis k p volume
        (le_top : Ω ≤ ⊤) := ⟨_, rfl⟩
  have hRfn : ∀ w, SobolevMultiIndex.fn (R w)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] SobolevMultiIndex.fn w := by
    intro w
    rw [hR]
    exact SobolevMultiIndex.fn_restrictL _ _
  have hRle : ∀ w, ‖R w‖ ≤ ‖w‖ := by
    intro w
    rw [hR]
    exact SobolevMultiIndex.norm_restrictL_apply_le _ _
  refine ⟨v, hvs, hvc, fun n ↦ R (V n), fun n ↦ ?_, ?_⟩
  · exact (hRfn _).trans (ae_mono (Measure.restrict_mono le_top le_rfl) (hV n))
  · have hRPu : R (P u) = u := SobolevMultiIndex.ext_of_fn_ae_eq ((hRfn _).trans (hP u))
    rw [← hRPu, tendsto_iff_norm_sub_tendsto_zero]
    obtain ⟨C, hCdef⟩ : ∃ C : ℝ≥0∞, C = ∑ α : MultiIndexLE (Fin N) k,
      ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin (∑ i, α.1 i) ↦ EuclideanSpace ℝ (Fin N)) ℝ
        (multiIndexTuple ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis :
          Fin N → EuclideanSpace ℝ (Fin N)) α.1)‖ₑ := ⟨_, rfl⟩
    have hC : C ≠ ⊤ := by
      rw [hCdef]
      exact ENNReal.sum_ne_top.2 fun _ _ ↦ enorm_ne_top
    have hsub : ∀ n, sobolevNorm (SobolevMultiIndex.fn (V n - P u)) k p ⊤ volume
        = sobolevNorm (v n - SobolevMultiIndex.fn (P u)) k p ⊤ volume := fun n ↦
      sobolevNorm_congr_ae ((SobolevMultiIndex.fn_sub _ _).trans
        ((hV n).sub (Filter.EventuallyEq.refl _ _)))
    have hfin : ∀ᶠ n in atTop,
        sobolevNorm (v n - SobolevMultiIndex.fn (P u)) k p ⊤ volume ≠ ⊤ := by
      filter_upwards [ENNReal.tendsto_nhds_zero.1 hvt 1 one_pos] with n hn
      exact (hn.trans_lt ENNReal.one_lt_top).ne
    have hbound : ∀ n, sobolevNorm (v n - SobolevMultiIndex.fn (P u)) k p ⊤ volume ≠ ⊤ →
        ‖R (V n) - R (P u)‖
          ≤ (C * sobolevNorm (v n - SobolevMultiIndex.fn (P u)) k p ⊤ volume).toReal := by
      intro n hn
      rw [← map_sub]
      refine (hRle _).trans ?_
      have h := SobolevMultiIndex.ofReal_norm_le_sobolevNorm_of_order hp' (V n - P u)
      rw [hsub n, ← hCdef] at h
      exact (ENNReal.toReal_ofReal (norm_nonneg _)).symm.le.trans
        (ENNReal.toReal_mono (ENNReal.mul_ne_top hC hn) h)
    refine squeeze_zero' (g := fun n ↦
      (C * sobolevNorm (v n - SobolevMultiIndex.fn (P u)) k p ⊤ volume).toReal)
      (Eventually.of_forall fun _ ↦ norm_nonneg _) (hfin.mono hbound) ?_
    have h1 : Tendsto (fun n ↦ C * sobolevNorm (v n - SobolevMultiIndex.fn (P u)) k p ⊤ volume)
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hvt (Or.inr hC)
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def] using this

/-- **Density of $C^\infty(\overline{\Omega})$ in $W^{k,p}(\Omega)$.** Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be an open set of class $C^k$, $k \ge 1$, with bounded
boundary, let $1 \le p < \infty$, and let $u \in W^{k,p}(\Omega)$. Then there are smooth
functions $v_n$ with compact support on $\mathbb{R}^{d+1}$ and elements
$w_n \in W^{k,p}(\Omega)$ such that $w_n = v_n$ almost everywhere on $\Omega$ and $w_n \to u$ in
$W^{k,p}(\Omega)$.

This extends Corollary 9.8 of [brezis2011functional] to every order; it corresponds to Theorem
7.3.2 of [han2009theoretical]. The proof combines
`IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain` with
`SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_order`. -/
theorem SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_isContDiffChartDomain
    {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} (hp' : p ≠ ⊤) (hk : 1 ≤ k)
    (hΩ : IsContDiffChartDomain k (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (u : SobolevEuclidean (d + 1) k p Ω) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧
      (∀ n, HasCompactSupport (v n)) ∧ ∃ w : ℕ → SobolevEuclidean (d + 1) k p Ω,
        (∀ n, SobolevMultiIndex.fn (w n)
          =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] v n) ∧
        Tendsto w atTop (𝓝 u) :=
  SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_order hp'
    (IsSobolevExtensionDomainOfOrder.of_isContDiffChartDomain hk hΩ hΓ) u

end DensityExtensionHigher
