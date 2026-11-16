/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter13.Section06

/-!
# Conn, Gould and Toint, Section 13.10: Affine slices of the positive orthant

This module formalizes the barrier trial test and the distance comparisons of [conn2000trust],
Section 13.10, for a feasible set that is the intersection of the positive orthant with an affine
subspace. Algorithm 13.10.1 keeps the step in the nullspace of the equality constraints and applies
a fraction-to-boundary test. The analysis compares two distances of a point $x$ to the boundary: the
ambient distance $\min_i x_i$ to the boundary of the orthant, and the relative distance to the
boundary of the affine slice.

The slice is described in orthonormal coordinates on the slice. For each bound $x_i \ge 0$, the
weight $w_i \in [0, 1]$ is the length of the projection of the coordinate normal $e_i$ onto the
equality nullspace. A coordinate with $w_i \le 0$ is constant on the slice, $x_i = c_i$ with
$c_i > 0$, and gives no boundary hyperplane. For the other coordinates the distance in the slice to
the hyperplane $x_i = 0$ is $x_i / w_i$, by (13.10.13), and the relative distance is the minimum of
these quotients. Lemma 13.10.1 shows that the two distances are comparable on the whole slice, and
Theorem 13.10.2 transfers an ambient fraction-to-boundary test to the relative distance.

## Main definitions

* Algorithm 13.10.1, `ConnGouldToint.Chapter13.AffineOrthantBarrierTrial`: the trial test, with the
  step in the equality nullspace and a strictly feasible trial point.
* Equation (13.10.8), `ConnGouldToint.Chapter13.affineBarrierAmbientDistance`: the ambient distance
  $\min_i x_i$.
* Equations (13.10.8) and (13.10.10), `ConnGouldToint.Chapter13.affineBarrierSliceDistance`: the
  relative distance $\min_{w_i > 0} x_i / w_i$.
* Equation (13.10.15), `ConnGouldToint.Chapter13.affineBarrierNormalFactor`: the least positive
  weight.

## Main results

* Equations (13.10.10)–(13.10.13), `ConnGouldToint.Chapter13.affineBarrier_hyperplane_distance`: the
  distance to a hyperplane is the slack divided by the length of the normal.
* Equation (13.10.15), `ConnGouldToint.Chapter13.affineBarrier_normalFactor_mul_sliceDistance_le`:
  the least positive weight times the relative distance is at most the ambient distance, when a
  movable bound attains the ambient distance.
* Lemma 13.10.1, `ConnGouldToint.Chapter13.lemma_13_10_1`: the ambient distance is at most the
  relative distance, and at least a fixed multiple of $\min\{1, \text{relative distance}\}$.
* Theorem 13.10.2, `ConnGouldToint.Chapter13.theorem_13_10_2`: an ambient fraction-to-boundary test
  implies a relative one when the relative distance is at most one.

## Implementation notes

* Points of the slice are vectors $x \in \mathbb{R}^\iota$ of bound slacks, with the coordinates
  $w_i \le 0$ fixed to $c_i$. The weights are hypotheses $w_i \le 1$, not projections of a given
  matrix.

## Deviations from the source

* **Algorithm 13.10.1** (correction). The printed test compares unsigned distances to the boundary,
  which a point outside the feasible set can pass. The trial point must also be strictly feasible.
  See `ConnGouldToint.Chapter13.AffineOrthantBarrierTrial`.
-/

open Metric Set

namespace ConnGouldToint.Chapter13

/-- **Algorithm 13.10.1** of [conn2000trust], trial test. Let $A : E \to F$ be linear, let
$C \subseteq E$ be the feasible set, and let $\sigma$, $\Delta$, $x$ and $s$ be the
fraction-to-boundary parameter, the radius, the iterate and the step. The step $s$ is an
**admissible trial** if $\|s\| \le \Delta$, $As = 0$, $x + s$ lies in the interior of $C$,
$$\sigma \operatorname{dist}(x, \partial C) \le \operatorname{dist}(x + s, \partial C),$$
and $s$ satisfies the given sufficient decrease condition.

**Correction.** The source tests only the distance inequality. The distance to the boundary is
unsigned, so a point outside $C$ can also satisfy it. The definition therefore requires that
$x + s$ lies in the interior of $C$.

The interiority and distance conditions are `ConnGouldToint.Chapter13.BarrierAdmissibleTrial`. -/
def AffineOrthantBarrierTrial {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] (A : E →ₗ[ℝ] F) (C : Set E) (σ Δ : ℝ)
    (x s : E) (sufficient : E → Prop) : Prop :=
  ‖s‖ ≤ Δ ∧ A s = 0 ∧ BarrierAdmissibleTrial C σ x (x + s) ∧ sufficient s

/-- **Equations (13.10.10)–(13.10.13)** of [conn2000trust]. Let $E$ be a real inner product space,
$n \in E$ nonzero, $b \in \mathbb{R}$, and let $x \in E$ satisfy $b + \langle n, x \rangle > 0$.
Then the distance from $x$ to the hyperplane $\{y : b + \langle n, y \rangle = 0\}$ is
$$\frac{b + \langle n, x \rangle}{\|n\|}.$$
-/
theorem affineBarrier_hyperplane_distance {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n x : E} {b : ℝ}
    (hn : n ≠ 0) (hx : 0 < b + inner ℝ n x) :
    infDist x {y : E | b + inner ℝ n y = 0} = (b + inner ℝ n x) / ‖n‖ := by
  have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn
  let a := b + inner ℝ n x
  let y := x - (a / ‖n‖ ^ 2) • n
  have hy : y ∈ {v : E | b + inner ℝ n v = 0} := by
    change b + inner ℝ n (x - (a / ‖n‖ ^ 2) • n) = 0
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hnpos).ne']
    dsimp only [a]
    ring
  have hdist : dist x y = a / ‖n‖ := by
    rw [dist_eq_norm, show x - y = (a / ‖n‖ ^ 2) • n by simp [y], norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg hx.le (sq_nonneg _))]
    field_simp [hnpos.ne']
    rfl
  refine le_antisymm ((infDist_le_dist_of_mem hy).trans_eq hdist) ?_
  apply (le_infDist ⟨y, hy⟩).mpr
  intro v hv
  change b + inner ℝ n v = 0 at hv
  have he : a = inner ℝ n (x - v) := by rw [inner_sub_right]; dsimp only [a]; linarith
  rw [dist_eq_norm]
  apply (div_le_iff₀ hnpos).mpr
  change a ≤ ‖x - v‖ * ‖n‖
  rw [he, mul_comm]
  exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Equation (13.10.8)** of [conn2000trust], ambient distance. For $x \in \mathbb{R}^\iota$ with
$\iota$ nonempty, the **ambient distance** is $\min_i x_i$.

For $x > 0$ this is the Euclidean distance from $x$ to the boundary of the positive orthant. The
definition is the minimum itself. -/
noncomputable def affineBarrierAmbientDistance (x : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty x

private noncomputable def movableBounds (w : ι → ℝ) : Finset ι :=
  open Classical in Finset.univ.filter fun i ↦ 0 < w i

omit [Nonempty ι] in
private theorem movableBounds_nonempty (w : ι → ℝ) (hw : ∃ i, 0 < w i) :
    (movableBounds w).Nonempty := by
  classical
  obtain ⟨i, hi⟩ := hw
  exact ⟨i, by simp [movableBounds, hi]⟩

/-- **Equations (13.10.8) and (13.10.10)** of [conn2000trust], relative distance. Let
$w \in \mathbb{R}^\iota$ have at least one positive entry. The **relative distance** of $x$ to
the boundary of the slice is
$$\min_{i : w_i > 0} \frac{x_i}{w_i},$$
the minimum in (13.10.10) after each hyperplane distance is evaluated by (13.10.13).

A coordinate with $w_i \le 0$ is constant on the slice and gives no hyperplane, so it does not
enter the minimum. -/
noncomputable def affineBarrierSliceDistance (w x : ι → ℝ) (hw : ∃ i, 0 < w i) : ℝ :=
  (movableBounds w).inf' (movableBounds_nonempty w hw) fun i ↦ x i / w i

/-- **Equation (13.10.15)** of [conn2000trust], the geometric factor. Let $w \in \mathbb{R}^\iota$
have at least one positive entry. The **normal factor** is $\omega = \min_{i : w_i > 0} w_i$,
the least positive length of a coordinate normal projected onto the equality nullspace. -/
noncomputable def affineBarrierNormalFactor (w : ι → ℝ) (hw : ∃ i, 0 < w i) : ℝ :=
  (movableBounds w).inf' (movableBounds_nonempty w hw) w

/-- **Equation (13.10.15)** of [conn2000trust]. Let $w, x \in \mathbb{R}^\iota$ with $x > 0$,
$w_i \le 1$ for all $i$ and $w_i > 0$ for some $i$. Suppose that some $i$ with $w_i > 0$ attains
the ambient distance, $\min_j x_j = x_i$. Then the normal factor satisfies $0 < \omega \le 1$
and
$$\omega \min_{j : w_j > 0} \frac{x_j}{w_j} \le \min_j x_j.$$
-/
theorem affineBarrier_normalFactor_mul_sliceDistance_le (w x : ι → ℝ) (hw : ∃ i, 0 < w i)
    (hx : ∀ i, 0 < x i) (hunit : ∀ i, w i ≤ 1)
    (hmovable : ∃ i, 0 < w i ∧ affineBarrierAmbientDistance x = x i) :
    affineBarrierNormalFactor w hw ∈ Ioc (0 : ℝ) 1 ∧
      affineBarrierNormalFactor w hw * affineBarrierSliceDistance w x hw ≤
        affineBarrierAmbientDistance x := by
  classical
  obtain ⟨i, hi, hdist⟩ := hmovable
  have him : i ∈ movableBounds w := by simp [movableBounds, hi]
  have hpos : 0 < affineBarrierNormalFactor w hw := by
    unfold affineBarrierNormalFactor
    rw [Finset.lt_inf'_iff]
    intro j hj
    exact (Finset.mem_filter.mp (show j ∈ Finset.univ.filter _ from hj)).2
  have hwle : affineBarrierNormalFactor w hw ≤ w i := Finset.inf'_le _ him
  have hsle : affineBarrierSliceDistance w x hw ≤ x i / w i := Finset.inf'_le _ him
  refine ⟨⟨hpos, hwle.trans (hunit i)⟩, ?_⟩
  calc
    _ ≤ affineBarrierNormalFactor w hw * (x i / w i) :=
      mul_le_mul_of_nonneg_left hsle hpos.le
    _ ≤ w i * (x i / w i) := mul_le_mul_of_nonneg_right hwle (div_nonneg (hx i).le hi.le)
    _ = x i := mul_div_cancel₀ _ hi.ne'
    _ = _ := hdist.symm

/-- **Lemma 13.10.1** of [conn2000trust]. Let $w, c \in \mathbb{R}^\iota$ with $w_i \le 1$ for all
$i$, $w_i > 0$ for some $i$, and $c_i > 0$ whenever $w_i \le 0$. Write $d_A(x) = \min_i x_i$ and
$d_S(x) = \min_{w_i > 0} x_i / w_i$. There is $\sigma \in (0, 1)$ such that every $x > 0$ with
$x_i = c_i$ whenever $w_i \le 0$ satisfies
$$d_A(x) \le d_S(x) \quad\text{and}\quad \sigma \min\{1, d_S(x)\} \le d_A(x).$$

The lemma is stated in orthonormal coordinates on the slice. The weights $w_i$ are the lengths
of the projected normals, so they are at most one. The comparison is uniform over the whole
positive slice. A positive weight is needed for the boundary of the slice to be nonempty. -/
theorem lemma_13_10_1 (w c : ι → ℝ) (hw : ∃ i, 0 < w i)
    (hunit : ∀ i, w i ≤ 1) (hc : ∀ i, w i ≤ 0 → 0 < c i) :
    ∃ σ ∈ Ioo (0 : ℝ) 1, ∀ x : ι → ℝ, (∀ i, 0 < x i) →
      (∀ i, w i ≤ 0 → x i = c i) →
      affineBarrierAmbientDistance x ≤ affineBarrierSliceDistance w x hw ∧
      σ * min 1 (affineBarrierSliceDistance w x hw) ≤ affineBarrierAmbientDistance x := by
  classical
  let T := Finset.univ.image (fun i ↦ if 0 < w i then w i else c i)
  have hT : T.Nonempty := Finset.univ_nonempty.image _
  let σ := min (1 / 2) (T.inf' hT id)
  have hσ : σ ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨lt_min (by norm_num) ((Finset.lt_inf'_iff hT (f := id)).mpr ?_), ?_⟩
    · intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      by_cases hi : 0 < w i
      · simp [hi]
      · simpa [hi] using hc i (le_of_not_gt hi)
    · exact (min_le_left _ _).trans_lt (by norm_num)
  have hσi (i : ι) : σ ≤ if 0 < w i then w i else c i :=
    (min_le_right _ _).trans (Finset.inf'_le id (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  refine ⟨σ, hσ, fun x hx hconst ↦ ⟨?_, ?_⟩⟩
  · unfold affineBarrierSliceDistance
    apply Finset.le_inf'
    intro i hi
    have hp : 0 < w i := (Finset.mem_filter.mp (show i ∈ Finset.univ.filter _ from hi)).2
    exact (Finset.inf'_le x (Finset.mem_univ i)).trans
      ((le_div_iff₀ hp).mpr (by nlinarith [mul_nonneg (hx i).le (sub_nonneg.mpr (hunit i))]))
  · unfold affineBarrierAmbientDistance
    apply Finset.le_inf'
    intro i _
    by_cases hp : 0 < w i
    · have hr : affineBarrierSliceDistance w x hw ≤ x i / w i :=
        Finset.inf'_le _ (by simp [movableBounds, hp])
      have hσw : σ ≤ w i := by simpa [hp] using hσi i
      have hpos : 0 ≤ x i / w i := div_nonneg (hx i).le hp.le
      calc
        _ ≤ σ * (x i / w i) := mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hr) hσ.1.le
        _ ≤ w i * (x i / w i) := mul_le_mul_of_nonneg_right hσw hpos
        _ = x i := mul_div_cancel₀ _ hp.ne'
    · have hσc : σ ≤ c i := by simpa [hp] using hσi i
      exact ((mul_le_mul_of_nonneg_left (min_le_left _ _) hσ.1.le).trans_eq
        (mul_one _)).trans (hσc.trans_eq (hconst i (le_of_not_gt hp)).symm)

/-- **Theorem 13.10.2** of [conn2000trust]. Let $w$, $c$, $d_A$ and $d_S$ be as in Lemma 13.10.1,
and let $\sigma \in (0, 1)$. There is $\theta \in (0, 1)$ with the following property. Let
$x, y > 0$ satisfy $x_i = y_i = c_i$ whenever $w_i \le 0$. If $\sigma d_A(x) \le d_A(y)$ and
$d_S(x) \le 1$, then
$$\theta\, d_S(x) \le d_S(y).$$
So an ambient fraction-to-boundary test implies a relative one whenever the current relative
distance is at most one. -/
theorem theorem_13_10_2 (w c : ι → ℝ) (hw : ∃ i, 0 < w i)
    (hunit : ∀ i, w i ≤ 1) (hc : ∀ i, w i ≤ 0 → 0 < c i)
    {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    ∃ θ ∈ Ioo (0 : ℝ) 1, ∀ x y : ι → ℝ, (∀ i, 0 < x i) → (∀ i, 0 < y i) →
      (∀ i, w i ≤ 0 → x i = c i ∧ y i = c i) →
      σ * affineBarrierAmbientDistance x ≤ affineBarrierAmbientDistance y →
      affineBarrierSliceDistance w x hw ≤ 1 →
      θ * affineBarrierSliceDistance w x hw ≤ affineBarrierSliceDistance w y hw := by
  obtain ⟨a, ha, hb⟩ := lemma_13_10_1 w c hw hunit hc
  refine ⟨σ * a, ⟨mul_pos hσ.1 ha.1, (mul_lt_of_lt_one_right hσ.1 ha.2).trans hσ.2⟩, ?_⟩
  intro x y hx hy hconst hstep hsmall
  have hx' := (hb x hx (fun i hi ↦ (hconst i hi).1)).2
  rw [min_eq_right hsmall] at hx'
  rw [mul_assoc]
  exact ((mul_le_mul_of_nonneg_left hx' hσ.1.le).trans hstep).trans
    (hb y hy (fun i hi ↦ (hconst i hi).2)).1

end ConnGouldToint.Chapter13
