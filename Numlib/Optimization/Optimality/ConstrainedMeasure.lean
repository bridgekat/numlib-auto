/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Basic.Real.Pointwise
import Numlib.Optimization.Descent
import Numlib.Optimization.Optimality.Approximate

/-!
# Criticality measures over admissible displacements

Let $E$ be a real normed space, let $A$ be a continuous $j$-linear form on $E$, write $A[d]^j$ for
$A(d, \dots, d)$, and let $\mathcal{B}$ be the closed unit ball of $E$. The constrained criticality
measures (6.1.5), (6.1.7), (6.1.9), (6.2.3)–(6.2.5) and (7.1.2) of [cartis2022evaluation] all have
the form
$$\omega = -\min_{d \in T \cap \mathcal{B}} A[d]^j = \sup_{d \in T \cap \mathcal{B}}
  \bigl(-A[d]^j\bigr),$$
where $A$ is a derivative tensor of the objective or of a model and $T$ is a set of admissible
displacements. The set $T$ is either the set $\mathcal{C}(x) = \{d \mid x + d \in C\}$ of feasible
steps of (6.1.2), or a restricted subset $\{d \in T \mid |B[d]^i| \le a\}$ as in (6.1.8), (6.1.10),
(6.2.1) and (6.2.2).

This file defines these sets and the measure $\omega$, and proves the facts that the analysis of
Chapters 6 and 7 of [cartis2022evaluation] uses: nonnegativity, monotonicity, stability under
perturbation of $A$, positive homogeneity, and the identification of the first-order measure with
$\|\nabla f(x)\|$ without constraints and with the first-order condition (1.1.6) on a convex set.

## Main definitions

* `Optimization.feasibleSteps`: the feasible displacements $\mathcal{C}(x) = \{d \mid x + d \in C\}$
  of (1.1.7) and (6.1.2).
* `Optimization.formCriticality`: the measure $\sup_{d \in T \cap \mathcal{B}} (-A[d]^j)$.
* `Optimization.restrictedSteps`: the restricted set $\{d \in T \mid |B[d]^i| \le a\}$.

## Main results

* `Optimization.formCriticality_nonneg`: if $j \ge 1$ and $0 \in T$, then $\omega \ge 0$.
* `Optimization.formCriticality_le_iff`: $\omega \le \varepsilon$ if and only if
  $A[d]^j \ge -\varepsilon$ for all $d \in T \cap \mathcal{B}$, the form of the termination tests.
* `Optimization.formCriticality_mono`: $\omega$ is monotone in the admissible set.
* `Optimization.formCriticality_le_add_of_abs_sub_le`,
  `Optimization.abs_formCriticality_sub_le_norm`: $\omega$ changes by at most $e$ when $A[d]^j$
  changes by at most $e$ on $T \cap \mathcal{B}$, and is $1$-Lipschitz in $A$.
* `Optimization.formCriticality_smul`: $\omega$ is positively homogeneous in $A$.
* `Optimization.inter_closedBall_restrictedSteps_subset`: the transfer of restricted sets in the
  proof of Theorem 6.2.3.
* `Optimization.formCriticality_one_univ`: without constraints, the first-order measure is $\|A\|$,
  that is, $\|\nabla f(x)\|$.
* `Optimization.formCriticality_eq_zero_iff`: on a convex set, the first-order measure vanishes
  exactly at the points that satisfy the first-order condition (1.1.6).
* `Optimization.exists_formCriticality_eq`: in finite dimension, the supremum is attained.

## Implementation notes

* The source writes the measures (6.1.5) and (6.1.9) as $-\min$; they are nonnegative, compare
  (6.2.3) and (7.1.2). The Lean measure is a supremum: it is `Optimization.decrementMeasure` of
  radius $1$ of the decrease $d \mapsto -A[d]^j$. The supremum is finite because the values are
  bounded by $\|A\|$. It is a maximum in finite dimension when $T$ is closed.
* The supremum is `sSup` in $\mathbb{R}$, so the measure is $0$ when $T \cap \mathcal{B}$ is empty.
-/

open Set Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Optimization

/-! ### Feasible displacements -/

section FeasibleSteps

/-- The **feasible displacements** at $x$ for a set $C \subseteq E$:
$$\mathcal{C}(x) = \{d \in E \mid x + d \in C\},$$
as in (1.1.7) and (6.1.2) of [cartis2022evaluation].

The set $\mathcal{M}^0_k(s)$ of the model in (6.2.1) is
`Optimization.feasibleSteps C (x_k + s)`. -/
def feasibleSteps (C : Set E) (x : E) : Set E := {d | x + d ∈ C}

variable {C : Set E} {x d : E}

omit [NormedSpace ℝ E] in
/-- A displacement $d$ is feasible at $x$ if and only if $x + d \in C$. -/
@[simp]
theorem mem_feasibleSteps : d ∈ feasibleSteps C x ↔ x + d ∈ C := Iff.rfl

omit [NormedSpace ℝ E] in
/-- The feasible displacements at $x$ are the preimage of $C$ under the translation
$d \mapsto x + d$. -/
theorem feasibleSteps_eq_preimage (C : Set E) (x : E) :
    feasibleSteps C x = (fun d => x + d) ⁻¹' C := rfl

omit [NormedSpace ℝ E] in
/-- The zero displacement is feasible at $x$ if and only if $x \in C$. -/
@[simp]
theorem zero_mem_feasibleSteps : 0 ∈ feasibleSteps C x ↔ x ∈ C := by
  simp

/-- If $C$ is convex, then the feasible displacements $\mathcal{C}(x)$ form a convex set. -/
theorem convex_feasibleSteps (hC : Convex ℝ C) (x : E) : Convex ℝ (feasibleSteps C x) :=
  hC.translate_preimage_right x

omit [NormedSpace ℝ E] in
/-- If $C$ is closed, then the feasible displacements $\mathcal{C}(x)$ form a closed set. -/
theorem isClosed_feasibleSteps (hC : IsClosed C) (x : E) : IsClosed (feasibleSteps C x) :=
  hC.preimage (continuous_const.add continuous_id)

/-- Let $C$ be convex and $x \in C$. If $d \in \mathcal{C}(x)$ and $0 \le t \le 1$, then
$t d \in \mathcal{C}(x)$: a feasible displacement can be shortened. -/
theorem smul_mem_feasibleSteps (hC : Convex ℝ C) (hx : x ∈ C) (hd : d ∈ feasibleSteps C x)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t • d ∈ feasibleSteps C x := by
  exact (convex_feasibleSteps hC x).smul_mem_of_zero_mem (zero_mem_feasibleSteps.2 hx) hd
    ⟨ht0, ht1⟩

end FeasibleSteps

/-! ### The criticality measure of a multilinear form -/

section FormCriticality

variable {j : ℕ}

/-- The **criticality measure** of a continuous $j$-linear form $A$ over a set $T$ of admissible
displacements:
$$\omega(A, T) = \sup_{d \in T,\ \|d\| \le 1} \bigl(-A[d]^j\bigr).$$
This is the quantity $-\min_{d \in T \cap \mathcal{B}} A[d]^j$ of (6.1.5), (6.1.7), (6.1.9),
(6.2.3)–(6.2.5) and (7.1.2) of [cartis2022evaluation].

The measure is `Optimization.decrementMeasure` of radius $1$ of the decrease
$d \mapsto -A[d]^j$. The supremum is `sSup` in $\mathbb{R}$, so $\omega(A, T) = 0$ when no
$d \in T$ has $\|d\| \le 1$. -/
noncomputable def formCriticality (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ)
    (T : Set E) : ℝ :=
  decrementMeasure (fun d => -A fun _ => d) 1 T

variable (A B : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ) {T T' : Set E}

/-- If $\|d\| \le 1$, then $|A[d]^j| \le \|A\|$. -/
theorem abs_apply_le_norm_of_mem_closedBall {d : E} (hd : d ∈ closedBall (0 : E) 1) :
    |A fun _ => d| ≤ ‖A‖ := by
  have hd' : ‖d‖ ≤ 1 := by simpa using hd
  calc |A fun _ => d| = ‖A fun _ => d‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖A‖ * ∏ _i : Fin j, ‖d‖ := A.le_opNorm _
    _ ≤ ‖A‖ * 1 := by
        gcongr
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) hd'
    _ = ‖A‖ := mul_one _

/-- For every set $T$, the values $-A[d]^j$ for $d \in T \cap \mathcal{B}$ are bounded above. -/
theorem bddAbove_formCriticality (T : Set E) :
    BddAbove ((fun d => -A fun _ => d) '' (closedBall 0 1 ∩ T)) := by
  refine ⟨‖A‖, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  exact (neg_le_abs _).trans (abs_apply_le_norm_of_mem_closedBall A hd.1)

/-- Every admissible displacement $d \in T \cap \mathcal{B}$ gives the lower bound
$-A[d]^j \le \omega(A, T)$. -/
theorem le_formCriticality {d : E} (hd : d ∈ closedBall 0 1 ∩ T) :
    (-A fun _ => d) ≤ formCriticality A T :=
  le_decrementMeasure (bddAbove_formCriticality A T) hd

/-- If $T \cap \mathcal{B}$ is nonempty and $-A[d]^j \le \varepsilon$ for all
$d \in T \cap \mathcal{B}$, then $\omega(A, T) \le \varepsilon$. -/
theorem formCriticality_le {ε : ℝ} (hT : (closedBall 0 1 ∩ T).Nonempty)
    (h : ∀ d ∈ closedBall 0 1 ∩ T, (-A fun _ => d) ≤ ε) : formCriticality A T ≤ ε :=
  decrementMeasure_le hT h

omit [NormedSpace ℝ E] in
/-- If $0 \in T$, then $0 \in \mathcal{B} \cap T$. -/
theorem zero_mem_closedBall_inter (hT : 0 ∈ T) : (0 : E) ∈ closedBall 0 1 ∩ T :=
  ⟨mem_closedBall_self zero_le_one, hT⟩

/-- Let $j \ge 1$ and $0 \in T$. Then the criticality measure is nonnegative: $\omega(A, T) \ge 0$.
Compare (6.1.5) of [cartis2022evaluation].

The displacement $d = 0$ gives the value $-A[0]^j = 0$, which needs $j \ge 1$. -/
theorem formCriticality_nonneg (hj : 1 ≤ j) (hT : 0 ∈ T) : 0 ≤ formCriticality A T := by
  have h := le_formCriticality A (zero_mem_closedBall_inter hT)
  have : (A fun _ => (0 : E)) = 0 := A.map_coord_zero ⟨0, hj⟩ rfl
  simpa [this] using h

/-- Let $0 \in T$. Then $\omega(A, T) \le \varepsilon$ if and only if
$$A[d]^j \ge -\varepsilon \quad \text{for all } d \in T \text{ with } \|d\| \le 1.$$
This is the form in which the termination tests (6.2.8), (6.2.9) and (7.1.4) of
[cartis2022evaluation] are used. -/
theorem formCriticality_le_iff (hT : 0 ∈ T) {ε : ℝ} :
    formCriticality A T ≤ ε ↔ ∀ d ∈ closedBall 0 1 ∩ T, -ε ≤ A fun _ => d := by
  constructor
  · intro h d hd
    linarith [le_formCriticality A hd]
  · intro h
    exact formCriticality_le A ⟨0, zero_mem_closedBall_inter hT⟩ fun d hd => by
      linarith [h d hd]

/-- Let $T \cap \mathcal{B}$ be nonempty and $T \cap \mathcal{B} \subseteq T'$. Then
$\omega(A, T) \le \omega(A, T')$.

Only the part of $T$ in the unit ball matters. -/
theorem formCriticality_mono (hT : (closedBall 0 1 ∩ T).Nonempty)
    (hTT' : closedBall 0 1 ∩ T ⊆ T') : formCriticality A T ≤ formCriticality A T' :=
  formCriticality_le A hT fun _ hd => le_formCriticality A ⟨hd.1, hTT' hd⟩

/-- Let $A$ and $B$ be continuous $j$-linear forms, let $T \cap \mathcal{B}$ be nonempty, and
suppose that $|A[d]^j - B[d]^j| \le e$ for all $d \in T \cap \mathcal{B}$. Then
$$|\omega(A, T) - \omega(B, T)| \le e.$$
This is the step "(6.2.23) $\Rightarrow$ …" in the proof of Lemma 6.2.1 of
[cartis2022evaluation]. -/
theorem abs_formCriticality_sub_le (hT : (closedBall 0 1 ∩ T).Nonempty) {e : ℝ}
    (h : ∀ d ∈ closedBall 0 1 ∩ T, |(A fun _ => d) - B fun _ => d| ≤ e) :
    |formCriticality A T - formCriticality B T| ≤ e :=
  abs_decrementMeasure_sub_le hT (bddAbove_formCriticality A T) (bddAbove_formCriticality B T)
    fun d hd => by rw [neg_sub_neg, abs_sub_comm]; exact h d hd

/-- Let $A$ and $B$ be continuous $j$-linear forms, let $T \cap \mathcal{B}$ be nonempty, and
suppose that $|A[d]^j - B[d]^j| \le e$ for all $d \in T \cap \mathcal{B}$. Then
$$\omega(A, T) \le \omega(B, T) + e.$$
This is the one-sided form of `Optimization.abs_formCriticality_sub_le`. -/
theorem formCriticality_le_add_of_abs_sub_le (hT : (closedBall 0 1 ∩ T).Nonempty) {e : ℝ}
    (h : ∀ d ∈ closedBall 0 1 ∩ T, |(A fun _ => d) - B fun _ => d| ≤ e) :
    formCriticality A T ≤ formCriticality B T + e := by
  linarith [(abs_le.1 (abs_formCriticality_sub_le A B hT h)).2]

/-- If $T \cap \mathcal{B}$ is nonempty, then $|\omega(A, T) - \omega(B, T)| \le \|A - B\|$: the
measure is $1$-Lipschitz in the form for the operator norm. -/
theorem abs_formCriticality_sub_le_norm (hT : (closedBall 0 1 ∩ T).Nonempty) :
    |formCriticality A T - formCriticality B T| ≤ ‖A - B‖ :=
  abs_formCriticality_sub_le A B hT fun d hd => by
    simpa using abs_apply_le_norm_of_mem_closedBall (A - B) hd.1

/-- For $c \ge 0$ and every set $T$, $\omega(cA, T) = c \, \omega(A, T)$. This positive homogeneity
is used in Lemma 7.2.1 of [cartis2022evaluation]. -/
theorem formCriticality_smul {c : ℝ} (hc : 0 ≤ c) (T : Set E) :
    formCriticality (c • A) T = c * formCriticality A T := by
  rw [formCriticality, formCriticality, decrementMeasure_def, decrementMeasure_def, ← smul_eq_mul,
    ← Real.sSup_smul_of_nonneg hc,
    ← Set.image_smul, Set.image_image]
  congr 1
  refine Set.image_congr fun _ _ => ?_
  simp

/-- For a continuous linear form $A$ (the case $j = 1$), the unconstrained measure is the norm:
$\omega(A, E) = \|A\|$. With $A = \nabla f(x)$ this is $\|\nabla f(x)\|$, as in the remark after
(6.1.10) of [cartis2022evaluation]. -/
theorem formCriticality_one_univ (A : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) :
    formCriticality A univ = ‖A‖ := by
  set ℓ : E →L[ℝ] ℝ := continuousMultilinearCurryFin1 ℝ E ℝ A
  have hℓ : ∀ s, ℓ s = A fun _ => s := fun s => by
    simp only [ℓ, continuousMultilinearCurryFin1_apply]
    congr 1
  rw [formCriticality, decrementMeasure_def, inter_univ]
  have : (fun d => -A fun _ => d) = fun s => -ℓ s := funext fun s => by rw [hℓ]
  rw [this, sSup_neg_apply_closedBall ℓ zero_le_one, one_mul]
  exact (continuousMultilinearCurryFin1 ℝ E ℝ).norm_map A

/-- For every $f : E \to \mathbb{R}$ and $x \in E$, the unconstrained first-order measure is
$\omega(\nabla f(x), E) = \|\nabla f(x)\|$.

Here $\nabla f(x)$ is `iteratedFDeriv ℝ 1 f x` in the measure and `fderiv ℝ f x` in the norm. No
differentiability is assumed; if $f$ is not differentiable at $x$, both sides are $0$. -/
theorem formCriticality_iteratedFDeriv_one_univ (f : E → ℝ) (x : E) :
    formCriticality (iteratedFDeriv ℝ 1 f x) univ = ‖fderiv ℝ f x‖ := by
  rw [formCriticality_one_univ, norm_iteratedFDeriv_one]

/-- For every $f : E \to \mathbb{R}$ and $x \in E$, the unconstrained first-order measure satisfies
$\omega(\nabla f(x), E) \le \varepsilon$ if and only if $\|\nabla f(x)\| \le \varepsilon$, the
test (2.1.2) of [cartis2022evaluation] (`Optimization.IsApproxFirstOrder`). -/
theorem formCriticality_iteratedFDeriv_one_univ_le_iff (f : E → ℝ) (x : E) {ε : ℝ} :
    formCriticality (iteratedFDeriv ℝ 1 f x) univ ≤ ε ↔ IsApproxFirstOrder f x ε := by
  rw [formCriticality_iteratedFDeriv_one_univ, isApproxFirstOrder_iff]

/-- For a formal multilinear series $D$ and a set $T$, the first-order criticality measure of the
linear term $D_1$ over $T$ is the first-order Taylor measure of radius $1$ over $T$:
$$\omega(D_1, T) = \sup_{d \in T,\ \|d\| \le 1} \bigl(T_1(0) - T_1(d)\bigr),$$
where $T_1$ is the first-order Taylor sum of $D$. This links the measure to (12.1.12) and
(14.2.2) of [cartis2022evaluation]; the right side is `Optimization.taylorMeasure D 1 1 T`. -/
theorem formCriticality_eq_taylorMeasure_one (D : FormalMultilinearSeries ℝ E ℝ) (T : Set E) :
    formCriticality (D 1) T = taylorMeasure D 1 1 T := by
  rw [formCriticality, taylorMeasure]
  congr 1
  funext d
  rw [FormalMultilinearSeries.taylorDecrement_one_apply]

/-- Let $C$ be convex, $x \in C$, and let $A$ be a continuous linear form. Then the first-order
measure over the feasible displacements vanishes if and only if $A$ satisfies the first-order
condition:
$$\omega(A, \mathcal{C}(x)) = 0 \iff A[y - x] \ge 0 \text{ for all } y \in C.$$
With $A = \nabla f(x)$ this is the first-order condition (1.1.6) of [cartis2022evaluation]. -/
theorem formCriticality_eq_zero_iff {C : Set E} (hC : Convex ℝ C) {x : E} (hx : x ∈ C)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) :
    formCriticality A (feasibleSteps C x) = 0 ↔ ∀ y ∈ C, 0 ≤ A fun _ => y - x := by
  have h0 : (0 : E) ∈ feasibleSteps C x := zero_mem_feasibleSteps.2 hx
  have hlin : ∀ (c : ℝ) (v : E), (A fun _ => c • v) = c * A fun _ => v := fun c v => by
    rw [A.apply_smul_diag, pow_one, smul_eq_mul]
  rw [le_antisymm_iff, and_iff_left (formCriticality_nonneg A le_rfl h0),
    formCriticality_le_iff A h0]
  simp only [neg_zero]
  constructor
  · intro h y hy
    have hd : y - x ∈ feasibleSteps C x := by simpa using hy
    rcases le_or_gt ‖y - x‖ 1 with hle | hgt
    · exact h _ ⟨by simpa using hle, hd⟩
    · have hpos : 0 < ‖y - x‖ := by linarith
      have hmem : ‖y - x‖⁻¹ • (y - x) ∈ closedBall (0 : E) 1 ∩ feasibleSteps C x :=
        ⟨by simp [norm_smul, hpos.ne'],
          smul_mem_feasibleSteps hC hx hd (inv_nonneg.2 hpos.le) (inv_le_one_of_one_le₀ hgt.le)⟩
      have := h _ hmem
      rw [hlin] at this
      exact nonneg_of_mul_nonneg_right (by linarith) (inv_pos.2 hpos)
  · intro h d hd
    simpa using h (x + d) hd.2

/-- Let $C$ be convex, $x \in C$ and $f : E \to \mathbb{R}$. Then
$$\omega(\nabla f(x), \mathcal{C}(x)) = 0 \iff \nabla f(x)[y - x] \ge 0 \text{ for all } y \in
  C,$$
which is the first-order condition (1.1.6) of [cartis2022evaluation].

No differentiability is assumed. Here $\nabla f(x)$ is `iteratedFDeriv ℝ 1 f x` in the measure
and `fderiv ℝ f x` in the condition. -/
theorem formCriticality_fderiv_eq_zero_iff {f : E → ℝ} {C : Set E} (hC : Convex ℝ C) {x : E}
    (hx : x ∈ C) :
    formCriticality (iteratedFDeriv ℝ 1 f x) (feasibleSteps C x) = 0 ↔
      ∀ y ∈ C, 0 ≤ fderiv ℝ f x (y - x) := by
  simp only [formCriticality_eq_zero_iff hC hx, iteratedFDeriv_one_apply]

/-- Let $C$ be convex, $x \in C$, and let $f : E \to \mathbb{R}$ be differentiable at $x$. If $x$ is
a local minimizer of $f$ on $C$, then $\omega(\nabla f(x), \mathcal{C}(x)) = 0$. -/
theorem formCriticality_eq_zero_of_isLocalMinOn {f : E → ℝ} {C : Set E} (hC : Convex ℝ C)
    {x : E} (hx : x ∈ C) (hmin : IsLocalMinOn f C x) (hf : DifferentiableAt ℝ f x) :
    formCriticality (iteratedFDeriv ℝ 1 f x) (feasibleSteps C x) = 0 := by
  rw [formCriticality_fderiv_eq_zero_iff hC hx]
  intro y hy
  exact Descent.fderiv_apply_sub_nonneg_of_isLocalMinOn (f' := fderiv ℝ f) hC hx hmin
    hf.hasFDerivAt y hy

/-- Let $E$ be finite-dimensional, let $T$ be closed, and let $T \cap \mathcal{B}$ be nonempty. Then
the supremum in $\omega(A, T)$ is attained: there is $d \in T$ with $\|d\| \le 1$ and
$-A[d]^j = \omega(A, T)$. This justifies the $\min$ in the formulas of [cartis2022evaluation]. -/
theorem exists_formCriticality_eq [FiniteDimensional ℝ E] (hT : IsClosed T)
    (hne : (closedBall 0 1 ∩ T).Nonempty) :
    ∃ d ∈ closedBall 0 1 ∩ T, (-A fun _ => d) = formCriticality A T := by
  have hK : IsCompact (closedBall (0 : E) 1 ∩ T) := (isCompact_closedBall 0 1).inter_right hT
  have hc : Continuous fun d : E => -A fun _ => d :=
    (A.cont.comp (continuous_pi fun _ => continuous_id)).neg
  obtain ⟨d, hd, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
  rw [formCriticality, decrementMeasure_def]
  refine ⟨d, hd, (IsGreatest.csSup_eq (s := (fun d => -A fun _ => d) '' (closedBall 0 1 ∩ T))
    (a := -A fun _ => d) ⟨⟨d, hd, rfl⟩, ?_⟩).symm⟩
  rintro _ ⟨e, he, rfl⟩
  exact hmax he

end FormCriticality

/-! ### Restricted admissible sets -/

section RestrictedSteps

variable {i j : ℕ}

/-- The **restricted set** of displacements in $T$ on which a continuous $i$-linear form $B$ is
small:
$$\{d \in T \mid |B[d]^i| \le a\}.$$
In [cartis2022evaluation], the set $\mathcal{C}^1(x, \alpha)$ of (6.1.8) is the restricted set
with $B = \nabla f(x)$, bound $a = \tau_1 \alpha$ and $T = \mathcal{C}(x)$. The set
$\mathcal{C}^2(x, \alpha_1, \alpha_2)$ of (6.1.10) is the restricted set with
$B = \nabla^2 f(x)$, bound $a = \tau_2 \alpha_2$ and $T = \mathcal{C}^1(x, \alpha_1)$. The sets
(6.2.1) and (6.2.2) are the model counterparts. -/
def restrictedSteps (B : ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ) (a : ℝ) (T : Set E) :
    Set E :=
  {d ∈ T | |B fun _ => d| ≤ a}

variable {B : ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ} {a b : ℝ} {T T' : Set E}

/-- A displacement $d$ is in the restricted set if and only if $d \in T$ and $|B[d]^i| \le a$. -/
@[simp]
theorem mem_restrictedSteps {d : E} :
    d ∈ restrictedSteps B a T ↔ d ∈ T ∧ |B fun _ => d| ≤ a := Iff.rfl

/-- The restricted set is a subset of $T$. -/
theorem restrictedSteps_subset : restrictedSteps B a T ⊆ T := fun _ hd => hd.1

/-- Let $i \ge 1$ and $a \ge 0$. Then $0$ is in the restricted set $\{d \in T \mid |B[d]^i| \le a\}$
if and only if $0 \in T$. -/
theorem zero_mem_restrictedSteps (hi : 1 ≤ i) (ha : 0 ≤ a) :
    0 ∈ restrictedSteps B a T ↔ 0 ∈ T := by
  have : (B fun _ => (0 : E)) = 0 := B.map_coord_zero ⟨0, hi⟩ rfl
  simp [this, ha]

/-- If $a \le b$ and $T \subseteq T'$, then $\{d \in T \mid |B[d]^i| \le a\} \subseteq \{d \in T'
\mid |B[d]^i| \le b\}$. -/
theorem restrictedSteps_mono (hab : a ≤ b) (hT : T ⊆ T') :
    restrictedSteps B a T ⊆ restrictedSteps B b T' :=
  fun _ hd => ⟨hT hd.1, hd.2.trans hab⟩

/-- Transfer of restricted sets. Let $A$ and $B$ be continuous $i$-linear forms with
$|A[d]^i - B[d]^i| \le e$ for all $d \in T \cap \mathcal{B}$, and let $e + a \le b$. Then
$$\mathcal{B} \cap \{d \in T \mid |A[d]^i| \le a\} \subseteq \{d \in T \mid |B[d]^i| \le b\}.$$

This is the inclusion $\mathcal{C}^1(x_{k+1}, \varepsilon_1) \cap \mathcal{B} \subseteq
\mathcal{M}^1_k(s_k)$ in the proof of Theorem 6.2.3 of [cartis2022evaluation]. The intersection
with $\mathcal{B}$ is needed because the estimate (6.2.23) holds on the unit ball only. -/
theorem inter_closedBall_restrictedSteps_subset
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin i => E) ℝ) {e : ℝ}
    (h : ∀ d ∈ closedBall 0 1 ∩ T, |(A fun _ => d) - B fun _ => d| ≤ e) (hab : e + a ≤ b) :
    closedBall 0 1 ∩ restrictedSteps A a T ⊆ restrictedSteps B b T := by
  rintro d ⟨hd, hdT, hA⟩
  refine ⟨hdT, ?_⟩
  have := h d ⟨hd, hdT⟩
  calc |B fun _ => d| ≤ |(A fun _ => d) - B fun _ => d| + |A fun _ => d| := by
        have := abs_sub_abs_le_abs_sub (B fun _ => d) (A fun _ => d)
        rw [abs_sub_comm] at this
        linarith
    _ ≤ e + a := add_le_add this hA
    _ ≤ b := hab

end RestrictedSteps

end Optimization
