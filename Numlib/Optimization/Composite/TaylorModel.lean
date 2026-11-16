/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.HighOrder.MeasureTest
import Numlib.Analysis.Calculus.MultivariateTaylor.Remainder
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Generalized Taylor models and criticality of composite functions

Consider a composite objective $w = f + h \circ c$ with $f : E \to \mathbb{R}$ and $c : E \to F$
smooth and $h : F \to \mathbb{R}$ Lipschitz and possibly nonsmooth. Following §14.1 of
[cartis2022evaluation], the *generalized Taylor model* of order $j$ at $x$ is
$$T_{w,j}(x, s) = T_{f,j}(x, s) + h(T_{c,j}(x, s)),$$
as in (14.1.5): the Taylor polynomials of $f$ and $c$ are used, but $h$ is kept exactly. The
composite criticality measure (14.1.6) is $\varphi^\delta_{w,j}(x) = w(x) - \min_{\|d\| \le \delta}
T_{w,j}(x, d)$, the largest decrease of the model over the ball of radius $\delta$.

This module builds these objects from derivative data $D_f$ and $D_c$, that is, from sequences of
multilinear maps, with the Taylor sums $T_{f,j}(d) = \sum_{i=0}^{j} \frac{1}{i!} D_{f,i}[d]^i$ and
$T_{c,j}(d) = \sum_{i=0}^{j} \frac{1}{i!} D_{c,i}[d]^i$. It defines the decrement
$\Delta T_{w,j}(d) = T_{w,j}(0) - T_{w,j}(d)$, the measure $\varphi^\delta_{w,j}$ as the supremum of
$\Delta T_{w,j}$ over the feasible displacements $d \in S$ with $\|d\| \le \delta$, and the
$(\varepsilon, \delta)$-approximate optimality condition (14.1.9). It proves that the measure is
finite, nonnegative, monotone and attained in finite dimension, the first-order necessary condition
of Lemma 14.1.1, and the bound on the remainder $|w(x + s) - T_{w,p}(x, s)|$ used in the proof of
Lemma 14.1.6.

## Main definitions

* `Optimization.IsSubadditive`: $h(a + b) \le h(a) + h(b)$ for all $a, b$.
* `Optimization.HasLipschitzConst`: $h$ is Lipschitz with a real constant $L \ge 0$.
* `Optimization.compositeTaylorDecrement`: the decrement
  $\Delta T_{w,j}(d) = T_{w,j}(0) - T_{w,j}(d)$.
* `Optimization.compositeTaylorMeasure`: the measure $\varphi^\delta_{w,j}$ of (14.1.6) over a set
  $S$ of feasible displacements.
* `Optimization.IsEpsDeltaApproxComposite`: the condition (14.1.9), $\varphi^{\delta_j}_{w,j} \le
  \varepsilon_j \delta_j^j / j!$ for $1 \le j \le q$.

## Main results

* `Optimization.abs_compositeTaylorDecrement_le`: $|\Delta T_{w,j}(d)| \le \sum_{i=1}^{j}
  (\|D_{f,i}\| + L_h \|D_{c,i}\|) \|d\|^i / i!$, so the measure is a finite supremum.
* `Optimization.exists_compositeTaylorMeasure_eq`: in finite dimension, the supremum that defines
  the measure is attained.
* `Optimization.compositeTaylorDecrement_one_nonpos_of_isLocalMinOn`: at a local minimizer of $w$
  over a convex set, with $h$ convex, $\Delta T_{w,1}(x, s) \le 0$ for all feasible $s$ (Lemma
  14.1.1).
* `Optimization.abs_sub_compositeTaylor_le_of_lipschitz`: $|w(x + s) - T_{w,p}(x, s)| \le (L_f + L_h
  L_c) \|s\|^{p+1} / (p + 1)!$ (proof of Lemma 14.1.6).

## Implementation notes

* All definitions take derivative data `Df : FormalMultilinearSeries ℝ E ℝ` and
  `Dc : FormalMultilinearSeries ℝ E F`, as the core `Optimization.taylorMeasure` does. The data are
  `ftaylorSeries ℝ f x` and `ftaylorSeries ℝ c x` for the function itself. They are the jets at a
  trial step of the regularized model for the model measure of ARqpC (14.1.14).
* The measure is an instance of `Optimization.decrementMeasure` over a set `S` of feasible
  displacements. The unconstrained case is `S = univ`, and the constrained case of §14.2 of
  [cartis2022evaluation] is `S = {d | x + d ∈ X}`.
* `Optimization.IsSubadditive` is defined here because Mathlib's `Subadditive` is about sequences.
  The assumption h.S0 of [cartis2022evaluation] is subadditivity together with $h(0) = 0$, which the
  theorems assume separately.
* Lipschitz constants are real numbers, since they enter explicit bounds.
  `Optimization.HasLipschitzConst.of_lipschitzWith` converts from Mathlib's `LipschitzWith`.
-/

open Set Metric Finset Filter Topology
open scoped Nat

namespace Optimization

section Subadditive

/-- A function $h : F \to \mathbb{R}$ on an additive type is **subadditive** if
$h(a + b) \le h(a) + h(b)$ for all $a, b \in F$.

The assumption h.S0 of [cartis2022evaluation] asks for subadditivity and also for $h(0) = 0$;
the theorems below assume $h(0) = 0$ separately. Mathlib's `Subadditive` is a different notion,
about sequences. -/
def IsSubadditive {F : Type*} [Add F] (h : F → ℝ) : Prop := ∀ a b, h (a + b) ≤ h a + h b

/-- A seminorm $p$ on a real vector space is subadditive: $p(a + b) \le p(a) + p(b)$. -/
theorem _root_.Seminorm.isSubadditive {G : Type*} [AddCommGroup G] [Module ℝ G]
    (p : Seminorm ℝ G) :
    IsSubadditive (p : G → ℝ) :=
  fun a b => map_add_le_add p a b

variable {F : Type*} [NormedAddCommGroup F]

/-- The function $h : F \to \mathbb{R}$ **has Lipschitz constant** $L$ if $L \ge 0$ and
$|h(a) - h(b)| \le L \|a - b\|$ for all $a, b \in F$. This is the assumption h.L of
[cartis2022evaluation], with $L = L_{h,0}$.

The constant is a real number, since it enters explicit bounds.
`Optimization.HasLipschitzConst.of_lipschitzWith` converts from Mathlib's `LipschitzWith`. -/
structure HasLipschitzConst (h : F → ℝ) (L : ℝ) : Prop where
  /-- The constant is nonnegative: $L \ge 0$. -/
  nonneg : 0 ≤ L
  /-- The Lipschitz inequality $|h(a) - h(b)| \le L \|a - b\|$ for all $a, b$. -/
  abs_sub_le : ∀ a b, |h a - h b| ≤ L * ‖a - b‖

/-- If $h$ is Lipschitz with constant $K \ge 0$ in the sense of Mathlib's `LipschitzWith`, then $h$
has Lipschitz constant $K$. -/
theorem HasLipschitzConst.of_lipschitzWith {h : F → ℝ} {K : NNReal} (hK : LipschitzWith K h) :
    HasLipschitzConst h K :=
  ⟨K.2, fun a b => by simpa [Real.dist_eq, dist_eq_norm] using hK.dist_le_mul a b⟩

/-- If $h$ has Lipschitz constant $L$, then $h$ is Lipschitz with constant $L$ in the sense of
Mathlib's `LipschitzWith`. -/
theorem HasLipschitzConst.lipschitzWith {h : F → ℝ} {L : ℝ} (hL : HasLipschitzConst h L) :
    LipschitzWith ⟨L, hL.nonneg⟩ h :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [Real.dist_eq, dist_eq_norm]
    exact hL.abs_sub_le a b

/-- A function with a Lipschitz constant is continuous. -/
theorem HasLipschitzConst.continuous {h : F → ℝ} {L : ℝ} (hL : HasLipschitzConst h L) :
    Continuous h :=
  hL.lipschitzWith.continuous

variable {h h' : F → ℝ} {Lh : ℝ}

/-- $h$ is subadditive if and only if $h(a + b) \le h(a) + h(b)$ for all $a, b$. -/
theorem isSubadditive_iff : IsSubadditive h ↔ ∀ a b, h (a + b) ≤ h a + h b := Iff.rfl

/-- The sum of two subadditive functions is subadditive. -/
theorem IsSubadditive.add (hh : IsSubadditive h) (hh' : IsSubadditive h') :
    IsSubadditive (h + h') := fun a b => by
  simp only [Pi.add_apply]
  linarith [hh a b, hh' a b]

/-- The norm $a \mapsto \|a\|$ is subadditive. -/
theorem isSubadditive_norm : IsSubadditive (fun a : F => ‖a‖) := norm_add_le

/-- If $h$ is subadditive and odd, $h(-a) = -h(a)$ for all $a$, then $h$ is additive:
$h(a + b) = h(a) + h(b)$. -/
theorem IsSubadditive.map_add_of_odd (hh : IsSubadditive h) (hodd : ∀ a, h (-a) = -h a)
    (a b : F) : h (a + b) = h a + h b := by
  have := hh (a + b) (-b)
  rw [add_neg_cancel_right, hodd] at this
  linarith [hh a b]

/-- If $h$ is subadditive, then $h(a + b) - h(a) \le h(b)$ for all $a, b$. -/
theorem IsSubadditive.sub_le (hh : IsSubadditive h) (a b : F) : h (a + b) - h a ≤ h b := by
  linarith [hh a b]

/-- If $h(0) = 0$ and $h$ has Lipschitz constant $L_h$, then $|h(a)| \le L_h \|a\|$ for all $a$.
This is (14.1.4) of [cartis2022evaluation]. -/
theorem abs_le_of_lipschitz_of_map_zero (h0 : h 0 = 0)
    (hLip : HasLipschitzConst h Lh) (a : F) : |h a| ≤ Lh * ‖a‖ := by
  simpa [h0] using hLip.abs_sub_le a 0

/-- If $h$ is subadditive, $h(0) = 0$, and $h$ has Lipschitz constant $L_h$, then
$h(a + b) - h(a) \le h(b) \le L_h \|b\|$; the theorem states $h(a + b) - h(a) \le L_h \|b\|$. -/
theorem IsSubadditive.sub_le_mul_norm (hh : IsSubadditive h) (h0 : h 0 = 0)
    (hLip : HasLipschitzConst h Lh) (a b : F) : h (a + b) - h a ≤ Lh * ‖b‖ :=
  (hh.sub_le a b).trans ((le_abs_self _).trans (abs_le_of_lipschitz_of_map_zero h0 hLip b))

/-- The zero function is subadditive. -/
theorem isSubadditive_zero {G : Type*} [Add G] : IsSubadditive (0 : G → ℝ) := fun _ _ => by simp

/-- The zero function has Lipschitz constant $0$. -/
theorem hasLipschitzConst_zero : HasLipschitzConst (0 : F → ℝ) 0 :=
  ⟨le_rfl, fun _ _ => by simp⟩

end Subadditive

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### The composite decrement and measure -/

section Decrement

variable (Df : FormalMultilinearSeries ℝ E ℝ) (Dc : FormalMultilinearSeries ℝ E F) (h : F → ℝ)
  (j : ℕ)

/-- Let $D_f$ and $D_c$ be derivative data, that is, sequences of multilinear maps on $E$ with
values in $\mathbb{R}$ and in $F$, and let $h : F \to \mathbb{R}$. The **composite Taylor
decrement** of order $j$ along $d \in E$ is the decrease of the generalized Taylor model
$T_{w,j}(s) = T_{f,j}(s) + h(T_{c,j}(s))$ from $0$ to $d$:
$$\Delta T_{w,j}(d) = \bigl(T_{f,j}(0) + h(T_{c,j}(0))\bigr) - \bigl(T_{f,j}(d) +
  h(T_{c,j}(d))\bigr),$$
where $T_{f,j}(s) = \sum_{i=0}^{j} \frac{1}{i!} D_{f,i}[s]^i$ and $T_{c,j}(s) = \sum_{i=0}^{j}
\frac{1}{i!} D_{c,i}[s]^i$. This is the model (14.1.5) of [cartis2022evaluation] as it enters
the measure (14.1.6).

The function $h$ is kept exactly, so $T_{w,j}$ is not a Taylor polynomial of
$w = f + h \circ c$. The Taylor sums are `FormalMultilinearSeries.taylorSum` of `Df` and `Dc`. -/
noncomputable def compositeTaylorDecrement (d : E) : ℝ :=
  (Df.taylorSum j 0 + h (Dc.taylorSum j 0)) - (Df.taylorSum j d + h (Dc.taylorSum j d))

/-- The composite decrement is the Taylor decrement of $D_f$ plus the decrease of $h$: $\Delta
T_{w,j}(d) = \Delta T_{f,j}(d) + h(T_{c,j}(0)) - h(T_{c,j}(d))$. -/
theorem compositeTaylorDecrement_eq (d : E) :
    compositeTaylorDecrement Df Dc h j d =
      Df.taylorDecrement j d + (h (Dc.taylorSum j 0) - h (Dc.taylorSum j d)) := by
  rw [compositeTaylorDecrement, FormalMultilinearSeries.taylorDecrement]
  ring

/-- With $h = 0$, the composite decrement is the Taylor decrement $\Delta T_{f,j}$ of $D_f$. -/
@[simp]
theorem compositeTaylorDecrement_zero_fun :
    compositeTaylorDecrement Df Dc (0 : F → ℝ) j = Df.taylorDecrement j := by
  ext d
  simp [compositeTaylorDecrement_eq]

/-- The composite decrement vanishes at $d = 0$. -/
@[simp]
theorem compositeTaylorDecrement_zero_right : compositeTaylorDecrement Df Dc h j 0 = 0 :=
  sub_self _

/-- If $h$ is continuous, then $d \mapsto \Delta T_{w,j}(d)$ is continuous. -/
theorem continuous_compositeTaylorDecrement (hc : Continuous h) :
    Continuous (compositeTaylorDecrement Df Dc h j) :=
  continuous_const.sub ((Df.contDiff_taylorSum j (n := 0)).continuous.add
    (hc.comp (Dc.contDiff_taylorSum j (n := 0)).continuous))

/-- For derivative data $D_c$ with values in $F$ and every $d \in E$,
$$\|T_{c,j}(0) - T_{c,j}(d)\| \le \sum_{i=1}^{j} \|D_{c,i}\| \, \frac{\|d\|^i}{i!}.$$
-/
theorem norm_taylorSum_zero_sub_le (d : E) :
    ‖Dc.taylorSum j 0 - Dc.taylorSum j d‖ ≤ ∑ i ∈ Finset.Icc 1 j, ‖Dc i‖ * ‖d‖ ^ i / i ! := by
  rw [Dc.taylorSum_zero_right, Dc.taylorSum_eq_add, sub_add_cancel_left, norm_neg]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_eq_div]
  gcongr
  exact Dc.norm_apply_diagonal_le i d

variable {Df Dc h j} {Lh : ℝ}

/-- **Bound on the composite decrement.** If $h$ has Lipschitz constant $L_h$, then for every
$d \in E$
$$|\Delta T_{w,j}(d)| \le \sum_{i=1}^{j} \bigl(\|D_{f,i}\| + L_h \|D_{c,i}\|\bigr)
  \frac{\|d\|^i}{i!}.$$

The norms $\|D_{f,i}\|$ and $\|D_{c,i}\|$ are operator norms of multilinear maps. The bound
shows that the supremum in `Optimization.compositeTaylorMeasure` is finite. -/
theorem abs_compositeTaylorDecrement_le (hLip : HasLipschitzConst h Lh) (d : E) :
    |compositeTaylorDecrement Df Dc h j d| ≤
      ∑ i ∈ Finset.Icc 1 j, (‖Df i‖ + Lh * ‖Dc i‖) * ‖d‖ ^ i / i ! := by
  rw [compositeTaylorDecrement_eq]
  have h1 := Df.abs_taylorDecrement_le j d
  have h2 : |h (Dc.taylorSum j 0) - h (Dc.taylorSum j d)| ≤
      Lh * ∑ i ∈ Finset.Icc 1 j, ‖Dc i‖ * ‖d‖ ^ i / i ! :=
    (hLip.abs_sub_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_taylorSum_zero_sub_le Dc j d) hLip.nonneg)
  have he : ∑ i ∈ Finset.Icc 1 j, (‖Df i‖ + Lh * ‖Dc i‖) * ‖d‖ ^ i / i ! =
      ∑ i ∈ Finset.Icc 1 j, ‖Df i‖ * ‖d‖ ^ i / i ! +
        Lh * ∑ i ∈ Finset.Icc 1 j, ‖Dc i‖ * ‖d‖ ^ i / i ! := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- If $h$ has Lipschitz constant $L_h$, then for every $\delta \in \mathbb{R}$ and $S \subseteq E$
the values $\Delta T_{w,j}(d)$ for $\|d\| \le \delta$ and $d \in S$ are bounded above. -/
theorem bddAbove_compositeTaylorDecrement (hLip : HasLipschitzConst h Lh) (δ : ℝ) (S : Set E) :
    BddAbove (compositeTaylorDecrement Df Dc h j '' (closedBall 0 δ ∩ S)) := by
  refine ⟨∑ i ∈ Finset.Icc 1 j, (‖Df i‖ + Lh * ‖Dc i‖) * δ ^ i / i !,
    forall_mem_image.2 fun d hd => ?_⟩
  refine (le_abs_self _).trans ((abs_compositeTaylorDecrement_le hLip d).trans
    (sum_le_sum fun i _ => ?_))
  have := hLip.nonneg
  gcongr
  exact mem_closedBall_zero_iff.1 hd.1

end Decrement

section Measure

variable (Df : FormalMultilinearSeries ℝ E ℝ) (Dc : FormalMultilinearSeries ℝ E F) (h : F → ℝ)
  (j : ℕ) (δ : ℝ) (S : Set E)

/-- Let $D_f$, $D_c$ be derivative data, $h : F \to \mathbb{R}$, $\delta \in \mathbb{R}$ and
$S \subseteq E$ a set of feasible displacements. The **composite criticality measure** of order
$j$ is
$$\varphi^\delta_{w,j} = \sup \{\Delta T_{w,j}(d) \mid \|d\| \le \delta, \ d \in S\}.$$
For $D_f$ and $D_c$ the Taylor series of $f$ and $c$ at $x$ and $S = E$, this is the measure
$\varphi^\delta_{w,j}(x) = w(x) - \min_{\|d\| \le \delta} T_{w,j}(x, d)$ of (14.1.6) of
[cartis2022evaluation], with minimization variable $d$.

The supremum is `sSup` in `ℝ`; it is $0$ if the set of values is empty, and it is finite when
$h$ is Lipschitz (`Optimization.bddAbove_compositeTaylorDecrement`). The measure is
`Optimization.decrementMeasure` of `Optimization.compositeTaylorDecrement`. With
$S = \{d \mid x + d \in X\}$ it is the constrained measure of §14.2 of [cartis2022evaluation].
With the jets of the regularized model at a trial step $s$ it is the model measure
$\varphi^\delta_{\hat m,j}(s)$ of (14.1.14). -/
noncomputable def compositeTaylorMeasure : ℝ :=
  decrementMeasure (compositeTaylorDecrement Df Dc h j) δ S

/-- The composite measure is the supremum $\sup \Delta T_{w,j}(\bar B(0, \delta) \cap S)$. -/
theorem compositeTaylorMeasure_eq_sSup :
    compositeTaylorMeasure Df Dc h j δ S =
      sSup (compositeTaylorDecrement Df Dc h j '' (closedBall 0 δ ∩ S)) := rfl

/-- With $h = 0$, the composite measure is the Taylor measure `Optimization.taylorMeasure` of $D_f$.
-/
@[simp]
theorem compositeTaylorMeasure_zero_fun :
    compositeTaylorMeasure Df Dc (0 : F → ℝ) j δ S = taylorMeasure Df j δ S := by
  rw [compositeTaylorMeasure, compositeTaylorDecrement_zero_fun]
  rfl

variable {Df Dc h j δ S} {Lh : ℝ} {d : E}

/-- If $h$ has a Lipschitz constant, then $\Delta T_{w,j}(d) \le \varphi^\delta_{w,j}$ for every
$d \in S$ with $\|d\| \le \delta$. -/
theorem compositeTaylorDecrement_le_compositeTaylorMeasure (hLip : HasLipschitzConst h Lh)
    (hd : d ∈ closedBall 0 δ ∩ S) :
    compositeTaylorDecrement Df Dc h j d ≤ compositeTaylorMeasure Df Dc h j δ S :=
  le_decrementMeasure (bddAbove_compositeTaylorDecrement hLip δ S) hd

/-- If $h$ has a Lipschitz constant, $0 \in S$ and $\delta \ge 0$, then
$\varphi^\delta_{w,j} \ge 0$. -/
theorem compositeTaylorMeasure_nonneg (hLip : HasLipschitzConst h Lh)
    (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) : 0 ≤ compositeTaylorMeasure Df Dc h j δ S :=
  decrementMeasure_nonneg (bddAbove_compositeTaylorDecrement hLip δ S) h0 hδ
    (compositeTaylorDecrement_zero_right Df Dc h j)

/-- If $h$ has a Lipschitz constant, $0 \in S$ and $0 \le \delta \le \delta'$, then
$\varphi^\delta_{w,j} \le \varphi^{\delta'}_{w,j}$, with both measures over $S$. -/
theorem compositeTaylorMeasure_mono_radius {δ' : ℝ} (hLip : HasLipschitzConst h Lh)
    (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) (hδδ' : δ ≤ δ') :
    compositeTaylorMeasure Df Dc h j δ S ≤ compositeTaylorMeasure Df Dc h j δ' S :=
  decrementMeasure_mono_radius ⟨0, mem_closedBall_self hδ, h0⟩
    (bddAbove_compositeTaylorDecrement hLip δ' S) hδδ'

/-- If $h$ has a Lipschitz constant, $0 \in S$, $\delta \ge 0$ and $S \subseteq S'$, then the
measure over $S$ is at most the measure over $S'$. -/
theorem compositeTaylorMeasure_mono_set {S' : Set E} (hLip : HasLipschitzConst h Lh)
    (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) (hSS' : S ⊆ S') :
    compositeTaylorMeasure Df Dc h j δ S ≤ compositeTaylorMeasure Df Dc h j δ S' :=
  decrementMeasure_mono_set ⟨0, mem_closedBall_self hδ, h0⟩
    (bddAbove_compositeTaylorDecrement hLip δ S') hSS'

/-- Let $E$ be finite-dimensional, $h$ continuous, $S \subseteq E$ closed with $0 \in S$, and
$\delta \ge 0$. Then the composite measure is attained: there is $d \in S$ with
$\|d\| \le \delta$ and
$$\Delta T_{w,j}(d) = \varphi^\delta_{w,j}.$$

Such a $d$ is an optimality displacement. The proof uses that $\Delta T_{w,j}$ is continuous and
that $\bar B(0, \delta) \cap S$ is compact and nonempty. -/
theorem exists_compositeTaylorMeasure_eq [FiniteDimensional ℝ E] (hc : Continuous h)
    (hS : IsClosed S) (h0 : (0 : E) ∈ S) (hδ : 0 ≤ δ) :
    ∃ d ∈ closedBall 0 δ ∩ S,
      compositeTaylorDecrement Df Dc h j d = compositeTaylorMeasure Df Dc h j δ S :=
  exists_decrementMeasure_eq hS h0 hδ
    (continuous_compositeTaylorDecrement Df Dc h j hc).continuousOn

end Measure

/-! ### Approximate minimizers -/

section Approx

variable {Df : FormalMultilinearSeries ℝ E ℝ} {Dc : FormalMultilinearSeries ℝ E F} {h : F → ℝ}
  {S : Set E} {q : ℕ} {ε δ : ℕ → ℝ}

/-- Let $D_f$, $D_c$ be derivative data, $h : F \to \mathbb{R}$, $S \subseteq E$ a set of feasible
displacements, $q \in \mathbb{N}$, and $(\varepsilon_j)$, $(\delta_j)$ real sequences. The data
are **$(\varepsilon, \delta)$-approximately $q$-th order optimal** for the composite function if
$$\varphi^{\delta_j}_{w,j} \le \varepsilon_j \frac{\delta_j^j}{j!} \qquad \text{for } 1 \le j
  \le q.$$
When $D_f$ is `ftaylorSeries ℝ f x` and $D_c$ is `ftaylorSeries ℝ c x`, this is the condition
(14.1.9) of [cartis2022evaluation] at $x$. -/
def IsEpsDeltaApproxComposite (Df : FormalMultilinearSeries ℝ E ℝ)
    (Dc : FormalMultilinearSeries ℝ E F) (h : F → ℝ) (S : Set E) (q : ℕ) (ε δ : ℕ → ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 q, compositeTaylorMeasure Df Dc h j (δ j) S ≤ ε j * δ j ^ j / j !

/-- The condition `Optimization.IsEpsDeltaApproxComposite` holds if and only if
$\varphi^{\delta_j}_{w,j} \le \varepsilon_j \delta_j^j / j!$ for $1 \le j \le q$. -/
theorem isEpsDeltaApproxComposite_iff :
    IsEpsDeltaApproxComposite Df Dc h S q ε δ ↔
      ∀ j ∈ Finset.Icc 1 q, compositeTaylorMeasure Df Dc h j (δ j) S ≤ ε j * δ j ^ j / j ! :=
  Iff.rfl

/-- With $h = 0$, composite approximate optimality is the smooth condition
`Optimization.IsEpsDeltaApprox` of (12.1.25) of [cartis2022evaluation]. -/
theorem isEpsDeltaApproxComposite_zero_fun_iff :
    IsEpsDeltaApproxComposite Df Dc (0 : F → ℝ) S q ε δ ↔ IsEpsDeltaApprox Df S q ε δ := by
  simp only [IsEpsDeltaApproxComposite, compositeTaylorMeasure_zero_fun, IsEpsDeltaApprox]

/-- Let $\varsigma > 0$, and for each $1 \le j \le q$ let $d_j$ be an approximate optimality
displacement of $\Delta T_{w,j}$: $d_j \in S$, $\|d_j\| \le \delta_j$ and $\varsigma
\varphi^{\delta_j}_{w,j} \le \Delta T_{w,j}(d_j)$. If the test $\Delta T_{w,j}(d_j) \le
\varsigma \varepsilon_j \delta_j^j / j!$ passes for $1 \le j \le q$, then the condition (14.1.9)
holds. This is the certification by the Step-1 test (14.1.10) of [cartis2022evaluation]. -/
theorem MeasureTestPasses.isEpsDeltaApproxComposite {ς : ℝ} {d : ℕ → E} (hς : 0 < ς)
    (hd : ∀ j ∈ Finset.Icc 1 q,
      IsApproxMeasureStep (compositeTaylorDecrement Df Dc h j) (δ j) S ς (d j))
    (htest : MeasureTestPasses (fun j => compositeTaylorDecrement Df Dc h j) q ς ε δ d) :
    IsEpsDeltaApproxComposite Df Dc h S q ε δ :=
  isEpsDeltaApprox_of_measureTestPasses (Δ := fun j => compositeTaylorDecrement Df Dc h j) hς hd
    htest

end Approx

/-! ### First-order necessity (Lemma 14.1.1) -/

section Necessity

/-- For $g : E \to G$, the first-order Taylor polynomial along a ray is $T_{g,1}(x, \alpha s) =
g(x) + \alpha \nabla g(x)[s]$. -/
private theorem taylorSum_one_ftaylorSeries_smul {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (g : E → G) (x s : E) (α : ℝ) :
    (ftaylorSeries ℝ g x).taylorSum 1 (α • s) = g x + α • fderiv ℝ g x s := by
  rw [FormalMultilinearSeries.taylorSum_eq_add, Finset.Icc_self, sum_singleton]
  simp only [ftaylorSeries, iteratedFDeriv_zero_apply, Nat.factorial_one, Nat.cast_one,
    inv_one, one_smul]
  rw [show (fun _ : Fin 1 => α • s) = fun i : Fin 1 => (fun _ => α) i • (fun _ => s) i from rfl,
    ContinuousMultilinearMap.map_smul_univ, iteratedFDeriv_one_apply]
  simp

private theorem taylorSum_ftaylorSeries_zero {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (g : E → G) (x : E) (p : ℕ) :
    (ftaylorSeries ℝ g x).taylorSum p 0 = g x :=
  taylorPolynomial_zero_right g p x

/-- For the jets of $f$ and $c$ at $x$, the first-order composite decrement along a ray is $\Delta
T_{w,1}(x, \alpha s) = w(x) - \bigl(f(x) + \alpha \nabla f(x)[s] + h(c(x) + \alpha \nabla
c(x)[s])\bigr)$. -/
private theorem compositeTaylorDecrement_one_smul (f : E → ℝ) (c : E → F) (h : F → ℝ) (x s : E)
    (α : ℝ) :
    compositeTaylorDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h 1 (α • s) =
      (f x + h (c x)) - (f x + α * fderiv ℝ f x s + h (c x + α • fderiv ℝ c x s)) := by
  rw [compositeTaylorDecrement, taylorSum_one_ftaylorSeries_smul f,
    taylorSum_one_ftaylorSeries_smul c, taylorSum_ftaylorSeries_zero f,
    taylorSum_ftaylorSeries_zero c, smul_eq_mul]

/-- **First-order necessary condition for composite problems.** Let $X \subseteq E$ be convex and
$x \in X$. Let $f : E \to \mathbb{R}$ and $c : E \to F$ be differentiable at $x$, and let
$h : F \to \mathbb{R}$ be convex with a Lipschitz constant. If $x$ is a local minimizer of
$w = f + h \circ c$ on $X$, then for every $s$ with $x + s \in X$
$$\Delta T_{w,1}(x, s) \le 0,$$
so $0$ is a global minimizer of $T_{w,1}(x, \cdot)$ over $X - x$. This generalizes Lemma 14.1.1
of [cartis2022evaluation].

The decrement is `Optimization.compositeTaylorDecrement` of `ftaylorSeries ℝ f x` and
`ftaylorSeries ℝ c x`. Local minimality, Lipschitz continuity of $h$, and no subadditivity are
enough. -/
theorem compositeTaylorDecrement_one_nonpos_of_isLocalMinOn {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {Lh : ℝ} {X : Set E} {x : E} (hX : Convex ℝ X) (hx : x ∈ X) (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (hconv : ConvexOn ℝ univ h)
    (hLip : HasLipschitzConst h Lh)
    (hmin : IsLocalMinOn (fun z => f z + h (c z)) X x) {s : E} (hs : x + s ∈ X) :
    compositeTaylorDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h 1 s ≤ 0 := by
  set Δ := compositeTaylorDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h 1 s with hΔ
  by_contra hpos
  push Not at hpos
  set a := fderiv ℝ f x s
  set b := fderiv ℝ c x s
  -- the decrement along `α s` is at least `α Δ` (convexity of the model in `α`)
  have hlin : ∀ α ∈ Icc (0 : ℝ) 1,
      α * Δ ≤ (f x + h (c x)) - (f x + α * a + h (c x + α • b)) := by
    intro α hα
    have hΔ1 := compositeTaylorDecrement_one_smul f c h x s 1
    rw [one_smul, one_smul, one_mul] at hΔ1
    have hcv := hconv.2 (mem_univ (c x)) (mem_univ (c x + b)) (sub_nonneg.2 hα.2) hα.1
      (by ring)
    rw [smul_eq_mul, smul_eq_mul, smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul]
      at hcv
    rw [hΔ, hΔ1]
    nlinarith
  -- first-order expansions of `f` and `c` along the ray
  have hline : HasDerivAt (fun α : ℝ => x + α • s) s 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add x
  have hx0 : x + (0 : ℝ) • s = x := by simp
  have hfo := hasDerivAt_iff_isLittleO.1
    (HasFDerivAt.comp_hasDerivAt (0 : ℝ) (hx0 ▸ hf.hasFDerivAt) hline)
  have hco := hasDerivAt_iff_isLittleO.1
    (HasFDerivAt.comp_hasDerivAt (0 : ℝ) (hx0 ▸ hc.hasFDerivAt) hline)
  set ε := Δ / (2 * (1 + |Lh|))
  have hε : 0 < ε := by positivity
  have hf' := (hfo.def hε).filter_mono (nhdsWithin_le_nhds (s := Ioi 0))
  have hc' := (hco.def hε).filter_mono (nhdsWithin_le_nhds (s := Ioi 0))
  -- local minimality along the ray
  have hray : Tendsto (fun α : ℝ => x + α • s) (𝓝[Ioo 0 1] 0) (𝓝[X] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun α hα => ?_⟩
    · have := (hline.continuousAt.tendsto).mono_left (nhdsWithin_le_nhds (s := Ioo 0 1))
      simpa using this
    · have := hX.add_smul_mem hx hs ⟨hα.1.le, hα.2.le⟩
      simpa using this
  have hmin' := hray.eventually hmin
  have hIoo : 𝓝[Ioo (0 : ℝ) 1] 0 = 𝓝[>] 0 := nhdsWithin_Ioo_eq_nhdsGT one_pos
  rw [hIoo] at hmin'
  have hpos' : ∀ᶠ α in 𝓝[>] (0 : ℝ), α ∈ Ioo (0 : ℝ) 1 := by
    rw [← hIoo]; exact self_mem_nhdsWithin
  obtain ⟨α, ⟨hα0, hα1⟩, hm, hfα, hcα⟩ := (hpos'.and (hmin'.and (hf'.and hc'))).exists
  simp only [Function.comp_apply, zero_smul, add_zero, sub_zero, smul_eq_mul, Real.norm_eq_abs,
    abs_of_pos hα0] at hm hfα hcα
  have hl := hlin α ⟨hα0.le, hα1.le⟩
  -- `w(x + α s) ≤ T_{w,1}(x, α s) + ε α (1 + |Lh|)`
  have hhα : h (c (x + α • s)) - h (c x + α • b) ≤ |Lh| * (ε * α) := by
    have := hLip.abs_sub_le (c (x + α • s)) (c x + α • b)
    have hcα' : ‖c (x + α • s) - (c x + α • b)‖ ≤ ε * α := by
      rw [← sub_sub]; exact hcα
    calc h (c (x + α • s)) - h (c x + α • b) ≤ Lh * ‖c (x + α • s) - (c x + α • b)‖ :=
          (le_abs_self _).trans this
      _ ≤ |Lh| * ‖c (x + α • s) - (c x + α • b)‖ := by gcongr; exact le_abs_self _
      _ ≤ |Lh| * (ε * α) := by gcongr
  have hfα' : f (x + α • s) - f x - α * a ≤ ε * α := (le_abs_self _).trans hfα
  have hεΔ : ε * (1 + |Lh|) = Δ / 2 := by
    simp only [ε]; field_simp
  nlinarith [abs_nonneg Lh]

/-- Let $X \subseteq E$ be convex, $x \in X$, let $f$ and $c$ be differentiable at $x$, and let $h$
be convex with a Lipschitz constant. If $x$ is a local minimizer of $f + h \circ c$ on $X$, then
for every $\delta \ge 0$ the first-order composite measure $\varphi^\delta_{w,1}(x)$ over the
feasible displacements $\{d \mid x + d \in X\}$ is $0$. This is a consequence of Lemma 14.1.1 of
[cartis2022evaluation]. -/
theorem compositeTaylorMeasure_one_eq_zero_of_isLocalMinOn {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {Lh : ℝ} {X : Set E} {x : E} (hX : Convex ℝ X) (hx : x ∈ X) (hf : DifferentiableAt ℝ f x)
    (hc : DifferentiableAt ℝ c x) (hconv : ConvexOn ℝ univ h)
    (hLip : HasLipschitzConst h Lh)
    (hmin : IsLocalMinOn (fun z => f z + h (c z)) X x) {δ : ℝ} (hδ : 0 ≤ δ) :
    compositeTaylorMeasure (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h 1 δ
      {d | x + d ∈ X} = 0 := by
  have h0 : (0 : E) ∈ closedBall 0 δ ∩ {d | x + d ∈ X} :=
    ⟨mem_closedBall_self hδ, by simpa using hx⟩
  have hle : ∀ d ∈ closedBall 0 δ ∩ {d | x + d ∈ X},
      compositeTaylorDecrement (ftaylorSeries ℝ f x) (ftaylorSeries ℝ c x) h 1 d ≤ 0 :=
    fun d hd => compositeTaylorDecrement_one_nonpos_of_isLocalMinOn hX hx hf hc hconv hLip hmin hd.2
  refine le_antisymm (decrementMeasure_le ⟨0, h0⟩ hle) ?_
  have := le_decrementMeasure ⟨0, forall_mem_image.2 hle⟩ h0
  rwa [compositeTaylorDecrement_zero_right] at this

end Necessity

/-! ### Value remainder -/

/-- **Remainder of the composite model, anchored form.** Let $C \subseteq E$ be convex, and let
$f : E \to \mathbb{R}$ and $c : E \to F$ be $p$ times continuously differentiable at every point
of $C$. Suppose that $\nabla^p f$ and $\nabla^p c$ are Lipschitz with anchor $x$: $\|\nabla^p
f(y) - \nabla^p f(x)\| \le L_f \|y - x\|$ and $\|\nabla^p c(y) - \nabla^p c(x)\| \le L_c \|y -
x\|$ for $y \in C$. Let $h$ have Lipschitz constant $L_h$. Then for $x, x + s \in C$
$$\bigl|f(x + s) + h(c(x + s)) - \bigl(T_{f,p}(x, s) + h(T_{c,p}(x, s))\bigr)\bigr| \le
  \frac{L_f + L_h L_c}{(p + 1)!} \|s\|^{p+1}.$$

This is the form of `Optimization.abs_sub_compositeTaylor_le_of_lipschitz` that the proof of
Lemma 14.1.6 of [cartis2022evaluation] needs. $T_{f,p}(x, \cdot)$ is `taylorPolynomial f p x`,
and $T_{c,p}(x, \cdot)$ is the Taylor sum of `ftaylorSeries ℝ c x`. -/
theorem abs_sub_compositeTaylor_le_of_lipschitzAnchored {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {p : ℕ} {Lf Lc Lh : ℝ} {C : Set E} {x s : E} (hC : Convex ℝ C)
    (hf : ∀ y ∈ C, ContDiffAt ℝ p f y) (hc : ∀ y ∈ C, ContDiffAt ℝ p c y)
    (hLf : ∀ y ∈ C, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f x‖ ≤ Lf * ‖y - x‖)
    (hLc : ∀ y ∈ C, ‖iteratedFDeriv ℝ p c y - iteratedFDeriv ℝ p c x‖ ≤ Lc * ‖y - x‖)
    (hLip : HasLipschitzConst h Lh) (hx : x ∈ C) (hxs : x + s ∈ C) :
    |(f (x + s) + h (c (x + s))) -
        (taylorPolynomial f p x s + h ((ftaylorSeries ℝ c x).taylorSum p s))| ≤
      (Lf + Lh * Lc) / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by
  have h1 := norm_sub_taylorPolynomial_le_of_lipschitzAnchored hC hf hLf hx hxs
  have h2 := norm_sub_taylorPolynomial_le_of_lipschitzAnchored hC hc hLc hx hxs
  have h3 : |h (c (x + s)) - h ((ftaylorSeries ℝ c x).taylorSum p s)| ≤
      Lh * (Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)) :=
    (hLip.abs_sub_le _ _).trans (mul_le_mul_of_nonneg_left h2 hLip.nonneg)
  calc _ = |(f (x + s) - taylorPolynomial f p x s) +
        (h (c (x + s)) - h ((ftaylorSeries ℝ c x).taylorSum p s))| := by ring_nf
    _ ≤ |f (x + s) - taylorPolynomial f p x s| +
        |h (c (x + s)) - h ((ftaylorSeries ℝ c x).taylorSum p s)| := abs_add_le _ _
    _ ≤ Lf / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) + Lh * (Lc / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1)) :=
        add_le_add h1 h3
    _ = (Lf + Lh * Lc) / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by ring

/-- **Remainder of the composite model.** Let $C \subseteq E$ be convex, let $f : E \to \mathbb{R}$
and $c : E \to F$ be $p$ times continuously differentiable at every point of $C$, with
$\nabla^p f$ Lipschitz with constant $L_f$ and $\nabla^p c$ Lipschitz with constant $L_c$ on
$C$, and let $h$ have Lipschitz constant $L_h$. Then for $x, x + s \in C$
$$\bigl|w(x + s) - T_{w,p}(x, s)\bigr| \le \frac{L_f + L_h L_c}{(p + 1)!} \|s\|^{p+1},$$
where $w = f + h \circ c$ and $T_{w,p}(x, s) = T_{f,p}(x, s) + h(T_{c,p}(x, s))$. This is the
estimate in the proof of Lemma 14.1.6 of [cartis2022evaluation], with
$L_{w,p} = L_{f,p} + L_{h,0} L_{c,p}$ as in (14.1.27).

The operator norm is used for $\nabla^p c$. Componentwise constants for
$c : \mathbb{R}^n \to \mathbb{R}^m$ give a factor $\sqrt{m}$; see
`ContinuousMultilinearMap.norm_le_sqrt_card_mul_of_euclidean`. -/
theorem abs_sub_compositeTaylor_le_of_lipschitz {f : E → ℝ} {c : E → F} {h : F → ℝ} {p : ℕ}
    {Lf Lc Lh : ℝ} {C : Set E} {x s : E} (hC : Convex ℝ C) (hf : ∀ y ∈ C, ContDiffAt ℝ p f y)
    (hc : ∀ y ∈ C, ContDiffAt ℝ p c y) (hLf : IteratedFDerivLipschitzOn f p Lf C)
    (hLc : IteratedFDerivLipschitzOn c p Lc C) (hLip : HasLipschitzConst h Lh)
    (hx : x ∈ C) (hxs : x + s ∈ C) :
    |(f (x + s) + h (c (x + s))) -
        (taylorPolynomial f p x s + h ((ftaylorSeries ℝ c x).taylorSum p s))| ≤
      (Lf + Lh * Lc) / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) :=
  abs_sub_compositeTaylor_le_of_lipschitzAnchored hC hf hc
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hLf y hy x hx)
    (fun y hy => iteratedFDerivLipschitzOn_iff.1 hLc y hy x hx) hLip hx hxs

end Optimization
