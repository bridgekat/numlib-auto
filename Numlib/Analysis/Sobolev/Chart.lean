/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the boundary-regularity section of
`Numlib/Analysis/Sobolev/Domain.lean`; the partition of unity of Lemma 9.3 belongs beside
`Mathlib.Geometry.Manifold.PartitionOfUnity`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Numlib.Analysis.Sobolev.Domain

/-!
# Open sets of class $C^n$ by local charts

Write $N = d + 1$ and $x = (x', x_N)$ for a point of $\mathbb{R}^N$, with $x' \in \mathbb{R}^d$. Let
$Q = \{x : \|x'\| < 1, |x_N| < 1\}$ be the unit cylinder, $Q_+ = Q \cap \{x_N > 0\}$ its upper half
and $Q_0 = Q \cap \{x_N = 0\}$ its equator. Following §9.2 of [brezis2011functional], an open set
$\Omega \subseteq \mathbb{R}^N$ is of class $C^n$ if every boundary point has an open neighbourhood
$U$ and a bijection $H : Q \to U$ with $H \in C^n(\overline{Q})$, $H^{-1} \in C^n(\overline{U})$,
$H(Q_+) = U \cap \Omega$ and $H(Q_0) = U \cap \partial\Omega$. This module defines these charts
(`ContDiffChart`) and the open sets of class $C^n$ by charts (`IsContDiffChartDomain`), for the same
regularity index $n$ as the graph definition `IsContDiffDomain` of `Numlib.Analysis.Sobolev.Domain`,
and it shows that the graph definition implies the chart definition.

The module contains no Sobolev space. It also contains geometric facts that the Sobolev modules
need: the half space $\mathbb{R}^N_+$; the splitting $\mathbb{R}^{d+1} \cong \mathbb{R} \times
\mathbb{R}^d$ of Lebesgue measure along the last coordinate, which is the Fubini step of every
argument that integrates in $x_N$ first; the finite atlas of a bounded boundary; the partition of
unity of Lemma 9.3 of [brezis2011functional]; and the hypotheses `IsDiffeoOnWithBoundedJacobian` of
Proposition 9.6 there, with its footnote 6 (a $C^1$ diffeomorphism between open sets with bounded
Jacobians on both sides), which a chart restricted to $Q_+$ satisfies.

## Main definitions

* `EuclideanSpace.upperHalfSpace`: the half space $\{x_N > 0\}$ of $\mathbb{R}^{d+1}$.
* `unitChartCube`, `unitChartCubePos`, `unitChartCubeZero`: the cylinder $Q$ and its parts $Q_+$ and
  $Q_0$.
* `EuclideanSpace.lastInitEquiv`: the measurable equivalence $x \mapsto (x_N, x')$ of
  $\mathbb{R}^{d+1}$ with $\mathbb{R} \times \mathbb{R}^d$.
* `ContDiffChart`: a local chart of class $C^n$ of $\Omega$ at a boundary point.
* `IsContDiffChartDomain`: the open sets of class $C^n$ by charts.
* `IsDiffeoOnWithBoundedJacobian`: a $C^1$ diffeomorphism between open sets with bounded Jacobians.

## Main results

* `EuclideanSpace.measurePreserving_lastInit`: the map $x \mapsto (x_N, x')$ carries Lebesgue
  measure to the product of Lebesgue measures.
* `IsContDiffDomain.isContDiffChartDomain`: an open set whose boundary is locally the graph of a
  $C^n$ function is of class $C^n$ by charts.
* `IsContDiffChartDomain.exists_finite_atlas`: a bounded boundary is covered by finitely many
  charts.
* `IsCompact.exists_contDiff_partitionOfUnity`: Lemma 9.3 of [brezis2011functional], a smooth
  partition of unity $\theta_0 + \sum_i \theta_i = 1$ subordinate to a finite open cover of a
  compact set, with $\theta_0$ zero near the set and each $\theta_i$ compactly supported.
* `ContDiffOn.exists_norm_fderiv_le_of_isCompact`: a $C^1$ function on a compact set has a bounded
  derivative on the interior of the set.
* `ContDiffChart.isDiffeoOnWithBoundedJacobian_pos`: a chart restricted to $Q_+$ is a $C^1$
  diffeomorphism onto $U \cap \Omega$ with bounded Jacobians.

## Implementation notes

* Two definitions of a $C^n$ domain are in this library. The definition `IsContDiffDomain` of
  [han2009theoretical] uses local graphs after a rigid motion of the coordinates. The definition
  `IsContDiffChartDomain` of [brezis2011functional] uses charts. The two are equivalent, but only
  the direction from graphs to charts is elementary: the chart is $H(y', y_N) = T^{-1}(x_0' +
  \varepsilon y', g(x_0' + \varepsilon y') + \varepsilon y_N)$. The converse needs the implicit
  function theorem; nothing uses it, and it is not proved. The extension theorem of §9.2 of
  [brezis2011functional] is proved under the chart hypothesis, because its proof uses charts
  (transfer to $Q_+$ by $H$, reflection, transfer back). Results with a graph hypothesis reach it
  through `IsContDiffDomain.isContDiffChartDomain`.
* `ContDiffChart` is a structure, not Mathlib's `OpenPartialHomeomorph`, because the source of a
  chart is fixed to be $Q$ and the regularity is required on the closures $\overline{Q}$ and
  $\overline{U}$. `OpenPartialHomeomorph` carries neither.
* The condition $H^{-1} \in C^n(\overline{U})$ is `ContDiffOn ℝ n c.invFun (closure c.U)` in the
  sense of Mathlib. The set `closure U` need not be uniquely differentiable at its boundary. So the
  bound on the derivative of $H^{-1}$ on $U$ comes from a covering argument
  (`ContDiffOn.exists_norm_fderiv_le_of_isCompact`), not from the continuity of `fderivWithin` on
  the closure.
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped ContDiff ENNReal InnerProductSpace Manifold Topology

noncomputable section

variable {d : ℕ}

/-! ### The half space, and the first coordinates as a linear map -/

namespace EuclideanSpace

/-- **The upper half space** $\mathbb{R}^N_+ = \{x = (x', x_N) : x_N > 0\}$ of §9.2 of
[brezis2011functional], Notation, for $N = d + 1$.

The last coordinate is the one over which the boundary is a graph in `IsBoundaryGraphAt`, and
`isBoundaryOfClass_upperHalfSpace` uses the same set. -/
def upperHalfSpace (d : ℕ) : Set (EuclideanSpace ℝ (Fin (d + 1))) := {x | 0 < x (Fin.last d)}

/-- A point $x$ lies in $\mathbb{R}^N_+$ if and only if $x_N > 0$. -/
theorem mem_upperHalfSpace {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ upperHalfSpace d ↔ 0 < x (Fin.last d) :=
  Iff.rfl

/-- The half space $\mathbb{R}^N_+$ is open. -/
theorem isOpen_upperHalfSpace : IsOpen (upperHalfSpace d) :=
  isOpen_lt continuous_const (by fun_prop)

/-- The half space $\mathbb{R}^N_+$ as an element of `TopologicalSpace.Opens`, the form in which
Sobolev spaces on it are stated. -/
def upperHalfSpaceOpens (d : ℕ) : Opens (EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨upperHalfSpace d, isOpen_upperHalfSpace⟩

/-- The underlying set of `EuclideanSpace.upperHalfSpaceOpens d` is
`EuclideanSpace.upperHalfSpace d`. -/
@[simp]
theorem coe_upperHalfSpaceOpens : (upperHalfSpaceOpens d : Set _) = upperHalfSpace d := rfl

/-- The map $x \mapsto x'$ from $\mathbb{R}^{d+1}$ to its first $d$ coordinates
(`EuclideanSpace.init`), as a continuous linear map. -/
def initL : EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearMap.toContinuousLinearMap
    { toFun := init
      map_add' := fun x y ↦ by ext i; simp
      map_smul' := fun c x ↦ by ext i; simp }

/-- The map `EuclideanSpace.initL` sends $x$ to $x'$. -/
@[simp]
theorem initL_apply (x : EuclideanSpace ℝ (Fin (d + 1))) : initL x = init x := rfl

/-- The map $x \mapsto x'$ from $\mathbb{R}^{d+1}$ to $\mathbb{R}^d$ is continuous. -/
theorem continuous_init : Continuous (init : EuclideanSpace ℝ (Fin (d + 1)) → _) :=
  (initL (d := d)).continuous

/-- The map $x \mapsto x'$ from $\mathbb{R}^{d+1}$ to $\mathbb{R}^d$ is of class $C^n$ for every
$n$. -/
theorem contDiff_init {n : WithTop ℕ∞} :
    ContDiff ℝ n (init : EuclideanSpace ℝ (Fin (d + 1)) → _) :=
  (initL (d := d)).contDiff

/-- The first coordinates of a sum: $(x + y)' = x' + y'$. -/
@[simp]
theorem init_add (x y : EuclideanSpace ℝ (Fin (d + 1))) : init (x + y) = init x + init y :=
  map_add initL x y

/-- The first coordinates of a difference: $(x - y)' = x' - y'$. -/
@[simp]
theorem init_sub (x y : EuclideanSpace ℝ (Fin (d + 1))) : init (x - y) = init x - init y :=
  map_sub initL x y

/-- The first coordinates of a scalar multiple: $(cx)' = c x'$. -/
@[simp]
theorem init_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) : init (c • x) = c • init x :=
  map_smul initL c x

/-- The first coordinates of $0$ are $0$. -/
@[simp]
theorem init_zero : init (0 : EuclideanSpace ℝ (Fin (d + 1))) = 0 := map_zero initL

/-- The first coordinates of $a e_N$ vanish, where $e_N$ is the last standard basis vector of
$\mathbb{R}^{d+1}$. -/
@[simp]
theorem init_single_last (a : ℝ) : init (single (Fin.last d) a) = 0 := by
  ext i
  simp [Fin.castSucc_ne_last]

/-- The norm splits along the last coordinate: $\|x\|^2 = \|x'\|^2 + x_N^2$ for
$x \in \mathbb{R}^{d+1}$. -/
theorem norm_sq_eq_init_add_last (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ‖x‖ ^ 2 = ‖init x‖ ^ 2 + x (Fin.last d) ^ 2 := by
  rw [real_norm_sq_eq, real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp

/-- For $x \in \mathbb{R}^{d+1}$, $\|x'\| \le \|x\|$. -/
theorem norm_init_le (x : EuclideanSpace ℝ (Fin (d + 1))) : ‖init x‖ ≤ ‖x‖ :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by nlinarith [norm_sq_eq_init_add_last x, sq_nonneg (x (Fin.last d))])

/-- For $x \in \mathbb{R}^{d+1}$, $|x_N| \le \|x\|$. -/
theorem abs_apply_last_le (x : EuclideanSpace ℝ (Fin (d + 1))) : |x (Fin.last d)| ≤ ‖x‖ :=
  (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by nlinarith [norm_sq_eq_init_add_last x, sq_nonneg ‖init x‖, sq_abs (x (Fin.last d))])

end EuclideanSpace

/-! ### The unit cylinder $Q$ and its parts $Q_+$ and $Q_0$ -/

open EuclideanSpace in
/-- **The unit cylinder** $Q = \{x = (x', x_N) : \|x'\| < 1, |x_N| < 1\}$ of §9.2 of
[brezis2011functional], Notation. It is the domain of every local chart.

The source calls $Q$ a cube. With the Euclidean norm of $x'$ it is a cylinder. -/
def unitChartCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {x | ‖init x‖ < 1 ∧ |x (Fin.last d)| < 1}

/-- **The upper half cylinder** $Q_+ = Q \cap \mathbb{R}^N_+ = \{x \in Q : x_N > 0\}$ of §9.2 of
[brezis2011functional], Notation. -/
def unitChartCubePos (d : ℕ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {x ∈ unitChartCube d | 0 < x (Fin.last d)}

/-- **The equator** $Q_0 = \{x \in Q : x_N = 0\} = \{(x', 0) : \|x'\| < 1\}$ of the cylinder, §9.2
of [brezis2011functional], Notation. It is the part of $Q$ that a chart maps onto the boundary. -/
def unitChartCubeZero (d : ℕ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  {x ∈ unitChartCube d | x (Fin.last d) = 0}

open EuclideanSpace

/-- A point $x$ lies in $Q$ if and only if $\|x'\| < 1$ and $|x_N| < 1$. -/
theorem mem_unitChartCube {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ unitChartCube d ↔ ‖init x‖ < 1 ∧ |x (Fin.last d)| < 1 :=
  Iff.rfl

/-- A point $x$ lies in $Q_+$ if and only if $x \in Q$ and $x_N > 0$. -/
theorem mem_unitChartCubePos {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ unitChartCubePos d ↔ x ∈ unitChartCube d ∧ 0 < x (Fin.last d) :=
  Iff.rfl

/-- A point $x$ lies in $Q_0$ if and only if $x \in Q$ and $x_N = 0$. -/
theorem mem_unitChartCubeZero {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ unitChartCubeZero d ↔ x ∈ unitChartCube d ∧ x (Fin.last d) = 0 :=
  Iff.rfl

/-- The upper half cylinder is contained in the cylinder: $Q_+ \subseteq Q$. -/
theorem unitChartCubePos_subset : unitChartCubePos d ⊆ unitChartCube d := fun _ hx ↦ hx.1

/-- The equator is contained in the cylinder: $Q_0 \subseteq Q$. -/
theorem unitChartCubeZero_subset : unitChartCubeZero d ⊆ unitChartCube d := fun _ hx ↦ hx.1

/-- $Q_+ = Q \cap \mathbb{R}^N_+$, as the source writes it. -/
theorem unitChartCubePos_eq_inter :
    unitChartCubePos d = unitChartCube d ∩ upperHalfSpace d :=
  rfl

/-- The origin lies in $Q$. -/
theorem zero_mem_unitChartCube : (0 : EuclideanSpace ℝ (Fin (d + 1))) ∈ unitChartCube d := by
  simp [mem_unitChartCube]

/-- The origin lies in $Q_0$. -/
theorem zero_mem_unitChartCubeZero :
    (0 : EuclideanSpace ℝ (Fin (d + 1))) ∈ unitChartCubeZero d :=
  ⟨zero_mem_unitChartCube, by simp⟩

/-- The map $x \mapsto x_N$ on $\mathbb{R}^{d+1}$ is continuous. -/
theorem continuous_apply_last :
    Continuous fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦ x (Fin.last d) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last d)).continuous

/-- The map $x \mapsto |x_N|$ on $\mathbb{R}^{d+1}$ is continuous. -/
theorem continuous_abs_apply_last :
    Continuous fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦ |x (Fin.last d)| :=
  continuous_apply_last.abs

/-- The cylinder $Q$ is open. -/
theorem isOpen_unitChartCube : IsOpen (unitChartCube d) :=
  (isOpen_lt continuous_init.norm continuous_const).inter
    (isOpen_lt continuous_abs_apply_last continuous_const)

/-- The upper half cylinder $Q_+$ is open. -/
theorem isOpen_unitChartCubePos : IsOpen (unitChartCubePos d) :=
  isOpen_unitChartCube.inter isOpen_upperHalfSpace

/-- The cylinder $Q$ lies in the open ball of radius $2$ about the origin. -/
theorem unitChartCube_subset_ball : unitChartCube d ⊆ Metric.ball 0 2 := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  have h := norm_sq_eq_init_add_last x
  have h1 : ‖init x‖ ^ 2 < 1 := by nlinarith [hx.1, norm_nonneg (init x)]
  have h2 : x (Fin.last d) ^ 2 < 1 := by
    nlinarith [hx.2, abs_nonneg (x (Fin.last d)), sq_abs (x (Fin.last d))]
  nlinarith [norm_nonneg x]

/-- The cylinder $Q$ is bounded. -/
theorem isBounded_unitChartCube : Bornology.IsBounded (unitChartCube d) :=
  Metric.isBounded_ball.subset unitChartCube_subset_ball

/-- The closure of the cylinder is the closed cylinder: $\overline{Q} = \{x : \|x'\| \le 1, |x_N|
\le 1\}$. -/
theorem closure_unitChartCube :
    closure (unitChartCube d) = {x | ‖init x‖ ≤ 1 ∧ |x (Fin.last d)| ≤ 1} := by
  apply Subset.antisymm
  · refine closure_minimal (fun x hx ↦ ⟨hx.1.le, hx.2.le⟩) ?_
    exact (isClosed_le continuous_init.norm continuous_const).inter
      (isClosed_le continuous_abs_apply_last continuous_const)
  · intro x hx
    have ht : Tendsto (fun n : ℕ ↦ (1 - 1 / ((n : ℝ) + 1)) • x) atTop (𝓝 x) := by
      have : Tendsto (fun n : ℕ ↦ (1 - 1 / ((n : ℝ) + 1))) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this.smul_const x
    refine mem_closure_of_tendsto ht (Eventually.of_forall fun n ↦ ?_)
    have h0 : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    have h1 : 1 - 1 / ((n : ℝ) + 1) < 1 := by
      rw [sub_lt_self_iff]; positivity
    refine ⟨?_, ?_⟩
    · rw [init_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
      calc (1 - 1 / ((n : ℝ) + 1)) * ‖init x‖ ≤ (1 - 1 / ((n : ℝ) + 1)) * 1 := by
            gcongr; exact hx.1
        _ < 1 := by linarith
    · rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg h0]
      calc (1 - 1 / ((n : ℝ) + 1)) * |x (Fin.last d)| ≤ (1 - 1 / ((n : ℝ) + 1)) * 1 := by
            gcongr; exact hx.2
        _ < 1 := by linarith

/-- The closure $\overline{Q}$ of the cylinder is compact. -/
theorem isCompact_closure_unitChartCube : IsCompact (closure (unitChartCube d)) :=
  isBounded_unitChartCube.isCompact_closure

/-- The equator is the part of the frontier of $Q_+$ inside $Q$: $Q \cap \partial Q_+ = Q_0$.

This is how the condition "$u = 0$ on $Q_0$" is read for a function $u$ on $Q_+$. -/
theorem unitChartCube_inter_frontier_unitChartCubePos :
    unitChartCube d ∩ frontier (unitChartCubePos d) = unitChartCubeZero d := by
  have hproj : IsOpenMap (fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦ x (Fin.last d)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last d)).isOpenMap fun a ↦
      ⟨single (Fin.last d) a, by simp⟩
  have hfr : frontier (upperHalfSpace d) = {x | x (Fin.last d) = 0} := by
    have : upperHalfSpace d = (fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦ x (Fin.last d)) ⁻¹' Ioi 0 :=
      rfl
    rw [this, ← hproj.preimage_frontier_eq_frontier_preimage (by fun_prop), frontier_Ioi]
    rfl
  rw [unitChartCubePos_eq_inter, inter_comm, inter_comm (unitChartCube d),
    frontier_inter_open_inter isOpen_unitChartCube, hfr]
  ext x
  simp [mem_unitChartCubeZero, and_comm]

/-- The equator lies in the frontier of the upper half cylinder: $Q_0 \subseteq \partial Q_+$. -/
theorem unitChartCubeZero_subset_frontier_unitChartCubePos :
    unitChartCubeZero d ⊆ frontier (unitChartCubePos d) :=
  unitChartCube_inter_frontier_unitChartCubePos.symm.subset.trans inter_subset_right


/-!
### The splitting of Lebesgue measure along the last coordinate

The map $x \mapsto (x_N, x')$ identifies $\mathbb{R}^{d+1}$ with $\mathbb{R} \times \mathbb{R}^d$
and carries Lebesgue measure to the product measure. It is the Fubini step of every argument that
integrates in $x_N$ first.
-/

namespace EuclideanSpace

/-- For $x' \in \mathbb{R}^d$ and $t \in \mathbb{R}$, the point $(x', t)$ of $\mathbb{R}^{d+1}$,
with first coordinates $x'$ and last coordinate $t$. It is the inverse of the splitting
$x \mapsto (x_N, x')$. -/
def snocLast (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ ↦ ℝ) x' t)

/-- For $i < d$, the $i$-th coordinate of $(x', t)$ is $x'_i$. -/
@[simp]
theorem snocLast_apply_castSucc (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) (i : Fin d) :
    snocLast x' t i.castSucc = x' i := by
  simp [snocLast]

/-- The last coordinate of $(x', t)$ is $t$. -/
@[simp]
theorem snocLast_apply_last (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    snocLast x' t (Fin.last d) = t := by
  simp [snocLast]

/-- The first coordinates of $(x', t)$ are $x'$. -/
@[simp]
theorem init_snocLast (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) : init (snocLast x' t) = x' := by
  ext i
  simp

/-- Every point $x$ of $\mathbb{R}^{d+1}$ is the point $(x', x_N)$. -/
@[simp]
theorem snocLast_init_last (x : EuclideanSpace ℝ (Fin (d + 1))) :
    snocLast (init x) (x (Fin.last d)) = x := by
  ext i
  induction i using Fin.lastCases <;> simp

/-- The splitting $x \mapsto (x_N, x')$ of $\mathbb{R}^{d+1}$ as $\mathbb{R} \times \mathbb{R}^d$,
as a continuous linear equivalence. -/
def lastInitL (d : ℕ) : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] ℝ × EuclideanSpace ℝ (Fin d) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x ↦ (x (Fin.last d), init x)
      invFun := fun p ↦ snocLast p.2 p.1
      map_add' := fun x y ↦ by simp
      map_smul' := fun c x ↦ by simp
      left_inv := fun x ↦ by simp
      right_inv := fun p ↦ by simp }

/-- The splitting `EuclideanSpace.lastInitL d` sends $x$ to $(x_N, x')$. -/
@[simp]
theorem lastInitL_apply (x : EuclideanSpace ℝ (Fin (d + 1))) :
    lastInitL d x = (x (Fin.last d), init x) :=
  rfl

/-- The inverse of the splitting `EuclideanSpace.lastInitL d` sends $(t, x')$ to the point $(x', t)$
of $\mathbb{R}^{d+1}$. -/
@[simp]
theorem lastInitL_symm_apply (p : ℝ × EuclideanSpace ℝ (Fin d)) :
    (lastInitL d).symm p = snocLast p.2 p.1 :=
  rfl

/-- The map that sends $(x', t) \in \mathbb{R}^d \times \mathbb{R}$ to the point $(x', t)$ of
$\mathbb{R}^{d+1}$ is continuous. -/
theorem continuous_snocLast :
    Continuous fun p : EuclideanSpace ℝ (Fin d) × ℝ ↦ snocLast p.1 p.2 :=
  (lastInitL d).symm.continuous.comp continuous_swap

/-- The splitting $x \mapsto (x_N, x')$ as a measurable equivalence of $\mathbb{R}^{d+1}$ with
$\mathbb{R} \times \mathbb{R}^d$. -/
def lastInitEquiv (d : ℕ) : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin d) :=
  (lastInitL d).toHomeomorph.toMeasurableEquiv

/-- The measurable equivalence `EuclideanSpace.lastInitEquiv d` sends $x$ to $(x_N, x')$. -/
@[simp]
theorem lastInitEquiv_apply (x : EuclideanSpace ℝ (Fin (d + 1))) :
    lastInitEquiv d x = (x (Fin.last d), init x) :=
  rfl

/-- The inverse of `EuclideanSpace.lastInitEquiv d` sends $(t, x')$ to the point $(x', t)$ of
$\mathbb{R}^{d+1}$. -/
@[simp]
theorem lastInitEquiv_symm_apply (p : ℝ × EuclideanSpace ℝ (Fin d)) :
    (lastInitEquiv d).symm p = snocLast p.2 p.1 :=
  rfl

/-- **The splitting of Lebesgue measure along the last coordinate.** The map $x \mapsto (x_N, x')$
carries Lebesgue measure on $\mathbb{R}^{d+1}$ to the product of the Lebesgue measures on
$\mathbb{R}$ and $\mathbb{R}^d$. -/
theorem measurePreserving_lastInit (d : ℕ) :
    MeasurePreserving (lastInitEquiv d) volume volume := by
  have h1 := PiLp.volume_preserving_ofLp (Fin (d + 1))
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d)
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin d))
  have h := (h3.comp h2).comp h1
  have hfun : ⇑(lastInitEquiv d) = Prod.map id (WithLp.toLp 2) ∘
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) (Fin.last d) ∘ WithLp.ofLp := by
    funext x
    refine Prod.ext rfl ?_
    ext i
    simp [MeasurableEquiv.piFinSuccAbove, init, Fin.init]
  rw [hfun]
  exact h

/-- Fubini's theorem along the last coordinate, for the Lebesgue integral: for an almost everywhere
measurable $f : \mathbb{R}^{d+1} \to [0, \infty]$,
$$\int f(x) \, dx = \int_{\mathbb{R}^d} \int_{\mathbb{R}} f(x', t) \, dt \, dx'.$$
-/
theorem lintegral_lastInit (f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ≥0∞) (hf : AEMeasurable f) :
    ∫⁻ x, f x = ∫⁻ x', ∫⁻ t, f (snocLast x' t) := by
  have h := (measurePreserving_lastInit d).symm (lastInitEquiv d)
  calc ∫⁻ x, f x
      = ∫⁻ p : ℝ × EuclideanSpace ℝ (Fin d), (f ∘ (lastInitEquiv d).symm) p
          ∂((volume : Measure ℝ).prod volume) :=
        (h.lintegral_comp_emb (lastInitEquiv d).symm.measurableEmbedding f).symm
    _ = ∫⁻ x', ∫⁻ t, (f ∘ (lastInitEquiv d).symm) (t, x') :=
        lintegral_prod_symm _ (hf.comp_quasiMeasurePreserving h.quasiMeasurePreserving)
    _ = ∫⁻ x', ∫⁻ t, f (snocLast x' t) := rfl

/-- Fubini's theorem along the last coordinate, for the Bochner integral: for a real normed space
$G$ and an integrable $f : \mathbb{R}^{d+1} \to G$,
$$\int f(x) \, dx = \int_{\mathbb{R}^d} \int_{\mathbb{R}} f(x', t) \, dt \, dx'.$$
-/
theorem integral_lastInit {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : EuclideanSpace ℝ (Fin (d + 1)) → G) (hf : Integrable f) :
    ∫ x, f x = ∫ x', ∫ t, f (snocLast x' t) := by
  have h := (measurePreserving_lastInit d).symm (lastInitEquiv d)
  calc ∫ x, f x
      = ∫ p : ℝ × EuclideanSpace ℝ (Fin d), (f ∘ (lastInitEquiv d).symm) p
          ∂((volume : Measure ℝ).prod volume) :=
        (h.integral_comp' f).symm
    _ = ∫ x', ∫ t, (f ∘ (lastInitEquiv d).symm) (t, x') :=
        integral_prod_symm _ (h.integrable_comp_of_integrable hf)
    _ = ∫ x', ∫ t, f (snocLast x' t) := rfl

/-!
### The splitting $x \mapsto (x', x_N)$, and the vertical lines of $\mathbb{R}^{d+1}$

This part gives the splitting in the order that the implicit function theorem uses
(`EuclideanSpace.initLastL`, which is `EuclideanSpace.lastInitL` with the factors swapped), the
derivative of a vertical line $t \mapsto (x', t)$, and the norms and inner products of points
$(x', t)$.
-/

/-- The splitting $x \mapsto (x', x_N)$ of $\mathbb{R}^{d+1}$ as $\mathbb{R}^d \times \mathbb{R}$,
as a continuous linear equivalence.

It is `EuclideanSpace.lastInitL` followed by the swap of the two factors. This is the order in
which Mathlib's implicit function theorem on a product $E_1 \times E_2$ solves for the second
factor. -/
def initLastL (d : ℕ) :
    EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin d) × ℝ :=
  (lastInitL d).trans (ContinuousLinearEquiv.prodComm ℝ ℝ (EuclideanSpace ℝ (Fin d)))

/-- The splitting `EuclideanSpace.initLastL d` sends $x$ to $(x', x_N)$. -/
@[simp]
theorem initLastL_apply (x : EuclideanSpace ℝ (Fin (d + 1))) :
    initLastL d x = (init x, x (Fin.last d)) :=
  rfl

/-- The inverse of the splitting `EuclideanSpace.initLastL d` sends
$(x', t) \in \mathbb{R}^d \times \mathbb{R}$ to the point $(x', t)$ of $\mathbb{R}^{d+1}$. -/
@[simp]
theorem initLastL_symm_apply (p : EuclideanSpace ℝ (Fin d) × ℝ) :
    (initLastL d).symm p = snocLast p.1 p.2 :=
  rfl

/-- The point $(0, 1)$ of $\mathbb{R}^{d+1}$ is the last standard basis vector $e_N$. -/
theorem snocLast_zero_one :
    snocLast (0 : EuclideanSpace ℝ (Fin d)) 1 = single (Fin.last d) 1 := by
  ext i
  induction i using Fin.lastCases <;> simp [Fin.castSucc_ne_last]

/-- For fixed $x' \in \mathbb{R}^d$, the vertical line $t \mapsto (x', t)$ has the derivative $e_N$
at every $t \in \mathbb{R}$. -/
theorem hasDerivAt_snocLast (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun t ↦ snocLast x' t) (single (Fin.last d) 1) t := by
  have h : HasDerivAt (fun t : ℝ ↦ (x', t)) ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)) t :=
    (hasDerivAt_const t x').prodMk (hasDerivAt_id t)
  have := (initLastL d).symm.hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def, snocLast_zero_one] using this

/-- The vertical line $t \mapsto (x', t)$ is the affine line through $(x', 0)$ and $(x', 1)$:
$(x', t) = (1 - t)(x', 0) + t (x', 1)$. -/
theorem snocLast_eq_lineMap (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    snocLast x' t = AffineMap.lineMap (snocLast x' 0) (snocLast x' 1) t := by
  rw [AffineMap.lineMap_apply_module]
  ext i
  induction i using Fin.lastCases
  · simp
  · simp only [PiLp.add_apply, PiLp.smul_apply, snocLast_apply_castSucc, smul_eq_mul]
    ring

/-- The map $x \mapsto x'$ does not increase distances: $\operatorname{dist}(x', y') \le
\operatorname{dist}(x, y)$. -/
theorem dist_init_le (x y : EuclideanSpace ℝ (Fin (d + 1))) :
    dist (init x) (init y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← init_sub]
  exact norm_init_le _

/-- For $x' \in \mathbb{R}^d$ and $t \in \mathbb{R}$, $\|(x', t)\| \le \|x'\| + |t|$. -/
theorem norm_snocLast_le (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ‖snocLast x' t‖ ≤ ‖x'‖ + |t| := by
  have h := norm_sq_eq_init_add_last (snocLast x' t)
  rw [init_snocLast, snocLast_apply_last] at h
  have h2 : ‖snocLast x' t‖ ^ 2 ≤ (‖x'‖ + |t|) ^ 2 := by
    rw [h]; nlinarith [norm_nonneg x', abs_nonneg t, sq_abs t]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-- For $v \in \mathbb{R}^d$, $\|(v, -1)\| = \sqrt{1 + \|v\|^2}$. -/
theorem norm_snocLast_neg_one (v : EuclideanSpace ℝ (Fin d)) :
    ‖snocLast v (-1)‖ = Real.sqrt (1 + ‖v‖ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (snocLast v (-1))), norm_sq_eq_init_add_last]
  simp [add_comm]

/-- Two points of a vertical line satisfy $\|(x', s) - (x', t)\| = |s - t|$. -/
theorem norm_snocLast_sub_snocLast (x' : EuclideanSpace ℝ (Fin d)) (s t : ℝ) :
    ‖snocLast x' s - snocLast x' t‖ = |s - t| := by
  have h := norm_sq_eq_init_add_last (snocLast x' s - snocLast x' t)
  simp only [init_sub, init_snocLast, sub_self, norm_zero, PiLp.sub_apply, snocLast_apply_last,
    zero_pow two_ne_zero, zero_add] at h
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_sq_eq_abs]

/-- The inner product of two points of $\mathbb{R}^{d+1}$ split along the last coordinate: for
$x, y \in \mathbb{R}^d$ and $s, t \in \mathbb{R}$, $\langle (x, s), (y, t) \rangle = \langle x,
y \rangle + st$. -/
theorem inner_snocLast (x y : EuclideanSpace ℝ (Fin d)) (s t : ℝ) :
    ⟪snocLast x s, snocLast y t⟫_ℝ = ⟪x, y⟫_ℝ + s * t := by
  simp only [PiLp.inner_apply, Fin.sum_univ_castSucc, snocLast_apply_castSucc, snocLast_apply_last,
    RCLike.inner_apply, conj_trivial]
  ring

section Graph

variable {g : EuclideanSpace ℝ (Fin d) → ℝ}

/-- If $g : \mathbb{R}^d \to \mathbb{R}$ is continuous, the graph map $x' \mapsto (x', g(x'))$ is
continuous. -/
theorem continuous_snocLast_graph (hg : Continuous g) :
    Continuous fun x' ↦ snocLast x' (g x') :=
  continuous_snocLast.comp (continuous_id.prodMk hg)

/-- Let $g \in C^1(\mathbb{R}^d)$ and $s \in \mathbb{R}$. The map $x' \mapsto (x', g(x') + s)$ has
at $x'$ the derivative $v \mapsto (v, Dg(x') v)$.

The derivative is written as the inverse of `EuclideanSpace.initLastL` composed with the pair of
the identity and `fderiv ℝ g x'`. -/
theorem hasFDerivAt_snocLast_add (hg : ContDiff ℝ 1 g) (x' : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    HasFDerivAt (fun x' ↦ snocLast x' (g x' + s))
      (((initLastL d).symm : EuclideanSpace ℝ (Fin d) × ℝ →L[ℝ] _).comp
        ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ g x'))) x' := by
  have h1 : HasFDerivAt (fun x' ↦ (x', g x' + s))
      ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ g x')) x' :=
    (hasFDerivAt_id x').prodMk ((hg.differentiable one_ne_zero x').hasFDerivAt.add_const s)
  exact (initLastL d).symm.hasFDerivAt.comp x' h1

/-- For $g : \mathbb{R}^d \to \mathbb{R}$ and $x' \in \mathbb{R}^d$, the linear map
$v \mapsto (v, Dg(x') v)$ sends the standard basis vector $e_i$ of $\mathbb{R}^d$ to
$e_i + \partial_i g(x') \, e_N$ in $\mathbb{R}^{d+1}$, where $\partial_i g(x') = Dg(x') e_i$.

This is the derivative of $x' \mapsto (x', g(x') + s)$ in the direction $e_i$. -/
theorem snocLast_add_fderiv_apply_single (x' : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    ((initLastL d).symm : EuclideanSpace ℝ (Fin d) × ℝ →L[ℝ] _).comp
        ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ g x')) (EuclideanSpace.single i 1)
      = EuclideanSpace.single i.castSucc 1
        + fderiv ℝ g x' (EuclideanSpace.single i 1)
          • EuclideanSpace.single (Fin.last d) (1 : ℝ) := by
  ext j
  induction j using Fin.lastCases <;> simp [Fin.castSucc_ne_last, Fin.castSucc_inj]

end Graph
end EuclideanSpace


/-! ### Local charts, and open sets of class $C^n$ by charts -/

variable {n : WithTop ℕ∞} {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **A local chart of class $C^n$** of $\Omega \subseteq \mathbb{R}^{d+1}$ at a boundary point, as
in the Definition of §9.2 of [brezis2011functional]. A chart consists of an open set $U$ and a
bijection $H : Q \to U$ from the unit cylinder $Q$ with inverse $H^{-1}$, such that
$H \in C^n(\overline{Q})$, $H^{-1} \in C^n(\overline{U})$, $H(Q_+) = U \cap \Omega$ and
$H(Q_0) = U \cap \partial\Omega$.

The regularity on the closures is Mathlib's `ContDiffOn` on `closure (unitChartCube d)` and on
`closure U`. The maps $H$ and $H^{-1}$ are functions on all of $\mathbb{R}^{d+1}$; only the
values of $H$ on $Q$ and of $H^{-1}$ on $U$ matter. -/
structure ContDiffChart (n : WithTop ℕ∞) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) where
  /-- The open neighbourhood $U$ of the boundary point. -/
  U : Set (EuclideanSpace ℝ (Fin (d + 1)))
  /-- The chart $H : Q \to U$. -/
  toFun : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))
  /-- The inverse chart $H^{-1} : U \to Q$. -/
  invFun : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))
  /-- The set $U$ is open. -/
  isOpen_U : IsOpen U
  /-- The chart is of class $C^n$ on the closed cylinder: $H \in C^n(\overline{Q})$. -/
  contDiffOn : ContDiffOn ℝ n toFun (closure (unitChartCube d))
  /-- The inverse chart is of class $C^n$ on the closure of $U$: $H^{-1} \in C^n(\overline{U})$. -/
  contDiffOn_invFun : ContDiffOn ℝ n invFun (closure U)
  /-- The chart $H$ is a bijection of $Q$ onto $U$. -/
  bijOn : BijOn toFun (unitChartCube d) U
  /-- The inverse chart $H^{-1}$ inverts $H$ on $Q$ and on $U$. -/
  invOn : InvOn invFun toFun (unitChartCube d) U
  /-- The chart maps the upper half cylinder onto the part of $U$ in $\Omega$:
  $H(Q_+) = U \cap \Omega$. -/
  image_pos : toFun '' unitChartCubePos d = U ∩ Ω
  /-- The chart maps the equator onto the part of $U$ on the boundary:
  $H(Q_0) = U \cap \partial\Omega$. -/
  image_zero : toFun '' unitChartCubeZero d = U ∩ frontier Ω

namespace ContDiffChart

variable (c : ContDiffChart n Ω)

/-- A chart of class $C^n$ is a chart of class $C^m$ for every $m \le n$, with the same $U$, $H$ and
$H^{-1}$. -/
def ofLE {m : WithTop ℕ∞} (hmn : m ≤ n) : ContDiffChart m Ω :=
  { c with
    contDiffOn := c.contDiffOn.of_le hmn
    contDiffOn_invFun := c.contDiffOn_invFun.of_le hmn }

/-- The chart `c.ofLE hmn` has the same set $U$ as `c`. -/
@[simp] theorem ofLE_U {m : WithTop ℕ∞} (hmn : m ≤ n) : (c.ofLE hmn).U = c.U := rfl

/-- The chart `c.ofLE hmn` has the same map $H$ as `c`. -/
@[simp] theorem ofLE_toFun {m : WithTop ℕ∞} (hmn : m ≤ n) : (c.ofLE hmn).toFun = c.toFun := rfl

/-- The inverse $H^{-1}$ of the chart `c.ofLE hmn` is the inverse of `c`. -/
@[simp] theorem ofLE_invFun {m : WithTop ℕ∞} (hmn : m ≤ n) :
    (c.ofLE hmn).invFun = c.invFun := rfl

/-- A chart $H$ is continuous on the closed cylinder $\overline{Q}$. -/
theorem continuousOn : ContinuousOn c.toFun (closure (unitChartCube d)) :=
  c.contDiffOn.continuousOn

/-- The inverse $H^{-1}$ of a chart is continuous on $\overline{U}$. -/
theorem continuousOn_invFun : ContinuousOn c.invFun (closure c.U) :=
  c.contDiffOn_invFun.continuousOn

/-- A chart $H$ maps $Q$ into $U$. -/
theorem mapsTo : MapsTo c.toFun (unitChartCube d) c.U := c.bijOn.mapsTo

/-- A chart $H$ is injective on $Q$. -/
theorem injOn : InjOn c.toFun (unitChartCube d) := c.bijOn.injOn

/-- A chart $H$ maps $Q$ onto $U$. -/
theorem surjOn : SurjOn c.toFun (unitChartCube d) c.U := c.bijOn.surjOn

/-- A chart maps the cylinder onto its set: $H(Q) = U$. -/
theorem image_unitChartCube : c.toFun '' unitChartCube d = c.U := c.bijOn.image_eq

/-- For $y \in Q$, $H^{-1}(H(y)) = y$. -/
theorem invFun_toFun {y : EuclideanSpace ℝ (Fin (d + 1))} (hy : y ∈ unitChartCube d) :
    c.invFun (c.toFun y) = y :=
  c.invOn.1 hy

/-- For $x \in U$, $H(H^{-1}(x)) = x$. -/
theorem toFun_invFun {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ c.U) :
    c.toFun (c.invFun x) = x :=
  c.invOn.2 hx

/-- The inverse $H^{-1}$ of a chart maps $U$ into $Q$. -/
theorem mapsTo_invFun : MapsTo c.invFun c.U (unitChartCube d) :=
  c.invOn.1.mapsTo c.surjOn

/-- The inverse $H^{-1}$ of a chart is a bijection of $U$ onto $Q$. -/
theorem bijOn_invFun : BijOn c.invFun c.U (unitChartCube d) :=
  c.invOn.symm.bijOn c.mapsTo_invFun c.mapsTo

/-- The inverse $H^{-1}$ of a chart is injective on $U$. -/
theorem injOn_invFun : InjOn c.invFun c.U := c.bijOn_invFun.injOn

/-- The inverse of a chart maps the part of $U$ in $\Omega$ onto the upper half cylinder:
$H^{-1}(U \cap \Omega) = Q_+$. -/
theorem invFun_image_inter : c.invFun '' (c.U ∩ Ω) = unitChartCubePos d := by
  rw [← c.image_pos]
  exact (c.invOn.1.mono unitChartCubePos_subset).image_image

/-- The inverse of a chart maps the part of $U$ on the boundary onto the equator:
$H^{-1}(U \cap \partial\Omega) = Q_0$. -/
theorem invFun_image_inter_frontier : c.invFun '' (c.U ∩ frontier Ω) = unitChartCubeZero d := by
  rw [← c.image_zero]
  exact (c.invOn.1.mono unitChartCubeZero_subset).image_image

/-- For $y \in Q$, $H(y) \in \Omega$ if and only if $y \in Q_+$. -/
theorem toFun_mem_iff {y : EuclideanSpace ℝ (Fin (d + 1))} (hy : y ∈ unitChartCube d) :
    c.toFun y ∈ Ω ↔ y ∈ unitChartCubePos d := by
  constructor
  · intro h
    have : c.toFun y ∈ c.toFun '' unitChartCubePos d := c.image_pos ▸ ⟨c.mapsTo hy, h⟩
    obtain ⟨z, hz, hzy⟩ := this
    rwa [← c.injOn (unitChartCubePos_subset hz) hy hzy]
  · intro h
    exact (c.image_pos ▸ mem_image_of_mem c.toFun h : c.toFun y ∈ c.U ∩ Ω).2

/-- For $y \in Q$, $H(y) \in \partial\Omega$ if and only if $y \in Q_0$. -/
theorem toFun_mem_frontier_iff {y : EuclideanSpace ℝ (Fin (d + 1))} (hy : y ∈ unitChartCube d) :
    c.toFun y ∈ frontier Ω ↔ y ∈ unitChartCubeZero d := by
  constructor
  · intro h
    have : c.toFun y ∈ c.toFun '' unitChartCubeZero d := c.image_zero ▸ ⟨c.mapsTo hy, h⟩
    obtain ⟨z, hz, hzy⟩ := this
    rwa [← c.injOn (unitChartCubeZero_subset hz) hy hzy]
  · intro h
    exact (c.image_zero ▸ mem_image_of_mem c.toFun h : c.toFun y ∈ c.U ∩ frontier Ω).2

/-- For $x \in U$, $H^{-1}(x) \in Q_+$ if and only if $x \in \Omega$. -/
theorem invFun_mem_pos_iff {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ c.U) :
    c.invFun x ∈ unitChartCubePos d ↔ x ∈ Ω := by
  rw [← c.toFun_mem_iff (c.mapsTo_invFun hx), c.toFun_invFun hx]

/-- For $x \in U$, $H^{-1}(x) \in Q_0$ if and only if $x \in \partial\Omega$. -/
theorem invFun_mem_zero_iff {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ c.U) :
    c.invFun x ∈ unitChartCubeZero d ↔ x ∈ frontier Ω := by
  rw [← c.toFun_mem_frontier_iff (c.mapsTo_invFun hx), c.toFun_invFun hx]

/-- The set $U$ of a chart is contained in $H(\overline{Q})$. -/
theorem U_subset_image_closure : c.U ⊆ c.toFun '' closure (unitChartCube d) :=
  c.image_unitChartCube ▸ image_mono subset_closure

/-- The image $H(\overline{Q})$ of the closed cylinder under a chart is compact. -/
theorem isCompact_image_closure : IsCompact (c.toFun '' closure (unitChartCube d)) :=
  isCompact_closure_unitChartCube.image_of_continuousOn c.continuousOn

/-- The set $U$ of a chart is bounded. -/
theorem isBounded_U : Bornology.IsBounded c.U :=
  c.isCompact_image_closure.isBounded.subset c.U_subset_image_closure

/-- The closure of the set $U$ of a chart is compact.

The set $U$ is contained in the compact set $H(\overline{Q})$. -/
theorem isCompact_closure_U : IsCompact (closure c.U) :=
  c.isCompact_image_closure.of_isClosed_subset isClosed_closure
    (c.isCompact_image_closure.isClosed.closure_subset_iff.2 c.U_subset_image_closure)

end ContDiffChart

/-- **An open set of class $C^n$ by local charts**, as in the Definition of §9.2 of
[brezis2011functional]: $\Omega \subseteq \mathbb{R}^{d+1}$ is open, and every boundary point of
$\Omega$ lies in the set $U$ of some chart of class $C^n$ of $\Omega$.

Neither $\Omega$ nor its boundary is required to be bounded. A theorem that needs a bounded
boundary $\Gamma$ states it as a hypothesis. This is the chart counterpart of the graph
condition `IsContDiffDomain`, and `IsContDiffDomain.isContDiffChartDomain` relates the two. -/
def IsContDiffChartDomain (n : WithTop ℕ∞) (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) : Prop :=
  IsOpen Ω ∧ ∀ x₀ ∈ frontier Ω, ∃ c : ContDiffChart n Ω, x₀ ∈ c.U

namespace IsContDiffChartDomain

/-- An open set of class $C^n$ by charts is open. -/
theorem isOpen (h : IsContDiffChartDomain n Ω) : IsOpen Ω := h.1

/-- Every boundary point $x_0$ of an open set of class $C^n$ by charts lies in the set $U$ of some
chart of class $C^n$. -/
theorem exists_chart (h : IsContDiffChartDomain n Ω) {x₀ : EuclideanSpace ℝ (Fin (d + 1))}
    (hx₀ : x₀ ∈ frontier Ω) : ∃ c : ContDiffChart n Ω, x₀ ∈ c.U :=
  h.2 x₀ hx₀

/-- An open set of class $C^n$ by charts is of class $C^m$ by charts for every $m \le n$. -/
theorem of_le {m : WithTop ℕ∞} (h : IsContDiffChartDomain n Ω) (hmn : m ≤ n) :
    IsContDiffChartDomain m Ω :=
  ⟨h.1, fun x₀ hx₀ ↦ let ⟨c, hc⟩ := h.2 x₀ hx₀; ⟨c.ofLE hmn, hc⟩⟩

/-- **A compact part of the boundary is covered by finitely many charts.** Let $\Omega$ be of class
$C^n$ by charts, and let $K \subseteq \partial\Omega$ be compact. Then there are finitely many
charts of class $C^n$ of $\Omega$ whose sets $U$ cover $K$.

This is the finite atlas at the start of the proof of Theorem 9.7 of [brezis2011functional], in
a form that also serves an unbounded boundary met inside a ball (Corollary 9.8 there). The
charts are indexed by `Fin k`. -/
theorem exists_finite_atlas_of_isCompact (h : IsContDiffChartDomain n Ω)
    {K : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hK : IsCompact K) (hKΩ : K ⊆ frontier Ω) :
    ∃ (k : ℕ) (c : Fin k → ContDiffChart n Ω), K ⊆ ⋃ i, (c i).U := by
  have hcov : K ⊆ ⋃ c : ContDiffChart n Ω, c.U := fun x hx ↦
    let ⟨c, hc⟩ := h.2 x (hKΩ hx); mem_iUnion.2 ⟨c, hc⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun c : ContDiffChart n Ω ↦ c.U)
    (fun c ↦ c.isOpen_U) hcov
  refine ⟨t.card, fun i ↦ (t.equivFin.symm i : ContDiffChart n Ω), fun x hx ↦ ?_⟩
  obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.1 (ht hx)
  exact mem_iUnion.2 ⟨t.equivFin ⟨c, hct⟩, by simpa using hxc⟩

/-- **A bounded boundary is covered by finitely many charts.** Let $\Omega$ be of class $C^n$ by
charts with bounded boundary $\partial\Omega$. Then there are finitely many charts of class
$C^n$ of $\Omega$ whose sets $U$ cover $\partial\Omega$. This is the first sentence of the proof
of Theorem 9.7 of [brezis2011functional]. -/
theorem exists_finite_atlas (h : IsContDiffChartDomain n Ω)
    (hΓ : Bornology.IsBounded (frontier Ω)) :
    ∃ (k : ℕ) (c : Fin k → ContDiffChart n Ω), frontier Ω ⊆ ⋃ i, (c i).U :=
  h.exists_finite_atlas_of_isCompact (Metric.isCompact_of_isClosed_isBounded isClosed_frontier hΓ)
    subset_rfl

end IsContDiffChartDomain


/-!
### From a local graph to a local chart

Suppose that, after the rigid motion $T$, the set $\Omega$ is the region above the graph of $g$ near
$x_0$. Then $\Psi(x) = Tx - g((Tx)') \, e_N$ straightens the graph onto the hyperplane $\{y_N = 0\}$
and maps the region above the graph to the upper half space. The chart at $x_0$ is
$H(y) = \Psi^{-1}(\Psi(x_0) + \varepsilon y)$ for a small $\varepsilon > 0$.
-/

namespace EuclideanSpace

variable (T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
  (g : EuclideanSpace ℝ (Fin d) → ℝ)

/-- For a rigid motion $T$ of $\mathbb{R}^{d+1}$ and $g : \mathbb{R}^d \to \mathbb{R}$, the map
$$\Psi(x) = Tx - g((Tx)') \, e_N,$$
which straightens the graph of $g$ seen through $T$: it maps the region
$\{x : (Tx)_N > g((Tx)')\}$ above the graph onto the upper half space. -/
def graphStraighten (x : EuclideanSpace ℝ (Fin (d + 1))) : EuclideanSpace ℝ (Fin (d + 1)) :=
  T x - g (init (T x)) • single (Fin.last d) 1

/-- The inverse of the straightening map `EuclideanSpace.graphStraighten`:
$y \mapsto T^{-1}(y + g(y') \, e_N)$. -/
def graphUnstraighten (y : EuclideanSpace ℝ (Fin (d + 1))) : EuclideanSpace ℝ (Fin (d + 1)) :=
  T.symm (y + g (init y) • single (Fin.last d) 1)

/-- The straightening map $\Psi$ keeps the first coordinates of $Tx$: $\Psi(x)' = (Tx)'$. -/
@[simp]
theorem init_graphStraighten (x : EuclideanSpace ℝ (Fin (d + 1))) :
    init (graphStraighten T g x) = init (T x) := by
  simp [graphStraighten]

/-- The last coordinate of the straightening map is $\Psi(x)_N = (Tx)_N - g((Tx)')$. -/
theorem graphStraighten_apply_last (x : EuclideanSpace ℝ (Fin (d + 1))) :
    graphStraighten T g x (Fin.last d) = T x (Fin.last d) - g (init (T x)) := by
  simp [graphStraighten]

/-- The map `EuclideanSpace.graphUnstraighten` is a left inverse of the straightening map $\Psi$. -/
@[simp]
theorem graphUnstraighten_graphStraighten (x : EuclideanSpace ℝ (Fin (d + 1))) :
    graphUnstraighten T g (graphStraighten T g x) = x := by
  simp [graphUnstraighten, graphStraighten]

/-- The map `EuclideanSpace.graphUnstraighten` is a right inverse of the straightening map $\Psi$.
-/
@[simp]
theorem graphStraighten_graphUnstraighten (y : EuclideanSpace ℝ (Fin (d + 1))) :
    graphStraighten T g (graphUnstraighten T g y) = y := by
  simp [graphStraighten, graphUnstraighten]

/-- A rigid motion $T$ of $\mathbb{R}^{d+1}$ is of class $C^n$ for every $n$. -/
theorem contDiff_affineIsometryEquiv {n : WithTop ℕ∞} : ContDiff ℝ n T :=
  T.toAffineIsometry.toContinuousAffineMap.contDiff

/-- If $g$ is of class $C^n$, then the straightening map $\Psi$ is of class $C^n$. -/
theorem contDiff_graphStraighten {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (graphStraighten T g) :=
  (contDiff_affineIsometryEquiv T).sub
    ((hg.comp (contDiff_init.comp (contDiff_affineIsometryEquiv T))).smul contDiff_const)

/-- If $g$ is of class $C^n$, then the inverse of the straightening map is of class $C^n$. -/
theorem contDiff_graphUnstraighten {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (graphUnstraighten T g) :=
  (contDiff_affineIsometryEquiv T.symm).comp
    (contDiff_id.add ((hg.comp contDiff_init).smul contDiff_const))

end EuclideanSpace

section Bridge

variable {x₀ : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ}
  {T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1))}
  {g : EuclideanSpace ℝ (Fin d) → ℝ}

/-- **A boundary point of a set that is locally above a graph lies on the graph.** Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open, let $T$ be a rigid motion of $\mathbb{R}^{d+1}$,
let $g : \mathbb{R}^d \to \mathbb{R}$ be continuous, let $r > 0$, and suppose that
$$\Omega \cap B(x_0, r) = \{x \in B(x_0, r) : (Tx)_N > g((Tx)')\}.$$
If $x_0 \in \partial\Omega$, then $(Tx_0)_N = g((Tx_0)')$.

A point strictly above the graph would be an interior point of $\Omega$, and a point strictly
below the graph would have a neighbourhood that misses $\Omega$. -/
theorem IsBoundaryGraphAt.last_eq_of_mem_frontier (hg : Continuous g) (hΩ : IsOpen Ω)
    (hx₀ : x₀ ∈ frontier Ω) (hr : 0 < r)
    (hgraph : Ω ∩ Metric.ball x₀ r =
      {x ∈ Metric.ball x₀ r | g (init (T x)) < T x (Fin.last d)}) :
    T x₀ (Fin.last d) = g (init (T x₀)) := by
  have hgraph' : ∀ x, x ∈ Ω ∩ Metric.ball x₀ r ↔
      x ∈ Metric.ball x₀ r ∧ g (init (T x)) < T x (Fin.last d) := fun x ↦ by
    rw [hgraph]; exact Iff.rfl
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- strictly below the graph: a neighbourhood of `x₀` misses `Ω`
    have hcont : Continuous fun x : EuclideanSpace ℝ (Fin (d + 1)) ↦ T x (Fin.last d) :=
      continuous_apply_last.comp T.continuous
    have hWo : IsOpen {x : EuclideanSpace ℝ (Fin (d + 1)) |
        x ∈ Metric.ball x₀ r ∧ T x (Fin.last d) < g (init (T x))} :=
      Metric.isOpen_ball.inter (isOpen_lt hcont (hg.comp (continuous_init.comp T.continuous)))
    obtain ⟨x, ⟨hxb, hxlt⟩, hxΩ⟩ :=
      mem_closure_iff.1 hx₀.1 _ hWo ⟨Metric.mem_ball_self hr, hlt⟩
    have := ((hgraph' x).1 ⟨hxΩ, hxb⟩).2
    exact absurd this (not_lt.2 hxlt.le)
  · -- strictly above the graph: `x₀` is an interior point of `Ω`
    have : x₀ ∈ Ω := ((hgraph' x₀).2 ⟨Metric.mem_ball_self hr, hgt⟩).1
    exact hx₀.2 (by rwa [hΩ.interior_eq])

open EuclideanSpace in
/-- **The chart at a boundary point of a locally graphical set.** Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open, let $T$ be a rigid motion of $\mathbb{R}^{d+1}$,
let $g : \mathbb{R}^d \to \mathbb{R}$ be of class $C^n$, let $r > 0$, and suppose that
$$\Omega \cap B(x_0, r) = \{x \in B(x_0, r) : (Tx)_N > g((Tx)')\}.$$
If $x_0 \in \partial\Omega$, then $x_0$ lies in the set $U$ of some chart of class $C^n$ of
$\Omega$.

The chart is $H(y) = \Psi^{-1}(\Psi(x_0) + \varepsilon y)$ for the straightening map $\Psi$
(`EuclideanSpace.graphStraighten`) and a small $\varepsilon > 0$. -/
theorem IsBoundaryGraphAt.exists_contDiffChart (hg : ContDiff ℝ n g) (hΩ : IsOpen Ω)
    (hx₀ : x₀ ∈ frontier Ω) (hr : 0 < r)
    (hgraph : Ω ∩ Metric.ball x₀ r =
      {x ∈ Metric.ball x₀ r | g (init (T x)) < T x (Fin.last d)}) :
    ∃ c : ContDiffChart n Ω, x₀ ∈ c.U := by
  set Ψ := graphStraighten T g with hΨ
  set Ψ' := graphUnstraighten T g with hΨ'
  have hΨΨ' : ∀ y, Ψ (Ψ' y) = y := graphStraighten_graphUnstraighten T g
  have hΨ'Ψ : ∀ x, Ψ' (Ψ x) = x := graphUnstraighten_graphStraighten T g
  have hΨd : ContDiff ℝ n Ψ := contDiff_graphStraighten T g hg
  have hΨ'd : ContDiff ℝ n Ψ' := contDiff_graphUnstraighten T g hg
  have hΨ'c : Continuous Ψ' := hΨ'd.continuous
  set y₀ := Ψ x₀ with hy₀def
  have hy₀ : y₀ (Fin.last d) = 0 := by
    rw [hy₀def, hΨ, graphStraighten_apply_last,
      IsBoundaryGraphAt.last_eq_of_mem_frontier hg.continuous hΩ hx₀ hr hgraph, sub_self]
  -- the scale `ε` of the chart
  obtain ⟨δ, hδ, hδball⟩ : ∃ δ > 0, ∀ z, dist z y₀ < δ → Ψ' z ∈ Metric.ball x₀ r := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hΨ'c.continuousAt (x := y₀)) r hr
    exact ⟨δ, hδ, fun z hz ↦ by simpa [Metric.mem_ball, hy₀def, hΨ'Ψ] using h hz⟩
  set ε := δ / 4 with hε
  have hε0 : 0 < ε := by positivity
  set H : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) :=
    fun y ↦ Ψ' (y₀ + ε • y) with hH
  set Hinv : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)) :=
    fun x ↦ ε⁻¹ • (Ψ x - y₀) with hHinv
  have hHinvH : ∀ y, Hinv (H y) = y := fun y ↦ by
    simp [hH, hHinv, hΨΨ', smul_smul, inv_mul_cancel₀ hε0.ne']
  have hHHinv : ∀ x, H (Hinv x) = x := fun x ↦ by
    simp [hH, hHinv, smul_smul, mul_inv_cancel₀ hε0.ne', hΨ'Ψ]
  have hHd : ContDiff ℝ n H := hΨ'd.comp (contDiff_const.add (contDiff_id.const_smul ε))
  have hHinvd : ContDiff ℝ n Hinv := (hΨd.sub contDiff_const).const_smul ε⁻¹
  let e : EuclideanSpace ℝ (Fin (d + 1)) ≃ₜ EuclideanSpace ℝ (Fin (d + 1)) :=
    { toFun := H
      invFun := Hinv
      left_inv := hHinvH
      right_inv := hHHinv
      continuous_toFun := hHd.continuous
      continuous_invFun := hHinvd.continuous }
  -- the chart sends the cylinder into the ball where `Ω` is a graph
  have hball : ∀ y ∈ unitChartCube d, H y ∈ Metric.ball x₀ r := fun y hy ↦ by
    refine hδball _ ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε0.le]
    have : ‖y‖ < 2 := by simpa using unitChartCube_subset_ball hy
    calc ε * ‖y‖ ≤ ε * 2 := by gcongr
      _ < δ := by rw [hε]; linarith
  have hmemΩ : ∀ y ∈ unitChartCube d, (H y ∈ Ω ↔ y ∈ unitChartCubePos d) := fun y hy ↦ by
    have h1 : H y ∈ Ω ↔ H y ∈ Ω ∩ Metric.ball x₀ r := (and_iff_left (hball y hy)).symm
    rw [h1, hgraph, mem_ofPred_eq, and_iff_right (hball y hy), mem_unitChartCubePos,
      and_iff_right hy]
    have hlast : T (H y) (Fin.last d) - g (init (T (H y))) = ε * y (Fin.last d) := by
      have := congrArg (fun z : EuclideanSpace ℝ (Fin (d + 1)) ↦ z (Fin.last d)) (hΨΨ' (y₀ + ε • y))
      simpa [hΨ, graphStraighten_apply_last, hy₀] using this
    rw [← sub_pos, hlast, mul_pos_iff_of_pos_left hε0]
  have hQpos : unitChartCube d ∩ H ⁻¹' Ω = unitChartCubePos d := by
    ext y
    constructor
    · rintro ⟨hy, hyΩ⟩
      exact (hmemΩ y hy).1 hyΩ
    · intro hy
      exact ⟨unitChartCubePos_subset hy, (hmemΩ y (unitChartCubePos_subset hy)).2 hy⟩
  have hQzero : unitChartCube d ∩ H ⁻¹' frontier Ω = unitChartCubeZero d := by
    have h1 : H ⁻¹' frontier Ω = frontier (H ⁻¹' Ω) := e.preimage_frontier Ω
    have h2 := frontier_inter_open_inter (s := H ⁻¹' Ω) isOpen_unitChartCube
    rw [h1, ← unitChartCube_inter_frontier_unitChartCubePos, ← hQpos,
      inter_comm (unitChartCube d) (H ⁻¹' Ω), inter_comm, ← h2, inter_comm]
  refine ⟨{ U := H '' unitChartCube d
            toFun := H
            invFun := Hinv
            isOpen_U := e.isOpenMap _ isOpen_unitChartCube
            contDiffOn := hHd.contDiffOn
            contDiffOn_invFun := hHinvd.contDiffOn
            bijOn := e.injective.injOn.bijOn_image
            invOn := ⟨fun y _ ↦ hHinvH y, fun x _ ↦ hHHinv x⟩
            image_pos := by rw [← hQpos, image_inter_preimage]
            image_zero := by rw [← hQzero, image_inter_preimage] }, ?_⟩
  exact ⟨0, zero_mem_unitChartCube, by simp [hH, hy₀def, hΨ'Ψ]⟩

end Bridge

/-- **Graphs give charts.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a $C^n$ domain in the sense
of `IsContDiffDomain`: $\Omega$ is open, and its boundary is locally the graph of a $C^n$
function after a rigid motion of the coordinates (Definition 7.2.1 of [han2009theoretical]).
Then $\Omega$ is an open set of class $C^n$ by charts in the sense of §9.2 of
[brezis2011functional].

This is the elementary direction of the equivalence of the two definitions. Through it, every
result stated for open sets of class $C^n$ by charts applies to the graph domains of the finite
element literature. -/
theorem IsContDiffDomain.isContDiffChartDomain (h : IsContDiffDomain n Ω) :
    IsContDiffChartDomain n Ω := by
  refine ⟨h.isOpen, fun x₀ hx₀ ↦ ?_⟩
  obtain ⟨r, hr, T, g, hg, hgraph⟩ := h.isBoundaryOfClass x₀ hx₀
  exact IsBoundaryGraphAt.exists_contDiffChart hg h.isOpen hx₀ hr hgraph

/-- The half space $\mathbb{R}^{d+1}_+$ is an open set of class $C^n$ by charts, for every $n$. This
is the case $\Omega = \mathbb{R}^N_+$ of Theorem 9.7 of [brezis2011functional], read as an
instance of the definition. -/
theorem isContDiffChartDomain_upperHalfSpace :
    IsContDiffChartDomain n (EuclideanSpace.upperHalfSpace d) :=
  IsContDiffDomain.isContDiffChartDomain
    ⟨EuclideanSpace.isOpen_upperHalfSpace, isBoundaryOfClass_upperHalfSpace contDiff_const⟩


/-! ### The partition of unity of Lemma 9.3 -/

section PartitionOfUnity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Partition of unity.** Let $E$ be a finite-dimensional real normed space, let
$\Gamma \subseteq E$ be compact, and let $(U_i)_{i \in \iota}$ be a finite family of open sets
that covers $\Gamma$. There are smooth functions $\theta_0$ and $\theta_i$, $i \in \iota$, from
$E$ to $[0, 1]$, such that
$$\theta_0 + \sum_{i \in \iota} \theta_i = 1 \quad \text{on } E,$$
each $\theta_i$ has compact support contained in $U_i$, and the support of $\theta_0$ is
disjoint from $\Gamma$, so that $\theta_0$ vanishes on a neighbourhood of $\Gamma$. This is
Lemma 9.3 of [brezis2011functional].

The supports are the closed supports `tsupport`. The proof applies Mathlib's
`SmoothPartitionOfUnity.exists_isSubordinate` to the open cover of $E$ by $E \setminus \Gamma$
and the sets $U_i \cap B(0, R)$, where $B(0, R)$ is a ball that contains $\Gamma$. The
intersection with the ball makes the supports compact. -/
theorem IsCompact.exists_contDiff_partitionOfUnity [FiniteDimensional ℝ E] {Γ : Set E}
    (hΓ : IsCompact Γ) {ι : Type*} [Fintype ι] {U : ι → Set E} (hU : ∀ i, IsOpen (U i))
    (hΓU : Γ ⊆ ⋃ i, U i) :
    ∃ (θ₀ : E → ℝ) (θ : ι → E → ℝ), ContDiff ℝ ∞ θ₀ ∧ (∀ i, ContDiff ℝ ∞ (θ i)) ∧
      (∀ x, θ₀ x ∈ Icc (0 : ℝ) 1) ∧ (∀ i x, θ i x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, θ₀ x + ∑ i, θ i x = 1) ∧ (∀ i, HasCompactSupport (θ i)) ∧
      (∀ i, tsupport (θ i) ⊆ U i) ∧ Disjoint (tsupport θ₀) Γ := by
  obtain ⟨R, hR⟩ := hΓ.isBounded.subset_ball 0
  let V : Option ι → Set E := fun j ↦ j.elim Γᶜ fun i ↦ U i ∩ Metric.ball 0 R
  have hVo : ∀ j, IsOpen (V j) := by
    rintro (_ | i)
    · exact hΓ.isClosed.isOpen_compl
    · exact (hU i).inter Metric.isOpen_ball
  have hVcov : (univ : Set E) ⊆ ⋃ j, V j := fun x _ ↦ by
    by_cases hx : x ∈ Γ
    · obtain ⟨i, hi⟩ := mem_iUnion.1 (hΓU hx)
      exact mem_iUnion.2 ⟨some i, hi, hR hx⟩
    · exact mem_iUnion.2 ⟨none, hx⟩
  obtain ⟨f, hf⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, E)) isClosed_univ V hVo hVcov
  refine ⟨f none, fun i ↦ f (some i), contMDiff_iff_contDiff.1 (f none).contMDiff,
    fun i ↦ contMDiff_iff_contDiff.1 (f (some i)).contMDiff,
    fun x ↦ ⟨f.nonneg none x, f.le_one none x⟩, fun i x ↦ ⟨f.nonneg _ x, f.le_one _ x⟩,
    fun x ↦ ?_, fun i ↦ ?_, fun i ↦ (hf (some i)).trans inter_subset_left,
    disjoint_compl_left.mono_left (hf none)⟩
  · have := f.sum_eq_one (mem_univ x)
    rwa [finsum_eq_sum_of_fintype, Fintype.sum_option] at this
  · exact Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _)
      (Metric.isBounded_ball.subset ((hf (some i)).trans inter_subset_right))

/-- The derivatives of a smooth partition of unity sum to zero: if $\theta_0$ and $\theta_i$ are
smooth with $\theta_0 + \sum_i \theta_i = 1$, then $D\theta_0(z) v + \sum_i D\theta_i(z) v = 0$
for all $z, v \in E$. -/
theorem fderiv_add_sum_eq_zero_of_partition {ι : Type*} [Fintype ι] {θ₀ : E → ℝ}
    {θ : ι → E → ℝ} (hθ₀ : ContDiff ℝ ∞ θ₀) (hθ : ∀ i, ContDiff ℝ ∞ (θ i))
    (hsum : ∀ x, θ₀ x + ∑ i, θ i x = 1) (z v : E) :
    fderiv ℝ θ₀ z v + ∑ i, fderiv ℝ (θ i) z v = 0 := by
  have h1 : HasFDerivAt (fun x ↦ θ₀ x + ∑ i, θ i x)
      (fderiv ℝ θ₀ z + ∑ i, fderiv ℝ (θ i) z) z :=
    (hθ₀.differentiable (by simp) z).hasFDerivAt.add
      (HasFDerivAt.fun_sum fun i _ ↦ ((hθ i).differentiable (by simp) z).hasFDerivAt)
  have h2 : HasFDerivAt (fun x ↦ θ₀ x + ∑ i, θ i x) (0 : E →L[ℝ] ℝ) z := by
    have : (fun x ↦ θ₀ x + ∑ i, θ i x) = fun _ ↦ (1 : ℝ) := funext hsum
    rw [this]
    exact hasFDerivAt_const 1 z
  have := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) (h1.unique h2)
  simpa using this

end PartitionOfUnity

/-- Let $\Omega$ be an open subset of a topological space, and let $K$ be disjoint from the frontier
$\partial\Omega$. Then $K \cap \overline{\Omega} \subseteq \Omega$.

This is how "$\theta_0|_\Omega \in C_c^\infty(\Omega)$" is read for the function $\theta_0$ of
`IsCompact.exists_contDiff_partitionOfUnity` with $\Gamma = \partial\Omega$. The closed support
of $\theta_0$ meets $\overline{\Omega}$ in a closed subset of $\Omega$, which is compact when
$\Omega$ is bounded (`IsClosed.isCompact_inter_closure_of_isBounded`). -/
theorem inter_closure_subset_of_disjoint_frontier {X : Type*} [TopologicalSpace X] {K Ω : Set X}
    (hΩ : IsOpen Ω) (h : Disjoint K (frontier Ω)) : K ∩ closure Ω ⊆ Ω := by
  rintro x ⟨hxK, hxc⟩
  by_contra hxΩ
  exact disjoint_left.1 h hxK ⟨hxc, fun hi ↦ hxΩ (hΩ.interior_eq ▸ hi)⟩

/-- In a proper pseudometric space, if $K$ is closed and $\Omega$ is bounded, then
$K \cap \overline{\Omega}$ is compact. -/
theorem IsClosed.isCompact_inter_closure_of_isBounded {X : Type*} [PseudoMetricSpace X]
    [ProperSpace X] {K Ω : Set X} (hK : IsClosed K) (hΩ : Bornology.IsBounded Ω) :
    IsCompact (K ∩ closure Ω) :=
  Metric.isCompact_of_isClosed_isBounded (hK.inter isClosed_closure)
    (hΩ.closure.subset inter_subset_right)

/-! ### Bounded derivatives, and diffeomorphisms with bounded Jacobians -/

section Jacobian

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **A $C^1$ function on a compact set has a bounded derivative on the interior of the set.** Let
$\mathbb{K}$ be a nontrivially normed field, let $E$ and $F$ be normed spaces over $\mathbb{K}$,
let $s \subseteq E$ be compact, and let $f : E \to F$ be of class $C^1$ on $s$. Then there is
$M$ with $\|Df(x)\| \le M$ for every $x$ in the interior of $s$.

No unique differentiability of $s$ is required. At each point of $s$ the derivative is read off
the local Taylor data of `ContDiffWithinAt`; at interior points this is the ordinary derivative,
and it is continuous, hence bounded, near the point. Compactness makes the bound uniform. -/
theorem ContDiffOn.exists_norm_fderiv_le_of_isCompact {f : E → F} {s : Set E}
    (hf : ContDiffOn 𝕜 1 f s) (hs : IsCompact s) :
    ∃ M, ∀ x ∈ interior s, ‖fderiv 𝕜 f x‖ ≤ M := by
  -- a local bound near each point of `s`
  have key : ∀ x ∈ s, ∃ W ∈ 𝓝 x, ∃ M : ℝ, ∀ y ∈ W ∩ interior s, ‖fderiv 𝕜 f y‖ ≤ M := by
    intro x hx
    have h1 : ContDiffWithinAt 𝕜 (0 + 1) f s x := by simpa using hf x hx
    obtain ⟨u, hu, -, f', hf', hf'c⟩ :=
      (contDiffWithinAt_succ_iff_hasFDerivWithinAt (n := 0) (by simp)).1 h1
    rw [insert_eq_of_mem hx] at hu
    have hxu : x ∈ u := mem_of_mem_nhdsWithin hx hu
    obtain ⟨v, hv, hcont⟩ := (contDiffWithinAt_zero hxu).1 hf'c
    have hxv : x ∈ v := mem_of_mem_nhdsWithin hxu hv
    have hev : ∀ᶠ y in 𝓝 x, y ∈ u ∩ v → ‖f' y‖ ≤ ‖f' x‖ + 1 := by
      rw [← eventually_nhdsWithin_iff]
      filter_upwards [(hcont x ⟨hxu, hxv⟩).eventually (Metric.ball_mem_nhds (f' x) one_pos)]
        with y hy
      have := mem_ball_iff_norm.1 hy
      linarith [norm_sub_norm_le (f' y) (f' x)]
    obtain ⟨A, hA, hAu⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hu
    obtain ⟨B, hB, hBv⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hv
    obtain ⟨C, hC, hCev⟩ := eventually_iff_exists_mem.1 hev
    obtain ⟨A', hA'A, hA'o, hxA'⟩ := mem_nhds_iff.1 hA
    refine ⟨A' ∩ B ∩ C, inter_mem (inter_mem (hA'o.mem_nhds hxA') hB) hC, ‖f' x‖ + 1, ?_⟩
    rintro y ⟨⟨⟨hyA', hyB⟩, hyC⟩, hyi⟩
    have hyu : y ∈ u := hAu ⟨hA'A hyA', interior_subset hyi⟩
    have hyv : y ∈ v := hBv ⟨hyB, hyu⟩
    have hu_nhds : u ∈ 𝓝 y := by
      refine mem_of_superset ((hA'o.inter isOpen_interior).mem_nhds ⟨hyA', hyi⟩) ?_
      rintro z ⟨hzA', hzi⟩
      exact hAu ⟨hA'A hzA', interior_subset hzi⟩
    rw [((hf' y hyu).hasFDerivAt hu_nhds).fderiv]
    exact hCev y hyC ⟨hyu, hyv⟩
  choose! W hW M hM using key
  obtain ⟨t, hts, htW⟩ := hs.elim_nhds_subcover W hW
  obtain ⟨M₀, hM₀⟩ := (t.image M).exists_le
  refine ⟨M₀, fun y hy ↦ ?_⟩
  obtain ⟨x, hxt, hyW⟩ := mem_iUnion₂.1 (htW (interior_subset hy))
  exact (hM x (hts x hxt) y ⟨hyW, hy⟩).trans (hM₀ _ (Finset.mem_image_of_mem M hxt))

end Jacobian

section Diffeo

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

/-- Let $E$ and $E'$ be real normed spaces, let $s \subseteq E'$ and $t \subseteq E$, and let
$M \in \mathbb{R}$. A map $H : E' \to E$ is a **$C^1$ diffeomorphism of $s$ onto $t$ with
Jacobians bounded by $M$**, with inverse $H^{-1} : E \to E'$ (`Hinv`), if $s$ and $t$ are open,
$H$ is a bijection of $s$ onto $t$ with inverse $H^{-1}$, $H \in C^1(s)$, $H^{-1} \in C^1(t)$,
and
$$\|DH(y)\| \le M \text{ for } y \in s, \qquad \|DH^{-1}(x)\| \le M \text{ for } x \in t.$$
These are the hypotheses of Proposition 9.6 of [brezis2011functional] with its footnote 6,
$\operatorname{Jac} H \in L^\infty(s)$ and $\operatorname{Jac} H^{-1} \in L^\infty(t)$.

The sets are open, so the derivatives are the ordinary ones. A chart restricted to $Q_+$
satisfies these hypotheses (`ContDiffChart.isDiffeoOnWithBoundedJacobian_pos`). -/
structure IsDiffeoOnWithBoundedJacobian (H : E' → E) (Hinv : E → E') (s : Set E') (t : Set E)
    (M : ℝ) : Prop where
  /-- The source $s$ is open. -/
  isOpen_source : IsOpen s
  /-- The target $t$ is open. -/
  isOpen_target : IsOpen t
  /-- The map $H$ is a bijection of $s$ onto $t$. -/
  bijOn : BijOn H s t
  /-- The map $H^{-1}$ inverts $H$ on $s$ and on $t$. -/
  invOn : InvOn Hinv H s t
  /-- The map $H$ is of class $C^1$ on $s$. -/
  contDiffOn : ContDiffOn ℝ 1 H s
  /-- The map $H^{-1}$ is of class $C^1$ on $t$. -/
  contDiffOn_invFun : ContDiffOn ℝ 1 Hinv t
  /-- The derivative of $H$ is bounded by $M$ on $s$. -/
  norm_fderiv_le : ∀ y ∈ s, ‖fderiv ℝ H y‖ ≤ M
  /-- The derivative of $H^{-1}$ is bounded by $M$ on $t$. -/
  norm_fderiv_invFun_le : ∀ x ∈ t, ‖fderiv ℝ Hinv x‖ ≤ M

namespace IsDiffeoOnWithBoundedJacobian

variable {H : E' → E} {Hinv : E → E'} {s : Set E'} {t : Set E} {M : ℝ}

/-- If $H$ is a $C^1$ diffeomorphism of $s$ onto $t$ with inverse $H^{-1}$ and Jacobians bounded by
$M$, then $H^{-1}$ is a $C^1$ diffeomorphism of $t$ onto $s$ with inverse $H$ and Jacobians
bounded by $M$. -/
theorem symm (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) :
    IsDiffeoOnWithBoundedJacobian Hinv H t s M where
  isOpen_source := h.isOpen_target
  isOpen_target := h.isOpen_source
  bijOn := h.invOn.symm.bijOn (h.invOn.1.mapsTo h.bijOn.surjOn) h.bijOn.mapsTo
  invOn := h.invOn.symm
  contDiffOn := h.contDiffOn_invFun
  contDiffOn_invFun := h.contDiffOn
  norm_fderiv_le := h.norm_fderiv_invFun_le
  norm_fderiv_invFun_le := h.norm_fderiv_le

/-- If $H$ is a $C^1$ diffeomorphism of $s$ onto $t$ with Jacobians bounded by $M$, then its
Jacobians are bounded by every $M' \ge M$. -/
theorem mono_bound {M' : ℝ} (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) (hM : M ≤ M') :
    IsDiffeoOnWithBoundedJacobian H Hinv s t M' :=
  { h with
    norm_fderiv_le := fun y hy ↦ (h.norm_fderiv_le y hy).trans hM
    norm_fderiv_invFun_le := fun x hx ↦ (h.norm_fderiv_invFun_le x hx).trans hM }

/-- If $H$ is a $C^1$ diffeomorphism of $s$ onto $t$ with inverse $H^{-1}$ and Jacobians bounded by
$M$, and $A \subseteq s$ is open, then $H$ is a $C^1$ diffeomorphism of $A$ onto $H(A)$ with
inverse $H^{-1}$ and Jacobians bounded by $M$. -/
theorem restrict (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M)
    {A : Set E'} (hA : IsOpen A) (hAs : A ⊆ s) :
    IsDiffeoOnWithBoundedJacobian H Hinv A (H '' A) M where
  isOpen_source := hA
  isOpen_target := by
    have e : H '' A = t ∩ Hinv ⁻¹' A := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨h.bijOn.mapsTo (hAs hy), by rw [mem_preimage, h.invOn.1 (hAs hy)]; exact hy⟩
      · rintro ⟨hx, hx'⟩
        exact ⟨Hinv x, hx', h.invOn.2 hx⟩
    rw [e]
    exact h.contDiffOn_invFun.continuousOn.isOpen_inter_preimage h.isOpen_target hA
  bijOn := (h.bijOn.injOn.mono hAs).bijOn_image
  invOn := ⟨h.invOn.1.mono hAs, fun x hx ↦ h.invOn.2 (h.bijOn.mapsTo.image_subset (by
    exact (image_mono hAs) hx))⟩
  contDiffOn := h.contDiffOn.mono hAs
  contDiffOn_invFun := h.contDiffOn_invFun.mono (h.bijOn.mapsTo.image_subset.trans' (image_mono
    hAs))
  norm_fderiv_le := fun y hy ↦ h.norm_fderiv_le y (hAs hy)
  norm_fderiv_invFun_le := fun x hx ↦
    h.norm_fderiv_invFun_le x (h.bijOn.mapsTo.image_subset (image_mono hAs hx))

end IsDiffeoOnWithBoundedJacobian

end Diffeo

namespace ContDiffChart

variable (c : ContDiffChart n Ω)

/-- **The Jacobians of a chart are bounded.** For a chart of class $C^n$ with $n \ge 1$, there is
$M$ with $\|DH(y)\| \le M$ for every $y \in Q$ and $\|DH^{-1}(x)\| \le M$ for every $x \in U$.

The maps $H$ and $H^{-1}$ are of class $C^1$ on the compact closures $\overline{Q}$ and
$\overline{U}$ (`ContDiffOn.exists_norm_fderiv_le_of_isCompact`). -/
theorem exists_norm_fderiv_le (hn : 1 ≤ n) :
    ∃ M, (∀ y ∈ unitChartCube d, ‖fderiv ℝ c.toFun y‖ ≤ M) ∧
      ∀ x ∈ c.U, ‖fderiv ℝ c.invFun x‖ ≤ M := by
  obtain ⟨M₁, hM₁⟩ :=
    (c.contDiffOn.of_le hn).exists_norm_fderiv_le_of_isCompact isCompact_closure_unitChartCube
  obtain ⟨M₂, hM₂⟩ :=
    (c.contDiffOn_invFun.of_le hn).exists_norm_fderiv_le_of_isCompact c.isCompact_closure_U
  refine ⟨max M₁ M₂, fun y hy ↦ ?_, fun x hx ↦ ?_⟩
  · exact (hM₁ y (isOpen_unitChartCube.subset_interior_iff.2 subset_closure hy)).trans
      (le_max_left _ _)
  · exact (hM₂ x (c.isOpen_U.subset_interior_iff.2 subset_closure hx)).trans (le_max_right _ _)

/-- **A chart is a $C^1$ diffeomorphism with bounded Jacobians.** For a chart of class $C^n$ with
$n \ge 1$, the map $H$ is a $C^1$ diffeomorphism of $Q$ onto $U$ with inverse $H^{-1}$ and
Jacobians bounded by some $M$. -/
theorem isDiffeoOnWithBoundedJacobian (hn : 1 ≤ n) :
    ∃ M, IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (unitChartCube d) c.U M := by
  obtain ⟨M, hM₁, hM₂⟩ := c.exists_norm_fderiv_le hn
  exact ⟨M, isOpen_unitChartCube, c.isOpen_U, c.bijOn, c.invOn,
    (c.contDiffOn.of_le hn).mono subset_closure, (c.contDiffOn_invFun.of_le hn).mono subset_closure,
    hM₁, hM₂⟩

/-- **A chart restricted to the half cylinder is a $C^1$ diffeomorphism with bounded Jacobians.**
Let $\Omega$ be open. For a chart of class $C^n$ of $\Omega$ with $n \ge 1$, the map $H$ is a
$C^1$ diffeomorphism of $Q_+$ onto $U \cap \Omega$ with inverse $H^{-1}$ and Jacobians bounded
by some $M$.

This is the form in which Proposition 9.6 of [brezis2011functional] is applied in step (b) of
the proof of Theorem 9.7 there, the transfer $v_i(y) = u(H_i(y))$. -/
theorem isDiffeoOnWithBoundedJacobian_pos (hn : 1 ≤ n) (hΩ : IsOpen Ω) :
    ∃ M, IsDiffeoOnWithBoundedJacobian c.toFun c.invFun (unitChartCubePos d) (c.U ∩ Ω) M := by
  obtain ⟨M, hM₁, hM₂⟩ := c.exists_norm_fderiv_le hn
  refine ⟨M, isOpen_unitChartCubePos, c.isOpen_U.inter hΩ, ?_,
    ⟨c.invOn.1.mono unitChartCubePos_subset, c.invOn.2.mono inter_subset_left⟩,
    (c.contDiffOn.of_le hn).mono (unitChartCubePos_subset.trans subset_closure),
    (c.contDiffOn_invFun.of_le hn).mono (inter_subset_left.trans subset_closure),
    fun y hy ↦ hM₁ y (unitChartCubePos_subset hy), fun x hx ↦ hM₂ x hx.1⟩
  rw [← c.image_pos]
  exact (c.injOn.mono unitChartCubePos_subset).bijOn_image

end ContDiffChart

end
