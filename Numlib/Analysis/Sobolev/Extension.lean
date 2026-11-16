/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Reflection.lean` and `Numlib/Analysis/Sobolev/Chart.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.Reflection

/-!
# The extension operator for an open set of class $C^1$ with bounded boundary

Let $\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^1$ whose boundary $\partial\Omega$ is
bounded, and let $1 \le p \le \infty$. This module constructs a bounded linear **extension
operator** $P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ with $Pu = u$ almost everywhere on
$\Omega$, $\|Pu\|_{L^p(\mathbb{R}^N)} \le C \|u\|_{L^p(\Omega)}$ and $\|Pu\|_{W^{1,p}(\mathbb{R}^N)}
\le C \|u\|_{W^{1,p}(\Omega)}$. This is Theorem 9.7 of [brezis2011functional], and the presentation
follows §9.2 of that book: Theorem 9.7 and its proof, Corollary 9.8 and Remark 9. As a consequence,
for $1 \le p < \infty$ the restrictions to $\Omega$ of the functions of $C_c^\infty(\mathbb{R}^N)$
are dense in $W^{1,p}(\Omega)$ (Corollary 9.8), also when $\partial\Omega$ is not bounded. The
module also constructs an extension operator for the unit square $(0, 1)^2$, which is not of class
$C^1$ (Remark 9).

Points of $\mathbb{R}^N$, $N = d + 1$, are written $x = (x', x_N)$ with $x' \in \mathbb{R}^d$, and
$|x'|$ is the Euclidean norm. A local chart $H$ maps the unit cylinder
$Q = \{x : |x'| < 1, |x_N| < 1\}$ onto an open set $U$, and the upper half cylinder
$Q_+ = Q \cap \{x_N > 0\}$ onto $U \cap \Omega$. The cylinder of radius $r$ is
$Q_r = \{x : |x'| < r, |x_N| < r\}$, and $\sigma$ is the reflection $(x', x_N) \mapsto (x', -x_N)$
across the hyperplane $x_N = 0$. The proofs use the reflection lemma of
`Numlib.Analysis.Sobolev.Reflection`, the charts of `Numlib.Analysis.Sobolev.Chart`, the transport
along diffeomorphisms of `Numlib.Analysis.Sobolev.Calculus`, and the cut-offs and zero extensions of
`Numlib.Analysis.Sobolev.Cutoff` and `Numlib.Analysis.Sobolev.Operators`.

## Main definitions

* `cylinder`: the open cylinder $Q_r$.
* `scaleLast`: the linear map $(x', x_N) \mapsto (x', l x_N)$.
* `SobolevEuclidean.chartExtendL`: the chart-local extension $W^{1,p}(\Omega) \to W^{1,p}(U)$ of a
  chart $H : Q \to U$, which restricts to $U \cap \Omega$, transports to $Q_+$ along $H$, reflects
  to $Q$ and transports back to $U$ along $H^{-1}$.
* `EuclideanSpace.rect`: the open rectangle $(a_1, b_1) \times (a_2, b_2)$ of $\mathbb{R}^2$.

## Main results

* `SobolevEuclidean.chartExtendL_fn_ae_eq`, `SobolevEuclidean.exists_eLpNorm_fn_chartExtendL_le`:
  the chart-local extension of $u$ agrees with $u$ on $U \cap \Omega$, and its $L^p(U)$ norm is at
  most a constant times $\|u\|_{L^p(U \cap \Omega)}$.
* `SobolevEuclidean.exists_extensionL_of_atlas`: an extension operator for the functions $u$ with
  $u = \chi u$, given finitely many charts that cover a compact set $K$ and a cut-off $\chi$ whose
  support meets $\partial\Omega$ only in $K$.
* `SobolevEuclidean.exists_extensionL`: the extension theorem, Theorem 9.7 of
  [brezis2011functional], for an open set of class $C^1$ with bounded boundary.
* `IsSobolevExtensionDomain.of_isContDiffChartDomain`,
  `IsSobolevExtensionDomain.of_isContDiffDomain`: an open set of class $C^1$ with bounded boundary,
  defined by charts or by graphs, is a $W^{1,p}$-extension domain.
* `SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_isBounded_frontier`: Corollary
  9.8, the density of the restrictions of $C_c^\infty(\mathbb{R}^N)$ in $W^{1,p}(\Omega)$, when
  $\partial\Omega$ is bounded.
* `SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto`: Corollary 9.8 for every open set
  of class $C^1$.
* `SobolevEuclidean.exists_reflectionStep`: an extension operator by reflection across a translated
  hyperplane.
* `SobolevEuclidean.exists_extensionL_unitSquare`: Remark 9, an extension operator for the unit
  square $(0, 1)^2$.
* `IsSobolevExtensionDomain.of_extension_step`: an open set that extends into a $W^{1,p}$-extension
  domain is a $W^{1,p}$-extension domain.

## Proof outline

The proof of Theorem 9.7 is the one of the book. Finitely many charts $H_i : Q \to U_i$, $i < k$,
cover the compact boundary (`IsContDiffChartDomain.exists_finite_atlas`), and Lemma 9.3 gives smooth
functions with $\theta_0 + \sum_i \theta_i = 1$, $\theta_i$ compactly supported in $U_i$ and
$\theta_0$ zero near $\partial\Omega$ (`IsCompact.exists_contDiff_partitionOfUnity`). In step (a),
$\bar u_0 = \theta_0 u$ extended by zero is in $W^{1,p}(\mathbb{R}^N)$
(`SobolevMultiIndex.extendZeroMulL`), because $\theta_0$ is a cut-off for $\Omega$
(`IsSobolevCutoff`): $\nabla\theta_0 = -\sum_i \nabla\theta_i$ has compact support, and $\theta_0$
vanishes near $\partial\Omega$. In step (b), for each chart, $u$ is restricted to $U_i \cap \Omega$
(`SobolevMultiIndex.restrictL`), transported to $Q_+$ along $H_i$ (Proposition 9.6,
`SobolevMultiIndex.compDiffeoL`), reflected to $Q$ (Lemma 9.2, `SobolevEuclidean.evenReflectionL`)
and transported back to $U_i$ along $H_i^{-1}$; this is `SobolevEuclidean.chartExtendL`. The result
is multiplied by $\theta_i$ and extended by zero, which gives $\hat u_i$. In step (c),
$Pu = \bar u_0 + \sum_i \hat u_i$. Its restriction to $\Omega$ is
$(\theta_0 + \sum_i \theta_i) u = u$, and its norms are bounded by products of the constants of the
steps.

The extension operator of the unit square is the composite of four reflections across the sides
$x_2 = 0$, $x_2 = 1$, $x_1 = 0$ and $x_1 = 1$ (`SobolevEuclidean.exists_reflectionStep`), which
reach $W^{1,p}((-1, 3)^2)$, and of the multiplication by a smooth cut-off followed by extension by
zero. The assembly is `SobolevEuclidean.exists_extensionL_of_steps`.

## Implementation notes

* An element $u$ of $W^{1,p}(\Omega)$ carries a function `SobolevMultiIndex.fn u` on all of
  $\mathbb{R}^N$. "$Pu = u$ on $\Omega$" means that the two functions agree almost everywhere on
  $\Omega$, and the $L^p$ norms are `MeasureTheory.eLpNorm` of these functions for the Lebesgue
  measure restricted to the set. The space $\mathbb{R}^N$ is the open set `⊤`, and the exponent
  $1 \le p \le \infty$ is `p : ℝ≥0∞` with `[Fact (1 ≤ p)]`.
* Theorem 9.7 is stated existentially, as `∃ P C, …`, as the book states it, because its uses only
  need some operator. The constant `C` is a real number, the $L^p$ bound uses `ENNReal.ofReal C`,
  and the bound $\|Pu\| \le C \|u\|$ is in the norm of `SobolevEuclidean`, which is the $W^{1,p}$
  norm.
* The construction goes through `SobolevEuclidean.exists_extensionL_of_atlas`, which takes an
  explicit finite atlas that covers a compact piece $K$ of the boundary and a cut-off $\chi$ with
  $\operatorname{supp} \chi \cap \partial\Omega \subseteq K$, and extends the functions with
  $u = \chi u$. Theorem 9.7 is the case $K = \partial\Omega$ and $\chi = 1$.
* Every identity about the composite operators is proved first with the operators as variables
  (`SobolevEuclidean.chartExtend_fn_of_ops`, `SobolevEuclidean.exists_extensionL_of_ops` and the
  other `_of_ops` lemmas), and then instantiated once. With the concrete operators
  `SobolevMultiIndex.compDiffeoL` and `SobolevEuclidean.evenReflectionL` in a goal, each rewrite
  needs about a second of unification, and the proofs exceed the default heartbeat limit.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace EuclideanSpace
open scoped ContDiff Distributions ENNReal Topology RealInnerProductSpace

noncomputable section

/-! ### The cylinder under the reflection across `x_N = 0` -/

section Cylinder

variable {d : ℕ}

/-- Let $E$ be a real inner product space and let $v \in E$ be a unit vector, $\|v\| = 1$. The
reflection $\sigma$ across the hyperplane $v^\perp$ (`hyperplaneReflection v`) is
$$\sigma x = x - 2 \langle x, v \rangle v$$
for every $x \in E$. -/
theorem hyperplaneReflection_apply_of_norm_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : E} (hv : ‖v‖ = 1) (x : E) :
    hyperplaneReflection v x = x - (2 * ⟪x, v⟫) • v := by
  rw [hyperplaneReflection, Submodule.reflection_apply, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton, hv, real_inner_comm]
  simp only [one_pow, two_smul, mul_smul, RCLike.ofReal_one, div_one]
  abel

/-- The reflection $\sigma$ across the hyperplane $x_N = 0$ of $\mathbb{R}^N$, $N = d + 1$, negates
the last coordinate and keeps the others: $(\sigma x)_i = -x_N$ if $i = N$, and
$(\sigma x)_i = x_i$ otherwise.

Here $\sigma$ is `hyperplaneReflection` of the last unit vector $e_N$, and the index $N$ is
`Fin.last d`. -/
theorem hyperplaneReflection_single_last_apply (x : EuclideanSpace ℝ (Fin (d + 1)))
    (i : Fin (d + 1)) :
    hyperplaneReflection (single (Fin.last d) (1 : ℝ)) x i
      = if i = Fin.last d then -x (Fin.last d) else x i := by
  rw [hyperplaneReflection_apply_of_norm_eq_one EuclideanSpace.norm_single_last_one,
    EuclideanSpace.inner_single_last_one, PiLp.sub_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h; ring
  · ring

/-- The reflection $\sigma$ across $x_N = 0$ keeps the first $N - 1$ coordinates: $(\sigma x)' = x'$
for every $x \in \mathbb{R}^N$. -/
theorem init_hyperplaneReflection_single_last (x : EuclideanSpace ℝ (Fin (d + 1))) :
    init (hyperplaneReflection (single (Fin.last d) (1 : ℝ)) x) = init x := by
  ext i
  simp [hyperplaneReflection_single_last_apply, Fin.castSucc_ne_last]

/-- The reflection $\sigma$ across $x_N = 0$ negates the last coordinate: $(\sigma x)_N = -x_N$ for
every $x \in \mathbb{R}^N$. -/
theorem hyperplaneReflection_single_last_apply_last (x : EuclideanSpace ℝ (Fin (d + 1))) :
    hyperplaneReflection (single (Fin.last d) (1 : ℝ)) x (Fin.last d) = -x (Fin.last d) := by
  simp [hyperplaneReflection_single_last_apply]

/-- The unit cylinder $Q$ is invariant under the reflection $\sigma$ across $x_N = 0$: for every
$x \in \mathbb{R}^N$, $\sigma x \in Q$ if and only if $x \in Q$. -/
theorem mem_unitChartCube_hyperplaneReflection_iff (x : EuclideanSpace ℝ (Fin (d + 1))) :
    hyperplaneReflection (single (Fin.last d) (1 : ℝ)) x ∈ unitChartCube d ↔
      x ∈ unitChartCube d := by
  simp [mem_unitChartCube, init_hyperplaneReflection_single_last,
    hyperplaneReflection_single_last_apply_last]

/-- The unit cylinder $Q$ is symmetric under the reflection $\sigma$ across $x_N = 0$:
$\sigma(Q) = Q$. -/
theorem hyperplaneReflection_image_unitChartCube :
    hyperplaneReflection (single (Fin.last d) (1 : ℝ)) '' unitChartCube d = unitChartCube d := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_unitChartCube_hyperplaneReflection_iff y).2 hy
  · intro hx
    exact ⟨hyperplaneReflection _ x, (mem_unitChartCube_hyperplaneReflection_iff x).2 hx,
      hyperplaneReflection_hyperplaneReflection _ x⟩

/-- The unit cylinder $Q = \{(x', x_N) : |x'| < 1, |x_N| < 1\}$ of $\mathbb{R}^{d+1}$
(`unitChartCube d`), as an element of `TopologicalSpace.Opens`. -/
def unitChartCubeOpens (d : ℕ) : Opens (EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨unitChartCube d, isOpen_unitChartCube⟩

/-- The underlying set of `unitChartCubeOpens d` is the unit cylinder `unitChartCube d`. -/
@[simp]
theorem coe_unitChartCubeOpens : (unitChartCubeOpens d : Set _) = unitChartCube d := rfl

/-- The unit cylinder $Q$, as an open set `unitChartCubeOpens d`, is symmetric under the reflection
$\sigma$ across $x_N = 0$: $\sigma(Q) = Q$. -/
theorem hyperplaneReflection_image_unitChartCubeOpens :
    hyperplaneReflection (single (Fin.last d) (1 : ℝ)) '' (unitChartCubeOpens d : Set _)
      = unitChartCubeOpens d :=
  hyperplaneReflection_image_unitChartCube

/-- The positive half of the unit cylinder $Q$ for the unit vector $e_N$, that is
$Q \cap \{x : \langle x, e_N \rangle > 0\}$ (`posHalf`), is the upper half cylinder
$Q_+ = Q \cap \{x_N > 0\}$ (`unitChartCubePos d`). -/
theorem coe_posHalf_unitChartCubeOpens :
    (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d) : Set _)
      = unitChartCubePos d := by
  ext x
  simp [coe_posHalf, unitChartCubePos, EuclideanSpace.inner_single_last_one]

end Cylinder

/-- Let $\sigma : \alpha \to \alpha$ be an involution, $\sigma \circ \sigma = \mathrm{id}$, and let
$s \subseteq \alpha$ satisfy $\sigma x \in s \iff x \in s$ for every $x$. Then $\sigma(s) = s$. -/
theorem Function.Involutive.image_eq_of_forall_mem_iff {α : Type*} {σ : α → α}
    (hσ : Function.Involutive σ) {s : Set α} (h : ∀ x, σ x ∈ s ↔ x ∈ s) : σ '' s = s := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (h y).2 hy
  · intro hx
    exact ⟨σ x, (h x).2 hx, hσ x⟩

/-! ### Scaling the last coordinate, and the cylinders $Q_r$ -/

section ScaleLast

variable {d : ℕ}

/-- For $l \in \mathbb{R}$, the continuous linear map $(x', x_N) \mapsto (x', l x_N)$ of
$\mathbb{R}^{d+1}$, which scales the last coordinate by $l$.

For $l < 0$ it maps the lower half space into the upper half space. The reflection for
higher-order Sobolev spaces is a linear combination of the compositions with `scaleLast (l j)`
for several factors $l_j$. -/
def scaleLast (l : ℝ) : EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
  ContinuousLinearMap.id ℝ _ +
    (l - 1) • (EuclideanSpace.proj (Fin.last d)).smulRight (single (Fin.last d) (1 : ℝ))

/-- The coordinates of `scaleLast l x`: the last coordinate is $l x_N$, and every other coordinate
$x_i$ is unchanged. -/
theorem scaleLast_apply (l : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin (d + 1)) :
    scaleLast l x i = if i = Fin.last d then l * x (Fin.last d) else x i := by
  simp only [scaleLast, add_apply, ContinuousLinearMap.id_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, PiLp.add_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h; ring
  · ring

/-- The last coordinate of `scaleLast l x` is $l x_N$. -/
@[simp]
theorem scaleLast_apply_last (l : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    scaleLast l x (Fin.last d) = l * x (Fin.last d) := by
  simp [scaleLast_apply]

/-- The map `scaleLast l` keeps the first $d$ coordinates $x'$. -/
@[simp]
theorem init_scaleLast (l : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    init (scaleLast l x) = init x := by
  ext i
  simp [scaleLast_apply, Fin.castSucc_ne_last]

/-- Scaling the last coordinate by $l'$ and then by $l$ is scaling it by $l l'$: `scaleLast l
(scaleLast l' x) = scaleLast (l * l') x`. -/
theorem scaleLast_scaleLast (l l' : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    scaleLast l (scaleLast l' x) = scaleLast (l * l') x := by
  ext i
  simp only [scaleLast_apply]
  split_ifs with h
  · subst h; simp [mul_assoc]
  · rfl

/-- Scaling the last coordinate by $1$ is the identity. -/
theorem scaleLast_one (x : EuclideanSpace ℝ (Fin (d + 1))) : scaleLast 1 x = x := by
  ext i
  simp only [scaleLast_apply]
  split_ifs with h
  · subst h; ring
  · rfl

/-- Scaling the last coordinate fixes every point of the hyperplane $x_N = 0$. -/
theorem scaleLast_of_apply_last_eq_zero (l : ℝ) {x : EuclideanSpace ℝ (Fin (d + 1))}
    (hx : x (Fin.last d) = 0) : scaleLast l x = x := by
  ext i
  simp only [scaleLast_apply]
  split_ifs with h
  · subst h; rw [hx, mul_zero]
  · rfl

/-- For $l \neq 0$, the map `scaleLast l` as a continuous linear equivalence of $\mathbb{R}^{d+1}$,
with inverse `scaleLast l⁻¹`. -/
def scaleLastEquiv {l : ℝ} (hl : l ≠ 0) :
    EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
  ContinuousLinearEquiv.equivOfInverse (scaleLast l) (scaleLast l⁻¹)
    (fun x ↦ by rw [scaleLast_scaleLast, inv_mul_cancel₀ hl, scaleLast_one])
    (fun x ↦ by rw [scaleLast_scaleLast, mul_inv_cancel₀ hl, scaleLast_one])

/-- The equivalence `scaleLastEquiv hl` acts as `scaleLast l`. -/
@[simp]
theorem scaleLastEquiv_apply {l : ℝ} (hl : l ≠ 0) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    scaleLastEquiv hl x = scaleLast l x :=
  rfl

/-- The inverse of `scaleLastEquiv hl` acts as `scaleLast l⁻¹`. -/
@[simp]
theorem scaleLastEquiv_symm_apply {l : ℝ} (hl : l ≠ 0) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    (scaleLastEquiv hl).symm x = scaleLast l⁻¹ x :=
  rfl

/-- Let $l \neq 0$, let $L$ be the map $(x', x_N) \mapsto (x', l x_N)$ (`scaleLast l`), and let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open. Then for some $M$ the map $L$ is a $C^1$
diffeomorphism of $L^{-1}(\Omega)$ onto $\Omega$, with inverse $(x', x_N) \mapsto (x', x_N / l)$
and with derivatives bounded by $M$ (`IsDiffeoOnWithBoundedJacobian`). -/
theorem scaleLast_isDiffeoOnWithBoundedJacobian {l : ℝ} (hl : l ≠ 0)
    (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
    ∃ M, IsDiffeoOnWithBoundedJacobian (scaleLast l) (scaleLast l⁻¹)
      (scaleLast l ⁻¹' (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) M := by
  have h := isDiffeoOnWithBoundedJacobian_affine (scaleLastEquiv hl) 0 Ω
  simp only [scaleLastEquiv_apply, add_zero, scaleLastEquiv_symm_apply, sub_zero] at h
  exact ⟨_, h⟩

end ScaleLast

section CylinderR

variable {d : ℕ}

/-- The **cylinder**
$$Q_r = \{(x', x_N) \in \mathbb{R}^{d+1} : |x'| < r, \ |x_N| < r\}$$
of radius $r$, as an open set. For $r \le 1$ it lies in the unit cylinder $Q$, and for $r < 1$
its closure is a compact subset of $Q$.

The chart-local extensions for higher-order Sobolev spaces are defined on these cylinders. A
chart of class $C^k$ is of class $C^k$ on the closure of $Q$ only, and the transport of
$W^{k,p}$ along a map needs the map to be of class $C^k$ on an open neighbourhood of the closure
of its source. For $r < 1$ the set $Q$ is such a neighbourhood of the closure of $Q_r$. -/
def cylinder (d : ℕ) (r : ℝ) : Opens (EuclideanSpace ℝ (Fin (d + 1))) :=
  ⟨{x | ‖init x‖ < r ∧ |x (Fin.last d)| < r},
    (isOpen_lt continuous_init.norm continuous_const).inter
      (isOpen_lt continuous_abs_apply_last continuous_const)⟩

/-- A point $x$ lies in $Q_r$ if and only if $|x'| < r$ and $|x_N| < r$. -/
theorem mem_cylinder {r : ℝ} {x : EuclideanSpace ℝ (Fin (d + 1))} :
    x ∈ cylinder d r ↔ ‖init x‖ < r ∧ |x (Fin.last d)| < r :=
  Iff.rfl

/-- For $r \le 1$, the cylinder $Q_r$ lies in the unit cylinder $Q$. -/
theorem cylinder_subset_unitChartCube {r : ℝ} (hr : r ≤ 1) :
    (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ unitChartCube d :=
  fun _ hx ↦ ⟨hx.1.trans_le hr, hx.2.trans_le hr⟩

/-- The closure of $Q_r$ lies in the closed cylinder $\{x : |x'| \le r, |x_N| \le r\}$. -/
theorem closure_cylinder_subset (r : ℝ) :
    closure (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))
      ⊆ {x | ‖init x‖ ≤ r ∧ |x (Fin.last d)| ≤ r} :=
  closure_minimal (fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩)
    ((isClosed_le continuous_init.norm continuous_const).inter
      (isClosed_le continuous_abs_apply_last continuous_const))

/-- For $r < 1$, the closure of $Q_r$ lies in the open unit cylinder $Q$. -/
theorem closure_cylinder_subset_unitChartCube {r : ℝ} (hr : r < 1) :
    closure (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ unitChartCube d :=
  fun _ hx ↦ ⟨(closure_cylinder_subset r hx).1.trans_lt hr,
    (closure_cylinder_subset r hx).2.trans_lt hr⟩

/-- The cylinder $Q_r$ is bounded. -/
theorem isBounded_cylinder (r : ℝ) :
    Bornology.IsBounded (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) := by
  refine (isBounded_iff_forall_norm_le.2 ⟨2 * |r|, fun x hx ↦ ?_⟩)
  have h1 : ‖x‖ ^ 2 ≤ (2 * |r|) ^ 2 := by
    rw [norm_sq_eq_init_add_last]
    have hr : 0 ≤ |r| := abs_nonneg r
    have hi : ‖init x‖ ≤ |r| := hx.1.le.trans (le_abs_self r)
    have hl : |x (Fin.last d)| ≤ |r| := hx.2.le.trans (le_abs_self r)
    nlinarith [sq_abs (x (Fin.last d)), abs_nonneg (x (Fin.last d)), norm_nonneg (init x)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

/-- The closure of the cylinder $Q_r$ is compact. -/
theorem isCompact_closure_cylinder (r : ℝ) :
    IsCompact (closure (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  (isBounded_cylinder r).isCompact_closure

/-- The cylinder $Q_r$ has finite Lebesgue measure. -/
theorem volume_cylinder_lt_top (r : ℝ) :
    volume (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) < ⊤ :=
  (isBounded_cylinder r).measure_lt_top

/-- The cylinder $Q_r$ is convex. -/
theorem convex_cylinder (r : ℝ) :
    Convex ℝ (cylinder d r : Set (EuclideanSpace ℝ (Fin (d + 1)))) := by
  have e1 : {x : EuclideanSpace ℝ (Fin (d + 1)) | ‖init x‖ < r}
      = initL.toLinearMap ⁻¹' ball (0 : EuclideanSpace ℝ (Fin d)) r := by
    ext x; simp [initL_apply, mem_ball, dist_zero_right]
  have e2 : {x : EuclideanSpace ℝ (Fin (d + 1)) | |x (Fin.last d)| < r}
      = (EuclideanSpace.proj (Fin.last d)).toLinearMap ⁻¹' ball (0 : ℝ) r := by
    ext x; simp [mem_ball]
  have h1 : Convex ℝ {x : EuclideanSpace ℝ (Fin (d + 1)) | ‖init x‖ < r} := by
    rw [e1]; exact (convex_ball _ _).linear_preimage _
  have h2 : Convex ℝ {x : EuclideanSpace ℝ (Fin (d + 1)) | |x (Fin.last d)| < r} := by
    rw [e2]; exact (convex_ball _ _).linear_preimage _
  exact h1.inter h2

/-- The cylinder $Q_r$ is symmetric under the reflection $\sigma$ across $x_N = 0$:
$\sigma(Q_r) = Q_r$. -/
theorem hyperplaneReflection_image_cylinder (r : ℝ) :
    hyperplaneReflection (single (Fin.last d) (1 : ℝ)) '' (cylinder d r : Set _) = cylinder d r :=
      by
  refine Function.Involutive.image_eq_of_forall_mem_iff (hyperplaneReflection_hyperplaneReflection
    _)
    fun x ↦ ?_
  simp [mem_cylinder, init_hyperplaneReflection_single_last,
    hyperplaneReflection_single_last_apply_last]

/-- If $|l| \le 1$ and $x \in Q_r$, then $(x', l x_N) \in Q_r$: the map `scaleLast l` maps $Q_r$
into itself. -/
theorem scaleLast_mem_cylinder {l r : ℝ} (hl : |l| ≤ 1) {x : EuclideanSpace ℝ (Fin (d + 1))}
    (hx : x ∈ cylinder d r) : scaleLast l x ∈ cylinder d r := by
  refine ⟨by rw [init_scaleLast]; exact hx.1, ?_⟩
  rw [scaleLast_apply_last, abs_mul]
  calc |l| * |x (Fin.last d)| ≤ 1 * |x (Fin.last d)| :=
        mul_le_mul_of_nonneg_right hl (abs_nonneg _)
    _ = |x (Fin.last d)| := one_mul _
    _ < r := hx.2

/-- The positive half of $Q_r$ for the unit vector $e_N$ (`posHalf`) is $Q_r \cap \{x_N > 0\}$. -/
theorem coe_posHalf_cylinder (r : ℝ) :
    (posHalf (single (Fin.last d) (1 : ℝ)) (cylinder d r) : Set (EuclideanSpace ℝ (Fin (d + 1))))
      = (cylinder d r : Set _) ∩ {x | 0 < x (Fin.last d)} := by
  rw [coe_posHalf]
  ext x
  simp [EuclideanSpace.inner_single_last_one]

/-- If $K$ is a compact subset of the unit cylinder $Q$, then $K \subseteq Q_r$ for some $r < 1$. -/
theorem exists_lt_one_subset_cylinder {K : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hK : IsCompact K) (hKQ : K ⊆ unitChartCube d) : ∃ r, r < 1 ∧ K ⊆ cylinder d r := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, zero_lt_one, empty_subset _⟩
  obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hne
    (continuous_init.norm.max continuous_abs_apply_last).continuousOn
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = max ‖init x₀‖ |x₀ (Fin.last d)| := ⟨_, rfl⟩
  have hm1 : m < 1 := by rw [hm]; exact max_lt (hKQ hx₀).1 (hKQ hx₀).2
  refine ⟨(m + 1) / 2, by linarith, fun x hx ↦ ?_⟩
  have h : max ‖init x‖ |x (Fin.last d)| ≤ m := by rw [hm]; exact hmax hx
  exact ⟨by linarith [le_max_left ‖init x‖ |x (Fin.last d)|],
    by linarith [le_max_right ‖init x‖ |x (Fin.last d)|]⟩

end CylinderR

/-!
### The chart-local extension

Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open, let $1 \le p \le \infty$, and let $H : Q \to U$ be
a chart of class $C^1$ of $\Omega$ (`ContDiffChart 1 Ω`), with inverse $H^{-1}$. Step (b) of the
proof of Theorem 9.7 of [brezis2011functional] maps $W^{1,p}(\Omega)$ to $W^{1,p}(U)$ in four steps:
restriction to $U \cap \Omega$, transport to $Q_+$ along $H$, even reflection to $Q$, and transport
back to $U$ along $H^{-1}$.
-/

section ChartLocal

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

namespace ContDiffChart

variable (c : ContDiffChart 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- The range $U$ of a chart $H : Q \to U$, as an open set. -/
def opensU : Opens (EuclideanSpace ℝ (Fin (d + 1))) := ⟨c.U, c.isOpen_U⟩

/-- The underlying set of `c.opensU` is the range $U$ of the chart. -/
@[simp]
theorem coe_opensU : (c.opensU : Set _) = c.U := rfl

/-- The intersection $U \cap \Omega$ of the range $U$ of a chart with $\Omega$, as an open set. -/
def opensInter : Opens (EuclideanSpace ℝ (Fin (d + 1))) := ⟨c.U ∩ Ω, c.isOpen_U.inter Ω.isOpen⟩

/-- The underlying set of `c.opensInter` is $U \cap \Omega$. -/
@[simp]
theorem coe_opensInter : (c.opensInter : Set _) = c.U ∩ Ω := rfl

/-- The set $U \cap \Omega$ is contained in $\Omega$. -/
theorem opensInter_le : c.opensInter ≤ Ω := fun _ hx ↦ hx.2

/-- The set $U \cap \Omega$ is contained in the range $U$ of the chart. -/
theorem opensInter_le_opensU : c.opensInter ≤ c.opensU := fun _ hx ↦ hx.1

/-- Let $H : Q \to U$ be a chart of class $C^1$ of an open set $\Omega \subseteq \mathbb{R}^{d+1}$.
Then for some $M$ the chart $H$ is a $C^1$ diffeomorphism of the upper half cylinder $Q_+$ onto
$U \cap \Omega$, with inverse $H^{-1}$ and with derivatives bounded by $M$
(`IsDiffeoOnWithBoundedJacobian`).

The set $Q_+$ is written as the positive half `posHalf e_N Q` of the cylinder. -/
theorem exists_isDiffeoOnWithBoundedJacobian_posHalf :
    ∃ M, IsDiffeoOnWithBoundedJacobian c.toFun c.invFun
      (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d) : Set _)
      (c.opensInter : Set _) M := by
  rw [coe_posHalf_unitChartCubeOpens, coe_opensInter]
  exact c.isDiffeoOnWithBoundedJacobian_pos le_rfl Ω.isOpen

/-- Let $H : Q \to U$ be a chart of class $C^1$ of an open set $\Omega \subseteq \mathbb{R}^{d+1}$.
Then for some $M$ the inverse $H^{-1}$ is a $C^1$ diffeomorphism of $U$ onto the unit cylinder
$Q$, with inverse $H$ and with derivatives bounded by $M$ (`IsDiffeoOnWithBoundedJacobian`). -/
theorem exists_isDiffeoOnWithBoundedJacobian_invFun :
    ∃ M, IsDiffeoOnWithBoundedJacobian c.invFun c.toFun (c.opensU : Set _)
      (unitChartCubeOpens d : Set _) M := by
  obtain ⟨M, hM⟩ := c.isDiffeoOnWithBoundedJacobian le_rfl
  exact ⟨M, hM.symm⟩

end ContDiffChart

namespace SobolevEuclidean

variable (p) (c : ContDiffChart 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- For a chart $H : Q \to U$ of class $C^1$ of $\Omega$, the restriction
$W^{1,p}(\Omega) \to W^{1,p}(U \cap \Omega)$, $u \mapsto u|_{U \cap \Omega}$. This is the first
map of step (b) of the proof of Theorem 9.7 of [brezis2011functional]. -/
def chartRestrictL :
    SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p c.opensInter :=
  SobolevMultiIndex.restrictL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p volume
    c.opensInter_le

/-- For a chart $H : Q \to U$ of class $C^1$ of $\Omega$, the transport
$W^{1,p}(U \cap \Omega) \to W^{1,p}(Q_+)$, $v \mapsto v \circ H$. This is the second map of step
(b) of the proof of Theorem 9.7 of [brezis2011functional].

It is `SobolevMultiIndex.compDiffeoL` (Proposition 9.6) for the diffeomorphism of
`ContDiffChart.exists_isDiffeoOnWithBoundedJacobian_posHalf`. -/
def chartTransferL : SobolevEuclidean (d + 1) 1 p c.opensInter →L[ℝ]
    SobolevEuclidean (d + 1) 1 p (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d)) :=
  SobolevMultiIndex.compDiffeoL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume
    c.exists_isDiffeoOnWithBoundedJacobian_posHalf.choose_spec

/-- The even reflection $W^{1,p}(Q_+) \to W^{1,p}(Q)$, $v \mapsto v^\star$, across the hyperplane
$x_N = 0$, where $v^\star(x', x_N) = v(x', |x_N|)$. This is the third map of step (b) of the
proof of Theorem 9.7 of [brezis2011functional].

It is `SobolevEuclidean.evenReflectionL` (Lemma 9.2) for the open set $Q$ and the unit vector
$e_N$. -/
def cubeReflectL : SobolevEuclidean (d + 1) 1 p
    (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d)) →L[ℝ]
    SobolevEuclidean (d + 1) 1 p (unitChartCubeOpens d) :=
  SobolevEuclidean.evenReflectionL EuclideanSpace.norm_single_last_one
    hyperplaneReflection_image_unitChartCubeOpens

/-- For a chart $H : Q \to U$ of class $C^1$ of $\Omega$, the transport $W^{1,p}(Q) \to W^{1,p}(U)$,
$w \mapsto w \circ H^{-1}$. This is the fourth map of step (b) of the proof of Theorem 9.7 of
[brezis2011functional].

It is `SobolevMultiIndex.compDiffeoL` for the diffeomorphism of
`ContDiffChart.exists_isDiffeoOnWithBoundedJacobian_invFun`. -/
def chartRetransferL : SobolevEuclidean (d + 1) 1 p (unitChartCubeOpens d) →L[ℝ]
    SobolevEuclidean (d + 1) 1 p c.opensU :=
  SobolevMultiIndex.compDiffeoL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p volume
    c.exists_isDiffeoOnWithBoundedJacobian_invFun.choose_spec

/-- The **chart-local extension** of step (b) of the proof of Theorem 9.7 of [brezis2011functional].
For a chart $H : Q \to U$ of class $C^1$ of $\Omega$, it is the bounded linear map
$W^{1,p}(\Omega) \to W^{1,p}(U)$,
$$u \mapsto \left( u|_{U \cap \Omega} \circ H \right)^\star \circ H^{-1},$$
the composite of the restriction to $U \cap \Omega$, the transport to $Q_+$ along $H$, the even
reflection to $Q$, and the transport back to $U$ along $H^{-1}$.

Its function agrees with $u$ on $U \cap \Omega$ (`SobolevEuclidean.chartExtendL_fn_ae_eq`), and
its $L^p(U)$ norm is at most a constant times $\|u\|_{L^p(U \cap \Omega)}$
(`SobolevEuclidean.exists_eLpNorm_fn_chartExtendL_le`). It is the function
$w_i \in W^{1,p}(U_i)$ of the book, with $w_i = u$ on $U_i \cap \Omega$ and
$\|w_i\|_{W^{1,p}(U_i)} \le C \|u\|_{W^{1,p}(U_i \cap \Omega)}$. Here the bound in $W^{1,p}$ is
the boundedness of this linear map on $W^{1,p}(\Omega)$. -/
def chartExtendL : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p c.opensU :=
  chartRetransferL p c ∘L cubeReflectL p ∘L chartTransferL p c ∘L chartRestrictL p c

/-- The chart-local extension of $u$ is the image of $u$ under the four maps of step (b) in turn:
`SobolevEuclidean.chartRestrictL`, `SobolevEuclidean.chartTransferL`,
`SobolevEuclidean.cubeReflectL` and `SobolevEuclidean.chartRetransferL`. -/
theorem chartExtendL_apply (u : SobolevEuclidean (d + 1) 1 p Ω) :
    chartExtendL p c u = chartRetransferL p c (cubeReflectL p (chartTransferL p c
      (chartRestrictL p c u))) :=
  rfl

/-- For $u \in W^{1,p}(\Omega)$, the function of the restriction of $u$ to $U \cap \Omega$ agrees
with the function of $u$ almost everywhere on $U \cap \Omega$. -/
theorem fn_chartRestrictL (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (chartRestrictL p c u) =ᵐ[volume.restrict (c.opensInter : Set _)]
      SobolevMultiIndex.fn u :=
  SobolevMultiIndex.fn_restrictL _ _

/-- For $v \in W^{1,p}(U \cap \Omega)$, the function of the transport of $v$ to $Q_+$ is
$v \circ H$, almost everywhere on $Q_+$. -/
theorem fn_chartTransferL (v : SobolevEuclidean (d + 1) 1 p c.opensInter) :
    SobolevMultiIndex.fn (chartTransferL p c v)
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d) : Set _)]
        fun y ↦ SobolevMultiIndex.fn v (c.toFun y) :=
  SobolevMultiIndex.fn_compDiffeoL _ _

/-- There is a finite constant $C$ such that the transport $v \circ H$ of every
$v \in W^{1,p}(U \cap \Omega)$ (`SobolevEuclidean.chartTransferL`) satisfies
$$\|v \circ H\|_{L^p(Q_+)} \le C \|v\|_{L^p(U \cap \Omega)}.$$
-/
theorem exists_eLpNorm_fn_chartTransferL_le : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ v : SobolevEuclidean (d + 1) 1 p c.opensInter,
      eLpNorm (SobolevMultiIndex.fn (chartTransferL p c v)) p
        (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d) : Set _))
        ≤ C * eLpNorm (SobolevMultiIndex.fn v) p (volume.restrict (c.opensInter : Set _)) :=
  SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le _

/-- For $w \in W^{1,p}(Q_+)$, the even reflection $w^\star$ agrees with $w$ almost everywhere on
$Q_+$. -/
theorem fn_cubeReflectL_restrict
    (w : SobolevEuclidean (d + 1) 1 p
      (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d))) :
    SobolevMultiIndex.fn (cubeReflectL p w)
      =ᵐ[volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d) : Set _)]
        SobolevMultiIndex.fn w :=
  SobolevMultiIndex.fn_evenReflectionL_restrict _ _ _

/-- For $w \in W^{1,p}(Q_+)$, the even reflection $w^\star$ satisfies
$\|w^\star\|_{L^p(Q)} \le 2 \|w\|_{L^p(Q_+)}$. -/
theorem eLpNorm_fn_cubeReflectL_le
    (w : SobolevEuclidean (d + 1) 1 p
      (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d))) :
    eLpNorm (SobolevMultiIndex.fn (cubeReflectL p w)) p
        (volume.restrict (unitChartCubeOpens d : Set _))
      ≤ 2 * eLpNorm (SobolevMultiIndex.fn w) p
        (volume.restrict (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d) : Set _)) :=
  SobolevMultiIndex.eLpNorm_fn_evenReflectionL_le _ _ _

/-- For $w \in W^{1,p}(Q)$, the function of the transport of $w$ to $U$ is $w \circ H^{-1}$, almost
everywhere on $U$. -/
theorem fn_chartRetransferL (w : SobolevEuclidean (d + 1) 1 p (unitChartCubeOpens d)) :
    SobolevMultiIndex.fn (chartRetransferL p c w) =ᵐ[volume.restrict (c.opensU : Set _)]
      fun x ↦ SobolevMultiIndex.fn w (c.invFun x) :=
  SobolevMultiIndex.fn_compDiffeoL _ _

/-- There is a finite constant $C$ such that the transport $w \circ H^{-1}$ of every
$w \in W^{1,p}(Q)$ (`SobolevEuclidean.chartRetransferL`) satisfies
$$\|w \circ H^{-1}\|_{L^p(U)} \le C \|w\|_{L^p(Q)}.$$
-/
theorem exists_eLpNorm_fn_chartRetransferL_le : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ w : SobolevEuclidean (d + 1) 1 p (unitChartCubeOpens d),
      eLpNorm (SobolevMultiIndex.fn (chartRetransferL p c w)) p (volume.restrict (c.opensU : Set _))
        ≤ C * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (unitChartCubeOpens d : Set _)) :=
  SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le _

/-- Let $H : Q \to U$ be a chart of class $C^1$ of $\Omega$, and let $P$ be a property of points of
$\mathbb{R}^{d+1}$ that holds almost everywhere on $Q_+$. Then $P(H^{-1} x)$ holds for almost
every $x \in U \cap \Omega$. -/
theorem ae_comp_chart_invFun {P : EuclideanSpace ℝ (Fin (d + 1)) → Prop}
    (hP : ∀ᵐ y ∂volume.restrict
      (posHalf (single (Fin.last d) (1 : ℝ)) (unitChartCubeOpens d) : Set _), P y) :
    ∀ᵐ x ∂volume.restrict (c.opensInter : Set _), P (c.invFun x) :=
  c.exists_isDiffeoOnWithBoundedJacobian_posHalf.choose_spec.symm.ae_comp_restrict hP

end SobolevEuclidean

end ChartLocal

/-! ### The chart-local extension: identity and bound -/

section ChartLocalSpec

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Let $\Omega, \Omega_c, Q_+, Q, U \subseteq \mathbb{R}^{d+1}$ be open, let $H, H^{-1} :
\mathbb{R}^{d+1} \to \mathbb{R}^{d+1}$ be maps, let $1 \le p \le \infty$, and let
$R : W^{1,p}(\Omega) \to W^{1,p}(\Omega_c)$, $T_1 : W^{1,p}(\Omega_c) \to W^{1,p}(Q_+)$,
$S : W^{1,p}(Q_+) \to W^{1,p}(Q)$ and $T_2 : W^{1,p}(Q) \to W^{1,p}(U)$ be bounded linear maps.
Assume that, almost everywhere on the set named, $Ru = u$ on $\Omega_c$, $T_1 v = v \circ H$ on
$Q_+$, $Sw = w$ on $Q_+$, and $T_2 w = w \circ H^{-1}$ on $U$. Assume also that every property
that holds almost everywhere on $Q_+$ holds at $H^{-1} x$ for almost every $x \in \Omega_c$,
that $\Omega_c \subseteq U$, and that $H(H^{-1} x) = x$ for $x \in \Omega_c$. Then for every
$u \in W^{1,p}(\Omega)$,
$$T_2(S(T_1(Ru))) = u \quad \text{almost everywhere on } \Omega_c.$$

The four maps stand for the restriction, the transport, the reflection and the transport back of
step (b) of the proof of Theorem 9.7 of [brezis2011functional], and $\Omega_c$ stands for
$U \cap \Omega$. The instance is `SobolevEuclidean.chartExtendL_fn_ae_eq`. -/
theorem SobolevEuclidean.chartExtend_fn_of_ops
    {Ω Ωc Qp Q U : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    {H Hinv : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (R : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p Ωc)
    (T₁ : SobolevEuclidean (d + 1) 1 p Ωc →L[ℝ] SobolevEuclidean (d + 1) 1 p Qp)
    (S : SobolevEuclidean (d + 1) 1 p Qp →L[ℝ] SobolevEuclidean (d + 1) 1 p Q)
    (T₂ : SobolevEuclidean (d + 1) 1 p Q →L[ℝ] SobolevEuclidean (d + 1) 1 p U)
    (hRfn : ∀ u, SobolevMultiIndex.fn (R u) =ᵐ[volume.restrict (Ωc : Set _)] SobolevMultiIndex.fn u)
    (hT₁fn : ∀ v, SobolevMultiIndex.fn (T₁ v) =ᵐ[volume.restrict (Qp : Set _)]
      fun y ↦ SobolevMultiIndex.fn v (H y))
    (hSfn : ∀ w, SobolevMultiIndex.fn (S w) =ᵐ[volume.restrict (Qp : Set _)] SobolevMultiIndex.fn w)
    (hT₂fn : ∀ w, SobolevMultiIndex.fn (T₂ w) =ᵐ[volume.restrict (U : Set _)]
      fun x ↦ SobolevMultiIndex.fn w (Hinv x))
    (htrans : ∀ {P : EuclideanSpace ℝ (Fin (d + 1)) → Prop},
      (∀ᵐ y ∂volume.restrict (Qp : Set _), P y) → ∀ᵐ x ∂volume.restrict (Ωc : Set _), P (Hinv x))
    (hΩcU : Ωc ≤ U) (hHinv : ∀ x ∈ (Ωc : Set _), H (Hinv x) = x)
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (T₂ (S (T₁ (R u)))) =ᵐ[volume.restrict (Ωc : Set _)]
      SobolevMultiIndex.fn u := by
  have h1 : ∀ᵐ x ∂volume.restrict (Ωc : Set _), SobolevMultiIndex.fn (T₂ (S (T₁ (R u)))) x
      = SobolevMultiIndex.fn (S (T₁ (R u))) (Hinv x) :=
    ae_restrict_of_ae_restrict_of_subset hΩcU (hT₂fn (S (T₁ (R u))))
  have h2 : ∀ᵐ x ∂volume.restrict (Ωc : Set _), SobolevMultiIndex.fn (S (T₁ (R u))) (Hinv x)
      = SobolevMultiIndex.fn (T₁ (R u)) (Hinv x) := htrans (hSfn (T₁ (R u)))
  have h3 : ∀ᵐ x ∂volume.restrict (Ωc : Set _), SobolevMultiIndex.fn (T₁ (R u)) (Hinv x)
      = SobolevMultiIndex.fn (R u) (H (Hinv x)) := htrans (hT₁fn (R u))
  filter_upwards [h1, h2, h3, hRfn u, ae_restrict_mem Ωc.isOpen.measurableSet]
    with x hx1 hx2 hx3 hx4 hxΩc
  rw [hx1, hx2, hx3, hHinv x hxΩc, hx4]

/-- Let $\Omega, \Omega_c, Q_+, Q, U \subseteq \mathbb{R}^{d+1}$ be open, let $1 \le p \le \infty$,
and let $R : W^{1,p}(\Omega) \to W^{1,p}(\Omega_c)$, $T_1 : W^{1,p}(\Omega_c) \to W^{1,p}(Q_+)$,
$S : W^{1,p}(Q_+) \to W^{1,p}(Q)$ and $T_2 : W^{1,p}(Q) \to W^{1,p}(U)$ be bounded linear maps.
Assume that $Ru = u$ almost everywhere on $\Omega_c$, and that for constants
$C_1, C_2 \in [0, \infty]$
$$\|T_1 v\|_{L^p(Q_+)} \le C_1 \|v\|_{L^p(\Omega_c)}, \quad
  \|S w\|_{L^p(Q)} \le 2 \|w\|_{L^p(Q_+)}, \quad
  \|T_2 w\|_{L^p(U)} \le C_2 \|w\|_{L^p(Q)}.$$
Then $\|T_2(S(T_1(Ru)))\|_{L^p(U)} \le C_2 \cdot 2 C_1 \|u\|_{L^p(\Omega_c)}$ for every
$u \in W^{1,p}(\Omega)$. -/
theorem SobolevEuclidean.eLpNorm_chartExtend_of_ops
    {Ω Ωc Qp Q U : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (R : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p Ωc)
    (T₁ : SobolevEuclidean (d + 1) 1 p Ωc →L[ℝ] SobolevEuclidean (d + 1) 1 p Qp)
    (S : SobolevEuclidean (d + 1) 1 p Qp →L[ℝ] SobolevEuclidean (d + 1) 1 p Q)
    (T₂ : SobolevEuclidean (d + 1) 1 p Q →L[ℝ] SobolevEuclidean (d + 1) 1 p U)
    (hRfn : ∀ u, SobolevMultiIndex.fn (R u) =ᵐ[volume.restrict (Ωc : Set _)] SobolevMultiIndex.fn u)
    {C₁ C₂ : ℝ≥0∞}
    (hT₁Lp : ∀ v, eLpNorm (SobolevMultiIndex.fn (T₁ v)) p (volume.restrict (Qp : Set _))
      ≤ C₁ * eLpNorm (SobolevMultiIndex.fn v) p (volume.restrict (Ωc : Set _)))
    (hSLp : ∀ w, eLpNorm (SobolevMultiIndex.fn (S w)) p (volume.restrict (Q : Set _))
      ≤ 2 * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (Qp : Set _)))
    (hT₂Lp : ∀ w, eLpNorm (SobolevMultiIndex.fn (T₂ w)) p (volume.restrict (U : Set _))
      ≤ C₂ * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (Q : Set _)))
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    eLpNorm (SobolevMultiIndex.fn (T₂ (S (T₁ (R u))))) p (volume.restrict (U : Set _))
      ≤ C₂ * (2 * C₁) * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ωc : Set _)) := by
  calc eLpNorm (SobolevMultiIndex.fn (T₂ (S (T₁ (R u))))) p (volume.restrict (U : Set _))
      ≤ C₂ * eLpNorm (SobolevMultiIndex.fn (S (T₁ (R u)))) p (volume.restrict (Q : Set _)) :=
        hT₂Lp _
    _ ≤ C₂ * (2 * eLpNorm (SobolevMultiIndex.fn (T₁ (R u))) p (volume.restrict (Qp : Set _))) := by
        gcongr; exact hSLp _
    _ ≤ C₂ * (2 * (C₁ * eLpNorm (SobolevMultiIndex.fn (R u)) p
          (volume.restrict (Ωc : Set _)))) := by
        gcongr; exact hT₁Lp _
    _ = C₂ * (2 * C₁) * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ωc : Set _)) := by
        rw [eLpNorm_congr_ae (hRfn u)]; ring

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  (c : ContDiffChart 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- Let $H : Q \to U$ be a chart of class $C^1$ of an open set $\Omega \subseteq \mathbb{R}^{d+1}$,
and let $1 \le p \le \infty$. For every $u \in W^{1,p}(\Omega)$, the chart-local extension $w$
of $u$ (`SobolevEuclidean.chartExtendL`) agrees with $u$ almost everywhere on $U \cap \Omega$.

This is the identity $w_i = u$ on $U_i \cap \Omega$ in step (b) of the proof of Theorem 9.7 of
[brezis2011functional]. -/
theorem SobolevEuclidean.chartExtendL_fn_ae_eq (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (SobolevEuclidean.chartExtendL p c u)
      =ᵐ[volume.restrict (c.opensInter : Set _)] SobolevMultiIndex.fn u := by
  rw [SobolevEuclidean.chartExtendL_apply]
  exact SobolevEuclidean.chartExtend_fn_of_ops (SobolevEuclidean.chartRestrictL p c)
    (SobolevEuclidean.chartTransferL p c) (SobolevEuclidean.cubeReflectL p)
    (SobolevEuclidean.chartRetransferL p c) (SobolevEuclidean.fn_chartRestrictL p c)
    (SobolevEuclidean.fn_chartTransferL p c) (SobolevEuclidean.fn_cubeReflectL_restrict p)
    (SobolevEuclidean.fn_chartRetransferL p c) (fun h ↦ SobolevEuclidean.ae_comp_chart_invFun c h)
    c.opensInter_le_opensU (fun x hx ↦ c.toFun_invFun hx.1) u

/-- Let $H : Q \to U$ be a chart of class $C^1$ of an open set $\Omega \subseteq \mathbb{R}^{d+1}$,
and let $1 \le p \le \infty$. There is a finite constant $C$ such that the chart-local extension
$w$ of every $u \in W^{1,p}(\Omega)$ (`SobolevEuclidean.chartExtendL`) satisfies
$$\|w\|_{L^p(U)} \le C \|u\|_{L^p(U \cap \Omega)}.$$

This is the $L^p$ part of the bound $\|w_i\|_{W^{1,p}(U_i)} \le C \|u\|_{W^{1,p}(U_i \cap
\Omega)}$ in step (b) of the proof of Theorem 9.7 of [brezis2011functional]. -/
theorem SobolevEuclidean.exists_eLpNorm_fn_chartExtendL_le : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
      eLpNorm (SobolevMultiIndex.fn (SobolevEuclidean.chartExtendL p c u)) p
        (volume.restrict (c.opensU : Set _))
        ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (c.opensInter : Set _)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := SobolevEuclidean.exists_eLpNorm_fn_chartTransferL_le p c
  obtain ⟨C₂, hC₂, h₂⟩ := SobolevEuclidean.exists_eLpNorm_fn_chartRetransferL_le p c
  refine ⟨C₂ * (2 * C₁), ENNReal.mul_ne_top hC₂ (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hC₁),
    fun u ↦ ?_⟩
  rw [SobolevEuclidean.chartExtendL_apply]
  exact SobolevEuclidean.eLpNorm_chartExtend_of_ops (SobolevEuclidean.chartRestrictL p c)
    (SobolevEuclidean.chartTransferL p c) (SobolevEuclidean.cubeReflectL p)
    (SobolevEuclidean.chartRetransferL p c) (SobolevEuclidean.fn_chartRestrictL p c) h₁
    (SobolevEuclidean.eLpNorm_fn_cubeReflectL_le p) h₂ u

end ChartLocalSpec

/-! ### The assembly over an atlas -/

section Assembly

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞}
  {Ω : Opens E} {μ : Measure E}

/-- Let $\Omega$ be an open subset of a real normed space $E$ with a measure $\mu$. The function of
a finite sum $\sum_{i \in s} w_i$ of elements of $W^{k,p}(\Omega)$ is, $\mu$-almost everywhere
on $\Omega$, the sum of the functions of the $w_i$. -/
theorem SobolevMultiIndex.fn_finset_sum {κ : Type*} (s : Finset κ)
    (w : κ → SobolevMultiIndex F b k p Ω μ) :
    SobolevMultiIndex.fn (∑ i ∈ s, w i) =ᵐ[μ.restrict (Ω : Set E)]
      ∑ i ∈ s, SobolevMultiIndex.fn (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using SobolevMultiIndex.fn_zero (F := F) (b := b) (k := k) (p := p) (Ω := Ω) (μ := μ)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (SobolevMultiIndex.fn_add _ _).trans ((EventuallyEq.refl _ _).add ih)

end Assembly


section Atlas

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {k : ℕ} {U Ωc : Fin k → Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  {E₀ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤}
  {E : ∀ i, SobolevEuclidean (d + 1) 1 p (U i) →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤}
  {C : ∀ i, SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p (U i)}
  {P : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤}

/-- Let $\Omega$ and $U_i$, $i < k$, be open subsets of $\mathbb{R}^{d+1}$, and let $E_0 :
W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^{d+1})$, $E_i : W^{1,p}(U_i) \to
W^{1,p}(\mathbb{R}^{d+1})$, $C_i : W^{1,p}(\Omega) \to W^{1,p}(U_i)$ and $P : W^{1,p}(\Omega)
\to W^{1,p}(\mathbb{R}^{d+1})$ be bounded linear maps with $Pu = E_0 u + \sum_i E_i(C_i u)$ for
all $u$. Then the function of $Pu$ is, almost everywhere on $\mathbb{R}^{d+1}$, the function of
$E_0 u$ plus the sum of the functions of the $E_i(C_i u)$. -/
theorem SobolevEuclidean.fn_extension_of_ops (hP : ∀ u, P u = E₀ u + ∑ i, E i (C i u))
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    SobolevMultiIndex.fn (P u) =ᵐ[volume]
      SobolevMultiIndex.fn (E₀ u) + ∑ i, SobolevMultiIndex.fn (E i (C i u)) := by
  rw [hP u]
  exact eventuallyEq_restrict_coe_top_iff.1 ((SobolevMultiIndex.fn_add _ _).trans
    ((EventuallyEq.refl _ _).add (SobolevMultiIndex.fn_finset_sum _ _)))

/-- Step (c) of the proof of Theorem 9.7 of [brezis2011functional], the identity $Pu = u$ on
$\Omega$, with the operators as variables. Let $\Omega$, $U_i$ and $\Omega_i$, $i < k$, be open
subsets of $\mathbb{R}^{d+1}$ with $\Omega_i = U_i \cap \Omega$, and let $E_0$, $E_i$, $C_i$ and
$P$ be bounded linear maps as in `SobolevEuclidean.fn_extension_of_ops`, with
$Pu = E_0 u + \sum_i E_i(C_i u)$ for all $u$. Let $\alpha_0, \alpha_i, \chi : \mathbb{R}^{d+1}
\to \mathbb{R}$ satisfy $\alpha_0 + \sum_i \alpha_i = \chi$ on $\Omega$, and $\alpha_i = 0$
outside $U_i$. Assume that, almost everywhere, $E_0 u = \mathbf{1}_\Omega \alpha_0 u$ and
$E_i w = \mathbf{1}_{U_i} \alpha_i w$ on $\mathbb{R}^{d+1}$, and $C_i u = u$ on $\Omega_i$. If
$u \in W^{1,p}(\Omega)$ satisfies $u = \chi u$ almost everywhere on $\Omega$, then $Pu = u$
almost everywhere on $\Omega$.

In the proof of the book, $E_0$ is the zero extension of $\alpha_0 u$, $C_i$ is the chart-local
extension to $U_i$, and $E_i$ is the zero extension of $\alpha_i w$ from $U_i$. -/
theorem SobolevEuclidean.fn_extension_ae_eq_of_ops
    (hΩc : ∀ i, (Ωc i : Set (EuclideanSpace ℝ (Fin (d + 1))))
      = (U i : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {α₀ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {α : Fin k → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {χ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hsum : ∀ x ∈ (Ω : Set _), α₀ x + ∑ i, α i x = χ x)
    (hα : ∀ i x, x ∉ (U i : Set _) → α i x = 0)
    (hE₀fn : ∀ u, SobolevMultiIndex.fn (E₀ u) =ᵐ[volume]
      (Ω : Set _).indicator fun x ↦ α₀ x • SobolevMultiIndex.fn u x)
    (hEfn : ∀ i w, SobolevMultiIndex.fn (E i w) =ᵐ[volume]
      (U i : Set _).indicator fun x ↦ α i x • SobolevMultiIndex.fn w x)
    (hCfn : ∀ i u, SobolevMultiIndex.fn (C i u) =ᵐ[volume.restrict (Ωc i : Set _)]
      SobolevMultiIndex.fn u)
    (hP : ∀ u, P u = E₀ u + ∑ i, E i (C i u)) (u : SobolevEuclidean (d + 1) 1 p Ω)
    (hu : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set _)]
      fun x ↦ χ x * SobolevMultiIndex.fn u x) :
    SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u := by
  have hΩmeas : MeasurableSet (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := Ω.isOpen.measurableSet
  have h1 : ∀ᵐ x ∂volume, x ∈ (Ω : Set _) →
      SobolevMultiIndex.fn (E₀ u) x = α₀ x • SobolevMultiIndex.fn u x := by
    filter_upwards [hE₀fn u] with x hx hxΩ
    rw [hx, Set.indicator_of_mem hxΩ]
  have h2 : ∀ᵐ x ∂volume, ∀ i, x ∈ (Ω : Set _) →
      SobolevMultiIndex.fn (E i (C i u)) x = α i x • SobolevMultiIndex.fn u x := by
    rw [ae_all_iff]
    intro i
    filter_upwards [hEfn i (C i u), (ae_restrict_iff' (Ωc i).isOpen.measurableSet).1 (hCfn i u)]
      with x hx hx' hxΩ
    rw [hx]
    by_cases hxU : x ∈ (U i : Set _)
    · rw [Set.indicator_of_mem hxU, hx' (by rw [hΩc i]; exact ⟨hxU, hxΩ⟩)]
    · rw [Set.indicator_of_notMem hxU, hα i x hxU, zero_smul]
  filter_upwards [ae_restrict_of_ae (SobolevEuclidean.fn_extension_of_ops hP u),
    ae_restrict_of_ae h1, ae_restrict_of_ae h2, ae_restrict_mem hΩmeas, hu]
    with x hx hx1 hx2 hxΩ hxu
  rw [hx, Pi.add_apply, Finset.sum_apply, hx1 hxΩ]
  simp_rw [hx2 _ hxΩ]
  rw [← Finset.sum_smul, ← add_smul, hsum x hxΩ, smul_eq_mul, ← hxu]

/-- Step (c) of the proof of Theorem 9.7 of [brezis2011functional], the $L^p$ bound, with the
operators as variables. Let $\Omega$, $U_i$ and $\Omega_i$, $i < k$, be open subsets of
$\mathbb{R}^{d+1}$ with $\Omega_i = U_i \cap \Omega$, and let $E_0$, $E_i$, $C_i$ and $P$ be
bounded linear maps as in `SobolevEuclidean.fn_extension_of_ops`, with
$Pu = E_0 u + \sum_i E_i(C_i u)$ for all $u$. Assume that for constants
$A_0, A_i, B_i \in [0, \infty]$
$$\|E_0 u\|_{L^p(\mathbb{R}^{d+1})} \le A_0 \|u\|_{L^p(\Omega)}, \quad
  \|E_i w\|_{L^p(\mathbb{R}^{d+1})} \le A_i \|w\|_{L^p(U_i)}, \quad
  \|C_i u\|_{L^p(U_i)} \le B_i \|u\|_{L^p(\Omega_i)}.$$
Then for every $u \in W^{1,p}(\Omega)$
$$\|Pu\|_{L^p(\mathbb{R}^{d+1})} \le \Big( A_0 + \sum_i A_i B_i \Big) \|u\|_{L^p(\Omega)}.$$
-/
theorem SobolevEuclidean.eLpNorm_fn_extension_le_of_ops
    (hΩc : ∀ i, (Ωc i : Set (EuclideanSpace ℝ (Fin (d + 1))))
      = (U i : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    {A₀ : ℝ≥0∞} {A B : Fin k → ℝ≥0∞}
    (hE₀Lp : ∀ u, eLpNorm (SobolevMultiIndex.fn (E₀ u)) p volume
      ≤ A₀ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)))
    (hELp : ∀ i w, eLpNorm (SobolevMultiIndex.fn (E i w)) p volume
      ≤ A i * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (U i : Set _)))
    (hCLp : ∀ i u, eLpNorm (SobolevMultiIndex.fn (C i u)) p (volume.restrict (U i : Set _))
      ≤ B i * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ωc i : Set _)))
    (hP : ∀ u, P u = E₀ u + ∑ i, E i (C i u)) (u : SobolevEuclidean (d + 1) 1 p Ω) :
    eLpNorm (SobolevMultiIndex.fn (P u)) p volume
      ≤ (A₀ + ∑ i, A i * B i)
        * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)) := by
  have hΩcΩ : ∀ i, (Ωc i : Set (EuclideanSpace ℝ (Fin (d + 1))))
      ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) := fun i ↦ by
    rw [hΩc i]; exact inter_subset_right
  rw [eLpNorm_congr_ae (SobolevEuclidean.fn_extension_of_ops hP u), add_mul, Finset.sum_mul]
  refine (eLpNorm_add_le Fact.out).trans (add_le_add (hE₀Lp u) ?_)
  refine (eLpNorm_sum_le Fact.out).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  refine (hELp i (C i u)).trans ?_
  rw [mul_assoc]
  gcongr
  refine (hCLp i u).trans ?_
  gcongr
  exact hΩcΩ i

/-- The assembly $Pu = \bar u_0 + \sum_i \hat u_i$ of step (c) of the proof of Theorem 9.7 of
[brezis2011functional], with the operators as variables. Let $\Omega$, $U_i$ and $\Omega_i$,
$i < k$, be open subsets of $\mathbb{R}^{d+1}$ with $\Omega_i = U_i \cap \Omega$, let
$1 \le p \le \infty$, and let $E_0 : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^{d+1})$, $E_i :
W^{1,p}(U_i) \to W^{1,p}(\mathbb{R}^{d+1})$ and $C_i : W^{1,p}(\Omega) \to W^{1,p}(U_i)$ be
bounded linear maps. Let $\alpha_0, \alpha_i, \chi : \mathbb{R}^{d+1} \to \mathbb{R}$ satisfy
$\alpha_0 + \sum_i \alpha_i = \chi$ on $\Omega$ and $\alpha_i = 0$ outside $U_i$. Assume that,
almost everywhere, $E_0 u = \mathbf{1}_\Omega \alpha_0 u$ and
$E_i w = \mathbf{1}_{U_i} \alpha_i w$ on $\mathbb{R}^{d+1}$, and $C_i u = u$ on $\Omega_i$.
Assume also that for finite constants $A_0, A_i, B_i \in [0, \infty)$
$$\|E_0 u\|_{L^p(\mathbb{R}^{d+1})} \le A_0 \|u\|_{L^p(\Omega)}, \quad
  \|E_i w\|_{L^p(\mathbb{R}^{d+1})} \le A_i \|w\|_{L^p(U_i)}, \quad
  \|C_i u\|_{L^p(U_i)} \le B_i \|u\|_{L^p(\Omega_i)}.$$
Then there are a bounded linear map $P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^{d+1})$ and a
constant $K \in \mathbb{R}$ such that every $u \in W^{1,p}(\Omega)$ with $u = \chi u$ almost
everywhere on $\Omega$ satisfies $Pu = u$ almost everywhere on $\Omega$ and
$$\|Pu\|_{L^p(\mathbb{R}^{d+1})} \le K \|u\|_{L^p(\Omega)}, \qquad
  \|Pu\|_{W^{1,p}(\mathbb{R}^{d+1})} \le K \|u\|_{W^{1,p}(\Omega)}.$$

The operator is $Pu = E_0 u + \sum_i E_i(C_i u)$. The identity comes from
`SobolevEuclidean.fn_extension_ae_eq_of_ops` and the $L^p$ bound from
`SobolevEuclidean.eLpNorm_fn_extension_le_of_ops`. -/
theorem SobolevEuclidean.exists_extensionL_of_ops
    (hΩc : ∀ i, (Ωc i : Set (EuclideanSpace ℝ (Fin (d + 1))))
      = (U i : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (E₀ : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤)
    (E : ∀ i, SobolevEuclidean (d + 1) 1 p (U i) →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤)
    (C : ∀ i, SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p (U i))
    {α₀ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {α : Fin k → EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {χ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hsum : ∀ x ∈ (Ω : Set _), α₀ x + ∑ i, α i x = χ x)
    (hα : ∀ i x, x ∉ (U i : Set _) → α i x = 0)
    (hE₀fn : ∀ u, SobolevMultiIndex.fn (E₀ u) =ᵐ[volume]
      (Ω : Set _).indicator fun x ↦ α₀ x • SobolevMultiIndex.fn u x)
    (hEfn : ∀ i w, SobolevMultiIndex.fn (E i w) =ᵐ[volume]
      (U i : Set _).indicator fun x ↦ α i x • SobolevMultiIndex.fn w x)
    (hCfn : ∀ i u, SobolevMultiIndex.fn (C i u) =ᵐ[volume.restrict (Ωc i : Set _)]
      SobolevMultiIndex.fn u)
    {A₀ : ℝ≥0∞} {A B : Fin k → ℝ≥0∞} (hA₀ : A₀ ≠ ⊤) (hA : ∀ i, A i ≠ ⊤) (hB : ∀ i, B i ≠ ⊤)
    (hE₀Lp : ∀ u, eLpNorm (SobolevMultiIndex.fn (E₀ u)) p volume
      ≤ A₀ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)))
    (hELp : ∀ i w, eLpNorm (SobolevMultiIndex.fn (E i w)) p volume
      ≤ A i * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (U i : Set _)))
    (hCLp : ∀ i u, eLpNorm (SobolevMultiIndex.fn (C i u)) p (volume.restrict (U i : Set _))
      ≤ B i * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ωc i : Set _))) :
    ∃ (P : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤) (K : ℝ),
      ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set _)]
          (fun x ↦ χ x * SobolevMultiIndex.fn u x) →
        SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal K * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)) ∧
        ‖P u‖ ≤ K * ‖u‖ := by
  obtain ⟨P, hP⟩ : ∃ P : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤,
      ∀ u, P u = E₀ u + ∑ i, E i (C i u) :=
    ⟨E₀ + ∑ i, (E i).comp (C i), fun u ↦ by
      simp only [add_apply, sum_apply, ContinuousLinearMap.comp_apply]⟩
  have hK₀ : A₀ + ∑ i, A i * B i ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hA₀, ENNReal.sum_ne_top.2 fun i _ ↦ ENNReal.mul_ne_top (hA i) (hB i)⟩
  refine ⟨P, max (A₀ + ∑ i, A i * B i).toReal ‖P‖, fun u hu ↦
    ⟨SobolevEuclidean.fn_extension_ae_eq_of_ops hΩc hsum hα hE₀fn hEfn hCfn hP u hu, ?_, ?_⟩⟩
  · refine (SobolevEuclidean.eLpNorm_fn_extension_le_of_ops hΩc hE₀Lp hELp hCLp hP u).trans ?_
    gcongr
    calc A₀ + ∑ i, A i * B i = ENNReal.ofReal (A₀ + ∑ i, A i * B i).toReal :=
          (ENNReal.ofReal_toReal hK₀).symm
      _ ≤ ENNReal.ofReal (max (A₀ + ∑ i, A i * B i).toReal ‖P‖) :=
          ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end Atlas

/-! ### Theorem 9.7 -/

section Theorem97

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let $E$ be a real normed space, and let $\theta_0, \theta_i : E \to \mathbb{R}$, for $i$ in a
finite index set, satisfy $\theta_0 + \sum_i \theta_i = 1$ everywhere, with every $\theta_i$
smooth. Then $D\theta_0(x) = -\sum_i D\theta_i(x)$ for every $x \in E$. -/
theorem fderiv_eq_neg_sum_of_add_sum_eq_one {ι : Type*} [Fintype ι] {θ₀ : E → ℝ}
    {θ : ι → E → ℝ} (hθ : ∀ i, ContDiff ℝ ∞ (θ i)) (hsum : ∀ x, θ₀ x + ∑ i, θ i x = 1) (x : E) :
    fderiv ℝ θ₀ x = -∑ i, fderiv ℝ (θ i) x := by
  have hθ₀ : θ₀ = fun x ↦ 1 - ∑ i, θ i x := funext fun x ↦ eq_sub_of_add_eq (hsum x)
  have : HasFDerivAt θ₀ (0 - ∑ i, fderiv ℝ (θ i) x) x := by
    rw [hθ₀]
    exact (hasFDerivAt_const (1 : ℝ) x).sub
      (HasFDerivAt.fun_sum fun i _ ↦ ((hθ i).differentiable (by simp) x).hasFDerivAt)
  rw [this.fderiv, zero_sub]

/-- Let $\Omega$ be an open subset of a real normed space $E$ and let $K \subseteq E$. Let
$\theta_0, \theta_i : E \to \mathbb{R}$, for $i$ in a finite index set, be smooth, with
$|\theta_0| \le 1$, $\theta_0 + \sum_i \theta_i = 1$, every $\theta_i$ compactly supported, and
$\operatorname{supp} \theta_0$ disjoint from $K$. Let $\chi : E \to \mathbb{R}$ be smooth, with
$|\chi| \le M$ and $\|D\chi\| \le M$ for some $M$, and with $\operatorname{supp} \chi \cap
\partial\Omega \subseteq K$. Then $\theta_0 \chi$ is a Sobolev cut-off for $\Omega$
(`IsSobolevCutoff`).

Here $\theta_0$ is the function of the partition of unity of Lemma 9.3 of [brezis2011functional]
on a compact set $K \subseteq \partial\Omega$, and $\operatorname{supp}$ is the closed support
`tsupport`. The product is bounded since $|\theta_0| \le 1$, its derivative is bounded since
$D\theta_0 = -\sum_i D\theta_i$ has compact support, and its support misses $\partial\Omega$
since $\operatorname{supp}(\theta_0 \chi) \cap \partial\Omega \subseteq \operatorname{supp}
\theta_0 \cap K = \emptyset$. -/
theorem IsSobolevCutoff.mul_of_partition {ι : Type*} [Fintype ι] {Ω : Opens E} {K : Set E}
    {θ₀ : E → ℝ} {θ : ι → E → ℝ} {χ : E → ℝ} (hθ₀ : ContDiff ℝ ∞ θ₀)
    (hθ : ∀ i, ContDiff ℝ ∞ (θ i)) (hθ₀1 : ∀ x, |θ₀ x| ≤ 1)
    (hsum : ∀ x, θ₀ x + ∑ i, θ i x = 1) (hθc : ∀ i, HasCompactSupport (θ i))
    (hθ₀K : Disjoint (tsupport θ₀) K) (hχ : ContDiff ℝ ∞ χ)
    (hχb : ∃ M, ∀ x, |χ x| ≤ M ∧ ‖fderiv ℝ χ x‖ ≤ M)
    (hχK : tsupport χ ∩ frontier (Ω : Set E) ⊆ K) :
    IsSobolevCutoff Ω fun x ↦ θ₀ x * χ x where
  contDiff := hθ₀.mul hχ
  exists_bound := by
    obtain ⟨Mχ, hMχ⟩ := hχb
    choose Mθ hMθ using fun i ↦
      ((hθc i).fderiv ℝ).exists_bound_of_continuous ((hθ i).continuous_fderiv (by simp))
    have hMχ0 : 0 ≤ Mχ := (abs_nonneg _).trans (hMχ 0).1
    have hMθ0 : 0 ≤ ∑ i, Mθ i := Finset.sum_nonneg fun i _ ↦ (norm_nonneg _).trans (hMθ i 0)
    refine ⟨Mχ + Mχ * ∑ i, Mθ i, fun x ↦ ⟨?_, ?_⟩⟩
    · calc |θ₀ x * χ x| = |θ₀ x| * |χ x| := abs_mul _ _
        _ ≤ 1 * Mχ := mul_le_mul (hθ₀1 x) (hMχ x).1 (abs_nonneg _) zero_le_one
        _ ≤ Mχ + Mχ * ∑ i, Mθ i := by nlinarith [mul_nonneg hMχ0 hMθ0]
    · rw [fderiv_fun_mul (hθ₀.differentiable (by simp) x) (hχ.differentiable (by simp) x),
        fderiv_eq_neg_sum_of_add_sum_eq_one hθ hsum x]
      calc ‖θ₀ x • fderiv ℝ χ x + χ x • -∑ i, fderiv ℝ (θ i) x‖
          ≤ ‖θ₀ x • fderiv ℝ χ x‖ + ‖χ x • -∑ i, fderiv ℝ (θ i) x‖ := norm_add_le _ _
        _ ≤ 1 * Mχ + Mχ * ∑ i, Mθ i := by
          gcongr
          · rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul (hθ₀1 x) (hMχ x).2 (norm_nonneg _) zero_le_one
          · rw [norm_smul, Real.norm_eq_abs, norm_neg]
            exact mul_le_mul (hMχ x).1
              ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ hMθ i x)) (norm_nonneg _) hMχ0
        _ = Mχ + Mχ * ∑ i, Mθ i := by ring
  disjoint_frontier := Set.disjoint_left.2 fun x hx hxf ↦
    hθ₀K.notMem_of_mem_left (tsupport_mul_subset_left hx)
      (hχK ⟨tsupport_mul_subset_right hx, hxf⟩)

/-- Let $\Omega$ be an open subset of a real normed space $E$, let $\theta : E \to \mathbb{R}$ be
smooth with compact support contained in $\Omega$, and let $\chi : E \to \mathbb{R}$ be smooth.
Then $\theta \chi$ is a Sobolev cut-off for $\Omega$ (`IsSobolevCutoff`).

These are the functions $\theta_i \chi$ of the proof of Theorem 9.7 of [brezis2011functional]. -/
theorem IsSobolevCutoff.mul_of_hasCompactSupport {Ω : Opens E} {θ χ : E → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ) (hθΩ : tsupport θ ⊆ Ω)
    (hχ : ContDiff ℝ ∞ χ) : IsSobolevCutoff Ω fun x ↦ θ x * χ x :=
  IsSobolevCutoff.of_hasCompactSupport (hθ.mul hχ) hθc.mul_right
    (tsupport_mul_subset_left.trans hθΩ)

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- The assembly of Theorem 9.7 of [brezis2011functional] over an explicit atlas. Let
$\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be open, let $1 \le p \le \infty$, and let
$K \subseteq \mathbb{R}^N$ be compact. Let $H_i : Q \to U_i$, $i < k$, be charts of class $C^1$
of $\Omega$ with $K \subseteq \bigcup_i U_i$. Let $\chi : \mathbb{R}^N \to \mathbb{R}$ be
smooth, with $|\chi| \le M$ and $\|D\chi\| \le M$ for some $M$, and with $\operatorname{supp}
\chi \cap \partial\Omega \subseteq K$. Then there are a bounded linear map
$P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ and a constant $C$ such that every
$u \in W^{1,p}(\Omega)$ with $u = \chi u$ almost everywhere on $\Omega$ satisfies $Pu = u$
almost everywhere on $\Omega$ and
$$\|Pu\|_{L^p(\mathbb{R}^N)} \le C \|u\|_{L^p(\Omega)}, \qquad
  \|Pu\|_{W^{1,p}(\mathbb{R}^N)} \le C \|u\|_{W^{1,p}(\Omega)}.$$

The operator is $Pu = \theta_0 \chi u + \sum_i \theta_i \chi w_i$, each term extended by zero.
Here $\theta_0, \theta_i$ is the partition of unity of Lemma 9.3 on $K$ subordinate to the $U_i$
(`IsCompact.exists_contDiff_partitionOfUnity`), the zero extensions are
`SobolevMultiIndex.extendZeroMulL` with the cut-offs $\theta_0 \chi$ for $\Omega$ and
$\theta_i \chi$ for $U_i$, and $w_i$ is the chart-local extension
`SobolevEuclidean.chartExtendL` of $u$ for the chart $H_i$. Theorem 9.7 is the case
$K = \partial\Omega$ and $\chi = 1$ (`SobolevEuclidean.exists_extensionL`). Corollary 9.8 for an
unbounded boundary uses $K = \partial\Omega \cap \bar B(0, 4R)$ and a cut-off $\chi$ equal to
$1$ on $\bar B(0, 2R)$ (`SobolevEuclidean.exists_contDiff_hasCompactSupport_norm_sub_lt`). -/
theorem SobolevEuclidean.exists_extensionL_of_atlas {K : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hK : IsCompact K) {k : ℕ}
    (c : Fin k → ContDiffChart 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hc : K ⊆ ⋃ i, (c i).U) {χ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχb : ∃ M, ∀ x, |χ x| ≤ M ∧ ‖fderiv ℝ χ x‖ ≤ M)
    (hχK : tsupport χ ∩ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ K) :
    ∃ (P : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
        SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set _)]
          (fun x ↦ χ x * SobolevMultiIndex.fn u x) →
        SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)) ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨θ₀, θ, hθ₀, hθ, hθ₀01, -, hsum, hθc, hθU, hθ₀K⟩ :=
    hK.exists_contDiff_partitionOfUnity (fun i ↦ (c i).isOpen_U) hc
  have hα₀ : IsSobolevCutoff Ω fun x ↦ θ₀ x * χ x :=
    IsSobolevCutoff.mul_of_partition hθ₀ hθ
      (fun x ↦ abs_le.2 ⟨by linarith [(hθ₀01 x).1], (hθ₀01 x).2⟩) hsum hθc hθ₀K hχ hχb hχK
  have hα : ∀ i, IsSobolevCutoff (c i).opensU fun x ↦ θ i x * χ x := fun i ↦
    IsSobolevCutoff.mul_of_hasCompactSupport (hθ i) (hθc i) (hθU i) hχ
  obtain ⟨M₀, -, hM₀⟩ := hα₀.exists_nonneg_bound
  choose M hM0 hM using fun i ↦ (hα i).exists_nonneg_bound
  choose B hB hBu using fun i ↦ SobolevEuclidean.exists_eLpNorm_fn_chartExtendL_le (p := p) (c i)
  refine SobolevEuclidean.exists_extensionL_of_ops (U := fun i ↦ (c i).opensU)
    (Ωc := fun i ↦ (c i).opensInter) (fun i ↦ rfl)
    (SobolevMultiIndex.extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis p
      volume hα₀)
    (fun i ↦ SobolevMultiIndex.extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      p volume (hα i))
    (fun i ↦ SobolevEuclidean.chartExtendL p (c i)) (fun x _ ↦ ?_) (fun i x hx ↦ ?_)
    (fun u ↦ SobolevMultiIndex.fn_extendZeroMulL hα₀ u)
    (fun i w ↦ SobolevMultiIndex.fn_extendZeroMulL (hα i) w)
    (fun i u ↦ SobolevEuclidean.chartExtendL_fn_ae_eq (c i) u)
    (A₀ := ENNReal.ofReal M₀) (A := fun i ↦ ENNReal.ofReal (M i)) ENNReal.ofReal_ne_top
    (fun i ↦ ENNReal.ofReal_ne_top) hB
    (fun u ↦ SobolevMultiIndex.eLpNorm_fn_extendZeroMulL_le hα₀ (fun x ↦ (hM₀ x).1) u)
    (fun i w ↦ SobolevMultiIndex.eLpNorm_fn_extendZeroMulL_le (hα i) (fun x ↦ (hM i x).1) w) hBu
  · rw [← Finset.sum_mul, ← add_mul, hsum x, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hθU i h), zero_mul]

/-- The **extension theorem**. Let $\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be an open set of
class $C^1$ (`IsContDiffChartDomain 1`) whose boundary $\partial\Omega$ is bounded, and let
$1 \le p \le \infty$. Then there are a bounded linear map
$P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ and a constant $C$, which depends only on
$\Omega$ and $p$, such that every $u \in W^{1,p}(\Omega)$ satisfies $Pu = u$ almost everywhere
on $\Omega$ and
$$\|Pu\|_{L^p(\mathbb{R}^N)} \le C \|u\|_{L^p(\Omega)}, \qquad
  \|Pu\|_{W^{1,p}(\mathbb{R}^N)} \le C \|u\|_{W^{1,p}(\Omega)}.$$
This is Theorem 9.7 of [brezis2011functional].

The proof is `SobolevEuclidean.exists_extensionL_of_atlas` for $K = \partial\Omega$, which is
compact because it is closed and bounded, for the finite atlas of
`IsContDiffChartDomain.exists_finite_atlas`, and for $\chi = 1$. -/
theorem SobolevEuclidean.exists_extensionL
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ (P : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) 1 p Ω,
        SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)) ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨k, c, hc⟩ := hΩ.exists_finite_atlas hΓ
  obtain ⟨P, C, hP⟩ := SobolevEuclidean.exists_extensionL_of_atlas (p := p)
    (Metric.isCompact_of_isClosed_isBounded isClosed_frontier hΓ) c hc
    (contDiff_const (c := (1 : ℝ))) ⟨1, fun x ↦ by simp⟩ inter_subset_right
  exact ⟨P, C, fun u ↦ hP u (Eventually.of_forall fun x ↦ (one_mul _).symm)⟩

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^1$ (`IsContDiffChartDomain 1`)
whose boundary is bounded. Then $\Omega$ is a $W^{1,p}$-extension domain
(`IsSobolevExtensionDomain`) for every $1 \le p \le \infty$.

This is Theorem 9.7 of [brezis2011functional] in the form of the abstract hypothesis of
`Numlib.Analysis.Sobolev.Cutoff`. -/
theorem IsSobolevExtensionDomain.of_isContDiffChartDomain
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    IsSobolevExtensionDomain (d + 1) p Ω := by
  obtain ⟨P, C, hP⟩ := SobolevEuclidean.exists_extensionL (p := p) hΩ hΓ
  exact ⟨P.comp (Submodule.subtypeL _), fun u ↦ (hP u).1⟩

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an open set whose boundary is locally the graph of a
$C^1$ function (`IsContDiffDomain 1`, the graph definition of [han2009theoretical]), and let the
boundary be bounded. Then $\Omega$ is a $W^{1,p}$-extension domain (`IsSobolevExtensionDomain`)
for every $1 \le p \le \infty$.

This is Theorem 9.7 of [brezis2011functional]. The proof passes from graphs to charts by
`IsContDiffDomain.isContDiffChartDomain`. -/
theorem IsSobolevExtensionDomain.of_isContDiffDomain
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    IsSobolevExtensionDomain (d + 1) p Ω :=
  IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ.isContDiffChartDomain hΓ

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^1$ (`IsContDiffChartDomain 1`)
whose boundary is bounded, and let $1 \le p < \infty$. For every $u \in W^{1,p}(\Omega)$ there
are functions $v_n \in C_c^\infty(\mathbb{R}^N)$ and $w_n \in W^{1,p}(\Omega)$ with $w_n = v_n$
almost everywhere on $\Omega$ and $w_n \to u$ in $W^{1,p}(\Omega)$. Thus the restrictions to
$\Omega$ of the functions of $C_c^\infty(\mathbb{R}^N)$ are dense in $W^{1,p}(\Omega)$. This is
Corollary 9.8 of [brezis2011functional] for a bounded boundary, the first paragraph of its
proof.

The proof applies the abstract density result
`SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn` to the
extension operator of Theorem 9.7. -/
theorem SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_isBounded_frontier
    (hp' : p ≠ ⊤) (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧
      (∀ n, HasCompactSupport (v n)) ∧ ∃ w : ℕ → SobolevEuclidean (d + 1) 1 p Ω,
        (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume.restrict (Ω : Set _)] v n) ∧
        Tendsto w atTop (𝓝 u) :=
  SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn hp'
    (IsSobolevExtensionDomain.of_isContDiffChartDomain hΩ hΓ) ⟨u, Submodule.mem_top⟩

end Theorem97

/-! ### Corollary 9.8 on a general open set of class $C^1$ -/

section Corollary98

/-- Let $E$ be a real normed space, $c > 0$, $x \in E$ and $r \in \mathbb{R}$. Then
$\|c^{-1} x\| \le r$ if and only if $\|x\| \le c r$. -/
theorem norm_inv_smul_le_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    (hc : 0 < c) (x : E) (r : ℝ) : ‖c⁻¹ • x‖ ≤ r ↔ ‖x‖ ≤ c * r := by
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hc, inv_mul_le_iff₀ hc]

/-- Let $E$ be a real normed space, $c > 0$, $x \in E$ and $r \in \mathbb{R}$. Then
$\|c^{-1} x\| < r$ if and only if $\|x\| < c r$. -/
theorem norm_inv_smul_lt_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    (hc : 0 < c) (x : E) (r : ℝ) : ‖c⁻¹ • x‖ < r ↔ ‖x‖ < c * r := by
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hc, inv_mul_lt_iff₀ hc]

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^1$ (`IsContDiffChartDomain 1`),
with no condition on its boundary, let $1 \le p < \infty$, let $u \in W^{1,p}(\Omega)$ and let
$\varepsilon > 0$. Then there are $v \in C_c^\infty(\mathbb{R}^N)$ and $w \in W^{1,p}(\Omega)$
with $w = v$ almost everywhere on $\Omega$ and $\|w - u\|_{W^{1,p}(\Omega)} < \varepsilon$. This
is Corollary 9.8 of [brezis2011functional] for one $\varepsilon$.

The proof is the second paragraph of the proof of Corollary 9.8. For $R$ large, a smooth cut-off
$\zeta_R$ gives $\|\zeta_R u - u\| < \varepsilon / 2$ (`SobolevMultiIndex.tendsto_cutoff_smul`),
and $\zeta_R u$ vanishes outside $B(0, 2R)$. The extension operator of
`SobolevEuclidean.exists_extensionL_of_atlas` for the compact set
$K = \partial\Omega \cap \bar B(0, 4R)$, a finite atlas that covers it, and a cut-off $\chi$
equal to $1$ on $\bar B(0, 2R)$ with support in $\bar B(0, 4R)$, extends the multiples of
$\zeta_R u$. The abstract density result
`SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn` on the
line $\mathbb{R} \zeta_R u$ then gives $v$ and $w$ with $\|w - \zeta_R u\| < \varepsilon / 2$. -/
theorem SobolevEuclidean.exists_contDiff_hasCompactSupport_norm_sub_lt (hp' : p ≠ ⊤)
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (u : SobolevEuclidean (d + 1) 1 p Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) (w : SobolevEuclidean (d + 1) 1 p Ω),
      ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
        SobolevMultiIndex.fn w =ᵐ[volume.restrict (Ω : Set _)] v ∧ ‖w - u‖ < ε := by
  obtain ⟨ζ, hζ, hζ1, hζs, hζ01⟩ :=
    exists_contDiff_eqOn_one_closedBall_one (EuclideanSpace ℝ (Fin (d + 1)))
  obtain ⟨V, hV, -, hVt⟩ := SobolevMultiIndex.tendsto_cutoff_smul hp' hζ hζ01 hζ1
    (hζs.trans ball_subset_closedBall) u
  obtain ⟨n, hn⟩ := (Metric.tendsto_atTop.1 hVt) (ε / 2) (half_pos hε)
  have hVn : ‖V n - u‖ < ε / 2 := by simpa [dist_eq_norm] using hn n le_rfl
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (n : ℝ) + 1 := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; positivity
  have h2R : 0 < 2 * R := mul_pos two_pos hR
  have hn1 : (0 : ℝ) < n + 1 := hRdef ▸ hR
  -- the cut-off `χ`, equal to `1` on `closedBall 0 (2R)` and supported in `closedBall 0 (4R)`
  obtain ⟨χ, hχdef⟩ : ∃ χ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
    χ = fun x ↦ ζ ((2 * R)⁻¹ • x) := ⟨_, rfl⟩
  have hχ : ContDiff ℝ ∞ χ := hχdef ▸ hζ.comp (contDiff_id.const_smul _)
  have hχ1 : ∀ x, ‖x‖ ≤ 2 * R → χ x = 1 := fun x hx ↦ by
    rw [hχdef]
    exact hζ1 (mem_closedBall_zero_iff.2 ((norm_inv_smul_le_iff h2R x 1).2 (by linarith)))
  have hχs : tsupport χ ⊆ closedBall 0 (4 * R) := by
    refine closure_minimal (fun x hx ↦ mem_closedBall_zero_iff.2 ?_) isClosed_closedBall
    have h0 : ζ ((2 * R)⁻¹ • x) ≠ 0 := by rw [hχdef] at hx; exact hx
    have h := (norm_inv_smul_lt_iff h2R x 2).1 (mem_ball_zero_iff.1 (hζs (subset_closure h0)))
    linarith
  have hχc : HasCompactSupport χ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall _ _) (isClosed_tsupport _) hχs
  have hχb : ∃ M, ∀ x, |χ x| ≤ M ∧ ‖fderiv ℝ χ x‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hχc.fderiv ℝ).exists_bound_of_continuous (hχ.continuous_fderiv (by simp))
    refine ⟨max 1 M, fun x ↦ ⟨?_, (hM x).trans (le_max_right _ _)⟩⟩
    rw [hχdef]
    exact (abs_le.2 ⟨by linarith [(hζ01 ((2 * R)⁻¹ • x)).1], (hζ01 ((2 * R)⁻¹ • x)).2⟩).trans
      (le_max_left _ _)
  -- the compact piece of the boundary and its atlas
  have hK : IsCompact
      (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ closedBall 0 (4 * R)) :=
    (isCompact_closedBall _ _).inter_left isClosed_frontier
  have hχK : tsupport χ ∩ frontier (Ω : Set _)
      ⊆ frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ∩ closedBall 0 (4 * R) :=
    fun x hx ↦ ⟨hx.2, hχs hx.1⟩
  obtain ⟨k, c, hc⟩ := hΩ.exists_finite_atlas_of_isCompact hK inter_subset_left
  obtain ⟨P, C, hP⟩ := SobolevEuclidean.exists_extensionL_of_atlas (p := p) hK c hc hχ hχb hχK
  -- the extension operator on the line `ℝ ζ_R u`
  have hχζ : ∀ (a t : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))),
      a * (ζ ((n + 1 : ℝ)⁻¹ • x) * t) = χ x * (a * (ζ ((n + 1 : ℝ)⁻¹ • x) * t)) := by
    intro a t x
    by_cases h0 : ζ ((n + 1 : ℝ)⁻¹ • x) = 0
    · rw [h0]; ring
    · have hmem := (norm_inv_smul_lt_iff hn1 x 2).1 (mem_ball_zero_iff.1 (hζs (subset_closure h0)))
      rw [hχ1 x (by rw [hRdef]; linarith), one_mul]
  have key : ∀ z : SobolevEuclidean (d + 1) 1 p Ω, (∃ a : ℝ, a • V n = z) →
      SobolevMultiIndex.fn z =ᵐ[volume.restrict (Ω : Set _)]
        fun x ↦ χ x * SobolevMultiIndex.fn z x := by
    rintro z ⟨a, rfl⟩
    filter_upwards [SobolevMultiIndex.fn_smul a (V n), hV n] with x hx hxV
    have hA : SobolevMultiIndex.fn (a • V n) x
        = a * (ζ ((n + 1 : ℝ)⁻¹ • x) * SobolevMultiIndex.fn u x) :=
      hx.trans (congrArg (a * ·) hxV)
    exact hA.trans ((hχζ a _ x).trans (congrArg (χ x * ·) hA.symm))
  have hS : HasSobolevExtensionOn (ℝ ∙ V n) :=
    ⟨P.comp (Submodule.subtypeL _), fun w ↦ (hP w (key w (Submodule.mem_span_singleton.1 w.2))).1⟩
  obtain ⟨vv, hvv, hvvc, ww, hww, hwwt⟩ :=
    SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn hp'
      hS ⟨V n, Submodule.mem_span_singleton_self _⟩
  obtain ⟨m, hm⟩ := (Metric.tendsto_atTop.1 hwwt) (ε / 2) (half_pos hε)
  refine ⟨vv m, ww m, hvv m, hvvc m, hww m, ?_⟩
  calc ‖ww m - u‖ ≤ ‖ww m - V n‖ + ‖V n - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by simpa [dist_eq_norm] using hm m le_rfl) hVn
    _ = ε := add_halves ε

/-- Let $\Omega \subseteq \mathbb{R}^N$ be an open set of class $C^1$ (`IsContDiffChartDomain 1`),
whose boundary need not be bounded, and let $1 \le p < \infty$. For every
$u \in W^{1,p}(\Omega)$ there are functions $v_n \in C_c^\infty(\mathbb{R}^N)$ and
$w_n \in W^{1,p}(\Omega)$ with $w_n = v_n$ almost everywhere on $\Omega$ and $w_n \to u$ in
$W^{1,p}(\Omega)$. This is Corollary 9.8 of [brezis2011functional], the density of the
restrictions of $C_c^\infty(\mathbb{R}^N)$ in $W^{1,p}(\Omega)$.

The sequence comes from `SobolevEuclidean.exists_contDiff_hasCompactSupport_norm_sub_lt` with
$\varepsilon = 1/(n+1)$. -/
theorem SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto (hp' : p ≠ ⊤)
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧
      (∀ n, HasCompactSupport (v n)) ∧ ∃ w : ℕ → SobolevEuclidean (d + 1) 1 p Ω,
        (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume.restrict (Ω : Set _)] v n) ∧
        Tendsto w atTop (𝓝 u) := by
  choose v w hv hvc hw hwu using fun n : ℕ ↦
    SobolevEuclidean.exists_contDiff_hasCompactSupport_norm_sub_lt hp' hΩ u
      (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨v, hv, hvc, w, hw, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ (hwu n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end Corollary98

/-! ### Remark 9: the unit square by four reflections -/

section Square

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Let $\Omega, \Omega_0, \Omega_1, \Omega_2 \subseteq \mathbb{R}^N$ be open, let
$1 \le p \le \infty$, and let $S : W^{1,p}(\Omega_0) \to W^{1,p}(\Omega_1)$,
$S' : W^{1,p}(\Omega_1) \to W^{1,p}(\Omega_2)$ and
$S'' : W^{1,p}(\Omega_0) \to W^{1,p}(\Omega_2)$ be bounded linear maps with $S'' u = S'(Su)$ for
all $u$. Assume that $Su = u$ and $S'w = w$ almost everywhere on $\Omega$, and that for
constants $C, C' \in [0, \infty]$
$$\|Su\|_{L^p(\Omega_1)} \le C \|u\|_{L^p(\Omega_0)}, \qquad
  \|S'w\|_{L^p(\Omega_2)} \le C' \|w\|_{L^p(\Omega_1)}.$$
Then for every $u \in W^{1,p}(\Omega_0)$, $S''u = u$ almost everywhere on $\Omega$, and
$\|S''u\|_{L^p(\Omega_2)} \le C' C \|u\|_{L^p(\Omega_0)}$. -/
theorem SobolevEuclidean.extension_step_comp {Ω Ω₀ Ω₁ Ω₂ : Opens (EuclideanSpace ℝ (Fin N))}
    (S : SobolevEuclidean N 1 p Ω₀ →L[ℝ] SobolevEuclidean N 1 p Ω₁)
    (S' : SobolevEuclidean N 1 p Ω₁ →L[ℝ] SobolevEuclidean N 1 p Ω₂)
    (S'' : SobolevEuclidean N 1 p Ω₀ →L[ℝ] SobolevEuclidean N 1 p Ω₂) (hS'' : ∀ u, S'' u = S' (S u))
    {C C' : ℝ≥0∞}
    (hS : ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
      eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (Ω₁ : Set _))
        ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₀ : Set _)))
    (hS' : ∀ w, SobolevMultiIndex.fn (S' w) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn w ∧
      eLpNorm (SobolevMultiIndex.fn (S' w)) p (volume.restrict (Ω₂ : Set _))
        ≤ C' * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (Ω₁ : Set _))) :
    ∀ u, SobolevMultiIndex.fn (S'' u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
      eLpNorm (SobolevMultiIndex.fn (S'' u)) p (volume.restrict (Ω₂ : Set _))
        ≤ C' * C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₀ : Set _)) := fun u ↦ by
  rw [hS'' u]
  exact ⟨(hS' (S u)).1.trans (hS u).1,
    (hS' (S u)).2.trans (by rw [mul_assoc]; gcongr; exact (hS u).2)⟩

/-- A reflection across a translated hyperplane, with the operators as variables. Let
$v, c \in \mathbb{R}^N$ and let $V, \Omega_0, \Omega_1 \subseteq \mathbb{R}^N$ be open with
$V_+ = \Omega_0 - c$ and $\Omega_1 = V + c$, where
$V_+ = V \cap \{x : \langle x, v \rangle > 0\}$ (`posHalf v V`). Let $1 \le p \le \infty$, and
let $T_1 : W^{1,p}(\Omega_0) \to W^{1,p}(V_+)$, $R : W^{1,p}(V_+) \to W^{1,p}(V)$ and
$T_2 : W^{1,p}(V) \to W^{1,p}(\Omega_1)$ be bounded linear maps such that, almost everywhere on
the set named, $(T_1 u)(y) = u(y + c)$ on $V_+$, $Rw = w$ on $V_+$, and $(T_2 w)(y) = w(y - c)$
on $\Omega_1$. Assume that for constants $C_1, C_2 \in [0, \infty]$
$$\|T_1 u\|_{L^p(V_+)} \le C_1 \|u\|_{L^p(\Omega_0)}, \quad
  \|Rw\|_{L^p(V)} \le 2 \|w\|_{L^p(V_+)}, \quad
  \|T_2 w\|_{L^p(\Omega_1)} \le C_2 \|w\|_{L^p(V)}.$$
Then for every $u \in W^{1,p}(\Omega_0)$, $T_2(R(T_1 u)) = u$ almost everywhere on $\Omega_0$,
and $\|T_2(R(T_1 u))\|_{L^p(\Omega_1)} \le C_2 \cdot 2 \cdot C_1 \|u\|_{L^p(\Omega_0)}$. -/
theorem SobolevEuclidean.exists_reflectionStep_of_ops {v c : EuclideanSpace ℝ (Fin N)}
    {V Ω₀ Ω₁ : Opens (EuclideanSpace ℝ (Fin N))}
    (h₀ : (posHalf v V : Set (EuclideanSpace ℝ (Fin N))) = (fun x ↦ x + c) ⁻¹' Ω₀)
    (h₁ : (Ω₁ : Set (EuclideanSpace ℝ (Fin N))) = (fun x ↦ x + -c) ⁻¹' V)
    (T₁ : SobolevEuclidean N 1 p Ω₀ →L[ℝ] SobolevEuclidean N 1 p (posHalf v V))
    (R : SobolevEuclidean N 1 p (posHalf v V) →L[ℝ] SobolevEuclidean N 1 p V)
    (T₂ : SobolevEuclidean N 1 p V →L[ℝ] SobolevEuclidean N 1 p Ω₁) {C₁ C₂ : ℝ≥0∞}
    (hT₁ : ∀ u, SobolevMultiIndex.fn (T₁ u) =ᵐ[volume.restrict (posHalf v V : Set _)]
      fun y ↦ SobolevMultiIndex.fn u (y + c))
    (hT₁L : ∀ u, eLpNorm (SobolevMultiIndex.fn (T₁ u)) p (volume.restrict (posHalf v V : Set _))
      ≤ C₁ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₀ : Set _)))
    (hR : ∀ w, SobolevMultiIndex.fn (R w) =ᵐ[volume.restrict (posHalf v V : Set _)]
      SobolevMultiIndex.fn w)
    (hRL : ∀ w, eLpNorm (SobolevMultiIndex.fn (R w)) p (volume.restrict (V : Set _))
      ≤ 2 * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (posHalf v V : Set _)))
    (hT₂ : ∀ w, SobolevMultiIndex.fn (T₂ w) =ᵐ[volume.restrict (Ω₁ : Set _)]
      fun y ↦ SobolevMultiIndex.fn w (y + -c))
    (hT₂L : ∀ w, eLpNorm (SobolevMultiIndex.fn (T₂ w)) p (volume.restrict (Ω₁ : Set _))
      ≤ C₂ * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (V : Set _))) :
    ∀ u, SobolevMultiIndex.fn (T₂ (R (T₁ u))) =ᵐ[volume.restrict (Ω₀ : Set _)]
        SobolevMultiIndex.fn u ∧
      eLpNorm (SobolevMultiIndex.fn (T₂ (R (T₁ u)))) p (volume.restrict (Ω₁ : Set _))
        ≤ C₂ * 2 * C₁ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₀ : Set _)) := by
  intro u
  have hΩ₀m : MeasurableSet (Ω₀ : Set (EuclideanSpace ℝ (Fin N))) := Ω₀.isOpen.measurableSet
  have hΩ₁m : MeasurableSet (Ω₁ : Set (EuclideanSpace ℝ (Fin N))) := Ω₁.isOpen.measurableSet
  have hPm : MeasurableSet (posHalf v V : Set (EuclideanSpace ℝ (Fin N))) :=
    (posHalf v V).isOpen.measurableSet
  -- membership bookkeeping
  have hmem : ∀ x, x ∈ (Ω₀ : Set _) → x + -c ∈ (posHalf v V : Set _) := fun x hx ↦ by
    rw [h₀]
    simpa using hx
  have hΩ₀₁ : (Ω₀ : Set (EuclideanSpace ℝ (Fin N))) ⊆ Ω₁ := fun x hx ↦ by
    rw [h₁]
    exact (hmem x hx).1
  refine ⟨?_, ?_⟩
  · -- the identity on `Ω₀`
    have h2 : ∀ᵐ x ∂volume, x ∈ (Ω₁ : Set _) →
        SobolevMultiIndex.fn (T₂ (R (T₁ u))) x = SobolevMultiIndex.fn (R (T₁ u)) (x + -c) :=
      (ae_restrict_iff' hΩ₁m).1 (hT₂ (R (T₁ u)))
    have h3 : ∀ᵐ y ∂volume, y ∈ (posHalf v V : Set _) →
        SobolevMultiIndex.fn (R (T₁ u)) y = SobolevMultiIndex.fn (T₁ u) y :=
      (ae_restrict_iff' hPm).1 (hR (T₁ u))
    have h4 : ∀ᵐ y ∂volume, y ∈ (posHalf v V : Set _) →
        SobolevMultiIndex.fn (T₁ u) y = SobolevMultiIndex.fn u (y + c) :=
      (ae_restrict_iff' hPm).1 (hT₁ u)
    have h3' := (measurePreserving_add_right volume (-c)).quasiMeasurePreserving.ae h3
    have h4' := (measurePreserving_add_right volume (-c)).quasiMeasurePreserving.ae h4
    rw [EventuallyEq, ae_restrict_iff' hΩ₀m]
    filter_upwards [h2, h3', h4'] with x hx2 hx3 hx4 hx
    rw [hx2 (hΩ₀₁ hx), hx3 (hmem x hx), hx4 (hmem x hx)]
    simp
  · -- the `L^p` bound
    calc eLpNorm (SobolevMultiIndex.fn (T₂ (R (T₁ u)))) p (volume.restrict (Ω₁ : Set _))
        ≤ C₂ * eLpNorm (SobolevMultiIndex.fn (R (T₁ u))) p (volume.restrict (V : Set _)) :=
          hT₂L _
      _ ≤ C₂ * (2 * eLpNorm (SobolevMultiIndex.fn (T₁ u)) p
          (volume.restrict (posHalf v V : Set _))) := by gcongr; exact hRL _
      _ ≤ C₂ * (2 * (C₁ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₀ : Set _)))) := by
          gcongr; exact hT₁L _
      _ = C₂ * 2 * C₁ * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₀ : Set _)) := by
          ring

/-- A reflection across a translated hyperplane. Let $v \in \mathbb{R}^N$ be a unit vector, let
$c \in \mathbb{R}^N$, and let $V, \Omega_0, \Omega_1 \subseteq \mathbb{R}^N$ be open, with
$\sigma(V) = V$ for the reflection $\sigma$ across $v^\perp$, with $V_+ = \Omega_0 - c$ for
$V_+ = V \cap \{x : \langle x, v \rangle > 0\}$, and with $\Omega_1 = V + c$. Let
$1 \le p \le \infty$. Then there are a bounded linear map
$S : W^{1,p}(\Omega_0) \to W^{1,p}(\Omega_1)$ and a finite constant $C$ such that every
$u \in W^{1,p}(\Omega_0)$ satisfies $Su = u$ almost everywhere on $\Omega_0$ and
$\|Su\|_{L^p(\Omega_1)} \le C \|u\|_{L^p(\Omega_0)}$.

The map $S$ translates by $c$ (`SobolevEuclidean.compDiffeoL` for the translation), reflects
(`SobolevEuclidean.evenReflectionL`), and translates back. It is one of the "four successive
reflections" of Remark 9 in Chapter 9 of [brezis2011functional]. -/
theorem SobolevEuclidean.exists_reflectionStep {v c : EuclideanSpace ℝ (Fin N)} (hv : ‖v‖ = 1)
    {V Ω₀ Ω₁ : Opens (EuclideanSpace ℝ (Fin N))}
    (hV : hyperplaneReflection v '' (V : Set (EuclideanSpace ℝ (Fin N))) = V)
    (h₀ : (posHalf v V : Set (EuclideanSpace ℝ (Fin N))) = (fun x ↦ x + c) ⁻¹' Ω₀)
    (h₁ : (Ω₁ : Set (EuclideanSpace ℝ (Fin N))) = (fun x ↦ x + -c) ⁻¹' V) :
    ∃ (S : SobolevEuclidean N 1 p Ω₀ →L[ℝ] SobolevEuclidean N 1 p Ω₁) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω₀ : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (Ω₁ : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₀ : Set _)) := by
  -- the two translations as diffeomorphisms with bounded Jacobians
  have hd₁ := isDiffeoOnWithBoundedJacobian_affine
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N))) c Ω₀
  have hd₂ := isDiffeoOnWithBoundedJacobian_affine
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N))) (-c) V
  simp only [ContinuousLinearEquiv.coe_refl', id, ContinuousLinearEquiv.refl_symm] at hd₁ hd₂
  rw [← h₀] at hd₁
  rw [← h₁] at hd₂
  obtain ⟨C₁, hC₁, hT₁L⟩ := SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le
    (F := ℝ) (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (p := p) (μ := volume) hd₁
  obtain ⟨C₂, hC₂, hT₂L⟩ := SobolevMultiIndex.exists_eLpNorm_fn_compDiffeoL_le
    (F := ℝ) (b := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis) (p := p) (μ := volume) hd₂
  refine ⟨SobolevEuclidean.compDiffeoL hd₂ ∘L SobolevEuclidean.evenReflectionL hv hV ∘L
    SobolevEuclidean.compDiffeoL hd₁, C₂ * 2 * C₁,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hC₂ (by simp)) hC₁, ?_⟩
  exact SobolevEuclidean.exists_reflectionStep_of_ops h₀ h₁ (SobolevEuclidean.compDiffeoL hd₁)
    (SobolevEuclidean.evenReflectionL hv hV) (SobolevEuclidean.compDiffeoL hd₂)
    (fun u ↦ SobolevMultiIndex.fn_compDiffeoL hd₁ u) hT₁L
    (fun w ↦ SobolevMultiIndex.fn_evenReflectionL_restrict hv hV w)
    (fun w ↦ SobolevMultiIndex.eLpNorm_fn_evenReflectionL_le hv hV w)
    (fun w ↦ SobolevMultiIndex.fn_compDiffeoL hd₂ w) hT₂L


/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $1 \le p \le \infty$, and let
$P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ be a bounded linear map with $Pu = u$ almost
everywhere on $\Omega$ and $\|Pu\|_{L^p(\mathbb{R}^N)} \le C \|u\|_{L^p(\Omega)}$ for every $u$,
for a finite constant $C \in [0, \infty)$. Then there are a bounded linear map $P'$ and a real
constant $C'$ in the form of `SobolevEuclidean.exists_extensionL`: $P'u = u$ almost everywhere
on $\Omega$, $\|P'u\|_{L^p(\mathbb{R}^N)} \le C' \|u\|_{L^p(\Omega)}$ and
$\|P'u\|_{W^{1,p}(\mathbb{R}^N)} \le C' \|u\|_{W^{1,p}(\Omega)}$ for every $u$.

The proof takes $P' = P$ and $C' = \max\{C, \|P\|\}$. -/
theorem SobolevEuclidean.exists_extensionL_of_ops' {Ω : Opens (EuclideanSpace ℝ (Fin N))}
    (P : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hP : ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
      eLpNorm (SobolevMultiIndex.fn (P u)) p
          (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _))
        ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _))) :
    ∃ (P : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)) ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  refine ⟨P, max C.toReal ‖P‖, fun u ↦ ⟨(hP u).1, ?_, ?_⟩⟩
  · rw [← eLpNorm_restrict_coe_top]
    refine (hP u).2.trans ?_
    gcongr
    exact (ENNReal.ofReal_toReal hC).symm.le.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · exact (P.le_opNorm u).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- Assembly of an extension operator from four extension steps and a cut-off. Let $\Omega,
\Omega_1, \Omega_2, \Omega_3, \Omega_4 \subseteq \mathbb{R}^N$ be open, with
$\Omega \subseteq \Omega_1$, $\Omega \subseteq \Omega_2$ and $\Omega \subseteq \Omega_3$, let
$\Omega_0 = \Omega$, and let $1 \le p \le \infty$. Assume that for $j = 1, \dots, 4$ there are a
bounded linear map $S_j : W^{1,p}(\Omega_{j-1}) \to W^{1,p}(\Omega_j)$ and a finite constant
$C_j$ with $S_j u = u$ almost everywhere on $\Omega_{j-1}$ and $\|S_j u\|_{L^p(\Omega_j)} \le
C_j \|u\|_{L^p(\Omega_{j-1})}$ for every $u$. Assume also that there is a bounded linear map $E
: W^{1,p}(\Omega_4) \to W^{1,p}(\mathbb{R}^N)$ with $Ew = w$ almost everywhere on $\Omega$ and
$\|Ew\|_{L^p(\mathbb{R}^N)} \le \|w\|_{L^p(\Omega_4)}$ for every $w$. Then there are a bounded
linear map $P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ and a constant $C$ in the form of
Theorem 9.7: every $u \in W^{1,p}(\Omega)$ satisfies $Pu = u$ almost everywhere on $\Omega$,
$\|Pu\|_{L^p(\mathbb{R}^N)} \le C \|u\|_{L^p(\Omega)}$ and $\|Pu\|_{W^{1,p}(\mathbb{R}^N)} \le C
\|u\|_{W^{1,p}(\Omega)}$. -/
theorem SobolevEuclidean.exists_extensionL_of_steps
    {Ω Ω₁ Ω₂ Ω₃ Ω₄ : Opens (EuclideanSpace ℝ (Fin N))}
    (hΩ₁ : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ Ω₁)
    (hΩ₂ : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ Ω₂)
    (hΩ₃ : (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ Ω₃)
    (h₁ : ∃ (S : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p Ω₁) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (Ω₁ : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)))
    (h₂ : ∃ (S : SobolevEuclidean N 1 p Ω₁ →L[ℝ] SobolevEuclidean N 1 p Ω₂) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω₁ : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (Ω₂ : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₁ : Set _)))
    (h₃ : ∃ (S : SobolevEuclidean N 1 p Ω₂ →L[ℝ] SobolevEuclidean N 1 p Ω₃) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω₂ : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (Ω₃ : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₂ : Set _)))
    (h₄ : ∃ (S : SobolevEuclidean N 1 p Ω₃ →L[ℝ] SobolevEuclidean N 1 p Ω₄) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω₃ : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p (volume.restrict (Ω₄ : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω₃ : Set _)))
    (h₅ : ∃ E : SobolevEuclidean N 1 p Ω₄ →L[ℝ] SobolevEuclidean N 1 p ⊤, ∀ w,
      SobolevMultiIndex.fn (E w) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn w ∧
      eLpNorm (SobolevMultiIndex.fn (E w)) p
          (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin N))) : Set _))
        ≤ ENNReal.ofReal 1 * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (Ω₄ : Set _))) :
    ∃ (P : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set _)) ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  obtain ⟨S₁, C₁, hC₁, hS₁⟩ := h₁
  obtain ⟨S₂, C₂, hC₂, hS₂⟩ := h₂
  obtain ⟨S₃, C₃, hC₃, hS₃⟩ := h₃
  obtain ⟨S₄, C₄, hC₄, hS₄⟩ := h₄
  obtain ⟨E, hE⟩ := h₅
  have hres : ∀ {A B : Opens (EuclideanSpace ℝ (Fin N))}
      (h : (A : Set (EuclideanSpace ℝ (Fin N))) ⊆ (B : Set (EuclideanSpace ℝ (Fin N))))
      {f g : EuclideanSpace ℝ (Fin N) → ℝ},
      f =ᵐ[volume.restrict (B : Set _)] g → f =ᵐ[volume.restrict (A : Set _)] g := by
    intro _ _ h _ _ hfg
    exact hfg.filter_mono (ae_mono (Measure.restrict_mono h le_rfl))
  have hS₂' := fun u ↦ (hS₂ u).imp_left (hres hΩ₁)
  have hS₃' := fun u ↦ (hS₃ u).imp_left (hres hΩ₂)
  have hS₄' := fun u ↦ (hS₄ u).imp_left (hres hΩ₃)
  -- the composite, one operator at a time
  obtain ⟨P₂, hP₂⟩ : ∃ P₂ : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p Ω₂,
      ∀ u, P₂ u = S₂ (S₁ u) := ⟨S₂ ∘L S₁, fun u ↦ rfl⟩
  have h₂' := SobolevEuclidean.extension_step_comp S₁ S₂ P₂ hP₂ hS₁ hS₂'
  obtain ⟨P₃, hP₃⟩ : ∃ P₃ : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p Ω₃,
      ∀ u, P₃ u = S₃ (P₂ u) := ⟨S₃ ∘L P₂, fun u ↦ rfl⟩
  have h₃' := SobolevEuclidean.extension_step_comp P₂ S₃ P₃ hP₃ h₂' hS₃'
  obtain ⟨P₄, hP₄⟩ : ∃ P₄ : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p Ω₄,
      ∀ u, P₄ u = S₄ (P₃ u) := ⟨S₄ ∘L P₃, fun u ↦ rfl⟩
  have h₄' := SobolevEuclidean.extension_step_comp P₃ S₄ P₄ hP₄ h₃' hS₄'
  obtain ⟨P, hP⟩ : ∃ P : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤,
      ∀ u, P u = E (P₄ u) := ⟨E ∘L P₄, fun u ↦ rfl⟩
  have h₅' := SobolevEuclidean.extension_step_comp P₄ E P hP h₄' hE
  exact SobolevEuclidean.exists_extensionL_of_ops' P
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hC₄ (ENNReal.mul_ne_top hC₃
      (ENNReal.mul_ne_top hC₂ hC₁)))) h₅'

/-- The reflection $\sigma$ across the hyperplane $x_i = 0$ of $\mathbb{R}^N$ negates the coordinate
$i$ and keeps the others: $(\sigma x)_j = -x_i$ if $j = i$, and $(\sigma x)_j = x_j$ otherwise. -/
theorem hyperplaneReflection_single_apply (i : Fin N) (x : EuclideanSpace ℝ (Fin N)) (j : Fin N) :
    hyperplaneReflection (EuclideanSpace.single i (1 : ℝ)) x j
      = if j = i then -x i else x j := by
  rw [hyperplaneReflection_apply_of_norm_eq_one (by simp), EuclideanSpace.inner_single_right,
    PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  simp only [conj_trivial, one_mul]
  split_ifs with h
  · subst h; ring
  · ring

/-- For every vector $v$ of a real inner product space, the reflections across $v^\perp$ and across
$(-v)^\perp$ are equal. -/
theorem hyperplaneReflection_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) : hyperplaneReflection (-v) = hyperplaneReflection v := by
  have h : (ℝ ∙ -v) = (ℝ ∙ v) := by rw [← Set.neg_singleton, Submodule.span_neg]
  unfold hyperplaneReflection
  simp only [h]

/-- The open rectangle $(a_1, b_1) \times (a_2, b_2)$ of $\mathbb{R}^2$, as an open set. The
coordinate $x_1$ is `x 0`, and the coordinate $x_2$ is `x 1`. -/
def EuclideanSpace.rect (a₁ b₁ a₂ b₂ : ℝ) : Opens (EuclideanSpace ℝ (Fin 2)) :=
  ⟨{x | a₁ < x 0 ∧ x 0 < b₁ ∧ a₂ < x 1 ∧ x 1 < b₂}, by
    have h0 : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0 :=
      (EuclideanSpace.proj (0 : Fin 2)).continuous
    have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1 :=
      (EuclideanSpace.proj (1 : Fin 2)).continuous
    exact (isOpen_lt continuous_const h0).inter ((isOpen_lt h0 continuous_const).inter
      ((isOpen_lt continuous_const h1).inter (isOpen_lt h1 continuous_const)))⟩

/-- A point $x \in \mathbb{R}^2$ lies in the rectangle $(a_1, b_1) \times (a_2, b_2)$ if and only if
$a_1 < x_1 < b_1$ and $a_2 < x_2 < b_2$. -/
theorem EuclideanSpace.mem_rect {a₁ b₁ a₂ b₂ : ℝ} {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ (EuclideanSpace.rect a₁ b₁ a₂ b₂ : Set (EuclideanSpace ℝ (Fin 2)))
      ↔ a₁ < x 0 ∧ x 0 < b₁ ∧ a₂ < x 1 ∧ x 1 < b₂ :=
  Iff.rfl

/-- Every $x \in \mathbb{R}^2$ satisfies $\|x\| \le |x_1| + |x_2|$. -/
theorem EuclideanSpace.norm_le_abs_add_abs (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ≤ |x 0| + |x 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs]
  refine (Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq (by positivity))
  nlinarith [sq_abs (x 0), sq_abs (x 1), mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1))]

/-- The rectangle $(a_1, b_1) \times (a_2, b_2)$ lies in the closed ball with center $0$ and radius
$\max\{|a_1|, |b_1|\} + \max\{|a_2|, |b_2|\}$. In particular, it is bounded. -/
theorem EuclideanSpace.rect_subset_closedBall (a₁ b₁ a₂ b₂ : ℝ) :
    (EuclideanSpace.rect a₁ b₁ a₂ b₂ : Set (EuclideanSpace ℝ (Fin 2)))
      ⊆ closedBall 0 (max |a₁| |b₁| + max |a₂| |b₂|) := by
  intro x hx
  rw [EuclideanSpace.mem_rect] at hx
  rw [mem_closedBall_zero_iff]
  refine (EuclideanSpace.norm_le_abs_add_abs x).trans (add_le_add ?_ ?_)
  · exact abs_le.2 ⟨by linarith [neg_abs_le a₁, le_max_left |a₁| |b₁|],
      by linarith [le_abs_self b₁, le_max_right |a₁| |b₁|]⟩
  · exact abs_le.2 ⟨by linarith [neg_abs_le a₂, le_max_left |a₂| |b₂|],
      by linarith [le_abs_self b₂, le_max_right |a₂| |b₂|]⟩

/-- The closure of the unit square $(0, 1)^2$ lies in the closed square $[0, 1]^2$, which is
contained in $(-1, 3)^2$. -/
theorem EuclideanSpace.closure_rect_unit_subset :
    closure (EuclideanSpace.rect 0 1 0 1 : Set (EuclideanSpace ℝ (Fin 2)))
      ⊆ {x | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1} := by
  have h0 : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0 :=
    (EuclideanSpace.proj (0 : Fin 2)).continuous
  have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1 :=
    (EuclideanSpace.proj (1 : Fin 2)).continuous
  refine closure_minimal (fun x hx ↦ ?_) ((isClosed_le continuous_const h0).inter
    ((isClosed_le h0 continuous_const).inter
      ((isClosed_le continuous_const h1).inter (isClosed_le h1 continuous_const))))
  rw [EuclideanSpace.mem_rect] at hx
  exact ⟨hx.1.le, hx.2.1.le, hx.2.2.1.le, hx.2.2.2.le⟩

/-- The reflection across the side $x_2 = 0$ in Remark 9 in Chapter 9 of [brezis2011functional]. For
$1 \le p \le \infty$ there are a bounded linear map $S : W^{1,p}((0, 1) \times (0, 1)) \to
W^{1,p}((0, 1) \times (-1, 1))$ and a finite constant $C$ such that every $u$ satisfies $Su = u$
almost everywhere on $(0, 1) \times (0, 1)$ and
$$\|Su\|_{L^p((0, 1) \times (-1, 1))} \le C \|u\|_{L^p((0, 1) \times (0, 1))}.$$
-/
theorem SobolevEuclidean.exists_extension_rect_step₁ :
    ∃ (S : SobolevEuclidean 2 1 p (EuclideanSpace.rect 0 1 0 1) →L[ℝ]
        SobolevEuclidean 2 1 p (EuclideanSpace.rect 0 1 (-1) 1)) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u)
          =ᵐ[volume.restrict (EuclideanSpace.rect 0 1 0 1 : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p
            (volume.restrict (EuclideanSpace.rect 0 1 (-1) 1 : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (EuclideanSpace.rect 0 1 0 1 : Set _)) := by
  have he : ∀ i : Fin 2, ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by simp
  have hne : ∀ i : Fin 2, ‖(-EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by rw [norm_neg]; exact he i
  have hinv : ∀ i : Fin 2, Function.Involutive
      (hyperplaneReflection (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))) :=
    fun i x ↦ hyperplaneReflection_hyperplaneReflection _ x
  exact SobolevEuclidean.exists_reflectionStep (p := p)
    (v := EuclideanSpace.single 1 (1 : ℝ)) (c := 0) (he 1)
    (V := EuclideanSpace.rect 0 1 (-1) 1) (Ω₀ := EuclideanSpace.rect 0 1 0 1)
    (Ω₁ := EuclideanSpace.rect 0 1 (-1) 1)
    (by
      refine (hinv 1).image_eq_of_forall_mem_iff fun x ↦ ?_
      simp only [EuclideanSpace.mem_rect, hyperplaneReflection_single_apply, Fin.isValue,
        zero_ne_one, ↓reduceIte]
      constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
    (by
      ext x
      simp only [coe_posHalf, EuclideanSpace.inner_single_right, conj_trivial, one_mul,
        Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, add_zero, EuclideanSpace.mem_rect]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨h1, h2, h5, h4⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨⟨h1, h2, by linarith, h4⟩, h3⟩)
    (by
      ext x
      simp)
/-- The reflection across the side $x_2 = 1$ in Remark 9 in Chapter 9 of [brezis2011functional]. For
$1 \le p \le \infty$ there are a bounded linear map $S : W^{1,p}((0, 1) \times (-1, 1)) \to
W^{1,p}((0, 1) \times (-1, 3))$ and a finite constant $C$ such that every $u$ satisfies $Su = u$
almost everywhere on $(0, 1) \times (-1, 1)$ and
$$\|Su\|_{L^p((0, 1) \times (-1, 3))} \le C \|u\|_{L^p((0, 1) \times (-1, 1))}.$$
-/
theorem SobolevEuclidean.exists_extension_rect_step₂ :
    ∃ (S : SobolevEuclidean 2 1 p (EuclideanSpace.rect 0 1 (-1) 1) →L[ℝ]
        SobolevEuclidean 2 1 p (EuclideanSpace.rect 0 1 (-1) 3)) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u)
          =ᵐ[volume.restrict (EuclideanSpace.rect 0 1 (-1) 1 : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p
            (volume.restrict (EuclideanSpace.rect 0 1 (-1) 3 : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (EuclideanSpace.rect 0 1 (-1) 1 : Set _)) := by
  have he : ∀ i : Fin 2, ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by simp
  have hne : ∀ i : Fin 2, ‖(-EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by rw [norm_neg]; exact he i
  have hinv : ∀ i : Fin 2, Function.Involutive
      (hyperplaneReflection (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))) :=
    fun i x ↦ hyperplaneReflection_hyperplaneReflection _ x
  exact SobolevEuclidean.exists_reflectionStep (p := p)
    (v := -EuclideanSpace.single 1 (1 : ℝ)) (c := EuclideanSpace.single 1 (1 : ℝ)) (hne 1)
    (V := EuclideanSpace.rect 0 1 (-2) 2) (Ω₀ := EuclideanSpace.rect 0 1 (-1) 1)
    (Ω₁ := EuclideanSpace.rect 0 1 (-1) 3)
    (by
      rw [hyperplaneReflection_neg]
      refine (hinv 1).image_eq_of_forall_mem_iff fun x ↦ ?_
      simp only [EuclideanSpace.mem_rect, hyperplaneReflection_single_apply, Fin.isValue,
        zero_ne_one, ↓reduceIte]
      constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
    (by
      ext x
      simp only [coe_posHalf, inner_neg_right, EuclideanSpace.inner_single_right, conj_trivial,
        one_mul, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, EuclideanSpace.mem_rect,
        PiLp.add_apply, PiLp.single_apply, Fin.isValue, zero_ne_one, ↓reduceIte, add_zero]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨h1, h2, by linarith, by linarith⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨⟨h1, h2, by linarith, by linarith⟩, by linarith⟩)
    (by
      ext x
      simp only [Set.mem_preimage, EuclideanSpace.mem_rect, PiLp.add_apply, PiLp.neg_apply,
        PiLp.single_apply, Fin.isValue, zero_ne_one, ↓reduceIte, neg_zero, add_zero]
      constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
/-- The reflection across the side $x_1 = 0$ in Remark 9 in Chapter 9 of [brezis2011functional]. For
$1 \le p \le \infty$ there are a bounded linear map $S : W^{1,p}((0, 1) \times (-1, 3)) \to
W^{1,p}((-1, 1) \times (-1, 3))$ and a finite constant $C$ such that every $u$ satisfies
$Su = u$ almost everywhere on $(0, 1) \times (-1, 3)$ and
$$\|Su\|_{L^p((-1, 1) \times (-1, 3))} \le C \|u\|_{L^p((0, 1) \times (-1, 3))}.$$
-/
theorem SobolevEuclidean.exists_extension_rect_step₃ :
    ∃ (S : SobolevEuclidean 2 1 p (EuclideanSpace.rect 0 1 (-1) 3) →L[ℝ]
        SobolevEuclidean 2 1 p (EuclideanSpace.rect (-1) 1 (-1) 3)) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u)
          =ᵐ[volume.restrict (EuclideanSpace.rect 0 1 (-1) 3 : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p
            (volume.restrict (EuclideanSpace.rect (-1) 1 (-1) 3 : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (EuclideanSpace.rect 0 1 (-1) 3 : Set _)) := by
  have he : ∀ i : Fin 2, ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by simp
  have hne : ∀ i : Fin 2, ‖(-EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by rw [norm_neg]; exact he i
  have hinv : ∀ i : Fin 2, Function.Involutive
      (hyperplaneReflection (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))) :=
    fun i x ↦ hyperplaneReflection_hyperplaneReflection _ x
  exact SobolevEuclidean.exists_reflectionStep (p := p)
    (v := EuclideanSpace.single 0 (1 : ℝ)) (c := 0) (he 0)
    (V := EuclideanSpace.rect (-1) 1 (-1) 3) (Ω₀ := EuclideanSpace.rect 0 1 (-1) 3)
    (Ω₁ := EuclideanSpace.rect (-1) 1 (-1) 3)
    (by
      refine (hinv 0).image_eq_of_forall_mem_iff fun x ↦ ?_
      simp only [EuclideanSpace.mem_rect, hyperplaneReflection_single_apply, Fin.isValue,
        one_ne_zero, ↓reduceIte]
      constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
    (by
      ext x
      simp only [coe_posHalf, EuclideanSpace.inner_single_right, conj_trivial, one_mul,
        Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, add_zero, EuclideanSpace.mem_rect]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨h5, h2, h3, h4⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨⟨by linarith, h2, h3, h4⟩, h1⟩)
    (by
      ext x
      simp)
/-- The reflection across the side $x_1 = 1$ in Remark 9 in Chapter 9 of [brezis2011functional]. For
$1 \le p \le \infty$ there are a bounded linear map $S : W^{1,p}((-1, 1) \times (-1, 3)) \to
W^{1,p}((-1, 3) \times (-1, 3))$ and a finite constant $C$ such that every $u$ satisfies
$Su = u$ almost everywhere on $(-1, 1) \times (-1, 3)$ and
$$\|Su\|_{L^p((-1, 3) \times (-1, 3))} \le C \|u\|_{L^p((-1, 1) \times (-1, 3))}.$$
-/
theorem SobolevEuclidean.exists_extension_rect_step₄ :
    ∃ (S : SobolevEuclidean 2 1 p (EuclideanSpace.rect (-1) 1 (-1) 3) →L[ℝ]
        SobolevEuclidean 2 1 p (EuclideanSpace.rect (-1) 3 (-1) 3)) (C : ℝ≥0∞), C ≠ ⊤ ∧
      ∀ u, SobolevMultiIndex.fn (S u)
          =ᵐ[volume.restrict (EuclideanSpace.rect (-1) 1 (-1) 3 : Set _)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (S u)) p
            (volume.restrict (EuclideanSpace.rect (-1) 3 (-1) 3 : Set _))
          ≤ C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (EuclideanSpace.rect (-1) 1 (-1) 3 : Set _)) := by
  have he : ∀ i : Fin 2, ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by simp
  have hne : ∀ i : Fin 2, ‖(-EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    fun i ↦ by rw [norm_neg]; exact he i
  have hinv : ∀ i : Fin 2, Function.Involutive
      (hyperplaneReflection (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 2))) :=
    fun i x ↦ hyperplaneReflection_hyperplaneReflection _ x
  exact SobolevEuclidean.exists_reflectionStep (p := p)
    (v := -EuclideanSpace.single 0 (1 : ℝ)) (c := EuclideanSpace.single 0 (1 : ℝ)) (hne 0)
    (V := EuclideanSpace.rect (-2) 2 (-1) 3) (Ω₀ := EuclideanSpace.rect (-1) 1 (-1) 3)
    (Ω₁ := EuclideanSpace.rect (-1) 3 (-1) 3)
    (by
      rw [hyperplaneReflection_neg]
      refine (hinv 0).image_eq_of_forall_mem_iff fun x ↦ ?_
      simp only [EuclideanSpace.mem_rect, hyperplaneReflection_single_apply, Fin.isValue,
        one_ne_zero, ↓reduceIte]
      constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
    (by
      ext x
      simp only [coe_posHalf, inner_neg_right, EuclideanSpace.inner_single_right, conj_trivial,
        one_mul, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, EuclideanSpace.mem_rect,
        PiLp.add_apply, PiLp.single_apply, Fin.isValue, one_ne_zero, ↓reduceIte, add_zero]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
        exact ⟨by linarith, by linarith, h3, h4⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨⟨by linarith, by linarith, h3, h4⟩, by linarith⟩)
    (by
      ext x
      simp only [Set.mem_preimage, EuclideanSpace.mem_rect, PiLp.add_apply, PiLp.neg_apply,
        PiLp.single_apply, Fin.isValue, one_ne_zero, ↓reduceIte, neg_zero, add_zero]
      constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;>
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
/-- The cut-off step in Remark 9 in Chapter 9 of [brezis2011functional]. For $1 \le p \le \infty$
there is a bounded linear map $E : W^{1,p}((-1, 3)^2) \to W^{1,p}(\mathbb{R}^2)$ such that every
$w$ satisfies $Ew = w$ almost everywhere on the unit square $(0, 1)^2$ and
$\|Ew\|_{L^p(\mathbb{R}^2)} \le \|w\|_{L^p((-1, 3)^2)}$.

The map is $w \mapsto \psi w$, extended by zero, for a smooth function $\psi$ that equals $1$ on
the unit square and has support in $(-1, 3)^2$. -/
theorem SobolevEuclidean.exists_extension_rect_cutoff :
    ∃ E : SobolevEuclidean 2 1 p (EuclideanSpace.rect (-1) 3 (-1) 3) →L[ℝ]
      SobolevEuclidean 2 1 p ⊤, ∀ w,
      SobolevMultiIndex.fn (E w)
        =ᵐ[volume.restrict (EuclideanSpace.rect 0 1 0 1 : Set _)] SobolevMultiIndex.fn w ∧
      eLpNorm (SobolevMultiIndex.fn (E w)) p
          (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin 2))) : Set _))
        ≤ ENNReal.ofReal 1 * eLpNorm (SobolevMultiIndex.fn w) p
          (volume.restrict (EuclideanSpace.rect (-1) 3 (-1) 3 : Set _)) := by
  -- the cut-off
  have hKc : IsCompact (closure (EuclideanSpace.rect 0 1 0 1 : Set (EuclideanSpace ℝ (Fin 2)))) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (((Metric.isBounded_iff_subset_closedBall 0).2
        ⟨_, EuclideanSpace.rect_subset_closedBall 0 1 0 1⟩).closure)
  have hKV : closure (EuclideanSpace.rect 0 1 0 1 : Set (EuclideanSpace ℝ (Fin 2)))
      ⊆ EuclideanSpace.rect (-1) 3 (-1) 3 := fun x hx ↦ by
    have h := EuclideanSpace.closure_rect_unit_subset hx
    rw [SetLike.mem_coe, ← SetLike.mem_coe, EuclideanSpace.mem_rect]
    exact ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2.1], by linarith [h.2.2.2]⟩
  obtain ⟨ψ, hψs, hψ1, hψsupp, hψ01⟩ :=
    hKc.exists_contDiff_eqOn_one (EuclideanSpace.rect (-1) 3 (-1) 3).isOpen hKV
  have hψc : HasCompactSupport ψ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 _) (isClosed_tsupport ψ)
      (hψsupp.trans (EuclideanSpace.rect_subset_closedBall (-1) 3 (-1) 3))
  have hcut : IsSobolevCutoff (EuclideanSpace.rect (-1) 3 (-1) 3) ψ :=
    IsSobolevCutoff.of_hasCompactSupport hψs hψc hψsupp
  have hψM : ∀ x, |ψ x| ≤ 1 := fun x ↦
    abs_le.2 ⟨by linarith [(hψ01 x).1], (hψ01 x).2⟩
  have hΩ₄ : (EuclideanSpace.rect 0 1 0 1 : Set (EuclideanSpace ℝ (Fin 2)))
      ⊆ EuclideanSpace.rect (-1) 3 (-1) 3 := fun x hx ↦ by
    rw [EuclideanSpace.mem_rect] at hx ⊢
    exact ⟨by linarith [hx.1], by linarith [hx.2.1], by linarith [hx.2.2.1],
      by linarith [hx.2.2.2]⟩
  refine ⟨SobolevMultiIndex.extendZeroMulL ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis p
    volume hcut, fun w ↦ ⟨?_, ?_⟩⟩
  · have h := (SobolevMultiIndex.fn_extendZeroMulL_restrict hcut w).filter_mono
      (ae_mono (Measure.restrict_mono hΩ₄ le_rfl))
    rw [EventuallyEq, ae_restrict_iff' (EuclideanSpace.rect 0 1 0 1).isOpen.measurableSet] at h ⊢
    filter_upwards [h] with x hx hxΩ
    rw [hx hxΩ, hψ1 (subset_closure hxΩ), Pi.one_apply, one_smul]
  · rw [eLpNorm_restrict_coe_top]
    exact SobolevMultiIndex.eLpNorm_fn_extendZeroMulL_le hcut hψM w

/-- An extension operator for the unit square, which is not of class $C^1$. Let $\Omega = (0, 1)
\times (0, 1) \subseteq \mathbb{R}^2$ (`EuclideanSpace.rect 0 1 0 1`) and $1 \le p \le \infty$.
There are a bounded linear map $P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^2)$ and a constant
$C$ such that every $u \in W^{1,p}(\Omega)$ satisfies $Pu = u$ almost everywhere on $\Omega$ and
$$\|Pu\|_{L^p(\mathbb{R}^2)} \le C \|u\|_{L^p(\Omega)}, \qquad
  \|Pu\|_{W^{1,p}(\mathbb{R}^2)} \le C \|u\|_{W^{1,p}(\Omega)}.$$
This is Remark 9 in Chapter 9 of [brezis2011functional] (Figure 6), in the form of
`SobolevEuclidean.exists_extensionL`.

The operator is the composite of four successive reflections
(`SobolevEuclidean.exists_reflectionStep`) across $x_2 = 0$, $x_2 = 1$, $x_1 = 0$ and $x_1 = 1$,
which reach $W^{1,p}((-1, 3)^2)$, and of the multiplication by a smooth $\psi$ equal to $1$ on
the square with support in $(-1, 3)^2$, followed by extension by zero
(`SobolevMultiIndex.extendZeroMulL`). -/
theorem SobolevEuclidean.exists_extensionL_unitSquare :
    ∃ (P : SobolevEuclidean 2 1 p (EuclideanSpace.rect 0 1 0 1) →L[ℝ]
        SobolevEuclidean 2 1 p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean 2 1 p (EuclideanSpace.rect 0 1 0 1),
        SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (EuclideanSpace.rect 0 1 0 1 : Set _)]
          SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p
            (volume.restrict (EuclideanSpace.rect 0 1 0 1 : Set _)) ∧
        ‖P u‖ ≤ C * ‖u‖ := by
  refine SobolevEuclidean.exists_extensionL_of_steps ?_ ?_ ?_
    (SobolevEuclidean.exists_extension_rect_step₁ (p := p))
    (SobolevEuclidean.exists_extension_rect_step₂ (p := p))
    (SobolevEuclidean.exists_extension_rect_step₃ (p := p))
    (SobolevEuclidean.exists_extension_rect_step₄ (p := p))
    (SobolevEuclidean.exists_extension_rect_cutoff (p := p))
  · intro x hx
    rw [EuclideanSpace.mem_rect] at hx ⊢
    exact ⟨hx.1, hx.2.1, by linarith [hx.2.2.1], hx.2.2.2⟩
  · intro x hx
    rw [EuclideanSpace.mem_rect] at hx ⊢
    exact ⟨hx.1, hx.2.1, by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩
  · intro x hx
    rw [EuclideanSpace.mem_rect] at hx ⊢
    exact ⟨by linarith [hx.1], hx.2.1, by linarith [hx.2.2.1], by linarith [hx.2.2.2]⟩

end Square

/-! ### Extension domains from extension operators and extension steps -/

section Steps

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open and let $1 \le p \le \infty$. If there are a bounded
linear map $P : W^{1,p}(\Omega) \to W^{1,p}(\mathbb{R}^N)$ and a constant $C$ such that every
$u$ satisfies $Pu = u$ almost everywhere on $\Omega$, $\|Pu\|_{L^p(\mathbb{R}^N)} \le C
\|u\|_{L^p(\Omega)}$ and $\|Pu\|_{W^{1,p}(\mathbb{R}^N)} \le C \|u\|_{W^{1,p}(\Omega)}$, then
$\Omega$ is a $W^{1,p}$-extension domain (`IsSobolevExtensionDomain`).

The predicate does not contain the $L^p$ bound, so the proof does not use it. -/
theorem IsSobolevExtensionDomain.of_exists_extensionL {Ω : Opens 𝔼}
    (h : ∃ (P : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p ⊤) (C : ℝ),
      ∀ u, SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (Ω : Set 𝔼)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (Ω : Set 𝔼)) ∧
        ‖P u‖ ≤ C * ‖u‖) : IsSobolevExtensionDomain N p Ω := by
  obtain ⟨P, C, hP⟩ := h
  exact ⟨P.comp (Submodule.subtypeL ⊤), fun u ↦ (hP u.1).1⟩

/-- An extension step into an extension domain. Let $\Omega \subseteq \Omega_1 \subseteq
\mathbb{R}^N$ be open, let $1 \le p \le \infty$, let $\Omega_1$ be a $W^{1,p}$-extension domain
(`IsSobolevExtensionDomain`), and let $S : W^{1,p}(\Omega) \to W^{1,p}(\Omega_1)$ be a bounded
linear map with $Su = u$ almost everywhere on $\Omega$ for every $u$. Then $\Omega$ is a
$W^{1,p}$-extension domain.

If $P$ is an extension operator of $\Omega_1$, then $u \mapsto P(Su)$ is one of $\Omega$. -/
theorem IsSobolevExtensionDomain.of_extension_step {Ω Ω₁ : Opens 𝔼}
    (hΩ₁ : IsSobolevExtensionDomain N p Ω₁) (hle : Ω ≤ Ω₁)
    (S : SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p Ω₁)
    (hS : ∀ u, SobolevMultiIndex.fn (S u) =ᵐ[volume.restrict (Ω : Set 𝔼)]
      SobolevMultiIndex.fn u) : IsSobolevExtensionDomain N p Ω := by
  obtain ⟨P, hP⟩ := hΩ₁
  refine ⟨P ∘L (ContinuousLinearMap.id ℝ _).codRestrict ⊤ (fun _ ↦ Submodule.mem_top) ∘L S ∘L
    Submodule.subtypeL ⊤, fun u ↦ ?_⟩
  have h1 := hP ⟨S u.1, Submodule.mem_top⟩
  exact (h1.filter_mono
    (ae_mono (Measure.restrict_mono (SetLike.coe_subset_coe.2 hle) le_rfl))).trans (hS u.1)

end Steps
