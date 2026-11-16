/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Cutoff.lean` and `Numlib/Analysis/Sobolev/Calculus.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Numlib.Analysis.Sobolev.Calculus

/-!
# Extension by reflection

This module formalizes Lemma 9.2 of [brezis2011functional], §9.2: the even reflection $u^\star$ of a
function $u \in W^{1,p}(Q_+)$ across the hyperplane $x_N = 0$ lies in $W^{1,p}(Q)$, with
$\|u^\star\|_{L^p(Q)} \le 2 \|u\|_{L^p(Q_+)}$. The tangential derivatives of $u^\star$ are the even
reflections of those of $u$, and its normal derivative is the odd reflection of that of $u$. As
consequences, the module proves the extension theorem for the half space, the case
$\Omega = \mathbb{R}^N_+$ of Theorem 9.7, and Corollary 9.8 on the half space. It also proves the
trace inequality of Lemma 9.9 of [brezis2011functional], Comments on Chapter 9, 7:
$$\|u(\cdot, 0)\|_{L^p(\mathbb{R}^{N-1})} \le p^{1/p} \big(\|u\|_{L^p(\mathbb{R}^N_+)} +
  \|\partial_N u\|_{L^p(\mathbb{R}^N_+)}\big)$$
for $u \in C_c^1(\mathbb{R}^N)$ and $1 \le p < \infty$.

The source proves the lemma on $Q_+$ and remarks that the proof is unchanged on $\mathbb{R}^N_+$. In
Remark 9 it reflects a square across each of its sides. This module states all these cases as one
result in general position. Let $E$ be a finite-dimensional real inner product space with its
Lebesgue measure, let $v$ be a unit vector, let $\sigma$ be the reflection across the hyperplane
$v^\perp$, let $V$ be an open set with $\sigma(V) = V$, and let
$V_+ = V \cap \{x : \langle x, v \rangle > 0\}$.

## Main definitions

* `hyperplaneReflection`: the reflection $\sigma$ across the hyperplane $v^\perp$.
* `evenReflection`, `oddReflection`: the extensions $u^\star$ and $f^\square$ of a function from the
  half space $\langle x, v \rangle \ge 0$ to $E$.
* `reflectFDeriv`: the reflected tensor derivative, which is the derivative of $u^\star$ when $w$ is
  the derivative of $u$.
* `posHalf`: the positive half $V_+$ of an open set $V$.
* `SobolevMultiIndex.evenReflectionL`, `SobolevEuclidean.evenReflectionL`: the reflection
  $u \mapsto u^\star$ as a bounded linear map $W^{1,p}(V_+) \to W^{1,p}(V)$.

## Main results

* `inner_hyperplaneReflection`, `measurePreserving_hyperplaneReflection`, `volume_inner_eq_zero`:
  $\langle \sigma x, v \rangle = -\langle x, v \rangle$, $\sigma$ preserves Lebesgue measure, and
  the hyperplane $v^\perp$ is a null set.
* `HasWeakFDerivOn.evenReflection`: Lemma 9.2, the identity. If $u$ has the weak derivative $w$ on
  $V_+$, then $u^\star$ has the weak derivative `reflectFDeriv v w` on $V$.
* `MemSobolev.evenReflection`: Lemma 9.2, membership. If $u \in W^{1,p}(V_+)$, then
  $u^\star \in W^{1,p}(V)$.
* `eLpNorm_evenReflection_le`: the bound $\|u^\star\|_{L^p(V)} \le 2 \|u\|_{L^p(V_+)}$ of Lemma 9.2.
* `SobolevEuclidean.exists_extensionL_upperHalfSpace`, `IsSobolevExtensionDomain.upperHalfSpace`:
  Theorem 9.7 for the half space.
* `SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_upperHalfSpace`: Corollary 9.8 on
  the half space.
* `eLpNorm_lastZero_le_of_contDiff`: Lemma 9.9, the trace inequality on the half space.

## Proof outline

For Lemma 9.2, let $\varphi$ be a test function on $V$, and let
$\eta_k(x) = \eta(k \langle x, v \rangle)$ for a smooth cutoff $\eta$. The functions
$\eta_k \varphi$ and $\eta_k (\varphi \circ \sigma)$ are test functions on $V_+$. Their defining
identities, in the directions $y$ and $\sigma y$, add up to the identity for $\varphi$, up to a term
that carries the factor $k \eta'(k \langle x, v \rangle) (\varphi - \varphi \circ \sigma)$. This
term tends to $0$, because $\varphi - \varphi \circ \sigma$ vanishes on the hyperplane and $u$ is
integrable near it.

For Lemma 9.9, the one-dimensional inequality `enorm_rpow_le_lintegral_Ioi_of_hasDerivAt` follows
from the fundamental theorem of calculus for $|v|^p$ along a half-line and from Young's inequality.
Fubini's theorem along the last coordinate gives the inequality on the half space.

## Notation

* $\sigma$: the reflection `hyperplaneReflection v`, and $V_+$: the positive half `posHalf v V`.
* $u^\star$ and $f^\square$: the even reflection `evenReflection v u` and the odd reflection
  `oddReflection v f`.
* $\mathbb{R}^N_+ = \{x : x_N > 0\}$: the upper half space `EuclideanSpace.upperHalfSpace d`, with
  $N = d + 1$. The vector $e_N$ is the last basis vector.

## Implementation notes

* The reflection $\sigma$ is Mathlib's `Submodule.reflection (ℝ ∙ v)ᗮ`.
* The tensor form `HasWeakFDerivOn` makes the tangential and the normal cases of Lemma 9.2 one
  formula. On the reflected half, the derivative of $u^\star$ is
  $x \mapsto w(\sigma x) \circ \sigma$ (`reflectFDeriv v w`), by the chain rule for the linear
  isometry $\sigma$. In a direction $y \perp v$ this is the even reflection of $\partial_y u$, and
  along $v$ it is the odd reflection of $\partial_v u$.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology RealInnerProductSpace

noncomputable section

/-! ### The reflection across a hyperplane -/

section HyperplaneReflection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The reflection across the hyperplane $v^\perp$**, as a linear isometry equivalence of $E$. It
fixes $v^\perp$ and sends $v$ to $-v$. For a unit vector $v$ it is
$$\sigma(x) = x - 2 \langle x, v \rangle v,$$
and for $v = 0$ it is the identity.

The definition is Mathlib's `Submodule.reflection (ℝ ∙ v)ᗮ`. For $v = e_N$ it is the map
$(x', x_N) \mapsto (x', -x_N)$ of [brezis2011functional], §9.2, Lemma 9.2. -/
def hyperplaneReflection (v : E) : E ≃ₗᵢ[ℝ] E := Submodule.reflection (ℝ ∙ v)ᗮ

variable (v : E)

/-- The reflection sends $v$ to $-v$: $\sigma(v) = -v$. -/
@[simp]
theorem hyperplaneReflection_apply_self : hyperplaneReflection v v = -v :=
  Submodule.reflection_orthogonalComplement_singleton_eq_neg v

/-- The reflection is an involution: $\sigma(\sigma(x)) = x$ for every $x \in E$. -/
@[simp]
theorem hyperplaneReflection_hyperplaneReflection (x : E) :
    hyperplaneReflection v (hyperplaneReflection v x) = x :=
  Submodule.reflection_reflection _ x

/-- The reflection reverses the component along $v$: $\langle \sigma(x), v \rangle = -\langle x, v
\rangle$ for every $x \in E$. -/
theorem inner_hyperplaneReflection (x : E) : ⟪hyperplaneReflection v x, v⟫ = -⟪x, v⟫ := by
  have h := (hyperplaneReflection v).inner_map_map x v
  rw [hyperplaneReflection_apply_self, inner_neg_right] at h
  linarith

/-- The reflection fixes the hyperplane: if $\langle x, v \rangle = 0$, then $\sigma(x) = x$. -/
theorem hyperplaneReflection_apply_of_inner_eq_zero {x : E} (h : ⟪x, v⟫ = 0) :
    hyperplaneReflection v x = x :=
  Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_orthogonal_singleton_iff_inner_left.2 h)

/-- The reflection is an involution on sets: $\sigma(\sigma(s)) = s$ for every set $s \subseteq E$.
-/
theorem hyperplaneReflection_image_image (s : Set E) :
    hyperplaneReflection v '' (hyperplaneReflection v '' s) = s := by
  rw [Set.image_image]
  simp

/-- The preimage of a set under the involution $\sigma$ is its image: $\sigma^{-1}(s) = \sigma(s)$
for every set $s \subseteq E$. -/
theorem preimage_hyperplaneReflection (s : Set E) :
    hyperplaneReflection v ⁻¹' s = hyperplaneReflection v '' s := by
  ext x
  constructor
  · intro hx
    exact ⟨hyperplaneReflection v x, hx, hyperplaneReflection_hyperplaneReflection v x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- On a finite-dimensional space $E$, the reflection $\sigma$ preserves Lebesgue measure. -/
theorem measurePreserving_hyperplaneReflection :
    MeasurePreserving (hyperplaneReflection v) volume volume :=
  (hyperplaneReflection v).measurePreserving

omit [FiniteDimensional ℝ E] in
/-- The reflection $\sigma$ is a measurable embedding. -/
theorem measurableEmbedding_hyperplaneReflection :
    MeasurableEmbedding (hyperplaneReflection v) :=
  (hyperplaneReflection v).toHomeomorph.measurableEmbedding

/-- **The hyperplane $v^\perp$ is a null set.** Let $E$ be finite-dimensional and let $v \neq 0$.
Then the set $\{x \in E : \langle x, v \rangle = 0\}$ has Lebesgue measure $0$, because it is a
proper subspace of $E$. -/
theorem volume_inner_eq_zero {v : E} (hv : v ≠ 0) : volume {x : E | ⟪x, v⟫ = 0} = 0 := by
  have h1 : {x : E | ⟪x, v⟫ = 0} = ((ℝ ∙ v)ᗮ : Set E) := by
    ext x
    exact (Submodule.mem_orthogonal_singleton_iff_inner_left).symm
  have h2 : (ℝ ∙ v)ᗮ ≠ ⊤ := by
    intro h
    have hv' : v ∈ (ℝ ∙ v)ᗮ := by rw [h]; exact Submodule.mem_top
    exact hv (inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_left.1 hv'))
  rw [h1]
  exact Measure.addHaar_submodule volume _ h2

/-- Let $E$ be finite-dimensional and let $v \neq 0$. Then $\langle x, v \rangle \neq 0$ for almost
every $x \in E$. -/
theorem ae_inner_ne_zero {v : E} (hv : v ≠ 0) : ∀ᵐ x : E, ⟪x, v⟫ ≠ 0 :=
  measure_eq_zero_iff_ae_notMem.1 (volume_inner_eq_zero hv)

end HyperplaneReflection

/-! ### The cutoff $\eta$ in the normal direction -/

section Cutoff

/-- The cutoff $\eta(t) = \tau(2t - 1)$ of the proof of Lemma 9.2 of [brezis2011functional], where
$\tau$ is `Real.smoothTransition`. It is smooth, $\eta = 0$ on $(-\infty, 1/2]$, $\eta = 1$ on
$[1, \infty)$, and $\eta$ takes values in $[0, 1]$. -/
def reflectionCutoff (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1)

/-- The cutoff $\eta$ is smooth ($C^\infty$). -/
theorem contDiff_reflectionCutoff : ContDiff ℝ ∞ reflectionCutoff :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- The cutoff vanishes on $(-\infty, 1/2]$: $\eta(t) = 0$ for $t \le 1/2$. -/
theorem reflectionCutoff_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) : reflectionCutoff t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The cutoff equals $1$ on $[1, \infty)$: $\eta(t) = 1$ for $t \ge 1$. -/
theorem reflectionCutoff_of_one_le {t : ℝ} (ht : 1 ≤ t) : reflectionCutoff t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The cutoff is nonnegative: $\eta(t) \ge 0$ for every $t \in \mathbb{R}$. -/
theorem reflectionCutoff_nonneg (t : ℝ) : 0 ≤ reflectionCutoff t :=
  Real.smoothTransition.nonneg _

/-- The cutoff is at most $1$: $\eta(t) \le 1$ for every $t \in \mathbb{R}$. -/
theorem reflectionCutoff_le_one (t : ℝ) : reflectionCutoff t ≤ 1 :=
  Real.smoothTransition.le_one _

/-- The cutoff satisfies $|\eta(t)| \le 1$ for every $t \in \mathbb{R}$. -/
theorem abs_reflectionCutoff_le_one (t : ℝ) : |reflectionCutoff t| ≤ 1 := by
  rw [abs_of_nonneg (reflectionCutoff_nonneg t)]
  exact reflectionCutoff_le_one t

/-- The derivative of the cutoff vanishes where the cutoff is locally constant: $\eta'(t) = 0$ if
$t < 1/2$ or $t > 1$. -/
theorem deriv_reflectionCutoff_eq_zero {t : ℝ} (ht : t < 1 / 2 ∨ 1 < t) :
    deriv reflectionCutoff t = 0 := by
  rcases ht with ht | ht
  · have : reflectionCutoff =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact reflectionCutoff_of_le_half (le_of_lt hs)
    rw [this.deriv_eq, deriv_const]
  · have : reflectionCutoff =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact reflectionCutoff_of_one_le (le_of_lt hs)
    rw [this.deriv_eq, deriv_const]

/-- The derivative of the cutoff is bounded: there is a constant $C \ge 0$ with $|\eta'(t)| \le C$
for every $t \in \mathbb{R}$. -/
theorem exists_abs_deriv_reflectionCutoff_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv reflectionCutoff t| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (contDiff_reflectionCutoff.continuous_deriv (by simp)).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t ↦ ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact ((Real.norm_eq_abs _).symm.trans_le (hC t ht)).trans (le_max_left _ _)
  · have : t < 1 / 2 ∨ 1 < t := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · exact Or.inl (by linarith)
      · exact Or.inr ht
    rw [deriv_reflectionCutoff_eq_zero this, abs_zero]
    exact le_max_right _ _

end Cutoff

/-! ### The even and odd reflections, and the half sets -/

section Definitions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Extension by even reflection** across the hyperplane $v^\perp$:
$$u^\star(x) = \begin{cases} u(x) & \text{if } \langle x, v \rangle \ge 0, \\ u(\sigma(x)) &
  \text{otherwise.} \end{cases}$$

This is the function $u^\star$ of [brezis2011functional], §9.2, Lemma 9.2, for $v = e_N$. The
value on the hyperplane does not matter, because the hyperplane is a null set. -/
def evenReflection (v : E) (u : E → F) (x : E) : F :=
  if 0 ≤ ⟪x, v⟫ then u x else u (hyperplaneReflection v x)

/-- **Extension by odd reflection**:
$$f^\square(x) = \begin{cases} f(x) & \text{if } \langle x, v \rangle \ge 0, \\ -f(\sigma(x)) &
  \text{otherwise.} \end{cases}$$

This is the function $f^\square$ of [brezis2011functional], §9.2, proof of Lemma 9.2. -/
def oddReflection [Neg F] (v : E) (f : E → F) (x : E) : F :=
  if 0 ≤ ⟪x, v⟫ then f x else -f (hyperplaneReflection v x)

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The reflected tensor derivative** of $w : E \to \mathcal{L}(E, F)$:
$$x \mapsto \begin{cases} w(x) & \text{if } \langle x, v \rangle \ge 0, \\ w(\sigma(x)) \circ
  \sigma & \text{otherwise.} \end{cases}$$

This is the derivative of $u^\star$ when $w$ is the derivative of $u$, by the chain rule for the
linear isometry $\sigma$. In a direction $y \perp v$ it is the even reflection of
$x \mapsto w(x) y$, and along $v$ it is the odd reflection of $x \mapsto w(x) v$. -/
def reflectFDeriv (v : E) (w : E → E →L[ℝ] F) (x : E) : E →L[ℝ] F :=
  if 0 ≤ ⟪x, v⟫ then w x
  else (w (hyperplaneReflection v x)).comp
    ((hyperplaneReflection v).toContinuousLinearEquiv : E →L[ℝ] E)

variable (v : E)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- On the half space $\langle x, v \rangle \ge 0$, the even reflection is the function itself:
$u^\star(x) = u(x)$. -/
theorem evenReflection_of_nonneg {u : E → F} {x : E} (hx : 0 ≤ ⟪x, v⟫) :
    evenReflection v u x = u x := by
  simp [evenReflection, hx]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- On the half space $\langle x, v \rangle < 0$, the even reflection is the function at the
reflected point: $u^\star(x) = u(\sigma(x))$. -/
theorem evenReflection_of_neg {u : E → F} {x : E} (hx : ⟪x, v⟫ < 0) :
    evenReflection v u x = u (hyperplaneReflection v x) := by
  simp [evenReflection, not_le.2 hx]

/-- On the half space $\langle x, v \rangle \ge 0$, the reflected derivative `reflectFDeriv v w`
equals $w(x)$. -/
theorem reflectFDeriv_of_nonneg {w : E → E →L[ℝ] F} {x : E} (hx : 0 ≤ ⟪x, v⟫) :
    reflectFDeriv v w x = w x := by
  simp [reflectFDeriv, hx]

/-- On the half space $\langle x, v \rangle < 0$, the reflected derivative `reflectFDeriv v w`
equals $w(\sigma(x)) \circ \sigma$. -/
theorem reflectFDeriv_of_neg {w : E → E →L[ℝ] F} {x : E} (hx : ⟪x, v⟫ < 0) :
    reflectFDeriv v w x = (w (hyperplaneReflection v x)).comp
      ((hyperplaneReflection v).toContinuousLinearEquiv : E →L[ℝ] E) := by
  simp [reflectFDeriv, not_le.2 hx]

/-- In a direction $y$ with $\langle y, v \rangle = 0$, the reflected derivative `reflectFDeriv v w`
applied to $y$ is the even reflection of $x \mapsto w(x) y$. -/
theorem reflectFDeriv_apply_of_inner_eq_zero (w : E → E →L[ℝ] F) {y : E} (hy : ⟪y, v⟫ = 0)
    (x : E) : reflectFDeriv v w x y = evenReflection v (fun z ↦ w z y) x := by
  by_cases hx : 0 ≤ ⟪x, v⟫
  · rw [reflectFDeriv_of_nonneg v hx, evenReflection_of_nonneg v hx]
  · rw [reflectFDeriv_of_neg v (not_le.1 hx), evenReflection_of_neg v (not_le.1 hx),
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      hyperplaneReflection_apply_of_inner_eq_zero v hy]

/-- Along $v$, the reflected derivative `reflectFDeriv v w` applied to $v$ is the odd reflection of
$x \mapsto w(x) v$. -/
theorem reflectFDeriv_apply_self (w : E → E →L[ℝ] F) (x : E) :
    reflectFDeriv v w x v = oddReflection v (fun z ↦ w z v) x := by
  by_cases hx : 0 ≤ ⟪x, v⟫
  · simp [reflectFDeriv, oddReflection, hx]
  · simp [reflectFDeriv, oddReflection, hx]

/-- The reflected derivative has the norm of the derivative at the reflected point: the norm of
`reflectFDeriv v w` at $x$ equals the norm of the even reflection of $w$ at $x$. -/
theorem norm_reflectFDeriv (w : E → E →L[ℝ] F) (x : E) :
    ‖reflectFDeriv v w x‖ = ‖evenReflection v w x‖ := by
  by_cases hx : 0 ≤ ⟪x, v⟫
  · rw [reflectFDeriv_of_nonneg v hx, evenReflection_of_nonneg v hx]
  · rw [reflectFDeriv_of_neg v (not_le.1 hx), evenReflection_of_neg v (not_le.1 hx)]
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _

omit [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The positive half** $V_+ = V \cap \{x : \langle x, v \rangle > 0\}$ of an open set $V$, as an
open set. The function to be reflected lives on $V_+$. For $V = Q$ and $v = e_N$ it is $Q_+$,
and for $V = E$ it is a half space. -/
def posHalf (v : E) (V : Opens E) : Opens E :=
  ⟨(V : Set E) ∩ {x | 0 < ⟪x, v⟫},
    V.isOpen.inter (isOpen_lt continuous_const (continuous_id.inner continuous_const))⟩

/-- The underlying set of `posHalf v V` is $V \cap \{x : \langle x, v \rangle > 0\}$. -/
@[simp]
theorem coe_posHalf (V : Opens E) : (posHalf v V : Set E) = (V : Set E) ∩ {x | 0 < ⟪x, v⟫} :=
  rfl

/-- The positive half is a subset of the open set: $V_+ \subseteq V$. -/
theorem posHalf_le (V : Opens E) : posHalf v V ≤ V := fun _ hx ↦ hx.1

end Definitions

/-!
### Integrals of reflected functions

Let $G$ be a function on $V$ that agrees with $A$ on $\{\langle x, v \rangle \ge 0\}$ and with
$B \circ \sigma$ on $\{\langle x, v \rangle < 0\}$. Then $\int_V G = \int_{V_+} A + \int_{V_+} B$,
because the hyperplane is a null set and $\sigma$ preserves measure. Both $u^\star$ and
`reflectFDeriv v w`, multiplied by a test function, have this form.
-/

section Shape

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {v : E} {V : Opens E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The negative half $V_- = V \cap \{x : \langle x, v \rangle < 0\}$ of an open set $V$ is open. -/
theorem isOpen_negHalf : IsOpen ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}) :=
  V.isOpen.inter (isOpen_lt (continuous_id.inner continuous_const) continuous_const)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The positive half $V_+$ and the negative half $V_-$ of $V$ are disjoint. -/
theorem disjoint_posHalf_negHalf :
    Disjoint (posHalf v V : Set E) ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}) :=
  Set.disjoint_left.2 fun x hx hx' ↦
    (lt_asymm (show (0 : ℝ) < ⟪x, v⟫ from hx.2) (show ⟪x, v⟫ < 0 from hx'.2)).elim

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If $\sigma(V) = V$, then $x \in V$ if and only if $\sigma(x) \in V$. -/
theorem mem_of_image_eq (hV : hyperplaneReflection v '' (V : Set E) = V) {x : E} :
    x ∈ (V : Set E) ↔ hyperplaneReflection v x ∈ (V : Set E) := by
  constructor
  · intro hx
    rw [← hV]
    exact mem_image_of_mem _ hx
  · intro hx
    have : hyperplaneReflection v (hyperplaneReflection v x)
        ∈ hyperplaneReflection v '' (V : Set E) := mem_image_of_mem _ hx
    rwa [hyperplaneReflection_hyperplaneReflection, hV] at this

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If $\sigma(V) = V$, then the negative half is the reflection of the positive half:
$\sigma^{-1}(V_+) = V \cap \{x : \langle x, v \rangle < 0\}$. -/
theorem preimage_posHalf (hV : hyperplaneReflection v '' (V : Set E) = V) :
    hyperplaneReflection v ⁻¹' (posHalf v V : Set E) = (V : Set E) ∩ {x | ⟪x, v⟫ < 0} := by
  ext x
  simp only [mem_preimage, coe_posHalf, mem_inter_iff, mem_ofPred_eq, inner_hyperplaneReflection,
    ← mem_of_image_eq hV]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

/-- Let $v \neq 0$. Then $V$ is equal to the union $V_+ \cup V_-$ of its two halves up to a null
set. -/
theorem ae_eq_posHalf_union_negHalf (hv : v ≠ 0) :
    (V : Set E) =ᵐ[volume] (posHalf v V : Set E) ∪ ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}) := by
  filter_upwards [ae_inner_ne_zero hv] with x hx
  simp only [coe_posHalf, mem_union, mem_inter_iff, mem_ofPred_eq, eq_iff_iff]
  constructor
  · intro hxV
    rcases lt_or_gt_of_ne hx with h | h
    · exact Or.inr ⟨hxV, h⟩
    · exact Or.inl ⟨hxV, h⟩
  · rintro (h | h) <;> exact h.1

variable (hv : v ≠ 0) (hV : hyperplaneReflection v '' (V : Set E) = V) {G A B : E → F}
  (hA : ∀ x ∈ (V : Set E), 0 ≤ ⟪x, v⟫ → G x = A x)
  (hB : ∀ x ∈ (V : Set E), ⟪x, v⟫ < 0 → G x = B (hyperplaneReflection v x))
include hv hV hA hB

omit [NormedSpace ℝ F] in
/-- Let $v \neq 0$, let $\sigma(V) = V$, and let $G$ agree with $A$ on
$V \cap \{\langle x, v \rangle \ge 0\}$ and with $B \circ \sigma$ on
$V \cap \{\langle x, v \rangle < 0\}$. If $A$ and $B$ are almost everywhere strongly measurable
on $V_+$, then $G$ is almost everywhere strongly measurable on $V$. -/
theorem aestronglyMeasurable_of_reflected
    (hAm : AEStronglyMeasurable A (volume.restrict (posHalf v V : Set E)))
    (hBm : AEStronglyMeasurable B (volume.restrict (posHalf v V : Set E))) :
    AEStronglyMeasurable G (volume.restrict (V : Set E)) := by
  have hBσ : AEStronglyMeasurable (B ∘ hyperplaneReflection v)
      (volume.restrict ((V : Set E) ∩ {x | ⟪x, v⟫ < 0})) := by
    rw [← preimage_posHalf hV]
    exact hBm.comp_measurePreserving
      ((measurePreserving_hyperplaneReflection v).restrict_preimage_emb
        (measurableEmbedding_hyperplaneReflection v) _)
  have h1 : AEStronglyMeasurable ((posHalf v V : Set E).indicator A
      + ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}).indicator (B ∘ hyperplaneReflection v)) volume :=
    ((aestronglyMeasurable_indicator_iff (posHalf v V).isOpen.measurableSet).2 hAm).add
      ((aestronglyMeasurable_indicator_iff isOpen_negHalf.measurableSet).2 hBσ)
  refine (h1.mono_measure Measure.restrict_le_self).congr ?_
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet,
    ae_restrict_of_ae (ae_inner_ne_zero hv)] with x hxV hx
  rcases lt_or_gt_of_ne hx with h | h
  · have hxm : x ∈ (V : Set E) ∩ {x | ⟪x, v⟫ < 0} := ⟨hxV, h⟩
    have hxp : x ∉ (posHalf v V : Set E) := fun h' ↦ lt_asymm h (show (0 : ℝ) < ⟪x, v⟫ from h'.2)
    rw [Pi.add_apply, Set.indicator_of_notMem hxp, Set.indicator_of_mem hxm, zero_add, hB x hxV h]
    rfl
  · have hxp : x ∈ (posHalf v V : Set E) := ⟨hxV, h⟩
    have hxm : x ∉ (V : Set E) ∩ {x | ⟪x, v⟫ < 0} := fun h' ↦
      lt_asymm h (show ⟪x, v⟫ < 0 from h'.2)
    rw [Pi.add_apply, Set.indicator_of_mem hxp, Set.indicator_of_notMem hxm, add_zero,
      hA x hxV h.le]

omit [NormedSpace ℝ F] in
/-- **The $L^p$ norm of a reflected function.** Let $v \neq 0$, let $\sigma(V) = V$, let $1 \le p$,
and let $G$ agree with $A$ on $V \cap \{\langle x, v \rangle \ge 0\}$ and with $B \circ \sigma$
on $V \cap \{\langle x, v \rangle < 0\}$. If $B$ is almost everywhere strongly measurable on
$V_+$, then
$$\|G\|_{L^p(V)} \le \|A\|_{L^p(V_+)} + \|B\|_{L^p(V_+)}.$$
-/
theorem eLpNorm_le_of_reflected {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hBm : AEStronglyMeasurable B (volume.restrict (posHalf v V : Set E))) :
    eLpNorm G p (volume.restrict (V : Set E))
      ≤ eLpNorm A p (volume.restrict (posHalf v V : Set E))
        + eLpNorm B p (volume.restrict (posHalf v V : Set E)) := by
  have hBσ : AEStronglyMeasurable (B ∘ hyperplaneReflection v)
      (volume.restrict ((V : Set E) ∩ {x | ⟪x, v⟫ < 0})) := by
    rw [← preimage_posHalf hV]
    exact hBm.comp_measurePreserving
      ((measurePreserving_hyperplaneReflection v).restrict_preimage_emb
        (measurableEmbedding_hyperplaneReflection v) _)
  have heq : G =ᵐ[volume.restrict (V : Set E)] (posHalf v V : Set E).indicator A
      + ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}).indicator (B ∘ hyperplaneReflection v) := by
    filter_upwards [ae_restrict_mem V.isOpen.measurableSet,
      ae_restrict_of_ae (ae_inner_ne_zero hv)] with x hxV hx
    rcases lt_or_gt_of_ne hx with h | h
    · have hxm : x ∈ (V : Set E) ∩ {x | ⟪x, v⟫ < 0} := ⟨hxV, h⟩
      have hxp : x ∉ (posHalf v V : Set E) := fun h' ↦
        lt_asymm h (show (0 : ℝ) < ⟪x, v⟫ from h'.2)
      rw [Pi.add_apply, Set.indicator_of_notMem hxp, Set.indicator_of_mem hxm, zero_add,
        hB x hxV h]
      rfl
    · have hxp : x ∈ (posHalf v V : Set E) := ⟨hxV, h⟩
      have hxm : x ∉ (V : Set E) ∩ {x | ⟪x, v⟫ < 0} := fun h' ↦
        lt_asymm h (show ⟪x, v⟫ < 0 from h'.2)
      rw [Pi.add_apply, Set.indicator_of_mem hxp, Set.indicator_of_notMem hxm, add_zero,
        hA x hxV h.le]
  calc eLpNorm G p (volume.restrict (V : Set E))
      = eLpNorm ((posHalf v V : Set E).indicator A
          + ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}).indicator (B ∘ hyperplaneReflection v)) p
          (volume.restrict (V : Set E)) := eLpNorm_congr_ae heq
    _ ≤ eLpNorm ((posHalf v V : Set E).indicator A) p (volume.restrict (V : Set E))
        + eLpNorm (((V : Set E) ∩ {x | ⟪x, v⟫ < 0}).indicator (B ∘ hyperplaneReflection v)) p
          (volume.restrict (V : Set E)) :=
        eLpNorm_add_le hp
    _ ≤ eLpNorm ((posHalf v V : Set E).indicator A) p volume
        + eLpNorm (((V : Set E) ∩ {x | ⟪x, v⟫ < 0}).indicator (B ∘ hyperplaneReflection v)) p
          volume :=
        add_le_add (eLpNorm_mono_measure _ Measure.restrict_le_self)
          (eLpNorm_mono_measure _ Measure.restrict_le_self)
    _ = eLpNorm A p (volume.restrict (posHalf v V : Set E))
        + eLpNorm B p (volume.restrict (posHalf v V : Set E)) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict
            (posHalf v V).isOpen.measurableSet.nullMeasurableSet,
          eLpNorm_indicator_eq_eLpNorm_restrict isOpen_negHalf.measurableSet.nullMeasurableSet,
          ← preimage_posHalf hV, eLpNorm_comp_measurePreserving hBm
            ((measurePreserving_hyperplaneReflection v).restrict_preimage_emb
              (measurableEmbedding_hyperplaneReflection v) _)]

/-- **The integral of a reflected function.** Let $v \neq 0$, let $\sigma(V) = V$, and let $G$ agree
with $A$ on $V \cap \{\langle x, v \rangle \ge 0\}$ and with $B \circ \sigma$ on
$V \cap \{\langle x, v \rangle < 0\}$. If $A$ and $B$ are integrable on $V_+$, then
$$\int_V G = \int_{V_+} A + \int_{V_+} B.$$
-/
theorem setIntegral_of_reflected
    (hAi : IntegrableOn A (posHalf v V : Set E)) (hBi : IntegrableOn B (posHalf v V : Set E)) :
    ∫ x in (V : Set E), G x = (∫ x in (posHalf v V : Set E), A x)
      + ∫ x in (posHalf v V : Set E), B x := by
  have hVm : MeasurableSet ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}) := isOpen_negHalf.measurableSet
  have hVp : MeasurableSet (posHalf v V : Set E) := (posHalf v V).isOpen.measurableSet
  have hGA : EqOn G A (posHalf v V : Set E) := fun x hx ↦ hA x hx.1 hx.2.le
  have hGB : EqOn G (B ∘ hyperplaneReflection v) ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}) :=
    fun x hx ↦ hB x hx.1 hx.2
  have hBσ : IntegrableOn (B ∘ hyperplaneReflection v) ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}) := by
    rw [← preimage_posHalf hV]
    exact (((measurePreserving_hyperplaneReflection v).restrict_preimage_emb
      (measurableEmbedding_hyperplaneReflection v) _).integrable_comp_emb
      (measurableEmbedding_hyperplaneReflection v)).2 hBi
  calc ∫ x in (V : Set E), G x
      = ∫ x in (posHalf v V : Set E) ∪ ((V : Set E) ∩ {x | ⟪x, v⟫ < 0}), G x :=
        setIntegral_congr_set (ae_eq_posHalf_union_negHalf hv)
    _ = (∫ x in (posHalf v V : Set E), G x) + ∫ x in (V : Set E) ∩ {x | ⟪x, v⟫ < 0}, G x :=
        setIntegral_union disjoint_posHalf_negHalf hVm (hAi.congr_fun hGA.symm hVp)
          (hBσ.congr_fun hGB.symm hVm)
    _ = (∫ x in (posHalf v V : Set E), A x)
        + ∫ x in (V : Set E) ∩ {x | ⟪x, v⟫ < 0}, B (hyperplaneReflection v x) := by
        rw [setIntegral_congr_fun hVp hGA, setIntegral_congr_fun hVm hGB]
        rfl
    _ = (∫ x in (posHalf v V : Set E), A x) + ∫ x in (posHalf v V : Set E), B x := by
        rw [← preimage_posHalf hV,
          (measurePreserving_hyperplaneReflection v).setIntegral_preimage_emb
          (measurableEmbedding_hyperplaneReflection v) B _]

end Shape

/-! ### Lemma 9.2: the identity -/

section Identity

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {v : E} {V : Opens E} {p : ℝ≥0∞}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- Let $\mu$ be a measure that is finite on compact sets, let $S$ be a measurable set, let $g$ be a
continuous real function with compact support, let $1 \le p$, and let $f \in L^p(S)$. Then
$x \mapsto g(x) f(x)$ is integrable on $S$. -/
theorem integrableOn_smul_of_memLp {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {S : Set E}
    (hS : MeasurableSet S) {g : E → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {f : E → F} (hp : 1 ≤ p) (hf : MemLp f p (μ.restrict S)) :
    IntegrableOn (fun x ↦ g x • f x) S μ := by
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
  have hgtop : MemLp g ⊤ (μ.restrict S) :=
    memLp_top_of_bound hg.aestronglyMeasurable C (Eventually.of_forall hC)
  have h1 : MemLp (fun x ↦ g x • f x) p (μ.restrict S) := hgtop.smul hf
  refine memLp_one_iff_integrable.1 (h1.mono_exponent_of_measure_support_ne_top
    (s := tsupport g) (fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]) ?_ hp)
  rw [Measure.restrict_apply' hS]
  exact ((measure_mono inter_subset_left).trans_lt hgc.measure_lt_top).ne

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of $x \mapsto \langle x, v \rangle$ at every point is the linear form
$y \mapsto \langle v, y \rangle$ (`innerSL ℝ v`). -/
theorem hasFDerivAt_inner_right (v x : E) : HasFDerivAt (fun x ↦ ⟪x, v⟫) (innerSL ℝ v) x := by
  have : (fun x ↦ ⟪x, v⟫) = innerSL ℝ v := funext fun x ↦ by simp [real_inner_comm]
  rw [this]
  exact (innerSL ℝ v).hasFDerivAt

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For $c \in \mathbb{R}$, the derivative of the cutoff $x \mapsto \eta(c \langle x, v \rangle)$ at
$x$ is $\eta'(c \langle x, v \rangle) \, c \, \langle v, \cdot \rangle$. -/
theorem hasFDerivAt_reflectionCutoff_inner (v : E) (c : ℝ) (x : E) :
    HasFDerivAt (fun x ↦ reflectionCutoff (c * ⟪x, v⟫))
      (deriv reflectionCutoff (c * ⟪x, v⟫) • (c • innerSL ℝ v)) x :=
  ((contDiff_reflectionCutoff.differentiable (by simp)) _).hasDerivAt.comp_hasFDerivAt x
    ((hasFDerivAt_inner_right v x).const_mul c)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $\varphi : E \to \mathbb{R}$ be of class $C^1$ and $c \in \mathbb{R}$. Then the derivative
of $x \mapsto \eta(c \langle x, v \rangle) \varphi(x)$ at $x$ in the direction $y$ is
$$\eta(c \langle x, v \rangle) \, D\varphi(x) y + \eta'(c \langle x, v \rangle) \, c \, \langle
  y, v \rangle \, \varphi(x).$$
-/
theorem fderiv_reflectionCutoff_mul_apply (v : E) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (c : ℝ)
    (x y : E) :
    fderiv ℝ (fun x ↦ reflectionCutoff (c * ⟪x, v⟫) * φ x) x y
      = reflectionCutoff (c * ⟪x, v⟫) * fderiv ℝ φ x y
        + deriv reflectionCutoff (c * ⟪x, v⟫) * c * ⟪y, v⟫ * φ x := by
  have h : HasFDerivAt (fun x ↦ reflectionCutoff (c * ⟪x, v⟫) * φ x)
      (reflectionCutoff (c * ⟪x, v⟫) • fderiv ℝ φ x
        + φ x • (deriv reflectionCutoff (c * ⟪x, v⟫) • (c • innerSL ℝ v))) x :=
    (hasFDerivAt_reflectionCutoff_inner v c x).mul (hφ.differentiable one_ne_zero x).hasFDerivAt
  rw [h.fderiv]
  simp only [add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_comm]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $t > 0$. Then $\eta((n + 1) t) \to 1$ as $n \to \infty$. -/
theorem tendsto_reflectionCutoff_mul {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦ reflectionCutoff (((n : ℝ) + 1) * t)) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / t)
  filter_upwards [eventually_ge_atTop N] with n hn
  refine (reflectionCutoff_of_one_le ?_).symm
  have hn' : (1 : ℝ) / t ≤ (n : ℝ) + 1 := hN.trans (by exact_mod_cast (hn.trans (Nat.le_succ n)))
  rwa [div_le_iff₀ ht] at hn'

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $t > 0$. Then $\eta'((n + 1) t) = 0$ for all large $n$, since eventually $(n + 1) t > 1$. -/
theorem eventually_deriv_reflectionCutoff_mul_eq_zero {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, deriv reflectionCutoff (((n : ℝ) + 1) * t) = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / t)
  filter_upwards [eventually_ge_atTop N] with n hn
  refine deriv_reflectionCutoff_eq_zero (Or.inr ?_)
  have hn' : (1 : ℝ) / t < (n : ℝ) + 1 :=
    hN.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hn)
  rwa [div_lt_iff₀ ht] at hn'

/-- The cutoff $\theta_n(x) = \eta((n + 1) \langle x, v \rangle) \varphi(x)$ of a test function
$\varphi$ on $V$, as a test function on $V_+$. Its support lies in $\operatorname{tsupport}
\varphi \cap \{x : \langle x, v \rangle \ge 1/(2(n + 1))\}$. -/
def cutoffTestFunction (v : E) (V : Opens E) (φ : 𝓓(V, ℝ)) (n : ℕ) : 𝓓(posHalf v V, ℝ) where
  toFun x := reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * φ x
  contDiff' := (contDiff_reflectionCutoff.comp
    (contDiff_const.mul (contDiff_id.inner ℝ contDiff_const))).mul φ.contDiff
  hasCompactSupport' := φ.hasCompactSupport.mul_left
  tsupport_subset' := by
    refine subset_inter (tsupport_mul_subset_right.trans φ.tsupport_subset) ?_
    have hcl : IsClosed {x : E | 1 / 2 ≤ ((n : ℝ) + 1) * ⟪x, v⟫} :=
      isClosed_le continuous_const (continuous_const.mul (continuous_id.inner continuous_const))
    refine (closure_minimal ?_ hcl).trans fun x hx ↦ ?_
    · intro x hx
      by_contra h
      apply hx
      change reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * φ x = 0
      rw [reflectionCutoff_of_le_half (le_of_lt (not_le.1 h)), zero_mul]
    · have hx' : (1 : ℝ) / 2 ≤ ((n : ℝ) + 1) * ⟪x, v⟫ := hx
      by_contra hxv
      have : ((n : ℝ) + 1) * ⟪x, v⟫ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 hxv)
      linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The value of `cutoffTestFunction v V φ n` at $x$ is
$\eta((n + 1) \langle x, v \rangle) \varphi(x)$. -/
theorem cutoffTestFunction_apply (φ : 𝓓(V, ℝ)) (n : ℕ) (x : E) :
    cutoffTestFunction v V φ n x = reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * φ x :=
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of `cutoffTestFunction v V φ n` at $x$ in the direction $y$ is
$$\eta((n + 1) \langle x, v \rangle) \, D\varphi(x) y + \eta'((n + 1) \langle x, v \rangle) \,
  (n + 1) \, \langle y, v \rangle \, \varphi(x).$$
-/
theorem fderiv_cutoffTestFunction_apply (φ : 𝓓(V, ℝ)) (n : ℕ) (x y : E) :
    fderiv ℝ (cutoffTestFunction v V φ n) x y
      = reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * fderiv ℝ φ x y
        + deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * ((n : ℝ) + 1) * ⟪y, v⟫ * φ x :=
  fderiv_reflectionCutoff_mul_apply v (φ.contDiff.of_le (by simp)) _ x y

/-- If $\sigma(V) = V$, then the reflected test function $\varphi \circ \sigma$ of a test function
$\varphi$ on $V$ is a test function on $V$. -/
def TestFunction.compHyperplaneReflection (hV : hyperplaneReflection v '' (V : Set E) = V)
    (φ : 𝓓(V, ℝ)) : 𝓓(V, ℝ) where
  toFun x := φ (hyperplaneReflection v x)
  contDiff' := φ.contDiff.comp (hyperplaneReflection v).contDiff
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (hyperplaneReflection v).toHomeomorph
  tsupport_subset' := by
    have h1 : tsupport (fun x ↦ φ (hyperplaneReflection v x))
        ⊆ hyperplaneReflection v ⁻¹' tsupport φ :=
      closure_minimal (fun x hx ↦ subset_closure hx)
        ((isClosed_tsupport _).preimage (hyperplaneReflection v).continuous)
    refine h1.trans ?_
    rw [preimage_hyperplaneReflection, ← hV]
    exact image_mono φ.tsupport_subset

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The value of `TestFunction.compHyperplaneReflection hV φ` at $x$ is $\varphi(\sigma(x))$. -/
theorem TestFunction.compHyperplaneReflection_apply (hV : hyperplaneReflection v '' (V : Set E) = V)
    (φ : 𝓓(V, ℝ)) (x : E) :
    TestFunction.compHyperplaneReflection hV φ x = φ (hyperplaneReflection v x) :=
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The chain rule for the reflection. Let $\varphi : E \to \mathbb{R}$ be of class $C^1$. Then for
all $x, y \in E$,
$$D(\varphi \circ \sigma)(x) y = D\varphi(\sigma(x)) \, \sigma(y).$$
-/
theorem fderiv_comp_hyperplaneReflection_apply {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (x y : E) :
    fderiv ℝ (fun x ↦ φ (hyperplaneReflection v x)) x y
      = fderiv ℝ φ (hyperplaneReflection v x) (hyperplaneReflection v y) := by
  have hσ : HasFDerivAt (hyperplaneReflection v)
      ((hyperplaneReflection v).toContinuousLinearEquiv : E →L[ℝ] E) x :=
    (hyperplaneReflection v).toContinuousLinearEquiv.hasFDerivAt
  have h := (hφ.differentiable one_ne_zero _).hasFDerivAt.comp x hσ
  rw [show (fun x ↦ φ (hyperplaneReflection v x)) = φ ∘ hyperplaneReflection v from rfl, h.fderiv]
  rfl

omit [CompleteSpace F] in
/-- **Lemma 9.2** of [brezis2011functional] (extension by reflection), the identity. Let $E$ be a
finite-dimensional real inner product space with Lebesgue measure, let $v \in E$ be a unit
vector, let $V \subseteq E$ be an open set with $\sigma(V) = V$, and let $1 \le p \le \infty$.
Let $u : E \to F$ have the weak derivative $w$ on $V_+$, with $u \in L^p(V_+)$ and
$w \in L^p(V_+)$. Then the even reflection $u^\star$ has the weak derivative `reflectFDeriv v w`
on $V$.

The proof is the proof of the source, §9.2, with the cases (7) and (8) treated at once. Let
$\varphi$ be a test function on $V$ and $y$ a direction, and let
$\eta_n(x) = \eta((n + 1) \langle x, v \rangle)$. The cutoffs $\theta_n = \eta_n \varphi$ and
$\theta'_n = \eta_n (\varphi \circ \sigma)$ are test functions on $V_+$. So the defining
identity of $w$ holds for $\theta_n$ in the direction $y$ and for $\theta'_n$ in the direction
$\sigma y$. The sum of the two identities is
$$\int_{V_+} \eta_n \big(\partial_y \varphi + (\partial_y \varphi) \circ \sigma\big) u +
  \int_{V_+} (n + 1) \eta'_n \langle y, v \rangle (\varphi - \varphi \circ \sigma) u =
  -\int_{V_+} \eta_n \big(\varphi \, w(y) + (\varphi \circ \sigma) \, w(\sigma y)\big).$$
As $n \to \infty$, the first and the last integral converge by dominated convergence, since
$\eta_n \to 1$ off the null hyperplane and $|\eta_n| \le 1$. The middle integral tends to $0$:
$|\varphi - \varphi \circ \sigma| \le M \langle x, v \rangle$ by the mean value theorem, and
$\eta'_n$ vanishes off $\{(n + 1) \langle x, v \rangle \le 1\}$. So the integrand is bounded by
a fixed multiple of $|u|$ on the support and tends to $0$ pointwise. The limit identity is the
identity for $\varphi$, after $\int_V$ is split into $\int_{V_+} + \int_{V_-}$ and $V_-$ is
folded onto $V_+$ by the measure-preserving map $\sigma$ (`setIntegral_of_reflected`). -/
theorem HasWeakFDerivOn.evenReflection (hv : ‖v‖ = 1)
    (hV : hyperplaneReflection v '' (V : Set E) = V) (hp : 1 ≤ p) {u : E → F}
    {w : E → E →L[ℝ] F} (hu : HasWeakFDerivOn u w (posHalf v V) volume)
    (hup : MemLp u p (volume.restrict (posHalf v V : Set E)))
    (hwp : MemLp w p (volume.restrict (posHalf v V : Set E))) :
    HasWeakFDerivOn (evenReflection v u) (reflectFDeriv v w) V volume := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hVp : MeasurableSet (posHalf v V : Set E) := (posHalf v V).isOpen.measurableSet
  have hum := hup.aestronglyMeasurable
  have hwm := hwp.aestronglyMeasurable
  obtain ⟨σL, hσL⟩ : ∃ σL : E →L[ℝ] E,
    σL = ((hyperplaneReflection v).toContinuousLinearEquiv : E →L[ℝ] E) := ⟨_, rfl⟩
  have hσL' : ∀ x, σL x = hyperplaneReflection v x := fun x ↦ by rw [hσL]; rfl
  have hwσm : AEStronglyMeasurable (fun z ↦ (w z).comp σL)
      (volume.restrict (posHalf v V : Set E)) :=
    ((ContinuousLinearMap.compL ℝ E E F).flip σL).continuous.comp_aestronglyMeasurable hwm
  have hwσn : ∀ z, ‖(w z).comp σL‖ = ‖w z‖ := fun z ↦ by
    rw [hσL]
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _
  -- the reflected function and derivative lie in `L^p(V)`, hence are locally integrable
  have hurp : MemLp (_root_.evenReflection v u) p (volume.restrict (V : Set E)) := by
    refine (eLpNorm_le_of_reflected hv0 hV (fun x _ hx ↦ evenReflection_of_nonneg v hx)
      (fun x _ hx ↦ evenReflection_of_neg v hx) hp hum).trans_lt ?_
    exact ENNReal.add_lt_top.2 ⟨hup, hup⟩
  have hwrB : ∀ x ∈ (V : Set E), ⟪x, v⟫ < 0 →
      reflectFDeriv v w x = (w (hyperplaneReflection v x)).comp σL := by
    intro x _ hx
    rw [reflectFDeriv_of_neg v hx, hσL]
  have hwrp : MemLp (reflectFDeriv v w) p (volume.restrict (V : Set E)) := by
    refine (eLpNorm_le_of_reflected hv0 hV (fun x _ hx ↦ reflectFDeriv_of_nonneg v hx)
      hwrB hp hwσm).trans_lt (ENNReal.add_lt_top.2 ⟨hwp, ?_⟩)
    refine (eLpNorm_mono_ae hwσm (Eventually.of_forall fun z ↦ (hwσn z).le)).trans_lt hwp
  refine hasWeakFDerivOn_iff.2 ⟨hurp.locallyIntegrableOn hp, hwrp.locallyIntegrableOn hp,
    fun φ y ↦ ?_⟩
  -- the reflected test function, and the difference `χ = φ - φ ∘ σ`
  obtain ⟨ψ, hψ⟩ : ∃ ψ : 𝓓(V, ℝ), ψ = TestFunction.compHyperplaneReflection hV φ := ⟨_, rfl⟩
  have hψx : ∀ x, ψ x = φ (hyperplaneReflection v x) := fun x ↦ by rw [hψ]; rfl
  have hψd : ∀ x, fderiv ℝ ψ x (hyperplaneReflection v y)
      = fderiv ℝ φ (hyperplaneReflection v x) y := by
    intro x
    have : (ψ : E → ℝ) = fun x ↦ φ (hyperplaneReflection v x) := funext hψx
    rw [this, fderiv_comp_hyperplaneReflection_apply (φ.contDiff.of_le (by simp)),
      hyperplaneReflection_hyperplaneReflection]
  obtain ⟨χ, hχ⟩ : ∃ χ : E → ℝ, χ = fun x ↦ φ x - φ (hyperplaneReflection v x) := ⟨_, rfl⟩
  have hχs : ContDiff ℝ ∞ χ := by
    rw [hχ]
    exact φ.contDiff.sub (φ.contDiff.comp (hyperplaneReflection v).contDiff)
  have hχc : HasCompactSupport χ := by
    rw [hχ]
    exact φ.hasCompactSupport.sub
      (φ.hasCompactSupport.comp_homeomorph (hyperplaneReflection v).toHomeomorph)
  obtain ⟨Mχ, hMχ⟩ := (hχc.fderiv ℝ).exists_bound_of_continuous (hχs.continuous_fderiv (by simp))
  have hMχ0 : 0 ≤ Mχ := (norm_nonneg _).trans (hMχ 0)
  have hχ_bound : ∀ x, |χ x| ≤ Mχ * |⟪x, v⟫| := by
    intro x
    have hx0 : χ (x - ⟪x, v⟫ • v) = 0 := by
      have h0 : ⟪x - ⟪x, v⟫ • v, v⟫ = 0 := by
        rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
        ring
      rw [hχ]
      simp only
      rw [hyperplaneReflection_apply_of_inner_eq_zero v h0, sub_self]
    have := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ (hχs.differentiable (by simp)).differentiableAt) (fun z _ ↦ hMχ z)
      (mem_univ (x - ⟪x, v⟫ • v)) (mem_univ x)
    rw [hx0, sub_zero, sub_sub_cancel, norm_smul, hv, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs] at this
    exact this
  obtain ⟨Cη, hCη0, hCη⟩ := exists_abs_deriv_reflectionCutoff_le
  -- the cut-off test functions on `V₊`
  obtain ⟨θ, hθ⟩ : ∃ θ : ℕ → 𝓓(posHalf v V, ℝ), θ = cutoffTestFunction v V φ := ⟨_, rfl⟩
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ℕ → 𝓓(posHalf v V, ℝ), θ' = cutoffTestFunction v V ψ := ⟨_, rfl⟩
  have hθx : ∀ n x, θ n x = reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * φ x := fun (n : ℕ) x ↦ by
    rw [hθ]; rfl
  have hθ'x : ∀ n x, θ' n x = reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)
      * φ (hyperplaneReflection v x) := fun (n : ℕ) x ↦ by
    rw [hθ', cutoffTestFunction_apply, hψx]
  have hθd : ∀ n x, fderiv ℝ (θ n) x y
      = reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * fderiv ℝ φ x y
        + deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * ((n : ℝ) + 1) * ⟪y, v⟫ * φ x :=
    fun n x ↦ by rw [hθ]; exact fderiv_cutoffTestFunction_apply φ n x y
  have hθ'd : ∀ n x, fderiv ℝ (θ' n) x (hyperplaneReflection v y)
      = reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * fderiv ℝ φ (hyperplaneReflection v x) y
        - deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * ((n : ℝ) + 1) * ⟪y, v⟫
          * φ (hyperplaneReflection v x) := by
    intro n x
    rw [hθ', fderiv_cutoffTestFunction_apply ψ n x, hψd, inner_hyperplaneReflection, hψx]
    ring
  -- the identities of the weak derivative on `V₊` for the two cut-offs
  have I1 : ∀ n : ℕ, ∫ x in (posHalf v V : Set E), fderiv ℝ (θ n) x y • u x
      = -∫ x in (posHalf v V : Set E), θ n x • w x y := fun n : ℕ ↦
    hu.integral_smul_eq (θ n) y
  have I2 : ∀ n : ℕ,
      ∫ x in (posHalf v V : Set E), fderiv ℝ (θ' n) x (hyperplaneReflection v y) • u x
      = -∫ x in (posHalf v V : Set E), θ' n x • w x (hyperplaneReflection v y) := fun n : ℕ ↦
    hu.integral_smul_eq (θ' n) (hyperplaneReflection v y)
  -- the three pieces and their limits
  obtain ⟨a, ha⟩ : ∃ a : E → ℝ,
    a = fun x ↦ fderiv ℝ φ x y + fderiv ℝ φ (hyperplaneReflection v x) y := ⟨_, rfl⟩
  have hac : Continuous a := by
    rw [ha]
    exact (φ.fderivApply y).contDiff.continuous.add
      ((φ.fderivApply y).contDiff.continuous.comp (hyperplaneReflection v).continuous)
  have hacs : HasCompactSupport a := by
    rw [ha]
    exact (φ.fderivApply y).hasCompactSupport.add
      ((φ.fderivApply y).hasCompactSupport.comp_homeomorph (hyperplaneReflection v).toHomeomorph)
  obtain ⟨b, hb⟩ : ∃ b : E → F, b = fun x ↦
    φ x • w x y + φ (hyperplaneReflection v x) • w x (hyperplaneReflection v y) := ⟨_, rfl⟩
  have hwy : ∀ z : E, MemLp (fun x ↦ w x z) p (volume.restrict (posHalf v V : Set E)) := fun z ↦
    (ContinuousLinearMap.apply ℝ F z).comp_memLp' hwp
  have hbi : IntegrableOn b (posHalf v V : Set E) := by
    rw [hb]
    exact (integrableOn_smul_of_memLp hVp φ.contDiff.continuous φ.hasCompactSupport hp
      (hwy y)).add (integrableOn_smul_of_memLp hVp
        (φ.contDiff.continuous.comp (hyperplaneReflection v).continuous)
        (φ.hasCompactSupport.comp_homeomorph (hyperplaneReflection v).toHomeomorph) hp (hwy _))
  have hai : IntegrableOn (fun x ↦ a x • u x) (posHalf v V : Set E) :=
    integrableOn_smul_of_memLp hVp hac hacs hp hup
  obtain ⟨e, he⟩ : ∃ e : ℕ → E → ℝ, e = fun (n : ℕ) (x : E) ↦
    deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * ((n : ℝ) + 1) * ⟪y, v⟫ * χ x := ⟨_, rfl⟩
  have hec : ∀ n : ℕ, Continuous (e n) := fun n : ℕ ↦ by
    rw [he]
    exact (((contDiff_reflectionCutoff.continuous_deriv (by simp)).comp
      (continuous_const.mul (continuous_id.inner continuous_const))).mul continuous_const).mul
      continuous_const |>.mul hχs.continuous
  have hecs : ∀ n : ℕ, HasCompactSupport (e n) := fun n : ℕ ↦ by
    rw [he]
    exact hχc.mul_left
  have hηc : ∀ n : ℕ, Continuous fun x ↦ reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) := fun n : ℕ ↦
    contDiff_reflectionCutoff.continuous.comp
      (continuous_const.mul (continuous_id.inner continuous_const))
  -- the algebraic identity `L_n + X_n = -R_n`
  have hLX : ∀ n : ℕ, (∫ x in (posHalf v V : Set E),
        (reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * a x) • u x)
      + ∫ x in (posHalf v V : Set E), e n x • u x
      = -∫ x in (posHalf v V : Set E), reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) • b x := by
    intro n
    have i1 : IntegrableOn (fun x ↦ fderiv ℝ (θ n) x y • u x) (posHalf v V : Set E) :=
      integrableOn_smul_of_memLp hVp ((θ n).fderivApply y).contDiff.continuous
        ((θ n).fderivApply y).hasCompactSupport hp hup
    have i2 : IntegrableOn (fun x ↦ fderiv ℝ (θ' n) x (hyperplaneReflection v y) • u x)
        (posHalf v V : Set E) :=
      integrableOn_smul_of_memLp hVp ((θ' n).fderivApply _).contDiff.continuous
        ((θ' n).fderivApply _).hasCompactSupport hp hup
    have j1 : IntegrableOn (fun x ↦ θ n x • w x y) (posHalf v V : Set E) :=
      integrableOn_smul_of_memLp hVp (θ n).contDiff.continuous (θ n).hasCompactSupport hp (hwy y)
    have j2 : IntegrableOn (fun x ↦ θ' n x • w x (hyperplaneReflection v y))
        (posHalf v V : Set E) :=
      integrableOn_smul_of_memLp hVp (θ' n).contDiff.continuous (θ' n).hasCompactSupport hp
        (hwy _)
    have hL : (∫ x in (posHalf v V : Set E),
          (reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * a x) • u x)
        + ∫ x in (posHalf v V : Set E), e n x • u x
        = (∫ x in (posHalf v V : Set E), fderiv ℝ (θ n) x y • u x)
          + ∫ x in (posHalf v V : Set E), fderiv ℝ (θ' n) x (hyperplaneReflection v y) • u x := by
      rw [← integral_add i1 i2]
      have hia : IntegrableOn (fun x ↦ (reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * a x) • u x)
          (posHalf v V : Set E) :=
        integrableOn_smul_of_memLp hVp ((hηc n).mul hac) hacs.mul_left hp hup
      have hie : IntegrableOn (fun x ↦ e n x • u x) (posHalf v V : Set E) :=
        integrableOn_smul_of_memLp hVp (hec n) (hecs n) hp hup
      rw [← integral_add hia hie]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only
      rw [hθd, hθ'd, ha, he, hχ, ← add_smul, ← add_smul]
      congr 1
      simp only
      ring
    have hR : -∫ x in (posHalf v V : Set E), reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) • b x
        = -(∫ x in (posHalf v V : Set E), θ n x • w x y)
          + -∫ x in (posHalf v V : Set E), θ' n x • w x (hyperplaneReflection v y) := by
      rw [← neg_add, ← integral_add j1 j2]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only
      rw [hθx, hθ'x, hb, smul_add, mul_smul, mul_smul]
    rw [hL, hR, I1, I2]
  -- the limits
  have hsplitL : Tendsto (fun n : ℕ ↦ ∫ x in (posHalf v V : Set E),
      (reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * a x) • u x) atTop
      (𝓝 (∫ x in (posHalf v V : Set E), a x • u x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖a x • u x‖)
      (fun n : ℕ ↦ ((hηc n).mul hac).aestronglyMeasurable.smul hum) hai.norm
      (fun n : ℕ ↦ Eventually.of_forall fun x ↦ ?_) ?_
    · rw [norm_smul, norm_smul, norm_mul, Real.norm_eq_abs (reflectionCutoff _)]
      calc |reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)| * ‖a x‖ * ‖u x‖
          ≤ 1 * ‖a x‖ * ‖u x‖ := by gcongr; exact abs_reflectionCutoff_le_one _
        _ = ‖a x‖ * ‖u x‖ := by rw [one_mul]
    · filter_upwards [ae_restrict_mem hVp] with x hx
      have := ((tendsto_reflectionCutoff_mul (show (0 : ℝ) < ⟪x, v⟫ from hx.2)).mul_const
        (a x)).smul_const (u x)
      simpa using this
  have hsplitX : Tendsto (fun n : ℕ ↦ ∫ x in (posHalf v V : Set E), e n x • u x) atTop (𝓝 0) := by
    have hKint : IntegrableOn ((tsupport χ).indicator u) (posHalf v V : Set E) := by
      rw [IntegrableOn, integrable_indicator_iff (isClosed_tsupport χ).measurableSet,
        IntegrableOn, Measure.restrict_restrict (isClosed_tsupport χ).measurableSet]
      have : IsFiniteMeasure (volume.restrict (tsupport χ ∩ (posHalf v V : Set E))) :=
        isFiniteMeasure_restrict.2 ((measure_mono inter_subset_left).trans_lt
          hχc.measure_lt_top).ne
      exact (hup.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)).integrable hp
    have h0 : (0 : F) = ∫ x in (posHalf v V : Set E), (0 : F) := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence
      (fun x ↦ (Cη * Mχ * |⟪y, v⟫|) * ‖(tsupport χ).indicator u x‖)
      (fun n : ℕ ↦ (hec n).aestronglyMeasurable.smul hum) (hKint.norm.const_mul _)
      (fun n : ℕ ↦ Eventually.of_forall fun x ↦ ?_) ?_
    · rw [norm_smul, Real.norm_eq_abs]
      by_cases hxχ : x ∈ tsupport χ
      · rw [Set.indicator_of_mem hxχ]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [he]
        simp only
        by_cases hx1 : 1 < ((n : ℝ) + 1) * ⟪x, v⟫
        · rw [deriv_reflectionCutoff_eq_zero (Or.inr hx1), zero_mul, zero_mul, zero_mul, abs_zero]
          positivity
        · rw [abs_mul, abs_mul, abs_mul]
          rcases le_or_gt ⟪x, v⟫ 0 with hxv | hxv
          · have : ((n : ℝ) + 1) * ⟪x, v⟫ ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by positivity) hxv
            have hηz : deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) = 0 :=
              deriv_reflectionCutoff_eq_zero (Or.inl (by linarith))
            rw [hηz, abs_zero, zero_mul, zero_mul, zero_mul]
            positivity
          · calc |deriv reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)| * |(n : ℝ) + 1| * |⟪y, v⟫|
                  * |χ x|
                ≤ Cη * |(n : ℝ) + 1| * |⟪y, v⟫| * (Mχ * |⟪x, v⟫|) := by
                  gcongr
                  · exact hCη _
                  · exact hχ_bound x
              _ = Cη * Mχ * |⟪y, v⟫| * (((n : ℝ) + 1) * ⟪x, v⟫) := by
                  rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), abs_of_pos hxv]; ring
              _ ≤ Cη * Mχ * |⟪y, v⟫| * 1 := by
                  gcongr
                  exact not_lt.1 hx1
              _ = Cη * Mχ * |⟪y, v⟫| := mul_one _
      · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hxχ
        rw [he]
        simp only
        rw [hχ0, mul_zero, abs_zero, zero_mul]
        positivity
    · filter_upwards [ae_restrict_mem hVp] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_deriv_reflectionCutoff_mul_eq_zero
        (show (0 : ℝ) < ⟪x, v⟫ from hx.2)] with n hn
      rw [he]
      simp only
      rw [hn, zero_mul, zero_mul, zero_mul, zero_smul]
  have hsplitR : Tendsto (fun n : ℕ ↦ ∫ x in (posHalf v V : Set E),
      reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) • b x) atTop
      (𝓝 (∫ x in (posHalf v V : Set E), b x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖b x‖)
      (fun n : ℕ ↦ (hηc n).aestronglyMeasurable.smul hbi.aestronglyMeasurable) hbi.norm
      (fun n : ℕ ↦ Eventually.of_forall fun x ↦ ?_) ?_
    · rw [norm_smul, Real.norm_eq_abs]
      calc |reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫)| * ‖b x‖ ≤ 1 * ‖b x‖ := by
            gcongr; exact abs_reflectionCutoff_le_one _
        _ = ‖b x‖ := one_mul _
    · filter_upwards [ae_restrict_mem hVp] with x hx
      have := (tendsto_reflectionCutoff_mul (show (0 : ℝ) < ⟪x, v⟫ from hx.2)).smul_const (b x)
      simpa using this
  -- the limit identity on `V₊`
  have hlim : (∫ x in (posHalf v V : Set E), a x • u x)
      = -∫ x in (posHalf v V : Set E), b x := by
    have h1 := hsplitL.add hsplitX
    rw [add_zero] at h1
    have h2 : Tendsto (fun n : ℕ ↦ (∫ x in (posHalf v V : Set E),
        (reflectionCutoff (((n : ℝ) + 1) * ⟪x, v⟫) * a x) • u x)
        + ∫ x in (posHalf v V : Set E), e n x • u x) atTop
        (𝓝 (-∫ x in (posHalf v V : Set E), b x)) := by
      simp only [hLX]
      exact hsplitR.neg
    exact tendsto_nhds_unique h1 h2
  -- fold the integrals over `V` onto `V₊`
  have hmain : ∀ x, ⟪x, v⟫ < 0 → hyperplaneReflection v (hyperplaneReflection v x) = x :=
    fun x _ ↦ hyperplaneReflection_hyperplaneReflection v x
  have hd1 : IntegrableOn (fun x ↦ fderiv ℝ φ x y • u x) (posHalf v V : Set E) :=
    integrableOn_smul_of_memLp hVp (g := fun x ↦ fderiv ℝ φ x y)
      (φ.fderivApply y).contDiff.continuous (φ.fderivApply y).hasCompactSupport hp hup
  have hd2 : IntegrableOn (fun x ↦ fderiv ℝ φ (hyperplaneReflection v x) y • u x)
      (posHalf v V : Set E) :=
    integrableOn_smul_of_memLp hVp (g := fun x ↦ fderiv ℝ φ (hyperplaneReflection v x) y)
      ((φ.fderivApply y).contDiff.continuous.comp (hyperplaneReflection v).continuous)
      ((φ.fderivApply y).hasCompactSupport.comp_homeomorph
        (hyperplaneReflection v).toHomeomorph) hp hup
  have hIL : ∫ x in (V : Set E), fderiv ℝ φ x y • _root_.evenReflection v u x
      = ∫ x in (posHalf v V : Set E), a x • u x := by
    rw [setIntegral_of_reflected hv0 hV (G := fun x ↦ fderiv ℝ φ x y • _root_.evenReflection v u x)
      (A := fun x ↦ fderiv ℝ φ x y • u x)
      (B := fun z ↦ fderiv ℝ φ (hyperplaneReflection v z) y • u z)
      (fun x _ hx ↦ by rw [evenReflection_of_nonneg v hx])
      (fun x _ hx ↦ by rw [evenReflection_of_neg v hx, hmain x hx]) hd1 hd2, ← integral_add hd1 hd2]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [ha, ← add_smul]
  have he1 : IntegrableOn (fun x ↦ φ x • w x y) (posHalf v V : Set E) :=
    integrableOn_smul_of_memLp hVp φ.contDiff.continuous φ.hasCompactSupport hp (hwy y)
  have he2 : IntegrableOn (fun x ↦ φ (hyperplaneReflection v x) • w x (hyperplaneReflection v y))
      (posHalf v V : Set E) :=
    integrableOn_smul_of_memLp hVp (g := fun x ↦ φ (hyperplaneReflection v x))
      (φ.contDiff.continuous.comp (hyperplaneReflection v).continuous)
      (φ.hasCompactSupport.comp_homeomorph (hyperplaneReflection v).toHomeomorph) hp (hwy _)
  have hIR : ∫ x in (V : Set E), φ x • reflectFDeriv v w x y
      = ∫ x in (posHalf v V : Set E), b x := by
    rw [setIntegral_of_reflected hv0 hV (G := fun x ↦ φ x • reflectFDeriv v w x y)
      (A := fun x ↦ φ x • w x y)
      (B := fun z ↦ φ (hyperplaneReflection v z) • w z (hyperplaneReflection v y))
      (fun x _ hx ↦ by rw [reflectFDeriv_of_nonneg v hx])
      (fun x _ hx ↦ by
        rw [reflectFDeriv_of_neg v hx, hmain x hx, ContinuousLinearMap.comp_apply]
        rfl) he1 he2, ← integral_add he1 he2]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [hb]
  rw [hIL, hIR, hlim]

end Identity

/-! ### Lemma 9.2: membership and norms -/

section Membership

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {v : E} {V : Opens E} {p : ℝ≥0∞}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F] in
/-- The even reflection is additive: $(f + g)^\star = f^\star + g^\star$. -/
theorem evenReflection_add (v : E) (f g : E → F) :
    evenReflection v (f + g) = evenReflection v f + evenReflection v g := by
  funext x
  simp only [evenReflection, Pi.add_apply]
  split_ifs <;> rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The even reflection commutes with scalar multiplication: $(c f)^\star = c f^\star$ for
$c \in \mathbb{R}$. -/
theorem evenReflection_smul (v : E) (c : ℝ) (f : E → F) :
    evenReflection v (c • f) = c • evenReflection v f := by
  funext x
  simp only [evenReflection, Pi.smul_apply]
  split_ifs <;> rfl

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The even reflection depends on the function only up to a null set of $V_+$. Let $v \neq 0$ and
$\sigma(V) = V$. If $f = g$ almost everywhere on $V_+$, then $f^\star = g^\star$ almost
everywhere on $V$. -/
theorem evenReflection_congr_ae (hv : v ≠ 0) (hV : hyperplaneReflection v '' (V : Set E) = V)
    {f g : E → F} (h : f =ᵐ[volume.restrict (posHalf v V : Set E)] g) :
    evenReflection v f =ᵐ[volume.restrict (V : Set E)] evenReflection v g := by
  have h1 : ∀ᵐ x ∂volume, x ∈ (posHalf v V : Set E) → f x = g x :=
    (ae_restrict_iff' (posHalf v V).isOpen.measurableSet).1 h
  have h2 : ∀ᵐ x ∂volume, hyperplaneReflection v x ∈ (posHalf v V : Set E) →
      f (hyperplaneReflection v x) = g (hyperplaneReflection v x) :=
    (measurePreserving_hyperplaneReflection v).quasiMeasurePreserving.tendsto_ae.eventually h1
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet, ae_restrict_of_ae (ae_inner_ne_zero hv),
    ae_restrict_of_ae h1, ae_restrict_of_ae h2] with x hxV hx hx1 hx2
  rcases lt_or_gt_of_ne hx with h | h
  · rw [evenReflection_of_neg v h, evenReflection_of_neg v h]
    refine hx2 ⟨(mem_of_image_eq hV).1 hxV, ?_⟩
    change (0 : ℝ) < ⟪hyperplaneReflection v x, v⟫
    rw [inner_hyperplaneReflection]
    linarith
  · rw [evenReflection_of_nonneg v h.le, evenReflection_of_nonneg v h.le]
    exact hx1 ⟨hxV, h⟩

omit [NormedSpace ℝ F] in
/-- **The $L^p$ bound of Lemma 9.2.** Let $v \neq 0$, let $\sigma(V) = V$ and $1 \le p$, and let $u$
be almost everywhere strongly measurable on $V_+$. Then
$$\|u^\star\|_{L^p(V)} \le 2 \|u\|_{L^p(V_+)}.$$
-/
theorem eLpNorm_evenReflection_le (hv : v ≠ 0) (hV : hyperplaneReflection v '' (V : Set E) = V)
    (hp : 1 ≤ p) {u : E → F} (hu : AEStronglyMeasurable u (volume.restrict (posHalf v V : Set E))) :
    eLpNorm (evenReflection v u) p (volume.restrict (V : Set E))
      ≤ 2 * eLpNorm u p (volume.restrict (posHalf v V : Set E)) := by
  rw [two_mul]
  exact eLpNorm_le_of_reflected hv hV (fun x _ hx ↦ evenReflection_of_nonneg v hx)
    (fun x _ hx ↦ evenReflection_of_neg v hx) hp hu

omit [NormedSpace ℝ F] in
/-- Let $v \neq 0$ and $\sigma(V) = V$. If $u$ is almost everywhere strongly measurable on $V_+$,
then $u^\star$ is almost everywhere strongly measurable on $V$. -/
theorem aestronglyMeasurable_evenReflection (hv : v ≠ 0)
    (hV : hyperplaneReflection v '' (V : Set E) = V) {u : E → F}
    (hu : AEStronglyMeasurable u (volume.restrict (posHalf v V : Set E))) :
    AEStronglyMeasurable (evenReflection v u) (volume.restrict (V : Set E)) :=
  aestronglyMeasurable_of_reflected hv hV (fun _ _ hx ↦ evenReflection_of_nonneg v hx)
    (fun _ _ hx ↦ evenReflection_of_neg v hx) hu hu

omit [NormedSpace ℝ F] in
/-- Let $v \neq 0$, let $\sigma(V) = V$ and $1 \le p$. If $u \in L^p(V_+)$, then
$u^\star \in L^p(V)$. -/
theorem MeasureTheory.MemLp.evenReflection (hv : v ≠ 0)
    (hV : hyperplaneReflection v '' (V : Set E) = V)
    (hp : 1 ≤ p) {u : E → F} (hu : MemLp u p (volume.restrict (posHalf v V : Set E))) :
    MemLp (evenReflection v u) p (volume.restrict (V : Set E)) :=
  (eLpNorm_evenReflection_le hv hV hp hu.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofNat_lt_top hu)

/-- Let $v \neq 0$, let $\sigma(V) = V$ and $1 \le p$, and let $w : E \to \mathcal{L}(E, F)$ be
almost everywhere strongly measurable on $V_+$. Then the reflected derivative $\tilde w$ =
`reflectFDeriv v w` satisfies
$$\|\tilde w\|_{L^p(V)} \le 2 \|w\|_{L^p(V_+)}.$$

The reflected derivative has the norm of the even reflection of $w$ (`norm_reflectFDeriv`). -/
theorem eLpNorm_reflectFDeriv_le (hv : v ≠ 0) (hV : hyperplaneReflection v '' (V : Set E) = V)
    (hp : 1 ≤ p) {w : E → E →L[ℝ] F}
    (hw : AEStronglyMeasurable w (volume.restrict (posHalf v V : Set E))) :
    eLpNorm (reflectFDeriv v w) p (volume.restrict (V : Set E))
      ≤ 2 * eLpNorm w p (volume.restrict (posHalf v V : Set E)) := by
  have hwσ : AEStronglyMeasurable
      (fun z ↦ (w z).comp ((hyperplaneReflection v).toContinuousLinearEquiv : E →L[ℝ] E))
      (volume.restrict (posHalf v V : Set E)) :=
    ((ContinuousLinearMap.compL ℝ E E F).flip _).continuous.comp_aestronglyMeasurable hw
  rw [two_mul]
  refine (eLpNorm_le_of_reflected hv hV (fun x _ hx ↦ reflectFDeriv_of_nonneg v hx)
    (fun x _ hx ↦ reflectFDeriv_of_neg v hx) hp hwσ).trans ?_
  gcongr
  exact eLpNorm_mono_ae hwσ (Eventually.of_forall fun z ↦
    (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _).le)

/-- **Lemma 9.2** of [brezis2011functional], membership. Let $v$ be a unit vector, let $V$ be an
open set with $\sigma(V) = V$, and let $1 \le p \le \infty$. If $u \in W^{1,p}(V_+)$, then its
even reflection $u^\star$ lies in $W^{1,p}(V)$.

The bounds of the source are separate results: $\|u^\star\|_{L^p(V)} \le 2 \|u\|_{L^p(V_+)}$ is
`eLpNorm_evenReflection_le`, and the bound of the derivative is `eLpNorm_reflectFDeriv_le`. -/
theorem MemSobolev.evenReflection (hv : ‖v‖ = 1)
    (hV : hyperplaneReflection v '' (V : Set E) = V) (hp : 1 ≤ p) {u : E → F}
    (hu : MemSobolev u 1 p (posHalf v V) volume) :
    MemSobolev (evenReflection v u) 1 p V volume := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  obtain ⟨w, hw, hwp⟩ := hu.exists_hasWeakIteratedFDerivOn (n := 1) le_rfl
  obtain ⟨e, he⟩ : ∃ e : (E [×1]→L[ℝ] F) ≃ₗᵢ[ℝ] (E →L[ℝ] F),
    e = continuousMultilinearCurryFin1 ℝ E F := ⟨_, rfl⟩
  have hw' : HasWeakFDerivOn u (fun x ↦ e (w x)) (posHalf v V) volume := by
    unfold HasWeakFDerivOn
    rw [he]
    simpa using hw
  have hwp' : MemLp (fun x ↦ e (w x)) p (volume.restrict (posHalf v V : Set E)) :=
    e.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hwp
  have hid := hw'.evenReflection hv hV hp hu.memLp hwp'
  have hup : MemLp (_root_.evenReflection v u) p (volume.restrict (V : Set E)) :=
    hu.memLp.evenReflection hv0 hV hp
  have hWp : MemLp (reflectFDeriv v fun x ↦ e (w x)) p (volume.restrict (V : Set E)) :=
    (eLpNorm_reflectFDeriv_le hv0 hV hp hwp'.aestronglyMeasurable).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofNat_lt_top hwp')
  refine ⟨hup, fun n hn ↦ ?_⟩
  have hn' : n ≤ 1 := by exact_mod_cast hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn' with rfl | rfl
  · exact ⟨_, hasWeakIteratedFDerivOn_zero hid.locallyIntegrableOn,
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
        |>.comp_memLp' hup⟩
  · exact ⟨_, hid,
      (continuousMultilinearCurryFin1 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
        |>.comp_memLp' hWp⟩

end Membership

/-! ### Lemma 9.2 on the typed spaces -/

section Typed

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {v : E} {V : Opens E}

omit [CompleteSpace F] in
/-- **Lemma 9.2** of [brezis2011functional] in the multi-index formulation. Let $b$ be a basis of
$E$, let $v$ be a unit vector, let $V$ be an open set with $\sigma(V) = V$, and let
$1 \le p \le \infty$. If $u$ lies in $W^{1,p}(V_+)$ in the sense of `MemSobolevMultiIndex`, then
$u^\star$ lies in $W^{1,p}(V)$ in the same sense. -/
theorem MemSobolevMultiIndex.evenReflection (hv : ‖v‖ = 1)
    (hV : hyperplaneReflection v '' (V : Set E) = V) {u : E → F}
    (hu : MemSobolevMultiIndex b u 1 p (posHalf v V) volume) :
    MemSobolevMultiIndex b (evenReflection v u) 1 p V volume :=
  (hu.memSobolev.evenReflection hv hV Fact.out).memSobolevMultiIndex

namespace SobolevMultiIndex

variable (hv : ‖v‖ = 1) (hV : hyperplaneReflection v '' (V : Set E) = V)
include hv hV

/-- **The extension by reflection of Lemma 9.2 on the typed spaces**, as a function. For a unit
vector $v$ and an open set $V$ with $\sigma(V) = V$, it sends $u \in W^{1,p}(V_+)$ to an element
of $W^{1,p}(V)$ whose function is $u^\star$.

The element is chosen from `MemSobolevMultiIndex.evenReflection`. It is linear and bounded, and
`SobolevMultiIndex.evenReflectionL` is its bundled form. -/
def evenReflection (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    SobolevMultiIndex F b 1 p V volume :=
  ((memSobolevMultiIndex u).evenReflection hv hV).exists_sobolevMultiIndex.choose

/-- The function of `SobolevMultiIndex.evenReflection hv hV u` is $u^\star$ almost everywhere on
$V$. -/
theorem fn_evenReflection (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    fn (evenReflection hv hV u) =ᵐ[volume.restrict (V : Set E)] _root_.evenReflection v (fn u) :=
  ((memSobolevMultiIndex u).evenReflection hv hV).exists_sobolevMultiIndex.choose_spec

/-- On $V_+$, the function of `SobolevMultiIndex.evenReflection hv hV u` is the function of $u$,
almost everywhere. -/
theorem fn_evenReflection_restrict (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    fn (evenReflection hv hV u) =ᵐ[volume.restrict (posHalf v V : Set E)] fn u := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (posHalf_le v V) (fn_evenReflection hv hV u),
    ae_restrict_mem (posHalf v V).isOpen.measurableSet] with x hx hxV
  rw [hx, evenReflection_of_nonneg v (le_of_lt (show (0 : ℝ) < ⟪x, v⟫ from hxV.2))]

/-- The typed reflection is additive: $(u + w)^\star = u^\star + w^\star$ in $W^{1,p}(V)$. -/
theorem evenReflection_add (u w : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    evenReflection hv hV (u + w) = evenReflection hv hV u + evenReflection hv hV w := by
  refine ext_of_fn_ae_eq ((fn_evenReflection hv hV (u + w)).trans (EventuallyEq.trans ?_
    (fn_add _ _).symm))
  refine (evenReflection_congr_ae (ne_zero_of_norm_ne_zero (by rw [hv]; exact one_ne_zero)) hV
    (fn_add u w)).trans ?_
  rw [_root_.evenReflection_add]
  exact ((fn_evenReflection hv hV u).add (fn_evenReflection hv hV w)).symm

/-- The typed reflection commutes with scalar multiplication: $(c u)^\star = c u^\star$ in
$W^{1,p}(V)$ for $c \in \mathbb{R}$. -/
theorem evenReflection_smul (c : ℝ) (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    evenReflection hv hV (c • u) = c • evenReflection hv hV u := by
  refine ext_of_fn_ae_eq ((fn_evenReflection hv hV (c • u)).trans (EventuallyEq.trans ?_
    (fn_smul _ _).symm))
  refine (evenReflection_congr_ae (ne_zero_of_norm_ne_zero (by rw [hv]; exact one_ne_zero)) hV
    (fn_smul c u)).trans ?_
  rw [_root_.evenReflection_smul]
  exact ((fn_evenReflection hv hV u).const_smul c).symm

/-- **The $L^p$ bound of the typed reflection**: for $u \in W^{1,p}(V_+)$,
$\|u^\star\|_{L^p(V)} \le 2 \|u\|_{L^p(V_+)}$. -/
theorem eLpNorm_fn_evenReflection_le (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    eLpNorm (fn (evenReflection hv hV u)) p (volume.restrict (V : Set E))
      ≤ 2 * eLpNorm (fn u) p (volume.restrict (posHalf v V : Set E)) := by
  rw [eLpNorm_congr_ae (fn_evenReflection hv hV u)]
  exact eLpNorm_evenReflection_le (ne_zero_of_norm_ne_zero (by rw [hv]; exact one_ne_zero)) hV
    Fact.out
    (memLp u).aestronglyMeasurable

/-- The partial derivatives of the reflected element. Let $u \in W^{1,p}(V_+)$, and let $w$ be a
weak tensor derivative of $u$ on $V_+$ with $w \in L^p(V_+)$. Let $\tilde w$ be the reflected
derivative `reflectFDeriv v w`. Then for every index $i$,
$$\partial_i (u^\star)(x) = \tilde w(x)(b_i) \qquad \text{for almost every } x \in V.$$
-/
theorem weakDeriv_evenReflection_single (u : SobolevMultiIndex F b 1 p (posHalf v V) volume)
    {w : E → E →L[ℝ] F} (hw : HasWeakFDerivOn (fn u) w (posHalf v V) volume)
    (hwp : MemLp w p (volume.restrict (posHalf v V : Set E))) (i : ι) :
    weakDeriv (evenReflection hv hV u) (MultiIndexLE.single i) =ᵐ[volume.restrict (V : Set E)]
      fun x ↦ reflectFDeriv v w x (b i) := by
  have h1 := (hasWeakIteratedLineDerivOn (evenReflection hv hV u) (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)
  have h2 := (((hw.evenReflection hv hV Fact.out (memLp u) hwp) :
    HasWeakIteratedFDerivOn 1 _ _ V volume).lineDeriv ![b i]).congr_ae
    (fn_evenReflection hv hV u).symm (EventuallyEq.refl _ _)
  filter_upwards [(ae_restrict_iff' V.isOpen.measurableSet).2 (h1.ae_eq h2)] with x hx
  simpa using hx

/-- **The typed reflection is bounded**: there is a constant $C$ with $\|u^\star\|_{W^{1,p}(V)} \le
C \|u\|_{W^{1,p}(V_+)}$ for every $u \in W^{1,p}(V_+)$.

The constant of the proof depends only on the basis. -/
theorem exists_norm_evenReflection_le :
    ∃ C : ℝ, ∀ u : SobolevMultiIndex F b 1 p (posHalf v V) volume,
      ‖evenReflection hv hV u‖ ≤ C * ‖u‖ := by
  have hv0 : v ≠ 0 := ne_zero_of_norm_ne_zero (by rw [hv]; exact one_ne_zero)
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = Fintype.card ι • ‖b.equivFunL.toContinuousLinearMap‖ :=
    ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = ∑ i, ‖b i‖ := ⟨_, rfl⟩
  have hMb0 : 0 ≤ Mb := by rw [hMb]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞, B = ENNReal.ofReal Mb * (2 * ENNReal.ofReal Cb) := ⟨_, rfl⟩
  have hB' : B ≠ ⊤ := by
    rw [hB]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)
  refine ⟨_, fun u ↦ norm_le_mul_norm_of_eLpNorm_le (evenReflection hv hV u) u
    ENNReal.ofNat_ne_top hB' (eLpNorm_fn_evenReflection_le hv hV u) fun i ↦ ?_⟩
  obtain ⟨w, hw, hwp, -, hwn⟩ := exists_hasWeakFDerivOn_fn u
  rw [← hCb] at hwn
  have h1 : eLpNorm (weakDeriv (evenReflection hv hV u) (MultiIndexLE.single i)) p
      (volume.restrict (V : Set E))
      ≤ ENNReal.ofReal Mb * eLpNorm (reflectFDeriv v w) p (volume.restrict (V : Set E)) := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Lp.memLp _).aestronglyMeasurable ?_ p
    filter_upwards [weakDeriv_evenReflection_single hv hV u hw hwp i] with x hx
    rw [hx, hMb]
    calc ‖reflectFDeriv v w x (b i)‖ ≤ ‖reflectFDeriv v w x‖ * ‖b i‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖reflectFDeriv v w x‖ * ∑ j, ‖b j‖ := by
          gcongr
          exact Finset.single_le_sum (f := fun j ↦ ‖b j‖) (fun _ _ ↦ norm_nonneg _)
            (Finset.mem_univ i)
      _ = (∑ j, ‖b j‖) * ‖reflectFDeriv v w x‖ := mul_comm _ _
  calc eLpNorm (weakDeriv (evenReflection hv hV u) (MultiIndexLE.single i)) p
        (volume.restrict (V : Set E))
      ≤ ENNReal.ofReal Mb * (2 * (ENNReal.ofReal Cb
        * ∑ j, eLpNorm (weakDeriv u (MultiIndexLE.single j)) p
          (volume.restrict (posHalf v V : Set E)))) := by
        refine h1.trans ?_
        gcongr
        exact (eLpNorm_reflectFDeriv_le hv0 hV Fact.out hwp.aestronglyMeasurable).trans
          (by gcongr)
    _ = B * ∑ j, eLpNorm (weakDeriv u (MultiIndexLE.single j)) p
          (volume.restrict (posHalf v V : Set E)) := by
        rw [hB]; ring

variable (F b p) in
/-- The reflection $u \mapsto u^\star$ as a linear map $W^{1,p}(V_+) \to W^{1,p}(V)$. -/
def evenReflectionₗ :
    SobolevMultiIndex F b 1 p (posHalf v V) volume →ₗ[ℝ] SobolevMultiIndex F b 1 p V volume where
  toFun := evenReflection hv hV
  map_add' := evenReflection_add hv hV
  map_smul' := evenReflection_smul hv hV

variable (F b p) in
/-- **Lemma 9.2** of [brezis2011functional] **as a bounded linear map**
$W^{1,p}(V_+) \to W^{1,p}(V)$, $u \mapsto u^\star$, for a unit vector $v$ and an open set $V$
with $\sigma(V) = V$. Its function is $u^\star$ (`SobolevMultiIndex.fn_evenReflectionL`), it
restricts to $u$ on $V_+$ (`SobolevMultiIndex.fn_evenReflectionL_restrict`), and its $L^p$ norm
is at most $2 \|u\|_{L^p(V_+)}$ (`SobolevMultiIndex.eLpNorm_fn_evenReflectionL_le`).

With $V = Q$ and $v = e_N$ it is the step $v_i \mapsto v_i^\star$ of the proof of the extension
theorem. With $V = E$ it is the extension operator of the half space. -/
def evenReflectionL :
    SobolevMultiIndex F b 1 p (posHalf v V) volume →L[ℝ] SobolevMultiIndex F b 1 p V volume :=
  (evenReflectionₗ F b p hv hV).mkContinuousOfExistsBound (exists_norm_evenReflection_le hv hV)

/-- The bundled map `SobolevMultiIndex.evenReflectionL` agrees with
`SobolevMultiIndex.evenReflection`. -/
@[simp]
theorem evenReflectionL_apply (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    evenReflectionL F b p hv hV u = evenReflection hv hV u :=
  rfl

/-- The function of `SobolevMultiIndex.evenReflectionL F b p hv hV u` is $u^\star$ almost everywhere
on $V$. -/
theorem fn_evenReflectionL (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    fn (evenReflectionL F b p hv hV u) =ᵐ[volume.restrict (V : Set E)]
      _root_.evenReflection v (fn u) :=
  fn_evenReflection hv hV u

/-- On $V_+$, the function of `SobolevMultiIndex.evenReflectionL F b p hv hV u` is the function of
$u$, almost everywhere. -/
theorem fn_evenReflectionL_restrict (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    fn (evenReflectionL F b p hv hV u) =ᵐ[volume.restrict (posHalf v V : Set E)] fn u :=
  fn_evenReflection_restrict hv hV u

/-- The $L^p$ bound of `SobolevMultiIndex.evenReflectionL`: the $L^p(V)$ norm of the function of the
image of $u$ is at most $2 \|u\|_{L^p(V_+)}$. -/
theorem eLpNorm_fn_evenReflectionL_le (u : SobolevMultiIndex F b 1 p (posHalf v V) volume) :
    eLpNorm (fn (evenReflectionL F b p hv hV u)) p (volume.restrict (V : Set E))
      ≤ 2 * eLpNorm (fn u) p (volume.restrict (posHalf v V : Set E)) :=
  eLpNorm_fn_evenReflection_le hv hV u

end SobolevMultiIndex

end Typed

section Euclidean

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {v : EuclideanSpace ℝ (Fin N)}
  {V : Opens (EuclideanSpace ℝ (Fin N))}

/-- **Lemma 9.2** of [brezis2011functional] **on $W^{1,p}$ of an open subset of $\mathbb{R}^N$**, as
a bounded linear map $W^{1,p}(V_+) \to W^{1,p}(V)$, $u \mapsto u^\star$, for $\|v\| = 1$ and
$\sigma(V) = V$.

It is `SobolevMultiIndex.evenReflectionL` on `SobolevEuclidean N 1 p V₊`. Its function, its
restriction to $V_+$ and its $L^p$ bound are given by `SobolevMultiIndex.fn_evenReflectionL`,
`SobolevMultiIndex.fn_evenReflectionL_restrict` and
`SobolevMultiIndex.eLpNorm_fn_evenReflectionL_le`. With $V = Q$ and $v = e_N$ it is the step
$v_i \mapsto v_i^\star$ of the proof of Theorem 9.7. With $V = \mathbb{R}^N$ it is the extension
operator of the half space. -/
noncomputable abbrev SobolevEuclidean.evenReflectionL (hv : ‖v‖ = 1)
    (hV : hyperplaneReflection v '' (V : Set (EuclideanSpace ℝ (Fin N))) = V) :
    SobolevEuclidean N 1 p (posHalf v V) →L[ℝ] SobolevEuclidean N 1 p V :=
  SobolevMultiIndex.evenReflectionL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p hv hV

end Euclidean

/-! ### The half space: Theorem 9.7 and Corollary 9.8 for $\Omega = \mathbb{R}^N_+$ -/

section HalfSpace

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

open EuclideanSpace

/-- The last basis vector $e_N$ of $\mathbb{R}^{d+1}$ is a unit vector. -/
theorem EuclideanSpace.norm_single_last_one :
    ‖(single (Fin.last d) (1 : ℝ) : EuclideanSpace ℝ (Fin (d + 1)))‖ = 1 := by
  simp

/-- The inner product of $x \in \mathbb{R}^{d+1}$ with the last basis vector is the last coordinate:
$\langle x, e_N \rangle = x_N$. -/
theorem EuclideanSpace.inner_single_last_one (x : EuclideanSpace ℝ (Fin (d + 1))) :
    ⟪x, single (Fin.last d) (1 : ℝ)⟫ = x (Fin.last d) := by
  rw [EuclideanSpace.inner_single_right]
  simp

/-- The whole space is invariant under every reflection: $\sigma(E) = E$. -/
theorem hyperplaneReflection_image_top {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) : hyperplaneReflection v '' ((⊤ : Opens E) : Set E) = ((⊤ : Opens E) : Set E) := by
  rw [Opens.coe_top, Set.image_univ, (hyperplaneReflection v).surjective.range_eq]

/-- For $v = e_N$, the positive half of the whole space $\mathbb{R}^{d+1}$ is the upper half space
$\mathbb{R}^N_+$. -/
theorem coe_posHalf_top_eq_upperHalfSpace :
    (posHalf (single (Fin.last d) (1 : ℝ)) (⊤ : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
      Set (EuclideanSpace ℝ (Fin (d + 1)))) = upperHalfSpace d := by
  ext x
  simp [coe_posHalf, upperHalfSpace, EuclideanSpace.inner_single_last_one]

/-- For $v = e_N$, the positive half of the whole space $\mathbb{R}^{d+1}$ is the upper half space
$\mathbb{R}^N_+$, as an equality of open sets. -/
theorem posHalf_top_eq_upperHalfSpaceOpens :
    posHalf (single (Fin.last d) (1 : ℝ)) (⊤ : Opens (EuclideanSpace ℝ (Fin (d + 1))))
      = upperHalfSpaceOpens d :=
  Opens.ext coe_posHalf_top_eq_upperHalfSpace

/-- If $f = g$ almost everywhere for $\mu$ restricted to $s$, and $s = t$, then $f = g$ almost
everywhere for $\mu$ restricted to $t$.

The statement is about plain functions, so that rewriting never touches a dependent type. -/
theorem Filter.EventuallyEq.of_restrict_eq {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} {f g : α → β} (h : f =ᵐ[μ.restrict s] g) (hst : s = t) : f =ᵐ[μ.restrict t] g :=
  hst ▸ h

/-- If $s = t$, then the $L^p$ norms of $f$ for $\mu$ restricted to $s$ and for $\mu$ restricted to
$t$ are equal.

The statement is about plain functions, so that rewriting never touches a dependent type. -/
theorem eLpNorm_restrict_congr_set_eq {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β]
    {μ : Measure α} {s t : Set α} (f : α → β) (p : ℝ≥0∞) (hst : s = t) :
    eLpNorm f p (μ.restrict s) = eLpNorm f p (μ.restrict t) :=
  hst ▸ rfl

/-- The assembly of the extension operator of the half space from a restriction $R$ and a reflection
$T$. Let $V$ be an open set equal to $\mathbb{R}^N_+$, and let
$R : W^{1,p}(\mathbb{R}^N_+) \to W^{1,p}(V)$, $T : W^{1,p}(V) \to W^{1,p}(\mathbb{R}^N)$ and $P
: W^{1,p}(\mathbb{R}^N_+) \to W^{1,p}(\mathbb{R}^N)$ be bounded linear maps with $Pu = T(Ru)$.
Assume that $Ru = u$ and $Tw = w$ almost everywhere on $V$, and that $\|Tw\|_{L^p(\mathbb{R}^N)}
\le 2 \|w\|_{L^p(V)}$. Then there is a constant $C$ such that for every
$u \in W^{1,p}(\mathbb{R}^N_+)$, $Pu = u$ almost everywhere on $\mathbb{R}^N_+$,
$\|Pu\|_{L^p(\mathbb{R}^N)} \le C \|u\|_{L^p(\mathbb{R}^N_+)}$ and
$\|Pu\|_{W^{1,p}(\mathbb{R}^N)} \le C \|u\|_{W^{1,p}(\mathbb{R}^N_+)}$.

The operators are variables because the elaboration of the composite is expensive when the
operators are concrete, and cheap when they are not. -/
theorem SobolevEuclidean.exists_extensionL_upperHalfSpace_of_ops
    {V : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hset : (V : Set (EuclideanSpace ℝ (Fin (d + 1)))) = upperHalfSpace d)
    (R : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d) →L[ℝ] SobolevEuclidean (d + 1) 1 p V)
    (T : SobolevEuclidean (d + 1) 1 p V →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤)
    (P : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d) →L[ℝ] SobolevEuclidean (d + 1) 1 p ⊤)
    (hP : ∀ u, P u = T (R u))
    (hRfn : ∀ u, SobolevMultiIndex.fn (R u) =ᵐ[volume.restrict (V : Set _)] SobolevMultiIndex.fn u)
    (hTfn : ∀ w, SobolevMultiIndex.fn (T w) =ᵐ[volume.restrict (V : Set _)] SobolevMultiIndex.fn w)
    (hTLp : ∀ w, eLpNorm (SobolevMultiIndex.fn (T w)) p
      (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (d + 1)))) : Set _))
      ≤ 2 * eLpNorm (SobolevMultiIndex.fn w) p (volume.restrict (V : Set _))) :
    ∃ C : ℝ, ∀ u : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d),
      SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (upperHalfSpace d)] SobolevMultiIndex.fn u ∧
      eLpNorm (SobolevMultiIndex.fn (P u)) p volume
        ≤ ENNReal.ofReal C * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (upperHalfSpace d))
      ∧ ‖P u‖ ≤ C * ‖u‖ := by
  refine ⟨max 2 ‖P‖, fun u ↦ ⟨?_, ?_, ?_⟩⟩
  · rw [hP u]
    exact ((hTfn (R u)).trans (hRfn u)).of_restrict_eq hset
  · rw [hP u]
    calc eLpNorm (SobolevMultiIndex.fn (T (R u))) p volume
        = eLpNorm (SobolevMultiIndex.fn (T (R u))) p
          (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (d + 1)))) : Set _)) :=
          (eLpNorm_restrict_coe_top _ _).symm
      _ ≤ 2 * eLpNorm (SobolevMultiIndex.fn (R u)) p (volume.restrict (V : Set _)) := hTLp (R u)
      _ = 2 * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (V : Set _)) := by
          rw [eLpNorm_congr_ae (hRfn u)]
      _ = 2 * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (upperHalfSpace d)) := by
          rw [eLpNorm_restrict_congr_set_eq _ _ hset]
      _ ≤ ENNReal.ofReal (max 2 ‖P‖)
          * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (upperHalfSpace d)) := by
          gcongr
          exact (ENNReal.ofReal_ofNat 2).symm.le.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- **The half-space extension theorem with the normal direction as a parameter.** Let
$1 \le p \le \infty$, and let $v \in \mathbb{R}^{d+1}$ be a unit vector whose positive half
$\{x : \langle x, v \rangle > 0\}$ of the whole space is the upper half space $\mathbb{R}^N_+$,
where $N = d + 1$. Then there are a bounded linear operator $P : W^{1,p}(\mathbb{R}^N_+) \to
W^{1,p}(\mathbb{R}^N)$ and a constant $C$ such that for every $u \in W^{1,p}(\mathbb{R}^N_+)$,
$$Pu = u \text{ a.e. on } \mathbb{R}^N_+, \qquad \|Pu\|_{L^p(\mathbb{R}^N)} \le C
  \|u\|_{L^p(\mathbb{R}^N_+)}, \qquad \|Pu\|_{W^{1,p}(\mathbb{R}^N)} \le C
  \|u\|_{W^{1,p}(\mathbb{R}^N_+)}.$$
This is Theorem 9.7 of [brezis2011functional] for the half space.

The case $v = e_N$ is `SobolevEuclidean.exists_extensionL_upperHalfSpace`. The operator is the
restriction to the positive half of $v$, followed by the even reflection
`SobolevEuclidean.evenReflectionL` across $v^\perp$ with $V = \mathbb{R}^N$. -/
theorem SobolevEuclidean.exists_extensionL_of_posHalf_top_eq {v : EuclideanSpace ℝ (Fin (d + 1))}
    (hv : ‖v‖ = 1)
    (hset : (posHalf v (⊤ : Opens (EuclideanSpace ℝ (Fin (d + 1)))) :
      Set (EuclideanSpace ℝ (Fin (d + 1)))) = upperHalfSpace d) :
    ∃ (P : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d) →L[ℝ]
        SobolevEuclidean (d + 1) 1 p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d),
        SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (upperHalfSpace d)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C
            * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (upperHalfSpace d))
        ∧ ‖P u‖ ≤ C * ‖u‖ := by
  have hV := hyperplaneReflection_image_top v
  have hle : posHalf v ⊤ ≤ upperHalfSpaceOpens d := by
    intro x hx
    rw [← SetLike.mem_coe, coe_upperHalfSpaceOpens, ← hset]
    exact hx
  exact ⟨SobolevEuclidean.evenReflectionL hv hV ∘L
      SobolevMultiIndex.restrictL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p
        volume hle,
    SobolevEuclidean.exists_extensionL_upperHalfSpace_of_ops hset
    (SobolevMultiIndex.restrictL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p volume
      hle) (SobolevEuclidean.evenReflectionL hv hV) _ (fun u ↦ rfl)
    (fun u ↦ SobolevMultiIndex.fn_restrictL _ _)
    (fun w ↦ SobolevMultiIndex.fn_evenReflectionL_restrict hv hV w)
    (fun w ↦ SobolevMultiIndex.eLpNorm_fn_evenReflectionL_le hv hV w)⟩

/-- **Theorem 9.7** of [brezis2011functional] **for the half space**. Let $1 \le p \le \infty$.
There are a bounded linear extension operator $P : W^{1,p}(\mathbb{R}^N_+) \to
W^{1,p}(\mathbb{R}^N)$ and a constant $C$ such that for every $u \in W^{1,p}(\mathbb{R}^N_+)$,
$$Pu = u \text{ a.e. on } \mathbb{R}^N_+, \qquad \|Pu\|_{L^p(\mathbb{R}^N)} \le C
  \|u\|_{L^p(\mathbb{R}^N_+)}, \qquad \|Pu\|_{W^{1,p}(\mathbb{R}^N)} \le C
  \|u\|_{W^{1,p}(\mathbb{R}^N_+)}.$$

The source states this case in §9.2: "This establishes Theorem 9.7 for
$\Omega = \mathbb{R}^N_+$". The operator is the even reflection
`SobolevEuclidean.evenReflectionL` across $x_N = 0$ with $V = \mathbb{R}^N$, whose $L^p$
constant is $2$. The statement has the shape of the extension theorem
`SobolevEuclidean.exists_extensionL` for a $C^1$ domain, so that the two cases are used in the
same way. -/
theorem SobolevEuclidean.exists_extensionL_upperHalfSpace :
    ∃ (P : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d) →L[ℝ]
        SobolevEuclidean (d + 1) 1 p ⊤) (C : ℝ),
      ∀ u : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d),
        SobolevMultiIndex.fn (P u) =ᵐ[volume.restrict (upperHalfSpace d)] SobolevMultiIndex.fn u ∧
        eLpNorm (SobolevMultiIndex.fn (P u)) p volume
          ≤ ENNReal.ofReal C
            * eLpNorm (SobolevMultiIndex.fn u) p (volume.restrict (upperHalfSpace d))
        ∧ ‖P u‖ ≤ C * ‖u‖ :=
  SobolevEuclidean.exists_extensionL_of_posHalf_top_eq EuclideanSpace.norm_single_last_one
    coe_posHalf_top_eq_upperHalfSpace

/-- **The half space is a $W^{1,p}$-extension domain** for every $1 \le p \le \infty$: there is a
bounded linear operator $P : W^{1,p}(\mathbb{R}^N_+) \to W^{1,p}(\mathbb{R}^N)$ with $Pu = u$
almost everywhere on $\mathbb{R}^N_+$.

This is the predicate `IsSobolevExtensionDomain`, obtained from
`SobolevEuclidean.exists_extensionL_upperHalfSpace`. It lets the embedding and compactness
theorems on a domain be read on $\mathbb{R}^N_+$ without the general extension theorem. -/
theorem IsSobolevExtensionDomain.upperHalfSpace :
    IsSobolevExtensionDomain (d + 1) p (upperHalfSpaceOpens d) := by
  obtain ⟨P, C, hP⟩ := SobolevEuclidean.exists_extensionL_upperHalfSpace (d := d) (p := p)
  exact ⟨P.comp (Submodule.subtypeL _), fun u ↦ (hP u).1⟩

/-- **Corollary 9.8** of [brezis2011functional] **on the half space**. Let $1 \le p < \infty$ and
$u \in W^{1,p}(\mathbb{R}^N_+)$. Then there are smooth functions $v_n$ with compact support on
$\mathbb{R}^N$ and elements $w_n \in W^{1,p}(\mathbb{R}^N_+)$ with $w_n = v_n$ almost everywhere
on $\mathbb{R}^N_+$, such that $w_n \to u$ in $W^{1,p}(\mathbb{R}^N_+)$.

So $u$ is the limit in $W^{1,p}(\mathbb{R}^N_+)$ of restrictions of functions of
$C_c^\infty(\mathbb{R}^N)$. The proof applies the abstract density result
`SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn` to the
extension by reflection. -/
theorem SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_upperHalfSpace (hp' : p ≠ ⊤)
    (u : SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d)) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ, (∀ n, ContDiff ℝ ∞ (v n)) ∧
      (∀ n, HasCompactSupport (v n)) ∧
        ∃ w : ℕ → SobolevEuclidean (d + 1) 1 p (upperHalfSpaceOpens d),
        (∀ n, SobolevMultiIndex.fn (w n) =ᵐ[volume.restrict (upperHalfSpace d)] v n) ∧
        Tendsto w atTop (𝓝 u) :=
  SobolevEuclidean.exists_seq_contDiff_hasCompactSupport_tendsto_of_hasSobolevExtensionOn hp'
    IsSobolevExtensionDomain.upperHalfSpace ⟨u, Submodule.mem_top⟩

end HalfSpace

/-! ### Lemma 9.9: the trace inequality on the half space -/

section Trace

/-- **Young's inequality** in the form
$$P a^{P-1} b \le (P - 1) a^P + b^P \qquad \text{for } P > 1 \text{ and } a, b \ge 0.$$
-/
theorem Real.mul_rpow_sub_one_mul_le {P : ℝ} (hP : 1 < P) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    P * (a ^ (P - 1) * b) ≤ (P - 1) * a ^ P + b ^ P := by
  have hpq := Real.HolderConjugate.conjExponent hP
  have h := Real.young_inequality_of_nonneg hb (Real.rpow_nonneg ha (P - 1)) hpq
  rw [← Real.rpow_mul ha, hpq.sub_one_mul_conj] at h
  have hQ : 0 < Real.conjExponent P := hpq.symm.pos
  have e : P / Real.conjExponent P = P - 1 := hpq.div_conj_eq_sub_one
  calc P * (a ^ (P - 1) * b) = P * (b * a ^ (P - 1)) := by ring
    _ ≤ P * (b ^ P / P + a ^ P / Real.conjExponent P) := by gcongr
    _ = b ^ P + (P / Real.conjExponent P) * a ^ P := by field_simp
    _ = (P - 1) * a ^ P + b ^ P := by rw [e]; ring

/-- **The one-dimensional trace inequality.** Let $v : \mathbb{R} \to \mathbb{R}$ be of class $C^1$
with continuous derivative $v'$, let $v(t) = 0$ for all $t \ge T$, and let $1 \le P < \infty$.
Then
$$|v(0)|^P \le \int_0^\infty \big((P - 1) |v(t)|^P + |v'(t)|^P\big) \, dt.$$

The proof starts from $G(v(0)) = -\int_0^\infty (G \circ v)'$ with $G(t) = |t|^P$ (for $P = 1$,
from $v(0) = -\int_0^\infty v'$), and uses Young's inequality
$P |v|^{P-1} |v'| \le (P - 1) |v|^P + |v'|^P$. This is the step on one line in the proof of
Lemma 9.9 of [brezis2011functional], Comments on Chapter 9, 7. The integral is a lower Lebesgue
integral of extended nonnegative reals. -/
theorem enorm_rpow_le_lintegral_Ioi_of_hasDerivAt {v v' : ℝ → ℝ} (hv : ContDiff ℝ 1 v)
    (hv' : ∀ t, HasDerivAt v (v' t) t) (hv'c : Continuous v') {T : ℝ}
    (hT : ∀ t, T ≤ t → v t = 0) {P : ℝ} (hP : 1 ≤ P) :
    ‖v 0‖ₑ ^ P ≤ ∫⁻ t in Ioi (0 : ℝ),
      (ENNReal.ofReal (P - 1) * ‖v t‖ₑ ^ P + ‖v' t‖ₑ ^ P) := by
  -- a point beyond the support, on the right of `0`
  obtain ⟨T', hT'0, hT'⟩ : ∃ T' : ℝ, 0 ≤ T' ∧ v T' = 0 :=
    ⟨max T 0, le_max_right _ _, hT _ (le_max_left _ _)⟩
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  rcases hP.eq_or_lt with rfl | hP1
  · -- `P = 1`: the fundamental theorem of calculus for `v` itself
    have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hv' t)
      (hv'c.intervalIntegrable 0 T')
    rw [hT', zero_sub] at hfund
    simp only [ENNReal.rpow_one, sub_self, ENNReal.ofReal_zero, zero_mul, zero_add]
    calc ‖v 0‖ₑ = ‖∫ t in Ioc 0 T', v' t‖ₑ := by
          rw [← intervalIntegral.integral_of_le hT'0, hfund, enorm_neg]
      _ ≤ ∫⁻ t in Ioc 0 T', ‖v' t‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t in Ioi 0, ‖v' t‖ₑ := lintegral_mono_set Ioc_subset_Ioi_self
  · -- `P > 1`: the fundamental theorem of calculus for `|v|^P`
    set Φ : ℝ → ℝ := fun t ↦ ‖v t‖ ^ P with hΦdef
    have hΦ : ContDiff ℝ 1 Φ := (contDiff_norm_rpow hP1).comp hv
    have hΦd : ∀ t, HasDerivAt Φ (P * ‖v t‖ ^ (P - 2) * v t * v' t) t := fun t ↦
      (hasDerivAt_norm_rpow (v t) hP1).comp t (hv' t)
    have hΦ' : ∀ t, deriv Φ t = P * ‖v t‖ ^ (P - 2) * v t * v' t := fun t ↦ (hΦd t).deriv
    have hΦc : Continuous (deriv Φ) := hΦ.continuous_deriv le_rfl
    have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ (hΦ.differentiable one_ne_zero t).hasDerivAt) (hΦc.intervalIntegrable 0 T')
    have hΦT : Φ T' = 0 := by simp [hΦdef, hT', Real.zero_rpow hP0.ne']
    rw [hΦT, zero_sub] at hfund
    -- the pointwise bound on the derivative
    have hpt : ∀ t, ‖deriv Φ t‖ₑ
        ≤ ENNReal.ofReal (P - 1) * ‖v t‖ₑ ^ P + ‖v' t‖ₑ ^ P := by
      intro t
      have h1 : ‖deriv Φ t‖ ≤ P * (‖v t‖ ^ (P - 1) * ‖v' t‖) := by
        rw [hΦ' t]
        rcases eq_or_ne (v t) 0 with h0 | h0
        · simp [h0, Real.zero_rpow (by linarith : P - 1 ≠ 0)]
        · have hpos : 0 < ‖v t‖ := norm_pos_iff.2 h0
          rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs P, abs_of_pos hP0,
            Real.norm_eq_abs (‖v t‖ ^ (P - 2)), abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
          have e : ‖v t‖ ^ (P - 2) * ‖v t‖ = ‖v t‖ ^ (P - 1) := by
            rw [← Real.rpow_add_one hpos.ne']
            ring_nf
          rw [mul_assoc, mul_assoc, ← mul_assoc (‖v t‖ ^ (P - 2)), e]
      calc ‖deriv Φ t‖ₑ = ENNReal.ofReal ‖deriv Φ t‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal ((P - 1) * ‖v t‖ ^ P + ‖v' t‖ ^ P) :=
          ENNReal.ofReal_le_ofReal (h1.trans
            (Real.mul_rpow_sub_one_mul_le hP1 (norm_nonneg _) (norm_nonneg _)))
        _ = ENNReal.ofReal (P - 1) * ‖v t‖ₑ ^ P + ‖v' t‖ₑ ^ P := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by linarith),
            ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hP0.le,
            ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hP0.le, ofReal_norm, ofReal_norm]
    calc ‖v 0‖ₑ ^ P = ‖Φ 0‖ₑ := by
          simp only [hΦdef]
          rw [← ofReal_norm (‖v 0‖ ^ P), Real.norm_eq_abs (‖v 0‖ ^ P),
            abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
            ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hP0.le, ofReal_norm]
      _ = ‖∫ t in Ioc 0 T', deriv Φ t‖ₑ := by
          rw [← intervalIntegral.integral_of_le hT'0, hfund, enorm_neg]
      _ ≤ ∫⁻ t in Ioc 0 T', ‖deriv Φ t‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t in Ioi 0, ‖deriv Φ t‖ₑ := lintegral_mono_set Ioc_subset_Ioi_self
      _ ≤ ∫⁻ t in Ioi 0, (ENNReal.ofReal (P - 1) * ‖v t‖ₑ ^ P + ‖v' t‖ₑ ^ P) :=
          lintegral_mono hpt

variable {d : ℕ} {p : ℝ≥0∞}

/-- The upper half space in the splitting by the last coordinate: $(x', t) \in \mathbb{R}^{d+1}_+$
if and only if $t > 0$. -/
theorem EuclideanSpace.snocLast_mem_upperHalfSpace_iff {x' : EuclideanSpace ℝ (Fin d)} {t : ℝ} :
    EuclideanSpace.snocLast x' t ∈ EuclideanSpace.upperHalfSpace d ↔ 0 < t := by
  simp [EuclideanSpace.mem_upperHalfSpace]

/-- Fubini's theorem along the last coordinate on the upper half space. For an almost everywhere
measurable function $f : \mathbb{R}^{d+1} \to [0, \infty]$,
$$\int_{\mathbb{R}^{d+1}_+} f = \int_{\mathbb{R}^d} \int_0^\infty f(x', t) \, dt \, dx'.$$
-/
theorem EuclideanSpace.lintegral_upperHalfSpace_lastInit (f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ≥0∞)
    (hf : AEMeasurable f) :
    ∫⁻ x in EuclideanSpace.upperHalfSpace d, f x
      = ∫⁻ x', ∫⁻ t in Ioi (0 : ℝ), f (EuclideanSpace.snocLast x' t) := by
  have hm : MeasurableSet (EuclideanSpace.upperHalfSpace d) :=
    EuclideanSpace.isOpen_upperHalfSpace.measurableSet
  rw [← lintegral_indicator hm, EuclideanSpace.lintegral_lastInit _ (hf.indicator hm)]
  refine lintegral_congr fun x' ↦ ?_
  rw [← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun t ↦ ?_
  by_cases ht : 0 < t
  · rw [Set.indicator_of_mem (Set.mem_Ioi.2 ht),
      Set.indicator_of_mem (EuclideanSpace.snocLast_mem_upperHalfSpace_iff.2 ht)]
  · rw [Set.indicator_of_notMem (mt Set.mem_Ioi.1 ht),
      Set.indicator_of_notMem (mt EuclideanSpace.snocLast_mem_upperHalfSpace_iff.1 ht)]

/-- **Lemma 9.9** of [brezis2011functional], Comments on Chapter 9, 7, the form with $p$-th powers.
Let $1 \le p < \infty$, and let $u : \mathbb{R}^{d+1} \to \mathbb{R}$ be of class $C^1$ with
compact support. Then
$$\int_{\mathbb{R}^d} |u(x', 0)|^p \, dx' \le (p - 1) \int_{\mathbb{R}^N_+} |u|^p +
  \int_{\mathbb{R}^N_+} |\partial_N u|^p,$$
where $N = d + 1$ and $\partial_N u(x) = Du(x) e_N$.

The proof applies `enorm_rpow_le_lintegral_Ioi_of_hasDerivAt` on each line $x' + t e_N$, and
integrates in $x'$ by Fubini's theorem (`EuclideanSpace.lintegral_upperHalfSpace_lastInit`). -/
theorem lintegral_enorm_lastZero_rpow_le_of_contDiff (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    ∫⁻ x' : EuclideanSpace ℝ (Fin d), ‖u (EuclideanSpace.snocLast x' 0)‖ₑ ^ p.toReal
      ≤ ENNReal.ofReal (p.toReal - 1)
          * (∫⁻ x in EuclideanSpace.upperHalfSpace d, ‖u x‖ₑ ^ p.toReal)
        + ∫⁻ x in EuclideanSpace.upperHalfSpace d,
            ‖fderiv ℝ u x (EuclideanSpace.single (Fin.last d) 1)‖ₑ ^ p.toReal := by
  set e : EuclideanSpace ℝ (Fin (d + 1)) := EuclideanSpace.single (Fin.last d) 1 with hedef
  set g : EuclideanSpace ℝ (Fin (d + 1)) → ℝ := fun x ↦ fderiv ℝ u x e with hgdef
  have hP1 : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp' hp
  have huc' : Continuous u := hu.continuous
  have hgc : Continuous g := (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- `u` vanishes beyond a radius `R`
  obtain ⟨R, -, hR⟩ := huc.exists_pos_le_norm
  -- the lines `t ↦ u (x', t)`
  have hline : ∀ x' : EuclideanSpace ℝ (Fin d),
      ContDiff ℝ 1 fun t : ℝ ↦ u (EuclideanSpace.snocLast x' t) := fun x' ↦
    hu.comp ((EuclideanSpace.lastInitL d).symm.contDiff.comp
      (contDiff_id.prodMk contDiff_const))
  have hderiv : ∀ (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ),
      HasDerivAt (fun s ↦ u (EuclideanSpace.snocLast x' s))
        (g (EuclideanSpace.snocLast x' t)) t := by
    intro x' t
    have h1 : HasDerivAt (fun s : ℝ ↦ EuclideanSpace.snocLast x' s) e t := by
      have h := ((EuclideanSpace.lastInitL d).symm.hasFDerivAt (x := (t, x'))).comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t x'))
      refine h.congr_deriv ?_
      ext i
      induction i using Fin.lastCases <;> simp [hedef, EuclideanSpace.snocLast, Fin.snoc,
        Fin.castSucc_ne_last]
    have h2 := (hu.differentiable one_ne_zero (EuclideanSpace.snocLast x' t)).hasFDerivAt
    exact h2.comp_hasDerivAt t h1
  have hvanish : ∀ (x' : EuclideanSpace ℝ (Fin d)) (t : ℝ), R ≤ t →
      u (EuclideanSpace.snocLast x' t) = 0 := fun x' t ht ↦ by
    refine hR _ (ht.trans ?_)
    calc t ≤ ‖t‖ := (le_abs_self t).trans_eq (Real.norm_eq_abs t).symm
      _ = ‖EuclideanSpace.snocLast x' t (Fin.last d)‖ := by simp
      _ ≤ ‖EuclideanSpace.snocLast x' t‖ := PiLp.norm_apply_le _ _
  -- the one-dimensional inequality on each line
  have hpt : ∀ x' : EuclideanSpace ℝ (Fin d),
      ‖u (EuclideanSpace.snocLast x' 0)‖ₑ ^ p.toReal
        ≤ ∫⁻ t in Ioi (0 : ℝ), (ENNReal.ofReal (p.toReal - 1)
            * ‖u (EuclideanSpace.snocLast x' t)‖ₑ ^ p.toReal
          + ‖g (EuclideanSpace.snocLast x' t)‖ₑ ^ p.toReal) := fun x' ↦
    enorm_rpow_le_lintegral_Ioi_of_hasDerivAt (hline x') (hderiv x')
      (hgc.comp (EuclideanSpace.continuous_snocLast.comp (Continuous.prodMk_right x')))
      (hvanish x') hP1
  -- Fubini
  have hum : AEMeasurable fun x ↦ ‖u x‖ₑ ^ p.toReal :=
    (huc'.measurable.enorm.pow_const _).aemeasurable
  have hgm : AEMeasurable fun x ↦ ‖g x‖ₑ ^ p.toReal :=
    (hgc.measurable.enorm.pow_const _).aemeasurable
  calc ∫⁻ x' : EuclideanSpace ℝ (Fin d), ‖u (EuclideanSpace.snocLast x' 0)‖ₑ ^ p.toReal
      ≤ ∫⁻ x', ∫⁻ t in Ioi (0 : ℝ), (ENNReal.ofReal (p.toReal - 1)
          * ‖u (EuclideanSpace.snocLast x' t)‖ₑ ^ p.toReal
          + ‖g (EuclideanSpace.snocLast x' t)‖ₑ ^ p.toReal) := lintegral_mono hpt
    _ = ∫⁻ x in EuclideanSpace.upperHalfSpace d,
          (ENNReal.ofReal (p.toReal - 1) * ‖u x‖ₑ ^ p.toReal + ‖g x‖ₑ ^ p.toReal) :=
        (EuclideanSpace.lintegral_upperHalfSpace_lastInit _
          ((hum.const_mul _).add hgm)).symm
    _ = ENNReal.ofReal (p.toReal - 1) * (∫⁻ x in EuclideanSpace.upperHalfSpace d, ‖u x‖ₑ ^ p.toReal)
          + ∫⁻ x in EuclideanSpace.upperHalfSpace d, ‖g x‖ₑ ^ p.toReal := by
        rw [lintegral_add_left' (hum.const_mul _).restrict, lintegral_const_mul'' _ hum.restrict]

/-- **Lemma 9.9** of [brezis2011functional], Comments on Chapter 9, 7 (the trace inequality on the
half space). Let $1 \le p < \infty$, and let $u : \mathbb{R}^{d+1} \to \mathbb{R}$ be of class
$C^1$ with compact support. Then
$$\Big(\int_{\mathbb{R}^d} |u(x', 0)|^p \, dx'\Big)^{1/p} \le p^{1/p}
  \big(\|u\|_{L^p(\mathbb{R}^N_+)} + \|\partial_N u\|_{L^p(\mathbb{R}^N_+)}\big),$$
where $N = d + 1$ and $\partial_N u(x) = Du(x) e_N$.

So the map $u \mapsto u(\cdot, 0)$ is bounded from $C_c^1(\mathbb{R}^N)$ with the norm of
$W^{1,p}(\mathbb{R}^N_+)$ to $L^p(\mathbb{R}^{N-1})$. The form with $p$-th powers is
`lintegral_enorm_lastZero_rpow_le_of_contDiff`. -/
theorem eLpNorm_lastZero_le_of_contDiff (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {u : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    eLpNorm (fun x' : EuclideanSpace ℝ (Fin d) ↦ u (EuclideanSpace.snocLast x' 0)) p volume
      ≤ ENNReal.ofReal p.toReal ^ (1 / p.toReal)
        * (eLpNorm u p (volume.restrict (EuclideanSpace.upperHalfSpace d))
          + eLpNorm (fun x ↦ fderiv ℝ u x (EuclideanSpace.single (Fin.last d) 1)) p
            (volume.restrict (EuclideanSpace.upperHalfSpace d))) := by
  set g : EuclideanSpace ℝ (Fin (d + 1)) → ℝ :=
    fun x ↦ fderiv ℝ u x (EuclideanSpace.single (Fin.last d) 1) with hgdef
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  have hP1 : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hp' hp
  have huc' : Continuous u := hu.continuous
  have hgc : Continuous g := (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hu0c : Continuous fun x' : EuclideanSpace ℝ (Fin d) ↦ u (EuclideanSpace.snocLast x' 0) :=
    huc'.comp (EuclideanSpace.continuous_snocLast.comp (continuous_id.prodMk continuous_const))
  set S : ℝ≥0∞ := eLpNorm u p (volume.restrict (EuclideanSpace.upperHalfSpace d))
    + eLpNorm g p (volume.restrict (EuclideanSpace.upperHalfSpace d)) with hSdef
  -- the `p`-th powers of the two norms on the half space are the integrals
  have hpow : ∀ f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ, Continuous f →
      (∫⁻ x in EuclideanSpace.upperHalfSpace d, ‖f x‖ₑ ^ p.toReal)
        = eLpNorm f p (volume.restrict (EuclideanSpace.upperHalfSpace d)) ^ p.toReal := by
    intro f hf
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hf.aestronglyMeasurable, ← ENNReal.rpow_mul,
      one_div_mul_cancel hP.ne', ENNReal.rpow_one]
  have hmain := lintegral_enorm_lastZero_rpow_le_of_contDiff hp hp' hu huc
  rw [hpow u huc', hpow g hgc] at hmain
  have hS : ∀ f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      eLpNorm f p (volume.restrict (EuclideanSpace.upperHalfSpace d)) ≤ S →
      eLpNorm f p (volume.restrict (EuclideanSpace.upperHalfSpace d)) ^ p.toReal
        ≤ S ^ p.toReal := fun f hf ↦ ENNReal.rpow_le_rpow hf hP.le
  have hbound : (∫⁻ x' : EuclideanSpace ℝ (Fin d), ‖u (EuclideanSpace.snocLast x' 0)‖ₑ ^ p.toReal)
      ≤ ENNReal.ofReal p.toReal * S ^ p.toReal := by
    calc (∫⁻ x' : EuclideanSpace ℝ (Fin d), ‖u (EuclideanSpace.snocLast x' 0)‖ₑ ^ p.toReal)
        ≤ ENNReal.ofReal (p.toReal - 1) * S ^ p.toReal + S ^ p.toReal :=
          hmain.trans (add_le_add (mul_le_mul' le_rfl (hS u (le_add_right le_rfl)))
            (hS g (le_add_left le_rfl)))
      _ = ENNReal.ofReal p.toReal * S ^ p.toReal := by
          rw [← add_one_mul, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith) zero_le_one,
            sub_add_cancel]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hu0c.aestronglyMeasurable]
  calc (∫⁻ x' : EuclideanSpace ℝ (Fin d), ‖u (EuclideanSpace.snocLast x' 0)‖ₑ ^ p.toReal)
        ^ (1 / p.toReal)
      ≤ (ENNReal.ofReal p.toReal * S ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow hbound (by positivity)
    _ = ENNReal.ofReal p.toReal ^ (1 / p.toReal) * S := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hP.ne', ENNReal.rpow_one]

end Trace
