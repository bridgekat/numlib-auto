/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Extremum.Moreau
import Numlib.Analysis.Convex.Subdifferential.Monotone

/-!
# Proximal mappings and maximal monotonicity of the subdifferential

Let $E$ be a real normed space with a symmetric positive definite pairing
$\langle x, y \rangle = B(x, y)$ whose quadratic form is continuous, and let
$w(x) = \tfrac12 \langle x, x \rangle$. For a closed proper convex function
$f \colon E \to [-\infty, +\infty]$ and a point $z \in E$, the infimum that defines the Moreau
envelope $(f \mathbin{\square} w)(z) = \inf_x \bigl(f(x) + w(z - x)\bigr)$ is attained at exactly
one point, the **proximal point** $\operatorname{prox}(z \mid f)$, when $E$ is finite-dimensional. A
point $x$ is this minimizer if and only if $z - x \in \partial f(x)$. This is the attainment and
uniqueness half of **Moreau's decomposition** ([rockafellar1970convex], Theorem 31.5). The identity
$(f \mathbin{\square} w) + (f^* \mathbin{\square} w) = w$ is in
`Numlib.Analysis.Convex.Extremum.Moreau`, and the gradient formulas are in
`Numlib.Analysis.Convex.Extremum.MoreauGradient`.

Two corollaries follow from the same monotonicity argument. The proximal mapping is nonexpansive, so
$(x, x^*) \mapsto x + x^*$ is a homeomorphism of the graph of $\partial f$ onto $E$. Also,
$\partial f$ is a **maximal monotone** mapping: it is maximal among monotone relations. This is a
different statement from the maximal cyclic monotonicity of a subdifferential.

The pairing $B$ is called **compatible** below if it is continuous and every continuous linear
functional on $E$ has the form $\langle \cdot, y \rangle$ for some $y \in E$
(`ConvexAnalysis.IsCompatiblePairing B`). Most results of the section on attainment assume this.

## Main definitions

* `ConvexAnalysis.moreauObj`: the objective $x \mapsto f(x) + w(z - x)$, whose infimum is
  $(f \mathbin{\square} w)(z)$.
* `ConvexAnalysis.prox`: the **proximal point** $\operatorname{prox}(z \mid f)$, a minimizer of this
  objective.

## Main results

* `ConvexAnalysis.subdifferential_quadFn_sub`: $\partial \bigl(w(z - \cdot)\bigr)(x) = \{x - z\}$.
* `ConvexAnalysis.recessionFn_quadFn_sub`: the function $w(z - \cdot)$ has recession function
  $+\infty$ in every direction $y \neq 0$.
* `ConvexAnalysis.argmin_moreauObj_nonempty`: the infimum of $f + w(z - \cdot)$ is attained.
* `ConvexAnalysis.mem_argmin_moreauObj_iff`: $x$ minimizes $f + w(z - \cdot)$ if and only if
  $z - x \in \partial f(x)$.
* `ConvexAnalysis.existsUnique_sub_mem_subdifferential`: exactly one $x$ satisfies
  $z - x \in \partial f(x)$.
* `ConvexAnalysis.prox_eq_iff`: $\operatorname{prox}(z \mid f) = x$ if and only if
  $z - x \in \partial f(x)$.
* `ConvexAnalysis.prox_add_prox_convexConj`: $z = \operatorname{prox}(z \mid f) +
  \operatorname{prox}(z \mid f^*)$.
* `ConvexAnalysis.pairingNorm_prox_sub_le`, `ConvexAnalysis.dist_prox_prox_le`,
  `ConvexAnalysis.lipschitzWith_prox`: the proximal mapping is nonexpansive.
* `ConvexAnalysis.subgradientRelHomeomorph`: the graph of $\partial f$ is homeomorphic to $E$.
* `ConvexAnalysis.isMaximalMonotoneRel_subgradientRel`: $\partial f$ is maximal monotone.

## Implementation notes

* All results use the pairing $B$ and not the norm of $E$. Therefore `ConvexAnalysis.prox` is
  available on product spaces that carry no `InnerProductSpace` instance. The norm of $E$ enters
  only in `ConvexAnalysis.continuous_prox`.
* `ConvexAnalysis.prox` is a choice by `Classical.epsilon` from the set of minimizers. Where this
  set is empty, its value is an unspecified point of $E$. The standing hypothesis
  `ConvexAnalysis.ClosedProperConvexFn f` makes the set a singleton.
* Finite dimension is used only for the attainment of the minimum.
-/

namespace ConvexAnalysis

/-! ### The Moreau objective and the subdifferential of the quadratic -/

section Objective

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} [IsContinuousInnerPairing B] {f : E → EReal}

/-- The **Moreau objective** of $f$ at $z$: the function $x \mapsto f(x) + w(z - x)$, with
$w(x) = \tfrac12 B(x, x)$. Its infimum over $x$ is the envelope $(f \mathbin{\square} w)(z)$.

The quadratic $w$ is `ConvexAnalysis.quadFn B`. -/
noncomputable def moreauObj (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (f : E → EReal) (z : E) : E → EReal :=
  f + fun x => quadFn B (z - x)

omit [IsContinuousInnerPairing B] in
/-- The Moreau objective is $f + w(z - \cdot)$. -/
theorem moreauObj_def (f : E → EReal) (z : E) :
    moreauObj B f z = f + fun x => quadFn B (z - x) := rfl

omit [IsContinuousInnerPairing B] in
/-- The Moreau objective at $x$ is $f(x) + w(z - x)$. -/
@[simp] theorem moreauObj_apply (f : E → EReal) (z x : E) :
    moreauObj B f z x = f x + quadFn B (z - x) := rfl

/-- For all $z, x \in E$, the vector $x - z$ is a subgradient of $u \mapsto w(z - u)$ at $x$. The
defect in the subgradient inequality is $\tfrac12 B(u - x, u - x)$. -/
theorem sub_mem_subdifferential_quadFn_sub (z x : E) :
    x - z ∈ subdifferential B (fun u => quadFn B (z - u)) x := by
  intro u
  simp only [quadFn_apply, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hexp := self_pairing_sub (B := B) (z - x) (u - x)
  have hinner : B (u - x) (x - z) = -B (z - x) (u - x) := by
    rw [show x - z = -(z - x) by abel, map_neg, pairing_comm B (u - x) (z - x)]
  rw [show z - u = (z - x) - (u - x) by abel]
  nlinarith [self_pairing_nonneg B (u - x)]

/-- **The subdifferential of the translated quadratic is a singleton.** For all $z, x \in E$,
$$\partial \bigl(w(z - \cdot)\bigr)(x) = \{x - z\}.$$

If $y$ is a subgradient, the subgradient inequality at the point $y + z$ forces $\tfrac12
B\bigl((z - x) + y, (z - x) + y\bigr) \le 0$, so $y = x - z$. -/
theorem subdifferential_quadFn_sub (z x : E) :
    subdifferential B (fun u => quadFn B (z - u)) x = {x - z} := by
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · have h := hy (y + z)
    simp only [quadFn_apply, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    have hnorm : B (z - (y + z)) (z - (y + z)) = B y y := by
      rw [show z - (y + z) = -y by abel, self_pairing_neg]
    have hyz : B (y + z - x) y = B y y + B (z - x) y := by
      rw [show y + z - x = y + (z - x) by abel, map_add, LinearMap.add_apply]
    rw [hnorm, hyz] at h
    have hexp := self_pairing_add (B := B) (z - x) y
    have hsq : B ((z - x) + y) ((z - x) + y) ≤ 0 := by nlinarith
    have hz : (z - x) + y = 0 :=
      self_pairing_eq_zero_iff.1 (le_antisymm hsq (self_pairing_nonneg B _))
    rw [Set.mem_singleton_iff, ← sub_eq_zero, show y - (x - z) = (z - x) + y by abel]
    exact hz
  · rw [Set.singleton_subset_iff]
    exact sub_mem_subdifferential_quadFn_sub z x

/-- **The subdifferential of the quadratic is the identity:** $\partial w(x) = \{x\}$ for every
$x \in E$. -/
theorem subdifferential_quadFn (x : E) : subdifferential B (quadFn B) x = {x} := by
  rw [← quadFn_zero_sub, subdifferential_quadFn_sub, sub_zero]

/-- For every $z \in E$, the function $u \mapsto w(z - u)$ is closed proper convex: it is finite,
convex and continuous. -/
theorem closedProperConvexFn_quadFn_sub (z : E) :
    ClosedProperConvexFn (fun x => quadFn B (z - x)) := by
  refine ⟨convexFn_quadFn_sub z, ?_, properConvex_quadFn_sub z⟩
  rw [closedConvex_iff_lowerSemicontinuous fun _ => quadFn_ne_bot _]
  exact (continuous_quadFn_sub z).lowerSemicontinuous

/-- **The translated quadratic recedes in no direction.** For every $z \in E$ and every $y \neq 0$,
the recession function of $x \mapsto w(z - x)$ satisfies
$$\bigl(w(z - \cdot)\bigr)0^+(y) = +\infty.$$

A finite value $\nu$ would give $\tfrac12 a^2 B(y, y) \le a \nu$ for every $a \ge 0$, which
fails for large $a$ because $B(y, y) > 0$. -/
theorem recessionFn_quadFn_sub (z : E) {y : E} (hy : y ≠ 0) :
    recessionFn (fun x => quadFn B (z - x)) y = ⊤ := by
  by_contra hne
  obtain ⟨ν, hν⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
    (recessionFn_ne_bot (properConvex_quadFn_sub z) y) (lt_top_iff_ne_top.2 hne)
  have hy2 : 0 < B y y := self_pairing_pos hy
  have ha1 : (1 : ℝ) ≤ max 1 (2 * (|ν| + 1) / B y y) := le_max_left _ _
  have ha0 : (0 : ℝ) ≤ max 1 (2 * (|ν| + 1) / B y y) := le_trans zero_le_one ha1
  have ha3 : 2 * (|ν| + 1) ≤ max 1 (2 * (|ν| + 1) / B y y) * B y y := by
    rw [← div_le_iff₀ hy2]
    exact le_max_right _ _
  have hkey := recessionFn_le_coe_iff_forall.1 (le_of_eq hν) z _ ha0
  have hz : quadFn B (z - z) = ((0 : ℝ) : EReal) := by
    rw [sub_self, quadFn_apply, map_zero]
    norm_num
  have hza : ∀ a : ℝ, quadFn B (z - (z + a • y)) = ((a ^ 2 * B y y / 2 : ℝ) : EReal) := by
    intro a
    rw [show z - (z + a • y) = -(a • y) by abel, quadFn_apply, self_pairing_neg,
      self_pairing_smul]
  simp only [hz, hza, ← EReal.coe_add, EReal.coe_le_coe_iff] at hkey
  nlinarith [hkey, mul_le_mul_of_nonneg_left ha3 ha0,
    mul_le_mul_of_nonneg_left (le_abs_self ν) ha0]

/-- **Uniqueness of the proximal point.** Let $f$ be proper convex and let $z \in E$. If
$z - x_1 \in \partial f(x_1)$ and $z - x_2 \in \partial f(x_2)$, then $x_1 = x_2$.

The monotonicity of $\partial f$ gives $0 \le B\bigl(x_1 - x_2, -(x_1 - x_2)\bigr)$, and the
definiteness of $B$ gives $x_1 = x_2$. -/
theorem eq_of_sub_mem_subdifferential (hp : ProperConvex f) {z x₁ x₂ : E}
    (h₁ : z - x₁ ∈ subdifferential B f x₁) (h₂ : z - x₂ ∈ subdifferential B f x₂) :
    x₁ = x₂ := by
  have hmono := isMonotoneRel_subgradientRel (B := B) hp (x₁, z - x₁) h₁ (x₂, z - x₂) h₂
  rw [show z - x₁ - (z - x₂) = -(x₁ - x₂) by abel, map_neg] at hmono
  rw [← sub_eq_zero]
  exact self_pairing_eq_zero_iff.1
    (le_antisymm (by linarith) (self_pairing_nonneg B (x₁ - x₂)))

/-- The **proximal mapping**: $\operatorname{prox}(z \mid f)$ is a point at which
$x \mapsto f(x) + w(z - x)$ attains its minimum. If there is no such point, the value is an
unspecified point of $E$. For a closed proper convex $f$ on a finite-dimensional space, the
minimizer exists and is unique.

The point is chosen by `Classical.epsilon` from `ConvexAnalysis.argmin (ConvexAnalysis.moreauObj
B f z)`. -/
noncomputable def prox (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (f : E → EReal) (z : E) : E :=
  Classical.epsilon fun x => x ∈ argmin (moreauObj B f z)

end Objective

/-! ### Attainment, uniqueness, and the proximal mapping -/

section Attainment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} [IsContinuousInnerPairing B] [IsCompatiblePairing B]
  {f : E → EReal}

omit [FiniteDimensional ℝ E] [IsCompatiblePairing B] in
/-- If $f$ is closed proper convex, then for every $z$ the Moreau objective $f + w(z - \cdot)$ is
closed proper convex. -/
theorem closedProperConvexFn_moreauObj (hf : ClosedProperConvexFn f) (z : E) :
    ClosedProperConvexFn (moreauObj B f z) := by
  obtain ⟨x₀, hx₀⟩ := hf.proper.convexDom_nonempty
  refine ClosedProperConvexFn.add hf (closedProperConvexFn_quadFn_sub z) ⟨x₀, ?_⟩
  exact mem_convexDom.2 (EReal.add_lt_top (mem_convexDom.1 hx₀).ne (quadFn_ne_top _))

omit [FiniteDimensional ℝ E] [IsCompatiblePairing B] in
/-- **The Moreau objective has no direction of recession.** If $f$ is closed proper convex, then for
every $z$ the recession cone of $f + w(z - \cdot)$ is $\{0\}$.

The recession function of the sum is $f0^+ + \bigl(w(z - \cdot)\bigr)0^+$, and the second term
is $+\infty$ off the origin. -/
theorem recessionConeFn_moreauObj (hf : ClosedProperConvexFn f) (z : E) :
    recessionConeFn (moreauObj B f z) = {0} := by
  have hg := closedProperConvexFn_moreauObj (B := B) hf z
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · by_contra hy0
    rw [Set.mem_singleton_iff] at hy0
    rw [mem_recessionConeFn, moreauObj_def,
      congrFun (recessionFn_add hf (closedProperConvexFn_quadFn_sub z)
          hg.proper.convexDom_nonempty) y,
      Pi.add_apply, recessionFn_quadFn_sub z hy0,
      EReal.add_top_of_ne_bot (recessionFn_ne_bot hf.proper y)] at hy
    exact absurd hy (by simp)
  · rw [Set.singleton_subset_iff, mem_recessionConeFn]
    exact recessionFn_apply_zero_le _

omit [IsCompatiblePairing B] in
/-- **Attainment.** Let $E$ be finite-dimensional and let $f$ be closed proper convex. Then for
every $z \in E$ the infimum that defines $(f \mathbin{\square} w)(z)$ is attained: the set of
minimizers of $x \mapsto f(x) + w(z - x)$ is nonempty.

The objective is closed proper convex with recession cone $\{0\}$, so it attains its minimum. -/
theorem argmin_moreauObj_nonempty (hf : ClosedProperConvexFn f) (z : E) :
    (argmin (moreauObj B f z)).Nonempty :=
  argmin_nonempty_of_recessionConeFn_eq_zero (closedProperConvexFn_moreauObj hf z).convex
    (closedProperConvexFn_moreauObj hf z).closed (closedProperConvexFn_moreauObj hf z).proper
    (recessionConeFn_moreauObj hf z)

omit [FiniteDimensional ℝ E] in
/-- **Characterization of the minimizer.** Let the pairing $B$ be compatible, and let $f$ be closed
proper convex. Then for all $z, x \in E$, the point $x$ minimizes $f + w(z - \cdot)$ if and only
if
$$z - x \in \partial f(x).$$

The proof combines Fermat's rule, the sum rule for subdifferentials and
`ConvexAnalysis.subdifferential_quadFn_sub`. Finite dimension is not needed. -/
theorem mem_argmin_moreauObj_iff (hf : ClosedProperConvexFn f) (z x : E) :
    x ∈ argmin (moreauObj B f z) ↔ z - x ∈ subdifferential B f x := by
  rw [mem_argmin_iff_zero_mem_subdifferential B, moreauObj_def,
    (isExactSum_quadFn_sub hf z).subdifferential_add x, subdifferential_quadFn_sub]
  constructor
  · rintro ⟨y, hy, w, hw, hsum⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have hyz : y = z - x := by
      rw [← sub_eq_zero, show y - (z - x) = y + (x - z) by abel]
      exact hsum
    rwa [hyz] at hy
  · intro h
    exact ⟨z - x, h, x - z, rfl, by abel_nf⟩

/-- Let $E$ be finite-dimensional, let the pairing $B$ be compatible, and let $f$ be closed proper
convex. Then for every $z \in E$ there is exactly one $x \in E$ with
$$z - x \in \partial f(x),$$
that is, exactly one splitting $z = x + x^*$ with $x^* \in \partial f(x)$. -/
theorem existsUnique_sub_mem_subdifferential (hf : ClosedProperConvexFn f) (z : E) :
    ∃! x : E, z - x ∈ subdifferential B f x := by
  obtain ⟨x, hx⟩ := argmin_moreauObj_nonempty (B := B) hf z
  have hx' := (mem_argmin_moreauObj_iff hf z x).1 hx
  exact ⟨x, hx', fun x' hx'' => eq_of_sub_mem_subdifferential hf.proper hx'' hx'⟩

omit [IsCompatiblePairing B] in
/-- If $E$ is finite-dimensional and $f$ is closed proper convex, then
$\operatorname{prox}(z \mid f)$ minimizes the Moreau objective $f + w(z - \cdot)$. -/
theorem prox_mem_argmin (hf : ClosedProperConvexFn f) (z : E) :
    prox B f z ∈ argmin (moreauObj B f z) :=
  Classical.epsilon_spec (argmin_moreauObj_nonempty hf z)

/-- If $E$ is finite-dimensional, the pairing $B$ is compatible and $f$ is closed proper convex,
then $z - \operatorname{prox}(z \mid f) \in \partial f(\operatorname{prox}(z \mid f))$: the
splitting $z = x + x^*$ with $x^* \in \partial f(x)$ exists at
$x = \operatorname{prox}(z \mid f)$. -/
theorem sub_prox_mem_subdifferential (hf : ClosedProperConvexFn f) (z : E) :
    z - prox B f z ∈ subdifferential B f (prox B f z) :=
  (mem_argmin_moreauObj_iff hf z _).1 (prox_mem_argmin hf z)

/-- If $E$ is finite-dimensional, the pairing $B$ is compatible, $f$ is closed proper convex and
$z - x \in \partial f(x)$, then $\operatorname{prox}(z \mid f) = x$. -/
theorem prox_eq_of_sub_mem_subdifferential (hf : ClosedProperConvexFn f) {z x : E}
    (h : z - x ∈ subdifferential B f x) : prox B f z = x :=
  eq_of_sub_mem_subdifferential hf.proper (sub_prox_mem_subdifferential hf z) h

/-- Let $E$ be finite-dimensional, let the pairing $B$ be compatible, and let $f$ be closed proper
convex. Then for all $z, x \in E$,
$$\operatorname{prox}(z \mid f) = x \iff z - x \in \partial f(x).$$
This combines attainment and uniqueness in one statement. -/
theorem prox_eq_iff (hf : ClosedProperConvexFn f) (z x : E) :
    prox B f z = x ↔ z - x ∈ subdifferential B f x :=
  ⟨fun h => h ▸ sub_prox_mem_subdifferential hf z, prox_eq_of_sub_mem_subdifferential hf⟩

/-- If $E$ is finite-dimensional, the pairing $B$ is compatible and $f$ is closed proper convex,
then the set of minimizers of the Moreau objective $f + w(z - \cdot)$ is
$\{\operatorname{prox}(z \mid f)\}$. -/
theorem argmin_moreauObj_eq_singleton (hf : ClosedProperConvexFn f) (z : E) :
    argmin (moreauObj B f z) = {prox B f z} := by
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · rw [Set.mem_singleton_iff]
    exact (prox_eq_of_sub_mem_subdifferential hf ((mem_argmin_moreauObj_iff hf z x).1 hx)).symm
  · rw [Set.singleton_subset_iff]
    exact prox_mem_argmin hf z

omit [IsCompatiblePairing B] in
/-- If $E$ is finite-dimensional and $f$ is closed proper convex, then the Moreau envelope is the
value of the objective at the proximal point:
$$(f \mathbin{\square} w)(z) = f(\operatorname{prox}(z \mid f)) + w(z - \operatorname{prox}(z
  \mid f)).$$
-/
theorem infConv_quadFn_eq_moreauObj_prox (hf : ClosedProperConvexFn f) (z : E) :
    infConv f (quadFn B) z = f (prox B f z) + quadFn B (z - prox B f z) := by
  rw [infConv_quadFn_apply hf.proper.ne_bot z]
  exact iInf_eq_of_mem_argmin (f := moreauObj B f z) (prox_mem_argmin hf z)

omit [FiniteDimensional ℝ E] in
/-- If the pairing $B$ is compatible and $f$ is closed proper convex, then the conjugate $f^*$ with
respect to $B$ is closed proper convex. -/
theorem closedProperConvexFn_convexConj (hf : ClosedProperConvexFn f) :
    ClosedProperConvexFn (convexConj B f) := by
  exact ⟨convexFn_convexConj _ _, closedConvex_convexConj, properConvex_convexConj hf⟩

/-- **Moreau's decomposition of a point.** Let $E$ be finite-dimensional, let the pairing $B$ be
compatible, and let $f$ be closed proper convex, with conjugate $f^*$ taken with respect to $B$.
Then for every $z \in E$,
$$\operatorname{prox}(z \mid f) + \operatorname{prox}(z \mid f^*) = z.$$

Conjugate inversion turns $x^* \in \partial f(x)$ into $x \in \partial f^*(x^*)$, so the second
part $x^*$ of the splitting $z = x + x^*$ is $\operatorname{prox}(z \mid f^*)$. -/
theorem prox_add_prox_convexConj (hf : ClosedProperConvexFn f) (z : E) :
    prox B f z + prox B (convexConj B f) z = z := by
  have hx : z - prox B f z ∈ subdifferential B f (prox B f z) := sub_prox_mem_subdifferential hf z
  have hstar : z - (z - prox B f z) ∈
      subdifferential B (convexConj B f) (z - prox B f z) := by
    rw [sub_sub_cancel]
    have h := (mem_subdifferential_convexConj_iff_of_closedConvex (B := B) hf.convex hf.closed).2 hx
    rwa [flip_eq_self] at h
  rw [prox_eq_of_sub_mem_subdifferential (closedProperConvexFn_convexConj hf) hstar]
  abel

/-! ### The graph of the subdifferential is homeomorphic to the space -/

/-- **The proximal mapping is nonexpansive** in the norm $\|x\|_B = \sqrt{B(x, x)}$ that the pairing
induces. Let $E$ be finite-dimensional, let the pairing $B$ be compatible, and let $f$ be closed
proper convex. Then for all $z_1, z_2 \in E$,
$$\|\operatorname{prox}(z_1 \mid f) - \operatorname{prox}(z_2 \mid f)\|_B \le \|z_1 - z_2\|_B.$$

With $x_i = \operatorname{prox}(z_i \mid f)$, the monotonicity of $\partial f$ gives $B(x_1 -
x_2, x_1 - x_2) \le B(x_1 - x_2, z_1 - z_2)$, and the Cauchy–Schwarz inequality finishes the
proof. The norm $\|\cdot\|_B$ is `ConvexAnalysis.pairingNorm B`. -/
theorem pairingNorm_prox_sub_le (hf : ClosedProperConvexFn f) (z₁ z₂ : E) :
    pairingNorm B (prox B f z₁ - prox B f z₂) ≤ pairingNorm B (z₁ - z₂) := by
  have hmono := isMonotoneRel_subgradientRel (B := B) hf.proper
    (prox B f z₁, z₁ - prox B f z₁) (sub_prox_mem_subdifferential hf z₁)
    (prox B f z₂, z₂ - prox B f z₂) (sub_prox_mem_subdifferential hf z₂)
  rw [show z₁ - prox B f z₁ - (z₂ - prox B f z₂)
      = (z₁ - z₂) - (prox B f z₁ - prox B f z₂) by abel, map_sub] at hmono
  have hcs := pairing_le_pairingNorm_mul B (prox B f z₁ - prox B f z₂) (z₁ - z₂)
  have hsq := pairingNorm_sq B (prox B f z₁ - prox B f z₂)
  rcases eq_or_lt_of_le (pairingNorm_nonneg B (prox B f z₁ - prox B f z₂)) with h0 | h0
  · rw [← h0]
    exact pairingNorm_nonneg _ _
  · refine le_of_mul_le_mul_left ?_ h0
    nlinarith

/-- If $E$ is finite-dimensional, the pairing $B$ is compatible and $f$ is closed proper convex,
then the proximal mapping $z \mapsto \operatorname{prox}(z \mid f)$ is continuous.

The mapping is Lipschitz. The constant is $1$ for the norm that the pairing induces. In the norm
of $E$, it is the ratio of the two constants of equivalence between the norms. -/
theorem continuous_prox (hf : ClosedProperConvexFn f) : Continuous (prox B f) := by
  obtain ⟨c, C, hc, hC, hlow, hhigh⟩ := exists_pairingNorm_le_and_le_pairingNorm B
  have hK : (0 : ℝ) ≤ C / c := by positivity
  refine (LipschitzWith.of_dist_le_mul (K := (C / c).toNNReal) fun z₁ z₂ => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK, div_mul_eq_mul_div, le_div_iff₀ hc]
  have h1 := hlow (prox B f z₁ - prox B f z₂)
  have h2 := pairingNorm_prox_sub_le (B := B) hf z₁ z₂
  have h3 := hhigh (z₁ - z₂)
  linarith

/-- Let $E$ be finite-dimensional, let the pairing $B$ be compatible, and let $f$ be closed proper
convex. The map $(x, x^*) \mapsto x + x^*$ is a homeomorphism from the graph of $\partial f$
onto $E$, with inverse $z \mapsto \bigl(\operatorname{prox}(z \mid f), z - \operatorname{prox}(z
\mid f)\bigr)$.

The map is bijective because every $z$ splits uniquely, it is continuous because addition is
continuous, and its inverse is continuous because the proximal mapping is nonexpansive. -/
noncomputable def subgradientRelHomeomorph (hf : ClosedProperConvexFn f) :
    ↥(subgradientRel B f) ≃ₜ E where
  toFun p := p.1.1 + p.1.2
  invFun z := ⟨(prox B f z, z - prox B f z), sub_prox_mem_subdifferential hf z⟩
  left_inv := by
    rintro ⟨⟨x, y⟩, hp⟩
    have hpx : prox B f (x + y) = x :=
      prox_eq_of_sub_mem_subdifferential hf (by rwa [show x + y - x = y by abel])
    refine Subtype.ext ?_
    simp only [hpx, Prod.mk.injEq, true_and]
    abel
  right_inv z := by
    simp only
    abel
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).add (continuous_snd.comp continuous_subtype_val)
  continuous_invFun :=
    Continuous.subtype_mk
      ((continuous_prox hf).prodMk (continuous_id.sub (continuous_prox hf))) _

/-- The homeomorphism `ConvexAnalysis.subgradientRelHomeomorph` sends $(x, x^*)$ to $x + x^*$. -/
@[simp] theorem subgradientRelHomeomorph_apply (hf : ClosedProperConvexFn f)
    (p : ↥(subgradientRel B f)) : subgradientRelHomeomorph hf p = p.1.1 + p.1.2 := rfl

/-- The inverse of `ConvexAnalysis.subgradientRelHomeomorph` sends $z$ to
$\bigl(\operatorname{prox}(z \mid f), z - \operatorname{prox}(z \mid f)\bigr)$. -/
@[simp] theorem subgradientRelHomeomorph_symm_apply (hf : ClosedProperConvexFn f) (z : E) :
    (subgradientRelHomeomorph hf).symm z
      = ⟨(prox B f z, z - prox B f z), sub_prox_mem_subdifferential hf z⟩ := rfl

/-! ### The subdifferential is maximal monotone -/

/-- Let $E$ be finite-dimensional, let the pairing $B$ be compatible, and let $f$ be closed proper
convex. Then the subdifferential $\partial f$ is **maximal monotone**: it is monotone, and every
monotone relation that contains its graph is equal to it.

Suppose that $(y, y^*)$ is monotonically related to every point of the graph. The unique
splitting of $y + y^*$ gives $(x, x^*)$ in the graph with $x + x^* = y + y^*$. Then
$y - x = -(y^* - x^*)$, so the monotonicity inequality reads $0 \le -\|y - x\|_B^2$, and
$(y, y^*) = (x, x^*)$. -/
theorem isMaximalMonotoneRel_subgradientRel (hf : ClosedProperConvexFn f) :
    IsMaximalMonotoneRel B (subgradientRel B f) := by
  refine ⟨isMonotoneRel_subgradientRel hf.proper, fun σ hσ hsub q hq => ?_⟩
  have hmem : (prox B f (q.1 + q.2), q.1 + q.2 - prox B f (q.1 + q.2))
      ∈ subgradientRel B f := sub_prox_mem_subdifferential hf (q.1 + q.2)
  have hmono := hσ q hq _ (hsub hmem)
  rw [show q.2 - (q.1 + q.2 - prox B f (q.1 + q.2)) = -(q.1 - prox B f (q.1 + q.2)) by abel,
    map_neg] at hmono
  have hq1 : q.1 = prox B f (q.1 + q.2) := by
    rw [← sub_eq_zero]
    exact self_pairing_eq_zero_iff.1
      (le_antisymm (by linarith) (self_pairing_nonneg B (q.1 - prox B f (q.1 + q.2))))
  have hq2 : q.2 = q.1 + q.2 - prox B f (q.1 + q.2) := by rw [← hq1]; abel
  rw [show q = (prox B f (q.1 + q.2), q.1 + q.2 - prox B f (q.1 + q.2)) from Prod.ext hq1 hq2]
  exact hmem

end Attainment

/-!
### The inner product case

For the pairing `innerₗ E`, the norm that the pairing induces is the norm of $E$, so the proximal
mapping is nonexpansive in the norm of $E$.
-/

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- Let $E$ be a finite-dimensional real inner product space and let $f$ be closed proper convex.
Then for all $z_1, z_2 \in E$,
$$\operatorname{dist}\bigl(\operatorname{prox}(z_1 \mid f), \operatorname{prox}(z_2 \mid
  f)\bigr) \le \operatorname{dist}(z_1, z_2).$$
-/
theorem dist_prox_prox_le (hf : ClosedProperConvexFn f) (z₁ z₂ : E) :
    dist (prox (innerₗ E) f z₁) (prox (innerₗ E) f z₂) ≤ dist z₁ z₂ := by
  have h := pairingNorm_prox_sub_le (B := innerₗ E) hf z₁ z₂
  rwa [pairingNorm_innerL, pairingNorm_innerL, ← dist_eq_norm, ← dist_eq_norm] at h

/-- Let $E$ be a finite-dimensional real inner product space and let $f$ be closed proper convex.
Then the proximal mapping $z \mapsto \operatorname{prox}(z \mid f)$ is Lipschitz with constant
$1$. -/
theorem lipschitzWith_prox (hf : ClosedProperConvexFn f) :
    LipschitzWith 1 (prox (innerₗ E) f) :=
  LipschitzWith.of_dist_le_mul fun z₁ z₂ => by
    simpa using dist_prox_prox_le hf z₁ z₂

end Inner

end ConvexAnalysis
