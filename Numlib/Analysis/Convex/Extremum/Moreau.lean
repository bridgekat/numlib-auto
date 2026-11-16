/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Continuity
import Numlib.Analysis.Convex.Duality.InnerPairing
import Numlib.Analysis.Convex.Operations.InfConv
import Numlib.Analysis.Convex.Extremum.Minimum

/-!
# Moreau's decomposition

Let $E$ be a real vector space and let $B$ be a symmetric positive definite bilinear form on $E$.
Write $\langle x, y \rangle = B(x, y)$ and let $w(z) = \tfrac12 \langle z, z \rangle$ be the
quadratic of $B$. With respect to the pairing $B$ of $E$ with itself, $w$ is its own conjugate:
$w^* = w$. Now let $E$ be a real normed space, let the quadratic form
$z \mapsto \langle z, z \rangle$ be continuous, and let every continuous linear functional on $E$
have the form $\langle \cdot, y \rangle$. Then for every closed proper convex function $f$ on $E$,
infimal convolution with $w$ splits $w$ between $f$ and its conjugate $f^*$:
$$(f \mathbin{\square} w)(z) + (f^* \mathbin{\square} w)(z) = w(z) \qquad \text{for all } z \in E.$$
This is the identity half of **Moreau's decomposition**, Theorem 31.5 of [rockafellar1970convex].
The function $f \mathbin{\square} w$, with $(f \mathbin{\square} w)(z) = \inf_x \{f(x) + w(z -
x)\}$, is the **Moreau envelope** of $f$. The presentation follows §31 of [rockafellar1970convex].

The existence and the uniqueness of the points that attain the two infima, and the proximal mapping,
are in `Numlib.Analysis.Convex.Extremum.Prox`, which needs finite dimension. The gradient formulas
for the two envelopes are in `Numlib.Analysis.Convex.Extremum.MoreauGradient`.

## Main definitions

* `ConvexAnalysis.quadFn`: the quadratic $w(z) = \tfrac12 B(z, z)$, as a function with values in the
  extended reals.

## Main results

* `ConvexAnalysis.convexConj_quadFn`: the quadratic is its own conjugate, $w^* = w$.
* `ConvexAnalysis.convexConj_quadFn_sub`: the conjugate of $x \mapsto w(z - x)$ is
  $y \mapsto \langle z, y \rangle + w(y)$.
* `ConvexAnalysis.moreau_add`: Moreau's decomposition $(f \mathbin{\square} w)(z) + (f^*
  \mathbin{\square} w)(z) = w(z)$.
* `ConvexAnalysis.infConv_quadFn_ne_top`, `ConvexAnalysis.infConv_quadFn_ne_bot`: the Moreau
  envelope of a closed proper convex function is finite everywhere.
* `ConvexAnalysis.mem_subdifferential_iff_infConv_eq`: for $z = x + y$, the point $x$ attains the
  infimum that defines $(f \mathbin{\square} w)(z)$ and the point $y$ attains the infimum that
  defines $(f^* \mathbin{\square} w)(z)$ if and only if $y \in \partial f(x)$.

## Proof outline

The infimum of a function $\varphi$ is $-\varphi^*(0)$. Apply this to $\varphi = f + w(z - \cdot)$.
Since $w(z - \cdot)$ is finite and continuous, the conjugate of this sum at the origin is the
infimal convolution of the two conjugates. The formula for the conjugate of $w(z - \cdot)$ and the
substitution $y \mapsto -y$ turn $\langle z, y \rangle + w(y)$ into $w(z - y) - w(z)$, and this
gives the decomposition.

## Implementation notes

* The constraint qualification for the conjugate of the sum is the continuity of $w(z - \cdot)$, not
  a relative-interior condition. So no finite dimension is needed.
* The proofs use only $B$ and never the norm of $E$. So the results apply to a product space with
  the pairing `ConvexAnalysis.prodPairing (innerₗ U) (innerₗ X)`, which has no `InnerProductSpace`
  instance. On a real inner product space with $B$ the inner product, $w(z) = \tfrac12 \|z\|^2$
  (`ConvexAnalysis.quadFn_innerL`).
-/

open RealInnerProductSpace

namespace ConvexAnalysis

/-! ### The quadratic $w(z) = \tfrac12 B(z, z)$ -/

section Quadratic

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ}

/-- Let $E$ be a real vector space and let $B$ be a bilinear form on $E$. The **quadratic** of $B$
is the function $w$ on $E$ with
$$w(z) = \tfrac12 B(z, z).$$

The function takes only real values, but it has values in `EReal`, so that it can be used with
`ConvexAnalysis.convexConj` and `ConvexAnalysis.infConv`. The definition puts no hypothesis on
$B$. -/
noncomputable def quadFn (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : E → EReal :=
  fun z => ((B z z / 2 : ℝ) : EReal)

/-- The quadratic has the value $w(z) = \tfrac12 B(z, z)$, a real number. -/
theorem quadFn_apply (z : E) : quadFn B z = ((B z z / 2 : ℝ) : EReal) := rfl

/-- The quadratic never takes the value $-\infty$. -/
theorem quadFn_ne_bot (z : E) : quadFn B z ≠ ⊥ := EReal.coe_ne_bot _

/-- The quadratic never takes the value $+\infty$. -/
theorem quadFn_ne_top (z : E) : quadFn B z ≠ ⊤ := EReal.coe_ne_top _

/-- The quadratic is even: $w(-z) = w(z)$. -/
@[simp] theorem quadFn_neg (z : E) : quadFn B (-z) = quadFn B z := by
  rw [quadFn_apply, quadFn_apply, self_pairing_neg]

/-- The quadratic translated to the origin is the quadratic: $w(0 - u) = w(u)$ for all $u$. -/
theorem quadFn_zero_sub : (fun u : E => quadFn B (0 - u)) = quadFn B := by
  funext u
  rw [zero_sub, quadFn_neg]

variable [IsInnerPairing B]

/-- Let $B$ be a symmetric positive definite bilinear form on $E$ and let $z \in E$. Then
$x \mapsto w(z - x)$ is a convex function. The defect in the convexity inequality at $u$ and $v$
with weights $a$ and $b$ is $\tfrac12 a b B(u - v, u - v) \ge 0$. -/
theorem convexFn_quadFn_sub (z : E) : ConvexFn (fun x => quadFn B (z - x)) := by
  refine convexFn_of_epi_combo fun x y μ ν hx hy a b ha hb hab => ?_
  rw [quadFn_apply, EReal.coe_le_coe_iff] at hx hy
  have harg : z - (a • x + b • y) = a • (z - x) + b • (z - y) := by
    rw [smul_sub, smul_sub, ← add_sub_add_comm, ← add_smul, hab, one_smul]
  rw [quadFn_apply, harg, EReal.coe_le_coe_iff]
  refine le_trans (self_pairing_combo_le ha hb hab) ?_
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

/-- For a symmetric positive definite bilinear form $B$, the quadratic $w$ is a convex function. -/
theorem convexFn_quadFn : ConvexFn (quadFn B) := by
  rw [← quadFn_zero_sub]
  exact convexFn_quadFn_sub 0

omit [IsInnerPairing B] in
/-- For every $z \in E$, the function $x \mapsto w(z - x)$ is proper: it is finite everywhere. -/
theorem properConvex_quadFn_sub (z : E) : ProperConvex (fun x => quadFn B (z - x)) :=
  properConvex_coe fun x => B (z - x) (z - x) / 2

/-- **The conjugate of a translate of the quadratic.** Let $B$ be a symmetric positive definite
bilinear form on $E$, and write $\langle x, y \rangle = B(x, y)$. Then for all $z, y \in E$, the
conjugate of $x \mapsto w(z - x)$ with respect to $B$ is
$$\sup_x \{\langle x, y \rangle - w(z - x)\} = \langle z, y \rangle + w(y).$$

The defect in the supremum at $x$ is $\tfrac12 B((x - z) - y, (x - z) - y)$, so the supremum is
attained at $x = z + y$. -/
theorem convexConj_quadFn_sub (z y : E) :
    convexConj B (fun x => quadFn B (z - x)) y = ((B z y : ℝ) : EReal) + quadFn B y := by
  have hsub : ∀ u : E, B (u - z) y = B u y - B z y := fun u => by
    rw [map_sub, LinearMap.sub_apply]
  rw [convexConj_apply]
  refine le_antisymm (iSup_le fun x => ?_) ?_
  · rw [quadFn_apply, quadFn_apply, ← EReal.coe_sub, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    linarith [self_pairing_sub (B := B) (x - z) y, self_pairing_nonneg B (x - z - y), hsub x,
      self_pairing_sub_rev (B := B) z x]
  · refine le_trans (le_of_eq ?_)
      (le_iSup (fun x : E => ((B x y : ℝ) : EReal) - quadFn B (z - x)) (z + y))
    have harg : z - (z + y) = -y := by abel
    have hadd : B (z + y) y = B z y + B y y := by rw [map_add, LinearMap.add_apply]
    rw [harg, quadFn_apply, quadFn_apply, ← EReal.coe_add, ← EReal.coe_sub,
      EReal.coe_eq_coe_iff, hadd, self_pairing_neg]
    ring

/-- **The quadratic is its own conjugate.** Let $B$ be a symmetric positive definite bilinear form
on $E$, and write $\langle x, y \rangle = B(x, y)$. Then the conjugate of $w$ with respect to
$B$ is $w$:
$$\sup_x \{\langle x, y \rangle - \tfrac12 \langle x, x \rangle\} = \tfrac12 \langle y, y
  \rangle \qquad \text{for all } y \in E.$$

The defect in the supremum at $x$ is $\tfrac12 B(x - y, x - y)$, so the supremum is attained at
$x = y$. -/
theorem convexConj_quadFn (y : E) : convexConj B (quadFn B) y = quadFn B y := by
  have h := convexConj_quadFn_sub (B := B) 0 y
  rwa [quadFn_zero_sub, map_zero, LinearMap.zero_apply, EReal.coe_zero, zero_add] at h

end Quadratic

/-! ### The quadratic in a topological space -/

section QuadraticTopology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} [IsContinuousInnerPairing B]

/-- Let $E$ be a topological vector space and let $B$ be a symmetric positive definite bilinear form
on $E$ whose quadratic form is continuous. Then $x \mapsto w(z - x)$ is continuous for every
$z \in E$. This is the constraint qualification that Moreau's decomposition uses. -/
theorem continuous_quadFn_sub (z : E) : Continuous (fun x => quadFn B (z - x)) := by
  have h : Continuous fun x : E => (B (z - x) (z - x) / 2 : ℝ) :=
    ((continuous_self_pairing' B).comp (continuous_const.sub continuous_id)).div_const 2
  exact continuous_coe_real_ereal.comp h

end QuadraticTopology

/-! ### The inner-product instance -/

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On a real inner product space, the quadratic of the inner product is $w(z) = \tfrac12 \|z\|^2$.
-/
@[simp] theorem quadFn_innerL (z : E) : quadFn (innerₗ E) z = ((‖z‖ ^ 2 / 2 : ℝ) : EReal) := by
  rw [quadFn_apply, innerₗ_apply_apply, real_inner_self_eq_norm_sq]

end Inner

/-! ### Moreau's decomposition -/

section Moreau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ} [IsContinuousInnerPairing B] [IsCompatiblePairing B] {f : E → EReal}

omit [IsContinuousInnerPairing B] [IsCompatiblePairing B] in
/-- The **Moreau envelope** written out: if $f$ never takes the value $-\infty$, then
$$(f \mathbin{\square} w)(z) = \inf_x \{f(x) + w(z - x)\}.$$
-/
theorem infConv_quadFn_apply (hb : ∀ x, f x ≠ ⊥) (z : E) :
    infConv f (quadFn B) z = ⨅ x, (f x + quadFn B (z - x)) := by
  rw [infConv_apply hb (fun x => quadFn_ne_bot x) z,
    ← (Equiv.subLeft z).iInf_comp (g := fun y => f (z - y) + quadFn B y)]
  exact iInf_congr fun x => by simp only [Equiv.subLeft_apply, sub_sub_cancel]

/-- Let $f$ be a closed proper convex function on $E$ and let $z \in E$. Then the sum of $f$ and
$x \mapsto w(z - x)$ is exact (`ConvexAnalysis.IsExactSum`): the conjugate of the sum is the
infimal convolution of the conjugates, and this infimal convolution is attained. The reason is
that $w(z - \cdot)$ is finite and continuous. -/
theorem isExactSum_quadFn_sub (hf : ClosedProperConvexFn f) (z : E) :
    IsExactSum B f (fun x => quadFn B (z - x)) := by
  obtain ⟨x₀, hx₀⟩ := hf.proper.convexDom_nonempty
  exact (IsExactSum.of_continuousAt (convexFn_quadFn_sub z) (properConvex_quadFn_sub z) hf.convex
    hf.proper (mem_convexDom.2 (lt_top_iff_ne_top.2 (quadFn_ne_top _))) hx₀
    (continuous_quadFn_sub z).continuousAt).symm

/-- Let $f$ be a closed proper convex function on $E$. Then the sum $f + w$ is exact
(`ConvexAnalysis.IsExactSum`). This is the case $z = 0$ of
`ConvexAnalysis.isExactSum_quadFn_sub`. -/
theorem isExactSum_quadFn (hf : ClosedProperConvexFn f) : IsExactSum B f (quadFn B) := by
  have h := isExactSum_quadFn_sub (B := B) hf 0
  rwa [quadFn_zero_sub] at h

/-- **Moreau's decomposition.** Let $E$ be a real normed space and let $B$ be a symmetric positive
definite bilinear form on $E$ whose quadratic form is continuous and such that every continuous
linear functional on $E$ has the form $B(\cdot, y)$. Let $f$ be a closed proper convex function
on $E$, let $f^*$ be its conjugate with respect to $B$, and let $w(z) = \tfrac12 B(z, z)$. Then
for every $z \in E$,
$$(f \mathbin{\square} w)(z) + (f^* \mathbin{\square} w)(z) = w(z).$$
This is the identity in Theorem 31.5 of [rockafellar1970convex].

The proof writes $(f \mathbin{\square} w)(z) = -\varphi^*(0)$ for $\varphi = f + w(z - \cdot)$
and computes $\varphi^*(0)$ by `ConvexAnalysis.isExactSum_quadFn_sub`. The substitution
$y \mapsto -y$ turns $\langle z, y \rangle + w(y)$ into $w(z - y) - w(z)$. -/
theorem moreau_add (hf : ClosedProperConvexFn f) (z : E) :
    infConv f (quadFn B) z + infConv (convexConj B f) (quadFn B) z = quadFn B z := by
  obtain ⟨x₀, hx₀⟩ := hf.proper.convexDom_nonempty
  obtain ⟨y₀, hy₀⟩ := (properConvex_convexConj hf (B := B)).convexDom_nonempty
  have hex : IsExactSum (B) f (fun x => quadFn B (z - x)) := isExactSum_quadFn_sub hf z
  have hD : infConv (convexConj B f) (quadFn B) z
      = ⨅ y, (convexConj B f y + quadFn B (z - y)) :=
    infConv_quadFn_apply (convexConj_ne_bot hf.proper.convexDom_nonempty) z
  have hP : infConv f (quadFn B) z
      = -(convexConj B (f + fun x => quadFn B (z - x)) 0) := by
    rw [infConv_quadFn_apply hf.proper.ne_bot z, ← iInf_eq_neg_convexConj_zero (B)]
    exact iInf_congr fun x => rfl
  have hstep : ∀ y : E,
      convexConj B f (0 - -y) + convexConj B (fun x => quadFn B (z - x)) (-y)
        = (convexConj B f y + quadFn B (z - y)) + ((-(B z z / 2) : ℝ) : EReal) := by
    intro y
    have hinner : B z (-y) = -B z y := by rw [map_neg]
    have hreal : B z (-y) + B y y / 2 = B (z - y) (z - y) / 2 + -(B z z / 2) := by
      rw [hinner]
      have h := self_pairing_sub (B := B) z y
      linarith
    rw [convexConj_quadFn_sub, zero_sub, neg_neg, quadFn_neg, quadFn_apply, quadFn_apply,
      ← EReal.coe_add, hreal, EReal.coe_add, ← add_assoc]
  have hQD : convexConj B (f + fun x => quadFn B (z - x)) 0
      = infConv (convexConj B f) (quadFn B) z + ((-(B z z / 2) : ℝ) : EReal) := by
    rw [hex.convexConj_add_apply 0,
      ← neg_surjective.iInf_comp fun y => convexConj B f (0 - y)
        + convexConj B (fun x => quadFn B (z - x)) y,
      hD, EReal.iInf_add_coe]
    exact iInf_congr hstep
  have hDt : infConv (convexConj B f) (quadFn B) z ≠ ⊤ := by
    rw [hD]
    obtain ⟨r, hr⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top (convexConj_ne_bot hf.proper.convexDom_nonempty y₀) hy₀
    have hle : (⨅ y, (convexConj B f y + quadFn B (z - y)))
        ≤ convexConj B f y₀ + quadFn B (z - y₀) := iInf_le _ y₀
    rw [hr, quadFn_apply, ← EReal.coe_add] at hle
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
  have hQb : convexConj B (f + fun x => quadFn B (z - x)) 0 ≠ ⊥ := by
    intro hc
    have hle := sub_le_convexConj B (f + fun x => quadFn B (z - x)) x₀ 0
    rw [hc, le_bot_iff, EReal.coe_sub_eq_bot_iff] at hle
    obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf.proper.ne_bot x₀) hx₀
    rw [Pi.add_apply, hp, quadFn_apply, ← EReal.coe_add] at hle
    exact absurd hle (EReal.coe_ne_top _)
  have hDb : infConv (convexConj B f) (quadFn B) z ≠ ⊥ := by
    intro hc
    rw [hc] at hQD
    simp only [EReal.bot_add] at hQD
    exact hQb hQD
  obtain ⟨d, hd⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hDb (lt_top_iff_ne_top.2 hDt)
  rw [hP, hQD, hd, ← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_add,
    quadFn_apply, EReal.coe_eq_coe_iff]
  ring

private theorem top_add_ne_coe (u : EReal) (r : ℝ) : ⊤ + u ≠ (r : EReal) := by
  rcases eq_or_ne u ⊥ with rfl | hu
  · rw [EReal.add_bot]
    exact (EReal.coe_ne_bot r).symm
  · rw [EReal.top_add_of_ne_bot hu]
    exact (EReal.coe_ne_top r).symm

/-- Let $f$ be a closed proper convex function on $E$, under the hypotheses of
`ConvexAnalysis.moreau_add`. Then the Moreau envelope $(f \mathbin{\square} w)(z)$ is never
$+\infty$.

Both infima in Moreau's decomposition are real numbers, since their sum is the real number
$w(z)$. -/
theorem infConv_quadFn_ne_top (hf : ClosedProperConvexFn f) (z : E) :
    infConv f (quadFn B) z ≠ ⊤ := by
  intro hc
  have h := moreau_add (B := B) hf z
  rw [hc, quadFn_apply] at h
  exact top_add_ne_coe _ _ h

/-- Let $f$ be a closed proper convex function on $E$, under the hypotheses of
`ConvexAnalysis.moreau_add`. Then the Moreau envelope $(f \mathbin{\square} w)(z)$ is never
$-\infty$. -/
theorem infConv_quadFn_ne_bot (hf : ClosedProperConvexFn f) (z : E) :
    infConv f (quadFn B) z ≠ ⊥ := by
  intro hc
  have h := moreau_add (B := B) hf z
  rw [hc, quadFn_apply, EReal.bot_add] at h
  exact EReal.bot_ne_coe _ h

/-- Let $f$ be a closed proper convex function on $E$, under the hypotheses of
`ConvexAnalysis.moreau_add`. Then the Moreau envelope $(f^* \mathbin{\square} w)(z)$ of the
conjugate is never $+\infty$. -/
theorem infConv_convexConj_quadFn_ne_top (hf : ClosedProperConvexFn f) (z : E) :
    infConv (convexConj B f) (quadFn B) z ≠ ⊤ := by
  intro hc
  have h := moreau_add (B := B) hf z
  rw [hc, EReal.add_top_of_ne_bot (infConv_quadFn_ne_bot (B := B) hf z), quadFn_apply] at h
  exact absurd h (EReal.coe_ne_top _).symm

/-- Let $f$ be a closed proper convex function on $E$, under the hypotheses of
`ConvexAnalysis.moreau_add`. Then the Moreau envelope $(f^* \mathbin{\square} w)(z)$ of the
conjugate is never $-\infty$. -/
theorem infConv_convexConj_quadFn_ne_bot (hf : ClosedProperConvexFn f) (z : E) :
    infConv (convexConj B f) (quadFn B) z ≠ ⊥ := by
  intro hc
  have h := moreau_add (B := B) hf z
  rw [hc, EReal.add_bot, quadFn_apply] at h
  exact absurd h (EReal.coe_ne_bot _).symm

/-- **The Kuhn–Tucker conditions for Moreau's decomposition.** Let $f$ be a closed proper convex
function on $E$, under the hypotheses of `ConvexAnalysis.moreau_add`, and let $x, y, z \in E$
with $x + y = z$. Then $y \in \partial f(x)$ if and only if both
$$f(x) + w(y) = (f \mathbin{\square} w)(z) \quad \text{and} \quad f^*(y) + w(x) = (f^*
  \mathbin{\square} w)(z).$$
That is, $x$ attains the infimum that defines $(f \mathbin{\square} w)(z)$ and $y$ attains the
infimum that defines $(f^* \mathbin{\square} w)(z)$.

The subdifferential is taken with respect to $B$. The proof uses `ConvexAnalysis.moreau_add`.
The sum of the two left sides is $(f(x) + f^*(y)) + (w(x) + w(y))$, and
$\langle x, y \rangle + w(x) + w(y) = w(z)$. So Fenchel's inequality makes this sum at least
$w(z)$, which is the sum of the two infima, with equality exactly when $y \in \partial f(x)$.
The existence and the uniqueness of such a splitting of $z$ are in
`Numlib.Analysis.Convex.Extremum.Prox`. -/
theorem mem_subdifferential_iff_infConv_eq (hf : ClosedProperConvexFn f) {x y z : E}
    (hz : x + y = z) :
    y ∈ subdifferential (B) f x ↔
      f x + quadFn B y = infConv f (quadFn B) z ∧
        convexConj B f y + quadFn B x = infConv (convexConj B f) (quadFn B) z := by
  have hzx : z - x = y := by rw [← hz]; abel
  have hzy : z - y = x := by rw [← hz]; abel
  have hPle : infConv f (quadFn B) z ≤ f x + quadFn B y := by
    rw [infConv_quadFn_apply hf.proper.ne_bot z, ← hzx]
    exact iInf_le _ x
  have hDle : infConv (convexConj B f) (quadFn B) z ≤ convexConj B f y + quadFn B x := by
    rw [infConv_quadFn_apply (convexConj_ne_bot hf.proper.convexDom_nonempty) z, ← hzy]
    exact iInf_le _ y
  have hreal : B y y / 2 + B x x / 2 = B x x / 2 + B y y / 2 := by ring
  have hkey : (f x + quadFn B y) + (convexConj B f y + quadFn B x)
      = (f x + convexConj B f y) + ((B x x / 2 + B y y / 2 : ℝ) : EReal) := by
    rw [add_add_add_comm, quadFn_apply, quadFn_apply, ← EReal.coe_add, hreal]
  have hwz : ((B x y : ℝ) : EReal) + ((B x x / 2 + B y y / 2 : ℝ) : EReal) = quadFn B z := by
    rw [← EReal.coe_add, quadFn_apply, ← hz, EReal.coe_eq_coe_iff]
    have h := self_pairing_add (B := B) x y
    linarith
  constructor
  · intro hmem
    have hfen : f x + convexConj B f y = ((B x y : ℝ) : EReal) :=
      hf.proper.mem_subdifferential_iff_add_convexConj_eq.1 hmem
    have hsum : (f x + quadFn B y) + (convexConj B f y + quadFn B x)
        = infConv f (quadFn B) z + infConv (convexConj B f) (quadFn B) z := by
      rw [hkey, hfen, hwz, moreau_add (B := B) hf z]
    obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (infConv_quadFn_ne_bot (B := B) hf z)
      (lt_top_iff_ne_top.2 (infConv_quadFn_ne_top (B := B) hf z))
    obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
      (infConv_convexConj_quadFn_ne_bot (B := B) hf z)
      (lt_top_iff_ne_top.2 (infConv_convexConj_quadFn_ne_top (B := B) hf z))
    have hAb : f x + quadFn B y ≠ ⊥ := by
      intro hcon
      rw [hcon, le_bot_iff, hp] at hPle
      exact absurd hPle (EReal.coe_ne_bot p)
    have hCb : convexConj B f y + quadFn B x ≠ ⊥ := by
      intro hcon
      rw [hcon, le_bot_iff, hq] at hDle
      exact absurd hDle (EReal.coe_ne_bot q)
    obtain ⟨hAt, hCt⟩ := (EReal.add_ne_top_iff_ne_top₂ hAb hCb).1
      (by rw [hsum, hp, hq, ← EReal.coe_add]; exact EReal.coe_ne_top _)
    obtain ⟨a, ha⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hAb (lt_top_iff_ne_top.2 hAt)
    obtain ⟨c, hcc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hCb (lt_top_iff_ne_top.2 hCt)
    rw [hp, ha, EReal.coe_le_coe_iff] at hPle
    rw [hq, hcc, EReal.coe_le_coe_iff] at hDle
    rw [ha, hcc, hp, hq, ← EReal.coe_add, ← EReal.coe_add,
      EReal.coe_eq_coe_iff] at hsum
    refine ⟨?_, ?_⟩
    · rw [ha, hp, EReal.coe_eq_coe_iff]
      linarith
    · rw [hcc, hq, EReal.coe_eq_coe_iff]
      linarith
  · rintro ⟨h1, h2⟩
    have hsum : (f x + convexConj B f y) + ((B x x / 2 + B y y / 2 : ℝ) : EReal)
        = ((B z z / 2 : ℝ) : EReal) := by
      rw [← hkey, h1, h2, moreau_add hf z, quadFn_apply]
    rw [hf.proper.mem_subdifferential_iff_add_convexConj_eq,
      EReal.eq_coe_sub_of_add_coe_eq_coe hsum, EReal.coe_eq_coe_iff, ← hz]
    have h := self_pairing_add (B := B) x y
    linarith

end Moreau

end ConvexAnalysis
