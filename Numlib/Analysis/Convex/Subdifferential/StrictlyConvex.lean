/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Subdifferential.EssentiallySmooth
import Numlib.Analysis.Convex.Duality.InnerPairing

/-!
# Essential strict convexity

Let $\langle \cdot, \cdot \rangle$ be a bilinear pairing of real vector spaces $E$ and $F$, and let
$f \colon E \to [-\infty, +\infty]$. The function $f$ is **essentially strictly convex** if it is
strictly convex on every convex subset of $\operatorname{dom} \partial f = \{x : \partial f(x) \neq
\emptyset\}$. This module proves that a proper convex function is essentially strictly convex if and
only if no two distinct points share a subgradient. On a finite-dimensional real inner product
space, $\partial f^*$ is the inverse of $\partial f$ for a closed convex $f$, so this condition says
that $\partial f^*$ is single-valued.

From this follows Theorem 26.3 of [rockafellar1970convex]: a closed proper convex function is
essentially strictly convex if and only if its conjugate $f^*$ is essentially smooth, and $f^*$ is
essentially strictly convex if and only if $f$ is essentially smooth. This duality is what makes the
Legendre transformation an involution: strict convexity on one side corresponds to smoothness on the
other.

## Main definitions

* `ConvexAnalysis.StrictConvexOnFn`: $f$ satisfies the convexity inequality strictly between any two
  distinct points of a set $C$.
* `ConvexAnalysis.EssentiallyStrictlyConvex`: $f$ is strictly convex on every convex subset of
  $\operatorname{dom} \partial f$.

## Main results

* `ConvexAnalysis.mem_subdifferential_of_combo` and
  `ConvexAnalysis.le_combo_of_mem_subdifferential`: a subgradient shared by two points is a
  subgradient at every point between them, and $f$ is affine on the segment between them.
* `ConvexAnalysis.essentiallyStrictlyConvex_iff_pairwise_disjoint`: a proper convex $f$ is
  essentially strictly convex if and only if distinct points have disjoint subdifferentials.
* `ConvexAnalysis.mem_subdifferential_convexConj_innerL_iff`: for a closed convex $f$,
  $u \in \partial f^*(w)$ if and only if $w \in \partial f(u)$.
* `ConvexAnalysis.subsingleton_subdifferential_convexConj_iff` and
  `ConvexAnalysis.pairwise_disjoint_subdifferential_convexConj_iff`: $\partial f^*$ is single-valued
  if and only if $\partial f$ is injective, and $\partial f^*$ is injective if and only if
  $\partial f$ is single-valued.
* `ConvexAnalysis.essentiallySmooth_convexConj_iff_essentiallyStrictlyConvex` and
  `ConvexAnalysis.essentiallyStrictlyConvex_convexConj_iff_essentiallySmooth`: the duality of
  Theorem 26.3 of [rockafellar1970convex], in both directions.
* `ConvexAnalysis.subdifferential_injective_iff`: $\partial f$ is single-valued and injective if and
  only if $f$ is essentially smooth and strictly convex on
  $\operatorname{int}(\operatorname{dom} f)$.

## Implementation notes

* The definitions need only a real vector space with a pairing. The duality results need a
  finite-dimensional real inner product space, because `ConvexAnalysis.EssentiallySmooth` does, and
  they use the pairing `innerₗ E` of $E$ with itself.
* For a proper $f$, every point of $\operatorname{dom} \partial f$ is in $\operatorname{dom} f$, so
  all values of $f$ in the proofs are finite and the arithmetic is real. The only case distinction
  in `EReal` is on $f(z)$ at the test point $z$ of the subgradient inequality, where
  $f(z) = +\infty$ makes the inequality trivial.
-/

namespace ConvexAnalysis

open Filter Metric Topology

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- Let $E$ be a real vector space, let $f \colon E \to [-\infty, +\infty]$ and let $C \subseteq E$.
The function $f$ is **strictly convex on $C$** if for all distinct $x, y \in C$ and all
$a, b > 0$ with $a + b = 1$,
$$f(a x + b y) < a f(x) + b f(y).$$

The condition says nothing about points outside $C$ and does not ask $f$ to be finite. The
arithmetic is in `EReal`. -/
def StrictConvexOnFn (f : E → EReal) (C : Set E) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → x ≠ y → ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
    f (a • x + b • y) < (a : EReal) * f x + (b : EReal) * f y

/-- If $f$ is strictly convex on $C$ and $D \subseteq C$, then $f$ is strictly convex on $D$. -/
theorem StrictConvexOnFn.mono {C D : Set E} (h : StrictConvexOnFn f C) (hDC : D ⊆ C) :
    StrictConvexOnFn f D := fun _ hx _ hy hne _ _ ha hb hab =>
  h (hDC hx) (hDC hy) hne ha hb hab

/-- Let $C$ be a convex set on which $f$ takes neither the value $-\infty$ nor the value $+\infty$.
Then $f$ is strictly convex on $C$ if and only if its real trace $x \mapsto f(x)$ is strictly
convex on $C$ in the sense of Mathlib's `StrictConvexOn`.

This is the way to apply the definition to a concrete function, because Mathlib's results on
strict convexity, such as the second-derivative criteria, are stated for real functions.
Finiteness is needed in both directions. Where $f(x) = +\infty$, the `EReal` inequality is
vacuous and the real one is not. Where $f(x) = -\infty$, the real one is vacuous and the `EReal`
one is not. -/
theorem strictConvexOnFn_iff_strictConvexOn {C : Set E} (hC : Convex ℝ C)
    (hbot : ∀ x ∈ C, f x ≠ ⊥) (htop : ∀ x ∈ C, f x ≠ ⊤) :
    StrictConvexOnFn f C ↔ StrictConvexOn ℝ C (fun x => (f x).toReal) := by
  have hcoe : ∀ x ∈ C, f x = (((f x).toReal : ℝ) : EReal) := fun x hx =>
    (EReal.coe_toReal (htop x hx) (hbot x hx)).symm
  constructor
  · refine fun h => ⟨hC, fun x hx y hy hne a b ha hb hab => ?_⟩
    have hlt := h hx hy hne ha hb hab
    rw [hcoe x hx, hcoe y hy, hcoe _ (hC hx hy ha.le hb.le hab), ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hlt
    simpa using hlt
  · intro h x hx y hy hne a b ha hb hab
    have hlt := h.2 hx hy hne ha hb hab
    rw [hcoe x hx, hcoe y hy, hcoe _ (hC hx hy ha.le hb.le hab), ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    simpa using hlt

/-- Let $\langle \cdot, \cdot \rangle$ be a pairing of $E$ with $F$ and let
$f \colon E \to [-\infty, +\infty]$. The function $f$ is **essentially strictly convex** if it
is strictly convex on every convex set $C \subseteq \operatorname{dom} \partial f$, where
$\operatorname{dom} \partial f$ is the set of points at which $f$ has a subgradient.

For a proper convex $f$, this is weaker than strict convexity on $\operatorname{dom} f$ and
stronger than strict convexity on the relative interior of $\operatorname{dom} f$, and there are
examples that separate it from both. The pairing is the implicit argument `B`, through
`ConvexAnalysis.domSubdifferential B f`. -/
def EssentiallyStrictlyConvex (f : E → EReal) : Prop :=
  ∀ ⦃C : Set E⦄, Convex ℝ C → C ⊆ domSubdifferential B f → StrictConvexOnFn f C

/-- Let $f$ be proper, let $v \in \partial f(x)$ and let $z \in \operatorname{dom} f$. Then
$$f(x) + \langle z - x, v \rangle \le f(z)$$
as an inequality between real numbers. Both values are finite: $f(x)$ because $f$ has a
subgradient at $x$, and $f(z)$ because $z \in \operatorname{dom} f$. -/
theorem sub_le_of_mem_subdifferential (hp : ProperConvex f) {v : F} {x z : E}
    (h : v ∈ subdifferential B f x) (hz : z ∈ convexDom f) :
    (f x).toReal + B (z - x) v ≤ (f z).toReal := by
  have hle := h z
  have hxt : f x ≠ ⊤ := (mem_convexDom.1 (mem_convexDom_of_mem_subdifferential hp h)).ne
  have hzt : f z ≠ ⊤ := (mem_convexDom.1 hz).ne
  rw [← EReal.coe_toReal hxt (hp.ne_bot x), ← EReal.coe_toReal hzt (hp.ne_bot z),
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
  exact hle

/-- Let $f$ be proper and let $x \in \operatorname{dom} f$. If
$f(x) + \langle z - x, v \rangle \le f(z)$ as real numbers for every
$z \in \operatorname{dom} f$, then $v \in \partial f(x)$. Outside $\operatorname{dom} f$, the
subgradient inequality holds because $f(z) = +\infty$. -/
theorem mem_subdifferential_of_forall_sub_le (hp : ProperConvex f) {v : F} {x : E}
    (hx : x ∈ convexDom f)
    (h : ∀ z ∈ convexDom f, (f x).toReal + B (z - x) v ≤ (f z).toReal) : v
        ∈ subdifferential B f x := by
  intro z
  by_cases hz : z ∈ convexDom f
  · rw [← EReal.coe_toReal (mem_convexDom.1 hx).ne (hp.ne_bot x),
      ← EReal.coe_toReal (mem_convexDom.1 hz).ne (hp.ne_bot z), ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    exact h z hz
  · rw [top_le_iff.1 (not_lt.1 fun hlt => hz (mem_convexDom.2 hlt))]
    exact le_top

end Defs

section Segment

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {v : F} {x₁ x₂ : E} {a b : ℝ}

/-- If $a + b = 1$, then for all $z \in E$ and $v \in F$,
$$\langle z - (a x_1 + b x_2), v \rangle = a \langle z - x_1, v \rangle + b \langle z - x_2, v
  \rangle.$$
-/
theorem pairing_sub_combo (hab : a + b = 1) (z : E) :
    B (z - (a • x₁ + b • x₂)) v = a * B (z - x₁) v + b * B (z - x₂) v := by
  have hsplit : z - (a • x₁ + b • x₂) = a • (z - x₁) + b • (z - x₂) := by
    rw [smul_sub, smul_sub]
    match_scalars <;> linarith [hab]
  rw [hsplit, map_add, LinearMap.add_apply, map_smul, map_smul,
    LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]

/-- If $a + b = 1$, then $\langle a x_1 + b x_2 - x_1, v \rangle = b \langle x_2 - x_1, v \rangle$.
-/
theorem pairing_combo_sub_left (hab : a + b = 1) :
    B (a • x₁ + b • x₂ - x₁) v = b * B (x₂ - x₁) v := by
  have hsplit : a • x₁ + b • x₂ - x₁ = b • (x₂ - x₁) := by
    rw [smul_sub]
    match_scalars <;> linarith [hab]
  rw [hsplit, map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- If $a + b = 1$, then $\langle a x_1 + b x_2 - x_2, v \rangle = -a \langle x_2 - x_1, v \rangle$.
-/
theorem pairing_combo_sub_right (hab : a + b = 1) :
    B (a • x₁ + b • x₂ - x₂) v = -(a * B (x₂ - x₁) v) := by
  have hsplit : a • x₁ + b • x₂ - x₂ = (-a) • (x₂ - x₁) := by
    rw [smul_sub]
    match_scalars <;> linarith [hab]
  rw [hsplit, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Let $f$ be a proper convex function on $E$, let $v \in \partial f(x_1) \cap \partial f(x_2)$,
and let $a, b > 0$ with $a + b = 1$. Then
$$v \in \partial f(a x_1 + b x_2).$$
So a subgradient shared by two points is a subgradient at every point of the segment between
them.

Geometrically, the graph of $z \mapsto \langle z, v \rangle - f^*(v)$ is a supporting hyperplane
to the epigraph of $f$ that touches it at both endpoints, so it touches it along the whole
segment. -/
theorem mem_subdifferential_of_combo (hf : ConvexFn f) (hp : ProperConvex f)
    (h₁ : v ∈ subdifferential B f x₁) (h₂ : v ∈ subdifferential B f x₂)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    v ∈ subdifferential B f (a • x₁ + b • x₂) := by
  have hx₁ : x₁ ∈ convexDom f := mem_convexDom_of_mem_subdifferential hp h₁
  have hx₂ : x₂ ∈ convexDom f := mem_convexDom_of_mem_subdifferential hp h₂
  have hcomb : a • x₁ + b • x₂ ∈ convexDom f := hf.convex_convexDom hx₁ hx₂ ha.le hb.le hab
  refine mem_subdifferential_of_forall_sub_le hp hcomb fun z hz => ?_
  -- The combination's value is bounded by the combination of the endpoint values.
  have hcv := (convexFn_iff_le hp.ne_bot).1 hf x₁ x₂ a b ha hb hab
  have hreal : (f (a • x₁ + b • x₂)).toReal ≤ a * (f x₁).toReal + b * (f x₂).toReal := by
    rw [← EReal.coe_toReal (mem_convexDom.1 hx₁).ne (hp.ne_bot x₁),
      ← EReal.coe_toReal (mem_convexDom.1 hx₂).ne (hp.ne_bot x₂),
      ← EReal.coe_toReal (mem_convexDom.1 hcomb).ne (hp.ne_bot _), ← EReal.coe_mul,
      ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at hcv
    exact hcv
  rw [pairing_sub_combo hab z]
  have hA := mul_le_mul_of_nonneg_left (sub_le_of_mem_subdifferential hp h₁ hz) ha.le
  have hB' := mul_le_mul_of_nonneg_left (sub_le_of_mem_subdifferential hp h₂ hz) hb.le
  have hsum : a * (f z).toReal + b * (f z).toReal = (f z).toReal := by
    rw [← add_mul, hab, one_mul]
  linarith

/-- Let $f$ be proper, let $v \in \partial f(x_1) \cap \partial f(x_2)$, let $a, b > 0$ with
$a + b = 1$, and let $a x_1 + b x_2 \in \operatorname{dom} f$. Then
$$a f(x_1) + b f(x_2) \le f(a x_1 + b x_2).$$
For a convex $f$, the convexity inequality on the segment is therefore an equality, so $f$ is
affine on the segment and is not strictly convex there. -/
theorem le_combo_of_mem_subdifferential (hp : ProperConvex f) (h₁ : v ∈ subdifferential B f x₁)
    (h₂ : v ∈ subdifferential B f x₂) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hcomb : a • x₁ + b • x₂ ∈ convexDom f) :
    (a : EReal) * f x₁ + (b : EReal) * f x₂ ≤ f (a • x₁ + b • x₂) := by
  have hx₁ : x₁ ∈ convexDom f := mem_convexDom_of_mem_subdifferential hp h₁
  have hx₂ : x₂ ∈ convexDom f := mem_convexDom_of_mem_subdifferential hp h₂
  have hs₁ := sub_le_of_mem_subdifferential hp h₁ hcomb
  have hs₂ := sub_le_of_mem_subdifferential hp h₂ hcomb
  rw [pairing_combo_sub_left hab] at hs₁
  rw [pairing_combo_sub_right hab] at hs₂
  have hA := mul_le_mul_of_nonneg_left hs₁ ha.le
  have hB' := mul_le_mul_of_nonneg_left hs₂ hb.le
  have hsum : a * (f (a • x₁ + b • x₂)).toReal + b * (f (a • x₁ + b • x₂)).toReal
      = (f (a • x₁ + b • x₂)).toReal := by rw [← add_mul, hab, one_mul]
  rw [← EReal.coe_toReal (mem_convexDom.1 hx₁).ne (hp.ne_bot x₁),
    ← EReal.coe_toReal (mem_convexDom.1 hx₂).ne (hp.ne_bot x₂),
    ← EReal.coe_toReal (mem_convexDom.1 hcomb).ne (hp.ne_bot _), ← EReal.coe_mul,
    ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

/-- Let $f$ be proper, let $x_1, x_2 \in \operatorname{dom} f$, let $a, b > 0$ with $a + b = 1$, and
let $v \in \partial f(a x_1 + b x_2)$. If
$$a f(x_1) + b f(x_2) \le f(a x_1 + b x_2)$$
as real numbers, then $v \in \partial f(x_1)$ and $v \in \partial f(x_2)$. So if $f$ is not
strictly convex between $x_1$ and $x_2$ and has a subgradient at a point between them, that
subgradient is a subgradient at both endpoints.

The two subgradient inequalities at the endpoints add up to the reverse of the hypothesis, so
neither of them can be strict. -/
theorem mem_subdifferential_endpoints_of_le_combo (hp : ProperConvex f) (hx₁ : x₁ ∈ convexDom f)
    (hx₂ : x₂ ∈ convexDom f) (hv : v ∈ subdifferential B f (a • x₁ + b • x₂))
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hle : a * (f x₁).toReal + b * (f x₂).toReal ≤ (f (a • x₁ + b • x₂)).toReal) :
    v ∈ subdifferential B f x₁ ∧ v ∈ subdifferential B f x₂ := by
  have hs₁ := sub_le_of_mem_subdifferential hp hv hx₁
  have hs₂ := sub_le_of_mem_subdifferential hp hv hx₂
  rw [show x₁ - (a • x₁ + b • x₂) = -(a • x₁ + b • x₂ - x₁) by abel, map_neg,
    LinearMap.neg_apply, pairing_combo_sub_left hab] at hs₁
  rw [show x₂ - (a • x₁ + b • x₂) = -(a • x₁ + b • x₂ - x₂) by abel, map_neg,
    LinearMap.neg_apply, pairing_combo_sub_right hab] at hs₂
  have hsum : a * (f (a • x₁ + b • x₂)).toReal + b * (f (a • x₁ + b • x₂)).toReal
      = (f (a • x₁ + b • x₂)).toReal := by rw [← add_mul, hab, one_mul]
  -- Both endpoint inequalities are equalities.
  have he₁ : (f (a • x₁ + b • x₂)).toReal - b * B (x₂ - x₁) v = (f x₁).toReal := by
    refine le_antisymm (by linarith) (le_of_mul_le_mul_left ?_ ha)
    have hB' := mul_le_mul_of_nonneg_left hs₂ hb.le
    linarith
  have he₂ : (f (a • x₁ + b • x₂)).toReal + a * B (x₂ - x₁) v = (f x₂).toReal := by
    refine le_antisymm (by linarith) (le_of_mul_le_mul_left ?_ hb)
    have hA := mul_le_mul_of_nonneg_left hs₁ ha.le
    linarith
  constructor
  · refine mem_subdifferential_of_forall_sub_le hp hx₁ fun z hz => ?_
    have hz' := sub_le_of_mem_subdifferential hp hv hz
    have hlin : B (z - x₁) v = B (z - (a • x₁ + b • x₂)) v + b * B (x₂ - x₁) v := by
      rw [show z - x₁ = (z - (a • x₁ + b • x₂)) + (a • x₁ + b • x₂ - x₁) by abel, map_add,
        LinearMap.add_apply, pairing_combo_sub_left hab]
    rw [hlin, ← he₁]
    linarith
  · refine mem_subdifferential_of_forall_sub_le hp hx₂ fun z hz => ?_
    have hz' := sub_le_of_mem_subdifferential hp hv hz
    have hlin : B (z - x₂) v = B (z - (a • x₁ + b • x₂)) v - a * B (x₂ - x₁) v := by
      rw [show z - x₂ = (z - (a • x₁ + b • x₂)) + (a • x₁ + b • x₂ - x₂) by abel, map_add,
        LinearMap.add_apply, pairing_combo_sub_right hab]
      ring
    rw [hlin, ← he₂]
    linarith

end Segment

section Reformulation

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- Let $\langle \cdot, \cdot \rangle$ be a pairing of $E$ with $F$ and let $f$ be a proper convex
function on $E$. Then $f$ is essentially strictly convex if and only if for all $x_1 \neq x_2$
the subdifferentials $\partial f(x_1)$ and $\partial f(x_2)$ are disjoint.

If two distinct points share a subgradient, the segment between them lies in
$\operatorname{dom} \partial f$ and $f$ is affine on it, so $f$ is not strictly convex there.
Conversely, if $f$ is not strictly convex on a convex set
$C \subseteq \operatorname{dom} \partial f$, then a subgradient at a point between two points of
$C$ is, by `ConvexAnalysis.mem_subdifferential_endpoints_of_le_combo`, a subgradient at both of
them. -/
theorem essentiallyStrictlyConvex_iff_pairwise_disjoint (hf : ConvexFn f) (hp : ProperConvex f) :
    EssentiallyStrictlyConvex (B := B) f ↔
      ∀ x₁ x₂ : E, x₁ ≠ x₂ → Disjoint (subdifferential B f x₁) (subdifferential B f x₂) := by
  constructor
  · intro hes x₁ x₂ hne
    rw [Set.disjoint_left]
    intro v h₁ h₂
    -- The segment lies in `dom ∂f`.
    have hseg : segment ℝ x₁ x₂ ⊆ domSubdifferential B f := by
      rintro _ ⟨a, b, ha, hb, hab, rfl⟩
      rcases eq_or_lt_of_le ha with rfl | ha'
      · have hb1 : b = 1 := by linarith
        subst hb1
        simpa using ⟨v, h₂⟩
      rcases eq_or_lt_of_le hb with rfl | hb'
      · have ha1 : a = 1 := by linarith
        subst ha1
        simpa using ⟨v, h₁⟩
      exact ⟨v, mem_subdifferential_of_combo hf hp h₁ h₂ ha' hb' hab⟩
    have hstrict := hes (convex_segment x₁ x₂) hseg (left_mem_segment ℝ x₁ x₂)
      (right_mem_segment ℝ x₁ x₂) hne (a := 1/2) (b := 1/2) (by norm_num) (by norm_num)
      (by norm_num)
    have hcomb : (1/2 : ℝ) • x₁ + (1/2 : ℝ) • x₂ ∈ convexDom f :=
      hf.convex_convexDom (mem_convexDom_of_mem_subdifferential hp h₁)
          (mem_convexDom_of_mem_subdifferential hp h₂)
        (by norm_num) (by norm_num) (by norm_num)
    exact absurd (le_combo_of_mem_subdifferential hp h₁ h₂ (by norm_num) (by norm_num) (by norm_num)
      hcomb) (not_le.2 hstrict)
  · intro hdisj C hC hCsub x₁ hx₁ x₂ hx₂ hne a b ha hb hab
    by_contra hcon
    push Not at hcon
    have hmem : a • x₁ + b • x₂ ∈ C := hC hx₁ hx₂ ha.le hb.le hab
    obtain ⟨v, hv⟩ := hCsub hmem
    have hx₁d : x₁ ∈ convexDom f := domSubdifferential_subset_convexDom hp (hCsub hx₁)
    have hx₂d : x₂ ∈ convexDom f := domSubdifferential_subset_convexDom hp (hCsub hx₂)
    have hcombd : a • x₁ + b • x₂ ∈ convexDom f := hf.convex_convexDom hx₁d hx₂d ha.le hb.le hab
    have hle : a * (f x₁).toReal + b * (f x₂).toReal ≤ (f (a • x₁ + b • x₂)).toReal := by
      rw [← EReal.coe_toReal (mem_convexDom.1 hx₁d).ne (hp.ne_bot x₁),
        ← EReal.coe_toReal (mem_convexDom.1 hx₂d).ne (hp.ne_bot x₂),
        ← EReal.coe_toReal (mem_convexDom.1 hcombd).ne (hp.ne_bot _), ← EReal.coe_mul,
        ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at hcon
      exact hcon
    obtain ⟨hsub₁, hsub₂⟩ :=
      mem_subdifferential_endpoints_of_le_combo hp hx₁d hx₂d hv ha hb hab hle
    exact (Set.disjoint_left.1 (hdisj x₁ x₂ hne)) hsub₁ hsub₂

end Reformulation

section Conjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- Let $E$ be a finite-dimensional real inner product space and let $f$ be a closed convex function
on $E$. Then for all $u, w \in E$,
$$u \in \partial f^*(w) \iff w \in \partial f(u),$$
so $\partial f^*$ is the inverse of $\partial f$.

The conjugate and both subdifferentials are taken for the pairing `innerₗ E`. The statement is
written with `convexConj (innerₗ E)` so that later rewrites need not deal with the flip of
`innerₗ E`. -/
theorem mem_subdifferential_convexConj_innerL_iff (hf : ConvexFn f) (hcl : ClosedConvex f)
    (u w : E) :
    u ∈ subdifferential (innerₗ E) (convexConj (innerₗ E) f) w ↔ w
        ∈ subdifferential (innerₗ E) f u := by
  have h :=
    mem_subdifferential_convexConj_iff_of_closedConvex (B := innerₗ E) (f := f) (x := u)
        (y := w) hf hcl
  rwa [flip_innerₗ] at h

/-- Let $E$ be a finite-dimensional real inner product space and let $f$ be a closed convex function
on $E$. Then $\partial f^*(w)$ has at most one element for every $w$ if and only if
$\partial f(x_1)$ and $\partial f(x_2)$ are disjoint for all $x_1 \neq x_2$. That is,
$\partial f^*$ is single-valued if and only if $\partial f$ is injective. -/
theorem subsingleton_subdifferential_convexConj_iff (hf : ConvexFn f) (hcl : ClosedConvex f) :
    (∀ w : E, (subdifferential (innerₗ E) (convexConj (innerₗ E) f) w).Subsingleton) ↔
      ∀ x₁ x₂ : E, x₁ ≠ x₂ →
        Disjoint (subdifferential (innerₗ E) f x₁) (subdifferential (innerₗ E) f x₂) := by
  constructor
  · intro h x₁ x₂ hne
    rw [Set.disjoint_left]
    intro v hv₁ hv₂
    exact hne (h v ((mem_subdifferential_convexConj_innerL_iff hf hcl x₁ v).2 hv₁)
      ((mem_subdifferential_convexConj_innerL_iff hf hcl x₂ v).2 hv₂))
  · intro h v x₁ hx₁ x₂ hx₂
    by_contra hne
    exact (Set.disjoint_left.1 (h x₁ x₂ hne))
      ((mem_subdifferential_convexConj_innerL_iff hf hcl x₁ v).1 hx₁)
      ((mem_subdifferential_convexConj_innerL_iff hf hcl x₂ v).1 hx₂)

/-- Let $E$ be a finite-dimensional real inner product space and let $f$ be a closed convex function
on $E$. Then $\partial f^*(y_1)$ and $\partial f^*(y_2)$ are disjoint for all $y_1 \neq y_2$ if
and only if $\partial f(z)$ has at most one element for every $z$. That is, $\partial f^*$ is
injective if and only if $\partial f$ is single-valued. This is the mirror image of
`ConvexAnalysis.subsingleton_subdifferential_convexConj_iff`. -/
theorem pairwise_disjoint_subdifferential_convexConj_iff (hf : ConvexFn f) (hcl : ClosedConvex f) :
    (∀ y₁ y₂ : E, y₁ ≠ y₂ →
        Disjoint (subdifferential (innerₗ E) (convexConj (innerₗ E) f) y₁)
          (subdifferential (innerₗ E) (convexConj (innerₗ E) f) y₂)) ↔
      ∀ z : E, (subdifferential (innerₗ E) f z).Subsingleton := by
  constructor
  · intro h z y₁ hy₁ y₂ hy₂
    by_contra hne
    exact (Set.disjoint_left.1 (h y₁ y₂ hne))
      ((mem_subdifferential_convexConj_innerL_iff hf hcl z y₁).2 hy₁)
      ((mem_subdifferential_convexConj_innerL_iff hf hcl z y₂).2 hy₂)
  · intro h y₁ y₂ hne
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    exact hne (h z ((mem_subdifferential_convexConj_innerL_iff hf hcl z y₁).1 hz₁)
      ((mem_subdifferential_convexConj_innerL_iff hf hcl z y₂).1 hz₂))

/-- Let $E$ be a finite-dimensional real inner product space and let $f$ be a closed proper convex
function on $E$. Then the conjugate $f^*$ is essentially smooth if and only if $f$ is
essentially strictly convex.

This is one direction of Theorem 26.3 of [rockafellar1970convex]. The conjugate and the
subdifferentials are taken for the pairing `innerₗ E`. The proof combines
`ConvexAnalysis.subsingleton_subdifferential_convexConj_iff` with
`ConvexAnalysis.essentiallyStrictlyConvex_iff_pairwise_disjoint` and the characterization of
essential smoothness by single-valued subdifferentials. -/
theorem essentiallySmooth_convexConj_iff_essentiallyStrictlyConvex (hf : ConvexFn f)
    (hp : ProperConvex f)
    (hcl : ClosedConvex f) :
    EssentiallySmooth (convexConj (innerₗ E) f) ↔ EssentiallyStrictlyConvex (B := innerₗ E) f := by
  have hcp : ClosedProperConvexFn f := ⟨hf, hcl, hp⟩
  have hgc : ConvexFn (convexConj (innerₗ E) f) := convexFn_convexConj _ f
  have hgp : ProperConvex (convexConj (innerₗ E) f) := properConvex_convexConj hcp
  have hgcl : ClosedConvex (convexConj (innerₗ E) f) := closedConvex_convexConj
  rw [← subsingleton_subdifferential_iff_essentiallySmooth hgc hgp hgcl,
    essentiallyStrictlyConvex_iff_pairwise_disjoint hf hp,
    subsingleton_subdifferential_convexConj_iff hf hcl]

/-- Let $E$ be a finite-dimensional real inner product space and let $f$ be a closed convex function
on $E$. Then $f^{**} = f$, where both conjugates are taken for the pairing `innerₗ E`. -/
theorem convexConj_convexConj_innerL (hf : ConvexFn f) (hcl : ClosedConvex f) :
    convexConj (innerₗ E) (convexConj (innerₗ E) f) = f := by
  have h : convexConj ((innerₗ E).flip) (convexConj (innerₗ E) f) = f := convexBiconj_eq_self hf hcl
  rwa [flip_innerₗ] at h

/-- Let $E$ be a finite-dimensional real inner product space and let $f$ be a closed proper convex
function on $E$. Then $f^*$ is essentially strictly convex if and only if $f$ is essentially
smooth.

This is the other direction of Theorem 26.3 of [rockafellar1970convex]. It is
`ConvexAnalysis.essentiallySmooth_convexConj_iff_essentiallyStrictlyConvex` applied to $f^*$,
together with $f^{**} = f$. -/
theorem essentiallyStrictlyConvex_convexConj_iff_essentiallySmooth (hf : ConvexFn f)
    (hp : ProperConvex f)
    (hcl : ClosedConvex f) :
    EssentiallyStrictlyConvex (B := innerₗ E) (convexConj (innerₗ E) f) ↔ EssentiallySmooth f := by
  rw [← essentiallySmooth_convexConj_iff_essentiallyStrictlyConvex (convexFn_convexConj _ f)
    (properConvex_convexConj ⟨hf, hcl, hp⟩) closedConvex_convexConj,
        convexConj_convexConj_innerL hf hcl]

/-- Let $E$ be a finite-dimensional real inner product space and let $f$ be a closed proper convex
function on $E$. Then the following are equivalent:

* $\partial f$ is single-valued and injective: $\partial f(z)$ has at most one element for every
  $z$, and $\partial f(x_1)$, $\partial f(x_2)$ are disjoint for all $x_1 \neq x_2$;
* $f$ is essentially smooth and strictly convex on $\operatorname{int}(\operatorname{dom} f)$.

If $f$ is essentially smooth, then $\operatorname{dom} \partial f =
\operatorname{int}(\operatorname{dom} f)$, so essential strict convexity, which is about all
convex subsets of $\operatorname{dom} \partial f$, reduces to strict convexity on this one
convex set. -/
theorem subdifferential_injective_iff (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) :
    ((∀ z : E, (subdifferential (innerₗ E) f z).Subsingleton) ∧
        ∀ x₁ x₂ : E, x₁ ≠ x₂ →
          Disjoint (subdifferential (innerₗ E) f x₁) (subdifferential (innerₗ E) f x₂)) ↔
      (EssentiallySmooth f ∧ StrictConvexOnFn f (interior (convexDom f))) := by
  have hdom : Convex ℝ (convexDom f) := hf.convex_convexDom
  rw [subsingleton_subdifferential_iff_essentiallySmooth hf hp hcl,
    ← essentiallyStrictlyConvex_iff_pairwise_disjoint hf hp]
  refine and_congr_right fun hes => ⟨fun h => ?_, fun h => ?_⟩
  · refine h hdom.interior fun z hz => ?_
    rw [mem_domSubdifferential, subdifferential_eq_singleton_of_essentiallySmooth hf hes hz]
    exact Set.singleton_nonempty _
  · refine fun C hC hCsub => h.mono fun z hz => ?_
    by_contra hzint
    obtain ⟨v, hv⟩ := hCsub hz
    rw [subdifferential_eq_empty_of_essentiallySmooth hf hp hcl hes hzint] at hv
    exact absurd hv (Set.notMem_empty v)

end Conjugate

end ConvexAnalysis
