/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Exact
import Numlib.Analysis.Convex.Subdifferential.Defs

/-!
# Subdifferential calculus

Let $E$ and $F$ be real vector spaces paired by a bilinear form $\langle x, y \rangle$. This module
computes the subdifferential of a sum $f_1 + \dots + f_m$, of an inverse image
$gA : x \mapsto g(Ax)$ under a linear map $A$, of a positive multiple $cf$, of an affine function,
and of the indicator function of an intersection. Each rule has one inclusion that holds for all
functions: subgradients of the pieces assemble into a subgradient of the whole, for example
$\partial f(x) + \partial g(x) \subseteq \partial (f + g)(x)$. The reverse inclusion, the useful
one, needs the constraint qualification that makes the corresponding rule for conjugates exact, for
example $(f + g)^* = f^* \mathbin{\square} g^*$ with attainment. The rules are therefore stated for
the interfaces `ConvexAnalysis.IsExactSum`, `ConvexAnalysis.IsExactFinsetSum` and
`ConvexAnalysis.IsExactImage`. The classical versions with relative interiors follow with the
constructors `ConvexAnalysis.IsExactSum.of_relint`, `ConvexAnalysis.IsExactFinsetSum.of_relint` and
`ConvexAnalysis.IsExactImage.of_relint`. The presentation follows [rockafellar1970convex], §23.

## Main results

* `ConvexAnalysis.IsExactSum.subdifferential_add`,
  `ConvexAnalysis.IsExactFinsetSum.subdifferential_finsetSum`: $\partial (f_1 + \dots + f_m)(x) =
  \partial f_1(x) + \dots + \partial f_m(x)$ when the sum is exact, for two summands and for $m$
  summands. This is Theorem 23.8 of [rockafellar1970convex].
* `ConvexAnalysis.IsExactImage.subdifferential_compLin`: $\partial (gA)(x) = A^* \partial g(Ax)$
  when the inverse image is exact. This is Theorem 23.9 of [rockafellar1970convex].
* `ConvexAnalysis.subdifferential_coe_mul`, `ConvexAnalysis.subdifferential_coe_affineMap`:
  $\partial (cf)(x) = c \, \partial f(x)$ for $c > 0$, and the subdifferential of an affine function
  is the single vector that represents its linear part.
* `ConvexAnalysis.IsExactSum.normalCone_inter`: the normal cone to an intersection is the sum of the
  normal cones.
* `ConvexAnalysis.subdifferential_add_normalCone_convexDom_subset`,
  `ConvexAnalysis.normalCone_convexDom_eq_zero_of_subdifferential_eq_singleton`: a normal vector to
  $\operatorname{dom} f$ can be added to a subgradient, so a unique subgradient forces the normal
  cone to $\operatorname{dom} f$ to be $\{0\}$.

## Implementation notes

* Every proof reduces to the conjugate characterization $y \in \partial f(x) \iff f(x) + f^*(y) \le
  \langle x, y \rangle$, which never meets $\infty - \infty$. No epigraph, directional derivative or
  separating hyperplane appears in the proofs.
* The sum rule also needs the fact that two inequalities in `EReal` whose sum holds with equality
  each hold with equality. This is where the properness carried by `ConvexAnalysis.IsExactSum` is
  used.
* The rule for $m$ summands is proved for the whole family at once, not by iteration of the rule for
  two summands: `EReal` has no subtraction that would remove one summand.
* The adjoint $A^* : H \to F$ of $A : E \to G$, for pairings of $E$ with $F$ and of $G$ with $H$, is
  data: `ConvexAnalysis.IsAdjointPair B B' A A'` states $\langle Ax, z \rangle' = \langle x, A^* z
  \rangle$.
-/

open Pointwise

namespace ConvexAnalysis

/-! ### Sums -/

section Add

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- **The inclusion that always holds** for sums: for all $f, g : E \to [-\infty, +\infty]$ and
$x \in E$,
$$\partial f(x) + \partial g(x) \subseteq \partial (f + g)(x).$$
The two subgradient inequalities add. -/
theorem subdifferential_add_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) (x : E) :
    subdifferential B f x + subdifferential B g x ⊆ subdifferential B (f + g) x := by
  rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩ z
  have h₁ := hy₁ z
  have h₂ := hy₂ z
  rw [Pi.add_apply, Pi.add_apply, map_add, EReal.coe_add, add_add_add_comm]
  exact add_le_add h₁ h₂

/-- **Subdifferential of a sum.** Let $f, g : E \to [-\infty, +\infty]$ add exactly: both are
proper, and for every $y \in F$ the infimal convolution that defines
$(f^* \mathbin{\square} g^*)(y)$ is attained, so that $(f + g)^*(y) = f^*(y_1) + g^*(y_2)$ for
some $y_1 + y_2 = y$. Then for every $x \in E$
$$\partial (f + g)(x) = \partial f(x) + \partial g(x).$$

This is Theorem 23.8 of [rockafellar1970convex], with the hypothesis on relative interiors
replaced by its consequence `ConvexAnalysis.IsExactSum`. The classical hypothesis gives this
interface through `ConvexAnalysis.IsExactSum.of_relint`. For $y \in \partial (f + g)(x)$,
exactness gives a splitting $y = y_1 + y_2$, and equality in Fenchel's inequality for $f + g$
forces equality in the inequalities for $f$ at $y_1$ and for $g$ at $y_2$. -/
theorem IsExactSum.subdifferential_add (h : IsExactSum B f g) (x : E) :
    subdifferential B (f + g) x = subdifferential B f x + subdifferential B g x := by
  refine Set.Subset.antisymm (fun y hy => ?_) (subdifferential_add_subset B f g x)
  obtain ⟨y₁, y₂, rfl, hle⟩ := h.exact_le y
  have hy' := mem_subdifferential_iff_add_convexConj_le.1 hy
  rw [Pi.add_apply] at hy'
  have hkey : (f x + convexConj B f y₁) + (g x + convexConj B g y₂)
      ≤ ((B x y₁ + B x y₂ : ℝ) : EReal) := by
    calc (f x + convexConj B f y₁) + (g x + convexConj B g y₂)
        = (f x + g x) + (convexConj B f y₁ + convexConj B g y₂) := (add_add_add_comm _ _ _ _).symm
      _ ≤ (f x + g x) + convexConj B (f + g) (y₁ + y₂) := add_le_add le_rfl hle
      _ ≤ ((B x (y₁ + y₂) : ℝ) : EReal) := hy'
      _ = ((B x y₁ + B x y₂ : ℝ) : EReal) := by rw [map_add]
  have hkey' : (g x + convexConj B g y₂) + (f x + convexConj B f y₁)
      ≤ ((B x y₂ + B x y₁ : ℝ) : EReal) := by
    rw [add_comm (g x + convexConj B g y₂), add_comm (B x y₂)]
    exact hkey
  have hf := h.properConvex_left.le_add_convexConj (B := B) x y₁
  have hg := h.properConvex_right.le_add_convexConj (B := B) x y₂
  exact ⟨y₁, mem_subdifferential_iff_add_convexConj_le.2
      (EReal.le_coe_of_add_le_coe_add hf hg hkey),
    y₂, mem_subdifferential_iff_add_convexConj_le.2
      (EReal.le_coe_of_add_le_coe_add hg hf hkey'), rfl⟩

end Add

/-! ### Sums of $m$ functions -/

section FinsetAdd

variable {ι E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Finset ι} {f : ι → E → EReal}

/-- **The inclusion that always holds** for $m$ summands: for every finite family $(f_i)_{i \in s}$
and every $x$,
$$\partial f_1(x) + \dots + \partial f_m(x) \subseteq \partial (f_1 + \dots + f_m)(x).$$
For the empty family the left side is $\{0\}$ and the right side is $\partial 0(x)$, which
contains $0$. -/
theorem subdifferential_finsetSum_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Finset ι)
    (f : ι → E → EReal) (x : E) :
    ∑ i ∈ s, subdifferential B (f i) x ⊆ subdifferential B (∑ i ∈ s, f i) x := by
  induction s using Finset.cons_induction with
  | empty =>
    intro y hy
    simp only [Finset.sum_empty, Set.mem_zero] at hy
    subst hy
    simp [mem_subdifferential]
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (Set.add_subset_add_left ih).trans (subdifferential_add_subset B (f i) _ x)

/-- **Subdifferential of a finite sum.** Let $(f_i)_{i \in s}$ be a finite family of functions
$E \to [-\infty, +\infty]$ that adds exactly: every $f_i$ is proper, and for every $y \in F$ the
$m$-fold infimal convolution that defines $(f_1^* \mathbin{\square} \dots \mathbin{\square}
f_m^*)(y)$ is attained. Then for every $x \in E$
$$\partial \Big(\sum_{i \in s} f_i\Big)(x) = \sum_{i \in s} \partial f_i(x).$$

This is Theorem 23.8 of [rockafellar1970convex], with the hypothesis on relative interiors
replaced by `ConvexAnalysis.IsExactFinsetSum`, which `ConvexAnalysis.IsExactFinsetSum.of_relint`
supplies. Exactness gives a splitting $y = y_1 + \dots + y_m$ whose conjugate values add up to
$(\sum_i f_i)^*(y)$, and $y \in \partial (\sum_i f_i)(x)$ makes the sum of the $m$ Fenchel
inequalities an equality, hence each of them. The proof does not iterate the rule for two
summands. -/
theorem IsExactFinsetSum.subdifferential_finsetSum (h : IsExactFinsetSum B s f) (x : E) :
    subdifferential B (∑ i ∈ s, f i) x = ∑ i ∈ s, subdifferential B (f i) x := by
  refine Set.Subset.antisymm (fun y hy => ?_) (subdifferential_finsetSum_subset B s f x)
  obtain ⟨y', hy', hle⟩ := h.exact_le y
  have hfen : ∀ i ∈ s, ((B x (y' i) : ℝ) : EReal) ≤ f i x + convexConj B (f i) (y' i) :=
    fun i hi => (h.proper i hi).le_add_convexConj x (y' i)
  have hsum : ∑ i ∈ s, (f i x + convexConj B (f i) (y' i))
      ≤ ((∑ i ∈ s, B x (y' i) : ℝ) : EReal) := by
    calc ∑ i ∈ s, (f i x + convexConj B (f i) (y' i))
        = (∑ i ∈ s, f i) x + ∑ i ∈ s, convexConj B (f i) (y' i) := by
          rw [Finset.sum_add_distrib, Finset.sum_apply]
      _ ≤ (∑ i ∈ s, f i) x + convexConj B (∑ i ∈ s, f i) y := add_le_add le_rfl hle
      _ ≤ ((B x y : ℝ) : EReal) := mem_subdifferential_iff_add_convexConj_le.1 hy
      _ = ((∑ i ∈ s, B x (y' i) : ℝ) : EReal) := by rw [← hy', map_sum]
  have hmem : ∀ i ∈ s, y' i ∈ subdifferential B (f i) x := fun i hi =>
    mem_subdifferential_iff_add_convexConj_le.2
      (EReal.le_coe_of_sum_le_coe_sum (c := fun i => B x (y' i))
        (u := fun i => f i x + convexConj B (f i) (y' i)) hfen hsum hi)
  have hgoal := Set.finsetSum_mem_finsetSum s (fun i => subdifferential B (f i) x) y' hmem
  rwa [hy'] at hgoal

end FinsetAdd

/-! ### Linear maps -/

section Image

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

/-- **The inclusion that always holds** for inverse images. Let $A : E \to G$ be linear with adjoint
$A^* : H \to F$. For every $g : G \to [-\infty, +\infty]$ and $x \in E$, $A^*$ maps subgradients
of $g$ at $Ax$ to subgradients of $gA$ at $x$:
$$A^* \partial g(Ax) \subseteq \partial (gA)(x).$$
-/
theorem image_subdifferential_subset (hA : IsAdjointPair B B' A A') (g : G → EReal) (x : E) :
    A' '' subdifferential B' g (A x) ⊆ subdifferential B (compLin g A) x := by
  rintro _ ⟨z, hz, rfl⟩ w
  have hw := hz (A w)
  rwa [compLin_apply, compLin_apply, ← hA (w - x) z, map_sub]

/-- **Subdifferential of an inverse image.** Let $E$ be paired with $F$ and $G$ with $H$, let
$A : E \to G$ be linear with adjoint $A^* : H \to F$, and let $g : G \to [-\infty, +\infty]$
pull back exactly along $A$: $g$ is proper, and wherever $(gA)^*(y)$ is finite, the infimum of
$g^*$ over $\{z \mid A^* z = y\}$ is attained at a point $z$ with $g^*(z) \le (gA)^*(y)$. Then
for every $x \in E$
$$\partial (gA)(x) = A^* \partial g(Ax).$$

This is Theorem 23.9 of [rockafellar1970convex], with the hypothesis on relative interiors
replaced by `ConvexAnalysis.IsExactImage`, which `ConvexAnalysis.IsExactImage.of_relint`
supplies. The inverse image $gA$ is `ConvexAnalysis.compLin g A`. A subgradient at $x$ makes
$(gA)^*(y)$ finite, and the point $z$ given by exactness then satisfies Fenchel's inequality for
$g$ with equality. -/
theorem IsExactImage.subdifferential_compLin {hA : IsAdjointPair B B' A A'}
    (h : IsExactImage B B' A A' hA g) (x : E) :
    subdifferential B (compLin g A) x = A' '' subdifferential B' g (A x) := by
  refine Set.Subset.antisymm (fun y hy => ?_) (image_subdifferential_subset hA g x)
  have hne : compLin g A x ≠ ⊥ := by rw [compLin_apply]; exact h.proper.ne_bot (A x)
  have hfin : convexConj B (compLin g A) y < ⊤ := by
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    have hsub := mem_subdifferential_iff_add_convexConj_le.1 hy
    rw [htop, EReal.add_top_of_ne_bot hne, top_le_iff] at hsub
    exact absurd hsub (EReal.coe_ne_top _)
  obtain ⟨z, rfl, hle⟩ := h.exact_le y hfin
  refine ⟨z, mem_subdifferential_iff_add_convexConj_le.2 ?_, rfl⟩
  calc g (A x) + convexConj B' g z
      ≤ g (A x) + convexConj B (compLin g A) (A' z) := add_le_add le_rfl hle
    _ = compLin g A x + convexConj B (compLin g A) (A' z) := by rw [compLin_apply]
    _ ≤ ((B x (A' z) : ℝ) : EReal) := mem_subdifferential_iff_add_convexConj_le.1 hy
    _ = ((B' (A x) z : ℝ) : EReal) := by rw [hA x z]

end Image

/-! ### Scalar multiples -/

section Smul

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

/-- Let $c > 0$. For every $f : E \to [-\infty, +\infty]$ and $x \in E$,
$$\partial (cf)(x) = c \, \partial f(x).$$
Multiplication of the subgradient inequality by $c > 0$ can be undone, also in `EReal`.

Positivity is needed for both inclusions. At $c = 0$ the left side is $\{y \mid \langle w, y
\rangle = 0 \text{ for all } w\}$, which has no relation to $\partial f(x)$. For $c < 0$ the
inequality reverses, and $cf$ is concave where $f$ is convex. The case $c < 0$ holds only for
affine $f$ (`ConvexAnalysis.subdifferential_coe_mul_affineMap`). -/
theorem subdifferential_coe_mul {c : ℝ} (hc : 0 < c) (f : E → EReal) (x : E) :
    subdifferential B (fun y => (c : EReal) * f y) x = c • subdifferential B f x := by
  ext v
  constructor
  · intro hv
    refine ⟨c⁻¹ • v, fun z => ?_, ?_⟩
    swap
    · change c • (c⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    have h1 := hv z
    have hp : B (z - x) (c⁻¹ • v) = c⁻¹ * B (z - x) v := by rw [map_smul, smul_eq_mul]
    rw [hp]
    refine (EReal.coe_mul_add_coe_le_coe_mul_iff hc (f x) (f z) _).1 ?_
    rw [show c * (c⁻¹ * B (z - x) v) = B (z - x) v from by field_simp]
    exact h1
  · rintro ⟨w, hw, rfl⟩
    intro z
    have hp : B (z - x) (c • w) = c * B (z - x) w := by rw [map_smul, smul_eq_mul]
    rw [hp]
    exact (EReal.coe_mul_add_coe_le_coe_mul_iff hc (f x) (f z) _).2 (hw z)

/-- Let the pairing separate the points of $F$: $\langle w, y \rangle = 0$ for all $w$ implies
$y = 0$. Then for every $f : E \to [-\infty, +\infty]$ and $x$, the subdifferential of
$0 \cdot f$ at $x$ is $\{0\}$. Here $0 \cdot f$ is computed in `EReal`, where
$0 \cdot (\pm\infty) = 0$.

This explains the remark "Omit terms with $\lambda_i = 0$" in the Kuhn–Tucker conditions, and
why it matters. The set $\partial f_i(x)$ can be empty at a boundary point of
$\operatorname{dom} f_i$, and then the term $0 \cdot \partial f_i(x)$ would be $\emptyset$, not
$\{0\}$, and would make the whole sum empty. -/
theorem subdifferential_zero_mul (hB : Function.Injective B.flip) (f : E → EReal) (x : E) :
    subdifferential B (fun y => ((0 : ℝ) : EReal) * f y) x = {(0 : F)} := by
  have hz : (fun y => ((0 : ℝ) : EReal) * f y) = fun _ : E => (0 : EReal) := by
    funext y; rw [EReal.coe_zero, zero_mul]
  rw [hz]
  ext v
  rw [Set.mem_singleton_iff]
  constructor
  · intro hv
    have hle : ∀ w : E, B w v ≤ 0 := by
      intro w
      have h := hv (x + w)
      rw [add_sub_cancel_left, zero_add] at h
      have h' : ((B w v : ℝ) : EReal) ≤ (0 : EReal) := h
      exact_mod_cast h'
    refine hB (LinearMap.ext fun w => ?_)
    change B w v = B w 0
    rw [map_zero]
    refine le_antisymm (hle w) ?_
    have hneg := hle (-w)
    rw [map_neg B w, LinearMap.neg_apply] at hneg
    linarith
  · rintro rfl
    intro z
    rw [zero_add, map_zero]
    exact le_of_eq (by norm_num)

/-- Let the pairing separate the points of $F$, let $a : E \to \mathbb{R}$ be affine, and let
$b \in F$ represent its linear part: $\langle w, b \rangle = a(w) - a(0)$ for all $w$. Then for
every $x \in E$
$$\partial a(x) = \{b\}.$$

No differentiation and no topology are needed: the vector $b$ is given, together with the
identity $\langle w, b \rangle = $ `a.linear w`. Separation of points is
`Function.Injective B.flip`. -/
theorem subdifferential_coe_affineMap (hB : Function.Injective B.flip) (a : E →ᵃ[ℝ] ℝ) {b : F}
    (hb : ∀ w : E, B w b = a.linear w) (x : E) :
    subdifferential B (fun y => ((a y : ℝ) : EReal)) x = {b} := by
  have hdec : ∀ z : E, a z - a x = a.linear (z - x) := by
    intro z
    have h1 : ∀ y : E, a y = a.linear y + a 0 := fun y => congrFun (AffineMap.decomp a) y
    rw [h1 z, h1 x, map_sub]
    ring
  ext v
  rw [Set.mem_singleton_iff]
  constructor
  · intro hv
    have hle : ∀ w : E, B w v ≤ a.linear w := by
      intro w
      have h := hv (w + x)
      rw [add_sub_cancel_right, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
      have hd := hdec (w + x)
      rw [add_sub_cancel_right] at hd
      linarith
    refine hB (LinearMap.ext fun w => ?_)
    change B w v = B w b
    rw [hb w]
    refine le_antisymm (hle w) ?_
    have hneg := hle (-w)
    rw [map_neg B w, LinearMap.neg_apply, map_neg a.linear w] at hneg
    linarith
  · rintro rfl
    intro z
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, hb (z - x)]
    linarith [hdec z]

/-- Let the pairing separate the points of $F$, let $a : E \to \mathbb{R}$ be affine with linear
part represented by $b \in F$, and let $c$ be any real number. Then
$\partial (ca)(x) = c \, \partial a(x)$ for every $x$.

An affine function satisfies the subgradient inequality with equality, so a negative $c$
reverses nothing. This case covers the multipliers of equality constraints, which can be
negative. -/
theorem subdifferential_coe_mul_affineMap (hB : Function.Injective B.flip) (c : ℝ) (a : E →ᵃ[ℝ] ℝ)
    {b : F} (hb : ∀ w : E, B w b = a.linear w) (x : E) :
    subdifferential B (fun y => (c : EReal) * ((a y : ℝ) : EReal)) x
      = c • subdifferential B (fun y => ((a y : ℝ) : EReal)) x := by
  have hfun : (fun y => (c : EReal) * ((a y : ℝ) : EReal))
      = fun y => (((c • a) y : ℝ) : EReal) := by
    funext y
    rw [← EReal.coe_mul]
    rfl
  have hb' : ∀ w : E, B w (c • b) = (c • a).linear w := by
    intro w
    rw [map_smul, smul_eq_mul, hb w]
    rfl
  rw [hfun, subdifferential_coe_affineMap hB (c • a) hb' x, subdifferential_coe_affineMap hB a hb x,
    Set.smul_set_singleton]

end Smul

/-! ### Normal cones to an intersection -/

section NormalCone

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C D : Set E} {x : E}

/-- **The inclusion that always holds** for normal cones: for all sets $C, D \subseteq E$ and every
$x \in E$,
$$N_C(x) + N_D(x) \subseteq N_{C \cap D}(x).$$
The proof is direct, not through indicator functions, so it needs neither $x \in C$ nor
$x \in D$. -/
theorem normalCone_add_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C D : Set E) (x : E) :
    normalCone B C x + normalCone B D x ⊆ normalCone B (C ∩ D) x := by
  rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩ z hz
  rw [map_add]
  exact add_nonpos (hy₁ z hz.1) (hy₂ z hz.2)

/-- Let the indicator functions $\delta(\cdot \mid C)$ and $\delta(\cdot \mid D)$ add exactly
(`ConvexAnalysis.IsExactSum`), and let $x \in C \cap D$. Then
$$N_{C \cap D}(x) = N_C(x) + N_D(x).$$

The proof applies `ConvexAnalysis.IsExactSum.subdifferential_add` to the two indicator
functions. -/
theorem IsExactSum.normalCone_inter (h : IsExactSum B (indicatorFn C) (indicatorFn D))
    (hC : x ∈ C) (hD : x ∈ D) :
    normalCone B (C ∩ D) x = normalCone B C x + normalCone B D x := by
  have hsum := h.subdifferential_add x
  rwa [indicatorFn_add, subdifferential_indicatorFn (Set.mem_inter hC hD),
    subdifferential_indicatorFn hC,
    subdifferential_indicatorFn hD] at hsum

end NormalCone

/-! ### The normal cone to the effective domain -/

section NormalConeDom

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E}

/-- For every $f : E \to [-\infty, +\infty]$ and $x \in E$, a normal vector to
$\operatorname{dom} f$ at $x$ can be added to a subgradient at $x$:
$$\partial f(x) + N_{\operatorname{dom} f}(x) \subseteq \partial f(x).$$

This is the elementary inclusion behind the equation $\partial f(x) + N_{\operatorname{dom}
f}(x) = \partial f(x)$. Neither convexity nor a topology is needed. -/
theorem subdifferential_add_normalCone_convexDom_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal)
    (x : E) :
    subdifferential B f x + normalCone B (convexDom f) x ⊆ subdifferential B f x := by
  rintro _ ⟨y, hy, n, hn, rfl⟩ z
  by_cases hz : z ∈ convexDom f
  · have hle : ((B (z - x) (y + n) : ℝ) : EReal) ≤ ((B (z - x) y : ℝ) : EReal) := by
      rw [map_add, EReal.coe_le_coe_iff]
      linarith [hn z hz]
    exact (add_le_add (le_refl (f x)) hle).trans (hy z)
  · rw [top_le_iff.1 (not_lt.1 fun h => hz (mem_convexDom.2 h))]
    exact le_top

/-- Let $f : E \to [-\infty, +\infty]$ and $x \in E$. If $\partial f(x) = \{y_0\}$ is a single
point, then
$$N_{\operatorname{dom} f}(x) = \{0\}.$$

For every normal vector $n$ to $\operatorname{dom} f$ at $x$, the vector $y_0 + n$ is again a
subgradient, so $n = 0$. With `ConvexAnalysis.mem_interior_of_normalCone_eq_zero` this turns
uniqueness of the subgradient into the statement that $x$ is an interior point of
$\operatorname{dom} f$. -/
theorem normalCone_convexDom_eq_zero_of_subdifferential_eq_singleton {y₀ : F}
    (h : subdifferential B f x = {y₀}) : normalCone B (convexDom f) x = {0} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨fun z _ => by simp, fun n hn => ?_⟩
  have hy₀ : y₀ ∈ subdifferential B f x := by rw [h]; rfl
  have hmem := subdifferential_add_normalCone_convexDom_subset B f x (Set.add_mem_add hy₀ hn)
  rw [h, Set.mem_singleton_iff] at hmem
  simpa using hmem

end NormalConeDom

/-!
### Transport along a linear isomorphism

`ConvexAnalysis.convexConj_comp_linearEquiv` is the substitution rule for the conjugate. The
subdifferential obeys the same rule, for every adjoint pair of linear isomorphisms.
-/

section LinearEquivTransport

variable {E F G H : Type*}
variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]

/-- **Composition with a linear isomorphism.** Let $E$ be paired with $F$ and $G$ with $H$, and let
$A : E \to G$ and $A^* : H \to F$ be linear isomorphisms that are adjoint: $\langle Ax, z
\rangle' = \langle x, A^* z \rangle$. Then for every $g : G \to [-\infty, +\infty]$ and
$x \in E$,
$$\partial (g \circ A)(x) = A^* \partial g(Ax).$$
This is the counterpart for subdifferentials of `ConvexAnalysis.convexConj_comp_linearEquiv`. No
exactness hypothesis is needed. -/
theorem subdifferential_comp_linearEquiv {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
    (A : E ≃ₗ[ℝ] G) (A' : H ≃ₗ[ℝ] F)
    (hA : IsAdjointPair B B' (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F)) (g : G → EReal) (x : E) :
    subdifferential B (fun u => g (A u)) x = A' '' subdifferential B' g (A x) := by
  ext y
  constructor
  · intro hy
    refine ⟨A'.symm y, fun w => ?_, A'.apply_symm_apply y⟩
    have hw : g (A x) + ((B (A.symm w - x) y : ℝ) : EReal) ≤ g (A (A.symm w)) := hy (A.symm w)
    rw [LinearEquiv.apply_symm_apply] at hw
    have h2 := hA (A.symm w - x) (A'.symm y)
    simp only [LinearEquiv.coe_coe] at h2
    have h1 : A (A.symm w - x) = w - A x := by simp
    have h3 : A' (A'.symm y) = y := A'.apply_symm_apply y
    rw [h1, h3] at h2
    rw [h2]
    exact hw
  · rintro ⟨v, hv, rfl⟩
    intro w
    have hw : g (A x) + ((B' (A w - A x) v : ℝ) : EReal) ≤ g (A w) := hv (A w)
    have h2 := hA (w - x) v
    simp only [LinearEquiv.coe_coe] at h2
    have h1 : A (w - x) = A w - A x := map_sub A w x
    rw [h1] at h2
    rw [← h2]
    exact hw

end LinearEquivTransport

end ConvexAnalysis
