/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Subdifferential.Differentiability
import Numlib.Analysis.Convex.Subdifferential.GradientLimit
import Numlib.Analysis.Convex.Subdifferential.Reconstruction
import NumlibSurface.Rockafellar.Common.Euclidean

/-!
# Rockafellar, Section 25: Differentiability of convex functions

This module formalizes Section 25 of [rockafellar1970convex], on the relation between the
subdifferential $\partial f$ of a convex function $f$ on $\mathbb{R}^n$ and its gradient $\nabla f$.
Theorem 25.1 shows that $f$ is differentiable at a point $x$ exactly when $\partial f(x)$ consists
of a single vector, and then $\partial f(x) = \{\nabla f(x)\}$. Theorem 25.2 characterizes
differentiability at $x$ by linearity of the directional derivative $f'(x; \cdot)$. Theorems
25.3–25.5 show that a proper convex function is differentiable on a dense subset $D$ of
$\operatorname{int}(\operatorname{dom} f)$ whose complement in
$\operatorname{int}(\operatorname{dom} f)$ has measure zero, and that $\nabla f$ is continuous on
$D$. Theorem 25.6 recovers $\partial f(x)$ from the limits of gradients at nearby points, $\partial
f(x) = \operatorname{cl}(\operatorname{conv} S(x)) + K(x)$, and Theorem 25.7 shows that the
gradients of a pointwise convergent sequence of convex functions converge.

The proofs specialize the backbone modules
`Numlib.Analysis.Convex.Subdifferential.Differentiability`,
`Numlib.Analysis.Convex.Subdifferential.GradientLimit` and
`Numlib.Analysis.Convex.Subdifferential.Reconstruction`. All eleven numbered results of the section
are formalized.

## Main definitions

* `Rockafellar.HasGradientVecAt`: $\nabla f(x) = b$ for a vector $b \in \mathbb{R}^n$.
* `Rockafellar.gradientVec`: the vector $\nabla f(x)$, defined for every $x$ and equal to the
  gradient where $f$ is differentiable.

## Main results

* Theorem 25.1, `Rockafellar.theorem_25_1`, `Rockafellar.theorem_25_1_forward`,
  `Rockafellar.theorem_25_1_converse`, `Rockafellar.theorem_25_1_le` and
  `Rockafellar.theorem_25_1_differentiableAtFn`: a proper convex $f$ is differentiable at $x$ with
  $\nabla f(x) = b$ if and only if $\partial f(x) = \{b\}$, and then $f(z) \ge f(x) + \langle \nabla
  f(x), z - x \rangle$ for every $z$.
* Corollary 25.1.1, `Rockafellar.corollary_25_1_1_mem_interior` and
  `Rockafellar.corollary_25_1_1_proper`: if a convex $f$ is differentiable at $x$, then
  $x \in \operatorname{int}(\operatorname{dom} f)$ and $f$ is proper.
* Corollary 25.1.2, `Rockafellar.corollary_25_1_2`: the exposed points of $\operatorname{epi} f^*$
  are the points $(x^*, f^*(x^*))$ with $x^* = \nabla f(x)$ for some $x$.
* Corollary 25.1.3, `Rockafellar.corollary_25_1_3`: the exposed points of a closed convex set $C$
  are the gradients of its support function.
* Theorem 25.2, `Rockafellar.theorem_25_2`, `Rockafellar.theorem_25_2_dirDeriv` and
  `Rockafellar.theorem_25_2_partial`: a convex $f$ finite at $x$ is differentiable at $x$ if and
  only if $f'(x; \cdot)$ is linear, and it suffices that the $n$ two-sided partial derivatives exist
  and are finite.
* Theorem 25.3, `Rockafellar.theorem_25_3_differentiableAtFn_iff`,
  `Rockafellar.theorem_25_3_countable`, `Rockafellar.theorem_25_3_dense`,
  `Rockafellar.theorem_25_3_continuousAt` and `Rockafellar.theorem_25_3_monotone`: a proper convex
  function on $\mathbb{R}$ is differentiable at all but countably many points of
  $\operatorname{int}(\operatorname{dom} f)$, and its derivative is continuous and non-decreasing
  where it exists.
* Theorem 25.4, `Rockafellar.theorem_25_4_continuousAt_iff`, `Rockafellar.theorem_25_4_dense` and
  `Rockafellar.theorem_25_4_measure`: the two-sided directional derivative $f'(x; y)$ exists exactly
  where $x \mapsto f'(x; y)$ is continuous, on a dense subset of
  $\operatorname{int}(\operatorname{dom} f)$ with complement of measure zero.
* Theorem 25.5, `Rockafellar.theorem_25_5_dense`, `Rockafellar.theorem_25_5_measure` and
  `Rockafellar.theorem_25_5_continuousOn`: a proper convex function is differentiable on a dense
  subset $D$ of $\operatorname{int}(\operatorname{dom} f)$ with complement of measure zero, and
  $\nabla f$ is continuous on $D$.
* Corollary 25.5.1, `Rockafellar.corollary_25_5_1`: a finite convex function that is differentiable
  on an open convex set $C$ is continuously differentiable on $C$.
* Theorem 25.6, `Rockafellar.theorem_25_6`: for a closed proper convex $f$ with
  $\operatorname{int}(\operatorname{dom} f) \neq \emptyset$, $\partial f(x) =
  \operatorname{cl}(\operatorname{conv} S(x)) + K(x)$.
* Theorem 25.7, `Rockafellar.theorem_25_7` and `Rockafellar.theorem_25_7_uniform`: if convex
  functions $f_i$ converge pointwise to $g$ on an open convex set $C$, then
  $\nabla f_i \to \nabla g$ on $C$, uniformly on compact subsets.

## Conventions

* A function $f : \mathbb{R}^n \to [-\infty, +\infty]$ is `f : Rn n → EReal`. Its effective domain
  $\operatorname{dom} f = \{x \mid f(x) < +\infty\}$ is `ConvexAnalysis.convexDom f`, and
  $\partial f(x)$ is `ConvexAnalysis.subdifferential (Rockafellar.pairing n) f x`.
* "$f$ is differentiable at $x$" is `ConvexAnalysis.DifferentiableAtFn f x`: $f$ agrees near $x$
  with a real-valued function that is Fréchet differentiable at $x$.
* The one-sided directional derivative $f'(x; y)$ is `ConvexAnalysis.dirDeriv f x y`, the infimum
  over $t > 0$ of $(f(x + ty) - f(x))/t$. The two-sided directional derivative in the direction $y$
  exists when $f'(x; y) = -f'(x; -y)$.
* The real trace of $f$ is the function $z \mapsto$ `(f z).toReal`, which sends $\pm\infty$ to $0$.

## Implementation notes

* The gradient of the backbone is a continuous linear functional, while the gradient $\nabla f(x)$
  of the source is a vector. The map `Rockafellar.linFn`, the Fréchet–Riesz map
  $b \mapsto \langle \cdot, b \rangle$, translates between them.
  `Rockafellar.differentiableAtFn_iff_differentiableAt` relates differentiability of $f$ to
  Mathlib's `DifferentiableAt` for the real trace of $f$.
* Theorem 25.3 is stated for functions on `ℝ` rather than on `Rn 1`, because the interval $I$ of the
  source is an open interval of the real line.
* Several results hold in any normed space: the forward half of Theorem 25.1, both halves of
  Corollary 25.1.1, the necessity half of Theorem 25.2 and the density clause of Theorem 25.4. The
  converse half of Theorem 25.1, which uses Corollary 11.6.1, and the continuity and measure-zero
  clauses of Theorems 25.4 and 25.5 use the finite dimension of $\mathbb{R}^n$.

## Deviations from the source

* **Theorem 25.3**, continuity and monotonicity (generalization). The source states that $f'$ is
  continuous and non-decreasing relative to $D$. Here the right derivative, which is defined on all
  of $\mathbb{R}$, is continuous at each point of $D$ and non-decreasing on $\mathbb{R}$. See
  `Rockafellar.theorem_25_3_continuousAt` and `Rockafellar.theorem_25_3_monotone`.
* **Theorem 25.4**, first assertion (generalization). The source assumes $y \neq 0$. The statement
  also holds for $y = 0$. See `Rockafellar.theorem_25_4_continuousAt_iff`.
* **Theorem 25.6** (reading). The source sets $K(x) = \emptyset$ for
  $x \notin \operatorname{dom} f$. Here $K(x)$ is the normal cone, which is defined at every $x$.
  See `Rockafellar.theorem_25_6`.
* **Theorem 25.7** (generalization). The source assumes that all functions are differentiable on
  $C$. The pointwise statement uses differentiability at $x$ only. See `Rockafellar.theorem_25_7`.
-/

open Filter MeasureTheory Topology
open scoped Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ}

/-! ### The gradient $\nabla f(x)$ as a vector -/

section GradientVector

variable {f : Rn n → EReal} {b x : Rn n}

/-- **Section 25** of [rockafellar1970convex], the gradient as a vector. Let
$f : \mathbb{R}^n \to [-\infty, +\infty]$ and $b, x \in \mathbb{R}^n$. Then $\nabla f(x) = b$
means that $f$ agrees on a neighbourhood of $x$ with a real-valued function whose Fréchet
derivative at $x$ is the linear function $z \mapsto \langle z, b \rangle$.

The definition is `ConvexAnalysis.HasGradientAtFn` for the functional `Rockafellar.linFn b`. In
particular $\nabla f(x) = b$ implies that $f$ is finite near $x$. -/
def HasGradientVecAt (f : Rn n → EReal) (b x : Rn n) : Prop :=
  HasGradientAtFn f (linFn b) x

/-- The relation $\nabla f(x) = b$ of `Rockafellar.HasGradientVecAt` holds if and only if
`ConvexAnalysis.HasGradientAtFn f (Rockafellar.linFn b) x` holds. -/
theorem hasGradientVecAt_iff_hasGradientAtFn :
    HasGradientVecAt f b x ↔ HasGradientAtFn f (linFn b) x := Iff.rfl

/-- A function $f$ on $\mathbb{R}^n$ is differentiable at $x$ if and only if there is a vector
$b \in \mathbb{R}^n$ with $\nabla f(x) = b$. -/
theorem differentiableAtFn_iff_exists_hasGradientVecAt :
    DifferentiableAtFn f x ↔ ∃ b : Rn n, HasGradientVecAt f b x := by
  constructor
  · rintro ⟨f', hf'⟩
    obtain ⟨b, hb⟩ := exists_linFn f'
    refine ⟨b, ?_⟩
    rw [hasGradientVecAt_iff_hasGradientAtFn, hb]
    exact hf'
  · rintro ⟨b, hb⟩
    exact ⟨linFn b, hb⟩

/-- **Section 25** of [rockafellar1970convex], the gradient vector. For
$f : \mathbb{R}^n \to [-\infty, +\infty]$ and $x \in \mathbb{R}^n$, the vector $\nabla f(x)$ is
the vector $v$ with $\langle z, v \rangle = Dg(x)\,z$ for every $z$, where $Dg(x)$ is the
Fréchet derivative at $x$ of the real trace $g$ of $f$.

The real trace is `fun z => (f z).toReal`, and $Dg(x)$ is Mathlib's `fderiv`. The vector is
defined for every $x$. Where $f$ is differentiable it is the gradient of $f$
(`Rockafellar.hasGradientVecAt_gradientVec`). Where the real trace is not differentiable,
`fderiv` is $0$ and so is the vector. -/
noncomputable def gradientVec (f : Rn n → EReal) (x : Rn n) : Rn n :=
  (InnerProductSpace.toDual ℝ (Rn n)).symm (fderiv ℝ (fun z => (f z).toReal) x)

/-- The linear function $z \mapsto \langle z, v \rangle$, for the vector $v$ given by
`Rockafellar.gradientVec f x`, is the Fréchet derivative at $x$ of the real trace $z \mapsto$
`(f z).toReal` of $f$. -/
theorem linFn_gradientVec (f : Rn n → EReal) (x : Rn n) :
    linFn (gradientVec f x) = fderiv ℝ (fun z => (f z).toReal) x := by
  rw [linFn_eq_toDual]
  exact (InnerProductSpace.toDual ℝ (Rn n)).apply_symm_apply _

/-- If $\nabla f(x) = b$, then `Rockafellar.gradientVec f x` is $b$. In particular, the gradient
vector is unique where it exists. -/
theorem HasGradientVecAt.gradientVec_eq (h : HasGradientVecAt f b x) : gradientVec f x = b := by
  have hfd : fderiv ℝ (fun z => (f z).toReal) x = linFn b :=
    HasGradientAtFn.fderiv_toReal_eq (hasGradientVecAt_iff_hasGradientAtFn.1 h)
  have hg : gradientVec f x
      = (InnerProductSpace.toDual ℝ (Rn n)).symm (fderiv ℝ (fun z => (f z).toReal) x) := rfl
  rw [hg, hfd, linFn_eq_toDual, LinearIsometryEquiv.symm_apply_apply]

/-- If $f$ is differentiable at $x$, then $\nabla f(x)$ is the vector `Rockafellar.gradientVec f x`.
-/
theorem hasGradientVecAt_gradientVec (h : DifferentiableAtFn f x) :
    HasGradientVecAt f (gradientVec f x) x := by
  have hd := DifferentiableAtFn.hasGradientAtFn_fderiv h
  rw [← linFn_gradientVec f x] at hd
  exact hd

/-- Let $g : \mathbb{R}^n \to \mathbb{R}$ have the Fréchet derivative
$z \mapsto \langle z, b \rangle$ at $x$. Then $g$, viewed as a function with values in
$[-\infty, +\infty]$, satisfies $\nabla g(x) = b$. This is the translation used where the source
takes a finite convex function. -/
theorem hasGradientVecAt_coe {g : Rn n → ℝ} (hd : HasFDerivAt g (linFn b) x) :
    HasGradientVecAt (fun z => ((g z : ℝ) : EReal)) b x :=
  hasGradientAtFn_coe hd

/-- Let $f$ be a proper function on $\mathbb{R}^n$, and let
$x \in \operatorname{int}(\operatorname{dom} f)$. Then $f$ is differentiable at $x$ if and only
if its real trace $z \mapsto$ `(f z).toReal` is differentiable at $x$ in the sense of Mathlib's
`DifferentiableAt`. By Corollary 25.1.1, every point of differentiability of $f$ lies in
$\operatorname{int}(\operatorname{dom} f)$. -/
theorem differentiableAtFn_iff_differentiableAt (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) :
    DifferentiableAtFn f x ↔ DifferentiableAt ℝ (fun z => (f z).toReal) x :=
  differentiableAtFn_iff_differentiableAt_toReal hp hx

end GradientVector

/-! ### Theorem 25.1 and its corollaries -/

section Theorem251

variable {f : Rn n → EReal} {b x : Rn n}

/-- **Theorem 25.1** of [rockafellar1970convex], forward half. Let $f$ be a convex function on
$\mathbb{R}^n$, and suppose that $\nabla f(x) = b$. Then $b$ is the unique subgradient of $f$ at
$x$:
$$\partial f(x) = \{b\}.$$

The argument works in any normed space, and the uniqueness half uses neither convexity nor
properness. -/
theorem theorem_25_1_forward (hf : ConvexFn f) (h : HasGradientVecAt f b x) :
    subdifferential (pairing n) f x = {b} := by
  have hs := subdifferential_innerL_eq_singleton (E := Rn n) hf
    (hasGradientVecAt_iff_hasGradientAtFn.1 h)
  rwa [linFn_eq_toDual, LinearIsometryEquiv.symm_apply_apply] at hs

/-- **Theorem 25.1** of [rockafellar1970convex], the subgradient inequality. Let $f$ be a convex
function on $\mathbb{R}^n$ with $\nabla f(x) = b$. Then
$$f(z) \ge f(x) + \langle z - x, \nabla f(x) \rangle \quad \text{for every } z \in
  \mathbb{R}^n.$$

Like the forward half, this holds in any normed space. -/
theorem theorem_25_1_le (hf : ConvexFn f) (h : HasGradientVecAt f b x) (z : Rn n) :
    f x + ((pairing n (z - x) b : ℝ) : EReal) ≤ f z := by
  have hle := HasGradientAtFn.le hf (hasGradientVecAt_iff_hasGradientAtFn.1 h) z
  rwa [linFn_apply] at hle

/-- **Theorem 25.1** of [rockafellar1970convex], converse half. Let $f$ be a proper convex function
on $\mathbb{R}^n$ with $\partial f(x) = \{b\}$. Then $f$ is differentiable at $x$ and
$\nabla f(x) = b$.

This half uses the finite dimension of $\mathbb{R}^n$: a convex set in $\mathbb{R}^n$ is a
neighbourhood of every point at which its normal cone is $\{0\}$ (Corollary 11.6.1). The source
passes over this step. -/
theorem theorem_25_1_converse (hf : ConvexFn f) (hp : ProperConvex f)
    (h : subdifferential (pairing n) f x = {b}) : HasGradientVecAt f b x := by
  have hg := hasGradientAtFn_toDual_of_subdifferential_eq_singleton (E := Rn n) hf hp h
  rw [hasGradientVecAt_iff_hasGradientAtFn, linFn_eq_toDual]
  exact hg

/-- **Theorem 25.1** of [rockafellar1970convex]. Let $f$ be a proper convex function on
$\mathbb{R}^n$, and let $x, b \in \mathbb{R}^n$. Then $f$ is differentiable at $x$ with gradient
$b$ if and only if $b$ is the unique subgradient of $f$ at $x$:
$$\nabla f(x) = b \iff \partial f(x) = \{b\}.$$

The source assumes that $f$ is finite at $x$. Here properness takes the place of this
hypothesis: each side of the equivalence makes $f(x)$ finite. The two directions are
`Rockafellar.theorem_25_1_forward` and `Rockafellar.theorem_25_1_converse`. -/
theorem theorem_25_1 (hf : ConvexFn f) (hp : ProperConvex f) :
    HasGradientVecAt f b x ↔ subdifferential (pairing n) f x = {b} :=
  ⟨theorem_25_1_forward hf, theorem_25_1_converse hf hp⟩

/-- **Theorem 25.1** of [rockafellar1970convex], the sentence after it. Let $f$ be a proper convex
function on $\mathbb{R}^n$. Then $f$ is differentiable at $x$ if and only if $\partial f(x)$
consists of exactly one vector. -/
theorem theorem_25_1_differentiableAtFn (hf : ConvexFn f) (hp : ProperConvex f) :
    DifferentiableAtFn f x ↔ ∃ b : Rn n, subdifferential (pairing n) f x = {b} := by
  rw [differentiableAtFn_iff_exists_hasGradientVecAt]
  exact exists_congr fun _ => theorem_25_1 hf hp

/-- **Corollary 25.1.1** of [rockafellar1970convex], second half. Let $f$ be a convex function on
$\mathbb{R}^n$, and suppose that $f$ is differentiable at $x$ with $\nabla f(x) = b$. Then $f$
is proper.

This holds in any topological vector space. -/
theorem corollary_25_1_1_proper (hf : ConvexFn f) (h : HasGradientVecAt f b x) : ProperConvex f :=
  HasGradientAtFn.proper hf (hasGradientVecAt_iff_hasGradientAtFn.1 h)

/-- **Corollary 25.1.1** of [rockafellar1970convex], first half. Let
$f : \mathbb{R}^n \to [-\infty, +\infty]$ with $\nabla f(x) = b$. Then
$x \in \operatorname{int}(\operatorname{dom} f)$.

Neither convexity nor differentiability is used, only that $f$ is finite near $x$, which the
definition of $\nabla f(x)$ presupposes. -/
theorem corollary_25_1_1_mem_interior (h : HasGradientVecAt f b x) : x ∈ interior (convexDom f) :=
  HasGradientAtFn.mem_interior_convexDom (hasGradientVecAt_iff_hasGradientAtFn.1 h)

/-- **Corollary 25.1.2** of [rockafellar1970convex]. Let $f$ be a proper convex function on
$\mathbb{R}^n$ with conjugate $f^*$, and let $y \in \mathbb{R}^n$ and $\mu \in \mathbb{R}$. Then
$(y, \mu)$ is an exposed point of $\operatorname{epi} f^*$ if and only if $\mu = f^*(y)$ and
there is a point $x$ at which $f$ is differentiable with $\nabla f(x) = y$.

As in the source, $f$ need not be closed. The proof in the source replaces $f$ by
$\operatorname{cl} f$, on the strength of the remark $\nabla(\operatorname{cl} f) = \nabla f$,
which it does not prove. That remark needs
$\operatorname{int}(\operatorname{dom}(\operatorname{cl} f)) =
\operatorname{int}(\operatorname{dom} f)$ and $\operatorname{cl} f = f$ on this interior; the
backbone proves both. The conjugate is `ConvexAnalysis.convexConj (Rockafellar.pairing n) f`,
and exposed points are Mathlib's `Set.exposedPoints`. -/
theorem corollary_25_1_2 (hf : ConvexFn f) (hp : ProperConvex f) {y : Rn n} {μ : ℝ} :
    (y, μ) ∈ (epi (convexConj (pairing n) f)).exposedPoints ℝ ↔
      convexConj (pairing n) f y = (μ : EReal) ∧ ∃ x : Rn n, HasGradientVecAt f y x := by
  rw [mem_exposedPoints_epi_convexConj_iff_of_properConvex (B := pairing n) hf hp]
  exact and_congr_right fun _ => exists_congr fun _ => (theorem_25_1 hf hp).symm

/-- **Corollary 25.1.3** of [rockafellar1970convex]. Let $g$ be a positively homogeneous proper
convex function on $\mathbb{R}^n$, and let
$$C = \{z \mid \langle y, z \rangle \le g(y) \text{ for every } y\}.$$
Then $z$ is an exposed point of $C$ if and only if there is a point $y$ at which $g$ is
differentiable with $\nabla g(y) = z$.

The source takes $C$ to be a non-empty closed convex set. These properties of $C$ follow from
the other hypotheses and are not assumed. The set $C$ is `ConvexAnalysis.supportSet
(Rockafellar.pairing n) g`. -/
theorem corollary_25_1_3 {g : Rn n → EReal} {C : Set (Rn n)} (hgh : PosHomogeneous g)
    (hgc : ConvexFn g) (hgp : ProperConvex g)
    (hC : C = supportSet (pairing n) g) {z : Rn n} :
    z ∈ C.exposedPoints ℝ ↔ ∃ y : Rn n, HasGradientVecAt g z y := by
  subst hC
  have h := mem_exposedPoints_supportSet_iff_of_properConvex (B := pairing n) hgh hgc hgp (z := z)
  simp only [flip_pairing] at h
  rw [h]
  exact exists_congr fun _ => (theorem_25_1 hgc hgp).symm

end Theorem251

/-! ### Theorem 25.2 -/

section Theorem252

variable {f : Rn n → EReal} {b x : Rn n}

/-- **Theorem 25.2** of [rockafellar1970convex], necessity. Let $f$ be a convex function on
$\mathbb{R}^n$ with $\nabla f(x) = b$. Then the directional derivative at $x$ is linear:
$$f'(x; v) = \langle v, b \rangle \quad \text{for every } v \in \mathbb{R}^n.$$

Like the forward half of Theorem 25.1, this holds in any normed space. -/
theorem theorem_25_2_dirDeriv (hf : ConvexFn f) (h : HasGradientVecAt f b x) (v : Rn n) :
    dirDeriv f x v = ((pairing n v b : ℝ) : EReal) := by
  have hd := HasGradientAtFn.dirDeriv_eq hf (hasGradientVecAt_iff_hasGradientAtFn.1 h) v
  rwa [linFn_apply] at hd

/-- **Theorem 25.2** of [rockafellar1970convex]. Let $f$ be a convex function on $\mathbb{R}^n$, and
let $x$ be a point where $f$ is finite. Then $f$ is differentiable at $x$ if and only if the
directional derivative $f'(x; \cdot)$ is linear, that is, there is a vector $b \in \mathbb{R}^n$
with
$$f'(x; v) = \langle v, b \rangle \quad \text{for every } v \in \mathbb{R}^n.$$

Linearity of $f'(x; \cdot)$ is written as the existence of such a $b$, which on $\mathbb{R}^n$
is the same. The sufficiency half uses the finite dimension of $\mathbb{R}^n$, through an
estimate on a cross-polytope that uses only the $2n$ one-sided derivatives along $\pm e_j$,
where $e_1, \dots, e_n$ is the standard basis. -/
theorem theorem_25_2 (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    DifferentiableAtFn f x ↔
      ∃ b : Rn n, ∀ v : Rn n, dirDeriv f x v = ((pairing n v b : ℝ) : EReal) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := differentiableAtFn_iff_exists_hasGradientVecAt.1 h
    exact ⟨c, theorem_25_2_dirDeriv hf hc⟩
  · rintro ⟨c, hc⟩
    refine ⟨linFn c, hasGradientAtFn_of_dirDeriv_eq hf ht hb fun v => ?_⟩
    rw [hc v, linFn_apply]

/-- **Theorem 25.2** of [rockafellar1970convex], last sentence. Let $f$ be a convex function on
$\mathbb{R}^n$, finite at $x$, and let $e_1, \dots, e_n$ be the standard basis. Suppose that
each two-sided partial derivative of $f$ at $x$ exists and is a real number $c_j$:
$$f'(x; e_j) = c_j \quad \text{and} \quad f'(x; -e_j) = -c_j \quad \text{for every } j.$$
Then $f$ is differentiable at $x$.

The vector $e_j$ is `EuclideanSpace.single j 1`, with $j$ in `Fin n`. -/
theorem theorem_25_2_partial (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (c : Fin n → ℝ)
    (hpos : ∀ j, dirDeriv f x (EuclideanSpace.single j (1 : ℝ)) = ((c j : ℝ) : EReal))
    (hneg : ∀ j, dirDeriv f x (-EuclideanSpace.single j (1 : ℝ)) = ((-c j : ℝ) : EReal)) :
    DifferentiableAtFn f x :=
  differentiableAtFn_of_forall_basis_dirDeriv_eq (EuclideanSpace.basisFun (Fin n) ℝ).toBasis hf
    ht hb c (fun j => by simpa using hpos j) fun j => by simpa using hneg j

end Theorem252

/-!
### Theorem 25.3, on the real line

The interval $I$ of the source is an open interval of $\mathbb{R}$ on which $f$ is finite. Here $f$
is a function on $\mathbb{R}$ and $I = \operatorname{int}(\operatorname{dom} f)$. The source defines
the derivative $f'$ only on the set $D$ of points of differentiability. Here $f'$ is the right
derivative $f'_+$, `ConvexAnalysis.rightDeriv f`, which is defined everywhere and agrees with $f'$
on $D$. So the clauses below are those of the source, made stronger.
-/

section Theorem253

variable {f : ℝ → EReal}

/-- **Theorem 25.3** of [rockafellar1970convex], the definition of $D$. Let $f$ be a proper convex
function on $\mathbb{R}$, and let $x \in \operatorname{int}(\operatorname{dom} f)$. Then $f$ is
differentiable at $x$ if and only if its left and right derivatives at $x$ are equal:
$f'_-(x) = f'_+(x)$.

The one-sided derivatives are `ConvexAnalysis.leftDeriv f x` and
`ConvexAnalysis.rightDeriv f x`, with values in $[-\infty, +\infty]$. -/
theorem theorem_25_3_differentiableAtFn_iff (hf : ConvexFn f) (hp : ProperConvex f) {x : ℝ}
    (hx : x ∈ interior (convexDom f)) : DifferentiableAtFn f x ↔ leftDeriv f x = rightDeriv f x :=
  differentiableAtFn_iff_leftDeriv_eq_rightDeriv hf hp hx

/-- **Theorem 25.3** of [rockafellar1970convex], first assertion. Let $f$ be a proper convex
function on $\mathbb{R}$. Then the set of points of
$I = \operatorname{int}(\operatorname{dom} f)$ at which $f$ is not differentiable is countable.
That is, $D$ contains all but countably many points of $I$. -/
theorem theorem_25_3_countable (hf : ConvexFn f) (hp : ProperConvex f) :
    {x ∈ interior (convexDom f) | ¬DifferentiableAtFn f x}.Countable :=
  countable_not_differentiableAtFn hf hp

/-- **Theorem 25.3** of [rockafellar1970convex], the parenthesis. Let $f$ be a proper convex
function on $\mathbb{R}$. Then the set $D$ of points at which $f$ is differentiable is dense in
$I = \operatorname{int}(\operatorname{dom} f)$:
$$\operatorname{int}(\operatorname{dom} f) \subseteq \operatorname{cl} D.$$
-/
theorem theorem_25_3_dense (hf : ConvexFn f) (hp : ProperConvex f) :
    interior (convexDom f) ⊆ closure {z : ℝ | DifferentiableAtFn f z} :=
  subset_closure_differentiableAtFn hf hp

/-- **Theorem 25.3** of [rockafellar1970convex], second assertion. Let $f$ be a closed proper convex
function on $\mathbb{R}$, and let $x \in \operatorname{int}(\operatorname{dom} f)$ be a point at
which $f$ is differentiable. Then the right derivative $f'_+$ is continuous at $x$.

**Generalization.** The source states that $f'$ is continuous relative to $D$. Here the right
derivative, which is defined on all of $\mathbb{R}$, is continuous at each point of $D$ in the
ordinary sense.

Closedness of $f$ corresponds to the step of the source's proof that extends $f$ to a closed
proper convex function on the line. -/
theorem theorem_25_3_continuousAt (hf : ClosedProperConvexFn f) {x : ℝ}
    (hx : x ∈ interior (convexDom f))
        (hd : DifferentiableAtFn f x) : ContinuousAt (rightDeriv f) x :=
  continuousAt_rightDeriv_of_differentiableAtFn hf hx hd

/-- **Theorem 25.3** of [rockafellar1970convex], third assertion. Let $f$ be a proper convex
function on $\mathbb{R}$. Then the right derivative $f'_+$ is non-decreasing on $\mathbb{R}$.

**Generalization.** The source states that $f'$ is non-decreasing relative to $D$. Here the
right derivative is non-decreasing on the whole line. -/
theorem theorem_25_3_monotone (hf : ConvexFn f) (hp : ProperConvex f) : Monotone (rightDeriv f) :=
  monotone_rightDeriv hf hp

end Theorem253

/-! ### Theorem 25.4 -/

section Theorem254

variable {f : Rn n → EReal} {x : Rn n}

/-- **Theorem 25.4** of [rockafellar1970convex], first assertion. Let $f$ be a proper convex
function on $\mathbb{R}^n$, let $x \in \operatorname{int}(\operatorname{dom} f)$, and let
$y \in \mathbb{R}^n$. Then the function $z \mapsto f'(z; y)$ is continuous at $x$ if and only if
the two-sided directional derivative of $f$ at $x$ in the direction $y$ exists:
$$f'(x; y) = -f'(x; -y).$$

**Generalization.** The source assumes $y \neq 0$. The hypothesis is not needed: for $y = 0$
both sides hold. -/
theorem theorem_25_4_continuousAt_iff (hf : ConvexFn f) (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) (y : Rn n) :
    ContinuousAt (fun z => dirDeriv f z y) x ↔ dirDeriv f x y = -dirDeriv f x (-y) :=
  continuousAt_dirDeriv_iff hf hp hx y

/-- **Theorem 25.4** of [rockafellar1970convex], density. Let $f$ be a proper convex function on
$\mathbb{R}^n$, and let $y \in \mathbb{R}^n$. Then the set of points
$z \in \operatorname{int}(\operatorname{dom} f)$ with $f'(z; y) = -f'(z; -y)$ is dense in
$\operatorname{int}(\operatorname{dom} f)$.

This clause holds in any space: the restriction of $f$ to a line in the direction $y$ reduces it
to Theorem 25.3. -/
theorem theorem_25_4_dense (hf : ConvexFn f) (hp : ProperConvex f) (y : Rn n) :
    interior (convexDom f) ⊆
      closure {z ∈ interior (convexDom f) | dirDeriv f z y = -dirDeriv f z (-y)} :=
  subset_closure_twoSided_dirDeriv hf hp y

/-- **Theorem 25.4** of [rockafellar1970convex], measure zero. Let $f$ be a proper convex function
on $\mathbb{R}^n$, and let $y \in \mathbb{R}^n$. Then the set of points
$z \in \operatorname{int}(\operatorname{dom} f)$ with $f'(z; y) \neq -f'(z; -y)$ has Lebesgue
measure zero.

The source proves this clause first, by a Fubini argument over lines, and deduces Theorem 25.5
from it. Here the order is reversed: Theorem 25.5 follows from Rademacher's theorem, and this
clause follows from Theorem 25.5. -/
theorem theorem_25_4_measure (hf : ConvexFn f) (hp : ProperConvex f) (y : Rn n) :
    volume (interior (convexDom f) \ {z | dirDeriv f z y = -dirDeriv f z (-y)}) = 0 :=
  measure_diff_twoSided_dirDeriv hf hp y

end Theorem254

/-! ### Theorem 25.5 and its corollary -/

section Theorem255

variable {f : Rn n → EReal}

/-- **Theorem 25.5** of [rockafellar1970convex], density. Let $f$ be a proper convex function on
$\mathbb{R}^n$, and let $D$ be the set of points at which $f$ is differentiable. Then $D$ is
dense in $\operatorname{int}(\operatorname{dom} f)$:
$$\operatorname{int}(\operatorname{dom} f) \subseteq \operatorname{cl} D.$$
-/
theorem theorem_25_5_dense (hf : ConvexFn f) (hp : ProperConvex f) :
    interior (convexDom f) ⊆ closure {z : Rn n | DifferentiableAtFn f z} :=
  interior_convexDom_subset_closure_differentiableAtFn hf hp

/-- **Theorem 25.5** of [rockafellar1970convex], measure zero. Let $f$ be a proper convex function
on $\mathbb{R}^n$, and let $D$ be the set of points at which $f$ is differentiable. Then
$\operatorname{int}(\operatorname{dom} f) \setminus D$ has Lebesgue measure zero.

This is Rademacher's theorem. Convexity supplies only the local Lipschitz constants of $f$. -/
theorem theorem_25_5_measure (hf : ConvexFn f) (hp : ProperConvex f) :
    volume (interior (convexDom f) \ {z : Rn n | DifferentiableAtFn f z}) = 0 :=
  measure_diff_differentiableAtFn hf hp

/-- **Theorem 25.5** of [rockafellar1970convex], continuity. Let $f$ be a proper convex function on
$\mathbb{R}^n$, and let $D$ be the set of points at which $f$ is differentiable. Then the
gradient mapping $x \mapsto \nabla f(x)$ is continuous on $D$.

The gradient mapping is `Rockafellar.gradientVec f`. The proof is Corollary 24.5.1, with both
subdifferentials reduced to single vectors by Theorem 25.1. -/
theorem theorem_25_5_continuousOn (hf : ConvexFn f) (hp : ProperConvex f) :
    ContinuousOn (gradientVec f) {z : Rn n | DifferentiableAtFn f z} :=
  (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp_continuousOn
    (continuousOn_fderiv_toReal hf hp)

/-- **Corollary 25.5.1** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be an open
convex set, and let $g : \mathbb{R}^n \to \mathbb{R}$ be convex on $C$ and differentiable at
every point of $C$. Then $g$ is continuously differentiable on $C$: its derivative
$x \mapsto Dg(x)$ is continuous on $C$.

The source states this corollary without proof. The proof here extends $g$ by $+\infty$ outside
$C$ and applies the continuity clause of Theorem 25.5. Convexity of $C$ is part of Mathlib's
`ConvexOn`, and the derivative is Mathlib's `fderiv ℝ g`, a continuous linear functional. -/
theorem corollary_25_5_1 {C : Set (Rn n)} {g : Rn n → ℝ} (hC : IsOpen C) (hg : ConvexOn ℝ C g)
    (hd : DifferentiableOn ℝ g C) : ContinuousOn (fderiv ℝ g) C := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact continuousOn_empty _
  · exact continuousOn_fderiv_of_convexOn hC hne hg hd

end Theorem255

/-! ### Theorem 25.6 -/

section Theorem256

variable {f : Rn n → EReal} {x : Rn n}

/-- The set $S(x)$ of the source, in vector form: $v$ lies in `ConvexAnalysis.gradientLimits f x` if
and only if there are sequences $x_i \to x$ and $v_i \to v$ in $\mathbb{R}^n$ with
$\nabla f(x_i) = v_i$ for every $i$. -/
theorem mem_gradientLimits_iff {v : Rn n} :
    v ∈ gradientLimits f x ↔ ∃ xs vs : ℕ → Rn n, Tendsto xs atTop (𝓝 x) ∧
      (∀ i, HasGradientVecAt f (vs i) (xs i)) ∧ Tendsto vs atTop (𝓝 v) := by
  constructor
  · rintro ⟨xs, vs, h1, h2, h3⟩
    refine ⟨xs, vs, h1, fun i => ?_, h3⟩
    rw [hasGradientVecAt_iff_hasGradientAtFn, linFn_eq_toDual]
    exact h2 i
  · rintro ⟨xs, vs, h1, h2, h3⟩
    refine ⟨xs, vs, h1, fun i => ?_, h3⟩
    have hi := h2 i
    rw [hasGradientVecAt_iff_hasGradientAtFn, linFn_eq_toDual] at hi
    exact hi

/-- Let $f$ be a proper function on $\mathbb{R}^n$ with $\partial f(x) \neq \emptyset$. Then the
recession cone of $\partial f(x)$ is the normal cone to $\operatorname{dom} f$ at $x$. The
source leaves this as an exercise in Section 23 and says that it is verified in the proof of
Theorem 25.6. That proof uses only the inclusion $\subseteq$, and the equality is proved here
separately. -/
theorem recessionCone_subdifferential_eq_normalCone (hp : ProperConvex f) {v : Rn n}
    (hv : v ∈ subdifferential (pairing n) f x) :
    recessionCone (subdifferential (pairing n) f x) = normalCone (pairing n) (convexDom f) x :=
  ConvexAnalysis.recessionCone_subdifferential_eq_normalCone hp hv

/-- **Theorem 25.6** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$ such that $\operatorname{int}(\operatorname{dom} f)$ is non-empty. Then for every
$x \in \mathbb{R}^n$
$$\partial f(x) = \operatorname{cl}(\operatorname{conv} S(x)) + K(x),$$
where $S(x)$ is the set of all limits of sequences $\nabla f(x_i)$ such that $f$ is
differentiable at $x_i$ and $x_i \to x$, and $K(x)$ is the normal cone to $\operatorname{dom} f$
at $x$.

**Reading.** The source sets $K(x) = \emptyset$ for $x \notin \operatorname{dom} f$. Here $K(x)$
is `ConvexAnalysis.normalCone`, which is defined at every $x$. The two readings agree wherever
both sides are non-empty. For $x \notin \operatorname{dom} f$ the left side is empty, so the
theorem forces $\operatorname{cl}(\operatorname{conv} S(x))$ to be empty.

The set $S(x)$ is `ConvexAnalysis.gradientLimits f x` (see
`Rockafellar.mem_gradientLimits_iff`). -/
theorem theorem_25_6 (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hne : (interior (convexDom f)).Nonempty) :
    subdifferential (pairing n) f x
      = closure (convexHull ℝ (gradientLimits f x)) + normalCone (pairing n) (convexDom f) x :=
  subdifferential_eq_closure_convexHull_gradientLimits_add_normalCone hf hp hcl hne

end Theorem256

/-! ### Theorem 25.7 -/

section Theorem257

variable {C : Set (Rn n)} {f : ℕ → Rn n → EReal} {g : Rn n → EReal} {x : Rn n}

/-- **Theorem 25.7** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be an open convex
set. Let $f_0, f_1, \dots$ be proper convex functions on $\mathbb{R}^n$ and let $g$ be a proper
convex function on $\mathbb{R}^n$, all finite on $C$, such that $f_i(z) \to g(z)$ for every
$z \in C$. Let $x \in C$, and suppose that $g$ and every $f_i$ are differentiable at $x$. Then
$$\lim_{i \to \infty} \nabla f_i(x) = \nabla g(x).$$

**Generalization.** The source assumes that $g$ and the $f_i$ are differentiable on all of $C$.
Only differentiability at $x$ is used.

For arbitrary differentiable functions the conclusion is false. Convexity supplies it through
the upper semicontinuity of $\partial f$ under pointwise convergence (Theorem 24.5). Finiteness
on $C$ is written as $C \subseteq \operatorname{dom} f_i$ and
$C \subseteq \operatorname{dom} g$, together with properness. -/
theorem theorem_25_7 (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfp : ∀ i, ProperConvex (f i)) (hfC : ∀ i, C ⊆ convexDom (f i)) (hg : ConvexFn g)
        (hgp : ProperConvex g)
    (hgC : C ⊆ convexDom g) (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z))) (hx : x ∈ C)
    {b : ℕ → Rn n} {b' : Rn n} (hb : ∀ i, HasGradientVecAt (f i) (b i) x)
    (hb' : HasGradientVecAt g b' x) : Tendsto b atTop (𝓝 b') := by
  have h := tendsto_of_hasGradientAtFn hC hCc hf hfp hfC hg hgp hgC hconv hx
    (G := fun i => linFn (b i)) (G' := linFn b') (fun i => hb i) hb'
  have hsymm : ∀ c : Rn n, (InnerProductSpace.toDual ℝ (Rn n)).symm (linFn c) = c := fun c => by
    rw [linFn_eq_toDual, LinearIsometryEquiv.symm_apply_apply]
  have hc : Tendsto (fun i => (InnerProductSpace.toDual ℝ (Rn n)).symm (linFn (b i))) atTop
      (𝓝 ((InnerProductSpace.toDual ℝ (Rn n)).symm (linFn b'))) :=
    ((InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.tendsto _).comp h
  simpa only [hsymm] using hc

/-- **Theorem 25.7** of [rockafellar1970convex], the sentence after it. Under the hypotheses of
`Rockafellar.theorem_25_7`, with $g$ and every $f_i$ differentiable at every point of $C$, the
gradient mappings $\nabla f_i$ converge to $\nabla g$ uniformly on every compact set
$S \subseteq C$.

The source says closed bounded subset, which in $\mathbb{R}^n$ means compact. The gradient
mappings are `Rockafellar.gradientVec`. -/
theorem theorem_25_7_uniform (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfp : ∀ i, ProperConvex (f i)) (hfC : ∀ i, C ⊆ convexDom (f i)) (hg : ConvexFn g)
        (hgp : ProperConvex g)
    (hgC : C ⊆ convexDom g) (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z)))
    (hfd : ∀ i, ∀ z ∈ C, DifferentiableAtFn (f i) z)
    (hgd : ∀ z ∈ C, DifferentiableAtFn g z) {S : Set (Rn n)} (hS : IsCompact S) (hSC : S ⊆ C) :
    TendstoUniformlyOn (fun i => gradientVec (f i)) (gradientVec g) atTop S := by
  have h := tendstoUniformlyOn_fderiv_toReal hC hCc hf hfp hfC hg hgp hgC hconv hfd hgd hS hSC
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with i hi z hz
  have hdist : dist (gradientVec g z) (gradientVec (f i) z)
      = dist (fderiv ℝ (fun w => (g w).toReal) z) (fderiv ℝ (fun w => (f i w).toReal) z) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.dist_map _ _
  rw [hdist]
  exact hi z hz

end Theorem257

end Rockafellar
