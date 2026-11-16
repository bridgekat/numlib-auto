/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.LocallyConvex.Polar
import Numlib.Analysis.Convex.Closure

/-!
# Dual pairs

Convex duality (conjugacy, support functions, polarity, the dual operations, normal cones) is a
theory about a **pairing**, a bilinear form $\langle x, y \rangle = B(x, y)$ between two real vector
spaces $E$ and $F$. It is not a theory about $\mathbb{R}^n$, nor about a space and its topological
dual. This module collects the vocabulary that the rest of the development is stated in, following
§12 of [rockafellar1970convex] and the dual pairs of Chapter IV of [schaefer1971topological]. It
defines the affine functions $x \mapsto \langle x, y \rangle - c$, adjoint pairs of linear maps, and
the product pairing of $U \times X$ with $V \times Y$, and shows that a continuous linear functional
on $E \times \mathbb{R}$ splits uniquely into a horizontal part and a vertical coefficient.

The topology on $E$ relates to the pairing in two grades. The pairing is **continuous** if every
functional $\langle \cdot, y \rangle$ is continuous on $E$, and **compatible** if moreover every
continuous linear functional on $E$ has this form. Half of the theory (the conjugate is closed, the
polar is closed, $f^*$ does not see $\operatorname{cl} f$) needs only the first. The decisive
example is a Banach space paired with its dual in the norm topology of the dual: that pairing is
continuous on both sides, but compatible on the side of the dual only if the space is reflexive.

## Main definitions

* `ConvexAnalysis.affineFn`: the affine function $x \mapsto \langle x, y \rangle - c$. Conjugacy
  keeps account of the affine functions below a convex function, and these are those functions.
* `ConvexAnalysis.IsContinuousPairing`, `ConvexAnalysis.IsCompatiblePairing`: the pairing is
  continuous, or compatible, for the topology of $E$.
* `ConvexAnalysis.evalCLM`: the map $y \mapsto \langle \cdot, y \rangle$ from $F$ to the continuous
  dual of $E$.
* `ConvexAnalysis.IsAdjointPair`: linear maps $A : E \to G$ and $A' : H \to F$ are adjoint for given
  pairings of $E$ with $F$ and of $G$ with $H$.
* `ConvexAnalysis.prodPairing`, `ConvexAnalysis.negFst`: the pairing of $U \times X$ with
  $V \times Y$, and the sign change on the first factor that the adjoint of a convex bifunction is
  stated with.

## Main results

* `ConvexAnalysis.convexFn_affineFn`, `ConvexAnalysis.closedConvex_affineFn`: the affine functions
  of a pairing are convex, and closed when the pairing is continuous.
* `ConvexAnalysis.affineFn_le_iff`: $x \mapsto \langle x, y \rangle - c$ lies below $f$ if and only
  if $\langle x, y \rangle - f(x) \le c$ for every $x$, the inequality that the conjugate measures.
* `ConvexAnalysis.isAdjointPair_adjoint`, `ConvexAnalysis.isAdjointPair_topDualPairing`: the two
  sources of an adjoint: a finite-dimensional real inner product space paired with itself, and a
  space paired with its topological dual.
* `ConvexAnalysis.instIsCompatiblePairingTopDual`: a real vector space with a topology is compatibly
  paired with its own continuous dual, in its own topology. The Fenchel–Moreau theorem is applied
  through this instance in practice.
* `ConvexAnalysis.instIsContinuousPairingProd`, `ConvexAnalysis.instIsCompatiblePairingProd`,
  `ConvexAnalysis.isContinuousPairing_prodPairing_flip`: a product of continuous (or compatible)
  pairings is continuous (or compatible), on either side.
* `ConvexAnalysis.exists_unique_dual_prod`: a continuous linear functional on $E \times \mathbb{R}$
  is $(x, \mu) \mapsto g(x) + c \mu$ for a unique pair $(g, c)$. The Fenchel–Moreau theorem uses
  this twice, to split a separating functional into a horizontal part and a vertical coefficient
  before it recognizes an affine minorant.

## Implementation notes

* There is no transpose operation. For a linear map $A : E \to G$ between arbitrarily paired spaces,
  a transpose need not exist, and when it exists it is extra data. This is why
  `ConvexAnalysis.IsAdjointPair` is a predicate on a given pair of maps, with four spaces, and not
  an operation.
* A separating pairing is Mathlib's `LinearMap.Nondegenerate`.
* Where a statement of [rockafellar1970convex] needs a hypothesis that the book does not write, the
  hypothesis is always one of two kinds: a linear map must be continuous, or a subspace must be
  closed. Both are automatic in finite dimensions.
* The continuity and compatibility conditions are fields `continuous_left` and `surjective_eval` of
  the two classes. The theorems `ConvexAnalysis.continuous_pairing` and
  `ConvexAnalysis.exists_pairing_eq` give them in the form that proofs apply.
-/

open Set

namespace ConvexAnalysis

/-! ### The affine functions of a pairing -/

section Affine

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)

/-- The **affine function** $x \mapsto \langle x, y \rangle - c$ of the pairing $B$, for $y \in F$
and $c \in \mathbb{R}$, with values in the extended reals.

These are the affine minorants that conjugacy quantifies over. Such a function lies below $f$
exactly when its epigraph contains $\operatorname{epi} f$, and $f^*(y)$ is the least $c$ for
which this happens. -/
noncomputable def affineFn (y : F) (c : ℝ) : E → EReal :=
  fun x => ((B x y : ℝ) : EReal) - (c : EReal)

variable {B}

/-- The affine function `ConvexAnalysis.affineFn B y c` takes the value $B(x, y) - c$ at $x$. -/
@[simp] theorem affineFn_apply (y : F) (c : ℝ) (x : E) :
    affineFn B y c x = ((B x y : ℝ) : EReal) - (c : EReal) := rfl

/-- The affine function `ConvexAnalysis.affineFn B y c` takes the real value $B(x, y) - c$ at $x$,
embedded in the extended reals. -/
theorem affineFn_eq_coe (y : F) (c : ℝ) (x : E) :
    affineFn B y c x = ((B x y - c : ℝ) : EReal) := by
  rw [affineFn_apply, EReal.coe_sub]

/-- An affine function of a pairing never takes the value $-\infty$. -/
theorem affineFn_ne_bot (y : F) (c : ℝ) (x : E) : affineFn B y c x ≠ ⊥ := by
  rw [affineFn_eq_coe]; exact EReal.coe_ne_bot _

/-- An affine function of a pairing never takes the value $+\infty$. -/
theorem affineFn_ne_top (y : F) (c : ℝ) (x : E) : affineFn B y c x ≠ ⊤ := by
  rw [affineFn_eq_coe]; exact EReal.coe_ne_top _

/-- An affine function of a pairing is proper: it is finite somewhere and never takes the value
$-\infty$. -/
theorem properConvex_affineFn (y : F) (c : ℝ) : ProperConvex (affineFn B y c) :=
  ⟨⟨0, lt_top_iff_ne_top.2 (affineFn_ne_top y c 0)⟩, affineFn_ne_bot y c⟩

/-- For $a, c, c' \in \mathbb{R}$, $y, y' \in F$ and $x \in E$, the affine function with slope
$a y + y'$ and constant $a c + c'$ takes at $x$ the value $$a (B(x, y) - c) + (B(x, y') - c').$$

This is the algebraic content of the "vertical half-space" step in the argument with affine
minorants. -/
theorem affineFn_smul_add (a : ℝ) (y y' : F) (c c' : ℝ) (x : E) :
    affineFn B (a • y + y') (a * c + c') x = ((a * (B x y - c) + (B x y' - c') : ℝ) : EReal) := by
  rw [affineFn_eq_coe, map_add, map_smul, smul_eq_mul]
  congr 1
  ring

/-- For $y \in F$ and $c \in \mathbb{R}$, the affine function $x \mapsto B(x, y) - c$ is convex. -/
theorem convexFn_affineFn (y : F) (c : ℝ) : ConvexFn (affineFn B y c) := by
  refine convexFn_of_epi_combo fun x x' μ ν hx hx' a b ha hb hab => ?_
  rw [affineFn_eq_coe, EReal.coe_le_coe_iff] at hx hx'
  rw [affineFn_eq_coe, EReal.coe_le_coe_iff, map_add, map_smul, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  have h1 : a * (B x y - c) ≤ a * μ := mul_le_mul_of_nonneg_left hx ha
  have h2 : b * (B x' y - c) ≤ b * ν := mul_le_mul_of_nonneg_left hx' hb
  have h3 : a * c + b * c = c := by linear_combination c * hab
  linarith

/-- **The inequality that the conjugate measures.** Let $f : E \to [-\infty, +\infty]$, $y \in F$
and $c \in \mathbb{R}$. The affine function $x \mapsto B(x, y) - c$ lies below $f$ if and only
if $$B(x, y) - f(x) \le c \quad \text{for every } x \in E.$$

No properness hypothesis is placed on $f$. -/
theorem affineFn_le_iff {f : E → EReal} {y : F} {c : ℝ} :
    affineFn B y c ≤ f ↔ ∀ x, ((B x y : ℝ) : EReal) - f x ≤ (c : EReal) :=
  forall_congr' fun _ => EReal.coe_sub_le_comm.symm

end Affine

/-! ### Affine functions and topology -/

section AffineTopology

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {y : F} {c : ℝ}

/-- Let $E$ be a topological space. If $x \mapsto B(x, y)$ is continuous on $E$, then the affine
function $x \mapsto B(x, y) - c$ is continuous as a map to the extended reals. -/
theorem continuous_affineFn (h : Continuous fun x => B x y) : Continuous (affineFn B y c) := by
  simp only [funext (affineFn_eq_coe (B := B) y c)]
  exact EReal.continuous_coe_iff.2 (h.sub continuous_const)

/-- Let $E$ be a topological space. If $x \mapsto B(x, y)$ is continuous on $E$, then the affine
function $x \mapsto B(x, y) - c$ is lower semicontinuous. -/
theorem lowerSemicontinuous_affineFn (h : Continuous fun x => B x y) :
    LowerSemicontinuous (affineFn B y c) := (continuous_affineFn h).lowerSemicontinuous

variable [IsTopologicalAddGroup E]

/-- Let $E$ carry a topology that makes it a topological additive group. If $x \mapsto B(x, y)$ is
continuous on $E$, then the affine function $x \mapsto B(x, y) - c$ is closed: it equals its
closure `ConvexAnalysis.convexCl`.

In the weak topology `WeakBilin B`, and so in any finer topology, the hypothesis holds for every
$y$. -/
theorem closedConvex_affineFn (h : Continuous fun x => B x y) : ClosedConvex (affineFn B y c) :=
  (closedConvex_iff_lowerSemicontinuous (affineFn_ne_bot y c)).2 (lowerSemicontinuous_affineFn h)

end AffineTopology

/-! ### Adjoint pairs -/

section AdjointPair

variable {E F G H K L : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
  [AddCommGroup K] [Module ℝ K] [AddCommGroup L] [Module ℝ L]

/-- Let $B$ pair $E$ with $F$ and $B'$ pair $G$ with $H$. Linear maps $A : E \to G$ and
$A' : H \to F$ form an **adjoint pair** if $$B'(A x, z) = B(x, A' z) \quad \text{for all } x \in
E,\ z \in H.$$

The adjoint is data, not a property of $A$: between arbitrarily paired spaces a transpose need
not exist, and when it exists it need not be unique unless $B$ separates on the right
(`ConvexAnalysis.IsAdjointPair.unique`). -/
def IsAdjointPair (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F) : Prop := ∀ x z, B' (A x) z = B x (A' z)

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ} {B'' : K →ₗ[ℝ] L →ₗ[ℝ] ℝ}

/-- The identity of $E$ is adjoint to the identity of $F$ for any pairing $B$ of $E$ with $F$. -/
theorem isAdjointPair_id : IsAdjointPair B B LinearMap.id LinearMap.id := fun _ _ => rfl

/-- If $(A, A')$ is an adjoint pair for the pairings $B$ and $B'$, then $(A', A)$ is an adjoint pair
for the flipped pairings $B'^{\mathrm{flip}}$ and $B^{\mathrm{flip}}$. -/
theorem IsAdjointPair.flip {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} (h : IsAdjointPair B B' A A') :
    IsAdjointPair B'.flip B.flip A' A := fun z x => (h x z).symm

/-- Adjoint pairs compose: if $(A, A')$ is an adjoint pair for $B$ and $B'$, and $(C, C')$ is an
adjoint pair for $B'$ and $B''$, then $(C A, A' C')$ is an adjoint pair for $B$ and $B''$. -/
theorem IsAdjointPair.comp {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {C : G →ₗ[ℝ] K} {C' : L →ₗ[ℝ] H}
    (h : IsAdjointPair B B' A A') (h' : IsAdjointPair B' B'' C C') :
    IsAdjointPair B B'' (C ∘ₗ A) (A' ∘ₗ C') := fun x w => by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h' (A x) w, h x (C' w)]

/-- If $(A, A')$ and $(C, C')$ are adjoint pairs for $B$ and $B'$, then so is $(A + C, A' + C')$. -/
theorem IsAdjointPair.add {A C : E →ₗ[ℝ] G} {A' C' : H →ₗ[ℝ] F} (h : IsAdjointPair B B' A A')
    (h' : IsAdjointPair B B' C C') : IsAdjointPair B B' (A + C) (A' + C') := fun x z => by
  simp only [LinearMap.add_apply, map_add, h x z, h' x z]

/-- If $(A, A')$ is an adjoint pair for $B$ and $B'$ and $a \in \mathbb{R}$, then so is
$(a A, a A')$. -/
theorem IsAdjointPair.smul {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} (a : ℝ)
    (h : IsAdjointPair B B' A A') : IsAdjointPair B B' (a • A) (a • A') := fun x z => by
  simp only [LinearMap.smul_apply, map_smul, h x z, smul_eq_mul]

/-- The adjoint is unique when $B$ separates on the right: if $(A, A')$ and $(A, C')$ are adjoint
pairs for $B$ and $B'$, and $B(x, y) = 0$ for all $x$ implies $y = 0$, then $A' = C'$. -/
theorem IsAdjointPair.unique (hB : B.SeparatingRight) {A : E →ₗ[ℝ] G} {A' C' : H →ₗ[ℝ] F}
    (h : IsAdjointPair B B' A A') (h' : IsAdjointPair B B' A C') : A' = C' := by
  ext z
  refine sub_eq_zero.1 (hB _ fun x => ?_)
  rw [map_sub, sub_eq_zero, ← h x z, ← h' x z]

end AdjointPair

/-! ### Adjoint pairs from Mathlib's adjoints -/

section InnerProduct

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- **A real Hilbert space paired with itself.** Let $E$ and $G$ be real Hilbert spaces and
$A : E \to G$ a continuous linear map. Then $A$ and its Hilbert adjoint $A^*$ form an adjoint
pair for the inner products of $E$ and $G$.

The adjoint is `ContinuousLinearMap.adjoint A`. -/
theorem isAdjointPair_clm_adjoint [CompleteSpace E] [CompleteSpace G] (A : E →L[ℝ] G) :
    IsAdjointPair (innerₗ E) (innerₗ G) (A : E →ₗ[ℝ] G)
      ((ContinuousLinearMap.adjoint A : G →L[ℝ] E) : G →ₗ[ℝ] E) := fun x z => by
  simpa using (ContinuousLinearMap.adjoint_inner_right A x z).symm

/-- **The setting of $\mathbb{R}^n$ in [rockafellar1970convex].** Let $E$ and $G$ be
finite-dimensional real inner product spaces and $A : E \to G$ a linear map. Then $A$ and its
adjoint $A^*$ form an adjoint pair for the inner products: $$\langle A x, z \rangle = \langle x,
A^* z \rangle \quad \text{for all } x \in E,\ z \in G.$$

In finite dimensions every linear map has an adjoint, and `LinearMap.adjoint` gives it. -/
theorem isAdjointPair_adjoint [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] (A : E →ₗ[ℝ] G) :
    IsAdjointPair (innerₗ E) (innerₗ G) A (LinearMap.adjoint A) := fun x z => by
  simpa using (LinearMap.adjoint_inner_right A x z).symm

end InnerProduct

section TopDual

variable {E G : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]

/-- **A space paired with its topological dual.** Let $E$ and $G$ be real vector spaces with
topologies, each paired with its continuous dual by $\langle x, g \rangle = g(x)$, and let
$A : E \to G$ be a continuous linear map. Then $A$ and the map $g \mapsto g \circ A$ from $G^*$
to $E^*$ form an adjoint pair: $$g(A x) = (g \circ A)(x).$$

No completeness or finite dimension is needed. The map $g \mapsto g \circ A$ is
`ContinuousLinearMap.precomp ℝ A`. The two pairings are `(topDualPairing ℝ E).flip` and
`(topDualPairing ℝ G).flip`. -/
theorem isAdjointPair_topDualPairing (A : E →L[ℝ] G) :
    IsAdjointPair (topDualPairing ℝ E).flip (topDualPairing ℝ G).flip (A : E →ₗ[ℝ] G)
      ((ContinuousLinearMap.precomp ℝ A : (G →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)) :
        (G →L[ℝ] ℝ) →ₗ[ℝ] (E →L[ℝ] ℝ)) := fun _ _ => rfl

end TopDual

/-! ### Products of pairings -/

section Prod

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The **product pairing** of $U \times X$ with $V \times Y$ determined by a pairing $B_u$ of $U$
with $V$ and a pairing $B_x$ of $X$ with $Y$: $$\langle (u, x), (v, y) \rangle = B_u(u, v) +
B_x(x, y).$$

This is the pairing that a convex bifunction $U \to X \to [-\infty, +\infty]$ is conjugated
against. -/
def prodPairing (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    (U × X) →ₗ[ℝ] (V × Y) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun p q => Bu p.1 q.1 + Bx p.2 q.2)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; ring)
    (fun _ _ _ => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul]; ring)

/-- The product pairing sends $(u, x)$ and $(v, y)$ to $B_u(u, v) + B_x(x, y)$. -/
@[simp] theorem prodPairing_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (p : U × X) (q : V × Y) : prodPairing Bu Bx p q = Bu p.1 q.1 + Bx p.2 q.2 := rfl

/-- The flip of the product pairing of $B_u$ and $B_x$ is the product pairing of the flips of $B_u$
and $B_x$. -/
theorem prodPairing_flip (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    (prodPairing Bu Bx).flip = prodPairing Bu.flip Bx.flip :=
  LinearMap.ext fun q => LinearMap.ext fun p => by
    simp

/-- The **sign change on the first factor** of a pairing $B$ of $U \times X$ with $V \times Y$:
$$\langle (u, x), q \rangle' = B((-u, x), q).$$

The adjoint $F^*$ of a convex bifunction is conjugated against this pairing;
`ConvexAnalysis.prodPairing` alone has the opposite sign on the first factor. -/
def negFst (B : (U × X) →ₗ[ℝ] (V × Y) →ₗ[ℝ] ℝ) : (U × X) →ₗ[ℝ] (V × Y) →ₗ[ℝ] ℝ :=
  B.comp (LinearMap.prodMap (-LinearMap.id) LinearMap.id)

/-- The pairing `ConvexAnalysis.negFst B` sends $(u, x)$ and $q$ to $B((-u, x), q)$. -/
@[simp] theorem negFst_apply (B : (U × X) →ₗ[ℝ] (V × Y) →ₗ[ℝ] ℝ) (p : U × X) (q : V × Y) :
    negFst B p q = B (-p.1, p.2) q := rfl

/-- The sign change of a product pairing sends $(u, x)$ and $(v, y)$ to $-B_u(u, v) + B_x(x, y)$. -/
@[simp] theorem negFst_prodPairing_apply (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (p : U × X) (q : V × Y) :
    negFst (prodPairing Bu Bx) p q = -Bu p.1 q.1 + Bx p.2 q.2 := by
  rw [negFst_apply, prodPairing_apply, map_neg, LinearMap.neg_apply]

/-- The sign change on the first factor is an involution. -/
@[simp] theorem negFst_negFst (B : (U × X) →ₗ[ℝ] (V × Y) →ₗ[ℝ] ℝ) : negFst (negFst B) = B :=
  LinearMap.ext fun p => LinearMap.ext fun q => by
    simp

/-- **The sign change of a product pairing is a product pairing**: the sign change of the product
pairing of $B_u$ and $B_x$ is the product pairing of $-B_u$ and $B_x$.

The result is an equation of linear maps, not a pointwise identity
(`ConvexAnalysis.negFst_prodPairing_apply`), so that the sign-changed product pairing inherits
continuity and compatibility from the factors by instance search. -/
theorem negFst_prodPairing (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    negFst (prodPairing Bu Bx) = prodPairing (-Bu) Bx :=
  LinearMap.ext fun p => LinearMap.ext fun q => by
    simp

/-- The flip of the sign change of the product pairing of $B_u$ and $B_x$ is the product pairing of
$-B_u^{\mathrm{flip}}$ and $B_x^{\mathrm{flip}}$. -/
theorem negFst_prodPairing_flip (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) :
    (negFst (prodPairing Bu Bx)).flip = prodPairing (-Bu.flip) Bx.flip :=
  LinearMap.ext fun q => LinearMap.ext fun p => by
    simp

end Prod

/-! ### The topological dual of $E \times \mathbb{R}$ -/

section ProdDual

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- Let $E$ be a real vector space with a topology, and $g$ a continuous linear functional on
$E \times \mathbb{R}$. Then $g(x, \mu) = g(x, 0) + g(0, 1) \mu$ for all $x \in E$ and
$\mu \in \mathbb{R}$. -/
theorem dual_prod_apply (g : (E × ℝ) →L[ℝ] ℝ) (x : E) (μ : ℝ) :
    g (x, μ) = g.comp (ContinuousLinearMap.inl ℝ E ℝ) x + g (0, 1) * μ := by
  have h : ((x, μ) : E × ℝ) = (x, 0) + μ • ((0 : E), (1 : ℝ)) := by simp
  rw [h, map_add, map_smul, smul_eq_mul]
  simp [ContinuousLinearMap.inl, mul_comm]

/-- **A continuous linear functional on $E \times \mathbb{R}$ splits uniquely.** Let $E$ be a real
vector space with a topology, and $g$ a continuous linear functional on $E \times \mathbb{R}$.
There is a unique pair $(h, c)$, with $h$ a continuous linear functional on $E$ and
$c \in \mathbb{R}$, such that $$g(x, \mu) = h(x) + c \mu \quad \text{for all } x \in E,\ \mu \in
\mathbb{R}.$$

The classification of the closed half-spaces of $E \times \mathbb{R}$ into vertical ($c = 0$),
upper ($c < 0$) and lower ($c > 0$) ones is read off from this decomposition. -/
theorem exists_unique_dual_prod (g : (E × ℝ) →L[ℝ] ℝ) :
    ∃! p : (E →L[ℝ] ℝ) × ℝ, ∀ (x : E) (μ : ℝ), g (x, μ) = p.1 x + p.2 * μ := by
  refine ⟨(g.comp (ContinuousLinearMap.inl ℝ E ℝ), g (0, 1)), dual_prod_apply g, ?_⟩
  rintro ⟨y, c⟩ h
  have hc : c = g (0, 1) := by simpa using (h 0 1).symm
  subst hc
  have hy : y = g.comp (ContinuousLinearMap.inl ℝ E ℝ) := by
    ext x
    have hx := h x 0
    simp only [mul_zero, add_zero] at hx
    simpa using hx.symm
  simp [hy]

end ProdDual


/-!
### Continuous and compatible topologies

The two conditions are two classes, in the order that the definitions force: the base class, then
the evaluation map `ConvexAnalysis.evalCLM`, then the extension which asserts that this map is onto.
Mathlib's `LinearMap.IsContPerfPair` cannot replace them: it asks for joint continuity of
$(x, y) \mapsto B(x, y)$, so that $F$ would need a topology, and for bijectivity on both sides where
surjectivity on one side is enough.
-/

section Compatible

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F]

/-- Let $E$ be a topological space. A pairing $B$ of $E$ with $F$ is **continuous** if for every
$y \in F$ the functional $x \mapsto B(x, y)$ is continuous on $E$.

This is all that the closedness results need (`ConvexAnalysis.closedConvex_convexConj`,
`ConvexAnalysis.convexConj_convexCl`, `ConvexAnalysis.isClosed_polarCone`,
`ConvexAnalysis.isClosed_subdifferential`), and it is strictly weaker than
`ConvexAnalysis.IsCompatiblePairing`. -/
class IsContinuousPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : Prop where
  /-- For every $y \in F$, the functional $x \mapsto B(x, y)$ is continuous on $E$. -/
  continuous_left (B) (y : F) : Continuous fun x : E => B x y

/-- If $B$ is a continuous pairing, then for every $y \in F$ the functional $x \mapsto B(x, y)$ is
continuous on $E$. -/
theorem continuous_pairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] (y : F) :
    Continuous fun x : E => B x y :=
  IsContinuousPairing.continuous_left B y

/-- **The evaluation map of a continuous pairing**: the linear map $y \mapsto B(\cdot, y)$ from $F$
to the continuous dual of $E$.

It turns characterizations of half-spaces that quantify over the continuous dual
`StrongDual ℝ E` into statements about $F$. `ConvexAnalysis.IsCompatiblePairing` asserts that it
is onto. -/
def evalCLM (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] : F →ₗ[ℝ] StrongDual ℝ E where
  toFun y := ⟨B.flip y, continuous_pairing B y⟩
  map_add' y₁ y₂ := ContinuousLinearMap.ext fun x => map_add (B x) y₁ y₂
  map_smul' a y := ContinuousLinearMap.ext fun x => map_smul (B x) a y

/-- The evaluation map sends $y$ to the functional $x \mapsto B(x, y)$. -/
@[simp] theorem evalCLM_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] (y : F) (x : E) :
    evalCLM B y x = B x y := rfl

/-- A continuous pairing $B$ gives a continuous pairing `B.flip.flip`.

The two are equal by definition but not syntactically, and instance search does not unfold
`LinearMap.flip`. Every result that is stated for one side and then used at `B.flip` asks for
this instance. -/
instance instIsContinuousPairingFlipFlip (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] :
    IsContinuousPairing B.flip.flip :=
  ‹IsContinuousPairing B›

/-- Let $E$ be a topological space. The topology of $E$ is **compatible** with the pairing $B$ if
$B$ is continuous and every continuous linear functional on $E$ has the form $x \mapsto B(x, y)$
for some $y \in F$, that is, `ConvexAnalysis.evalCLM B` is onto.

This is the hypothesis under which conjugacy is an involution. It does not say which compatible
topology $E$ carries: the weak topology $\sigma(E, F)$ is the coarsest one, but a Banach space
paired with its own dual satisfies the condition in the norm topology. -/
class IsCompatiblePairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : Prop
    extends IsContinuousPairing B where
  /-- Every continuous linear functional on $E$ has the form $x \mapsto B(x, y)$ for some $y \in F$.
  -/
  surjective_eval (B) : Function.Surjective (evalCLM B)

/-- If $B$ is a compatible pairing, then every continuous linear functional $g$ on $E$ has the form
$g(x) = B(x, y)$ for some $y \in F$. -/
theorem exists_pairing_eq (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B] (g : StrongDual ℝ E) :
    ∃ y : F, ∀ x, g x = B x y := by
  obtain ⟨y, hy⟩ := IsCompatiblePairing.surjective_eval B g
  exact ⟨y, fun x => by rw [← hy, evalCLM_apply]⟩

instance instIsCompatiblePairingFlipFlip (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B] :
    IsCompatiblePairing B.flip.flip :=
  ‹IsCompatiblePairing B›

/-!
### Negated pairings

The negation $-B$ is a pairing of the same two spaces, and the minimax theory uses it often: the
concave argument of a saddle function is paired against $-B_u$.
-/

omit [TopologicalSpace E] in
/-- The flip of $-B$ is $-B^{\mathrm{flip}}$. -/
theorem flip_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : (-B).flip = -B.flip :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

instance isContinuousPairing_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] :
    IsContinuousPairing (-B) :=
  ⟨fun y => (continuous_pairing B y).neg⟩

instance isCompatiblePairing_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B] :
    IsCompatiblePairing (-B) where
  surjective_eval := fun g => by
    obtain ⟨y, hy⟩ := exists_pairing_eq B (-g)
    refine ⟨y, ContinuousLinearMap.ext fun x => ?_⟩
    have h : (-B) x y = -(B x y) := rfl
    rw [evalCLM_apply, h, ← hy]
    exact neg_neg _

instance isCompatiblePairing_flip_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [TopologicalSpace F]
    [IsCompatiblePairing B.flip] : IsCompatiblePairing (-B).flip := by
  rw [flip_neg]
  infer_instance

end Compatible

section CompatibleInstances

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- A real vector space $E$ with a topology is compatibly paired with its own continuous dual, by
$\langle x, g \rangle = g(x)$, in its own topology.

The pairing is `(topDualPairing ℝ E).flip`. The Fenchel–Moreau theorem is applied through this
instance in practice. -/
instance instIsCompatiblePairingTopDual :
    IsCompatiblePairing (topDualPairing ℝ E).flip where
  continuous_left y := y.continuous
  surjective_eval g := ⟨g, rfl⟩

/-- A normed space $E$ is continuously paired with its continuous dual, by
$\langle g, x \rangle = g(x)$, for the norm topology of the dual.

Compatibility fails here unless $E$ is reflexive, which is why the closedness results are stated
for `ConvexAnalysis.IsContinuousPairing`. -/
instance instIsContinuousPairingTopDualNorm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : IsContinuousPairing (topDualPairing ℝ E) :=
  ⟨fun x => (ContinuousLinearMap.apply ℝ ℝ x).continuous⟩

/-- **Every continuous linear functional on the dual of a finite-dimensional normed space is
evaluation at a point.** Let $E$ be a finite-dimensional real normed space and $\Lambda$ a
continuous linear functional on $E^*$. There is $y \in E$ with $\Lambda(g) = g(y)$ for every
$g \in E^*$.

This is reflexivity in the form that the half-space arguments need. Equivalently,
`topDualPairing ℝ E`, as opposed to its flip, is a compatible pairing when $E$ is
finite-dimensional. -/
theorem exists_forall_apply_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : StrongDual ℝ (StrongDual ℝ E)) :
    ∃ y : E, ∀ g : StrongDual ℝ E, Λ g = g y := by
  set φ : Module.Dual ℝ (Module.Dual ℝ E) :=
    (Λ : StrongDual ℝ E →ₗ[ℝ] ℝ).comp
      (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).toLinearMap with hφ
  refine ⟨(Module.evalEquiv ℝ E).symm φ, fun g => ?_⟩
  have h := Module.apply_evalEquiv_symm_apply (R := ℝ) (M := E) (g : E →ₗ[ℝ] ℝ) φ
  have hg : LinearMap.toContinuousLinearMap (g : E →ₗ[ℝ] ℝ) = g :=
    ContinuousLinearMap.ext fun x => rfl
  rw [hφ] at h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hg, ContinuousLinearMap.coe_coe] at h
  exact h.symm

/-- A finite-dimensional normed space $E$ is compatibly paired with its continuous dual from the
side of the dual too: the pairing $\langle g, x \rangle = g(x)$ is compatible for the norm
topology of $E^*$.

With `ConvexAnalysis.instIsCompatiblePairingTopDual`, this makes both `topDualPairing ℝ E` and
its flip compatible, so that a conjugate $f^*$ can be treated as a function in its own right. -/
instance instIsCompatiblePairingTopDualFinite {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] : IsCompatiblePairing (topDualPairing ℝ E) where
  continuous_left x := (ContinuousLinearMap.apply ℝ ℝ x).continuous
  surjective_eval Λ := by
    obtain ⟨y, hy⟩ := exists_forall_apply_eq Λ
    exact ⟨y, ContinuousLinearMap.ext fun g => (hy g).symm⟩

/-- A real Hilbert space is compatibly paired with itself by the inner product. This is the
Fréchet–Riesz theorem. -/
instance instIsCompatiblePairingInner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] : IsCompatiblePairing (innerₗ E) where
  continuous_left y := by simpa using (continuous_id.inner continuous_const : _)
  surjective_eval g := ⟨(InnerProductSpace.toDual ℝ E).symm g, by
    ext x
    rw [evalCLM_apply, innerₗ_apply_apply, real_inner_comm,
      InnerProductSpace.toDual_symm_apply]⟩

end CompatibleInstances

section ProdInstances

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace U] [TopologicalSpace X]

/-- Let $U$ and $X$ be topological spaces. If $B_u$ (pairing $U$ with $V$) and $B_x$ (pairing $X$
with $Y$) are continuous pairings, then their product pairing is a continuous pairing of
$U \times X$, with the product topology, with $V \times Y$. -/
instance instIsContinuousPairingProd (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu] [IsContinuousPairing Bx] :
    IsContinuousPairing (prodPairing Bu Bx) where
  continuous_left q := by
    simp only [prodPairing_apply]
    exact ((continuous_pairing Bu q.1).comp continuous_fst).add
      ((continuous_pairing Bx q.2).comp continuous_snd)

/-- Let $U$ and $X$ be topological spaces. If $B_u$ and $B_x$ are compatible pairings, then their
product pairing is a compatible pairing of $U \times X$ with $V \times Y$.

The proof splits a continuous linear functional on $U \times X$ as
$g(u, x) = g(u, 0) + g(0, x)$. -/
instance instIsCompatiblePairingProd (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bx] :
    IsCompatiblePairing (prodPairing Bu Bx) where
  toIsContinuousPairing := instIsContinuousPairingProd Bu Bx
  surjective_eval g := by
    obtain ⟨v, hv⟩ := exists_pairing_eq Bu (g.comp (ContinuousLinearMap.inl ℝ U X))
    obtain ⟨y, hy⟩ := exists_pairing_eq Bx (g.comp (ContinuousLinearMap.inr ℝ U X))
    refine ⟨(v, y), ContinuousLinearMap.ext fun p => ?_⟩
    have hsplit : ((p.1, 0) : U × X) + ((0, p.2) : U × X) = p := by
      rw [Prod.mk_add_mk, add_zero, zero_add]
    rw [evalCLM_apply, prodPairing_apply, ← hv, ← hy]
    simpa using (map_add g ((p.1, 0) : U × X) ((0, p.2) : U × X)).symm.trans (by rw [hsplit])

/-- If $B_u$ and $B_x$ are continuous pairings, then the sign change on the first factor of their
product pairing is a continuous pairing. The adjoint of a convex bifunction is conjugated
against this pairing. -/
instance instIsContinuousPairingNegFstProd (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu] [IsContinuousPairing Bx] :
    IsContinuousPairing (negFst (prodPairing Bu Bx)) := by
  rw [negFst_prodPairing]
  infer_instance

/-- If $B_u$ and $B_x$ are compatible pairings, then the sign change on the first factor of their
product pairing is a compatible pairing. The adjoint of a convex bifunction is conjugated
against this pairing. -/
instance instIsCompatiblePairingNegFstProd (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu] [IsCompatiblePairing Bx] :
    IsCompatiblePairing (negFst (prodPairing Bu Bx)) := by
  rw [negFst_prodPairing]
  infer_instance

end ProdInstances

section ProdDualInstances

variable {U V X Y : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace V] [TopologicalSpace Y]

/-- Let $V$ and $Y$ be topological spaces. If the flips of $B_u$ and $B_x$ are continuous pairings,
then the flip of their product pairing is a continuous pairing of $V \times Y$, with the product
topology, with $U \times X$.

This is not an instance, because `(ConvexAnalysis.prodPairing Bu Bx).flip` is not syntactically
a product pairing; `ConvexAnalysis.prodPairing_flip` turns it into one. -/
theorem isContinuousPairing_prodPairing_flip (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsContinuousPairing Bx.flip] :
    IsContinuousPairing (prodPairing Bu Bx).flip := by
  rw [prodPairing_flip]
  infer_instance

/-- If the flips of $B_u$ and $B_x$ are continuous pairings, then the flip of the sign change of
their product pairing is a continuous pairing.

Unlike `ConvexAnalysis.isContinuousPairing_prodPairing_flip`, this is an instance, because
`(ConvexAnalysis.negFst (ConvexAnalysis.prodPairing Bu Bx)).flip` matches syntactically. -/
instance instIsContinuousPairingNegFstProdFlip (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsContinuousPairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsContinuousPairing Bx.flip] :
    IsContinuousPairing (negFst (prodPairing Bu Bx)).flip := by
  rw [negFst_prodPairing_flip]
  infer_instance

/-- If the flips of $B_u$ and $B_x$ are compatible pairings, then the flip of the sign change of
their product pairing is a compatible pairing. This is the compatible counterpart of
`ConvexAnalysis.instIsContinuousPairingNegFstProdFlip`. -/
instance instIsCompatiblePairingNegFstProdFlip (Bu : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    [IsCompatiblePairing Bu.flip] (Bx : X →ₗ[ℝ] Y →ₗ[ℝ] ℝ) [IsCompatiblePairing Bx.flip] :
    IsCompatiblePairing (negFst (prodPairing Bu Bx)).flip := by
  rw [negFst_prodPairing_flip]
  infer_instance

end ProdDualInstances


end ConvexAnalysis
