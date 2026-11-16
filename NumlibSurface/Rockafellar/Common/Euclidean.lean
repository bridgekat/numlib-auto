/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Convergence
import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Duality.InnerPairing
import Numlib.Analysis.Convex.Duality.GaugeLike
import Numlib.Analysis.Convex.Duality.Level
import Numlib.Analysis.Convex.Duality.Relint
import Numlib.Analysis.Convex.EuclideanProd
import Numlib.Analysis.Convex.HullDirections
import Numlib.Analysis.Convex.Operations.Basic
import Numlib.Analysis.Convex.Recession.Cone
import Numlib.Analysis.Convex.Simplicial
import Numlib.Analysis.Convex.Subdifferential.Defs
import Numlib.LinearAlgebra.Subspace
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.TFAE

/-!
# Rockafellar, shared conventions: the Euclidean space $\mathbb{R}^n$

This module fixes the ambient space of the surface library for [rockafellar1970convex]. It is not a
section of the book. The book works throughout in $\mathbb{R}^n$ with the inner product
$\langle x, y \rangle = \sum_i x_i y_i$, and every section module of `NumlibSurface.Rockafellar` is
stated in the vocabulary of this module. The space $\mathbb{R}^n$ is `Rockafellar.Rn n`, defined as
`EuclideanSpace ℝ (Fin n)`. The inner product on it is `Rockafellar.pairing n`, read as a bilinear
map. The backbone states its duality theory for an abstract pairing of two real vector spaces, and
this one pairing instantiates all of it. The general facts about a pairing of a space with itself by
an inner product are in the backbone module `Numlib.Analysis.Convex.Duality.InnerPairing`. This
module gives their form for $\mathbb{R}^n$, in the namespace `Rockafellar` that the rest of the
library uses.

## Main definitions

* `Rockafellar.Rn`: the space $\mathbb{R}^n$ with its Euclidean structure.
* `Rockafellar.pairing`: the inner product $\langle x, y \rangle$ on $\mathbb{R}^n$, as a bilinear
  map, so that the duality theory of the backbone applies.
* `Rockafellar.pairingProd`: the pairing $\langle (u, x), (u^*, x^*) \rangle = \langle u, u^*
  \rangle + \langle x, x^* \rangle$ of $\mathbb{R}^m \times \mathbb{R}^n$ with itself.
* `Rockafellar.pairingAdjoint`: the pairing $-\langle u, u^* \rangle + \langle x, x^* \rangle$ of
  $\mathbb{R}^m \times \mathbb{R}^n$ with itself, which the adjoint of a bifunction uses.
* `Rockafellar.linFn`: the linear function $x \mapsto \langle x, b \rangle$ defined by a vector $b$.

## Main results

* `Rockafellar.flip_pairing`: the pairing is equal to its flip.
* `Rockafellar.pairing_comm`, `Rockafellar.forall_pairing_le_comm`,
  `Rockafellar.forall_pairing_lt_comm`: the pairing is symmetric, so a system
  $\langle a_i, x \rangle \le \alpha_i$ can be written with the variable in either argument.
* `Rockafellar.pairing_eq_sum`, `Rockafellar.pairing_two`: the pairing in coordinates.
* `Rockafellar.exists_linFn`, `Rockafellar.linFn_eq_toDual`, `Rockafellar.linFn_eq_zero_iff`,
  `Rockafellar.toDual_apply_eq_pairing`, `Rockafellar.separatingRight_pairing`: every continuous
  linear function on $\mathbb{R}^n$ is $\langle \cdot, b \rangle$ for a vector $b$, and the related
  separation facts.
* `Rockafellar.pairingProd_euclideanProdEquiv`: the pairing of $\mathbb{R}^m \times \mathbb{R}^n$ is
  the inner product of $\mathbb{R}^{m+n}$ after concatenation of coordinates.

## Implementation notes

* A textbook in $\mathbb{R}^n$ identifies the space with its dual and writes $x^*$ for a vector of
  the same space. Both arguments of `Rockafellar.pairing n` are in `Rockafellar.Rn n`, so the star
  of the book is a naming convention here and not a distinction of types. The backbone keeps its two
  spaces apart, so that the general theory cannot use the identification of a space with its dual
  without saying so.
* `Rockafellar.Rn`, `Rockafellar.pairing`, `Rockafellar.pairingProd`, `Rockafellar.pairingAdjoint`
  and `Rockafellar.linFn` are abbreviations, so that instance search sees the underlying Mathlib and
  backbone terms.
-/

namespace Rockafellar

open ConvexAnalysis

/-- The ambient space of the surface library: the space $\mathbb{R}^n$ of real $n$-tuples with its
Euclidean structure, which is `EuclideanSpace ℝ (Fin n)`.

Coordinates are indexed by `Fin n`, so they are numbered from $0$ to $n - 1$. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The **standard inner product** $\langle x, y \rangle$ on $\mathbb{R}^n$, as a bilinear map
$\mathbb{R}^n \times \mathbb{R}^n \to \mathbb{R}$. This is the form that the duality theory of
the backbone takes, and a statement of the book that writes $\langle x, x^* \rangle$ for vectors
of one space means this pairing.

It is Mathlib's `innerₗ` for `Rockafellar.Rn n`. It is an `abbrev` and not a `def`, because
instance search does not unfold a plain `def`, and every pairing class that the surface needs is
stated for `innerₗ`. -/
noncomputable abbrev pairing (n : ℕ) : Rn n →ₗ[ℝ] Rn n →ₗ[ℝ] ℝ := innerₗ (Rn n)

/-- The pairing $\langle x, y \rangle$ is the inner product of $x$ and $y$ in `Rockafellar.Rn n`. -/
@[simp] theorem pairing_apply {n : ℕ} (x y : Rn n) : pairing n x y = inner ℝ x y := rfl

/-- The pairing on $\mathbb{R}^n$ is equal to its flip:
$\langle y, x \rangle = \langle x, y \rangle$ as bilinear maps.

A backbone statement that asks for the flipped pairing `(Rockafellar.pairing n).flip` is
therefore a statement about `Rockafellar.pairing n` again. -/
@[simp] theorem flip_pairing (n : ℕ) : (pairing n).flip = pairing n :=
  flip_eq_self (pairing n)

/-- The pairing is symmetric: for $x, y \in \mathbb{R}^n$,
$\langle x, y \rangle = \langle y, x \rangle$.

The book writes a linear system as $\langle a_i, x \rangle \le \alpha_i$, with the data in the
first argument. The backbone puts the variable in the first argument of `B x y`. -/
theorem pairing_comm {n : ℕ} (x y : Rn n) : pairing n x y = pairing n y x := real_inner_comm y x

/-- Let $(a_i)_{i \in I}$ be vectors in $\mathbb{R}^n$, let $(\alpha_i)_{i \in I}$ be real numbers,
and let $x \in \mathbb{R}^n$. Then $\langle a_i, x \rangle \le \alpha_i$ for all $i$ if and only
if $\langle x, a_i \rangle \le \alpha_i$ for all $i$.

This translates a system of weak inequalities between the form of the book and the form of the
backbone. -/
theorem forall_pairing_le_comm {n : ℕ} {ι : Sort*} (a : ι → Rn n) (α : ι → ℝ) (x : Rn n) :
    (∀ i, pairing n (a i) x ≤ α i) ↔ ∀ i, pairing n x (a i) ≤ α i :=
  forall_congr' fun i => by rw [pairing_comm]

/-- Let $(a_i)_{i \in I}$ be vectors in $\mathbb{R}^n$, let $(\alpha_i)_{i \in I}$ be real numbers,
and let $x \in \mathbb{R}^n$. Then $\langle a_i, x \rangle < \alpha_i$ for all $i$ if and only
if $\langle x, a_i \rangle < \alpha_i$ for all $i$.

This translates a system of strict inequalities between the form of the book and the form of the
backbone. -/
theorem forall_pairing_lt_comm {n : ℕ} {ι : Sort*} (a : ι → Rn n) (α : ι → ℝ) (x : Rn n) :
    (∀ i, pairing n (a i) x < α i) ↔ ∀ i, pairing n x (a i) < α i :=
  forall_congr' fun i => by rw [pairing_comm]

/-- The pairing in coordinates: for $u, v \in \mathbb{R}^n$,
$\langle u, v \rangle = \sum_i u_i v_i$. -/
theorem pairing_eq_sum {n : ℕ} (u v : Rn n) : pairing n u v = ∑ i, u i * v i := by
  simp only [pairing_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The pairing on $\mathbb{R}^2$ in coordinates: $\langle u, v \rangle = u_0 v_0 + u_1 v_1$, with
the coordinates numbered from $0$.

Almost all counterexamples of the book are in $\mathbb{R}^2$, and their computations start from
this formula. -/
theorem pairing_two (u v : Rn 2) : pairing 2 u v = u 0 * v 0 + u 1 * v 1 := by
  rw [pairing_eq_sum, Fin.sum_univ_two]

/-- Each coordinate function $x \mapsto x_i$ on $\mathbb{R}^n$ is continuous.

A counterexample that cuts a region out of $\mathbb{R}^n$ by inequalities between coordinates
uses this to show that the region is open. -/
theorem continuous_coord {n : ℕ} (i : Fin n) : Continuous fun x : Rn n => x i :=
  PiLp.continuous_apply (p := 2) (fun _ : Fin n => ℝ) i

/-- The pairing on $\mathbb{R}^n$ separates points in the second argument: if
$\langle x, y \rangle = 0$ for all $x$, then $y = 0$.

This is the hypothesis `LinearMap.SeparatingRight` that the backbone's duality for level sets
and recession cones uses in place of the condition $y \neq 0$ of a book. -/
theorem separatingRight_pairing (n : ℕ) : (pairing n).SeparatingRight :=
  separatingRight_innerL

/-- The **product pairing** of $\mathbb{R}^m \times \mathbb{R}^n$ with itself:
$$\langle (u, x), (u^*, x^*) \rangle = \langle u, u^* \rangle + \langle x, x^* \rangle.$$
A bifunction from $\mathbb{R}^m$ to $\mathbb{R}^n$ is conjugated with respect to this pairing.

It is `ConvexAnalysis.prodPairing` of the two pairings `Rockafellar.pairing m` and
`Rockafellar.pairing n`. -/
noncomputable abbrev pairingProd (m n : ℕ) : (Rn m × Rn n) →ₗ[ℝ] (Rn m × Rn n) →ₗ[ℝ] ℝ :=
  prodPairing (pairing m) (pairing n)

/-- The **sign-flipped product pairing** of $\mathbb{R}^m \times \mathbb{R}^n$ with itself:
$$\langle (u, x), (u^*, x^*) \rangle = -\langle u, u^* \rangle + \langle x, x^* \rangle.$$
This is the pairing for which Section 30 of [rockafellar1970convex] states the adjoint $F^*$ of
a convex bifunction $F$.

It is `ConvexAnalysis.negFst` applied to `Rockafellar.pairingProd m n`. -/
noncomputable abbrev pairingAdjoint (m n : ℕ) : (Rn m × Rn n) →ₗ[ℝ] (Rn m × Rn n) →ₗ[ℝ] ℝ :=
  negFst (pairingProd m n)

/-- For $p, q \in \mathbb{R}^m \times \mathbb{R}^n$, the product pairing of $p$ and $q$ is the inner
product in $\mathbb{R}^{m+n}$ of the vectors obtained by concatenation of coordinates.

The concatenation is `euclideanProdEquiv`. A text in $\mathbb{R}^n$ makes this identification
without comment when it writes a point of $\mathbb{R}^m \times \mathbb{R}^n$ as a point of
$\mathbb{R}^{m+n}$. -/
theorem pairingProd_euclideanProdEquiv {m n : ℕ} (p q : Rn m × Rn n) :
    pairingProd m n p q = pairing (m + n) (euclideanProdEquiv m n p) (euclideanProdEquiv m n q) :=
  (inner_euclideanProdEquiv p q).symm

/-!
### Dimension

The equation $\dim \mathbb{R}^n = n$ is Mathlib's `finrank_euclideanSpace_fin`, which Mathlib does
not mark `simp`. The attribute is added here, because every dimension count in the surface uses it.
-/

attribute [simp] finrank_euclideanSpace_fin

/-!
### Instances

Each `example` below asserts that instance search finds a class that the surface needs, with no
hypothesis. Together they test that `Rockafellar.Rn` and the pairings above instantiate the
backbone.
-/

section Instances

variable {m n : ℕ}

-- Ambient structure on `Rn n`.
noncomputable example : NormedAddCommGroup (Rn n) := inferInstance
noncomputable example : InnerProductSpace ℝ (Rn n) := inferInstance
noncomputable example : NormedSpace ℝ (Rn n) := inferInstance
example : FiniteDimensional ℝ (Rn n) := inferInstance
example : CompleteSpace (Rn n) := inferInstance
example : ProperSpace (Rn n) := inferInstance
example : T2Space (Rn n) := inferInstance
example : LocallyConvexSpace ℝ (Rn n) := inferInstance
example : IsTopologicalAddGroup (Rn n) := inferInstance
example : ContinuousSMul ℝ (Rn n) := inferInstance
example : TopologicalSpace.SeparableSpace (Rn n) := inferInstance
example : SeparatingDual ℝ (Rn n) := inferInstance

-- The self-pairing, and the flips the backbone asks for.
example : IsInnerPairing (pairing n) := inferInstance
example : IsContinuousInnerPairing (pairing n) := inferInstance
example : IsContinuousPairing (pairing n) := inferInstance
example : IsCompatiblePairing (pairing n) := inferInstance
example : IsContinuousPairing (pairing n).flip := inferInstance
example : IsCompatiblePairing (pairing n).flip := inferInstance
example : IsCompatiblePairing (pairing n).flip.flip := inferInstance

-- Negated pairings: §34 and §37 conjugate against these.
example : IsContinuousPairing (-pairing n) := inferInstance
example : IsCompatiblePairing (-pairing n) := inferInstance
example : IsCompatiblePairing (-pairing n).flip := inferInstance

-- Product pairings: §29–§30, §37.
example : IsInnerPairing (pairingProd m n) := inferInstance
example : IsContinuousPairing (pairingProd m n) := inferInstance
example : IsCompatiblePairing (pairingProd m n) := inferInstance
example : IsContinuousPairing (pairingProd m n).flip := inferInstance
example : IsCompatiblePairing (pairingProd m n).flip := inferInstance

-- The adjoint pairing of §30.
example : IsContinuousPairing (pairingAdjoint m n) := inferInstance
example : IsCompatiblePairing (pairingAdjoint m n) := inferInstance
example : IsContinuousPairing (pairingAdjoint m n).flip := inferInstance
example : IsCompatiblePairing (pairingAdjoint m n).flip := inferInstance

end Instances

/-!
### Linear functions as vectors

A book writes a linear function on $\mathbb{R}^n$ as $\langle \cdot, b \rangle$ and quantifies over
the vector $b$. The backbone quantifies over continuous linear functionals, which is what separation
produces. The translation is Mathlib's `innerSL ℝ b`, here under the name `Rockafellar.linFn b`. The
facts about it are backbone facts, stated again for $\mathbb{R}^n$.
-/

section LinFn

variable {n : ℕ}

/-- The vector $b \in \mathbb{R}^n$ read as the continuous linear function
$x \mapsto \langle x, b \rangle$.

It is Mathlib's `innerSL ℝ b`. -/
noncomputable abbrev linFn (b : Rn n) : Rn n →L[ℝ] ℝ := innerSL ℝ b

/-- The linear function defined by $b$ takes the value $\langle x, b \rangle$ at $x$. -/
@[simp] theorem linFn_apply (b x : Rn n) : linFn b x = pairing n x b := by
  simp only [linFn, innerSL_apply_apply, pairing_apply]
  exact real_inner_comm x b

/-- For $b \in \mathbb{R}^n$, the function $\langle \cdot, b \rangle$ is zero if and only if
$b = 0$.

So the condition $b \neq 0$ and the condition that $\{x \mid \langle x, b \rangle = \beta\}$ is
a hyperplane are the same. -/
theorem linFn_eq_zero_iff {b : Rn n} : linFn b = 0 ↔ b = 0 :=
  innerSL_eq_zero_iff

/-- Every continuous linear function $f$ on $\mathbb{R}^n$ has the form
$f = \langle \cdot, b \rangle$ for some $b \in \mathbb{R}^n$.

This identification (the Fréchet–Riesz theorem) lets a surface statement quantify over vectors
while its proof quantifies over functionals. -/
theorem exists_linFn (f : Rn n →L[ℝ] ℝ) : ∃ b : Rn n, linFn b = f :=
  exists_innerSL_eq f

/-- For $b \in \mathbb{R}^n$, the linear function $\langle \cdot, b \rangle$ is the image of $b$
under the Fréchet–Riesz map `InnerProductSpace.toDual`.

So the translation from vectors to functionals in the surface is the same map as the one in the
backbone's results on gradients. -/
theorem linFn_eq_toDual (b : Rn n) : linFn b = InnerProductSpace.toDual ℝ (Rn n) b :=
  (toDual_eq_innerSL b).symm

/-- For $v, x \in \mathbb{R}^n$, the functional that represents $v$ by the Fréchet–Riesz map takes
the value $\langle x, v \rangle$ at $x$.

The backbone results about `ConvexAnalysis.HasGradientAtFn` give the left-hand side, and the
surface statements use the right-hand side. -/
theorem toDual_apply_eq_pairing (v x : Rn n) :
    (InnerProductSpace.toDual ℝ (Rn n) v) x = pairing n x v :=
  toDual_apply_eq_innerL v x

end LinFn

/-!
### The adjoint of a linear transformation

For two arbitrary paired spaces, the transpose of a linear map need not exist, so the backbone takes
the adjoint of a linear map as data. On $\mathbb{R}^n$ the adjoint is canonical, and
`ConvexAnalysis.isAdjointPair_adjoint` already covers `innerₗ (Rockafellar.Rn n)`. A surface section
writes the adjoint $A^*$ of a linear transformation $A$ as `LinearMap.adjoint A` and supplies the
hypothesis with this lemma.
-/

end Rockafellar
