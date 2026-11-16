/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.GaugeLike
import Numlib.Analysis.Convex.Duality.Ops
import NumlibSurface.Rockafellar.Chapter02.Section07

/-!
# Rockafellar, Section 12: Conjugates of convex functions

This module formalizes Section 12 of [rockafellar1970convex]. For a function
$f : \mathbb{R}^n \to [-\infty, +\infty]$ the conjugate is $f^*(x^*) = \sup_x \{\langle x, x^*
\rangle - f(x)\}$. The section shows that a closed convex function is the supremum of its affine
minorants, that $f^*$ is closed and convex, that $f^{**} = \operatorname{cl} f$ for convex $f$ (the
Fenchel–Moreau theorem), so that conjugacy is a symmetric one-to-one correspondence on the closed
proper convex functions, and how $f^*$ changes under a change of variables. It ends with the
monotone conjugate $g^+$ of a non-decreasing function on the non-negative orthant. All 9 numbered
results of the section are formalized. The proofs specialize the conjugacy theory of
`Numlib.Analysis.Convex.Duality.Conjugate` to the self-pairing of $\mathbb{R}^n$.

## Main definitions

* `Rockafellar.IsOrthogonalEquiv`: a linear bijection $A$ of $\mathbb{R}^n$ with
  $\langle Ax, Ay \rangle = \langle x, y \rangle$.
* `Rockafellar.SymmetricWrt`: $f$ is symmetric with respect to a set $G$ of linear bijections if
  $f(Ax) = f(x)$ for all $x$ and all $A \in G$.
* `Rockafellar.nonnegOrthant`: the non-negative orthant
  $K = \{z \mid z_j \ge 0 \text{ for all } j\}$.
* `Rockafellar.posPart`: the componentwise positive part $y^+$ of $y$.
* `Rockafellar.MonotoneOrthantFn`: a non-decreasing closed convex function on $K$, finite at the
  origin and $+\infty$ off $K$.
* `Rockafellar.monotoneConjOrthant`: the monotone conjugate $g^+$, which is $g^*$ on $K$ and
  $+\infty$ off $K$.

## Main results

* Theorem 12.1, `Rockafellar.theorem_12_1`: a closed convex function is the pointwise supremum of
  the affine functions below it.
* Corollary 12.1.1, `Rockafellar.corollary_12_1_1`: for any $f$,
  $\operatorname{cl}(\operatorname{conv} f)$ is the pointwise supremum of the affine functions below
  $f$.
* Corollary 12.1.2, `Rockafellar.corollary_12_1_2`: a proper convex function has an affine minorant.
* Theorem 12.2, `Rockafellar.theorem_12_2_convex`, `Rockafellar.theorem_12_2_closed`,
  `Rockafellar.theorem_12_2_proper`, `Rockafellar.theorem_12_2_conj_clFn`,
  `Rockafellar.theorem_12_2_biconj`: $f^*$ is convex and closed, $f^*$ is proper if and only if $f$
  is, $(\operatorname{cl} f)^* = f^*$, and $f^{**} = \operatorname{cl} f$ for convex $f$.
* Corollary 12.2.1, `Rockafellar.corollary_12_2_1`: conjugacy is a symmetric one-to-one
  correspondence on the closed proper convex functions.
* Corollary 12.2.2, `Rockafellar.corollary_12_2_2`: for convex $f$, the supremum that defines $f^*$
  can be taken over $\operatorname{ri}(\operatorname{dom} f)$.
* Fenchel's inequality, `Rockafellar.fenchel_inequality`:
  $\langle x, x^* \rangle \le f(x) + f^*(x^*)$ for proper $f$.
* Theorem 12.3, `Rockafellar.theorem_12_3`: the conjugate of $x \mapsto h(A(x - a)) + \langle x, a^*
  \rangle + \alpha$.
* Corollary 12.3.1, `Rockafellar.corollary_12_3_1`: a closed convex $f$ is symmetric with respect to
  a set of orthogonal transformations if and only if $f^*$ is.
* Theorem 12.4, `Rockafellar.theorem_12_4_mem`, `Rockafellar.theorem_12_4_involutive`: the monotone
  conjugate of a non-decreasing closed convex function on $K$ that is finite at the origin is again
  such a function, and $g^{++} = g$.

## Proof outline

The book prints Theorem 12.4 without a proof. The proof here does not use the symmetrization
$f(x) = g(|x|)$ that the text of the section suggests, and so it does not need to know whether
$x \mapsto g(|x|)$ is convex. The key fact is `Rockafellar.convexConj_posPart`: for $g$ as in the
theorem, $g^*(y^+) = g^*(y)$, where $y^+$ is the componentwise positive part of $y$. Thus the
supremum that defines $g^{++}$ can be taken over $K$ alone, and the Fenchel–Moreau theorem gives
$g^{++} = g$.

## Conventions

* The conjugate $f^*$ is `ConvexAnalysis.convexConj (Rockafellar.pairing n) f`. It is defined by the
  supremum of the book for an arbitrary $f : \mathbb{R}^n \to [-\infty, +\infty]$, and the supremum
  of the empty set is $-\infty$.
* An affine function on $\mathbb{R}^n$ is $x \mapsto \langle x, b \rangle - \beta$, which is
  `ConvexAnalysis.affineFn (Rockafellar.pairing n) b β`. It is indexed by the pair $(b, \beta)$.
* A function on the orthant $K$ is a function on $\mathbb{R}^n$ that is $+\infty$ off $K$, following
  the convention of Section 4.

## Deviations from the source

* **Theorem 12.2**, convexity and closedness of $f^*$ and $(\operatorname{cl} f)^* = f^*$
  (generalization). These clauses hold for every $f$, not only for convex $f$. See
  `Rockafellar.theorem_12_2_convex`, `Rockafellar.theorem_12_2_closed` and
  `Rockafellar.theorem_12_2_conj_clFn`.
* **Fenchel's inequality** (generalization). The inequality holds for every proper $f$, not only for
  proper convex $f$. See `Rockafellar.fenchel_inequality`.
* **Theorem 12.3** (generalization). The function $h$ need not be convex. See
  `Rockafellar.theorem_12_3`.
-/

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ} {f : Rn n → EReal}

/-! ### Theorem 12.1 -/

/-- **Theorem 12.1** of [rockafellar1970convex]. Let $f : \mathbb{R}^n \to [-\infty, +\infty]$ be a
closed convex function. Then $f$ is the pointwise supremum of all affine functions $h \le f$:
for every $x$,
$$f(x) = \sup \{\langle x, b \rangle - \beta \mid (b, \beta) \in \mathbb{R}^n \times
  \mathbb{R},\ \langle z, b \rangle - \beta \le f(z) \text{ for all } z\}.$$

An affine function on $\mathbb{R}^n$ is $x \mapsto \langle x, b \rangle - \beta$, which is
`ConvexAnalysis.affineFn (Rockafellar.pairing n) b β`. Every affine function has this form
because `Rockafellar.pairing n` identifies $\mathbb{R}^n$ with its own dual. The supremum of the
empty set is $-\infty$, which covers the case $f \equiv -\infty$. -/
theorem theorem_12_1 (hf : ConvexFn f) (hc : ClosedConvex f) :
    f = fun x => ⨆ p ∈ {p : Rn n × ℝ | affineFn (pairing n) p.1 p.2 ≤ f},
      affineFn (pairing n) p.1 p.2 x :=
  eq_biSup_affineFn hf hc

/-- **Corollary 12.1.1** of [rockafellar1970convex]. Let $f : \mathbb{R}^n \to [-\infty, +\infty]$
be any function. Then $\operatorname{cl}(\operatorname{conv} f)$ is the pointwise supremum of
all affine functions on $\mathbb{R}^n$ that are majorized by $f$:
$$\operatorname{cl}(\operatorname{conv} f)(x) = \sup \{\langle x, b \rangle - \beta \mid \langle
  z, b \rangle - \beta \le f(z) \text{ for all } z\}.$$
In particular, $f$ and $\operatorname{cl}(\operatorname{conv} f)$ have the same affine
minorants.

The convex hull $\operatorname{conv} f$ is `ConvexAnalysis.convHullFn f`, and the closure is
`ConvexAnalysis.convexCl`. -/
theorem corollary_12_1_1 (f : Rn n → EReal) :
    convexCl (convHullFn f) = fun x => ⨆ p ∈ {p : Rn n × ℝ | affineFn (pairing n) p.1 p.2 ≤ f},
      affineFn (pairing n) p.1 p.2 x := by
  have hset : {p : Rn n × ℝ | affineFn (pairing n) p.1 p.2 ≤ convexCl (convHullFn f)}
      = {p : Rn n × ℝ | affineFn (pairing n) p.1 p.2 ≤ f} := by
    ext p
    simp only [Set.mem_ofPred_eq, ← convexConj_le_coe_iff, convexConj_convexCl,
        convexConj_convHullFn]
  rw [eq_biSup_affineFn (B := pairing n) (convexFn_convexCl (convexFn_convHullFn f))
    (closedConvex_convexCl _), hset]

/-- **Corollary 12.1.2** of [rockafellar1970convex]. Let $f$ be a proper convex function on
$\mathbb{R}^n$. Then there exist $b \in \mathbb{R}^n$ and $\beta \in \mathbb{R}$ such that
$f(x) \ge \langle x, b \rangle - \beta$ for every $x$.

The book states this corollary without a proof of its own. -/
theorem corollary_12_1_2 (hf : ConvexFn f) (hp : ProperConvex f) :
    ∃ (b : Rn n) (β : ℝ), ∀ x, ((inner ℝ x b : ℝ) : EReal) - (β : EReal) ≤ f x := by
  have hcl : ClosedProperConvexFn (convexCl f) :=
    ⟨convexFn_convexCl hf, closedConvex_convexCl f, hf.properConvex_convexCl hp⟩
  obtain ⟨⟨b, hb⟩, -⟩ := properConvex_convexConj (B := pairing n) hcl
  rw [mem_convexDom, convexConj_convexCl] at hb
  obtain ⟨β, hβ, -⟩ := EReal.lt_iff_exists_real_btwn.1 hb
  exact ⟨b, β, convexConj_le_coe_iff.1 hβ.le⟩

/-! ### Theorem 12.2: Fenchel–Moreau -/

/-- **Theorem 12.2** of [rockafellar1970convex], convexity of the conjugate. For every function
$f : \mathbb{R}^n \to [-\infty, +\infty]$, the conjugate $f^*$ is convex.

**Generalization.** The book states the theorem for convex $f$. Convexity of $f$ is not needed,
because $f^*$ is a pointwise supremum of affine functions for every $f$. -/
theorem theorem_12_2_convex (f : Rn n → EReal) : ConvexFn (convexConj (pairing n) f) :=
  convexFn_convexConj _ f

/-- **Theorem 12.2** of [rockafellar1970convex], closedness of the conjugate. For every function
$f : \mathbb{R}^n \to [-\infty, +\infty]$, the conjugate $f^*$ is closed.

**Generalization.** The book states the theorem for convex $f$. Convexity of $f$ is not needed. -/
theorem theorem_12_2_closed (f : Rn n → EReal) : ClosedConvex (convexConj (pairing n) f) :=
  closedConvex_convexConj

/-- **Theorem 12.2** of [rockafellar1970convex], properness of the conjugate. Let $f$ be a convex
function on $\mathbb{R}^n$. Then $f^*$ is proper if and only if $f$ is proper.

The backbone result `ConvexAnalysis.properConvex_convexConj_iff` also asks for $f$ to be closed.
On $\mathbb{R}^n$ the closure of a proper convex function is again proper (Theorem 7.4), so that
hypothesis can be removed, and `ConvexAnalysis.convexConj_convexCl` carries the conclusion back
from $\operatorname{cl} f$ to $f$. -/
theorem theorem_12_2_proper
    (hf : ConvexFn f) : ProperConvex (convexConj (pairing n) f) ↔ ProperConvex f := by
  refine ⟨properConvex_of_properConvex_convexConj, fun hp => ?_⟩
  have h := properConvex_convexConj (B := pairing n)
    ⟨convexFn_convexCl hf, closedConvex_convexCl f, hf.properConvex_convexCl hp⟩
  rwa [convexConj_convexCl] at h

/-- **Theorem 12.2** of [rockafellar1970convex], conjugate of the closure. For every function
$f : \mathbb{R}^n \to [-\infty, +\infty]$, $(\operatorname{cl} f)^* = f^*$.

**Generalization.** The book states the theorem for convex $f$. Convexity of $f$ is not needed. -/
theorem theorem_12_2_conj_clFn (f : Rn n → EReal) :
    convexConj (pairing n) (convexCl f) = convexConj (pairing n) f :=
  convexConj_convexCl f

/-- **Theorem 12.2** of [rockafellar1970convex] (Fenchel–Moreau theorem). Let $f$ be a convex
function on $\mathbb{R}^n$. Then $f^{**} = \operatorname{cl} f$.

On $\mathbb{R}^n$ both sides of the pairing are the same space, so $f^{**}$ is
`ConvexAnalysis.convexConj (Rockafellar.pairing n)` applied twice. `Rockafellar.flip_pairing`
removes the flipped pairing that the backbone biconjugate uses. -/
theorem theorem_12_2_biconj (hf : ConvexFn f) :
    convexConj (pairing n) (convexConj (pairing n) f) = convexCl f := by
  have h := convexBiconj_eq_convexCl (B := pairing n) hf
  rwa [convexBiconj, flip_pairing] at h

/-- **Corollary 12.2.1** of [rockafellar1970convex]. The conjugacy operation $f \mapsto f^*$ induces
a symmetric one-to-one correspondence in the class of all closed proper convex functions on
$\mathbb{R}^n$.

The correspondence is a bijection (`Equiv`) of the subtype of closed proper convex functions
onto itself. It sends $f$ to $f^*$ (`Rockafellar.corollary_12_2_1_apply`). "Symmetric" means
that the inverse also sends $g$ to $g^*$ (`Rockafellar.corollary_12_2_1_symm_apply`). The
definition is `ConvexAnalysis.convexConjEquiv` for `Rockafellar.pairing n`. -/
noncomputable def corollary_12_2_1 (n : ℕ) :
    {f : Rn n → EReal // ClosedProperConvexFn f} ≃ {g : Rn n → EReal // ClosedProperConvexFn g} :=
  convexConjEquiv (pairing n)

/-- The correspondence of Corollary 12.2.1 sends a closed proper convex function $f$ to its
conjugate $f^*$. -/
@[simp] theorem corollary_12_2_1_apply (f : {f : Rn n → EReal // ClosedProperConvexFn f}) :
    ((corollary_12_2_1 n f : {g : Rn n → EReal // ClosedProperConvexFn g}) : Rn n → EReal)
      = convexConj (pairing n) f := rfl

/-- The correspondence of Corollary 12.2.1 is **symmetric**: its inverse sends a closed proper
convex function $g$ to $g^*$, so the inverse is the correspondence itself. -/
@[simp] theorem corollary_12_2_1_symm_apply
    (g : {g : Rn n → EReal // ClosedProperConvexFn g}) :
    (((corollary_12_2_1 n).symm g : {f : Rn n → EReal // ClosedProperConvexFn f}) : Rn n → EReal)
      = convexConj (pairing n) g := by
  simp [corollary_12_2_1, convexConjEquiv]

/-- **Corollary 12.2.2** of [rockafellar1970convex]. Let $f$ be a convex function on $\mathbb{R}^n$.
Then for every $x^* \in \mathbb{R}^n$,
$$f^*(x^*) = \sup \{\langle x, x^* \rangle - f(x) \mid x \in
  \operatorname{ri}(\operatorname{dom} f)\}.$$

The effective domain $\operatorname{dom} f = \{x \mid f(x) < +\infty\}$ is
`ConvexAnalysis.convexDom f`. The supremum of the empty set is $-\infty$. -/
theorem corollary_12_2_2 (hf : ConvexFn f) (y : Rn n) :
    convexConj (pairing n) f y = ⨆ x ∈ ri (convexDom f), ((inner ℝ x y : ℝ) : EReal) - f x := by
  have hdomconv : Convex ℝ (convexDom f) := hf.convex_convexDom
  have hsub : ri (convexDom f) ⊆ convexDom f := intrinsicInterior_subset
  have hg : ConvexFn (convexRestrict (ri (convexDom f)) f) := hf.convexRestrict hdomconv.relint
  have hdomg : convexDom (convexRestrict (ri (convexDom f)) f) = ri (convexDom f) := by
    ext x
    by_cases hx : x ∈ ri (convexDom f)
    · simp only [mem_convexDom, convexRestrict_of_mem hx]
      exact ⟨fun _ => hx, fun _ => hsub hx⟩
    · simp [hx]
  have hri : ri (convexDom (convexRestrict (ri (convexDom f)) f)) = ri (convexDom f) := by
    rw [hdomg, hdomconv.relint_relint]
  have hcl : convexCl (convexRestrict (ri (convexDom f)) f) = convexCl f :=
    corollary_7_3_4 hg hf hri fun x hx => convexRestrict_of_mem (hri ▸ hx)
  have hconj : convexConj (pairing n) (convexRestrict (ri (convexDom f)) f)
      = convexConj (pairing n) f := by
    rw [← convexConj_convexCl (B := pairing n) (convexRestrict (ri (convexDom f)) f), hcl,
        convexConj_convexCl]
  rw [← hconj, convexConj_apply]
  refine le_antisymm (iSup_le fun x => ?_) (iSup₂_le fun x hx => ?_)
  · by_cases hx : x ∈ ri (convexDom f)
    · rw [convexRestrict_of_mem hx]
      exact le_iSup₂ (f := fun x (_ : x ∈ ri (convexDom f)) =>
        ((inner ℝ x y : ℝ) : EReal) - f x) x hx
    · rw [convexRestrict_of_notMem hx]
      simp
  · rw [← convexRestrict_of_mem (f := f) hx]
    exact le_iSup (fun x : Rn n => ((pairing n x y : ℝ) : EReal)
      - convexRestrict (ri (convexDom f)) f x) x

/-! ### Fenchel's inequality -/

/-- **Section 12** of [rockafellar1970convex], Fenchel's inequality (p. 105). Let $f$ be a proper
function on $\mathbb{R}^n$. Then for all $x, x^* \in \mathbb{R}^n$,
$$\langle x, x^* \rangle \le f(x) + f^*(x^*).$$

**Generalization.** The book states the inequality for a proper convex function $f$. Convexity
is not needed.

Properness cannot be removed: for $f \equiv +\infty$ the conjugate is $f^* \equiv -\infty$, and
the right-hand side is $(+\infty) + (-\infty) = -\infty$ in the arithmetic of `EReal`. -/
theorem fenchel_inequality (hp : ProperConvex f) (x y : Rn n) :
    ((inner ℝ x y : ℝ) : EReal) ≤ f x + convexConj (pairing n) f y :=
  hp.le_add_convexConj (B := pairing n) x y

/-! ### Theorem 12.3 -/

/-- **Theorem 12.3** of [rockafellar1970convex]. Let $h : \mathbb{R}^n \to [-\infty, +\infty]$, let
$A$ be a one-to-one linear transformation of $\mathbb{R}^n$ onto $\mathbb{R}^n$ with adjoint
$A^*$, let $a, a^* \in \mathbb{R}^n$ and $\alpha \in \mathbb{R}$, and let
$$f(x) = h(A(x - a)) + \langle x, a^* \rangle + \alpha.$$
Then for every $x^* \in \mathbb{R}^n$,
$$f^*(x^*) = h^*(A^{*-1}(x^* - a^*)) + \langle x^*, a \rangle + \alpha^*, \qquad \alpha^* =
  -\alpha - \langle a, a^* \rangle.$$

**Generalization.** The book states the theorem for a convex function $h$. Convexity of $h$ is
not needed.

The adjoint is taken as data: $A^*$ is the linear bijection `A'`, and the hypothesis `hA` is
$\langle Ax, z \rangle = \langle x, A^* z \rangle$ for all $x, z$. Over $\mathbb{R}^n$ the
adjoint exists and is unique, but it must still be supplied. The vector $a^*$ is `b`. -/
theorem theorem_12_3 (A A' : Rn n ≃ₗ[ℝ] Rn n)
    (hA : ∀ x z : Rn n, (inner ℝ (A x) z : ℝ) = inner ℝ x (A' z))
    (h : Rn n → EReal) (a b : Rn n) (α : ℝ) (y : Rn n) :
    convexConj (pairing n) (fun x => h (A (x - a)) + ((inner ℝ x b : ℝ) : EReal) + (α : EReal)) y
      = convexConj (pairing n) h (A'.symm (y - b)) + ((inner ℝ a y : ℝ) : EReal)
        + ((-α - inner ℝ a b : ℝ) : EReal) :=
  convexConj_comp_affine (B := pairing n) (B' := pairing n) A A' (fun x z => hA x z) h a b α y

/-! ### Corollary 12.3.1 -/

/-- **Section 12** of [rockafellar1970convex], definition of an orthogonal transformation (p. 109).
A linear bijection $A$ of $\mathbb{R}^n$ onto itself is an **orthogonal linear transformation**
if $\langle Ax, Ay \rangle = \langle x, y \rangle$ for all $x, y$.

`Rockafellar.orthogonalEquiv_adjoint` shows that the adjoint of an orthogonal $A$ is $A^{-1}$,
which is the identity $A^{*-1} = A$ of the book. -/
def IsOrthogonalEquiv (A : Rn n ≃ₗ[ℝ] Rn n) : Prop :=
  ∀ x y : Rn n, (inner ℝ (A x) (A y) : ℝ) = inner ℝ x y

/-- Let $A$ be an orthogonal linear transformation of $\mathbb{R}^n$. Then $\langle Ax, z \rangle =
\langle x, A^{-1} z \rangle$ for all $x, z$, that is, the adjoint of $A$ is $A^{-1}$. -/
theorem orthogonalEquiv_adjoint {A : Rn n ≃ₗ[ℝ] Rn n} (hA : IsOrthogonalEquiv A) (x z : Rn n) :
    (inner ℝ (A x) z : ℝ) = inner ℝ x (A.symm z) := by
  rw [← hA x (A.symm z), LinearEquiv.apply_symm_apply]

/-- **Section 12** of [rockafellar1970convex], definition of symmetry (p. 109). Let $G$ be a set of
linear bijections of $\mathbb{R}^n$. A function $f : \mathbb{R}^n \to [-\infty, +\infty]$ is
**symmetric with respect to $G$** if $f(Ax) = f(x)$ for every $x$ and every $A \in G$. -/
def SymmetricWrt (f : Rn n → EReal) (G : Set (Rn n ≃ₗ[ℝ] Rn n)) : Prop :=
  ∀ A ∈ G, ∀ x, f (A x) = f x

/-- Let $A$ be an orthogonal linear transformation of $\mathbb{R}^n$, and let $f$ satisfy
$f(Ax) = f(x)$ for every $x$. Then $f^*(Ax^*) = f^*(x^*)$ for every $x^*$. This is the half of
Corollary 12.3.1 that needs no closedness. It is Theorem 12.3 with $h = f$, $a = a^* = 0$ and
$\alpha = 0$, together with $A^{*-1} = A$. -/
theorem convexConj_comp_orthogonal {A : Rn n ≃ₗ[ℝ] Rn n} (hA : IsOrthogonalEquiv A)
    (hfA : ∀ x, f (A x) = f x) (y : Rn n) :
    convexConj (pairing n) f (A y) = convexConj (pairing n) f y := by
  have h := convexConj_comp_linearEquiv (B := pairing n) (B' := pairing n) A A.symm
    (orthogonalEquiv_adjoint hA) f y
  rw [LinearEquiv.symm_symm] at h
  rw [← h]
  exact congrArg (fun g => convexConj (pairing n) g y) (funext hfA)

/-- **Corollary 12.3.1** of [rockafellar1970convex]. Let $f$ be a closed convex function on
$\mathbb{R}^n$, and let $G$ be a set of orthogonal linear transformations of $\mathbb{R}^n$.
Then $f$ is symmetric with respect to $G$ if and only if $f^*$ is symmetric with respect to $G$. -/
theorem corollary_12_3_1 (hf : ConvexFn f) (hc : ClosedConvex f) {G : Set (Rn n ≃ₗ[ℝ] Rn n)}
    (hG : ∀ A ∈ G, IsOrthogonalEquiv A) :
    SymmetricWrt f G ↔ SymmetricWrt (convexConj (pairing n) f) G := by
  refine ⟨fun h A hA => convexConj_comp_orthogonal (hG A hA) (h A hA), fun h A hA => ?_⟩
  have hb : convexConj (pairing n) (convexConj (pairing n) f) = f := by
    rw [theorem_12_2_biconj hf, hc]
  have hsym := convexConj_comp_orthogonal (f := convexConj (pairing n) f) (hG A hA) (h A hA)
  rw [hb] at hsym
  exact hsym

/-! ### Theorem 12.4: monotone conjugacy on the non-negative orthant -/

section MonotoneConjugacy

/-- **Section 12** of [rockafellar1970convex], the non-negative orthant (p. 111). The **non-negative
orthant** of $\mathbb{R}^n$ is $K = \{z \mid z_j \ge 0 \text{ for all } j\}$. -/
def nonnegOrthant (n : ℕ) : Set (Rn n) := {z : Rn n | ∀ j, 0 ≤ z j}

/-- A vector $z$ lies in the non-negative orthant if and only if $z_j \ge 0$ for every $j$. -/
theorem mem_nonnegOrthant {z : Rn n} : z ∈ nonnegOrthant n ↔ ∀ j, 0 ≤ z j := Iff.rfl

/-- The inner product of $\mathbb{R}^n$ in coordinates: $\langle x, y \rangle = \sum_j x_j y_j$. -/
theorem inner_rn (x y : Rn n) : (inner ℝ x y : ℝ) = ∑ j, x j * y j := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The non-negative orthant is convex. -/
theorem convex_nonnegOrthant (n : ℕ) : Convex ℝ (nonnegOrthant n) := by
  intro x hx y hy a b ha hb _ j
  exact add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hb (hy j))

/-- The non-negative orthant is closed. -/
theorem isClosed_nonnegOrthant (n : ℕ) : IsClosed (nonnegOrthant n) := by
  have hset : nonnegOrthant n = ⋂ j, (fun z : Rn n => z j) ⁻¹' Set.Ici (0 : ℝ) := by
    ext z; simp [nonnegOrthant]
  rw [hset]
  exact isClosed_iInter fun j =>
    isClosed_Ici.preimage (PiLp.continuous_apply (p := 2) (fun _ : Fin n => ℝ) j)

/-- The origin lies in the non-negative orthant. -/
theorem zero_mem_nonnegOrthant (n : ℕ) : (0 : Rn n) ∈ nonnegOrthant n := fun _ => le_rfl

/-- The componentwise **positive part** of $y \in \mathbb{R}^n$: the vector $y^+$ with
$(y^+)_j = \max\{y_j, 0\}$. It equals $y$ when $y$ lies in the non-negative orthant. -/
noncomputable def posPart (y : Rn n) : Rn n := WithLp.toLp 2 fun j => max (y j) 0

/-- The coordinates of the positive part: $(y^+)_j = \max\{y_j, 0\}$. -/
@[simp] theorem posPart_apply (y : Rn n) (j : Fin n) : posPart y j = max (y j) 0 := rfl

/-- The positive part $y^+$ lies in the non-negative orthant. -/
theorem posPart_mem (y : Rn n) : posPart y ∈ nonnegOrthant n := fun _ => le_max_right _ _

/-- Each coordinate of $y$ is at most the corresponding coordinate of $y^+$: $y_j \le (y^+)_j$. -/
theorem le_posPart (y : Rn n) (j : Fin n) : y j ≤ posPart y j := le_max_left _ _

/-- If $y$ lies in the non-negative orthant, then $y^+ = y$. -/
theorem posPart_of_mem {y : Rn n} (hy : y ∈ nonnegOrthant n) : posPart y = y := by
  ext j; exact max_eq_left (hy j)

/-- The vector obtained from $z$ by setting to zero the coordinates $j$ with $y_j < 0$: its $j$-th
coordinate is $z_j$ if $y_j \ge 0$ and $0$ otherwise.

It is the competitor in the proof of `Rockafellar.convexConj_posPart`, the fact that makes the
truncation in `Rockafellar.monotoneConjOrthant` harmless. -/
noncomputable def maskNonneg (y z : Rn n) : Rn n :=
  WithLp.toLp 2 fun j => if 0 ≤ y j then z j else 0

/-- The coordinates of `Rockafellar.maskNonneg y z`: the $j$-th coordinate is $z_j$ if $y_j \ge 0$
and $0$ otherwise. -/
@[simp] theorem maskNonneg_apply (y z : Rn n) (j : Fin n) :
    maskNonneg y z j = if 0 ≤ y j then z j else 0 := rfl

/-- If $z$ lies in the non-negative orthant, then so does `Rockafellar.maskNonneg y z`. -/
theorem maskNonneg_mem {z : Rn n} (y : Rn n) (hz : z ∈ nonnegOrthant n) :
    maskNonneg y z ∈ nonnegOrthant n := by
  intro j
  rw [maskNonneg_apply]
  split
  · exact hz j
  · exact le_rfl

/-- If $z$ lies in the non-negative orthant, then each coordinate of `Rockafellar.maskNonneg y z` is
at most the corresponding coordinate of $z$. -/
theorem maskNonneg_le {z : Rn n} (y : Rn n) (hz : z ∈ nonnegOrthant n) (j : Fin n) :
    maskNonneg y z j ≤ z j := by
  rw [maskNonneg_apply]
  split
  · exact le_rfl
  · exact hz j

/-- Write $\tilde z$ for `Rockafellar.maskNonneg y z`. Then $\langle \tilde z, y \rangle = \langle
z, y^+ \rangle$. -/
theorem inner_maskNonneg (y z : Rn n) :
    (inner ℝ (maskNonneg y z) y : ℝ) = inner ℝ z (posPart y) := by
  rw [inner_rn, inner_rn]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [maskNonneg_apply, posPart_apply]
  split_ifs with hj
  · rw [max_eq_left hj]
  · rw [max_eq_right (le_of_not_ge hj), zero_mul, mul_zero]

/-- If $z$ lies in the non-negative orthant, then $\langle y, z \rangle \le \langle y^+, z \rangle$
for every $y$. -/
theorem inner_le_inner_posPart {z : Rn n} (hz : z ∈ nonnegOrthant n) (y : Rn n) :
    (inner ℝ y z : ℝ) ≤ inner ℝ (posPart y) z := by
  rw [inner_rn, inner_rn]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (le_posPart y j) (hz j)

/-- **Section 12** of [rockafellar1970convex], the functions of Theorem 12.4 (p. 111). A function
$g : \mathbb{R}^n \to [-\infty, +\infty]$ is a **non-decreasing closed convex function on the
non-negative orthant** $K$, finite at the origin, if $g = +\infty$ off $K$, $g(z) \le g(z')$
whenever $0 \le z \le z'$ componentwise, $g$ is convex and closed, and $g(0)$ is finite.

The function on $K$ of the book is encoded, following the convention of Section 4, as a function
on all of $\mathbb{R}^n$ that is $+\infty$ off $K$. The book's hypotheses on $g$ are exactly the
fields of this structure. -/
structure MonotoneOrthantFn (f : Rn n → EReal) : Prop where
  /-- The function is $+\infty$ off the non-negative orthant. -/
  top_of_notMem : ∀ ⦃z : Rn n⦄, z ∉ nonnegOrthant n → f z = ⊤
  /-- The function $g$ is non-decreasing on the orthant: $g(z) \le g(z')$ whenever $0 \le z$ and
  $z \le z'$ componentwise. -/
  mono : ∀ ⦃z z' : Rn n⦄, z ∈ nonnegOrthant n → (∀ j, z j ≤ z' j) → f z ≤ f z'
  /-- The function is convex. -/
  convex : ConvexFn f
  /-- The function is closed, that is, lower semicontinuous. -/
  closed : ClosedConvex f
  /-- The value at the origin is not $+\infty$. -/
  zero_ne_top : f 0 ≠ ⊤
  /-- The value at the origin is not $-\infty$. -/
  zero_ne_bot : f 0 ≠ ⊥

/-- A non-decreasing closed convex function $g$ on the non-negative orthant attains its minimum over
the orthant at the origin: $g(0) \le g(z)$ for every $z$ in the orthant. -/
theorem MonotoneOrthantFn.zero_le {f : Rn n → EReal} (hf : MonotoneOrthantFn f)
    {z : Rn n} (hz : z ∈ nonnegOrthant n) : f 0 ≤ f z :=
  hf.mono (zero_mem_nonnegOrthant n) fun j => hz j

/-- A non-decreasing closed convex function on the non-negative orthant that is finite at the origin
is proper. -/
theorem MonotoneOrthantFn.proper {f : Rn n → EReal}
    (hf : MonotoneOrthantFn f) : ProperConvex f := by
  refine ⟨⟨0, lt_of_le_of_ne le_top hf.zero_ne_top⟩, fun z hz => ?_⟩
  by_cases hzm : z ∈ nonnegOrthant n
  · exact hf.zero_ne_bot (le_bot_iff.1 (hz ▸ hf.zero_le hzm))
  · exact absurd (hf.top_of_notMem hzm) (hz ▸ bot_ne_top)

/-- **Section 12** of [rockafellar1970convex], the monotone conjugate (p. 111). The **monotone
conjugate** $g^+$ of $g : \mathbb{R}^n \to [-\infty, +\infty]$ is $g^*$ on the non-negative
orthant $K$ and $+\infty$ off $K$. The truncation makes the correspondence one between functions
on $K$. -/
noncomputable def monotoneConjOrthant (f : Rn n → EReal) : Rn n → EReal :=
  convexRestrict (nonnegOrthant n) (convexConj (pairing n) f)

/-- **Section 12** of [rockafellar1970convex], formula for the monotone conjugate (p. 111). Let
$g : \mathbb{R}^n \to [-\infty, +\infty]$ be $+\infty$ off the non-negative orthant $K$. Then
for every $z^* \in K$,
$$g^+(z^*) = \sup \{\langle z, z^* \rangle - g(z) \mid z \in K\}.$$
-/
theorem monotoneConjOrthant_apply {f : Rn n → EReal}
    (htop : ∀ ⦃z : Rn n⦄, z ∉ nonnegOrthant n → f z = ⊤) {y : Rn n} (hy : y ∈ nonnegOrthant n) :
    monotoneConjOrthant f y = ⨆ z ∈ nonnegOrthant n, ((inner ℝ z y : ℝ) : EReal) - f z := by
  rw [monotoneConjOrthant, convexRestrict_of_mem hy, convexConj_apply]
  refine le_antisymm (iSup_le fun z => ?_) (iSup₂_le fun z hz => ?_)
  · by_cases hz : z ∈ nonnegOrthant n
    · exact le_iSup₂ (f := fun z (_ : z ∈ nonnegOrthant n) =>
        ((inner ℝ z y : ℝ) : EReal) - f z) z hz
    · rw [htop hz]; simp
  · exact le_iSup (fun z : Rn n => ((pairing n z y : ℝ) : EReal) - f z) z

/-- The monotone conjugate is $+\infty$ off the non-negative orthant: $g^+(y) = +\infty$ if
$y \notin K$. -/
theorem monotoneConjOrthant_of_notMem (f : Rn n → EReal) {y : Rn n}
    (hy : y ∉ nonnegOrthant n) : monotoneConjOrthant f y = ⊤ :=
  convexRestrict_of_notMem hy

/-- The monotone conjugate majorizes the conjugate: $g^*(y) \le g^+(y)$ for every $y$. -/
theorem convexConj_le_monotoneConjOrthant (f : Rn n → EReal) (y : Rn n) :
    convexConj (pairing n) f y ≤ monotoneConjOrthant f y := by
  by_cases hy : y ∈ nonnegOrthant n
  · rw [monotoneConjOrthant, convexRestrict_of_mem hy]
  · rw [monotoneConjOrthant_of_notMem f hy]; exact le_top

/-- Let $g$ be $+\infty$ off the non-negative orthant. Then $g^*$ is non-decreasing: if
$y_j \le y'_j$ for every $j$, then $g^*(y) \le g^*(y')$. -/
theorem convexConj_mono_of_top_of_notMem {f : Rn n → EReal}
    (htop : ∀ ⦃z : Rn n⦄, z ∉ nonnegOrthant n → f z = ⊤) {y y' : Rn n} (h : ∀ j, y j ≤ y' j) :
    convexConj (pairing n) f y ≤ convexConj (pairing n) f y' := by
  rw [convexConj_apply, convexConj_apply]
  refine iSup_le fun z => ?_
  by_cases hz : z ∈ nonnegOrthant n
  · refine le_trans ?_ (le_iSup (fun z : Rn n => ((pairing n z y' : ℝ) : EReal) - f z) z)
    refine EReal.sub_le_sub ?_ le_rfl
    rw [EReal.coe_le_coe_iff]
    change (inner ℝ z y : ℝ) ≤ inner ℝ z y'
    rw [inner_rn, inner_rn]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hz j)
  · rw [htop hz]; simp

/-- Let $g$ be a non-decreasing closed convex function on the non-negative orthant that is finite at
the origin. Then $g^*(y^+) = g^*(y)$ for every $y \in \mathbb{R}^n$, where $y^+$ is the
componentwise positive part of $y$.

This is the fact that makes the truncation in the monotone conjugate harmless; see the proof
outline in the module doc comment. -/
theorem convexConj_posPart {f : Rn n → EReal} (hf : MonotoneOrthantFn f) (y : Rn n) :
    convexConj (pairing n) f (posPart y) = convexConj (pairing n) f y := by
  refine le_antisymm ?_ (convexConj_mono_of_top_of_notMem hf.top_of_notMem (le_posPart y))
  rw [convexConj_apply, convexConj_apply]
  refine iSup_le fun z => ?_
  by_cases hz : z ∈ nonnegOrthant n
  · refine le_trans ?_
      (le_iSup (fun w : Rn n => ((pairing n w y : ℝ) : EReal) - f w) (maskNonneg y z))
    refine EReal.sub_le_sub (le_of_eq ?_)
      (hf.mono (maskNonneg_mem y hz) (maskNonneg_le y hz))
    rw [EReal.coe_eq_coe_iff]
    exact (inner_maskNonneg y z).symm
  · rw [hf.top_of_notMem hz]; simp

/-- **Theorem 12.4** of [rockafellar1970convex], first half. Let $g$ be a non-decreasing lower
semicontinuous convex function on the non-negative orthant $K$ such that $g(0)$ is finite. Then
the monotone conjugate $g^+$ is again a non-decreasing lower semicontinuous convex function on
$K$ that is finite at the origin.

The book states Theorem 12.4 without a proof. Since $g$ attains its minimum over $K$ at the
origin, $g^+(0) = -g(0)$. The class of functions is `Rockafellar.MonotoneOrthantFn`. -/
theorem theorem_12_4_mem {f : Rn n → EReal} (hf : MonotoneOrthantFn f) :
    MonotoneOrthantFn (monotoneConjOrthant f) := by
  have hzero : monotoneConjOrthant f 0 = -f 0 := by
    rw [monotoneConjOrthant, convexRestrict_of_mem (zero_mem_nonnegOrthant n), convexConj_apply]
    refine le_antisymm (iSup_le fun z => ?_) ?_
    · by_cases hz : z ∈ nonnegOrthant n
      · have h0 : ((pairing n z 0 : ℝ) : EReal) = 0 := by
          rw [map_zero, EReal.coe_zero]
        rw [h0, zero_sub, EReal.neg_le_neg_iff]
        exact hf.zero_le hz
      · rw [hf.top_of_notMem hz]; simp
    · refine le_trans (le_of_eq ?_)
        (le_iSup (fun z : Rn n => ((pairing n z 0 : ℝ) : EReal) - f z) 0)
      rw [map_zero, EReal.coe_zero, zero_sub]
  refine ⟨fun y hy => monotoneConjOrthant_of_notMem f hy, ?_,
    (convexFn_convexConj (pairing n) f).convexRestrict (convex_nonnegOrthant n),
    (closedConvex_convexConj (B := pairing n) (f := f)).convexRestrict
        ?_ (isClosed_nonnegOrthant n),
    ?_, ?_⟩
  · intro y y' hy hyy'
    have hy' : y' ∈ nonnegOrthant n := fun j => le_trans (hy j) (hyy' j)
    rw [monotoneConjOrthant, convexRestrict_of_mem hy, convexRestrict_of_mem hy']
    exact convexConj_mono_of_top_of_notMem hf.top_of_notMem hyy'
  · exact fun y => convexConj_ne_bot hf.proper.convexDom_nonempty y
  · rw [hzero]
    exact fun h => hf.zero_ne_bot (EReal.neg_eq_top_iff.1 h)
  · rw [hzero]
    exact fun h => hf.zero_ne_top (EReal.neg_eq_bot_iff.1 h)

/-- **Theorem 12.4** of [rockafellar1970convex], second half. Let $g$ be a non-decreasing lower
semicontinuous convex function on the non-negative orthant such that $g(0)$ is finite. Then
$(g^+)^+ = g$.

The book states Theorem 12.4 without a proof. The proof here is described in the module doc
comment. -/
theorem theorem_12_4_involutive {f : Rn n → EReal} (hf : MonotoneOrthantFn f) :
    monotoneConjOrthant (monotoneConjOrthant f) = f := by
  have hbi : convexConj (pairing n) (convexConj (pairing n) f) = f := by
    rw [theorem_12_2_biconj hf.convex, hf.closed]
  funext z
  by_cases hz : z ∈ nonnegOrthant n
  · have hLHS : convexConj (pairing n) (convexConj (pairing n) f) z
        = ⨆ y : Rn n, ((pairing n y z : ℝ) : EReal) - convexConj (pairing n) f y :=
            convexConj_apply _ _ _
    have hRHS : convexConj (pairing n) (monotoneConjOrthant f) z
        = ⨆ w : Rn n, ((pairing n w z : ℝ) : EReal) - monotoneConjOrthant f w :=
            convexConj_apply _ _ _
    have hge : convexConj (pairing n) (convexConj (pairing n) f) z
        ≤ convexConj (pairing n) (monotoneConjOrthant f) z := by
      rw [hLHS, hRHS]
      refine iSup_le fun y => ?_
      refine le_trans ?_
        (le_iSup (fun w : Rn n => ((pairing n w z : ℝ) : EReal) - monotoneConjOrthant f w)
          (posPart y))
      refine EReal.sub_le_sub ?_ (le_of_eq ?_)
      · rw [EReal.coe_le_coe_iff]
        exact inner_le_inner_posPart hz y
      · rw [monotoneConjOrthant, convexRestrict_of_mem (posPart_mem y), convexConj_posPart hf]
    have hle := convexConj_antitone (pairing n) (convexConj_le_monotoneConjOrthant f) z
    rw [hbi] at hge hle
    rw [monotoneConjOrthant, convexRestrict_of_mem hz]
    exact le_antisymm hle hge
  · rw [monotoneConjOrthant_of_notMem _ hz, (hf.top_of_notMem hz).symm]

end MonotoneConjugacy

end Rockafellar
