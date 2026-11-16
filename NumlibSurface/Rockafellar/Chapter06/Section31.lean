/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Extremum.ConeDuality
import Numlib.Analysis.Convex.Extremum.MoreauGradient
import Numlib.Analysis.Convex.Extremum.Normal
import Numlib.Analysis.Convex.Polyhedral.Duality
import NumlibSurface.Rockafellar.Chapter03.Section12
import NumlibSurface.Rockafellar.Chapter03.Section14
import NumlibSurface.Rockafellar.Chapter03.Section16
import NumlibSurface.Rockafellar.Chapter04.Section19

/-!
# Rockafellar, Section 31: Fenchel's duality theorem

This module formalizes Section 31 of [rockafellar1970convex]. For a proper convex function $f$ and a
proper concave function $g$ on $\mathbb{R}^n$, **Fenchel's duality theorem** states
$$\inf_x \{f(x) - g(x)\} = \sup_{x^*} \{g^*(x^*) - f^*(x^*)\}$$
under a condition on relative interiors, where $f^*$ is the convex conjugate and $g^*$ the concave
conjugate. The section extends the theorem to $\inf_x \{f(x) - g(Ax)\} = \sup_{u^*} \{g^*(u^*) -
f^*(A^* u^*)\}$ for a linear transformation $A$, shows that this pair of problems is a convex
program and its dual in the sense of Sections 29 and 30, gives the Kuhn–Tucker conditions
$A^* u^* \in \partial f(x)$ and $Ax \in \partial g^*(u^*)$ for optimality, and specializes the
theorem to the minimum of a convex function over a convex cone: $\inf_K f = -\inf_{K^*} f^*$. The
section ends with Moreau's theorem $(f \mathbin{\square} w) + (f^* \mathbin{\square} w) = w$ for
$w(z) = \tfrac12 |z|^2$ and the proximation $\operatorname{prox}(z \mid f)$ that it defines.
Moreau's results go back to J.-J. Moreau, *Proximité et dualité dans un espace hilbertien*, Bull.
Soc. Math. France **93** (1965), 273–299.

All 12 numbered results of Section 31 are formalized, together with the polyhedral forms of Theorem
31.1, Corollary 31.2.1 and Theorem 31.4, and the unnumbered contraction property of the proximation.
Two assertions that the book does not prove are proved here: the polyhedral form of Corollary
31.2.1, for which the book says "the proof will not be given here", and Corollary 31.5.1, which the
book states without proof. The proofs specialize `Numlib.Analysis.Convex.Extremum.Fenchel`,
`Numlib.Analysis.Convex.Extremum.ConeDuality`, `Numlib.Analysis.Convex.Extremum.MoreauGradient`,
`Numlib.Analysis.Convex.Extremum.Normal` and `Numlib.Analysis.Convex.Polyhedral.Duality`.

## Main definitions

* Theorem 31.2, `Rockafellar.fenchelBifun`: the bifunction $(Fu)(x) = f(x) - g(Ax + u)$, the Fenchel
  problem perturbed by a translation of the concave function.
* Corollary 31.5.1, `Rockafellar.corollary_31_5_1`: the homeomorphism $(x, x^*) \mapsto x + x^*$
  from the graph of $\partial f$ onto $\mathbb{R}^n$.

## Main results

* Theorem 31.1, `Rockafellar.theorem_31_1_weak`, `Rockafellar.theorem_31_1_a`,
  `Rockafellar.theorem_31_1_b`, `Rockafellar.theorem_31_1_finite`, with the attainment and
  polyhedral forms: Fenchel's duality theorem $\inf (f - g) = \sup (g^* - f^*)$, with attainment of
  the supremum under (a) and of the infimum under (b).
* Theorem 31.2, `Rockafellar.theorem_31_2_convex`, `Rockafellar.theorem_31_2_proper`,
  `Rockafellar.theorem_31_2_closed`, `Rockafellar.theorem_31_2_infBifun`,
  `Rockafellar.theorem_31_2_domBifun`, `Rockafellar.theorem_31_2_relint_domBifun`,
  `Rockafellar.theorem_31_2_stronglyConsistent_iff`, `Rockafellar.theorem_31_2_adjoint`,
  `Rockafellar.theorem_31_2_supBifun_adjoint`, `Rockafellar.theorem_31_2_domConcaveBifun_adjoint`,
  `Rockafellar.theorem_31_2_concaveStronglyConsistent_iff`: the Fenchel bifunction is a proper
  convex bifunction, closed when $f$ and $g$ are, and its adjoint is
  $(F^* x^*)(u^*) = g^*(u^*) - f^*(A^* u^* + x^*)$.
* Corollary 31.2.1, `Rockafellar.corollary_31_2_1_a`, `Rockafellar.corollary_31_2_1_b`, with the
  attainment and polyhedral forms: $\inf_x \{f(x) - g(Ax)\} = \sup_{u^*} \{g^*(u^*) - f^*(A^*
  u^*)\}$ under condition (a) or (b).
* Theorem 31.3, `Rockafellar.theorem_31_3`: the primal and the dual value agree at $(x, u^*)$ if and
  only if $x$ and $u^*$ satisfy the Kuhn–Tucker conditions $A^* u^* \in \partial f(x)$ and
  $-u^* \in \partial(-g)(Ax)$.
* Corollary 31.3.1, `Rockafellar.corollary_31_3_1`: under condition (a) of Corollary 31.2.1, $x$
  minimizes $f - gA$ if and only if some $u^*$ satisfies the Kuhn–Tucker conditions with $x$.
* Theorem 31.4, `Rockafellar.theorem_31_4_dualCone`, `Rockafellar.theorem_31_4_a`,
  `Rockafellar.theorem_31_4_b`, `Rockafellar.theorem_31_4_optimality`,
  `Rockafellar.theorem_31_4_weak`, with the attainment and polyhedral forms: $\inf \{f(x) \mid x \in
  K\} = -\inf \{f^*(x^*) \mid x^* \in K^*\}$ for a convex cone $K$ and its dual cone $K^*$.
* Corollary 31.4.1, `Rockafellar.corollary_31_4_1_a`, `Rockafellar.corollary_31_4_1_b`,
  `Rockafellar.corollary_31_4_1_optimality`: the same over the non-negative orthant, with
  complementary slackness.
* Corollary 31.4.2, `Rockafellar.corollary_31_4_2_a`, `Rockafellar.corollary_31_4_2_b_attained`,
  `Rockafellar.corollary_31_4_2_optimality`: the same over a subspace $L$ and its orthogonal
  complement $L^\perp$.
* Corollary 31.4.3, `Rockafellar.corollary_31_4_3`: for a co-finite $h$ that is finite everywhere,
  $\inf_{x \in K} \{h(z + x) - \langle z^*, x \rangle\} + \inf_{x^* \in K^*} \{h^*(z^* + x^*) -
  \langle z, x^* \rangle\} = \langle z, z^* \rangle$.
* Theorem 31.5, `Rockafellar.theorem_31_5`, with `Rockafellar.theorem_31_5_existsUnique` and the
  gradient formulas: Moreau's theorem $(f \mathbin{\square} w) + (f^* \mathbin{\square} w) = w$,
  with both infima finite and uniquely attained.
* Unnumbered result, `Rockafellar.prox_contraction`: $|\operatorname{prox}(z_1 \mid f) -
  \operatorname{prox}(z_0 \mid f)| \le |z_1 - z_0|$.
* Corollary 31.5.2, `Rockafellar.corollary_31_5_2`: $\partial f$ is a maximal monotone mapping.

## Implementation notes

* The dual cone $K^* = \{x^* \mid \langle x, x^* \rangle \ge 0 \text{ for all } x \in K\}$ of the
  book is `-(ConvexAnalysis.polarCone (Rockafellar.pairing n) K)`, the negative of the polar cone.
  `Rockafellar.theorem_31_4_dualCone` gives the unfolded form.
* The adjoint $A^*$ of a linear map $A$ is `LinearMap.adjoint A`. No adjointness hypothesis is an
  argument of any declaration, because on $\mathbb{R}^n$ the transpose is canonical, and
  `ConvexAnalysis.isAdjointPair_adjoint` supplies the datum that the backbone asks for.
* The conditions (a) and (b) of Theorem 31.1 enter the backbone through `ConvexAnalysis.IsExactSum`:
  each condition, and each of its polyhedral forms, makes the infimal convolution of the conjugates
  exact.
* In Theorem 31.5, the function $w$ is `ConvexAnalysis.quadFn`, the infimal convolution is
  `ConvexAnalysis.infConv`, and the proximation is `ConvexAnalysis.prox`. The function
  $x \mapsto f(x) + w(z - x)$, whose infimum is $(f \mathbin{\square} w)(z)$, is
  `ConvexAnalysis.moreauObj`.
* Differences of extended real numbers follow the convention $\infty - \infty = -\infty$ of `EReal`.

## Deviations from the source

* **Theorem 31.1**, finiteness (generalization). The book assumes (a) and (b). The statement assumes
  only a point of $\operatorname{dom} f \cap \operatorname{dom} g$ and a point of
  $\operatorname{dom} g^* \cap \operatorname{dom} f^*$. See `Rockafellar.theorem_31_1_finite`.
* **Theorem 31.2**, properness (generalization). The statement needs no relative-interior
  hypothesis. See `Rockafellar.theorem_31_2_proper`.
* **Corollary 31.2.1** under (a) (generalization). The book assumes $f$ closed. The statement does
  not. See `Rockafellar.corollary_31_2_1_a`.
* **Theorem 31.3** (generalization). The book assumes $f$ and $g$ closed. The statement does not,
  and it writes the second Kuhn–Tucker condition as $-u^* \in \partial(-g)(Ax)$, which is the
  condition $Ax \in \partial g^*(u^*)$ of the book when $g$ is closed. See
  `Rockafellar.theorem_31_3`.
* **Corollary 31.3.1** (generalization). The book assumes $f$ closed. The statement does not. See
  `Rockafellar.corollary_31_3_1`.
* **Theorem 31.4** under (a) (generalization). The book assumes $f$ and $K$ closed. The statement
  does not. See `Rockafellar.theorem_31_4_a`.
* **Corollary 31.4.1** under (a) (generalization). The book assumes $f$ closed. The statement does
  not. See `Rockafellar.corollary_31_4_1_a`.
* **Corollary 31.4.2** under (a) (generalization). The book assumes $f$ closed. The statement does
  not. See `Rockafellar.corollary_31_4_2_a`.
* **Corollary 31.4.3** (generalization). The book assumes $K$ closed. Only the attainment of the
  first infimum needs it. See `Rockafellar.corollary_31_4_3` and
  `Rockafellar.corollary_31_4_3_attained`.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {m n : ℕ}

/-!
### Theorem 31.1: Fenchel's duality theorem

The two conditions (a) and (b) of [rockafellar1970convex] are two sufficient conditions for one
property of the backbone, `ConvexAnalysis.IsExactSum`. The polyhedral forms that the last paragraph
of the theorem announces are two more. The four private lemmas below prove exactly these four, and
each numbered statement follows from one of them in one line.
-/

/-- Condition (a) of Theorem 31.1, $\operatorname{ri}(\operatorname{dom} f) \cap
\operatorname{ri}(\operatorname{dom} g) \neq \emptyset$, makes the sum of $f$ and $-g$ exact
(Theorem 16.4). -/
private theorem isExactSum_neg_of_relint {f g : Rn n → EReal} (hf : ConvexFn f)
    (hpf : ProperConvex f)
    (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ ri (convexDom f))
    (hxg : x₀ ∈ ri (concaveDom g)) : IsExactSum (pairing n) f fun x => -(g x) :=
  IsExactSum.of_relint hf hpf (concaveFn_iff_convexFn_neg.1 hg)
    (properConcave_iff_properConvex_neg.1 hpg) hxf (by rwa [← concaveDom_eq_convexDom_neg])

/-- Condition (b) of Theorem 31.1, $\operatorname{ri}(\operatorname{dom} g^*) \cap
\operatorname{ri}(\operatorname{dom} f^*) \neq \emptyset$, makes the sum of $f^*$ and $-g^*$
exact. -/
private theorem isExactSum_convexConj_of_relint {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConcaveFn g) {y₀ : Rn n}
    (hyf : y₀ ∈ ri (convexDom (convexConj (pairing n) f)))
    (hyg : y₀ ∈ ri (concaveDom (concaveConj (pairing n) g))) :
    IsExactSum (pairing n).flip (convexConj (pairing n) f)
      fun y => -(concaveConj (pairing n) g y) := by
  refine IsExactSum.of_relint (convexFn_convexConj (pairing n) f)
      (properConvex_convexConj (B := pairing n) hf)
    (concaveFn_iff_convexFn_neg.1 (concaveFn_concaveConj (pairing n) g))
    (properConcave_iff_properConvex_neg.1 ⟨⟨y₀, intrinsicInterior_subset hyg⟩,
      fun y => concaveConj_ne_top hg.proper.concaveDom_nonempty y⟩)
    hyf ?_
  rwa [← concaveDom_eq_convexDom_neg]

/-- **Theorem 31.1** of [rockafellar1970convex], the inequality at the start of the proof. For all
functions $f, g : \mathbb{R}^n \to [-\infty, +\infty]$ and all $x, x^* \in \mathbb{R}^n$,
$$g^*(x^*) - f^*(x^*) \le f(x) - g(x).$$

This is Fenchel's inequality, used twice. No hypothesis is needed: with the convention
$\infty - \infty = -\infty$, both cases of $\infty - \infty$ fall on the correct side of the
inequality. -/
theorem theorem_31_1_weak (f g : Rn n → EReal) (x y : Rn n) :
    concaveConj (pairing n) g y - convexConj (pairing n) f y ≤ f x - g x :=
  concaveConj_sub_convexConj_le_sub (pairing n) f g x y

/-- **Theorem 31.1** of [rockafellar1970convex] (Fenchel's duality theorem), condition (a). Let $f$
be a proper convex function and $g$ a proper concave function on $\mathbb{R}^n$. If
$\operatorname{ri}(\operatorname{dom} f) \cap \operatorname{ri}(\operatorname{dom} g) \neq
\emptyset$, then
$$\inf_x \{f(x) - g(x)\} = \sup_{x^*} \{g^*(x^*) - f^*(x^*)\}.$$

Here $f^*$ is the convex conjugate `ConvexAnalysis.convexConj` and $g^*$ is the concave
conjugate `ConvexAnalysis.concaveConj`. Condition (a) enters only through Theorem 16.4. -/
theorem theorem_31_1_a {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : ProperConvex f)
    (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ ri (convexDom f))
    (hxg : x₀ ∈ ri (concaveDom g)) :
    (⨅ x, f x - g x) = ⨆ y : Rn n, concaveConj (pairing n) g y - convexConj (pairing n) f y :=
  fenchel_duality (isExactSum_neg_of_relint hf hpf hg hpg hxf hxg)

/-- **Theorem 31.1** of [rockafellar1970convex], attainment under (a). Let $f$ be a proper convex
function and $g$ a proper concave function on $\mathbb{R}^n$ with
$\operatorname{ri}(\operatorname{dom} f) \cap \operatorname{ri}(\operatorname{dom} g) \neq
\emptyset$. Then some $x^*$ satisfies $g^*(x^*) - f^*(x^*) = \inf_x \{f(x) - g(x)\}$: the
supremum is attained.

This specializes `ConvexAnalysis.exists_concaveConj_sub_convexConj_eq`. -/
theorem theorem_31_1_a_attained {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : ProperConvex f)
    (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ ri (convexDom f))
    (hxg : x₀ ∈ ri (concaveDom g)) :
    ∃ y : Rn n, concaveConj (pairing n) g y - convexConj (pairing n) f y = ⨅ x, f x - g x :=
  exists_concaveConj_sub_convexConj_eq (isExactSum_neg_of_relint hf hpf hg hpg hxf hxg)

/-- **Theorem 31.1** of [rockafellar1970convex], attainment under (a), as a greatest element. Under
the hypotheses of `Rockafellar.theorem_31_1_a`, the value $\inf_x \{f(x) - g(x)\}$ is the
greatest element of the set of the values $g^*(x^*) - f^*(x^*)$.

This specializes `ConvexAnalysis.isGreatest_concaveConj_sub_convexConj`. -/
theorem theorem_31_1_a_isGreatest {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : ProperConvex f)
    (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ ri (convexDom f))
    (hxg : x₀ ∈ ri (concaveDom g)) :
    IsGreatest (Set.range fun y : Rn n =>
      concaveConj (pairing n) g y - convexConj (pairing n) f y) (⨅ x, f x - g x) :=
  isGreatest_concaveConj_sub_convexConj (isExactSum_neg_of_relint hf hpf hg hpg hxf hxg)

/-- **Theorem 31.1** of [rockafellar1970convex] (Fenchel's duality theorem), condition (b). Let $f$
be a closed proper convex function and $g$ a closed proper concave function on $\mathbb{R}^n$.
If $\operatorname{ri}(\operatorname{dom} g^*) \cap \operatorname{ri}(\operatorname{dom} f^*)
\neq \emptyset$, then
$$\inf_x \{f(x) - g(x)\} = \sup_{x^*} \{g^*(x^*) - f^*(x^*)\}.$$

The proof applies condition (a) to the dual pair $(f^*, g^*)$ and then the Fenchel–Moreau
theorem. The domain $\operatorname{dom} g^*$ is the set where $g^* > -\infty$. -/
theorem theorem_31_1_b {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConcaveFn g) {y₀ : Rn n}
        (hyf : y₀ ∈ ri (convexDom (convexConj (pairing n) f)))
    (hyg : y₀ ∈ ri (concaveDom (concaveConj (pairing n) g))) :
    (⨅ x, f x - g x) = ⨆ y : Rn n, concaveConj (pairing n) g y - convexConj (pairing n) f y :=
  fenchel_duality_of_closed hf hg (isExactSum_convexConj_of_relint hf hg hyf hyg)

/-- **Theorem 31.1** of [rockafellar1970convex], attainment under (b). Under the hypotheses of
`Rockafellar.theorem_31_1_b`, some $x$ satisfies $f(x) - g(x) = \inf_z \{f(z) - g(z)\}$: the
infimum is attained.

This specializes `ConvexAnalysis.exists_sub_eq_iInf`. -/
theorem theorem_31_1_b_attained {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConcaveFn g) {y₀ : Rn n}
        (hyf : y₀ ∈ ri (convexDom (convexConj (pairing n) f)))
    (hyg : y₀ ∈ ri (concaveDom (concaveConj (pairing n) g))) :
    ∃ x : Rn n, f x - g x = ⨅ z, f z - g z :=
  exists_sub_eq_iInf hf hg (isExactSum_convexConj_of_relint hf hg hyf hyg)

/-!
### Theorem 31.1: the polyhedral forms

"If $g$ is actually polyhedral, $\operatorname{ri}(\operatorname{dom} g)$ and
$\operatorname{ri}(\operatorname{dom} g^*)$ can be replaced by $\operatorname{dom} g$ and
$\operatorname{dom} g^*$ in (a) and (b), respectively (and the closure assumption in (b) is
superfluous). Similarly if $f$ is polyhedral". All four forms use Theorem 20.1
(`ConvexAnalysis.IsExactSum.of_polyhedral`) in place of Theorem 16.4. The closure assumption is
superfluous because a proper polyhedral convex function is closed (Corollary 19.1.2).
-/

/-- Condition (a) of Theorem 31.1 with $f$ polyhedral: a point of $\operatorname{dom} f \cap
\operatorname{ri}(\operatorname{dom} g)$ makes the sum of $f$ and $-g$ exact. -/
private theorem isExactSum_neg_of_polyhedral_left {f g : Rn n → EReal} (hf : PolyhedralFn f)
    (hpf : ProperConvex f) (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n}
        (hxf : x₀ ∈ convexDom f)
    (hxg : x₀ ∈ ri (concaveDom g)) : IsExactSum (pairing n) f fun x => -(g x) :=
  IsExactSum.of_polyhedral hf hpf (concaveFn_iff_convexFn_neg.1 hg)
    (properConcave_iff_properConvex_neg.1 hpg) hxf (by rwa [← concaveDom_eq_convexDom_neg])

/-- Condition (a) of Theorem 31.1 with $g$ polyhedral: a point of
$\operatorname{ri}(\operatorname{dom} f) \cap \operatorname{dom} g$ makes the sum of $f$ and
$-g$ exact. -/
private theorem isExactSum_neg_of_polyhedral_right {f g : Rn n → EReal} (hf : ConvexFn f)
    (hpf : ProperConvex f) (hg : PolyhedralFn fun x => -(g x)) (hpg : ProperConcave g) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (convexDom f)) (hxg : x₀ ∈ concaveDom g) :
    IsExactSum (pairing n) f fun x => -(g x) :=
  (IsExactSum.of_polyhedral hg (properConcave_iff_properConvex_neg.1 hpg) hf hpf
    (by rwa [← concaveDom_eq_convexDom_neg]) hxf).symm

/-- If $-g$ is polyhedral, then $-g^*$ is polyhedral: $-g^*$ is the convex conjugate of $-g$
composed with $y \mapsto -y$, the conjugate of a polyhedral function is polyhedral (Theorem
19.2), and a linear substitution preserves polyhedrality. -/
private theorem polyhedralFn_neg_concaveConj {g : Rn n → EReal}
    (hg : PolyhedralFn fun x => -(g x)) :
    PolyhedralFn fun y : Rn n => -(concaveConj (pairing n) g y) := by
  have hfun : (fun y : Rn n => -(concaveConj (pairing n) g y))
      = compLin (convexConj (pairing n) fun x => -(g x)) (-LinearMap.id) := by
    funext y
    rw [neg_concaveConj, compLin_apply]
    rfl
  rw [hfun]
  change Polyhedral (epi _)
  rw [epi_compLin]
  exact Polyhedral.comap (PolyhedralFn.convexConj (B := pairing n) hg) _

/-- A proper polyhedral concave function is closed (Corollary 19.1.2 for concave functions), so the
closure assumption of Theorem 31.1(b) is superfluous for it. -/
private theorem closedProperConcaveFn_of_polyhedral {g : Rn n → EReal}
    (hg : PolyhedralFn fun x => -(g x)) (hpg : ProperConcave g) : ClosedProperConcaveFn g := by
  have hp : ProperConvex fun x => -(g x) := hpg.properConvex_neg
  exact closedProperConcaveFn_iff_closedProperConvexFn_neg.2
    ⟨hg.convexFn, hg.closedConvex hp.ne_bot, hp⟩

/-- **Theorem 31.1** of [rockafellar1970convex], polyhedral form of (a) with $f$ polyhedral. Let $f$
be a proper polyhedral convex function and $g$ a proper concave function on $\mathbb{R}^n$. If
$\operatorname{dom} f \cap \operatorname{ri}(\operatorname{dom} g) \neq \emptyset$, then $\inf_x
\{f(x) - g(x)\} = \sup_{x^*} \{g^*(x^*) - f^*(x^*)\}$. -/
theorem theorem_31_1_a_polyhedral_left {f g : Rn n → EReal} (hf : PolyhedralFn f)
    (hpf : ProperConvex f)
    (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom f)
    (hxg : x₀ ∈ ri (concaveDom g)) :
    (⨅ x, f x - g x) = ⨆ y : Rn n, concaveConj (pairing n) g y - convexConj (pairing n) f y :=
  fenchel_duality (isExactSum_neg_of_polyhedral_left hf hpf hg hpg hxf hxg)

/-- **Theorem 31.1** of [rockafellar1970convex], attainment under the polyhedral form of (a) with
$f$ polyhedral. Under the hypotheses of `Rockafellar.theorem_31_1_a_polyhedral_left`, the
supremum $\sup_{x^*} \{g^*(x^*) - f^*(x^*)\}$ is attained. -/
theorem theorem_31_1_a_polyhedral_left_attained {f g : Rn n → EReal} (hf : PolyhedralFn f)
    (hpf : ProperConvex f) (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n}
        (hxf : x₀ ∈ convexDom f)
    (hxg : x₀ ∈ ri (concaveDom g)) :
    ∃ y : Rn n, concaveConj (pairing n) g y - convexConj (pairing n) f y = ⨅ x, f x - g x :=
  exists_concaveConj_sub_convexConj_eq (isExactSum_neg_of_polyhedral_left hf hpf hg hpg hxf hxg)

/-- **Theorem 31.1** of [rockafellar1970convex], polyhedral form of (a) with $g$ polyhedral. Let $f$
be a proper convex function and $g$ a proper polyhedral concave function on $\mathbb{R}^n$. If
$\operatorname{ri}(\operatorname{dom} f) \cap \operatorname{dom} g \neq \emptyset$, then $\inf_x
\{f(x) - g(x)\} = \sup_{x^*} \{g^*(x^*) - f^*(x^*)\}$.

A polyhedral concave $g$ is stated as a polyhedral convex $-g$. -/
theorem theorem_31_1_a_polyhedral_right {f g : Rn n → EReal} (hf : ConvexFn f)
    (hpf : ProperConvex f)
    (hg : PolyhedralFn fun x => -(g x)) (hpg : ProperConcave g) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (convexDom f)) (hxg : x₀ ∈ concaveDom g) :
    (⨅ x, f x - g x) = ⨆ y : Rn n, concaveConj (pairing n) g y - convexConj (pairing n) f y :=
  fenchel_duality (isExactSum_neg_of_polyhedral_right hf hpf hg hpg hxf hxg)

/-- **Theorem 31.1** of [rockafellar1970convex], attainment under the polyhedral form of (a) with
$g$ polyhedral. Under the hypotheses of `Rockafellar.theorem_31_1_a_polyhedral_right`, the
supremum $\sup_{x^*} \{g^*(x^*) - f^*(x^*)\}$ is attained. -/
theorem theorem_31_1_a_polyhedral_right_attained {f g : Rn n → EReal} (hf : ConvexFn f)
    (hpf : ProperConvex f) (hg : PolyhedralFn fun x => -(g x)) (hpg : ProperConcave g) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (convexDom f)) (hxg : x₀ ∈ concaveDom g) :
    ∃ y : Rn n, concaveConj (pairing n) g y - convexConj (pairing n) f y = ⨅ x, f x - g x :=
  exists_concaveConj_sub_convexConj_eq (isExactSum_neg_of_polyhedral_right hf hpf hg hpg hxf hxg)

/-- **Theorem 31.1** of [rockafellar1970convex], polyhedral form of (b) with $f$ polyhedral. Let $f$
be a proper polyhedral convex function and $g$ a closed proper concave function on
$\mathbb{R}^n$. If $\operatorname{dom} f^* \cap \operatorname{ri}(\operatorname{dom} g^*) \neq
\emptyset$, then $\inf_x \{f(x) - g(x)\} = \sup_{x^*} \{g^*(x^*) - f^*(x^*)\}$.

The function $f$ is not assumed closed: a proper polyhedral convex function is closed. -/
theorem theorem_31_1_b_polyhedral_left {f g : Rn n → EReal} (hf : PolyhedralFn f)
    (hpf : ProperConvex f)
    (hg : ClosedProperConcaveFn g) {y₀ : Rn n} (hyf : y₀ ∈ convexDom (convexConj (pairing n) f))
    (hyg : y₀ ∈ ri (concaveDom (concaveConj (pairing n) g))) :
    (⨅ x, f x - g x) = ⨆ y : Rn n, concaveConj (pairing n) g y - convexConj (pairing n) f y := by
  have hfc : ClosedProperConvexFn f := ⟨hf.convexFn, hf.closedConvex hpf.ne_bot, hpf⟩
  refine fenchel_duality_of_closed hfc hg (IsExactSum.of_polyhedral
    (PolyhedralFn.convexConj (B := pairing n) hf) (properConvex_convexConj (B := pairing n) hfc)
    (concaveFn_iff_convexFn_neg.1 (concaveFn_concaveConj (pairing n) g))
    (properConcave_iff_properConvex_neg.1 ⟨⟨y₀, intrinsicInterior_subset hyg⟩,
      fun y => concaveConj_ne_top hg.proper.concaveDom_nonempty y⟩) hyf ?_)
  change y₀ ∈ ri (convexDom fun y => -(concaveConj (pairing n) g y))
  rwa [← concaveDom_eq_convexDom_neg]

/-- **Theorem 31.1** of [rockafellar1970convex], polyhedral form of (b) with $g$ polyhedral. Let $f$
be a closed proper convex function and $g$ a proper polyhedral concave function on
$\mathbb{R}^n$. If $\operatorname{ri}(\operatorname{dom} f^*) \cap \operatorname{dom} g^* \neq
\emptyset$, then $\inf_x \{f(x) - g(x)\} = \sup_{x^*} \{g^*(x^*) - f^*(x^*)\}$.

The function $g$ is not assumed closed. -/
theorem theorem_31_1_b_polyhedral_right {f g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : PolyhedralFn fun x => -(g x)) (hpg : ProperConcave g) {y₀ : Rn n}
    (hyf : y₀ ∈ ri (convexDom (convexConj (pairing n) f)))
    (hyg : y₀ ∈ concaveDom (concaveConj (pairing n) g)) :
    (⨅ x, f x - g x) = ⨆ y : Rn n, concaveConj (pairing n) g y - convexConj (pairing n) f y := by
  refine fenchel_duality_of_closed hf (closedProperConcaveFn_of_polyhedral hg hpg)
    (IsExactSum.of_polyhedral (polyhedralFn_neg_concaveConj hg)
      (properConcave_iff_properConvex_neg.1 ⟨⟨y₀, hyg⟩,
        fun y => concaveConj_ne_top hpg.concaveDom_nonempty y⟩)
      (convexFn_convexConj (pairing n) f) (properConvex_convexConj (B := pairing n) hf) ?_ hyf).symm
  rwa [← concaveDom_eq_convexDom_neg]

/-- **Theorem 31.1** of [rockafellar1970convex], finiteness: "if (a) and (b) both hold, the infimum
and supremum are necessarily finite". Let $f, g : \mathbb{R}^n \to [-\infty, +\infty]$, with $f$
proper (finite somewhere and never $-\infty$) and $g$ proper (finite somewhere and never
$+\infty$). If $\operatorname{dom} f \cap \operatorname{dom} g$ and $\operatorname{dom} f^* \cap
\operatorname{dom} g^*$ are non-empty, then $\inf_x \{f(x) - g(x)\}$ is a real number.

**Generalization.** The book assumes (a) and (b). The statement uses only the weaker conditions
without relative interiors, which (a) and (b) imply, and it does not assume $f$ convex or $g$
concave. A point of $\operatorname{dom} f \cap \operatorname{dom} g$ bounds the infimum above,
and a point of $\operatorname{dom} f^* \cap \operatorname{dom} g^*$ bounds it below by weak
duality. -/
theorem theorem_31_1_finite {f g : Rn n → EReal} (hpf : ProperConvex f) (hpg : ProperConcave g)
    {x₀ : Rn n} (hxf : x₀ ∈ convexDom f) (hxg : x₀ ∈ concaveDom g) {y₀ : Rn n}
    (hyf : y₀ ∈ convexDom (convexConj (pairing n) f))
    (hyg : y₀ ∈ concaveDom (concaveConj (pairing n) g)) :
    ∃ r : ℝ, (⨅ x, f x - g x) = (r : EReal) := by
  have hgy : (⊥ : EReal) < concaveConj (pairing n) g y₀ := hyg
  have hfy : convexConj (pairing n) f y₀ < ⊤ := hyf
  obtain ⟨c, hc⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hgy.ne'
    (lt_top_iff_ne_top.2 (concaveConj_ne_top hpg.concaveDom_nonempty y₀))
  obtain ⟨d, hd⟩ := EReal.exists_coe_of_ne_bot_of_lt_top
    (convexConj_ne_bot hpf.convexDom_nonempty y₀) hfy
  have hlow : ((c - d : ℝ) : EReal) ≤ ⨅ x, f x - g x := by
    refine le_iInf fun x => ?_
    have h := theorem_31_1_weak f g x y₀
    rwa [hc, hd, ← EReal.coe_sub] at h
  have hbot : (⨅ x, f x - g x) ≠ ⊥ := by
    intro hcon
    rw [hcon, le_bot_iff] at hlow
    exact EReal.coe_ne_bot _ hlow
  have htop : (⨅ x, f x - g x) < ⊤ := by
    refine lt_of_le_of_lt (iInf_le (fun x => f x - g x) x₀) ?_
    have h1 : f x₀ < ⊤ := hxf
    have h2 : (⊥ : EReal) < g x₀ := hxg
    have h3 : -(g x₀) ≠ ⊤ := by rw [Ne, EReal.neg_eq_top_iff]; exact h2.ne'
    exact EReal.add_lt_top h1.ne h3
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hbot htop
  exact ⟨r, hr⟩

/-!
### Corollary 31.2.1: a linear transformation between the two functions

Condition (a) of [rockafellar1970convex], a point $x \in \operatorname{ri}(\operatorname{dom} f)$
with $Ax \in \operatorname{ri}(\operatorname{dom} g)$, does two things, and the backbone separates
them. It makes the sum of $f$ and $-(g \circ A)$ exact (Theorem 16.4, `ConvexAnalysis.IsExactSum`),
and it makes the pullback of $-g$ along $A$ exact (Theorem 16.3, `ConvexAnalysis.IsExactImage`).
-/

/-- Condition (a) of Corollary 31.2.1, the exact pullback: a point $x_0$ with $Ax_0 \in
\operatorname{ri}(\operatorname{dom} g)$ makes the pullback of $-g$ along $A$ exact (Theorem
16.3). -/
private theorem isExactImage_neg_of_relint {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    (hg : ClosedProperConcaveFn g) {x₀ : Rn n} (hx₀ : A x₀ ∈ ri (concaveDom g)) :
    IsExactImage (pairing n) (pairing m) A (LinearMap.adjoint A) (isAdjointPair_adjoint A)
      fun w => -(g w) :=
  IsExactImage.of_relint_closed (isAdjointPair_adjoint A) hg.closedProperConvexFn_neg
    (by rwa [← concaveDom_eq_convexDom_neg])

/-- Condition (a) of Corollary 31.2.1, the exact sum: by Theorem 16.4, with
$\operatorname{ri}(\operatorname{dom}(-(g \circ A))) =
A^{-1}(\operatorname{ri}(\operatorname{dom}(-g)))$ from Theorem 6.7, the sum of $f$ and
$-(g \circ A)$ is exact. -/
private theorem isExactSum_neg_comp_of_relint {f : Rn n → EReal} {g : Rn m → EReal}
    (A : Rn n →ₗ[ℝ] Rn m) (hf : ConvexFn f) (hpf : ProperConvex f) (hg : ConcaveFn g)
    (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ ri (convexDom f))
    (hxg : A x₀ ∈ ri (concaveDom g)) : IsExactSum (pairing n) f fun x => -(g (A x)) := by
  have hgn : ConvexFn fun w => -(g w) := concaveFn_iff_convexFn_neg.1 hg
  have hpgn : ProperConvex fun w => -(g w) := properConcave_iff_properConvex_neg.1 hpg
  have hxg' : A x₀ ∈ ri (convexDom fun w => -(g w)) := by rwa [← concaveDom_eq_convexDom_neg]
  have hcomp : ConvexFn (compLin (fun w => -(g w)) A) := convexFn_compLin A hgn
  have hpcomp : ProperConvex (compLin (fun w => -(g w)) A) :=
    ⟨⟨x₀, by rw [convexDom_compLin]; exact Set.mem_preimage.2 (intrinsicInterior_subset hxg')⟩,
      fun x => hpgn.ne_bot (A x)⟩
  have hri : x₀ ∈ ri (convexDom (compLin (fun w => -(g w)) A)) := by
    rw [convexDom_compLin, Convex.relint_preimage hgn.convex_convexDom A ⟨x₀, hxg'⟩]
    exact hxg'
  exact IsExactSum.of_relint hf hpf hcomp hpcomp hxf hri

/-- **Corollary 31.2.1** of [rockafellar1970convex], condition (a). Let $f$ be a proper convex
function on $\mathbb{R}^n$, let $g$ be a closed proper concave function on $\mathbb{R}^m$, and
let $A : \mathbb{R}^n \to \mathbb{R}^m$ be linear. If some
$x \in \operatorname{ri}(\operatorname{dom} f)$ has
$Ax \in \operatorname{ri}(\operatorname{dom} g)$, then
$$\inf_x \{f(x) - g(Ax)\} = \sup_{u^*} \{g^*(u^*) - f^*(A^* u^*)\}.$$

**Generalization.** The book assumes $f$ closed. The statement does not, because condition (a)
does not use it. -/
theorem corollary_31_2_1_a {f : Rn n → EReal} {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    (hf : ConvexFn f) (hpf : ProperConvex f) (hg : ClosedProperConcaveFn g) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (convexDom f)) (hxg : A x₀ ∈ ri (concaveDom g)) :
    (⨅ x, f x - g (A x))
      = ⨆ z : Rn m, concaveConj (pairing m) g z
          - convexConj (pairing n) f (LinearMap.adjoint A z) :=
  fenchel_duality_comp (isAdjointPair_adjoint A)
    (isExactSum_neg_comp_of_relint A hf hpf hg.concave hg.proper hxf hxg)
    (isExactImage_neg_of_relint A hg hxg)

/-- **Corollary 31.2.1** of [rockafellar1970convex], attainment under (a). Under the hypotheses of
`Rockafellar.corollary_31_2_1_a`, some $u^*$ satisfies $g^*(u^*) - f^*(A^* u^*) = \inf_x
\{f(x) - g(Ax)\}$: the supremum is attained.

This specializes `ConvexAnalysis.exists_concaveConj_sub_convexConj_comp_eq`. -/
theorem corollary_31_2_1_a_attained {f : Rn n → EReal} {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    (hf : ConvexFn f) (hpf : ProperConvex f) (hg : ClosedProperConcaveFn g) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (convexDom f)) (hxg : A x₀ ∈ ri (concaveDom g)) :
    ∃ z : Rn m, concaveConj (pairing m) g z - convexConj (pairing n) f (LinearMap.adjoint A z)
      = ⨅ x, f x - g (A x) :=
  exists_concaveConj_sub_convexConj_comp_eq (isAdjointPair_adjoint A)
    (isExactSum_neg_comp_of_relint A hf hpf hg.concave hg.proper hxf hxg)
    (isExactImage_neg_of_relint A hg hxg)

/-- **Corollary 31.2.1** of [rockafellar1970convex], polyhedral form with $g$ polyhedral. Let $f$ be
a proper convex function on $\mathbb{R}^n$, let $g$ be a proper polyhedral concave function on
$\mathbb{R}^m$, and let $A : \mathbb{R}^n \to \mathbb{R}^m$ be linear. If some
$x \in \operatorname{ri}(\operatorname{dom} f)$ has $Ax \in \operatorname{dom} g$, then
$$\inf_x \{f(x) - g(Ax)\} = \sup_{u^*} \{g^*(u^*) - f^*(A^* u^*)\}.$$

The book states this without proof: "It can be shown that in Corollary 31.2.1, just as in
Theorem 31.1, $\operatorname{ri}$ can be omitted whenever the corresponding function $f$ or $g$
is actually polyhedral. However, the proof will not be given here." Both parts of condition (a)
have polyhedral forms. Since $-(g \circ A)$ is polyhedral, Theorem 20.1 replaces Theorem 16.4
for the sum, and `ConvexAnalysis.IsExactImage.of_polyhedral` (Corollary 19.3.1 in place of
Theorem 16.3) gives the pullback. Neither needs a relative interior on the side of $g$, and $g$
is closed automatically. -/
theorem corollary_31_2_1_a_polyhedral_right {f : Rn n → EReal} {g : Rn m → EReal}
    (A : Rn n →ₗ[ℝ] Rn m) (hf : ConvexFn f) (hpf : ProperConvex f)
    (hg : PolyhedralFn fun w => -(g w)) (hpg : ProperConcave g) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (convexDom f)) (hxg : A x₀ ∈ concaveDom g) :
    (⨅ x, f x - g (A x))
      = ⨆ z : Rn m, concaveConj (pairing m) g z
          - convexConj (pairing n) f (LinearMap.adjoint A z) := by
  have hpgn : ProperConvex fun w => -(g w) := properConcave_iff_properConvex_neg.1 hpg
  have hxg' : A x₀ ∈ convexDom fun w => -(g w) := by rwa [← concaveDom_eq_convexDom_neg]
  refine fenchel_duality_comp (isAdjointPair_adjoint A)
    ((IsExactSum.of_polyhedral (PolyhedralFn.compLin hg A)
      ⟨⟨x₀, hxg'⟩, fun x => hpgn.ne_bot (A x)⟩ hf hpf hxg' hxf).symm)
    (IsExactImage.of_polyhedral (isAdjointPair_adjoint A) hg hpgn hxg')

/-- **Corollary 31.2.1** of [rockafellar1970convex], polyhedral form with $f$ polyhedral. Let $f$ be
a proper polyhedral convex function on $\mathbb{R}^n$, let $g$ be a closed proper concave
function on $\mathbb{R}^m$, and let $A : \mathbb{R}^n \to \mathbb{R}^m$ be linear. If some
$x \in \operatorname{dom} f$ has $Ax \in \operatorname{ri}(\operatorname{dom} g)$, then
$$\inf_x \{f(x) - g(Ax)\} = \sup_{u^*} \{g^*(u^*) - f^*(A^* u^*)\}.$$

This is the other half of the assertion that the book does not prove. Only the sum changes,
because the pullback concerns $g$ alone. -/
theorem corollary_31_2_1_a_polyhedral_left {f : Rn n → EReal} {g : Rn m → EReal}
    (A : Rn n →ₗ[ℝ] Rn m) (hf : PolyhedralFn f) (hpf : ProperConvex f)
    (hg : ClosedProperConcaveFn g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom f)
    (hxg : A x₀ ∈ ri (concaveDom g)) :
    (⨅ x, f x - g (A x))
      = ⨆ z : Rn m, concaveConj (pairing m) g z
          - convexConj (pairing n) f (LinearMap.adjoint A z) := by
  have hgn : ConvexFn fun w => -(g w) := concaveFn_iff_convexFn_neg.1 hg.concave
  have hpgn : ProperConvex fun w => -(g w) := properConcave_iff_properConvex_neg.1 hg.proper
  have hxg' : A x₀ ∈ ri (convexDom fun w => -(g w)) := by rwa [← concaveDom_eq_convexDom_neg]
  have hpcomp : ProperConvex (compLin (fun w => -(g w)) A) :=
    ⟨⟨x₀, by rw [convexDom_compLin]; exact Set.mem_preimage.2 (intrinsicInterior_subset hxg')⟩,
      fun x => hpgn.ne_bot (A x)⟩
  have hri : x₀ ∈ ri (convexDom (compLin (fun w => -(g w)) A)) := by
    rw [convexDom_compLin, Convex.relint_preimage hgn.convex_convexDom A ⟨x₀, hxg'⟩]
    exact hxg'
  exact fenchel_duality_comp (isAdjointPair_adjoint A)
    (IsExactSum.of_polyhedral hf hpf (convexFn_compLin A hgn) hpcomp hxf hri)
    (isExactImage_neg_of_relint A hg hxg)

/-! ### Theorem 31.3: the Kuhn–Tucker conditions -/

/-- **Theorem 31.3** of [rockafellar1970convex], weak duality, the "general inequality" of the
proof. For all functions $f$ on $\mathbb{R}^n$ and $g$ on $\mathbb{R}^m$, every linear
$A : \mathbb{R}^n \to \mathbb{R}^m$, and all $x \in \mathbb{R}^n$, $u^* \in \mathbb{R}^m$,
$$g^*(u^*) - f^*(A^* u^*) \le f(x) - g(Ax).$$
-/
theorem theorem_31_3_weak {f : Rn n → EReal} {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    (x : Rn n) (z : Rn m) :
    concaveConj (pairing m) g z - convexConj (pairing n) f (LinearMap.adjoint A z) ≤ f x
        - g (A x) :=
  concaveConj_sub_convexConj_comp_le_sub (isAdjointPair_adjoint A) x z

/-- **Theorem 31.3** of [rockafellar1970convex]. Let $f$ be a proper function on $\mathbb{R}^n$
(finite somewhere and never $-\infty$), let $g$ be a function that is proper in the concave
sense on $\mathbb{R}^m$ (finite somewhere and never $+\infty$), and let
$A : \mathbb{R}^n \to \mathbb{R}^m$ be linear. For $x \in \mathbb{R}^n$ and
$u^* \in \mathbb{R}^m$,
$$f(x) - g(Ax) = g^*(u^*) - f^*(A^* u^*)$$
if and only if $x$ and $u^*$ satisfy the **Kuhn–Tucker conditions** $A^* u^* \in \partial f(x)$
and $-u^* \in \partial(-g)(Ax)$, that is, $u^*$ is a supergradient of $g$ at $Ax$.

**Generalization.** The book assumes $f$ and $g$ closed, and it writes the second condition as
$Ax \in \partial g^*(u^*)$, with the superdifferential of the concave function $g^*$. For closed
$g$ the two forms of the second condition are equivalent. The statement does not assume $f$ and
$g$ closed, and it does not assume $f$ convex or $g$ concave either: only properness is used.
Without closedness of $g$, the condition $Ax \in \partial g^*(u^*)$ is weaker and does not give
the equality, so the statement uses the form $-u^* \in \partial(-g)(Ax)$.

`Rockafellar.theorem_31_3_kuhnTucker_concave` translates the second condition into Fenchel's
equality $g(Ax) + g^*(u^*) = \langle Ax, u^* \rangle$ for the concave pair. -/
theorem theorem_31_3 {f : Rn n → EReal} {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    (hpf : ProperConvex f) (hpg : ProperConcave g) {x : Rn n} {z : Rn m} :
    f x - g (A x)
        = concaveConj (pairing m) g z - convexConj (pairing n) f (LinearMap.adjoint A z) ↔
      LinearMap.adjoint A z ∈ subdifferential (pairing n) f x ∧
        -z ∈ subdifferential (pairing m) (fun w => -(g w)) (A x) :=
  sub_comp_eq_concaveConj_sub_convexConj_iff (isAdjointPair_adjoint A) hpf
    (properConcave_iff_properConvex_neg.1 hpg)

/-- **Theorem 31.3** of [rockafellar1970convex], the second Kuhn–Tucker condition in the form of the
book. Let $g$ be a function that is proper in the concave sense on $\mathbb{R}^m$ (finite
somewhere and never $+\infty$), and let $w, u^* \in \mathbb{R}^m$. Then
$-u^* \in \partial(-g)(w)$ if and only if Fenchel's inequality for the concave pair holds with
equality:
$$g(w) + g^*(u^*) = \langle w, u^* \rangle.$$

This is Theorem 23.5 for concave functions. It specializes
`ConvexAnalysis.neg_mem_subdifferential_neg_iff_add_concaveConj_eq`. -/
theorem theorem_31_3_kuhnTucker_concave {g : Rn m → EReal} (hpg : ProperConcave g) (w z : Rn m) :
    -z ∈ subdifferential (pairing m) (fun v => -(g v)) w ↔
      g w + concaveConj (pairing m) g z = ((pairing m w z : ℝ) : EReal) :=
  neg_mem_subdifferential_neg_iff_add_concaveConj_eq (properConcave_iff_properConvex_neg.1 hpg)

/-- **Theorem 31.3** of [rockafellar1970convex], first consequence. For all functions $f$, $g$ and
every linear $A$: if $f(x) - g(Ax) = g^*(u^*) - f^*(A^* u^*)$, then $x$ minimizes $f - gA$, that
is, $\inf_w \{f(w) - g(Aw)\} = f(x) - g(Ax)$.

Only weak duality is used. -/
theorem theorem_31_3_iInf {f : Rn n → EReal} {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    {x : Rn n} {z : Rn m}
    (h : f x - g (A x)
      = concaveConj (pairing m) g z - convexConj (pairing n) f (LinearMap.adjoint A z)) :
    (⨅ w, f w - g (A w)) = f x - g (A x) :=
  iInf_sub_comp_eq_of_sub_eq (isAdjointPair_adjoint A) h

/-- **Theorem 31.3** of [rockafellar1970convex], second consequence. For all functions $f$, $g$ and
every linear $A$: if $f(x) - g(Ax) = g^*(u^*) - f^*(A^* u^*)$, then $u^*$ maximizes
$g^* - f^* A^*$. -/
theorem theorem_31_3_iSup {f : Rn n → EReal} {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    {x : Rn n} {z : Rn m}
    (h : f x - g (A x)
      = concaveConj (pairing m) g z - convexConj (pairing n) f (LinearMap.adjoint A z)) :
    (⨆ w : Rn m, concaveConj (pairing m) g w - convexConj (pairing n) f (LinearMap.adjoint A w))
      = concaveConj (pairing m) g z - convexConj (pairing n) f (LinearMap.adjoint A z) :=
  iSup_sub_comp_eq_of_sub_eq (isAdjointPair_adjoint A) h

/-- **Theorem 31.3** of [rockafellar1970convex] for $A$ the identity, the case of Fenchel's duality
theorem. Let $f$ be proper (finite somewhere and never $-\infty$) and $g$ proper (finite
somewhere and never $+\infty$) on $\mathbb{R}^n$. Then $f(x) - g(x) = g^*(x^*) - f^*(x^*)$ if
and only if $x^* \in \partial f(x)$ and $-x^* \in \partial(-g)(x)$.

For closed $g$ the second condition is the condition $x \in \partial g^*(x^*)$ of the book. This
specializes `ConvexAnalysis.sub_eq_concaveConj_sub_convexConj_iff`. -/
theorem theorem_31_3_id {f g : Rn n → EReal} (hpf : ProperConvex f) (hpg : ProperConcave g)
    {x y : Rn n} :
    f x - g x = concaveConj (pairing n) g y - convexConj (pairing n) f y ↔
      y ∈ subdifferential (pairing n) f x ∧ -y ∈ subdifferential (pairing n) (fun z => -(g z)) x :=
  sub_eq_concaveConj_sub_convexConj_iff hpf (properConcave_iff_properConvex_neg.1 hpg)

/-- **Corollary 31.3.1** of [rockafellar1970convex]. Let $f$ be a proper convex function on
$\mathbb{R}^n$, let $g$ be a closed proper concave function on $\mathbb{R}^m$, and let
$A : \mathbb{R}^n \to \mathbb{R}^m$ be linear. Assume that some $x_0 \in
\operatorname{ri}(\operatorname{dom} f)$ has $Ax_0 \in \operatorname{ri}(\operatorname{dom} g)$.
Then $x \in \mathbb{R}^n$ minimizes $f - gA$ if and only if there is a $u^* \in \mathbb{R}^m$
with $A^* u^* \in \partial f(x)$ and $-u^* \in \partial(-g)(Ax)$.

**Generalization.** The book assumes $f$ closed. The statement does not.

The proof of the book is "Apply Corollary 31.2.1". The forward direction uses the attainment
clause of that corollary, and the backward direction uses only weak duality. -/
theorem corollary_31_3_1 {f : Rn n → EReal} {g : Rn m → EReal} (A : Rn n →ₗ[ℝ] Rn m)
    (hf : ConvexFn f) (hpf : ProperConvex f) (hg : ClosedProperConcaveFn g) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (convexDom f)) (hxg : A x₀ ∈ ri (concaveDom g)) (x : Rn n) :
    (⨅ w, f w - g (A w)) = f x - g (A x) ↔
      ∃ z : Rn m, LinearMap.adjoint A z ∈ subdifferential (pairing n) f x ∧
        -z ∈ subdifferential (pairing m) (fun w => -(g w)) (A x) :=
  iInf_sub_comp_eq_iff_exists_kuhnTucker (isAdjointPair_adjoint A)
    (isExactSum_neg_comp_of_relint A hf hpf hg.concave hg.proper hxf hxg)
    (isExactImage_neg_of_relint A hg hxg) x

/-- **Corollary 31.3.1** of [rockafellar1970convex] for $A$ the identity, the form that Fenchel's
duality theorem itself carries. Let $f$ be a proper convex function and $g$ a proper concave
function on $\mathbb{R}^n$ with $\operatorname{ri}(\operatorname{dom} f) \cap
\operatorname{ri}(\operatorname{dom} g) \neq \emptyset$. Then $x$ minimizes $f - g$ if and only
if there is an $x^*$ with $x^* \in \partial f(x)$ and $-x^* \in \partial(-g)(x)$.

This specializes `ConvexAnalysis.iInf_sub_eq_iff_exists_kuhnTucker`. -/
theorem corollary_31_3_1_id {f g : Rn n → EReal} (hf : ConvexFn f) (hpf : ProperConvex f)
    (hg : ConcaveFn g) (hpg : ProperConcave g) {x₀ : Rn n} (hxf : x₀ ∈ ri (convexDom f))
    (hxg : x₀ ∈ ri (concaveDom g)) (x : Rn n) :
    (⨅ z, f z - g z) = f x - g x ↔
      ∃ y : Rn n, y ∈ subdifferential (pairing n) f x ∧
        -y ∈ subdifferential (pairing n) (fun z => -(g z)) x :=
  iInf_sub_eq_iff_exists_kuhnTucker (isExactSum_neg_of_relint hf hpf hg hpg hxf hxg) x

/-!
### Theorem 31.4: the minimum of a convex function over a convex cone

The dual cone $K^*$ of [rockafellar1970convex] is the negative of `ConvexAnalysis.polarCone`.
Negation of a set is a preimage, so $y \in -K^\circ$ unfolds to $-y \in K^\circ$.
`Rockafellar.theorem_31_4_dualCone` states the useful form.
-/

/-- **Theorem 31.4** of [rockafellar1970convex], the dual cone. For $K \subseteq \mathbb{R}^n$, the
dual cone $K^* = \{x^* \mid \langle x, x^* \rangle \ge 0 \text{ for all } x \in K\}$ is the
negative of the polar cone $K^\circ$: $y \in -K^\circ$ if and only if
$\langle z, y \rangle \ge 0$ for every $z \in K$. -/
theorem theorem_31_4_dualCone {K : Set (Rn n)} {y : Rn n} :
    y ∈ -(polarCone (pairing n) K) ↔ ∀ z ∈ K, (0 : ℝ) ≤ pairing n z y :=
  mem_neg_polarCone

/-- Condition (a) of Theorem 31.4 makes the sum of $f$ and the indicator function
$\delta(\cdot \mid K)$ exact. -/
private theorem isExactSum_indicatorFn_of_relint {B : Rn n →ₗ[ℝ] Rn n →ₗ[ℝ] ℝ}
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] {f : Rn n → EReal} {K : Set (Rn n)}
    (hf : ConvexFn f) (hpf : ProperConvex f) (hK : Convex ℝ K) {x₀ : Rn n}
        (hxf : x₀ ∈ ri (convexDom f))
    (hxK : x₀ ∈ ri K) : IsExactSum B f (indicatorFn K) :=
  IsExactSum.of_relint hf hpf (convexFn_indicatorFn.2 hK)
    ⟨⟨x₀, by rw [convexDom_indicatorFn]; exact intrinsicInterior_subset hxK⟩, indicatorFn_ne_bot K⟩
    hxf (by rwa [convexDom_indicatorFn])

/-- Condition (a) of Theorem 31.4 for a polyhedral $K$, with $K$ in place of $\operatorname{ri} K$,
makes the sum of $f$ and $\delta(\cdot \mid K)$ exact. -/
private theorem isExactSum_indicatorFn_of_polyhedral {B : Rn n →ₗ[ℝ] Rn n →ₗ[ℝ] ℝ}
    [IsCompatiblePairing B] [IsCompatiblePairing B.flip] {f : Rn n → EReal} {K : Set (Rn n)}
    (hf : ConvexFn f) (hpf : ProperConvex f) (hK : Polyhedral K) {x₀ : Rn n}
        (hxf : x₀ ∈ ri (convexDom f))
    (hxK : x₀ ∈ K) : IsExactSum B f (indicatorFn K) :=
  (IsExactSum.of_polyhedral (polyhedralFn_indicatorFn hK)
    ⟨⟨x₀, by rwa [convexDom_indicatorFn]⟩, indicatorFn_ne_bot K⟩ hf hpf
    (by rwa [convexDom_indicatorFn]) hxf).symm

/-- The negative $-S$ of a polyhedral set $S$ is polyhedral, because $-S$ is the preimage of $S$
under $y \mapsto -y$. -/
private theorem polyhedral_neg_set {S : Set (Rn n)} (hS : Polyhedral S) : Polyhedral (-S) := by
  have h : (-S) = (-LinearMap.id : Rn n →ₗ[ℝ] Rn n) ⁻¹' S := rfl
  rw [h]
  exact Polyhedral.comap hS _

/-- If $K$ is a polyhedral cone, then $K^*$ is polyhedral: for a cone the polar cone is the polar
set (`ConvexAnalysis.polarCone_eq_polarSet_of_isCone`), which is polyhedral by Corollary 19.2.2,
and negation preserves polyhedrality. -/
private theorem polyhedral_neg_polarCone {K : Set (Rn n)} (hK : Polyhedral K)
    (hcone : ∀ a : ℝ, 0 < a → a • K = K) : Polyhedral (-(polarCone (pairing n) K)) := by
  rw [polarCone_eq_polarSet_of_isCone (isCone_iff_smul_eq.2 hcone)]
  exact polyhedral_neg_set (corollary_19_2_2 hK)

/-- **Theorem 31.4** of [rockafellar1970convex], condition (a). Let $f$ be a proper convex function
on $\mathbb{R}^n$, and let $K$ be a non-empty convex cone ($aK = K$ for every $a > 0$). If
$\operatorname{ri}(\operatorname{dom} f) \cap \operatorname{ri} K \neq \emptyset$, then
$$\inf \{f(x) \mid x \in K\} = -\inf \{f^*(x^*) \mid x^* \in K^*\}.$$

**Generalization.** The book assumes $f$ and $K$ closed. Condition (a) does not use closedness,
which belongs to condition (b).

This specializes `ConvexAnalysis.iInf_mem_eq_neg_iInf_mem_neg_polarCone`. -/
theorem theorem_31_4_a {f : Rn n → EReal} {K : Set (Rn n)} (hf : ConvexFn f) (hpf : ProperConvex f)
    (hK : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (convexDom f)) (hxK : x₀ ∈ ri K) :
    (⨅ z ∈ K, f z) = -(⨅ w ∈ -(polarCone (pairing n) K), convexConj (pairing n) f w) :=
  iInf_mem_eq_neg_iInf_mem_neg_polarCone
    (isExactSum_indicatorFn_of_relint (B := pairing n) hf hpf hK hxf hxK)
      (isCone_iff_smul_eq.2 hcone) hne

/-- **Theorem 31.4** of [rockafellar1970convex], attainment under (a). Under the hypotheses of
`Rockafellar.theorem_31_4_a`, the infimum of $f^*$ over $K^*$ is attained at some $x^* \in K^*$.

This specializes `ConvexAnalysis.exists_mem_neg_polarCone_convexConj_eq_iInf`. -/
theorem theorem_31_4_a_attained {f : Rn n → EReal} {K : Set (Rn n)} (hf : ConvexFn f)
    (hpf : ProperConvex f) (hK : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty)
    {x₀ : Rn n} (hxf : x₀ ∈ ri (convexDom f)) (hxK : x₀ ∈ ri K) :
    ∃ y ∈ -(polarCone (pairing n) K), convexConj (pairing n) f y
      = ⨅ w ∈ -(polarCone (pairing n) K), convexConj (pairing n) f w :=
  exists_mem_neg_polarCone_convexConj_eq_iInf
    (isExactSum_indicatorFn_of_relint (B := pairing n) hf hpf hK hxf hxK)
      (isCone_iff_smul_eq.2 hcone) hne

/-- **Theorem 31.4** of [rockafellar1970convex], polyhedral form of (a): "if $K$ is polyhedral,
$\operatorname{ri} K$ and $\operatorname{ri} K^*$ can be replaced by $K$ and $K^*$ in (a) and
(b)". Let $f$ be a proper convex function on $\mathbb{R}^n$ and $K$ a non-empty polyhedral
convex cone. If $\operatorname{ri}(\operatorname{dom} f) \cap K \neq \emptyset$, then $\inf
\{f(x) \mid x \in K\} = -\inf \{f^*(x^*) \mid x^* \in K^*\}$. -/
theorem theorem_31_4_a_polyhedral {f : Rn n → EReal} {K : Set (Rn n)} (hf : ConvexFn f)
    (hpf : ProperConvex f) (hK : Polyhedral K) (hcone : ∀ a : ℝ, 0 < a → a • K = K)
        (hne : K.Nonempty)
    {x₀ : Rn n} (hxf : x₀ ∈ ri (convexDom f)) (hxK : x₀ ∈ K) :
    (⨅ z ∈ K, f z) = -(⨅ w ∈ -(polarCone (pairing n) K), convexConj (pairing n) f w) :=
  iInf_mem_eq_neg_iInf_mem_neg_polarCone
    (isExactSum_indicatorFn_of_polyhedral (B := pairing n) hf hpf hK hxf hxK)
      (isCone_iff_smul_eq.2 hcone) hne

/-- **Theorem 31.4** of [rockafellar1970convex], attainment under the polyhedral form of (a). Under
the hypotheses of `Rockafellar.theorem_31_4_a_polyhedral`, the infimum of $f^*$ over $K^*$ is
attained. -/
theorem theorem_31_4_a_polyhedral_attained {f : Rn n → EReal} {K : Set (Rn n)} (hf : ConvexFn f)
    (hpf : ProperConvex f) (hK : Polyhedral K) (hcone : ∀ a : ℝ, 0 < a → a • K = K)
        (hne : K.Nonempty)
    {x₀ : Rn n} (hxf : x₀ ∈ ri (convexDom f)) (hxK : x₀ ∈ K) :
    ∃ y ∈ -(polarCone (pairing n) K), convexConj (pairing n) f y
      = ⨅ w ∈ -(polarCone (pairing n) K), convexConj (pairing n) f w :=
  exists_mem_neg_polarCone_convexConj_eq_iInf
    (isExactSum_indicatorFn_of_polyhedral (B := pairing n) hf hpf hK hxf hxK)
      (isCone_iff_smul_eq.2 hcone) hne

/-- **Theorem 31.4** of [rockafellar1970convex], condition (b). Let $f$ be a closed proper convex
function on $\mathbb{R}^n$, and let $K$ be a non-empty closed convex cone. If
$\operatorname{ri}(\operatorname{dom} f^*) \cap \operatorname{ri} K^* \neq \emptyset$, then
$$\inf \{f(x) \mid x \in K\} = -\inf \{f^*(x^*) \mid x^* \in K^*\}.$$

The proof applies condition (a) to the dual pair $f^*$ and $K^*$, and returns by $K^{**} = K$
(Theorem 14.1, `ConvexAnalysis.neg_polarCone_neg_polarCone`) and $f^{**} = f$ (the
Fenchel–Moreau theorem). These two steps use the closedness of $K$ and of $f$. -/
theorem theorem_31_4_b {f : Rn n → EReal} {K : Set (Rn n)} (hf : ClosedProperConvexFn f)
    (hK : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (hcl : IsClosed K)
    {y₀ : Rn n} (hyf : y₀ ∈ ri (convexDom (convexConj (pairing n) f)))
    (hyK : y₀ ∈ ri (-(polarCone (pairing n) K))) :
    (⨅ z ∈ K, f z) = -(⨅ w ∈ -(polarCone (pairing n) K), convexConj (pairing n) f w) := by
  have hex : IsExactSum (pairing n).flip (convexConj (pairing n) f)
      (indicatorFn (-(polarCone (pairing n) K))) :=
    isExactSum_indicatorFn_of_relint (B := (pairing n).flip) (convexFn_convexConj (pairing n) f)
      (properConvex_convexConj (B := pairing n) hf) (convex_neg_polarCone (pairing n) K) hyf hyK
  have h := iInf_mem_eq_neg_iInf_mem_neg_polarCone hex
    (isCone_iff_smul_eq.2 (smul_neg_polarCone (pairing n) K)) (neg_polarCone_nonempty (pairing n) K)
  rw [neg_polarCone_neg_polarCone hK (isCone_iff_smul_eq.2 hcone) hne hcl,
    show convexConj (pairing n).flip (convexConj (pairing n) f)
        = f from convexBiconj_eq_self hf.convex hf.closed]
    at h
  rw [h, neg_neg]

/-- **Theorem 31.4** of [rockafellar1970convex], attainment under (b). Under the hypotheses of
`Rockafellar.theorem_31_4_b`, the infimum of $f$ over $K$ is attained at some $x \in K$.

This specializes `ConvexAnalysis.exists_mem_eq_iInf_of_isExactSum_convexConj`. -/
theorem theorem_31_4_b_attained {f : Rn n → EReal} {K : Set (Rn n)} (hf : ClosedProperConvexFn f)
    (hK : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (hcl : IsClosed K)
    {y₀ : Rn n} (hyf : y₀ ∈ ri (convexDom (convexConj (pairing n) f)))
    (hyK : y₀ ∈ ri (-(polarCone (pairing n) K))) :
    ∃ x ∈ K, f x = ⨅ z ∈ K, f z :=
  exists_mem_eq_iInf_of_isExactSum_convexConj (convexBiconj_eq_self hf.convex hf.closed)
    (isExactSum_indicatorFn_of_relint (B := (pairing n).flip) (convexFn_convexConj (pairing n) f)
      (properConvex_convexConj (B := pairing n) hf) (convex_neg_polarCone (pairing n) K) hyf hyK)
    hK (isCone_iff_smul_eq.2 hcone) hne hcl

/-- **Theorem 31.4** of [rockafellar1970convex], polyhedral form of (b). Let $f$ be a closed proper
convex function on $\mathbb{R}^n$ and $K$ a non-empty polyhedral convex cone. If
$\operatorname{ri}(\operatorname{dom} f^*) \cap K^* \neq \emptyset$, then $\inf \{f(x) \mid x
\in K\} = -\inf \{f^*(x^*) \mid x^* \in K^*\}$.

Since $K$ is polyhedral, $K^*$ is polyhedral, and a polyhedral set is closed, so no closedness
hypothesis is needed. -/
theorem theorem_31_4_b_polyhedral {f : Rn n → EReal} {K : Set (Rn n)} (hf : ClosedProperConvexFn f)
    (hK : Polyhedral K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) {y₀ : Rn n}
    (hyf : y₀ ∈ ri (convexDom (convexConj (pairing n) f))) (hyK : y₀ ∈ -(polarCone (pairing n) K)) :
    (⨅ z ∈ K, f z) = -(⨅ w ∈ -(polarCone (pairing n) K), convexConj (pairing n) f w) := by
  have hex : IsExactSum (pairing n).flip (convexConj (pairing n) f)
      (indicatorFn (-(polarCone (pairing n) K))) :=
    isExactSum_indicatorFn_of_polyhedral (B := (pairing n).flip) (convexFn_convexConj (pairing n) f)
      (properConvex_convexConj (B := pairing n) hf) (polyhedral_neg_polarCone hK hcone) hyf hyK
  have h := iInf_mem_eq_neg_iInf_mem_neg_polarCone hex
    (isCone_iff_smul_eq.2 (smul_neg_polarCone (pairing n) K)) (neg_polarCone_nonempty (pairing n) K)
  rw [neg_polarCone_neg_polarCone hK.convex
    (isCone_iff_smul_eq.2 hcone) hne (Polyhedral.isClosed hK),
    show convexConj (pairing n).flip (convexConj (pairing n) f)
        = f from convexBiconj_eq_self hf.convex hf.closed]
    at h
  rw [h, neg_neg]

/-- **Theorem 31.4** of [rockafellar1970convex], attainment under the polyhedral form of (b). Under
the hypotheses of `Rockafellar.theorem_31_4_b_polyhedral`, the infimum of $f$ over $K$ is
attained. -/
theorem theorem_31_4_b_polyhedral_attained {f : Rn n → EReal} {K : Set (Rn n)}
    (hf : ClosedProperConvexFn f) (hK : Polyhedral K) (hcone : ∀ a : ℝ, 0 < a → a • K = K)
    (hne : K.Nonempty) {y₀ : Rn n} (hyf : y₀ ∈ ri (convexDom (convexConj (pairing n) f)))
    (hyK : y₀ ∈ -(polarCone (pairing n) K)) :
    ∃ x ∈ K, f x = ⨅ z ∈ K, f z :=
  exists_mem_eq_iInf_of_isExactSum_convexConj (convexBiconj_eq_self hf.convex hf.closed)
    (isExactSum_indicatorFn_of_polyhedral (B := (pairing n).flip)
        (convexFn_convexConj (pairing n) f)
      (properConvex_convexConj (B := pairing n) hf) (polyhedral_neg_polarCone hK hcone) hyf hyK)
    hK.convex (isCone_iff_smul_eq.2 hcone) hne (Polyhedral.isClosed hK)

/-- **Theorem 31.4** of [rockafellar1970convex], optimality conditions. Let $f$ be a function that
is proper in the convex sense on $\mathbb{R}^n$ (finite somewhere and never $-\infty$), let
$K \subseteq \mathbb{R}^n$, and let $x \in K$ and $x^* \in K^*$. Then the primal and dual values
agree, $f(x) = -f^*(x^*)$, that is,
$$f(x) + f^*(x^*) = 0,$$
if and only if $x^* \in \partial f(x)$ and $\langle x, x^* \rangle = 0$.

The book reads this off the Kuhn–Tucker conditions of Theorem 31.3 for
$g = -\delta(\cdot \mid K)$, where $x \in \partial g^*(x^*)$ unfolds into the three conditions
$x \in K$, $x^* \in K^*$ and $\langle x, x^* \rangle = 0$. This specializes
`ConvexAnalysis.add_convexConj_eq_zero_iff_mem_subdifferential_and_pairing_eq_zero`. -/
theorem theorem_31_4_optimality {f : Rn n → EReal} {K : Set (Rn n)} (hpf : ProperConvex f)
    {x y : Rn n}
    (hxK : x ∈ K) (hyK : y ∈ -(polarCone (pairing n) K)) :
    f x + convexConj (pairing n) f y = 0 ↔
      y ∈ subdifferential (pairing n) f x ∧ (pairing n x y : ℝ) = 0 :=
  add_convexConj_eq_zero_iff_mem_subdifferential_and_pairing_eq_zero hpf hxK hyK

/-- **Theorem 31.4** of [rockafellar1970convex]: the optimality conditions make $x$ optimal for the
primal problem. If $x^* \in K^*$, $x^* \in \partial f(x)$ and $\langle x, x^* \rangle = 0$, then
$f(x) \le f(z)$ for every $z \in K$. -/
theorem theorem_31_4_optimality_primal {f : Rn n → EReal} {K : Set (Rn n)} {x y : Rn n}
    (hyK : y ∈ -(polarCone (pairing n) K)) (hy : y ∈ subdifferential (pairing n) f x)
    (hxy : (pairing n x y : ℝ) = 0) {z : Rn n} (hz : z ∈ K) : f x ≤ f z :=
  forall_le_of_mem_subdifferential_of_pairing_eq_zero hyK hy hxy hz

/-- **Theorem 31.4** of [rockafellar1970convex]: the optimality conditions make $x^*$ optimal for
the dual problem. Let $f$ be proper (finite somewhere and never $-\infty$). If $x \in K$,
$x^* \in \partial f(x)$ and $\langle x, x^* \rangle = 0$, then $f^*(x^*) \le f^*(w)$ for every
$w \in K^*$. -/
theorem theorem_31_4_optimality_dual {f : Rn n → EReal} {K : Set (Rn n)} (hpf : ProperConvex f)
    {x y : Rn n} (hxK : x ∈ K) (hy : y ∈ subdifferential (pairing n) f x)
    (hxy : (pairing n x y : ℝ) = 0) {w : Rn n} (hwK : w ∈ -(polarCone (pairing n) K)) :
    convexConj (pairing n) f y ≤ convexConj (pairing n) f w :=
  convexConj_le_convexConj_of_mem_subdifferential_of_pairing_eq_zero hpf hxK hy hxy hwK

/-- **Theorem 31.4** of [rockafellar1970convex], weak duality. For every function $f$ on
$\mathbb{R}^n$, every $K \subseteq \mathbb{R}^n$, $x \in K$ and $x^* \in K^*$,
$$-f^*(x^*) \le f(x).$$
-/
theorem theorem_31_4_weak {f : Rn n → EReal} {K : Set (Rn n)} {x : Rn n} (hxK : x ∈ K) {w : Rn n}
    (hwK : w ∈ -(polarCone (pairing n) K)) : -(convexConj (pairing n) f w) ≤ f x :=
  neg_convexConj_le_of_mem_neg_polarCone hxK hwK

/-!
### Corollary 31.4.1: the non-negative orthant

`Rockafellar.nonnegOrthant n` is the set $\{z \mid z \ge 0\}$ of Section 12. The book states the
conditions of Corollary 31.4.1 without a relative interior on the side of the orthant, which is the
polyhedral form of Theorem 31.4. The orthant is polyhedral, which permits this.
-/

/-- The non-negative orthant is polyhedral: it is defined by the $n$ inequalities $-\xi_j \le 0$. -/
private theorem polyhedral_nonnegOrthant (n : ℕ) : Polyhedral (nonnegOrthant n) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : Fin n → (Rn n →ₗ[ℝ] ℝ), ∀ (j : Fin n) (x : Rn n), c j x = x j :=
    ⟨fun j => ⟨⟨fun x => x j, fun _ _ => rfl⟩, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  refine ⟨(Finset.univ : Finset (Fin n)).image fun j => (-(c j), (0 : ℝ)), ?_⟩
  ext x
  constructor
  · intro hx q hq
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
    simpa [hc j x] using hx j
  · intro hx j
    have h := hx (-(c j), (0 : ℝ)) (Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩)
    simpa [hc j x] using h

/-- The non-negative orthant is invariant under multiplication by every $a > 0$, which is the cone
condition of the book. -/
private theorem smul_nonnegOrthant (n : ℕ) {a : ℝ} (ha : 0 < a) :
    a • nonnegOrthant n = nonnegOrthant n := by
  ext z
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨u, hu, rfl⟩ j
    exact mul_nonneg ha.le (hu j)
  · intro hz
    exact ⟨a⁻¹ • z, fun j => mul_nonneg (inv_nonneg.2 ha.le) (hz j),
      by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]⟩

/-- The non-negative orthant is self-dual: if $K$ is the non-negative orthant of $\mathbb{R}^n$,
then $K^* = -K^\circ = K$.

`ConvexAnalysis.polarCone_nonnegOrthant` (Theorem 14.1) gives $K^\circ$ as the non-positive
orthant, and the sign in the definition of $K^*$ turns it back. -/
theorem neg_polarCone_nonnegOrthant (n : ℕ) :
    -(polarCone (pairing n) (nonnegOrthant n)) = nonnegOrthant n := by
  have h : polarCone (pairing n) (nonnegOrthant n) = {y : Rn n | ∀ i, y i ≤ 0} :=
    polarCone_nonnegOrthant
  rw [h]
  ext y
  constructor
  · intro hy j
    simpa using (Set.mem_neg.1 hy) j
  · intro hy
    exact Set.mem_neg.2 fun j => by simpa using hy j

/-- For $x \ge 0$ and $x^* \ge 0$ in $\mathbb{R}^n$, $\langle x, x^* \rangle = 0$ if and only if
$\xi_j \xi_j^* = 0$ for every $j$. This is complementary slackness in Corollary 31.4.1. -/
private theorem pairing_eq_zero_iff_of_mem_nonnegOrthant {x y : Rn n} (hx : x ∈ nonnegOrthant n)
    (hy : y ∈ nonnegOrthant n) : (pairing n x y : ℝ) = 0 ↔ ∀ j, x j * y j = 0 := by
  rw [pairing_apply, inner_rn,
    Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (hx j) (hy j)]
  exact ⟨fun h j => h j (Finset.mem_univ j), fun h j _ => h j⟩

/-- **Corollary 31.4.1** of [rockafellar1970convex], condition (a). Let $f$ be a proper convex
function on $\mathbb{R}^n$. If some $x \in \operatorname{ri}(\operatorname{dom} f)$ satisfies
$x \ge 0$, then
$$\inf \{f(x) \mid x \ge 0\} = -\inf \{f^*(x^*) \mid x^* \ge 0\}.$$

**Generalization.** The book assumes $f$ closed. Condition (a) does not use it, as in
`Rockafellar.theorem_31_4_a`.

This is the polyhedral form of Theorem 31.4 for the non-negative orthant, which is polyhedral
and is its own dual cone (`Rockafellar.neg_polarCone_nonnegOrthant`). The condition of the book
asks only $x \ge 0$, not $x \in \operatorname{ri} K$. -/
theorem corollary_31_4_1_a {f : Rn n → EReal} (hf : ConvexFn f) (hpf : ProperConvex f) {x₀ : Rn n}
    (hxf : x₀ ∈ ri (convexDom f)) (hx₀ : x₀ ∈ nonnegOrthant n) :
    (⨅ z ∈ nonnegOrthant n, f z)
      = -(⨅ w ∈ nonnegOrthant n, convexConj (pairing n) f w) := by
  have h := theorem_31_4_a_polyhedral hf hpf (polyhedral_nonnegOrthant n)
    (fun a ha => smul_nonnegOrthant n ha) ⟨0, zero_mem_nonnegOrthant n⟩ hxf hx₀
  rwa [neg_polarCone_nonnegOrthant] at h

/-- **Corollary 31.4.1** of [rockafellar1970convex], attainment under (a). Under the hypotheses of
`Rockafellar.corollary_31_4_1_a`, the infimum of $f^*$ over $\{x^* \mid x^* \ge 0\}$ is
attained. -/
theorem corollary_31_4_1_a_attained {f : Rn n → EReal} (hf : ConvexFn f) (hpf : ProperConvex f)
    {x₀ : Rn n} (hxf : x₀ ∈ ri (convexDom f)) (hx₀ : x₀ ∈ nonnegOrthant n) :
    ∃ y ∈ nonnegOrthant n, convexConj (pairing n) f y
      = ⨅ w ∈ nonnegOrthant n, convexConj (pairing n) f w := by
  have h := theorem_31_4_a_polyhedral_attained hf hpf (polyhedral_nonnegOrthant n)
    (fun a ha => smul_nonnegOrthant n ha) ⟨0, zero_mem_nonnegOrthant n⟩ hxf hx₀
  rwa [neg_polarCone_nonnegOrthant] at h

/-- **Corollary 31.4.1** of [rockafellar1970convex], condition (b). Let $f$ be a closed proper
convex function on $\mathbb{R}^n$. If some $x^* \in \operatorname{ri}(\operatorname{dom} f^*)$
satisfies $x^* \ge 0$, then
$$\inf \{f(x) \mid x \ge 0\} = -\inf \{f^*(x^*) \mid x^* \ge 0\}.$$
-/
theorem corollary_31_4_1_b {f : Rn n → EReal} (hf : ClosedProperConvexFn f) {y₀ : Rn n}
    (hyf : y₀ ∈ ri (convexDom (convexConj (pairing n) f))) (hy₀ : y₀ ∈ nonnegOrthant n) :
    (⨅ z ∈ nonnegOrthant n, f z)
      = -(⨅ w ∈ nonnegOrthant n, convexConj (pairing n) f w) := by
  have h := theorem_31_4_b_polyhedral hf (polyhedral_nonnegOrthant n)
    (fun a ha => smul_nonnegOrthant n ha) ⟨0, zero_mem_nonnegOrthant n⟩ hyf
    (by rw [neg_polarCone_nonnegOrthant]; exact hy₀)
  rwa [neg_polarCone_nonnegOrthant] at h

/-- **Corollary 31.4.1** of [rockafellar1970convex], attainment under (b). Under the hypotheses of
`Rockafellar.corollary_31_4_1_b`, the infimum of $f$ over $\{x \mid x \ge 0\}$ is attained. -/
theorem corollary_31_4_1_b_attained {f : Rn n → EReal} (hf : ClosedProperConvexFn f) {y₀ : Rn n}
    (hyf : y₀ ∈ ri (convexDom (convexConj (pairing n) f))) (hy₀ : y₀ ∈ nonnegOrthant n) :
    ∃ x ∈ nonnegOrthant n, f x = ⨅ z ∈ nonnegOrthant n, f z := by
  refine theorem_31_4_b_polyhedral_attained hf (polyhedral_nonnegOrthant n)
    (fun a ha => smul_nonnegOrthant n ha) ⟨0, zero_mem_nonnegOrthant n⟩ (y₀ := y₀) hyf ?_
  rw [neg_polarCone_nonnegOrthant]
  exact hy₀

/-- **Corollary 31.4.1** of [rockafellar1970convex], complementary slackness. Let $f$ be a function
that is proper in the convex sense on $\mathbb{R}^n$ (finite somewhere and never $-\infty$), and
let $x = (\xi_1, \dots, \xi_n) \ge 0$ and $x^* = (\xi_1^*, \dots, \xi_n^*) \ge 0$. Then
$f(x) + f^*(x^*) = 0$, which means that the two infima are the negatives of each other and are
attained at $x$ and $x^*$, if and only if $x^* \in \partial f(x)$ and $\xi_j \xi_j^* = 0$ for
every $j$.

The condition $\langle x, x^* \rangle = 0$ of Theorem 31.4 becomes the condition on coordinates
because both vectors are non-negative. -/
theorem corollary_31_4_1_optimality {f : Rn n → EReal} (hpf : ProperConvex f) {x y : Rn n}
    (hx : x ∈ nonnegOrthant n) (hy : y ∈ nonnegOrthant n) :
    f x + convexConj (pairing n) f y = 0 ↔
      y ∈ subdifferential (pairing n) f x ∧ ∀ j, x j * y j = 0 := by
  have hyK : y ∈ -(polarCone (pairing n) (nonnegOrthant n)) := by
    rw [neg_polarCone_nonnegOrthant]; exact hy
  rw [theorem_31_4_optimality hpf hx hyK, pairing_eq_zero_iff_of_mem_nonnegOrthant hx hy]

/-! ### Corollary 31.4.2: a subspace -/

/-- The polar cone of a subspace $L$ of $\mathbb{R}^n$ is its orthogonal complement $L^\perp$.

The backbone gives the polar cone of a subspace as its annihilator
(`ConvexAnalysis.polarCone_coe_submodule'`), and on $\mathbb{R}^n$ the annihilator is the
orthogonal complement `Mᗮ`. -/
theorem polarCone_coe_submodule_eq_orthogonal (M : Submodule ℝ (Rn n)) :
    polarCone (pairing n) (M : Set (Rn n)) = ((Mᗮ : Submodule ℝ (Rn n)) : Set (Rn n)) :=
  polarCone_submodule_rn M

/-- **Corollary 31.4.2** of [rockafellar1970convex], condition (a). Let $f$ be a proper convex
function on $\mathbb{R}^n$ and $L$ a subspace of $\mathbb{R}^n$. If $L \cap
\operatorname{ri}(\operatorname{dom} f) \neq \emptyset$, then
$$\inf \{f(x) \mid x \in L\} = -\inf \{f^*(x^*) \mid x^* \in L^\perp\}.$$

**Generalization.** The book assumes $f$ closed. Condition (a) does not use it, as in
`Rockafellar.theorem_31_4_a`.

This is Theorem 31.4 for $K = L$, where the dual cone $K^* = -K^\circ$ is $L^\perp$. A subspace
is polyhedral, so the condition of the book needs no relative interior on the side of $L$. -/
theorem corollary_31_4_2_a {f : Rn n → EReal} (hf : ConvexFn f) (hpf : ProperConvex f)
    {M : Submodule ℝ (Rn n)} {x₀ : Rn n} (hxf : x₀ ∈ ri (convexDom f)) (hxM : x₀ ∈ M) :
    (⨅ z ∈ (M : Set (Rn n)), f z)
      = -(⨅ w ∈ ((Mᗮ : Submodule ℝ (Rn n)) : Set (Rn n)), convexConj (pairing n) f w) := by
  have hex := isExactSum_indicatorFn_of_polyhedral (B := pairing n) hf hpf
    (polyhedral_coe_submodule M) hxf hxM
  have h := iInf_mem_submodule_eq_neg_iInf_mem_polarCone hex
  rwa [polarCone_coe_submodule_eq_orthogonal] at h

/-- **Corollary 31.4.2** of [rockafellar1970convex], attainment under (a). Under the hypotheses of
`Rockafellar.corollary_31_4_2_a`, the infimum of $f^*$ over $L^\perp$ is attained. -/
theorem corollary_31_4_2_a_attained {f : Rn n → EReal} (hf : ConvexFn f) (hpf : ProperConvex f)
    {M : Submodule ℝ (Rn n)} {x₀ : Rn n} (hxf : x₀ ∈ ri (convexDom f)) (hxM : x₀ ∈ M) :
    ∃ y ∈ ((Mᗮ : Submodule ℝ (Rn n)) : Set (Rn n)), convexConj (pairing n) f y
      = ⨅ w ∈ ((Mᗮ : Submodule ℝ (Rn n)) : Set (Rn n)), convexConj (pairing n) f w := by
  have h := theorem_31_4_a_polyhedral_attained hf hpf (polyhedral_coe_submodule M)
    (fun a ha => smul_coe_submodule M ha) ⟨0, M.zero_mem⟩ hxf hxM
  rwa [neg_polarCone_coe_submodule, polarCone_coe_submodule_eq_orthogonal] at h

/-- **Corollary 31.4.2** of [rockafellar1970convex], attainment under (b). Let $f$ be a closed
proper convex function on $\mathbb{R}^n$ and $L$ a subspace of $\mathbb{R}^n$. If $L^\perp \cap
\operatorname{ri}(\operatorname{dom} f^*) \neq \emptyset$, then the infimum of $f$ over $L$ is
attained at some $x \in L$. -/
theorem corollary_31_4_2_b_attained {f : Rn n → EReal} (hf : ClosedProperConvexFn f)
    {M : Submodule ℝ (Rn n)} {y₀ : Rn n} (hyf : y₀ ∈ ri (convexDom (convexConj (pairing n) f)))
    (hyM : y₀ ∈ Mᗮ) :
    ∃ x ∈ (M : Set (Rn n)), f x = ⨅ z ∈ (M : Set (Rn n)), f z := by
  refine theorem_31_4_b_polyhedral_attained hf (polyhedral_coe_submodule M)
    (fun a ha => smul_coe_submodule M ha) ⟨0, M.zero_mem⟩ (y₀ := y₀) hyf ?_
  rw [neg_polarCone_coe_submodule, polarCone_coe_submodule_eq_orthogonal]
  exact hyM

/-- **Corollary 31.4.2** of [rockafellar1970convex], optimality conditions. Let $f$ be a function
that is proper in the convex sense on $\mathbb{R}^n$ (finite somewhere and never $-\infty$), let
$L$ be a subspace, and let $x \in L$ and $x^* \in L^\perp$. Then $f(x) + f^*(x^*) = 0$ if and
only if $x^* \in \partial f(x)$.

Over a subspace the condition $\langle x, x^* \rangle = 0$ of Theorem 31.4 holds automatically. -/
theorem corollary_31_4_2_optimality {f : Rn n → EReal} (hpf : ProperConvex f)
    {M : Submodule ℝ (Rn n)} {x y : Rn n} (hxM : x ∈ M) (hyM : y ∈ Mᗮ) :
    f x + convexConj (pairing n) f y = 0 ↔ y ∈ subdifferential (pairing n) f x := by
  refine add_convexConj_eq_zero_iff_mem_subdifferential_of_mem_submodule hpf hxM ?_
  rw [polarCone_coe_submodule_eq_orthogonal]
  exact hyM

/-! ### Corollary 31.4.3: the duality between a co-finite $h$ and $h^*$ -/

/-- **Corollary 31.4.3** of [rockafellar1970convex]. Let $h$ be a co-finite convex function on
$\mathbb{R}^n$ that is finite everywhere, let $K$ be a non-empty convex cone, and let
$z, z^* \in \mathbb{R}^n$. Then
$$\inf_{x \in K} \{h(z + x) - \langle x, z^* \rangle\} + \inf_{x^* \in K^*} \{h^*(z^* + x^*) -
  \langle z, x^* \rangle\} = \langle z, z^* \rangle.$$

**Generalization.** The book assumes $K$ closed throughout the corollary. Only the attainment of
the first infimum needs it (`Rockafellar.corollary_31_4_3_attained`).

A co-finite function (`ConvexAnalysis.Cofinite`) is a closed proper convex function whose
recession function is $+\infty$ in every direction $y \neq 0$, and "finite everywhere" is
$\operatorname{dom} h = \mathbb{R}^n$. The proof is Theorem 12.3 followed by Theorem 31.4: the
function $f(x) = h(z + x) - \langle x, z^* \rangle$ has $\operatorname{dom} f = \mathbb{R}^n$
and $\operatorname{dom} f^* = \mathbb{R}^n$, so both conditions of Theorem 31.4 hold in their
strongest form. -/
theorem corollary_31_4_3 {h : Rn n → EReal} (hcof : Cofinite h) (hdom : convexDom h = univ)
    {K : Set (Rn n)} (hconv : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty)
    (z z' : Rn n) :
    (⨅ x ∈ K, (h (z + x) - ((pairing n x z' : ℝ) : EReal)))
        + (⨅ w ∈ -(polarCone (pairing n) K),
            (convexConj (pairing n) h (z' + w) - ((pairing n z w : ℝ) : EReal)))
      = ((pairing n z z' : ℝ) : EReal) :=
  iInf_mem_add_iInf_mem_neg_polarCone_eq_pairing hcof hdom hconv
    (isCone_iff_smul_eq.2 hcone) hne z z'

/-- **Corollary 31.4.3** of [rockafellar1970convex]: under the hypotheses of
`Rockafellar.corollary_31_4_3`, the first infimum $\inf_{x \in K} \{h(z + x) - \langle x, z^*
\rangle\}$ is a real number. -/
theorem corollary_31_4_3_iInf_eq_coe {h : Rn n → EReal} (hcof : Cofinite h)
    (hdom : convexDom h = univ)
    {K : Set (Rn n)} (hconv : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty)
    (z z' : Rn n) :
    ∃ s : ℝ, (⨅ x ∈ K, (h (z + x) - ((pairing n x z' : ℝ) : EReal))) = (s : EReal) :=
  exists_iInf_mem_eq_coe_of_cofinite hcof hdom hconv (isCone_iff_smul_eq.2 hcone) hne z z'

/-- **Corollary 31.4.3** of [rockafellar1970convex]: under the hypotheses of
`Rockafellar.corollary_31_4_3`, the second infimum $\inf_{x^* \in K^*} \{h^*(z^* + x^*) -
\langle z, x^* \rangle\}$ is a real number. -/
theorem corollary_31_4_3_iInf_dual_eq_coe {h : Rn n → EReal} (hcof : Cofinite h)
    (hdom : convexDom h = univ) {K : Set (Rn n)} (hconv : Convex ℝ K)
    (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (z z' : Rn n) :
    ∃ r : ℝ, (⨅ w ∈ -(polarCone (pairing n) K),
      (convexConj (pairing n) h (z' + w) - ((pairing n z w : ℝ) : EReal))) = (r : EReal) :=
  exists_iInf_mem_neg_polarCone_eq_coe_of_cofinite hcof hdom hconv
    (isCone_iff_smul_eq.2 hcone) hne z z'

/-- **Corollary 31.4.3** of [rockafellar1970convex]: under the hypotheses of
`Rockafellar.corollary_31_4_3`, and if $K$ is closed, the first infimum is attained at some
$x \in K$.

This is the only part of the corollary that needs $K$ closed. -/
theorem corollary_31_4_3_attained {h : Rn n → EReal} (hcof : Cofinite h) (hdom : convexDom h = univ)
    {K : Set (Rn n)} (hconv : Convex ℝ K) (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty)
    (hcl : IsClosed K) (z z' : Rn n) :
    ∃ x ∈ K, h (z + x) - ((pairing n x z' : ℝ) : EReal)
      = ⨅ u ∈ K, (h (z + u) - ((pairing n u z' : ℝ) : EReal)) :=
  exists_iInf_mem_eq_of_cofinite hcof hdom hconv (isCone_iff_smul_eq.2 hcone) hne hcl z z'

/-- **Corollary 31.4.3** of [rockafellar1970convex]: under the hypotheses of
`Rockafellar.corollary_31_4_3`, the second infimum is attained at some $x^* \in K^*$.

Closedness of $K$ is not needed. The statement carries the co-finiteness of $h$, although the
attainment of this infimum does not need it. -/
theorem corollary_31_4_3_dual_attained {h : Rn n → EReal} (hcof : Cofinite h)
    (hdom : convexDom h = univ) {K : Set (Rn n)} (hconv : Convex ℝ K)
    (hcone : ∀ a : ℝ, 0 < a → a • K = K) (hne : K.Nonempty) (z z' : Rn n) :
    ∃ w ∈ -(polarCone (pairing n) K),
      convexConj (pairing n) h (z' + w) - ((pairing n z w : ℝ) : EReal)
        = ⨅ v ∈ -(polarCone (pairing n) K),
            (convexConj (pairing n) h (z' + v) - ((pairing n z v : ℝ) : EReal)) :=
  exists_iInf_mem_neg_polarCone_eq_of_cofinite hcof hdom hconv (isCone_iff_smul_eq.2 hcone) hne z z'

/-!
### Theorem 31.5 (Moreau), proximations, and the two corollaries

The function $w$ of [rockafellar1970convex] is `ConvexAnalysis.quadFn (Rockafellar.pairing n)`, and
`Rockafellar.theorem_31_5_quadFn` shows that it is $w(z) = \tfrac12 |z|^2$. The infimal convolution
is `ConvexAnalysis.infConv`, and the proximation is `ConvexAnalysis.prox`. The function
$x \mapsto f(x) + w(z - x)$, whose infimum is $(f \mathbin{\square} w)(z)$, is
`ConvexAnalysis.moreauObj`.
-/

/-- **Theorem 31.5** of [rockafellar1970convex], the function $w$: $w(z) = \tfrac12 |z|^2$ for every
$z \in \mathbb{R}^n$. This specializes `ConvexAnalysis.quadFn_innerL`. -/
theorem theorem_31_5_quadFn (z : Rn n) : quadFn (pairing n) z = ((‖z‖ ^ 2 / 2 : ℝ) : EReal) :=
  quadFn_innerL z

/-- **Theorem 31.5** of [rockafellar1970convex] (Moreau's theorem). Let $f$ be a closed proper
convex function on $\mathbb{R}^n$, and let $w(z) = \tfrac12 |z|^2$. Then
$$(f \mathbin{\square} w) + (f^* \mathbin{\square} w) = w,$$
as an equation between functions on $\mathbb{R}^n$.

The proof in the backbone is Theorem 27.1(a) applied to $x \mapsto f(x) + w(z - x)$, with
`ConvexAnalysis.IsExactSum.convexConj_add_apply` splitting the conjugate of this sum at the
origin. It uses no separation and no relative interior. -/
theorem theorem_31_5 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    infConv f (quadFn (pairing n)) + infConv (convexConj (pairing n) f) (quadFn (pairing n))
      = quadFn (pairing n) :=
  funext fun z => moreau_add hf z

/-- **Theorem 31.5** of [rockafellar1970convex], the identity at a point. Let $f$ be a closed proper
convex function on $\mathbb{R}^n$ and $z \in \mathbb{R}^n$. Then
$$\inf_x \{f(x) + w(z - x)\} + \inf_{x^*} \{f^*(x^*) + w(z - x^*)\} = w(z).$$
-/
theorem theorem_31_5_apply {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    (⨅ x, (f x + quadFn (pairing n) (z - x)))
        + (⨅ y, (convexConj (pairing n) f y + quadFn (pairing n) (z - y)))
      = quadFn (pairing n) z := by
  rw [← infConv_quadFn_apply hf.proper.ne_bot z,
    ← infConv_quadFn_apply (convexConj_ne_bot hf.proper.convexDom_nonempty) z]
  exact moreau_add hf z

/-- **Theorem 31.5** of [rockafellar1970convex]: "both infima are finite". For a closed proper
convex function $f$ on $\mathbb{R}^n$ and $z \in \mathbb{R}^n$, $(f \mathbin{\square} w)(z)$ is
a real number.

This specializes `ConvexAnalysis.infConv_quadFn_ne_bot` and
`ConvexAnalysis.infConv_quadFn_ne_top`. -/
theorem theorem_31_5_finite {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    ∃ r : ℝ, infConv f (quadFn (pairing n)) z = (r : EReal) :=
  EReal.exists_coe_of_ne_bot_of_lt_top (infConv_quadFn_ne_bot hf z)
    (lt_top_iff_ne_top.2 (infConv_quadFn_ne_top hf z))

/-- **Theorem 31.5** of [rockafellar1970convex]: for a closed proper convex function $f$ on
$\mathbb{R}^n$ and $z \in \mathbb{R}^n$, the dual infimum $(f^* \mathbin{\square} w)(z)$ is a
real number too. -/
theorem theorem_31_5_finite_conj {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    ∃ r : ℝ, infConv (convexConj (pairing n) f) (quadFn (pairing n)) z = (r : EReal) :=
  EReal.exists_coe_of_ne_bot_of_lt_top (infConv_convexConj_quadFn_ne_bot hf z)
    (lt_top_iff_ne_top.2 (infConv_convexConj_quadFn_ne_top hf z))

/-- **Theorem 31.5** of [rockafellar1970convex], unique attainment. Let $f$ be a closed proper
convex function on $\mathbb{R}^n$ and $z \in \mathbb{R}^n$. There is exactly one pair $(x, x^*)$
with $x + x^* = z$ and $x^* \in \partial f(x)$.

The book states that the two infima of Theorem 31.5 are uniquely attained at $x$ and $x^*$; for
the first infimum this is `Rockafellar.theorem_31_5_argmin_eq`. In the backbone, uniqueness
comes from the monotonicity of $\partial f$ (Theorem 24.8) at the two pairs, not from strict
convexity of $w$. Attainment is Theorem 27.2, through the recession function of
$x \mapsto f(x) + w(z - x)$. This specializes
`ConvexAnalysis.existsUnique_sub_mem_subdifferential`. -/
theorem theorem_31_5_existsUnique {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    ∃! p : Rn n × Rn n, p.1 + p.2 = z ∧ p.2 ∈ subdifferential (pairing n) f p.1 := by
  obtain ⟨x, hx, huniq⟩ := existsUnique_sub_mem_subdifferential (B := pairing n) hf z
  refine ⟨(x, z - x), ⟨by module, hx⟩, ?_⟩
  rintro ⟨u, v⟩ ⟨hsum, hmem⟩
  have hsum' : u + v = z := hsum
  have hv : v = z - u := by rw [← hsum']; abel
  subst hv
  have hu : u = x := huniq u hmem
  subst hu
  rfl

/-- **Theorem 31.5** of [rockafellar1970convex], the minimizer. Let $f$ be a closed proper convex
function on $\mathbb{R}^n$ and $z, x \in \mathbb{R}^n$. Then $x$ minimizes
$x' \mapsto f(x') + w(z - x')$ if and only if $z - x \in \partial f(x)$.

This specializes `ConvexAnalysis.mem_argmin_moreauObj_iff`. -/
theorem theorem_31_5_argmin_iff {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z x : Rn n) :
    x ∈ argmin (moreauObj (pairing n) f z) ↔ z - x ∈ subdifferential (pairing n) f x :=
  mem_argmin_moreauObj_iff hf z x

/-- **Theorem 31.5** of [rockafellar1970convex]: for a closed proper convex function $f$ on
$\mathbb{R}^n$ and $z \in \mathbb{R}^n$, the set of minimizers of $x \mapsto f(x) + w(z - x)$ is
the single point $\operatorname{prox}(z \mid f)$.

This specializes `ConvexAnalysis.argmin_moreauObj_eq_singleton`. -/
theorem theorem_31_5_argmin_eq {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    argmin (moreauObj (pairing n) f z) = {prox (pairing n) f z} :=
  argmin_moreauObj_eq_singleton hf z

/-- **Section 31** of [rockafellar1970convex], the defining property of the **proximation**. For a
closed proper convex function $f$ on $\mathbb{R}^n$ and $z, x \in \mathbb{R}^n$,
$\operatorname{prox}(z \mid f) = x$ if and only if $z - x \in \partial f(x)$.

This specializes `ConvexAnalysis.prox_eq_iff`. -/
theorem prox_eq_iff_sub_mem_subdifferential {f : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (z x : Rn n) : prox (pairing n) f z = x ↔ z - x ∈ subdifferential (pairing n) f x :=
  prox_eq_iff hf z x

/-- **Section 31** of [rockafellar1970convex], Moreau's decomposition. For a closed proper convex
function $f$ on $\mathbb{R}^n$ and $z \in \mathbb{R}^n$,
$$z = \operatorname{prox}(z \mid f) + \operatorname{prox}(z \mid f^*).$$
-/
theorem prox_add_prox_convexConj_eq {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    prox (pairing n) f z + prox (pairing n) (convexConj (pairing n) f) z = z :=
  prox_add_prox_convexConj hf z

/-- **Section 31** of [rockafellar1970convex]. For a closed proper convex function $f$ on
$\mathbb{R}^n$ and $z \in \mathbb{R}^n$, $\operatorname{prox}(z \mid f^*) = z -
\operatorname{prox}(z \mid f)$.

This specializes `ConvexAnalysis.prox_convexConj_eq`. -/
theorem prox_convexConj_eq_sub {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    prox (pairing n) (convexConj (pairing n) f) z = z - prox (pairing n) f z :=
  prox_convexConj_eq hf z

/-- **Theorem 31.5** of [rockafellar1970convex], gradient of the Moreau envelope of $f$. Let $f$ be
a closed proper convex function on $\mathbb{R}^n$ and $z \in \mathbb{R}^n$. Then the gradient of
$f \mathbin{\square} w$ at $z$ is
$$\nabla (f \mathbin{\square} w)(z) = z - \operatorname{prox}(z \mid f),$$
which is the vector $x^* = \operatorname{prox}(z \mid f^*)$ of the book.

The gradient is Mathlib's `gradient` of the real-valued function
$u \mapsto (f \mathbin{\square} w)(u)$, read through `EReal.toReal`. Mathlib's `gradient` is
defined at every point, so the formula alone does not state differentiability. The
subdifferential of $f \mathbin{\square} w$ at $z$ is the single point
$\operatorname{prox}(z \mid f^*)$, and the converse of Theorem 25.1 makes it a gradient. This
specializes `ConvexAnalysis.gradient_infConv_quadFn`. -/
theorem theorem_31_5_gradient {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    gradient (fun u => (infConv f (quadFn (pairing n)) u).toReal) z
      = z - prox (pairing n) f z :=
  gradient_infConv_quadFn hf z

/-- **Theorem 31.5** of [rockafellar1970convex], gradient of the Moreau envelope of $f^*$. Let $f$
be a closed proper convex function on $\mathbb{R}^n$ and $z \in \mathbb{R}^n$. Then the gradient
of $f^* \mathbin{\square} w$ at $z$ is
$$\nabla (f^* \mathbin{\square} w)(z) = \operatorname{prox}(z \mid f),$$
which is the vector $x$ of the book.

The gradient is read through `EReal.toReal`, as in `Rockafellar.theorem_31_5_gradient`. This
specializes `ConvexAnalysis.gradient_infConv_convexConj_quadFn`. -/
theorem theorem_31_5_gradient_conj {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z : Rn n) :
    gradient (fun u => (infConv (convexConj (pairing n) f) (quadFn (pairing n)) u).toReal) z
      = prox (pairing n) f z :=
  gradient_infConv_convexConj_quadFn hf z

/-- **Section 31** of [rockafellar1970convex]. For a closed proper convex function $f$ on
$\mathbb{R}^n$, the mapping $z \mapsto \operatorname{prox}(z \mid f)$ is continuous.

The mapping is the gradient mapping of the differentiable convex function
$f^* \mathbin{\square} w$, hence continuous (Corollary 25.5.1). This specializes
`ConvexAnalysis.continuous_prox`. -/
theorem prox_continuous {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    Continuous (prox (pairing n) f) :=
  continuous_prox hf

/-- **Section 31** of [rockafellar1970convex], the contraction property of the proximation, which
the book states and proves in the text without a number, and on which Corollary 31.5.2 is built.
For a closed proper convex function $f$ on $\mathbb{R}^n$ and $z_0, z_1 \in \mathbb{R}^n$,
$$|\operatorname{prox}(z_1 \mid f) - \operatorname{prox}(z_0 \mid f)| \le |z_1 - z_0|.$$

With $x_i = \operatorname{prox}(z_i \mid f)$ and $x_i^* = z_i - x_i$, expand $|z_1 - z_0|^2$;
the cross term is non-negative by monotonicity of $\partial f$, so
$|z_1 - z_0|^2 \ge |x_1 - x_0|^2$. -/
theorem prox_contraction {f : Rn n → EReal} (hf : ClosedProperConvexFn f) (z₀ z₁ : Rn n) :
    ‖prox (pairing n) f z₁ - prox (pairing n) f z₀‖ ≤ ‖z₁ - z₀‖ := by
  have h := dist_prox_prox_le (E := Rn n) hf z₁ z₀
  rwa [dist_eq_norm, dist_eq_norm] at h

/-- **Section 31** of [rockafellar1970convex], the contraction property of the proximation as a
Lipschitz bound: for a closed proper convex function $f$ on $\mathbb{R}^n$, the mapping
$z \mapsto \operatorname{prox}(z \mid f)$ is Lipschitz with constant $1$.

This specializes `ConvexAnalysis.lipschitzWith_prox`. -/
theorem prox_lipschitzWith_one {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    LipschitzWith 1 (prox (pairing n) f) :=
  lipschitzWith_prox hf

/-- **Section 31** of [rockafellar1970convex]: "the range of $\operatorname{prox}(\cdot \mid f)$ is
of course $\operatorname{dom} \partial f$". For a closed proper convex function $f$ on
$\mathbb{R}^n$, the range of $z \mapsto \operatorname{prox}(z \mid f)$ is the set of points $x$
with $\partial f(x) \neq \emptyset$.

Each inclusion takes one step: $z - \operatorname{prox}(z \mid f) \in \partial
f(\operatorname{prox}(z \mid f))$ gives $\subseteq$, and a subgradient $y \in \partial f(x)$
gives $x = \operatorname{prox}(x + y \mid f)$. -/
theorem range_prox {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    Set.range (prox (pairing n) f) = {x : Rn n | (subdifferential (pairing n) f x).Nonempty} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z - prox (pairing n) f z, sub_prox_mem_subdifferential hf z⟩
  · rintro ⟨y, hy⟩
    refine ⟨x + y, prox_eq_of_sub_mem_subdifferential hf ?_⟩
    rwa [add_sub_cancel_left]

/-- **Corollary 31.5.1** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$. The mapping $(x, x^*) \mapsto x + x^*$ is a one-to-one mapping of the graph of
$\partial f$ onto $\mathbb{R}^n$ that is continuous in both directions. So the graph of
$\partial f$ is homeomorphic to $\mathbb{R}^n$.

The book states the corollary without proof. A `Homeomorph` is exactly this statement.
Bijectivity is Theorem 31.5, and the continuity of the inverse $z \mapsto (\operatorname{prox}(z
\mid f), z - \operatorname{prox}(z \mid f))$ is `Rockafellar.prox_contraction`. Theorem 24.4 is
not used. The graph of $\partial f$ is `ConvexAnalysis.subgradientRel`. -/
noncomputable def corollary_31_5_1 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    ↥(subgradientRel (pairing n) f) ≃ₜ Rn n :=
  subgradientRelHomeomorph hf

/-- The homeomorphism of Corollary 31.5.1 is the mapping $(x, x^*) \mapsto x + x^*$ of
[rockafellar1970convex]. -/
@[simp] theorem corollary_31_5_1_apply {f : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (p : ↥(subgradientRel (pairing n) f)) : corollary_31_5_1 hf p = p.1.1 + p.1.2 := rfl

/-- The inverse of the homeomorphism of Corollary 31.5.1 is Moreau's decomposition $z \mapsto
(\operatorname{prox}(z \mid f), z - \operatorname{prox}(z \mid f))$. -/
@[simp] theorem corollary_31_5_1_symm_apply {f : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (z : Rn n) :
    (corollary_31_5_1 hf).symm z
      = ⟨(prox (pairing n) f z, z - prox (pairing n) f z), sub_prox_mem_subdifferential hf z⟩ :=
  rfl

/-- **Corollary 31.5.2** of [rockafellar1970convex]. If $f$ is a closed proper convex function on
$\mathbb{R}^n$, then $\partial f$ is a maximal monotone mapping from $\mathbb{R}^n$ to
$\mathbb{R}^n$.

Given $(y, y^*)$ outside the graph of $\partial f$, Theorem 31.5 gives $(x, x^*)$ in the graph
with $x + x^* = y + y^*$, and then $\langle y - x, y^* - x^* \rangle = -|y - x|^2 < 0$. This is
maximality among monotone mappings, not the maximality among cyclically monotone mappings of
Theorem 24.9. The book says explicitly that neither implies the other. -/
theorem corollary_31_5_2 {f : Rn n → EReal} (hf : ClosedProperConvexFn f) :
    IsMaximalMonotoneRel (pairing n) (subgradientRel (pairing n) f) :=
  isMaximalMonotoneRel_subgradientRel hf
/-!
### Theorem 31.2: Fenchel's problem as a convex program

The book presents the Fenchel problem as the convex program of Section 29 for the bifunction
$(Fu)(x) = f(x) - g(Ax + u)$: the perturbation translates the concave function. The theory of
Sections 29 and 30 then applies, and Corollary 31.2.1 is what Theorem 30.4 and Corollary 30.5.2 give
back.
-/

/-- **Theorem 31.2** of [rockafellar1970convex], the Fenchel bifunction. Let
$A : \mathbb{R}^n \to \mathbb{R}^m$ be linear, $f$ a function on $\mathbb{R}^n$ and $g$ a
function on $\mathbb{R}^m$. The **Fenchel bifunction** is the bifunction $F$ from $\mathbb{R}^m$
to $\mathbb{R}^n$ given by
$$(Fu)(x) = f(x) - g(Ax + u).$$
Its program $(P)$ is the Fenchel problem of minimizing $f - gA$, perturbed by a translation of
the concave function. -/
noncomputable def fenchelBifun (A : Rn n →ₗ[ℝ] Rn m) (f : Rn n → EReal) (g : Rn m → EReal) :
    Bifun (Rn m) (Rn n) := fun u x => f x - g (A x + u)

/-- The value of the Fenchel bifunction: $(Fu)(x) = f(x) - g(Ax + u)$. -/
@[simp] theorem fenchelBifun_apply (A : Rn n →ₗ[ℝ] Rn m) (f : Rn n → EReal) (g : Rn m → EReal)
    (u : Rn m) (x : Rn n) : fenchelBifun A f g u x = f x - g (A x + u) := rfl

/-- The linear map $(u, x) \mapsto Ax + u$. The preimage of $-g$ under it is the second summand of
the graph function of the Fenchel bifunction. -/
private def shiftLin (A : Rn n →ₗ[ℝ] Rn m) : (Rn m × Rn n) →ₗ[ℝ] Rn m :=
  A ∘ₗ LinearMap.snd ℝ (Rn m) (Rn n) + LinearMap.fst ℝ (Rn m) (Rn n)

private theorem shiftLin_apply (A : Rn n →ₗ[ℝ] Rn m) (p : Rn m × Rn n) :
    shiftLin A p = A p.2 + p.1 := rfl

/-- The graph function of the Fenchel bifunction is a sum of two preimages under linear maps: $f$
under the projection $(u, x) \mapsto x$, and $-g$ under $(u, x) \mapsto Ax + u$. -/
private theorem graphFn_fenchelBifun (A : Rn n →ₗ[ℝ] Rn m) (f : Rn n → EReal)
    (g : Rn m → EReal) :
    graphFn (fenchelBifun A f g)
      = compLin f (LinearMap.snd ℝ (Rn m) (Rn n)) + compLin (fun w => -(g w)) (shiftLin A) := rfl

/-- **Theorem 31.2** of [rockafellar1970convex], convexity. Let $f$ be a proper convex function on
$\mathbb{R}^n$, $g$ a proper concave function on $\mathbb{R}^m$, and
$A : \mathbb{R}^n \to \mathbb{R}^m$ linear. Then the Fenchel bifunction $F$ is a convex
bifunction. -/
theorem theorem_31_2_convex (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hf : ConvexFn f) (hpf : ProperConvex f) (hg : ConcaveFn g) (hpg : ProperConcave g) :
    ConvexBifun (fenchelBifun A f g) := by
  rw [convexBifun_iff, graphFn_fenchelBifun]
  refine ConvexFn.add (convexFn_compLin _ hf)
    (convexFn_compLin _ (concaveFn_iff_convexFn_neg.1 hg)) (fun p => hpf.ne_bot _) fun p => ?_
  simpa using hpg.ne_top (shiftLin A p)

/-- **Theorem 31.2** of [rockafellar1970convex], properness. Let $f$ be proper on $\mathbb{R}^n$
(finite somewhere and never $-\infty$), $g$ proper on $\mathbb{R}^m$ (finite somewhere and never
$+\infty$), and $A : \mathbb{R}^n \to \mathbb{R}^m$ linear. Then the Fenchel bifunction $F$ is
proper.

**Generalization.** Properness needs no relative-interior hypothesis, only a point of
$\operatorname{dom} f$ and a point of $\operatorname{dom} g$, which the properness of $f$ and
$g$ gives. -/
theorem theorem_31_2_proper (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hpf : ProperConvex f)
        (hpg : ProperConcave g) : ProperConvex (graphFn (fenchelBifun A f g)) := by
  obtain ⟨x₀, hx₀⟩ := hpf.convexDom_nonempty
  obtain ⟨w₀, hw₀⟩ := hpg.concaveDom_nonempty
  refine ⟨⟨(w₀ - A x₀, x₀), ?_⟩, fun p => ?_⟩
  · obtain ⟨a, ha⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hpf.ne_bot x₀) hx₀
    obtain ⟨b, hb⟩ :=
      EReal.exists_coe_of_ne_bot_of_lt_top (ne_of_gt hw₀) (lt_top_iff_ne_top.2 (hpg.ne_top w₀))
    have hA : A x₀ + (w₀ - A x₀) = w₀ := by abel
    have hval : graphFn (fenchelBifun A f g) (w₀ - A x₀, x₀) = ((a - b : ℝ) : EReal) := by
      have hg0 : graphFn (fenchelBifun A f g) (w₀ - A x₀, x₀) = f x₀ - g w₀ := by
        simp only [graphFn, fenchelBifun, hA]
      rw [hg0, ha, hb, ← EReal.coe_sub]
    change graphFn (fenchelBifun A f g) (w₀ - A x₀, x₀) < ⊤
    rw [hval]
    exact EReal.coe_lt_top _
  · exact EReal.add_ne_bot_iff.2 ⟨hpf.ne_bot p.2, by simpa using hpg.ne_top (A p.2 + p.1)⟩

/-- **Theorem 31.2** of [rockafellar1970convex], closedness. Let $f$ be a closed proper convex
function on $\mathbb{R}^n$, $g$ a closed proper concave function on $\mathbb{R}^m$, and
$A : \mathbb{R}^n \to \mathbb{R}^m$ linear. Then the Fenchel bifunction $F$ is closed. -/
theorem theorem_31_2_closed (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hf : ClosedProperConvexFn f) (hg : ClosedProperConcaveFn g) :
    ClosedConvexBifun (fenchelBifun A f g) := by
  have hgn : ClosedProperConvexFn fun w => -(g w) := hg.closedProperConvexFn_neg
  rw [closedConvexBifun_iff, graphFn_fenchelBifun]
  refine (ClosedProperConvexFn.add
    ⟨convexFn_compLin _ hf.convex,
      closedConvex_compLin hf.closed (LinearMap.continuous_of_finiteDimensional _),
      ⟨?_, fun p => hf.proper.ne_bot _⟩⟩
    ⟨convexFn_compLin _ hgn.convex,
      closedConvex_compLin hgn.closed (LinearMap.continuous_of_finiteDimensional _),
      ⟨?_, fun p => hgn.proper.ne_bot _⟩⟩ ?_).closed
  · obtain ⟨x₀, hx₀⟩ := hf.proper.convexDom_nonempty
    exact ⟨(0, x₀), hx₀⟩
  · obtain ⟨w₀, hw₀⟩ := hgn.proper.convexDom_nonempty
    exact ⟨(w₀, 0), by simpa [shiftLin_apply] using hw₀⟩
  · obtain ⟨p, hp⟩ := (theorem_31_2_proper A hf.proper hg.proper).convexDom_nonempty
    exact ⟨p, hp⟩

/-- The linear map $(w, x) \mapsto w - Ax$. Its image of $\operatorname{dom} g \times
\operatorname{dom} f$ is $\operatorname{dom} F$; writing
$\operatorname{dom} g - A(\operatorname{dom} f)$ as one linear image lets Theorem 6.6 and the
product formula for relative interiors apply at once. -/
private def subLin (A : Rn n →ₗ[ℝ] Rn m) : (Rn m × Rn n) →ₗ[ℝ] Rn m :=
  LinearMap.fst ℝ (Rn m) (Rn n) - A ∘ₗ LinearMap.snd ℝ (Rn m) (Rn n)

private theorem subLin_apply (A : Rn n →ₗ[ℝ] Rn m) (p : Rn m × Rn n) :
    subLin A p = p.1 - A p.2 := rfl

private theorem sub_image_eq_subLin_image (A : Rn n →ₗ[ℝ] Rn m) (S : Set (Rn m))
    (T : Set (Rn n)) : S - A '' T = subLin A '' (S ×ˢ T) := by
  ext u
  constructor
  · rintro ⟨w, hw, -, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(w, x), ⟨hw, hx⟩, rfl⟩
  · rintro ⟨⟨w, x⟩, ⟨hw, hx⟩, rfl⟩
    exact ⟨w, hw, A x, ⟨x, hx, rfl⟩, rfl⟩

/-- Theorem 6.6 and Corollary 6.6.2 combined: for convex sets $S$ and $T$, $\operatorname{ri}(S -
AT) = \operatorname{ri} S - A(\operatorname{ri} T)$. The map $(w, x) \mapsto w - Ax$ is defined
on a product, so Theorem 6.6 is used in its backbone form `Convex.relint_image`. -/
private theorem relint_sub_image (A : Rn n →ₗ[ℝ] Rn m) {S : Set (Rn m)} {T : Set (Rn n)}
    (hS : Convex ℝ S) (hT : Convex ℝ T) : ri (S - A '' T) = ri S - A '' ri T := by
  rw [sub_image_eq_subLin_image, sub_image_eq_subLin_image,
    Convex.relint_image (hS.prod hT) (subLin A), intrinsicInterior_prod_eq]

/-- For proper $f$ and $g$, $(Fu)(x) < +\infty$ if and only if $x \in \operatorname{dom} f$ and
$Ax + u \in \operatorname{dom} g$. -/
private theorem fenchelBifun_ne_top_iff {f : Rn n → EReal} {g : Rn m → EReal} (hpf : ProperConvex f)
    (hpg : ProperConcave g) (A : Rn n →ₗ[ℝ] Rn m) (u : Rn m) (x : Rn n) :
    fenchelBifun A f g u x ≠ ⊤ ↔ x ∈ convexDom f ∧ A x + u ∈ concaveDom g := by
  have hb : -(g (A x + u)) ≠ ⊥ := by simpa using hpg.ne_top (A x + u)
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (EReal.add_ne_top_iff_ne_top₂ (hpf.ne_bot x) hb).1 h
    have h2' : g (A x + u) ≠ ⊥ := by simpa using h2
    exact ⟨lt_top_iff_ne_top.2 h1, bot_lt_iff_ne_bot.2 h2'⟩
  · rintro ⟨h1, h2⟩
    refine (EReal.add_ne_top_iff_ne_top₂ (hpf.ne_bot x) hb).2
      ⟨lt_top_iff_ne_top.1 h1, ?_⟩
    simpa using (ne_of_gt h2)

/-- **Theorem 31.2** of [rockafellar1970convex], the optimal value. For all functions $f$ on
$\mathbb{R}^n$, $g$ on $\mathbb{R}^m$ and every linear $A : \mathbb{R}^n \to \mathbb{R}^m$, the
optimal value of the program of the Fenchel bifunction is the Fenchel infimum:
$$(\inf F)(0) = \inf_x \{f(x) - g(Ax)\}.$$
-/
theorem theorem_31_2_infBifun (A : Rn n →ₗ[ℝ] Rn m) (f : Rn n → EReal) (g : Rn m → EReal) :
    infBifun (fenchelBifun A f g) 0 = ⨅ x, f x - g (A x) :=
  iInf_congr fun x => by rw [fenchelBifun_apply, add_zero]

/-- **Theorem 31.2** of [rockafellar1970convex], the effective domain. Let $f$ be proper on
$\mathbb{R}^n$ (finite somewhere and never $-\infty$), $g$ proper on $\mathbb{R}^m$ (finite
somewhere and never $+\infty$), and $A : \mathbb{R}^n \to \mathbb{R}^m$ linear. Then the
effective domain of the Fenchel bifunction is
$$\operatorname{dom} F = \operatorname{dom} g - A(\operatorname{dom} f).$$
-/
theorem theorem_31_2_domBifun (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hpf : ProperConvex f) (hpg : ProperConcave g) :
    convexDomBifun (fenchelBifun A f g) = concaveDom g - A '' convexDom f := by
  rw [sub_image_eq_subLin_image]
  ext u
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hx1, hx2⟩ := (fenchelBifun_ne_top_iff hpf hpg A u x).1 hx
    refine ⟨(A x + u, x), ⟨hx2, hx1⟩, ?_⟩
    change A x + u - A x = u
    abel
  · rintro ⟨⟨w, x⟩, ⟨hw, hx⟩, rfl⟩
    refine ⟨x, (fenchelBifun_ne_top_iff hpf hpg A _ x).2 ⟨hx, ?_⟩⟩
    have hAx : A x + subLin A (w, x) = w := by change A x + (w - A x) = w; abel
    rwa [hAx]

/-- **Theorem 31.2** of [rockafellar1970convex], the relative interior of the effective domain. Let
$f$ be a proper convex function on $\mathbb{R}^n$, $g$ a proper concave function on
$\mathbb{R}^m$, and $A : \mathbb{R}^n \to \mathbb{R}^m$ linear. Then
$$\operatorname{ri}(\operatorname{dom} F) = \operatorname{ri}(\operatorname{dom} g) -
  A(\operatorname{ri}(\operatorname{dom} f)).$$

The proof uses Theorem 6.6 and Corollary 6.6.2. -/
theorem theorem_31_2_relint_domBifun (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hf : ConvexFn f) (hpf : ProperConvex f) (hg : ConcaveFn g) (hpg : ProperConcave g) :
    ri (convexDomBifun (fenchelBifun A f g)) = ri (concaveDom g) - A '' ri (convexDom f) := by
  rw [theorem_31_2_domBifun A hpf hpg,
    relint_sub_image A hg.convex_concaveDom hf.convex_convexDom]

/-- **Theorem 31.2** of [rockafellar1970convex], strong consistency. Let $f$ be a proper convex
function on $\mathbb{R}^n$, $g$ a proper concave function on $\mathbb{R}^m$, and
$A : \mathbb{R}^n \to \mathbb{R}^m$ linear. The program of the Fenchel bifunction is strongly
consistent if and only if some $x \in \operatorname{ri}(\operatorname{dom} f)$ has
$Ax \in \operatorname{ri}(\operatorname{dom} g)$. This is condition (a) of Corollary 31.2.1 in
the form of a program. -/
theorem theorem_31_2_stronglyConsistent_iff (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal}
    {g : Rn m → EReal} (hf : ConvexFn f) (hpf : ProperConvex f) (hg : ConcaveFn g)
    (hpg : ProperConcave g) :
    StronglyConsistent (fenchelBifun A f g) ↔ ∃ x ∈ ri (convexDom f), A x ∈ ri (concaveDom g) := by
  have key : ri (convexDomBifun (fenchelBifun A f g))
      = subLin A '' (ri (concaveDom g) ×ˢ ri (convexDom f)) := by
    rw [theorem_31_2_relint_domBifun A hf hpf hg hpg, sub_image_eq_subLin_image]
  have h0 : StronglyConsistent (fenchelBifun A f g)
      ↔ (0 : Rn m) ∈ subLin A '' (ri (concaveDom g) ×ˢ ri (convexDom f)) := by
    change (0 : Rn m) ∈ ri (convexDomBifun (fenchelBifun A f g)) ↔ _
    rw [key]
  rw [h0]
  constructor
  · rintro ⟨⟨w, x⟩, ⟨hw, hx⟩, hz⟩
    have hz' : w - A x = 0 := hz
    exact ⟨x, hx, (sub_eq_zero.1 hz') ▸ hw⟩
  · rintro ⟨x, hx, hAx⟩
    refine ⟨(A x, x), ⟨hAx, hx⟩, ?_⟩
    change A x - A x = 0
    exact sub_self _

/-- For $a, b \in [-\infty, +\infty]$ and $P, K \in \mathbb{R}$,
$a - b + (P - K) = (P - b) + (a - K)$. This regroups the five terms of the third display of the
book; no finiteness is needed. -/
private theorem ereal_regroup (a b : EReal) (P K : ℝ) :
    a - b + ((P - K : ℝ) : EReal) = ((P : ℝ) : EReal) - b + (a - ((K : ℝ) : EReal)) := by
  rw [EReal.coe_sub, sub_eq_add_neg a b, sub_eq_add_neg ((P : ℝ) : EReal) ((K : ℝ) : EReal),
    sub_eq_add_neg ((P : ℝ) : EReal) b, sub_eq_add_neg a ((K : ℝ) : EReal)]
  simp only [add_comm, add_left_comm, add_assoc]

/-- The substitution $y = Ax + u$ of the book, as a bijection of $\mathbb{R}^m \times \mathbb{R}^n$.
-/
private def shiftEquiv (A : Rn n →ₗ[ℝ] Rn m) : (Rn m × Rn n) ≃ (Rn m × Rn n) where
  toFun q := (q.1 - A q.2, q.2)
  invFun p := (A p.2 + p.1, p.2)
  left_inv := by rintro ⟨w, x⟩; simp
  right_inv := by rintro ⟨u, x⟩; simp

/-- **Theorem 31.2** of [rockafellar1970convex], the adjoint. Let $f$ be proper on $\mathbb{R}^n$
(finite somewhere and never $-\infty$), $g$ proper on $\mathbb{R}^m$ (finite somewhere and never
$+\infty$), and $A : \mathbb{R}^n \to \mathbb{R}^m$ linear. Then the adjoint of the Fenchel
bifunction is
$$(F^* x^*)(u^*) = g^*(u^*) - f^*(A^* u^* + x^*)$$
for all $x^* \in \mathbb{R}^n$ and $u^* \in \mathbb{R}^m$.

The adjoint is `Rockafellar.dualProgram`, which is `ConvexAnalysis.convexAdjointBifun` at the
two Euclidean pairings. -/
theorem theorem_31_2_adjoint (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hpf : ProperConvex f) (hpg : ProperConcave g) (y : Rn n) (v : Rn m) :
    convexAdjointBifun (pairing m) (pairing n) (fenchelBifun A f g) y v
      = concaveConj (pairing m) g v - convexConj (pairing n) f (LinearMap.adjoint A v + y) := by
  obtain ⟨x₀, hx₀⟩ := hpf.convexDom_nonempty
  obtain ⟨w₀, hw₀⟩ := hpg.concaveDom_nonempty
  obtain ⟨fa, hfa⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hpf.ne_bot x₀) hx₀
  obtain ⟨gb, hgb⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (ne_of_gt hw₀) (lt_top_iff_ne_top.2 (hpg.ne_top w₀))
  have hpair : ∀ (x : Rn n) (w : Rn m),
      (pairing m (w - A x) v - pairing n x y : ℝ)
        = (pairing m w v : ℝ) - (pairing n x (LinearMap.adjoint A v + y) : ℝ) := by
    intro x w
    have hA : (pairing m (A x) v : ℝ) = (pairing n x (LinearMap.adjoint A v) : ℝ) :=
      isAdjointPair_adjoint A x v
    simp only [map_sub, LinearMap.sub_apply, map_add, hA]
    ring
  have hsplit : convexAdjointBifun (pairing m) (pairing n) (fenchelBifun A f g) y v
      = ⨅ q : Rn m × Rn n,
          ((((pairing m q.1 v : ℝ) : EReal) - g q.1)
            + (f q.2 - ((pairing n q.2 (LinearMap.adjoint A v + y) : ℝ) : EReal))) := by
    rw [convexAdjointBifun_apply, ← (shiftEquiv A).iInf_comp]
    refine iInf_congr fun q => ?_
    obtain ⟨w, x⟩ := q
    have hAx : A x + (w - A x) = w := by abel
    have h1 : fenchelBifun A f g (w - A x) x = f x - g w := by
      rw [fenchelBifun_apply, hAx]
    change fenchelBifun A f g (w - A x) x
        + ((pairing m (w - A x) v - pairing n x y : ℝ) : EReal)
      = (((pairing m w v : ℝ) : EReal) - g w)
        + (f x - ((pairing n x (LinearMap.adjoint A v + y) : ℝ) : EReal))
    rw [h1, hpair x w]
    exact ereal_regroup (f x) (g w) _ _
  have hb1 : ((pairing m w₀ v : ℝ) : EReal) - g w₀ ≠ ⊤ := by
    rw [hgb, ← EReal.coe_sub]; exact EReal.coe_ne_top _
  have hb3 : f x₀ - ((pairing n x₀ (LinearMap.adjoint A v + y) : ℝ) : EReal) ≠ ⊤ := by
    rw [hfa, ← EReal.coe_sub]; exact EReal.coe_ne_top _
  have ht1 : (⨅ w : Rn m, (((pairing m w v : ℝ) : EReal) - g w)) ≠ ⊤ := by
    intro hcon
    exact hb1 (top_le_iff.1 (by rw [← hcon]; exact iInf_le _ w₀))
  have ht2 : (⨅ x : Rn n, (f x - ((pairing n x (LinearMap.adjoint A v + y) : ℝ) : EReal)))
      ≠ ⊤ := by
    intro hcon
    exact hb3 (top_le_iff.1 (by rw [← hcon]; exact iInf_le _ x₀))
  have hsp := EReal.iInf_prod_add
      (fun w : Rn m => (((pairing m w v : ℝ) : EReal) - g w))
      (fun x : Rn n => f x - ((pairing n x (LinearMap.adjoint A v + y) : ℝ) : EReal)) ht1 ht2
  have hc1 : (⨅ w : Rn m, (((pairing m w v : ℝ) : EReal) - g w))
      = concaveConj (pairing m) g v := rfl
  have hc2 : (⨅ x : Rn n, (f x - ((pairing n x (LinearMap.adjoint A v + y) : ℝ) : EReal)))
      = -(convexConj (pairing n) f (LinearMap.adjoint A v + y)) := by
    rw [convexConj_apply, EReal.neg_iSup]
    exact (iInf_congr fun x => EReal.neg_coe_sub _ _).symm
  rw [hsplit, hsp, hc1, hc2, ← sub_eq_add_neg]

/-- **Theorem 31.2** of [rockafellar1970convex], the optimal value of the dual program. Let $f$ be
proper on $\mathbb{R}^n$ (finite somewhere and never $-\infty$), $g$ proper on $\mathbb{R}^m$
(finite somewhere and never $+\infty$), and $A : \mathbb{R}^n \to \mathbb{R}^m$ linear. Then
$$\sup F^* 0 = \sup_{u^*} \{g^*(u^*) - f^*(A^* u^*)\}.$$
-/
theorem theorem_31_2_supBifun_adjoint (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hpf : ProperConvex f) (hpg : ProperConcave g) :
    supBifun (convexAdjointBifun (pairing m) (pairing n) (fenchelBifun A f g)) 0
      = ⨆ v, concaveConj (pairing m) g v - convexConj (pairing n) f (LinearMap.adjoint A v) :=
  iSup_congr fun v => by rw [theorem_31_2_adjoint A hpf hpg 0 v, add_zero]

/-- For proper $f$ and $g$, $(F^* x^*)(u^*) > -\infty$ if and only if
$u^* \in \operatorname{dom} g^*$ and $A^* u^* + x^* \in \operatorname{dom} f^*$. -/
private theorem convexAdjointBifun_fenchelBifun_ne_bot_iff (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal}
    {g : Rn m → EReal} (hpf : ProperConvex f) (hpg : ProperConcave g) (y : Rn n) (v : Rn m) :
    convexAdjointBifun (pairing m) (pairing n) (fenchelBifun A f g) y v ≠ ⊥
      ↔ v ∈ concaveDom (concaveConj (pairing m) g)
        ∧ LinearMap.adjoint A v + y ∈ convexDom (convexConj (pairing n) f) := by
  rw [theorem_31_2_adjoint A hpf hpg y v, sub_eq_add_neg]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := EReal.add_ne_bot_iff.1 h
    have h2' : convexConj (pairing n) f (LinearMap.adjoint A v + y) ≠ ⊤ := by simpa using h2
    exact ⟨bot_lt_iff_ne_bot.2 h1, lt_top_iff_ne_top.2 h2'⟩
  · rintro ⟨h1, h2⟩
    refine EReal.add_ne_bot_iff.2 ⟨ne_of_gt h1, ?_⟩
    simpa using (lt_top_iff_ne_top.1 h2)

/-- **Theorem 31.2** of [rockafellar1970convex], the effective domain of the adjoint. Let $f$ be
proper on $\mathbb{R}^n$ (finite somewhere and never $-\infty$), $g$ proper on $\mathbb{R}^m$
(finite somewhere and never $+\infty$), and $A : \mathbb{R}^n \to \mathbb{R}^m$ linear. Then the
effective domain of the concave bifunction $F^*$ is
$$\operatorname{dom} F^* = \operatorname{dom} f^* - A^*(\operatorname{dom} g^*).$$
This mirrors `Rockafellar.theorem_31_2_domBifun`. -/
theorem theorem_31_2_domConcaveBifun_adjoint (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal}
    {g : Rn m → EReal} (hpf : ProperConvex f) (hpg : ProperConcave g) :
    concaveDomBifun (convexAdjointBifun (pairing m) (pairing n) (fenchelBifun A f g))
      = convexDom (convexConj (pairing n) f)
        - LinearMap.adjoint A '' concaveDom (concaveConj (pairing m) g) := by
  rw [sub_image_eq_subLin_image]
  ext y
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨h1, h2⟩ := (convexAdjointBifun_fenchelBifun_ne_bot_iff A hpf hpg y v).1 hv
    refine ⟨(LinearMap.adjoint A v + y, v), ⟨h2, h1⟩, ?_⟩
    change LinearMap.adjoint A v + y - LinearMap.adjoint A v = y
    abel
  · rintro ⟨⟨w, v⟩, ⟨hw, hv⟩, rfl⟩
    refine ⟨v, (convexAdjointBifun_fenchelBifun_ne_bot_iff A hpf hpg _ v).2 ⟨hv, ?_⟩⟩
    have hz : LinearMap.adjoint A v + subLin (LinearMap.adjoint A) (w, v) = w := by
      change LinearMap.adjoint A v + (w - LinearMap.adjoint A v) = w
      abel
    rwa [hz]

/-- **Theorem 31.2** of [rockafellar1970convex], strong consistency of the dual. Let $f$ be proper
on $\mathbb{R}^n$ (finite somewhere and never $-\infty$), $g$ proper on $\mathbb{R}^m$ (finite
somewhere and never $+\infty$), and $A : \mathbb{R}^n \to \mathbb{R}^m$ linear. The dual program
is strongly consistent if and only if some $u^* \in \operatorname{ri}(\operatorname{dom} g^*)$
has $A^* u^* \in \operatorname{ri}(\operatorname{dom} f^*)$. This is condition (b) of Corollary
31.2.1 in the form of a program. -/
theorem theorem_31_2_concaveStronglyConsistent_iff (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal}
    {g : Rn m → EReal} (hpf : ProperConvex f) (hpg : ProperConcave g) :
    ConcaveStronglyConsistent (convexAdjointBifun (pairing m) (pairing n) (fenchelBifun A f g))
      ↔ ∃ v ∈ ri (concaveDom (concaveConj (pairing m) g)),
          LinearMap.adjoint A v ∈ ri (convexDom (convexConj (pairing n) f)) := by
  have hcf : Convex ℝ (convexDom (convexConj (pairing n) f)) :=
      (convexFn_convexConj (pairing n) f).convex_convexDom
  have hcg : Convex ℝ (concaveDom (concaveConj (pairing m) g)) :=
    (concaveFn_concaveConj (pairing m) g).convex_concaveDom
  have key : ri (concaveDomBifun (convexAdjointBifun (pairing m) (pairing n) (fenchelBifun A f g)))
      = subLin (LinearMap.adjoint A)
          '' (ri (convexDom (convexConj (pairing n) f))
            ×ˢ ri (concaveDom (concaveConj (pairing m) g))) := by
    rw [theorem_31_2_domConcaveBifun_adjoint A hpf hpg,
      relint_sub_image (LinearMap.adjoint A) hcf hcg, sub_image_eq_subLin_image]
  have h0 :
      ConcaveStronglyConsistent (convexAdjointBifun (pairing m) (pairing n) (fenchelBifun A f g))
      ↔ (0 : Rn n) ∈ subLin (LinearMap.adjoint A)
          '' (ri (convexDom (convexConj (pairing n) f))
            ×ˢ ri (concaveDom (concaveConj (pairing m) g))) := by
    change (0 : Rn n)
      ∈ ri (concaveDomBifun (convexAdjointBifun (pairing m) (pairing n) (fenchelBifun A f g))) ↔ _
    rw [key]
  rw [h0]
  constructor
  · rintro ⟨⟨w, v⟩, ⟨hw, hv⟩, hz⟩
    have hz' : w - LinearMap.adjoint A v = 0 := hz
    exact ⟨v, hv, (sub_eq_zero.1 hz') ▸ hw⟩
  · rintro ⟨v, hv, hAv⟩
    refine ⟨(LinearMap.adjoint A v, v), ⟨hAv, hv⟩, ?_⟩
    change LinearMap.adjoint A v - LinearMap.adjoint A v = 0
    exact sub_self _

/-- **Corollary 31.2.1** of [rockafellar1970convex], condition (b). Let $f$ be a closed proper
convex function on $\mathbb{R}^n$, $g$ a closed proper concave function on $\mathbb{R}^m$, and
$A : \mathbb{R}^n \to \mathbb{R}^m$ linear. If some $u^* \in
\operatorname{ri}(\operatorname{dom} g^*)$ has $A^* u^* \in \operatorname{ri}(\operatorname{dom}
f^*)$, then
$$\inf_x \{f(x) - g(Ax)\} = \sup_{u^*} \{g^*(u^*) - f^*(A^* u^*)\}.$$

The proof is Theorem 31.2 followed by Theorem 30.4(b) and Theorem 30.3. -/
theorem corollary_31_2_1_b (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hf : ClosedProperConvexFn f) (hg : ClosedProperConcaveFn g) {v₀ : Rn m}
    (hv : v₀ ∈ ri (concaveDom (concaveConj (pairing m) g)))
    (hAv : LinearMap.adjoint A v₀ ∈ ri (convexDom (convexConj (pairing n) f))) :
    (⨅ x, f x - g (A x))
      = ⨆ v : Rn m,
          concaveConj (pairing m) g v - convexConj (pairing n) f (LinearMap.adjoint A v) := by
  have hF : ConvexBifun (fenchelBifun A f g) :=
    theorem_31_2_convex A hf.convex hf.proper hg.concave hg.proper
  have hcl : ClosedConvexBifun (fenchelBifun A f g) := theorem_31_2_closed A hf hg
  have hs : ConcaveStronglyConsistent
      (convexAdjointBifun (pairing m) (pairing n) (fenchelBifun A f g)) :=
    (theorem_31_2_concaveStronglyConsistent_iff A hf.proper hg.proper).2 ⟨v₀, hv, hAv⟩
  have hnorm : Normal (fenchelBifun A f g) :=
    normal_of_concaveStronglyConsistent_convexAdjointBifun hF hcl hs
  have hgap := (normal_iff_iSup_convexAdjointBifun_eq (Bu := pairing m) (pairing n) hF).1 hnorm
  rw [← theorem_31_2_infBifun A f g, ← hgap]
  exact theorem_31_2_supBifun_adjoint A hf.proper hg.proper

/-- **Corollary 31.2.1** of [rockafellar1970convex], attainment under (b). Under the hypotheses of
`Rockafellar.corollary_31_2_1_b`, the infimum $\inf_x \{f(x) - g(Ax)\}$ is attained at some $x$. -/
theorem corollary_31_2_1_b_attained (A : Rn n →ₗ[ℝ] Rn m) {f : Rn n → EReal} {g : Rn m → EReal}
    (hf : ClosedProperConvexFn f) (hg : ClosedProperConcaveFn g) {v₀ : Rn m}
    (hv : v₀ ∈ ri (concaveDom (concaveConj (pairing m) g)))
    (hAv : LinearMap.adjoint A v₀ ∈ ri (convexDom (convexConj (pairing n) f))) :
    ∃ x, f x - g (A x) = ⨅ z, f z - g (A z) := by
  have hF : ConvexBifun (fenchelBifun A f g) :=
    theorem_31_2_convex A hf.convex hf.proper hg.concave hg.proper
  have hcl : ClosedConvexBifun (fenchelBifun A f g) := theorem_31_2_closed A hf hg
  have hs : ConcaveStronglyConsistent
      (convexAdjointBifun (pairing m) (pairing n) (fenchelBifun A f g)) :=
    (theorem_31_2_concaveStronglyConsistent_iff A hf.proper hg.proper).2 ⟨v₀, hv, hAv⟩
  have hinf : infBifun (fenchelBifun A f g) 0 = ⨅ x, f x - g (A x) :=
    theorem_31_2_infBifun A f g
  by_cases hc : Consistent (fenchelBifun A f g)
  · have hnorm : Normal (fenchelBifun A f g) :=
      normal_of_concaveStronglyConsistent_convexAdjointBifun hF hcl hs
    have hgap : (⨆ v, convexAdjointBifun (pairing m) (pairing n) (fenchelBifun A f g) 0 v)
        = infBifun (fenchelBifun A f g) 0 :=
      (normal_iff_iSup_convexAdjointBifun_eq (Bu := pairing m) (pairing n) hF).1 hnorm
    have hv0 : convexAdjointBifun (pairing m) (pairing n) (fenchelBifun A f g) 0 v₀ ≠ ⊥ := by
      refine (convexAdjointBifun_fenchelBifun_ne_bot_iff A hf.proper hg.proper 0 v₀).2
        ⟨intrinsicInterior_subset hv, ?_⟩
      rw [add_zero]
      exact intrinsicInterior_subset hAv
    have hbot : infBifun (fenchelBifun A f g) 0 ≠ ⊥ := by
      rw [← hgap]
      intro h
      exact hv0 (le_bot_iff.1 (h ▸ le_iSup
        (fun v => convexAdjointBifun (pairing m) (pairing n) (fenchelBifun A f g) 0 v) v₀))
    obtain ⟨x, hx⟩ := exists_infBifun_eq_of_concaveStronglyConsistent (Bu := pairing m)
      (Bx := pairing n) hF hcl hc hbot hs
    refine ⟨x, ?_⟩
    rw [← hinf, ← hx, fenchelBifun_apply, add_zero]
  · have h1 : ∀ x : Rn n, f x - g (A x) = ⊤ := by
      intro x
      by_contra hx
      refine hc ⟨x, ?_⟩
      rw [fenchelBifun_apply, add_zero]
      exact hx
    refine ⟨0, ?_⟩
    rw [h1 0]
    simp only [h1, iInf_const]

end Rockafellar
