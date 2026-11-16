/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: beside `Mathlib.Topology.MetricSpace.Holder` and
`Mathlib.Topology.ContinuousMap.Bounded.Basic`, as the Hölder spaces `C^{k,β}`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Holder
import Numlib.Analysis.Calculus.ContDiffOnClosure
import Numlib.Analysis.Normed.Operator.Embedding

/-!
# The Hölder spaces $C^{j,\beta}(\overline{\Omega})$

Let $\Omega$ be an open set of a real normed space $E$, let $F$ be a real normed space, let
$j \in \mathbb{N}$, and let $\beta \ge 0$ be an exponent. The Hölder space
$C^{j,\beta}(\overline{\Omega})$ consists of the functions $f : \Omega \to F$ of class $C^j$ whose
derivatives $D^i f$, $i \le j$, extend to bounded continuous functions on $\overline{\Omega}$, and
whose top derivative $D^j f$ is $\beta$-Hölder continuous. Its norm is
$$\|f\| = \sum_{i \le j} \|D^i f\|_\infty + [D^j f]_\beta, \qquad [g]_\beta = \sup_{x \neq y}
  \frac{\|g(x) - g(y)\|}{\|x - y\|^\beta}.$$
This is the space of [han2009theoretical], §1.4.1, and the target of the Sobolev embedding
$W^{k,p}(\Omega) \hookrightarrow C^{j,\beta}(\overline{\Omega})$ of Theorem 7.3.7 (c) there.

The module proves that $C^{j,\beta}(\overline{\Omega})$ is a Banach space, that it embeds
continuously in the bounded continuous functions on $\overline{\Omega}$ and in
$C^{j,\beta'}(\overline{\Omega})$ for $\beta' \le \beta$ on a bounded $\Omega$, and that the second
embedding is compact for $0 < \beta' < \beta$ when $E$ and $F$ are finite-dimensional and the
derivatives of order less than $j$ are uniformly Hölder.

## Main definitions

* `holderSeminorm`: the Hölder seminorm $[g]_\beta$.
* `HolderSpace`, with `HolderSpace.deriv u i` the extension of the $i$-th derivative and `⇑u` the
  function on the closure: the Hölder space $C^{j,\beta}(\overline{\Omega})$.
* `HolderSpace.toBCFL`: the inclusion of $C^{j,\beta}(\overline{\Omega})$ in the bounded continuous
  functions on $\overline{\Omega}$, a bounded linear map of norm at most $1$.
* `HolderSpace.toLowerL`: the inclusion $C^{j,\beta}(\overline{\Omega}) \to
  C^{j,\beta'}(\overline{\Omega})$ for $\beta' \le \beta$ on a bounded $\Omega$, a bounded linear
  map.
* `HolderSpace.mk'`: the element of $C^{j,\beta}(\overline{\Omega})$ given by a $C^j$ function on
  $\Omega$ whose derivatives have bounded continuous extensions to $\overline{\Omega}$, the top one
  Hölder.

## Main results

* `HolderSpace.instNormedAddCommGroup`, `HolderSpace.instNormedSpaceReal`,
  `HolderSpace.instCompleteSpace`: $C^{j,\beta}(\overline{\Omega})$ is a Banach space when $F$ is
  complete ([han2009theoretical], §1.4.1).
* `HolderSpace.exists_subseq_tendsto_toLower`: the **Arzelà–Ascoli theorem with Hölder
  interpolation**. For a bounded $\Omega$ in a finite-dimensional $E$, with $F$ finite-dimensional,
  a bounded sequence of $C^{j,\beta}(\overline{\Omega})$ whose derivatives of order less than $j$
  are uniformly Hölder has a subsequence that converges in $C^{j,\beta'}(\overline{\Omega})$, for
  $0 < \beta' < \beta$.
* `HolderSpace.isCompactEmbedding_toLowerL`, `HolderSpace.isCompactEmbedding_toLowerL_comp`: the
  compact embedding $C^{j,\beta}(\overline{\Omega}) \hookrightarrow\hookrightarrow
  C^{j,\beta'}(\overline{\Omega})$ for $0 < \beta' < \beta$, if the derivatives of order less than
  $j$ are uniformly Hölder with constants proportional to the norm.
* `HolderSpace.isCompactEmbedding_toLowerL_zero`: the compact embedding for $j = 0$, without further
  conditions.

## Implementation notes

* An element is represented by the tuple $(G_0, \dots, G_j)$ of the continuous extensions of its
  derivatives, with $G_i$ a bounded continuous function on $\overline{\Omega}$ with values in the
  $i$-linear maps $E^i \to F$. The tuple must satisfy two conditions: there is a function
  $f : E \to F$ of class $C^j$ on $\Omega$ with $G_i = D^i f$ on $\Omega$
  (`HolderSpace.IsDerivTuple`), and $G_j$ is $\beta$-Hölder. As for the one-dimensional space
  $C^k[a, b]$ of `Numlib.Analysis.Calculus.ContDiffMapIcc`, the extensions are carried and not the
  function. A function on $E$ has values off $\overline{\Omega}$ that the space
  $C^{j,\beta}(\overline{\Omega})$ does not see, so with the function the norm would only be a
  seminorm. The extensions also give a meaning to the values of the derivatives on the boundary.
* The tuple is determined by its zeroth entry on $\Omega$ (`HolderSpace.ext_of_eqOn`). Therefore a
  map into the space that is specified on representatives, such as a Sobolev embedding, is linear.
* `holderSeminorm` is a real supremum. It is $0$ on a function that is not Hölder, because the
  supremum of an unbounded family of reals is $0$ in Mathlib. Each statement about it has the Hölder
  hypothesis that makes the supremum the true one.
* The norm is equivalent to the norm of [han2009theoretical], §1.4.1, but not equal to it. The
  source takes the maximum of the sup norms, where this module takes their sum. The source sums the
  Hölder seminorms of the partial derivatives of order $j$, where this module takes the Hölder
  seminorm of the full $j$-th Fréchet derivative.
* The exponent $\beta$ is any element of `ℝ≥0`. The source takes $\beta \in (0, 1]$.
* For $j \ge 1$ the compact embedding needs a condition on the derivatives of order less than $j$.
  On a general bounded open set, a function with bounded gradient need not be uniformly continuous
  up to the boundary (for example, in a spiralling corridor). So the compact embedding is not a
  theorem about arbitrary bounded open sets with this norm, in which only the top derivative is
  Hölder. The condition is empty for $j = 0$. It holds on a convex $\Omega$ by the mean value
  inequality, which this module does not prove. On Sobolev extension domains, Morrey's theorem
  supplies it (`Numlib.Analysis.Sobolev.HolderEmbedding`).
-/

open Filter Metric Set TopologicalSpace

open scoped BoundedContinuousFunction NNReal Topology

noncomputable section

/-! ### The Hölder seminorm -/

section HolderSeminorm

variable {X F : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup F]

/-- The **Hölder seminorm** of a function $g : X \to F$ on a pseudometric space with exponent
$\beta \in \mathbb{R}$:
$$[g]_\beta = \sup_{x, y \in X} \frac{\|g(x) - g(y)\|}{d(x, y)^\beta}.$$

This is the seminorm of [han2009theoretical], §1.4.1. The quotient is $0$ where $d(x, y) = 0$,
because division by $0$ gives $0$; so the pairs with $x = y$ contribute $0$. As a real supremum,
$[g]_\beta$ is $0$ if the family of quotients is not bounded above, for example if $g$ is not
$\beta$-Hölder, and it is $0$ if $X$ is empty. -/
def holderSeminorm (β : ℝ) (g : X → F) : ℝ :=
  ⨆ p : X × X, ‖g p.1 - g p.2‖ / dist p.1 p.2 ^ β

/-- The Hölder seminorm is nonnegative. -/
theorem holderSeminorm_nonneg (β : ℝ) (g : X → F) : 0 ≤ holderSeminorm β g :=
  Real.iSup_nonneg fun _ ↦ div_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _)

/-- A Hölder bound bounds the seminorm: if $C \ge 0$ and $\|g(x) - g(y)\| \le C \, d(x, y)^\beta$
for all $x, y \in X$, then $[g]_\beta \le C$. -/
theorem holderSeminorm_le {β C : ℝ} {g : X → F} (hC : 0 ≤ C)
    (h : ∀ x y, ‖g x - g y‖ ≤ C * dist x y ^ β) : holderSeminorm β g ≤ C :=
  Real.iSup_le (fun p ↦ div_le_of_le_mul₀ (Real.rpow_nonneg dist_nonneg _) hC (h p.1 p.2)) hC

/-- If $g$ is $\beta$-Hölder with constant $C$ (`HolderWith C β g`), then $[g]_\beta \le C$. -/
theorem HolderWith.holderSeminorm_le {C β : ℝ≥0} {g : X → F} (h : HolderWith C β g) :
    holderSeminorm β g ≤ C :=
  _root_.holderSeminorm_le C.coe_nonneg fun x y ↦ by simpa only [dist_eq_norm] using h.dist_le x y

/-- If $g$ is $\beta$-Hölder, then the quotients $\|g(x) - g(y)\| / d(x, y)^\beta$, $x, y \in X$,
are bounded above. -/
theorem HolderWith.bddAbove_holderQuotient {C β : ℝ≥0} {g : X → F} (h : HolderWith C β g) :
    BddAbove (range fun p : X × X ↦ ‖g p.1 - g p.2‖ / dist p.1 p.2 ^ (β : ℝ)) :=
  ⟨C, forall_mem_range.2 fun p ↦ div_le_of_le_mul₀ (Real.rpow_nonneg dist_nonneg _) C.coe_nonneg
    (by simpa only [dist_eq_norm] using h.dist_le p.1 p.2)⟩

/-- The **seminorm is a Hölder constant**. If $g$ is $\beta$-Hölder with some constant, then for all
$x, y \in X$
$$\|g(x) - g(y)\| \le [g]_\beta \, d(x, y)^\beta.$$
-/
theorem norm_sub_le_holderSeminorm_mul {β : ℝ≥0} {g : X → F}
    (h : ∃ C : ℝ≥0, HolderWith C β g) (x y : X) :
    ‖g x - g y‖ ≤ holderSeminorm β g * dist x y ^ (β : ℝ) := by
  obtain ⟨C, hC⟩ := h
  rcases (Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) (β : ℝ)).eq_or_lt with hxy | hd
  · have h0 : ‖g x - g y‖ ≤ 0 := by
      have := hC.dist_le x y
      rwa [← hxy, mul_zero, dist_eq_norm] at this
    rw [← hxy, mul_zero]
    exact h0
  · rw [← div_le_iff₀ hd]
    exact le_ciSup hC.bddAbove_holderQuotient (x, y)

/-- If $d(g(x), g(y)) \le C \, d(x, y)^\beta$ for all $x, y \in X$, with $C, \beta \ge 0$, then $g$
is $\beta$-Hölder with constant $C$ (`HolderWith C β g`). -/
theorem holderWith_of_dist_le {C β : ℝ≥0} {g : X → F}
    (h : ∀ x y, dist (g x) (g y) ≤ C * dist x y ^ (β : ℝ)) : HolderWith C β g := fun x y ↦ by
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg β.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x y)

/-- If $d(g(x), g(y)) \le C \, d(x, y)^\beta$ for all $x, y$ in a set $s \subseteq X$, with
$C, \beta \ge 0$, then $g$ is $\beta$-Hölder on $s$ with constant $C$ (`HolderOnWith C β g s`). -/
theorem holderOnWith_of_dist_le {C β : ℝ≥0} {g : X → F} {s : Set X}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (g x) (g y) ≤ C * dist x y ^ (β : ℝ)) :
    HolderOnWith C β g s := fun x hx y hy ↦ by
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg β.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

/-- If $g$ is $\beta$-Hölder with some constant, then $g$ is $\beta$-Hölder with the constant
$[g]_\beta$. -/
theorem holderWith_holderSeminorm {β : ℝ≥0} {g : X → F} (h : ∃ C : ℝ≥0, HolderWith C β g) :
    HolderWith ⟨holderSeminorm β g, holderSeminorm_nonneg _ _⟩ β g :=
  holderWith_of_dist_le fun x y ↦ by
    rw [dist_eq_norm]
    exact norm_sub_le_holderSeminorm_mul h x y

/-- The Hölder seminorm of the zero function is $0$. -/
@[simp]
theorem holderSeminorm_zero (β : ℝ) : holderSeminorm β (0 : X → F) = 0 :=
  le_antisymm (Real.iSup_le (fun p ↦ by simp) le_rfl) (holderSeminorm_nonneg _ _)

/-- The Hölder seminorm of $-g$ equals that of $g$. -/
theorem holderSeminorm_neg (β : ℝ) (g : X → F) : holderSeminorm β (-g) = holderSeminorm β g := by
  simp only [holderSeminorm, Pi.neg_apply, neg_sub_neg, norm_sub_rev]

/-- The Hölder seminorm is absolutely homogeneous: for a real normed space $F$ and
$c \in \mathbb{R}$, $[c g]_\beta = |c| \, [g]_\beta$. -/
theorem holderSeminorm_smul [NormedSpace ℝ F] (β : ℝ) (c : ℝ) (g : X → F) :
    holderSeminorm β (c • g) = |c| * holderSeminorm β g := by
  simp only [holderSeminorm, Pi.smul_apply, ← smul_sub, norm_smul, Real.norm_eq_abs,
    mul_div_assoc, Real.mul_iSup_of_nonneg (abs_nonneg c)]

/-- The Hölder seminorm is subadditive on Hölder functions: if $g$ and $h$ are $\beta$-Hölder with
some constants, then $[g + h]_\beta \le [g]_\beta + [h]_\beta$. -/
theorem holderSeminorm_add_le {β : ℝ≥0} {g h : X → F} (hg : ∃ C : ℝ≥0, HolderWith C β g)
    (hh : ∃ C : ℝ≥0, HolderWith C β h) :
    holderSeminorm β (g + h) ≤ holderSeminorm β g + holderSeminorm β h := by
  obtain ⟨Cg, hCg⟩ := hg
  obtain ⟨Ch, hCh⟩ := hh
  refine Real.iSup_le (fun p ↦ ?_)
    (add_nonneg (holderSeminorm_nonneg _ _) (holderSeminorm_nonneg _ _))
  calc ‖(g + h) p.1 - (g + h) p.2‖ / dist p.1 p.2 ^ (β : ℝ)
      ≤ (‖g p.1 - g p.2‖ + ‖h p.1 - h p.2‖) / dist p.1 p.2 ^ (β : ℝ) := by
        refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg dist_nonneg _)
        rw [Pi.add_apply, Pi.add_apply, add_sub_add_comm]
        exact norm_add_le _ _
    _ = ‖g p.1 - g p.2‖ / dist p.1 p.2 ^ (β : ℝ) + ‖h p.1 - h p.2‖ / dist p.1 p.2 ^ (β : ℝ) :=
        add_div _ _ _
    _ ≤ holderSeminorm β g + holderSeminorm β h :=
        add_le_add (le_ciSup hCg.bddAbove_holderQuotient p) (le_ciSup hCh.bddAbove_holderQuotient p)

/-- **Hölder interpolation.** Let $0 < \beta$ and $\beta' \le \beta$. Let $g : X \to F$ satisfy
$\|g(x) - g(y)\| \le A$ for all $x, y$, and let $g$ be $\beta$-Hölder with constant $C$. Then
$g$ is $\beta'$-Hölder with constant
$$A^{1 - \beta'/\beta} \, C^{\beta'/\beta}.$$
-/
theorem HolderWith.of_le_of_forall_norm_sub_le {β β' : ℝ≥0} (hβ : 0 < β) (hβ' : β' ≤ β)
    {g : X → F} {A C : ℝ≥0} (hA : ∀ x y, ‖g x - g y‖ ≤ A) (hC : HolderWith C β g) :
    HolderWith (A ^ ((1 - β' / β : ℝ≥0) : ℝ) * C ^ ((β' / β : ℝ≥0) : ℝ)) β' g := by
  have h0 : HolderWith A 0 g := fun x y ↦ by
    rw [NNReal.coe_zero, ENNReal.rpow_zero, mul_one, edist_dist, dist_eq_norm,
      ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hA x y)
  have ht : (1 - β' / β : ℝ≥0) + β' / β = 1 :=
    tsub_add_cancel_of_le (div_le_one_of_le₀ hβ' β.coe_nonneg)
  have := h0.interpolate hC ht
  rwa [zero_mul, zero_add, mul_div_cancel₀ _ hβ.ne'] at this

end HolderSeminorm

/-! ### The space $C^{j,\beta}(\overline{\Omega})$ -/

section Space

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {j : ℕ} {β : ℝ≥0}

namespace HolderSpace

variable (Ω F j) in
/-- The tuples $(G_0, \dots, G_j)$ of bounded continuous functions on $\overline{\Omega}$, where
$G_i$ takes values in the continuous $i$-linear maps $E^i \to F$. This is the ambient space of
`HolderSpace`. -/
abbrev Tuple : Type _ := ∀ i : Fin (j + 1), closure (Ω : Set E) →ᵇ (E [×(i : ℕ)]→L[ℝ] F)

/-- A tuple $(G_0, \dots, G_j)$ is a **derivative tuple** if it is the tuple of derivatives of one
function of class $C^j$ on $\Omega$: there is $f : E \to F$ of class $C^j$ on $\Omega$ with
$G_i(x) = D^i f(x)$ for every $x \in \Omega$ and every $i \le j$.

The function is unique on $\Omega$, because it is $G_0$ there. The tuple is determined by $G_0$
on $\Omega$ (`HolderSpace.IsDerivTuple.eq_of_eqOn`). The derivative $D^i f$ is
`iteratedFDeriv ℝ i f`. -/
def IsDerivTuple (G : Tuple Ω F j) : Prop :=
  ∃ f : E → F, ContDiffOn ℝ j f Ω ∧
    ∀ (i : Fin (j + 1)) (x : E) (hx : x ∈ Ω), G i ⟨x, subset_closure hx⟩ = iteratedFDeriv ℝ i f x

/-- The sum of two derivative tuples is a derivative tuple. -/
theorem IsDerivTuple.add {G H : Tuple Ω F j} (hG : IsDerivTuple G) (hH : IsDerivTuple H) :
    IsDerivTuple (G + H) := by
  obtain ⟨f, hf, hfG⟩ := hG
  obtain ⟨g, hg, hgH⟩ := hH
  refine ⟨f + g, hf.add hg, fun i x hx ↦ ?_⟩
  have hi : ((i : ℕ) : WithTop ℕ∞) ≤ j := by exact_mod_cast Nat.lt_succ_iff.1 i.2
  rw [Pi.add_apply, add_apply, hfG i x hx, hgH i x hx,
    iteratedFDeriv_add_apply ((hf.contDiffAt (Ω.isOpen.mem_nhds hx)).of_le hi)
      ((hg.contDiffAt (Ω.isOpen.mem_nhds hx)).of_le hi)]

/-- The zero tuple is a derivative tuple. -/
theorem IsDerivTuple.zero : IsDerivTuple (0 : Tuple Ω F j) :=
  ⟨0, contDiffOn_const, fun i x _ ↦ by simp⟩

/-- A real multiple of a derivative tuple is a derivative tuple. -/
theorem IsDerivTuple.smul (c : ℝ) {G : Tuple Ω F j} (hG : IsDerivTuple G) :
    IsDerivTuple (c • G) := by
  obtain ⟨f, hf, hfG⟩ := hG
  refine ⟨c • f, hf.const_smul c, fun i x hx ↦ ?_⟩
  have hi : ((i : ℕ) : WithTop ℕ∞) ≤ j := by exact_mod_cast Nat.lt_succ_iff.1 i.2
  rw [Pi.smul_apply, smul_apply, hfG i x hx,
    iteratedFDeriv_const_smul_apply ((hf.contDiffAt (Ω.isOpen.mem_nhds hx)).of_le hi)]

variable (Ω F j β) in
/-- The derivative tuples whose top entry $G_j$ is $\beta$-Hölder with some constant, as a real
subspace of the tuples. This is the carrier of `HolderSpace`. -/
def submodule : Submodule ℝ (Tuple Ω F j) where
  carrier := {G | IsDerivTuple G ∧ ∃ C : ℝ≥0, HolderWith C β (G (Fin.last j))}
  add_mem' hG hH := ⟨hG.1.add hH.1, let ⟨C, hC⟩ := hG.2; let ⟨D, hD⟩ := hH.2; ⟨C + D, hC.add hD⟩⟩
  zero_mem' := ⟨IsDerivTuple.zero, 0, HolderWith.zero⟩
  smul_mem' c _ hG := ⟨hG.1.smul c, let ⟨C, hC⟩ := hG.2; ⟨C * ‖c‖₊, hC.smul c⟩⟩

end HolderSpace

variable (Ω F j β) in
/-- The **Hölder space** $C^{j,\beta}(\overline{\Omega})$ of [han2009theoretical], §1.4.1. Its
elements are the functions $f$ of class $C^j$ on the open set $\Omega$ whose derivatives
$D^i f$, $i \le j$, extend to bounded continuous functions on $\overline{\Omega}$, with
$\beta$-Hölder top derivative $D^j f$. The norm is $\|f\| = \sum_{i \le j} \|D^i f\|_\infty +
[D^j f]_\beta$.

An element is the tuple $(G_0, \dots, G_j)$ of the continuous extensions of the derivatives
(`HolderSpace.deriv u i`), and `⇑u`, which is $G_0$, is the function on $\overline{\Omega}$. The
module doc comment explains why the extensions are carried and not the function. The norm is
equivalent to the norm of the source, which takes the maximum of the sup norms and sums the
seminorms of the partial derivatives of order $j$. The exponent $\beta$ is any element of `ℝ≥0`. -/
def HolderSpace : Type _ :=
  HolderSpace.submodule Ω F j β

namespace HolderSpace

instance : AddCommGroup (HolderSpace Ω F j β) :=
  inferInstanceAs (AddCommGroup (submodule Ω F j β))

instance : Module ℝ (HolderSpace Ω F j β) :=
  inferInstanceAs (Module ℝ (submodule Ω F j β))

/-- The continuous extension to $\overline{\Omega}$ of the $i$-th derivative of
$u \in C^{j,\beta}(\overline{\Omega})$, for $i \le j$. For $i = 0$ it is $u$ itself, as a
$0$-linear map. -/
def deriv (u : HolderSpace Ω F j β) (i : Fin (j + 1)) :
    closure (Ω : Set E) →ᵇ (E [×(i : ℕ)]→L[ℝ] F) :=
  u.1 i

/-- Each $u \in C^{j,\beta}(\overline{\Omega})$ is a function on $\overline{\Omega}$: its zeroth
derivative, through the identification of $0$-linear maps with their values. -/
instance : CoeFun (HolderSpace Ω F j β) fun _ ↦ closure (Ω : Set E) → F :=
  ⟨fun u x ↦ continuousMultilinearCurryFin0 ℝ E F (u.deriv 0 x)⟩

/-- The value $u(x)$ is the value of the $0$-linear map `u.deriv 0 x`. -/
theorem coe_def (u : HolderSpace Ω F j β) (x : closure (Ω : Set E)) :
    u x = continuousMultilinearCurryFin0 ℝ E F (u.deriv 0 x) :=
  rfl

/-- The tuple of derivatives of an element of $C^{j,\beta}(\overline{\Omega})$ is a derivative
tuple. -/
theorem isDerivTuple (u : HolderSpace Ω F j β) : IsDerivTuple u.deriv := u.2.1

/-- The top derivative of an element of $C^{j,\beta}(\overline{\Omega})$ is $\beta$-Hölder with some
constant. -/
theorem exists_holderWith (u : HolderSpace Ω F j β) :
    ∃ C : ℝ≥0, HolderWith C β (u.deriv (Fin.last j)) := u.2.2

/-- Two elements of $C^{j,\beta}(\overline{\Omega})$ with the same derivatives $G_i$ for all
$i \le j$ are equal. -/
@[ext]
theorem ext {u v : HolderSpace Ω F j β} (h : ∀ i, u.deriv i = v.deriv i) : u = v :=
  Subtype.ext (funext h)

/-- The derivatives of $u + v$ are the sums of the derivatives of $u$ and $v$. -/
@[simp]
theorem deriv_add (u v : HolderSpace Ω F j β) (i : Fin (j + 1)) :
    (u + v).deriv i = u.deriv i + v.deriv i := rfl

/-- The derivatives of $u - v$ are the differences of the derivatives of $u$ and $v$. -/
@[simp]
theorem deriv_sub (u v : HolderSpace Ω F j β) (i : Fin (j + 1)) :
    (u - v).deriv i = u.deriv i - v.deriv i := rfl

/-- The derivatives of $-u$ are the negatives of the derivatives of $u$. -/
@[simp]
theorem deriv_neg (u : HolderSpace Ω F j β) (i : Fin (j + 1)) : (-u).deriv i = -u.deriv i := rfl

/-- The derivatives of $c u$ are $c$ times the derivatives of $u$. -/
@[simp]
theorem deriv_smul (c : ℝ) (u : HolderSpace Ω F j β) (i : Fin (j + 1)) :
    (c • u).deriv i = c • u.deriv i := rfl

/-- The derivatives of $0$ are $0$. -/
@[simp]
theorem deriv_zero (i : Fin (j + 1)) : (0 : HolderSpace Ω F j β).deriv i = 0 := rfl

/-- As functions on $\overline{\Omega}$, $(u + v)(x) = u(x) + v(x)$. -/
@[simp]
theorem coe_add (u v : HolderSpace Ω F j β) (x : closure (Ω : Set E)) : (u + v) x = u x + v x := by
  rw [coe_def, coe_def, coe_def, deriv_add, add_apply]
  exact (continuousMultilinearCurryFin0 ℝ E F).map_add _ _

/-- As functions on $\overline{\Omega}$, $(c u)(x) = c \, u(x)$. -/
@[simp]
theorem coe_smul (c : ℝ) (u : HolderSpace Ω F j β) (x : closure (Ω : Set E)) :
    (c • u) x = c • u x := by
  rw [coe_def, coe_def, deriv_smul, smul_apply]
  exact (continuousMultilinearCurryFin0 ℝ E F).map_smul _ _

/-- As a function on $\overline{\Omega}$, the zero element is $0$. -/
@[simp]
theorem coe_zero (x : closure (Ω : Set E)) : (0 : HolderSpace Ω F j β) x = 0 := by
  rw [coe_def, deriv_zero, FunLike.coe_zero, Pi.zero_apply]
  exact (continuousMultilinearCurryFin0 ℝ E F).map_zero

/-! ### The norm -/

/-- The norm of $C^{j,\beta}(\overline{\Omega})$: $\|u\| = \sum_{i \le j} \|D^i u\|_\infty + [D^j
u]_\beta$, with the sup norms taken on $\overline{\Omega}$. -/
instance : Norm (HolderSpace Ω F j β) :=
  ⟨fun u ↦ ∑ i, ‖u.deriv i‖ + holderSeminorm β (u.deriv (Fin.last j))⟩

/-- The norm of $C^{j,\beta}(\overline{\Omega})$ is
$$\|u\| = \sum_{i \le j} \|D^i u\|_\infty + [D^j u]_\beta,$$
where $D^i u$ is the extension `HolderSpace.deriv u i` to $\overline{\Omega}$ and
$\|\cdot\|_\infty$ is the sup norm on $\overline{\Omega}$. -/
theorem norm_def (u : HolderSpace Ω F j β) :
    ‖u‖ = ∑ i, ‖u.deriv i‖ + holderSeminorm β (u.deriv (Fin.last j)) :=
  rfl

/-- The sum of the sup norms of the derivatives is at most the norm:
$\sum_{i \le j} \|D^i u\|_\infty \le \|u\|$. -/
theorem sum_norm_deriv_le_norm (u : HolderSpace Ω F j β) : ∑ i, ‖u.deriv i‖ ≤ ‖u‖ :=
  le_add_of_nonneg_right (holderSeminorm_nonneg _ _)

/-- Each derivative is bounded in sup norm by the norm: $\|D^i u\|_\infty \le \|u\|$ for every
$i \le j$. -/
theorem norm_deriv_le (u : HolderSpace Ω F j β) (i : Fin (j + 1)) : ‖u.deriv i‖ ≤ ‖u‖ :=
  (Finset.single_le_sum (f := fun i ↦ ‖u.deriv i‖) (fun _ _ ↦ norm_nonneg _)
    (Finset.mem_univ i)).trans (sum_norm_deriv_le_norm u)

/-- The Hölder seminorm of the top derivative is bounded by the norm: $[D^j u]_\beta \le \|u\|$. -/
theorem holderSeminorm_le_norm (u : HolderSpace Ω F j β) :
    holderSeminorm β (u.deriv (Fin.last j)) ≤ ‖u‖ :=
  le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)

/-- The norm $\|u\| = \sum_{i \le j} \|D^i u\|_\infty + [D^j u]_\beta$ satisfies the axioms of a
norm on a real vector space. The sum of the sup norms is a norm, and the Hölder seminorm of the
top derivative is a seminorm: it is subadditive on Hölder functions and absolutely homogeneous. -/
theorem normedSpaceCore : NormedSpace.Core ℝ (HolderSpace Ω F j β) where
  norm_nonneg u := add_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    (holderSeminorm_nonneg _ _)
  norm_smul c u := by
    rw [norm_def, norm_def, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ ↦ by rw [deriv_smul, norm_smul, Real.norm_eq_abs]
    · rw [deriv_smul, Real.norm_eq_abs]
      exact holderSeminorm_smul _ c _
  norm_triangle u v := by
    simp only [norm_def, deriv_add]
    have h1 : ∑ i, ‖u.deriv i + v.deriv i‖ ≤ ∑ i, ‖u.deriv i‖ + ∑ i, ‖v.deriv i‖ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ ↦ norm_add_le _ _
    have h2 := holderSeminorm_add_le (β := β) u.exists_holderWith v.exists_holderWith
    rw [FunLike.coe_add]
    linarith
  norm_eq_zero_iff u := by
    constructor
    · intro h
      have hle := sum_norm_deriv_le_norm u
      have h0 : ∑ i, ‖u.deriv i‖ = 0 :=
        le_antisymm (by linarith) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
      rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ norm_nonneg _] at h0
      exact ext fun i ↦ norm_eq_zero.1 (h0 i (Finset.mem_univ i))
    · rintro rfl
      simp [norm_def]

/-- $C^{j,\beta}(\overline{\Omega})$ is a normed group under the norm $\|u\| = \sum_{i \le j} \|D^i
u\|_\infty + [D^j u]_\beta$. -/
instance : NormedAddCommGroup (HolderSpace Ω F j β) := NormedAddCommGroup.ofCore normedSpaceCore

/-- $C^{j,\beta}(\overline{\Omega})$ is a real normed space. -/
instance : NormedSpace ℝ (HolderSpace Ω F j β) := NormedSpace.ofCore normedSpaceCore

/-- The top derivative $D^j u$ of $u \in C^{j,\beta}(\overline{\Omega})$ is $\beta$-Hölder with
constant $\|u\|$. -/
theorem holderWith_norm (u : HolderSpace Ω F j β) : HolderWith ‖u‖₊ β (u.deriv (Fin.last j)) :=
  (holderWith_holderSeminorm u.exists_holderWith).mono
    (NNReal.coe_le_coe.1 (by rw [coe_nnnorm]; exact holderSeminorm_le_norm u))

/-! ### Uniqueness: the tuple is determined by the function on $\Omega$ -/

omit [NormedSpace ℝ E] in
/-- The points of $\overline{\Omega}$ that lie in $\Omega$ are dense in $\overline{\Omega}$. -/
theorem dense_preimage_val_closure (Ω : Opens E) :
    Dense (Subtype.val ⁻¹' (Ω : Set E) : Set (closure (Ω : Set E))) := by
  intro x
  rw [closure_subtype]
  refine closure_mono (fun y hy ↦ ?_) x.2
  exact ⟨⟨y, subset_closure hy⟩, hy, rfl⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Let $G$ be a Hausdorff space. Two continuous functions $\overline{\Omega} \to G$ that agree at
every point of $\Omega$ are equal. -/
theorem eq_of_forall_eq_of_continuous {G : Type*} [TopologicalSpace G] [T2Space G]
    {f g : closure (Ω : Set E) → G} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x (hx : x ∈ Ω), f ⟨x, subset_closure hx⟩ = g ⟨x, subset_closure hx⟩) : f = g := by
  funext x
  have hpre : EqOn f g (Subtype.val ⁻¹' (Ω : Set E)) := by
    rintro ⟨y, hyc⟩ hy
    exact h y hy
  exact hpre.of_subset_closure hf.continuousOn hg.continuousOn (subset_univ _)
    (by rw [(dense_preimage_val_closure Ω).closure_eq]) (mem_univ x)

/-- Two derivative tuples $G$ and $H$ with $G_0 = H_0$ on $\Omega$ are equal.

The higher entries are the derivatives of the zeroth entry on $\Omega$. All entries are
continuous on $\overline{\Omega}$, in which $\Omega$ is dense. -/
theorem IsDerivTuple.eq_of_eqOn {G H : Tuple Ω F j} (hG : IsDerivTuple G) (hH : IsDerivTuple H)
    (h : ∀ x (hx : x ∈ Ω), G 0 ⟨x, subset_closure hx⟩ = H 0 ⟨x, subset_closure hx⟩) : G = H := by
  obtain ⟨f, hf, hfG⟩ := hG
  obtain ⟨g, hg, hgH⟩ := hH
  have hfg : EqOn f g Ω := fun x hx ↦ by
    have := h x hx
    rw [hfG 0 x hx, hgH 0 x hx] at this
    simpa [iteratedFDeriv_zero_apply] using congrArg (continuousMultilinearCurryFin0 ℝ E F) this
  funext i
  refine BoundedContinuousFunction.ext fun x ↦ ?_
  have hpre : EqOn (G i) (H i) (Subtype.val ⁻¹' (Ω : Set E)) := by
    rintro ⟨y, hyc⟩ hy
    have hy' : y ∈ Ω := hy
    rw [hfG i y hy', hgH i y hy']
    have hev : f =ᶠ[𝓝 y] g := by
      filter_upwards [Ω.isOpen.mem_nhds hy'] with z hz
      exact hfg hz
    exact (hev.iteratedFDeriv (𝕜 := ℝ) i).eq_of_nhds
  exact hpre.of_subset_closure (G i).continuous.continuousOn (H i).continuous.continuousOn
    (subset_univ _) (by rw [(dense_preimage_val_closure Ω).closure_eq]) (mem_univ x)

/-- An element of $C^{j,\beta}(\overline{\Omega})$ is determined by its values on $\Omega$: if
$u(x) = v(x)$ for all $x \in \Omega$, then $u = v$. -/
theorem ext_of_eqOn {u v : HolderSpace Ω F j β}
    (h : ∀ x (hx : x ∈ Ω), u ⟨x, subset_closure hx⟩ = v ⟨x, subset_closure hx⟩) : u = v :=
  Subtype.ext (u.isDerivTuple.eq_of_eqOn v.isDerivTuple fun x hx ↦
    (continuousMultilinearCurryFin0 ℝ E F).injective (h x hx))


/-! ### Constructors and the inclusions -/

/-- The element of $C^{j,\beta}(\overline{\Omega})$ given by a function. Let $f : E \to F$ be of
class $C^j$ on $\Omega$. For each $i \le j$, let $G_i$ be a function from $E$ to the continuous
$i$-linear maps $E^i \to F$ that is continuous on $\overline{\Omega}$, with $\|G_i(x)\| \le M_i$
for $x \in \overline{\Omega}$ and $G_i = D^i f$ on $\Omega$. Let $G_j$ be $\beta$-Hölder on
$\overline{\Omega}$ with constant $C$. Then the restrictions of the $G_i$ to $\overline{\Omega}$
form an element of $C^{j,\beta}(\overline{\Omega})$. -/
def mk' (f : E → F) (hf : ContDiffOn ℝ j f Ω) (G : ∀ i : Fin (j + 1), E → (E [×(i : ℕ)]→L[ℝ] F))
    (hGc : ∀ i, ContinuousOn (G i) (closure (Ω : Set E))) (M : Fin (j + 1) → ℝ)
    (hGb : ∀ i, ∀ x ∈ closure (Ω : Set E), ‖G i x‖ ≤ M i)
    (hGeq : ∀ i, ∀ x ∈ Ω, G i x = iteratedFDeriv ℝ i f x) {C : ℝ≥0}
    (hH : HolderOnWith C β (G (Fin.last j)) (closure (Ω : Set E))) : HolderSpace Ω F j β :=
  ⟨fun i ↦ BoundedContinuousFunction.ofNormedAddCommGroup ((closure (Ω : Set E)).domRestrict (G i))
      (continuousOn_iff_continuous_domRestrict.1 (hGc i)) (M i) fun x ↦ hGb i x x.2,
    ⟨f, hf, fun i x hx ↦ hGeq i x hx⟩, C, HolderWith.restrict_iff.2 hH⟩

/-- The $i$-th derivative of `HolderSpace.mk' f hf G …` is the restriction of $G_i$ to
$\overline{\Omega}$. -/
@[simp]
theorem deriv_mk' (f : E → F) (hf : ContDiffOn ℝ j f Ω)
    (G : ∀ i : Fin (j + 1), E → (E [×(i : ℕ)]→L[ℝ] F))
    (hGc : ∀ i, ContinuousOn (G i) (closure (Ω : Set E))) (M : Fin (j + 1) → ℝ)
    (hGb : ∀ i, ∀ x ∈ closure (Ω : Set E), ‖G i x‖ ≤ M i)
    (hGeq : ∀ i, ∀ x ∈ Ω, G i x = iteratedFDeriv ℝ i f x) {C : ℝ≥0}
    (hH : HolderOnWith C β (G (Fin.last j)) (closure (Ω : Set E))) (i : Fin (j + 1))
    (x : closure (Ω : Set E)) : (mk' f hf G hGc M hGb hGeq hH).deriv i x = G i x :=
  rfl

/-- The element `HolderSpace.mk' f hf G …` agrees with $f$ on $\Omega$. -/
theorem coe_mk' (f : E → F) (hf : ContDiffOn ℝ j f Ω)
    (G : ∀ i : Fin (j + 1), E → (E [×(i : ℕ)]→L[ℝ] F))
    (hGc : ∀ i, ContinuousOn (G i) (closure (Ω : Set E))) (M : Fin (j + 1) → ℝ)
    (hGb : ∀ i, ∀ x ∈ closure (Ω : Set E), ‖G i x‖ ≤ M i)
    (hGeq : ∀ i, ∀ x ∈ Ω, G i x = iteratedFDeriv ℝ i f x) {C : ℝ≥0}
    (hH : HolderOnWith C β (G (Fin.last j)) (closure (Ω : Set E))) (x : E) (hx : x ∈ Ω) :
    mk' f hf G hGc M hGb hGeq hH ⟨x, subset_closure hx⟩ = f x :=
  (LinearIsometryEquiv.eq_symm_apply _).mp (hGeq 0 x hx)

/-- If the bounds $M_i$ are nonnegative, then the norm of `HolderSpace.mk' f hf G …` is at most
$\sum_{i \le j} M_i + C$, where $C$ is the Hölder constant of $G_j$. -/
theorem norm_mk'_le (f : E → F) (hf : ContDiffOn ℝ j f Ω)
    (G : ∀ i : Fin (j + 1), E → (E [×(i : ℕ)]→L[ℝ] F))
    (hGc : ∀ i, ContinuousOn (G i) (closure (Ω : Set E))) (M : Fin (j + 1) → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hGb : ∀ i, ∀ x ∈ closure (Ω : Set E), ‖G i x‖ ≤ M i)
    (hGeq : ∀ i, ∀ x ∈ Ω, G i x = iteratedFDeriv ℝ i f x) {C : ℝ≥0}
    (hH : HolderOnWith C β (G (Fin.last j)) (closure (Ω : Set E))) :
    ‖mk' f hf G hGc M hGb hGeq hH‖ ≤ ∑ i, M i + C := by
  rw [norm_def]
  refine add_le_add (Finset.sum_le_sum fun i _ ↦ ?_) ?_
  · exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      (continuousOn_iff_continuous_domRestrict.1 (hGc i)) (hM i) fun x ↦ hGb i x x.2
  · exact (HolderWith.restrict_iff.2 hH).holderSeminorm_le

/-- The function $u$ on $\overline{\Omega}$ of $u \in C^{j,\beta}(\overline{\Omega})$, as a bounded
continuous function. -/
def toBCF (u : HolderSpace Ω F j β) : closure (Ω : Set E) →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ u x)
    ((continuousMultilinearCurryFin0 ℝ E F).continuous.comp (u.deriv 0).continuous) ‖u‖ fun x ↦ by
      rw [coe_def]
      exact ((continuousMultilinearCurryFin0 ℝ E F).norm_map _).le.trans
        ((BoundedContinuousFunction.norm_coe_le_norm _ x).trans (norm_deriv_le u 0))

/-- The bounded continuous function `u.toBCF` takes the value $u(x)$ at $x$. -/
@[simp]
theorem toBCF_apply (u : HolderSpace Ω F j β) (x : closure (Ω : Set E)) : u.toBCF x = u x := rfl

/-- The sup norm of $u$ on $\overline{\Omega}$ is at most the norm of $u$ in
$C^{j,\beta}(\overline{\Omega})$. -/
theorem norm_toBCF_le (u : HolderSpace Ω F j β) : ‖u.toBCF‖ ≤ ‖u‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg u) _

variable (Ω F j β) in
/-- The **inclusion** of $C^{j,\beta}(\overline{\Omega})$ in the bounded continuous functions on
$\overline{\Omega}$, $u \mapsto u$. It is a bounded linear map of norm at most $1$. -/
def toBCFL : HolderSpace Ω F j β →L[ℝ] (closure (Ω : Set E) →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := toBCF
      map_add' := fun u v ↦ BoundedContinuousFunction.ext fun x ↦ coe_add u v x
      map_smul' := fun c u ↦ BoundedContinuousFunction.ext fun x ↦ coe_smul c u x }
    1 fun u ↦ by rw [one_mul]; exact norm_toBCF_le u

/-- The inclusion `HolderSpace.toBCFL` maps $u$ to the function $x \mapsto u(x)$. -/
@[simp]
theorem toBCFL_apply (u : HolderSpace Ω F j β) (x : closure (Ω : Set E)) :
    toBCFL Ω F j β u x = u x := rfl

/-- The inclusion in the bounded continuous functions on $\overline{\Omega}$ is injective: an
element is determined by its function. -/
theorem toBCFL_injective : Function.Injective (toBCFL Ω F j β) := fun u v huv ↦
  ext_of_eqOn fun x hx ↦ by
    have := congrArg (fun f : closure (Ω : Set E) →ᵇ F ↦ f ⟨x, subset_closure hx⟩) huv
    simpa using this

/-- The inclusion of $C^{j,\beta}(\overline{\Omega})$ in the bounded continuous functions on
$\overline{\Omega}$ is a continuous embedding: it is injective and bounded.

The relation is `IsContinuousEmbedding`. -/
theorem isContinuousEmbedding_toBCFL : IsContinuousEmbedding (toBCFL Ω F j β).toLinearMap :=
  ⟨toBCFL_injective, 1, fun u ↦ by rw [one_mul]; exact norm_toBCF_le u⟩

section Lower

variable {β' : ℝ≥0}

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Let $\Omega$ be bounded and $\beta' \le \beta$. If $g$ on $\overline{\Omega}$ is $\beta$-Hölder
with constant $C$, then there is $D \ge 0$ such that $g$ is $\beta'$-Hölder with constant
$C D^{\beta - \beta'}$.

The number $D$ is a bound of the diameter of $\overline{\Omega}$. -/
theorem exists_holderWith_of_le (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : β' ≤ β)
    {g : closure (Ω : Set E) → F} {C : ℝ≥0} (hg : HolderWith C β g) :
    ∃ D : ℝ≥0, HolderWith (C * D ^ ((β : ℝ) - β')) β' g := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.1 hb.closure
  refine ⟨R.toNNReal, hg.of_le (fun x y ↦ ?_) hβ'⟩
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (hR x.2 y.2)

/-- **Lowering the Hölder exponent.** Let $\Omega$ be bounded and $\beta' \le \beta$. For
$u \in C^{j,\beta}(\overline{\Omega})$, this is the element of $C^{j,\beta'}(\overline{\Omega})$
with the same tuple of derivatives as $u$. -/
def toLower (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : β' ≤ β) (u : HolderSpace Ω F j β) :
    HolderSpace Ω F j β' :=
  ⟨u.1, u.isDerivTuple, let ⟨C, hC⟩ := u.exists_holderWith
    let ⟨D, hD⟩ := exists_holderWith_of_le hb hβ' hC; ⟨C * D ^ ((β : ℝ) - β'), hD⟩⟩

/-- Lowering the Hölder exponent does not change the derivatives. -/
@[simp]
theorem deriv_toLower (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : β' ≤ β)
    (u : HolderSpace Ω F j β) (i : Fin (j + 1)) : (toLower hb hβ' u).deriv i = u.deriv i := rfl

/-- Lowering the Hölder exponent does not change the function on $\overline{\Omega}$. -/
@[simp]
theorem coe_toLower (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : β' ≤ β)
    (u : HolderSpace Ω F j β) (x : closure (Ω : Set E)) : toLower hb hβ' u x = u x := rfl

/-- Lowering the Hölder exponent is additive. -/
theorem toLower_add (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : β' ≤ β)
    (u v : HolderSpace Ω F j β) : toLower hb hβ' (u + v) = toLower hb hβ' u + toLower hb hβ' v :=
  ext fun _ ↦ rfl

/-- Lowering the Hölder exponent commutes with multiplication by a real number. -/
theorem toLower_smul (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : β' ≤ β) (c : ℝ)
    (u : HolderSpace Ω F j β) : toLower hb hβ' (c • u) = c • toLower hb hβ' u :=
  ext fun _ ↦ rfl

/-- Lowering the Hölder exponent is injective. -/
theorem toLower_injective (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : β' ≤ β) :
    Function.Injective (toLower hb hβ' : HolderSpace Ω F j β → HolderSpace Ω F j β') :=
  fun _ _ huv ↦ ext fun i ↦ congrArg (fun w : HolderSpace Ω F j β' ↦ w.deriv i) huv

/-- The inclusion $C^{j,\beta}(\overline{\Omega}) \to C^{j,\beta'}(\overline{\Omega})$ is bounded.
Let $\Omega$ be bounded and $\beta' \le \beta$. Then there is $K \ge 0$ with
$$\|u\|_{C^{j,\beta'}} \le K \, \|u\|_{C^{j,\beta}} \quad \text{for all } u \in
  C^{j,\beta}(\overline{\Omega}).$$

The proof takes $K = 1 + D^{\beta - \beta'}$, with $D$ a bound of the diameter of
$\overline{\Omega}$. -/
theorem exists_forall_norm_toLower_le (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : β' ≤ β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : HolderSpace Ω F j β, ‖toLower hb hβ' u‖ ≤ K * ‖u‖ := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.1 hb.closure
  refine ⟨1 + R.toNNReal ^ ((β : ℝ) - β'), by positivity, fun u ↦ ?_⟩
  have h1 : HolderWith (‖u‖₊ * R.toNNReal ^ ((β : ℝ) - β')) β' (u.deriv (Fin.last j)) :=
    (holderWith_norm u).of_le (fun x y ↦ by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hR x.2 y.2)) hβ'
  have h2 := h1.holderSeminorm_le
  rw [NNReal.coe_mul, NNReal.coe_rpow, coe_nnnorm] at h2
  calc ‖toLower hb hβ' u‖
      = ∑ i, ‖u.deriv i‖ + holderSeminorm β' (u.deriv (Fin.last j)) := rfl
    _ ≤ ‖u‖ + ‖u‖ * (R.toNNReal : ℝ) ^ ((β : ℝ) - β') :=
        add_le_add (sum_norm_deriv_le_norm u) h2
    _ = (1 + (R.toNNReal : ℝ) ^ ((β : ℝ) - β')) * ‖u‖ := by ring

variable (Ω F j) in
/-- The **inclusion** $C^{j,\beta}(\overline{\Omega}) \to C^{j,\beta'}(\overline{\Omega})$ for a
bounded $\Omega$ and $\beta' \le \beta$, as a bounded linear map. It is `HolderSpace.toLower`. -/
def toLowerL (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : β' ≤ β) :
    HolderSpace Ω F j β →L[ℝ] HolderSpace Ω F j β' :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := toLower hb hβ'
      map_add' := toLower_add hb hβ'
      map_smul' := toLower_smul hb hβ' }
    (let ⟨K, _, hK⟩ := exists_forall_norm_toLower_le (F := F) (j := j) hb hβ'; ⟨K, hK⟩)

/-- The inclusion `HolderSpace.toLowerL` maps $u$ to `HolderSpace.toLower hb hβ' u`. -/
@[simp]
theorem toLowerL_apply (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : β' ≤ β)
    (u : HolderSpace Ω F j β) : toLowerL Ω F j hb hβ' u = toLower hb hβ' u := rfl

/-- The inclusion $C^{j,\beta}(\overline{\Omega}) \hookrightarrow C^{j,\beta'}(\overline{\Omega})$
is a continuous embedding for a bounded $\Omega$ and $\beta' \le \beta$. These are the
inclusions $C^{m,\beta}(\overline{\Omega}) \subset C^{m,\alpha}(\overline{\Omega})$ of
[han2009theoretical], §1.4.1.

The relation is `IsContinuousEmbedding`: the inclusion is injective and bounded. -/
theorem isContinuousEmbedding_toLowerL (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : β' ≤ β) :
    IsContinuousEmbedding (toLowerL Ω F j hb hβ').toLinearMap :=
  ⟨toLower_injective hb hβ', _, (toLowerL Ω F j hb hβ').le_opNorm⟩

end Lower

/-! ### Uniform limits of derivative tuples -/

section Limit

open scoped Classical in
/-- The extension by zero of a function on $\overline{\Omega}$ to $E$. -/
def extendZero (h : closure (Ω : Set E) → F) (x : E) : F :=
  if hx : x ∈ closure (Ω : Set E) then h ⟨x, hx⟩ else 0

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The extension by zero of $h$ agrees with $h$ at each point of $\overline{\Omega}$. -/
theorem extendZero_of_mem (h : closure (Ω : Set E) → F) {x : E} (hx : x ∈ closure (Ω : Set E)) :
    extendZero h x = h ⟨x, hx⟩ := by
  simp [extendZero, hx]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The extension by zero of $h$ agrees with $h$ on $\overline{\Omega}$, with the point taken as an
element of the subtype. -/
theorem extendZero_coe (h : closure (Ω : Set E) → F) (x : closure (Ω : Set E)) :
    extendZero h x = h x :=
  extendZero_of_mem h x.2

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The extension by zero of a bounded continuous function on $\overline{\Omega}$ is continuous on
$\overline{\Omega}$. -/
theorem continuousOn_extendZero (h : closure (Ω : Set E) →ᵇ F) :
    ContinuousOn (extendZero h) (closure (Ω : Set E)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert h.continuous using 1
  funext x
  exact extendZero_coe h x

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- If bounded continuous functions $G_n$ on $\overline{\Omega}$ converge uniformly to $L$, then
their extensions by zero converge uniformly on $\Omega$ to the extension by zero of $L$. -/
theorem tendstoUniformlyOn_extendZero {G : ℕ → closure (Ω : Set E) →ᵇ F}
    {L : closure (Ω : Set E) →ᵇ F} (h : Tendsto G atTop (𝓝 L)) :
    TendstoUniformlyOn (fun n ↦ extendZero (G n)) (extendZero L) atTop (Ω : Set E) := by
  rw [BoundedContinuousFunction.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff] at h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [h ε hε] with n hn x hx
  rw [extendZero_of_mem _ (subset_closure hx), extendZero_of_mem _ (subset_closure hx)]
  exact hn ⟨x, subset_closure hx⟩

/-- The **derivative tuples are closed under uniform limits**. Let $G^{(n)}$ be derivative tuples,
and let $G^{(n)}_i \to L_i$ uniformly on $\overline{\Omega}$ for each $i \le j$. Then $L$ is a
derivative tuple.

The function is the extension by zero of $L_0$. Each $L_i$ is its $i$-th derivative on $\Omega$,
by Mathlib's `hasFDerivAt_of_tendstoUniformlyOn`. -/
theorem IsDerivTuple.of_tendsto {G : ℕ → Tuple Ω F j} (hG : ∀ n, IsDerivTuple (G n))
    {L : Tuple Ω F j} (hL : ∀ i, Tendsto (fun n ↦ G n i) atTop (𝓝 (L i))) : IsDerivTuple L := by
  choose f hf hfG using hG
  -- the extensions by zero of the limit entries, and of the entries
  set g : ∀ i : Fin (j + 1), E → (E [×(i : ℕ)]→L[ℝ] F) := fun i ↦ extendZero (L i) with hg
  have hgn : ∀ (n) (i : Fin (j + 1)), ∀ x ∈ Ω, extendZero (G n i) x = iteratedFDeriv ℝ i (f n) x :=
    fun n i x hx ↦ by rw [extendZero_of_mem _ (subset_closure hx), hfG n i x hx]
  -- the derivative of `g i` on `Ω` is `g (i + 1)`
  have hd : ∀ i : Fin (j + 1), ∀ hi : (i : ℕ) < j, ∀ x ∈ Ω, HasFDerivAt (g i)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin ((i : ℕ) + 1) ↦ E) F
        (g ⟨(i : ℕ) + 1, by omega⟩ x)) x := by
    intro i hi x hx
    have hunif : TendstoUniformlyOn
        (fun n x ↦ continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin ((i : ℕ) + 1) ↦ E) F
          (extendZero (G n ⟨(i : ℕ) + 1, by omega⟩) x))
        (fun x ↦ continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin ((i : ℕ) + 1) ↦ E) F
          (g ⟨(i : ℕ) + 1, by omega⟩ x)) atTop Ω :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin ((i : ℕ) + 1) ↦ E) F).isometry
        |>.uniformContinuous.comp_tendstoUniformlyOn
        (tendstoUniformlyOn_extendZero (hL ⟨(i : ℕ) + 1, by omega⟩))
    refine hasFDerivAt_of_tendstoUniformlyOn (f := fun n ↦ iteratedFDeriv ℝ i (f n)) Ω.isOpen hunif
      (fun n y hy ↦ ?_) (fun y hy ↦ ?_) hx
    · have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ i (f n)) y :=
        ((hf n).contDiffAt (Ω.isOpen.mem_nhds hy)).differentiableAt_iteratedFDeriv
          (by exact_mod_cast hi)
      refine hdiff.hasFDerivAt.congr_fderiv ?_
      rw [fderiv_iteratedFDeriv, Function.comp_apply, hgn n _ y hy]
    · exact ((tendstoUniformlyOn_extendZero (hL i)).tendsto_at hy).congr fun n ↦ hgn n i y hy
  -- the function and its derivatives
  set f₀ : E → F := fun x ↦ continuousMultilinearCurryFin0 ℝ E F (g 0 x) with hf₀
  have hiter : ∀ i : Fin (j + 1), ∀ x ∈ Ω, iteratedFDeriv ℝ i f₀ x = g i x := by
    intro i
    obtain ⟨i, hi⟩ := i
    induction i with
    | zero =>
      intro x hx
      change iteratedFDeriv ℝ 0 f₀ x = g 0 x
      rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, hf₀]
      exact (continuousMultilinearCurryFin0 ℝ E F).symm_apply_apply _
    | succ i ih =>
      intro x hx
      have hi' : i < j + 1 := by omega
      have hij : i < j := by omega
      have heq : iteratedFDeriv ℝ i f₀ =ᶠ[𝓝 x] g ⟨i, hi'⟩ := by
        filter_upwards [Ω.isOpen.mem_nhds hx] with z hz
        exact ih hi' z hz
      change iteratedFDeriv ℝ (i + 1) f₀ x = g ⟨i + 1, hi⟩ x
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, heq.fderiv_eq,
        (hd ⟨i, hi'⟩ hij x hx).fderiv]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ E) F).symm_apply_apply _
  refine ⟨f₀, ?_, fun i x hx ↦ ?_⟩
  · refine contDiffOn_of_continuousOn_differentiableOn (fun m hm ↦ ?_) (fun m hm ↦ ?_)
    · have hm' : m < j + 1 := by exact_mod_cast Nat.lt_succ_of_le (by exact_mod_cast hm)
      refine ((continuousOn_extendZero (L ⟨m, hm'⟩)).mono subset_closure).congr fun x hx ↦ ?_
      rw [iteratedFDerivWithin_of_isOpen _ Ω.isOpen hx, hiter ⟨m, hm'⟩ x hx]
    · have hmj : m < j := by exact_mod_cast hm
      have hm' : m < j + 1 := by omega
      refine DifferentiableOn.congr (f := g ⟨m, hm'⟩) (fun x hx ↦ ?_) fun x hx ↦ ?_
      · exact (hd ⟨m, hm'⟩ hmj x hx).differentiableAt.differentiableWithinAt
      · rw [iteratedFDerivWithin_of_isOpen _ Ω.isOpen hx, hiter ⟨m, hm'⟩ x hx]
  · rw [hiter i x hx, hg]
    exact (extendZero_of_mem _ (subset_closure hx)).symm

end Limit


/-! ### Completeness -/

section Complete

/-- A uniform limit of $\beta$-Hölder functions with a common constant is $\beta$-Hölder with that
constant. Let $H_n$ be bounded continuous functions on $X$ with values in $G$, each
$\beta$-Hölder with constant $C$, that converge uniformly to $L$. Then $L$ is $\beta$-Hölder
with constant $C$.

The space $X$ carries a pseudometric, for the Hölder condition, and a topology, for the
continuity of the $H_n$. The statement does not require that the topology is the one of the
pseudometric. -/
theorem holderWith_of_tendsto {X G : Type*} [PseudoMetricSpace X] [TopologicalSpace X]
    [SeminormedAddCommGroup G] {H : ℕ → X →ᵇ G} {L : X →ᵇ G} (hL : Tendsto H atTop (𝓝 L))
    {C : ℝ≥0} (hH : ∀ n, HolderWith C β (H n)) : HolderWith C β L :=
  holderWith_of_dist_le fun x y ↦ by
    have hx := ((continuous_eval_const x).tendsto L).comp hL
    have hy := ((continuous_eval_const y).tendsto L).comp hL
    exact le_of_tendsto' (hx.dist hy) fun n ↦ (hH n).dist_le x y

variable (Ω F j β) in
/-- The $i$-th derivative, $u \mapsto D^i u$, from $C^{j,\beta}(\overline{\Omega})$ to the bounded
continuous functions on $\overline{\Omega}$ with values in the $i$-linear maps $E^i \to F$, as a
bounded linear map of norm at most $1$. -/
def derivCLM (i : Fin (j + 1)) :
    HolderSpace Ω F j β →L[ℝ] (closure (Ω : Set E) →ᵇ (E [×(i : ℕ)]→L[ℝ] F)) :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ u.deriv i, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    1 fun u ↦ by rw [one_mul]; exact norm_deriv_le u i

/-- The map `HolderSpace.derivCLM` takes $u$ to its $i$-th derivative `u.deriv i`. -/
@[simp]
theorem derivCLM_apply (i : Fin (j + 1)) (u : HolderSpace Ω F j β) :
    derivCLM Ω F j β i u = u.deriv i :=
  rfl

/-- $C^{j,\beta}(\overline{\Omega})$ is a **Banach space** when $F$ is complete. This is stated in
[han2009theoretical], §1.4.1.

A Cauchy sequence converges entrywise in the Banach spaces of bounded continuous functions on
$\overline{\Omega}$ with values in the $i$-linear maps. The limit tuple is a derivative tuple
(`HolderSpace.IsDerivTuple.of_tendsto`) with Hölder top entry
(`HolderSpace.holderWith_of_tendsto`). The Hölder seminorm of the difference tends to $0$,
because the Cauchy estimate $\|(u_n - u_m)(x) - (u_n - u_m)(y)\| \le \varepsilon \|x -
y\|^\beta$ passes to the limit $m \to \infty$. -/
instance [CompleteSpace F] : CompleteSpace (HolderSpace Ω F j β) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  have hc : ∀ i : Fin (j + 1), ∃ L : closure (Ω : Set E) →ᵇ (E [×(i : ℕ)]→L[ℝ] F),
      Tendsto (fun n ↦ (u n).deriv i) atTop (𝓝 L) := fun i ↦
    cauchySeq_tendsto_of_complete ((derivCLM Ω F j β i).uniformContinuous.comp_cauchySeq hu)
  choose L hL using hc
  -- the limit tuple is in the space
  obtain ⟨R, -, hR⟩ := cauchySeq_bdd hu
  have hM : ∀ n, ‖u n‖ ≤ ‖u 0‖ + R := fun n ↦ by
    have := (hR n 0).le
    rw [dist_eq_norm] at this
    linarith [norm_le_norm_add_norm_sub' (u n) (u 0)]
  have hLh : HolderWith (‖u 0‖ + R).toNNReal β (L (Fin.last j)) :=
    holderWith_of_tendsto (hL (Fin.last j)) fun n ↦ (holderWith_norm (u n)).mono
      (NNReal.coe_le_coe.1 (by rw [coe_nnnorm]; exact (hM n).trans (Real.le_coe_toNNReal _)))
  obtain ⟨w, hw⟩ : ∃ w : HolderSpace Ω F j β, w.deriv = L :=
    ⟨⟨L, IsDerivTuple.of_tendsto (fun n ↦ (u n).isDerivTuple) hL, _, hLh⟩, rfl⟩
  refine ⟨w, Metric.tendsto_atTop.2 fun ε hε ↦ ?_⟩
  -- the sup-norm part
  have h1 : Tendsto (fun n ↦ ∑ i, ‖(u n).deriv i - w.deriv i‖) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin (j + 1))) fun i _ ↦
      tendsto_iff_norm_sub_tendsto_zero.1 (hw ▸ hL i)
    simpa using this
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.1 h1) (ε / 2) (by positivity)
  -- the Hölder part, by the Cauchy estimate passed to the limit
  obtain ⟨N₂, hN₂⟩ := Metric.cauchySeq_iff.1 hu (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hs : holderSeminorm β ((u n).deriv (Fin.last j) - w.deriv (Fin.last j)) ≤ ε / 2 := by
    refine holderSeminorm_le (by positivity) fun x y ↦ ?_
    have hlim : Tendsto (fun m ↦ ‖((u n).deriv (Fin.last j) - (u m).deriv (Fin.last j)) x
        - ((u n).deriv (Fin.last j) - (u m).deriv (Fin.last j)) y‖) atTop
        (𝓝 ‖((u n).deriv (Fin.last j) - w.deriv (Fin.last j)) x
          - ((u n).deriv (Fin.last j) - w.deriv (Fin.last j)) y‖) := by
      have hx := ((continuous_eval_const x).tendsto _).comp (hw ▸ hL (Fin.last j))
      have hy := ((continuous_eval_const y).tendsto _).comp (hw ▸ hL (Fin.last j))
      simp only [sub_apply]
      exact ((tendsto_const_nhds.sub hx).sub (tendsto_const_nhds.sub hy)).norm
    refine le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨N₂, fun m hm ↦ ?_⟩)
    have hnm : ‖u n - u m‖ ≤ ε / 2 := by
      rw [← dist_eq_norm]
      exact (hN₂ n (le_of_max_le_right hn) m hm).le
    calc ‖((u n).deriv (Fin.last j) - (u m).deriv (Fin.last j)) x
          - ((u n).deriv (Fin.last j) - (u m).deriv (Fin.last j)) y‖
        = ‖(u n - u m).deriv (Fin.last j) x - (u n - u m).deriv (Fin.last j) y‖ := rfl
      _ ≤ holderSeminorm β ((u n - u m).deriv (Fin.last j)) * dist x y ^ (β : ℝ) :=
          norm_sub_le_holderSeminorm_mul (u n - u m).exists_holderWith x y
      _ ≤ ε / 2 * dist x y ^ (β : ℝ) := by
          gcongr
          exact (holderSeminorm_le_norm _).trans hnm
  have h2 := hN₁ n (le_of_max_le_left hn)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)] at h2
  rw [dist_eq_norm, norm_def]
  simp only [deriv_sub]
  linarith

end Complete

/-! ### Arzelà–Ascoli: compactness in the weaker Hölder norm -/

section Compact

/-- If $E$ and $F$ are finite-dimensional real normed spaces, then the space of continuous
$n$-linear maps $E^n \to F$ is finite-dimensional.

The continuous multilinear maps inject linearly into the multilinear maps. -/
instance _root_.ContinuousMultilinearMap.instFiniteDimensional [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (n : ℕ) : FiniteDimensional ℝ (E [×n]→L[ℝ] F) :=
  Module.Finite.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {β' : ℝ≥0}

/-- The **Arzelà–Ascoli theorem** for a sequence of Hölder functions. Let $E$ and $F$ be
finite-dimensional and $\Omega$ bounded. Let $H_n$ be bounded continuous functions on
$\overline{\Omega}$ with values in the $i$-linear maps $E^i \to F$, with $\|H_n\|_\infty \le M$,
and $\theta$-Hölder with a common constant $C$, where $\theta > 0$. Then the closure of the set
$\{H_n\}$ is compact. -/
theorem isCompact_closure_range_of_holderWith (hb : Bornology.IsBounded (Ω : Set E)) {i : ℕ}
    (H : ℕ → closure (Ω : Set E) →ᵇ (E [×i]→L[ℝ] F)) {M : ℝ} (hM : ∀ n, ‖H n‖ ≤ M) {C θ : ℝ≥0}
    (hθ : 0 < θ) (hH : ∀ n, HolderWith C θ (H n)) : IsCompact (closure (range H)) := by
  have : CompactSpace (closure (Ω : Set E)) := isCompact_iff_compactSpace.1 hb.isCompact_closure
  refine BoundedContinuousFunction.arzela_ascoli (closedBall 0 M) (isCompact_closedBall 0 M) _
    (fun f x hf ↦ ?_) ?_
  · obtain ⟨n, rfl⟩ := hf
    exact mem_closedBall_zero_iff.2 ((BoundedContinuousFunction.norm_coe_le_norm _ x).trans (hM n))
  · refine Metric.equicontinuous_of_continuity_modulus (fun d ↦ C * d ^ (θ : ℝ)) ?_ _ ?_
    · have h := (Real.continuous_rpow_const θ.coe_nonneg).tendsto 0
      rw [Real.zero_rpow (by exact_mod_cast hθ.ne')] at h
      simpa using h.const_mul (C : ℝ)
    · rintro x y ⟨_, ⟨n, rfl⟩⟩
      exact (hH n).dist_le x y

/-- The difference of two functions that are $\beta$-Hölder with constant $C$ is $\beta$-Hölder with
constant $2C$. -/
theorem holderWith_sub {X G : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup G]
    {g h : X → G} {C : ℝ≥0} (hg : HolderWith C β g) (hh : HolderWith C β h) :
    HolderWith (2 * C) β (g - h) :=
  holderWith_of_dist_le fun x y ↦ by
    rw [dist_eq_norm, Pi.sub_apply, Pi.sub_apply, sub_sub_sub_comm, NNReal.coe_mul,
      NNReal.coe_ofNat]
    calc ‖g x - g y - (h x - h y)‖ ≤ ‖g x - g y‖ + ‖h x - h y‖ := norm_sub_le _ _
      _ ≤ C * dist x y ^ (β : ℝ) + C * dist x y ^ (β : ℝ) := by
          rw [← dist_eq_norm, ← dist_eq_norm]
          exact add_le_add (hg.dist_le x y) (hh.dist_le x y)
      _ = 2 * C * dist x y ^ (β : ℝ) := by ring

/-- The **Arzelà–Ascoli theorem in $C^{j,\beta}(\overline{\Omega})$, with Hölder interpolation**.
Let $E$ and $F$ be finite-dimensional, let $\Omega$ be bounded, and let $0 < \beta' < \beta$.
Let $(u_n)$ be a sequence of $C^{j,\beta}(\overline{\Omega})$ with $\|u_n\| \le M$. Suppose that
for each $i < j$ there are $C \ge 0$ and $\theta > 0$ such that every $D^i u_n$ is
$\theta$-Hölder with constant $C$. Then there are a strictly increasing
$\varphi : \mathbb{N} \to \mathbb{N}$ and $w \in C^{j,\beta'}(\overline{\Omega})$ such that
$u_{\varphi(n)} \to w$ in $C^{j,\beta'}(\overline{\Omega})$.

Each entry has a uniformly convergent subsequence by the Arzelà–Ascoli theorem. The limit tuple
is a derivative tuple with $\beta$-Hölder top entry. The $\beta'$-Hölder seminorm of the
difference $d$ tends to $0$ by the interpolation $[d]_{\beta'} \le (2 \|d\|_\infty)^{1 -
\beta'/\beta} [d]_\beta^{\beta'/\beta}$. The convergence is of
`HolderSpace.toLower hb hβ.le (u (φ n))`. -/
theorem exists_subseq_tendsto_toLower (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : 0 < β')
    (hβ : β' < β) (u : ℕ → HolderSpace Ω F j β) {M : ℝ} (hM : ∀ n, ‖u n‖ ≤ M)
    (hlow : ∀ i : Fin (j + 1), (i : ℕ) < j →
      ∃ C θ : ℝ≥0, 0 < θ ∧ ∀ n, HolderWith C θ ((u n).deriv i)) :
    ∃ (φ : ℕ → ℕ) (w : HolderSpace Ω F j β'), StrictMono φ ∧
      Tendsto (fun n ↦ toLower hb hβ.le (u (φ n))) atTop (𝓝 w) := by
  have hβ0 : 0 < β := hβ'.trans hβ
  have hMn : ∀ n, ‖u n‖₊ ≤ M.toNNReal := fun n ↦
    NNReal.coe_le_coe.1 (by rw [coe_nnnorm]; exact (hM n).trans (Real.le_coe_toNNReal _))
  -- each entry is uniformly bounded and uniformly Hölder
  have hall : ∀ i : Fin (j + 1), ∃ C θ : ℝ≥0, 0 < θ ∧ ∀ n, HolderWith C θ ((u n).deriv i) := by
    intro i
    rcases Nat.lt_or_ge (i : ℕ) j with hi | hi
    · exact hlow i hi
    · obtain rfl : i = Fin.last j := Fin.ext (le_antisymm (Nat.lt_succ_iff.1 i.2) hi)
      exact ⟨M.toNNReal, β, hβ0, fun n ↦ (holderWith_norm (u n)).mono (hMn n)⟩
  have hK : ∀ i : Fin (j + 1), IsCompact (closure (range fun n ↦ (u n).deriv i)) := fun i ↦ by
    obtain ⟨C, θ, hθ, hC⟩ := hall i
    exact isCompact_closure_range_of_holderWith hb (fun n ↦ (u n).deriv i)
      (fun n ↦ (norm_deriv_le (u n) i).trans (hM n)) hθ hC
  -- a subsequence converging entrywise, by compactness of the product
  obtain ⟨L, -, φ, hφ, hLφ⟩ := (isCompact_univ_pi hK).tendsto_subseq
    (x := fun n ↦ (u n).deriv) fun n ↦ Set.mem_univ_pi.2 fun i ↦ subset_closure ⟨n, rfl⟩
  have hL : ∀ i, Tendsto (fun n ↦ (u (φ n)).deriv i) atTop (𝓝 (L i)) := fun i ↦
    tendsto_pi_nhds.1 hLφ i
  -- the limit is in the space
  have hLh : HolderWith M.toNNReal β (L (Fin.last j)) :=
    holderWith_of_tendsto (hL (Fin.last j)) fun n ↦ (holderWith_norm (u (φ n))).mono (hMn _)
  obtain ⟨D, hD⟩ := exists_holderWith_of_le hb hβ.le hLh
  obtain ⟨w, hw⟩ : ∃ w : HolderSpace Ω F j β', w.deriv = L :=
    ⟨⟨L, IsDerivTuple.of_tendsto (fun n ↦ (u (φ n)).isDerivTuple) hL, _, hD⟩, rfl⟩
  refine ⟨φ, w, hφ, ?_⟩
  -- the convergence in `C^{j,β'}`: the sup norms and the interpolated Hölder seminorm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun n ↦ ∑ i, ‖(u (φ n)).deriv i - w.deriv i‖) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin (j + 1))) fun i _ ↦
      tendsto_iff_norm_sub_tendsto_zero.1 (hw ▸ hL i)
    simpa using this
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : ℝ≥0, t₁ = 1 - β' / β := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t₂ : ℝ≥0, t₂ = β' / β := ⟨_, rfl⟩
  have ht₁0 : 0 < (t₁ : ℝ) := by
    rw [ht₁, NNReal.coe_sub (div_le_one_of_le₀ hβ.le β.coe_nonneg), NNReal.coe_div, NNReal.coe_one,
      sub_pos, div_lt_one (by exact_mod_cast hβ0)]
    exact_mod_cast hβ
  have h2 : Tendsto (fun n ↦ ((2 * ‖(u (φ n)).deriv (Fin.last j) - w.deriv (Fin.last j)‖).toNNReal
      : ℝ) ^ (t₁ : ℝ) * ((2 * M.toNNReal : ℝ≥0) : ℝ) ^ (t₂ : ℝ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n ↦ (2 * ‖(u (φ n)).deriv (Fin.last j) - w.deriv (Fin.last j)‖).toNNReal
        : ℕ → ℝ) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 (hw ▸ hL (Fin.last j))).const_mul 2
      rw [mul_zero] at this
      refine (this.congr fun n ↦ ?_)
      rw [Real.coe_toNNReal _ (by positivity)]
    have hr := ((Real.continuous_rpow_const ht₁0.le).tendsto 0).comp h0
    rw [Function.comp_def, Real.zero_rpow ht₁0.ne'] at hr
    simpa using hr.mul_const _
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (by simpa only [add_zero] using h1.add h2)
  rw [norm_def]
  simp only [deriv_toLower, deriv_sub]
  refine add_le_add le_rfl ?_
  -- the interpolation
  have hsub : HolderWith (2 * M.toNNReal) β
      ((u (φ n)).deriv (Fin.last j) - w.deriv (Fin.last j)) :=
    holderWith_sub ((holderWith_norm (u (φ n))).mono (hMn _)) (hw ▸ hLh)
  have hA : ∀ x y, ‖((u (φ n)).deriv (Fin.last j) - w.deriv (Fin.last j)) x
      - ((u (φ n)).deriv (Fin.last j) - w.deriv (Fin.last j)) y‖
      ≤ (2 * ‖(u (φ n)).deriv (Fin.last j) - w.deriv (Fin.last j)‖).toNNReal := fun x y ↦ by
    rw [Real.coe_toNNReal _ (by positivity), two_mul]
    exact (norm_sub_le _ _).trans (add_le_add (BoundedContinuousFunction.norm_coe_le_norm _ x)
      (BoundedContinuousFunction.norm_coe_le_norm _ y))
  have hint := HolderWith.of_le_of_forall_norm_sub_le hβ0 hβ.le hA hsub
  rw [← ht₁, ← ht₂] at hint
  have := hint.holderSeminorm_le
  rwa [NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_rpow, FunLike.coe_sub] at this

/-- The **compact embedding** $C^{j,\beta}(\overline{\Omega}) \hookrightarrow\hookrightarrow
C^{j,\beta'}(\overline{\Omega})$. Let $E$ and $F$ be finite-dimensional, let $\Omega$ be
bounded, and let $0 < \beta' < \beta$. Suppose that for each $i < j$ there are $C \ge 0$ and
$\theta > 0$ such that, for every $u \in C^{j,\beta}(\overline{\Omega})$,
$$\|D^i u(x) - D^i u(y)\| \le C \|u\| \, \|x - y\|^\theta \quad \text{for all } x, y \in
  \overline{\Omega}.$$
Then the inclusion $C^{j,\beta}(\overline{\Omega}) \to C^{j,\beta'}(\overline{\Omega})$ is a
compact embedding. This is the Hölder-space part of Theorem 7.3.8 (c) of [han2009theoretical].

The condition on the derivatives of order less than $j$ is empty for $j = 0$. It holds on convex
sets by the mean value inequality, and on Sobolev extension domains by Morrey's theorem. On an
arbitrary bounded open set it can fail, because a function with bounded gradient need not be
uniformly continuous up to the boundary. The relation is `IsCompactEmbedding`. -/
theorem isCompactEmbedding_toLowerL (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : 0 < β')
    (hβ : β' < β) (hlow : ∀ i : Fin (j + 1), (i : ℕ) < j → ∃ C θ : ℝ≥0, 0 < θ ∧
      ∀ u : HolderSpace Ω F j β, HolderWith (C * ‖u‖₊) θ (u.deriv i)) :
    IsCompactEmbedding (toLowerL Ω F j hb hβ.le).toLinearMap := by
  refine ⟨isContinuousEmbedding_toLowerL hb hβ.le, fun u ⟨M, hM⟩ ↦ ?_⟩
  obtain ⟨φ, w, hφ, hw⟩ := exists_subseq_tendsto_toLower hb hβ' hβ u hM fun i hi ↦ by
    obtain ⟨C, θ, hθ, hC⟩ := hlow i hi
    refine ⟨C * M.toNNReal, θ, hθ, fun n ↦ (hC (u n)).mono ?_⟩
    gcongr
    exact NNReal.coe_le_coe.1 (by rw [coe_nnnorm]; exact (hM n).trans (Real.le_coe_toNNReal _))
  exact ⟨φ, w, hφ, hw⟩

/-- A bounded linear map into $C^{j,\beta}(\overline{\Omega})$ whose images have uniformly Hölder
lower-order derivatives is a **compact embedding into** $C^{j,\beta'}(\overline{\Omega})$. Let
$E$ and $F$ be finite-dimensional, let $\Omega$ be bounded, and let $0 < \beta' < \beta$. Let
$V$ be a real normed space and let $T : V \to C^{j,\beta}(\overline{\Omega})$ be an injective
bounded linear map. Suppose that for each $i < j$ there are $C \ge 0$ and $\theta > 0$ such
that, for every $v \in V$, $D^i(Tv)$ is $\theta$-Hölder with constant $C \|v\|$. Then
$v \mapsto Tv$, viewed in $C^{j,\beta'}(\overline{\Omega})$, is a compact embedding of $V$.

This is the form in which the compact Sobolev embedding $W^{m,p}(\Omega)
\hookrightarrow\hookrightarrow C^{k,\beta'}(\overline{\Omega})$ is proved. There the uniform
Hölder continuity of the lower derivatives comes from the embedding theorem at the lower orders. -/
theorem isCompactEmbedding_toLowerL_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : 0 < β') (hβ : β' < β)
    (T : V →L[ℝ] HolderSpace Ω F j β) (hT : Function.Injective T)
    (hlow : ∀ i : Fin (j + 1), (i : ℕ) < j → ∃ C θ : ℝ≥0, 0 < θ ∧
      ∀ v, HolderWith (C * ‖v‖₊) θ ((T v).deriv i)) :
    IsCompactEmbedding ((toLowerL Ω F j hb hβ.le).comp T).toLinearMap := by
  refine ⟨⟨(toLower_injective hb hβ.le).comp hT, _,
    ((toLowerL Ω F j hb hβ.le).comp T).le_opNorm⟩, fun v ⟨M, hM⟩ ↦ ?_⟩
  have hM' : ∀ n, ‖T (v n)‖ ≤ ‖T‖ * M := fun n ↦
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM n) (norm_nonneg _))
  obtain ⟨φ, w, hφ, hw⟩ := exists_subseq_tendsto_toLower hb hβ' hβ (fun n ↦ T (v n)) hM'
    fun i hi ↦ by
      obtain ⟨C, θ, hθ, hC⟩ := hlow i hi
      refine ⟨C * M.toNNReal, θ, hθ, fun n ↦ (hC (v n)).mono ?_⟩
      gcongr
      exact NNReal.coe_le_coe.1 (by rw [coe_nnnorm]; exact (hM n).trans (Real.le_coe_toNNReal _))
  exact ⟨φ, w, hφ, hw⟩

/-- The **compact embedding** $C^{0,\beta}(\overline{\Omega}) \hookrightarrow\hookrightarrow
C^{0,\beta'}(\overline{\Omega})$ for $0 < \beta' < \beta$, with $E$ and $F$ finite-dimensional
and $\Omega$ bounded. No further condition is needed. -/
theorem isCompactEmbedding_toLowerL_zero (hb : Bornology.IsBounded (Ω : Set E)) (hβ' : 0 < β')
    (hβ : β' < β) :
    IsCompactEmbedding (toLowerL Ω F 0 hb hβ.le).toLinearMap :=
  isCompactEmbedding_toLowerL hb hβ' hβ fun _ hi ↦ absurd hi (Nat.not_lt_zero _)

end Compact

end HolderSpace

end Space
