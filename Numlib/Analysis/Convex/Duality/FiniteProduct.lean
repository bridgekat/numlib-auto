/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.InnerPairing
import Numlib.Analysis.Convex.Duality.RelintSeparation

/-!
# Convex analysis on a finite product

Let $E$ and $F$ be real vector spaces paired by $\langle x, y \rangle$, and let $\iota$ be a finite
index type. The product $E^\iota$ is paired with $F^\iota$ by $\langle x, y \rangle = \sum_i \langle
x_i, y_i \rangle$. For this pairing, product sets, separable sums of functions and, when $E$ is
finite-dimensional, relative interiors are computed coordinatewise. The support function of
$\prod_i C_i$ is $y \mapsto \sum_i \delta^*(y_i \mid C_i)$, the conjugate of
$x \mapsto \sum_i f_i(x_i)$ is $y \mapsto \sum_i f_i^*(y_i)$, and $\operatorname{ri} \prod_i C_i =
\prod_i \operatorname{ri} C_i$ (`Convex.relint_univ_pi`).

The module then reads one theorem through this dictionary. A finite family of nonempty convex sets
$C_i \subseteq E$ has a common relative interior point exactly when there is no family $(y_i)$ in
$F$ with $\sum_i y_i = 0$, $\sum_i \delta^*(y_i \mid C_i) \le 0$ and
$\sum_i \delta^*(-y_i \mid C_i) > 0$. This is Corollary 16.2.2 of [rockafellar1970convex]; the
material also uses §6 and §13 there.

## Main definitions

* `ConvexAnalysis.piPairing`: the pairing $\langle x, y \rangle = \sum_i \langle x_i, y_i \rangle$
  of $E^\iota$ with $F^\iota$, with instances for the four pairing classes. It is to `Set.pi` what
  `ConvexAnalysis.prodPairing` is to the product of two sets.

## Main results

* `ConvexAnalysis.supportFn_univ_pi`: the support function of a product set is the sum of the
  support functions of the factors.
* `ConvexAnalysis.convexConj_piFn`: the conjugate of a separable sum of proper functions is the
  separable sum of the conjugates, $(x \mapsto \sum_i f_i(x_i))^* = (y \mapsto \sum_i f_i^*(y_i))$.
* `ConvexAnalysis.iInter_relint_nonempty_iff_supportFn`: a finite family of nonempty convex sets has
  a common relative interior point exactly when no family $y$ with $\sum_i y_i = 0$ has $\sum_i
  \delta^*(y_i \mid C_i) \le 0 < \sum_i \delta^*(-y_i \mid C_i)$.
* `ConvexAnalysis.iInter_relint_convexDom_nonempty_iff`: the same criterion for the effective
  domains of proper convex functions, with the recession functions of the conjugates in place of the
  support functions.

## Proof outline

The diagonal $\{x : x_1 = \dots = x_m\}$ is a subspace of $E^\iota$. Its annihilator under the
product pairing is the set of families $y$ with $\sum_i y_i = 0$. So the criterion for a common
relative interior point is the subspace criterion
`ConvexAnalysis.submodule_inter_relint_nonempty_iff_supportFn` of
`Numlib.Analysis.Convex.Duality.RelintSeparation`, applied to the diagonal and the product set
$\prod_i C_i$.

## Implementation notes

* `ConvexAnalysis.piPairing` sums over `Finset.univ`, so the index type is a `Fintype`.
* The product is not dependent, because the diagonal subspace needs all factors to be the same
  space. The results about `Set.pi` would hold without change for a dependent product.
* `ConvexAnalysis.supportFn_univ_pi` needs no nonemptiness hypothesis, because $-\infty$ absorbs in
  a sum. When a factor is empty, both sides are $-\infty$, for different reasons: on the left the
  product set is empty, and on the right one summand is $-\infty$.
-/

open Set

namespace ConvexAnalysis

/-! ### The pairing of a finite product -/

section Pairing

variable {ι E F : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **product pairing** of $E^\iota$ with $F^\iota$, for a finite index type $\iota$: $$\langle
x, y \rangle = \sum_{i \in \iota} \langle x_i, y_i \rangle.$$ It is the analogue of
`ConvexAnalysis.prodPairing` for a finite family. Under this pairing a product of sets has a
separable support function (`ConvexAnalysis.supportFn_univ_pi`). -/
def piPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) : (ι → E) →ₗ[ℝ] (ι → F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i, B (x i) (y i))
    (fun _ _ _ => by simp [← Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum])
    (fun _ _ _ => by simp [← Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum])

/-- The value of the product pairing: $\langle x, y \rangle = \sum_i \langle x_i, y_i \rangle$. -/
@[simp] theorem piPairing_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (x : ι → E) (y : ι → F) :
    piPairing B x y = ∑ i, B (x i) (y i) := rfl

/-- The flip of the product pairing is the product pairing of the flipped pairing:
$(y, x) \mapsto \sum_i \langle x_i, y_i \rangle$. -/
theorem piPairing_flip (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    (piPairing (ι := ι) B).flip = piPairing B.flip :=
  LinearMap.ext fun _ => LinearMap.ext fun _ => by simp

end Pairing

section PairingInstances

variable {ι E F : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F]

/-- If each map $x \mapsto \langle x, y \rangle$ is continuous on $E$, then each map
$x \mapsto \sum_i \langle x_i, y_i \rangle$ is continuous on $E^\iota$ with the product
topology. -/
instance instIsContinuousPairingPi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsContinuousPairing B] :
    IsContinuousPairing (piPairing (ι := ι) B) where
  continuous_left y := by
    simp only [piPairing_apply]
    exact continuous_finsetSum _ fun i _ => (continuous_pairing B (y i)).comp (continuous_apply i)

/-- If the continuous linear functionals on $E$ are exactly the maps
$x \mapsto \langle x, y \rangle$ with $y \in F$, then the continuous linear functionals on
$E^\iota$ are exactly the maps $x \mapsto \sum_i \langle x_i, y_i \rangle$ with $y \in F^\iota$. -/
instance instIsCompatiblePairingPi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B] :
    IsCompatiblePairing (piPairing (ι := ι) B) where
  toIsContinuousPairing := instIsContinuousPairingPi B
  surjective_eval g := by
    classical
    choose y hy using fun i : ι =>
      exists_pairing_eq B (g.comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i))
    refine ⟨y, ContinuousLinearMap.ext fun x => ?_⟩
    rw [evalCLM_apply, piPairing_apply,
      ← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => E) g x]
    exact Finset.sum_congr rfl fun i _ => (hy i (x i)).symm

end PairingInstances

section InnerInstances

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] {B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ}

/-- If a pairing of $E$ with itself is symmetric and positive definite, then so is the product
pairing of $E^\iota$ with itself. The product carries no inner product structure of its own, but
the pairing does not need one. -/
instance isInnerPairing_piPairing [IsInnerPairing B] : IsInnerPairing (piPairing (ι := ι) B) where
  pairing_comm _ _ := Finset.sum_congr rfl fun i _ => pairing_comm B _ _
  self_nonneg _ := Finset.sum_nonneg fun i _ => self_pairing_nonneg B _
  eq_zero_of_self_eq_zero x h := by
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      fun i _ => self_pairing_nonneg B (x i)).1 h
    funext i
    exact self_pairing_eq_zero_iff.1 (hzero i (Finset.mem_univ i))

/-- If a symmetric positive definite pairing of $E$ with itself has a continuous quadratic form
$x \mapsto \langle x, x \rangle$, then the quadratic form
$x \mapsto \sum_i \langle x_i, x_i \rangle$ of the product pairing is continuous on $E^\iota$. -/
instance isContinuousInnerPairing_piPairing [TopologicalSpace E] [IsContinuousInnerPairing B] :
    IsContinuousInnerPairing (piPairing (ι := ι) B) where
  continuous_self :=
    continuous_finsetSum _ fun i _ => (continuous_self_pairing' B).comp (continuous_apply i)

end InnerInstances

/-!
### The relative interior of a product set

For finite-dimensional $E$, the relative interior of a product of convex sets is the product of the
relative interiors. This result is `Convex.relint_univ_pi` in
`Numlib.Analysis.Convex.RelativeInterior`.
-/

section Relint

variable {ι E : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

end Relint

/-! ### The support function of a product set

The supremum of a separable sum over a product of sets is the sum of the suprema. -/

section Support

variable {ι E F : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **The support function of a product set.** Let $\iota$ be finite and $C_i \subseteq E$ for
$i \in \iota$. Then for every $y \in F^\iota$, $$\delta^*\Bigl(y \Bigm| \prod_i C_i\Bigr) =
\sum_i \delta^*(y_i \mid C_i),$$ where the support function on the left is taken with respect to
the product pairing. No hypothesis is needed. If some $C_i$ is empty, both sides are $-\infty$.

The support function is `ConvexAnalysis.supportFn`, with $\delta^*(y \mid C) = \sup_{x \in C}
\langle x, y \rangle$. -/
theorem supportFn_univ_pi (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : ι → Set E) (y : ι → F) :
    supportFn (piPairing B) (univ.pi C) y = ∑ i, supportFn B (C i) (y i) := by
  classical
  by_cases hne : ∀ i, (C i).Nonempty
  · have hcoe : ∀ x : ι → E,
        ((piPairing B x y : ℝ) : EReal) = ∑ i, ((B (x i) (y i) : ℝ) : EReal) := fun x => by
      rw [piPairing_apply, EReal.coe_sum]
    rw [supportFn_apply]
    simp only [hcoe, supportFn_apply]
    exact EReal.biSup_sum_univ_pi hne (fun i z => ((B z (y i) : ℝ) : EReal))
      (fun i z _ => EReal.coe_ne_bot _) Finset.univ
  · simp only [not_forall, Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨i₀, hi₀⟩ := hne
    have hempty : univ.pi C = ∅ := Set.univ_pi_eq_empty_iff.2 ⟨i₀, hi₀⟩
    rw [← Finset.add_sum_erase _ (fun i => supportFn B (C i) (y i)) (Finset.mem_univ i₀), hi₀]
    simp only [hempty, supportFn_empty]
    exact (EReal.bot_add _).symm

end Support

/-!
### The conjugate of a separable sum

This is the other half of the finite-product dictionary. The difference
$\langle x, y \rangle - \sum_i f_i(x_i)$ splits as $\sum_i (\langle x_i, y_i \rangle - f_i(x_i))$
only after the case of a value $+\infty$ is handled, and the absorption of $-\infty$ handles it.
-/

section Separable

variable {ι E F : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **The conjugate of a separable sum.** Let $\iota$ be finite, and let
$f_i : E \to [-\infty, +\infty]$ be proper for each $i \in \iota$. Then for every
$y \in F^\iota$, $$\Bigl(x \mapsto \sum_i f_i(x_i)\Bigr)^*(y) = \sum_i f_i^*(y_i),$$ where the
conjugate on the left is taken with respect to the product pairing.

Properness keeps the two sides away from $\infty - \infty$. It lets the supremum that defines
$f_i^*$ be taken over $\operatorname{dom} f_i$, and it keeps each $f_i^*(y_i)$ different from
$-\infty$, so no summand on the right absorbs the others. -/
theorem convexConj_piFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : ι → E → EReal) (hf : ∀ i, ProperConvex (f i))
    (y : ι → F) :
    convexConj (piPairing B) (fun x => ∑ i, f i (x i)) y = ∑ i, convexConj B (f i) (y i) := by
  have hbot : ∀ i z, f i z ≠ ⊥ := fun i z => (hf i).ne_bot z
  have hoff : ∀ i, ∀ z ∉ convexDom (f i), (((B z (y i) : ℝ) : EReal) - f i z) = ⊥ := by
    intro i z hz
    have hz' : ¬ (f i z < ⊤) := hz
    rw [top_le_iff.1 (not_lt.1 hz'), EReal.sub_top]
  have hval : ∀ i, ∀ z ∈ convexDom (f i), (((B z (y i) : ℝ) : EReal) - f i z) ≠ ⊥ := by
    intro i z hz
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot i z) hz
    rw [hr, ← EReal.coe_sub]
    exact EReal.coe_ne_bot _
  have hcoord : ∀ i, convexConj B (f i) (y i)
      = ⨆ z ∈ convexDom (f i), (((B z (y i) : ℝ) : EReal) - f i z) :=
    fun i => by rw [convexConj_apply, iSup_split _ (· ∈ convexDom (f i)),
      iSup₂_eq_bot.2 (hoff i), sup_bot_eq]
  have hsplit : ∀ x : ι → E, ((piPairing B x y : ℝ) : EReal) - (∑ i, f i (x i))
      = ∑ i, (((B (x i) (y i) : ℝ) : EReal) - f i (x i)) := by
    intro x
    rw [piPairing_apply, EReal.coe_sum]
    exact EReal.sum_sub_sum Finset.univ _ (fun i => f i (x i)) fun i _ => hbot i (x i)
  have hprod : convexConj (piPairing B) (fun x => ∑ i, f i (x i)) y
      = ⨆ x ∈ univ.pi fun i => convexDom (f i), ∑ i,
          (((B (x i) (y i) : ℝ) : EReal) - f i (x i)) := by
    rw [convexConj_apply]
    simp only [hsplit]
    rw [iSup_split _ (· ∈ univ.pi fun i => convexDom (f i)),
      sup_eq_left.2 (iSup₂_le fun x hx => ?_)]
    obtain ⟨i₀, -, hi₀⟩ : ∃ i₀ ∈ (univ : Set ι), x i₀ ∉ convexDom (f i₀) := by
      simpa [Set.mem_pi] using hx
    exact (WithBot.sum_eq_bot_iff.2 ⟨i₀, Finset.mem_univ i₀, hoff i₀ (x i₀) hi₀⟩).le.trans bot_le
  rw [hprod]
  simp only [hcoord]
  exact EReal.biSup_sum_univ_pi (fun i => (hf i).convexDom_nonempty)
    (fun i z => ((B z (y i) : ℝ) : EReal) - f i z) hval Finset.univ

end Separable

/-!
### A common relative interior point of a finite family

The diagonal $\{x : x_1 = \dots = x_m\}$ is a subspace of $E^\iota$. Its annihilator under the
product pairing is the set of families $y$ with $\sum_i y_i = 0$.
-/

section Diagonal

variable {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}
  [IsCompatiblePairing B]

/-- **A common relative interior point of a finite family of convex sets.** Let $E$ be a
finite-dimensional real normed space, and let the continuous linear functionals on $E$ be
exactly the maps $x \mapsto \langle x, y \rangle$ with $y \in F$. Suppose that the pairing
separates the points of $F$: if $\langle x, y \rangle = 0$ for all $x \in E$, then $y = 0$. Let
$\iota$ be finite, and let $C_i \subseteq E$ be nonempty and convex for each $i \in \iota$. Then
$\bigcap_i \operatorname{ri} C_i \ne \emptyset$ if and only if there is no family
$(y_i)_{i \in \iota}$ in $F$ with $$\sum_i y_i = 0, \qquad \sum_i \delta^*(y_i \mid C_i) \le 0,
\qquad \sum_i \delta^*(-y_i \mid C_i) > 0.$$ This is Corollary 16.2.2 of
[rockafellar1970convex].

The separation hypothesis is `B.SeparatingRight`, and $\operatorname{ri}$ is
`intrinsicInterior ℝ`. The proof applies
`ConvexAnalysis.submodule_inter_relint_nonempty_iff_supportFn` in $E^\iota$ to the diagonal
subspace and the product set $\prod_i C_i$. The separation hypothesis turns the annihilator of
the diagonal into the condition $\sum_i y_i = 0$. -/
theorem iInter_relint_nonempty_iff_supportFn (hB : B.SeparatingRight) (C : ι → Set E)
    (hC : ∀ i, Convex ℝ (C i)) (hne : ∀ i, (C i).Nonempty) :
    (⋂ i, ri (C i)).Nonempty ↔
      ¬ ∃ y : ι → F, (∑ i, y i = 0) ∧ (∑ i, supportFn B (C i) (y i)) ≤ 0 ∧
        0 < ∑ i, supportFn B (C i) (-(y i)) := by
  obtain ⟨L, hL⟩ : ∃ L : Submodule ℝ (ι → E), ∀ x : ι → E, x ∈ L ↔ ∃ z : E, ∀ i, x i = z := by
    refine ⟨LinearMap.range (LinearMap.pi fun _ : ι => LinearMap.id), fun x => ?_⟩
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, fun _ => rfl⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, funext fun i => (hz i).symm⟩
  have hstep := submodule_inter_relint_nonempty_iff_supportFn (B := piPairing B) L
    (convex_pi fun i _ => hC i) (Set.univ_pi_nonempty_iff.2 hne)
  rw [Convex.relint_univ_pi C hC] at hstep
  simp only [supportFn_univ_pi, Pi.neg_apply] at hstep
  have hleft : ((L : Set (ι → E)) ∩ univ.pi fun i => ri (C i)).Nonempty
      ↔ (⋂ i, ri (C i)).Nonempty := by
    constructor
    · rintro ⟨x, hxL, hxpi⟩
      obtain ⟨z, hz⟩ := (hL x).1 hxL
      refine ⟨z, mem_iInter.2 fun i => ?_⟩
      have hmem := hxpi i (mem_univ i)
      rwa [hz i] at hmem
    · rintro ⟨z, hz⟩
      rw [mem_iInter] at hz
      exact ⟨fun _ => z, (hL _).2 ⟨z, fun _ => rfl⟩, fun i _ => hz i⟩
  have hann : ∀ y : ι → F, (∀ x ∈ L, piPairing B x y = 0) ↔ ∑ i, y i = 0 := by
    intro y
    constructor
    · intro h
      refine hB _ fun z => ?_
      have hz := h (fun _ => z) ((hL _).2 ⟨z, fun _ => rfl⟩)
      rw [piPairing_apply] at hz
      rw [map_sum]
      exact hz
    · intro h x hx
      obtain ⟨z, hz⟩ := (hL x).1 hx
      have hval : ∑ i, B (x i) (y i) = B z (∑ i, y i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hz i]
      rw [piPairing_apply, hval, h, map_zero]
  rw [← hleft, hstep]
  exact not_congr (exists_congr fun y => and_congr_left' (hann y))

/-- **A common relative interior point of a finite family of effective domains.** Let $E$ be a
finite-dimensional real normed space, let the continuous linear functionals on $E$ be exactly
the maps $x \mapsto \langle x, y \rangle$ with $y \in F$, and suppose that the pairing separates
the points of $F$. Let $\iota$ be finite, and for each $i \in \iota$ let
$f_i : E \to [-\infty, +\infty]$ be a proper convex function whose conjugate $f_i^*$ is proper.
Then $\bigcap_i \operatorname{ri}(\operatorname{dom} f_i) \ne \emptyset$ if and only if there is
no family $(y_i)_{i \in \iota}$ in $F$ with $$\sum_i y_i = 0, \qquad \sum_i (f_i^* 0^+)(y_i) \le
0, \qquad \sum_i (f_i^* 0^+)(-y_i) > 0,$$ where $f_i^* 0^+$ is the recession function of
$f_i^*$.

This is `ConvexAnalysis.iInter_relint_nonempty_iff_supportFn` at $C_i = \operatorname{dom} f_i$,
whose support function is the recession function of $f_i^*$
(`ConvexAnalysis.recessionFn_convexConj`). -/
theorem iInter_relint_convexDom_nonempty_iff (hB : B.SeparatingRight) (f : ι → E → EReal)
    (hf : ∀ i, ConvexFn (f i)) (hp : ∀ i, ProperConvex (f i))
        (hc : ∀ i, ProperConvex (convexConj B (f i))) :
    (⋂ i, ri (convexDom (f i))).Nonempty ↔
      ¬ ∃ y : ι → F, (∑ i, y i = 0) ∧ (∑ i, recessionFn (convexConj B (f i)) (y i)) ≤ 0 ∧
        0 < ∑ i, recessionFn (convexConj B (f i)) (-(y i)) := by
  have hrec : ∀ i, recessionFn (convexConj B (f i)) = supportFn B (convexDom (f i)) :=
    fun i => recessionFn_convexConj (hp i) (hc i)
  simp only [hrec]
  exact iInter_relint_nonempty_iff_supportFn hB _ (fun i => (hf i).convex_convexDom)
    fun i => (hp i).convexDom_nonempty

end Diagonal

end ConvexAnalysis
