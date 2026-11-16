/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Operations.Basic
import Numlib.Analysis.Convex.Operations.Hull

/-!
# The complete lattice of convex functions

Let $E$ be a real vector space. The convex functions $E \to [-\infty, +\infty]$, ordered pointwise,
form a complete lattice. The least upper bound of a family is its pointwise supremum, because a
pointwise supremum of convex functions is convex. The greatest lower bound is not the pointwise
infimum, which need not be convex. It is the convex hull $\operatorname{conv}\{f_i\}$, the greatest
convex function below every $f_i$. The presentation follows [rockafellar1970convex], §5.

An example on $\mathbb{R}$ shows the difference. The indicator functions of $\{0\}$ and $\{1\}$ have
pointwise minimum $+\infty$ at $1/2$, but their meet is the indicator function of $[0, 1]$, which is
$0$ at $1/2$. So the inclusion of the convex functions into all functions preserves arbitrary
suprema but not infima.

## Main definitions

* `ConvexAnalysis.ConvexFns`: the type of convex functions on $E$, with the complete lattice
  structure `ConvexAnalysis.ConvexFns.instCompleteLattice`.
* `ConvexAnalysis.ConvexFns.coeOrderEmbedding`: the inclusion into $E \to [-\infty, +\infty]$ as an
  order embedding.
* `ConvexAnalysis.ConvexFns.coeSSupHom`: the inclusion as a map that preserves arbitrary suprema.

## Main results

* `ConvexAnalysis.ConvexFns.coe_sSup`, `ConvexAnalysis.ConvexFns.coe_sup`: the join is the pointwise
  supremum.
* `ConvexAnalysis.ConvexFns.coe_iInf`, `ConvexAnalysis.ConvexFns.coe_inf`: the meet is the convex
  hull `ConvexAnalysis.convFn`, and `ConvexAnalysis.convFn₂` for two functions.
* `ConvexAnalysis.ConvexFns.coe_top`, `ConvexAnalysis.ConvexFns.coe_bot`: the greatest and the least
  element are the constants $+\infty$ and $-\infty$.
* `ConvexAnalysis.ConvexFns.not_coe_inf_eq_inf`: the meet is not the pointwise minimum in general.

## Implementation notes

* `ConvexAnalysis.ConvexFns E` is a reducible abbreviation for the subtype of convex functions that
  `ConvexAnalysis.gci_val_convHullFn` is stated about. The coreflection then lifts to a
  `CompleteLattice` directly, and the order is definitionally the pointwise order.
-/

open Set

namespace ConvexAnalysis

/-! ### The type of convex functions -/

/-- The type of **convex functions on $E$**: the functions $f : E \to [-\infty, +\infty]$ with
convex epigraph, ordered pointwise. -/
abbrev ConvexFns (E : Type*) [AddCommGroup E] [Module ℝ E] := {f : E → EReal // ConvexFn f}

namespace ConvexFns

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The convex functions on $E$, ordered pointwise, form a **complete lattice**.

The instance transports the coreflection `ConvexAnalysis.gci_val_convHullFn` by
`GaloisCoinsertion.liftCompleteLattice`. So each lattice operation is the corresponding
operation on $E \to [-\infty, +\infty]$ followed by the convex hull `ConvexAnalysis.convHullFn`.
The lemmas below evaluate this hull. -/
noncomputable instance instCompleteLattice : CompleteLattice (ConvexFns E) :=
  gci_val_convHullFn.liftCompleteLattice

/-- The inclusion of the convex functions into $E \to [-\infty, +\infty]$ is an **order embedding**:
$f \le g$ in the lattice of convex functions if and only if $f(x) \le g(x)$ for every $x \in E$. -/
noncomputable def coeOrderEmbedding : ConvexFns E ↪o (E → EReal) := OrderEmbedding.subtype _

/-- The underlying function of `ConvexAnalysis.ConvexFns.coeOrderEmbedding` is the inclusion
`Subtype.val`. -/
@[simp]
theorem coe_coeOrderEmbedding :
    ⇑(coeOrderEmbedding : ConvexFns E ↪o (E → EReal)) = Subtype.val := rfl

/-- A function $g : E \to [-\infty, +\infty]$ is the underlying function of an element of the
lattice if and only if $g$ is convex. -/
@[simp]
theorem mem_range_coe {g : E → EReal} :
    g ∈ Set.range (Subtype.val : ConvexFns E → (E → EReal)) ↔ ConvexFn g :=
  ⟨fun ⟨f, hf⟩ => hf ▸ f.2, fun h => ⟨⟨g, h⟩, rfl⟩⟩

/-! ### Suprema: the join is pointwise -/

/-- **The least upper bound is the pointwise supremum.** For a set $s$ of convex functions on $E$,
the underlying function of $\sup s$ is $x \mapsto \sup_{f \in s} f(x)$.

This is the supremum $\sup\{f_i\}$ of [rockafellar1970convex]. -/
@[simp]
theorem coe_sSup (s : Set (ConvexFns E)) :
    ((sSup s : ConvexFns E) : E → EReal) = sSup (Subtype.val '' s) := by
  refine convHullFn_eq_self ?_
  have h : sSup (Subtype.val '' s) = fun x => ⨆ f : s, ((f : ConvexFns E) : E → EReal) x := by
    rw [sSup_image']
    exact funext fun x => iSup_apply
  rw [h]
  exact convexFn_iSup fun f : s => (f : ConvexFns E).2

/-- For a family $(f_i)$ of convex functions, the underlying function of $\bigsqcup_i f_i$ is the
pointwise supremum of the $f_i$. -/
theorem coe_iSup {ι : Sort*} (f : ι → ConvexFns E) :
    ((⨆ i, f i : ConvexFns E) : E → EReal) = ⨆ i, (f i : E → EReal) := by
  rw [iSup, coe_sSup, ← Set.range_comp]
  rfl

/-- For a family $(f_i)$ of convex functions and $x \in E$, the value of $\bigsqcup_i f_i$ at $x$ is
$\sup_i f_i(x)$. -/
@[simp]
theorem coe_iSup_apply {ι : Sort*} (f : ι → ConvexFns E) (x : E) :
    ((⨆ i, f i : ConvexFns E) : E → EReal) x = ⨆ i, (f i : E → EReal) x := by
  rw [coe_iSup, iSup_apply]

/-- For a set $s$ of convex functions and $x \in E$, the value of $\sup s$ at $x$ is
$\sup_{f \in s} f(x)$. -/
theorem coe_sSup_apply (s : Set (ConvexFns E)) (x : E) :
    ((sSup s : ConvexFns E) : E → EReal) x = ⨆ f ∈ s, (f : E → EReal) x := by
  rw [coe_sSup, sSup_image', iSup_apply, iSup_subtype]

/-- The join of two convex functions $f, g$ is their pointwise maximum
$x \mapsto \max\{f(x), g(x)\}$. -/
@[simp]
theorem coe_sup (f g : ConvexFns E) :
    ((f ⊔ g : ConvexFns E) : E → EReal) = (f : E → EReal) ⊔ (g : E → EReal) :=
  convHullFn_eq_self (f.2.sup g.2)

/-- The inclusion of the convex functions into $E \to [-\infty, +\infty]$, as a map that **preserves
arbitrary suprema** (an `sSupHom`).

There is no such map for infima: see `ConvexAnalysis.ConvexFns.not_coe_inf_eq_inf`. -/
noncomputable def coeSSupHom : sSupHom (ConvexFns E) (E → EReal) where
  toFun := Subtype.val
  map_sSup' := coe_sSup

/-- The underlying function of `ConvexAnalysis.ConvexFns.coeSSupHom` is the inclusion `Subtype.val`.
-/
@[simp]
theorem coe_coeSSupHom : ⇑(coeSSupHom : sSupHom (ConvexFns E) (E → EReal)) = Subtype.val := rfl

/-! ### Infima: the meet is a convex hull -/

/-- **The greatest lower bound is a convex hull.** For a set $s$ of convex functions, the underlying
function of $\inf s$ is the convex hull `ConvexAnalysis.convHullFn` of the pointwise infimum
$x \mapsto \inf_{f \in s} f(x)$. -/
theorem coe_sInf (s : Set (ConvexFns E)) :
    ((sInf s : ConvexFns E) : E → EReal) = convHullFn (sInf (Subtype.val '' s)) := rfl

/-- The greatest lower bound of a family $(f_i)$ of convex functions is their convex hull
$\operatorname{conv}\{f_i\}$ (`ConvexAnalysis.convFn`). It is not the pointwise infimum, which
in general is not convex.

This is the function $\operatorname{conv}\{f_i \mid i \in I\}$ of [rockafellar1970convex]. -/
@[simp]
theorem coe_iInf {ι : Sort*} (f : ι → ConvexFns E) :
    ((⨅ i, f i : ConvexFns E) : E → EReal) = convFn (fun i => (f i : E → EReal)) := by
  rw [convFn_eq_convHullFn_iInf, iInf, coe_sInf, ← Set.range_comp]
  refine congrArg convHullFn (funext fun x => ?_)
  change (⨅ i, (f i : E → EReal)) x = ⨅ i, (f i : E → EReal) x
  exact iInf_apply

/-- The meet of two convex functions $f, g$ is their convex hull $\operatorname{conv}\{f, g\}$
(`ConvexAnalysis.convFn₂`). -/
@[simp]
theorem coe_inf (f g : ConvexFns E) :
    ((f ⊓ g : ConvexFns E) : E → EReal) = convFn₂ (f : E → EReal) (g : E → EReal) :=
  convHullFn_inf _ _

/-- The meet of two convex functions lies below their pointwise minimum. In general it lies strictly
below: see `ConvexAnalysis.ConvexFns.exists_coe_inf_lt_inf`. -/
theorem coe_inf_le_inf (f g : ConvexFns E) :
    ((f ⊓ g : ConvexFns E) : E → EReal) ≤ (f : E → EReal) ⊓ (g : E → EReal) :=
  (coe_inf f g).trans_le (convFn₂_le_inf _ _)

/-! ### The extreme elements -/

/-- The greatest convex function is the constant $+\infty$. -/
@[simp]
theorem coe_top : ((⊤ : ConvexFns E) : E → EReal) = ⊤ :=
  convHullFn_eq_self (convexFn_const ⊤)

/-- The least convex function is the constant $-\infty$. -/
@[simp]
theorem coe_bot : ((⊥ : ConvexFns E) : E → EReal) = ⊥ :=
  convHullFn_eq_self (convexFn_const ⊥)

end Module

/-! ### The meet is not the pointwise infimum -/

/-- **The meet of two convex functions can be strictly below their pointwise minimum.** There are
convex functions $f, g : \mathbb{R} \to [-\infty, +\infty]$ and a point $x \in \mathbb{R}$ with
$(f \sqcap g)(x) < \min\{f(x), g(x)\}$.

The witnesses are the indicator functions of $\{0\}$ and $\{1\}$ at $x = 1/2$, as in
`ConvexAnalysis.convFn₂_indicatorFn_lt_inf`. -/
theorem exists_coe_inf_lt_inf :
    ∃ (f g : ConvexFns ℝ) (x : ℝ),
      ((f ⊓ g : ConvexFns ℝ) : ℝ → EReal) x < ((f : ℝ → EReal) ⊓ (g : ℝ → EReal)) x := by
  refine ⟨⟨indicatorFn ({0} : Set ℝ), convexFn_indicatorFn.2 (convex_singleton 0)⟩,
    ⟨indicatorFn ({1} : Set ℝ), convexFn_indicatorFn.2 (convex_singleton 1)⟩, 1 / 2, ?_⟩
  rw [coe_inf, Pi.inf_apply]
  exact convFn₂_indicatorFn_lt_inf

/-- **The inclusion of the convex functions does not preserve binary meets.** It is not true that
$f \sqcap g$ is the pointwise minimum of $f$ and $g$ for all convex
$f, g : \mathbb{R} \to [-\infty, +\infty]$.

So the inclusion is not an `sInfHom`, and not even a lattice homomorphism. Compare
`ConvexAnalysis.ConvexFns.coeSSupHom`. -/
theorem not_coe_inf_eq_inf :
    ¬ ∀ f g : ConvexFns ℝ,
      ((f ⊓ g : ConvexFns ℝ) : ℝ → EReal) = (f : ℝ → EReal) ⊓ (g : ℝ → EReal) := by
  obtain ⟨f, g, x, hx⟩ := exists_coe_inf_lt_inf
  exact fun h => absurd (congrFun (h f g) x) hx.ne

end ConvexFns

end ConvexAnalysis
