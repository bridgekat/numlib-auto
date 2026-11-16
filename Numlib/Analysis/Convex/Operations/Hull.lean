/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Join
import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.Convex.Operations.Epi

/-!
# The convex hull of a family of functions

Let $E$ be a real vector space. The pointwise infimum of a family of convex functions
$f_i : E \to [-\infty, +\infty]$ is in general not convex, and the convex hull takes its place. The
convex hull $\operatorname{conv}\{f_i\}$ is the function determined by the convex hull of the union
of the epigraphs, and it is the greatest convex function below every $f_i$. When the $f_i$ are
convex and never take the value $-\infty$, it is given by the formula
$$(\operatorname{conv}\{f_i\})(x) = \inf\Big\{\sum_i \lambda_i f_i(x_i) \Bigm|
  \lambda_i \ge 0,\ \sum_i \lambda_i = 1,\ \sum_i \lambda_i x_i = x\Big\},$$
over the convex combinations with finitely many nonzero coefficients. This is Theorem 5.6 of
[rockafellar1970convex]. The convex hull $\operatorname{conv} g$ of a single function is the
greatest convex function below $g$. The presentation follows [rockafellar1970convex], §5.

## Main definitions

* `ConvexAnalysis.convFn`: the convex hull $\operatorname{conv}\{f_i\}$ of a family, the infimum in
  the lattice of convex functions.
* `ConvexAnalysis.convHullFn`: the convex hull $\operatorname{conv} g$ of a single function, the
  coreflection onto the convex functions.
* `ConvexAnalysis.gci_val_convHullFn`: $\operatorname{conv}$ as a right adjoint of the inclusion of
  the convex functions, in the form of a `GaloisCoinsertion`.
* `ConvexAnalysis.convFn₂`: the convex hull $\operatorname{conv}\{f, g\}$ of two functions, the meet
  of two convex functions.

## Main results

* `ConvexAnalysis.convexFn_convFn`: the convex hull of a family is convex.
* `ConvexAnalysis.convFn_le`, `ConvexAnalysis.le_convFn`, `ConvexAnalysis.isGreatest_convFn`: the
  convex hull is the greatest convex function below every $f_i$. The other results of the module
  follow from this universal property.
* `ConvexAnalysis.convFn_le_iInf`: the convex hull lies below the pointwise infimum, in general
  strictly (`ConvexAnalysis.convFn₂_indicatorFn_lt_inf`).
* `ConvexAnalysis.convFn_eq_convHullFn_iInf`, `ConvexAnalysis.convFn_unit`: the convex hull of a
  family is the convex hull of its pointwise infimum, and the convex hull of one function is the
  convex hull of a one-element family.
* `ConvexAnalysis.convFn_apply`: the explicit formula above; `ConvexAnalysis.convFn₂_apply` is the
  form for two functions.
* `ConvexAnalysis.IsEpiLike.mem_convexHull_of_le`, `ConvexAnalysis.epi_convFn₂`,
  `ConvexAnalysis.isEpiLike_convexHull_epi_union`: these results describe when the infimum in the
  formula for two functions is attained. The set $\operatorname{epi}(\operatorname{conv}\{f, g\})$
  equals $\operatorname{conv}(\operatorname{epi} f \cup \operatorname{epi} g)$ exactly when this
  hull is an epigraph, and the hull can fail to be an epigraph only by failing to be closed.

## Implementation notes

* The two hulls determine each other (`ConvexAnalysis.convFn_eq_convHullFn_iInf`,
  `ConvexAnalysis.convFn_unit`) but have different roles: only `ConvexAnalysis.convHullFn` is an
  adjoint, and only `ConvexAnalysis.convFn` takes a family.
* With `ConvexAnalysis.gci_val_convHullFn`, the convex functions form a complete lattice with
  infimum `ConvexAnalysis.convFn` and pointwise supremum: see `ConvexAnalysis.ConvexFns`.
-/

open Set

namespace ConvexAnalysis


section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### The convex hull of a family -/

section Family

variable {ι : Sort*} {f : ι → E → EReal} {g : E → EReal}

/-- The **convex hull of a family of functions** $f_i : E \to [-\infty, +\infty]$: the function
determined (`ConvexAnalysis.ofEpi`) by the convex hull of the union of the epigraphs,
$$\operatorname{conv}\{f_i\} = \operatorname{ofEpi}\Big(\operatorname{conv} \bigcup_i
  \operatorname{epi} f_i\Big).$$

Equivalently (`ConvexAnalysis.isGreatest_convFn`), it is the greatest convex function $h$,
proper or not, with $h \le f_i$ for every $i$. -/
noncomputable def convFn (f : ι → E → EReal) : E → EReal :=
  ofEpi (convexHull ℝ (⋃ i, epi (f i)))

/-- The convex hull of a family of functions is a convex function, because the convex hull of a set
is convex. -/
theorem convexFn_convFn (f : ι → E → EReal) : ConvexFn (convFn f) :=
  convexFn_ofEpi (convex_convexHull ℝ _)

/-- The convex hull of a family of functions lies below each member:
$\operatorname{conv}\{f_i\} \le f_i$ for every $i$. -/
theorem convFn_le (f : ι → E → EReal) (i : ι) : convFn f ≤ f i := by
  have h : epi (f i) ⊆ convexHull ℝ (⋃ j, epi (f j)) :=
    (subset_iUnion (fun j => epi (f j)) i).trans (subset_convexHull ℝ _)
  have h' := ofEpi_mono h
  rwa [ofEpi_epi] at h'

/-- **The universal property.** If $g$ is convex and $g \le f_i$ for every $i$, then
$g \le \operatorname{conv}\{f_i\}$.

With `ConvexAnalysis.convFn_le` and `ConvexAnalysis.convexFn_convFn`, this makes the convex hull
the greatest convex function below every $f_i$. -/
theorem le_convFn (hg : ConvexFn g) (h : ∀ i, g ≤ f i) : g ≤ convFn f :=
  subset_epi_iff_le_ofEpi.1 (convexHull_min (iUnion_subset fun i => epi_anti (h i)) hg.convex_epi)

/-- The convex hull $\operatorname{conv}\{f_i\}$ is the greatest element of the set of convex
functions $g$ with $g \le f_i$ for every $i$. -/
theorem isGreatest_convFn (f : ι → E → EReal) :
    IsGreatest {g : E → EReal | ConvexFn g ∧ ∀ i, g ≤ f i} (convFn f) :=
  ⟨⟨convexFn_convFn f, convFn_le f⟩, fun _ hg => le_convFn hg.1 hg.2⟩

/-- The convex hull is monotone: if $f_i \le f'_i$ for every $i$, then $\operatorname{conv}\{f_i\}
\le \operatorname{conv}\{f'_i\}$. -/
theorem convFn_mono {f₁ f₂ : ι → E → EReal} (h : ∀ i, f₁ i ≤ f₂ i) : convFn f₁ ≤ convFn f₂ :=
  le_convFn (convexFn_convFn f₁) fun i => (convFn_le f₁ i).trans (h i)

/-- If the convex hull $\operatorname{conv} \bigcup_i \operatorname{epi} f_i$ is epi-like, then it
is the epigraph of $\operatorname{conv}\{f_i\}$.

The hull need not be epi-like: already for two functions, the infimum in the formula for
$\operatorname{conv}\{f_i\}$ need not be attained. -/
theorem epi_convFn (h : IsEpiLike (convexHull ℝ (⋃ i, epi (f i)))) :
    epi (convFn f) = convexHull ℝ (⋃ i, epi (f i)) :=
  epi_ofEpi h

/-- The convex hull lies below the pointwise infimum: $(\operatorname{conv}\{f_i\})(x) \le \inf_i
f_i(x)$ for every $x \in E$.

In general the inequality is strict (`ConvexAnalysis.convFn₂_indicatorFn_lt_inf`). This is the
reason for the notion of convex hull. -/
theorem convFn_le_iInf (f : ι → E → EReal) (x : E) : convFn f x ≤ ⨅ i, f i x :=
  le_iInf fun i => convFn_le f i x

/-- If the pointwise infimum $x \mapsto \inf_i f_i(x)$ is convex, then it is the convex hull
$\operatorname{conv}\{f_i\}$. -/
theorem convFn_eq_iInf (hc : ConvexFn fun x => ⨅ i, f i x) : convFn f = fun x => ⨅ i, f i x :=
  le_antisymm (fun x => convFn_le_iInf f x)
    (le_convFn hc fun i x => iInf_le (fun j => f j x) i)

end Family

/-! ### The convex hull of a single function -/

section Single

variable {g h : E → EReal}

/-- The **convex hull** $\operatorname{conv} g$ of a function $g : E \to [-\infty, +\infty]$: the
function determined by the convex hull of $\operatorname{epi} g$,
$$\operatorname{conv} g = \operatorname{ofEpi}(\operatorname{conv} \operatorname{epi} g).$$

It is the greatest convex function below $g$ (`ConvexAnalysis.isGreatest_convHullFn`). -/
noncomputable def convHullFn (g : E → EReal) : E → EReal := ofEpi (convexHull ℝ (epi g))

/-- The convex hull $\operatorname{conv} g$ of a function is convex. -/
theorem convexFn_convHullFn (g : E → EReal) : ConvexFn (convHullFn g) :=
  convexFn_ofEpi (convex_convexHull ℝ _)

/-- The convex hull of a function lies below the function: $\operatorname{conv} g \le g$. -/
theorem convHullFn_le (g : E → EReal) : convHullFn g ≤ g := by
  have h' := ofEpi_mono (subset_convexHull ℝ (epi g))
  rwa [ofEpi_epi] at h'

/-- **The universal property of $\operatorname{conv} g$.** If $h$ is convex and $h \le g$, then
$h \le \operatorname{conv} g$. -/
theorem le_convHullFn (hh : ConvexFn h) (hg : h ≤ g) : h ≤ convHullFn g :=
  subset_epi_iff_le_ofEpi.1 (convexHull_min (epi_anti hg) hh.convex_epi)

/-- The convex hull $\operatorname{conv} g$ is the greatest element of the set of convex functions
$h$ with $h \le g$. -/
theorem isGreatest_convHullFn (g : E → EReal) :
    IsGreatest {h : E → EReal | ConvexFn h ∧ h ≤ g} (convHullFn g) :=
  ⟨⟨convexFn_convHullFn g, convHullFn_le g⟩, fun _ hh => le_convHullFn hh.1 hh.2⟩

/-- The convex hull is monotone: $g \le h$ implies $\operatorname{conv} g \le \operatorname{conv}
h$. -/
theorem convHullFn_mono (hgh : g ≤ h) : convHullFn g ≤ convHullFn h :=
  le_convHullFn (convexFn_convHullFn g) ((convHullFn_le g).trans hgh)

/-- A convex function is its own convex hull: if $g$ is convex, then $\operatorname{conv} g = g$. -/
theorem convHullFn_eq_self (hg : ConvexFn g) : convHullFn g = g :=
  le_antisymm (convHullFn_le g) (le_convHullFn hg le_rfl)

/-- A function $g$ is convex if and only if $\operatorname{conv} g = g$. -/
theorem convexFn_iff_convHullFn_eq : ConvexFn g ↔ convHullFn g = g :=
  ⟨convHullFn_eq_self, fun h => h ▸ convexFn_convHullFn g⟩

/-- The convex hull is idempotent: $\operatorname{conv}(\operatorname{conv} g) = \operatorname{conv}
g$. -/
theorem convHullFn_idem (g : E → EReal) : convHullFn (convHullFn g) = convHullFn g :=
  convHullFn_eq_self (convexFn_convHullFn g)

end Single

/-! ### The coreflection onto the convex functions -/

section Coreflection

/-- **$\operatorname{conv}$ is right adjoint to the inclusion of the convex functions.** For convex
$h$ and any $g : E \to [-\infty, +\infty]$, $h \le g$ if and only if
$h \le \operatorname{conv} g$.

The adjunction is a `GaloisConnection` between the subtype of convex functions and
$E \to [-\infty, +\infty]$. -/
theorem gc_val_convHullFn :
    GaloisConnection (Subtype.val : {g : E → EReal // ConvexFn g} → (E → EReal))
      (fun g : E → EReal => (⟨convHullFn g, convexFn_convHullFn g⟩ :
        {g : E → EReal // ConvexFn g})) :=
  fun h g => ⟨fun hle => le_convHullFn h.2 hle,
    fun hle => (show (h : E → EReal) ≤ convHullFn g from hle).trans (convHullFn_le g)⟩

/-- The adjunction `ConvexAnalysis.gc_val_convHullFn` as a **Galois coinsertion**, which holds
because $\operatorname{conv}$ fixes the convex functions.

The convex functions therefore inherit a complete lattice structure, in which the infimum is
`ConvexAnalysis.convFn`: see `ConvexAnalysis.ConvexFns.instCompleteLattice`. -/
noncomputable def gci_val_convHullFn :
    GaloisCoinsertion (Subtype.val : {g : E → EReal // ConvexFn g} → (E → EReal))
      (fun g : E → EReal => (⟨convHullFn g, convexFn_convHullFn g⟩ :
        {g : E → EReal // ConvexFn g})) :=
  gc_val_convHullFn.toGaloisCoinsertion fun h => convHullFn_le (h : E → EReal)

end Coreflection

/-! ### The two hulls determine each other -/

section Compare

variable {ι : Sort*} {f : ι → E → EReal}

/-- The convex hull of a family is the convex hull of its pointwise infimum:
$$\operatorname{conv}\{f_i\} = \operatorname{conv}\Big(x \mapsto \inf_i f_i(x)\Big).$$

[rockafellar1970convex] states that the convex hull of a collection "is the convex hull of the
pointwise infimum of the collection". Both sides are the greatest convex function below every
$f_i$. -/
theorem convFn_eq_convHullFn_iInf (f : ι → E → EReal) :
    convFn f = convHullFn fun x => ⨅ i, f i x :=
  le_antisymm (le_convHullFn (convexFn_convFn f) fun x => convFn_le_iInf f x)
    (le_convFn (convexFn_convHullFn _) fun i =>
      (convHullFn_le _).trans fun x => iInf_le (fun j => f j x) i)

/-- For a nonempty index type, the convex hull of a constant family $f_i = g$ is
$\operatorname{conv} g$. -/
theorem convFn_const [Nonempty ι] (g : E → EReal) : convFn (fun _ : ι => g) = convHullFn g := by
  rw [convFn_eq_convHullFn_iInf]
  simp

/-- The convex hull of the one-element family $\{g\}$ is the convex hull $\operatorname{conv} g$ of
the single function $g$. -/
theorem convFn_unit (g : E → EReal) : convFn (fun _ : Unit => g) = convHullFn g := by
  rw [convFn_eq_convHullFn_iInf]
  simp

end Compare

/-! ### The binary case -/

section Binary

variable {f g h : E → EReal}

/-- The **convex hull of two functions** $f, g : E \to [-\infty, +\infty]$:
$$\operatorname{conv}\{f, g\} = \operatorname{ofEpi}(\operatorname{conv}(\operatorname{epi} f
  \cup \operatorname{epi} g)).$$

It is the greatest convex function below both $f$ and $g$, that is, the meet in the lattice of
convex functions. -/
noncomputable def convFn₂ (f g : E → EReal) : E → EReal := ofEpi (convexHull ℝ (epi f ∪ epi g))

/-- The convex hull $\operatorname{conv}\{f, g\}$ of two functions is convex. -/
theorem convexFn_convFn₂ (f g : E → EReal) : ConvexFn (convFn₂ f g) :=
  convexFn_ofEpi (convex_convexHull ℝ _)

/-- The convex hull of two functions lies below the first: $\operatorname{conv}\{f, g\} \le f$. -/
theorem convFn₂_le_left (f g : E → EReal) : convFn₂ f g ≤ f := by
  have h' := ofEpi_mono (subset_union_left.trans (subset_convexHull ℝ (epi f ∪ epi g)))
  rwa [ofEpi_epi] at h'

/-- The convex hull of two functions lies below the second: $\operatorname{conv}\{f, g\} \le g$. -/
theorem convFn₂_le_right (f g : E → EReal) : convFn₂ f g ≤ g := by
  have h' := ofEpi_mono (subset_union_right.trans (subset_convexHull ℝ (epi f ∪ epi g)))
  rwa [ofEpi_epi] at h'

/-- **The universal property, binary case.** If $h$ is convex, $h \le f$ and $h \le g$, then
$h \le \operatorname{conv}\{f, g\}$. -/
theorem le_convFn₂ (hh : ConvexFn h) (h₁ : h ≤ f) (h₂ : h ≤ g) : h ≤ convFn₂ f g :=
  subset_epi_iff_le_ofEpi.1
    (convexHull_min (union_subset (epi_anti h₁) (epi_anti h₂)) hh.convex_epi)

/-- The convex hull $\operatorname{conv}\{f, g\}$ is the greatest element of the set of convex
functions $h$ with $h \le f$ and $h \le g$. -/
theorem isGreatest_convFn₂ (f g : E → EReal) :
    IsGreatest {h : E → EReal | ConvexFn h ∧ h ≤ f ∧ h ≤ g} (convFn₂ f g) :=
  ⟨⟨convexFn_convFn₂ f g, convFn₂_le_left f g, convFn₂_le_right f g⟩,
    fun _ hh => le_convFn₂ hh.1 hh.2.1 hh.2.2⟩

/-- The convex hull of two functions lies below their pointwise minimum:
$\operatorname{conv}\{f, g\} \le \min\{f, g\}$. In general the inequality is strict. -/
theorem convFn₂_le_inf (f g : E → EReal) : convFn₂ f g ≤ f ⊓ g :=
  le_inf (convFn₂_le_left f g) (convFn₂_le_right f g)

/-- The convex hull of two functions is the convex hull of the family indexed by
$\{\mathrm{true}, \mathrm{false}\}$ whose members are $f$ and $g$. -/
theorem convFn₂_eq_convFn (f g : E → EReal) :
    convFn₂ f g = convFn (fun b : Bool => cond b f g) := by
  refine le_antisymm (le_convFn (convexFn_convFn₂ f g) fun b => ?_)
    (le_convFn₂ (convexFn_convFn _) (convFn_le _ true) (convFn_le _ false))
  cases b
  · exact convFn₂_le_right f g
  · exact convFn₂_le_left f g

/-- **The inequality `ConvexAnalysis.convFn₂_le_inf` is strict in general.** Let
$f = \delta(\cdot \mid \{0\})$ and $g = \delta(\cdot \mid \{1\})$ on $\mathbb{R}$. Then
$$(\operatorname{conv}\{f, g\})(1/2) < \min\{f(1/2), g(1/2)\}.$$

Both functions are convex. Their pointwise minimum is $+\infty$ at $1/2$, while their convex
hull, the indicator function of the segment $[0, 1]$, is $0$ there. -/
theorem convFn₂_indicatorFn_lt_inf :
    convFn₂ (indicatorFn ({0} : Set ℝ)) (indicatorFn ({1} : Set ℝ)) (1 / 2) <
      indicatorFn ({0} : Set ℝ) (1 / 2) ⊓ indicatorFn ({1} : Set ℝ) (1 / 2) := by
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ epi (indicatorFn ({0} : Set ℝ)) := by
    refine mk_mem_epi.2 (le_of_eq ?_)
    simp
  have h1 : ((1 : ℝ), (0 : ℝ)) ∈ epi (indicatorFn ({1} : Set ℝ)) := by
    refine mk_mem_epi.2 (le_of_eq ?_)
    simp
  have hconv := convex_convexHull ℝ
    (epi (indicatorFn ({0} : Set ℝ)) ∪ epi (indicatorFn ({1} : Set ℝ)))
  have hmid := hconv (subset_convexHull ℝ _ (Or.inl h0)) (subset_convexHull ℝ _ (Or.inr h1))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hpt : ((1 / 2 : ℝ), (0 : ℝ)) ∈
      convexHull ℝ (epi (indicatorFn ({0} : Set ℝ)) ∪ epi (indicatorFn ({1} : Set ℝ))) := by
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hmid
  refine lt_of_le_of_lt (ofEpi_apply_le hpt) ?_
  rw [indicatorFn_of_notMem (by norm_num : (1 / 2 : ℝ) ∉ ({0} : Set ℝ)),
    indicatorFn_of_notMem (by norm_num : (1 / 2 : ℝ) ∉ ({1} : Set ℝ))]
  simp

/-! #### The explicit formula for two functions -/

/-- Let $f, g : E \to [-\infty, +\infty]$ never take the value $-\infty$. Let $a, b \ge 0$ with
$a + b = 1$, and let $u, v \in E$ with $a u + b v = x$. Then
$$(\operatorname{conv}\{f, g\})(x) \le a f(u) + b g(v).$$

This is the easy half of `ConvexAnalysis.convFn₂_apply`. Only the hypothesis $f, g \neq -\infty$
is needed, not full properness. If $-\infty$ were allowed, the right-hand side could be
$-\infty$ (since $-\infty + \infty = -\infty$ in `EReal`) while the left-hand side is $+\infty$. -/
theorem convFn₂_le_combo (hf : ∀ x, f x ≠ ⊥) (hg : ∀ x, g x ≠ ⊥) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) {u v x : E} (hx : a • u + b • v = x) :
    convFn₂ f g x ≤ (a : EReal) * f u + (b : EReal) * g v := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    have hxv : v = x := by rw [← hx, hb1]; simp
    subst hb1
    subst hxv
    simp only [EReal.coe_zero, EReal.coe_one, zero_mul, one_mul, zero_add]
    exact convFn₂_le_right f g v
  rcases eq_or_lt_of_le hb with rfl | hb'
  · have ha1 : a = 1 := by linarith
    have hxu : u = x := by rw [← hx, ha1]; simp
    subst ha1
    subst hxu
    simp only [EReal.coe_zero, EReal.coe_one, zero_mul, one_mul, add_zero]
    exact convFn₂_le_left f g u
  by_cases hS : (a : EReal) * f u + (b : EReal) * g v = ⊤
  · rw [hS]; exact le_top
  have hfu : f u ≠ ⊤ := by
    intro hfu
    exact hS (by rw [hfu, EReal.coe_mul_top_of_pos ha',
      EReal.top_add_of_ne_bot (EReal.coe_mul_ne_bot hb'.le (hg v))])
  have hgv : g v ≠ ⊤ := by
    intro hgv
    exact hS (by rw [hgv, EReal.coe_mul_top_of_pos hb',
      EReal.add_top_of_ne_bot (EReal.coe_mul_ne_bot ha'.le (hf u))])
  obtain ⟨μ, hμ⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (hf u) (lt_top_iff_ne_top.2 hfu)
  obtain ⟨ν, hν⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (hg v) (lt_top_iff_ne_top.2 hgv)
  have hpt : (x, a * μ + b * ν) ∈ convexHull ℝ (epi f ∪ epi g) := by
    have hmem := convex_convexHull ℝ (epi f ∪ epi g)
      (subset_convexHull ℝ _ (Or.inl (mk_mem_epi.2 hμ.le)))
      (subset_convexHull ℝ _ (Or.inr (mk_mem_epi.2 hν.le))) ha hb hab
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hx] using hmem
  refine (ofEpi_apply_le hpt).trans (le_of_eq ?_)
  rw [hμ, hν, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]

/-- Let $f, g : E \to [-\infty, +\infty]$ be proper convex functions. Then for every $x \in E$,
$$(\operatorname{conv}\{f, g\})(x) = \inf\{a f(u) + b g(v) \mid a, b \ge 0,\ a + b = 1,\ a u + b
  v = x\}.$$

The infimum is over all such representations of $x$, and it need not be attained.
`ConvexAnalysis.convFn_apply` proves the same formula for an arbitrary family and needs only the
half of properness that excludes $-\infty$. Here the nonemptiness of $\operatorname{dom} f$ and
$\operatorname{dom} g$ is used as well: it makes the epigraphs nonempty, so that the convex hull
of their union is a convex join. -/
theorem convFn₂_apply (hf : ConvexFn f) (hg : ConvexFn g) (hf' : ProperConvex f)
    (hg' : ProperConvex g)
    (x : E) :
    convFn₂ f g x = sInf {z : EReal | ∃ (a b : ℝ) (u v : E), 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
      a • u + b • v = x ∧ z = (a : EReal) * f u + (b : EReal) * g v} := by
  have hfe : (epi f).Nonempty := ((convexDom_eq_fst_image_epi f) ▸ hf'.convexDom_nonempty).of_image
  have hge : (epi g).Nonempty := ((convexDom_eq_fst_image_epi g) ▸ hg'.convexDom_nonempty).of_image
  refine le_antisymm (le_sInf ?_) ?_
  · rintro z ⟨a, b, u, v, ha, hb, hab, hx, rfl⟩
    exact convFn₂_le_combo hf'.ne_bot hg'.ne_bot ha hb hab hx
  · refine le_ofEpi fun μ hμ => ?_
    rw [hf.convex_epi.convexHull_union hg.convex_epi hfe hge] at hμ
    obtain ⟨p, hp, q, hq, a, b, ha, hb, hab, hcombo⟩ := mem_convexJoin.1 hμ
    have hx : a • p.1 + b • q.1 = x := congrArg Prod.fst hcombo
    have hμ2 : a * p.2 + b * q.2 = μ := congrArg Prod.snd hcombo
    have h₁ : (a : EReal) * f p.1 ≤ (a : EReal) * (p.2 : EReal) :=
      mul_le_mul_of_nonneg_left (mem_epi.1 hp) (by exact_mod_cast ha)
    have h₂ : (b : EReal) * g q.1 ≤ (b : EReal) * (q.2 : EReal) :=
      mul_le_mul_of_nonneg_left (mem_epi.1 hq) (by exact_mod_cast hb)
    have hmem : (a : EReal) * f p.1 + (b : EReal) * g q.1 ∈
        {z : EReal | ∃ (a b : ℝ) (u v : E), 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
          a • u + b • v = x ∧ z = (a : EReal) * f u + (b : EReal) * g v} :=
      ⟨a, b, p.1, q.1, ha, hb, hab, hx, rfl⟩
    refine (sInf_le hmem).trans ?_
    refine (add_le_add h₁ h₂).trans (le_of_eq ?_)
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, hμ2]

/-- The convex hull of the pointwise minimum is the convex hull of the pair:
$\operatorname{conv}(\min\{f, g\}) = \operatorname{conv}\{f, g\}$.

Both sides are the greatest convex function below $f$ and $g$. -/
theorem convHullFn_inf (f g : E → EReal) : convHullFn (f ⊓ g) = convFn₂ f g :=
  le_antisymm
    (le_convFn₂ (convexFn_convHullFn _) ((convHullFn_le _).trans inf_le_left)
      ((convHullFn_le _).trans inf_le_right))
    (le_convHullFn (convexFn_convFn₂ f g) (convFn₂_le_inf f g))

/-!
#### When a convex hull of epigraphs is again an epigraph

$\operatorname{epi}(\operatorname{conv}\{f, g\})$ equals $\operatorname{conv}(\operatorname{epi} f
\cup \operatorname{epi} g)$ only when this hull is epi-like, that is, exactly when the infimum in
the formula is attained. Of the two conditions of `ConvexAnalysis.isEpiLike_iff_forall`, upward
closedness holds without hypotheses, and only attainment is in question.
-/

/-- Let $F \subseteq E \times \mathbb{R}$ be epi-like. Then $\operatorname{conv} F$ is upward closed
in the vertical direction: if $(x, \mu) \in \operatorname{conv} F$ and $\mu \le \nu$, then
$(x, \nu) \in \operatorname{conv} F$.

In other words, $\operatorname{conv} F$ inherits every translation $p \mapsto p + (0, t)$ with
$t \ge 0$ that $F$ admits. -/
theorem IsEpiLike.mem_convexHull_of_le {F : Set (E × ℝ)} (hF : IsEpiLike F) {x : E} {μ ν : ℝ}
    (hmem : (x, μ) ∈ convexHull ℝ F) (hμν : μ ≤ ν) : (x, ν) ∈ convexHull ℝ F := by
  have hconv : Convex ℝ ((fun p : E × ℝ => p + ((0 : E), ν - μ)) ⁻¹' convexHull ℝ F) := by
    intro u hu v hv a b ha hb hab
    have hsplit : a • ((0 : E), ν - μ) + b • ((0 : E), ν - μ) = ((0 : E), ν - μ) := by
      rw [← add_smul, hab, one_smul]
    have heq : a • (u + ((0 : E), ν - μ)) + b • (v + ((0 : E), ν - μ))
        = a • u + b • v + ((0 : E), ν - μ) := by
      rw [smul_add, smul_add, add_add_add_comm, hsplit]
    change a • u + b • v + ((0 : E), ν - μ) ∈ convexHull ℝ F
    rw [← heq]
    exact convex_convexHull ℝ F hu hv ha hb hab
  have hsub : convexHull ℝ F ⊆ (fun p : E × ℝ => p + ((0 : E), ν - μ)) ⁻¹' convexHull ℝ F := by
    refine convexHull_min (fun p hp => ?_) hconv
    change p + ((0 : E), ν - μ) ∈ convexHull ℝ F
    refine subset_convexHull ℝ F ?_
    have hpair : p + ((0 : E), ν - μ) = (p.1, p.2 + (ν - μ)) := Prod.ext (by simp) (by simp)
    rw [hpair]
    exact hF.mem_of_le (x := p.1) (μ := p.2) hp (by linarith)
  have hres := hsub hmem
  change ((x, μ) : E × ℝ) + ((0 : E), ν - μ) ∈ convexHull ℝ F at hres
  have hval : μ + (ν - μ) = ν := by ring
  have hxy : ((x, μ) : E × ℝ) + ((0 : E), ν - μ) = (x, ν) := by
    rw [Prod.mk_add_mk, add_zero, hval]
  rwa [hxy] at hres

/-- If $\operatorname{conv}(\operatorname{epi} f \cup \operatorname{epi} g)$ is epi-like, then it is
the epigraph of $\operatorname{conv}\{f, g\}$.

This is the binary case of `ConvexAnalysis.epi_convFn`. -/
theorem epi_convFn₂ (hF : IsEpiLike (convexHull ℝ (epi f ∪ epi g))) :
    epi (convFn₂ f g) = convexHull ℝ (epi f ∪ epi g) :=
  epi_ofEpi hF

end Binary

end Module

/-! ### The explicit formula in general -/

section Formula

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}

/-- **The easy half of `ConvexAnalysis.convFn_apply`.** Let $f_i : E \to [-\infty, +\infty]$, let
$t$ be a finite index set, and let $w_i \ge 0$ and $p_i \in E$ for $i \in t$, with
$\sum_{i \in t} w_i = 1$ and $\sum_{i \in t} w_i p_i = x$. If $f_i(p_i) \neq -\infty$ for every
$i \in t$, then
$$(\operatorname{conv}\{f_i\})(x) \le \sum_{i \in t} w_i f_i(p_i).$$

No convexity is needed. -/
theorem convFn_le_sum {f : ι → E → EReal} {t : Finset ι} {w : ι → ℝ} {p : ι → E} {x : E}
    (hf' : ∀ i ∈ t, f i (p i) ≠ ⊥) (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i ∈ t, w i = 1)
    (hwx : ∑ i ∈ t, w i • p i = x) : convFn f x ≤ ∑ i ∈ t, (w i : EReal) * f i (p i) := by
  classical
  by_cases htop : ∑ i ∈ t, (w i : EReal) * f i (p i) = ⊤
  · rw [htop]; exact le_top
  have hbot : ∀ i ∈ t, (w i : EReal) * f i (p i) ≠ ⊥ := fun i hi =>
    EReal.coe_mul_ne_bot (hw₀ i hi) (hf' i hi)
  have hnetop := EReal.forall_ne_top_of_sum_ne_top t _ hbot htop
  -- discard the indices carrying zero weight, whose points need not lie in `dom (f i)`
  set t' : Finset ι := t.filter (fun i => 0 < w i) with ht'def
  have hsub : t' ⊆ t := Finset.filter_subset _ _
  have hzero : ∀ i ∈ t, i ∉ t' → w i = 0 := by
    intro i hi hi'
    rcases eq_or_lt_of_le (hw₀ i hi) with h | h
    · exact h.symm
    · exact absurd (Finset.mem_filter.2 ⟨hi, h⟩) hi'
  have hw₁' : ∑ i ∈ t', w i = 1 := by rw [Finset.sum_subset hsub hzero]; exact hw₁
  have hwx' : ∑ i ∈ t', w i • p i = x := by
    rw [Finset.sum_subset hsub fun i hi hi' => by rw [hzero i hi hi', zero_smul]]; exact hwx
  obtain ⟨μ, hμ⟩ : ∃ μ : ι → ℝ, ∀ i ∈ t', f i (p i) = (μ i : EReal) := by
    refine ⟨fun i => (f i (p i)).toReal, fun i hi => ?_⟩
    have hpos : 0 < w i := (Finset.mem_filter.1 hi).2
    have hne : f i (p i) ≠ ⊤ := fun hcon =>
      hnetop i (hsub hi) (by rw [hcon, EReal.coe_mul_top_of_pos hpos])
    exact (EReal.coe_toReal hne (hf' i (hsub hi))).symm
  have hcm := Finset.centerMass_mem_convexHull t'
    (fun i hi => ((Finset.mem_filter.1 hi).2).le) (by rw [hw₁']; exact zero_lt_one)
    (z := fun i => ((p i, μ i) : E × ℝ))
    (fun i hi => mem_iUnion.2 ⟨i, mk_mem_epi.2 (le_of_eq (hμ i hi))⟩)
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw₁'] at hcm
  have hsplit : ∑ i ∈ t', w i • ((p i, μ i) : E × ℝ) = (x, ∑ i ∈ t', w i * μ i) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]; simpa using hwx'
    · rw [Prod.snd_sum]; simp [smul_eq_mul]
  rw [hsplit] at hcm
  refine (ofEpi_apply_le hcm).trans (le_of_eq ?_)
  rw [EReal.coe_sum,
    ← Finset.sum_subset hsub (fun i hi hi' => by rw [hzero i hi hi']; simp)]
  exact Finset.sum_congr rfl fun i hi => by rw [hμ i hi, ← EReal.coe_mul]

/-- Let $f_i : E \to [-\infty, +\infty]$ be convex functions that never take the value $-\infty$.
Then for every $x \in E$,
$$(\operatorname{conv}\{f_i\})(x) = \inf\Big\{\sum_{i \in t} w_i f_i(p_i) \Bigm|
  t \text{ finite},\ w_i \ge 0,\ \sum_{i \in t} w_i = 1,\ \sum_{i \in t} w_i p_i = x\Big\}.$$
This is Theorem 5.6 of [rockafellar1970convex].

[rockafellar1970convex] assumes the $f_i$ proper. Only the half of properness that excludes
$-\infty$ is used, in two places: it keeps $w_i f_i(p_i)$ from being $-\infty$ where $w_i = 0$,
and it turns a finite bound on the sum into a finite bound on each term. As for sums, the
nonemptiness of $\operatorname{dom} f_i$ is not needed.

The description of a convex hull by convex combinations takes the points of the hull from the
sets $\operatorname{epi} f_i$ with repetitions, but the infimum here takes one point per index.
The proof of $\ge$ merges the points taken from one $\operatorname{epi} f_i$ into their center
of mass. This is the only use of the convexity of the $f_i$. -/
theorem convFn_apply {f : ι → E → EReal} (hf : ∀ i, ConvexFn (f i)) (hf' : ∀ i x, f i x ≠ ⊥)
    (x : E) :
    convFn f x = sInf {z : EReal | ∃ (t : Finset ι) (w : ι → ℝ) (p : ι → E),
      (∀ i ∈ t, 0 ≤ w i) ∧ ∑ i ∈ t, w i = 1 ∧ ∑ i ∈ t, w i • p i = x ∧
        z = ∑ i ∈ t, (w i : EReal) * f i (p i)} := by
  classical
  refine le_antisymm (le_sInf ?_) ?_
  -- **`≤`**: the convex hull is below the value of every representation of `x`.
  · rintro z ⟨t, w, p, hw₀, hw₁, hwx, rfl⟩
    exact convFn_le_sum (fun i _ => hf' i (p i)) hw₀ hw₁ hwx
  -- **`≥`**: every point of the convex hull of the union comes from a representation.
  · refine le_ofEpi fun ν hν => ?_
    rw [convexHull_eq] at hν
    obtain ⟨κ, s, w, z, hw₀, hw₁, hz, hcm⟩ := hν
    set s' : Finset κ := s.filter (fun j => 0 < w j) with hs'def
    have hsub : s' ⊆ s := Finset.filter_subset _ _
    have hwpos : ∀ j ∈ s', 0 < w j := fun j hj => (Finset.mem_filter.1 hj).2
    have hzero : ∀ j ∈ s, j ∉ s' → w j = 0 := by
      intro j hj hj'
      rcases eq_or_lt_of_le (hw₀ j hj) with h | h
      · exact h.symm
      · exact absurd (Finset.mem_filter.2 ⟨hj, h⟩) hj'
    have hw₁' : ∑ j ∈ s', w j = 1 := by rw [Finset.sum_subset hsub hzero]; exact hw₁
    have hcm' : ∑ j ∈ s', w j • z j = (x, ν) := by
      rw [Finset.sum_subset hsub fun j hj hj' => by rw [hzero j hj hj', zero_smul],
        ← Finset.centerMass_eq_of_sum_1 _ _ hw₁]
      exact hcm
    -- choose, for each point of the combination, an index whose epigraph it belongs to
    obtain ⟨j₀, hj₀⟩ : s'.Nonempty :=
      Finset.nonempty_of_sum_ne_zero (by rw [hw₁']; exact one_ne_zero)
    obtain ⟨i₀, -⟩ := mem_iUnion.1 (hz j₀ (hsub hj₀))
    have hchoice : ∀ j : κ, ∃ i : ι, j ∈ s' → z j ∈ epi (f i) := by
      intro j
      by_cases hj : j ∈ s'
      · obtain ⟨i, hi⟩ := mem_iUnion.1 (hz j (hsub hj))
        exact ⟨i, fun _ => hi⟩
      · exact ⟨i₀, fun hcon => absurd hcon hj⟩
    choose σ hσ using hchoice
    -- merge the points drawn from one and the same epigraph into their center of mass
    obtain ⟨W, hW⟩ : ∃ W : ι → ℝ, ∀ i, W i = ∑ j ∈ s' with σ j = i, w j := ⟨_, fun _ => rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : ι → E × ℝ,
        ∀ i, Q i = (s'.filter fun j => σ j = i).centerMass w z := ⟨_, fun _ => rfl⟩
    have hmaps : ∀ j ∈ s', σ j ∈ s'.image σ := fun j hj => Finset.mem_image_of_mem σ hj
    have hWpos : ∀ i ∈ s'.image σ, 0 < W i := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
      rw [hW]
      exact Finset.sum_pos (fun k hk => hwpos k (Finset.mem_filter.1 hk).1)
        ⟨j, Finset.mem_filter.2 ⟨hj, rfl⟩⟩
    have hQmem : ∀ i ∈ s'.image σ, Q i ∈ epi (f i) := by
      intro i hi
      rw [hQ]
      refine (hf i).convex_epi.centerMass_mem
        (fun j hj => (hwpos j (Finset.mem_filter.1 hj).1).le) ?_ (fun j hj => ?_)
      · have := hWpos i hi; rwa [hW] at this
      · obtain ⟨hj₁, hj₂⟩ := Finset.mem_filter.1 hj
        exact hj₂ ▸ hσ j hj₁
    have hWsum : ∑ i ∈ s'.image σ, W i = 1 := by
      simp only [hW]
      rw [Finset.sum_fiberwise_of_maps_to hmaps w]
      exact hw₁'
    have hQsum : ∑ i ∈ s'.image σ, W i • Q i = (x, ν) := by
      have hstep : ∀ i ∈ s'.image σ, W i • Q i = ∑ j ∈ s' with σ j = i, w j • z j := by
        intro i hi
        have hWi : (∑ j ∈ s' with σ j = i, w j) ≠ 0 := by
          have hpos := hWpos i hi
          rw [hW] at hpos
          exact hpos.ne'
        rw [hQ, Finset.centerMass, hW, smul_inv_smul₀ hWi]
      rw [Finset.sum_congr rfl hstep,
        Finset.sum_fiberwise_of_maps_to hmaps (fun j => w j • z j)]
      exact hcm'
    have hx' : ∑ i ∈ s'.image σ, W i • (Q i).1 = x := by
      have hfst := congrArg Prod.fst hQsum
      rw [Prod.fst_sum] at hfst
      simpa using hfst
    have hν' : ∑ i ∈ s'.image σ, W i * (Q i).2 = ν := by
      have hsnd := congrArg Prod.snd hQsum
      rw [Prod.snd_sum] at hsnd
      simpa [smul_eq_mul] using hsnd
    have hval : ∑ i ∈ s'.image σ, (W i : EReal) * f i ((Q i).1) ≤ (ν : EReal) := by
      calc ∑ i ∈ s'.image σ, (W i : EReal) * f i ((Q i).1)
          ≤ ∑ i ∈ s'.image σ, (W i : EReal) * (((Q i).2 : ℝ) : EReal) :=
            Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (mem_epi.1 (hQmem i hi))
              (by exact_mod_cast (hWpos i hi).le)
        _ = ((∑ i ∈ s'.image σ, W i * (Q i).2 : ℝ) : EReal) := by
            rw [EReal.coe_sum]
            exact Finset.sum_congr rfl fun i _ => EReal.coe_mul _ _
        _ = (ν : EReal) := by rw [hν']
    have hmemS : (∑ i ∈ s'.image σ, (W i : EReal) * f i ((Q i).1)) ∈
        {z : EReal | ∃ (t : Finset ι) (w : ι → ℝ) (p : ι → E),
          (∀ i ∈ t, 0 ≤ w i) ∧ ∑ i ∈ t, w i = 1 ∧ ∑ i ∈ t, w i • p i = x ∧
            z = ∑ i ∈ t, (w i : EReal) * f i (p i)} :=
      ⟨s'.image σ, W, fun i => (Q i).1, fun i hi => (hWpos i hi).le, hWsum, hx', rfl⟩
    exact (sInf_le hmemS).trans hval

end Formula

/-! ### Closedness supplies the missing half -/

section Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {f g : E → EReal}

/-- Let $E$ be a real vector space with a topology. If $\operatorname{conv}(\operatorname{epi} f
\cup \operatorname{epi} g)$ is closed, then it is epi-like.

Upward closedness holds without hypotheses (`ConvexAnalysis.IsEpiLike.mem_convexHull_of_le`),
and closedness gives the attainment of the vertical infima. So
$\operatorname{conv}(\operatorname{epi} f \cup \operatorname{epi} g)$ can fail to be an epigraph
only by failing to be closed. This turns the closedness criteria for convex hulls into
statements that the infimum in the formula is attained. -/
theorem isEpiLike_convexHull_epi_union (hc : IsClosed (convexHull ℝ (epi f ∪ epi g))) :
    IsEpiLike (convexHull ℝ (epi f ∪ epi g)) :=
  IsEpiLike.of_isClosed (fun _ _ _ hmem hle =>
    ((isEpiLike_epi f).union (isEpiLike_epi g)).mem_convexHull_of_le hmem hle) hc

end Topology

end ConvexAnalysis
