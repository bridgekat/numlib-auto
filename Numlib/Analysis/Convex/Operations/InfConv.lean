/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Indicator
import Numlib.Analysis.Convex.Operations.Epi

/-!
# Infimal convolution

Let $E$ be an additive group and let $f, g \colon E \to [-\infty, +\infty]$. The **infimal
convolute** $f \mathbin{\square} g$ is the operation on functions that corresponds to the addition
of epigraphs: it is the function determined by $\operatorname{epi} f + \operatorname{epi} g$. When
neither function takes the value $-\infty$, it is given by the classical formula $$(f
\mathbin{\square} g)(x) = \inf_{y \in E} \big( f(x - y) + g(y) \big),$$ which is analogous to the
formula for integral convolution ([rockafellar1970convex], §5). The infimal convolute of two convex
functions is convex, and infimal convolution is dual to pointwise addition under conjugacy. Infimal
convolution is commutative and associative, and the indicator function $\delta(\cdot \mid 0)$ of the
origin is its identity element.

The **supremal convolute** of two concave functions $g$ and $h$ is $-((-g) \mathbin{\square} (-h))$.
When neither function takes the value $+\infty$, its value at $x$ is
$\sup \{ g(x_1) + h(x_2) \mid x_1 + x_2 = x \}$. Each property of infimal convolution gives a
property of supremal convolution by one negation.

## Main definitions

* `ConvexAnalysis.infConv`: the infimal convolute $f \mathbin{\square} g$.
* `ConvexAnalysis.supConv`: the supremal convolute $-((-g) \mathbin{\square} (-h))$ of $g$ and $h$.
* `ConvexAnalysis.InfConvFn`: a copy of the type of functions $E \to [-\infty, +\infty]$ whose
  addition is infimal convolution, so that $f_1 \mathbin{\square} \cdots \mathbin{\square} f_m$ is a
  finite sum.

## Main results

* `ConvexAnalysis.convexFn_infConv`: the infimal convolute of two convex functions is convex.
  `ConvexAnalysis.convexFn_sum_toInfConvFn` is the form with $m$ functions.
* `ConvexAnalysis.infConv_apply`: if $f$ and $g$ never take the value $-\infty$, then $(f
  \mathbin{\square} g)(x) = \inf_y ( f(x - y) + g(y) )$.
* `ConvexAnalysis.infConv_le_add`: under the same hypotheses,
  $(f \mathbin{\square} g)(x) \le f(x - y) + g(y)$. `ConvexAnalysis.sum_toInfConvFn_apply_le` and
  `ConvexAnalysis.sum_toInfConvFn_le_sum` are the forms with $m$ functions.
* `ConvexAnalysis.convexDom_infConv`: $\operatorname{dom}(f \mathbin{\square} g) =
  \operatorname{dom} f + \operatorname{dom} g$, with no hypothesis.
* `ConvexAnalysis.supConv_apply`, `ConvexAnalysis.concaveDom_supConv`,
  `ConvexAnalysis.concaveFn_supConv`: the formula, the effective domain and the concavity of the
  supremal convolute.
* `ConvexAnalysis.infConv_comp_neg`: infimal convolution commutes with the reflection $x \mapsto -x$
  of the argument.
* `ConvexAnalysis.InfConvFn.instAddCommMonoid`: infimal convolution is commutative and associative,
  with identity element $\delta(\cdot \mid 0)$.
* `ConvexAnalysis.infConv_indicatorFn_singleton`: $f \mathbin{\square} \delta(\cdot \mid a)$ is the
  translate $x \mapsto f(x - a)$.
* `ConvexAnalysis.subset_epi_infConv`, `ConvexAnalysis.epi_infConv`: $\operatorname{epi} f +
  \operatorname{epi} g \subseteq \operatorname{epi}(f \mathbin{\square} g)$, with equality when
  $\operatorname{epi} f + \operatorname{epi} g$ is an epigraph.

## Implementation notes

* `ConvexAnalysis.infConv f g` is defined as `ConvexAnalysis.ofEpi (epi f + epi g)`, not by the
  classical formula. The formula is wrong when one function takes the value $+\infty$ where the
  other takes $-\infty$. For example, if $f \equiv +\infty$ and $g(0) = -\infty$, then
  $\operatorname{epi} f + \operatorname{epi} g = \emptyset$, so
  $(f \mathbin{\square} g)(0) = +\infty$, but the formula gives $+\infty + (-\infty) = -\infty$ in
  `EReal`. `ConvexAnalysis.infConv_apply` recovers the formula when $f \ne -\infty$ and
  $g \ne -\infty$ everywhere. This example uses only one value $+\infty$ and one value $-\infty$, so
  a hypothesis on only one of the two functions is not sufficient.
* `ConvexAnalysis.InfConvFn E` is a type synonym of `E → EReal`. A synonym is necessary because
  `E → EReal` already has the pointwise addition, to which infimal convolution is dual. Additive
  notation is natural, because infimal convolution is the addition of epigraphs.
-/

open Pointwise Set

namespace ConvexAnalysis

/-! ### The definition and its epigraph -/

section Basic

variable {E : Type*} [AddCommGroup E] {f g f₁ f₂ g₁ g₂ : E → EReal} {y z : E} {ν ρ : ℝ}

/-- The **infimal convolute** $f \mathbin{\square} g$ of $f, g \colon E \to [-\infty, +\infty]$ is
the function determined by the sum of the epigraphs: $$(f \mathbin{\square} g)(x) = \inf \{ \mu
\in \mathbb{R} \mid (x, \mu) \in \operatorname{epi} f + \operatorname{epi} g \}.$$

This definition does not use the formula $(f \mathbin{\square} g)(x) = \inf_y ( f(x - y) + g(y)
)$, which is wrong when $f$ or $g$ takes the value $-\infty$. The formula is
`ConvexAnalysis.infConv_apply`. -/
noncomputable def infConv (f g : E → EReal) : E → EReal := ofEpi (epi f + epi g)

/-- The infimal convolute $f \mathbin{\square} g$ is the function determined by
$\operatorname{epi} f + \operatorname{epi} g$. -/
theorem infConv_def (f g : E → EReal) : infConv f g = ofEpi (epi f + epi g) := rfl

/-- The **supremal convolute** of $g, h \colon E \to [-\infty, +\infty]$ is the function $$x \mapsto
-\big( (-g) \mathbin{\square} (-h) \big)(x).$$ It is the concave form of $\square$ in
[rockafellar1970convex], with the value $\sup \{ g(x_1) + h(x_2) \mid x_1 + x_2 = x \}$ at $x$
under the hypotheses of `ConvexAnalysis.supConv_apply`.

With this definition, every property of `ConvexAnalysis.infConv` gives a property of the
supremal convolute by one negation. -/
noncomputable def supConv (g h : E → EReal) : E → EReal :=
  fun x => -(infConv (fun w => -(g w)) (fun w => -(h w)) x)

/-- The supremal convolute of $g$ and $h$ is $x \mapsto -((-g) \mathbin{\square} (-h))(x)$. -/
theorem supConv_def (g h : E → EReal) :
    supConv g h = fun x => -(infConv (fun w => -(g w)) (fun w => -(h w)) x) := rfl

/-- The negative of the supremal convolute of $g$ and $h$ is the infimal convolute
$(-g) \mathbin{\square} (-h)$. Both convolutions negate values, not arguments. -/
@[simp] theorem neg_supConv (g h : E → EReal) (x : E) :
    -(supConv g h x) = infConv (fun w => -(g w)) (fun w => -(h w)) x := neg_neg _

/-- The sum of the epigraphs is contained in the epigraph of the infimal convolute:
$\operatorname{epi} f + \operatorname{epi} g \subseteq \operatorname{epi}(f \mathbin{\square}
g)$. -/
theorem subset_epi_infConv (f g : E → EReal) : epi f + epi g ⊆ epi (infConv f g) :=
  subset_epi_ofEpi _

/-- If $\operatorname{epi} f + \operatorname{epi} g$ is the epigraph of some function, then it is
the epigraph of the infimal convolute: $$\operatorname{epi}(f \mathbin{\square} g) =
\operatorname{epi} f + \operatorname{epi} g.$$ [rockafellar1970convex] describes
$\operatorname{epi}(f \mathbin{\square} g)$ in this way.

The hypothesis cannot be removed, because a sum of epigraphs need not be an epigraph. On
$\mathbb{R}$, let $f(x) = 1/x$ for $x > 0$ and $f(x) = +\infty$ otherwise, and let $g \equiv 0$.
Both functions are convex. Every vertical section of
$\operatorname{epi} f + \operatorname{epi} g$ is $(0, \infty)$, so the sum is
$\mathbb{R} \times (0, \infty)$. But $f \mathbin{\square} g \equiv 0$ has the epigraph
$\mathbb{R} \times [0, \infty)$. -/
theorem epi_infConv (h : IsEpiLike (epi f + epi g)) : epi (infConv f g) = epi f + epi g :=
  epi_ofEpi h

/-- The vertical sections of a sum of epigraphs are closed upwards: if $(x, \mu) \in
\operatorname{epi} f + \operatorname{epi} g$ and $\mu \le \nu$, then $(x, \nu) \in
\operatorname{epi} f + \operatorname{epi} g$.

This is the half of `ConvexAnalysis.IsEpiLike` that always holds. The other half, attainment of
the infimum, can fail. -/
theorem mem_epi_add_epi_of_le {x : E} {μ ν : ℝ} (h : ((x, μ) : E × ℝ) ∈ epi f + epi g)
    (hμν : μ ≤ ν) : ((x, ν) : E × ℝ) ∈ epi f + epi g := by
  obtain ⟨⟨y', a⟩, h₁, ⟨z', b⟩, h₂, heq⟩ := h
  have hy : y' + z' = x := congrArg Prod.fst heq
  have hab : a + b = μ := congrArg Prod.snd heq
  refine ⟨(y', a), h₁, (z', b + (ν - μ)), mk_mem_epi.2 ?_, ?_⟩
  · exact (mk_mem_epi.1 h₂).trans (by exact_mod_cast (by linarith : b ≤ b + (ν - μ)))
  · change ((y', a) : E × ℝ) + (z', b + (ν - μ)) = (x, ν)
    rw [Prod.mk_add_mk, hy, show a + (b + (ν - μ)) = ν by linarith]

/-- If $f(y) \le \nu$ and $g(z) \le \rho$ for real numbers $\nu$ and $\rho$, then
$(f \mathbin{\square} g)(y + z) \le \nu + \rho$.

The bound is stated with real upper bounds, inside the epigraphs, so that no sum
$+\infty + (-\infty)$ occurs. -/
theorem infConv_apply_le (hy : f y ≤ (ν : EReal)) (hz : g z ≤ (ρ : EReal)) :
    infConv f g (y + z) ≤ ((ν + ρ : ℝ) : EReal) := by
  refine ofEpi_apply_le ?_
  have hmem : ((y, ν) : E × ℝ) + (z, ρ) ∈ epi f + epi g :=
    Set.add_mem_add (mk_mem_epi.2 hy) (mk_mem_epi.2 hz)
  rwa [Prod.mk_add_mk] at hmem

/-! ### The effective domain -/

/-- For all $f, g \colon E \to [-\infty, +\infty]$, the effective domain of the infimal convolute is
the sum of the effective domains: $$\operatorname{dom}(f \mathbin{\square} g) =
\operatorname{dom} f + \operatorname{dom} g.$$

No hypothesis is needed, unlike for pointwise addition (`ConvexAnalysis.convexDom_add`). The
reason is that the effective domain is the projection of the epigraph on $E$, and this
projection is additive. -/
theorem convexDom_infConv
    (f g : E → EReal) : convexDom (infConv f g) = convexDom f + convexDom g := by
  rw [infConv_def, convexDom_ofEpi, convexDom_eq_fst_image_epi f, convexDom_eq_fst_image_epi g]
  exact Set.image_add (AddMonoidHom.fst E ℝ)

/-- For all $g, h \colon E \to [-\infty, +\infty]$, the effective domain (the set where the function
is greater than $-\infty$) of the supremal convolute of $g$ and $h$ is the sum of the effective
domains of $g$ and $h$. No hypothesis is needed. -/
theorem concaveDom_supConv (g h : E → EReal) :
    concaveDom (supConv g h) = concaveDom g + concaveDom h := by
  rw [concaveDom_eq_convexDom_neg, concaveDom_eq_convexDom_neg, concaveDom_eq_convexDom_neg]
  simp only [neg_supConv]
  exact convexDom_infConv _ _

/-! ### The infimum formula -/

/-- Let $f, g \colon E \to [-\infty, +\infty]$ never take the value $-\infty$. Then for all
$x, y \in E$, $$(f \mathbin{\square} g)(x) \le f(x - y) + g(y).$$

Both hypotheses are needed. Without them the right side can be $+\infty + (-\infty) = -\infty$
while the left side is $+\infty$. -/
theorem infConv_le_add (hf : ∀ x, f x ≠ ⊥) (hg : ∀ x, g x ≠ ⊥) (x y : E) :
    infConv f g x ≤ f (x - y) + g y := by
  rcases eq_top_or_lt_top (f (x - y)) with h1 | h1
  · rw [h1, EReal.top_add_of_ne_bot (hg y)]
    exact le_top
  rcases eq_top_or_lt_top (g y) with h2 | h2
  · rw [h2, EReal.add_top_of_ne_bot (hf (x - y))]
    exact le_top
  obtain ⟨p, hp⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hf (x - y)) h1
  obtain ⟨q, hq⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hg y) h2
  rw [hp, hq, ← EReal.coe_add]
  simpa using infConv_apply_le (f := f) (g := g) hp.le hq.le

/-- **The formula for the infimal convolute.** Let $f, g \colon E \to [-\infty, +\infty]$ never take
the value $-\infty$. Then for every $x \in E$, $$(f \mathbin{\square} g)(x) = \inf_{y \in E}
\big( f(x - y) + g(y) \big).$$

[rockafellar1970convex] notes that this formula is analogous to the classical formula for
integral convolution. The hypotheses make the sum on the right side meaningful. -/
theorem infConv_apply (hf : ∀ x, f x ≠ ⊥) (hg : ∀ x, g x ≠ ⊥) (x : E) :
    infConv f g x = ⨅ y, f (x - y) + g y := by
  refine le_antisymm (le_iInf fun y => infConv_le_add hf hg x y) (le_ofEpi fun μ hμ => ?_)
  obtain ⟨⟨a, ν⟩, ha, ⟨b, ρ⟩, hb, hab⟩ := Set.mem_add.1 hμ
  rw [Prod.mk_add_mk, Prod.mk.injEq] at hab
  refine le_trans (iInf_le (fun y => f (x - y) + g y) b) ?_
  rw [← hab.1, add_sub_cancel_right, ← hab.2, EReal.coe_add]
  exact add_le_add (mk_mem_epi.1 ha) (mk_mem_epi.1 hb)

/-- **The formula for the supremal convolute.** Let $g, h \colon E \to [-\infty, +\infty]$ never
take the value $+\infty$. Then for every $x \in E$, the supremal convolute of $g$ and $h$ has
the value $$\sup_{y \in E} \big( g(x - y) + h(y) \big).$$

The hypotheses mirror those of `ConvexAnalysis.infConv_apply`. Without them, a summand is
$+\infty + (-\infty)$ at a point where one function is $+\infty$ and the other is $-\infty$, and
`EReal` gives this sum the value $-\infty$, which is wrong here. -/
theorem supConv_apply {g h : E → EReal} (hg : ∀ x, g x ≠ ⊤) (hh : ∀ x, h x ≠ ⊤) (x : E) :
    supConv g h x = ⨆ y, g (x - y) + h y := by
  change -(infConv (fun w => -(g w)) (fun w => -(h w)) x) = _
  rw [infConv_apply (fun z => by simpa using hg z) (fun z => by simpa using hh z), EReal.neg_iInf]
  refine iSup_congr fun y => ?_
  rw [EReal.neg_add_of_ne_bot (by simpa using hg (x - y)) (by simpa using hh y), neg_neg, neg_neg]

/-! ### Commutativity, associativity, monotonicity -/

/-- Infimal convolution is commutative: $f \mathbin{\square} g = g \mathbin{\square} f$. -/
theorem infConv_comm (f g : E → EReal) : infConv f g = infConv g f := by
  rw [infConv_def, infConv_def, add_comm]

/-- Supremal convolution is commutative. -/
theorem supConv_comm (g h : E → EReal) : supConv g h = supConv h g :=
  funext fun x => congrArg Neg.neg (congrFun (infConv_comm _ _) x)

/-- **Infimal convolution commutes with the reflection of the argument.** For all
$f, g \colon E \to [-\infty, +\infty]$ and $x \in E$, $$\big( f(-\,\cdot) \mathbin{\square}
g(-\,\cdot) \big)(x) = (f \mathbin{\square} g)(-x).$$

The map $(x, \mu) \mapsto (-x, \mu)$ is an additive bijection of $E \times \mathbb{R}$, so it
carries the sum of the epigraphs to the sum of their images. -/
theorem infConv_comp_neg (f g : E → EReal) (x : E) :
    infConv (fun w => f (-w)) (fun w => g (-w)) x = infConv f g (-x) := by
  have key : ∀ μ : ℝ, ((x, μ) : E × ℝ) ∈ epi (fun w => f (-w)) + epi (fun w => g (-w))
      ↔ ((-x, μ) : E × ℝ) ∈ epi f + epi g := by
    intro μ
    constructor
    · rintro ⟨⟨a, α⟩, ha, ⟨b, β⟩, hb, hab⟩
      have hab' : ((a, α) : E × ℝ) + (b, β) = (x, μ) := hab
      rw [Prod.mk_add_mk, Prod.mk.injEq] at hab'
      refine ⟨(-a, α), mk_mem_epi.2 (mk_mem_epi.1 ha), (-b, β),
        mk_mem_epi.2 (mk_mem_epi.1 hb), ?_⟩
      change ((-a, α) : E × ℝ) + (-b, β) = (-x, μ)
      rw [Prod.mk_add_mk, ← neg_add, hab'.1, hab'.2]
    · rintro ⟨⟨a, α⟩, ha, ⟨b, β⟩, hb, hab⟩
      have hab' : ((a, α) : E × ℝ) + (b, β) = (-x, μ) := hab
      rw [Prod.mk_add_mk, Prod.mk.injEq] at hab'
      refine ⟨(-a, α), ?_, (-b, β), ?_, ?_⟩
      · exact mk_mem_epi.2 (by rw [neg_neg]; exact mk_mem_epi.1 ha)
      · exact mk_mem_epi.2 (by rw [neg_neg]; exact mk_mem_epi.1 hb)
      · change ((-a, α) : E × ℝ) + (-b, β) = (x, μ)
        rw [Prod.mk_add_mk, ← neg_add, hab'.1, neg_neg, hab'.2]
  exact le_antisymm (le_ofEpi fun μ hμ => ofEpi_apply_le ((key μ).2 hμ))
    (le_ofEpi fun μ hμ => ofEpi_apply_le ((key μ).1 hμ))

/-- For sets $F, G \subseteq E \times \mathbb{R}$, $$\operatorname{epi}(\operatorname{ofEpi} F) + G
\subseteq \operatorname{epi}(\operatorname{ofEpi}(F + G)),$$ where $\operatorname{ofEpi} F$ is
the function determined by $F$.

Replacing $F$ by the epigraph of the function it determines does not move the lower boundary of
the sum, because the added points are limits from above of points of $F$. This is the key step
of the associativity of $\square$. -/
theorem epi_ofEpi_add_subset (F G : Set (E × ℝ)) :
    epi (ofEpi F) + G ⊆ epi (ofEpi (F + G)) := by
  rintro p hp
  obtain ⟨⟨w, μ⟩, hwμ, ⟨u, σ⟩, huσ, rfl⟩ := Set.mem_add.1 hp
  rw [Prod.mk_add_mk]
  refine mk_mem_epi.2 (EReal.le_of_forall_lt_iff_le.1 fun q hq => le_of_lt ?_)
  replace hq := EReal.coe_lt_coe_iff.1 hq
  have hlt : ofEpi F w < ((μ + (q - (μ + σ)) : ℝ) : EReal) :=
    lt_of_le_of_lt (mk_mem_epi.1 hwμ)
      (by exact_mod_cast (by linarith : μ < μ + (q - (μ + σ))))
  obtain ⟨τ, hτF, hτ⟩ := ofEpi_lt_iff.1 hlt
  have hmem : ((w, τ) : E × ℝ) + (u, σ) ∈ F + G := Set.add_mem_add hτF huσ
  rw [Prod.mk_add_mk] at hmem
  refine lt_of_le_of_lt (ofEpi_apply_le hmem) ?_
  have hτ' : τ < μ + (q - (μ + σ)) := by exact_mod_cast hτ
  exact_mod_cast (by linarith : τ + σ < q)

/-- For a set $F \subseteq E \times \mathbb{R}$, the infimal convolute of the function determined by
$F$ with $g$ is the function determined by $F + \operatorname{epi} g$. -/
theorem infConv_ofEpi_left (F : Set (E × ℝ)) (g : E → EReal) :
    infConv (ofEpi F) g = ofEpi (F + epi g) := by
  refine le_antisymm (ofEpi_mono (Set.add_subset_add_right (subset_epi_ofEpi F))) ?_
  exact subset_epi_iff_le_ofEpi.1 (epi_ofEpi_add_subset F (epi g))

/-- For a set $G \subseteq E \times \mathbb{R}$, the infimal convolute of $f$ with the function
determined by $G$ is the function determined by $\operatorname{epi} f + G$. -/
theorem infConv_ofEpi_right (f : E → EReal) (G : Set (E × ℝ)) :
    infConv f (ofEpi G) = ofEpi (epi f + G) := by
  rw [infConv_comm, infConv_ofEpi_left, add_comm]

/-- Infimal convolution is associative: $(f \mathbin{\square} g) \mathbin{\square} h = f
\mathbin{\square} (g \mathbin{\square} h)$.

This does not follow directly from the associativity of the addition of sets, because
$\operatorname{epi}(f \mathbin{\square} g)$ is in general larger than
$\operatorname{epi} f + \operatorname{epi} g$. `ConvexAnalysis.epi_ofEpi_add_subset` closes the
gap. -/
theorem infConv_assoc (f g h : E → EReal) :
    infConv (infConv f g) h = infConv f (infConv g h) := by
  rw [infConv_def f g, infConv_def g h, infConv_ofEpi_left, infConv_ofEpi_right, add_assoc]

/-- Supremal convolution is associative. -/
theorem supConv_assoc (g h k : E → EReal) :
    supConv (supConv g h) k = supConv g (supConv h k) := by
  simp only [supConv_def, neg_neg]
  exact congrArg (fun F : E → EReal => fun x => -(F x)) (infConv_assoc _ _ _)

/-- Infimal convolution is monotone in both arguments: if $f_1 \le f_2$ and $g_1 \le g_2$, then $f_1
\mathbin{\square} g_1 \le f_2 \mathbin{\square} g_2$. -/
theorem infConv_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : infConv f₁ g₁ ≤ infConv f₂ g₂ :=
  ofEpi_mono (Set.add_subset_add (epi_anti hf) (epi_anti hg))

/-- Supremal convolution is monotone in both arguments. -/
theorem supConv_mono {h₁ h₂ : E → EReal} (hg : g₁ ≤ g₂) (hh : h₁ ≤ h₂) :
    supConv g₁ h₁ ≤ supConv g₂ h₂ := fun x =>
  EReal.neg_le_neg_iff.2 (infConv_mono (fun w => EReal.neg_le_neg_iff.2 (hg w))
    (fun w => EReal.neg_le_neg_iff.2 (hh w)) x)

/-! ### Indicator functions: the identity element and translation -/

/-- Adding the epigraph of $\delta(\cdot \mid a)$, which is the half-line
$\{a\} \times [0, \infty)$, translates an epigraph horizontally by $a$: $$\operatorname{epi} f +
\operatorname{epi} \delta(\cdot \mid a) = \operatorname{epi}\big( x \mapsto f(x - a) \big).$$
Unlike a general sum of epigraphs, this sum is an epigraph. -/
theorem epi_add_epi_indicatorFn_singleton (f : E → EReal) (a : E) :
    epi f + epi (indicatorFn ({a} : Set E)) = epi fun x => f (x - a) := by
  rw [epi_indicatorFn]
  ext p
  constructor
  · intro hp
    obtain ⟨⟨w, ν'⟩, hw, ⟨u, σ⟩, hu, rfl⟩ := Set.mem_add.1 hp
    have hu1 : u = a := hu.1
    have hu2 : (0 : ℝ) ≤ σ := hu.2
    subst hu1
    rw [Prod.mk_add_mk]
    refine mk_mem_epi.2 ?_
    rw [add_sub_cancel_right]
    exact (mk_mem_epi.1 hw).trans (by exact_mod_cast (by linarith : ν' ≤ ν' + σ))
  · intro hp
    obtain ⟨w, μ⟩ := p
    have hmem : ((w - a, μ) : E × ℝ) + (a, 0) ∈ epi f + ({a} ×ˢ Ici (0 : ℝ)) :=
      Set.add_mem_add (mk_mem_epi.2 (mk_mem_epi.1 hp)) ⟨rfl, le_refl (0 : ℝ)⟩
    simpa using hmem

/-- The infimal convolute $f \mathbin{\square} \delta(\cdot \mid a)$ is the translate
$x \mapsto f(x - a)$ of $f$. -/
theorem infConv_indicatorFn_singleton (f : E → EReal) (a : E) :
    infConv f (indicatorFn ({a} : Set E)) = fun x => f (x - a) := by
  rw [infConv_def, epi_add_epi_indicatorFn_singleton, ofEpi_epi]

/-- The indicator function $\delta(\cdot \mid 0)$ is a right identity for infimal convolution:
$f \mathbin{\square} \delta(\cdot \mid 0) = f$. -/
@[simp] theorem infConv_indicatorFn_zero (f : E → EReal) :
    infConv f (indicatorFn ({0} : Set E)) = f := by
  simpa using infConv_indicatorFn_singleton f 0

/-- The indicator function $\delta(\cdot \mid 0)$ is a left identity for infimal convolution:
$\delta(\cdot \mid 0) \mathbin{\square} f = f$. -/
@[simp] theorem indicatorFn_zero_infConv (f : E → EReal) :
    infConv (indicatorFn ({0} : Set E)) f = f := by
  rw [infConv_comm, infConv_indicatorFn_zero]

/-- The infimal convolute of two indicator functions is the indicator function of the sum of the
sets: $\delta(\cdot \mid S) \mathbin{\square} \delta(\cdot \mid T) = \delta(\cdot \mid S + T)$. -/
theorem infConv_indicatorFn (S T : Set E) :
    infConv (indicatorFn S) (indicatorFn T) = indicatorFn (S + T) := by
  have hepi : epi (indicatorFn S) + epi (indicatorFn T) = epi (indicatorFn (S + T)) := by
    rw [epi_indicatorFn, epi_indicatorFn, epi_indicatorFn]
    ext p
    constructor
    · rintro ⟨q, ⟨hq, hq0⟩, r, ⟨hr, hr0⟩, rfl⟩
      exact ⟨⟨q.1, hq, r.1, hr, rfl⟩,
        Set.mem_Ici.2 (add_nonneg (Set.mem_Ici.1 hq0) (Set.mem_Ici.1 hr0))⟩
    · rintro ⟨hw, hc⟩
      obtain ⟨a, ha, b, hb, hab⟩ := hw
      refine ⟨(a, p.2), ⟨ha, hc⟩, (b, 0), ⟨hb, Set.mem_Ici.2 (le_refl 0)⟩, ?_⟩
      have hab2 : a + b = p.1 := hab
      change ((a, p.2) : E × ℝ) + (b, 0) = p
      rw [Prod.mk_add_mk, hab2, add_zero]
  rw [infConv_def, hepi, ofEpi_epi]

/-- The supremal convolute of $-\delta(\cdot \mid S)$ and $-\delta(\cdot \mid T)$ is
$-\delta(\cdot \mid S + T)$. This is the concave form of `ConvexAnalysis.infConv_indicatorFn`. -/
theorem supConv_neg_indicatorFn (S T : Set E) :
    supConv (fun x => -(indicatorFn S x)) (fun x => -(indicatorFn T x))
      = fun x => -(indicatorFn (S + T) x) := by
  funext x
  simp only [supConv_def, neg_neg]
  rw [infConv_indicatorFn]

/-- If $g(0) \le 0$, then $f \mathbin{\square} g \le f$, because $g \le \delta(\cdot \mid 0)$. -/
theorem infConv_le_left (f : E → EReal) (hg : g 0 ≤ 0) : infConv f g ≤ f := by
  refine le_of_le_of_eq (infConv_mono (le_refl f) ?_) (infConv_indicatorFn_zero f)
  intro w
  by_cases hw : w = 0
  · subst hw
    simpa using hg
  · have hw' : w ∉ ({0} : Set E) := fun hmem => hw hmem
    simp [hw']

/-- If $f(0) \le 0$, then $f \mathbin{\square} g \le g$. -/
theorem infConv_le_right (hf : f 0 ≤ 0) (g : E → EReal) : infConv f g ≤ g := by
  rw [infConv_comm]
  exact infConv_le_left g hf

end Basic

/-! ### Convexity of an infimal convolute -/

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f g : E → EReal}

/-- Let $E$ be a real vector space. If $f, g \colon E \to [-\infty, +\infty]$ are convex, then
$f \mathbin{\square} g$ is convex.

No properness is needed. The classical hypothesis of properness only makes the infimum formula
meaningful, and the definition by epigraphs does not use that formula. -/
theorem convexFn_infConv (hf : ConvexFn f) (hg : ConvexFn g) : ConvexFn (infConv f g) :=
  convexFn_ofEpi (hf.convex_epi.add hg.convex_epi)

/-- Let $E$ be a real vector space. If $g, h \colon E \to [-\infty, +\infty]$ are concave, then
their supremal convolute is concave. -/
theorem concaveFn_supConv {h : E → EReal} (hg : ConcaveFn g) (hh : ConcaveFn h) :
    ConcaveFn (supConv g h) := by
  rw [concaveFn_iff_convexFn_neg]
  simp only [neg_supConv]
  exact convexFn_infConv hg.convexFn_neg hh.convexFn_neg

end Module

/-! ### Infimal convolution as a commutative monoid -/

/-- A copy of the type `E → EReal` of functions $E \to [-\infty, +\infty]$, whose addition is
infimal convolution and whose zero is $\delta(\cdot \mid 0)$.

The sum `∑ i ∈ s, ConvexAnalysis.toInfConvFn (f i)` is the infimal convolute $f_1
\mathbin{\square} \cdots \mathbin{\square} f_m$ of [rockafellar1970convex]. -/
def InfConvFn (E : Type*) : Type _ := E → EReal

/-- A function $E \to [-\infty, +\infty]$, as an element of `ConvexAnalysis.InfConvFn E`. -/
def toInfConvFn {E : Type*} (f : E → EReal) : InfConvFn E := f

/-- An element of `ConvexAnalysis.InfConvFn E`, as a function $E \to [-\infty, +\infty]$. -/
def ofInfConvFn {E : Type*} (F : InfConvFn E) : E → EReal := F

/-- Converting a function to `ConvexAnalysis.InfConvFn E` and back gives the same function. -/
@[simp] theorem ofInfConvFn_toInfConvFn {E : Type*} (f : E → EReal) :
    ofInfConvFn (toInfConvFn f) = f := rfl

/-- Converting an element of `ConvexAnalysis.InfConvFn E` to a function and back gives the same
element. -/
@[simp] theorem toInfConvFn_ofInfConvFn {E : Type*} (F : InfConvFn E) :
    toInfConvFn (ofInfConvFn F) = F := rfl

section Monoid

variable {E : Type*} [AddCommGroup E]

/-- The addition of `ConvexAnalysis.InfConvFn E` is infimal convolution. -/
noncomputable instance InfConvFn.instAdd : Add (InfConvFn E) := ⟨infConv⟩

/-- The zero of `ConvexAnalysis.InfConvFn E` is the indicator function $\delta(\cdot \mid 0)$. -/
noncomputable instance InfConvFn.instZero : Zero (InfConvFn E) := ⟨indicatorFn {0}⟩

/-- The sum of two functions in `ConvexAnalysis.InfConvFn E` is their infimal convolute. -/
@[simp] theorem toInfConvFn_add (f g : E → EReal) :
    toInfConvFn f + toInfConvFn g = toInfConvFn (infConv f g) := rfl

/-- The indicator function $\delta(\cdot \mid 0)$ is the zero of `ConvexAnalysis.InfConvFn E`. -/
@[simp] theorem toInfConvFn_indicatorFn_zero :
    toInfConvFn (indicatorFn ({0} : Set E)) = 0 := rfl

/-- As a function, the sum of $F$ and $G$ in `ConvexAnalysis.InfConvFn E` is the infimal convolute
of $F$ and $G$. -/
@[simp] theorem ofInfConvFn_add (F G : InfConvFn E) :
    ofInfConvFn (F + G) = infConv (ofInfConvFn F) (ofInfConvFn G) := rfl

/-- As a function, the zero of `ConvexAnalysis.InfConvFn E` is $\delta(\cdot \mid 0)$. -/
@[simp] theorem ofInfConvFn_zero :
    ofInfConvFn (0 : InfConvFn E) = indicatorFn ({0} : Set E) := rfl

/-- The functions $E \to [-\infty, +\infty]$ on an additive commutative group $E$ form a commutative
monoid under infimal convolution, with identity element $\delta(\cdot \mid 0)$. That is,
$\square$ is associative and commutative, and $f \mathbin{\square} \delta(\cdot \mid 0) =
\delta(\cdot \mid 0) \mathbin{\square} f = f$. -/
noncomputable instance InfConvFn.instAddCommMonoid : AddCommMonoid (InfConvFn E) where
  add := (· + ·)
  zero := 0
  add_assoc := infConv_assoc
  zero_add := indicatorFn_zero_infConv
  add_zero := infConv_indicatorFn_zero
  add_comm := infConv_comm
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl

end Monoid

section MonoidConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Let $E$ be a real vector space and let $f_i \colon E \to [-\infty, +\infty]$ be convex for every
$i$ in a finite set $s$. Then the infimal convolute of the $f_i$, $i \in s$, is convex.

For $s = \emptyset$ the infimal convolute is $\delta(\cdot \mid 0)$, which is convex because
$\{0\}$ is convex. -/
theorem convexFn_sum_toInfConvFn {ι : Type*} {s : Finset ι} {f : ι → E → EReal}
    (hf : ∀ i ∈ s, ConvexFn (f i)) :
    ConvexFn (ofInfConvFn (∑ i ∈ s, toInfConvFn (f i))) := by
  induction s using Finset.cons_induction with
  | empty => simpa using convexFn_indicatorFn.2 (convex_singleton (0 : E))
  | cons i t hi ih =>
    rw [Finset.sum_cons]
    simp only [ofInfConvFn_add, ofInfConvFn_toInfConvFn]
    exact convexFn_infConv (hf i (by simp)) (ih fun j hj => hf j (by simp [hj]))

end MonoidConvex

section MonoidSum

variable {ι E : Type*} [AddCommGroup E] {s : Finset ι} {g : ι → E → EReal}

/-- Let $s$ be a finite set, let $g_i \colon E \to [-\infty, +\infty]$, $y_i \in E$ and
$c_i \in \mathbb{R}$ for $i \in s$, and let $g_i(y_i) \le c_i$ for every $i \in s$. Then $$\Big(
\mathop{\square}_{i \in s} g_i \Big) \Big( \sum_{i \in s} y_i \Big) \le \sum_{i \in s} c_i.$$

This is `ConvexAnalysis.infConv_apply_le` applied repeatedly. No hypothesis on the values of the
$g_i$ is needed. -/
theorem sum_toInfConvFn_apply_le {y : ι → E} {c : ι → ℝ}
    (h : ∀ i ∈ s, g i (y i) ≤ (c i : EReal)) :
    ofInfConvFn (∑ i ∈ s, toInfConvFn (g i)) (∑ i ∈ s, y i) ≤ ((∑ i ∈ s, c i : ℝ) : EReal) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, Finset.sum_empty, ofInfConvFn_zero,
      indicatorFn_of_mem (s := ({0} : Set E)) (Set.mem_singleton_iff.2 rfl)]
    exact_mod_cast le_rfl
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_cons, ofInfConvFn_add,
      ofInfConvFn_toInfConvFn]
    exact infConv_apply_le (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

/-- Let $s$ be a finite set, let $g_i \colon E \to [-\infty, +\infty]$ never take the value
$-\infty$ for $i \in s$, and let $y_i \in E$. Then $$\Big( \mathop{\square}_{i \in s} g_i \Big)
\Big( \sum_{i \in s} y_i \Big) \le \sum_{i \in s} g_i(y_i).$$

The hypothesis is on each $g_i$ separately, not on a partial convolute. Infimal convolution does
not preserve the property of never taking the value $-\infty$: on $\mathbb{R}$, $g_1(x) = -x$
and $g_2(x) = x$ are finite everywhere, but $g_1 \mathbin{\square} g_2 \equiv -\infty$. -/
theorem sum_toInfConvFn_le_sum (hg : ∀ i ∈ s, ∀ x, g i x ≠ ⊥) (y : ι → E) :
    ofInfConvFn (∑ i ∈ s, toInfConvFn (g i)) (∑ i ∈ s, y i) ≤ ∑ i ∈ s, g i (y i) := by
  rcases eq_or_ne (∑ i ∈ s, g i (y i)) ⊤ with htop | htop
  · rw [htop]; exact le_top
  have hfin : ∀ i ∈ s, g i (y i) ≠ ⊤ :=
    EReal.forall_ne_top_of_sum_ne_top s _ (fun i hi => hg i hi (y i)) htop
  have hci : ∀ i ∈ s, g i (y i) = (((g i (y i)).toReal : ℝ) : EReal) := fun i hi =>
    (EReal.coe_toReal (hfin i hi) (hg i hi (y i))).symm
  have hsum : ∑ i ∈ s, g i (y i) = ((∑ i ∈ s, (g i (y i)).toReal : ℝ) : EReal) := by
    rw [EReal.coe_sum]
    exact Finset.sum_congr rfl hci
  rw [hsum]
  exact sum_toInfConvFn_apply_le fun i hi => (hci i hi).le

/-- For a finite set $s$ and functions $g_i \colon E \to [-\infty, +\infty]$, the effective domain
of the infimal convolute of the $g_i$, $i \in s$, is $\sum_{i \in s} \operatorname{dom} g_i$. No
hypothesis is needed. For $s = \emptyset$ the infimal convolute is $\delta(\cdot \mid 0)$, whose
effective domain $\{0\}$ is the empty sum of sets. -/
theorem convexDom_sum_toInfConvFn (s : Finset ι) (g : ι → E → EReal) :
    convexDom (ofInfConvFn (∑ i ∈ s, toInfConvFn (g i))) = ∑ i ∈ s, convexDom (g i) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ofInfConvFn_zero, convexDom_indicatorFn,
      Set.singleton_zero]
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, ofInfConvFn_add, ofInfConvFn_toInfConvFn,
        convexDom_infConv,
      ih]

end MonoidSum

end ConvexAnalysis
