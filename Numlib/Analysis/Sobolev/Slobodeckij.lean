/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/MultiIndex.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.MultiIndex

/-!
# The Sobolev–Slobodeckij spaces of fractional order

Let $\Omega$ be an open subset of a real normed space $E$ of dimension $d$, let $k \ge 0$ be an
integer, and let $0 < \sigma < 1$. The Sobolev–Slobodeckij space $W^{s,p}(\Omega)$ of real order
$s = k + \sigma$ consists of the functions $v$ of the integer-order space $W^{k,p}(\Omega)$ whose
weak derivatives of top order have a finite Sobolev–Slobodeckij (or Gagliardo) seminorm
$$[v]_{\sigma,p,\Omega} = \Big[\sum_{|\alpha| = k} \int_{\Omega \times \Omega}
  \frac{|\partial^\alpha v(x) - \partial^\alpha v(y)|^p}{\|x - y\|^{\sigma p + d}}
  \, dx \, dy\Big]^{1/p},$$
with the norm $\|v\|_{s,p,\Omega} = [\|v\|_{k,p,\Omega}^p + [v]_{\sigma,p,\Omega}^p]^{1/p}$. This is
Definition 7.2.10 of [han2009theoretical], and the closure $W_0^{s,p}(\Omega)$ of the test functions
in it is Definition 7.2.11 there. This module defines both spaces and proves that the norm of the
Lean type is the displayed norm. Below, $Q_{\sigma,p} w$ is the difference quotient $(x, y) \mapsto
(w(x) - w(y)) / \|x - y\|^{\sigma + d/p}$, so that $\partial^\alpha v$ contributes to the seminorm
through the $L^p(\Omega \times \Omega)$ norm of $Q_{\sigma,p} \partial^\alpha v$.

The integer-order space with the norm $\|v\|_{k,p,\Omega}$ is `SobolevMultiIndex` of
`Numlib.Analysis.Sobolev.MultiIndex`, whose derivatives are indexed by multi-indices. This module is
its extension to fractional order: the norm above adjoins the seminorm to that norm in the $\ell^p$
combination. Nothing here reduces to the integer-order space at $\sigma = 0$, because the seminorm
diverges there. The integer-order space is a separate object, as it is in the source.

## Main definitions

* `prodRestrict`: the measure $\mu|_\Omega \otimes \mu|_\Omega$ on $\Omega \times \Omega$, over
  which the seminorm is taken.
* `slobodeckijQuotient`: the difference quotient $Q_{\sigma,p} w$, whose membership in
  $L^p(\Omega \times \Omega)$ is the condition that the space imposes on $w = \partial^\alpha v$.
* `SobolevSlobodeckijTuple`: the ambient space, pairs of a family of $L^p(\Omega)$ functions and a
  family of $L^p(\Omega \times \Omega)$ functions in the $\ell^p$ norm.
* `SobolevSlobodeckij`, with `SobolevSlobodeckij.fn`, `SobolevSlobodeckij.toSobolevMultiIndex`
  and `SobolevSlobodeckij.testFunctions`: the space $W^{s,p}(\Omega)$, the function of an element,
  its integer-order part, and the image of the test functions.
* `SobolevSlobodeckijZero`: the space $W_0^{s,p}(\Omega)$, the closure of the test functions in
  $W^{s,p}(\Omega)$.

## Main results

* `slobodeckijQuotient_congr_ae`: if $w = w'$ almost everywhere on $\Omega$, then
  $Q_{\sigma,p} w = Q_{\sigma,p} w'$ almost everywhere on $\Omega \times \Omega$, so the condition
  is well posed on weak derivatives.
* `SobolevSlobodeckij.ext_of_fn_ae_eq`: an element of $W^{s,p}(\Omega)$ is determined by its
  function up to a null set.
* `SobolevSlobodeckij.norm_eq_add` and `SobolevSlobodeckij.norm_snd_rpow`: for $1 \le p < \infty$,
  the norm of the space is the norm $\|v\|_{s,p,\Omega}$ displayed above.

## Implementation notes

* The space is a submodule of a pair. An element is a family $(\partial^\alpha v)_{|\alpha| \le k}$
  of $W^{k,p}(\Omega)$ together with a family $(h_\alpha)_{|\alpha| = k}$ of
  $L^p(\Omega \times \Omega)$ functions, constrained to be the difference quotients
  $h_\alpha = Q_{\sigma,p} \partial^\alpha v$ of its top-order members. The two families are
  combined in the $\ell^p$ norm of `WithLp p (· × ·)`. The norm of the pair is then the displayed
  norm without any rewriting, which is the reason for this shape; `SobolevSlobodeckij.norm_eq_add`
  together with `SobolevSlobodeckij.norm_snd_rpow` is the proof. The same device makes
  `SobolevMultiIndex` a submodule of a `PiLp p` of $L^p(\Omega)$ spaces.
* Like `Numlib.Analysis.Sobolev.MultiIndex`, this module does not follow the API of Mathlib PR 32305
  and its continuation `grunweg/SobolevSlobodeckij` (Michael Rothgang, Filippo Nuccio and Floris van
  Doorn). There the weak derivative is tensor-valued and uses no basis, whereas the seminorm here is
  a sum over the multi-indices of top order, which is the form that the source displays. Despite its
  name, that development contains the integer-order space. If it gets a fractional-order space, that
  space should be compared with this module.
* The module does not prove that $W^{s,p}(\Omega)$ is a Banach space (and reflexive exactly for
  $1 < p < \infty$, and a Hilbert space for $p = 2$), which the source states without proof.
  Completeness would need the submodule to be closed in the ambient pair space, which is a further
  argument.
* The module does not prove that $C_0^\infty(\Omega) \subseteq W^{s,p}(\Omega)$, which the source
  also states without proof. Thus `SobolevSlobodeckij.testFunctions` is the image of
  $C_0^\infty(\Omega) \cap W^{s,p}(\Omega)$. This is what "$C_0^\infty(\Omega)$ as a subset of
  $W^{s,p}(\Omega)$" means in any case, so `SobolevSlobodeckijZero` is the space of Definition
  7.2.11 as it stands. But nothing here produces a nonzero element of it, and there is no analogue
  of `TestFunction.exists_mem_testFunctions`.
* The missing inclusion is true whenever $0 < \sigma < 1$ and $1 \le p < \infty$, by this argument.
  A test function $\varphi$ satisfies $|\partial^\alpha \varphi(x) - \partial^\alpha \varphi(y)| \le
  L \|x - y\|$, because it is smooth with compact support. So the integrand is at most
  $L^p \|x - y\|^{p(1 - \sigma) - d}$. Bound this by $G(x - y)$, where $G$ is the same power cut off
  outside a ball that contains $\Omega - \Omega$, and integrate by Tonelli's theorem. The
  translation invariance of $\mu$ replaces the inner integral $\int G(x - y) \, dy$ by
  $\int G(z) \, dz$, which is finite by `MeasureTheory.integrableOn_ball_of_norm_le_rpow` because
  the exponent $d - p(1 - \sigma)$ is less than $d$. The difficulty in this argument is a Lipschitz
  constant for `iteratedFDeriv` of a test function.
-/

open Filter MeasureTheory Module Set TopologicalSpace

open scoped Distributions ENNReal Topology

/-! ### The difference quotient -/

section Quotient

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {σ : ℝ} {p : ℝ≥0∞} {w w' : E → F}

variable (Ω μ) in
/-- The product measure $\mu|_\Omega \otimes \mu|_\Omega$ on $E \times E$, where $\mu|_\Omega$ is
the restriction of the measure $\mu$ to the open set $\Omega$. The Sobolev–Slobodeckij seminorm
of `SobolevSlobodeckij` is an integral over $\Omega \times \Omega$ for this measure. -/
noncomputable abbrev prodRestrict (Ω : Opens E) (μ : Measure E) : Measure (E × E) :=
  (μ.restrict (Ω : Set E)).prod (μ.restrict (Ω : Set E))

/-- Let $E$ and $F$ be real normed spaces, let $d = \dim E$, and let $\sigma \in \mathbb{R}$ and
$p \in [0, \infty]$. The **Slobodeckij difference quotient** of a function $w : E \to F$ is the
function $Q_{\sigma,p} w : E \times E \to F$,
$$Q_{\sigma,p} w(x, y) = \frac{w(x) - w(y)}{\|x - y\|^{\sigma + d/p}}.$$
Definition 7.2.10 of [han2009theoretical] asks that $Q_{\sigma,p} \partial^\alpha v$ lie in
$L^p(\Omega \times \Omega)$ for the weak derivatives $\partial^\alpha v$ of top order. The
$p$-th power of $\|Q_{\sigma,p} w\|$ is the integrand
$\|w(x) - w(y)\|^p / \|x - y\|^{\sigma p + d}$ of the seminorm displayed there.

The source writes the numerator in absolute value. This does not matter, because membership in
$L^p$ depends on a function only through its norm. The value is the scalar
$(\|x - y\|^{\sigma + d/p})^{-1}$ times $w(x) - w(y)$, so it is $0$ on the diagonal $x = y$. The
number $d$ is `Module.finrank ℝ E`, which is $0$ when $E$ is infinite-dimensional, and $d/p$
uses `ENNReal.toReal p`, so it is $0$ for $p = \infty$. -/
noncomputable def slobodeckijQuotient (σ : ℝ) (p : ℝ≥0∞) (w : E → F) : E × E → F :=
  fun z ↦ (‖z.1 - z.2‖ ^ (σ + finrank ℝ E / p.toReal))⁻¹ • (w z.1 - w z.2)

omit [MeasurableSpace E] in
/-- For all $x, y \in E$, the norm of the difference quotient is the quotient of norms
$$\|Q_{\sigma,p} w(x, y)\| = \frac{\|w(x) - w(y)\|}{\|x - y\|^{\sigma + d/p}}.$$
-/
theorem norm_slobodeckijQuotient (σ : ℝ) (p : ℝ≥0∞) (w : E → F) (z : E × E) :
    ‖slobodeckijQuotient σ p w z‖ =
      ‖w z.1 - w z.2‖ / ‖z.1 - z.2‖ ^ (σ + finrank ℝ E / p.toReal) := by
  simp only [slobodeckijQuotient, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [← div_eq_inv_mul]

omit [MeasurableSpace E] in
/-- The difference quotient is additive in the function: $Q_{\sigma,p}(w + w') = Q_{\sigma,p} w +
Q_{\sigma,p} w'$. -/
theorem slobodeckijQuotient_add :
    slobodeckijQuotient σ p (w + w') = slobodeckijQuotient σ p w + slobodeckijQuotient σ p w' := by
  funext z
  simp only [slobodeckijQuotient, Pi.add_apply, smul_sub, smul_add]
  abel

omit [MeasurableSpace E] in
/-- The difference quotient is homogeneous in the function:
$Q_{\sigma,p}(c w) = c \, Q_{\sigma,p} w$ for every $c \in \mathbb{R}$. -/
theorem slobodeckijQuotient_smul (c : ℝ) :
    slobodeckijQuotient σ p (c • w) = c • slobodeckijQuotient σ p w := by
  funext z
  simp only [slobodeckijQuotient, Pi.smul_apply]
  module

/-- Let $\mu$ be an s-finite measure on $E$ and let $\Omega \subseteq E$ be open. If $w = w'$
$\mu$-almost everywhere on $\Omega$, then $Q_{\sigma,p} w = Q_{\sigma,p} w'$ almost everywhere
on $\Omega \times \Omega$ for the measure $\mu|_\Omega \otimes \mu|_\Omega$. Hence the condition
in `SobolevSlobodeckij` is a condition on the weak derivatives $\partial^\alpha v$, which are
determined only almost everywhere.

The proof uses that both projections of the product measure are quasi measure preserving. -/
theorem slobodeckijQuotient_congr_ae {Ω : Opens E} {μ : Measure E} [SFinite μ]
    (h : w =ᵐ[μ.restrict (Ω : Set E)] w') :
    slobodeckijQuotient σ p w =ᵐ[prodRestrict Ω μ] slobodeckijQuotient σ p w' := by
  have h1 := h.comp_tendsto (Measure.quasiMeasurePreserving_fst
    (μ := μ.restrict (Ω : Set E)) (ν := μ.restrict (Ω : Set E))).tendsto_ae
  have h2 := h.comp_tendsto (Measure.quasiMeasurePreserving_snd
    (μ := μ.restrict (Ω : Set E)) (ν := μ.restrict (Ω : Set E))).tendsto_ae
  filter_upwards [h1, h2] with z hz1 hz2
  simp only [slobodeckijQuotient, Function.comp_apply] at *
  rw [hz1, hz2]

end Quotient

/-! ### The space $W^{s,p}(\Omega)$ -/

section Space

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι] [LinearOrder ι]
  {b : Basis ι ℝ E} {k : ℕ} {σ : ℝ} {p : ℝ≥0∞} {Ω : Opens E} {μ : Measure E}

variable (F ι k p Ω μ) in
/-- The ambient space of $W^{s,p}(\Omega)$ for $s = k + \sigma$. An element is a pair $(U_1, U_2)$:
$U_1 = (w_\alpha)_{|\alpha| \le k}$ is a family of $L^p(\Omega)$ functions indexed by the
multi-indices of order at most $k$, an element of `SobolevMultiIndexTuple F ι k p Ω μ`, and
$U_2 = (h_\alpha)_{|\alpha| = k}$ is a family of $L^p(\Omega \times \Omega)$ functions indexed
by the multi-indices of order exactly $k$. The norm is the $\ell^p$ combination of the $\ell^p$
norm of $U_1$ and the $\ell^p$ norm of the family of the norms
$\|h_\alpha\|_{L^p(\Omega \times \Omega)}$.

`SobolevSlobodeckij` is the subspace in which $h_\alpha$ is the difference quotient of
$w_\alpha$, and on it this norm is the norm of Definition 7.2.10 of [han2009theoretical]. The
pair is a `WithLp p` of a product, the second family is a `PiLp p`, and
$L^p(\Omega \times \Omega)$ is taken for the measure `prodRestrict Ω μ`. -/
abbrev SobolevSlobodeckijTuple : Type _ :=
  WithLp p (SobolevMultiIndexTuple F ι k p Ω μ ×
    PiLp p fun _ : MultiIndexEq ι k ↦ Lp F p (prodRestrict Ω μ))

variable [OpensMeasurableSpace E] [SFinite μ]

variable (F b k σ p Ω μ) in
/-- Let $E$ be a real normed space with a basis $b$ indexed by a finite linearly ordered type
$\iota$, with a σ-algebra in which the open sets are measurable, and let $\mu$ be an s-finite
measure on $E$. Let $F$ be a real normed space, $\Omega \subseteq E$ open, $k \in \mathbb{N}$,
$\sigma \in \mathbb{R}$ and $p \in [0, \infty]$. The **Sobolev–Slobodeckij space**
$W^{s,p}(\Omega)$ of order $s = k + \sigma$ is the subspace of
`SobolevSlobodeckijTuple F ι k p Ω μ` of the pairs $((w_\beta)_{|\beta| \le k},
(h_\alpha)_{|\alpha| = k})$ such that the first family lies in $W^{k,p}(\Omega)$, so that
$w_\beta = \partial^\beta v$ for the function $v = w_0$, and such that for each $\alpha$ with
$|\alpha| = k$
$$h_\alpha(x, y) = \frac{\partial^\alpha v(x) - \partial^\alpha v(y)}{\|x - y\|^{\sigma +
  d/p}}$$
for almost every $(x, y) \in \Omega \times \Omega$. This is Definition 7.2.10 of
[han2009theoretical].

The source takes $0 < \sigma < 1$. That restriction makes this the space of the source, but the
definition is well formed without it, and it is not imposed here. The space $W^{k,p}(\Omega)$ is
`SobolevMultiIndex F b k p Ω μ`, with multi-indices taken with respect to $b$, and the quotient
is `slobodeckijQuotient`. The norm that the space has as a subspace of an $\ell^p$ combination
is the norm of the source, by `SobolevSlobodeckij.norm_eq_add` and
`SobolevSlobodeckij.norm_snd_rpow`. -/
def SobolevSlobodeckij (k : ℕ) (σ : ℝ) (p : ℝ≥0∞) (Ω : Opens E) (μ : Measure E)
    [SFinite μ] : Submodule ℝ (SobolevSlobodeckijTuple F ι k p Ω μ) where
  carrier := {U | U.fst ∈ SobolevMultiIndex F b k p Ω μ ∧
    ∀ α : MultiIndexEq ι k,
      U.snd α =ᵐ[prodRestrict Ω μ] slobodeckijQuotient σ p (U.fst α.1)}
  zero_mem' := by
    refine ⟨Submodule.zero_mem _, fun α ↦ ?_⟩
    have h1 : slobodeckijQuotient σ p ((0 : SobolevSlobodeckijTuple F ι k p Ω μ).fst α.1 : E → F)
        =ᵐ[prodRestrict Ω μ] 0 := by
      refine (slobodeckijQuotient_congr_ae (Ω := Ω) (Lp.coeFn_zero F p _)).trans ?_
      filter_upwards with z
      simp [slobodeckijQuotient]
    exact (Lp.coeFn_zero F p _).trans h1.symm
  add_mem' := by
    rintro U V ⟨hU1, hU2⟩ ⟨hV1, hV2⟩
    refine ⟨Submodule.add_mem _ hU1 hV1, fun α ↦ ?_⟩
    refine (Lp.coeFn_add _ _).trans ((hU2 α).add (hV2 α)) |>.trans ?_
    exact ((slobodeckijQuotient_congr_ae (Ω := Ω) (Lp.coeFn_add (U.fst α.1) (V.fst α.1))).trans
      (by rw [slobodeckijQuotient_add])).symm
  smul_mem' := by
    rintro c U ⟨hU1, hU2⟩
    refine ⟨Submodule.smul_mem _ c hU1, fun α ↦ ?_⟩
    refine (Lp.coeFn_smul _ _).trans ((hU2 α).const_smul c) |>.trans ?_
    exact ((slobodeckijQuotient_congr_ae (Ω := Ω) (Lp.coeFn_smul c (U.fst α.1))).trans
      (by rw [slobodeckijQuotient_smul])).symm

namespace SobolevSlobodeckij

/-- The $W^{k,p}(\Omega)$ part of an element of $W^{s,p}(\Omega)$: its first family
$(\partial^\beta v)_{|\beta| \le k}$, as an element of the integer-order space
`SobolevMultiIndex F b k p Ω μ`. -/
def toSobolevMultiIndex (U : SobolevSlobodeckij F b k σ p Ω μ) : SobolevMultiIndex F b k p Ω μ :=
  ⟨(U : SobolevSlobodeckijTuple F ι k p Ω μ).fst, U.2.1⟩

/-- The function $v$ underlying an element of $W^{s,p}(\Omega)$: the component at the multi-index
$0$ of its first family. An element is a term of a `Submodule`, so this is written
`SobolevSlobodeckij.fn U` rather than `U.fn`. -/
noncomputable def fn (U : SobolevSlobodeckij F b k σ p Ω μ) : E → F :=
  SobolevMultiIndexTuple.fn (U : SobolevSlobodeckijTuple F ι k p Ω μ).fst

/-- The function underlying an element of $W^{s,p}(\Omega)$ is the function underlying its
$W^{k,p}(\Omega)$ part `SobolevSlobodeckij.toSobolevMultiIndex`. -/
theorem fn_toSobolevMultiIndex (U : SobolevSlobodeckij F b k σ p Ω μ) :
    SobolevMultiIndex.fn (toSobolevMultiIndex U) = fn U := rfl

/-- For an element $((w_\beta)_{|\beta| \le k}, (h_\alpha)_{|\alpha| = k})$ of $W^{s,p}(\Omega)$ and
each multi-index $\alpha$ with $|\alpha| = k$, the function $h_\alpha$ equals the difference
quotient $Q_{\sigma,p} w_\alpha$ almost everywhere on $\Omega \times \Omega$. -/
theorem snd_ae (U : SobolevSlobodeckij F b k σ p Ω μ) (α : MultiIndexEq ι k) :
    ((U : SobolevSlobodeckijTuple F ι k p Ω μ).snd α : E × E → F) =ᵐ[prodRestrict Ω μ]
      slobodeckijQuotient σ p ((U : SobolevSlobodeckijTuple F ι k p Ω μ).fst α.1) := U.2.2 α


/-- Let $E$ be finite-dimensional with its Borel σ-algebra, and let $F$ be complete. If the
functions of two elements $U$ and $V$ of $W^{s,p}(\Omega)$ agree almost everywhere on $\Omega$,
then $U = V$.

The first family is determined by its function, by `SobolevMultiIndex.ext_of_fn_ae_eq`, and the
second family consists of the difference quotients of the first, by `SobolevSlobodeckij.snd_ae`. -/
theorem ext_of_fn_ae_eq [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]
    {U V : SobolevSlobodeckij F b k σ p Ω μ} (h : fn U =ᵐ[μ.restrict (Ω : Set E)] fn V) :
    U = V := by
  have h1 : toSobolevMultiIndex U = toSobolevMultiIndex V := SobolevMultiIndex.ext_of_fn_ae_eq h
  have h1' : (U : SobolevSlobodeckijTuple F ι k p Ω μ).fst
      = (V : SobolevSlobodeckijTuple F ι k p Ω μ).fst := congrArg Subtype.val h1
  refine Subtype.ext ((WithLp.ext_iff _).2 (Prod.ext h1' ?_))
  ext α
  have e := snd_ae V α
  rw [← h1'] at e
  exact (snd_ae U α).trans e.symm
/-- The function of the zero element of $W^{s,p}(\Omega)$ is $0$ almost everywhere on $\Omega$. -/
theorem fn_zero : fn (0 : SobolevSlobodeckij F b k σ p Ω μ) =ᵐ[μ.restrict (Ω : Set E)] 0 :=
  SobolevMultiIndexTuple.fn_zero

/-- The function of a sum $U + V$ in $W^{s,p}(\Omega)$ is, almost everywhere on $\Omega$, the sum of
the functions of $U$ and $V$. -/
theorem fn_add (U V : SobolevSlobodeckij F b k σ p Ω μ) :
    fn (U + V) =ᵐ[μ.restrict (Ω : Set E)] fn U + fn V :=
  SobolevMultiIndexTuple.fn_add _ _

/-- The function of a scalar multiple $c U$ in $W^{s,p}(\Omega)$ is, almost everywhere on $\Omega$,
$c$ times the function of $U$. -/
theorem fn_smul (c : ℝ) (U : SobolevSlobodeckij F b k σ p Ω μ) :
    fn (c • U) =ᵐ[μ.restrict (Ω : Set E)] c • fn U :=
  SobolevMultiIndexTuple.fn_smul _ _

variable [Fact (1 ≤ p)]

/-- Let $1 \le p < \infty$. For an element $U = ((w_\beta)_{|\beta| \le k}, (h_\alpha)_{|\alpha| =
k})$ of $W^{s,p}(\Omega)$,
$$\|U\| = \Big(\sum_{|\beta| \le k} \|w_\beta\|_{L^p(\Omega)}^p + \sum_{|\alpha| = k}
  \|h_\alpha\|_{L^p(\Omega \times \Omega)}^p\Big)^{1/p}.$$
The first sum is $\|v\|_{k,p,\Omega}^p$, by `SobolevMultiIndex.norm_eq_sum`, and the second is
the $p$-th power $[v]_{\sigma,p,\Omega}^p$ of the Sobolev–Slobodeckij seminorm, by
`SobolevSlobodeckij.norm_snd_rpow`. Together they give the norm of Definition 7.2.10 of
[han2009theoretical]. -/
theorem norm_eq_add (hp : p ≠ ⊤) (U : SobolevSlobodeckij F b k σ p Ω μ) :
    ‖U‖ = ((∑ α : MultiIndexLE ι k,
          ‖(U : SobolevSlobodeckijTuple F ι k p Ω μ).fst α‖ ^ p.toReal)
        + ∑ α : MultiIndexEq ι k,
          ‖(U : SobolevSlobodeckijTuple F ι k p Ω μ).snd α‖ ^ p.toReal) ^ (1 / p.toReal) := by
  have htp := p.toReal_pos_iff_ne_top.mpr hp
  rw [← Submodule.norm_coe, WithLp.prod_norm_eq_add htp, PiLp.norm_eq_sum htp,
    PiLp.norm_eq_sum htp, one_div, Real.rpow_inv_rpow (by positivity) htp.ne',
    Real.rpow_inv_rpow (by positivity) htp.ne']

/-- The **Sobolev–Slobodeckij seminorm**. Let $1 \le p < \infty$. For an element
$((w_\beta)_{|\beta| \le k}, (h_\alpha)_{|\alpha| = k})$ of $W^{s,p}(\Omega)$ and a multi-index
$\alpha$ with $|\alpha| = k$,
$$\|h_\alpha\|_{L^p(\Omega \times \Omega)}^p = \int_{\Omega \times \Omega}
  \frac{\|w_\alpha(x) - w_\alpha(y)\|^p}{\|x - y\|^{\sigma p + d}} \, d\mu(x) \, d\mu(y).$$
The sum of these integrals over $|\alpha| = k$ is the $p$-th power of the seminorm
$[v]_{\sigma,p,\Omega}$ of Definition 7.2.10 of [han2009theoretical]. -/
theorem norm_snd_rpow (hp : p ≠ ⊤) (U : SobolevSlobodeckij F b k σ p Ω μ) (α : MultiIndexEq ι k) :
    ‖(U : SobolevSlobodeckijTuple F ι k p Ω μ).snd α‖ ^ p.toReal =
      ∫ z, ‖((U : SobolevSlobodeckijTuple F ι k p Ω μ).fst α.1 : E → F) z.1
            - ((U : SobolevSlobodeckijTuple F ι k p Ω μ).fst α.1 : E → F) z.2‖ ^ p.toReal
          / ‖z.1 - z.2‖ ^ (σ * p.toReal + finrank ℝ E) ∂(prodRestrict Ω μ) := by
  have htp := p.toReal_pos_iff_ne_top.mpr hp
  have h0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  rw [Lp.norm_def, (Lp.memLp _).eLpNorm_eq_integral_rpow_norm h0 hp,
    ENNReal.toReal_ofReal (by positivity), Real.rpow_inv_rpow (by positivity) htp.ne']
  refine integral_congr_ae ?_
  filter_upwards [snd_ae U α] with z hz
  rw [hz, norm_slobodeckijQuotient,
    Real.div_rpow (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg _)]
  congr 2
  field_simp

variable (F b k σ p Ω μ) in
/-- The image of the test functions $C_0^\infty(\Omega)$ in $W^{s,p}(\Omega)$: the submodule of the
elements whose function agrees almost everywhere on $\Omega$ with a test function on $\Omega$.

Unlike its counterpart `Sobolev.testFunctions` for integer order, this submodule comes with no
proof that every test function occurs; the implementation notes of the module say what that
statement is and how it can be proved. So this submodule is the image of
$C_0^\infty(\Omega) \cap W^{s,p}(\Omega)$, which is what "$C_0^\infty(\Omega)$ as a subset of
$W^{s,p}(\Omega)$" means in any case. -/
def testFunctions : Submodule ℝ (SobolevSlobodeckij F b k σ p Ω μ) where
  carrier := {U | ∃ φ : 𝓓(Ω, F), fn U =ᵐ[μ.restrict (Ω : Set E)] φ}
  zero_mem' := ⟨0, fn_zero⟩
  add_mem' := fun {U V} ⟨φ, hφ⟩ ⟨ψ, hψ⟩ ↦ ⟨φ + ψ, (fn_add U V).trans (hφ.add hψ)⟩
  smul_mem' := fun c U ⟨φ, hφ⟩ ↦ ⟨c • φ, (fn_smul c U).trans (hφ.const_smul c)⟩

end SobolevSlobodeckij

variable (F b k σ p Ω μ) in
/-- Let $p \ge 1$. The **Sobolev–Slobodeckij space** $W_0^{s,p}(\Omega)$ is the closure of
$C_0^\infty(\Omega)$ in $W^{s,p}(\Omega)$. This is Definition 7.2.11 of [han2009theoretical].

The closure is taken in the norm of $W^{s,p}(\Omega)$, which for an order $s$ that is not an
integer is strictly stronger than the norm of $W^{k,p}(\Omega)$. This is the point of the
definition, because $C_0^\infty(\Omega)$ is dense in neither space in general. The set whose
closure is taken is `SobolevSlobodeckij.testFunctions`; see the implementation notes of the
module. -/
noncomputable def SobolevSlobodeckijZero [Fact (1 ≤ p)] :
    Submodule ℝ (SobolevSlobodeckij F b k σ p Ω μ) :=
  (SobolevSlobodeckij.testFunctions F b k σ p Ω μ).topologicalClosure

end Space
