/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Calculus.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.Calculus

/-!
# The affine change of variables in $L^p$ and in $W^{m,p}$

Let $E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$, let
$T \colon E \to E$ be a continuous linear bijection, let $c \in E$, and let $F(x) = Tx + c$. This
module transports $L^p$ norms, $L^p$ membership, $W^{m,p}$ membership and the top-order Sobolev
seminorm along $F$, from an open set $\Omega$ to its preimage $F^{-1}(\Omega)$. It is the general
content of Theorem 10.3.4 of [han2009theoretical], whose reference element technique rests on the
two estimates
$$|v \circ F|_{m,p,F^{-1}\Omega} \le \|T\|^m |\det T|^{-1/p} |v|_{m,p,\Omega} \qquad (10.3.5)$$
and
$$|v|_{m,p,\Omega} \le \|T^{-1}\|^m |\det T|^{1/p} |v \circ F|_{m,p,F^{-1}\Omega} \qquad (10.3.6).$$
The second estimate is the first one for $F^{-1}$.

The $L^p$ norm changes by the factor $|\det T|^{-1/p}$, by the pushforward formula for $\mu$ under
$F$. The weak derivative of order $n$ of $v \circ F$ is $x \mapsto \partial^n v(F x) \circ (T,
\dots, T)$, which has operator norm at most $\|T\|^n \|\partial^n v(F x)\|$. Together these give
(10.3.5).

## Main definitions

* `affinePreimage`: the open set $F^{-1}(\Omega)$.

## Main results

* `eLpNorm_comp_affine`: $\|f \circ F\|_{L^p(F^{-1}A)} = |\det T|^{-1/p} \|f\|_{L^p(A)}$ for every
  exponent $p$ and every measurable set $A$.
* `memLp_comp_affine`: $f \in L^p(A)$ implies $f \circ F \in L^p(F^{-1}A)$.
* `memSobolev_comp_affine`, `memSobolev_comp_affine_iff`: $v \in W^{m,p}(\Omega)$ if and only if
  $v \circ F \in W^{m,p}(F^{-1}\Omega)$, for every order $m \in \mathbb{N} \cup \{\infty\}$ and
  every exponent $p$.
* `sobolevSeminorm_comp_affine_le`: the estimate (10.3.5) for every exponent $p$.
* `sobolevSeminorm_comp_affine_le_of_image`, `sobolevSeminorm_le_comp_affine_of_image`: the
  estimates (10.3.5) and (10.3.6) at $p = 2$, for a reference set $\hat K$ and its image
  $K = F(\hat K)$.
* `memSobolev_comp_affine_inv`: $\varphi \in W^{m,p}(\hat K)$ implies
  $\varphi \circ F^{-1} \in W^{m,p}(K)$.
* `ContinuousLinearEquiv.det_symm_eq_inv`: $\det T^{-1} = (\det T)^{-1}$.
* `closure_affinePreimage`, `ContinuousOn.comp_affine_closure`: the closure of $F^{-1}(\Omega)$ is
  $F^{-1}(\overline{\Omega})$, so a function that is continuous on $\overline{\Omega}$ composes with
  $F$ to a function that is continuous on $\overline{F^{-1}(\Omega)}$.

## Implementation notes

* The seminorm is `sobolevSeminorm` of `Numlib.Analysis.Sobolev.Domain`: the $L^p(\Omega)$ norm of
  the operator norm of the weak derivative tensor of order $m$. For this seminorm the constants are
  exactly the ones displayed above, with no factor that depends on the dimension, by
  `ContinuousMultilinearMap.norm_compContinuousLinearMap_le`.
* The identity for the weak derivative is `HasWeakIteratedFDerivOn.comp_affineEquiv` of
  `Numlib.Analysis.Sobolev.Calculus`, and the pushforward formula is `map_affine_addHaar`. The $L^p$
  identity needs no measurability of $f$, by `MeasurableEmbedding.eLpNorm_map_measure`.
* The forms with $\hat K$ and $K = F(\hat K)$ are the forms that the finite element interpolation
  estimates use. The transport of continuity up to the boundary is the transport of the hypothesis
  "continuous on $\overline{K}$" of these estimates.
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped ENNReal

noncomputable section

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {G : Type*} [NormedAddCommGroup G]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $T \colon E \to E$ be a continuous linear bijection, let $c \in E$, and let
$\Omega \subseteq E$ be open. This is the open set $F^{-1}(\Omega) = \{x \in E : Tx + c \in
\Omega\}$ of the affine map $F(x) = Tx + c$. -/
abbrev affinePreimage (T : E ≃L[ℝ] E) (c : E) (Ω : Opens E) : Opens E :=
  ⟨(fun x ↦ T x + c) ⁻¹' Ω, Ω.isOpen.preimage (T.continuous.add continuous_const)⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A point $x$ lies in $F^{-1}(\Omega)$ if and only if $Tx + c \in \Omega$. -/
@[simp]
theorem mem_affinePreimage {T : E ≃L[ℝ] E} {c : E} {Ω : Opens E} {x : E} :
    x ∈ affinePreimage T c Ω ↔ T x + c ∈ Ω :=
  Iff.rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $T \colon E \to E$ be a continuous linear bijection, let $c \in E$, and let
$\Omega \subseteq E$ be open. The inverse of $F(x) = Tx + c$ is $y \mapsto T^{-1} y - T^{-1} c$,
and the preimage of $F^{-1}(\Omega)$ under this inverse is $\Omega$. -/
theorem affinePreimage_symm (T : E ≃L[ℝ] E) (c : E) (Ω : Opens E) :
    affinePreimage T.symm (-T.symm c) (affinePreimage T c Ω) = Ω := by
  ext y
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $T \colon E \to E$ be a continuous linear bijection, let $c \in E$, and let
$\hat\Omega, \Omega \subseteq E$ be open. If $F(\hat\Omega) = \Omega$ for $F(x) = Tx + c$, then
$F^{-1}(\Omega) = \hat\Omega$. -/
theorem affinePreimage_eq_of_image_eq (T : E ≃L[ℝ] E) (c : E) {Ωhat Ω : Opens E}
    (h : (fun x ↦ T x + c) '' Ωhat = Ω) : affinePreimage T c Ω = Ωhat := by
  ext x
  change T x + c ∈ (Ω : Set E) ↔ x ∈ (Ωhat : Set E)
  rw [← h]
  exact ⟨fun ⟨y, hy, hxy⟩ ↦ by rwa [← T.injective (add_right_cancel hxy)],
    fun hx ↦ ⟨x, hx, rfl⟩⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $T \colon E \to E$ be a continuous linear bijection, let $c \in E$, and let
$\Omega \subseteq E$ be open. Then
$$\overline{F^{-1}(\Omega)} = F^{-1}(\overline{\Omega})$$
for $F(x) = Tx + c$, because $F$ is a homeomorphism. -/
theorem closure_affinePreimage (T : E ≃L[ℝ] E) (c : E) (Ω : Opens E) :
    closure (affinePreimage T c Ω : Set E) = (fun x ↦ T x + c) ⁻¹' closure (Ω : Set E) :=
  ((T.affineHomeomorph c).preimage_closure Ω).symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $T \colon E \to E$ be a continuous linear bijection, let $c \in E$, and let
$\Omega \subseteq E$ be open. If $v \colon E \to G$ is continuous on $\overline{\Omega}$, then
$x \mapsto v(Tx + c)$ is continuous on $\overline{F^{-1}(\Omega)}$. -/
theorem ContinuousOn.comp_affine_closure {v : E → G} {Ω : Opens E}
    (hv : ContinuousOn v (closure (Ω : Set E))) (T : E ≃L[ℝ] E) (c : E) :
    ContinuousOn (fun x ↦ v (T x + c)) (closure (affinePreimage T c Ω : Set E)) := by
  rw [closure_affinePreimage]
  exact hv.comp (T.continuous.add continuous_const).continuousOn (mapsTo_preimage _ _)

/-- The **affine change of variables in an $L^p$ norm**. Let $T \colon E \to E$ be a continuous
linear bijection, let $c \in E$, let $F(x) = Tx + c$, and let $A \subseteq E$ be measurable.
Then for every function $f \colon E \to G$ and every exponent $p \in [0, \infty]$,
$$\|f \circ F\|_{L^p(F^{-1}A)} = |\det T|^{-1/p} \, \|f\|_{L^p(A)},$$
where the norms are taken for the restrictions of $\mu$ to $F^{-1}A$ and to $A$.

The exponent $1/p$ is `(1 / p).toReal`, which is $0$ for $p = \infty$, so the factor is $1$
there. The function $f$ need not be measurable. The proof uses the pushforward formula
`map_affine_addHaar` and `MeasurableEmbedding.eLpNorm_map_measure`. -/
theorem eLpNorm_comp_affine (T : E ≃L[ℝ] E) (c : E) {A : Set E} (hA : MeasurableSet A)
    (f : E → G) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ f (T x + c)) p (μ.restrict ((fun x ↦ T x + c) ⁻¹' A))
      = ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal
        * eLpNorm f p (μ.restrict A) := by
  have hmeas : Measurable fun x ↦ T x + c := (measurableEmbedding_affine T c).measurable
  have h1 : (μ.restrict ((fun x ↦ T x + c) ⁻¹' A)).map (fun x ↦ T x + c)
      = ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| • μ.restrict A := by
    rw [← Measure.restrict_map hmeas hA, map_affine_addHaar, Measure.restrict_smul]
  rw [← smul_eq_mul, ← eLpNorm_smul_measure_of_ne_zero
    (by simp [(LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero]), ← h1,
    (measurableEmbedding_affine T c).eLpNorm_map_measure]
  rfl

/-- Let $T \colon E \to E$ be a continuous linear bijection, let $c \in E$, and let $A \subseteq E$
be measurable. If $f \in L^p(A)$, then $x \mapsto f(Tx + c)$ lies in $L^p(F^{-1}A)$ for
$F(x) = Tx + c$. -/
theorem memLp_comp_affine (T : E ≃L[ℝ] E) (c : E) {A : Set E} (hA : MeasurableSet A)
    {f : E → G} {p : ℝ≥0∞} (hf : MemLp f p (μ.restrict A)) :
    MemLp (fun x ↦ f (T x + c)) p (μ.restrict ((fun x ↦ T x + c) ⁻¹' A)) := by
  rw [memLp_iff, eLpNorm_comp_affine T c hA]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
    hf

/-- **Membership of $W^{m,p}$ transports along an affine map.** Let $T \colon E \to E$ be a
continuous linear bijection, let $c \in E$, let $F(x) = Tx + c$, and let $\Omega \subseteq E$ be
open. If $v \in W^{m,p}(\Omega)$ for an order $m \in \mathbb{N} \cup \{\infty\}$ and an exponent
$p \in [0, \infty]$, then $v \circ F \in W^{m,p}(F^{-1}\Omega)$.

The weak derivative of order $n$ of $v \circ F$ is $x \mapsto \partial^n v(F x) \circ (T, \dots,
T)$, by `HasWeakIteratedFDerivOn.comp_affineEquiv`. This is the affine case, at all orders, of
`MemSobolev.comp_diffeoOn`. -/
theorem memSobolev_comp_affine [NormedSpace ℝ G] (T : E ≃L[ℝ] E) (c : E) {Ω : Opens E}
    {v : E → G} {m : ℕ∞} {p : ℝ≥0∞} (h : MemSobolev v m p Ω μ) :
    MemSobolev (fun x ↦ v (T x + c)) m p (affinePreimage T c Ω) μ := by
  refine ⟨memLp_comp_affine T c Ω.isOpen.measurableSet h.1, fun n hn ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.2 n hn
  refine ⟨_, hw.comp_affineEquiv T c, ?_⟩
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    fun _ : Fin n ↦ (T : E →L[ℝ] E)).comp_memLp' (memLp_comp_affine T c Ω.isOpen.measurableSet hwp)

/-- **Membership of $W^{m,p}$ is invariant under an affine map.** Let $T \colon E \to E$ be a
continuous linear bijection, let $c \in E$, let $F(x) = Tx + c$, and let $\Omega \subseteq E$ be
open. For every order $m \in \mathbb{N} \cup \{\infty\}$ and every exponent $p \in [0, \infty]$,
$v \in W^{m,p}(\Omega)$ if and only if $v \circ F \in W^{m,p}(F^{-1}\Omega)$. -/
theorem memSobolev_comp_affine_iff [NormedSpace ℝ G] (T : E ≃L[ℝ] E) (c : E) {Ω : Opens E}
    {v : E → G} {m : ℕ∞} {p : ℝ≥0∞} :
    MemSobolev v m p Ω μ ↔ MemSobolev (fun x ↦ v (T x + c)) m p (affinePreimage T c Ω) μ := by
  refine ⟨memSobolev_comp_affine T c, fun h ↦ ?_⟩
  have := memSobolev_comp_affine T.symm (-T.symm c) h
  rw [affinePreimage_symm] at this
  simpa using this

/-- **The seminorm bound of the affine change of variables.** Let $G$ be a real Banach space, let
$T \colon E \to E$ be a continuous linear bijection, let $c \in E$, let $F(x) = Tx + c$, and let
$\Omega \subseteq E$ be open. If $v \in W^{m,p}(\Omega)$ for $m \in \mathbb{N}$ and an exponent
$p \in [0, \infty]$, then
$$|v \circ F|_{m,p,F^{-1}\Omega} \le \|T\|^m \, |\det T|^{-1/p} \, |v|_{m,p,\Omega}.$$
This is the estimate (10.3.5) of Theorem 10.3.4 of [han2009theoretical].

The seminorm is `sobolevSeminorm`, and the inequality holds in $[0, \infty]$. The exponent $1/p$
is `(1 / p).toReal`, which is $0$ for $p = \infty$. The proof bounds $\partial^m (v \circ
F)(x) = \partial^m v(F x) \circ (T, \dots, T)$ in norm by $\|T\|^m \|\partial^m v(F x)\|$
(`ContinuousMultilinearMap.norm_compContinuousLinearMap_le`) and then applies
`eLpNorm_comp_affine`. -/
theorem sobolevSeminorm_comp_affine_le [NormedSpace ℝ G] [CompleteSpace G] (T : E ≃L[ℝ] E) (c : E)
    {Ω : Opens E} {v : E → G} {m : ℕ} {p : ℝ≥0∞} (h : MemSobolev v m p Ω μ) :
    sobolevSeminorm (fun x ↦ v (T x + c)) m p (affinePreimage T c Ω) μ
      ≤ ENNReal.ofReal (‖(T : E →L[ℝ] E)‖ ^ m)
        * (ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal
          * sobolevSeminorm v m p Ω μ) := by
  obtain ⟨w, hw, hwp⟩ := h.2 m le_rfl
  have hw' := hw.comp_affineEquiv T c
  -- the chosen weak derivatives are `w` and its transport, almost everywhere
  have e1 : sobolevSeminorm v m p Ω μ = eLpNorm w p (μ.restrict Ω) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_)
    exact hw.weakIteratedFDeriv_ae_eq
  have e2 : sobolevSeminorm (fun x ↦ v (T x + c)) m p (affinePreimage T c Ω) μ
      = eLpNorm (fun x ↦ (w (T x + c)).compContinuousLinearMap fun _ ↦ (T : E →L[ℝ] E)) p
        (μ.restrict ((fun x ↦ T x + c) ⁻¹' Ω)) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' (affinePreimage T c Ω).isOpen.measurableSet).2 ?_)
    exact hw'.weakIteratedFDeriv_ae_eq
  rw [e1, e2, ← eLpNorm_comp_affine T c Ω.isOpen.measurableSet,
    ← Real.enorm_eq_ofReal (by positivity), ← eLpNorm_const_smul]
  refine eLpNorm_mono_ae ?_ (Eventually.of_forall fun x ↦ ?_)
  · exact ((ContinuousMultilinearMap.compContinuousLinearMapL fun _ : Fin m ↦
      (T : E →L[ℝ] E)).comp_memLp' (memLp_comp_affine T c Ω.isOpen.measurableSet hwp))
      |>.aestronglyMeasurable
  · simp only [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) m)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For a continuous linear bijection $T$ of $E$, $\det T^{-1} = (\det T)^{-1}$. -/
theorem ContinuousLinearEquiv.det_symm_eq_inv (T : E ≃L[ℝ] E) :
    LinearMap.det (T.symm : E →ₗ[ℝ] E) = (LinearMap.det (T : E →ₗ[ℝ] E))⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← LinearMap.det_comp]
  have : (T.symm : E →ₗ[ℝ] E).comp (T : E →ₗ[ℝ] E) = LinearMap.id :=
    LinearMap.ext fun x ↦ T.symm_apply_apply x
  rw [this, LinearMap.det_id]

/-! ### The change of variables between a reference set and its affine image -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $T \colon E \to E$ be a continuous linear bijection and let $c \in E$. The image of a
bounded set under $x \mapsto Tx + c$ is bounded. -/
theorem isBounded_image_affine (T : E ≃L[ℝ] E) (c : E) {s : Set E}
    (hs : Bornology.IsBounded s) : Bornology.IsBounded ((fun x ↦ T x + c) '' s) :=
  ((isometry_add_right c).lipschitzWith.comp (T : E →L[ℝ] E).lipschitzWith).isBounded_image hs

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For a continuous linear bijection $T$ of $E$,
$$|\det T|^{1/2} \cdot |\det T|^{-1/2} = 1.$$
-/
theorem abs_det_rpow_half_mul_rpow_neg_half (T : E ≃L[ℝ] E) :
    |LinearMap.det (T : E →ₗ[ℝ] E)| ^ (1 / 2 : ℝ)
      * |LinearMap.det (T : E →ₗ[ℝ] E)| ^ (-(1 / 2 : ℝ)) = 1 := by
  have hdet : 0 < |LinearMap.det (T : E →ₗ[ℝ] E)| :=
    abs_pos.2 (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero
  rw [Real.rpow_neg hdet.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hdet _).ne']

/-- Let $a \ge 0$, $m \in \mathbb{N}$ and $x \in \mathbb{R}$. In $[0, \infty]$, the product of $a^m$
and $|x|^{1/2}$ is the real number $a^m |x|^{1/2}$. This is the form in which the constants of
the affine change of variables at $p = 2$ appear.

The exponent $1/2$ on the left side is `(1 / (2 : ℝ≥0∞)).toReal`, as in `eLpNorm_comp_affine`. -/
theorem ofReal_pow_mul_ofReal_abs_rpow {a : ℝ} (ha : 0 ≤ a) (m : ℕ) (x : ℝ) :
    ENNReal.ofReal (a ^ m) * ENNReal.ofReal |x| ^ (1 / (2 : ℝ≥0∞)).toReal
      = ENNReal.ofReal (a ^ m * |x| ^ (1 / 2 : ℝ)) := by
  have h2 : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by norm_num
  rw [h2, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
    ← ENNReal.ofReal_mul (pow_nonneg ha m)]

/-- **Functions transported from a reference set to its affine image.** Let $T \colon E \to E$ be a
continuous linear bijection, let $c \in E$, let $F(x) = Tx + c$, and let $\hat K, K \subseteq E$
be open with $F(\hat K) = K$. If $\varphi \in W^{m,p}(\hat K)$ for an order
$m \in \mathbb{N} \cup \{\infty\}$ and an exponent $p \in [0, \infty]$, then
$\varphi \circ F^{-1} \in W^{m,p}(K)$, where $F^{-1}(y) = T^{-1}(y - c)$.

This is `memSobolev_comp_affine` for the inverse map. -/
theorem memSobolev_comp_affine_inv [NormedSpace ℝ G] (T : E ≃L[ℝ] E) (c : E) {Khat K : Opens E}
    (hK : (fun x ↦ T x + c) '' Khat = K) {φ : E → G} {m : ℕ∞} {p : ℝ≥0∞}
    (hφ : MemSobolev φ m p Khat μ) :
    MemSobolev (φ ∘ fun y ↦ T.symm (y - c)) m p K μ := by
  have hKhat : Khat = affinePreimage T c K := (affinePreimage_eq_of_image_eq T c hK).symm
  have h := memSobolev_comp_affine T.symm (-T.symm c) hφ
  rw [hKhat, affinePreimage_symm] at h
  refine h.congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp [sub_eq_add_neg]

/-- **The seminorm of the pullback to the reference set.** Let $G$ be a real Banach space, let
$T \colon E \to E$ be a continuous linear bijection, let $c \in E$, let $F(x) = Tx + c$, and let
$\hat K, K \subseteq E$ be open with $F(\hat K) = K$. If $v \in H^m(K)$ for $m \in \mathbb{N}$,
then
$$|v \circ F|_{m,\hat K} \le \|T\|^m \, |\det T|^{-1/2} \, |v|_{m,K}.$$
This is the estimate (10.3.5) of [han2009theoretical] at $p = 2$.

Here $H^m$ is $W^{m,2}$ and $|\cdot|_{m,K}$ is `sobolevSeminorm` with $p = 2$. The proof is
`sobolevSeminorm_comp_affine_le` with $\hat K$ written as $F^{-1}(K)$. -/
theorem sobolevSeminorm_comp_affine_le_of_image [NormedSpace ℝ G] [CompleteSpace G]
    (T : E ≃L[ℝ] E) (c : E) {Khat K : Opens E} (hK : (fun x ↦ T x + c) '' Khat = K) {m : ℕ}
    {v : E → G} (hv : MemSobolev v m 2 K μ) :
    sobolevSeminorm (fun x ↦ v (T x + c)) m 2 Khat μ
      ≤ ENNReal.ofReal (‖(T : E →L[ℝ] E)‖ ^ m * |LinearMap.det (T : E →ₗ[ℝ] E)| ^ (-(1 / 2 : ℝ)))
        * sobolevSeminorm v m 2 K μ := by
  have hKhat : Khat = affinePreimage T c K := (affinePreimage_eq_of_image_eq T c hK).symm
  subst hKhat
  refine (sobolevSeminorm_comp_affine_le T c hv).trans (le_of_eq ?_)
  rw [← mul_assoc, ofReal_pow_mul_ofReal_abs_rpow (norm_nonneg _), abs_inv,
    Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _)]

/-- **The seminorm on the image, bounded by the seminorm of the pullback.** Let $G$ be a real Banach
space, let $T \colon E \to E$ be a continuous linear bijection, let $c \in E$, let
$F(x) = Tx + c$, and let $\hat K, K \subseteq E$ be open with $F(\hat K) = K$. If $v \in H^m(K)$
for $m \in \mathbb{N}$, then
$$|v|_{m,K} \le \|T^{-1}\|^m \, |\det T|^{1/2} \, |v \circ F|_{m,\hat K}.$$
This is the estimate (10.3.6) of [han2009theoretical] at $p = 2$.

Here $H^m$ is $W^{m,2}$ and $|\cdot|_{m,K}$ is `sobolevSeminorm` with $p = 2$. The proof is
`sobolevSeminorm_comp_affine_le_of_image` for $F^{-1}$. -/
theorem sobolevSeminorm_le_comp_affine_of_image [NormedSpace ℝ G] [CompleteSpace G]
    (T : E ≃L[ℝ] E) (c : E) {Khat K : Opens E} (hK : (fun x ↦ T x + c) '' Khat = K) {m : ℕ}
    {v : E → G} (hv : MemSobolev v m 2 K μ) :
    sobolevSeminorm v m 2 K μ
      ≤ ENNReal.ofReal
          (‖(T.symm : E →L[ℝ] E)‖ ^ m * |LinearMap.det (T : E →ₗ[ℝ] E)| ^ (1 / 2 : ℝ))
        * sobolevSeminorm (fun x ↦ v (T x + c)) m 2 Khat μ := by
  have hKhat : Khat = affinePreimage T c K := (affinePreimage_eq_of_image_eq T c hK).symm
  subst hKhat
  have h' : MemSobolev (fun x ↦ v (T x + c)) m 2 (affinePreimage T c K) μ :=
    memSobolev_comp_affine T c hv
  have key := sobolevSeminorm_comp_affine_le T.symm (-T.symm c) h'
  rw [affinePreimage_symm] at key
  have hfun : (fun y ↦ v (T (T.symm y + -T.symm c) + c)) = v := by
    funext y
    simp
  rw [hfun] at key
  refine key.trans (le_of_eq ?_)
  rw [← mul_assoc, ofReal_pow_mul_ofReal_abs_rpow (norm_nonneg _),
    ContinuousLinearEquiv.det_symm_eq_inv, inv_inv]

end Affine

end
