/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.PDE.Elliptic.Spectral
import Numlib.FiniteElement.Interpolation
import Numlib.Variational.Galerkin

/-!
# Finite element error estimates on triangulations

This file proves the a priori error estimate of the Galerkin method on finite element spaces over a
regular family of triangulations of a plane domain $\Omega \subseteq \mathbb{R}^2$, following
Theorem 10.4.1 and Example 10.4.2 of [han2009theoretical] and Property 12.2 of
[quarteroni2000numerical]. The setting is a subspace $V \subseteq H^1(\Omega)$, a bilinear form $a$
on $V$ that is bounded and coercive, the solution $u \in V$ of $a(u, v) = \ell(v)$ for all
$v \in V$, and Galerkin solutions $u_h$ on subspaces $V_h \subseteq V$. The proof combines Céa's
lemma `IsGalerkinSolution.norm_sub_le`, with the global nodal interpolant $v_h = \Pi_h u$ as
competitor, and the global interpolation estimate `Triangulation.sobolevNorm_sub_globalInterp_le` at
$m = 1$. The one-dimensional counterpart is `Numlib.FiniteElement.Interval`.

The finite element space enters only through the hypothesis $\Pi_h u \in V_h$. For
$V = H^1_0(\Omega)$ and $V_h$ the space of continuous piecewise polynomials that vanish on
$\partial\Omega$ (`Triangulation.polySpaceZero`), this hypothesis is
`LagrangeElement.exists_mem_polySpaceZero_globalInterp`. The regularity of the solution is read on a
representative $\tilde u$ that is continuous up to the boundary, as in the interpolation estimates.

## Main results

* `FiniteElement.norm_sub_le_of_isGalerkinSolution`: $\|u - u_h\|_V \le c\, h^k |u|_{k+1,\Omega}$
  for a conforming element that reproduces $\mathbb{P}_k$, on a regular family of triangulations.
* `FiniteElement.tendsto_norm_sub_of_isGalerkinSolution`: $\|u - u_h\|_V \to 0$ along the family,
  when $u$ can be approximated in $V$ by functions of $H^{k+1}(\Omega) \cap C(\bar\Omega)$ whose
  interpolants lie in $V_h$.
* `FiniteElement.norm_sub_le_of_isGalerkinSolution_dirichletForm`: for the Poisson problem
  $-\Delta u = f$, $u = 0$ on $\partial\Omega$, on a polygon with the $\mathbb{P}_k$ Lagrange
  element, $\|u - u_h\|_{H^1_0} \le (M/\alpha_0)\, C h^s \|u\|_{s+1,\Omega}$ for $1 \le s \le k$,
  with $M = 1$ and $\alpha_0 = (1 + (2R)^2)^{-1}$ for $\Omega \subseteq B(0, R)$.

## Implementation notes

* The space $H^1(\Omega)$ is `SobolevEuclidean 2 1 2 Ω`, with the norm built from multi-indices. The
  interpolation estimates use the tensor Sobolev norm `sobolevNorm`, and
  `FiniteElement.exists_norm_le_sobolevNorm` compares the two norms.
* Boundedness and coercivity of the form are `SesqForm.IsBoundedWith` and `SesqForm.IsCoerciveWith`,
  and a Galerkin solution is `IsGalerkinSolution`.
* A family of triangulations is indexed along an arbitrary filter.
-/

open Filter MeasureTheory Set TopologicalSpace EuclideanSpace Topology Metric
open scoped ENNReal

namespace FiniteElement

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-! ### Comparison of the norm of $H^1(\Omega)$ with the tensor Sobolev norm -/

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open. There is a constant $C \ge 0$ such that every
$w \in H^1(\Omega)$ satisfies $$\|w\|_{H^1(\Omega)} \le C\, \|w\|_{1,\Omega},$$ where the left
side is the norm of `SobolevEuclidean N 1 2 Ω` and the right side is the tensor Sobolev norm of
the function of $w$.

The right side is `sobolevNorm (SobolevMultiIndex.fn w) 1 2 Ω volume`, converted to a real
number. The proof is `SobolevMultiIndex.ofReal_norm_le_sobolevNorm` in real form, and its
constant depends only on $N$. -/
theorem exists_norm_le_sobolevNorm {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SobolevEuclidean N 1 2 Ω,
      ‖w‖ ≤ C * (sobolevNorm (SobolevMultiIndex.fn w) 1 2 Ω volume).toReal := by
  obtain ⟨C₂, hC₂fin, hC₂⟩ : ∃ C₂ : ℝ≥0∞, C₂ ≠ ⊤ ∧ ∀ w : SobolevEuclidean N 1 2 Ω,
      ENNReal.ofReal ‖w‖ ≤ C₂ * sobolevNorm (SobolevMultiIndex.fn w) 1 2 Ω volume :=
    ⟨_, ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.sum_ne_top.2 fun _ _ ↦ enorm_ne_top⟩,
      fun w ↦ SobolevMultiIndex.ofReal_norm_le_sobolevNorm (by simp) w⟩
  refine ⟨C₂.toReal, ENNReal.toReal_nonneg, fun w ↦ ?_⟩
  have hfin : sobolevNorm (SobolevMultiIndex.fn w) 1 2 Ω volume ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_
      ((SobolevMultiIndex.memSobolev_fn w).sobolevNorm_le_sum_sobolevSeminorm (by simp))
    exact ENNReal.sum_ne_top.2 fun n _ ↦ ((SobolevMultiIndex.memSobolev_fn w).mono_order
      (by exact_mod_cast Nat.lt_succ_iff.1 n.2)).sobolevSeminorm_ne_top
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hC₂fin hfin) (hC₂ w)
  rwa [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul] at h

/-- Let $C$ be a constant with $\|w\|_{H^1(\Omega)} \le C \|w\|_{1,\Omega}$ for every
$w \in H^1(\Omega)$, and let $V \subseteq H^1(\Omega)$ be a subspace. If $w, w_h \in V$, and the
functions $w'$ and $g$ agree almost everywhere on $\Omega$ with the functions of $w$ and $w_h$,
then $\|w - w_h\| \le C \|w' - g\|_{1,\Omega}$. -/
theorem norm_sub_le_of_fn_ae_eq {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} {C : ℝ}
    (hC : ∀ w : SobolevEuclidean N 1 2 Ω,
      ‖w‖ ≤ C * (sobolevNorm (SobolevMultiIndex.fn w) 1 2 Ω volume).toReal)
    {V : Submodule ℝ (SobolevEuclidean N 1 2 Ω)} (w wh : V) {w' g : EuclideanSpace ℝ (Fin N) → ℝ}
    (hw : SobolevMultiIndex.fn (w : SobolevEuclidean N 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] w')
    (hwh : SobolevMultiIndex.fn (wh : SobolevEuclidean N 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] g) :
    ‖w - wh‖ ≤ C * (sobolevNorm (w' - g) 1 2 Ω volume).toReal := by
  have hfn : SobolevMultiIndex.fn
      ((w : SobolevEuclidean N 1 2 Ω) - (wh : SobolevEuclidean N 1 2 Ω))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] w' - g := by
    refine (SobolevMultiIndex.fn_sub _ _).trans ?_
    filter_upwards [hw, hwh] with x h1 h2
    simp only [Pi.sub_apply, h1, h2]
  have h := hC ((w : SobolevEuclidean N 1 2 Ω) - (wh : SobolevEuclidean N 1 2 Ω))
  rw [sobolevNorm_congr_ae hfn] at h
  exact h

/-- The global interpolation estimate at $m = 1$, in real form. Let $\mathcal{T}$ be a triangulation
of $\Omega$ with mesh parameter $h$, let $\Pi_h$ be the global interpolant of a reference
element, let $c \ge 0$ and let $v \in H^{k+1}(\Omega)$. If $\|v - \Pi_h v\|_{1,\Omega} \le c\,
h^{(k+1)-1} |v|_{k+1,\Omega}$ holds in $[0, \infty]$, then the real values satisfy $\|v - \Pi_h
v\|_{1,\Omega} \le c\, h^k |v|_{k+1,\Omega}$. -/
theorem toReal_sobolevNorm_sub_globalInterp_le {k : ℕ} {I : ℕ} {xhat : Fin I → 𝔼₂}
    {φhat : Fin I → 𝔼₂ → ℝ} {Ω : Opens 𝔼₂} {𝒯 : Triangulation Ω} {c : ℝ} (hc : 0 ≤ c)
    {v : 𝔼₂ → ℝ} (hv : MemSobolev v (k + 1) 2 Ω volume)
    (h : sobolevNorm (v - 𝒯.globalInterp xhat φhat v) 1 2 Ω volume
      ≤ ENNReal.ofReal (c * 𝒯.meshSize ^ (k + 1 - 1)) * sobolevSeminorm v (k + 1) 2 Ω volume) :
    (sobolevNorm (v - 𝒯.globalInterp xhat φhat v) 1 2 Ω volume).toReal
      ≤ c * 𝒯.meshSize ^ k * (sobolevSeminorm v (k + 1) 2 Ω volume).toReal := by
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    hv.sobolevSeminorm_ne_top) h
  rwa [ENNReal.toReal_mul, Nat.add_sub_cancel,
    ENNReal.toReal_ofReal (mul_nonneg hc (pow_nonneg 𝒯.meshSize_nonneg k))] at h'

/-! ### The error estimate and the convergence -/

/-- **Finite element error estimate.** Let $\Omega \subseteq \mathbb{R}^2$ be open, and let
$\{\mathcal{T}_h\}$ be a regular family of triangulations of $\Omega$, indexed along a filter,
whose mesh parameters $h$ are at most $H$. Let the reference element on the reference triangle
$\hat K$ have nodes $\hat x_i \in \overline{\hat K}$ and $C^1$ shape functions $\hat\varphi_i$.
Let it reproduce $\mathbb{P}_k(\hat K)$ for some $k \ge 1$, that is, the nodal interpolant of
every polynomial of total degree at most $k$ equals the polynomial on $\hat K$, and let it be
conforming on every $\mathcal{T}_h$. Let $V \subseteq H^1(\Omega)$ be a subspace, and let $a$ be
a bilinear form on $V$ that is bounded with constant $M$ and coercive with constant $c_0 > 0$.
Then there is a constant $c \ge 0$ with the following property. Let $\ell$ be a continuous
linear functional on $V$, let $u \in V$ satisfy $a(u, v) = \ell(v)$ for all $v \in V$, and for
every $h$ let $u_h$ be a Galerkin solution on a subspace $V_h \subseteq V$. Let $\tilde u$ agree
almost everywhere on $\Omega$ with the function of $u$, with $\tilde u \in H^{k+1}(\Omega)$ and
$\tilde u$ continuous on $\bar\Omega$, and assume that for every $h$ the interpolant
$\Pi_h \tilde u$ is the function of an element of $V_h$. Then for every $h$ $$\|u - u_h\|_V \le
c\, h^k |\tilde u|_{k+1,\Omega}.$$ This is Theorem 10.4.1, estimate (10.4.4), of
[han2009theoretical].

The constant $c$ does not depend on $\ell$, $u$, $\tilde u$ or $h$. Here $h$ is
`Triangulation.meshSize`, the interpolant is `Triangulation.globalInterp`, regularity is
`FiniteElement.IsRegularFamily` for the sets of open elements, conformity is
`Triangulation.IsConformingElement`, and the seminorm is `sobolevSeminorm`. The proof is Céa's
lemma `IsGalerkinSolution.norm_sub_le` with $v_h = \Pi_h u$, followed by the interpolation
estimate `Triangulation.sobolevNorm_sub_globalInterp_le` at $m = 1$, with the norm of $V$
compared to the tensor norm by `FiniteElement.exists_norm_le_sobolevNorm`. -/
theorem norm_sub_le_of_isGalerkinSolution {k : ℕ} (hk : 1 ≤ k) {I : ℕ} (xhat : Fin I → 𝔼₂)
    (φhat : Fin I → 𝔼₂ → ℝ) (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂))
    (hφ : ∀ i, ContDiff ℝ 1 (φhat i))
    (hP : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ referenceTriangle, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H)
    (hconf : ∀ i, (𝒯 i).IsConformingElement xhat φhat)
    {V : Submodule ℝ (SobolevEuclidean 2 1 2 Ω)} {a : SesqForm ℝ V} {M c₀ : ℝ}
    (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsCoerciveWith c₀) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (ℓ : V →L[ℝ] ℝ) (u : V), (∀ v, a u v = ℓ v) →
      ∀ (Vh : ι → Submodule ℝ V) (uh : ι → V), (∀ i, IsGalerkinSolution a ℓ (Vh i) (uh i)) →
      ∀ ũ : 𝔼₂ → ℝ,
        SobolevMultiIndex.fn (u : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ũ →
        MemSobolev ũ (k + 1) 2 Ω volume → ContinuousOn ũ (closure (Ω : Set 𝔼₂)) →
        (∀ i, ∃ w ∈ Vh i, SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω)
          =ᵐ[volume.restrict (Ω : Set 𝔼₂)] (𝒯 i).globalInterp xhat φhat ũ) →
        ∀ i, ‖u - uh i‖
          ≤ c * (𝒯 i).meshSize ^ k * (sobolevSeminorm ũ (k + 1) 2 Ω volume).toReal := by
  have h10 := Triangulation.sobolevNorm_sub_globalInterp_le (m := 1) le_rfl hk xhat φhat hx hφ hP
    hreg hH hconf
  obtain ⟨c₁, hc₁, hest⟩ := h10
  have hCC := exists_norm_le_sobolevNorm Ω
  obtain ⟨C, hC0, hC⟩ := hCC
  refine ⟨max (M / c₀) 0 * (C * c₁), by positivity,
    fun ℓ u hu Vh uh huh ũ hũ hũk hũc hint i ↦ ?_⟩
  obtain ⟨w, hw, hfw⟩ := hint i
  have hcea := IsGalerkinSolution.norm_sub_le hc₀ hM ha (huh i) hu hw
  have h1 := norm_sub_le_of_fn_ae_eq hC u w hũ hfw
  have h2 := toReal_sobolevNorm_sub_globalInterp_le hc₁ hũk (hest i ũ hũk hũc)
  calc ‖u - uh i‖ ≤ M / c₀ * ‖u - w‖ := hcea
    _ ≤ max (M / c₀) 0 * ‖u - w‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max (M / c₀) 0
          * (C * (c₁ * (𝒯 i).meshSize ^ k * (sobolevSeminorm ũ (k + 1) 2 Ω volume).toReal)) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hC0)
    _ = _ := by ring

/-- **Convergence of the finite element method.** Assume the hypotheses of
`FiniteElement.norm_sub_le_of_isGalerkinSolution` on $\Omega$, the family $\{\mathcal{T}_h\}$,
the reference element, $V$ and $a$. Let $u \in V$ satisfy $a(u, v) = \ell(v)$ for all $v \in V$,
and let $u_h$ be Galerkin solutions on subspaces $V_h \subseteq V$. Assume that for every
$\varepsilon > 0$ there are $w \in V$ with $\|u - w\| < \varepsilon$ and a function $w'$ that
agrees almost everywhere on $\Omega$ with the function of $w$, with $w' \in H^{k+1}(\Omega)$,
$w'$ continuous on $\bar\Omega$, and $\Pi_h w'$ the function of an element of $V_h$ for every
$h$. Then $\|u - u_h\|_V \to 0$ along the family. This is the convergence statement of Theorem
10.4.1 of [han2009theoretical].

The family is indexed along an arbitrary filter, so the proof repeats the $\varepsilon$-argument
of `IsGalerkinSolution.tendsto` instead of applying it. -/
theorem tendsto_norm_sub_of_isGalerkinSolution {k : ℕ} (hk : 1 ≤ k) {I : ℕ} (xhat : Fin I → 𝔼₂)
    (φhat : Fin I → 𝔼₂ → ℝ) (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂))
    (hφ : ∀ i, ContDiff ℝ 1 (φhat i))
    (hP : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ referenceTriangle, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H)
    (hconf : ∀ i, (𝒯 i).IsConformingElement xhat φhat)
    {V : Submodule ℝ (SobolevEuclidean 2 1 2 Ω)} {a : SesqForm ℝ V} {M c₀ : ℝ}
    (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsCoerciveWith c₀) {ℓ : V →L[ℝ] ℝ}
    {u : V} (hu : ∀ v, a u v = ℓ v) {Vh : ι → Submodule ℝ V} {uh : ι → V}
    (huh : ∀ i, IsGalerkinSolution a ℓ (Vh i) (uh i))
    (hdense : ∀ ε > 0, ∃ (w : V) (w' : 𝔼₂ → ℝ), ‖u - w‖ < ε ∧
      SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] w' ∧
      MemSobolev w' (k + 1) 2 Ω volume ∧ ContinuousOn w' (closure (Ω : Set 𝔼₂)) ∧
      ∀ i, ∃ wh ∈ Vh i, SobolevMultiIndex.fn (wh : SobolevEuclidean 2 1 2 Ω)
        =ᵐ[volume.restrict (Ω : Set 𝔼₂)] (𝒯 i).globalInterp xhat φhat w') :
    Tendsto (fun i ↦ ‖u - uh i‖) l (𝓝 0) := by
  have h10 := Triangulation.sobolevNorm_sub_globalInterp_le (m := 1) le_rfl hk xhat φhat hx hφ hP
    hreg hH hconf
  obtain ⟨c₁, hc₁, hest⟩ := h10
  have hCC := exists_norm_le_sobolevNorm Ω
  obtain ⟨C, hC0, hC⟩ := hCC
  have hmesh : Tendsto (fun i ↦ (𝒯 i).meshSize) l (𝓝 0) :=
    ((isRegularFamily_range_K_iff l 𝒯).1 hreg).2
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M', hM'0, hMM'⟩ : ∃ M' : ℝ, 0 ≤ M' ∧ M / c₀ ≤ M' := ⟨max (M / c₀) 0, le_max_right _ _,
    le_max_left _ _⟩
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ M' * (2 * δ) < ε := by
    refine ⟨ε / (2 * (M' + 1)), by positivity, ?_⟩
    rw [mul_div_assoc', mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨w, w', hw, hfw, hw'k, hw'c, hwh⟩ := hdense δ hδ
  -- the interpolation error of `w'` tends to zero with the mesh parameter
  have hev : ∀ᶠ i in l,
      C * (c₁ * (𝒯 i).meshSize ^ k * (sobolevSeminorm w' (k + 1) 2 Ω volume).toReal) < δ := by
    have ht : Tendsto (fun i ↦ C * (c₁ * (𝒯 i).meshSize ^ k
        * (sobolevSeminorm w' (k + 1) 2 Ω volume).toReal)) l
        (𝓝 (C * (c₁ * (0 : ℝ) ^ k * (sobolevSeminorm w' (k + 1) 2 Ω volume).toReal))) :=
      (((hmesh.pow k).const_mul c₁).mul_const _).const_mul C
    rw [zero_pow (by omega), mul_zero, zero_mul, mul_zero] at ht
    exact ht.eventually_lt_const hδ
  filter_upwards [hev] with i hi
  obtain ⟨wh, hwh', hfwh⟩ := hwh i
  have hcea := IsGalerkinSolution.norm_sub_le hc₀ hM ha (huh i) hu hwh'
  have h1 := norm_sub_le_of_fn_ae_eq hC w wh hfw hfwh
  have h2 := toReal_sobolevNorm_sub_globalInterp_le hc₁ hw'k (hest i w' hw'k hw'c)
  have hwwh : ‖w - wh‖ < δ :=
    (h1.trans (mul_le_mul_of_nonneg_left h2 hC0)).trans_lt hi
  rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
  calc ‖u - uh i‖ ≤ M / c₀ * ‖u - wh‖ := hcea
    _ ≤ M' * ‖u - wh‖ := mul_le_mul_of_nonneg_right hMM' (norm_nonneg _)
    _ ≤ M' * (‖u - w‖ + ‖w - wh‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub u w wh
    _ ≤ M' * (δ + δ) := by gcongr
    _ = M' * (2 * δ) := by ring
    _ < ε := hδε

/-! ### The Poisson problem with the $\mathbb{P}_k$ Lagrange element -/

/-- The Dirichlet form $a_0(u, v) = \int_\Omega \nabla u \cdot \nabla v$, restricted to
$H^1_0(\Omega)$, is bounded with constant $M = 1$: $|a_0(u, v)| \le \|u\| \|v\|$. -/
theorem dirichletForm_restrict_isBoundedWith (Ω : Opens 𝔼₂) :
    ((Elliptic.dirichletForm Ω).restrict (SobolevEuclideanZero 2 1 2 Ω)).IsBoundedWith 1 :=
  fun u v ↦ Elliptic.dirichletForm_isBoundedWith Ω u v

/-- **Finite element error for the Poisson problem.** Let $\Omega \subseteq \mathbb{R}^2$ be open
with $\Omega \subseteq B(0, R)$ for some $R \ge 0$. Let $\{\mathcal{T}_h\}$ be a regular family
of triangulations of $\Omega$, indexed along a filter, with mesh parameters at most $H$, such
that $\partial\Omega$ is a union of element edges of every $\mathcal{T}_h$. Let $1 \le s \le k$.
Then there is a constant $C \ge 0$ with the following property. Let $f \in L^2(\Omega)$, and let
$u \in H^1_0(\Omega)$ satisfy $$\int_\Omega \nabla u \cdot \nabla v = \int_\Omega f v \quad
\text{for all } v \in H^1_0(\Omega).$$ For every $h$ let $u_h$ be the Galerkin solution on the
space $V_h$ of continuous piecewise polynomials of degree at most $k$ that vanish on
$\partial\Omega$. Let $\tilde u$ agree almost everywhere on $\Omega$ with the function of $u$,
with $\tilde u \in H^{s+1}(\Omega)$, $\tilde u$ continuous on $\bar\Omega$ and $\tilde u = 0$ on
$\partial\Omega$. Then for every $h$ $$\|u - u_h\|_{H^1_0(\Omega)} \le \frac{M}{\alpha_0}\, C\,
h^s \|\tilde u\|_{s+1,\Omega},$$ where $M = 1$ is the continuity constant of the form and
$\alpha_0 = (1 + (2R)^2)^{-1}$ is its coercivity constant on $H^1_0(\Omega)$ from the Poincaré
inequality. The constant $C$ does not depend on $h$, $f$ or $u$. This is Example 10.4.2 of
[han2009theoretical] and Property 12.2, estimate (12.96), of [quarteroni2000numerical].

The form is `Elliptic.dirichletForm` restricted to `SobolevEuclideanZero 2 1 2 Ω`, the
right-hand side is `Elliptic.load`, $V_h$ is `Triangulation.polySpaceZero 2 k`, and the
condition on $\partial\Omega$ is `Triangulation.FrontierSubsetEdges`. The proof applies
`FiniteElement.norm_sub_le_of_isGalerkinSolution` to the $\mathbb{P}_k$ Lagrange element, whose
interpolant $\Pi_h \tilde u$ lies in $V_h$ by
`LagrangeElement.exists_mem_polySpaceZero_globalInterp`, and bounds the seminorm by the norm. -/
theorem norm_sub_le_of_isGalerkinSolution_dirichletForm {k s : ℕ} (hs : 1 ≤ s) (hsk : s ≤ k)
    {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H) (hedge : ∀ i, (𝒯 i).FrontierSubsetEdges)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : (Ω : Set 𝔼₂) ⊆ ball 0 R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂)))
      (u : SobolevEuclideanZero 2 1 2 Ω),
      (∀ v : SobolevEuclideanZero 2 1 2 Ω, Elliptic.dirichletForm Ω u v = Elliptic.load Ω f v) →
      ∀ uh : ι → SobolevEuclideanZero 2 1 2 Ω,
        (∀ i, IsGalerkinSolution
          ((Elliptic.dirichletForm Ω).restrict (SobolevEuclideanZero 2 1 2 Ω))
          ((Elliptic.load Ω f).comp (SobolevEuclideanZero 2 1 2 Ω).subtypeL)
          ((𝒯 i).polySpaceZero 2 k) (uh i)) →
        ∀ ũ : 𝔼₂ → ℝ,
          SobolevMultiIndex.fn (u : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ũ →
          MemSobolev ũ (s + 1) 2 Ω volume → ContinuousOn ũ (closure (Ω : Set 𝔼₂)) →
          EqOn ũ 0 (frontier (Ω : Set 𝔼₂)) →
          ∀ i, ‖u - uh i‖ ≤ (1 / (1 + (2 * R) ^ 2)⁻¹) * C * (𝒯 i).meshSize ^ s
            * (sobolevNorm ũ (s + 1) 2 Ω volume).toReal := by
  have hk0 : 0 < k := by omega
  have hpos : (0 : ℝ) < (1 + (2 * R) ^ 2)⁻¹ := by positivity
  have h10 := norm_sub_le_of_isGalerkinSolution (k := s) hs
    (LagrangeElement.node k) (LagrangeElement.shape k)
    (LagrangeElement.node_mem_closure hk0)
    (fun i ↦ (LagrangeElement.contDiff_shape k i).of_le (by simp))
    (fun q hq x _ ↦ LagrangeElement.nodalInterp_eval hk0 q (hq.trans hsk) x)
    hreg hH (fun i ↦ LagrangeElement.isConformingElement hk0 (𝒯 i))
    (dirichletForm_restrict_isBoundedWith Ω) hpos
    (Elliptic.dirichletForm_restrict_isCoerciveWith (d := 1) Ω hR hΩ)
  obtain ⟨c, hc0, hc⟩ := h10
  refine ⟨c / (1 + (2 * R) ^ 2), by positivity, fun f u hu uh huh ũ hũ hũk hũc hũ0 i ↦ ?_⟩
  have hint : ∀ i, ∃ w ∈ (𝒯 i).polySpaceZero 2 k,
      SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
        (𝒯 i).globalInterp (LagrangeElement.node k) (LagrangeElement.shape k) ũ := fun i ↦
    LagrangeElement.exists_mem_polySpaceZero_globalInterp hk0 (𝒯 i) 2 (by simp) (hedge i) hũ0
  have h := hc ((Elliptic.load Ω f).comp (SobolevEuclideanZero 2 1 2 Ω).subtypeL) u hu
    (fun i ↦ (𝒯 i).polySpaceZero 2 k) uh huh ũ hũ hũk hũc hint i
  refine h.trans ?_
  -- the seminorm is bounded by the norm, and `(M/α₀) C = c`
  have hfin : sobolevNorm ũ (s + 1) 2 Ω volume ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hũk.sobolevNorm_le_sum_sobolevSeminorm (by simp))
    exact ENNReal.sum_ne_top.2 fun n _ ↦
      (hũk.mono_order (by exact_mod_cast Nat.lt_succ_iff.1 n.2)).sobolevSeminorm_ne_top
  have hle : (sobolevSeminorm ũ (s + 1) 2 Ω volume).toReal
      ≤ (sobolevNorm ũ (s + 1) 2 Ω volume).toReal :=
    ENNReal.toReal_mono hfin
      (eLpNorm_weakIteratedFDeriv_le_sobolevNorm (by simp) (by simp) le_rfl)
  have hh0 : 0 ≤ (𝒯 i).meshSize := (𝒯 i).meshSize_nonneg
  have hcc : 1 / (1 + (2 * R) ^ 2)⁻¹ * (c / (1 + (2 * R) ^ 2)) = c := by
    field_simp
  rw [hcc]
  gcongr

end FiniteElement
