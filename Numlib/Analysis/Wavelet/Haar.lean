/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Numlib.Analysis.InnerProductSpace.OrthonormalSeries

/-!
# The Haar system on $L^2(\mathbb{R})$

Let $\varphi = \mathbf{1}_{[0,1)}$ be the unit step and $\psi(x) = \varphi(2x) - \varphi(2x - 1)$
the Haar wavelet. For integers $j$ and $k$, the Haar scaling function
$\varphi_{j,k}(x) = 2^{j/2} \varphi(2^j x - k)$ is the normalized indicator of the dyadic interval
$I_{j,k} = [k 2^{-j}, (k + 1) 2^{-j})$, and the Haar wavelet
$\psi_{j,k}(x) = 2^{j/2} \psi(2^j x - k)$ takes the values $\pm 2^{j/2}$ on the two halves of
$I_{j,k}$. The scaling space $V_j$ and the wavelet space $W_j$ are the closed spans in
$L^2(\mathbb{R})$ of the $\varphi_{j,k}$ and of the $\psi_{j,k}$, $k \in \mathbb{Z}$. The
presentation follows [han2009theoretical], §4.4 (Theorems 4.4.1–4.4.4 and Exercise 4.4.4).

The module proves that the spaces $V_j$ are orthonormally generated, scale invariant, nested, dense
in union and trivial in intersection; that $V_{j+1}$ is the orthogonal direct sum of $V_j$ and
$W_j$; the decomposition and reconstruction formulas that relate the coefficients of consecutive
levels; and that the wavelets $\psi_{j,k}$ of all levels form a Hilbert basis of $L^2(\mathbb{R})$.
All scale-invariance statements use the unitary dilation $(D_c f)(x) = |c|^{1/2} f(cx)$, $c \neq 0$,
of $L^2(\mathbb{R})$, which the module defines first. $P_S$ denotes the orthogonal projection onto a
closed subspace $S$.

## Main definitions

* `MeasureTheory.Lp.dilationₗᵢ`: the dilation $D_c$, as a linear isometric equivalence of
  $L^2(\mathbb{R})$.
* `Haar.dyadic`: the dyadic interval $I_{j,k}$.
* `Haar.scalingFun`, `Haar.waveletFun`: the Haar scaling functions $\varphi_{j,k}$ and wavelets
  $\psi_{j,k}$.
* `Haar.V`, `Haar.W`: the scaling spaces $V_j$ and the wavelet spaces $W_j$; `Haar.hilbertBasis_V`
  and `Haar.hilbertBasis_W` are their Hilbert bases.
* `Haar.hilbertBasis`: the wavelets $\psi_{j,k}$ of all levels, as a Hilbert basis of
  $L^2(\mathbb{R})$.

## Main results

* `Haar.orthonormal_scalingFun`: for each $j$, the functions $\varphi_{j,k}$, $k \in \mathbb{Z}$,
  are orthonormal.
* `Haar.V_eq_map_dilation`: $V_j = D_{2^j}(V_0)$.
* `Haar.V_le_V_succ`: $V_j \subseteq V_{j+1}$.
* `Haar.topologicalClosure_iSup_V`: $\bigcup_j V_j$ is dense in $L^2(\mathbb{R})$.
* `Haar.iInf_V_eq_bot`: $\bigcap_j V_j = \{0\}$.
* `Haar.mem_W_iff`: $f \in W_j$ if and only if $f \in V_{j+1}$ and $f$ is orthogonal to every
  $\varphi_{j,k}$.
* `Haar.isCompl_V_W`: $V_j$ and $W_j$ are complementary subspaces of $V_{j+1}$.
* `Haar.decomposition`, `Haar.reconstruction`: the scaling and wavelet coefficients of level $j$ in
  terms of the scaling coefficients of level $j + 1$, and back.
* `Haar.starProjection_V_eq_sum`: for $i \le j$, $P_{V_j} f = P_{V_i} f + \sum_{l=i}^{j-1} P_{W_l}
  f$.
* `Haar.orthonormal_waveletFun_prod`: the wavelets of all levels are orthonormal.

## Proof outline

Density is the only approximation argument: a continuous function with compact support is the $L^2$
limit of its dyadic step functions, which lie in the $V_j$, and such functions are dense in
$L^2(\mathbb{R})$. Separation follows from the bound $|\langle \varphi_{i,k}, f \rangle| \le
2^{(j-i)/2} \|f\|$ for $f \in V_j$ and $j \le i$, which tends to $0$ as $j \to -\infty$.
Completeness of the wavelets follows from the multi-level decomposition: if $f$ is orthogonal to
every wavelet, all its projections $P_{V_j} f$ are equal, so they lie in $\bigcap_j V_j = \{0\}$,
and density gives $f = 0$.

## Implementation notes

* The spaces $V_j$ and $W_j$ are closed subspaces: `Haar.V j` is `(Submodule.span ℝ (Set.range
  (Haar.scalingFun j))).topologicalClosure`, so that "Hilbert basis", the nesting,
  $\bigcap_j V_j = \{0\}$ and the density of $\bigcup_j V_j$ are statements in $L^2(\mathbb{R})$.
  The space $V_j$ of [han2009theoretical], the set of finite linear combinations of the
  $\varphi_{j,k}$, is a dense subspace of `Haar.V j`.
* The union $\bigcup_j V_j$ is the supremum `⨆ j, Haar.V j` of submodules, and the intersection is
  the infimum `⨅ j, Haar.V j`.
* Mathlib has `MeasureTheory.Lp.compMeasurePreserving`, but a scaling $x \mapsto cx$ is not measure
  preserving, only quasi-measure-preserving. The map on almost-everywhere classes that underlies
  `MeasureTheory.Lp.dilationₗᵢ` is therefore built from
  `MeasureTheory.AEEqFun.compQuasiMeasurePreserving`.
* The coefficients are inner products with the normalized functions: the scaling and wavelet
  coefficients of $f$ are $\langle \varphi_{j,k}, f \rangle$ and $\langle \psi_{j,k}, f \rangle$.
* None of this material is in Mathlib.
-/

open scoped ENNReal Pointwise

noncomputable section

namespace MeasureTheory.Lp

variable {c d : ℝ}

/-! ### Auxiliary facts about the scaling $x \mapsto cx$ of $\mathbb{R}$ -/

/-- Multiplication $x \mapsto cx$ by a constant $c \neq 0$ is quasi-measure-preserving for Lebesgue
measure on $\mathbb{R}$. -/
private theorem qmp_const_mul (hc : c ≠ 0) :
    QuasiMeasurePreserving (fun x : ℝ => c * x) volume volume := by
  refine ⟨measurable_const_mul c, ?_⟩
  rw [Real.map_volume_mul_left hc]
  exact Measure.smul_absolutelyContinuous

/-- Let $c \neq 0$. If $g = g'$ almost everywhere on $\mathbb{R}$, then $x \mapsto g(cx)$ and
$x \mapsto g'(cx)$ are equal almost everywhere. -/
theorem ae_comp_const_mul (hc : c ≠ 0) {g g' : ℝ → ℝ} (h : g =ᵐ[volume] g') :
    (fun x => g (c * x)) =ᵐ[volume] fun x => g' (c * x) :=
  h.comp_tendsto (qmp_const_mul hc).tendsto_ae

/-- Let $c \neq 0$ and let $g : \mathbb{R} \to \mathbb{R}$ be almost everywhere strongly measurable.
The $L^2$ seminorm of $x \mapsto g(cx)$ is $|c^{-1}|^{1/2} \|g\|_{L^2}$, as an element of
$[0, \infty]$. -/
theorem _root_.MeasureTheory.eLpNorm_comp_const_mul (hc : c ≠ 0) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g volume) :
    eLpNorm (fun x => g (c * x)) 2 volume
      = ENNReal.ofReal |c⁻¹| ^ (1 / 2 : ℝ) * eLpNorm g 2 volume := by
  have hmap : Measure.map (fun x : ℝ => c * x) volume = ENNReal.ofReal |c⁻¹| • volume :=
    Real.map_volume_mul_left hc
  have hg' : AEStronglyMeasurable g (Measure.map (fun x : ℝ => c * x) volume) := by
    rw [hmap]; exact hg.mono_ac Measure.smul_absolutelyContinuous
  have h1 := eLpNorm_map_measure (p := 2) hg' (measurable_const_mul c).aemeasurable
  rw [hmap, eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞) _ _ hg] at h1
  have h2 : ((1 : ℝ≥0∞) / 2).toReal = (1 / 2 : ℝ) := by simp
  rw [h2, smul_eq_mul, Function.comp_def] at h1
  exact h1.symm

/-- Let $c \neq 0$. If $s \subseteq \mathbb{R}$ has finite Lebesgue measure, then its preimage under
$x \mapsto cx$ has finite Lebesgue measure. -/
theorem volume_preimage_const_mul_ne_top (hc : c ≠ 0) {s : Set ℝ} (hμs : volume s ≠ ∞) :
    volume ((fun x : ℝ => c * x) ⁻¹' s) ≠ ∞ := by
  rw [Real.volume_preimage_mul_left hc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμs

/-- For $c \neq 0$ and $s \subseteq \mathbb{R}$, the preimage of $s$ under $x \mapsto cx$ is the
rescaled set $c^{-1} s$. -/
theorem preimage_const_mul_eq_inv_smul (hc : c ≠ 0) (s : Set ℝ) :
    (fun x : ℝ => c * x) ⁻¹' s = c⁻¹ • s := by
  ext x
  rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hc), inv_inv,
    smul_eq_mul]

/-! ### Precomposition with a scaling -/

private theorem mem_Lp_compQMP (hc : c ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    f.1.compQuasiMeasurePreserving (fun x : ℝ => c * x) (qmp_const_mul hc)
      ∈ Lp ℝ 2 (volume : Measure ℝ) := by
  rw [mem_Lp_iff_eLpNorm_lt_top,
    eLpNorm_congr_ae (AEEqFun.coeFn_compQuasiMeasurePreserving _ _), Function.comp_def,
    eLpNorm_comp_const_mul hc (Lp.aestronglyMeasurable f)]
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) (eLpNorm_lt_top f)

/-- For $c \neq 0$, the precomposition $f \mapsto f(c\,\cdot)$ with the scaling by $c$, as a linear
map of $L^2(\mathbb{R})$. -/
private noncomputable def compConstMul (c : ℝ) (hc : c ≠ 0) :
    Lp ℝ 2 (volume : Measure ℝ) →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) where
  toFun f := ⟨f.1.compQuasiMeasurePreserving _ (qmp_const_mul hc), mem_Lp_compQMP hc f⟩
  map_add' := by rintro ⟨⟨_⟩, _⟩ ⟨⟨_⟩, _⟩; rfl
  map_smul' := by rintro r ⟨⟨_⟩, _⟩; rfl

private theorem coeFn_compConstMul (hc : c ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    compConstMul c hc f =ᵐ[volume] fun x => f (c * x) :=
  AEEqFun.coeFn_compQuasiMeasurePreserving f.1 (qmp_const_mul hc)

private theorem norm_compConstMul (hc : c ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ‖compConstMul c hc f‖ = |c⁻¹| ^ (1 / 2 : ℝ) * ‖f‖ := by
  rw [norm_def, norm_def, eLpNorm_congr_ae (coeFn_compConstMul hc f),
    eLpNorm_comp_const_mul hc (Lp.aestronglyMeasurable f), ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (abs_nonneg _)]

/-! ### The dilation as a linear map -/

/-- For $c \neq 0$, the dilation $f \mapsto |c|^{1/2} f(c\,\cdot)$ of $L^2(\mathbb{R})$, as a linear
map. -/
private noncomputable def dilationₗ (c : ℝ) (hc : c ≠ 0) :
    Lp ℝ 2 (volume : Measure ℝ) →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  (|c| ^ (1 / 2 : ℝ)) • compConstMul c hc

private theorem dilationₗ_apply (c : ℝ) (hc : c ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    dilationₗ c hc f = (|c| ^ (1 / 2 : ℝ)) • compConstMul c hc f := rfl

private theorem coeFn_dilationₗ (c : ℝ) (hc : c ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    dilationₗ c hc f =ᵐ[volume] fun x => |c| ^ (1 / 2 : ℝ) * f (c * x) := by
  rw [dilationₗ_apply]
  filter_upwards [Lp.coeFn_smul (|c| ^ (1 / 2 : ℝ)) (compConstMul c hc f),
    coeFn_compConstMul hc f] with x hx hx'
  rw [hx]
  simp [hx']

private theorem norm_dilationₗ (hc : c ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    ‖dilationₗ c hc f‖ = ‖f‖ := by
  rw [dilationₗ_apply, norm_smul, norm_compConstMul hc, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg c) _), ← mul_assoc,
    ← Real.mul_rpow (abs_nonneg c) (abs_nonneg c⁻¹), ← abs_mul, mul_inv_cancel₀ hc, abs_one,
    Real.one_rpow, one_mul]

private theorem dilationₗ_congr {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a = b) :
    dilationₗ a ha = dilationₗ b hb := by subst h; rfl

private theorem dilationₗ_one (h : (1 : ℝ) ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    dilationₗ 1 h f = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_dilationₗ 1 h f] with x hx
  rw [hx]
  simp

private theorem dilationₗ_comp (hc : c ≠ 0) (hd : d ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    dilationₗ c hc (dilationₗ d hd f) = dilationₗ (d * c) (mul_ne_zero hd hc) f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_dilationₗ c hc (dilationₗ d hd f),
    ae_comp_const_mul hc (coeFn_dilationₗ d hd f),
    coeFn_dilationₗ (d * c) (mul_ne_zero hd hc) f] with x hx hx2 hx3
  rw [hx, hx3, hx2, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [← Real.mul_rpow (abs_nonneg c) (abs_nonneg d), ← abs_mul, mul_comm c d]

/-! ### The unitary dilation of $L^2(\mathbb{R})$ -/

/-- For $c \in \mathbb{R}$ with $c \neq 0$, the **dilation** $D_c$ of $L^2(\mathbb{R})$ is
$$(D_c f)(x) = |c|^{1/2} f(cx).$$
It is a linear isometric equivalence of $L^2(\mathbb{R})$ onto itself, with inverse
$D_{c^{-1}}$. It is the scaling of [han2009theoretical], §4.4.

The factor $|c|^{1/2}$ makes $D_c$ preserve the $L^2$ norm. The inverse is given by
`MeasureTheory.Lp.dilationₗᵢ_symm`, and the composition rule $D_c D_d = D_{dc}$ by
`MeasureTheory.Lp.dilationₗᵢ_trans`. -/
noncomputable def dilationₗᵢ (c : ℝ) (hc : c ≠ 0) :
    Lp ℝ 2 (volume : Measure ℝ) ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ) where
  toFun := dilationₗ c hc
  map_add' := map_add (dilationₗ c hc)
  map_smul' := map_smul (dilationₗ c hc)
  invFun := dilationₗ c⁻¹ (inv_ne_zero hc)
  left_inv f := by
    rw [dilationₗ_comp (inv_ne_zero hc) hc f,
      dilationₗ_congr (mul_ne_zero hc (inv_ne_zero hc)) one_ne_zero (mul_inv_cancel₀ hc)]
    exact dilationₗ_one _ f
  right_inv f := by
    rw [dilationₗ_comp hc (inv_ne_zero hc) f,
      dilationₗ_congr (mul_ne_zero (inv_ne_zero hc) hc) one_ne_zero (inv_mul_cancel₀ hc)]
    exact dilationₗ_one _ f
  norm_map' := norm_dilationₗ hc

/-- For $c \neq 0$ and $f \in L^2(\mathbb{R})$, $(D_c f)(x) = |c|^{1/2} f(cx)$ for almost every
$x \in \mathbb{R}$. -/
theorem dilationₗᵢ_apply (c : ℝ) (hc : c ≠ 0) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    dilationₗᵢ c hc f =ᵐ[volume] fun x => |c| ^ (1 / 2 : ℝ) * f (c * x) :=
  coeFn_dilationₗ c hc f

/-- Two dilations compose into one: $D_c (D_d f) = D_{dc} f$ for $c, d \neq 0$ and
$f \in L^2(\mathbb{R})$. -/
theorem dilationₗᵢ_trans (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (f : Lp ℝ 2 (volume : Measure ℝ)) :
    dilationₗᵢ c hc (dilationₗᵢ d hd f) = dilationₗᵢ (d * c) (mul_ne_zero hd hc) f :=
  dilationₗ_comp hc hd f

/-- For $c \neq 0$, the inverse of the dilation $D_c$ is $D_{c^{-1}}$. -/
theorem dilationₗᵢ_symm (c : ℝ) (hc : c ≠ 0) :
    (dilationₗᵢ c hc).symm = dilationₗᵢ c⁻¹ (inv_ne_zero hc) :=
  LinearIsometryEquiv.ext fun _ => rfl

/-! ### Action on indicator functions -/

/-- Let $c \neq 0$, let $s \subseteq \mathbb{R}$ be measurable with finite measure, and let
$r \in \mathbb{R}$. Then $D_c (r \mathbf{1}_s) = |c|^{1/2} r \mathbf{1}_{c^{-1} s}$, where
$c^{-1} s$ is the preimage of $s$ under $x \mapsto cx$. -/
theorem dilationₗᵢ_indicatorConstLp (c : ℝ) (hc : c ≠ 0) {s : Set ℝ} (hs : MeasurableSet s)
    (hμs : volume s ≠ ∞) (r : ℝ) :
    dilationₗᵢ c hc (indicatorConstLp 2 hs hμs r)
      = indicatorConstLp 2 (measurable_const_mul c hs)
          (volume_preimage_const_mul_ne_top hc hμs) (|c| ^ (1 / 2 : ℝ) * r) := by
  refine Lp.ext ?_
  filter_upwards [dilationₗᵢ_apply c hc (indicatorConstLp 2 hs hμs r),
    ae_comp_const_mul hc (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := r)),
    indicatorConstLp_coeFn (p := 2) (hs := measurable_const_mul c hs)
      (hμs := volume_preimage_const_mul_ne_top hc hμs) (c := |c| ^ (1 / 2 : ℝ) * r)] with
    x hx hx2 hx3
  rw [hx, hx2, hx3]
  by_cases hxs : c * x ∈ s
  · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem (Set.mem_preimage.mpr hxs)]
  · rw [Set.indicator_of_notMem hxs,
      Set.indicator_of_notMem (fun h => hxs (Set.mem_preimage.mp h)), mul_zero]

end MeasureTheory.Lp

/-! ### Two elementary facts about `indicatorConstLp` -/

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} {s t : Set α}

/-- Let $s$ be a measurable set of finite measure and $c, a \in \mathbb{R}$. In $L^p(\mu)$,
$c \cdot (a \mathbf{1}_s) = (ca) \mathbf{1}_s$. -/
theorem smul_indicatorConstLp (c : ℝ) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (a : ℝ) :
    c • indicatorConstLp p hs hμs a = indicatorConstLp p hs hμs (c * a) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul c (indicatorConstLp p hs hμs a),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := a),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c * a)] with x h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2, smul_eq_mul]
  by_cases hx : x ∈ s <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-- If $s = t$, then $c \mathbf{1}_s$ and $c \mathbf{1}_t$ are the same element of $L^p(\mu)$,
whatever the proofs that the sets are measurable with finite measure. -/
theorem indicatorConstLp_congr_set (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (ht : MeasurableSet t)
    (hμt : μ t ≠ ⊤) (h : s = t) (c : ℝ) :
    indicatorConstLp p hs hμs c = indicatorConstLp p ht hμt c := by
  subst h
  rfl

end MeasureTheory

/-! ### The Haar scaling functions -/

namespace Haar

open MeasureTheory Real

/-- The **dyadic interval** of level $j \in \mathbb{Z}$ and index $k \in \mathbb{Z}$ is
$I_{j,k} = [k 2^{-j}, (k + 1) 2^{-j})$. It is the support of the Haar scaling function
$\varphi_{j,k}$. -/
def dyadic (j k : ℤ) : Set ℝ := Set.Ico ((k : ℝ) * 2 ^ (-j)) (((k : ℝ) + 1) * 2 ^ (-j))

/-- The dyadic interval $I_{j,k}$ is measurable. -/
theorem measurableSet_dyadic (j k : ℤ) : MeasurableSet (dyadic j k) := measurableSet_Ico

/-- The dyadic interval $I_{j,k}$ has Lebesgue measure $2^{-j}$. -/
@[simp]
theorem volume_dyadic (j k : ℤ) : volume (dyadic j k) = ENNReal.ofReal ((2 : ℝ) ^ (-j)) := by
  rw [dyadic, Real.volume_Ico]
  congr 1
  ring

/-- The dyadic interval $I_{j,k}$ has finite Lebesgue measure. -/
theorem volume_dyadic_ne_top (j k : ℤ) : volume (dyadic j k) ≠ ⊤ := by
  rw [volume_dyadic]
  exact ENNReal.ofReal_ne_top

/-- Distinct dyadic intervals of the same level are disjoint: $I_{j,k} \cap I_{j,l} = \emptyset$ for
$k \neq l$. -/
theorem dyadic_inter_dyadic (j : ℤ) {k l : ℤ} (h : k ≠ l) : dyadic j k ∩ dyadic j l = ∅ := by
  have ht : (0 : ℝ) < 2 ^ (-j) := by positivity
  rw [dyadic, dyadic, Set.Ico_inter_Ico]
  refine Set.Ico_eq_empty (not_lt.mpr ?_)
  rcases lt_or_gt_of_ne h with hkl | hkl
  · have hkl' : ((k : ℝ) + 1) ≤ (l : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ l)
    exact le_trans (min_le_left _ _) (le_trans (by nlinarith) (le_max_right _ _))
  · have hkl' : ((l : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast (by omega : l + 1 ≤ k)
    exact le_trans (min_le_right _ _) (le_trans (by nlinarith) (le_max_left _ _))

/-- The dyadic interval $I_{0,0}$ is $[0, 1)$. -/
@[simp]
theorem dyadic_zero_zero : dyadic 0 0 = Set.Ico 0 1 := by
  simp [dyadic]

/-- Let $\varphi = \mathbf{1}_{[0,1)}$ be the unit step. The **Haar scaling function** of level
$j \in \mathbb{Z}$ and index $k \in \mathbb{Z}$ is
$$\varphi_{j,k}(x) = 2^{j/2} \varphi(2^j x - k) = 2^{j/2} \mathbf{1}_{I_{j,k}}(x),$$
the normalized indicator of the dyadic interval $I_{j,k} = [k 2^{-j}, (k + 1) 2^{-j})$. This is
the function of (4.4.1) in [han2009theoretical].

The function is the element `MeasureTheory.indicatorConstLp` of $L^2(\mathbb{R})$ for the set
`Haar.dyadic j k` and the constant $\sqrt{2^j} = 2^{j/2}$. -/
def scalingFun (j k : ℤ) : Lp ℝ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (measurableSet_dyadic j k) (volume_dyadic_ne_top j k) (√((2 : ℝ) ^ j))

/-- The scaling function $\varphi_{0,0}$ is the unit step $\varphi = \mathbf{1}_{[0,1)}$. -/
theorem scalingFun_zero_zero :
    scalingFun 0 0 =
      indicatorConstLp 2 (measurableSet_dyadic 0 0) (volume_dyadic_ne_top 0 0) 1 := by
  rw [scalingFun]
  norm_num

/-- Every scaling function is a dilation of a scaling function of level $0$:
$\varphi_{j,k} = D_{2^j} \varphi_{0,k}$. -/
theorem scalingFun_eq_dilation (j k : ℤ) :
    scalingFun j k = Lp.dilationₗᵢ ((2 : ℝ) ^ j) (zpow_ne_zero j two_ne_zero) (scalingFun 0 k) := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have hd0 : dyadic 0 k = Set.Ico (k : ℝ) ((k : ℝ) + 1) := by simp [dyadic]
  have hset : (fun x : ℝ => (2 : ℝ) ^ j * x) ⁻¹' dyadic 0 k = dyadic j k := by
    rw [hd0, Set.preimage_const_mul_Ico₀ _ _ hpos, dyadic]
    congr 1 <;> rw [zpow_neg, div_eq_mul_inv]
  simp only [scalingFun]
  rw [Lp.dilationₗᵢ_indicatorConstLp,
    indicatorConstLp_congr_set _ _ (measurableSet_dyadic j k) (volume_dyadic_ne_top j k) hset]
  congr 1
  rw [abs_of_pos hpos, ← Real.sqrt_eq_rpow]
  simp

/-- For each level $j \in \mathbb{Z}$, the scaling functions $\varphi_{j,k}$, $k \in \mathbb{Z}$,
are orthonormal in $L^2(\mathbb{R})$. This is Theorem 4.4.1(1) of [han2009theoretical].

The functions of one level have norm $1$ and disjoint supports $I_{j,k}$; see
`Haar.inner_scalingFun_self` and `Haar.inner_scalingFun_of_ne`. -/
theorem orthonormal_scalingFun (j : ℤ) : Orthonormal ℝ (scalingFun j) := by
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  rw [orthonormal_iff_ite]
  intro k l
  rw [scalingFun, scalingFun,
    L2.inner_indicatorConstLp_indicatorConstLp (measurableSet_dyadic j k)
      (measurableSet_dyadic j l) (volume_dyadic_ne_top j k) (volume_dyadic_ne_top j l)]
  rcases eq_or_ne k l with rfl | h
  · rw [Set.inter_self, measureReal_def, volume_dyadic,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
    rw [Real.mul_self_sqrt hpos.le, zpow_neg, inv_mul_cancel₀ hpos.ne']
    simp
  · rw [dyadic_inter_dyadic j h]
    simp [h]

/-- Each scaling function has norm one: $\langle \varphi_{j,k}, \varphi_{j,k} \rangle = 1$. -/
theorem inner_scalingFun_self (j k : ℤ) :
    inner ℝ (scalingFun j k) (scalingFun j k) = (1 : ℝ) := by
  have h := orthonormal_scalingFun j
  rw [orthonormal_iff_ite] at h
  simpa using h k k

/-- Scaling functions of the same level with different indices are orthogonal: $\langle
\varphi_{j,k}, \varphi_{j,l} \rangle = 0$ for $k \neq l$. -/
theorem inner_scalingFun_of_ne (j : ℤ) {k l : ℤ} (h : k ≠ l) :
    inner ℝ (scalingFun j k) (scalingFun j l) = (0 : ℝ) := by
  have hon := orthonormal_scalingFun j
  rw [orthonormal_iff_ite] at hon
  simpa [h] using hon k l

/-- The identity $(\sqrt{2})^{-1} (\sqrt{2})^{-1} \cdot 2 = 1$, the normalization of the two-scale
relation. -/
private theorem inv_sqrt_two_mul_self : (√2)⁻¹ * (√2)⁻¹ * 2 = 1 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-! ### The scaling spaces -/

/-- The **Haar scaling space** of level $j \in \mathbb{Z}$ is the closed linear span
$$V_j = \overline{\operatorname{span}} \{\varphi_{j,k} : k \in \mathbb{Z}\}$$
in $L^2(\mathbb{R})$.

In [han2009theoretical], §4.4, $V_j$ is the set of finite linear combinations of the
$\varphi_{j,k}$; that set is a dense subspace of the space defined here. With the closure, $V_j$
is a Hilbert space with the Hilbert basis `Haar.hilbertBasis_V`. -/
def V (j : ℤ) : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)) :=
  (Submodule.span ℝ (Set.range (scalingFun j))).topologicalClosure

/-- The scaling space $V_j$ is closed in $L^2(\mathbb{R})$. -/
theorem isClosed_V (j : ℤ) : IsClosed (V j : Set (Lp ℝ 2 (volume : Measure ℝ))) :=
  Submodule.isClosed_topologicalClosure _

/-- The scaling function $\varphi_{j,k}$ lies in the scaling space $V_j$. -/
theorem scalingFun_mem_V (j k : ℤ) : scalingFun j k ∈ V j :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self k))

/-- A function $f \in L^2(\mathbb{R})$ lies in the orthogonal complement $V_j^\perp$ if and only if
$\langle \varphi_{j,k}, f \rangle = 0$ for every $k \in \mathbb{Z}$. -/
theorem mem_orthogonal_V_iff (j : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    f ∈ (V j)ᗮ ↔ ∀ k : ℤ, inner ℝ (scalingFun j k) f = 0 := by
  refine ⟨fun h k => (Submodule.mem_orthogonal _ _).1 h _ (scalingFun_mem_V j k), fun h => ?_⟩
  simp only [V]
  rw [Submodule.orthogonal_closure]
  exact Submodule.mem_orthogonal_span_range h

/-- The scaling functions $\varphi_{j,k}$, $k \in \mathbb{Z}$, of level $j$, as a Hilbert basis of
the scaling space $V_j$. -/
def hilbertBasis_V (j : ℤ) : HilbertBasis ℤ ℝ (V j) :=
  (orthonormal_scalingFun j).hilbertBasisTopologicalClosure

/-- Let $D$ be a linear isometric equivalence of $L^2(\mathbb{R})$ onto itself and $K$ a subspace of
$L^2(\mathbb{R})$. Then $D(\overline{K}) = \overline{D(K)}$. -/
theorem map_topologicalClosure
    (D : Lp ℝ 2 (volume : Measure ℝ) ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ))
    (K : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ))) :
    K.topologicalClosure.map D.toLinearEquiv.toLinearMap
      = (K.map D.toLinearEquiv.toLinearMap).topologicalClosure := by
  refine SetLike.ext' ?_
  rw [Submodule.map_coe, Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe,
    Submodule.map_coe]
  exact D.toHomeomorph.image_closure _

/-- Let $D$ be a linear isometric equivalence of $L^2(\mathbb{R})$ onto itself, and let $(f_i)$ and
$(g_i)$ be families in $L^2(\mathbb{R})$ with $D f_i = g_i$ for every $i$. Then $D$ maps the
closed linear span of the $f_i$ onto the closed linear span of the $g_i$. -/
theorem map_topologicalClosure_span_range
    (D : Lp ℝ 2 (volume : Measure ℝ) ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ)) {ι : Type*}
    {f g : ι → Lp ℝ 2 (volume : Measure ℝ)} (hfg : ∀ i, D (f i) = g i) :
    (Submodule.span ℝ (Set.range f)).topologicalClosure.map D.toLinearEquiv.toLinearMap
      = (Submodule.span ℝ (Set.range g)).topologicalClosure := by
  have himg : D.toLinearEquiv.toLinearMap '' Set.range f = Set.range g := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hfg)
  rw [map_topologicalClosure, Submodule.map_span, himg]

/-- The scaling spaces are **scale invariant**: for each $j \in \mathbb{Z}$, $V_j$ is the image of
$V_0$ under the dilation by $2^j$,
$$V_j = D_{2^j}(V_0) = \{x \mapsto 2^{j/2} f(2^j x) : f \in V_0\}.$$
This is Theorem 4.4.1(2) of [han2009theoretical].

$D_{2^j}$ is `MeasureTheory.Lp.dilationₗᵢ (2 ^ j)`. The proof applies
`Haar.map_topologicalClosure_span_range` to `Haar.scalingFun_eq_dilation`. -/
theorem V_eq_map_dilation (j : ℤ) :
    V j = (V 0).map
      (Lp.dilationₗᵢ ((2 : ℝ) ^ j) (zpow_ne_zero j two_ne_zero)).toLinearEquiv.toLinearMap :=
  (map_topologicalClosure_span_range _ fun k => (scalingFun_eq_dilation j k).symm).symm

/-- The **two-scale relation**: $\varphi_{j,k} = \frac{1}{\sqrt{2}} (\varphi_{j+1,2k} +
\varphi_{j+1,2k+1})$. The two functions on the right are supported on the two halves of
$I_{j,k}$. -/
theorem scalingFun_two_scale (j k : ℤ) :
    scalingFun j k = (√2)⁻¹ • (scalingFun (j + 1) (2 * k) + scalingFun (j + 1) (2 * k + 1)) := by
  have ht : (0 : ℝ) < 2 ^ (-(j + 1)) := by positivity
  have hstep : (2 : ℝ) ^ (-(j + 1)) * 2 = 2 ^ (-j) := by
    rw [← zpow_add_one₀ (two_ne_zero' ℝ)]
    congr 1
    ring
  have hdisj : Disjoint (dyadic (j + 1) (2 * k)) (dyadic (j + 1) (2 * k + 1)) :=
    Set.disjoint_iff_inter_eq_empty.mpr (dyadic_inter_dyadic (j + 1) (by omega))
  have hunion : dyadic (j + 1) (2 * k) ∪ dyadic (j + 1) (2 * k + 1) = dyadic j k := by
    simp only [dyadic]
    push_cast
    rw [Set.Ico_union_Ico_eq_Ico (by nlinarith) (by nlinarith)]
    congr 1 <;> rw [← hstep] <;> ring
  simp only [scalingFun]
  rw [← indicatorConstLp_disjoint_union (measurableSet_dyadic (j + 1) (2 * k))
      (measurableSet_dyadic (j + 1) (2 * k + 1)) (volume_dyadic_ne_top (j + 1) (2 * k))
      (volume_dyadic_ne_top (j + 1) (2 * k + 1)) hdisj,
    smul_indicatorConstLp,
    indicatorConstLp_congr_set _ _ (measurableSet_dyadic j k) (volume_dyadic_ne_top j k) hunion]
  congr 1
  rw [zpow_add_one₀ (two_ne_zero' ℝ), Real.sqrt_mul (by positivity)]
  field_simp

/-- The scaling spaces are **nested**: $V_j \subseteq V_{j+1}$ for every $j \in \mathbb{Z}$. This is
Theorem 4.4.1(3) of [han2009theoretical].

It follows from the two-scale relation `Haar.scalingFun_two_scale`. -/
theorem V_le_V_succ (j : ℤ) : V j ≤ V (j + 1) := by
  refine Submodule.topologicalClosure_minimal _ ?_ (isClosed_V (j + 1))
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  rw [scalingFun_two_scale]
  exact Submodule.smul_mem _ _
    (Submodule.add_mem _ (scalingFun_mem_V _ _) (scalingFun_mem_V _ _))

/-! ### Dyadic intervals and the floor function -/

private theorem mul_zpow_neg_le_iff (j : ℤ) (a x : ℝ) : a * 2 ^ (-j) ≤ x ↔ a ≤ 2 ^ j * x := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  rw [zpow_neg, ← div_eq_mul_inv, div_le_iff₀ h2, mul_comm x ((2 : ℝ) ^ j)]

private theorem lt_mul_zpow_neg_iff (j : ℤ) (a x : ℝ) : x < a * 2 ^ (-j) ↔ 2 ^ j * x < a := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  rw [zpow_neg, ← div_eq_mul_inv, lt_div_iff₀ h2, mul_comm x ((2 : ℝ) ^ j)]

private theorem le_mul_zpow_neg_iff (j : ℤ) (a x : ℝ) : x ≤ a * 2 ^ (-j) ↔ 2 ^ j * x ≤ a := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ h2, mul_comm x ((2 : ℝ) ^ j)]

private theorem mem_dyadic_iff (j k : ℤ) (x : ℝ) :
    x ∈ dyadic j k ↔ (k : ℝ) ≤ 2 ^ j * x ∧ 2 ^ j * x < (k : ℝ) + 1 := by
  rw [dyadic, Set.mem_Ico, mul_zpow_neg_le_iff, lt_mul_zpow_neg_iff]

private theorem mem_dyadic_iff_floor (j k : ℤ) (x : ℝ) :
    x ∈ dyadic j k ↔ k = ⌊(2 : ℝ) ^ j * x⌋ := by
  rw [mem_dyadic_iff, eq_comm, Int.floor_eq_iff]

/-! ### Finite sums of indicators in `L²` -/

private theorem coeFn_sum_indicatorConstLp (j : ℤ) (s : Finset ℤ) (c : ℤ → ℝ) :
    ((∑ k ∈ s, indicatorConstLp 2 (measurableSet_dyadic j k) (volume_dyadic_ne_top j k) (c k) :
        Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)
      =ᵐ[volume] fun x => ∑ k ∈ s, (dyadic j k).indicator (fun _ => c k) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)
  · intro a t ha ih
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add
        (indicatorConstLp 2 (measurableSet_dyadic j a) (volume_dyadic_ne_top j a) (c a))
        (∑ k ∈ t, indicatorConstLp 2 (measurableSet_dyadic j k) (volume_dyadic_ne_top j k) (c k)),
      ih, indicatorConstLp_coeFn (p := 2) (hs := measurableSet_dyadic j a)
        (hμs := volume_dyadic_ne_top j a) (c := c a)] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Finset.sum_insert ha]

/-! ### The dyadic step approximation -/

/-- The dyadic step function $x \mapsto \sum_{k=-M}^{M-1} g(k 2^{-j}) \mathbf{1}_{I_{j,k}}(x)$ of
$g$ at level $j$, which vanishes outside $[-M 2^{-j}, M 2^{-j})$. -/
private def stepFun (g : ℝ → ℝ) (j M : ℤ) : ℝ → ℝ := fun x =>
  ∑ k ∈ Finset.Ico (-M) M, (dyadic j k).indicator (fun _ => g ((k : ℝ) * 2 ^ (-j))) x

private theorem stepFun_apply (g : ℝ → ℝ) (j M : ℤ) (x : ℝ) :
    stepFun g j M x =
      ∑ k ∈ Finset.Ico (-M) M, (dyadic j k).indicator (fun _ => g ((k : ℝ) * 2 ^ (-j))) x :=
  rfl

/-- The dyadic step function of $g$ at level $j$, as a finite combination of the $\varphi_{j,k}$ in
$L^2(\mathbb{R})$; it lies in $V_j$. -/
private def stepLp (g : ℝ → ℝ) (j M : ℤ) : Lp ℝ 2 (volume : Measure ℝ) :=
  ∑ k ∈ Finset.Ico (-M) M, (g ((k : ℝ) * 2 ^ (-j)) * √((2 : ℝ) ^ (-j))) • scalingFun j k

private theorem stepLp_mem_V (g : ℝ → ℝ) (j M : ℤ) : stepLp g j M ∈ V j :=
  Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (scalingFun_mem_V j k)

private theorem stepLp_eq_sum (g : ℝ → ℝ) (j M : ℤ) :
    stepLp g j M = ∑ k ∈ Finset.Ico (-M) M,
      indicatorConstLp 2 (measurableSet_dyadic j k) (volume_dyadic_ne_top j k)
        (g ((k : ℝ) * 2 ^ (-j))) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [scalingFun, smul_indicatorConstLp]
  congr 1
  rw [mul_assoc, ← Real.sqrt_mul (by positivity), ← zpow_add₀ (two_ne_zero' ℝ)]
  simp

private theorem coeFn_stepLp (g : ℝ → ℝ) (j M : ℤ) :
    (stepLp g j M : ℝ → ℝ) =ᵐ[volume] stepFun g j M := by
  rw [stepLp_eq_sum]
  exact coeFn_sum_indicatorConstLp j _ _

/-- A continuous function $g$ with compact support is within $\varepsilon$ in the $L^2$ seminorm of
one of its dyadic step functions. -/
private theorem exists_step_approx (g : ℝ → ℝ) (hgc : Continuous g) (hgs : HasCompactSupport g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ j M : ℤ, eLpNorm (g - stepFun g j M) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨R, hR⟩ := hgs.isCompact.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨R₀, hR₀0, hzero⟩ :
      ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ x : ℝ, R₀ < |x| → g x = 0 := by
    refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have h := hR hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
    exact absurd (h.trans (le_max_left _ _)) (not_le.2 hx)
  -- the fixed window and the target modulus of continuity
  have hCpos : (0 : ℝ) < √(2 * (R₀ + 2)) := Real.sqrt_pos.mpr (by linarith)
  have hδ : (0 : ℝ) < ε / √(2 * (R₀ + 2)) := div_pos hε hCpos
  obtain ⟨η, hη, huc⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) _ hδ
  obtain ⟨j, hjlt, hjge⟩ : ∃ j : ℤ, (2 : ℝ) ^ (-j) < η ∧ (1 : ℝ) ≤ 2 ^ j := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨(n : ℤ), ?_, ?_⟩
    · have hrw : (2 : ℝ) ^ (-(n : ℤ)) = (1 / 2 : ℝ) ^ n := by
        rw [zpow_neg, zpow_natCast, one_div, inv_pow]
      rw [hrw]; exact hn
    · rw [zpow_natCast]; exact one_le_pow₀ (by norm_num)
  have hj0 : (0 : ℝ) < 2 ^ (-j) := by positivity
  obtain ⟨M, hMlow, hMhigh⟩ :
      ∃ M : ℤ, R₀ + 1 ≤ (M : ℝ) * 2 ^ (-j) ∧ (M : ℝ) * 2 ^ (-j) ≤ R₀ + 2 := by
    refine ⟨⌈(2 : ℝ) ^ j * (R₀ + 1)⌉, (le_mul_zpow_neg_iff j _ _).mpr (Int.le_ceil _), ?_⟩
    refine (mul_zpow_neg_le_iff j _ _).mpr ?_
    have h := Int.ceil_lt_add_one ((2 : ℝ) ^ j * (R₀ + 1))
    linarith
  refine ⟨j, M, ?_⟩
  -- the pointwise bound
  have hkey : ∀ x : ℝ, ‖(g - stepFun g j M) x‖ ≤
      ‖(Set.Ico (-((M : ℝ) * 2 ^ (-j))) ((M : ℝ) * 2 ^ (-j))).indicator
        (fun _ => ε / √(2 * (R₀ + 2))) x‖ := by
    intro x
    by_cases hx : x ∈ Set.Ico (-((M : ℝ) * 2 ^ (-j))) ((M : ℝ) * 2 ^ (-j))
    · rw [Set.indicator_of_mem hx]
      have hk : ⌊(2 : ℝ) ^ j * x⌋ ∈ Finset.Ico (-M) M := by
        rw [Finset.mem_Ico]
        refine ⟨?_, ?_⟩
        · rw [Int.le_floor]
          push_cast
          rw [← mul_zpow_neg_le_iff j (-(M : ℝ)) x, neg_mul]
          exact hx.1
        · rw [Int.floor_lt]
          exact (lt_mul_zpow_neg_iff j (M : ℝ) x).mp hx.2
      have hstep : stepFun g j M x = g ((⌊(2 : ℝ) ^ j * x⌋ : ℝ) * 2 ^ (-j)) := by
        have hsum := Finset.sum_eq_single_of_mem (f := fun k : ℤ =>
            (dyadic j k).indicator (fun _ => g ((k : ℝ) * 2 ^ (-j))) x)
          ⌊(2 : ℝ) ^ j * x⌋ hk (fun b _ hb =>
            Set.indicator_of_notMem (fun hmem => hb ((mem_dyadic_iff_floor j b x).mp hmem)) _)
        rw [stepFun_apply, hsum, Set.indicator_of_mem ((mem_dyadic_iff_floor j _ x).mpr rfl)]
      have hxd : x ∈ dyadic j ⌊(2 : ℝ) ^ j * x⌋ := (mem_dyadic_iff_floor j _ x).mpr rfl
      rw [dyadic, Set.mem_Ico] at hxd
      have hdist : dist x ((⌊(2 : ℝ) ^ j * x⌋ : ℝ) * 2 ^ (-j)) < η := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hxd.1])]
        linarith
      have hgd := huc hdist
      rw [Real.dist_eq] at hgd
      rw [Pi.sub_apply, hstep, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hδ.le]
      linarith
    · rw [Set.indicator_of_notMem hx]
      have hgx : g x = 0 := by
        refine hzero x ?_
        rcases lt_or_ge x (-((M : ℝ) * 2 ^ (-j))) with h | h
        · rw [abs_of_neg (by linarith)]
          linarith
        · have hb2 : (M : ℝ) * 2 ^ (-j) ≤ x := by
            by_contra hcon
            exact hx ⟨h, not_le.mp hcon⟩
          rw [abs_of_nonneg (by linarith)]
          linarith
      have hstep0 : stepFun g j M x = 0 := by
        rw [stepFun_apply]
        refine Finset.sum_eq_zero fun k hk => ?_
        refine Set.indicator_of_notMem (fun hmem => hx ?_) _
        rw [Finset.mem_Ico] at hk
        rw [dyadic, Set.mem_Ico] at hmem
        have hk1 : (-(M : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hk.1
        have hk2 : ((k : ℝ) + 1) ≤ (M : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ M)
        have h1 : (-(M : ℝ)) * 2 ^ (-j) ≤ (k : ℝ) * 2 ^ (-j) :=
          mul_le_mul_of_nonneg_right hk1 hj0.le
        have h2 : ((k : ℝ) + 1) * 2 ^ (-j) ≤ (M : ℝ) * 2 ^ (-j) :=
          mul_le_mul_of_nonneg_right hk2 hj0.le
        rw [neg_mul] at h1
        exact ⟨le_trans h1 hmem.1, lt_of_lt_of_le hmem.2 h2⟩
      rw [Pi.sub_apply, hgx, hstep0]
      simp
  -- from the pointwise bound to the `L²` bound
  have hvol : volume (Set.Ico (-((M : ℝ) * 2 ^ (-j))) ((M : ℝ) * 2 ^ (-j)))
      ≤ ENNReal.ofReal (2 * (R₀ + 2)) := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hmeas : AEStronglyMeasurable (g - stepFun g j M) volume :=
    hgc.aestronglyMeasurable.sub (Finset.measurable_sum _ fun k _ =>
      measurable_const.indicator (measurableSet_dyadic j k)).aestronglyMeasurable
  calc eLpNorm (g - stepFun g j M) 2 volume
      ≤ eLpNorm ((Set.Ico (-((M : ℝ) * 2 ^ (-j))) ((M : ℝ) * 2 ^ (-j))).indicator
          (fun _ => ε / √(2 * (R₀ + 2)))) 2 volume := eLpNorm_mono hmeas hkey
    _ ≤ ‖ε / √(2 * (R₀ + 2))‖ₑ
        * volume (Set.Ico (-((M : ℝ) * 2 ^ (-j))) ((M : ℝ) * 2 ^ (-j)))
          ^ (1 / (2 : ℝ≥0∞).toReal) :=
        eLpNorm_indicator_const_le _ _ measurableSet_Ico.nullMeasurableSet
    _ ≤ ENNReal.ofReal (ε / √(2 * (R₀ + 2)))
        * (ENNReal.ofReal (2 * (R₀ + 2))) ^ (1 / (2 : ℝ≥0∞).toReal) := by
        gcongr
        · exact le_of_eq (Real.enorm_eq_ofReal hδ.le)
    _ = ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← ENNReal.ofReal_mul hδ.le]
        congr 1
        rw [show (1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) by norm_num,
          ← Real.sqrt_eq_rpow]
        exact div_mul_cancel₀ ε hCpos.ne'

/-! ### Density -/

/-- The scaling spaces are **dense**: their union is dense in $L^2(\mathbb{R})$,
$$\overline{\textstyle\bigcup_{j \in \mathbb{Z}} V_j} = L^2(\mathbb{R}).$$
This is Theorem 4.4.1(4) of [han2009theoretical].

The union is the supremum `⨆ j, Haar.V j` of submodules. The proof approximates $f$ by a
continuous function with compact support, and that function by its dyadic step functions, which
lie in the $V_j$. -/
theorem topologicalClosure_iSup_V : (⨆ j : ℤ, V j).topologicalClosure = ⊤ := by
  refine Submodule.dense_iff_topologicalClosure_eq_top.mp fun f => ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, hgs, hgapprox, hgc, hgmem⟩ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by norm_num)
      (ε := ENNReal.ofReal (ε / 3)) (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  obtain ⟨j, M, hstep⟩ := exists_step_approx g hgc hgs (ε := ε / 3) (by linarith)
  refine ⟨stepLp g j M, ?_, ?_⟩
  · exact le_iSup V j (stepLp_mem_V g j M)
  · have h1 : ((f - hgmem.toLp g : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)
        =ᵐ[volume] (f : ℝ → ℝ) - g := by
      filter_upwards [Lp.coeFn_sub f (hgmem.toLp g), hgmem.coeFn_toLp] with x hx hx2
      rw [hx, Pi.sub_apply, Pi.sub_apply, hx2]
    have h2 : ((hgmem.toLp g - stepLp g j M : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ)
        =ᵐ[volume] g - stepFun g j M := by
      filter_upwards [Lp.coeFn_sub (hgmem.toLp g) (stepLp g j M), hgmem.coeFn_toLp,
        coeFn_stepLp g j M] with x hx hx2 hx3
      rw [hx, Pi.sub_apply, Pi.sub_apply, hx2, hx3]
    have hn1 : ‖f - hgmem.toLp g‖ ≤ ε / 3 := by
      rw [Lp.norm_def, eLpNorm_congr_ae h1]
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgapprox
      rwa [ENNReal.toReal_ofReal (by linarith)] at h
    have hn2 : ‖hgmem.toLp g - stepLp g j M‖ ≤ ε / 3 := by
      rw [Lp.norm_def, eLpNorm_congr_ae h2]
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hstep
      rwa [ENNReal.toReal_ofReal (by linarith)] at h
    have hsplit : f - stepLp g j M
        = (f - hgmem.toLp g) + (hgmem.toLp g - stepLp g j M) := by abel
    rw [dist_eq_norm, hsplit]
    have := norm_add_le (f - hgmem.toLp g) (hgmem.toLp g - stepLp g j M)
    linarith

/-! ### Separation -/

/-- If $u \in V_j$ and $v$ is orthogonal to every $\varphi_{j,k}$, $k \in \mathbb{Z}$, then
$\langle u, v \rangle = 0$. -/
private theorem inner_eq_zero_of_mem_V {j : ℤ} {u v : Lp ℝ 2 (volume : Measure ℝ)}
    (hu : u ∈ V j) (h : ∀ k : ℤ, inner ℝ (scalingFun j k) v = (0 : ℝ)) :
    inner ℝ u v = (0 : ℝ) :=
  (Submodule.mem_orthogonal _ _).1 ((mem_orthogonal_V_iff j v).2 h) u hu

/-- The identity $2^{-i} \sqrt{2^j} \sqrt{2^i} = \sqrt{2^{j-i}}$, which relates the scaling
functions of the levels $j$ and $i$. -/
private theorem sqrt_zpow_mul (j i : ℤ) :
    (2 : ℝ) ^ (-i) * (√((2 : ℝ) ^ j) * √((2 : ℝ) ^ i)) = √((2 : ℝ) ^ (j - i)) := by
  have hi : (0 : ℝ) < 2 ^ i := by positivity
  have hji : (0 : ℝ) ≤ (2 : ℝ) ^ (j - i) := by positivity
  have key : √((2 : ℝ) ^ (j - i)) * √((2 : ℝ) ^ i) = √((2 : ℝ) ^ j) := by
    rw [← Real.sqrt_mul hji, ← zpow_add₀ (two_ne_zero' ℝ)]
    congr 2
    ring
  have hsi : √((2 : ℝ) ^ i) * √((2 : ℝ) ^ i) = 2 ^ i := Real.mul_self_sqrt hi.le
  calc (2 : ℝ) ^ (-i) * (√((2 : ℝ) ^ j) * √((2 : ℝ) ^ i))
      = 2 ^ (-i) * ((√((2 : ℝ) ^ (j - i)) * √((2 : ℝ) ^ i)) * √((2 : ℝ) ^ i)) := by rw [key]
    _ = 2 ^ (-i) * (√((2 : ℝ) ^ (j - i)) * (√((2 : ℝ) ^ i) * √((2 : ℝ) ^ i))) := by ring
    _ = ((2 : ℝ) ^ (-i) * 2 ^ i) * √((2 : ℝ) ^ (j - i)) := by rw [hsi]; ring
    _ = √((2 : ℝ) ^ (j - i)) := by rw [← zpow_add₀ (two_ne_zero' ℝ)]; simp

/-- For $j \le i$, each dyadic interval $I_{i,k}$ of level $i$ lies in some dyadic interval
$I_{j,l}$ of level $j$. -/
private theorem exists_dyadic_subset {j i : ℤ} (hji : j ≤ i) (k : ℤ) :
    ∃ l : ℤ, dyadic i k ⊆ dyadic j l := by
  have hmi : (((i - j).toNat : ℤ)) = i - j := Int.toNat_of_nonneg (by omega)
  set m : ℕ := (i - j).toNat
  have hBA : (2 : ℝ) ^ (-j) = (2 : ℝ) ^ m * 2 ^ (-i) := by
    rw [← zpow_natCast (2 : ℝ) m, hmi, ← zpow_add₀ (two_ne_zero' ℝ)]
    congr 1
    omega
  have hpos : (0 : ℤ) < 2 ^ m := pow_pos (by norm_num) m
  have hdiv := Int.mul_ediv_add_emod k (2 ^ m)
  have hmod0 : 0 ≤ k % 2 ^ m := Int.emod_nonneg k (by positivity)
  have hmodlt := Int.emod_lt_of_pos k hpos
  have h1 : 2 ^ m * (k / 2 ^ m) ≤ k := by linarith
  have hexp : (2 : ℤ) ^ m * (k / 2 ^ m + 1) = 2 ^ m * (k / 2 ^ m) + 2 ^ m := by ring
  have h2 : k + 1 ≤ 2 ^ m * (k / 2 ^ m + 1) := by rw [hexp]; linarith
  refine ⟨k / 2 ^ m, ?_⟩
  have hA : (0 : ℝ) < 2 ^ (-i) := by positivity
  intro x hx
  rw [dyadic, Set.mem_Ico] at hx ⊢
  have hc1 : ((k / 2 ^ m : ℤ) : ℝ) * 2 ^ (-j) ≤ (k : ℝ) * 2 ^ (-i) := by
    rw [hBA, ← mul_assoc]
    have hcast : ((k / 2 ^ m : ℤ) : ℝ) * 2 ^ m = ((2 ^ m * (k / 2 ^ m) : ℤ) : ℝ) := by
      push_cast; ring
    rw [hcast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast h1) hA.le
  have hc2 : ((k : ℝ) + 1) * 2 ^ (-i) ≤ (((k / 2 ^ m : ℤ) : ℝ) + 1) * 2 ^ (-j) := by
    rw [hBA, ← mul_assoc]
    have hcast : (((k / 2 ^ m : ℤ) : ℝ) + 1) * 2 ^ m = ((2 ^ m * (k / 2 ^ m + 1) : ℤ) : ℝ) := by
      push_cast; ring
    rw [hcast]
    refine mul_le_mul_of_nonneg_right ?_ hA.le
    exact_mod_cast h2
  exact ⟨le_trans hc1 hx.1, lt_of_lt_of_le hx.2 hc2⟩

private theorem inner_scalingFun_cross {j i l k : ℤ} (hsub : dyadic i k ⊆ dyadic j l) :
    inner ℝ (scalingFun j l) (scalingFun i k) = √((2 : ℝ) ^ (j - i)) := by
  rw [scalingFun, scalingFun,
    L2.inner_indicatorConstLp_indicatorConstLp (measurableSet_dyadic j l)
      (measurableSet_dyadic i k) (volume_dyadic_ne_top j l) (volume_dyadic_ne_top i k),
    Set.inter_eq_right.mpr hsub, measureReal_def, volume_dyadic,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  rw [← sqrt_zpow_mul j i]
  ring

private theorem inner_scalingFun_cross_zero {j i l k m : ℤ} (hsub : dyadic i k ⊆ dyadic j l)
    (hm : m ≠ l) : inner ℝ (scalingFun j m) (scalingFun i k) = (0 : ℝ) := by
  have hempty : dyadic j m ∩ dyadic i k = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hx2⟩
    have hx3 : x ∈ dyadic j m ∩ dyadic j l := ⟨hx1, hsub hx2⟩
    rw [dyadic_inter_dyadic j hm] at hx3
    exact hx3
  rw [scalingFun, scalingFun,
    L2.inner_indicatorConstLp_indicatorConstLp (measurableSet_dyadic j m)
      (measurableSet_dyadic i k) (volume_dyadic_ne_top j m) (volume_dyadic_ne_top i k),
    hempty]
  simp

/-- For $j \le i$, $f \in V_j$ and $k \in \mathbb{Z}$, the coefficient of level $i$ satisfies
$|\langle \varphi_{i,k}, f \rangle| \le 2^{(j-i)/2} \|f\|$. -/
private theorem abs_inner_scalingFun_le {j i : ℤ} (hji : j ≤ i) (k : ℤ)
    {f : Lp ℝ 2 (volume : Measure ℝ)} (hf : f ∈ V j) :
    |inner ℝ (scalingFun i k) f| ≤ √((2 : ℝ) ^ (j - i)) * ‖f‖ := by
  obtain ⟨l, hsub⟩ := exists_dyadic_subset hji k
  set c : ℝ := √((2 : ℝ) ^ (j - i))
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hperp : ∀ m : ℤ,
      inner ℝ (scalingFun j m) (scalingFun i k - c • scalingFun j l) = (0 : ℝ) := by
    intro m
    rw [inner_sub_right, real_inner_smul_right]
    rcases eq_or_ne m l with rfl | hm
    · rw [inner_scalingFun_cross hsub, inner_scalingFun_self]
      ring
    · rw [inner_scalingFun_cross_zero hsub hm, inner_scalingFun_of_ne j hm]
      ring
  have hzero := inner_eq_zero_of_mem_V hf hperp
  rw [real_inner_comm] at hzero
  rw [inner_sub_left, real_inner_smul_left, sub_eq_zero] at hzero
  rw [hzero, abs_mul, abs_of_nonneg hc0]
  refine mul_le_mul_of_nonneg_left ?_ hc0
  have hnorm : ‖scalingFun j l‖ = 1 := (orthonormal_scalingFun j).1 l
  have := abs_real_inner_le_norm (scalingFun j l) f
  rwa [hnorm, one_mul] at this

private theorem inner_scalingFun_eq_zero_of_mem_iInf {f : Lp ℝ 2 (volume : Measure ℝ)}
    (hf : ∀ j : ℤ, f ∈ V j) (i k : ℤ) : inner ℝ (scalingFun i k) f = (0 : ℝ) := by
  by_contra hne
  have hpos : 0 < |inner ℝ (scalingFun i k) f| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos hpos (by positivity : (0 : ℝ) < ‖f‖ + 1)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hji : i - 2 * (n : ℤ) ≤ i := by omega
  have hsq : √((2 : ℝ) ^ (i - 2 * (n : ℤ) - i)) = (1 / 2 : ℝ) ^ n := by
    have hrw : i - 2 * (n : ℤ) - i = (-(n : ℤ)) + (-(n : ℤ)) := by ring
    rw [hrw, zpow_add₀ (two_ne_zero' ℝ), Real.sqrt_mul_self (by positivity),
      zpow_neg, zpow_natCast, one_div, inv_pow]
  have hb := abs_inner_scalingFun_le hji k (hf (i - 2 * (n : ℤ)))
  rw [hsq] at hb
  have hle : (1 / 2 : ℝ) ^ n * ‖f‖ ≤ (1 / 2 : ℝ) ^ n * (‖f‖ + 1) := by
    have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n
    nlinarith [norm_nonneg f]
  have hlt : (1 / 2 : ℝ) ^ n * (‖f‖ + 1) < |inner ℝ (scalingFun i k) f| := by
    have h1 := mul_lt_mul_of_pos_right hn (by positivity : (0 : ℝ) < ‖f‖ + 1)
    rwa [div_mul_cancel₀ _ (by positivity : (‖f‖ + 1) ≠ 0)] at h1
  linarith

/-- The scaling spaces are **separated**: their intersection is zero,
$$\bigcap_{j \in \mathbb{Z}} V_j = \{0\}.$$
This is Theorem 4.4.1(5) of [han2009theoretical].

The intersection is the infimum `⨅ j, Haar.V j` of submodules. For $f$ in every $V_j$ and
$j \le i$, the coefficient $\langle \varphi_{i,k}, f \rangle$ is bounded by $2^{(j-i)/2} \|f\|$
in absolute value, and this bound tends to $0$ as $j \to -\infty$. -/
theorem iInf_V_eq_bot : (⨅ j : ℤ, V j) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hfV : ∀ j : ℤ, f ∈ V j := fun j => (Submodule.mem_iInf _).mp hf j
  have hzero := inner_scalingFun_eq_zero_of_mem_iInf hfV
  have horth : ∀ i : ℤ, V i ≤ (Submodule.span ℝ {f})ᗮ := by
    intro i u hu
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact inner_eq_zero_of_mem_V hu (hzero i)
  have hclose : (⨆ i : ℤ, V i).topologicalClosure ≤ (Submodule.span ℝ {f})ᗮ :=
    Submodule.topologicalClosure_minimal _ (iSup_le horth) (Submodule.isClosed_orthogonal _)
  rw [topologicalClosure_iSup_V] at hclose
  have hfmem : f ∈ (Submodule.span ℝ {f})ᗮ := hclose Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hfmem
  exact inner_self_eq_zero.mp hfmem

/-! ### The wavelet functions and wavelet spaces -/

/-- Let $\varphi = \mathbf{1}_{[0,1)}$ and $\psi(x) = \varphi(2x) - \varphi(2x - 1)$. The **Haar
wavelet** of level $j \in \mathbb{Z}$ and index $k \in \mathbb{Z}$ is
$$\psi_{j,k}(x) = 2^{j/2} \psi(2^j x - k) = \frac{1}{\sqrt{2}} \bigl(\varphi_{j+1,2k}(x) -
  \varphi_{j+1,2k+1}(x)\bigr).$$
It equals $2^{j/2}$ on the left half of the dyadic interval $I_{j,k}$ and $-2^{j/2}$ on the
right half. This is the function of (4.4.2) in [han2009theoretical].

The definition is the second expression. `Haar.waveletFun_eq_sub_indicator` gives the closed
form. -/
def waveletFun (j k : ℤ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (√2)⁻¹ • (scalingFun (j + 1) (2 * k) - scalingFun (j + 1) (2 * k + 1))

/-- The defining formula of the Haar wavelet: $\psi_{j,k} = \frac{1}{\sqrt{2}} (\varphi_{j+1,2k} -
\varphi_{j+1,2k+1})$. -/
theorem waveletFun_eq (j k : ℤ) :
    waveletFun j k = (√2)⁻¹ • (scalingFun (j + 1) (2 * k) - scalingFun (j + 1) (2 * k + 1)) :=
  rfl

/-- The Haar wavelet in closed form: $\psi_{j,k} = 2^{j/2} \mathbf{1}_{I_{j+1,2k}} - 2^{j/2}
\mathbf{1}_{I_{j+1,2k+1}}$. The two intervals are the left and right halves of $I_{j,k}$, so
this is $2^{j/2} \psi(2^j x - k)$ with $\psi = \mathbf{1}_{[0,1/2)} - \mathbf{1}_{[1/2,1)}$. -/
theorem waveletFun_eq_sub_indicator (j k : ℤ) :
    waveletFun j k =
      indicatorConstLp 2 (measurableSet_dyadic (j + 1) (2 * k))
          (volume_dyadic_ne_top (j + 1) (2 * k)) (√((2 : ℝ) ^ j)) -
        indicatorConstLp 2 (measurableSet_dyadic (j + 1) (2 * k + 1))
          (volume_dyadic_ne_top (j + 1) (2 * k + 1)) (√((2 : ℝ) ^ j)) := by
  have hconst : (√2)⁻¹ * √((2 : ℝ) ^ (j + 1)) = √((2 : ℝ) ^ j) := by
    rw [zpow_add_one₀ (two_ne_zero' ℝ), Real.sqrt_mul (by positivity)]
    field_simp
  rw [waveletFun, smul_sub]
  simp only [scalingFun, smul_indicatorConstLp, hconst]

/-- For each level $j$, the wavelets $\psi_{j,k}$, $k \in \mathbb{Z}$, are orthonormal. -/
theorem orthonormal_waveletFun (j : ℤ) : Orthonormal ℝ (waveletFun j) := by
  rw [orthonormal_iff_ite]
  intro k l
  simp only [waveletFun, real_inner_smul_left, real_inner_smul_right, inner_sub_left,
    inner_sub_right]
  rcases eq_or_ne k l with rfl | h
  · rw [inner_scalingFun_self, inner_scalingFun_self,
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k ≠ 2 * k + 1),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k + 1 ≠ 2 * k),
      show (if k = k then (1 : ℝ) else 0) = 1 from by simp]
    linear_combination inv_sqrt_two_mul_self
  · rw [inner_scalingFun_of_ne (j + 1) (by omega : 2 * k ≠ 2 * l),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k ≠ 2 * l + 1),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k + 1 ≠ 2 * l),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k + 1 ≠ 2 * l + 1),
      show (if k = l then (1 : ℝ) else 0) = 0 from by simp [h]]
    ring

/-- The **Haar wavelet space** of level $j \in \mathbb{Z}$ is the closed linear span
$$W_j = \overline{\operatorname{span}} \{\psi_{j,k} : k \in \mathbb{Z}\}$$
in $L^2(\mathbb{R})$. It corresponds to the wavelet space $W_j$ of [han2009theoretical], §4.4.

As for `Haar.V`, the space is closed by definition. `Haar.W_eq_inf_orthogonal` shows that it is
the orthogonal complement of $V_j$ in $V_{j+1}$. -/
def W (j : ℤ) : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)) :=
  (Submodule.span ℝ (Set.range (waveletFun j))).topologicalClosure

/-- The wavelet $\psi_{j,k}$ lies in the wavelet space $W_j$. -/
theorem waveletFun_mem_W (j k : ℤ) : waveletFun j k ∈ W j :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self k))

/-- The wavelets $\psi_{j,k}$, $k \in \mathbb{Z}$, of level $j$, as a Hilbert basis of the wavelet
space $W_j$. -/
def hilbertBasis_W (j : ℤ) : HilbertBasis ℤ ℝ (W j) :=
  (orthonormal_waveletFun j).hilbertBasisTopologicalClosure

/-- The scaling functions of level $j + 1$ in terms of level $j$: $\varphi_{j+1,2k} =
\frac{1}{\sqrt{2}} (\varphi_{j,k} + \psi_{j,k})$ and $\varphi_{j+1,2k+1} = \frac{1}{\sqrt{2}}
(\varphi_{j,k} - \psi_{j,k})$. -/
theorem scalingFun_succ_eq (j k : ℤ) :
    scalingFun (j + 1) (2 * k) = (√2)⁻¹ • (scalingFun j k + waveletFun j k) ∧
      scalingFun (j + 1) (2 * k + 1) = (√2)⁻¹ • (scalingFun j k - waveletFun j k) := by
  have hone : (√2)⁻¹ * ((√2)⁻¹ * 2) = 1 := by linear_combination inv_sqrt_two_mul_self
  have key : ∀ a b : Lp ℝ 2 (volume : Measure ℝ),
      (√2)⁻¹ • ((√2)⁻¹ • (a + b) + (√2)⁻¹ • (a - b)) = a ∧
        (√2)⁻¹ • ((√2)⁻¹ • (a + b) - (√2)⁻¹ • (a - b)) = b := by
    intro a b
    constructor
    · rw [show (√2)⁻¹ • (a + b) + (√2)⁻¹ • (a - b) = ((√2)⁻¹ * 2) • a by module, smul_smul,
        hone, one_smul]
    · rw [show (√2)⁻¹ • (a + b) - (√2)⁻¹ • (a - b) = ((√2)⁻¹ * 2) • b by module, smul_smul,
        hone, one_smul]
  refine ⟨?_, ?_⟩
  · rw [waveletFun, scalingFun_two_scale j k]
    exact (key _ _).1.symm
  · rw [waveletFun, scalingFun_two_scale j k]
    exact (key _ _).2.symm

/-- The wavelet space $W_j$ is closed in $L^2(\mathbb{R})$. -/
theorem isClosed_W (j : ℤ) : IsClosed (W j : Set (Lp ℝ 2 (volume : Measure ℝ))) :=
  Submodule.isClosed_topologicalClosure _

instance (j : ℤ) : CompleteSpace (V j) := (isClosed_V j).completeSpace_coe

instance (j : ℤ) : CompleteSpace (W j) := (isClosed_W j).completeSpace_coe

/-- A scaling function and a wavelet of the same level are orthogonal:
$\langle \varphi_{j,k}, \psi_{j,l} \rangle = 0$ for all $k, l \in \mathbb{Z}$. -/
theorem inner_scalingFun_waveletFun (j k l : ℤ) :
    inner ℝ (scalingFun j k) (waveletFun j l) = 0 := by
  simp only [waveletFun, scalingFun_two_scale j k, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_sub_right]
  rcases eq_or_ne k l with rfl | h
  · rw [inner_scalingFun_self, inner_scalingFun_self,
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k ≠ 2 * k + 1),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k + 1 ≠ 2 * k)]
    ring
  · rw [inner_scalingFun_of_ne (j + 1) (by omega : 2 * k ≠ 2 * l),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k ≠ 2 * l + 1),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k + 1 ≠ 2 * l),
      inner_scalingFun_of_ne (j + 1) (by omega : 2 * k + 1 ≠ 2 * l + 1)]
    ring

/-- The wavelet $\psi_{j,k}$ lies in the scaling space $V_{j+1}$. -/
theorem waveletFun_mem_V_succ (j k : ℤ) : waveletFun j k ∈ V (j + 1) :=
  Submodule.smul_mem _ _
    (Submodule.sub_mem _ (scalingFun_mem_V _ _) (scalingFun_mem_V _ _))

/-- The wavelet space of level $j$ lies in the scaling space of level $j + 1$:
$W_j \subseteq V_{j+1}$. -/
theorem W_le_V_succ (j : ℤ) : W j ≤ V (j + 1) := by
  refine Submodule.topologicalClosure_minimal _ ?_ (isClosed_V (j + 1))
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact waveletFun_mem_V_succ j k

/-- Every element of the scaling space $V_j$ is orthogonal to the wavelet space $W_j$:
$V_j \subseteq W_j^\perp$. -/
theorem V_le_orthogonal_W (j : ℤ) : V j ≤ (W j)ᗮ := by
  simp only [W]
  rw [Submodule.orthogonal_closure]
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact Submodule.mem_orthogonal_span_range fun l => by
    rw [real_inner_comm]; exact inner_scalingFun_waveletFun j k l

/-- Every element of the wavelet space $W_j$ is orthogonal to the scaling space $V_j$:
$W_j \subseteq V_j^\perp$. This is `Haar.V_le_orthogonal_W` read the other way. -/
theorem W_le_orthogonal_V (j : ℤ) : W j ≤ (V j)ᗮ :=
  (Submodule.le_orthogonal_orthogonal _).trans (Submodule.orthogonal_le (V_le_orthogonal_W j))

/-- The scaling space $V_{j+1}$ lies in the closure of $V_j + W_j$, because every $\varphi_{j+1,k}$
lies in $V_j + W_j$. -/
private theorem V_succ_le_topologicalClosure_sup (j : ℤ) :
    V (j + 1) ≤ (V j ⊔ W j).topologicalClosure := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  have hle : V j ⊔ W j ≤ (V j ⊔ W j).topologicalClosure := Submodule.le_topologicalClosure _
  rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain rfl : m = 2 * k := by omega
    rw [(scalingFun_succ_eq j k).1]
    exact hle (Submodule.smul_mem _ _ (Submodule.add_mem _
      (Submodule.mem_sup_left (scalingFun_mem_V j k))
      (Submodule.mem_sup_right (waveletFun_mem_W j k))))
  · obtain rfl : m = 2 * k + 1 := by omega
    rw [(scalingFun_succ_eq j k).2]
    exact hle (Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.mem_sup_left (scalingFun_mem_V j k))
      (Submodule.mem_sup_right (waveletFun_mem_W j k))))

/-- Let $j \in \mathbb{Z}$ and $f \in L^2(\mathbb{R})$. Then $f \in W_j$ if and only if
$f \in V_{j+1}$ and
$$\langle \varphi_{j,k}, f \rangle = 0 \quad \text{for every } k \in \mathbb{Z}.$$
This is Theorem 4.4.2 of [han2009theoretical].

In terms of the coefficients $a_k = \langle \varphi_{j+1,k}, f \rangle$, the condition says
$a_{2k+1} = -a_{2k}$ for every $k$, because $\langle \varphi_{j,k}, f \rangle = (a_{2k} +
a_{2k+1}) / \sqrt{2}$ by the two-scale relation. -/
theorem mem_W_iff (j : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    f ∈ W j ↔ f ∈ V (j + 1) ∧ ∀ k : ℤ, inner ℝ (scalingFun j k) f = 0 := by
  refine ⟨fun h => ⟨W_le_V_succ j h, (mem_orthogonal_V_iff j f).1 (W_le_orthogonal_V j h)⟩,
    fun ⟨hf, horth⟩ => ?_⟩
  have hfV : f ∈ (V j)ᗮ := (mem_orthogonal_V_iff j f).2 horth
  set u := (W j).starProjection f with hu
  have huW : u ∈ W j := (W j).starProjection_apply_mem f
  have hr1 : f - u ∈ (W j)ᗮ := (W j).sub_starProjection_mem_orthogonal f
  have hr2 : f - u ∈ (V j)ᗮ := Submodule.sub_mem _ hfV (W_le_orthogonal_V j huW)
  have hr3 : f - u ∈ V (j + 1) := Submodule.sub_mem _ hf (W_le_V_succ j huW)
  have hr4 : f - u ∈ (V j ⊔ W j)ᗮ := by
    rw [← Submodule.inf_orthogonal]
    exact ⟨hr2, hr1⟩
  have hr5 : f - u ∈ (V (j + 1))ᗮ := by
    refine Submodule.orthogonal_le (V_succ_le_topologicalClosure_sup j) ?_
    rwa [Submodule.orthogonal_closure]
  have : f - u = 0 := by
    have := Submodule.inf_orthogonal_eq_bot (K := V (j + 1))
    rw [Submodule.eq_bot_iff] at this
    exact this _ ⟨hr3, hr5⟩
  rwa [sub_eq_zero.mp this]

/-- The wavelet space is the orthogonal complement of $V_j$ in $V_{j+1}$:
$W_j = V_{j+1} \cap V_j^\perp$. -/
theorem W_eq_inf_orthogonal (j : ℤ) : W j = V (j + 1) ⊓ (V j)ᗮ := by
  ext f
  rw [mem_W_iff, Submodule.mem_inf, mem_orthogonal_V_iff]

/-- The scaling and wavelet spaces of level $j$ span the scaling space of level $j + 1$:
$V_j + W_j = V_{j+1}$, with no closure needed. -/
theorem sup_V_W (j : ℤ) : V j ⊔ W j = V (j + 1) := by
  refine le_antisymm (sup_le (V_le_V_succ j) (W_le_V_succ j)) fun f hf => ?_
  set g := (V j).starProjection f with hg
  have hgV : g ∈ V j := (V j).starProjection_apply_mem f
  have hr : f - g ∈ (V j)ᗮ := (V j).sub_starProjection_mem_orthogonal f
  have hrW : f - g ∈ W j := by
    refine (mem_W_iff j (f - g)).2 ⟨Submodule.sub_mem _ hf (V_le_V_succ j hgV), ?_⟩
    exact (mem_orthogonal_V_iff j (f - g)).1 hr
  have := Submodule.add_mem (V j ⊔ W j) (Submodule.mem_sup_left hgV)
    (Submodule.mem_sup_right hrW)
  rwa [add_sub_cancel] at this

/-- The scaling and wavelet spaces of the same level meet only in zero: $V_j \cap W_j = \{0\}$. -/
theorem disjoint_V_W (j : ℤ) : Disjoint (V j) (W j) := by
  rw [disjoint_iff, Submodule.eq_bot_iff]
  rintro f ⟨hV, hW⟩
  have := Submodule.inf_orthogonal_eq_bot (K := V j)
  rw [Submodule.eq_bot_iff] at this
  exact this _ ⟨hV, W_le_orthogonal_V j hW⟩

/-- For each $j \in \mathbb{Z}$, the subspaces $V_j$ and $W_j$ of $V_{j+1}$ are complementary:
$$V_j \cap W_j = \{0\}, \qquad V_j + W_j = V_{j+1}.$$
Since $V_j \perp W_j$, the space $V_{j+1}$ is the orthogonal direct sum $V_j \oplus W_j$. See
[han2009theoretical], §4.4.

The Lean statement is `IsCompl` in the lattice of subspaces of $V_{j+1}$, with $V_j$ and $W_j$
pulled back along the inclusion of $V_{j+1}$ by `Submodule.comap`. The orthogonality
$V_j \perp W_j$ is `Haar.V_le_orthogonal_W`. -/
theorem isCompl_V_W (j : ℤ) :
    IsCompl ((V j).comap (V (j + 1)).subtype) ((W j).comap (V (j + 1)).subtype) := by
  have hinj : Function.Injective (V (j + 1)).subtype := Subtype.coe_injective
  constructor
  · rw [disjoint_iff, ← Submodule.comap_inf, (disjoint_V_W j).eq_bot, Submodule.comap_bot,
      Submodule.ker_subtype]
  · rw [codisjoint_iff]
    refine Submodule.map_injective_of_injective hinj ?_
    rw [Submodule.map_sup, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
      Submodule.map_subtype_top, inf_eq_right.mpr (V_le_V_succ j),
      inf_eq_right.mpr (W_le_V_succ j), sup_V_W]

/-! ### Decomposition and reconstruction -/

/-- The **decomposition** (analysis) step. Let $f \in L^2(\mathbb{R})$ and $j, k \in \mathbb{Z}$,
and write $a^j_k = \langle \varphi_{j,k}, f \rangle$ and $b^j_k = \langle \psi_{j,k}, f \rangle$
for the scaling and wavelet coefficients of $f$. Then
$$a^j_k = \frac{1}{\sqrt{2}} \bigl(a^{j+1}_{2k} + a^{j+1}_{2k+1}\bigr), \qquad b^j_k =
  \frac{1}{\sqrt{2}} \bigl(a^{j+1}_{2k} - a^{j+1}_{2k+1}\bigr).$$
This is Theorem 4.4.3 of [han2009theoretical].

The coefficients are inner products with the normalized functions $\varphi_{j,k}$ and
$\psi_{j,k}$. -/
theorem decomposition (j k : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    inner ℝ (scalingFun j k) f =
        (√2)⁻¹ * (inner ℝ (scalingFun (j + 1) (2 * k)) f +
          inner ℝ (scalingFun (j + 1) (2 * k + 1)) f) ∧
      inner ℝ (waveletFun j k) f =
        (√2)⁻¹ * (inner ℝ (scalingFun (j + 1) (2 * k)) f -
          inner ℝ (scalingFun (j + 1) (2 * k + 1)) f) := by
  refine ⟨?_, ?_⟩
  · rw [scalingFun_two_scale j k, real_inner_smul_left, inner_add_left]
  · rw [waveletFun, real_inner_smul_left, inner_sub_left]

/-- The **reconstruction** (synthesis) step, inverse to `Haar.decomposition`. Let
$f \in L^2(\mathbb{R})$ and $j, k \in \mathbb{Z}$, and write
$a^j_k = \langle \varphi_{j,k}, f \rangle$ and $b^j_k = \langle \psi_{j,k}, f \rangle$. Then
$$a^{j+1}_{2k} = \frac{1}{\sqrt{2}} \bigl(a^j_k + b^j_k\bigr), \qquad a^{j+1}_{2k+1} =
  \frac{1}{\sqrt{2}} \bigl(a^j_k - b^j_k\bigr).$$
This is Theorem 4.4.4 of [han2009theoretical]. -/
theorem reconstruction (j k : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    inner ℝ (scalingFun (j + 1) (2 * k)) f =
        (√2)⁻¹ * (inner ℝ (scalingFun j k) f + inner ℝ (waveletFun j k) f) ∧
      inner ℝ (scalingFun (j + 1) (2 * k + 1)) f =
        (√2)⁻¹ * (inner ℝ (scalingFun j k) f - inner ℝ (waveletFun j k) f) := by
  obtain ⟨h1, h2⟩ := scalingFun_succ_eq j k
  refine ⟨?_, ?_⟩
  · rw [h1, real_inner_smul_left, inner_add_left]
  · rw [h2, real_inner_smul_left, inner_sub_left]

/-! ### The multi-level decomposition -/

/-- The scaling spaces increase with the level: if $i \le j$, then $V_i \subseteq V_j$.

The proof iterates `Haar.V_le_V_succ`. -/
theorem V_mono {i j : ℤ} (h : i ≤ j) : V i ≤ V j := by
  induction j, h using Int.leInduction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (V_le_V_succ n)

/-- A function $f \in L^2(\mathbb{R})$ lies in $W_j^\perp$ if and only if
$\langle \psi_{j,k}, f \rangle = 0$ for every $k \in \mathbb{Z}$. -/
theorem mem_orthogonal_W_iff (j : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    f ∈ (W j)ᗮ ↔ ∀ k : ℤ, inner ℝ (waveletFun j k) f = 0 := by
  refine ⟨fun h k => (Submodule.mem_orthogonal _ _).1 h _ (waveletFun_mem_W j k), fun h => ?_⟩
  simp only [W]
  rw [Submodule.orthogonal_closure]
  exact Submodule.mem_orthogonal_span_range h

/-- **One analysis step**, as a splitting of the projection: for $f \in L^2(\mathbb{R})$ and
$j \in \mathbb{Z}$,
$$P_{V_{j+1}} f = P_{V_j} f + P_{W_j} f.$$
It holds because $V_{j+1}$ is the orthogonal direct sum of $V_j$ and $W_j$. -/
theorem starProjection_V_succ (j : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    (V (j + 1)).starProjection f = (V j).starProjection f + (W j).starProjection f := by
  obtain ⟨g, hg⟩ : ∃ g, (V (j + 1)).starProjection f = g := ⟨_, rfl⟩
  have hgmem : g ∈ V (j + 1) := hg ▸ (V (j + 1)).starProjection_apply_mem f
  -- projecting `f` onto `V j` or `W j` is projecting `g` onto them
  have hVg : (V j).starProjection g = (V j).starProjection f := by
    rw [← hg]
    exact congrFun (congrArg DFunLike.coe
      (Submodule.starProjection_comp_starProjection_of_le (V_le_V_succ j))) f
  have hWg : (W j).starProjection g = (W j).starProjection f := by
    rw [← hg]
    exact congrFun (congrArg DFunLike.coe
      (Submodule.starProjection_comp_starProjection_of_le (W_le_V_succ j))) f
  -- the part of `g` orthogonal to `V j` lies in `W j`, and is what `W j` projects it to
  have hsub : g - (V j).starProjection g ∈ W j := by
    refine (mem_W_iff j _).2 ⟨Submodule.sub_mem _ hgmem
      (V_le_V_succ j ((V j).starProjection_apply_mem g)), ?_⟩
    exact (mem_orthogonal_V_iff j _).1 ((V j).sub_starProjection_mem_orthogonal g)
  have hzero : (W j).starProjection ((V j).starProjection g) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr
      (V_le_orthogonal_W j ((V j).starProjection_apply_mem g))
  have hWval : (W j).starProjection g = g - (V j).starProjection g := by
    have h := map_sub ((W j).starProjection) g ((V j).starProjection g)
    rw [hzero, sub_zero] at h
    rw [← h]
    exact Submodule.starProjection_eq_self_iff.mpr hsub
  rw [hg, ← hVg, ← hWg, hWval]
  abel

/-- The **multi-level Haar decomposition**. Let $i \le j$ be integers and $f \in L^2(\mathbb{R})$.
Then
$$P_{V_j} f = P_{V_i} f + \sum_{l=i}^{j-1} P_{W_l} f,$$
the splitting of the projection onto $V_j$ into the coarse part in $V_i$ and the detail parts in
the intermediate wavelet spaces. This is the content of (4.4.9)–(4.4.13) and (4.4.18) of
[han2009theoretical].

The projection $P_S$ is `Submodule.starProjection`, and the sum runs over `Finset.Ico i j`. The
formula iterates `Haar.starProjection_V_succ`. It is the Haar transform as an algorithm: $j - i$
rounds of `Haar.decomposition` produce exactly these summands, and each summand is expanded in
its own orthonormal system by `Haar.hilbertBasis_V` and `Haar.hilbertBasis_W`. -/
theorem starProjection_V_eq_sum {i j : ℤ} (h : i ≤ j) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    (V j).starProjection f
      = (V i).starProjection f + ∑ l ∈ Finset.Ico i j, (W l).starProjection f := by
  induction j, h using Int.leInduction with
  | base => simp
  | succ n hn ih =>
      rw [starProjection_V_succ, ih, ← Finset.sum_Ico_add_eq_sum_Ico_add_one hn, add_assoc]

/-- The coarse part of $f$ at level $j$, expanded in the scaling functions of level $j$:
$$P_{V_j} f = \sum_{k \in \mathbb{Z}} \langle \varphi_{j,k}, f \rangle \varphi_{j,k},$$
with unconditional convergence in $L^2(\mathbb{R})$. It corresponds to the expansion
$f_j = \sum_k a^j_k \varphi(2^j x - k)$ of [han2009theoretical], §4.4; here the coefficients are
taken against the normalized functions $\varphi_{j,k}$. -/
theorem hasSum_inner_smul_starProjection_V (j : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    HasSum (fun k : ℤ => (inner ℝ (scalingFun j k) f) • scalingFun j k)
      ((V j).starProjection f) :=
  (orthonormal_scalingFun j).hasSum_inner_smul_starProjection f

/-- The detail part of $f$ at level $j$, expanded in the wavelets of level $j$:
$$P_{W_j} f = \sum_{k \in \mathbb{Z}} \langle \psi_{j,k}, f \rangle \psi_{j,k},$$
with unconditional convergence in $L^2(\mathbb{R})$. It corresponds to the expansion
$w_j = \sum_k b^j_k \psi(2^j x - k)$ of [han2009theoretical], §4.4; here the coefficients are
taken against the normalized functions $\psi_{j,k}$. -/
theorem hasSum_inner_smul_starProjection_W (j : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    HasSum (fun k : ℤ => (inner ℝ (waveletFun j k) f) • waveletFun j k)
      ((W j).starProjection f) :=
  (orthonormal_waveletFun j).hasSum_inner_smul_starProjection f

/-! ### The Haar wavelets as a basis of $L^2(\mathbb{R})$ -/

/-- Wavelets of different levels are orthogonal: for $i < j$ and $k, l \in \mathbb{Z}$,
$\langle \psi_{i,k}, \psi_{j,l} \rangle = 0$. The reason is that
$W_i \subseteq V_{i+1} \subseteq V_j$ and $V_j \perp W_j$. -/
theorem inner_waveletFun_of_lt {i j : ℤ} (hij : i < j) (k l : ℤ) :
    inner ℝ (waveletFun i k) (waveletFun j l) = 0 := by
  have hmem : waveletFun i k ∈ (W j)ᗮ :=
    (((W_le_V_succ i).trans (V_mono (by omega))).trans (V_le_orthogonal_W j)) (waveletFun_mem_W i k)
  rw [real_inner_comm]
  exact (Submodule.mem_orthogonal _ _).1 hmem _ (waveletFun_mem_W j l)

/-- The Haar wavelets $\psi_{j,k}$ of all levels and indices, $(j, k) \in \mathbb{Z}^2$, are
orthonormal. -/
theorem orthonormal_waveletFun_prod :
    Orthonormal ℝ fun p : ℤ × ℤ => waveletFun p.1 p.2 := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, k⟩ ⟨j, l⟩
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [inner_waveletFun_of_lt hij, ite_eq_right (by simp [Prod.ext_iff]; omega)]
  · have h := (orthonormal_iff_ite.mp (orthonormal_waveletFun i)) k l
    rw [h]
    by_cases hkl : k = l
    · rw [ite_eq_left hkl, ite_eq_left (by rw [hkl])]
    · rw [ite_eq_right hkl, ite_eq_right (by simp [Prod.ext_iff, hkl])]
  · rw [real_inner_comm, inner_waveletFun_of_lt hij, ite_eq_right (by simp [Prod.ext_iff]; omega)]

/-- A function orthogonal to every Haar wavelet is zero: the orthogonal complement of the span of
$\{\psi_{j,k} : j, k \in \mathbb{Z}\}$ is $\{0\}$. -/
theorem orthogonal_span_waveletFun_prod_eq_bot :
    (Submodule.span ℝ (Set.range fun p : ℤ × ℤ => waveletFun p.1 p.2))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  -- `f` is orthogonal to every wavelet space, so every detail projection vanishes
  have hW : ∀ j : ℤ, (W j).starProjection f = 0 := by
    intro j
    refine (Submodule.starProjection_apply_eq_zero_iff _).mpr
      ((mem_orthogonal_W_iff j f).2 fun k => ?_)
    exact (Submodule.mem_orthogonal _ _).1 hf _ (Submodule.subset_span ⟨(j, k), rfl⟩)
  -- the coarse projections are then all equal, hence lie in every scaling space
  have hV : ∀ {i j : ℤ}, i ≤ j → (V j).starProjection f = (V i).starProjection f := by
    intro i j hij
    rw [starProjection_V_eq_sum hij f, Finset.sum_congr rfl fun l _ => hW l, Finset.sum_const_zero,
      add_zero]
  have hmem : ∀ j : ℤ, (V j).starProjection f ∈ ⨅ i : ℤ, V i := by
    intro j
    refine Submodule.mem_iInf _ |>.mpr fun i => ?_
    rcases le_total i j with hij | hij
    · rw [hV hij]
      exact (V i).starProjection_apply_mem f
    · exact V_mono hij ((V j).starProjection_apply_mem f)
  have hVzero : ∀ j : ℤ, (V j).starProjection f = 0 := by
    intro j
    have := hmem j
    rw [iInf_V_eq_bot, Submodule.mem_bot] at this
    exact this
  -- so `f` is orthogonal to every scaling space, and those are dense
  have horth : ∀ i : ℤ, V i ≤ (Submodule.span ℝ {f})ᗮ := by
    intro i u hu
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact (Submodule.mem_orthogonal _ _).1
      ((Submodule.starProjection_apply_eq_zero_iff _).mp (hVzero i)) u hu
  have hclose : (⨆ i : ℤ, V i).topologicalClosure ≤ (Submodule.span ℝ {f})ᗮ :=
    Submodule.topologicalClosure_minimal _ (iSup_le horth) (Submodule.isClosed_orthogonal _)
  rw [topologicalClosure_iSup_V] at hclose
  have hfmem : f ∈ (Submodule.span ℝ {f})ᗮ := hclose Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hfmem
  exact inner_self_eq_zero.mp hfmem

/-- The **Haar basis**: the wavelets
$$\psi_{j,k}(x) = 2^{j/2} \psi(2^j x - k), \qquad (j, k) \in \mathbb{Z}^2,$$
form a Hilbert basis of $L^2(\mathbb{R})$. This is Exercise 4.4.4 of [han2009theoretical].

The basis is built by `HilbertBasis.mkOfOrthogonalEqBot` from `Haar.orthonormal_waveletFun_prod`
and `Haar.orthogonal_span_waveletFun_prod_eq_bot`. `Haar.coe_hilbertBasis` identifies its
elements. -/
noncomputable def hilbertBasis : HilbertBasis (ℤ × ℤ) ℝ (Lp ℝ 2 (volume : Measure ℝ)) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_waveletFun_prod
    orthogonal_span_waveletFun_prod_eq_bot

/-- The element of `Haar.hilbertBasis` at $(j, k)$ is the wavelet $\psi_{j,k}$. -/
@[simp]
theorem coe_hilbertBasis : ⇑hilbertBasis = fun p : ℤ × ℤ => waveletFun p.1 p.2 :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

end Haar

end
