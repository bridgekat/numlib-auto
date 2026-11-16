/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Numlib.Analysis.Fourier.TrigonometricPolynomial
import Numlib.FiniteDifference.TwoLevel

/-!
# Constant-coefficient difference schemes on the integer grid

A **stencil** is a finitely supported family $(c_s)_{s \in \mathbb{Z}}$ of real weights. It acts on
grid functions $u \colon \mathbb{Z} \to M$, for any real vector space $M$, by the finite convolution
$$(cu)_j = \sum_s c_s u_{j-s},$$
so $c_s$ is the weight of the neighbour $s$ steps to the left. The three-point stencils
$(cu)_j = c_- u_{j-1} + c_0 u_j + c_+ u_{j+1}$ cover every explicit scheme of
[quarteroni2000numerical], §13.7. The conservative form $u_j - \lambda (h(u_j, u_{j+1}) - h(u_{j-1},
u_j))$ of their (13.36), with a linear numerical flux $h(u, v) = \alpha u + \beta v$, is a
three-point stencil. The **discrete norms** $\|v\|_{\Delta, p} = \Delta x^{1/p} \|v\|_{\ell^p}$ of
[quarteroni2000numerical], (13.47), and the **stability of a family of schemes** over every finite
horizon, $\|Q^n\| \le C_T$ for $n \Delta t \le T$ and small steps ([quarteroni2000numerical],
(13.46), and Definition 6.3.1 of [han2009theoretical]), complete the setting.

Three facts carry the theory. First, **finite speed of propagation**: if every $s$ in the support
has $|s| \le r$, then $(c^n u)_j$ depends only on the values of $u$ within distance $nr$ of $j$.
This is the numerical domain of dependence, and it is the source of the necessary
Courant–Friedrichs–Lewy condition of [quarteroni2000numerical], §13.8.3. Second, a **monotone**
stencil, with $c_s \ge 0$ and $\sum_s c_s = 1$, takes convex averages of neighbouring values. It
therefore satisfies the discrete maximum principle, and it is nonexpansive in every $\ell^p$. The
upwind and Lax–Friedrichs schemes are monotone exactly under the CFL condition. Third, a stencil is
a bounded operator on $\ell^p(\mathbb{Z})$ with norm at most $\sum_s |c_s|$ (Young's inequality for
a finitely supported kernel), because it is a weighted sum of shift isometries. For $p = 2$ the
sharp bound is the supremum of the modulus of the **symbol**
$\sigma(\varphi) = \sum_s c_s e^{-is\varphi}$, the amplification factor of the mode
$j \mapsto e^{ij\varphi}$. This $\ell^2$ bound is the whole-line counterpart of the periodic von
Neumann analysis of `Numlib.FiniteDifference.VonNeumann`.

## Main definitions

* `lp.compEquivₗᵢ`: reindexing of $\ell^p$ along a bijection of the index set, as a linear isometry.
* `lp.shiftₗᵢ`: the translation $u \mapsto (j \mapsto u_{j-s})$ on $\ell^p(\mathbb{Z})$.
* `FiniteDifference.Stencil`: a finitely supported family of real weights on $\mathbb{Z}$.
* `FiniteDifference.Stencil.apply`: the action $(cu)_j = \sum_s c_s u_{j-s}$ of a stencil.
* `FiniteDifference.Stencil.threePoint`: the stencil $(cu)_j = c_- u_{j-1} + c_0 u_j + c_+ u_{j+1}$.
* `FiniteDifference.Stencil.ofFlux`: the stencil of the conservative form with the linear flux
  $h(u, v) = \alpha u + \beta v$.
* `FiniteDifference.IsConservativeForm`: a step of the form $u_j - \lambda (h(u_j, u_{j+1}) -
  h(u_{j-1}, u_j))$.
* `FiniteDifference.Stencil.IsMonotone`: nonnegative weights with sum $1$.
* `FiniteDifference.Stencil.lpCLM`: a stencil as a bounded operator on $\ell^p(\mathbb{Z})$.
* `FiniteDifference.Stencil.symbol`: the symbol $\sigma(\varphi) = \sum_s c_s e^{-is\varphi}$.
* `FiniteDifference.discreteNorm`: the discrete norm $\|v\|_{\Delta, p} = \Delta x^{1/p}
  \|v\|_{\ell^p}$.
* `FiniteDifference.IsStableFamily`: stability of a family of schemes over every finite horizon.

## Main results

* `FiniteDifference.Stencil.isConservativeForm_iff`: a step is in conservative form with a linear
  flux if and only if it is the action of `FiniteDifference.Stencil.ofFlux`.
* `FiniteDifference.Stencil.iterate_apply_congr_of_eqOn`: finite speed of propagation.
* `FiniteDifference.Stencil.IsMonotone.apply_le_iSup` and
  `FiniteDifference.Stencil.IsMonotone.iInf_le_apply`: the discrete maximum principle
  $\inf_i u_i \le (cu)_j \le \sup_i u_i$ for a monotone stencil.
* `FiniteDifference.Stencil.norm_lpCLM_le`: the operator norm on $\ell^p(\mathbb{Z})$ is at most
  $\sum_s |c_s|$.
* `FiniteDifference.Stencil.IsMonotone.norm_lpCLM_le_one`: a monotone stencil has operator norm at
  most $1$ on every $\ell^p(\mathbb{Z})$.
* `FiniteDifference.Stencil.apply_exp_eq_symbol_smul`: the mode $j \mapsto e^{ij\varphi}$ is an
  eigenvector with eigenvalue $\sigma(\varphi)$.
* `FiniteDifference.Stencil.norm_lpCLM_two_le_of_symbol_le`: the operator norm on
  $\ell^2(\mathbb{Z})$ is at most $\sup_\varphi |\sigma(\varphi)|$.
* `FiniteDifference.IsStableFamily.exists_norm_sub_le`: every member of a stable family satisfies
  the error bound of `FiniteDifference.norm_sub_le_of_stable` with a common constant.

## Implementation notes

* A stencil is `ℤ →₀ ℝ`. Its action is defined on grid functions with values in any real vector
  space, so that it also acts on the complex Fourier modes.
* Mathlib has no reindexing isometry of `lp` along a bijection of the index set. It is built here as
  `lp.compEquivₗᵢ`, and the shifts are the case of the bijection $j \mapsto j - s$ of $\mathbb{Z}$.
* `FiniteDifference.IsStableFamily` is stated for a family of normed spaces that depends on the
  index of the scheme, so that the periodic grids `Fin N` and the line `ℤ` are both instances.
-/

open Set Filter Topology Finset Function
open scoped ENNReal

/-! ### Reindexing and shifting $\ell^p$ -/

namespace Memℓp

variable {α β E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- Let $E$ be a normed group, let $p \in [0, \infty]$, and let $e \colon \alpha \to \beta$ be a
bijection. If $f \colon \beta \to E$ is in $\ell^p$, then $f \circ e$ is in $\ell^p$. -/
theorem comp_equiv {f : β → E} (hf : Memℓp f p) (e : α ≃ β) : Memℓp (f ∘ e) p := by
  rcases p.trichotomy with rfl | rfl | hp
  · exact memℓp_zero ((memℓp_zero_iff.1 hf).preimage e.injective.injOn)
  · refine memℓp_infty ?_
    have h := hf.bddAbove
    rwa [← e.surjective.range_comp fun i => ‖f i‖] at h
  · exact memℓp_gen ((e.summable_iff (f := fun i => ‖f i‖ ^ p.toReal)).2 (hf.summable hp))

end Memℓp

namespace lp

variable {α β E : Type*} [NormedAddCommGroup E] {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Reindexing $\ell^p$ along a bijection.** Let $E$ be a normed space over a normed field
$\mathbb{K}$, let $p \ge 1$, and let $e \colon \alpha \to \beta$ be a bijection. The map
$f \mapsto f \circ e$, that is $(f \circ e)(a) = f(e(a))$, is a linear isometric equivalence
from $\ell^p(\beta, E)$ onto $\ell^p(\alpha, E)$.

The $\ell^p$ norm is a sum or a supremum over the index set, and both are invariant under
bijections. -/
noncomputable def compEquivₗᵢ (e : α ≃ β) :
    lp (fun _ : β => E) p ≃ₗᵢ[𝕜] lp (fun _ : α => E) p where
  toFun f := ⟨(f : β → E) ∘ e, (lp.memℓp f).comp_equiv e⟩
  invFun g := ⟨(g : α → E) ∘ e.symm, (lp.memℓp g).comp_equiv e.symm⟩
  left_inv f := lp.ext (by ext b; simp)
  right_inv g := lp.ext (by ext a; simp)
  map_add' f g := rfl
  map_smul' c f := rfl
  norm_map' f := by
    rcases p.trichotomy with rfl | rfl | hp
    · exact absurd (Fact.out : (1 : ℝ≥0∞) ≤ 0) (by simp)
    · change ⨆ a, ‖f (e a)‖ = ⨆ b, ‖f b‖
      exact e.iSup_comp (g := fun b => ‖(f : β → E) b‖)
    · change ‖(⟨(f : β → E) ∘ e, (lp.memℓp f).comp_equiv e⟩ : lp (fun _ : α => E) p)‖ = ‖f‖
      rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
      congr 1
      exact e.tsum_eq fun b => ‖f b‖ ^ p.toReal

/-- The reindexing isometry `lp.compEquivₗᵢ` acts by precomposition: its value at $f$ is
$a \mapsto f(e(a))$. -/
@[simp]
theorem compEquivₗᵢ_apply (e : α ≃ β) (f : lp (fun _ : β => E) p) (a : α) :
    compEquivₗᵢ (𝕜 := 𝕜) e f a = f (e a) := rfl

/-- **Translation on $\ell^p(\mathbb{Z})$.** Let $E$ be a normed space, let $p \ge 1$, and let
$s \in \mathbb{Z}$. The shift $S_s$ with $(S_s u)_j = u_{j-s}$ is a linear isometric equivalence
of $\ell^p(\mathbb{Z}, E)$.

It is `lp.compEquivₗᵢ` for the bijection $j \mapsto j - s$ of $\mathbb{Z}$. -/
noncomputable def shiftₗᵢ (p : ℝ≥0∞) [Fact (1 ≤ p)] (s : ℤ) :
    lp (fun _ : ℤ => E) p ≃ₗᵢ[𝕜] lp (fun _ : ℤ => E) p :=
  compEquivₗᵢ (Equiv.subRight s)

/-- The shift acts by translation: $(S_s u)_j = u_{j-s}$. -/
@[simp]
theorem shiftₗᵢ_apply (s : ℤ) (u : lp (fun _ : ℤ => E) p) (j : ℤ) :
    shiftₗᵢ (𝕜 := 𝕜) p s u j = u (j - s) := rfl

end lp

namespace FiniteDifference

/-! ### Stencils and their action -/

/-- A **stencil** is a finitely supported family $(c_s)_{s \in \mathbb{Z}}$ of real weights on the
integer grid. The weight $c_s$ belongs to the neighbour $s$ steps to the left in the action
`FiniteDifference.Stencil.apply`. -/
abbrev Stencil := ℤ →₀ ℝ

namespace Stencil

variable {M : Type*} [AddCommMonoid M] [Module ℝ M]

/-- The **action of a stencil** $c$ on a grid function $u \colon \mathbb{Z} \to M$, where $M$ is a
real vector space, is the finite convolution
$$(cu)_j = \sum_s c_s u_{j-s}.$$
-/
noncomputable def apply (c : Stencil) (u : ℤ → M) : ℤ → M :=
  fun j => c.sum fun s a => a • u (j - s)

/-- The action of a stencil is the finite sum $(cu)_j = \sum_{s \in \operatorname{supp} c} c_s
u_{j-s}$ over its support. -/
theorem apply_apply (c : Stencil) (u : ℤ → M) (j : ℤ) :
    apply c u j = ∑ s ∈ c.support, c s • u (j - s) := rfl

/-- The action of a stencil is additive: $c(u + v) = cu + cv$. -/
theorem apply_add (c : Stencil) (u v : ℤ → M) : apply c (u + v) = apply c u + apply c v := by
  ext j
  simp [apply_apply, smul_add, Finset.sum_add_distrib]

/-- The action of a stencil commutes with real scalars: $c(ru) = r (cu)$. -/
theorem apply_smul (c : Stencil) (r : ℝ) (u : ℤ → M) : apply c (r • u) = r • apply c u := by
  ext j
  simp [apply_apply, Finset.smul_sum, smul_comm r]

/-- The action of a stencil $c$ as a real linear map $u \mapsto cu$ on the grid functions
$\mathbb{Z} \to M$. -/
noncomputable def applyₗ (c : Stencil) : (ℤ → M) →ₗ[ℝ] (ℤ → M) where
  toFun := apply c
  map_add' := apply_add c
  map_smul' := apply_smul c

/-- The linear map `FiniteDifference.Stencil.applyₗ` of a stencil acts by
`FiniteDifference.Stencil.apply`. -/
@[simp]
theorem applyₗ_apply (c : Stencil) (u : ℤ → M) : applyₗ c u = apply c u := rfl

/-- The action of a stencil reads a grid function only through the support. Let $c$ be a stencil,
let $j \in \mathbb{Z}$, and let $u, v \colon \mathbb{Z} \to M$ satisfy $u_{j-s} = v_{j-s}$ for
every $s$ in the support of $c$. Then $(cu)_j = (cv)_j$. -/
theorem apply_congr {c : Stencil} {u v : ℤ → M} {j : ℤ}
    (h : ∀ s ∈ c.support, u (j - s) = v (j - s)) : apply c u j = apply c v j :=
  Finset.sum_congr rfl fun s hs => by dsimp only; rw [h s hs]

/-- The **three-point stencil** with weights $c_-, c_0, c_+ \in \mathbb{R}$: the stencil with
$c_1 = c_-$, $c_0 = c_0$ and $c_{-1} = c_+$, which sends $u$ to
$j \mapsto c_- u_{j-1} + c_0 u_j + c_+ u_{j+1}$. -/
noncomputable def threePoint (cm c0 cp : ℝ) : Stencil :=
  Finsupp.single 1 cm + Finsupp.single 0 c0 + Finsupp.single (-1) cp

/-- The action of the three-point stencil: for $c_-, c_0, c_+ \in \mathbb{R}$, every grid function
$u$ and every $j \in \mathbb{Z}$,
$$(cu)_j = c_- u_{j-1} + c_0 u_j + c_+ u_{j+1}.$$
-/
theorem threePoint_apply (cm c0 cp : ℝ) (u : ℤ → M) (j : ℤ) :
    apply (threePoint cm c0 cp) u j = cm • u (j - 1) + c0 • u j + cp • u (j + 1) := by
  simp only [apply, threePoint]
  rw [Finsupp.sum_add_index' (h := fun s a => a • u (j - s)) (fun _ => zero_smul ℝ _)
      (fun _ _ _ => add_smul _ _ _),
    Finsupp.sum_add_index' (h := fun s a => a • u (j - s)) (fun _ => zero_smul ℝ _)
      (fun _ _ _ => add_smul _ _ _),
    Finsupp.sum_single_index (h := fun s a => a • u (j - s)) (zero_smul ℝ _),
    Finsupp.sum_single_index (h := fun s a => a • u (j - s)) (zero_smul ℝ _),
    Finsupp.sum_single_index (h := fun s a => a • u (j - s)) (zero_smul ℝ _), sub_zero,
    sub_neg_eq_add]

/-- The support of a three-point stencil lies in $\{-1, 0, 1\}$. -/
theorem support_threePoint_subset (cm c0 cp : ℝ) :
    (threePoint cm c0 cp).support ⊆ {1, 0, -1} := by
  refine (Finsupp.support_add.trans (union_subset_union Finsupp.support_add le_rfl)).trans ?_
  refine union_subset (union_subset ?_ ?_) ?_ <;>
    exact Finsupp.support_single_subset.trans (by simp)

/-- The weights of the three-point stencil with weights $c_-, c_0, c_+$ sum to $c_- + c_0 + c_+$. -/
theorem threePoint_sum (cm c0 cp : ℝ) :
    (threePoint cm c0 cp).sum (fun _ a => a) = cm + c0 + cp := by
  simp only [threePoint]
  rw [Finsupp.sum_add_index' (h := fun _ a => a) (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_add_index' (h := fun _ a => a) (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index (h := fun _ a => a) rfl,
    Finsupp.sum_single_index (h := fun _ a => a) rfl,
    Finsupp.sum_single_index (h := fun _ a => a) rfl]

/-! ### Conservative form -/

/-- The **conservative form** of a linear numerical flux. For
$\lambda, \alpha, \beta \in \mathbb{R}$, `FiniteDifference.Stencil.ofFlux` is the three-point
stencil with weights $c_- = \lambda \alpha$, $c_0 = 1 - \lambda (\alpha - \beta)$ and
$c_+ = -\lambda \beta$. It sends $u$ to
$$j \mapsto u_j - \lambda \bigl( h(u_j, u_{j+1}) - h(u_{j-1}, u_j) \bigr), \qquad h(u, v) =
  \alpha u + \beta v,$$
which is the conservative form (13.36) of [quarteroni2000numerical]. -/
noncomputable def ofFlux (lam α β : ℝ) : Stencil :=
  threePoint (lam * α) (1 - lam * (α - β)) (-(lam * β))

/-- The action of `FiniteDifference.Stencil.ofFlux` is the conservative form (13.36) of
[quarteroni2000numerical]: for $\lambda, \alpha, \beta \in \mathbb{R}$ and
$u \colon \mathbb{Z} \to \mathbb{R}$,
$$(cu)_j = u_j - \lambda \bigl( (\alpha u_j + \beta u_{j+1}) - (\alpha u_{j-1} + \beta u_j)
  \bigr).$$
-/
theorem ofFlux_apply (lam α β : ℝ) (u : ℤ → ℝ) (j : ℤ) :
    apply (ofFlux lam α β) u j
      = u j - lam * ((α * u j + β * u (j + 1)) - (α * u (j - 1) + β * u j)) := by
  rw [ofFlux, threePoint_apply]
  simp only [smul_eq_mul]
  ring

end Stencil

/-- **A step in conservative form** ([quarteroni2000numerical], (13.36)). Let
$\lambda \in \mathbb{R}$ and let $h \colon \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ be a
numerical flux. A map $Q$ on real grid functions is in **conservative form** with $\lambda$ and
$h$ if, for every $u$ and every $j$,
$$(Qu)_j = u_j - \lambda \bigl( h(u_j, u_{j+1}) - h(u_{j-1}, u_j) \bigr).$$

The scheme advances by the difference of the numerical flux across the two half-cells.
[quarteroni2000numerical] write every explicit scheme for a conservation law $u_t + f(u)_x = 0$
in this form. -/
def IsConservativeForm (lam : ℝ) (h : ℝ → ℝ → ℝ) (step : (ℤ → ℝ) → (ℤ → ℝ)) : Prop :=
  ∀ u j, step u j = u j - lam * (h (u j) (u (j + 1)) - h (u (j - 1)) (u j))

namespace Stencil

/-- Let $\lambda, \alpha, \beta \in \mathbb{R}$. A map $Q$ on real grid functions is in conservative
form with $\lambda$ and the linear flux $h(u, v) = \alpha u + \beta v$ if and only if $Q$ is the
action of the stencil `FiniteDifference.Stencil.ofFlux` with parameters
$\lambda, \alpha, \beta$. -/
theorem isConservativeForm_iff {lam α β : ℝ} {step : (ℤ → ℝ) → (ℤ → ℝ)} :
    IsConservativeForm lam (fun u v => α * u + β * v) step ↔ step = apply (ofFlux lam α β) := by
  constructor
  · intro h
    funext u j
    rw [ofFlux_apply, h u j]
  · rintro rfl u j
    exact ofFlux_apply lam α β u j

/-- For $\lambda, \alpha, \beta \in \mathbb{R}$, the action of `FiniteDifference.Stencil.ofFlux` is
in conservative form with $\lambda$ and the flux $h(u, v) = \alpha u + \beta v$. -/
theorem isConservativeForm_ofFlux (lam α β : ℝ) :
    IsConservativeForm lam (fun u v => α * u + β * v) (apply (ofFlux lam α β)) :=
  isConservativeForm_iff.2 rfl

/-! ### Finite speed of propagation -/

variable {M : Type*} [AddCommMonoid M] [Module ℝ M]

/-- **Finite speed of propagation**, the numerical domain of dependence ([quarteroni2000numerical],
§13.8.3). Let $c$ be a stencil and let $r \in \mathbb{Z}$ with $|s| \le r$ for every $s$ in the
support of $c$. Let $n \in \mathbb{N}$, let $j \in \mathbb{Z}$, and let the grid functions
$u, v \colon \mathbb{Z} \to M$ satisfy $u_i = v_i$ whenever $|i - j| \le nr$. Then the $n$-fold
applications of $c$ agree at $j$:
$$(c^n u)_j = (c^n v)_j.$$
-/
theorem iterate_apply_congr_of_eqOn {c : Stencil} {r : ℤ} (hr : ∀ s ∈ c.support, |s| ≤ r)
    (n : ℕ) {u v : ℤ → M} {j : ℤ} (huv : ∀ i, |i - j| ≤ n * r → u i = v i) :
    (apply c)^[n] u j = (apply c)^[n] v j := by
  induction n generalizing j with
  | zero => exact huv j (by simp)
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    refine apply_congr fun s hs => ih fun i hi => huv i ?_
    have h1 := hr s hs
    have h2 : |i - j| ≤ |i - (j - s)| + |s| := by
      calc |i - j| = |(i - (j - s)) + (-s)| := by ring_nf
        _ ≤ |i - (j - s)| + |-s| := abs_add_le _ _
        _ = |i - (j - s)| + |s| := by rw [abs_neg]
    push_cast
    nlinarith

/-! ### Monotone stencils and the discrete maximum principle -/

/-- A **monotone stencil** has nonnegative weights with sum $1$: $c_s \ge 0$ for every $s$, and
$\sum_s c_s = 1$. Each value of the scheme is then a convex average of neighbouring values. -/
def IsMonotone (c : Stencil) : Prop := (∀ s, 0 ≤ c s) ∧ c.sum (fun _ a => a) = 1

/-- The weights of a monotone stencil are nonnegative: $c_s \ge 0$. -/
theorem IsMonotone.nonneg {c : Stencil} (hc : c.IsMonotone) (s : ℤ) : 0 ≤ c s := hc.1 s

/-- The weights of a monotone stencil sum to $1$: $\sum_{s \in \operatorname{supp} c} c_s = 1$. -/
theorem IsMonotone.sum_eq_one {c : Stencil} (hc : c.IsMonotone) : ∑ s ∈ c.support, c s = 1 := hc.2

/-- **The discrete maximum principle**, upper bound. Let $c$ be a monotone stencil, let
$B \in \mathbb{R}$, and let $u \colon \mathbb{Z} \to \mathbb{R}$ satisfy $u_i \le B$ for every
$i$. Then $(cu)_j \le B$ for every $j \in \mathbb{Z}$. -/
theorem IsMonotone.apply_le {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ} {B : ℝ}
    (hu : ∀ i, u i ≤ B) (j : ℤ) : apply c u j ≤ B := by
  rw [apply_apply]
  calc ∑ s ∈ c.support, c s • u (j - s) ≤ ∑ s ∈ c.support, c s * B :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hu _) (hc.nonneg s)
    _ = B := by rw [← Finset.sum_mul, hc.sum_eq_one, one_mul]

/-- **The discrete maximum principle**, lower bound. Let $c$ be a monotone stencil, let
$B \in \mathbb{R}$, and let $u \colon \mathbb{Z} \to \mathbb{R}$ satisfy $B \le u_i$ for every
$i$. Then $B \le (cu)_j$ for every $j \in \mathbb{Z}$. -/
theorem IsMonotone.le_apply {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ} {B : ℝ}
    (hu : ∀ i, B ≤ u i) (j : ℤ) : B ≤ apply c u j := by
  rw [apply_apply]
  calc B = ∑ s ∈ c.support, c s * B := by rw [← Finset.sum_mul, hc.sum_eq_one, one_mul]
    _ ≤ ∑ s ∈ c.support, c s • u (j - s) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hu _) (hc.nonneg s)

/-- Iteration of a monotone stencil keeps an upper bound. Let $c$ be a monotone stencil, let
$B \in \mathbb{R}$, and let $u \colon \mathbb{Z} \to \mathbb{R}$ satisfy $u_i \le B$ for every
$i$. Then $(c^n u)_j \le B$ for every $n \in \mathbb{N}$ and every $j \in \mathbb{Z}$. -/
theorem IsMonotone.iterate_apply_le {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ} {B : ℝ}
    (hu : ∀ i, u i ≤ B) (n : ℕ) (j : ℤ) : (apply c)^[n] u j ≤ B := by
  induction n generalizing j with
  | zero => exact hu j
  | succ n ih => rw [iterate_succ_apply']; exact hc.apply_le ih j

/-- Iteration of a monotone stencil keeps a lower bound. Let $c$ be a monotone stencil, let
$B \in \mathbb{R}$, and let $u \colon \mathbb{Z} \to \mathbb{R}$ satisfy $B \le u_i$ for every
$i$. Then $B \le (c^n u)_j$ for every $n \in \mathbb{N}$ and every $j \in \mathbb{Z}$. -/
theorem IsMonotone.le_iterate_apply {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ} {B : ℝ}
    (hu : ∀ i, B ≤ u i) (n : ℕ) (j : ℤ) : B ≤ (apply c)^[n] u j := by
  induction n generalizing j with
  | zero => exact hu j
  | succ n ih => rw [iterate_succ_apply']; exact hc.le_apply ih j

/-- **The discrete maximum principle** ([quarteroni2000numerical], (13.53)). Let $c$ be a monotone
stencil and let $u \colon \mathbb{Z} \to \mathbb{R}$ be bounded above. Then for every
$j \in \mathbb{Z}$,
$$(cu)_j \le \sup_i u_i.$$
-/
theorem IsMonotone.apply_le_iSup {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ}
    (hu : BddAbove (range u)) (j : ℤ) : apply c u j ≤ ⨆ i, u i :=
  hc.apply_le (fun i => le_ciSup hu i) j

/-- **The discrete maximum principle**, lower half. Let $c$ be a monotone stencil and let
$u \colon \mathbb{Z} \to \mathbb{R}$ be bounded below. Then for every $j \in \mathbb{Z}$,
$$\inf_i u_i \le (cu)_j.$$
-/
theorem IsMonotone.iInf_le_apply {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ}
    (hu : BddBelow (range u)) (j : ℤ) : ⨅ i, u i ≤ apply c u j :=
  hc.le_apply (fun i => ciInf_le hu i) j

/-- The iterated discrete maximum principle. Let $c$ be a monotone stencil and let
$u \colon \mathbb{Z} \to \mathbb{R}$ be bounded above. Then for every $n \in \mathbb{N}$ and
every $j \in \mathbb{Z}$,
$$(c^n u)_j \le \sup_i u_i.$$

Together with the lower half, this says that the supremum norm of the solution of a monotone
scheme never increases. -/
theorem IsMonotone.iterate_apply_le_iSup {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ}
    (hu : BddAbove (range u)) (n : ℕ) (j : ℤ) : (apply c)^[n] u j ≤ ⨆ i, u i :=
  hc.iterate_apply_le (fun i => le_ciSup hu i) n j

/-- The iterated discrete maximum principle, lower half. Let $c$ be a monotone stencil and let
$u \colon \mathbb{Z} \to \mathbb{R}$ be bounded below. Then for every $n \in \mathbb{N}$ and
every $j \in \mathbb{Z}$,
$$\inf_i u_i \le (c^n u)_j.$$
-/
theorem IsMonotone.iInf_le_iterate_apply {c : Stencil} (hc : c.IsMonotone) {u : ℤ → ℝ}
    (hu : BddBelow (range u)) (n : ℕ) (j : ℤ) : ⨅ i, u i ≤ (apply c)^[n] u j :=
  hc.le_iterate_apply (fun i => ciInf_le hu i) n j

/-! ### The stencil as a bounded operator on $\ell^p(\mathbb{Z})$ -/

section Lp

variable {p : ℝ≥0∞}

/-- The action of a stencil is the finite sum of the shifted grid functions, weighted by the
coefficients: $cu = \sum_{s \in \operatorname{supp} c} c_s \, u(\cdot - s)$. -/
theorem apply_eq_sum (c : Stencil) (u : ℤ → M) :
    apply c u = fun j => ∑ s ∈ c.support, (c s • (u ∘ Equiv.subRight s)) j := by
  ext j
  rw [apply_apply]
  rfl

/-- A stencil maps $\ell^p$ to $\ell^p$. Let $c$ be a stencil, let $p \in [0, \infty]$, and let
$u \colon \mathbb{Z} \to \mathbb{R}$ be in $\ell^p$. Then $cu$ is in $\ell^p$.

The proof writes $cu$ as a finite linear combination of shifts of $u$. -/
theorem memℓp_apply (c : Stencil) {u : ℤ → ℝ} (hu : Memℓp u p) : Memℓp (apply c u) p := by
  rw [apply_eq_sum]
  exact Memℓp.finsetSum c.support (f := fun s => c s • (u ∘ Equiv.subRight s))
    fun s _ => (hu.comp_equiv (Equiv.subRight s)).const_smul (c s)

variable [Fact (1 ≤ p)]

/-- **The stencil as a bounded operator on $\ell^p(\mathbb{Z})$.** For a stencil $c$ and $p \ge 1$,
`FiniteDifference.Stencil.lpCLM` is the continuous linear operator
$$\sum_{s \in \operatorname{supp} c} c_s S_s$$
on the real space $\ell^p(\mathbb{Z})$, where $S_s$ is the shift `lp.shiftₗᵢ` with
$(S_s u)_j = u_{j-s}$. -/
noncomputable def lpCLM (c : Stencil) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    lp (fun _ : ℤ => ℝ) p →L[ℝ] lp (fun _ : ℤ => ℝ) p :=
  ∑ s ∈ c.support, c s • (lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) p s).toLinearIsometry.toContinuousLinearMap

/-- **The operator of a stencil acts by the stencil.** For a stencil $c$, $p \ge 1$ and
$u \in \ell^p(\mathbb{Z})$, the image of $u$ under `FiniteDifference.Stencil.lpCLM` is the grid
function $cu$. -/
theorem coeFn_lpCLM (c : Stencil) (u : lp (fun _ : ℤ => ℝ) p) : ⇑(lpCLM c p u) = apply c u := by
  ext j
  rw [lpCLM, _root_.sum_apply, lp.coeFn_sum, Finset.sum_apply, apply_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_apply, lp.coeFn_smul, Pi.smul_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, lp.shiftₗᵢ_apply]

/-- The operator of a stencil acts by the stencil at each point: the image of $u$ under
`FiniteDifference.Stencil.lpCLM` has the value $(cu)_j$ at $j$. -/
theorem lpCLM_apply (c : Stencil) (u : lp (fun _ : ℤ => ℝ) p) (j : ℤ) :
    lpCLM c p u j = apply c u j := by
  rw [coeFn_lpCLM]

/-- **Young's inequality for a finitely supported kernel on $\mathbb{Z}$.** For a stencil $c$ and
$p \ge 1$, the operator norm of $c$ on $\ell^p(\mathbb{Z})$ satisfies
$$\|c\|_{\ell^p \to \ell^p} \le \sum_{s \in \operatorname{supp} c} |c_s|.$$

The proof is the triangle inequality for the sum of shifts, each of which is an isometry. -/
theorem norm_lpCLM_le (c : Stencil) : ‖lpCLM c p‖ ≤ ∑ s ∈ c.support, |c s| := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (lp.shiftₗᵢ (E := ℝ) (𝕜 := ℝ) p s).toLinearIsometry.norm_toContinuousLinearMap_le

/-- **Monotone stencils are nonexpansive in every $\ell^p$.** For a monotone stencil $c$ and
$p \ge 1$, the operator norm of $c$ on $\ell^p(\mathbb{Z})$ is at most $1$.

This is the $\|\cdot\|_{\Delta, 1}$ stability of the upwind and Lax–Friedrichs schemes under the
CFL condition of [quarteroni2000numerical], §13.8.3, with constant $1$. -/
theorem IsMonotone.norm_lpCLM_le_one {c : Stencil} (hc : c.IsMonotone) : ‖lpCLM c p‖ ≤ 1 := by
  refine (norm_lpCLM_le c).trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl fun s _ => abs_of_nonneg (hc.nonneg s)]
  exact hc.sum_eq_one

/-- **Monotone stencils are nonexpansive.** For a monotone stencil $c$, $p \ge 1$ and
$u \in \ell^p(\mathbb{Z})$,
$$\|cu\|_{\ell^p} \le \|u\|_{\ell^p}.$$
-/
theorem IsMonotone.norm_lpCLM_apply_le {c : Stencil} (hc : c.IsMonotone)
    (u : lp (fun _ : ℤ => ℝ) p) : ‖lpCLM c p u‖ ≤ ‖u‖ := by
  have := (lpCLM c p).le_of_opNorm_le hc.norm_lpCLM_le_one u
  rwa [one_mul] at this

end Lp

/-! ### The symbol -/

section Symbol

open Complex

/-- **The symbol of a stencil.** For a stencil $c$ and $\varphi \in \mathbb{R}$, the symbol is
$$\sigma(\varphi) = \sum_{s \in \operatorname{supp} c} c_s e^{-is\varphi} \in \mathbb{C}.$$
It is the amplification factor of the Fourier mode $j \mapsto e^{ij\varphi}$ under the stencil. -/
noncomputable def symbol (c : Stencil) (φ : ℝ) : ℂ :=
  ∑ s ∈ c.support, (c s : ℂ) * exp (-(I * s * φ))

/-- **The Fourier modes are eigenvectors of every stencil.** For a stencil $c$ and
$\varphi \in \mathbb{R}$, the complex grid function $e_\varphi \colon j \mapsto e^{ij\varphi}$
satisfies
$$c e_\varphi = \sigma(\varphi) e_\varphi,$$
where $\sigma$ is the symbol of $c$. -/
theorem apply_exp_eq_symbol_smul (c : Stencil) (φ : ℝ) :
    apply c (fun j : ℤ => exp (I * j * φ)) = symbol c φ • fun j : ℤ => exp (I * j * φ) := by
  ext j
  rw [apply_apply, Pi.smul_apply, symbol, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Complex.real_smul, mul_assoc (c s : ℂ), ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The symbol of a stencil is $2\pi$-periodic: $\sigma(\varphi + 2\pi) = \sigma(\varphi)$. -/
theorem symbol_add_two_pi (c : Stencil) (φ : ℝ) : symbol c (φ + 2 * Real.pi) = symbol c φ := by
  unfold symbol
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  rw [show -(I * s * ((φ + 2 * Real.pi : ℝ) : ℂ)) = -(I * s * φ) + (-s : ℤ) * (2 * Real.pi * I) by
    push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The symbol of the three-point stencil with weights $c_-, c_0, c_+$ is
$$\sigma(\varphi) = c_0 + c_- e^{-i\varphi} + c_+ e^{i\varphi}.$$
-/
theorem symbol_threePoint (cm c0 cp : ℝ) (φ : ℝ) :
    symbol (threePoint cm c0 cp) φ = c0 + cm * exp (-(I * φ)) + cp * exp (I * φ) := by
  have h := congrFun (apply_exp_eq_symbol_smul (threePoint cm c0 cp) φ) 0
  rw [threePoint_apply, Pi.smul_apply, smul_eq_mul] at h
  simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, zero_sub, zero_add,
    Int.cast_neg, Int.cast_one, Complex.real_smul] at h
  rw [← h]
  ring_nf

end Symbol

/-!
### The $\ell^2$ bound from the symbol

The operator norm of a stencil on $\ell^2(\mathbb{Z})$ is at most the supremum of the modulus of its
symbol. This is the whole-line counterpart of the von Neumann analysis on a periodic grid. The proof
is Parseval's identity on $\mathbb{Z}$ for trigonometric polynomials (`integral_norm_sq_trigPoly`).
That identity needs only the orthogonality of the exponentials over one period, $\int_0^{2\pi}
e^{ik\varphi} \, d\varphi = 2\pi \delta_{k0}$ (`integral_exp_I_int_mul`), together with the fact
that the symbol of a convolution is the product of the symbols. The bound for a finitely supported
grid function extends to all of $\ell^2$ by summing over larger and larger finite sets of indices.
-/

section SymbolLTwo

open Complex

/-- Reindexing of a shifted sum: if $A$ contains $s + \operatorname{supp} w$, then $\sum_{j \in A}
w_{j-s} e^{-ij\varphi} = \sum_{t \in \operatorname{supp} w} w_t e^{-i(s+t)\varphi}$. -/
private theorem sum_shift_eq (s : ℤ) (A : Finset ℤ) (w : ℤ →₀ ℝ)
    (hA : ∀ t ∈ w.support, s + t ∈ A) (φ : ℝ) :
    (∑ j ∈ A, ((w (j - s) : ℝ) : ℂ) * exp (-(I * j * φ)))
      = ∑ t ∈ w.support, ((w t : ℝ) : ℂ) * exp (-(I * ((s : ℂ) + t) * φ)) := by
  classical
  have hmap : (∑ t ∈ w.support, ((w t : ℝ) : ℂ) * exp (-(I * ((s : ℂ) + t) * φ)))
      = ∑ j ∈ w.support.map ⟨(s + ·), add_right_injective s⟩,
          ((w (j - s) : ℝ) : ℂ) * exp (-(I * j * φ)) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Function.Embedding.coeFn_mk, add_sub_cancel_left]
    push_cast
    ring_nf
  rw [hmap]
  refine (Finset.sum_subset (fun j hj => ?_) fun j hjA hj => ?_).symm
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_map.1 hj
    exact hA t ht
  · have hw : w (j - s) = 0 := by
      by_contra hne
      refine hj (Finset.mem_map.2 ⟨j - s, Finsupp.mem_support_iff.2 hne, ?_⟩)
      simp only [Function.Embedding.coeFn_mk]
      ring
    rw [hw]
    simp

/-- The symbol of a convolution is the product of the symbols: the trigonometric polynomial of $cw$
is $\sigma(\varphi)$ times the trigonometric polynomial of $w$. -/
private theorem sum_apply_mul_exp (c : Stencil) (w : ℤ →₀ ℝ) (A : Finset ℤ)
    (hA : ∀ s ∈ c.support, ∀ t ∈ w.support, s + t ∈ A) (φ : ℝ) :
    (∑ j ∈ A, ((apply c (w : ℤ → ℝ) j : ℝ) : ℂ) * exp (-(I * j * φ)))
      = symbol c φ * ∑ t ∈ w.support, ((w t : ℝ) : ℂ) * exp (-(I * t * φ)) := by
  have hlhs : (∑ j ∈ A, ((apply c (w : ℤ → ℝ) j : ℝ) : ℂ) * exp (-(I * j * φ)))
      = ∑ s ∈ c.support, ∑ j ∈ A,
          (c s : ℂ) * (((w (j - s) : ℝ) : ℂ) * exp (-(I * j * φ))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [apply_apply]
    push_cast [smul_eq_mul]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hlhs, symbol, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [← Finset.mul_sum, sum_shift_eq s A w (fun t ht => hA s hs t ht) φ, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show (-(I * ((s : ℂ) + t) * φ)) = -(I * s * φ) + -(I * t * φ) by ring, Complex.exp_add]
  ring

/-- The $\ell^2$ bound for a finitely supported grid function $w$: if $|\sigma(\varphi)| \le \rho$
for every $\varphi$, then $\sum_{j \in A} (cw)_j^2 \le \rho^2 \sum_t w_t^2$. -/
private theorem sum_sq_apply_le (c : Stencil) {ρ : ℝ} (hρ : ∀ φ : ℝ, ‖symbol c φ‖ ≤ ρ)
    (w : ℤ →₀ ℝ) (A : Finset ℤ) (hA : ∀ s ∈ c.support, ∀ t ∈ w.support, s + t ∈ A) :
    (∑ j ∈ A, apply c (w : ℤ → ℝ) j ^ 2) ≤ ρ ^ 2 * ∑ t ∈ w.support, w t ^ 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set U : ℝ → ℂ := fun φ => ∑ t ∈ w.support, ((w t : ℝ) : ℂ) * exp (-(I * t * φ)) with hU
  have hleft := integral_norm_sq_trigPoly A fun j => ((apply c (w : ℤ → ℝ) j : ℝ) : ℂ)
  have hright := integral_norm_sq_trigPoly w.support fun t => ((w t : ℝ) : ℂ)
  have hmono : (∫ φ in (0 : ℝ)..(2 * Real.pi),
      ‖∑ j ∈ A, ((apply c (w : ℤ → ℝ) j : ℝ) : ℂ) * exp (-(I * j * φ))‖ ^ 2)
      ≤ ρ ^ 2 * ∫ φ in (0 : ℝ)..(2 * Real.pi), ‖U φ‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hpi.le
      ((by fun_prop : Continuous fun φ : ℝ =>
        ‖∑ j ∈ A, ((apply c (w : ℤ → ℝ) j : ℝ) : ℂ) * exp (-(I * j * φ))‖ ^ 2).intervalIntegrable
          _ _)
      ((by fun_prop : Continuous fun φ : ℝ => ρ ^ 2 * ‖U φ‖ ^ 2).intervalIntegrable _ _)
      fun φ _ => ?_
    rw [sum_apply_mul_exp c w A hA φ, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hρ φ) 2) (by positivity)
  rw [hleft, hright] at hmono
  have hcast : ∀ x : ℝ, ‖((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hcast] at hmono
  nlinarith [hmono, Real.pi_pos]

/-- **The $\ell^2$ operator norm of a stencil is bounded by the supremum of its symbol.** Let $c$ be
a stencil and let $\rho \in \mathbb{R}$ with $|\sigma(\varphi)| \le \rho$ for every
$\varphi \in \mathbb{R}$. Then the operator norm of $c$ on $\ell^2(\mathbb{Z})$ satisfies
$$\|c\|_{\ell^2 \to \ell^2} \le \rho.$$

This sharp $\ell^2$ bound replaces the bound $\sum_s |c_s|$ of
`FiniteDifference.Stencil.norm_lpCLM_le`. It is the whole-line counterpart of the periodic von
Neumann criterion of `Numlib.FiniteDifference.VonNeumann`. The proof applies Parseval's identity
$\int_0^{2\pi} |\sum_s v_s e^{-is\varphi}|^2 \, d\varphi = 2\pi \sum_s |v_s|^2$ for
trigonometric polynomials to a finitely supported truncation of the grid function and to its
image, and then passes to the limit over the finite sets of indices. -/
theorem norm_lpCLM_two_le_of_symbol_le (c : Stencil) {ρ : ℝ} (hρ : ∀ φ : ℝ, ‖symbol c φ‖ ≤ ρ) :
    ‖lpCLM c 2‖ ≤ ρ := by
  classical
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (hρ 0)
  refine ContinuousLinearMap.opNorm_le_bound _ hρ0 fun u => ?_
  have htoReal : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  have hnorm_sq : ∀ v : lp (fun _ : ℤ => ℝ) 2, ‖v‖ ^ 2 = ∑' j : ℤ, (v j) ^ 2 := by
    intro v
    have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by rw [htoReal]; norm_num) v
    rw [htoReal] at h
    have hr : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := fun x => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [hr, Real.norm_eq_abs, sq_abs] at h
    exact h
  have hsummable : Summable fun j : ℤ => (lpCLM c 2 u j) ^ 2 := by
    have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by rw [htoReal]; norm_num) (lpCLM c 2 u)
    rw [htoReal] at h
    have hr : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := fun x => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [hr, Real.norm_eq_abs, sq_abs] at h
    exact h.summable
  have hkey : ∀ B : Finset ℤ, (∑ j ∈ B, (lpCLM c 2 u j) ^ 2) ≤ ρ ^ 2 * ‖u‖ ^ 2 := by
    intro B
    -- the finitely supported truncation of `u` that `(c ⋆ u)` sees on `B`
    set A : Finset ℤ := Finset.image₂ (fun j s => j - s) B c.support with hA
    set w : ℤ →₀ ℝ := Finsupp.onFinset A (fun t => if t ∈ A then (u : ℤ → ℝ) t else 0)
      (fun t ht => by by_contra hnot; rw [ite_eq_right hnot] at ht; exact ht rfl) with hw
    have hwA : ∀ t ∈ A, w t = (u : ℤ → ℝ) t := by
      intro t ht
      simp only [hw, Finsupp.onFinset_apply, ite_eq_left ht]
    have hwsupp : w.support ⊆ A := Finsupp.support_onFinset_subset
    have hagree : ∀ j ∈ B, apply c (w : ℤ → ℝ) j = apply c (u : ℤ → ℝ) j := by
      intro j hj
      rw [apply_apply, apply_apply]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hwA (j - s) (Finset.mem_image₂.2 ⟨j, hj, s, hs, rfl⟩)]
    set A₂ : Finset ℤ := B ∪ Finset.image₂ (fun s t => s + t) c.support w.support with hA₂
    have hAA : ∀ s ∈ c.support, ∀ t ∈ w.support, s + t ∈ A₂ := fun s hs t ht =>
      Finset.mem_union_right _ (Finset.mem_image₂.2 ⟨s, hs, t, ht, rfl⟩)
    have hsub : B ⊆ A₂ := Finset.subset_union_left
    calc (∑ j ∈ B, (lpCLM c 2 u j) ^ 2)
        = ∑ j ∈ B, apply c (w : ℤ → ℝ) j ^ 2 := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [lpCLM_apply, hagree j hj]
      _ ≤ ∑ j ∈ A₂, apply c (w : ℤ → ℝ) j ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => sq_nonneg _
      _ ≤ ρ ^ 2 * ∑ t ∈ w.support, w t ^ 2 := sum_sq_apply_le c hρ w A₂ hAA
      _ ≤ ρ ^ 2 * ‖u‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg ρ)
          rw [hnorm_sq u]
          have hsum : Summable fun j : ℤ => ((u : ℤ → ℝ) j) ^ 2 := by
            have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by rw [htoReal]; norm_num) u
            rw [htoReal] at h
            have hr : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := fun x => by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            simp only [hr, Real.norm_eq_abs, sq_abs] at h
            exact h.summable
          refine le_trans (le_of_eq (Finset.sum_congr rfl fun t ht => ?_))
            (hsum.sum_le_tsum w.support fun j _ => sq_nonneg _)
          rw [hwA t (hwsupp ht)]
  have hle : ‖lpCLM c 2 u‖ ^ 2 ≤ (ρ * ‖u‖) ^ 2 := by
    rw [hnorm_sq (lpCLM c 2 u), mul_pow]
    exact hsummable.tsum_le_of_sum_le hkey
  nlinarith [norm_nonneg (lpCLM c 2 u), mul_nonneg hρ0 (norm_nonneg u), hle]

end SymbolLTwo

end Stencil

/-! ### Discrete norms and stable families -/

/-- **The discrete $L^p$ norms** of [quarteroni2000numerical], (13.47). For $p \in [0, \infty]$, a
mesh size $\Delta x$ and $v \in \ell^p(\mathbb{Z})$,
$$\|v\|_{\Delta, p} = \Delta x^{1/p} \|v\|_{\ell^p}.$$
For $0 < p < \infty$ and $\Delta x \ge 0$ this is $(\Delta x \sum_j |v_j|^p)^{1/p}$, and for
$p = \infty$ it is $\sup_j |v_j|$.

The exponent is $1/p$ as a real number, which is $0$ for $p = \infty$ and for $p = 0$, so the
factor is then $1$. For $p = 0$ the value is the Mathlib norm of `lp` at $p = 0$, the number of
nonzero entries of $v$. -/
noncomputable def discreteNorm (p : ℝ≥0∞) (Δx : ℝ) (v : lp (fun _ : ℤ => ℝ) p) : ℝ :=
  Δx ^ (1 / p).toReal * ‖v‖

/-- The discrete maximum norm is the supremum norm: $\|v\|_{\Delta, \infty} = \|v\|_{\ell^\infty}$
for every $\Delta x$. -/
theorem discreteNorm_top (Δx : ℝ) (v : lp (fun _ : ℤ => ℝ) ∞) : discreteNorm ∞ Δx v = ‖v‖ := by
  simp [discreteNorm]

/-- The discrete $L^2$ norm: for $\Delta x \ge 0$ and $v \in \ell^2(\mathbb{Z})$, $\|v\|_{\Delta,
2} = \sqrt{\Delta x \sum_j v_j^2}$. -/
theorem discreteNorm_two_eq_sqrt {Δx : ℝ} (hΔx : 0 ≤ Δx) (v : lp (fun _ : ℤ => ℝ) 2) :
    discreteNorm 2 Δx v = √(Δx * ∑' j, v j ^ 2) := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hsum : ∀ j, ‖v j‖ ^ (2 : ℝ) = v j ^ 2 := fun j => by
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [discreteNorm, lp.norm_eq_tsum_rpow h2, Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, one_div, ENNReal.toReal_inv, hsum]
  rw [← Real.mul_rpow hΔx (tsum_nonneg fun j => sq_nonneg _)]

/-- The discrete $L^1$ norm: for every $\Delta x$ and $v \in \ell^1(\mathbb{Z})$,
$\|v\|_{\Delta, 1} = \Delta x \sum_j |v_j|$. -/
theorem discreteNorm_one (Δx : ℝ) (v : lp (fun _ : ℤ => ℝ) 1) :
    discreteNorm 1 Δx v = Δx * ∑' j, |v j| := by
  have h1 : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num
  rw [discreteNorm, lp.norm_eq_tsum_rpow h1]
  simp [Real.norm_eq_abs]

/-- **Stability of a family of schemes** ([quarteroni2000numerical], (13.46)). Let
$(E_i)_{i \in \iota}$ be a family of real normed spaces, and for each $i$ let
$\Delta t_i, \Delta x_i \in \mathbb{R}$ be the steps and $Q_i \colon E_i \to E_i$ a continuous
linear map. The family is **stable** if for every horizon $T > 0$ there are $C \in \mathbb{R}$
and $\delta_0 > 0$ such that
$$\|Q_i^n\| \le C$$
for every $i$ with $0 < \Delta t_i \le \delta_0$ and $0 < \Delta x_i \le \delta_0$, and every
$n \in \mathbb{N}$ with $n \Delta t_i \le T$.

The form on a fixed space is Definition 6.3.1 of [han2009theoretical]. The spaces $E_i$ depend
on $i$, so that periodic grids and the whole line are both instances. When $E_i$ is a space of
grid functions and the discrete norm is a constant multiple of the $\ell^p$ norm, the bound
$\|Q_i^n\| \le C$ is $\|u^n\|_\Delta \le C \|u^0\|_\Delta$. -/
def IsStableFamily {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (Δt Δx : ι → ℝ) (Q : ∀ i, E i →L[ℝ] E i) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ i, 0 < Δt i → Δt i ≤ δ₀ → 0 < Δx i → Δx i ≤ δ₀ →
    ∀ n : ℕ, (n : ℝ) * Δt i ≤ T → ‖Q i ^ n‖ ≤ C

namespace IsStableFamily

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {Δt Δx : ι → ℝ} {Q : ∀ i, E i →L[ℝ] E i}

/-- A stable family satisfies a pointwise bound. If the family $(Q_i)$ is stable and $T > 0$, there
are $C \in \mathbb{R}$ and $\delta_0 > 0$ such that $\|Q_i^n u\| \le C \|u\|$ for every $i$ with
$0 < \Delta t_i \le \delta_0$ and $0 < \Delta x_i \le \delta_0$, every $n \in \mathbb{N}$ with
$n \Delta t_i \le T$, and every $u \in E_i$. -/
theorem norm_le_of_isStableFamily (h : IsStableFamily Δt Δx Q) {T : ℝ} (hT : 0 < T) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ i, 0 < Δt i → Δt i ≤ δ₀ → 0 < Δx i → Δx i ≤ δ₀ →
      ∀ n : ℕ, (n : ℝ) * Δt i ≤ T → ∀ u : E i, ‖(Q i ^ n) u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, δ₀, hδ₀, hC⟩ := h T hT
  exact ⟨C, δ₀, hδ₀, fun i h1 h2 h3 h4 n hn u =>
    (Q i ^ n).le_of_opNorm_le (hC i h1 h2 h3 h4 n hn) u⟩

/-- **Convergence of each member of a stable family.** Let the family $(Q_i)$ with steps
$\Delta t_i, \Delta x_i$ be stable, and let $T > 0$. Then there are $C \in \mathbb{R}$ and
$\delta_0 > 0$ with the following property. Let $i$ satisfy $0 < \Delta t_i \le \delta_0$ and
$0 < \Delta x_i \le \delta_0$, let $\delta \ge 0$, and let $N \in \mathbb{N}$ with
$N \Delta t_i \le T$. Let the sequences $u, v, g, \tau$ in $E_i$ satisfy
$v^{m+1} = Q_i v^m + \Delta t_i g^m$ and $u^{m+1} = Q_i u^m + \Delta t_i g^m + \Delta t_i
\tau^m$ for $m < N$, with $u^0 = v^0$ and $\|\tau^m\| \le \delta$ for $m < N$. Then
$$\|u^m - v^m\| \le C T \delta \quad \text{for every } m \le N.$$

This is the error accumulation theorem `FiniteDifference.norm_sub_le_of_stable`, with $M_0 = C$,
applied to each member of the family. -/
theorem exists_norm_sub_le (h : IsStableFamily Δt Δx Q) {T : ℝ} (hT : 0 < T) :
    ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ i, 0 < Δt i → Δt i ≤ δ₀ → 0 < Δx i → Δx i ≤ δ₀ →
      ∀ {u v g τ : ℕ → E i} {δ : ℝ} {N : ℕ}, 0 ≤ δ → (N : ℝ) * Δt i ≤ T →
        (∀ m < N, v (m + 1) = Q i (v m) + Δt i • g m) →
        (∀ m < N, u (m + 1) = Q i (u m) + Δt i • g m + Δt i • τ m) → u 0 = v 0 →
        (∀ m < N, ‖τ m‖ ≤ δ) → ∀ m ≤ N, ‖u m - v m‖ ≤ C * T * δ := by
  obtain ⟨C, δ₀, hδ₀, hC⟩ := h T hT
  refine ⟨C, δ₀, hδ₀, fun i h1 h2 h3 h4 u v g τ δ N hδ hN hv hu h0 hτ m hm => ?_⟩
  refine norm_sub_le_of_stable h1.le hδ hN hv hu h0 (fun k hk => hC i h1 h2 h3 h4 k ?_) hτ hm
  exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) h1.le) hN

end IsStableFamily

end FiniteDifference
