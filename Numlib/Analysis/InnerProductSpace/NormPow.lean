/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.NormPow`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Real powers of the norm away from the origin

Let $E$ be a real inner product space. Mathlib's `hasFDerivAt_norm_rpow` differentiates
$x \mapsto \|x\|^p$ under the hypothesis $p > 1$, which makes the function differentiable at the
origin as well. Away from the origin the same formula
$$D(\|\cdot\|^p)(x)[h] = p \|x\|^{p-2} \langle x, h \rangle$$
holds for every real exponent $p$. A radial function with a singularity at the origin needs this
case, and its exponent is typically negative.

Off the origin, $x \mapsto \|x\|^\lambda$ is smooth, and its $n$-th derivative is homogeneous of
degree $\lambda - n$. On a finite-dimensional space it is therefore bounded by
$C_n \|x\|^{\lambda - n}$. Its values on tuples of one direction are derivatives along lines. The
radial value is $\lambda(\lambda-1)\cdots(\lambda-n+1) \|x\|^{\lambda-n}$. In a unit direction
$u \perp x$ the value is $\|x\|^{\lambda-n} h^{(n)}(0)$ for $h(t) = (1 + t^2)^{\lambda/2}$, whose
even derivatives at $0$ are $h^{(2j)}(0) = \prod_{i<j} (2i + 1)(\lambda - 2i)$. These are nonzero
unless $\lambda$ is a nonnegative even integer. These values decide for which $\lambda$ the function
$|x|^\lambda$ lies in the Sobolev space $W^{k,p}$ near the origin, as in Example 7.2.5 of
[han2009theoretical].

## Main results

* `hasFDerivAt_norm_rpow_of_ne_zero`: for every real $p$ and $x \ne 0$, the derivative of
  $\|\cdot\|^p$ at $x$ is $h \mapsto p \|x\|^{p-2} \langle x, h \rangle$.
* `norm_fderiv_norm_rpow_of_ne_zero`: this derivative has operator norm $|p| \|x\|^{p-1}$, the
  coordinate-free form of $|\nabla |x|^p| = |p| |x|^{p-1}$.
* `contDiffOn_normRpow`, `iteratedFDeriv_normRpow_smul`, `exists_norm_iteratedFDeriv_normRpow_le`:
  smoothness off the origin, homogeneity of the derivatives, and the bound
  $\|D^n(\|\cdot\|^\lambda)(x)\| \le C_n \|x\|^{\lambda - n}$.
* `iteratedFDeriv_apply_const_eq_iteratedDeriv`: the value of $D^N f(x)$ on $(u, \dots, u)$ is the
  $N$-th derivative of $t \mapsto f(x + t u)$ at $0$.
* `iteratedFDeriv_normRpow_apply_unit`: the radial value $\lambda(\lambda-1)\cdots(\lambda-k+1)
  \|x\|^{\lambda-k}$.
* `iteratedFDeriv_normRpow_apply_perp`, `iteratedFDeriv_normRpow_apply_cons_perp`: the values in a
  unit direction orthogonal to $x$, and the mixed values with one radial direction.
* `iteratedDeriv_one_add_sq_rpow_two_mul`: the even derivatives of $(1 + t^2)^{\lambda/2}$ at $0$.

## Notation

* $D^n f(x)[u_1, \dots, u_n]$: the $n$-th derivative `iteratedFDeriv ℝ n f x` of $f$ at $x$, applied
  to the tuple $(u_1, \dots, u_n)$.
* $h(t) = (1 + t^2)^{\lambda/2}$, written `fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)`.

## Implementation notes

* The exponent $\lambda$ is written `lam`. The falling factorial
  $\lambda(\lambda-1)\cdots(\lambda-k+1)$ is `∏ j : Fin k, (lam - j)`.
-/

open Filter Metric Module Set Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {x : E}

/-- Let $x \in E$ with $x \ne 0$ and let $p \in \mathbb{R}$. Then $y \mapsto \|y\|^p$ is
differentiable at $x$, with derivative
$$h \mapsto p \|x\|^{p-2} \langle x, h \rangle.$$

Mathlib's `hasFDerivAt_norm_rpow` gives the same formula under the hypothesis $p > 1$, which
gives differentiability at the origin too. Here the exponent is arbitrary and the origin is
excluded. -/
theorem hasFDerivAt_norm_rpow_of_ne_zero (hx : x ≠ 0) (p : ℝ) :
    HasFDerivAt (fun x : E ↦ ‖x‖ ^ p) ((p * ‖x‖ ^ (p - 2)) • innerSL ℝ x) x := by
  apply HasStrictFDerivAt.hasFDerivAt
  convert! (hasStrictFDerivAt_norm_sq x).rpow_const (p := p / 2) (by simp [hx]) using 0
  simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  ring_nf

/-- Let $x \in E$ with $x \ne 0$ and let $p \in \mathbb{R}$. Then the derivative of
$y \mapsto \|y\|^p$ at $x$ has operator norm
$$\|D(\|\cdot\|^p)(x)\| = |p| \|x\|^{p-1}.$$
This is the coordinate-free form of $|\nabla |x|^p| = |p| |x|^{p-1}$. -/
theorem norm_fderiv_norm_rpow_of_ne_zero (hx : x ≠ 0) (p : ℝ) :
    ‖fderiv ℝ (fun x : E ↦ ‖x‖ ^ p) x‖ = |p| * ‖x‖ ^ (p - 1) := by
  rw [(hasFDerivAt_norm_rpow_of_ne_zero hx p).fderiv, norm_smul, norm_mul, innerSL_apply_norm,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) (p - 2)), mul_assoc,
    ← Real.rpow_add_one (norm_ne_zero_iff.2 hx)]
  ring_nf

/-- Let $x \in E$ with $x \ne 0$. Then the norm is differentiable at $x$, with derivative
$$h \mapsto \frac{\langle x, h \rangle}{\|x\|}.$$

This is the case $p = 1$ of `hasFDerivAt_norm_rpow_of_ne_zero`. The norm is not differentiable
at the origin, so the hypothesis $x \ne 0$ cannot be dropped. -/
theorem hasFDerivAt_norm_of_ne_zero (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h := hasFDerivAt_norm_rpow_of_ne_zero hx 1
  simp only [Real.rpow_one] at h
  convert h using 2
  rw [one_mul, show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]

/-!
### Smoothness, homogeneity and the bound on the derivatives of $\|x\|^\lambda$ off the origin
-/

section Derivatives

/-- For every $\lambda \in \mathbb{R}$ and $n \in \mathbb{N}$, the function
$x \mapsto \|x\|^\lambda$ is $n$ times continuously differentiable on $E \setminus \{0\}$. -/
theorem contDiffOn_normRpow (lam : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun x : E ↦ ‖x‖ ^ lam) {0}ᶜ := fun _ hx ↦
  ((contDiffAt_norm (𝕜 := ℝ) hx).rpow_const_of_ne (norm_ne_zero_iff.2 hx)).contDiffWithinAt

variable [FiniteDimensional ℝ E]

/-- **Homogeneity of the derivatives of $\|x\|^\lambda$.** Let $E$ be finite-dimensional, let
$\lambda \in \mathbb{R}$, $n \in \mathbb{N}$, $t > 0$ and $x \in E$ with $x \ne 0$. Then
$$D^n(\|\cdot\|^\lambda)(t x) = t^{\lambda - n} D^n(\|\cdot\|^\lambda)(x).$$

The proof uses $\|t x\|^\lambda = t^\lambda \|x\|^\lambda$ and the chain rule for the scaling
$x \mapsto t x$. -/
theorem iteratedFDeriv_normRpow_smul (lam : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) {x : E}
    (hx : x ≠ 0) :
    iteratedFDeriv ℝ n (fun y : E ↦ ‖y‖ ^ lam) (t • x)
      = t ^ (lam - n) • iteratedFDeriv ℝ n (fun y : E ↦ ‖y‖ ^ lam) x := by
  set v : E → ℝ := fun y ↦ ‖y‖ ^ lam with hv
  let g : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E t ht.ne').toContinuousLinearEquiv
  have hg : ∀ y, g y = t • y := fun y ↦ rfl
  have hs : IsOpen ({0}ᶜ : Set E) := isOpen_compl_singleton
  have hpre : g ⁻¹' ({0}ᶜ : Set E) = {0}ᶜ := by
    ext y
    simp [hg, ht.ne']
  have hgx : g x ∈ ({0}ᶜ : Set E) := by
    rw [hg]
    exact smul_ne_zero ht.ne' hx
  -- the chain rule for the scaling
  have h1 := g.iteratedFDerivWithin_comp_right v hs.uniqueDiffOn hgx n
  rw [hpre, iteratedFDerivWithin_of_isOpen n hs hx, iteratedFDerivWithin_of_isOpen n hs hgx] at h1
  -- `v ∘ g = t^λ • v`
  have hcomp : v ∘ g = t ^ lam • v := by
    funext y
    simp only [Function.comp_apply, hg, hv, Pi.smul_apply, smul_eq_mul, norm_smul,
      Real.norm_of_nonneg ht.le, Real.mul_rpow ht.le (norm_nonneg y)]
  have hx' : ContDiffAt ℝ n v x := (contDiffOn_normRpow lam n).contDiffAt (hs.mem_nhds hx)
  rw [hcomp, iteratedFDeriv_const_smul_apply hx'] at h1
  -- the composite with the scaling is `t^n` times the derivative
  have h2 : (iteratedFDeriv ℝ n v (g x)).compContinuousLinearMap (fun _ ↦ (g : E →L[ℝ] E))
      = t ^ n • iteratedFDeriv ℝ n v (g x) := by
    ext m
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, hg, smul_apply]
    rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [h2, hg] at h1
  have htn : (t ^ n : ℝ) ≠ 0 := pow_ne_zero n ht.ne'
  rw [← hg, hg]
  calc iteratedFDeriv ℝ n v (t • x)
      = (t ^ n)⁻¹ • (t ^ n • iteratedFDeriv ℝ n v (t • x)) := by
        rw [smul_smul, inv_mul_cancel₀ htn, one_smul]
    _ = (t ^ n)⁻¹ • (t ^ lam • iteratedFDeriv ℝ n v x) := by rw [h1]
    _ = t ^ (lam - n) • iteratedFDeriv ℝ n v x := by
        rw [smul_smul, Real.rpow_sub ht, Real.rpow_natCast, div_eq_inv_mul]

/-- Let $E$ be finite-dimensional, let $\lambda \in \mathbb{R}$ and $n \in \mathbb{N}$. Then there
is a constant $C \ge 0$ such that for every $x \ne 0$,
$$\|D^n(\|\cdot\|^\lambda)(x)\| \le C \|x\|^{\lambda - n}.$$

The constant $C$ is the maximum of $\|D^n(\|\cdot\|^\lambda)\|$ on the unit sphere. The bound
follows from homogeneity (`iteratedFDeriv_normRpow_smul`) and the compactness of the sphere. -/
theorem exists_norm_iteratedFDeriv_normRpow_le (lam : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, x ≠ 0 →
      ‖iteratedFDeriv ℝ n (fun y : E ↦ ‖y‖ ^ lam) x‖ ≤ C * ‖x‖ ^ (lam - n) := by
  set v : E → ℝ := fun y ↦ ‖y‖ ^ lam with hv
  have hcont : ContinuousOn (iteratedFDeriv ℝ n v) (sphere (0 : E) 1) :=
    (ContinuousOn.continuousOn_iteratedFDeriv (contDiffOn_normRpow lam n) isOpen_compl_singleton
      le_rfl).mono fun y hy ↦ by
        simp only [mem_compl_iff, mem_singleton_iff]
        rintro rfl
        simp at hy
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun x hx ↦ ?_⟩
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
  set u : E := ‖x‖⁻¹ • x with hu
  have hu1 : u ∈ sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu1
    simp at hu1
  have hxu : x = ‖x‖ • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
  have key := iteratedFDeriv_normRpow_smul lam n hnx hu0
  rw [← hxu] at key
  rw [key, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hnx.le _), mul_comm]
  exact mul_le_mul_of_nonneg_right ((hC u hu1).trans (le_max_left _ _))
    (Real.rpow_nonneg hnx.le _)

end Derivatives

/-! ### The iterated derivative along a line, and the radial derivative of $\|x\|^\lambda$ -/

section Radial

/-- Let $\lambda, c \in \mathbb{R}$ and $k \in \mathbb{N}$. For every $t > -c$, the $k$-th
derivative of $s \mapsto (c + s)^\lambda$ at $t$ is
$$\lambda(\lambda-1)\cdots(\lambda-k+1) (c + t)^{\lambda - k}.$$
-/
theorem iteratedDeriv_const_add_rpow (lam c : ℝ) (k : ℕ) :
    ∀ t : ℝ, -c < t →
      iteratedDeriv k (fun s : ℝ ↦ (c + s) ^ lam) t
        = (∏ j : Fin k, (lam - j)) * (c + t) ^ (lam - k) := by
  induction k with
  | zero =>
    intro t _
    simp
  | succ k ih =>
    intro t ht
    have hopen : IsOpen {s : ℝ | -c < s} := isOpen_lt continuous_const continuous_id
    have hev : iteratedDeriv k (fun s : ℝ ↦ (c + s) ^ lam)
        =ᶠ[𝓝 t] fun s ↦ (∏ j : Fin k, (lam - j)) * (c + s) ^ (lam - k) :=
      Filter.eventually_of_mem (hopen.mem_nhds ht) fun s hs ↦ ih s hs
    have hct : c + t ≠ 0 := by linarith
    have hder : HasDerivAt (fun s ↦ (∏ j : Fin k, (lam - j)) * (c + s) ^ (lam - k))
        ((∏ j : Fin k, (lam - j)) * (1 * (lam - k) * (c + t) ^ (lam - k - 1))) t :=
      (((hasDerivAt_id t).const_add c).rpow_const (Or.inl hct)).const_mul _
    rw [iteratedDeriv_succ, hev.deriv_eq, hder.deriv, Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_succ]
    rw [show lam - (k + 1) = lam - k - 1 by ring]
    ring

/-- Let $E$ and $F$ be real normed spaces, let $s \subseteq E$ be open, and let $f : E \to F$ be $N$
times continuously differentiable on $s$. Then for every $x \in s$ and every direction
$u \in E$,
$$D^N f(x)[u, \dots, u] = \frac{d^N}{dt^N} f(x + t u) \Big|_{t = 0}.$$

The proof applies the chain rule to the affine map $t \mapsto x + t u$, restricted to the open
preimage of $s$. -/
theorem iteratedFDeriv_apply_const_eq_iteratedDeriv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} (hs : IsOpen s)
    {N : ℕ} {f : E → F} (hf : ContDiffOn ℝ N f s) {x : E} (hx : x ∈ s) (u : E) :
    iteratedFDeriv ℝ N f x (fun _ ↦ u) = iteratedDeriv N (fun t : ℝ ↦ f (x + t • u)) 0 := by
  let g : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight u
  have hg : ∀ t : ℝ, g t = t • u := fun t ↦ rfl
  set F' : E → F := fun z ↦ f (x + z) with hF'
  set s' : Set E := (fun z ↦ x + z) ⁻¹' s with hs'
  have hs'o : IsOpen s' := hs.preimage (continuous_const.add continuous_id)
  have hf' : ContDiffOn ℝ N F' s' :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn fun z hz ↦ hz
  have hpo : IsOpen (g ⁻¹' s') := hs'o.preimage g.continuous
  have h0 : g 0 ∈ s' := by simp [hs', hg, hx]
  have h1 := g.iteratedFDerivWithin_comp_right hf' hs'o.uniqueDiffOn hpo.uniqueDiffOn h0 le_rfl
  rw [iteratedFDerivWithin_of_isOpen N hpo (by simpa using h0),
    iteratedFDerivWithin_of_isOpen N hs'o h0, map_zero] at h1
  have h2 : iteratedFDeriv ℝ N F' 0 = iteratedFDeriv ℝ N f x := by
    rw [hF', iteratedFDeriv_comp_add_left' N x]
    simp
  rw [h2] at h1
  have h3 := congrArg (fun T : ℝ [×N]→L[ℝ] F ↦ T fun _ ↦ (1 : ℝ)) h1
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hg, one_smul] at h3
  rw [← iteratedDeriv_eq_iteratedFDeriv] at h3
  rw [← h3]
  rfl

/-- **The radial derivatives of $\|x\|^\lambda$.** Let $\lambda \in \mathbb{R}$, $k \in \mathbb{N}$
and $x \in E$ with $x \ne 0$, and let $u = x / \|x\|$. Then
$$D^k(\|\cdot\|^\lambda)(x)[u, \dots, u] = \lambda(\lambda-1)\cdots(\lambda-k+1)
  \|x\|^{\lambda - k}.$$

Along the ray $t \mapsto x + t u$ the function is $(\|x\| + t)^\lambda$, and
`iteratedDeriv_const_add_rpow` gives its derivatives. -/
theorem iteratedFDeriv_normRpow_apply_unit (lam : ℝ) (k : ℕ) {x : E} (hx : x ≠ 0) :
    iteratedFDeriv ℝ k (fun y : E ↦ ‖y‖ ^ lam) x (fun _ ↦ ‖x‖⁻¹ • x)
      = (∏ j : Fin k, (lam - j)) * ‖x‖ ^ (lam - k) := by
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
  set u : E := ‖x‖⁻¹ • x with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
  have hxu : x = ‖x‖ • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
  rw [iteratedFDeriv_apply_const_eq_iteratedDeriv isOpen_compl_singleton
    (contDiffOn_normRpow lam k) hx u]
  -- along the ray the function is `(|x| + t)^λ`
  have hev : (fun t : ℝ ↦ ‖x + t • u‖ ^ lam) =ᶠ[𝓝 (0 : ℝ)] fun t ↦ (‖x‖ + t) ^ lam := by
    have : {t : ℝ | -‖x‖ < t} ∈ 𝓝 (0 : ℝ) :=
      (isOpen_lt continuous_const continuous_id).mem_nhds (by simpa using hnx)
    filter_upwards [this] with t ht
    have ht' : -‖x‖ < t := ht
    rw [show x + t • u = (‖x‖ + t) • u by rw [add_smul, ← hxu], norm_smul, hu1, mul_one,
      Real.norm_of_nonneg (by linarith)]
  rw [hev.iteratedDeriv_eq, iteratedDeriv_const_add_rpow lam ‖x‖ k 0 (by simpa using hnx),
    add_zero]

end Radial

/-!
### The derivatives of $(1 + t^2)^{\lambda/2}$ at the origin

Along a line through $x \ne 0$ in a unit direction $u \perp x$,
$$\|x + t u\|^\lambda = \|x\|^\lambda \bigl(1 + t^2 / \|x\|^2\bigr)^{\lambda/2}.$$
So the derivatives of $\|\cdot\|^\lambda$ in directions orthogonal to $x$ are those of
$h(t) = (1 + t^2)^{\lambda/2}$ at $0$. The function $h$ satisfies $(1 + t^2) h' = \lambda t h$. This
gives the recursion $h^{(n+2)}(0) = (n + 1)(\lambda - n) h^{(n)}(0)$, and hence $h^{(2j)}(0) =
\prod_{i<j} (2i + 1)(\lambda - 2i)$, which is nonzero unless $\lambda$ is a nonnegative even
integer. The necessity half of Example 7.2.5 of [han2009theoretical] needs this at the odd integers
$\lambda$, where the radial derivative $\lambda(\lambda-1)\cdots(\lambda-k+1)$ vanishes.
-/

/-- For every $\lambda \in \mathbb{R}$, the function $t \mapsto (1 + t^2)^{\lambda/2}$ is smooth on
$\mathbb{R}$. -/
theorem contDiff_one_add_sq_rpow (lam : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) :=
  (contDiff_const.add (contDiff_id.pow 2)).rpow_const_of_ne fun t ↦ by positivity

/-- For every $\lambda \in \mathbb{R}$, the derivative of $t \mapsto (1 + t^2)^{\lambda/2}$ is
$t \mapsto \lambda t (1 + t^2)^{\lambda/2 - 1}$. -/
theorem deriv_one_add_sq_rpow (lam : ℝ) :
    deriv (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2))
      = fun t ↦ lam * t * (1 + t ^ 2) ^ (lam / 2 - 1) := by
  funext t
  have h1 : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  have h : HasDerivAt (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2))
      ((2 * t ^ (2 - 1) * 1) * (lam / 2) * (1 + t ^ 2) ^ (lam / 2 - 1)) t :=
    (((hasDerivAt_id t).pow 2).const_add 1).rpow_const (Or.inl h1)
  rw [h.deriv, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  ring

/-- The function $h(t) = (1 + t^2)^{\lambda/2}$ satisfies the differential equation
$(1 + t^2) h'(t) = \lambda t h(t)$ for every $t \in \mathbb{R}$, written as
$h'(t) + t^2 h'(t) = \lambda t h(t)$. -/
theorem deriv_one_add_sq_rpow_ode (lam : ℝ) :
    (fun t : ℝ ↦ deriv (fun s : ℝ ↦ (1 + s ^ 2) ^ (lam / 2)) t
        + t ^ 2 * deriv (fun s : ℝ ↦ (1 + s ^ 2) ^ (lam / 2)) t)
      = fun t ↦ lam * (t * (1 + t ^ 2) ^ (lam / 2)) := by
  funext t
  simp only [deriv_one_add_sq_rpow]
  have h0 : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  rw [Real.rpow_sub_one h0]
  field_simp

/-- Let $h(t) = (1 + t^2)^{\lambda/2}$ with $\lambda \in \mathbb{R}$. Then for every
$n \in \mathbb{N}$,
$$h^{(n+2)}(0) = (n + 1)(\lambda - n) h^{(n)}(0).$$

The proof differentiates the equation $(1 + t^2) h' = \lambda t h$ $n + 1$ times by the Leibniz
rule and evaluates at $0$. -/
theorem iteratedDeriv_one_add_sq_rpow_succ_succ (lam : ℝ) (n : ℕ) :
    iteratedDeriv (n + 2) (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0
      = (n + 1) * (lam - n) * iteratedDeriv n (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0 := by
  set h : ℝ → ℝ := fun t ↦ (1 + t ^ 2) ^ (lam / 2) with hh
  have hsm : ContDiff ℝ (⊤ : ℕ∞) h := contDiff_one_add_sq_rpow lam
  have hsm' : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := (contDiff_infty_iff_deriv.1 hsm).2
  have key := congrArg (fun g : ℝ → ℝ ↦ iteratedDeriv (n + 1) g 0) (deriv_one_add_sq_rpow_ode lam)
  have hsq : ContDiffAt ℝ (n + 1) (fun t : ℝ ↦ t ^ 2) 0 := by fun_prop
  have hid : ContDiffAt ℝ (n + 1) (fun t : ℝ ↦ t) 0 := contDiffAt_id
  have hh1 : ContDiffAt ℝ (n + 1) h 0 := (hsm.of_le (by simp)).contDiffAt
  have hh1' : ContDiffAt ℝ (n + 1) (deriv h) 0 := (hsm'.of_le (by simp)).contDiffAt
  -- the left-hand side
  have hL : iteratedDeriv (n + 1) (fun t ↦ deriv h t + t ^ 2 * deriv h t) 0
      = iteratedDeriv (n + 2) h 0 + (n + 1) * n * iteratedDeriv n h 0 := by
    rw [iteratedDeriv_fun_add hh1' (hsq.mul hh1'), iteratedDeriv_fun_mul hsq hh1']
    simp only [iteratedDeriv_fun_pow_zero, Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range]
    rcases n with _ | n
    · have e2 : iteratedDeriv 2 h 0 = iteratedDeriv 1 (deriv h) 0 := by rw [iteratedDeriv_succ']
      simp [e2]
    · have e1 : iteratedDeriv (n + 1 + 2) h 0 = iteratedDeriv (n + 1 + 1) (deriv h) 0 := by
        rw [iteratedDeriv_succ']
      have e2 : iteratedDeriv (n + 1) h 0 = iteratedDeriv n (deriv h) 0 := by
        rw [iteratedDeriv_succ']
      rw [ite_eq_left (by omega), show n + 1 + 1 - 2 = n by omega, e1, e2, Nat.cast_choose_two]
      push_cast
      rw [Nat.factorial_two]
      push_cast
      ring
  -- the right-hand side
  have hR : iteratedDeriv (n + 1) (fun t ↦ lam * (t * h t)) 0
      = lam * ((n + 1) * iteratedDeriv n h 0) := by
    rw [iteratedDeriv_const_mul lam (hid.mul hh1), iteratedDeriv_fun_mul hid hh1]
    have h12 : 1 < n + 1 + 1 := by omega
    simp only [iteratedDeriv_fun_id_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_range, h12, ite_true, Nat.choose_one_right,
      Nat.add_sub_cancel]
    push_cast
    ring
  rw [hL, hR] at key
  linear_combination key

/-- Let $h(t) = (1 + t^2)^{\lambda/2}$ with $\lambda \in \mathbb{R}$. Then for every
$j \in \mathbb{N}$,
$$h^{(2j)}(0) = \prod_{i<j} (2i + 1)(\lambda - 2i).$$

The proof is an induction with the recursion `iteratedDeriv_one_add_sq_rpow_succ_succ`. In
particular $h^{(2j)}(0) \ne 0$ for every $j$ if $\lambda$ is not a nonnegative even integer. For
$\lambda = 2i$ the value vanishes for $j \ge i + 1$, because $h$ is then the polynomial
$(1 + t^2)^i$. -/
theorem iteratedDeriv_one_add_sq_rpow_two_mul (lam : ℝ) (j : ℕ) :
    iteratedDeriv (2 * j) (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0
      = ∏ i : Fin j, ((2 * (i : ℝ) + 1) * (lam - 2 * i)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, iteratedDeriv_one_add_sq_rpow_succ_succ, ih,
      Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    ring

/-- If $\lambda \ne 2i$ for every $i \in \mathbb{N}$, then the even derivatives $h^{(2j)}(0)$ of
$h(t) = (1 + t^2)^{\lambda/2}$ are nonzero for every $j \in \mathbb{N}$. -/
theorem iteratedDeriv_one_add_sq_rpow_two_mul_ne_zero {lam : ℝ} (hlam : ∀ i : ℕ, lam ≠ 2 * i)
    (j : ℕ) :
    iteratedDeriv (2 * j) (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0 ≠ 0 := by
  rw [iteratedDeriv_one_add_sq_rpow_two_mul]
  exact Finset.prod_ne_zero_iff.2 fun i _ ↦
    mul_ne_zero (by positivity) (sub_ne_zero.2 (hlam i))


/-! ### The derivatives of $\|x\|^\lambda$ in directions orthogonal to $x$ -/

section Perp

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Let $x, u \in E$ be unit vectors with $\langle x, u \rangle = 0$. Then along the line
$t \mapsto x + t u$,
$$\|x + t u\|^\lambda = (1 + t^2)^{\lambda/2} \quad \text{for every } t \in \mathbb{R}.$$
-/
theorem normRpow_add_smul_of_inner_eq_zero (lam : ℝ) {x u : E} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1)
    (hxu : ⟪x, u⟫ = 0) :
    (fun t : ℝ ↦ ‖x + t • u‖ ^ lam) = fun t ↦ (1 + t ^ 2) ^ (lam / 2) := by
  funext t
  have hsq : ‖x + t • u‖ ^ 2 = 1 + t ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, hxu, norm_smul, hx, hu, Real.norm_eq_abs]
    simp [sq_abs]
  rw [← hsq, ← Real.rpow_natCast_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

/-- **The derivatives of $\|x\|^\lambda$ in a direction orthogonal to $x$.** Let $E$ be
finite-dimensional, let $\lambda \in \mathbb{R}$ and $N \in \mathbb{N}$, let $x \in E$ with
$x \ne 0$, and let $u$ be a unit vector with $\langle x, u \rangle = 0$. Then
$$D^N(\|\cdot\|^\lambda)(x)[u, \dots, u] = \|x\|^{\lambda - N} h^{(N)}(0), \qquad h(t) = (1 +
  t^2)^{\lambda/2}.$$

Homogeneity reduces the claim to $\|x\| = 1$. There the line $t \mapsto x + t u$ gives
$\|x + t u\|^\lambda = (1 + t^2)^{\lambda/2}$. -/
theorem iteratedFDeriv_normRpow_apply_perp (lam : ℝ) (N : ℕ) {x u : E} (hx : x ≠ 0)
    (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0) :
    iteratedFDeriv ℝ N (fun y : E ↦ ‖y‖ ^ lam) x (fun _ ↦ u)
      = ‖x‖ ^ (lam - N) * iteratedDeriv N (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0 := by
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
  set v : E := ‖x‖⁻¹ • x with hv
  have hv1 : ‖v‖ = 1 := by
    rw [hv, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv1
    exact zero_ne_one hv1
  have hxv : x = ‖x‖ • v := by
    rw [hv, smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
  have hvu : ⟪v, u⟫ = 0 := by
    rw [hv, real_inner_smul_left, hxu, mul_zero]
  have key := iteratedFDeriv_normRpow_smul lam N hnx hv0
  rw [← hxv] at key
  rw [key, smul_apply, smul_eq_mul,
    iteratedFDeriv_apply_const_eq_iteratedDeriv isOpen_compl_singleton
      (contDiffOn_normRpow lam N) hv0 u,
    normRpow_add_smul_of_inner_eq_zero lam hv1 hu hvu]

/-- **The mixed derivatives of $\|x\|^\lambda$, once radially and $N$ times orthogonally.** Let $E$
be finite-dimensional, let $\lambda \in \mathbb{R}$ and $N \in \mathbb{N}$, let $x \in E$ with
$x \ne 0$, and let $u$ be a unit vector with $\langle x, u \rangle = 0$. Then
$$D^{N+1}(\|\cdot\|^\lambda)(x)\Bigl[\frac{x}{\|x\|}, u, \dots, u\Bigr] = (\lambda - N)
  \|x\|^{\lambda - N - 1} h^{(N)}(0), \qquad h(t) = (1 + t^2)^{\lambda/2}.$$

The radial direction is the first argument (`Fin.cons`). The outer derivative is the radial
derivative of $G(y) = D^N(\|\cdot\|^\lambda)(y)[u, \dots, u]$, which is homogeneous of degree
$\lambda - N$ by `iteratedFDeriv_normRpow_smul`. -/
theorem iteratedFDeriv_normRpow_apply_cons_perp (lam : ℝ) (N : ℕ) {x u : E} (hx : x ≠ 0)
    (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0) :
    iteratedFDeriv ℝ (N + 1) (fun y : E ↦ ‖y‖ ^ lam) x (Fin.cons (‖x‖⁻¹ • x) fun _ ↦ u)
      = (lam - N) * ‖x‖ ^ (lam - (N + 1))
        * iteratedDeriv N (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0 := by
  set f : E → ℝ := fun y ↦ ‖y‖ ^ lam with hf
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
  set v : E := ‖x‖⁻¹ • x with hv
  have hv1 : ‖v‖ = 1 := by
    rw [hv, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv1
    exact zero_ne_one hv1
  have hxv : x = ‖x‖ • v := by
    rw [hv, smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
  have hvu : ⟪v, u⟫ = 0 := by
    rw [hv, real_inner_smul_left, hxu, mul_zero]
  rw [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]
  -- the function `G = D^N f (·)(u, …, u)` and its derivative at `x`
  set G : E → ℝ := fun w ↦ iteratedFDeriv ℝ N f w fun _ ↦ u with hG
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ N f) x :=
    ((contDiffOn_normRpow lam (N + 1)).contDiffAt
      (isOpen_compl_singleton.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self N)
  have hGd : HasFDerivAt G
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin N ↦ E) ℝ fun _ ↦ u).comp
        (fderiv ℝ (iteratedFDeriv ℝ N f) x)) x :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin N ↦ E) ℝ fun _ ↦ u).hasFDerivAt.comp x
      hdiff.hasFDerivAt
  have e1 : fderiv ℝ (iteratedFDeriv ℝ N f) x v (fun _ ↦ u) = fderiv ℝ G x v := by
    rw [hGd.fderiv]
    rfl
  rw [e1]
  -- the line `t ↦ x + t v` through `x` in the radial direction
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    simpa using this
  have hGx : HasFDerivAt G (fderiv ℝ G x) (x + (0 : ℝ) • v) := by
    rw [zero_smul, add_zero]
    exact hGd.differentiableAt.hasFDerivAt
  have hcomp := hGx.comp_hasDerivAt (0 : ℝ) hline
  rw [← hcomp.deriv]
  -- along the line, `G(x + t v) = (|x| + t)^{λ-N} G(v)`
  have hev : (G ∘ fun t : ℝ ↦ x + t • v) =ᶠ[𝓝 (0 : ℝ)]
      fun t ↦ (‖x‖ + t) ^ (lam - N) * G v := by
    have : {t : ℝ | -‖x‖ < t} ∈ 𝓝 (0 : ℝ) :=
      (isOpen_lt continuous_const continuous_id).mem_nhds (by simpa using hnx)
    filter_upwards [this] with t ht
    have hpos : 0 < ‖x‖ + t := by linarith
    simp only [Function.comp_apply, hG]
    rw [show x + t • v = (‖x‖ + t) • v by rw [add_smul, ← hxv],
      iteratedFDeriv_normRpow_smul lam N hpos hv0, smul_apply, smul_eq_mul]
  rw [hev.deriv_eq]
  have hder : HasDerivAt (fun t : ℝ ↦ (‖x‖ + t) ^ (lam - N) * G v)
      ((1 * (lam - N) * (‖x‖ + 0) ^ (lam - N - 1)) * G v) 0 :=
    (((hasDerivAt_id (0 : ℝ)).const_add ‖x‖).rpow_const (Or.inl (by simpa using hnx.ne')))
      |>.mul_const _
  rw [hder.deriv, add_zero]
  have hGv : G v = iteratedDeriv N (fun t : ℝ ↦ (1 + t ^ 2) ^ (lam / 2)) 0 := by
    rw [hG]
    simp only
    rw [iteratedFDeriv_normRpow_apply_perp lam N hv0 hu hvu, hv1, Real.one_rpow, one_mul]
  rw [hGv, show lam - (N + 1) = lam - N - 1 by ring]
  ring

omit [FiniteDimensional ℝ E] in
/-- If $E$ has dimension at least $2$, then for every $x \in E$ there is a unit vector $u$ with
$\langle x, u \rangle = 0$. -/
theorem exists_norm_eq_one_inner_eq_zero (hd : 2 ≤ finrank ℝ E) (x : E) :
    ∃ u : E, ‖u‖ = 1 ∧ ⟪x, u⟫ = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
    obtain ⟨w, hw0⟩ := exists_ne (0 : E)
    have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw0
    exact ⟨‖w‖⁻¹ • w, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnw.ne'],
      inner_zero_left _⟩
  · have : Fact (finrank ℝ E = (finrank ℝ E - 1) + 1) := ⟨by omega⟩
    have hfr : finrank ℝ (ℝ ∙ x)ᗮ = finrank ℝ E - 1 :=
      Submodule.finrank_orthogonal_span_singleton hx
    have hne : (ℝ ∙ x)ᗮ ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hfr
      omega
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw0
    refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnw.ne']
    · rw [real_inner_smul_right, (Submodule.mem_orthogonal_singleton_iff_inner_right).1 hw,
        mul_zero]

end Perp
