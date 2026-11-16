/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.FDeriv.Partial` (the partial operators on `E × ℝ`) and
`Mathlib.Analysis.Calculus.Deriv.Comp` (a bounded linear map commutes with `d/dt`).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Calculus.DerivativeTest.Laplacian
import Numlib.Analysis.Calculus.IteratedFDeriv

/-!
# Calculus on a space-time product: the time derivative and the spatial Laplacian

Let $E$ be a finite-dimensional real inner product space, and let
$w \colon E \times \mathbb{R} \to \mathbb{R}$ be a function of space and time. This module defines
the two partial operators on $w$: the time derivative $\partial_t w$ (`Heat.timeDeriv`) and the
spatial Laplacian $\Delta_x w$ (`Heat.spaceLaplacian`), which is the Laplacian of the slice
$y \mapsto w(y, t)$. It proves their smoothness, their locality on open sets, the commutation
$\partial_t \Delta_x w = \Delta_x \partial_t w$ for smooth $w$, and the same facts for their
iterates. The commutation follows from the symmetry of the iterated derivative
(`Numlib.Analysis.Calculus.IteratedFDeriv`). The module supports [brezis2011functional], chapter 10,
Remark 4 and Remark 10.

The last sections contain three elementary facts. First, a bounded linear map commutes with the
derivative of a curve. It is stated for an additive, homogeneous map with a norm bound, which is the
form in which the evaluation at a point of a canonical $C^k(\bar\Omega)$ representative enters
`Numlib.Analysis.PDE.Bochner.SpaceTime`. Second, the second iterated derivative within a set is a
twice iterated derivative within the set. Third, a curve with values in a submodule whose derivative
lies in the submodule is differentiable as a curve in the submodule.

## Main definitions

* `Heat.timeDeriv`: the time derivative $\partial_t w(x, t) = \frac{d}{dt} w(x, t)$.
* `Heat.spaceLaplacian`: the spatial Laplacian $\Delta_x w(x, t) = \Delta(w(\cdot, t))(x)$.

## Main results

* `Heat.timeDeriv_spaceLaplacian`: $\partial_t \Delta_x w = \Delta_x \partial_t w$ for smooth $w$.
* `Heat.contDiff_timeDeriv`, `Heat.contDiff_spaceLaplacian`: both operators preserve smoothness.
* `Heat.timeDeriv_eqOn`, `Heat.spaceLaplacian_eqOn`: both operators are local on open sets.
* `Heat.timeDeriv_iterate_apply_zero_eq_zero`: the iterated time derivatives of a smooth function
  that vanishes on $\{x\} \times (0, T)$ vanish at $(x, 0)$.
* `Bochner.hasDerivWithinAt_of_forall_add_smul_norm_le`: a bounded linear map commutes with the
  derivative of a curve.
* `iteratedDerivWithin_two`: the second iterated derivative within a set.
* `HasDerivWithinAt.codRestrict_submodule`: a curve in a submodule with a derivative in the
  submodule.

## Implementation notes

* The operators are in the namespace `Heat`, which they share with
  `Numlib.Analysis.PDE.Heat.Classical` (the classical heat equation) and `Numlib.Analysis.PDE.Wave`
  (Remark 10 of [brezis2011functional], chapter 10). Nothing in this module is specific to the heat
  equation.
* The Laplacian of a function on $E$ is Mathlib's `Laplacian.laplacian`, written $\Delta$.
-/

open Filter Set Topology InnerProductSpace Laplacian
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Heat

/-! ### The time derivative and the spatial Laplacian of a function of $(x, t)$ -/

section SpaceTimeCalculus

variable {w w₁ w₂ : E × ℝ → ℝ}

/-- **The time derivative.** For $w \colon E \times \mathbb{R} \to \mathbb{R}$, the time derivative
$\partial_t w \colon E \times \mathbb{R} \to \mathbb{R}$ is
$$\partial_t w(x, t) = \frac{d}{ds} w(x, s) \Big|_{s = t}.$$

The derivative is Mathlib's `deriv`, which is $0$ where $s \mapsto w(x, s)$ is not
differentiable. -/
noncomputable def timeDeriv (w : E × ℝ → ℝ) : E × ℝ → ℝ :=
  fun p ↦ deriv (fun s ↦ w (p.1, s)) p.2

/-- **The spatial Laplacian.** For $w \colon E \times \mathbb{R} \to \mathbb{R}$, the spatial
Laplacian $\Delta_x w \colon E \times \mathbb{R} \to \mathbb{R}$ is
$$\Delta_x w(x, t) = \Delta \big( y \mapsto w(y, t) \big)(x),$$
the Laplacian of the slice $y \mapsto w(y, t)$ at $x$. -/
noncomputable def spaceLaplacian (w : E × ℝ → ℝ) : E × ℝ → ℝ :=
  fun p ↦ Δ (fun y ↦ w (y, p.2)) p.1

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The value $\partial_t w(x, t)$ is the derivative of $s \mapsto w(x, s)$ at $t$. -/
@[simp]
theorem timeDeriv_apply (w : E × ℝ → ℝ) (x : E) (t : ℝ) :
    timeDeriv w (x, t) = deriv (fun s ↦ w (x, s)) t := rfl

/-- The value $\Delta_x w(x, t)$ is the Laplacian of $y \mapsto w(y, t)$ at $x$. -/
@[simp]
theorem spaceLaplacian_apply (w : E × ℝ → ℝ) (x : E) (t : ℝ) :
    spaceLaplacian w (x, t) = Δ (fun y ↦ w (y, t)) x := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Let $E$ be a real normed space, and let $w \colon E \times \mathbb{R} \to \mathbb{R}$ be of
class $C^n$, with $i \le n$. Then for $t \in \mathbb{R}$, $x \in E$ and $m_1, \dots, m_i \in E$,
$$\nabla^i \big( y \mapsto w(y, t) \big)(x)[m_1, \dots, m_i] = \nabla^i w(x, t)[(m_1, 0), \dots,
  (m_i, 0)].$$

The slice is $w$ composed with the affine map $y \mapsto (y, 0) + (0, t)$. -/
theorem iteratedFDeriv_slice_fst [NormedSpace ℝ E] {n : WithTop ℕ∞} (hw : ContDiff ℝ n w)
    {i : ℕ} (hi : (i : WithTop ℕ∞) ≤ n) (t : ℝ) (x : E) (m : Fin i → E) :
    iteratedFDeriv ℝ i (fun y ↦ w (y, t)) x m = iteratedFDeriv ℝ i w (x, t) fun k ↦ (m k, 0) := by
  have h1 : (fun y ↦ w (y, t)) =
      (fun q : E × ℝ ↦ w (q + (0, t))) ∘ (ContinuousLinearMap.inl ℝ E ℝ) :=
    funext fun y ↦ by simp
  have h2 : ContDiff ℝ n fun q : E × ℝ ↦ w (q + (0, t)) := hw.comp (contDiff_id.add contDiff_const)
  rw [h1, (ContinuousLinearMap.inl ℝ E ℝ).iteratedFDeriv_comp_right h2 x hi,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_right]
  simp

/-- Let $w$ be of class $C^2$, and let $(b_i)$ be the standard orthonormal basis of $E$
(`stdOrthonormalBasis`). Then at every $p \in E \times \mathbb{R}$,
$$\Delta_x w(p) = \sum_i \nabla^2 w(p)[(b_i, 0), (b_i, 0)].$$
-/
theorem spaceLaplacian_eq_sum_iteratedFDeriv (hw : ContDiff ℝ 2 w) (p : E × ℝ) :
    spaceLaplacian w p = ∑ i, iteratedFDeriv ℝ 2 w p
      ![(stdOrthonormalBasis ℝ E i, 0), (stdOrthonormalBasis ℝ E i, 0)] := by
  obtain ⟨x, t⟩ := p
  rw [spaceLaplacian_apply,
    laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y ↦ w (y, t)) (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_slice_fst hw le_rfl]
  congr 1
  funext k
  fin_cases k <;> rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Let $E$ be a real normed space, and let $w$ be of class $C^1$. Then at every
$p \in E \times \mathbb{R}$, the time derivative is the derivative of $w$ in the direction
$(0, 1)$: $\partial_t w(p) = Dw(p)(0, 1)$. -/
theorem timeDeriv_eq_fderiv [NormedSpace ℝ E] (hw : ContDiff ℝ 1 w) (p : E × ℝ) :
    timeDeriv w p = fderiv ℝ w p (0, 1) := by
  obtain ⟨x, t⟩ := p
  have h : HasDerivAt (fun s : ℝ ↦ (x, s)) ((0 : E), (1 : ℝ)) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  exact ((hw.differentiable one_ne_zero (x, t)).hasFDerivAt.comp_hasDerivAt t h).deriv

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Let $E$ be a real normed space. If $w$ is smooth ($C^\infty$), then $\partial_t w$ is smooth. -/
theorem contDiff_timeDeriv [NormedSpace ℝ E] (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (timeDeriv w) := by
  have : timeDeriv w = fun p ↦ fderiv ℝ w p (0, 1) :=
    funext fun p ↦ timeDeriv_eq_fderiv (hw.of_le (by simp)) p
  rw [this]
  exact hw.fderiv_apply_right (0, 1)

/-- If $w$ is smooth ($C^\infty$), then $\Delta_x w$ is smooth. -/
theorem contDiff_spaceLaplacian (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (spaceLaplacian w) := by
  have : spaceLaplacian w = fun p ↦ ∑ i, iteratedFDeriv ℝ 2 w p
      ![(stdOrthonormalBasis ℝ E i, 0), (stdOrthonormalBasis ℝ E i, 0)] :=
    funext fun p ↦ spaceLaplacian_eq_sum_iteratedFDeriv (hw.of_le (by simp)) p
  rw [this]
  refine ContDiff.sum fun i _ ↦ ?_
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E × ℝ) ℝ _).contDiff.comp
    (hw.iteratedFDeriv_right (m := ∞) (i := 2) (by simp))

/-- **The time derivative commutes with the spatial Laplacian.** If
$w \colon E \times \mathbb{R} \to \mathbb{R}$ is smooth ($C^\infty$), then
$$\partial_t (\Delta_x w) = \Delta_x (\partial_t w).$$

Both sides equal $\sum_i \nabla^3 w[(0, 1), (b_i, 0), (b_i, 0)]$ for the standard orthonormal
basis $(b_i)$ of $E$. The proof differentiates along $(0, 1)$ last on the left side and first on
the right side, and uses the symmetry of the iterated derivative. -/
theorem timeDeriv_spaceLaplacian (hw : ContDiff ℝ ∞ w) :
    timeDeriv (spaceLaplacian w) = spaceLaplacian (timeDeriv w) := by
  funext p
  have hL : spaceLaplacian w = fun q ↦ ∑ i, iteratedFDeriv ℝ 2 w q
      ![(stdOrthonormalBasis ℝ E i, 0), (stdOrthonormalBasis ℝ E i, 0)] :=
    funext fun q ↦ spaceLaplacian_eq_sum_iteratedFDeriv (hw.of_le (by simp)) q
  have hd : ∀ m : Fin 2 → E × ℝ, ∀ q, DifferentiableAt ℝ (fun z ↦ iteratedFDeriv ℝ 2 w z m) q :=
    fun m q ↦ ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E × ℝ) ℝ m).contDiff.comp
      (hw.iteratedFDeriv_right (m := ∞) (i := 2) (by simp))).differentiable (by simp) q
  have hT : timeDeriv w = fun q ↦ fderiv ℝ w q (0, 1) :=
    funext fun q ↦ timeDeriv_eq_fderiv (hw.of_le (by simp)) q
  have hL' : spaceLaplacian w = ∑ i, fun q ↦ iteratedFDeriv ℝ 2 w q
      ![(stdOrthonormalBasis ℝ E i, 0), (stdOrthonormalBasis ℝ E i, 0)] := by
    rw [hL]
    funext q
    simp only [Finset.sum_apply]
  rw [timeDeriv_eq_fderiv ((contDiff_spaceLaplacian hw).of_le (by simp)),
    spaceLaplacian_eq_sum_iteratedFDeriv ((contDiff_timeDeriv hw).of_le (by simp)), hL',
    fderiv_sum fun i _ ↦ hd _ p, sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  set m : Fin 2 → E × ℝ := ![(stdOrthonormalBasis ℝ E i, 0), (stdOrthonormalBasis ℝ E i, 0)]
  have h3 := iteratedFDeriv_succ_apply_left_of_differentiableAt
    ((hw.iteratedFDeriv_right (m := 1) (i := 2) (by simp)).differentiable one_ne_zero p)
    (Fin.cons (0, 1) m)
  rw [Fin.tail_cons, Fin.cons_zero] at h3
  have h4 := hw.iteratedFDeriv_succ_apply_left' 2 (Fin.cons (0, 1) m) p
  rw [Fin.tail_cons, Fin.cons_zero] at h4
  rw [hT, ← h3, h4]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Let $E$ be a real normed space, and let $V \subseteq E \times \mathbb{R}$ be open. If
$w_1 = w_2$ on $V$, then $\partial_t w_1 = \partial_t w_2$ on $V$. -/
theorem timeDeriv_eqOn {V : Set (E × ℝ)} (hV : IsOpen V) (h : EqOn w₁ w₂ V) :
    EqOn (timeDeriv w₁) (timeDeriv w₂) V := by
  rintro ⟨x, t⟩ hp
  have hmem : (fun s : ℝ ↦ (x, s)) ⁻¹' V ∈ 𝓝 t :=
    (hV.preimage (continuous_const.prodMk continuous_id)).mem_nhds hp
  exact Filter.EventuallyEq.deriv_eq (eventually_of_mem hmem fun s hs ↦ h hs)

/-- Let $V \subseteq E \times \mathbb{R}$ be open. If $w_1 = w_2$ on $V$, then
$\Delta_x w_1 = \Delta_x w_2$ on $V$. -/
theorem spaceLaplacian_eqOn {V : Set (E × ℝ)} (hV : IsOpen V) (h : EqOn w₁ w₂ V) :
    EqOn (spaceLaplacian w₁) (spaceLaplacian w₂) V := by
  rintro ⟨x, t⟩ hp
  have hmem : (fun y : E ↦ (y, t)) ⁻¹' V ∈ 𝓝 x :=
    (hV.preimage (continuous_id.prodMk continuous_const)).mem_nhds hp
  exact (laplacian_congr_nhds (eventually_of_mem hmem fun y hy ↦ h hy)).eq_of_nhds

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- For every $c \in \mathbb{R}$ and every $w$, $\partial_t (c w) = c \, \partial_t w$. -/
theorem timeDeriv_const_smul (c : ℝ) (w : E × ℝ → ℝ) :
    timeDeriv (c • w) = c • timeDeriv w := by
  funext ⟨x, t⟩
  simp only [timeDeriv_apply, Pi.smul_apply, smul_eq_mul]
  exact congrFun (deriv_const_mul_field' c) t

/-- For every $c \in \mathbb{R}$ and every smooth ($C^\infty$) $w$,
$\Delta_x (c w) = c \, \Delta_x w$. -/
theorem spaceLaplacian_const_smul (c : ℝ) (hw : ContDiff ℝ ∞ w) :
    spaceLaplacian (c • w) = c • spaceLaplacian w := by
  funext ⟨x, t⟩
  have : (fun y ↦ (c • w) (y, t)) = c • fun y ↦ w (y, t) := rfl
  have hslice : ContDiffAt ℝ 2 (fun y ↦ w (y, t)) x :=
    (hw.comp (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by simp)
  change Δ (fun y ↦ (c • w) (y, t)) x = c • Δ (fun y ↦ w (y, t)) x
  rw [this, laplacian_smul c hslice]

/-- If $w$ is smooth ($C^\infty$), then the iterate $\Delta_x^j w$ is smooth for every
$j \in \mathbb{N}$. -/
theorem contDiff_spaceLaplacian_iterate (hw : ContDiff ℝ ∞ w) (j : ℕ) :
    ContDiff ℝ ∞ (spaceLaplacian^[j] w) := by
  induction j with
  | zero => exact hw
  | succ j ih => rw [Function.iterate_succ_apply']; exact contDiff_spaceLaplacian ih

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Let $E$ be a real normed space. If $w$ is smooth ($C^\infty$), then the iterate $\partial_t^j w$
is smooth for every $j \in \mathbb{N}$. -/
theorem contDiff_timeDeriv_iterate [NormedSpace ℝ E] (hw : ContDiff ℝ ∞ w) (j : ℕ) :
    ContDiff ℝ ∞ (timeDeriv^[j] w) := by
  induction j with
  | zero => exact hw
  | succ j ih => rw [Function.iterate_succ_apply']; exact contDiff_timeDeriv ih

/-- If $w$ is smooth ($C^\infty$), then $\partial_t (\Delta_x^j w) = \Delta_x^j (\partial_t w)$ for
every $j \in \mathbb{N}$. -/
theorem timeDeriv_spaceLaplacian_iterate (hw : ContDiff ℝ ∞ w) (j : ℕ) :
    timeDeriv (spaceLaplacian^[j] w) = spaceLaplacian^[j] (timeDeriv w) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      timeDeriv_spaceLaplacian (contDiff_spaceLaplacian_iterate hw j), ih]

/-- Let $V \subseteq E \times \mathbb{R}$ be open. If $w_1 = w_2$ on $V$, then
$\Delta_x^j w_1 = \Delta_x^j w_2$ on $V$ for every $j \in \mathbb{N}$. -/
theorem spaceLaplacian_iterate_eqOn {V : Set (E × ℝ)} (hV : IsOpen V) (h : EqOn w₁ w₂ V)
    (j : ℕ) : EqOn (spaceLaplacian^[j] w₁) (spaceLaplacian^[j] w₂) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact spaceLaplacian_eqOn hV ih

/-- For every $c \in \mathbb{R}$, every smooth ($C^\infty$) $w$ and every $j \in \mathbb{N}$,
$\Delta_x^j (c w) = c \, \Delta_x^j w$. -/
theorem spaceLaplacian_iterate_const_smul (c : ℝ) (hw : ContDiff ℝ ∞ w) (j : ℕ) :
    spaceLaplacian^[j] (c • w) = c • spaceLaplacian^[j] w := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      spaceLaplacian_const_smul c (contDiff_spaceLaplacian_iterate hw j)]

/-- For every $w$, $j \in \mathbb{N}$ and $t \in \mathbb{R}$, the slice
$y \mapsto \Delta_x^j w(y, t)$ is the iterated Laplacian $\Delta^j$ of the slice
$y \mapsto w(y, t)$. -/
theorem spaceLaplacian_iterate_slice (w : E × ℝ → ℝ) (j : ℕ) (t : ℝ) :
    (fun y ↦ spaceLaplacian^[j] w (y, t)) = Laplacian.laplacian^[j] fun y ↦ w (y, t) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- For every $w$, $j \in \mathbb{N}$ and $x \in E$, the slice $s \mapsto \partial_t^j w(x, s)$ is
the $j$-fold iterated derivative of the slice $s \mapsto w(x, s)$. -/
theorem timeDeriv_iterate_slice (w : E × ℝ → ℝ) (j : ℕ) (x : E) :
    (fun s ↦ timeDeriv^[j] w (x, s)) = deriv^[j] fun s ↦ w (x, s) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

end SpaceTimeCalculus

/-- Let $s \subseteq \mathbb{R}$ be open, and let $f \colon \mathbb{R} \to \mathbb{R}$ vanish on
$s$. Then the $j$-fold iterated derivative of $f$ vanishes on $s$, for every $j \in \mathbb{N}$. -/
theorem iterate_deriv_eq_zero_of_eqOn {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : EqOn f 0 s) (j : ℕ) : EqOn (deriv^[j] f) 0 s := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro t ht
    rw [Function.iterate_succ_apply', Pi.zero_apply,
      Filter.EventuallyEq.deriv_eq (eventually_of_mem (hs.mem_nhds ht) ih), deriv_zero,
      Pi.zero_apply]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Iterated time derivatives at the initial time.** Let $E$ be a real normed space, let $T > 0$,
let $u \colon E \times \mathbb{R} \to \mathbb{R}$ be smooth ($C^\infty$), and let $x \in E$ with
$u(x, t) = 0$ for all $t \in (0, T)$. Then $\partial_t^n u(x, 0) = 0$ for every
$n \in \mathbb{N}$.

The iterated time derivatives vanish on $\{x\} \times (0, T)$ by
`Heat.iterate_deriv_eq_zero_of_eqOn`, and they are continuous. -/
theorem timeDeriv_iterate_apply_zero_eq_zero [NormedSpace ℝ E] {T : ℝ} {u : E × ℝ → ℝ}
    (hT : 0 < T) (hsmooth : ContDiff ℝ ∞ u) {x : E} (hx : ∀ t ∈ Ioo 0 T, u (x, t) = 0) (n : ℕ) :
    timeDeriv^[n] u (x, 0) = 0 := by
  have h1 : EqOn (fun s ↦ timeDeriv^[n] u (x, s)) 0 (Ioo 0 T) := by
    rw [timeDeriv_iterate_slice]
    exact iterate_deriv_eq_zero_of_eqOn isOpen_Ioo (fun t ht ↦ hx t ht) n
  have h2 : EqOn (fun s ↦ timeDeriv^[n] u (x, s)) 0 (Icc 0 T) := by
    rw [← closure_Ioo hT.ne]
    exact h1.of_subset_closure ((contDiff_timeDeriv_iterate hsmooth n).continuous.comp
      (continuous_const.prodMk continuous_id)).continuousOn continuousOn_const subset_closure
      subset_rfl
  exact h2 (left_mem_Icc.2 hT.le)

end Heat

/-! ### Evaluation of a bounded linear family commutes with the time derivative -/

namespace Bochner

section Linear

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] {Φ : V → W}

/-- Let $V$ and $W$ be real normed spaces, and let $\Phi \colon V \to W$ be additive and
homogeneous, with $\|\Phi(w)\| \le C \|w\|$ for all $w$. Then
$\|\Phi(w_1) - \Phi(w_2)\| \le C \|w_1 - w_2\|$ for all $w_1, w_2 \in V$. -/
theorem norm_sub_le_of_forall_add_smul_norm_le (hadd : ∀ w₁ w₂, Φ (w₁ + w₂) = Φ w₁ + Φ w₂)
    (hsmul : ∀ (c : ℝ) w, Φ (c • w) = c • Φ w) {C : ℝ} (hb : ∀ w, ‖Φ w‖ ≤ C * ‖w‖) (w₁ w₂ : V) :
    ‖Φ w₁ - Φ w₂‖ ≤ C * ‖w₁ - w₂‖ := by
  let L : V →ₗ[ℝ] W := ⟨⟨Φ, hadd⟩, hsmul⟩
  have : Φ w₁ - Φ w₂ = Φ (w₁ - w₂) := (map_sub L w₁ w₂).symm
  rw [this]
  exact hb _

/-- **A bounded linear map commutes with the derivative of a curve.** Let $\Phi \colon V \to W$ be
additive and homogeneous, with $\|\Phi(w)\| \le C \|w\|$ for all $w$. If a curve
$v \colon \mathbb{R} \to V$ has the derivative $v'$ at $t$ within $s \subseteq \mathbb{R}$, then
$r \mapsto \Phi(v(r))$ has the derivative $\Phi(v')$ at $t$ within $s$.

This is how the evaluation at a point of the canonical $C^k(\bar\Omega)$ representative, a
bounded linear functional of $w \in H^m(\Omega)$, commutes with $d/dt$. -/
theorem hasDerivWithinAt_of_forall_add_smul_norm_le (hadd : ∀ w₁ w₂, Φ (w₁ + w₂) = Φ w₁ + Φ w₂)
    (hsmul : ∀ (c : ℝ) w, Φ (c • w) = c • Φ w) {C : ℝ} (hb : ∀ w, ‖Φ w‖ ≤ C * ‖w‖)
    {v : ℝ → V} {v' : V} {s : Set ℝ} {t : ℝ} (hv : HasDerivWithinAt v v' s t) :
    HasDerivWithinAt (fun r ↦ Φ (v r)) (Φ v') s t := by
  let L : V →L[ℝ] W := LinearMap.mkContinuous ⟨⟨Φ, hadd⟩, hsmul⟩ C hb
  exact L.hasFDerivAt.comp_hasDerivWithinAt t hv

end Linear

end Bochner

/-! ### The second iterated derivative within a set -/

/-- Let $F$ be a real normed space, let $f \colon \mathbb{R} \to F$, and let
$s \subseteq \mathbb{R}$. The second iterated derivative of $f$ within $s$ is the derivative
within $s$ of the derivative of $f$ within $s$. -/
theorem iteratedDerivWithin_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (s : Set ℝ) : iteratedDerivWithin 2 f s = derivWithin (derivWithin f s) s :=
  iteratedDerivWithin_succ.trans (congrArg (fun g ↦ derivWithin g s) iteratedDerivWithin_one)

/-! ### A curve in a submodule -/

/-- Let $K$ be a real normed space and $V \subseteq K$ a submodule. Let $W \colon \mathbb{R} \to K$
take values in $V$, and let $W$ have the derivative $W' \in V$ at $t$ within
$s \subseteq \mathbb{R}$. Then $W$, as a curve in $V$, has the derivative $W'$ at $t$ within
$s$. -/
theorem HasDerivWithinAt.codRestrict_submodule {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] (V : Submodule ℝ K) {W : ℝ → K} {W' : K} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt W W' s t) (hW : ∀ t, W t ∈ V) (hW' : W' ∈ V) :
    HasDerivWithinAt (fun t => (⟨W t, hW t⟩ : V)) ⟨W', hW'⟩ s t := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at h ⊢
  rw [tendsto_subtype_rng]
  refine h.congr' (Filter.Eventually.of_forall fun b => ?_)
  simp [slope]
