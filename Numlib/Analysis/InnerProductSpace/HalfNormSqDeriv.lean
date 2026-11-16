/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.InnerProductSpace.NormPow

/-!
# Diagonal derivatives along lines and of half squared norms

Let $E$ be a real normed space and let $F$ be a real inner product space. For a map $g$ on $E$ that
is $n$ times continuously differentiable at $x$, the diagonal value $\nabla^n g(x)[d]^n$ of its
$n$-th derivative is the $n$-th derivative of $s \mapsto g(x + s d)$ at $s = 0$. With this reduction
to one variable, the file computes the diagonal derivatives of order at most three of
$\tfrac12 \|u\|^2$ for a map $u : E \to F$:
$$\nabla^2\bigl(\tfrac12 \|u\|^2\bigr)(x)[d]^2 = \|\nabla u(x)[d]\|^2 + \langle u(x), \nabla^2
  u(x)[d]^2 \rangle,$$
$$\nabla^3\bigl(\tfrac12 \|u\|^2\bigr)(x)[d]^3 = 3 \langle \nabla u(x)[d], \nabla^2 u(x)[d]^2
  \rangle + \langle u(x), \nabla^3 u(x)[d]^3 \rangle.$$
These are the formulas (14.3.38) and (14.3.39) of [cartis2022evaluation].

## Main results

* `iteratedFDeriv_apply_eq_iteratedDeriv`: for $g$ of class $C^n$ at $x$, $\nabla^n g(x)[d]^n$ is
  the $n$-th derivative of $s \mapsto g(x + s d)$ at $0$.
* `iteratedDeriv_two_half_norm_sq`, `iteratedDeriv_three_half_norm_sq`: for
  $\psi : \mathbb{R} \to F$, $(\tfrac12 \|\psi\|^2)'' = \|\psi'\|^2 + \langle \psi, \psi'' \rangle$
  and $(\tfrac12 \|\psi\|^2)''' = 3 \langle \psi', \psi'' \rangle + \langle \psi, \psi''' \rangle$.
* `fderiv_half_norm_sq_apply`, `iteratedFDeriv_two_half_norm_sq_apply`,
  `iteratedFDeriv_three_half_norm_sq_apply`: the diagonal derivatives of orders one, two and three
  of $\tfrac12 \|u\|^2$.

## Notation

* $\nabla^n g(x)[d]^n$: the value `iteratedFDeriv ℝ n g x (fun _ => d)` of the $n$-th derivative of
  $g$ at $x$ on the tuple $(d, \dots, d)$.

## Implementation notes

* The function $\tfrac12 \|u\|^2$ is written `fun z => ‖u z‖ ^ 2 / 2`.
-/

open Filter Set
open scoped Topology RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- Let $E$ and $G$ be real normed spaces, let $g : E \to G$ be $n$ times continuously
differentiable at $x$ with $n \ne 0$, and let $e \in G$. Then the $n$-th derivative of
$z \mapsto g(z) - e$ at $x$ equals the $n$-th derivative of $g$ at $x$. -/
theorem iteratedFDeriv_sub_const_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : E → G} {x : E} {n : ℕ} (hn : n ≠ 0) (hg : ContDiffAt ℝ n g x) (e : G) :
    iteratedFDeriv ℝ n (fun z => g z - e) x = iteratedFDeriv ℝ n g x := by
  have : (fun z => g z - e) = g - fun _ => e := rfl
  rw [this, iteratedFDeriv_sub_apply hg contDiffAt_const, iteratedFDeriv_const_of_ne hn,
    Pi.zero_apply, sub_zero]

section Diagonal

/-- Let $E$ and $G$ be real normed spaces and let $g : E \to G$ be $n$ times continuously
differentiable at $x$. Then for every direction $d \in E$,
$$\nabla^n g(x)[d]^n = \frac{d^n}{ds^n} g(x + s d) \Big|_{s = 0}.$$

This is a pointwise form of `iteratedFDeriv_apply_const_eq_iteratedDeriv`, which assumes the
smoothness on an open set. -/
theorem iteratedFDeriv_apply_eq_iteratedDeriv {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {g : E → G} {x : E} {n : ℕ} (hg : ContDiffAt ℝ n g x) (d : E) :
    iteratedFDeriv ℝ n g x (fun _ => d) = iteratedDeriv n (fun s : ℝ => g (x + s • d)) 0 := by
  obtain ⟨u, hu, hgu⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨t, htu, ht, hxt⟩ := mem_nhds_iff.1 hu
  exact iteratedFDeriv_apply_const_eq_iteratedDeriv ht (hgu.mono htu) hxt d

/-- Let $G$ be a real normed space. If $\psi : \mathbb{R} \to G$ is $n + 1$ times continuously
differentiable at $a$, then its derivative $\psi'$ is $n$ times continuously differentiable at
$a$. -/
theorem contDiffAt_deriv_of_succ {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ψ : ℝ → G} {a : ℝ} {n : ℕ} (hψ : ContDiffAt ℝ (n + 1) ψ a) :
    ContDiffAt ℝ n (deriv ψ) a := by
  have h : ContDiffAt ℝ n (fderiv ℝ ψ) a := hψ.fderiv_right le_rfl
  exact h.clm_apply contDiffAt_const

section OneDim

variable {ψ : ℝ → F} {a : ℝ}

/-- If $\psi : \mathbb{R} \to F$ is differentiable at $a$, then $s \mapsto \tfrac12 \|\psi(s)\|^2$
has the derivative $\langle \psi(a), \psi'(a) \rangle$ at $a$. -/
theorem hasDerivAt_half_norm_sq (hψ : DifferentiableAt ℝ ψ a) :
    HasDerivAt (fun s => ‖ψ s‖ ^ 2 / 2) ⟪ψ a, deriv ψ a⟫ a := by
  have h := (hψ.hasDerivAt.norm_sq).div_const 2
  convert h using 1
  ring

/-- If $\psi : \mathbb{R} \to F$ is twice continuously differentiable at $a$, then the second
derivative of $s \mapsto \tfrac12 \|\psi(s)\|^2$ at $a$ is
$$\bigl(\tfrac12 \|\psi\|^2\bigr)''(a) = \|\psi'(a)\|^2 + \langle \psi(a), \psi''(a) \rangle.$$
-/
theorem iteratedDeriv_two_half_norm_sq (hψ : ContDiffAt ℝ 2 ψ a) :
    iteratedDeriv 2 (fun s => ‖ψ s‖ ^ 2 / 2) a =
      ‖deriv ψ a‖ ^ 2 + ⟪ψ a, iteratedDeriv 2 ψ a⟫ := by
  have hev : deriv (fun s => ‖ψ s‖ ^ 2 / 2) =ᶠ[𝓝 a] fun s => ⟪ψ s, deriv ψ s⟫ := by
    filter_upwards [hψ.eventually (by simp)] with s hs
    exact (hasDerivAt_half_norm_sq (hs.differentiableAt (by simp))).deriv
  have h1 : DifferentiableAt ℝ (deriv ψ) a :=
    (contDiffAt_deriv_of_succ (n := 1) hψ).differentiableAt (by simp)
  have hd := (hψ.differentiableAt (by simp)).hasDerivAt.inner ℝ h1.hasDerivAt
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, hd.deriv, iteratedDeriv_succ,
    iteratedDeriv_one, real_inner_self_eq_norm_sq]
  ring

/-- If $\psi : \mathbb{R} \to F$ is three times continuously differentiable at $a$, then the third
derivative of $s \mapsto \tfrac12 \|\psi(s)\|^2$ at $a$ is
$$\bigl(\tfrac12 \|\psi\|^2\bigr)'''(a) = 3 \langle \psi'(a), \psi''(a) \rangle + \langle
  \psi(a), \psi'''(a) \rangle.$$
-/
theorem iteratedDeriv_three_half_norm_sq (hψ : ContDiffAt ℝ 3 ψ a) :
    iteratedDeriv 3 (fun s => ‖ψ s‖ ^ 2 / 2) a =
      3 * ⟪deriv ψ a, iteratedDeriv 2 ψ a⟫ + ⟪ψ a, iteratedDeriv 3 ψ a⟫ := by
  have hev : iteratedDeriv 2 (fun s => ‖ψ s‖ ^ 2 / 2) =ᶠ[𝓝 a]
      fun s => ‖deriv ψ s‖ ^ 2 + ⟪ψ s, iteratedDeriv 2 ψ s⟫ := by
    filter_upwards [hψ.eventually (by simp)] with s hs
    exact iteratedDeriv_two_half_norm_sq (hs.of_le (by norm_num))
  have h1 : ContDiffAt ℝ 2 (deriv ψ) a := contDiffAt_deriv_of_succ (n := 2) hψ
  have h2 : DifferentiableAt ℝ (iteratedDeriv 2 ψ) a := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (contDiffAt_deriv_of_succ (n := 1) h1).differentiableAt (by simp)
  have hd1 := (h1.differentiableAt (by simp)).hasDerivAt.norm_sq
  have hd2 := (hψ.differentiableAt (by simp)).hasDerivAt.inner ℝ h2.hasDerivAt
  have hd : HasDerivAt (fun s => ‖deriv ψ s‖ ^ 2 + ⟪ψ s, iteratedDeriv 2 ψ s⟫) _ a :=
    hd1.add hd2
  have h21 : deriv (deriv ψ) = iteratedDeriv 2 ψ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv, iteratedDeriv_succ (n := 2), h21]
  ring

end OneDim

variable {u : E → F} {x d : E}

/-- If $u : E \to F$ is differentiable at $x$, then for every direction $d \in E$,
$$\nabla\bigl(\tfrac12 \|u\|^2\bigr)(x)[d] = \langle u(x), \nabla u(x)[d] \rangle.$$
-/
theorem fderiv_half_norm_sq_apply (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun z => ‖u z‖ ^ 2 / 2) x d = ⟪u x, fderiv ℝ u x d⟫ := by
  have h := (hu.hasFDerivAt.norm_sq.const_smul (2⁻¹ : ℝ))
  have hfun : (fun z => ‖u z‖ ^ 2 / 2) = (2⁻¹ : ℝ) • fun z => ‖u z‖ ^ 2 := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, h.fderiv]
  simp

/-- Let $G$ be a real normed space. If $g : E \to G$ is $n$ times continuously differentiable at
$x$, then for every $d \in E$ the map $s \mapsto g(x + s d)$ on $\mathbb{R}$ is $n$ times
continuously differentiable at $0$. -/
theorem contDiffAt_comp_line {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : E → G}
    {n : ℕ} (hg : ContDiffAt ℝ n g x) (d : E) :
    ContDiffAt ℝ n (fun s : ℝ => g (x + s • d)) 0 := by
  have hl : ContDiffAt ℝ n (fun s : ℝ => x + s • d) 0 :=
    contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hg' : ContDiffAt ℝ n g (x + (0 : ℝ) • d) := by rwa [zero_smul, add_zero]
  exact hg'.comp 0 hl

/-- If $u : E \to F$ is twice continuously differentiable at $x$, then for every direction $d \in E$
the diagonal second derivative of $\tfrac12 \|u\|^2$ is
$$\nabla^2\bigl(\tfrac12 \|u\|^2\bigr)(x)[d]^2 = \|\nabla u(x)[d]\|^2 + \langle u(x), \nabla^2
  u(x)[d]^2 \rangle.$$
This is (14.3.38) of [cartis2022evaluation]. -/
theorem iteratedFDeriv_two_half_norm_sq_apply (hu : ContDiffAt ℝ 2 u x) :
    iteratedFDeriv ℝ 2 (fun z => ‖u z‖ ^ 2 / 2) x (fun _ => d) =
      ‖fderiv ℝ u x d‖ ^ 2 + ⟪u x, iteratedFDeriv ℝ 2 u x (fun _ => d)⟫ := by
  have hG : ContDiffAt ℝ 2 (fun z => ‖u z‖ ^ 2 / 2) x := (hu.norm_sq ℝ).div_const _
  have hψ := contDiffAt_comp_line hu d
  rw [iteratedFDeriv_apply_eq_iteratedDeriv hG d, iteratedFDeriv_apply_eq_iteratedDeriv hu d,
    ← iteratedFDeriv_one_apply (m := fun _ => d),
    iteratedFDeriv_apply_eq_iteratedDeriv (hu.of_le (by norm_num)) d, iteratedDeriv_one]
  have := iteratedDeriv_two_half_norm_sq hψ
  simpa only [zero_smul, add_zero] using this

/-- If $u : E \to F$ is three times continuously differentiable at $x$, then for every direction
$d \in E$ the diagonal third derivative of $\tfrac12 \|u\|^2$ is
$$\nabla^3\bigl(\tfrac12 \|u\|^2\bigr)(x)[d]^3 = 3 \langle \nabla u(x)[d], \nabla^2 u(x)[d]^2
  \rangle + \langle u(x), \nabla^3 u(x)[d]^3 \rangle.$$
This is (14.3.39) of [cartis2022evaluation]. -/
theorem iteratedFDeriv_three_half_norm_sq_apply (hu : ContDiffAt ℝ 3 u x) :
    iteratedFDeriv ℝ 3 (fun z => ‖u z‖ ^ 2 / 2) x (fun _ => d) =
      3 * ⟪fderiv ℝ u x d, iteratedFDeriv ℝ 2 u x (fun _ => d)⟫ +
        ⟪u x, iteratedFDeriv ℝ 3 u x (fun _ => d)⟫ := by
  have hG : ContDiffAt ℝ 3 (fun z => ‖u z‖ ^ 2 / 2) x := (hu.norm_sq ℝ).div_const _
  have hψ := contDiffAt_comp_line hu d
  rw [iteratedFDeriv_apply_eq_iteratedDeriv hG d, iteratedFDeriv_apply_eq_iteratedDeriv hu d,
    iteratedFDeriv_apply_eq_iteratedDeriv (hu.of_le (by norm_num)) d,
    ← iteratedFDeriv_one_apply (m := fun _ => d),
    iteratedFDeriv_apply_eq_iteratedDeriv (hu.of_le (by norm_num)) d, iteratedDeriv_one]
  have := iteratedDeriv_three_half_norm_sq hψ
  simpa only [zero_smul, add_zero] using this

end Diagonal
