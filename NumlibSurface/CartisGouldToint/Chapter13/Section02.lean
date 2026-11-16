/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.MvLagrange
import Numlib.FiniteDifference.Gradient
import Numlib.FiniteDifference.MixedPartial
import NumlibSurface.CartisGouldToint.Chapter13.Section01

/-!
# Cartis, Gould and Toint, Section 13.2: Fast convergence using low-degree oracles

This module formalizes Section 13.2 of [cartis2022evaluation]. The methods TRqIDA and ARqpIDA of
Section 13.1 need inexact derivatives of degrees up to $r$, with $r = q$ for TRqIDA and $r = p$ for
ARqpIDA. Section 13.2 obtains the derivatives of degrees $o + 1, \dots, r$ from oracles of degree at
most $o$, by a finite derivative-approximation scheme: finite differences or multivariate
interpolation. The errors of such a scheme have the form (13.1.2), $\|\bar\nabla^i f(x) - \nabla^i
f(x)\| \le \kappa_{\nabla,i} h_i$. Theorem 13.2.1 then follows from Theorems 13.1.8 and 13.1.19 once
oracle calls are counted: a function value costs one call and a derivative estimate costs $c$ calls,
so the number of oracle calls before the first approximately optimal iterate is at most
$\#F + c \cdot \#D$.

The stencil formulas (13.2.1) estimate an entry $\nabla^i f(x)[e_{j_1}, \dots, e_{j_i}]$ of a
derivative tensor from values of $\nabla^o f$ at points $x + h z_k$ with integer vectors $z_k$, with
error $O(h^{p-i+1})$. Interpolation (13.2.2)–(13.2.4) estimates the derivatives of $f$ by those of
the polynomial of degree at most $p$ that interpolates $f$ at poised points near $x$. Both estimates
satisfy (13.1.2) when the step or the radius is the power $h_i^{1/(p-i+1)}$ of the requested
accuracy. The proofs use `Numlib.FiniteDifference.Gradient`, `Numlib.FiniteDifference.MixedPartial`
and `Numlib.Approximation.MvLagrange`.

## Main definitions

* Section 13.2, `CartisGouldToint.Chapter13.FiniteDerivativeApproxScheme`: a finite
  derivative-approximation scheme, a deterministic map from a point and requested accuracies to
  inexact derivatives that satisfy (13.1.2), with a fixed number of oracle calls per estimate.
* Section 13.2, forward differences, `CartisGouldToint.Chapter13.fdGradientScheme`,
  `CartisGouldToint.Chapter13.fdHessianScheme`: the forward-difference gradient and Hessian are
  schemes.
* Equation (13.2.1) as a scheme, `CartisGouldToint.Chapter13.stencilScheme`: the stencil estimates
  of the derivative tensors form a scheme.
* Equations (13.2.2)–(13.2.3) as a scheme, `CartisGouldToint.Chapter13.interpolationScheme`: the
  derivatives of the interpolation model form a scheme from function values.

## Main results

* Equation (13.2.1), `CartisGouldToint.Chapter13.eq_13_2_1`,
  `CartisGouldToint.Chapter13.eq_13_2_1_ida`: stencil formulas estimate the entries of
  $\nabla^i f(x)$ from values of $\nabla^o f$ with error $K L_{f,p} h^{p-i+1}$, and with error
  $K L_{f,p} h$ for $h \le 1$.
* Equation (13.2.2), `CartisGouldToint.Chapter13.eq_13_2_2_card`: the number of interpolation points
  is $\sum_{i=0}^p \binom{n+i-1}{i}$.
* Equation (13.2.4), `CartisGouldToint.Chapter13.eq_13_2_4`,
  `CartisGouldToint.Chapter13.eq_13_2_4_scaled`: the error bound for the derivatives of the
  interpolation model, and its scaled form with error $O(\delta^{p-i+1})$.
* Theorem 13.2.1, `CartisGouldToint.Chapter13.theorem_13_2_1_i`,
  `CartisGouldToint.Chapter13.theorem_13_2_1_ii`: with derivatives from a scheme, TRqIDA needs
  $O(\epsilon_{\min}^{-(q+1)})$ oracle calls and ARqpIDA needs $O(\max_j \epsilon_j^{-\pi_j})$
  oracle calls.
* Existence of runs, `CartisGouldToint.Chapter13.exists_algorithm_13_1_1_of_scheme`,
  `CartisGouldToint.Chapter13.exists_algorithm_13_1_2_of_scheme`,
  `CartisGouldToint.Chapter13.exists_algorithm_13_1_1_fdGradient`: runs of TRqIDA and ARqpIDA driven
  by a scheme exist.

## Implementation notes

* A scheme is exact in the degrees $\le o$, which the oracles compute, and declares the number of
  oracle calls of degree $\le o$ per estimate in the field `cost`. Oracle calls are a counting
  convention, as all evaluation counts of the source are.
* The forward-difference gradient ($o = 0$, $r = 1$, $n$ function values) and Hessian ($o = 1$,
  $r = 2$, $n$ gradients) are those of `Numlib.FiniteDifference.Gradient`.
* The stencil of (13.2.1) is a tensor product of one-dimensional derivative weights
  (`FiniteDifference.isMixedStencil_tensor`), and the error bound is Taylor's theorem for
  $\nabla^o f$ (`FiniteDifference.abs_sum_iteratedFDeriv_sub_le`). The scheme
  `CartisGouldToint.Chapter13.stencilScheme` assembles the derivative tensors of degrees
  $o < i \le r$ from their entries (`CartisGouldToint.Chapter13.stencilTensor`,
  `CartisGouldToint.Chapter13.eq_sum_coordProd`), with step $h_i^{1/(p-i+1)}$
  (`CartisGouldToint.Chapter13.accuracyStep`), and satisfies (13.1.2) in the tensor norm.
* Interpolation uses `Approximation.IsLagrangeBasis`: polynomial functions of total degree at most
  $p$ on $\mathbb{R}^n$ (`Approximation.polyFunLE`, built from `MvPolynomial`) with
  $\ell_i(y_j) = \delta_{ij}$ at poised points. The scheme
  `CartisGouldToint.Chapter13.interpolationScheme` uses function values only ($o = 0$, $m$ values
  per estimate) and one interpolation radius $\delta = \min_i h_i^{1/(p-i+1)}$ for all degrees.

## Deviations from the source

* **Equation (13.2.1)** (generalization). The source states the error $O(h^{p-i+1})$ for
  $h \in (0, 1]$; the bound holds for every $h > 0$. See `CartisGouldToint.Chapter13.eq_13_2_1`.
* **Equation (13.2.2)** (typo). The source interpolates at $d + 1$ points $y_0, \dots, y_d$ with
  $d = \sum_{i=0}^p \binom{n+i-1}{i}$; the number of points is $d$, and the scaled bound after
  (13.2.4) has the factor $m = d$ in place of $d + 1$. See
  `CartisGouldToint.Chapter13.eq_13_2_2_card`, `CartisGouldToint.Chapter13.eq_13_2_4_scaled`.
* **Display after (13.2.4)** (generalization). Only the bound
  $\|\nabla^i \hat\ell_j(0)\| \le \Lambda_i$ at the centre is used, where the source takes
  $\Lambda_i$ as a maximum over the unit ball, and the points need only lie in the closed unit ball.
  See `CartisGouldToint.Chapter13.eq_13_2_4_scaled`.
* **Theorem 13.2.1, (13.2.5)–(13.2.7)** (typo). The source prints $O(\min_j \epsilon_j^{-\dots})$;
  the bounds are $O(\max_j \epsilon_j^{-\dots})$, consistent with Theorems 13.1.8 and 13.1.19. See
  `CartisGouldToint.Chapter13.theorem_13_2_1_i`, `CartisGouldToint.Chapter13.theorem_13_2_1_ii`.

## Not formalized

* The derivative-free discussion of Section 13.2.
-/

open Set Finset Optimization
open scoped Nat

namespace CartisGouldToint.Chapter13

variable {n : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- **Section 13.2** of [cartis2022evaluation], finite derivative-approximation scheme. Let
$f : \mathbb{R}^n \to \mathbb{R}$, degrees $o$ and $r$, and constants $\kappa_{\nabla,i}$. A
**finite derivative-approximation scheme** for $f$ from oracles of degree at most $o$ consists
of

* a map `est` that gives, for a point $x$ and requested accuracies $h$, inexact derivatives
  $\bar\nabla^i f(x)$;
* a number `cost` of oracle calls per estimate,

such that the estimates satisfy (13.1.2), $\|\bar\nabla^i f(x) - \nabla^i f(x)\| \le
\kappa_{\nabla,i} h_i$ for $i \in [1, r]$ whenever $h_i > 0$ for $i \in [1, r]$, and are exact
in the degrees $i \le o$.

The oracles of degree at most $o$ give the derivatives of $f$ of degree at most $o$ exactly. The
estimates are jets `FormalMultilinearSeries ℝ ℝⁿ ℝ`, and the error model is
`Optimization.JetApprox`. -/
structure FiniteDerivativeApproxScheme (f : ℝⁿ → ℝ) (o r : ℕ) (κg : ℕ → ℝ) where
  /-- The inexact derivatives at a point $x$ for the requested accuracies $h$. -/
  est : ℝⁿ → (ℕ → ℝ) → FormalMultilinearSeries ℝ ℝⁿ ℝ
  /-- The number of oracle calls of degree at most $o$ per estimate. -/
  cost : ℕ
  /-- The error model (13.1.2): if $h_i > 0$ for $i \in [1, r]$, then $\|\bar\nabla^i f(x) -
  \nabla^i f(x)\| \le \kappa_{\nabla,i} h_i$ for $i \in [1, r]$. -/
  approx : ∀ x h, (∀ i ∈ Finset.Icc 1 r, 0 < h i) →
    JetApprox (ftaylorSeries ℝ f x) (est x h) r (fun i => κg i * h i)
  /-- The estimates of degree $i \le o$ are the exact derivatives $\nabla^i f(x)$, for all
  accuracies. -/
  exact_low : ∀ x h, ∀ i ≤ o, est x h i = iteratedFDeriv ℝ i f x

/-- **Section 13.2** of [cartis2022evaluation], first display: the forward-difference gradient. Let
$f$ be $C^1$ with $\|\nabla f(y) - \nabla f(z)\| \le L \|y - z\|$ for all $y, z$. The
forward-difference gradient with step $h_1$,
$$[\bar\nabla f(x)]_i = \frac{f(x + h_1 e_i) - f(x)}{h_1},$$
together with the exact derivatives of the other degrees, is a finite derivative-approximation
scheme with $o = 0$, $r = 1$, $n$ function values per estimate and
$\kappa_{\nabla,1} = \sqrt{n} L / 2$.

The step is the requested accuracy $h_1$. The gradient enters the jet through
`Optimization.gradientJet`, and the error bound is `FiniteDifference.jetApprox_fdGradient`. -/
noncomputable def fdGradientScheme (f : ℝⁿ → ℝ) {L : ℝ} (hf : ContDiff ℝ 1 f)
    (hL : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖) :
    FiniteDerivativeApproxScheme f 0 1 (fun _ => √n * L / 2) where
  est x h := gradientJet (ftaylorSeries ℝ f x) (FiniteDifference.fdGradient f (h 1) x)
  cost := n
  approx x h hh := by
    refine (FiniteDifference.jetApprox_fdGradient hf hL (hh 1 (by simp)) x).mono_err ?_
    intro i hi
    obtain rfl : i = 1 := by simpa using hi
    exact le_rfl
  exact_low x h i hi := by
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    rw [gradientJet_apply_of_ne _ _ (by norm_num)]
    rfl

/-- **Section 13.2** of [cartis2022evaluation], fourth display: the forward-difference Hessian. Let
$f$ be $C^2$ with $\|\nabla^2 f(y) - \nabla^2 f(z)\| \le L \|y - z\|$ for all $y, z$. The
forward-difference Hessian with step $h_2$,
$$[\bar\nabla^2 f(x)]_{ij} = \frac{[\nabla f(x + h_2 e_j)]_i - [\nabla f(x)]_i}{h_2},$$
together with the exact derivatives of the other degrees, is a finite derivative-approximation
scheme with $o = 1$, $r = 2$, $n$ gradient values per estimate,
$\kappa_{\nabla,2} = \sqrt{n} L / 2$ and $\kappa_{\nabla,1} = 0$.

The Hessian is the operator `Optimization.hessianOperator f`, and it enters the jet through
`Optimization.hessianJet`. The error bound is `FiniteDifference.jetApprox_fdHessian`. -/
noncomputable def fdHessianScheme (f : ℝⁿ → ℝ) {L : ℝ} (hf : ContDiff ℝ 2 f)
    (hL : ∀ y z, ‖hessianOperator f y - hessianOperator f z‖ ≤ L * ‖y - z‖) :
    FiniteDerivativeApproxScheme f 1 2 (fun i => if i = 2 then √n * L / 2 else 0) where
  est x h := hessianJet (ftaylorSeries ℝ f x) (FiniteDifference.fdHessian f (h 2) x)
  cost := n
  approx x h hh := by
    refine (FiniteDifference.jetApprox_fdHessian hf hL (hh 2 (by simp)) x).mono_err ?_
    intro i hi
    by_cases h2 : i = 2 <;> simp [h2]
  exact_low x h i hi := by
    rw [hessianJet_apply_of_ne _ _ (by omega)]
    rfl

/-! ### Stencil formulas (13.2.1) -/

section Stencil

/-- The stencil points $x + \sum_\ell h z_\ell e_\ell$ with integer coordinates $z_\ell$ (in units
of $h$) are $x$ plus $h$ times the points of the tensor-product stencil. -/
private theorem sum_mul_int_smul_single {r K : ℕ} (h : ℝ) (j' : Fin r → Fin n)
    (l : Fin r → Fin (K + 1)) :
    ∑ m, (h * ((∑ t, if j' t = m then ((l t : ℕ) : ℤ) else 0 : ℤ) : ℝ)) •
        EuclideanSpace.single m (1 : ℝ) =
      h • FiniteDifference.tensorPoint (fun t => EuclideanSpace.single (j' t) (1 : ℝ)) l := by
  ext q
  simp only [FiniteDifference.tensorPoint, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, PiLp.single_apply, Int.cast_sum, Int.cast_ite, Int.cast_natCast,
    Int.cast_zero]
  simp_rw [mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  simp [mul_ite, eq_comm]

/-- The stencil formula (13.2.1) for a derivative of degree $o + r$, with the stencil indexed by a
finite type. -/
private theorem eq_13_2_1_aux {p o r : ℕ} (hor : o + r ≤ p) (j : Fin (o + r) → Fin n) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ) (z : ι → Fin n → ℤ) (K : ℝ), 0 ≤ K ∧
      ∀ (f : ℝⁿ → ℝ) (L h : ℝ) (C : Set ℝⁿ) (x : ℝⁿ), Convex ℝ C →
        (∀ y ∈ C, ContDiffAt ℝ p f y) → IteratedFDerivLipschitzOn f p L C → x ∈ C → 0 < h →
        (∀ k, x + ∑ ℓ, (h * z k ℓ) • EuclideanSpace.single ℓ (1 : ℝ) ∈ C) →
        |∑ k, c k / h ^ r * iteratedFDeriv ℝ o f
              (x + ∑ ℓ, (h * z k ℓ) • EuclideanSpace.single ℓ (1 : ℝ))
              (fun t => EuclideanSpace.single (j (Fin.castAdd r t)) 1) -
            iteratedFDeriv ℝ (o + r) f x (fun t => EuclideanSpace.single (j t) 1)| ≤
          K * L * h ^ (p - (o + r) + 1) := by
  let u : Fin r → ℝⁿ := fun t => EuclideanSpace.single (j (Fin.natAdd o t)) (1 : ℝ)
  let v : Fin o → ℝⁿ := fun t => EuclideanSpace.single (j (Fin.castAdd r t)) (1 : ℝ)
  refine ⟨Fin r → Fin (p - o + 1 - r + 1), inferInstance,
    FiniteDifference.tensorWeight (p - o + 1 - r) r,
    fun l ℓ => ∑ t, if j (Fin.natAdd o t) = ℓ then ((l t : ℕ) : ℤ) else 0,
    (∑ l, |FiniteDifference.tensorWeight (p - o + 1 - r) r l| *
      ‖FiniteDifference.tensorPoint u l‖ ^ (p - o + 1)) / ((p - o + 1)! : ℝ), by positivity, ?_⟩
  intro f L h C x hC hf hL hx hh hz
  simp only [sum_mul_int_smul_single] at hz ⊢
  have hb := FiniteDifference.abs_sum_iteratedFDeriv_sub_le hC hf hL hx hor
    (FiniteDifference.isMixedStencil_tensor (q := p - o) (by omega) u) v hh hz
  have hdir : (fun t => EuclideanSpace.single (j t) (1 : ℝ)) = Fin.append v u :=
    Fin.append_castAdd_natAdd.symm
  have hv : ∏ t, ‖v t‖ = 1 := by simp [v]
  rw [hv, mul_one, ← hdir] at hb
  refine hb.trans (le_of_eq ?_)
  ring

/-- **Equation (13.2.1)** of [cartis2022evaluation]. Let $0 \le o < i \le p$ and
$j_1, \dots, j_i \in [1, n]$. There are finitely many coefficients
$c_1, \dots, c_N \in \mathbb{R}$, integer vectors $z_1, \dots, z_N \in \mathbb{Z}^n$ and a
constant $K \ge 0$, independent of $f$ and of $h$, with the following property. Let
$C \subseteq \mathbb{R}^n$ be convex, let $f$ be $C^p$ near every point of $C$ with $\nabla^p f$
Lipschitz on $C$ with constant $L$, let $x \in C$ and $h > 0$, and let the stencil points
$x + h z_k$ lie in $C$. Then
$$\left| \sum_{k=1}^N \frac{c_k}{h^{i-o}} \nabla^o f(x + h z_k)[e_{j_1}, \dots, e_{j_o}] -
  \nabla^i f(x)[e_{j_1}, \dots, e_{j_i}] \right| \le K L h^{p-i+1}.$$

**Generalization.** The source states the error as $O(h^{p-i+1})$ for $h \in (0, 1]$. The bound
holds for every $h > 0$.

The source states (13.2.1) without proof; it could not find the result in the literature
(footnote 93). It writes the coefficients as $c_{i,j}$, which absorb the power of $h$ (here
$c_k / h^{i-o}$), and asks that each displacement $h z_{k,\ell}$ be an integer multiple of $h$.
The stencil is the tensor product, over the $i - o$ differentiated directions, of the
one-dimensional weights on the nodes $0, 1, \dots, p - i + 1$ that are exact for polynomials of
degree $p - i + 1$ (`FiniteDifference.isMixedStencil_tensor`). The error comes from Taylor's
theorem for $\nabla^o f$ (`FiniteDifference.abs_sum_iteratedFDeriv_sub_le`). -/
theorem eq_13_2_1 {p o i : ℕ} (hoi : o < i) (hip : i ≤ p) (j : Fin i → Fin n) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (z : Fin N → Fin n → ℤ) (K : ℝ), 0 ≤ K ∧
      ∀ (f : ℝⁿ → ℝ) (L h : ℝ) (C : Set ℝⁿ) (x : ℝⁿ), Convex ℝ C →
        (∀ y ∈ C, ContDiffAt ℝ p f y) → IteratedFDerivLipschitzOn f p L C → x ∈ C → 0 < h →
        (∀ k, x + ∑ ℓ, (h * z k ℓ) • EuclideanSpace.single ℓ (1 : ℝ) ∈ C) →
        |∑ k, c k / h ^ (i - o) * iteratedFDeriv ℝ o f
              (x + ∑ ℓ, (h * z k ℓ) • EuclideanSpace.single ℓ (1 : ℝ))
              (fun t => EuclideanSpace.single (j (Fin.castLE hoi.le t)) 1) -
            iteratedFDeriv ℝ i f x (fun t => EuclideanSpace.single (j t) 1)| ≤
          K * L * h ^ (p - i + 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hoi.le
  obtain ⟨ι, _, c, z, K, hK, H⟩ := eq_13_2_1_aux hip j
  let F := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun k => c (F.symm k), fun k => z (F.symm k), K, hK,
    fun f L h C x hC hf hL hx hh hz => ?_⟩
  have := H f L h C x hC hf hL hx hh fun k => by simpa using hz (F k)
  rw [Nat.add_sub_cancel_left]
  convert this using 3
  exact F.symm.sum_comp (fun k => c k / h ^ r * iteratedFDeriv ℝ o f
    (x + ∑ ℓ, (h * z k ℓ) • EuclideanSpace.single ℓ (1 : ℝ))
    (fun t => EuclideanSpace.single (j (Fin.castAdd r t)) 1))

/-- **Equation (13.2.1)** of [cartis2022evaluation], in the form (13.1.2). With the stencil of
`CartisGouldToint.Chapter13.eq_13_2_1`, under the same hypotheses and with $L \ge 0$ and
$0 < h \le 1$, the error in each entry is at most $K L h$:
$$\left| \sum_{k=1}^N \frac{c_k}{h^{i-o}} \nabla^o f(x + h z_k)[e_{j_1}, \dots, e_{j_o}] -
  \nabla^i f(x)[e_{j_1}, \dots, e_{j_i}] \right| \le K L h.$$

This is the entrywise analogue of (13.1.2) with the accuracies $h_i = h$. The form in the tensor
norm is `CartisGouldToint.Chapter13.stencilScheme`. -/
theorem eq_13_2_1_ida {p o i : ℕ} (hoi : o < i) (hip : i ≤ p) (j : Fin i → Fin n) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (z : Fin N → Fin n → ℤ) (K : ℝ), 0 ≤ K ∧
      ∀ (f : ℝⁿ → ℝ) (L h : ℝ) (C : Set ℝⁿ) (x : ℝⁿ), Convex ℝ C →
        (∀ y ∈ C, ContDiffAt ℝ p f y) → IteratedFDerivLipschitzOn f p L C → 0 ≤ L → x ∈ C →
        0 < h → h ≤ 1 → (∀ k, x + ∑ ℓ, (h * z k ℓ) • EuclideanSpace.single ℓ (1 : ℝ) ∈ C) →
        |∑ k, c k / h ^ (i - o) * iteratedFDeriv ℝ o f
              (x + ∑ ℓ, (h * z k ℓ) • EuclideanSpace.single ℓ (1 : ℝ))
              (fun t => EuclideanSpace.single (j (Fin.castLE hoi.le t)) 1) -
            iteratedFDeriv ℝ i f x (fun t => EuclideanSpace.single (j t) 1)| ≤ K * L * h := by
  obtain ⟨N, c, z, K, hK, H⟩ := eq_13_2_1 (p := p) hoi hip j
  refine ⟨N, c, z, K, hK, fun f L h C x hC hf hL hL0 hx hh hh1 hz => ?_⟩
  refine (H f L h C x hC hf hL hx hh hz).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_of_le_one hh.le hh1 (by omega)) (by positivity)

/-- The step $t^{1/(p-i+1)}$ for an accuracy $t$, whose $(p - i + 1)$-st power is $t$. At this step
(or interpolation radius), an error $O(\text{step}^{p-i+1})$ becomes $O(t)$, the form (13.1.2)
with accuracy $t$. -/
noncomputable def accuracyStep (p i : ℕ) (t : ℝ) : ℝ :=
  t ^ (((p - i + 1 : ℕ) : ℝ)⁻¹)

/-- For $t \ge 0$, $(t^{1/(p-i+1)})^{p-i+1} = t$. -/
theorem accuracyStep_pow (p i : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    accuracyStep p i t ^ (p - i + 1) = t :=
  Real.rpow_inv_natCast_pow ht (by omega)

/-- For $t > 0$, the step $t^{1/(p-i+1)}$ is positive. -/
theorem accuracyStep_pos (p i : ℕ) {t : ℝ} (ht : 0 < t) : 0 < accuracyStep p i t :=
  Real.rpow_pos_of_pos ht _

/-- For indices $j_1, \dots, j_i \in [1, n]$, the coordinate form
$(v_1, \dots, v_i) \mapsto \prod_t [v_t]_{j_t}$, the multilinear form dual to
$e_{j_1} \otimes \dots \otimes e_{j_i}$. A tensor is the sum of its entries
$A[e_{j_1}, \dots, e_{j_i}]$ times these forms (`CartisGouldToint.Chapter13.eq_sum_coordProd`). -/
noncomputable def coordProd {i : ℕ} (j : Fin i → Fin n) :
    ContinuousMultilinearMap ℝ (fun _ : Fin i => ℝⁿ) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin i) ℝ).compContinuousLinearMap
    fun t => EuclideanSpace.proj (j t)

/-- The coordinate form takes the value $\prod_t [v_t]_{j_t}$ at $(v_1, \dots, v_i)$. -/
theorem coordProd_apply {i : ℕ} (j : Fin i → Fin n) (v : Fin i → ℝⁿ) :
    coordProd j v = ∏ t, v t (j t) := by
  simp [coordProd]

/-- The coordinate forms have norm at most $1$. -/
theorem norm_coordProd_le {i : ℕ} (j : Fin i → Fin n) : ‖coordProd j‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun v => ?_
  rw [coordProd_apply, one_mul, norm_prod]
  gcongr with t
  exact PiLp.norm_apply_le (v t) (j t)

/-- A continuous multilinear form $A$ on $\mathbb{R}^n$ is determined by its entries:
$$A = \sum_{j_1, \dots, j_i} A[e_{j_1}, \dots, e_{j_i}] \, \pi_{j_1, \dots, j_i},$$
where $\pi_{j_1, \dots, j_i}$ is the coordinate form `CartisGouldToint.Chapter13.coordProd`. -/
theorem eq_sum_coordProd {i : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin i => ℝⁿ) ℝ) :
    A = ∑ j : Fin i → Fin n, A (fun t => EuclideanSpace.single (j t) 1) • coordProd j := by
  ext v
  have hv : v = fun t => ∑ k, v t k • EuclideanSpace.single k (1 : ℝ) :=
    funext fun t => (FiniteDifference.sum_smul_single (v t)).symm
  conv_lhs => rw [hv, A.map_sum (fun t k => v t k • EuclideanSpace.single k (1 : ℝ))]
  simp only [_root_.sum_apply, smul_apply, coordProd_apply, smul_eq_mul]
  refine sum_congr rfl fun j _ => ?_
  rw [show (fun t => v t (j t) • EuclideanSpace.single (j t) (1 : ℝ)) =
    fun t => (fun t => v t (j t)) t • (fun t => EuclideanSpace.single (j t) (1 : ℝ)) t from rfl,
    A.map_smul_univ, smul_eq_mul, mul_comm]

/-- The number $N$ of points of the stencil of `CartisGouldToint.Chapter13.eq_13_2_1` for the entry
with indices $j_1, \dots, j_i$, if $o < i \le p$; otherwise $0$. -/
noncomputable def stencilSize (p o : ℕ) {i : ℕ} (j : Fin i → Fin n) : ℕ :=
  if hij : o < i ∧ i ≤ p then (eq_13_2_1 hij.1 hij.2 j).choose else 0

/-- The error constant $K$ of the stencil of `CartisGouldToint.Chapter13.eq_13_2_1` for the entry
with indices $j_1, \dots, j_i$, if $o < i \le p$; otherwise $0$. -/
noncomputable def stencilConst (p o : ℕ) {i : ℕ} (j : Fin i → Fin n) : ℝ :=
  if hij : o < i ∧ i ≤ p then
    (eq_13_2_1 hij.1 hij.2 j).choose_spec.choose_spec.choose_spec.choose else 0

/-- The stencil error constants are nonnegative. -/
theorem stencilConst_nonneg (p o : ℕ) {i : ℕ} (j : Fin i → Fin n) : 0 ≤ stencilConst p o j := by
  unfold stencilConst
  split_ifs with hij
  · exact (eq_13_2_1 hij.1 hij.2 j).choose_spec.choose_spec.choose_spec.choose_spec.1
  · exact le_rfl

/-- The stencil estimate (13.2.1) of the entry $\nabla^i f(x)[e_{j_1}, \dots, e_{j_i}]$ with step
$h$,
$$\sum_{k=1}^N \frac{c_k}{h^{i-o}} \nabla^o f(x + h z_k)[e_{j_1}, \dots, e_{j_o}],$$
computed from $N$ values of $\nabla^o f$ with the stencil of
`CartisGouldToint.Chapter13.eq_13_2_1`, if $o < i \le p$; otherwise $0$. -/
noncomputable def stencilEntry (f : ℝⁿ → ℝ) (p o : ℕ) {i : ℕ} (j : Fin i → Fin n) (x : ℝⁿ)
    (h : ℝ) : ℝ :=
  if hij : o < i ∧ i ≤ p then
    ∑ k, (eq_13_2_1 hij.1 hij.2 j).choose_spec.choose k / h ^ (i - o) * iteratedFDeriv ℝ o f
      (x + ∑ ℓ, (h * (eq_13_2_1 hij.1 hij.2 j).choose_spec.choose_spec.choose k ℓ) •
        EuclideanSpace.single ℓ (1 : ℝ))
      (fun t => EuclideanSpace.single (j (Fin.castLE hij.1.le t)) 1)
  else 0

/-- Let $o < i \le p$, let $f$ be $C^p$ on $\mathbb{R}^n$ with $\nabla^p f$ Lipschitz with constant
$L$, and let $h > 0$. Then the stencil estimate of the entry
$\nabla^i f(x)[e_{j_1}, \dots, e_{j_i}]$ with step $h$ has error at most $K_{i,j} L h^{p-i+1}$,
where $K_{i,j}$ is the stencil constant of the entry. -/
theorem abs_stencilEntry_sub_le {f : ℝⁿ → ℝ} {p o i : ℕ} {L h : ℝ} (hoi : o < i) (hip : i ≤ p)
    (hf : ContDiff ℝ p f) (hL : IteratedFDerivLipschitzOn f p L univ) (j : Fin i → Fin n)
    (x : ℝⁿ) (hh : 0 < h) :
    |stencilEntry f p o j x h - iteratedFDeriv ℝ i f x (fun t => EuclideanSpace.single (j t) 1)| ≤
      stencilConst p o j * L * h ^ (p - i + 1) := by
  have hij : o < i ∧ i ≤ p := ⟨hoi, hip⟩
  rw [stencilEntry, dite_eq_left hij, stencilConst, dite_eq_left hij]
  exact (eq_13_2_1 hij.1 hij.2 j).choose_spec.choose_spec.choose_spec.choose_spec.2 f L h univ x
    convex_univ (fun _ _ => hf.contDiffAt) hL (mem_univ x) hh fun _ => mem_univ _

/-- The **stencil estimate of the derivative tensor** $\nabla^i f(x)$ with step $h$: the multilinear
form $\sum_j E_j \, \pi_j$, where $E_j$ is the stencil estimate of the entry with indices
$j = (j_1, \dots, j_i)$ and $\pi_j$ is the coordinate form
`CartisGouldToint.Chapter13.coordProd`. -/
noncomputable def stencilTensor (f : ℝⁿ → ℝ) (p o i : ℕ) (x : ℝⁿ) (h : ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin i => ℝⁿ) ℝ :=
  ∑ j : Fin i → Fin n, stencilEntry f p o j x h • coordProd j

/-- Error of the stencil estimate in the tensor norm. Let $o < i \le p$, let $f$ be $C^p$ on
$\mathbb{R}^n$ with $\nabla^p f$ Lipschitz with constant $L$, and let $h > 0$. Then the stencil
estimate $\bar\nabla^i f(x)$ satisfies
$$\|\bar\nabla^i f(x) - \nabla^i f(x)\| \le K_i L h^{p-i+1}, \qquad K_i = \sum_j K_{i,j},$$
the sum of the entrywise constants. -/
theorem norm_stencilTensor_sub_le {f : ℝⁿ → ℝ} {p o i : ℕ} {L h : ℝ} (hoi : o < i) (hip : i ≤ p)
    (hf : ContDiff ℝ p f) (hL : IteratedFDerivLipschitzOn f p L univ) (x : ℝⁿ) (hh : 0 < h) :
    ‖stencilTensor f p o i x h - iteratedFDeriv ℝ i f x‖ ≤
      (∑ j : Fin i → Fin n, stencilConst p o j) * L * h ^ (p - i + 1) := by
  have hA := eq_sum_coordProd (iteratedFDeriv ℝ i f x)
  calc ‖stencilTensor f p o i x h - iteratedFDeriv ℝ i f x‖
      = ‖∑ j : Fin i → Fin n, (stencilEntry f p o j x h -
          iteratedFDeriv ℝ i f x (fun t => EuclideanSpace.single (j t) 1)) • coordProd j‖ := by
        conv_lhs => rw [hA]
        rw [stencilTensor, ← sum_sub_distrib]
        exact congrArg norm (Finset.sum_congr rfl fun j _ =>
          (sub_smul (stencilEntry f p o j x h) _ (coordProd j)).symm)
    _ ≤ ∑ j : Fin i → Fin n, stencilConst p o j * L * h ^ (p - i + 1) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
        rw [norm_smul, Real.norm_eq_abs]
        calc _ ≤ |stencilEntry f p o j x h -
              iteratedFDeriv ℝ i f x (fun t => EuclideanSpace.single (j t) 1)| * 1 :=
              mul_le_mul_of_nonneg_left (norm_coordProd_le j) (abs_nonneg _)
          _ ≤ _ := by rw [mul_one]; exact abs_stencilEntry_sub_le hoi hip hf hL j x hh
    _ = _ := by rw [← sum_mul, ← sum_mul]

/-- **Equation (13.2.1)** of [cartis2022evaluation] as a finite derivative-approximation scheme. Let
$f$ be $C^p$ on $\mathbb{R}^n$ with $\nabla^p f$ Lipschitz with constant $L \ge 0$, and let
$r \le p$. For the requested accuracies $h$, the scheme gives the derivative tensors of degrees
$o < i \le r$ by the stencil estimates with step $h_i^{1/(p-i+1)}$, and the exact derivatives of
degrees $i \le o$. It satisfies (13.1.2) in the tensor norm with
$\kappa_{\nabla,i} = (\sum_j K_{i,j}) L$. Each estimate costs
$\sum_{o < i \le r} \sum_j N_{i,j}$ evaluations of derivatives of degree $o$, where $N_{i,j}$ is
the number of points of the stencil of the entry $j$.

The step is `CartisGouldToint.Chapter13.accuracyStep`, the tensor estimate is
`CartisGouldToint.Chapter13.stencilTensor`, and the numbers of points are
`CartisGouldToint.Chapter13.stencilSize`. -/
noncomputable def stencilScheme (f : ℝⁿ → ℝ) {p o r : ℕ} {L : ℝ} (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hL0 : 0 ≤ L) (hrp : r ≤ p) :
    FiniteDerivativeApproxScheme f o r
      (fun i => (∑ j : Fin i → Fin n, stencilConst p o j) * L) where
  est x h i := if o < i then stencilTensor f p o i x (accuracyStep p i (h i)) else
    iteratedFDeriv ℝ i f x
  cost := ∑ i ∈ Finset.Ioc o r, ∑ j : Fin i → Fin n, stencilSize p o j
  approx x h hh i hi := by
    obtain ⟨hi1, hir⟩ := Finset.mem_Icc.1 hi
    have hK : 0 ≤ (∑ j : Fin i → Fin n, stencilConst p o j) * L :=
      mul_nonneg (sum_nonneg fun j _ => stencilConst_nonneg p o j) hL0
    by_cases hoi : o < i
    · simp only [hoi, ↓reduceIte]
      refine (norm_stencilTensor_sub_le hoi (by omega) hf hL x
        (accuracyStep_pos p i (hh i hi))).trans (le_of_eq ?_)
      rw [accuracyStep_pow p i (hh i hi).le]
    · simp only [hoi, ↓reduceIte]
      rw [show ftaylorSeries ℝ f x i = iteratedFDeriv ℝ i f x from rfl, sub_self, norm_zero]
      exact mul_nonneg hK (hh i hi).le
  exact_low x h i hi := by
    simp [show ¬ o < i by omega]

end Stencil

/-! ### Multivariate interpolation (13.2.2)–(13.2.4) -/

section Interpolation

open Approximation

/-- **Equation (13.2.2)** of [cartis2022evaluation]. Let $\ell_1, \dots, \ell_m$ be the Lagrange
polynomials of degree $p$ of $m$ poised points in $\mathbb{R}^n$. Then
$$m = d = \sum_{i=0}^p \binom{n+i-1}{i},$$
which is $\binom{n+p}{p}$, the dimension of the polynomials of degree at most $p$, because the
Lagrange polynomials form a basis.

**Typo.** The source indexes the points as $y_0, \dots, y_d$, that is, $d + 1$ points. The
number of points is $d$. For example, $n = p = 1$ gives $d = 2$, and linear interpolation on the
line uses two points.

The Lagrange polynomials are `Approximation.IsLagrangeBasis`. -/
theorem eq_13_2_2_card {p m : ℕ} {y : Fin m → ℝⁿ} {ℓ : Fin m → ℝⁿ → ℝ}
    (hℓ : IsLagrangeBasis n p y ℓ) : m = ∑ i ∈ range (p + 1), (n + i - 1).choose i :=
  hℓ.card_eq_sum_choose

/-- **Equation (13.2.4)** of [cartis2022evaluation]. Let $\ell_1, \dots, \ell_m$ be the Lagrange
polynomials of degree $p$ of poised points $y_1, \dots, y_m$ (13.2.2), and let
$w = \sum_j f(y_j) \ell_j$ be the interpolation model (13.2.3). Let $C$ be a convex set that
contains $x$ and the points $y_j$, and let $f$ be $C^p$ near every point of $C$ with
$\nabla^p f$ Lipschitz on $C$ with constant $L_{f,p}$. Then for $i \in [0, p]$
$$\|\nabla^i w(x) - \nabla^i f(x)\| \le \frac{L_{f,p}}{(p+1)!} \sum_{j=1}^m \|y_j - x\|^{p+1}
  \|\nabla^i \ell_j(x)\|.$$

The source quotes this bound from the literature. -/
theorem eq_13_2_4 {p m : ℕ} {y : Fin m → ℝⁿ} {ℓ : Fin m → ℝⁿ → ℝ}
    (hℓ : IsLagrangeBasis n p y ℓ) {f : ℝⁿ → ℝ} {L : ℝ} {C : Set ℝⁿ} {x : ℝⁿ} (hC : Convex ℝ C)
    (hf : ∀ z ∈ C, ContDiffAt ℝ p f z) (hL : IteratedFDerivLipschitzOn f p L C) (hx : x ∈ C)
    (hy : ∀ j, y j ∈ C) {i : ℕ} (hi : i ≤ p) :
    ‖iteratedFDeriv ℝ i (fun v => ∑ j, f (y j) * ℓ j v) x - iteratedFDeriv ℝ i f x‖ ≤
      L / ((p + 1)! : ℝ) * ∑ j, ‖y j - x‖ ^ (p + 1) * ‖iteratedFDeriv ℝ i (ℓ j) x‖ :=
  hℓ.norm_iteratedFDeriv_sub_le hC hf hL hx hy hi

/-- **Section 13.2** of [cartis2022evaluation], the display after (13.2.4): the interpolation error
with scaled points has the form (13.1.2). Let $\hat\ell_1, \dots, \hat\ell_m$ be the Lagrange
polynomials of degree $p$ of poised points $\hat y_1, \dots, \hat y_m$ in the closed unit ball,
let $i \le p$, and let $\|\nabla^i \hat\ell_j(0)\| \le \Lambda_i$ for all $j$. Let $\delta > 0$,
let $C$ be a convex set that contains $x$ and the points $x + \delta \hat y_j$, and let $f$ be
$C^p$ near every point of $C$ with $\nabla^p f$ Lipschitz on $C$ with constant $L \ge 0$. The
model $w$ that interpolates $f$ at the points $x + \delta \hat y_j$, with the Lagrange
polynomials $v \mapsto \hat\ell_j((v - x)/\delta)$, satisfies
$$\|\nabla^i w(x) - \nabla^i f(x)\| \le \frac{L m}{(p+1)!} \Lambda_i \delta^{p-i+1}.$$
This is (13.1.2) with $\kappa_{\nabla,i} = L m \Lambda_i / (p+1)!$ and $h_i = \delta^{p-i+1}$.

**Typo.** The source writes $d + 1$ for the number $m$ of points; see
`CartisGouldToint.Chapter13.eq_13_2_2_card`.

**Generalization.** The source takes $\Lambda_i$ as a maximum of $\|\nabla^i \hat\ell_j\|$ over
the unit ball. Only the value at the centre is used. -/
theorem eq_13_2_4_scaled {p m : ℕ} {y : Fin m → ℝⁿ} {ℓ : Fin m → ℝⁿ → ℝ}
    (hℓ : IsLagrangeBasis n p y ℓ) (hy1 : ∀ j, ‖y j‖ ≤ 1) {i : ℕ} (hi : i ≤ p) {Λ : ℝ}
    (hΛ : ∀ j, ‖iteratedFDeriv ℝ i (ℓ j) 0‖ ≤ Λ) {f : ℝⁿ → ℝ} {L δ : ℝ} {C : Set ℝⁿ} {x : ℝⁿ}
    (hδ : 0 < δ) (hC : Convex ℝ C) (hf : ∀ z ∈ C, ContDiffAt ℝ p f z)
    (hL : IteratedFDerivLipschitzOn f p L C) (hL0 : 0 ≤ L) (hx : x ∈ C)
    (hyC : ∀ j, x + δ • y j ∈ C) :
    ‖iteratedFDeriv ℝ i (fun v => ∑ j, f (x + δ • y j) * ℓ j (δ⁻¹ • (v - x))) x -
        iteratedFDeriv ℝ i f x‖ ≤ L * m / ((p + 1)! : ℝ) * Λ * δ ^ (p - i + 1) :=
  hℓ.norm_iteratedFDeriv_sub_le_of_scaled hy1 hi hΛ hδ hC hf hL hL0 hx hyC

/-- The interpolation radius $\delta = \min_{i \in [1, r]} h_i^{1/(p-i+1)}$ of
`CartisGouldToint.Chapter13.interpolationScheme`. For positive accuracies it is the largest
radius with $\delta^{p-i+1} \le h_i$ for all $i \in [1, r]$, as in the choice
$h_i = \delta^{p-i+1}$ of the source with one interpolation set for all degrees. -/
noncomputable def interpRadius (p r : ℕ) (h : ℕ → ℝ) : ℝ :=
  epsMin r fun i => accuracyStep p i (h i)

/-- **Section 13.2** of [cartis2022evaluation], interpolation as a finite derivative-approximation
scheme. Let $\hat\ell_1, \dots, \hat\ell_m$ be the Lagrange polynomials of degree $p$ of poised
reference points $\hat y_1, \dots, \hat y_m$ in the closed unit ball, with
$\|\nabla^i \hat\ell_j(0)\| \le \Lambda_i$ for all $i$ and $j$. Let $f$ be $C^p$ on
$\mathbb{R}^n$ with $\nabla^p f$ Lipschitz with constant $L \ge 0$, and let $1 \le r \le p$. For
the requested accuracies $h$, let $\delta = \min_i h_i^{1/(p-i+1)}$ and let $w$ be the model
that interpolates $f$ at the points $x + \delta \hat y_j$. The derivatives $\nabla^i w(x)$ of
degrees $i \ge 1$, together with $f(x)$ in degree $0$, form a scheme from function values
($o = 0$, $m$ values per estimate) with $\kappa_{\nabla,i} = L m \Lambda_i / (p+1)!$. The error
$\kappa_{\nabla,i} \delta^{p-i+1}$ is at most $\kappa_{\nabla,i} h_i$, with
$\delta^{p-i+1} = h_i$ for the degree that attains the minimum.

The radius is `CartisGouldToint.Chapter13.interpRadius`, and the error bound is
`CartisGouldToint.Chapter13.eq_13_2_4_scaled`. -/
noncomputable def interpolationScheme (f : ℝⁿ → ℝ) {p m r : ℕ} {L : ℝ} {y : Fin m → ℝⁿ}
    {ℓ : Fin m → ℝⁿ → ℝ} {Λ : ℕ → ℝ} (hℓ : IsLagrangeBasis n p y ℓ) (hy1 : ∀ j, ‖y j‖ ≤ 1)
    (hΛ : ∀ i j, ‖iteratedFDeriv ℝ i (ℓ j) 0‖ ≤ Λ i) (hf : ContDiff ℝ p f)
    (hL : IteratedFDerivLipschitzOn f p L univ) (hL0 : 0 ≤ L) (hr : 1 ≤ r) (hrp : r ≤ p) :
    FiniteDerivativeApproxScheme f 0 r (fun i => L * m / ((p + 1)! : ℝ) * Λ i) where
  est x h i := if i = 0 then iteratedFDeriv ℝ i f x else
    iteratedFDeriv ℝ i (fun v => ∑ j, f (x + interpRadius p r h • y j) *
      ℓ j ((interpRadius p r h)⁻¹ • (v - x))) x
  cost := m
  approx x h hh i hi := by
    obtain ⟨hi1, hir⟩ := Finset.mem_Icc.1 hi
    have hδ : 0 < interpRadius p r h :=
      epsMin_pos hr fun k hk => accuracyStep_pos p k (hh k hk)
    have hδh : interpRadius p r h ≤ accuracyStep p i (h i) := epsMin_le hi
    simp only [show i ≠ 0 by omega, ↓reduceIte]
    refine (hℓ.norm_iteratedFDeriv_sub_le_of_scaled hy1 (by omega) (hΛ i) hδ convex_univ
      (fun z _ => hf.contDiffAt) hL hL0 (mem_univ x) fun _ => mem_univ _).trans ?_
    have hm : 0 < m := by
      rw [hℓ.card_eq]
      exact Nat.choose_pos (by omega)
    have hΛ0 : 0 ≤ Λ i := (norm_nonneg _).trans (hΛ i ⟨0, hm⟩)
    have hpow : interpRadius p r h ^ (p - i + 1) ≤ h i := by
      rw [← accuracyStep_pow p i (hh i hi).le]
      exact pow_le_pow_left₀ hδ.le hδh _
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  exact_low x h i hi := by
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    simp

end Interpolation

/-- For $t \in (0, 1]$, $|\log t| \le 1 / t$. -/
theorem abs_log_le_inv {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : |Real.log t| ≤ 1 / t := by
  rw [abs_of_nonpos (Real.log_nonpos ht.le ht1), ← Real.log_inv, one_div]
  have := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
  linarith

/-- For $t \in (0, 1]$, $m \ge 1$, $b, c \ge 0$ and $a \le a' / t^m$, the bound
$a + b |\log t| + c \le (a' + b + c) / t^m$ holds. -/
private theorem le_div_pow_of_log {a a' b c t : ℝ} {m : ℕ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hm : 1 ≤ m) (hb : 0 ≤ b) (hc : 0 ≤ c) (ha : a ≤ a' / t ^ m) :
    a + b * |Real.log t| + c ≤ (a' + b + c) / t ^ m := by
  have htm : 0 < t ^ m := pow_pos ht m
  have htm1 : t ^ m ≤ t := by
    calc t ^ m ≤ t ^ 1 := pow_le_pow_of_le_one ht.le ht1 hm
      _ = t := pow_one t
  have h1 : |Real.log t| ≤ 1 / t ^ m :=
    (abs_log_le_inv ht ht1).trans (one_div_le_one_div_of_le htm htm1)
  have h2 : c ≤ c / t ^ m := le_div_self hc htm (pow_le_one₀ ht.le ht1)
  rw [add_div, add_div]
  have := mul_le_mul_of_nonneg_left h1 hb
  rw [mul_one_div] at this
  linarith

section TR

variable {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : TRqIDAParams} {L : ℕ → ℝ} {x₀ : ℝⁿ}

/-- **Theorem 13.2.1** of [cartis2022evaluation], trust-region part (13.2.5). Assume f.D0qL and f.Bb
with the lower bound $f_{\rm low}$. Let $S$ be a finite derivative-approximation scheme for $f$
from oracles of degree at most $o$ that produces inexact derivatives up to degree $q$, with $c$
oracle calls per estimate. Then there is a constant $C$, independent of the tolerances, with the
following property. Every TRqIDA run whose derivative estimates are those of the scheme,
$\bar\nabla f(x_k) = S(x_k, h_k)$, has a first iterate $x_{k_\epsilon}$ that is an
$(\epsilon, \delta_{k_\epsilon})$-approximate $q$-th order minimizer, and before $k_\epsilon$
the number of oracle calls of degree at most $o$ satisfies
$$\#F + c \cdot \#D \le \frac{C}{\epsilon_{\min}^{q+1}} = C \max_j \epsilon_j^{-(q+1)},$$
where $\#F$ is the number of function values and $\#D$ the number of derivative estimates.

**Typo.** The source prints the bound as $O(\min_j \epsilon_j^{-(q+1)})$. The bound is
$O(\max_j \epsilon_j^{-(q+1)})$, consistent with Theorem 13.1.8.

The constant $C$ depends on $f$, the constants of the method, the starting point and the scheme.
The approximate-optimality test is `CartisGouldToint.Chapter13.trTest`. The proof applies
`CartisGouldToint.Chapter13.theorem_13_1_8` and bounds its logarithmic terms by multiples of
$\epsilon_{\min}^{-(q+1)}$. -/
theorem theorem_13_2_1_i (hf : AssumptionD0qL f P.q L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow) {o : ℕ} (S : FiniteDerivativeApproxScheme f o P.q κg) :
    ∃ C, ∀ (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop), algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc →
      (∀ k, D k = S.est (x k) (h k)) →
      ∃ kε, IsFirstHit (trTest f P ε x Δ) kε ∧
        (derivEvalCount (fun i => ¬ acc i) kε : ℝ) + S.cost *
          derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i)) kε ≤
        C / epsMin P.q ε ^ (P.q + 1) := by
  set κΔ := min 1 (P.γ₁ * ((1 - P.η₂) /
    (lipMax L P.q + 4 * (P.q + 1)! * P.κs * ordMax P.q κg)))
  set A := trKappaS P κΔ * (1 + Real.log P.γ₃ / |Real.log P.γ₂|) * (f x₀ - flow)
  set B := 1 / |Real.log P.γ₂|
  set Cc := |Real.log (P.ς * (κΔ / 2) / P.Δ₀)| / |Real.log P.γ₂| + 1
  set E := P.q * (P.q + 1) / |Real.log P.γh|
  set F := |Real.log (trKappaAcc P κΔ (lipMax L P.q + ordMax P.q κg * P.κh) (ordMax P.q κg) /
    P.κh)| / |Real.log P.γh| + 2 with hF_def
  refine ⟨(A + B + Cc) + S.cost * (A + E + F), fun ε x Δ h D dd jk s acc hrun _ => ?_⟩
  have hκΔ : IsTRKappaDelta P (lipMax L P.q) (ordMax P.q κg) κΔ := by
    have := hf.one_le_lipMax; have := hrun.kappaMax_nonneg; have := P.κs_pos
    exact ⟨lt_min one_pos (mul_pos P.γ₁_pos (div_pos P.one_sub_η₂_pos (by positivity))),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨kε, hk, -, -, h1, h2⟩ := theorem_13_1_8 hf hb hrun hκΔ
  refine ⟨kε, hk, ?_⟩
  have hε := hrun.epsMin_pos
  have hε1 := hrun.epsMin_le_one
  have hq : 1 ≤ P.q + 1 := by omega
  have hB : 0 ≤ B := by positivity
  have hC : 0 ≤ Cc := by positivity
  have hE : 0 ≤ E := by positivity
  have hF : 0 ≤ F := by positivity
  have h1' := h1.trans (le_div_pow_of_log hε hε1 hq hB hC le_rfl)
  have h2' := (h2.trans (le_of_eq (by rw [hF_def]; ring))).trans
    (le_div_pow_of_log hε hε1 hq hE hF (le_refl (A / epsMin P.q ε ^ (P.q + 1))))
  have hcost : (0 : ℝ) ≤ S.cost := Nat.cast_nonneg _
  calc (derivEvalCount (fun i => ¬ acc i) kε : ℝ) + S.cost *
        derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ trqRatio f D x s jk i)) kε
      ≤ (A + B + Cc) / epsMin P.q ε ^ (P.q + 1) +
          S.cost * ((A + E + F) / epsMin P.q ε ^ (P.q + 1)) :=
        add_le_add h1' (mul_le_mul_of_nonneg_left h2' hcost)
    _ = ((A + B + Cc) + S.cost * (A + E + F)) / epsMin P.q ε ^ (P.q + 1) := by ring

end TR

section AR

variable {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : ARqpIDAParams} {L : ℕ → ℝ} {x₀ : ℝⁿ}

/-- For $\epsilon \in (0, 1]^q$, $\min_j \epsilon_j^{\pi_j} \le \epsilon_{\min}$, where
$\pi_j \ge 1$ are the exponents of Lemma 13.1.18. -/
theorem epsMin_rpow_arPi_le {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) :
    epsMin P.q (fun j => ε j ^ arPi P.q P.p j) ≤ epsMin P.q ε := by
  obtain ⟨j, hj, he⟩ := exists_epsMin_eq (ε := ε) P.one_le_q
  rw [he]
  refine (epsMin_le hj).trans ?_
  obtain ⟨hj1, hjq⟩ := Finset.mem_Icc.1 hj
  have hp := P.one_le_p
  have hπ : 1 ≤ arPi P.q P.p j := by
    unfold arPi arPiOf
    split_ifs
    · rw [le_div_iff₀ (by exact_mod_cast (show 0 < P.p - j + 1 by omega)), one_mul]
      have : P.p - j + 1 ≤ P.p + 1 := by omega
      exact_mod_cast this
    · rw [le_div_iff₀ (by exact_mod_cast (show 0 < P.p by omega)), one_mul]
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      nlinarith
  calc ε j ^ arPi P.q P.p j ≤ ε j ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (hε j hj).1 (hε j hj).2 hπ
    _ = ε j := Real.rpow_one _

/-- **Theorem 13.2.1** of [cartis2022evaluation], regularization part (13.2.6)–(13.2.7). Assume
f.D0pL and f.Bb with the lower bound $f_{\rm low}$. Let $S$ be a finite derivative-approximation
scheme for $f$ from oracles of degree at most $o$ that produces inexact derivatives up to degree
$p$, with $c$ oracle calls per estimate. Then there is a constant $C$, independent of the
tolerances, with the following property. Every ARqpIDA run with the radii control
(13.1.69)–(13.1.70) at every iteration, whose derivative estimates are those of the scheme, has
a first iterate $x_{k_\epsilon}$ that is approximately optimal for some radii in $(0, 1]^q$, and
before $k_\epsilon$
$$\#F + c \cdot \#D \le \frac{C}{\min_j \epsilon_j^{\pi_j}},$$
with $\pi_j = (p+1)/(p-j+1)$ if $q \le 2$ and $\pi_j = j (p+1)/p$ if $q > 2$. The bound is
$O(\max_j \epsilon_j^{-\pi_j})$.

**Typo.** The source prints $\min_j$ in place of $\max_j$ in the orders (13.2.6)–(13.2.7).

The exponents are `Optimization.arPi`, and the approximate-optimality test is
`CartisGouldToint.Chapter13.arTest`. The proof applies
`CartisGouldToint.Chapter13.arqpIDA_complexity` with the decrease of
`CartisGouldToint.Chapter13.lemma_13_1_18`. -/
theorem theorem_13_2_1_ii (hf : AssumptionD0pL f P.p L) {flow : ℝ}
    (hb : Chapter02.AssumptionBb f flow) {o : ℕ}
    (S : FiniteDerivativeApproxScheme f o P.p κg) :
    ∃ C, ∀ (ε : ℕ → ℝ) (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop), algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc →
      (∀ i, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc i) →
      (∀ k, D k = S.est (x k) (h k)) →
      ∃ kε, IsFirstHit (arTest f P ε x) kε ∧
        (derivEvalCount (fun i => ¬ acc i) kε : ℝ) + S.cost *
          derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε ≤
        C / epsMin P.q (fun j => ε j ^ arPi P.q P.p j) := by
  set κΔm := P.σmin / ((P.p + 1)! : ℝ) * arStepConst P.q P.p (1 - P.θ)
    (arConstA P L (ordMax P.p κg)) (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
      (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)))
  set cT := 1 + |Real.log P.γ₁| / Real.log P.γ₂
  set A := (f x₀ - flow) / (P.η₁ * κΔm / 2)
  set Cc := Real.log (arqpIDASigmaMax P (L P.p) (ordMax P.p κg) / P.σ₀) / Real.log P.γ₂ + 2 +
    |Real.log P.γ₁| / Real.log P.γ₂
  set E := P.p * (P.q + 1) / |Real.log P.γh|
  set F := |Real.log (arKappaAcc P (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
    (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) (lipMax L P.p + ordMax P.p κg * P.κh)
    (arqpIDASigmaMax P (L P.p) (ordMax P.p κg)) (ordMax P.p κg) / P.κh)| / |Real.log P.γh| + 3
  refine ⟨(cT * A + |Cc|) + S.cost * (A + E + F),
    fun ε x σ δ δ₁ δs h D dd jk s acc hrun hrc _ => ?_⟩
  set m := epsMin P.q (fun j => ε j ^ arPi P.q P.p j)
  have hm : 0 < m := Optimization.epsMin_pos P.one_le_q fun j hj =>
    Real.rpow_pos_of_pos (hrun.eps_mem j hj).1 _
  have hmε : m ≤ epsMin P.q ε := epsMin_rpow_arPi_le hrun.eps_mem
  have hε := hrun.epsMin_pos
  have hε1 := hrun.epsMin_le_one
  have hm1 : m ≤ 1 := hmε.trans hε1
  have hA := one_le_arConstA (hf.one_le le_rfl) hrun.kappaMax_nonneg (P := P) (L := L)
  have hLb := hrun.one_le_Lbar hf.normalized
  have hκpos : 0 < κΔm := by
    have hk0 : 0 < arKappaHat P.q (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) :=
      lt_min (arKappaDelta1_pos (by linarith))
        (div_pos (sub_pos.2 P.θ_lt_one) (by positivity))
    have hC : 0 < arStepConst P.q P.p (1 - P.θ) (arConstA P L (ordMax P.p κg))
        (arKappaDelta1 P (lipMax L P.p + ordMax P.p κg * P.κh)
          (arqpIDASigmaMax P (L P.p) (ordMax P.p κg))) := by
      have := sub_pos.2 P.θ_lt_one
      unfold arStepConst arStepConstOf
      split_ifs <;> positivity
    have := P.σmin_pos
    positivity
  have hc : 0 < P.η₁ * κΔm / 2 * m := by have := P.η₁_pos; positivity
  obtain ⟨kε, hk, h1, h2⟩ := arqpIDA_complexity hf hb hrun hrc hc fun k hk hρ hnot =>
    (lemma_13_1_18 hf hrun (hrc k) hk hρ hnot).2
  refine ⟨kε, hk, ?_⟩
  have hdiv : (f x₀ - flow) / (P.η₁ * κΔm / 2 * m) = A / m := (div_div _ _ _).symm
  rw [hdiv] at h1 h2
  have hlog : |Real.log (epsMin P.q ε)| ≤ 1 / m :=
    (abs_log_le_inv hε hε1).trans (one_div_le_one_div_of_le hm hmε)
  have hcT : 0 ≤ cT := by have := P.log_γ₂_pos; positivity
  have hE : 0 ≤ E := by positivity
  have hF : 0 ≤ F := by positivity
  have hdivm : ∀ {c : ℝ}, 0 ≤ c → c ≤ c / m := fun hc => le_div_self hc hm hm1
  have h1' : (derivEvalCount (fun i => ¬ acc i) kε : ℝ) ≤ (cT * A + |Cc|) / m := by
    calc _ ≤ cT * (A / m) + Cc := h1
      _ ≤ cT * (A / m) + |Cc| / m :=
          add_le_add le_rfl ((le_abs_self _).trans (hdivm (abs_nonneg _)))
      _ = (cT * A + |Cc|) / m := by ring
  have h2' : (derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε :
      ℝ) ≤ (A + E + F) / m := by
    calc _ ≤ A / m + E * |Real.log (epsMin P.q ε)| + F := by
          have := h2; simp only [E, F] at this ⊢; linarith
      _ ≤ A / m + E * (1 / m) + F / m :=
          add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog hE)) (hdivm hF)
      _ = (A + E + F) / m := by ring
  have hcost : (0 : ℝ) ≤ S.cost := Nat.cast_nonneg _
  calc (derivEvalCount (fun i => ¬ acc i) kε : ℝ) + S.cost *
        derivEvalCount (fun i => acc i ∨ (¬ acc i ∧ P.η₁ ≤ arqpIDARatio f P D x s i)) kε
      ≤ (cT * A + |Cc|) / m + S.cost * ((A + E + F) / m) :=
        add_le_add h1' (mul_le_mul_of_nonneg_left h2' hcost)
    _ = ((cT * A + |Cc|) + S.cost * (A + E + F)) / m := by ring

end AR

/-! ### Runs driven by a scheme -/

section Existence

/-- TRqIDA runs driven by a scheme exist. Let the constants of Step 0, tolerances
$\epsilon \in (0, 1]^q$ with $\epsilon_{\min} \le \vartheta$ and oracle constants
$\kappa_{\nabla,i} \ge 0$ be given. For every finite derivative-approximation scheme $S$ that
produces derivatives up to degree $q$ and every starting point $x_0$, there is a TRqIDA run with
derivative estimates $S(x_k, h_k)$, which is the hypothesis of
`CartisGouldToint.Chapter13.theorem_13_2_1_i`. -/
theorem exists_algorithm_13_1_1_of_scheme {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : TRqIDAParams}
    {ε : ℕ → ℝ} (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hϑ : epsMin P.q ε ≤ P.ϑ)
    (hκg : ∀ i ∈ Finset.Icc 1 P.q, 0 ≤ κg i) {o : ℕ} (S : FiniteDerivativeApproxScheme f o P.q κg)
    (x₀ : ℝⁿ) :
    ∃ (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
      (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop),
      algorithm_13_1_1 f κg P ε x₀ x Δ h D dd jk s acc ∧ ∀ k, D k = S.est (x k) (h k) :=
  exists_algorithm_13_1_1 hε hϑ hκg x₀ S.est S.approx

/-- ARqpIDA runs driven by a scheme exist. Assume f.D0pL, and let the constants of Step 0 with
positive initial accuracies, tolerances $\epsilon \in (0, 1]^q$ with
$\epsilon_j \le \delta_{0,j}$ and oracle constants $\kappa_{\nabla,i} \ge 0$ be given. For every
finite derivative-approximation scheme $S$ that produces derivatives up to degree $p$ and every
starting point $x_0$, there is an ARqpIDA run with derivative estimates $S(x_k, h_k)$ and the
radii control at every iteration, which are the hypotheses of
`CartisGouldToint.Chapter13.theorem_13_2_1_ii`. -/
theorem exists_algorithm_13_1_2_of_scheme {f : ℝⁿ → ℝ} {κg : ℕ → ℝ} {P : ARqpIDAParams}
    {ε : ℕ → ℝ} {L : ℕ → ℝ} (hf : AssumptionD0pL f P.p L)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hεδ : ∀ j ∈ Finset.Icc 1 P.q, ε j ≤ P.δ₀ j)
    (hκg : ∀ i ∈ Finset.Icc 1 P.p, 0 ≤ κg i) (hh₀ : ∀ i ∈ Finset.Icc 1 P.p, 0 < P.h₀ i) {o : ℕ}
    (S : FiniteDerivativeApproxScheme f o P.p κg) (x₀ : ℝⁿ) :
    ∃ (x : ℕ → ℝⁿ) (σ : ℕ → ℝ) (δ δ₁ δs : ℕ → ℕ → ℝ) (h : ℕ → ℕ → ℝ)
      (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ) (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ)
      (acc : ℕ → Prop), algorithm_13_1_2 f κg P ε x₀ x σ δ δ₁ δs h D dd jk s acc ∧
        (∀ k, D k = S.est (x k) (h k)) ∧
        ∀ k, RadiiControl P ε (lipMax L P.p + ordMax P.p κg * P.κh) σ δs s acc k :=
  exists_algorithm_13_1_2 S.est hf hε hεδ hκg hh₀ x₀ fun y h' hh =>
    S.approx y h' fun i hi => (hh i hi).1

/-- TRqIDA with forward-difference gradients. Let $q = 1$, let $f$ be $C^1$ with
$\|\nabla f(y) - \nabla f(z)\| \le L \|y - z\|$ for all $y, z$ and $L \ge 0$, and let
$\epsilon \in (0, 1]^q$ with $\epsilon_{\min} \le \vartheta$. Then for every starting point
$x_0$ there is a TRqIDA run with $\kappa_{\nabla,1} = \sqrt{n} L / 2$ whose gradient estimate at
$x_k$ is the forward-difference gradient with step $h_{k,1}$. The method uses function values
only.

The derivative estimates are `Optimization.gradientJet` of the exact jet with the
forward-difference gradient `FiniteDifference.fdGradient`. -/
theorem exists_algorithm_13_1_1_fdGradient {f : ℝⁿ → ℝ} {P : TRqIDAParams} {ε : ℕ → ℝ}
    {L : ℝ} (hq : P.q = 1) (hf : ContDiff ℝ 1 f)
    (hL : ∀ y z, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ L * ‖y - z‖) (hL0 : 0 ≤ L)
    (hε : ∀ j ∈ Finset.Icc 1 P.q, ε j ∈ Set.Ioc 0 1) (hϑ : epsMin P.q ε ≤ P.ϑ) (x₀ : ℝⁿ) :
    ∃ (x : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (h : ℕ → ℕ → ℝ) (D : ℕ → FormalMultilinearSeries ℝ ℝⁿ ℝ)
      (dd : ℕ → ℕ → ℝⁿ) (jk : ℕ → ℕ) (s : ℕ → ℝⁿ) (acc : ℕ → Prop),
      algorithm_13_1_1 f (fun _ => √n * L / 2) P ε x₀ x Δ h D dd jk s acc ∧
        ∀ k, D k = gradientJet (ftaylorSeries ℝ f (x k))
          (FiniteDifference.fdGradient f (h k 1) (x k)) :=
  exists_algorithm_13_1_1 hε hϑ (fun _ _ => by positivity) x₀
    (fdGradientScheme f hf hL).est fun y h' hh => by
      rw [hq]; exact (fdGradientScheme f hf hL).approx y h' (hq ▸ hh)

end Existence

end CartisGouldToint.Chapter13
