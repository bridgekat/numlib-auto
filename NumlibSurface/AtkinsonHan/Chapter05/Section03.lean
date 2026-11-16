/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Numlib.Analysis.Calculus.MeanValue
import Numlib.Analysis.Convex.Gateaux
import Numlib.IntegralEquations.Basic

/-!
# Atkinson and Han, Section 5.3: Differential Calculus for Nonlinear Operators

This module formalizes Section 5.3 of [han2009theoretical]: the Fréchet and Gâteaux derivatives of a
nonlinear operator between real normed spaces, the rules of differentiation, the mean value
inequality, the second-order Taylor remainder, partial derivatives, and, in Section 5.3.4, convex
functionals. An operator $f$ has the **Fréchet derivative** $A \in \mathcal{L}(V, W)$ at $u_0$ if
$f(u_0 + h) = f(u_0) + Ah + o(\|h\|)$, and the **Gâteaux derivative** $A$ at $u_0$ if
$\lim_{t \to 0} (f(u_0 + th) - f(u_0))/t = Ah$ for every direction $h$. The results on convex
functionals specialize the backbone module `Numlib.Analysis.Convex.Gateaux`, and the Taylor estimate
specializes `Numlib.Analysis.Calculus.MeanValue`.

## Main definitions

* Definition 5.3.2, `AtkinsonHan.Chapter05.HasGateauxDerivAt`: $A$ is the Gâteaux derivative of $f$
  at $u_0$.

## Main results

* Definition 5.3.1, `AtkinsonHan.Chapter05.fderiv_unique`: the Fréchet derivative is unique.
* Definition 5.3.1, `AtkinsonHan.Chapter05.hasFDerivAt_iff_isLittleO`: the Fréchet derivative in the
  little-$o$ form (5.3.5).
* Definition 5.3.1, `AtkinsonHan.Chapter05.hasFDerivWithinAt_iff_of_mem_nhds`: at an interior point
  of the domain, the derivative within the domain is the derivative at the point.
* Proposition 5.3.3, `AtkinsonHan.Chapter05.proposition_5_3_3`: a Fréchet differentiable operator is
  continuous.
* Proposition 5.3.4(i), `AtkinsonHan.Chapter05.HasFDerivAt.hasGateauxDerivAt`: a Fréchet derivative
  is a Gâteaux derivative.
* Proposition 5.3.4(ii), `AtkinsonHan.Chapter05.hasFDerivAt_of_hasGateauxDerivAt_uniform`:
  difference quotients that converge uniformly over the unit directions give a Fréchet derivative.
* Proposition 5.3.4(iii), `AtkinsonHan.Chapter05.hasFDerivAt_of_hasGateauxDerivAt_continuousAt`: a
  Gâteaux derivative that exists near $u_0$ and is continuous at $u_0$ is a Fréchet derivative.
* Proposition 5.3.5, `AtkinsonHan.Chapter05.proposition_5_3_5`: the sum rule;
  `AtkinsonHan.Chapter05.HasGateauxDerivAt.add` and
  `AtkinsonHan.Chapter05.HasGateauxDerivAt.const_smul` are the Gâteaux versions.
* Proposition 5.3.6, `AtkinsonHan.Chapter05.proposition_5_3_6`: the product rule for a bounded
  bilinear map.
* Proposition 5.3.7, `AtkinsonHan.Chapter05.proposition_5_3_7`: the chain rule;
  `AtkinsonHan.Chapter05.HasGateauxDerivAt.comp` is the clause with a Gâteaux differentiable inner
  map.
* Example 5.3.8, `AtkinsonHan.Chapter05.example_5_3_8`: an affine map has a constant derivative.
* Example 5.3.9, `AtkinsonHan.Chapter05.example_5_3_9`: the derivative of a map from $\mathbb{R}^m$
  to $\mathbb{R}^n$ is the Jacobian matrix.
* Example 5.3.10, `AtkinsonHan.Chapter05.example_5_3_10`: the derivative of the Urysohn integral
  operator on $C[a, b]$ is a Fredholm integral operator.
* Proposition 5.3.11, `AtkinsonHan.Chapter05.proposition_5_3_11` and
  `AtkinsonHan.Chapter05.proposition_5_3_11_iSup`: the mean value inequality (5.3.7).
* Corollary 5.3.12, `AtkinsonHan.Chapter05.corollary_5_3_12`: an operator with zero derivative on a
  connected open set is constant there.
* Proposition 5.3.13, `AtkinsonHan.Chapter05.proposition_5_3_13`: the second-order Taylor remainder
  under a bound on $F''$; `AtkinsonHan.Chapter05.norm_sub_sub_fderiv_le_half_mul_sq` is the form
  under a Lipschitz bound on $F'$, which Section 5.4 uses.
* Definition 5.3.14 and Proposition 5.3.15, `AtkinsonHan.Chapter05.proposition_5_3_15_fst` and
  `AtkinsonHan.Chapter05.proposition_5_3_15_snd`: a Fréchet differentiable map of two variables has
  partial derivatives.
* Equation (5.3.8), `AtkinsonHan.Chapter05.equation_5_3_8`: the total derivative is the sum of the
  partial derivatives.
* Proposition 5.3.15, `AtkinsonHan.Chapter05.proposition_5_3_15_of_partial`: continuous partial
  derivatives give a Fréchet derivative.
* Corollary 5.3.16, `AtkinsonHan.Chapter05.corollary_5_3_16`: $f$ is continuously differentiable
  near a point if and only if its partial derivatives exist and are continuous there.
* Theorem 5.3.17, `AtkinsonHan.Chapter05.theorem_5_3_17`: convexity through the tangent plane
  inequality and through monotonicity of the derivative.
* Theorem 5.3.18, `AtkinsonHan.Chapter05.theorem_5_3_18`: the strict version of Theorem 5.3.17.
* Theorem 5.3.19, `AtkinsonHan.Chapter05.theorem_5_3_19` and
  `AtkinsonHan.Chapter05.theorem_5_3_19_submodule`: a minimizer of a convex functional is
  characterized by the variational inequality (5.3.10), and over a subspace by the variational
  equation (5.3.11).

## Implementation notes

* The Fréchet derivative of Definition 5.3.1 is Mathlib's `HasFDerivAt`, so only the Gâteaux
  derivative has a definition here. The book requires $u_0$ to be an interior point of the domain
  $K$, that is $B(u_0, r) \subseteq K$ for some $r > 0$. This is `K ∈ 𝓝 u₀`, and there
  `HasFDerivWithinAt` and `HasFDerivAt` agree.
* `AtkinsonHan.Chapter05.HasGateauxDerivAt` is built from Mathlib's `HasLineDerivAt`, one direction
  at a time.

## Deviations from the source

* **Theorem 5.3.19** (generalization). The book states that the minimization problem and the
  variational inequality (5.3.10) are equivalent as problems; here they are equivalent at each point
  $u \in K$. See `AtkinsonHan.Chapter05.theorem_5_3_19`.

## Not formalized

* The exercises of Section 5.3.
-/

open Filter Set Topology

namespace AtkinsonHan.Chapter05

section Frechet

variable {V₁ V₂ V₃ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]
  [NormedAddCommGroup V₂] [NormedSpace ℝ V₂] [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]

/-- **Definition 5.3.1** of [han2009theoretical], uniqueness. Let $V_1$ and $V_2$ be real normed
spaces and $f : V_1 \to V_2$. If $A, B \in \mathcal{L}(V_1, V_2)$ are both Fréchet derivatives
of $f$ at $u_0$, then $A = B$. -/
theorem fderiv_unique {f : V₁ → V₂} {A B : V₁ →L[ℝ] V₂} {u₀ : V₁} (hA : HasFDerivAt f A u₀)
    (hB : HasFDerivAt f B u₀) : A = B :=
  hA.unique hB

/-- **Definition 5.3.1** of [han2009theoretical], in the little-$o$ form (5.3.5). Let
$f : V_1 \to V_2$ and $A \in \mathcal{L}(V_1, V_2)$. Then $A$ is the Fréchet derivative of $f$
at $u_0$ if and only if
$$f(u_0 + h) - f(u_0) - Ah = o(\|h\|) \quad \text{as } h \to 0.$$
-/
theorem hasFDerivAt_iff_isLittleO {f : V₁ → V₂} {A : V₁ →L[ℝ] V₂} {u₀ : V₁} :
    HasFDerivAt f A u₀ ↔ (fun h => f (u₀ + h) - f u₀ - A h) =o[𝓝 0] fun h => h :=
  hasFDerivAt_iff_isLittleO_nhds_zero

/-- **Definition 5.3.1** of [han2009theoretical], the interior point condition. Let
$f : V_1 \to V_2$, $A \in \mathcal{L}(V_1, V_2)$ and $K \subseteq V_1$, and let $u_0$ be an
interior point of $K$. Then $A$ is the Fréchet derivative of $f$ at $u_0$ relative to $K$ if and
only if $A$ is the Fréchet derivative of $f$ at $u_0$.

The book requires $B(u_0, r) \subseteq K$ for some $r > 0$. This is the hypothesis `K ∈ 𝓝 u₀`. -/
theorem hasFDerivWithinAt_iff_of_mem_nhds {f : V₁ → V₂} {A : V₁ →L[ℝ] V₂} {K : Set V₁} {u₀ : V₁}
    (hK : K ∈ 𝓝 u₀) : HasFDerivWithinAt f A K u₀ ↔ HasFDerivAt f A u₀ :=
  ⟨fun h => h.hasFDerivAt hK, fun h => h.hasFDerivWithinAt⟩

/-- **Proposition 5.3.3** of [han2009theoretical]. If $f : V_1 \to V_2$ has a Fréchet derivative at
$u_0$, then $f$ is continuous at $u_0$. -/
theorem proposition_5_3_3 {f : V₁ → V₂} {A : V₁ →L[ℝ] V₂} {u₀ : V₁} (hf : HasFDerivAt f A u₀) :
    ContinuousAt f u₀ :=
  hf.continuousAt

/-- **Proposition 5.3.5** of [han2009theoretical] (sum rule). If $f, g : V_1 \to V_2$ have the
Fréchet derivatives $A$ and $B$ at $u_0$ and $c \in \mathbb{R}$, then
$u \mapsto f(u) + c\, g(u)$ has the Fréchet derivative $A + cB$ at $u_0$. -/
theorem proposition_5_3_5 {f g : V₁ → V₂} {A B : V₁ →L[ℝ] V₂} {u₀ : V₁} (hf : HasFDerivAt f A u₀)
    (hg : HasFDerivAt g B u₀) (c : ℝ) :
    HasFDerivAt (fun u => f u + c • g u) (A + c • B) u₀ :=
  hf.add (hg.const_smul c)

/-- **Proposition 5.3.6** of [han2009theoretical] (product rule). Let $V$, $V_1$, $V_2$ and $W$ be
real normed spaces and let $b : V_1 \times V_2 \to W$ be a bounded bilinear map. If
$f_1 : V \to V_1$ and $f_2 : V \to V_2$ have the Fréchet derivatives $A_1$ and $A_2$ at $u_0$,
then $B(u) = b(f_1(u), f_2(u))$ has a Fréchet derivative at $u_0$, given by
$$B'(u_0) h = b(A_1 h, f_2(u_0)) + b(f_1(u_0), A_2 h).$$

The bilinear map is `b : V₁ →L[ℝ] V₂ →L[ℝ] W`. -/
theorem proposition_5_3_6 {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W]
    [NormedSpace ℝ W] (b : V₁ →L[ℝ] V₂ →L[ℝ] W) {f₁ : V → V₁} {f₂ : V → V₂} {A₁ : V →L[ℝ] V₁}
    {A₂ : V →L[ℝ] V₂} {u₀ : V} (h₁ : HasFDerivAt f₁ A₁ u₀) (h₂ : HasFDerivAt f₂ A₂ u₀) :
    HasFDerivAt (fun u => b (f₁ u) (f₂ u))
      ((b.flip (f₂ u₀)).comp A₁ + (b (f₁ u₀)).comp A₂) u₀ := by
  have h := b.hasFDerivAt_of_bilinear h₁ h₂
  convert h using 1
  ext u
  simp [ContinuousLinearMap.precompR, ContinuousLinearMap.precompL, add_comm]

/-- **Proposition 5.3.7** of [han2009theoretical] (chain rule). Let $f : V_1 \to V_2$ and
$g : V_2 \to V_3$. If $f$ has the Fréchet derivative $A$ at $u_0$ and $g$ has the Fréchet
derivative $B$ at $f(u_0)$, then $g \circ f$ has the Fréchet derivative $BA$ at $u_0$.

The clause with a Gâteaux differentiable inner map is
`AtkinsonHan.Chapter05.HasGateauxDerivAt.comp`. -/
theorem proposition_5_3_7 {f : V₁ → V₂} {g : V₂ → V₃} {A : V₁ →L[ℝ] V₂} {B : V₂ →L[ℝ] V₃} {u₀ : V₁}
    (hg : HasFDerivAt g B (f u₀)) (hf : HasFDerivAt f A u₀) :
    HasFDerivAt (fun u => g (f u)) (B.comp A) u₀ :=
  hg.comp u₀ hf

/-- **Example 5.3.8** of [han2009theoretical]. Let $L \in \mathcal{L}(V_1, V_2)$ and $b \in V_2$.
The affine map $f(v) = Lv + b$ has the Fréchet derivative $L$ at every point $u_0$. -/
theorem example_5_3_8 (L : V₁ →L[ℝ] V₂) (b : V₂) (u₀ : V₁) :
    HasFDerivAt (fun v => L v + b) L u₀ :=
  L.hasFDerivAt.add_const b

/-- **Example 5.3.9** of [han2009theoretical]. Let $T : \mathbb{R}^m \to \mathbb{R}^n$ have the
Fréchet derivative $A$ at $v_0$. Then the matrix of $A$ is the **Jacobian matrix** of $T$ at
$v_0$: for all $i$ and $j$, the function $s \mapsto T_i(v_0 + (s - v_{0,j}) e_j)$ is
differentiable at $s = v_{0,j}$, and its derivative $(\partial T_i / \partial x_j)(v_0)$ is the
$(i, j)$ entry of the matrix of $A$.

The partial derivative is a `HasDerivAt` statement for the function
`s ↦ T (Function.update v₀ j s) i`, which replaces the $j$-th coordinate of $v_0$ by $s$. The
matrix of $A$ is `LinearMap.toMatrix'`. The coordinates are indexed by `Fin m` and `Fin n`, from
$0$. -/
theorem example_5_3_9 {m n : ℕ} {T : (Fin m → ℝ) → (Fin n → ℝ)}
    {A : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)} {v₀ : Fin m → ℝ} (hT : HasFDerivAt T A v₀)
    (i : Fin n) (j : Fin m) :
    HasDerivAt (fun s : ℝ => T (Function.update v₀ j s) i)
      (LinearMap.toMatrix' (A : (Fin m → ℝ) →ₗ[ℝ] Fin n → ℝ) i j) (v₀ j) := by
  have hupd : HasDerivAt (Function.update v₀ j) (Pi.single j (1 : ℝ)) (v₀ j) := by
    have h := (hasFDerivAt_update (𝕜 := ℝ) (i := j) v₀ (v₀ j)).hasDerivAt
    refine h.congr_deriv ?_
    ext k
    by_cases hk : k = j <;> simp [hk]
  have hcomp : HasDerivAt (fun s : ℝ => T (Function.update v₀ j s)) (A (Pi.single j 1)) (v₀ j) :=
    hT.comp_hasDerivAt_of_eq (v₀ j) hupd (by rw [Function.update_eq_self])
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ)
    i).hasFDerivAt.comp_hasDerivAt (v₀ j) hcomp

end Frechet

section Urysohn

open IntegralOperator

/-- **Example 5.3.10** of [han2009theoretical]. Let $a \le b$, and let $k$ and $k_z$ be continuous
functions on $[a, b] \times [a, b] \times \mathbb{R}$ such that $k_z(x, y, z)$ is the derivative
of $t \mapsto k(x, y, t)$ at $t = z$. Then the Urysohn integral operator
$$\mathcal{K}(u)(x) = \int_a^b k(x, y, u(y))\, dy$$
on $C[a, b]$ has, at every $u \in C[a, b]$, the Fréchet derivative
$$\mathcal{K}'(u) v(x) = \int_a^b k_z(x, y, u(y))\, v(y)\, dy,$$
the Fredholm integral operator with the kernel $k_z(x, y, u(y))$.

The operators are `IntegralOperator.urysohn` and `IntegralOperator.fredholm`, and the kernel is
`IntegralOperator.urysohnDerivKernel`. -/
theorem example_5_3_10 {a b : ℝ} (hab : a ≤ b) {k kz : C(Icc a b × Icc a b × ℝ, ℝ)}
    (hk : ∀ (x y : Icc a b) (z : ℝ), HasDerivAt (fun t => k (x, y, t)) (kz (x, y, z)) z)
    (u : C(Icc a b, ℝ)) :
    HasFDerivAt (urysohn hab k) (fredholm hab (urysohnDerivKernel kz u)) u :=
  hasFDerivAt_urysohn hab hk u

end Urysohn

section Gateaux

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- **Definition 5.3.2** of [han2009theoretical]. Let $V$ and $W$ be real normed spaces,
$f : V \to W$ and $A \in \mathcal{L}(V, W)$. Then $A$ is the **Gâteaux derivative** of $f$ at
$u_0$ if
$$\lim_{t \to 0} \frac{f(u_0 + th) - f(u_0)}{t} = Ah \quad \text{for every } h \in V.$$

Each of these limits is Mathlib's `HasLineDerivAt`. The difference quotient form is
`AtkinsonHan.Chapter05.hasGateauxDerivAt_iff_tendsto`. -/
def HasGateauxDerivAt (f : V → W) (A : V →L[ℝ] W) (u₀ : V) : Prop :=
  ∀ h : V, HasLineDerivAt ℝ f (A h) u₀ h

/-- The Gâteaux derivative of Definition 5.3.2 as a limit of difference quotients: $A$ is the
Gâteaux derivative of $f$ at $u_0$ if and only if $t^{-1}(f(u_0 + th) - f(u_0)) \to Ah$ as
$t \to 0$ with $t \neq 0$, for every $h \in V$. -/
theorem hasGateauxDerivAt_iff_tendsto {f : V → W} {A : V →L[ℝ] W} {u₀ : V} :
    HasGateauxDerivAt f A u₀ ↔
      ∀ h : V, Tendsto (fun t : ℝ => t⁻¹ • (f (u₀ + t • h) - f u₀)) (𝓝[≠] 0) (𝓝 (A h)) := by
  simp only [HasGateauxDerivAt, hasLineDerivAt_iff_tendsto_slope_zero]

/-- The Gâteaux derivative is unique: if $A$ and $B$ are both Gâteaux derivatives of $f$ at $u_0$,
then $A = B$. -/
theorem HasGateauxDerivAt.unique {f : V → W} {A B : V →L[ℝ] W} {u₀ : V}
    (hA : HasGateauxDerivAt f A u₀) (hB : HasGateauxDerivAt f B u₀) : A = B := by
  ext h
  exact (hA h).unique (hB h)

/-- **Proposition 5.3.4(i)** of [han2009theoretical]. If $A$ is the Fréchet derivative of
$f : V \to W$ at $u_0$, then $A$ is also the Gâteaux derivative of $f$ at $u_0$. -/
theorem HasFDerivAt.hasGateauxDerivAt {f : V → W} {A : V →L[ℝ] W} {u₀ : V}
    (hf : HasFDerivAt f A u₀) : HasGateauxDerivAt f A u₀ := fun h => hf.hasLineDerivAt h

/-- **Proposition 5.3.5** of [han2009theoretical], the sum of two Gâteaux derivatives. If $A$ and
$B$ are the Gâteaux derivatives of $f$ and $g$ at $u_0$, then $A + B$ is the Gâteaux derivative
of $f + g$ at $u_0$. -/
theorem HasGateauxDerivAt.add {f g : V → W} {A B : V →L[ℝ] W} {u₀ : V}
    (hf : HasGateauxDerivAt f A u₀) (hg : HasGateauxDerivAt g B u₀) :
    HasGateauxDerivAt (fun u => f u + g u) (A + B) u₀ := fun h =>
  HasDerivAt.add (hf h) (hg h)

/-- **Proposition 5.3.5** of [han2009theoretical], scalar multiples of a Gâteaux derivative. If $A$
is the Gâteaux derivative of $f$ at $u_0$ and $c \in \mathbb{R}$, then $cA$ is the Gâteaux
derivative of $cf$ at $u_0$. -/
theorem HasGateauxDerivAt.const_smul {f : V → W} {A : V →L[ℝ] W} {u₀ : V}
    (hf : HasGateauxDerivAt f A u₀) (c : ℝ) :
    HasGateauxDerivAt (fun u => c • f u) (c • A) u₀ := fun h =>
  HasDerivAt.const_smul c (hf h)

/-- **Proposition 5.3.7** of [han2009theoretical], the mixed chain rule. Let $f : V \to W$ and
$g : W \to X$. If $f$ has the Gâteaux derivative $A$ at $u_0$ and $g$ has the Fréchet derivative
$B$ at $f(u_0)$, then $g \circ f$ has the Gâteaux derivative $BA$ at $u_0$.

Only the outer map needs a Fréchet derivative, because the composite is tested one direction at
a time, and along each direction $g$ is composed with a curve. The clause with two Fréchet
derivatives is `AtkinsonHan.Chapter05.proposition_5_3_7`. -/
theorem HasGateauxDerivAt.comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : V → W}
    {g : W → X} {A : V →L[ℝ] W} {B : W →L[ℝ] X} {u₀ : V} (hg : HasFDerivAt g B (f u₀))
    (hf : HasGateauxDerivAt f A u₀) : HasGateauxDerivAt (fun u => g (f u)) (B.comp A) u₀ := by
  intro h
  exact hg.comp_hasDerivAt_of_eq 0 (hf h) (by simp)

/-- **Proposition 5.3.4(ii)** of [han2009theoretical]. Let $f : V \to W$ and
$A \in \mathcal{L}(V, W)$. Assume that the difference quotients converge to $Ah$ uniformly over
the unit directions: for every $\varepsilon > 0$ there is $\delta > 0$ such that
$$\left\| \frac{f(u_0 + th) - f(u_0)}{t} - Ah \right\| \le \varepsilon \quad \text{for all } h
  \text{ with } \|h\| = 1 \text{ and all } 0 < t < \delta.$$
Then $A$ is the Fréchet derivative of $f$ at $u_0$. -/
theorem hasFDerivAt_of_hasGateauxDerivAt_uniform {f : V → W} {A : V →L[ℝ] W} {u₀ : V}
    (hunif : ∀ ε > 0, ∃ δ > 0, ∀ h : V, ‖h‖ = 1 → ∀ t : ℝ, 0 < t → t < δ →
      ‖t⁻¹ • (f (u₀ + t • h) - f u₀) - A h‖ ≤ ε) :
    HasFDerivAt f A u₀ := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hunif ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : V) hδ] with h hh
  rcases eq_or_ne h 0 with rfl | h0
  · simp
  have hnpos : 0 < ‖h‖ := norm_pos_iff.2 h0
  have hlt : ‖h‖ < δ := by simpa [dist_eq_norm] using hh
  have he : ‖‖h‖⁻¹ • h‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnpos.ne']
  have hkey := hbound (‖h‖⁻¹ • h) he ‖h‖ hnpos hlt
  have hsm : ‖h‖ • (‖h‖⁻¹ • h) = h := by
    rw [smul_smul, mul_inv_cancel₀ hnpos.ne', one_smul]
  have hexp : f (u₀ + h) - f u₀ - A h
      = ‖h‖ • (‖h‖⁻¹ • (f (u₀ + ‖h‖ • (‖h‖⁻¹ • h)) - f u₀) - A (‖h‖⁻¹ • h)) := by
    rw [hsm, smul_sub, smul_smul, mul_inv_cancel₀ hnpos.ne', one_smul, ← map_smul, hsm]
  rw [hexp, norm_smul, norm_norm, hsm]
  calc ‖h‖ * ‖‖h‖⁻¹ • (f (u₀ + h) - f u₀) - A (‖h‖⁻¹ • h)‖ ≤ ‖h‖ * ε := by
        gcongr
        rwa [hsm] at hkey
    _ = ε * ‖h‖ := mul_comm _ _

/-- A Gâteaux derivative gives the derivative of a restriction to a line at any parameter. If $A$ is
the Gâteaux derivative of $f$ at $u + th$, then $s \mapsto f(u + sh)$ has the derivative $Ah$ at
$s = t$.

Definition 5.3.2 gives this derivative only at $s = 0$; a translation of the parameter gives it
at $s = t$. The mean value argument of
`AtkinsonHan.Chapter05.hasFDerivAt_of_hasGateauxDerivAt_continuousAt` uses it in this form. It
is `HasLineDerivAt.hasDerivAt_line` in the single direction $h$. -/
theorem HasGateauxDerivAt.hasDerivAt_line {f : V → W} {A : V →L[ℝ] W} {u h : V} {t : ℝ}
    (hG : HasGateauxDerivAt f A (u + t • h)) :
    HasDerivAt (fun s : ℝ => f (u + s • h)) (A h) t :=
  (hG h).hasDerivAt_line

/-- **Proposition 5.3.4(iii)** of [han2009theoretical]. Let $f : V \to W$, $u_0 \in V$ and $r > 0$.
Assume that $f$ has a Gâteaux derivative $A(u)$ at every $u$ in the ball $B(u_0, r)$, and that
the map $u \mapsto A(u)$ from $V$ to $\mathcal{L}(V, W)$ is continuous at $u_0$. Then $A(u_0)$
is the Fréchet derivative of $f$ at $u_0$.

The proof is the book's: it applies the mean value inequality to
$s \mapsto f(u_0 + sh) - s A(u_0) h$ on $[0, 1]$. -/
theorem hasFDerivAt_of_hasGateauxDerivAt_continuousAt {f : V → W} {A : V → V →L[ℝ] W} {u₀ : V}
    {r : ℝ} (hr : 0 < r) (hG : ∀ u ∈ Metric.ball u₀ r, HasGateauxDerivAt f (A u) u)
    (hA : ContinuousAt A u₀) : HasFDerivAt f (A u₀) u₀ := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδA⟩ : ∃ δ > 0, ∀ u : V, ‖u - u₀‖ < δ → ‖A u - A u₀‖ ≤ ε := by
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hA ε hε
    refine ⟨δ, hδ, fun u hu => ?_⟩
    rw [← dist_eq_norm]
    exact (hd (by rwa [dist_eq_norm])).le
  filter_upwards [Metric.ball_mem_nhds (0 : V) (lt_min hδ hr)] with h hh
  have hnorm : ‖h‖ < min δ r := by simpa [dist_eq_norm] using hh
  have hle : ∀ t ∈ Icc (0 : ℝ) 1, ‖(u₀ + t • h) - u₀‖ ≤ ‖h‖ := by
    intro t ht
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    nlinarith [norm_nonneg h, ht.2, ht.1]
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, u₀ + t • h ∈ Metric.ball u₀ r := fun t ht => by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt (hle t ht) (lt_of_lt_of_le hnorm (min_le_right _ _))
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f (u₀ + s • h) - s • A u₀ h) (A (u₀ + t • h) h - A u₀ h) t := by
    intro t ht
    have h1 := (hG _ (hmem t ht)).hasDerivAt_line (t := t)
    have h2 : HasDerivAt (fun s : ℝ => s • A u₀ h) (A u₀ h) t := by
      simpa using (hasDerivAt_id t).smul_const (A u₀ h)
    exact h1.sub h2
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖A (u₀ + t • h) h - A u₀ h‖ ≤ ε * ‖h‖ := by
    intro t ht
    have hd : ‖A (u₀ + t • h) - A u₀‖ ≤ ε :=
      hδA _ (lt_of_le_of_lt (hle t ht) (lt_of_lt_of_le hnorm (min_le_left _ _)))
    calc ‖A (u₀ + t • h) h - A u₀ h‖ = ‖(A (u₀ + t • h) - A u₀) h‖ := by rw [sub_apply]
      _ ≤ ‖A (u₀ + t • h) - A u₀‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg _)
  have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hderiv t ht).hasDerivWithinAt) hbound (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one)
  rw [show f (u₀ + h) - f u₀ - A u₀ h = f (u₀ + h) - A u₀ h - f u₀ from by abel]
  simpa using hmvt

end Gateaux

section MeanValue

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- **Proposition 5.3.11** of [han2009theoretical] (mean value inequality (5.3.7)), with an explicit
bound on the derivative. Let $F : V \to W$ have the Fréchet derivative $F'(z)$ at every point
$z$ of the segment $[u, w]$, and let $\|F'(z)\| \le C$ for all $z \in [u, w]$. Then
$$\|F(u) - F(w)\| \le C \|u - w\|.$$
-/
theorem proposition_5_3_11 {F : V → W} {F' : V → V →L[ℝ] W} {u w : V} {C : ℝ}
    (hF : ∀ z ∈ segment ℝ u w, HasFDerivAt F (F' z) z)
    (hC : ∀ z ∈ segment ℝ u w, ‖F' z‖ ≤ C) : ‖F u - F w‖ ≤ C * ‖u - w‖ :=
  (convex_segment u w).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hF z hz).hasFDerivWithinAt) hC (right_mem_segment ℝ u w)
    (left_mem_segment ℝ u w)

/-- **Proposition 5.3.11** of [han2009theoretical] (mean value inequality (5.3.7)), in the book's
form. Let $F : V \to W$ have the Fréchet derivative $F'(z)$ at every point $z$ of the segment
$[u, w]$, and let $F' : V \to \mathcal{L}(V, W)$ be continuous. Then
$$\|F(u) - F(w)\| \le \sup_{0 \le \theta \le 1} \|F'((1 - \theta) u + \theta w)\| \, \|u -
  w\|.$$

The continuity of $F'$ is a hypothesis of the book. It makes the supremum finite, so that `iSup`
is a true supremum. -/
theorem proposition_5_3_11_iSup {F : V → W} {F' : V → V →L[ℝ] W} {u w : V}
    (hF : ∀ z ∈ segment ℝ u w, HasFDerivAt F (F' z) z) (hF' : Continuous F') :
    ‖F u - F w‖ ≤ (⨆ θ : Icc (0 : ℝ) 1, ‖F' ((1 - (θ : ℝ)) • u + (θ : ℝ) • w)‖) * ‖u - w‖ := by
  set c : Icc (0 : ℝ) 1 → ℝ := fun θ => ‖F' ((1 - (θ : ℝ)) • u + (θ : ℝ) • w)‖ with hc
  have hcont : Continuous c := by
    fun_prop
  have hbdd : BddAbove (range c) := (isCompact_range hcont).bddAbove
  refine proposition_5_3_11 hF fun z hz => ?_
  rw [segment_eq_image ℝ u w] at hz
  obtain ⟨θ, hθ, rfl⟩ := hz
  exact le_ciSup hbdd ⟨θ, hθ⟩

/-- **Corollary 5.3.12** of [han2009theoretical]. Let $K \subseteq V$ be open and connected, and let
$F : V \to W$ be differentiable on $K$ with $F'(u) = 0$ for all $u \in K$. Then $F$ is constant
on $K$: $F(u) = F(v)$ for all $u, v \in K$.

The connectedness is `IsPreconnected K`; it differs from connectedness only for the empty set. -/
theorem corollary_5_3_12 {F : V → W} {K : Set V} (hK : IsOpen K) (hKc : IsPreconnected K)
    (hF : DifferentiableOn ℝ F K) (hF' : K.EqOn (fderiv ℝ F) 0) {u v : V} (hu : u ∈ K)
    (hv : v ∈ K) : F u = F v :=
  hK.is_const_of_fderiv_eq_zero hKc hF hF' hu hv

/-- The Taylor estimate for an operator with a Lipschitz continuous derivative. Let $s \subseteq V$
be convex, and let $F : V \to W$ have the Fréchet derivative $F'(z)$ at every $z \in s$, with
$\|F'(z) - F'(w)\| \le L \|z - w\|$ for all $z, w \in s$. Then for all $x, y \in s$,
$$\|F(y) - F(x) - F'(x)(y - x)\| \le \frac{L}{2} \|y - x\|^2.$$

This is the sharp form of Proposition 5.3.13, and the estimate (5.4.5) of Section 5.4 rests on
it. It is `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le` under the two-sided
Lipschitz condition of the book. -/
theorem norm_sub_sub_fderiv_le_half_mul_sq {s : Set V} (hs : Convex ℝ s) {F : V → W}
    {F' : V → V →L[ℝ] W} {L : ℝ} (hF : ∀ z ∈ s, HasFDerivAt F (F' z) z)
    (hL : ∀ z ∈ s, ∀ w ∈ s, ‖F' z - F' w‖ ≤ L * ‖z - w‖) {x y : V} (hx : x ∈ s) (hy : y ∈ s) :
    ‖F y - F x - F' x (y - x)‖ ≤ L / 2 * ‖y - x‖ ^ 2 :=
  hs.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le hF hx hy fun z hz => hL z hz x hx

/-- **Proposition 5.3.13** of [han2009theoretical]. Let $F : V \to W$ have the Fréchet derivative
$F'(z)$ at every point $z$ of the segment $[u_0, u_0 + h]$, let $F'$ have the Fréchet derivative
$F''(z)$ there, and let $\|F''(z)\| \le C$ on the segment. Then
$$\|F(u_0 + h) - F(u_0) - F'(u_0) h\| \le \frac{C}{2} \|h\|^2.$$
-/
theorem proposition_5_3_13 {F : V → W} {F' : V → V →L[ℝ] W} {F'' : V → V →L[ℝ] V →L[ℝ] W} {u₀ h : V}
    {C : ℝ} (hF : ∀ z ∈ segment ℝ u₀ (u₀ + h), HasFDerivAt F (F' z) z)
    (hF' : ∀ z ∈ segment ℝ u₀ (u₀ + h), HasFDerivAt F' (F'' z) z)
    (hC : ∀ z ∈ segment ℝ u₀ (u₀ + h), ‖F'' z‖ ≤ C) :
    ‖F (u₀ + h) - F u₀ - F' u₀ h‖ ≤ C / 2 * ‖h‖ ^ 2 := by
  have hs : Convex ℝ (segment ℝ u₀ (u₀ + h)) := convex_segment _ _
  have hL : ∀ z ∈ segment ℝ u₀ (u₀ + h), ∀ w ∈ segment ℝ u₀ (u₀ + h),
      ‖F' z - F' w‖ ≤ C * ‖z - w‖ := fun z hz w hw =>
    hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun p hp => (hF' p hp).hasFDerivWithinAt) hC hw hz
  have hmain := norm_sub_sub_fderiv_le_half_mul_sq hs hF hL (left_mem_segment ℝ u₀ (u₀ + h))
    (right_mem_segment ℝ u₀ (u₀ + h))
  simpa using hmain

end MeanValue

section Partial

variable {U V W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Definition 5.3.14** and **Proposition 5.3.15** of [han2009theoretical], the partial derivative
in the first variable. Let $f : U \times V \to W$ have the Fréchet derivative $A$ at
$p = (u_0, v_0)$. Then $u \mapsto f(u, v_0)$ has the Fréchet derivative $h \mapsto A(h, 0)$ at
$u_0$. This is the partial derivative $f_u(u_0, v_0)$.

The map $h \mapsto A(h, 0)$ is `A.comp (ContinuousLinearMap.inl ℝ U V)`. -/
theorem proposition_5_3_15_fst {f : U × V → W} {A : U × V →L[ℝ] W} {p : U × V}
    (hf : HasFDerivAt f A p) :
    HasFDerivAt (fun u => f (u, p.2)) (A.comp (ContinuousLinearMap.inl ℝ U V)) p.1 :=
  hf.comp p.1 (hasFDerivAt_prodMk_left p.1 p.2)

/-- **Definition 5.3.14** and **Proposition 5.3.15** of [han2009theoretical], the partial derivative
in the second variable. Let $f : U \times V \to W$ have the Fréchet derivative $A$ at
$p = (u_0, v_0)$. Then $v \mapsto f(u_0, v)$ has the Fréchet derivative $k \mapsto A(0, k)$ at
$v_0$. This is the partial derivative $f_v(u_0, v_0)$.

The map $k \mapsto A(0, k)$ is `A.comp (ContinuousLinearMap.inr ℝ U V)`. -/
theorem proposition_5_3_15_snd {f : U × V → W} {A : U × V →L[ℝ] W} {p : U × V}
    (hf : HasFDerivAt f A p) :
    HasFDerivAt (fun v => f (p.1, v)) (A.comp (ContinuousLinearMap.inr ℝ U V)) p.2 :=
  hf.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)

/-- **Equation (5.3.8)** of [han2009theoretical]. The total derivative is the sum of the two partial
derivatives: for $A \in \mathcal{L}(U \times V, W)$, $h \in U$ and $k \in V$,
$$A(h, k) = A(h, 0) + A(0, k),$$
which for $A = f'(u_0, v_0)$ reads $f'(u_0, v_0)(h, k) = f_u(u_0, v_0) h + f_v(u_0, v_0) k$. -/
theorem equation_5_3_8 (A : U × V →L[ℝ] W) (h : U) (k : V) :
    A (h, k) = A.comp (ContinuousLinearMap.inl ℝ U V) h
      + A.comp (ContinuousLinearMap.inr ℝ U V) k := by
  have hsum : ((h, k) : U × V) = (h, 0) + (0, k) := by simp
  rw [hsum, map_add]
  rfl

/-- **Proposition 5.3.15** of [han2009theoretical], the converse. Let $f : U \times V \to W$ and
$p \in U \times V$. Assume that for all $q$ in a neighbourhood of $p$ the partial derivatives
$f_u(q)$ and $f_v(q)$ exist, and that $f_u$ and $f_v$ are continuous at $p$. Then $f$ has a
Fréchet derivative at $p$, given by $(h, k) \mapsto f_u(p) h + f_v(p) k$.

The function $f$ is curried, `f : U → V → W`, and `↿f` is the function on $U \times V$. The
derivative is `ContinuousLinearMap.coprod` of the partial derivatives. The proof is Mathlib's
`hasStrictFDerivAt_uncurry_coprod`. -/
theorem proposition_5_3_15_of_partial {f : U → V → W} {f₁ : U → V → U →L[ℝ] W}
    {f₂ : U → V → V →L[ℝ] W}
    {p : U × V} (df₁ : ∀ᶠ q in 𝓝 p, HasFDerivAt (f · q.2) (↿f₁ q) q.1)
    (df₂ : ∀ᶠ q in 𝓝 p, HasFDerivAt (f q.1 ·) (↿f₂ q) q.2) (cf₁ : ContinuousAt (↿f₁) p)
    (cf₂ : ContinuousAt (↿f₂) p) : HasFDerivAt (↿f) ((↿f₁ p).coprod (↿f₂ p)) p :=
  (hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂).hasFDerivAt

/-- Composition on the right with a fixed $L \in \mathcal{L}(X, Y)$ is a continuous map from
$\mathcal{L}(Y, Z)$ to $\mathcal{L}(X, Z)$. -/
private theorem continuous_comp_right {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : X →L[ℝ] Y) : Continuous fun B : Y →L[ℝ] Z => B.comp L :=
  ((ContinuousLinearMap.compL ℝ X Y Z).flip L).continuous

/-- **Corollary 5.3.16** of [han2009theoretical]. Let $f : U \times V \to W$ and $p \in U \times V$.
Then $f$ is continuously Fréchet differentiable in a neighbourhood of $p$ if and only if there
is a neighbourhood $s$ of $p$ such that the partial derivatives $f_u(q)$ and $f_v(q)$ exist for
all $q \in s$ and are continuous on $s$.

The left-hand side is `ContDiffAt ℝ 1 (↿f) p`: in Mathlib, as in the book, $C^1$ at a point
means differentiable in a neighbourhood with a derivative that is continuous there. The forward
direction applies `AtkinsonHan.Chapter05.proposition_5_3_15_fst` and
`AtkinsonHan.Chapter05.proposition_5_3_15_snd` at each point of the neighbourhood. The backward
direction applies `AtkinsonHan.Chapter05.proposition_5_3_15_of_partial` at each point of the
neighbourhood. -/
theorem corollary_5_3_16 {f : U → V → W} {p : U × V} :
    ContDiffAt ℝ 1 (↿f) p ↔
      ∃ (f₁ : U → V → U →L[ℝ] W) (f₂ : U → V → V →L[ℝ] W) (s : Set (U × V)), s ∈ 𝓝 p ∧
        (∀ q ∈ s, HasFDerivAt (f · q.2) (↿f₁ q) q.1) ∧
        (∀ q ∈ s, HasFDerivAt (f q.1 ·) (↿f₂ q) q.2) ∧
        ContinuousOn (↿f₁) s ∧ ContinuousOn (↿f₂) s := by
  constructor
  · intro hf
    obtain ⟨F, s, hs, hFc, hFd⟩ := contDiffAt_one_iff.1 hf
    refine ⟨fun a b => (F (a, b)).comp (ContinuousLinearMap.inl ℝ U V),
      fun a b => (F (a, b)).comp (ContinuousLinearMap.inr ℝ U V), s, hs,
      fun q hq => proposition_5_3_15_fst (hFd q hq),
      fun q hq => proposition_5_3_15_snd (hFd q hq), ?_, ?_⟩
    · exact (continuous_comp_right (ContinuousLinearMap.inl ℝ U V)).comp_continuousOn hFc
    · exact (continuous_comp_right (ContinuousLinearMap.inr ℝ U V)).comp_continuousOn hFc
  · rintro ⟨f₁, f₂, s, hs, hd₁, hd₂, hc₁, hc₂⟩
    obtain ⟨t, hts, hto, hpt⟩ := mem_nhds_iff.1 hs
    have hcop : Continuous fun z : (U →L[ℝ] W) × (V →L[ℝ] W) => z.1.coprod z.2 := by
      simp only [← ContinuousLinearMap.comp_fst_add_comp_snd]
      exact ((continuous_comp_right (ContinuousLinearMap.fst ℝ U V)).comp continuous_fst).add
        ((continuous_comp_right (ContinuousLinearMap.snd ℝ U V)).comp continuous_snd)
    refine contDiffAt_one_iff.2
      ⟨fun q => (↿f₁ q).coprod (↿f₂ q), t, hto.mem_nhds hpt, ?_, fun q hq => ?_⟩
    · exact hcop.comp_continuousOn (((hc₁.mono hts).prodMk (hc₂.mono hts)))
    · have hq' : t ∈ 𝓝 q := hto.mem_nhds hq
      refine proposition_5_3_15_of_partial ?_ ?_ ?_ ?_
      · filter_upwards [hq'] with r hr using hd₁ r (hts hr)
      · filter_upwards [hq'] with r hr using hd₂ r (hts hr)
      · exact (hc₁.mono hts).continuousAt hq'
      · exact (hc₂.mono hts).continuousAt hq'

end Partial

section Convexity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {K : Set V} {f : V → ℝ} {f' : V → V →L[ℝ] ℝ}

/-- **Theorem 5.3.17** of [han2009theoretical]. Let $K \subseteq V$ be convex, and let
$f : V \to \mathbb{R}$ have a Gâteaux derivative $f'(u)$ at every $u \in K$. Then the following
are equivalent: (a) $f$ is convex on $K$; (b) $f(u) + \langle f'(u), v - u \rangle \le f(v)$ for
all $u, v \in K$; (c) $\langle f'(v) - f'(u), v - u \rangle \ge 0$ for all $u, v \in K$.

The statement is the conjunction of (a) $\iff$ (b) and (a) $\iff$ (c). These are
`convexOn_iff_forall_add_lineDeriv_le` and `convexOn_iff_monotone_lineDeriv`, whose hypothesis
`∀ h, HasLineDerivAt ℝ f (f' u h) u h` is `AtkinsonHan.Chapter05.HasGateauxDerivAt f (f' u) u`
by definition. -/
theorem theorem_5_3_17 (hK : Convex ℝ K) (hG : ∀ u ∈ K, HasGateauxDerivAt f (f' u) u) :
    (ConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, f u + f' u (v - u) ≤ f v) ∧
      (ConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, 0 ≤ (f' v - f' u) (v - u)) :=
  ⟨convexOn_iff_forall_add_lineDeriv_le hK hG, convexOn_iff_monotone_lineDeriv hK hG⟩

/-- **Theorem 5.3.18** of [han2009theoretical]. Let $K \subseteq V$ be convex, and let
$f : V \to \mathbb{R}$ have a Gâteaux derivative $f'(u)$ at every $u \in K$. Then $f$ is
strictly convex on $K$ if and only if $f(u) + \langle f'(u), v - u \rangle < f(v)$ for all
$u, v \in K$ with $u \neq v$, and if and only if $\langle f'(v) - f'(u), v - u \rangle > 0$ for
all $u, v \in K$ with $u \neq v$.

The proofs are `strictConvexOn_iff_forall_add_lineDeriv_lt` and
`strictConvexOn_iff_forall_lineDeriv_sub_pos`. -/
theorem theorem_5_3_18 (hK : Convex ℝ K) (hG : ∀ u ∈ K, HasGateauxDerivAt f (f' u) u) :
    (StrictConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, u ≠ v → f u + f' u (v - u) < f v) ∧
      (StrictConvexOn ℝ K f ↔ ∀ u ∈ K, ∀ v ∈ K, u ≠ v → 0 < (f' v - f' u) (v - u)) :=
  ⟨strictConvexOn_iff_forall_add_lineDeriv_lt hK hG,
    strictConvexOn_iff_forall_lineDeriv_sub_pos hK hG⟩

/-- **Theorem 5.3.19** of [han2009theoretical]. Let $K \subseteq V$ be convex, and let
$f : V \to \mathbb{R}$ be convex on $K$ with a Gâteaux derivative $f'(u)$ at every $u \in K$.
Then $u \in K$ minimizes $f$ over $K$ if and only if $u$ solves the variational inequality
(5.3.10):
$$\langle f'(u), v - u \rangle \ge 0 \quad \text{for all } v \in K.$$

**Generalization.** The book states that the minimization problem and the variational inequality
are equivalent as problems. This statement gives the equivalence at each point $u \in K$, which
implies the book's form.

The convexity of $K$ is part of `ConvexOn ℝ K f`, so it is not a separate hypothesis. The proof
is `isMinOn_iff_forall_lineDeriv_nonneg`. -/
theorem theorem_5_3_19 (hG : ∀ u ∈ K, HasGateauxDerivAt f (f' u) u) (hcvx : ConvexOn ℝ K f)
    {u : V} (hu : u ∈ K) : IsMinOn f K u ↔ ∀ v ∈ K, 0 ≤ f' u (v - u) :=
  isMinOn_iff_forall_lineDeriv_nonneg hcvx hG hu

/-- **Theorem 5.3.19** of [han2009theoretical], formula (5.3.11). Let $K$ be a subspace of $V$, and
let $f : V \to \mathbb{R}$ be convex on $K$ with a Gâteaux derivative $f'(u)$ at every
$u \in K$. Then $u \in K$ minimizes $f$ over $K$ if and only if $u$ solves the variational
equation
$$\langle f'(u), v \rangle = 0 \quad \text{for all } v \in K.$$

The proof is `isMinOn_iff_forall_lineDeriv_eq_zero`. -/
theorem theorem_5_3_19_submodule (K : Submodule ℝ V)
    (hG : ∀ u ∈ (K : Set V), HasGateauxDerivAt f (f' u) u) (hcvx : ConvexOn ℝ (K : Set V) f)
    {u : V} (hu : u ∈ K) : IsMinOn f (K : Set V) u ↔ ∀ v ∈ K, f' u v = 0 :=
  isMinOn_iff_forall_lineDeriv_eq_zero hcvx hG hu

end Convexity

end AtkinsonHan.Chapter05
