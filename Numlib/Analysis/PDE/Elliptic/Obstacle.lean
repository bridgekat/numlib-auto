/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Dual
import Numlib.Analysis.PDE.DirichletLaplacian

/-!
# The obstacle problem: the Lewy–Stampacchia inequality and $H^2$ regularity

Let $\Omega \subseteq \mathbb{R}^N$ be open, let $\psi \in H^1(\Omega)$ be an obstacle and let
$f \in L^2(\Omega)$ be a load. The obstacle problem for the Laplacian is the variational inequality
$$u \in \mathcal{K} := \{v \in H^1_0(\Omega) : v \ge \psi \text{ a.e.}\}, \qquad \int_\Omega \nabla
  u \cdot \nabla (v - u) \ge \int_\Omega f (v - u) \quad \text{for all } v \in \mathcal{K},$$
as in [han2009theoretical], Examples 11.1.1 and 11.3.10, and the Comments on Chapter 9 of
[brezis2011functional]. When the obstacle has $-\Delta \psi = q \in L^2(\Omega)$ in the weak sense,
the **Lewy–Stampacchia inequality** $f \le -\Delta u \le \max\{f, q\}$ holds, so
$-\Delta u \in L^2(\Omega)$. On a $C^2$ domain the linear regularity theory then gives
$u \in H^2(\Omega)$ with
$$\|u\|_{H^2(\Omega)} \le C \big(\|f\|_{L^2} + \|\max\{f, q\} - f\|_{L^2} + \|u\|_{L^2}\big).$$
This is the case $p = 2$ of Theorem 11.3.12 of [han2009theoretical], for the Laplacian. That source
attributes the theorem to Brezis and Stampacchia, and quotes it also from Gilbarg and Trudinger. The
argument is the classical one; see also Kinderlehrer and Stampacchia, *An Introduction to
Variational Inequalities and Their Applications*, Chapter IV, and Rodrigues, *Obstacle Problems in
Mathematical Physics*, §5:4.

## Main definitions

* `Elliptic.IsObstacleSolution`: $u$ solves the obstacle problem with obstacle $\psi$ and load $f$.

## Main results

* `Elliptic.IsObstacleSolution.load_le_dirichletForm`: the lower bound $f \le -\Delta u$, that is,
  $\int_\Omega f \Phi \le \int_\Omega \nabla u \cdot \nabla \Phi$ for $\Phi \in H^1_0(\Omega)$ with
  $\Phi \ge 0$.
* `Elliptic.IsObstacleSolution.dirichletForm_le_load_sup`: the upper bound
  $-\Delta u \le \max\{f, q\}$, that is, $\int_\Omega \nabla u \cdot \nabla \Phi \le \int_\Omega
  \max\{f, q\} \Phi$ for $\Phi \in H^1_0(\Omega)$ with $\Phi \ge 0$.
* `Elliptic.IsObstacleSolution.exists_dirichletForm_eq_load`: $-\Delta u = f + h$ for some
  $h \in L^2(\Omega)$ with $\|h\|_2 \le 2 \|\max\{f, q\} - f\|_2$.
* `Elliptic.regularity_obstacle`: on a $C^2$ domain with bounded boundary, $u \in H^2(\Omega)$ with
  an $H^2$ bound.
* `Elliptic.IsObstacleSolution.norm_le`: the a priori bound $\|u\|_{H^1} \le 2(1 +
  (2R)^2)(\|w\|_{H^1} + \|f\|_2)$ for $\Omega \subseteq B(0, R)$ and an admissible $w$.
* `Elliptic.regularity_obstacle_sobolev_two`: for an obstacle in $H^2(\Omega)$ with
  $\psi^+ \in H^1_0(\Omega)$, $\|u\|_{H^2} \le C (\|f\|_2 + \|\psi\|_{H^2})$.

## Proof outline

The lower bound is the variational inequality tested with $v = u + \Phi$, where
$\Phi \in H^1_0(\Omega)$ and $\Phi \ge 0$.

The upper bound is the classical truncation argument. Let $\Phi \in H^1_0(\Omega)$ with
$\Phi \ge 0$, let $\varepsilon > 0$, and let $z = u - \psi \ge 0$. The competitor $v = u -
\min\{\varepsilon \Phi, z\} = \max\{u - \varepsilon \Phi, \psi\}$ is admissible, and it gives
$$\int_\Omega \nabla z \cdot \nabla \min\{\varepsilon \Phi, z\} \le \int_\Omega (f - q)
  \min\{\varepsilon \Phi, z\} \le \varepsilon \int_\Omega (f - q)^+ \Phi.$$
The left side is $\varepsilon \int_{\{z \ge \varepsilon \Phi\}} \nabla z \cdot \nabla \Phi +
\int_{\{z < \varepsilon \Phi\}} |\nabla z|^2 \ge \varepsilon \int_{\{z \ge \varepsilon \Phi\}}
\nabla z \cdot \nabla \Phi$, because $\nabla \min\{a, b\} = 1_{\{a \le b\}} \nabla a + 1_{\{a > b\}}
\nabla b$, which follows from $\nabla w^+ = 1_{\{w > 0\}} \nabla w$. As $\varepsilon \downarrow 0$
the set $\{z \ge \varepsilon \Phi\}$ fills $\{z > 0\}$, and $\nabla z = 0$ almost everywhere on the
complement (Stampacchia). Hence $\int_\Omega \nabla z \cdot \nabla \Phi \le \int_\Omega (f - q)^+
\Phi$, which is $\int_\Omega \nabla u \cdot \nabla \Phi \le \int_\Omega \max\{f, q\} \Phi$.

The two bounds make the functional $\Phi \mapsto \int_\Omega \nabla u \cdot \nabla \Phi -
\int_\Omega f \Phi$ on $H^1_0(\Omega)$ nonnegative on nonnegative $\Phi$, and bounded there by
$\int_\Omega (\max\{f, q\} - f) \Phi$. With $\Phi = \Phi^+ - \Phi^-$ it is bounded by
$2 \|\max\{f, q\} - f\|_2 \|\Phi\|_2$ on all of $H^1_0(\Omega)$. The Hahn–Banach and Riesz theorems
represent it as $\Phi \mapsto \int_\Omega h \Phi$ with $h \in L^2(\Omega)$, which is
$-\Delta u = f + h$. The linear regularity theorem, Theorem 9.25 of [brezis2011functional], then
gives the $H^2$ bound.

## Implementation notes

* The upper bound and the regularity results are stated on $\mathbb{R}^{d+1}$, so $N \ge 1$. They
  need a domain of class $C^1$ (or $C^2$) by local charts with bounded boundary
  (`IsContDiffChartDomain`). The reason is the one delicate point of the argument,
  $\min\{\varepsilon \Phi, z\} \in H^1_0(\Omega)$. This function is
  $\varepsilon \Phi - (\varepsilon \Phi - z)^+$ with $0 \le (\varepsilon \Phi - z)^+ \le \varepsilon
  \Phi$, and a function squeezed between $0$ and an element of $H^1_0(\Omega)$ lies in
  $H^1_0(\Omega)$ (`SobolevEuclideanZero.mem_of_nonneg_of_le`, on such a domain). The extension by
  zero of that function is $\min\{\tilde v^+, \bar w\}$, with $\tilde v$ a Sobolev extension of the
  function and $\bar w$ the extension by zero of the majorant, so it lies in $H^1(\mathbb{R}^N)$,
  and Proposition 9.18 of [brezis2011functional] concludes.
* The hypothesis $-\Delta \psi = q$ is `Elliptic.IsWeakSolution (Elliptic.dirichletForm Ω)
  (SobolevEuclideanZero (d + 1) 1 2 Ω) ψ q`, that is, $\int_\Omega \nabla \psi \cdot \nabla \Phi =
  \int_\Omega q \Phi$ for all $\Phi \in H^1_0(\Omega)$. The function $\max\{f, q\}$ is the lattice
  supremum `f ⊔ q` in $L^2(\Omega)$.
* For $\Phi \in H^1(\Omega)$, the norm $\|\Phi\|_{L^2(\Omega)}$ is
  `‖SobolevMultiIndex.weakDeriv Φ 0‖`.
* The statement $u \in H^2(\Omega)$ is `MemSobolevMultiIndex` of order $2$ for the function of $u$.
* The $H^2$ bound holds for every element of `SobolevEuclidean (d + 1) 2 2 Ω` whose function is
  that of $u$.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

namespace Elliptic

/-! ### The obstacle problem and the lower bound $f \le -\Delta u$ -/

section Obstacle

variable {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N)))

open SobolevMultiIndex

/-- A **solution of the obstacle problem** with obstacle $\psi \in H^1(\Omega)$ and load
$f \in L^2(\Omega)$ is a $u \in H^1(\Omega)$ with $u \in H^1_0(\Omega)$, $u \ge \psi$ almost
everywhere on $\Omega$, and
$$\int_\Omega \nabla u \cdot \nabla (v - u) \ge \int_\Omega f (v - u)$$
for every $v \in H^1_0(\Omega)$ with $v \ge \psi$ almost everywhere on $\Omega$. This is
(11.1.7) of [han2009theoretical].

The open set $\Omega \subseteq \mathbb{R}^N$ is arbitrary. The left side of the inequality is
`Elliptic.dirichletForm Ω u (v - u)`, and the right side is `Elliptic.load Ω f (v - u)`. -/
structure IsObstacleSolution (ψ : SobolevEuclidean N 1 2 Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))))
    (u : SobolevEuclidean N 1 2 Ω) : Prop where
  /-- The solution lies in $H^1_0(\Omega)$. -/
  mem_zero : u ∈ SobolevEuclideanZero N 1 2 Ω
  /-- The solution satisfies $u \ge \psi$ almost everywhere on $\Omega$. -/
  ae_le : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn ψ x ≤ fn u x
  /-- The variational inequality: $\int_\Omega \nabla u \cdot \nabla (v - u) \ge \int_\Omega f (v -
  u)$ for every $v \in H^1_0(\Omega)$ with $v \ge \psi$ almost everywhere on $\Omega$. -/
  ineq : ∀ v ∈ SobolevEuclideanZero N 1 2 Ω,
    (∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), fn ψ x ≤ fn v x) →
      load Ω f (v - u) ≤ dirichletForm Ω u (v - u)

variable {Ω}

/-- The lower bound $f \le -\Delta u$ of the **Lewy–Stampacchia inequality**. Let $u$ solve the
obstacle problem with obstacle $\psi \in H^1(\Omega)$ and load $f \in L^2(\Omega)$. Then for
every $\Phi \in H^1_0(\Omega)$ with $\Phi \ge 0$ almost everywhere,
$$\int_\Omega f \Phi \le \int_\Omega \nabla u \cdot \nabla \Phi.$$

The proof tests the variational inequality with $v = u + \Phi$. -/
theorem IsObstacleSolution.load_le_dirichletForm {ψ : SobolevEuclidean N 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
    {u : SobolevEuclidean N 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {Φ : SobolevEuclidean N 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero N 1 2 Ω)
    (hΦ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), 0 ≤ fn Φ x) :
    load Ω f Φ ≤ dirichletForm Ω u Φ := by
  have h := hu.ineq (u + Φ) (add_mem hu.mem_zero hΦ) (by
    filter_upwards [hu.ae_le, hΦ0, Lp.coeFn_add (weakDeriv u 0) (weakDeriv Φ 0)] with x h1 h2 h3
    have e : fn (u + Φ) x = fn u x + fn Φ x := h3
    rw [e]
    linarith)
  rwa [add_sub_cancel_left] at h

end Obstacle

/-! ### The upper bound $-\Delta u \le \max\{f, -\Delta \psi\}$: the truncation step -/

section Upper

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- For $f \in L^2(\Omega)$ and $v \in H^1(\Omega)$, the product $f v$ is integrable on $\Omega$. -/
theorem integrable_mul_fn (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (v : SobolevEuclidean (d + 1) 1 2 Ω) :
    Integrable (fun x ↦ f x * fn v x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  (L2.integrable_inner (𝕜 := ℝ) f (weakDeriv v 0)).congr
    (Eventually.of_forall fun x ↦ by
      simp only [RCLike.inner_apply, conj_trivial]
      rw [mul_comm]
      rfl)

/-- For $v, w \in H^1(\Omega)$ and each $i$, the product $\partial_i v\, \partial_i w$ is integrable
on $\Omega$. -/
theorem integrable_weakDeriv_mul_weakDeriv (v w : SobolevEuclidean (d + 1) 1 2 Ω)
    (i : Fin (d + 1)) :
    Integrable (fun x ↦ weakDeriv v (MultiIndexLE.single i) x
      * weakDeriv w (MultiIndexLE.single i) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  (L2.integrable_inner (𝕜 := ℝ) (weakDeriv v (MultiIndexLE.single i))
    (weakDeriv w (MultiIndexLE.single i))).congr
    (Eventually.of_forall fun x ↦ by
      simp only [RCLike.inner_apply, conj_trivial]
      rw [mul_comm])

/-- For $\Phi, z \in H^1(\Omega)$ and $\varepsilon \in \mathbb{R}$, the partial derivatives of
$\varepsilon \Phi - z$ are $\varepsilon \partial_i \Phi - \partial_i z$ almost everywhere on
$\Omega$. -/
theorem weakDeriv_smul_sub_ae_eq (ε : ℝ) (Φ z : SobolevEuclidean (d + 1) 1 2 Ω)
    (i : Fin (d + 1)) :
    ⇑(weakDeriv (ε • Φ - z) (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ ε * weakDeriv Φ (MultiIndexLE.single i) x
        - weakDeriv z (MultiIndexLE.single i) x := by
  have h1 : weakDeriv (ε • Φ - z) (MultiIndexLE.single i)
      = ε • weakDeriv Φ (MultiIndexLE.single i) - weakDeriv z (MultiIndexLE.single i) := by
    rw [← weakDerivL_apply, map_sub, map_smul, weakDerivL_apply, weakDerivL_apply]
  rw [h1]
  filter_upwards [Lp.coeFn_sub (ε • weakDeriv Φ (MultiIndexLE.single i))
    (weakDeriv z (MultiIndexLE.single i)),
    Lp.coeFn_smul ε (weakDeriv Φ (MultiIndexLE.single i))] with x hx1 hx2
  rw [hx1, Pi.sub_apply, hx2, Pi.smul_apply, smul_eq_mul]

/-- For $\Phi, z \in H^1(\Omega)$ and $\varepsilon \in \mathbb{R}$, the function of
$\varepsilon \Phi - z$ is $\varepsilon \Phi - z$ almost everywhere on $\Omega$. -/
theorem fn_smul_sub_ae_eq (ε : ℝ) (Φ z : SobolevEuclidean (d + 1) 1 2 Ω) :
    fn (ε • Φ - z) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ ε * fn Φ x - fn z x := by
  filter_upwards [Lp.coeFn_sub (weakDeriv (ε • Φ) 0) (weakDeriv z 0),
    Lp.coeFn_smul ε (weakDeriv Φ 0)] with x h1 h2
  have e : fn (ε • Φ - z) x = fn (ε • Φ) x - fn z x := h1
  have e2 : fn (ε • Φ) x = ε * fn Φ x := by
    rw [show fn (ε • Φ) x = (ε • fn Φ) x from h2, Pi.smul_apply, smul_eq_mul]
  rw [e, e2]

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a domain of class $C^1$ by local charts with bounded
boundary. Let $\Phi \in H^1_0(\Omega)$ with $\Phi \ge 0$, let $z \in H^1(\Omega)$ with $z \ge 0$
almost everywhere, and let $\varepsilon > 0$. Then there is $\theta \in H^1_0(\Omega)$ whose
function is $\min\{\varepsilon \Phi, z\} = \varepsilon \Phi - (\varepsilon \Phi - z)^+$ almost
everywhere, with
$$\partial_i \theta = \varepsilon \partial_i \Phi - 1_{\{\varepsilon \Phi - z > 0\}}\,
  \partial_i(\varepsilon \Phi - z)$$
almost everywhere on $\Omega$, for each $i$.

The positive part $P = (\varepsilon \Phi - z)^+$ lies in $H^1_0(\Omega)$ because
$0 \le P \le \varepsilon \Phi$ (`SobolevEuclideanZero.mem_of_nonneg_of_le`). The formula for the
partial derivatives is `SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_posPart`. In the
indicator, $\varepsilon \Phi - z$ is the function of the element `ε • Φ - z` of $H^1(\Omega)$. -/
theorem exists_min_elem
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {Φ : SobolevEuclidean (d + 1) 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hΦ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn Φ x)
    {z : SobolevEuclidean (d + 1) 1 2 Ω}
    (hz0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn z x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ θ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
      (fn θ =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ ε * fn Φ x - max (ε * fn Φ x - fn z x) 0) ∧
      ∀ i, ⇑(weakDeriv θ (MultiIndexLE.single i))
        =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ ε * weakDeriv Φ (MultiIndexLE.single i) x
          - {x | 0 < fn (ε • Φ - z) x}.indicator
            (weakDeriv (ε • Φ - z) (MultiIndexLE.single i)) x := by
  have hyfn := fn_smul_sub_ae_eq ε Φ z
  obtain ⟨P, hP⟩ :=
    ((memSobolevMultiIndex (ε • Φ - z)).posPart one_le_two).exists_sobolevMultiIndex
  have hεΦ : fn (ε • Φ) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      ε • fn Φ := Lp.coeFn_smul ε (weakDeriv Φ 0)
  have hP0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn P x := by
    filter_upwards [hP] with x hx
    rw [hx]
    exact le_max_right _ _
  have hPle : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn P x ≤ fn (ε • Φ) x := by
    filter_upwards [hP, hyfn, hz0, hεΦ, hΦ0] with x h1 h2 h3 h4 h5
    rw [h1, h2, h4, Pi.smul_apply, smul_eq_mul]
    exact max_le (by linarith) (mul_nonneg hε.le h5)
  have hPmem : P ∈ SobolevEuclideanZero (d + 1) 1 2 Ω :=
    SobolevEuclideanZero.mem_of_nonneg_of_le hΩ hΓ
      ((SobolevEuclideanZero (d + 1) 1 2 Ω).smul_mem ε hΦ) hP0 hPle
  refine ⟨ε • Φ - P, sub_mem ((SobolevEuclideanZero (d + 1) 1 2 Ω).smul_mem ε hΦ) hPmem,
    ?_, fun i ↦ ?_⟩
  · filter_upwards [Lp.coeFn_sub (weakDeriv (ε • Φ) 0) (weakDeriv P 0), hεΦ, hP, hyfn]
      with x h1 h2 h3 h4
    have e : fn (ε • Φ - P) x = fn (ε • Φ) x - fn P x := h1
    rw [e, h2, h3, h4, Pi.smul_apply, smul_eq_mul]
  · have h1 : weakDeriv (ε • Φ - P) (MultiIndexLE.single i)
        = ε • weakDeriv Φ (MultiIndexLE.single i) - weakDeriv P (MultiIndexLE.single i) := by
      rw [← weakDerivL_apply, map_sub, map_smul, weakDerivL_apply, weakDerivL_apply]
    have h2 := weakDeriv_single_ae_eq_of_fn_ae_eq_posPart hP i
    rw [h1]
    filter_upwards [Lp.coeFn_sub (ε • weakDeriv Φ (MultiIndexLE.single i))
      (weakDeriv P (MultiIndexLE.single i)), Lp.coeFn_smul ε (weakDeriv Φ (MultiIndexLE.single i)),
      h2] with x hx1 hx2 hx3
    rw [hx1, Pi.sub_apply, hx2, Pi.smul_apply, smul_eq_mul, hx3]

/-- Let $u$ solve the obstacle problem with obstacle $\psi$ and load $f$. If
$\theta \in H^1_0(\Omega)$ and $\theta \le u - \psi$ almost everywhere on $\Omega$, then
$$\int_\Omega \nabla u \cdot \nabla \theta \le \int_\Omega f \theta.$$

The proof tests the variational inequality with $v = u - \theta$. -/
theorem IsObstacleSolution.dirichletForm_le_load_of_le {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {θ : SobolevEuclidean (d + 1) 1 2 Ω} (hθ : θ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hθz : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn θ x ≤ fn u x - fn ψ x) :
    dirichletForm Ω u θ ≤ load Ω f θ := by
  have hvψ : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn ψ x ≤ fn (u - θ) x := by
    filter_upwards [Lp.coeFn_sub (weakDeriv u 0) (weakDeriv θ 0), hθz] with x h1 h2
    have e : fn (u - θ) x = fn u x - fn θ x := h1
    rw [e]
    linarith
  have hVI := hu.ineq (u - θ) (sub_mem hu.mem_zero hθ) hvψ
  rw [sub_sub_cancel_left, (load Ω f).map_neg, (dirichletForm Ω u).map_neg,
    neg_le_neg_iff] at hVI
  exact hVI

/-- Let $u$ solve the obstacle problem with obstacle $\psi$ and load $f$, and let
$-\Delta \psi = q \in L^2(\Omega)$ in the weak sense on $H^1_0(\Omega)$. Let $z = u - \psi$, and
let $\theta \in H^1_0(\Omega)$ with $\theta \le z$ almost everywhere on $\Omega$. Then
$$\int_\Omega \nabla z \cdot \nabla \theta \le \int_\Omega (f - q) \theta.$$
-/
theorem IsObstacleSolution.dirichletForm_sub_le {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : IsWeakSolution (dirichletForm Ω) (SobolevEuclideanZero (d + 1) 1 2 Ω) ψ q)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {θ : SobolevEuclidean (d + 1) 1 2 Ω} (hθ : θ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hθz : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn θ x ≤ fn u x - fn ψ x) {z : SobolevEuclidean (d + 1) 1 2 Ω} (hz : z = u - ψ) :
    dirichletForm Ω z θ ≤ load Ω (f - q) θ := by
  have hVI := hu.dirichletForm_le_load_of_le hθ hθz
  have huzψ : u = z + ψ := by
    rw [hz, sub_add_cancel]
  have hsplit : dirichletForm Ω u θ = dirichletForm Ω z θ + load Ω q θ := by
    rw [huzψ, dirichletForm_add_left, hψ θ hθ]
  have e : load Ω (f - q) θ = load Ω f θ - load Ω q θ := by
    simp only [load_apply_inner, inner_sub_left]
  refine le_of_le_of_eq ?_ e.symm
  calc dirichletForm Ω z θ = dirichletForm Ω u θ - load Ω q θ := eq_sub_of_add_eq hsplit.symm
    _ ≤ load Ω f θ - load Ω q θ := sub_le_sub_right hVI _

/-- Let $g \in L^2(\Omega)$, $\theta, \Phi \in H^1(\Omega)$ and $\varepsilon \in \mathbb{R}$, with
$0 \le \theta \le \varepsilon \Phi$ almost everywhere on $\Omega$. Then
$$\int_\Omega g \theta \le \varepsilon \int_\Omega g^+ \Phi.$$
-/
theorem load_le_smul_load_sup_zero
    (g : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {θ Φ : SobolevEuclidean (d + 1) 1 2 Ω} {ε : ℝ}
    (hθ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn θ x)
    (hθle : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn θ x ≤ ε * fn Φ x) :
    load Ω g θ ≤ ε * load Ω (g ⊔ 0) Φ := by
  rw [load_apply, load_apply, ← integral_const_mul]
  refine integral_mono_ae (integrable_mul_fn _ _) ((integrable_mul_fn _ _).const_mul ε) ?_
  filter_upwards [hθ0, hθle, Lp.coeFn_sup g 0, Lp.coeFn_zero ℝ 2
    (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))] with x h1 h2 h3 h4
  simp only [h3, h4, Pi.sup_apply, Pi.zero_apply]
  calc g x * fn θ x ≤ max (g x) 0 * fn θ x :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) h1
    _ ≤ max (g x) 0 * (ε * fn Φ x) :=
        mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = ε * (max (g x) 0 * fn Φ x) := by ring

/-- Let $\theta, z, \Phi, y \in H^1(\Omega)$, $\varepsilon \in \mathbb{R}$ and an index $i$ be such
that, almost everywhere on $\Omega$, $\partial_i \theta = \varepsilon \partial_i \Phi - 1_{\{y >
0\}} \partial_i y$ and $\partial_i y = \varepsilon \partial_i \Phi - \partial_i z$. Then
$$\int_\Omega \varepsilon\, 1_{\{y \le 0\}}\, \partial_i z\, \partial_i \Phi \le \int_\Omega
  \partial_i z\, \partial_i \theta.$$
This is one component of the lower bound for $\int_\Omega \nabla z \cdot \nabla
\min\{\varepsilon \Phi, z\}$.

Pointwise, $\partial_i z\, \partial_i \theta = 1_{\{y \le 0\}} \varepsilon\, \partial_i z\,
\partial_i \Phi + 1_{\{y > 0\}} (\partial_i z)^2$. -/
theorem integral_indicator_le_integral_weakDeriv_mul {θ z Φ y : SobolevEuclidean (d + 1) 1 2 Ω}
    {ε : ℝ} (i : Fin (d + 1))
    (hDθ : ⇑(weakDeriv θ (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ ε * weakDeriv Φ (MultiIndexLE.single i) x
        - {x | 0 < fn y x}.indicator (weakDeriv y (MultiIndexLE.single i)) x)
    (hDy : ⇑(weakDeriv y (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ ε * weakDeriv Φ (MultiIndexLE.single i) x - weakDeriv z (MultiIndexLE.single i) x) :
    ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      ε * {x | fn y x ≤ 0}.indicator
        (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x
      ≤ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        weakDeriv z (MultiIndexLE.single i) x * weakDeriv θ (MultiIndexLE.single i) x := by
  have hint : Integrable (fun x ↦ ε * {x | fn y x ≤ 0}.indicator
      (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := by
    refine ((integrable_weakDeriv_mul_weakDeriv z Φ i).indicator₀ ?_).const_mul ε
    exact nullMeasurableSet_le (Lp.aestronglyMeasurable (weakDeriv y 0)).aemeasurable
      aemeasurable_const
  refine integral_mono_ae hint (integrable_weakDeriv_mul_weakDeriv z θ i) ?_
  filter_upwards [hDθ, hDy] with x hx1 hx2
  rw [hx1]
  by_cases hyx : 0 < fn y x
  · rw [indicator_of_mem (show x ∈ {x | 0 < fn y x} from hyx), hx2,
      indicator_of_notMem (show x ∉ {x | fn y x ≤ 0} from not_le.2 hyx)]
    nlinarith [sq_nonneg (weakDeriv z (MultiIndexLE.single i) x)]
  · rw [indicator_of_notMem (show x ∉ {x | 0 < fn y x} from hyx),
      indicator_of_mem (show x ∈ {x | fn y x ≤ 0} from not_lt.1 hyx)]
    ring_nf
    exact le_refl _

/-- The truncation step of the proof of the Lewy–Stampacchia inequality. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a domain of class $C^1$ by local charts with bounded
boundary. Let $u$ solve the obstacle problem with obstacle $\psi$ and load $f$, and let
$-\Delta \psi = q \in L^2(\Omega)$ in the weak sense on $H^1_0(\Omega)$. Let $z = u - \psi$, let
$\Phi \in H^1_0(\Omega)$ with $\Phi \ge 0$ almost everywhere, and let $\varepsilon > 0$. Then
$$\sum_i \int_{\{\varepsilon \Phi \le z\}} \partial_i z\, \partial_i \Phi \le \int_\Omega (f -
  q)^+ \Phi.$$

The competitor $v = u - \min\{\varepsilon \Phi, z\} = \max\{u - \varepsilon \Phi, \psi\}$ is
admissible, and
$$\varepsilon \sum_i \int_{\{\varepsilon \Phi \le z\}} \partial_i z\, \partial_i \Phi \le
  \int_\Omega \nabla z \cdot \nabla \min\{\varepsilon \Phi, z\} \le \int_\Omega (f - q)
  \min\{\varepsilon \Phi, z\} \le \varepsilon \int_\Omega (f - q)^+ \Phi.$$
The first inequality is `Elliptic.integral_indicator_le_integral_weakDeriv_mul`, the second is
`Elliptic.IsObstacleSolution.dirichletForm_sub_le`, and the third is
`Elliptic.load_le_smul_load_sup_zero`. The membership
$\min\{\varepsilon \Phi, z\} \in H^1_0(\Omega)$ is `Elliptic.exists_min_elem`. The set
$\{\varepsilon \Phi \le z\}$ is the set where the function of `ε • Φ - z` is at most $0$. -/
theorem IsObstacleSolution.truncation_step
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : IsWeakSolution (dirichletForm Ω) (SobolevEuclideanZero (d + 1) 1 2 Ω) ψ q)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {Φ : SobolevEuclidean (d + 1) 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hΦ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn Φ x)
    {ε : ℝ} (hε : 0 < ε) {z : SobolevEuclidean (d + 1) 1 2 Ω} (hz : z = u - ψ) :
    ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        {x | fn (ε • Φ - z) x ≤ 0}.indicator
          (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x
      ≤ load Ω ((f - q) ⊔ 0) Φ := by
  have hzfn : fn z =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fn u - fn ψ := by
    rw [hz]
    exact Lp.coeFn_sub (weakDeriv u 0) (weakDeriv ψ 0)
  have hz0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn z x := by
    filter_upwards [hzfn, hu.ae_le] with x h1 h2
    rw [h1, Pi.sub_apply]
    linarith
  obtain ⟨θ, hθmem, hθfn, hDθ⟩ := exists_min_elem hΩ hΓ hΦ hΦ0 hz0 hε
  have hθ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn θ x := by
    filter_upwards [hθfn, hz0, hΦ0] with x h1 h2 h3
    rw [h1]
    rcases le_total (ε * fn Φ x - fn z x) 0 with h | h
    · rw [max_eq_right h, sub_zero]
      exact mul_nonneg hε.le h3
    · rw [max_eq_left h]
      linarith
  have hθle : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn θ x ≤ ε * fn Φ x := by
    filter_upwards [hθfn] with x h1
    rw [h1]
    linarith [le_max_right (ε * fn Φ x - fn z x) 0]
  have hθz : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn θ x ≤ fn u x - fn ψ x := by
    filter_upwards [hθfn, hzfn] with x h1 h2
    rw [h1]
    rw [Pi.sub_apply] at h2
    linarith [le_max_left (ε * fn Φ x - fn z x) 0]
  have hmid := hu.dirichletForm_sub_le hψ hθmem hθz hz
  have hright := load_le_smul_load_sup_zero (f - q) hθ0 hθle
  have hleft : ε * ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      {x | fn (ε • Φ - z) x ≤ 0}.indicator
        (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x
      ≤ dirichletForm Ω z θ := by
    have hi : ∀ i, ε * ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        {x | fn (ε • Φ - z) x ≤ 0}.indicator
          (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x
        ≤ ⟪weakDeriv z (MultiIndexLE.single i), weakDeriv θ (MultiIndexLE.single i)⟫_ℝ := by
      intro i
      rw [L2.inner_eq_integral_mul, ← integral_const_mul]
      exact integral_indicator_le_integral_weakDeriv_mul i (hDθ i)
        (weakDeriv_smul_sub_ae_eq ε Φ z i)
    rw [dirichletForm_apply_inner, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ hi i
  exact le_of_mul_le_mul_left (hleft.trans (hmid.trans hright)) hε

end Upper

/-! ### The upper bound: the limit $\varepsilon \downarrow 0$ -/

section UpperLimit

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- Let $-\Delta \psi = q \in L^2(\Omega)$ in the weak sense on $H^1_0(\Omega)$, let
$u \in H^1(\Omega)$, and let $z = u - \psi$. Then for every $\Phi \in H^1_0(\Omega)$,
$$\int_\Omega \nabla u \cdot \nabla \Phi = \int_\Omega \nabla z \cdot \nabla \Phi + \int_\Omega
  q \Phi.$$
-/
theorem dirichletForm_eq_dirichletForm_sub_add_load {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : IsWeakSolution (dirichletForm Ω) (SobolevEuclideanZero (d + 1) 1 2 Ω) ψ q)
    {u z : SobolevEuclidean (d + 1) 1 2 Ω} (hz : z = u - ψ)
    {Φ : SobolevEuclidean (d + 1) 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω) :
    dirichletForm Ω u Φ = dirichletForm Ω z Φ + load Ω q Φ := by
  have huzψ : u = z + ψ := by
    rw [hz, sub_add_cancel]
  rw [huzψ, dirichletForm_add_left, hψ Φ hΦ]

/-- For real numbers $a$ and $b$, $\max\{a - b, 0\} + b = \max\{a, b\}$. -/
theorem max_sub_zero_add (a b : ℝ) : max (a - b) 0 + b = max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right (sub_nonpos.2 h), max_eq_right h, zero_add]
  · rw [max_eq_left (sub_nonneg.2 h), max_eq_left h, sub_add_cancel]

/-- For $f, q \in L^2(\Omega)$, $(f - q)^+ + q = \max\{f, q\}$ in $L^2(\Omega)$. -/
theorem sub_sup_zero_add_eq_sup
    (f q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    (f - q) ⊔ 0 + q = f ⊔ q := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add ((f - q) ⊔ 0) q, Lp.coeFn_sup (f - q) 0, Lp.coeFn_sub f q,
    Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
    Lp.coeFn_sup f q] with x h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, Pi.sup_apply, h3, Pi.sub_apply, h4, Pi.zero_apply, h5, Pi.sup_apply]
  exact max_sub_zero_add _ _

/-- For $f, q \in L^2(\Omega)$ and $\Phi \in H^1(\Omega)$, $\int_\Omega (f - q)^+ \Phi + \int_\Omega
q \Phi = \int_\Omega \max\{f, q\} \Phi$. -/
theorem load_sub_sup_zero_add_load
    (f q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    (Φ : SobolevEuclidean (d + 1) 1 2 Ω) :
    load Ω ((f - q) ⊔ 0) Φ + load Ω q Φ = load Ω (f ⊔ q) Φ := by
  exact (load_add (Ω := Ω) ((f - q) ⊔ 0) q Φ).symm.trans
    (congrArg (fun g ↦ load Ω g Φ) (sub_sup_zero_add_eq_sup f q))

/-- The Lewy–Stampacchia upper bound for $z = u - \psi$. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be
a domain of class $C^1$ by local charts with bounded boundary. Let $u$ solve the obstacle
problem with obstacle $\psi$ and load $f$, and let $-\Delta \psi = q \in L^2(\Omega)$ in the
weak sense on $H^1_0(\Omega)$. Let $z = u - \psi$. Then for every $\Phi \in H^1_0(\Omega)$ with
$\Phi \ge 0$ almost everywhere,
$$\int_\Omega \nabla z \cdot \nabla \Phi \le \int_\Omega (f - q)^+ \Phi.$$

The proof applies `Elliptic.IsObstacleSolution.truncation_step` with $\varepsilon_n = 1/(n+1)$
and uses dominated convergence. As $n \to \infty$, $1_{\{\varepsilon_n \Phi \le z\}} \to 1$
where $z > 0$, and $\partial_i z = 0$ almost everywhere on $\{z = 0\}$
(`SobolevMultiIndex.weakDeriv_single_ae_eq_of_fn_ae_eq_posPart`, since $z = z^+$). So $\sum_i
\int_{\{\varepsilon_n \Phi \le z\}} \partial_i z\, \partial_i \Phi \to \sum_i \int_\Omega
\partial_i z\, \partial_i \Phi$. -/
theorem IsObstacleSolution.dirichletForm_sub_le_load_sup_zero
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : IsWeakSolution (dirichletForm Ω) (SobolevEuclideanZero (d + 1) 1 2 Ω) ψ q)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {Φ : SobolevEuclidean (d + 1) 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hΦ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn Φ x)
    {z : SobolevEuclidean (d + 1) 1 2 Ω} (hz : z = u - ψ) :
    dirichletForm Ω z Φ ≤ load Ω ((f - q) ⊔ 0) Φ := by
  have hzfn : fn z =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fn u - fn ψ := by
    rw [hz]
    exact Lp.coeFn_sub (weakDeriv u 0) (weakDeriv ψ 0)
  have hz0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn z x := by
    filter_upwards [hzfn, hu.ae_le] with x h1 h2
    rw [h1, Pi.sub_apply]
    linarith
  -- `∂ᵢz = 0` where `z = 0`
  have hDz : ∀ i, ⇑(weakDeriv z (MultiIndexLE.single i))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      {x | 0 < fn z x}.indicator (weakDeriv z (MultiIndexLE.single i)) := fun i ↦
    weakDeriv_single_ae_eq_of_fn_ae_eq_posPart (u := z) (v := z)
      (by filter_upwards [hz0] with x hx; rw [max_eq_left hx]) i
  -- the sequence `ε n = 1/(n+1)`
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ, ε = fun n : ℕ ↦ 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hεpos : ∀ n, 0 < ε n := fun n ↦ by rw [hεdef]; positivity
  have hεt : Tendsto ε atTop (𝓝 0) := hεdef ▸ tendsto_one_div_add_atTop_nhds_zero_nat
  have hstep : ∀ n, ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      {x | fn (ε n • Φ - z) x ≤ 0}.indicator
        (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x
      ≤ load Ω ((f - q) ⊔ 0) Φ := fun n ↦
    hu.truncation_step hΩ hΓ hψ hΦ hΦ0 (hεpos n) hz
  have hyfn : ∀ n, fn (ε n • Φ - z) =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
      fun x ↦ ε n * fn Φ x - fn z x := fun n ↦ fn_smul_sub_ae_eq (ε n) Φ z
  -- the limit of each component
  have hlim : ∀ i, Tendsto (fun n ↦ ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      {x | fn (ε n • Φ - z) x ≤ 0}.indicator
        (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x)
      atTop (𝓝 (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x)) := by
    intro i
    refine tendsto_integral_of_dominated_convergence
      (fun x ↦ ‖weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x‖)
      (fun n ↦ ?_) (integrable_weakDeriv_mul_weakDeriv z Φ i).norm
      (fun n ↦ Eventually.of_forall fun x ↦ norm_indicator_le_norm_self _ _) ?_
    · exact (aestronglyMeasurable_indicator_iff₀ (nullMeasurableSet_le
        (Lp.aestronglyMeasurable (weakDeriv (ε n • Φ - z) 0)).aemeasurable aemeasurable_const)).2
        (integrable_weakDeriv_mul_weakDeriv z Φ i).aestronglyMeasurable.restrict
    · filter_upwards [ae_all_iff.2 hyfn, hDz i] with x hx hDx
      by_cases hzx : 0 < fn z x
      · have hev : ∀ᶠ n in atTop, fn (ε n • Φ - z) x ≤ 0 := by
          have h1 : Tendsto (fun n ↦ ε n * fn Φ x - fn z x) atTop
              (𝓝 (0 * fn Φ x - fn z x)) := (hεt.mul_const _).sub_const _
          rw [zero_mul, zero_sub] at h1
          filter_upwards [h1.eventually (gt_mem_nhds (neg_lt_zero.2 hzx))] with n hn
          rw [hx n]
          exact hn.le
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        rw [indicator_of_mem (show x ∈ {x | fn (ε n • Φ - z) x ≤ 0} from hn)]
      · have h0 : weakDeriv z (MultiIndexLE.single i) x = 0 := by
          rw [hDx, indicator_of_notMem (show x ∉ {x | 0 < fn z x} from hzx)]
        have hzero : ∀ n, {x | fn (ε n • Φ - z) x ≤ 0}.indicator
            (fun x ↦ weakDeriv z (MultiIndexLE.single i) x
              * weakDeriv Φ (MultiIndexLE.single i) x) x = 0 := fun n ↦ by
          rw [Set.indicator_apply]
          split_ifs
          · rw [h0, zero_mul]
          · rfl
        simp only [hzero, h0, zero_mul]
        exact tendsto_const_nhds
  have hsum : Tendsto (fun n ↦ ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      {x | fn (ε n • Φ - z) x ≤ 0}.indicator
        (fun x ↦ weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x) x)
      atTop (𝓝 (∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
        weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x)) :=
    tendsto_finsetSum _ fun i _ ↦ hlim i
  have hzΦ := le_of_tendsto' hsum hstep
  have e : dirichletForm Ω z Φ = ∑ i, ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      weakDeriv z (MultiIndexLE.single i) x * weakDeriv Φ (MultiIndexLE.single i) x := by
    rw [dirichletForm_apply_inner]
    simp only [L2.inner_eq_integral_mul]
  exact e.trans_le hzΦ

/-- The upper bound $-\Delta u \le \max\{f, -\Delta \psi\}$ of the **Lewy–Stampacchia inequality**.
Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a domain of class $C^1$ by local charts with bounded
boundary. Let $u$ solve the obstacle problem with obstacle $\psi$ and load $f$, and let
$-\Delta \psi = q \in L^2(\Omega)$ in the weak sense on $H^1_0(\Omega)$. Then for every
$\Phi \in H^1_0(\Omega)$ with $\Phi \ge 0$ almost everywhere,
$$\int_\Omega \nabla u \cdot \nabla \Phi \le \int_\Omega \max\{f, q\} \Phi.$$

The proof adds $\int_\Omega \nabla (u - \psi) \cdot \nabla \Phi \le \int_\Omega (f - q)^+ \Phi$
(`Elliptic.IsObstacleSolution.dirichletForm_sub_le_load_sup_zero`) and $\int_\Omega \nabla \psi
\cdot \nabla \Phi = \int_\Omega q \Phi$, and uses $(f - q)^+ + q = \max\{f, q\}$. -/
theorem IsObstacleSolution.dirichletForm_le_load_sup
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : IsWeakSolution (dirichletForm Ω) (SobolevEuclideanZero (d + 1) 1 2 Ω) ψ q)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {Φ : SobolevEuclidean (d + 1) 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hΦ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn Φ x) :
    dirichletForm Ω u Φ ≤ load Ω (f ⊔ q) Φ := by
  obtain ⟨z, hz⟩ : ∃ z : SobolevEuclidean (d + 1) 1 2 Ω, z = u - ψ := ⟨_, rfl⟩
  have h1 := hu.dirichletForm_sub_le_load_sup_zero hΩ hΓ hψ hΦ hΦ0 hz
  have h2 := dirichletForm_eq_dirichletForm_sub_add_load hψ hz hΦ
  have h3 := load_sub_sup_zero_add_load f q Φ
  linarith

end UpperLimit

/-! ### From the two-sided bound to $-\Delta u \in L^2(\Omega)$ -/

section Representation

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- Let $\Omega \subseteq \mathbb{R}^N$ be open, let $T$ be a continuous linear functional on
$H^1_0(\Omega)$, and let $C \ge 0$ with $|T \Phi| \le C \|\Phi\|_{L^2(\Omega)}$ for every
$\Phi \in H^1_0(\Omega)$. Then there is $h \in L^2(\Omega)$ with $\|h\|_{L^2(\Omega)} \le C$ and
$T \Phi = \int_\Omega h \Phi$ for every $\Phi \in H^1_0(\Omega)$.

The proof applies `exists_inner_of_forall_abs_le` to the injective inclusion of $H^1_0(\Omega)$
into $L^2(\Omega)$ (`SobolevMultiIndexZero.fnL`). -/
theorem exists_load_eq_of_forall_abs_le (T : SobolevEuclideanZero N 1 2 Ω →L[ℝ] ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hT : ∀ Φ : SobolevEuclideanZero N 1 2 Ω,
      |T Φ| ≤ C * ‖weakDeriv (Φ : SobolevEuclidean N 1 2 Ω) 0‖) :
    ∃ h : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))), ‖h‖ ≤ C ∧
      ∀ Φ : SobolevEuclideanZero N 1 2 Ω, T Φ = load Ω h Φ := by
  obtain ⟨h, hh, hT'⟩ := exists_inner_of_forall_abs_le
    (SobolevMultiIndexZero.fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 2 Ω volume)
    SobolevMultiIndexZero.fnL_injective T hC hT
  exact ⟨h, hh, fun Φ ↦ (hT' Φ).trans (load_apply_inner Ω h Φ).symm⟩

end Representation

section LpBound

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- The two-sided Lewy–Stampacchia bound on nonnegative test functions. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a domain of class $C^1$ by local charts with bounded
boundary. Let $u$ solve the obstacle problem with obstacle $\psi$ and load $f$, and let
$-\Delta \psi = q \in L^2(\Omega)$ in the weak sense on $H^1_0(\Omega)$. Then for every
$\Phi \in H^1_0(\Omega)$ with $\Phi \ge 0$ almost everywhere,
$$\Big|\int_\Omega \nabla u \cdot \nabla \Phi - \int_\Omega f \Phi\Big| \le \|\max\{f, q\} -
  f\|_{L^2(\Omega)} \|\Phi\|_{L^2(\Omega)}.$$

The proof combines `Elliptic.IsObstacleSolution.load_le_dirichletForm` and
`Elliptic.IsObstacleSolution.dirichletForm_le_load_sup`. -/
theorem IsObstacleSolution.abs_dirichletForm_sub_load_le_of_nonneg
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : IsWeakSolution (dirichletForm Ω) (SobolevEuclideanZero (d + 1) 1 2 Ω) ψ q)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {Φ : SobolevEuclidean (d + 1) 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hΦ0 : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))), 0 ≤ fn Φ x) :
    |dirichletForm Ω u Φ - load Ω f Φ| ≤ ‖f ⊔ q - f‖ * ‖weakDeriv Φ 0‖ := by
  have h1 := hu.load_le_dirichletForm hΦ hΦ0
  have h2 := hu.dirichletForm_le_load_sup hΩ hΓ hψ hΦ hΦ0
  have h3 : load Ω (f ⊔ q) Φ - load Ω f Φ = load Ω (f ⊔ q - f) Φ := by
    simp only [load_apply_inner, inner_sub_left]
  have h4 := abs_load_le Ω (f ⊔ q - f) Φ
  rw [abs_of_nonneg (by linarith)]
  linarith [le_abs_self (load Ω (f ⊔ q - f) Φ)]

/-- Under the hypotheses of `Elliptic.IsObstacleSolution.abs_dirichletForm_sub_load_le_of_nonneg` on
$\Omega$, $\psi$, $q$, $f$ and $u$: for every $\Phi \in H^1_0(\Omega)$,
$$\Big|\int_\Omega \nabla u \cdot \nabla \Phi - \int_\Omega f \Phi\Big| \le 2 \|\max\{f, q\} -
  f\|_{L^2(\Omega)} \|\Phi\|_{L^2(\Omega)}.$$

The proof splits $\Phi = \Phi^+ - \Phi^-$. -/
theorem IsObstacleSolution.abs_dirichletForm_sub_load_le
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : IsWeakSolution (dirichletForm Ω) (SobolevEuclideanZero (d + 1) 1 2 Ω) ψ q)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {Φ : SobolevEuclidean (d + 1) 1 2 Ω} (hΦ : Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω) :
    |dirichletForm Ω u Φ - load Ω f Φ| ≤ 2 * ‖f ⊔ q - f‖ * ‖weakDeriv Φ 0‖ := by
  obtain ⟨P, hPmem, Q, hQmem, hΦPQ, hP0, hQ0, hPn, hQn⟩ :=
    SobolevEuclideanZero.exists_eq_sub_of_nonneg hΦ
  have h1 := hu.abs_dirichletForm_sub_load_le_of_nonneg hΩ hΓ hψ hPmem hP0
  have h2 := hu.abs_dirichletForm_sub_load_le_of_nonneg hΩ hΓ hψ hQmem hQ0
  have e : dirichletForm Ω u Φ - load Ω f Φ
      = (dirichletForm Ω u P - load Ω f P) - (dirichletForm Ω u Q - load Ω f Q) := by
    rw [hΦPQ, (dirichletForm Ω u).map_sub, (load Ω f).map_sub]
    ring
  rw [e]
  have hg0 : 0 ≤ ‖f ⊔ q - f‖ := norm_nonneg _
  calc |(dirichletForm Ω u P - load Ω f P) - (dirichletForm Ω u Q - load Ω f Q)|
      ≤ |dirichletForm Ω u P - load Ω f P| + |dirichletForm Ω u Q - load Ω f Q| :=
        abs_sub _ _
    _ ≤ ‖f ⊔ q - f‖ * ‖weakDeriv Φ 0‖ + ‖f ⊔ q - f‖ * ‖weakDeriv Φ 0‖ :=
        add_le_add (h1.trans (mul_le_mul_of_nonneg_left hPn hg0))
          (h2.trans (mul_le_mul_of_nonneg_left hQn hg0))
    _ = 2 * ‖f ⊔ q - f‖ * ‖weakDeriv Φ 0‖ := by ring

/-- $-\Delta u \in L^2(\Omega)$ for the solution of the obstacle problem. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a domain of class $C^1$ by local charts with bounded
boundary. Let $u$ solve the obstacle problem with obstacle $\psi$ and load $f$, and let
$-\Delta \psi = q \in L^2(\Omega)$ in the weak sense on $H^1_0(\Omega)$. Then there is
$h \in L^2(\Omega)$ with $\|h\|_{L^2(\Omega)} \le 2 \|\max\{f, q\} - f\|_{L^2(\Omega)}$ and
$$\int_\Omega \nabla u \cdot \nabla \Phi = \int_\Omega (f + h) \Phi \qquad \text{for every }
  \Phi \in H^1_0(\Omega),$$
that is, $-\Delta u = f + h$ in the weak sense.

The proof applies `Elliptic.exists_load_eq_of_forall_abs_le` to the bound of
`Elliptic.IsObstacleSolution.abs_dirichletForm_sub_load_le`. -/
theorem IsObstacleSolution.exists_dirichletForm_eq_load
    (hΩ : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (hψ : IsWeakSolution (dirichletForm Ω) (SobolevEuclideanZero (d + 1) 1 2 Ω) ψ q)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u) :
    ∃ h : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      ‖h‖ ≤ 2 * ‖f ⊔ q - f‖ ∧
      ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω u Φ = load Ω (f + h) Φ := by
  obtain ⟨T, hT⟩ : ∃ T : SobolevEuclideanZero (d + 1) 1 2 Ω →L[ℝ] ℝ,
      T = (dirichletForm Ω u - load Ω f).comp (SobolevEuclideanZero (d + 1) 1 2 Ω).subtypeL :=
    ⟨_, rfl⟩
  have hTapply : ∀ Φ : SobolevEuclideanZero (d + 1) 1 2 Ω,
      T Φ = dirichletForm Ω u Φ - load Ω f Φ := fun Φ ↦ by rw [hT]; rfl
  obtain ⟨h, hh, hTh⟩ := exists_load_eq_of_forall_abs_le T (C := 2 * ‖f ⊔ q - f‖)
    (by positivity) fun Φ ↦ by
    rw [hTapply]
    exact hu.abs_dirichletForm_sub_load_le hΩ hΓ hψ Φ.2
  refine ⟨h, hh, fun Φ hΦ ↦ ?_⟩
  have := hTh ⟨Φ, hΦ⟩
  rw [hTapply] at this
  rw [load_add]
  linarith

end LpBound

/-! ### $H^2$ regularity of the solution of the obstacle problem -/

section Regularity

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- Let $u$ solve the obstacle problem with obstacle $\psi$ and load $f$, and let
$h \in L^2(\Omega)$ with $\int_\Omega \nabla u \cdot \nabla \Phi = \int_\Omega (f + h) \Phi$ for
every $\Phi \in H^1_0(\Omega)$. Then $u \in H^1_0(\Omega)$ and
$$\int_\Omega \nabla u \cdot \nabla \Phi + \int_\Omega u \Phi = \int_\Omega (f + h + u) \Phi
  \qquad \text{for every } \Phi \in H^1_0(\Omega),$$
so $u$ is the Galerkin solution in $H^1_0(\Omega)$ of $-\Delta u + u = f + h + u$ for the form
`Elliptic.laplaceForm Ω` of $-\Delta + 1$. -/
theorem IsObstacleSolution.isGalerkinSolution_laplace {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {h : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    (heq : ∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω u Φ = load Ω (f + h) Φ) :
    IsGalerkinSolution (laplaceForm Ω) (load Ω (f + h + weakDeriv u 0))
      (SobolevEuclideanZero (d + 1) 1 2 Ω) u := by
  refine ⟨hu.mem_zero, fun Φ hΦ ↦ ?_⟩
  rw [laplaceForm_apply_eq_dirichletForm_add_weakDeriv, heq Φ hΦ]
  simp only [load_apply_inner, inner_add_left]

/-- **$H^2$ regularity for the obstacle problem.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a
domain of class $C^2$ by local charts with bounded boundary. There is a constant $C \ge 0$ with
the following property. Let $\psi \in H^1(\Omega)$ and $q \in L^2(\Omega)$ with $\int_\Omega
\nabla \psi \cdot \nabla \Phi = \int_\Omega q \Phi$ for every $\Phi \in H^1_0(\Omega)$, let
$f \in L^2(\Omega)$, and let $u$ solve the obstacle problem with obstacle $\psi$ and load $f$.
Then $u \in H^2(\Omega)$, and every $U \in H^2(\Omega)$ whose function is $u$ almost everywhere
satisfies
$$\|U\|_{H^2(\Omega)} \le C \big(\|f\|_{L^2} + 2 \|\max\{f, q\} - f\|_{L^2} +
  \|u\|_{L^2}\big).$$
This is the case $p = 2$ of Theorem 11.3.12 of [han2009theoretical] (due to Brezis and
Stampacchia), for the Laplacian.

The Lewy–Stampacchia inequality gives $-\Delta u = f + h$ with $h \in L^2(\Omega)$ and
$\|h\|_2 \le 2 \|\max\{f, q\} - f\|_2$
(`Elliptic.IsObstacleSolution.exists_dirichletForm_eq_load`). So $u$ is the weak solution of
$-\Delta u + u = f + h + u$ in $H^1_0(\Omega)$, and the linear regularity theorem
`Elliptic.regularity_dirichlet` (Theorem 9.25 of [brezis2011functional]) applies. The constant
$C$ is the constant of that theorem. -/
theorem regularity_obstacle
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ψ : SobolevEuclidean (d + 1) 1 2 Ω)
        (q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))),
        (∀ Φ ∈ SobolevEuclideanZero (d + 1) 1 2 Ω, dirichletForm Ω ψ Φ = load Ω q Φ) →
        ∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
          (u : SobolevEuclidean (d + 1) 1 2 Ω), IsObstacleSolution Ω ψ f u →
          MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) 2 2 Ω
            volume ∧
          ∀ U : SobolevEuclidean (d + 1) 2 2 Ω,
            fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fn u →
            ‖U‖ ≤ C * (‖f‖ + 2 * ‖f ⊔ q - f‖ + ‖weakDeriv u 0‖) := by
  obtain ⟨C, hC0, hC⟩ := regularity_dirichlet hΩ hΓ
  refine ⟨C, hC0, fun ψ q hψ f u hu ↦ ?_⟩
  obtain ⟨h, hh, heq⟩ := hu.exists_dirichletForm_eq_load (hΩ.of_le (by norm_num)) hΓ hψ
  obtain ⟨hmem, hbound⟩ := hC (f + h + weakDeriv u 0) u (hu.isGalerkinSolution_laplace heq)
  refine ⟨hmem, fun U hU ↦ (hbound U hU).trans (mul_le_mul_of_nonneg_left ?_ hC0)⟩
  calc ‖f + h + weakDeriv u 0‖ ≤ ‖f + h‖ + ‖weakDeriv u 0‖ := norm_add_le _ _
    _ ≤ ‖f‖ + ‖h‖ + ‖weakDeriv u 0‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖f‖ + 2 * ‖f ⊔ q - f‖ + ‖weakDeriv u 0‖ := by gcongr

end Regularity

/-! ### A norm estimate for the bound of Theorem 11.3.12 of [han2009theoretical] -/

section Estimates

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

/-- For $f, q \in L^2(\Omega)$, $\|\max\{f, q\} - f\|_{L^2(\Omega)} \le \|q - f\|_{L^2(\Omega)}$,
since $\max\{f, q\} - f = (q - f)^+$. -/
theorem norm_sup_sub_le (f q : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))) :
    ‖f ⊔ q - f‖ ≤ ‖q - f‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_sub (f ⊔ q) f, Lp.coeFn_sup f q, Lp.coeFn_sub q f] with x h1 h2 h3
  rw [h1, Pi.sub_apply, h2, Pi.sup_apply, h3, Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs]
  rcases le_total (f x) (q x) with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, sub_self, abs_zero]
    exact abs_nonneg _

end Estimates

/-! ### The a priori $H^1$ bound and the $H^2$ bound for obstacles in $H^2(\Omega)$ -/

section APriori

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}

open SobolevMultiIndex

/-- Let $K \ge 1$ and $s, t \ge 0$ be real numbers with $t^2 \le K (s t + s^2)$. Then $t \le 2 K s$.
-/
theorem le_two_mul_of_sq_le {K s t : ℝ} (hK : 1 ≤ K) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : t ^ 2 ≤ K * (s * t + s ^ 2)) : t ≤ 2 * K * s := by
  by_contra hcon
  have hlt : 2 * K * s < t := lt_of_not_ge hcon
  have hKs : 0 ≤ K * s := mul_nonneg (by linarith) hs
  nlinarith [mul_lt_mul_of_pos_left hlt (show (0 : ℝ) < t by linarith), mul_nonneg hKs hs,
    mul_nonneg hKs ht]

/-- The **a priori $H^1$ bound for the obstacle problem**. Let $R \ge 0$, and let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open with $\Omega \subseteq B(0, R)$. Let $u$ solve the
obstacle problem with obstacle $\psi$ and load $f$, and let $w \in H^1_0(\Omega)$ with
$w \ge \psi$ almost everywhere on $\Omega$. Then
$$\|u\|_{H^1(\Omega)} \le 2 \big(1 + (2R)^2\big) \big(\|w\|_{H^1(\Omega)} +
  \|f\|_{L^2(\Omega)}\big).$$

Write $a(u, v) = \int_\Omega \nabla u \cdot \nabla v$ and $\ell(v) = \int_\Omega f v$. The
variational inequality tested with $v = w$ gives $a(u, u) \le a(u, w) - \ell(w) + \ell(u) \le
\|u\| \|w\| + \|f\| \|w\| + \|f\| \|u\|$, and $a(u, u) \ge (1 + (2R)^2)^{-1} \|u\|^2$ by
Poincaré's inequality. -/
theorem IsObstacleSolution.norm_le {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    {ψ : SobolevEuclidean (d + 1) 1 2 Ω}
    {f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))}
    {u : SobolevEuclidean (d + 1) 1 2 Ω} (hu : IsObstacleSolution Ω ψ f u)
    {w : SobolevEuclidean (d + 1) 1 2 Ω} (hw : w ∈ SobolevEuclideanZero (d + 1) 1 2 Ω)
    (hψw : ∀ᵐ x ∂(volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))),
      fn ψ x ≤ fn w x) :
    ‖u‖ ≤ 2 * (1 + (2 * R) ^ 2) * (‖w‖ + ‖f‖) := by
  have hK : (1 : ℝ) ≤ 1 + (2 * R) ^ 2 := by
    have := sq_nonneg (2 * R)
    linarith
  have hpos : (0 : ℝ) < 1 + (2 * R) ^ 2 := by positivity
  have hVI := hu.ineq w hw hψw
  have e1 : load Ω f (w - u) = load Ω f w - load Ω f u := (load Ω f).map_sub w u
  have e2 : dirichletForm Ω u (w - u) = dirichletForm Ω u w - dirichletForm Ω u u :=
    (dirichletForm Ω u).map_sub w u
  have hα := norm_sq_le_dirichletForm_self hR hΩ hu.mem_zero
  have hM : |dirichletForm Ω u w| ≤ ‖u‖ * ‖w‖ := by
    have := dirichletForm_isBoundedWith Ω u w
    rwa [one_mul, Real.norm_eq_abs] at this
  have hℓ : ∀ v : SobolevEuclidean (d + 1) 1 2 Ω, |load Ω f v| ≤ ‖f‖ * ‖v‖ := fun v ↦
    (abs_load_le Ω f v).trans (mul_le_mul_of_nonneg_left (norm_weakDeriv_le v 0) (norm_nonneg _))
  have hℓw := hℓ w
  have hℓu := hℓ u
  have h2 : ‖u‖ ^ 2 ≤ (1 + (2 * R) ^ 2) * (‖u‖ * ‖w‖ + ‖f‖ * ‖w‖ + ‖f‖ * ‖u‖) := by
    refine hα.trans (mul_le_mul_of_nonneg_left ?_ hpos.le)
    have := abs_le.1 hM
    have := abs_le.1 hℓw
    have := abs_le.1 hℓu
    linarith
  have hquad : ‖u‖ ^ 2 ≤ (1 + (2 * R) ^ 2) * ((‖w‖ + ‖f‖) * ‖u‖ + (‖w‖ + ‖f‖) ^ 2) := by
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ hpos.le)
    nlinarith [norm_nonneg u, norm_nonneg w, norm_nonneg f]
  exact le_two_mul_of_sq_le hK (by positivity) (norm_nonneg _) hquad

/-- Let $R \ge 0$, and let $\Omega \subseteq \mathbb{R}^{d+1}$ be a domain of class $C^2$ by local
charts with $\Omega \subseteq B(0, R)$. There is a constant $C \ge 0$ with the following
property. Let $\Psi \in H^2(\Omega)$ and $\psi \in H^1(\Omega)$ have the same function almost
everywhere, and let $\psi^+$ be the function of an element of $H^1_0(\Omega)$. Let
$f \in L^2(\Omega)$, and let $u$ solve the obstacle problem with obstacle $\psi$ and load $f$.
Then $u \in H^2(\Omega)$, and every $U \in H^2(\Omega)$ whose function is $u$ almost everywhere
satisfies
$$\|U\|_{H^2(\Omega)} \le C \big(\|f\|_{L^2(\Omega)} + \|\Psi\|_{H^2(\Omega)}\big).$$
This is Theorem 11.3.12 of [han2009theoretical] for $p = 2$, the Laplacian, an obstacle in
$H^2(\Omega)$ and a $C^2$ domain.

The hypothesis $\psi^+ \in H^1_0(\Omega)$ stands for the condition "$\psi \le 0$ on $\Gamma$" of
[han2009theoretical]. The obstacle has $-\Delta \psi = q := -\sum_i \partial_{ii} \Psi \in
L^2(\Omega)$ in the weak sense (`Elliptic.dirichletForm_eq_load_neg_sobolevLaplacianL`). So
`Elliptic.regularity_obstacle` bounds $\|u\|_{H^2}$ by
$C_0 (\|f\| + 2 \|\max\{f, q\} - f\| + \|u\|_2)$. Then $\|\max\{f, q\} - f\| \le \|q - f\| \le
\|f\| + (d + 1) \|\Psi\|_{H^2}$. The a priori bound `Elliptic.IsObstacleSolution.norm_le` with
$w = \psi^+$, together with $\|\psi^+\|_{H^1} \le \|\psi\|_{H^1} \le \|\Psi\|_{H^2}$, gives
$\|u\|_2 \le 2 (1 + (2R)^2) (\|\Psi\|_{H^2} + \|f\|)$. -/
theorem regularity_obstacle_sobolev_two {R : ℝ} (hR : 0 ≤ R)
    (hΩb : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (hΩ : IsContDiffChartDomain 2 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ψ : SobolevEuclidean (d + 1) 2 2 Ω) (ψ : SobolevEuclidean (d + 1) 1 2 Ω),
        fn ψ =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fn Ψ →
        (∃ w ∈ SobolevEuclideanZero (d + 1) 1 2 Ω,
          fn w =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
            fun x ↦ max (fn ψ x) 0) →
        ∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))))
          (u : SobolevEuclidean (d + 1) 1 2 Ω), IsObstacleSolution Ω ψ f u →
          MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis (fn u) 2 2 Ω
            volume ∧
          ∀ U : SobolevEuclidean (d + 1) 2 2 Ω,
            fn U =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fn u →
            ‖U‖ ≤ C * (‖f‖ + ‖Ψ‖) := by
  have hΓ : Bornology.IsBounded (frontier (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
    (isBounded_ball.subset hΩb).closure.subset frontier_subset_closure
  obtain ⟨C₀, hC₀, hreg⟩ := regularity_obstacle hΩ hΓ
  refine ⟨C₀ * (3 + 2 * ((d : ℝ) + 1) + 2 * (1 + (2 * R) ^ 2)), by positivity,
    fun Ψ ψ hψΨ hψ f u hu ↦ ?_⟩
  obtain ⟨w, hw, hwψ⟩ := hψ
  have hq := dirichletForm_eq_load_neg_sobolevLaplacianL Ψ hψΨ
  obtain ⟨hmem, hbound⟩ := hreg ψ _ hq f u hu
  refine ⟨hmem, fun U hU ↦ (hbound U hU).trans ?_⟩
  -- `‖ψ‖_{H¹} ≤ ‖Ψ‖_{H²}`
  have hψ1 : ‖ψ‖ ≤ ‖Ψ‖ := by
    have e : ψ = toLowerOrder ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 2 Ω volume
        (by norm_num) Ψ :=
      SobolevMultiIndex.ext_of_fn_ae_eq hψΨ
    rw [e]
    exact norm_toLowerOrder_le _ _
  -- `‖max (f, q) − f‖ ≤ ‖f‖ + (d + 1) ‖Ψ‖`
  have h1 : ‖f ⊔ -sobolevLaplacianL Ω Ψ - f‖ ≤ ‖f‖ + ((d : ℝ) + 1) * ‖Ψ‖ := by
    refine (norm_sup_sub_le f _).trans ((norm_sub_le _ f).trans ?_)
    rw [norm_neg]
    have := norm_sobolevLaplacianL_le Ψ
    push_cast at this
    linarith
  -- `‖u‖₂ ≤ ‖u‖_{H¹} ≤ 2 (1 + (2R)²) (‖Ψ‖ + ‖f‖)`
  have hw1 : ‖w‖ ≤ ‖Ψ‖ := (SobolevEuclidean.norm_le_of_fn_ae_eq_posPart hwψ).trans hψ1
  have hu1 : ‖u‖ ≤ 2 * (1 + (2 * R) ^ 2) * (‖w‖ + ‖f‖) :=
    hu.norm_le hR hΩb hw (by
      filter_upwards [hwψ] with x hx
      rw [hx]
      exact le_max_left _ _)
  have hu2 : ‖weakDeriv u 0‖ ≤ 2 * (1 + (2 * R) ^ 2) * (‖Ψ‖ + ‖f‖) :=
    (norm_weakDeriv_le u 0).trans
      (hu1.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))
  have hf0 : 0 ≤ ‖f‖ := norm_nonneg _
  have hΨ0 : 0 ≤ ‖Ψ‖ := norm_nonneg _
  have hd1 : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
  calc C₀ * (‖f‖ + 2 * ‖f ⊔ -sobolevLaplacianL Ω Ψ - f‖ + ‖weakDeriv u 0‖)
      ≤ C₀ * ((3 + 2 * ((d : ℝ) + 1) + 2 * (1 + (2 * R) ^ 2)) * (‖f‖ + ‖Ψ‖)) :=
        mul_le_mul_of_nonneg_left (by
          linarith [mul_nonneg hd1 hf0, mul_nonneg hd1 hΨ0]) hC₀
    _ = C₀ * (3 + 2 * ((d : ℝ) + 1) + 2 * (1 + (2 * R) ^ 2)) * (‖f‖ + ‖Ψ‖) := by ring

end APriori

end Elliptic

end
