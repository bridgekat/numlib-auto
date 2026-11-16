/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Poincare
import Numlib.Analysis.Sobolev.Zero
import Numlib.MeasureTheory.Function.LpSpace.Duality
import Numlib.Variational.PLaplacianEnergy
import NumlibSurface.AtkinsonHan.Chapter03.Section03
import NumlibSurface.AtkinsonHan.Chapter05.Section03

/-!
# Atkinson and Han, Section 8.8: A nonlinear problem

This module formalizes Section 8.8 of [han2009theoretical]. For $1 < p < \infty$ the section studies
the boundary value problem (8.8.1)–(8.8.2)
$$-\operatorname{div} \left[ (1 + |\nabla u|^2)^{p/2 - 1} \nabla u \right] = f \text{ in } \Omega,
  \qquad u = 0 \text{ on } \Gamma,$$
through its weak formulation (8.8.6), $a(u; u, v) = \ell(v)$ for all $v \in V$, and the minimization
problem (8.8.9) for the energy (8.8.10)
$$E(v) = \frac1p \int_\Omega (1 + |\nabla v|^2)^{p/2} \, dx - \ell(v)$$
on $V = W^{1,p}_0(\Omega)$. Lemmas 8.8.1–8.8.4 show that $E$ is coercive, continuous, strictly
convex and Gâteaux differentiable, and Theorem 8.8.5 concludes that the two problems are equivalent
and have exactly one solution.

The proofs use the backbone module `Numlib.Variational.PLaplacianEnergy`, which studies the integral
$\int (1 + |G|^2)^{p/2}$ of an abstract vector field $G$, the Poincaré inequality of
`Numlib.Analysis.Sobolev.Poincare`, Theorem 3.3.12 on the minimizers of a functional on a reflexive
space, and Theorem 5.3.19 on the derivative at a minimizer.

## Main definitions

* Equation (8.8.5), `AtkinsonHan.Chapter08.normV`: the norm $\|v\|_V = (\int_\Omega |\nabla v|^p \,
  dx)^{1/p}$.
* Equation (8.8.10), `AtkinsonHan.Chapter08.energyFunctional`: the energy $E$.
* Equation (8.8.7), `AtkinsonHan.Chapter08.formA`: the form $a(w; u, v) = \int_\Omega (1 + |\nabla
  w|^2)^{p/2 - 1} \nabla u \cdot \nabla v \, dx$.
* Equation (8.8.11), `AtkinsonHan.Chapter08.energyDeriv`: the derivative $E'(u) \in V'$.

## Main results

* Exercise 8.8.1, `AtkinsonHan.Chapter08.normV_le` and `AtkinsonHan.Chapter08.norm_le_normV`:
  $\|\cdot\|_V$ is equivalent to the norm $\|\cdot\|_{1,p}$ of $W^{1,p}(\Omega)$.
* Lemma 8.8.1, `AtkinsonHan.Chapter08.lemma_8_8_1`: $E(v) \ge \frac1p \|v\|_V^p - C \|v\|_V$, so $E$
  is coercive.
* Lemma 8.8.2, `AtkinsonHan.Chapter08.lemma_8_8_2`: $E$ is continuous.
* Lemma 8.8.3, `AtkinsonHan.Chapter08.lemma_8_8_3`: $E$ is strictly convex.
* Lemma 8.8.4, `AtkinsonHan.Chapter08.lemma_8_8_4`: $E$ is Gâteaux differentiable, with $\langle
  E'(u), v \rangle = a(u; u, v) - \ell(v)$ (8.8.11).
* Theorem 8.8.5, `AtkinsonHan.Chapter08.theorem_8_8_5`: (8.8.6) and (8.8.9) are equivalent, and both
  have exactly one solution.

## Conventions

* $\Omega \subseteq B(0, R) \subseteq \mathbb{R}^{d+1}$ is a bounded open set. The source writes
  $\mathbb{R}^d$; the dimension here is $d + 1$, because the backbone's Poincaré inequality is
  stated in that form. The exponent is `p : ℝ≥0∞` with $1 < p < \infty$.
* $V = W^{1,p}_0(\Omega)$ is the backbone's `SobolevEuclideanZero (d + 1) 1 p Ω`, the closure of
  $C_0^\infty(\Omega)$ in $W^{1,p}(\Omega)$ in the multi-index form of Definition 7.2.2. The space
  `AtkinsonHan.Chapter07.definition_7_2_9 1 p Ω` of Chapter 7 is the same closure in the tensor
  form, with an equivalent but different norm.
* The gradient $\nabla v : \Omega \to \mathbb{R}^{d+1}$, $x \mapsto (\partial_i v(x))_i$, is
  `SobolevMultiIndex.gradFn v`, and $|\nabla v|$ is its Euclidean norm.
* The right side is any $f \in V'$, that is `StrongDual ℝ V`, which is the space
  $V' = W^{-1,p^*}(\Omega)$ of the source. The value $\ell(v) = \int_\Omega f v \, dx$ of the source
  is `f v`.

## Implementation notes

* The source takes $\|\cdot\|_V$ as the norm of $V$ and states its equivalence with
  $\|\cdot\|_{1,p}$ as Exercise 8.8.1. Here the type $V$ carries $\|\cdot\|_{1,p}$, and the
  equivalence is `AtkinsonHan.Chapter08.normV_le` and `AtkinsonHan.Chapter08.norm_le_normV`, from
  the Poincaré inequality `SobolevEuclideanZero.norm_le_gradNorm` and the comparison of the
  Euclidean norm of $\nabla v$ with the $\ell^p$ norm of its components in
  `Numlib.Analysis.Sobolev.Cutoff`. So every topological statement (coercivity, continuity,
  reflexivity) is the same for either norm. A second norm structure on a copy of the type would need
  the completeness and the reflexivity of $V$ to be proved again. The constants are explicit but not
  sharp.
* Several general facts are stated on an abstract space, so that their application to $V$ is one
  step: `AtkinsonHan.Chapter08.convexOn_const_mul_sub_of_forall`,
  `AtkinsonHan.Chapter08.strictConvexOn_const_mul_sub_of_forall`,
  `AtkinsonHan.Chapter08.one_div_mul_integral_const_mul_mul_sub`,
  `AtkinsonHan.Chapter08.hasDerivAt_line_of_eq` and
  `AtkinsonHan.Chapter08.forall_nonneg_sub_iff_forall_eq_zero`.

## Deviations from the source

* **Lemma 8.8.2** (generalization). The section assumes $1 < p < \infty$. The continuity of $E$
  holds here for $1 \le p < \infty$. See `AtkinsonHan.Chapter08.lemma_8_8_2`.
-/

open Filter MeasureTheory Metric Set TopologicalSpace Topology
open scoped ENNReal InnerProductSpace

namespace AtkinsonHan.Chapter08

open SobolevMultiIndex

/-! ### The space $V$, its norm (8.8.5), the energy (8.8.10) and the form (8.8.7) -/

section Energy

variable {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Equation (8.8.5)** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open
and $1 \le p < \infty$. The **norm** of $v \in V = W^{1,p}_0(\Omega)$ is
$$\|v\|_V = \left( \int_\Omega |\nabla v|^p \, dx \right)^{1/p},$$
with the Euclidean norm $|\nabla v|$ of the gradient.

The definition uses `p.toReal`. For $p = \infty$ it has no meaning, and all results about it
assume $p < \infty$. -/
noncomputable def normV (v : SobolevEuclideanZero (d + 1) 1 p Ω) : ℝ :=
  (∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
    ‖gradFn (v : SobolevEuclidean (d + 1) 1 p Ω) x‖ ^ p.toReal) ^ (1 / p.toReal)

/-- **Equation (8.8.10)** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open,
$1 \le p < \infty$ and $f \in V'$. The **energy functional** on $V = W^{1,p}_0(\Omega)$ is
$$E(v) = \frac1p \int_\Omega (1 + |\nabla v|^2)^{p/2} \, dx - f(v).$$

The integral is the backbone's `PLaplacian.energy` of the gradient $\nabla v$. -/
noncomputable def energyFunctional (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω))
    (v : SobolevEuclideanZero (d + 1) 1 p Ω) : ℝ :=
  (1 / p.toReal) * PLaplacian.energy p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) - f v

/-- **Equation (8.8.7)** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open
and $1 \le p < \infty$. For $w, u, v \in V = W^{1,p}_0(\Omega)$ the **form** is
$$a(w; u, v) = \int_\Omega (1 + |\nabla w|^2)^{p/2 - 1} \, \nabla u \cdot \nabla v \, dx.$$

The weight $(1 + |\xi|^2)^{p/2 - 1}$ is `PLaplacian.derivWeight`. -/
noncomputable def formA (w u v : SobolevEuclideanZero (d + 1) 1 p Ω) : ℝ :=
  ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
    PLaplacian.derivWeight p.toReal (gradFn (w : SobolevEuclidean (d + 1) 1 p Ω) x)
      * ⟪gradFn (u : SobolevEuclidean (d + 1) 1 p Ω) x,
          gradFn (v : SobolevEuclidean (d + 1) 1 p Ω) x⟫_ℝ

variable {Ω}

/-- The norm (8.8.5) is nonnegative: $\|v\|_V \ge 0$. -/
theorem normV_nonneg (v : SobolevEuclideanZero (d + 1) 1 p Ω) : 0 ≤ normV Ω v :=
  Real.rpow_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- For $p < \infty$, $\|v\|_V^p = \int_\Omega |\nabla v|^p \, dx$. -/
theorem normV_rpow (hp' : p ≠ ⊤) (v : SobolevEuclideanZero (d + 1) 1 p Ω) :
    normV Ω v ^ p.toReal = ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))),
      ‖gradFn (v : SobolevEuclidean (d + 1) 1 p Ω) x‖ ^ p.toReal := by
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp'
  rw [normV, ← Real.rpow_mul (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _),
    one_div_mul_cancel hpr.ne', Real.rpow_one]

/-- **Exercise 8.8.1** of [han2009theoretical], one half. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be
open and $1 \le p < \infty$. Then for every $v \in W^{1,p}_0(\Omega)$,
$$\|v\|_V \le (d + 1) \, \|v\|_{1,p}.$$
-/
theorem normV_le (hp' : p ≠ ⊤) (v : SobolevEuclideanZero (d + 1) 1 p Ω) :
    normV Ω v ≤ (d + 1 : ℝ) * ‖v‖ := by
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp'
  have h1 := integral_norm_gradFn_rpow_le hp' (v : SobolevEuclidean (d + 1) 1 p Ω)
  simp only [Fintype.card_fin] at h1
  have h2 : SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 p Ω) ≤ ‖v‖ :=
    SobolevMultiIndex.gradNorm_le_norm _
  rw [← normV_rpow hp'] at h1
  have h3 : normV Ω v ^ p.toReal ≤ ((d + 1 : ℝ) * ‖v‖) ^ p.toReal := by
    rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
    refine h1.trans ?_
    push_cast
    gcongr
    exact SobolevMultiIndex.gradNorm_nonneg _
  exact (Real.rpow_le_rpow_iff (normV_nonneg v) (by positivity) hpr).1 h3

/-- **Exercise 8.8.1** of [han2009theoretical], the other half (the Poincaré inequality). Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open and contained in the ball $B(0, R)$ with $R \ge 0$,
and let $1 \le p < \infty$. Then for every $v \in W^{1,p}_0(\Omega)$,
$$\|v\|_{1,p} \le \left( 1 + (2R)^p \right)^{1/p} (d + 1)^{1/p} \, \|v\|_V.$$
-/
theorem norm_le_normV (hp' : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (v : SobolevEuclideanZero (d + 1) 1 p Ω) :
    ‖v‖ ≤ (1 + (2 * R) ^ p.toReal) ^ (1 / p.toReal) * (d + 1 : ℝ) ^ (1 / p.toReal)
      * normV Ω v := by
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp'
  have hP := SobolevEuclideanZero.norm_le_gradNorm hp' hR hΩ v
  have h1 := gradNorm_rpow_le_integral hp' (v : SobolevEuclidean (d + 1) 1 p Ω)
  simp only [Fintype.card_fin] at h1
  rw [← normV_rpow hp'] at h1
  have h2 : SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 p Ω)
      ≤ (d + 1 : ℝ) ^ (1 / p.toReal) * normV Ω v := by
    have h3 : SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 p Ω) ^ p.toReal
        ≤ ((d + 1 : ℝ) ^ (1 / p.toReal) * normV Ω v) ^ p.toReal := by
      rw [Real.mul_rpow (by positivity) (normV_nonneg v), ← Real.rpow_mul (by positivity),
        one_div_mul_cancel hpr.ne', Real.rpow_one]
      exact_mod_cast h1
    exact (Real.rpow_le_rpow_iff (SobolevMultiIndex.gradNorm_nonneg _)
      (mul_nonneg (by positivity) (normV_nonneg v)) hpr).1 h3
  calc ‖v‖ ≤ (1 + (2 * R) ^ p.toReal) ^ (1 / p.toReal)
        * SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 p Ω) := hP
    _ ≤ (1 + (2 * R) ^ p.toReal) ^ (1 / p.toReal) * ((d + 1 : ℝ) ^ (1 / p.toReal) * normV Ω v) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

end Energy

/-! ### Lemmas 8.8.1–8.8.3: coercivity, continuity, strict convexity -/

section Lemmas

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Poincaré inequality as injectivity of the gradient. Let $\Omega \subseteq \mathbb{R}^{d+1}$
be open and contained in the ball $B(0, R)$ with $R \ge 0$, and let $1 \le p < \infty$. If
$u, v \in W^{1,p}_0(\Omega)$ have $\nabla u = \nabla v$ almost everywhere on $\Omega$, then
$u = v$. -/
theorem eq_of_gradFn_ae_eq (hp' : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    {u v : SobolevEuclideanZero (d + 1) 1 p Ω}
    (h : gradFn (u : SobolevEuclidean (d + 1) 1 p Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) : u = v := by
  have h0 : gradFn ((u - v : SobolevEuclideanZero (d + 1) 1 p Ω) : SobolevEuclidean (d + 1) 1 p Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] 0 := by
    filter_upwards [gradFn_sub (u : SobolevEuclidean (d + 1) 1 p Ω) v, h] with x h1 h2
    rw [Submodule.coe_sub, h1, Pi.sub_apply, h2, sub_self, Pi.zero_apply]
  have hg := gradNorm_eq_zero_of_gradFn_ae_eq_zero hp' h0
  have hP := SobolevEuclideanZero.norm_le_gradNorm hp' hR hΩ (u - v)
  rw [hg, mul_zero] at hP
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hP)

/-- **Lemma 8.8.1** of [han2009theoretical] (coercivity). Let $\Omega \subseteq \mathbb{R}^{d+1}$ be
open and contained in the ball $B(0, R)$ with $R \ge 0$, let $1 < p < \infty$ and let
$f \in V'$. Then there is a constant $C$ such that for all $v \in V$
$$E(v) \ge \frac1p \|v\|_V^p - C \|v\|_V,$$
and $E$ is coercive: $E(v) \to \infty$ as $\|v\| \to \infty$.

The source takes $C = \|f\|_{V'}$, the dual norm for $\|\cdot\|_V$. Here the norm of $V$ is
$\|\cdot\|_{1,p}$, and $C$ is $\|f\|$ times the constant of the Poincaré inequality. Coercivity
is `IsCoerciveFunctionalOn` on all of $V$ (Definition 3.3.9). It is stated for
$\|\cdot\|_{1,p}$, and it holds for $\|\cdot\|_V$ as well, since the two norms are equivalent.
The bound $\frac1p \int |\nabla v|^p \le \frac1p \int (1 + |\nabla v|^2)^{p/2}$ is
`PLaplacian.integral_norm_rpow_le_energy`. -/
theorem lemma_8_8_1 (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω)) :
    (∃ C : ℝ, ∀ v, (1 / p.toReal) * normV Ω v ^ p.toReal - C * normV Ω v
      ≤ energyFunctional Ω f v) ∧
    IsCoerciveFunctionalOn (energyFunctional Ω f) univ := by
  have hpr : 1 < p.toReal := PLaplacian.one_lt_toReal hp hp'
  have hpr0 : 0 < p.toReal := by linarith
  have := isFiniteMeasure_restrict_of_subset_ball hΩ
  -- the constant of Poincaré's inequality
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℝ, 0 < K ∧ ∀ v : SobolevEuclideanZero (d + 1) 1 p Ω,
      ‖v‖ ≤ K * normV Ω v :=
    ⟨_, by positivity, fun v ↦ norm_le_normV hp' hR hΩ v⟩
  have hlow : ∀ v : SobolevEuclideanZero (d + 1) 1 p Ω,
      (1 / p.toReal) * normV Ω v ^ p.toReal - (‖f‖ * K) * normV Ω v ≤ energyFunctional Ω f v := by
    intro v
    have h1 : normV Ω v ^ p.toReal ≤ PLaplacian.energy p
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) := by
      rw [normV_rpow hp']
      exact PLaplacian.integral_norm_rpow_le_energy hp.le hp' (memLp_gradFn _)
    have h2 : f v ≤ ‖f‖ * K * normV Ω v := by
      calc f v ≤ ‖f v‖ := Real.le_norm_self _
        _ ≤ ‖f‖ * ‖v‖ := f.le_opNorm v
        _ ≤ ‖f‖ * (K * normV Ω v) := mul_le_mul_of_nonneg_left (hK v) (norm_nonneg _)
        _ = ‖f‖ * K * normV Ω v := by ring
    unfold energyFunctional
    have h3 : (1 / p.toReal) * normV Ω v ^ p.toReal ≤ (1 / p.toReal) * PLaplacian.energy p
        (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  refine ⟨⟨‖f‖ * K, hlow⟩, ?_⟩
  -- coercivity in the `W^{1,p}` norm
  refine isCoerciveFunctionalOn_of_rpow_sub_mul_le (c := 1 / (p.toReal * K ^ p.toReal))
    (C := ‖f‖) (by positivity) hpr fun v _ ↦ ?_
  have h4 : ‖v‖ ^ p.toReal ≤ K ^ p.toReal * normV Ω v ^ p.toReal := by
    rw [← Real.mul_rpow hK0.le (normV_nonneg v)]
    exact Real.rpow_le_rpow (norm_nonneg _) (hK v) hpr0.le
  have h5 : 1 / (p.toReal * K ^ p.toReal) * ‖v‖ ^ p.toReal
      ≤ (1 / p.toReal) * normV Ω v ^ p.toReal := by
    have hKp : 0 < K ^ p.toReal := by positivity
    calc 1 / (p.toReal * K ^ p.toReal) * ‖v‖ ^ p.toReal
        ≤ 1 / (p.toReal * K ^ p.toReal) * (K ^ p.toReal * normV Ω v ^ p.toReal) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = (1 / p.toReal) * normV Ω v ^ p.toReal := by
          field_simp
  have h6 : f v ≤ ‖f‖ * ‖v‖ := (Real.le_norm_self _).trans (f.le_opNorm v)
  have h7 : normV Ω v ^ p.toReal ≤ PLaplacian.energy p
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) := by
    rw [normV_rpow hp']
    exact PLaplacian.integral_norm_rpow_le_energy hp.le hp' (memLp_gradFn _)
  have h8 : (1 / p.toReal) * normV Ω v ^ p.toReal ≤ (1 / p.toReal) * PLaplacian.energy p
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) :=
    mul_le_mul_of_nonneg_left h7 (by positivity)
  unfold energyFunctional
  linarith

/-- Let $V$ be a real normed space, $f \in V'$, $c \ge 0$, and let $\Phi : V \to \mathbb{R}$ satisfy
$\Phi(a u + b v) \le a \Phi(u) + b \Phi(v)$ for all $u, v$ and all $a, b \ge 0$ with
$a + b = 1$. Then $v \mapsto c \, \Phi(v) - f(v)$ is convex on $V$. -/
theorem convexOn_const_mul_sub_of_forall {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Φ : V → ℝ} (f : V →L[ℝ] ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hΦ : ∀ u v : V, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      Φ (a • u + b • v) ≤ a * Φ u + b * Φ v) :
    ConvexOn ℝ univ fun v ↦ c * Φ v - f v := by
  refine ⟨convex_univ, fun u _ v _ a b ha hb hab ↦ ?_⟩
  have hf : f (a • u + b • v) = a * f u + b * f v := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp only [smul_eq_mul]
  rw [hf]
  nlinarith [mul_le_mul_of_nonneg_left (hΦ u v a b ha hb hab) hc]

/-- Let $V$ be a real normed space, $f \in V'$, $c > 0$, and let $\Phi : V \to \mathbb{R}$ satisfy
$\Phi(a u + b v) < a \Phi(u) + b \Phi(v)$ for all $u \ne v$ and all $a, b > 0$ with $a + b = 1$.
Then $v \mapsto c \, \Phi(v) - f(v)$ is strictly convex on $V$. -/
theorem strictConvexOn_const_mul_sub_of_forall {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {Φ : V → ℝ} (f : V →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hΦ : ∀ u v : V, u ≠ v → ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      Φ (a • u + b • v) < a * Φ u + b * Φ v) :
    StrictConvexOn ℝ univ fun v ↦ c * Φ v - f v := by
  refine ⟨convex_univ, fun u _ v _ huv a b ha hb hab ↦ ?_⟩
  have hf : f (a • u + b • v) = a * f u + b * f v := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp only [smul_eq_mul]
  rw [hf]
  nlinarith [mul_lt_mul_of_pos_left (hΦ u v huv a b ha hb hab) hc]

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open and contained in a ball $B(0, R)$, let
$1 \le p < \infty$ and let $f \in V'$. Then the energy $E$ is convex on $V$.

This is the non-strict half of Lemma 8.8.3 of [han2009theoretical]. The proof uses the convexity
of $\xi \mapsto (1 + |\xi|^2)^{p/2}$ under the integral (`PLaplacian.energy_combo_le`) and the
linearity of the gradient (`SobolevMultiIndex.gradFn_combo`). -/
theorem convexOn_energyFunctional (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω)) :
    ConvexOn ℝ univ (energyFunctional Ω f) := by
  have := isFiniteMeasure_restrict_of_subset_ball hΩ
  refine convexOn_const_mul_sub_of_forall f (by positivity) fun u v a b ha hb hab ↦ ?_
  calc PLaplacian.energy p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (gradFn ((a • u + b • v : SobolevEuclideanZero (d + 1) 1 p Ω) :
          SobolevEuclidean (d + 1) 1 p Ω))
      = PLaplacian.energy p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (a • gradFn (u : SobolevEuclidean (d + 1) 1 p Ω)
          + b • gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) :=
        PLaplacian.energy_congr_ae p (gradFn_combo a b (u : SobolevEuclidean (d + 1) 1 p Ω) v)
    _ ≤ _ := PLaplacian.energy_combo_le (p := p) Fact.out hp'
        (memLp_gradFn (u : SobolevEuclidean (d + 1) 1 p Ω))
        (memLp_gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) ha hb hab

/-- **Lemma 8.8.3** of [han2009theoretical] (strict convexity). Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open and contained in the ball $B(0, R)$ with $R \ge 0$,
let $1 < p < \infty$ and let $f \in V'$. Then the energy $E$ is strictly convex on $V$.

The function $\xi \mapsto \frac1p (1 + |\xi|^2)^{p/2}$ is strictly convex on $\mathbb{R}^{d+1}$
(Exercise 5.3.13, `PLaplacian.strictConvexOn_kernel`). This gives a strict inequality under the
integral where $\nabla u \ne \nabla v$ (`PLaplacian.energy_combo_lt`), and $\nabla u = \nabla v$
almost everywhere forces $u = v$ by the Poincaré inequality
(`AtkinsonHan.Chapter08.eq_of_gradFn_ae_eq`). -/
theorem lemma_8_8_3 (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω)) :
    StrictConvexOn ℝ univ (energyFunctional Ω f) := by
  have := isFiniteMeasure_restrict_of_subset_ball hΩ
  have hpr : 0 < 1 / p.toReal := by
    have := PLaplacian.one_lt_toReal hp hp'
    positivity
  refine strictConvexOn_const_mul_sub_of_forall f hpr fun u v huv a b ha hb hab ↦ ?_
  have hne : ¬ gradFn (u : SobolevEuclidean (d + 1) 1 p Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        gradFn (v : SobolevEuclidean (d + 1) 1 p Ω) :=
    fun h ↦ huv (eq_of_gradFn_ae_eq hp' hR hΩ h)
  calc PLaplacian.energy p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (gradFn ((a • u + b • v : SobolevEuclideanZero (d + 1) 1 p Ω) :
          SobolevEuclidean (d + 1) 1 p Ω))
      = PLaplacian.energy p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (a • gradFn (u : SobolevEuclidean (d + 1) 1 p Ω)
          + b • gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) :=
        PLaplacian.energy_congr_ae p (gradFn_combo a b (u : SobolevEuclidean (d + 1) 1 p Ω) v)
    _ < _ := PLaplacian.energy_combo_lt hp hp'
        (memLp_gradFn (u : SobolevEuclidean (d + 1) 1 p Ω))
        (memLp_gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) hne ha hb hab

/-- The energy is bounded above on bounded sets. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open and
contained in a ball $B(0, R)$, let $1 \le p < \infty$ and let $f \in V'$. Then for every
$v \in V$,
$$E(v) \le \frac1p \, 2^p \left( |\Omega| + (d + 1)^p \|v\|^p \right) + \|f\| \, \|v\|.$$

The proof uses `PLaplacian.energy_le` and `SobolevMultiIndex.integral_norm_gradFn_rpow_le`. -/
theorem energyFunctional_le (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω))
    (v : SobolevEuclideanZero (d + 1) 1 p Ω) :
    energyFunctional Ω f v ≤ (1 / p.toReal) * (2 ^ p.toReal
      * ((volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))).real univ
        + (d + 1 : ℝ) ^ p.toReal * ‖v‖ ^ p.toReal)) + ‖f‖ * ‖v‖ := by
  have := isFiniteMeasure_restrict_of_subset_ball hΩ
  have hpr : 0 ≤ 1 / p.toReal := by positivity
  have h1 := PLaplacian.energy_le (p := p) Fact.out hp'
    (memLp_gradFn (v : SobolevEuclidean _ 1 p Ω))
  have h2 := integral_norm_gradFn_rpow_le hp' (v : SobolevEuclidean (d + 1) 1 p Ω)
  simp only [Fintype.card_fin] at h2
  have h3 : SobolevMultiIndex.gradNorm (v : SobolevEuclidean (d + 1) 1 p Ω) ^ p.toReal
      ≤ ‖v‖ ^ p.toReal :=
    Real.rpow_le_rpow (SobolevMultiIndex.gradNorm_nonneg _)
      (SobolevMultiIndex.gradNorm_le_norm _) ENNReal.toReal_nonneg
  have h4 : -(f v) ≤ ‖f‖ * ‖v‖ := by
    have := f.le_opNorm v
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (f v)]
  have h5 : PLaplacian.energy p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) ≤ 2 ^ p.toReal
      * ((volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))).real univ
        + (d + 1 : ℝ) ^ p.toReal * ‖v‖ ^ p.toReal) := by
    refine h1.trans ?_
    gcongr
    refine h2.trans ?_
    push_cast
    gcongr
  unfold energyFunctional
  nlinarith [mul_le_mul_of_nonneg_left h5 hpr]

/-- **Lemma 8.8.2** of [han2009theoretical] (continuity). Let $\Omega \subseteq \mathbb{R}^{d+1}$ be
open and contained in a ball $B(0, R)$, let $1 \le p < \infty$ and let $f \in V'$. Then the
energy $E$ is continuous on $V$.

**Generalization.** The section assumes $1 < p < \infty$. The lemma here also holds for $p = 1$.

The source estimates $|E(v) - E(u)|$ by a mean-value argument and Hölder's inequality. Here
continuity follows from the convexity of $E$ (`AtkinsonHan.Chapter08.convexOn_energyFunctional`)
and its bound on balls (`AtkinsonHan.Chapter08.energyFunctional_le`): a convex function that is
bounded above near every point is continuous (`ConvexOn.continuousOn_tfae`). -/
theorem lemma_8_8_2 (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω)) :
    Continuous (energyFunctional Ω f) := by
  rw [← continuousOn_univ]
  refine ((convexOn_energyFunctional hp' hΩ f).continuousOn_tfae isOpen_univ univ_nonempty).out 5 2
    |>.1 fun x₀ _ ↦ ?_
  refine ⟨(1 / p.toReal) * (2 ^ p.toReal
      * ((volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))).real univ
        + (d + 1 : ℝ) ^ p.toReal * (‖x₀‖ + 1) ^ p.toReal)) + ‖f‖ * (‖x₀‖ + 1), ?_⟩
  rw [Filter.eventually_map]
  filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with v hv
  have hv1 : ‖v‖ ≤ ‖x₀‖ + 1 := by
    have := mem_ball_iff_norm.1 hv
    linarith [norm_le_norm_add_norm_sub' v x₀]
  refine (energyFunctional_le hp' hΩ f v).trans ?_
  gcongr

end Lemmas

/-! ### Lemma 8.8.4: the Gâteaux derivative (8.8.11) -/

section Gateaux

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {p : ℝ≥0∞} [Fact (1 ≤ p)]

attribute [local instance] ENNReal.fact_one_le_conjExponent

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open and contained in a ball $B(0, R)$, let
$1 < p < \infty$, let $u \in V$ and let $i$ be an index. The **weighted derivative**
$(1 + |\nabla u|^2)^{p/2 - 1} \partial_i u$, which appears in the derivative (8.8.11), as an
element of $L^{p'}(\Omega)$ with $p'$ the conjugate exponent of $p$.

The membership in $L^{p'}(\Omega)$ is `PLaplacian.memLp_derivWeight_mul`. -/
noncomputable def weightedDeriv (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (u : SobolevEuclideanZero (d + 1) 1 p Ω) (i : Fin (d + 1)) :
    Lp ℝ (ENNReal.conjExponent p) (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) :=
  haveI := isFiniteMeasure_restrict_of_subset_ball hΩ
  (PLaplacian.memLp_derivWeight_mul hp hp' (memLp_gradFn (u : SobolevEuclidean (d + 1) 1 p Ω))
    (Lp.aestronglyMeasurable (SobolevMultiIndex.weakDeriv (u : SobolevEuclidean (d + 1) 1 p Ω)
      (MultiIndexLE.single i)))
    fun x ↦ by
      rw [← Real.norm_eq_abs]
      exact norm_le_norm_gradFn _ x i).toLp _

/-- The weighted derivative of $u$ in direction $i$ is equal almost everywhere on $\Omega$ to the
function $(1 + |\nabla u|^2)^{p/2 - 1} \partial_i u$. -/
theorem coeFn_weightedDeriv (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (u : SobolevEuclideanZero (d + 1) 1 p Ω) (i : Fin (d + 1)) :
    (weightedDeriv hp hp' hΩ u i : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))]
        fun x ↦ PLaplacian.derivWeight p.toReal (gradFn (u : SobolevEuclidean (d + 1) 1 p Ω) x)
          * SobolevMultiIndex.weakDeriv (u : SobolevEuclidean (d + 1) 1 p Ω)
            (MultiIndexLE.single i) x :=
  MemLp.coeFn_toLp _

/-- **Equation (8.8.11)** of [han2009theoretical], the derivative as a functional. Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open and contained in a ball $B(0, R)$, let
$1 < p < \infty$, $f \in V'$ and $u \in V$. The **derivative** $E'(u) \in V'$ is the bounded
linear functional
$$v \mapsto \sum_i \int_\Omega (1 + |\nabla u|^2)^{p/2 - 1} \, \partial_i u \, \partial_i v \,
  dx - f(v).$$

Each term is the $L^p$–$L^{p'}$ pairing `MeasureTheory.Lp.toDualCLM` of the weighted derivative
of $u$ in $L^{p'}(\Omega)$ with $\partial_i v \in L^p(\Omega)$. Its value is $a(u; u, v) - f(v)$
by `AtkinsonHan.Chapter08.energyDeriv_apply`. -/
noncomputable def energyDeriv (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω))
    (u : SobolevEuclideanZero (d + 1) 1 p Ω) : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω) :=
  (∑ i : Fin (d + 1), (Lp.toDualCLM ℝ p (ENNReal.conjExponent p)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (weightedDeriv hp hp' hΩ u i)).comp
    ((SobolevMultiIndex.weakDerivL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume
      (MultiIndexLE.single i)).comp (SobolevEuclideanZero (d + 1) 1 p Ω).subtypeL)) - f

/-- **Equation (8.8.11)** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open
and contained in a ball $B(0, R)$, let $1 < p < \infty$, $f \in V'$ and $u, v \in V$. Then
$$\langle E'(u), v \rangle = a(u; u, v) - f(v).$$
-/
theorem energyDeriv_apply (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω))
    (u v : SobolevEuclideanZero (d + 1) 1 p Ω) :
    energyDeriv hp hp' hΩ f u v = formA Ω u u v - f v := by
  have hint : ∀ i : Fin (d + 1), Integrable (fun x ↦ (weightedDeriv hp hp' hΩ u i : _ → ℝ) x
      * SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 p Ω) (MultiIndexLE.single i) x)
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) := fun i ↦
    (Lp.memLp (weightedDeriv hp hp' hΩ u i)).integrable_mul (Lp.memLp _)
  have h1 : energyDeriv hp hp' hΩ f u v = (∑ i : Fin (d + 1),
      ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))), (weightedDeriv hp hp' hΩ u i : _ → ℝ) x
        * SobolevMultiIndex.weakDeriv (v : SobolevEuclidean (d + 1) 1 p Ω)
          (MultiIndexLE.single i) x) - f v := by
    simp only [energyDeriv, sub_apply, sum_apply, ContinuousLinearMap.comp_apply,
      Lp.toDualCLM_apply]
    rfl
  rw [h1, formA, ← integral_finsetSum _ fun i _ ↦ hint i]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 fun i ↦ coeFn_weightedDeriv hp hp' hΩ u i] with x hx
  simp only [hx, inner_gradFn, Finset.mul_sum, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- For $c \ne 0$, real functions $a$ and $b$ on a measure space, and $r \in \mathbb{R}$,
$$\frac1c \int c \, a \, b \, d\mu - r = \int a \, b \, d\mu - r.$$

If $a b$ is not integrable, both integrals are $0$ by the convention of the Bochner integral. -/
theorem one_div_mul_integral_const_mul_mul_sub {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {c : ℝ} (hc : c ≠ 0) (a b : X → ℝ) (r : ℝ) :
    (1 / c) * (∫ x, c * a x * b x ∂μ) - r = (∫ x, a x * b x ∂μ) - r := by
  have e : (fun x ↦ c * a x * b x) = fun x ↦ c * (a x * b x) := by
    funext x
    ring
  rw [e, integral_const_mul]
  field_simp

/-- Let $V$ be a real normed space, $E : V \to \mathbb{R}$, $f \in V'$, $c \in \mathbb{R}$,
$u, v \in V$, and $\Psi : \mathbb{R} \to \mathbb{R}$. If
$E(u + t v) = c \, \Psi(t) - f(u + t v)$ for all $t \in \mathbb{R}$ and $\Psi$ has the
derivative $\Psi'$ at $0$, then $t \mapsto E(u + t v)$ has the derivative $c \, \Psi' - f(v)$ at
$t = 0$. -/
theorem hasDerivAt_line_of_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {E : V → ℝ}
    (f : V →L[ℝ] ℝ) {c : ℝ} {Ψ : ℝ → ℝ} {u v : V} {Ψ' : ℝ}
    (hE : ∀ t : ℝ, E (u + t • v) = c * Ψ t - f (u + t • v)) (hΨ : HasDerivAt Ψ Ψ' 0) :
    HasDerivAt (fun t : ℝ ↦ E (u + t • v)) (c * Ψ' - f v) 0 := by
  have hfun : (fun t : ℝ ↦ E (u + t • v)) = fun t ↦ c * Ψ t - (f u + t * f v) := by
    funext t
    rw [hE t, map_add, map_smul, smul_eq_mul]
  rw [hfun]
  have h := (hΨ.const_mul c).sub (((hasDerivAt_id (0 : ℝ)).const_mul (f v)).const_add (f u))
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)).congr_deriv ?_
  · simp only [Pi.sub_apply, id, mul_comm]
  · simp

/-- **Lemma 8.8.4** of [han2009theoretical] (Gâteaux differentiability). Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open and contained in a ball $B(0, R)$, let
$1 < p < \infty$ and let $f \in V'$. Then at every $u \in V$ the energy $E$ is Gâteaux
differentiable with derivative $E'(u)$ (`AtkinsonHan.Chapter08.energyDeriv`), and for all
$v \in V$ the formula (8.8.11) holds:
$$\langle E'(u), v \rangle = \int_\Omega (1 + |\nabla u|^2)^{p/2 - 1} \, \nabla u \cdot \nabla v
  \, dx - f(v).$$

Gâteaux differentiability is `AtkinsonHan.Chapter05.HasGateauxDerivAt` of Definition 5.3.2. As
in the source, the difference quotient converges by dominated convergence, with the dominating
function $[1 + (|\nabla u| + |\nabla v|)^2]^{(p-1)/2} |\nabla v| \in L^1(\Omega)$
(`PLaplacian.hasDerivAt_energy_line`, `PLaplacian.integrable_kernelBound_mul`). -/
theorem lemma_8_8_4 (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ}
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω))
    (u : SobolevEuclideanZero (d + 1) 1 p Ω) :
    Chapter05.HasGateauxDerivAt (energyFunctional Ω f) (energyDeriv hp hp' hΩ f u) u ∧
      ∀ v, energyDeriv hp hp' hΩ f u v = formA Ω u u v - f v := by
  have := isFiniteMeasure_restrict_of_subset_ball hΩ
  refine ⟨fun v ↦ ?_, energyDeriv_apply hp hp' hΩ f u⟩
  rw [energyDeriv_apply]
  -- the line `t ↦ E(u + t v)` is `t ↦ (1/p) Φ(∇u + t ∇v) − f(u + t v)`
  have hΦ : ∀ t : ℝ, PLaplacian.energy p
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (gradFn ((u + t • v : SobolevEuclideanZero (d + 1) 1 p Ω) : SobolevEuclidean (d + 1) 1 p Ω))
      = PLaplacian.energy p (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
        (gradFn (u : SobolevEuclidean (d + 1) 1 p Ω)
          + t • gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) := by
    intro t
    have hcoe : ((u + t • v : SobolevEuclideanZero (d + 1) 1 p Ω) : SobolevEuclidean (d + 1) 1 p Ω)
        = (u : SobolevEuclidean (d + 1) 1 p Ω) + t • (v : SobolevEuclidean (d + 1) 1 p Ω) := rfl
    rw [hcoe]
    refine PLaplacian.energy_congr_ae p ?_
    filter_upwards [gradFn_add (u : SobolevEuclidean (d + 1) 1 p Ω) (t • v),
      gradFn_smul t (v : SobolevEuclidean (d + 1) 1 p Ω)] with x h1 h2
    rw [h1, Pi.add_apply, h2]
    rfl
  have hE : ∀ t : ℝ, energyFunctional Ω f (u + t • v) = (1 / p.toReal) * PLaplacian.energy p
      (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
      (gradFn (u : SobolevEuclidean (d + 1) 1 p Ω)
        + t • gradFn (v : SobolevEuclidean (d + 1) 1 p Ω)) - f (u + t • v) := fun t ↦
    congrArg (fun z ↦ (1 / p.toReal) * z - f (u + t • v)) (hΦ t)
  have hD := PLaplacian.hasDerivAt_energy_line hp hp'
    (memLp_gradFn (u : SobolevEuclidean (d + 1) 1 p Ω))
    (memLp_gradFn (v : SobolevEuclidean (d + 1) 1 p Ω))
  have key := hasDerivAt_line_of_eq f hE hD
  have hpr : 0 < p.toReal := by linarith [PLaplacian.one_lt_toReal hp hp']
  exact key.congr_deriv (one_div_mul_integral_const_mul_mul_sub hpr.ne' _ _ _)

end Gateaux

/-! ### Theorem 8.8.5: existence, uniqueness, and the equivalence of (8.8.6) and (8.8.9) -/

section Main

variable {d : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Let $V$ be a real normed space, $L \in V'$ and $w \in V$. Then $L(v - w) \ge 0$ for all
$v \in V$ if and only if $L = 0$. -/
theorem forall_nonneg_sub_iff_forall_eq_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (w : V) : (∀ v, 0 ≤ L (v - w)) ↔ ∀ v, L v = 0 := by
  constructor
  · intro H v
    have h1 := H (v + w)
    have h2 := H (-v + w)
    rw [add_sub_cancel_right] at h1 h2
    rw [map_neg] at h2
    linarith
  · intro H v
    rw [H]

/-- **Theorem 8.8.5** of [han2009theoretical]. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open and
contained in the ball $B(0, R)$ with $R \ge 0$, let $1 < p < \infty$ and let $f \in V'$, where
$V = W^{1,p}_0(\Omega)$. Then:

* the minimization problem (8.8.9), to find $u \in V$ with $E(u) = \inf_{v \in V} E(v)$, has
  exactly one solution;
* $u \in V$ solves (8.8.9) if and only if $u$ solves the weak formulation (8.8.6),
  $a(u; u, v) = f(v)$ for all $v \in V$;
* so (8.8.6) also has exactly one solution.

Existence is Theorem 3.3.12 (`AtkinsonHan.Chapter03.theorem_3_3_12`) on the reflexive space $V$,
for the energy, which is coercive by Lemma 8.8.1, continuous by Lemma 8.8.2 and convex by Lemma
8.8.3. The space $V$ is reflexive for every $1 < p < \infty$ by
`SobolevMultiIndexZero.instIsReflexive` and the reflexivity of $L^p(\Omega)$
(`MeasureTheory.Lp.instIsReflexive`). Uniqueness is the strict convexity of Lemma 8.8.3
(`IsMinOn.eq_of_strictConvexOn`). The equivalence is Theorem 5.3.19 in its subspace form
(`AtkinsonHan.Chapter05.theorem_5_3_19_submodule`, with $K = V$) together with Lemma 8.8.4: $u$
minimizes $E$ if and only if $\langle E'(u), v \rangle = a(u; u, v) - f(v) = 0$ for all $v$. -/
theorem theorem_8_8_5 (hp : 1 < p) (hp' : p ≠ ⊤) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) ⊆ ball 0 R)
    (f : StrongDual ℝ (SobolevEuclideanZero (d + 1) 1 p Ω)) :
    (∃! u, IsMinOn (energyFunctional Ω f) univ u) ∧
    (∀ u, IsMinOn (energyFunctional Ω f) univ u ↔ ∀ v, formA Ω u u v = f v) ∧
    ∃! u : SobolevEuclideanZero (d + 1) 1 p Ω, ∀ v, formA Ω u u v = f v := by
  have : Fact (1 < p) := ⟨hp⟩
  have : Fact (p ≠ ⊤) := ⟨hp'⟩
  have hconv := convexOn_energyFunctional hp' hΩ f
  have hcont := lemma_8_8_2 hp' hΩ f
  have hcoer := (lemma_8_8_1 hp hp' hR hΩ f).2
  have hstrict := lemma_8_8_3 hp hp' hR hΩ f
  obtain ⟨u, -, humin⟩ := Chapter03.theorem_3_3_12 univ_nonempty isClosed_univ convex_univ hconv
    (hcont.lowerSemicontinuous.lowerSemicontinuousOn univ) (Or.inr hcoer)
  have huniq : ∀ w, IsMinOn (energyFunctional Ω f) univ w → w = u := fun w hw ↦
    IsMinOn.eq_of_strictConvexOn hstrict hw humin (mem_univ _) (mem_univ _)
  have hiff : ∀ w, IsMinOn (energyFunctional Ω f) univ w ↔ ∀ v, formA Ω w w v = f v := fun w ↦ by
    have h := Chapter05.theorem_5_3_19 (V := SobolevEuclideanZero (d + 1) 1 p Ω) (K := univ)
      (f := energyFunctional Ω f) (f' := fun w ↦ energyDeriv hp hp' hΩ f w)
      (fun w _ ↦ (lemma_8_8_4 hp hp' hΩ f w).1) hconv (mem_univ w)
    have h2 := forall_nonneg_sub_iff_forall_eq_zero (V := SobolevEuclideanZero (d + 1) 1 p Ω)
      (energyDeriv hp hp' hΩ f w) w
    refine h.trans ⟨fun H v ↦ ?_, fun H v _ ↦ ?_⟩
    · have := (h2.1 fun v ↦ H v (mem_univ v)) v
      rw [energyDeriv_apply] at this
      exact sub_eq_zero.1 this
    · refine h2.2 (fun v ↦ ?_) v
      rw [energyDeriv_apply]
      exact sub_eq_zero.2 (H v)
  exact ⟨⟨u, humin, huniq⟩, hiff, ⟨u, (hiff u).1 humin, fun w hw ↦ huniq w ((hiff w).2 hw)⟩⟩

end Main

end AtkinsonHan.Chapter08
