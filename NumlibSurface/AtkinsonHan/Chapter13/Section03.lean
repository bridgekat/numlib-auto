/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Fourier.Truncation
import NumlibSurface.AtkinsonHan.Chapter12.Section01

/-!
# Atkinson and Han, Section 13.3: The Fourier–Galerkin method for a first kind equation

This module formalizes the convergence theorem of Section 13.3 of [han2009theoretical]. The boundary
integral equation of the first kind for the interior Dirichlet problem is $(A + B) \varphi = g$ on
$L^2(0, 2\pi)$. Here $A$ is the logarithmic single layer operator, an isomorphism $H^q \to H^{q+1}$
of the periodic Sobolev scale, and $B$ is a smoothing perturbation. The Fourier–Galerkin method
seeks $\varphi_n$ among the trigonometric polynomials of degree at most $n$ with
$P_n (A + B) \varphi_n = P_n g$, where $P_n$ is the $L^2$-orthogonal projection onto them. Since $A$
commutes with $P_n$, applying $A^{-1}$ gives the second kind equation (13.3.13), $$\varphi_n + P_n
A^{-1} B \varphi_n = P_n A^{-1} g.$$ The book says that the convergence proof is "simply a
repetition of the general argument given in Theorem 12.1.2". The module states this argument with
$C = A^{-1} B$, and takes the two facts that the book assumes about $C$ as hypotheses: $C$ is
compact on $L^2$, and $I + C$ is invertible.

The proof is Theorem 12.1.2 and (12.1.24) of `NumlibSurface.AtkinsonHan.Chapter12.Section01` at
$\lambda = 1$ and $K = -C$, with the Fourier truncation of `Numlib.Analysis.Fourier.Truncation`.

## Main results

* (13.3.14), `AtkinsonHan.Chapter13.equation_13_3_14`: for all large $n$, the Galerkin equations
  $\varphi_n + P_n C \varphi_n = P_n f$ are uniquely solvable, the inverses $(I + P_n C)^{-1}$ are
  uniformly bounded, and $\|\varphi - \varphi_n\| \le \|(I + P_n C)^{-1}\| \, \|\varphi - P_n
  \varphi\|$.

## Conventions

* $L^2(0, 2\pi)$ is `Lp ℝ 2 haarAddCircle` on `AddCircle (2 * π)`, whose measure is the normalized
  Haar measure. The normalization scales the norm by a constant and changes nothing in a statement
  about projections and a compact operator.
* The projection $P_n$ is `trigProjCLM (2 * π) n`.

## Deviations from the source

* **(13.3.9)–(13.3.14)** (generalization). The book takes $C = A^{-1} B$ and derives its properties
  from the Sobolev theory. The theorem holds for every compact operator $C$ on $L^2(0, 2\pi)$ with
  $I + C$ invertible. See `AtkinsonHan.Chapter13.equation_13_3_14`.

## Not formalized

* **The solvability theory (13.3.2)–(13.3.7) and the rate (13.3.15).** They need the periodic
  Sobolev scale: $A : H^q \to H^{q+1}$ an isomorphism, $B : H^q \to H^{q+2}$, the compact embedding
  $H^{q+2} \to H^{q+1}$, and the approximation theorem for trigonometric polynomials in $H^q$. They
  would give the two hypotheses of `AtkinsonHan.Chapter13.equation_13_3_14` from the smoothness of
  the kernel of $B$; the book assumes the unique solvability in the same way.
* **The commutation $P_n A = A P_n$.** It follows from the identification of $A$ as a Fourier
  multiplier, (13.2.32), which is `AtkinsonHan.Chapter13.equation_13_2_32`, but it is not stated as
  an operator identity here.
-/

open AddCircle Filter MeasureTheory Topology

open scoped Real

namespace AtkinsonHan.Chapter13

open AtkinsonHan.Chapter12

local notation "L²p" => Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))

/-- **Equation (13.3.14)** of [han2009theoretical], with (13.3.9)–(13.3.13): the Fourier–Galerkin
method for the first kind equation (Section 13.3.1). Let $C$ be a compact operator on
$L^2(0, 2\pi)$ with $I + C$ invertible, and let $P_n$ be the $L^2$-orthogonal projection onto
the trigonometric polynomials of degree at most $n$. Then there is a constant $c$ such that, for
all sufficiently large $n$:

* $I + P_n C$ is invertible with $\|(I + P_n C)^{-1}\| \le c$;
* for every $f$, the Galerkin equation (13.3.13) $\varphi_n + P_n C \varphi_n = P_n f$ has
  exactly one solution $\varphi_n$;
* if $(I + C) \varphi = f$ and $\varphi_n + P_n C \varphi_n = P_n f$, then $$\|\varphi -
  \varphi_n\| \le \|(I + P_n C)^{-1}\| \, \|\varphi - P_n \varphi\|.$$

So the Galerkin error is, up to a constant independent of $n$, the $L^2$ truncation error of the
Fourier series of $\varphi$.

**Generalization.** The book takes $C = A^{-1} B$, with $A$ the logarithmic single layer
operator and $B$ a smoothing operator, and takes the compactness of $C$ and the invertibility of
$I + C$ from its Sobolev theory. The theorem holds for every compact $C$ with $I + C$
invertible.

The invertibility of $I + C$ is an equivalence `e` with `↑e = 1 + C`. The projection $P_n$ is
`trigProjCLM (2 * π) n`. The proof is `AtkinsonHan.Chapter12.theorem_12_1_2` and
`AtkinsonHan.Chapter12.equation_12_1_24` at $\lambda = 1$ and $K = -C$; the Fourier truncation
contributes `norm_trigProjCLM_le_one` and `tendsto_trigProjCLM`, which make
`AtkinsonHan.Chapter12.lemma_12_1_4` applicable. -/
theorem equation_13_3_14 {C : L²p →L[ℝ] L²p} (hC : IsCompactOperator C) (e : L²p ≃L[ℝ] L²p)
    (he : (e : L²p →L[ℝ] L²p) = 1 + C) :
    ∃ c : ℝ, ∀ᶠ n in atTop, ∃ en : L²p ≃L[ℝ] L²p,
      (en : L²p →L[ℝ] L²p) = 1 + trigProjCLM (2 * π) n ∘L C ∧
        ‖(en.symm : L²p →L[ℝ] L²p)‖ ≤ c ∧
        (∀ f : L²p, ∃! φn : L²p,
          (1 + trigProjCLM (2 * π) n ∘L C : L²p →L[ℝ] L²p) φn = trigProjCLM (2 * π) n f) ∧
        ∀ f φ φn : L²p, (1 + C : L²p →L[ℝ] L²p) φ = f →
          (1 + trigProjCLM (2 * π) n ∘L C : L²p →L[ℝ] L²p) φn = trigProjCLM (2 * π) n f →
          ‖φ - φn‖ ≤ ‖(en.symm : L²p →L[ℝ] L²p)‖ * ‖φ - trigProjCLM (2 * π) n φ‖ := by
  set P : ℕ → L²p →L[ℝ] L²p := fun n => trigProjCLM (2 * π) n with hPdef
  have hP : ∀ n, IsIdempotentElem (P n) := fun n => isIdempotentElem_trigProjCLM _ n
  have hKC : ∀ n, ((1 : ℝ) • 1 - P n ∘L (-C) : L²p →L[ℝ] L²p) = 1 + P n ∘L C := by
    intro n
    rw [one_smul, ContinuousLinearMap.comp_neg, sub_neg_eq_add]
  have hK : ((1 : ℝ) • 1 - (-C) : L²p →L[ℝ] L²p) = 1 + C := by rw [one_smul, sub_neg_eq_add]
  have hCneg : IsCompactOperator ⇑(-C) := by
    simpa using hC.neg
  have hconv := lemma_12_1_4 (K := -C) hCneg (P := P) fun x => tendsto_trigProjCLM x
  have hhalf : ∀ᶠ n in atTop,
      ‖(e.symm : L²p →L[ℝ] L²p)‖ * ‖(-C) - P n ∘L (-C)‖ ≤ 1 / 2 := by
    have h0 : Tendsto (fun n => ‖(e.symm : L²p →L[ℝ] L²p)‖ * ‖(-C) - P n ∘L (-C)‖) atTop (𝓝 0) := by
      simpa using hconv.const_mul ‖(e.symm : L²p →L[ℝ] L²p)‖
    exact (h0.eventually_le_const (by norm_num)).mono fun n hn => hn
  refine ⟨2 * ‖(e.symm : L²p →L[ℝ] L²p)‖, ?_⟩
  filter_upwards [hhalf] with n hn
  obtain ⟨e', he'coe, he'norm, he'sol⟩ :=
    theorem_12_1_2 (μ := (1 : ℝ)) one_ne_zero (K := -C) (P := P n) (hP n) e (by rw [hK]; exact he)
      (lt_of_le_of_lt hn (by norm_num))
  have hnn : (0 : ℝ) ≤ ‖(e.symm : L²p →L[ℝ] L²p)‖ * ‖(-C) - P n ∘L (-C)‖ := by positivity
  have hbound : ‖(e'.symm : L²p →L[ℝ] L²p)‖ ≤ 2 * ‖(e.symm : L²p →L[ℝ] L²p)‖ := by
    refine he'norm.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (e.symm : L²p →L[ℝ] L²p)]
  have hsol : ∀ f φn : L²p, IsProjectionSolution (1 : ℝ) (-C) (P n) f φn ↔
      (1 + P n ∘L C : L²p →L[ℝ] L²p) φn = P n f := by
    intro f φn
    rw [isProjectionSolution_iff_smul_sub_comp one_ne_zero (hP n), hKC n]
  refine ⟨e', by rw [he'coe, hKC n], hbound, fun f => ?_, fun f φ φn hφ hφn => ?_⟩
  · simpa only [hsol] using he'sol f
  · have h24 := (equation_12_1_24 (μ := (1 : ℝ)) (K := -C) (P := P n) (hP n)
      (e' := e') (by rw [he'coe]) (f := f) (u := φ) (un := φn)
      (by rw [hK]; exact hφ) ((hsol f φn).mpr hφn)).2
    simpa using h24

end AtkinsonHan.Chapter13
