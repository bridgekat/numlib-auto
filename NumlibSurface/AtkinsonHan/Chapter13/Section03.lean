import Numlib.Analysis.Fourier.Truncation
import NumlibSurface.AtkinsonHan.Chapter12.Section01

/-!
# Atkinson–Han §13.3: the Fourier–Galerkin method for a first kind equation

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §13.3.

The boundary integral equation of the *first* kind for the interior Dirichlet problem is
`(A + B) φ = g` on `L²(0, 2π)`, with `A` the logarithmic single layer operator — an isomorphism
`H^q → H^{q+1}` of the periodic Sobolev scale — and `B` a smoothing perturbation.  The
Fourier–Galerkin method seeks `φ_n` in the trigonometric polynomials of degree at most `n` with
`P_n (A + B) φ_n = P_n g`, where `P_n` is the `L²`-orthogonal projection onto them.  Since `A`
commutes with `P_n`, applying `A⁻¹` turns this into the *second* kind equation (13.3.13)

`φ_n + P_n A⁻¹ B φ_n = P_n A⁻¹ g`,

and the book says of the convergence proof that it is "simply a repetition of the general argument
given in Theorem 12.1.2".  That is what is formalized here, with `C = A⁻¹ B` and the two facts the
book assumes about it — compactness of `C` on `L²` and invertibility of `I + C` — as hypotheses.

## Main results

* `equation_13_3_14` — for all large `n` the Galerkin equations `φ_n + P_n C φ_n = P_n f` are
  uniquely solvable, the inverses `(I + P_n C)⁻¹` are uniformly bounded, and
  `‖φ - φ_n‖ ≤ ‖(I + P_n C)⁻¹‖ ‖φ - P_n φ‖`.

## Not formalized here

* The solvability theory (13.3.2)–(13.3.7) and the rate (13.3.15), which need the periodic Sobolev
  scale: `A : H^q → H^{q+1}` an isomorphism, `B : H^q → H^{q+2}`, the compact embedding
  `H^{q+2} → H^{q+1}` and the approximation theorem for trigonometric polynomials in `H^q`.  They
  are what would *supply* the two hypotheses of `equation_13_3_14` from smoothness of the kernel of
  `B`; the book assumes unique solvability in exactly the same way.
* The identification of `A` as a Fourier multiplier, (13.2.32); it lives in
  `Chapter13/Section02`'s group and is what makes `P_n A = A P_n` a theorem rather than a step of
  the derivation.

## Conventions

`L²(0, 2π)` is `Lp ℝ 2 haarAddCircle` on `AddCircle (2π)`, whose measure is the *normalized* Haar
measure; the normalization scales the norm by a constant and changes nothing in a statement about
projections and a compact operator.  The book's projection `P_n` is `trigProjCLM (2π) n` of
`Numlib/Analysis/Fourier/Truncation`, and the equations are written as the general projection
method `AtkinsonHan.Chapter12.IsProjectionSolution` at `λ = 1` and `K = -C`, which is (13.3.13).
-/

open AddCircle Filter MeasureTheory Topology

open scoped Real

namespace AtkinsonHan.Chapter13

open AtkinsonHan.Chapter12

local notation "L²p" => Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))

/-- **§13.3.1, (13.3.9)–(13.3.14): the Fourier–Galerkin method for the first kind equation.**
Let `C = A⁻¹ B` be a compact operator on `L²(0, 2π)` with `I + C` invertible — the two facts the
book takes from its Sobolev space theory — and let `P_n` be the `L²`-orthogonal projection onto the
trigonometric polynomials of degree at most `n`.  Then there is a constant `c` such that, for all
large `n`,

* `I + P_n C` is invertible with `‖(I + P_n C)⁻¹‖ ≤ c`, so the Galerkin equations (13.3.13)
  `φ_n + P_n C φ_n = P_n f` have exactly one solution for every right-hand side; and
* the solution of `(I + C) φ = f` satisfies `‖φ - φ_n‖ ≤ ‖(I + P_n C)⁻¹‖ ‖φ - P_n φ‖`,

so the Galerkin error is the `L²` truncation error of the Fourier series of `φ`, up to a constant
independent of `n`.

Everything is `theorem_12_1_2` and `equation_12_1_24` at `λ = 1` and `K = -C`: what the Fourier
truncation contributes is `norm_trigProjCLM_le_one` and `tendsto_trigProjCLM`, which make
`lemma_12_1_4` applicable. -/
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
