import Mathlib.Analysis.Complex.ExponentialBounds
import Numlib.Approximation.CompositeQuadrature
import Numlib.IntegralEquations.Nystrom
import Numlib.IntegralEquations.SecondKind
import NumlibSurface.AtkinsonHan.Chapter02.Section03

/-!
# Atkinson–Han §12.4: the Nyström method and collectively compact approximation

Surface file for Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
Analysis Framework*, 3rd edition, Springer, 2009, §12.4.

The section has an abstract half, §12.4.3, and a concrete half: the perturbation theorem whose
hypothesis constrains `(T - S) S` rather than `T - S`, the assumptions A1–A3 and Lemma 12.4.7 on
the one side, and on the other the Nyström operators of a quadrature rule, for which those
assumptions are verified.  Both are formalized here.  The abstract half is the framework which
makes the Nyström method analysable, and which §12.5 reuses for product integration.

## Main results

* `theorem_12_4_3` — Anselone's perturbation theorem, with the inverse bound (12.4.23) and the
  error bound (12.4.24).
* `IsCollectivelyCompactFamily` — assumptions A1–A3, with
  `IsCollectivelyCompactFamily.isCollectivelyCompact` and
  `isCollectivelyCompactFamily_of_isCollectivelyCompact` identifying the book's condition (12.4.53)
  on the closed unit ball with the backbone `IsCollectivelyCompact`, which quantifies over some
  neighbourhood of the origin instead.
* `lemma_12_4_7_a`–`lemma_12_4_7_d` — the four clauses of Lemma 12.4.7.
* `exists_norm_inverse_le_of_isCollectivelyCompactFamily` — the abstract half of Theorem 12.4.4:
  for large `n` the approximate equations are uniquely solvable, the inverses are uniformly
  bounded, and the error is controlled by the consistency error `‖(K - K_n) u‖` at the exact
  solution.
* `isCollectivelyCompactFamily_nystromCLM` — the Nyström operators of a sequence of convergent
  quadrature rules with uniformly bounded absolute weight sums satisfy A1–A3.
* `lemma_12_4_2_a`–`lemma_12_4_2_c` — the three clauses of Lemma 12.4.2: the identities
  (12.4.14)–(12.4.15) expressing `(K - K_n) K` and `(K - K_n) K_n` through the single kernel `e_n`,
  the norm formulas (12.4.16)–(12.4.17), and (12.4.18), that both norms tend to zero.
* `theorem_12_4_4` — the Nyström instance of the abstract theorem.
* `example_12_4_5` — the composite trapezoidal rule error `-h² (b - a) g''(ξ) / 12`, an instance
  of `Quadrature.sub_composite_trapezoid_eq` in `Numlib/Approximation/CompositeQuadrature`.
* `equation_12_4_39` — its asymptotic form `-(h²/12) [g'(b) - g'(a)] + O(h⁴)`, the first
  Euler–Maclaurin term, with the explicit remainder `(b - a) h⁴ ‖g⁗‖_∞ / 720`.  The book quotes
  this one from the literature; it is `Quadrature.abs_sub_trapezoidSum_add_le`.
* `equation_12_4_44` — the same expansion for the Nyström *consistency error*, uniformly in the row
  variable: `‖(K - K_n) u - h² d‖_∞ ≤ (b - a) h⁴ M₄ / 720`.  The hypotheses on the row integrands
  `y ↦ k (t, y) u (y)` are carried as a family `G t` of `C⁴` functions with a bound on the fourth
  derivatives that does not depend on `t`, which is what makes the estimate uniform.
* `example_12_4_6` — the asymptotic error expansion `u - u_n = h² γ + O(h⁴)` of the Nyström
  solution, with `γ` the solution of the book's auxiliary integral equation, in the two forms
  described in its doc comment.
* `expKernel`, `norm_fredholm_expKernel` and `example_12_4_1` — the equation (12.4.7) the section
  computes with, `2 u(x) - ∫₀¹ e^{x y} u(y) dy = f(x)`: its operator has norm exactly `e - 1`, and
  since `e - 1 < 2` the equation is uniquely solvable for every `f ∈ C[0, 1]`, which is the one
  claim of Example 12.4.1 that is not a measured number.

## Not formalized here

The numerical half of Example 12.4.1: the nodal errors (12.4.8) and (12.4.9) of the three-point
Simpson and three-point Gauss–Legendre rules, the comparison of Nyström interpolation with
quadratic interpolation off the nodes, and Figure 12.1.  They are computed floating-point numbers,
not statements; only the unique solvability the example opens with is stated, as
`example_12_4_1`.

Nothing else of §12.4 except the *unconditional* form of the last clause of Example 12.4.6.  The
book's "by a similar argument, `r_n = O(h⁴)`" needs `‖(K - K_n) γ‖ = O(h²)`, hence the smoothness
of the solution `γ` of the auxiliary equation, hence differentiation under the integral sign; here
that bound is a hypothesis of the clause that needs it, and everything else is proved.

## Conventions

As in §12.1 the book's scalar `λ` is written `μ`, `λ` being Lean's lambda binder; the measure of
the concrete half is therefore written `ν`.  The book's domain is a closed bounded `D` in `ℝ^m`
with Lebesgue measure, and the statements below are for a compact space with a finite Borel
measure, the generality at which the backbone `IntegralOperator.kernelCLM` and
`IntegralOperator.nystromCLM` are written; the book's case is `IntegralOperator.regionMeasure D`.
The book's family is `K_n` with limit `K`; here the family is `K : ℕ → X →L[𝕜] X` and its limit is
`L`, so that the family is named once and indexed.  Doc comments below quote the book's `K` and
`K_n`, which are this file's `L` and `K n`.
-/

open Filter Topology

namespace AtkinsonHan.Chapter12

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-! ### Anselone's perturbation theorem -/

/-- **Theorem 12.4.3**: let `S` and `T` be bounded operators on a Banach space with `S` compact,
let `λ ≠ 0` be such that `λ - T` is invertible, and assume (12.4.22),

`‖(λ - T)⁻¹‖ ‖(T - S) S‖ < |λ|`.

Then `λ - S` is invertible with the bound (12.4.23),

`‖(λ - S)⁻¹‖ ≤ (1 + ‖(λ - T)⁻¹‖ ‖S‖) / (|λ| - ‖(λ - T)⁻¹‖ ‖(T - S) S‖)`,

and the solutions of `(λ - T) u = f` and `(λ - S) z = f` satisfy (12.4.24),
`‖u - z‖ ≤ ‖(λ - S)⁻¹‖ ‖T u - S u‖`.

The book prints (12.4.22) as `‖(T - S) S‖ < |λ| / ‖(λ - T)⁻¹‖`; the equivalent product form is
used here, since it divides by nothing.  The hypothesis is on `(T - S) S` and not on `T - S`,
which is exactly why the theorem applies to quadrature approximations of an integral operator,
where `‖T - S‖` does not tend to zero. -/
theorem theorem_12_4_3 [CompleteSpace X] {μ : 𝕜} (hμ : μ ≠ 0) {S T : X →L[𝕜] X}
    (hS : IsCompactOperator S) {e : X ≃L[𝕜] X} (he : (e : X →L[𝕜] X) = μ • 1 - T)
    (h : ‖(e.symm : X →L[𝕜] X)‖ * ‖(T - S) ∘L S‖ < ‖μ‖) :
    ∃ e' : X ≃L[𝕜] X, (e' : X →L[𝕜] X) = μ • 1 - S ∧
      ‖(e'.symm : X →L[𝕜] X)‖ ≤ (1 + ‖(e.symm : X →L[𝕜] X)‖ * ‖S‖) /
        (‖μ‖ - ‖(e.symm : X →L[𝕜] X)‖ * ‖(T - S) ∘L S‖) ∧
      ∀ f u z : X, (μ • 1 - T : X →L[𝕜] X) u = f → (μ • 1 - S : X →L[𝕜] X) z = f →
        ‖u - z‖ ≤ ‖(e'.symm : X →L[𝕜] X)‖ * ‖T u - S u‖ := by
  obtain ⟨e', he'coe, he'norm⟩ := SecondKind.exists_equiv_of_isCompactOperator hμ hS he h
  exact ⟨e', he'coe, he'norm, fun _ _ _ hu hz => SecondKind.norm_sub_le he'coe hu hz⟩

/-! ### The assumptions A1–A3 -/

/-- **Assumptions A1–A3 of §12.4.3**: on a Banach space, `K` and the `K_n` are bounded linear
operators (A1), `K_n u → K u` for every `u` (A2), and the set `{K_n v : n ≥ 1, ‖v‖ ≤ 1}` of
(12.4.53) has compact closure (A3) — a *collectively compact family of pointwise convergent
operators*.

Boundedness is carried by the type `X →L[𝕜] X`, so A1 needs no field.  The backbone
`IsCollectivelyCompact` states A3 for *some* neighbourhood of the origin rather than for the
closed unit ball; the two agree, by `IsCollectivelyCompactFamily.isCollectivelyCompact` and
`isCollectivelyCompactFamily_of_isCollectivelyCompact`. -/
structure IsCollectivelyCompactFamily (K : ℕ → X →L[𝕜] X) (L : X →L[𝕜] X) : Prop where
  /-- A2: the family converges pointwise to `L`. -/
  tendsto : ∀ x, Tendsto (fun n => K n x) atTop (𝓝 (L x))
  /-- A3, the book's (12.4.53): the union of the images of the closed unit ball is relatively
  compact. -/
  isCompact_closure : IsCompact (closure (⋃ n, K n '' Metric.closedBall 0 1))

/-- A3 in the book's form implies the backbone's, since the closed unit ball is a neighbourhood of
the origin. -/
theorem IsCollectivelyCompactFamily.isCollectivelyCompact {K : ℕ → X →L[𝕜] X} {L : X →L[𝕜] X}
    (h : IsCollectivelyCompactFamily K L) : IsCollectivelyCompact K :=
  ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos, h.isCompact_closure⟩

/-- The converse identification: a pointwise convergent family that is collectively compact in the
backbone's sense satisfies the book's A1–A3.  A neighbourhood of the origin contains a ball of
some radius `r`, and scaling by `r / 2` carries the closed unit ball into it, so the two unions of
images differ by a homeomorphism of the space. -/
theorem isCollectivelyCompactFamily_of_isCollectivelyCompact {K : ℕ → X →L[𝕜] X} {L : X →L[𝕜] X}
    (hK : IsCollectivelyCompact K) (hL : ∀ x, Tendsto (fun n => K n x) atTop (𝓝 (L x))) :
    IsCollectivelyCompactFamily K L := by
  obtain ⟨U, hU, hcpt⟩ := hK
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨hL, ?_⟩
  obtain ⟨c, hcnorm⟩ : ∃ c : 𝕜, ‖c‖ = r / 2 :=
    ⟨((r / 2 : ℝ) : 𝕜), by rw [RCLike.norm_ofReal, abs_of_pos (by linarith)]⟩
  have hc0 : c ≠ 0 := by
    rw [← norm_ne_zero_iff, hcnorm]
    exact ne_of_gt (by linarith)
  have hsub : closure (⋃ n, K n '' Metric.closedBall (0 : X) 1) ⊆
      (fun y : X => c⁻¹ • y) '' closure (⋃ i, K i '' U) := by
    refine closure_minimal ?_ ((hcpt.image (continuous_const_smul c⁻¹)).isClosed)
    rintro z hz
    obtain ⟨n, hzn⟩ := Set.mem_iUnion.1 hz
    obtain ⟨x, hx, rfl⟩ := hzn
    have hxU : c • x ∈ U := by
      refine hrU (mem_ball_zero_iff.2 ?_)
      rw [norm_smul, hcnorm]
      calc r / 2 * ‖x‖ ≤ r / 2 * 1 :=
            mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hx) (by linarith)
        _ < r := by linarith
    refine ⟨K n (c • x), subset_closure (Set.mem_iUnion.2 ⟨n, ⟨c • x, hxU, rfl⟩⟩), ?_⟩
    simp only [map_smul, inv_smul_smul₀ hc0]
  exact (hcpt.image (continuous_const_smul c⁻¹)).of_isClosed_subset isClosed_closure hsub

/-! ### Lemma 12.4.7 -/

variable {K : ℕ → X →L[𝕜] X} {L : X →L[𝕜] X}

/-- **Lemma 12.4.7 (1)**: the pointwise limit of a collectively compact family is compact. -/
theorem lemma_12_4_7_a (h : IsCollectivelyCompactFamily K L) : IsCompactOperator L :=
  IsCollectivelyCompact.isCompactOperator_of_tendsto h.isCollectivelyCompact h.tendsto

/-- **Lemma 12.4.7 (2)**: a collectively compact family is uniformly bounded in operator norm. -/
theorem lemma_12_4_7_b (h : IsCollectivelyCompactFamily K L) : ∃ C, ∀ n, ‖K n‖ ≤ C :=
  IsCollectivelyCompact.exists_opNorm_le h.isCollectivelyCompact

/-- **Lemma 12.4.7 (3)**: `‖(K - K_n) M‖ → 0` for every compact operator `M`.  Only the pointwise
convergence A2 is used; the estimate holds for a compact `M` into the space, of whatever
domain. -/
theorem lemma_12_4_7_c [CompleteSpace X] {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    (h : IsCollectivelyCompactFamily K L) {M : U →L[𝕜] X} (hM : IsCompactOperator M) :
    Tendsto (fun n => ‖(L - K n) ∘L M‖) atTop (𝓝 0) := by
  refine tendsto_opNorm_comp_of_isCompactOperator (fun x => ?_) hM
  have hx : Tendsto (fun n => L x - K n x) atTop (𝓝 (L x - L x)) :=
    tendsto_const_nhds.sub (h.tendsto x)
  rw [sub_self] at hx
  simpa using hx

/-- **Lemma 12.4.7 (4)**: `‖(K - K_n) K_n‖ → 0`, although `‖K - K_n‖` need not tend to zero at all.
This is the hypothesis (12.4.22) of Theorem 12.4.3 for all large `n`, and it is the whole point of
the collectively compact framework. -/
theorem lemma_12_4_7_d [CompleteSpace X] (h : IsCollectivelyCompactFamily K L) :
    Tendsto (fun n => ‖(L - K n) ∘L K n‖) atTop (𝓝 0) :=
  IsCollectivelyCompact.tendsto_opNorm_sub_comp h.isCollectivelyCompact h.tendsto

/-! ### The convergence of the approximate equations -/

/-- **The abstract half of Theorem 12.4.4**: for a collectively compact, pointwise convergent
family `K_n` on a Banach space and `λ ≠ 0` with `λ - K` invertible, there is a constant `c` such
that for all large `n` the operator `λ - K_n` is invertible with `‖(λ - K_n)⁻¹‖ ≤ c` (12.4.32),
and the solutions of `(λ - K) u = f` and `(λ - K_n) u_n = f` satisfy

`‖u - u_n‖ ≤ c ‖(K - K_n) u‖`,

the consistency error at the *exact* solution.  The book states this for the Nyström operators on
`C(D)`; every step of its proof is Lemma 12.4.7 followed by Theorem 12.4.3, so the abstract
statement is the one worth having.

The constant is `c = 2 (1 + ‖(λ - K)⁻¹‖ C) / |λ|` with `C` the uniform bound of
`lemma_12_4_7_b`. -/
theorem exists_norm_inverse_le_of_isCollectivelyCompactFamily [CompleteSpace X] {μ : 𝕜}
    (hμ : μ ≠ 0) (h : IsCollectivelyCompactFamily K L) {e : X ≃L[𝕜] X}
    (he : (e : X →L[𝕜] X) = μ • 1 - L) :
    ∃ c : ℝ, ∀ᶠ n in atTop, ∃ en : X ≃L[𝕜] X, (en : X →L[𝕜] X) = μ • 1 - K n ∧
      ‖(en.symm : X →L[𝕜] X)‖ ≤ c ∧
      ∀ f u un : X, (μ • 1 - L : X →L[𝕜] X) u = f → (μ • 1 - K n : X →L[𝕜] X) un = f →
        ‖u - un‖ ≤ c * ‖L u - K n u‖ := by
  have hμpos : (0 : ℝ) < ‖μ‖ := norm_pos_iff.2 hμ
  obtain ⟨C, hC⟩ := lemma_12_4_7_b h
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hA0 : (0 : ℝ) ≤ ‖(e.symm : X →L[𝕜] X)‖ := norm_nonneg _
  refine ⟨(1 + ‖(e.symm : X →L[𝕜] X)‖ * C) / (‖μ‖ / 2), ?_⟩
  have hsmall : ∀ᶠ n in atTop,
      ‖(e.symm : X →L[𝕜] X)‖ * ‖(L - K n) ∘L K n‖ < ‖μ‖ / 2 := by
    have h0 : Tendsto (fun n => ‖(e.symm : X →L[𝕜] X)‖ * ‖(L - K n) ∘L K n‖) atTop (𝓝 0) := by
      simpa using (lemma_12_4_7_d h).const_mul ‖(e.symm : X →L[𝕜] X)‖
    exact h0.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hsmall] with n hn
  obtain ⟨en, hencoe, hennorm, herr⟩ :=
    theorem_12_4_3 hμ (IsCollectivelyCompact.isCompactOperator h.isCollectivelyCompact n) he
      (by linarith)
  have hbound : ‖(en.symm : X →L[𝕜] X)‖ ≤
      (1 + ‖(e.symm : X →L[𝕜] X)‖ * C) / (‖μ‖ / 2) := by
    refine hennorm.trans ?_
    have hnum : 1 + ‖(e.symm : X →L[𝕜] X)‖ * ‖K n‖ ≤ 1 + ‖(e.symm : X →L[𝕜] X)‖ * C := by
      linarith [mul_le_mul_of_nonneg_left (hC n) hA0]
    have hnum0 : (0 : ℝ) ≤ 1 + ‖(e.symm : X →L[𝕜] X)‖ * C := by
      linarith [mul_nonneg hA0 hC0]
    have hden : ‖μ‖ / 2 ≤ ‖μ‖ - ‖(e.symm : X →L[𝕜] X)‖ * ‖(L - K n) ∘L K n‖ := by linarith
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    calc (1 + ‖(e.symm : X →L[𝕜] X)‖ * ‖K n‖) * (‖μ‖ / 2)
        ≤ (1 + ‖(e.symm : X →L[𝕜] X)‖ * C) * (‖μ‖ / 2) :=
          mul_le_mul_of_nonneg_right hnum (by linarith)
      _ ≤ (1 + ‖(e.symm : X →L[𝕜] X)‖ * C) *
            (‖μ‖ - ‖(e.symm : X →L[𝕜] X)‖ * ‖(L - K n) ∘L K n‖) :=
          mul_le_mul_of_nonneg_left hden hnum0
  exact ⟨en, hencoe, hbound, fun f u un hu hun =>
    (herr f u un hu hun).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))⟩

/-! ### The Nyström operators -/

section Nystrom

open IntegralOperator MeasureTheory

variable {D : Type*} [TopologicalSpace D] [CompactSpace D] [MeasurableSpace D] [BorelSpace D]
  (ν : Measure D) [IsFiniteMeasure ν]

/-- **The Nyström family satisfies A1–A3.**  With `K u (t) = ∫ k (t, s) u (s) dν` the integral
operator of a continuous kernel and

`K_n u (t) = Σ_j w_{n,j} k (t, x_{n,j}) u (x_{n,j})`

the Nyström operators (12.4.4) of a sequence of quadrature rules, the family `{K_n}` converges to
`K` pointwise on `C(D)` and is collectively compact, as soon as the rules converge at every
continuous integrand and their absolute weight sums are bounded — the book's (12.4.3).

This is the missing instance of the framework: A2 is
`IntegralOperator.tendsto_nystromCLM` and A3 is
`IntegralOperator.isCollectivelyCompact_nystromCLM`, both proved from the uniform convergence of
the rules on the compact set of row integrands. -/
theorem isCollectivelyCompactFamily_nystromCLM (k : C(D × D, ℝ)) {m : ℕ → ℕ}
    {w : ∀ n, Fin (m n) → ℝ} {x : ∀ n, Fin (m n) → D} {W : ℝ} (hW : ∀ n, ∑ j, |w n j| ≤ W)
    (hQ : ∀ v : C(D, ℝ), Tendsto (fun n => Quadrature.functional (w n) (x n) v) atTop
      (𝓝 (integralCLM ν v))) :
    IsCollectivelyCompactFamily (fun n => nystromCLM (w n) (x n) k) (kernelCLM ν k) :=
  isCollectivelyCompactFamily_of_isCollectivelyCompact
    (isCollectivelyCompact_nystromCLM k hW) fun u => tendsto_nystromCLM ν hQ u

/-- **Lemma 12.4.2, first clause.**  With

`e_n (t, s) = ∫ k (t, v) k (v, s) dν - Σ_j w_j k (t, x_j) k (x_j, s)`

the quadrature error of the composed kernel, `(K - K_n) K` is the integral operator of `e_n`
(12.4.14), and hence its norm is the largest row integral of `e_n` (12.4.16). -/
theorem lemma_12_4_2_a [SecondCountableTopology D] [Nonempty D] {m : ℕ} (w : Fin m → ℝ)
    (x : Fin m → D) (k : C(D × D, ℝ)) :
    (kernelCLM ν k - nystromCLM w x k) ∘L kernelCLM ν k = kernelCLM ν (compKernel ν w x k) ∧
      ‖(kernelCLM ν k - nystromCLM w x k) ∘L kernelCLM ν k‖
        = ⨆ t, ∫ s, |compKernel ν w x k (t, s)| ∂ν := by
  refine ⟨kernelCLM_sub_nystromCLM_comp_kernelCLM ν w x k, ?_⟩
  rw [kernelCLM_sub_nystromCLM_comp_kernelCLM ν w x k, norm_kernelCLM]

/-- **Lemma 12.4.2, second clause.**  `(K - K_n) K_n` is the *Nyström* operator of the same kernel
`e_n` (12.4.15), and hence its norm is the largest absolute weight sum of `e_n` (12.4.17). -/
theorem lemma_12_4_2_b [T2Space D] [Nonempty D] {m : ℕ} {w : Fin m → ℝ} {x : Fin m → D}
    (hx : Function.Injective x) (k : C(D × D, ℝ)) :
    (kernelCLM ν k - nystromCLM w x k) ∘L nystromCLM w x k
        = nystromCLM w x (compKernel ν w x k) ∧
      ‖(kernelCLM ν k - nystromCLM w x k) ∘L nystromCLM w x k‖
        = ⨆ t, ∑ j, |w j * compKernel ν w x k (t, x j)| := by
  refine ⟨kernelCLM_sub_nystromCLM_comp_nystromCLM ν w x k, ?_⟩
  rw [kernelCLM_sub_nystromCLM_comp_nystromCLM ν w x k, norm_nystromCLM hx]

/-- **Lemma 12.4.2, third clause (12.4.18)**: for a convergent quadrature rule the composed
quadrature error tends to zero uniformly, `max_{t,s} |e_n (t, s)| → 0`, and therefore so do both
operator norms — which is hypothesis (12.4.22) of Theorem 12.4.3 for all large `n`.

The two bounds are `‖(K - K_n) K‖ ≤ ν(D) ‖e_n‖` and `‖(K - K_n) K_n‖ ≤ W ‖e_n‖`, read off the
identities of the two clauses above. -/
theorem lemma_12_4_2_c [SecondCountableTopology D] {m : ℕ → ℕ} {w : ∀ n, Fin (m n) → ℝ}
    {x : ∀ n, Fin (m n) → D} (k : C(D × D, ℝ)) {W : ℝ} (hW : ∀ n, ∑ j, |w n j| ≤ W)
    (hQ : ∀ v : C(D, ℝ), Tendsto (fun n => Quadrature.functional (w n) (x n) v) atTop
      (𝓝 (integralCLM ν v))) :
    Tendsto (fun n => ‖(kernelCLM ν k - nystromCLM (w n) (x n) k) ∘L kernelCLM ν k‖)
        atTop (𝓝 0) ∧
      Tendsto (fun n => ‖(kernelCLM ν k - nystromCLM (w n) (x n) k) ∘L
        nystromCLM (w n) (x n) k‖) atTop (𝓝 0) := by
  have hW0 : (0 : ℝ) ≤ W := le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hW 0)
  have he := tendsto_norm_compKernel ν k hQ
  constructor
  · refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using he.const_mul (ν.real Set.univ))
    rw [kernelCLM_sub_nystromCLM_comp_kernelCLM ν (w n) (x n) k]
    refine norm_kernelCLM_le ν (by positivity) fun t => ?_
    have hint : (∫ s, |compKernel ν (w n) (x n) k (t, s)| ∂ν)
        ≤ ∫ _s : D, ‖compKernel ν (w n) (x n) k‖ ∂ν :=
      integral_mono (integrable_kernel_row ν _ t).abs (integrable_const _) fun s => by
        simpa using (compKernel ν (w n) (x n) k).norm_coe_le_norm (t, s)
    rwa [integral_const, smul_eq_mul] at hint
  · refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using he.const_mul W)
    rw [kernelCLM_sub_nystromCLM_comp_nystromCLM ν (w n) (x n) k]
    refine norm_nystromCLM_le (by positivity) fun t => ?_
    calc ∑ j, |w n j * compKernel ν (w n) (x n) k (t, x n j)|
        ≤ ∑ j, |w n j| * ‖compKernel ν (w n) (x n) k‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (by simpa using (compKernel ν (w n) (x n) k).norm_coe_le_norm (t, x n j))
            (abs_nonneg _)
      _ = (∑ j, |w n j|) * ‖compKernel ν (w n) (x n) k‖ := by rw [Finset.sum_mul]
      _ ≤ W * ‖compKernel ν (w n) (x n) k‖ :=
          mul_le_mul_of_nonneg_right (hW n) (norm_nonneg _)

/-- **Theorem 12.4.4**: let `k` be a continuous kernel on a compact `D` carrying a finite Borel
measure, let the quadrature rules converge at every continuous integrand with uniformly bounded
absolute weight sums, and let `λ ≠ 0` be such that `λ - K` is invertible on `C(D)`.  Then there is
a constant `c` such that, for all large `n`, `λ - K_n` is invertible with `‖(λ - K_n)⁻¹‖ ≤ c`
(12.4.32) — so the Nyström equations are uniquely solvable — and

`‖u - u_n‖_∞ ≤ c ‖K u - K_n u‖_∞`,

the consistency error of the quadrature rule at the *exact* solution.

Every step is `exists_norm_inverse_le_of_isCollectivelyCompactFamily` applied to
`isCollectivelyCompactFamily_nystromCLM`; the book's bound (12.4.23) is inside
`theorem_12_4_3`. -/
theorem theorem_12_4_4 {μ : ℝ} (hμ : μ ≠ 0) (k : C(D × D, ℝ)) {m : ℕ → ℕ}
    {w : ∀ n, Fin (m n) → ℝ} {x : ∀ n, Fin (m n) → D} {W : ℝ} (hW : ∀ n, ∑ j, |w n j| ≤ W)
    (hQ : ∀ v : C(D, ℝ), Tendsto (fun n => Quadrature.functional (w n) (x n) v) atTop
      (𝓝 (integralCLM ν v)))
    {e : C(D, ℝ) ≃L[ℝ] C(D, ℝ)}
    (he : (e : C(D, ℝ) →L[ℝ] C(D, ℝ)) = μ • 1 - kernelCLM ν k) :
    ∃ c : ℝ, ∀ᶠ n in atTop, ∃ en : C(D, ℝ) ≃L[ℝ] C(D, ℝ),
      (en : C(D, ℝ) →L[ℝ] C(D, ℝ)) = μ • 1 - nystromCLM (w n) (x n) k ∧
      ‖(en.symm : C(D, ℝ) →L[ℝ] C(D, ℝ))‖ ≤ c ∧
      ∀ f u un : C(D, ℝ), (μ • 1 - kernelCLM ν k : C(D, ℝ) →L[ℝ] C(D, ℝ)) u = f →
        (μ • 1 - nystromCLM (w n) (x n) k : C(D, ℝ) →L[ℝ] C(D, ℝ)) un = f →
        ‖u - un‖ ≤ c * ‖kernelCLM ν k u - nystromCLM (w n) (x n) k u‖ :=
  exists_norm_inverse_le_of_isCollectivelyCompactFamily hμ
    (isCollectivelyCompactFamily_nystromCLM ν k hW hQ) he

end Nystrom

/-! ### Example 12.4.1: the equation the section computes with -/

section Example

open IntegralOperator MeasureTheory Set

/-- **The kernel `e^{x y}` on `[0, 1]²`**, the kernel of (12.4.7) — and, on `[0, b]`, of the
equations (12.2.8) and (12.3.18) that Examples 12.2.1 and 12.3.2 compute with as well.  It is the
book's standard test kernel for the whole chapter: smooth, positive, and of moderate size. -/
noncomputable def expKernel : C(Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun p => Real.exp ((p.1 : ℝ) * (p.2 : ℝ)), by fun_prop⟩

/-- The row integrals of `expKernel` are `∫₀¹ e^{x y} dy`: the kernel is positive, so the absolute
value does nothing, and on `[0, 1]` the projection `projIcc` is the identity. -/
theorem row_expKernel (x : Icc (0 : ℝ) 1) :
    ∫ y in (0 : ℝ)..1, |expKernel (x, projIcc 0 1 zero_le_one y)|
      = ∫ y in (0 : ℝ)..1, Real.exp ((x : ℝ) * y) := by
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le zero_le_one] at hy
  rw [expKernel]
  simp [projIcc_of_mem zero_le_one hy]

/-- The largest row integral of `e^{x y}` over `x ∈ [0, 1]` is `e - 1`, attained at `x = 1`: for
`0 ≤ x ≤ 1` and `0 ≤ y ≤ 1` one has `x y ≤ y`, so every row integral is at most `∫₀¹ e^y = e - 1`,
with equality in the last row. -/
theorem isGreatest_row_expKernel :
    IsGreatest (Set.range fun x : Icc (0 : ℝ) 1 => ∫ y in (0 : ℝ)..1, Real.exp ((x : ℝ) * y))
      (Real.exp 1 - 1) := by
  constructor
  · refine ⟨⟨1, by norm_num⟩, ?_⟩
    norm_num [integral_exp]
  · rintro _ ⟨x, rfl⟩
    have hx := x.2
    calc ∫ y in (0 : ℝ)..1, Real.exp ((x : ℝ) * y)
        ≤ ∫ y in (0 : ℝ)..1, Real.exp y := by
          refine intervalIntegral.integral_mono_on zero_le_one
            ((by fun_prop : Continuous fun y : ℝ => Real.exp ((x : ℝ) * y)).intervalIntegrable 0 1)
            (Real.continuous_exp.intervalIntegrable 0 1) fun y hy => ?_
          exact Real.exp_le_exp.2 (by nlinarith [hx.1, hx.2, hy.1, hy.2])
      _ = Real.exp 1 - 1 := by simp [integral_exp]

/-- **`‖K‖ = e − 1`** for the integral operator of (12.4.7), which is the number the book quotes as
`≐ 1.72`.  This is (2.2.8), the operator-norm formula for a kernel operator on `C[a, b]`, at
`isGreatest_row_expKernel`. -/
theorem norm_fredholm_expKernel :
    ‖fredholm zero_le_one expKernel‖ = Real.exp 1 - 1 := by
  have hne : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩
  rw [norm_fredholm zero_le_one expKernel]
  simp only [row_expKernel]
  exact isGreatest_row_expKernel.isLUB.ciSup_eq

/-- **Example 12.4.1**, the opening claim.  For the equation (12.4.7),

`2 u(x) - ∫₀¹ e^{y x} u(y) dy = f(x)`,  `0 ≤ x ≤ 1`,

the operator norm is `‖K‖ = e - 1 ≐ 1.72`, so `‖K‖ < |λ| = 2` and the geometric series theorem
makes the equation uniquely solvable for every `f ∈ C[0, 1]`, with
`‖(2 - K)⁻¹‖ ≤ 1 / (2 - (e - 1))` and `‖u‖ ≤ ‖f‖ / (2 - (e - 1))`.  That is the book's own reason
for choosing `λ = 2`, and it is Example 2.3.2 of §2.3 read at this kernel,
`AtkinsonHan.Chapter02.example_2_3_2_integral`.

The rest of Example 12.4.1 is arithmetic: the nodal errors (12.4.8) and (12.4.9) of the
three-point Simpson and three-point Gauss–Legendre rules, and the comparison of the Nyström
interpolation formula (12.4.6) with quadratic interpolation away from the nodes.  Those are
measured floating-point numbers and are not stated; the general statement they illustrate is
`theorem_12_4_4`. -/
theorem example_12_4_1 :
    ‖fredholm zero_le_one expKernel‖ = Real.exp 1 - 1 ∧
      ∃ e : C(Icc (0 : ℝ) 1, ℝ) ≃L[ℝ] C(Icc (0 : ℝ) 1, ℝ),
        (e : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] C(Icc (0 : ℝ) 1, ℝ))
            = (2 : ℝ) • (1 : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] C(Icc (0 : ℝ) 1, ℝ))
              - fredholm zero_le_one expKernel ∧
          ‖(e.symm : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] C(Icc (0 : ℝ) 1, ℝ))‖
            ≤ 1 / (2 - (Real.exp 1 - 1)) ∧
          ∀ u f : C(Icc (0 : ℝ) 1, ℝ),
            (2 : ℝ) • u - fredholm zero_le_one expKernel u = f →
              ‖u‖ ≤ ‖f‖ / (2 - (Real.exp 1 - 1)) := by
  have hsup : (⨆ x, ∫ y in (0 : ℝ)..1, |expKernel (x, projIcc 0 1 zero_le_one y)|)
      = Real.exp 1 - 1 := by
    have hne : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩
    simp only [row_expKernel]
    exact isGreatest_row_expKernel.isLUB.ciSup_eq
  have hlt : (⨆ x, ∫ y in (0 : ℝ)..1, |expKernel (x, projIcc 0 1 zero_le_one y)|)
      < |(2 : ℝ)| := by
    rw [hsup, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := Real.exp_one_lt_d9
    linarith
  obtain ⟨e, he, hb, hu⟩ := Chapter02.example_2_3_2_integral zero_le_one expKernel hlt
  rw [hsup, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hb hu
  exact ⟨norm_fredholm_expKernel, e, he, hb, hu⟩

end Example

/-! ### The composite trapezoidal rule -/

/-- **Example 12.4.5, the composite trapezoidal rule error.**  For `g` of class `C²` on `[a, b]`,
the uniform mesh `x_j = a + j h` with `h = (b - a)/N` and the composite trapezoidal rule,

`∫_a^b g - h [g(x_0)/2 + g(x_1) + ⋯ + g(x_{N-1}) + g(x_N)/2] = -h² (b - a) g''(ξ)/12`

for some `ξ` in `[a, b]`.  This is `Quadrature.sub_composite_trapezoid_eq` written with the book's
displayed sum, which is `Quadrature.trapezoidSum_eq`.

The asymptotic form (12.4.39), `= -(h²/12) [g'(b) - g'(a)] + O(h⁴)` for `g` of class `C⁴`, is a
different statement: the book quotes it from the literature, it is the first Euler–Maclaurin term,
and Example 12.4.6 needs that one and not this one. -/
theorem example_12_4_5 {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) {h : ℝ}
    (hh : h = (b - a) / N) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) :
    ∃ ξ ∈ Set.Icc a b,
      (∫ t in a..b, g t) - h * ((g a + g b) / 2 + ∑ j ∈ Finset.Ico 1 N, g (a + j * h))
        = -(h ^ 2 * (b - a) / 12) * iteratedDeriv 2 g ξ := by
  have hd1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdd : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv.mp hg).2.2
  have hd2 : Differentiable ℝ (deriv g) := hdd.differentiable (by norm_num)
  have hc2 : Continuous (deriv (deriv g)) := (contDiff_one_iff_deriv.mp hdd).2
  have hiter : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hxN : a + (N : ℝ) * h = b := by
    have hc : (N : ℝ) * ((b - a) / N) = b - a := by field_simp
    rw [hh, hc]
    ring
  obtain ⟨ξ, hξ, hval⟩ := Quadrature.sub_composite_trapezoid_eq hab hN hh
    (g' := deriv g) (g'' := deriv (deriv g)) (fun x _ => (hd1 x).hasDerivAt)
    (fun x _ => (hd2 x).hasDerivAt) hc2.continuousOn
  refine ⟨ξ, hξ, ?_⟩
  rw [hiter, ← hval, Quadrature.trapezoidSum_eq hN, hxN]

/-- **(12.4.39), the asymptotic form of the composite trapezoidal error.**  For `g` of class `C⁴`
on `[a, b]` with `|g⁗| ≤ M` there, and the uniform mesh `h = (b - a)/N`,

`∫_a^b g - h [g(x_0)/2 + ⋯ + g(x_N)/2] = -(h²/12) [g'(b) - g'(a)] + O(h⁴)`,

with the explicit remainder bound `(b - a) h⁴ M / 720`.

This is the first Euler–Maclaurin term, and it is a *different* statement from the mean value form
`example_12_4_5`: it names the leading term, which is what Example 12.4.6 and Richardson
extrapolation need.  The book quotes it from the literature; it is proved in the backbone as
`Quadrature.abs_sub_trapezoidSum_add_le`, by two further integrations by parts of the Peano
identity on each panel followed by a telescoping sum. -/
theorem equation_12_4_39 {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) {h : ℝ}
    (hh : h = (b - a) / N) {g : ℝ → ℝ} (hg : ContDiff ℝ 4 g) {M : ℝ}
    (hM : ∀ t ∈ Set.Icc a b, |iteratedDeriv 4 g t| ≤ M) :
    |(∫ t in a..b, g t) - h * ((g a + g b) / 2 + ∑ j ∈ Finset.Ico 1 N, g (a + j * h))
        + h ^ 2 / 12 * (deriv g b - deriv g a)| ≤ (b - a) * h ^ 4 * M / 720 := by
  have hd0 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hc3 : ContDiff ℝ 3 (deriv g) := (contDiff_succ_iff_deriv.mp hg).2.2
  have hd1 : Differentiable ℝ (deriv g) := hc3.differentiable (by norm_num)
  have hc2 : ContDiff ℝ 2 (deriv (deriv g)) := (contDiff_succ_iff_deriv.mp hc3).2.2
  have hd2 : Differentiable ℝ (deriv (deriv g)) := hc2.differentiable (by norm_num)
  have hc1 : ContDiff ℝ 1 (deriv (deriv (deriv g))) := (contDiff_succ_iff_deriv.mp hc2).2.2
  have hd3 : Differentiable ℝ (deriv (deriv (deriv g))) := hc1.differentiable (by norm_num)
  have hcont4 : Continuous (deriv (deriv (deriv (deriv g)))) := (contDiff_one_iff_deriv.mp hc1).2
  have hiter : iteratedDeriv 4 g = deriv (deriv (deriv (deriv g))) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hxN : a + (N : ℝ) * h = b := by
    have hc : (N : ℝ) * ((b - a) / N) = b - a := by field_simp
    rw [hh, hc]
    ring
  have hbound := Quadrature.abs_sub_trapezoidSum_add_le hab hN hh
    (g' := deriv g) (g'' := deriv (deriv g)) (g₃ := deriv (deriv (deriv g)))
    (g₄ := deriv (deriv (deriv (deriv g)))) (M := M) (fun t _ => (hd0 t).hasDerivAt)
    (fun t _ => (hd1 t).hasDerivAt) (fun t _ => (hd2 t).hasDerivAt)
    (fun t _ => (hd3 t).hasDerivAt) hcont4.continuousOn (by rw [← hiter]; exact hM)
  rwa [Quadrature.trapezoidSum_eq hN, hxN] at hbound

/-! ### The asymptotic error expansion of the Nyström solution -/

section Expansion

open IntegralOperator MeasureTheory

/-- The error identity of a second kind equation, in the form the asymptotic expansion needs: if
`(λ - K) u = f` and `(λ - K_n) u_n = f` and `(λ - K_n) γ_n = d`, then

`u - u_n - r γ_n = (λ - K_n)⁻¹ [(K - K_n) u - r d]`

for every scalar `r`.  At `r = 0` it is (12.4.45). -/
private theorem sub_smul_eq_symm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : ℝ}
    {K Kn : V →L[ℝ] V} {en : V ≃L[ℝ] V} (hen : (en : V →L[ℝ] V) = μ • 1 - Kn)
    {u un f d γn : V} (hu : (μ • 1 - K : V →L[ℝ] V) u = f)
    (hun : (μ • 1 - Kn : V →L[ℝ] V) un = f) (hγn : (μ • 1 - Kn : V →L[ℝ] V) γn = d) (r : ℝ) :
    u - un - r • γn = en.symm (K u - Kn u - r • d) := by
  have e0 : (μ • 1 - Kn : V →L[ℝ] V) (u - un) = K u - Kn u := by
    rw [map_sub, hun, ← hu]
    simp only [sub_apply, smul_apply, one_apply_eq_self]
    abel
  have e1 : (μ • 1 - Kn : V →L[ℝ] V) (u - un - r • γn) = K u - Kn u - r • d := by
    rw [map_sub, map_smul, hγn, e0]
  rw [← e1, ← hen, ContinuousLinearEquiv.coe_coe, en.symm_apply_apply]

/-- The auxiliary solutions of the exact and of the approximate equation differ by
`γ_n - γ = (λ - K_n)⁻¹ (K_n - K) γ`, which is what makes `γ_n → γ`. -/
private theorem sub_aux_eq_symm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : ℝ}
    {K Kn : V →L[ℝ] V} {en : V ≃L[ℝ] V} (hen : (en : V →L[ℝ] V) = μ • 1 - Kn)
    {d γ γn : V} (hγ : (μ • 1 - K : V →L[ℝ] V) γ = d)
    (hγn : (μ • 1 - Kn : V →L[ℝ] V) γn = d) :
    γn - γ = en.symm (Kn γ - K γ) := by
  have e1 : (μ • 1 - Kn : V →L[ℝ] V) (γn - γ) = Kn γ - K γ := by
    rw [map_sub, hγn, ← hγ]
    simp only [sub_apply, smul_apply, one_apply_eq_self]
    abel
  rw [← e1, ← hen, ContinuousLinearEquiv.coe_coe, en.symm_apply_apply]

variable {a b : ℝ}

/-- **(12.4.44), the asymptotic error formula of the Nyström method with the trapezoidal rule,
uniformly in the row variable.**  Let `K` be the integral operator of a continuous kernel on
`[a, b]`, let `K_n` be the Nyström operator of a rule that *is* the composite trapezoidal rule on
the uniform mesh of `N` panels — that is what `hquad` says — and let the row integrands
`y ↦ k (t, y) u (y)` be given by a family `G t` of `C⁴` functions on the line with a bound `M₄` on
the fourth derivatives that is uniform in `t`.  Then

`‖(K - K_n) u - h² d‖_∞ ≤ (b - a) h⁴ M₄ / 720`,
`d (t) = -(1/12) [∂_y (k (t, y) u (y))]_{y = a}^{y = b}`,

which is (12.4.44) with the `O(h⁴)` made explicit.

This is `equation_12_4_39` applied at each row `t`; what makes it *uniform* is that the hypotheses
are carried as a family, so that the constant `M₄` does not depend on `t`.  Everything else is the
identification of `IntegralOperator.nystromCLM` with `Quadrature.trapezoidSum` on the clamped
integrand, which `hquad` and `IntegralOperator.nystromCLM_apply_eq_functional` supply. -/
theorem equation_12_4_44 (hab : a < b) (k : C(Set.Icc a b × Set.Icc a b, ℝ))
    {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : h = (b - a) / N)
    {m : ℕ} {w : Fin m → ℝ} {x : Fin m → Set.Icc a b}
    (hquad : ∀ v : C(Set.Icc a b, ℝ), Quadrature.functional w x v
      = Quadrature.trapezoidSum (fun y => v (Set.projIcc a b hab.le y)) a h N)
    (u : C(Set.Icc a b, ℝ)) {G : Set.Icc a b → ℝ → ℝ}
    (hG : ∀ t, ContDiff ℝ 4 (G t))
    (hGval : ∀ t y : Set.Icc a b, k (t, y) * u y = G t (y : ℝ))
    {M₄ : ℝ} (hM₄ : ∀ t : Set.Icc a b, ∀ y ∈ Set.Icc a b, |iteratedDeriv 4 (G t) y| ≤ M₄)
    {d : C(Set.Icc a b, ℝ)}
    (hd : ∀ t : Set.Icc a b, d t = -(1 / 12) * (deriv (G t) b - deriv (G t) a)) :
    ‖kernelCLM (iccMeasure a b) k u - nystromCLM w x k u - h ^ 2 • d‖
      ≤ (b - a) * h ^ 4 * M₄ / 720 := by
  have hab' : a ≤ b := hab.le
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hh0 : 0 < h := by
    rw [hh]
    exact div_pos (by linarith) hNR
  have hbN : a + (N : ℝ) * h = b := by
    rw [hh]
    field_simp
    ring
  have hnode : ∀ r : ℝ, 0 ≤ r → r ≤ (N : ℝ) → a + r * h ∈ Set.Icc a b := by
    intro r hr0 hrN
    refine ⟨by nlinarith, ?_⟩
    nlinarith
  have hM0 : (0 : ℝ) ≤ M₄ :=
    le_trans (abs_nonneg _) (hM₄ ⟨a, Set.left_mem_Icc.2 hab'⟩ a (Set.left_mem_Icc.2 hab'))
  have hKu : ∀ t : Set.Icc a b, kernelCLM (iccMeasure a b) k u t = ∫ y in a..b, G t y := by
    intro t
    rw [← fredholm_eq_kernelCLM hab' k, fredholm_apply]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hab'] at hy
    rw [hGval t (Set.projIcc a b hab' y), coe_projIcc_of_mem hab' hy]
  have hKnu : ∀ t : Set.Icc a b,
      nystromCLM w x k u t = Quadrature.trapezoidSum (G t) a h N := by
    intro t
    have hcl : ∀ r : ℝ, r ∈ Set.Icc a b →
        (rowMul k u t) (Set.projIcc a b hab' r) = G t r := by
      intro r hr
      rw [rowMul_apply, hGval t (Set.projIcc a b hab' r), coe_projIcc_of_mem hab' hr]
    rw [nystromCLM_apply_eq_functional, hquad, Quadrature.trapezoidSum, Quadrature.trapezoidSum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt : j < N := Finset.mem_range.1 hj
    have hjN : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hjlt.le
    have hj1 : (j : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hjlt
    rw [hcl _ (hnode _ (Nat.cast_nonneg j) hjN), hcl _ (hnode _ (by positivity) hj1)]
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  have htrap : Quadrature.trapezoidSum (G t) a h N
      = h * ((G t a + G t b) / 2 + ∑ j ∈ Finset.Ico 1 N, G t (a + j * h)) := by
    rw [Quadrature.trapezoidSum_eq hN, hbN]
  have hval : (kernelCLM (iccMeasure a b) k u - nystromCLM w x k u - h ^ 2 • d) t
      = (∫ y in a..b, G t y)
        - h * ((G t a + G t b) / 2 + ∑ j ∈ Finset.Ico 1 N, G t (a + j * h))
        + h ^ 2 / 12 * (deriv (G t) b - deriv (G t) a) := by
    rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
      hKu t, hKnu t, htrap, hd t]
    ring
  rw [hval, Real.norm_eq_abs]
  exact equation_12_4_39 hab hN hh (hG t) (hM₄ t)

/-- **Example 12.4.6, the asymptotic error expansion of the Nyström solution.**  In the setting of
`equation_12_4_44`, let `λ ≠ 0` be such that `λ - K` is invertible and let the quadrature rules
have uniformly bounded absolute weight sums.  Then the book's auxiliary function `γ`, the solution
of

`λ γ (x) - ∫_a^b k (x, y) γ (y) dy = -(1/12) [∂_y (k (x, y) u (y))]_{y = a}^{y = b}`,

exists, `‖(K - K_n) γ‖ → 0`, and for all large `n` the same equation with `K` replaced by `K_n` has
a solution `γ_n` with

* `‖u - u_n - h_n² γ_n‖_∞ ≤ c (b - a) h_n⁴ M₄ / 720` — this is (12.4.49), with `γ_n` in place of
  `γ` and the `O(h⁴)` made explicit;
* `‖γ_n - γ‖ ≤ c ‖(K - K_n) γ‖`, so `γ_n → γ` and `u - u_n = h_n² γ + o(h_n²)`;
* and, whenever `‖(K - K_n) γ‖ ≤ c₂ h_n²`,
  `‖u - u_n - h_n² γ‖ ≤ c (b - a) h_n⁴ M₄ / 720 + c c₂ h_n⁴`, which is (12.4.49) with the book's
  `γ` itself.

The last hypothesis is what the *smoothness of `γ`* buys — (12.4.43) applied to the row integrands
`k (·, y) γ (y)` gives it as soon as those are `C²` uniformly — and it is the one place where this
statement is conditional.  It is exactly the book's "by a similar argument, it can also be shown
that `r_n = O(h⁴)`": proving it outright means differentiating `γ = (1/λ) (d + K γ)` twice under
the integral sign, for which the library has no machinery.  Everything else — the expansion
(12.4.44) uniformly in the row variable, the identity (12.4.45) and the convergence `γ_n → γ` — is
proved here.

The proof replaces the book's `ε_n = (λ - K)⁻¹ (K - K_n) u` by the exactly computable
`h_n² γ_n = (λ - K_n)⁻¹ (h_n² d)`: then `(λ - K_n)(u - u_n - h_n² γ_n) = (K - K_n) u - h_n² d`,
whose norm `equation_12_4_44` bounds, and `(λ - K_n)(γ_n - γ) = (K_n - K) γ`. -/
theorem example_12_4_6 (hab : a < b) (k : C(Set.Icc a b × Set.Icc a b, ℝ))
    {N : ℕ → ℕ} (hN : ∀ n, 0 < N n) {hs : ℕ → ℝ} (hhs : ∀ n, hs n = (b - a) / N n)
    (hlim : Tendsto hs atTop (𝓝 0))
    {m : ℕ → ℕ} {w : ∀ n, Fin (m n) → ℝ} {x : ∀ n, Fin (m n) → Set.Icc a b} {W : ℝ}
    (hW : ∀ n, ∑ j, |w n j| ≤ W)
    (hquad : ∀ n, ∀ v : C(Set.Icc a b, ℝ), Quadrature.functional (w n) (x n) v
      = Quadrature.trapezoidSum (fun y => v (Set.projIcc a b hab.le y)) a (hs n) (N n))
    {μ : ℝ} (hμ : μ ≠ 0) {e : C(Set.Icc a b, ℝ) ≃L[ℝ] C(Set.Icc a b, ℝ)}
    (he : (e : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ))
      = μ • 1 - kernelCLM (iccMeasure a b) k)
    (u : C(Set.Icc a b, ℝ)) {G : Set.Icc a b → ℝ → ℝ} (hG : ∀ t, ContDiff ℝ 4 (G t))
    (hGval : ∀ t y : Set.Icc a b, k (t, y) * u y = G t (y : ℝ))
    {M₄ : ℝ} (hM₄ : ∀ t : Set.Icc a b, ∀ y ∈ Set.Icc a b, |iteratedDeriv 4 (G t) y| ≤ M₄)
    {d : C(Set.Icc a b, ℝ)}
    (hd : ∀ t : Set.Icc a b, d t = -(1 / 12) * (deriv (G t) b - deriv (G t) a)) :
    ∃ (γ : C(Set.Icc a b, ℝ)) (c : ℝ),
      (μ • 1 - kernelCLM (iccMeasure a b) k :
        C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) γ = d ∧
      Tendsto (fun n => ‖kernelCLM (iccMeasure a b) k γ - nystromCLM (w n) (x n) k γ‖)
        atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∃ γn : C(Set.Icc a b, ℝ),
        (μ • 1 - nystromCLM (w n) (x n) k :
          C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) γn = d ∧
        ‖γn - γ‖ ≤ c * ‖kernelCLM (iccMeasure a b) k γ - nystromCLM (w n) (x n) k γ‖ ∧
        ∀ f un : C(Set.Icc a b, ℝ),
          (μ • 1 - kernelCLM (iccMeasure a b) k :
            C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) u = f →
          (μ • 1 - nystromCLM (w n) (x n) k :
            C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) un = f →
          ‖u - un - hs n ^ 2 • γn‖ ≤ c * ((b - a) * hs n ^ 4 * M₄ / 720) ∧
          ∀ c₂ : ℝ,
            ‖kernelCLM (iccMeasure a b) k γ - nystromCLM (w n) (x n) k γ‖ ≤ c₂ * hs n ^ 2 →
            ‖u - un - hs n ^ 2 • γ‖
              ≤ c * ((b - a) * hs n ^ 4 * M₄ / 720) + c * c₂ * hs n ^ 4 := by
  have hab' : a ≤ b := hab.le
  have hQ : ∀ v : C(Set.Icc a b, ℝ),
      Tendsto (fun n => Quadrature.functional (w n) (x n) v) atTop
        (𝓝 (integralCLM (iccMeasure a b) v)) := by
    intro v
    have hcont : ContinuousOn (fun y : ℝ => v (Set.projIcc a b hab' y)) (Set.Icc a b) :=
      (continuous_apply_projIcc hab' v).continuousOn
    have hint : integralCLM (iccMeasure a b) v = ∫ y in a..b, v (Set.projIcc a b hab' y) := by
      rw [integralCLM_apply, ← integral_iccMeasure hab' fun y => v (Set.projIcc a b hab' y)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp)
    rw [hint]
    refine (Quadrature.tendsto_trapezoidSum (g := fun y : ℝ => v (Set.projIcc a b hab' y))
      hab' hcont hN hhs hlim).congr fun n => ?_
    rw [hquad n v]
  have hfam := isCollectivelyCompactFamily_nystromCLM (iccMeasure a b) k hW hQ
  obtain ⟨c₀, hc₀⟩ := theorem_12_4_4 (ν := iccMeasure a b) hμ k hW hQ he
  have hγ : (μ • 1 - kernelCLM (iccMeasure a b) k :
      C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) (e.symm d) = d := by
    rw [← he, ContinuousLinearEquiv.coe_coe, e.apply_symm_apply]
  refine ⟨e.symm d, c₀, hγ, ?_, ?_⟩
  · have h1 : Tendsto (fun n => nystromCLM (w n) (x n) k (e.symm d)) atTop
        (𝓝 (kernelCLM (iccMeasure a b) k (e.symm d))) := hfam.tendsto (e.symm d)
    have h2 : Tendsto (fun n => kernelCLM (iccMeasure a b) k (e.symm d)
        - nystromCLM (w n) (x n) k (e.symm d)) atTop
        (𝓝 (kernelCLM (iccMeasure a b) k (e.symm d)
          - kernelCLM (iccMeasure a b) k (e.symm d))) := tendsto_const_nhds.sub h1
    rw [sub_self] at h2
    simpa using h2.norm
  filter_upwards [hc₀] with n hn
  obtain ⟨en, hencoe, hennorm, -⟩ := hn
  have hc00 : (0 : ℝ) ≤ c₀ := le_trans (norm_nonneg _) hennorm
  have hsym : ∀ v : C(Set.Icc a b, ℝ), ‖en.symm v‖ ≤ c₀ * ‖v‖ := fun v =>
    (ContinuousLinearMap.le_opNorm (en.symm : C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) v).trans
      (mul_le_mul_of_nonneg_right hennorm (norm_nonneg v))
  have hγn : (μ • 1 - nystromCLM (w n) (x n) k :
      C(Set.Icc a b, ℝ) →L[ℝ] C(Set.Icc a b, ℝ)) (en.symm d) = d := by
    rw [← hencoe, ContinuousLinearEquiv.coe_coe, en.apply_symm_apply]
  have hgap : ‖en.symm d - e.symm d‖
      ≤ c₀ * ‖kernelCLM (iccMeasure a b) k (e.symm d)
        - nystromCLM (w n) (x n) k (e.symm d)‖ := by
    rw [sub_aux_eq_symm hencoe hγ hγn]
    refine (hsym _).trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) hc00)
    exact norm_sub_rev _ _
  refine ⟨en.symm d, hγn, hgap, fun f un hu hun => ?_⟩
  have hbase : ‖u - un - hs n ^ 2 • en.symm d‖ ≤ c₀ * ((b - a) * hs n ^ 4 * M₄ / 720) := by
    rw [sub_smul_eq_symm hencoe hu hun hγn (hs n ^ 2)]
    refine (hsym _).trans (mul_le_mul_of_nonneg_left ?_ hc00)
    exact equation_12_4_44 hab k (hN n) (hhs n) (hquad n) u hG hGval hM₄ hd
  refine ⟨hbase, fun c₂ hc₂ => ?_⟩
  have hsq : (0 : ℝ) ≤ hs n ^ 2 := sq_nonneg _
  have hsplit : u - un - hs n ^ 2 • e.symm d
      = (u - un - hs n ^ 2 • en.symm d) + hs n ^ 2 • (en.symm d - e.symm d) := by
    rw [smul_sub]
    abel
  calc ‖u - un - hs n ^ 2 • e.symm d‖
      ≤ ‖u - un - hs n ^ 2 • en.symm d‖ + ‖hs n ^ 2 • (en.symm d - e.symm d)‖ := by
        rw [hsplit]
        exact norm_add_le _ _
    _ = ‖u - un - hs n ^ 2 • en.symm d‖ + hs n ^ 2 * ‖en.symm d - e.symm d‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsq]
    _ ≤ c₀ * ((b - a) * hs n ^ 4 * M₄ / 720) + hs n ^ 2 * (c₀ * (c₂ * hs n ^ 2)) := by
        gcongr
        exact hgap.trans (mul_le_mul_of_nonneg_left hc₂ hc00)
    _ = c₀ * ((b - a) * hs n ^ 4 * M₄ / 720) + c₀ * c₂ * hs n ^ 4 := by ring

end Expansion

end AtkinsonHan.Chapter12
