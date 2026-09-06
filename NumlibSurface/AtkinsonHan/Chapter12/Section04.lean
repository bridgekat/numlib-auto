import Numlib.Approximation.CompositeQuadrature
import Numlib.IntegralEquations.Nystrom
import Numlib.IntegralEquations.SecondKind

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
* `lemma_12_4_2_a`–`lemma_12_4_2_c` — the three clauses of Lemma 12.4.2: the identities (12.4.14)
  expressing `(K - K_n) K` and `(K - K_n) K_n` through the single kernel `e_n`, the norm formulas
  (12.4.16)–(12.4.17), and (12.4.18), that both norms tend to zero.
* `theorem_12_4_4` — the Nyström instance of the abstract theorem.
* `example_12_4_5` — the composite trapezoidal rule error `-h² (b - a) g''(ξ) / 12`, an instance
  of `Quadrature.sub_composite_trapezoid_eq` in `Numlib/Approximation/CompositeQuadrature`.
* `equation_12_4_39` — its asymptotic form `-(h²/12) [g'(b) - g'(a)] + O(h⁴)`, the first
  Euler–Maclaurin term, with the explicit remainder `(b - a) h⁴ ‖g⁗‖_∞ / 720`.  The book quotes
  this one from the literature; it is `Quadrature.abs_sub_trapezoidSum_add_le`.

## Not formalized here

Example 12.4.6, the `h²`-expansion of the *Nyström* error that justifies Richardson extrapolation.
Its operator half is `SecondKind.norm_sub_le`; what is missing is the expansion `u - u_n = h² γ +
O(h⁴)` with `γ` itself the solution of an integral equation whose data is the Euler–Maclaurin
boundary term of `equation_12_4_39` applied to the *kernel* in the second variable, uniformly in
the first.  That is a statement about the Nyström error kernel and not about a single integrand,
and it is what remains.

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
`e_n` (12.4.14), and hence its norm is the largest absolute weight sum of `e_n` (12.4.17). -/
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

end AtkinsonHan.Chapter12
