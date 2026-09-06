import Numlib.IntegralEquations.SecondKind

/-!
# Atkinson–Han §12.4: the Nyström method and collectively compact approximation

Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009.

Only the abstract half of the section, §12.4.3, is formalized: the perturbation theorem whose
hypothesis constrains `(T - S) S` rather than `T - S`, the assumptions A1–A3, and Lemma 12.4.7.
That is the framework which makes the Nyström method analysable, and which §12.5 reuses for
product integration.  As in §12.1 the book's scalar `λ` is written `μ`, `λ` being Lean's lambda
binder.

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

## Not formalized here

Lemma 12.4.2 and Theorem 12.4.4 in their stated form, which instantiate this framework for the
numerical integral operators `K_n u (x) = Σ_j w_j k (x, t_j) u (t_j)` on `C(D)`.  Their content is
that those operators form a collectively compact, pointwise convergent family, which needs the
`C(D)` integral-operator toolkit together with a convergent quadrature rule; neither the
quadrature rule nor its Banach–Steinhaus convergence criterion exists yet.  Once they do,
`theorem_12_4_4` is one application of `exists_norm_inverse_le_of_isCollectivelyCompactFamily` and
belongs in this file.
-/

open Filter Topology

namespace AtkinsonHan.Ch12

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

end AtkinsonHan.Ch12
