import NumlibSurface.CartisGouldToint.Chapter14.Section03Genuine

/-!
# Cartis–Gould–Toint §14.3: Theorem 14.3.9 for TPqp-GC runs with a trust-region INNER

Surface file for C. Cartis, N. I. M. Gould and Ph. L. Toint, *Evaluation Complexity of
Algorithms for Nonconvex Optimization* [cartis2022evaluation], Theorem 14.3.9 (complexity of
TPqp-GC, Algorithm 14.3.2) when INNER is of trust-region type. The theorem is proved for **every**
run whose INNER calls are genuine TRq-SC runs (Algorithm 12.2.1 with a feasible set,
`Chapter12.algorithm_12_2_1_feasible`, threshold `ϑ`), in both phases, under X.CNe, c.D1qLB.X,
f.D1qLB.X and f.B.Fb, with constants chosen before the tolerances `ε₀`, `ε`.

For every Phase-2 run with TRq-SC calls, the INNER contract keyed on INNER's own test
(`IsInnerPhaseRunStrong`) holds with `t`-independent constants except for one logarithmic term:
unsuccessful steps do not move; every successful step decreases `μ(·, t_k)` by at least
`κ_decr ε'_min^{q+1}` (Lemma 12.2.4, with `ε'_j = β ‖r(x_k, t_k)‖ ε_j`), for every successful
step, not only those not followed by a termination; the radii of a call stay above
`κ_ρ ε'_min ≥ κ_ρ βθ ε₀ ε_min` (Lemma 12.2.3 with (12.2.9)), so the returned radii are at least
that and the number of iterations of a call is at most
`κ_uns (|𝒮| + 1) + |log(κ_ρ ε'_min/Δ₀)|/|log γ₂|` (Lemma 2.3.1). The constants of Lemma 12.2.3
depend on the derivatives at the start of the call, which Lemma 14.3.6 (ii) bounds uniformly on
`𝓛_μ(t)` (`trqKappaDelta_ge`). Then `IsTPqpGCPhase2.exists_const_order_of_strong_unc` bounds
Phase 2. Phase 1 uses the additive cost contract from Theorem 12.2.5 (`lemma_14_3_7_add`).

## Main definitions

* `trqSCKappaDelta`, `trqSCKappaRad`, `trqSCKappaDecr`, `trqSCKappaUns`, `trqSCKappaUnc0`,
  `trqSCKappaS`, `trqSCKappaA`, `trqSCKappaC`: the constants of the TRq-SC analysis with the
  derivative bound `M` in place of the derivatives at the starting point; `trqSCLogTerm`: the
  logarithmic term `|log(ε₀ ε_min)|`;
* `IsTRqSCCallOut`, `IsTRqSCPhase2Calls`: Phase-2 INNER calls that are TRq-SC runs, with their
  output radii `min(Δ_e, ϑ)`, cut at any iteration by any test of (14.3.32);
* `IsTRqSCOutputCost`: a Phase-1 INNER call that is a terminating TRq-SC run, with its evaluation
  counts;
* `IsTPqpGCTRqSCRun`: TPqp-GC runs whose INNER calls are TRq-SC runs in both phases.

## Main results

* `IsTRqSCCallOut.contract`, `IsTRqSCPhase2Calls.isInnerPhaseRunStrong`: the INNER contract for
  every run, with the exponents `π_j = q + 1` and radii `ρ_j = κ_ρ βθ ε₀ ε_min`;
* `IsTRqSCOutputCost.cost_le`, `phase1_call_cost_trq`: the cost of the Phase-1 calls;
* `IsTPqpGCPhase2.exists_const_order_of_strong_unc` (in `Chapter14.Section03Genuine`): Phase 2
  within an order bound with a count constant `κ_unc` chosen after `ε` (the function-evaluation
  bound is affine in `κ_unc`);
* `theorem_14_3_9_trq`: Theorem 14.3.9 for every run of `IsTPqpGCTRqSCRun` and every `q ≥ 1`:
  `O((1 + |log(ε₀ ε_min)|) max[ε₀^{-1}, max_j ε₀^{-q} ε_j^{-(q+1)}])` evaluations of `(f, c)` and
  `O(max_j ε₀^{-q} ε_j^{-(q+1)})` derivative evaluations;
* `theorem_14_3_9_trq_one`: for `q = 1` the exponent is the printed `π_1 = 2`, so the derivative
  count is in the printed order and the function count is in the printed order up to the factor
  `1 + |log(ε₀ ε_1)|`;
* `exists_algorithm_12_2_1_feasible`: TRq-SC runs exist from every point of a closed `X`;
* `exists_isTPqpGCTRqSCRun`: the run class is not empty (`X` closed, `x₀ ∈ X`, `β ≤ ϑ ≤ 1`,
  `β₁ ‖c(x₀)‖ ≤ ϑ`).

## Deviations from the book

* Exponents: (14.2.12) prints `π_j = j + 1` for TRq-SC; Lemma 12.2.4 (and the TRq-SC row of
  Lemma 14.2.2 as proved in `Chapter14.Section02`) gives the decrease `κ ε_min^{q+1}`, i.e.
  `π_j = q + 1`, which is also the order `O(max_j ε_j^{-(q+1)})` that the book's own
  Theorem 14.2.4 lists for TRq-SC (OCR l. 16351). The row `j + 1` is false as a per-iteration
  decrease for `q = 2` with `κ_decr` depending only on the algorithm parameters, `ϑ` and the
  f.D1qLaB.X constants, as in (12.2.14) (`lemma_14_2_2_trq_printed_false_uniform`,
  `Chapter14.Section03TrustRegionSharp`: the radius is shared by the orders and is driven down by
  first-order failures). The theorem is proved with `π_j = q + 1`; the printed exponents agree
  for `q = 1` (`theorem_14_3_9_trq_one`). For `q ≥ 2` the printed order
  `max_j ε₀^{-j} ε_j^{-(j+1)}` would be smaller than the proved `max_j ε₀^{-q} ε_j^{-(q+1)}` (by
  an unbounded factor as `ε_1 → 0` with the other tolerances equal to `1`). The printed order is
  false for whole runs for every `q ≥ 2`, even with the factor `1 + |log(ε₀ ε_min)|`, for runs
  ending in Phase 1 and in Phase 2 (`theorem_14_3_9_trq_printed_false`,
  `theorem_14_3_9_trq_printed_false_phase2`, `Chapter14.Section03TrustRegionPrinted`).
* The factor `1 + |log(ε₀ ε_min)|` on the function evaluations: every INNER call restarts from the
  radius `Δ₀` (the book's INNER interface returns no trust-region radius), so the unsuccessful
  iterations of a call are bounded only by `log(Δ₀/(κ_ρ ε'_min))` (the TRq-SC `κ_unc` of
  Lemma 14.2.3 contains `|log ε_min|`, `Chapter14.Section02`), and Lemma 14.3.8 multiplies this by
  the number of outer iterations. The book treats `κ_unc` as a constant. The derivative count has
  no such factor. For `q = 1` the factor is needed: on an example satisfying all hypotheses,
  every run uses `≳ ε₀^{-1} log(1/ε₀)` evaluations for `ε_1 = 1/2`
  (`theorem_14_3_9_trq_log_necessary`, `Chapter14.Section03TrustRegionSharp`). The example works for
  every `q` (`theorem_14_3_9_trq_log_necessary_inv`: no bound `κ_F ε₀^{-1}` at fixed dual
  tolerances), but for `q ≥ 2` it does not show that the factor is needed: the printed order and
  the proved one are then at least `ε₀^{-2}` (`inv_sq_le_tpqpOrderF_trqLogTol`). In the proof the
  factor multiplies the whole order; the case-(a) iterations and Phase 1 contribute only
  `Λ ε₀^{-1}` (within the printed order for `q ≥ 2`, since `|log u| ≤ 1/u`), and the rest comes
  from the case-(b) calls, whose number is only bounded by the order itself.
* The book's f.D1qLB.Fb is not defined in the book (only f.D1pLB.X is, OCR l. 17195); f.D1qLB.X
  (`AssumptionD1pLBX` with `q`) is used. c.D1qLB.X is `AssumptionCD1pLBX` with `q`.
* The INNER threshold `ϑ ∈ (0, 1]` is fixed for all calls and must dominate the tolerances of the
  calls: `β ≤ ϑ` (Phase 2) and `β₁ ‖c(x₀)‖ ≤ ϑ` (Phase 1) (the book's Step 0 of Algorithm 12.2.1
  asks `ϑ ∈ [ε_min, 1]`).
* As in `Chapter14.Section03Genuine`: the book's `f_up - f_low - 1` is `f_up - f_low + 1`,
  `max_j` is kept (`tpqpOrderF`, `tpqpOrderD`), the constants depend on the data, on `P`, `ϑ`, `θ`,
  `β`, `β₁`, `f_up - f_low` and `‖c(x₀)‖`, and f.B.Fb is on `ℱ_{β_F}` with `ε₀ ≤ β_F`.

## Not formalized

The failure of (14.2.11) with the exponents `j + 1` for a single fixed `f`; whether the factor
`1 + |log(ε₀ ε_min)|` is needed for `q ≥ 2`; orders between the printed and the proved ones, and
lower bounds attaining the proved order (archived at commit 8c2b1518 on branch
`claude/cartis-gould-toint-formalization`). The TRqIDA-SC and TRqEDA-SC INNER variants.
-/

open Set Metric
open scoped Nat

namespace CartisGouldToint.Chapter14

variable {n m : ℕ}

set_option hygiene false in
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

set_option hygiene false in
local notation "ℝᵐ" => EuclideanSpace ℝ (Fin m)

/-- `a b ≤ 1` for `a ≤ 1` and `b ∈ [0, 1]`. -/
private theorem mul_le_one_aux {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) :
    a * b ≤ 1 :=
  (mul_le_of_le_one_left hb0 ha).trans hb

/-! ### The constants of the TRq-SC analysis -/

section Constants

variable (P : Optimization.TRqParams) (L : ℕ → ℝ) (ϑ M : ℝ) (q : ℕ)

/-- The lower bound `κ_Δ(M) = γ₁ (1 - η₂)/L_f · min(ϑ, Δ₀ δ₀^q/(2 q! M))` of the constant `κ_Δ`
of (12.2.14) of [cartis2022evaluation] (`Chapter12.trqKappaDelta`), for a bound `M` on the
derivatives of orders `1, …, q` at the starting point and `L_f = max(1, max_j L_j)`. -/
noncomputable def trqSCKappaDelta : ℝ :=
  Optimization.trqKappa P (Chapter12.finMax 1 L q) ϑ M q

/-- The radius constant `κ_ρ = min(γ₁ ϑ, ς κ_Δ(M), Δ₀)` of a TRq-SC run: the trust-region radii
up to termination, and the optimality radii `min(Δ_k, ϑ)`, are at least `κ_ρ ε_min`
(Lemma 12.2.3 of [cartis2022evaluation] with (12.2.9)). -/
noncomputable def trqSCKappaRad : ℝ :=
  min (min (P.γ₁ * ϑ) (trqSCKappaDelta P L ϑ M q * P.ς)) P.Δ₀

/-- The decrease constant `κ_decr = η₁ (ς κ_Δ(M))^{q+1}/q!` of Lemma 12.2.4 of
[cartis2022evaluation] (the TRq-SC row of Lemma 14.2.2): a successful iteration decreases the
objective by at least `κ_decr ε_min^{q+1}`. -/
noncomputable def trqSCKappaDecr : ℝ :=
  P.η₁ * ((P.ς * trqSCKappaDelta P L ϑ M q) ^ (q + 1) / q !)

/-- The constant `κ_uns = 1 + log γ₃/|log γ₂|` of Lemma 2.3.1 of [cartis2022evaluation] (the
TRq-SC row of Lemma 14.2.3). -/
noncomputable def trqSCKappaUns : ℝ :=
  1 + Real.log P.γ₃ / |Real.log P.γ₂|

/-- The constant part `κ_uns + (|log Δ₀| + |log κ_ρ| + |log(βθ)|)/|log γ₂|` of the count of the
iterations of one Phase-2 TRq-SC call; the full count adds `|log(ε₀ ε_min)|/|log γ₂|`
(`trqSCLogTerm`). -/
noncomputable def trqSCKappaUnc0 (β θ : ℝ) : ℝ :=
  trqSCKappaUns P + (|Real.log P.Δ₀| + |Real.log (trqSCKappaRad P L ϑ M q)| +
    |Real.log (β * θ)|) / |Real.log P.γ₂|

/-- The constant `κ^S = q!/(η₁ (ς κ_Δ(M))^{q+1})` of Theorem 12.2.5 of [cartis2022evaluation]
with `κ_Δ(M)` in place of `κ_Δ`. -/
noncomputable def trqSCKappaS : ℝ :=
  q ! / (P.η₁ * (P.ς * trqSCKappaDelta P L ϑ M q) ^ (q + 1))

/-- The constant `κ^A = κ^S (1 + log γ₃/|log γ₂|)` of Theorem 12.2.5 of [cartis2022evaluation]
with `κ_Δ(M)` in place of `κ_Δ`. -/
noncomputable def trqSCKappaA : ℝ :=
  trqSCKappaS P L ϑ M q * trqSCKappaUns P

/-- An upper bound `(|log ς| + |log κ_Δ(M)| + |log Δ₀|)/|log γ₂| + 1` for the constant
`κ^C = |log(ς κ_Δ/Δ₀)|/|log γ₂| + 1` of Theorem 12.2.5 of [cartis2022evaluation]. -/
noncomputable def trqSCKappaC : ℝ :=
  (|Real.log P.ς| + |Real.log (trqSCKappaDelta P L ϑ M q)| + |Real.log P.Δ₀|) /
    |Real.log P.γ₂| + 1

/-- The logarithmic term `|log(ε₀ ε_min)|`, `ε_min = min_{j ∈ [1 : q]} ε_j`, of the number of
unsuccessful iterations of the trust-region INNER calls. -/
noncomputable def trqSCLogTerm (q : ℕ) (ε : ℕ → ℝ) : ℝ :=
  |Real.log (ε 0 * Chapter12.finMin 1 ε q)|

variable {P L ϑ M q}

/-- `κ_Δ(M) > 0` for `ϑ, M > 0`. -/
theorem trqSCKappaDelta_pos (hϑ : 0 < ϑ) (hM : 0 < M) : 0 < trqSCKappaDelta P L ϑ M q :=
  Optimization.trqKappa_pos (zero_lt_one.trans_le Chapter12.one_le_finMax) hϑ hM

/-- `κ_Δ(M) < 1` for `ϑ ≤ 1`. -/
theorem trqSCKappaDelta_lt_one (hϑ1 : ϑ ≤ 1) : trqSCKappaDelta P L ϑ M q < 1 :=
  Optimization.trqKappa_lt_one Chapter12.one_le_finMax hϑ1

/-- `κ_ρ > 0` for `ϑ, M > 0`. -/
theorem trqSCKappaRad_pos (hϑ : 0 < ϑ) (hM : 0 < M) : 0 < trqSCKappaRad P L ϑ M q :=
  lt_min (lt_min (mul_pos P.γ₁_pos hϑ) (mul_pos (trqSCKappaDelta_pos hϑ hM) P.ς_pos)) P.Δ₀_pos

/-- `κ_ρ ≤ γ₁ ϑ`. -/
theorem trqSCKappaRad_le_γ₁ : trqSCKappaRad P L ϑ M q ≤ P.γ₁ * ϑ :=
  (min_le_left _ _).trans (min_le_left _ _)

/-- `κ_decr > 0` for `ϑ, M > 0`. -/
theorem trqSCKappaDecr_pos (hϑ : 0 < ϑ) (hM : 0 < M) : 0 < trqSCKappaDecr P L ϑ M q := by
  have := trqSCKappaDelta_pos (P := P) (L := L) (q := q) hϑ hM
  have := P.ς_pos
  have := P.η₁_pos
  unfold trqSCKappaDecr
  positivity

/-- `κ_uns ≥ 1`. -/
theorem one_le_trqSCKappaUns : 1 ≤ trqSCKappaUns P := by
  unfold trqSCKappaUns
  have := Real.log_nonneg P.one_le_γ₃
  have : 0 ≤ Real.log P.γ₃ / |Real.log P.γ₂| := div_nonneg this (abs_nonneg _)
  linarith

/-- The constant part of the count constant is nonnegative. -/
theorem trqSCKappaUnc0_nonneg (β θ : ℝ) : 0 ≤ trqSCKappaUnc0 P L ϑ M q β θ := by
  unfold trqSCKappaUnc0
  have := one_le_trqSCKappaUns (P := P)
  have : 0 ≤ (|Real.log P.Δ₀| + |Real.log (trqSCKappaRad P L ϑ M q)| +
    |Real.log (β * θ)|) / |Real.log P.γ₂| := by positivity
  linarith

/-- `κ^S ≥ 0` for `ϑ, M > 0`. -/
theorem trqSCKappaS_nonneg (hϑ : 0 < ϑ) (hM : 0 < M) : 0 ≤ trqSCKappaS P L ϑ M q := by
  have := trqSCKappaDelta_pos (P := P) (L := L) (q := q) hϑ hM
  have := P.ς_pos
  have := P.η₁_pos
  unfold trqSCKappaS
  positivity

/-- `κ^A ≥ 0` for `ϑ, M > 0`. -/
theorem trqSCKappaA_nonneg (hϑ : 0 < ϑ) (hM : 0 < M) : 0 ≤ trqSCKappaA P L ϑ M q :=
  mul_nonneg (trqSCKappaS_nonneg hϑ hM) (zero_le_one.trans one_le_trqSCKappaUns)

/-- `κ^C ≥ 1`. -/
theorem one_le_trqSCKappaC : 1 ≤ trqSCKappaC P L ϑ M q := by
  unfold trqSCKappaC
  have : 0 ≤ (|Real.log P.ς| + |Real.log (trqSCKappaDelta P L ϑ M q)| + |Real.log P.Δ₀|) /
    |Real.log P.γ₂| := by positivity
  linarith

/-- `κ_Δ(M)` is nonincreasing in `M`. -/
theorem trqKappa_anti {L' ϑ M M' : ℝ} (hL : 0 < L') (hϑ : 0 ≤ ϑ) (hM : 0 < M) (hMM : M ≤ M') :
    Optimization.trqKappa P L' ϑ M' q ≤ Optimization.trqKappa P L' ϑ M q := by
  unfold Optimization.trqKappa
  have := P.γ₁_pos
  have := P.one_sub_η₂_pos
  have := P.Δ₀_pos
  have hf : (0 : ℝ) < q ! := by positivity
  have hmin : 0 ≤ min P.Δ₀ ϑ := le_min P.Δ₀_pos.le hϑ
  refine mul_le_mul_of_nonneg_left (min_le_min le_rfl ?_) (by positivity)
  exact div_le_div_of_nonneg_left (mul_nonneg P.Δ₀_pos.le (pow_nonneg hmin q)) (by positivity)
    (by gcongr)

/-- **The constant `κ_Δ` of (12.2.14) is at least `κ_Δ(M)`** at a starting point `y` where it is
positive (which holds when the run does not stop at `0`) and the derivatives of orders `1, …, q`
are bounded by `M`. -/
theorem trqKappaDelta_ge {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : E → ℝ}
    {y : E} (hpos : 0 < Chapter12.trqKappaDelta F P q L ϑ y)
    (hM : Chapter12.finMax 0 (fun i => ‖iteratedFDeriv ℝ i F y‖) q ≤ M) (hϑ : 0 ≤ ϑ) :
    trqSCKappaDelta P L ϑ M q ≤ Chapter12.trqKappaDelta F P q L ϑ y := by
  unfold Chapter12.trqKappaDelta at hpos ⊢
  unfold trqSCKappaDelta
  set M₀ := Chapter12.finMax 0 (fun i => ‖iteratedFDeriv ℝ i F y‖) q with hM₀
  have hM₀0 : 0 < M₀ := by
    rcases (Chapter12.le_finMax_left : (0 : ℝ) ≤ M₀).lt_or_eq with h | h
    · exact h
    · exfalso
      have h' : M₀ = 0 := by rw [hM₀]; exact h.symm
      rw [h'] at hpos
      unfold Optimization.trqKappa at hpos
      have h0 : min ϑ (P.Δ₀ * min P.Δ₀ ϑ ^ q / (2 * q ! * 0)) ≤ 0 := by
        rw [mul_zero, div_zero]; exact min_le_right _ _
      have := P.γ₁_pos
      have := P.one_sub_η₂_pos
      have hL : 0 < Chapter12.finMax 1 L q := zero_lt_one.trans_le Chapter12.one_le_finMax
      exact absurd hpos (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) h0))
  exact trqKappa_anti (zero_lt_one.trans_le Chapter12.one_le_finMax) hϑ hM₀0 hM

end Constants

/-! ### One INNER call of Phase 2 realized by TRq-SC -/

section Call

variable {F : ℝⁿ → ℝ} {X : Set ℝⁿ} {q : ℕ} {P : Optimization.TRqParams} {ϑ : ℝ} {ε : ℕ → ℝ}
  {xi : ℕ → ℝⁿ} {e : ℕ} {succ : ℕ → Prop} {δo : ℕ → ℝ}

/-- One INNER call of Phase 2 of TPqp-GC realized by TRq-SC, with its output radii: the iterates
`x_{k,0}, …, x_{k,e}` are the first `e + 1` iterates of a TRq-SC run
(`Chapter12.algorithm_12_2_1_feasible`: Algorithm 12.2.1 with feasible Step-1 displacements and
steps, `x_{k,i} + d ∈ X`) on `F` with threshold `ϑ`, whose first termination index `k_ε` is at
least `e` (the call may be cut before INNER terminates, by any test of (14.3.32)); the successful
iterations are those of the run, and the returned radii are the optimality radii
`δ_e = min(Δ_e, ϑ)` of the run at the last iterate (at a termination, the radii certifying
(14.3.19), `Chapter12.theorem_12_2_5_anchored`). -/
def IsTRqSCCallOut (F : ℝⁿ → ℝ) (X : Set ℝⁿ) (q : ℕ) (P : Optimization.TRqParams) (ϑ : ℝ)
    (ε : ℕ → ℝ) (xi : ℕ → ℝⁿ) (e : ℕ) (succ : ℕ → Prop) (δo : ℕ → ℝ) : Prop :=
  ∃ (x s : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝⁿ) (kε : ℕ),
    Chapter12.algorithm_12_2_1_feasible F X P q ε ϑ x s Δ jk d ∧
    Optimization.IsFirstHit (Chapter12.trqStop F P q ε ϑ x Δ d) kε ∧
    e ≤ kε ∧ (∀ i ≤ e, xi i = x i) ∧
    (∀ i < e, (succ i ↔ P.η₁ ≤ Chapter12.trqRho F x s jk i)) ∧
    ∀ j ∈ Finset.Icc 1 q, δo j = min (Δ e) ϑ

/-- **The radius bound of a TRq-SC run**: up to (and including) termination,
`Δ_e ≥ κ_ρ ε_min` (Lemma 12.2.3 of [cartis2022evaluation] with (12.2.9) and `κ_Δ ≥ κ_Δ(M)`),
under anchored f.D1qL on a set `S` containing the sublevel set of the run at its start, with the
derivatives at the start bounded by `M`. -/
theorem trq_radius_ge {X₀ S : Set ℝⁿ} {L : ℕ → ℝ} {M : ℝ} {x s : ℕ → ℝⁿ} {Δ : ℕ → ℝ}
    {jk : ℕ → ℕ} {d : ℕ → ℕ → ℝⁿ}
    (hr : Chapter12.algorithm_12_2_1_feasible F X P q ε ϑ x s Δ jk d)
    (hF : Chapter12.AssumptionD1pLAnchored F X₀ S q L)
    (hM : ∀ y ∈ S, Chapter12.finMax 0 (fun i => ‖iteratedFDeriv ℝ i F y‖) q ≤ M)
    (hXX₀ : X ⊆ X₀) (hA : ∀ y ∈ X, F y ≤ F (x 0) → y ∈ S) (hx0 : x 0 ∈ X)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1)
    (hnot : ∀ i < e, ¬ Chapter12.trqStop F P q ε ϑ x Δ d i) :
    trqSCKappaRad P L ϑ M q * Chapter12.finMin 1 ε q ≤ Δ e := by
  have hεm1 : Chapter12.finMin 1 ε q ≤ 1 := Chapter12.finMin_le_left
  have hεm0 : 0 < Chapter12.finMin 1 ε q :=
    Chapter12.finMin_pos one_pos fun j hj => (hε j hj).1
  rcases e with _ | k
  · rw [hr.toIsTRRun.delta_zero]
    calc trqSCKappaRad P L ϑ M q * Chapter12.finMin 1 ε q ≤ P.Δ₀ * 1 :=
          mul_le_mul (min_le_right _ _) hεm1 hεm0.le P.Δ₀_pos.le
      _ = P.Δ₀ := mul_one _
  · have hk : ∀ i ≤ k, ¬ Chapter12.trqStop F P q ε ϑ x Δ d i := fun i hi => hnot i (by omega)
    obtain ⟨⟨hκ0, -⟩, -, hΔ⟩ := Chapter12.lemma_12_2_3_anchored hr hF hXX₀ hA hx0 hϑ0 hϑ1
      (fun j hj => (hε j hj).1.le) hk
    have hgap : P.ς * Chapter12.finMin 1 ε q ≤
        Optimization.prefixMin (Chapter12.trqGapSeq F ϑ x Δ jk d) k :=
      (Optimization.IsTRqRun.trqGap_ge hr hϑ0 (fun _ hj => Chapter12.finMin_le hj) hk).1
    have hκ := trqKappaDelta_ge hκ0 (hM _ (hA _ hx0 le_rfl)) hϑ0.le
    refine le_trans (le_min ?_ ?_) hΔ
    · calc trqSCKappaRad P L ϑ M q * Chapter12.finMin 1 ε q ≤ (P.γ₁ * ϑ) * 1 :=
            mul_le_mul trqSCKappaRad_le_γ₁ hεm1 hεm0.le (mul_pos P.γ₁_pos hϑ0).le
        _ = P.γ₁ * ϑ := mul_one _
    · calc trqSCKappaRad P L ϑ M q * Chapter12.finMin 1 ε q ≤
            (trqSCKappaDelta P L ϑ M q * P.ς) * Chapter12.finMin 1 ε q :=
            mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) hεm0.le
        _ = trqSCKappaDelta P L ϑ M q * (P.ς * Chapter12.finMin 1 ε q) := by ring
        _ ≤ _ := mul_le_mul hκ hgap (mul_pos P.ς_pos hεm0).le hκ0.le

open Classical in
/-- **The INNER contract of one TRq-SC call of Phase 2** ([cartis2022evaluation], Lemmas 12.2.3,
12.2.4 and 2.3.1 with a feasible set, i.e. the TRq-SC rows of Lemmas 14.2.2–14.2.3), for every
call `IsTRqSCCallOut` on an objective `F` satisfying anchored f.D1qL (constants `L`, open convex
`X₀ ⊇ X`) on a set `S` containing the sublevel set of `F` at the start of the call, with the
derivatives of orders `1, …, q` bounded by `M > 0` on `S`, tolerances `ε ∈ (0, 1]^q` and
`ε_min ≤ ϑ ≤ 1`:
(stay) unsuccessful iterations do not move;
(count) `e ≤ κ_uns (|𝒮| + 1) + |log(κ_ρ ε_min/Δ₀)|/|log γ₂|` (Lemma 2.3.1 with the radius bound
`Δ_e ≥ κ_ρ ε_min`), `𝒮` the successful iterations of the call;
(decrease) every successful iteration decreases `F` by at least `κ_decr ε_min^{q+1}`
(Lemma 12.2.4: the TRq-SC row of (14.2.12) is `π_j = q + 1`, see `Chapter14.Section02`);
(radii) the returned radii `min(Δ_e, ϑ)` are at least `κ_ρ ε_min`. -/
theorem IsTRqSCCallOut.contract {X₀ S : Set ℝⁿ} {L : ℕ → ℝ} {M : ℝ}
    (hF : Chapter12.AssumptionD1pLAnchored F X₀ S q L)
    (hM : ∀ y ∈ S, Chapter12.finMax 0 (fun i => ‖iteratedFDeriv ℝ i F y‖) q ≤ M) (hM0 : 0 < M)
    (hXX₀ : X ⊆ X₀) (h : IsTRqSCCallOut F X q P ϑ ε xi e succ δo) (hx0 : xi 0 ∈ X)
    (hS : ∀ y ∈ X, F y ≤ F (xi 0) → y ∈ S) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1)
    (hϑ : Chapter12.finMin 1 ε q ≤ ϑ) (hϑ1 : ϑ ≤ 1) :
    (∀ i < e, ¬ succ i → xi (i + 1) = xi i) ∧
    (e : ℝ) ≤ trqSCKappaUns P * ((Finset.range e).filter succ).card + trqSCKappaUns P +
      |Real.log (trqSCKappaRad P L ϑ M q * Chapter12.finMin 1 ε q / P.Δ₀)| /
        |Real.log P.γ₂| ∧
    (∀ i < e, succ i →
      trqSCKappaDecr P L ϑ M q * Chapter12.finMin 1 ε q ^ (q + 1) ≤ F (xi i) - F (xi (i + 1))) ∧
    (∀ j ∈ Finset.Icc 1 q, trqSCKappaRad P L ϑ M q * Chapter12.finMin 1 ε q ≤ δo j) := by
  obtain ⟨x, s, Δ, jk, d, kε, hr, hhit, he, hxi, hsucc, hδo⟩ := h
  have hx0' : x 0 ∈ X := hxi 0 (Nat.zero_le _) ▸ hx0
  have hA : ∀ y ∈ X, F y ≤ F (x 0) → y ∈ S := by rw [← hxi 0 (Nat.zero_le _)]; exact hS
  have hnot : ∀ i < e, ¬ Chapter12.trqStop F P q ε ϑ x Δ d i :=
    fun i hi => hhit.2 i (lt_of_lt_of_le hi he)
  have hεm0 : 0 < Chapter12.finMin 1 ε q :=
    Chapter12.finMin_pos one_pos fun j hj => (hε j hj).1
  have hϑ0 : 0 < ϑ := hεm0.trans_le hϑ
  have hrad := trq_radius_ge hr hF hM hXX₀ hA hx0' hε hϑ0 hϑ1 hnot
  have hκR : 0 < trqSCKappaRad P L ϑ M q := trqSCKappaRad_pos hϑ0 hM0
  refine ⟨fun i hi hs => ?_, ?_, fun i hi hs => ?_, fun j hj => ?_⟩
  · -- unsuccessful iterations do not move
    rw [hxi i hi.le, hxi (i + 1) hi]
    exact hr.toIsTRRun.eq_of_not_succ (fun l hl => hnot l (by omega))
      (not_le.1 ((hsucc i hi).not.1 hs))
  · -- Lemma 2.3.1 with the radius bound
    have h3 := hr.toIsTRRun.le_succ_count hnot (mul_pos hκR hεm0) hrad
    have hS' : (Finset.range e).filter succ =
        (Finset.range e).filter (fun j => P.η₁ ≤ Chapter12.trqRho F x s jk j) :=
      Finset.filter_congr fun i hi => hsucc i (Finset.mem_range.1 hi)
    have hcard := card_successSet_le (fun j => P.η₁ ≤ Chapter12.trqRho F x s jk j) e
    rw [hS']
    have hu := one_le_trqSCKappaUns (P := P)
    have := mul_le_mul_of_nonneg_right hcard (zero_le_one.trans hu)
    unfold trqSCKappaUns at hu this ⊢
    linarith
  · -- Lemma 12.2.4 with `κ_Δ ≥ κ_Δ(M)`
    have hk : ∀ l ≤ i, ¬ Chapter12.trqStop F P q ε ϑ x Δ d l := fun l hl => hnot l (by omega)
    have hdec := (Chapter12.lemma_12_2_4_anchored hr hF hXX₀ hA hx0' hε hϑ hϑ1 hk).2
      ((hsucc i hi).1 hs)
    obtain ⟨⟨hκ0, -⟩, -⟩ := Chapter12.lemma_12_2_3_anchored hr hF hXX₀ hA hx0' hϑ0 hϑ1
      (fun j hj => (hε j hj).1.le) (k := 0) (fun l hl => hnot l (by omega))
    have hκ := trqKappaDelta_ge hκ0 (hM _ (hA _ hx0' le_rfl)) hϑ0.le
    rw [hxi i hi.le, hxi (i + 1) hi]
    refine le_trans ?_ hdec
    have hκ' := trqSCKappaDelta_pos (P := P) (L := L) (q := q) hϑ0 hM0
    have hpow : (P.ς * trqSCKappaDelta P L ϑ M q) ^ (q + 1) ≤
        (P.ς * Chapter12.trqKappaDelta F P q L ϑ (x 0)) ^ (q + 1) :=
      pow_le_pow_left₀ (mul_pos P.ς_pos hκ').le (mul_le_mul_of_nonneg_left hκ P.ς_pos.le) _
    unfold trqSCKappaDecr
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hpow (by positivity)) (by positivity)) P.η₁_pos.le
  · -- the returned radii
    rw [hδo j hj]
    refine le_min hrad ?_
    calc trqSCKappaRad P L ϑ M q * Chapter12.finMin 1 ε q ≤ (P.γ₁ * ϑ) * 1 :=
          mul_le_mul trqSCKappaRad_le_γ₁ Chapter12.finMin_le_left hεm0.le
            (mul_pos P.γ₁_pos hϑ0).le
      _ ≤ ϑ := by nlinarith [P.γ₁_le_one]

end Call

/-! ### Phase 2 with TRq-SC calls: the INNER contract for every run -/

section Phase2

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ} {P : Optimization.TRqParams}
  {ϑ θ β : ℝ} {ε : ℕ → ℝ} {x₁ : ℝⁿ} {D : TPqpSeq n}

/-- **The INNER calls of Phase 2 of TPqp-GC are TRq-SC runs** ([cartis2022evaluation],
Algorithm 14.3.2, Step 1: `INNER(μ(·, t_k), X, q, x_k, β ‖r(x_k, t_k)‖ ε)` with INNER of
trust-region type): for every outer iteration `k ≥ 1` reached, the iterates, successful iterations
and output radii `δ_{k+1}` of the `k`-th call are those of a TRq-SC run on `μ(·, t_k)` with
threshold `ϑ` and tolerances `β ‖r(x_k, t_k)‖ ε_j` (`IsTRqSCCallOut`), cut at any iteration (by
any test of (14.3.32)). -/
def IsTRqSCPhase2Calls (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ)
    (P : Optimization.TRqParams) (ϑ θ β : ℝ) (ε : ℕ → ℝ) (D : TPqpSeq n) : Prop :=
  ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
    IsTRqSCCallOut (Constrained.targetMerit f c (D.t k)) X q P ϑ
      (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) (D.xi k) (D.e k)
      (D.succ k) (D.δ (k + 1))

/-- **The residual at the outer iterates is at least `θε₀`**: `‖r(x_k, t_k)‖ ≥ θε₀` for every
outer iteration `k ≥ 1` reached (`‖r(x_1, t_1)‖ = ε₀`, `‖r(x_{k+1}, t_{k+1})‖ = ε₀` after a
case-(a) iteration and `‖r(x_{k+1}, t_{k+1})‖ = ‖r(x_{k+1}, t_k)‖ ≥ θε₀` after a case-(b)
iteration). -/
theorem IsTPqpGCPhase2.le_targetResidual (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) :
    ∀ k, 1 ≤ k → D.Before f c X q θ ε k →
      θ * ε 0 ≤ Constrained.targetResidual f c (D.t k) (D.x k) := by
  have hθε : θ * ε 0 ≤ ε 0 := mul_le_of_le_one_left h.ε₀_pos.le h.θ_lt_one.le
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro _
    rw [h.t_one, h.x_one, Constrained.targetResidual_sub_sqrt h.ε₀_pos.le
      (h.norm_one_le.trans hθε)]
    exact hθε
  | succ k hk1 _ =>
    intro hK
    have T := h.isTargetSequence hK
    have hs : ¬ D.Stop f c X q θ ε k := hK k hk1 (Nat.lt_succ_self k)
    rcases IsTPqpGCPhase2.isKa_or_isKb_of_not_stop hs with ha | hb
    · rw [T.residual_succ_of_Ka h.θ_lt_one.le h.ε₀_pos.le hk1 (Nat.lt_succ_self k) ha]
      exact hθε
    · have hna : ¬ D.IsKa f c θ ε k := fun ha => absurd hb.1 (not_le.2 ha)
      rw [T.residual_succ_of_not_Ka hk1 (Nat.lt_succ_self k) hna]
      exact hb.1

/-- The tolerances `ε'_j = β ‖r(x_k, t_k)‖ ε_j` of the `k`-th call lie in `(0, 1]`, their minimum
is at most `ϑ` when `β ≤ ϑ`, and at least `βθ ε₀ ε_min`. -/
theorem IsTPqpGCPhase2.call_tol (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D) (hq : 1 ≤ q)
    (hβϑ : β ≤ ϑ) {k : ℕ} (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) :
    (∀ j ∈ Finset.Icc 1 q,
      β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j ∈ Ioc 0 1) ∧
    Chapter12.finMin 1 (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) q ≤
      ϑ ∧
    β * θ * (ε 0 * Chapter12.finMin 1 ε q) ≤
      Chapter12.finMin 1 (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) q := by
  set r := Constrained.targetResidual f c (D.t k) (D.x k) with hr
  have hlo := h.le_targetResidual k hk1 hk
  have hhi : r ≤ ε 0 := (h.isTargetSequence hk).residual_le h.θ_lt_one.le h.ε₀_pos.le hk1 le_rfl
  have hε₀ := h.ε₀_pos
  have hε₀1 : ε 0 ≤ 1 := h.ε_le_one 0 (by simp)
  have hβ := h.β_pos
  have hθ := h.θ_pos
  have hβ1 : β ≤ 1 := h.β_le_θ.trans h.θ_lt_one.le
  have hr0 : 0 < r := lt_of_lt_of_le (mul_pos hθ hε₀) hlo
  have hεj : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    ⟨h.ε_pos' hj, h.ε_le_one j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))⟩
  have hle : ∀ j ∈ Finset.Icc 1 q, β * r * ε j ≤ β := fun j hj => by
    have h1 : r * ε j ≤ 1 := by nlinarith [hεj j hj]
    nlinarith [hεj j hj]
  refine ⟨fun j hj => ⟨by have := (hεj j hj).1; positivity, (hle j hj).trans hβ1⟩, ?_, ?_⟩
  · exact (Chapter12.finMin_le (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)).trans
      ((hle 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)).trans hβϑ)
  · have hεm0 : 0 < Chapter12.finMin 1 ε q := Chapter12.finMin_pos one_pos fun j hj => (hεj j hj).1
    have hεm1 : Chapter12.finMin 1 ε q ≤ 1 := Chapter12.finMin_le_left
    refine Chapter12.le_finMin ?_ fun j hj => ?_
    · exact mul_le_one_aux (mul_le_one_aux hβ1 hθ.le h.θ_lt_one.le) (by positivity)
        (mul_le_one_aux hε₀1 hεm0.le hεm1)
    · have h1 : θ * ε 0 * Chapter12.finMin 1 ε q ≤ r * ε j :=
        mul_le_mul hlo (Chapter12.finMin_le hj) hεm0.le hr0.le
      nlinarith

/-- `|log(a b/D)| ≤ |log D| + |log a| + |log u| + |log v|` for `a, D > 0` and `0 < u v ≤ b ≤ 1`
with `u, v ∈ (0, 1]`. -/
theorem abs_log_mul_div_le {a b u v D : ℝ} (ha : 0 < a) (hu : 0 < u) (hv : 0 < v) (hu1 : u ≤ 1)
    (hv1 : v ≤ 1) (hb : u * v ≤ b) (hb1 : b ≤ 1) (hD : 0 < D) :
    |Real.log (a * b / D)| ≤ |Real.log D| + |Real.log a| + |Real.log u| + |Real.log v| := by
  have hb0 : 0 < b := lt_of_lt_of_le (mul_pos hu hv) hb
  rw [Real.log_div (mul_pos ha hb0).ne' hD.ne', Real.log_mul ha.ne' hb0.ne']
  have hlb : |Real.log b| ≤ |Real.log u| + |Real.log v| := by
    rw [abs_of_nonpos (Real.log_nonpos hb0.le hb1), abs_of_nonpos (Real.log_nonpos hu.le hu1),
      abs_of_nonpos (Real.log_nonpos hv.le hv1)]
    have := Real.log_le_log (mul_pos hu hv) hb
    rw [Real.log_mul hu.ne' hv.ne'] at this
    linarith
  calc |Real.log a + Real.log b - Real.log D| ≤ |Real.log a| + |Real.log b| + |Real.log D| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

/-- **Every Phase-2 run of TPqp-GC whose INNER calls are TRq-SC runs satisfies the INNER contract
keyed on INNER's own test** (`IsInnerPhaseRunStrong`; [cartis2022evaluation], Lemmas 14.2.2–14.2.3,
TRq-SC rows, applied to `μ(·, t_k)`), with the exponents `π_l = q + 1` (the decrease of
Lemma 12.2.4 is `κ_decr ε'_min^{q+1}`, `ε'_l = β ‖r(x_k, t_k)‖ ε_l`), the `t`-independent constants
`κ_decr = trqSCKappaDecr P L ϑ M q`, `κ_uns = trqSCKappaUns P`, the count constant
`κ_unc = κ_unc⁰ + |log(ε₀ ε_min)|/|log γ₂|` (`trqSCKappaUnc0`, `trqSCLogTerm`: every call restarts
from the radius `Δ₀` and the radii can shrink to `κ_ρ ε'_min ≥ κ_ρ βθ ε₀ ε_min`), and radii
`ρ_j = κ_ρ βθ ε₀ ε_min`, when every `μ(·, t)` satisfies anchored f.D1qL with constants `L` on
`𝓛_μ(t)` (for an open convex `X₀ ⊇ X`) with derivatives of orders `1, …, q` bounded by `M > 0`
there (Lemma 14.3.6 (ii) gives both under c.D1qLB.X and f.D1qLB.X), `1 ≤ q` and `β ≤ ϑ ≤ 1`. This
holds for every run, with calls cut by any test of (14.3.32). -/
theorem IsTRqSCPhase2Calls.isInnerPhaseRunStrong (h : IsTPqpGCPhase2 f c X q θ β ε x₁ D)
    (hcalls : IsTRqSCPhase2Calls f c X q P ϑ θ β ε D) (hq : 1 ≤ q) {X₀ : Set ℝⁿ}
    {L : ℕ → ℝ} {M : ℝ}
    (hμ : ∀ t, Chapter12.AssumptionD1pLAnchored (Constrained.targetMerit f c t) X₀
      (muSublevel f c X t) q L)
    (hμM : ∀ t, ∀ y ∈ muSublevel f c X t, Chapter12.finMax 0
      (fun i => ‖iteratedFDeriv ℝ i (Constrained.targetMerit f c t) y‖) q ≤ M) (hM0 : 0 < M)
    (hXX₀ : X ⊆ X₀) (hβϑ : β ≤ ϑ) (hϑ1 : ϑ ≤ 1) :
    IsInnerPhaseRunStrong f c X q θ β ε D (trqSCKappaDecr P L ϑ M q) (trqSCKappaUns P)
      (trqSCKappaUnc0 P L ϑ M q β θ + trqSCLogTerm q ε / |Real.log P.γ₂|)
      (fun _ => (q : ℝ) + 1)
      (fun _ => trqSCKappaRad P L ϑ M q * β * θ * (ε 0 * Chapter12.finMin 1 ε q)) := by
  have hϑ0 : 0 < ϑ := h.β_pos.trans_le hβϑ
  have hκR := trqSCKappaRad_pos (P := P) (L := L) (q := q) hϑ0 hM0
  have hC := fun k (hk1 : 1 ≤ k) (hk : D.Before f c X q θ ε k) =>
    (hcalls k hk1 hk).contract (hμ (D.t k)) (hμM (D.t k)) hM0 hXX₀
      (by rw [h.inner_zero k hk1 hk]; exact h.x_mem k hk1 hk) (h.call_sublevel hk1 hk)
      (h.call_tol hq hβϑ hk1 hk).1 (h.call_tol hq hβϑ hk1 hk).2.1 hϑ1
  refine ⟨fun k hk1 hk => ?_, fun k hk1 hk => (hC k hk1 hk).1,
    fun k hk1 hk i hi hs _ _ => ?_, fun k hk1 hk _ _ j hj => ?_⟩
  · -- the count, with the logarithm of the radius bound
    obtain ⟨htol, -, hlow⟩ := h.call_tol hq hβϑ hk1 hk
    have hε₀ := h.ε₀_pos
    have hε₀1 : ε 0 ≤ 1 := h.ε_le_one 0 (by simp)
    have hεm0 : 0 < Chapter12.finMin 1 ε q :=
      Chapter12.finMin_pos one_pos fun j hj => h.ε_pos' hj
    have hεm1 : Chapter12.finMin 1 ε q ≤ 1 := Chapter12.finMin_le_left
    have hβθ1 : β * θ ≤ 1 := by
      nlinarith [h.β_le_θ, h.θ_lt_one, h.β_pos, h.θ_pos]
    have hlog := abs_log_mul_div_le hκR (mul_pos h.β_pos h.θ_pos) (mul_pos hε₀ hεm0) hβθ1
      (by nlinarith) hlow Chapter12.finMin_le_left P.Δ₀_pos
    have hg : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
    have hcount := (hC k hk1 hk).2.1
    unfold TPqpSeq.succCount
    unfold trqSCKappaUnc0 trqSCLogTerm
    have : |Real.log (trqSCKappaRad P L ϑ M q * Chapter12.finMin 1
        (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) q / P.Δ₀)| /
          |Real.log P.γ₂| ≤
        (|Real.log P.Δ₀| + |Real.log (trqSCKappaRad P L ϑ M q)| + |Real.log (β * θ)|) /
          |Real.log P.γ₂| + |Real.log (ε 0 * Chapter12.finMin 1 ε q)| / |Real.log P.γ₂| := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hlog hg.le
    linarith
  · -- the decrease, at an order `l` attaining `ε'_min`
    obtain ⟨htol, -, -⟩ := h.call_tol hq hβϑ hk1 hk
    obtain ⟨l, hl, hmin⟩ := Chapter12.exists_finMin_eq hq fun j hj => (htol j hj).2
    refine ⟨l, hl, ?_⟩
    have hdec := (hC k hk1 hk).2.2.1 i hi hs
    rw [hmin] at hdec
    have e : ((q : ℝ) + 1) = ((q + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e, Real.rpow_natCast]
    exact hdec
  · -- the radii
    have hlow := (h.call_tol hq hβϑ hk1 hk).2.2
    calc trqSCKappaRad P L ϑ M q * β * θ * (ε 0 * Chapter12.finMin 1 ε q) =
          trqSCKappaRad P L ϑ M q * (β * θ * (ε 0 * Chapter12.finMin 1 ε q)) := by ring
      _ ≤ trqSCKappaRad P L ϑ M q * Chapter12.finMin 1
          (fun j => β * Constrained.targetResidual f c (D.t k) (D.x k) * ε j) q :=
        mul_le_mul_of_nonneg_left hlow hκR.le
      _ ≤ D.δ (k + 1) j := (hC k hk1 hk).2.2.2 j hj

end Phase2

/-! ### One INNER call of Phase 1 realized by TRq-SC -/

section Phase1Call

variable {F : ℝⁿ → ℝ} {X : Set ℝⁿ} {q : ℕ} {P : Optimization.TRqParams} {ϑ : ℝ} {ε : ℕ → ℝ}

/-- `(y, δ)` is the output of a TRq-SC call `INNER(F, X, q, x^S, ε)` with threshold `ϑ` whose run
uses `nF` evaluations of `F` and `nD` evaluations of its derivatives: a TRq-SC run
(`Chapter12.algorithm_12_2_1_feasible`) from `x^S` terminating first at `k_ε` with `x_{k_ε} = y`,
the returned radii `δ_j = min(Δ_{k_ε}, ϑ)` (which certify (14.3.19) at `y`,
`Chapter12.theorem_12_2_5_anchored`), `nF = k_ε + 1` (`Optimization.funEvalCount`) and `nD` the
number of successful iterations plus one (`Optimization.derivEvalCount`). -/
def IsTRqSCOutputCost (F : ℝⁿ → ℝ) (X : Set ℝⁿ) (q : ℕ) (P : Optimization.TRqParams) (ϑ : ℝ)
    (ε : ℕ → ℝ) (xS y : ℝⁿ) (δ : ℕ → ℝ) (nF nD : ℕ) : Prop :=
  ∃ (x s : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝⁿ) (kε : ℕ),
    Chapter12.algorithm_12_2_1_feasible F X P q ε ϑ x s Δ jk d ∧
    Optimization.IsFirstHit (Chapter12.trqStop F P q ε ϑ x Δ d) kε ∧
    x 0 = xS ∧ x kε = y ∧ (∀ j ∈ Finset.Icc 1 q, δ j = min (Δ kε) ϑ) ∧
    nF = Optimization.funEvalCount kε ∧
    nD = Optimization.derivEvalCount (fun k => P.η₁ ≤ Chapter12.trqRho F x s jk k) kε

/-- `|log b| ≤ |log u| + |log v|` for `0 < u v ≤ b ≤ 1` with `u, v ∈ (0, 1]`. -/
theorem abs_log_le_of_mul_le {b u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hu1 : u ≤ 1) (hv1 : v ≤ 1)
    (hb : u * v ≤ b) (hb1 : b ≤ 1) : |Real.log b| ≤ |Real.log u| + |Real.log v| := by
  have hb0 : 0 < b := lt_of_lt_of_le (mul_pos hu hv) hb
  rw [abs_of_nonpos (Real.log_nonpos hb0.le hb1), abs_of_nonpos (Real.log_nonpos hu.le hu1),
    abs_of_nonpos (Real.log_nonpos hv.le hv1)]
  have := Real.log_le_log (mul_pos hu hv) hb
  rw [Real.log_mul hu.ne' hv.ne'] at this
  linarith

/-- **The cost of one TRq-SC call** ([cartis2022evaluation], Theorem 12.2.5 with a feasible set,
the TRq-SC row of Theorem 14.2.4, with `κ_Δ ≥ κ_Δ(M)`): under anchored f.D1qL on a set `S`
containing the sublevel set at `x^S`, derivatives bounded by `M > 0` on `S`, `F ≥ 0` on `X`,
`ε ∈ (0, 1]^q` and `ε_min ≤ ϑ ≤ 1`, the call uses at most
`κ^A F(x^S)/ε_min^{q+1} + κ^B |log ε_min| + κ^C` evaluations of `F` and
`κ^S F(x^S)/ε_min^{q+1} + 1` derivative evaluations, with constants independent of `x^S`. -/
theorem IsTRqSCOutputCost.cost_le {X₀ S : Set ℝⁿ} {L : ℕ → ℝ} {M : ℝ} {xS y : ℝⁿ}
    {δ : ℕ → ℝ} {nF nD : ℕ} (hF : Chapter12.AssumptionD1pLAnchored F X₀ S q L)
    (hM : ∀ z ∈ S, Chapter12.finMax 0 (fun i => ‖iteratedFDeriv ℝ i F z‖) q ≤ M) (hM0 : 0 < M)
    (hXX₀ : X ⊆ X₀) (hb : ∀ z ∈ X, 0 ≤ F z) (h : IsTRqSCOutputCost F X q P ϑ ε xS y δ nF nD)
    (hxS : xS ∈ X) (hS : ∀ z ∈ X, F z ≤ F xS → z ∈ S)
    (hε : ∀ j ∈ Finset.Icc 1 q, ε j ∈ Ioc 0 1) (hϑ : Chapter12.finMin 1 ε q ≤ ϑ)
    (hϑ1 : ϑ ≤ 1) :
    (nF : ℝ) ≤ trqSCKappaA P L ϑ M q * F xS / Chapter12.finMin 1 ε q ^ (q + 1) +
        Chapter12.kappaBTRq P * |Real.log (Chapter12.finMin 1 ε q)| + trqSCKappaC P L ϑ M q ∧
      (nD : ℝ) ≤ trqSCKappaS P L ϑ M q * F xS / Chapter12.finMin 1 ε q ^ (q + 1) + 1 := by
  obtain ⟨x, s, Δ, jk, d, kε, hr, hhit, hx0, -, -, hnF, hnD⟩ := h
  subst hx0 hnF hnD
  obtain ⟨kε', hhit', -, -, -, hF', hD'⟩ :=
    Chapter12.theorem_12_2_5_anchored (flow := 0) hb hF hXX₀ hS hxS hε hϑ hϑ1 hr
  rw [hhit'.unique hhit, sub_zero] at hF' hD'
  have hεm0 : 0 < Chapter12.finMin 1 ε q :=
    Chapter12.finMin_pos one_pos fun j hj => (hε j hj).1
  have hϑ0 : 0 < ϑ := hεm0.trans_le hϑ
  have hF0 : 0 ≤ F (x 0) := hb _ hxS
  have hg : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
  have hB0 : 0 ≤ Chapter12.kappaBTRq P := by unfold Chapter12.kappaBTRq; positivity
  have hA0 := trqSCKappaA_nonneg (P := P) (L := L) (q := q) hϑ0 hM0
  have hS0 := trqSCKappaS_nonneg (P := P) (L := L) (q := q) hϑ0 hM0
  have hC1 := one_le_trqSCKappaC (P := P) (L := L) (ϑ := ϑ) (M := M) (q := q)
  have hpow : 0 < Chapter12.finMin 1 ε q ^ (q + 1) := pow_pos hεm0 _
  have hAt : 0 ≤ trqSCKappaA P L ϑ M q * F (x 0) / Chapter12.finMin 1 ε q ^ (q + 1) := by
    positivity
  have hSt : 0 ≤ trqSCKappaS P L ϑ M q * F (x 0) / Chapter12.finMin 1 ε q ^ (q + 1) := by
    positivity
  have hlog0 : 0 ≤ Chapter12.kappaBTRq P * |Real.log (Chapter12.finMin 1 ε q)| := by positivity
  rcases Nat.eq_zero_or_pos kε with h0 | hpos
  · subst h0
    have e1 : (Optimization.funEvalCount 0 : ℝ) = 1 := by simp [Optimization.funEvalCount]
    have e2 : (Optimization.derivEvalCount
        (fun k => P.η₁ ≤ Chapter12.trqRho F x s jk k) 0 : ℝ) = 1 := by
      simp [Optimization.derivEvalCount]
    rw [e1, e2]
    exact ⟨by linarith, by linarith⟩
  · -- `κ_Δ ≥ κ_Δ(M)` at `x₀`
    obtain ⟨⟨hκ0, hκ1⟩, -⟩ := Chapter12.lemma_12_2_3_anchored hr hF hXX₀ hS hxS hϑ0 hϑ1
      (fun j hj => (hε j hj).1.le) (k := 0) (fun i hi => hhit.2 i (by omega))
    have hκ := trqKappaDelta_ge hκ0 (hM _ (hS _ hxS le_rfl)) hϑ0.le
    have hκ' := trqSCKappaDelta_pos (P := P) (L := L) (q := q) hϑ0 hM0
    have hp1 : 0 < P.ς * trqSCKappaDelta P L ϑ M q := mul_pos P.ς_pos hκ'
    have hpow' : (P.ς * trqSCKappaDelta P L ϑ M q) ^ (q + 1) ≤
        (P.ς * Chapter12.trqKappaDelta F P q L ϑ (x 0)) ^ (q + 1) :=
      pow_le_pow_left₀ hp1.le (mul_le_mul_of_nonneg_left hκ P.ς_pos.le) _
    have hSle : Chapter12.kappaSTRq F P q L ϑ (x 0) ≤ trqSCKappaS P L ϑ M q := by
      unfold Chapter12.kappaSTRq trqSCKappaS
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (mul_pos P.η₁_pos (pow_pos hp1 _)) (mul_le_mul_of_nonneg_left hpow' P.η₁_pos.le)
    have hAle : Chapter12.kappaATRq F P q L ϑ (x 0) ≤ trqSCKappaA P L ϑ M q := by
      unfold Chapter12.kappaATRq trqSCKappaA
      exact mul_le_mul_of_nonneg_right hSle (zero_le_one.trans one_le_trqSCKappaUns)
    have hCle : Chapter12.kappaCTRq F P q L ϑ (x 0) ≤ trqSCKappaC P L ϑ M q := by
      unfold Chapter12.kappaCTRq trqSCKappaC
      have hlogκ : |Real.log (Chapter12.trqKappaDelta F P q L ϑ (x 0))| ≤
          |Real.log (trqSCKappaDelta P L ϑ M q)| := by
        rw [abs_of_nonpos (Real.log_nonpos hκ0.le hκ1.le),
          abs_of_nonpos (Real.log_nonpos hκ'.le (hκ.trans hκ1.le))]
        exact neg_le_neg (Real.log_le_log hκ' hκ)
      have : |Real.log (P.ς * Chapter12.trqKappaDelta F P q L ϑ (x 0) / P.Δ₀)| ≤
          |Real.log P.ς| + |Real.log (trqSCKappaDelta P L ϑ M q)| + |Real.log P.Δ₀| := by
        rw [Real.log_div (mul_pos P.ς_pos hκ0).ne' P.Δ₀_pos.ne',
          Real.log_mul P.ς_pos.ne' hκ0.ne']
        calc _ ≤ |Real.log P.ς + Real.log (Chapter12.trqKappaDelta F P q L ϑ (x 0))| +
              |Real.log P.Δ₀| := abs_sub _ _
          _ ≤ |Real.log P.ς| + |Real.log (Chapter12.trqKappaDelta F P q L ϑ (x 0))| +
              |Real.log P.Δ₀| := add_le_add (abs_add_le _ _) le_rfl
          _ ≤ _ := by linarith
      linarith [div_le_div_of_nonneg_right this hg.le]
    have h1 : Chapter12.kappaATRq F P q L ϑ (x 0) * F (x 0) / Chapter12.finMin 1 ε q ^ (q + 1) ≤
        trqSCKappaA P L ϑ M q * F (x 0) / Chapter12.finMin 1 ε q ^ (q + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAle hF0) hpow.le
    have h2 : Chapter12.kappaSTRq F P q L ϑ (x 0) * F (x 0) / Chapter12.finMin 1 ε q ^ (q + 1) ≤
        trqSCKappaS P L ϑ M q * F (x 0) / Chapter12.finMin 1 ε q ^ (q + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hSle hF0) hpow.le
    exact ⟨by linarith, by linarith⟩

/-- `κ gap/ε_min^{q+1} ≤ κ gap max_j ε_j^{-(q+1)}` (`innerEvalBound` with the exponents
`π_j = q + 1`), for `κ, gap ≥ 0` and `ε ∈ (0, 1]^q`, `q ≥ 1`. -/
theorem le_innerEvalBound_succ {κ gap : ℝ} (hκ : 0 ≤ κ) (hgap : 0 ≤ gap) (hq : 1 ≤ q)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1) :
    κ * gap / Chapter12.finMin 1 ε q ^ (q + 1) ≤
      innerEvalBound κ (fun _ => (q : ℝ) + 1) q gap ε := by
  obtain ⟨l, hl, hmin⟩ := Chapter12.exists_finMin_eq hq fun j hj => (hε j hj).2
  unfold innerEvalBound
  rw [hmin, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hκ hgap)
  have e : (ε l ^ (q + 1))⁻¹ = ε l ^ (-((q : ℝ) + 1)) := by
    rw [Real.rpow_neg (hε l hl).1.le, show ((q : ℝ) + 1) = ((q + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [e]
  exact le_ciSup (f := fun j : Finset.Icc 1 q => ε j ^ (-((q : ℝ) + 1)))
    (Set.finite_range _).bddAbove ⟨l, hl⟩

end Phase1Call

/-! ### TPqp-GC runs with a trust-region INNER in both phases -/

section Run

/-- **A run of TPqp-GC with INNER = TRq-SC in both phases** ([cartis2022evaluation],
Algorithm 14.3.2 with INNER of trust-region type): a run (`algorithm_14_3_2`) whose Phase-1 INNER
calls (14.3.23) `x_k = INNER(ν, X, q, x_{k-1}, β₁ ‖c(x_{k-1})‖ (θε₀, ε_1, …, ε_q))` are TRq-SC
runs on `ν` with threshold `ϑ` that use `nF₁ k` evaluations of `c` and `nD₁ k` of its derivatives
(`IsTRqSCOutputCost`), and whose Phase-2 INNER calls (if Phase 2 is entered) are TRq-SC runs on
`μ(·, t_k)` with threshold `ϑ` and their output radii, cut at any iteration
(`IsTRqSCPhase2Calls`). -/
structure IsTPqpGCTRqSCRun (f : ℝⁿ → ℝ) (c : ℝⁿ → ℝᵐ) (X : Set ℝⁿ) (q : ℕ)
    (P : Optimization.TRqParams) (ϑ θ β₁ β : ℝ) (ε : ℕ → ℝ) (x₀ : ℝⁿ) (xP : ℕ → ℝⁿ)
    (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ) : Prop where
  /-- The TPqp-GC run. -/
  run : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D
  /-- The Phase-1 INNER calls are TRq-SC runs with their evaluation counts. -/
  phase1 : ∀ k, 1 ≤ k → k ≤ k₁ → IsTRqSCOutputCost (phi2 c) X q P ϑ
    (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) (xP (k - 1)) (xP k) (δP k) (nF₁ k)
      (nD₁ k)
  /-- The Phase-2 INNER calls are TRq-SC runs with their output radii. -/
  phase2 : ‖c (xP k₁)‖ ≤ θ * ε 0 → IsTRqSCPhase2Calls f c X q P ϑ θ β ε D

end Run

/-! ### Theorem 14.3.9 with a trust-region INNER -/

section Theorem1439

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {X : Set ℝⁿ} {q : ℕ}

/-- c.D1qLB.X gives, through Lemma 14.3.6 (i), anchored f.D1qL for `ν` on `𝓛_ν(x₀)` with the
constants `L^A_j + L^B_j ‖c(x₀)‖` and the bound `max(1, max_j (B^A_j + B^B_j ‖c(x₀)‖))` on the
derivatives of orders `1, …, q` there. -/
theorem exists_nu_trq {X₀ : Set ℝⁿ} {Lc Bc : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ q Lc Bc) :
    ∃ LA LB BA BB : ℕ → ℝ, ∀ x₀ : ℝⁿ,
      Chapter12.AssumptionD1pLAnchored (phi2 c) X₀ (nuSublevel c X x₀) q
        (fun j => LA j + LB j * ‖c x₀‖) ∧
      ∀ y ∈ nuSublevel c X x₀, Chapter12.finMax 0
        (fun i => ‖iteratedFDeriv ℝ i (phi2 c) y‖) q ≤
          Chapter12.finMax 1 (fun j => BA j + BB j * ‖c x₀‖) q := by
  obtain ⟨LA, LB, BA, BB, h1, hν⟩ := lemma_14_3_6_i hc
  refine ⟨LA, LB, BA, BB, fun x₀ => ⟨⟨hc.isOpen, hc.convex, fun x hx => hc.subset hx.1,
    fun y hy => (hν x₀).1.contDiffAt (hc.isOpen.mem_nhds hy), fun j _ => ?_,
    fun j hj => ((hν x₀).2 j hj).1⟩, fun y hy => ?_⟩⟩
  · have := (h1 j).1
    have := (h1 j).2.1
    have := norm_nonneg (c x₀)
    nlinarith
  · exact Chapter12.finMax_le (zero_le_one.trans Chapter12.le_finMax_left) fun i hi =>
      (((hν x₀).2 i hi).2 y hy).trans
        (Chapter12.le_finMax (u := fun j => BA j + BB j * ‖c x₀‖) hi)

/-- c.D1qLB.X and f.D1qLB.X give, through Lemma 14.3.6 (ii), anchored f.D1qL for every `μ(·, t)`
on `𝓛_μ(t)` with constants `L_μ` and the bound `max(1, max_j B_{μ,j})` on the derivatives of
orders `1, …, q` there, independent of `t`. -/
theorem exists_mu_trq {X₀ : Set ℝⁿ} {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ q Lc Bc) (hf : AssumptionD1pLBX f X X₀ q Lf Bf) :
    ∃ Lμ Bμ : ℕ → ℝ, ∀ t : ℝ,
      Chapter12.AssumptionD1pLAnchored (Constrained.targetMerit f c t) X₀ (muSublevel f c X t)
        q Lμ ∧
      ∀ y ∈ muSublevel f c X t, Chapter12.finMax 0
        (fun i => ‖iteratedFDeriv ℝ i (Constrained.targetMerit f c t) y‖) q ≤
          Chapter12.finMax 1 Bμ q := by
  obtain ⟨Lμ, Bμ, h2, hμ⟩ := lemma_14_3_6_ii hc hf
  refine ⟨Lμ, Bμ, fun t => ⟨⟨hc.isOpen, hc.convex, fun x hx => hc.subset hx.1,
    fun y hy => (hμ t).1.contDiffAt (hc.isOpen.mem_nhds hy), fun j _ => (h2 j).1,
    fun j hj => ((hμ t).2 j hj).1⟩, fun y hy => ?_⟩⟩
  exact Chapter12.finMax_le (zero_le_one.trans Chapter12.le_finMax_left) fun i hi =>
    (((hμ t).2 i hi).2 y hy).trans (Chapter12.le_finMax (u := Bμ) hi)

/-- The bad-iteration term with the radii `ρ'_j = ε₀ ε_min` is within the order with the
exponents `q + 1`: `(ε₀ ε_j (ε₀ ε_min)^{j-1})^{-1} ≤ ε₀^{-q} ε_min^{-(q+1)}` for `j ∈ [1 : q]`
and tolerances in `(0, 1]`. -/
theorem inv_bad_le_trq {ε₀ εj εm : ℝ} (h0 : 0 < ε₀) (h01 : ε₀ ≤ 1) (hm0 : 0 < εm) (hm1 : εm ≤ 1)
    (hmj : εm ≤ εj) {j : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ q) :
    (ε₀ * εj * (ε₀ * εm) ^ (j - 1))⁻¹ ≤ ε₀ ^ (1 - ((q : ℝ) + 1)) * εm ^ (-((q : ℝ) + 1)) := by
  have hp : 0 < ε₀ * εm := mul_pos h0 hm0
  have hp1 : ε₀ * εm ≤ 1 := mul_le_one_aux h01 hm0.le hm1
  have h1 : (ε₀ * εm) ^ j ≤ ε₀ * εj * (ε₀ * εm) ^ (j - 1) := by
    rw [← mul_pow_sub_one (by omega : j ≠ 0) (ε₀ * εm)]
    gcongr
  have h2 : (ε₀ * εm) ^ q ≤ (ε₀ * εm) ^ j := pow_le_pow_of_le_one hp.le hp1 hjq
  calc (ε₀ * εj * (ε₀ * εm) ^ (j - 1))⁻¹ ≤ ((ε₀ * εm) ^ j)⁻¹ := inv_anti₀ (pow_pos hp _) h1
    _ ≤ ((ε₀ * εm) ^ q)⁻¹ := inv_anti₀ (pow_pos hp _) h2
    _ ≤ _ := inv_pow_le_term_succ h0 hm0 hm1 q

/-- The number of Phase-1 iterations of TPqp-GC is at most `1 + ‖c(x₀)‖/(θ |log β₁|) ε₀^{-1}`
(Theorem 14.3.3, `ceil_log_div_le`). -/
theorem phase1_iter_le {θ β₁ β : ℝ} {ε : ℕ → ℝ} {x₀ : ℝⁿ} {xP : ℕ → ℝⁿ} {δP : ℕ → ℕ → ℝ}
    {k₁ : ℕ} {D : TPqpSeq n} (h : algorithm_14_3_2 f c X q θ β₁ β ε x₀ xP δP k₁ D)
    (hθ0 : 0 < θ) : (k₁ : ℝ) ≤ 1 + ‖c x₀‖ / (θ * |Real.log β₁|) * (ε 0)⁻¹ := by
  have hε₀ : 0 < ε 0 := by
    have := h.phase1.ε_pos 0 (by simp)
    rw [phase1Tol_zero] at this
    exact pos_of_mul_pos_right this hθ0.le
  obtain ⟨⟨kmax, hhit, hkmax, -⟩, -⟩ := theorem_14_3_3 h.phase1
  rw [hhit.unique h.phase1_end, phase1Tol_zero, h.start] at hkmax
  have h1 : (k₁ : ℝ) ≤ 1 + ‖c x₀‖ / (θ * ε 0 * |Real.log β₁|) :=
    (Nat.cast_le.2 hkmax).trans (ceil_log_div_le (mul_pos hθ0 hε₀) (norm_nonneg _)
      h.phase1.β_pos h.phase1.β_lt_one)
  have h2 : ‖c x₀‖ / (θ * ε 0 * |Real.log β₁|) = ‖c x₀‖ / (θ * |Real.log β₁|) * (ε 0)⁻¹ := by
    field_simp
  rwa [h2] at h1

/-- **The Phase-1 cost contract of TRq-SC calls** ([cartis2022evaluation], (14.3.20)–(14.3.21)
in the additive form of `lemma_14_3_7_add`, with the exponents `π_j = q + 1`): under anchored
f.D1qL for `ν` on `𝓛_ν(x₀)` (constants `L_ν`, derivatives bounded by `M_ν > 0`),
`ϑ ≤ 1` and `β₁ ‖c(x₀)‖ ≤ ϑ`, the `k`-th Phase-1 call of a TPqp-GC run with TRq-SC calls uses at
most `κ^A ν(x_{k-1}) max_j ε'_j^{-(q+1)} + κ^B (|log(β₁θ)| + |log(ε₀ ε_min)|) + κ^C` evaluations
of `c` and `κ^S ν(x_{k-1}) max_j ε'_j^{-(q+1)} + 1` derivative evaluations
(`IsTRqSCOutputCost.cost_le`, `‖c(x_{k-1})‖ > θε₀`). -/
theorem phase1_call_cost_trq {P : Optimization.TRqParams} {ϑ θ β₁ β : ℝ} {ε : ℕ → ℝ}
    {x₀ : ℝⁿ} {xP : ℕ → ℝⁿ} {δP : ℕ → ℕ → ℝ} {k₁ : ℕ} {D : TPqpSeq n} {nF₁ nD₁ : ℕ → ℕ}
    (hR : IsTPqpGCTRqSCRun f c X q P ϑ θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁) (hq : 1 ≤ q)
    {X₀ : Set ℝⁿ} {Lν : ℕ → ℝ} {Mν : ℝ}
    (hν : Chapter12.AssumptionD1pLAnchored (phi2 c) X₀ (nuSublevel c X x₀) q Lν)
    (hνM : ∀ y ∈ nuSublevel c X x₀,
      Chapter12.finMax 0 (fun i => ‖iteratedFDeriv ℝ i (phi2 c) y‖) q ≤ Mν) (hMν0 : 0 < Mν)
    (hXX₀ : X ⊆ X₀) (hϑ1 : ϑ ≤ 1) (hβ₁ϑ : β₁ * ‖c x₀‖ ≤ ϑ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) :
    ∀ k ∈ Finset.Icc 1 k₁,
      (nF₁ k : ℝ) ≤ innerEvalBound (trqSCKappaA P Lν ϑ Mν q) (fun _ => (q : ℝ) + 1) q
        (phi2 c (xP (k - 1))) (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) +
          (Chapter12.kappaBTRq P * (|Real.log (β₁ * θ)| + trqSCLogTerm q ε) +
            trqSCKappaC P Lν ϑ Mν q) ∧
      (nD₁ k : ℝ) ≤ innerEvalBound (trqSCKappaS P Lν ϑ Mν q) (fun _ => (q : ℝ) + 1) q
        (phi2 c (xP (k - 1))) (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) + 1 := by
  have h := hR.run
  have hε₀ := hε 0 (by simp)
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  have hεm0 : 0 < Chapter12.finMin 1 ε q := Chapter12.finMin_pos one_pos fun j hj => (hεI j hj).1
  have hεm1 : Chapter12.finMin 1 ε q ≤ 1 := Chapter12.finMin_le_left
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  have hβ₁0 := h.phase1.β_pos
  have hβ₁1 := h.phase1.β_lt_one
  intro k hk
  obtain ⟨hk1, hkk⟩ := Finset.mem_Icc.1 hk
  have hmem : xP (k - 1) ∈ X := by
    rcases Nat.eq_zero_or_pos (k - 1) with h0 | hpos
    · rw [h0]; exact h.phase1.mem_zero
    · exact h.phase1.mem (k - 1) hpos fun i hi => h.phase1_end.2 i (by omega)
  have hck : ‖c (xP (k - 1))‖ ≤ ‖c x₀‖ := by
    have := h.phase1.norm_le_pow_mul (Nat.zero_le (k - 1)) fun l hl =>
      h.phase1_end.2 l (by omega)
    rw [h.start] at this
    exact this.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hβ₁0.le hβ₁1.le))
  have hlo : θ * ε 0 < ‖c (xP (k - 1))‖ := by
    have := h.phase1_end.2 (k - 1) (by omega)
    simp only [lenStop, not_or, not_le, phase1Tol_zero] at this
    exact this.1
  have hck0 := hck
  obtain ⟨r, hr⟩ : ∃ x, x = ‖c (xP (k - 1))‖ := ⟨_, rfl⟩
  rw [← hr] at hck hlo ⊢
  have hr0 : 0 < r := (mul_pos hθ0 hε₀.1).trans hlo
  have hϑ0 : 0 < ϑ := lt_of_lt_of_le (mul_pos hβ₁0 (hr0.trans_le hck)) hβ₁ϑ
  obtain ⟨ε', hε'⟩ : ∃ e : ℕ → ℝ, e = fun j => β₁ * r * phase1Tol θ ε j := ⟨_, rfl⟩
  rw [← hε']
  have hε'j : ∀ j ∈ Finset.Icc 1 q, ε' j = β₁ * r * ε j := fun j hj => by
    simp only [hε']
    rw [phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega)]
  have hle : ∀ j ∈ Finset.Icc 1 q, ε' j ≤ ϑ := fun j hj => by
    rw [hε'j j hj]
    calc β₁ * r * ε j ≤ β₁ * ‖c x₀‖ * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hck hβ₁0.le) (hεI j hj).2 (hεI j hj).1.le
            (mul_nonneg hβ₁0.le (norm_nonneg _))
      _ ≤ ϑ := by rw [mul_one]; exact hβ₁ϑ
  have htol : ∀ j ∈ Finset.Icc 1 q, ε' j ∈ Ioc 0 1 := fun j hj =>
    ⟨by rw [hε'j j hj]; have := (hεI j hj).1; positivity, (hle j hj).trans hϑ1⟩
  have hϑ' : Chapter12.finMin 1 ε' q ≤ ϑ := (Chapter12.finMin_le h1q).trans (hle 1 h1q)
  have hcall := (hR.phase1 k hk1 hkk)
  rw [← hr, ← hε'] at hcall
  have hcall' := hcall.cost_le hν hνM hMν0 hXX₀ (fun y _ => by rw [phi2_apply]; positivity) hmem
    (fun y hy hyk => ⟨hy, (norm_le_of_phi2_le hyk).trans hck0⟩) htol hϑ' hϑ1
  -- the logarithm of `ε'_min`
  have hεm' : β₁ * θ * (ε 0 * Chapter12.finMin 1 ε q) ≤ Chapter12.finMin 1 ε' q := by
    refine Chapter12.le_finMin ?_ fun j hj => ?_
    · exact mul_le_one_aux (mul_le_one_aux hβ₁1.le hθ0.le hθ1.le) (mul_pos hε₀.1 hεm0).le
        (mul_le_one_aux hε₀.2 hεm0.le hεm1)
    · rw [hε'j j hj]
      have : θ * ε 0 * Chapter12.finMin 1 ε q ≤ r * ε j :=
        mul_le_mul hlo.le (Chapter12.finMin_le hj) hεm0.le hr0.le
      calc β₁ * θ * (ε 0 * Chapter12.finMin 1 ε q) =
            β₁ * (θ * ε 0 * Chapter12.finMin 1 ε q) := by ring
        _ ≤ β₁ * (r * ε j) := mul_le_mul_of_nonneg_left this hβ₁0.le
        _ = β₁ * r * ε j := by ring
  have hlog : |Real.log (Chapter12.finMin 1 ε' q)| ≤
      |Real.log (β₁ * θ)| + trqSCLogTerm q ε :=
    abs_log_le_of_mul_le (mul_pos hβ₁0 hθ0) (mul_pos hε₀.1 hεm0)
      (mul_le_one_aux hβ₁1.le hθ0.le hθ1.le) (mul_le_one_aux hε₀.2 hεm0.le hεm1) hεm'
      Chapter12.finMin_le_left
  have hε'I : ∀ j ∈ Finset.Icc 1 q, 0 < ε' j ∧ ε' j ≤ 1 := fun j hj => htol j hj
  have hν0 : 0 ≤ phi2 c (xP (k - 1)) := by rw [phi2_apply]; positivity
  have hB0 : 0 ≤ Chapter12.kappaBTRq P := by unfold Chapter12.kappaBTRq; positivity
  refine ⟨hcall'.1.trans ?_, hcall'.2.trans ?_⟩
  · have h1 := le_innerEvalBound_succ
      (trqSCKappaA_nonneg (P := P) (L := Lν) (q := q) hϑ0 hMν0) hν0 hq hε'I
    have h2 := mul_le_mul_of_nonneg_left hlog hB0
    linarith
  · have := le_innerEvalBound_succ
      (trqSCKappaS_nonneg (P := P) (L := Lν) (q := q) hϑ0 hMν0) hν0 hq hε'I
    linarith

/-- **Theorem 14.3.9** of [cartis2022evaluation] (complexity of TPqp-GC) **for every run with a
trust-region INNER** (TRq-SC, Algorithm 12.2.1 with a feasible set, threshold `ϑ`, in both
phases), under c.D1qLB.X and f.D1qLB.X (on an open convex `X₀ ⊇ X`) and f.B.Fb on `ℱ_{β_F}`,
with `q ≥ 1`. For TRq parameters `P`, `ϑ ≤ 1`, `θ ∈ (0, 1)`, `0 < β ≤ ϑ`, `β₁` and a starting
point `x₀` with `β₁ ‖c(x₀)‖ ≤ ϑ`, there are constants `κ_F, κ_L, κ_D ≥ 0` such that for all
tolerances `ε ∈ (0, 1]^{q+1}` with `ε₀ ≤ β_F` and every TPqp-GC run whose INNER calls are TRq-SC
runs (`IsTPqpGCTRqSCRun`; Phase-2 calls may be cut by any test of (14.3.32); such runs exist,
`exists_isTPqpGCTRqSCRun`):
* if Phase 1 ends with `‖c(x₁)‖ > θε₀`, it uses at most `(κ_F + κ_L Λ) O_F` evaluations of `c`
  and `κ_D O_D` derivative evaluations;
* otherwise Phase 2 terminates at some `k_ε`, and both phases together use at most
  `(κ_F + κ_L Λ) O_F` evaluations of `(f, c)` and `κ_D O_D` derivative evaluations,

where `π_j = q + 1` for every `j` (the exponent of Lemma 12.2.4, the TRq-SC row of Lemma 14.2.2 as
proved in `Chapter14.Section02`), `O_F = max[ε₀^{-1}, max_j ε₀^{-q} ε_j^{-(q+1)}]`
(`tpqpOrderF`), `O_D = max_j ε₀^{-q} ε_j^{-(q+1)}` (`tpqpOrderD`) and
`Λ = |log(ε₀ ε_min)|` (`trqSCLogTerm`).

Deviations from the printed statement: (14.2.12) prints `π_j = j + 1` for TRq-SC; the decrease
proved for TRq (Lemma 12.2.4) is `κ ε_min^{q+1}`, which gives `π_j = q + 1`, the order of the TRq-SC
row of the book's Theorem 14.2.4 (the row `j + 1` is false per iteration for `q = 2` with `κ_decr`
depending only on the algorithm parameters and the f.D1qLaB.X constants,
`lemma_14_2_2_trq_printed_false_uniform`, and for whole runs for every `q ≥ 2`,
`theorem_14_3_9_trq_printed_false`); the two agree for `q = 1`
(`theorem_14_3_9_trq_one`). The function-evaluation bound carries the factor `1 + Λ`,
which is needed for `q = 1` (`theorem_14_3_9_trq_log_necessary`): every INNER call restarts from the
radius `Δ₀`, and its unsuccessful iterations are bounded only by `log(Δ₀/(κ_ρ ε'_min))` (Lemma 2.3.1
with Lemma 12.2.3), `ε'_min ≥ βθ ε₀ ε_min`, which the counting of Lemma 14.3.8 multiplies by the
number of outer iterations; the derivative bound has no such factor. The book's f.D1qLB.Fb is not
defined in the book; f.D1qLB.X (f.D1pLB.X with `q`) is used.
-/
theorem theorem_14_3_9_trq (hq : 1 ≤ q) {X₀ : Set ℝⁿ} {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ q Lc Bc) (hf : AssumptionD1pLBX f X X₀ q Lf Bf)
    {βF flow fup : ℝ} (hB : Chapter07.AssumptionBFb f c X βF flow fup)
    (P : Optimization.TRqParams) {ϑ θ β β₁ : ℝ} (hϑ1 : ϑ ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ0 : 0 < β) (hβϑ : β ≤ ϑ) (x₀ : ℝⁿ) (hβ₁ϑ : β₁ * ‖c x₀‖ ≤ ϑ) :
    ∃ κF κL κD : ℝ, 0 ≤ κF ∧ 0 ≤ κL ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun f c X q P ϑ θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ →
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
            (κF + κL * trqSCLogTerm q ε) * tpqpOrderF (fun _ => (q : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * tpqpOrderD (fun _ => (q : ℝ) + 1) q ε) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c X q θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            (κF + κL * trqSCLogTerm q ε) * tpqpOrderF (fun _ => (q : ℝ) + 1) q ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (fun _ => (q : ℝ) + 1) q ε) := by
  have hϑ0 : 0 < ϑ := hβ0.trans_le hβϑ
  obtain ⟨LA, LB, BA, BB, hν⟩ := exists_nu_trq hc
  obtain ⟨Lμ, Bμ, hμ⟩ := exists_mu_trq hc hf
  have hMν0 : 0 < Chapter12.finMax 1 (fun j => BA j + BB j * ‖c x₀‖) q := finMax_one_pos
  have hMμ0 : 0 < Chapter12.finMax 1 Bμ q := finMax_one_pos
  have hg : 0 < |Real.log P.γ₂| := abs_pos.2 (Real.log_neg P.γ₂_pos P.γ₂_lt_one).ne
  -- Phase 2 constants
  have hκ : 0 < trqSCKappaDecr P Lμ ϑ (Chapter12.finMax 1 Bμ q) q :=
    trqSCKappaDecr_pos hϑ0 hMμ0
  have hκρ : 0 < trqSCKappaRad P Lμ ϑ (Chapter12.finMax 1 Bμ q) q * β * θ := by
    have := trqSCKappaRad_pos (P := P) (L := Lμ) (q := q) hϑ0 hMμ0
    positivity
  obtain ⟨CF, CU, CD, hCF, hCU, hCD, hord⟩ :=
    IsTPqpGCPhase2.exists_const_order_of_strong_unc (f := f) (c := c) (X := X) (θ := θ)
      (β := β) hq (πmax := (q : ℝ) + 1) hκ (zero_le_one.trans one_le_trqSCKappaUns) hκρ
      (finMax_one_pos (B := Bf)) (abs_nonneg (fup - flow + 1)) zero_le_one hθ0 hθ1 hβ0
  obtain ⟨U0, hU0⟩ : ∃ x, x = trqSCKappaUnc0 P Lμ ϑ (Chapter12.finMax 1 Bμ q) q β θ :=
    ⟨_, rfl⟩
  have hU00 : 0 ≤ U0 := hU0 ▸ trqSCKappaUnc0_nonneg β θ
  -- Phase 1 constants
  obtain ⟨κA, hκA⟩ : ∃ x, x = trqSCKappaA P (fun j => LA j + LB j * ‖c x₀‖) ϑ
      (Chapter12.finMax 1 (fun j => BA j + BB j * ‖c x₀‖) q) q := ⟨_, rfl⟩
  obtain ⟨κS, hκS⟩ : ∃ x, x = trqSCKappaS P (fun j => LA j + LB j * ‖c x₀‖) ϑ
      (Chapter12.finMax 1 (fun j => BA j + BB j * ‖c x₀‖) q) q := ⟨_, rfl⟩
  obtain ⟨κC, hκC⟩ : ∃ x, x = trqSCKappaC P (fun j => LA j + LB j * ‖c x₀‖) ϑ
      (Chapter12.finMax 1 (fun j => BA j + BB j * ‖c x₀‖) q) q := ⟨_, rfl⟩
  obtain ⟨κB, hκB⟩ : ∃ x, x = Chapter12.kappaBTRq P := ⟨_, rfl⟩
  have hκA0 : 0 ≤ κA := hκA ▸ trqSCKappaA_nonneg hϑ0 hMν0
  have hκS0 : 0 ≤ κS := hκS ▸ trqSCKappaS_nonneg hϑ0 hMν0
  have hκC0 : 0 ≤ κC := hκC ▸ zero_le_one.trans one_le_trqSCKappaC
  have hκB0 : 0 ≤ κB := by rw [hκB]; unfold Chapter12.kappaBTRq; positivity
  obtain ⟨W, hW⟩ : ∃ x, x = ∑ j ∈ Finset.Icc 1 q, |β₁ ^ (1 - 2 * ((q : ℝ) + 1)) /
      (β₁ ^ (1 - ((q : ℝ) + 1)) - 1) * θ ^ (1 - ((q : ℝ) + 1))| := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := hW ▸ Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨c₁, hc₁⟩ : ∃ x, x = 1 + ‖c x₀‖ / (θ * |Real.log β₁|) := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  obtain ⟨lb, hlb⟩ : ∃ x, x = |Real.log (β₁ * θ)| := ⟨_, rfl⟩
  have hlb0 : 0 ≤ lb := hlb ▸ abs_nonneg _
  obtain ⟨r₀, hr₀⟩ : ∃ x, x = ‖c x₀‖ := ⟨_, rfl⟩
  have hr₀0 : 0 ≤ r₀ := hr₀ ▸ norm_nonneg _
  obtain ⟨g, hg'⟩ : ∃ x, x = |Real.log P.γ₂| := ⟨_, rfl⟩
  rw [← hg'] at hg
  refine ⟨1 / 2 * κA * r₀ * W + c₁ * (κB * lb + κC) + CF + CU * U0,
    c₁ * κB + CU / g, 1 / 2 * κS * r₀ * W + c₁ + CD,
    by positivity, by positivity, by positivity,
    fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR => ?_⟩
  have h := hR.run
  have hε₀ := hε 0 (by simp)
  have hεI : ∀ l ∈ Finset.Icc 1 q, 0 < ε l ∧ ε l ≤ 1 := fun l hl =>
    hε l (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hl).2))
  have hεm0 : 0 < Chapter12.finMin 1 ε q := Chapter12.finMin_pos one_pos fun j hj => (hεI j hj).1
  have hεm1 : Chapter12.finMin 1 ε q ≤ 1 := Chapter12.finMin_le_left
  obtain ⟨Λ, hΛ⟩ : ∃ x, x = trqSCLogTerm q ε := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := hΛ ▸ abs_nonneg _
  obtain ⟨O, hO⟩ : ∃ x, x = tpqpOrderF (fun _ => (q : ℝ) + 1) q ε := ⟨_, rfl⟩
  obtain ⟨OD, hOD⟩ : ∃ x, x = tpqpOrderD (fun _ => (q : ℝ) + 1) q ε := ⟨_, rfl⟩
  rw [← hΛ, ← hO, ← hOD]
  have hOT : ∀ j ∈ Finset.Icc 1 q, ε 0 ^ (1 - ((q : ℝ) + 1)) * ε j ^ (-((q : ℝ) + 1)) ≤ O :=
    fun j hj => by rw [hO]; exact term_le_tpqpOrderF (π := fun _ => (q : ℝ) + 1) hj
  have hO0 : (ε 0)⁻¹ ≤ O := by rw [hO]; exact inv_le_tpqpOrderF
  have hO1 : 1 ≤ O := by rw [hO]; exact one_le_tpqpOrderF hε₀.1 hε₀.2
  have hOnn : 0 ≤ O := zero_le_one.trans hO1
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  have hFD : O ≤ OD := by
    rw [hO, hOD]
    refine tpqpOrderF_le_tpqpOrderD hε h1q ?_
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  -- Phase 1: the number of iterations
  have hk₁ : (k₁ : ℝ) ≤ c₁ * O := by
    have h1 := phase1_iter_le h hθ0
    rw [← hr₀] at h1
    have h3 : 0 ≤ r₀ / (θ * |Real.log β₁|) := by positivity
    have h4 : r₀ / (θ * |Real.log β₁|) * (ε 0)⁻¹ ≤ r₀ / (θ * |Real.log β₁|) * O :=
      mul_le_mul_of_nonneg_left hO0 h3
    rw [hc₁, ← hr₀]
    nlinarith
  -- Phase 1: the cost contract
  have hcost := phase1_call_cost_trq hR hq (hν x₀).1 (hν x₀).2 hMν0 hc.subset hϑ1 hβ₁ϑ hθ0 hθ1 hε
  rw [← hκA, ← hκS, ← hκC, ← hκB, ← hlb, ← hΛ] at hcost
  have hπ1 : ∀ l ∈ Finset.Icc 1 q, 1 < (fun _ : ℕ => (q : ℝ) + 1) l := fun l _ => by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    change 1 < (q : ℝ) + 1
    linarith
  have hF1 := (lemma_14_3_7_add h hθ0 hπ1 hκA0 fun k hk => (hcost k hk).1).trans
    (add_le_add (phase1Bound_le (π := fun _ : ℕ => (q : ℝ) + 1) hκA0 (norm_nonneg _)
      (fun j hj => (hε j hj).1) hOT) le_rfl)
  have hD1 := (lemma_14_3_7_add h hθ0 hπ1 hκS0 fun k hk => (hcost k hk).2).trans
    (add_le_add (phase1Bound_le (π := fun _ : ℕ => (q : ℝ) + 1) hκS0 (norm_nonneg _)
      (fun j hj => (hε j hj).1) hOT) le_rfl)
  rw [← hW, ← hr₀] at hF1 hD1
  have ha0 : 0 ≤ κB * (lb + Λ) + κC := by positivity
  have hF1' : ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
      (1 / 2 * κA * r₀ * W + c₁ * (κB * lb + κC) + c₁ * κB * Λ) * O := by
    have := mul_le_mul_of_nonneg_right hk₁ ha0
    linarith only [hF1, this]
  have hD1' : ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ (1 / 2 * κS * r₀ * W + c₁) * O := by
    linarith only [hD1, hk₁]
  have hP1D : 0 ≤ 1 / 2 * κS * r₀ * W + c₁ := by positivity
  have hextra : 0 ≤ (CF + CU * U0) * O + CU / g * Λ * O := by positivity
  have hD1'' : ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ (1 / 2 * κS * r₀ * W + c₁) * OD :=
    hD1'.trans (mul_le_mul_of_nonneg_left hFD hP1D)
  refine ⟨fun _ => ⟨by linarith only [hF1', hextra],
    by linarith only [hD1'', mul_nonneg hCD (hOnn.trans hFD)]⟩, fun hc1 => ?_⟩
  -- Phase 2
  have h2 := h.phase2 hc1
  have hin := (hR.phase2 hc1).isInnerPhaseRunStrong h2 hq (hμ := fun t => (hμ t).1)
    (fun t => (hμ t).2) hMμ0 hc.subset hβϑ hϑ1
  rw [← hU0, ← hg'] at hin
  obtain ⟨l, hl, hmin⟩ := Chapter12.exists_finMin_eq hq fun j hj => (hεI j hj).2
  have hκunc : 0 ≤ U0 + trqSCLogTerm q ε / g := by rw [← hΛ]; positivity
  obtain ⟨kε, hend, hF2, hD2⟩ := hord (ρ' := fun _ => ε 0 * Chapter12.finMin 1 ε q) hκunc h2
    hin (fun _ _ => mul_pos hε₀.1 hεm0)
    (fun l _ => ⟨by positivity, le_rfl⟩) hB hεβ (le_abs_self _)
    (fun _ hy => hf.contDiffAt_of_le le_rfl hy) (fun _ hy => hc.contDiffAt_of_le le_rfl hy)
    (fun _ hy _ => hf.norm_iteratedFDeriv_le_finMax le_rfl (hf.subset hy)) hO0 hOT
    (fun j hj => by
      rw [one_mul]
      refine (inv_bad_le_trq hε₀.1 hε₀.2 hεm0 hεm1 (Chapter12.finMin_le hj)
        (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2).trans ?_
      have := hOT l hl
      rw [hmin]
      exact this)
  rw [← hΛ] at hF2
  have hD2' : (D.derivEvals kε : ℝ) ≤ CD * OD := hD2.trans (mul_le_mul_of_nonneg_left hFD hCD)
  refine ⟨kε, hend, ?_, by linarith only [hD1'', hD2']⟩
  have e : (CF + CU * (U0 + Λ / g)) * O = (CF + CU * U0) * O + CU / g * Λ * O := by ring
  linarith only [hF1', hF2, e]

/-- `tpqpOrderF` depends only on the exponents `π_j`, `j ∈ [1 : q]`. -/
theorem tpqpOrderF_congr {π π' : ℕ → ℝ} {ε : ℕ → ℝ} (h : ∀ j ∈ Finset.Icc 1 q, π j = π' j) :
    tpqpOrderF π q ε = tpqpOrderF π' q ε := by
  unfold tpqpOrderF Chapter12.finMax
  congr 2
  exact Finset.image_congr fun j hj => by simp only [h j hj]

/-- `tpqpOrderD` depends only on the exponents `π_j`, `j ∈ [1 : q]`. -/
theorem tpqpOrderD_congr {π π' : ℕ → ℝ} {ε : ℕ → ℝ} (h : ∀ j ∈ Finset.Icc 1 q, π j = π' j) :
    tpqpOrderD π q ε = tpqpOrderD π' q ε := by
  unfold tpqpOrderD Chapter12.finMax
  congr 2
  exact Finset.image_congr fun j hj => by simp only [h j hj]

/-- **Theorem 14.3.9** of [cartis2022evaluation] **with a trust-region INNER for `q = 1`, with the
printed exponent `π_1 = 2`** (the TRq-SC entry `j + 1` of (14.2.12)): `theorem_14_3_9_trq` with
`q = 1`, where the exponent `q + 1` of Lemma 12.2.4 is the printed `j + 1`. The derivative
evaluations are `O(max_j ε₀^{-j} ε_j^{-(j+1)}) = O(ε₀^{-1} ε_1^{-2})`, the printed order; the
evaluations of `(f, c)` are `O((1 + |log(ε₀ ε_1)|) max[ε₀^{-1}, ε₀^{-1} ε_1^{-2}])`, the printed
order up to the factor `1 + |log(ε₀ ε_1)|` from the restarts of the trust-region radius. That
factor is needed: the printed bound fails (`theorem_14_3_9_trq_log_necessary`). -/
theorem theorem_14_3_9_trq_one {X₀ : Set ℝⁿ} {Lc Bc Lf Bf : ℕ → ℝ}
    (hc : AssumptionCD1pLBX c X X₀ 1 Lc Bc) (hf : AssumptionD1pLBX f X X₀ 1 Lf Bf)
    {βF flow fup : ℝ} (hB : Chapter07.AssumptionBFb f c X βF flow fup)
    (P : Optimization.TRqParams) {ϑ θ β β₁ : ℝ} (hϑ1 : ϑ ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ0 : 0 < β) (hβϑ : β ≤ ϑ) (x₀ : ℝⁿ) (hβ₁ϑ : β₁ * ‖c x₀‖ ≤ ϑ) :
    ∃ κF κL κD : ℝ, 0 ≤ κF ∧ 0 ≤ κL ∧ 0 ≤ κD ∧
      ∀ ε : ℕ → ℝ, (∀ j ∈ Finset.range 2, 0 < ε j ∧ ε j ≤ 1) → ε 0 ≤ βF →
      ∀ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
        IsTPqpGCTRqSCRun f c X 1 P ϑ θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ →
        (θ * ε 0 < ‖c (xP k₁)‖ →
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) ≤
            (κF + κL * |Real.log (ε 0 * ε 1)|) * tpqpOrderF (fun j => (j : ℝ) + 1) 1 ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) ≤ κD * tpqpOrderD (fun j => (j : ℝ) + 1) 1 ε) ∧
        (‖c (xP k₁)‖ ≤ θ * ε 0 → ∃ kε, D.IsEnd f c X 1 θ ε kε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nF₁ k : ℝ) + D.funEvals kε ≤
            (κF + κL * |Real.log (ε 0 * ε 1)|) * tpqpOrderF (fun j => (j : ℝ) + 1) 1 ε ∧
          ∑ k ∈ Finset.Icc 1 k₁, (nD₁ k : ℝ) + D.derivEvals kε ≤
            κD * tpqpOrderD (fun j => (j : ℝ) + 1) 1 ε) := by
  obtain ⟨κF, κL, κD, h0, h1, h2, H⟩ :=
    theorem_14_3_9_trq le_rfl hc hf hB P hϑ1 hθ0 hθ1 hβ0 hβϑ x₀ hβ₁ϑ
  refine ⟨κF, κL, κD, h0, h1, h2, fun ε hε hεβ xP δP k₁ D nF₁ nD₁ hR => ?_⟩
  have hπ : ∀ j ∈ Finset.Icc 1 1,
      (fun _ : ℕ => ((1 : ℕ) : ℝ) + 1) j = (fun j : ℕ => (j : ℝ) + 1) j :=
    fun j hj => by rw [Finset.Icc_self, Finset.mem_singleton] at hj; subst hj; rfl
  have hΛ : trqSCLogTerm 1 ε = |Real.log (ε 0 * ε 1)| := by
    have hε1 := hε 1 (by simp)
    unfold trqSCLogTerm
    congr 3
    exact le_antisymm (Chapter12.finMin_le (Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩))
      (Chapter12.le_finMin hε1.2 fun j hj => by
        rw [Finset.Icc_self, Finset.mem_singleton] at hj; subst hj; exact le_rfl)
  rw [← tpqpOrderF_congr hπ, ← tpqpOrderD_congr hπ, ← hΛ]
  exact H ε hε hεβ xP δP k₁ D nF₁ nD₁ hR

end Theorem1439

/-! ### Existence of TPqp-GC runs with a trust-region INNER -/

section Existence

variable {F : ℝⁿ → ℝ} {X : Set ℝⁿ} {q : ℕ} {P : Optimization.TRqParams} {ϑ : ℝ} {ε : ℕ → ℝ}

/-- **TRq-SC runs exist** ([cartis2022evaluation], Algorithm 12.2.1 with a feasible set, as used
in §14.2): for a closed `X`, `ϑ ≥ 0` and every starting point `x₀ ∈ X`, there is a run of
`Chapter12.algorithm_12_2_1_feasible` from `x₀` (from `Optimization.exists_isTRqRun` with the
feasible displacements `{d | y + d ∈ X}` at points `y ∈ X`; the iterates stay in `X` up to
termination). -/
theorem exists_algorithm_12_2_1_feasible (hX : IsClosed X) (F : ℝⁿ → ℝ)
    (P : Optimization.TRqParams) (q : ℕ) (ε : ℕ → ℝ) (hϑ : 0 ≤ ϑ) {x₀ : ℝⁿ} (hx₀ : x₀ ∈ X) :
    ∃ (x s : ℕ → ℝⁿ) (Δ : ℕ → ℝ) (jk : ℕ → ℕ) (d : ℕ → ℕ → ℝⁿ), x 0 = x₀ ∧
      Chapter12.algorithm_12_2_1_feasible F X P q ε ϑ x s Δ jk d := by
  classical
  obtain ⟨C', hC'⟩ : ∃ C' : ℝⁿ → Set ℝⁿ,
      ∀ y, C' y = if y ∈ X then {e | y + e ∈ X} else univ := ⟨_, fun _ => rfl⟩
  have hC : ∀ y, IsClosed (C' y) := fun y => by
    rw [hC']
    by_cases hy : y ∈ X
    · simp only [hy, ↓reduceIte]
      exact hX.preimage (continuous_const.add continuous_id)
    · simp only [hy, ↓reduceIte]
      exact isClosed_univ
  have hC0 : ∀ y, (0 : ℝⁿ) ∈ C' y := fun y => by
    rw [hC']
    by_cases hy : y ∈ X <;> simp [hy]
  obtain ⟨x, s, Δ, jk, d, hx0, hr⟩ := Optimization.exists_isTRqRun F
    (fun y => ftaylorSeries ℝ F y) C' hC hC0 P q ε hϑ x₀
  have hmem : ∀ k, (∀ i < k, ¬ Optimization.trqTest (fun k => ftaylorSeries ℝ F (x k)) P q ε ϑ
      Δ d i) → x k ∈ X := by
    intro k
    induction k with
    | zero => intro _; rw [hx0]; exact hx₀
    | succ k ih =>
      intro hk
      have hk' : ∀ i ≤ k, ¬ Optimization.trqTest (fun k => ftaylorSeries ℝ F (x k)) P q ε ϑ
          Δ d i := fun i hi => hk i (Nat.lt_succ_of_le hi)
      have hxk := ih fun i hi => hk' i hi.le
      have hacc := hr.accept k hk'
      by_cases hs : P.η₁ ≤ Optimization.trqRatio F (fun k => ftaylorSeries ℝ F (x k)) x s jk k
      · rw [hacc.eq_add hs]
        have := (hr.step k hk').mem.2
        rw [hC'] at this
        simp only [hxk, ↓reduceIte] at this
        exact this
      · rw [hacc.eq_self (not_le.1 hs)]
        exact hxk
  have hS : ∀ k, (∀ i < k, ¬ Optimization.trqTest (fun k => ftaylorSeries ℝ F (x k)) P q ε ϑ
      Δ d i) → C' (x k) = {e | x k + e ∈ X} := fun k hk => by
    rw [hC']
    simp only [hmem k hk, ↓reduceIte]
  refine ⟨x, s, Δ, jk, d, hx0, ⟨⟨hr.delta_zero, fun k hk => ?_, hr.accept⟩,
    fun k hk j hj => ?_, hr.cap⟩⟩
  · have h1 := hr.step k hk
    have h2 := hS k fun i hi => hk i hi.le
    exact h2 ▸ h1
  · have h1 := hr.witness k hk j hj
    have h2 := hS k hk
    exact h2 ▸ h1

/-- `F` does not increase along a feasible TRq run before termination (with `ε ≥ 0`, `ϑ ≥ 0`):
a successful step has a positive Taylor decrease. -/
theorem trq_step_le {x s : ℕ → ℝⁿ} {Δ : ℕ → ℝ} {jk : ℕ → ℕ} {d : ℕ → ℕ → ℝⁿ}
    (h : Chapter12.algorithm_12_2_1_feasible F X P q ε ϑ x s Δ jk d)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) (hϑ : 0 ≤ ϑ) {k : ℕ}
    (hk : ∀ i ≤ k, ¬ Chapter12.trqStop F P q ε ϑ x Δ d i) : F (x (k + 1)) ≤ F (x k) := by
  have hst := Optimization.IsTRqRun.isTRqStep h hk
  have hδ : 0 ≤ min (Δ k) ϑ :=
    le_min (Optimization.IsTRqRun.delta_pos' h fun i hi => hk i hi.le).le hϑ
  have hpos : 0 < (ftaylorSeries ℝ F (x k)).taylorDecrement (jk k) (s k) := by
    refine lt_of_le_of_lt ?_ (hst.lt_taylorDecrement.trans_le hst.taylorDecrement_le)
    exact div_nonneg (mul_nonneg (mul_nonneg P.ς_pos.le (hε _ hst.order_mem))
      (pow_nonneg hδ _)) (Nat.cast_nonneg _)
  exact (h.accept k hk).le Optimization.trqRatio_eq hpos

variable {f : ℝⁿ → ℝ} {c : ℝⁿ → ℝᵐ} {θ β : ℝ}

open Classical in
/-- **One INNER call of Phase 2 by TRq-SC exists** from every `(x, t)` with `x ∈ X` and
`θε₀ ≤ ‖r(x, t)‖ ≤ ε₀`: TRq-SC on `μ(·, t)` with threshold `ϑ` and tolerances `β ‖r(x, t)‖ ε`
(which terminates, `Chapter12.theorem_12_2_5_anchored`), stopped at its termination or as soon as
`‖r(·, t)‖ < θε₀`, returning the radii `min(Δ_e, ϑ)`; its output satisfies (14.3.32) (the first
or the third test). -/
theorem exists_trqCallData {t : ℝ} {L : ℕ → ℝ} {X₀ : Set ℝⁿ}
    (hμ : Chapter12.AssumptionD1pLAnchored (Constrained.targetMerit f c t) X₀
      (muSublevel f c X t) q L) (hXX₀ : X ⊆ X₀) (P : Optimization.TRqParams) (hq : 1 ≤ q)
    (hX : IsClosed X) (hθ0 : 0 < θ) (hβ0 : 0 < β) (hβθ : β ≤ θ) (hβϑ : β ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {x : ℝⁿ} (hx : x ∈ X)
    (hlo : θ * ε 0 ≤ Constrained.targetResidual f c t x)
    (hhi : Constrained.targetResidual f c t x ≤ ε 0) :
    ∃ o : CallOut n, o.xi 0 = x ∧ o.xi o.e ∈ X ∧
      (∀ j ∈ Finset.Icc 1 q, 0 < o.δ j ∧ o.δ j ≤ 1) ∧
      (Constrained.targetResidual f c t (o.xi o.e) < θ * ε 0 ∨
        meritCrit f c X q ε t (o.xi o.e) o.δ) ∧
      (∀ i < o.e, Constrained.targetMerit f c t (o.xi (i + 1)) ≤
        Constrained.targetMerit f c t (o.xi i)) ∧
      (∀ i < o.e, θ * ε 0 ≤ Constrained.targetResidual f c t (o.xi i)) ∧
      Constrained.targetResidual f c t (o.xi o.e) ≤ Constrained.targetResidual f c t x ∧
      IsTRqSCCallOut (Constrained.targetMerit f c t) X q P ϑ
        (fun j => β * Constrained.targetResidual f c t x * ε j) o.xi o.e o.succ o.δ := by
  obtain ⟨F, hFdef⟩ : ∃ F, F = Constrained.targetMerit f c t := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = Constrained.targetResidual f c t x := ⟨_, rfl⟩
  rw [← hFdef] at hμ ⊢
  rw [← hρ] at hlo hhi ⊢
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have hε₀ := hε 0 (by simp)
  have hρ0 : 0 < ρ := lt_of_lt_of_le (mul_pos hθ0 hε₀.1) hlo
  have hβ1 : β ≤ 1 := hβϑ.trans hϑ1
  have hle : ∀ j ∈ Finset.Icc 1 q, β * ρ * ε j ≤ β := fun j hj => by
    have h1 : ρ * ε j ≤ 1 := by nlinarith [hεI j hj]
    nlinarith [hεI j hj]
  have hε' : ∀ j ∈ Finset.Icc 1 q, β * ρ * ε j ∈ Ioc 0 1 := fun j hj =>
    ⟨by have := (hεI j hj).1; positivity, (hle j hj).trans hβ1⟩
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  have hϑ' : Chapter12.finMin 1 (fun j => β * ρ * ε j) q ≤ ϑ :=
    (Chapter12.finMin_le h1q).trans ((hle 1 h1q).trans hβϑ)
  have hϑ0 : 0 < ϑ := hβ0.trans_le hβϑ
  have hS : ∀ y ∈ X, F y ≤ F x → y ∈ muSublevel f c X t := fun y hy hyx => by
    rw [hFdef] at hyx
    exact ⟨hy, (Constrained.targetMerit_le_targetMerit_iff.1 hyx).trans
      ((hρ ▸ hhi).trans hε₀.2)⟩
  obtain ⟨xr, s, Δ, jk, d, hx0, hr⟩ := exists_algorithm_12_2_1_feasible hX F P q
    (fun j => β * ρ * ε j) hϑ0.le hx
  have hA : ∀ y ∈ X, F y ≤ F (xr 0) → y ∈ muSublevel f c X t := by rw [hx0]; exact hS
  have hxr0 : xr 0 ∈ X := hx0 ▸ hx
  obtain ⟨kε, hhit, -, -, hcertε, -, -⟩ := Chapter12.theorem_12_2_5_anchored (flow := 0)
    (fun y _ => by rw [hFdef]; exact Constrained.targetMerit_nonneg) hμ hXX₀ hA hxr0 hε' hϑ'
    hϑ1 hr
  have hex : ∃ i, i = kε ∨ Constrained.targetResidual f c t (xr i) < θ * ε 0 :=
    ⟨kε, Or.inl rfl⟩
  set e := Nat.find hex with he
  have he_le : e ≤ kε := Nat.find_min' hex (Or.inl rfl)
  have hnot : ∀ i < e, ¬ Chapter12.trqStop F P q (fun j => β * ρ * ε j) ϑ xr Δ d i :=
    fun i hi => hhit.2 i (by omega)
  have hε'0 : ∀ j ∈ Finset.Icc 1 q, 0 ≤ β * ρ * ε j := fun j hj => (hε' j hj).1.le
  have hsub := Chapter12.trq_mem_sublevel hr hxr0 hε'0 hϑ0.le e hnot
  have hmono : ∀ i < e, F (xr (i + 1)) ≤ F (xr i) := fun i hi =>
    trq_step_le hr hε'0 hϑ0.le fun l hl => hnot l (by omega)
  have hres : Constrained.targetResidual f c t (xr e) ≤ ρ := by
    have := hsub.2
    rw [hx0, hFdef] at this
    rw [hρ]
    exact Constrained.targetMerit_le_targetMerit_iff.1 this
  have hlow : ∀ i < e, θ * ε 0 ≤ Constrained.targetResidual f c t (xr i) := fun i hi => by
    have := Nat.find_min hex hi
    push Not at this
    exact this.2
  have hδ : 0 < min (Δ e) ϑ := lt_min (Optimization.IsTRqRun.delta_pos' hr hnot) hϑ0
  refine ⟨⟨xr, e, fun i => P.η₁ ≤ Chapter12.trqRho F xr s jk i, fun _ => min (Δ e) ϑ⟩, hx0,
    hsub.1, fun _ _ => ⟨hδ, (min_le_right _ _).trans hϑ1⟩, ?_, fun i hi => hFdef ▸ hmono i hi,
    hlow, hres, ⟨xr, s, Δ, jk, d, kε, hr, hhit, he_le, fun _ _ => rfl, fun _ _ => Iff.rfl,
      fun _ _ => rfl⟩⟩
  by_cases hlt : Constrained.targetResidual f c t (xr e) < θ * ε 0
  · exact Or.inl hlt
  · -- the call has terminated: the certificate gives the third test of (14.3.32)
    have hek : e = kε := by
      rcases Nat.find_spec hex with h' | h'
      · exact h'
      · exact absurd h' hlt
    refine Or.inr fun j hj => ?_
    have hcert := hcertε j hj
    rw [← hek, hFdef] at hcert
    refine hcert.trans ?_
    have hge := not_lt.1 hlt
    have hεj := (hεI j hj).1
    have : β * ρ ≤ Constrained.targetResidual f c t (xr e) := by nlinarith
    have : β * ρ * ε j ≤ ε j * Constrained.targetResidual f c t (xr e) := by nlinarith
    change β * ρ * ε j * min (Δ e) ϑ ^ j / (j ! : ℝ) ≤
      ε j * Constrained.targetResidual f c t (xr e) * min (Δ e) ϑ ^ j / (j ! : ℝ)
    gcongr

/-- **TPqp-GC runs with INNER = TRq-SC in both phases exist** (so the class `IsTPqpGCTRqSCRun` of
`theorem_14_3_9_trq` is not empty) under X.CNe (`X` closed), c.D1qLB.X and f.D1qLB.X (on an open
convex `X₀ ⊇ X`), for all TRq parameters, `θ ∈ (0, 1)`, `β ∈ (0, θ]` with `β ≤ ϑ ≤ 1`,
`ε ∈ (0, 1]^{q+1}`, `β₁ ∈ (0, 1)` with `β₁ ‖c(x₀)‖ < 1` and `β₁ ‖c(x₀)‖ ≤ ϑ`, and `x₀ ∈ X`:
Phase 1 is LENq-SC with TRq-SC calls on `ν`, Phase 2 has the calls of `exists_trqCallData`
(`phase2_core_of`). -/
theorem exists_isTPqpGCTRqSCRun (hX : IsClosed X) (hq : 1 ≤ q) {X₀ : Set ℝⁿ}
    {Lc Bc Lf Bf : ℕ → ℝ} (hc : AssumptionCD1pLBX c X X₀ q Lc Bc)
    (hf : AssumptionD1pLBX f X X₀ q Lf Bf) (P : Optimization.TRqParams) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hβ0 : 0 < β) (hβθ : β ≤ θ) (hβϑ : β ≤ ϑ) (hϑ1 : ϑ ≤ 1)
    (hε : ∀ j ∈ Finset.range (q + 1), 0 < ε j ∧ ε j ≤ 1) {β₁ : ℝ} (hβ₁0 : 0 < β₁)
    (hβ₁1 : β₁ < 1) {x₀ : ℝⁿ} (hx₀ : x₀ ∈ X) (hβ₁c : β₁ * ‖c x₀‖ < 1)
    (hβ₁ϑ : β₁ * ‖c x₀‖ ≤ ϑ) :
    ∃ (xP : ℕ → ℝⁿ) (δP : ℕ → ℕ → ℝ) (k₁ : ℕ) (D : TPqpSeq n) (nF₁ nD₁ : ℕ → ℕ),
      IsTPqpGCTRqSCRun f c X q P ϑ θ β₁ β ε x₀ xP δP k₁ D nF₁ nD₁ := by
  obtain ⟨LA, LB, BA, BB, hν⟩ := exists_nu_trq hc
  obtain ⟨Lμ, Bμ, hμ⟩ := exists_mu_trq hc hf
  have hϑ0 : 0 < ϑ := hβ0.trans_le hβϑ
  have hεI : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 := fun j hj =>
    hε j (Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_Icc.1 hj).2))
  have h1q : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
  have hε₁ : ∀ j ∈ Finset.range (q + 1), 0 < phase1Tol θ ε j ∧ phase1Tol θ ε j ≤ 1 := by
    intro j hj
    by_cases h0 : j = 0
    · subst h0
      obtain ⟨h1, h2⟩ := hε 0 hj
      simp only [phase1Tol_zero]
      exact ⟨mul_pos hθ0 h1, by nlinarith⟩
    · rw [phase1Tol_of_ne θ ε h0]
      exact hε j hj
  -- Phase 1: LENq-SC with TRq-SC calls on `ν`
  obtain ⟨xP, δP, nF, nD, hxP0, hrun, hcalls⟩ := lenq_core_of hε₁ hβ₁0 hβ₁1 hx₀ hβ₁c
    (fun y o => IsTRqSCOutputCost (phi2 c) X q P ϑ (fun j => β₁ * ‖c y‖ * phase1Tol θ ε j) y o.1
      o.2.1 o.2.2.1 o.2.2.2) fun y hyX hy0 hry _ => by
      have hε' : ∀ j ∈ Finset.Icc 1 q, β₁ * ‖c y‖ * phase1Tol θ ε j ∈ Ioc 0 1 := fun j hj => by
        rw [phase1Tol_of_ne θ ε (by have := (Finset.mem_Icc.1 hj).1; omega)]
        refine ⟨by have := (hεI j hj).1; positivity, ?_⟩
        calc β₁ * ‖c y‖ * ε j ≤ β₁ * ‖c x₀‖ * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left hy0 hβ₁0.le) (hεI j hj).2
                (hεI j hj).1.le (mul_nonneg hβ₁0.le (norm_nonneg _))
          _ ≤ 1 := by rw [mul_one]; exact hβ₁c.le
      have hle1 : β₁ * ‖c y‖ * phase1Tol θ ε 1 ≤ ϑ := by
        rw [phase1Tol_of_ne θ ε one_ne_zero]
        calc β₁ * ‖c y‖ * ε 1 ≤ β₁ * ‖c x₀‖ * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left hy0 hβ₁0.le) (hεI 1 h1q).2
                (hεI 1 h1q).1.le (mul_nonneg hβ₁0.le (norm_nonneg _))
          _ ≤ ϑ := by rw [mul_one]; exact hβ₁ϑ
      have hϑ' : Chapter12.finMin 1 (fun j => β₁ * ‖c y‖ * phase1Tol θ ε j) q ≤ ϑ :=
        (Chapter12.finMin_le h1q).trans hle1
      obtain ⟨x, s, Δ, jk, d, hx0, hr⟩ := exists_algorithm_12_2_1_feasible hX (phi2 c) P q
        (fun j => β₁ * ‖c y‖ * phase1Tol θ ε j) hϑ0.le hyX
      have hxr0 : x 0 ∈ X := hx0 ▸ hyX
      have hA : ∀ z ∈ X, phi2 c z ≤ phi2 c (x 0) → z ∈ nuSublevel c X x₀ := fun z hz hzy => by
        rw [hx0] at hzy
        exact ⟨hz, (norm_le_of_phi2_le hzy).trans hy0⟩
      obtain ⟨kε, hhit, hmem, hrad, hcert, -, -⟩ := Chapter12.theorem_12_2_5_anchored (flow := 0)
        (fun z _ => by rw [phi2_apply]; positivity) (hν x₀).1 hc.subset hA hxr0 hε' hϑ' hϑ1 hr
      have hsub := Chapter12.trq_mem_sublevel hr hxr0 (fun j hj => (hε' j hj).1.le) hϑ0.le kε
        hhit.2
      refine ⟨(x kε, fun _ => min (Δ kε) ϑ, Optimization.funEvalCount kε,
        Optimization.derivEvalCount (fun k => P.η₁ ≤ Chapter12.trqRho (phi2 c) x s jk k) kε),
        hmem, ?_, fun _ _ => hrad, hcert, ⟨x, s, Δ, jk, d, kε, hr, hhit, hx0, rfl,
          fun _ _ => rfl, rfl, rfl⟩⟩
      have := hsub.2
      rw [hx0] at this
      exact norm_le_of_phi2_le this
  obtain ⟨⟨k₁, hhit, -, -⟩, -⟩ := theorem_14_3_3 hrun
  have hcalls' : ∀ k, 1 ≤ k → k ≤ k₁ → IsTRqSCOutputCost (phi2 c) X q P ϑ
      (fun j => β₁ * ‖c (xP (k - 1))‖ * phase1Tol θ ε j) (xP (k - 1)) (xP k) (δP k) (nF k)
        (nD k) :=
    fun k hk1 hk => hcalls k hk1 fun i hi => hhit.2 i (hi.trans_le hk)
  by_cases hc1 : ‖c (xP k₁)‖ ≤ θ * ε 0
  · have hmem : xP k₁ ∈ X := by
      rcases Nat.eq_zero_or_pos k₁ with h0 | hpos
      · rw [h0]; exact hrun.mem_zero
      · exact hrun.mem k₁ hpos hhit.2
    -- Phase 2 with the calls of `exists_trqCallData`
    obtain ⟨D, hD, hcallsD⟩ := phase2_core_of hθ0 hθ1 hβ0 hβθ hε hmem hc1
      (fun x t o => IsTRqSCCallOut (Constrained.targetMerit f c t) X q P ϑ
        (fun j => β * Constrained.targetResidual f c t x * ε j) o.xi o.e o.succ o.δ)
      (fun x t hx hlo hhi _ => exists_trqCallData (hμ t).1 hc.subset P hq hX hθ0 hβ0 hβθ hβϑ
        hϑ1 hε hx hlo hhi)
    exact ⟨xP, δP, k₁, D, nF, nD, ⟨⟨hxP0, hrun, hhit, fun _ => hD⟩, hcalls',
      fun _ k hk1 hk => (hcallsD k hk1 hk).2⟩⟩
  · exact ⟨xP, δP, k₁, ⟨fun _ => x₀, fun _ => 0, fun _ _ => 0, fun _ _ => x₀, fun _ => 0,
      fun _ _ => False⟩, nF, nD, ⟨⟨hxP0, hrun, hhit, fun h => absurd h hc1⟩, hcalls',
      fun h => absurd h hc1⟩⟩

end Existence

end CartisGouldToint.Chapter14
